module

public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoOpenUnitary
public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoOpenVac

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

namespace CorFourTwoOpen

@[expose] def GGTorusIrredSC (p : ℕ) (R : Type) [Group R] (I : Set (MulAut R)) : Prop :=
  ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
    ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
    ∀ A : Subgroup (MulAut L'), IsElemAbelian p A →
      (∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) →
      p ^ 3 ≤ Nat.card A → GGTorusSelfCent p A →
      ∃ W : Set L',
        (∀ n ∈ W, ∀ a ∈ A, (n * (a n)⁻¹) ^ p = 1 ∧ ∀ a' ∈ A, a' (n * (a n)⁻¹) = n * (a n)⁻¹) ∧
        (∀ A' : Subgroup (MulAut L'), A' ≤ A →
          (∀ n ∈ W, ∀ a ∈ A', MulAut.conj n * a * (MulAut.conj n)⁻¹ ∈ A') → A' = ⊥ ∨ A' = A) ∧
        (∃ n ∈ W, ∃ a ∈ A, MulAut.conj n * a * (MulAut.conj n)⁻¹ ≠ a) ∧
        ∀ f : MulAut L' → MulAut L', (∀ a ∈ A, f a ∈ A) →
          (∀ a ∈ A, ∀ b ∈ A, f (a * b) = f a * f b) →
          (∀ n ∈ W, ∀ a ∈ A, f (MulAut.conj n * a * (MulAut.conj n)⁻¹) =
            MulAut.conj n * f a * (MulAut.conj n)⁻¹) →
          ∃ c : ℕ, ∀ a ∈ A, f a = a ^ c

section Irred

variable {G : Type} [Group G] [Finite G]

theorem ggTableBIrred_of_ggTorusIrredSC {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) (hL : commutator L = ⊤) {R : Type} [Group R]
    (θ : L ⧸ Subgroup.center L ≃* R) {I : Set (MulAut R)}
    (hBsN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hBs3 : ∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ)
    (hT : GGTorusIrredSC p R I) : GGTableBIrred Bs x L := by
  classical
  obtain ⟨hp, hBs, hxB, hLx, -⟩ := hcfg.tableB_facts
  have := Fact.mk hp
  have hS : LargeEvenSStar p B x L := hcfg.1.2.2.2.2.2.2.1
  have hBBs : B ≤ Bs := hcfg.2.1.1
  have hBN : B ≤ Subgroup.normalizer (L : Set G) := hBBs.trans hBsN
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  set γ := ggGamma L hBsN with hγ
  have hBp : ∀ b : Bs, b ^ p = 1 := fun b => Subtype.ext (by simpa using hBs.2 b b.2)
  have hBc : ∀ a b : Bs, a * b = b * a := fun a b =>
    Subtype.ext (IsElemAbelian.comm hBs a.2 b.2)
  have hA : IsElemAbelian p γ.range := isElemAbelian_range hBc hBp γ
  have hAI : ∀ a ∈ γ.range, ∃ φ ∈ I, ∀ l : L, φ (ggQuotHom θ l) = ggQuotHom θ (a l) := by
    rintro _ ⟨b, rfl⟩
    exact ⟨ggBeta L θ hBsN b, ggBeta_mem L θ hBsN hBs3 b, fun l => ggBeta_ggQuotHom L hBsN θ b l⟩
  have hcA := card_range_ggGamma_mul L hBN hp hS
  have hle : Nat.card (ggGamma L hBN).range ≤ Nat.card γ.range := by
    refine Subgroup.card_le_of_le ?_
    rintro _ ⟨b, rfl⟩
    exact ⟨⟨b, hBBs b.2⟩, rfl⟩
  have h3' : p ^ 3 ≤ Nat.card γ.range := by
    refine le_trans ?_ hle
    have h4 := pow_four_le_card_of_bmax hp hS.1 hcfg.1.2.2.2.2.2.1.2.2.2
    rw [← hcA, pow_succ] at h4
    exact Nat.le_of_mul_le_mul_right h4 hp.pos
  obtain ⟨W, hW1, hW2, ⟨n₀, hn₀, a₀, ha₀, hna₀⟩, hW4⟩ := hT L (ggQuotHom θ)
    (ggQuotHom_surjective θ) (by rw [ker_ggQuotHom]) hL γ.range hA hAI h3'
    (ggTorusSelfCent_ggGamma hBsN hSC)
  have hker : ∀ b : Bs, γ b = 1 ↔ (b : G) ∈ Subgroup.zpowers x := fun b => by
    rw [hγ, ggGamma_eq_one_iff, ← inf_centralizer_eq_zpowers_of_elemAbelian hp hBs hxB hS.2.2.1
      hS.2.2.2.1.1 hS.2.2.2.2]
    exact ⟨fun h => ⟨b.2, h⟩, fun h => h.2⟩
  have hWB : ∀ n ∈ W, ∀ b ∈ Bs, (n : G) * b * (n : G)⁻¹ ∈ Bs := by
    intro n hn b hb
    obtain ⟨htp, htA⟩ := hW1 n hn (γ ⟨b, hb⟩) ⟨⟨b, hb⟩, rfl⟩
    have htG : ((n * (γ ⟨b, hb⟩ n)⁻¹ : L) : G) = n * b * (n : G)⁻¹ * b⁻¹ := by
      push_cast
      rw [hγ, ggGamma_coe]
      group
    have htC : ((n * (γ ⟨b, hb⟩ n)⁻¹ : L) : G) ∈ Subgroup.centralizer (Bs : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro b' hb'
      have h1 := congrArg Subtype.val (htA (γ ⟨b', hb'⟩) ⟨⟨b', hb'⟩, rfl⟩)
      rw [hγ, ggGamma_coe] at h1
      calc b' * ((n * (γ ⟨b, hb⟩ n)⁻¹ : L) : G)
          = b' * ((n * (γ ⟨b, hb⟩ n)⁻¹ : L) : G) * b'⁻¹ * b' := by group
        _ = ((n * (γ ⟨b, hb⟩ n)⁻¹ : L) : G) * b' := by rw [h1]
    have htp' : ((n * (γ ⟨b, hb⟩ n)⁻¹ : L) : G) ^ p = 1 := by
      have := congrArg Subtype.val htp
      simpa using this
    have htB := hSC _ htC htp'
    have e : (n : G) * b * (n : G)⁻¹ = ((n * (γ ⟨b, hb⟩ n)⁻¹ : L) : G) * b := by
      rw [htG]
      group
    rw [e]
    exact Bs.mul_mem htB hb
  have hWN : ∀ n ∈ W, (n : G) ∈ L ⊓ Subgroup.normalizer (Bs : Set G) := by
    intro n hn
    refine ⟨n.2, ?_⟩
    have h := mem_normalizer_of_forall_conj_mem (W := Bs) (g := (n : G)⁻¹) (fun w hw => by
      simpa using hWB n hn w hw)
    simpa using Subgroup.inv_mem _ h
  have hconj : ∀ n ∈ W, ∀ b : Bs, ∃ hnb : (n : G) * b * (n : G)⁻¹ ∈ Bs,
      γ ⟨(n : G) * b * (n : G)⁻¹, hnb⟩ = MulAut.conj n * γ b * (MulAut.conj n)⁻¹ :=
    fun n hn b => ⟨hWB n hn b b.2, ggGamma_conj L hBsN n b (hWB n hn b b.2)⟩
  refine ⟨?_, ?_, ?_⟩
  ·
    intro S hxS hSB hSinv
    set A' : Subgroup (MulAut L) := (S.subgroupOf Bs).map γ with hA'
    have hA'A : A' ≤ γ.range := by
      rintro _ ⟨s, -, rfl⟩
      exact ⟨s, rfl⟩
    have hA'inv : ∀ n ∈ W, ∀ a ∈ A', MulAut.conj n * a * (MulAut.conj n)⁻¹ ∈ A' := by
      rintro n hn _ ⟨s, hs, rfl⟩
      obtain ⟨hns, he⟩ := hconj n hn s
      exact ⟨⟨_, hns⟩, Subgroup.mem_subgroupOf.mpr
        (hSinv n (hWN n hn) s (Subgroup.mem_subgroupOf.mp hs)), he⟩
    rcases hW2 A' hA'A hA'inv with h | h
    · left
      refine le_antisymm (fun s hs => ?_) hxS
      have h1 : γ ⟨s, hSB hs⟩ ∈ A' := ⟨⟨s, hSB hs⟩, Subgroup.mem_subgroupOf.mpr hs, rfl⟩
      rw [h, Subgroup.mem_bot] at h1
      exact (hker _).mp h1
    · right
      refine le_antisymm hSB (fun b hb => ?_)
      have h1 : γ ⟨b, hb⟩ ∈ A' := h ▸ ⟨⟨b, hb⟩, rfl⟩
      obtain ⟨s, hs, hsb⟩ := h1
      have h2 : γ (⟨b, hb⟩ * s⁻¹) = 1 := by rw [map_mul, map_inv, ← hsb, mul_inv_cancel]
      have h3 : (b : G) * (s : G)⁻¹ ∈ S := hxS ((hker _).mp h2)
      have e : b = (b * (s : G)⁻¹) * s := by group
      rw [e]
      exact S.mul_mem h3 (Subgroup.mem_subgroupOf.mp hs)
  ·
    obtain ⟨b, rfl⟩ := ha₀
    refine ⟨n₀, hWN n₀ hn₀, b, b.2, fun hcomm => hna₀ ?_⟩
    obtain ⟨hnb, he⟩ := hconj n₀ hn₀ b
    rw [← he]
    congr 1
    exact Subtype.ext (show (n₀ : G) * b * (n₀ : G)⁻¹ = b by rw [hcomm, mul_inv_cancel_right])
  ·
    intro H hHB hHinv hHsup hHinf φ hφH hφmul hφN
    have hH1 : ∀ h (hh : h ∈ H), γ ⟨h, hHB hh⟩ = 1 → h = 1 := by
      intro h hh h1
      have h2 : h ∈ H ⊓ Subgroup.zpowers x := ⟨hh, (hker _).mp h1⟩
      rw [hHinf] at h2
      exact Subgroup.mem_bot.mp h2
    have huniq : ∀ h (hh : h ∈ H) h' (hh' : h' ∈ H), γ ⟨h, hHB hh⟩ = γ ⟨h', hHB hh'⟩ →
        h = h' := by
      intro h hh h' hh' he
      have h1 : γ ⟨h * h'⁻¹, hHB (H.mul_mem hh (H.inv_mem hh'))⟩ = 1 := by
        have e : (⟨h * h'⁻¹, hHB (H.mul_mem hh (H.inv_mem hh'))⟩ : Bs) =
            ⟨h, hHB hh⟩ * (⟨h', hHB hh'⟩ : Bs)⁻¹ := rfl
        rw [e, map_mul, map_inv, he, mul_inv_cancel]
      have h2 := hH1 _ (H.mul_mem hh (H.inv_mem hh')) h1
      rw [mul_inv_eq_one] at h2
      exact h2
    have hex : ∀ a ∈ γ.range, ∃ h, ∃ hh : h ∈ H, γ ⟨h, hHB hh⟩ = a := by
      rintro _ ⟨b, rfl⟩
      have hxH : ∀ h ∈ H, x * h = h * x := fun h hh =>
        mul_comm_of_isElemAbelian hBs hxB (hHB hh)
      have hbsup : (b : G) ∈ H ⊔ Subgroup.zpowers x := by
        rw [hHsup]
        exact b.2
      obtain ⟨h, hh, j, hj⟩ := exists_mem_mul_pow_of_mem_sup hxH hbsup
      refine ⟨h, hh, ?_⟩
      have e : b = ⟨h, hHB hh⟩ * (⟨x, hxB⟩ : Bs) ^ j := Subtype.ext (by
        rw [Subgroup.coe_mul, Subgroup.coe_pow]
        exact hj)
      have hx1 : γ ⟨x, hxB⟩ = 1 := (hker _).mpr (Subgroup.mem_zpowers x)
      rw [e, map_mul, map_pow, hx1, one_pow, mul_one]
    let f : MulAut L → MulAut L := fun a =>
      if ha : ∃ h, ∃ hh : h ∈ H, γ ⟨h, hHB hh⟩ = a then
        γ ⟨φ ha.choose, hHB (hφH _ ha.choose_spec.choose)⟩
      else a
    have hf : ∀ h (hh : h ∈ H), f (γ ⟨h, hHB hh⟩) = γ ⟨φ h, hHB (hφH h hh)⟩ := by
      intro h hh
      have hex' : ∃ h', ∃ hh' : h' ∈ H, γ ⟨h', hHB hh'⟩ = γ ⟨h, hHB hh⟩ := ⟨h, hh, rfl⟩
      have heq : hex'.choose = h :=
        huniq _ hex'.choose_spec.choose _ hh hex'.choose_spec.choose_spec
      change (if ha : ∃ h', ∃ hh' : h' ∈ H, γ ⟨h', hHB hh'⟩ = γ ⟨h, hHB hh⟩ then
        γ ⟨φ ha.choose, hHB (hφH _ ha.choose_spec.choose)⟩ else γ ⟨h, hHB hh⟩) = _
      rw [dite_eq_left hex']
      congr 1
      exact Subtype.ext (congrArg φ heq)
    obtain ⟨c, hc⟩ := hW4 f
      (by
        intro a ha
        obtain ⟨h, hh, rfl⟩ := hex a ha
        rw [hf h hh]
        exact ⟨_, rfl⟩)
      (by
        intro a ha b hb
        obtain ⟨h, hh, rfl⟩ := hex a ha
        obtain ⟨h', hh', rfl⟩ := hex b hb
        have e : γ ⟨h, hHB hh⟩ * γ ⟨h', hHB hh'⟩ = γ ⟨h * h', hHB (H.mul_mem hh hh')⟩ := by
          rw [← map_mul]
          rfl
        rw [e, hf _ (H.mul_mem hh hh'), hf h hh, hf h' hh', ← map_mul]
        congr 1
        exact Subtype.ext (hφmul h hh h' hh'))
      (by
        intro n hn a ha
        obtain ⟨h, hh, rfl⟩ := hex a ha
        obtain ⟨hnh, he⟩ := hconj n hn ⟨h, hHB hh⟩
        have hnhH : (n : G) * h * (n : G)⁻¹ ∈ H := hHinv n (hWN n hn) h hh
        obtain ⟨hnφ, he'⟩ := hconj n hn ⟨φ h, hHB (hφH h hh)⟩
        have e1 : γ ⟨(n : G) * h * (n : G)⁻¹, hnh⟩ = γ ⟨(n : G) * h * (n : G)⁻¹, hHB hnhH⟩ :=
          rfl
        rw [← he, e1, hf _ hnhH, hf h hh, ← he']
        congr 1
        exact Subtype.ext (hφN n (hWN n hn) h hh))
    refine ⟨c, fun h hh => ?_⟩
    have h1 := hc _ ⟨⟨h, hHB hh⟩, rfl⟩
    rw [hf h hh, ← map_pow] at h1
    have hhc : h ^ c ∈ H := H.pow_mem hh c
    have e : ((⟨h, hHB hh⟩ : Bs) ^ c) = ⟨h ^ c, hHB hhc⟩ := rfl
    rw [e] at h1
    exact huniq _ (hφH h hh) _ hhc h1


end Irred

section Coord

open UCoord

theorem eq_bot_or_eq_top_of_permAutV {d p : ℕ} (hp : p.Prime) (hd : 2 ≤ d) (hpd : ¬ p ∣ d)
    (U : Subgroup ↥(sumZero d p))
    (hU : ∀ (σ : Equiv.Perm (Fin d)), ∀ f ∈ U, permAutV σ f ∈ U) : U = ⊥ ∨ U = ⊤ := by
  classical
  have := Fact.mk hp
  rcases U.bot_or_exists_ne_one with hbot | ⟨f, hfU, hf1⟩
  · exact Or.inl hbot
  right
  obtain ⟨i, j, hij⟩ : ∃ i j, crd f i ≠ crd f j := by
    by_contra h
    push Not at h
    apply hf1
    have hd0 : (d : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      exact hpd
    have hsum := sum_crd f
    have hc : ∀ k, crd f k = crd f ⟨0, by omega⟩ := fun k => h k _
    rw [Finset.sum_congr rfl (fun k _ => hc k), Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul] at hsum
    have h0 : crd f ⟨0, by omega⟩ = 0 := (mul_eq_zero.mp hsum).resolve_left hd0
    exact ext_crd fun k => by rw [hc k, h0, crd_one]
  have hij' : i ≠ j := fun h => hij (h ▸ rfl)
  have hroot : rootV i j ∈ U := by
    have h1 : f * (permAutV (Equiv.swap i j) f)⁻¹ ∈ U := U.mul_mem hfU (U.inv_mem (hU _ f hfU))
    rw [mul_inv_permAutV_swap hij' f] at h1
    have hc0 : crd f i - crd f j ≠ 0 := sub_ne_zero.mpr hij
    have h2 : (rootV i j ^ (crd f i - crd f j).val) ^ ((crd f i - crd f j)⁻¹).val =
        (rootV i j : ↥(sumZero d p)) := by
      refine ext_crd fun k => ?_
      rw [crd_pow, crd_pow, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, ← mul_assoc,
        inv_mul_cancel₀ hc0, one_mul]
    rw [← h2]
    exact U.pow_mem h1 _
  have hall : ∀ a b : Fin d, a ≠ b → rootV a b ∈ U := by
    intro a b hab
    obtain ⟨σ, hσa, hσb⟩ := exists_perm_apply_apply hij' hab
    rw [← hσa, ← hσb, ← permAutV_rootV]
    exact hU σ _ hroot
  set k₀ : Fin d := ⟨0, by omega⟩ with hk₀
  have hcrd : ∀ (s : Finset (Fin d)) (F : Fin d → ↥(sumZero d p)) (m : Fin d),
      crd (∏ k ∈ s, F k) m = ∑ k ∈ s, crd (F k) m := by
    intro s F m
    induction s using Finset.induction_on with
    | empty => rw [Finset.prod_empty, Finset.sum_empty, crd_one]
    | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, crd_mul, ih]
  rw [eq_top_iff]
  intro g _
  have hprod : (∏ k : Fin d, rootV k k₀ ^ (crd g k).val : ↥(sumZero d p)) ∈ U := by
    have hmem : ∀ k, (rootV k k₀ ^ (crd g k).val : ↥(sumZero d p)) ∈ U := by
      intro k
      by_cases hk : k = k₀
      · have h1 : (rootV k k₀ : ↥(sumZero d p)) = 1 :=
          ext_crd fun m => by rw [hk, crd_rootV, sub_self, crd_one]
        rw [h1, one_pow]
        exact U.one_mem
      · exact U.pow_mem (hall k k₀ hk) _
    have hind : ∀ s : Finset (Fin d), (∏ k ∈ s, rootV k k₀ ^ (crd g k).val : ↥(sumZero d p)) ∈ U := by
      intro s
      induction s using Finset.induction_on with
      | empty => rw [Finset.prod_empty]; exact U.one_mem
      | insert a s ha ih => rw [Finset.prod_insert ha]; exact U.mul_mem (hmem a) ih
    exact hind Finset.univ
  have heq : (∏ k : Fin d, rootV k k₀ ^ (crd g k).val : ↥(sumZero d p)) = g := by
    refine ext_crd fun m => ?_
    rw [hcrd]
    have e1 : ∀ k, crd (rootV k k₀ ^ (crd g k).val : ↥(sumZero d p)) m =
        (if m = k then crd g k else 0) - (if m = k₀ then crd g k else 0) := by
      intro k
      rw [crd_pow, ZMod.natCast_zmod_val, crd_rootV]
      split_ifs <;> ring
    rw [Finset.sum_congr rfl (fun k _ => e1 k)]
    have h1 : ∑ k, (if m = k then crd g k else 0) = crd g m := by simp
    have h2 : ∑ k, (if m = k₀ then crd g k else 0) = 0 := by
      by_cases hm : m = k₀
      · simp only [hm, ite_true]
        exact sum_crd g
      · simp [hm]
    calc ∑ k, ((if m = k then crd g k else 0) - if m = k₀ then crd g k else 0)
        = (∑ k, (if m = k then crd g k else 0)) - ∑ k, (if m = k₀ then crd g k else 0) :=
          Finset.sum_sub_distrib _ _
      _ = crd g m - 0 := by rw [h1, h2]
      _ = crd g m := sub_zero _
  rw [← heq]
  exact hprod

end Coord

section Unitary

open UCoord


theorem ggTorusIrredSC_unitary {K : Type} [Field K] [Finite K] {n d p : ℕ}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hd : 3 ≤ d) (hdq : (d, 2 ^ n) ≠ (3, 2))
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ n + 1) (hpd : ¬ p ∣ d) :
    GGTorusIrredSC p (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))
        (LargeEvenGUSet (Fin d) K (2 ^ n))) := by
  intro L' _ _ ψ hψ hker hperf A hA hAI h3 hsc
  have := Fact.mk hp
  have hZ := TableBUE.center_proj_eq_bot hK hd hdq
  have hIp : ∀ φ ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))
      (LargeEvenGUSet (Fin d) K (2 ^ n)), φ ^ p = 1 →
        φ ∈ Set.range (MulAut.conj : LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)) →*
          MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))) :=
    fun φ hφ hφp => InndiagSU.ggOutdiagPrime_unitary hK hn hd hdq hp hpq hpd φ hφ hφp
  have hcp := StdSubRestU.ggCenterPrime_unitary hK hn hd hdq hp hp2 hpd
  have hT := UModel.ggTorusPermEltSC_unitary hK hn (by omega) hp hp2 hpq hpd
  obtain ⟨Θ, hW, hP, -⟩ := exists_permModel hp hZ hIp hcp hT hψ hker hperf hA hAI h3 hsc
  obtain ⟨Ws, hWs1, hWs4⟩ := ggTorusSchurSC_of_permElt hp hp2 (by omega) hpd hZ hIp hcp hT L' ψ
    hψ hker hperf A hA hAI h3 hsc
  have hΘ : ∀ (m : L') (hm : MulAut.conj m ∈ Subgroup.normalizer (A : Set (MulAut L')))
      (σ : Equiv.Perm (Fin d)), ggConjAut A hm = MulAut.congr Θ (permAutV σ) →
      ∀ f, MulAut.conj m * (Θ f : MulAut L') * (MulAut.conj m)⁻¹ = Θ (permAutV σ f) := by
    intro m hm σ hmσ f
    have h1 := congrArg (fun φ : MulAut ↥A => ((φ (Θ f) : ↥A) : MulAut L')) hmσ
    simp only [ggConjAut_apply, MulAut.congr_apply, MulEquiv.trans_apply,
      MulEquiv.symm_apply_apply] at h1
    exact h1
  refine ⟨Ws ∪ {m | MulAut.conj m ∈ Subgroup.normalizer (A : Set (MulAut L'))}, ?_, ?_, ?_, ?_⟩
  · rintro m (hm | hm)
    · exact hWs1 m hm
    · exact hW m hm
  · intro A' hA'A hinv
    set U : Subgroup ↥(sumZero d p) := (A'.subgroupOf A).comap Θ.toMonoidHom with hU
    have hUinv : ∀ σ : Equiv.Perm (Fin d), ∀ f ∈ U, permAutV σ f ∈ U := by
      intro σ f hf
      obtain ⟨m, hm, hmσ⟩ := hP σ
      have h1 : MulAut.conj m * (Θ f : MulAut L') * (MulAut.conj m)⁻¹ ∈ A' :=
        hinv m (Or.inr hm) _ hf
      rw [hΘ m hm σ hmσ f] at h1
      exact h1
    rcases eq_bot_or_eq_top_of_permAutV hp (by omega) hpd U hUinv with h | h
    · left
      rw [eq_bot_iff]
      intro a ha
      have hf : Θ.symm ⟨a, hA'A ha⟩ ∈ U := by
        show ((Θ (Θ.symm ⟨a, hA'A ha⟩) : ↥A) : MulAut L') ∈ A'
        rw [MulEquiv.apply_symm_apply]
        exact ha
      rw [h, Subgroup.mem_bot] at hf
      have h2 : (⟨a, hA'A ha⟩ : ↥A) = 1 := by
        rw [← MulEquiv.apply_symm_apply Θ ⟨a, hA'A ha⟩, hf, map_one]
      rw [Subgroup.mem_bot]
      exact congrArg Subtype.val h2
    · right
      refine le_antisymm hA'A fun a ha => ?_
      have hf : Θ.symm ⟨a, ha⟩ ∈ U := by
        rw [h]
        trivial
      have h1 : ((Θ (Θ.symm ⟨a, ha⟩) : ↥A) : MulAut L') ∈ A' := hf
      rw [MulEquiv.apply_symm_apply] at h1
      exact h1
  · obtain ⟨i₀, i₁, h01⟩ : ∃ i₀ i₁ : Fin d, i₀ ≠ i₁ :=
      ⟨⟨0, by omega⟩, ⟨1, by omega⟩, by simp [Fin.ext_iff]⟩
    obtain ⟨m, hm, hmσ⟩ := hP (Equiv.swap i₀ i₁)
    refine ⟨m, Or.inr hm, Θ (rootV i₀ i₁), (Θ (rootV i₀ i₁)).2, fun heq => ?_⟩
    rw [hΘ m hm _ hmσ, permAutV_rootV, Equiv.swap_apply_left, Equiv.swap_apply_right] at heq
    have h1 := congrArg (fun g => crd g i₀) (Θ.injective (Subtype.ext heq))
    simp only [crd_rootV_left h01, crd_rootV_right h01.symm] at h1
    exact one_ne_zero (SpCoord.coord_eq_zero_of_eq_neg hp hp2 h1.symm)
  · intro f hfA hfmul hfW
    exact hWs4 f hfA hfmul fun m hm a ha => hfW m (Or.inl hm) a ha

theorem recipeUnitary_torusIrredSC {d n p : ℕ} (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1)
    (hn : 1 ≤ n) (hd : 3 ≤ d) (hdq : (d, 2 ^ n) ≠ (3, 2)) (hpd : ¬ p ∣ d) {Q : LargeEvenRawCont}
    (hQ : LargeEvenRecipeUnitary d (2 ^ n) Q) :
    LargeEvenRecipeUnitary d (2 ^ n) fun R _ I F => Q R I F ∧ GGTorusIrredSC p R I := by
  obtain ⟨K, _, _, hK, hQ⟩ := hQ
  exact ⟨K, inferInstance, inferInstance, hK, hQ, ggTorusIrredSC_unitary hK hn hd hdq hp
    (TableBU.ne_two_of_dvd_two_pow_add_one hn hpq) hpq hpd⟩

end Unitary

theorem ggTableBIrredInputOn_of_labelsSC {S : ℕ → LargeEvenLabel → Prop}
    (h : ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → LargeEvenInLambda2 lab → S p lab →
      LargeEvenLabelAll lab fun R _ I _ => GGTorusIrredSC p R I) :
    GGTableBIrredInputOn S := by
  intro G _ _ p B Bs x L D J hcfg hM
  have hp : p.Prime := hcfg.1.2.2.2.2.2.1.1
  obtain ⟨hL, lab, -, hraw⟩ := largeEvenMarking_and_labelAll (S := fun lab => S p lab)
    (fun lab hlab hs => h p lab hp hlab hs) (fun _ _ _ _ _ _ hP => hP.1) hM
  obtain ⟨R, _, I, F, -, -, θ, ⟨-, -, hBsN, hBs3⟩, hirr⟩ := largeEvenRawDatum_exists hraw
  exact ggTableBIrred_of_ggTorusIrredSC hcfg hL θ hBsN hBs3 hirr

end CorFourTwoOpen

open CorFourTwoOpen

section Labels


theorem largeEvenLabelAll_torusIrredSC_unitary {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (h : GGUnitaryCoprimeLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ => GGTorusIrredSC p R I := by
  obtain ⟨t, l, n⟩ := lab
  have hn : 1 ≤ n := hlab.1
  intro Q hQ
  rcases h with ⟨h, hpn, hpl⟩ | ⟨h, hl, hpn⟩
  · dsimp only at h hpn hpl
    subst h
    have hl2 : 2 ≤ l := hlab.2.1
    have hl2n : l = 2 → 2 ≤ n := hlab.2.2
    refine recipeUnitary_torusIrredSC hp hpn hn (by omega) ?_ hpl hQ
    intro heq
    simp only [Prod.mk.injEq] at heq
    have hn2 := hl2n (by omega)
    have h4 : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
    omega
  · dsimp only at h hl hpn
    subst h hl
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    rw [ite_eq_right (show ¬ (3 = 2) by decide), ite_eq_left (show (3 = 3) from rfl)] at hQ ⊢
    have hp2 : p ≠ 2 := TableBU.ne_two_of_dvd_two_pow_add_one hn hpn
    refine recipeUnitary_torusIrredSC hp hpn hn (by norm_num) (by simp) (fun h4 => hp2 ?_) hQ
    have h1 : p ∣ 2 ^ 2 := by norm_num; exact h4
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h1)

theorem ggTableBIrredInputOn_unitary : GGTableBIrredInputOn GGUnitaryCoprimeLabel :=
  ggTableBIrredInputOn_of_labelsSC fun _ _ hp hlab h =>
    largeEvenLabelAll_torusIrredSC_unitary hp hlab h

theorem ggTableBIrredInputOn_unitaryVac :
    GGTableBIrredInputOn fun p lab => GGUnitaryCoprimeLabel p lab ∧
      GGCorFourTwoOpenVacLabel p lab :=
  fun G _ _ p B Bs x L D J hC hL =>
    ggTableBIrredInputOn_unitary G p B Bs x L D J hC (hL.mono fun _ _ h => h.1)

theorem ggTableBCxInputOn_unitaryVac (ha₀ : GGLNoncyclicInput) :
    GGTableBCxInputOn fun p lab => GGUnitaryCoprimeLabel p lab ∧
      GGCorFourTwoOpenVacLabel p lab :=
  ggTableBCxInputOn_of_irred (ggBstarInnerDiagLInputOn_vac ha₀ GGUnitaryCoprimeLabel)
    ggTableBIrredInputOn_unitaryVac

theorem ggTableBModuleInputOn_unitaryVac (ha₀ : GGLNoncyclicInput) :
    GGTableBModuleInputOn fun p lab => GGUnitaryCoprimeLabel p lab ∧
      GGCorFourTwoOpenVacLabel p lab :=
  ggTableBModuleInputOn_of_irred (ggBstarInnerDiagLInputOn_vac ha₀ GGUnitaryCoprimeLabel)
    ggTableBIrredInputOn_unitaryVac

theorem ggTableBActionInputOn_unitaryVac (ha₀ : GGLNoncyclicInput) :
    GGTableBActionInputOn fun p lab => GGUnitaryCoprimeLabel p lab ∧
      GGCorFourTwoOpenVacLabel p lab :=
  ggTableBActionInputOn_of_irred (ggBstarInnerDiagLInputOn_vac ha₀ GGUnitaryCoprimeLabel)
    ggTableBIrredInputOn_unitaryVac

end Labels

end CFSG.StandardType

end
