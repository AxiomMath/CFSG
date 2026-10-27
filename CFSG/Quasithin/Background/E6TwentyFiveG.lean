module

public import CFSG.Quasithin.Background.E6TwentyFiveC
public import CFSG.Quasithin.Background.E6TwentyFiveD
public import CFSG.Quasithin.Background.E6TwentyFiveF
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
public import CFSG.Quasithin.Background.E6TwentyFiveE
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.Quasithin

namespace E6

open CFSG.Open CFSG.QuasithinUnique CFSG.RankThree.PartOne CFSG.LocalAnalysis.ComponentInitial

section Endgame

variable {G : Type} [Group G] [Finite G]

theorem mem_of_inner_pElem {U L : Subgroup G} (hLU : L ≤ Subgroup.centralizer (U : Set G))
    (hZ : IsPGroup 2 ↥(Subgroup.center ↥L)) [Group.IsPerfect L] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hrank : CFSG.Open.pRank p (Subgroup.normalizer (U : Set G)) ≤ 2) {a b : G}
    (haL : a ∈ L) (hbL : b ∈ L) (hab : IsPair p a b) {y : G} {k : ℕ} (hyk : y ^ p ^ k = 1)
    (hyU : y ∈ Subgroup.normalizer (U : Set G)) (hyL : y ∈ Subgroup.normalizer (L : Set G))
    (ℓ : ↥L) (hinner : centerQuotientConj L ⟨y, hyL⟩ = MulAut.conj (ℓ : L ⧸ Subgroup.center L)) :
    y ∈ L := by
  have : Fact p.Prime := ⟨hp⟩
  have hc := mul_inv_mem_centralizer_of_eq_conj hyL ℓ hinner
  rcases exists_orderOf_eq_or_mem hZ hp hp2 hyk ℓ.2 hc with ⟨x, hxz, hxo⟩ | hyL'
  · exfalso
    obtain ⟨hab, ha, hb, ha1, hba⟩ := hab
    have hLN : L ≤ Subgroup.normalizer (U : Set G) :=
      hLU.trans (Subgroup.centralizer_le_normalizer _)
    have hcN : y * (ℓ : G)⁻¹ ∈ Subgroup.normalizer (U : Set G) :=
      Subgroup.mul_mem _ hyU (Subgroup.inv_mem _ (hLN ℓ.2))
    have hxN : x ∈ Subgroup.normalizer (U : Set G) := (Subgroup.zpowers_le.mpr hcN) hxz
    have hxC : x ∈ Subgroup.centralizer (L : Set G) := (Subgroup.zpowers_le.mpr hc) hxz
    have hxp : x ^ p = 1 := by rw [← hxo]; exact pow_orderOf_eq_one x
    have hxL : x ∉ L := by
      intro hxL
      obtain ⟨j, hj⟩ := hZ ⟨⟨x, hxL⟩, Subgroup.mem_center_iff.mpr fun l =>
        Subtype.ext (Subgroup.mem_centralizer_iff.mp hxC l l.2)⟩
      have hj' : x ^ 2 ^ j = 1 := by
        have := congrArg (fun w : ↥(Subgroup.center ↥L) => ((w : ↥L) : G)) hj
        simpa using this
      have hd := orderOf_dvd_of_pow_eq_one hj'
      rw [hxo] at hd
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hd))
    have hcax : Commute a x := Subgroup.mem_centralizer_iff.mp hxC a haL
    have hcbx : Commute b x := Subgroup.mem_centralizer_iff.mp hxC b hbL
    have h3 := three_le_pRank_of_elems (C₁ := Subgroup.zpowers a) (C₂ := L) (hLN haL) (hLN hbL)
      hxN hab hcax hcbx ha hb hxp ha1 (Subgroup.mem_zpowers a) hba haL hbL hxL
    omega
  · exact hyL'

theorem exists_conj_of_congr_mem_range {A B : Type*} [Group A] [Group B] (ε : A ≃* B)
    {β : MulAut A} (h : MulAut.congr ε β ∈ (MulAut.conj : B →* MulAut B).range) :
    ∃ a : A, β = MulAut.conj a := by
  obtain ⟨z, hz⟩ := h
  refine ⟨ε.symm z, MulEquiv.ext fun q => ?_⟩
  have h1 := congrArg (fun φ : MulAut B => φ (ε q)) hz
  simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
    MulAut.conj_apply] at h1
  apply ε.injective
  rw [MulAut.conj_apply, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, h1]

omit [Finite G] in
theorem centerQuotientConj_eq_conj {L : Subgroup G} {y : G}
    (hy : y ∈ Subgroup.normalizer (L : Set G)) {ℓ : ↥L}
    (h : L.normalizerMonoidHom ⟨y, hy⟩ = MulAut.conj ℓ) :
    centerQuotientConj L ⟨y, hy⟩ = MulAut.conj (ℓ : L ⧸ Subgroup.center L) := by
  ext q
  induction q using QuotientGroup.induction_on with
  | H l =>
    change ((L.normalizerMonoidHom ⟨y, hy⟩ l : L) : L ⧸ Subgroup.center L) = _
    rw [h, MulAut.conj_apply, MulAut.conj_apply, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
      QuotientGroup.mk_inv]

end Endgame

theorem e625SLeTwoLie_holds : E625SLeTwoLie := by
  intro G _ _ T M V U L X hV hset hD hLc hlie s Y Vs hB
  classical
  have hD' := hD
  obtain ⟨hLU, hLn, hLM, hCL, hXLM, hXcyc, hXcard, hUX1, hUX2, hreg, hnorm, hNL, hLMX, -⟩ := hD'
  obtain ⟨h, hm, hU, hr, hU1, hUm⟩ := hset
  have hV2 : IsPGroup 2 V := h.isPGroup_V
  have hXMU : X ≤ M ⊓ Subgroup.centralizer (U : Set G) :=
    le_inf (hXLM.trans inf_le_right) ((hXLM.trans inf_le_left).trans hLU)
  obtain ⟨-, hfixmap, -⟩ := hyp102_autI hV h hU hU1 hUm hXMU hXcyc hXcard hUX2 hreg hnorm
  obtain ⟨⟨hYsup, hYind, hYcomm⟩, -, -, ⟨-, htrans⟩, hdich⟩ := hB
  obtain ⟨i₀, hXY₀⟩ : ∃ i₀, autI hV X ≤ Y i₀ := by
    rcases hdich with ⟨i, hi⟩ | ⟨-, i, hi, -⟩
    · exact ⟨i, hi.le⟩
    · exact ⟨i, hi⟩
  by_contra hs
  push Not at hs
  obtain ⟨i₁, hi₁⟩ : ∃ i₁ : Fin s, i₁ ≠ i₀ := by
    by_contra hall
    push Not at hall
    have h1 : (Finset.univ : Finset (Fin s)) ⊆ {i₀} := fun k _ => by simp [hall k]
    have h2 := Finset.card_le_card h1
    simp only [Finset.card_univ, Fintype.card_fin, Finset.card_singleton] at h2
    omega
  obtain ⟨i₂, hi₂₀, hi₂₁⟩ : ∃ i₂ : Fin s, i₂ ≠ i₀ ∧ i₂ ≠ i₁ := by
    by_contra hall
    push Not at hall
    have h1 : (Finset.univ : Finset (Fin s)) ⊆ {i₀, i₁} := fun k _ => by
      by_cases hk : k = i₀
      · simp [hk]
      · simp [hall k hk]
    have h2 := (Finset.card_le_card h1).trans (Finset.card_insert_le _ _)
    simp only [Finset.card_univ, Fintype.card_fin, Finset.card_singleton] at h2
    omega
  set n := E3.mQuot V U with hndef
  have hn0 : n ≠ 0 := by omega
  have h4 : 4 ≤ 2 ^ n :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hU1
  have hodd : ∀ p : ℕ, p ∣ 2 ^ n - 1 → p ≠ 2 := by
    rintro p hpd rfl
    have he : Even (2 ^ n) := (Nat.even_pow' hn0).2 even_two
    have ho : Odd (2 ^ n - 1) := Nat.Even.sub_odd (by omega) he odd_one
    exact (Nat.not_even_iff_odd.2 ho) (even_iff_two_dvd.2 hpd)
  have hO := oddCoreIn_eq_bot_of_maximal h hU (maximal_of_eq_rParam h hr) hU1
  have hZ := isPGroup_center_of_oddCoreIn_eq_bot hLU hLn hO
  have : Group.IsPerfect ↥L := by
    have h1 : Group.IsPerfect ↥(L.subgroupOf (Subgroup.centralizer (U : Set G))) := hLc.2.1.1
    exact Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hLU).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hLU).surjective
  have hrank : ∀ p : ℕ, p.Prime → p ≠ 2 →
      CFSG.Open.pRank p (Subgroup.normalizer (U : Set G)) ≤ 2 := fun p hp hp2 =>
    (A1b.pRank_le_evenRank hp hp2 ⟨U, hU.2.1, hV2.to_le hU.1, rfl⟩).trans h.qtke.2.2
  have hnormU : ∀ y ∈ Subgroup.normalizer (V : Set G),
      (∀ hy : y ∈ Subgroup.normalizer (V : Set G), ∀ ξ ∈ autI hV X,
        convI hV ⟨y, hy⟩ * ξ = ξ * convI hV ⟨y, hy⟩) → y ∈ Subgroup.normalizer (U : Set G) := by
    intro y hyN hc
    have hle : U.map (MulAut.conj y).toMonoidHom ≤ U := by
      rintro _ ⟨u, hu, rfl⟩
      rw [← hfixmap] at hu ⊢
      obtain ⟨w, hw, rfl⟩ := hu
      refine ⟨convI hV ⟨y, hyN⟩ w, fun ξ hξ => ?_, ?_⟩
      · rw [← MulAut.mul_apply, ← hc hyN ξ hξ, MulAut.mul_apply, hw ξ hξ]
      · rw [E3.valHom_apply, convI_apply_val]
        rfl
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact Subgroup.eq_of_le_of_card_ge hle
      (Subgroup.card_map_of_injective (MulAut.conj y).injective).ge
  have hsupC : Y i₁ ⊔ Y i₂ ≤ Subgroup.centralizer (Y i₀ : Set (MulAut (IntMod V hV))) := by
    refine sup_le (fun φ hφ => ?_) (fun φ hφ => ?_) <;> rw [Subgroup.mem_centralizer_iff] <;>
      intro ξ hξ
    · exact hYcomm i₀ i₁ (Ne.symm hi₁) ξ hξ φ hφ
    · exact hYcomm i₀ i₂ (Ne.symm hi₂₀) ξ hξ φ hφ
  have hdisj : ∀ φ, φ ∈ Y i₀ → φ ∈ Y i₁ ⊔ Y i₂ → φ = 1 := by
    intro φ h0 h12
    have hle : Y i₁ ⊔ Y i₂ ≤ ⨆ (j : Fin s) (_ : j ≠ i₀), Y j :=
      sup_le (le_iSup₂_of_le i₁ hi₁ le_rfl) (le_iSup₂_of_le i₂ hi₂₀ le_rfl)
    have hd := (hYind i₀).mono_right hle
    exact (Subgroup.disjoint_def.mp hd) h0 h12
  have hNU : ∀ g : Subgroup.normalizer (V : Set G), convI hV g ∈ Y i₁ ⊔ Y i₂ →
      (g : G) ∈ Subgroup.normalizer (U : Set G) := by
    intro g hg
    refine hnormU g g.2 fun hy ξ hξ => ?_
    exact (Subgroup.mem_centralizer_iff.mp (hsupC hg) ξ (hXY₀ hξ)).symm
  have hNLg : ∀ g : Subgroup.normalizer (V : Set G), (g : G) ∈ M → convI hV g ∈ Y i₁ ⊔ Y i₂ →
      (g : G) ∈ Subgroup.normalizer (L : Set G) :=
    fun g hgM hg => hNL g ⟨hgM, g.2⟩ (hNU g hg)
  have hLX : ∀ g : Subgroup.normalizer (V : Set G), (g : G) ∈ L → (g : G) ∈ M →
      convI hV g ∈ Y i₀ := fun g hgL hgM => hXY₀ ((mem_autI hV).2 ⟨g, hLMX ⟨hgL, hgM⟩, rfl⟩)
  have hel : ∀ i : Fin s, ∀ p : ℕ, p.Prime → p ∣ 2 ^ n - 1 →
      ∃ g : Subgroup.normalizer (V : Set G), (g : G) ∈ M ∧ (∃ b : ℕ, (g : G) ^ p ^ b = 1) ∧
        convI hV g ∈ Y i ∧ orderOf (convI hV g) = p ^ padicValNat p (2 ^ n - 1) := by
    intro i p hp hpd
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨φ, hφM, hφ⟩ := htrans i₀ i
    obtain ⟨ξ, hξ⟩ := hXcyc.exists_generator
    have hξo : orderOf (ξ : MulAut (IntMod V hV)) = 2 ^ n - 1 := by
      rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hξ, hXcard]
    set ξ₁ := φ * (ξ : MulAut (IntMod V hV)) * φ⁻¹ with hξ₁
    have hξ₁Y : ξ₁ ∈ Y i := by
      rw [← hφ]
      exact ⟨ξ, hXY₀ ξ.2, rfl⟩
    have hξ₁o : orderOf ξ₁ = 2 ^ n - 1 := by
      rw [← hξo]
      exact MulEquiv.orderOf_eq (MulAut.conj φ) _
    set a := padicValNat p (2 ^ n - 1) with ha
    have hdvd : p ^ a ∣ 2 ^ n - 1 := pow_padicValNat_dvd
    set ξ₂ := ξ₁ ^ ((2 ^ n - 1) / p ^ a) with hξ₂
    have hξ₂o : orderOf ξ₂ = p ^ a := by
      rw [hξ₂, ← hξ₁o]
      exact orderOf_pow_orderOf_div (by rw [hξ₁o]; omega) (by rw [hξ₁o]; exact hdvd)
    have hξ₂Y : ξ₂ ∈ Y i := Subgroup.pow_mem _ hξ₁Y _
    have hξ₂M : ξ₂ ∈ autI hV M :=
      e624Y_le hV (hXLM.trans inf_le_right) (hYsup ▸ (le_iSup Y i) hξ₂Y)
    obtain ⟨g₀, hg₀M, hg₀⟩ := (mem_autI hV).1 hξ₂M
    obtain ⟨k, b, hk1, hk2⟩ := exists_pow_orderOf_eq (convI hV) hp (g := g₀)
      (by rw [hg₀, hξ₂o])
    refine ⟨g₀ ^ k, M.pow_mem hg₀M k, ⟨b, ?_⟩, ?_, hk2⟩
    · have h1 := pow_orderOf_eq_one (g₀ ^ k)
      rw [hk1] at h1
      have h2 := congrArg Subtype.val h1
      simpa using h2
    · rw [map_pow, hg₀]
      exact Subgroup.pow_mem _ hξ₂Y k
  have hfinal : ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ a b : G, a ∈ L → b ∈ L → IsPair p a b →
      ∀ g : Subgroup.normalizer (V : Set G), (g : G) ∈ M → (∃ k : ℕ, (g : G) ^ p ^ k = 1) →
      convI hV g ∈ Y i₁ ⊔ Y i₂ → convI hV g ≠ 1 →
      ∀ hgL : (g : G) ∈ Subgroup.normalizer (L : Set G),
      (∃ ℓ : ↥L, centerQuotientConj L ⟨g, hgL⟩ = MulAut.conj (ℓ : L ⧸ Subgroup.center L)) →
      False := by
    intro p hp hp2 a b haL hbL hab g hgM ⟨k, hgk⟩ hgY hg1 hgL ⟨ℓ, hℓ⟩
    have hgLL := mem_of_inner_pElem hLU hZ hp hp2 (hrank p hp hp2) haL hbL hab hgk
      (hNU g hgY) hgL ℓ hℓ
    exact hg1 (hdisj _ (hLX g hgLL hgM) hgY)
  have hgen : ∀ p : ℕ, p.Prime → p ∣ 2 ^ n - 1 → ∀ c : ℕ, ¬ p ∣ c →
      (∀ x : Subgroup.normalizer (L : Set G), ∃ ℓ : ↥L,
        centerQuotientConj L (x ^ (c * n)) = MulAut.conj (ℓ : L ⧸ Subgroup.center L)) →
      False := by
    intro p hp hpd c hc hP
    have : Fact p.Prime := ⟨hp⟩
    have hp2 := hodd p hpd
    obtain ⟨a, b, haL, hbL, hab⟩ := exists_pair_of_lie hZ hlie hp hp2 hpd
    obtain ⟨g, hgM, ⟨k, hgk⟩, hgY, hgo⟩ := hel i₁ p hp hpd
    have hgL := hNLg g hgM (Subgroup.mem_sup_left hgY)
    refine hfinal p hp hp2 a b haL hbL hab (g ^ (c * n)) (M.pow_mem hgM _) ⟨k, ?_⟩ ?_ ?_
      (Subgroup.pow_mem _ hgL _) (hP ⟨g, hgL⟩)
    · rw [SubgroupClass.coe_pow, ← pow_mul, mul_comm, pow_mul, hgk, one_pow]
    · rw [map_pow]
      exact Subgroup.pow_mem _ (Subgroup.mem_sup_left hgY) _
    · rw [map_pow]
      exact pow_ne_one_of_orderOf hp2 hn0 hpd hc hgo
  have hlie₀ := hlie
  rcases hlie₀ with hPSL | hSp
  ·
    obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hPSL
    let ε : (↥L ⧸ Subgroup.center ↥L) ≃* LinearFlag.projectiveSL 3 K :=
      (e.trans
        (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 K).symm).trans
        (LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 K)
    have hPε : ∀ x : Subgroup.normalizer (L : Set G),
        MulAut.congr ε (centerQuotientConj L x) ∈ (MulAut.conj :
          LinearFlag.projectiveSL 3 K →* MulAut _).range →
        ∃ ℓ : ↥L, centerQuotientConj L x = MulAut.conj (ℓ : L ⧸ Subgroup.center L) := by
      intro x hx
      obtain ⟨q, hq⟩ := exists_conj_of_congr_mem_range ε hx
      obtain ⟨ℓ, rfl⟩ := QuotientGroup.mk_surjective q
      exact ⟨ℓ, hq⟩
    rcases (by omega : n = 2 ∨ 3 ≤ n) with hn2 | hn3
    ·
      have hK4 : Nat.card K = 2 ^ 2 := by rw [hK, hn2]
      have hpd3 : 3 ∣ 2 ^ n - 1 := by
        rw [hn2]
        norm_num
      have hv3 : padicValNat 3 (2 ^ n - 1) = 1 := by
        rw [hn2]
        exact padicValNat_self (p := 3)
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      obtain ⟨a, b, haL, hbL, hab⟩ := exists_pair_of_lie hZ hlie Nat.prime_three (by norm_num) hpd3
      obtain ⟨g₁, hg₁M, ⟨b₁, hg₁b⟩, hg₁Y, hg₁o⟩ := hel i₁ 3 Nat.prime_three hpd3
      obtain ⟨g₂, hg₂M, ⟨b₂, hg₂b⟩, hg₂Y, hg₂o⟩ := hel i₂ 3 Nat.prime_three hpd3
      rw [hv3, pow_one] at hg₁o hg₂o
      have hg₁L := hNLg g₁ hg₁M (Subgroup.mem_sup_left hg₁Y)
      have hg₂L := hNLg g₂ hg₂M (Subgroup.mem_sup_right hg₂Y)
      have hβ : ∀ (g : Subgroup.normalizer (V : Set G)) (hgL : (g : G) ∈
          Subgroup.normalizer (L : Set G)) (b : ℕ), (g : G) ^ 3 ^ b = 1 →
          MulAut.congr ε (centerQuotientConj L ⟨g, hgL⟩) ^ 3 ^ b = 1 := by
        intro g hgL b hgb
        have h1 : (⟨g, hgL⟩ : Subgroup.normalizer (L : Set G)) ^ 3 ^ b = 1 := Subtype.ext hgb
        rw [← map_pow, ← map_pow, h1, map_one, map_one]
      by_cases hβ₁I : MulAut.congr ε (centerQuotientConj L ⟨g₁, hg₁L⟩) ∈ (MulAut.conj :
          LinearFlag.projectiveSL 3 K →* MulAut _).range
      · refine hfinal 3 Nat.prime_three (by norm_num) a b haL hbL hab g₁ hg₁M ⟨b₁, hg₁b⟩
          (Subgroup.mem_sup_left hg₁Y) ?_ hg₁L (hPε _ hβ₁I)
        intro h1
        rw [h1, orderOf_one] at hg₁o
        norm_num at hg₁o
      · obtain ⟨k, hk⟩ := exists_mul_pow_mem_inner_L34 hK4 (hβ g₁ hg₁L b₁ hg₁b)
          (hβ g₂ hg₂L b₂ hg₂b) hβ₁I
        set w : Subgroup.normalizer (V : Set G) := g₂ * g₁ ^ k with hw
        have hwY : convI hV w ∈ Y i₁ ⊔ Y i₂ := by
          rw [hw, map_mul, map_pow]
          exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hg₂Y)
            (Subgroup.pow_mem _ (Subgroup.mem_sup_left hg₁Y) k)
        have hcomm : Commute (convI hV g₁) (convI hV g₂) :=
          hYcomm i₁ i₂ (Ne.symm hi₂₁) _ hg₁Y _ hg₂Y
        have hu₁ : convI hV g₁ ^ 3 = 1 := by
          rw [← hg₁o]
          exact pow_orderOf_eq_one _
        have hu₂ : convI hV g₂ ^ 3 = 1 := by
          rw [← hg₂o]
          exact pow_orderOf_eq_one _
        have hwo : orderOf (convI hV w) = 3 ^ 1 := by
          rw [pow_one]
          apply orderOf_eq_prime
          · rw [hw, map_mul, map_pow, ((hcomm.symm).pow_right k).mul_pow, hu₂, one_mul, ← pow_mul,
              mul_comm k 3, pow_mul, hu₁, one_pow]
          · rw [hw, map_mul, map_pow]
            intro h1
            have h2 : convI hV g₂ = (convI hV g₁ ^ k)⁻¹ := eq_inv_of_mul_eq_one_left h1
            have h3 : convI hV g₂ ∈ Y i₁ ⊓ Y i₂ := by
              refine ⟨?_, hg₂Y⟩
              rw [h2]
              exact Subgroup.inv_mem _ (Subgroup.pow_mem _ hg₁Y k)
            rw [disjoint_iff.mp (hYind.pairwiseDisjoint (Ne.symm hi₂₁)), Subgroup.mem_bot] at h3
            rw [h3, orderOf_one] at hg₂o
            norm_num at hg₂o
        obtain ⟨k', b', hk'1, hk'2⟩ := exists_pow_orderOf_eq (convI hV) Nat.prime_three hwo
        have hwM : (w : G) ∈ M := M.mul_mem hg₂M (M.pow_mem hg₁M k)
        have hwL : (w : G) ∈ Subgroup.normalizer (L : Set G) :=
          Subgroup.mul_mem _ hg₂L (Subgroup.pow_mem _ hg₁L k)
        refine hfinal 3 Nat.prime_three (by norm_num) a b haL hbL hab (w ^ k')
          (M.pow_mem hwM k') ⟨b', ?_⟩ ?_ ?_ (Subgroup.pow_mem _ hwL k') (hPε _ ?_)
        · have h1 := pow_orderOf_eq_one (w ^ k')
          rw [hk'1] at h1
          have h2 := congrArg Subtype.val h1
          simpa using h2
        · rw [map_pow]
          exact Subgroup.pow_mem _ hwY k'
        · intro h1
          rw [h1, orderOf_one] at hk'2
          norm_num at hk'2
        · have e1 : (⟨((w ^ k' : Subgroup.normalizer (V : Set G)) : G),
              Subgroup.pow_mem _ hwL k'⟩ : Subgroup.normalizer (L : Set G)) =
              ((⟨g₂, hg₂L⟩ : Subgroup.normalizer (L : Set G)) * ⟨g₁, hg₁L⟩ ^ k) ^ k' := rfl
          rw [e1, map_pow, map_pow, map_mul, map_mul, map_pow, map_pow]
          exact Subgroup.pow_mem _ hk k'
    · obtain ⟨p, hp, hpd, hp3⟩ := exists_prime_dvd_two_pow_sub_one_ne_three hn3
      refine hgen p hp hpd 6 ?_ fun x => hPε _ ?_
      · intro h6
        rcases (Nat.Prime.dvd_mul hp).mp (show p ∣ 2 * 3 from h6) with h | h
        · exact hodd p hpd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)
        · exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h)
      · rw [map_pow, map_pow]
        exact pow_six_mul_mem_inner_projectiveSL (by omega) hK _
  ·
    obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hSp
    have : CharP K 2 := by
      have := Fintype.ofFinite K
      exact charP_of_card_eq_prime_pow (by rwa [← Nat.card_eq_fintype_card])
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (show 2 ^ n - 1 ≠ 1 by omega)
    refine hgen p hp hpd 2 (fun h => hodd p hpd ((Nat.prime_dvd_prime_iff_eq hp
      Nat.prime_two).mp h)) fun x => ?_
    have hin := pow_two_mul_mem_inner_sp4 (by omega) hK (MulAut.congr e (L.normalizerMonoidHom x))
    rw [← map_pow (MulAut.congr e), ← map_pow L.normalizerMonoidHom] at hin
    obtain ⟨ℓ, hℓ⟩ := exists_conj_of_congr_mem_range e hin
    exact ⟨ℓ, centerQuotientConj_eq_conj _ hℓ⟩

theorem e625SLeTwo_holds : E625SLeTwo :=
  e625SLeTwo_of e625SLeTwoLie_holds

end E6

end CFSG.Quasithin
