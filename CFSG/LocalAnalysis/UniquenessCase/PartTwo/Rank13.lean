module

public import CFSG.LocalAnalysis.SectionRank.SubgroupRank
public import CFSG.Quasithin.H13.NQBlockPRankProduct
public import CFSG.RankThree.PartTwo.Sec4.T444.Coprime
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7L710CoverA
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalThreeInner
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.RankThree.PartOne.Census3.Interface
public import CFSG.RankThree.PartOne.S12.Hyp
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.RankThree.PartOne (pElementSubgroup)

variable {G : Type} [Group G] [Finite G]

theorem s13_Rank13_pRank_bot {p : ℕ} (hp : p.Prime) :
    CFSG.Open.pRank p (⊥ : Subgroup G) = 0 := by
  refine Nat.le_zero.mp (CFSG.SectionRank.pRank_le hp.one_lt fun E hE _ => ?_)
  rw [le_bot_iff.mp hE, pow_zero, Subgroup.card_bot]

theorem s13_pRank_sup_eq_add {p : ℕ} (hp : p.Prime) {A B : Subgroup G}
    (hAB : B ≤ Subgroup.centralizer (A : Set G)) (hdisj : A ⊓ B = ⊥) :
    CFSG.Open.pRank p (A ⊔ B) = CFSG.Open.pRank p A + CFSG.Open.pRank p B := by
  have hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a := fun a ha b hb =>
    (Subgroup.mem_centralizer_iff.mp (hAB hb)) a ha
  have hc : ∀ (m : ↥A) (n : ↥B), Commute (A.subtype m) (B.subtype n) :=
    fun m n => hcomm m m.2 n n.2
  let φ : ↥A × ↥B →* G := MonoidHom.noncommCoprod A.subtype B.subtype hc
  have hφ : ∀ (m : ↥A) (n : ↥B), φ (m, n) = (m : G) * (n : G) :=
    fun m n => MonoidHom.noncommCoprod_apply _ _ _ (m, n)
  have hinj : Function.Injective φ := by
    rintro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ h
    rw [hφ, hφ] at h
    have h1 : (a₁ : G)⁻¹ * (a₂ : G) = (b₁ : G) * (b₂ : G)⁻¹ := by
      calc (a₁ : G)⁻¹ * (a₂ : G)
          = (a₁ : G)⁻¹ * (a₂ * b₂) * (b₂ : G)⁻¹ := by group
        _ = (a₁ : G)⁻¹ * (a₁ * b₁) * (b₂ : G)⁻¹ := by rw [← h]
        _ = (b₁ : G) * (b₂ : G)⁻¹ := by group
    have hA : (a₁ : G)⁻¹ * (a₂ : G) ∈ A := mul_mem (inv_mem a₁.2) a₂.2
    have hB : (a₁ : G)⁻¹ * (a₂ : G) ∈ B := by
      rw [h1]; exact mul_mem b₁.2 (inv_mem b₂.2)
    have hbot : (a₁ : G)⁻¹ * (a₂ : G) ∈ (A ⊓ B : Subgroup G) := ⟨hA, hB⟩
    rw [hdisj, Subgroup.mem_bot] at hbot
    have ha : (a₁ : G) = (a₂ : G) := inv_mul_eq_one.mp hbot
    have hb : (b₁ : G) = (b₂ : G) := by
      have h2 : (b₁ : G) * (b₂ : G)⁻¹ = 1 := h1 ▸ hbot
      exact mul_inv_eq_one.mp h2
    exact Prod.ext (Subtype.ext ha) (Subtype.ext hb)
  have hmem : ∀ x, φ x ∈ A ⊔ B := by
    rintro ⟨a, b⟩
    rw [hφ a b]
    exact Subgroup.mul_mem_sup a.2 b.2
  let ψ : ↥A × ↥B →* ↥(A ⊔ B) := φ.codRestrict (A ⊔ B) hmem
  have hψinj : Function.Injective ψ :=
    (MonoidHom.injective_codRestrict φ (A ⊔ B) hmem).mpr hinj
  have hφrange : A ⊔ B ≤ φ.range :=
    sup_le (fun a ha => ⟨(⟨a, ha⟩, 1), by rw [hφ]; simp⟩)
      (fun b hb => ⟨(1, ⟨b, hb⟩), by rw [hφ]; simp⟩)
  have hψsurj : Function.Surjective ψ := by
    intro y
    obtain ⟨p, hp⟩ := hφrange y.2
    exact ⟨p, Subtype.ext (by change (φ p : G) = (y : G); exact hp)⟩
  let e : ↥A × ↥B ≃* ↥(A ⊔ B) := MulEquiv.ofBijective ψ ⟨hψinj, hψsurj⟩
  calc CFSG.Open.pRank p (A ⊔ B)
      = CFSG.Open.pRank p (⊤ : Subgroup ↥(A ⊔ B)) :=
        CFSG.SectionRank.pRank_eq_pRank_top_subgroup (A ⊔ B)
    _ = CFSG.Open.pRank p (⊤ : Subgroup (↥A × ↥B)) :=
        (CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e).symm
    _ = CFSG.pRank p (↥A × ↥B) :=
        (CFSG.SectionRank.pRank_eq_open_pRank_top p (↥A × ↥B)).symm
    _ = CFSG.pRank p ↥A + CFSG.pRank p ↥B := CFSG.Quasithin.H13.NQBlock.pRank_prod_eq hp
    _ = CFSG.Open.pRank p (⊤ : Subgroup ↥A) + CFSG.Open.pRank p (⊤ : Subgroup ↥B) := by
        rw [CFSG.SectionRank.pRank_eq_open_pRank_top p ↥A,
          CFSG.SectionRank.pRank_eq_open_pRank_top p ↥B]
    _ = CFSG.Open.pRank p A + CFSG.Open.pRank p B := by
        rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup A,
          ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup B]

theorem s13_pRank_iSup_eq_sum {ι : Type} [DecidableEq ι] {p : ℕ} (hp : p.Prime) (s : Finset ι)
    (J : ι → Subgroup G)
    (hcomm : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → J i ≤ Subgroup.centralizer (J j : Set G))
    (hdisj : ∀ i ∈ s, J i ⊓ (⨆ j ∈ s.erase i, J j) = ⊥) :
    CFSG.Open.pRank p (⨆ i ∈ s, J i) = ∑ i ∈ s, CFSG.Open.pRank p (J i) := by
  classical
  revert hcomm hdisj
  induction s using Finset.induction_on with
  | empty =>
      intro hcomm hdisj
      rw [← Finset.iSup_coe, Finset.coe_empty, iSup_emptyset, s13_Rank13_pRank_bot hp,
        Finset.sum_empty]
  | insert a s has ih =>
      intro hcomm hdisj
      have hcomm' : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → J i ≤ Subgroup.centralizer (J j : Set G) :=
        fun i hi j hj hij =>
          hcomm i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij
      have hdisj' : ∀ i ∈ s, J i ⊓ (⨆ j ∈ s.erase i, J j) = ⊥ := by
        intro i hi
        have hle : (⨆ j ∈ s.erase i, J j) ≤ (⨆ j ∈ (insert a s).erase i, J j) :=
          biSup_mono fun j hj => Finset.mem_erase.mpr
            ⟨(Finset.mem_erase.mp hj).1, Finset.mem_insert_of_mem (Finset.mem_erase.mp hj).2⟩
        refine le_bot_iff.mp ((inf_le_inf le_rfl hle).trans ?_)
        exact le_of_eq (hdisj i (Finset.mem_insert_of_mem hi))
      have hBa : (⨆ j ∈ s, J j) ≤ Subgroup.centralizer (J a : Set G) :=
        iSup₂_le fun j hj =>
          hcomm j (Finset.mem_insert_of_mem hj) a (Finset.mem_insert_self a s)
            (fun h => has (h ▸ hj))
      have hdisjA : J a ⊓ (⨆ j ∈ s, J j) = ⊥ := by
        simpa [Finset.erase_insert has] using hdisj a (Finset.mem_insert_self a s)
      rw [Finset.iSup_insert, s13_pRank_sup_eq_add hp hBa hdisjA, ih hcomm' hdisj',
        Finset.sum_insert has]

theorem s13_pRank_pElementSubgroup {p : ℕ} (hp : p.Prime) (H : Subgroup G) :
    CFSG.Open.pRank p (pElementSubgroup p H) = CFSG.Open.pRank p H := by
  refine le_antisymm ?_ ?_
  · exact CFSG.SectionRank.pRank_mono hp.one_lt ((Subgroup.closure_le H).mpr fun x hx => hx.1)
  · obtain ⟨E, hEH, hE, hcard⟩ := CFSG.SectionRank.exists_pRank hp.one_lt H
    refine CFSG.SectionRank.le_pRank hp.one_lt ?_ hE hcard
    intro x hx
    refine Subgroup.subset_closure ⟨hEH hx, ?_⟩
    rcases hp.eq_one_or_self_of_dvd (orderOf x) (orderOf_dvd_of_pow_eq_one (hE.2 x hx)) with
      h1 | h1
    · exact ⟨0, by rw [h1, pow_zero]⟩
    · exact ⟨1, by rw [h1, pow_one]⟩

theorem s13_pRank_map_eq {G' : Type} [Group G'] [Finite G'] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (f : G →* G') (hf : IsPGroup 2 f.ker) (H : Subgroup G) :
    CFSG.Open.pRank p (H.map f) = CFSG.Open.pRank p H := by
  have hker : ¬ p ∣ Nat.card f.ker := by
    obtain ⟨k, hk⟩ := hf.exists_card_eq
    rw [hk]
    intro hdvd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hdvd))
  refine le_antisymm (CFSG.RankThree.PartTwo.Sec4.pRank_map_le_of_not_dvd hp f hker H) ?_
  obtain ⟨E, hEH, hE, hcard⟩ := CFSG.SectionRank.exists_pRank hp.one_lt H
  have hEp : IsPGroup p ↥E := fun x => ⟨1, by
    rw [pow_one]
    exact Subtype.ext (hE.2 x x.2)⟩
  have hdisj : E ⊓ f.ker = ⊥ :=
    CFSG.RankThree.PartTwo.Sec4.inf_eq_bot_of_isPGroup_of_not_dvd hp hEp hker
  have hinj : ∀ x ∈ E, f x = 1 → x = 1 := by
    intro x hx hfx
    have hx' : x ∈ E ⊓ f.ker := ⟨hx, MonoidHom.mem_ker.mpr hfx⟩
    rw [hdisj, Subgroup.mem_bot] at hx'
    exact hx'
  have hcard' : Nat.card (E.map f) = p ^ CFSG.Open.pRank p H := by
    rw [CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7L710.card_map_of_le hinj
      (le_refl E), hcard]
  exact CFSG.SectionRank.le_pRank hp.one_lt (Subgroup.map_mono hEH)
    (CFSG.SectionRank.isElemAbelian_map hE f) hcard'

theorem s13_pElementSubgroup_map {G' : Type} [Group G'] {p : ℕ} (hp : p.Prime) (f : G →* G')
    (H : Subgroup G) :
    (pElementSubgroup p H).map f = pElementSubgroup p (H.map f) := by
  refine le_antisymm ?_ ?_
  · rw [pElementSubgroup, MonoidHom.map_closure]
    refine Subgroup.closure_mono ?_
    rintro y ⟨x, hx, rfl⟩
    refine ⟨Subgroup.mem_map_of_mem f hx.1, ?_⟩
    obtain ⟨k, hk⟩ := hx.2
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow hp).1 (hk ▸ orderOf_map_dvd f x)
    exact ⟨i, hi⟩
  · rw [pElementSubgroup]
    refine (Subgroup.closure_le _).mpr ?_
    rintro y ⟨hy, j, hj⟩
    obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.1 hy
    obtain ⟨n, e, hn, hfix⟩ := CFSG.AGLEmbedding.exists_pPart_pow hp h
    have hpow : (f h) ^ orderOf h = 1 := by rw [← map_pow, pow_orderOf_eq_one, map_one]
    have hpe : ∃ k, (f h) ^ p ^ k = 1 := ⟨j, by rw [← hj, pow_orderOf_eq_one]⟩
    refine Subgroup.mem_map.mpr ⟨h ^ n, ?_, ?_⟩
    · refine Subgroup.subset_closure ⟨pow_mem hh n, ?_⟩
      obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow hp).1 (orderOf_dvd_iff_pow_eq_one.mpr hn)
      exact ⟨i, hi⟩
    · rw [map_pow]
      exact hfix (f h) hpow hpe

theorem s13_exists_orderOf_of_pElementSubgroup_ne_bot {p : ℕ} (hp : p.Prime) {H : Subgroup G}
    (h : pElementSubgroup p H ≠ ⊥) : ∃ s ∈ pElementSubgroup p H, orderOf s = p := by
  have hgen : ∃ x ∈ ({x : G | x ∈ H ∧ ∃ k : ℕ, orderOf x = p ^ k} : Set G), x ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact h (le_antisymm ((Subgroup.closure_le (⊥ : Subgroup G)).mpr fun x hx => by
      rw [hcon x hx]
      exact Subgroup.mem_bot.mpr rfl) bot_le)
  obtain ⟨x, hxS, hxne⟩ := hgen
  obtain ⟨hxH, k, hk⟩ := hxS
  have hkpos : 0 < k := by
    by_contra hk0
    exact hxne (orderOf_eq_one_iff.mp (by rw [hk, Nat.eq_zero_of_not_pos hk0, pow_zero]))
  have hk1 : 1 ≤ k := hkpos
  set s : G := x ^ (p ^ (k - 1)) with hs_def
  have hs_pow : s ^ p = 1 := by
    rw [hs_def, ← pow_mul, show p ^ (k - 1) * p = p ^ k by
      rw [← pow_succ, Nat.sub_add_cancel hk1], ← hk, pow_orderOf_eq_one]
  have hs_ne : s ≠ 1 := by
    intro hs1
    have hdvd : orderOf x ∣ p ^ (k - 1) := by
      rw [hs_def] at hs1
      exact orderOf_dvd_iff_pow_eq_one.mpr hs1
    rw [hk] at hdvd
    have hle := Nat.le_of_dvd (pow_pos hp.pos (k - 1)) hdvd
    have hlt : p ^ (k - 1) < p ^ k :=
      Nat.pow_lt_pow_right hp.one_lt (Nat.sub_one_lt hkpos.ne')
    omega
  have horder : orderOf s = p := by
    have hdvd : orderOf s ∣ p := orderOf_dvd_iff_pow_eq_one.mpr hs_pow
    rcases hp.eq_one_or_self_of_dvd (orderOf s) hdvd with h1 | h1
    · exact absurd (orderOf_eq_one_iff.mp h1) hs_ne
    · exact h1
  refine ⟨s, Subgroup.subset_closure ⟨?_, ⟨1, by rw [horder, pow_one]⟩⟩, horder⟩
  rw [hs_def]
  exact pow_mem hxH (p ^ (k - 1))

theorem s13_exists_pPart_mul {p : ℕ} (hp : p.Prime) {A B : Subgroup G}
    (hAB : B ≤ Subgroup.centralizer (A : Set G)) {x a b : G} (hx : ∃ k : ℕ, x ^ p ^ k = 1)
    (ha : a ∈ A) (hb : b ∈ B) (hxab : x = a * b) :
    ∃ a' ∈ pElementSubgroup p A, ∃ b' ∈ pElementSubgroup p B, x = a' * b' := by
  have hab : Commute a b := (Subgroup.mem_centralizer_iff.mp (hAB hb)) a ha
  obtain ⟨n, e, hn, hfix⟩ := CFSG.AGLEmbedding.exists_pPart_pow hp ((a, b) : G × G)
  have hpair : (a, b) ^ orderOf (a, b) = 1 := pow_orderOf_eq_one (a, b)
  have hab1 : a ^ orderOf (a, b) = 1 := by
    have h := congrArg Prod.fst hpair
    rw [Prod.pow_mk] at h
    exact h
  have hbb1 : b ^ orderOf (a, b) = 1 := by
    have h := congrArg Prod.snd hpair
    rw [Prod.pow_mk] at h
    exact h
  have hx1 : x ^ orderOf (a, b) = 1 := by
    rw [hxab, hab.mul_pow, hab1, hbb1, mul_one]
  have hxn : x ^ n = x := hfix x hx1 hx
  have hna : (a ^ n) ^ p ^ e = 1 := by
    have h := congrArg Prod.fst hn
    rw [Prod.pow_mk] at h
    exact h
  have hnb : (b ^ n) ^ p ^ e = 1 := by
    have h := congrArg Prod.snd hn
    rw [Prod.pow_mk] at h
    exact h
  refine ⟨a ^ n, Subgroup.subset_closure ⟨pow_mem ha n, ?_⟩,
    b ^ n, Subgroup.subset_closure ⟨pow_mem hb n, ?_⟩, ?_⟩
  · obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow hp).1 (orderOf_dvd_iff_pow_eq_one.mpr hna)
    exact ⟨i, hi⟩
  · obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow hp).1 (orderOf_dvd_iff_pow_eq_one.mpr hnb)
    exact ⟨i, hi⟩
  · rw [← hxn, hxab, hab.mul_pow]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
