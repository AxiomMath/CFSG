module

public import CFSG.RankThree.PartTwo.Sec11.Item1120V0BarFam
public import CFSG.RankThree.PartTwo.Sec11.Item1120V0BarCount
public import CFSG.RankThree.PartTwo.Sec11.KS11Lie2ProofExc

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.ABGLocalTools (IsSylowOf)

namespace Item1120V0Bar

section PureL3

theorem range_conj_normal (Z : Type) [Group Z] :
    ((MulAut.conj : Z →* MulAut Z).range).Normal := by
  refine ⟨fun n hn g => ?_⟩
  obtain ⟨z, rfl⟩ := MonoidHom.mem_range.mp hn
  refine MonoidHom.mem_range.mpr ⟨g z, ?_⟩
  ext x
  simp [MulAut.mul_apply, MulAut.conj_apply, MulAut.apply_inv_self, map_mul, map_inv]

theorem conj_mem_zpowers_conj {Z : Type} [Group Z] {g x : Z}
    (hx : x ∈ Subgroup.zpowers g) : MulAut.conj x ∈ Subgroup.zpowers (MulAut.conj g) := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  rw [map_zpow]
  exact zpow_mem (Subgroup.mem_zpowers _) k

theorem card_le_three_mul_card_inf {A : Type*} [Group A] [Finite A] (N : Subgroup A) [N.Normal]
    {σ : A} (hσ3 : σ ^ 3 ∈ N) {P : Subgroup A} (hP : P ≤ N ⊔ Subgroup.zpowers σ) :
    Nat.card P ≤ 3 * Nat.card (P ⊓ N : Subgroup A) := by
  let f : P →* A ⧸ N := (QuotientGroup.mk' N).comp P.subtype
  have hσbar : QuotientGroup.mk' N σ ^ 3 = 1 := by
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hσ3
  have hord : orderOf (QuotientGroup.mk' N σ) ≤ 3 :=
    Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hσbar)
  let S : Subgroup A := (Subgroup.zpowers (QuotientGroup.mk' N σ)).comap (QuotientGroup.mk' N)
  have hNS : N ≤ S := by
    intro n hn
    show QuotientGroup.mk' N n ∈ Subgroup.zpowers (QuotientGroup.mk' N σ)
    rw [QuotientGroup.mk'_apply N n, (QuotientGroup.eq_one_iff n).mpr hn]
    exact Subgroup.one_mem _
  have hσS : Subgroup.zpowers σ ≤ S := by
    rw [Subgroup.zpowers_le]
    show QuotientGroup.mk' N σ ∈ Subgroup.zpowers (QuotientGroup.mk' N σ)
    exact Subgroup.mem_zpowers _
  have hPS : P ≤ S := hP.trans (sup_le hNS hσS)
  have hrange : f.range ≤ Subgroup.zpowers (QuotientGroup.mk' N σ) := by
    rintro _ ⟨p, rfl⟩
    exact hPS p.2
  have hker : f.ker = (P ⊓ N).subgroupOf P := by
    ext p
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    show QuotientGroup.mk' N (p : A) = 1 ↔ (p : A) ∈ P ∧ (p : A) ∈ N
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact ⟨fun h => ⟨p.2, h⟩, fun h => h.2⟩
  have hindex : Nat.card f.range ≤ 3 :=
    calc Nat.card f.range ≤ Nat.card (Subgroup.zpowers (QuotientGroup.mk' N σ)) :=
          Subgroup.card_le_of_le hrange
      _ = orderOf (QuotientGroup.mk' N σ) := Nat.card_zpowers _
      _ ≤ 3 := hord
  have hdeg : Nat.card P = Nat.card f.ker * Nat.card f.range := by
    rw [← Subgroup.index_ker f]
    exact (Subgroup.card_mul_index (H := f.ker)).symm
  have hkerc : Nat.card f.ker = Nat.card (P ⊓ N : Subgroup A) := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : P ⊓ N ≤ P)).toEquiv
  calc Nat.card P = Nat.card f.ker * Nat.card f.range := hdeg
    _ ≤ Nat.card f.ker * 3 := Nat.mul_le_mul (le_refl _) hindex
    _ = 3 * Nat.card (P ⊓ N : Subgroup A) := by rw [hkerc, Nat.mul_comm]

theorem card_le_of_isPGroup_of_le_range_conj {Z : Type} [Group Z] [Finite Z]
    (hcent : Function.Injective (MulAut.conj : Z →* MulAut Z)) {P : Subgroup (MulAut Z)}
    (hP : IsPGroup 3 P) (hPN : P ≤ (MulAut.conj : Z →* MulAut Z).range) :
    Nat.card P ≤ 3 ^ (Nat.card Z).factorization 3 := by
  let Q : Subgroup Z := P.comap (MulAut.conj : Z →* MulAut Z)
  have hQ3 : IsPGroup 3 Q := by
    refine isPGroup_iff_pow_pow_eq_one.2 fun g => ?_
    have hgP : MulAut.conj (g : Z) ∈ P := g.2
    obtain ⟨k, hk⟩ := IsPGroup.exists_pow_pow_eq_one hP ⟨MulAut.conj (g : Z), hgP⟩
    refine ⟨k, ?_⟩
    have hk' : MulAut.conj ((g : Z) ^ 3 ^ k) = MulAut.conj 1 := by
      rw [map_pow, map_one]
      have h := congrArg Subtype.val hk
      simpa only [Subgroup.coe_pow, Subgroup.coe_one, Subgroup.coe_mk] using h
    have h1 : (g : Z) ^ 3 ^ k = 1 := hcent hk'
    apply Subtype.ext
    simpa only [Subgroup.coe_pow, Subgroup.coe_one] using h1
  have hcardQ : Nat.card P ≤ Nat.card Q := by
    refine Nat.card_le_card_of_surjective
      (fun x : Q => (⟨MulAut.conj (x : Z), x.2⟩ : P)) ?_
    intro p
    obtain ⟨z, hz⟩ := MonoidHom.mem_range.mp (hPN p.2)
    refine ⟨⟨z, ?_⟩, Subtype.ext hz⟩
    show MulAut.conj z ∈ P
    rw [hz]
    exact p.2
  exact hcardQ.trans (card_le_three_pow_of_isPGroup hQ3)

theorem v0Concl_of_outer {Z : Type} [Group Z] [Finite Z] {σ : MulAut Z} {ξ γ : Z} {a : ℕ}
    (hcent : Function.Injective (MulAut.conj : Z →* MulAut Z))
    (hσξ : σ * MulAut.conj ξ = MulAut.conj ξ * σ)
    (hdisj : Subgroup.zpowers σ ⊓ Subgroup.zpowers (MulAut.conj ξ) = ⊥)
    (hξ : orderOf ξ = 3 ^ a)
    (hP : IsPGroup 3 (Subgroup.closure
      ({σ, MulAut.conj ξ, MulAut.conj γ} : Set (MulAut Z))))
    (hσcube : σ ^ 3 ∈ (MulAut.conj : Z →* MulAut Z).range)
    (hZ : (Nat.card Z).factorization 3 = 2 * a)
    (hout : 3 ^ a ≤ orderOf σ) :
    V0Concl σ ξ γ := by
  haveI := range_conj_normal Z
  unfold V0Concl
  have hUcard : orderOf σ * 3 ^ a ≤
      Nat.card (Subgroup.closure ({σ, MulAut.conj ξ} : Set (MulAut Z))) := by
    have h := orderOf_mul_le_card_closure_pair hσξ hdisj
    rwa [orderOf_injective (MulAut.conj : Z →* MulAut Z) hcent ξ, hξ] at h
  have hcardU : 3 ^ (2 * a) ≤
      Nat.card (Subgroup.closure ({σ, MulAut.conj ξ} : Set (MulAut Z))) := by
    rw [two_mul, pow_add]
    exact (Nat.mul_le_mul hout (le_refl (3 ^ a))).trans hUcard
  have hQN : Subgroup.closure ({σ, MulAut.conj ξ, MulAut.conj γ} : Set (MulAut Z)) ≤
      (MulAut.conj : Z →* MulAut Z).range ⊔ Subgroup.zpowers σ := by
    rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with h | h | h
    · rw [h]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers σ)
    · rw [h]
      exact Subgroup.mem_sup_left (MonoidHom.mem_range.mpr ⟨ξ, rfl⟩)
    · rw [h]
      exact Subgroup.mem_sup_left (MonoidHom.mem_range.mpr ⟨γ, rfl⟩)
  have hQ3 : IsPGroup 3 (Subgroup.closure ({σ, MulAut.conj ξ, MulAut.conj γ} : Set (MulAut Z)) ⊓
      (MulAut.conj : Z →* MulAut Z).range : Subgroup (MulAut Z)) :=
    hP.to_inf_left
  have hcardQ : Nat.card (Subgroup.closure ({σ, MulAut.conj ξ, MulAut.conj γ} : Set (MulAut Z))) ≤
      3 * Nat.card (Subgroup.closure ({σ, MulAut.conj ξ} : Set (MulAut Z))) := by
    have h1 := card_le_three_mul_card_inf _ hσcube hQN
    have h2 := card_le_of_isPGroup_of_le_range_conj hcent hQ3 inf_le_right
    refine h1.trans ?_
    refine (Nat.mul_le_mul (le_refl 3) h2).trans ?_
    rw [hZ]
    exact Nat.mul_le_mul (le_refl 3) hcardU
  have hUQ : Subgroup.closure ({σ, MulAut.conj ξ} : Set (MulAut Z)) ≤
      Subgroup.closure ({σ, MulAut.conj ξ, MulAut.conj γ} : Set (MulAut Z)) :=
    Subgroup.closure_mono
      (Set.insert_subset_insert (Set.singleton_subset_iff.2 (Set.mem_insert _ _)))
  have hconj := conj_mem_of_card_le_three_mul hP hUQ hcardQ
  have hγQ : MulAut.conj γ ∈
      Subgroup.closure ({σ, MulAut.conj ξ, MulAut.conj γ} : Set (MulAut Z)) :=
    Subgroup.subset_closure
      (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
  have hσU : σ ∈ Subgroup.closure ({σ, MulAut.conj ξ} : Set (MulAut Z)) :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  have hξU : MulAut.conj ξ ∈ Subgroup.closure ({σ, MulAut.conj ξ} : Set (MulAut Z)) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  exact ⟨hconj _ hγQ _ hσU, hconj _ hγQ _ hξU⟩

theorem v0Concl_of_diag {Z : Type} [Group Z] [Finite Z] {σ : MulAut Z} {ξ γ : Z} {a : ℕ}
    (hcent : Function.Injective (MulAut.conj : Z →* MulAut Z))
    (hσ3 : ∃ k : ℕ, σ ^ 3 ^ k = 1)
    (hσξ : σ * MulAut.conj ξ = MulAut.conj ξ * σ)
    (hdisj : Subgroup.zpowers σ ⊓ Subgroup.zpowers (MulAut.conj ξ) = ⊥)
    (hξ : orderOf ξ = 3 ^ a)
    (hP : IsPGroup 3 (Subgroup.closure
      ({σ, MulAut.conj ξ, MulAut.conj γ} : Set (MulAut Z))))
    (hσcube : σ ^ 3 ∈ (MulAut.conj : Z →* MulAut Z).range)
    (hZ : (Nat.card Z).factorization 3 = 2 * a)
    (hlow : 3 ^ a ≤ 3 * orderOf σ)
    (houter : σ ∉ (MulAut.conj : Z →* MulAut Z).range → 3 ^ a ≤ orderOf σ) :
    V0Concl σ ξ γ := by
  by_cases hσN : σ ∈ (MulAut.conj : Z →* MulAut Z).range
  ·
    obtain ⟨b, rfl⟩ := MonoidHom.mem_range.mp hσN
    have hbξ : b * ξ = ξ * b := by
      apply hcent
      rw [map_mul, map_mul]
      exact hσξ
    have hdisj' : Subgroup.zpowers b ⊓ Subgroup.zpowers ξ = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      rw [Subgroup.mem_inf] at hx
      rw [Subgroup.mem_bot]
      apply hcent
      rw [map_one]
      have h1 : MulAut.conj x ∈
          Subgroup.zpowers (MulAut.conj b) ⊓ Subgroup.zpowers (MulAut.conj ξ) :=
        Subgroup.mem_inf.mpr ⟨conj_mem_zpowers_conj hx.1, conj_mem_zpowers_conj hx.2⟩
      rw [hdisj, Subgroup.mem_bot] at h1
      exact h1
    have hlow' : 3 ^ a ≤ 3 * orderOf b := by
      rw [← orderOf_injective (MulAut.conj : Z →* MulAut Z) hcent b]
      exact hlow
    have hcard : 3 ^ (Nat.card Z).factorization 3 ≤ 3 * (orderOf b * orderOf ξ) := by
      rw [hZ, hξ]
      calc 3 ^ (2 * a) = 3 ^ a * 3 ^ a := by rw [two_mul, pow_add]
        _ ≤ (3 * orderOf b) * 3 ^ a := Nat.mul_le_mul hlow' (le_refl _)
        _ = 3 * (orderOf b * 3 ^ a) := by rw [mul_assoc]
    unfold V0Concl
    exact v0_conclusion_of_inner hcent hP hbξ hdisj' hcard
  · exact v0Concl_of_outer hcent hσξ hdisj hξ hP hσcube hZ (houter hσN)

theorem congr_conj_eq {Z X : Type} [Group Z] [Group X] (φ : Z ≃* X) (z : Z) :
    MulAut.congr φ (MulAut.conj z) = MulAut.conj (φ z) := by
  ext x
  show φ (z * φ.symm x * z⁻¹) = φ z * x * (φ z)⁻¹
  simp only [map_mul, map_inv, MulEquiv.apply_symm_apply]

theorem zpowers_inf_zpowers_conj_eq_bot {Z : Type} [Group Z] [Finite Z] {J : Subgroup Z}
    (hJT : IsType424 (J ⧸ aschbacherSolvableCore 3 J)) {σ : MulAut Z} {ξ : Z}
    (hξJ : ξ ∈ J) (hξ3 : ∃ k : ℕ, ξ ^ 3 ^ k = 1) (hσJ : ∀ j ∈ J, σ j = j) :
    Subgroup.zpowers σ ⊓ Subgroup.zpowers (MulAut.conj ξ) = ⊥ := by
  obtain ⟨k, hk⟩ := hξ3
  obtain ⟨H, hH⟩ : ∃ H : Subgroup (MulAut Z), ∀ τ : MulAut Z, τ ∈ H ↔ ∀ j ∈ J, τ j = j :=
    ⟨{ carrier := {τ | ∀ j ∈ J, τ j = j}
       mul_mem' := by
         intro a b ha hb j hj
         change a (b j) = j
         rw [hb j hj, ha j hj]
       one_mem' := by
         intro j _
         rfl
       inv_mem' := by
         intro a ha j hj
         calc a⁻¹ j = a⁻¹ (a j) := by rw [ha j hj]
           _ = j := MulEquiv.symm_apply_apply a j },
     fun τ => Iff.rfl⟩
  have hσH : σ ∈ H := (hH σ).mpr hσJ
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxσ, hxξ⟩ := Subgroup.mem_inf.mp hx
  have hxfix : ∀ j ∈ J, x j = j := (hH x).mp (Subgroup.zpowers_le.mpr hσH hxσ)
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hxξ
  have hxconj : x = MulAut.conj (ξ ^ n) := by
    rw [map_zpow]
    exact hn.symm
  have hξnJ : ξ ^ n ∈ J := J.zpow_mem hξJ n
  have hc : ∀ j ∈ J, ξ ^ n * j = j * ξ ^ n := by
    intro j hj
    have h1 : x j = j := hxfix j hj
    rw [hxconj, MulAut.conj_apply] at h1
    exact mul_inv_eq_iff_eq_mul.mp h1
  obtain ⟨y, hyθ, hye⟩ := KS11Lie2Proof.mem_theta_of_central hJT hξnJ hc
  have hye' : (y : Z) = ξ ^ n := hye
  have hyk : y ^ 3 ^ k = 1 := by
    apply Subtype.ext
    show (y : Z) ^ 3 ^ k = 1
    rw [hye', ← zpow_natCast, ← zpow_mul, mul_comm n, zpow_mul, zpow_natCast, hk, one_zpow]
  have hy1 : y = 1 := eq_one_of_mem_theta_of_pow_eq_one hyθ hyk
  have hξn : ξ ^ n = 1 := by
    rw [← hye']
    simp [hy1]
  rw [Subgroup.mem_bot, hxconj, hξn, map_one]

end PureL3

end Item1120V0Bar

end CFSG.RankThree.PartTwo.Sec11

end
