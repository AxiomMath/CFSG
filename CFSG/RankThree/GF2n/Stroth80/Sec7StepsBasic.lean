module

public import CFSG.RankThree.GF2n.Stroth80.Sec7Stmt

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G]

theorem hallWitt_id (a b c : G) :
    b⁻¹ * ⁅⁅a⁻¹, b⁆⁻¹, c⁻¹⁆ * b * (c⁻¹ * ⁅⁅b⁻¹, c⁆⁻¹, a⁻¹⁆ * c) *
      (a⁻¹ * ⁅⁅c⁻¹, a⁆⁻¹, b⁻¹⁆ * a) = 1 := by
  simp only [commutatorElement_def]
  group

theorem three_subgroup_mod (N : Subgroup G) (x y z : G) (hx : ∀ n ∈ N, x * n * x⁻¹ ∈ N)
    (hy : ∀ n ∈ N, y⁻¹ * n * y ∈ N) (hz : ∀ n ∈ N, z * n * z⁻¹ ∈ N)
    (h2 : ⁅⁅y, z⁻¹⁆⁻¹, x⁆ ∈ N) (h3 : ⁅⁅z, x⁻¹⁆⁻¹, y⁆ ∈ N) : ⁅⁅x, y⁻¹⁆⁻¹, z⁆ ∈ N := by
  have key := hallWitt_id x⁻¹ y⁻¹ z⁻¹
  simp only [inv_inv] at key
  have e1 : y * ⁅⁅x, y⁻¹⁆⁻¹, z⁆ * y⁻¹ * (z * ⁅⁅y, z⁻¹⁆⁻¹, x⁆ * z⁻¹) *
      (x * ⁅⁅z, x⁻¹⁆⁻¹, y⁆ * x⁻¹) = 1 := key
  have h4 : z * ⁅⁅y, z⁻¹⁆⁻¹, x⁆ * z⁻¹ ∈ N := hz _ h2
  have h5 : x * ⁅⁅z, x⁻¹⁆⁻¹, y⁆ * x⁻¹ ∈ N := hx _ h3
  have h6 : y * ⁅⁅x, y⁻¹⁆⁻¹, z⁆ * y⁻¹ = ((z * ⁅⁅y, z⁻¹⁆⁻¹, x⁆ * z⁻¹) *
      (x * ⁅⁅z, x⁻¹⁆⁻¹, y⁆ * x⁻¹))⁻¹ := by
    rw [eq_inv_iff_mul_eq_one]
    rw [← e1]
    group
  have h7 : y * ⁅⁅x, y⁻¹⁆⁻¹, z⁆ * y⁻¹ ∈ N := by
    rw [h6]
    exact N.inv_mem (N.mul_mem h4 h5)
  have h8 := hy _ h7
  have e2 : y⁻¹ * (y * ⁅⁅x, y⁻¹⁆⁻¹, z⁆ * y⁻¹) * y = ⁅⁅x, y⁻¹⁆⁻¹, z⁆ := by group
  rwa [e2] at h8

theorem commutator_eq_one_on {E : Type*} [AddCommGroup E] (A B : E ≃+ E) (V W : AddSubgroup E)
    (hAW : ∀ w ∈ W, A w ∈ W) (hAW' : ∀ w ∈ W, A.symm w ∈ W)
    (hBW : ∀ w ∈ W, B w ∈ W) (hBW' : ∀ w ∈ W, B.symm w ∈ W)
    (hAV : ∀ v ∈ V, A v = v) (hBV : ∀ v ∈ V, B v = v)
    (hAd : ∀ w ∈ W, A w - w ∈ V) (hBd : ∀ w ∈ W, B w - w ∈ V) (w : E) (hw : w ∈ W) :
    A (B (A.symm (B.symm w))) = w := by
  have hAinv : ∀ u ∈ W, A.symm u = u - (A u - u) := by
    intro u hu
    have h1 := hAV (A u - u) (hAd u hu)
    have h2 : A (u - (A u - u)) = u := by
      rw [map_sub, h1]
      abel
    exact A.symm_apply_eq.mpr h2.symm
  have hBinv : ∀ u ∈ W, B.symm u = u - (B u - u) := by
    intro u hu
    have h1 := hBV (B u - u) (hBd u hu)
    have h2 : B (u - (B u - u)) = u := by
      rw [map_sub, h1]
      abel
    exact B.symm_apply_eq.mpr h2.symm
  set v₁ := B.symm w with hv₁
  have hv₁W : v₁ ∈ W := hBW' w hw
  set v₂ := A.symm v₁ with hv₂
  have hv₂W : v₂ ∈ W := hAW' v₁ hv₁W
  have e1 : A v₂ = v₁ := A.apply_symm_apply v₁
  have e2 : B v₁ = w := B.apply_symm_apply w
  have d1 : B v₁ - v₁ ∈ V := hBd v₁ hv₁W
  have d2 : A v₂ - v₂ ∈ V := hAd v₂ hv₂W
  have d3 : B v₂ - v₂ ∈ V := hBd v₂ hv₂W
  rw [e1] at d2
  rw [e2] at d1
  have f1 : A (B v₂) = A v₂ + (B v₂ - v₂) := by
    have : B v₂ = v₂ + (B v₂ - v₂) := by abel
    conv_lhs => rw [this]
    rw [map_add, hAV _ d3]
  rw [f1, e1]
  have f2 : v₁ - v₂ ∈ V := d2
  have f3 : B v₂ = B v₁ - (v₁ - v₂) := by
    have : v₂ = v₁ - (v₁ - v₂) := by abel
    conv_lhs => rw [this]
    rw [map_sub, hBV _ f2]
  have f4 : B v₂ - v₂ = B v₁ - v₁ := by
    rw [f3]
    abel
  rw [f4, e2]
  abel

private theorem commEgen_conj_mem {Q Z0 : Subgroup G} (hQZ0 : Q ≤ Z0) {y : G}
    (hy : ∀ z ∈ Z0, ⁅z, y⁆ ∈ Q) {h : G} (hh : h ∈ Z0) : y * h * y⁻¹ ∈ Z0 := by
  have h1 : ⁅h, y⁆ ∈ Z0 := hQZ0 (hy h hh)
  have h2 : y * h * y⁻¹ = ⁅h, y⁆⁻¹ * h := by
    rw [commutatorElement_def]
    group
  rw [h2]
  exact mul_mem (inv_mem h1) hh

private theorem commEgen_mem_normalizer {Q Z0 : Subgroup G} (hQZ0 : Q ≤ Z0) {y : G}
    (hy : ∀ z ∈ Z0, ⁅z, y⁆ ∈ Q) (hy' : ∀ z ∈ Z0, ⁅z, y⁻¹⁆ ∈ Q) :
    y ∈ Subgroup.normalizer (Z0 : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    exact commEgen_conj_mem hQZ0 hy hh
  · intro hh
    have h3 := commEgen_conj_mem hQZ0 hy' hh
    have e : y⁻¹ * (y * h * y⁻¹) * y⁻¹⁻¹ = h := by group
    rw [e] at h3
    exact h3

private theorem commEgen_normalizer_conj {Z0 : Subgroup G} {x n : G}
    (hx : x ∈ Subgroup.normalizer (Z0 : Set G)) (hn : n ∈ Z0) : x * n * x⁻¹ ∈ Z0 :=
  (Subgroup.mem_normalizer_iff.mp hx n).mp hn

private theorem commEgen_le_of_forall {M Q Z0 H : Subgroup G}
    (h : ∀ g ∈ M, (∀ z ∈ Z0, ∀ y ∈ conjSubgroup g Z0, ⁅z, y⁆ ∈ Q) → conjSubgroup g Z0 ≤ H) :
    Egen M Q Z0 ≤ H := by
  unfold Egen
  exact iSup_le fun g => iSup_le fun hg => iSup_le fun hΓ => h g hg hΓ

private theorem commEgen_conj_le_Egen {M Q Z0 : Subgroup G} {g : G} (hg : g ∈ M)
    (hΓ : ∀ z ∈ Z0, ∀ y ∈ conjSubgroup g Z0, ⁅z, y⁆ ∈ Q) :
    conjSubgroup g Z0 ≤ Egen M Q Z0 := by
  unfold Egen
  exact le_iSup_of_le g (le_iSup_of_le hg (le_iSup_of_le hΓ le_rfl))

private theorem commEgen_le_normalizer {M Q Z0 : Subgroup G} (hQZ0 : Q ≤ Z0) :
    Egen M Q Z0 ≤ Subgroup.normalizer (Z0 : Set G) := by
  refine commEgen_le_of_forall (fun g _ hΓ => ?_)
  intro y hy
  exact commEgen_mem_normalizer hQZ0 (fun z hz => hΓ z hz y hy)
    (fun z hz => hΓ z hz y⁻¹ (inv_mem hy))

private def commEgenC1 (M Q Z0 : Subgroup G)
    (hN : Egen M Q Z0 ≤ Subgroup.normalizer (Z0 : Set G)) : Subgroup G where
  carrier := {x | x ∈ Egen M Q Z0 ∧
    ∀ g ∈ M, (∀ z ∈ Z0, ∀ y ∈ conjSubgroup g Z0, ⁅z, y⁆ ∈ Q) → ∀ y ∈ conjSubgroup g Z0,
      ⁅x, y⁆ ∈ Z0}
  mul_mem' := by
    intro a b ha hb
    obtain ⟨ha1, ha2⟩ := ha
    obtain ⟨hb1, hb2⟩ := hb
    show _ ∧ _
    refine ⟨mul_mem ha1 hb1, fun g hg hΓ y hy => ?_⟩
    have e : ⁅a * b, y⁆ = a * ⁅b, y⁆ * a⁻¹ * ⁅a, y⁆ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact mul_mem (commEgen_normalizer_conj (hN ha1) (hb2 g hg hΓ y hy)) (ha2 g hg hΓ y hy)
  one_mem' := by
    show _ ∧ _
    refine ⟨one_mem _, fun g _ _ y _ => ?_⟩
    rw [commutatorElement_one_left]
    exact one_mem _
  inv_mem' := by
    intro a ha
    obtain ⟨ha1, ha2⟩ := ha
    show _ ∧ _
    refine ⟨inv_mem ha1, fun g hg hΓ y hy => ?_⟩
    have e : ⁅a⁻¹, y⁆ = a⁻¹ * ⁅a, y⁆⁻¹ * a := by
      simp only [commutatorElement_def]
      group
    rw [e]
    have h3 := commEgen_normalizer_conj (inv_mem (hN ha1)) (inv_mem (ha2 g hg hΓ y hy))
    rw [inv_inv] at h3
    exact h3

private def commEgenC2 (M Q Z0 : Subgroup G)
    (hN : Egen M Q Z0 ≤ Subgroup.normalizer (Z0 : Set G)) : Subgroup G where
  carrier := {y | y ∈ Egen M Q Z0 ∧ ∀ x ∈ Egen M Q Z0, ⁅x, y⁆ ∈ Z0}
  mul_mem' := by
    intro a b ha hb
    obtain ⟨ha1, ha2⟩ := ha
    obtain ⟨hb1, hb2⟩ := hb
    show _ ∧ _
    refine ⟨mul_mem ha1 hb1, fun x hx => ?_⟩
    have e : ⁅x, a * b⁆ = ⁅x, a⁆ * (a * ⁅x, b⁆ * a⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact mul_mem (ha2 x hx) (commEgen_normalizer_conj (hN ha1) (hb2 x hx))
  one_mem' := by
    show _ ∧ _
    refine ⟨one_mem _, fun x _ => ?_⟩
    rw [commutatorElement_one_right]
    exact one_mem _
  inv_mem' := by
    intro a ha
    obtain ⟨ha1, ha2⟩ := ha
    show _ ∧ _
    refine ⟨inv_mem ha1, fun x hx => ?_⟩
    have e : ⁅x, a⁻¹⁆ = a⁻¹ * ⁅x, a⁆⁻¹ * a := by
      simp only [commutatorElement_def]
      group
    rw [e]
    have h3 := commEgen_normalizer_conj (inv_mem (hN ha1)) (inv_mem (ha2 x hx))
    rw [inv_inv] at h3
    exact h3

private theorem mem_commEgenC1 {M Q Z0 : Subgroup G}
    {hN : Egen M Q Z0 ≤ Subgroup.normalizer (Z0 : Set G)} {x : G} :
    x ∈ commEgenC1 M Q Z0 hN ↔ x ∈ Egen M Q Z0 ∧
      ∀ g ∈ M, (∀ z ∈ Z0, ∀ y ∈ conjSubgroup g Z0, ⁅z, y⁆ ∈ Q) → ∀ y ∈ conjSubgroup g Z0,
        ⁅x, y⁆ ∈ Z0 :=
  Iff.rfl

private theorem mem_commEgenC2 {M Q Z0 : Subgroup G}
    {hN : Egen M Q Z0 ≤ Subgroup.normalizer (Z0 : Set G)} {y : G} :
    y ∈ commEgenC2 M Q Z0 hN ↔ y ∈ Egen M Q Z0 ∧ ∀ x ∈ Egen M Q Z0, ⁅x, y⁆ ∈ Z0 :=
  Iff.rfl

private theorem commEgen_le_C1 {M Q Z0 : Subgroup G} (hQZ0 : Q ≤ Z0)
    (hgen : ∀ g₁ ∈ M, (∀ z ∈ Z0, ∀ y ∈ conjSubgroup g₁ Z0, ⁅z, y⁆ ∈ Q) →
      ∀ g₂ ∈ M, (∀ z ∈ Z0, ∀ y ∈ conjSubgroup g₂ Z0, ⁅z, y⁆ ∈ Q) →
      ∀ y₁ ∈ conjSubgroup g₁ Z0, ∀ y₂ ∈ conjSubgroup g₂ Z0, ⁅y₁, y₂⁆ ∈ Z0) :
    Egen M Q Z0 ≤ commEgenC1 M Q Z0 (commEgen_le_normalizer hQZ0) := by
  refine commEgen_le_of_forall (fun g hg hΓ => ?_)
  intro y hy
  refine mem_commEgenC1.2 ⟨commEgen_conj_le_Egen hg hΓ hy, fun g' hg' hΓ' y' hy' => ?_⟩
  exact hgen g hg hΓ g' hg' hΓ' y hy y' hy'

private theorem commEgen_le_C2 {M Q Z0 : Subgroup G} (hQZ0 : Q ≤ Z0)
    (hgen : ∀ g₁ ∈ M, (∀ z ∈ Z0, ∀ y ∈ conjSubgroup g₁ Z0, ⁅z, y⁆ ∈ Q) →
      ∀ g₂ ∈ M, (∀ z ∈ Z0, ∀ y ∈ conjSubgroup g₂ Z0, ⁅z, y⁆ ∈ Q) →
      ∀ y₁ ∈ conjSubgroup g₁ Z0, ∀ y₂ ∈ conjSubgroup g₂ Z0, ⁅y₁, y₂⁆ ∈ Z0) :
    Egen M Q Z0 ≤ commEgenC2 M Q Z0 (commEgen_le_normalizer hQZ0) := by
  refine commEgen_le_of_forall (fun g hg hΓ => ?_)
  intro y hy
  refine mem_commEgenC2.2 ⟨commEgen_conj_le_Egen hg hΓ hy, fun x hx => ?_⟩
  exact (mem_commEgenC1.1 (commEgen_le_C1 hQZ0 hgen hx)).2 g hg hΓ y hy

theorem commutator_Egen_le {M Q Z0 : Subgroup G} (hQZ0 : Q ≤ Z0)
    (hgen : ∀ g₁ ∈ M, (∀ z ∈ Z0, ∀ y ∈ conjSubgroup g₁ Z0, ⁅z, y⁆ ∈ Q) →
      ∀ g₂ ∈ M, (∀ z ∈ Z0, ∀ y ∈ conjSubgroup g₂ Z0, ⁅z, y⁆ ∈ Q) →
      ∀ y₁ ∈ conjSubgroup g₁ Z0, ∀ y₂ ∈ conjSubgroup g₂ Z0, ⁅y₁, y₂⁆ ∈ Z0) :
    ⁅Egen M Q Z0, Egen M Q Z0⁆ ≤ Z0 := by
  rw [Subgroup.commutator_le]
  intro x hx y hy
  exact (mem_commEgenC2.1 (commEgen_le_C2 hQZ0 hgen hy)).2 x hx

section SylowNormalizer

variable {X : Type*} [Group X] [Finite X]

theorem exists_sylow_two_of_normalizer_le {H T : Subgroup X} (hT : IsPGroup 2 T) (hTH : T ≤ H)
    (hmax : ∀ S : Subgroup X, S ≤ H → IsPGroup 2 S → T ≤ S → S ≤ T)
    (hN : Subgroup.normalizer (T : Set X) ≤ H) :
    ∃ P : Sylow 2 X, P.toSubgroup = T := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hTP⟩ := hT.exists_le_sylow
  refine ⟨P, le_antisymm ?_ hTP⟩
  by_contra hne
  haveI : Group.IsNilpotent ↥P.toSubgroup := P.isPGroup'.isNilpotent
  have hNC : NormalizerCondition ↥P.toSubgroup := Group.normalizerCondition_of_isNilpotent
  have hK : T.subgroupOf P.toSubgroup < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    apply hne
    intro x hx
    have hmem : (⟨x, hx⟩ : ↥P.toSubgroup) ∈ T.subgroupOf P.toSubgroup := by
      rw [htop]
      exact Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp hmem
  obtain ⟨y, hyN, hyK⟩ := SetLike.exists_of_lt (hNC _ hK)
  have hyT : (y : X) ∉ T := fun h => hyK (Subgroup.mem_subgroupOf.mpr h)
  have hyP : (y : X) ∈ P.toSubgroup := y.2
  have hyNorm : (y : X) ∈ Subgroup.normalizer (T : Set X) := by
    refine Subgroup.mem_normalizer_iff.mpr (fun h => ?_)
    by_cases hh : h ∈ P.toSubgroup
    · have key := Subgroup.mem_normalizer_iff.mp hyN (⟨h, hh⟩ : ↥P.toSubgroup)
      simpa [Subgroup.mem_subgroupOf] using key
    · constructor
      · intro hT'
        exact absurd (hTP hT') hh
      · intro hc
        exfalso
        apply hh
        have h2 := mul_mem (mul_mem (inv_mem hyP) (hTP hc)) hyP
        simpa [mul_assoc] using h2
  have hyH : (y : X) ∈ H := hN hyNorm
  have hSP : T ⊔ Subgroup.zpowers (y : X) ≤ P.toSubgroup :=
    sup_le hTP (Subgroup.zpowers_le.mpr hyP)
  have hSH : T ⊔ Subgroup.zpowers (y : X) ≤ H :=
    sup_le hTH (Subgroup.zpowers_le.mpr hyH)
  have hpS : IsPGroup 2 ↥(T ⊔ Subgroup.zpowers (y : X)) := P.isPGroup'.to_le hSP
  have hSle : T ⊔ Subgroup.zpowers (y : X) ≤ T :=
    hmax _ hSH hpS le_sup_left
  have hyS : (y : X) ∈ T ⊔ Subgroup.zpowers (y : X) :=
    (le_sup_right : Subgroup.zpowers (y : X) ≤ T ⊔ Subgroup.zpowers (y : X))
      (Subgroup.mem_zpowers _)
  exact hyT (hSle hyS)

end SylowNormalizer

end CFSG.RankThree.GF2n.Stroth80
