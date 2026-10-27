module

public import CFSG.RankThree.PartTwo.Sec11.Item116Points
public import CFSG.RankThree.PartTwo.Sec11.Item112

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Coords

variable {G : Type*} [Group G]

theorem pow_eq_pow_mod_three {M : Type*} [Monoid M] {x : M} (hx : x ^ 3 = 1) (n : ℕ) :
    x ^ n = x ^ (n % 3) := by
  conv_lhs => rw [← Nat.div_add_mod n 3, pow_add, pow_mul, hx, one_pow, one_mul]

theorem zpow_eq_pow_val {x : G} (hx : x ^ 3 = 1) (m : ℤ) : x ^ m = x ^ ((m : ZMod 3).val) := by
  have h1 : ((((m : ZMod 3).val : ℕ) : ℤ)) = m % 3 := ZMod.val_intCast m
  rw [← zpow_natCast, h1]
  conv_lhs => rw [← Int.mul_ediv_add_emod m 3, zpow_add, zpow_mul]
  rw [show (x ^ (3 : ℤ)) = 1 by rw [zpow_ofNat, hx], one_zpow, one_mul]

theorem exists_coords_triple {A : Subgroup G} [Finite A]
    (hcomm : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u) (hexp : ∀ u ∈ A, u ^ 3 = 1)
    (h27 : Nat.card A = 27) {x y z : G} (hx : x ∈ A) (hy : y ∈ A) (hz : z ∈ A)
    (hgen : Subgroup.closure {x, y, z} = A) :
    ∃ f : Multiplicative (Fin 3 → ZMod 3) ≃* A,
      f (Multiplicative.ofAdd (Pi.single 0 1)) = ⟨x, hx⟩ ∧
      f (Multiplicative.ofAdd (Pi.single 1 1)) = ⟨y, hy⟩ ∧
      f (Multiplicative.ofAdd (Pi.single 2 1)) = ⟨z, hz⟩ ∧
      ∀ v : Fin 3 → ZMod 3, (f (Multiplicative.ofAdd v) : G) =
        x ^ (v 0).val * y ^ (v 1).val * z ^ (v 2).val := by
  classical
  have : Fact (1 < 3) := ⟨by norm_num⟩
  let _ : CommGroup A :=
    { (inferInstance : Group A) with mul_comm := fun u v => Subtype.ext (hcomm u u.2 v v.2) }
  have h3 : ∀ u : A, u ^ 3 = 1 := fun u => Subtype.ext (by simpa using hexp u u.2)
  set X : A := ⟨x, hx⟩
  set Y : A := ⟨y, hy⟩
  set Z : A := ⟨z, hz⟩
  have hadd : ∀ (u : A) (a b : ZMod 3), u ^ (a + b).val = u ^ a.val * u ^ b.val := by
    intro u a b
    rw [ZMod.val_add, ← pow_eq_pow_mod_three (h3 u), pow_add]
  let φ : Multiplicative (Fin 3 → ZMod 3) →* A :=
    { toFun := fun v => X ^ ((Multiplicative.toAdd v) 0).val *
        Y ^ ((Multiplicative.toAdd v) 1).val * Z ^ ((Multiplicative.toAdd v) 2).val
      map_one' := by simp
      map_mul' := fun v w => by
        simp only [toAdd_mul, Pi.add_apply, hadd]
        simp only [mul_assoc, mul_left_comm] }
  have hφx : φ (Multiplicative.ofAdd (Pi.single 0 1)) = X := by
    simp [φ, ZMod.val_one]
  have hφy : φ (Multiplicative.ofAdd (Pi.single 1 1)) = Y := by
    simp [φ, ZMod.val_one]
  have hφz : φ (Multiplicative.ofAdd (Pi.single 2 1)) = Z := by
    simp [φ, ZMod.val_one]
  have hsurj : Function.Surjective φ := by
    rw [← MonoidHom.range_eq_top]
    have hle : Subgroup.closure ({x, y, z} : Set G) ≤ φ.range.map A.subtype := by
      rw [Subgroup.closure_le]
      intro u hu
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
      rcases hu with rfl | rfl | rfl
      · exact ⟨X, ⟨_, hφx⟩, rfl⟩
      · exact ⟨Y, ⟨_, hφy⟩, rfl⟩
      · exact ⟨Z, ⟨_, hφz⟩, rfl⟩
    rw [eq_top_iff]
    intro u _
    obtain ⟨u', hu', hu'eq⟩ := hle (hgen ▸ u.2 : (u : G) ∈ Subgroup.closure {x, y, z})
    have : u' = u := Subtype.ext hu'eq
    rw [← this]
    exact hu'
  have hbij : Function.Bijective φ := by
    refine hsurj.bijective_of_nat_card_le ?_
    rw [h27, Nat.card_eq_fintype_card]
    simp
  refine ⟨MulEquiv.ofBijective φ hbij, hφx, hφy, hφz, fun v => ?_⟩
  rfl

end Coords

section Mat

variable {G : Type} [Group G] {A : Subgroup G}

@[expose] noncomputable def coordMat (f : Multiplicative (Fin 3 → ZMod 3) ≃* A)
    (w : Subgroup.normalizer (A : Set G)) : KFacts.Mat33 :=
  LinearMap.toMatrix' (Sec12.wAction f w : (Fin 3 → ZMod 3) →ₗ[ZMod 3] (Fin 3 → ZMod 3))

theorem coordMat_mul (f : Multiplicative (Fin 3 → ZMod 3) ≃* A)
    (w₁ w₂ : Subgroup.normalizer (A : Set G)) :
    coordMat f (w₁ * w₂) = coordMat f w₁ * coordMat f w₂ := by
  rw [coordMat, coordMat, coordMat, map_mul, ← LinearMap.toMatrix'_mul]
  rfl

theorem wAction_eq_of_conj {f : Multiplicative (Fin 3 → ZMod 3) ≃* A}
    {w : Subgroup.normalizer (A : Set G)} {v u : Fin 3 → ZMod 3}
    (h : (w : G) * (f (Multiplicative.ofAdd v) : G) * (w : G)⁻¹ =
      (f (Multiplicative.ofAdd u) : G)) :
    Sec12.wAction f w v = u := by
  have h1 : f (Multiplicative.ofAdd (Sec12.wAction f w v)) = f (Multiplicative.ofAdd u) :=
    Subtype.ext ((Sec12.wAction_apply f w v).trans h)
  exact Multiplicative.ofAdd.injective (f.injective h1)

theorem coordMat_eq {f : Multiplicative (Fin 3 → ZMod 3) ≃* A}
    {w : Subgroup.normalizer (A : Set G)} {M : KFacts.Mat33}
    (h : ∀ j : Fin 3, (w : G) * (f (Multiplicative.ofAdd (Pi.single j 1)) : G) * (w : G)⁻¹ =
      (f (Multiplicative.ofAdd (fun i => M i j)) : G)) :
    coordMat f w = M := by
  ext i j
  rw [coordMat, LinearMap.toMatrix'_apply, LinearEquiv.coe_coe, wAction_eq_of_conj (h j)]

theorem coordMat_eq' {f : Multiplicative (Fin 3 → ZMod 3) ≃* A}
    {w : Subgroup.normalizer (A : Set G)} {M : KFacts.Mat33}
    (h0 : (w : G) * (f (Multiplicative.ofAdd (Pi.single 0 1)) : G) * (w : G)⁻¹ =
      (f (Multiplicative.ofAdd (fun i => M i 0)) : G))
    (h1 : (w : G) * (f (Multiplicative.ofAdd (Pi.single 1 1)) : G) * (w : G)⁻¹ =
      (f (Multiplicative.ofAdd (fun i => M i 1)) : G))
    (h2 : (w : G) * (f (Multiplicative.ofAdd (Pi.single 2 1)) : G) * (w : G)⁻¹ =
      (f (Multiplicative.ofAdd (fun i => M i 2)) : G)) :
    coordMat f w = M :=
  coordMat_eq fun j => by
    fin_cases j
    · exact h0
    · exact h1
    · exact h2

theorem conj_mem_zpowers_of_coordMat {f : Multiplicative (Fin 3 → ZMod 3) ≃* A}
    {w : Subgroup.normalizer (A : Set G)} (h0 : coordMat f w 0 2 = 0)
    (h1 : coordMat f w 1 2 = 0) :
    (w : G) * (f (Multiplicative.ofAdd (Pi.single 2 1)) : G) * (w : G)⁻¹ ∈
      Subgroup.zpowers (f (Multiplicative.ofAdd (Pi.single 2 1)) : G) := by
  set v := Sec12.wAction f w (Pi.single 2 1) with hv
  have hv0 : v 0 = 0 := by
    rw [← h0, coordMat, LinearMap.toMatrix'_apply]
    rfl
  have hv1 : v 1 = 0 := by
    rw [← h1, coordMat, LinearMap.toMatrix'_apply]
    rfl
  have hveq : v = (v 2).val • Pi.single 2 1 := by
    ext i
    fin_cases i
    · simp [hv0]
    · simp [hv1]
    · simp
  rw [← Sec12.wAction_apply f w, ← hv, hveq, ofAdd_nsmul, map_pow, Subgroup.coe_pow]
  exact Subgroup.npow_mem_zpowers _ _

theorem conj_not_mem_zpowers_of_coordMat {f : Multiplicative (Fin 3 → ZMod 3) ≃* A}
    {w : Subgroup.normalizer (A : Set G)} (h : coordMat f w 1 0 ≠ 0) :
    (w : G) * (f (Multiplicative.ofAdd (Pi.single 0 1)) : G) * (w : G)⁻¹ ∉
      Subgroup.zpowers (f (Multiplicative.ofAdd (Pi.single 0 1)) : G) := by
  rintro ⟨k, hk⟩
  apply h
  have hk' : (w : G) * (f (Multiplicative.ofAdd (Pi.single 0 1)) : G) * (w : G)⁻¹ =
      (f (Multiplicative.ofAdd (k • Pi.single 0 1)) : G) := by
    rw [ofAdd_zsmul, map_zpow, Subgroup.coe_zpow]
    exact hk.symm
  rw [coordMat, LinearMap.toMatrix'_apply, LinearEquiv.coe_coe, wAction_eq_of_conj hk']
  simp

@[expose] def GoodWord (Y : KFacts.Mat33) : Prop := Y 0 2 = 0 ∧ Y 1 2 = 0 ∧ Y 1 0 ≠ 0

instance (Y : KFacts.Mat33) : Decidable (GoodWord Y) := by
  unfold GoodWord
  infer_instance

theorem goodWord_cases : ∀ α β γ x : ZMod 3, α ≠ 0 → β ≠ 0 →
    GoodWord !![1, 0, 0; β, 1, γ; 0, 0, 1] ∨
    GoodWord (!![1, 0, 0; β, 1, γ; 0, 0, 1] * !![2, x, 0; 0, 1, 0; 0, 0, 1] *
      !![1, 0, 0; β, 1, γ; 0, 0, 1] * !![2, x, 0; 0, 1, 0; 0, 0, 1] *
      !![1, 0, 0; β, 1, γ; 0, 0, 1]) ∨
    GoodWord (!![1, 0, 0; β, 1, γ; 0, 0, 1] * !![1, α, 0; 0, 1, 0; 0, 0, 1] *
      !![2, x, 0; 0, 1, 0; 0, 0, 1] * !![1, 0, 0; β, 1, γ; 0, 0, 1] *
      !![1, 0, 0; β, 1, γ; 0, 0, 1]) ∨
    GoodWord (!![1, 0, 0; β, 1, γ; 0, 0, 1] * !![1, α, 0; 0, 1, 0; 0, 0, 1] *
      !![1, α, 0; 0, 1, 0; 0, 0, 1] * !![2, x, 0; 0, 1, 0; 0, 0, 1] *
      !![1, 0, 0; β, 1, γ; 0, 0, 1] * !![1, 0, 0; β, 1, γ; 0, 0, 1]) := by
  decide +kernel

end Mat

section CaseOne

variable {G : Type} [Group G] [Finite G]

theorem false_of_not_mem_hyperplane {A B : Subgroup G} {c d l₀ l₁ w₀ : G}
    (hexp : ∀ u ∈ A, u ^ 3 = 1) (hcomm : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u)
    (h27 : Nat.card A = 27) (hBA : B ≤ A) (hB9 : Nat.card B = 9) (hcA : c ∈ A) (hcB : c ∉ B)
    (hdB : d ∈ B) (hd1 : d ≠ 1)
    (hl₀ : l₀ ∈ Subgroup.normalizer (A : Set G)) (hl₁ : l₁ ∈ Subgroup.normalizer (A : Set G))
    (hw₀ : w₀ ∈ Subgroup.normalizer (A : Set G)) (hw₀B : w₀ ∈ Subgroup.normalizer (B : Set G))
    (hl₀c : l₀ * c * l₀⁻¹ = c) (hl₀d : l₀ * d * l₀⁻¹ = d)
    (hl₀A : ∀ u ∈ A, l₀ * u * l₀⁻¹ * u⁻¹ ∈ Subgroup.zpowers d)
    (hl₀1 : ∃ u ∈ A, l₀ * u * l₀⁻¹ ≠ u)
    (hl₁c : l₁ * c * l₁⁻¹ = c) (hl₁d : l₁ * d * l₁⁻¹ = d⁻¹)
    (hl₁A : ∀ u ∈ A, l₁ * u * l₁⁻¹ * u⁻¹ ∈ Subgroup.zpowers d)
    (hw₀d : w₀ * d * w₀⁻¹ ∉ Subgroup.zpowers d)
    (hH : ∀ y ∈ Subgroup.normalizer (A : Set G),
      y ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) → y * d * y⁻¹ ∈ Subgroup.zpowers d) :
    False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (1 < 3) := ⟨by norm_num⟩
  have hdA := hBA hdB
  set e := w₀ * d * w₀⁻¹ with he
  have heB : e ∈ B := (Subgroup.mem_normalizer_iff.mp hw₀B d).mp hdB
  have heA := hBA heB
  have hA3 : IsPGroup 3 A := fun u => ⟨1, Subtype.ext (by simpa using hexp u u.2)⟩
  have hd3 : d ^ 3 = 1 := hexp d hdA
  have he3 : e ^ 3 = 1 := hexp e heA
  have hdeB : Subgroup.closure ({d, e} : Set G) ≤ B := by
    rw [Subgroup.closure_le]
    intro u hu
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
    rcases hu with rfl | rfl
    · exact hdB
    · exact heB
  have hBde : Subgroup.closure ({d, e} : Set G) = B := by
    have hdo : orderOf d = 3 := orderOf_eq_prime hd3 hd1
    have h1 : Subgroup.zpowers d ≤ Subgroup.closure ({d, e} : Set G) :=
      Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))
    have h9 := Sec9.three_mul_card_le_of_le_of_ne hA3 (hdeB.trans hBA) h1 (fun h => hw₀d (by
      rw [h]
      exact Subgroup.subset_closure (by simp)))
    rw [Nat.card_zpowers, hdo] at h9
    exact Subgroup.eq_of_le_of_card_ge hdeB (by rw [hB9]; omega)
  have hAgen : Subgroup.closure ({d, e, c} : Set G) = A :=
    closure_triple_eq hexp h27 hdA heA hcA hd1 hw₀d (fun h => hcB (hBde ▸ h))
  obtain ⟨f, hfd, hfe, hfc, hfv⟩ := exists_coords_triple hcomm hexp h27 hdA heA hcA hAgen
  have hfd' : (f (Multiplicative.ofAdd (Pi.single 0 1)) : G) = d := congrArg Subtype.val hfd
  have hfe' : (f (Multiplicative.ofAdd (Pi.single 1 1)) : G) = e := congrArg Subtype.val hfe
  have hfc' : (f (Multiplicative.ofAdd (Pi.single 2 1)) : G) = c := congrArg Subtype.val hfc
  have key : ∀ y : Subgroup.normalizer (A : Set G), GoodWord (coordMat f y) → False := by
    rintro y ⟨h0, h1, h10⟩
    have hyc := conj_mem_zpowers_of_coordMat h0 h1
    rw [hfc'] at hyc
    have hyd := hH y y.2 (Sec10.mem_normalizer_zpowers_of_conj_mem hyc)
    have hyd' := conj_not_mem_zpowers_of_coordMat h10
    rw [hfd'] at hyd'
    exact hyd' hyd
  have hcen : ∀ g : G, g * d * g⁻¹ = d → g * e * g⁻¹ = e → g * c * g⁻¹ = c →
      ∀ u ∈ A, g * u * g⁻¹ = u := by
    intro g h1 h2 h3 u hu
    have hle : Subgroup.closure ({d, e, c} : Set G) ≤ Subgroup.centralizer ({g} : Set G) := by
      rw [Subgroup.closure_le]
      intro v hv
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      rcases hv with hv | hv | hv <;> rw [hv]
      · exact mul_comm_of_conj_eq h1
      · exact mul_comm_of_conj_eq h2
      · exact mul_comm_of_conj_eq h3
    have := Subgroup.mem_centralizer_singleton_iff.mp (hle (hAgen ▸ hu))
    rw [← this, mul_inv_cancel_right]
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hl₀A e heA)
  have hl₀e : l₀ * e * l₀⁻¹ = d ^ m * e := by rw [hm]; group
  set α : ZMod 3 := (m : ZMod 3) with hα
  have hl₀e' : l₀ * e * l₀⁻¹ = d ^ α.val * e := by rw [hl₀e, zpow_eq_pow_val hd3]
  have hα0 : α ≠ 0 := by
    intro h0
    obtain ⟨u, hu, hu1⟩ := hl₀1
    apply hu1
    refine hcen l₀ hl₀d ?_ hl₀c u hu
    rw [hl₀e', h0, ZMod.val_zero, pow_zero, one_mul]
  have hM0 : coordMat f ⟨l₀, hl₀⟩ = !![1, α, 0; 0, 1, 0; 0, 0, 1] := by
    apply coordMat_eq'
    · rw [hfd', hfv]
      simp [hl₀d, ZMod.val_one]
    · rw [hfe', hfv]
      simp [hl₀e', ZMod.val_one]
    · rw [hfc', hfv]
      simp [hl₀c, ZMod.val_one]
  obtain ⟨m', hm'⟩ := Subgroup.mem_zpowers_iff.mp (hl₁A e heA)
  have hl₁e : l₁ * e * l₁⁻¹ = d ^ m' * e := by rw [hm']; group
  set x : ZMod 3 := (m' : ZMod 3) with hx
  have hl₁e' : l₁ * e * l₁⁻¹ = d ^ x.val * e := by rw [hl₁e, zpow_eq_pow_val hd3]
  have hl₁d' : l₁ * d * l₁⁻¹ = d ^ 2 := by
    rw [hl₁d, inv_eq_iff_mul_eq_one, ← pow_succ']
    exact hd3
  have hM1 : coordMat f ⟨l₁, hl₁⟩ = !![2, x, 0; 0, 1, 0; 0, 0, 1] := by
    apply coordMat_eq'
    · rw [hfd', hfv]
      simp only [hl₁d']
      simp
      rfl
    · rw [hfe', hfv]
      simp [hl₁e', ZMod.val_one]
    · rw [hfc', hfv]
      simp [hl₁c, ZMod.val_one]
  set f₂ := w₀ * l₀ * w₀⁻¹ with hf₂
  have hf₂N : f₂ ∈ Subgroup.normalizer (A : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hw₀ hl₀) (Subgroup.inv_mem _ hw₀)
  have hf₂e : f₂ * e * f₂⁻¹ = e := by
    rw [hf₂, he]
    calc w₀ * l₀ * w₀⁻¹ * (w₀ * d * w₀⁻¹) * (w₀ * l₀ * w₀⁻¹)⁻¹ = w₀ * (l₀ * d * l₀⁻¹) * w₀⁻¹ :=
          by group
      _ = w₀ * d * w₀⁻¹ := by rw [hl₀d]
  have hf₂A : ∀ u ∈ A, f₂ * u * f₂⁻¹ * u⁻¹ ∈ Subgroup.zpowers e := by
    intro u hu
    have hu' : w₀⁻¹ * u * w₀⁻¹⁻¹ ∈ A :=
      (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hw₀) u).mp hu
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hl₀A _ hu')
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    have h1 : f₂ * u * f₂⁻¹ * u⁻¹ =
        w₀ * (l₀ * (w₀⁻¹ * u * w₀⁻¹⁻¹) * l₀⁻¹ * (w₀⁻¹ * u * w₀⁻¹⁻¹)⁻¹) * w₀⁻¹ := by
      rw [hf₂]
      group
    rw [h1, ← hk, he, ← conj_zpow]
  obtain ⟨m₂, hm₂⟩ := Subgroup.mem_zpowers_iff.mp (hf₂A d hdA)
  obtain ⟨m₃, hm₃⟩ := Subgroup.mem_zpowers_iff.mp (hf₂A c hcA)
  set β : ZMod 3 := (m₂ : ZMod 3) with hβ
  set γ : ZMod 3 := (m₃ : ZMod 3) with hγ
  have hf₂d : f₂ * d * f₂⁻¹ = d * e ^ β.val := by
    have h1 : f₂ * d * f₂⁻¹ = e ^ m₂ * d := by rw [hm₂]; group
    rw [h1, zpow_eq_pow_val he3, hcomm _ (A.pow_mem heA _) d hdA]
  have hf₂c : f₂ * c * f₂⁻¹ = e ^ γ.val * c := by
    have h1 : f₂ * c * f₂⁻¹ = e ^ m₃ * c := by rw [hm₃]; group
    rw [h1, zpow_eq_pow_val he3]
  have hβ0 : β ≠ 0 := by
    intro h0
    apply hα0
    have hf₂d' : f₂ * d * f₂⁻¹ = d := by rw [hf₂d, h0, ZMod.val_zero, pow_zero, mul_one]
    have hBC : B ≤ Subgroup.centralizer ({f₂} : Set G) := by
      rw [← hBde, Subgroup.closure_le]
      intro v hv
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      rcases hv with hv | hv <;> rw [hv]
      · exact mul_comm_of_conj_eq hf₂d'
      · exact mul_comm_of_conj_eq hf₂e
    have hwe : w₀ * e * w₀⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.mp hw₀B e).mp heB
    have h1 : l₀ * e * l₀⁻¹ = e := by
      have h2 := Subgroup.mem_centralizer_singleton_iff.mp (hBC hwe)
      calc l₀ * e * l₀⁻¹ = w₀⁻¹ * (f₂ * (w₀ * e * w₀⁻¹) * f₂⁻¹) * w₀ := by rw [hf₂]; group
        _ = w₀⁻¹ * (w₀ * e * w₀⁻¹) * w₀ := by rw [← h2, mul_inv_cancel_right]
        _ = e := by group
    rw [hl₀e'] at h1
    have h3 : d ^ α.val = 1 := by
      calc d ^ α.val = d ^ α.val * e * e⁻¹ := by group
        _ = 1 := by rw [h1, mul_inv_cancel]
    have hdo : orderOf d = 3 := orderOf_eq_prime hd3 hd1
    have h4 := orderOf_dvd_of_pow_eq_one h3
    rw [hdo] at h4
    have h5 : α.val < 3 := ZMod.val_lt α
    have h6 : α.val = 0 := by omega
    exact (ZMod.val_eq_zero α).mp h6
  have hF2 : coordMat f ⟨f₂, hf₂N⟩ = !![1, 0, 0; β, 1, γ; 0, 0, 1] := by
    apply coordMat_eq'
    · rw [hfd', hfv]
      simp [hf₂d, ZMod.val_one]
    · rw [hfe', hfv]
      simp [hf₂e, ZMod.val_one]
    · rw [hfc', hfv]
      simp [hf₂c, ZMod.val_one]
  set L0 : Subgroup.normalizer (A : Set G) := ⟨l₀, hl₀⟩
  set L1 : Subgroup.normalizer (A : Set G) := ⟨l₁, hl₁⟩
  set F2 : Subgroup.normalizer (A : Set G) := ⟨f₂, hf₂N⟩
  rcases goodWord_cases α β γ x hα0 hβ0 with h | h | h | h
  · exact key F2 (by rwa [hF2])
  · exact key (F2 * L1 * F2 * L1 * F2) (by simpa only [coordMat_mul, hM1, hF2] using h)
  · exact key (F2 * L0 * L1 * F2 * F2) (by simpa only [coordMat_mul, hM0, hM1, hF2] using h)
  · exact key (F2 * L0 * L0 * L1 * F2 * F2) (by simpa only [coordMat_mul, hM0, hM1, hF2] using h)

end CaseOne

end CFSG.RankThree.PartTwo.Sec11
