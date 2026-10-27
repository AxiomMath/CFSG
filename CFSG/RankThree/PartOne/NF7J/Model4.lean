module

public import CFSG.RankThree.PartOne.NF7J.Model3

public section

namespace CFSG.RankThree.PartOne.NF7J

open Matrix CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KFU CFSG.Assembly.LowTwoRank
  CFSG.RankThree.PartOne.N143 CFSG.RankThree.PartOne.HESS
open scoped commutatorElement

section Rel

variable {G : Type} [Group G] [Finite G] {p : ℕ} {c : G} {L E : Subgroup G} {f : ℕ} {K : Type}
  [Field K] [Finite K] [CharP K 2] {F : RFrame G p c L E f K} {D : Datum p E}

omit [Finite G] in
theorem commutes_conjBy_iff (w : G) (S S' : Subgroup G) :
    (∀ a ∈ conjBy w S, ∀ b ∈ conjBy w S', a * b = b * a) ↔ (∀ a ∈ S, ∀ b ∈ S', a * b = b * a) := by
  constructor
  · intro h a ha b hb
    have h1 : w * a * w⁻¹ ∈ conjBy w S := by
      rw [Equivariance.mem_conjBy]
      simpa [mul_assoc] using ha
    have h2 : w * b * w⁻¹ ∈ conjBy w S' := by
      rw [Equivariance.mem_conjBy]
      simpa [mul_assoc] using hb
    have := h _ h1 _ h2
    have e : w * (a * b) * w⁻¹ = w * (b * a) * w⁻¹ := by
      calc w * (a * b) * w⁻¹ = (w * a * w⁻¹) * (w * b * w⁻¹) := by group
        _ = (w * b * w⁻¹) * (w * a * w⁻¹) := this
        _ = w * (b * a) * w⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel e)
  · intro h a ha b hb
    rw [Equivariance.mem_conjBy] at ha hb
    have := h _ ha _ hb
    have e : w⁻¹ * (a * b) * w = w⁻¹ * (b * a) * w := by
      calc w⁻¹ * (a * b) * w = (w⁻¹ * a * w) * (w⁻¹ * b * w) := by group
        _ = (w⁻¹ * b * w) * (w⁻¹ * a * w) := this
        _ = w⁻¹ * (b * a) * w := by group
    exact mul_left_cancel (mul_right_cancel e)

variable (B : Base F D)

@[expose] noncomputable def iotaU (x : GL (Fin 3) (ZMod 2)) : Subgroup G := by
  classical
  exact if h : ∃ S, IsIota B x S then Classical.choose h else ⊥

theorem iotaU_spec {x : GL (Fin 3) (ZMod 2)} (h : ∃ S, IsIota B x S) : IsIota B x (iotaU B x) := by
  classical
  unfold iotaU
  simp only [h, ↓reduceDIte]
  exact Classical.choose_spec h

variable (X : EFacts G p c E) (N : Norm F D)

theorem isOrd4_iff (x : GL (Fin 3) (ZMod 2)) : IsOrd4 (x : M32) ↔ x ^ 4 = 1 ∧ x * x ≠ 1 := by
  constructor
  · rintro ⟨-, h2, h4⟩
    refine ⟨Units.ext ?_, fun h => h2 ?_⟩
    · rw [Units.val_pow_eq_pow_val]
      exact h4
    · have := congrArg (fun u : GL (Fin 3) (ZMod 2) => (u : M32)) h
      rw [Units.val_mul] at this
      exact this
  · rintro ⟨h4, h2⟩
    refine ⟨det3_GL x, fun h => h2 (Units.ext ?_), ?_⟩
    · rw [Units.val_mul]
      exact h
    · rw [← Units.val_pow_eq_pow_val, h4]
      rfl

theorem isOrd4_conj {x : GL (Fin 3) (ZMod 2)} (hx : IsOrd4 (x : M32)) (hh : GL (Fin 3) (ZMod 2)) :
    IsOrd4 ((hh * x * hh⁻¹ : GL (Fin 3) (ZMod 2)) : M32) := by
  rw [isOrd4_iff] at hx ⊢
  obtain ⟨h4, h2⟩ := hx
  refine ⟨?_, ?_⟩
  · rw [conj_pow, h4]
    group
  · intro h
    apply h2
    have e : hh * (x * x) * hh⁻¹ = (hh * x * hh⁻¹) * (hh * x * hh⁻¹) := by group
    rw [← e] at h
    have := congrArg (fun u : GL (Fin 3) (ZMod 2) => hh⁻¹ * u * hh) h
    simpa [mul_assoc] using this

theorem isOrd4_inv {x : GL (Fin 3) (ZMod 2)} (hx : IsOrd4 (x : M32)) :
    IsOrd4 ((x⁻¹ : GL (Fin 3) (ZMod 2)) : M32) := by
  rw [isOrd4_iff] at hx ⊢
  obtain ⟨h4, h2⟩ := hx
  refine ⟨?_, fun h => h2 ?_⟩
  · rw [inv_pow, h4, inv_one]
  · calc x * x = (x⁻¹ * x⁻¹)⁻¹ := by rw [_root_.mul_inv_rev, inv_inv]
      _ = 1 := by rw [h, inv_one]

include N in
theorem exists_iota {x : GL (Fin 3) (ZMod 2)} (hx : IsOrd4 (x : M32)) : IsIota B x (iotaU B x) :=
  iotaU_spec B (isIota_exists B N hx)

include X N in
theorem iotaU_conj (hdvd : p ∣ 2 ^ f - 1) (hodd : 2 ^ f % 3 = 2) {x : GL (Fin 3) (ZMod 2)}
    (hx : IsOrd4 (x : M32)) (hh : GL (Fin 3) (ZMod 2)) {w₂ : G}
    (hw₂ : w₂ ∈ Subgroup.normalizer (E : Set G))
    (hw₂e : conjAut E w₂ hw₂ = ((D.e.symm hh : ↥D.H) : MulAut E)) :
    iotaU B (hh * x * hh⁻¹) = conjBy w₂ (iotaU B x) :=
  isIota_unique X B N hdvd hodd (exists_iota B N (isOrd4_conj hx hh))
    (isIota_conj B (exists_iota B N hx) hh hw₂ hw₂e)

include X N in
theorem iotaU_inv (hdvd : p ∣ 2 ^ f - 1) (hodd : 2 ^ f % 3 = 2) {x : GL (Fin 3) (ZMod 2)}
    (hx : IsOrd4 (x : M32)) {y : G} (hy : y ∈ Subgroup.normalizer (E : Set G))
    (hye : conjAut E y hy = D.ν) : iotaU B x⁻¹ = conjBy y (iotaU B x) := by
  have hx' : IsOrd4 ((x⁻¹ : GL (Fin 3) (ZMod 2)) : M32) := isOrd4_inv hx
  exact isIota_unique X B N hdvd hodd (exists_iota B N hx')
    (isIota_inv X B hdvd hodd (exists_iota B N hx) hy hye).1

include X N in
theorem iotaU_inv_ne (hdvd : p ∣ 2 ^ f - 1) (hodd : 2 ^ f % 3 = 2) {x : GL (Fin 3) (ZMod 2)}
    (hx : IsOrd4 (x : M32)) {y : G} (hy : y ∈ Subgroup.normalizer (E : Set G))
    (hye : conjAut E y hy = D.ν) : iotaU B x⁻¹ ≠ iotaU B x := by
  rw [iotaU_inv B X N hdvd hodd hx hy hye]
  exact (isIota_inv X B hdvd hodd (exists_iota B N hx) hy hye).2

include X N in
theorem iotaU_rootGp (hdvd : p ∣ 2 ^ f - 1) (hodd : 2 ^ f % 3 = 2) {x : GL (Fin 3) (ZMod 2)}
    (hx : IsOrd4 (x : M32)) {y : G} (hy : y ∈ Subgroup.normalizer (E : Set G))
    (hye : conjAut E y hy = D.ν) :
    ∀ S₂ ∈ RootGp p E f (D.ν * ((D.e.symm (x * x) : ↥D.H) : MulAut E)),
      S₂ = iotaU B x ∨ S₂ = iotaU B x⁻¹ := by
  intro S₂ hS₂
  obtain ⟨w, hw, hS, hn⟩ := isIota_witness B (exists_iota B N hx)
  rw [hn, RFrame.mem_rootGp_conj_iff hw, B.rootGp_zp X] at hS₂
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hS₂
  have hinv := iotaU_inv B X N hdvd hodd hx hy hye
  rcases hS₂ with h | h
  · left
    have := congrArg (conjBy w) h
    rw [Equivariance.conjBy_conjBy_inv] at this
    rw [this, hS]
  · right
    have := congrArg (conjBy w) h
    rw [Equivariance.conjBy_conjBy_inv] at this
    rw [this, hinv, hS]
    exact (conjBy_y_R X B hdvd hodd hy hye hw).symm

include X N in
theorem iotaU_node {x : GL (Fin 3) (ZMod 2)} (hx : IsOrd4 (x : M32)) :
    iotaU B x ∈ RootGp p E f (D.ν * ((D.e.symm (x * x) : ↥D.H) : MulAut E)) :=
  isIota_node X B (exists_iota B N hx)

@[expose] noncomputable def iotaM (g : M32) : Subgroup G := by
  classical
  exact if h : det3 g = 1 then iotaU B (matUnit' g h) else ⊥

@[expose] def Nrel (g g' : M32) : Prop :=
  ¬ ∀ a ∈ iotaM B g, ∀ b ∈ iotaM B g', a * b = b * a

theorem iotaM_unit (x : GL (Fin 3) (ZMod 2)) : iotaM B (x : M32) = iotaU B x := by
  classical
  unfold iotaM
  simp only [det3_GL x, ↓reduceDIte]
  congr 1
  exact Units.ext (matUnit'_val _ _)

theorem Nrel_unit (x x' : GL (Fin 3) (ZMod 2)) :
    Nrel B (x : M32) (x' : M32) ↔ ¬ ∀ a ∈ iotaU B x, ∀ b ∈ iotaU B x', a * b = b * a := by
  unfold Nrel
  rw [iotaM_unit, iotaM_unit]

theorem Nrel_symm (g g' : M32) (h : Nrel B g g') : Nrel B g' g := by
  intro h'
  apply h
  intro a ha b hb
  exact (h' b hb a ha).symm

theorem det3_mul (A B : M32) : det3 (A * B) = det3 A * det3 B := by
  rw [← det3_eq, ← det3_eq, ← det3_eq, Matrix.det_mul]

theorem exists_unit_of_det {g : M32} (hg : det3 g = 1) : ∃ x : GL (Fin 3) (ZMod 2), (x : M32) = g :=
  ⟨matUnit' g hg, matUnit'_val g hg⟩

include X N in
theorem Nrel_conj (hdvd : p ∣ 2 ^ f - 1) (hodd : 2 ^ f % 3 = 2) {h g g' g₁ g₁' : M32}
    (hh : det3 h = 1) (hg : IsOrd4 g) (hg' : IsOrd4 g') (e1 : h * g = g₁ * h)
    (e2 : h * g' = g₁' * h) : Nrel B g g' ↔ Nrel B g₁ g₁' := by
  have d1 : det3 g₁ = 1 := by
    have := det3_mul h g
    rw [e1, det3_mul, hh, hg.1] at this
    simpa using this
  have d1' : det3 g₁' = 1 := by
    have := det3_mul h g'
    rw [e2, det3_mul, hh, hg'.1] at this
    simpa using this
  obtain ⟨hu, rfl⟩ := exists_unit_of_det hh
  obtain ⟨x, rfl⟩ := exists_unit_of_det hg.1
  obtain ⟨x', rfl⟩ := exists_unit_of_det hg'.1
  obtain ⟨x₁, rfl⟩ := exists_unit_of_det d1
  obtain ⟨x₁', rfl⟩ := exists_unit_of_det d1'
  have u1 : x₁ = hu * x * hu⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq]
    apply Units.ext
    rw [Units.val_mul, Units.val_mul]
    exact e1.symm
  have u2 : x₁' = hu * x' * hu⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq]
    apply Units.ext
    rw [Units.val_mul, Units.val_mul]
    exact e2.symm
  obtain ⟨w₂, hw₂, hw₂e⟩ := D.exists_lift (D.e.symm hu).2
  rw [Nrel_unit, Nrel_unit, u1, u2, iotaU_conj B X N hdvd hodd hg hu hw₂ hw₂e,
    iotaU_conj B X N hdvd hodd hg' hu hw₂ hw₂e, commutes_conjBy_iff]

include X N in
theorem Nrel_inv (hdvd : p ∣ 2 ^ f - 1) (hodd : 2 ^ f % 3 = 2) (hy : ∃ (y : G)
    (hy : y ∈ Subgroup.normalizer (E : Set G)), conjAut E y hy = D.ν) {g g' : M32}
    (hg : IsOrd4 g) (hg' : IsOrd4 g') : Nrel B g g' ↔ Nrel B (g ^ 3) (g' ^ 3) := by
  obtain ⟨y, hy, hye⟩ := hy
  obtain ⟨x, rfl⟩ := exists_unit_of_det hg.1
  obtain ⟨x', rfl⟩ := exists_unit_of_det hg'.1
  have cube : ∀ z : GL (Fin 3) (ZMod 2), IsOrd4 (z : M32) → ((z : M32)) ^ 3 = ((z⁻¹ : GL (Fin 3) (ZMod 2)) : M32) := by
    intro z hz
    rw [isOrd4_iff] at hz
    have h3 : z ^ 3 = z⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      rw [← pow_succ]
      exact hz.1
    rw [← h3, Units.val_pow_eq_pow_val]
  rw [cube x hg, cube x' hg', Nrel_unit, Nrel_unit, iotaU_inv B X N hdvd hodd hg hy hye,
    iotaU_inv B X N hdvd hodd hg' hy hye, commutes_conjBy_iff]

end Rel

end CFSG.RankThree.PartOne.NF7J
