module

public import CFSG.Quasithin.Background.SmithB51SL3Lin

public section

namespace CFSG.Quasithin

namespace B5

open CFSG.Assembly.LowTwoRank Matrix
open scoped Matrix

variable {K : Type} [Field K]

private def slaT (g : ↥(StatedSL 3 K)) : Matrix (Fin 3) (Fin 3) K :=
  (((g⁻¹ : ↥(StatedSL 3 K)) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)ᵀ

private def slaDual (D : Subgroup ↥(StatedSL 3 K)) : Submodule K (Fin 3 → K) where
  carrier := {z | ∀ g ∈ D, slaT g *ᵥ z = z}
  add_mem' := fun ha hb g hg => by rw [Matrix.mulVec_add, ha g hg, hb g hg]
  zero_mem' := fun g _ => Matrix.mulVec_zero _
  smul_mem' := fun c v hv g hg => by rw [Matrix.mulVec_smul, hv g hg]

private theorem mem_slaDual {D : Subgroup ↥(StatedSL 3 K)} {z : Fin 3 → K} :
    z ∈ slaDual D ↔ ∀ g ∈ D, slaT g *ᵥ z = z := Iff.rfl

private theorem sla_dot_transpose (M : Matrix (Fin 3) (Fin 3) K) (c z : Fin 3 → K) :
    c ⬝ᵥ (Mᵀ *ᵥ z) = z ⬝ᵥ (M *ᵥ c) := by
  rw [Matrix.mulVec_transpose, dotProduct_comm, Matrix.dotProduct_mulVec]

private def slaPsi (A : GL (Fin 3) K) (σ : K ≃+* K) (z : Fin 3 → K) : Fin 3 → K :=
  (A : Matrix (Fin 3) (Fin 3) K) *ᵥ (fun i => σ (z i))

private theorem slaPsi_injective (A : GL (Fin 3) K) (σ : K ≃+* K) :
    Function.Injective (slaPsi A σ) := by
  intro z z' h
  have h1 : (fun i => σ (z i)) = (fun i => σ (z' i)) := by
    have := congrArg (fun y => ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ y) h
    simpa [slaPsi, Matrix.mulVec_mulVec] using this
  funext i
  exact σ.injective (congrFun h1 i)

private theorem slaPsi_act {θ : ↥(StatedSL 3 K) ≃* ↥(StatedSL 3 K)} {Aθ : GL (Fin 3) K}
    {σ : K ≃+* K}
    (hθ : ∀ g : ↥(StatedSL 3 K),
      (((θ g : ↥(StatedSL 3 K)) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        (Aθ : Matrix (Fin 3) (Fin 3) K) * (slaT g).map σ *
          ((Aθ⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))
    (g : ↥(StatedSL 3 K)) (z : Fin 3 → K) :
    slAct (θ g) (slaPsi Aθ σ z) = slaPsi Aθ σ (slaT g *ᵥ z) := by
  unfold slAct slaPsi
  rw [hθ g, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec _ _ (Aθ : Matrix (Fin 3) (Fin 3) K), Units.inv_mul, Matrix.one_mulVec]
  congr 1
  funext i
  exact (RingHom.map_mulVec σ.toRingHom (slaT g) z i).symm

private theorem sla_card_fix_map {θ : ↥(StatedSL 3 K) ≃* ↥(StatedSL 3 K)} {Aθ : GL (Fin 3) K}
    {σ : K ≃+* K} [Finite K]
    (hθ : ∀ g : ↥(StatedSL 3 K),
      (((θ g : ↥(StatedSL 3 K)) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        (Aθ : Matrix (Fin 3) (Fin 3) K) * (slaT g).map σ *
          ((Aθ⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))
    (D : Subgroup ↥(StatedSL 3 K)) :
    Nat.card ↥(fixK (D.map θ.toMonoidHom)) = Nat.card ↥(slaDual D) := by
  have key : ∀ z, z ∈ slaDual D ↔ slaPsi Aθ σ z ∈ fixK (D.map θ.toMonoidHom) := by
    intro z
    constructor
    · intro hz h hh
      obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.1 hh
      show slAct (θ g) (slaPsi Aθ σ z) = slaPsi Aθ σ z
      rw [slaPsi_act hθ, hz g hg]
    · intro hz g hg
      have := hz (θ g) (Subgroup.mem_map.2 ⟨g, hg, rfl⟩)
      change slAct (θ g) (slaPsi Aθ σ z) = slaPsi Aθ σ z at this
      rw [slaPsi_act hθ] at this
      exact slaPsi_injective Aθ σ this
  let e : (Fin 3 → K) ≃ (Fin 3 → K) :=
    Equiv.ofBijective (slaPsi Aθ σ) (Finite.injective_iff_bijective.1 (slaPsi_injective Aθ σ))
  exact (Nat.card_congr (e.subtypeEquiv key)).symm

private theorem sla_finrank_fix_map {θ : ↥(StatedSL 3 K) ≃* ↥(StatedSL 3 K)} {Aθ : GL (Fin 3) K}
    {σ : K ≃+* K} [Finite K]
    (hθ : ∀ g : ↥(StatedSL 3 K),
      (((θ g : ↥(StatedSL 3 K)) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        (Aθ : Matrix (Fin 3) (Fin 3) K) * (slaT g).map σ *
          ((Aθ⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))
    (D : Subgroup ↥(StatedSL 3 K)) :
    Module.finrank K (fixK (D.map θ.toMonoidHom)) = Module.finrank K (slaDual D) := by
  have h := sla_card_fix_map hθ D
  have h1 : Nat.card ↥(fixK (D.map θ.toMonoidHom)) =
      Nat.card K ^ Module.finrank K (fixK (D.map θ.toMonoidHom)) :=
    Module.natCard_eq_pow_finrank (K := K)
  have h2 : Nat.card ↥(slaDual D) = Nat.card K ^ Module.finrank K (slaDual D) :=
    Module.natCard_eq_pow_finrank (K := K)
  rw [h1, h2] at h
  exact Nat.pow_right_injective (Nat.succ_le_of_lt Finite.one_lt_card) h

private theorem sla_core [Finite K] (D : Subgroup ↥(StatedSL 3 K))
    (h2 : Module.finrank K (fixK D) = 2) (h2' : Module.finrank K (slaDual D) = 2) :
    Nat.card ↥D ≤ Nat.card K := by
  classical
  let B : LinearMap.BilinForm K (Fin 3 → K) := Matrix.toBilin' (1 : Matrix (Fin 3) (Fin 3) K)
  have hBnd : B.Nondegenerate :=
    LinearMap.BilinForm.nondegenerate_toBilin'_of_det_ne_zero' _ (by simp)
  have hBapp : ∀ x y, B x y = x ⬝ᵥ y := fun x y => by
    rw [Matrix.toBilin'_apply', Matrix.one_mulVec]
  let L : Submodule K (Fin 3 → K) := B.orthogonal (fixK D)
  have hLdim : Module.finrank K L = 1 := by
    rw [LinearMap.BilinForm.finrank_orthogonal hBnd, Module.finrank_fin_fun, h2]
  have htop : slaDual D ≠ ⊤ := by
    intro h
    rw [h, finrank_top, Module.finrank_fin_fun] at h2'
    omega
  obtain ⟨z₀, hz₀⟩ : ∃ z₀, z₀ ∉ slaDual D := by
    by_contra hall
    push Not at hall
    exact htop (eq_top_iff.2 fun z _ => hall z)
  have hsup : slaDual D ⊔ Submodule.span K {z₀} = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have hlt : slaDual D < slaDual D ⊔ Submodule.span K {z₀} := by
      refine lt_of_le_of_ne le_sup_left fun h => hz₀ ?_
      have hz : z₀ ∈ slaDual D ⊔ Submodule.span K {z₀} :=
        Submodule.mem_sup_right (Submodule.mem_span_singleton_self z₀)
      rwa [← h] at hz
    have h1 := Submodule.finrank_lt_finrank_of_lt hlt
    have h3 := Submodule.finrank_le (slaDual D ⊔ Submodule.span K {z₀})
    rw [Module.finrank_fin_fun] at h3 ⊢
    omega
  have hmemL : ∀ g ∈ D, ∀ z, slaT g *ᵥ z - z ∈ L := by
    intro g hg z
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro c hc
    rw [hBapp, dotProduct_sub, slaT, sla_dot_transpose]
    have hfix : slAct g⁻¹ c = c := hc g⁻¹ (D.inv_mem hg)
    change z ⬝ᵥ slAct g⁻¹ c - c ⬝ᵥ z = 0
    rw [hfix, dotProduct_comm, sub_self]
  let F : ↥D → ↥L := fun g => ⟨slaT g.1 *ᵥ z₀ - z₀, hmemL g.1 g.2 z₀⟩
  have hF : Function.Injective F := by
    intro g g' hgg'
    have h1 : slaT g.1 *ᵥ z₀ = slaT g'.1 *ᵥ z₀ := sub_left_injective (congrArg Subtype.val hgg')
    have h2 : ∀ z, slaT g.1 *ᵥ z = slaT g'.1 *ᵥ z := by
      intro z
      have hz : z ∈ slaDual D ⊔ Submodule.span K {z₀} := hsup ▸ Submodule.mem_top
      obtain ⟨w, hw, y, hy, rfl⟩ := Submodule.mem_sup.1 hz
      obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hy
      rw [Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
        mem_slaDual.1 hw g.1 g.2, mem_slaDual.1 hw g'.1 g'.2, h1]
    have h3 : slaT g.1 = slaT g'.1 := Matrix.ext_iff_mulVec.2 h2
    have h4 : g.1⁻¹ = g'.1⁻¹ := Subtype.ext (Units.ext (Matrix.transpose_inj.1 h3))
    exact Subtype.ext (inv_injective h4)
  calc Nat.card ↥D ≤ Nat.card ↥L := Nat.card_le_card_of_injective F hF
    _ = Nat.card K := by rw [Module.natCard_eq_pow_finrank (K := K), hLdim, pow_one]

theorem sl3_pair_bound [Finite K] [CharP K 2] {n : ℕ} (hK : Nat.card K = 2 ^ n)
    (D : Subgroup ↥(StatedSL 3 K)) (hsq : ∀ g ∈ D, g * g = 1)
    (hcomm : ∀ g ∈ D, ∀ h ∈ D, g * h = h * g)
    (θ : ↥(StatedSL 3 K) ≃* ↥(StatedSL 3 K)) (Aθ : GL (Fin 3) K) (σ : K ≃+* K)
    (hθ : ∀ g : ↥(StatedSL 3 K),
      (((θ g : ↥(StatedSL 3 K)) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        (Aθ : Matrix (Fin 3) (Fin 3) K) *
          ((((g⁻¹ : ↥(StatedSL 3 K)) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)ᵀ).map σ *
            ((Aθ⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) :
    3 * rk ↥D ≤ 2 * (n * (3 - Module.finrank K (fixK D)) +
      n * (3 - Module.finrank K (fixK (D.map θ.toMonoidHom)))) := by
  by_cases hD : D = ⊥
  · subst hD
    rw [rk_bot]
    omega
  have hDp : IsPGroup 2 ↥D :=
    isPGroup_two_of_sq_eq_one fun v => Subtype.ext (by simpa [pow_two] using hsq v.1 v.2)
  have hcardD : Nat.card ↥D = 2 ^ rk ↥D := card_eq_two_pow_of_isPGroup hDp
  have h2n : rk ↥D ≤ n * 2 := by
    have h1 := card_le_sq hsq hcomm
    rw [hcardD, hK, ← pow_mul] at h1
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h1
  have ha : Module.finrank K (fixK D) ≤ 2 := finrank_le_two_of_ne_top (fixK_ne_top hD)
  have hD' : D.map θ.toMonoidHom ≠ ⊥ := fun h =>
    hD ((Subgroup.map_eq_bot_iff_of_injective D θ.injective).1 h)
  have hb : Module.finrank K (fixK (D.map θ.toMonoidHom)) ≤ 2 :=
    finrank_le_two_of_ne_top (fixK_ne_top hD')
  by_cases hcase : Module.finrank K (fixK D) = 2 ∧
      Module.finrank K (fixK (D.map θ.toMonoidHom)) = 2
  · obtain ⟨h1, h2⟩ := hcase
    have hdual : Module.finrank K (slaDual D) = 2 := by
      rw [← sla_finrank_fix_map hθ D, h2]
    have hcore := sla_core D h1 hdual
    rw [hcardD, hK] at hcore
    have : rk ↥D ≤ n := (Nat.pow_le_pow_iff_right (by norm_num)).1 hcore
    rw [h1, h2]
    omega
  · have h3 : 3 ≤ (3 - Module.finrank K (fixK D)) +
        (3 - Module.finrank K (fixK (D.map θ.toMonoidHom))) := by omega
    have h4 := Nat.mul_le_mul_left n h3
    rw [Nat.mul_add] at h4
    nlinarith

end B5

end CFSG.Quasithin
