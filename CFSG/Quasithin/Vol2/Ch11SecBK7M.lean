module

public import CFSG.Quasithin.Vol2.Ch11SecBK7B

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Quasithin Matrix
open CFSG.Quasithin.Vol2.KGNat
open CFSG.Assembly.LowTwoRank (StatedSp)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply)

namespace K7

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem exists_common_centre {ι : Type*}
    (L : ι → (Fin 2 ⊕ Fin 2 → K) →ₗ[K] (Fin 2 ⊕ Fin 2 → K))
    (hLB : ∀ i x y, Matrix.toBilin' (spJ K) (L i x) (L i y) = Matrix.toBilin' (spJ K) x y)
    {D₀ : Set (Fin 2 ⊕ Fin 2 → K)} (hfix : ∀ i, ∀ d ∈ D₀, L i d = d)
    (hD₀ : Nat.card K ^ 3 ≤ Nat.card D₀) {i₀ : ι} {x₀ : Fin 2 ⊕ Fin 2 → K}
    (hx₀ : L i₀ x₀ ≠ x₀) :
    ∃ y : Fin 2 ⊕ Fin 2 → K, y ≠ 0 ∧ ∀ i, ∃ c : K, ∀ x, L i x = mat 2 K (trv y c) *ᵥ x := by
  classical
  have hB : (Matrix.toBilin' (spJ K)).Nondegenerate := toBilin'_spJ_nondegenerate
  set D := Submodule.span K D₀ with hD
  have hq : 1 < Nat.card K := Finite.one_lt_card
  have hV : Module.finrank K (Fin 2 ⊕ Fin 2 → K) = 4 := by
    rw [Module.finrank_fintype_fun_eq_card]
    simp
  have hD3 : 3 ≤ Module.finrank K D := by
    have h1 : Nat.card D₀ ≤ Nat.card D := Nat.card_mono (Set.toFinite _) Submodule.subset_span
    rw [Module.natCard_eq_pow_finrank (K := K) (V := ↥D)] at h1
    exact (pow_le_pow_iff_right₀ hq).mp (hD₀.trans h1)
  have hfixD : ∀ i, ∀ d ∈ D, L i d = d := fun i d hd =>
    LinearMap.eqOn_span (f := L i) (g := LinearMap.id) (fun d hd => hfix i d hd) hd
  set R := (Matrix.toBilin' (spJ K)).orthogonal D with hR
  have hR1 : Module.finrank K R ≤ 1 := by
    rw [hR, LinearMap.BilinForm.finrank_orthogonal hB, hV]
    omega
  have hmem : ∀ i x, L i x - x ∈ R := by
    intro i x
    rw [hR, LinearMap.BilinForm.mem_orthogonal_iff]
    intro d hd
    rw [map_sub, ← hLB i d x, hfixD i d hd, sub_self]
  have hy0 : L i₀ x₀ - x₀ ≠ 0 := sub_ne_zero.mpr hx₀
  have hRy : K ∙ (L i₀ x₀ - x₀) = R :=
    Submodule.eq_of_le_of_finrank_le ((Submodule.span_singleton_le_iff_mem _ R).mpr
      (hmem i₀ x₀)) (by rw [finrank_span_singleton hy0]; exact hR1)
  have hsmul : ∀ i x, ∃ d : K, L i x = x + d • (L i₀ x₀ - x₀) := by
    intro i x
    have h := hmem i x
    rw [← hRy, Submodule.mem_span_singleton] at h
    obtain ⟨d, hd⟩ := h
    exact ⟨d, by rw [hd]; abel⟩
  refine ⟨_, hy0, fun i => ?_⟩
  obtain ⟨x₁, hx₁⟩ := exists_bil_eq_one hy0
  obtain ⟨c, hc⟩ := hsmul i x₁
  refine ⟨c, fun x => ?_⟩
  obtain ⟨d, hd⟩ := hsmul i x
  have e := hLB i x x₁
  rw [hd, hc] at e
  simp only [bil_add_left, bil_add_right, bil_smul_left, bil_smul_right, bil_self, mul_zero,
    add_zero] at e
  rw [bil_comm (L i₀ x₀ - x₀) x₁, hx₁] at e
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rw [hd, trv_mulVec]
  congr 2
  linear_combination e - c * Matrix.toBilin' (spJ K) x (L i₀ x₀ - x₀) * h2

variable {W : Type*} [CommGroup W] {H : Subgroup (MulAut W)} {Z : Subgroup W}
  {π : ↥(StatedSp 2 K) →* ↥H} {f : W → (Fin 2 ⊕ Fin 2 → K)}

theorem exists_isometry_of_fix (hf : IsCoord (linModelNat (StatedSp 2 K)) H Z π f)
    {x : MulAut W} (hxZ : ∀ z ∈ Z, x z ∈ Z) (hxZ' : ∀ z ∈ Z, x⁻¹ z ∈ Z)
    (hxH : ∀ h ∈ H, x * h * x⁻¹ ∈ H) (hxH' : ∀ h ∈ H, x⁻¹ * h * x ∈ H) (hxx : x * x = 1)
    {U : Subgroup W} (hU : ∀ u ∈ U, x u = u) (hcard : Nat.card K ^ 3 ≤ Nat.card (hf.img U)) :
    ∃ L : (Fin 2 ⊕ Fin 2 → K) →ₗ[K] (Fin 2 ⊕ Fin 2 → K), (∀ w, L (f w) = f (x w)) ∧
      (∀ u v, Matrix.toBilin' (spJ K) (L u) (L v) = Matrix.toBilin' (spJ K) u v) ∧
      ∀ d ∈ hf.img U, L d = d := by
  have he0 : (Pi.single (.inl 0) 1 : Fin 2 ⊕ Fin 2 → K) ≠ 0 := fun h =>
    (one_ne_zero : (1 : K) ≠ 0) (by simpa using congrFun h (.inl 0))
  obtain ⟨σ, hσ⟩ := hf.exists_semilinear (fun T hT => commutant_statedSp T hT) he0 x hxZ hxZ'
    hxH'
  set T := hf.autMap x hxZ with hTdef
  have hTf : ∀ w, T (f w) = f (x w) := hf.autMap_apply x hxZ
  have hfixU : ∀ d ∈ hf.img U, T d = d := by
    rintro _ ⟨u, hu, rfl⟩
    rw [hTf, hU u hu]
  have hq : 1 < Nat.card K := Finite.one_lt_card
  have hfix : Nat.card (hf.img U) ≤ Nat.card (fixAdd T) :=
    Nat.card_le_card_of_injective (fun d => (⟨d.1, hfixU d.1 d.2⟩ : fixAdd T))
      fun a b h => Subtype.ext (by have := congrArg Subtype.val h; simpa using this)
  have hM : Nat.card (Fin 2 ⊕ Fin 2 → K) = Nat.card K ^ 4 := by
    rw [Nat.card_fun]
    simp
  have hσid : ∀ c, σ c = c := semilinear_eq_id_of_card_fix hσ (by
    calc Nat.card (Fin 2 ⊕ Fin 2 → K) = Nat.card K ^ 4 := hM
      _ < Nat.card K ^ 6 := Nat.pow_lt_pow_right hq (by norm_num)
      _ = (Nat.card K ^ 3) ^ 2 := by ring
      _ ≤ Nat.card (fixAdd T) ^ 2 := Nat.pow_le_pow_left (hcard.trans hfix) 2)
  let TL : (Fin 2 ⊕ Fin 2 → K) →ₗ[K] (Fin 2 ⊕ Fin 2 → K) :=
    { toFun := T
      map_add' := map_add T
      map_smul' := fun c v => by rw [hσ, hσid]; rfl }
  have hTL : ∀ w, TL (f w) = f (x w) := hTf
  have hnorm : ∀ γ : ↥(StatedSp 2 K), ∃ γ' : ↥(StatedSp 2 K), ∀ v,
      TL (((γ : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v) =
        ((γ' : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ TL v := by
    intro γ
    obtain ⟨γ', hγ'⟩ := hf.onto ⟨_, hxH _ (π γ).2⟩
    refine ⟨γ', fun v => ?_⟩
    have h1 := hf.autMap_lin x hxZ γ' γ (congrArg Subtype.val hγ').symm v
    exact (congrArg T (linModelNat_lin _ γ v).symm).trans (h1.trans (linModelNat_lin _ γ' _))
  obtain ⟨c, hc⟩ := exists_similitude TL hnorm
  have hTT : ∀ v, TL (TL v) = v := by
    intro v
    obtain ⟨w, rfl⟩ := hf.surj v
    rw [hTL, hTL, ← MulAut.mul_apply, hxx, MulAut.one_apply]
  have hc1 : c = 1 := similitude_eq_one hTT hc
  exact ⟨TL, hTL, fun u v => by rw [hc, hc1, one_mul], hfixU⟩

end K7

end CFSG.Quasithin.Vol2.Ch11.SecB
