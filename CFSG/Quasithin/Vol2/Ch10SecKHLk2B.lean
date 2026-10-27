module

public import CFSG.Quasithin.Vol2.Ch10SecKHLk2A
public import CFSG.Quasithin.Vol2.Ch10SecKHNine

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.C10KH

open CFSG.Open CFSG.LieType.BorelTits Matrix CFSG.QuasithinUnique
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag SteinbergCH
open scoped Pointwise

variable {K₀ : Type*} [Group K₀] [Finite K₀]

omit [Finite K₀] in
theorem isPGroup_of_map {L : Type*} [Group L] {θ : K₀ →* L} (hker : IsPGroup 2 θ.ker)
    {P : Subgroup K₀} {R' : Subgroup L} (hR' : IsPGroup 2 R') (hP : ∀ p ∈ P, θ p ∈ R') :
    IsPGroup 2 P := by
  intro p
  obtain ⟨a, ha⟩ := hR' ⟨θ p, hP p p.2⟩
  have ha' : θ ((p : K₀) ^ 2 ^ a) = 1 := by
    rw [map_pow]
    exact congrArg Subtype.val ha
  obtain ⟨b, hb⟩ := hker ⟨_, ha'⟩
  refine ⟨a + b, Subtype.ext ?_⟩
  have hb' : ((p : K₀) ^ 2 ^ a) ^ 2 ^ b = 1 := congrArg Subtype.val hb
  rw [Subgroup.coe_pow, pow_add, pow_mul, hb', Subgroup.coe_one]

theorem mem_sup_of_conj_le {n : ℕ} (hn : n = 4 ∨ n = 5)
    {θ : K₀ →* Matrix.SpecialLinearGroup (Fin n) (ZMod 2)} (hθ : Function.Surjective θ)
    (hker : IsPGroup 2 θ.ker) (U₀ : Sylow 2 K₀) {X₀ : Subgroup K₀}
    (hUX : (U₀ : Subgroup K₀) ≤ Subgroup.normalizer (X₀ : Set K₀))
    (h9 : (pCoreOf 2 X₀).relIndex X₀ = 9) {k : K₀}
    (hk : ∀ w ∈ pCoreOf 2 (X₀ ⊔ (U₀ : Subgroup K₀)), k * w * k⁻¹ ∈ (U₀ : Subgroup K₀)) :
    k ∈ X₀ ⊔ (U₀ : Subgroup K₀) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set SL := Matrix.SpecialLinearGroup (Fin n) (ZMod 2)
  obtain ⟨D₀, hDX, hD₀⟩ := exists_le_card_nine h9
  have hdec := fun y hy => exists_inv_mul_mem hDX hD₀ h9 (y := y) hy
  have hPU := pCoreOf_le_of_le_normalizer U₀ hUX
  have hDU := mul_comm_of_le_normalizer hDX hUX hPU hdec
  have hJ : X₀ ⊔ (U₀ : Subgroup K₀) = D₀ ⊔ U₀ :=
    le_antisymm (sup_le (le_sup_of_dec hPU hdec) le_sup_right)
      (sup_le (hDX.trans le_sup_left) le_sup_right)
  have hkerU : θ.ker ≤ (U₀ : Subgroup K₀) := hker.le_sylow_of_normal U₀
  set Ub : Sylow 2 SL := Sylow.mapSurjective hθ U₀ with hUb
  have hUbc : (Ub : Subgroup SL) = (U₀ : Subgroup K₀).map θ := Sylow.coe_mapSurjective _ U₀
  have hDker : D₀ ⊓ θ.ker = ⊥ := by
    obtain ⟨a, ha⟩ := (IsPGroup.iff_card).1 hker
    refine disjoint_iff.1 (Subgroup.disjoint_of_coprime_natCard ?_)
    rw [hD₀, ha]
    exact Nat.Coprime.pow_right a (by norm_num)
  have hDb : Nat.card (D₀.map θ) = 9 := by
    have hinj : Function.Injective (θ.domRestrict D₀) := by
      refine (injective_iff_map_eq_one _).2 fun d hd => ?_
      have hmem : (d : K₀) ∈ D₀ ⊓ θ.ker := ⟨d.2, hd⟩
      rw [hDker, Subgroup.mem_bot] at hmem
      exact Subtype.ext hmem
    rw [← MonoidHom.domRestrict_range, ← hD₀]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hDUb : ((D₀.map θ : Subgroup SL) : Set SL) * ((Ub : Subgroup SL) : Set SL) =
      ((Ub : Subgroup SL) : Set SL) * (D₀.map θ : Subgroup SL) := by
    rw [hUbc, Subgroup.coe_map, Subgroup.coe_map, ← Set.image_mul, ← Set.image_mul, hDU]
  obtain ⟨-, -, hrest⟩ :=
    binary_linear_four_five_nine_Sylow_products_have_abelian_inner_common_action
      (K := ZMod 2) (Nat.card_zmod 2) hn Ub
  obtain ⟨-, ⟨g, a, -, -, -, hY, hB, hRle, hRnormal, hRp, -⟩, -⟩ := hrest _ hDb hDUb
  set R' := (blockRadical n (ZMod 2) (compositionCuts a)).map (MulAut.conj g).toMonoidHom
  have hJb : (X₀ ⊔ (U₀ : Subgroup K₀)).map θ = D₀.map θ ⊔ (Ub : Subgroup SL) := by
    rw [hJ, Subgroup.map_sup, hUbc]
  have hRW : ∀ r ∈ R', ∃ w ∈ pCoreOf 2 (X₀ ⊔ (U₀ : Subgroup K₀)), θ w = r := by
    intro r hr
    have hrJ : r ∈ (X₀ ⊔ (U₀ : Subgroup K₀)).map θ := hJb ▸ hRle hr
    obtain ⟨j, hj, rfl⟩ := hrJ
    refine ⟨j, ?_, rfl⟩
    have hjP : θ j ∈ R' := hr
    set P := R'.comap θ ⊓ (X₀ ⊔ (U₀ : Subgroup K₀))
    have hPJ : P ≤ X₀ ⊔ (U₀ : Subgroup K₀) := inf_le_right
    have hnorm : X₀ ⊔ (U₀ : Subgroup K₀) ≤ Subgroup.normalizer (P : Set K₀) := by
      have hconj : ∀ x ∈ X₀ ⊔ (U₀ : Subgroup K₀), ∀ p ∈ P, x * p * x⁻¹ ∈ P := by
        intro x hx p hp
        refine ⟨?_, Subgroup.mul_mem _ (Subgroup.mul_mem _ hx hp.2) (Subgroup.inv_mem _ hx)⟩
        show θ (x * p * x⁻¹) ∈ R'
        rw [map_mul, map_mul, map_inv]
        have hxJ : θ x ∈ D₀.map θ ⊔ (Ub : Subgroup SL) := hJb ▸ Subgroup.mem_map_of_mem θ hx
        exact hRnormal.conj_mem ⟨θ p, hRle hp.1⟩ hp.1 ⟨θ x, hxJ⟩
      intro x hx
      rw [Subgroup.mem_normalizer_iff]
      intro p
      refine ⟨hconj x hx p, fun h => ?_⟩
      have h' := hconj x⁻¹ (Subgroup.inv_mem _ hx) _ h
      simpa [mul_assoc] using h'
    exact le_pCoreOf_of_le_normalizer 2 hPJ hnorm
      (isPGroup_of_map hker hRp fun p hp => hp.1) ⟨hjP, hj⟩
  have hconjR : ∀ r ∈ blockRadical n (ZMod 2) (compositionCuts a),
      (g⁻¹ * θ k * g) * r * (g⁻¹ * θ k * g)⁻¹ ∈ unitriangular n (ZMod 2) := by
    intro r hr
    have hr' : g * r * g⁻¹ ∈ R' := (mem_map_conj_iff g _ _).2 (by simpa [mul_assoc] using hr)
    obtain ⟨w, hw, hwr⟩ := hRW _ hr'
    have h1 : θ (k * w * k⁻¹) ∈ (Ub : Subgroup SL) :=
      hUbc ▸ Subgroup.mem_map_of_mem θ (hk w hw)
    rw [hB, mem_map_conj_iff, map_mul, map_mul, map_inv, hwr] at h1
    have he : (g⁻¹ * θ k * g) * r * (g⁻¹ * θ k * g)⁻¹ =
        g⁻¹ * (θ k * (g * r * g⁻¹) * (θ k)⁻¹) * g := by group
    rw [he]
    exact h1
  have hθk : θ k ∈ (X₀ ⊔ (U₀ : Subgroup K₀)).map θ := by
    rw [hJb, hY, mem_map_conj_iff]
    exact mem_flagStabilizer_of_conj_le hconjR
  obtain ⟨j, hj, hjk⟩ := hθk
  have hjk' : j⁻¹ * k ∈ θ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hjk, inv_mul_cancel]
  have hkj : k = j * (j⁻¹ * k) := by group
  rw [hkj]
  exact Subgroup.mul_mem _ hj (le_sup_right (a := X₀) (hkerU hjk'))

end CFSG.Quasithin.Vol2.Ch10.SecB.C10KH
