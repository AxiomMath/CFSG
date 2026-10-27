module

public import CFSG.LocalAnalysis.StandardType.StarFour.Dictionary
public import CFSG.LocalAnalysis.StandardType.StarFour.ThreeLeM
public import CFSG.LocalAnalysis.StandardType.GGSixLSixFiveKnownForms
public import CFSG.LocalAnalysis.StandardType.StarFour.CentralizerSL

public section

namespace CFSG.StandardType.StarFour

open CFSG.Assembly CFSG.Blueprint CFSG.StandardType
open scoped IsMulCommutative

variable {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type} [AddCommGroup V] [Module F V]
  [Module.Finite F V] {X : Type} [Group X]

private theorem hat_mem_repCentSL {P : Type} [CommGroup P] (η : P →* SpecialLinearGroup F V)
    {B₁ D : Subgroup X} (hat : B₁ →* SpecialLinearGroup F V) (hcomm : IsMulCommutative B₁)
    (hDη : η.range = (D.subgroupOf B₁).map hat) (b : B₁) :
    hat b ∈ repCentSL (groupRep η) := by
  haveI : IsMulCommutative B₁ := hcomm
  rw [repCentSL, Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
  intro y hy
  obtain ⟨q, rfl⟩ := hy
  change SpecialLinearGroup.toLinearEquiv (η q) * SpecialLinearGroup.toLinearEquiv (hat b) =
    SpecialLinearGroup.toLinearEquiv (hat b) * SpecialLinearGroup.toLinearEquiv (η q)
  have hq : η q ∈ (D.subgroupOf B₁).map hat := by
    rw [← hDη]
    exact MonoidHom.mem_range.mpr ⟨q, rfl⟩
  obtain ⟨d, _hd, hd⟩ := Subgroup.mem_map.mp hq
  rw [← hd]
  have hinner : hat d * hat b = hat b * hat d := by
    rw [← map_mul, ← map_mul, mul_comm' d b]
  simpa only [map_mul] using congrArg SpecialLinearGroup.toLinearEquiv hinner

private noncomputable def rhoBlock {P : Type} [CommGroup P]
    {η : P →* SpecialLinearGroup F V} (fr : SemiFrame F (groupRep η)) (i : Fin fr.r) :
    repCentSL (groupRep η) →*
      ((Fin (fr.m i) → fr.E i) ≃ₗ[fr.E i] (Fin (fr.m i) → fr.E i)) where
  toFun h := SemiFrame.blockEquiv fr h i
  map_one' := SemiFrame.blockEquiv_one fr i
  map_mul' h₁ h₂ := SemiFrame.blockEquiv_mul fr h₁ h₂ i

private theorem block_comm_of_scalar {P : Type} [CommGroup P]
    (η : P →* SpecialLinearGroup F V) (fr : SemiFrame F (groupRep η)) (i : Fin fr.r)
    (hb : SpecialLinearGroup F V) (hhb : hb ∈ repCentSL (groupRep η)) (a : (fr.E i)ˣ)
    (ha : ∀ w : Fin (fr.m i) → fr.E i,
      SemiFrame.blockLin fr (⟨hb, hhb⟩ : repCentSL (groupRep η)) i w = a • w)
    (u : SpecialLinearGroup F V) (hu : u ∈ fr.slOnBlock i) : hb * u = u * hb := by
  obtain ⟨B, hB⟩ := hu
  apply SpecialLinearGroup.ext
  intro v
  apply fr.Φ.injective
  funext j
  have hb_apply : ∀ (x : V) (k : Fin fr.r),
      fr.Φ (hb x) k = SemiFrame.blockLin fr (⟨hb, hhb⟩ : repCentSL (groupRep η)) k (fr.Φ x k) :=
    fun x k => SemiFrame.blockLin_spec fr ⟨hb, hhb⟩ k x
  by_cases hj : j = i
  · rw [hj]
    have hL : fr.Φ ((hb * u) v) i = a • B (fr.Φ v i) := by
      simp only [SpecialLinearGroup.coe_mul, LinearEquiv.mul_apply]
      rw [hb_apply (u v) i]
      have hu_i : fr.Φ (u v) i = B (fr.Φ v i) := by
        have h := congrFun (hB v) i
        simpa [Function.update_self] using h
      rw [hu_i, ha]
    have hR : fr.Φ ((u * hb) v) i = a • B (fr.Φ v i) := by
      simp only [SpecialLinearGroup.coe_mul, LinearEquiv.mul_apply]
      have hu_i : fr.Φ (u (hb v)) i = B (fr.Φ (hb v) i) := by
        have h := congrFun (hB (hb v)) i
        simpa [Function.update_self] using h
      rw [hu_i, hb_apply v i, ha]
      exact LinearEquiv.map_smul
        (B : (Fin (fr.m i) → fr.E i) ≃ₗ[fr.E i] (Fin (fr.m i) → fr.E i))
        a (fr.Φ v i)
    rw [hL, hR]
  · have hL : fr.Φ ((hb * u) v) j =
        SemiFrame.blockLin fr (⟨hb, hhb⟩ : repCentSL (groupRep η)) j (fr.Φ v j) := by
      simp only [SpecialLinearGroup.coe_mul, LinearEquiv.mul_apply]
      rw [hb_apply (u v) j]
      have hu_j : fr.Φ (u v) j = fr.Φ v j := by
        have h := congrFun (hB v) j
        simpa [Function.update_of_ne hj] using h
      rw [hu_j]
    have hR : fr.Φ ((u * hb) v) j =
        SemiFrame.blockLin fr (⟨hb, hhb⟩ : repCentSL (groupRep η)) j (fr.Φ v j) := by
      simp only [SpecialLinearGroup.coe_mul, LinearEquiv.mul_apply]
      have hu_j : fr.Φ (u (hb v)) j = fr.Φ (hb v) j := by
        have h := congrFun (hB (hb v)) j
        simpa [Function.update_of_ne hj] using h
      rw [hu_j, hb_apply v j]
    rw [hL, hR]

theorem three_le_of_shape {P : Type} [CommGroup P] (η : P →* SpecialLinearGroup F V)
    (fr : SemiFrame F (groupRep η)) (i : Fin fr.r) (hgood : fr.GoodAtBlock i)
    (ψ : SpecialLinearGroup F V →* X) (hψ : Function.Injective ψ) (p : ℕ) (hp : p.Prime)
    (hp2 : p ≠ 2) (B₁ D J : Subgroup X) (hat : B₁ →* SpecialLinearGroup F V)
    (hhat : ∀ (b : B₁) (u : SpecialLinearGroup F V),
      (b : X) * ψ u * (b : X)⁻¹ = ψ (hat b * u * (hat b)⁻¹))
    (hB₁ : IsElemAbelian p B₁) (hcard : p ^ 4 ≤ Nat.card B₁) (hD : D ≤ B₁)
    (hDcard : Nat.card D = p ^ 2) (hDη : η.range = (D.subgroupOf B₁).map hat)
    (hJ : J = (fr.slOnBlock i).map ψ) (hBJ : B₁ ⊓ Subgroup.centralizer (J : Set X) = D) :
    3 ≤ fr.m i := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hcomm : IsMulCommutative B₁ := hB₁.1
  haveI : IsMulCommutative B₁ := hcomm
  letI : CommGroup B₁ := inferInstance
  by_contra hcon
  have hmi : fr.m i = 2 :=
    le_antisymm (Nat.lt_succ_iff.mp (Nat.lt_of_not_le hcon)) hgood.1
  have hpE : (p : fr.E i) ≠ 0 := by
    haveI hchar : CharP (fr.E i) 2 :=
      charP_of_injective_algebraMap (algebraMap F (fr.E i)).injective 2
    intro h0
    have h2dvd : 2 ∣ p := (CharP.cast_eq_zero_iff (fr.E i) 2 p).mp h0
    have hodd : Odd p := (hp.eq_two_or_odd').resolve_left hp2
    exact hodd.not_two_dvd_nat h2dvd
  let hmem : ∀ b : B₁, hat b ∈ repCentSL (groupRep η) :=
    fun b => hat_mem_repCentSL η hat hcomm hDη b
  let ρ₁ : B₁ →* repCentSL (groupRep η) := hat.codRestrict _ hmem
  let ρ : B₁ →* ((Fin (fr.m i) → fr.E i) ≃ₗ[fr.E i] (Fin (fr.m i) → fr.E i)) :=
    (rhoBlock fr i).comp ρ₁
  have hker : ∀ b : B₁, (∃ a : (fr.E i)ˣ, ∀ w, ρ b w = a • w) →
      b ∈ D.subgroupOf B₁ := by
    intro b hb
    obtain ⟨a, ha⟩ := hb
    rw [Subgroup.mem_subgroupOf]
    have hcent : (b : X) ∈ Subgroup.centralizer (J : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [hJ] at hy
      obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hy
      have hcommu : hat b * u = u * hat b :=
        block_comm_of_scalar η fr i (hat b) (hmem b) a (fun w => ha w) u hu
      have h1 : hat b * u * (hat b)⁻¹ = u := by
        rw [hcommu, mul_assoc, mul_inv_cancel, mul_one]
      have h2 : (b : X) * ψ u * (b : X)⁻¹ = ψ u := by
        rw [hhat b u, h1]
      exact (mul_inv_eq_iff_eq_mul.mp h2).symm
    have hmem' : (b : X) ∈ B₁ ⊓ Subgroup.centralizer (J : Set X) := ⟨b.2, hcent⟩
    rw [hBJ] at hmem'
    exact hmem'
  have hcardD : Nat.card (D.subgroupOf B₁) = p ^ 2 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hD).toEquiv).trans hDcard
  have hDsub : Nat.card (D.subgroupOf B₁) ≤ p ^ 2 := le_of_eq hcardD
  have hBp : ∀ b : B₁, b ^ p = 1 := by
    intro b
    apply Subtype.ext
    simpa using hB₁.2 b b.2
  have hne : Module.finrank (fr.E i) (Fin (fr.m i) → fr.E i) ≠ 2 :=
    finrank_ne_two_of_elemAbelian_action (E := fr.E i) (W := Fin (fr.m i) → fr.E i)
      (B := B₁) hp2 hpE hBp ρ (D.subgroupOf B₁) hDsub hker hcard
  rw [Module.finrank_fin_fun] at hne
  exact hne hmi

end CFSG.StandardType.StarFour
