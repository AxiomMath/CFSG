module

public import CFSG.RankThree.PartTwo.Sec4.HeringK419OneFieldGL3Engine
public import CFSG.RankThree.PartTwo.Sec4.HeringK419OneFieldGL3Char3

public section

namespace CFSG.RankThree.PartTwo.Sec4.HeringOF

open Matrix
open scoped _root_.Classical commutatorElement

theorem commute_scalar_gl {ι : Type} [Fintype ι] [DecidableEq ι] {E : Type} [Field E]
    (g : GL ι E) (z : Eˣ) : Commute g (Matrix.GeneralLinearGroup.scalar ι z) := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar]
  exact ((Matrix.scalar_commute (z : E) (fun r => Commute.all (z : E) r) _)).eq.symm

theorem scalar_gl_injective {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι] {E : Type}
    [Field E] : Function.Injective (Matrix.GeneralLinearGroup.scalar ι (R := E)) := by
  intro a b h
  obtain ⟨i⟩ := ‹Nonempty ι›
  have h1 : ((Matrix.GeneralLinearGroup.scalar ι a : GL ι E) : Matrix ι ι E) =
      ((Matrix.GeneralLinearGroup.scalar ι b : GL ι E) : Matrix ι ι E) := by rw [h]
  rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.GeneralLinearGroup.coe_scalar] at h1
  have h2 := congrFun (congrFun h1 i) i
  simp only [Matrix.scalar_apply, Matrix.diagonal_apply_eq] at h2
  exact Units.ext h2

theorem commutatorElement_mul_central_left {T : Type*} [Group T] {w : T}
    (hw : w ∈ Subgroup.center T) (p q : T) : ⁅p * w, q⁆ = ⁅p, q⁆ := by
  rw [commutatorElement_def, commutatorElement_def]
  have h1 : w * q = q * w := (Subgroup.mem_center_iff.mp hw q).symm
  calc p * w * q * (p * w)⁻¹ * q⁻¹ = p * (w * q) * w⁻¹ * p⁻¹ * q⁻¹ := by group
    _ = p * (q * w) * w⁻¹ * p⁻¹ * q⁻¹ := by rw [h1]
    _ = p * q * p⁻¹ * q⁻¹ := by group

theorem commutatorElement_mul_central_right {T : Type*} [Group T] {w : T}
    (hw : w ∈ Subgroup.center T) (p q : T) : ⁅p, q * w⁆ = ⁅p, q⁆ := by
  rw [commutatorElement_def, commutatorElement_def]
  have h1 : w * p⁻¹ = p⁻¹ * w := (Subgroup.mem_center_iff.mp hw p⁻¹).symm
  calc p * (q * w) * p⁻¹ * (q * w)⁻¹ = p * q * (w * p⁻¹) * w⁻¹ * q⁻¹ := by group
    _ = p * q * (p⁻¹ * w) * w⁻¹ * q⁻¹ := by rw [h1]
    _ = p * q * p⁻¹ * q⁻¹ := by group

section Twisted


theorem not_isType419_of_twisted_gl3 {E : Type} [Field E] [Finite E]
    {T : Type} [Group T] (ρ : T →* GL (Fin 3) E) (hρ : Function.Injective ρ)
    {K : Type} [Group K] (hK : IsType419 K) (hs : IsSimpleGroup K)
    (hZ : Subgroup.center K = ⊥) (θ : T →* K) (hθ : Function.Surjective θ)
    (hker : ∀ t : T, θ t = 1 →
      ∃ z : Eˣ, ρ t = Matrix.GeneralLinearGroup.scalar (Fin 3) z)
    (A : GL (Fin 3) E) (c : Eˣ)
    (hA3 : ((A : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) ^ 3 =
      (c : E) • (1 : Matrix (Fin 3) (Fin 3) E))
    (hAn : ∀ b : E, ((A : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) ≠
      b • (1 : Matrix (Fin 3) (Fin 3) E))
    (htw : ∀ t : T, ∃ z : Eˣ,
      A * ρ t * A⁻¹ = ρ t * Matrix.GeneralLinearGroup.scalar (Fin 3) z) : False := by
  have hnc := Item419Res3.exists_noncommuting_isType419 hK hZ
  have hperfK : commutator K = ⊤ := commutator_eq_top_of_simple_nonabelian hs hnc
  choose z hz using htw
  have hzmul : ∀ s t : T, z (s * t) = z s * z t := by
    intro s t
    apply scalar_gl_injective (ι := Fin 3) (E := E)
    apply mul_left_cancel (a := ρ (s * t))
    rw [← hz (s * t)]
    have h1 : A * ρ (s * t) * A⁻¹ = (A * ρ s * A⁻¹) * (A * ρ t * A⁻¹) := by
      rw [map_mul]
      group
    rw [h1, hz s, hz t, map_mul, map_mul]
    calc ρ s * Matrix.GeneralLinearGroup.scalar (Fin 3) (z s) *
          (ρ t * Matrix.GeneralLinearGroup.scalar (Fin 3) (z t)) =
        ρ s * (Matrix.GeneralLinearGroup.scalar (Fin 3) (z s) * ρ t) *
          Matrix.GeneralLinearGroup.scalar (Fin 3) (z t) := by group
      _ = ρ s * (ρ t * Matrix.GeneralLinearGroup.scalar (Fin 3) (z s)) *
          Matrix.GeneralLinearGroup.scalar (Fin 3) (z t) := by
        rw [(commute_scalar_gl (ρ t) (z s)).eq]
      _ = ρ s * ρ t * (Matrix.GeneralLinearGroup.scalar (Fin 3) (z s) *
          Matrix.GeneralLinearGroup.scalar (Fin 3) (z t)) := by group
  let zh : T →* Eˣ :=
    { toFun := z
      map_one' := by
        apply scalar_gl_injective (ι := Fin 3) (E := E)
        apply mul_left_cancel (a := ρ 1)
        rw [← hz 1, map_one, map_one]
        group
      map_mul' := hzmul }
  have hPA : ∀ t ∈ commutator T, ρ t * A = A * ρ t := by
    intro t ht
    have hle : commutator T ≤ zh.ker := by
      rw [commutator_def]
      refine Subgroup.commutator_le.mpr fun a _ b _ => ?_
      rw [MonoidHom.mem_ker, map_commutatorElement,
        commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm _ _)]
    have h1 : z t = 1 := MonoidHom.mem_ker.mp (hle ht)
    have h2 := hz t
    rw [show z t = 1 from h1, map_one, mul_one] at h2
    calc ρ t * A = (A * ρ t * A⁻¹) * A := by rw [h2]
      _ = A * ρ t := by group
  have hθP : Subgroup.map θ (commutator T) = ⊤ := by
    rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top,
      MonoidHom.range_eq_top_of_surjective θ hθ]
    exact hperfK
  have hsplit : ∀ s : T, ∃ p ∈ commutator T, ∃ w : T, θ w = 1 ∧ s = p * w := by
    intro s
    have hs' : θ s ∈ Subgroup.map θ (commutator T) := by rw [hθP]; exact Subgroup.mem_top _
    obtain ⟨p, hp, hps⟩ := Subgroup.mem_map.mp hs'
    refine ⟨p, hp, p⁻¹ * s, ?_, by group⟩
    rw [map_mul, map_inv, hps, inv_mul_cancel]
  have hcentral : ∀ w : T, θ w = 1 → w ∈ Subgroup.center T := by
    intro w hw
    obtain ⟨y, hy⟩ := hker w hw
    rw [Subgroup.mem_center_iff]
    intro g
    apply hρ
    rw [map_mul, map_mul, hy]
    exact (commute_scalar_gl (ρ g) y).eq
  have hPP : ⁅commutator T, commutator T⁆ = commutator T := by
    refine le_antisymm (Subgroup.commutator_le_self _) ?_
    rw [commutator_def (G := T)]
    refine Subgroup.commutator_le.mpr fun s _ t _ => ?_
    obtain ⟨p₁, hp₁, w₁, hw₁, rfl⟩ := hsplit s
    obtain ⟨p₂, hp₂, w₂, hw₂, rfl⟩ := hsplit t
    rw [commutatorElement_mul_central_left (hcentral w₁ hw₁),
      commutatorElement_mul_central_right (hcentral w₂ hw₂)]
    exact Subgroup.commutator_mem_commutator hp₁ hp₂
  have hP' : commutator (commutator T) = ⊤ :=
    Group.isPerfect_def.mp (Subgroup.isPerfect_iff.mpr hPP)
  let ρ' : commutator T →* GL (Fin 3) E := ρ.comp (commutator T).subtype
  let π' : commutator T →* K := θ.comp (commutator T).subtype
  have hρ' : Function.Injective ρ' := hρ.comp (commutator T).subtype_injective
  have hπ' : Function.Surjective π' := by
    intro k
    obtain ⟨s, hs⟩ := hθ k
    obtain ⟨p, hp, w, hw, rfl⟩ := hsplit s
    refine ⟨⟨p, hp⟩, ?_⟩
    change θ p = k
    rw [← hs, map_mul, hw, mul_one]
  have hker' : ∀ p : commutator T, π' p = 1 →
      ∃ z : Eˣ, ρ' p = Matrix.GeneralLinearGroup.scalar (Fin 3) z := fun p hp => hker p hp
  have hcomm' : ∀ p : commutator T, ρ' p * A = A * ρ' p := fun p => hPA p p.2
  by_cases h3 : (3 : E) = 0
  · haveI : CharP E 3 :=
      (CharP.charP_iff_prime_eq_zero Nat.prime_three).mpr (by exact_mod_cast h3)
    exact not_isType419_of_commute_gl3_char3 hP' ρ' hρ' hK hs hZ π' hπ' hker' A c hA3 hAn hcomm'
  · exact not_isType419_of_commute_gl3 h3 hP' ρ' hρ' hK hs hZ π' hπ' hker' A c hA3 hAn hcomm'

end Twisted

end CFSG.RankThree.PartTwo.Sec4.HeringOF
