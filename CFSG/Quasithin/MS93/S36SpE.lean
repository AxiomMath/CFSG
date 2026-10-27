module

public import CFSG.Quasithin.MS93.S36SpECore
public import CFSG.Quasithin.MS93.FFMain
public import CFSG.Quasithin.H13.A5S1521b

public section

namespace CFSG.Quasithin.MS93.S36E

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.MS93.S36SP
open CFSG.Quasithin.MS93.S36
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

theorem coreData_two (h : PUHyp M T L) {k : ℕ} (hk2 : 2 ≤ k) {φ : MulAut ↥T} {Y Y' : Subgroup G}
    (hφ : EndSide M T L k φ Y) (hφ' : EndSide M T L k φ⁻¹ Y')
    (hside : (tImage φ (pCoreOf 2 M)).relIndex (normalClosureIn M Y) ≤
      (tImage φ⁻¹ (pCoreOf 2 M)).relIndex (normalClosureIn M Y')) :
    CoreData M T L k φ Y Y' (Uq M T L ⊓ Zq M L) (Uq M T L ⊓ Zq M L) := by
  have hCZ : Uq M T L ⊓ Zq M L ≤ Z0q M T := inf_le_left.trans (Uq_le_Z0q h.L_le)
  have hCn : M ≤ Subgroup.normalizer ((Uq M T L ⊓ Zq M L : Subgroup G) : Set G) :=
    le_normalizer_inf (le_normalizer_Uq h.le_normalizer) (le_normalizer_Zq h.le_normalizer)
  have hCL : L ≤ Subgroup.centralizer ((Uq M T L ⊓ Zq M L : Subgroup G) : Set G) := by
    rw [← Subgroup.le_centralizer_iff]
    exact inf_le_right.trans inf_le_right
  have hCQ : Uq M T L ⊓ Zq M L ≤ pCoreOf 2 M := hCZ.trans h.Z0q_le_pCoreOf
  refine
    { crit' := hφ.crit'
      index := hφ.index
      Yp_ge := hφ.Y_ge
      Yp_le := hφ.Y_le
      Yp_comm := hφ.Y_comm hk2
      not_le := hφ.not_le
      comm_le := hφ.comm_le
      key := hφ.key
      Ym_ge := hφ'.Y_ge
      Ym_le := hφ'.Y_le
      Ym_comm := hφ'.Y_comm hk2
      index_le := hφ'.index_le
      Kp_le := hCZ
      Kp_n := hCn
      Kp_L := hCL
      Kp_E := ?_
      Km_n := hCn
      Km_Z := hCZ
      Km_le := hφ.C_le hk2
      K_inf := hφ.inf_C hk2
      side := hside }
  intro e he c hc
  have hR'Q : normalClosureIn M Y' ≤ pCoreOf 2 M :=
    normalClosureIn_le_of_le (pCoreOf_le' M) (le_normalizer_pCoreOf M)
      (hφ'.Y_le.trans inf_le_right)
  obtain ⟨l, hl, hact⟩ := hφ.key hk2 e (tImage_mono φ hR'Q he)
  have h1 := hact _ ⊥ hCn (fun m _ => by
      rw [Subgroup.mem_normalizer_iff]
      intro x
      simp only [Subgroup.mem_bot]
      constructor
      · rintro rfl
        group
      · intro h1
        have := congrArg (fun y => m⁻¹ * y * m) h1
        simpa [mul_assoc] using this) bot_le hCQ (by
      rw [le_bot_iff, Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact (Z0q_le_center h (hCZ hx) hy).symm) c hc
  rw [Subgroup.mem_bot, mul_inv_eq_one] at h1
  have h2 : l * c * l⁻¹ = c := by
    rw [← Subgroup.mem_centralizer_iff.1 (hCL hl) c hc, mul_inv_cancel_right]
  rw [h2] at h1
  calc e * c = e * c * e⁻¹ * e := by group
    _ = c * e := by rw [h1]

theorem coreData_one (h : PUHyp M T L) {k : ℕ} {φ : MulAut ↥T} {Y Y' K K' : Subgroup G}
    (hφ : EndSide M T L k φ Y) (hφ' : EndSide M T L k φ⁻¹ Y')
    (hK : ⁅Y, pCoreOf 2 M⁆ ≤ K ∧ K ≤ tImage φ (Uq M T L) ∧
      K ≤ Subgroup.centralizer (M : Set G) ∧ K ⊓ tImage φ (Uq M T L ⊓ Zq M L) = ⊥)
    (hK' : ⁅Y', pCoreOf 2 M⁆ ≤ K' ∧ K' ≤ tImage φ⁻¹ (Uq M T L) ∧
      K' ≤ Subgroup.centralizer (M : Set G))
    (hside : (tImage φ (pCoreOf 2 M)).relIndex (normalClosureIn M Y) ≤
      (tImage φ⁻¹ (pCoreOf 2 M)).relIndex (normalClosureIn M Y')) (hk : k = 1) :
    CoreData M T L k φ Y Y' K K' := by
  obtain ⟨hYK, hKU, hKc, hKinf⟩ := hK
  obtain ⟨hYK', hKU', hKc'⟩ := hK'
  have hUT : Uq M T L ≤ T := h.Uq_le_Xq.trans ((Xq_le_pCoreOf M).trans h.pCore_le)
  have hcentZ : ∀ {θ : MulAut ↥T} {J : Subgroup G}, J ≤ tImage θ (Uq M T L) →
      J ≤ Subgroup.centralizer (M : Set G) → J ≤ Z0q M T := by
    intro θ J hJU hJc x hx
    have hxT : x ∈ T := tImage_le θ _ (hJU hx)
    have hx2 : x ^ 2 = 1 := by
      obtain ⟨t, ht, rfl⟩ := mem_tImage.1 (hJU hx)
      have h2 : t ^ 2 = 1 := Subtype.ext (h.isElemAbelian_Uq.2 _ ht)
      rw [← Subgroup.coe_pow, ← map_pow, h2, map_one]
      rfl
    have hxZ : x ∈ omegaOneCenterOf T := by
      refine Subgroup.subset_closure ⟨⟨hxT, ?_⟩, hx2⟩
      exact Subgroup.centralizer_le h.le (hJc hx)
    exact le_normalClosureIn ((PU.omegaOneCenterOf_le T).trans h.le) hxZ
  have hcentn : ∀ {J : Subgroup G}, J ≤ Subgroup.centralizer (M : Set G) →
      M ≤ Subgroup.normalizer (J : Set G) := by
    intro J hJ m hm
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      rw [Subgroup.mem_centralizer_iff.1 (hJ hx) m hm, mul_inv_cancel_right]
      exact hx
    · intro hx
      have h1 := Subgroup.mem_centralizer_iff.1 (hJ hx) m hm
      have e1 : m * x * m⁻¹ = x := by
        have h2 : m * (m * x * m⁻¹) = m * x := by
          rw [h1]
          group
        exact mul_left_cancel h2
      rw [e1] at hx
      exact hx
  have hcentL : ∀ {J : Subgroup G}, J ≤ Subgroup.centralizer (M : Set G) →
      L ≤ Subgroup.centralizer (J : Set G) := by
    intro J hJ
    rw [← Subgroup.le_centralizer_iff]
    exact hJ.trans (Subgroup.centralizer_le h.L_le)
  refine
    { crit' := hφ.crit'
      index := hφ.index
      Yp_ge := hφ.Y_ge
      Yp_le := hφ.Y_le
      Yp_comm := hYK
      not_le := hφ.not_le
      comm_le := hφ.comm_le
      key := fun hk2 => absurd hk2 (by omega)
      Ym_ge := hφ'.Y_ge
      Ym_le := hφ'.Y_le
      Ym_comm := hYK'
      index_le := hφ'.index_le
      Kp_le := hcentZ hKU hKc
      Kp_n := hcentn hKc
      Kp_L := hcentL hKc
      Kp_E := fun e he c hc => (Subgroup.mem_centralizer_iff.1 (hKc hc) e
        ((tImage_le φ _).trans h.le he))
      Km_n := hcentn hKc'
      Km_Z := hcentZ hKU' hKc'
      Km_le := ?_
      K_inf := ?_
      side := hside }
  · calc tImage φ K' ≤ tImage φ (tImage φ⁻¹ (Uq M T L)) := tImage_mono φ hKU'
      _ = Uq M T L := tImage_tImage_inv φ hUT
  · rw [eq_bot_iff, ← hKinf]
    rintro x ⟨hxK, hxK'⟩
    refine ⟨hxK, ?_⟩
    obtain ⟨t, ht, rfl⟩ := mem_tImage.1 hxK'
    have htU : (t : G) ∈ Uq M T L := (apply_mem_tImage_iff φ t).1 (hKU hxK)
    refine apply_mem_tImage φ ⟨htU, h.Uq_le_Xq htU, ?_⟩
    show (t : G) ∈ Subgroup.centralizer (L : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact Subgroup.mem_centralizer_iff.1 (hKc' ht) l (h.L_le hl)

end CFSG.Quasithin.MS93.S36E

namespace CFSG.Quasithin.MS93.S36SP

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.MS93.S36E
open CFSG.Quasithin.MS93.S36

theorem s36SpEnd_holds :
    S36SpEnd := by
  intro G _ _ M T L h k ψ Yp Ym hcom hp hm
  have hSQ : SQTKQuot := fun _ _ _ _ _ _ hS f hf hQ =>
    H13.A5.sqtkGroup_of_surjective_quasisimple hS f hf hQ
  have hk : 1 ≤ k := by
    by_contra hk0
    have h0 : k = 0 := by omega
    have h1 := hp.index
    rw [h0, pow_zero, Subgroup.relIndex_eq_one] at h1
    exact hp.crit h1
  have hm' : EndSide M T L k ψ⁻¹⁻¹ Yp := by rwa [inv_inv]
  rcases (show k = 1 ∨ 2 ≤ k by omega) with hk1 | hk2
  · obtain ⟨Kp, hKp⟩ := hp.two hk1
    obtain ⟨Km, hKm⟩ := hm.two hk1
    by_cases hside : (tImage ψ (pCoreOf 2 M)).relIndex (normalClosureIn M Yp) ≤
        (tImage ψ⁻¹ (pCoreOf 2 M)).relIndex (normalClosureIn M Ym)
    · exact core_false ms14AS_holds hSQ h hk hcom
        (coreData_one h hp hm hKp ⟨hKm.1, hKm.2.1, hKm.2.2.1⟩ hside hk1)
    · have hKp' : ⁅Yp, pCoreOf 2 M⁆ ≤ Kp ∧ Kp ≤ tImage ψ⁻¹⁻¹ (Uq M T L) ∧
          Kp ≤ Subgroup.centralizer (M : Set G) := by
        rw [inv_inv]
        exact ⟨hKp.1, hKp.2.1, hKp.2.2.1⟩
      have hside' : (tImage ψ⁻¹ (pCoreOf 2 M)).relIndex (normalClosureIn M Ym) ≤
          (tImage ψ⁻¹⁻¹ (pCoreOf 2 M)).relIndex (normalClosureIn M Yp) := by
        rw [inv_inv]
        exact le_of_lt (not_le.1 hside)
      exact core_false ms14AS_holds hSQ h hk hcom
        (coreData_one h hm hm' hKm hKp' hside' hk1)
  · by_cases hside : (tImage ψ (pCoreOf 2 M)).relIndex (normalClosureIn M Yp) ≤
        (tImage ψ⁻¹ (pCoreOf 2 M)).relIndex (normalClosureIn M Ym)
    · exact core_false ms14AS_holds hSQ h hk hcom (coreData_two h hk2 hp hm hside)
    · have hside' : (tImage ψ⁻¹ (pCoreOf 2 M)).relIndex (normalClosureIn M Ym) ≤
          (tImage ψ⁻¹⁻¹ (pCoreOf 2 M)).relIndex (normalClosureIn M Yp) := by
        rw [inv_inv]
        exact le_of_lt (not_le.1 hside)
      exact core_false ms14AS_holds hSQ h hk hcom (coreData_two h hk2 hm hm' hside')

end CFSG.Quasithin.MS93.S36SP
