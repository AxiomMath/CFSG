module

public import CFSG.Quasithin.H13.L32A770f
public import CFSG.Quasithin.H13.L32A753a

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.CosetGeom

variable {G : Type} [Group G] [Finite G] {T L V K : Subgroup G}

namespace Not1471

variable {γ γ' : F8.Geom T L (hz T V)} {g k : ↥((L ⊔ T) ⊔ hz T V)}
  (N : Not1471 T L V (hz T V) γ γ' g k)
include N

omit [Finite G] N in
theorem uα_eq' : conjSub (k : G) (F8.Uγ V (hz T V) (g : G)) =
    conjSub ((k : G) * g) (conjClosure V (hz T V)) := by
  rw [conjSub_mul, F8.Uγ]

theorem uα_le_T (C : Ctx753 T L V K) :
    conjSub ((k : G) * g) (conjClosure V (hz T V)) ≤ T := by
  rw [← (uα_eq' (g := g) (k := k))]
  exact (N.uα_le C.hF98).trans (pCoreOf_le_of_le C.hyp le_sup_right)

theorem uα_le_R1 (C : Ctx753 T L V K) :
    conjSub ((k : G) * g) (conjClosure V (hz T V)) ≤ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) := by
  rw [← (uα_eq' (g := g) (k := k))]
  exact N.uα_le C.hF98

theorem uα_le_hz (C : Ctx753 T L V K) :
    conjSub ((k : G) * g) (conjClosure V (hz T V)) ≤ hz T V :=
  (N.uα_le_T C).trans C.T_le

theorem conjClosure_le_Gα (C : Ctx753 T L V K) :
    conjClosure V (hz T V) ≤ conjSub ((k : G) * g) (hz T V) := by
  have hF := C.hF98
  have h1 := (hF.F913_2 N.setup).1.trans ((pCoreOf_le 2 _).trans inf_le_right)
  rw [N.stab_γ hF] at h1
  have h2 := conjSub_mono (k : G) h1
  rw [conjSub_eq_self_iff.mpr (le_normalizer_conjClosure V _ N.mem), ← conjSub_mul] at h2
  exact h2

theorem comm_le' (C : Ctx753 T L V K) :
    ⁅conjClosure V (hz T V), conjSub ((k : G) * g) (conjClosure V (hz T V))⁆ ≤
      conjClosure V (hz T V) ⊓ conjSub ((k : G) * g) (conjClosure V (hz T V)) := by
  rw [← (uα_eq' (g := g) (k := k))]
  exact N.commutator_le C.hF98

omit N in
theorem uα_comm (C : Ctx753 T L V K) {a b : G}
    (ha : a ∈ conjSub ((k : G) * g) (conjClosure V (hz T V)))
    (hb : b ∈ conjSub ((k : G) * g) (conjClosure V (hz T V))) : a * b = b * a := by
  have h := C.hF98.F911_3
  have h' := F7.isElemAbelian_conjSub (g := (k : G) * g) h
  exact F7.isElemAbelian_comm h' ha hb

omit [Finite G] in
theorem D_eq :
    centralizerMod (conjSub ((k : G) * g) (fsuV1 T V)) (conjClosure V (hz T V))
      (conjSub ((k : G) * g) (conjClosure V (hz T V))) =
      conjSub (k : G) (F8.DH V (fsuV1 T V) (hz T V) (g : G)) := by
  have hUk : conjSub (k : G) (conjClosure V (hz T V)) = conjClosure V (hz T V) :=
    conjSub_eq_self_iff.mpr (le_normalizer_conjClosure V _ N.mem)
  rw [F8.DH, conjSub_centralizerMod, F8.A₁, F8.Uγ, ← conjSub_mul, ← conjSub_mul, hUk]

omit [Finite G] N in
theorem comm_D_le :
    ⁅centralizerMod (conjSub ((k : G) * g) (fsuV1 T V)) (conjClosure V (hz T V))
      (conjSub ((k : G) * g) (conjClosure V (hz T V))),
      conjSub ((k : G) * g) (conjClosure V (hz T V))⁆ ≤ conjSub ((k : G) * g) (fsuV1 T V) := by
  rw [Subgroup.commutator_comm]
  exact commutator_centralizerMod_le _ _ _

theorem inf_le_D (C : Ctx753 T L V K) :
    conjClosure V (hz T V) ⊓ conjSub ((k : G) * g) (conjClosure V (hz T V)) ≤
      centralizerMod (conjSub ((k : G) * g) (fsuV1 T V)) (conjClosure V (hz T V))
        (conjSub ((k : G) * g) (conjClosure V (hz T V))) := by
  rintro u ⟨hu, huα⟩
  have hZN : conjSub ((k : G) * g) (hz T V) ≤
      Subgroup.normalizer (conjSub ((k : G) * g) (fsuV1 T V) : Set G) :=
    conjSub_le_normalizer C.hF98.H_normalizes_V₁ _
  refine ⟨hu, hZN (N.conjClosure_le_Gα C hu), fun a ha => ?_⟩
  rw [uα_comm C huα ha, mul_inv_cancel_right, mul_inv_cancel]
  exact one_mem _

theorem comm_le_D (C : Ctx753 T L V K) :
    ⁅conjClosure V (hz T V), conjSub ((k : G) * g) (conjClosure V (hz T V))⁆ ≤
      centralizerMod (conjSub ((k : G) * g) (fsuV1 T V)) (conjClosure V (hz T V))
        (conjSub ((k : G) * g) (conjClosure V (hz T V))) :=
  (N.comm_le' C).trans (N.inf_le_D C)

theorem Dγ_conj (C : Ctx753 T L V K) :
    conjSub (k : G) (F8.Dγ V (fsuV1 T V) (hz T V) (g : G)) =
      conjSub ((k : G) * g) (conjClosure V (hz T V)) ⊓ pCoreOf 2 (hz T V) := by
  rw [C.hF98.Dγ_eq_inf_pCoreOf N.setup, conjSub_inf,
    conjSub_eq_self_iff.mpr (le_normalizer_pCoreOf 2 _ N.mem), (uα_eq' (g := g) (k := k))]

theorem relIndex_D_le (C : Ctx753 T L V K) :
    (centralizerMod (conjSub ((k : G) * g) (fsuV1 T V)) (conjClosure V (hz T V))
      (conjSub ((k : G) * g) (conjClosure V (hz T V)))).relIndex (conjClosure V (hz T V)) ≤
      (conjSub ((k : G) * g) (conjClosure V (hz T V)) ⊓ pCoreOf 2 (hz T V)).relIndex
        (conjSub ((k : G) * g) (conjClosure V (hz T V))) := by
  have hF := C.hF98
  have hUp : IsPGroup 2 ↥(conjClosure V (hz T V)) := isPGroup_of_isElemAbelian hF.F911_3
  have hUγp : IsPGroup 2 ↥(F8.Uγ V (hz T V) (g : G)) := by
    rw [F8.Uγ]
    exact F7.isPGroup_conjSub hUp
  have hle := N.le
  have hUk : conjSub (k : G) (conjClosure V (hz T V)) = conjClosure V (hz T V) :=
    conjSub_eq_self_iff.mpr (le_normalizer_conjClosure V _ N.mem)
  rw [N.D_eq, ← hUk, relIndex_conjSub, hUk, ← N.Dγ_conj C, ← (uα_eq' (g := g) (k := k)),
    relIndex_conjSub,
    HypF98.relIndex_eq_two_pow_mIdx hUp, HypF98.relIndex_eq_two_pow_mIdx hUγp]
  exact Nat.pow_le_pow_right (by norm_num) hle

theorem one_lt_relIndex (C : Ctx753 T L V K) :
    1 < (conjSub ((k : G) * g) (conjClosure V (hz T V)) ⊓ pCoreOf 2 (hz T V)).relIndex
      (conjSub ((k : G) * g) (conjClosure V (hz T V))) := by
  have hF := C.hF98
  have hUp : IsPGroup 2 ↥(conjClosure V (hz T V)) := isPGroup_of_isElemAbelian hF.F911_3
  have hUγp : IsPGroup 2 ↥(F8.Uγ V (hz T V) (g : G)) := by
    rw [F8.Uγ]
    exact F7.isPGroup_conjSub hUp
  rw [← N.Dγ_conj C, ← (uα_eq' (g := g) (k := k)), relIndex_conjSub,
    HypF98.relIndex_eq_two_pow_mIdx hUγp]
  exact Nat.one_lt_two_pow (Nat.pos_iff_ne_zero.1 N.pos)

theorem exists_sym_of_eq (C : Ctx753 T L V K)
    (heq : mIdx (F8.Uγ V (hz T V) (g : G)) (F8.Dγ V (fsuV1 T V) (hz T V) (g : G)) =
      mIdx (conjClosure V (hz T V)) (F8.DH V (fsuV1 T V) (hz T V) (g : G))) :
    ∃ (δ δ' : F8.Geom T L (hz T V)) (k₂ h₀ : ↥((L ⊔ T) ⊔ hz T V)) (y : G),
      Not1471 T L V (hz T V) δ δ' k₂ h₀ ∧
      conjSub y (conjClosure V (hz T V)) = conjSub ((k : G) * g) (conjClosure V (hz T V)) ∧
      conjSub y (conjSub ((h₀ : G) * k₂) (conjClosure V (hz T V))) = conjClosure V (hz T V) ∧
      conjSub y (hz T V) = conjSub ((k : G) * g) (hz T V) ∧
      conjSub y (conjSub ((h₀ : G) * k₂) (hz T V)) = hz T V ∧
      conjSub y (fsuV1 T V) = conjSub ((k : G) * g) (fsuV1 T V) ∧
      conjSub y (conjSub ((h₀ : G) * k₂) (fsuV1 T V)) = fsuV1 T V := by
  have hF := C.hF98
  have hyp := hF.amalgamHypV
  have hstabγ₁ : stab (F8.γ₁ T L (hz T V)) = hz T V := stab_γ₁ hyp.le₂
  have hn := hF.not_Vγ_le_ballStab_of_lt N.setup N.dγ_lt
  obtain ⟨δ, δ', k₂, y₀, sk, hy₀γ, hy₀γ₁, hUδ, hUγ, hDH, hDγ⟩ :=
    hF.exists_symmetric_setup N.setup hn
  have hb3 : 3 ≤ critDist ((L ⊔ T) ⊔ hz T V) (L ⊔ T) (hz T V) V := hF.three_le_b_and_odd.1
  obtain ⟨-, ⟨γ₂, hγ₂nb, hd⟩⟩ :=
    exists_nbrs_of_geodesic hyp.gen sk.critical.geodesic (by omega : 2 ≤ _)
  obtain ⟨h₀, hh₀1, hh₀2⟩ := exists_stab_smul_eq (γ := F8.γ₁ T L (hz T V)) hγ₂nb
    (adj_γ₀_γ₁ (G₀ := (L ⊔ T) ⊔ hz T V) (G₁ := L ⊔ T) (G₂ := hz T V)).symm
  have hh₀H : (h₀ : G) ∈ hz T V := by
    have := mem_stab_of_smul_eq hh₀1
    rwa [hstabγ₁] at this
  have hUp : IsPGroup 2 ↥(conjClosure V (hz T V)) := isPGroup_of_isElemAbelian hF.F911_3
  have hpos := mIdx_pos_of_lt_of_isPGroup hUp (hF.lemma_14_5_17 N.setup)
  have N' : Not1471 T L V (hz T V) δ δ' k₂ h₀ :=
    { setup := sk
      pos := by
        rw [hUδ, hDγ, mIdx_conjSub]
        exact hpos
      le := le_of_eq (by
        rw [hDH, hUδ, hDγ, mIdx_conjSub, ← heq,
          ← mIdx_conjSub (y₀ : G) (F8.Uγ V (hz T V) (g : G)), hUγ])
      mem := hh₀H
      geo := ⟨γ₂, hγ₂nb, hd, hh₀2⟩ }
  have hUH : ∀ w ∈ hz T V, conjSub w (conjClosure V (hz T V)) = conjClosure V (hz T V) :=
    fun w hw => conjSub_eq_self_iff.mpr (le_normalizer_conjClosure V _ hw)
  have hHH : ∀ w ∈ hz T V, conjSub w (hz T V) = hz T V := fun w hw =>
    conjSub_eq_self_iff.mpr (Subgroup.le_normalizer hw)
  have hV1H : ∀ w ∈ hz T V, conjSub w (fsuV1 T V) = fsuV1 T V := fun w hw =>
    conjSub_eq_self_iff.mpr (hF.H_normalizes_V₁ hw)
  have hUδ' : conjSub (k₂ : G) (conjClosure V (hz T V)) =
      conjSub (y₀ : G) (conjClosure V (hz T V)) := hUδ
  have hUγ' : conjSub (y₀ : G)⁻¹ (conjClosure V (hz T V)) =
      conjSub (g : G) (conjClosure V (hz T V)) := by
    have e := congrArg (conjSub (y₀ : G)⁻¹) hUγ
    rw [conjSub_conjSub_inv] at e
    exact e.symm
  have hy₀γ' : y₀⁻¹ • F8.γ₁ T L (hz T V) = γ := by rw [← hy₀γ, inv_smul_smul]
  have hy₀δ' : y₀⁻¹ • δ = F8.γ₁ T L (hz T V) := by rw [← hy₀γ₁, inv_smul_smul]
  have hgy : (g : G)⁻¹ * (y₀ : G)⁻¹ ∈ hz T V := by
    have h1 : (g⁻¹ * y₀⁻¹) • F8.γ₁ T L (hz T V) = F8.γ₁ T L (hz T V) := by
      rw [mul_smul, hy₀γ', ← N.setup.edge₁, inv_smul_smul]
    have := mem_stab_of_smul_eq h1
    rw [hstabγ₁] at this
    simpa using this
  have hyk : (y₀ : G)⁻¹ * (k₂ : G) ∈ hz T V := by
    have h1 : (y₀⁻¹ * k₂) • F8.γ₁ T L (hz T V) = F8.γ₁ T L (hz T V) := by
      rw [mul_smul, sk.edge₁, hy₀δ']
    have := mem_stab_of_smul_eq h1
    rw [hstabγ₁] at this
    simpa using this
  have hy₀g : (y₀ : G)⁻¹ = (g : G) * ((g : G)⁻¹ * (y₀ : G)⁻¹) := by group
  have hy₀H : conjSub (y₀ : G)⁻¹ (hz T V) = conjSub (g : G) (hz T V) := by
    rw [hy₀g, conjSub_mul, hHH _ hgy]
  have hy₀V1 : conjSub (y₀ : G)⁻¹ (fsuV1 T V) = conjSub (g : G) (fsuV1 T V) := by
    rw [hy₀g, conjSub_mul, hV1H _ hgy]
  have hy : (k : G) * (y₀ : G)⁻¹ * (h₀ : G)⁻¹ * ((h₀ : G) * k₂) =
      (k : G) * ((y₀ : G)⁻¹ * k₂) := by group
  refine ⟨δ, δ', k₂, h₀, (k : G) * (y₀ : G)⁻¹ * (h₀ : G)⁻¹, N', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [conjSub_mul, conjSub_mul, hUH _ (inv_mem hh₀H), hUγ', ← conjSub_mul]
  · rw [← conjSub_mul, hy, conjSub_mul, conjSub_mul, hUδ', conjSub_conjSub_inv, hUH _ N.mem]
  · rw [conjSub_mul, conjSub_mul, hHH _ (inv_mem hh₀H), hy₀H, ← conjSub_mul]
  · rw [← conjSub_mul, hy, conjSub_mul, hHH _ hyk, hHH _ N.mem]
  · rw [conjSub_mul, conjSub_mul, hV1H _ (inv_mem hh₀H), hy₀V1, ← conjSub_mul]
  · rw [← conjSub_mul, hy, conjSub_mul, hV1H _ hyk, hV1H _ N.mem]

end Not1471

end CFSG.Quasithin.H13.L32A
