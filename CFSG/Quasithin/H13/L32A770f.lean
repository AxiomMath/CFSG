module

public import CFSG.Quasithin.H13.L32A770a

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open CFSG.Quasithin.CosetGeom
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

omit [Finite G] in
theorem mIdx_conjSub (w : G) (X Y : Subgroup G) :
    mIdx (conjSub w X) (conjSub w Y) = mIdx X Y := by
  unfold mIdx
  rw [relIndex_conjSub]

namespace Not1471

variable {γ γ' : F8.Geom T L (hz T V)} {g k : ↥((L ⊔ T) ⊔ hz T V)}
  (N : Not1471 T L V (hz T V) γ γ' g k)
include N

theorem relIndex_Dγ (h : Hyp147 G T L V) (hF : HypF98 T V L (fsuV1 T V) V (hz T V))
    (h2 : (pCoreOf 2 (hz T V)).relIndex (conjSub (k : G) (F8.Uγ V (hz T V) (g : G)) ⊔
      pCoreOf 2 (hz T V)) = 2) :
    (F8.Dγ V (fsuV1 T V) (hz T V) (g : G)).relIndex (F8.Uγ V (hz T V) (g : G)) = 2 := by
  have hWN := N.uα_le_normalizer h hF
  rw [A4.relIndex_sup_eq_of_le_normalizer' hWN, ← Subgroup.inf_relIndex_left] at h2
  rw [hF.Dγ_eq_inf_pCoreOf N.setup, ← relIndex_conjSub (k : G), conjSub_inf,
    conjSub_eq_self_iff.mpr (le_normalizer_pCoreOf 2 _ N.mem)]
  exact h2

theorem comm_D_eq (h : Hyp147 G T L V) (hMod : StmtL32NModule) (h63 : Thm14_7_63)
    (hF : HypF98 T V L (fsuV1 T V) V (hz T V)) (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4)
    (h2 : (pCoreOf 2 (hz T V)).relIndex (conjSub (k : G) (F8.Uγ V (hz T V) (g : G)) ⊔
      pCoreOf 2 (hz T V)) = 2) :
    ⁅centralizerMod (conjSub ((k : G) * g) (fsuV1 T V)) (fsuU T V)
      (conjSub ((k : G) * g) (fsuU T V)), conjSub ((k : G) * g) (fsuU T V)⁆ =
      conjSub ((k : G) * g) (fsuV1 T V) := by
  obtain ⟨s, hsW, hsQ, -⟩ := N.exists_mem_not_mem h hMod hF h2
  have hsR : s ∈ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) := by
    have := N.uα_le hF
    rw [uα_eq (g := g) (k := k) h hMod] at this
    exact this hsW
  set D := centralizerMod (conjSub ((k : G) * g) (fsuV1 T V)) (fsuU T V)
    (conjSub ((k : G) * g) (fsuU T V)) with hD
  have hDU : D ≤ fsuU T V := centralizerMod_le_left _ _ _
  have hcard : Nat.card ↥(conjSub ((k : G) * g) (fsuV1 T V)) = 2 := by
    rw [conjSub, Subgroup.card_map_of_injective (MulAut.conj _).injective]
    exact hF.card_V₁
  have hle : ⁅D, conjSub ((k : G) * g) (fsuU T V)⁆ ≤ conjSub ((k : G) * g) (fsuV1 T V) := by
    rw [Subgroup.commutator_comm]
    exact commutator_centralizerMod_le _ _ _
  rcases HypF98.eq_bot_or_eq_of_card_eq_two hcard hle with hb | he
  · exfalso
    have hDle : D ≤ V ⊔ u0 T V := by
      intro d hd
      refine mem_sup_u0_of_comm_mem h hMod h63 hF h1222 h1332 h1334 hsR hsQ (hDU hd) ?_
      have h1 : ⁅d, s⁆ = 1 := by
        rw [← Subgroup.mem_bot, ← hb]
        exact Subgroup.commutator_mem_commutator hd hsW
      have h2' : s * d * s⁻¹ * d⁻¹ = 1 := by
        rw [commutatorElement_def] at h1
        calc s * d * s⁻¹ * d⁻¹ = (d * s * d⁻¹ * s⁻¹)⁻¹ := by group
          _ = 1 := by rw [h1, inv_one]
      rw [h2']
      exact one_mem _
    have e1 := Subgroup.relIndex_mul_relIndex D (V ⊔ u0 T V) (fsuU T V) hDle
      (sup_le (le_conjClosure V _) (centralizerMod_le_left _ _ _))
    rw [(relIndex_sup_u0 h hMod h63 hF).2, N.relIndex_D h hMod hF h2] at e1
    omega
  · exact he

theorem exists_sym70 (h : Hyp147 G T L V) (hMod : StmtL32NModule)
    (hF : HypF98 T V L (fsuV1 T V) V (hz T V))
    (h2 : (pCoreOf 2 (hz T V)).relIndex (conjSub (k : G) (F8.Uγ V (hz T V) (g : G)) ⊔
      pCoreOf 2 (hz T V)) = 2) :
    ∃ (δ δ' : F8.Geom T L (hz T V)) (k₂ h₀ : ↥((L ⊔ T) ⊔ hz T V)) (y : G),
      Not1471 T L V (hz T V) δ δ' k₂ h₀ ∧
      conjSub y (fsuU T V) = conjSub ((k : G) * g) (fsuU T V) ∧
      conjSub y (conjSub ((h₀ : G) * k₂) (fsuU T V)) = fsuU T V ∧
      conjSub y (hz T V) = conjSub ((k : G) * g) (hz T V) ∧
      conjSub y (conjSub ((h₀ : G) * k₂) (hz T V)) = hz T V ∧
      conjSub y (fsuV1 T V) = conjSub ((k : G) * g) (fsuV1 T V) ∧
      conjSub y (conjSub ((h₀ : G) * k₂) (fsuV1 T V)) = fsuV1 T V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hyp := hF.amalgamHypV
  have hUeq : fsuU T V = conjClosure V (hz T V) := fsuU_eq_conjClosure_hz hMod h
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
  have hγ1 : mIdx (F8.Uγ V (hz T V) (g : G)) (F8.Dγ V (fsuV1 T V) (hz T V) (g : G)) = 1 := by
    unfold mIdx
    rw [N.relIndex_Dγ h hF h2]
    simp
  have hH1 : mIdx (conjClosure V (hz T V)) (F8.DH V (fsuV1 T V) (hz T V) (g : G)) = 1 := by
    unfold mIdx
    rw [N.relIndex_DH h hF h2]
    simp
  have hUγ'' : conjClosure V (hz T V) = conjSub (y₀ : G) (F8.Uγ V (hz T V) (g : G)) := hUγ.symm
  have N' : Not1471 T L V (hz T V) δ δ' k₂ h₀ :=
    { setup := sk
      pos := by
        rw [hUδ, hDγ, mIdx_conjSub, hH1]
        norm_num
      le := le_of_eq (by
        rw [hUδ, hDγ, hDH, mIdx_conjSub, hH1, hUγ'', mIdx_conjSub, hγ1])
      mem := hh₀H
      geo := ⟨γ₂, hγ₂nb, hd, hh₀2⟩ }
  have hUH : ∀ w ∈ hz T V, conjSub w (fsuU T V) = fsuU T V := fun w hw => by
    rw [hUeq]
    exact conjSub_eq_self_iff.mpr (le_normalizer_conjClosure V _ hw)
  have hHH : ∀ w ∈ hz T V, conjSub w (hz T V) = hz T V := fun w hw =>
    conjSub_eq_self_iff.mpr (Subgroup.le_normalizer hw)
  have hV1H : ∀ w ∈ hz T V, conjSub w (fsuV1 T V) = fsuV1 T V := fun w hw =>
    conjSub_eq_self_iff.mpr (hF.H_normalizes_V₁ hw)
  have hUδ' : conjSub (k₂ : G) (fsuU T V) = conjSub (y₀ : G) (fsuU T V) := by
    rw [hUeq]
    exact hUδ
  have hUγ' : conjSub (y₀ : G)⁻¹ (fsuU T V) = conjSub (g : G) (fsuU T V) := by
    have e := congrArg (conjSub (y₀ : G)⁻¹) hUγ
    rw [conjSub_conjSub_inv] at e
    rw [hUeq]
    exact e.symm
  have hy₀γ' : y₀⁻¹ • F8.γ₁ T L (hz T V) = γ := by rw [← hy₀γ, inv_smul_smul]
  have hy₀δ' : y₀⁻¹ • δ = F8.γ₁ T L (hz T V) := by rw [← hy₀γ₁, inv_smul_smul]
  have hstabδ : stab δ = conjSub (k₂ : G) (hz T V) := by
    rw [← sk.edge₁, stab_smul, hstabγ₁]
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

theorem v1_le (h : Hyp147 G T L V) (hMod : StmtL32NModule) (h63 : Thm14_7_63)
    (hF : HypF98 T V L (fsuV1 T V) V (hz T V)) (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4) (h69 : Lemma14_7_69)
    (h2 : (pCoreOf 2 (hz T V)).relIndex (conjSub (k : G) (F8.Uγ V (hz T V) (g : G)) ⊔
      pCoreOf 2 (hz T V)) = 2) :
    fsuV1 T V ≤ ⁅fsuU T V, conjSub ((k : G) * g) (fsuU T V)⁆ := by
  obtain ⟨δ, δ', k₂, h₀, y, N', hU, hW, -, -, -, hV1'⟩ := N.exists_sym70 h hMod hF h2
  have h2' := h69 G T L V h δ δ' k₂ h₀ N'
  have he := N'.comm_D_eq h hMod h63 hF h1222 h1332 h1334 h2'
  have e := congrArg (conjSub y) he
  rw [← conjSub_commutator, conjSub_centralizerMod, hV1', hU, hW] at e
  rw [← e, Subgroup.commutator_comm]
  exact Subgroup.commutator_mono le_rfl (centralizerMod_le_left _ _ _)

end Not1471

end CFSG.Quasithin.H13.L32A
