module

public import CFSG.LocalAnalysis.StandardType.FS81.D6FrameK6
public import CFSG.LocalAnalysis.StandardType.FS81.ConstructYD6
public import CFSG.LocalAnalysis.StandardType.FS81.D6Cent
public import CFSG.LocalAnalysis.StandardType.FS81.D6RootCore
public import CFSG.LocalAnalysis.StandardType.FS81.D6Gen
public import CFSG.LocalAnalysis.StandardType.FS81.RootHostOrth

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.StandardType.FrameRoute.FS81

open D6M CFSG.ClassicalInvolution.WeakCT CFSG.Timmesfeld
open scoped Matrix

variable {G : Type} [Group G]

private theorem comm_symm {X Y : Subgroup G}
    (h : ∀ a ∈ X, ∀ c ∈ Y, a * c = c * a) : ∀ a ∈ Y, ∀ c ∈ X, a * c = c * a :=
  fun a ha c hc => (h c hc a ha).symm

private theorem d6_comm_of (U : Fin 6 → Subgroup G)
    (h02 : ∀ a ∈ U 0, ∀ c ∈ U 2, a * c = c * a) (h03 : ∀ a ∈ U 0, ∀ c ∈ U 3, a * c = c * a)
    (h04 : ∀ a ∈ U 0, ∀ c ∈ U 4, a * c = c * a) (h05 : ∀ a ∈ U 0, ∀ c ∈ U 5, a * c = c * a)
    (h13 : ∀ a ∈ U 1, ∀ c ∈ U 3, a * c = c * a) (h14 : ∀ a ∈ U 1, ∀ c ∈ U 4, a * c = c * a)
    (h15 : ∀ a ∈ U 1, ∀ c ∈ U 5, a * c = c * a) (h24 : ∀ a ∈ U 2, ∀ c ∈ U 4, a * c = c * a)
    (h25 : ∀ a ∈ U 2, ∀ c ∈ U 5, a * c = c * a) (h45 : ∀ a ∈ U 4, ∀ c ∈ U 5, a * c = c * a) :
    ∀ i j : Fin 6, i ≠ j → ¬ edgeD 6 i j → ¬ edgeD 6 j i →
      ∀ a ∈ U i, ∀ c ∈ U j, a * c = c * a := by
  intro i j hij h1 h2
  fin_cases i <;> fin_cases j <;>
    first
    | exact absurd rfl hij
    | exact absurd (by decide) h1
    | exact absurd (by decide) h2
    | assumption
    | exact comm_symm (by assumption)

private theorem d6_pair_of (U : Fin 6 → Subgroup G)
    (p01 : ∃ W, LinearBlockStandardPair (ZMod 2) W (U 0) (U 1))
    (p12 : ∃ W, LinearBlockStandardPair (ZMod 2) W (U 1) (U 2))
    (p23 : ∃ W, LinearBlockStandardPair (ZMod 2) W (U 2) (U 3))
    (p34 : ∃ W, LinearBlockStandardPair (ZMod 2) W (U 3) (U 4))
    (p35 : ∃ W, LinearBlockStandardPair (ZMod 2) W (U 3) (U 5)) :
    ∀ i j : Fin 6, edgeD 6 i j → ∃ W, LinearBlockStandardPair (ZMod 2) W (U i) (U j) := by
  intro i j h
  fin_cases i <;> fin_cases j <;>
    first
    | exact absurd h (by decide)
    | assumption

private theorem e7_comm_of (U : Fin 7 → Subgroup G)
    (h01 : ∀ a ∈ U 0, ∀ c ∈ U 1, a * c = c * a) (h03 : ∀ a ∈ U 0, ∀ c ∈ U 3, a * c = c * a)
    (h04 : ∀ a ∈ U 0, ∀ c ∈ U 4, a * c = c * a) (h05 : ∀ a ∈ U 0, ∀ c ∈ U 5, a * c = c * a)
    (h06 : ∀ a ∈ U 0, ∀ c ∈ U 6, a * c = c * a) (h12 : ∀ a ∈ U 1, ∀ c ∈ U 2, a * c = c * a)
    (h14 : ∀ a ∈ U 1, ∀ c ∈ U 4, a * c = c * a) (h15 : ∀ a ∈ U 1, ∀ c ∈ U 5, a * c = c * a)
    (h16 : ∀ a ∈ U 1, ∀ c ∈ U 6, a * c = c * a) (h24 : ∀ a ∈ U 2, ∀ c ∈ U 4, a * c = c * a)
    (h25 : ∀ a ∈ U 2, ∀ c ∈ U 5, a * c = c * a) (h26 : ∀ a ∈ U 2, ∀ c ∈ U 6, a * c = c * a)
    (h35 : ∀ a ∈ U 3, ∀ c ∈ U 5, a * c = c * a) (h36 : ∀ a ∈ U 3, ∀ c ∈ U 6, a * c = c * a)
    (h46 : ∀ a ∈ U 4, ∀ c ∈ U 6, a * c = c * a) :
    ∀ i j : Fin 7, i ≠ j → ¬ edgeE 7 i j → ¬ edgeE 7 j i →
      ∀ a ∈ U i, ∀ c ∈ U j, a * c = c * a := by
  intro i j hij h1 h2
  fin_cases i <;> fin_cases j <;>
    first
    | exact absurd rfl hij
    | exact absurd (by decide) h1
    | exact absurd (by decide) h2
    | assumption
    | exact comm_symm (by assumption)

private theorem e7_pair_of (U : Fin 7 → Subgroup G)
    (p02 : ∃ W, LinearBlockStandardPair (ZMod 2) W (U 0) (U 2))
    (p13 : ∃ W, LinearBlockStandardPair (ZMod 2) W (U 1) (U 3))
    (p23 : ∃ W, LinearBlockStandardPair (ZMod 2) W (U 2) (U 3))
    (p34 : ∃ W, LinearBlockStandardPair (ZMod 2) W (U 3) (U 4))
    (p45 : ∃ W, LinearBlockStandardPair (ZMod 2) W (U 4) (U 5))
    (p56 : ∃ W, LinearBlockStandardPair (ZMod 2) W (U 5) (U 6)) :
    ∀ i j : Fin 7, edgeE 7 i j → ∃ W, LinearBlockStandardPair (ZMod 2) W (U i) (U j) := by
  intro i j h
  fin_cases i <;> fin_cases j <;>
    first
    | exact absurd h (by decide)
    | assumption

private theorem node_rel {K : Subgroup G} (e : ↥K ≃* ↥Om12) :
    (∀ i j : Fin 6, i ≠ j → ¬ edgeD 6 i j → ¬ edgeD 6 j i →
      ∀ a ∈ tr e (node i), ∀ c ∈ tr e (node j), a * c = c * a) ∧
    (∀ i j : Fin 6, edgeD 6 i j →
      ∃ W, LinearBlockStandardPair (ZMod 2) W (tr e (node i)) (tr e (node j))) :=
  ⟨fun _ _ h1 h2 h3 => tr_commute e (node_commute h1 h2 h3), fun _ _ h =>
    (node_pair h).elim fun _ hW => tr_pair e (node_le_Om12 _) (node_le_Om12 _) hW⟩

private theorem node_pair' {K : Subgroup G} (e : ↥K ≃* ↥Om12) {i j : Fin 6} (h : edgeD 6 j i) :
    ∃ W, LinearBlockStandardPair (ZMod 2) W (tr e (node i)) (tr e (node j)) :=
  ((node_rel e).2 j i h).imp fun _ => pair_symm

private theorem iSup_node_eq [Finite G] {b₀ : G} {K E : Subgroup G}
    (hstd : StdLoc b₀ K E Row.D6) (e : ↥K ≃* ↥Om12) : ⨆ j, tr e (node j) = K := by
  obtain ⟨-, ⟨⟨-, -, -, hcenter, -, -, -, -⟩, -, -, -, -, -⟩, ⟨hrow, -⟩⟩ := id hstd
  exact iSup_eq_of_D6_frame hrow hcenter (fun j => tr e (node j)) (fun j => tr_le_K e _)
    (node_rel e).1 (node_rel e).2

private theorem iSup_L₁_eq [Finite G] {b₀ : G} {K E : Subgroup G} {B : Basis3 G 7}
    {e : ↥K ≃* ↥Om12} {w₁ w₂ : G} {K₆ : Subgroup G} (hstd : StdLoc b₀ K E Row.D6)
    (hH : HostData b₀ K E B e w₁ w₂) (hK6 : K6Data K e w₁ w₂ K₆) :
    ⨆ j, (![tr e flip0, K₆, tr e (node 4), tr e (node 3), tr e (node 2), tr e (node 5)] :
      Fin 6 → Subgroup G) j = K.map (MulAut.conj w₁).toMonoidHom := by
  obtain ⟨-, ⟨⟨-, -, -, hcenter, -, -, -, -⟩, -, -, -, -, -⟩, ⟨hrow, -⟩⟩ := id hstd
  have hKc := (node_rel e).1
  have hf0c : ∀ j : Fin 6, j ≠ 1 → ∀ a ∈ tr e flip0, ∀ c ∈ tr e (node j), a * c = c * a :=
    fun _ hj => tr_commute e (flip0_commute_node hj)
  refine iSup_eq_of_D6_frame (isRow_D6_map_conj hrow w₁) (center_map_conj_eq_bot hcenter w₁)
    ![tr e flip0, K₆, tr e (node 4), tr e (node 3), tr e (node 2), tr e (node 5)] (fun j => ?_)
    (d6_comm_of _ (hf0c 4 (by decide)) (hf0c 3 (by decide)) (hf0c 2 (by decide))
      (hf0c 5 (by decide)) hK6.comm_K4 hK6.comm_K3 hK6.comm_K5'
      (hKc 4 2 (by decide) (by decide) (by decide)) (hKc 4 5 (by decide) (by decide) (by decide))
      (hKc 2 5 (by decide) (by decide) (by decide)))
    (d6_pair_of _ hK6.pair_K1' hK6.pair_K5 (node_pair' e (i := 4) (j := 3) (by decide))
      (node_pair' e (i := 3) (j := 2) (by decide)) ((node_rel e).2 3 5 (by decide)))
  fin_cases j
  · show tr e flip0 ≤ _
    rw [← hH.L_flip0]
    exact tr_le_K _ _
  · exact hK6.le_L
  · show tr e (node 4) ≤ _
    rw [← hH.L_node2]
    exact tr_le_K _ _
  · exact hH.K4_le_L
  · show tr e (node 2) ≤ _
    rw [← hH.L_node4]
    exact tr_le_K _ _
  · show tr e (node 5) ≤ _
    rw [← hH.L_node5]
    exact tr_le_K _ _

private theorem e7Frame_rel {K : Subgroup G} (e : ↥K ≃* ↥Om12) {K₆' : Subgroup G}
    {U : Fin 7 → Subgroup G} (hU : U = ![K₆', tr e (node 5), tr e (node 4), tr e (node 3),
      tr e (node 2), tr e (node 1), tr e (node 0)])
    (h5 : ∀ a ∈ K₆', ∀ c ∈ tr e (node 5), a * c = c * a)
    (h3 : ∀ a ∈ K₆', ∀ c ∈ tr e (node 3), a * c = c * a)
    (h2 : ∀ a ∈ K₆', ∀ c ∈ tr e (node 2), a * c = c * a)
    (h1 : ∀ a ∈ K₆', ∀ c ∈ tr e (node 1), a * c = c * a)
    (h0 : ∀ a ∈ K₆', ∀ c ∈ tr e (node 0), a * c = c * a)
    (hp : ∃ W, LinearBlockStandardPair (ZMod 2) W K₆' (tr e (node 4))) :
    (∀ i j : Fin 7, i ≠ j → ¬ edgeE 7 i j → ¬ edgeE 7 j i →
      ∀ a ∈ U i, ∀ c ∈ U j, a * c = c * a) ∧
    (∀ i j : Fin 7, edgeE 7 i j → ∃ W, LinearBlockStandardPair (ZMod 2) W (U i) (U j)) := by
  subst hU
  have hKc := (node_rel e).1
  exact ⟨e7_comm_of _ h5 h3 h2 h1 h0
      (hKc 5 4 (by decide) (by decide) (by decide)) (hKc 5 2 (by decide) (by decide) (by decide))
      (hKc 5 1 (by decide) (by decide) (by decide)) (hKc 5 0 (by decide) (by decide) (by decide))
      (hKc 4 2 (by decide) (by decide) (by decide)) (hKc 4 1 (by decide) (by decide) (by decide))
      (hKc 4 0 (by decide) (by decide) (by decide)) (hKc 3 1 (by decide) (by decide) (by decide))
      (hKc 3 0 (by decide) (by decide) (by decide)) (hKc 2 0 (by decide) (by decide) (by decide)),
    e7_pair_of _ hp (node_pair' e (i := 5) (j := 3) (by decide))
      (node_pair' e (i := 4) (j := 3) (by decide)) (node_pair' e (i := 3) (j := 2) (by decide))
      (node_pair' e (i := 2) (j := 1) (by decide)) (node_pair' e (i := 1) (j := 0) (by decide))⟩

theorem exists_d6Frame [Finite G] {b₀ : G} {K E : Subgroup G}
    (hstd : StdLoc b₀ K E Row.D6) {B : Basis3 G 7} (hB : Adapted B b₀ K E)
    (hrec : RecOutD6 B b₀) :
    ∃ (U : Fin 7 → Subgroup G) (g : G),
      (∀ i j : Fin 7, i ≠ j → ¬ edgeE 7 i j → ¬ edgeE 7 j i →
        ∀ a ∈ U i, ∀ c ∈ U j, a * c = c * a) ∧
      (∀ i j : Fin 7, edgeE 7 i j → ∃ W, LinearBlockStandardPair (ZMod 2) W (U i) (U j)) ∧
      K ≤ ⨆ k, U k ∧ b₀ ∈ ⨆ k, U k ∧ g * b₀ * g⁻¹ ∈ K ∧ g⁻¹ * b₀ * g ∈ K ∧
      g ∈ Subgroup.normalizer (E : Set G) ∧
      (∀ k, U k ≤ K ∨ U k ≤ K.map (MulAut.conj g).toMonoidHom) ∧
      K.map (MulAut.conj g).toMonoidHom ≤ ⨆ k, U k ∧
      (∀ v, g * B.vec v * g⁻¹ = B.vec (wbar1 *ᵥ v)) ∧ ∀ k, k ≠ 0 → U k ≤ K := by
  classical
  obtain ⟨e, w₁, w₂, hH⟩ := exists_hostData hstd hB hrec
  obtain ⟨K₆, hK6⟩ := exists_K6Data hstd hB hrec hH
  obtain ⟨k, hk, hc1, hc0⟩ := exists_K6'_commute hH hK6
  have hb₀ : b₀ = B.vec vθ := by rw [vec_vθ, hB.2.1]
  have hkL : k ∈ K.map (MulAut.conj w₁).toMonoidHom := by
    rw [← hH.L_flip0] at hk
    exact tr_le_K _ _ hk
  have hkc : ∀ {j : Fin 6}, j ≠ 1 → ∀ x ∈ tr e (node j), k * x = x * k :=
    fun hj x hx => tr_commute e (flip0_commute_node hj) k hk x hx
  have hp : ∃ W, LinearBlockStandardPair (ZMod 2) W (K₆.map (MulAut.conj k).toMonoidHom)
      (tr e (node 4)) := by
    obtain ⟨W, hW⟩ := hK6.pair_K5
    have h := pair_map_conj hW k
    rw [map_conj_eq_of_commute (hkc (by decide))] at h
    exact ⟨_, h⟩
  set U : Fin 7 → Subgroup G := ![K₆.map (MulAut.conj k).toMonoidHom, tr e (node 5),
    tr e (node 4), tr e (node 3), tr e (node 2), tr e (node 1), tr e (node 0)] with hU
  obtain ⟨hcomm, hpair⟩ := e7Frame_rel e hU (commute_map_conj hK6.comm_K5' (hkc (by decide)))
    (commute_map_conj hK6.comm_K4 (hkc (by decide)))
    (commute_map_conj hK6.comm_K3 (hkc (by decide))) hc1 hc0 hp
  have hKU : K ≤ ⨆ i, U i := by
    rw [← iSup_node_eq hstd e]
    refine iSup_le fun j => ?_
    fin_cases j
    · exact le_iSup_of_le (6 : Fin 7) le_rfl
    · exact le_iSup_of_le (5 : Fin 7) le_rfl
    · exact le_iSup_of_le (4 : Fin 7) le_rfl
    · exact le_iSup_of_le (3 : Fin 7) le_rfl
    · exact le_iSup_of_le (2 : Fin 7) le_rfl
    · exact le_iSup_of_le (1 : Fin 7) le_rfl
  have hkU : k ∈ ⨆ i, U i := hKU (tr_le_K e _ hk)
  have hK6U : K₆ ≤ ⨆ i, U i := by
    intro z hz
    have h1 : k * z * k⁻¹ ∈ ⨆ i, U i := le_iSup U 0
      (show k * z * k⁻¹ ∈ K₆.map (MulAut.conj k).toMonoidHom from ⟨z, hz, rfl⟩)
    have h2 : z = k⁻¹ * (k * z * k⁻¹) * k := by group
    rw [h2]
    exact mul_mem (mul_mem (inv_mem hkU) h1) hkU
  have hLU : K.map (MulAut.conj w₁).toMonoidHom ≤ ⨆ i, U i := by
    rw [← iSup_L₁_eq hstd hH hK6]
    refine iSup_le fun j => ?_
    fin_cases j
    · exact (tr_le_K e flip0).trans hKU
    · exact hK6U
    all_goals exact (tr_le_K e _).trans hKU
  have hb₀U : b₀ ∈ ⨆ i, U i := by
    refine hLU ?_
    rw [mem_map_conj, hb₀, (hH.w₁v vθ).2, wbar1_vθ]
    exact E7Frame.vec_mem_K hB (vP_zero 0)
  refine ⟨U, w₁, hcomm, hpair, hKU, hb₀U, ?_, ?_, hH.w₁N, fun i => ?_, hLU,
    fun v => (hH.w₁v v).1, fun i hi => ?_⟩
  · rw [hb₀, (hH.w₁v vθ).1, wbar1_vθ]
    exact E7Frame.vec_mem_K hB (vP_zero 0)
  · rw [hb₀, (hH.w₁v vθ).2, wbar1_vθ]
    exact E7Frame.vec_mem_K hB (vP_zero 0)
  · fin_cases i
    · right
      show K₆.map (MulAut.conj k).toMonoidHom ≤ _
      rintro _ ⟨z, hz, rfl⟩
      exact mul_mem (mul_mem hkL (hK6.le_L hz)) (inv_mem hkL)
    all_goals exact Or.inl (tr_le_K e _)
  · fin_cases i
    · exact absurd rfl hi
    all_goals exact tr_le_K e _

theorem d6FrameAt_holds : D6FrameAt :=
  fun _ _ _ _ _ _ hstd _ hB hrec => by
    obtain ⟨U, g, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, -⟩ := exists_d6Frame hstd.toLoc hB hrec
    exact ⟨U, g, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈⟩

theorem l2ConstructYAt_D6_holds : L2ConstructYAt Row.D6 :=
  l2ConstructYAt_D6_of d6FrameAt_holds d6RootCoreAt_holds d6CapAt_holds

end CFSG.StandardType.FrameRoute.FS81
