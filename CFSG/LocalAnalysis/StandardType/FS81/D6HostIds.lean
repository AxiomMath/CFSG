module

public import CFSG.LocalAnalysis.StandardType.FS81.D6Hosts
public import CFSG.LocalAnalysis.StandardType.FS81.D6ModelOm
public import CFSG.LocalAnalysis.StandardType.FS81.D6ModelTorus
public import CFSG.LocalAnalysis.StandardType.FS81.D6Norm

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.StandardType.FrameRoute.FS81.D6M

open CFSG.ClassicalInvolution.WeakCT CFSG.Timmesfeld
open scoped Matrix

variable {G : Type} [Group G]

private theorem six_le_Om12 {X : Subgroup (V12 ≃ₗ[ZMod 2] V12)}
    (hX : X = node 0 ∨ X = node 2 ∨ X = node 4 ∨ X = node 5 ∨ X = flip0 ∨ X = flip2) :
    X ≤ Om12 := by
  rcases hX with rfl | rfl | rfl | rfl | rfl | rfl
  exacts [node_le_Om12 0, node_le_Om12 2, node_le_Om12 4, node_le_Om12 5, flip0_le_Om12,
    flip2_le_Om12]

variable {b₀ : G} {K E : Subgroup G} {B : Basis3 G 7}

theorem e_torus (hB : Adapted B b₀ K E) {e : ↥K ≃* ↥Om12} (he : IsFrameModel B e) :
    (∀ h, ((e ⟨B.vec (vP 0), h⟩ : ↥Om12) : V12 ≃ₗ[ZMod 2] V12) ∈ node 0) ∧
    (∀ h, ((e ⟨B.vec (vP 1), h⟩ : ↥Om12) : V12 ≃ₗ[ZMod 2] V12) ∈ node 2) ∧
    (∀ h, ((e ⟨B.vec (vP 2), h⟩ : ↥Om12) : V12 ≃ₗ[ZMod 2] V12) ∈ node 4) ∧
    (∀ h, ((e ⟨B.vec (vM 0), h⟩ : ↥Om12) : V12 ≃ₗ[ZMod 2] V12) ∈ flip0) ∧
    (∀ h, ((e ⟨B.vec (vM 1), h⟩ : ↥Om12) : V12 ≃ₗ[ZMod 2] V12) ∈ flip2) ∧
    (∀ h, ((e ⟨B.vec (vM 2), h⟩ : ↥Om12) : V12 ≃ₗ[ZMod 2] V12) ∈ node 5) := by
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
  · rw [e_vec_pair hB he 0 1 (vec_vP B).1 h]; exact frameRot01_mem.1
  · rw [e_vec_pair hB he 2 3 (vec_vP B).2.1 h]; exact frameRot23_mem.1
  · rw [e_vec_pair hB he 4 5 (vec_vP B).2.2 h]; exact frameRot45_mem.1
  · rw [e_vec_pair_inv hB he 0 1 (vec_vM B).1 h]; exact frameRot01_mem.2
  · rw [e_vec_pair_inv hB he 2 3 (vec_vM B).2.1 h]; exact frameRot23_mem.2
  · rw [e_vec_pair_inv hB he 4 5 (vec_vM B).2.2 h]; exact frameRot45_mem.2

private theorem vP_ne_zero (j : Fin 3) : vP j ≠ 0 := by revert j; decide

private theorem vM_ne_zero (j : Fin 3) : vM j ≠ 0 := by revert j; decide

theorem isRootAt_K (hB : Adapted B b₀ K E) (hKC : K ≤ Subgroup.centralizer ({b₀} : Set G))
    {e : ↥K ≃* ↥Om12} (he : IsFrameModel B e) :
    IsRootAt E B (tr e (node 0)) (vP 0) ∧ IsRootAt E B (tr e (node 2)) (vP 1) ∧
      IsRootAt E B (tr e (node 4)) (vP 2) ∧ IsRootAt E B (tr e flip0) (vM 0) ∧
      IsRootAt E B (tr e flip2) (vM 1) ∧ IsRootAt E B (tr e (node 5)) (vM 2) := by
  obtain ⟨t0, t2, t4, tf0, tf2, t5⟩ := e_torus hB he
  have hP : ∀ j, B.vec (vP j) ∈ K := fun j => E7Frame.vec_mem_K hB (vP_zero j)
  have hM : ∀ j, B.vec (vM j) ∈ K := fun j => E7Frame.vec_mem_K hB (vM_zero j)
  have hX : ∀ {X : Subgroup (V12 ≃ₗ[ZMod 2] V12)},
      (X = node 0 ∨ X = node 2 ∨ X = node 4 ∨ X = node 5 ∨ X = flip0 ∨ X = flip2) →
      ∀ {v : Coords 7} (hv : v ≠ 0) (hvK : B.vec v ∈ K),
      ((e ⟨B.vec v, hvK⟩ : ↥Om12) : V12 ≃ₗ[ZMod 2] V12) ∈ X → IsRootAt E B (tr e X) v :=
    fun {_} hX {_} hv hvK hvX => isRootAt_tr hB hKC he frameRot_pow_three (six_le_Om12 hX)
      (fun i => frameRot_conj_mem i hX) (fun _ hh hh1 hh3 => exists_inv_closure hX hh hh1 hh3)
      hv hvK hvX
  exact ⟨hX (Or.inl rfl) (vP_ne_zero 0) (hP 0) (t0 _),
    hX (Or.inr (Or.inl rfl)) (vP_ne_zero 1) (hP 1) (t2 _),
    hX (Or.inr (Or.inr (Or.inl rfl))) (vP_ne_zero 2) (hP 2) (t4 _),
    hX (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) (vM_ne_zero 0) (hM 0) (tf0 _),
    hX (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))) (vM_ne_zero 1) (hM 1) (tf2 _),
    hX (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) (vM_ne_zero 2) (hM 2) (t5 _)⟩

private theorem comm_node {i j : Fin 6} (h : i ≠ j ∧ ¬ edgeD 6 i j ∧ ¬ edgeD 6 j i) :
    ∀ a ∈ node i, ∀ c ∈ node j, a * c = c * a :=
  node_commute h.1 h.2.1 h.2.2

theorem le_host_L [Finite G] (hstd : StdLoc b₀ K E Row.D6) (hB : Adapted B b₀ K E)
    (hrec : RecOutD6 B b₀) {e : ↥K ≃* ↥Om12} (he : IsFrameModel B e) {w : G}
    (hw : w * b₀ * w⁻¹ = B.vec (vP 0)) :
    tr e (node 2) ≤ K.map (MulAut.conj w).toMonoidHom ∧
      tr e (node 3) ≤ K.map (MulAut.conj w).toMonoidHom ∧
      tr e (node 4) ≤ K.map (MulAut.conj w).toMonoidHom ∧
      tr e (node 5) ≤ K.map (MulAut.conj w).toMonoidHom ∧
      tr e flip2 ≤ K.map (MulAut.conj w).toMonoidHom := by
  have hL := rootHost_map_conj hstd hB hrec hw
  have hxK : B.vec (vP 0) ∈ K := E7Frame.vec_mem_K hB (vP_zero 0)
  have hxZ := (e_torus hB he).1 hxK
  obtain ⟨W₁, h₂₃⟩ := node_pair (i := 2) (j := 3) (by decide)
  obtain ⟨W₂, h₃₄⟩ := node_pair (i := 3) (j := 4) (by decide)
  obtain ⟨W₃, h₃₅⟩ := node_pair (i := 3) (j := 5) (by decide)
  obtain ⟨W₄, hf₃⟩ := flip2_pair_node3
  have p₂₃ := tr_le_host e hxK hL (node_le_Om12 2) (node_le_Om12 3) h₂₃ hxZ
    (comm_node (by decide)) (comm_node (by decide))
  have p₃₄ := tr_le_host e hxK hL (node_le_Om12 3) (node_le_Om12 4) h₃₄ hxZ
    (comm_node (by decide)) (comm_node (by decide))
  have p₃₅ := tr_le_host e hxK hL (node_le_Om12 3) (node_le_Om12 5) h₃₅ hxZ
    (comm_node (by decide)) (comm_node (by decide))
  have pf₃ := tr_le_host e hxK hL flip2_le_Om12 (node_le_Om12 3) hf₃ hxZ
    (flip2_commute_node (j := 0) (by decide) (by decide)) (comm_node (by decide))
  exact ⟨p₂₃.1, p₂₃.2, p₃₄.2, p₃₅.2, pf₃.1⟩

theorem le_host_M [Finite G] (hstd : StdLoc b₀ K E Row.D6) (hB : Adapted B b₀ K E)
    (hrec : RecOutD6 B b₀) {e : ↥K ≃* ↥Om12} (he : IsFrameModel B e) {w : G}
    (hw : w * b₀ * w⁻¹ = B.vec (vM 2)) :
    tr e (node 0) ≤ K.map (MulAut.conj w).toMonoidHom ∧
      tr e (node 1) ≤ K.map (MulAut.conj w).toMonoidHom ∧
      tr e (node 2) ≤ K.map (MulAut.conj w).toMonoidHom ∧
      tr e flip0 ≤ K.map (MulAut.conj w).toMonoidHom ∧
      tr e flip2 ≤ K.map (MulAut.conj w).toMonoidHom := by
  have hM := rootHost_map_conj hstd hB hrec hw
  have hxK : B.vec (vM 2) ∈ K := E7Frame.vec_mem_K hB (vM_zero 2)
  have hxZ := (e_torus hB he).2.2.2.2.2 hxK
  obtain ⟨W₁, h₀₁⟩ := node_pair (i := 0) (j := 1) (by decide)
  obtain ⟨W₂, h₁₂⟩ := node_pair (i := 1) (j := 2) (by decide)
  obtain ⟨W₃, hf₀⟩ := flip0_pair_node1
  obtain ⟨W₄, hf₂⟩ := flip2_pair_node1
  have p₀₁ := tr_le_host e hxK hM (node_le_Om12 0) (node_le_Om12 1) h₀₁ hxZ
    (comm_node (by decide)) (comm_node (by decide))
  have p₁₂ := tr_le_host e hxK hM (node_le_Om12 1) (node_le_Om12 2) h₁₂ hxZ
    (comm_node (by decide)) (comm_node (by decide))
  have pf₀ := tr_le_host e hxK hM flip0_le_Om12 (node_le_Om12 1) hf₀ hxZ
    (flip0_commute_node (j := 5) (by decide)) (comm_node (by decide))
  have pf₂ := tr_le_host e hxK hM (node_le_Om12 1) flip2_le_Om12 hf₂ hxZ
    (comm_node (by decide)) (flip2_commute_node (j := 5) (by decide) (by decide))
  exact ⟨p₀₁.1, p₀₁.2, p₁₂.2, pf₀.1, pf₂.2⟩

theorem tr_le_host_M_of_L [Finite G] (hstd : StdLoc b₀ K E Row.D6)
    (hB : Adapted B b₀ K E) (hrec : RecOutD6 B b₀) {e : ↥K ≃* ↥Om12} (he : IsFrameModel B e)
    {w₁ : G} (hw₁ : ∀ v, w₁⁻¹ * B.vec v * w₁ = B.vec (wbar1 *ᵥ v)) {w : G}
    (hw : w * b₀ * w⁻¹ = B.vec (vM 2)) {W X Y : Subgroup (V12 ≃ₗ[ZMod 2] V12)}
    (hXO : X ≤ Om12) (hYO : Y ≤ Om12) (hp : LinearBlockStandardPair (ZMod 2) W X Y)
    (hX5 : ∀ a ∈ X, ∀ c ∈ node 5, a * c = c * a) (hY5 : ∀ a ∈ Y, ∀ c ∈ node 5, a * c = c * a) :
    tr (conjModel e w₁) X ≤ K.map (MulAut.conj w).toMonoidHom ∧
      tr (conjModel e w₁) Y ≤ K.map (MulAut.conj w).toMonoidHom := by
  have hM := rootHost_map_conj hstd hB hrec hw
  have hK : B.vec (vM 2) ∈ K := E7Frame.vec_mem_K hB (vM_zero 2)
  have hwv : w₁⁻¹ * B.vec (vM 2) * w₁ = B.vec (vM 2) := by rw [hw₁, wbar1_vM]
  have hxL : B.vec (vM 2) ∈ K.map (MulAut.conj w₁).toMonoidHom :=
    mem_map_conj.mpr (by rw [hwv]; exact hK)
  have hxZ : ((conjModel e w₁ ⟨B.vec (vM 2), hxL⟩ : ↥Om12) : V12 ≃ₗ[ZMod 2] V12) ∈ node 5 := by
    rw [conjModel_vec e hwv hxL hK]
    exact (e_torus hB he).2.2.2.2.2 hK
  exact tr_le_host (conjModel e w₁) hxL hM hXO hYO hp hxZ hX5 hY5

theorem le_host_M_of_L [Finite G] (hstd : StdLoc b₀ K E Row.D6) (hB : Adapted B b₀ K E)
    (hrec : RecOutD6 B b₀) {e : ↥K ≃* ↥Om12} (he : IsFrameModel B e) {w₁ : G}
    (hw₁ : ∀ v, w₁⁻¹ * B.vec v * w₁ = B.vec (wbar1 *ᵥ v)) {w : G}
    (hw : w * b₀ * w⁻¹ = B.vec (vM 2)) :
    tr (conjModel e w₁) (node 0) ≤ K.map (MulAut.conj w).toMonoidHom ∧
      tr (conjModel e w₁) (node 1) ≤ K.map (MulAut.conj w).toMonoidHom ∧
      tr (conjModel e w₁) (node 2) ≤ K.map (MulAut.conj w).toMonoidHom ∧
      tr (conjModel e w₁) flip0 ≤ K.map (MulAut.conj w).toMonoidHom := by
  obtain ⟨W₁, h₀₁⟩ := node_pair (i := 0) (j := 1) (by decide)
  obtain ⟨W₂, h₁₂⟩ := node_pair (i := 1) (j := 2) (by decide)
  obtain ⟨W₃, hf₀⟩ := flip0_pair_node1
  have p₀₁ := tr_le_host_M_of_L hstd hB hrec he hw₁ hw (node_le_Om12 0) (node_le_Om12 1) h₀₁
    (comm_node (by decide)) (comm_node (by decide))
  have p₁₂ := tr_le_host_M_of_L hstd hB hrec he hw₁ hw (node_le_Om12 1) (node_le_Om12 2) h₁₂
    (comm_node (by decide)) (comm_node (by decide))
  have pf₀ := tr_le_host_M_of_L hstd hB hrec he hw₁ hw flip0_le_Om12 (node_le_Om12 1) hf₀
    (flip0_commute_node (j := 5) (by decide)) (comm_node (by decide))
  exact ⟨p₀₁.1, p₀₁.2, p₁₂.2, pf₀.1⟩

structure HostData (b₀ : G) (K E : Subgroup G) (B : Basis3 G 7) (e : ↥K ≃* ↥Om12) (w₁ w₂ : G) :
    Prop where
  frame : IsFrameModel B e
  w₁N : w₁ ∈ Subgroup.normalizer (E : Set G)
  w₁v : ∀ v, w₁ * B.vec v * w₁⁻¹ = B.vec (wbar1 *ᵥ v) ∧ w₁⁻¹ * B.vec v * w₁ = B.vec (wbar1 *ᵥ v)
  w₂N : w₂ ∈ Subgroup.normalizer (E : Set G)
  w₂v : ∀ v, w₂ * B.vec v * w₂⁻¹ = B.vec (wbar2 *ᵥ v) ∧ w₂⁻¹ * B.vec v * w₂ = B.vec (wbar2 *ᵥ v)
  L_flip0 : tr (conjModel e w₁) flip0 = tr e flip0
  L_node2 : tr (conjModel e w₁) (node 2) = tr e (node 4)
  L_flip2 : tr (conjModel e w₁) flip2 = tr e flip2
  L_node4 : tr (conjModel e w₁) (node 4) = tr e (node 2)
  L_node5 : tr (conjModel e w₁) (node 5) = tr e (node 5)
  K4_le_L : tr e (node 3) ≤ K.map (MulAut.conj w₁).toMonoidHom
  M_node0 : tr (conjModel e w₂) (node 0) = tr e (node 0)
  M_flip0 : tr (conjModel e w₂) flip0 = tr e (node 2)
  M_node2 : tr (conjModel e w₂) (node 2) = tr e flip0
  M_flip2 : tr (conjModel e w₂) flip2 = tr e flip2
  M_node4 : tr (conjModel e w₂) (node 4) = tr e (node 4)
  M_node5 : tr (conjModel e w₂) (node 5) = tr (conjModel e w₁) (node 0)
  K2_le_M : tr e (node 1) ≤ K.map (MulAut.conj w₂).toMonoidHom

theorem exists_hostData [Finite G] (hstd : StdLoc b₀ K E Row.D6) (hB : Adapted B b₀ K E)
    (hrec : RecOutD6 B b₀) : ∃ e w₁ w₂, HostData b₀ K E B e w₁ w₂ := by
  obtain ⟨e, he⟩ := exists_mulEquiv_frame_D6 hstd hB hrec (l₀ := framePair) isFrame_frameList
  obtain ⟨w₁, hw₁N, hw₁⟩ := exists_weyl1 hstd hB hrec
  obtain ⟨w₂, hw₂N, hw₂⟩ := exists_weyl2 hstd hB hrec
  have he' : IsFrameModel B e := he
  have hKC : K ≤ Subgroup.centralizer ({b₀} : Set G) := hstd.2.1.1.2.1
  have hb₀ : b₀ = B.vec vθ := by rw [vec_vθ, hB.2.1]
  have hw₁b : w₁ * b₀ * w₁⁻¹ = B.vec (vP 0) := by rw [hb₀, (hw₁ _).1, wbar1_vθ]
  have hw₂b : w₂ * b₀ * w₂⁻¹ = B.vec (vM 2) := by rw [hb₀, (hw₂ _).1, wbar2_vθ]
  obtain ⟨R0, R2, R4, Rf0, Rf2, R5⟩ := isRootAt_K hB hKC he'
  obtain ⟨L2, L3, L4, L5, Lf2⟩ := le_host_L hstd hB hrec he' hw₁b
  obtain ⟨M0, M1, M2, Mf0, Mf2⟩ := le_host_M hstd hB hrec he' hw₂b
  obtain ⟨ML0, -, ML2, MLf0⟩ := le_host_M_of_L hstd hB hrec he' (fun v => (hw₁ v).2) hw₂b
  have idL : ∀ {X Y : Subgroup G} {u v : Coords 7}, u 0 = 0 → wt u = 2 → IsRootAt E B X u →
      IsRootAt E B Y v → w₁ * B.vec u * w₁⁻¹ = B.vec v →
      Y ≤ K.map (MulAut.conj w₁).toMonoidHom → X ≤ K → X.map (MulAut.conj w₁).toMonoidHom = Y :=
    fun hu0 hu hX hY hwv hYL hXK =>
      map_conj_eq_of_isRootAt hstd hB hrec hu0 hu hX hXK hY hw₁N hwv hYL
  have idM : ∀ {X Y : Subgroup G} {u v : Coords 7}, u 0 = 0 → wt u = 2 → IsRootAt E B X u →
      IsRootAt E B Y v → w₂ * B.vec u * w₂⁻¹ = B.vec v →
      Y ≤ K.map (MulAut.conj w₂).toMonoidHom → X ≤ K → X.map (MulAut.conj w₂).toMonoidHom = Y :=
    fun hu0 hu hX hY hwv hYL hXK =>
      map_conj_eq_of_isRootAt hstd hB hrec hu0 hu hX hXK hY hw₂N hwv hYL
  have hL2 : tr (conjModel e w₁) (node 2) = tr e (node 4) := by
    rw [tr_conjModel]
    exact idL (vP_zero 1) (wt_vP 1) R2 R4 (by rw [(hw₁ _).1, wbar1_vP1]) L4 (tr_le_K e _)
  have hL4 : tr (conjModel e w₁) (node 4) = tr e (node 2) := by
    rw [tr_conjModel]
    exact idL (vP_zero 2) (wt_vP 2) R4 R2 (by rw [(hw₁ _).1, wbar1_vP2]) L2 (tr_le_K e _)
  have hLf2 : tr (conjModel e w₁) flip2 = tr e flip2 := by
    rw [tr_conjModel]
    exact idL (vM_zero 1) (wt_vM 1) Rf2 Rf2 (by rw [(hw₁ _).1, wbar1_vM]) Lf2 (tr_le_K e _)
  have hL5 : tr (conjModel e w₁) (node 5) = tr e (node 5) := by
    rw [tr_conjModel]
    exact idL (vM_zero 2) (wt_vM 2) R5 R5 (by rw [(hw₁ _).1, wbar1_vM]) L5 (tr_le_K e _)
  have R0L : IsRootAt E B (tr (conjModel e w₁) (node 0)) vθ := by
    rw [tr_conjModel]
    exact R0.map_conj hw₁N (by rw [(hw₁ _).1, wbar1_vP0])
  have Rf0L : IsRootAt E B (tr (conjModel e w₁) flip0) (vM 0) := by
    rw [tr_conjModel]
    exact Rf0.map_conj hw₁N (by rw [(hw₁ _).1, wbar1_vM])
  have hM0 : tr (conjModel e w₂) (node 0) = tr e (node 0) := by
    rw [tr_conjModel]
    exact idM (vP_zero 0) (wt_vP 0) R0 R0 (by rw [(hw₂ _).1, wbar2_vP0]) M0 (tr_le_K e _)
  have hMf0 : tr (conjModel e w₂) flip0 = tr e (node 2) := by
    rw [tr_conjModel]
    exact idM (vM_zero 0) (wt_vM 0) Rf0 R2 (by rw [(hw₂ _).1, wbar2_vM0]) M2 (tr_le_K e _)
  have hM2 : tr (conjModel e w₂) (node 2) = tr e flip0 := by
    rw [tr_conjModel]
    exact idM (vP_zero 1) (wt_vP 1) R2 Rf0 (by rw [(hw₂ _).1, wbar2_vP1]) Mf0 (tr_le_K e _)
  have hMf2 : tr (conjModel e w₂) flip2 = tr e flip2 := by
    rw [tr_conjModel]
    exact idM (vM_zero 1) (wt_vM 1) Rf2 Rf2 (by rw [(hw₂ _).1, wbar2_vM1]) Mf2 (tr_le_K e _)
  have hM4 : tr (conjModel e w₂) (node 4) = tr e (node 4) := by
    rw [tr_conjModel]
    exact idM (vP_zero 2) (wt_vP 2) R4 R4 (by rw [(hw₂ _).1, wbar2_vP2])
      (by rw [← hL2]; exact ML2) (tr_le_K e _)
  have hM5 : tr (conjModel e w₂) (node 5) = tr (conjModel e w₁) (node 0) := by
    rw [tr_conjModel]
    exact idM (vM_zero 2) (wt_vM 2) R5 R0L (by rw [(hw₂ _).1, wbar2_vM2]) ML0 (tr_le_K e _)
  have hLf0 : tr (conjModel e w₁) flip0 = tr e flip0 := by
    have h1 : (tr e (node 2)).map (MulAut.conj w₂).toMonoidHom = tr (conjModel e w₁) flip0 :=
      idM (vP_zero 1) (wt_vP 1) R2 Rf0L (by rw [(hw₂ _).1, wbar2_vP1]) MLf0 (tr_le_K e _)
    rw [← h1, ← tr_conjModel, hM2]
  exact ⟨e, w₁, w₂, he', hw₁N, hw₁, hw₂N, hw₂, hLf0, hL2, hLf2, hL4, hL5, L3, hM0, hMf0, hM2, hMf2,
    hM4, hM5, M1⟩

end CFSG.StandardType.FrameRoute.FS81.D6M
