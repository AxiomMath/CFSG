module

public import CFSG.LocalAnalysis.StandardType.FS81.StdLoc
public import CFSG.LocalAnalysis.StandardType.FS81.D6FrameModel
public import CFSG.LocalAnalysis.StandardType.FS81.D6HostIds

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.StandardType.FrameRoute.FS81.D6M

open CFSG.ClassicalInvolution.WeakCT CFSG.Timmesfeld
open scoped Matrix

variable {G : Type} [Group G]

noncomputable abbrev wc0Om : ↥Om12 := ⟨wc0, flip2_le_Om12 wc0_mem⟩
noncomputable abbrev wm2Om : ↥Om12 := ⟨wm2, node_le_Om12 2 wm2_mem⟩
noncomputable abbrev wmu0Om : ↥Om12 := ⟨wmu0, node_le_Om12 0 wmu0_mem⟩
noncomputable abbrev wphi0Om : ↥Om12 := ⟨wphi0, flip0_le_Om12 wphi0_mem⟩
noncomputable abbrev wmu4Om : ↥Om12 := ⟨wmu4, node_le_Om12 4 wmu4_mem⟩
noncomputable abbrev wmu5Om : ↥Om12 := ⟨wmu5, node_le_Om12 5 wmu5_mem⟩

noncomputable abbrev c0G {K : Subgroup G} (e : ↥K ≃* ↥Om12) : G := trElt e wc0Om

structure K6Data (K : Subgroup G) (e : ↥K ≃* ↥Om12) (w₁ w₂ : G) (K₆ : Subgroup G) : Prop where
  le_L : K₆ ≤ K.map (MulAut.conj w₁).toMonoidHom
  le_M : K₆ ≤ K.map (MulAut.conj w₂).toMonoidHom
  pair_K5 : ∃ W, LinearBlockStandardPair (ZMod 2) W K₆ (tr e (node 4))
  pair_K1' : ∃ W, LinearBlockStandardPair (ZMod 2) W (tr e flip0) K₆
  comm_K4 : ∀ a ∈ K₆, ∀ c ∈ tr e (node 3), a * c = c * a
  comm_K3 : ∀ a ∈ K₆, ∀ c ∈ tr e (node 2), a * c = c * a
  comm_K5' : ∀ a ∈ K₆, ∀ c ∈ tr e (node 5), a * c = c * a
  norm : ∃ k₀ ∈ tr (conjModel e w₁) (node 0), ∃ k₁ ∈ tr e flip0, ∃ k₅ ∈ tr e (node 4),
    ∀ z ∈ K₆, (k₀ * k₁ * k₅ * c0G e) * z * (k₀ * k₁ * k₅ * c0G e)⁻¹ ∈ K₆

theorem mem_of_tr_eq {K L : Subgroup G} {e : ↥K ≃* ↥Om12} {e₁ : ↥L ≃* ↥Om12}
    {X X' : Subgroup (V12 ≃ₗ[ZMod 2] V12)} (h : tr e₁ X' = tr e X) {g : G} (hg : g ∈ tr e X) :
    ∃ hL : g ∈ L, ((e₁ ⟨g, hL⟩ : ↥Om12) : V12 ≃ₗ[ZMod 2] V12) ∈ X' := by
  rw [← h] at hg
  exact ⟨tr_le_K e₁ X' hg, (mem_tr_iff e₁ X' ⟨g, _⟩).mp hg⟩

theorem model_trElt_ne_one {K L : Subgroup G} (e : ↥K ≃* ↥Om12) (e₁ : ↥L ≃* ↥Om12)
    {x : ↥Om12} (hx : (x : V12 ≃ₗ[ZMod 2] V12) ≠ 1) (hL : trElt e x ∈ L) :
    ((e₁ ⟨trElt e x, hL⟩ : ↥Om12) : V12 ≃ₗ[ZMod 2] V12) ≠ 1 := by
  intro h
  have h1 : e₁ ⟨trElt e x, hL⟩ = 1 := Subtype.ext h
  rw [MulEquiv.map_eq_one_iff] at h1
  have h2' : trElt e x = 1 := congrArg Subtype.val h1
  have h2 : e.symm x = 1 := Subtype.ext h2'
  rw [MulEquiv.map_eq_one_iff] at h2
  exact hx (congrArg Subtype.val h2)

theorem model_mul_four {L : Subgroup G} (e₁ : ↥L ≃* ↥Om12) {a b c d : G} (ha : a ∈ L)
    (hb : b ∈ L) (hc : c ∈ L) (hd : d ∈ L) (h : a * b * c * d ∈ L) :
    ((e₁ ⟨a * b * c * d, h⟩ : ↥Om12) : V12 ≃ₗ[ZMod 2] V12) =
      (e₁ ⟨a, ha⟩ : V12 ≃ₗ[ZMod 2] V12) * (e₁ ⟨b, hb⟩ : V12 ≃ₗ[ZMod 2] V12) *
        (e₁ ⟨c, hc⟩ : V12 ≃ₗ[ZMod 2] V12) * (e₁ ⟨d, hd⟩ : V12 ≃ₗ[ZMod 2] V12) := by
  have : (⟨a * b * c * d, h⟩ : ↥L) = ⟨a, ha⟩ * ⟨b, hb⟩ * ⟨c, hc⟩ * ⟨d, hd⟩ := rfl
  rw [this, map_mul, map_mul, map_mul]
  rfl

theorem exists_K6Data [Finite G] {b₀ : G} {K E : Subgroup G} {B : Basis3 G 7}
    {e : ↥K ≃* ↥Om12} {w₁ w₂ : G} (hstd : StdLoc b₀ K E Row.D6)
    (hB : Adapted B b₀ K E) (hrec : RecOutD6 B b₀) (hH : HostData b₀ K E B e w₁ w₂) :
    ∃ K₆, K6Data K e w₁ w₂ K₆ := by
  classical
  have hK4L := hH.K4_le_L
  have hK5L : tr e (node 4) ≤ K.map (MulAut.conj w₁).toMonoidHom := by
    rw [← hH.L_node2]
    exact tr_le_K _ _
  have hK3L : tr e (node 2) ≤ K.map (MulAut.conj w₁).toMonoidHom := by
    rw [← hH.L_node4]
    exact tr_le_K _ _
  have hp2 : ∃ W, LinearBlockStandardPair (ZMod 2) W
      (pull (conjModel e w₁) (tr e (node 3))) (node 2) := by
    obtain ⟨W, hW⟩ := node_pair (show edgeD 6 3 4 by decide)
    obtain ⟨W', hW'⟩ := tr_pair e (node_le_Om12 3) (node_le_Om12 4) hW
    obtain ⟨W'', h⟩ := pull_pair (conjModel e w₁) hK4L hK5L hW'
    rw [← hH.L_node2, pull_tr _ (node_le_Om12 2)] at h
    exact ⟨_, h⟩
  have hp4 : ∃ W, LinearBlockStandardPair (ZMod 2) W
      (pull (conjModel e w₁) (tr e (node 3))) (node 4) := by
    obtain ⟨W, hW⟩ := node_pair (show edgeD 6 2 3 by decide)
    obtain ⟨W', hW'⟩ := tr_pair e (node_le_Om12 2) (node_le_Om12 3) hW
    obtain ⟨W'', h⟩ := pull_pair (conjModel e w₁) hK3L hK4L hW'
    rw [← hH.L_node4, pull_tr _ (node_le_Om12 4)] at h
    exact ⟨_, pair_symm h⟩
  obtain ⟨h4L, hn⟩ := mem_of_tr_eq hH.L_node2 (trElt_mem_tr e (x := wmu4Om) wmu4_mem)
  obtain ⟨h5L, hn₅⟩ := mem_of_tr_eq hH.L_node5 (trElt_mem_tr e (x := wmu5Om) wmu5_mem)
  obtain ⟨h2L, hn₄⟩ := mem_of_tr_eq hH.L_node4 (trElt_mem_tr e (x := wm2Om) wm2_mem)
  obtain ⟨h0L, hγ⟩ := mem_of_tr_eq hH.L_flip2 (trElt_mem_tr e (x := wc0Om) wc0_mem)
  have hprodL : trElt e wmu4Om * trElt e wmu5Om * trElt e wm2Om * trElt e wc0Om ∈
      K.map (MulAut.conj w₁).toMonoidHom :=
    mul_mem (mul_mem (mul_mem h4L h5L) h2L) h0L
  have hg₃ : ∀ g ∈ tr e (node 3),
      (trElt e wmu4Om * trElt e wmu5Om * trElt e wm2Om * trElt e wc0Om) * g *
        (trElt e wmu4Om * trElt e wmu5Om * trElt e wm2Om * trElt e wc0Om)⁻¹ ∈ tr e (node 3) := by
    have h := trElt_conj_mem e (x := wmu4Om * wmu5Om * wm2Om * wc0Om) witness_node3
    simpa only [trElt_mul] using h
  have hnorm4 := pull_conj_mem (conjModel e w₁) hprodL hg₃
  rw [model_mul_four (conjModel e w₁) h4L h5L h2L h0L hprodL] at hnorm4
  obtain ⟨Z₆, hZ6O, hR1, hR2, hc4, hc5, hcZ4, m, hm, hnorm⟩ :=
    exists_Z6 (pull_le_Om12 _ _) hp2 hp4 hn hn₅ hn₄ hγ
      (model_trElt_ne_one e (conjModel e w₁) wc0_ne_one h0L) hnorm4
  have hw₂ : w₂ * b₀ * w₂⁻¹ = B.vec (vM 2) := by
    have hb₀ : b₀ = B.vec vθ := by rw [vec_vθ, hB.2.1]
    rw [hb₀, (hH.w₂v vθ).1, wbar2_vθ]
  obtain ⟨W₁, hW₁⟩ := hR1
  refine ⟨tr (conjModel e w₁) Z₆, ⟨tr_le_K _ _, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · exact (tr_le_host_M_of_L hstd hB hrec hH.frame (fun v => (hH.w₁v v).2) hw₂ hZ6O
      (node_le_Om12 2) hW₁ hc5
      (fun a ha c hc => node_commute (by decide) (by decide) (by decide) a ha c hc)).1
  · obtain ⟨W', h⟩ := tr_pair (conjModel e w₁) hZ6O (node_le_Om12 2) hW₁
    rw [hH.L_node2] at h
    exact ⟨_, h⟩
  · obtain ⟨W, hW⟩ := hR2
    obtain ⟨W', h⟩ := tr_pair (conjModel e w₁) flip0_le_Om12 hZ6O hW
    rw [hH.L_flip0] at h
    exact ⟨_, h⟩
  · have h := tr_commute (conjModel e w₁) hcZ4
    rwa [tr_pull _ hK4L] at h
  · have h := tr_commute (conjModel e w₁) hc4
    rwa [hH.L_node4] at h
  · have h := tr_commute (conjModel e w₁) hc5
    rwa [hH.L_node5] at h
  · have hmO : m ∈ Om12 := node_le_Om12 2 hm
    have hcoe : ((wmu0Om * wphi0Om * (⟨m, hmO⟩ : ↥Om12) *
        conjModel e w₁ ⟨trElt e wc0Om, h0L⟩ : ↥Om12) : V12 ≃ₗ[ZMod 2] V12) =
        wmu0 * wphi0 * m * (conjModel e w₁ ⟨trElt e wc0Om, h0L⟩ : V12 ≃ₗ[ZMod 2] V12) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_mk]
    have hx := trElt_conj_mem (conjModel e w₁)
      (x := wmu0Om * wphi0Om * (⟨m, hmO⟩ : ↥Om12) * conjModel e w₁ ⟨trElt e wc0Om, h0L⟩)
      (by rw [hcoe]; exact hnorm)
    have hγt : trElt (conjModel e w₁) (conjModel e w₁ ⟨trElt e wc0Om, h0L⟩) = c0G e := by
      simp only [trElt, MulEquiv.symm_apply_apply]
    rw [trElt_mul, trElt_mul, trElt_mul, hγt] at hx
    refine ⟨_, trElt_mem_tr _ (x := wmu0Om) wmu0_mem, _, ?_, _, ?_, hx⟩
    · rw [← hH.L_flip0]
      exact trElt_mem_tr _ (x := wphi0Om) wphi0_mem
    · rw [← hH.L_node2]
      exact trElt_mem_tr _ (x := (⟨m, hmO⟩ : ↥Om12)) hm

theorem exists_K6'_commute {b₀ : G} {K E : Subgroup G} {B : Basis3 G 7}
    {e : ↥K ≃* ↥Om12} {w₁ w₂ : G} (hH : HostData b₀ K E B e w₁ w₂) {K₆ : Subgroup G}
    (hK6 : K6Data K e w₁ w₂ K₆) :
    ∃ k ∈ tr e flip0,
      (∀ a ∈ K₆.map (MulAut.conj k).toMonoidHom, ∀ b ∈ tr e (node 1), a * b = b * a) ∧
      ∀ a ∈ K₆.map (MulAut.conj k).toMonoidHom, ∀ b ∈ tr e (node 0), a * b = b * a := by
  classical
  have hK2M := hH.K2_le_M
  have hK1'M : tr e flip0 ≤ K.map (MulAut.conj w₂).toMonoidHom := by
    rw [← hH.M_node2]
    exact tr_le_K _ _
  have hK1M : tr e (node 0) ≤ K.map (MulAut.conj w₂).toMonoidHom := by
    rw [← hH.M_node0]
    exact tr_le_K _ _
  have hK5M : tr e (node 4) ≤ K.map (MulAut.conj w₂).toMonoidHom := by
    rw [← hH.M_node4]
    exact tr_le_K _ _
  have hp2 : ∃ W, LinearBlockStandardPair (ZMod 2) W
      (pull (conjModel e w₂) (tr e (node 1))) (node 2) := by
    obtain ⟨W, hW⟩ := flip0_pair_node1
    obtain ⟨W', hW'⟩ := tr_pair e flip0_le_Om12 (node_le_Om12 1) hW
    obtain ⟨W'', h⟩ := pull_pair (conjModel e w₂) hK1'M hK2M hW'
    rw [← hH.M_node2, pull_tr _ (node_le_Om12 2)] at h
    exact ⟨_, pair_symm h⟩
  have hp0 : ∃ W, LinearBlockStandardPair (ZMod 2) W
      (pull (conjModel e w₂) (tr e (node 1))) (node 0) := by
    obtain ⟨W, hW⟩ := node_pair (show edgeD 6 0 1 by decide)
    obtain ⟨W', hW'⟩ := tr_pair e (node_le_Om12 0) (node_le_Om12 1) hW
    obtain ⟨W'', h⟩ := pull_pair (conjModel e w₂) hK1M hK2M hW'
    rw [← hH.M_node0, pull_tr _ (node_le_Om12 0)] at h
    exact ⟨_, pair_symm h⟩
  have hq2 : ∃ W, LinearBlockStandardPair (ZMod 2) W (pull (conjModel e w₂) K₆) (node 2) := by
    obtain ⟨W, hW⟩ := hK6.pair_K1'
    obtain ⟨W', h⟩ := pull_pair (conjModel e w₂) hK1'M hK6.le_M hW
    rw [← hH.M_node2, pull_tr _ (node_le_Om12 2)] at h
    exact ⟨_, pair_symm h⟩
  have hq4 : ∃ W, LinearBlockStandardPair (ZMod 2) W (pull (conjModel e w₂) K₆) (node 4) := by
    obtain ⟨W, hW⟩ := hK6.pair_K5
    obtain ⟨W', h⟩ := pull_pair (conjModel e w₂) hK6.le_M hK5M hW
    rw [← hH.M_node4, pull_tr _ (node_le_Om12 4)] at h
    exact ⟨_, h⟩
  obtain ⟨hc0M, hγ⟩ := mem_of_tr_eq hH.M_flip2 (trElt_mem_tr e (x := wc0Om) wc0_mem)
  have hγ1 := model_trElt_ne_one e (conjModel e w₂) wc0_ne_one hc0M
  obtain ⟨h0M, ha₁⟩ := mem_of_tr_eq hH.M_node0 (trElt_mem_tr e (x := wmu0Om) wmu0_mem)
  obtain ⟨hf0M, hn₁⟩ := mem_of_tr_eq hH.M_node2 (trElt_mem_tr e (x := wphi0Om) wphi0_mem)
  obtain ⟨h2M, hb₁⟩ := mem_of_tr_eq hH.M_flip0 (trElt_mem_tr e (x := wm2Om) wm2_mem)
  have hprod₁ : trElt e wmu0Om * trElt e wphi0Om * trElt e wm2Om * trElt e wc0Om ∈
      K.map (MulAut.conj w₂).toMonoidHom :=
    mul_mem (mul_mem (mul_mem h0M hf0M) h2M) hc0M
  have hg₁ : ∀ g ∈ tr e (node 1),
      (trElt e wmu0Om * trElt e wphi0Om * trElt e wm2Om * trElt e wc0Om) * g *
        (trElt e wmu0Om * trElt e wphi0Om * trElt e wm2Om * trElt e wc0Om)⁻¹ ∈ tr e (node 1) := by
    have h := trElt_conj_mem e (x := wmu0Om * wphi0Om * wm2Om * wc0Om) witness_node1
    simpa only [trElt_mul] using h
  have hnorm₁ := pull_conj_mem (conjModel e w₂) hprod₁ hg₁
  rw [model_mul_four (conjModel e w₂) h0M hf0M h2M hc0M hprod₁] at hnorm₁
  obtain ⟨k₀, hk₀, k₁, hk₁, k₅, hk₅, hnorm₆⟩ := hK6.norm
  obtain ⟨hk₀M, ha₆⟩ := mem_of_tr_eq hH.M_node5 hk₀
  obtain ⟨hk₁M, hn₆⟩ := mem_of_tr_eq hH.M_node2 hk₁
  obtain ⟨hk₅M, hb₆⟩ := mem_of_tr_eq hH.M_node4 hk₅
  have hprod₆ : k₀ * k₁ * k₅ * c0G e ∈ K.map (MulAut.conj w₂).toMonoidHom :=
    mul_mem (mul_mem (mul_mem hk₀M hk₁M) hk₅M) hc0M
  have hnorm₆' := pull_conj_mem (conjModel e w₂) hprod₆ hnorm₆
  rw [model_mul_four (conjModel e w₂) hk₀M hk₁M hk₅M hc0M hprod₆] at hnorm₆'
  obtain ⟨k, hk, hc2, hc0⟩ := exists_conj_commute (pull_le_Om12 _ _) (pull_le_Om12 _ _)
    hp2 hp0 hq2 hq4 hγ hγ1 ha₁ hn₁ hb₁ hnorm₁ ha₆ hn₆ hb₆ hnorm₆'
  have hkO : k ∈ Om12 := node_le_Om12 2 hk
  have hK6' : tr (conjModel e w₂) ((pull (conjModel e w₂) K₆).map (MulAut.conj k).toMonoidHom) =
      K₆.map (MulAut.conj (trElt (conjModel e w₂) ⟨k, hkO⟩)).toMonoidHom := by
    have h1 := tr_map_conj (conjModel e w₂) ⟨k, hkO⟩ (pull_le_Om12 (conjModel e w₂) K₆)
    rwa [tr_pull _ hK6.le_M] at h1
  refine ⟨trElt (conjModel e w₂) ⟨k, hkO⟩, ?_, ?_, ?_⟩
  · rw [← hH.M_node2]
    exact trElt_mem_tr _ (x := ⟨k, hkO⟩) hk
  · have h := tr_commute (conjModel e w₂) hc2
    rwa [hK6', tr_pull _ hK2M] at h
  · have h := tr_commute (conjModel e w₂) hc0
    rwa [hK6', hH.M_node0] at h

end CFSG.StandardType.FrameRoute.FS81.D6M
