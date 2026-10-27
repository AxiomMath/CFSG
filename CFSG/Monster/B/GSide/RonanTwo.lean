module

public import CFSG.Monster.B.TwoA.Amalgam.TypeFourDist
public import CFSG.Monster.B.GSide.MuFour
public import CFSG.Monster.B.GSide.RonanTwoOmega

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.GSide

open SimpleGraph CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Amalgam CFSG.Monster.B.TwoA.Unitary

theorem mem_sphereFour_comm
    {v w : CVert} : w ∈ sphereFour v ↔ v ∈ sphereFour w := by
  have h : ∀ a b : CVert, LabelFour a b → LabelFour b a := fun a b h => by
    have e : orderOf (clabel b * clabel a) = orderOf (clabel a * clabel b) := by
      have e1 : clabel b * clabel a = MulAut.conj (clabel a)⁻¹ (clabel a * clabel b) := by
        rw [MulAut.conj_apply, inv_inv]
        group
      rw [e1, MulEquiv.orderOf_eq]
    show orderOf (clabel b * clabel a) = 4 ∨ orderOf (clabel b * clabel a) = 8
    rw [e]
    exact h
  exact ⟨fun hw => ⟨SimpleGraph.dist_comm.trans hw.1, h v w hw.2⟩,
    fun hv => ⟨SimpleGraph.dist_comm.trans hv.1, h w v hv.2⟩⟩

theorem ne_of_labelThree
    {z u : CVert} (h : LabelThree z u) : z ≠ u := by
  rintro rfl
  have h1 : clabel z * clabel z = 1 := by
    rw [← sq, ← orderOf_clabel z, pow_orderOf_eq_one]
  rcases h with h | h <;> rw [lblOrd, h1, orderOf_one] at h <;> omega

theorem exists_adj_of_mem_cPi
    {v x y : CVert} {s : Shat} (hvs : v ∈ cPi s) (hxs : x ∈ cPi s)
    (hys : y ∈ cPi s) (hvx : v ≠ x) (hnvx : ¬ cgraph.Adj v x) (hxy : cgraph.Adj x y)
    (hvy : v ≠ y) (hnvy : ¬ cgraph.Adj v y) :
    ∃ c, cgraph.Adj v c ∧ cgraph.Adj c x ∧ cgraph.Adj c y := by
  have adjT : ∀ a b : CVert, cgraph.Adj (cvMul a s⁻¹) (cvMul b s⁻¹) ↔ cgraph.Adj a b :=
    fun a b => cgraph_adj_cvMul a b s⁻¹
  let V : cPi0 := ⟨_, mem_cPi_iff.1 hvs⟩
  let X : cPi0 := ⟨_, mem_cPi_iff.1 hxs⟩
  let Y : cPi0 := ⟨_, mem_cPi_iff.1 hys⟩
  have hVX : V ≠ X := fun e => hvx (cvMul_injective _ (congrArg Subtype.val e))
  have hVY : V ≠ Y := fun e => hvy (cvMul_injective _ (congrArg Subtype.val e))
  have hXY : cgraphPi.Adj X Y := (adjT x y).2 hxy
  have h1 := (cgraphPi_adj_iff hVX).not.1 fun h => hnvx ((adjT v x).1 h)
  have h2 := (cgraphPi_adj_iff hVY).not.1 fun h => hnvy ((adjT v y).1 h)
  have h3 := (cgraphPi_adj_iff hXY.ne).1 hXY
  obtain ⟨cb, hcb, hcby⟩ := exists_adj_mu_omega (x := cpsi X) (v := cpsi V) (y := cpsi Y)
    (fun e => h1 (Or.inl e.symm)) (fun h => h1 (Or.inr h.symm)) (h3.imp Eq.symm id)
    (fun h => h2 (Or.inr h))
  rw [SimpleGraph.mem_commonNeighbors] at hcb
  obtain ⟨k, hk⟩ := piPt_surjective cb
  let C : cPi0 := piV k
  have hC : cpsi C = cb := (cpsi_piV k).trans hk
  have hne : ∀ A : cPi0, omegaGraph.Adj (cpsi A) cb → A ≠ C := fun A h e => by
    rw [e, hC] at h
    exact h.ne rfl
  have hXC : cgraphPi.Adj X C := (cgraphPi_adj_iff (hne X hcb.1)).2 (Or.inr (hC ▸ hcb.1))
  have hVC : cgraphPi.Adj V C := (cgraphPi_adj_iff (hne V hcb.2)).2 (Or.inr (hC ▸ hcb.2))
  have hYC : cgraphPi.Adj Y C := (cgraphPi_adj_iff (hne Y hcby.symm)).2
    (Or.inr (hC ▸ hcby.symm))
  have hVC' : cgraph.Adj (cvMul v s⁻¹) C.1 := hVC
  have hXC' : cgraph.Adj (cvMul x s⁻¹) C.1 := hXC
  have hYC' : cgraph.Adj (cvMul y s⁻¹) C.1 := hYC
  refine ⟨cvMul C.1 s, ?_, ?_, ?_⟩
  · have h := (cgraph_adj_cvMul _ _ s).2 hVC'
    rwa [cvMul_inv_cancel'] at h
  · have h := (cgraph_adj_cvMul _ _ s).2 hXC'
    rw [cvMul_inv_cancel'] at h
    exact h.symm
  · have h := (cgraph_adj_cvMul _ _ s).2 hYC'
    rw [cvMul_inv_cancel'] at h
    exact h.symm

theorem cgraph_ronan_two
    (HT3 : ∀ a b : CVert, b ∈ sphereThree a →
      ∀ u ∈ cgraph.neighborSet b \ cgraph.commonNeighbors a b,
        (cgraph.neighborSet u ∩ cgraph.commonNeighbors a b).Nonempty)
    (H8064 : ∀ a b : CVert, b ∈ sphereFour a → ∀ u ∈ cgraph.neighborSet a,
      (cvOrbit (vStab a ⊓ vStab b) u).ncard = 8064 → cgraph.dist b u = 3)
    (HRem : ∀ a b : CVert, b ∈ sphereFour a → ∀ u ∈ cgraph.neighborSet a,
      (cvOrbit (vStab a ⊓ vStab b) u).ncard = 663552 → u ∈ sphereThree b)
    (HT4a : ∀ a b : CVert, b ∈ sphereFour a → ∀ u ∈ cgraph.neighborSet a,
      (cvOrbit (vStab a ⊓ vStab b) u).ncard = 36288 →
        (cgraph.neighborSet u ∩ cgraph.commonNeighbors a b).ncard = 24)
    (HT4b : ∀ a b : CVert, b ∈ sphereFour a → ∀ u ∈ cgraph.neighborSet a,
      ((cvOrbit (vStab a ⊓ vStab b) u).ncard = 1161216 ∨
        (cvOrbit (vStab a ⊓ vStab b) u).ncard = 2097152) →
        ∃ z ∈ cgraph.commonNeighbors a b, LabelThree z u) :
    ∀ v x y : CVert, cgraph.dist v x = 2 → cgraph.dist v y = 2 → cgraph.Adj x y →
      ∃ c c', cgraph.Adj v c ∧ cgraph.Adj c x ∧ cgraph.Adj v c' ∧ cgraph.Adj c' y ∧
        (c = c' ∨ cgraph.Adj c c') := by
  have caseA : ∀ v x y : CVert, x ∈ sphereThree v → cgraph.dist v y = 2 → cgraph.Adj x y →
      ∃ c, cgraph.Adj v c ∧ cgraph.Adj c x ∧ cgraph.Adj c y := by
    intro v x y hx hy hxy
    obtain ⟨-, hna, -⟩ := cgraph_dist_eq_two_iff.1 hy
    obtain ⟨c, hcy, hc⟩ := HT3 v x hx y ⟨hxy, fun h => hna ((mem_commonNeighbors _).1 h).1⟩
    rw [SimpleGraph.mem_commonNeighbors] at hc
    exact ⟨c, hc.1, hc.2.symm, hcy.symm⟩
  have hsph : ∀ v w : CVert, cgraph.dist v w = 2 → w ∈ sphereThree v ∨ w ∈ sphereFour v :=
    fun v w h => by
      have hw : w ∈ {w | cgraph.dist v w = 2} := h
      rw [(native_coset_graph_two_distance_two_orbits.2.2.1 v).1] at hw
      exact hw
  intro v x y hx hy hxy
  have strong : (∃ c, cgraph.Adj v c ∧ cgraph.Adj c x ∧ cgraph.Adj c y) →
      ∃ c c', cgraph.Adj v c ∧ cgraph.Adj c x ∧ cgraph.Adj v c' ∧ cgraph.Adj c' y ∧
        (c = c' ∨ cgraph.Adj c c') :=
    fun ⟨c, h1, h2, h3⟩ => ⟨c, c, h1, h2, h1, h3, Or.inl rfl⟩
  have caseA' : y ∈ sphereThree v → ∃ c, cgraph.Adj v c ∧ cgraph.Adj c x ∧ cgraph.Adj c y :=
    fun hy3 => by
      obtain ⟨c, h1, h2, h3⟩ := caseA v y x hy3 hx hxy.symm
      exact ⟨c, h1, h3, h2⟩
  rcases hsph v x hx with hx3 | hx4
  · exact strong (caseA v x y hx3 hy hxy)
  obtain ⟨hvx, hnvx, -⟩ := cgraph_dist_eq_two_iff.1 hx
  obtain ⟨hvy, hnvy, -⟩ := cgraph_dist_eq_two_iff.1 hy
  have hvx4 : v ∈ sphereFour x := mem_sphereFour_comm.1 hx4
  obtain ⟨x', Ω, R, φ, α, ⟨s, hxs, hvs⟩, -, -, -, -, hΩpart, hΩorb, hΩcard, -, hΩ0, -, hΩpi,
    -⟩ := native_type_four_pair_eight_neighborhood_orbits x v hvx4
  obtain ⟨i, hi, -⟩ := hΩpart y hxy
  have horb : (cvOrbit (vStab x ⊓ vStab v) y).ncard =
      ![648, 8064, 663552, 1, 1134, 36288, 1161216, 2097152] i := by
    rw [hΩorb i y hi, hΩcard i]
  have hpi : y ∈ cgraph.neighborSet x ∩ cPi s → ∃ c c', cgraph.Adj v c ∧ cgraph.Adj c x ∧
      cgraph.Adj v c' ∧ cgraph.Adj c' y ∧ (c = c' ∨ cgraph.Adj c c') :=
    fun h => strong (exists_adj_of_mem_cPi hvs hxs h.2 hvx hnvx hxy hvy hnvy)
  have hT4b : ((cvOrbit (vStab x ⊓ vStab v) y).ncard = 1161216 ∨
      (cvOrbit (vStab x ⊓ vStab v) y).ncard = 2097152) →
      ∃ c c', cgraph.Adj v c ∧ cgraph.Adj c x ∧ cgraph.Adj v c' ∧ cgraph.Adj c' y ∧
        (c = c' ∨ cgraph.Adj c c') := fun h => by
    obtain ⟨z, hz, hzy⟩ := HT4b x v hvx4 y hxy h
    rw [SimpleGraph.mem_commonNeighbors] at hz
    have hyz := Amalgam.mem_sphereThree_of_labelThree hz.1 hxy (ne_of_labelThree hzy) hzy
    obtain ⟨c', hc'v, hc'⟩ := HT3 y z (mem_sphereThree_comm.1 hyz) v
      ⟨hz.2.symm, fun h' => hnvy ((mem_commonNeighbors _).1 h').1.symm⟩
    rw [SimpleGraph.mem_commonNeighbors] at hc'
    exact ⟨z, c', hz.2, hz.1.symm, hc'v, hc'.1.symm, Or.inr hc'.2⟩
  fin_cases i
  ·
    change y ∈ Ω 0 at hi
    rw [hΩ0] at hi
    exact absurd ((mem_commonNeighbors _).1 hi).2 hnvy
  ·
    change (cvOrbit (vStab x ⊓ vStab v) y).ncard = 8064 at horb
    have h := H8064 x v hvx4 y hxy horb
    omega
  ·
    change (cvOrbit (vStab x ⊓ vStab v) y).ncard = 663552 at horb
    exact strong (caseA' (HRem x v hvx4 y hxy horb))
  · change y ∈ Ω 3 at hi
    exact hpi (by rw [hΩpi s hxs hvs]; exact Or.inl (Or.inr hi))
  · change y ∈ Ω 4 at hi
    exact hpi (by rw [hΩpi s hxs hvs]; exact Or.inr hi)
  ·
    change (cvOrbit (vStab x ⊓ vStab v) y).ncard = 36288 at horb
    have h := HT4a x v hvx4 y hxy horb
    obtain ⟨c, hcy, hc⟩ := Set.nonempty_of_ncard_ne_zero (by rw [h]; norm_num)
    rw [SimpleGraph.mem_commonNeighbors] at hc
    exact strong ⟨c, hc.2, hc.1.symm, hcy.symm⟩
  · change (cvOrbit (vStab x ⊓ vStab v) y).ncard = 1161216 at horb
    exact hT4b (Or.inl horb)
  · change (cvOrbit (vStab x ⊓ vStab v) y).ncard = 2097152 at horb
    exact hT4b (Or.inr horb)

theorem cgraph_triangulable_of_local_weak
    (B0 : ∀ x y : CVert, cgraph.dist x y ≤ 3)
    (B2tri' : ∀ v x y : CVert, cgraph.dist v x = 2 → cgraph.dist v y = 2 → cgraph.Adj x y →
      ∃ c c', cgraph.Adj v c ∧ cgraph.Adj c x ∧ cgraph.Adj v c' ∧ cgraph.Adj c' y ∧
        (c = c' ∨ cgraph.Adj c c'))
    (B3loc : ∀ v u c : CVert, cgraph.dist v u = 3 → cgraph.Adj u c → cgraph.dist v c = 2 →
      c ∈ sphereFour v)
    (B3con : ∀ v u : CVert, cgraph.dist v u = 3 →
      (cgraph.induce (cgraph.neighborSet u ∩ sphereFour v)).Connected)
    (B3tri : ∀ v x y : CVert, cgraph.dist v x = 3 → cgraph.dist v y = 3 → cgraph.Adj x y →
      ∃ h, cgraph.dist v h = 2 ∧ cgraph.Adj h x ∧ cgraph.Adj h y) :
    CFSG.Monster.B.Recog.Triangulable cgraph := by
  refine triangulable_of_dist_le_three_weak B0 (fun v w hvw => ?_) B2tri' (fun v u hvu => ?_)
    B3tri
  · have hw : w ∈ sphereThree v ∪ sphereFour v := by
      rw [← (native_coset_graph_two_distance_two_orbits.2.2.1 v).1]
      exact hvw
    rcases hw with hw | hw
    · exact ((native_order_three_common_neighbors_exact_3510.1 v w hw).1).preconnected
    · exact (cgraph_mu_connected_of_mem_sphereFour v w hw).preconnected
  · have e : {c | cgraph.Adj u c ∧ cgraph.dist v c = 2} = cgraph.neighborSet u ∩ sphereFour v := by
      ext c
      exact ⟨fun ⟨huc, hvc⟩ => ⟨huc, B3loc v u c hvu huc hvc⟩, fun ⟨huc, hc⟩ => ⟨huc, hc.1⟩⟩
    rw [e]
    exact (B3con v u hvu).preconnected

end CFSG.Monster.B.GSide
