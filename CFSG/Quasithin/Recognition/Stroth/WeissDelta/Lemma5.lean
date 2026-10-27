module

public import CFSG.Quasithin.Recognition.Stroth.RootGroupRegular

public section

open scoped commutatorElement

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Stroth CFSG.Geometry.GeneralizedPolygons
  CFSG.GH74.GLS.SP CFSG.GH74.BNPair CFSG.QuasithinUnique
  CFSG.Quasithin.H13.F431.TwoF4 CFSG.Quasithin.H13.F431.Un
  CFSG.LieType.Ree.ReeTag CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

namespace CFSG.Quasithin.Stroth.WeissDelta

variable {V : Type} {Γ : SimpleGraph V} {H : Type} [Group H] [MulAction H V]
  [GraphAction H Γ]

variable (H) in
@[expose] def secondKernel (Γ : SimpleGraph V) (z : V) : Subgroup H :=
  fixingSubgroup H (Γ.neighborSet z) ⊓
    ⨅ w ∈ Γ.neighborSet z, fixingSubgroup H (Γ.neighborSet w)

theorem mem_secondKernel_iff {z : V} {g : H} :
    g ∈ secondKernel H Γ z ↔
      (∀ w, Γ.Adj z w → g • w = w) ∧
        (∀ v, Γ.Adj z v → ∀ w, Γ.Adj v w → g • w = w) := by
  simp only [secondKernel, Subgroup.mem_inf, Subgroup.mem_iInf, mem_fixingSubgroup_iff,
    SimpleGraph.mem_neighborSet]

theorem conj_mem_fixingSubgroup_neighborSet (g x : H) (z : V)
    (hx : x ∈ fixingSubgroup H (Γ.neighborSet z)) :
    g * x * g⁻¹ ∈ fixingSubgroup H (Γ.neighborSet (g • z)) := by
  rw [mem_fixingSubgroup_iff] at hx ⊢
  intro v hv
  have hv' : Γ.Adj z (g⁻¹ • v) := by
    simpa using (GraphAction.adj_smul g⁻¹ (g • z) v).mpr hv
  calc (g * x * g⁻¹) • v = g • (x • (g⁻¹ • v)) := by rw [mul_smul, mul_smul]
    _ = g • (g⁻¹ • v) := by rw [hx _ hv']
    _ = v := by rw [smul_inv_smul]

theorem conj_mem_secondKernel (g : H) {z : V} {x : H}
    (hx : x ∈ secondKernel H Γ z) : g * x * g⁻¹ ∈ secondKernel H Γ (g • z) := by
  rw [mem_secondKernel_iff] at hx ⊢
  refine ⟨fun v hv => ?_, fun v hv w hw => ?_⟩
  · have hv' : Γ.Adj z (g⁻¹ • v) := by
      simpa using (GraphAction.adj_smul g⁻¹ (g • z) v).mpr hv
    calc (g * x * g⁻¹) • v = g • (x • (g⁻¹ • v)) := by rw [mul_smul, mul_smul]
      _ = g • (g⁻¹ • v) := by rw [hx.1 _ hv']
      _ = v := by rw [smul_inv_smul]
  · have hv' : Γ.Adj z (g⁻¹ • v) := by
      simpa using (GraphAction.adj_smul g⁻¹ (g • z) v).mpr hv
    have hw' : Γ.Adj (g⁻¹ • v) (g⁻¹ • w) := by
      simpa using (GraphAction.adj_smul g⁻¹ v w).mpr hw
    calc (g * x * g⁻¹) • w = g • (x • (g⁻¹ • w)) := by rw [mul_smul, mul_smul]
      _ = g • (g⁻¹ • w) := by rw [hx.2 _ hv' _ hw']
      _ = w := by rw [smul_inv_smul]

@[expose] def path5 (a b c d e : V) (hab : Γ.Adj a b) (hbc : Γ.Adj b c)
    (hcd : Γ.Adj c d) (hde : Γ.Adj d e) : GPath Γ 4 where
  toFun i := if i = 0 then a else if i = 1 then b else if i = 2 then c
    else if i = 3 then d else e
  adj i hi := by
    have hi' : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases hi' with rfl | rfl | rfl | rfl <;> simp [hab, hbc, hcd, hde]
  tail i hi := by
    have h0 : i ≠ 0 := by omega
    have h1 : i ≠ 1 := by omega
    have h2 : i ≠ 2 := by omega
    have h3 : i ≠ 3 := by omega
    have h40 : (4 : ℕ) ≠ 0 := by norm_num
    have h41 : (4 : ℕ) ≠ 1 := by norm_num
    have h42 : (4 : ℕ) ≠ 2 := by norm_num
    have h43 : (4 : ℕ) ≠ 3 := by norm_num
    simp [h0, h1, h2, h3, h40, h41, h42, h43]

theorem path5_noBack {a b c d e : V} (hab : Γ.Adj a b) (hbc : Γ.Adj b c)
    (hcd : Γ.Adj c d) (hde : Γ.Adj d e) (hac : a ≠ c) (hbd : b ≠ d) (hce : c ≠ e) :
    (path5 a b c d e hab hbc hcd hde).NoBack := by
  intro i hi
  have hi' : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases hi' with rfl | rfl | rfl <;> simp [path5, hac, hbd, hce]

theorem commutator_pathRootGroup_le_secondKernel (hM : MoufangCondition H Γ 4)
    (hW : WeissFree H Γ 4) {p : GPath Γ 6} (hp : p.NoBack) :
    ⁅pathRootGroup H Γ (p.drop 2 (by norm_num)),
        pathRootGroup H Γ (p.drop 2 (by norm_num))⁆ ≤ secondKernel H Γ (p 4) := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  have hmemU : ∀ {g : H}, g ∈ pathRootGroup H Γ (p.drop 2 (by norm_num)) →
      g ∈ fixingSubgroup H (Γ.neighborSet (p 3)) ∧
        g ∈ fixingSubgroup H (Γ.neighborSet (p 4)) ∧
          g ∈ fixingSubgroup H (Γ.neighborSet (p 5)) := by
    intro g hg
    have hfix := mem_pathRootGroup.mp hg
    refine ⟨?_, ?_, ?_⟩
    · rw [mem_fixingSubgroup_iff]
      intro w hw
      have h := hfix 1 (by norm_num) (by norm_num) w
      have h1 : (p.drop 2 (by norm_num) : GPath Γ 4) 1 = p 3 := by simp
      rw [h1] at h
      exact h hw
    · rw [mem_fixingSubgroup_iff]
      intro w hw
      have h := hfix 2 (by norm_num) (by norm_num) w
      have h1 : (p.drop 2 (by norm_num) : GPath Γ 4) 2 = p 4 := by simp
      rw [h1] at h
      exact h hw
    · rw [mem_fixingSubgroup_iff]
      intro w hw
      have h := hfix 3 (by norm_num) (by norm_num) w
      have h1 : (p.drop 2 (by norm_num) : GPath Γ 4) 3 = p 5 := by simp
      rw [h1] at h
      exact h hw
  obtain ⟨ha3, ha4, ha5⟩ := hmemU ha
  obtain ⟨hb3, hb4, hb5⟩ := hmemU hb
  refine mem_secondKernel_iff.mpr ⟨?_, ?_⟩
  · intro w hw
    have hmem : ⁅a, b⁆ ∈ fixingSubgroup H (Γ.neighborSet (p 4)) :=
      Subgroup.commutator_le_self _ (Subgroup.commutator_mem_commutator ha4 hb4)
    exact (mem_fixingSubgroup_iff H).mp hmem w hw
  · intro v hv w hw
    by_cases hv3 : v = p 3
    · subst hv3
      have hmem : ⁅a, b⁆ ∈ fixingSubgroup H (Γ.neighborSet (p 3)) :=
        Subgroup.commutator_le_self _ (Subgroup.commutator_mem_commutator ha3 hb3)
      exact (mem_fixingSubgroup_iff H).mp hmem w hw
    · obtain ⟨c, hcfix, hc5⟩ := hM (p.take 4 (by norm_num)) (hp.take 4 (by norm_num))
        (p 5) v (by simpa using p.adj 4 (by norm_num)) hv
        (by
          have h3 : (p.take 4 (by norm_num) : GPath Γ 4) 3 = p 3 := by simp
          rw [h3]
          exact (hp 3 (by norm_num)).symm)
        (by
          have h3 : (p.take 4 (by norm_num) : GPath Γ 4) 3 = p 3 := by simp
          rw [h3]
          exact hv3)
      have hcfixg : ∀ i, 1 ≤ i → i ≤ 3 →
          c ∈ fixingSubgroup H (Γ.neighborSet ((p.take 4 (by norm_num) : GPath Γ 4) i)) := by
        intro i hi1 hi3
        exact (mem_fixingSubgroup_iff H).mpr (hcfix i hi1 hi3)
      have hc2g : c ∈ fixingSubgroup H (Γ.neighborSet (p 2)) := by
        simpa using hcfixg 2 (by norm_num) (by norm_num)
      have hc3g : c ∈ fixingSubgroup H (Γ.neighborSet (p 3)) := by
        simpa using hcfixg 3 (by norm_num) (by norm_num)
      have hc2 : c • p 2 = p 2 :=
        (mem_fixingSubgroup_iff H).mp hc3g (p 2) (by simpa using (p.adj 2 (by norm_num)).symm)
      have hc3 : c • p 3 = p 3 :=
        (mem_fixingSubgroup_iff H).mp hc2g (p 3) (p.adj 2 (by norm_num))
      have hc4 : c • p 4 = p 4 :=
        (mem_fixingSubgroup_iff H).mp hc3g (p 4) (p.adj 3 (by norm_num))
      let h : H := (c * b⁻¹ * c⁻¹) * b
      have hh3 : h ∈ fixingSubgroup H (Γ.neighborSet (p 3)) := by
        have hconj : c * b⁻¹ * c⁻¹ ∈ fixingSubgroup H (Γ.neighborSet (p 3)) := by
          have := conj_mem_fixingSubgroup_neighborSet c b⁻¹ (p 3) (Subgroup.inv_mem _ hb3)
          simpa [hc3] using this
        exact Subgroup.mul_mem _ hconj hb3
      have hh4 : h ∈ fixingSubgroup H (Γ.neighborSet (p 4)) := by
        have hconj : c * b⁻¹ * c⁻¹ ∈ fixingSubgroup H (Γ.neighborSet (p 4)) := by
          have := conj_mem_fixingSubgroup_neighborSet c b⁻¹ (p 4) (Subgroup.inv_mem _ hb4)
          simpa [hc4] using this
        exact Subgroup.mul_mem _ hconj hb4
      have hh2 : h ∈ fixingSubgroup H (Γ.neighborSet (p 2)) := by
        have hb2 : b • p 2 = p 2 :=
          (mem_fixingSubgroup_iff H).mp hb3 (p 2) (by simpa using (p.adj 2 (by norm_num)).symm)
        have hb2inv : b⁻¹ • p 2 = p 2 := by
          simpa [hb2] using (inv_smul_smul b (p 2))
        have hconj : b⁻¹ * c⁻¹ * b ∈ fixingSubgroup H (Γ.neighborSet (p 2)) := by
          have := conj_mem_fixingSubgroup_neighborSet b⁻¹ c⁻¹ (p 2)
            (Subgroup.inv_mem _ hc2g)
          simpa [hb2inv] using this
        have heq : h = c * (b⁻¹ * c⁻¹ * b) := by
          simp only [h]
          group
        rw [heq]
        exact Subgroup.mul_mem _ hc2g hconj
      have hcomm_ah : ⁅a, h⁆ = 1 := by
        have hm3 : ⁅a, h⁆ ∈ fixingSubgroup H (Γ.neighborSet (p 3)) :=
          Subgroup.commutator_le_self _ (Subgroup.commutator_mem_commutator ha3 hh3)
        have hm4 : ⁅a, h⁆ ∈ fixingSubgroup H (Γ.neighborSet (p 4)) :=
          Subgroup.commutator_le_self _ (Subgroup.commutator_mem_commutator ha4 hh4)
        have ha2 : a • p 2 = p 2 :=
          (mem_fixingSubgroup_iff H).mp ha3 (p 2) (by simpa using (p.adj 2 (by norm_num)).symm)
        have hm2 : ⁅a, h⁆ ∈ fixingSubgroup H (Γ.neighborSet (p 2)) := by
          have hconj : a * h * a⁻¹ ∈ fixingSubgroup H (Γ.neighborSet (p 2)) := by
            have := conj_mem_fixingSubgroup_neighborSet a h (p 2) hh2
            rwa [ha2] at this
          rw [commutatorElement_def]
          exact Subgroup.mul_mem _ hconj (Subgroup.inv_mem _ hh2)
        have hh5 : h • p 5 = p 5 :=
          (mem_fixingSubgroup_iff H).mp hh4 (p 5) (p.adj 4 (by norm_num))
        have hm5 : ⁅a, h⁆ ∈ fixingSubgroup H (Γ.neighborSet (p 5)) := by
          have hconj : h * a⁻¹ * h⁻¹ ∈ fixingSubgroup H (Γ.neighborSet (p 5)) := by
            have := conj_mem_fixingSubgroup_neighborSet h a⁻¹ (p 5) (Subgroup.inv_mem _ ha5)
            rwa [hh5] at this
          rw [commutatorElement_def]
          have := Subgroup.mul_mem _ ha5 hconj
          simpa only [mul_assoc] using this
        let q : GPath Γ 4 := path5 (p 5) (p 4) (p 3) (p 2) (p 1)
          (p.adj 4 (by norm_num)).symm (p.adj 3 (by norm_num)).symm
          (p.adj 2 (by norm_num)).symm (p.adj 1 (by norm_num)).symm
        have hqnb : q.NoBack := by
          intro i hi
          have hi' : i = 0 ∨ i = 1 ∨ i = 2 := by omega
          rcases hi' with rfl | rfl | rfl
          · simpa [q, path5] using (hp 3 (by norm_num)).symm
          · simpa [q, path5] using (hp 2 (by norm_num)).symm
          · simpa [q, path5] using (hp 1 (by norm_num)).symm
        have hqfix : ∀ i, i ≤ 4 → ⁅a, h⁆ • q i = q i := by
          intro i hi
          have hi' : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
          rcases hi' with rfl | rfl | rfl | rfl | rfl
          · simpa [q, path5] using
              (mem_fixingSubgroup_iff H).mp hm4 (p 5) (p.adj 4 (by norm_num))
          · simpa [q, path5] using
              (mem_fixingSubgroup_iff H).mp hm3 (p 4) (p.adj 3 (by norm_num))
          · simpa [q, path5] using
              (mem_fixingSubgroup_iff H).mp hm2 (p 3) (p.adj 2 (by norm_num))
          · simpa [q, path5] using
              (mem_fixingSubgroup_iff H).mp hm3 (p 2) (by simpa using (p.adj 2 (by norm_num)).symm)
          · simpa [q, path5] using
              (mem_fixingSubgroup_iff H).mp hm2 (p 1) (by simpa using (p.adj 1 (by norm_num)).symm)
        exact hW q hqnb ⁅a, h⁆ hqfix
          (fun x hx => (mem_fixingSubgroup_iff H).mp hm5 x hx)
          (fun x hx => (mem_fixingSubgroup_iff H).mp hm4 x hx)
      have hb_eq : (c * b * c⁻¹) * h = b := by
        simp only [h]
        group
      have hcomm_eq : ⁅a, b⁆ = ⁅a, c * b * c⁻¹⁆ := by
        conv_lhs => rw [← hb_eq]
        rw [commutatorElement_mul_right_eq_mul_conj, hcomm_ah, mul_one]
        group
      have hadj : Γ.Adj (p 4) (c • p 5) := by
        have h := (GraphAction.adj_smul c (p 4) (p 5)).mpr (p.adj 4 (by norm_num))
        rwa [hc4] at h
      have hafix : a • (c • p 5) = c • p 5 :=
        (mem_fixingSubgroup_iff H).mp ha4 (c • p 5) hadj
      have hcomm_v : ⁅a, c * b * c⁻¹⁆ ∈ fixingSubgroup H (Γ.neighborSet (c • p 5)) := by
        have hcb : c * b * c⁻¹ ∈ fixingSubgroup H (Γ.neighborSet (c • p 5)) :=
          conj_mem_fixingSubgroup_neighborSet c b (p 5) hb5
        have hconj : a * (c * b * c⁻¹) * a⁻¹ ∈
            fixingSubgroup H (Γ.neighborSet (c • p 5)) := by
          have := conj_mem_fixingSubgroup_neighborSet a (c * b * c⁻¹) (c • p 5) hcb
          rwa [hafix] at this
        rw [commutatorElement_def]
        change a * (c * b * c⁻¹) * a⁻¹ * (c * b * c⁻¹)⁻¹ ∈
          fixingSubgroup H (Γ.neighborSet (c • p 5))
        exact Subgroup.mul_mem _ hconj (Subgroup.inv_mem _ hcb)
      rw [hcomm_eq]
      have hw' : Γ.Adj (c • p 5) w := by rwa [hc5]
      exact (mem_fixingSubgroup_iff H).mp hcomm_v w hw'

theorem secondKernel_ne_bot_of_not_comm (hM : MoufangCondition H Γ 4)
    (hW : WeissFree H Γ 4) {p : GPath Γ 6} (hp : p.NoBack)
    (hnc : ∃ a ∈ pathRootGroup H Γ (p.drop 2 (by norm_num)),
      ∃ b ∈ pathRootGroup H Γ (p.drop 2 (by norm_num)), a * b ≠ b * a) :
    secondKernel H Γ (p 4) ≠ ⊥ := by
  obtain ⟨a, ha, b, hb, hab⟩ := hnc
  have hle := commutator_pathRootGroup_le_secondKernel hM hW hp
  have hmem : ⁅a, b⁆ ∈ secondKernel H Γ (p 4) :=
    (Subgroup.commutator_le.mp hle) a ha b hb
  intro hbot
  have hone : ⁅a, b⁆ = 1 := by
    have : ⁅a, b⁆ ∈ (⊥ : Subgroup H) := by rwa [hbot] at hmem
    simpa using this
  exact hab (commutatorElement_eq_one_iff_mul_comm.mp hone)

theorem commutator_secondKernel_eq_bot (hW : WeissFree H Γ 4)
    (hne : ∀ v w : V, Γ.Adj v w → ∃ u, Γ.Adj v u ∧ u ≠ w) {y z y' : V} (hyz : Γ.Adj y z)
    (hzy' : Γ.Adj z y') (hyy' : y ≠ y') :
    ⁅secondKernel H Γ y, secondKernel H Γ y'⁆ = ⊥ := by
  rw [eq_bot_iff, Subgroup.commutator_le]
  intro a ha b hb
  rw [Subgroup.mem_bot]
  obtain ⟨w, hy'w, hwz⟩ := hne y' z hzy'.symm
  obtain ⟨u, hwu, huy'⟩ := hne w y' hy'w.symm
  have hA := mem_secondKernel_iff.mp ha
  have hB := mem_secondKernel_iff.mp hb
  have hAz : a ∈ fixingSubgroup H (Γ.neighborSet z) :=
    (mem_fixingSubgroup_iff H).mpr (hA.2 z hyz)
  have hBz : b ∈ fixingSubgroup H (Γ.neighborSet z) :=
    (mem_fixingSubgroup_iff H).mpr (hB.2 z hzy'.symm)
  have ha_y : a • y = y := (mem_fixingSubgroup_iff H).mp hAz y hyz.symm
  have hb_y : b • y = y := (mem_fixingSubgroup_iff H).mp hBz y hyz.symm
  have ha_y' : a • y' = y' := (mem_fixingSubgroup_iff H).mp hAz y' hzy'
  have hb_y' : b • y' = y' := (mem_fixingSubgroup_iff H).mp hBz y' hzy'
  have hmemA : ⁅a, b⁆ ∈ secondKernel H Γ y := by
    have hconj : b * a⁻¹ * b⁻¹ ∈ secondKernel H Γ y := by
      have := conj_mem_secondKernel b (z := y) (Subgroup.inv_mem _ ha)
      rwa [hb_y] at this
    rw [commutatorElement_def]
    have := Subgroup.mul_mem _ ha hconj
    simpa only [mul_assoc] using this
  have hmemB : ⁅a, b⁆ ∈ secondKernel H Γ y' := by
    have hconj : a * b * a⁻¹ ∈ secondKernel H Γ y' := by
      have := conj_mem_secondKernel a (z := y') hb
      rwa [ha_y'] at this
    rw [commutatorElement_def]
    exact Subgroup.mul_mem _ hconj (Subgroup.inv_mem _ hb)
  have hIy : ⁅a, b⁆ ∈ fixingSubgroup H (Γ.neighborSet y) :=
    (mem_fixingSubgroup_iff H).mpr (mem_secondKernel_iff.mp hmemA).1
  have hIz : ⁅a, b⁆ ∈ fixingSubgroup H (Γ.neighborSet z) :=
    (mem_fixingSubgroup_iff H).mpr ((mem_secondKernel_iff.mp hmemA).2 z hyz)
  have hIy' : ⁅a, b⁆ ∈ fixingSubgroup H (Γ.neighborSet y') :=
    (mem_fixingSubgroup_iff H).mpr (mem_secondKernel_iff.mp hmemB).1
  have hIw : ⁅a, b⁆ ∈ fixingSubgroup H (Γ.neighborSet w) :=
    (mem_fixingSubgroup_iff H).mpr ((mem_secondKernel_iff.mp hmemB).2 w hy'w)
  let q : GPath Γ 4 := path5 y z y' w u hyz hzy' hy'w hwu
  have hqnb : q.NoBack := by
    intro i hi
    have hi' : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases hi' with rfl | rfl | rfl
    · simpa [q, path5] using hyy'
    · simpa [q, path5] using hwz.symm
    · simpa [q, path5] using huy'.symm
  have hqfix : ∀ i, i ≤ 4 → ⁅a, b⁆ • q i = q i := by
    intro i hi
    have hi' : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
    rcases hi' with rfl | rfl | rfl | rfl | rfl
    · simpa [q, path5] using (mem_fixingSubgroup_iff H).mp hIz y hyz.symm
    · simpa [q, path5] using (mem_fixingSubgroup_iff H).mp hIy z hyz
    · simpa [q, path5] using (mem_fixingSubgroup_iff H).mp hIz y' hzy'
    · simpa [q, path5] using (mem_fixingSubgroup_iff H).mp hIy' w hy'w
    · simpa [q, path5] using (mem_fixingSubgroup_iff H).mp hIw u hwu
  exact hW q hqnb ⁅a, b⁆ hqfix
    (fun x hx => (mem_fixingSubgroup_iff H).mp hIy x hx)
    (fun x hx => (mem_fixingSubgroup_iff H).mp hIz x hx)

end CFSG.Quasithin.Stroth.WeissDelta

end
