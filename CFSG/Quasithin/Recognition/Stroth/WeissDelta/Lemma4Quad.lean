module

public import CFSG.Quasithin.Recognition.Stroth.WeissDelta.Lemma4Transfer
public import CFSG.Quasithin.Recognition.Stroth.WeissDelta.Lemma5Kernel2
public import CFSG.Quasithin.Recognition.Stroth.WeissDelta.VertexFacts

public section

open scoped Pointwise commutatorElement

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Stroth CFSG.Geometry.GeneralizedPolygons
  CFSG.GH74.GLS.SP CFSG.GH74.BNPair CFSG.QuasithinUnique
  CFSG.Quasithin.H13.F431.TwoF4 CFSG.Quasithin.H13.F431.Un
  CFSG.LieType.Ree.ReeTag CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

namespace CFSG.Quasithin.Stroth.WeissDelta

variable {V : Type} {Γ : SimpleGraph V} {H : Type} [Group H] [MulAction H V] [GraphAction H Γ]

structure QuadSetup (H : Type) [Group H] [MulAction H V] (Γ : SimpleGraph V)
    [GraphAction H Γ] (k m : ℕ) (F : Type) [Field F] (ut : V → Prop) : Prop where
  egirth : ((2 * 4 + 2 : ℕ) : ℕ∞) < Γ.egirth
  moufang : MoufangCondition H Γ 4
  weissFree : WeissFree H Γ 4
  ne : ∀ v w : V, Γ.Adj v w → ∃ u, Γ.Adj v u ∧ u ≠ w
  three : ∀ v w w' : V, Γ.Adj v w → Γ.Adj v w' → ∃ u, Γ.Adj v u ∧ u ≠ w ∧ u ≠ w'
  val : ∀ v w : V, Γ.Adj v w → ∃ e : ℕ, Nat.card {y : V // Γ.Adj v y ∧ y ≠ w} = 2 ^ e
  loc : ∀ w u v : V, Γ.Adj w u → Γ.Adj w v → ∃ g : H, g • w = w ∧ g • u = v
  kernel_le : ∀ z, FixingNeighbourhoodFixesVertex (H := H) (Γ := Γ) z
  adj : ∀ v w, Γ.Adj v w → (ut v ↔ ¬ ut w)
  conj : ∀ v w, (ut v ↔ ut w) → ∃ g : H, g • v = w
  u3 : ∀ v, ut v → IsLocalU3 H Γ v k F
  l2 : ∀ v, ¬ ut v → IsLocalL2 H Γ v m

namespace QuadSetup

variable {k m : ℕ} {F : Type} [Field F] [Finite F] {ut : V → Prop}

theorem localFacts [Finite H] (hk : 2 ≤ k) (hm : 3 ≤ m) (hF : Nat.card F = (2 ^ k) ^ 2)
    (hS : QuadSetup H Γ k m F ut) (z : V) : LocalFacts H Γ z := by
  by_cases hz : ut z
  · exact (vertexFacts_of_isLocalU3 hk F hF (hS.kernel_le z) (hS.u3 z hz)).1
  · exact (vertexFacts_of_isLocalL2 (by omega : 2 ≤ m) (hS.kernel_le z) (hS.l2 z hz)).1

theorem rootFacts [Finite H] (hk : 2 ≤ k) (hm : 3 ≤ m) (hF : Nat.card F = (2 ^ k) ^ 2)
    (hS : QuadSetup H Γ k m F ut) (z : V) : RootFacts H Γ 4 z := by
  by_cases hz : ut z
  · exact rootFacts_of_isLocalU3 (n := 4) (by norm_num) hS.moufang hS.weissFree hS.ne hS.val
      hS.kernel_le hk F hF (hS.u3 z hz)
  · exact rootFacts_of_isLocalL2 (n := 4) (by norm_num) hS.moufang hS.weissFree hS.ne hS.val
      hS.kernel_le (by omega : 2 ≤ m) (hS.l2 z hz)

theorem secondKernel_ne_bot [Finite H] (hk : 2 ≤ k)
    (hF : Nat.card F = (2 ^ k) ^ 2) (hS : QuadSetup H Γ k m F ut) {x : V} (hx : ut x) :
    secondKernel H Γ x ≠ ⊥ := by
  classical
  have hcard : Nat.card {w : V // Γ.Adj x w} = 2 ^ (3 * k) + 1 := (hS.u3 x hx).1
  obtain ⟨⟨z, hxz⟩, -⟩ := Nat.card_pos_iff.mp (by rw [hcard]; positivity)
  obtain ⟨p, hp, hpx, hpz⟩ := exists_backward_noBack hS.ne hxz 4
  have hpz' : p 3 ≠ z := hpz (by norm_num)
  obtain ⟨z', hzz', hz'x⟩ := hS.ne z x hxz.symm
  have hpxz : Γ.Adj (p 4) z := by rw [hpx]; exact hxz
  have hqadj : Γ.Adj ((p.snoc z hpxz) 5) z' := by
    rw [GPath.snoc_last]
    exact hzz'
  let q : GPath Γ 6 := (p.snoc z hpxz).snoc z' hqadj
  have hq : q.NoBack := by
    refine GPath.noBack_snoc ?_ hqadj (fun _ => ?_)
    · refine GPath.noBack_snoc hp hpxz (fun _ => ?_)
      exact hpz'.symm
    · simpa [hpx] using hz'x
  have hq4 : q 4 = x := by
    show ((p.snoc z hpxz).snoc z' hqadj) 4 = x
    rw [GPath.snoc_of_le _ _ _ (by norm_num : 4 ≤ 5)]
    rw [GPath.snoc_of_le _ _ _ (by norm_num : 4 ≤ 4)]
    exact hpx
  have hxL : ¬ ut z := (hS.adj x z hxz).mp hx
  have hz'U : ut z' := by
    by_contra hz'
    exact hxL ((hS.adj z z' hzz').mpr hz')
  have hq6 : q 6 = z' := by
    show ((p.snoc z hpxz).snoc z' hqadj) 6 = z'
    rw [GPath.snoc_last]
  have hnc : ∃ a ∈ pathRootGroup H Γ (q.drop 2 (by norm_num)),
      ∃ b ∈ pathRootGroup H Γ (q.drop 2 (by norm_num)), a * b ≠ b * a :=
    exists_not_comm_pathRootGroup_of_isLocalU3 (n := 4) (by norm_num) hS.moufang
      hS.weissFree hS.ne hS.val hS.kernel_le hk F hF (hq.drop 2 (by norm_num))
      (by simpa [hq6] using hS.u3 z' hz'U)
  have hne := secondKernel_ne_bot_of_not_comm hS.moufang hS.weissFree hq hnc
  simpa [hq4] using hne

theorem exists_mem_kernelAt [Finite V] [Finite H] (hk : 2 ≤ k) (hm : 3 ≤ m)
    (hF : Nat.card F = (2 ^ k) ^ 2) (hS : QuadSetup H Γ k m F ut) (W : ClosedGoodPath H Γ)
    (hu : ut (W.x 0)) :
    ∃ m₀ ∈ W.kernelAt 0, m₀ ∈ socleAt H Γ (W.x 2) ∧
      m₀ ^ (2 ^ k - 1) ∈ fixingSubgroup H (Γ.neighborSet (W.x 2)) ∧
      m₀ ∉ fixingSubgroup H (Γ.neighborSet (W.x 2)) := by
  classical
  let F₀ : Subgroup H := fixingSubgroup H (Γ.neighborSet (W.x 0))
  let G₀ : Subgroup H := MulAction.stabilizer H (W.x 0)
  have hLF := localFacts hk hm hF hS
  have hRF := rootFacts hk hm hF hS
  have hq2 : 2 ≤ 2 ^ k := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega : 1 ≤ k)
  have hx1' : Γ.Adj (W.x 0) (W.x (-1)) := by simpa using (W.adj (-1)).symm
  have h11 : W.x 1 ≠ W.x (-1) := by simpa using (W.ne_add_two (-1)).symm
  have hUF₀ : UnitaryFacts H Γ (W.x 0) (2 ^ k) :=
    (vertexFacts_of_isLocalU3 hk F hF (hS.kernel_le (W.x 0)) (hS.u3 (W.x 0) hu)).2.2
  obtain ⟨t, htT, htNot⟩ := hUF₀.exists_pow (W.x 1) (W.x (-1)) (W.adj 0) hx1' h11
  have htSoc : t ∈ socleAt H Γ (W.x 0) :=
    (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp htT)).1.1
  have htStab : t ∈ G₀ :=
    socleAt_le_stabilizer (hLF (W.x 0)).kernel_le htSoc
  have htPow : (t ^ (2 ^ k + 1)) ^ (2 ^ k + 1) ∉ F₀ := htNot
  have hC : ∀ g : H, CenterFacts H Γ (g • W.x 0) (2 ^ k + 1) := by
    intro g
    exact (vertexFacts_of_isLocalU3 hk F hF (hS.kernel_le (g • W.x 0))
      (isLocalU3_smul (hS.u3 (W.x 0) hu) g)).2.1
  have hsecond : secondKernel H Γ (W.x 0) ≠ ⊥ := secondKernel_ne_bot hk hF hS hu
  obtain ⟨y, hyadj, hyne, a, haG1y, haFix0, haFix1, haFix1', haOdd, haConj⟩ :=
    exists_odd_mem_fixingSubgroup_of_secondKernel_ne_bot (e := 2 ^ k + 1)
      hS.moufang hS.weissFree hS.ne hS.val hS.loc hLF hRF hC hsecond
      (W.adj 0) hx1' h11 htT
  have haStab : a ∈ G₀ := MulAction.mem_stabilizer_iff.mpr haFix0
  have htPowStab : t ^ (2 ^ k + 1) ∈ G₀ := G₀.pow_mem htStab _
  have hF₀le : F₀ ≤ socleAt H Γ (W.x 0) := by
    unfold socleAt
    exact le_sup_right
  have haSoc : a ∈ socleAt H Γ (W.x 0) := by
    have hmem : (a * (t ^ (2 ^ k + 1))⁻¹) * t ^ (2 ^ k + 1) ∈ socleAt H Γ (W.x 0) :=
      (socleAt H Γ (W.x 0)).mul_mem (hF₀le haConj) (Subgroup.pow_mem _ htSoc _)
    have heq : (a * (t ^ (2 ^ k + 1))⁻¹) * t ^ (2 ^ k + 1) = a := by group
    rwa [heq] at hmem
  have haPow : a ^ (2 ^ k - 1) ∈ F₀ := by
    haveI hN₀ : (F₀.subgroupOf G₀).Normal := by
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer_inf]
      exact (le_inf (stabilizer_le_normalizer_fixingSubgroup (H := H) (Γ := Γ)
        (z := W.x 0)) G₀.le_normalizer).trans
        Subgroup.inf_normalizer_le_normalizer_inf
    let aK : G₀ := ⟨a, haStab⟩
    let tK : G₀ := ⟨t ^ (2 ^ k + 1), htPowStab⟩
    have hdiv : aK * tK⁻¹ ∈ F₀.subgroupOf G₀ := by
      rw [Subgroup.mem_subgroupOf]
      simpa [aK, tK] using haConj
    have hquot : (QuotientGroup.mk aK : G₀ ⧸ F₀.subgroupOf G₀) =
        QuotientGroup.mk tK := by
      rw [QuotientGroup.eq_iff_div_mem]
      simpa [div_eq_mul_inv] using hdiv
    have hpowquot : (QuotientGroup.mk (aK ^ (2 ^ k - 1)) :
        G₀ ⧸ F₀.subgroupOf G₀) = QuotientGroup.mk (tK ^ (2 ^ k - 1)) := by
      simpa using congrArg (fun z => z ^ (2 ^ k - 1)) hquot
    have hmemK : (aK ^ (2 ^ k - 1)) / (tK ^ (2 ^ k - 1)) ∈ F₀.subgroupOf G₀ :=
      QuotientGroup.eq_iff_div_mem.mp hpowquot
    have hprod : a ^ (2 ^ k - 1) *
        ((t ^ (2 ^ k + 1)) ^ (2 ^ k - 1))⁻¹ ∈ F₀ := by
      rw [Subgroup.mem_subgroupOf] at hmemK
      simpa [aK, tK, div_eq_mul_inv, Subgroup.coe_pow] using hmemK
    have hpowcard : (t ^ (2 ^ k + 1)) ^ (2 ^ k - 1) =
        t ^ ((2 ^ k) ^ 2 - 1) := by
      have hexp : (2 ^ k + 1) * (2 ^ k - 1) = (2 ^ k) ^ 2 - 1 := by
        simpa using (Nat.sq_sub_sq (2 ^ k) 1).symm
      rw [← pow_mul, hexp]
    have htPowCard : (t ^ (2 ^ k + 1)) ^ (2 ^ k - 1) ∈ F₀ := by
      rw [hpowcard]
      exact hUF₀.pow_card (W.x 1) (W.x (-1)) (W.adj 0) hx1' h11 t htT
    have := F₀.mul_mem hprod htPowCard
    simpa [mul_assoc] using this
  have haNot : a ∉ F₀ := by
    intro haF
    apply htPow
    have htmem : t ^ (2 ^ k + 1) ∈ F₀ := by
      have heq : (a * (t ^ (2 ^ k + 1))⁻¹)⁻¹ * a = t ^ (2 ^ k + 1) := by group
      rw [← heq]
      exact F₀.mul_mem (F₀.inv_mem haConj) haF
    exact Subgroup.pow_mem _ htmem _
  have hKle : Subgroup.zpowers a ≤ MulAction.stabilizer H (W.x (-1)) ⊓
      MulAction.stabilizer H (W.x 0) := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.mem_inf.mpr
      ⟨MulAction.mem_stabilizer_iff.mpr haFix1', MulAction.mem_stabilizer_iff.mpr haFix0⟩
  have hKodd : ∀ z, Odd ((fixingSubgroup H (Γ.neighborSet z)).relIndex
      (Subgroup.zpowers a)) := by
    intro z
    exact Odd.of_dvd_nat (by rw [Nat.card_zpowers]; exact haOdd)
      (Subgroup.relIndex_dvd_card _ _)
  obtain ⟨u₄, hu₄adj, hu₄ne, hu₄fix⟩ :=
    (hLF (W.x (-1))).oddFix (W.x 0) (W.adj (-1)) (Subgroup.zpowers a)
      hKle (hKodd (W.x (-1)))
  have hu₄a : a • u₄ = u₄ := hu₄fix a (Subgroup.mem_zpowers a)
  have hKle' : Subgroup.zpowers a ≤ MulAction.stabilizer H u₄ ⊓
      MulAction.stabilizer H (W.x (-1)) := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.mem_inf.mpr
      ⟨MulAction.mem_stabilizer_iff.mpr hu₄a, MulAction.mem_stabilizer_iff.mpr haFix1'⟩
  obtain ⟨u₅, hu₅adj, hu₅ne, hu₅fix⟩ :=
    (hLF u₄).oddFix (W.x (-1)) hu₄adj.symm (Subgroup.zpowers a)
      hKle' (hKodd u₄)
  have hyadj' : Γ.Adj y (W.x 1) := by simpa using hyadj.symm
  have h10 : Γ.Adj (W.x 1) (W.x 0) := by simpa using (W.adj 0).symm
  let p4 : GPath Γ 4 := path5 y (W.x 1) (W.x 0) (W.x (-1)) u₄
    hyadj' h10 hx1' hu₄adj
  have hp4nb : p4.NoBack :=
    path5_noBack hyadj' h10 hx1' hu₄adj hyne h11 hu₄ne.symm
  let p : GPath Γ 5 := p4.snoc u₅ hu₅adj
  have hpnb : p.NoBack := GPath.noBack_snoc hp4nb hu₅adj (fun _ => hu₅ne)
  have hpv : p 0 = y ∧ p 1 = W.x 1 ∧ p 2 = W.x 0 ∧ p 3 = W.x (-1) ∧
      p 4 = u₄ ∧ p 5 = u₅ := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [p, p4, path5, GPath.snoc_of_le, GPath.snoc_last]
  obtain ⟨hp0, hp1, hp2, hp3, hp4, hp5⟩ := hpv
  have haStabPath : a ∈ GPath.stabPath (H := H) p := by
    rw [GPath.mem_stabPath_iff]
    intro j hj
    interval_cases j
    · rw [hp0]
      exact MulAction.mem_stabilizer_iff.mp ((hLF y).kernel_le haG1y)
    · rw [hp1]
      exact haFix1
    · rw [hp2]
      exact haFix0
    · rw [hp3]
      exact haFix1'
    · rw [hp4]
      exact hu₄a
    · rw [hp5]
      exact hu₅fix a (Subgroup.mem_zpowers a)
  obtain ⟨WP, hWP⟩ := ClosedGoodPath.exists_of_noBack (n := 4) (by norm_num)
    hS.moufang hS.weissFree hS.ne hLF hpnb
  have hwin : WP.window 0 5 = p := by
    apply GPath.ext'
    intro j hj
    rw [ClosedGoodPath.window_apply WP 0 (s := 5) hj, zero_add]
    exact hWP j (by omega)
  have haStabWP : a ∈ WP.stab := by
    rw [← ClosedGoodPath.stabPath_window (n := 4) (by norm_num) hS.weissFree hLF WP 0,
      hwin]
    exact haStabPath
  have hWP0 : WP.x 0 = y := by
    have h1 : WP.x ((0 : ℕ) : ℤ) = p.toFun 0 := hWP 0 (by norm_num)
    exact h1.trans hp0
  have haKernelWP : a ∈ WP.kernelAt 0 := by
    refine ⟨?_, haStabWP⟩
    rwa [hWP0]
  have hyU : ut y := by
    have hx1L : ¬ ut (W.x 1) := (hS.adj (W.x 0) (W.x 1) (W.adj 0)).mp hu
    by_contra hy
    exact hx1L ((hS.adj (W.x 1) y hyadj).mpr hy)
  have htype : ut y ↔ ut (W.x 0) := ⟨fun _ => hu, fun _ => hyU⟩
  obtain ⟨g₀, hg₀⟩ := hS.conj y (W.x 0) htype
  have hg₀' : g₀ • WP.x 0 = W.x 0 := by rw [hWP0]; exact hg₀
  obtain ⟨g, hg⟩ := ClosedGoodPath.exists_smul_eq (n := 4) (by norm_num)
    hS.moufang hS.weissFree hS.ne hLF hS.loc WP W ⟨g₀, hg₀'⟩
  let m₀ : H := g * a * g⁻¹
  have hm₀Kernel : m₀ ∈ W.kernelAt 0 := by
    have hmap := ClosedGoodPath.kernelAt_eq_map_conj WP W hg 0
    rw [hmap]
    exact Subgroup.mem_map_of_mem _ haKernelWP
  have hx2 : WP.x 2 = W.x 0 := by
    have h1 : WP.x ((2 : ℕ) : ℤ) = p.toFun 2 := hWP 2 (by norm_num)
    exact h1.trans hp2
  have haSocWP : a ∈ socleAt H Γ (WP.x 2) := by
    rw [hx2]
    exact haSoc
  have hm₀Soc : m₀ ∈ socleAt H Γ (W.x 2) := by
    have hmap := socleAt_smul (H := H) (Γ := Γ) g (WP.x 2)
    rw [hg 2] at hmap
    rw [hmap]
    exact Subgroup.mem_map_of_mem _ haSocWP
  have haPowWP : a ^ (2 ^ k - 1) ∈ fixingSubgroup H (Γ.neighborSet (WP.x 2)) := by
    rw [hx2]
    exact haPow
  have hm₀Pow : m₀ ^ (2 ^ k - 1) ∈ fixingSubgroup H (Γ.neighborSet (W.x 2)) := by
    have hmap := fixingSubgroup_neighborSet_smul (H := H) (Γ := Γ) g (WP.x 2)
    rw [hg 2] at hmap
    rw [hmap]
    have hmem : (MulAut.conj g).toMonoidHom (a ^ (2 ^ k - 1)) ∈
        (fixingSubgroup H (Γ.neighborSet (WP.x 2))).map
          (MulAut.conj g).toMonoidHom :=
      Subgroup.mem_map_of_mem _ haPowWP
    rw [map_pow] at hmem
    simpa [m₀, MulAut.conj_apply] using hmem
  have hm₀Not : m₀ ∉ fixingSubgroup H (Γ.neighborSet (W.x 2)) := by
    intro hm₀F
    have haF : a ∈ F₀ := by
      have h := conj_mem_fixingSubgroup_neighborSet (H := H) (Γ := Γ) g⁻¹ m₀
        (W.x 2) hm₀F
      have hg2inv : g⁻¹ • W.x 2 = WP.x 2 := by
        have := congrArg (fun v => g⁻¹ • v) (hg 2)
        simpa using this.symm
      rw [hg2inv] at h
      have h' : g⁻¹ * m₀ * g ∈ fixingSubgroup H (Γ.neighborSet (WP.x 2)) := by
        simpa using h
      have heq : g⁻¹ * m₀ * g = a := by simp [m₀, mul_assoc]
      rw [heq] at h'
      rw [hx2] at h'
      simpa [F₀] using h'
    exact haNot haF
  exact ⟨m₀, hm₀Kernel, hm₀Soc, hm₀Pow, hm₀Not⟩

theorem exists_twoFix_of_claimA [Finite V] [Finite H] (hk : 2 ≤ k) (hm : 3 ≤ m)
    (hF : Nat.card F = (2 ^ k) ^ 2) (hS : QuadSetup H Γ k m F ut) (W : ClosedGoodPath H Γ)
    (hu : ut (W.x 0)) {h : H} (hH : h ∈ W.kernelAt 0) (h1 : h ∈ socleAt H Γ (W.x 1))
    (h2 : h ∈ socleAt H Γ (W.x 2))
    (hq : h ^ (2 ^ k - 1) ∈ fixingSubgroup H (Γ.neighborSet (W.x 2)))
    (hn : h ∉ fixingSubgroup H (Γ.neighborSet (W.x 2))) :
    ∃ (p : GPath Γ 5) (g : H), p.NoBack ∧ p 0 = W.x 1 ∧
      g ∈ fixingSubgroup H (Γ.neighborSet (p 0)) ⊓ GPath.stabPath (H := H) p ∧
      ∀ z, Γ.Adj (p 1) z → z ≠ p 0 → z ≠ p 2 → g • z ≠ z := by
  classical
  let F₂ : Subgroup H := fixingSubgroup H (Γ.neighborSet (W.x 2))
  let T₂ : Subgroup H := socTorus H Γ (W.x 2) (W.x 1) (W.x 3)
  have hLF := localFacts hk hm hF hS
  have hq2 : 2 ≤ 2 ^ k := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega : 1 ≤ k)
  have hx1not : ¬ ut (W.x 1) := (hS.adj (W.x 0) (W.x 1) (W.adj 0)).mp hu
  have hx2U : ut (W.x 2) := by
    by_contra hx2
    exact hx1not ((hS.adj (W.x 1) (W.x 2) (W.adj 1)).mpr hx2)
  have hstab1 : h • W.x 1 = W.x 1 := (ClosedGoodPath.mem_stab_iff.mp hH.2) 1
  have hstab2 : h • W.x 2 = W.x 2 := (ClosedGoodPath.mem_stab_iff.mp hH.2) 2
  have hstab3 : h • W.x 3 = W.x 3 := (ClosedGoodPath.mem_stab_iff.mp hH.2) 3
  have hhT₂ : h ∈ T₂ := by
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨h2, ?_⟩, ?_⟩
    · exact MulAction.mem_stabilizer_iff.mpr hstab1
    · exact MulAction.mem_stabilizer_iff.mpr hstab3
  have hnot : h ^ (2 ^ k + 1) ∉ F₂ := by
    intro hmem
    apply hn
    have hsq : h ^ 2 ∈ F₂ := by
      have hsplit : h ^ (2 ^ k + 1) = h ^ 2 * h ^ (2 ^ k - 1) := by
        rw [← pow_add]
        congr 1
        omega
      rw [hsplit] at hmem
      have := F₂.mul_mem hmem (F₂.inv_mem hq)
      simpa [mul_assoc] using this
    obtain ⟨m, hm⟩ :=
      dvd_trans (by norm_num : 2 ∣ 2) (pow_dvd_pow 2 (by omega : 1 ≤ k))
    have hqmem : h ^ (2 ^ k) ∈ F₂ := by
      rw [hm, pow_mul]
      exact F₂.pow_mem hsq m
    have hpow : h ^ (2 ^ k) = h ^ (2 ^ k - 1) * h := by
      conv_lhs => rw [show 2 ^ k = (2 ^ k - 1) + 1 by omega]
      rw [pow_succ]
    have hh : h = h ^ (2 ^ k) * (h ^ (2 ^ k - 1))⁻¹ := by
      rw [hpow]
      group
    rw [hh]
    exact F₂.mul_mem hqmem (F₂.inv_mem hq)
  have hfixonly : ∀ u, Γ.Adj (W.x 2) u → h • u = u → u = W.x 1 ∨ u = W.x 3 := by
    intro u hu2 hfu
    exact ((vertexFacts_of_isLocalU3 hk F hF (hS.kernel_le (W.x 2))
      (hS.u3 (W.x 2) hx2U)).2.2).fix_two (W.x 1) (W.x 3) (W.adj 1).symm (W.adj 2)
      (W.ne_add_two 1) h hhT₂ hnot u hu2 hfu
  let Ω₁ := {w : V // Γ.Adj (W.x 1) w}
  have h2tr : ∀ {a b c d : Ω₁}, a ≠ b → c ≠ d →
      ∃ g : ↥(localGroup H Γ (W.x 1)), g • a = c ∧ g • b = d :=
    MulAction.is_two_pretransitive_iff.mp (hS.l2 (W.x 1) hx1not).2.1
  obtain ⟨p₀, hp0, hp2⟩ := h2tr (a := ⟨W.x 0, (W.adj 0).symm⟩)
    (b := ⟨W.x 2, W.adj 1⟩) (c := ⟨W.x 2, W.adj 1⟩)
    (d := ⟨W.x 0, (W.adj 0).symm⟩)
    (fun hbad => W.ne_add_two 0 (congrArg Subtype.val hbad))
    (fun hbad => (W.ne_add_two 0).symm (congrArg Subtype.val hbad))
  have hp0' : (p₀.1 : Equiv.Perm Ω₁) ⟨W.x 0, (W.adj 0).symm⟩ =
      ⟨W.x 2, W.adj 1⟩ := by
    simpa [Subgroup.smul_def, Ω₁] using hp0
  have hp2' : (p₀.1 : Equiv.Perm Ω₁) ⟨W.x 2, W.adj 1⟩ =
      ⟨W.x 0, (W.adj 0).symm⟩ := by
    simpa [Subgroup.smul_def, Ω₁] using hp2
  have hp0range : p₀.1 ∈ (localPermHom (H := H) Γ (W.x 1)).range := p₀.2
  obtain ⟨σ, hσ⟩ := hp0range
  have hσ0 : (σ : H) • W.x 0 = W.x 2 := by
    have h := congrArg (fun e : Equiv.Perm Ω₁ => (e ⟨W.x 0, (W.adj 0).symm⟩).1) hσ
    rw [localPermHom_apply] at h
    exact h.trans (congrArg Subtype.val hp0')
  have hσ2 : (σ : H) • W.x 2 = W.x 0 := by
    have h := congrArg (fun e : Equiv.Perm Ω₁ => (e ⟨W.x 2, W.adj 1⟩).1) hσ
    rw [localPermHom_apply] at h
    exact h.trans (congrArg Subtype.val hp2')
  have hσ1 : (σ : H) • W.x 1 = W.x 1 := MulAction.mem_stabilizer_iff.mp σ.2
  let h' : H := (σ : H) * h * (σ : H)⁻¹
  have h'fix0 : h' • W.x 0 = W.x 0 := by
    have hσinv0 : (σ : H)⁻¹ • W.x 0 = W.x 2 := by
      have h := congrArg (fun v => (σ : H)⁻¹ • v) hσ2
      simpa using h.symm
    calc h' • W.x 0 = (σ : H) • (h • ((σ : H)⁻¹ • W.x 0)) := by
          change ((σ : H) * h * (σ : H)⁻¹) • W.x 0 =
            (σ : H) • (h • ((σ : H)⁻¹ • W.x 0))
          rw [mul_smul, mul_smul]
      _ = (σ : H) • (h • W.x 2) := by rw [hσinv0]
      _ = (σ : H) • W.x 2 := by rw [hstab2]
      _ = W.x 0 := hσ2
  have h'fix2 : h' • W.x 2 = W.x 2 := by
    have hσinv2 : (σ : H)⁻¹ • W.x 2 = W.x 0 := by
      have h := congrArg (fun v => (σ : H)⁻¹ • v) hσ0
      simpa using h.symm
    have hfix0 : h • W.x 0 = W.x 0 := (ClosedGoodPath.mem_stab_iff.mp hH.2) 0
    calc h' • W.x 2 = (σ : H) • (h • ((σ : H)⁻¹ • W.x 2)) := by
          change ((σ : H) * h * (σ : H)⁻¹) • W.x 2 =
            (σ : H) • (h • ((σ : H)⁻¹ • W.x 2))
          rw [mul_smul, mul_smul]
      _ = (σ : H) • (h • W.x 0) := by rw [hσinv2]
      _ = (σ : H) • W.x 0 := by rw [hfix0]
      _ = W.x 2 := hσ0
  have h'G1 : h' ∈ fixingSubgroup H (Γ.neighborSet (W.x 2)) := by
    have h := conj_mem_fixingSubgroup_neighborSet (σ : H) h (W.x 0) hH.1
    rwa [hσ0] at h
  have h'soc : h' ∈ socleAt H Γ (W.x 1) := by
    have hmap := socleAt_smul (H := H) (Γ := Γ) (σ : H) (W.x 1)
    rw [hσ1] at hmap
    rw [hmap]
    exact Subgroup.mem_map_of_mem _ h1
  let T : Subgroup H := socTorus H Γ (W.x 1) (W.x 0) (W.x 2)
  have hTmem : ∀ {t : H}, t ∈ T ↔
      t ∈ socleAt H Γ (W.x 1) ∧ t ∈ MulAction.stabilizer H (W.x 0) ∧
        t ∈ MulAction.stabilizer H (W.x 2) := by
    intro t
    change t ∈ (socleAt H Γ (W.x 1) ⊓ MulAction.stabilizer H (W.x 0)) ⊓
      MulAction.stabilizer H (W.x 2) ↔ _
    simp [Subgroup.mem_inf, and_assoc]
  have hTle : T ≤ MulAction.stabilizer H (W.x 1) := by
    intro t ht
    exact socleAt_le_stabilizer (hLF (W.x 1)).kernel_le (hTmem.mp ht).1
  have hhT : h ∈ T := hTmem.mpr ⟨h1,
    MulAction.mem_stabilizer_iff.mpr ((ClosedGoodPath.mem_stab_iff.mp hH.2) 0),
    MulAction.mem_stabilizer_iff.mpr hstab2⟩
  have hh'T : h' ∈ T := hTmem.mpr ⟨h'soc,
    MulAction.mem_stabilizer_iff.mpr h'fix0,
    MulAction.mem_stabilizer_iff.mpr h'fix2⟩
  obtain ⟨b, hbT, -, hbgen⟩ := (hLF (W.x 1)).torusGen (W.x 0) (W.x 2)
    (W.adj 0).symm (W.adj 1) (W.ne_add_two 0) T le_rfl le_sup_left
  let φ := localPermHom (H := H) Γ (W.x 1)
  have hmemC : ∀ {t : H} (ht : t ∈ T),
      φ ⟨t, hTle ht⟩ ∈ Subgroup.zpowers (φ ⟨b, hTle hbT⟩) := by
    intro t ht
    have hsup : t ∈ Subgroup.closure {b} ⊔ fixingSubgroup H (Γ.neighborSet (W.x 1)) :=
      hbgen ht
    rw [← Subgroup.zpowers_eq_closure b] at hsup
    have hzu : Subgroup.zpowers b ≤ MulAction.stabilizer H (W.x 1) := by
      rw [Subgroup.zpowers_le]
      exact hTle hbT
    have hnorm : Subgroup.zpowers b ≤
        Subgroup.normalizer (fixingSubgroup H (Γ.neighborSet (W.x 1)) : Set H) :=
      hzu.trans stabilizer_le_normalizer_fixingSubgroup
    change t ∈ (↑(Subgroup.zpowers b ⊔
      fixingSubgroup H (Γ.neighborSet (W.x 1))) : Set H) at hsup
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hnorm] at hsup
    rcases hsup with ⟨p, hp, k, hk, hpk⟩
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hp
    have hkφ : φ ⟨k, (hLF (W.x 1)).kernel_le hk⟩ = 1 := by
      ext w
      rw [Equiv.Perm.one_apply, localPermHom_apply]
      exact (mem_fixingSubgroup_iff H).mp hk w.1 w.2
    have ht_eq : (⟨t, hTle ht⟩ : ↥(MulAction.stabilizer H (W.x 1))) =
        (⟨p, hzu hp⟩ : ↥(MulAction.stabilizer H (W.x 1))) *
          ⟨k, (hLF (W.x 1)).kernel_le hk⟩ := Subtype.ext hpk.symm
    have hpbun : (⟨p, hzu hp⟩ : ↥(MulAction.stabilizer H (W.x 1))) =
        (⟨b, hTle hbT⟩ : ↥(MulAction.stabilizer H (W.x 1))) ^ n :=
      Subtype.ext hn.symm
    have hcalc : φ ⟨t, hTle ht⟩ = (φ ⟨b, hTle hbT⟩) ^ n := by
      calc φ ⟨t, hTle ht⟩ =
          φ ((⟨p, hzu hp⟩ : ↥(MulAction.stabilizer H (W.x 1))) *
            ⟨k, (hLF (W.x 1)).kernel_le hk⟩) := by rw [ht_eq]
        _ = φ ⟨p, hzu hp⟩ * φ ⟨k, (hLF (W.x 1)).kernel_le hk⟩ := map_mul _ _ _
        _ = φ ⟨p, hzu hp⟩ := by rw [hkφ, mul_one]
        _ = φ (⟨b, hTle hbT⟩ ^ n) := by rw [hpbun]
        _ = (φ ⟨b, hTle hbT⟩) ^ n := map_zpow φ ⟨b, hTle hbT⟩ n
    rw [hcalc]
    exact Subgroup.zpow_mem_zpowers (φ ⟨b, hTle hbT⟩) n
  have hhC : φ ⟨h, hTle hhT⟩ ∈ Subgroup.zpowers (φ ⟨b, hTle hbT⟩) := hmemC hhT
  have hh'C : φ ⟨h', hTle hh'T⟩ ∈ Subgroup.zpowers (φ ⟨b, hTle hbT⟩) := hmemC hh'T
  have hbun : (⟨h', hTle hh'T⟩ : ↥(MulAction.stabilizer H (W.x 1))) =
      σ * (⟨h, hTle hhT⟩ : ↥(MulAction.stabilizer H (W.x 1))) * σ⁻¹ := by
    ext
    simp [h', mul_assoc]
  have hord : orderOf (φ ⟨h, hTle hhT⟩) = orderOf (φ ⟨h', hTle hh'T⟩) := by
    have hconj : φ ⟨h', hTle hh'T⟩ =
        φ σ * φ ⟨h, hTle hhT⟩ * (φ σ)⁻¹ := by
      rw [hbun, map_mul, map_mul, map_inv]
    rw [hconj]
    simpa [MulAut.conj_apply] using
      ((MulAut.conj (φ σ)).orderOf_eq (φ ⟨h, hTle hhT⟩)).symm
  have hΩcard : Nat.card Ω₁ = 2 ^ m + 1 := (hS.l2 (W.x 1) hx1not).1
  haveI : Finite Ω₁ := Nat.finite_of_card_ne_zero (by rw [hΩcard]; exact Nat.succ_ne_zero _)
  haveI : Finite ↥(localGroup H Γ (W.x 1)) := Subtype.finite
  let C : Subgroup (Equiv.Perm Ω₁) := Subgroup.zpowers (φ ⟨b, hTle hbT⟩)
  let c₁ : ↥C := ⟨φ ⟨h, hTle hhT⟩, hhC⟩
  let c₂ : ↥C := ⟨φ ⟨h', hTle hh'T⟩, hh'C⟩
  have hCcard : Nat.card (Subgroup.zpowers c₁) = Nat.card (Subgroup.zpowers c₂) := by
    rw [Nat.card_zpowers, Nat.card_zpowers]
    calc orderOf c₁ = orderOf (φ ⟨h, hTle hhT⟩) := (Subgroup.orderOf_coe c₁).symm
      _ = orderOf (φ ⟨h', hTle hh'T⟩) := hord
      _ = orderOf c₂ := Subgroup.orderOf_coe c₂
  have hCeq : Subgroup.zpowers c₁ = Subgroup.zpowers c₂ :=
    IsCyclic.subgroup_eq_iff_card_eq.mpr hCcard
  have hc1mem : c₁ ∈ Subgroup.zpowers c₂ := by
    rw [← hCeq]
    exact Subgroup.mem_zpowers c₁
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hc1mem
  have hiφ : (φ ⟨h', hTle hh'T⟩) ^ i = φ ⟨h, hTle hhT⟩ := by
    have h := congrArg (fun z : ↥C => (z : Equiv.Perm Ω₁)) hi
    simpa [c₁, c₂] using h
  let w : H := h' ^ i * h⁻¹
  have hwstab1 : w ∈ MulAction.stabilizer H (W.x 1) :=
    (MulAction.stabilizer H (W.x 1)).mul_mem
      ((MulAction.stabilizer H (W.x 1)).zpow_mem (hTle hh'T) i)
      ((MulAction.stabilizer H (W.x 1)).inv_mem (hTle hhT))
  have hwφ : φ ⟨w, hwstab1⟩ = 1 := by
    have hbunw : (⟨w, hwstab1⟩ : ↥(MulAction.stabilizer H (W.x 1))) =
        (⟨h', hTle hh'T⟩ : ↥(MulAction.stabilizer H (W.x 1))) ^ i *
          (⟨h, hTle hhT⟩ : ↥(MulAction.stabilizer H (W.x 1)))⁻¹ := by
      ext
      simp [w]
    rw [hbunw, map_mul, map_zpow, map_inv, hiφ]
    group
  have hwG1 : w ∈ fixingSubgroup H (Γ.neighborSet (W.x 1)) := by
    have hker : (⟨w, hwstab1⟩ : ↥(MulAction.stabilizer H (W.x 1))) ∈ φ.ker := by
      rw [MonoidHom.mem_ker]
      exact hwφ
    rw [show φ.ker = (fixingSubgroup H (Γ.neighborSet (W.x 1))).subgroupOf
        (MulAction.stabilizer H (W.x 1)) from localPermHom_ker] at hker
    exact Subgroup.mem_subgroupOf.mp hker
  have hwstab2 : w ∈ MulAction.stabilizer H (W.x 2) := by
    rw [MulAction.mem_stabilizer_iff]
    exact (mem_fixingSubgroup_iff H).mp hwG1 (W.x 2) (W.adj 1)
  let φ₂ := localPermHom (H := H) Γ (W.x 2)
  have hhstab2 : h ∈ MulAction.stabilizer H (W.x 2) :=
    MulAction.mem_stabilizer_iff.mpr hstab2
  have hhinvstab2 : h⁻¹ ∈ MulAction.stabilizer H (W.x 2) :=
    (MulAction.stabilizer H (W.x 2)).inv_mem hhstab2
  have h'powstab2 : h' ^ i ∈ MulAction.stabilizer H (W.x 2) :=
    (MulAction.stabilizer H (W.x 2)).zpow_mem
      ((hLF (W.x 2)).kernel_le h'G1) i
  have h'powG1 : h' ^ i ∈ fixingSubgroup H (Γ.neighborSet (W.x 2)) :=
    (fixingSubgroup H (Γ.neighborSet (W.x 2))).zpow_mem h'G1 i
  have h'powφ₂ : φ₂ ⟨h' ^ i, h'powstab2⟩ = 1 := by
    ext u
    rw [Equiv.Perm.one_apply, localPermHom_apply]
    exact (mem_fixingSubgroup_iff H).mp h'powG1 u.1 u.2
  have hwφ₂ : φ₂ ⟨w, hwstab2⟩ = φ₂ ⟨h⁻¹, hhinvstab2⟩ := by
    have hbunw : (⟨w, hwstab2⟩ : ↥(MulAction.stabilizer H (W.x 2))) =
        (⟨h' ^ i, h'powstab2⟩ : ↥(MulAction.stabilizer H (W.x 2))) *
          ⟨h⁻¹, hhinvstab2⟩ := by
      ext
      simp [w]
    rw [hbunw, map_mul, h'powφ₂, one_mul]
  have hT₂le : T₂ ≤ MulAction.stabilizer H (W.x 2) := by
    intro t ht
    exact socleAt_le_stabilizer (hLF (W.x 2)).kernel_le ht.1.1
  have hφh_odd : Odd (orderOf (φ₂ ⟨h, hT₂le hhT₂⟩)) := by
    have hrel := Subgroup.relIndex_subgroupOf (H := F₂) (K := T₂)
      (L := MulAction.stabilizer H (W.x 2)) hT₂le
    have hcard : Nat.card ((T₂.subgroupOf (MulAction.stabilizer H (W.x 2))).map φ₂) =
        F₂.relIndex T₂ := by
      calc Nat.card ((T₂.subgroupOf (MulAction.stabilizer H (W.x 2))).map φ₂) =
          φ₂.ker.relIndex (T₂.subgroupOf (MulAction.stabilizer H (W.x 2))) :=
            (Subgroup.relIndex_ker _ φ₂).symm
        _ = (F₂.subgroupOf (MulAction.stabilizer H (W.x 2))).relIndex
              (T₂.subgroupOf (MulAction.stabilizer H (W.x 2))) := by
            rw [show φ₂.ker = (F₂.subgroupOf (MulAction.stabilizer H (W.x 2))) from
              localPermHom_ker]
        _ = F₂.relIndex T₂ := hrel
    have hmem : φ₂ ⟨h, hT₂le hhT₂⟩ ∈
        (T₂.subgroupOf (MulAction.stabilizer H (W.x 2))).map φ₂ := by
      refine Subgroup.mem_map_of_mem φ₂ ?_
      rw [Subgroup.mem_subgroupOf]
      exact hhT₂
    have hoddT : Odd (F₂.relIndex T₂) :=
      (hLF (W.x 2)).torusOdd (W.x 1) (W.x 3) (W.adj 1).symm (W.adj 2)
        (W.ne_add_two 1)
    exact Odd.of_dvd_nat (by rw [hcard]; exact hoddT)
      (Subgroup.orderOf_dvd_natCard _ hmem)
  have hφhinv_odd : Odd (orderOf (φ₂ ⟨h⁻¹, hhinvstab2⟩)) := by
    have hbun : (⟨h⁻¹, hhinvstab2⟩ : ↥(MulAction.stabilizer H (W.x 2))) =
        (⟨h, hT₂le hhT₂⟩ : ↥(MulAction.stabilizer H (W.x 2)))⁻¹ := by
      ext
      simp
    rw [hbun, map_inv]
    simpa [orderOf_inv] using hφh_odd
  have hwφ₂_odd : Odd (orderOf (φ₂ ⟨w, hwstab2⟩)) := by
    rw [hwφ₂]
    exact hφhinv_odd
  obtain ⟨n, hnodd, hnφ⟩ := exists_odd_pow_map_eq φ₂ ⟨w, hwstab2⟩ hwφ₂_odd
  let g₀ : H := w ^ n
  have hg0G1 : g₀ ∈ fixingSubgroup H (Γ.neighborSet (W.x 1)) :=
    Subgroup.pow_mem _ hwG1 n
  have hg0odd : Odd (orderOf g₀) := by
    change Odd (orderOf ((⟨w, hwstab2⟩ ^ n :
      ↥(MulAction.stabilizer H (W.x 2))) : H))
    rwa [Subgroup.orderOf_coe]
  have hg0stab2 : g₀ ∈ MulAction.stabilizer H (W.x 2) := by
    rw [MulAction.mem_stabilizer_iff]
    exact (mem_fixingSubgroup_iff H).mp hg0G1 (W.x 2) (W.adj 1)
  have hg0x2 : g₀ • W.x 2 = W.x 2 :=
    MulAction.mem_stabilizer_iff.mp hg0stab2
  have hg0φw : φ₂ ⟨g₀, hg0stab2⟩ = φ₂ ⟨w, hwstab2⟩ := by
    have hbun : (⟨g₀, hg0stab2⟩ : ↥(MulAction.stabilizer H (W.x 2))) =
        (⟨w, hwstab2⟩ : ↥(MulAction.stabilizer H (W.x 2))) ^ n := by
      ext
      simp [g₀]
    rw [hbun]
    exact hnφ
  have hw_on_x3 : w • W.x 3 = h⁻¹ • W.x 3 := by
    have h := congrArg (fun e : Equiv.Perm {u : V // Γ.Adj (W.x 2) u} =>
      (e ⟨W.x 3, W.adj 2⟩).1) hwφ₂
    rw [localPermHom_apply, localPermHom_apply] at h
    exact h
  have hg0x3 : g₀ • W.x 3 = W.x 3 := by
    have hperm := congrArg (fun e : Equiv.Perm {u : V // Γ.Adj (W.x 2) u} =>
      (e ⟨W.x 3, W.adj 2⟩).1) hg0φw
    rw [localPermHom_apply, localPermHom_apply] at hperm
    have hw3 : w • W.x 3 = W.x 3 := by
      rw [hw_on_x3]
      have hinv := congrArg (fun v => h⁻¹ • v) hstab3
      simpa using hinv.symm
    exact hperm.trans hw3
  have hKle_of : ∀ {z₁ z₂ : V}, g₀ • z₁ = z₁ → g₀ • z₂ = z₂ →
      Subgroup.zpowers g₀ ≤ MulAction.stabilizer H z₁ ⊓ MulAction.stabilizer H z₂ := by
    intro z₁ z₂ h₁ h₂
    rw [Subgroup.zpowers_le]
    exact Subgroup.mem_inf.mpr
      ⟨MulAction.mem_stabilizer_iff.mpr h₁, MulAction.mem_stabilizer_iff.mpr h₂⟩
  have hKodd_of : ∀ z, Odd ((fixingSubgroup H (Γ.neighborSet z)).relIndex
      (Subgroup.zpowers g₀)) := by
    intro z
    exact Odd.of_dvd_nat (by rw [Nat.card_zpowers]; exact hg0odd)
      (Subgroup.relIndex_dvd_card _ _)
  obtain ⟨u₃, hu₃adj, hu₃ne, hu₃fix⟩ :=
    (hLF (W.x 3)).oddFix (W.x 2) (W.adj 2).symm (Subgroup.zpowers g₀)
      (hKle_of hg0x3 hg0x2) (hKodd_of (W.x 3))
  have hu₃g0 : g₀ • u₃ = u₃ := hu₃fix g₀ (Subgroup.mem_zpowers g₀)
  obtain ⟨u₄, hu₄adj, hu₄ne, hu₄fix⟩ :=
    (hLF u₃).oddFix (W.x 3) hu₃adj.symm (Subgroup.zpowers g₀)
      (hKle_of hu₃g0 hg0x3) (hKodd_of u₃)
  have hu₄g0 : g₀ • u₄ = u₄ := hu₄fix g₀ (Subgroup.mem_zpowers g₀)
  obtain ⟨u₅, hu₅adj, hu₅ne, hu₅fix⟩ :=
    (hLF u₄).oddFix u₃ hu₄adj.symm (Subgroup.zpowers g₀)
      (hKle_of hu₄g0 hu₃g0) (hKodd_of u₄)
  let p4 : GPath Γ 4 := path5 (W.x 1) (W.x 2) (W.x 3) u₃ u₄
    (W.adj 1) (W.adj 2) hu₃adj hu₄adj
  have hp4nb : p4.NoBack :=
    path5_noBack (W.adj 1) (W.adj 2) hu₃adj hu₄adj
      (W.ne_add_two 1) hu₃ne.symm hu₄ne.symm
  let p : GPath Γ 5 := p4.snoc u₅ hu₅adj
  have hpnb : p.NoBack := GPath.noBack_snoc hp4nb hu₅adj (fun _ => hu₅ne)
  have hpv : p 0 = W.x 1 ∧ p 1 = W.x 2 ∧ p 2 = W.x 3 ∧ p 3 = u₃ ∧
      p 4 = u₄ ∧ p 5 = u₅ := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [p, p4, path5, GPath.snoc_of_le, GPath.snoc_last]
  obtain ⟨hp0, hp1, hp2, hp3, hp4, hp5⟩ := hpv
  have hgp : g₀ ∈ GPath.stabPath (H := H) p := by
    rw [GPath.mem_stabPath_iff]
    intro j hj
    interval_cases j
    · rw [hp0]
      exact MulAction.mem_stabilizer_iff.mp ((hLF (W.x 1)).kernel_le hg0G1)
    · rw [hp1]
      exact hg0x2
    · rw [hp2]
      exact hg0x3
    · rw [hp3]
      exact hu₃g0
    · rw [hp4]
      exact hu₄g0
    · rw [hp5]
      exact hu₅fix g₀ (Subgroup.mem_zpowers g₀)
  refine ⟨p, g₀, hpnb, hp0, ?_, ?_⟩
  · exact Subgroup.mem_inf.mpr ⟨by rwa [hp0], hgp⟩
  · intro z hz hz0 hz2 hfix
    have hz' : Γ.Adj (W.x 2) z := by rwa [hp1] at hz
    have hg0z : g₀ • z = w • z := by
      have h := congrArg (fun e : Equiv.Perm {u : V // Γ.Adj (W.x 2) u} =>
        (e ⟨z, hz'⟩).1) hg0φw
      rw [localPermHom_apply, localPermHom_apply] at h
      exact h
    have hwz : w • z = h⁻¹ • z := by
      have h := congrArg (fun e : Equiv.Perm {u : V // Γ.Adj (W.x 2) u} =>
        (e ⟨z, hz'⟩).1) hwφ₂
      rw [localPermHom_apply, localPermHom_apply] at h
      exact h
    have hhinv : h⁻¹ • z = z := by
      rw [hg0z, hwz] at hfix
      exact hfix
    have hhz : h • z = z := by
      have h := congrArg (fun v => h • v) hhinv
      simpa using h.symm
    rcases hfixonly z hz' hhz with hzx1 | hzx3
    · exact hz0 (hzx1.trans hp0.symm)
    · exact hz2 (hzx3.trans hp2.symm)
end QuadSetup

end CFSG.Quasithin.Stroth.WeissDelta

end
