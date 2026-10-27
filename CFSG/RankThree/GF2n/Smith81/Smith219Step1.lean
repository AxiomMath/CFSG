module

public import CFSG.RankThree.GF2n.Smith81.OrthStmt
public import CFSG.RankThree.GF2n.Smith81.LinStmt

public section

namespace CFSG.RankThree.GF2n.Smith81.Smith219Step1

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80

variable {G : Type} [Group G] [Finite G] {M Q Z : Subgroup G}

@[expose] def CosetUnique (M Q Z : Subgroup G) (z : G) : Prop :=
  ∀ x : G, x ∈ M → x ∉ Q → IsConj z x → ∀ c ∈ Z, IsConj z (x * c) → c = 1

theorem cosetUnique_of_inter {z : G}
    (h : ∀ x : G, x ∈ M → x ∉ Q → IsConj z x → conjClassSet z ∩ cosetSet x Z = {x}) :
    CosetUnique M Q Z z := by
  intro x hxM hxQ hxc c hc hxc'
  have hmem : x * c ∈ conjClassSet z ∩ cosetSet x Z := ⟨hxc', ⟨c, hc, rfl⟩⟩
  rw [h x hxM hxQ hxc] at hmem
  have : x * c = x := hmem
  simpa using this

theorem commute_Z_of_mem_M (H : StrothHyp M Q Z) {z f e : G} (h12 : CosetUnique M Q Z z)
    (hfM : f ∈ M) (hf : IsConj z f) (he : e ∈ Z) : Commute e f := by
  by_cases hfQ : f ∈ Q
  · exact Z_central H he hfQ
  · have hfN : f ∈ Subgroup.normalizer (Z : Set G) := by
      rw [H.normalizer_Z.1]; exact hfM
    have hc : f⁻¹ * e * f ∈ Z := by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem hfN) e).mp he
      simpa using this
    have h1 := h12 f hfM hfQ hf (f⁻¹ * e * f * e⁻¹) (mul_mem hc (inv_mem he)) (by
      rw [show f * (f⁻¹ * e * f * e⁻¹) = e * f * e⁻¹ by group]
      exact hf.trans (isConj_iff.mpr ⟨e, rfl⟩))
    calc e * f = (f * (f⁻¹ * e * f * e⁻¹)) * e := by group
      _ = f * e := by rw [h1, mul_one]

theorem rootSet_eq_Z_sharp_of_212 (H : StrothHyp M Q Z) {z : G} (hz : z ∈ Z) (hz1 : z ≠ 1)
    (h12 : CosetUnique M Q Z z) :
    CFSG.Timmesfeld.rootSet (CFSG.Timmesfeld.CorB.cls z) z = {e | e ∈ Z ∧ e ≠ 1} := by
  ext e
  constructor
  · rintro ⟨heD, hcomm⟩
    have he1 : e ≠ 1 := by
      intro h
      have : IsConj z 1 := h ▸ heD
      exact hz1 (isConj_one_left.mp this)
    refine ⟨?_, he1⟩
    have hQc : Q ≤ Subgroup.centralizer ({e} : Set G) := by
      rw [H.gen]
      refine iSup₂_le fun g hgQ => ?_
      intro w hw
      rw [Subgroup.mem_centralizer_singleton_iff]
      by_cases hw1 : w = 1
      · rw [hw1]; simp
      · have hwQ : w ∈ Q := hgQ hw
        have hw' : g⁻¹ * w * g ∈ Z := mem_conjSubgroup.mp hw
        have hw1' : g⁻¹ * w * g ≠ 1 := by
          intro h
          apply hw1
          have : w = g * (g⁻¹ * w * g) * g⁻¹ := by group
          rw [this, h]; group
        obtain ⟨m, -, hm⟩ := Z_isConj H hz hz1 hw' hw1'
        have hwD : w ∈ CFSG.Timmesfeld.CorB.cls z := by
          refine isConj_iff.mpr ⟨g * m, ?_⟩
          calc g * m * z * (g * m)⁻¹ = g * (m * z * m⁻¹) * g⁻¹ := by group
            _ = w := by rw [hm]; group
        have hzw : Commute z w := (Z_central H hz hwQ : z * w = w * z)
        exact ((hcomm w hwD).2 hzw).symm.eq
    rw [← H.centralizer_Q]
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    exact Subgroup.mem_centralizer_singleton_iff.mp (hQc hf)
  · rintro ⟨heZ, he1⟩
    obtain ⟨m, -, hm⟩ := Z_isConj H hz hz1 heZ he1
    refine ⟨isConj_iff.mpr ⟨m, hm⟩, fun f hf => ?_⟩
    have hfc : IsConj z f := hf
    constructor
    · intro hef
      have hfM : f ∈ M := mem_M_of_commute_Z H heZ he1 hef.symm.eq
      exact commute_Z_of_mem_M H h12 hfM hfc hz
    · intro hzf
      have hfM : f ∈ M := mem_M_of_commute_Z H hz hz1 hzf.symm.eq
      exact commute_Z_of_mem_M H h12 hfM hfc heZ

theorem rootGroup_eq_Z_of_212 (H : StrothHyp M Q Z) {z : G} (hz : z ∈ Z) (hz1 : z ≠ 1)
    (h12 : CosetUnique M Q Z z) :
    CFSG.Timmesfeld.rootGroup (CFSG.Timmesfeld.CorB.cls z) z = Z := by
  rw [CFSG.Timmesfeld.rootGroup, rootSet_eq_Z_sharp_of_212 H hz hz1 h12]
  apply le_antisymm
  · rw [Subgroup.closure_le]
    exact fun e he => he.1
  · intro x hx
    by_cases hx1 : x = 1
    · rw [hx1]; exact Subgroup.one_mem _
    · exact Subgroup.subset_closure ⟨hx, hx1⟩

theorem rootGroup_eq_Z_orth (h212 : Smith212OrthCoreStatement) {B : Subgroup G}
    (hc : SmithOrthCfg M Q Z B) {z : G} (hz : z ∈ Z) (hz1 : z ≠ 1) :
    CFSG.Timmesfeld.rootGroup (CFSG.Timmesfeld.CorB.cls z) z = Z :=
  rootGroup_eq_Z_of_212 hc.ctx.hyp hz hz1 (cosetUnique_of_inter fun x hxM hxQ hxc =>
    (h212 G M Q Z B hc z hz hz1 x hxM hxQ hxc).1)

theorem rootGroup_eq_Z_lin {B V₁ V₂ : Subgroup G} (H : StrothHyp M Q Z)
    (h212 : Lin212Prop M Q Z B V₁ V₂) {z : G} (hz : z ∈ Z) (hz1 : z ≠ 1) :
    CFSG.Timmesfeld.rootGroup (CFSG.Timmesfeld.CorB.cls z) z = Z := by
  refine rootGroup_eq_Z_of_212 H hz hz1 fun x hxM hxQ hxc c hc hxc' => ?_
  obtain ⟨X, hX, hxX⟩ := exists_isZConjugate_mem hz hxc
  have hx1 : x ≠ 1 := fun h => hxQ (h ▸ Q.one_mem)
  have hsit : Sit M Q Z X x := ⟨H, hX, hxX, hx1, hxM, hxQ⟩
  obtain ⟨g, hg⟩ := isConj_iff.mp hxc'
  exact (h212 X x hsit).2.2.2.1 c hc ⟨g, z, hz, hz1, hg.symm⟩

end CFSG.RankThree.GF2n.Smith81.Smith219Step1
