module

public import CFSG.LocalAnalysis.StandardType.GGLatRootBridge
import CFSG.LieType.Chevalley.LangStronglyOrthogonalCommute
import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneClassD4Torus
import CFSG.LieType.Steinberg.Minuscule.ChevExtras
import CFSG.LieType.Steinberg.TwistedE6.Roots
import CFSG.LieType.Steinberg.Adjoint.Presentation
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate117
public import Certificates.Certificate120

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint
open scoped commutatorElement

section RootGroups

private theorem not_isRoot_nsmul_sub_nsmul {τ : Tag} {α β : Fin τ.rank → ℤ}
    (hα : IsRoot τ α) (hβ : IsRoot τ β) (h0 : iform α β = 0)
    (hm : ¬ IsRoot τ (α - β)) {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    ¬ IsRoot τ (a • α - b • β) := by
  have h0' : iform α (-β) = 0 := by
    rw [CFSG.LieType.Chevalley.iform_neg_right, h0, neg_zero]
  have hm' : ¬ IsRoot τ (α + -β) := by rwa [sub_eq_add_neg] at hm
  have h := CFSG.LieType.Chevalley.not_isRoot_nsmul_add_nsmul hα
    (CFSG.LieType.Steinberg.TagRoots.isRoot_neg hβ) h0' hm' ha hb
  simpa only [sub_eq_add_neg, smul_neg] using h

private theorem stronglyOrth_not_root_pos_comb {τ : Tag} {α β : Fin τ.rank → ℤ}
    (hα : IsRoot τ α) (hβ : IsRoot τ β) (hne : α ≠ β) (hne' : α ≠ -β)
    (hadd : ¬ IsRoot τ (α + β)) (hsub : ¬ IsRoot τ (α - β))
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    ¬ IsRoot τ (a • α + b • β) ∧ ¬ IsRoot τ (a • α - b • β) := by
  have h0 := CFSG.SeitzReduction.iform_eq_zero_of_not_isRoot_add_sub hα hβ hne hne' hadd hsub
  exact ⟨CFSG.LieType.Chevalley.not_isRoot_nsmul_add_nsmul hα hβ h0 hadd ha hb,
    not_isRoot_nsmul_sub_nsmul hα hβ h0 hsub ha hb⟩

private theorem rootGroup_commute_of_chevalleyExtras {K : Type*} [Group K]
    (D : UniversalRootDatum K) {k : Type*} [Field k]
    {x : (Fin D.rank → ℤ) → k → K}
    {C : (Fin D.rank → ℤ) → (Fin D.rank → ℤ) → ℕ × ℕ → ℤ}
    {O : CFSG.LieType.Steinberg.CommOrder
      (CFSG.LieType.Steinberg.RootSystem.ofCartan D.isFiniteType D.divisible)}
    (hE : CFSG.LieType.Steinberg.ChevalleyExtras D k x C O)
    {α β : Fin D.rank → ℤ} (hα : α ∈ D.roots) (hβ : β ∈ D.roots) (hab : α + β ≠ 0)
    (hempty : ∀ a b : ℕ, 0 < a → 0 < b → a • α + b • β ∉ D.roots) :
    ∀ a ∈ D.rootGroup α, ∀ b ∈ D.rootGroup β, a * b = b * a := by
  have hnil : O.list α β = [] := by
    rw [List.eq_nil_iff_forall_not_mem]
    intro p hp
    obtain ⟨h1, h2, h3⟩ := (O.mem_iff α hα β hβ hab p).1 hp
    exact hempty p.1 p.2 h1 h2 h3
  have hcomm : ∀ c d : k, x α c * x β d = x β d * x α c := by
    intro c d
    have h := hE.comm α hα β hβ hab c d
    rw [hnil, List.map_nil, List.prod_nil] at h
    exact commutatorElement_eq_one_iff_mul_comm.mp h
  intro a ha b hb
  obtain ⟨c, hc⟩ := ((hE.param α hα).1 a).1 ha
  obtain ⟨d, hd⟩ := ((hE.param β hβ).1 b).1 hb
  rw [← hc, ← hd]
  exact hcomm c d

private theorem e6Datum_rootGroup_commute (k : Type*) [Field k]
    {x y : Fin (Tag.rank .E6) → ℤ} (hx : IsRoot .E6 x) (hy : IsRoot .E6 y)
    (hne : x ≠ y) (hne' : x ≠ -y) (hadd : ¬ IsRoot .E6 (x + y))
    (hsub : ¬ IsRoot .E6 (x - y)) :
    ∀ u ∈ (CFSG.LieType.Steinberg.Minuscule.e6Datum k).rootGroup x,
      ∀ v ∈ (CFSG.LieType.Steinberg.Minuscule.e6Datum k).rootGroup y, u * v = v * u := by
  obtain ⟨O⟩ := CFSG.LieType.Steinberg.nonempty_commOrder_ofCartan
    (CFSG.LieType.Steinberg.Minuscule.e6Datum k).isFiniteType
    (Dv := (CFSG.LieType.Steinberg.Minuscule.e6Datum k).divisible) rfl
  have hC := CFSG.LieType.Steinberg.Minuscule.e6Data_valid.commutatorFormula_commC k
    CFSG.LieType.Steinberg.Minuscule.posDef_cartan_E6 _
    (CFSG.LieType.Steinberg.Minuscule.roots_eq
      CFSG.LieType.Steinberg.Minuscule.isFiniteType_cartan_E6) O
  have hE := CFSG.LieType.Steinberg.Minuscule.e6_chevalleyExtras k O _ hC
  refine rootGroup_commute_of_chevalleyExtras (CFSG.LieType.Steinberg.Minuscule.e6Datum k) hE
    ((CFSG.LieType.Steinberg.Minuscule.e6Data_valid.mem_minDatum_roots
      CFSG.LieType.Steinberg.Minuscule.isFiniteType_cartan_E6 k).2 hx)
    ((CFSG.LieType.Steinberg.Minuscule.e6Data_valid.mem_minDatum_roots
      CFSG.LieType.Steinberg.Minuscule.isFiniteType_cartan_E6 k).2 hy) ?_ ?_
  · exact fun h => hne' (add_eq_zero_iff_eq_neg.mp h)
  · intro a b ha hb hmem
    exact (stronglyOrth_not_root_pos_comb hx hy hne hne' hadd hsub ha hb).1
      ((CFSG.LieType.Steinberg.Minuscule.e6Data_valid.mem_minDatum_roots
        CFSG.LieType.Steinberg.Minuscule.isFiniteType_cartan_E6 k).1 hmem)

private theorem e7Datum_rootGroup_commute (k : Type*) [Field k]
    {x y : Fin (Tag.rank .E7) → ℤ} (hx : IsRoot .E7 x) (hy : IsRoot .E7 y)
    (hne : x ≠ y) (hne' : x ≠ -y) (hadd : ¬ IsRoot .E7 (x + y))
    (hsub : ¬ IsRoot .E7 (x - y)) :
    ∀ u ∈ (CFSG.LieType.Steinberg.Minuscule.e7Datum k).rootGroup x,
      ∀ v ∈ (CFSG.LieType.Steinberg.Minuscule.e7Datum k).rootGroup y, u * v = v * u := by
  obtain ⟨O⟩ := CFSG.LieType.Steinberg.nonempty_commOrder_ofCartan
    (CFSG.LieType.Steinberg.Minuscule.e7Datum k).isFiniteType
    (Dv := (CFSG.LieType.Steinberg.Minuscule.e7Datum k).divisible) rfl
  have hC := CFSG.LieType.Steinberg.Minuscule.e7Data_valid.commutatorFormula_commC k
    CFSG.LieType.Steinberg.Minuscule.posDef_cartan_E7 _
    (CFSG.LieType.Steinberg.Minuscule.roots_eq
      CFSG.LieType.Steinberg.Minuscule.isFiniteType_cartan_E7) O
  have hE := CFSG.LieType.Steinberg.Minuscule.e7_chevalleyExtras k O _ hC
  refine rootGroup_commute_of_chevalleyExtras (CFSG.LieType.Steinberg.Minuscule.e7Datum k) hE
    ((CFSG.LieType.Steinberg.Minuscule.e7Data_valid.mem_minDatum_roots
      CFSG.LieType.Steinberg.Minuscule.isFiniteType_cartan_E7 k).2 hx)
    ((CFSG.LieType.Steinberg.Minuscule.e7Data_valid.mem_minDatum_roots
      CFSG.LieType.Steinberg.Minuscule.isFiniteType_cartan_E7 k).2 hy) ?_ ?_
  · exact fun h => hne' (add_eq_zero_iff_eq_neg.mp h)
  · intro a b ha hb hmem
    exact (stronglyOrth_not_root_pos_comb hx hy hne hne' hadd hsub ha hb).1
      ((CFSG.LieType.Steinberg.Minuscule.e7Data_valid.mem_minDatum_roots
        CFSG.LieType.Steinberg.Minuscule.isFiniteType_cartan_E7 k).1 hmem)

private theorem twistedRootSubgroup_commute {G : Type*} [Group G]
    {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : Type*} [Fintype κ] [DecidableEq κ]
    (Φ : Set (ι → ℤ)) (o : ι → κ) (X : (ι → ℤ) → Subgroup G) (σ : G →* G)
    {α β : κ → ℤ}
    (hbase : ∀ x ∈ Φ, ∀ y ∈ Φ,
      (∃ c : ℕ, 0 < c ∧ CFSG.LieType.Steinberg.orbitSum o x = c • α) →
      (∃ c' : ℕ, 0 < c' ∧ CFSG.LieType.Steinberg.orbitSum o y = c' • β) →
      ∀ u ∈ X x, ∀ v ∈ X y, u * v = v * u) :
    ∀ a ∈ CFSG.LieType.Steinberg.twistedRootSubgroup Φ o X σ α,
      ∀ b ∈ CFSG.LieType.Steinberg.twistedRootSubgroup Φ o X σ β, a * b = b * a := by
  have hA : (⨆ x ∈ Φ, ⨆ (_ : ∃ c : ℕ, 0 < c ∧ CFSG.LieType.Steinberg.orbitSum o x = c • α),
        X x : Subgroup G) ≤ Subgroup.centralizer
      ((⨆ y ∈ Φ, ⨆ (_ : ∃ c : ℕ, 0 < c ∧ CFSG.LieType.Steinberg.orbitSum o y = c • β),
        X y) : Subgroup G) := by
    refine iSup_le fun x => iSup_le fun hx => iSup_le fun hpx => ?_
    rw [Subgroup.le_centralizer_iff]
    refine iSup_le fun y => iSup_le fun hy => iSup_le fun hpy => ?_
    rw [Subgroup.le_centralizer_iff]
    intro u hu
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact (hbase x hx y hy hpx hpy u hu v hv).symm
  intro a ha b hb
  have haA : a ∈ (⨆ x ∈ Φ,
      ⨆ (_ : ∃ c : ℕ, 0 < c ∧ CFSG.LieType.Steinberg.orbitSum o x = c • α), X x) :=
    (Subgroup.mem_inf.mp ha).1
  have hbA : b ∈ (⨆ y ∈ Φ,
      ⨆ (_ : ∃ c : ℕ, 0 < c ∧ CFSG.LieType.Steinberg.orbitSum o y = c • β), X y) :=
    (Subgroup.mem_inf.mp hb).1
  exact (Subgroup.mem_centralizer_iff.mp (hA haA) b hbA).symm

@[expose] def GGRootGroupsCommute : Prop :=
  ∀ (t : StatedLieTag) (n f : ℕ), GGExcFive t → ∀ α ∈ (ggU t n f).D.roots,
    ∀ β ∈ (ggU t n f).D.roots, StronglyOrth (ggU t n f).D α β →
      ∀ a ∈ (ggU t n f).D.rootGroup α, ∀ b ∈ (ggU t n f).D.rootGroup β, a * b = b * a

section ExcCertRootGroups

theorem ggRootGroupsCommute_holds : GGRootGroupsCommute := by
  intro t n f ht
  rcases ht with rfl | rfl | rfl | rfl | rfl
  ·
    intro α hα β hβ hso a ha b hb
    have hIα : IsRoot .F4 α := (mem_rootFinset (τ := .F4)).mp ((mem_roots_F4 n f α).mp hα)
    have hIβ : IsRoot .F4 β := (mem_rootFinset (τ := .F4)).mp ((mem_roots_F4 n f β).mp hβ)
    have hadd : ¬ IsRoot .F4 (α + β) := fun h =>
      hso.2.2.1 ((mem_roots_F4 n f _).mpr ((mem_rootFinset (τ := .F4)).mpr h))
    have hsub : ¬ IsRoot .F4 (α - β) := fun h =>
      hso.2.2.2 ((mem_roots_F4 n f _).mpr ((mem_rootFinset (τ := .F4)).mpr h))
    obtain ⟨O⟩ := CFSG.LieType.Steinberg.nonempty_commOrder_ofCartan
      (CFSG.LieType.Steinberg.Adjoint.f4Datum (GaloisField 2 f)).isFiniteType
      (Dv := (CFSG.LieType.Steinberg.Adjoint.f4Datum (GaloisField 2 f)).divisible) rfl
    obtain ⟨C, hC⟩ := CFSG.LieType.Steinberg.Adjoint.f4_commutatorFormula (GaloisField 2 f) O
    refine rootGroup_commute_of_chevalleyExtras (ggU .F4 n f).D
      (CFSG.LieType.Steinberg.Adjoint.f4_chevalleyExtras (GaloisField 2 f) O C hC.2)
      hα hβ ?_ ?_ a ha b hb
    · exact fun h => hso.2.1 (add_eq_zero_iff_eq_neg.mp h)
    · intro a' b' ha' hb' hmem
      exact (stronglyOrth_not_root_pos_comb hIα hIβ hso.1 hso.2.1 hadd hsub ha' hb').1
        ((mem_rootFinset (τ := .F4)).mp ((mem_roots_F4 n f _).mp hmem))
  ·
    intro α hα β hβ hso a ha b hb
    have hIα : IsRoot .E6 α := (mem_rootFinset (τ := .E6)).mp ((mem_roots_E6 n f α).mp hα)
    have hIβ : IsRoot .E6 β := (mem_rootFinset (τ := .E6)).mp ((mem_roots_E6 n f β).mp hβ)
    have hadd : ¬ IsRoot .E6 (α + β) := fun h =>
      hso.2.2.1 ((mem_roots_E6 n f _).mpr ((mem_rootFinset (τ := .E6)).mpr h))
    have hsub : ¬ IsRoot .E6 (α - β) := fun h =>
      hso.2.2.2 ((mem_roots_E6 n f _).mpr ((mem_rootFinset (τ := .E6)).mpr h))
    exact e6Datum_rootGroup_commute (GaloisField 2 f) hIα hIβ hso.1 hso.2.1 hadd hsub a ha b hb
  ·
    intro α hα β hβ hso a ha b hb
    have hIα : IsRoot .E7 α := (mem_rootFinset (τ := .E7)).mp ((mem_roots_E7 n f α).mp hα)
    have hIβ : IsRoot .E7 β := (mem_rootFinset (τ := .E7)).mp ((mem_roots_E7 n f β).mp hβ)
    have hadd : ¬ IsRoot .E7 (α + β) := fun h =>
      hso.2.2.1 ((mem_roots_E7 n f _).mpr ((mem_rootFinset (τ := .E7)).mpr h))
    have hsub : ¬ IsRoot .E7 (α - β) := fun h =>
      hso.2.2.2 ((mem_roots_E7 n f _).mpr ((mem_rootFinset (τ := .E7)).mpr h))
    exact e7Datum_rootGroup_commute (GaloisField 2 f) hIα hIβ hso.1 hso.2.1 hadd hsub a ha b hb
  ·
    intro α hα β hβ hso a ha b hb
    have hIα : IsRoot .E8 α := (mem_rootFinset (τ := .E8)).mp ((mem_roots_E8 n f α).mp hα)
    have hIβ : IsRoot .E8 β := (mem_rootFinset (τ := .E8)).mp ((mem_roots_E8 n f β).mp hβ)
    have hadd : ¬ IsRoot .E8 (α + β) := fun h =>
      hso.2.2.1 ((mem_roots_E8 n f _).mpr ((mem_rootFinset (τ := .E8)).mpr h))
    have hsub : ¬ IsRoot .E8 (α - β) := fun h =>
      hso.2.2.2 ((mem_roots_E8 n f _).mpr ((mem_rootFinset (τ := .E8)).mpr h))
    obtain ⟨O⟩ := CFSG.LieType.Steinberg.nonempty_commOrder_ofCartan
      (CFSG.LieType.Steinberg.Adjoint.e8Datum (GaloisField 2 f)).isFiniteType
      (Dv := (CFSG.LieType.Steinberg.Adjoint.e8Datum (GaloisField 2 f)).divisible) rfl
    obtain ⟨C, hC⟩ := CFSG.LieType.Steinberg.Adjoint.e8_commutatorFormula (GaloisField 2 f) O
    refine rootGroup_commute_of_chevalleyExtras (ggU .E8 n f).D
      (CFSG.LieType.Steinberg.Adjoint.e8_chevalleyExtras (GaloisField 2 f) O C hC.2)
      hα hβ ?_ ?_ a ha b hb
    · exact fun h => hso.2.1 (add_eq_zero_iff_eq_neg.mp h)
    · intro a' b' ha' hb' hmem
      exact (stronglyOrth_not_root_pos_comb hIα hIβ hso.1 hso.2.1 hadd hsub ha' hb').1
        ((mem_rootFinset (τ := .E8)).mp ((mem_roots_E8 n f _).mp hmem))
  ·
    intro α hα β hβ hso a ha b hb
    have hIα : IsRoot .F4 α := (mem_rootFinset (τ := .F4)).mp ((mem_roots_twistedE6 n f α).mp hα)
    have hIβ : IsRoot .F4 β := (mem_rootFinset (τ := .F4)).mp ((mem_roots_twistedE6 n f β).mp hβ)
    have hadd : ¬ IsRoot .F4 (α + β) := fun h =>
      hso.2.2.1 ((mem_roots_twistedE6 n f _).mpr ((mem_rootFinset (τ := .F4)).mpr h))
    have hsub : ¬ IsRoot .F4 (α - β) := fun h =>
      hso.2.2.2 ((mem_roots_twistedE6 n f _).mpr ((mem_rootFinset (τ := .F4)).mpr h))
    have hbase : ∀ x ∈ {x : Fin (Tag.rank .E6) → ℤ | IsRoot .E6 x},
        ∀ y ∈ {y : Fin (Tag.rank .E6) → ℤ | IsRoot .E6 y},
        (∃ c : ℕ, 0 < c ∧ CFSG.LieType.Steinberg.orbitSum TwistedE6.orbitMap x = c • α) →
        (∃ c' : ℕ, 0 < c' ∧ CFSG.LieType.Steinberg.orbitSum TwistedE6.orbitMap y = c' • β) →
        ∀ u ∈ CFSG.LieType.Steinberg.Minuscule.e6Data_valid.rootGroup
            (GaloisField 2 (2 * f)) x,
          ∀ v ∈ CFSG.LieType.Steinberg.Minuscule.e6Data_valid.rootGroup
            (GaloisField 2 (2 * f)) y, u * v = v * u := by
      intro x hxΦ y hyΦ ⟨c, hc, hxproj⟩ ⟨c', hc', hyproj⟩ u hu v hv
      have hxproj1 : TwistedE6.proj x = α := by
        obtain ⟨α₀, hα₀, hα₀eq⟩ := TwistedE6.exists_proj_eq hIα
        have hc1 : c = 1 := by
          refine TwistedE6.eq_one_of_proj_eq_nsmul hxΦ hα₀ hc ?_
          change CFSG.LieType.Steinberg.orbitSum TwistedE6.orbitMap x = c • TwistedE6.proj α₀
          exact hxproj.trans (congrArg (fun v => c • v) hα₀eq).symm
        show TwistedE6.proj x = α
        rw [show TwistedE6.proj x = c • α from hxproj, hc1, one_smul]
      have hyproj1 : TwistedE6.proj y = β := by
        obtain ⟨β₀, hβ₀, hβ₀eq⟩ := TwistedE6.exists_proj_eq hIβ
        have hc1 : c' = 1 := by
          refine TwistedE6.eq_one_of_proj_eq_nsmul hyΦ hβ₀ hc' ?_
          change CFSG.LieType.Steinberg.orbitSum TwistedE6.orbitMap y = c' • TwistedE6.proj β₀
          exact hyproj.trans (congrArg (fun v => c' • v) hβ₀eq).symm
        show TwistedE6.proj y = β
        rw [show TwistedE6.proj y = c' • β from hyproj, hc1, one_smul]
      refine e6Datum_rootGroup_commute (GaloisField 2 (2 * f)) hxΦ hyΦ ?_ ?_ ?_ ?_ u hu v hv
      · intro h
        have := congrArg TwistedE6.proj h
        rw [hxproj1, hyproj1] at this
        exact hso.1 this
      · intro h
        have := congrArg TwistedE6.proj h
        rw [map_neg, hxproj1, hyproj1] at this
        exact hso.2.1 this
      · intro hr
        have := TwistedE6.isRoot_proj hr
        rw [map_add, hxproj1, hyproj1] at this
        exact hadd this
      · intro hr
        have := TwistedE6.isRoot_proj hr
        rw [map_sub, hxproj1, hyproj1] at this
        exact hsub this
    have hcomm := twistedRootSubgroup_commute
      {x : Fin (Tag.rank .E6) → ℤ | IsRoot .E6 x} TwistedE6.orbitMap
      (CFSG.LieType.Steinberg.Minuscule.e6Data_valid.rootGroup (GaloisField 2 (2 * f)))
      (CFSG.LieType.Steinberg.TwistedE6.sigma (GaloisField 2 (2 * f))
        (CFSG.LieType.Steinberg.Exceptional.frobQ 2 f))
      (α := α) (β := β) hbase
    have ha' : a.1 ∈ CFSG.LieType.Steinberg.twistedRootSubgroup
        {x : Fin (Tag.rank .E6) → ℤ | IsRoot .E6 x} TwistedE6.orbitMap
        (CFSG.LieType.Steinberg.Minuscule.e6Data_valid.rootGroup (GaloisField 2 (2 * f)))
        (CFSG.LieType.Steinberg.TwistedE6.sigma (GaloisField 2 (2 * f))
          (CFSG.LieType.Steinberg.Exceptional.frobQ 2 f)) α := ha
    have hb' : b.1 ∈ CFSG.LieType.Steinberg.twistedRootSubgroup
        {x : Fin (Tag.rank .E6) → ℤ | IsRoot .E6 x} TwistedE6.orbitMap
        (CFSG.LieType.Steinberg.Minuscule.e6Data_valid.rootGroup (GaloisField 2 (2 * f)))
        (CFSG.LieType.Steinberg.TwistedE6.sigma (GaloisField 2 (2 * f))
          (CFSG.LieType.Steinberg.Exceptional.frobQ 2 f)) β := hb
    exact Subtype.ext (hcomm a.1 ha' b.1 hb')

end ExcCertRootGroups

end RootGroups

end CFSG.StandardType
