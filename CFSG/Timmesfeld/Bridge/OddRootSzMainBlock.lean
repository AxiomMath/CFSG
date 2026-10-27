module

public import CFSG.Timmesfeld.Bridge.OddRootSzMainComp
import CFSG.Timmesfeld.Bridge.OddLocalBlock
import CFSG.Timmesfeld.Bridge.OddTranspMain

public section

namespace CFSG.Timmesfeld.Bridge.OddRoot

open CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity CFSG.Timmesfeld.Bridge
  CFSG.Timmesfeld.Bridge.OddTransp CFSG.Timmesfeld.Bridge.OddLocal
  CFSG.Timmesfeld.Bridge.Asc72 CFSG.BenderSuzuki
open CFSG.ComponentClassification.AschbacherToolkit.Bender (sylowCenter mem_sylowCenter)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {D : Set G} {d e : G} {E : Set G} {n : ℕ}

@[expose] def viewE (D : Set G) (c : G) : Set G :=
  {u | u ∈ D ∧ Commute u c ∧ u ∉ rootSet D c}

theorem viewE_conj (hN : Connectivity.IsNormalSet D) (g c : G) :
    viewE D (g * c * g⁻¹) = (fun x => g * x * g⁻¹) '' viewE D c := by
  have hD : (MulAut.conj g) '' D = D := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa using hN g y hy
    · intro hx
      refine ⟨g⁻¹ * x * g, by simpa using hN g⁻¹ x hx, ?_⟩
      simp [MulAut.conj_apply, mul_assoc]
  have hroot : rootSet D (g * c * g⁻¹) =
      (fun x => g * x * g⁻¹) '' rootSet D c := by
    have hfun : (⇑(MulAut.conj g) : G → G) = fun x => g * x * g⁻¹ :=
      funext (MulAut.conj_apply g)
    have h := CFSG.Timmesfeld.rootSet_map (MulAut.conj g) (E := D) hD c
    rw [hfun] at h
    exact h
  ext x
  constructor
  · rintro ⟨hxD, hxc, hxr⟩
    refine ⟨g⁻¹ * x * g, ⟨?_, ?_, ?_⟩, by group⟩
    · simpa using hN g⁻¹ x hxD
    · have hxc' : Commute (g * (g⁻¹ * x * g) * g⁻¹) (g * c * g⁻¹) := by
        simpa [mul_assoc] using hxc
      simpa [mul_assoc] using (Commute.conj_iff g).mp hxc'
    · intro hmem
      apply hxr
      rw [hroot]
      exact ⟨g⁻¹ * x * g, hmem, by group⟩
  · rintro ⟨y, ⟨hyD, hyc, hyr⟩, rfl⟩
    refine ⟨hN g y hyD, ?_, ?_⟩
    · exact (Commute.conj_iff g).mpr hyc
    · rw [hroot]
      rintro ⟨z, hz, hzy⟩
      apply hyr
      have hzy' : z = y := by
        have h := congrArg (fun w => g⁻¹ * w * g) hzy
        simpa [mul_assoc] using h
      rwa [hzy'] at hz

private theorem rootSet_subset_normSet_diff (c : SzCfg G D d E e n) :
    rootSet D d ⊆ normSet D E \ E := by
  intro u hu
  have huD : u ∈ D := hu.1
  have hcommE : ∀ x ∈ E, Commute u x := by
    intro x hx
    have hxd : Commute d x := (c.subset_commSet hx).2.1.symm
    exact (hu.2 x (c.subset_commSet hx).1).2 hxd
  refine ⟨⟨huD, mem_normalizer_of_commute hcommE⟩, ?_⟩
  intro huE
  obtain ⟨x, hxE, hxnc⟩ := c.exists_not_commute huE
  exact hxnc (hcommE x hxE).symm

theorem SzCfg.disjoint (c : SzCfg G D d E e n) : Disjoint (rootSet D d) E := by
  rw [Set.disjoint_left]
  intro u hu huE
  exact (rootSet_subset_normSet_diff c hu).2 huE

theorem SzCfg.commute_of_mem_rootSet_d (c : SzCfg G D d E e n) {u x : G}
    (hu : u ∈ rootSet D d) (hx : x ∈ Subgroup.closure E) : Commute u x := by
  have hcommE : ∀ y ∈ E, Commute u y := by
    intro y hy
    have hyd : Commute d y := (c.subset_commSet hy).2.1.symm
    exact (hu.2 y (c.subset_commSet hy).1).2 hyd
  have hcen : Subgroup.closure E ≤ Subgroup.centralizer ({u} : Set G) := by
    rw [Subgroup.closure_le]
    intro y hy
    exact Subgroup.mem_centralizer_singleton_iff.mpr (hcommE y hy).symm
  exact (Subgroup.mem_centralizer_singleton_iff.mp (hcen hx)).symm

private theorem reach_of_mem_of_szCfg (c : SzCfg G D d E e n) :
    ∀ a ∈ D, ∀ b ∈ D, Reach D a b := by
  intro a ha b hb
  by_contra h
  exact c.hyp.conn ⟨a, ha, b, hb, h⟩

private theorem isMaxBlock_normSet_diff_of_szCfg (c : SzCfg G D d E e n) :
    IsMaxBlock D (normSet D E \ E) :=
  isMaxBlock_normSet_diff c.hyp.setup (reach_of_mem_of_szCfg c) c.d_mem c.maxOrbit

private theorem isBlock_normSet_diff_of_szCfg (c : SzCfg G D d E e n) :
    MulAction.IsBlock (ConjAct G) (normSet D E \ E) :=
  (isMaxBlock_normSet_diff_of_szCfg c).2.2.2.1

private theorem commutingSet_diff_normSet_eq (c : SzCfg G D d E e n) :
    {x : G | x ∈ D ∧ Commute d x} \ (normSet D E \ E) = E := by
  ext x
  constructor
  · rintro ⟨⟨hxD, hxd⟩, hxF⟩
    by_contra hxE
    exact hxF ⟨mem_normSet_of_commute c.hyp.setup.normal c.maxOrbit hxD hxd.symm, hxE⟩
  · intro hxE
    exact ⟨⟨(c.subset_commSet hxE).1, (c.subset_commSet hxE).2.1.symm⟩,
      fun h => h.2 hxE⟩

private theorem normSet_normSet_diff_eq (c : SzCfg G D d E e n) :
    normSet D (normSet D E \ E) \ (normSet D E \ E) = E := by
  have hblock : MulAction.IsBlock (ConjAct G) (normSet D E \ E) :=
    isBlock_normSet_diff_of_szCfg c
  have hdF : d ∈ normSet D E \ E := self_mem_F c.hyp.setup.normal c.d_mem c.maxOrbit
  apply Set.Subset.antisymm
  · rintro x ⟨hxN, hxF⟩
    have hxd : Commute x d := by
      by_contra hnc
      have hdN : d ∈ Subgroup.normalizer (normSet D E \ E) :=
        (isBlock_conj_iff.mp hblock d d hdF (by simpa using hdF))
      exact hxF (mem_of_not_commute c.hyp.setup.oddT hdF.1.1 hxN.1 (fun h => hnc h.symm)
        hdF hdN hxN.2)
    have hxC : x ∈ {y : G | y ∈ D ∧ Commute d y} \ (normSet D E \ E) :=
      ⟨⟨hxN.1, hxd.symm⟩, hxF⟩
    rwa [commutingSet_diff_normSet_eq c] at hxC
  · intro x hxE
    have hxN : x ∈ normSet D (normSet D E \ E) := by
      refine ⟨(c.subset_commSet hxE).1, mem_normalizer_of_commute ?_⟩
      intro y hy
      exact (commute_of_mem_F c.hyp.setup c.maxOrbit hy hxE).symm
    exact ⟨hxN, fun h => h.2 hxE⟩

private theorem conj_normSet_diff_subset (c : SzCfg G D d E e n) {k : G}
    (hk : k * d * k⁻¹ = e) :
    OddLocal.conjSet k (normSet D E \ E) ⊆ E := by
  let F : Set G := normSet D E \ E
  let B : Set G := OddLocal.conjSet k F
  have hFblock : MulAction.IsBlock (ConjAct G) F := isBlock_normSet_diff_of_szCfg c
  have hdF : d ∈ F := self_mem_F c.hyp.setup.normal c.d_mem c.maxOrbit
  have heB : e ∈ B := ⟨d, hdF, hk⟩
  have hsmul : (ConjAct.toConjAct k • F : Set G) = B := by
    ext y
    simp only [OddLocal.conjSet, Set.mem_image, Set.mem_smul_set, ConjAct.toConjAct_smul]
    rfl
  have hBblock : MulAction.IsBlock (ConjAct G) B := by
    rw [← hsmul]
    exact hFblock.translate (ConjAct.toConjAct k)
  have heNotF : e ∉ F := fun h => h.2 c.e_mem
  have hBneF : B ≠ F := fun h => heNotF (h ▸ heB)
  have hBdisj : Disjoint B F := by
    rcases hFblock.smul_eq_or_disjoint (ConjAct.toConjAct k) with h | h
    · exact absurd (hsmul.symm.trans h) hBneF
    · rwa [hsmul] at h
  have hdB : d ∉ B := fun hd => (Set.disjoint_left.mp hBdisj) hd hdF
  have hcommDe : Commute d e := ((c.subset_commSet c.e_mem).2.1).symm
  have hcomm' : Commute (k⁻¹ * d * k) d := by
    have h1 : Commute (k * (k⁻¹ * d * k) * k⁻¹) (k * d * k⁻¹) := by
      have hleft : k * (k⁻¹ * d * k) * k⁻¹ = d := by group
      rw [hleft, hk]
      exact hcommDe
    simpa [mul_assoc] using (Commute.conj_iff k).mp h1
  have hkD : k⁻¹ * d * k ∈ D := by
    simpa using c.hyp.setup.conj_mem k⁻¹ c.d_mem
  have hknotF : k⁻¹ * d * k ∉ F := by
    intro hF
    exact hdB ⟨k⁻¹ * d * k, hF, by group⟩
  have hkE : k⁻¹ * d * k ∈ E := by
    have hC : k⁻¹ * d * k ∈ {x : G | x ∈ D ∧ Commute d x} \ F :=
      ⟨⟨hkD, hcomm'.symm⟩, hknotF⟩
    rwa [commutingSet_diff_normSet_eq c] at hC
  have hd_eq : d = k * (k⁻¹ * d * k) * k⁻¹ := by group
  intro b hbB
  obtain ⟨f, hfF, rfl⟩ := hbB
  have hbD : k * f * k⁻¹ ∈ D := c.hyp.setup.conj_mem k hfF.1.1
  have hbd : Commute (k * f * k⁻¹) d := by
    have hcomm_ef : Commute (k⁻¹ * d * k) f :=
      (commute_of_mem_F c.hyp.setup c.maxOrbit hfF hkE).symm
    have hconj : Commute (k * (k⁻¹ * d * k) * k⁻¹) (k * f * k⁻¹) :=
      (Commute.conj_iff k).mpr hcomm_ef
    rw [← hd_eq] at hconj
    exact hconj.symm
  have hbN : k * f * k⁻¹ ∈ normSet D E :=
    mem_normSet_of_commute c.hyp.setup.normal c.maxOrbit hbD hbd
  have hbNotF : k * f * k⁻¹ ∉ F := fun hbF => (Set.disjoint_left.mp hBdisj) ⟨f, hfF, rfl⟩ hbF
  by_cases hbE : k * f * k⁻¹ ∈ E
  · exact hbE
  · exact absurd ⟨hbN, hbE⟩ hbNotF

private theorem isBlock_conjSet_normSet_diff (c : SzCfg G D d E e n) (k : G) :
    MulAction.IsBlock (ConjAct G) (OddLocal.conjSet k (normSet D E \ E)) := by
  let F : Set G := normSet D E \ E
  have hFblock : MulAction.IsBlock (ConjAct G) F := isBlock_normSet_diff_of_szCfg c
  have hsmul : (ConjAct.toConjAct k • F : Set G) = OddLocal.conjSet k F := by
    ext y
    simp only [OddLocal.conjSet, Set.mem_image, Set.mem_smul_set, ConjAct.toConjAct_smul]
  rw [← hsmul]
  exact hFblock.translate (ConjAct.toConjAct k)

private theorem isBlock_subset_eq (c : SzCfg G D d E e n) {B : Set G}
    (hBblock : MulAction.IsBlock (ConjAct G) B) (heB : e ∈ B) (hBsubE : B ⊆ E)
    {u v : G} (huB : u ∈ B) (hvB : v ∈ B) (huv : ¬ Commute u v) : B = E := by
  obtain ⟨P, heP⟩ := c.exists_szS c.e_mem
  have huE : u ∈ E := hBsubE huB
  have hvE : v ∈ E := hBsubE hvB
  have huN : u ∈ Subgroup.normalizer B :=
    isBlock_conj_iff.mp hBblock u u huB (by simpa using huB)
  have hvN : v ∈ Subgroup.normalizer B :=
    isBlock_conj_iff.mp hBblock v v hvB (by simpa using hvB)
  have hcN : ∀ x ∈ szComp E e, x ∈ Subgroup.normalizer B := by
    intro x hx
    refine isBlock_conj_iff.mp hBblock x e heB ?_
    rw [hx.2.eq, mul_inv_cancel_right]
    exact heB
  have hnotboth : ¬ (u ∈ szComp E e ∧ v ∈ szComp E e) := by
    rintro ⟨huc, hvc⟩
    have huP : u ∈ szS E P := (c.mem_szS_iff_commute P c.e_mem huE heP).mpr huc.2
    have hvP : v ∈ szS E P := (c.mem_szS_iff_commute P c.e_mem hvE heP).mpr hvc.2
    have hzu : szMk E ⟨u, Subgroup.subset_closure huE⟩ ∈
        sylowCenter (P : Subgroup (SzBar E)) :=
      c.mk_mem_sylowCenter P huE (mem_szS_iff.mp huP).2
    have hzv : szMk E ⟨v, Subgroup.subset_closure hvE⟩ ∈
        sylowCenter (P : Subgroup (SzBar E)) :=
      c.mk_mem_sylowCenter P hvE (mem_szS_iff.mp hvP).2
    have hcommK : Commute (szMk E ⟨u, Subgroup.subset_closure huE⟩)
        (szMk E ⟨v, Subgroup.subset_closure hvE⟩) :=
      (mem_sylowCenter.mp hzv).2 _ (mem_sylowCenter.mp hzu).1
    have hcommH : Commute (⟨u, Subgroup.subset_closure huE⟩ : ↥(Subgroup.closure E))
        (⟨v, Subgroup.subset_closure hvE⟩ : ↥(Subgroup.closure E)) :=
      (c.commute_mk_iff (u := ⟨u, Subgroup.subset_closure huE⟩)
        (v := ⟨v, Subgroup.subset_closure hvE⟩) huE hvE).mp hcommK
    exact huv ((commute_coe_iff (H := Subgroup.closure E)).mpr hcommH)
  have hHle : Subgroup.closure E ≤ Subgroup.normalizer B := by
    rcases not_and_or.mp hnotboth with huc | hvc
    · have hne : ¬ Commute e u := fun h => huc ⟨huE, h.symm⟩
      rw [← c.closure_insert_comp c.e_mem huE hne]
      rw [Subgroup.closure_le]
      intro x hx
      rcases hx with rfl | hxc
      · exact huN
      · exact hcN x hxc
    · have hne : ¬ Commute e v := fun h => hvc ⟨hvE, h.symm⟩
      rw [← c.closure_insert_comp c.e_mem hvE hne]
      rw [Subgroup.closure_le]
      intro x hx
      rcases hx with rfl | hxc
      · exact hvN
      · exact hcN x hxc
  apply Set.Subset.antisymm hBsubE
  intro x hxE
  obtain ⟨h, hh, hhx⟩ := c.exists_conj c.e_mem hxE
  rw [← hhx]
  exact ((Subgroup.mem_set_normalizer_iff.mp (hHle hh)) e).mp heB

private theorem false_of_isBlock_subset (c : SzCfg G D d E e n) {B : Set G}
    (hBblock : MulAction.IsBlock (ConjAct G) B) (heB : e ∈ B) (hBsubE : B ⊆ E)
    {u v : G} (huB : u ∈ B) (hvB : v ∈ B) (huv : ¬ Commute u v) : False := by
  have hBE : B = E := isBlock_subset_eq c hBblock heB hBsubE huB hvB huv
  have hEblock : MulAction.IsBlock (ConjAct G) E := hBE ▸ hBblock
  let F : Set G := normSet D E \ E
  have hFblock : MulAction.IsBlock (ConjAct G) F := isBlock_normSet_diff_of_szCfg c
  have hdF : d ∈ F := self_mem_F c.hyp.setup.normal c.d_mem c.maxOrbit
  have hFsubD : F ⊆ D := fun x hx => hx.1.1
  have hEcommF : ∀ x ∈ E, ∀ y ∈ F, Commute x y := by
    intro x hx y hy
    exact (commute_of_mem_F c.hyp.setup c.maxOrbit hy hx).symm
  have hclosed : ∀ x ∈ E ∪ F, ∀ y ∈ D, Commute x y → y ∈ E ∪ F := by
    intro x hx y hyD hxy
    rcases hx with hxE | hxF
    · have hyN : y ∈ normSet D E := by
        refine ⟨hyD, ?_⟩
        have hmem : y * x * y⁻¹ = x := by
          calc y * x * y⁻¹ = x * y * y⁻¹ := by rw [← hxy.eq]
            _ = x := by group
        refine isBlock_conj_iff.mp hEblock y x hxE ?_
        rw [hmem]
        exact hxE
      by_cases hyE : y ∈ E
      · exact Or.inl hyE
      · exact Or.inr ⟨hyN, hyE⟩
    · have hyN : y ∈ normSet D F := by
        refine ⟨hyD, ?_⟩
        have hmem : y * x * y⁻¹ = x := by
          calc y * x * y⁻¹ = x * y * y⁻¹ := by rw [← hxy.eq]
            _ = x := by group
        refine isBlock_conj_iff.mp hFblock y x hxF ?_
        rw [hmem]
        exact hxF
      by_cases hyF : y ∈ F
      · exact Or.inr hyF
      · have hyE : y ∈ E := by
          rw [← normSet_normSet_diff_eq c]
          exact ⟨hyN, hyF⟩
        exact Or.inl hyE
  have hDsub : D ⊆ E ∪ F := by
    intro y hyD
    exact mem_of_reach hclosed (Or.inr hdF) (reach_of_mem_of_szCfg c d c.d_mem y hyD)
  have hnorm : ∀ x ∈ D, x ∈ Subgroup.normalizer F := by
    intro x hxD
    rcases hDsub hxD with hxE | hxF
    · exact mem_normalizer_of_commute (fun y hy => hEcommF x hxE y hy)
    · exact isBlock_conj_iff.mp hFblock x x hxF (by simpa using hxF)
  have htop : Subgroup.closure D ≤ Subgroup.normalizer F := by
    rw [Subgroup.closure_le]
    exact hnorm
  rw [c.hyp.setup.gen] at htop
  have hFD : F = D := by
    apply Set.Subset.antisymm hFsubD
    intro y hyD
    obtain ⟨h, hh⟩ := isConj_iff.mp (c.hyp.setup.isConj c.d_mem hyD)
    rw [← hh]
    exact ((Subgroup.mem_set_normalizer_iff.mp (htop (Subgroup.mem_top h))) d).mp hdF
  exact (isMaxBlock_normSet_diff_of_szCfg c).2.2.1 hFD

private theorem commute_of_mem_normSet_diff (c : SzCfg G D d E e n) {f g : G}
    (hf : f ∈ normSet D E \ E) (hg : g ∈ normSet D E \ E) : Commute f g := by
  by_contra hfg
  obtain ⟨k, hk⟩ := isConj_iff.mp (c.hyp.setup.isConj c.d_mem (c.subset_commSet c.e_mem).1)
  let F : Set G := normSet D E \ E
  let B : Set G := OddLocal.conjSet k F
  have hBblock : MulAction.IsBlock (ConjAct G) B := isBlock_conjSet_normSet_diff c k
  have hBsubE : B ⊆ E := conj_normSet_diff_subset c hk
  have hdF : d ∈ F := self_mem_F c.hyp.setup.normal c.d_mem c.maxOrbit
  have heB : e ∈ B := ⟨d, hdF, hk⟩
  have huB : k * f * k⁻¹ ∈ B := ⟨f, hf, rfl⟩
  have hvB : k * g * k⁻¹ ∈ B := ⟨g, hg, rfl⟩
  have huv : ¬ Commute (k * f * k⁻¹) (k * g * k⁻¹) := fun h =>
    hfg ((Commute.conj_iff k).mp h)
  exact false_of_isBlock_subset c hBblock heB hBsubE huB hvB huv

private theorem normSet_diff_subset_rootSet (c : SzCfg G D d E e n) :
    normSet D E \ E ⊆ rootSet D d := by
  intro f hf
  have hfD : f ∈ D := hf.1.1
  have hdF : d ∈ normSet D E \ E := self_mem_F c.hyp.setup.normal c.d_mem c.maxOrbit
  refine ⟨hfD, ?_⟩
  intro y hyD
  constructor
  · intro hfy
    have hyN : y ∈ normSet D (normSet D E \ E) := by
      refine ⟨hyD, ?_⟩
      have hmem : y * f * y⁻¹ = f := by
        calc y * f * y⁻¹ = f * y * y⁻¹ := by rw [← hfy.eq]
          _ = f := by group
      refine isBlock_conj_iff.mp (isBlock_normSet_diff_of_szCfg c) y f hf ?_
      rw [hmem]
      exact hf
    by_cases hyF : y ∈ normSet D E \ E
    · exact (commute_of_mem_normSet_diff c hdF hyF)
    · have hyE : y ∈ E := by
        rw [← normSet_normSet_diff_eq c]
        exact ⟨hyN, hyF⟩
      exact ((c.subset_commSet hyE).2.1).symm
  · intro hdy
    have hyN : y ∈ normSet D E := mem_normSet_of_commute c.hyp.setup.normal c.maxOrbit hyD hdy.symm
    by_cases hyE : y ∈ E
    · exact commute_of_mem_F c.hyp.setup c.maxOrbit hf hyE
    · exact commute_of_mem_normSet_diff c hf ⟨hyN, hyE⟩

theorem SzCfg.normSet_diff_eq (c : SzCfg G D d E e n) :
    normSet D E \ E = rootSet D d :=
  Set.Subset.antisymm (normSet_diff_subset_rootSet c) (rootSet_subset_normSet_diff c)

theorem SzCfg.commute_d_iff (c : SzCfg G D d E e n) {x : G} (hx : x ∈ D) :
    Commute x d ↔ x ∈ rootSet D d ∨ x ∈ E := by
  constructor
  · intro hxd
    have hxN : x ∈ normSet D E := mem_normSet_of_commute c.hyp.setup.normal c.maxOrbit hx hxd
    by_cases hxE : x ∈ E
    · exact Or.inr hxE
    · refine Or.inl ?_
      rw [← c.normSet_diff_eq]
      exact ⟨hxN, hxE⟩
  · rintro (hxroot | hxE)
    · exact (hxroot.2 d c.d_mem).2 (Commute.refl d)
    · exact (c.subset_commSet hxE).2.1

theorem SzCfg.viewE_eq (c : SzCfg G D d E e n) : viewE D d = E := by
  ext x
  constructor
  · rintro ⟨hxD, hxd, hxr⟩
    rcases (c.commute_d_iff hxD).mp hxd with hxroot | hxE
    · exact absurd hxroot hxr
    · exact hxE
  · intro hxE
    exact ⟨(c.subset_commSet hxE).1, (c.subset_commSet hxE).2.1,
      fun hxroot => (Set.disjoint_left.mp (c.disjoint)) hxroot hxE⟩

end CFSG.Timmesfeld.Bridge.OddRoot
