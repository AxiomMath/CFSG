module

public import CFSG.LocalAnalysis.StandardType.GGNbrWeylTypeDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenCore
public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenWeylLift
public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenTwE6Three
import TauCeti.GroupTheory.SpecificGroups.Dihedral.Basic

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

private lemma ggWTGlue_card_G2 : Nat.card (CoxeterMatrix.G₂).Group = 12 := by
  let cs := (CoxeterMatrix.G₂).toCoxeterSystem
  have hs : cs.simple 0 * cs.simple 0 = 1 := cs.simple_mul_simple_self 0
  have ht : cs.simple 1 * cs.simple 1 = 1 := cs.simple_mul_simple_self 1
  have hs1 : cs.simple 0 ≠ 1 := cs.simple_ne_one 0
  have ht1 : cs.simple 1 ≠ 1 := cs.simple_ne_one 1
  have hn : orderOf (cs.simple 0 * cs.simple 1) = 6 := by
    rw [cs.orderOf_simple_mul_simple]; decide
  have hgen : Subgroup.closure ({cs.simple 0, cs.simple 1} : Set (CoxeterMatrix.G₂).Group) = ⊤ := by
    rw [← cs.subgroup_closure_range_simple]
    congr 1
    ext x
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro (hx | hx)
      · exact ⟨0, hx.symm⟩
      · exact ⟨1, hx.symm⟩
    · rintro ⟨i, hi⟩
      rw [← hi]
      have hi' : i = 0 ∨ i = 1 := by
        have h : i.val = 0 ∨ i.val = 1 := by omega
        rcases h with h | h
        · exact Or.inl (Fin.ext h)
        · exact Or.inr (Fin.ext h)
      rcases hi' with rfl | rfl <;> simp
  have e : DihedralGroup 6 ≃* (CoxeterMatrix.G₂).Group :=
    TauCeti.dihedralGroupMulEquiv (s := cs.simple 0) (t := cs.simple 1) (n := 6)
      hs ht hs1 ht1 hn hgen
  calc Nat.card (CoxeterMatrix.G₂).Group = Nat.card (DihedralGroup 6) :=
        (Nat.card_congr e.toEquiv).symm
    _ = 12 := by rw [DihedralGroup.nat_card]

section Glue

variable {G : Type} [Group G] [Finite G]

theorem ggAutomizer_le_closure_ggTorusReflSet_of_mulEquiv {p : ℕ} {L' : Type} [Group L']
    {A : Subgroup (MulAut L')} {ι : Type} {M : CoxeterMatrix ι}
    (f : M.Group ≃* ↥(ggAutomizer (MulAut.conj : L' →* MulAut L').range A))
    (hrefl : ∀ i : ι,
      ((f (M.simple i) : ↥(ggAutomizer (MulAut.conj : L' →* MulAut L').range A)) :
        MulAut ↥A) ∈ ggTorusReflSet p A) :
    ggAutomizer (MulAut.conj : L' →* MulAut L').range A ≤
      Subgroup.closure (ggTorusReflSet p A) := by
  let H : Subgroup (MulAut L') := (MulAut.conj : L' →* MulAut L').range
  let f' : M.Group →* MulAut ↥A :=
    (Subgroup.subtype (ggAutomizer H A)).comp (f : M.Group →* ↥(ggAutomizer H A))
  have hgen : Subgroup.closure (Set.range M.simple) = ⊤ := by
    have hrange : Set.range M.simple = Set.range (PresentedGroup.of : ι → M.Group) := rfl
    rw [hrange]
    exact PresentedGroup.closure_range_of _
  have hle : Subgroup.closure (Set.range M.simple) ≤
      Subgroup.comap f' (Subgroup.closure (ggTorusReflSet p A)) := by
    rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact Subgroup.subset_closure (by simpa [f'] using hrefl i)
  intro φ hφ
  have hw : f.symm ⟨φ, hφ⟩ ∈ Subgroup.closure (Set.range M.simple) := by
    rw [hgen]; exact Subgroup.mem_top _
  have hmem : f' (f.symm ⟨φ, hφ⟩) ∈ Subgroup.closure (ggTorusReflSet p A) := hle hw
  simpa [f'] using hmem

theorem ggWeylOfType_of_ggTorusReflSet {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J) (hNoTr : GGNoTransvection p Bs)
    {K : Subgroup G} (hN : Bs ≤ Subgroup.normalizer (K : Set G)) {ι : Type}
    {M : CoxeterMatrix ι}
    (f : M.Group ≃*
      ↥(ggAutomizer (MulAut.conj : ↥K →* MulAut ↥K).range (ggGamma K hN).range))
    (hrefl : ∀ i : ι,
      ((f (M.simple i) :
        ↥(ggAutomizer (MulAut.conj : ↥K →* MulAut ↥K).range (ggGamma K hN).range)) :
        MulAut ↥(ggGamma K hN).range) ∈ ggTorusReflSet p (ggGamma K hN).range)
    (hZ : Nat.card ↥(Bs ⊓ K ⊓ Subgroup.centralizer (K : Set G)) ≤ p) :
    GGWeylOfType p M (ggAutomizer K Bs) := by
  classical
  obtain ⟨hp, hBs, -, -, -⟩ := hcfg.tableB_facts
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  let A : Subgroup (MulAut ↥K) := (ggGamma K hN).range
  let H : Subgroup (MulAut ↥K) := (MulAut.conj : ↥K →* MulAut ↥K).range
  let Aut : Subgroup (MulAut ↥A) := ggAutomizer H A
  have hW' : ggAutomizer H A ≤ Subgroup.closure (ggTorusReflSet p A) :=
    ggAutomizer_le_closure_ggTorusReflSet_of_mulEquiv f hrefl
  have hex : ∀ a ∈ Aut,
      ∃ c ∈ Subgroup.closure {φ : MulAut ↥Bs | φ ∈ ggAutomizer K Bs ∧ GGIsReflection p φ},
        GGOverGamma hN c a :=
    exists_overGamma_of_weylReflSet hp hp2 hBs hSC hN hW'
  have hCle : Subgroup.closure {φ : MulAut ↥Bs | φ ∈ ggAutomizer K Bs ∧ GGIsReflection p φ} ≤
      ggAutomizer K Bs := (Subgroup.closure_le _).mpr fun φ hφ => hφ.1
  have hexu : ∀ a : ↥Aut, ∃! c : MulAut ↥Bs,
      c ∈ ggAutomizer K Bs ∧ GGOverGamma hN c (a : MulAut ↥A) := by
    intro a
    obtain ⟨c, hcl, hcov⟩ := hex (a : MulAut ↥A) a.2
    refine ⟨c, ⟨hCle hcl, hcov⟩, ?_⟩
    rintro d ⟨hd, hdov⟩
    have h1 : GGOverGamma hN (c⁻¹ * d) 1 := by
      have h := hcov.inv.mul hdov
      rwa [inv_mul_cancel] at h
    have hκ : c⁻¹ * d ∈ ggAutomizer K Bs :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ (hCle hcl)) hd
    exact (inv_mul_eq_one.mp (eq_one_of_ggOverGamma_one hp hBs hNoTr hN hZ hκ h1)).symm
  let Φfun : ↥Aut → MulAut ↥Bs := fun a => Classical.choose (hexu a)
  have hΦmem : ∀ a : ↥Aut, Φfun a ∈ ggAutomizer K Bs :=
    fun a => (Classical.choose_spec (hexu a)).1.1
  have hΦover : ∀ a : ↥Aut, GGOverGamma hN (Φfun a) (a : MulAut ↥A) :=
    fun a => (Classical.choose_spec (hexu a)).1.2
  have hΦuniq : ∀ (a : ↥Aut) (d : MulAut ↥Bs), d ∈ ggAutomizer K Bs →
      GGOverGamma hN d (a : MulAut ↥A) → d = Φfun a :=
    fun a d hd hdv => (Classical.choose_spec (hexu a)).2 d ⟨hd, hdv⟩
  have hΦone : Φfun 1 = 1 := by
    exact (hΦuniq 1 1 (ggAutomizer K Bs).one_mem
      (by simpa using (GGOverGamma.one (hN := hN) : GGOverGamma hN 1 (1 : MulAut ↥A)))).symm
  have hΦmul : ∀ a b : ↥Aut, Φfun (a * b) = Φfun a * Φfun b := by
    intro a b
    exact (hΦuniq (a * b) (Φfun a * Φfun b)
      ((ggAutomizer K Bs).mul_mem (hΦmem a) (hΦmem b)) (by
        have h := (hΦover a).mul (hΦover b)
        simpa [Subgroup.coe_mul] using h)).symm
  let Φhom : ↥Aut →* ↥(ggAutomizer K Bs) :=
    { toFun := fun a => ⟨Φfun a, hΦmem a⟩
      map_one' := by
        apply Subtype.ext
        exact hΦone
      map_mul' := by
        intro a b
        apply Subtype.ext
        exact hΦmul a b }
  have hinj : Function.Injective Φhom := by
    intro a b hab
    have hab' : Φfun a = Φfun b := by
      have h := congrArg (fun c : ↥(ggAutomizer K Bs) => (c : MulAut ↥Bs)) hab
      simpa [Φhom] using h
    apply Subtype.ext
    apply MulEquiv.ext
    intro x
    obtain ⟨y, rfl⟩ := MonoidHom.rangeRestrict_surjective (ggGamma K hN) x
    have ha := hΦover a y
    have hb := hΦover b y
    rw [hab'] at ha
    exact ha.symm.trans hb
  have hsurj : Function.Surjective Φhom := by
    intro c
    obtain ⟨g, hgK, hg, hc⟩ :=
      (mem_ggAutomizer_iff (H := K) (Bs := Bs) (φ := (c : MulAut ↥Bs))).mp c.2
    have hceq : (c : MulAut ↥Bs) = ggConjAut Bs hg := by
      apply MulEquiv.ext
      intro b
      apply Subtype.ext
      rw [ggConjAut_apply]
      exact hc b
    let a0 : MulAut ↥A := ggConjAut A (conj_mem_normalizer_range_ggGamma hN hgK hg)
    have ha0 : a0 ∈ Aut :=
      ggConjAut_mem_ggAutomizer (H := H) (Bs := A)
        (g := MulAut.conj (⟨g, hgK⟩ : ↥K))
        (MonoidHom.mem_range.mpr ⟨⟨g, hgK⟩, rfl⟩)
        (conj_mem_normalizer_range_ggGamma hN hgK hg)
    refine ⟨⟨a0, ha0⟩, ?_⟩
    apply Subtype.ext
    exact (hΦuniq ⟨a0, ha0⟩ (c : MulAut ↥Bs) c.2 (by
      rw [hceq]
      exact ggOverGamma_conjAut (hN := hN) hgK hg)).symm
  let Φe : ↥Aut ≃* ↥(ggAutomizer K Bs) := MulEquiv.ofBijective Φhom ⟨hinj, hsurj⟩
  refine ⟨f.trans Φe, ?_⟩
  intro i
  obtain ⟨n, hn, hnW, hceq, hrefl'⟩ := hrefl i
  have hrefl'' : GGIsReflection p (ggConjAut A hn) := by
    rw [← hceq]; exact hrefl'
  obtain ⟨g, hgK, hg, hreflg, hover⟩ :=
    exists_isReflection_overGamma_of_weylElt hp hp2 hBs hSC hN hnW hn hrefl''
  have hcg : ggConjAut Bs hg ∈ ggAutomizer K Bs :=
    ggConjAut_mem_ggAutomizer (H := K) hgK hg
  have hΦa : Φfun (f (M.simple i)) = ggConjAut Bs hg := by
    refine (hΦuniq (f (M.simple i)) (ggConjAut Bs hg) hcg ?_).symm
    rw [hceq]
    exact hover
  have hΦe_apply : ((Φe (f (M.simple i)) : ↥(ggAutomizer K Bs)) : MulAut ↥Bs) =
      ggConjAut Bs hg := by
    change Φfun (f (M.simple i)) = ggConjAut Bs hg
    exact hΦa
  rw [MulEquiv.trans_apply]
  show GGIsReflection p ((Φe (f (M.simple i)) : ↥(ggAutomizer K Bs)) : MulAut ↥Bs)
  rw [hΦe_apply]
  exact hreflg

theorem ggWeylReflectionGroup_of_ggTorusWeylTypeW_TB {p r : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J) (hNoTr : GGNoTransvection p Bs)
    {K : Subgroup G} {R : Type} [Group R] (θ : K ⧸ Subgroup.center K ≃* R) {I : Set (MulAut R)}
    (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    (hTB : GGTorusTBGroup p r R I K (ggQuotHom θ) (ggGamma K hN).range)
    (hT : GGTorusWeylTypeW p r R I)
    (hZ : Nat.card ↥(Bs ⊓ K ⊓ Subgroup.centralizer (K : Set G)) ≤ p) :
    GGWeylReflectionGroup p (ggAutomizer K Bs) ∧
      ¬ GGWeylOfType p CoxeterMatrix.G₂ (ggAutomizer K Bs) := by
  obtain ⟨ι, M, f, hWM, hne, hrefl⟩ := hT K (ggQuotHom θ) (ggGamma K hN).range hTB
  obtain ⟨e, he⟩ := ggWeylOfType_of_ggTorusReflSet hcfg hNoTr hN f hrefl hZ
  refine ⟨⟨ι, M, hWM, e, he⟩, ?_⟩
  rintro ⟨e', -⟩
  have hcard : Nat.card ↥(ggAutomizer K Bs) = 12 := by
    have h1 : Nat.card (CoxeterMatrix.G₂).Group = Nat.card ↥(ggAutomizer K Bs) :=
      Nat.card_congr e'.toEquiv
    rw [← h1]
    exact ggWTGlue_card_G2
  exact hne ((Nat.card_congr (f.symm.trans e).toEquiv).trans hcard)

theorem ggWeylReflectionGroup_of_ggTorusWeylTypeW {p r : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J) (hNoTr : GGNoTransvection p Bs)
    {y : G} {K : Subgroup G} (hnb : GGNbr p B x D J y K) (hK : commutator K = ⊤)
    {R : Type} [Group R] (θ : K ⧸ Subgroup.center K ≃* R) {I : Set (MulAut R)}
    (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    (hBsI : ∀ (b : G) (hb : b ∈ Bs), ggLAut K θ ⟨b, hN hb⟩ ∈ I)
    (hlift : GGTorusLift p r R) (hT : GGTorusWeylTypeW p r R I)
    (hZ : Nat.card ↥(Bs ⊓ K ⊓ Subgroup.centralizer (K : Set G)) ≤ p) :
    GGWeylReflectionGroup p (ggAutomizer K Bs) ∧
      ¬ GGWeylOfType p CoxeterMatrix.G₂ (ggAutomizer K Bs) :=
  ggWeylReflectionGroup_of_ggTorusWeylTypeW_TB hcfg hNoTr θ hN
    (ggTorusTBGroup_of_nbr hcfg hnb hK θ hN hBsI hlift) hT hZ

theorem ggWeylReflectionGroup_of_ggTorusWeylTypeW_card {p r : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J) (hr3 : 3 ≤ r)
    (hNoTr : GGNoTransvection p Bs) {y : G} {K : Subgroup G} (hnb : GGNbr p B x D J y K)
    (hK : commutator K = ⊤) {R : Type} [Group R] (θ : K ⧸ Subgroup.center K ≃* R)
    {I : Set (MulAut R)} (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    (hBsI : ∀ (b : G) (hb : b ∈ Bs), ggLAut K θ ⟨b, hN hb⟩ ∈ I)
    (hr : p ^ r ≤ Nat.card (ggGamma K hN).range) (hT : GGTorusWeylTypeW p r R I)
    (hZ : Nat.card ↥(Bs ⊓ K ⊓ Subgroup.centralizer (K : Set G)) ≤ p) :
    GGWeylReflectionGroup p (ggAutomizer K Bs) ∧
      ¬ GGWeylOfType p CoxeterMatrix.G₂ (ggAutomizer K Bs) :=
  ggWeylReflectionGroup_of_ggTorusWeylTypeW_TB hcfg hNoTr θ hN
    (ggTorusTBGroup_of_nbr_card hcfg hr3 hnb hK θ hN hBsI hr) hT hZ

end Glue

end CFSG.StandardType

end
