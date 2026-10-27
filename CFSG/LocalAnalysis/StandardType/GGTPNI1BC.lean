module

public import CFSG.LocalAnalysis.StandardType.GGTPNI1
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSmallRestTri
public import CFSG.LocalAnalysis.StandardType.GGRoundFourSmallASpLift
public import CFSG.LocalAnalysis.StandardType.GGAssemblyThreeHypSix
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid
public import CFSG.LocalAnalysis.ComponentClassification.LocalComponents
public import CFSG.RankThree.Classical.SteinbergBJSymplecticCrossPrimeBlocks
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.ClassicalGroups.Symplectic.ComponentCartanRank
public import CFSG.ClassicalGroups.Symplectic.DiagonalTorusRank
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface
public import CFSG.SignalizerFunctorTheorem.NonLocal.Cross
public import CFSG.SignalizerFunctorTheorem.NonLocal.SpData
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeC.Agreement

public section

namespace CFSG.StandardType

open CFSG CFSG.Open CFSG.Assembly CFSG.RankThree.Classical CFSG.RankThree.PartOne.KCPrimary
  Polynomial

theorem tpbc_hasLabel_C_iff (n f : ℕ) (X : Type) [Group X] :
    GGHasLabel ⟨.C, n, f⟩ X ↔
      CFSG.Assembly.LargeEvenRecipeSymplectic n (2 ^ f) false
        (fun R' _ _ _ => Nonempty (X ≃* R')) := by
  dsimp only [GGHasLabel, CFSG.StandardType.LargeEvenRawDatum]
  rfl

theorem tpbc_hasLabel_B_iff_C (n f : ℕ) (X : Type) [Group X] :
    GGHasLabel ⟨.B, n, f⟩ X ↔ GGHasLabel ⟨.C, n, f⟩ X := by
  dsimp only [GGHasLabel, CFSG.StandardType.LargeEvenRawDatum]
  rfl

theorem tpbc_card_le_of_isElemAbelian_sl2 {F : Type} [Field F] [Finite F] [CharP F 2] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {A : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)}
    (hA : IsElemAbelian p A) : Nat.card A ≤ p :=
  TableBExcSmallRest.card_le_of_isElemAbelian_sl2 hp hp2 hA

theorem tpbc_statedClassicalModel_of_hasLabel_C {X : Type} [Group X] {n f : ℕ}
    (hn : 3 ≤ n) (hf : 1 ≤ f) (hX : GGHasLabel ⟨.C, n, f⟩ X) :
    StatedClassicalModel X .PSp n 2 f := by
  obtain ⟨K, hF, hfin, hK, ⟨e⟩⟩ := hX
  refine ⟨⟨Nat.prime_two, hf, by omega, ?_⟩, K, hF, hfin, hK, ⟨e⟩⟩
  intro h
  simp only [Prod.mk.injEq] at h
  omega

theorem tpbc_exists_spLift_top {L : Type} [Group L] [Finite L] {n f : ℕ} (hn : 4 ≤ n)
    (hperf : commutator L = ⊤)
    (hmod : StatedClassicalModel (L ⧸ Subgroup.center L) .PSp n 2 f) :
    ∃ φ : StatedSp n (GaloisField 2 f) →* L, Function.Injective φ ∧ φ.range = ⊤ := by
  have hmodTop : StatedClassicalModel
      ((⊤ : Subgroup L) ⧸ Subgroup.center (⊤ : Subgroup L)) .PSp n 2 f := by
    obtain ⟨hadm, K, hF, hfin, hK, ⟨e⟩⟩ := hmod
    refine ⟨hadm, K, hF, hfin, hK, ⟨?e'⟩⟩
    exact (QuotientGroup.congr _ _ Subgroup.topEquiv
      (Subgroup.map_center_eq Subgroup.topEquiv)).trans e
  have hperfTop : commutator ↥(⊤ : Subgroup L) = ⊤ := by
    haveI : Group.IsPerfect L := ⟨hperf⟩
    haveI : Group.IsPerfect ↥(⊤ : Subgroup L) :=
      Group.IsPerfect.ofSurjective (f := (Subgroup.topEquiv (G := L)).symm.toMonoidHom)
        (Subgroup.topEquiv (G := L)).symm.surjective
    exact Group.IsPerfect.commutator_eq_top
  exact ggSpLiftInput_holds (G := L) (L := (⊤ : Subgroup L)) n f hn hperfTop hmodTop

private theorem tpbc_centerQuotAut_conj {X : Type} [Group X] (g : X) :
    centerQuotAut X (MulAut.conj g : MulAut X) =
      MulAut.conj (QuotientGroup.mk g : X ⧸ Subgroup.center X) := by
  ext q
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
  simp [centerQuotAut_mk, MulAut.conj_apply]

private theorem tpbc_ggInducedAut_conj {X : Type} [Group X] {R : Type} [Group R]
    (θ : X ⧸ Subgroup.center X ≃* R) (g : X) :
    ggInducedAut θ (MulAut.conj g : MulAut X) =
      MulAut.conj (θ (g : X ⧸ Subgroup.center X)) := by
  change MulAut.congr θ (centerQuotAut X (MulAut.conj g)) =
    MulAut.conj (θ (g : X ⧸ Subgroup.center X))
  rw [tpbc_centerQuotAut_conj, mulAut_congr_conj]

theorem tpbc_mem_inn_of_subset_inn {X : Type} [Group X] {R : Type} [Group R]
    (hperf : commutator X = ⊤) (θ : X ⧸ Subgroup.center X ≃* R) {I : Set (MulAut R)}
    (hI : I ⊆ LargeEvenInnSet R) {A : Subgroup (MulAut X)} (hind : GGInducedInn A θ I) :
    A ≤ (MulAut.conj : X →* MulAut X).range := by
  rintro a ha
  have h1 : ggInducedAut θ a ∈ I := hind a ha
  obtain ⟨r, hr⟩ := hI h1
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (θ.symm r)
  refine ⟨g, ?_⟩
  apply ggInducedAut_injective_of_perfect hperf θ
  have hgr : θ (g : X ⧸ Subgroup.center X) = r := by
    rw [show (g : X ⧸ Subgroup.center X) = θ.symm r from hg, MulEquiv.apply_symm_apply]
  rw [tpbc_ggInducedAut_conj, hgr]
  exact hr

private theorem tpbc_tag_BC_of_ggLabelIso {lab labL : LargeEvenLabel}
    (h : GGLabelIso lab labL) (htag : labL.tag = .B ∨ labL.tag = .C) (hr : 4 ≤ labL.rank) :
    lab.tag = .B ∨ lab.tag = .C := by
  unfold GGLabelIso at h
  rcases h with rfl | ⟨h1, -⟩ | ⟨-, h2⟩ | ⟨-, h2⟩ | ⟨-, h2⟩ | ⟨-, h2⟩ | ⟨-, h2⟩ | ⟨h2, -⟩
  · exact htag
  · exact h1
  all_goals
    exfalso
    rw [h2] at hr
    simp at hr

private theorem tpbc_mem_inn_of_marking
    {L : Type} [Group L] {E : Subgroup (MulAut L)} {labL : LargeEvenLabel}
    (hΛL : LargeEvenInLambda2 labL) (hBC : labL.tag = .B ∨ labL.tag = .C)
    (hr : 4 ≤ labL.rank)
    (hlabL : GGHasLabel labL (L ⧸ Subgroup.center L))
    (hmark : LargeEvenMarking L (fun _ _ _ I _ θ => GGInducedInn E θ I)) :
    E ≤ (MulAut.conj : L →* MulAut L).range := by
  obtain ⟨hperf, lab, hlab, hraw⟩ := hmark
  obtain ⟨tag, rank, n⟩ := lab
  have hHas : GGHasLabel ⟨tag, rank, n⟩ (L ⧸ Subgroup.center L) :=
    largeEvenRawDatum_mono (fun R _ I F hq => ⟨hq.2.2.choose⟩) hraw
  have hiso : GGLabelIso ⟨tag, rank, n⟩ labL :=
    ggLabelRigidInput_holds ⟨tag, rank, n⟩ labL (L ⧸ Subgroup.center L) hlab hΛL hHas hlabL
  have hBC' : tag = .B ∨ tag = .C := tpbc_tag_BC_of_ggLabelIso hiso hBC hr
  have hInnLab : GGInnerDiagInnLabel ⟨tag, rank, n⟩ :=
    Or.inl (hBC'.elim (fun h => Or.inl h) (fun h => Or.inr (Or.inl h)))
  have hall := largeEvenLabelAll_subset_inn hlab hInnLab
  rcases hBC' with htag | htag
  · subst tag
    obtain ⟨K, _, _, hK, hQ0, hGuard⟩ := hall _ hraw
    obtain ⟨hsimple, hna, θ, hind⟩ := hQ0
    exact tpbc_mem_inn_of_subset_inn hperf θ (hGuard hsimple hna) hind
  · subst tag
    obtain ⟨K, _, _, hK, hQ0, hGuard⟩ := hall _ hraw
    obtain ⟨hsimple, hna, θ, hind⟩ := hQ0
    exact tpbc_mem_inn_of_subset_inn hperf θ (hGuard hsimple hna) hind

@[expose] def TpbcCore : Prop :=
  ∀ (p m n : ℕ), p.Prime → p ≠ 2 → 3 ≤ m → 1 ≤ n →
    ∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 ^ n →
    ∀ (x : StatedSp (m + 1) K) (J E : Subgroup (StatedSp (m + 1) K)),
      x ≠ 1 → x ∈ E → IsElemAbelian p E →
      CFSG.Assembly.IsComponentOf J (Subgroup.centralizer {x}) →
      GGHasLabel ⟨.C, m, n⟩ (↥J ⧸ Subgroup.center ↥J) →
      (∀ e ∈ E, ∀ j ∈ J, e * j = j * e) →
      E ≤ Subgroup.zpowers x

section Transport

private theorem tpbc_mem_center_of_conj_eq_one {X : Type*} [Group X] {z : X}
    (hz : MulAut.conj z = 1) : z ∈ Subgroup.center X := by
  rw [Subgroup.mem_center_iff]
  intro g
  have h1 : z * g * z⁻¹ = g := by
    have := congrArg (fun τ : MulAut X => τ g) hz
    simpa [MulAut.conj_apply] using this
  calc g * z = z * g * z⁻¹ * z := by rw [h1]
    _ = z * g := by group

private theorem tpbc_conj_injective {X : Type*} [Group X] (hZ : Subgroup.center X = ⊥) :
    Function.Injective (MulAut.conj : X →* MulAut X) := by
  intro a b hab
  have h1 : MulAut.conj (a * b⁻¹) = 1 := by
    rw [map_mul, map_inv, hab, mul_inv_cancel]
  have h2 := tpbc_mem_center_of_conj_eq_one h1
  rw [hZ, Subgroup.mem_bot] at h2
  exact mul_inv_eq_one.mp h2

private theorem tpbc_ggAutFixedSubgroup_conj {X : Type*} [Group X] (g : X) :
    ggAutFixedSubgroup (MulAut.conj g : MulAut X) = Subgroup.centralizer ({g} : Set X) := by
  ext l
  rw [mem_ggAutFixedSubgroup, Subgroup.mem_centralizer_singleton_iff, MulAut.conj_apply]
  constructor
  · intro h
    have h' : g * l = l * g := by
      have := congrArg (· * g) h
      simpa [mul_assoc] using this
    exact h'.symm
  · intro h
    rw [← h, mul_assoc, mul_inv_cancel, mul_one]

private theorem tpbc_map_centralizer_singleton {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (d : G) :
    (Subgroup.centralizer ({d} : Set G)).map e.toMonoidHom =
      Subgroup.centralizer ({e d} : Set H) := by
  ext h
  simp only [Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff, MulEquiv.coe_toMonoidHom]
  constructor
  · rintro ⟨g, hg, rfl⟩
    rw [← map_mul, ← map_mul, hg]
  · intro hh
    refine ⟨e.symm h, e.injective ?_, e.apply_symm_apply h⟩
    simpa [map_mul] using hh

private theorem tpbc_isComponentOf_map_mulEquiv {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) {J C : Subgroup G} (h : CFSG.Assembly.IsComponentOf J C) :
    CFSG.Assembly.IsComponentOf (J.map e.toMonoidHom) (C.map e.toMonoidHom) :=
  ⟨Subgroup.map_mono h.1, CFSG.Assembly.IsSubnormal.map e.toMonoidHom h.2.1,
    CFSG.Assembly.IsQuasisimple.of_mulEquiv
      (J.equivMapOfInjective e.toMonoidHom e.injective).symm h.2.2⟩

theorem tpbc_of_core
    (hcore : TpbcCore) : GGI1PairRankOn GGPairBC := by
  intro p hp hp2 L _ _ J y E labL labJ hΛL hΛJ hpair hlabL hlabJ hy hyE hE hcomp hfix hmark
  obtain ⟨tagL, mL, nL⟩ := labL
  obtain ⟨tagJ, m, n⟩ := labJ
  obtain ⟨htagJ, hrankJ, htagL, hrankL, hnL⟩ := hpair
  change tagJ = .B ∨ tagJ = .C at htagJ
  change 3 ≤ m at hrankJ
  change tagL = .B ∨ tagL = .C at htagL
  change mL = m + 1 at hrankL
  change nL = n at hnL
  have hn1 : 1 ≤ n := hΛJ.1
  have hlabL_C : GGHasLabel ⟨.C, m + 1, n⟩ (L ⧸ Subgroup.center L) := by
    rcases htagL with h | h
    · subst h
      rw [hrankL, hnL] at hlabL
      exact (tpbc_hasLabel_B_iff_C (m + 1) n (L ⧸ Subgroup.center L)).mp hlabL
    · subst h
      rw [hrankL, hnL] at hlabL
      exact hlabL
  have hlabJ_C : GGHasLabel ⟨.C, m, n⟩ (↥J ⧸ Subgroup.center ↥J) := by
    rcases htagJ with h | h
    · subst h
      exact (tpbc_hasLabel_B_iff_C m n (↥J ⧸ Subgroup.center ↥J)).mp hlabJ
    · subst h
      exact hlabJ
  have hmodL : StatedClassicalModel (L ⧸ Subgroup.center L) .PSp (m + 1) 2 n :=
    tpbc_statedClassicalModel_of_hasLabel_C (by omega) hn1 hlabL_C
  obtain ⟨φ, hφinj, hφtop⟩ :=
    tpbc_exists_spLift_top (L := L) (n := m + 1) (f := n) (by omega) hmark.1 hmodL
  have hφsurj : Function.Surjective φ := MonoidHom.range_eq_top.mp hφtop
  let α : L ≃* StatedSp (m + 1) (GaloisField 2 n) :=
    (MulEquiv.ofBijective φ ⟨hφinj, hφsurj⟩).symm
  haveI : CharP (GaloisField 2 n) 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega) (GaloisField.card 2 n (by omega))
  have hSpCenter : Subgroup.center (StatedSp (m + 1) (GaloisField 2 n)) = ⊥ :=
    CFSG.ClassicalGroups.Symplectic.center_statedSp_eq_bot_of_charP_two (m := m + 1) (by omega)
  have hZL : Subgroup.center L = ⊥ := by
    apply le_antisymm _ bot_le
    intro z hz
    rw [Subgroup.mem_bot]
    have hz' : α z ∈ Subgroup.center (StatedSp (m + 1) (GaloisField 2 n)) := by
      rw [← Subgroup.map_center_eq α]
      exact Subgroup.mem_map.mpr ⟨z, hz, rfl⟩
    rw [hSpCenter, Subgroup.mem_bot] at hz'
    exact α.injective (by rw [hz', map_one])
  have hinn : E ≤ (MulAut.conj : L →* MulAut L).range :=
    tpbc_mem_inn_of_marking hΛL htagL (by show 4 ≤ mL; omega) hlabL hmark
  obtain ⟨x₀, hx₀⟩ := hinn hyE
  let Ē : Subgroup L := E.comap (MulAut.conj : L →* MulAut L)
  have hĒelem : IsElemAbelian p Ē := hE.comap (tpbc_conj_injective hZL)
  have hx₀Ē : x₀ ∈ Ē := by
    rw [Subgroup.mem_comap, hx₀]
    exact hyE
  have hx₀ne : x₀ ≠ 1 := by
    intro h
    exact hy (by rw [← hx₀, h, map_one])
  let E' : Subgroup (StatedSp (m + 1) (GaloisField 2 n)) := Ē.map α.toMonoidHom
  let J' : Subgroup (StatedSp (m + 1) (GaloisField 2 n)) := J.map α.toMonoidHom
  let x : StatedSp (m + 1) (GaloisField 2 n) := α x₀
  have hE'elem : IsElemAbelian p E' := hĒelem.map α.toMonoidHom
  have hxE' : x ∈ E' := Subgroup.mem_map.mpr ⟨x₀, hx₀Ē, rfl⟩
  have hxne : x ≠ 1 := by
    intro h
    refine hx₀ne (α.injective ?_)
    rw [map_one]
    exact h
  have hcomp₀ : CFSG.Assembly.IsComponentOf J (Subgroup.centralizer ({x₀} : Set L)) := by
    have heq : ggAutFixedSubgroup y = Subgroup.centralizer ({x₀} : Set L) := by
      rw [← hx₀, tpbc_ggAutFixedSubgroup_conj]
    simpa [heq] using hcomp
  have hcomp' : CFSG.Assembly.IsComponentOf J'
      (Subgroup.centralizer ({x} : Set (StatedSp (m + 1) (GaloisField 2 n)))) := by
    have hmap := tpbc_isComponentOf_map_mulEquiv α hcomp₀
    rw [tpbc_map_centralizer_singleton α x₀] at hmap
    exact hmap
  have hJ'lab : GGHasLabel ⟨.C, m, n⟩ (↥J' ⧸ Subgroup.center ↥J') :=
    ggHasLabel_quotCenter_of_mulEquiv
      (J.equivMapOfInjective α.toMonoidHom α.injective) hlabJ_C
  have hfix' : ∀ e ∈ E', ∀ j ∈ J', e * j = j * e := by
    intro e he j hj
    change e ∈ Ē.map α.toMonoidHom at he
    change j ∈ J.map α.toMonoidHom at hj
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp he
    obtain ⟨j₀, hj₀, rfl⟩ := Subgroup.mem_map.mp hj
    have hbE : MulAut.conj b ∈ E := hb
    have hcomm : b * j₀ = j₀ * b := by
      have h := hfix (MulAut.conj b) hbE j₀ hj₀
      rw [MulAut.conj_apply] at h
      have h' := congrArg (· * b) h
      simpa [mul_assoc] using h'
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul α b j₀, ← map_mul α j₀ b, hcomm]
  have hcorele : E' ≤ Subgroup.zpowers x :=
    hcore p m n hp hp2 hrankJ hn1 (GaloisField 2 n) (GaloisField.card 2 n (by omega))
      x J' E' hxne hxE' hE'elem hcomp' hJ'lab hfix'
  have hĒle : Ē ≤ Subgroup.zpowers x₀ := by
    intro b hb
    have hb' : α b ∈ E' := Subgroup.mem_map.mpr ⟨b, hb, rfl⟩
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hcorele hb')
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, α.injective ?_⟩
    rw [map_zpow]
    simpa using hk
  intro e he
  have hmap : Ē.map (MulAut.conj : L →* MulAut L) = E := Subgroup.map_comap_eq_self hinn
  rw [← hmap] at he
  obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp he
  obtain ⟨k, hk⟩ : ∃ k : ℤ, x₀ ^ k = b := Subgroup.mem_zpowers_iff.mp (hĒle hb)
  exact Subgroup.mem_zpowers_iff.mpr ⟨k, by rw [← hk, map_zpow, hx₀]⟩

end Transport

end CFSG.StandardType

end
