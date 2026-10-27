module

public import CFSG.LocalAnalysis.StandardType.GGTBJE6ThreeCore
public import CFSG.LocalAnalysis.StandardType.GGTBJE6ThreeTransfer
public import CFSG.LocalAnalysis.StandardType.GGTBJE6ThreeInstance
public import CFSG.LocalAnalysis.StandardType.GGE6D4LocalDatum
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeIndepDatumOfTor
public import CFSG.LocalAnalysis.StandardType.GGTBJE6ThreeRow
public import CFSG.LocalAnalysis.StandardType.GGTBE6
public import CFSG.LocalAnalysis.StandardType.GGTBTorLiftRowsHolds
public import CFSG.LocalAnalysis.StandardType.GGTBXPlumb

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley TableBExc
  TableBExc.E6Three

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggE6Three_tbGroup_of_label
    (hRig : GGLabelRigidInput) {G : Type} [Group G] [Finite G]
    {Bs X : Subgroup G} (hInn : GGInnerDiagOn Bs X) (hTBat : GGTorusTBAt 3 Bs X) {n : ℕ}
    (hΛ : LargeEvenInLambda2 (⟨.E6, 0, n⟩ : LargeEvenLabel))
    (hXl : GGHasLabel (⟨.E6, 0, n⟩ : LargeEvenLabel) (↥X ⧸ Subgroup.center ↥X))
    (h3 : 3 ∣ 2 ^ n - 1) :
    ∃ (hN : Bs ≤ Subgroup.normalizer (X : Set G)) (K : Type) (_ : Field K) (_ : Finite K)
      (_ : CharP K 2) (ψ₀ : ↥X →* ↥(adjointGroup Tag.E6 K)), 3 ∣ Nat.card K - 1 ∧
      GGTorusTBGroup 3 5 ↥(adjointGroup Tag.E6 K)
        ((hatAut Tag.E6 K).range : Set (MulAut ↥(adjointGroup Tag.E6 K))) ↥X ψ₀
        (ggGamma X hN).range := by
  have hN : Bs ≤ Subgroup.normalizer (X : Set G) := ggInnerDiagOn_le_normalizer hInn
  have hmark := ggInnerDiagOn_relabel hRig hInn hΛ hXl
  have hmark' := largeEvenMarking_and_labelAll
    (S := fun lab' => lab' = (⟨.E6, 0, n⟩ : LargeEvenLabel))
    (P' := fun R _ I _ => ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2)
        (e : R ≃* ↥(adjointGroup Tag.E6 K)), GGTorusLift 3 5 R ∧ 3 ∣ Nat.card K - 1 ∧
          ∀ φ ∈ I, MulAut.congr e φ ∈ (hatAut Tag.E6 K).range)
    (fun lab' _ h' => by
      rw [h']
      exact ggR1E6ThreeRow_labelAll_adjoint rfl h3)
    (fun _ _ _ _ _ _ hP => hP.1) hmark
  obtain ⟨-, lab', -, hraw'⟩ := hmark'
  obtain ⟨R, _, I, F, -, -, θ, ⟨⟨-, -, hind⟩, K, hKF, hKfin, hKchar, e, hlift, h3K, hIe⟩⟩ :=
    largeEvenRawDatum_exists hraw'
  have hBsI : ∀ (b : G) (hb : b ∈ Bs), ggLAut X θ ⟨b, hN hb⟩ ∈ I :=
    fun b hb => ggLAut_mem_of_induces X θ hN hind hb
  exact ⟨hN, K, hKF, hKfin, hKchar, e.toMonoidHom.comp (ggQuotHom θ), h3K,
    GGTorusTBGroup.mulEquiv
      (I' := ((hatAut Tag.E6 K).range : Set (MulAut ↥(adjointGroup Tag.E6 K))))
      e hIe (hTBat 5 θ hN hBsI hlift)⟩

theorem ggE6Three_hKer_of_label
    (hRig : GGLabelRigidInput) {G : Type} [Group G] [Finite G]
    {Bs X : Subgroup G} (hBs : IsElemAbelian 3 Bs) (hInn : GGInnerDiagOn Bs X)
    (hTBat : GGTorusTBAt 3 Bs X) {n : ℕ} (hΛ : LargeEvenInLambda2 (⟨.E6, 0, n⟩ : LargeEvenLabel))
    (hXl : GGHasLabel (⟨.E6, 0, n⟩ : LargeEvenLabel) (↥X ⧸ Subgroup.center ↥X))
    (h3 : 3 ∣ 2 ^ n - 1) (hN : Bs ≤ Subgroup.normalizer (X : Set G)) :
    ∀ m : ↥(X ⊓ Subgroup.normalizer (Bs : Set G)), ggTDρA hN m = 1 → ggTDρB X Bs m = 1 := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hM : 3 ∣ ggTorM (⟨.E6, 0, n⟩ : LargeEvenLabel) := by
    simpa [ggTorM] using h3
  have hrow := GGTBTorRowAt.e6Three (p := 3) (lab := (⟨.E6, 0, n⟩ : LargeEvenLabel)) rfl rfl hM
  obtain ⟨hodd, hpm, hMw, hMC⟩ := l05nPlP1_row_facts hp hp2 hΛ hrow
  obtain ⟨hN', hTor⟩ := ggTorData_of_hasLabel hRig hInn hTBat hΛ hXl
    (ggTBTorE6_holds _ hΛ rfl hM) (ggTBTorLiftRows_holds 3 _ _ _ _ _ _ hp hp2 hΛ hrow)
  obtain ⟨w, hw⟩ := hTor
  intro m hm
  exact ggTD_ker hN hw hp2 hBs m hm

theorem ggTBJE6Levi_threeT_of_label
    (hRig : GGLabelRigidInput) {G : Type} [Group G] [Finite G] {Bs J X : Subgroup G} {g : G}
    (hBs : IsElemAbelian 3 Bs)
    (hSC : ∀ a ∈ Subgroup.centralizer (Bs : Set G), a ^ 3 = 1 → a ∈ Bs)
    (hJX : J ≤ X) (hgBs : g ∈ Bs) (hJg : J ≤ Subgroup.centralizer ({g} : Set G))
    (hgX : ∃ l ∈ X, g * l * g⁻¹ ≠ l)
    (hcomp : IsComponentOf J (X ⊓ Subgroup.centralizer ({g} : Set G)))
    (bX : ↥Bs) (hbX1 : bX ≠ 1) (hbXc : (bX : G) ∈ Subgroup.centralizer (X : Set G))
    (hcardJ : Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) ≤ 3 ^ 3)
    (hInn : GGInnerDiagOn Bs X) (hTBat : GGTorusTBAt 3 Bs X) {n : ℕ}
    (hΛ : LargeEvenInLambda2 (⟨.E6, 0, n⟩ : LargeEvenLabel))
    (hXl : GGHasLabel (⟨.E6, 0, n⟩ : LargeEvenLabel) (↥X ⧸ Subgroup.center ↥X))
    (h3 : 3 ∣ 2 ^ n - 1) {labJ : LargeEvenLabel} (hΛJ : LargeEvenInLambda2 labJ)
    (hJlab : GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J))
    (hD4 : ¬ (labJ.tag = .D ∧ labJ.rank = 4)) :
    GGResSideDatum 3 Bs X J ∨ GGResLeviSideDatumLE3 3 Bs X J := by
  obtain ⟨hN, K, hKF, hKfin, hKchar, ψ₀, h3K, hTB⟩ :=
    ggE6Three_tbGroup_of_label hRig hInn hTBat hΛ hXl h3
  have hKer := ggE6Three_hKer_of_label hRig hBs hInn hTBat hΛ hXl h3 hN
  obtain ⟨κ, hF, hCall⟩ := ggE6Three_frameClass_of_tb h3K hTB
  have hC := ggE6Three_coordData_of_frameA hBs hSC hN hgBs hJX hgX hcomp hKer hF
    (P := fun J' => ∃ m : ℕ, 1 ≤ m ∧
      GGHasLabel (⟨.D, 4, m⟩ : LargeEvenLabel) (↥J' ⧸ Subgroup.center ↥J')) hCall
  refine ggTBJE6Levi_of_threeCoordData hgBs hJX hJg hC ?_ bX hbX1 hbXc hcardJ
  rintro ⟨m, hm, hlab⟩
  have hJperf : Group.IsPerfect ↥J := ⟨hcomp.2.2.1⟩
  have hlabJ : GGHasLabel (⟨.D, 4, m⟩ : LargeEvenLabel) (↥J ⧸ Subgroup.center ↥J) :=
    ggHasLabel_quotCenter_of_central_cover hJperf
      (Subgroup.subgroupOfEquivOfLe hJX).symm.toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hJX).symm.surjective
      (fun z hz => by
        rw [(MulEquiv.map_eq_one_iff _).mp (MonoidHom.mem_ker.mp hz)]
        exact Subgroup.one_mem _) hlab
  have hiso := hRig labJ (⟨.D, 4, m⟩ : LargeEvenLabel) (↥J ⧸ Subgroup.center ↥J) hΛJ
    ⟨hm, (by norm_num : 3 ≤ 4)⟩ hJlab hlabJ
  apply hD4
  rcases hiso with h | h | h | h | h | h | h | h
  · rw [h]
    exact ⟨rfl, rfl⟩
  all_goals (exfalso; simp at h)

end CFSG.StandardType

end
