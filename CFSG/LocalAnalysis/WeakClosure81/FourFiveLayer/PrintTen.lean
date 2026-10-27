module

public import CFSG.Quasithin.Background.RonanE111WrP
public import CFSG.LocalAnalysis.UniquenessCase.UCFront12
import CFSG.Quasithin.Vol2.Ch11SecBRootLiftAux
import CFSG.Quasithin.Background.RonanE51Two
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.ClassicalGroups
public import CFSG.Holt.General.Basic
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporJ4Quot
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeListed
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeThree
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19Defs
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2
public import CFSG.Quasithin.Background.A3Structure318Red
public import CFSG.Quasithin.Background.A3Structure36A
public import CFSG.Quasithin.Background.A3Structure36BAction
public import CFSG.Quasithin.Background.A3Structure36BBase
public import CFSG.Quasithin.Background.A3Structure36BCase3Base
public import CFSG.Quasithin.Background.A3Structure36BCasesBase
public import CFSG.Quasithin.Background.A3Structure36BCommonBase
public import CFSG.Quasithin.Background.A3Structure36BFrattini
public import CFSG.Quasithin.Background.A3Structure36BHeisBase
public import CFSG.Quasithin.Background.A3Structure36BHomocyclic
public import CFSG.Quasithin.Background.A3Structure36BPrimeDataBase
public import CFSG.Quasithin.Background.A3Structure36BStarBase
public import CFSG.Quasithin.Background.A3Structure36Base
public import CFSG.Quasithin.Background.A3Structure37Base
public import CFSG.Quasithin.Background.A3Structure37Comm
public import CFSG.Quasithin.Background.A3Structure37Frattini
public import CFSG.Quasithin.Background.A3Structure37KeyBase
public import CFSG.Quasithin.Background.A3Structure37Schur
public import CFSG.Quasithin.Background.A3Structure38Part3
public import CFSG.Quasithin.Background.B216Quotient
public import CFSG.Quasithin.Background.B6
public import CFSG.Quasithin.Background.B6Example
public import CFSG.Quasithin.Background.C2Inputs
public import CFSG.Quasithin.Background.D2
public import CFSG.Quasithin.Background.D2Dihedral
public import CFSG.Quasithin.Background.E2Hyp
public import CFSG.Quasithin.Background.E2SolvTwo
public import CFSG.Quasithin.Background.E2TwoProofDefs
public import CFSG.Quasithin.Background.E3OffenderB
public import CFSG.Quasithin.Background.F2Equiv
public import CFSG.Quasithin.Background.F9FiveStruct
public import CFSG.Quasithin.Background.F9G2
public import CFSG.Quasithin.Background.F9Geometry
public import CFSG.Quasithin.Background.RonanE111Defs
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtF112ListC
public import CFSG.Quasithin.EmptyFaithful.S14117
public import CFSG.Quasithin.EmptyFaithful.S14117Coprime
public import CFSG.Quasithin.EmptyFaithful.S14117Rank
public import CFSG.Quasithin.EmptyFaithful.S142Statements
public import CFSG.Quasithin.EmptyFaithful.S152N11
public import CFSG.Quasithin.H13.A5S1326
public import CFSG.Quasithin.H13.A5Top
public import CFSG.Quasithin.Vol2.Ch10StatementsE
public import CFSG.Quasithin.Vol2.Ch10StatementsInputs
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS2
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS3
public import CFSG.Quasithin.Vol2.Ch11SecBNPCaseS
public import CFSG.Quasithin.Vol2.Ch11SecBTCIso
public import CFSG.Quasithin.Vol2.Ch11StatementsE
public import CFSG.Quasithin.Vol2.Ch11StatementsInputsAS
public import CFSG.Quasithin.Vol2.Ch11StatementsInputsAS2
public import CFSG.Sporadic.Schreier.J4SProfileNode
import CFSG.Quasithin.Vol2.Ch6Defs

public section

namespace CFSG.LocalAnalysis.WeakClosure81.FourFiveLayer

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.Quasithin.E1 CFSG.QuasithinUnique
  CFSG.Quasithin.E2.E22N CFSG.Quasithin.E2.E22N.E111R CFSG.Quasithin.RonanE111
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem isSolvable_of_twoResidual_eq_map_tenS {J Y : Subgroup G} [Y.Normal]
    {I : Subgroup (G ⧸ Y)} (hY : Group.IsSolvable ↥Y) (hI : Group.IsSolvable ↥I)
    (hres : twoResidual I = (twoResidual J).map (QuotientGroup.mk' Y)) :
    Group.IsSolvable ↥J := by
  set π := QuotientGroup.mk' Y with hπ
  haveI := hY
  have hJY : Group.IsSolvable ↥(twoResidual J ⊓ Y) :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion inf_le_right)
      (Subgroup.inclusion_injective _)
  haveI := hI
  have hIres : Group.IsSolvable ↥(twoResidual I) :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion (twoResidual_le I))
      (Subgroup.inclusion_injective _)
  have hmap : ∀ x : ↥(twoResidual J), π (x : G) ∈ twoResidual I := by
    intro x
    rw [hres]
    exact Subgroup.mem_map_of_mem π x.2
  let f : ↥(twoResidual J) →* ↥(twoResidual I) :=
    (π.comp (twoResidual J).subtype).codRestrict _ hmap
  have hker : f.ker = (twoResidual J ⊓ Y).subgroupOf (twoResidual J) := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun hx => ⟨x.2, (QuotientGroup.eq_one_iff _).mp (congrArg Subtype.val hx)⟩,
      fun hx => Subtype.ext ((QuotientGroup.eq_one_iff _).mpr hx.2)⟩
  have hle : f.ker ≤
      (Subgroup.inclusion (inf_le_left : twoResidual J ⊓ Y ≤ twoResidual J)).range := by
    rw [hker, Subgroup.inclusion_range]
  haveI := hJY
  haveI := hIres
  exact RonanE51.isSolvable_of_twoResidual (Group.isSolvable_of_ker_le_range _ f hle)

private theorem isEP_of_isE_tenS {n : ℕ} (hn : 1 ≤ n) {T A K : Subgroup G} (hK : E1.IsE 1 ⊤ T A K)
    (hKs : Group.IsSolvable ↥K) : UniquenessCase.UC22.F12.IsEP n ⊤ T A K := by
  have h := E1.IsE.mono hn hK
  exact ⟨h.1, h.2.1, h.2.2.1, Or.inl (E1.isE_eOne_of_isSolvable h hKs)⟩

private theorem ten_eight_bot_centralizer_tenS {A Y₁ : Subgroup G} [Y₁.Normal]
    (hcomm : perfectCore (⊤ : Subgroup G) = ⁅perfectCore (⊤ : Subgroup G), A⁆)
    (hYA0 : ⁅Y₁, A⁆ = ⊥) :
    perfectCore (⊤ : Subgroup G) ≤ Subgroup.centralizer (Y₁ : Set G) := by
  have hAc : A ≤ Subgroup.centralizer (Y₁ : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (by rw [Subgroup.commutator_comm]; exact hYA0)
  have hCnorm : ∀ g c : G, c ∈ Subgroup.centralizer (Y₁ : Set G) →
      g * c * g⁻¹ ∈ Subgroup.centralizer (Y₁ : Set G) := by
    intro g c hc
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro y hy
    have hy' : g⁻¹ * y * g ∈ Y₁ := by
      have := Subgroup.Normal.conj_mem inferInstance y hy g⁻¹
      simpa using this
    have h1 := hc _ hy'
    calc y * (g * c * g⁻¹) = g * ((g⁻¹ * y * g) * c) * g⁻¹ := by group
      _ = g * (c * (g⁻¹ * y * g)) * g⁻¹ := by rw [h1]
      _ = (g * c * g⁻¹) * y := by group
  calc perfectCore (⊤ : Subgroup G) = ⁅perfectCore (⊤ : Subgroup G), A⁆ := hcomm
    _ ≤ Subgroup.centralizer (Y₁ : Set G) := by
      refine Subgroup.commutator_le.mpr fun p hp a ha => ?_
      have e : ⁅p, a⁆ = (p * a * p⁻¹) * a⁻¹ := rfl
      rw [e]
      exact Subgroup.mul_mem _ (hCnorm p a (hAc ha)) (Subgroup.inv_mem _ (hAc ha))

private theorem ten_eight_bot_le_perfect_tenS {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hres : twoResidual (⊤ : Subgroup G) = perfectCore (⊤ : Subgroup G))
    {Y₁ : Subgroup G} (hY₁ : IsPGroup r Y₁) : Y₁ ≤ perfectCore (⊤ : Subgroup G) := by
  intro y hy
  obtain ⟨k, hk⟩ := hY₁ ⟨y, hy⟩
  have hyk : y ^ r ^ k = 1 := by simpa using congrArg Subtype.val hk
  obtain ⟨j, hj⟩ := twoResidual_isTwoQuotient (⊤ : Subgroup G) y (Subgroup.mem_top y)
  rw [← hres]
  exact E1.mem_of_pow_mem_two_p hr hr2 (by rw [hyk]; exact Subgroup.one_mem _) hj

private theorem ten_eight_bot_perfect_le_sup_tenS {Y₁ J₁ : Subgroup G} [Y₁.Normal]
    (hJY : J₁ ⊔ Y₁ = ⊤) :
    perfectCore (⊤ : Subgroup G) ≤ perfectCore J₁ ⊔ Y₁ := by
  set P := perfectCore (⊤ : Subgroup G) with hP
  set P₁ := perfectCore J₁ with hP₁
  have hπ : (⊤ : Subgroup G).map (QuotientGroup.mk' Y₁) = J₁.map (QuotientGroup.mk' Y₁) := by
    have h1 : (J₁ ⊔ Y₁).map (QuotientGroup.mk' Y₁) = J₁.map (QuotientGroup.mk' Y₁) := by
      rw [Subgroup.map_sup, (Subgroup.map_eq_bot_iff Y₁).mpr (QuotientGroup.ker_mk' Y₁).ge,
        sup_bot_eq]
    rw [← h1, hJY]
  have h1 : P.map (QuotientGroup.mk' Y₁) = P₁.map (QuotientGroup.mk' Y₁) := by
    rw [hP, hP₁, map_perfectCore, map_perfectCore, hπ]
  calc P ≤ (P.map (QuotientGroup.mk' Y₁)).comap (QuotientGroup.mk' Y₁) :=
        Subgroup.le_comap_map _ _
    _ = (P₁.map (QuotientGroup.mk' Y₁)).comap (QuotientGroup.mk' Y₁) := by rw [h1]
    _ = P₁ ⊔ Y₁ := by rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk']

private theorem ten_eight_bot_finish_tenS {Y₁ J₁ : Subgroup G} [Y₁.Normal]
    (hPC : perfectCore (⊤ : Subgroup G) ≤ Subgroup.centralizer (Y₁ : Set G))
    (hY₁P : Y₁ ≤ perfectCore (⊤ : Subgroup G))
    (hPle : perfectCore (⊤ : Subgroup G) ≤ perfectCore J₁ ⊔ Y₁)
    (hY₁ab : ∀ a ∈ Y₁, ∀ b ∈ Y₁, a * b = b * a) : Y₁ ≤ J₁ := by
  set P := perfectCore (⊤ : Subgroup G) with hP
  set P₁ := perfectCore J₁ with hP₁
  have hP₁P : P₁ ≤ P := perfectCore_mono le_top
  have hYP₁ : Y₁ ≤ Subgroup.normalizer (P₁ : Set G) := by
    intro y hy
    apply E1.mem_normalizer_of_conj_mem
    intro p hp
    have h1 : y * p = p * y := Subgroup.mem_centralizer_iff.mp (hPC (hP₁P hp)) y hy
    have e : y * p * y⁻¹ = p := by
      calc y * p * y⁻¹ = (p * y) * y⁻¹ := by rw [h1]
        _ = p := by group
    rw [e]
    exact hp
  have hUnorm : P₁ ⊔ Y₁ ≤ Subgroup.normalizer (P₁ : Set G) :=
    sup_le Subgroup.le_normalizer hYP₁
  have hP₁U : (P₁.subgroupOf (P₁ ⊔ Y₁)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr hUnorm
  have hY₁solv : Group.IsSolvable Y₁ := by
    have : IsMulCommutative ↥Y₁ := ⟨⟨fun a b => Subtype.ext (hY₁ab a a.2 b b.2)⟩⟩
    infer_instance
  have hperfU : P ≤ perfectCore (P₁ ⊔ Y₁) :=
    le_perfectCore_of_perfect hPle (perfectCore_perfect ⊤)
  have hPP₁ : P ≤ P₁ :=
    hperfU.trans (perfectCore_le_of_sup_solvable le_sup_left hP₁U rfl hY₁solv)
  exact (hY₁P.trans hPP₁).trans (perfectCore_le J₁)

private theorem ten_eight_step_ne_bot_tenS {A Y₁ J₁ : Subgroup G} [Y₁.Normal]
    (hY₁ab : ∀ a ∈ Y₁, ∀ b ∈ Y₁, a * b = b * a)
    (hmin : ∀ K : Subgroup G, K.Normal → K ≤ Y₁ → K ≠ ⊥ → K = Y₁)
    (hJY : J₁ ⊔ Y₁ = ⊤) (hYA : ⁅Y₁, A⁆ ≤ J₁) (hYA0 : ⁅Y₁, A⁆ ≠ ⊥) : Y₁ ≤ J₁ := by
  have hnormY : ∀ g : G, g ∈ Subgroup.normalizer (Y₁ : Set G) := fun g => by
    rw [Subgroup.normalizer_eq_top_iff.mpr inferInstance]
    exact Subgroup.mem_top g
  have hcommY : ⁅Y₁, A⁆ ≤ Y₁ := Subgroup.commutator_le.mpr fun n hn a ha => by
    have e : ⁅n, a⁆ = n * (a * n⁻¹ * a⁻¹) := by simp only [commutatorElement_def]; group
    rw [e]
    exact Y₁.mul_mem hn (Subgroup.Normal.conj_mem inferInstance n⁻¹ (Y₁.inv_mem hn) a)
  set N := Subgroup.normalClosure ((⁅Y₁, A⁆ : Subgroup G) : Set G) with hN
  have hNY : N ≤ Y₁ := Subgroup.normalClosure_le_normal hcommY
  have hNne : N ≠ ⊥ := fun h => hYA0 (le_bot_iff.mp (Subgroup.le_normalClosure.trans h.le))
  have hNeq : N = Y₁ := hmin N inferInstance hNY hNne
  have hNJ : N ≤ J₁ := by
    rw [hN, Subgroup.normalClosure, Subgroup.closure_le]
    intro g hg
    obtain ⟨z, hz, hconj⟩ := Group.mem_conjugatesOfSet_iff.mp hg
    obtain ⟨c, hc⟩ := isConj_iff.mp hconj
    have hcmem : c ∈ (↑(J₁ ⊔ Y₁) : Set G) := by
      rw [hJY]
      exact Subgroup.mem_top c
    rw [Subgroup.coe_mul_of_left_le_normalizer_right J₁ Y₁ (fun x _ => hnormY x)] at hcmem
    obtain ⟨j, hj, y, hy, hjy⟩ := hcmem
    have hzY : z ∈ Y₁ := hcommY hz
    have e : g = j * z * j⁻¹ := by
      rw [← hc, ← hjy]
      have hyz : y * z = z * y := hY₁ab y hy z hzY
      calc j * y * z * (j * y)⁻¹ = j * (y * z) * y⁻¹ * j⁻¹ := by group
        _ = j * (z * y) * y⁻¹ * j⁻¹ := by rw [hyz]
        _ = j * z * j⁻¹ := by group
    rw [e]
    exact J₁.mul_mem (J₁.mul_mem hj (hYA hz)) (J₁.inv_mem hj)
  rw [← hNeq]
  exact hNJ

private theorem ten_eight_step_tenS {r : ℕ} {T A Y₁ J₁ : Subgroup G} [Y₁.Normal]
    (hT : IsSylowIn 2 T ⊤) (hA : A ≤ T) (hAab : IsElemAbelian 2 A)
    (hres : twoResidual (⊤ : Subgroup G) = perfectCore (⊤ : Subgroup G))
    (hcomm : perfectCore (⊤ : Subgroup G) = ⁅perfectCore (⊤ : Subgroup G), A⁆) (hr : r.Prime)
    (hY₁ : IsPGroup r Y₁) (hY₁ab : ∀ a ∈ Y₁, ∀ b ∈ Y₁, a * b = b * a)
    (hmin : ∀ K : Subgroup G, K.Normal → K ≤ Y₁ → K ≠ ⊥ → K = Y₁) (hTJ : T ≤ J₁)
    (hJY : J₁ ⊔ Y₁ = ⊤)
    (hE : ⨆ K ∈ {K : Subgroup G | E1.IsE 1 ⊤ T A K ∧ Group.IsSolvable ↥K}, K ≤ J₁) :
    Y₁ ≤ J₁ := by
  by_cases hr2 : r = 2
  · subst hr2
    have : Fact (Nat.Prime 2) := ⟨hr⟩
    exact (hT.le_of_normal le_top inferInstance hY₁).trans hTJ
  have hYA : ⁅Y₁, A⁆ ≤ J₁ := by
    refine (E1.comm_le_iSup_twoResidual hr hr2 hT hA hAab hY₁).trans ?_
    refine iSup₂_le fun K hK => (twoResidual_le K).trans ?_
    exact (le_iSup₂_of_le K ⟨hK.1, E1.RootLift.isSolvable_of_eOne hK.2.1⟩ le_rfl).trans hE
  by_cases hYA0 : ⁅Y₁, A⁆ = ⊥
  · exact ten_eight_bot_finish_tenS (ten_eight_bot_centralizer_tenS hcomm hYA0)
      (ten_eight_bot_le_perfect_tenS hr hr2 hres hY₁) (ten_eight_bot_perfect_le_sup_tenS hJY)
      hY₁ab
  · exact ten_eight_step_ne_bot_tenS hY₁ab hmin hJY hYA hYA0

private def TenSInduction_tenS (n : ℕ) : Prop :=
  ∀ (G' : Type) [Group G'] [Finite G'], Nat.card G' ≤ n →
    ∀ {T A Y J : Subgroup G'} [Y.Normal], IsSylowIn 2 T ⊤ → A ≤ T →
      IsElemAbelian 2 A →
      twoResidual (⊤ : Subgroup G') = perfectCore (⊤ : Subgroup G') →
      perfectCore (⊤ : Subgroup G') = ⁅perfectCore (⊤ : Subgroup G'), A⁆ →
      Group.IsSolvable ↥Y → T ≤ J → J ⊔ Y = ⊤ →
      J ⊔ (⨆ K ∈ {K : Subgroup G' | E1.IsE 1 ⊤ T A K ∧ Group.IsSolvable ↥K}, K) = ⊤

private theorem ten_eight_quotient_tenS {A Y J Y₁ : Subgroup G} [Y₁.Normal]
    (hY : Group.IsSolvable ↥Y)
    (hres : twoResidual (⊤ : Subgroup G) = perfectCore (⊤ : Subgroup G))
    (hcomm : perfectCore (⊤ : Subgroup G) = ⁅perfectCore (⊤ : Subgroup G), A⁆)
    (hJY : J ⊔ Y = ⊤) :
    Group.IsSolvable ↥(Y.map (QuotientGroup.mk' Y₁)) ∧
      twoResidual (⊤ : Subgroup (G ⧸ Y₁)) = perfectCore (⊤ : Subgroup (G ⧸ Y₁)) ∧
      perfectCore (⊤ : Subgroup (G ⧸ Y₁)) =
        ⁅perfectCore (⊤ : Subgroup (G ⧸ Y₁)), A.map (QuotientGroup.mk' Y₁)⁆ ∧
      J.map (QuotientGroup.mk' Y₁) ⊔ Y.map (QuotientGroup.mk' Y₁) = ⊤ := by
  set π := QuotientGroup.mk' Y₁ with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective Y₁
  haveI := hY
  have hYs : Group.IsSolvable ↥(Y.map π) :=
    Group.isSolvable_of_surjective (π.subgroupMap_surjective Y)
  have hres' : twoResidual (⊤ : Subgroup (G ⧸ Y₁)) = perfectCore (⊤ : Subgroup (G ⧸ Y₁)) := by
    have h1 := congrArg (Subgroup.map π) hres
    rw [E1.map_twoResidual π ⊤, map_perfectCore π ⊤, Subgroup.map_top_of_surjective π hπs] at h1
    exact h1
  have hcomm' : perfectCore (⊤ : Subgroup (G ⧸ Y₁)) =
      ⁅perfectCore (⊤ : Subgroup (G ⧸ Y₁)), A.map π⁆ := by
    have h1 := congrArg (Subgroup.map π) hcomm
    rw [Subgroup.map_commutator, map_perfectCore π ⊤,
      Subgroup.map_top_of_surjective π hπs] at h1
    exact h1
  have hJY' : J.map π ⊔ Y.map π = ⊤ := by
    rw [← Subgroup.map_sup, hJY, Subgroup.map_top_of_surjective π hπs]
  exact ⟨hYs, hres', hcomm', hJY'⟩

private theorem ten_eight_map_top_tenS {T A J J₁ Y₁ : Subgroup G} [Y₁.Normal]
    (hY₁solv : Group.IsSolvable ↥Y₁) (hT : IsSylowIn 2 T ⊤) (hA : A ≤ T)
    (hAab : IsElemAbelian 2 A) (hTJ : T ≤ J)
    (hJ₁ : J₁ = J ⊔ ⨆ K ∈ {K : Subgroup G | E1.IsE 1 ⊤ T A K ∧ Group.IsSolvable ↥K}, K)
    (hIH : J.map (QuotientGroup.mk' Y₁) ⊔
      ⨆ K ∈ {K : Subgroup (G ⧸ Y₁) | E1.IsE 1 ⊤ (T.map (QuotientGroup.mk' Y₁))
        (A.map (QuotientGroup.mk' Y₁)) K ∧ Group.IsSolvable ↥K}, K = ⊤) :
    J₁.map (QuotientGroup.mk' Y₁) = ⊤ := by
  set π := QuotientGroup.mk' Y₁ with hπ
  refine top_le_iff.mp ?_
  rw [← hIH]
  refine sup_le ?_ (iSup₂_le fun K hK => ?_)
  rw [hJ₁]
  exact Subgroup.map_mono le_sup_left
  obtain ⟨J', hJ', hJ'K⟩ := E1.ten_seven hT hA hAab hK.1
  have hJ'solv : Group.IsSolvable ↥J' :=
    isSolvable_of_twoResidual_eq_map_tenS hY₁solv
      (E1.RootLift.isSolvable_of_eOne (E1.isE_eOne_of_isSolvable hK.1 hK.2).1) hJ'K
  have hJ'J₁ : J' ≤ J₁ := by
    rw [hJ₁]
    exact (le_iSup₂_of_le (f := fun K (_ : K ∈ {K : Subgroup G | E1.IsE 1 ⊤ T A K ∧
      Group.IsSolvable ↥K}) => K) J' ⟨hJ', hJ'solv⟩ le_rfl).trans le_sup_right
  have hTJ₁ : T ≤ J₁ := by
    rw [hJ₁]
    exact hTJ.trans le_sup_left
  calc K ≤ twoResidual K ⊔ (T.map π ⊓ K) :=
        E1.le_twoResidual_sup_of_isSylowIn hK.1.2.2.1
    _ ≤ (twoResidual J').map π ⊔ T.map π := by
      rw [hJ'K]
      exact sup_le_sup le_rfl inf_le_left
    _ ≤ J₁.map π := sup_le (Subgroup.map_mono ((twoResidual_le J').trans hJ'J₁))
      (Subgroup.map_mono hTJ₁)

private theorem ten_eight_succ_setup_tenS {n : ℕ} (ih : TenSInduction_tenS n)
    {T A Y J J₁ Y₁ : Subgroup G} [Y.Normal] [Y₁.Normal]
    (hY : Group.IsSolvable ↥Y) (hY₁solv : Group.IsSolvable ↥Y₁)
    (hcardlt : Nat.card (G ⧸ Y₁) ≤ n)
    (hT : IsSylowIn 2 T ⊤) (hA : A ≤ T) (hAab : IsElemAbelian 2 A)
    (hres : twoResidual (⊤ : Subgroup G) = perfectCore (⊤ : Subgroup G))
    (hcomm : perfectCore (⊤ : Subgroup G) = ⁅perfectCore (⊤ : Subgroup G), A⁆)
    (hTJ : T ≤ J) (hJY : J ⊔ Y = ⊤)
    (hJ₁ : J₁ = J ⊔ ⨆ K ∈ {K : Subgroup G | E1.IsE 1 ⊤ T A K ∧ Group.IsSolvable ↥K}, K) :
    J₁ ⊔ Y₁ = ⊤ := by
  set π := QuotientGroup.mk' Y₁ with hπ
  have hYnorm : Y.Normal := inferInstance
  have hYn : (Y.map π).Normal :=
    Subgroup.Normal.map hYnorm π (QuotientGroup.mk'_surjective Y₁)
  obtain ⟨hYs, hres', hcomm', hJY'⟩ :=
    ten_eight_quotient_tenS (Y₁ := Y₁) hY hres hcomm hJY
  haveI := hYn
  have hIH := ih (G ⧸ Y₁) hcardlt (T := T.map π) (A := A.map π) (Y := Y.map π)
    (J := J.map π) (E1.isSylowIn_two_map_top (QuotientGroup.mk'_surjective Y₁) hT)
    (Subgroup.map_mono hA) (E1.isElemAbelian_map' π hAab) hres' hcomm' hYs
    (Subgroup.map_mono hTJ) hJY'
  have hπJ₁ := ten_eight_map_top_tenS hY₁solv hT hA hAab hTJ hJ₁ hIH
  have h := Subgroup.comap_map_eq π J₁
  rw [hπJ₁, Subgroup.comap_top, QuotientGroup.ker_mk'] at h
  exact h.symm

private theorem ten_eight_succ_tenS {n : ℕ} (ih : TenSInduction_tenS n)
    {T A Y J : Subgroup G} [Y.Normal] (hn : Nat.card G ≤ n + 1)
    (hT : IsSylowIn 2 T ⊤) (hA : A ≤ T) (hAab : IsElemAbelian 2 A)
    (hres : twoResidual (⊤ : Subgroup G) = perfectCore (⊤ : Subgroup G))
    (hcomm : perfectCore (⊤ : Subgroup G) = ⁅perfectCore (⊤ : Subgroup G), A⁆)
    (hY : Group.IsSolvable ↥Y) (hTJ : T ≤ J) (hJY : J ⊔ Y = ⊤) :
    J ⊔ (⨆ K ∈ {K : Subgroup G | E1.IsE 1 ⊤ T A K ∧ Group.IsSolvable ↥K}, K) = ⊤ := by
  set J₁ := J ⊔ (⨆ K ∈ {K : Subgroup G | E1.IsE 1 ⊤ T A K ∧ Group.IsSolvable ↥K}, K) with hJ₁
  by_cases hYbot : Y = ⊥
  · rw [hYbot, sup_bot_eq] at hJY
    exact top_le_iff.mp (hJY ▸ le_sup_left)
  · obtain ⟨Y₁, hY₁n, hY₁Y, hY₁ne, hY₁min⟩ :=
      CFSG.exists_minimal_normal_le Y inferInstance hYbot
    have : Y₁.Normal := hY₁n
    have hY₁solv : Group.IsSolvable Y₁ :=
      Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hY₁Y)
        (Subgroup.inclusion_injective hY₁Y)
    have hIM : CFSG.IsMinimalNormal Y₁ := ⟨fun K _ hKY => by
      by_cases hK : K = ⊥
      · exact Or.inl hK
      · exact Or.inr (hY₁min K ‹_› hKY hK)⟩
    obtain ⟨r, hr, hEA⟩ := CFSG.minimalNormal_solvable_exists_isElementaryAbelian Y₁
    have hY₁p : IsPGroup r Y₁ := CFSG.IsElementaryAbelian.isPGroup r Y₁
    have hY₁ab : ∀ a ∈ Y₁, ∀ b ∈ Y₁, a * b = b * a := fun a ha b hb =>
      congrArg Subtype.val (hEA.toIsMulCommutative.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
    have hcardlt : Nat.card (G ⧸ Y₁) ≤ n := by
      have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup Y₁
      have h2 : 1 < Nat.card Y₁ := (Subgroup.one_lt_card_iff_ne_bot Y₁).mpr hY₁ne
      have h3 := Nat.card_pos (α := G ⧸ Y₁)
      nlinarith
    have hJ₁Y₁ : J₁ ⊔ Y₁ = ⊤ := ten_eight_succ_setup_tenS ih hY hY₁solv hcardlt hT hA
      hAab hres hcomm hTJ hJY hJ₁
    have hE : ⨆ K ∈ {K : Subgroup G | E1.IsE 1 ⊤ T A K ∧ Group.IsSolvable ↥K}, K ≤ J₁ := by
      rw [hJ₁]
      exact le_sup_right
    have hY₁J₁ : Y₁ ≤ J₁ := ten_eight_step_tenS hT hA hAab hres hcomm hr hY₁p hY₁ab hY₁min
      (hTJ.trans le_sup_left) hJ₁Y₁ hE
    rw [← hJ₁Y₁]
    exact (sup_eq_left.mpr hY₁J₁).symm

private theorem ten_eight_aux_tenS (n : ℕ) : TenSInduction_tenS n := by
  induction n with
  | zero =>
    intro G' _ _ h
    exact absurd h (by have := Nat.card_pos (α := G'); omega)
  | succ n ih =>
    intro G' _ _ hn T A Y J _ hT hA hAab hres hcomm hY hTJ hJY
    exact ten_eight_succ_tenS (G := G') ih hn hT hA hAab hres hcomm hY hTJ hJY

theorem ten_eight_auxS {T A Y J : Subgroup G} [Y.Normal] (hT : IsSylowIn 2 T ⊤) (hA : A ≤ T)
    (hAab : IsElemAbelian 2 A)
    (hres : twoResidual (⊤ : Subgroup G) = perfectCore (⊤ : Subgroup G))
    (hcomm : perfectCore (⊤ : Subgroup G) = ⁅perfectCore (⊤ : Subgroup G), A⁆)
    (hY : Group.IsSolvable ↥Y) (hTJ : T ≤ J) (hJY : J ⊔ Y = ⊤) :
    J ⊔ (⨆ K ∈ {K : Subgroup G | E1.IsE 1 ⊤ T A K ∧ Group.IsSolvable ↥K}, K) = ⊤ :=
  ten_eight_aux_tenS (Nat.card G) G le_rfl hT hA hAab hres hcomm hY hTJ hJY

theorem ten_sixS {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {T A X Y : Subgroup G} [X.Normal]
    [Y.Normal] (hT : IsSylowIn 2 T ⊤) (hA : A ≤ T) (hAab : IsElemAbelian 2 A)
    (hY : Group.IsSolvable ↥Y) (hXp : IsPGroup p (X.map (QuotientGroup.mk' Y)))
    (hXA : ⁅X.map (QuotientGroup.mk' Y), A.map (QuotientGroup.mk' Y)⁆ =
      X.map (QuotientGroup.mk' Y)) :
    X ≤ (⨆ K ∈ {K : Subgroup G | E1.IsE 1 ⊤ T A K ∧ Group.IsSolvable ↥K}, K) ⊔ Y := by
  set π := QuotientGroup.mk' Y with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective Y
  set Xb : Subgroup (G ⧸ Y) := X.map π with hXb
  set Ab : Subgroup (G ⧸ Y) := A.map π with hAb
  have hXbn : Xb.Normal := Subgroup.Normal.map inferInstance π hπs
  have hTb : IsSylowIn 2 (T.map π) ⊤ := E1.isSylowIn_two_map_top hπs hT
  have hAbT : Ab ≤ T.map π := Subgroup.map_mono hA
  have hAbab : IsElemAbelian 2 Ab := E1.isElemAbelian_map' π hAab
  have key : Xb ≤ (⨆ K ∈ {K : Subgroup G | E1.IsE 1 ⊤ T A K ∧ Group.IsSolvable ↥K}, K).map π := by
    calc Xb = ⁅Xb, Ab⁆ := hXA.symm
      _ ≤ ⨆ K ∈ {K : Subgroup (G ⧸ Y) | E1.IsE 1 ⊤ (T.map π) Ab K ∧
          EOne ↥K (Ab.subgroupOf K) ∧ Nat.card (barO2 ↥K (Ab.subgroupOf K)) ≤ 2 ^ 1},
          twoResidual K := E1.comm_le_iSup_twoResidual hp hp2 hTb hAbT hAbab hXp
      _ ≤ _ := by
        refine iSup₂_le fun K hK => ?_
        obtain ⟨J, hJ, hJK⟩ := E1.ten_seven_eOne hT hA hAab hK.1 ⟨hK.2.1, hK.2.2⟩
        have hJs : Group.IsSolvable ↥J :=
          isSolvable_of_twoResidual_eq_map_tenS hY (E1.RootLift.isSolvable_of_eOne hK.2.1) hJK
        rw [hJK]
        exact (Subgroup.map_mono (twoResidual_le J)).trans
          (Subgroup.map_mono (le_iSup₂_of_le J ⟨hJ, hJs⟩ le_rfl))
  intro x hx
  obtain ⟨e, he, hex⟩ := key (Subgroup.mem_map_of_mem π hx)
  have hy : e⁻¹ * x ∈ Y := by
    rw [← QuotientGroup.ker_mk' Y, MonoidHom.mem_ker, map_mul, map_inv]
    change (π e)⁻¹ * π x = 1
    rw [hex]
    exact inv_mul_cancel _
  have h2 : x = e * (e⁻¹ * x) := by group
  rw [h2]
  exact Subgroup.mul_mem_sup he hy

private theorem lift_pgroup_sub_hXp_tenS {p : ℕ} {T₀ N Y : Subgroup G}
    [(Y.subgroupOf (N ⊔ T₀)).Normal] (hpg : ∀ x ∈ N, ∃ k : ℕ, x ^ p ^ k ∈ Y) :
    IsPGroup p ((N.subgroupOf (N ⊔ T₀)).map
      (QuotientGroup.mk' (Y.subgroupOf (N ⊔ T₀)))) := by
  intro y
  obtain ⟨x, hx, hxy⟩ := y.2
  obtain ⟨k, hk⟩ := hpg (x : G) (Subgroup.mem_subgroupOf.mp hx)
  refine ⟨k, Subtype.ext ?_⟩
  show (y : ↥(N ⊔ T₀) ⧸ Y.subgroupOf (N ⊔ T₀)) ^ p ^ k = 1
  rw [← hxy, ← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact Subgroup.mem_subgroupOf.mpr (by simpa using hk)

private theorem lift_pgroup_sub_hXAle_tenS {T₀ N Y A : Subgroup G}
    [(Y.subgroupOf (N ⊔ T₀)).Normal] (hT₀N : T₀ ≤ Subgroup.normalizer (N : Set G)) :
    ⁅(N.subgroupOf (N ⊔ T₀)).map (QuotientGroup.mk' (Y.subgroupOf (N ⊔ T₀))),
      (A.subgroupOf (N ⊔ T₀)).map (QuotientGroup.mk' (Y.subgroupOf (N ⊔ T₀)))⁆ ≤
      (N.subgroupOf (N ⊔ T₀)).map (QuotientGroup.mk' (Y.subgroupOf (N ⊔ T₀))) := by
  have hNK : N ≤ N ⊔ T₀ := le_sup_left
  have hKN : N ⊔ T₀ ≤ Subgroup.normalizer (N : Set G) :=
    sup_le Subgroup.le_normalizer hT₀N
  haveI hNn : (N.subgroupOf (N ⊔ T₀)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNK).mpr hKN
  have hXbn : ((N.subgroupOf (N ⊔ T₀)).map
      (QuotientGroup.mk' (Y.subgroupOf (N ⊔ T₀)))).Normal :=
    Subgroup.Normal.map inferInstance (QuotientGroup.mk' (Y.subgroupOf (N ⊔ T₀)))
      (QuotientGroup.mk'_surjective _)
  refine Subgroup.commutator_le.mpr fun x hx a _ => ?_
  have h1 := Subgroup.mul_mem _ hx (hXbn.conj_mem x⁻¹ (Subgroup.inv_mem _ hx) a)
  rw [commutatorElement_def]
  simpa [mul_assoc] using h1

private theorem lift_pgroup_sub_hYbot_tenS {T₀ N Y : Subgroup G}
    [(Y.subgroupOf (N ⊔ T₀)).Normal] :
    (Y.subgroupOf (N ⊔ T₀)).map (QuotientGroup.mk' (Y.subgroupOf (N ⊔ T₀))) = ⊥ := by
  rw [eq_bot_iff]
  rintro _ ⟨y, hy, rfl⟩
  rw [Subgroup.mem_bot]
  exact (QuotientGroup.eq_one_iff y).mpr hy

private theorem lift_pgroup_sub_hXAge_tenS {T₀ N Y A : Subgroup G}
    [(Y.subgroupOf (N ⊔ T₀)).Normal] (hAK : A ≤ N ⊔ T₀) (hYK : Y ≤ N ⊔ T₀) (hgen : N ≤ ⁅N, A⁆ ⊔ Y) :
    (N.subgroupOf (N ⊔ T₀)).map (QuotientGroup.mk' (Y.subgroupOf (N ⊔ T₀))) ≤
      ⁅(N.subgroupOf (N ⊔ T₀)).map (QuotientGroup.mk' (Y.subgroupOf (N ⊔ T₀))),
        (A.subgroupOf (N ⊔ T₀)).map (QuotientGroup.mk' (Y.subgroupOf (N ⊔ T₀)))⁆ := by
  have hNK : N ≤ N ⊔ T₀ := le_sup_left
  have hcl : ⁅N, A⁆ ≤ N ⊔ T₀ := Subgroup.commutator_le.mpr fun n hn a ha => by
    rw [commutatorElement_def]
    exact (N ⊔ T₀).mul_mem ((N ⊔ T₀).mul_mem ((N ⊔ T₀).mul_mem (hNK hn) (hAK ha))
      ((N ⊔ T₀).inv_mem (hNK hn))) ((N ⊔ T₀).inv_mem (hAK ha))
  have hsubeq : (⁅N, A⁆ ⊔ Y).subgroupOf (N ⊔ T₀) =
      ⁅N.subgroupOf (N ⊔ T₀), A.subgroupOf (N ⊔ T₀)⁆ ⊔ Y.subgroupOf (N ⊔ T₀) := by
    apply Subgroup.map_injective (N ⊔ T₀).subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le (sup_le hcl hYK), Subgroup.map_sup,
      E111R.commutator_subgroupOf hNK hAK, Subgroup.map_subgroupOf_eq_of_le hcl,
      Subgroup.map_subgroupOf_eq_of_le hYK]
  have h1 : N.subgroupOf (N ⊔ T₀) ≤
      ⁅N.subgroupOf (N ⊔ T₀), A.subgroupOf (N ⊔ T₀)⁆ ⊔ Y.subgroupOf (N ⊔ T₀) := by
    rw [← hsubeq]
    exact Subgroup.subgroupOf_mono _ hgen
  have h2 := Subgroup.map_mono (f := QuotientGroup.mk' (Y.subgroupOf (N ⊔ T₀))) h1
  rwa [Subgroup.map_sup, lift_pgroup_sub_hYbot_tenS (T₀ := T₀) (N := N) (Y := Y),
    sup_bot_eq, Subgroup.map_commutator] at h2

private theorem lift_pgroup_sub_hmem_tenS {T T₀ N A : Subgroup G}
    (hT : IsSylowIn 2 T ⊤) (hAT : A ≤ T) (hAab : IsElemAbelian 2 A) (hT₀T : T₀ ≤ T)
    (hAT₀ : A ≤ T₀) (hSyl : IsSylowIn 2 (T ⊓ (N ⊔ T₀)) (N ⊔ T₀))
    (hτ : E1.tauOf ⊤ T A ≤ T₀) {K' : Subgroup ↥(N ⊔ T₀)}
    (hK' : E1.IsE 1 ⊤ ((T ⊓ (N ⊔ T₀)).subgroupOf (N ⊔ T₀))
      (A.subgroupOf (N ⊔ T₀)) K') :
    E1.IsE 1 ⊤ T A (K'.map (N ⊔ T₀).subtype) := by
  have h1 : E1.IsE 1 (N ⊔ T₀) (((T ⊓ (N ⊔ T₀)).subgroupOf (N ⊔ T₀)).map (N ⊔ T₀).subtype)
      ((A.subgroupOf (N ⊔ T₀)).map (N ⊔ T₀).subtype) (K'.map (N ⊔ T₀).subtype) :=
    (E1.isE_map_subtype (N ⊔ T₀)).mpr hK'
  rw [Subgroup.map_subgroupOf_eq_of_le (inf_le_right : T ⊓ (N ⊔ T₀) ≤ N ⊔ T₀),
    Subgroup.map_subgroupOf_eq_of_le (hAT₀.trans le_sup_right)] at h1
  exact E1.eight_two hT hAT hAab le_top (hτ.trans (le_inf hT₀T le_sup_right)) hSyl h1

private theorem lift_pgroup_sub_transport_tenS {T T₀ N Y A : Subgroup G}
    (hYN : Y ≤ N)
    (hLift : N.subgroupOf (N ⊔ T₀) ≤
      (⨆ K' ∈ {K' : Subgroup ↥(N ⊔ T₀) | E1.IsE 1 ⊤ ((T ⊓ (N ⊔ T₀)).subgroupOf (N ⊔ T₀))
        (A.subgroupOf (N ⊔ T₀)) K' ∧ Group.IsSolvable ↥K'}, K') ⊔
      Y.subgroupOf (N ⊔ T₀))
    (hmem : ∀ K' : Subgroup ↥(N ⊔ T₀), E1.IsE 1 ⊤ ((T ⊓ (N ⊔ T₀)).subgroupOf (N ⊔ T₀))
      (A.subgroupOf (N ⊔ T₀)) K' → E1.IsE 1 ⊤ T A (K'.map (N ⊔ T₀).subtype)) :
    N ≤ (⨆ X ∈ {X : Subgroup G | E1.IsE 1 ⊤ T A X ∧ Group.IsSolvable ↥X}, X) ⊔ Y := by
  have hNK : N ≤ N ⊔ T₀ := le_sup_left
  have hYK : Y ≤ N ⊔ T₀ := hYN.trans hNK
  have hfin : (N.subgroupOf (N ⊔ T₀)).map (N ⊔ T₀).subtype ≤
      (⨆ X ∈ {X : Subgroup G | E1.IsE 1 ⊤ T A X ∧ Group.IsSolvable ↥X}, X) ⊔ Y := by
    refine (Subgroup.map_mono hLift).trans ?_
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hYK, Subgroup.map_iSup]
    refine sup_le_sup_right (iSup_le fun K' => ?_) Y
    rw [Subgroup.map_iSup]
    refine iSup_le fun hK' => ?_
    have hK's : Group.IsSolvable ↥(K'.map (N ⊔ T₀).subtype) := by
      haveI := hK'.2
      exact Group.isSolvable_of_surjective
        (f := (Subgroup.equivMapOfInjective K' (N ⊔ T₀).subtype
          (N ⊔ T₀).subtype_injective).toMonoidHom)
        (Subgroup.equivMapOfInjective K' (N ⊔ T₀).subtype (N ⊔ T₀).subtype_injective).surjective
    exact le_iSup₂_of_le (K'.map (N ⊔ T₀).subtype) ⟨hmem K' hK'.1, hK's⟩ le_rfl
  rw [Subgroup.map_subgroupOf_eq_of_le hNK] at hfin
  exact hfin

theorem lift_pgroup_subS {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {T T₀ N Y A : Subgroup G}
    (hT : IsSylowIn 2 T ⊤) (hT₀T : T₀ ≤ T) (hAT₀ : A ≤ T₀) (hAab : IsElemAbelian 2 A)
    (hT₀N : T₀ ≤ Subgroup.normalizer (N : Set G)) (hT₀Y : T₀ ≤ Subgroup.normalizer (Y : Set G))
    (hNY : N ≤ Subgroup.normalizer (Y : Set G)) (hYN : Y ≤ N)
    (hpg : ∀ x ∈ N, ∃ k : ℕ, x ^ p ^ k ∈ Y) (hgen : N ≤ ⁅N, A⁆ ⊔ Y)
    (hSyl : IsSylowIn 2 (T ⊓ (N ⊔ T₀)) (N ⊔ T₀)) (hτ : E1.tauOf ⊤ T A ≤ T₀)
    (hYs : Group.IsSolvable ↥Y) :
    N ≤ (⨆ K ∈ {K : Subgroup G | E1.IsE 1 ⊤ T A K ∧ Group.IsSolvable ↥K}, K) ⊔ Y := by
  set K : Subgroup G := N ⊔ T₀ with hKdef
  have hNK : N ≤ K := le_sup_left
  have hT₀K : T₀ ≤ K := le_sup_right
  have hYK : Y ≤ K := hYN.trans hNK
  have hAK : A ≤ K := hAT₀.trans hT₀K
  have hAT : A ≤ T := hAT₀.trans hT₀T
  have hKN : K ≤ Subgroup.normalizer (N : Set G) := sup_le Subgroup.le_normalizer hT₀N
  have hKY : K ≤ Subgroup.normalizer (Y : Set G) := sup_le hNY hT₀Y
  haveI hNn : (N.subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNK).mpr hKN
  haveI hYn : (Y.subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hYK).mpr hKY
  have hSylK : IsSylowIn 2 ((T ⊓ K).subgroupOf K) ⊤ := by
    rw [← E1.isSylowIn_map_of_injective K.subtype_injective,
      Subgroup.map_subgroupOf_eq_of_le (inf_le_right : T ⊓ K ≤ K), Subgroup.map_top,
      Subgroup.range_subtype]
    exact hSyl
  have hAT' : A.subgroupOf K ≤ (T ⊓ K).subgroupOf K :=
    Subgroup.subgroupOf_mono K (le_inf hAT hAK)
  have hAab' : IsElemAbelian 2 (A.subgroupOf K) := ronanE111_isElemAbelian_subgroupOf hAab K
  have hYsK : Group.IsSolvable ↥(Y.subgroupOf K) := by
    haveI := hYs
    exact Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hYK).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hYK).injective
  have hXp := lift_pgroup_sub_hXp_tenS (T₀ := T₀) hpg
  have hXA : ⁅(N.subgroupOf K).map (QuotientGroup.mk' (Y.subgroupOf K)),
      (A.subgroupOf K).map (QuotientGroup.mk' (Y.subgroupOf K))⁆ =
      (N.subgroupOf K).map (QuotientGroup.mk' (Y.subgroupOf K)) :=
    le_antisymm (lift_pgroup_sub_hXAle_tenS hT₀N)
      (lift_pgroup_sub_hXAge_tenS hAK hYK hgen)
  have hLift := ten_sixS hp hp2 hSylK hAT' hAab' hYsK hXp hXA
  have hmem : ∀ K' : Subgroup ↥K, E1.IsE 1 ⊤ ((T ⊓ K).subgroupOf K) (A.subgroupOf K) K' →
      E1.IsE 1 ⊤ T A (K'.map K.subtype) := fun K' hK' =>
    lift_pgroup_sub_hmem_tenS hT hAT hAab hT₀T hAT₀ hSyl hτ hK'
  exact lift_pgroup_sub_transport_tenS hYN hLift hmem

private theorem pgroup_diag_wrY_solvable_tenS {X T A J C : Subgroup G} [Fintype ↥C]
    (h : E111R.DiagSetting X T A J C) {YR : Subgroup G} (hYT : YR ≤ T) :
    Group.IsSolvable ↥(RonanE111.wrY h.diagComm T A YR) := by
  have hT : IsSylowIn 2 T ⊤ := h.red.2.2.2.2.2.1
  have hYT' : RonanE111.wrY h.diagComm T A YR ≤ T := RonanE111.pg_wrY_le_T h hYT
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : IsPGroup 2 (RonanE111.wrY h.diagComm T A YR) := hT.isPGroup.to_le hYT'
  have := h2.isNilpotent
  infer_instance

private theorem pgroup_diag_sylow_tenS {X T A J C : Subgroup G} [Fintype ↥C]
    (h : E111R.DiagSetting X T A J C) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {R YR : Subgroup G}
    (hYT' : RonanE111.wrY h.diagComm T A YR ≤ T)
    (hYN : RonanE111.wrY h.diagComm T A YR ≤ RonanE111.wrN h.diagComm T A R)
    (hNY : RonanE111.wrN h.diagComm T A R ≤
      Subgroup.normalizer (RonanE111.wrY h.diagComm T A YR : Set G))
    (hpg : ∀ x ∈ RonanE111.wrN h.diagComm T A R, ∃ k : ℕ,
      x ^ p ^ k ∈ RonanE111.wrY h.diagComm T A YR) :
    IsSylowIn 2 (T ⊓ (RonanE111.wrN h.diagComm T A R ⊔ RonanE111.actT T A))
      (RonanE111.wrN h.diagComm T A R ⊔ RonanE111.actT T A) := by
  have hT : IsSylowIn 2 T ⊤ := h.red.2.2.2.2.2.1
  have hT2 : IsPGroup 2 T := hT.isPGroup
  have hYn : ((RonanE111.wrY h.diagComm T A YR).subgroupOf
      (RonanE111.wrN h.diagComm T A R)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hYN).mpr hNY
  haveI := hYn
  have hodd := RonanE111.pg_odd_index hp hp2 hpg
  have hSylN : IsSylowIn 2 (T ⊓ RonanE111.wrN h.diagComm T A R)
      (RonanE111.wrN h.diagComm T A R) :=
    RonanE111.pg_isSylowIn_of_odd_index inf_le_right (hT2.to_le inf_le_left)
      (le_inf hYT' hYN) hodd
  exact RonanE111.pg_sylow_sup h hT2 hSylN

theorem pgroup_diag_coverP {X T A J C : Subgroup G} [Fintype ↥C] {n : ℕ} (hn : 1 ≤ n)
    (h : E111R.DiagSetting X T A J C) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {R YR : Subgroup G}
    (hRJ : R ≤ J) (hYR : YR ≤ R) (hYRn : ∀ r ∈ R, ∀ y ∈ YR, r * y * r⁻¹ ∈ YR) (hYT : YR ≤ T)
    (hRE : ∀ e ∈ RonanE111.actE T A J, A1b.conjSub e R = R)
    (hYE : ∀ e ∈ RonanE111.actE T A J, A1b.conjSub e YR = YR)
    (hpq : ∀ x ∈ R, ∃ k : ℕ, x ^ p ^ k ∈ YR)
    (hgen : R ≤ ⁅R, A ⊓ Subgroup.normalizer (J : Set G)⁆ ⊔ YR) :
    RonanE111.dimg h.diagComm R ≤
      T ⊔ ⨆ K ∈ {K : Subgroup G | UniquenessCase.UC22.F12.IsEP n ⊤ T A K}, K := by
  have hYJ : YR ≤ J := hYR.trans hRJ
  have hRN : R ≤ Subgroup.normalizer (YR : Set G) := RonanE111.pg_le_normalizer hYRn
  have hNY : RonanE111.wrN h.diagComm T A R ≤
      Subgroup.normalizer (RonanE111.wrY h.diagComm T A YR : Set G) :=
    RonanE111.pg_wrN_le_normalizer_wrY h hRJ hYJ hRN hYE
  have hYN : RonanE111.wrY h.diagComm T A YR ≤ RonanE111.wrN h.diagComm T A R :=
    RonanE111.wr_wrY_le_wrN h hYR
  have hYT' : RonanE111.wrY h.diagComm T A YR ≤ T := RonanE111.pg_wrY_le_T h hYT
  have hpg := RonanE111.wrP_pgroup h hRJ hRE hpq
  have hgen' := RonanE111.pg_wrN_le_comm_sup h hRJ hYR hgen
  have hT : IsSylowIn 2 T ⊤ := h.red.2.2.2.2.2.1
  have hSylH := pgroup_diag_sylow_tenS h hp hp2 hYT' hYN hNY hpg
  have hτ : E1.tauOf ⊤ T A ≤ RonanE111.actT T A :=
    E111R.tauOf_le (E111R.pCoreOf_two_eq_bot h.red) T A
  have hYsolv := pgroup_diag_wrY_solvable_tenS h hYT
  have hLift := lift_pgroup_subS hp hp2 (T₀ := RonanE111.actT T A)
    (N := RonanE111.wrN h.diagComm T A R) (Y := RonanE111.wrY h.diagComm T A YR) (A := A)
    hT RonanE111.pg_actT_le_T (RonanE111.pg_A_le_actT h) h.elem
    (RonanE111.pg_actT_le_normalizer_wrN h) (RonanE111.pg_actT_le_normalizer_wrY h) hNY hYN
    hpg hgen' hSylH hτ hYsolv
  have hset : (⨆ K ∈ {K : Subgroup G | E1.IsE 1 ⊤ T A K ∧ Group.IsSolvable ↥K}, K) ≤
      ⨆ K ∈ {K : Subgroup G | UniquenessCase.UC22.F12.IsEP n ⊤ T A K}, K :=
    iSup₂_le fun K hK => le_iSup₂_of_le K (isEP_of_isE_tenS hn hK.1 hK.2) le_rfl
  calc RonanE111.dimg h.diagComm R ≤ RonanE111.wrN h.diagComm T A R :=
        RonanE111.wr_dimg_le_wrN h
    _ ≤ (⨆ K ∈ {K : Subgroup G | E1.IsE 1 ⊤ T A K ∧ Group.IsSolvable ↥K}, K) ⊔
          RonanE111.wrY h.diagComm T A YR := hLift
    _ ≤ (⨆ K ∈ {K : Subgroup G | UniquenessCase.UC22.F12.IsEP n ⊤ T A K}, K) ⊔ T :=
        sup_le_sup hset hYT'
    _ = T ⊔ ⨆ K ∈ {K : Subgroup G | UniquenessCase.UC22.F12.IsEP n ⊤ T A K}, K :=
        sup_comm _ _
