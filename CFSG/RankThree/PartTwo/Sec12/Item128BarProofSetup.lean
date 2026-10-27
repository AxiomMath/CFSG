module

public import CFSG.RankThree.PartTwo.Sec12.Item128Bar
public import CFSG.RankThree.PartTwo.Sec12.Item128BarProofTools
public import CFSG.RankThree.PartTwo.Sec4.Statements423
public import CFSG.RankThree.PartTwo.Sec9.Hyp91SmallBridge
public import CFSG.RankThree.PartTwo.Sec13.Item131Transport
import CFSG.RankThree.PartTwo.Sec9.Hyp91SmallModels
import CFSG.RankThree.PartTwo.Sec13.Naturality
import CFSG.RankThree.PartTwo.Sec13.Item137Tools
import CFSG.RankThree.PartTwo.Sec6.Item612Local
import CFSG.RankThree.PartTwo.Sec11.FixedCentralizer

public section

namespace CFSG.RankThree.PartTwo.Sec12.Proof128

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec13 (lBarA)

section Setup

variable {G : Type} [Group G] [Finite G]

theorem centralizer_setup (hst : PartTwoStanding G) {A : Subgroup G} (hAF : A ∈ partTwoF G)
    (h27 : Nat.card A = 27) {a : G} (haA : a ∈ A) (ha1 : a ≠ 1) :
    SectionFourHyp (Subgroup.centralizer ({a} : Set G)) ∧
      A ≤ Subgroup.centralizer ({a} : Set G) ∧
      Maximal (fun B : Subgroup (Subgroup.centralizer ({a} : Set G)) =>
        CFSG.Assembly.IsElemAbelian 3 B) (A.subgroupOf (Subgroup.centralizer ({a} : Set G))) ∧
      Nat.card (A.subgroupOf (Subgroup.centralizer ({a} : Set G))) = 27 := by
  have hAe : CFSG.Assembly.IsElemAbelian 3 A := hAF.1
  have hcomm : ∀ y ∈ A, ∀ z ∈ A, y * z = z * y := fun y hy z hz =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨y, hy⟩ ⟨z, hz⟩)
  set C := Subgroup.centralizer ({a} : Set G) with hCdef
  have hAC : A ≤ C := fun x hx => Subgroup.mem_centralizer_singleton_iff.mpr (hcomm x hx a haA)
  have hCtop : C ≠ ⊤ := by
    intro hCt
    have haZ : a ∈ Subgroup.center G := Subgroup.mem_center_iff.mpr fun g => by
      have hg : g ∈ C := hCt ▸ Subgroup.mem_top g
      exact Subgroup.mem_centralizer_singleton_iff.mp hg
    rcases hst.isSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with hb | ht
    · rw [hb, Subgroup.mem_bot] at haZ
      exact ha1 haZ
    · obtain ⟨x, y, hxy⟩ := hst.nonabelian
      exact hxy (Subgroup.mem_center_iff.mp (ht ▸ Subgroup.mem_top y) x)
  have hS4 : SectionFourHyp C := hst.toTheoremFourHyp.sectionFourHyp hCtop
  set A' := A.subgroupOf C with hA'def
  have hA'map : A'.map C.subtype = A := by
    rw [hA'def, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hAC]
  have hA'e : CFSG.Assembly.IsElemAbelian 3 A' :=
    ⟨⟨⟨fun x y => Subtype.ext (Subtype.ext (hcomm _ (Subgroup.mem_subgroupOf.mp x.2) _
      (Subgroup.mem_subgroupOf.mp y.2)))⟩⟩,
      fun x hx => Subtype.ext (hAe.2 _ (Subgroup.mem_subgroupOf.mp hx))⟩
  have h27' : Nat.card A' = 27 := by
    rw [← h27, ← hA'map, Subgroup.card_map_of_injective C.subtype_injective]
  refine ⟨hS4, hAC, ⟨hA'e, fun B hB hAB => ?_⟩, h27'⟩
  have hBe : CFSG.Assembly.IsElemAbelian 3 (B.map C.subtype) := by
    refine ⟨⟨⟨fun x y => ?_⟩⟩, ?_⟩
    · obtain ⟨_, x, hx, rfl⟩ := x
      obtain ⟨_, y, hy, rfl⟩ := y
      apply Subtype.ext
      change (x : G) * y = y * x
      exact congrArg Subtype.val (congrArg Subtype.val (hB.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩))
    · rintro _ ⟨x, hx, rfl⟩
      simpa using congrArg Subtype.val (hB.2 x hx)
  have hAB' : A ≤ B.map C.subtype := fun x hx =>
    ⟨⟨x, hAC hx⟩, hAB (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
  have hBA := hAF.2.1 _ hBe hAB'
  intro x hx
  have : (x : G) ∈ A := hBA ▸ ⟨x, hx, rfl⟩
  exact Subgroup.mem_subgroupOf.mpr this

theorem card_autThetaQuot_eq_nine {A : Subgroup G} (hAe : CFSG.Assembly.IsElemAbelian 3 A)
    (h27 : Nat.card A = 27) {a : G} (haA : a ∈ A) (ha1 : a ≠ 1) {K : Subgroup G}
    (hK : K ∈ lA422 A a) : Nat.card (Sec4.autThetaQuot A K) = 9 := by
  obtain ⟨-, hAN, hsc, -⟩ := hK
  have h := Sec13.card_inf_mul_card_autThetaQuot hAN
  rw [Sec13.sectionCentralizer_eq_inf hAN] at hsc
  have heq : (A ⊓ Sec4.thetaQuotCentralizer K : Subgroup G) = Subgroup.zpowers a :=
    SetLike.coe_injective hsc
  rw [heq, Sec13.card_zpowers_of_pow_three (hAe.2 a haA) ha1, h27] at h
  omega

theorem thetaAlpha_eq_bot_of_fixedCore {A K : Subgroup G} {a : G}
    (hAe : CFSG.Assembly.IsElemAbelian 3 A) (h27 : Nat.card A = 27) (haA : a ∈ A) (ha1 : a ≠ 1)
    (hK : K ∈ lA422 A a)
    (hfix : ∀ e ∈ A, e ∉ Subgroup.zpowers a → ∀ (he : e ∈ Subgroup.normalizer (K : Set G))
      (N : Subgroup (MulAut (K ⧸ aschbacherSolvableCore 3 K))),
      (∀ ν ∈ N, ν * Sec4.thetaQuotMulAut K (Sec4.compAction K ⟨e, he⟩) =
        Sec4.thetaQuotMulAut K (Sec4.compAction K ⟨e, he⟩) * ν) →
      ¬ 3 ∣ Nat.card N →
      (∀ ℓ : K ⧸ aschbacherSolvableCore 3 K,
        Sec4.thetaQuotMulAut K (Sec4.compAction K ⟨e, he⟩) ℓ = ℓ →
          ∀ ν ∈ N, MulAut.conj ℓ * ν * (MulAut.conj ℓ)⁻¹ ∈ N) →
      N = ⊥) :
    thetaAlpha 3 ((Sec4.autThetaQuot A K).subgroupOf
      (Sec4.autThetaQuot (Subgroup.centralizer ({a} : Set G)) K)) = ⊥ := by
  have hKC : K ≤ Subgroup.centralizer ({a} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hK.1
  have hAC : A ≤ Subgroup.centralizer ({a} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (hAe.1.is_comm.comm ⟨x, hx⟩ ⟨a, haA⟩))
  have hsc := hK.2.2.1
  set X := Sec4.autThetaQuot (Subgroup.centralizer ({a} : Set G)) K with hX
  set B := (Sec4.autThetaQuot A K).subgroupOf X with hB
  have hcore : ∀ b : X, b ∈ B → b ≠ 1 →
      inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({b} : Set X)) = ⊥ := by
    intro b hb hb1
    obtain ⟨e, he, heA, hbe⟩ := Sec4.mem_autThetaQuot_iff.mp (Subgroup.mem_subgroupOf.mp hb)
    have hε : Sec4.thetaQuotMulAut K (Sec4.compAction K ⟨e, he⟩) = (b : MulAut _) := hbe
    have hec : e ∉ Subgroup.zpowers a := by
      intro hec
      apply hb1
      have h2 : e ∈ Late.sectionCentralizer A K ((aschbacherSolvableCore 3 K).map K.subtype) := by
        rw [hsc]
        exact hec
      rw [Late.sectionCentralizer] at h2
      obtain ⟨-, h2'⟩ := h2
      apply Subtype.ext
      rw [← hε]
      exact KFacts.thetaQuotMulAut_compAction_eq_one_of_forall he h2'
    set Q := inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({b} : Set X)) with hQ
    have hQC : Q ≤ Subgroup.centralizer ({b} : Set X) := Subgroup.map_subtype_le _
    have hN : Q.map X.subtype = ⊥ := by
      refine hfix e heA hec he (Q.map X.subtype) ?_ ?_ ?_
      · rintro _ ⟨q, hq, rfl⟩
        rw [hε]
        exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp (hQC hq))
      · intro h3
        apply Sec11.not_three_dvd_card_inSubgroup_theta (Subgroup.centralizer ({b} : Set X))
        rwa [Subgroup.card_map_of_injective X.subtype_injective] at h3
      · intro ℓ hℓ ν hν
        obtain ⟨q, hq, rfl⟩ := hν
        obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (aschbacherSolvableCore 3 K) ℓ
        have hlN : (l : G) ∈ Subgroup.normalizer (K : Set G) := Subgroup.le_normalizer l.2
        have hlX : MulAut.conj (QuotientGroup.mk' (aschbacherSolvableCore 3 K) l) ∈ X := by
          refine Sec4.mem_autThetaQuot_iff.mpr ⟨l, hlN, hKC l.2, ?_⟩
          exact KFacts.thetaQuotMulAut_compAction_of_mem l.2 hlN
        set γ : X := ⟨_, hlX⟩ with hγ
        have hγb : γ ∈ Subgroup.centralizer ({b} : Set X) := by
          rw [Subgroup.mem_centralizer_singleton_iff]
          apply Subtype.ext
          change MulAut.conj (QuotientGroup.mk' (aschbacherSolvableCore 3 K) l) * (b : MulAut _) =
            (b : MulAut _) * MulAut.conj (QuotientGroup.mk' (aschbacherSolvableCore 3 K) l)
          rw [hε] at hℓ
          have h1 := KFacts.mul_conj_mul_inv (b : MulAut _)
            (QuotientGroup.mk' (aschbacherSolvableCore 3 K) l)
          rw [hℓ] at h1
          calc MulAut.conj (QuotientGroup.mk' (aschbacherSolvableCore 3 K) l) * (b : MulAut _) =
              (b : MulAut _) * MulAut.conj (QuotientGroup.mk' (aschbacherSolvableCore 3 K) l) *
                (b : MulAut _)⁻¹ * (b : MulAut _) := by rw [h1]
            _ = (b : MulAut _) * MulAut.conj (QuotientGroup.mk' (aschbacherSolvableCore 3 K) l) :=
              by group
        exact ⟨γ * q * γ⁻¹, Sec13.conj_mem_inSubgroup_theta hγb hq, rfl⟩
    exact (Subgroup.map_eq_bot_iff_of_injective _ X.subtype_injective).mp hN
  have hAX : Sec4.autThetaQuot A K ≤ X := Sec13.autThetaQuot_mono hAC K
  obtain ⟨b₀, hb₀, hb₀1⟩ : ∃ b ∈ B, b ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hle : Sec4.autThetaQuot A K ≤ ⊥ := by
      intro τ hτ
      have h1 := hcon ⟨τ, hAX hτ⟩ (Subgroup.mem_subgroupOf.mpr hτ)
      exact Subgroup.mem_bot.mpr (congrArg Subtype.val h1)
    have h9 := card_autThetaQuot_eq_nine hAe h27 haA ha1 hK
    rw [le_bot_iff.mp hle, Subgroup.card_bot] at h9
    omega
  have hJ : thetaJ 3 B = ⊥ := by
    refine eq_bot_iff.mpr (iSup_le fun b => iSup_le fun hb => iSup_le fun hb1 => ?_)
    rw [hcore b hb hb1, Subgroup.commutator_bot_left]
  have hT : thetaT 3 B = ⊥ := by
    refine eq_bot_iff.mpr ((iInf_le_of_le b₀ (iInf_le_of_le hb₀ (iInf_le_of_le hb₀1 le_rfl))).trans
      ?_)
    rw [hcore b₀ hb₀ hb₀1]
  rw [thetaAlpha, hJ, hT, sup_bot_eq]

end Setup


section Cases

variable {G : Type} [Group G] [Finite G]

theorem hyp81_of_mem_lA422 (hst : PartTwoStanding G) {A : Subgroup G} (hAF : A ∈ partTwoF G)
    (hFE : partTwoF G = partTwoE G) (h27 : Nat.card A = 27) {a : G} (haA : a ∈ A)
    (ha1 : a ≠ 1) {K : Subgroup G} (hK : K ∈ lA422 A a) {x : G} (hxA : x ∈ A) (hx1 : x ≠ 1)
    (hk : KFacts.InducesStdKind K x .field ∨ KFacts.InducesStdKind K x .graphField) :
    Sec8.Hyp81 G A a K x :=
  ⟨hst, hAF, haA, ha1, hK.1, hK.2.2.1, hxA, hx1, hk, fun hbig => absurd hbig (by omega),
    fun _ => hFE.symm⟩

theorem not_lTwoEight (hst : PartTwoStanding G) {A : Subgroup G} (hAF : A ∈ partTwoF G)
    (hFE : partTwoF G = partTwoE G) (h27 : Nat.card A = 27) {a : G} (haA : a ∈ A)
    (ha1 : a ≠ 1) {K : Subgroup G} (hK : K ∈ lA422 A a) {x : G} (hxA : x ∈ A) (hx1 : x ≠ 1)
    (hk : KFacts.InducesStdKind K x .field ∨ KFacts.InducesStdKind K x .graphField) :
    ¬ Nonempty (K ⧸ aschbacherSolvableCore 3 K ≃*
      CFSG.Assembly.RankThreeEven.projSL 2 (GaloisField 2 3)) := by
  intro hL
  have h81 := hyp81_of_mem_lA422 hst hAF hFE h27 haA ha1 hK hxA hx1 hk
  exact hK.2.2.2 (thetaAlpha_eq_bot_of_fixedCore hAF.1 h27 haA ha1 hK fun e heA hec he N =>
    KFacts.eq_bot_of_hyp81_psl28 h81 h27 hL hK.2.1 heA hec he N)

theorem not_slThreePiEight (hst : PartTwoStanding G) {A : Subgroup G} (hAF : A ∈ partTwoF G)
    (hFE : partTwoF G = partTwoE G) (h27 : Nat.card A = 27) {a : G} (haA : a ∈ A)
    (ha1 : a ≠ 1) {K : Subgroup G} (hK : K ∈ lA422 A a) {x : G} (hxA : x ∈ A) (hx1 : x ≠ 1)
    (hk : KFacts.InducesStdKind K x .field ∨ KFacts.InducesStdKind K x .graphField) :
    ¬ Sec4.IsSLThreePiAt (K ⧸ aschbacherSolvableCore 3 K) 8 := by
  intro hSL
  have h81 := hyp81_of_mem_lA422 hst hAF hFE h27 haA ha1 hK hxA hx1 hk
  exact hK.2.2.2 (thetaAlpha_eq_bot_of_fixedCore hAF.1 h27 haA ha1 hK fun e heA hec he N =>
    KFacts.eq_bot_of_hyp81_su38 h81 h27 hSL hK.2.1 heA hec he N)

theorem not_inducesStdKind (h1134 : Sec11.Item1134E27N) (hst : PartTwoStanding G)
    {A : Subgroup G} (hAF : A ∈ partTwoF G) (hAT : A ∉ partTwoT G)
    (hFE : partTwoF G = partTwoE G) (h27 : Nat.card A = 27) {a : G} (haA : a ∈ A) (ha1 : a ≠ 1)
    {K : Subgroup G} (hK : K ∈ lA422 A a) {x : G} (hxA : x ∈ A) (hx1 : x ≠ 1) :
    ¬ (KFacts.InducesStdKind K x .field ∨ KFacts.InducesStdKind K x .graphField) := by
  intro hk
  have hsc := hK.2.2.1
  have hsc' := hsc
  rw [Sec13.sectionCentralizer_eq_inf hK.2.1] at hsc'
  have hle : A ⊓ Sec4.thetaQuotCentralizer K ≤ Subgroup.zpowers a := fun y hy => by
    have : y ∈ ((A ⊓ Sec4.thetaQuotCentralizer K : Subgroup G) : Set G) := hy
    rw [hsc'] at this
    exact this
  have hstar : K ∈ lStarAt A a :=
    ⟨Sec6.mem_lStar_of_inf_le_zpowers hAF.1 haA ha1 hK.1 hK.2.1 hle, hK.1⟩
  have hx := h1134 G A a K hst hAF hAT h27 haA ha1 hstar hsc
    (not_lTwoEight hst hAF hFE h27 haA ha1 hK hxA hx1 hk)
    (not_slThreePiEight hst hAF hFE h27 haA ha1 hK hxA hx1 hk) (fun _ => hFE.symm) x hxA
  rcases hk with hk | hk
  · exact hx.1 hk
  · exact hx.2 hk

theorem cases423 (h423 : Sec4.Item4_23) (hst : PartTwoStanding G) {A : Subgroup G}
    (hAF : A ∈ partTwoF G) (h27 : Nat.card A = 27) {a : G} (haA : a ∈ A) (ha1 : a ≠ 1)
    {K : Subgroup G} (hK : K ∈ lA422 A a) :
    (∃ σ : Sec4.autIn K A, orderOf σ = 4) ∨
    (Sec8.IsZ3PGLThreePi (lBarA a K A) ∧ Nonempty (Sec4.autIn K A ≃* Multiplicative (ZMod 3)) ∧
      ∃ x ∈ A, x ≠ 1 ∧ Sec4.InducesTypeOn K x 3) ∨
    ((∀ σ ∈ Sec4.autIn K A, σ ^ 3 = 1) ∧ Nat.card (Sec4.autIn K A) = 9) ∨
    (Sec4.IsSLThreePiTwo (lBarA a K A) ∧ Nonempty (Sec4.autIn K A ≃* Multiplicative (ZMod 3))) ∨
    ((Nonempty (lBarA a K A ≃* Multiplicative (ZMod 3) × CFSG.Blueprint.NativeSporadic.M12) ∨
        Nonempty (lBarA a K A ≃* Multiplicative (ZMod 3) × CFSG.Blueprint.NativeSporadic.J2)) ∧
      Nonempty (Sec4.autIn K A ≃* Equiv.Perm (Fin 3))) ∨
    ∃ x ∈ A, x ≠ 1 ∧
      (KFacts.InducesStdKind K x .field ∨ KFacts.InducesStdKind K x .graphField) := by
  have hAe : CFSG.Assembly.IsElemAbelian 3 A := hAF.1
  obtain ⟨hS4, hAC, hmax, h27'⟩ := centralizer_setup hst hAF h27 haA ha1
  set C := Subgroup.centralizer ({a} : Set G) with hCdef
  set A' := A.subgroupOf C with hA'def
  have hA'map : A'.map C.subtype = A := by
    rw [hA'def, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hAC]
  set a' : C := ⟨a, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ with ha'def
  have ha'A : a' ∈ A' := Subgroup.mem_subgroupOf.mpr haA
  have ha'Z : a' ∈ Subgroup.center C := Subgroup.mem_center_iff.mpr fun y =>
    Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp y.2)
  have ha'1 : a' ≠ 1 := fun h => ha1 (congrArg Subtype.val h)
  have hKC : K ≤ C := Sec6.le_centralizer_of_mem_thetaComponentsAt hK.1
  obtain ⟨K', hK', hK'K⟩ := hK.1
  replace hK'K : K'.map C.subtype = K := hK'K
  have hK'eq : K' = K.subgroupOf C := by
    rw [← hK'K]
    exact (Subgroup.comap_map_eq_self_of_injective C.subtype_injective K').symm
  have h9 : Nat.card (Sec4.autThetaQuot A' K') = 9 := by
    have := card_autThetaQuot_eq_nine hAe h27 haA ha1 hK
    rw [← hA'map, ← hK'K, ← Sec13.map_autThetaQuot_sub C A' K',
      Subgroup.card_map_of_injective (MulAut.congr (Sec13.thetaQuotEquivSub C K')).injective]
      at this
    exact this
  have hα' : thetaAlpha 3 ((Sec4.autThetaQuot A' K').subgroupOf (Sec4.autThetaQuot ⊤ K')) ≠ ⊥ := by
    rw [← Sec13.thetaAlpha_subgroupOf_map_ne_bot_iff (MulAut.congr (Sec13.thetaQuotEquivSub C K'))
      (Sec4.autThetaQuot A' K') (Sec4.autThetaQuot ⊤ K'), Sec13.map_autThetaQuot_sub,
      Sec13.map_autThetaQuot_sub, hA'map, hK'K]
    have hC' : (⊤ : Subgroup C).map C.subtype = C := by
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    rw [hC']
    exact hK.2.2.2
  obtain ⟨eImg⟩ := Sec13.nonempty_thetaImage_equiv_lBarA (c := a) hKC hAC
  have eImg' : Nonempty (Sec4.thetaImage (K' ⊔ A') ≃* lBarA a K A) := by
    rw [hK'eq]
    exact ⟨eImg⟩
  obtain ⟨eI⟩ := eImg'
  obtain ⟨eAut⟩ := Sec13.nonempty_autIn_subgroupOf_equiv C hKC hAC
  have eAut' : Nonempty (Sec4.autIn K' A' ≃* Sec4.autIn K A) := by
    rw [hK'eq]
    exact ⟨eAut⟩
  obtain ⟨eA⟩ := eAut'
  rcases h423 C hS4 A' hmax h27' a' ha'A ha'Z ha'1 K' hK' h9 hα' with
    ⟨-, hQ⟩ | ⟨hPGL, ⟨eZ3⟩, x, hxA, hx1, hx3⟩ | ⟨-, -, hE, hE9⟩ | ⟨hSL2, ⟨eZ3⟩⟩ |
      ⟨-, ⟨eZ4⟩⟩ | ⟨-, ⟨eQ⟩⟩ | ⟨hMJ, ⟨eS3⟩⟩ | ⟨x, hxA, hx1, hk⟩
  · left
    rcases hQ with he | he
    · obtain ⟨e⟩ := he
      exact exists_orderOf_eq_four_of_quaternion (eA.symm.trans e)
    · obtain ⟨e⟩ := he
      exact exists_orderOf_eq_four_of_sl23 (eA.symm.trans e)
  · right; left
    refine ⟨Sec13.isZ3PGLThreePi_of_mulEquiv eI hPGL, ⟨eA.symm.trans eZ3⟩, (x : G),
      Subgroup.mem_subgroupOf.mp hxA, fun h => hx1 (Subtype.ext h), ?_⟩
    have := Sec13.inducesTypeOn_sub C K' hx3
    rwa [hK'K] at this
  · right; right; left
    refine ⟨fun σ hσ => ?_, by rw [← hE9]; exact (Nat.card_congr eA.toEquiv).symm⟩
    set t := eA.symm ⟨σ, hσ⟩ with ht
    have ht3 : t ^ 3 = 1 := Subtype.ext (by simpa using hE.2 _ t.2)
    have h1 : (⟨σ, hσ⟩ : Sec4.autIn K A) ^ 3 = 1 := by
      have : (⟨σ, hσ⟩ : Sec4.autIn K A) = eA t := by rw [ht, MulEquiv.apply_symm_apply]
      rw [this, ← map_pow, ht3, map_one]
    simpa using congrArg Subtype.val h1
  · right; right; right; left
    exact ⟨Sec13.isSLThreePiTwo_of_mulEquiv eI hSL2, ⟨eA.symm.trans eZ3⟩⟩
  · left
    exact exists_orderOf_eq_four_of_zmod4 (eA.symm.trans eZ4)
  · left
    exact exists_orderOf_eq_four_of_quaternion (eA.symm.trans eQ)
  · right; right; right; right; left
    refine ⟨?_, ⟨eA.symm.trans eS3⟩⟩
    rcases hMJ with he | he
    · obtain ⟨e⟩ := he
      exact Or.inl ⟨eI.symm.trans e⟩
    · obtain ⟨e⟩ := he
      exact Or.inr ⟨eI.symm.trans e⟩
  · right; right; right; right; right
    refine ⟨(x : G), Subgroup.mem_subgroupOf.mp hxA, fun h => hx1 (Subtype.ext h), ?_⟩
    rcases hk with hk | hk
    · have := Sec13.inducesStdKind_sub C K' hk
      rw [hK'K] at this
      exact Or.inl this
    · have := Sec13.inducesStdKind_sub C K' hk
      rw [hK'K] at this
      exact Or.inr this

end Cases

end CFSG.RankThree.PartTwo.Sec12.Proof128
