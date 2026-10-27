module

public import CFSG.Quasithin.Recognition.Stroth.Str83G2CaseB2
public import CFSG.GroupTheory.PermSylowTwo.Alt
public import CFSG.Quasithin.Recognition.Stroth.Str83G2PartTwoSzK
public import CFSG.Quasithin.Recognition.Stroth.Str83G2CaseB
public import CFSG.Quasithin.Recognition.Stroth.Str83G2Tools2
public import CFSG.Quasithin.Recognition.Stroth.Str83G2Tools3

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.GH74.Uniqueness.Bender
open CFSG.LieType.BorelTits
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]
variable {L1 L2 S : Subgroup G} {a : ℕ}

theorem bigB_le_normalizer_Z1 (L1 L2 S : Subgroup G) :
    bigB L1 L2 S ≤ Subgroup.normalizer (Z1 L1 L2 S : Set G) := by
  have hBP1 : bigB L1 L2 S ≤ P1 L1 L2 S := by
    rw [bigB, P1]
    exact le_sup_right
  exact hBP1.trans ((le_normalizer_pCoreOf 2 (P1 L1 L2 S)).trans
    (A4.normalizer_le_normalizer_omegaOneCenterOf (Q1 L1 L2 S)))


theorem str83_partTwo_caseB_step4_dimension
    (hF : F112HypW L1 L2 S) (hB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (ha : 1 ≤ a) (hSz : Nonempty (oTwoQuot ↥L1 ≃* Sz a))
    (hL2 : IsL2Quot (2 * a + 1) (oTwoQuot ↥L2))
    (hII : ¬ L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G))
    (hZ2 : L2 ⊔ S ≤ Subgroup.centralizer (Z2 L1 L2 S : Set G))
    (hJ : ¬ jAtLeast (2 ^ pRank 2 S) (2 ^ (2 * a + 1)) S ≤ Q1 L1 L2 S)
    (hBc : Z1 L1 L2 S ≤ Q2 L1 L2 S)
    {D2 : Subgroup G} (hD2 : RonanF13.HallTwoPrime D2 (borelOf L2 S))
    (hB2D : borelOf L2 S = (S ⊓ L2) ⊔ D2) :
    (2 ^ (2 * a + 1)) ^ 2 ≤ Nat.card ↥(Z1 L1 L2 S ⊓
      Subgroup.centralizer (D2 : Set G)) := by
  classical
  obtain ⟨hXe, hXQ, hCount, hNat⟩ :=
    str83_partTwo_caseB_steps123 hF hB ha hSz hL2 hII hZ2 hJ hBc
  have hS1 : S = (S ⊓ L1) ⊔ Q1 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_left hF.1 hB (Or.inl ⟨a, ha, hSz⟩)
  have hS2 : S = (S ⊓ L2) ⊔ Q2 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_right hF.1 hB (Or.inr (Or.inr ⟨2 * a + 1, by omega, hL2⟩))
  have hQ1S : Q1 L1 L2 S ≤ S := by
    conv_rhs => rw [hS1]
    exact le_sup_right
  have hQ2S : Q2 L1 L2 S ≤ S := by
    conv_rhs => rw [hS2]
    exact le_sup_right
  set H : Subgroup G := L2 ⊔ S with hHdef
  set V : Subgroup G := Z1 L1 L2 S with hVdef
  set X : Subgroup G := conjClosure V H with hXdef
  letI : CommGroup ↥X := hXe.1.instCommGroup
  have hHleP2 : H ≤ P2 L1 L2 S := by
    rw [hHdef]
    exact sup_le le_sup_left ((le_sup_right : S ≤ bigB L1 L2 S).trans le_sup_right)
  have hXQ2 : X ≤ Q2 L1 L2 S := by
    rw [hXdef]
    refine conjClosure_le fun g hg v hv => ?_
    exact (Subgroup.mem_normalizer_iff.mp
      (le_normalizer_pCoreOf 2 (P2 L1 L2 S) (hHleP2 hg)) v).mp (hBc hv)
  have hXH : X ≤ H := (hXQ2.trans hQ2S).trans le_sup_right
  have hX2 : IsPGroup 2 X := hXe.isPGroup
  have hHX : H ≤ Subgroup.normalizer (X : Set G) := by
    rw [hXdef]
    exact le_normalizer_conjClosure V H
  have hXnormal : IsNormalIn H X X :=
    ⟨le_rfl, fun g hg x hx =>
      (Subgroup.mem_normalizer_iff.mp (hHX hg) x).mp hx⟩
  have hVX : V ≤ X := by rw [hXdef]; exact le_conjClosure V H
  have hVe : IsElemAbelian 2 V := by
    rw [hVdef]; exact SmithC27.isElemAbelian_omegaOneCenterOf (Q1 L1 L2 S)
  have hV2 : IsPGroup 2 V := hVe.isPGroup
  have hVcard : Nat.card ↥V = (2 ^ (2 * a + 1)) ^ 4 := by
    rw [hVdef, str83_partTwo_card_z1 hF hB ha hSz hL2 hII hZ2 hJ]
    rw [show 2 ^ (4 * (2 * a + 1)) = (2 ^ (2 * a + 1)) ^ 4 by
      rw [← pow_mul, mul_comm]]
  obtain ⟨w, hwH, hwD, -, -, hSw⟩ :=
    frameT1 hF hB ha hSz hL2 hD2.1 hD2.2.1 hB2D.symm
  have hJQ1 : thompsonJ S ≤ Q1 L1 L2 S :=
    thompsonJ_le_Q1_of_caseII hF hB (Or.inl ⟨a, ha, hSz⟩) hII
  have hJQ2 : ¬ thompsonJ S ≤ Q2 L1 L2 S :=
    not_thompsonJ_le_Q2_of_caseII hF hB (Or.inl ⟨a, ha, hSz⟩) hII
  have hQ1Q2 : Q1 L1 L2 S ⊔ Q2 L1 L2 S = S :=
    q1_sup_q2_eq_s_of_caseII hF ha hSz hL2 hJQ1 hJQ2
  have hQ1n : S ≤ Subgroup.normalizer (Q1 L1 L2 S : Set G) :=
    ((le_sup_right : S ≤ bigB L1 L2 S).trans le_sup_right).trans
      (le_normalizer_pCoreOf 2 (P1 L1 L2 S))
  have hQ2n : S ≤ Subgroup.normalizer (Q2 L1 L2 S : Set G) :=
    ((le_sup_right : S ≤ bigB L1 L2 S).trans le_sup_right).trans
      (le_normalizer_pCoreOf 2 (P2 L1 L2 S))
  have hQ2H : H ≤ Subgroup.normalizer (Q2 L1 L2 S : Set G) := by
    rw [hHdef]
    exact sup_le ((le_sup_left : L2 ≤ P2 L1 L2 S).trans
      (le_normalizer_pCoreOf 2 (P2 L1 L2 S))) hQ2n
  have hV1 : Q1 L1 L2 S ≤ Subgroup.centralizer (V : Set G) := by
    rw [hVdef]
    exact SmithC27.pCoreOf_le_centralizer_omegaOneCenterOf (P1 L1 L2 S)
  have hSnormV : S ≤ Subgroup.normalizer (V : Set G) := by
    rw [hVdef]
    exact ((le_sup_right : S ≤ bigB L1 L2 S).trans le_sup_right).trans
      ((le_normalizer_pCoreOf 2 (P1 L1 L2 S)).trans
        (A4.normalizer_le_normalizer_omegaOneCenterOf (Q1 L1 L2 S)))
  have hV2n : Q2 L1 L2 S ≤ Subgroup.normalizer (V : Set G) := hQ2S.trans hSnormV
  have hT4 := inf_conjugate_centralized_of_le (H0 := H) (S := S) (Q1 := Q1 L1 L2 S)
    (Q2 := Q2 L1 L2 S) (V := V) hSw hwH hQ1Q2 hQ1S hQ2S hQ1n hQ2n
    (pCoreOf_isPGroup 2 (P2 L1 L2 S)) hQ2H hV1 hV2n
  have hD2H : D2 ≤ H := by
    rw [hHdef]
    exact (hD2.1.trans (F1.borelOf_le L2 S)).trans le_sup_left
  have hD2B : D2 ≤ bigB L1 L2 S := by
    rw [bigB]
    exact hD2.1.trans (le_sup_right.trans le_sup_left)
  have hD2V : D2 ≤ Subgroup.normalizer (V : Set G) := hD2B.trans (bigB_le_normalizer_Z1 L1 L2 S)
  have hD2odd : Odd (Nat.card D2) := hD2.2.1
  have hD2O2 : D2 ≤ oTwoUpper H := by
    intro d hd
    exact mem_oTwoUpper_of_odd (hD2H hd)
      (Odd.of_dvd_nat hD2odd (Subgroup.orderOf_dvd_natCard D2 hd))
  have hD2Cinf : D2 ≤ Subgroup.centralizer (V ⊓ conjugate V w : Set G) :=
    hD2O2.trans hT4
  have hD2Vw : D2 ≤ Subgroup.normalizer (conjugate V w : Set G) := by
    have hconjD : conjugate D2 w = D2 := conjugate_eq_self_of_mem_normalizer hwD
    intro d hd
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      rw [mem_conjugate_iff] at hx ⊢
      have hwd : w * d * w⁻¹ ∈ D2 := by
        have : d ∈ conjugate D2 w := by rw [hconjD]; exact hd
        exact (mem_conjugate_iff D2 w d).mp this
      have hconj : (w * d * w⁻¹) * (w * x * w⁻¹) * (w * d * w⁻¹)⁻¹ ∈ V :=
        (Subgroup.mem_normalizer_iff.mp (hD2V hwd) (w * x * w⁻¹)).mp hx
      convert hconj using 1
      group
    · intro hx
      rw [mem_conjugate_iff] at hx ⊢
      have hwd : w * d * w⁻¹ ∈ D2 := by
        have : d ∈ conjugate D2 w := by rw [hconjD]; exact hd
        exact (mem_conjugate_iff D2 w d).mp this
      have hconj : (w * d * w⁻¹) * (w * x * w⁻¹) * (w * d * w⁻¹)⁻¹ ∈ V := by
        convert hx using 1
        group
      exact (Subgroup.mem_normalizer_iff.mp (hD2V hwd) (w * x * w⁻¹)).mpr hconj
  haveI : Fintype (GaloisField 2 (2 * a + 1)) := Fintype.ofFinite _
  have hGF : Nat.card (GaloisField 2 (2 * a + 1)) = 2 ^ (2 * a + 1) :=
    GaloisField.card 2 (2 * a + 1) (by omega)
  have hb : ∀ L N : Subgroup G, IsChiefStep H X L N → ¬ IsCentralStep H L N →
      Nat.card (N ⧸ L.subgroupOf N) ≤ (2 ^ (2 * a + 1)) ^ 2 := by
    intro L N hstep hnc
    let hE := CFSG.Quasithin.isElemAbelian_chiefMod hstep hXH hX2
    have hnat := hNat L N hstep hXH hnc hE
    rw [natCard_quotient_of_isNaturalChiefStep (h := hnat), hGF]
  have hXbound : Nat.card ↥⁅X, D2⁆ ≤ (2 ^ (2 * a + 1)) ^ 4 :=
    card_commutator_le_of_two_steps (q := 2 ^ (2 * a + 1))
      hXH hXnormal hXe hD2H hD2odd hCount hb
  have hcommX : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x := by
    intro x hx y hy
    simpa using (hXe.1.is_comm.comm (⟨x, hx⟩ : ↥X) (⟨y, hy⟩ : ↥X))
  have hVD : ⁅V, D2⁆ ≤ V := CFSG.QuasithinUnique.Setup.Layer.commutator_le_left hD2V
  have hVwD : ⁅conjugate V w, D2⁆ ≤ conjugate V w :=
    CFSG.QuasithinUnique.Setup.Layer.commutator_le_left hD2Vw
  have hconjcomm : conjugate ⁅V, D2⁆ w = ⁅conjugate V w, D2⁆ := by
    calc conjugate ⁅V, D2⁆ w
        = (⁅V, D2⁆).map (MulAut.conj w⁻¹).toMonoidHom := rfl
      _ = ⁅V.map (MulAut.conj w⁻¹).toMonoidHom,
            D2.map (MulAut.conj w⁻¹).toMonoidHom⁆ := Subgroup.map_commutator _ _ _
      _ = ⁅conjugate V w, conjugate D2 w⁆ := rfl
      _ = ⁅conjugate V w, D2⁆ := by rw [conjugate_eq_self_of_mem_normalizer hwD]
  have hcardVw : Nat.card ↥⁅conjugate V w, D2⁆ = Nat.card ↥⁅V, D2⁆ := by
    rw [← hconjcomm]
    exact Subgroup.card_map_of_injective (f := (MulAut.conj w⁻¹).toMonoidHom)
      (MulAut.conj w⁻¹).injective
  have hVinf : ⁅V, D2⁆ ⊓ ⁅conjugate V w, D2⁆ = ⊥ := by
    refine le_bot_iff.mp ?_
    intro x hx
    have hxV : x ∈ V := hVD hx.1
    have hxVw : x ∈ conjugate V w := hVwD hx.2
    have hxD : x ∈ ⁅X, D2⁆ :=
      (Subgroup.commutator_mono hVX le_rfl) hx.1
    have hxC : x ∈ Subgroup.centralizer (D2 : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro d hd
      exact (Subgroup.mem_centralizer_iff.mp (hD2Cinf hd) x ⟨hxV, hxVw⟩).symm
    have hD2NX : D2 ≤ Subgroup.normalizer (X : Set G) :=
      hD2H.trans (D14.le_normalizer_of_isNormalIn (H := H) (U := X) hXnormal)
    have hbot : ⁅X, D2⁆ ⊓ Subgroup.centralizer (D2 : Set G) = ⊥ :=
      CFSG.Quasithin.Vol2.Ch10.SecA.commutator_inf_centralizer_eq_bot
        (W := X) (D := D2) (h2 := hXe.2) hD2odd hD2NX
    have : x ∈ ⁅X, D2⁆ ⊓ Subgroup.centralizer (D2 : Set G) := ⟨hxD, hxC⟩
    rwa [hbot] at this
  have hD2NX : D2 ≤ Subgroup.normalizer (X : Set G) :=
    hD2H.trans (D14.le_normalizer_of_isNormalIn (H := H) (U := X) hXnormal)
  have hXw : conjugate X w = X := conjugate_eq_self_of_mem_normalizer (hHX hwH)
  have hVwX : conjugate V w ≤ X :=
    (Subgroup.map_mono hVX).trans (le_of_eq hXw)
  have hsup_le : ⁅V, D2⁆ ⊔ ⁅conjugate V w, D2⁆ ≤ ⁅X, D2⁆ :=
    sup_le (Subgroup.commutator_mono hVX le_rfl)
      (Subgroup.commutator_mono hVwX le_rfl)
  have hcard_sup : Nat.card ↥(⁅V, D2⁆ ⊔ ⁅conjugate V w, D2⁆) =
      Nat.card ↥⁅V, D2⁆ * Nat.card ↥⁅conjugate V w, D2⁆ := by
    have hprod := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute
      ⁅V, D2⁆ ⁅conjugate V w, D2⁆ ?_
    · rw [hVinf, Subgroup.card_bot, mul_one] at hprod
      exact hprod.1
    · intro a ha b hb
      exact hcommX a (hVX (hVD ha)) b (hVwX (hVwD hb))
  have hcard_sup' : Nat.card ↥(⁅V, D2⁆ ⊔ ⁅conjugate V w, D2⁆) =
      Nat.card ↥⁅V, D2⁆ ^ 2 := by
    rw [hcard_sup, hcardVw, pow_two]
  have hcard_sup_le : Nat.card ↥⁅V, D2⁆ ^ 2 ≤ (2 ^ (2 * a + 1)) ^ 4 := by
    rw [← hcard_sup']
    exact (Subgroup.card_le_of_le hsup_le).trans hXbound
  have hVD_le : Nat.card ↥⁅V, D2⁆ ≤ (2 ^ (2 * a + 1)) ^ 2 := by
    have hq4 : (2 ^ (2 * a + 1)) ^ 4 = ((2 ^ (2 * a + 1)) ^ 2) ^ 2 := by ring
    rw [hq4] at hcard_sup_le
    exact (Nat.pow_le_pow_iff_left (by norm_num : 2 ≠ 0)).mp hcard_sup_le
  have hcop : Nat.Coprime (Nat.card D2) (Nat.card V) := by
    obtain ⟨k, hk⟩ := hV2.exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_right k (Odd.coprime_two_right hD2odd)
  obtain ⟨hsupV, hdisjV⟩ :=
    CFSG.QuasithinUnique.Setup.Layer.coprime_abelian_decomp V D2 hD2V
      (fun x y => by
        simpa using (hVe.1.is_comm.comm (x : ↥V) (y : ↥V))) hcop
  have hcardVsplit : Nat.card ↥V = Nat.card ↥(V ⊓ Subgroup.centralizer (D2 : Set G)) *
      Nat.card ↥⁅V, D2⁆ := by
    have hprod := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute
      (V ⊓ Subgroup.centralizer (D2 : Set G)) ⁅V, D2⁆ ?_
    · have hinf : (V ⊓ Subgroup.centralizer (D2 : Set G)) ⊓ ⁅V, D2⁆ = ⊥ :=
        disjoint_iff.mp hdisjV
      rw [hsupV, hinf, Subgroup.card_bot, mul_one] at hprod
      exact hprod.1
    · intro a ha b hb
      simpa using (hVe.1.is_comm.comm (⟨a, ha.1⟩ : ↥V) (⟨b, hVD hb⟩ : ↥V))
  have hC_ge : (2 ^ (2 * a + 1)) ^ 2 ≤
      Nat.card ↥(V ⊓ Subgroup.centralizer (D2 : Set G)) := by
    have hle : (2 ^ (2 * a + 1)) ^ 2 * (2 ^ (2 * a + 1)) ^ 2 ≤
        Nat.card ↥(V ⊓ Subgroup.centralizer (D2 : Set G)) *
          (2 ^ (2 * a + 1)) ^ 2 := by
      calc (2 ^ (2 * a + 1)) ^ 2 * (2 ^ (2 * a + 1)) ^ 2
          = (2 ^ (2 * a + 1)) ^ 4 := by ring
        _ = Nat.card ↥V := hVcard.symm
        _ = Nat.card ↥(V ⊓ Subgroup.centralizer (D2 : Set G)) *
              Nat.card ↥⁅V, D2⁆ := hcardVsplit
        _ ≤ Nat.card ↥(V ⊓ Subgroup.centralizer (D2 : Set G)) *
              (2 ^ (2 * a + 1)) ^ 2 := Nat.mul_le_mul_left _ hVD_le
    exact Nat.le_of_mul_le_mul_right hle (by positivity)
  simpa [hVdef] using hC_ge



theorem str83_partTwo_caseB_step4
    (hF : F112HypW L1 L2 S) (hB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (ha : 1 ≤ a) (hSz : Nonempty (oTwoQuot ↥L1 ≃* Sz a))
    (hL2 : IsL2Quot (2 * a + 1) (oTwoQuot ↥L2))
    (hII : ¬ L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G))
    (hZ2 : L2 ⊔ S ≤ Subgroup.centralizer (Z2 L1 L2 S : Set G))
    (hJ : ¬ jAtLeast (2 ^ pRank 2 S) (2 ^ (2 * a + 1)) S ≤ Q1 L1 L2 S)
    (hBc : Z1 L1 L2 S ≤ Q2 L1 L2 S)
    {D1 D2 : Subgroup G}
    (hD1 : RonanF13.HallTwoPrime D1 (borelOf L1 S))
    (hD2 : RonanF13.HallTwoPrime D2 (borelOf L2 S))
    (hB2D : borelOf L2 S = (S ⊓ L2) ⊔ D2)
    (hdelta : ∀ d ∈ D2, ∃ δ ∈ D1, ∀ l ∈ L1,
      (d * δ⁻¹) * l * (d * δ⁻¹)⁻¹ * l⁻¹ ∈ pCoreOf 2 L1) :
    D2 ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G) := by
  classical
  have hC_ge := str83_partTwo_caseB_step4_dimension hF hB ha hSz hL2 hII hZ2 hJ hBc hD2 hB2D
  have hD2H : D2 ≤ L2 ⊔ S :=
    (hD2.1.trans (F1.borelOf_le L2 S)).trans le_sup_left
  have hD2B : D2 ≤ bigB L1 L2 S := by
    rw [bigB]
    exact hD2.1.trans (le_sup_right.trans le_sup_left)
  have hq4 : 4 ≤ 2 ^ (2 * a + 1) := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  intro d hd
  obtain ⟨δ, hδD1, hδcomm⟩ := hdelta d hd
  by_cases hδ1 : δ = 1
  ·
    subst hδ1
    refine str83_partTwo_lemmaK_centralizes hF hB ha hSz hL2 hII hZ2 hJ (hD2B hd)
      (hZ2 (hD2H hd)) ?_
    simpa using hδcomm
  ·
    have hCle := str83_partTwo_card_centralizer_le hF hB ha hSz hL2 hII hZ2 hJ
      hD1 (hD2B hd) hδD1 hδ1 hδcomm
    have hle : Nat.card ↥(Z1 L1 L2 S ⊓ Subgroup.centralizer (D2 : Set G)) ≤
        Nat.card ↥(Z1 L1 L2 S ⊓ Subgroup.centralizer ({d} : Set G)) :=
      Subgroup.card_le_of_le
        (inf_le_inf_left _ (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hd)))
    have hqsq : (2 ^ (2 * a + 1)) ^ 2 ≤ 2 ^ (2 * a + 1) := hC_ge.trans hle |>.trans hCle
    have hq : 2 ≤ 2 ^ (2 * a + 1) := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have : 2 ^ (2 * a + 1) * 2 ^ (2 * a + 1) ≤ 2 ^ (2 * a + 1) := by
      simpa [pow_two] using hqsq
    exact absurd this (not_le.mpr (by nlinarith))


theorem exists_topmost_noncentral_factor {H X N : Subgroup G} {c : ℕ}
    (hser : IsChiefSeriesFrom H X N c) (hc : 0 < c) :
    ∃ M L : Subgroup G, L ≤ M ∧ M ≤ N ∧ IsChiefStep H X L M ∧
      ¬ IsCentralStep H L M ∧ F112W.IsChiefSeriesBetween H X M N 0 := by
  induction hser with
  | bot => exact absurd hc (Nat.lt_irrefl 0)
  | @central N L n hstep hcent hs ih =>
      obtain ⟨M, L', hL'M, hMN, hstep', hnc', hbetween⟩ := ih hc
      exact ⟨M, L', hL'M, hMN.trans hstep.2.2.1.le, hstep', hnc',
        F112W.IsChiefSeriesBetween.central hstep hcent hbetween⟩
  | @noncentral N L n hstep hnc hs ih =>
      exact ⟨N, L, hstep.2.2.1.le, le_rfl, hstep, hnc, F112W.IsChiefSeriesBetween.refl⟩

theorem topmost_factor_eq_of_le {H0 S X V D N L : Subgroup G} {w : G}
    (hXH0 : X ≤ H0) (hX : H0 ≤ Subgroup.normalizer (X : Set G))
    (hXe : IsElemAbelian 2 X)
    (hHN : H0 ≤ Subgroup.normalizer (N : Set G))
    (hHL : H0 ≤ Subgroup.normalizer (L : Set G))
    (hLN : L ≤ N) (hNX : N ≤ X) (hVX : V ≤ X)
    (hgen : X = conjClosure V H0)
    (hDodd : Odd (Nat.card D))
    (hD : D ≤ oTwoUpper H0)
    (hDV : D ≤ Subgroup.centralizer (V : Set G))
    (hS : IsSylowTwoOf S H0)
    (hVS : S ≤ Subgroup.normalizer (V : Set G))
    (hSw : S ⊔ conjugate S w = H0) (hwH : w ∈ H0)
    (hwD : w ∈ Subgroup.normalizer (D : Set G))
    (hO2 : ⁅X, oTwoUpper H0⁆ ≤ N)
    (hC : ∀ x ∈ N, (∀ d ∈ D, x * d * x⁻¹ * d⁻¹ ∈ L) → x ∈ L) :
    N = L := by
  classical
  let Hs := ↥H0
  let S' : Subgroup Hs := S.subgroupOf H0
  let X' : Subgroup Hs := X.subgroupOf H0
  let V' : Subgroup Hs := V.subgroupOf H0
  let D' : Subgroup Hs := D.subgroupOf H0
  let N' : Subgroup Hs := N.subgroupOf H0
  let L' : Subgroup Hs := L.subgroupOf H0
  let w' : Hs := ⟨w, hwH⟩
  have hSH0 : S ≤ H0 := hSw ▸ le_sup_left
  have hNH0 : N ≤ H0 := fun x hx => hXH0 (hNX hx)
  have hLH0 : L ≤ H0 := fun x hx => hNH0 (hLN hx)
  have hVH0 : V ≤ H0 := fun x hx => hXH0 (hVX hx)
  have hDH0 : D ≤ H0 := hD.trans (oTwoUpper_le H0)
  have hX'normal : X'.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hXH0).mpr hX
  have hN'normal : N'.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNH0).mpr hHN
  have hL'normal : L'.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLH0).mpr hHL
  have hXe' : IsElemAbelian 2 X' := hXe.subgroupOf H0
  have hLN' : L' ≤ N' := fun x hx => hLN (Subgroup.mem_subgroupOf.mp hx)
  have hNX' : N' ≤ X' := fun x hx => hNX (Subgroup.mem_subgroupOf.mp hx)
  have hVX' : V' ≤ X' := fun x hx => hVX (Subgroup.mem_subgroupOf.mp hx)
  have hDodd' : Odd (Nat.card D') := by
    rw [show Nat.card D' = Nat.card D from
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDH0).toEquiv]
    exact hDodd
  have hD' : D' ≤ oTwoUpper (⊤ : Subgroup Hs) := by
    intro d' hd'
    have hdD : (d' : G) ∈ D := Subgroup.mem_subgroupOf.mp hd'
    have hmap := oTwoUpper_map H0.subtype (⊤ : Subgroup Hs)
    rw [Subgroup.map_top, Subgroup.range_subtype] at hmap
    have hdO : (d' : G) ∈ (oTwoUpper (⊤ : Subgroup Hs)).map H0.subtype := by
      rw [← hmap]; exact hD hdD
    obtain ⟨e, he, hee⟩ := Subgroup.mem_map.mp hdO
    have heq : e = d' := Subtype.ext hee
    rwa [heq] at he
  have hDV' : D' ≤ Subgroup.centralizer (V' : Set Hs) := by
    intro d' hd'
    rw [Subgroup.mem_centralizer_iff]
    intro v' hv'
    have hdD : (d' : G) ∈ D := Subgroup.mem_subgroupOf.mp hd'
    have hvV : (v' : G) ∈ V := Subgroup.mem_subgroupOf.mp hv'
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hDV hdD) (v' : G) hvV)
  have hS' : IsSylowTwoOf S' ⊤ := CFSG.GroupTheory.PermSylowTwo.isSylowTwoOf_subgroupOf_top hS
  have hVS' : S' ≤ Subgroup.normalizer (V' : Set Hs) := by
    rw [← Subgroup.subgroupOf_normalizer_eq hVH0]
    intro s hs
    exact (Subgroup.mem_subgroupOf.mpr (hVS hs))
  have hSw' : S' ⊔ conjugate S' w' = ⊤ := by
    apply Subgroup.map_injective H0.subtype_injective
    calc (S' ⊔ conjugate S' w').map H0.subtype
        = S'.map H0.subtype ⊔ (conjugate S' w').map H0.subtype := Subgroup.map_sup _ _ _
      _ = S ⊔ conjugate S w := by
          rw [Subgroup.map_subgroupOf_eq_of_le hSH0, CFSG.map_conjugate,
            Subgroup.map_subgroupOf_eq_of_le hSH0]
          rfl
      _ = H0 := hSw
      _ = (⊤ : Subgroup Hs).map H0.subtype := by
          rw [Subgroup.map_top, Subgroup.range_subtype]
  have hwD' : w' ∈ Subgroup.normalizer (D' : Set Hs) := by
    rw [← Subgroup.subgroupOf_normalizer_eq hDH0]
    exact Subgroup.mem_subgroupOf.mpr hwD
  have hgen' : X' = conjClosure V' ⊤ := by
    apply Subgroup.map_injective H0.subtype_injective
    calc X'.map H0.subtype = X := Subgroup.map_subgroupOf_eq_of_le hXH0
      _ = conjClosure V H0 := hgen
      _ = (conjClosure V' ⊤).map H0.subtype := by
          rw [CFSG.Quasithin.map_conjClosure_eq, Subgroup.map_subgroupOf_eq_of_le hVH0,
            Subgroup.map_top, Subgroup.range_subtype]
  have hO2' : ⁅X', oTwoUpper (⊤ : Subgroup Hs)⁆ ≤ N' := by
    rw [Subgroup.commutator_le]
    intro x' hx' y' hy'
    have hxX : (x' : G) ∈ X := Subgroup.mem_subgroupOf.mp hx'
    have hmap := oTwoUpper_map H0.subtype (⊤ : Subgroup Hs)
    rw [Subgroup.map_top, Subgroup.range_subtype] at hmap
    have hyO : (y' : G) ∈ oTwoUpper H0 := by
      rw [hmap]
      exact Subgroup.mem_map_of_mem H0.subtype hy'
    have hcomm : (x' : G) * (y' : G) * (x' : G)⁻¹ * (y' : G)⁻¹ ∈ N :=
      hO2 (Subgroup.commutator_mem_commutator hxX hyO)
    have hcoe : ((x' * y' * x'⁻¹ * y'⁻¹ : Hs) : G) =
        (x' : G) * (y' : G) * (x' : G)⁻¹ * (y' : G)⁻¹ := by
      rfl
    exact Subgroup.mem_subgroupOf.mpr (hcoe ▸ hcomm)
  have hC' : ∀ x ∈ N', (∀ d ∈ D', x * d * x⁻¹ * d⁻¹ ∈ L') → x ∈ L' := by
    intro x' hx' hxd
    have hxN : (x' : G) ∈ N := Subgroup.mem_subgroupOf.mp hx'
    have hxdG : ∀ d ∈ D, (x' : G) * d * (x' : G)⁻¹ * d⁻¹ ∈ L := by
      intro d hd
      have hd' : (⟨d, hDH0 hd⟩ : Hs) ∈ D' := Subgroup.mem_subgroupOf.mpr hd
      exact Subgroup.mem_subgroupOf.mp (hxd ⟨d, hDH0 hd⟩ hd')
    exact Subgroup.mem_subgroupOf.mpr (hC (x' : G) hxN hxdG)
  haveI : L'.Normal := hL'normal
  haveI : N'.Normal := hN'normal
  have hN'eq : N' = L' :=
    topmost_factor_eq (H := Hs) (X := X') (V := V') (D := D') (S := S')
      (N := N') (L := L') (w := w') hX'normal hXe' hLN' hNX' hVX' hgen' hDodd'
      hD' hDV' hS' hVS' hSw' hwD' hO2' hC'
  calc N = N'.map H0.subtype := (Subgroup.map_subgroupOf_eq_of_le hNH0).symm
    _ = L'.map H0.subtype := by rw [hN'eq]
    _ = L := Subgroup.map_subgroupOf_eq_of_le hLH0

private theorem card_eq_one_of_isPGroup_two_of_odd {H : Type} [Group H] [Finite H]
    (hH : IsPGroup 2 H) (hodd : Odd (Nat.card H)) : Nat.card H = 1 := by
  obtain ⟨k, hk⟩ := hH.exists_card_eq
  have hk0 : k = 0 := by
    rcases k with _ | m
    · rfl
    · exfalso
      have heven : Even (2 ^ (m + 1)) := ⟨2 ^ m, by rw [pow_succ]; omega⟩
      exact (Nat.not_even_iff_odd.mpr (hk ▸ hodd)) heven
  rw [hk, hk0]
  simp

private theorem exists_sylow_image_L2
    {G : Type} [Group G] [Finite G] {L S : Subgroup G}
    (hsyl : IsSylowTwoOf (S ⊓ L) L) :
    ∃ (Q : Sylow 2 (oTwoQuot ↥L)) (_hQ : (Q : Subgroup (oTwoQuot ↥L)) =
      ((S ⊓ L).subgroupOf L).map (QuotientGroup.mk' (pCore 2 ↥L))),
      ((borelOf L S).subgroupOf L).map (QuotientGroup.mk' (pCore 2 ↥L)) =
        GH74.Uniqueness.Bender.borel (Q : Subgroup (oTwoQuot ↥L)) := by
  obtain ⟨hpg, hodd, hmap⟩ := CFSG.Quasithin.F1.map_borelOf_eq_normalizer hsyl
  exact ⟨hpg.toSylow hodd, IsPGroup.toSylow_coe hpg hodd, hmap⟩

theorem not_isPGroup_borelOf_of_l2_local
    {G : Type} [Group G] [Finite G] {L S : Subgroup G} {f : ℕ}
    (hsyl : IsSylowTwoOf (S ⊓ L) L) (hf : 2 ≤ f) (hL2 : IsL2Quot f (oTwoQuot ↥L)) :
    ¬ IsPGroup 2 ↥(borelOf L S) := by
  intro hB2
  obtain ⟨e⟩ := hL2
  have hBt : BenderType (oTwoQuot ↥L) f 1 1 := BenderType.linear f hf e
  obtain ⟨Q, hQ, himg⟩ := exists_sylow_image_L2 hsyl
  obtain ⟨t, hc⟩ := hBt.exists_benderCore Q
  have hsub2 : IsPGroup 2 ↥((borelOf L S).subgroupOf L) :=
    hB2.of_equiv (Subgroup.subgroupOfEquivOfLe (F1.borelOf_le L S)).symm
  have hcart2 : IsPGroup 2 ↥(cartan (Q : Subgroup (oTwoQuot ↥L)) t) := by
    refine (hsub2.map (QuotientGroup.mk' (pCore 2 ↥L))).to_le ?_
    rw [himg]
    exact cartan_le_borel Q t
  have hodd : Odd (Nat.card ↥(cartan (Q : Subgroup (oTwoQuot ↥L)) t)) := by
    rw [hc.card_cartan, mul_one]
    exact odd_two_pow_sub_one (m := f) (by omega)
  have h1 := card_eq_one_of_isPGroup_two_of_odd hcart2 hodd
  rw [hc.card_cartan, mul_one] at h1
  have h4 : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  omega

end CFSG.Quasithin.Stroth

end
