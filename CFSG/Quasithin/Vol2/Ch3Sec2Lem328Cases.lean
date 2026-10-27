module

public import CFSG.Quasithin.Vol2.Ch3Sec2Lem328Sec
public import CFSG.Quasithin.Vol2.Ch3Sec2Lem328Iso
public import CFSG.Quasithin.Vol2.Ch3Sec2Inputs
public import CFSG.Quasithin.Background.G64Realize
public import CFSG.Quasithin.Background.B5FinSp
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238BridgeAlt57G2Eq
public import CFSG.Quasithin.Background.B1MoreTenD
public import CFSG.Quasithin.Background.B5FinG2U33
public import CFSG.Quasithin.Background.B5Irr
public import CFSG.Quasithin.Background.JonesParshallG2Field

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint
open scoped commutatorElement

variable {V : Type} [CommGroup V] [Finite V]

@[expose] def Concl328 (L T : Subgroup (MulAut V)) : Prop :=
  (∃ n : ℕ, LieModel ↥L .PSL 2 2 n ∧ BinaryNaturalSL L ⊤ (fixV L) 2 n) ∨
  ((∃ (n : ℕ) (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
      Nonempty (↥L ≃* Matrix.SpecialLinearGroup (Fin 3) K) ∧ BinaryNaturalSL L ⊤ ⊥ 3 n) ∨
    (Nonempty (↥L ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) ∧ Nat.card V = 2 ^ 4 ∧
      BinaryNaturalSL L ⊤ (fixV L) 3 1)) ∨
  (∃ (n : ℕ) (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
    Nonempty (↥L ≃* ↥(Assembly.LowTwoRank.StatedSp 2 K)) ∧ BinaryNaturalSp4 L ⊤ (fixV L) n) ∨
  (∃ (n : ℕ) (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
    Nonempty (↥L ≃* ↥⁅quasithinG2 K, quasithinG2 K⁆) ∧ G2NaturalDerived L ⊤ (fixV L) n) ∨
  ((Nonempty (↥L ≃* alternatingGroup (Fin 5)) ∧ AlternatingNatural L ⊤ ⊥ 5) ∨
    (Nonempty (↥L ≃* alternatingGroup (Fin 7)) ∧ AlternatingNatural L ⊤ ⊥ 7)) ∨
  (Nonempty (↥L ≃* alternatingGroup (Fin 6)) ∧ AlternatingNatural L ⊤ (fixV L) 6) ∨
  (Nonempty (↥(L ⊔ T) ≃* alternatingGroup (Fin 7)) ∧ Nat.card V = 2 ^ 4) ∨
  (Group.IsPerfect ↥L ∧ Nat.card (Subgroup.center ↥L) = 3 ∧
    Nonempty (↥L ⧸ Subgroup.center ↥L ≃* alternatingGroup (Fin 6)) ∧ Nat.card V = 2 ^ 6) ∨
  (∃ n : ℕ, (n = 4 ∨ n = 5) ∧
    Nonempty (↥(L ⊔ T) ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) ∧
    BinaryNaturalSL L ⊤ ⊥ n 1) ∨
  (Nonempty (↥L ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) ∧ SLExteriorTwo L ⊤ (fixV L) 4) ∨
  (Nonempty (↥(L ⊔ T) ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) ∧ Nat.card V = 2 ^ 10)

theorem nonempty_g2Two_commutator_equiv
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) :
    Nonempty (↥⁅quasithinG2 K, quasithinG2 K⁆ ≃* ↥JonesParshall.subG2) := by
  have : Fintype K := Fintype.ofFinite K
  have hF : Fintype.card K = 2 := by rw [← Nat.card_eq_fintype_card, hK]
  have : CharP K 2 := charP_of_card_eq_prime_pow (f := 1) (by rw [hF, pow_one])
  let ε : K ≃+* ZMod 2 := (ZMod.ringEquivOfPrime K Nat.prime_two hF).symm
  have hc : ⁅quasithinG2 K, quasithinG2 K⁆ =
      ⁅Explicit.cayleyGroup K, Explicit.cayleyGroup K⁆ := by
    rw [CFSG.QuasithinUnique.Bridge.Alt57Model.quasithinG2_eq_cayleyGroup]
  exact ⟨(MulEquiv.subgroupCongr hc).trans (((JonesParshall.zornConj ε).subgroupMap _).trans
    (MulEquiv.subgroupCongr ((JonesParshall.map_cayley_commutator ε).trans
      JonesParshall.g2Two_commutator_eq)))⟩

theorem isSimpleGroup_g2Two_commutator
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) :
    IsSimpleGroup ↥⁅quasithinG2 K, quasithinG2 K⁆ := by
  obtain ⟨e⟩ := nonempty_g2Two_commutator_equiv hK
  have : IsSimpleGroup U33G := isSimpleGroup_u33Pres
  exact (e.trans u33EquivSubG2.symm).isSimpleGroup

abbrev SecV (L : Subgroup (MulAut V)) : Type := Sec (commV L) (fixV L ⊓ commV L)

abbrev secG (L S : Subgroup (MulAut V)) : Subgroup (MulAut (SecV L)) :=
  autSec (L ⊔ S) (commV L) (fixV L ⊓ commV L)

abbrev secL (L : Subgroup (MulAut V)) : Subgroup (MulAut (SecV L)) :=
  autSec L (commV L) (fixV L ⊓ commV L)

theorem altDn_faithful_of_five_le {m : ℕ} (hm : 5 ≤ m) : (FFModel.altDn m).Faithful :=
  fun (σ : ↥(alternatingGroup (Fin m))) hσ =>
    Subtype.ext (G64.symDn_faithful hm (σ : Equiv.Perm (Fin m)) hσ)

section Constructors

variable {L T : Subgroup (MulAut V)}

omit [Finite V] in
theorem Concl328.c1 (h : ∃ n : ℕ, LieModel ↥L .PSL 2 2 n ∧ BinaryNaturalSL L ⊤ (fixV L) 2 n) :
    Concl328 L T := Or.inl h

omit [Finite V] in
theorem Concl328.c2a (h : ∃ (n : ℕ) (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
    Nonempty (↥L ≃* Matrix.SpecialLinearGroup (Fin 3) K) ∧ BinaryNaturalSL L ⊤ ⊥ 3 n) :
    Concl328 L T := Or.inr (Or.inl (Or.inl h))

omit [Finite V] in
theorem Concl328.c2b (h : Nonempty (↥L ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) ∧
    Nat.card V = 2 ^ 4 ∧ BinaryNaturalSL L ⊤ (fixV L) 3 1) : Concl328 L T :=
  Or.inr (Or.inl (Or.inr h))

omit [Finite V] in
theorem Concl328.c3 (h : ∃ (n : ℕ) (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
    Nonempty (↥L ≃* ↥(Assembly.LowTwoRank.StatedSp 2 K)) ∧ BinaryNaturalSp4 L ⊤ (fixV L) n) :
    Concl328 L T :=
  Or.inr (Or.inr (Or.inl h))

omit [Finite V] in
theorem Concl328.c4 (h : ∃ (n : ℕ) (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
    Nonempty (↥L ≃* ↥⁅quasithinG2 K, quasithinG2 K⁆) ∧ G2NaturalDerived L ⊤ (fixV L) n) :
    Concl328 L T := Or.inr (Or.inr (Or.inr (Or.inl h)))

omit [Finite V] in
theorem Concl328.c5a (h : Nonempty (↥L ≃* alternatingGroup (Fin 5)) ∧ AlternatingNatural L ⊤ ⊥ 5) :
    Concl328 L T := Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl h)))))

omit [Finite V] in
theorem Concl328.c5b (h : Nonempty (↥L ≃* alternatingGroup (Fin 7)) ∧ AlternatingNatural L ⊤ ⊥ 7) :
    Concl328 L T := Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr h)))))

omit [Finite V] in
theorem Concl328.c6 (h : Nonempty (↥L ≃* alternatingGroup (Fin 6)) ∧
    AlternatingNatural L ⊤ (fixV L) 6) : Concl328 L T :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))

omit [Finite V] in
theorem Concl328.c7 (h : Nonempty (↥(L ⊔ T) ≃* alternatingGroup (Fin 7)) ∧ Nat.card V = 2 ^ 4) :
    Concl328 L T := Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))

omit [Finite V] in
theorem Concl328.c8 (h : Group.IsPerfect ↥L ∧ Nat.card (Subgroup.center ↥L) = 3 ∧
    Nonempty (↥L ⧸ Subgroup.center ↥L ≃* alternatingGroup (Fin 6)) ∧ Nat.card V = 2 ^ 6) :
    Concl328 L T := Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))

omit [Finite V] in
theorem Concl328.c9 (h : ∃ n : ℕ, (n = 4 ∨ n = 5) ∧
    Nonempty (↥(L ⊔ T) ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) ∧
    BinaryNaturalSL L ⊤ ⊥ n 1) : Concl328 L T :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))

omit [Finite V] in
theorem Concl328.c10 (h : Nonempty (↥L ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) ∧
    SLExteriorTwo L ⊤ (fixV L) 4) : Concl328 L T :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))

omit [Finite V] in
theorem Concl328.c11 (h : Nonempty (↥(L ⊔ T) ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) ∧
    Nat.card V = 2 ^ 10) : Concl328 L T :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))

end Constructors

namespace Sec328

variable {L S : Subgroup (MulAut V)} (h : Sec328 L S)
include h

@[expose] noncomputable def equivL : ↥L ≃* ↥(secL L) :=
  B5.secEquiv L (le_sup_left.trans h.le_stabSub_commV) (le_sup_left.trans h.le_stabSub_fixV)
    h.inf_centSec_eq_bot

theorem card_eq : Nat.card V = Nat.card ↥(fixV L ⊓ commV L) * Nat.card (SecV L) := by
  have h1 :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup ((fixV L ⊓ commV L).subgroupOf (commV L))
  have h2 : Nat.card ↥((fixV L ⊓ commV L).subgroupOf (commV L)) = Nat.card ↥(fixV L ⊓ commV L) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  have h3 : Nat.card ↥(commV L) = Nat.card V := by rw [h.top, Subgroup.card_top]
  rw [← h3, h1, h2, mul_comm]

theorem fixV_inf : fixV L ⊓ commV L = fixV L := by rw [h.top, inf_top_eq]

theorem nontrivial_secL : Nontrivial ↥(secL L) := by
  have : Nontrivial ↥L := CFSG.ComponentClassification.Quasisimple.nontrivial
    (B1Red.isQuasisimple_to_open h.quasi)
  exact h.equivL.injective.nontrivial

theorem secL_eq_genFitting : secL L = quasithinGenFitting (secG L S) := h.b4Hyp.2.1

theorem isQuasisimple_secL : CFSG.IsQuasisimple ↥(secL L) := h.b4Hyp.2.2.1

theorem conj_mem_secL {g k : MulAut (SecV L)} (hg : g ∈ secG L S) (hk : k ∈ secL L) :
    g * k * g⁻¹ ∈ secL L := by
  have hgN : g ∈ Subgroup.normalizer
      (quasithinGenFitting (secG L S) : Set (MulAut (SecV L))) :=
    le_normalizer_quasithinGenFitting (secG L S) hg
  rw [← h.secL_eq_genFitting] at hgN
  exact (Subgroup.mem_normalizer_iff.mp hgN k).mp hk

theorem secL_le_secG : secL L ≤ secG L S := by
  rw [h.secL_eq_genFitting]
  exact quasithinGenFitting_le (secG L S)

theorem eq_one_of_mem_secG {b : MulAut (SecV L)} (hb : b ∈ secG L S) (hb2 : b ^ 2 = 1)
    (hc : ∀ k ∈ secL L, b * k = k * b) : b = 1 := by
  have hMW := h.le_stabSub_commV
  have hMU := h.le_stabSub_fixV
  let e := B5.secEquiv (L ⊔ S) hMW hMU h.sup_inf_centSec_eq_bot
  let y := e.symm ⟨b, hb⟩
  have hyb : ((e y : ↥(secG L S)) : MulAut (SecV L)) = b := by
    show ((e (e.symm ⟨b, hb⟩) : ↥(secG L S)) : MulAut (SecV L)) = b
    rw [MulEquiv.apply_symm_apply]
  have hyc : ∀ l ∈ L, l * (y : MulAut V) = (y : MulAut V) * l := by
    intro l hl
    have hlM : l ∈ L ⊔ S := Subgroup.mem_sup_left hl
    have hel : ((e ⟨l, hlM⟩ : ↥(secG L S)) : MulAut (SecV L)) ∈ secL L := by
      have h1 := B5.map_secHom_eq_autSec (L ⊔ S) hMW hMU (le_sup_left : L ≤ L ⊔ S)
      have h2 : B5.secHom (L ⊔ S) hMW hMU ⟨l, hlM⟩ ∈
          (L.subgroupOf (L ⊔ S)).map (B5.secHom (L ⊔ S) hMW hMU) := ⟨⟨l, hlM⟩, hl, rfl⟩
      rw [h1] at h2
      rw [B5.secEquiv_apply]
      exact h2
    have hcomm := hc _ hel
    have : e (⟨l, hlM⟩ * y) = e (y * ⟨l, hlM⟩) := by
      apply Subtype.ext
      rw [map_mul, map_mul, Subgroup.coe_mul, Subgroup.coe_mul, hyb]
      exact hcomm.symm
    exact congrArg Subtype.val (e.injective this)
  have hy2 : (y : MulAut V) ^ 2 ^ 1 = 1 := by
    rw [pow_one]
    have : e (y ^ 2) = e 1 := by
      apply Subtype.ext
      rw [map_pow, map_one, SubgroupClass.coe_pow, hyb, hb2]
      rfl
    exact congrArg Subtype.val (e.injective this)
  have hy1 : y = 1 := Subtype.ext (h.eq_one hyc hy2)
  rw [← hyb, hy1, map_one]
  rfl

theorem le_ffJ {B : Subgroup (MulAut (SecV L))} (hB : IsFFStarOffender (secG L S) B) :
    secL L ≤ ffJ (secG L S) := by
  have hBn : ∀ b ∈ B, ∀ k ∈ secL L, b * k * b⁻¹ ∈ secL L := fun b hb k hk =>
    h.conj_mem_secL (hB.1 hb) hk
  rcases B1Red.commutator_eq_or_commute (K := secL L) (B := B)
      (Or.inl (B1Red.isQuasisimple_to_open h.isQuasisimple_secL)) hBn with hc | hc
  · exact B1Red.K_le_ffJ h.secL_le_secG hB hc
  · exfalso
    apply hB.2.1
    rw [eq_bot_iff]
    intro b hb
    exact Subgroup.mem_bot.2 (h.eq_one_of_mem_secG (hB.1 hb) (hB.2.2.1.2 b hb) (hc b hb))

theorem eq_commutator_ffJ {B : Subgroup (MulAut (SecV L))} (hB : IsFFStarOffender (secG L S) B)
    (hs : IsSimpleGroup ↥⁅ffJ (secG L S), ffJ (secG L S)⁆) :
    secL L = ⁅ffJ (secG L S), ffJ (secG L S)⁆ := by
  have hLJ : secL L ≤ ffJ (secG L S) := h.le_ffJ hB
  have hperf : Group.IsPerfect ↥(secL L) := h.isQuasisimple_secL.1
  have hLJJ : secL L ≤ ⁅ffJ (secG L S), ffJ (secG L S)⁆ := by
    calc secL L = ⁅secL L, secL L⁆ := Subgroup.commutator_eq_self.symm
      _ ≤ ⁅ffJ (secG L S), ffJ (secG L S)⁆ := Subgroup.commutator_mono hLJ hLJ
  have hJG : ffJ (secG L S) ≤ secG L S := iSup_le fun A => iSup_le fun hA => hA.1
  have hnorm : ((secL L).subgroupOf ⁅ffJ (secG L S), ffJ (secG L S)⁆).Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact h.conj_mem_secL (hJG (B5.commutator_le_self _ g.2)) hx
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      ((secL L).subgroupOf ⁅ffJ (secG L S), ffJ (secG L S)⁆) with hbot | htop
  · exfalso
    have := h.nontrivial_secL
    obtain ⟨x, hx⟩ := exists_ne (1 : ↥(secL L))
    apply hx
    have hxm : (⟨x, hLJJ x.2⟩ : ↥⁅ffJ (secG L S), ffJ (secG L S)⁆) ∈
        (secL L).subgroupOf ⁅ffJ (secG L S), ffJ (secG L S)⁆ := x.2
    rw [hbot, Subgroup.mem_bot] at hxm
    have h3 : (x : MulAut (SecV L)) = 1 := congrArg Subtype.val hxm
    exact Subtype.ext h3
  · exact le_antisymm hLJJ (Subgroup.subgroupOf_eq_top.1 htop)

theorem sup_eq_of_autSec_eq (hG : secG L S = secL L) {T : Subgroup (MulAut V)} (hTS : T ≤ S) :
    L ⊔ T = L := by
  have hLS : L ⊔ S = L := B5.eq_of_autSec_eq h.le_stabSub_commV h.le_stabSub_fixV
    h.sup_inf_centSec_eq_bot le_rfl le_sup_left hG
  exact sup_eq_left.2 (hTS.trans (le_sup_right.trans hLS.le))

theorem symmetric_case {B : Subgroup (MulAut (SecV L))} (hB : IsFFStarOffender (secG L S) B)
    {m : ℕ} (hm : 5 ≤ m) (hS : SymmetricNatural (ffJ (secG L S)) ⊤ ⊥ m) :
    AlternatingNatural (secL L) ⊤ ⊥ m ∧ Nonempty (↥(secL L) ≃* alternatingGroup (Fin m)) := by
  obtain ⟨π, hπ⟩ := hS
  obtain ⟨e⟩ := nonempty_mulEquiv_of_realizesVia (G64.symDn_faithful hm) hπ
  obtain ⟨f⟩ := nonempty_commutator_equiv_alternating hm e
  have : IsSimpleGroup (alternatingGroup (Fin m)) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; exact hm)
  have hL := h.eq_commutator_ffJ hB f.isSimpleGroup
  rw [hL]
  exact ⟨B5.alternatingNatural_derived hm ⟨π, hπ⟩, ⟨f⟩⟩

theorem le_stabSub_commV' : L ≤ stabSub (commV L) := le_sup_left.trans h.le_stabSub_commV

theorem le_stabSub_fixV' : L ≤ stabSub (fixV L ⊓ commV L) := le_sup_left.trans h.le_stabSub_fixV

theorem concl_case1 {T : Subgroup (MulAut V)} {B : Subgroup (MulAut (SecV L))}
    (hc : B42Case1 (secG L S) (secL L) B) : Concl328 L T := by
  obtain ⟨-, ⟨n, hn⟩, -, -⟩ := hc
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := BinaryNaturalSL.exists_equiv hn
  have : Nontrivial ↥L := CFSG.ComponentClassification.Quasisimple.nontrivial
    (B1Red.isQuasisimple_to_open h.quasi)
  have hmod := B5.binaryNaturalSL_of_autSec inf_le_right h.le_stabSub_commV' h.le_stabSub_fixV'
    h.inf_centSec_eq_bot hn
  rw [h.fixV_inf, h.top] at hmod
  exact Concl328.c1 ⟨n, lieModel_psl_two_of_mulEquiv h.quasi.1 hK (h.equivL.trans e.symm), hmod⟩

theorem concl_case2 (hI16 : AsI16Cover328) {T : Subgroup (MulAut V)}
    (hc : B42Case2 (secG L S) (secL L)) : Concl328 L T := by
  obtain ⟨-, ⟨n, hm⟩, -⟩ := hc
  have hWU := B5.binaryNaturalSL_of_autSec inf_le_right h.le_stabSub_commV' h.le_stabSub_fixV'
    h.inf_centSec_eq_bot hm
  have hn1 : 1 ≤ n := B5.one_le_of_binaryNaturalSL hWU
  have hI := hI16 V h.sq L h.irr
  have hbot : fixV L ⊓ commV L = ⊥ → Concl328 L T := by
    intro hC
    have hmod := hWU
    rw [hC, h.top] at hmod
    obtain ⟨K, _, _, hK, ⟨e⟩⟩ := BinaryNaturalSL.exists_equiv hmod
    exact Concl328.c2a ⟨n, K, inferInstance, inferInstance, hK,
      ⟨e.symm.trans (specialLinearGroupEquivStatedSL 3 K).symm⟩, hmod⟩
  rcases Nat.lt_or_ge 1 n with hlt | hle
  · exact hbot (hI.1 (Or.inr (Or.inr (Or.inl ⟨n, hlt, hWU⟩))))
  · obtain rfl : n = 1 := le_antisymm hle hn1
    by_cases hC : fixV L ⊓ commV L = ⊥
    · exact hbot hC
    ·
      have hC2 : Nat.card ↥(fixV L ⊓ commV L) = 2 := by
        have h1 : 1 < Nat.card ↥(fixV L ⊓ commV L) := (Subgroup.one_lt_card_iff_ne_bot _).2 hC
        have h2 := hI.2 hWU
        omega
      obtain ⟨K, _, _, hK, π, hπ⟩ := hm
      have hK2 : Nat.card K = 2 := by rw [hK, pow_one]
      have hsec := card_eq_of_realizesVia_nat hπ
      rw [Subgroup.card_top, Subgroup.card_bot, mul_one] at hsec
      have h8 : Nat.card (Fin 3 → K) = 8 := by
        rw [Nat.card_fun, hK2]
        simp
      have hV : Nat.card V = 2 ^ 4 := by rw [h.card_eq, hC2, hsec, h8]; norm_num
      have hmod := hWU
      rw [h.fixV_inf, h.top] at hmod
      let e := MulEquiv.ofBijective π ⟨hπ.injective_of_faithful (FFModel.nat_faithful _), hπ.1⟩
      exact Concl328.c2b
        ⟨⟨h.equivL.trans (e.symm.trans (statedSLEquivZModTwo hK2))⟩, hV, hmod⟩

theorem concl_case3 {T : Subgroup (MulAut V)} {B : Subgroup (MulAut (SecV L))}
    (hB : IsFFStarOffender (secG L S) B) (hc : B42Case3 (secG L S) (secL L)) :
    Concl328 L T := by
  obtain ⟨⟨n, hn, hn1⟩, -⟩ := hc
  have hn0 : 1 ≤ n := B5.one_le_of_binaryNaturalSp4 hn
  rcases Nat.lt_or_ge 1 n with hlt | hle
  · rw [hn1 hlt] at hn
    have hmod := B5.binaryNaturalSp4_of_autSec inf_le_right h.le_stabSub_commV'
      h.le_stabSub_fixV' h.inf_centSec_eq_bot hn
    rw [h.fixV_inf, h.top] at hmod
    obtain ⟨K, _, _, hK, ⟨e⟩⟩ := BinaryNaturalSp4.exists_equiv hn
    exact Concl328.c3 ⟨n, K, inferInstance, inferInstance, hK, ⟨h.equivL.trans e.symm⟩, hmod⟩
  · obtain rfl : n = 1 := le_antisymm hle hn0
    obtain ⟨halt, ⟨e⟩⟩ := h.symmetric_case hB (by norm_num) (asSp4S6 _ _ _ _ hn)
    have hmod := B5.alternatingNatural_of_autSec inf_le_right h.le_stabSub_commV'
      h.le_stabSub_fixV' h.inf_centSec_eq_bot halt
    rw [h.fixV_inf, h.top] at hmod
    exact Concl328.c6 ⟨⟨h.equivL.trans e⟩, hmod⟩

theorem concl_case4
    {T : Subgroup (MulAut V)} {B : Subgroup (MulAut (SecV L))}
    (hB : IsFFStarOffender (secG L S) B) (hc : B42Case4 (secG L S) (secL L) B) :
    Concl328 L T := by
  obtain ⟨⟨n, hn, -, hn1⟩, -⟩ := hc
  have hn0 : 1 ≤ n := B5.one_le_of_g2Natural hn
  have key : G2NaturalDerived (secL L) ⊤ ⊥ n ∧ ∃ (K : Type) (_ : Field K) (_ : Finite K),
      Nat.card K = 2 ^ n ∧ Nonempty (↥(secL L) ≃* ↥⁅quasithinG2 K, quasithinG2 K⁆) := by
    by_cases hJL : ffJ (secG L S) = secL L
    · rw [hJL] at hn
      have hperf : Group.IsPerfect ↥(secL L) := h.isQuasisimple_secL.1
      have hcs : ⁅secL L, secL L⁆ = secL L := Subgroup.commutator_eq_self
      have hd := B5.g2NaturalDerived_of_g2Natural hn
      rw [hcs] at hd
      obtain ⟨K, _, _, hK, π, hπ⟩ := hn
      obtain ⟨e⟩ := nonempty_mulEquiv_of_realizesVia (zornQ_faithful le_rfl) hπ
      obtain ⟨f⟩ := nonempty_commutator_equiv e
      exact ⟨hd, K, inferInstance, inferInstance, hK, ⟨(MulEquiv.subgroupCongr hcs.symm).trans f⟩⟩
    · obtain rfl : n = 1 := by
        by_contra hne
        exact hJL (hn1 (by omega))
      have hd := B5.g2NaturalDerived_of_g2Natural hn
      obtain ⟨K, _, _, hK, π, hπ⟩ := hn
      have hK2 : Nat.card K = 2 := by rw [hK, pow_one]
      obtain ⟨e⟩ := nonempty_mulEquiv_of_realizesVia (zornQ_faithful le_rfl) hπ
      obtain ⟨f⟩ := nonempty_commutator_equiv e
      have : IsSimpleGroup ↥⁅quasithinG2 K, quasithinG2 K⁆ := isSimpleGroup_g2Two_commutator hK2
      have hL := h.eq_commutator_ffJ hB f.isSimpleGroup
      rw [← hL] at hd
      exact ⟨hd, K, inferInstance, inferInstance, hK, ⟨(MulEquiv.subgroupCongr hL).trans f⟩⟩
  obtain ⟨hd, K, _, _, hK, ⟨e⟩⟩ := key
  have hmod := B5.g2NaturalDerived_of_autSec inf_le_right h.le_stabSub_commV'
    h.le_stabSub_fixV' h.inf_centSec_eq_bot hd
  rw [h.fixV_inf, h.top] at hmod
  exact Concl328.c4 ⟨n, K, inferInstance, inferInstance, hK, ⟨h.equivL.trans e⟩, hmod⟩

theorem concl_case5 (hI16 : AsI16Cover328) {T : Subgroup (MulAut V)}
    {B : Subgroup (MulAut (SecV L))} (hB : IsFFStarOffender (secG L S) B)
    (hc : B42Case5 (secG L S) B) : Concl328 L T := by
  obtain ⟨⟨n, hn57, π, hπ, -⟩, -⟩ := hc
  have h5 : 5 ≤ n := by rcases hn57 with rfl | rfl <;> norm_num
  obtain ⟨halt, ⟨e⟩⟩ := h.symmetric_case hB h5 ⟨π, hπ⟩
  have hWU := B5.alternatingNatural_of_autSec inf_le_right h.le_stabSub_commV'
    h.le_stabSub_fixV' h.inf_centSec_eq_bot halt
  have hC : fixV L ⊓ commV L = ⊥ := by
    rcases hn57 with rfl | rfl
    · exact (hI16 V h.sq L h.irr).1 (Or.inl hWU)
    · exact (hI16 V h.sq L h.irr).1 (Or.inr (Or.inl hWU))
  rw [hC, h.top] at hWU
  rcases hn57 with rfl | rfl
  · exact Concl328.c5a ⟨⟨h.equivL.trans e⟩, hWU⟩
  · exact Concl328.c5b ⟨⟨h.equivL.trans e⟩, hWU⟩

theorem concl_case6 {T : Subgroup (MulAut V)} {B : Subgroup (MulAut (SecV L))}
    (hc : B42Case6 (secG L S) (secL L) B) : Concl328 L T := by
  obtain ⟨-, ⟨π, hπ⟩, -, -, -⟩ := hc
  obtain ⟨e⟩ := nonempty_mulEquiv_of_realizesVia (altDn_faithful_of_five_le (by norm_num)) hπ
  have hmod := B5.alternatingNatural_of_autSec inf_le_right h.le_stabSub_commV'
    h.le_stabSub_fixV' h.inf_centSec_eq_bot ⟨π, hπ⟩
  rw [h.fixV_inf, h.top] at hmod
  exact Concl328.c6 ⟨⟨h.equivL.trans e⟩, hmod⟩

theorem concl_case7 (hI16 : AsI16Cover328) {T : Subgroup (MulAut V)} (hTS : T ≤ S)
    {B : Subgroup (MulAut (SecV L))} (hc : B42Case7 (secG L S) (secL L) B) : Concl328 L T := by
  obtain ⟨hGJ, hJL, ⟨α, π, hπ⟩, hcard, -, -⟩ := hc
  have hLT := h.sup_eq_of_autSec_eq (hGJ.trans hJL) hTS
  obtain ⟨e⟩ := nonempty_mulEquiv_of_realizesVia (a7Four_faithful α) hπ
  have hWU := B5.a7Four_of_autSec inf_le_right h.le_stabSub_commV' h.le_stabSub_fixV'
    h.inf_centSec_eq_bot ⟨α, π, hπ⟩
  have hC := (hI16 V h.sq L h.irr).1
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hWU)))))))
  have h1 : Nat.card ↥(fixV L ⊓ commV L) = 1 := by rw [hC, Subgroup.card_bot]
  have hV : Nat.card V = 2 ^ 4 := by rw [h.card_eq, h1, one_mul, hcard]
  exact Concl328.c7 ⟨⟨(MulEquiv.subgroupCongr hLT).trans (h.equivL.trans e)⟩, hV⟩

theorem concl_case8 (hI16 : AsI16Cover328) {T : Subgroup (MulAut V)}
    {B : Subgroup (MulAut (SecV L))} (hc : B42Case8 (secG L S) (secL L) B) : Concl328 L T := by
  obtain ⟨-, hcard, -, K, hK, hf, Γ₀, hc4, hdet, hhat, hcen, π, hπ, -⟩ := hc
  have hWU := B5.tripleA6Six_of_autSec inf_le_right h.le_stabSub_commV' h.le_stabSub_fixV'
    h.inf_centSec_eq_bot ⟨K, hK, hf, Γ₀, hc4, hdet, hhat, hcen, ⟨π, hπ⟩⟩
  have hC := (hI16 V h.sq L h.irr).1
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hWU)))))))
  have h1 : Nat.card ↥(fixV L ⊓ commV L) = 1 := by rw [hC, Subgroup.card_bot]
  have hV : Nat.card V = 2 ^ 6 := by rw [h.card_eq, h1, one_mul, hcard]
  obtain ⟨e⟩ := nonempty_mulEquiv_of_realizesVia (FFModel.nat_faithful Γ₀) hπ
  obtain ⟨hp, hz, hq⟩ := isHat_parts_of_mulEquiv (h.equivL.trans e) hhat
  exact Concl328.c8 ⟨hp, hz, hq, hV⟩

theorem concl_case9 (hI16 : AsI16Cover328) {T : Subgroup (MulAut V)}
    (hc : B42Case9 (secG L S) (secL L)) : Concl328 L T := by
  obtain ⟨-, n, hn45, hn, -⟩ := hc
  have hWU := B5.binaryNaturalSL_of_autSec inf_le_right h.le_stabSub_commV' h.le_stabSub_fixV'
    h.inf_centSec_eq_bot hn
  have hC : fixV L ⊓ commV L = ⊥ := by
    rcases hn45 with rfl | rfl
    · exact (hI16 V h.sq L h.irr).1 (Or.inr (Or.inr (Or.inr (Or.inl hWU))))
    · exact (hI16 V h.sq L h.irr).1 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hWU)))))
  rw [hC, h.top] at hWU
  have hLT : L ⊔ T = L := sup_eq_left.2 ((eq_top_of_binaryNaturalSL_one hWU).symm ▸ le_top)
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := BinaryNaturalSL.exists_equiv hWU
  have hK2 : Nat.card K = 2 := by rw [hK, pow_one]
  exact Concl328.c9 ⟨n, hn45,
    ⟨(MulEquiv.subgroupCongr hLT).trans (e.symm.trans (statedSLEquivZModTwo hK2))⟩, hWU⟩

theorem concl_case10 {T : Subgroup (MulAut V)} {B : Subgroup (MulAut (SecV L))}
    (hc : B42Case10 (secG L S) (secL L) B) : Concl328 L T := by
  obtain ⟨⟨π, hπ⟩, -⟩ := hc
  have hmod := B5.slExteriorTwo_of_autSec inf_le_right h.le_stabSub_commV'
    h.le_stabSub_fixV' h.inf_centSec_eq_bot ⟨π, hπ⟩
  rw [h.fixV_inf, h.top] at hmod
  have := h.nontrivial_secL
  have hinj := injective_of_statedSL_zmodTwo (K := ZMod 2) (by simp) (by norm_num) hπ.1
  let e := MulEquiv.ofBijective π ⟨hinj, hπ.1⟩
  exact Concl328.c10 ⟨⟨h.equivL.trans (e.symm.trans (statedSLEquivZModTwo (by simp)))⟩, hmod⟩

theorem concl_case11 (hI16 : AsI16Cover328) {T : Subgroup (MulAut V)} (hTS : T ≤ S)
    {B : Subgroup (MulAut (SecV L))} (hc : B42Case11 (secG L S) (secL L) B) : Concl328 L T := by
  obtain ⟨hGJ, hJL, hcard, -, π, hπ, -⟩ := hc
  have hLT := h.sup_eq_of_autSec_eq (hGJ.trans hJL) hTS
  have hWU := B5.slExteriorTwo_of_autSec inf_le_right h.le_stabSub_commV'
    h.le_stabSub_fixV' h.inf_centSec_eq_bot (⟨π, hπ⟩ : SLExteriorTwo (secL L) ⊤ ⊥ 5)
  have hC := (hI16 V h.sq L h.irr).1
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hWU))))))
  have h1 : Nat.card ↥(fixV L ⊓ commV L) = 1 := by rw [hC, Subgroup.card_bot]
  have hV : Nat.card V = 2 ^ 10 := by rw [h.card_eq, h1, one_mul, hcard]
  have := h.nontrivial_secL
  have hinj := injective_of_statedSL_zmodTwo (K := ZMod 2) (by simp) (by norm_num) hπ.1
  let e := MulEquiv.ofBijective π ⟨hinj, hπ.1⟩
  exact Concl328.c11 ⟨⟨(MulEquiv.subgroupCongr hLT).trans
    (h.equivL.trans (e.symm.trans (statedSLEquivZModTwo (by simp))))⟩, hV⟩

theorem concl
    (hB42 : AsB42) (hI16 : AsI16Cover328)
    (hS : IsSylowTwoOf S (Subgroup.normalizer (L : Set (MulAut V))))
    (hFF : IsFFModule (Subgroup.normalizer (L : Set (MulAut V)))) {T : Subgroup (MulAut V)}
    (hTS : T ≤ S) : Concl328 L T := by
  obtain ⟨B, hB, hc⟩ := h.b42 hB42 hS hFF
  rcases hc with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11
  · exact h.concl_case1 h1
  · exact h.concl_case2 hI16 h2
  · exact h.concl_case3 hB h3
  · exact h.concl_case4 hB h4
  · exact h.concl_case5 hI16 hB h5
  · exact h.concl_case6 h6
  · exact h.concl_case7 hI16 hTS h7
  · exact h.concl_case8 hI16 h8
  · exact h.concl_case9 hI16 h9
  · exact h.concl_case10 h10
  · exact h.concl_case11 hI16 hTS h11

end Sec328

end CFSG.Quasithin.H13
