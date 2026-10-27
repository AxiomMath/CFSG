module

public import CFSG.Quasithin.Background.F1Borel
public import CFSG.Quasithin.Background.F1Amalgam

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7

universe u

variable {G : Type u} [Group G]

@[expose] def pStar (Li B : Subgroup G) : Subgroup G := pCoreOf 2 (Li ⊔ B) ⊔ Li

namespace F1

variable {Li Lj L1 L2 S : Subgroup G}

theorem parabolic_le_normalizer (h : Hyp111R Li Lj S) :
    Li ⊔ bigB Li Lj S ≤ Subgroup.normalizer (Li : Set G) :=
  sup_le Subgroup.le_normalizer (bigB_le_normalizer_left h).1

theorem parabolic_eq (Li Lj S : Subgroup G) :
    Li ⊔ bigB Li Lj S = Li ⊔ S ⊔ borelOf Lj S := by
  apply le_antisymm
  · exact sup_le (le_sup_left.trans le_sup_left)
      (sup_le (sup_le ((borelOf_le Li S).trans (le_sup_left.trans le_sup_left)) le_sup_right)
        (le_sup_right.trans le_sup_left))
  · exact sup_le (sup_le le_sup_left (le_sup_right.trans le_sup_right))
      ((le_sup_right.trans le_sup_left).trans le_sup_right)

theorem parabolic_charTwo (h : Hyp111R Li Lj S) : CharTwo (Li ⊔ bigB Li Lj S) := by
  rw [parabolic_eq]
  exact h.hyp.h1.charTwo

variable [Finite G]

theorem bigB_eq_parabolic_inf (h : Hyp111R Li Lj S) :
    bigB Li Lj S =
      (Li ⊔ bigB Li Lj S) ⊓ Subgroup.normalizer ((S ⊓ Li : Subgroup G) : Set G) := by
  have := bigB_eq_inf_normalizer h
  rwa [← parabolic_eq Li Lj S] at this

theorem pCoreOf_parabolic_le_normalizer_sylow (h : Hyp111R Li Lj S) :
    pCoreOf 2 (Li ⊔ bigB Li Lj S) ≤ Subgroup.normalizer ((S ⊓ Li : Subgroup G) : Set G) := by
  have hi := h.hyp.h1
  set P := Li ⊔ bigB Li Lj S with hP
  have hLiP : Li ≤ P := le_sup_left
  have hPLi : P ≤ Subgroup.normalizer (Li : Set G) := parabolic_le_normalizer h
  have hQLi : pCoreOf 2 P ≤ Subgroup.normalizer (Li : Set G) := (pCoreOf_le 2 P).trans hPLi
  have hLiQ : Li ≤ Subgroup.normalizer (pCoreOf 2 P : Set G) :=
    hLiP.trans (le_normalizer_pCoreOf 2 P)
  have hcomm : ⁅pCoreOf 2 P, Li⁆ ≤ S ⊓ Li := by
    refine (commutator_le_inf_of_normalizes hQLi hLiQ).trans ?_
    refine (pCoreOf_inf_le hLiP).trans ?_
    exact isSylowTwoOf_pCoreOf_le hi.sylow
  have key : ∀ q ∈ pCoreOf 2 P, ∀ x ∈ S ⊓ Li, q * x * q⁻¹ ∈ S ⊓ Li := by
    intro q hq x hx
    have hc : q * x * q⁻¹ * x⁻¹ ∈ S ⊓ Li := by
      have : q * x * q⁻¹ * x⁻¹ ∈ ⁅pCoreOf 2 P, Li⁆ := by
        simpa [commutatorElement_def] using Subgroup.commutator_mem_commutator hq hx.2
      exact hcomm this
    have e : q * x * q⁻¹ = (q * x * q⁻¹ * x⁻¹) * x := by group
    rw [e]
    exact (S ⊓ Li).mul_mem hc hx
  intro q hq
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact key q hq x
  · intro hx
    have := key q⁻¹ ((pCoreOf 2 P).inv_mem hq) _ hx
    have e : q⁻¹ * (q * x * q⁻¹) * q⁻¹⁻¹ = x := by group
    rwa [e] at this

theorem pCoreOf_parabolic_le_bigB (h : Hyp111R Li Lj S) :
    pCoreOf 2 (Li ⊔ bigB Li Lj S) ≤ bigB Li Lj S := by
  have h1 : pCoreOf 2 (Li ⊔ bigB Li Lj S) ≤
      (Li ⊔ bigB Li Lj S) ⊓ Subgroup.normalizer ((S ⊓ Li : Subgroup G) : Set G) :=
    le_inf (pCoreOf_le 2 _) (pCoreOf_parabolic_le_normalizer_sylow h)
  exact h1.trans (bigB_eq_parabolic_inf h).ge

theorem pCoreOf_le_pCoreOf_parabolic (h : Hyp111R Li Lj S) :
    pCoreOf 2 Li ≤ pCoreOf 2 (Li ⊔ bigB Li Lj S) :=
  le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 Li).trans le_sup_left)
    (le_normalizer_pCoreOf_of_le_normalizer (parabolic_le_normalizer h)) (pCoreOf_isPGroup 2 Li)

theorem inf_pCoreOf_parabolic_eq (h : Hyp111R Li Lj S) :
    pCoreOf 2 (Li ⊔ bigB Li Lj S) ⊓ Li = pCoreOf 2 Li :=
  le_antisymm (pCoreOf_inf_le le_sup_left)
    (le_inf (pCoreOf_le_pCoreOf_parabolic h) (pCoreOf_le 2 Li))

omit [Finite G] in
theorem pStar_le_parabolic (Li B : Subgroup G) : pStar Li B ≤ Li ⊔ B :=
  sup_le (pCoreOf_le 2 _) le_sup_left

omit [Finite G] in
theorem pStar_le_normalizer (h : Hyp111R Li Lj S) :
    Li ⊔ bigB Li Lj S ≤
      Subgroup.normalizer ((pStar Li (bigB Li Lj S) : Subgroup G) : Set G) :=
  le_normalizer_sup (le_normalizer_pCoreOf 2 _) (parabolic_le_normalizer h)

omit [Finite G] in
theorem pStar_normal (h : Hyp111R Li Lj S) :
    ((pStar Li (bigB Li Lj S)).subgroupOf (Li ⊔ bigB Li Lj S)).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (pStar_le_parabolic _ _)).mpr
    (pStar_le_normalizer h)

theorem pCoreOf_pStar (h : Hyp111R Li Lj S) :
    pCoreOf 2 (pStar Li (bigB Li Lj S)) = pCoreOf 2 (Li ⊔ bigB Li Lj S) := by
  apply le_antisymm
  · exact le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 _).trans (pStar_le_parabolic _ _))
      (le_normalizer_pCoreOf_of_le_normalizer (pStar_le_normalizer h)) (pCoreOf_isPGroup 2 _)
  · exact le_pCoreOf_of_le_normalizer 2 le_sup_left
      ((pStar_le_parabolic _ _).trans (le_normalizer_pCoreOf 2 _)) (pCoreOf_isPGroup 2 _)

omit [Finite G] in
theorem pStar_sup_bigB (Li Lj S : Subgroup G) :
    pStar Li (bigB Li Lj S) ⊔ bigB Li Lj S = Li ⊔ bigB Li Lj S := by
  apply le_antisymm
  · exact sup_le (pStar_le_parabolic _ _) le_sup_right
  · exact sup_le (le_sup_right.trans le_sup_left) le_sup_right

theorem isSylowTwoOf_sup_sup {Q L S : Subgroup G} (hSyl : IsSylowTwoOf (S ⊓ L) L)
    (hQ2 : IsPGroup 2 Q) (hQL : Q ≤ Subgroup.normalizer (L : Set G))
    (hSQ : S ⊓ L ≤ Subgroup.normalizer (Q : Set G)) :
    IsSylowTwoOf (Q ⊔ (S ⊓ L)) (Q ⊔ L) := by
  have hT2 : IsPGroup 2 ↥(Q ⊔ (S ⊓ L)) := by
    rw [sup_comm]
    exact hSyl.2.1.to_sup_of_normal_right' hQ2 hSQ
  have hTP : Q ⊔ (S ⊓ L) ≤ Q ⊔ L := sup_le_sup_left inf_le_right Q
  obtain ⟨T', hT', hTT'⟩ := exists_isSylowTwoOf_ge hTP hT2
  have hQT' : Q ≤ T' := le_sup_left.trans hTT'
  have hle : T' ≤ Q ⊔ (S ⊓ L) := by
    intro t ht
    have htP : t ∈ Q ⊔ L := hT'.1 ht
    obtain ⟨q, hq, l, hl, rfl⟩ := (mem_sup_iff_exists_mul_of_le_normalizer hQL).mp htP
    have hlT' : l ∈ T' := by
      have := T'.mul_mem (T'.inv_mem (hQT' hq)) ht
      simpa using this
    have hSiT' : S ⊓ L ≤ T' ⊓ L :=
      le_inf ((le_sup_right : S ⊓ L ≤ Q ⊔ (S ⊓ L)).trans hTT') inf_le_right
    have hR2 : IsPGroup 2 ↥(T' ⊓ L) := hT'.2.1.to_le inf_le_left
    have hEq : S ⊓ L = T' ⊓ L := eq_of_isSylowTwoOf_le hSyl inf_le_right hR2 hSiT'
    have hlSi : l ∈ S ⊓ L := by rw [hEq]; exact ⟨hlT', hl⟩
    exact (Q ⊔ (S ⊓ L)).mul_mem (Subgroup.mem_sup_left hq) (Subgroup.mem_sup_right hlSi)
  rw [le_antisymm hTT' hle]
  exact hT'

theorem isSylowTwoOf_pCoreOf_sup (h : Hyp111R Li Lj S) :
    IsSylowTwoOf (pCoreOf 2 (Li ⊔ bigB Li Lj S) ⊔ (S ⊓ Li)) (pStar Li (bigB Li Lj S)) :=
  isSylowTwoOf_sup_sup h.hyp.h1.sylow (pCoreOf_isPGroup 2 _)
    ((pCoreOf_le 2 _).trans (parabolic_le_normalizer h))
    ((inf_le_right.trans le_sup_left).trans (le_normalizer_pCoreOf 2 _))

theorem pCoreOf_sup_inf_left (h : Hyp111R Li Lj S) :
    (pCoreOf 2 (Li ⊔ bigB Li Lj S) ⊔ (S ⊓ Li)) ⊓ Li = S ⊓ Li := by
  have hSiQ : S ⊓ Li ≤ Subgroup.normalizer (pCoreOf 2 (Li ⊔ bigB Li Lj S) : Set G) :=
    (inf_le_right.trans le_sup_left).trans (le_normalizer_pCoreOf 2 _)
  apply le_antisymm
  · intro y hy
    obtain ⟨hyT, hyL⟩ := Subgroup.mem_inf.mp hy
    obtain ⟨q, hq, s', hs', rfl⟩ := (mem_sup_iff_exists_mul_of_normalizes hSiQ).mp hyT
    have hqLi : q ∈ Li := by
      have := Li.mul_mem hyL (Li.inv_mem hs'.2)
      simpa using this
    have hq2 : q ∈ pCoreOf 2 Li := by
      rw [← inf_pCoreOf_parabolic_eq h]
      exact ⟨hq, hqLi⟩
    have hqS : q ∈ S ⊓ Li := isSylowTwoOf_pCoreOf_le h.hyp.h1.sylow hq2
    exact (S ⊓ Li).mul_mem hqS hs'
  · exact le_inf le_sup_right inf_le_right

theorem pStar_inf_bigB (h : Hyp111R Li Lj S) :
    pStar Li (bigB Li Lj S) ⊓ bigB Li Lj S = pCoreOf 2 (Li ⊔ bigB Li Lj S) ⊔ borelOf Li S := by
  have hQLi : pCoreOf 2 (Li ⊔ bigB Li Lj S) ≤ Subgroup.normalizer (Li : Set G) :=
    (pCoreOf_le 2 _).trans (parabolic_le_normalizer h)
  apply le_antisymm
  · intro x hx
    obtain ⟨hxP, hxB⟩ := Subgroup.mem_inf.mp hx
    have hxP' : x ∈ pCoreOf 2 (Li ⊔ bigB Li Lj S) ⊔ Li := hxP
    obtain ⟨q, hq, l, hl, rfl⟩ := (mem_sup_iff_exists_mul_of_le_normalizer hQLi).mp hxP'
    have hqB : q ∈ bigB Li Lj S := pCoreOf_parabolic_le_bigB h hq
    have hlB : l ∈ bigB Li Lj S := by
      have := (bigB Li Lj S).mul_mem ((bigB Li Lj S).inv_mem hqB) hxB
      simpa using this
    have hlBi : l ∈ borelOf Li S := by
      rw [← inf_bigB_eq_borelOf h]
      exact ⟨hl, hlB⟩
    exact (pCoreOf 2 (Li ⊔ bigB Li Lj S) ⊔ borelOf Li S).mul_mem (Subgroup.mem_sup_left hq)
      (Subgroup.mem_sup_right hlBi)
  · exact le_inf (sup_le le_sup_left ((borelOf_le Li S).trans le_sup_right))
      (sup_le (pCoreOf_parabolic_le_bigB h) (le_sup_left.trans le_sup_left))

theorem pStar_inf_normalizer (h : Hyp111R Li Lj S) :
    pStar Li (bigB Li Lj S) ⊓
        Subgroup.normalizer
          ((pCoreOf 2 (Li ⊔ bigB Li Lj S) ⊔ (S ⊓ Li) : Subgroup G) : Set G) =
      pCoreOf 2 (Li ⊔ bigB Li Lj S) ⊔ borelOf Li S := by
  have hQLi : pCoreOf 2 (Li ⊔ bigB Li Lj S) ≤ Subgroup.normalizer (Li : Set G) :=
    (pCoreOf_le 2 _).trans (parabolic_le_normalizer h)
  apply le_antisymm
  · intro x hx
    obtain ⟨hxP, hxN⟩ := Subgroup.mem_inf.mp hx
    have hxP' : x ∈ pCoreOf 2 (Li ⊔ bigB Li Lj S) ⊔ Li := hxP
    obtain ⟨q, hq, l, hl, rfl⟩ := (mem_sup_iff_exists_mul_of_le_normalizer hQLi).mp hxP'
    have hqT : q ∈ Subgroup.normalizer
        ((pCoreOf 2 (Li ⊔ bigB Li Lj S) ⊔ (S ⊓ Li) : Subgroup G) : Set G) :=
      Subgroup.le_normalizer (Subgroup.mem_sup_left hq)
    have hlN := (Subgroup.normalizer
        ((pCoreOf 2 (Li ⊔ bigB Li Lj S) ⊔ (S ⊓ Li) : Subgroup G) : Set G)).mul_mem
      ((Subgroup.normalizer _).inv_mem hqT) hxN
    have hlN' : l ∈ Subgroup.normalizer
        ((pCoreOf 2 (Li ⊔ bigB Li Lj S) ⊔ (S ⊓ Li) : Subgroup G) : Set G) := by simpa using hlN
    have hlN2 := mem_normalizer_inf hlN' (Subgroup.le_normalizer hl)
    rw [pCoreOf_sup_inf_left h] at hlN2
    exact (pCoreOf 2 (Li ⊔ bigB Li Lj S) ⊔ borelOf Li S).mul_mem (Subgroup.mem_sup_left hq)
      (Subgroup.mem_sup_right ⟨hl, hlN2⟩)
  · refine le_inf (sup_le le_sup_left ((borelOf_le Li S).trans le_sup_right)) ?_
    refine sup_le ((le_sup_left : pCoreOf 2 (Li ⊔ bigB Li Lj S) ≤ _).trans Subgroup.le_normalizer)
      ?_
    exact le_normalizer_sup (((borelOf_le Li S).trans le_sup_left).trans (le_normalizer_pCoreOf 2 _))
      (borelOf_le_normalizer Li S)

theorem isRankOneListed_pStar (h : Hyp111R Li Lj S) (hL : IsRankOneListed (oTwoQuot ↥Li)) :
    IsRankOneListed (oTwoQuot ↥(pStar Li (bigB Li Lj S))) := by
  have hLiPs : Li ≤ pStar Li (bigB Li Lj S) := le_sup_right
  let φ : ↥Li →* ↥(pStar Li (bigB Li Lj S)) ⧸ pCore 2 ↥(pStar Li (bigB Li Lj S)) :=
    (QuotientGroup.mk' (pCore 2 ↥(pStar Li (bigB Li Lj S)))).comp (Subgroup.inclusion hLiPs)
  have hQLi : pCoreOf 2 (Li ⊔ bigB Li Lj S) ≤ Subgroup.normalizer (Li : Set G) :=
    (pCoreOf_le 2 _).trans (parabolic_le_normalizer h)
  have hsurj : Function.Surjective φ := by
    intro z
    induction z using QuotientGroup.induction_on with
    | H a =>
      obtain ⟨x, hx⟩ := a
      have hx' : x ∈ pCoreOf 2 (Li ⊔ bigB Li Lj S) ⊔ Li := hx
      obtain ⟨q, hq, l, hl, rfl⟩ := (mem_sup_iff_exists_mul_of_le_normalizer hQLi).mp hx'
      refine ⟨⟨l, hl⟩, ?_⟩
      have hqPs : q ∈ pCoreOf 2 (pStar Li (bigB Li Lj S)) := by
        rw [pCoreOf_pStar h]; exact hq
      have e : (⟨q * l, hx⟩ : ↥(pStar Li (bigB Li Lj S))) =
          ⟨q, Subgroup.mem_sup_left hq⟩ * ⟨l, hLiPs hl⟩ := rfl
      show QuotientGroup.mk (⟨l, hLiPs hl⟩ : ↥(pStar Li (bigB Li Lj S))) =
        QuotientGroup.mk ⟨q * l, hx⟩
      have hq1 : (QuotientGroup.mk (⟨q, Subgroup.mem_sup_left hq⟩ : ↥(pStar Li (bigB Li Lj S))) :
          ↥(pStar Li (bigB Li Lj S)) ⧸ pCore 2 ↥(pStar Li (bigB Li Lj S))) = 1 :=
        (QuotientGroup.eq_one_iff _).mpr
          ((mem_pCore_iff_coe (⟨q, Subgroup.mem_sup_left hq⟩ : ↥(pStar Li (bigB Li Lj S)))).mpr hqPs)
      rw [e, QuotientGroup.mk_mul, hq1, one_mul]
  have hker : pCore 2 ↥Li = φ.ker := by
    ext l
    rw [MonoidHom.mem_ker, mem_pCore_iff_coe]
    show (l : G) ∈ pCoreOf 2 Li ↔ QuotientGroup.mk (⟨l, hLiPs l.2⟩ : ↥(pStar Li (bigB Li Lj S))) = 1
    rw [QuotientGroup.eq_one_iff, mem_pCore_iff_coe]
    show (l : G) ∈ pCoreOf 2 Li ↔ (l : G) ∈ pCoreOf 2 (pStar Li (bigB Li Lj S))
    rw [pCoreOf_pStar h]
    constructor
    · intro hl
      exact pCoreOf_le_pCoreOf_parabolic h hl
    · intro hl
      rw [← inf_pCoreOf_parabolic_eq h]
      exact ⟨hl, l.2⟩
  let e : oTwoQuot ↥Li ≃* oTwoQuot ↥(pStar Li (bigB Li Lj S)) :=
    (QuotientGroup.quotientMulEquivOfEq hker).trans
      (QuotientGroup.quotientKerEquivOfSurjective φ hsurj)
  exact IsRankOneListed.of_mulEquiv e hL

theorem hypAAt_parabolic (h : Hyp111R Li Lj S) :
    HypAAt (Li ⊔ bigB Li Lj S) (bigB Li Lj S) (pStar Li (bigB Li Lj S)) where
  le := pStar_le_parabolic _ _
  normal := pStar_normal h
  pCore_eq := pCoreOf_pStar h
  sup_eq := pStar_sup_bigB Li Lj S
  charTwo := parabolic_charTwo h
  sylow :=
    ⟨pCoreOf 2 (Li ⊔ bigB Li Lj S) ⊔ (S ⊓ Li), isSylowTwoOf_pCoreOf_sup h,
      sup_le (pCoreOf_parabolic_le_bigB h) (inf_le_left.trans le_sup_right),
      (pStar_inf_bigB h).trans (pStar_inf_normalizer h).symm⟩
  listed := isRankOneListed_pStar h h.hyp.h1.listed

omit [Finite G] in
theorem parabolic_sup_parabolic (L1 L2 S : Subgroup G) :
    (L1 ⊔ bigB L1 L2 S) ⊔ (L2 ⊔ bigB L1 L2 S) = L1 ⊔ L2 ⊔ S := by
  apply le_antisymm
  · refine sup_le (sup_le (le_sup_left.trans le_sup_left) ?_) (sup_le (le_sup_right.trans le_sup_left) ?_)
    · exact sup_le (sup_le ((borelOf_le L1 S).trans (le_sup_left.trans le_sup_left))
        ((borelOf_le L2 S).trans (le_sup_right.trans le_sup_left))) le_sup_right
    · exact sup_le (sup_le ((borelOf_le L1 S).trans (le_sup_left.trans le_sup_left))
        ((borelOf_le L2 S).trans (le_sup_right.trans le_sup_left))) le_sup_right
  · exact sup_le (sup_le (le_sup_left.trans le_sup_left) (le_sup_left.trans le_sup_right))
      (le_sup_right.trans (le_sup_right.trans le_sup_left))

theorem coreIn_bigB_eq_bot (h : Hyp111R L1 L2 S) :
    coreIn (bigB L1 L2 S) ((L1 ⊔ bigB L1 L2 S) ⊔ (L2 ⊔ bigB L1 L2 S)) = ⊥ := by
  set P1 := L1 ⊔ bigB L1 L2 S with hP1
  set G0 := P1 ⊔ (L2 ⊔ bigB L1 L2 S) with hG0
  set Y := coreIn (bigB L1 L2 S) G0 with hY
  have hYG0 : G0 ≤ Subgroup.normalizer (Y : Set G) := le_normalizer_coreIn _ _
  have hYB : Y ≤ bigB L1 L2 S := coreIn_le_right _ _
  have hYP1 : Y ≤ P1 := hYB.trans le_sup_right
  have hP1G0 : P1 ≤ G0 := le_sup_left
  have hO2 : pCoreOf 2 Y = ⊥ := by
    have h1 : pCoreOf 2 Y ≤ pCoreOf 2 G0 :=
      le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 Y).trans (coreIn_le_left _ _))
        (le_normalizer_pCoreOf_of_le_normalizer hYG0) (pCoreOf_isPGroup 2 Y)
    have e : G0 = L1 ⊔ L2 ⊔ S := parabolic_sup_parabolic L1 L2 S
    rw [e, h.hyp.o2] at h1
    exact le_bot_iff.mp h1
  have hinf : pCoreOf 2 P1 ⊓ Y ≤ ⊥ := by
    have := pCoreOf_inf_le hYP1
    rwa [hO2] at this
  have hcomm : ⁅Y, pCoreOf 2 P1⁆ = ⊥ := by
    refine le_bot_iff.mp (le_trans (commutator_le_inf_of_normalizes ?_ ?_)
      (by rw [inf_comm]; exact hinf))
    · exact hYP1.trans (le_normalizer_pCoreOf 2 P1)
    · exact ((pCoreOf_le 2 P1).trans hP1G0).trans hYG0
  have hcent : Y ≤ Subgroup.centralizer (pCoreOf 2 P1 : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  have hYQ : Y ≤ pCoreOf 2 P1 := fun x hx => parabolic_charTwo h ⟨hYP1 hx, hcent hx⟩
  exact le_bot_iff.mp ((le_inf hYQ le_rfl).trans hinf)

theorem isWeakBNPair (h : Hyp111R L1 L2 S) :
    IsWeakBNPair (L1 ⊔ bigB L1 L2 S) (L2 ⊔ bigB L1 L2 S) := by
  have hinf := parabolic_inf_parabolic h
  refine ⟨inferInstance, inferInstance, ?_, ?_, ?_⟩
  · rw [hinf]
    exact coreIn_bigB_eq_bot h
  · refine ⟨pStar L1 (bigB L1 L2 S), ?_⟩
    rw [hinf]
    exact hypAAt_parabolic h
  · refine ⟨pStar L2 (bigB L1 L2 S), ?_⟩
    rw [hinf]
    have := hypAAt_parabolic h.symm
    rwa [bigB_comm] at this

end F1

theorem prop_F19 {L1 L2 S : Subgroup G} [Finite G] (h : Hyp111R L1 L2 S) :
    (L1 ⊔ bigB L1 L2 S) ⊓ (L2 ⊔ bigB L1 L2 S) = bigB L1 L2 S ∧
    IsWeakBNPair (L1 ⊔ bigB L1 L2 S) (L2 ⊔ bigB L1 L2 S) ∧
    coreIn (bigB L1 L2 S) (L1 ⊔ L2 ⊔ S) = ⊥ ∧
    ∃ c : (RankTwoAmalgam.ofSubgroups (L1 ⊔ bigB L1 L2 S) (L2 ⊔ bigB L1 L2 S)).Completion
        ↥(L1 ⊔ L2 ⊔ S), c.IsFaithful := by
  refine ⟨F1.parabolic_inf_parabolic h, F1.isWeakBNPair h, ?_, ?_⟩
  · rw [← F1.parabolic_sup_parabolic L1 L2 S]
    exact F1.coreIn_bigB_eq_bot h
  · exact ⟨RankTwoAmalgam.inclusionCompletion _ _ _ (F1.parabolic_sup_parabolic L1 L2 S),
      RankTwoAmalgam.inclusionCompletion_isFaithful _ _ _ _⟩

end CFSG.Quasithin
