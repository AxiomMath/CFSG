module

public import CFSG.RankThree.GF2n.Stroth78.Sec2FourIDim
public import CFSG.RankThree.GF2n.Stroth78.Sec2M3
public import CFSG.LargeExtraspecial.OrthoF2Basic
public import CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin
public import CFSG.RankThree.GF2n.Stroth78.Sec2Eighteen
public import CFSG.RankThree.GF2n.Stroth78.Sec2FourIFamily

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

public section

namespace CFSG.RankThree.GF2n.Stroth78

open CFSG CFSG.Open CFSG.RankThree.GF2n.Tim79a CFSG.LargeExtraspecial.Timmesfeld
open CFSG.RankThree.OrthogonalInvolutions
open Module
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G} {E F : Subgroup G}

theorem centerIn_QaOf_inf_Q_le_sup_zpowers_ZQ (S : Setting z E F) {a : G}
    (haQ : a ∈ Q z) (hzaZ : z ∉ centerIn (QaOf a)) :
    Q z ⊓ centerIn (QaOf a) ≤ Subgroup.zpowers a ⊔ ZQ z := by
  intro b hb
  by_contra hbnot
  obtain ⟨hbQ, hbZ⟩ := Subgroup.mem_inf.mp hb
  obtain ⟨hbQa, hbCent⟩ := Subgroup.mem_inf.mp hbZ
  obtain ⟨c, -, hcCa, hcb⟩ :=
    exists_conj_eq_mul_z_of_mem_Q S haQ hbQ hbnot
  have hcbA : c * b * c⁻¹ ∈ centerIn (QaOf a) :=
    conj_mem_centerIn_QaOf S hcCa hbZ
  have hbz : b * z ∈ centerIn (QaOf a) := by
    rw [← hcb]
    exact hcbA
  have hzA : z ∈ centerIn (QaOf a) := by
    have h : b⁻¹ * (b * z) ∈ centerIn (QaOf a) :=
      (centerIn (QaOf a)).mul_mem ((centerIn (QaOf a)).inv_mem hbZ) hbz
    simpa using h
  exact hzaZ hzA

theorem sq_eq_one_of_mem_centerIn_QaOf (S : Setting z E F) {a s : G}
    (hconj : IsConj z a) (hs : s ∈ centerIn (QaOf a)) : s ^ 2 = 1 :=
  (isElemAbelian_centerIn_QaOf S hconj).2 s hs

theorem commutator_zpowers_CQ_le_sup_zpowers_ZQ (S : Setting z E F) {a s : G}
    (haQ : a ∈ Q z) (hconj : IsConj z a)
    (hzaZ : z ∉ centerIn (QaOf a))
    (hsZ : s ∈ centerIn (QaOf a)) (hsH : s ∈ H z) :
    ⁅Subgroup.zpowers s,
      (Q z ⊓ Subgroup.centralizer ({a} : Set G) : Subgroup G)⁆
      ≤ Subgroup.zpowers a ⊔ ZQ z := by
  refine (Subgroup.commutator_mono ?_ le_rfl).trans
    ((commutator_centerIn_H_CQ_le S haQ hconj).trans ?_)
  · exact Subgroup.zpowers_le.mpr (Subgroup.mem_inf.mpr ⟨hsZ, hsH⟩)
  · exact centerIn_QaOf_inf_Q_le_sup_zpowers_ZQ S haQ hzaZ

theorem commutator_CQ_zpowers_le_sup_zpowers_ZQ (S : Setting z E F) {a s : G}
    (haQ : a ∈ Q z) (hconj : IsConj z a)
    (hzaZ : z ∉ centerIn (QaOf a))
    (hsZ : s ∈ centerIn (QaOf a)) (hsH : s ∈ H z) :
    ⁅(Q z ⊓ Subgroup.centralizer ({a} : Set G) : Subgroup G),
      Subgroup.zpowers s⁆ ≤ Subgroup.zpowers a ⊔ ZQ z := by
  rw [Subgroup.commutator_comm]
  exact commutator_zpowers_CQ_le_sup_zpowers_ZQ S haQ hconj hzaZ hsZ hsH

theorem mkQbar_mem_span_of_mem_sup_zpowers_ZQ (S : Setting z E F) {a q : G}
    (haQ : a ∈ Q z) (hconj : IsConj z a)
    (hqB : q ∈ Subgroup.zpowers a ⊔ ZQ z) (hqQ : q ∈ Q z) :
    Additive.ofMul (mkQbar S ⟨q, hqQ⟩) ∈
      Submodule.span (ZMod 2) {Additive.ofMul (mkQbar S ⟨a, haQ⟩)} := by
  have hB : Subgroup.zpowers a ⊔ ZQ z =
      Subgroup.closure (({a} : Set G) ∪ (ZQ z : Set G)) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.closure_union, Subgroup.closure_eq]
  have hBQ : Subgroup.closure (({a} : Set G) ∪ (ZQ z : Set G)) ≤ Q z := by
    rw [Subgroup.closure_le]
    rintro x (rfl | hxZ)
    · exact haQ
    · exact (inf_le_left : ZQ z ≤ Q z) hxZ
  have hP : ∀ x ∈ Subgroup.closure (({a} : Set G) ∪ (ZQ z : Set G)),
      ∀ hxQ : x ∈ Q z,
        Additive.ofMul (mkQbar S ⟨x, hxQ⟩) ∈
          Submodule.span (ZMod 2) {Additive.ofMul (mkQbar S ⟨a, haQ⟩)} := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
        intro hyQ
        rcases hy with hy | hy
        · rw [Set.mem_singleton_iff] at hy
          subst y
          have hclass : (mkQbar S ⟨a, hyQ⟩ : QbarOf S) = mkQbar S ⟨a, haQ⟩ := by
            congr 1
          rw [hclass]
          exact Submodule.mem_span_singleton_self _
        · have hy1 : (mkQbar S ⟨y, hyQ⟩ : QbarOf S) = 1 := by
            rw [← MonoidHom.mem_ker]
            rw [show (mkQbar S).ker = (ZQ z).subgroupOf (Q z) from
              QuotientGroup.ker_mk' _]
            exact Subgroup.mem_subgroupOf.mpr hy
          rw [hy1]
          exact Submodule.zero_mem _
    | one =>
        intro _
        exact Submodule.zero_mem _
    | mul y w hy hw ihy ihw =>
        intro hywQ
        have hyQ : y ∈ Q z := hBQ hy
        have hwQ : w ∈ Q z := hBQ hw
        have hmul : (mkQbar S ⟨y * w, hywQ⟩ : QbarOf S) =
            mkQbar S ⟨y, hyQ⟩ * mkQbar S ⟨w, hwQ⟩ := by
          rw [← map_mul]
          congr 1
        rw [hmul]
        change Additive.ofMul (mkQbar S ⟨y, hyQ⟩) +
          Additive.ofMul (mkQbar S ⟨w, hwQ⟩) ∈ _
        exact Submodule.add_mem _ (ihy hyQ) (ihw hwQ)
    | inv y hy ihy =>
        intro hyQ'
        have hyQ : y ∈ Q z := hBQ hy
        have hinv : (mkQbar S ⟨y⁻¹, hyQ'⟩ : QbarOf S) =
            (mkQbar S ⟨y, hyQ⟩)⁻¹ := by
          rw [← map_inv]
          congr 1
        rw [hinv]
        change -Additive.ofMul (mkQbar S ⟨y, hyQ⟩) ∈ _
        exact Submodule.neg_mem _ (ihy hyQ)
  exact hP q (hB ▸ hqB) hqQ

theorem QaInterImage_sup_zpowers_ZQ_le_span (S : Setting z E F) {a : G}
    (haQ : a ∈ Q z) (hconj : IsConj z a) :
    QaInterImage S (Subgroup.zpowers a ⊔ ZQ z) ≤
      Submodule.span (ZMod 2) {Additive.ofMul (mkQbar S ⟨a, haQ⟩)} := by
  intro v hv
  rw [mem_QaInterImage_iff] at hv
  obtain ⟨q, hqA, hqv⟩ := hv
  have hv' : v = Additive.ofMul (mkQbar S q) := (congrArg Additive.ofMul hqv).symm
  rw [hv']
  exact mkQbar_mem_span_of_mem_sup_zpowers_ZQ S haQ hconj hqA q.2

theorem commutator_mem_Q_of_mem_H {s q : G} (hsH : s ∈ H z)
    (hq : q ∈ Q z) : ⁅q, s⁆ ∈ Q z := by
  have hconj : s * q⁻¹ * s⁻¹ ∈ Q z :=
    fStar_normal (M := H z) hsH ((Q z).inv_mem hq)
  have h : ⁅q, s⁆ = q * (s * q⁻¹ * s⁻¹) := by
    rw [commutatorElement_def]
    group
  rw [h]
  exact (Q z).mul_mem hq hconj

theorem conj_sq_mem_ZQ (S : Setting z E F) {s q : G} (hsH : s ∈ H z) (hq : q ∈ Q z) :
    s * q ^ 2 * s⁻¹ ∈ ZQ z := by
  have hq2Z : q ^ 2 ∈ ZQ z := sq_mem_ZQ S hq
  have hq2Q : q ^ 2 ∈ Q z := (inf_le_left : ZQ z ≤ Q z) hq2Z
  have hq2Cent : q ^ 2 ∈ Subgroup.centralizer (Q z : Set G) :=
    (inf_le_right : ZQ z ≤ Subgroup.centralizer (Q z : Set G)) hq2Z
  refine Subgroup.mem_inf.mpr ⟨fStar_normal (M := H z) hsH hq2Q, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have hx' : s⁻¹ * x * s ∈ Q z := by
    change s⁻¹ * x * s ∈ fStar (H z)
    simpa using fStar_normal (M := H z) (Subgroup.inv_mem (H z) hsH) hx
  have hcomm : (s⁻¹ * x * s) * q ^ 2 = q ^ 2 * (s⁻¹ * x * s) :=
    Subgroup.mem_centralizer_iff.mp hq2Cent _ hx'
  calc
    x * (s * q ^ 2 * s⁻¹) = s * ((s⁻¹ * x * s) * q ^ 2) * s⁻¹ := by group
    _ = s * (q ^ 2 * (s⁻¹ * x * s)) * s⁻¹ := by rw [hcomm]
    _ = (s * q ^ 2 * s⁻¹) * x := by group

theorem mkQbar_commutator_eq_mul (S : Setting z E F) {s q : G}
    (hsH : s ∈ H z) (hq : q ∈ Q z) :
    (mkQbar S ⟨⁅q, s⁆, commutator_mem_Q_of_mem_H hsH hq⟩ : QbarOf S) =
      (mkQbar S ⟨q, hq⟩) *
        (mkQbar S (conjAutQ S ⟨s, hsH⟩ ⟨q, hq⟩)) := by
  have hq2Z : q ^ 2 ∈ ZQ z := sq_mem_ZQ S hq
  have hconjZ : s * q ^ 2 * s⁻¹ ∈ ZQ z := conj_sq_mem_ZQ S hsH hq
  have hconjQ : s * q * s⁻¹ ∈ Q z := fStar_normal (M := H z) hsH hq
  have hprodQ : q * (s * q * s⁻¹) ∈ Q z := (Q z).mul_mem hq hconjQ
  have hcommq : q * (s * q ^ 2 * s⁻¹) = (s * q ^ 2 * s⁻¹) * q :=
    Subgroup.mem_centralizer_iff.mp ((Subgroup.mem_inf.mp hconjZ).2) q hq
  have hsame : (mkQbar S ⟨q * (s * q * s⁻¹), hprodQ⟩ : QbarOf S) =
      (mkQbar S ⟨⁅q, s⁆, commutator_mem_Q_of_mem_H hsH hq⟩ : QbarOf S) := by
    simp only [mkQbar, QuotientGroup.mk'_apply]
    rw [QuotientGroup.eq_iff_div_mem]
    have hdiv : ((⟨q * (s * q * s⁻¹), hprodQ⟩ : ↥(Q z)) /
        ⟨⁅q, s⁆, commutator_mem_Q_of_mem_H hsH hq⟩ : ↥(Q z)) =
        ⟨s * q ^ 2 * s⁻¹, (inf_le_left : ZQ z ≤ Q z) hconjZ⟩ := by
      apply Subtype.ext
      simp only [Subgroup.coe_div, Subgroup.coe_mul, Subgroup.coe_mk, Subgroup.coe_inv,
        div_eq_mul_inv]
      rw [commutatorElement_def]
      calc
        q * (s * q * s⁻¹) * (q * s * q⁻¹ * s⁻¹)⁻¹ =
            q * (s * q ^ 2 * s⁻¹) * q⁻¹ := by
          rw [pow_two]
          group
        _ = (s * q ^ 2 * s⁻¹) * q * q⁻¹ := by rw [hcommq]
        _ = s * q ^ 2 * s⁻¹ := by group
    rw [hdiv]
    exact Subgroup.mem_subgroupOf.mpr hconjZ
  rw [← hsame, ← map_mul (mkQbar S) (⟨q, hq⟩ : ↥(Q z))
    (conjAutQ S ⟨s, hsH⟩ ⟨q, hq⟩)]
  congr 1
  apply Subtype.ext
  rw [Subgroup.coe_mul, conjAutQ_apply]

theorem additive_commutator_eq_sub (S : Setting z E F) {s q : G}
    (hsH : s ∈ H z) (hq : q ∈ Q z) :
    Additive.ofMul (mkQbar S ⟨⁅q, s⁆, commutator_mem_Q_of_mem_H hsH hq⟩) =
      conjQbar S ⟨s, hsH⟩ (Additive.ofMul (mkQbar S ⟨q, hq⟩)) -
        Additive.ofMul (mkQbar S ⟨q, hq⟩) := by
  calc
    Additive.ofMul (mkQbar S ⟨⁅q, s⁆, commutator_mem_Q_of_mem_H hsH hq⟩) =
        Additive.ofMul ((mkQbar S ⟨q, hq⟩) *
          mkQbar S (conjAutQ S ⟨s, hsH⟩ ⟨q, hq⟩)) := by
      rw [mkQbar_commutator_eq_mul S hsH hq]
    _ = Additive.ofMul (mkQbar S ⟨q, hq⟩) +
          Additive.ofMul (mkQbar S (conjAutQ S ⟨s, hsH⟩ ⟨q, hq⟩)) := rfl
    _ = Additive.ofMul (mkQbar S ⟨q, hq⟩) +
          conjQbar S ⟨s, hsH⟩ (Additive.ofMul (mkQbar S ⟨q, hq⟩)) := by
      congr 1
      simpa only [mkQbar, QuotientGroup.mk'_apply] using
        (conjQbar_apply_mk S ⟨s, hsH⟩ ⟨q, hq⟩).symm
    _ = conjQbar S ⟨s, hsH⟩ (Additive.ofMul (mkQbar S ⟨q, hq⟩)) -
          Additive.ofMul (mkQbar S ⟨q, hq⟩) := by
      rw [CFSG.RankThree.OrthogonalInvolutions.sub_eq_add_vec (ZMod 2), add_comm]

theorem mem_commSpace_conjQbar_iff (S : Setting z E F) {s : G} (hsH : s ∈ H z)
    {v : Additive (QbarOf S)} :
    v ∈ commSpace (conjQbar S ⟨s, hsH⟩) ↔
      ∃ q : ↥(Q z),
        v = Additive.ofMul (mkQbar S ⟨⁅(q : G), s⁆,
          commutator_mem_Q_of_mem_H hsH q.2⟩) := by
  constructor
  · intro hv
    rw [mem_commSpace] at hv
    obtain ⟨u, hu⟩ := hv
    obtain ⟨q, hq⟩ := QuotientGroup.mk'_surjective ((ZQ z).subgroupOf (Q z))
      (Additive.toMul u)
    have hu' : u = Additive.ofMul (mkQbar S q) := by
      have h := congrArg Additive.ofMul hq.symm
      simpa [mkQbar] using h
    refine ⟨q, ?_⟩
    rw [← hu, hu']
    exact (additive_commutator_eq_sub S hsH q.2).symm
  · rintro ⟨q, rfl⟩
    rw [mem_commSpace]
    exact ⟨Additive.ofMul (mkQbar S q),
      (additive_commutator_eq_sub S hsH q.2).symm⟩

theorem map_sub_QaInterImage_CQ_le_span (S : Setting z E F) {a s : G}
    (haQ : a ∈ Q z) (hconj : IsConj z a)
    (hzaZ : z ∉ centerIn (QaOf a))
    (hsZ : s ∈ centerIn (QaOf a)) (hsH : s ∈ H z) :
    Submodule.map
        ((conjQbar S ⟨s, hsH⟩ :
          Additive (QbarOf S) →ₗ[ZMod 2] Additive (QbarOf S)) - 1)
        (QaInterImage S (Q z ⊓ Subgroup.centralizer ({a} : Set G))) ≤
      Submodule.span (ZMod 2) {Additive.ofMul (mkQbar S ⟨a, haQ⟩)} := by
  intro w hw
  rw [Submodule.mem_map] at hw
  obtain ⟨v, hv, rfl⟩ := hw
  rw [mem_QaInterImage_iff] at hv
  obtain ⟨q, hqA, hqv⟩ := hv
  have hv' : v = Additive.ofMul (mkQbar S q) := (congrArg Additive.ofMul hqv).symm
  rw [hv']
  change conjQbar S ⟨s, hsH⟩ (Additive.ofMul (mkQbar S q)) -
      Additive.ofMul (mkQbar S q) ∈
    Submodule.span (ZMod 2) {Additive.ofMul (mkQbar S ⟨a, haQ⟩)}
  rw [← additive_commutator_eq_sub S hsH q.2]
  have hqC : (q : G) ∈ Q z ⊓ Subgroup.centralizer ({a} : Set G) := hqA
  have hcommSup : ⁅(q : G), s⁆ ∈ Subgroup.zpowers a ⊔ ZQ z := by
    have hmem : ⁅(q : G), s⁆ ∈
        ⁅(Q z ⊓ Subgroup.centralizer ({a} : Set G) : Subgroup G), Subgroup.zpowers s⁆ :=
      Subgroup.commutator_mem_commutator hqC (Subgroup.mem_zpowers s)
    exact commutator_CQ_zpowers_le_sup_zpowers_ZQ S haQ hconj hzaZ hsZ hsH hmem
  have hmemImg : Additive.ofMul (mkQbar S ⟨⁅(q : G), s⁆,
      commutator_mem_Q_of_mem_H hsH q.2⟩) ∈
      QaInterImage S (Subgroup.zpowers a ⊔ ZQ z) := by
    rw [mem_QaInterImage_iff]
    exact ⟨⟨⁅(q : G), s⁆, commutator_mem_Q_of_mem_H hsH q.2⟩, hcommSup, rfl⟩
  exact QaInterImage_sup_zpowers_ZQ_le_span S haQ hconj hmemImg

theorem QaInterImage_CQ_eq_orthogonal (S : Setting z E F) {a : G} (haQ : a ∈ Q z) :
    QaInterImage S (Q z ⊓ Subgroup.centralizer ({a} : Set G)) =
      LinearMap.BilinForm.orthogonal (qS S).polarBilin
        (Submodule.span (ZMod 2) {Additive.ofMul (mkQbar S ⟨a, haQ⟩)}) := by
  letI : Module (ZMod 2) (Additive (Abelianization F)) := modAbF S
  ext v
  constructor
  · intro hv
    rw [mem_QaInterImage_iff] at hv
    obtain ⟨q, hqC, hqv⟩ := hv
    have hv' : v = Additive.ofMul (mkQbar S q) := (congrArg Additive.ofMul hqv).symm
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro x hx
    rw [Submodule.mem_span_singleton] at hx
    obtain ⟨c, rfl⟩ := hx
    have hcomm : (a : G) * (q : G) = (q : G) * a :=
      Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hqC).2 a (Set.mem_singleton a)
    have hB0 : (qS S).polarBilin (Additive.ofMul (mkQbar S ⟨a, haQ⟩))
        (Additive.ofMul (mkQbar S q)) = 0 :=
      (polar_q_eq_zero_iff S ⟨a, haQ⟩ q).mpr hcomm
    rw [hv']
    rcases CFSG.RankThree.Literature.FSmith.zmod2_cases c with rfl | rfl
    · simp
    · simpa using hB0
  · intro hv
    obtain ⟨q, hq⟩ := QuotientGroup.mk'_surjective ((ZQ z).subgroupOf (Q z))
      (Additive.toMul v)
    have hv' : v = Additive.ofMul (mkQbar S q) := by
      have h := congrArg Additive.ofMul hq.symm
      simpa [mkQbar] using h
    rw [hv'] at hv
    have hB0 : (qS S).polarBilin (Additive.ofMul (mkQbar S ⟨a, haQ⟩))
        (Additive.ofMul (mkQbar S q)) = 0 :=
      (LinearMap.BilinForm.mem_orthogonal_iff.mp hv) _
        (Submodule.mem_span_singleton_self _)
    have hcomm : (a : G) * (q : G) = (q : G) * a :=
      (polar_q_eq_zero_iff S ⟨a, haQ⟩ q).mp hB0
    have hqC : (q : G) ∈ Q z ⊓ Subgroup.centralizer ({a} : Set G) := by
      refine Subgroup.mem_inf.mpr ⟨q.2, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst y
      exact hcomm
    rw [mem_QaInterImage_iff]
    refine ⟨q, hqC, ?_⟩
    rw [hv']
    rfl

theorem aV_ne_zero (S : Setting z E F) {a : G} (haQ : a ∈ Q z) (haZ : a ∉ ZQ z) :
    Additive.ofMul (mkQbar S ⟨a, haQ⟩) ≠ 0 := by
  intro h
  apply haZ
  have h1 : (mkQbar S ⟨a, haQ⟩ : QbarOf S) = 1 := by
    have := congrArg Additive.toMul h
    simpa using this
  rw [← MonoidHom.mem_ker] at h1
  rw [show (mkQbar S).ker = (ZQ z).subgroupOf (Q z) from QuotientGroup.ker_mk' _] at h1
  exact Subgroup.mem_subgroupOf.mp h1

theorem commSpace_le_span_of_w0 (S : Setting z E F) {a s : G}
    (haQ : a ∈ Q z) (hconj : IsConj z a)
    (hzaZ : z ∉ centerIn (QaOf a))
    (hsZ : s ∈ centerIn (QaOf a)) (hsH : s ∈ H z)
    {u0 : Additive (QbarOf S)}
    (hu0 : (qS S).polarBilin (Additive.ofMul (mkQbar S ⟨a, haQ⟩)) u0 = 1) :
    commSpace (conjQbar S ⟨s, hsH⟩) ≤
      Submodule.span (ZMod 2)
        ({Additive.ofMul (mkQbar S ⟨a, haQ⟩),
          conjQbar S ⟨s, hsH⟩ u0 - u0} : Set (Additive (QbarOf S))) := by
  letI : Module (ZMod 2) (Additive (Abelianization F)) := modAbF S
  let aV : Additive (QbarOf S) := Additive.ofMul (mkQbar S ⟨a, haQ⟩)
  let σ : Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S) := conjQbar S ⟨s, hsH⟩
  let φ : Additive (QbarOf S) →ₗ[ZMod 2] Additive (QbarOf S) :=
    (σ : Additive (QbarOf S) →ₗ[ZMod 2] Additive (QbarOf S)) - 1
  let B := (qS S).polarBilin
  let W0 : Submodule (ZMod 2) (Additive (QbarOf S)) :=
    QaInterImage S (Q z ⊓ Subgroup.centralizer ({a} : Set G))
  have hW0 : W0 = LinearMap.BilinForm.orthogonal B (Submodule.span (ZMod 2) {aV}) := by
    simpa [W0, B, aV] using QaInterImage_CQ_eq_orthogonal S haQ
  intro w hw
  rw [mem_commSpace] at hw
  obtain ⟨v, rfl⟩ := hw
  let c : ZMod 2 := B aV v
  have hvc : v + c • u0 ∈ W0 := by
    rw [hW0, LinearMap.BilinForm.mem_orthogonal_iff]
    intro x hx
    rw [Submodule.mem_span_singleton] at hx
    obtain ⟨d, rfl⟩ := hx
    rcases CFSG.RankThree.Literature.FSmith.zmod2_cases d with rfl | rfl
    · simp
    · simp only [one_smul]
      rw [LinearMap.map_add, LinearMap.map_smul, hu0, smul_eq_mul, mul_one]
      change (B aV v) + (B aV v) = 0
      exact CFSG.LargeExtraspecial.OrthoF2.zmod2_add_self _
  have hvdecomp : v = (v + c • u0) + c • u0 := by
    rw [add_assoc, add_self_vec (ZMod 2), add_zero]
  have hsub : φ v = φ (v + c • u0) + c • φ u0 := by
    conv_lhs => rw [hvdecomp]
    rw [map_add, map_smul]
  have hfirst : φ (v + c • u0) ∈ Submodule.span (ZMod 2) {aV} := by
    have hle := map_sub_QaInterImage_CQ_le_span S haQ hconj hzaZ hsZ hsH
    exact hle (Submodule.mem_map.mpr ⟨v + c • u0, hvc, rfl⟩)
  have hsecond : c • φ u0 ∈
      Submodule.span (ZMod 2) ({aV, σ u0 - u0} : Set (Additive (QbarOf S))) := by
    have hmem : φ u0 ∈
        Submodule.span (ZMod 2) ({aV, σ u0 - u0} : Set (Additive (QbarOf S))) :=
      Submodule.subset_span (by simp [φ])
    exact Submodule.smul_mem _ c hmem
  change φ v ∈ _
  rw [hsub]
  refine Submodule.add_mem _ ?_ hsecond
  have hmono : Submodule.span (ZMod 2) {aV} ≤
      Submodule.span (ZMod 2) ({aV, σ u0 - u0} : Set (Additive (QbarOf S))) := by
    refine Submodule.span_mono ?_
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact Set.mem_insert _ _
  exact hmono hfirst

theorem conjQbar_apply_mk_self (S : Setting z E F) {a s : G}
    (haQ : a ∈ Q z) (hsZ : s ∈ centerIn (QaOf a)) (hsH : s ∈ H z) :
    conjQbar S ⟨s, hsH⟩ (Additive.ofMul (QuotientGroup.mk ⟨a, haQ⟩)) =
      Additive.ofMul (QuotientGroup.mk ⟨a, haQ⟩) := by
  have hsub : conjAutQ S ⟨s, hsH⟩ ⟨a, haQ⟩ = ⟨a, haQ⟩ := by
    apply Subtype.ext
    rw [conjAutQ_apply]
    have hcomm : a * s = s * a :=
      Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hsZ).2 a (mem_QaOf_self a)
    rw [← hcomm]
    group
  rw [conjQbar_apply_mk, hsub]

theorem polar_aV_commSpace_eq_zero (S : Setting z E F) {a s : G}
    (haQ : a ∈ Q z) (hsZ : s ∈ centerIn (QaOf a)) (hsH : s ∈ H z)
    {w : Additive (QbarOf S)} (hw : w ∈ commSpace (conjQbar S ⟨s, hsH⟩)) :
    (qS S).polarBilin (Additive.ofMul (QuotientGroup.mk ⟨a, haQ⟩)) w = 0 := by
  letI : Module (ZMod 2) (Additive (Abelianization F)) := modAbF S
  rw [mem_commSpace] at hw
  obtain ⟨v, rfl⟩ := hw
  have hfix : conjQbar S ⟨s, hsH⟩ (Additive.ofMul (QuotientGroup.mk ⟨a, haQ⟩)) =
      Additive.ofMul (QuotientGroup.mk ⟨a, haQ⟩) :=
    conjQbar_apply_mk_self S haQ hsZ hsH
  have hiso : (qS S).polarBilin
      (conjQbar S ⟨s, hsH⟩ (Additive.ofMul (QuotientGroup.mk ⟨a, haQ⟩)))
      (conjQbar S ⟨s, hsH⟩ v) =
      (qS S).polarBilin (Additive.ofMul (QuotientGroup.mk ⟨a, haQ⟩)) v :=
    TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup
      (conjQbar_mem_orthogonal S ⟨s, hsH⟩) _ _
  have h1 : (qS S).polarBilin (Additive.ofMul (QuotientGroup.mk ⟨a, haQ⟩))
      (conjQbar S ⟨s, hsH⟩ v) =
      (qS S).polarBilin (Additive.ofMul (QuotientGroup.mk ⟨a, haQ⟩)) v := by
    calc
      (qS S).polarBilin (Additive.ofMul (QuotientGroup.mk ⟨a, haQ⟩))
          (conjQbar S ⟨s, hsH⟩ v) =
          (qS S).polarBilin
            (conjQbar S ⟨s, hsH⟩ (Additive.ofMul (QuotientGroup.mk ⟨a, haQ⟩)))
            (conjQbar S ⟨s, hsH⟩ v) := by rw [hfix]
      _ = (qS S).polarBilin (Additive.ofMul (QuotientGroup.mk ⟨a, haQ⟩)) v := hiso
  rw [LinearMap.map_sub, h1, sub_self]

theorem conj_s_eq_mul_z_of_commutator (S : Setting z E F) {s q : G}
    (hs2 : s ^ 2 = 1) (ht2 : ⁅q, s⁆ ^ 2 = z) :
    ⁅q, s⁆ * s * ⁅q, s⁆⁻¹ = s * z := by
  set t : G := ⁅q, s⁆ with ht
  have hs2' : s * s = 1 := by simpa [pow_two] using hs2
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs2'
  have hst : s * t * s = t⁻¹ := by
    rw [ht, commutatorElement_def, hsinv, mul_inv_rev]
    simp only [mul_inv_rev, hsinv, inv_inv]
    rw [show s * (q * s * q⁻¹ * s) * s = s * (q * s * q⁻¹) by
      calc
        s * (q * s * q⁻¹ * s) * s = (s * q * s * q⁻¹) * (s * s) := by group
        _ = (s * q * s * q⁻¹) * 1 := by rw [hs2']
        _ = s * (q * s * q⁻¹) := by group]
    group
  have h1 : t * s = s * t⁻¹ := by
    have h := congrArg (fun x => s * x) hst
    have hL : s * (s * t * s) = t * s := by
      calc
        s * (s * t * s) = (s * s) * t * s := by group
        _ = 1 * t * s := by rw [hs2']
        _ = t * s := by group
    rw [hL] at h
    exact h
  have hz2 : z ^ 2 = 1 := by
    simpa [S.hyp.orderOf_z] using pow_orderOf_eq_one z
  have hz2' : z * z = 1 := by simpa [pow_two] using hz2
  calc
    t * s * t⁻¹ = (s * t⁻¹) * t⁻¹ := by rw [h1]
    _ = s * (t⁻¹ * t⁻¹) := by group
    _ = s * (t ^ 2)⁻¹ := by group
    _ = s * z⁻¹ := by rw [ht2]
    _ = s * z := by rw [inv_eq_of_mul_eq_one_right hz2']

theorem q_eq_zero_of_mem_commSpace_conjQbar (S : Setting z E F) {a s : G}
    (haQ : a ∈ Q z) (hzaZ : z ∉ centerIn (QaOf a))
    (hsZ : s ∈ centerIn (QaOf a)) (hsH : s ∈ H z) (hs2 : s ^ 2 = 1)
    {w : Additive (QbarOf S)} (hw : w ∈ commSpace (conjQbar S ⟨s, hsH⟩)) :
    qS S w = 0 := by
  letI : Module (ZMod 2) (Additive (Abelianization F)) := modAbF S
  by_contra hqne
  obtain ⟨q, rfl⟩ := (mem_commSpace_conjQbar_iff S hsH).mp hw
  let t : G := ⁅(q : G), s⁆
  have htQ : t ∈ Q z := commutator_mem_Q_of_mem_H hsH q.2
  have htclass : Additive.ofMul (mkQbar S ⟨t, htQ⟩) =
      Additive.ofMul (mkQbar S ⟨⁅(q : G), s⁆,
        commutator_mem_Q_of_mem_H hsH q.2⟩) := rfl
  have hq1 : qS S (Additive.ofMul (mkQbar S ⟨t, htQ⟩)) = 1 := by
    rw [htclass]
    rcases CFSG.RankThree.Literature.FSmith.zmod2_cases
      (qS S (Additive.ofMul (mkQbar S ⟨⁅(q : G), s⁆,
        commutator_mem_Q_of_mem_H hsH q.2⟩))) with h | h
    · exact absurd h hqne
    · exact h
  have ht2z : t ^ 2 = z := by
    have htz : t ^ 2 ∈ Subgroup.zpowers z := sq_mem_zpowers_of_mem_Q S htQ
    rcases eq_one_or_z_of_mem_zpowers S htz with h1 | hz
    · have h0 : qS S (Additive.ofMul (mkQbar S ⟨t, htQ⟩)) = 0 :=
        (q_eq_zero_iff S ⟨t, htQ⟩).mpr h1
      rw [h0] at hq1
      exact False.elim (zero_ne_one hq1)
    · exact hz
  have hw' : Additive.ofMul (mkQbar S ⟨t, htQ⟩) ∈
      commSpace (conjQbar S ⟨s, hsH⟩) := by
    rw [htclass]
    exact (mem_commSpace_conjQbar_iff S hsH).mpr ⟨q, rfl⟩
  have hB0 : (qS S).polarBilin (Additive.ofMul (QuotientGroup.mk ⟨a, haQ⟩))
      (Additive.ofMul (mkQbar S ⟨t, htQ⟩)) = 0 := by
    have h := polar_aV_commSpace_eq_zero S haQ hsZ hsH hw'
    simpa only [mkQbar, QuotientGroup.mk'_apply] using h
  have htCa : t ∈ Subgroup.centralizer ({a} : Set G) := by
    have h := (polar_q_eq_zero_iff S ⟨a, haQ⟩ ⟨t, htQ⟩).mp hB0
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst y
    exact h
  have hconjZ : t * s * t⁻¹ ∈ centerIn (QaOf a) :=
    conj_mem_centerIn_QaOf S htCa hsZ
  have hsz : s * z ∈ centerIn (QaOf a) := by
    have ht2 : ⁅(q : G), s⁆ ^ 2 = z := ht2z
    rw [← conj_s_eq_mul_z_of_commutator S hs2 ht2]
    exact hconjZ
  have hz : z ∈ centerIn (QaOf a) := by
    have := (centerIn (QaOf a)).mul_mem ((centerIn (QaOf a)).inv_mem hsZ) hsz
    simpa using this
  exact hzaZ hz

theorem commutator_zpowers_eq_closure_commutator {s : G} (hs2 : s ^ 2 = 1) :
    ⁅Q z, Subgroup.zpowers s⁆ =
      Subgroup.closure {g : G | ∃ q ∈ Q z, ⁅q, s⁆ = g} := by
  have hs2' : s * s = 1 := by simpa [pow_two] using hs2
  rw [Subgroup.commutator_def]
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro g ⟨q, hq, t, ht, rfl⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ht
    obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' k
    · have h1 : ⁅q, s ^ (2 * m)⁆ = 1 := by
        rw [zpow_mul]
        simp [hs2]
      rw [h1]
      exact Subgroup.one_mem _
    · have h1 : s ^ (2 * m + 1) = s := by
        rw [zpow_add, zpow_mul]
        simp [hs2]
      rw [h1]
      exact Subgroup.subset_closure (Set.mem_setOf.mpr ⟨q, hq, rfl⟩)
  · rw [Subgroup.closure_le]
    rintro g ⟨q, hq, rfl⟩
    exact Subgroup.subset_closure ⟨q, hq, s, Subgroup.mem_zpowers s, rfl⟩

theorem commutator_zpowers_sq_eq_one (S : Setting z E F) {a s q : G}
    (haQ : a ∈ Q z)
    (hzaZ : z ∉ centerIn (QaOf a))
    (hsZ : s ∈ centerIn (QaOf a)) (hsH : s ∈ H z) (hs2 : s ^ 2 = 1)
    (hq : q ∈ Q z) : ⁅q, s⁆ ^ 2 = 1 := by
  letI : Module (ZMod 2) (Additive (Abelianization F)) := modAbF S
  have htQ : ⁅q, s⁆ ∈ Q z := commutator_mem_Q_of_mem_H hsH hq
  have hw : Additive.ofMul (mkQbar S ⟨⁅q, s⁆, htQ⟩) ∈
      commSpace (conjQbar S ⟨s, hsH⟩) :=
    (mem_commSpace_conjQbar_iff S hsH).mpr ⟨⟨q, hq⟩, rfl⟩
  have h0 := q_eq_zero_of_mem_commSpace_conjQbar S haQ hzaZ hsZ hsH hs2 hw
  exact (q_eq_zero_iff S ⟨⁅q, s⁆, htQ⟩).mp h0

theorem commutator_zpowers_commute (S : Setting z E F) {a s q₁ q₂ : G}
    (haQ : a ∈ Q z)
    (hzaZ : z ∉ centerIn (QaOf a))
    (hsZ : s ∈ centerIn (QaOf a)) (hsH : s ∈ H z) (hs2 : s ^ 2 = 1)
    (hq₁ : q₁ ∈ Q z) (hq₂ : q₂ ∈ Q z) :
    ⁅q₁, s⁆ * ⁅q₂, s⁆ = ⁅q₂, s⁆ * ⁅q₁, s⁆ := by
  letI : Module (ZMod 2) (Additive (Abelianization F)) := modAbF S
  have ht₁ : ⁅q₁, s⁆ ∈ Q z := commutator_mem_Q_of_mem_H hsH hq₁
  have ht₂ : ⁅q₂, s⁆ ∈ Q z := commutator_mem_Q_of_mem_H hsH hq₂
  have hw₁ : Additive.ofMul (mkQbar S ⟨⁅q₁, s⁆, ht₁⟩) ∈
      commSpace (conjQbar S ⟨s, hsH⟩) :=
    (mem_commSpace_conjQbar_iff S hsH).mpr ⟨⟨q₁, hq₁⟩, rfl⟩
  have hw₂ : Additive.ofMul (mkQbar S ⟨⁅q₂, s⁆, ht₂⟩) ∈
      commSpace (conjQbar S ⟨s, hsH⟩) :=
    (mem_commSpace_conjQbar_iff S hsH).mpr ⟨⟨q₂, hq₂⟩, rfl⟩
  have hw₁₂ : Additive.ofMul (mkQbar S ⟨⁅q₁, s⁆, ht₁⟩) +
      Additive.ofMul (mkQbar S ⟨⁅q₂, s⁆, ht₂⟩) ∈
      commSpace (conjQbar S ⟨s, hsH⟩) := Submodule.add_mem _ hw₁ hw₂
  have h0₁ := q_eq_zero_of_mem_commSpace_conjQbar S haQ hzaZ hsZ hsH hs2 hw₁
  have h0₂ := q_eq_zero_of_mem_commSpace_conjQbar S haQ hzaZ hsZ hsH hs2 hw₂
  have h0₁₂ := q_eq_zero_of_mem_commSpace_conjQbar S haQ hzaZ hsZ hsH hs2 hw₁₂
  have hB : (qS S).polarBilin (Additive.ofMul (mkQbar S ⟨⁅q₁, s⁆, ht₁⟩))
      (Additive.ofMul (mkQbar S ⟨⁅q₂, s⁆, ht₂⟩)) = 0 := by
    have h := map_add_eq (qS S)
      (Additive.ofMul (mkQbar S ⟨⁅q₁, s⁆, ht₁⟩))
      (Additive.ofMul (mkQbar S ⟨⁅q₂, s⁆, ht₂⟩))
    rw [h0₁, h0₂, h0₁₂, zero_add, zero_add] at h
    exact h.symm
  exact (polar_q_eq_zero_iff S ⟨⁅q₁, s⁆, ht₁⟩ ⟨⁅q₂, s⁆, ht₂⟩).mp hB

theorem isElemAbelian_commutator_zpowers (S : Setting z E F) {a s : G}
    (haQ : a ∈ Q z)
    (hzaZ : z ∉ centerIn (QaOf a))
    (hsZ : s ∈ centerIn (QaOf a)) (hsH : s ∈ H z) (hs2 : s ^ 2 = 1) :
    IsElemAbelian 2 ⁅Q z, Subgroup.zpowers s⁆ := by
  rw [commutator_zpowers_eq_closure_commutator hs2]
  refine IsElemAbelian.closure_of_commute ?_ ?_
  · rintro _ ⟨q₁, hq₁, rfl⟩ _ ⟨q₂, hq₂, rfl⟩
    exact commutator_zpowers_commute S haQ hzaZ hsZ hsH hs2 hq₁ hq₂
  · rintro _ ⟨q, hq, rfl⟩
    exact commutator_zpowers_sq_eq_one S haQ hzaZ hsZ hsH hs2 hq

theorem eq_one_of_commSpace_eq_span_singular (S : Setting z E F) {s c : G}
    (hsH : s ∈ H z) (hc : c ∈ Q z)
    (hc0 : Additive.ofMul (mkQbar S ⟨c, hc⟩) ≠ 0)
    (hcW : commSpace (conjQbar S ⟨s, hsH⟩) =
      Submodule.span (ZMod 2) {Additive.ofMul (mkQbar S ⟨c, hc⟩)})
    (hqc : qS S (Additive.ofMul (mkQbar S ⟨c, hc⟩)) = 0) :
    conjQbar S ⟨s, hsH⟩ = 1 := by
  letI : Module (ZMod 2) (Additive (Abelianization F)) := modAbF S
  let σ : Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S) := conjQbar S ⟨s, hsH⟩
  let B := (qS S).polarBilin
  let cV : Additive (QbarOf S) := Additive.ofMul (mkQbar S ⟨c, hc⟩)
  have hσO : σ ∈ TauCeti.QuadraticMap.orthogonalGroup (qS S) :=
    conjQbar_mem_orthogonal S ⟨s, hsH⟩
  have hfix : ∀ x : Additive (QbarOf S), B cV x = 0 → σ x = x := by
    intro x hx
    have hmem : σ x - x ∈ Submodule.span (ZMod 2) {cV} := by
      rw [← hcW]
      exact sub_mem_commSpace σ x
    obtain ⟨lam, hlam⟩ := Submodule.mem_span_singleton.mp hmem
    have hσx : σ x = x + lam • cV := by rw [hlam]; abel
    have hex : ∃ y, B cV y ≠ 0 := by
      by_contra h
      push Not at h
      exact hc0 ((q_nondegenerate S).1 cV h)
    obtain ⟨y, hy⟩ := hex
    have hy1 : B cV y = 1 := by
      rcases CFSG.RankThree.Literature.FSmith.zmod2_cases (B cV y) with h | h
      · exact absurd h hy
      · exact h
    have hmem_y : σ y - y ∈ Submodule.span (ZMod 2) {cV} := by
      rw [← hcW]
      exact sub_mem_commSpace σ y
    obtain ⟨nu, hnu⟩ := Submodule.mem_span_singleton.mp hmem_y
    have hσy : σ y = y + nu • cV := by rw [hnu]; abel
    have hσc : σ cV = cV := by
      have hmem_c : σ cV - cV ∈ Submodule.span (ZMod 2) {cV} := by
        rw [← hcW]
        exact sub_mem_commSpace σ cV
      obtain ⟨mu, hmu⟩ := Submodule.mem_span_singleton.mp hmem_c
      have h : σ cV = cV + mu • cV := by rw [hmu]; abel
      rcases CFSG.RankThree.Literature.FSmith.zmod2_cases mu with rfl | rfl
      · simpa using h
      · exfalso
        have h0 : σ cV = 0 := by
          rw [h, one_smul, add_self_vec (ZMod 2)]
        have hc0' : cV = 0 := σ.injective (by simpa using h0)
        exact hc0 hc0'
    have hBcσy : B cV (σ y) = B cV y := by
      have h := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hσO cV y
      rwa [hσc] at h
    have hBxc : B x cV = 0 := by
      have h := (QuadraticMap.polar_comm (qS S) x cV).trans hx
      simpa [B, QuadraticMap.polarBilin_apply_apply] using h
    have hBcc : B cV cV = 0 := polar_self_eq_zero (qS S) cV
    have hiso : B (σ x) (σ y) = B x y :=
      TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hσO x y
    have hmain : B (σ x) (σ y) = B x y + lam := by
      rw [hσx, hσy]
      simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul,
        hBcσy, hBxc, hBcc, hy1, mul_one, mul_zero, add_zero, zero_add]
    have hlam0 : lam = 0 := by
      rw [hmain] at hiso
      simpa using hiso
    rw [hσx, hlam0, zero_smul, add_zero]
  exact CFSG.LargeExtraspecial.eq_one_of_fix_orthogonal_of_map_eq_zero
    (q := qS S) (q_nondegenerate S) hqc hσO hfix

theorem mem_Q_of_conjQbar_eq_one (S : Setting z E F) {s : G} (hsH : s ∈ H z)
    (hσ : conjQbar S ⟨s, hsH⟩ = 1) : s ∈ Q z := by
  refine (S.hyp.centralizer_quotient s).mp ⟨hsH, ?_⟩
  intro x hx
  have hfix : conjQbar S ⟨s, hsH⟩
      (Additive.ofMul (QuotientGroup.mk (⟨x, hx⟩ : ↥(Q z)))) =
      Additive.ofMul (QuotientGroup.mk (⟨x, hx⟩ : ↥(Q z))) := by
    rw [hσ]
    rfl
  rw [conjQbar_apply_mk] at hfix
  have hq : (QuotientGroup.mk (conjAutQ S ⟨s, hsH⟩ ⟨x, hx⟩) : QbarOf S) =
      QuotientGroup.mk ⟨x, hx⟩ := Additive.ofMul.injective hfix
  have hmem := (QuotientGroup.eq_iff_div_mem).mp hq
  have hmem' : conjAutQ S ⟨s, hsH⟩ ⟨x, hx⟩ * ⟨x, hx⟩⁻¹ ∈
      (ZQ z).subgroupOf (Q z) := by
    simpa [div_eq_mul_inv] using hmem
  have hval : ((conjAutQ S ⟨s, hsH⟩ ⟨x, hx⟩ * ⟨x, hx⟩⁻¹ : ↥(Q z)) : G) ∈ ZQ z :=
    Subgroup.mem_subgroupOf.mp hmem'
  simpa [conjAutQ_apply, div_eq_mul_inv] using hval

theorem commSpace_ne_bot_of_not_mem_Q (S : Setting z E F) {s : G} (hsH : s ∈ H z)
    (hsQ : s ∉ Q z) : commSpace (conjQbar S ⟨s, hsH⟩) ≠ ⊥ := by
  intro hbot
  have hσ : conjQbar S ⟨s, hsH⟩ = 1 := by
    apply LinearEquiv.ext
    intro v
    have hmem : conjQbar S ⟨s, hsH⟩ v - v ∈ commSpace (conjQbar S ⟨s, hsH⟩) :=
      sub_mem_commSpace _ v
    rw [hbot] at hmem
    have h0 : conjQbar S ⟨s, hsH⟩ v - v = 0 := by simpa using hmem
    exact sub_eq_zero.mp h0
  exact hsQ (mem_Q_of_conjQbar_eq_one S hsH hσ)

theorem finrank_commSpace_eq_two (S : Setting z E F) {a s : G}
    (haQ : a ∈ Q z) (hconj : IsConj z a) (haZ : a ∉ ZQ z)
    (hzaZ : z ∉ centerIn (QaOf a))
    (hsZ : s ∈ centerIn (QaOf a)) (hsH : s ∈ H z) (hs2 : s ^ 2 = 1)
    (hsQ : s ∉ Q z) :
    finrank (ZMod 2) (commSpace (conjQbar S ⟨s, hsH⟩)) = 2 := by
  classical
  letI : Module (ZMod 2) (Additive (Abelianization F)) := modAbF S
  let V := Additive (QbarOf S)
  let aV : V := Additive.ofMul (mkQbar S ⟨a, haQ⟩)
  let B := (qS S).polarBilin
  have haV0 : aV ≠ 0 := aV_ne_zero S haQ haZ
  have hex : ∃ u0 : V, B aV u0 ≠ 0 := by
    by_contra h
    push Not at h
    exact haV0 ((q_nondegenerate S).1 aV h)
  obtain ⟨u0, hu0ne⟩ := hex
  have hu0 : B aV u0 = 1 := by
    rcases CFSG.RankThree.Literature.FSmith.zmod2_cases (B aV u0) with h | h
    · exact absurd h hu0ne
    · exact h
  have hle : commSpace (conjQbar S ⟨s, hsH⟩) ≤
      Submodule.span (ZMod 2)
        ({aV, conjQbar S ⟨s, hsH⟩ u0 - u0} : Set V) :=
    commSpace_le_span_of_w0 S haQ hconj hzaZ hsZ hsH hu0
  have hWne : commSpace (conjQbar S ⟨s, hsH⟩) ≠ ⊥ :=
    commSpace_ne_bot_of_not_mem_Q S hsH hsQ
  have hpos : 0 < finrank (ZMod 2) (commSpace (conjQbar S ⟨s, hsH⟩)) := by
    rw [Module.finrank_pos_iff_exists_ne_zero]
    obtain ⟨c, hcW, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hWne
    exact ⟨⟨c, hcW⟩, by simpa using hc0⟩
  have hdim_le : finrank (ZMod 2) (commSpace (conjQbar S ⟨s, hsH⟩)) ≤ 2 := by
    have h1 : finrank (ZMod 2) (commSpace (conjQbar S ⟨s, hsH⟩)) ≤
        finrank (ZMod 2) (Submodule.span (ZMod 2)
          ({aV, conjQbar S ⟨s, hsH⟩ u0 - u0} : Set V)) :=
      Submodule.finrank_mono hle
    have h2 : finrank (ZMod 2) (Submodule.span (ZMod 2)
          ({aV, conjQbar S ⟨s, hsH⟩ u0 - u0} : Set V)) ≤ 2 := by
      have hcard : ({aV, conjQbar S ⟨s, hsH⟩ u0 - u0} : Set V).toFinset.card ≤ 2 := by
        by_cases h : aV = conjQbar S ⟨s, hsH⟩ u0 - u0 <;> simp [h]
      exact le_trans (finrank_span_le_card _) hcard
    exact le_trans h1 h2
  have hdim_ne_one : finrank (ZMod 2) (commSpace (conjQbar S ⟨s, hsH⟩)) ≠ 1 := by
    intro hdim1
    obtain ⟨c, hcW, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hWne
    have hspan : commSpace (conjQbar S ⟨s, hsH⟩) =
        Submodule.span (ZMod 2) {c} :=
      eq_span_singleton_of_mem_of_finrank_eq_one hdim1 hcW hc0
    obtain ⟨q, hq⟩ := QuotientGroup.mk'_surjective ((ZQ z).subgroupOf (Q z))
      (Additive.toMul c)
    have hcvec : c = Additive.ofMul (mkQbar S q) := by
      have h := congrArg Additive.ofMul hq.symm
      simpa [mkQbar] using h
    have hc0' : Additive.ofMul (mkQbar S q) ≠ 0 := by
      rw [← hcvec]
      exact hc0
    have hspan' : commSpace (conjQbar S ⟨s, hsH⟩) =
        Submodule.span (ZMod 2) {Additive.ofMul (mkQbar S q)} := by
      rw [hspan, hcvec]
    have hc_mem : Additive.ofMul (mkQbar S q) ∈
        commSpace (conjQbar S ⟨s, hsH⟩) := by
      rw [hspan']
      exact Submodule.mem_span_singleton_self _
    have hqc : qS S (Additive.ofMul (mkQbar S q)) = 0 :=
      q_eq_zero_of_mem_commSpace_conjQbar S haQ hzaZ hsZ hsH hs2 hc_mem
    have hσ1 := eq_one_of_commSpace_eq_span_singular S hsH q.2 hc0' hspan' hqc
    exact hsQ (mem_Q_of_conjQbar_eq_one S hsH hσ1)
  omega

theorem QaInterImage_commutator_eq_commSpace (S : Setting z E F) {s : G}
    (hsH : s ∈ H z) (hs2 : s ^ 2 = 1) :
    QaInterImage S ⁅Q z, Subgroup.zpowers s⁆ =
      commSpace (conjQbar S ⟨s, hsH⟩) := by
  letI : Module (ZMod 2) (Additive (Abelianization F)) := modAbF S
  let A : Subgroup G := ⁅Q z, Subgroup.zpowers s⁆
  let W : Submodule (ZMod 2) (Additive (QbarOf S)) :=
    commSpace (conjQbar S ⟨s, hsH⟩)
  have hAeq : A = Subgroup.closure {g : G | ∃ q ∈ Q z, ⁅q, s⁆ = g} :=
    commutator_zpowers_eq_closure_commutator hs2
  have hclQ : Subgroup.closure {g : G | ∃ q ∈ Q z, ⁅q, s⁆ = g} ≤ Q z := by
    rw [Subgroup.closure_le]
    rintro g ⟨q, hq, rfl⟩
    exact commutator_mem_Q_of_mem_H hsH hq
  have hgen : ∀ q ∈ Subgroup.closure {g : G | ∃ x ∈ Q z, ⁅x, s⁆ = g},
      ∀ hq : q ∈ Q z, Additive.ofMul (mkQbar S ⟨q, hq⟩) ∈ W := by
    intro q hq
    induction hq using Subgroup.closure_induction with
    | mem x hx =>
        intro hxQ
        obtain ⟨y, hy, rfl⟩ := hx
        have htQ : ⁅y, s⁆ ∈ Q z := commutator_mem_Q_of_mem_H hsH hy
        have hclass : Additive.ofMul (mkQbar S ⟨⁅y, s⁆, hxQ⟩) =
            Additive.ofMul (mkQbar S ⟨⁅y, s⁆, htQ⟩) := rfl
        rw [hclass]
        rw [additive_commutator_eq_sub S hsH hy]
        exact sub_mem_commSpace _ _
    | one =>
        intro _
        exact Submodule.zero_mem _
    | mul x y hx hy ihx ihy =>
        intro hxyQ
        have hxQ : x ∈ Q z := hclQ hx
        have hyQ : y ∈ Q z := hclQ hy
        have hmul : Additive.ofMul (mkQbar S ⟨x * y, hxyQ⟩) =
            Additive.ofMul (mkQbar S ⟨x, hxQ⟩) +
              Additive.ofMul (mkQbar S ⟨y, hyQ⟩) := by
          have h1 : (mkQbar S ⟨x * y, hxyQ⟩ : QbarOf S) =
              mkQbar S ⟨x, hxQ⟩ * mkQbar S ⟨y, hyQ⟩ := by
            rw [← map_mul]
            congr 1
          rw [h1]
          rfl
        rw [hmul]
        exact Submodule.add_mem _ (ihx hxQ) (ihy hyQ)
    | inv x hx ihx =>
        intro hxQ
        have hxQ' : x ∈ Q z := hclQ hx
        have hinv : Additive.ofMul (mkQbar S ⟨x⁻¹, hxQ⟩) =
            -Additive.ofMul (mkQbar S ⟨x, hxQ'⟩) := by
          have h1 : (mkQbar S ⟨x⁻¹, hxQ⟩ : QbarOf S) =
              (mkQbar S ⟨x, hxQ'⟩)⁻¹ := by
            rw [← map_inv]
            congr 1
          rw [h1]
          rfl
        rw [hinv]
        exact Submodule.neg_mem _ (ihx hxQ')
  ext v
  rw [mem_QaInterImage_iff]
  constructor
  · rintro ⟨q, hqA, hqv⟩
    have hqA' : (q : G) ∈ Subgroup.closure {g : G | ∃ x ∈ Q z, ⁅x, s⁆ = g} := by
      rw [← hAeq]
      exact hqA
    have hv : v = Additive.ofMul (mkQbar S q) := (congrArg Additive.ofMul hqv).symm
    rw [hv]
    exact hgen q hqA' q.2
  · intro hv
    obtain ⟨q, hqv⟩ := (mem_commSpace_conjQbar_iff S hsH).mp hv
    have htQ : ⁅(q : G), s⁆ ∈ Q z := commutator_mem_Q_of_mem_H hsH q.2
    refine ⟨⟨⁅(q : G), s⁆, htQ⟩, ?_, ?_⟩
    · change (⁅(q : G), s⁆ : G) ∈ A
      rw [hAeq]
      exact Subgroup.subset_closure ⟨(q : G), q.2, rfl⟩
    · rw [hqv]
      rfl

theorem card_commSpace_eq_four (S : Setting z E F) {a s : G}
    (haQ : a ∈ Q z) (hconj : IsConj z a) (haZ : a ∉ ZQ z)
    (hzaZ : z ∉ centerIn (QaOf a))
    (hsZ : s ∈ centerIn (QaOf a)) (hsH : s ∈ H z) (hs2 : s ^ 2 = 1)
    (hsQ : s ∉ Q z) :
    Nat.card (commSpace (conjQbar S ⟨s, hsH⟩)) = 4 := by
  classical
  letI : Module (ZMod 2) (Additive (Abelianization F)) := modAbF S
  haveI : Module.Finite (ZMod 2) (commSpace (conjQbar S ⟨s, hsH⟩)) :=
    Module.Finite.of_finite
  have h := Module.natCard_eq_pow_finrank (K := ZMod 2)
    (V := commSpace (conjQbar S ⟨s, hsH⟩))
  have h2 : Nat.card (ZMod 2) = 2 := by simpa using Nat.card_zmod (n := 2)
  rw [h2, finrank_commSpace_eq_two S haQ hconj haZ hzaZ hsZ hsH hs2 hsQ] at h
  norm_num at h
  exact h

theorem card_sup_ZQ_eq_card_QaInterImage_mul (S : Setting z E F) (A : Subgroup G)
    (hA : A ≤ Q z) :
    Nat.card (A ⊔ ZQ z : Subgroup G) =
      Nat.card (QaInterImage S A) * Nat.card (ZQ z) := by
  have hnorm : A ≤ Subgroup.normalizer (ZQ z : Set G) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have haQ : a ∈ Q z := hA ha
    constructor
    · intro hx
      have hcomm : a * x = x * a :=
        Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hx).2 a haQ
      have hxeq : a * x * a⁻¹ = x := by rw [hcomm]; group
      rw [hxeq]
      exact hx
    · intro hx
      have hy : a * x * a⁻¹ ∈ ZQ z := hx
      have hcomm : a * (a * x * a⁻¹) = (a * x * a⁻¹) * a :=
        Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hy).2 a haQ
      have hxeq : x = a⁻¹ * (a * x * a⁻¹) * a := by group
      have hconj : a⁻¹ * (a * x * a⁻¹) * a = a * x * a⁻¹ := by
        calc
          a⁻¹ * (a * x * a⁻¹) * a = a⁻¹ * ((a * x * a⁻¹) * a) := by group
          _ = a⁻¹ * (a * (a * x * a⁻¹)) := by rw [← hcomm]
          _ = a * x * a⁻¹ := by group
      rw [hxeq, hconj]
      exact hy
  have hsup := CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
    (H := A) (K := ZQ z) hnorm
  have himg := card_QaInterImage_mul_card_inf S A hA
  have hpos : 0 < Nat.card (A ⊓ ZQ z : Subgroup G) := Nat.card_pos
  have h : Nat.card (A ⊔ ZQ z : Subgroup G) * Nat.card (A ⊓ ZQ z : Subgroup G) =
      (Nat.card (QaInterImage S A) * Nat.card (ZQ z)) *
        Nat.card (A ⊓ ZQ z : Subgroup G) := by
    rw [hsup, ← himg]
    ring
  exact Nat.mul_right_cancel hpos h

theorem exists_mem_centerIn_inf_H_of_mem_Rbar (S : Setting z E F) {a : G} {r : Hbar z}
    (hr : r ∈ Rbar S a) (hr1 : r ≠ 1) :
    ∃ s : ↥(H z), (s : G) ∈ centerIn (QaOf a) ∧ (s : G) ∈ H z ∧
      (s : G) ∉ Q z ∧ QuotientGroup.mk s = r := by
  rw [← map_R0_eq_Rbar S a] at hr
  obtain ⟨s, hs, hsr⟩ := Subgroup.mem_map.mp hr
  have hsZ : (s : G) ∈ centerIn (QaOf a) :=
    (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hs)).1
  have hsH : (s : G) ∈ H z :=
    (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hs)).2
  refine ⟨s, hsZ, hsH, ?_, ?_⟩
  · intro hsQ
    apply hr1
    rw [← hsr, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact Subgroup.mem_subgroupOf.mpr hsQ
  · simpa [QuotientGroup.mk'_apply] using hsr

theorem isA2Q_of_mem_centerIn_H (S : Setting z E F) {a s : G}
    (haQ : a ∈ Q z) (hconj : IsConj z a) (haZ : a ∉ ZQ z)
    (hzaZ : z ∉ centerIn (QaOf a))
    (hsZ : s ∈ centerIn (QaOf a)) (hsH : s ∈ H z)
    (hs2 : s ^ 2 = 1) (hsQ : s ∉ Q z) :
    IsA2Q S s := by
  let A : Subgroup G := ⁅Q z, Subgroup.zpowers s⁆
  have hA : A ≤ Q z := by
    rw [show A = Subgroup.closure {g : G | ∃ q ∈ Q z, ⁅q, s⁆ = g} from
      commutator_zpowers_eq_closure_commutator hs2]
    rw [Subgroup.closure_le]
    rintro g ⟨q, hq, rfl⟩
    exact commutator_mem_Q_of_mem_H hsH hq
  have hcard := card_sup_ZQ_eq_card_QaInterImage_mul S A hA
  rw [show QaInterImage S A = commSpace (conjQbar S ⟨s, hsH⟩) from
      QaInterImage_commutator_eq_commSpace S hsH hs2,
    card_commSpace_eq_four S haQ hconj haZ hzaZ hsZ hsH hs2 hsQ] at hcard
  exact ⟨hsH, hsQ, by rw [hs2]; exact (Q z).one_mem,
    hcard, isElemAbelian_commutator_zpowers S haQ hzaZ hsZ hsH hs2⟩

theorem isA2Hbar_of_mem_Rbar (S : Setting z E F) {a : G}
    (haQ : a ∈ Q z) (hconj : IsConj z a) (haZ : a ∉ ZQ z)
    (hza : z ∈ QaOf a)
    (hZQa : ¬ centerIn (QaOf a) ≤ Q z) :
    ∀ r ∈ Rbar S a, r ≠ 1 → IsA2Hbar S r := by
  intro r hr hr1
  obtain ⟨s, hsZ, hsH, hsQ, hsr⟩ :=
    exists_mem_centerIn_inf_H_of_mem_Rbar S hr hr1
  have hzaZ : z ∉ centerIn (QaOf a) :=
    z_not_mem_centerIn_Qa S haQ hconj haZ hza
  have hs2 : (s : G) ^ 2 = 1 := sq_eq_one_of_mem_centerIn_QaOf S hconj hsZ
  exact ⟨s, hsr, isA2Q_of_mem_centerIn_H S haQ hconj haZ hzaZ hsZ hsH hs2 hsQ⟩

end CFSG.RankThree.GF2n.Stroth78
