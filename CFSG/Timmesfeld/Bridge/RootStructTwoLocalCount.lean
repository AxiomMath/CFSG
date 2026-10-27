module

public import CFSG.Timmesfeld.Bridge.RootStructTwoLocalCore

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld
open scoped Pointwise

theorem two_mul_card_le_of_lt {G : Type*} [Group G] [Finite G] {H K : Subgroup G} (hle : H ≤ K)
    (hne : H ≠ K) : 2 * Nat.card H ≤ Nat.card K := by
  obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le hle
  have hK : 0 < Nat.card K := Nat.card_pos
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hm
    omega
  have hm1 : m ≠ 1 := by
    rintro rfl
    rw [mul_one] at hm
    exact hne (Subgroup.eq_of_le_of_card_ge hle hm.le)
  rw [hm, mul_comm]
  exact Nat.mul_le_mul_left _ (by omega)

namespace TwoLocalSetting

variable {G : Type*} [Group G] {D : Set G} (S : TwoLocalSetting G D)
include S

theorem line_mul_eq {a x : G} (ha : a ∈ D) (hx : x ∈ D) (haxD : a * x ∈ D) :
    rootGroup D a ⊔ rootGroup D (a * x) = rootGroup D a ⊔ rootGroup D x := by
  have hD := S.root
  rw [S.line_eq ha haxD, S.line_eq ha hx]
  refine le_antisymm (Subgroup.closure_le _ |>.2 ?_) (Subgroup.closure_le _ |>.2 ?_)
  · rintro y (hy | hy) <;> rw [hy]
    · exact Subgroup.subset_closure (Set.mem_insert _ _)
    · exact Subgroup.mul_mem _ (Subgroup.subset_closure (Set.mem_insert _ _))
        (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))
  · rintro y (hy | hy) <;> rw [hy]
    · exact Subgroup.subset_closure (Set.mem_insert _ _)
    · have hm : a * (a * x) ∈ Subgroup.closure ({a, a * x} : Set G) :=
        Subgroup.mul_mem _ (Subgroup.subset_closure (Set.mem_insert _ _))
          (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))
      rwa [← mul_assoc, hD.mul_self_eq_one ha, one_mul] at hm

theorem mem_rootLines_iff {a : G} (ha : a ∈ D) {L : Subgroup G} :
    L ∈ rootLines D a ↔ ∃ x ∈ D, Commute a x ∧ x ≠ a ∧ L = rootGroup D a ⊔ rootGroup D x := by
  constructor
  · rintro ⟨x, hx, hax, -, hxT, rfl⟩
    refine ⟨x, hx, hax, fun h => hxT ?_, rfl⟩
    rw [S.sing a ha, h]
    rfl
  · rintro ⟨x, hx, hax, hxa, rfl⟩
    refine ⟨x, hx, hax, S.mul_mem_of_commute ha hx hax (Ne.symm hxa), ?_, rfl⟩
    rw [S.sing a ha]
    exact hxa

theorem exists_transversal {a : G} (ha : a ∈ D) :
    ∃ P : Finset G, P.card = (rootLines D a).ncard ∧ (∀ x ∈ P, x ∈ D ∧ Commute a x ∧ x ≠ a) ∧
      (∀ x ∈ P, ∀ y ∈ P, x ≠ y → ¬ Commute x y) ∧
      ∀ x ∈ D, Commute a x → x ≠ a → x ∈ P ∨ a * x ∈ P := by
  classical
  have := S.hyp.finite
  have hD := S.root
  have hfin : (rootLines D a).Finite := Set.toFinite _
  have hch : ∀ L ∈ rootLines D a,
      ∃ x ∈ D, Commute a x ∧ x ≠ a ∧ L = rootGroup D a ⊔ rootGroup D x :=
    fun L hL => (S.mem_rootLines_iff ha).1 hL
  let f : Subgroup G → G := fun L => if h : L ∈ rootLines D a then (hch L h).choose else 1
  have hf : ∀ L ∈ rootLines D a, f L ∈ D ∧ Commute a (f L) ∧ f L ≠ a ∧
      L = rootGroup D a ⊔ rootGroup D (f L) := by
    intro L hL
    simp only [f, hL, ↓reduceDIte]
    exact (hch L hL).choose_spec
  have hinj : Set.InjOn f (rootLines D a) := by
    intro L hL L' hL' h
    rw [(hf L hL).2.2.2, (hf L' hL').2.2.2, h]
  refine ⟨hfin.toFinset.image f, ?_, ?_, ?_, ?_⟩
  · rw [Finset.card_image_of_injOn (by simpa using hinj), Set.ncard_eq_toFinset_card _ hfin]
  · intro x hx
    obtain ⟨L, hL, rfl⟩ := Finset.mem_image.1 hx
    exact ⟨(hf L (by simpa using hL)).1, (hf L (by simpa using hL)).2.1,
      (hf L (by simpa using hL)).2.2.1⟩
  · intro x hx y hy hxy hc
    obtain ⟨L, hL, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨L', hL', rfl⟩ := Finset.mem_image.1 hy
    have hL₁ := hf L (by simpa using hL)
    have hL₂ := hf L' (by simpa using hL')
    apply hxy
    congr 1
    rw [hL₁.2.2.2, hL₂.2.2.2]
    rcases (S.commute_iff_eq_or_eq_mul ha hL₁.1 hL₂.1 hL₁.2.1 hL₂.2.1 hL₁.2.2.1 hL₂.2.2.1).1 hc
      with h | h
    · rw [h]
    · rw [h, S.line_mul_eq ha hL₁.1 (S.mul_mem_of_commute ha hL₁.1 hL₁.2.1
        (Ne.symm hL₁.2.2.1))]
  · intro x hx hax hxa
    have hL : rootGroup D a ⊔ rootGroup D x ∈ rootLines D a :=
      (S.mem_rootLines_iff ha).2 ⟨x, hx, hax, hxa, rfl⟩
    obtain ⟨hy, hay, hya, hLy⟩ := hf _ hL
    have hmem : x ∈ rootGroup D a ⊔ rootGroup D (f (rootGroup D a ⊔ rootGroup D x)) := by
      rw [← hLy]
      exact Subgroup.mem_sup_right (rootSet_subset_rootGroup D x (mem_rootSet_self hx))
    have hPy : f (rootGroup D a ⊔ rootGroup D x) ∈ hfin.toFinset.image f :=
      Finset.mem_image_of_mem f (by simpa using hL)
    rcases (S.mem_line_iff ha hy hay hx).1 hmem with h | h | h
    · exact absurd h hxa
    · exact Or.inl (h ▸ hPy)
    · right
      rw [h, ← mul_assoc, hD.mul_self_eq_one ha, one_mul]
      exact hPy

theorem ncard_collinearSet {a : G} (ha : a ∈ D) :
    (Moufang.collinearSet D a).ncard = 2 * (rootLines D a).ncard := by
  classical
  have hD := S.root
  obtain ⟨P, hPk, hP, hnc, hcov⟩ := S.exists_transversal ha
  have e : Moufang.collinearSet D a = ((P ∪ P.image (a * ·) : Finset G) : Set G) := by
    rw [S.collinearSet_eq ha]
    ext x
    simp only [Set.mem_ofPred_eq, Finset.coe_union, Finset.coe_image, Set.mem_union,
      Finset.mem_coe, Set.mem_image]
    constructor
    · rintro ⟨hx, hax, hxa⟩
      rcases hcov x hx hax hxa with h | h
      · exact Or.inl h
      · exact Or.inr ⟨a * x, h, by rw [← mul_assoc, hD.mul_self_eq_one ha, one_mul]⟩
    · rintro (h | ⟨y, hy, rfl⟩)
      · exact hP x h
      · obtain ⟨hyD, hay, hya⟩ := hP y hy
        refine ⟨S.mul_mem_of_commute ha hyD hay (Ne.symm hya), (Commute.refl a).mul_right hay,
          fun h => hD.ne_one hyD ?_⟩
        have := congrArg (a⁻¹ * ·) h
        simpa using this
  have hdisj : Disjoint P (P.image (a * ·)) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hx'
    have hne : a * y ≠ y := fun h => hD.ne_one ha (by simpa using h)
    exact hnc _ hx y hy hne ((hP y hy).2.1.mul_left (Commute.refl y))
  rw [e, Set.ncard_coe_finset,
    Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injective _ (mul_right_injective a),
    hPk, two_mul]

theorem nCore_eq_closure_insert {a : G} (ha : a ∈ D) {P : Finset G}
    (hP : ∀ x ∈ P, x ∈ D ∧ Commute a x ∧ x ≠ a)
    (hcov : ∀ x ∈ D, Commute a x → x ≠ a → x ∈ P ∨ a * x ∈ P) :
    nCore D a = Subgroup.closure (insert a (P : Set G)) := by
  have hD := S.root
  refine le_antisymm ?_ ?_
  · rw [S.nCore_eq ha, Subgroup.closure_le]
    rintro x ⟨hx, hxa⟩
    have haS : a ∈ Subgroup.closure (insert a (P : Set G)) :=
      Subgroup.subset_closure (Set.mem_insert _ _)
    by_cases hxa' : x = a
    · rw [hxa']
      exact haS
    rcases hcov x hx hxa.symm hxa' with h | h
    · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ h)
    · have hm := Subgroup.mul_mem _ haS (Subgroup.subset_closure (Set.mem_insert_of_mem _ h))
      rwa [← mul_assoc, hD.mul_self_eq_one ha, one_mul] at hm
  · rw [Subgroup.closure_le]
    rintro x (rfl | hx)
    · exact S.self_mem ha
    · exact S.mem_nCore ha (hP x hx).1 (hP x hx).2.1.symm

theorem card_closure_insert_le [Finite G] {a : G} (ha : a ∈ D) (F : Finset G)
    (hF : ∀ x ∈ F, x ∈ nCore D a ∧ x * x = 1) :
    Nat.card (Subgroup.closure (insert a (F : Set G))) ≤ 2 ^ (F.card + 1) := by
  classical
  have hD := S.root
  induction F using Finset.induction_on with
  | empty =>
    rw [Finset.coe_empty, Finset.card_empty, zero_add, pow_one, insert_empty_eq,
      ← Subgroup.zpowers_eq_closure, Nat.card_zpowers, hD.orderOf_eq_two ha]
  | insert x F hxF ih =>
    have ih' := ih fun y hy => hF y (Finset.mem_insert_of_mem hy)
    obtain ⟨hxM, hxx⟩ := hF x (Finset.mem_insert_self x F)
    set N := Subgroup.closure (insert a (F : Set G))
    have hNM : N ≤ nCore D a := by
      rw [Subgroup.closure_le]
      rintro y (rfl | hy)
      · exact S.self_mem ha
      · exact (hF y (Finset.mem_insert_of_mem hy)).1
    have hconj : ∀ h ∈ N, x * h * x⁻¹ ∈ N := by
      intro h hh
      induction hh using Subgroup.closure_induction with
      | mem y hy =>
        have hyM : y ∈ nCore D a := hNM (Subgroup.subset_closure hy)
        have e : x * y * x⁻¹ = (x * y * x⁻¹ * y⁻¹) * y := by group
        rw [e]
        refine N.mul_mem ?_ (Subgroup.subset_closure hy)
        rcases S.commutator_eq ha hxM hyM with hc | hc <;> rw [hc]
        · exact N.one_mem
        · exact Subgroup.subset_closure (Set.mem_insert _ _)
      | one => simp [N.one_mem]
      | mul y z _ _ ihy ihz =>
        rw [show x * (y * z) * x⁻¹ = x * y * x⁻¹ * (x * z * x⁻¹) by group]
        exact N.mul_mem ihy ihz
      | inv y _ ihy =>
        rw [show x * y⁻¹ * x⁻¹ = (x * y * x⁻¹)⁻¹ by group]
        exact N.inv_mem ihy
    have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hxx
    have hnorm : Subgroup.zpowers x ≤ Subgroup.normalizer (N : Set G) := by
      rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
      intro h
      refine ⟨hconj h, fun hh => ?_⟩
      have := hconj _ hh
      have e : x * (x * h * x⁻¹) * x⁻¹ = h := by
        rw [hxinv, ← mul_assoc, ← mul_assoc, hxx, one_mul, mul_assoc, hxx, mul_one]
      rwa [e] at this
    have hcl : Subgroup.closure (insert a ((insert x F : Finset G) : Set G)) =
        N ⊔ Subgroup.zpowers x := by
      rw [Finset.coe_insert, Set.insert_comm, Set.insert_eq, Subgroup.closure_union, sup_comm,
        ← Subgroup.zpowers_eq_closure]
    have hcard : Nat.card (N ⊔ Subgroup.zpowers x : Subgroup G) ≤
        Nat.card N * Nat.card (Subgroup.zpowers x) := by
      have e := Subgroup.coe_mul_of_right_le_normalizer_left N (Subgroup.zpowers x) hnorm
      calc Nat.card (N ⊔ Subgroup.zpowers x : Subgroup G)
          = Nat.card ((N : Set G) * (Subgroup.zpowers x : Set G)) := by
            rw [← e]
            rfl
        _ ≤ Nat.card (N : Set G) * Nat.card (Subgroup.zpowers x : Set G) := Set.natCard_mul_le
        _ = Nat.card N * Nat.card (Subgroup.zpowers x) := rfl
    have hx2 : Nat.card (Subgroup.zpowers x) ≤ 2 := by
      rw [Nat.card_zpowers]
      exact Nat.le_of_dvd two_pos (orderOf_dvd_of_pow_eq_one (by rw [sq, hxx]))
    rw [hcl, Finset.card_insert_of_notMem hxF, pow_succ]
    calc Nat.card (N ⊔ Subgroup.zpowers x : Subgroup G)
        ≤ Nat.card N * Nat.card (Subgroup.zpowers x) := hcard
      _ ≤ 2 ^ (F.card + 1) * 2 := Nat.mul_le_mul ih' hx2

theorem card_nCore_le {a : G} (ha : a ∈ D) :
    Nat.card (nCore D a) ≤ 2 ^ ((rootLines D a).ncard + 1) := by
  have := S.hyp.finite
  have hD := S.root
  obtain ⟨P, hPk, hP, -, hcov⟩ := S.exists_transversal ha
  rw [S.nCore_eq_closure_insert ha hP hcov, ← hPk]
  exact S.card_closure_insert_le ha P fun x hx =>
    ⟨S.mem_nCore ha (hP x hx).1 (hP x hx).2.1.symm, hD.mul_self_eq_one (hP x hx).1⟩

theorem two_pow_mul_card_centralizer_le [DecidableEq G] {a : G} (ha : a ∈ D) {P : Finset G}
    (hP : ∀ x ∈ P, x ∈ D ∧ Commute a x ∧ x ≠ a) (hnc : ∀ x ∈ P, ∀ y ∈ P, x ≠ y → ¬ Commute x y)
    {x₀ : G} (hx₀ : x₀ ∈ P) (F : Finset G) (hF : F ⊆ P.erase x₀) :
    2 ^ F.card * Nat.card ↥(nCore D a ⊓ Subgroup.centralizer (F : Set G)) ≤
      Nat.card (nCore D a) := by
  classical
  have := S.hyp.finite
  have hM : ∀ x ∈ P, x ∈ nCore D a := fun x hx =>
    S.mem_nCore ha (hP x hx).1 (hP x hx).2.1.symm
  induction F using Finset.induction_on with
  | empty =>
    have e : nCore D a ⊓ Subgroup.centralizer ((∅ : Finset G) : Set G) = nCore D a :=
      inf_eq_left.2 fun x _ => Subgroup.mem_centralizer_iff.2 fun _ h => absurd h (by simp)
    rw [e, Finset.card_empty, pow_zero, one_mul]
  | insert x F hxF ih =>
    have hFsub : F ⊆ P.erase x₀ := fun y hy => hF (Finset.mem_insert_of_mem hy)
    have hxP : x ∈ P.erase x₀ := hF (Finset.mem_insert_self x F)
    obtain ⟨hxx₀, hxP'⟩ := Finset.mem_erase.1 hxP
    set K := nCore D a ⊓ Subgroup.centralizer (F : Set G)
    set K' := nCore D a ⊓ Subgroup.centralizer ((insert x F : Finset G) : Set G)
    have hle : K' ≤ K := inf_le_inf_left _
      (Subgroup.centralizer_le (by rw [Finset.coe_insert]; exact Set.subset_insert _ _))
    have hw : x * x₀ ∈ K := by
      refine Subgroup.mem_inf.2 ⟨(nCore D a).mul_mem (hM x hxP') (hM x₀ hx₀), ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hyP : y ∈ P.erase x₀ := hFsub hy
      obtain ⟨hyx₀, hyP'⟩ := Finset.mem_erase.1 hyP
      have hyx : y ≠ x := fun h => hxF (h ▸ hy)
      have key := (S.commute_mul_left_iff ha (hM x hxP') (hM x₀ hx₀) (hM y hyP')).2
        (iff_of_false (hnc x hxP' y hyP' (Ne.symm hyx)) (hnc x₀ hx₀ y hyP' (Ne.symm hyx₀)))
      exact key.eq.symm
    have hw' : x * x₀ ∉ K' := by
      intro h
      have hcx : Commute (x * x₀) x := by
        have := Subgroup.mem_centralizer_iff.1 h.2 x (by simp)
        exact this.symm
      rw [S.commute_mul_left_iff ha (hM x hxP') (hM x₀ hx₀) (hM x hxP')] at hcx
      exact hnc x₀ hx₀ x hxP' (Ne.symm hxx₀) (hcx.1 (Commute.refl x))
    have h2 : 2 * Nat.card K' ≤ Nat.card K :=
      two_mul_card_le_of_lt hle fun h => hw' (h ▸ hw)
    rw [Finset.card_insert_of_notMem hxF, pow_succ]
    calc 2 ^ F.card * 2 * Nat.card K' = 2 ^ F.card * (2 * Nat.card K') := by ring
      _ ≤ 2 ^ F.card * Nat.card K := Nat.mul_le_mul_left _ h2
      _ ≤ Nat.card (nCore D a) := ih hFsub

theorem two_pow_mul_card_center_le {a : G} (ha : a ∈ D) :
    2 ^ ((rootLines D a).ncard - 1) *
        Nat.card ↥(nCore D a ⊓ Subgroup.centralizer (nCore D a : Set G)) ≤
      Nat.card (nCore D a) := by
  classical
  have := S.hyp.finite
  obtain ⟨P, hPk, hP, hnc, hcov⟩ := S.exists_transversal ha
  rcases P.eq_empty_or_nonempty with hPe | ⟨x₀, hx₀⟩
  · rw [← hPk, hPe, Finset.card_empty, Nat.zero_sub, pow_zero, one_mul]
    exact Subgroup.card_le_of_le inf_le_left
  have hle : nCore D a ⊓ Subgroup.centralizer (nCore D a : Set G) ≤
      nCore D a ⊓ Subgroup.centralizer ((P.erase x₀ : Finset G) : Set G) := by
    refine inf_le_inf_left _ (Subgroup.centralizer_le ?_)
    intro y hy
    obtain ⟨-, hyP⟩ := Finset.mem_erase.1 hy
    exact S.mem_nCore ha (hP y hyP).1 (hP y hyP).2.1.symm
  have h := S.two_pow_mul_card_centralizer_le ha hP hnc hx₀ (P.erase x₀) le_rfl
  rw [Finset.card_erase_of_mem hx₀, hPk] at h
  exact (Nat.mul_le_mul_left _ (Subgroup.card_le_of_le hle)).trans h

theorem card_center_le {a : G} (ha : a ∈ D) :
    Nat.card ↥(nCore D a ⊓ Subgroup.centralizer (nCore D a : Set G)) ≤ 4 := by
  have h1 := S.two_pow_mul_card_center_le ha
  have h2 := S.card_nCore_le ha
  set k := (rootLines D a).ncard
  have h3 : 2 ^ (k + 1) ≤ 4 * 2 ^ (k - 1) := by
    rcases Nat.eq_zero_or_pos k with hk | hk
    · rw [hk]
      norm_num
    · rw [show k + 1 = (k - 1) + 2 by omega, pow_add]
      norm_num [mul_comm]
  have hpos : 0 < 2 ^ (k - 1) := by positivity
  by_contra hlt
  push Not at hlt
  have : 2 ^ (k - 1) * 4 < 2 ^ (k - 1) *
      Nat.card ↥(nCore D a ⊓ Subgroup.centralizer (nCore D a : Set G)) :=
    Nat.mul_lt_mul_of_pos_left hlt hpos
  omega

theorem self_mem_center {a : G} (ha : a ∈ D) :
    a ∈ nCore D a ⊓ Subgroup.centralizer (nCore D a : Set G) :=
  ⟨S.self_mem ha, Subgroup.mem_centralizer_iff.2 fun _ hm => (commute_of_mem_nCore hm).eq⟩

theorem conj_eq_or_of_mem_center {a z g : G} (ha : a ∈ D)
    (hz : z ∈ nCore D a ⊓ Subgroup.centralizer (nCore D a : Set G)) (hg : Commute g a) :
    g * z * g⁻¹ = z ∨ g * z * g⁻¹ = a * z := by
  classical
  have := S.hyp.finite
  have hD := S.root
  set Z := nCore D a ⊓ Subgroup.centralizer (nCore D a : Set G)
  have hga : g * a * g⁻¹ = a := by rw [hg.eq, mul_inv_cancel_right]
  have hgZ : g * z * g⁻¹ ∈ Z := by
    refine ⟨conj_mem_nCore S.hyp.isClass hg hz.1, Subgroup.mem_centralizer_iff.2 fun m hm => ?_⟩
    have hm' : g⁻¹ * m * g⁻¹⁻¹ ∈ nCore D a := conj_mem_nCore S.hyp.isClass hg.inv_left hm
    have hc := Subgroup.mem_centralizer_iff.1 hz.2 _ hm'
    calc m * (g * z * g⁻¹) = g * ((g⁻¹ * m * g⁻¹⁻¹) * z) * g⁻¹ := by group
      _ = g * (z * (g⁻¹ * m * g⁻¹⁻¹)) * g⁻¹ := by rw [hc]
      _ = g * z * g⁻¹ * m := by group
  by_cases hz1 : z = 1
  · left
    rw [hz1, mul_one, mul_inv_cancel]
  by_cases hza : z = a
  · left
    rw [hza, hga]
  by_contra hno
  push Not at hno
  set w := g * z * g⁻¹
  have hw1 : w ≠ 1 := fun h => hz1 (by
    have : g⁻¹ * w * g = z := by simp [w, mul_assoc]
    rw [← this, h]
    group)
  have hwa : w ≠ a := fun h => hza (by
    have : g⁻¹ * w * g = z := by simp [w, mul_assoc]
    rw [← this, h, mul_assoc, ← hg.eq, ← mul_assoc, inv_mul_cancel, one_mul])
  have haz1 : a * z ≠ 1 := fun h => hza (by
    have := eq_inv_of_mul_eq_one_right h
    rw [this, hD.inv_eq ha])
  have hT : ({1, a, z, a * z, w} : Finset G).card = 5 := by
    have ha1 : a ≠ 1 := hD.ne_one ha
    have hzaz : z ≠ a * z := fun h => ha1 (by
      have := congrArg (· * z⁻¹) h
      simpa using this.symm)
    have haaz : a ≠ a * z := fun h => hz1 (by
      have := congrArg (a⁻¹ * ·) h
      simpa using this.symm)
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_pair (Ne.symm hno.2)]
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hzaz, Ne.symm hno.1⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨Ne.symm hza, haaz, Ne.symm hwa⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨Ne.symm ha1, Ne.symm hz1, Ne.symm haz1, Ne.symm hw1⟩
  have hsub : (({1, a, z, a * z, w} : Finset G) : Set G) ⊆ (Z : Set G) := by
    intro y hy
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl
    · exact Z.one_mem
    · exact S.self_mem_center ha
    · exact hz
    · exact Z.mul_mem (S.self_mem_center ha) hz
    · exact hgZ
  have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_coe_finset, hT] at hle
  have h4 : (Z : Set G).ncard ≤ 4 := by
    rw [← Nat.card_coe_set_eq]
    exact S.card_center_le ha
  omega

end TwoLocalSetting

end CFSG.Timmesfeld.Bridge
