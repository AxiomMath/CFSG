module

public import CFSG.RankThree.GF2n.Smith81.TiRecognition

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.GH74.GLS.Bg.TwoGroups CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n
  CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement

section UT3

variable (F : Type*) [CommRing F]

def ut3SubA : Subgroup (UT3 F) where
  carrier := {x | x.a = 0}
  mul_mem' := by
    intro x y hx hy
    show x.a + y.a = 0
    rw [show x.a = 0 from hx, show y.a = 0 from hy, add_zero]
  one_mem' := rfl
  inv_mem' := by
    intro x hx
    show -x.a = 0
    rw [show x.a = 0 from hx, neg_zero]

def ut3SubB : Subgroup (UT3 F) where
  carrier := {x | x.b = 0}
  mul_mem' := by
    intro x y hx hy
    show x.b + y.b = 0
    rw [show x.b = 0 from hx, show y.b = 0 from hy, add_zero]
  one_mem' := rfl
  inv_mem' := by
    intro x hx
    show -x.b = 0
    rw [show x.b = 0 from hx, neg_zero]

variable {F}

theorem mem_ut3SubA {x : UT3 F} : x ∈ ut3SubA F ↔ x.a = 0 := Iff.rfl

theorem mem_ut3SubB {x : UT3 F} : x ∈ ut3SubB F ↔ x.b = 0 := Iff.rfl

theorem ut3_sq_eq_one_iff [CharP F 2] {x : UT3 F} : x * x = 1 ↔ x.a * x.b = 0 := by
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  constructor
  · intro h
    have hc := congrArg UT3.c h
    simp only [UT3.mul_def, UT3.one_def] at hc
    linear_combination hc - x.c * h2
  · intro h
    ext
    · show x.a + x.a = 0
      linear_combination x.a * h2
    · show x.b + x.b = 0
      linear_combination x.b * h2
    · show x.c + x.c + x.a * x.b = 0
      linear_combination x.c * h2 + h

theorem ut3_le_sub [CharP F 2] [IsDomain F] (P : Subgroup (UT3 F)) (hP : ∀ x ∈ P, x * x = 1) :
    P ≤ ut3SubA F ∨ P ≤ ut3SubB F := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hA, hB⟩ := hcon
  obtain ⟨x, hxP, hxA⟩ := SetLike.not_le_iff_exists.mp hA
  obtain ⟨y, hyP, hyB⟩ := SetLike.not_le_iff_exists.mp hB
  have hxa : x.a ≠ 0 := hxA
  have hyb : y.b ≠ 0 := hyB
  have hxb : x.b = 0 := by
    have := ut3_sq_eq_one_iff.mp (hP x hxP)
    exact (mul_eq_zero.mp this).resolve_left hxa
  have hya : y.a = 0 := by
    have := ut3_sq_eq_one_iff.mp (hP y hyP)
    exact (mul_eq_zero.mp this).resolve_right hyb
  have hxy := ut3_sq_eq_one_iff.mp (hP (x * y) (P.mul_mem hxP hyP))
  have : (x * y).a * (x * y).b = x.a * y.b := by
    simp [UT3.mul_def, hxb, hya]
  rw [this] at hxy
  exact mul_ne_zero hxa hyb hxy

end UT3

section Transport

variable {G : Type} [Group G] {Q : Subgroup G} {F : Type*} [Field F]

@[expose] def QSubOf (e : ↥Q ≃* UT3 F) (S : Subgroup (UT3 F)) : Subgroup G :=
  (S.map e.symm.toMonoidHom).map Q.subtype

theorem mem_QSubOf {e : ↥Q ≃* UT3 F} {S : Subgroup (UT3 F)} {x : G} :
    x ∈ QSubOf e S ↔ ∃ h : x ∈ Q, e ⟨x, h⟩ ∈ S := by
  constructor
  · rintro ⟨y, ⟨u, hu, rfl⟩, rfl⟩
    refine ⟨(e.symm u).2, ?_⟩
    simpa using hu
  · rintro ⟨h, hS⟩
    refine ⟨e.symm (e ⟨x, h⟩), ⟨e ⟨x, h⟩, hS, rfl⟩, ?_⟩
    simp

theorem QSubOf_le (e : ↥Q ≃* UT3 F) (S : Subgroup (UT3 F)) : QSubOf e S ≤ Q :=
  Subgroup.map_subtype_le _

theorem card_QSubOf (e : ↥Q ≃* UT3 F) (S : Subgroup (UT3 F)) :
    Nat.card (QSubOf e S) = Nat.card S := by
  unfold QSubOf
  rw [Subgroup.card_map_of_injective Q.subtype_injective,
    Subgroup.card_map_of_injective e.symm.injective]

theorem le_QSubOf (e : ↥Q ≃* UT3 F) {S : Subgroup (UT3 F)} {A : Subgroup G} (hAQ : A ≤ Q)
    (h : (A.subgroupOf Q).map e.toMonoidHom ≤ S) : A ≤ QSubOf e S := by
  intro x hx
  refine mem_QSubOf.mpr ⟨hAQ hx, h ⟨⟨x, hAQ hx⟩, hx, rfl⟩⟩

end Transport

section Perm

variable {G : Type} [Group G] [Finite G] {M Q Z : Subgroup G}
  {F : Type} [Field F] [CharP F 2] [Finite F]

theorem card_ut3SubA : Nat.card (ut3SubA F) = Nat.card F ^ 2 := by
  have e : ut3SubA F ≃ F × F :=
    { toFun := fun u => (u.1.b, u.1.c)
      invFun := fun p => ⟨⟨0, p.1, p.2⟩, rfl⟩
      left_inv := fun u => Subtype.ext (UT3.ext u.2.symm rfl rfl)
      right_inv := fun p => rfl }
  rw [Nat.card_congr e, Nat.card_prod]
  ring

theorem card_ut3SubB : Nat.card (ut3SubB F) = Nat.card F ^ 2 := by
  have e : ut3SubB F ≃ F × F :=
    { toFun := fun u => (u.1.a, u.1.c)
      invFun := fun p => ⟨⟨p.1, 0, p.2⟩, rfl⟩
      left_inv := fun u => Subtype.ext (UT3.ext rfl u.2.symm rfl)
      right_inv := fun p => rfl }
  rw [Nat.card_congr e, Nat.card_prod]
  ring

theorem Z_le_QSubOf (H : StrothHyp M Q Z) (e : ↥Q ≃* UT3 F) {S : Subgroup (UT3 F)}
    (hS : ∀ u : UT3 F, u.a = 0 → u.b = 0 → u ∈ S) : Z ≤ QSubOf e S := by
  intro z hz
  rw [H.hZ] at hz
  obtain ⟨y, hy, rfl⟩ := hz
  refine mem_QSubOf.mpr ⟨y.2, ?_⟩
  have hey : e y ∈ Subgroup.center (UT3 F) := by
    refine Subgroup.mem_center_iff.mpr fun g => ?_
    obtain ⟨y', rfl⟩ := e.surjective g
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hy y']
  obtain ⟨ha, hb⟩ := (Tim79.ut3_mem_center_iff _).mp hey
  exact hS _ ha hb

theorem eq_QSubOf_of_elem (e : ↥Q ≃* UT3 F) {A : Subgroup G} (hAQ : A ≤ Q)
    (hA2 : ∀ x ∈ A, x * x = 1) (hAc : Nat.card A = Nat.card F ^ 2) :
    A = QSubOf e (ut3SubA F) ∨ A = QSubOf e (ut3SubB F) := by
  have hF : IsDomain F := inferInstance
  have hA' : ∀ u ∈ (A.subgroupOf Q).map e.toMonoidHom, u * u = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    have hx2 : x * x = 1 := Subtype.ext (hA2 x hx)
    rw [← map_mul]
    show e (x * x) = 1
    rw [hx2, map_one]
  rcases ut3_le_sub _ hA' with h | h
  · left
    exact Subgroup.eq_of_le_of_card_ge (le_QSubOf e hAQ h)
      (by rw [card_QSubOf, card_ut3SubA, hAc])
  · right
    exact Subgroup.eq_of_le_of_card_ge (le_QSubOf e hAQ h)
      (by rw [card_QSubOf, card_ut3SubB, hAc])

@[expose] def IsQPlane (Q : Subgroup G) (F : Type) [Field F] [Finite F] (W : Subgroup G) : Prop :=
  W ≤ Q ∧ (∀ x ∈ W, x * x = 1) ∧ Nat.card W = Nat.card F ^ 2

theorem IsQPlane.conj (H : StrothHyp M Q Z) {m : G} (hm : m ∈ M) {W : Subgroup G}
    (hW : IsQPlane Q F W) : IsQPlane Q F (conjSubgroup m W) := by
  obtain ⟨hWQ, hW2, hWc⟩ := hW
  refine ⟨fun y hy => ?_, fun y hy => ?_, by rw [card_conjSubgroup, hWc]⟩
  · have hy' := mem_conjSubgroup.mp hy
    have := conj_mem_Q H hm (hWQ hy')
    simpa [mul_assoc] using this
  · have hy' := mem_conjSubgroup.mp hy
    have h2 := hW2 _ hy'
    calc y * y = m * ((m⁻¹ * y * m) * (m⁻¹ * y * m)) * m⁻¹ := by group
      _ = 1 := by rw [h2]; group

theorem QSubOf_ne (e : ↥Q ≃* UT3 F) : QSubOf e (ut3SubA F) ≠ QSubOf e (ut3SubB F) := by
  intro h
  have hu : ((e.symm ⟨1, 0, 0⟩ : ↥Q) : G) ∈ QSubOf e (ut3SubB F) :=
    mem_QSubOf.mpr ⟨(e.symm ⟨1, 0, 0⟩).2, by simpa [mem_ut3SubB] using rfl⟩
  rw [← h] at hu
  obtain ⟨h1, h2⟩ := mem_QSubOf.mp hu
  have : e ⟨((e.symm ⟨1, 0, 0⟩ : ↥Q) : G), h1⟩ = ⟨1, 0, 0⟩ := by simp
  rw [this] at h2
  exact one_ne_zero (mem_ut3SubA.mp h2)

theorem Q_le_normalizer_QSubOf (H : StrothHyp M Q Z) (e : ↥Q ≃* UT3 F) {S : Subgroup (UT3 F)}
    (hS : ∀ u : UT3 F, u.a = 0 → u.b = 0 → u ∈ S) :
    Q ≤ Subgroup.normalizer ((QSubOf e S : Subgroup G) : Set G) := by
  intro q hq
  refine Subgroup.mem_normalizer_fintype fun a ha => ?_
  have hcomm : ⁅q, a⁆ ∈ Z := comm_mem_Z H hq (QSubOf_le e S ha)
  have : q * a * q⁻¹ = ⁅q, a⁆ * a := by simp only [commutatorElement_def]; group
  rw [this]
  exact (QSubOf e S).mul_mem (Z_le_QSubOf H e hS hcomm) ha

theorem Q_le_normalizer_of_plane (H : StrothHyp M Q Z) (e : ↥Q ≃* UT3 F) {W : Subgroup G}
    (hW : IsQPlane Q F W) : Q ≤ Subgroup.normalizer (W : Set G) := by
  have hSa : ∀ u : UT3 F, u.a = 0 → u.b = 0 → u ∈ ut3SubA F := fun u ha _ => ha
  have hSb : ∀ u : UT3 F, u.a = 0 → u.b = 0 → u ∈ ut3SubB F := fun u _ hb => hb
  rcases eq_QSubOf_of_elem e hW.1 hW.2.1 hW.2.2 with h | h
  · rw [h]; exact Q_le_normalizer_QSubOf H e hSa
  · rw [h]; exact Q_le_normalizer_QSubOf H e hSb

theorem normalizes_plane_of_odd (H : StrothHyp M Q Z) (e : ↥Q ≃* UT3 F) {r : ℕ} (hr : Odd r)
    (hodd : ∀ m ∈ M, m ^ r ∈ Q) {W : Subgroup G} (hW : IsQPlane Q F W) :
    M ≤ Subgroup.normalizer (W : Set G) := by
  intro m hm
  rw [← conjSubgroup_eq_self_iff]
  by_contra hne
  have hinj : ∀ X Y : Subgroup G, conjSubgroup m X = conjSubgroup m Y → X = Y := fun X Y h =>
    Subgroup.map_injective (MulAut.conj m).injective h
  have hAab := QSubOf_ne e
  have hcases : ∀ X : Subgroup G, IsQPlane Q F X → X = QSubOf e (ut3SubA F) ∨
      X = QSubOf e (ut3SubB F) := fun X hX => eq_QSubOf_of_elem e hX.1 hX.2.1 hX.2.2
  set X₁ := conjSubgroup m W with hX₁
  set X₂ := conjSubgroup m X₁ with hX₂
  have hX₁P : IsQPlane Q F X₁ := hW.conj H hm
  have hX₂P : IsQPlane Q F X₂ := hX₁P.conj H hm
  have h12 : X₂ ≠ X₁ := by
    intro h
    exact hne (hinj _ _ (by rw [← hX₂, h]) |>.symm)
  have hX₂W : X₂ = W := by
    rcases hcases W hW with h0 | h0 <;> rcases hcases X₁ hX₁P with h1 | h1 <;>
      rcases hcases X₂ hX₂P with h2 | h2
    all_goals first
      | exact h2.trans h0.symm
      | exact absurd (h1.trans h0.symm) hne
      | exact absurd (h2.trans h1.symm) h12
  have hmW : conjSubgroup (m * m) W = W := by
    rw [conjSubgroup_mul]; exact hX₂W
  have hmX : conjSubgroup (m * m) X₁ = X₁ := by
    rw [conjSubgroup_mul, ← hX₂, hX₂W]
  have hpowW : ∀ k : ℕ, conjSubgroup (m ^ (2 * k)) W = W := by
    intro k
    induction k with
    | zero => simp [conjSubgroup_one]
    | succ k ih =>
      rw [show m ^ (2 * (k + 1)) = m ^ (2 * k) * (m * m) by group, conjSubgroup_mul, hmW, ih]
  obtain ⟨k, rfl⟩ := hr
  have h1 : conjSubgroup (m ^ (2 * k + 1)) W = X₁ := by
    rw [pow_succ', conjSubgroup_mul, hpowW k]
  have h2 : conjSubgroup (m ^ (2 * k + 1)) W = W :=
    conjSubgroup_eq_self_iff.mpr (Q_le_normalizer_of_plane H e hW (hodd m hm))
  exact hne (h1.symm.trans h2)

end Perm

section Outer

variable {G : Type} [Group G]

theorem generalizedFitting_eq_top_of_not_outer [Finite G] (hnot : ¬ OuterOnFStar G) :
    generalizedFitting G = ⊤ := by
  rw [eq_top_iff]
  intro g _
  unfold OuterOnFStar at hnot
  push Not at hnot
  obtain ⟨h, hhK, hgh⟩ := hnot g
  have hc : h⁻¹ * g ∈ Subgroup.centralizer (generalizedFitting G : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have := hgh x hx
    calc x * (h⁻¹ * g) = h⁻¹ * (h * x * h⁻¹) * g := by group
      _ = h⁻¹ * (g * x * g⁻¹) * g := by rw [this]
      _ = h⁻¹ * g * x := by group
  have hK := centralizer_generalizedFitting_le G hc
  have : g = h * (h⁻¹ * g) := by group
  rw [this]
  exact (generalizedFitting G).mul_mem hhK hK

theorem exists_odd_pow_mem_Q [Finite G] {M Q Z : Subgroup G}
    (H : StrothHyp M Q Z) {f : ℕ} (hZ : Nat.card Z = 2 ^ f) (hw : Width Q Z 1)
    (hG : (Nat.card G).factorization 2 = 3 * f) :
    ∃ r : ℕ, Odd r ∧ ∀ m ∈ M, m ^ r ∈ Q := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI hN : (Q.subgroupOf M).Normal := Subgroup.normal_subgroupOf_of_le_normalizer H.Q_normal.2
  have hQM : Q ≤ M := H.Q_normal.1
  refine ⟨(Q.subgroupOf M).index, ?_, fun m hm => ?_⟩
  · obtain ⟨S⟩ : Nonempty (Sylow 2 M) := inferInstance
    obtain ⟨T, hT⟩ := H.isSylow_of_sylow_M S
    have hcard : Nat.card (T : Subgroup G) = Nat.card (S : Subgroup M) := by
      rw [hT]
      exact Subgroup.card_map_of_injective M.subtype_injective
    have hS := Sylow.card_eq_multiplicity S
    have hT' := Sylow.card_eq_multiplicity T
    have hv : (Nat.card M).factorization 2 = 3 * f := by
      have : 2 ^ (Nat.card M).factorization 2 = 2 ^ (Nat.card G).factorization 2 := by
        rw [← hS, ← hT']
        exact hcard.symm
      rw [← hG]
      exact Nat.pow_right_injective (le_refl 2) this
    have hmul := Subgroup.card_mul_index (Q.subgroupOf M)
    have hQcard : Nat.card (Q.subgroupOf M) = 2 ^ (3 * f) := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQM).toEquiv]
      have : Nat.card Q = Nat.card Z ^ 3 := hw
      rw [this, hZ, ← pow_mul, mul_comm]
    rw [hQcard] at hmul
    have hMne : Nat.card M ≠ 0 := Nat.card_pos.ne'
    have hrne : (Q.subgroupOf M).index ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hmul
      exact hMne hmul.symm
    have hfac : (Nat.card M).factorization 2 =
        3 * f + ((Q.subgroupOf M).index).factorization 2 := by
      rw [← hmul, Nat.factorization_mul (by positivity) hrne, Finsupp.add_apply,
        Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same]
    have h0 : ((Q.subgroupOf M).index).factorization 2 = 0 := by omega
    have hndvd : ¬ 2 ∣ (Q.subgroupOf M).index := by
      intro hd
      have := (Nat.Prime.dvd_iff_one_le_factorization Nat.prime_two hrne).mp hd
      omega
    exact Nat.odd_iff.mpr (by omega)
  · have := Subgroup.pow_index_mem (Q.subgroupOf M) ⟨m, hm⟩
    simpa using Subgroup.mem_subgroupOf.mp this

end Outer

section Final

variable {G : Type} [Group G] [Finite G] {M Q Z : Subgroup G}

theorem card_UT3 {F : Type*} [CommRing F] [Finite F] :
    Nat.card (CFSG.GH74.GLS.Bg.TwoGroups.UT3 F) = Nat.card F ^ 3 := by
  have e : CFSG.GH74.GLS.Bg.TwoGroups.UT3 F ≃ F × F × F :=
    { toFun := fun u => (u.a, u.b, u.c)
      invFun := fun p => ⟨p.1, p.2.1, p.2.2⟩
      left_inv := fun u => rfl
      right_inv := fun p => rfl }
  rw [Nat.card_congr e, Nat.card_prod, Nat.card_prod]
  ring

theorem width_of_caseD1 (H : StrothHyp M Q Z) {n : ℕ} (h : CaseD1 Q Z n) :
    Nat.card Z = 2 ^ n ∧ Width Q Z 1 := by
  obtain ⟨hZ, ⟨e⟩⟩ := h
  refine ⟨hZ, ?_⟩
  have hn0 : n ≠ 0 := by
    rintro rfl
    have := H.q4
    rw [hZ] at this
    simp at this
  unfold Width
  rw [Nat.card_congr e.toEquiv, card_UT3, GaloisField.card 2 n hn0, hZ]

theorem outerOnFStar_of_psl3 (hOrd : TiLieOrders) (H : StrothHyp M Q Z) {n : ℕ}
    (hn : CaseD1 Q Z n) {f : ℕ} (hf : Nat.card Z = 2 ^ f)
    (hL : CFSG.Blueprint.LieModel (FStar G) .PSL 3 2 f) : OuterOnFStar G := by
  by_contra hnot
  have hK := generalizedFitting_eq_top_of_not_outer hnot
  have hFG : Nat.card (FStar G) = Nat.card G := by
    show Nat.card ↥(generalizedFitting G) = _
    rw [hK]
    exact Subgroup.card_top
  have hG2 : (Nat.card G).factorization 2 = 3 * f := by
    rw [← hFG]
    exact hOrd.1 _ f hL
  obtain ⟨hZ, hw⟩ := width_of_caseD1 H hn
  have hfn : f = n := Nat.pow_right_injective (le_refl 2) (hf.symm.trans hZ)
  obtain ⟨r, hr, hodd⟩ := exists_odd_pow_mem_Q H hf hw hG2
  obtain ⟨-, ⟨e⟩⟩ := hn
  obtain ⟨B, hc⟩ := exists_ctx_of_strothHyp H
  obtain ⟨g, hg⟩ := hc.conj
  subst hg
  have hgZ : conjSubgroup g Z ≠ Z := hc.ne
  have hgQ : conjSubgroup g Z ≤ Q := hc.le
  have hh := H.toHyp79.toHyp218 hgZ hgQ
  obtain ⟨y, hy⟩ := hh.exists_isOpp
  obtain ⟨x, hxW, hxV⟩ := hh.exists_conj_eq_V1 hy
  have hn0 : n ≠ 0 := by
    rintro rfl
    have := H.q4
    rw [hZ] at this
    simp at this
  obtain ⟨n', hn', hind, -⟩ := hc.inducesSL2
  obtain ⟨φ, ψ, -, -, -⟩ := hind
  have hn'n : n' = n := Nat.pow_right_injective (le_refl 2) (hn'.symm.trans hZ)
  subst hn'n
  have hW2 : ∀ w ∈ Z ⊔ conjSubgroup g Z, w * w = 1 := by
    intro w hw
    have h1 : (⟨w, hw⟩ : ↥(Z ⊔ conjSubgroup g Z)) * ⟨w, hw⟩ = 1 := by
      apply ψ.injective
      rw [map_mul, map_one]
      generalize ψ ⟨w, hw⟩ = v
      induction v using Multiplicative.rec with
      | ofAdd v =>
        show Multiplicative.ofAdd v * Multiplicative.ofAdd v = Multiplicative.ofAdd 0
        rw [← ofAdd_add]
        congr 1
        funext i
        simp [CharTwo.add_self_eq_zero]
    exact congrArg Subtype.val h1
  have hWcard : Nat.card ↥(Z ⊔ conjSubgroup g Z) = Nat.card (GaloisField 2 n') ^ 2 := by
    have h2 : Nat.card (Fin 2) = 2 := by simp
    rw [Nat.card_congr ψ.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_fun, h2]
  have hWplane : IsQPlane Q (GaloisField 2 n') (Z ⊔ conjSubgroup g Z) :=
    ⟨sup_le H.Z_normal.1 hgQ, hW2, hWcard⟩
  have hMW := normalizes_plane_of_odd H e hr hodd hWplane
  have hxM : x ∉ M := by
    intro hxM
    have hxZ : conjSubgroup x Z = Z :=
      conjSubgroup_eq_self_iff.mpr (by rw [H.normalizer_Z.1]; exact hxM)
    exact hgZ (hxV ▸ hxZ)
  have hlt : M < Subgroup.normalizer ((Z ⊔ conjSubgroup g Z : Subgroup G) : Set G) :=
    lt_of_le_of_ne hMW (fun h => hxM (h ▸ hxW))
  have hWne : (Z ⊔ conjSubgroup g Z) ≠ ⊥ := by
    intro h
    have hZb : Z ≤ ⊥ := h ▸ le_sup_left
    have := H.q4
    rw [le_bot_iff.mp hZb, Subgroup.card_bot] at this
    omega
  have hW2g : IsPGroup 2 ↥(Z ⊔ conjSubgroup g Z) := fun w =>
    ⟨1, Subtype.ext (by simpa [pow_two] using hW2 w w.2)⟩
  exact H.maxLocal.2 _ hlt ⟨_, hWne, hW2g, rfl⟩

end Final

end CFSG.RankThree.GF2n.Smith81
