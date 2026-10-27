module

public import CFSG.Quasithin.EmptyFaithful.S146xB2Two
public import CFSG.Quasithin.EmptyFaithful.S146xB2C2

public section

namespace CFSG.Quasithin

open CFSG.Open
open scoped commutatorElement

section Rank3

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem isElemAbelian_sup_of_commute {A B : Subgroup X} {p : ℕ} (hA : IsElemAbelian p A)
    (hB : IsElemAbelian p B) (hAB : A ≤ Subgroup.centralizer (B : Set X)) :
    IsElemAbelian p (A ⊔ B) := by
  have hAA : A ≤ Subgroup.centralizer (A : Set X) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact congrArg Subtype.val (hA.1.is_comm.comm ⟨y, hy⟩ ⟨x, hx⟩)
  have hBB : B ≤ Subgroup.centralizer (B : Set X) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact congrArg Subtype.val (hB.1.is_comm.comm ⟨y, hy⟩ ⟨x, hx⟩)
  have hC : A ⊔ B ≤ Subgroup.centralizer ((A ⊔ B : Subgroup X) : Set X) := by
    refine sup_le ?_ ?_
    · rw [Subgroup.le_centralizer_iff]
      exact sup_le hAA (Subgroup.le_centralizer_iff.mp hAB)
    · rw [Subgroup.le_centralizer_iff]
      exact sup_le hAB hBB
  refine ⟨⟨⟨fun a b => Subtype.ext ((Subgroup.mem_centralizer_iff.mp (hC b.2)) a a.2)⟩⟩, ?_⟩
  intro x hx
  have hx' : x ∈ ((A ⊔ B : Subgroup X) : Set X) := hx
  rw [Subgroup.coe_mul_of_left_le_normalizer_right A B
    (hAB.trans (Subgroup.centralizer_le_normalizer _))] at hx'
  obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.mp hx'
  have hcomm : Commute a b := ((Subgroup.mem_centralizer_iff.mp (hAB ha)) b hb).symm
  rw [hcomm.mul_pow, hA.2 a ha, hB.2 b hb, one_mul]


theorem le_pRank_of_commute_of_inf_eq_bot' {p : ℕ} (hp : p.Prime) {P Q H : Subgroup X}
    (hP : IsElemAbelian p P) (hQ : IsElemAbelian p Q)
    (hcomm : ∀ x ∈ P, ∀ y ∈ Q, x * y = y * x) (hPQ : P ⊓ Q = ⊥) {a b : ℕ}
    (ha : Nat.card P = p ^ a) (hb : Nat.card Q = p ^ b) (hPH : P ≤ H) (hQH : Q ≤ H) :
    a + b ≤ CFSG.Open.pRank p H := by
  have hPc := hP.1
  have hQc := hQ.1
  have hc : ∀ (x : P) (y : Q), Commute (P.subtype x) (Q.subtype y) := fun x y => hcomm x x.2 y y.2
  let f : P × Q →* X := MonoidHom.noncommCoprod P.subtype Q.subtype hc
  have hf : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    rintro ⟨x, y⟩ hxy
    have hxy' : (x : X) * y = 1 := hxy
    have hyP : (y : X) ∈ P := by
      rw [eq_inv_of_mul_eq_one_right hxy']
      exact P.inv_mem x.2
    have hy1 : (y : X) = 1 := by
      have : (y : X) ∈ P ⊓ Q := ⟨hyP, y.2⟩
      rw [hPQ, Subgroup.mem_bot] at this
      exact this
    rw [hy1, mul_one] at hxy'
    have hx1 : x = 1 := Subtype.ext hxy'
    have hy1' : y = 1 := Subtype.ext hy1
    rw [hx1, hy1']
    rfl
  refine CFSG.SectionRank.le_pRank_of_injective hp.one_lt (A := P × Q) ?_ ?_ ?_ f hf ?_
  · rintro ⟨x₁, y₁⟩ ⟨x₂, y₂⟩
    exact Prod.ext (mul_comm' x₁ x₂) (mul_comm' y₁ y₂)
  · rintro ⟨x, y⟩
    exact Prod.ext (Subtype.ext (hP.2 x x.2)) (Subtype.ext (hQ.2 y y.2))
  · rw [Nat.card_prod, ha, hb, pow_add]
  · rintro _ ⟨⟨x, y⟩, rfl⟩
    exact H.mul_mem (hPH x.2) (hQH y.2)

theorem three_le_pRank_of_three_commuting {K₁ K₂ K₃ : Subgroup X}
    (h12 : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a) (h13 : ∀ a ∈ K₁, ∀ b ∈ K₃, a * b = b * a)
    (h23 : ∀ a ∈ K₂, ∀ b ∈ K₃, a * b = b * a)
    (hZ₁ : ∀ x ∈ K₁, (∀ y ∈ K₁, x * y = y * x) → x = 1)
    (hZ₃ : ∀ x ∈ K₃, (∀ y ∈ K₃, x * y = y * x) → x = 1)
    {x₁ x₂ x₃ : X} (hx₁ : x₁ ∈ K₁) (hx₂ : x₂ ∈ K₂) (hx₃ : x₃ ∈ K₃)
    (ho₁ : orderOf x₁ = 3) (ho₂ : orderOf x₂ = 3) (ho₃ : orderOf x₃ = 3) :
    3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) := by
  classical
  have hcard : ∀ {x : X}, orderOf x = 3 → Nat.card (Subgroup.zpowers x) = 3 := fun {x} ho => by
    rw [Nat.card_zpowers, ho]
  have hel : ∀ {x : X}, orderOf x = 3 → IsElemAbelian 3 (Subgroup.zpowers x) := by
    intro x ho
    refine ⟨inferInstance, fun y hy => ?_⟩
    have hx3 : x ^ 3 = 1 := by rw [← ho]; exact pow_orderOf_eq_one x
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx3, one_zpow]
  set P₁ := Subgroup.zpowers x₁ with hP₁
  set P₂ := Subgroup.zpowers x₂ with hP₂
  set P₃ := Subgroup.zpowers x₃ with hP₃
  have hP₁K : P₁ ≤ K₁ := Subgroup.zpowers_le.mpr hx₁
  have hP₂K : P₂ ≤ K₂ := Subgroup.zpowers_le.mpr hx₂
  have hP₃K : P₃ ≤ K₃ := Subgroup.zpowers_le.mpr hx₃
  have hc12 : ∀ a ∈ P₁, ∀ b ∈ P₂, a * b = b * a := fun a ha b hb => h12 a (hP₁K ha) b (hP₂K hb)
  have hP₁₂ : P₁ ⊓ P₂ = ⊥ := by
    rw [eq_bot_iff]
    rintro z ⟨hz1, hz2⟩
    rw [Subgroup.mem_bot]
    exact hZ₁ z (hP₁K hz1) (fun y hy => (h12 y hy z (hP₂K hz2)).symm)
  have hE₂ : IsElemAbelian 3 (P₁ ⊔ P₂) :=
    isElemAbelian_sup_of_commute (hel ho₁) (hel ho₂)
      (fun a ha => Subgroup.mem_centralizer_iff.mpr fun b hb => (hc12 a ha b hb).symm)
  have hE₂card : Nat.card (P₁ ⊔ P₂ : Subgroup X) = 3 ^ 2 := by
    obtain ⟨hc, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute P₁ P₂ hc12
    rw [hP₁₂, hcard ho₁, hcard ho₂] at hc
    simpa using hc
  have hE₂C : P₁ ⊔ P₂ ≤ Subgroup.centralizer (K₃ : Set X) := by
    refine sup_le (fun a ha => ?_) (fun a ha => ?_)
    · exact Subgroup.mem_centralizer_iff.mpr fun b hb => (h13 a (hP₁K ha) b hb).symm
    · exact Subgroup.mem_centralizer_iff.mpr fun b hb => (h23 a (hP₂K ha) b hb).symm
  have hE₂P₃ : (P₁ ⊔ P₂) ⊓ P₃ = ⊥ := by
    rw [eq_bot_iff]
    rintro z ⟨hz1, hz3⟩
    rw [Subgroup.mem_bot]
    refine hZ₃ z (hP₃K hz3) fun y hy => ?_
    exact ((Subgroup.mem_centralizer_iff.mp (hE₂C hz1)) y hy).symm
  have h := le_pRank_of_commute_of_inf_eq_bot' Nat.prime_three (P := P₁ ⊔ P₂) (Q := P₃) (H := ⊤)
    hE₂ (hel ho₃)
    (fun x hx y hy => ((Subgroup.mem_centralizer_iff.mp (hE₂C hx)) y (hP₃K hy)).symm) hE₂P₃
    (a := 2) (b := 1) hE₂card (by rw [hcard ho₃]; norm_num) le_top le_top
  omega

section Psl2

theorem exists_psl2_model {N : Type} [Group N] {p : ℕ} (hN : IsPSL 2 p 1 N) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F),
      Nat.card F = p ∧ Nonempty (N ≃* CFSG.GorensteinWalter.PSL2 F) := by
  obtain ⟨-, K, hF, hFin, hK, ⟨e⟩⟩ := hN
  exact ⟨K, hF, hFin, by simpa using hK,
    ⟨e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K).symm⟩⟩

theorem three_dvd_card_of_isPSL_two {N : Type} [Group N] [Finite N] {p : ℕ} (hp : p.Prime)
    (hp7 : 7 ≤ p) (hN : IsPSL 2 p 1 N) : 3 ∣ Nat.card N := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := exists_psl2_model hN
  have : Fact p.Prime := ⟨hp⟩
  rw [Nat.card_congr e.toEquiv,
    CFSG.GorensteinWalter.psl2_card_formula F (CFSG.QuasithinUnique.Out21.hodd_of hp7 hF), hF]
  have hp3 : p % 3 = 1 ∨ p % 3 = 2 := by
    have h3 : ¬ 3 ∣ p := fun h => by
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp h
      omega
    omega
  have hpodd : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h | h
    · omega
    · exact h
  have h3 : 3 ∣ p * (p ^ 2 - 1) := by
    have h1 : p ^ 2 % 3 = 1 := by
      rcases hp3 with h | h <;> simp [Nat.pow_mod, h]
    have : 3 ∣ p ^ 2 - 1 := by omega
    exact Dvd.dvd.mul_left this p
  have h2 : 2 ∣ p * (p ^ 2 - 1) := by
    have h1 : p ^ 2 % 2 = 1 := by simp [Nat.pow_mod, hpodd]
    have : 2 ∣ p ^ 2 - 1 := by omega
    exact Dvd.dvd.mul_left this p
  have h6 : 3 * 2 ∣ p * (p ^ 2 - 1) :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h3 h2
  exact Nat.dvd_div_of_mul_dvd h6

theorem exists_orderOf_three_of_isPSL_two {N : Type} [Group N] [Finite N] {p : ℕ} (hp : p.Prime)
    (hp7 : 7 ≤ p) (hN : IsPSL 2 p 1 N) : ∃ x : N, orderOf x = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact exists_prime_orderOf_dvd_card' 3 (three_dvd_card_of_isPSL_two hp hp7 hN)

theorem isQuasisimple_of_simple_of_center_eq_bot {Q : Type} [Group Q] [Finite Q] (hs : IsSimpleGroup Q)
    (hZ : Subgroup.center Q = ⊥) : CFSG.IsQuasisimple Q := by
  have hnt : Nontrivial Q := hs.toNontrivial
  have hnc : ∃ a b : Q, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    obtain ⟨x, hx⟩ := exists_ne (1 : Q)
    have : x ∈ Subgroup.center Q := Subgroup.mem_center_iff.mpr fun g => (hcon g x)
    rw [hZ, Subgroup.mem_bot] at this
    exact hx this
  have hperf : Group.IsPerfect Q := by
    refine ⟨?_⟩
    rcases Subgroup.Normal.eq_bot_or_eq_top (commutator Q) with h | h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnc
      apply hab
      have : ⁅a, b⁆ ∈ commutator Q := Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      rw [h, Subgroup.mem_bot] at this
      exact commutatorElement_eq_one_iff_mul_comm.mp this
    · exact h
  let e : Q ≃* Q ⧸ Subgroup.center Q :=
    (QuotientGroup.quotientBot (G := Q)).symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)
  obtain ⟨a, b, hab⟩ := hnc
  have hne : e a * e b ≠ e b * e a := by
    rw [← map_mul, ← map_mul]
    exact fun h => hab (e.injective h)
  have hnt' : Nontrivial (Q ⧸ Subgroup.center Q) := e.symm.toEquiv.nontrivial
  have hsq : IsSimpleGroup (Q ⧸ Subgroup.center Q) :=
    IsSimpleGroup.isSimpleGroup_of_surjective (G := Q) e.toMonoidHom e.surjective
  exact ⟨hperf, hsq, e a, e b, hne⟩

end Psl2

section Comp

variable {X : Type} [Group X] [Finite X]

theorem isPSL_two_of_mulEquiv {A B : Type} [Group A] [Group B] {p : ℕ} (e : A ≃* B)
    (h : IsPSL 2 p 1 B) : IsPSL 2 p 1 A := by
  obtain ⟨hadm, K, hF, hFin, hK, ⟨e'⟩⟩ := h
  exact ⟨hadm, K, hF, hFin, hK, ⟨e.trans e'⟩⟩

theorem isQuasisimple_of_isPSL_two {N : Type} [Group N] [Finite N] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hN : IsPSL 2 p 1 N) : CFSG.IsQuasisimple N :=
  isQuasisimple_of_simple_of_center_eq_bot (CFSG.LieType.Simplicity.fam_PSL_simplicity N 2 p 1 hN).2
    (center_eq_bot_of_shape (Or.inl ⟨p, hp, hp2, hN⟩))

theorem isComponent_of_isPSL_two {K : Subgroup X} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : IsPSL 2 p 1 ↥K) (hsub : K.IsSubnormal) : CFSG.IsComponent K :=
  ⟨isQuasisimple_of_isPSL_two hp hp2 hK, hsub⟩

theorem mul_comm_of_isComponent_ne {K L : Subgroup X} (hK : CFSG.IsComponent K)
    (hL : CFSG.IsComponent L) (hne : K ≠ L) : ∀ a ∈ K, ∀ b ∈ L, a * b = b * a := by
  have h := (CFSG.LocalCores.distinct_components_commute hK hL).resolve_left hne
  have hle := Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
  intro a ha b hb
  exact ((Subgroup.mem_centralizer_iff.mp (hle ha)) b hb).symm

omit [Finite X] in
theorem isSubnormal_map_conj {K : Subgroup X} (hK : K.IsSubnormal) (g : X) :
    (K.map (MulAut.conj g).toMonoidHom).IsSubnormal :=
  Quasithin.A3.subnormal_top_iff.mp
    (Quasithin.A3.subnormal_top_map (MulAut.conj g).surjective (Quasithin.A3.subnormal_top_iff.mpr hK))

noncomputable def mapConjEquiv (K : Subgroup X) (g : X) : K ≃* K.map (MulAut.conj g).toMonoidHom :=
  Subgroup.equivMapOfInjective K (MulAut.conj g).toMonoidHom (MulAut.conj g).injective

omit [Finite X] in
theorem eq_one_of_forall_comm_of_isPSL {K : Subgroup X} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : IsPSL 2 p 1 ↥K) {x : X} (hx : x ∈ K) (hc : ∀ z ∈ K, x * z = z * x) : x = 1 := by
  have hz : (⟨x, hx⟩ : ↥K) ∈ Subgroup.center ↥K := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hc g g.2).symm
  rw [center_eq_bot_of_shape (Or.inl ⟨p, hp, hp2, hK⟩), Subgroup.mem_bot] at hz
  exact congrArg Subtype.val hz

theorem map_conj_eq_or_of_isPSL {K₁ K₂ : Subgroup X} {t s : X} {p : ℕ} (hp : p.Prime)
    (hp7 : 7 ≤ p) (hSQ : CFSG.Assembly.pRank 3 (⊤ : Subgroup X) ≤ 2)
    (hK₁ : IsPSL 2 p 1 ↥K₁) (hsub : K₁.IsSubnormal)
    (hK₂ : K₂ = K₁.map (MulAut.conj t).toMonoidHom) (hne : K₁ ≠ K₂) :
    K₁.map (MulAut.conj s).toMonoidHom = K₁ ∨ K₁.map (MulAut.conj s).toMonoidHom = K₂ := by
  by_contra hcon
  push Not at hcon
  obtain ⟨h31, h32⟩ := hcon
  have hp2 : p ≠ 2 := by omega
  set K₃ := K₁.map (MulAut.conj s).toMonoidHom with hK₃
  have hpsl : ∀ g : X, IsPSL 2 p 1 ↥(K₁.map (MulAut.conj g).toMonoidHom) := fun g =>
    isPSL_two_of_mulEquiv (mapConjEquiv K₁ g).symm hK₁
  have hcomp : ∀ g : X, CFSG.IsComponent (K₁.map (MulAut.conj g).toMonoidHom) := fun g =>
    isComponent_of_isPSL_two hp hp2 (hpsl g) (isSubnormal_map_conj hsub g)
  have hc₁ : CFSG.IsComponent K₁ := isComponent_of_isPSL_two hp hp2 hK₁ hsub
  have hc₂ : CFSG.IsComponent K₂ := hK₂ ▸ hcomp t
  have hc₃ : CFSG.IsComponent K₃ := hcomp s
  have c12 := mul_comm_of_isComponent_ne hc₁ hc₂ hne
  have c13 := mul_comm_of_isComponent_ne hc₁ hc₃ (Ne.symm h31)
  have c23 := mul_comm_of_isComponent_ne hc₂ hc₃ (Ne.symm h32)
  obtain ⟨y, hy⟩ := exists_orderOf_three_of_isPSL_two hp hp7 hK₁
  have hy' : orderOf (y : X) = 3 := by rw [Subgroup.orderOf_coe]; exact hy
  have hx₂ : t * (y : X) * t⁻¹ ∈ K₂ := by
    rw [hK₂]
    exact Subgroup.mem_map.mpr ⟨y, y.2, by simp [MulAut.conj_apply]⟩
  have hx₃ : s * (y : X) * s⁻¹ ∈ K₃ :=
    Subgroup.mem_map.mpr ⟨y, y.2, by simp [MulAut.conj_apply]⟩
  have ho₂ : orderOf (t * (y : X) * t⁻¹) = 3 := by
    have := MulEquiv.orderOf_eq (MulAut.conj t) (y : X)
    rw [MulAut.conj_apply] at this
    rw [this]; exact hy'
  have ho₃ : orderOf (s * (y : X) * s⁻¹) = 3 := by
    have := MulEquiv.orderOf_eq (MulAut.conj s) (y : X)
    rw [MulAut.conj_apply] at this
    rw [this]; exact hy'
  have h := three_le_pRank_of_three_commuting c12 c13 c23
    (fun x hx hc => eq_one_of_forall_comm_of_isPSL hp hp2 hK₁ hx hc)
    (fun x hx hc => eq_one_of_forall_comm_of_isPSL hp hp2 (hpsl s) hx hc)
    y.2 hx₂ hx₃ hy' ho₂ ho₃
  have h' : 3 ≤ CFSG.Assembly.pRank 3 (⊤ : Subgroup X) := h
  omega

end Comp

section Perm

variable {X : Type} [Group X]

theorem map_conj_map_conj_eq_mul {K : Subgroup X} {s t : X} :
    (K.map (MulAut.conj t).toMonoidHom).map (MulAut.conj s).toMonoidHom =
      K.map (MulAut.conj (s * t)).toMonoidHom := by
  ext y
  rw [mem_map_conj_toMonoidHom_iff, mem_map_conj_toMonoidHom_iff, mem_map_conj_toMonoidHom_iff]
  simp [mul_assoc]

theorem fix_or_swap_of_conj_eq_or {K₁ K₂ : Subgroup X} {t : X}
    (hK₂ : K₂ = K₁.map (MulAut.conj t).toMonoidHom) (hne : K₁ ≠ K₂)
    (horb : ∀ s : X, K₁.map (MulAut.conj s).toMonoidHom = K₁ ∨
      K₁.map (MulAut.conj s).toMonoidHom = K₂) (s : X) :
    (K₁.map (MulAut.conj s).toMonoidHom = K₁ ∧ K₂.map (MulAut.conj s).toMonoidHom = K₂) ∨
      (K₁.map (MulAut.conj s).toMonoidHom = K₂ ∧ K₂.map (MulAut.conj s).toMonoidHom = K₁) := by
  have hK₂s : K₂.map (MulAut.conj s).toMonoidHom = K₁.map (MulAut.conj (s * t)).toMonoidHom := by
    rw [hK₂, map_conj_map_conj_eq_mul]
  have hinj : ∀ A B : Subgroup X, A.map (MulAut.conj s).toMonoidHom =
      B.map (MulAut.conj s).toMonoidHom → A = B := fun A B h =>
    Subgroup.map_injective (MulAut.conj s).injective h
  rcases horb s with h1 | h1 <;> rcases horb (s * t) with h2 | h2
  · exact absurd (hinj _ _ (by rw [hK₂s, h2, h1])) (Ne.symm hne)
  · exact Or.inl ⟨h1, by rw [hK₂s, h2]⟩
  · exact Or.inr ⟨h1, by rw [hK₂s, h2]⟩
  · exact absurd (hinj _ _ (by rw [hK₂s, h2, h1])) hne

theorem inf_normalizer_le_normalizer_of_conj_eq_or {K₁ K₂ T : Subgroup X} {t : X}
    (hK₂ : K₂ = K₁.map (MulAut.conj t).toMonoidHom) (hne : K₁ ≠ K₂)
    (horb : ∀ s : X, K₁.map (MulAut.conj s).toMonoidHom = K₁ ∨
      K₁.map (MulAut.conj s).toMonoidHom = K₂) :
    T ⊓ Subgroup.normalizer (K₁ : Set X) ≤ Subgroup.normalizer (K₂ : Set X) := by
  intro s hs
  rcases fix_or_swap_of_conj_eq_or hK₂ hne horb s with ⟨-, h⟩ | ⟨h1, -⟩
  · exact Quasithin.A38.map_conj_eq_iff.mp h
  · exact absurd (((Quasithin.A38.map_conj_eq_iff.mpr hs.2).symm.trans h1)) hne

theorem normalizer_sup_of_conj_eq_or {K₁ K₂ : Subgroup X} {t : X}
    (hK₂ : K₂ = K₁.map (MulAut.conj t).toMonoidHom) (hne : K₁ ≠ K₂)
    (horb : ∀ s : X, K₁.map (MulAut.conj s).toMonoidHom = K₁ ∨
      K₁.map (MulAut.conj s).toMonoidHom = K₂) (s : X) :
    s ∈ Subgroup.normalizer ((K₁ ⊔ K₂ : Subgroup X) : Set X) := by
  refine Quasithin.A38.map_conj_eq_iff.mp ?_
  rw [Subgroup.map_sup]
  rcases fix_or_swap_of_conj_eq_or hK₂ hne horb s with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
  · rw [h1, h2, sup_comm]

theorem relIndex_inf_normalizer_le_two_of_conj_eq_or {K₁ K₂ T : Subgroup X} {t : X} (ht : t ∈ T)
    (hK₂ : K₂ = K₁.map (MulAut.conj t).toMonoidHom)
    (horb : ∀ s : X, K₁.map (MulAut.conj s).toMonoidHom = K₁ ∨
      K₁.map (MulAut.conj s).toMonoidHom = K₂) :
    (T ⊓ Subgroup.normalizer (K₁ : Set X)).relIndex T ≤ 2 := by
  classical
  set T₀ : Subgroup X := T ⊓ Subgroup.normalizer (K₁ : Set X) with hT₀
  have hcos : ∀ g : ↥T, g ∈ T₀.subgroupOf T ∨ (⟨t, ht⟩ : ↥T)⁻¹ * g ∈ T₀.subgroupOf T := by
    intro g
    rcases horb g with h | h
    · exact Or.inl ⟨g.2, Quasithin.A38.map_conj_eq_iff.mp h⟩
    · refine Or.inr ⟨T.mul_mem (T.inv_mem ht) g.2, ?_⟩
      refine Subgroup.mem_normalizer_iff.mpr (fun y => ?_)
      have hk2 : ∀ z, z ∈ K₂ ↔ t⁻¹ * z * t ∈ K₁ := by
        intro z; rw [hK₂]; exact mem_map_conj_toMonoidHom_iff
      have hg2 : ∀ z, z ∈ K₂ ↔ (g : X)⁻¹ * z * g ∈ K₁ := by
        intro z; rw [← h]; exact mem_map_conj_toMonoidHom_iff
      have h1 := hg2 ((g : X) * y * (g : X)⁻¹)
      have h2 := hk2 ((g : X) * y * (g : X)⁻¹)
      have e1 : (g : X)⁻¹ * ((g : X) * y * (g : X)⁻¹) * g = y := by group
      have e2 : t⁻¹ * ((g : X) * y * (g : X)⁻¹) * t =
          (⟨t, ht⟩ : ↥T)⁻¹.1 * g.1 * y * ((⟨t, ht⟩ : ↥T)⁻¹.1 * g.1)⁻¹ := by
        simp only [InvMemClass.coe_inv]; group
      rw [e1] at h1
      rw [e2] at h2
      exact h1.symm.trans h2
  have hsurj : Function.Surjective (fun b : Bool =>
      (QuotientGroup.mk (if b then (⟨t, ht⟩ : ↥T) else 1) : ↥T ⧸ T₀.subgroupOf T)) := by
    intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    rcases hcos g with h | h
    · exact ⟨false, by simpa using (QuotientGroup.eq.mpr (by simpa using Subgroup.inv_mem _ h))⟩
    · exact ⟨true, by simpa using (QuotientGroup.eq.mpr h)⟩
  have h := Nat.card_le_card_of_surjective _ hsurj
  have hb : Nat.card Bool = 2 := by simp [Nat.card_eq_fintype_card]
  have hidx : T₀.relIndex T = Nat.card (↥T ⧸ T₀.subgroupOf T) := Subgroup.index_eq_card _
  rw [hidx]
  omega

end Perm

section Cent

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem eq_one_of_forall_comm_sup {K₁ K₂ : Subgroup X} (hcomm : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a)
    (hZ₁ : ∀ x ∈ K₁, (∀ y ∈ K₁, x * y = y * x) → x = 1)
    (hZ₂ : ∀ x ∈ K₂, (∀ y ∈ K₂, x * y = y * x) → x = 1) {n : X} (hn : n ∈ K₁ ⊔ K₂)
    (hc : ∀ m ∈ K₁ ⊔ K₂, n * m = m * n) : n = 1 := by
  have hN : K₁ ≤ Subgroup.normalizer (K₂ : Set X) := le_normalizer_of_forall_commute hcomm
  have hn' : n ∈ ((K₁ ⊔ K₂ : Subgroup X) : Set X) := hn
  rw [Subgroup.coe_mul_of_left_le_normalizer_right K₁ K₂ hN] at hn'
  obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.mp hn'
  have h1 : a = 1 := by
    refine hZ₁ a ha fun k hk => ?_
    have h := hc k (Subgroup.mem_sup_left hk)
    have hbk : b * k = k * b := (hcomm k hk b hb).symm
    have e : (a * k) * b = (k * a) * b := by
      calc (a * k) * b = a * (k * b) := by rw [mul_assoc]
        _ = a * (b * k) := by rw [hbk]
        _ = a * b * k := by rw [mul_assoc]
        _ = k * (a * b) := h
        _ = (k * a) * b := by rw [mul_assoc]
    exact mul_right_cancel e
  have h2 : b = 1 := by
    refine hZ₂ b hb fun k hk => ?_
    have h := hc k (Subgroup.mem_sup_right hk)
    have hak : a * k = k * a := hcomm a ha k hk
    have e : a * (b * k) = a * (k * b) := by
      calc a * (b * k) = a * b * k := by rw [mul_assoc]
        _ = k * (a * b) := h
        _ = (k * a) * b := by rw [mul_assoc]
        _ = (a * k) * b := by rw [hak]
        _ = a * (k * b) := by rw [mul_assoc]
    exact mul_left_cancel e
  rw [h1, h2, one_mul]

theorem eq_one_of_centralizes_sup {K₁ K₂ T P : Subgroup X}
    (hcomm : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a)
    (hZ₁ : ∀ x ∈ K₁, (∀ y ∈ K₁, x * y = y * x) → x = 1)
    (hZ₂ : ∀ x ∈ K₂, (∀ y ∈ K₂, x * y = y * x) → x = 1)
    (hnorm : ∀ g : X, g ∈ Subgroup.normalizer ((K₁ ⊔ K₂ : Subgroup X) : Set X))
    (hX2 : ∀ x : X, ∃ k : ℕ, x ^ 2 ^ k ∈ K₁ ⊔ K₂)
    (hT : IsPGroup 2 T) (hodd : ¬ 2 ∣ T.index) (hTP : T ≤ P)
    (hP : ∀ x : X, (∀ g : X, g * x * g⁻¹ ∈ P) → x = 1)
    {x : X} (hx₁ : x ∈ Subgroup.centralizer (K₁ : Set X))
    (hx₂ : x ∈ Subgroup.centralizer (K₂ : Set X)) : x = 1 := by
  have : (K₁ ⊔ K₂).Normal := ⟨fun n hn g => (Subgroup.mem_normalizer_iff.mp (hnorm g) n).mp hn⟩
  refine centralizer_eq_one_of_coreFree (K₁ ⊔ K₂) T P
    (fun n hn hc => eq_one_of_forall_comm_sup hcomm hZ₁ hZ₂ hn hc) hX2 hT hodd hTP hP x ?_
  intro n hn
  have hle : K₁ ⊔ K₂ ≤ Subgroup.centralizer ({x} : Set X) := by
    refine sup_le (fun k hk => ?_) (fun k hk => ?_)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.mp hx₁ k hk)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.mp hx₂ k hk)
  have h := Subgroup.mem_centralizer_singleton_iff.mp (hle hn)
  calc x * n * x⁻¹ = n * x * x⁻¹ := by rw [← h]
    _ = n := by group

end Cent

end Rank3


end CFSG.Quasithin
