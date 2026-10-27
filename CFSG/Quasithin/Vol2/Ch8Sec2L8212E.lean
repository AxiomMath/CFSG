module

public import CFSG.Quasithin.H13.J4PlusType
public import CFSG.RankThree.PartOne.S10.PlaneTwoGroupLemmas
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch8Sec2L8210D
public import CFSG.Quasithin.Vol2.Ch9L34Gam

public section

namespace CFSG.Quasithin.H13

open scoped commutatorElement

section L8212E

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def commHom82 {E : Subgroup G} {z : G} (hzE : ∀ x ∈ E, x * z = z * x)
    (a : G) (hcomm : ∀ x ∈ E, ⁅a, x⁆ ∈ Subgroup.zpowers z) :
    ↥E →* ↥(Subgroup.zpowers z) :=
  MonoidHom.mk' (fun x => ⟨⁅a, (x : G)⁆, hcomm x x.2⟩) fun x y => by
    apply Subtype.ext
    have hc : (x : G) * ⁅a, (y : G)⁆ = ⁅a, (y : G)⁆ * x := by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hcomm y y.2)
      rw [← hk]
      exact (Commute.zpow_right (hzE x x.2) k).eq
    simp only [Subgroup.coe_mul]
    calc ⁅a, (x : G) * y⁆ = ⁅a, (x : G)⁆ * ((x : G) * ⁅a, (y : G)⁆ * (x : G)⁻¹) := by
          simp only [commutatorElement_def]
          group
      _ = ⁅a, (x : G)⁆ * ⁅a, (y : G)⁆ := by rw [hc, mul_inv_cancel_right]

omit [Finite G] in
theorem commHom82_apply {E : Subgroup G} {z : G} (hzE : ∀ x ∈ E, x * z = z * x) {a : G}
    (hcomm : ∀ x ∈ E, ⁅a, x⁆ ∈ Subgroup.zpowers z) (x : ↥E) :
    ((commHom82 hzE a hcomm x : ↥(Subgroup.zpowers z)) : G) = ⁅a, (x : G)⁆ := rfl

omit [Finite G] in
theorem commutator_mul_right_82 {E : Subgroup G} {z : G} (hzE : ∀ x ∈ E, x * z = z * x) {a : G}
    (hcomm : ∀ x ∈ E, ⁅a, x⁆ ∈ Subgroup.zpowers z) {x y : G} (hx : x ∈ E) (hy : y ∈ E) :
    ⁅a, x * y⁆ = ⁅a, x⁆ * ⁅a, y⁆ := by
  have := congrArg Subtype.val (map_mul (commHom82 hzE a hcomm) ⟨x, hx⟩ ⟨y, hy⟩)
  simpa only [Subgroup.coe_mul, commHom82_apply] using this

theorem card_eq_two_mul_inf_centralizer_82 {E : Subgroup G} {z : G} (hz1 : z ≠ 1)
    (hz2 : z ^ 2 = 1) (hzE : ∀ x ∈ E, x * z = z * x) {a b : G} (hbE : b ∈ E)
    (hcomm : ∀ x ∈ E, ⁅a, x⁆ ∈ Subgroup.zpowers z) (hab : ⁅a, b⁆ = z) :
    Nat.card ↥E = 2 * Nat.card ↥(E ⊓ Subgroup.centralizer ({a} : Set G)) := by
  set f := commHom82 hzE a hcomm with hf
  have hz2' : Nat.card ↥(Subgroup.zpowers z) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime hz2 hz1
  have hsurj : Function.Surjective f := by
    intro w
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp w.2
    refine ⟨⟨b, hbE⟩ ^ k, Subtype.ext ?_⟩
    rw [map_zpow, Subgroup.coe_zpow, commHom82_apply, hab]
    exact hk
  have h1 := card_eq_card_map_mul_82 f ⊤
  rw [Subgroup.map_top_of_surjective _ hsurj, Subgroup.card_top, Subgroup.card_top, hz2',
    top_inf_eq] at h1
  have hker : Nat.card ↥f.ker = Nat.card ↥(E ⊓ Subgroup.centralizer ({a} : Set G)) := by
    have e1 : f.ker = (E ⊓ Subgroup.centralizer ({a} : Set G)).subgroupOf E := by
      ext x
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      constructor
      · intro h
        refine ⟨x.2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
        have h2 := congrArg Subtype.val h
        rw [commHom82_apply, OneMemClass.coe_one, commutatorElement_eq_one_iff_mul_comm] at h2
        exact h2.symm
      · rintro ⟨-, h⟩
        apply Subtype.ext
        rw [commHom82_apply, OneMemClass.coe_one, commutatorElement_eq_one_iff_mul_comm]
        exact (Subgroup.mem_centralizer_singleton_iff.mp h).symm
    rw [e1]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  rw [h1, hker]

theorem exists_d8_basis_82 {z : G} (hz1 : z ≠ 1) (hz2 : z ^ 2 = 1) :
    ∀ (e : ℕ) (E A : Subgroup G), Nat.card ↥E = 2 ^ (2 * e + 1) → A ≤ E →
      (∀ a ∈ A, ∀ a' ∈ A, a * a' = a' * a) → (∀ a ∈ A, a ^ 2 = 1) →
      Nat.card ↥A = 2 ^ (e + 1) → z ∈ A → (∀ x ∈ E, x * z = z * x) →
      (∀ x ∈ E, ∀ y ∈ E, ⁅x, y⁆ ∈ Subgroup.zpowers z) → (∀ x ∈ E, x ^ 2 ∈ Subgroup.zpowers z) →
      (∀ a ∈ A, a ∉ Subgroup.zpowers z → ∃ x ∈ E, ⁅a, x⁆ ≠ 1) →
      ∃ a b : Fin e → G, (∀ i, a i ∈ E) ∧ (∀ i, b i ∈ E) ∧ (∀ i, a i ^ 2 = 1) ∧
        (∀ i, b i ^ 2 = 1) ∧ (∀ i, (a i * b i) ^ 2 = z) ∧
        (∀ i j, i ≠ j → Commute (a i) (a j) ∧ Commute (a i) (b j) ∧ Commute (b i) (b j)) ∧
        Subgroup.closure (Set.range a ∪ Set.range b ∪ {z}) = E ∧
        (∀ x ∈ E, (∀ i, Commute (a i) x ∧ Commute (b i) x) → x ∈ Subgroup.zpowers z) := by
  have hz2' : Nat.card ↥(Subgroup.zpowers z) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime hz2 hz1
  have hZ : ∀ w ∈ Subgroup.zpowers z, w = 1 ∨ w = z := by
    intro w hw
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    have hk : z ^ k = z ^ (k % 2) := by
      have := zpow_mod_orderOf z k
      rw [orderOf_eq_prime hz2 hz1] at this
      exact_mod_cast this.symm
    rcases Int.emod_two_eq_zero_or_one k with h | h
    · left
      rw [hk, h, zpow_zero]
    · right
      rw [hk, h, zpow_one]
  intro e
  induction e with
  | zero =>
    intro E A hE hAE _ _ _ hzA _ _ _ _
    have hEz : Subgroup.zpowers z = E := by
      refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr (hAE hzA)) ?_
      rw [hE, hz2']
      norm_num
    refine ⟨Fin.elim0, Fin.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0,
      fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, ?_, fun x hx _ => hEz ▸ hx⟩
    simp only [Set.range_eq_empty, Set.empty_union]
    rw [← Subgroup.zpowers_eq_closure]
    exact hEz
  | succ e ih =>
    intro E A hE hAE hAc hA2 hAcard hzA hzE hcomm hsq hnc
    obtain ⟨a, haA, haz⟩ : ∃ a ∈ A, a ∉ Subgroup.zpowers z := by
      by_contra h
      push Not at h
      have h1 : Nat.card ↥A ≤ Nat.card ↥(Subgroup.zpowers z) := Subgroup.card_le_of_le h
      rw [hAcard, hz2'] at h1
      have : 2 ^ 2 ≤ 2 ^ (e + 1 + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have haE : a ∈ E := hAE haA
    have ha2 : a ^ 2 = 1 := hA2 a haA
    obtain ⟨x, hxE, hax⟩ := hnc a haA haz
    have haxz : ⁅a, x⁆ = z := (hZ _ (hcomm a haE x hxE)).resolve_left hax
    obtain ⟨b, hbE, hb2, hab⟩ : ∃ b ∈ E, b ^ 2 = 1 ∧ ⁅a, b⁆ = z := by
      rcases hZ _ (hsq x hxE) with h | h
      · exact ⟨x, hxE, h, haxz⟩
      · refine ⟨x * a, E.mul_mem hxE haE, ?_, ?_⟩
        · have hax' : a * x = z * x * a := by
            rw [← haxz, commutatorElement_def]
            group
          have hxz : x * z = z * x := hzE x hxE
          have e1 : (x * a) ^ 2 = z * x ^ 2 * a ^ 2 := by
            calc (x * a) ^ 2 = x * (a * x) * a := by rw [sq]; group
              _ = x * (z * x * a) * a := by rw [hax']
              _ = (x * z) * x * a * a := by group
              _ = (z * x) * x * a * a := by rw [hxz]
              _ = z * x ^ 2 * a ^ 2 := by rw [sq, sq]; group
          rw [e1, h, ha2, mul_one, ← sq, hz2]
        · rw [← haxz]
          simp only [commutatorElement_def]
          group
    have hbz : b * z = z * b := hzE b hbE
    have hba : ⁅b, a⁆ = z := by
      rw [← commutatorElement_inv, hab]
      exact inv_eq_of_mul_eq_one_right (by rw [← sq, hz2])
    have hab' : (a * b) ^ 2 = z := by
      have h1 : a * b = z * b * a := by
        rw [← hab, commutatorElement_def]
        group
      have haz' : a * z = z * a := hzE a haE
      have e1 : (a * b) ^ 2 = z * a * b ^ 2 * a := by
        calc (a * b) ^ 2 = a * b * (a * b) := by rw [sq]
          _ = a * b * (z * b * a) := by rw [h1]
          _ = a * (b * z) * b * a := by group
          _ = a * (z * b) * b * a := by rw [hbz]
          _ = (a * z) * b * b * a := by group
          _ = (z * a) * b * b * a := by rw [haz']
          _ = z * a * b ^ 2 * a := by rw [sq]; group
      rw [e1, hb2, mul_one, mul_assoc, ← sq, ha2, mul_one]
    set Ea := E ⊓ Subgroup.centralizer ({a} : Set G) with hEa
    set E₁ := Ea ⊓ Subgroup.centralizer ({b} : Set G) with hE₁
    set A₁ := A ⊓ Subgroup.centralizer ({b} : Set G) with hA₁
    have hcomma : ∀ y ∈ E, ⁅a, y⁆ ∈ Subgroup.zpowers z := fun y hy => hcomm a haE y hy
    have hcommb : ∀ y ∈ E, ⁅b, y⁆ ∈ Subgroup.zpowers z := fun y hy => hcomm b hbE y hy
    have hzEa : ∀ y ∈ Ea, y * z = z * y := fun y hy => hzE y hy.1
    have haEa : a ∈ Ea := ⟨haE, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
    have hcardEa := card_eq_two_mul_inf_centralizer_82 hz1 hz2 hzE hbE hcomma hab
    have hcardE₁ := card_eq_two_mul_inf_centralizer_82 hz1 hz2 hzEa haEa
      (fun y hy => hcommb y hy.1) hba
    have hcardA₁ := card_eq_two_mul_inf_centralizer_82 hz1 hz2 (fun y hy => hzE y (hAE hy))
      haA (fun y hy => hcommb y (hAE hy)) hba
    have h0 : Nat.card ↥E = 2 * Nat.card ↥Ea := hcardEa
    have h0' : Nat.card ↥Ea = 2 * Nat.card ↥E₁ := hcardE₁
    have h0'' : Nat.card ↥A = 2 * Nat.card ↥A₁ := hcardA₁
    have hE₁c : Nat.card ↥E₁ = 2 ^ (2 * e + 1) := by
      have h1 : 2 ^ (2 * (e + 1) + 1) = 2 * (2 * 2 ^ (2 * e + 1)) := by ring
      rw [h1] at hE
      omega
    have hA₁c : Nat.card ↥A₁ = 2 ^ (e + 1) := by
      have h1 : 2 ^ (e + 1 + 1) = 2 * 2 ^ (e + 1) := by ring
      rw [h1] at hAcard
      omega
    have hE₁E : E₁ ≤ E := fun y hy => hy.1.1
    have hA₁E₁ : A₁ ≤ E₁ := fun y hy =>
      ⟨⟨hAE hy.1, Subgroup.mem_centralizer_singleton_iff.mpr (hAc y hy.1 a haA)⟩, hy.2⟩
    have hzA₁ : z ∈ A₁ := ⟨hzA, Subgroup.mem_centralizer_singleton_iff.mpr (hzE b hbE).symm⟩
    have hadj : ∀ y ∈ E, ∃ i j : ℕ, y * b ^ i * a ^ j ∈ E₁ := by
      intro y hy
      obtain ⟨i, hi⟩ : ∃ i : ℕ, ⁅a, y * b ^ i⁆ = 1 := by
        rcases hZ _ (hcomma y hy) with h | h
        · exact ⟨0, by rw [pow_zero, mul_one, h]⟩
        · refine ⟨1, ?_⟩
          rw [pow_one, commutator_mul_right_82 hzE hcomma hy hbE, h, hab, ← sq, hz2]
      have hy1 : y * b ^ i ∈ E := E.mul_mem hy (E.pow_mem hbE i)
      obtain ⟨j, hj⟩ : ∃ j : ℕ, ⁅b, y * b ^ i * a ^ j⁆ = 1 := by
        rcases hZ _ (hcommb _ hy1) with h | h
        · exact ⟨0, by rw [pow_zero, mul_one, h]⟩
        · refine ⟨1, ?_⟩
          rw [pow_one, commutator_mul_right_82 hzE hcommb hy1 haE, h, hba, ← sq, hz2]
      refine ⟨i, j, ⟨⟨E.mul_mem hy1 (E.pow_mem haE j), ?_⟩, ?_⟩⟩
      · show y * b ^ i * a ^ j ∈ Subgroup.centralizer ({a} : Set G)
        have h1 : ⁅a, y * b ^ i * a ^ j⁆ = 1 := by
          rw [commutator_mul_right_82 hzE hcomma hy1 (E.pow_mem haE j), hi, one_mul,
            commutatorElement_eq_one_iff_mul_comm]
          exact (Commute.self_pow a j).eq
        exact Subgroup.mem_centralizer_singleton_iff.mpr
          (commutatorElement_eq_one_iff_mul_comm.mp h1).symm
      · show y * b ^ i * a ^ j ∈ Subgroup.centralizer ({b} : Set G)
        exact Subgroup.mem_centralizer_singleton_iff.mpr
          (commutatorElement_eq_one_iff_mul_comm.mp hj).symm
    have hnc₁ : ∀ a₁ ∈ A₁, a₁ ∉ Subgroup.zpowers z → ∃ y ∈ E₁, ⁅a₁, y⁆ ≠ 1 := by
      intro a₁ ha₁ ha₁z
      obtain ⟨y, hyE, hy1⟩ := hnc a₁ ha₁.1 ha₁z
      obtain ⟨i, j, hij⟩ := hadj y hyE
      refine ⟨_, hij, fun h => hy1 ?_⟩
      have hcomm₁ : ∀ w ∈ E, ⁅a₁, w⁆ ∈ Subgroup.zpowers z := fun w hw =>
        hcomm a₁ (hAE ha₁.1) w hw
      have hb' : ⁅a₁, b ^ i⁆ = 1 := by
        rw [commutatorElement_eq_one_iff_mul_comm]
        exact (Commute.pow_right (Subgroup.mem_centralizer_singleton_iff.mp ha₁.2) i).eq
      have ha' : ⁅a₁, a ^ j⁆ = 1 := by
        rw [commutatorElement_eq_one_iff_mul_comm]
        exact (Commute.pow_right (hAc a₁ ha₁.1 a haA) j).eq
      rw [commutator_mul_right_82 hzE hcomm₁ (E.mul_mem hyE (E.pow_mem hbE i))
          (E.pow_mem haE j), commutator_mul_right_82 hzE hcomm₁ hyE (E.pow_mem hbE i), hb', ha',
        mul_one, mul_one] at h
      exact h
    obtain ⟨a', b', ha'E, hb'E, ha'2, hb'2, hab'2, hcomm', hgen', hcen'⟩ := ih E₁ A₁ hE₁c hA₁E₁
      (fun u hu v hv => hAc u hu.1 v hv.1) (fun u hu => hA2 u hu.1) hA₁c hzA₁
      (fun y hy => hzE y (hE₁E hy)) (fun x hx y hy => hcomm x (hE₁E hx) y (hE₁E hy))
      (fun x hx => hsq x (hE₁E hx)) hnc₁
    refine ⟨Fin.cons a a', Fin.cons b b', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · simpa using haE
      · simpa using hE₁E (ha'E i)
    · intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · simpa using hbE
      · simpa using hE₁E (hb'E i)
    · intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · simpa using ha2
      · simpa using ha'2 i
    · intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · simpa using hb2
      · simpa using hb'2 i
    · intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · simpa using hab'
      · simpa using hab'2 i
    ·
      have hca : ∀ y ∈ E₁, Commute a y := fun y hy =>
        (Subgroup.mem_centralizer_singleton_iff.mp hy.1.2).symm
      have hcb : ∀ y ∈ E₁, Commute b y := fun y hy =>
        (Subgroup.mem_centralizer_singleton_iff.mp hy.2).symm
      intro i j hij
      induction i using Fin.cases with
      | zero =>
        induction j using Fin.cases with
        | zero => exact absurd rfl hij
        | succ j =>
          simp only [Fin.cons_zero, Fin.cons_succ]
          exact ⟨hca _ (ha'E j), hca _ (hb'E j), hcb _ (hb'E j)⟩
      | succ i =>
        induction j using Fin.cases with
        | zero =>
          simp only [Fin.cons_zero, Fin.cons_succ]
          exact ⟨(hca _ (ha'E i)).symm, (hcb _ (ha'E i)).symm, (hcb _ (hb'E i)).symm⟩
        | succ j =>
          simp only [Fin.cons_succ]
          exact hcomm' i j fun h => hij (by rw [h])
    ·
      set S := Subgroup.closure (Set.range (Fin.cons a a' : Fin (e + 1) → G) ∪
        Set.range (Fin.cons b b' : Fin (e + 1) → G) ∪ {z}) with hS
      apply le_antisymm
      · rw [hS, Subgroup.closure_le]
        rintro _ ((⟨i, rfl⟩ | ⟨i, rfl⟩) | h)
        · refine Fin.cases ?_ (fun i => ?_) i
          · simpa using haE
          · simpa using hE₁E (ha'E i)
        · refine Fin.cases ?_ (fun i => ?_) i
          · simpa using hbE
          · simpa using hE₁E (hb'E i)
        · rw [Set.mem_singleton_iff] at h
          rw [h]
          exact hAE hzA
      · have haS : a ∈ S := Subgroup.subset_closure (Or.inl (Or.inl ⟨0, by simp⟩))
        have hbS : b ∈ S := Subgroup.subset_closure (Or.inl (Or.inr ⟨0, by simp⟩))
        have hE₁S : E₁ ≤ S := by
          rw [← hgen', Subgroup.closure_le]
          rintro _ ((⟨i, rfl⟩ | ⟨i, rfl⟩) | h)
          · exact Subgroup.subset_closure (Or.inl (Or.inl ⟨i.succ, by simp⟩))
          · exact Subgroup.subset_closure (Or.inl (Or.inr ⟨i.succ, by simp⟩))
          · exact Subgroup.subset_closure (Or.inr h)
        intro y hy
        obtain ⟨i, j, hij⟩ := hadj y hy
        have h1 : y = y * b ^ i * a ^ j * (a ^ j)⁻¹ * (b ^ i)⁻¹ := by group
        rw [h1]
        exact S.mul_mem (S.mul_mem (hE₁S hij) (S.inv_mem (S.pow_mem haS j)))
          (S.inv_mem (S.pow_mem hbS i))
    ·
      intro y hy hyc
      have hya : Commute a y := by simpa using (hyc 0).1
      have hyb : Commute b y := by simpa using (hyc 0).2
      refine hcen' y ⟨⟨hy, Subgroup.mem_centralizer_singleton_iff.mpr hya.eq.symm⟩,
        Subgroup.mem_centralizer_singleton_iff.mpr hyb.eq.symm⟩ fun i => ?_
      simpa using hyc i.succ

theorem extraspecial_d8_82 {z : G} (hz1 : z ≠ 1) (hz2 : z ^ 2 = 1) {e : ℕ} (he : 0 < e)
    {E A : Subgroup G} (hE : Nat.card ↥E = 2 ^ (2 * e + 1)) (hAE : A ≤ E)
    (hAc : ∀ a ∈ A, ∀ a' ∈ A, a * a' = a' * a) (hA2 : ∀ a ∈ A, a ^ 2 = 1)
    (hAcard : Nat.card ↥A = 2 ^ (e + 1)) (hzA : z ∈ A) (hzE : ∀ x ∈ E, x * z = z * x)
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, ⁅x, y⁆ ∈ Subgroup.zpowers z)
    (hsq : ∀ x ∈ E, x ^ 2 ∈ Subgroup.zpowers z)
    (hnc : ∀ a ∈ A, a ∉ Subgroup.zpowers z → ∃ x ∈ E, ⁅a, x⁆ ≠ 1) :
    IsExtraspecialPGroup 2 ↥E ∧ (Subgroup.center ↥E).map E.subtype = Subgroup.zpowers z ∧
      Nonempty (↥E ≃* J4.D8CentralProduct e) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, b, haE, hbE, ha2, hb2, hab, hcab, hgen, hcen⟩ :=
    exists_d8_basis_82 hz1 hz2 e E A hE hAE hAc hA2 hAcard hzA hzE hcomm hsq hnc
  have hzE' : z ∈ E := hAE hzA
  have hz2' : Nat.card ↥(Subgroup.zpowers z) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime hz2 hz1
  have hcenter : (Subgroup.center ↥E).map E.subtype = Subgroup.zpowers z := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      refine hcen _ x.2 fun i => ⟨?_, ?_⟩
      · have := Subgroup.mem_center_iff.mp hx (⟨a i, haE i⟩ : ↥E)
        exact congrArg Subtype.val this
      · have := Subgroup.mem_center_iff.mp hx (⟨b i, hbE i⟩ : ↥E)
        exact congrArg Subtype.val this
    · rw [Subgroup.zpowers_le]
      refine ⟨⟨z, hzE'⟩, Subgroup.mem_center_iff.mpr fun y => Subtype.ext ?_, rfl⟩
      exact (hzE y y.2)
  have hgen' : Subgroup.closure (Set.range a ∪ Set.range b) = E := by
    apply le_antisymm
    · rw [← hgen]
      exact Subgroup.closure_mono (Set.subset_union_left)
    · rw [← hgen, Subgroup.closure_le]
      rintro x (hx | hx)
      · exact Subgroup.subset_closure hx
      · rw [Set.mem_singleton_iff] at hx
        rw [hx, ← hab ⟨0, he⟩]
        have h1 : a ⟨0, he⟩ ∈ Subgroup.closure (Set.range a ∪ Set.range b) :=
          Subgroup.subset_closure (Set.mem_union_left _ (Set.mem_range_self _))
        have h2 : b ⟨0, he⟩ ∈ Subgroup.closure (Set.range a ∪ Set.range b) :=
          Subgroup.subset_closure (Set.mem_union_right _ (Set.mem_range_self _))
        exact Subgroup.pow_mem _ (Subgroup.mul_mem _ h1 h2) 2
  refine ⟨?_, hcenter, ?_⟩
  ·
    have hEp : IsPGroup 2 ↥E := IsPGroup.of_card hE
    set Z := (Subgroup.zpowers z).subgroupOf E with hZ
    have hZc : Nat.card ↥Z = 2 := by
      rw [hZ, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.zpowers_le.mpr hzE')).toEquiv,
        hz2']
    have hmemZ : ∀ x : ↥E, x ∈ Z ↔ (x : G) ∈ Subgroup.zpowers z := fun x =>
      Subgroup.mem_subgroupOf
    refine CFSG.RankThree.PartOne.PlaneCommuting.isExtraspecialPGroup_of_pairing hEp hZc ?_ ?_ ?_
      ?_ ?_
    · intro x hx
      rw [hmemZ] at hx
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hx
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      rw [← hk]
      exact (Commute.zpow_right (hzE g g.2) k).eq
    · intro x y
      rw [hmemZ]
      exact hcomm _ x.2 _ y.2
    · intro x
      rw [hmemZ]
      exact hsq _ x.2
    · intro x hx
      rw [hmemZ]
      refine hcen _ x.2 fun i => ⟨?_, ?_⟩
      · exact (congrArg Subtype.val (hx ⟨a i, haE i⟩)).symm
      · exact (congrArg Subtype.val (hx ⟨b i, hbE i⟩)).symm
    · refine ⟨⟨a ⟨0, he⟩, haE _⟩, fun h => ?_⟩
      rw [hmemZ] at h
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
      have hk' : z ^ k = a ⟨0, he⟩ := hk
      have hc : a ⟨0, he⟩ * b ⟨0, he⟩ = b ⟨0, he⟩ * a ⟨0, he⟩ := by
        rw [← hk']
        exact (Commute.zpow_left (show Commute z (b ⟨0, he⟩) from (hzE _ (hbE _)).symm) k).eq
      apply hz1
      rw [← hab ⟨0, he⟩]
      calc (a ⟨0, he⟩ * b ⟨0, he⟩) ^ 2 = a ⟨0, he⟩ * (b ⟨0, he⟩ * a ⟨0, he⟩) * b ⟨0, he⟩ := by
            rw [sq]; group
        _ = a ⟨0, he⟩ * (a ⟨0, he⟩ * b ⟨0, he⟩) * b ⟨0, he⟩ := by rw [hc]
        _ = a ⟨0, he⟩ ^ 2 * b ⟨0, he⟩ ^ 2 := by rw [sq, sq]; group
        _ = 1 := by rw [ha2, hb2, one_mul]
  ·
    have : Finite ↥E := inferInstance
    refine J4.nonempty_mulEquiv_D8CentralProduct (G := ↥E) he (fun i => ⟨a i, haE i⟩)
      (fun i => ⟨b i, hbE i⟩) ⟨z, hzE'⟩ (fun i => Subtype.ext (by simpa using ha2 i))
      (fun i => Subtype.ext (by simpa using hb2 i)) (fun i => Subtype.ext (by simpa using hab i))
      (Subtype.ext (by simpa using hz2)) (fun i j hij => ?_) ?_ hE
    · obtain ⟨h1, h2, h3⟩ := hcab i j hij
      exact ⟨Subtype.ext h1.eq, Subtype.ext h2.eq, Subtype.ext h3.eq⟩
    · apply Subgroup.map_injective E.subtype_injective
      rw [MonoidHom.map_closure, ← MonoidHom.range_eq_map, Subgroup.range_subtype,
        Set.image_union, ← Set.range_comp, ← Set.range_comp]
      exact hgen'

end L8212E

end CFSG.Quasithin.H13
