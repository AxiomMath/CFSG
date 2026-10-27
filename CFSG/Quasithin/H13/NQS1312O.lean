module

public import CFSG.Quasithin.Vol2.Ch11SecA04Hyp319
public import CFSG.Quasithin.Vol2.Ch10SecV1SK
public import CFSG.Quasithin.Background.A3Structure319
public import CFSG.Quasithin.Background.C4Defs
public import CFSG.Quasithin.H13.NQS1312U

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.U3.NLine

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.SteinbergCB CFSG.Assembly.LowTwoRank
open scoped IsMulCommutative commutatorElement Pointwise

theorem card_statedSL3 (F : Type) [Field F] [Fintype F] :
    Nat.card ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F) =
      Fintype.card F ^ 3 * (Fintype.card F ^ 3 - 1) * (Fintype.card F ^ 2 - 1) := by
  set q := Fintype.card F with hq
  have hq1 : 1 < q := Fintype.one_lt_card
  have h1 : Nat.card (Matrix.SpecialLinearGroup (Fin 3) F) * Nat.card Fˣ =
      Nat.card (GL (Fin 3) F) := Matrix.card_SL_mul_card_units
  have h2 : Nat.card (GL (Fin 3) F) = ∏ i : Fin 3, (q ^ 3 - q ^ (i : ℕ)) := Matrix.card_GL_field 3
  have hu : Nat.card Fˣ = q - 1 := by rw [Nat.card_units, Nat.card_eq_fintype_card]
  rw [← Nat.card_congr (specialLinearGroupEquivStatedSL 3 F).toEquiv]
  rw [h2, hu, Fin.prod_univ_three] at h1
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one] at h1
  have hpos : 0 < q - 1 := by omega
  refine Nat.eq_of_mul_eq_mul_right hpos ?_
  rw [h1]
  have e1 : q ^ 3 - q = q * (q ^ 2 - 1) := by
    rw [Nat.mul_sub, mul_one, ← pow_succ']
  have e2 : q ^ 3 - q ^ 2 = q ^ 2 * (q - 1) := by
    rw [Nat.mul_sub, mul_one, ← pow_succ]
  rw [e1, e2]
  ring

theorem odd_pow_sub_one_two_pow {m k : ℕ} (hm : 1 ≤ m) (hk : 1 ≤ k) : Odd ((2 ^ m) ^ k - 1) := by
  have h2 : 2 ∣ (2 ^ m) ^ k := by
    rw [← pow_mul]
    exact dvd_pow_self 2 (by positivity)
  have hpos : 1 ≤ (2 ^ m) ^ k := Nat.one_le_pow _ _ (by positivity)
  obtain ⟨c, hc⟩ := h2
  refine ⟨c - 1, ?_⟩
  have : 1 ≤ c := by
    rcases Nat.eq_zero_or_pos c with h | h
    · rw [h] at hc
      omega
    · exact h
  omega

theorem eq_of_card_statedSL3_eq {F F' : Type} [Field F] [Fintype F] [Field F'] [Fintype F']
    {m m' : ℕ} (hm : 1 ≤ m) (hm' : 1 ≤ m') (hF : Fintype.card F = 2 ^ m)
    (hF' : Fintype.card F' = 2 ^ m')
    (h : Nat.card ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F) =
      Nat.card ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F')) : m = m' := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [card_statedSL3, card_statedSL3, hF, hF'] at h
  have hv : ∀ {a : ℕ}, 1 ≤ a →
      padicValNat 2 ((2 ^ a) ^ 3 * ((2 ^ a) ^ 3 - 1) * ((2 ^ a) ^ 2 - 1)) = 3 * a := by
    intro a ha
    have h3 := odd_pow_sub_one_two_pow (k := 3) ha (by norm_num)
    have h2 := odd_pow_sub_one_two_pow (k := 2) ha (by norm_num)
    have hne3 : (2 ^ a) ^ 3 - 1 ≠ 0 := Nat.pos_iff_ne_zero.1 h3.pos
    have hne2 : (2 ^ a) ^ 2 - 1 ≠ 0 := Nat.pos_iff_ne_zero.1 h2.pos
    have e : (2 ^ a) ^ 3 = 2 ^ (3 * a) := by rw [← pow_mul, mul_comm]
    rw [padicValNat.mul (by positivity) hne2, padicValNat.mul (by positivity) hne3,
      padicValNat.eq_zero_of_not_dvd
        (fun hd => (Nat.not_even_iff_odd.2 h3) (even_iff_two_dvd.2 hd)),
      padicValNat.eq_zero_of_not_dvd
        (fun hd => (Nat.not_even_iff_odd.2 h2) (even_iff_two_dvd.2 hd)),
      e, padicValNat.prime_pow]
    ring
  have := congrArg (padicValNat 2) h
  rw [hv hm, hv hm'] at this
  omega

variable {G : Type} [Group G]

@[expose] noncomputable def quotEquivOf {K : Subgroup G} {Γ : Type*} [Group Γ] {α : ↥K →* Γ}
    (hα : Function.Surjective α) (hker : α.ker = CFSG.pCore 2 ↥K) :
    (↥K ⧸ CFSG.pCore 2 ↥K) ≃* Γ :=
  (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective α hα)

theorem quotEquivOf_mk {K : Subgroup G} {Γ : Type*} [Group Γ] {α : ↥K →* Γ}
    (hα : Function.Surjective α) (hker : α.ker = CFSG.pCore 2 ↥K) (l : ↥K) :
    quotEquivOf hα hker (QuotientGroup.mk l) = α l := rfl

theorem natOn_of_isSumVia_one {K W : Subgroup G} {F : Type} [Field F]
    {α : ↥K →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)} (hα : Function.Surjective α)
    (hker : α.ker = CFSG.pCore 2 ↥K) (h : IsSumOfNaturalModulesVia K W ⊥ α false 1) :
    Vol2.Ch11.SecA.NatOn K W F (quotEquivOf hα hker) := by
  obtain ⟨-, -, β, hβs, hβker, hβeq⟩ := h
  have hβi : Function.Injective β := by
    rw [← MonoidHom.ker_eq_bot_iff, hβker, Subgroup.bot_subgroupOf]
  let θ₀ : ↥W →* Multiplicative (Fin 3 → F) :=
    { toFun := fun w => Multiplicative.ofAdd ((Multiplicative.toAdd (β w)) 0)
      map_one' := by simp
      map_mul' := fun v w => by simp [map_mul] }
  have hθ₀ : Function.Bijective θ₀ := by
    refine ⟨fun v w hvw => hβi ?_, fun f => ?_⟩
    · apply Multiplicative.toAdd.injective
      funext i
      have hi : i = 0 := Subsingleton.elim i 0
      subst hi
      exact Multiplicative.ofAdd.injective hvw
    · obtain ⟨w, hw⟩ := hβs (Multiplicative.ofAdd fun _ => Multiplicative.toAdd f)
      exact ⟨w, by simp [θ₀, hw]⟩
  refine ⟨MulEquiv.ofBijective θ₀ hθ₀, fun l w hw => ?_⟩
  have h1 := hβeq l w ⟨_, hw⟩ rfl 0
  simp only [MulEquiv.ofBijective_apply, MonoidHom.coe_mk, OneHom.coe_mk, θ₀, quotEquivOf_mk]
  rw [h1]
  simp [moduleAct]

theorem natOn_of_isNaturalSection {K W : Subgroup G} {F : Type} [Field F]
    {α : ↥K →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)} (hα : Function.Surjective α)
    (hker : α.ker = CFSG.pCore 2 ↥K) {β : ↥W →* Multiplicative (Fin 3 → F)}
    (hβs : Function.Surjective β) (hβker : β.ker = (⊥ : Subgroup G).subgroupOf W)
    (hβeq : ∀ (a : ↥K) (u v : ↥W), (v : G) = a * u * a⁻¹ →
      Multiplicative.toAdd (β v) =
        ((α a : Matrix.GeneralLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec
          (Multiplicative.toAdd (β u))) :
    Vol2.Ch11.SecA.NatOn K W F (quotEquivOf hα hker) := by
  have hβi : Function.Injective β := by
    rw [← MonoidHom.ker_eq_bot_iff, hβker, Subgroup.bot_subgroupOf]
  refine ⟨MulEquiv.ofBijective β ⟨hβi, hβs⟩, fun l w hw => ?_⟩
  show β ⟨_, hw⟩ = Multiplicative.ofAdd
    (Matrix.mulVec
      ((((quotEquivOf hα hker (QuotientGroup.mk l)) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F))
      (Multiplicative.toAdd (β w)))
  rw [quotEquivOf_mk, ← hβeq l w ⟨_, hw⟩ rfl]
  rfl

@[expose] def prCoord {k : ℕ} {X : Type*} [AddCommGroup X] (j : Fin k) :
    Multiplicative (Fin k → X) →* Multiplicative X where
  toFun f := Multiplicative.ofAdd (Multiplicative.toAdd f j)
  map_one' := rfl
  map_mul' _ _ := rfl

@[expose] def natSummand {W : Subgroup G} {X : Type*} [AddCommGroup X]
    (β : ↥W →* Multiplicative (Fin 2 → X)) (j : Fin 2) : Subgroup G :=
  ((prCoord j.rev).comp β).ker.map W.subtype

theorem mem_natSummand {W : Subgroup G} {X : Type*} [AddCommGroup X]
    {β : ↥W →* Multiplicative (Fin 2 → X)} {j : Fin 2} {v : G} :
    v ∈ natSummand β j ↔ ∃ hv : v ∈ W, Multiplicative.toAdd (β ⟨v, hv⟩) j.rev = 0 := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w.2, by simpa [prCoord] using hw⟩
  · rintro ⟨hv, h⟩
    exact ⟨⟨v, hv⟩, by simpa [prCoord] using h, rfl⟩

theorem natSummand_le {W : Subgroup G} {X : Type*} [AddCommGroup X]
    (β : ↥W →* Multiplicative (Fin 2 → X)) (j : Fin 2) : natSummand β j ≤ W := by
  rintro _ ⟨w, -, rfl⟩
  exact w.2

omit [Group G] in
theorem fin2_ext_rev {X : Type*} {f g : Fin 2 → X} (j : Fin 2) (h1 : f j = g j)
    (h2 : f j.rev = g j.rev) : f = g := by
  funext i
  fin_cases j <;> fin_cases i <;> simp_all [Fin.rev]

theorem le_normalizer_of_conj_mem_line {K W : Subgroup G}
    (h : ∀ k ∈ K, ∀ w ∈ W, k * w * k⁻¹ ∈ W) : K ≤ normalizer (W : Set G) := by
  intro k hk
  rw [mem_normalizer_iff]
  intro w
  refine ⟨h k hk w, fun hw => ?_⟩
  have := h k⁻¹ (K.inv_mem hk) _ hw
  simpa [mul_assoc] using this

theorem natOn_of_isSumVia_two {K W : Subgroup G} {F : Type} [Field F]
    {α : ↥K →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)} (hα : Function.Surjective α)
    (hker : α.ker = CFSG.pCore 2 ↥K) (h : IsSumOfNaturalModulesVia K W ⊥ α false 2) :
    ∃ W₀ W₁ : Subgroup G, K ≤ normalizer (W₀ : Set G) ∧ K ≤ normalizer (W₁ : Set G) ∧
      W₀ ⊔ W₁ = W ∧ W₀ ⊓ W₁ = ⊥ ∧ Vol2.Ch11.SecA.NatOn K W₀ F (quotEquivOf hα hker) ∧
      Vol2.Ch11.SecA.NatOn K W₁ F (quotEquivOf hα hker) := by
  obtain ⟨hKW, -, β, hβs, hβker, hβeq⟩ := h
  have hβi : Function.Injective β := by
    rw [← MonoidHom.ker_eq_bot_iff, hβker, Subgroup.bot_subgroupOf]
  have hmA : ∀ g : Matrix.GeneralLinearGroup (Fin 3) F,
      moduleAct false g = (g : Matrix (Fin 3) (Fin 3) F) := fun g => by simp [moduleAct]
  have hnorm : ∀ j : Fin 2, K ≤ normalizer (natSummand β j : Set G) := by
    intro j
    refine le_normalizer_of_conj_mem_line fun k hk v hv => ?_
    obtain ⟨hvW, hv0⟩ := mem_natSummand.1 hv
    have hkv : k * v * k⁻¹ ∈ W := (mem_normalizer_iff.1 (hKW hk) v).1 hvW
    refine mem_natSummand.2 ⟨hkv, ?_⟩
    rw [hβeq ⟨k, hk⟩ ⟨v, hvW⟩ ⟨_, hkv⟩ rfl j.rev, hv0, hmA, Matrix.mulVec_zero]
  have hnat : ∀ j : Fin 2,
      Vol2.Ch11.SecA.NatOn K (natSummand β j) F (quotEquivOf hα hker) := by
    intro j
    let θ₀ : ↥(natSummand β j) →* Multiplicative (Fin 3 → F) :=
      { toFun := fun v => Multiplicative.ofAdd
          (Multiplicative.toAdd (β ⟨v, natSummand_le β j v.2⟩) j)
        map_one' := by
          show Multiplicative.ofAdd (Multiplicative.toAdd (β 1) j) = 1
          rw [map_one]
          rfl
        map_mul' := fun v w => by
          show Multiplicative.ofAdd (Multiplicative.toAdd
              (β (⟨v, natSummand_le β j v.2⟩ * ⟨w, natSummand_le β j w.2⟩)) j) =
            Multiplicative.ofAdd (Multiplicative.toAdd (β ⟨v, natSummand_le β j v.2⟩) j) *
              Multiplicative.ofAdd (Multiplicative.toAdd (β ⟨w, natSummand_le β j w.2⟩) j)
          rw [map_mul]
          rfl }
    have hθ₀ : Function.Bijective θ₀ := by
      refine ⟨fun v w hvw => ?_, fun f => ?_⟩
      · have hv0 := (mem_natSummand.1 v.2).2
        have hw0 := (mem_natSummand.1 w.2).2
        have h1 : β ⟨v, natSummand_le β j v.2⟩ = β ⟨w, natSummand_le β j w.2⟩ := by
          apply Multiplicative.toAdd.injective
          refine fin2_ext_rev j (Multiplicative.ofAdd.injective hvw) ?_
          rw [hv0, hw0]
        have h2 := hβi h1
        exact Subtype.ext (congrArg (fun x : ↥W => (x : G)) h2)
      · obtain ⟨w, hw⟩ := hβs (Multiplicative.ofAdd (Pi.single j (Multiplicative.toAdd f)))
        have hjr : j.rev ≠ j := by fin_cases j <;> decide
        have hwj : (w : G) ∈ natSummand β j := by
          refine mem_natSummand.2 ⟨w.2, ?_⟩
          have : (⟨(w : G), w.2⟩ : ↥W) = w := rfl
          rw [this, hw]
          simp [hjr]
        refine ⟨⟨w, hwj⟩, ?_⟩
        have : (⟨(w : G), natSummand_le β j hwj⟩ : ↥W) = w := rfl
        simp [θ₀, this, hw]
    refine ⟨MulEquiv.ofBijective θ₀ hθ₀, fun l w hw => ?_⟩
    simp only [MulEquiv.ofBijective_apply, MonoidHom.coe_mk, OneHom.coe_mk, θ₀, quotEquivOf_mk]
    rw [hβeq l ⟨w, natSummand_le β j w.2⟩ ⟨_, natSummand_le β j hw⟩ rfl j, hmA]
    rfl
  refine ⟨natSummand β 0, natSummand β 1, hnorm 0, hnorm 1, le_antisymm ?_ ?_, ?_, hnat 0, hnat 1⟩
  · exact sup_le (natSummand_le β 0) (natSummand_le β 1)
  · intro v hv
    set f := Multiplicative.toAdd (β ⟨v, hv⟩) with hf
    obtain ⟨w₀, hw₀⟩ := hβs (Multiplicative.ofAdd (Pi.single 0 (f 0)))
    obtain ⟨w₁, hw₁⟩ := hβs (Multiplicative.ofAdd (Pi.single 1 (f 1)))
    have h0 : (w₀ : G) ∈ natSummand β 0 := by
      refine mem_natSummand.2 ⟨w₀.2, ?_⟩
      have : (⟨(w₀ : G), w₀.2⟩ : ↥W) = w₀ := rfl
      rw [this, hw₀]
      simp
    have h1 : (w₁ : G) ∈ natSummand β 1 := by
      refine mem_natSummand.2 ⟨w₁.2, ?_⟩
      have : (⟨(w₁ : G), w₁.2⟩ : ↥W) = w₁ := rfl
      rw [this, hw₁]
      simp
    have hvw : (⟨v, hv⟩ : ↥W) = w₀ * w₁ := by
      apply hβi
      rw [map_mul, hw₀, hw₁]
      apply Multiplicative.toAdd.injective
      funext i
      fin_cases i <;> simp [hf]
    have : v = (w₀ : G) * w₁ := congrArg Subtype.val hvw
    rw [this]
    exact mul_mem_sup h0 h1
  · rw [eq_bot_iff]
    intro v ⟨h0, h1⟩
    obtain ⟨hvW, hv0⟩ := mem_natSummand.1 h0
    obtain ⟨hvW', hv1⟩ := mem_natSummand.1 h1
    have : β ⟨v, hvW⟩ = 1 := by
      apply Multiplicative.toAdd.injective
      funext i
      fin_cases i
      · simpa using hv1
      · simpa using hv0
    have h2 := hβi (this.trans (map_one β).symm)
    exact (Subgroup.mem_bot).2 (congrArg Subtype.val h2)

theorem isElemAbelian_of_injective_line {W : Subgroup G} {A : Type*} [AddCommGroup A]
    (h2 : ∀ a : A, a + a = 0) (β : ↥W →* Multiplicative A) (hβ : Function.Injective β) :
    IsElemAbelian 2 W := by
  refine ⟨⟨⟨fun a b => hβ ?_⟩⟩, fun x hx => ?_⟩
  · rw [map_mul, map_mul, mul_comm]
  · have h1 : β ⟨x, hx⟩ ^ 2 = 1 := by
      rw [pow_two]
      apply Multiplicative.toAdd.injective
      exact h2 _
    have h3 : (⟨x, hx⟩ : ↥W) ^ 2 = 1 := hβ (by rw [map_pow, h1, map_one])
    simpa using congrArg Subtype.val h3

omit [Group G] in
theorem add_self_eq_zero_line {F : Type} [Field F] [CharP F 2] {k : ℕ}
    (a : Fin k → Fin 3 → F) : a + a = 0 := by
  funext i j
  simp only [Pi.add_apply, Pi.zero_apply]
  exact CharTwo.add_self_eq_zero (a i j)

omit [Group G] in
theorem add_self_eq_zero_line' {F : Type} [Field F] [CharP F 2] (a : Fin 3 → F) : a + a = 0 := by
  funext j
  simp only [Pi.add_apply, Pi.zero_apply]
  exact CharTwo.add_self_eq_zero (a j)

theorem mem_normalizer_commutator_line {A B : Subgroup G} {g : G}
    (hA : g ∈ normalizer (A : Set G)) (hB : g ∈ normalizer (B : Set G)) :
    g ∈ normalizer ((⁅A, B⁆ : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hA hB ⊢
  rw [Subgroup.map_commutator, hA, hB]

theorem commutator_le_of_le_normalizer_line {A K : Subgroup G}
    (hA : A ≤ normalizer (K : Set G)) : ⁅A, K⁆ ≤ K := by
  rw [Subgroup.commutator_le]
  intro a ha k hk
  rw [commutatorElement_def]
  exact K.mul_mem ((mem_normalizer_iff.1 (hA ha) k).1 hk) (K.inv_mem hk)

theorem even_of_quot_statedSL3 {K : Subgroup G} {F F' : Type} [Field F] [Fintype F] [Field F']
    [Fintype F'] {n n' : ℕ} (hn : Even n) (hn1 : 1 ≤ n) (hcard : Fintype.card F = 2 ^ n)
    (hcard' : Fintype.card F' = 2 ^ n')
    {α : ↥K →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)} (hα : Function.Surjective α)
    (hker : α.ker = CFSG.pCore 2 ↥K)
    {α' : ↥K →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F')} (hα' : Function.Surjective α')
    (hker' : α'.ker = CFSG.pCore 2 ↥K) : Even n' := by
  have hn'1 : 1 ≤ n' := by
    rcases Nat.eq_zero_or_pos n' with h | h
    · have h1 : 1 < Fintype.card F' := Fintype.one_lt_card
      rw [hcard', h, pow_zero] at h1
      omega
    · exact h
  have hc := Nat.card_congr ((quotEquivOf hα' hker').symm.trans (quotEquivOf hα hker)).toEquiv
  rw [eq_of_card_statedSL3_eq hn'1 hn1 hcard' hcard hc]
  exact hn

theorem mem_of_a319_line [Finite G] (hF318 : A318Facts) (h36 : A36ForSQTK) (h38 : A38ForSQTK)
    {N K W : Subgroup G} (hN : SQTKGroup ↥N) (hK : K ∈ cComp N) {x : G} (hxN : x ∈ N)
    (hx3 : orderOf x = 3) (hWK : W ≤ K) (hKW : K ≤ normalizer (W : Set G))
    (hxW : x ∈ normalizer (W : Set G)) (hW : IsElemAbelian 2 W)
    (hHyp : ∀ H : Subgroup G, K ≤ H → W ≤ H → A319Hyp (K.subgroupOf H) (W.subgroupOf H)) :
    x ∈ K := by
  have hKN : K ≤ N := le_of_mem_cComp hK
  set H := K ⊔ zpowers x with hHdef
  have hHN : H ≤ N := sup_le hKN (zpowers_le.2 hxN)
  have hSQ : SQTKGroup ↥H := B5.sqtk_of_le hN hHN
  have hSQ' := SQTKHyp.of_sqtkGroup ↥H hSQ
  have hKH' : K ∈ cComp H := cComp_mem_of_le hK le_sup_left hHN
  have hHW : H ≤ normalizer (W : Set G) := sup_le hKW (zpowers_le.2 hxW)
  have hn : (W.subgroupOf H).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hHW
  have hab : IsElemAbelian 2 (W.subgroupOf H) := Vol2.Ch11.SecA.isElemAbelian_subgroupOf hW
  have h1 := a319 hF318 Vol2.Ch10.a319Facts_holds hSQ (h36 _ hSQ') (h38 _ hSQ')
    (subgroupOf_mem_cComp hKH') hn hab (hHyp H le_sup_left (hWK.trans le_sup_left))
  have hxH : x ∈ H := mem_sup_right (mem_zpowers x)
  have hx' : (⟨x, hxH⟩ : ↥H) ∈ oPrimeResidualOf 3 (⊤ : Subgroup ↥H) :=
    mem_oPrimeResidualOf_of_orderOf_three (Subgroup.mem_top _)
      (by rw [Subgroup.orderOf_mk]; exact hx3)
  rw [← h1] at hx'
  exact Subgroup.mem_subgroupOf.1 hx'

end CFSG.Quasithin.H13.U3.NLine
