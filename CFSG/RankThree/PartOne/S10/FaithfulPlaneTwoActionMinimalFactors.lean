module

public import CFSG.RankThree.PartOne.S10.PlaneContract
import CFSG.GroupTheory.HyperplaneGeneration
import CFSG.GroupTheory.ThompsonAxB
import CFSG.RankThree.GroupTheory.SteinbergBYMinimalCoprimeAction
import CFSG.RankThree.GroupTheory.SteinbergBMRelativeMinimalFrattini

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.GroupTheory.SteinbergBM
open scoped commutatorElement Pointwise

namespace PlaneFactors
variable {B S : Type} [Group B] [Group S] [MulDistribMulAction B S]

theorem isActionInvariant_sup {U V : Subgroup S} (hU : IsActionInvariant B U)
    (hV : IsActionInvariant B V) : IsActionInvariant B (U ⊔ V) := by
  intro b x hx
  have hle : U ⊔ V ≤ (U ⊔ V).comap (MulDistribMulAction.toMonoidHom S b) :=
    sup_le (fun u hu => le_sup_left (a := U) (b := V) (hU b u hu))
      (fun v hv => le_sup_right (a := U) (b := V) (hV b v hv))
  exact hle hx

theorem isActionInvariant_inf {U V : Subgroup S} (hU : IsActionInvariant B U)
    (hV : IsActionInvariant B V) : IsActionInvariant B (U ⊓ V) :=
  fun b x hx => ⟨hU b x hx.1, hV b x hx.2⟩

theorem isActionInvariant_fixedPointSubgroup_zpowers (hcomm : ∀ x y : B, x * y = y * x) (c : B) :
    IsActionInvariant B (CFSG.fixedPointSubgroup (Subgroup.zpowers c) S) := by
  intro b x hx
  rw [SolvableHall.mem_fixedPointSubgroup_zpowers_iff] at hx ⊢
  rw [← mul_smul, hcomm c b, mul_smul, hx]

theorem isActionInvariant_centralizer {X : Subgroup S} (hX : IsActionInvariant B X) :
    IsActionInvariant B (Subgroup.centralizer (X : Set S)) := by
  intro b x hx
  rw [Subgroup.mem_centralizer_iff] at hx ⊢
  intro y hy
  have h := congrArg (fun z => b • z) (hx (b⁻¹ • y) (hX b⁻¹ y hy))
  simpa [smul_mul', smul_inv_smul] using h

variable {B S : Type} [Group B] [Group S] [MulDistribMulAction B S]

theorem le_of_centralizers_le {p : ℕ} [Fact p.Prime] [Finite B] [Finite S]
    [IsElementaryAbelian p B] (hB : p ^ 2 ≤ Nat.card B) {U : Subgroup S}
    (hU : IsActionInvariant B U) (hpU : ¬ p ∣ Nat.card U) {F : Subgroup S}
    (hF : ∀ b : B, b ≠ 1 → U ⊓ CFSG.fixedPointSubgroup (Subgroup.zpowers b) S ≤ F) : U ≤ F := by
  have : CFSG.IsInvariant B S U := SolvableHall.isInvariant_of_forall_smul_mem hU
  have hgen := SolvableHall.coprime_centralizer_generation (p := p) (A := B) (H := U) hB hpU
  have hle : (⊤ : Subgroup U).map U.subtype ≤ F := by
    rw [← hgen, Subgroup.map_iSup]
    refine iSup_le fun b => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hb => ?_
    rintro _ ⟨y, hy, rfl⟩
    have h1 := (SolvableHall.mem_fixedPointSubgroup_zpowers_iff b y).mp hy
    refine hF b hb (Subgroup.mem_inf.mpr ⟨y.2, ?_⟩)
    rw [SolvableHall.mem_fixedPointSubgroup_zpowers_iff]
    exact congrArg Subtype.val h1
  intro x hx
  exact hle ⟨⟨x, hx⟩, Subgroup.mem_top _, rfl⟩

theorem exists_mul_of_invariant_isPGroup {l : ℕ} (hl : l.Prime) [Finite B] [Finite S]
    {U : Subgroup S} (hUl : IsPGroup l U) (hB : ¬ l ∣ Nat.card B)
    (hU : IsActionInvariant B U) {x : S} (hx : x ∈ U) :
    ∃ d ∈ actionCommutator B U, ∃ c ∈ U, (∀ a : B, a • c = c) ∧ x = d * c := by
  have : CFSG.IsInvariant B S U := SolvableHall.isInvariant_of_forall_smul_mem hU
  obtain ⟨d, hd, c, hc, hdc⟩ :=
    (coprime_pgroup_commutator_factorization (A := B) (Q := U) hl hUl hB).1 ⟨x, hx⟩
  have hsub : ∀ (a : B) (y : U), U.subtype (a • y) = a • U.subtype y := fun _ _ => rfl
  have hUtop : (⊤ : Subgroup U).map U.subtype = U := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  refine ⟨(d : S), ?_, (c : S), c.2, fun a => congrArg Subtype.val (hc a), ?_⟩
  · have h : (d : S) ∈ (actionCommutator B (⊤ : Subgroup U)).map U.subtype := ⟨d, hd, rfl⟩
    rwa [map_actionCommutator U.subtype hsub, hUtop] at h
  · exact congrArg Subtype.val hdc

section Order

variable {p : ℕ} {B : Type} [Group B]

theorem card_zpowers_of_ne_one (hp : p.Prime) (hB : IsElementaryAbelian p B) {b : B}
    (hb : b ≠ 1) : Nat.card (Subgroup.zpowers b) = p := by
  have : Fact p.Prime := ⟨hp⟩
  have hpow : b ^ p = 1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p p B) b
  rw [Nat.card_zpowers, orderOf_eq_prime hpow hb]

theorem zpowers_eq_of_mem [Finite B] (hp : p.Prime) (hB : IsElementaryAbelian p B) {x y : B}
    (hx : x ≠ 1) (hy : y ≠ 1) (hxy : y ∈ Subgroup.zpowers x) :
    Subgroup.zpowers y = Subgroup.zpowers x :=
  Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hxy)
    (by rw [card_zpowers_of_ne_one hp hB hx, card_zpowers_of_ne_one hp hB hy])

theorem zpowers_inf_zpowers_eq_bot [Finite B] (hp : p.Prime) (hB : IsElementaryAbelian p B)
    {x y : B} (hx : x ≠ 1) (hy : y ∉ Subgroup.zpowers x) :
    Subgroup.zpowers x ⊓ Subgroup.zpowers y = ⊥ := by
  rw [eq_bot_iff]
  intro c hc
  rw [Subgroup.mem_bot]
  by_contra hc1
  have hy1 : y ≠ 1 := fun h => hy (h ▸ Subgroup.one_mem _)
  have h1 : Subgroup.zpowers c = Subgroup.zpowers x := zpowers_eq_of_mem hp hB hx hc1 hc.1
  have h2 : Subgroup.zpowers c = Subgroup.zpowers y := zpowers_eq_of_mem hp hB hy1 hc1 hc.2
  have h3 : Subgroup.zpowers x = Subgroup.zpowers y := h1.symm.trans h2
  exact hy (h3 ▸ Subgroup.mem_zpowers y)

end Order

section Kernel

variable {p : ℕ} {B S : Type} [Group B] [Group S] [MulDistribMulAction B S] [Finite B]

theorem fixes_iff_mem_zpowers (hp : p.Prime) (hB : IsElementaryAbelian p B)
    (hBcard : Nat.card B = p ^ 2) {V : Subgroup S} (hVne : V ≠ ⊥)
    (hVc : actionCommutator B V = V) {b : B} (hb : b ≠ 1) (hbV : ∀ x ∈ V, b • x = x) (c : B) :
    (∀ x ∈ V, c • x = x) ↔ c ∈ Subgroup.zpowers b := by
  have : Fact p.Prime := ⟨hp⟩
  have hmemK : ∀ c : B, c ∈ fixingSubgroup B (V : Set S) ↔ ∀ x ∈ V, c • x = x := fun c =>
    mem_fixingSubgroup_iff B
  set K : Subgroup B := fixingSubgroup B (V : Set S) with hK
  have hzK : Subgroup.zpowers b ≤ K := by
    intro c hc
    rw [hmemK]
    intro x hx
    have hxf : x ∈ CFSG.fixedPointSubgroup (Subgroup.zpowers b) S :=
      (SolvableHall.mem_fixedPointSubgroup_zpowers_iff b x).mpr (hbV x hx)
    exact hxf ⟨c, hc⟩
  have hKtop : K ≠ ⊤ := by
    intro h
    apply hVne
    have hle : actionCommutator B V ≤ ⊥ := by
      refine (Subgroup.closure_le _).2 ?_
      rintro _ ⟨x, hx, d, rfl⟩
      have hd : d ∈ K := h ▸ Subgroup.mem_top d
      rw [(hmemK d).1 hd x hx, inv_mul_cancel]
      exact one_mem _
    rw [hVc] at hle
    exact le_bot_iff.mp hle
  have hKle : K ≤ Subgroup.zpowers b := by
    have hdvd : Nat.card K ∣ p ^ 2 := hBcard ▸ Subgroup.card_subgroup_dvd_card K
    obtain ⟨i, hi, hKi⟩ := (Nat.dvd_prime_pow hp).1 hdvd
    have hpK : p ∣ Nat.card K :=
      (card_zpowers_of_ne_one hp hB hb) ▸ Subgroup.card_dvd_of_le hzK
    interval_cases i
    · exfalso
      rw [pow_zero] at hKi
      rw [hKi] at hpK
      exact hp.one_lt.ne' (Nat.dvd_one.mp hpK)
    · exact (Subgroup.eq_of_le_of_card_ge hzK
        (by rw [hKi, card_zpowers_of_ne_one hp hB hb, pow_one])).ge
    · exfalso
      exact hKtop ((Subgroup.card_eq_iff_eq_top K).1 (by rw [hKi, hBcard]))
  constructor
  · intro hc
    exact hKle ((hmemK c).2 hc)
  · intro hc
    exact (hmemK c).1 (hzK hc)

end Kernel

section Factor

variable {B S : Type} [Group B] [Group S] [MulDistribMulAction B S] [Finite B] [Finite S]

theorem minimalPlaneFactor_of_minimal (hS : IsPGroup 2 S) (hB : ¬ 2 ∣ Nat.card B)
    {X : Subgroup S} (hXinv : IsActionInvariant B X) (hXne : X ≠ ⊥)
    (hXc : actionCommutator B X = X)
    (hmin : ∀ U : Subgroup S, U < X → IsActionInvariant B U → ActionCentralizes B U) :
    MinimalPlaneFactor B X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CFSG.IsInvariant B S X := SolvableHall.isInvariant_of_forall_smul_mem hXinv
  have hnt : ∃ (a : B) (q : X), a • q ≠ q := by
    by_contra hcon
    push Not at hcon
    apply hXne
    rw [← hXc, eq_bot_iff]
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨x, hx, a, rfl⟩
    have h2 : a • x = x := congrArg Subtype.val (hcon a ⟨x, hx⟩)
    rw [h2, inv_mul_cancel]
    exact one_mem _
  have hminX : ∀ R : Subgroup X, R ≠ ⊤ → (∀ (a : B), ∀ r ∈ R, a • r ∈ R) →
      ∀ (a : B), ∀ r ∈ R, a • r = r := by
    intro R hR hRinv a r hr
    have hlt : R.map X.subtype < X := by
      refine lt_of_le_of_ne (Subgroup.map_subtype_le R) ?_
      intro h
      apply hR
      rw [← Subgroup.comap_map_eq_self_of_injective X.subtype_injective R, h]
      exact Subgroup.subgroupOf_self X
    have hinv : IsActionInvariant B (R.map X.subtype) := by
      rintro b _ ⟨r', hr', rfl⟩
      exact ⟨b • r', hRinv b r' hr', rfl⟩
    exact Subtype.ext (hmin _ hlt hinv a (r : S) ⟨r, hr, rfl⟩)
  have hmain := CFSG.RankThree.GroupTheory.SteinbergBY.minimal_coprime_action_elementary_or_special
    (A := B) (P := X) (l := 2) (hS.to_subgroup X) hB hnt hminX
  let := CFSG.RankThree.GroupTheory.SteinbergBY.frattiniQuotientAction B X
  obtain ⟨-, -, ⟨-, -, hVnontriv, hVirr⟩, habel, hnonab⟩ := hmain
  refine ⟨hXinv, hXc, hmin, ?_, ?_, ?_⟩
  · obtain ⟨a, v, hv⟩ := hVnontriv
    obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective v
    refine ⟨a, q, q.2, fun hmem => ?_⟩
    obtain ⟨y, hy, hyeq⟩ := hmem
    have hyq : y = (a • q)⁻¹ * q := Subtype.ext hyeq
    apply hv
    change ((a • q : X) : X ⧸ frattini X) = (q : X ⧸ frattini X)
    rw [QuotientGroup.eq, ← hyq]
    exact hy
  · intro Y hΦY hYX hYinv
    set Φ := frattini X with hΦ
    set W : Subgroup X := Y.comap X.subtype with hW
    have hΦW : Φ ≤ W := fun y hy => hΦY ⟨y, hy, rfl⟩
    have hWinv : ∀ (a : B), ∀ w ∈ W, a • w ∈ W := fun a w hw => hYinv a (w : S) hw
    set W' : Subgroup (X ⧸ Φ) := W.map (QuotientGroup.mk' Φ) with hW'
    have hW'inv : ∀ (a : B), ∀ s ∈ W', a • s ∈ W' := by
      rintro a _ ⟨w, hw, rfl⟩
      exact ⟨a • w, hWinv a w hw, rfl⟩
    rcases hVirr W' hW'inv with h | h
    · left
      have hWΦ : W = Φ := by
        refine le_antisymm ?_ hΦW
        have h1 := (Subgroup.map_eq_bot_iff _).1 h
        rwa [QuotientGroup.ker_mk'] at h1
      apply le_antisymm
      · intro y hy
        have hmem : (⟨y, hYX hy⟩ : X) ∈ W := hy
        rw [hWΦ] at hmem
        exact ⟨_, hmem, rfl⟩
      · exact hΦY
    · right
      have hWtop : W = ⊤ := by
        rw [eq_top_iff]
        intro w _
        have hw : (w : X ⧸ Φ) ∈ W' := h ▸ Subgroup.mem_top _
        obtain ⟨w', hw', hw'eq⟩ := hw
        have h2 : w'⁻¹ * w ∈ Φ := QuotientGroup.eq.mp hw'eq
        have h3 := W.mul_mem hw' (hΦW h2)
        rwa [mul_inv_cancel_left] at h3
      refine le_antisymm hYX fun x hx => ?_
      have : (⟨x, hx⟩ : X) ∈ W := hWtop ▸ Subgroup.mem_top _
      exact this
  · by_cases hab : IsMulCommutative X
    · exact Or.inl (habel hab).2
    · right
      obtain ⟨hcf, hfc, hcne, hcel, hfix⟩ := hnonab hab
      have hfel : IsElementaryAbelian 2 ↥(frattini X) := by
        rw [← hcf]
        exact hcel
      have : IsElementaryAbelian 2 ↥(frattini X) := hfel
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · rw [← Subgroup.map_subtype_commutator X, hcf]
        rfl
      · show (frattini X).map X.subtype = (Subgroup.center X).map X.subtype
        rw [hfc]
      · intro hbot
        have h1 : frattini X = ⊥ :=
          (Subgroup.map_eq_bot_iff_of_injective (frattini X) X.subtype_injective).1 hbot
        exact hcne (hcf.trans h1)
      · exact IsElementaryAbelian.map_subtype (H := frattini X)
      · rintro b _ ⟨y, hy, rfl⟩
        have hy' : y ∈ Subgroup.center X := hfc ▸ hy
        exact congrArg Subtype.val (hfix b y hy')

end Factor

section Main

variable {p : ℕ} {B S : Type} [Group B] [Group S] [MulDistribMulAction B S] [Finite B] [Finite S]

omit [Group S] [MulDistribMulAction B S] [Finite B] [Finite S] in
theorem not_dvd_card_of_isPGroup_two (hp : p.Prime) (hp2 : p ≠ 2) {U : Type} [Group U] [Finite U]
    (hU : IsPGroup 2 U) : ¬ p ∣ Nat.card U := by
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hU
  rw [hk]
  intro h
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h))

omit [Group S] [MulDistribMulAction B S] [Finite B] [Finite S] in
theorem not_two_dvd_card_of_card_eq (hp : p.Prime) (hp2 : p ≠ 2) {C : Type} [Group C]
    (hC : Nat.card C = p ^ 2) : ¬ 2 ∣ Nat.card C := by
  rw [hC]
  intro h
  exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp
    (Nat.prime_two.dvd_of_dvd_pow h)).symm

theorem commutator_properties (hS : IsPGroup 2 S) (hB : ¬ 2 ∣ Nat.card B) {X : Subgroup S}
    (hX : IsActionInvariant B X) :
    actionCommutator B X ≤ X ∧ IsActionInvariant B (actionCommutator B X) ∧
      actionCommutator B (actionCommutator B X) = actionCommutator B X :=
  ⟨actionCommutator_le_of_invariant hX,
    fun b _ hx => smul_mem_actionCommutator_of_invariant hX b hx,
    actionCommutator_actionCommutator_of_isPGroup Nat.prime_two (hS.to_subgroup X) hB hX⟩

theorem exists_commutator_line (hp : p.Prime) (hp2 : p ≠ 2) (hB : IsElementaryAbelian p B)
    (hBcard : Nat.card B = p ^ 2) (hS : IsPGroup 2 S) {U : Subgroup S}
    (hUinv : IsActionInvariant B U) (hUfaith : ∀ c : B, (∀ x ∈ U, c • x = x) → c = 1) :
    ∃ b : B, b ≠ 1 ∧
      actionCommutator B (U ⊓ CFSG.fixedPointSubgroup (Subgroup.zpowers b) S) ≠ ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  have := hB
  by_contra hcon
  push Not at hcon
  have hle : U ≤ CFSG.fixedPointSubgroup B S := by
    refine le_of_centralizers_le (p := p) (by rw [hBcard]) hUinv
      (not_dvd_card_of_isPGroup_two hp hp2 (hS.to_subgroup U)) ?_
    intro b hb x hx c
    have h := gen_mem_actionCommutator (A := B) hx c
    rw [hcon b hb, Subgroup.mem_bot, inv_mul_eq_one] at h
    exact h.symm
  have hnt : Nontrivial B := by
    rw [← Finite.one_lt_card_iff_nontrivial, hBcard]
    exact Nat.one_lt_pow two_ne_zero hp.one_lt
  obtain ⟨c, hc⟩ := exists_ne (1 : B)
  exact hc (hUfaith c fun x hx => hle hx c)

theorem not_le_fixed_of_commuting (hp : p.Prime) (hp2 : p ≠ 2) (hB : IsElementaryAbelian p B)
    (hS : IsPGroup 2 S) {S₀ S₁ : Subgroup S} (hS₀inv : IsActionInvariant B S₀) (hS₁S₀ : S₁ ≤ S₀)
    (hS₀faith : ∀ c : B, (∀ x ∈ S₀, c • x = x) → c = 1) {b : B} (hb : b ≠ 1)
    (hker : ∀ c : B, (∀ x ∈ S₁, c • x = x) ↔ c ∈ Subgroup.zpowers b) :
    ¬ (S₀ ⊓ Subgroup.centralizer (S₁ : Set S) ≤
      CFSG.fixedPointSubgroup (Subgroup.zpowers b) S) := by
  intro hle
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CFSG.IsInvariant B S S₀ := SolvableHall.isInvariant_of_forall_smul_mem hS₀inv
  let α : Subgroup.zpowers b →* MulAut S₀ :=
    (MulDistribMulAction.toMulAut B S₀).comp (Subgroup.zpowers b).subtype
  let β : S₁ →* MulAut S₀ := (MulAut.conj : S₀ →* MulAut S₀).comp (Subgroup.inclusion hS₁S₀)
  have hαfix : ∀ (a : Subgroup.zpowers b) (s : S), s ∈ S₁ → (a : B) • s = s :=
    fun a s hs => (hker a).2 a.2 s hs
  have hcomm : ∀ a x, α a * β x = β x * α a := by
    intro a x
    refine MulEquiv.ext fun r => Subtype.ext ?_
    show (a : B) • ((x : S) * (r : S) * (x : S)⁻¹) = (x : S) * ((a : B) • (r : S)) * (x : S)⁻¹
    rw [smul_mul', smul_mul', smul_inv', hαfix a x x.2]
  have hfix : ∀ (a : Subgroup.zpowers b) (r : S₀), (∀ x, β x r = r) → α a r = r := by
    intro a r hr
    have hcent : (r : S) ∈ Subgroup.centralizer (S₁ : Set S) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have h := congrArg Subtype.val (hr ⟨y, hy⟩)
      change (y : S) * (r : S) * (y : S)⁻¹ = (r : S) at h
      simpa [mul_assoc] using congrArg (· * y) h
    exact Subtype.ext (hle ⟨r.2, hcent⟩ a)
  have hA2 : ¬ 2 ∣ Nat.card (Subgroup.zpowers b) := by
    rw [card_zpowers_of_ne_one hp hB hb]
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h).symm
  have h1 := CFSG.GroupTheory.thompson_A_times_B (p := 2) (hS.to_subgroup S₀) hA2
    (hS.to_subgroup S₁) α β hcomm hfix ⟨b, Subgroup.mem_zpowers b⟩
  refine hb (hS₀faith b fun x hx => ?_)
  have h2 := DFunLike.congr_fun h1 (⟨x, hx⟩ : S₀)
  exact congrArg Subtype.val h2

end Main

section Assembly

variable {p : ℕ} {B S : Type} [Group B] [Group S] [MulDistribMulAction B S] [Finite B] [Finite S]

omit [Group S] [MulDistribMulAction B S] [Finite S] in
theorem zpowers_sup_zpowers_eq_top (hp : p.Prime) (hB : IsElementaryAbelian p B)
    (hBcard : Nat.card B = p ^ 2) {x y : B} (hx : x ≠ 1) (hy : y ∉ Subgroup.zpowers x) :
    Subgroup.zpowers x ⊔ Subgroup.zpowers y = ⊤ := by
  set K := Subgroup.zpowers x ⊔ Subgroup.zpowers y with hK
  have hlt : Subgroup.zpowers x < K := by
    refine lt_of_le_of_ne le_sup_left fun h => hy ?_
    rw [h]
    exact (le_sup_right : Subgroup.zpowers y ≤ K) (Subgroup.mem_zpowers y)
  have hdvd : Nat.card K ∣ p ^ 2 := hBcard ▸ Subgroup.card_subgroup_dvd_card K
  obtain ⟨i, hi, hKi⟩ := (Nat.dvd_prime_pow hp).1 hdvd
  have hcard : p < Nat.card K := by
    have := Subgroup.card_lt_of_lt hlt
    rwa [card_zpowers_of_ne_one hp hB hx] at this
  interval_cases i
  · rw [pow_zero] at hKi
    rw [hKi] at hcard
    exact absurd hcard (by have := hp.one_lt; omega)
  · rw [hKi, pow_one] at hcard
    exact absurd hcard (lt_irrefl p)
  · exact (Subgroup.card_eq_iff_eq_top K).1 (by rw [hKi, hBcard])

theorem exists_second_factor (hp : p.Prime) (hp2 : p ≠ 2) (hB : IsElementaryAbelian p B)
    (hBcard : Nat.card B = p ^ 2) (hS : IsPGroup 2 S) {S₀ S₁ : Subgroup S}
    (hS₀inv : IsActionInvariant B S₀) (hS₁inv : IsActionInvariant B S₁) {b₁ : B} (hb₁ : b₁ ≠ 1)
    (hnot : ¬ (S₀ ⊓ Subgroup.centralizer (S₁ : Set S) ≤
      CFSG.fixedPointSubgroup (Subgroup.zpowers b₁) S)) :
    ∃ b₂ : B, b₂ ≠ 1 ∧ b₂ ∉ Subgroup.zpowers b₁ ∧ ∃ S₂ : Subgroup S,
      S₂ ≤ S₀ ⊓ Subgroup.centralizer (S₁ : Set S) ∧ (∃ x ∈ S₂, b₁ • x ≠ x) ∧
      IsActionInvariant B S₂ ∧ actionCommutator B S₂ = S₂ ∧ (∀ x ∈ S₂, b₂ • x = x) := by
  have : Fact p.Prime := ⟨hp⟩
  have := hB
  have hcommB : ∀ x y : B, x * y = y * x := fun x y => hB.is_comm.comm x y
  have hB2 := not_two_dvd_card_of_card_eq hp hp2 hBcard
  set X := S₀ ⊓ Subgroup.centralizer (S₁ : Set S) with hX
  have hXinv : IsActionInvariant B X :=
    isActionInvariant_inf hS₀inv (isActionInvariant_centralizer hS₁inv)
  obtain ⟨b₂, hb₂, hY⟩ : ∃ b₂ : B, b₂ ≠ 1 ∧ ¬ (X ⊓ CFSG.fixedPointSubgroup
      (Subgroup.zpowers b₂) S ≤ CFSG.fixedPointSubgroup (Subgroup.zpowers b₁) S) := by
    by_contra hcon
    push Not at hcon
    exact hnot (le_of_centralizers_le (p := p) (by rw [hBcard]) hXinv
      (not_dvd_card_of_isPGroup_two hp hp2 (hS.to_subgroup X)) hcon)
  set Y := X ⊓ CFSG.fixedPointSubgroup (Subgroup.zpowers b₂) S with hYdef
  have hYinv : IsActionInvariant B Y :=
    isActionInvariant_inf hXinv (isActionInvariant_fixedPointSubgroup_zpowers hcommB b₂)
  have hb₂b₁ : b₂ ∉ Subgroup.zpowers b₁ := by
    intro hmem
    apply hY
    have heq : Subgroup.zpowers b₂ = Subgroup.zpowers b₁ := zpowers_eq_of_mem hp hB hb₁ hb₂ hmem
    intro y hy
    have hb₁mem : b₁ ∈ Subgroup.zpowers b₂ := heq ▸ Subgroup.mem_zpowers b₁
    exact (SolvableHall.mem_fixedPointSubgroup_zpowers_iff b₁ y).2 (hy.2 ⟨b₁, hb₁mem⟩)
  obtain ⟨y, hyY, hy⟩ : ∃ y ∈ Y, y ∉ CFSG.fixedPointSubgroup (Subgroup.zpowers b₁) S := by
    by_contra hcon
    push Not at hcon
    exact hY hcon
  have hy' : b₁ • y ≠ y := fun h => hy ((SolvableHall.mem_fixedPointSubgroup_zpowers_iff b₁ y).2 h)
  obtain ⟨hS₂Y, hS₂inv, hS₂c⟩ := commutator_properties hS hB2 hYinv
  refine ⟨b₂, hb₂, hb₂b₁, actionCommutator B Y, hS₂Y.trans inf_le_left, ?_, hS₂inv, hS₂c,
    fun x hx => (SolvableHall.mem_fixedPointSubgroup_zpowers_iff b₂ x).1 (hS₂Y hx).2⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨d, hd, c, hcY, hc, hdc⟩ :=
    exists_mul_of_invariant_isPGroup Nat.prime_two (hS.to_subgroup Y) hB2 hYinv hyY
  apply hy'
  rw [hdc, smul_mul', hcon d hd, hc b₁]

end Assembly

section Final

variable {p : ℕ} {B S : Type} [Group B] [Group S] [MulDistribMulAction B S] [Finite B] [Finite S]

theorem centralizes_of_minimal (hp : p.Prime) (hp2 : p ≠ 2) (hB : IsElementaryAbelian p B)
    (hBcard : Nat.card B = p ^ 2) (hS : IsPGroup 2 S) {S₀ Si Sj : Subgroup S}
    (hS₀min : ∀ U : Subgroup S, IsActionInvariant B U →
      (∀ c : B, (∀ x ∈ U, c • x = x) → c = 1) → U ≤ S₀ → U = S₀)
    (hSiS₀ : Si ≤ S₀) (hSjS₀ : Sj ≤ S₀) (hSjinv : IsActionInvariant B Sj)
    (hcomm : ⁅Si, Sj⁆ = ⊥) (hSic : actionCommutator B Si = Si)
    {bi bj : B} (hbi : bi ≠ 1) (hbj : bj ∉ Subgroup.zpowers bi)
    (hki : ∀ c : B, (∀ x ∈ Si, c • x = x) ↔ c ∈ Subgroup.zpowers bi)
    (hkj : ∀ c : B, (∀ x ∈ Sj, c • x = x) ↔ c ∈ Subgroup.zpowers bj)
    (hJ : ∀ x ∈ Si ⊓ Sj, ∀ c : B, c • x = x) :
    ∀ U : Subgroup S, U < Si → IsActionInvariant B U → ActionCentralizes B U := by
  intro U hUlt hUinv
  by_contra hcon
  unfold ActionCentralizes at hcon
  push Not at hcon
  obtain ⟨c₀, u, hu, hcu⟩ := hcon
  have hB2 := not_two_dvd_card_of_card_eq hp hp2 hBcard
  obtain ⟨hVU, hVinv, hVc⟩ := commutator_properties hS hB2 hUinv
  set V := actionCommutator B U with hV
  have hUSi : U ≤ Si := hUlt.le
  have hVne : V ≠ ⊥ := by
    intro hbot
    have h := gen_mem_actionCommutator (A := B) hu c₀
    rw [← hV, hbot, Subgroup.mem_bot, inv_mul_eq_one] at h
    exact hcu h.symm
  have hbiV : ∀ x ∈ V, bi • x = x := fun x hx =>
    (hki bi).2 (Subgroup.mem_zpowers bi) x (hUSi (hVU hx))
  have hkV := fixes_iff_mem_zpowers hp hB hBcard hVne hVc hbi hbiV
  have hfaith : ∀ c : B, (∀ x ∈ V ⊔ Sj, c • x = x) → c = 1 := by
    intro c hc
    have h1 : c ∈ Subgroup.zpowers bi := (hkV c).1 fun x hx => hc x (Subgroup.mem_sup_left hx)
    have h2 : c ∈ Subgroup.zpowers bj := (hkj c).1 fun x hx => hc x (Subgroup.mem_sup_right hx)
    have h3 : c ∈ Subgroup.zpowers bi ⊓ Subgroup.zpowers bj := ⟨h1, h2⟩
    rwa [zpowers_inf_zpowers_eq_bot hp hB hbi hbj, Subgroup.mem_bot] at h3
  have hVSj : V ⊔ Sj = S₀ := hS₀min _ (isActionInvariant_sup hVinv hSjinv) hfaith
    (sup_le (hVU.trans (hUSi.trans hSiS₀)) hSjS₀)
  have hSicent : Si ≤ Subgroup.centralizer (Sj : Set S) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  have hVnorm : V ≤ Subgroup.normalizer (Sj : Set S) := fun v hv =>
    Subgroup.centralizer_le_normalizer (Sj : Set S) (hSicent (hUSi (hVU hv)))
  have hmul := Subgroup.coe_mul_of_left_le_normalizer_right V Sj hVnorm
  have hgen : ∀ x ∈ Si, ∀ c : B, x⁻¹ * (c • x) ∈ V := by
    intro x hxSi c
    have hx0 : x ∈ V ⊔ Sj := hVSj ▸ hSiS₀ hxSi
    have hx1 : x ∈ (V : Set S) * (Sj : Set S) := by
      rw [← hmul]
      exact hx0
    obtain ⟨v, hv, w, hw, rfl⟩ := hx1
    have hvSi : v ∈ Si := hUSi (hVU hv)
    have hwSi : w ∈ Si := by
      have h : w = v⁻¹ * (v * w) := by group
      rw [h]
      exact Si.mul_mem (Si.inv_mem hvSi) hxSi
    have hwfix : c • w = w := hJ w ⟨hwSi, hw⟩ c
    have ht : v⁻¹ * (c • v) ∈ V := by
      rw [← hVc]
      exact gen_mem_actionCommutator hv c
    have htSi : v⁻¹ * (c • v) ∈ Si := hUSi (hVU ht)
    have hwt : w * (v⁻¹ * (c • v)) = (v⁻¹ * (c • v)) * w :=
      Subgroup.mem_centralizer_iff.mp (hSicent htSi) w hw
    have hkey : (v * w)⁻¹ * (c • (v * w)) = w⁻¹ * ((v⁻¹ * (c • v)) * w) := by
      rw [smul_mul', hwfix, mul_inv_rev]
      group
    rw [hkey, ← hwt, inv_mul_cancel_left]
    exact ht
  have hSiU : Si ≤ U := by
    rw [← hSic]
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨x, hx, c, rfl⟩
    exact hVU (hgen x hx c)
  exact hUlt.not_ge hSiU

omit [Finite B] in
theorem exists_minimal_faithful_invariant (hfaith : ∀ c : B, (∀ s : S, c • s = s) → c = 1) :
    ∃ S₀ : Subgroup S, IsActionInvariant B S₀ ∧ (∀ c : B, (∀ x ∈ S₀, c • x = x) → c = 1) ∧
      ∀ U : Subgroup S, IsActionInvariant B U → (∀ c : B, (∀ x ∈ U, c • x = x) → c = 1) →
        U ≤ S₀ → U = S₀ := by
  obtain ⟨S₀, hS₀, hmin⟩ := (wellFounded_lt (α := Subgroup S)).has_min
    {U : Subgroup S | IsActionInvariant B U ∧ ∀ c : B, (∀ x ∈ U, c • x = x) → c = 1}
    ⟨⊤, fun b x _ => Subgroup.mem_top _,
      fun c hc => hfaith c fun s => hc s (Subgroup.mem_top s)⟩
  exact ⟨S₀, hS₀.1, hS₀.2, fun U hU hf hle =>
    by_contra fun hne => hmin U ⟨hU, hf⟩ (lt_of_le_of_ne hle hne)⟩

theorem exists_factors_of_minimal (hp : p.Prime) (hp2 : p ≠ 2) (hB : IsElementaryAbelian p B)
    (hBcard : Nat.card B = p ^ 2) (hS : IsPGroup 2 S) {S₀ : Subgroup S}
    (hS₀inv : IsActionInvariant B S₀)
    (hS₀faith : ∀ c : B, (∀ x ∈ S₀, c • x = x) → c = 1)
    (hS₀min : ∀ U : Subgroup S, IsActionInvariant B U →
      (∀ c : B, (∀ x ∈ U, c • x = x) → c = 1) → U ≤ S₀ → U = S₀) :
    ∃ S₁ S₂ : Subgroup S, S₁ ≠ ⊥ ∧ S₂ ≠ ⊥ ∧ S₁ ≤ S₀ ∧ S₂ ≤ S₀ ∧ S₀ = S₁ ⊔ S₂ ∧
      ⁅S₁, S₂⁆ = ⊥ ∧ MinimalPlaneFactor B S₁ ∧ MinimalPlaneFactor B S₂ ∧
      (∃ B₁ B₂ : Subgroup B, Nat.card B₁ = p ∧ Nat.card B₂ = p ∧ B₁ ≠ B₂ ∧ B₁ ⊓ B₂ = ⊥ ∧
        B₁ ⊔ B₂ = ⊤ ∧ (∀ c : B, c ∈ B₁ ↔ ∀ s ∈ S₁, c • s = s) ∧
        (∀ c : B, c ∈ B₂ ↔ ∀ s ∈ S₂, c • s = s)) ∧
      S₁ ⊓ S₂ ≤ S₀ ⊓ Subgroup.centralizer (S₀ : Set S) ∧ ActionCentralizes B (S₁ ⊓ S₂) := by
  have : Fact p.Prime := ⟨hp⟩
  have := hB
  have hcommB : ∀ x y : B, x * y = y * x := fun x y => hB.is_comm.comm x y
  have hB2 := not_two_dvd_card_of_card_eq hp hp2 hBcard
  obtain ⟨b₁, hb₁, hS₁ne⟩ := exists_commutator_line hp hp2 hB hBcard hS hS₀inv hS₀faith
  set X₁ := S₀ ⊓ CFSG.fixedPointSubgroup (Subgroup.zpowers b₁) S with hX₁
  have hX₁inv : IsActionInvariant B X₁ :=
    isActionInvariant_inf hS₀inv (isActionInvariant_fixedPointSubgroup_zpowers hcommB b₁)
  obtain ⟨hS₁X, hS₁inv, hS₁c⟩ := commutator_properties hS hB2 hX₁inv
  set S₁ := actionCommutator B X₁ with hS₁
  have hS₁S₀ : S₁ ≤ S₀ := hS₁X.trans inf_le_left
  have hb₁S₁ : ∀ x ∈ S₁, b₁ • x = x := fun x hx =>
    (SolvableHall.mem_fixedPointSubgroup_zpowers_iff b₁ x).1 (hS₁X hx).2
  have hk₁ := fixes_iff_mem_zpowers hp hB hBcard hS₁ne hS₁c hb₁ hb₁S₁
  have hnot := not_le_fixed_of_commuting hp hp2 hB hS hS₀inv hS₁S₀ hS₀faith hb₁ hk₁
  obtain ⟨b₂, hb₂, hb₂b₁, S₂, hS₂X, ⟨x₂, hx₂, hx₂ne⟩, hS₂inv, hS₂c, hb₂S₂⟩ :=
    exists_second_factor hp hp2 hB hBcard hS hS₀inv hS₁inv hb₁ hnot
  have hS₂S₀ : S₂ ≤ S₀ := hS₂X.trans inf_le_left
  have hS₂ne : S₂ ≠ ⊥ := by
    intro h
    rw [h, Subgroup.mem_bot] at hx₂
    exact hx₂ne (by rw [hx₂, smul_one])
  have hk₂ := fixes_iff_mem_zpowers hp hB hBcard hS₂ne hS₂c hb₂ hb₂S₂
  have hcomm : ⁅S₁, S₂⁆ = ⊥ := by
    rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (hS₂X.trans inf_le_right)
  have hbot : Subgroup.zpowers b₁ ⊓ Subgroup.zpowers b₂ = ⊥ :=
    zpowers_inf_zpowers_eq_bot hp hB hb₁ hb₂b₁
  have hfaith12 : ∀ c : B, (∀ x ∈ S₁ ⊔ S₂, c • x = x) → c = 1 := by
    intro c hc
    have h3 : c ∈ Subgroup.zpowers b₁ ⊓ Subgroup.zpowers b₂ :=
      ⟨(hk₁ c).1 fun x hx => hc x (Subgroup.mem_sup_left hx),
        (hk₂ c).1 fun x hx => hc x (Subgroup.mem_sup_right hx)⟩
    rwa [hbot, Subgroup.mem_bot] at h3
  have hS₀eq : S₁ ⊔ S₂ = S₀ :=
    hS₀min _ (isActionInvariant_sup hS₁inv hS₂inv) hfaith12 (sup_le hS₁S₀ hS₂S₀)
  have htop : Subgroup.zpowers b₁ ⊔ Subgroup.zpowers b₂ = ⊤ :=
    zpowers_sup_zpowers_eq_top hp hB hBcard hb₁ hb₂b₁
  have hJ : ∀ x ∈ S₁ ⊓ S₂, ∀ c : B, c • x = x := by
    intro x hx c
    have hle : Subgroup.zpowers b₁ ⊔ Subgroup.zpowers b₂ ≤ fixingSubgroup B ({x} : Set S) := by
      refine sup_le (fun g hg => ?_) (fun g hg => ?_)
      · rw [mem_fixingSubgroup_iff B]
        intro y hy
        rw [Set.mem_singleton_iff.mp hy]
        exact (hk₁ g).2 hg x hx.1
      · rw [mem_fixingSubgroup_iff B]
        intro y hy
        rw [Set.mem_singleton_iff.mp hy]
        exact (hk₂ g).2 hg x hx.2
    have hc : c ∈ fixingSubgroup B ({x} : Set S) := hle (htop ▸ Subgroup.mem_top c)
    exact (mem_fixingSubgroup_iff B).mp hc x rfl
  have hb₁b₂ : b₁ ∉ Subgroup.zpowers b₂ := by
    intro h
    have heq := zpowers_eq_of_mem hp hB hb₂ hb₁ h
    exact hb₂b₁ (by rw [heq]; exact Subgroup.mem_zpowers b₂)
  have hmin₁ := centralizes_of_minimal hp hp2 hB hBcard hS hS₀min hS₁S₀ hS₂S₀ hS₂inv
    hcomm hS₁c hb₁ hb₂b₁ hk₁ hk₂ hJ
  have hmin₂ := centralizes_of_minimal hp hp2 hB hBcard hS hS₀min hS₂S₀ hS₁S₀ hS₁inv
    (by rw [Subgroup.commutator_comm]; exact hcomm) hS₂c
    hb₂ hb₁b₂ hk₂ hk₁ (fun x hx c => hJ x (by rwa [inf_comm]) c)
  refine ⟨S₁, S₂, hS₁ne, hS₂ne, hS₁S₀, hS₂S₀, hS₀eq.symm, hcomm,
    minimalPlaneFactor_of_minimal hS hB2 hS₁inv hS₁ne hS₁c hmin₁,
    minimalPlaneFactor_of_minimal hS hB2 hS₂inv hS₂ne hS₂c hmin₂,
    ⟨Subgroup.zpowers b₁, Subgroup.zpowers b₂, card_zpowers_of_ne_one hp hB hb₁,
      card_zpowers_of_ne_one hp hB hb₂, ?_, hbot, htop, fun c => (hk₁ c).symm,
      fun c => (hk₂ c).symm⟩, ?_, fun c x hx => hJ x hx c⟩
  · intro h
    exact hb₂b₁ (h ▸ Subgroup.mem_zpowers b₂)
  · intro x hx
    refine Subgroup.mem_inf.mpr ⟨hS₁S₀ hx.1, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have hle : S₁ ⊔ S₂ ≤ Subgroup.centralizer ({x} : Set S) := by
      refine sup_le (fun y hy => ?_) (fun y hy => ?_)
      · rw [Subgroup.mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff.mp hh]
        exact Subgroup.mem_centralizer_iff.mp
          (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm hy) x hx.2
      · rw [Subgroup.mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff.mp hh]
        exact Subgroup.mem_centralizer_iff.mp
          (Subgroup.commutator_eq_bot_iff_le_centralizer.mp
            (by rw [Subgroup.commutator_comm]; exact hcomm) hy) x hx.1
    have hs' : s ∈ Subgroup.centralizer ({x} : Set S) := hle (hS₀eq ▸ hs)
    exact (Subgroup.mem_centralizer_iff.mp hs' x rfl).symm

end Final

end PlaneFactors

theorem faithful_plane_two_action_commuting_minimal_factors :
    ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (B S : Type) [Group B] [Group S] [Finite B] [Finite S]
      [MulDistribMulAction B S], IsElementaryAbelian p B → Nat.card B = p ^ 2 → IsPGroup 2 S →
      (∀ c : B, (∀ s : S, c • s = s) → c = 1) →
      ∃ S₀ S₁ S₂ : Subgroup S, IsActionInvariant B S₀ ∧ S₁ ≠ ⊥ ∧ S₂ ≠ ⊥ ∧ S₁ ≤ S₀ ∧ S₂ ≤ S₀ ∧
        S₀ = S₁ ⊔ S₂ ∧ ⁅S₁, S₂⁆ = ⊥ ∧ (∀ c : B, (∀ s ∈ S₀, c • s = s) → c = 1) ∧
        MinimalPlaneFactor B S₁ ∧ MinimalPlaneFactor B S₂ ∧
        (∃ B₁ B₂ : Subgroup B, Nat.card B₁ = p ∧ Nat.card B₂ = p ∧ B₁ ≠ B₂ ∧ B₁ ⊓ B₂ = ⊥ ∧
          B₁ ⊔ B₂ = ⊤ ∧ (∀ c : B, c ∈ B₁ ↔ ∀ s ∈ S₁, c • s = s) ∧
          (∀ c : B, c ∈ B₂ ↔ ∀ s ∈ S₂, c • s = s)) ∧
        S₁ ⊓ S₂ ≤ S₀ ⊓ Subgroup.centralizer (S₀ : Set S) ∧ ActionCentralizes B (S₁ ⊓ S₂) := by
  intro p hp hp2 B S _ _ _ _ _ hB hBcard hS hfaith
  obtain ⟨S₀, hS₀inv, hS₀faith, hS₀min⟩ := PlaneFactors.exists_minimal_faithful_invariant hfaith
  obtain ⟨S₁, S₂, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ :=
    PlaneFactors.exists_factors_of_minimal hp hp2 hB hBcard hS hS₀inv hS₀faith hS₀min
  exact ⟨S₀, S₁, S₂, hS₀inv, h1, h2, h3, h4, h5, h6, hS₀faith, h7, h8, h9, h10, h11⟩

end CFSG.RankThree.PartOne
