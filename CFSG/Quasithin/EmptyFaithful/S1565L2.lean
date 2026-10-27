module

public import CFSG.Quasithin.EmptyFaithful.S1565A

public section

namespace CFSG.Quasithin.S1565

variable {X : Type} [Group X] {W : Type} [CommGroup W]

theorem ucf_invSub_sup {φ : X →* MulAut W} {A B : Subgroup W} (hA : InvSub φ A) (hB : InvSub φ B) :
    InvSub φ (A ⊔ B) := by
  intro x w hw
  obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.mp hw
  rw [map_mul]
  exact Subgroup.mul_mem_sup (hA x a ha) (hB x b hb)

theorem ucf_invSub_inf {φ : X →* MulAut W} {A B : Subgroup W} (hA : InvSub φ A) (hB : InvSub φ B) :
    InvSub φ (A ⊓ B) := fun x w hw => ⟨hA x w hw.1, hB x w hw.2⟩

private noncomputable def ucfRestr (φ : X →* MulAut W) {E : Subgroup W} (hE : InvSub φ E) (x : X) :
    ↥E →* ↥E :=
  (((φ x).toMonoidHom.comp E.subtype)).codRestrict E (fun e => hE x e e.2)

private theorem ucfRestr_coe (φ : X →* MulAut W) {E : Subgroup W} (hE : InvSub φ E) (x : X) (e : ↥E) :
    ((ucfRestr φ hE x e : ↥E) : W) = φ x (e : W) := rfl

private noncomputable def ucfQuotAct (φ : X →* MulAut W) {E A : Subgroup W} (hE : InvSub φ E)
    (hA : InvSub φ A) (x : X) : (↥E ⧸ A.subgroupOf E) →* (↥E ⧸ A.subgroupOf E) :=
  QuotientGroup.map (A.subgroupOf E) (A.subgroupOf E) (ucfRestr φ hE x) (by
    intro a ha
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
    exact hA x _ ha)

private theorem ucfQuotAct_mk (φ : X →* MulAut W) {E A : Subgroup W} (hE : InvSub φ E)
    (hA : InvSub φ A) (x : X) (e : ↥E) :
    ucfQuotAct φ hE hA x (QuotientGroup.mk e) = QuotientGroup.mk (ucfRestr φ hE x e) :=
  rfl

@[instance_reducible] private noncomputable def ucfMulAction (φ : X →* MulAut W) {E A : Subgroup W} (hE : InvSub φ E)
    (hA : InvSub φ A) : MulAction X (↥E ⧸ A.subgroupOf E) where
  smul x q := ucfQuotAct φ hE hA x q
  one_smul q := by
    induction q using QuotientGroup.induction_on with
    | H e =>
      show ucfQuotAct φ hE hA 1 (QuotientGroup.mk e) = QuotientGroup.mk e
      rw [ucfQuotAct_mk]
      congr 1
      exact Subtype.ext (by rw [ucfRestr_coe, map_one]; rfl)
  mul_smul x y q := by
    induction q using QuotientGroup.induction_on with
    | H e =>
      show ucfQuotAct φ hE hA (x * y) (QuotientGroup.mk e) =
        ucfQuotAct φ hE hA x (ucfQuotAct φ hE hA y (QuotientGroup.mk e))
      rw [ucfQuotAct_mk, ucfQuotAct_mk, ucfQuotAct_mk]
      congr 1
      exact Subtype.ext (by simp only [ucfRestr_coe, map_mul]; rfl)


theorem ucf_exists_fixMod [Finite X] [Finite W] (φ : X →* MulAut W) (hW2 : ∀ w : W, w ^ 2 = 1)
    (N : Subgroup X) [N.Normal] (hN : IsPGroup 2 (X ⧸ N)) {E A : Subgroup W} (hE : InvSub φ E)
    (hA : InvSub φ A) (hNE : ∀ n ∈ N, ∀ e ∈ E, φ n e = e) (hEA : ¬ E ≤ A) :
    ∃ e ∈ E, e ∉ A ∧ ∀ x : X, φ x e * e⁻¹ ∈ A := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : MulAction X (↥E ⧸ A.subgroupOf E) := ucfMulAction φ hE hA
  have hker : N ≤ (MulAction.toPermHom X (↥E ⧸ A.subgroupOf E)).ker := by
    intro n hn
    rw [MonoidHom.mem_ker]
    ext q
    induction q using QuotientGroup.induction_on with
    | H e =>
      show ucfQuotAct φ hE hA n (QuotientGroup.mk e) = QuotientGroup.mk e
      rw [ucfQuotAct_mk]
      congr 1
      exact Subtype.ext (by rw [ucfRestr_coe]; exact hNE n hn e e.2)
  let ρ : X ⧸ N →* Equiv.Perm (↥E ⧸ A.subgroupOf E) :=
    QuotientGroup.lift N (MulAction.toPermHom X _) hker
  let _ : MulAction (X ⧸ N) (↥E ⧸ A.subgroupOf E) := MulAction.compHom _ ρ
  have hmod := hN.card_modEq_card_fixedPoints (↥E ⧸ A.subgroupOf E)
  have hW : IsPGroup 2 W := fun w => ⟨1, by simpa using hW2 w⟩
  have hV : IsPGroup 2 (↥E ⧸ A.subgroupOf E) := (hW.to_subgroup E).to_quotient _
  have hVnt : Nontrivial (↥E ⧸ A.subgroupOf E) := by
    obtain ⟨e, he, heA⟩ : ∃ e ∈ E, e ∉ A := by
      by_contra hcon
      push Not at hcon
      exact hEA hcon
    refine ⟨⟨QuotientGroup.mk ⟨e, he⟩, 1, fun h => heA ?_⟩⟩
    have := (QuotientGroup.eq_one_iff (N := A.subgroupOf E) (⟨e, he⟩ : ↥E)).mp h
    exact (Subgroup.mem_subgroupOf.mp this)
  obtain ⟨k, hk0, hk⟩ := (hV.nontrivial_iff_card).mp hVnt
  have hev : 2 ∣ Nat.card (↥E ⧸ A.subgroupOf E) := by
    rw [hk]; exact dvd_pow_self 2 hk0.ne'
  have hfix : 2 ∣ Nat.card (MulAction.fixedPoints (X ⧸ N) (↥E ⧸ A.subgroupOf E)) := by
    obtain ⟨c, hc⟩ := hev
    unfold Nat.ModEq at hmod
    omega
  have h1fix : (1 : ↥E ⧸ A.subgroupOf E) ∈
      MulAction.fixedPoints (X ⧸ N) (↥E ⧸ A.subgroupOf E) := by
    intro g
    induction g using QuotientGroup.induction_on with
    | H x =>
      show ucfQuotAct φ hE hA x 1 = 1
      exact map_one _
  have hFfin : Finite (MulAction.fixedPoints (X ⧸ N) (↥E ⧸ A.subgroupOf E)) := inferInstance
  have hcard2 : 1 < Nat.card (MulAction.fixedPoints (X ⧸ N) (↥E ⧸ A.subgroupOf E)) := by
    have hpos : 0 < Nat.card (MulAction.fixedPoints (X ⧸ N) (↥E ⧸ A.subgroupOf E)) :=
      Nat.card_pos_iff.mpr ⟨⟨⟨1, h1fix⟩⟩, hFfin⟩
    obtain ⟨c, hc⟩ := hfix
    omega
  have hnt := Finite.one_lt_card_iff_nontrivial.mp hcard2
  obtain ⟨⟨q, hq⟩, hq1⟩ := exists_ne (⟨1, h1fix⟩ :
    MulAction.fixedPoints (X ⧸ N) (↥E ⧸ A.subgroupOf E))
  induction q using QuotientGroup.induction_on with
  | H e =>
    refine ⟨(e : W), e.2, fun heA => hq1 ?_, fun x => ?_⟩
    · apply Subtype.ext
      show (QuotientGroup.mk e : ↥E ⧸ A.subgroupOf E) = 1
      exact (QuotientGroup.eq_one_iff e).mpr (Subgroup.mem_subgroupOf.mpr heA)
    · have h := hq (QuotientGroup.mk x)
      have h2 : ucfQuotAct φ hE hA x (QuotientGroup.mk e) = QuotientGroup.mk e := h
      rw [ucfQuotAct_mk, QuotientGroup.eq] at h2
      have h3 := Subgroup.mem_subgroupOf.mp h2
      have h4 := A.inv_mem h3
      rw [mul_comm]
      simpa [ucfRestr_coe] using h4

private def ucfFixSub (φ : X →* MulAut W) (E A : Subgroup W) : Subgroup W where
  carrier := {e | e ∈ E ∧ ∀ x : X, φ x e * e⁻¹ ∈ A}
  one_mem' := ⟨E.one_mem, fun x => by simp⟩
  mul_mem' := by
    rintro a b ⟨haE, ha⟩ ⟨hbE, hb⟩
    refine ⟨E.mul_mem haE hbE, fun x => ?_⟩
    have e : φ x (a * b) * (a * b)⁻¹ = (φ x a * a⁻¹) * (φ x b * b⁻¹) := by
      rw [map_mul]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel
    rw [e]
    exact A.mul_mem (ha x) (hb x)
  inv_mem' := by
    rintro a ⟨haE, ha⟩
    refine ⟨E.inv_mem haE, fun x => ?_⟩
    have e : φ x a⁻¹ * (a⁻¹)⁻¹ = (φ x a * a⁻¹)⁻¹ := by
      rw [map_inv]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel
    rw [e]
    exact A.inv_mem (ha x)

private theorem ucfFixSub_invSub (φ : X →* MulAut W) {E A : Subgroup W} (hE : InvSub φ E)
    (hA : InvSub φ A) : InvSub φ (ucfFixSub φ E A) := by
  rintro y f ⟨hfE, hf⟩
  refine ⟨hE y f hfE, fun x => ?_⟩
  have h1 := hf (y⁻¹ * x * y)
  have h2 := hA y _ h1
  have hxy : φ x (φ y f) = φ y (φ (y⁻¹ * x * y) f) := by
    have : x * y = y * (y⁻¹ * x * y) := by group
    calc φ x (φ y f) = φ (x * y) f := by rw [map_mul]; rfl
      _ = φ (y * (y⁻¹ * x * y)) f := by rw [this]
      _ = φ y (φ (y⁻¹ * x * y) f) := by rw [map_mul]; rfl
  have e : φ x (φ y f) * (φ y f)⁻¹ = φ y (φ (y⁻¹ * x * y) f * f⁻¹) := by
    rw [hxy, map_mul (φ y), map_inv (φ y)]
  rw [e]
  exact h2

theorem chiefFreeBelow_of_odd_element [Finite X] [Finite W] (φ : X →* MulAut W)
    (hW2 : ∀ w : W, w ^ 2 = 1) (N : Subgroup X) [N.Normal] (hN : IsPGroup 2 (X ⧸ N))
    {C : Subgroup W} (hC : InvSub φ C) (hNC : ∀ n ∈ N, ∀ c ∈ C, φ n c = c) (B : Subgroup X)
    {t₀ : X} (ht₀B : t₀ ∈ B) {m : ℕ} (hodd : Odd m) (J : Subgroup W)
    (hfm : ∀ w ∈ J, ((φ t₀) ^ m) w = w) (hJ : ∀ w ∈ J, φ t₀ w * w⁻¹ ∈ C → w ∈ C) :
    ChiefFreeBelow φ B J := by
  intro A A' hA'J hchief
  obtain ⟨hlt, hAinv, hA'inv, hmin⟩ := hchief
  have hEinv : InvSub φ (A' ⊓ C) := ucf_invSub_inf hA'inv hC
  have hD : InvSub φ (A ⊔ A' ⊓ C) := ucf_invSub_sup hAinv hEinv
  rcases hmin (A ⊔ A' ⊓ C) hD le_sup_left (sup_le hlt.le inf_le_left) with hDA | hDA'
  ·
    right
    have hEA : A' ⊓ C ≤ A := by rw [← hDA]; exact le_sup_right
    intro a ha hfix
    set f : MulAut W := φ t₀ with hf
    have hfma : (f ^ m) a = a := hfm a (hA'J ha)
    have hfa : f a * a⁻¹ ∈ A := hfix t₀ ht₀B
    have hpow : ∀ i : ℕ, (f ^ i) a * a⁻¹ ∈ A := by
      intro i
      induction i with
      | zero => simp
      | succ i ih =>
        have e : (f ^ (i + 1)) a * a⁻¹ = f ((f ^ i) a * a⁻¹) * (f a * a⁻¹) := by
          rw [pow_succ', MulAut.mul_apply, map_mul, map_inv]
          apply Additive.ofMul.injective
          simp only [ofMul_mul, ofMul_inv]
          abel
        rw [e]
        exact A.mul_mem (hAinv t₀ _ ih) hfa
    have hmem : ∀ i : ℕ, (f ^ i) a ∈ A' := by
      intro i
      have : f ^ i = φ (t₀ ^ i) := (map_pow φ t₀ i).symm
      rw [this]
      exact hA'inv _ a ha
    set u : W := ∏ i ∈ Finset.range m, (f ^ i) a with hu
    have hu' : u ∈ A' := Subgroup.prod_mem _ fun i _ => hmem i
    have hshift : ∏ i ∈ Finset.range m, (f ^ (i + 1)) a = u := by
      have h1 := Finset.prod_range_succ' (fun i => (f ^ i) a) m
      have h2 := Finset.prod_range_succ (fun i => (f ^ i) a) m
      rw [h1] at h2
      simp only [pow_zero, MulAut.one_apply, hfma] at h2
      exact mul_right_cancel h2
    have hfu : f u = u := by
      have h1 : f u = ∏ i ∈ Finset.range m, (f ^ (i + 1)) a := by
        rw [hu, map_prod]
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [pow_succ', MulAut.mul_apply]
      rw [h1, hshift]
    have hua : u * a⁻¹ ∈ A := by
      have e : u = (∏ i ∈ Finset.range m, ((f ^ i) a * a⁻¹)) * a ^ m := by
        rw [hu]
        have : ∀ i ∈ Finset.range m, (f ^ i) a = ((f ^ i) a * a⁻¹) * a := fun i _ => by
          rw [inv_mul_cancel_right]
        rw [Finset.prod_congr rfl this, Finset.prod_mul_distrib, Finset.prod_const,
          Finset.card_range]
      have hao : a ^ m = a := by
        obtain ⟨k, hk⟩ := hodd
        rw [hk, pow_succ, pow_mul, hW2, one_pow, one_mul]
      rw [e, hao, mul_assoc, mul_inv_cancel, mul_one]
      exact Subgroup.prod_mem _ fun i _ => hpow i
    have huC : u ∈ C := by
      refine hJ u (hA'J hu') ?_
      show f u * u⁻¹ ∈ C
      rw [hfu, mul_inv_cancel]
      exact C.one_mem
    have huA : u ∈ A := hEA ⟨hu', huC⟩
    have e : a = (u * a⁻¹)⁻¹ * u := by
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel
    rw [e]
    exact A.mul_mem (A.inv_mem hua) huA
  ·
    left
    have hEA : ¬ (A' ⊓ C ≤ A) := by
      intro h
      have : A ⊔ A' ⊓ C = A := sup_eq_left.mpr h
      rw [this] at hDA'
      exact hlt.ne hDA'
    obtain ⟨e₀, he₀E, he₀A, he₀fix⟩ := ucf_exists_fixMod φ hW2 N hN hEinv hAinv
      (fun n hn e he => hNC n hn e he.2) hEA
    have hFinv := ucfFixSub_invSub φ hEinv hAinv
    have hF1 : InvSub φ (A ⊔ ucfFixSub φ (A' ⊓ C) A) := ucf_invSub_sup hAinv hFinv
    have hFle : ucfFixSub φ (A' ⊓ C) A ≤ A' := fun f hf => hf.1.1
    rcases hmin (A ⊔ ucfFixSub φ (A' ⊓ C) A) hF1 le_sup_left (sup_le hlt.le hFle) with h1 | h1
    · exfalso
      apply he₀A
      rw [← h1]
      exact Subgroup.mem_sup_right ⟨he₀E, he₀fix⟩
    · intro x a' ha'
      rw [← h1] at ha'
      obtain ⟨a, ha, f, hf, rfl⟩ := Subgroup.mem_sup.mp ha'
      have e : φ x (a * f) * (a * f)⁻¹ = (φ x a * a⁻¹) * (φ x f * f⁻¹) := by
        rw [map_mul]
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_inv]
        abel
      rw [e]
      exact A.mul_mem (A.mul_mem (hAinv x a ha) (A.inv_mem ha)) (hf.2 x)

end CFSG.Quasithin.S1565
