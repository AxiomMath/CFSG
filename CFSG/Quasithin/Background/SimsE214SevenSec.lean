module

public import CFSG.Quasithin.Background.SimsE214Ten

public section

namespace CFSG.Quasithin.SimsE2

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

namespace E214S

variable {Γ : Type} [Group Γ]

theorem relIndex_sup_eq_mul {X W Z : Subgroup Γ} (hZX : Z ≤ X) (hZW : Z ≤ W)
    (hXW : X ≤ Subgroup.normalizer (W : Set Γ)) (hinf : X ⊓ W ≤ Z) :
    Z.relIndex (X ⊔ W) = Z.relIndex X * Z.relIndex W := by
  have := Subgroup.normal_subgroupOf_of_le_normalizer hXW
  have := Subgroup.normal_subgroupOf_sup_of_le_normalizer hXW
  have e : W.relIndex (X ⊔ W) = W.relIndex X :=
    Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalizerQuotient X W hXW).toEquiv.symm
  have h2 : W ⊓ X = Z := le_antisymm (by rw [inf_comm]; exact hinf) (le_inf hZW hZX)
  have h3 : W.relIndex X = Z.relIndex X := by
    rw [← Subgroup.inf_relIndex_right W X, h2]
  rw [← Subgroup.relIndex_mul_relIndex Z W (X ⊔ W) hZW le_sup_right, e, h3, mul_comm]

theorem relIndex_biSup_eq_pow {r : ℕ} {I Z : Subgroup Γ} (W : Fin r → Subgroup Γ) {c : ℕ}
    (hZ : ∀ i, Z ≤ W i) (hWI : ∀ i, W i ≤ I)
    (hN : ∀ i, I ≤ Subgroup.normalizer (W i : Set Γ)) (hc : ∀ i, Z.relIndex (W i) = c)
    (hind : ∀ i, W i ⊓ (⨆ j, ⨆ (_ : j ≠ i), W j) ≤ Z) {s : Finset (Fin r)} (hs : s.Nonempty) :
    Z.relIndex (⨆ i ∈ s, W i) = c ^ s.card := by
  induction hs using Finset.Nonempty.cons_induction with
  | singleton a => rw [Finset.iSup_singleton, Finset.card_singleton, pow_one, hc a]
  | cons a s ha hs ih =>
    rw [Finset.cons_eq_insert, Finset.iSup_insert, Finset.card_insert_of_notMem ha, pow_succ,
      sup_comm (W a), ← ih, ← hc a]
    refine relIndex_sup_eq_mul ?_ (hZ a) ?_ ?_
    · obtain ⟨b, hb⟩ := hs
      exact (hZ b).trans (le_iSup₂_of_le b hb le_rfl)
    · exact iSup₂_le fun i _ => (hWI i).trans (hN a)
    · have hle : (⨆ i ∈ s, W i) ≤ ⨆ j, ⨆ (_ : j ≠ a), W j :=
        iSup₂_le fun i hi => le_iSup₂_of_le i (ne_of_mem_of_not_mem hi ha) le_rfl
      calc (⨆ i ∈ s, W i) ⊓ W a ≤ (⨆ j, ⨆ (_ : j ≠ a), W j) ⊓ W a := inf_le_inf_right _ hle
        _ = W a ⊓ ⨆ j, ⨆ (_ : j ≠ a), W j := inf_comm _ _
        _ ≤ Z := hind a

theorem relIndex_iSup_eq_pow {r : ℕ} (hr : 0 < r) {I Z : Subgroup Γ} (W : Fin r → Subgroup Γ)
    {c : ℕ} (hZ : ∀ i, Z ≤ W i) (hWI : ∀ i, W i ≤ I)
    (hN : ∀ i, I ≤ Subgroup.normalizer (W i : Set Γ)) (hc : ∀ i, Z.relIndex (W i) = c)
    (hind : ∀ i, W i ⊓ (⨆ j, ⨆ (_ : j ≠ i), W j) ≤ Z) :
    Z.relIndex (⨆ i, W i) = c ^ r := by
  have : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  have h := relIndex_biSup_eq_pow W hZ hWI hN hc hind (Finset.univ_nonempty (α := Fin r))
  simpa using h

theorem relIndex_of_isNaturalSection {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type}
    [Field F] {I U Z J : Subgroup Γ} {S : Subgroup (Matrix.GeneralLinearGroup ι F)}
    (hN : IsNaturalSection I U Z J S) : Z.relIndex U = Nat.card (ι → F) := by
  obtain ⟨-, -, -, -, -, ψ, -, -, hψs, hψk, -⟩ := hN
  rw [Subgroup.relIndex, ← hψk, Subgroup.index_ker, MonoidHom.range_eq_top.2 hψs,
    Subgroup.card_top]
  rfl

variable [Finite Γ]

theorem relIndex_eq_two_pow_mQuot {X : Subgroup Γ} (hX : IsPGroup 2 X) (U : Subgroup Γ) :
    U.relIndex X = 2 ^ E3.mQuot X U := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := E213M.exists_relIndex_eq_two_pow hX U
  rw [E3.mQuot, ha, padicValNat.prime_pow]

theorem eq_or_eq_of_chief {I P Z : Subgroup Γ} (hP2 : IsPGroup 2 P) {m : ℕ}
    (hchief : ∀ Y₁ Y₂ : Subgroup Γ, Z ≤ Y₂ → Y₂ < Y₁ → Y₁ ≤ P →
      I ≤ Subgroup.normalizer (Y₁ : Set Γ) → I ≤ Subgroup.normalizer (Y₂ : Set Γ) →
      (∀ Y : Subgroup Γ, Y₂ ≤ Y → Y ≤ Y₁ → I ≤ Subgroup.normalizer (Y : Set Γ) →
        Y = Y₂ ∨ Y = Y₁) → m ≤ E3.mQuot Y₁ Y₂)
    (hIZ : I ≤ Subgroup.normalizer (Z : Set Γ)) (hIP : I ≤ Subgroup.normalizer (P : Set Γ))
    (hcard : Z.relIndex P < 2 ^ (2 * m)) {Y : Subgroup Γ} (hZY : Z ≤ Y) (hYP : Y ≤ P)
    (hIY : I ≤ Subgroup.normalizer (Y : Set Γ)) : Y = Z ∨ Y = P := by
  by_contra hne
  push Not at hne
  obtain ⟨hYZ, hYP'⟩ := hne
  have hZY' : Z < Y := lt_of_le_of_ne hZY (Ne.symm hYZ)
  have hYP'' : Y < P := lt_of_le_of_ne hYP hYP'
  obtain ⟨Y₁, ⟨hZY₁, hY₁Y, hIY₁⟩, hmin₁⟩ := wellFounded_lt.has_min
    {Y' : Subgroup Γ | Z < Y' ∧ Y' ≤ Y ∧ I ≤ Subgroup.normalizer (Y' : Set Γ)}
    ⟨Y, hZY', le_rfl, hIY⟩
  obtain ⟨Y₃, ⟨hY₁Y₃, hY₃P, hIY₃⟩, hmin₃⟩ := wellFounded_lt.has_min
    {Y' : Subgroup Γ | Y₁ < Y' ∧ Y' ≤ P ∧ I ≤ Subgroup.normalizer (Y' : Set Γ)}
    ⟨P, lt_of_le_of_lt hY₁Y hYP'', le_rfl, hIP⟩
  have h1 : m ≤ E3.mQuot Y₁ Z := by
    refine hchief Y₁ Z le_rfl hZY₁ (hY₁Y.trans hYP) hIY₁ hIZ fun Y' h₁ h₂ h₃ => ?_
    rcases eq_or_lt_of_le h₁ with h | h
    · exact Or.inl h.symm
    · exact Or.inr (by_contra fun hne => hmin₁ Y' ⟨h, h₂.trans hY₁Y, h₃⟩ (lt_of_le_of_ne h₂ hne))
  have h3 : m ≤ E3.mQuot Y₃ Y₁ := by
    refine hchief Y₃ Y₁ hZY₁.le hY₁Y₃ hY₃P hIY₃ hIY₁ fun Y' h₁ h₂ h₃ => ?_
    rcases eq_or_lt_of_le h₁ with h | h
    · exact Or.inl h.symm
    · exact Or.inr (by_contra fun hne => hmin₃ Y' ⟨h, h₂.trans hY₃P, h₃⟩ (lt_of_le_of_ne h₂ hne))
  have e1 := relIndex_eq_two_pow_mQuot (hP2.to_le (hY₁Y.trans hYP)) Z
  have e3 := relIndex_eq_two_pow_mQuot (hP2.to_le hY₃P) Y₁
  have hdvd : Z.relIndex Y₁ * Y₁.relIndex Y₃ ∣ Z.relIndex P := by
    rw [Subgroup.relIndex_mul_relIndex Z Y₁ Y₃ hZY₁.le hY₁Y₃.le]
    exact Dvd.intro _ (Subgroup.relIndex_mul_relIndex Z Y₃ P (hZY₁.le.trans hY₁Y₃.le) hY₃P)
  have hpos : 0 < Z.relIndex P := by
    show 0 < Nat.card (↥P ⧸ Z.subgroupOf P)
    exact Nat.card_pos
  have hle := Nat.le_of_dvd hpos hdvd
  rw [e1, e3] at hle
  have h4 : 2 ^ (2 * m) ≤ 2 ^ E3.mQuot Y₁ Z * 2 ^ E3.mQuot Y₃ Y₁ := by
    rw [two_mul, pow_add]
    exact Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) h1)
      (Nat.pow_le_pow_right (by norm_num) h3)
  omega

structure Sec (I P Z J : Subgroup Γ) : Prop where
  ZP : Z ≤ P
  PI : P ≤ I
  IP : I ≤ Subgroup.normalizer (P : Set Γ)
  IZ : I ≤ Subgroup.normalizer (Z : Set Γ)
  JI : J ≤ I
  IJ : I ≤ Subgroup.normalizer (J : Set Γ)
  J2 : IsPGroup 2 J
  comm : ∀ x ∈ P, ∀ y ∈ P, x * y * x⁻¹ * y⁻¹ ∈ Z
  sq : ∀ x ∈ P, x ^ 2 ∈ Z
  irr : ∀ Y : Subgroup Γ, Z ≤ Y → Y ≤ P → I ≤ Subgroup.normalizer (Y : Set Γ) → Y = Z ∨ Y = P
  ne : Z ≠ P

namespace Sec

variable {I P Z J : Subgroup Γ}

theorem normal (hS : Sec I P Z J) : (Z.subgroupOf P).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer hS.ZP).2 (hS.PI.trans hS.IZ)

variable [(Z.subgroupOf P).Normal]

noncomputable abbrev act (hS : Sec I P Z J) : ↥I →* MulAut (↥P ⧸ Z.subgroupOf P) :=
  Dih.conjSecAut P Z I hS.IP hS.IZ

theorem act_mk (hS : Sec I P Z J) (i : I) (y : P) :
    hS.act i (y : ↥P ⧸ Z.subgroupOf P) =
      ((⟨(i : Γ) * y * (i : Γ)⁻¹, (Subgroup.mem_normalizer_iff.mp (hS.IP i.2) y).mp y.2⟩ : P) :
        ↥P ⧸ Z.subgroupOf P) :=
  Dih.conjSecAut_mk i y

theorem comm_quot (hS : Sec I P Z J) (a b : ↥P ⧸ Z.subgroupOf P) : a * b = b * a := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf]
  have e : (((x * y)⁻¹ * (y * x) : P) : Γ) =
      (y : Γ)⁻¹ * (x : Γ)⁻¹ * (y : Γ)⁻¹⁻¹ * (x : Γ)⁻¹⁻¹ := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rw [e]
  exact hS.comm _ (P.inv_mem y.2) _ (P.inv_mem x.2)

theorem sq_quot (hS : Sec I P Z J) (a : ↥P ⧸ Z.subgroupOf P) : a * a = 1 := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
  rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, Subgroup.coe_mul,
    ← pow_two]
  exact hS.sq x x.2

theorem mk_eq_one_iff (y : P) : ((y : ↥P ⧸ Z.subgroupOf P) = 1) ↔ (y : Γ) ∈ Z := by
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]

theorem irr_quot (hS : Sec I P Z J) (Y : Subgroup (↥P ⧸ Z.subgroupOf P))
    (hY : ∀ i : I, ∀ q ∈ Y, hS.act i q ∈ Y) : Y = ⊥ ∨ Y = ⊤ := by
  have key : ∀ i ∈ I, ∀ x ∈ Dih.liftSec Y, i * x * i⁻¹ ∈ Dih.liftSec Y := by
    intro i hi x hx
    obtain ⟨hxP, hxY⟩ := Dih.mem_liftSec.1 hx
    refine Dih.mem_liftSec.2 ⟨(Subgroup.mem_normalizer_iff.mp (hS.IP hi) x).mp hxP, ?_⟩
    have := hY ⟨i, hi⟩ _ hxY
    rwa [act_mk] at this
  have hIY : I ≤ Subgroup.normalizer (Dih.liftSec Y : Set Γ) := fun i hi =>
    B6.mem_normalizer_of_forall_mem (key i hi)
      (fun x hx => by simpa using key i⁻¹ (I.inv_mem hi) x hx)
  rcases hS.irr _ (Dih.le_liftSec hS.ZP Y) (Dih.liftSec_le Y) hIY with h | h
  · left
    rw [eq_bot_iff]
    intro q hq
    obtain ⟨⟨x, hxP⟩, rfl⟩ := QuotientGroup.mk_surjective q
    have hx : x ∈ Dih.liftSec Y := Dih.mem_liftSec.2 ⟨hxP, hq⟩
    rw [h] at hx
    rw [Subgroup.mem_bot]
    exact (mk_eq_one_iff ⟨x, hxP⟩).2 hx
  · right
    rw [eq_top_iff]
    intro q _
    obtain ⟨⟨x, hxP⟩, rfl⟩ := QuotientGroup.mk_surjective q
    have hx : x ∈ Dih.liftSec Y := by rw [h]; exact hxP
    exact (Dih.mem_liftSec.1 hx).2

variable [Finite Γ]

theorem two_dvd_card (hS : Sec I P Z J) : 2 ∣ Nat.card (↥P ⧸ Z.subgroupOf P) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 (↥P ⧸ Z.subgroupOf P) := fun a => ⟨1, by rw [pow_one, pow_two, hS.sq_quot]⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hp
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · exfalso
    rw [pow_zero] at hn
    apply hS.ne
    refine le_antisymm hS.ZP fun x hx => ?_
    have h1 : ((⟨x, hx⟩ : P) : ↥P ⧸ Z.subgroupOf P) = 1 :=
      (Nat.card_eq_one_iff_unique.mp hn).1.elim _ _
    exact (mk_eq_one_iff ⟨x, hx⟩).1 h1
  · rw [hn]
    exact dvd_pow_self 2 hn0.ne'

theorem act_eq_one (hS : Sec I P Z J) {j : Γ} (hj : j ∈ J) : hS.act ⟨j, hS.JI hj⟩ = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let τ : ↥J →* MulAut (↥P ⧸ Z.subgroupOf P) := hS.act.comp (Subgroup.inclusion hS.JI)
  letI : MulAction ↥J (↥P ⧸ Z.subgroupOf P) := MulAction.compHom _ τ
  have hfix1 : (1 : ↥P ⧸ Z.subgroupOf P) ∈ MulAction.fixedPoints ↥J (↥P ⧸ Z.subgroupOf P) :=
    fun j' => map_one (τ j')
  obtain ⟨q, hq, hq1⟩ :=
    hS.J2.exists_fixed_point_of_prime_dvd_card_of_fixed_point _ hS.two_dvd_card hfix1
  let Fx : Subgroup (↥P ⧸ Z.subgroupOf P) :=
    { carrier := {q | ∀ j' : J, τ j' q = q}
      mul_mem' := fun {a b} ha hb j' => by rw [map_mul, ha j', hb j']
      one_mem' := fun j' => map_one (τ j')
      inv_mem' := fun {a} ha j' => by rw [map_inv, ha j'] }
  have hFx : ∀ i : I, ∀ q ∈ Fx, hS.act i q ∈ Fx := by
    intro i q hq j'
    have hj' : (i : Γ)⁻¹ * (j' : Γ) * (i : Γ) ∈ J := by
      have := (Subgroup.mem_normalizer_iff.mp (hS.IJ (I.inv_mem i.2)) j').mp j'.2
      simpa using this
    have e : Subgroup.inclusion hS.JI j' * i = i * Subgroup.inclusion hS.JI ⟨_, hj'⟩ := by
      apply Subtype.ext
      simp [mul_assoc]
    show hS.act (Subgroup.inclusion hS.JI j') (hS.act i q) = hS.act i q
    rw [← MulAut.mul_apply, ← map_mul, e, map_mul, MulAut.mul_apply]
    congr 1
    exact hq ⟨_, hj'⟩
  rcases hS.irr_quot Fx hFx with h | h
  · exfalso
    have hqF : q ∈ Fx := fun j' => hq j'
    rw [h, Subgroup.mem_bot] at hqF
    exact hq1 hqF.symm
  · ext q'
    have hq' : q' ∈ Fx := by rw [h]; exact Subgroup.mem_top q'
    exact hq' ⟨j, hj⟩

variable [(J.subgroupOf I).Normal]

noncomputable def starAct (hS : Sec I P Z J) :
    ↥I ⧸ J.subgroupOf I →* MulAut (↥P ⧸ Z.subgroupOf P) :=
  QuotientGroup.lift (J.subgroupOf I) hS.act fun j hj => by
    rw [MonoidHom.mem_ker]
    exact hS.act_eq_one (Subgroup.mem_subgroupOf.1 hj)

theorem starAct_mk (hS : Sec I P Z J) (i : I) :
    hS.starAct (i : ↥I ⧸ J.subgroupOf I) = hS.act i :=
  QuotientGroup.lift_mk _ _ _

theorem conj_mem_of_act (hS : Sec I P Z J) {x b : Γ} (hx : x ∈ P) (hb : b ∈ P) {i : I}
    (h : hS.act i ((⟨b, hb⟩ : P) : ↥P ⧸ Z.subgroupOf P) = ((⟨x, hx⟩ : P) : ↥P ⧸ Z.subgroupOf P)) :
    ((i : Γ) * b * (i : Γ)⁻¹)⁻¹ * x ∈ Z := by
  rw [act_mk, QuotientGroup.eq, Subgroup.mem_subgroupOf] at h
  simpa using h

end Sec

end E214S

end CFSG.Quasithin.SimsE2
