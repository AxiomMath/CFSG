module

public import CFSG.RankThree.PartTwo.Sec14.Item14ListStatements
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.ONTwoRank
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.RankThree.PartTwo.Sec15.Liebeck156

open Sec4.Census.Karpilovsky.Coordinator.ONTwoRank (card_le_eight_of_isElemAbelian_ON)

private theorem apply_apply_apply_eq {X : Type*} [Group X] {γ : MulAut X} (hγ3 : γ ^ 3 = 1)
    (z : X) : γ (γ (γ z)) = z := by
  have h := congrArg (fun g : MulAut X => g z) hγ3
  simpa [pow_succ] using h

private theorem card_modEq_card_inf {X : Type*} [Group X] {p n : ℕ} [Fact p.Prime]
    {σ : MulAut X} (hσ : σ ^ p ^ n = 1) {H F : Subgroup X} [Finite H]
    (hH : ∀ h ∈ H, σ h ∈ H) (hF : ∀ x, x ∈ F ↔ σ x = x) :
    Nat.card H ≡ Nat.card ↥(H ⊓ F) [MOD p] := by
  classical
  letI : Fintype H := Fintype.ofFinite H
  let f : Function.End H := fun h => ⟨σ h, hH h h.2⟩
  have hpow : ∀ (k : ℕ) (h : H), (((f ^ k) h : H) : X) = (σ ^ k) h := by
    intro k
    induction k with
    | zero => intro h; rfl
    | succ k ih =>
      intro h
      rw [pow_succ, pow_succ]
      exact ih (f h)
  have hf : f ^ p ^ n = 1 := by
    funext h
    apply Subtype.ext
    rw [hpow, hσ]
    rfl
  have := Equiv.Perm.card_fixedPoints_modEq (f := f) hf
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card] at this
  have hcard : Nat.card ↥(Function.fixedPoints f) = Nat.card ↥(H ⊓ F) := by
    refine Nat.card_congr
      { toFun := fun x => ⟨(x.1 : X), x.1.2, (hF _).2 (congrArg Subtype.val x.2)⟩
        invFun := fun x => ⟨⟨(x : X), x.2.1⟩, Subtype.ext ((hF _).1 x.2.2)⟩
        left_inv := fun x => rfl
        right_inv := fun x => rfl }
  rwa [hcard] at this

private theorem card_modEq_one_of_fixedPointFree {X : Type*} [Group X] {P H : Subgroup X}
    [Finite H] (hHP : H ≤ P) {γ : MulAut X} (hγ3 : γ ^ 3 = 1) (hH : ∀ h ∈ H, γ h ∈ H)
    (hfpf : ∀ x ∈ P, γ x = x → x = 1) : Nat.card H ≡ 1 [MOD 3] := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h := card_modEq_card_inf (p := 3) (n := 1) (σ := γ) (by rwa [pow_one])
    (F := MonoidHom.eqLocus (γ : X →* X) (MonoidHom.id X)) hH (fun x => Iff.rfl)
  have hbot : H ⊓ MonoidHom.eqLocus (γ : X →* X) (MonoidHom.id X) = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    exact hfpf x (hHP hx.1) hx.2
  rwa [hbot, Subgroup.card_bot] at h

private theorem conj_mem_of_normal {X : Type*} [Group X] {Y P : Subgroup X} (hPY : P ≤ Y)
    (hPn : (P.subgroupOf Y).Normal) {y x : X} (hy : y ∈ Y) (hx : x ∈ P) : y * x * y⁻¹ ∈ P := by
  have h := hPn.conj_mem ⟨x, hPY hx⟩ (Subgroup.mem_subgroupOf.2 hx) ⟨y, hy⟩
  exact Subgroup.mem_subgroupOf.1 h

private theorem exists_fixed_mul_mem {X : Type*} [Group X] [Finite X] {Y P : Subgroup X}
    (hPY : P ≤ Y) (hPn : (P.subgroupOf Y).Normal) (hP2 : IsPGroup 2 P) {γ : MulAut X}
    (hγ3 : γ ^ 3 = 1) (hγP : ∀ x ∈ P, γ x ∈ P) (hγc : ∀ y ∈ Y, γ y * y⁻¹ ∈ P) {y : X}
    (hy : y ∈ Y) : ∃ x ∈ P, γ (y * x) = y * x := by
  classical
  have hγ3' := apply_apply_apply_eq hγ3
  have ht : y⁻¹ * γ y ∈ P := by
    have := conj_mem_of_normal hPY hPn (inv_mem hy) (hγc y hy)
    simpa [mul_assoc] using this
  letI : Fintype P := Fintype.ofFinite P
  let f : Function.End P := fun x => ⟨(y⁻¹ * γ y) * γ x, mul_mem ht (hγP x x.2)⟩
  have hf : f ^ 3 = 1 := by
    funext x
    apply Subtype.ext
    show (y⁻¹ * γ y) * γ ((y⁻¹ * γ y) * γ ((y⁻¹ * γ y) * γ x)) = x
    simp only [map_mul, map_inv, hγ3']
    group
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hmod := Equiv.Perm.card_fixedPoints_modEq (f := f) (p := 3) (n := 1) (by rwa [pow_one])
  by_contra hne
  push Not at hne
  have h0 : Fintype.card ↑(Function.fixedPoints f) = 0 := by
    rw [Fintype.card_eq_zero_iff]
    refine ⟨fun ⟨x, hx⟩ => hne x x.2 ?_⟩
    have h1 : (y⁻¹ * γ y) * γ (x : X) = x := congrArg Subtype.val hx
    simp only [map_mul]
    calc γ y * γ (x : X) = y * ((y⁻¹ * γ y) * γ (x : X)) := by group
      _ = y * x := by rw [h1]
  rw [h0] at hmod
  obtain ⟨m, hm⟩ := (IsPGroup.iff_card (p := 2)).1 hP2
  have h3 : 3 ∣ Nat.card P := by
    rw [← Nat.card_eq_fintype_card] at hmod
    exact (Nat.modEq_zero_iff_dvd).1 hmod
  rw [hm] at h3
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
  omega

private def omegaZ {X : Type*} [Group X] (P : Subgroup X) : Subgroup X where
  carrier := {x | x ∈ P ∧ x * x = 1 ∧ ∀ y ∈ P, x * y = y * x}
  one_mem' := ⟨one_mem _, mul_one 1, fun y _ => by rw [one_mul, mul_one]⟩
  mul_mem' := by
    rintro a b ⟨haP, ha2, hac⟩ ⟨hbP, hb2, hbc⟩
    refine ⟨mul_mem haP hbP, ?_, fun y hy => ?_⟩
    · have hab : a * b = b * a := hac b hbP
      calc a * b * (a * b) = a * (b * a) * b := by group
        _ = a * (a * b) * b := by rw [hab]
        _ = (a * a) * (b * b) := by group
        _ = 1 := by rw [ha2, hb2, one_mul]
    · rw [mul_assoc, hbc y hy, ← mul_assoc, hac y hy, mul_assoc]
  inv_mem' := by
    rintro a ⟨haP, ha2, hac⟩
    have hinv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
    change a⁻¹ ∈ P ∧ a⁻¹ * a⁻¹ = 1 ∧ ∀ y ∈ P, a⁻¹ * y = y * a⁻¹
    rw [hinv]
    exact ⟨haP, ha2, hac⟩

private theorem omegaZ_le {X : Type*} [Group X] (P : Subgroup X) : omegaZ P ≤ P :=
  fun _ hx => hx.1

private theorem isElemAbelian_omegaZ {X : Type*} [Group X] (P : Subgroup X) :
    CFSG.Open.IsElemAbelian 2 (omegaZ P) :=
  ⟨⟨⟨fun a b => Subtype.ext (a.2.2.2 b b.2.1)⟩⟩, fun x hx => by rw [pow_two]; exact hx.2.1⟩

private theorem omegaZ_ne_bot {X : Type*} [Group X] [Finite X] {P : Subgroup X}
    (hP : IsPGroup 2 P) (hne : P ≠ ⊥) : omegaZ P ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Nontrivial P := (Subgroup.nontrivial_iff_ne_bot P).mpr hne
  have : Nontrivial (Subgroup.center P) := hP.center_nontrivial
  have hdvd : 2 ∣ Nat.card (Subgroup.center P) := by
    rcases (hP.to_subgroup (Subgroup.center P)).card_eq_or_dvd with hone | hdiv
    · have : Subsingleton (Subgroup.center P) := (Nat.card_eq_one_iff_unique.mp hone).1
      exact (not_subsingleton (Subgroup.center P) this).elim
    · exact hdiv
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center P) 2 hdvd
  have hc' : orderOf ((c : P) : X) = 2 := by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]
    exact hc
  intro hbot
  have hmem : ((c : P) : X) ∈ omegaZ P := by
    refine ⟨(c : P).2, ?_, fun y hy => ?_⟩
    · rw [← pow_two, ← hc']
      exact pow_orderOf_eq_one _
    · have h := Subgroup.mem_center_iff.mp c.2 ⟨y, hy⟩
      exact (congrArg Subtype.val h).symm
  rw [hbot, Subgroup.mem_bot] at hmem
  rw [hmem, orderOf_one] at hc'
  exact absurd hc' (by norm_num)

private theorem conj_mem_omegaZ {X : Type*} [Group X] {Y P : Subgroup X} (hPY : P ≤ Y)
    (hPn : (P.subgroupOf Y).Normal) {y w : X} (hy : y ∈ Y) (hw : w ∈ omegaZ P) :
    y * w * y⁻¹ ∈ omegaZ P := by
  obtain ⟨hwP, hw2, hwc⟩ := hw
  refine ⟨conj_mem_of_normal hPY hPn hy hwP, ?_, fun p hp => ?_⟩
  · calc y * w * y⁻¹ * (y * w * y⁻¹) = y * (w * w) * y⁻¹ := by group
      _ = 1 := by rw [hw2]; group
  · have hp' : y⁻¹ * p * y ∈ P := by
      simpa using conj_mem_of_normal hPY hPn (inv_mem hy) hp
    have h := hwc _ hp'
    calc y * w * y⁻¹ * p = y * (w * (y⁻¹ * p * y)) * y⁻¹ := by group
      _ = y * ((y⁻¹ * p * y) * w) * y⁻¹ := by rw [h]
      _ = p * (y * w * y⁻¹) := by group

private theorem map_mem_omegaZ {X : Type*} [Group X] {P : Subgroup X} {γ : MulAut X}
    (hγ3 : ∀ z, γ (γ (γ z)) = z) (hγP : ∀ x ∈ P, γ x ∈ P) {w : X} (hw : w ∈ omegaZ P) :
    γ w ∈ omegaZ P := by
  obtain ⟨hwP, hw2, hwc⟩ := hw
  refine ⟨hγP w hwP, by rw [← map_mul, hw2, map_one], fun p hp => ?_⟩
  have hp' : γ (γ p) ∈ P := hγP _ (hγP _ hp)
  have h := congrArg γ (hwc _ hp')
  rw [map_mul, map_mul, hγ3 p] at h
  exact h

private theorem alt5_klein : ∃ a b : alternatingGroup (Fin 5), a * a = 1 ∧ b * b = 1 ∧
    a * b = b * a ∧ a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b :=
  ⟨⟨Equiv.swap 0 1 * Equiv.swap 2 3, Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩,
    ⟨Equiv.swap 0 2 * Equiv.swap 1 3, Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩, by decide⟩

private theorem exists_klein_lift {X : Type*} [Group X] [Finite X] {Y P : Subgroup X}
    (hPY : P ≤ Y) (hPn : (P.subgroupOf Y).Normal) (hP2 : IsPGroup 2 P)
    (hA5 : Nonempty (↥Y ⧸ P.subgroupOf Y ≃* alternatingGroup (Fin 5))) {γ : MulAut X}
    (hγ3 : γ ^ 3 = 1) (hγP : ∀ x ∈ P, γ x ∈ P) (hγc : ∀ y ∈ Y, γ y * y⁻¹ ∈ P)
    (hfpf : ∀ x ∈ P, γ x = x → x = 1) :
    ∃ a b : X, a ∈ Y ∧ b ∈ Y ∧ γ a = a ∧ γ b = b ∧ a * a = 1 ∧ b * b = 1 ∧
      a * b = b * a ∧ a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b := by
  obtain ⟨e⟩ := hA5
  let q : ↥Y →* alternatingGroup (Fin 5) := e.toMonoidHom.comp (QuotientGroup.mk' (P.subgroupOf Y))
  have hq1 : ∀ y : Y, q y = 1 → (y : X) ∈ P := fun y hy => by
    have h1 : QuotientGroup.mk' (P.subgroupOf Y) y = 1 := e.injective (by rw [map_one]; exact hy)
    exact Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff y).1 h1)
  have hq2 : ∀ y : Y, (y : X) ∈ P → q y = 1 := fun y hy => by
    have h1 : QuotientGroup.mk' (P.subgroupOf Y) y = 1 :=
      (QuotientGroup.eq_one_iff y).2 (Subgroup.mem_subgroupOf.2 hy)
    show e (QuotientGroup.mk' (P.subgroupOf Y) y) = 1
    rw [h1]
    exact map_one e
  have hqs : Function.Surjective q := fun z => by
    obtain ⟨w, rfl⟩ := e.surjective z
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (P.subgroupOf Y) w
    exact ⟨y, rfl⟩
  obtain ⟨a₀, b₀, ha₀, hb₀, hab₀, ha1, hb1, hab1⟩ := alt5_klein
  obtain ⟨ya, hya⟩ := hqs a₀
  obtain ⟨yb, hyb⟩ := hqs b₀
  obtain ⟨xa, hxa, hfa⟩ := exists_fixed_mul_mem hPY hPn hP2 hγ3 hγP hγc ya.2
  obtain ⟨xb, hxb, hfb⟩ := exists_fixed_mul_mem hPY hPn hP2 hγ3 hγP hγc yb.2
  let a : Y := ya * ⟨xa, hPY hxa⟩
  let b : Y := yb * ⟨xb, hPY hxb⟩
  have hqa : q a = a₀ := by rw [map_mul, hya, hq2 ⟨xa, hPY hxa⟩ hxa, mul_one]
  have hqb : q b = b₀ := by rw [map_mul, hyb, hq2 ⟨xb, hPY hxb⟩ hxb, mul_one]
  have hγa : γ (a : X) = a := hfa
  have hγb : γ (b : X) = b := hfb
  have key : ∀ c : Y, q c = 1 → γ (c : X) = c → (c : X) = 1 :=
    fun c hc hγ => hfpf _ (hq1 c hc) hγ
  refine ⟨a, b, a.2, b.2, hγa, hγb, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact key (a * a) (by rw [map_mul, hqa, ha₀]) (by simp [map_mul, hγa])
  · exact key (b * b) (by rw [map_mul, hqb, hb₀]) (by simp [map_mul, hγb])
  · have h := key (a * b * a⁻¹ * b⁻¹)
      (by rw [map_mul, map_mul, map_mul, map_inv, map_inv, hqa, hqb, hab₀]; group)
      (by simp [map_mul, map_inv, hγa, hγb])
    have h' : (a : X) * b * (a : X)⁻¹ * (b : X)⁻¹ = 1 := h
    exact mul_inv_eq_one.1 (by simpa [mul_assoc] using h')
  · intro h
    have : a = 1 := Subtype.ext h
    rw [this, map_one] at hqa
    exact ha1 hqa.symm
  · intro h
    have : b = 1 := Subtype.ext h
    rw [this, map_one] at hqb
    exact hb1 hqb.symm
  · intro h
    have : a = b := Subtype.ext h
    rw [this, hqb] at hqa
    exact hab1 hqa.symm

private theorem four_le_card_closure {X : Type*} [Group X] [Finite X] {a b : X}
    (haa : a * a = 1) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab1 : a ≠ b) :
    4 ≤ Nat.card ↥(Subgroup.closure ({a, b} : Set X)) := by
  have ha : a ∈ Subgroup.closure ({a, b} : Set X) := Subgroup.subset_closure (by simp)
  have hb : b ∈ Subgroup.closure ({a, b} : Set X) := Subgroup.subset_closure (by simp)
  have hab1' : a * b ≠ 1 := fun h => hab1 (by
    rw [eq_inv_of_mul_eq_one_right h, inv_eq_of_mul_eq_one_right haa])
  let y : Fin 4 → X := ![1, a, b, a * b]
  have hy : Function.Injective y := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> first | rfl | (exfalso; simp [y] at hij; first
      | exact ha1 hij | exact ha1 hij.symm | exact hb1 hij | exact hb1 hij.symm
      | exact hab1' hij | exact hab1' hij.symm | exact hab1 hij | exact hab1 hij.symm)
  have hmem : ∀ i, y i ∈ Subgroup.closure ({a, b} : Set X) := by
    intro i
    fin_cases i <;> simp [y, one_mem, ha, hb, mul_mem ha hb]
  have := Nat.card_le_card_of_injective
    (fun i => (⟨y i, hmem i⟩ : Subgroup.closure ({a, b} : Set X)))
    (fun i j h => hy (congrArg Subtype.val h))
  simpa using this

private theorem exists_centralized_four_le {X : Type*} [Group X] [Finite X] {Y P : Subgroup X}
    (hPY : P ≤ Y) (hPn : (P.subgroupOf Y).Normal) (hP2 : IsPGroup 2 P) (hne : P ≠ ⊥)
    {γ : MulAut X} (hγ3 : γ ^ 3 = 1) (hγP : ∀ x ∈ P, γ x ∈ P)
    (hfpf : ∀ x ∈ P, γ x = x → x = 1) {a b : X} (haY : a ∈ Y) (hbY : b ∈ Y)
    (hγa : γ a = a) (hγb : γ b = b) (haa : a * a = 1) (hbb : b * b = 1) (hab : a * b = b * a) :
    ∃ W : Subgroup X, W ≤ P ∧ CFSG.Open.IsElemAbelian 2 W ∧
      (∀ x ∈ W, x * a = a * x ∧ x * b = b * x) ∧ 4 ≤ Nat.card W := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hγ3' := apply_apply_apply_eq hγ3
  have hconj2 : ∀ {t : X}, t * t = 1 → (MulAut.conj t) ^ 2 ^ 1 = 1 := fun {t} ht => by
    rw [pow_one, ← map_pow, pow_two, ht, map_one]
  have hFt : ∀ t x : X, x ∈ Subgroup.centralizer ({t} : Set X) ↔ (MulAut.conj t) x = x :=
    fun t x => by
      rw [Subgroup.mem_centralizer_singleton_iff, MulAut.conj_apply, mul_inv_eq_iff_eq_mul,
        eq_comm]
  have hWne : omegaZ P ≠ ⊥ := omegaZ_ne_bot hP2 hne
  have hWP : omegaZ P ≤ P := omegaZ_le P
  have hWev : 2 ∣ Nat.card (omegaZ P) := by
    rcases (hP2.to_le hWP).card_eq_or_dvd with h1 | h2
    · exact absurd (Subgroup.card_eq_one.1 h1) hWne
    · exact h2
  set W₁ : Subgroup X := omegaZ P ⊓ Subgroup.centralizer ({a} : Set X) with hW₁
  set W₂ : Subgroup X := W₁ ⊓ Subgroup.centralizer ({b} : Set X) with hW₂
  have h1 : Nat.card (omegaZ P) ≡ Nat.card W₁ [MOD 2] :=
    card_modEq_card_inf (hconj2 haa) (fun h hh => by
      rw [MulAut.conj_apply]; exact conj_mem_omegaZ hPY hPn haY hh) (hFt a)
  have hW₁ev : 2 ∣ Nat.card W₁ :=
    Nat.modEq_zero_iff_dvd.1 (h1.symm.trans (Nat.modEq_zero_iff_dvd.2 hWev))
  have hW₁b : ∀ h ∈ W₁, (MulAut.conj b) h ∈ W₁ := by
    intro h hh
    obtain ⟨hhW, hha⟩ := Subgroup.mem_inf.1 hh
    have hha' : h * a = a * h := Subgroup.mem_centralizer_singleton_iff.1 hha
    rw [MulAut.conj_apply]
    refine Subgroup.mem_inf.2 ⟨conj_mem_omegaZ hPY hPn hbY hhW,
      Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    have hab' : Commute a b := hab
    have hah : Commute a h := hha'.symm
    exact ((hab'.mul_right hah).mul_right hab'.inv_right).eq.symm
  have h2 : Nat.card W₁ ≡ Nat.card W₂ [MOD 2] :=
    card_modEq_card_inf (hconj2 hbb) hW₁b (hFt b)
  have hW₂ev : 2 ∣ Nat.card W₂ :=
    Nat.modEq_zero_iff_dvd.1 (h2.symm.trans (Nat.modEq_zero_iff_dvd.2 hW₁ev))
  have hW₂P : W₂ ≤ P := fun x hx => hWP (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hx).1).1
  have hW₂γ : ∀ h ∈ W₂, γ h ∈ W₂ := by
    intro h hh
    obtain ⟨hh1, hhb⟩ := Subgroup.mem_inf.1 hh
    obtain ⟨hhW, hha⟩ := Subgroup.mem_inf.1 hh1
    have hha' : h * a = a * h := Subgroup.mem_centralizer_singleton_iff.1 hha
    have hhb' : h * b = b * h := Subgroup.mem_centralizer_singleton_iff.1 hhb
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨map_mem_omegaZ hγ3' hγP hhW,
      Subgroup.mem_centralizer_singleton_iff.2 ?_⟩, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    · have := congrArg γ hha'
      rwa [map_mul, map_mul, hγa] at this
    · have := congrArg γ hhb'
      rwa [map_mul, map_mul, hγb] at this
  have h3 := card_modEq_one_of_fixedPointFree hW₂P hγ3 hW₂γ hfpf
  refine ⟨W₂, hW₂P, (isElemAbelian_omegaZ P).mono (fun x hx =>
    (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hx).1).1), fun x hx => ⟨?_, ?_⟩, ?_⟩
  · exact Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hx).1).2
  · exact Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hx).2
  · obtain ⟨j, hj⟩ := (IsPGroup.iff_card (p := 2)).1 (hP2.to_le hW₂P)
    rw [hj] at hW₂ev h3 ⊢
    rcases j with _ | _ | j
    · simp at hW₂ev
    · exact absurd h3 (by decide)
    · calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (j + 1 + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)

private theorem exists_elemAbelian_sixteen_le {X : Type*} [Group X] [Finite X]
    {Y P : Subgroup X} (hPY : P ≤ Y) (hPn : (P.subgroupOf Y).Normal) (hP2 : IsPGroup 2 P)
    (hA5 : Nonempty (↥Y ⧸ P.subgroupOf Y ≃* alternatingGroup (Fin 5))) {γ : MulAut X}
    (hγ3 : γ ^ 3 = 1) (hγP : ∀ x ∈ P, γ x ∈ P) (hγc : ∀ y ∈ Y, γ y * y⁻¹ ∈ P)
    (hfpf : ∀ x ∈ P, γ x = x → x = 1) (hne : P ≠ ⊥) :
    ∃ E : Subgroup X, CFSG.Open.IsElemAbelian 2 E ∧ 16 ≤ Nat.card E := by
  obtain ⟨a, b, haY, hbY, hγa, hγb, haa, hbb, hab, ha1, hb1, hab1⟩ :=
    exists_klein_lift hPY hPn hP2 hA5 hγ3 hγP hγc hfpf
  obtain ⟨W, hWP, hWE, hWc, hW4⟩ :=
    exists_centralized_four_le hPY hPn hP2 hne hγ3 hγP hfpf haY hbY hγa hγb haa hbb hab
  set V : Subgroup X := Subgroup.closure ({a, b} : Set X) with hV
  have hVE : CFSG.Open.IsElemAbelian 2 V := by
    refine CFSG.Open.IsElemAbelian.closure_of_commute (fun x hx y hy => ?_) (fun x hx => ?_)
    · rcases hx with rfl | hx
      · rcases hy with rfl | hy
        · rfl
        · rw [Set.mem_singleton_iff] at hy
          rw [hy]; exact hab
      · rw [Set.mem_singleton_iff] at hx
        rcases hy with rfl | hy
        · rw [hx]; exact hab.symm
        · rw [Set.mem_singleton_iff] at hy
          rw [hx, hy]
    · rcases hx with rfl | hx
      · rw [pow_two]; exact haa
      · rw [Set.mem_singleton_iff] at hx
        rw [hx, pow_two]; exact hbb
  have hVfix : ∀ x ∈ V, γ x = x := by
    have hle : V ≤ MonoidHom.eqLocus (γ : X →* X) (MonoidHom.id X) := by
      refine (Subgroup.closure_le _).2 ?_
      intro x hx
      rcases hx with rfl | hx
      · exact hγa
      · rw [Set.mem_singleton_iff] at hx
        rw [hx]; exact hγb
    exact fun x hx => hle hx
  have hWV : ∀ x ∈ W, ∀ y ∈ V, x * y = y * x := by
    have hle : V ≤ Subgroup.centralizer (W : Set X) := by
      refine (Subgroup.closure_le _).2 ?_
      intro y hy
      rcases hy with rfl | hy
      · exact Subgroup.mem_centralizer_iff.2 (fun h hh => (hWc h hh).1)
      · rw [Set.mem_singleton_iff] at hy
        rw [hy]
        exact Subgroup.mem_centralizer_iff.2 (fun h hh => (hWc h hh).2)
    exact fun x hx y hy => Subgroup.mem_centralizer_iff.1 (hle hy) x hx
  refine ⟨W ⊔ V, hWE.sup_of_commute hVE hWV, ?_⟩
  have hinj : Function.Injective (fun p : W × V => (⟨(p.1 : X) * p.2,
      mul_mem (Subgroup.mem_sup_left p.1.2) (Subgroup.mem_sup_right p.2.2)⟩ : ↥(W ⊔ V))) := by
    rintro ⟨⟨w, hw⟩, ⟨v, hv⟩⟩ ⟨⟨w', hw'⟩, ⟨v', hv'⟩⟩ h
    have h' : w * v = w' * v' := congrArg Subtype.val h
    have h1 : w'⁻¹ * w = v' * v⁻¹ := by
      calc w'⁻¹ * w = w'⁻¹ * (w * v) * v⁻¹ := by group
        _ = w'⁻¹ * (w' * v') * v⁻¹ := by rw [h']
        _ = v' * v⁻¹ := by group
    have hfix : γ (w'⁻¹ * w) = w'⁻¹ * w := by
      rw [h1]
      simp only [map_mul, map_inv, hVfix v hv, hVfix v' hv']
    have h2 : w'⁻¹ * w = 1 := hfpf _ (mul_mem (inv_mem (hWP hw')) (hWP hw)) hfix
    have hww : w' = w := inv_mul_eq_one.1 h2
    subst hww
    have hvv : v = v' := mul_left_cancel h'
    subst hvv
    rfl
  have hcard := Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_prod] at hcard
  have hV4 : 4 ≤ Nat.card V := four_le_card_closure haa ha1 hb1 hab1
  calc 16 = 4 * 4 := by norm_num
    _ ≤ Nat.card W * Nat.card V := Nat.mul_le_mul hW4 hV4
    _ ≤ Nat.card ↥(W ⊔ V) := hcard

private theorem card_alt5 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  rw [nat_card_alternatingGroup]
  simp [Nat.factorial]

private theorem card_alt6 : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  rw [nat_card_alternatingGroup]
  simp [Nat.factorial]

private theorem false_of_index_three {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hG : 6 < Nat.card G) {H : Subgroup G} (h : H.index = 3) : False := by
  let φ := MulAction.toPermHom G (G ⧸ H)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal φ.ker with hk | hk
  · have hinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).mp hk
    have h1 := Nat.card_le_card_of_injective _ hinj
    rw [Nat.card_perm] at h1
    have hc : Nat.card (G ⧸ H) = 3 := h
    rw [hc] at h1
    norm_num [Nat.factorial] at h1
    omega
  · have hHtop : H = ⊤ := by
      rw [eq_top_iff]
      intro x _
      have hx : x ∈ φ.ker := by rw [hk]; exact Subgroup.mem_top x
      rw [MonoidHom.mem_ker] at hx
      have h2 := congrArg (fun f : Equiv.Perm (G ⧸ H) => f (QuotientGroup.mk 1)) hx
      simp only [φ, MulAction.toPermHom_apply, MulAction.toPerm_apply, Equiv.Perm.coe_one,
        id_eq] at h2
      have h3 : (QuotientGroup.mk (x * 1) : G ⧸ H) = QuotientGroup.mk 1 := h2
      rw [QuotientGroup.eq] at h3
      simpa using H.inv_mem h3
    rw [hHtop, Subgroup.index_top] at h
    omega

private theorem ker_eq_of_ker_le {Y : Type*} [Group Y] [Finite Y] {N : Subgroup Y}
    (hN : IsPGroup 2 N) (hY60 : Nat.card Y = 60 * Nat.card N)
    (f : Y →* alternatingGroup (Fin 6)) (hKN : f.ker ≤ N) : f.ker = N := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI hs6 : IsSimpleGroup (alternatingGroup (Fin 6)) :=
    alternatingGroup.isSimpleGroup (by simp)
  have hrange := Subgroup.card_ker_mul_card_range f
  have hdvd := Subgroup.card_subgroup_dvd_card f.range
  rw [card_alt6] at hdvd
  obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le hKN
  have hKpos : 0 < Nat.card f.ker := Nat.card_pos
  have hR : Nat.card f.range = 60 * m := by
    refine Nat.eq_of_mul_eq_mul_left hKpos ?_
    rw [hrange, hY60, hm]
    ring
  rw [hR] at hdvd
  have hm6 : m ∣ 6 := by
    have : 60 * m ∣ 60 * 6 := by simpa using hdvd
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) this
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card (p := 2)).1 hN
  have hm2 : m ∣ 2 ^ a := ⟨Nat.card f.ker, by rw [← ha, hm]; ring⟩
  have hm_le : m ≤ 6 := Nat.le_of_dvd (by norm_num) hm6
  have hm_pos : 0 < m := Nat.pos_of_dvd_of_pos hm6 (by norm_num)
  have h3 : ¬ 3 ∣ 2 ^ a := fun h => by
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
    omega
  interval_cases m
  · have hle : Nat.card N ≤ Nat.card f.ker := by omega
    exact Subgroup.eq_of_le_of_card_ge hKN hle
  · exfalso
    have h3' : f.range.index = 3 := by
      have := Subgroup.card_mul_index f.range
      rw [hR, card_alt6] at this
      omega
    exact false_of_index_three (by rw [card_alt6]; norm_num) h3'
  · exact absurd hm2 h3
  · omega
  · omega
  · exact absurd ((by norm_num : 3 ∣ 6).trans hm2) h3

private theorem apply_eq_one_of_perfect {Y H : Type*} [Group Y] [Group H] [Finite H]
    (hY : Group.IsPerfect Y) {N : Subgroup Y} (hN : IsPGroup 2 N) (f : Y →* H)
    (hall : ∀ y : Y, ∃ n ∈ N, f y = f n) (y : Y) : f y = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := hY
  haveI : Group.IsPerfect f.range := Group.IsPerfect.range f
  have hR2 : IsPGroup 2 f.range := by
    intro g
    obtain ⟨y, hy⟩ := g.2
    obtain ⟨n, hn, hfn⟩ := hall y
    obtain ⟨k, hk⟩ := hN ⟨n, hn⟩
    refine ⟨k, Subtype.ext ?_⟩
    rw [Subgroup.coe_pow, ← hy, hfn, ← map_pow]
    have : n ^ 2 ^ k = 1 := congrArg Subtype.val hk
    rw [this, map_one]
    rfl
  have hsub : Subsingleton f.range := by
    by_contra hns
    rw [not_subsingleton_iff_nontrivial] at hns
    exact Group.IsPerfect.not_isNilpotent f.range hR2.isNilpotent
  exact congrArg Subtype.val (Subsingleton.elim (⟨f y, f.mem_range.2 ⟨y, rfl⟩⟩ : f.range) 1)

theorem le_ker_of_hom_A6 {Y : Type*} [Group Y] [Finite Y] (hY : Group.IsPerfect Y)
    {N : Subgroup Y} [N.Normal] (hN : IsPGroup 2 N)
    (hA5 : Nonempty (Y ⧸ N ≃* alternatingGroup (Fin 5)))
    (f : Y →* alternatingGroup (Fin 6)) : N ≤ f.ker := by
  obtain ⟨e⟩ := hA5
  haveI hs5 : IsSimpleGroup (alternatingGroup (Fin 5)) :=
    alternatingGroup.isSimpleGroup (by simp)
  haveI hs : IsSimpleGroup (Y ⧸ N) := e.isSimpleGroup
  haveI hKn : (f.ker.map (QuotientGroup.mk' N)).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective N)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (f.ker.map (QuotientGroup.mk' N)) with
    hbot | htop
  · have hKN : f.ker ≤ N := fun x hx => by
      have h := Subgroup.mem_map_of_mem (QuotientGroup.mk' N) hx
      rw [hbot, Subgroup.mem_bot] at h
      exact (QuotientGroup.eq_one_iff x).1 h
    have hY60 : Nat.card Y = 60 * Nat.card N := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup N, Nat.card_congr e.toEquiv, card_alt5]
    exact (ker_eq_of_ker_le hN hY60 f hKN).symm.le
  · have hall : ∀ y : Y, ∃ n ∈ N, f y = f n := by
      intro y
      have hy : QuotientGroup.mk' N y ∈ f.ker.map (QuotientGroup.mk' N) := by
        rw [htop]; trivial
      obtain ⟨k, hk, hky⟩ := Subgroup.mem_map.1 hy
      have hkn : k⁻¹ * y ∈ N := QuotientGroup.eq.1 hky
      refine ⟨k⁻¹ * y, hkn, ?_⟩
      rw [map_mul, map_inv, MonoidHom.mem_ker.1 hk, inv_one, one_mul]
    exact fun x _ => apply_eq_one_of_perfect hY hN f hall x

private theorem exists_hom_A6_ker_eq {X : Type*} [Group X] {U V : Subgroup X} [V.Normal]
    (hUV : U ⊔ V = ⊤) (hcomm : ⁅U, V⁆ = ⊥) (hcard : Nat.card ↥(U ⊓ V) = 3)
    (hU : Sec4.IsTripleCover ↥U (alternatingGroup (Fin 6))) :
    ∃ f : X →* alternatingGroup (Fin 6), f.ker = V := by
  obtain ⟨hZ, ⟨e⟩⟩ := hU
  let g : ↥U →* X ⧸ V := (QuotientGroup.mk' V).comp U.subtype
  have hgs : Function.Surjective g := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    have hx : x ∈ U ⊔ V := by rw [hUV]; exact Subgroup.mem_top x
    obtain ⟨u, hu, v, hv, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 hx
    refine ⟨⟨u, hu⟩, ?_⟩
    show (QuotientGroup.mk u : X ⧸ V) = QuotientGroup.mk (u * v)
    rw [QuotientGroup.eq]
    simpa using hv
  have hker0 : ∀ u : ↥U, u ∈ g.ker ↔ (u : X) ∈ V := fun u => by
    rw [MonoidHom.mem_ker]
    exact QuotientGroup.eq_one_iff (u : X)
  have hUc : U ≤ Subgroup.centralizer (V : Set X) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm
  have hle : g.ker ≤ Subgroup.center ↥U := by
    intro u hu
    rw [Subgroup.mem_center_iff]
    intro w
    exact Subtype.ext (Subgroup.mem_centralizer_iff.1 (hUc w.2) _ ((hker0 u).1 hu)).symm
  have hcard' : Nat.card g.ker = 3 := by
    rw [← hcard]
    exact Nat.card_congr
      { toFun := fun u => ⟨(u.1 : X), u.1.2, (hker0 u.1).1 u.2⟩
        invFun := fun x => ⟨⟨x.1, x.2.1⟩, (hker0 _).2 x.2.2⟩
        left_inv := fun u => rfl
        right_inv := fun x => rfl }
  haveI : Finite (Subgroup.center ↥U) := Nat.finite_of_card_ne_zero (by rw [hZ]; norm_num)
  have hker : g.ker = Subgroup.center ↥U :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hZ, hcard'])
  let ψ : X ⧸ V ≃* alternatingGroup (Fin 6) :=
    ((QuotientGroup.quotientKerEquivOfSurjective g hgs).symm.trans
      (QuotientGroup.quotientMulEquivOfEq hker)).trans e
  refine ⟨ψ.toMonoidHom.comp (QuotientGroup.mk' V), ?_⟩
  ext x
  rw [MonoidHom.mem_ker]
  show ψ (QuotientGroup.mk' V x) = 1 ↔ x ∈ V
  rw [map_eq_one_iff ψ ψ.injective]
  exact QuotientGroup.eq_one_iff x

private theorem eq_bot_of_le_of_card_three {X : Type*} [Group X] {P Z : Subgroup X} [Finite P]
    (hP : IsPGroup 2 P) (hle : P ≤ Z) (hZ : Nat.card Z = 3) : P = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, hm⟩ := (IsPGroup.iff_card (p := 2)).1 hP
  have hdvd : Nat.card P ∣ Nat.card Z := Subgroup.card_dvd_of_le hle
  rw [hm, hZ] at hdvd
  have hm0 : m = 0 := by
    rcases m with _ | m
    · rfl
    · exfalso
      have : 2 ∣ 3 := (dvd_pow_self 2 (Nat.succ_ne_zero m)).trans hdvd
      omega
  rw [hm0, pow_zero] at hm
  exact Subgroup.card_eq_one.1 hm

private theorem pow_three_of_mem {X : Type*} [Group X] {Z : Subgroup X} (hZ : Nat.card Z = 3)
    {x : X} (hx : x ∈ Z) : x ^ 3 = 1 := by
  have := orderOf_dvd_natCard (⟨x, hx⟩ : Z)
  rw [hZ, Subgroup.orderOf_mk] at this
  exact orderOf_dvd_iff_pow_eq_one.mp this

section Certified


private theorem card_le_eight_of_hom {X : Type*} [Group X]
    (π : X →* CFSG.Blueprint.NativeSporadic.ON) (hker : ∀ x, π x = 1 → x ^ 3 = 1)
    {E : Subgroup X} (hE : CFSG.Open.IsElemAbelian 2 E) : Nat.card E ≤ 8 := by
  have hinj : Function.Injective (π.comp E.subtype) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    apply Subtype.ext
    have h3 : (x : X) ^ 3 = 1 := hker x hx
    have h2 : (x : X) ^ 2 = 1 := hE.2 x x.2
    show (x : X) = 1
    calc (x : X) = (x : X) ^ 3 * ((x : X) ^ 2)⁻¹ := by group
      _ = 1 := by rw [h3, h2, inv_one, one_mul]
  have hrange : (π.comp E.subtype).range = E.map π := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hcard : Nat.card (E.map π) = Nat.card E := by
    rw [← hrange]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have := card_le_eight_of_isElemAbelian_ON (E.map π) (hE.map π)
  rwa [hcard] at this

theorem eq_bot_of_hom_ON {X : Type*} [Group X] [Finite X]
    (π : X →* CFSG.Blueprint.NativeSporadic.ON) (hker : ∀ x, π x = 1 → x ^ 3 = 1)
    {Y P : Subgroup X} (hPY : P ≤ Y) (hP2 : IsPGroup 2 P) (hPn : (P.subgroupOf Y).Normal)
    (hA5 : Nonempty (↥Y ⧸ P.subgroupOf Y ≃* alternatingGroup (Fin 5)))
    (γ : MulAut X) (hγ3 : γ ^ 3 = 1) (hγP : ∀ x ∈ P, γ x ∈ P)
    (hγc : ∀ y ∈ Y, γ y * y⁻¹ ∈ P) (hfpf : ∀ x ∈ P, γ x = x → x = 1) : P = ⊥ := by
  by_contra hne
  obtain ⟨E, hE, h16⟩ := exists_elemAbelian_sixteen_le hPY hPn hP2 hA5 hγ3 hγP hγc hfpf hne
  have := card_le_eight_of_hom π hker hE
  omega

theorem eq_bot_of_type156 {Xt : Type*} [Group Xt] [Finite Xt]
    (htype : Sec4.IsTripleCover Xt CFSG.Blueprint.NativeSporadic.ON ∨
      Sec4.IsTripleCover Xt (alternatingGroup (Fin 6)) ∨ Sec14.IsCentralProductA6Covers Xt)
    {Yt Pt : Subgroup Xt} (hYt : Group.IsPerfect ↥Yt) (hPY : Pt ≤ Yt) (hP2 : IsPGroup 2 Pt)
    (hPn : (Pt.subgroupOf Yt).Normal)
    (hA5 : Nonempty (↥Yt ⧸ Pt.subgroupOf Yt ≃* alternatingGroup (Fin 5)))
    (γ : MulAut Xt) (hγ3 : γ ^ 3 = 1) (_hγY : ∀ y ∈ Yt, γ y ∈ Yt)
    (hγP : ∀ x ∈ Pt, γ x ∈ Pt) (hγc : ∀ y ∈ Yt, γ y * y⁻¹ ∈ Pt)
    (hfpf : ∀ x ∈ Pt, γ x = x → x = 1) : Pt = ⊥ := by
  have hA6 : ∀ f : Xt →* alternatingGroup (Fin 6), Pt ≤ f.ker := fun f x hx => by
    have hx' : (⟨x, hPY hx⟩ : Yt) ∈ Pt.subgroupOf Yt := Subgroup.mem_subgroupOf.2 hx
    exact le_ker_of_hom_A6 hYt (hP2.of_equiv (Subgroup.subgroupOfEquivOfLe hPY).symm) hA5
      (f.comp Yt.subtype) hx'
  rcases htype with ⟨hZ, ⟨e⟩⟩ | ⟨hZ, ⟨e⟩⟩ | ⟨U, V, hUn, hVn, hUV, hcomm, hcard, hTU, hTV⟩
  · refine eq_bot_of_hom_ON (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center Xt))) ?_ hPY
      hP2 hPn hA5 γ hγ3 hγP hγc hfpf
    intro x hx
    have hx1 : QuotientGroup.mk' (Subgroup.center Xt) x = 1 :=
      e.injective (by rw [map_one]; exact hx)
    exact pow_three_of_mem hZ ((QuotientGroup.eq_one_iff x).1 hx1)
  · refine eq_bot_of_le_of_card_three hP2 (fun x hx => ?_) hZ
    have h1 := hA6 (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center Xt))) hx
    have hx1 : QuotientGroup.mk' (Subgroup.center Xt) x = 1 :=
      e.injective (by rw [map_one]; exact h1)
    exact (QuotientGroup.eq_one_iff x).1 hx1
  · obtain ⟨f₁, hf₁⟩ := exists_hom_A6_ker_eq hUV hcomm hcard hTU
    obtain ⟨f₂, hf₂⟩ := exists_hom_A6_ker_eq (U := V) (V := U) (by rwa [sup_comm])
      (by rwa [Subgroup.commutator_comm]) (by rwa [inf_comm]) hTV
    refine eq_bot_of_le_of_card_three hP2 (fun x hx => ?_) hcard
    exact ⟨by rw [← hf₂]; exact hA6 f₂ hx, by rw [← hf₁]; exact hA6 f₁ hx⟩

end Certified

end CFSG.RankThree.PartTwo.Sec15.Liebeck156
