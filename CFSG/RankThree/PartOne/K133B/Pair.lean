module

public import CFSG.RankThree.PartOne.Q1327T.Pair

public section

namespace CFSG.RankThree.PartOne.K133B

open CFSG CFSG.RankThree.PartOne

variable {G : Type} [Group G] {p : ℕ} {E : Subgroup G}

theorem isAutTransvection_of_same_moved [Finite G] (hd : RefFacts.ElemData p E) {t s : MulAut E}
    (ht : IsAutReflection p E t) (hs : IsAutReflection p E s) (hts : t * s ≠ s * t)
    (heq : autMoved E t = autMoved E s) : IsAutTransvection p E (t * s) := by
  have htt := RefFacts.mul_self_eq_one ht
  have hinvt : ∀ y ∈ autMoved E t, t y = y⁻¹ := fun y hy =>
    RefFacts.t_apply_inv_of_mem_autMoved hd ht hy
  have hinvs : ∀ y ∈ autMoved E t, s y = y⁻¹ := fun y hy =>
    RefFacts.t_apply_inv_of_mem_autMoved hd hs (heq ▸ hy)
  have hfix : ∀ y ∈ autMoved E t, (t * s) y = y := by
    intro y hy
    show t (s y) = y
    rw [hinvs y hy, map_inv, hinvt y hy, inv_inv]
  have hmov : ∀ e : E, (t * s) e * e⁻¹ ∈ autMoved E t := by
    intro e
    have hl₁ : s e * e⁻¹ ∈ autMoved E t :=
      heq ▸ (Q1327.mem_autMoved_iff' hd.comm s).2 ⟨e, rfl⟩
    have hl₂ : t e * e⁻¹ ∈ autMoved E t := (Q1327.mem_autMoved_iff' hd.comm t).2 ⟨e, rfl⟩
    have h1 : (t * s) e * e⁻¹ = (s e * e⁻¹)⁻¹ * (t e * e⁻¹) := by
      show t (s e) * e⁻¹ = _
      have h3 : t (s e) = t ((s e * e⁻¹) * e) := by group
      rw [h3, map_mul, hinvt _ hl₁]
      group
    rw [h1]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hl₁) hl₂
  have hne : t * s ≠ 1 := by
    intro h1
    apply hts
    have h3 : s = t⁻¹ := eq_inv_of_mul_eq_one_right h1
    have h4 : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
    rw [h3, h4]
  have hle : autMoved E (t * s) ≤ autMoved E t := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨e, rfl⟩
    exact hmov e
  refine ⟨hne, ?_, fun y hy => hfix y (hle hy)⟩
  have hdvd : Nat.card (autMoved E (t * s)) ∣ p := ht.2 ▸ Subgroup.card_dvd_of_le hle
  rcases (Nat.dvd_prime hd.prime).1 hdvd with h1 | h1
  · exfalso
    have hbot : autMoved E (t * s) = ⊥ := Subgroup.card_eq_one.1 h1
    apply hne
    ext e
    have h2 : (t * s) e * e⁻¹ ∈ autMoved E (t * s) := Subgroup.subset_closure ⟨e, rfl⟩
    rw [hbot, Subgroup.mem_bot, mul_inv_eq_one] at h2
    simpa using h2
  · exact h1

theorem autMoved_ne_of_noncomm [Finite G] (hd : RefFacts.ElemData p E) {t s : MulAut E}
    (ht : IsAutReflection p E t) (hs : IsAutReflection p E s) (hts : t * s ≠ s * t)
    (hnt : ¬ IsAutTransvection p E (t * s)) : autMoved E t ≠ autMoved E s :=
  fun heq => hnt (isAutTransvection_of_same_moved hd ht hs hts heq)

theorem card_sup_autMoved_eq [Finite G] (hd : RefFacts.ElemData p E) {t s : MulAut E}
    (ht : IsAutReflection p E t) (hs : IsAutReflection p E s)
    (hne : autMoved E t ≠ autMoved E s) : Nat.card ↥(autMoved E t ⊔ autMoved E s) = p ^ 2 := by
  have hdisj := Q1327T.inf_eq_bot_of_card_prime hd.prime ht.2 hs.2 hne
  rw [Torsion37.card_sup_of_commute_disjoint (fun k _ l _ => hd.comm k l)
    (disjoint_iff.2 hdisj), ht.2, hs.2, pow_two]

theorem dvd_card_inf_autFixed [Finite G] (hp : p.Prime) {φ : MulAut E} (hφp : φ ^ p = 1)
    {B : Subgroup E} (hBφ : ∀ x ∈ B, φ x ∈ B) (hB : p ∣ Nat.card B) :
    p ∣ Nat.card ↥(B ⊓ autFixed E φ) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fintype ↥B := Fintype.ofFinite _
  let f : Function.End ↥B := fun x => ⟨φ x, hBφ x x.2⟩
  have hf : ∀ (n : ℕ) (x : ↥B), ((f ^ n) x : E) = (φ ^ n) x := by
    intro n
    induction n with
    | zero => intro x; rfl
    | succ n ih =>
      intro x
      rw [pow_succ, pow_succ]
      exact ih (f x)
  have hfp : f ^ p ^ 1 = 1 := by
    rw [pow_one]
    funext x
    apply Subtype.ext
    rw [hf]
    have := congrArg (fun m : MulAut E => m (x : E)) hφp
    exact this
  have hmod := Equiv.Perm.card_fixedPoints_modEq (p := p) (n := 1) hfp
  have hcard : Nat.card ↑(Function.fixedPoints f) = Nat.card ↥(B ⊓ autFixed E φ) := by
    refine Nat.card_congr
      { toFun := fun x => ⟨(x.1 : E), x.1.2, congrArg Subtype.val x.2⟩
        invFun := fun y => ⟨⟨y.1, y.2.1⟩, Subtype.ext y.2.2⟩
        left_inv := fun x => rfl
        right_inv := fun y => rfl }
  rw [← hcard]
  have h0 : Fintype.card ↥B ≡ 0 [MOD p] := (Nat.modEq_zero_iff_dvd).2 (by
    rwa [Nat.card_eq_fintype_card] at hB)
  have h1 := hmod.symm.trans h0
  rw [Nat.card_eq_fintype_card]
  exact (Nat.modEq_zero_iff_dvd).1 h1

theorem isAutTransvection_of_decomp [Finite G] (hd : RefFacts.ElemData p E)
    (hcard : Nat.card E = p ^ 3) {φ : MulAut E} (hφ1 : φ ≠ 1) (hφp : φ ^ p = 1)
    {v : E} (hφv : φ v = v) {P : Subgroup E} (hPcard : Nat.card P = p ^ 2)
    (hPφ : ∀ x ∈ P, φ x ∈ P) (hvP : v ∉ P) (hEeq : Subgroup.zpowers v ⊔ P = ⊤) :
    IsAutTransvection p E φ := by
  have hp := hd.prime
  set C := autFixed E φ with hC
  have hvC : v ∈ C := hφv
  have hv1 : v ≠ 1 := fun h => hvP (h ▸ P.one_mem)
  have hvord : orderOf v = p := Q1327T.orderOf_eq_of_ne_one hd hv1
  have hzv : Nat.card ↥(Subgroup.zpowers v) = p := by rw [Nat.card_zpowers, hvord]
  have hvz : Subgroup.zpowers v ⊓ P = ⊥ := by
    have hd' : Nat.card ↥(Subgroup.zpowers v ⊓ P) ∣ p :=
      hzv ▸ Subgroup.card_dvd_of_le inf_le_left
    rcases (Nat.dvd_prime hp).1 hd' with h1 | h1
    · exact Subgroup.card_eq_one.1 h1
    · exfalso
      apply hvP
      have e : Subgroup.zpowers v ⊓ P = Subgroup.zpowers v :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h1, hzv])
      have : v ∈ Subgroup.zpowers v ⊓ P := by rw [e]; exact Subgroup.mem_zpowers v
      exact this.2
  have hzvC : Subgroup.zpowers v ≤ C := Subgroup.zpowers_le.2 hvC
  have hCeq : C = Subgroup.zpowers v ⊔ (P ⊓ C) := by
    apply le_antisymm
    · intro x hx
      have hx' : x ∈ Subgroup.zpowers v ⊔ P := by rw [hEeq]; trivial
      obtain ⟨a, ha, y, hy, rfl⟩ :=
        Torsion37.exists_mul_of_mem_sup_of_commute (fun k _ l _ => hd.comm k l) hx'
      have hyC : y ∈ C := by
        have := C.mul_mem (C.inv_mem (hzvC ha)) hx
        simpa using this
      exact Subgroup.mul_mem_sup ha ⟨hy, hyC⟩
    · exact sup_le hzvC inf_le_right
  have hcardC : Nat.card C = p * Nat.card ↥(P ⊓ C) := by
    conv_lhs => rw [hCeq]
    rw [Torsion37.card_sup_of_commute_disjoint (fun k _ l _ => hd.comm k l)
      (disjoint_iff.2 (eq_bot_iff.2 (hvz ▸ inf_le_inf_left _ inf_le_left))), hzv]
  have hPC : p ∣ Nat.card ↥(P ⊓ C) :=
    dvd_card_inf_autFixed hp hφp hPφ (by rw [hPcard]; exact dvd_pow_self p two_ne_zero)
  have hp2C : p ^ 2 ∣ Nat.card C := by
    rw [hcardC, pow_two]
    exact Nat.mul_dvd_mul_left p hPC
  have hCdvd : Nat.card C ∣ p ^ 3 := hcard ▸ Subgroup.card_subgroup_dvd_card C
  obtain ⟨k, hk3, hk⟩ := (Nat.dvd_prime_pow hp).1 hCdvd
  have hk2 : 2 ≤ k := (Nat.pow_dvd_pow_iff_le_right hp.one_lt).1 (hk ▸ hp2C)
  have hCne : Nat.card C ≠ p ^ 3 := by
    intro h3
    have htop : C = ⊤ := by
      rw [← Subgroup.card_eq_iff_eq_top, h3, hcard]
    apply hφ1
    ext x
    have hxC : φ x = x := by
      have : x ∈ C := by rw [htop]; trivial
      exact this
    rw [hxC]
    rfl
  have hCp2 : Nat.card C = p ^ 2 := by
    have : k = 2 := by
      by_contra hk2'
      have : k = 3 := by omega
      exact hCne (this ▸ hk)
    rw [hk, this]
  have hMcard : Nat.card (autMoved E φ) = p := by
    have h := Sec13Base.card_eq_mul hd.comm φ
    rw [hcard, ← hC, hCp2] at h
    have h2 : p ^ 2 * p = p ^ 2 * Nat.card (autMoved E φ) := by rw [← pow_succ]; exact h
    exact (Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos 2) h2).symm
  have hMP : autMoved E φ ≤ P := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨x, rfl⟩
    have hx' : x ∈ Subgroup.zpowers v ⊔ P := by rw [hEeq]; trivial
    obtain ⟨a, ha, y, hy, rfl⟩ :=
      Torsion37.exists_mul_of_mem_sup_of_commute (fun k _ l _ => hd.comm k l) hx'
    have haφ : φ a = a := hzvC ha
    have h1 : φ (a * y) * (a * y)⁻¹ = φ y * y⁻¹ := by
      rw [map_mul, haφ, mul_inv_rev]
      calc a * φ y * (y⁻¹ * a⁻¹) = (a * (φ y * y⁻¹)) * a⁻¹ := by group
        _ = ((φ y * y⁻¹) * a) * a⁻¹ := by rw [hd.comm a (φ y * y⁻¹)]
        _ = φ y * y⁻¹ := by group
    show φ (a * y) * (a * y)⁻¹ ∈ P
    rw [h1]
    exact P.mul_mem (hPφ y hy) (P.inv_mem hy)
  have hMφ : ∀ z ∈ autMoved E φ, φ z ∈ autMoved E φ := by
    intro z hz
    rw [← Sec13Base.range_moveHom hd.comm φ] at hz ⊢
    obtain ⟨x, rfl⟩ := hz
    exact ⟨φ x, by simp [Sec13Base.moveHom_apply]⟩
  have hMC : autMoved E φ ≤ C := by
    have hdv := dvd_card_inf_autFixed hp hφp hMφ (hMcard ▸ dvd_refl p)
    have hle : autMoved E φ ⊓ C ≤ autMoved E φ := inf_le_left
    have hcd : Nat.card ↥(autMoved E φ ⊓ C) ∣ p := hMcard ▸ Subgroup.card_dvd_of_le hle
    have hcp : Nat.card ↥(autMoved E φ ⊓ C) = p := Nat.dvd_antisymm hcd hdv
    have : autMoved E φ ⊓ C = autMoved E φ :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hcp, hMcard])
    rw [← this]
    exact inf_le_right
  exact ⟨hφ1, hMcard, hMC⟩

end CFSG.RankThree.PartOne.K133B
