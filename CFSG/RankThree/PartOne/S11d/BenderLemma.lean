module

public import CFSG.RankThree.PartOne.S11d.BaerClass2
public import CFSG.LocalAnalysis.SectionRank.Ccomm.OddCritical

public section

namespace CFSG.RankThree.PartOne.S11d

open Subgroup
open scoped commutatorElement

section Fixed

theorem exists_nonzero_fixed {G M : Type*} [Group G] [AddCommGroup M] [Finite M] {p : ℕ}
    [Fact p.Prime] [DistribMulAction G M] (hG : IsPGroup p G) (hM : ∀ x : M, p • x = 0)
    {V : AddSubgroup M} (hV : ∀ g : G, ∀ v ∈ V, g • v ∈ V) (hne : V ≠ ⊥) :
    ∃ v ∈ V, v ≠ 0 ∧ ∀ g : G, g • v = v := by
  classical
  let W : SubMulAction G M := { carrier := (V : Set M), smul_mem' := fun g v hv => hV g v hv }
  have hmod : Nat.card ↥W ≡ Nat.card (MulAction.fixedPoints G ↥W) [MOD p] :=
    hG.card_modEq_card_fixedPoints ↥W
  obtain ⟨v₀, hv₀V, hv₀⟩ : ∃ v ∈ V, v ≠ 0 := by
    by_contra h
    push Not at h
    exact hne ((AddSubgroup.eq_bot_iff_forall V).mpr h)
  have hdvd : p ∣ Nat.card ↥W := by
    have hord : addOrderOf (⟨v₀, hv₀V⟩ : V) = p :=
      addOrderOf_eq_prime (Subtype.ext (hM v₀)) (fun h => hv₀ (congrArg Subtype.val h))
    have h1 := addOrderOf_dvd_natCard (⟨v₀, hv₀V⟩ : V)
    rw [hord] at h1
    have h2 : Nat.card ↥W = Nat.card ↥V := Nat.card_congr (Equiv.refl _)
    rwa [h2]
  have hfp : p ∣ Nat.card (MulAction.fixedPoints G ↥W) :=
    (Nat.modEq_zero_iff_dvd).mp (hmod.symm.trans ((Nat.modEq_zero_iff_dvd).mpr hdvd))
  have hz0 : (⟨(0 : M), V.zero_mem⟩ : ↥W) ∈ MulAction.fixedPoints G ↥W := fun g =>
    Subtype.ext (smul_zero g)
  have : Nonempty (MulAction.fixedPoints G ↥W) := ⟨⟨_, hz0⟩⟩
  have hpos : 0 < Nat.card (MulAction.fixedPoints G ↥W) := Nat.card_pos
  have hge : p ≤ Nat.card (MulAction.fixedPoints G ↥W) := Nat.le_of_dvd hpos hfp
  have hone : 1 < Nat.card (MulAction.fixedPoints G ↥W) :=
    lt_of_lt_of_le (Fact.out : p.Prime).one_lt hge
  have hnt : Nontrivial (MulAction.fixedPoints G ↥W) := Finite.one_lt_card_iff_nontrivial.mp hone
  obtain ⟨b, hb⟩ := exists_ne (⟨_, hz0⟩ : MulAction.fixedPoints G ↥W)
  refine ⟨(b.1 : M), b.1.2, fun h0 => hb ?_, fun g => congrArg Subtype.val (b.2 g)⟩
  exact Subtype.ext (Subtype.ext h0)

end Fixed

section ClassTwo

variable {X : Type*} [Group X] [Finite X]

theorem exists_fixed_moved {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {D A S : Subgroup X}
    (hDexp : ∀ x ∈ D, x ^ p = 1)
    (hDcl : ∀ x ∈ D, ∀ y ∈ D, ∀ z ∈ D, ⁅x, y⁆ * z = z * ⁅x, y⁆)
    (hA : IsPGroup p A) (hS : ¬ p ∣ Nat.card S)
    (hAD : A ≤ normalizer (D : Set X)) (hSD : S ≤ normalizer (D : Set X))
    (hAS : A ≤ normalizer (S : Set X))
    (hmove : ∃ s ∈ S, ∃ d ∈ D, s * d * s⁻¹ ≠ d) :
    ∃ d ∈ D, (∀ a ∈ A, a * d * a⁻¹ = d) ∧ ∃ s ∈ S, s * d * s⁻¹ ≠ d := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hQ : ClassTwoExp p ↥D :=
    { central := fun x y z => Subtype.ext (by
        simpa [commutatorElement_def] using hDcl x x.2 y y.2 z z.2)
      prime := hp
      ne_two := hp2
      pow_eq_one := fun x => Subtype.ext (hDexp x x.2) }
  have : Finite (Baer p ↥D) := inferInstanceAs (Finite ↥D)
  let actD : normalizer (D : Set X) → (Baer p ↥D →+ Baer p ↥D) := fun g =>
    Baer.addMap (p := p) (D.normalizerMonoidHom g).toMonoidHom
  have hact : ∀ (g : normalizer (D : Set X)) (x : Baer p ↥D),
      ((Baer.val (actD g x) : ↥D) : X) = (g : X) * ((Baer.val x : ↥D) : X) * (g : X)⁻¹ := by
    intro g x
    simp [actD, Baer.val_addMap]
  let instA : DistribMulAction ↥A (Baer p ↥D) :=
    { smul := fun a x => actD ⟨a, hAD a.2⟩ x
      one_smul := fun x => Baer.ext (Subtype.ext (by
        change ((Baer.val (actD ⟨((1 : ↥A) : X), hAD (1 : ↥A).2⟩ x) : ↥D) : X) = _
        rw [hact]
        simp))
      mul_smul := fun a b x => Baer.ext (Subtype.ext (by
        change ((Baer.val (actD ⟨((a * b : ↥A) : X), hAD (a * b : ↥A).2⟩ x) : ↥D) : X) =
          ((Baer.val (actD ⟨(a : X), hAD a.2⟩ (actD ⟨(b : X), hAD b.2⟩ x)) : ↥D) : X)
        rw [hact, hact, hact]
        simp [mul_assoc]))
      smul_zero := fun a => map_zero _
      smul_add := fun a x y => map_add _ x y }
  have hsmulA : ∀ (a : ↥A) (x : Baer p ↥D),
      ((Baer.val (a • x) : ↥D) : X) = (a : X) * ((Baer.val x : ↥D) : X) * (a : X)⁻¹ :=
    fun a x => hact ⟨a, hAD a.2⟩ x
  let actS : ↥S → (Baer p ↥D →+ Baer p ↥D) := fun s => actD ⟨s, hSD s.2⟩
  have hactS : ∀ (s : ↥S) (x : Baer p ↥D),
      ((Baer.val (actS s x) : ↥D) : X) = (s : X) * ((Baer.val x : ↥D) : X) * (s : X)⁻¹ :=
    fun s x => hact ⟨s, hSD s.2⟩ x
  have hactS_mul : ∀ (s t : ↥S) (x : Baer p ↥D), actS (s * t) x = actS s (actS t x) := by
    intro s t x
    refine Baer.ext (Subtype.ext ?_)
    rw [hactS, hactS, hactS]
    simp [mul_assoc]
  let V : AddSubgroup (Baer p ↥D) :=
    AddSubgroup.closure {v | ∃ (s : ↥S) (x : Baer p ↥D), v = actS s x - x}
  have hVinv : ∀ (a : ↥A), ∀ v ∈ V, a • v ∈ V := by
    intro a v hv
    induction hv using AddSubgroup.closure_induction with
    | mem v hv =>
      obtain ⟨s, x, rfl⟩ := hv
      have hsa : (a : X) * (s : X) * (a : X)⁻¹ ∈ S := (mem_normalizer_iff.mp (hAS a.2) s).mp s.2
      have e : a • actS s x = actS ⟨_, hsa⟩ (a • x) := by
        refine Baer.ext (Subtype.ext ?_)
        rw [hsmulA, hactS, hactS, hsmulA]
        simp [mul_assoc]
      rw [smul_sub, e]
      exact AddSubgroup.subset_closure ⟨_, a • x, rfl⟩
    | zero => simp
    | add u w _ _ hu hw => rw [smul_add]; exact V.add_mem hu hw
    | neg u _ hu => rw [smul_neg]; exact V.neg_mem hu
  have hVne : V ≠ ⊥ := by
    obtain ⟨s, hs, d, hd, hsd⟩ := hmove
    intro hbot
    have hmem : actS ⟨s, hs⟩ (Baer.mk ⟨d, hd⟩) - Baer.mk ⟨d, hd⟩ ∈ V :=
      AddSubgroup.subset_closure ⟨⟨s, hs⟩, _, rfl⟩
    rw [hbot, AddSubgroup.mem_bot, sub_eq_zero] at hmem
    apply hsd
    have := congrArg (fun y => ((Baer.val y : ↥D) : X)) hmem
    simpa [hactS] using this
  have : Fintype ↥S := Fintype.ofFinite _
  let N : Baer p ↥D →+ Baer p ↥D := ∑ s : ↥S, actS s
  have hN : ∀ x, N x = ∑ s : ↥S, actS s x := fun x => AddMonoidHom.finsetSum_apply _ _ _
  have hNV : ∀ v ∈ V, N v = 0 := by
    intro v hv
    induction hv using AddSubgroup.closure_induction with
    | mem v hv =>
      obtain ⟨t, x, rfl⟩ := hv
      rw [map_sub, hN, hN]
      have : ∑ s : ↥S, actS s (actS t x) = ∑ s : ↥S, actS s x := by
        rw [← Fintype.sum_equiv (Equiv.mulRight t) (fun s => actS (s * t) x) (fun s => actS s x)
          (fun s => rfl)]
        exact Finset.sum_congr rfl fun s _ => (hactS_mul s t x).symm
      rw [this, sub_self]
    | zero => exact map_zero N
    | add u w _ _ hu hw => rw [map_add, hu, hw, add_zero]
    | neg u _ hu => rw [map_neg, hu, neg_zero]
  have hdisj : ∀ v ∈ V, (∀ s : ↥S, actS s v = v) → v = 0 := by
    intro v hv hfix
    have h1 : N v = Nat.card ↥S • v := by
      rw [hN]
      simp only [hfix, Finset.sum_const, Finset.card_univ, Nat.card_eq_fintype_card]
    have h2 : Nat.card ↥S • v = 0 := by rw [← h1]; exact hNV v hv
    have hcop : Nat.Coprime p (Nat.card ↥S) := (Nat.Prime.coprime_iff_not_dvd hp).mpr hS
    have h3 : addOrderOf v ∣ p := addOrderOf_dvd_of_nsmul_eq_zero (Baer.nsmul_prime_eq_zero v)
    have h4 : addOrderOf v ∣ Nat.card ↥S := addOrderOf_dvd_of_nsmul_eq_zero h2
    have h5 : addOrderOf v ∣ Nat.gcd p (Nat.card ↥S) := Nat.dvd_gcd h3 h4
    rw [hcop.gcd_eq_one] at h5
    exact AddMonoid.addOrderOf_eq_one_iff.mp (Nat.dvd_one.mp h5)
  obtain ⟨v, hvV, hv0, hvfix⟩ := exists_nonzero_fixed (G := ↥A) (M := Baer p ↥D) (V := V) hA
    (fun x => Baer.nsmul_prime_eq_zero x) hVinv hVne
  refine ⟨((Baer.val v : ↥D) : X), (Baer.val v).2, fun a ha => ?_, ?_⟩
  · have := congrArg (fun y => ((Baer.val y : ↥D) : X)) (hvfix ⟨a, ha⟩)
    rw [hsmulA] at this
    exact this
  · by_contra hno
    push Not at hno
    apply hv0
    apply hdisj v hvV
    intro s
    refine Baer.ext (Subtype.ext ?_)
    rw [hactS]
    exact hno s s.2

end ClassTwo

section Abstract

variable {X : Type*} [Group X] [Finite X]

omit [Finite X] in
theorem eq_one_of_mem_two_p {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {S Y : Subgroup X}
    (hS : IsPGroup 2 S) (hY : IsPGroup p Y) {g : X} (hgS : g ∈ S) (hgY : g ∈ Y) : g = 1 := by
  obtain ⟨k, hk⟩ := hS ⟨g, hgS⟩
  obtain ⟨m, hm⟩ := hY ⟨g, hgY⟩
  have h1 : g ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
  have h2 : g ^ (p ^ m) = 1 := by simpa using congrArg Subtype.val hm
  have h3 : orderOf g ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h1
  have h4 : orderOf g ∣ p ^ m := orderOf_dvd_of_pow_eq_one h2
  have hcop : Nat.Coprime (2 ^ k) (p ^ m) :=
    Nat.Coprime.pow _ _ ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2))
  have h5 : orderOf g ∣ Nat.gcd (2 ^ k) (p ^ m) := Nat.dvd_gcd h3 h4
  rw [hcop.gcd_eq_one] at h5
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h5)

theorem bender_abstract {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {A S : Subgroup X}
    (hA : IsPGroup p A) (hS : IsPGroup 2 S) (hAS : A ≤ normalizer (S : Set X))
    (hF3 : ∀ d : X, d ^ p = 1 → (∀ a ∈ A, a * d = d * a) → d ∈ A) :
    ⁅S, CFSG.pCore p X⁆ = ⊥ := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  set Y := CFSG.pCore p X with hYdef
  have hYn : Y.Normal := CFSG.pCore_normal
  have hYp : IsPGroup p Y := CFSG.pCore_isPGroup
  by_cases hY : Y = ⊥
  · rw [hY, Subgroup.commutator_bot_right]
  have : Nontrivial ↥Y := (Subgroup.nontrivial_iff_ne_bot Y).mpr hY
  obtain ⟨D, hDchar, -, hDcl, hDexp, hDfix⟩ :=
    CFSG.SectionRank.Ccomm.odd_critical_exponent_subgroup (P := ↥Y) hp2 hYp
  set D' : Subgroup X := D.map Y.subtype with hD'
  have hD'norm : ∀ g : X, ∀ x : X, x ∈ D' → g * x * g⁻¹ ∈ D' := by
    intro g x hx
    obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.mp hx
    have hfix := hDchar.fixed (MulAut.conjNormal (H := Y) g)
    have hd' : (MulAut.conjNormal (H := Y) g) d ∈ D := by
      have : d ∈ D.comap (MulAut.conjNormal (H := Y) g).toMonoidHom := by rw [hfix]; exact hd
      exact this
    exact Subgroup.mem_map.mpr ⟨_, hd', by simp [MulAut.conjNormal_apply]⟩
  have hD'N : ∀ H : Subgroup X, H ≤ normalizer (D' : Set X) := by
    intro H g _
    rw [mem_normalizer_iff]
    intro x
    refine ⟨hD'norm g x, fun hx => ?_⟩
    have := hD'norm g⁻¹ _ hx
    simpa [mul_assoc] using this
  have hD'exp : ∀ x ∈ D', x ^ p = 1 := by
    intro x hx
    obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.mp hx
    have := congrArg Subtype.val (show d ^ p = 1 from hDexp d hd)
    simpa using this
  have hD'cl : ∀ x ∈ D', ∀ y ∈ D', ∀ z ∈ D', ⁅x, y⁆ * z = z * ⁅x, y⁆ := by
    intro x₀ hx₀ y₀ hy₀ z₀ hz₀
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hx₀
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hy₀
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hz₀
    have h1 : ⁅x, y⁆ ∈ ⁅D, (⊤ : Subgroup ↥Y)⁆ := Subgroup.commutator_mem_commutator hx trivial
    have h2 := (hDcl h1).2
    have h3 : z * ⁅x, y⁆ = ⁅x, y⁆ * z := Subgroup.mem_centralizer_iff.mp h2 z hz
    have := congrArg Subtype.val h3.symm
    simpa [commutatorElement_def] using this
  have hSD' : ∀ s ∈ S, ∀ d ∈ D', s * d * s⁻¹ = d := by
    by_contra hno
    push Not at hno
    have hSp : ¬ p ∣ Nat.card S := by
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hS
      rw [hk]
      intro h
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h))
    obtain ⟨d, hdD, hdfix, s, hs, hmove⟩ := exists_fixed_moved hp hp2 hD'exp hD'cl hA hSp
      (hD'N A) (hD'N S) hAS hno
    have hdY : d ∈ Y := by
      obtain ⟨y, -, rfl⟩ := Subgroup.mem_map.mp hdD
      exact y.2
    have hdA : d ∈ A := hF3 d (hD'exp d hdD) (fun a ha => by
      have := hdfix a ha
      calc a * d = a * d * a⁻¹ * a := by group
        _ = d * a := by rw [this])
    apply hmove
    have h1 : s * d * s⁻¹ * d⁻¹ ∈ Y := Y.mul_mem (hYn.conj_mem d hdY s) (Y.inv_mem hdY)
    have h2 : s * d * s⁻¹ * d⁻¹ ∈ S := by
      have : s * d * s⁻¹ * d⁻¹ = s * (d * s⁻¹ * d⁻¹) := by group
      rw [this]
      exact S.mul_mem hs ((mem_normalizer_iff.mp (hAS hdA) s⁻¹).mp (S.inv_mem hs))
    have h3 := eq_one_of_mem_two_p hp hp2 hS hYp h2 h1
    calc s * d * s⁻¹ = (s * d * s⁻¹ * d⁻¹) * d := by group
      _ = d := by rw [h3, one_mul]
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro s hs
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hσ : MulAut.conjNormal (H := Y) s ∈ fixingSubgroup (MulAut ↥Y) (D : Set ↥Y) := by
    rw [mem_fixingSubgroup_iff]
    intro d hd
    apply Subtype.ext
    change ((MulAut.conjNormal (H := Y) s d : ↥Y) : X) = d
    rw [MulAut.conjNormal_apply]
    exact hSD' s hs d (Subgroup.mem_map.mpr ⟨d, hd, rfl⟩)
  have hord2 : orderOf (MulAut.conjNormal (H := Y) s) ∣ orderOf s := orderOf_map_dvd _ s
  obtain ⟨k, hk⟩ := hS ⟨s, hs⟩
  have hs2 : orderOf s ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hk)
  obtain ⟨m, hm⟩ := hDfix ⟨_, hσ⟩
  have hσp : orderOf (MulAut.conjNormal (H := Y) s) ∣ p ^ m := by
    have : (⟨_, hσ⟩ : ↥(fixingSubgroup (MulAut ↥Y) (D : Set ↥Y))) ^ (p ^ m) = 1 := hm
    have h1 : (MulAut.conjNormal (H := Y) s) ^ (p ^ m) = 1 := by
      simpa using congrArg Subtype.val this
    exact orderOf_dvd_of_pow_eq_one h1
  have hcop : Nat.Coprime (2 ^ k) (p ^ m) :=
    Nat.Coprime.pow _ _ ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2))
  have h5 : orderOf (MulAut.conjNormal (H := Y) s) ∣ Nat.gcd (2 ^ k) (p ^ m) :=
    Nat.dvd_gcd (hord2.trans hs2) hσp
  rw [hcop.gcd_eq_one] at h5
  have h6 : MulAut.conjNormal (H := Y) s = 1 := orderOf_eq_one_iff.mp (Nat.dvd_one.mp h5)
  have h7 := congrArg (fun φ : MulAut ↥Y => ((φ ⟨y, hy⟩ : ↥Y) : X)) h6
  simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h7
  have h7' : s * y * s⁻¹ = y := h7
  calc y * s = (s * y * s⁻¹) * s := by rw [h7']
    _ = s * y := by group

end Abstract

end CFSG.RankThree.PartOne.S11d
