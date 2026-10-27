module

public import CFSG.RankThree.PartTwo.Sec13.KF135Defs
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.RankThree.PartTwo.Sec13.KF135Proof.FamOdd

open CFSG Subgroup
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)

@[expose] def TwoAutFree (p : ℕ) (Q : Type*) [Group Q] : Prop :=
  ∀ α : MulAut Q, α ^ p = 1 → α = 1

@[expose] def NoTwoAut (p : ℕ) (G : Type*) [Group G] : Prop :=
  ∀ Q : Subgroup G, IsPGroup 2 Q → TwoAutFree p Q

theorem TwoAutFree.of_mulEquiv {p : ℕ} {Q R : Type*} [Group Q] [Group R] (e : Q ≃* R)
    (h : TwoAutFree p R) : TwoAutFree p Q := by
  intro α hα
  have h1 : MulAut.congr e α = 1 := h _ (by rw [← map_pow, hα, map_one])
  exact (MulAut.congr e).injective (h1.trans (map_one _).symm)

theorem NoTwoAut.of_injective {p : ℕ} {G H : Type*} [Group G] [Group H] (f : G →* H)
    (hf : Function.Injective f) (h : NoTwoAut p H) : NoTwoAut p G := fun Q hQ =>
  TwoAutFree.of_mulEquiv (Q.equivMapOfInjective f hf) (h _ (hQ.map f))

theorem NoTwoAut.of_mulEquiv {p : ℕ} {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (h : NoTwoAut p H) : NoTwoAut p G :=
  h.of_injective e.toMonoidHom e.injective

variable {S : Type} [Group S] [Finite S] {p : ℕ} {P : Subgroup (MulAut S)} {x u : MulAut S}
  {V : Subgroup (MulAut S)}

theorem mul_conj_mul_inv (σ : MulAut S) (g : S) :
    σ * MulAut.conj g * σ⁻¹ = MulAut.conj (σ g) := by
  apply MulEquiv.ext
  intro y
  change σ (g * σ⁻¹ y * g⁻¹) = σ g * y * (σ g)⁻¹
  rw [map_mul, map_mul, map_inv, MulAut.apply_inv_self]

theorem conj_injective (h : KF135Hyp S p P x u V) :
    Function.Injective (MulAut.conj : S →* MulAut S) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  have hker : (MulAut.conj : S →* MulAut S).ker = Subgroup.center S := by
    ext g
    rw [MonoidHom.mem_ker, Subgroup.mem_center_iff]
    constructor
    · intro hg y
      have hy := congrArg (fun φ : MulAut S => φ y) hg
      simp only [MulAut.conj_apply, MulAut.one_apply] at hy
      calc y * g = g * y * g⁻¹ * g := by rw [hy]
        _ = g * y := by group
    · intro hg
      apply MulEquiv.ext
      intro y
      rw [MulAut.conj_apply, MulAut.one_apply, ← hg y, mul_inv_cancel_right]
  rw [hker]
  haveI := h.simple
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center S) with hc | hc
  · exact hc
  · exfalso
    obtain ⟨a, b, hab⟩ := h.nonab
    have ha : a ∈ Subgroup.center S := by rw [hc]; exact Subgroup.mem_top a
    exact hab (Subgroup.mem_center_iff.1 ha b).symm

theorem V_le_inner_of_comm (h : KF135Hyp S p P x u V)
    (hc : ∀ σ τ : MulAut S, σ * τ * σ⁻¹ * τ⁻¹ ∈ inner S) : V ≤ inner S := by
  calc V = ⁅V, Subgroup.zpowers x⁆ := h.V_comm.symm
    _ ≤ inner S := by
      rw [Subgroup.commutator_le]
      intro a _ b _
      rw [commutatorElement_def]
      exact hc a b

theorem V_le_inner_of_mem (h : KF135Hyp S p P x u V) (hx : x ∈ inner S) : V ≤ inner S := by
  calc V = ⁅V, Subgroup.zpowers x⁆ := h.V_comm.symm
    _ ≤ ⁅V, inner S⁆ := Subgroup.commutator_mono le_rfl ((Subgroup.zpowers_le).2 hx)
    _ ≤ inner S := Subgroup.commutator_le_right _ _

theorem P_le_inner_of_not_dvd (h : KF135Hyp S p P x u V) (hd : ¬ p ∣ Nat.card (Outer S)) :
    P ≤ inner S := by
  intro y hy
  have h1 : (QuotientGroup.mk y : Outer S) ^ p = 1 := by
    rw [← QuotientGroup.mk_pow, h.exponent y hy, QuotientGroup.mk_one]
  rcases (Nat.dvd_prime h.prime).1 (orderOf_dvd_of_pow_eq_one h1) with h2 | h2
  · rwa [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at h2
  · exact absurd (h2 ▸ orderOf_dvd_natCard _) hd

theorem false_of_noTwoAut (h : KF135Hyp S p P x u V) (hV : V ≤ inner S) (hno : NoTwoAut p S) :
    False := by
  have hinj := conj_injective h
  set V₀ : Subgroup S := V.comap (MulAut.conj : S →* MulAut S) with hV₀
  have hV₀2 : IsPGroup 2 V₀ := h.V_two.comap_of_injective _ hinj
  have hxV₀ : ∀ g ∈ V₀, x g ∈ V₀ := by
    intro g hg
    change MulAut.conj (x g) ∈ V
    rw [← mul_conj_mul_inv]
    exact h.V_norm _ hg
  have hmap : V₀.map x.toMonoidHom = V₀ := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨g, hg, rfl⟩
      exact hxV₀ g hg
    · exact (Subgroup.card_map_of_injective (f := x.toMonoidHom) x.injective).ge
  let α : MulAut V₀ := (x.subgroupMap V₀).trans (MulEquiv.subgroupCongr hmap)
  have hα : ∀ (n : ℕ) (g : V₀), ((α ^ n) g : S) = (x ^ n) g := by
    intro n
    induction n with
    | zero => intro g; rfl
    | succ n ih =>
      intro g
      rw [pow_succ, MulAut.mul_apply, ih, pow_succ, MulAut.mul_apply]
      rfl
  have hαp : α ^ p = 1 := by
    apply MulEquiv.ext
    intro g
    apply Subtype.ext
    rw [hα, h.exponent x h.x_mem]
    rfl
  have hα1 := hno V₀ hV₀2 α hαp
  have hfix : ∀ g ∈ V₀, x g = g := fun g hg => by
    have := hα 1 ⟨g, hg⟩
    rw [pow_one, pow_one, hα1] at this
    exact this.symm
  have hcent : Subgroup.zpowers x ≤ Subgroup.centralizer (V : Set (MulAut S)) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro v hv
    obtain ⟨g, rfl⟩ := hV hv
    have hg : g ∈ V₀ := hv
    have hc : x * MulAut.conj g * x⁻¹ = MulAut.conj g := by rw [mul_conj_mul_inv, hfix g hg]
    calc MulAut.conj g * x = x * MulAut.conj g * x⁻¹ * x := by rw [hc]
      _ = x * MulAut.conj g := by group
  have hbot : ⁅V, Subgroup.zpowers x⁆ = ⊥ := by
    rw [Subgroup.commutator_comm]
    exact (Subgroup.commutator_eq_bot_iff_le_centralizer).2 hcent
  exact h.V_ne (h.V_comm.symm.trans hbot)

theorem exists_card_eq_pow (h : KF135Hyp S p P x u V) :
    ∃ k : ℕ, 3 ≤ k ∧ Nat.card P = p ^ k := by
  have : Fact p.Prime := ⟨h.prime⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 h.pgroup
  refine ⟨k, ?_, hk⟩
  have := h.card
  rw [hk] at this
  exact (Nat.pow_le_pow_iff_right h.prime.one_lt).1 this

theorem exists_elemAbelian_of_le_inner (h : KF135Hyp S p P x u V) (hP : P ≤ inner S) :
    ∃ E : Subgroup S, CFSG.Open.IsElemAbelian p E ∧ Nat.card E = p ^ 2 := by
  have : Fact p.Prime := ⟨h.prime⟩
  have hinj := conj_injective h
  obtain ⟨k, hk3, hk⟩ := exists_card_eq_pow h
  obtain ⟨E₀, hE₀⟩ := Sylow.exists_subgroup_card_pow_prime (G := P) p (n := 2)
    (hk ▸ pow_dvd_pow p (by omega))
  have hE₀c : IsMulCommutative E₀ := IsPGroup.isMulCommutative_of_card_eq_prime_sq hE₀
  have hE₀el : CFSG.Open.IsElemAbelian p E₀ :=
    ⟨hE₀c, fun y _ => Subtype.ext (by simpa using h.exponent (y : MulAut S) y.2)⟩
  set E₁ : Subgroup (MulAut S) := E₀.map P.subtype
  have hE₁ : CFSG.Open.IsElemAbelian p E₁ := hE₀el.map P.subtype
  have hE₁c : Nat.card E₁ = p ^ 2 := by
    rw [Subgroup.card_map_of_injective P.subtype_injective, hE₀]
  have hE₁r : E₁ ≤ (MulAut.conj : S →* MulAut S).range :=
    (Subgroup.map_subtype_le E₀).trans hP
  refine ⟨E₁.comap MulAut.conj, hE₁.comap hinj, ?_⟩
  have hc := Subgroup.card_map_of_injective (f := (MulAut.conj : S →* MulAut S))
    (K := E₁.comap MulAut.conj) hinj
  rw [Subgroup.map_comap_eq_self hE₁r] at hc
  rw [← hc, hE₁c]

theorem false_of_rankLE1 (h : KF135Hyp S p P x u V) (hP : P ≤ inner S)
    (hr : ∀ E : Subgroup S, CFSG.Open.IsElemAbelian p E → Nat.card E ≤ p) : False := by
  obtain ⟨E, hE, hc⟩ := exists_elemAbelian_of_le_inner h hP
  have h1 := hr E hE
  rw [hc] at h1
  have h2 : p < p ^ 2 := by
    have := h.prime.two_le
    rw [sq]
    nlinarith
  omega

theorem false_of_h2a_witness (h : KF135Hyp S p P x u V) {E T : Subgroup S}
    (hE : CFSG.Open.IsElemAbelian p E) (hEc : Nat.card E = p ^ 2) (hT : T ≠ ⊥)
    (hT2 : IsPGroup 2 T) (hET : E ≤ Subgroup.normalizer (T : Set S)) : False := by
  have hinj := conj_injective h
  obtain ⟨φ, hφ, hne⟩ := h.h2a (E.map MulAut.conj) (Subgroup.map_le_range _ _)
    (hE.map _) (by rw [Subgroup.card_map_of_injective hinj, hEc]) T hT hT2
  obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.1 hφ
  have hn := hET he
  apply hne
  ext y
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact (Subgroup.mem_normalizer_iff.1 hn t).1 ht
  · intro hy
    refine ⟨e⁻¹ * y * e, ?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.1 hn _).2 (by convert hy using 1; group)
    · change e * (e⁻¹ * y * e) * e⁻¹ = y
      group

theorem false_of_not_dvd_card (h : KF135Hyp S p P x u V)
    (hd : ¬ p ^ 3 ∣ Nat.card (Outer S) * Nat.card S) : False := by
  obtain ⟨k, hk3, hk⟩ := exists_card_eq_pow h
  apply hd
  calc p ^ 3 ∣ p ^ k := pow_dvd_pow p hk3
    _ = Nat.card P := hk.symm
    _ ∣ Nat.card (MulAut S) := Subgroup.card_subgroup_dvd_card P
    _ = Nat.card (Outer S) * Nat.card (inner S) :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup (inner S)
    _ ∣ Nat.card (Outer S) * Nat.card S :=
      mul_dvd_mul_left _ (Subgroup.card_range_dvd (MulAut.conj : S →* MulAut S))

theorem pow_three_dvd_of_dvd_mul {q a b m : ℕ} (hq : q.Prime) (hq5 : 5 ≤ q)
    (h : q ^ 3 ∣ 2 ^ a * 3 ^ b * m) : q ^ 3 ∣ m := by
  have h2 : Nat.Coprime (q ^ 3) (2 ^ a) :=
    Nat.Coprime.pow _ _ ((Nat.coprime_primes hq Nat.prime_two).2 (by omega))
  have h3 : Nat.Coprime (q ^ 3) (3 ^ b) :=
    Nat.Coprime.pow _ _ ((Nat.coprime_primes hq Nat.prime_three).2 (by omega))
  rw [mul_assoc] at h
  exact h3.dvd_of_dvd_mul_left (h2.dvd_of_dvd_mul_left h)

theorem false_of_card_dvd (h : KF135Hyp S p P x u V) {a b m : ℕ} (hm0 : 0 < m) (hm : m < 343)
    (hd : Nat.card (Outer S) * Nat.card S ∣ 2 ^ a * 3 ^ b * m) : False := by
  refine false_of_not_dvd_card h fun h3 => ?_
  have h1 := pow_three_dvd_of_dvd_mul h.prime (by linarith [h.seven_le]) (h3.trans hd)
  have h2 := Nat.le_of_dvd hm0 h1
  have h4 : 7 ^ 3 ≤ p ^ 3 := Nat.pow_le_pow_left h.seven_le 3
  omega

end CFSG.RankThree.PartTwo.Sec13.KF135Proof.FamOdd
