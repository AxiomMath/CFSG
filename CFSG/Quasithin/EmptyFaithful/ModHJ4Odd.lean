module

public import CFSG.Quasithin.EmptyFaithful.ModHJ4F
public import CFSG.Quasithin.EmptyFaithful.S146yBorelBase
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatExport
public import CFSG.Sporadic.J4
public import CFSG.Sporadic.J4.QTRankProof

public section

namespace CFSG.Quasithin.ModH.J4

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Blueprint
open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT

theorem mem_normalizer_map_equiv {Y Y' : Type} [Group Y] [Group Y'] (e : Y ≃* Y') (H : Subgroup Y)
    {x : Y} (hx : x ∈ Subgroup.normalizer (H : Set Y)) :
    e x ∈ Subgroup.normalizer ((H.map e.toMonoidHom : Subgroup Y') : Set Y') := by
  rw [Subgroup.mem_normalizer_iff] at hx ⊢
  intro y'
  obtain ⟨y, rfl⟩ := e.surjective y'
  have h1 : ∀ z : Y, e z ∈ H.map e.toMonoidHom ↔ z ∈ H := fun z => by
    constructor
    · rintro ⟨w, hw, hwz⟩
      exact (e.injective hwz) ▸ hw
    · intro hz
      exact ⟨z, hz, rfl⟩
  have h2 : e x * e y * (e x)⁻¹ = e (x * y * x⁻¹) := by simp
  rw [h2, h1, h1]
  exact hx y

theorem eq_bot_of_normalized_by_sylow_abstract {Γ : Type} [Group Γ] [Finite Γ] {E P₀ : Subgroup Γ}
    (hP0 : IsSylowTwoOf P₀ ⊤) (hEP0 : E ≤ P₀)
    (hE : ∀ {p : ℕ}, p.Prime → p ≠ 2 → ∀ P : Subgroup Γ, IsPGroup p ↥P →
      E ≤ Subgroup.normalizer (P : Set Γ) → P = ⊥)
    {Q : Type} [Group Q] [Finite Q] (φ : Q ≃* Γ) {S : Subgroup Q} (hS : IsSylowTwoOf S ⊤)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {P : Subgroup Q} (hP : IsPGroup p ↥P)
    (hSP : S ≤ Subgroup.normalizer (P : Set Q)) : P = ⊥ := by
  have hSΓ : IsSylowTwoOf (S.map φ.toMonoidHom) ⊤ :=
    CFSG.QuasithinUnique.Ch1.SporLat.isSylowTwoOf_map φ hS
  obtain ⟨g, hg⟩ := exists_conj_of_isSylowTwoOf_top hSΓ hP0
  let Φ : Q ≃* Γ := φ.trans (MulAut.conj g)
  have hSΦ : S.map Φ.toMonoidHom = P₀ := by
    rw [← hg, Subgroup.map_map]
    rfl
  have hnorm : P₀ ≤ Subgroup.normalizer ((P.map Φ.toMonoidHom : Subgroup Γ) : Set Γ) := by
    intro x hx
    rw [← hSΦ] at hx
    obtain ⟨σ, hσ, rfl⟩ := hx
    exact mem_normalizer_map_equiv Φ P (hSP hσ)
  have h := hE hp hp2 _ (hP.map Φ.toMonoidHom) (hEP0.trans hnorm)
  exact (Subgroup.map_eq_bot_iff_of_injective P Φ.injective).1 h

theorem eq_bot_of_normalized_by_sylow
    {Q : Type} [Group Q] [Finite Q] (e : Nonempty (Q ≃* NativeSporadic.Carrier .J4))
    {S : Subgroup Q} (hS : IsSylowTwoOf S ⊤) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {P : Subgroup Q} (hP : IsPGroup p ↥P) (hSP : S ≤ Subgroup.normalizer (P : Set Q)) : P = ⊥ := by
  obtain ⟨e⟩ := e
  have hF : J4Facts := CFSG.Sporadic.J4.j4Facts
  have hM : MatFacts := hF.mat
  have hP0 : IsSylowTwoOf P0 ⊤ := by
    let P0s : Sylow 2 J := Sylow.ofCard P0 (by rw [card_P0 hM hF, card_J_factorization hF])
    have h := K1.isSylowTwoOf_top_iff.2 ⟨P0s.isPGroup', P0s.not_dvd_index⟩
    rwa [Sylow.coe_ofCard] at h
  exact eq_bot_of_normalized_by_sylow_abstract hP0 Eg_le_P0
    (fun hp hp2 P' hP' hEP => eq_bot_of_normalized_by_E hF hp hp2 hP' hEP)
    (e.trans (CFSG.Sporadic.J4.seedEquiv hM)) hS hp hp2 hP hSP

theorem exists_normal_exponent_prime {G : Type} [Group G] [Finite G] [Nontrivial G]
    (hs : Group.IsSolvable G) :
    ∃ p : ℕ, p.Prime ∧ ∃ A : Subgroup G, A.Normal ∧ A ≠ ⊥ ∧ ∀ x ∈ A, x ^ p = 1 := by
  classical
  have hex : ∃ n, derivedSeries G n = ⊥ := hs.solvable
  have h0 : derivedSeries G (Nat.find hex) = ⊥ := Nat.find_spec hex
  have hn0 : Nat.find hex ≠ 0 := by
    intro h
    rw [h, derivedSeries_zero] at h0
    exact top_ne_bot h0
  obtain ⟨m, hm⟩ : ∃ m, Nat.find hex = m + 1 := ⟨Nat.find hex - 1, by omega⟩
  have hD : derivedSeries G m ≠ ⊥ := Nat.find_min hex (by omega)
  have hDcomm : ⁅derivedSeries G m, derivedSeries G m⁆ = ⊥ := by
    rw [← derivedSeries_succ, ← hm]
    exact h0
  have hcomm : ∀ x ∈ derivedSeries G m, ∀ y ∈ derivedSeries G m, x * y = y * x := by
    intro x hx y hy
    have := Subgroup.commutator_mem_commutator hx hy
    rw [hDcomm, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
    exact this
  have hDcard : Nat.card ↥(derivedSeries G m) ≠ 1 := by
    rwa [Ne, Subgroup.card_eq_one]
  have hp : (Nat.card ↥(derivedSeries G m)).minFac.Prime := Nat.minFac_prime hDcard
  have hpd : (Nat.card ↥(derivedSeries G m)).minFac ∣ Nat.card ↥(derivedSeries G m) :=
    Nat.minFac_dvd _
  have : Fact (Nat.card ↥(derivedSeries G m)).minFac.Prime := ⟨hp⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (Nat.card ↥(derivedSeries G m)).minFac hpd
  set p := (Nat.card ↥(derivedSeries G m)).minFac with hpdef
  let A : Subgroup G :=
    { carrier := {y | y ∈ derivedSeries G m ∧ y ^ p = 1}
      mul_mem' := fun {a b} ha hb =>
        ⟨(derivedSeries G m).mul_mem ha.1 hb.1, by
          rw [(show Commute a b from hcomm a ha.1 b hb.1).mul_pow, ha.2, hb.2, one_mul]⟩
      one_mem' := ⟨(derivedSeries G m).one_mem, one_pow _⟩
      inv_mem' := fun {a} ha => ⟨(derivedSeries G m).inv_mem ha.1, by rw [inv_pow, ha.2, inv_one]⟩ }
  refine ⟨p, hp, A, ?_, ?_, fun y hy => hy.2⟩
  · refine ⟨fun y hy g => ⟨?_, ?_⟩⟩
    · exact (derivedSeries_normal G m).conj_mem y hy.1 g
    · rw [conj_pow, hy.2]
      simp
  · intro hbot
    have hxA : (x : G) ∈ A := by
      refine ⟨x.2, ?_⟩
      have := pow_orderOf_eq_one x
      rw [hx] at this
      simpa using congrArg Subtype.val this
    rw [hbot, Subgroup.mem_bot] at hxA
    have hx1 : x = 1 := Subtype.ext hxA
    rw [hx1, orderOf_one] at hx
    exact hp.one_lt.ne hx

theorem solvableOverSylow_j4 :
    ∀ (Q : Type) [Group Q] [Finite Q], Nonempty (Q ≃* NativeSporadic.Carrier .J4) →
      ∀ S : Subgroup Q, IsSylowTwoOf S ⊤ → ∀ Z : Subgroup Q, Group.IsSolvable ↥Z → S ≤ Z →
        ∃ N : Subgroup Q, IsPGroup 2 ↥N ∧ N ≠ ⊥ ∧ Z ≤ Subgroup.normalizer (N : Set Q) := by
  classical
  intro Q _ _ e S hS Z hZs hSZ
  have hS1 : S ≠ ⊥ := by
    intro hbot
    obtain ⟨-, hidx⟩ := K1.isSylowTwoOf_top_iff.1 hS
    have hQ : Nat.card Q = 86775571046077562880 := by
      obtain ⟨e⟩ := e
      rw [Nat.card_congr e.toEquiv]
      exact CFSG.Sporadic.J4.card_J4
    subst hbot
    have h1 := Subgroup.card_mul_index (⊥ : Subgroup Q)
    rw [Subgroup.card_bot, one_mul, hQ] at h1
    apply hidx
    rw [h1]
    norm_num
  have hZ1 : Z ≠ ⊥ := fun h => hS1 (le_bot_iff.1 (h ▸ hSZ))
  have : Nontrivial ↥Z := (Subgroup.nontrivial_iff_ne_bot Z).2 hZ1
  obtain ⟨p, hp, AZ, hAZn, hAZ1, hAZp⟩ := exists_normal_exponent_prime hZs
  let A : Subgroup Q := AZ.map Z.subtype
  have hA1 : A ≠ ⊥ := fun h =>
    hAZ1 ((Subgroup.map_eq_bot_iff_of_injective AZ Z.subtype_injective).1 h)
  have hApg : IsPGroup p ↥A := by
    intro a
    obtain ⟨b, hb, hba⟩ := a.2
    refine ⟨1, Subtype.ext ?_⟩
    have h1 : (b : Q) ^ p = 1 := by simpa using congrArg Subtype.val (hAZp b hb)
    simpa [← hba] using h1
  have hconj : ∀ z ∈ Z, ∀ x ∈ A, z * x * z⁻¹ ∈ A := by
    intro z hz x hx
    obtain ⟨b, hb, rfl⟩ := hx
    exact ⟨⟨z, hz⟩ * b * ⟨z, hz⟩⁻¹, hAZn.conj_mem b hb ⟨z, hz⟩, rfl⟩
  have hZA : Z ≤ Subgroup.normalizer (A : Set Q) := by
    intro z hz
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨hconj z hz x, fun hx => ?_⟩
    have := hconj z⁻¹ (Z.inv_mem hz) _ hx
    simpa [mul_assoc] using this
  by_cases hp2 : p = 2
  · subst hp2
    exact ⟨A, hApg, hA1, hZA⟩
  · exact absurd (eq_bot_of_normalized_by_sylow e hS hp hp2 hApg (hSZ.trans hZA)) hA1

end CFSG.Quasithin.ModH.J4
