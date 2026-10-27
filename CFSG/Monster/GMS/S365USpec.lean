module

public import CFSG.Monster.GMS.S365UCheck
public import CFSG.Monster.GMS.S365UScan
public import CFSG.Monster.GMS.S365Facts
public import CFSG.Sporadic.Co1.Module.OddCent

public section

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic

namespace S365

section Parity

theorem odd_card_fixed {α : Type*} [DecidableEq α] (X : Finset α) (σ : α → α)
    (hX : ∀ x ∈ X, σ x ∈ X) (hσ : ∀ x, σ (σ x) = x) (h : Odd X.card) :
    Odd (X.filter fun x => σ x = x).card := by
  have hsplit := Finset.card_filter_add_card_filter_not (s := X) (fun x => σ x = x)
  have hN : (∑ x ∈ X.filter (fun x => ¬ σ x = x), (1 : ZMod 2)) = 0 := by
    refine Finset.sum_involution (fun a _ => σ a) (fun a _ => by decide)
      (fun a ha _ => by simpa using (Finset.mem_filter.1 ha).2) (fun a ha => ?_)
      (fun a _ => hσ a)
    obtain ⟨haX, hane⟩ := Finset.mem_filter.1 ha
    refine Finset.mem_filter.2 ⟨hX a haX, ?_⟩
    rw [hσ a]
    exact fun h' => hane h'.symm
  rw [Finset.sum_const, nsmul_eq_mul, mul_one] at hN
  have h2 : 2 ∣ (X.filter fun x => ¬ σ x = x).card := (ZMod.natCast_eq_zero_iff _ 2).1 hN
  rw [Nat.odd_iff] at h ⊢
  omega

end Parity

theorem exists_fixed_type4
    {r s : Co1} (hr : r * r = 1) (hs : s * s = 1) (hrs : r * s = s * r) :
    ∃ ω ∈ co1Orbit 2, co1Act r ω = ω ∧ co1Act s ω = ω := by
  classical
  have hfin : (co1Orbit 2).Finite := Set.toFinite _
  set X : Finset (Fin 24 → ZMod 2) := hfin.toFinset with hXdef
  have hXmem : ∀ x, x ∈ X ↔ x ∈ co1Orbit 2 := fun x => hfin.mem_toFinset
  have hXcard : Odd X.card := by
    have := Leech.ncard_co1Orbit_two
    rw [Set.ncard_eq_toFinset_card _ hfin] at this
    rw [hXdef, this]
    decide
  have hinv : ∀ (g : Co1), g * g = 1 → ∀ x, co1Act g (co1Act g x) = x := fun g hg x => by
    calc co1Act g (co1Act g x) = (co1Act g * co1Act g) x := (Module.End.mul_apply _ _ _).symm
      _ = co1Act (g * g) x := by rw [map_mul]
      _ = x := by rw [hg, map_one, Module.End.one_apply]
  have hmemX : ∀ (g : Co1) x, x ∈ X → co1Act g x ∈ X := fun g x hx =>
    (hXmem _).2 (Leech.co1Act_mem_co1Orbit ((hXmem x).1 hx) g)
  have h1 := odd_card_fixed X (co1Act r) (hmemX r) (hinv r hr) hXcard
  set X₁ := X.filter fun x => co1Act r x = x with hX₁
  have hcomm : ∀ x, co1Act s (co1Act r x) = co1Act r (co1Act s x) := fun x => by
    calc co1Act s (co1Act r x) = (co1Act s * co1Act r) x := (Module.End.mul_apply _ _ _).symm
      _ = co1Act (s * r) x := by rw [map_mul]
      _ = co1Act (r * s) x := by rw [hrs]
      _ = co1Act r (co1Act s x) := by rw [map_mul, Module.End.mul_apply]
  have hX₁s : ∀ x ∈ X₁, co1Act s x ∈ X₁ := by
    intro x hx
    obtain ⟨hxX, hxr⟩ := Finset.mem_filter.1 hx
    refine Finset.mem_filter.2 ⟨hmemX s x hxX, ?_⟩
    rw [← hcomm, hxr]
  have h2 := odd_card_fixed X₁ (co1Act s) hX₁s (hinv s hs) h1
  obtain ⟨ω, hω⟩ := Finset.card_pos.1 (Nat.pos_of_ne_zero (by
    intro h0
    rw [h0] at h2
    exact absurd h2 (by decide)))
  obtain ⟨hωX₁, hωs⟩ := Finset.mem_filter.1 hω
  obtain ⟨hωX, hωr⟩ := Finset.mem_filter.1 hωX₁
  exact ⟨ω, (hXmem ω).1 hωX, hωr, hωs⟩

@[expose] def UP (a b : Co1) : Prop :=
  ∃ v ∈ co1Orbit 2, (∃ p, v = p + co1Act a p) ∧ (∃ p, v = p + co1Act b p) ∧
    ∃ p, v = p + co1Act (a * b) p

theorem UP.conj {a b : Co1} (g : Co1) (h : UP a b) : UP (g * a * g⁻¹) (g * b * g⁻¹) := by
  obtain ⟨v, hv, ⟨p₁, h₁⟩, ⟨p₂, h₂⟩, ⟨p₃, h₃⟩⟩ := h
  have key : ∀ (c : Co1) (p : Fin 24 → ZMod 2),
      co1Act (g * c * g⁻¹) (co1Act g p) = co1Act g (co1Act c p) := fun c p => by
    calc co1Act (g * c * g⁻¹) (co1Act g p) = (co1Act (g * c * g⁻¹) * co1Act g) p :=
          (Module.End.mul_apply _ _ _).symm
      _ = co1Act (g * c * g⁻¹ * g) p := by rw [← map_mul]
      _ = co1Act (g * c) p := by rw [show g * c * g⁻¹ * g = g * c by group]
      _ = co1Act g (co1Act c p) := by rw [map_mul, Module.End.mul_apply]
  have hprod : g * a * g⁻¹ * (g * b * g⁻¹) = g * (a * b) * g⁻¹ := by group
  refine ⟨co1Act g v, Leech.co1Act_mem_co1Orbit hv g, ⟨co1Act g p₁, ?_⟩, ⟨co1Act g p₂, ?_⟩,
    ⟨co1Act g p₃, ?_⟩⟩
  · rw [key, ← map_add, ← h₁]
  · rw [key, ← map_add, ← h₂]
  · rw [hprod, key, ← map_add, ← h₃]

open CFSG.Sporadic.Co1.Module.Odd (rho3 Hst omega0 S_card_eq isCo1TwoA_rho3 rho3_ncard_fix
  oddHyp73 uCheck45_ok)

@[expose] def SS : Set Co1 := {t : Co1 | t ∈ Hst ∧ IsConj rho3 t}

theorem SS_conj_mem
    {n t : Co1} (hn : n ∈ Hst) (ht : t ∈ SS) : n * t * n⁻¹ ∈ SS :=
  ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hn ht.1) (Subgroup.inv_mem _ hn),
    ht.2.trans (isConj_iff.2 ⟨n, rfl⟩)⟩

theorem card_centralizer_rho3 :
    Nat.card ↥(Subgroup.centralizer ({rho3} : Set Co1)) = 89181388800 := by
  have h := isCo1TwoA_rho3.2
  rw [rho3_ncard_fix] at h
  norm_num at h
  omega

theorem UP_of_S
    {a b : Co1} (ha : a ∈ SS) (hb : b ∈ SS)
    (hab : a * b = b * a) (hab' : a * b ∈ SS) : UP a b := by
  obtain ⟨W, U, hW, hU⟩ := uCheck45_ok
  obtain ⟨v, -, -, h, -⟩ :=
    uk45_of_S hW hU oddHyp73 (S_card_eq card_centralizer_rho3) ha hb hab hab'
  exact ⟨v, h⟩

theorem co1FourU :
    Co1FourU := by
  intro r s hr hs hrs hrs2
  have hI := co1InvolutionFacts
  have hr2 : r * r = 1 := by
    have h : r ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.1 (by rw [hr.1])
    rwa [pow_two] at h
  have hs2 : s * s = 1 := by
    have h : s ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.1 (by rw [hs.1])
    rwa [pow_two] at h
  obtain ⟨ω, hω4, hωr, hωs⟩ := exists_fixed_type4 hr2 hs2 hrs
  have hω0 : omega0 ∈ co1Orbit 2 := by
    rw [CFSG.Sporadic.Co1.Module.Pairs.co1Orbit_two, CFSG.Sporadic.Co1.Module.Pairs.orbit_Co1_eq]
    exact CFSG.Sporadic.Co1.Module.Odd.omega0_mem
  obtain ⟨y, hy⟩ := Leech.exists_co1Act_eq hω0 hω4
  have hmem : ∀ u : Co1, co1Act u ω = ω → y⁻¹ * u * y ∈ Hst := by
    intro u hu
    refine MulAction.mem_stabilizer_iff.2 ?_
    show co1Act (y⁻¹ * u * y) omega0 = omega0
    have h1 : co1Act (y⁻¹ * u * y) omega0 = co1Act y⁻¹ (co1Act u (co1Act y omega0)) := by
      simp only [map_mul, Module.End.mul_apply]
    rw [h1, hy, hu, ← hy]
    simp only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have hconj : ∀ u : Co1, IsCo1TwoA u → IsConj rho3 (y⁻¹ * u * y) := by
    intro u hu
    have h1 : IsConj rho3 u :=
      hI.2.2 rho3 u isCo1TwoA_rho3.1 hu.1 isCo1TwoA_rho3.2 hu.2
    exact h1.trans (isConj_iff.2 ⟨y⁻¹, by group⟩)
  have hr'S : y⁻¹ * r * y ∈ SS := ⟨hmem r hωr, hconj r hr⟩
  have hs'S : y⁻¹ * s * y ∈ SS := ⟨hmem s hωs, hconj s hs⟩
  have hrs'S : y⁻¹ * r * y * (y⁻¹ * s * y) ∈ SS := by
    have e : y⁻¹ * r * y * (y⁻¹ * s * y) = y⁻¹ * (r * s) * y := by group
    rw [e]
    refine ⟨?_, hconj _ hrs2⟩
    rw [← e]
    exact Subgroup.mul_mem _ (hmem r hωr) (hmem s hωs)
  have hcomm' : y⁻¹ * r * y * (y⁻¹ * s * y) = y⁻¹ * s * y * (y⁻¹ * r * y) := by
    calc y⁻¹ * r * y * (y⁻¹ * s * y) = y⁻¹ * (r * s) * y := by group
      _ = y⁻¹ * (s * r) * y := by rw [hrs]
      _ = y⁻¹ * s * y * (y⁻¹ * r * y) := by group
  have hUP := (UP_of_S hr'S hs'S hcomm' hrs'S).conj y
  have e1 : y * (y⁻¹ * r * y) * y⁻¹ = r := by group
  have e2 : y * (y⁻¹ * s * y) * y⁻¹ = s := by group
  rw [e1, e2] at hUP
  exact hUP

end S365

end CFSG.Monster.GMS
