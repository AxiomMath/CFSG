module

public import CFSG.Quasithin.Background.A1cModuleAut

public section

namespace CFSG.Quasithin

namespace A37

open scoped commutatorElement

variable {V : Type*} [CommGroup V]

theorem commute_of_irreducible [Finite V] (S T : Subgroup (MulAut V))
    (hirr : XMod.IsIrrSec ↥S (⊥ : Subgroup V) ⊤)
    (hST : ∀ s ∈ S, ∀ t ∈ T, s * t = t * s) :
    ∀ t₁ ∈ T, ∀ t₂ ∈ T, t₁ * t₂ = t₂ * t₁ := by
  have hnt := XMod.nontrivial_eqvEnd hirr
  have hfin := XMod.finite_eqvEnd (A := ↥S) (P := V)
  let _ : DivisionRing ↥(XMod.eqvEnd ↥S V) :=
    DivisionRing.ofIsUnitOrEqZero (XMod.eqvEnd_isUnit_or_eq_zero hirr)
  have hfield : IsField ↥(XMod.eqvEnd ↥S V) := (littleWedderburn _).toIsField
  have hmem : ∀ t ∈ T, ∃ f : AddMonoid.End (Additive V), f ∈ XMod.eqvEnd ↥S V ∧
      ∀ p, f (Additive.ofMul p) = Additive.ofMul (t p) := by
    intro t ht
    let f : AddMonoid.End (Additive V) := MonoidHom.toAdditive (t : V →* V)
    refine ⟨f, ?_, fun p => rfl⟩
    refine XMod.mem_eqvEnd_iff.2 fun a p => ?_
    have h := congrArg (fun φ : MulAut V => φ p) (hST a a.2 t ht)
    exact h.symm
  intro t₁ h₁ t₂ h₂
  obtain ⟨f₁, hf₁, e₁⟩ := hmem t₁ h₁
  obtain ⟨f₂, hf₂, e₂⟩ := hmem t₂ h₂
  have h := hfield.mul_comm ⟨f₁, hf₁⟩ ⟨f₂, hf₂⟩
  refine MulEquiv.ext fun p => ?_
  have := congrArg (fun e : ↥(XMod.eqvEnd ↥S V) =>
    (e : AddMonoid.End (Additive V)) (Additive.ofMul p)) h
  change f₁ (f₂ (Additive.ofMul p)) = f₂ (f₁ (Additive.ofMul p)) at this
  rw [e₂, e₁, e₁, e₂] at this
  exact Additive.ofMul.injective this

theorem comm_mod_of_cyclic_section {H K : Subgroup V} (a b : MulAut V)
    (haK : ∀ k ∈ K, a k ∈ K) (hbK : ∀ k ∈ K, b k ∈ K)
    (haH : ∀ h ∈ H, a h ∈ H) (hbH : ∀ h ∈ H, b h ∈ H)
    (hcyc : ∃ h₀ ∈ H, ∀ h ∈ H, ∃ n : ℤ, h * (h₀ ^ n)⁻¹ ∈ K) :
    ∀ h ∈ H, a (b h) * (b (a h))⁻¹ ∈ K := by
  obtain ⟨h₀, hh₀, hgen⟩ := hcyc
  let fa : V ⧸ K →* V ⧸ K := QuotientGroup.map K K (a : V →* V) (fun k hk => haK k hk)
  let fb : V ⧸ K →* V ⧸ K := QuotientGroup.map K K (b : V →* V) (fun k hk => hbK k hk)
  have hfa : ∀ v : V, fa (v : V ⧸ K) = ((a v : V) : V ⧸ K) := fun v => rfl
  have hfb : ∀ v : V, fb (v : V ⧸ K) = ((b v : V) : V ⧸ K) := fun v => rfl
  have hmk : ∀ h ∈ H, ∃ n : ℤ, (h : V ⧸ K) = ((h₀ : V) : V ⧸ K) ^ n := by
    intro h hh
    obtain ⟨n, hn⟩ := hgen h hh
    refine ⟨n, ?_⟩
    rw [← QuotientGroup.mk_zpow, QuotientGroup.eq_iff_div_mem, div_eq_mul_inv]
    exact hn
  obtain ⟨ka, hka⟩ := hmk (a h₀) (haH h₀ hh₀)
  obtain ⟨kb, hkb⟩ := hmk (b h₀) (hbH h₀ hh₀)
  have e₁ : fa (fb (h₀ : V ⧸ K)) = ((h₀ : V) : V ⧸ K) ^ (kb * ka) := by
    rw [hfb, hkb, map_zpow, hfa, hka, ← zpow_mul, mul_comm]
  have e₂ : fb (fa (h₀ : V ⧸ K)) = ((h₀ : V) : V ⧸ K) ^ (kb * ka) := by
    rw [hfa, hka, map_zpow, hfb, hkb, ← zpow_mul]
  intro h hh
  obtain ⟨n, hn⟩ := hmk h hh
  have key : fa (fb (h : V ⧸ K)) = fb (fa (h : V ⧸ K)) := by
    rw [hn, map_zpow, map_zpow, e₁, map_zpow, map_zpow, e₂]
  rw [hfa, hfb, hfa, hfb] at key
  rw [QuotientGroup.eq_iff_div_mem] at key
  simpa [div_eq_mul_inv] using key

def trivialOnQuotient (J : Subgroup V) : Subgroup (MulAut V) where
  carrier := {s | ∀ v : V, s v * v⁻¹ ∈ J}
  one_mem' := fun v => by simp
  mul_mem' := fun {s t} hs ht v => by
    have h := J.mul_mem (hs (t v)) (ht v)
    simpa [MulAut.mul_apply, mul_assoc] using h
  inv_mem' := fun {s} hs v => by
    have h := J.inv_mem (hs (s⁻¹ v))
    simpa [mul_comm] using h

def fixesPointwise (J : Subgroup V) : Subgroup (MulAut V) where
  carrier := {s | ∀ j ∈ J, s j = j}
  one_mem' := fun j _ => rfl
  mul_mem' := fun {s t} hs ht j hj => by
    rw [MulAut.mul_apply, ht j hj, hs j hj]
  inv_mem' := fun {s} hs j hj => by
    calc s⁻¹ j = s⁻¹ (s j) := by rw [hs j hj]
      _ = j := MulAut.inv_apply_self V s j

theorem commute_of_flag {J : Subgroup V} {s t : MulAut V} (hs₁ : s ∈ fixesPointwise J)
    (hs₂ : s ∈ trivialOnQuotient J) (ht₁ : t ∈ fixesPointwise J)
    (ht₂ : t ∈ trivialOnQuotient J) : s * t = t * s := by
  refine MulEquiv.ext fun v => ?_
  have hj : t v * v⁻¹ ∈ J := ht₂ v
  have hj' : s v * v⁻¹ ∈ J := hs₂ v
  have e₁ : s (t v) = s v * (t v * v⁻¹) := by
    have : t v = v * (t v * v⁻¹) := by simp [mul_comm]
    conv_lhs => rw [this]
    rw [map_mul, hs₁ _ hj]
  have e₂ : t (s v) = t v * (s v * v⁻¹) := by
    have : s v = v * (s v * v⁻¹) := by simp [mul_comm]
    conv_lhs => rw [this]
    rw [map_mul, ht₁ _ hj']
  rw [MulAut.mul_apply, MulAut.mul_apply, e₁, e₂]
  exact mul_left_comm _ _ _

theorem irreducible_of_perfect [Finite V] {q : ℕ} (hq : q.Prime) (hV : Nat.card V = q ^ 2)
    (S : Subgroup (MulAut V)) (hS : ⁅S, S⁆ = S) (hne : S ≠ ⊥) :
    XMod.IsIrrSec ↥S (⊥ : Subgroup V) ⊤ := by
  have : Fact q.Prime := ⟨hq⟩
  have hqpos : 0 < q := hq.pos
  refine ⟨lt_of_le_of_ne bot_le fun h => ?_, fun J hJ _ _ => ?_⟩
  · have h1 := congrArg (fun H : Subgroup V => Nat.card H) h
    simp only [Subgroup.card_bot, Subgroup.card_top, hV] at h1
    have := Nat.one_lt_pow (two_ne_zero) hq.one_lt
    omega
  by_contra hcon
  push Not at hcon
  obtain ⟨hJbot, hJtop⟩ := hcon
  have hinv : ∀ s ∈ S, ∀ v ∈ J, s v ∈ J := fun s hs v hv => hJ ⟨s, hs⟩ v hv
  have hJcard : Nat.card J = q := by
    obtain ⟨m, hm, hm'⟩ := (Nat.dvd_prime_pow hq).1 (hV ▸ Subgroup.card_subgroup_dvd_card J)
    interval_cases m
    · exact absurd (Subgroup.card_eq_one.1 (by simpa using hm')) hJbot
    · simpa using hm'
    · exact absurd (Subgroup.eq_top_of_card_eq J (by rw [hm', hV])) hJtop
  have hQcard : Nat.card (V ⧸ J) = q := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup J
    rw [hV, hJcard, sq] at h
    exact (Nat.eq_of_mul_eq_mul_right hqpos h.symm)
  have hcycJ : IsCyclic J := isCyclic_of_prime_card hJcard
  have hcycQ : IsCyclic (V ⧸ J) := isCyclic_of_prime_card hQcard
  have hsecJ : ∃ h₀ ∈ J, ∀ h ∈ J, ∃ n : ℤ, h * (h₀ ^ n)⁻¹ ∈ (⊥ : Subgroup V) := by
    obtain ⟨g, hg⟩ := hcycJ.exists_generator
    refine ⟨g, g.2, fun h hh => ?_⟩
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 (hg ⟨h, hh⟩)
    refine ⟨n, ?_⟩
    have : ((g : V)) ^ n = h := by
      have := congrArg Subtype.val hn
      simpa using this
    rw [this, mul_inv_cancel]
    exact Subgroup.one_mem _
  have hsecQ : ∃ h₀ ∈ (⊤ : Subgroup V), ∀ h ∈ (⊤ : Subgroup V),
      ∃ n : ℤ, h * (h₀ ^ n)⁻¹ ∈ J := by
    obtain ⟨g, hg⟩ := hcycQ.exists_generator
    obtain ⟨v₀, rfl⟩ := QuotientGroup.mk_surjective g
    refine ⟨v₀, trivial, fun v _ => ?_⟩
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 (hg (v : V ⧸ J))
    refine ⟨n, ?_⟩
    rw [← QuotientGroup.mk_zpow, QuotientGroup.eq_iff_div_mem] at hn
    have := J.inv_mem hn
    simpa [div_eq_mul_inv] using this
  have hN₁ : ⁅S, S⁆ ≤ fixesPointwise J := by
    rw [Subgroup.commutator_le]
    intro a ha b hb j hj
    have hj' : a⁻¹ (b⁻¹ j) ∈ J := hinv _ (S.inv_mem ha) _ (hinv _ (S.inv_mem hb) _ hj)
    have h := comm_mod_of_cyclic_section (H := J) (K := ⊥) a b
      (fun k hk => by rw [Subgroup.mem_bot.1 hk, map_one]; exact Subgroup.one_mem _)
      (fun k hk => by rw [Subgroup.mem_bot.1 hk, map_one]; exact Subgroup.one_mem _)
      (hinv a ha) (hinv b hb) hsecJ _ hj'
    rw [Subgroup.mem_bot, mul_inv_eq_one] at h
    show (a * b * a⁻¹ * b⁻¹) j = j
    simp only [MulAut.mul_apply]
    rw [h]
    simp
  have hN₂ : ⁅S, S⁆ ≤ trivialOnQuotient J := by
    rw [Subgroup.commutator_le]
    intro a ha b hb v
    have h := comm_mod_of_cyclic_section (H := ⊤) (K := J) a b (hinv a ha) (hinv b hb)
      (fun _ _ => trivial) (fun _ _ => trivial) hsecQ (a⁻¹ (b⁻¹ v)) trivial
    have e : b (a (a⁻¹ (b⁻¹ v))) = v := by simp
    rw [e] at h
    show (a * b * a⁻¹ * b⁻¹) v * v⁻¹ ∈ J
    simpa [MulAut.mul_apply] using h
  rw [hS] at hN₁ hN₂
  apply hne
  rw [← hS, eq_bot_iff, Subgroup.commutator_le]
  intro a ha b hb
  rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
  exact commute_of_flag (hN₁ ha) (hN₂ ha) (hN₁ hb) (hN₂ hb)

theorem eq_bot_of_commute [Finite V] {q : ℕ} (hq : q.Prime) (hV : Nat.card V = q ^ 2)
    (S T : Subgroup (MulAut V)) (hS : ⁅S, S⁆ = S) (hne : S ≠ ⊥) (hT : ⁅T, T⁆ = T)
    (hST : ∀ s ∈ S, ∀ t ∈ T, s * t = t * s) : T = ⊥ := by
  have hcomm := commute_of_irreducible S T (irreducible_of_perfect hq hV S hS hne) hST
  rw [← hT, eq_bot_iff, Subgroup.commutator_le]
  intro a ha b hb
  rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
  exact hcomm a ha b hb

end A37

end CFSG.Quasithin
