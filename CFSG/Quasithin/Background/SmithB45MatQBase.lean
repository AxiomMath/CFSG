module

public import CFSG.Quasithin.Background.HMathieuFacts24Base

public section

namespace CFSG.Quasithin.B45Mat

open CFSG.Quasithin.H.Mathieu CFSG.QuasithinUnique.Setup.X1

variable {V : Type*} [CommGroup V]

theorem fix_comm_of_quadratic {A : Subgroup (MulAut V)} (hq : commSeries A 2 = ⊥)
    {s t : MulAut V} (hs : s ∈ A) (ht : t ∈ A) (v : V) : s (t v * v⁻¹) = t v * v⁻¹ := by
  have hQ : IsQuadratic A := (isQuadratic_iff_commSeries_two A).2 hq
  have hw : t v * v⁻¹ ∈ commV A := Subgroup.subset_closure ⟨t, ht, v, rfl⟩
  exact hQ hw s hs

theorem vm_inv_eq {n : ℕ} (c : MaskCoords V n) (m : ℕ) : (c.vm m)⁻¹ = c.vm m :=
  inv_eq_of_mul_eq_one_right (by rw [← c.vm_xor, Nat.xor_self, c.vm_zero])

variable {n : ℕ} {P : Type*} [Group P] {c : MaskCoords V n} {aut : P →* MulAut V}
  {act : P → ℕ → ℕ} {l : List P} {A : Subgroup (MulAut V)}

theorem act_fix_of_quadratic (hc : ChainAct c aut act) (hA : IsChainSub aut l A)
    (hq : commSeries A 2 = ⊥) {s t : P} (hs : s ∈ l) (ht : t ∈ l) {m : ℕ} (hm : m < 2 ^ n) :
    act s (act t m ^^^ m) = act t m ^^^ m := by
  have hsA : aut s ∈ A := (hA _).2 ⟨s, mem_subprods_of_mem hs, rfl⟩
  have htA : aut t ∈ A := (hA _).2 ⟨t, mem_subprods_of_mem ht, rfl⟩
  have hx : act t m ^^^ m < 2 ^ n := Nat.xor_lt_two_pow (hc.lt t m hm) hm
  have h1 := fix_comm_of_quadratic hq hsA htA (c.vm m)
  have h2 : aut t (c.vm m) * (c.vm m)⁻¹ = c.vm (act t m ^^^ m) := by
    rw [hc.spec t m hm, c.vm_xor, vm_inv_eq]
  rw [h2, hc.spec s _ hx] at h1
  exact c.vm_inj _ _ (hc.lt s _ hx) hx h1

theorem rkIdx_fixV_of_chain (hc : ChainAct c aut act) (hA : IsChainSub aut l A) :
    rkIdx (fixV A) = n - Nat.log 2 (fixMasks n act l).length :=
  c.rkIdx_of_card (card_fixV hc hA)

theorem rk_of_chain [DecidableEq P] (hA : IsChainSub aut l A) (hinj : Function.Injective aut)
    (hl : IndepList l) : rk ↥A = l.length := by
  unfold rk
  rw [card_of_chainSub hA hinj hl, padicValNat.prime_pow]

theorem two_lt_qOf_of_forall [Finite V] {G : Subgroup (MulAut V)}
    (h : ∀ A, IsA2 G A → commSeries A 2 = ⊥ → 2 * rk ↥A < rkIdx (fixV A)) :
    ((2 : ℚ) : WithTop ℚ) < qOf G := by
  unfold qOf
  rw [lt_kq_iff]
  intro A hA hq
  have hr : (0 : ℚ) < (rk ↥A : ℚ) := by exact_mod_cast hA.rk_pos
  have h2 : ((2 * rk ↥A : ℕ) : ℚ) < (rkIdx (fixV A) : ℚ) := by exact_mod_cast h A hA hq
  unfold rAV
  rw [lt_div_iff₀ hr]
  push_cast at h2
  linarith

theorem two_le_qOf_of_forall [Finite V] {G : Subgroup (MulAut V)}
    (h : ∀ A, IsA2 G A → commSeries A 2 = ⊥ → 2 * rk ↥A ≤ rkIdx (fixV A)) :
    ((2 : ℚ) : WithTop ℚ) ≤ qOf G := by
  unfold qOf
  rw [le_kq_iff]
  intro A hA hq
  have hr : (0 : ℚ) < (rk ↥A : ℚ) := by exact_mod_cast hA.rk_pos
  have h2 : ((2 * rk ↥A : ℕ) : ℚ) ≤ (rkIdx (fixV A) : ℚ) := by exact_mod_cast h A hA hq
  unfold rAV
  rw [le_div_iff₀ hr]
  push_cast at h2
  linarith

end CFSG.Quasithin.B45Mat
