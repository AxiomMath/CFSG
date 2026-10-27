module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarNoOffenderUOProjCount

public section

namespace CFSG.StandardType

namespace NoOffUO

open CFSG.Assembly

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Slice

variable {X : Type} [Fintype X] {p : ℕ}

omit [Fintype X] in
theorem card_inter_mul_eq [NeZero p] {S : Set (X → ZMod p)} {w : X → ZMod p}
    {φ : (X → ZMod p) → ZMod p} (hS : ∀ v ∈ S, ∀ t : ZMod p, v + t • w ∈ S)
    (hφ : ∀ v (t : ZMod p), φ (v + t • w) = φ v + t) :
    Nat.card (S ∩ {v | φ v = 0} : Set (X → ZMod p)) * p = Nat.card S := by
  have e : (S ∩ {v | φ v = 0} : Set (X → ZMod p)) × ZMod p ≃ S :=
    { toFun := fun vt => ⟨(vt.1 : X → ZMod p) + vt.2 • w, hS _ vt.1.2.1 _⟩
      invFun := fun v => (⟨(v : X → ZMod p) + (-φ v) • w, hS _ v.2 _, by
          change φ ((v : X → ZMod p) + (-φ v) • w) = 0
          rw [hφ, add_neg_cancel]⟩, φ v)
      left_inv := fun vt => by
        obtain ⟨⟨v, hv, hv0⟩, t⟩ := vt
        have h0 : φ v = 0 := hv0
        simp only [hφ, h0, zero_add]
        ext x
        · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
          ring
        · rfl
      right_inv := fun v => by
        apply Subtype.ext
        show (v : X → ZMod p) + (-φ v) • w + (φ v) • w = v
        rw [neg_smul, neg_add_cancel_right] }
  rw [← Nat.card_congr e, Nat.card_prod, Nat.card_zmod]

theorem card_evalZero_mul [NeZero p] [DecidableEq X] (x₀ : X) :
    Nat.card {v : X → ZMod p | v x₀ = 0} * p = p ^ Fintype.card X := by
  have h := card_inter_mul_eq (S := (Set.univ : Set (X → ZMod p))) (w := Pi.single x₀ 1)
    (φ := fun v => v x₀) (fun _ _ _ => Set.mem_univ _) (fun v t => by simp)
  rw [Set.univ_inter] at h
  rw [h, Nat.card_univ, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card]

theorem card_sumZero_mul [NeZero p] [DecidableEq X] (x₀ : X) :
    Nat.card {v : X → ZMod p | ∑ x, v x = 0} * p = p ^ Fintype.card X := by
  have h := card_inter_mul_eq (S := (Set.univ : Set (X → ZMod p))) (w := Pi.single x₀ 1)
    (φ := fun v : X → ZMod p => ∑ x, v x) (fun _ _ _ => Set.mem_univ _) (fun v t => by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
        ← Finset.mul_sum, Finset.sum_pi_single', Finset.mem_univ, ite_true, mul_one])
  rw [Set.univ_inter] at h
  rw [h, Nat.card_univ, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card]

theorem sum_add_smul_one {v : X → ZMod p} (hX : (Fintype.card X : ZMod p) = 0) (t : ZMod p) :
    ∑ x, (v + t • (1 : X → ZMod p)) x = ∑ x, v x := by
  simp only [Pi.add_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one,
    Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hX, zero_mul,
    add_zero]

theorem card_sumZero_evalZero_mul [NeZero p] (hX : (Fintype.card X : ZMod p) = 0) (x₀ : X) :
    Nat.card ({v : X → ZMod p | ∑ x, v x = 0} ∩ {v | v x₀ = 0} : Set (X → ZMod p)) * p =
      Nat.card {v : X → ZMod p | ∑ x, v x = 0} :=
  card_inter_mul_eq (w := 1) (φ := fun v => v x₀)
    (fun v hv t => by
      change ∑ x, (v + t • (1 : X → ZMod p)) x = 0
      rw [sum_add_smul_one hX]
      exact hv)
    (fun v t => by simp)

omit [Fintype X] in
theorem add_smul_one_mem_projFix {A : Subgroup (Equiv.Perm X)} {v : X → ZMod p}
    (hv : v ∈ projFix p A) (t : ZMod p) : v + t • (1 : X → ZMod p) ∈ projFix p A := by
  intro a ha
  obtain ⟨c, hc⟩ := hv a ha
  exact ⟨c, fun x => by simp only [Pi.add_apply, Pi.smul_apply, Pi.one_apply, hc x]; ring⟩

omit [Fintype X] in
theorem card_projFix_evalZero_mul [NeZero p] {A : Subgroup (Equiv.Perm X)} (x₀ : X) :
    Nat.card (projFix p A ∩ {v | v x₀ = 0} : Set (X → ZMod p)) * p = Nat.card (projFix p A) :=
  card_inter_mul_eq (w := 1) (φ := fun v => v x₀) (fun v hv t => add_smul_one_mem_projFix hv t)
    (fun v t => by simp)

theorem card_projFix_sumZero_evalZero_mul [NeZero p] {A : Subgroup (Equiv.Perm X)}
    (hX : (Fintype.card X : ZMod p) = 0) (x₀ : X) :
    Nat.card (projFix p A ∩ {v | ∑ x, v x = 0} ∩ {v | v x₀ = 0} : Set (X → ZMod p)) * p =
      Nat.card (projFix p A ∩ {v | ∑ x, v x = 0} : Set (X → ZMod p)) :=
  card_inter_mul_eq (w := 1) (φ := fun v => v x₀)
    (fun v hv t => ⟨add_smul_one_mem_projFix hv.1 t, by
      change ∑ x, (v + t • (1 : X → ZMod p)) x = 0
      rw [sum_add_smul_one hX]
      exact hv.2⟩)
    (fun v t => by simp)

end Slice

section Faith

variable {p n : ℕ}

theorem sum_single_sub_single (i j : Fin n) :
    ∑ x, (Pi.single i (1 : ZMod p) - Pi.single j (1 : ZMod p) : Fin n → ZMod p) x = 0 := by
  simp [Finset.sum_sub_distrib]

theorem perm_apply_of_single [Fact p.Prime] (hp2 : p ≠ 2) (hn : 4 ≤ n) {σ : Equiv.Perm (Fin n)}
    {s : ZMod p} {i j : Fin n} (hij : i ≠ j) {c : ZMod p}
    (hc : ∀ x, s * (Pi.single i (1 : ZMod p) - Pi.single j (1 : ZMod p) : Fin n → ZMod p) (σ x) =
      (Pi.single i (1 : ZMod p) - Pi.single j (1 : ZMod p) : Fin n → ZMod p) x + c) :
    (σ i = i ∧ s = 1) ∨ σ i = j := by
  classical
  set v : Fin n → ZMod p := Pi.single i 1 - Pi.single j 1 with hv
  have hv0 : ∑ x, v x = 0 := sum_single_sub_single i j
  have hvi : v i = 1 := by simp [hv, Pi.single_eq_of_ne hij]
  have hvo : ∀ x, x ≠ i → x ≠ j → v x = 0 := fun x hxi hxj => by
    simp [hv, Pi.single_eq_of_ne hxi, Pi.single_eq_of_ne hxj]
  have hc0 : c = 0 := by
    by_contra hcne
    have hcover : ∀ x, x ∈ ({i, j, σ.symm i, σ.symm j} : Finset (Fin n)) := by
      intro x
      by_contra hx
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
      obtain ⟨hxi, hxj, hxi', hxj'⟩ := hx
      have h1 : σ x ≠ i := fun h => hxi' (by rw [← h, Equiv.symm_apply_apply])
      have h2 : σ x ≠ j := fun h => hxj' (by rw [← h, Equiv.symm_apply_apply])
      have := hc x
      rw [hvo _ h1 h2, hvo x hxi hxj, mul_zero, zero_add] at this
      exact hcne this.symm
    have hcard : n ≤ 4 := by
      have := Finset.card_le_card (fun x _ => hcover x :
        (Finset.univ : Finset (Fin n)) ⊆ {i, j, σ.symm i, σ.symm j})
      rw [Finset.card_univ, Fintype.card_fin] at this
      exact this.trans Finset.card_le_four
    have hn4 : n = 4 := le_antisymm hcard hn
    have hsum : ∑ x, s * v (σ x) = ∑ x, (v x + c) := Finset.sum_congr rfl fun x _ => hc x
    rw [← Finset.mul_sum, Equiv.sum_comp σ v, hv0, mul_zero, Finset.sum_add_distrib, hv0,
      zero_add, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
    rw [hn4] at hsum
    have h4 : ((4 : ℕ) : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      intro h4
      have hpp : p.Prime := Fact.out
      have h2 : p ∣ 2 ^ 2 := by norm_num; exact h4
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).mp (hpp.dvd_of_dvd_pow h2))
    exact hcne ((mul_eq_zero.mp hsum.symm).resolve_left h4)
  have hi := hc i
  rw [hc0, add_zero, hvi] at hi
  by_cases h1 : σ i = i
  · left
    rw [h1, hvi, mul_one] at hi
    exact ⟨h1, hi⟩
  · by_cases h2 : σ i = j
    · exact Or.inr h2
    · rw [hvo _ h1 h2, mul_zero] at hi
      exact absurd hi zero_ne_one

theorem perm_eq_one_of_forall [Fact p.Prime] (hp2 : p ≠ 2) (hn : 4 ≤ n)
    {σ : Equiv.Perm (Fin n)} {s : ZMod p}
    (h : ∀ v : Fin n → ZMod p, ∑ i, v i = 0 → ∃ c : ZMod p, ∀ i, s * v (σ i) = v i + c) :
    σ = 1 ∧ s = 1 := by
  classical
  have key : ∀ i j : Fin n, i ≠ j → (σ i = i ∧ s = 1) ∨ σ i = j := by
    intro i j hij
    obtain ⟨c, hc⟩ := h (Pi.single i 1 - Pi.single j 1) (sum_single_sub_single i j)
    exact perm_apply_of_single hp2 hn hij hc
  have hfix : ∀ i, σ i = i ∧ s = 1 := by
    intro i
    obtain ⟨j, hj⟩ : ∃ j : Fin n, j ≠ i := by
      by_cases hi : (i : ℕ) = 0
      · exact ⟨⟨1, by omega⟩, fun h => by simp [Fin.ext_iff] at h; omega⟩
      · exact ⟨⟨0, by omega⟩, fun h => hi (by rw [← h])⟩
    obtain ⟨k, hki, hkj⟩ : ∃ k : Fin n, k ≠ i ∧ k ≠ j := by
      have hcard : 2 ≤ ((Finset.univ.erase i).erase j).card := by
        rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ _⟩),
          Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
        omega
      obtain ⟨k, hk⟩ := Finset.card_pos.mp (by omega : 0 < ((Finset.univ.erase i).erase j).card)
      exact ⟨k, (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1, (Finset.mem_erase.mp hk).1⟩
    rcases key i j hj.symm with h1 | h1
    · exact h1
    · rcases key i k hki.symm with h2 | h2
      · exact h2
      · exact absurd (h1.symm.trans h2) hkj.symm
  have h0 : 0 < n := by omega
  exact ⟨Equiv.ext fun i => (hfix i).1, (hfix ⟨0, h0⟩).2⟩

end Faith

section Rep

variable {G : Type} [Group G] {p n : ℕ}

@[expose] def IsProjRep (κ : G → (Fin n → ZMod p)) (Bs : Subgroup G) (g : G)
    (π : Equiv.Perm (Fin n)) (s : ZMod p) : Prop :=
  ∀ b ∈ Bs, ∃ c : ZMod p, ∀ i, κ (g⁻¹ * b * g) i = s * κ b (π i) + c

theorem IsProjRep.one (κ : G → (Fin n → ZMod p)) (Bs : Subgroup G) : IsProjRep κ Bs 1 1 1 :=
  fun _ _ => ⟨0, fun i => by simp⟩

theorem inv_mul_mul_mem_of_mem_normalizer {Bs : Subgroup G} {g b : G}
    (hg : g ∈ Subgroup.normalizer (Bs : Set G)) (hb : b ∈ Bs) : g⁻¹ * b * g ∈ Bs := by
  have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) b).mp hb
  rwa [inv_inv] at this

theorem IsProjRep.mul {κ : G → (Fin n → ZMod p)} {Bs : Subgroup G} {g g' : G}
    {π π' : Equiv.Perm (Fin n)} {s s' : ZMod p} (h : IsProjRep κ Bs g π s)
    (h' : IsProjRep κ Bs g' π' s') (hg : g ∈ Subgroup.normalizer (Bs : Set G)) :
    IsProjRep κ Bs (g * g') (π * π') (s * s') := by
  intro b hb
  obtain ⟨c, hc⟩ := h b hb
  obtain ⟨c', hc'⟩ := h' _ (inv_mul_mul_mem_of_mem_normalizer hg hb)
  refine ⟨s' * c + c', fun i => ?_⟩
  have e : (g * g')⁻¹ * b * (g * g') = g'⁻¹ * (g⁻¹ * b * g) * g' := by group
  rw [e, hc' i, hc (π' i), Equiv.Perm.mul_apply]
  ring

theorem IsProjRep.pow {κ : G → (Fin n → ZMod p)} {Bs : Subgroup G} {g : G}
    {π : Equiv.Perm (Fin n)} {s : ZMod p} (h : IsProjRep κ Bs g π s)
    (hg : g ∈ Subgroup.normalizer (Bs : Set G)) (k : ℕ) :
    IsProjRep κ Bs (g ^ k) (π ^ k) (s ^ k) := by
  induction k with
  | zero => simpa using IsProjRep.one κ Bs
  | succ k ih =>
    rw [pow_succ, pow_succ, pow_succ]
    exact ih.mul h (Subgroup.pow_mem _ hg k)

theorem IsProjRep.unique [Fact p.Prime] (hp2 : p ≠ 2) (hn : 4 ≤ n) {κ : G → (Fin n → ZMod p)}
    {Bs : Subgroup G}
    (hsurj : ∀ v : Fin n → ZMod p, ∑ i, v i = 0 → ∃ b ∈ Bs, ∃ c : ZMod p, ∀ i, κ b i = v i + c)
    {g : G} {π π' : Equiv.Perm (Fin n)} {s s' : ZMod p} (h : IsProjRep κ Bs g π s)
    (h' : IsProjRep κ Bs g π' s') (hs' : s' ≠ 0) : π = π' ∧ s = s' := by
  have key : ∀ v : Fin n → ZMod p, ∑ i, v i = 0 →
      ∃ c : ZMod p, ∀ j, (s'⁻¹ * s) * v ((π * π'⁻¹) j) = v j + c := by
    intro v hv
    obtain ⟨b, hb, c₀, hc₀⟩ := hsurj v hv
    obtain ⟨c, hc⟩ := h b hb
    obtain ⟨c', hc'⟩ := h' b hb
    refine ⟨s'⁻¹ * (s' * c₀ + c' - s * c₀ - c), fun j => ?_⟩
    have hjj : π' (π'⁻¹ j) = j := by
      rw [← Equiv.Perm.mul_apply, mul_inv_cancel, Equiv.Perm.one_apply]
    have e := (hc (π'⁻¹ j)).symm.trans (hc' (π'⁻¹ j))
    rw [hc₀, hc₀, hjj] at e
    rw [Equiv.Perm.mul_apply]
    apply mul_left_cancel₀ hs'
    have hinv : s' * s'⁻¹ = 1 := mul_inv_cancel₀ hs'
    linear_combination e + (s * v (π (π'⁻¹ j)) - (s' * c₀ + c' - s * c₀ - c)) * hinv
  obtain ⟨h1, h2⟩ := perm_eq_one_of_forall hp2 hn key
  exact ⟨mul_inv_eq_one.mp h1, (inv_mul_eq_one₀ hs').mp h2 |>.symm⟩

end Rep

section Main

variable {G : Type} [Group G] [Finite G] {p n : ℕ}

theorem card_le_card_of_realize {Bs : Subgroup G} {κ₀ : G → (Fin n → ZMod p)}
    {T : Set (Fin n → ZMod p)} (hT : ∀ w ∈ T, ∃ b ∈ Bs, κ₀ b = w) : Nat.card T ≤ Nat.card Bs := by
  choose f hf using hT
  refine Nat.card_le_card_of_injective (fun w : T => (⟨f w w.2, (hf w w.2).1⟩ : Bs)) ?_
  intro w w' h
  apply Subtype.ext
  have h1 := congrArg (fun y : Bs => κ₀ (y : G)) h
  simp only at h1
  rw [(hf w w.2).2, (hf w' w'.2).2] at h1
  exact h1

theorem noOffender_of_projRep (hp : p.Prime) (hp2 : p ≠ 2) (hn : 4 ≤ n)
    {N Bs : Subgroup G} (hBs : IsElemAbelian p Bs) (κ : G → (Fin n → ZMod p))
    (hinj : ∀ b ∈ Bs, ∀ b' ∈ Bs, (∃ c : ZMod p, ∀ i, κ b i = κ b' i + c) → b = b')
    (hsurj : ∀ v : Fin n → ZMod p, ∑ i, v i = 0 → ∃ b ∈ Bs, ∃ c : ZMod p, ∀ i, κ b i = v i + c)
    (hrep : ∀ g ∈ N, g ∈ Subgroup.normalizer (Bs : Set G) → g ^ p = 1 →
      ∃ (π : Equiv.Perm (Fin n)) (s : ZMod p), s ≠ 0 ∧ IsProjRep κ Bs g π s) :
    GGNoOffender p N Bs := by
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  intro E hEN hEB hE
  have hdata : ∀ e : E, ∃ (π : Equiv.Perm (Fin n)) (s : ZMod p), s ≠ 0 ∧
      IsProjRep κ Bs (e : G) π s :=
    fun e => hrep e (hEN e.2) (hEB e.2) (hE.2 e e.2)
  choose π s hs hπs using hdata
  have hs1 : ∀ e : E, s e = 1 := by
    intro e
    have h1 := (hπs e).pow (hEB e.2) p
    rw [hE.2 e e.2] at h1
    have h2 := (IsProjRep.unique hp2 hn hsurj h1 (IsProjRep.one κ Bs) one_ne_zero).2
    rwa [ZMod.pow_card] at h2
  let ρ : E →* Equiv.Perm (Fin n) :=
    { toFun := π
      map_one' := (IsProjRep.unique hp2 hn hsurj (hπs 1) (IsProjRep.one κ Bs) one_ne_zero).1
      map_mul' := fun e e' => (IsProjRep.unique hp2 hn hsurj (hπs (e * e'))
        ((hπs e).mul (hπs e') (hEB e.2)) (mul_ne_zero (hs e) (hs e'))).1 }
  have hker : ∀ e : E, π e = 1 → ∀ b ∈ Bs, (e : G) * b = b * e := by
    intro e he b hb
    obtain ⟨c, hc⟩ := hπs e b hb
    have hb' : (e : G)⁻¹ * b * e ∈ Bs := inv_mul_mul_mem_of_mem_normalizer (hEB e.2) hb
    have h1 : (e : G)⁻¹ * b * e = b := hinj _ hb' b hb ⟨c, fun i => by
      rw [hc i, he, hs1 e, one_mul]
      rfl⟩
    calc (e : G) * b = e * ((e : G)⁻¹ * b * e) := by rw [h1]
      _ = b * e := by group
  have hAcomm : ∀ a ∈ ρ.range, ∀ b ∈ ρ.range, a * b = b * a := by
    rintro _ ⟨e, rfl⟩ _ ⟨e', rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (TableB.IsElemAbelian.comm hE e.2 e'.2)
  have hAexp : ∀ a ∈ ρ.range, a ^ p = 1 := by
    rintro _ ⟨e, rfl⟩
    rw [← map_pow]
    have : e ^ p = 1 :=
      Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact hE.2 e e.2)
    rw [this, map_one]
  by_cases hA : ρ.range = ⊥
  · left
    intro e he
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    have h1 : π ⟨e, he⟩ = 1 := by
      have : ρ ⟨e, he⟩ ∈ ρ.range := ⟨_, rfl⟩
      rw [hA, Subgroup.mem_bot] at this
      exact this
    exact (hker ⟨e, he⟩ h1 b hb).symm
  right
  set x₀ : Fin n := ⟨0, by omega⟩ with hx₀
  set κ₀ : G → (Fin n → ZMod p) := fun b i => κ b i - κ b x₀ with hκ₀
  have hκ₀inj : ∀ b ∈ Bs, ∀ b' ∈ Bs, κ₀ b = κ₀ b' → b = b' := by
    intro b hb b' hb' h
    refine hinj b hb b' hb' ⟨κ b x₀ - κ b' x₀, fun i => ?_⟩
    have := congrFun h i
    simp only [hκ₀] at this
    linear_combination this
  have hκ₀x₀ : ∀ b, κ₀ b x₀ = 0 := fun b => sub_self _
  have hfix : ∀ b ∈ Bs ⊓ Subgroup.centralizer (E : Set G), κ₀ b ∈ projFix p ρ.range := by
    rintro b ⟨hb, hbE⟩ _ ⟨e, rfl⟩
    obtain ⟨c, hc⟩ := hπs e b hb
    have h1 : (e : G)⁻¹ * b * e = b := by
      have h0 := Subgroup.mem_centralizer_iff.mp hbE e e.2
      calc (e : G)⁻¹ * b * e = (e : G)⁻¹ * (e * b) := by rw [mul_assoc, h0]
        _ = b := by group
    refine ⟨κ b (π e x₀) - κ b x₀, fun x => ?_⟩
    have hx := hc x
    have hx₀' := hc x₀
    rw [h1, hs1 e, one_mul] at hx hx₀'
    change κ b (π e x) - κ b x₀ = κ b x - κ b x₀ + (κ b (π e x₀) - κ b x₀)
    linear_combination hx₀' - hx
  have hkerC : Nat.card ρ.ker ≤
      Nat.card (E ⊓ Subgroup.centralizer (Bs : Set G) : Subgroup G) := by
    refine Nat.card_le_card_of_injective
      (fun k : ρ.ker => (⟨((k : E) : G), (k : E).2, Subgroup.mem_centralizer_iff.mpr
        fun b hb => (hker k k.2 b hb).symm⟩ :
          (E ⊓ Subgroup.centralizer (Bs : Set G) : Subgroup G))) fun k k' h => ?_
    have h' := congrArg (fun y : (E ⊓ Subgroup.centralizer (Bs : Set G) : Subgroup G) =>
      (y : G)) h
    exact Subtype.ext (Subtype.ext h')
  have hE' := Subgroup.card_ker_mul_card_range ρ
  have hmain : Nat.card (Bs ⊓ Subgroup.centralizer (E : Set G) : Subgroup G) *
      Nat.card ρ.range < Nat.card Bs := by
    classical
    have hn' : 4 ≤ Fintype.card (Fin n) := by rw [Fintype.card_fin]; exact hn
    have hc1 := card_projFix_mul_lt hp3 hn' hAcomm hAexp hA
    have hc2 := card_projFix_sumZero_mul_lt hp3 hn' hAcomm hAexp hA
    rw [Fintype.card_fin] at hc1 hc2
    have hpn1 : p ^ n = p ^ (n - 1) * p := by rw [← pow_succ, Nat.sub_add_cancel (by omega)]
    have hpn2 : p ^ (n - 1) = p ^ (n - 2) * p := by
      rw [← pow_succ]
      congr 1
      omega
    have hCle : Nat.card (Bs ⊓ Subgroup.centralizer (E : Set G) : Subgroup G) ≤
        Nat.card (projFix p ρ.range ∩ {v | v x₀ = 0} : Set (Fin n → ZMod p)) := by
      refine Nat.card_le_card_of_injective
        (fun c : (Bs ⊓ Subgroup.centralizer (E : Set G) : Subgroup G) =>
          (⟨κ₀ c, hfix c c.2, hκ₀x₀ c⟩ :
            (projFix p ρ.range ∩ {v | v x₀ = 0} : Set (Fin n → ZMod p)))) ?_
      intro c c' h
      exact Subtype.ext (hκ₀inj c c.2.1 c' c'.2.1 (congrArg Subtype.val h))
    have hslice := card_projFix_evalZero_mul (p := p) (A := ρ.range) x₀
    have hreal : ∀ w : Fin n → ZMod p, w x₀ = 0 → ∑ i, w i = 0 → ∃ b ∈ Bs, κ₀ b = w := by
      intro w hw0 hwsum
      obtain ⟨b, hb, c, hc⟩ := hsurj w hwsum
      refine ⟨b, hb, funext fun i => ?_⟩
      change κ b i - κ b x₀ = w i
      rw [hc i, hc x₀, hw0]
      ring
    by_cases hbig : p ^ (n - 1) ≤ Nat.card Bs
    · have h1 : Nat.card (projFix p ρ.range ∩ {v | v x₀ = 0} : Set (Fin n → ZMod p)) *
          Nat.card ρ.range * p < p ^ (n - 1) * p := by
        rw [← hpn1, mul_right_comm, hslice]
        exact hc1
      calc Nat.card (Bs ⊓ Subgroup.centralizer (E : Set G) : Subgroup G) * Nat.card ρ.range
          ≤ Nat.card (projFix p ρ.range ∩ {v | v x₀ = 0} : Set (Fin n → ZMod p)) *
              Nat.card ρ.range := Nat.mul_le_mul_right _ hCle
        _ < p ^ (n - 1) := Nat.lt_of_mul_lt_mul_right h1
        _ ≤ Nat.card Bs := hbig
    push Not at hbig
    have hpn : (n : ZMod p) = 0 := by
      by_contra hpn
      refine absurd hbig (not_lt.mpr ?_)
      have hreal' : ∀ w ∈ {w : Fin n → ZMod p | w x₀ = 0}, ∃ b ∈ Bs, κ₀ b = w := by
        intro w hw0
        set t : ZMod p := (∑ i, w i) / (n : ZMod p) with ht
        have hnt : (n : ZMod p) * t = ∑ i, w i := by
          rw [ht]
          field_simp
        have hsum : ∑ i, (w - t • (1 : Fin n → ZMod p)) i = 0 := by
          simp only [Pi.sub_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one]
          rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul, hnt, sub_self]
        obtain ⟨b, hb, c, hc⟩ := hsurj _ hsum
        refine ⟨b, hb, funext fun i => ?_⟩
        change κ b i - κ b x₀ = w i
        rw [hc i, hc x₀]
        simp only [Pi.sub_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one]
        have hw0' : w x₀ = 0 := hw0
        rw [hw0']
        ring
      have h1 := card_le_card_of_realize hreal'
      have h2 := card_evalZero_mul (p := p) x₀
      rw [Fintype.card_fin, hpn1] at h2
      have h3 : Nat.card {w : Fin n → ZMod p | w x₀ = 0} = p ^ (n - 1) :=
        Nat.eq_of_mul_eq_mul_right (by omega) h2
      rw [← h3]
      exact h1
    have hH : Nat.card ({v : Fin n → ZMod p | ∑ x, v x = 0} ∩ {v | v x₀ = 0} :
        Set (Fin n → ZMod p)) = p ^ (n - 2) := by
      have e1 := card_sumZero_evalZero_mul (X := Fin n) (p := p)
        (by rw [Fintype.card_fin]; exact hpn) x₀
      have e2 := card_sumZero_mul (X := Fin n) (p := p) x₀
      rw [Fintype.card_fin, hpn1, hpn2, ← e1] at e2
      exact Nat.eq_of_mul_eq_mul_right (by omega) (Nat.eq_of_mul_eq_mul_right (by omega) e2)
    have hHB : p ^ (n - 2) ≤ Nat.card Bs := by
      have := card_le_card_of_realize (Bs := Bs) (κ₀ := κ₀)
        (T := {v : Fin n → ZMod p | ∑ x, v x = 0} ∩ {v | v x₀ = 0})
        (fun w hw => hreal w hw.2 hw.1)
      rwa [hH] at this
    have hallH : ∀ b ∈ Bs, ∑ i, κ₀ b i = 0 := by
      intro b₁ hb₁
      by_contra hsum₁
      refine absurd hbig (not_lt.mpr ?_)
      have hnot : κ₀ b₁ ∉ ({v : Fin n → ZMod p | ∑ x, v x = 0} ∩ {v | v x₀ = 0} :
          Set (Fin n → ZMod p)) := fun h => hsum₁ h.1
      have hreal2 : ∀ w ∈ (insert (κ₀ b₁) ({v : Fin n → ZMod p | ∑ x, v x = 0} ∩
          {v | v x₀ = 0}) : Set (Fin n → ZMod p)), ∃ b ∈ Bs, κ₀ b = w := by
        rintro w (hw | ⟨hw1, hw2⟩)
        · exact ⟨b₁, hb₁, hw.symm⟩
        · exact hreal w hw2 hw1
      have h1 := card_le_card_of_realize hreal2
      rw [Nat.card_coe_set_eq, Set.ncard_insert_of_notMem hnot (Set.toFinite _),
        ← Nat.card_coe_set_eq, hH] at h1
      obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp (TableB.isPGroup_of_isElemAbelian hBs)
      rw [hk] at h1 ⊢
      have hlt : n - 2 < k := (Nat.pow_lt_pow_iff_right (by omega)).mp
        (Nat.lt_iff_add_one_le.mpr h1)
      exact Nat.pow_le_pow_right (by omega) (by omega)
    have hCle' : Nat.card (Bs ⊓ Subgroup.centralizer (E : Set G) : Subgroup G) ≤
        Nat.card (projFix p ρ.range ∩ {v | ∑ x, v x = 0} ∩ {v | v x₀ = 0} :
          Set (Fin n → ZMod p)) := by
      refine Nat.card_le_card_of_injective
        (fun c : (Bs ⊓ Subgroup.centralizer (E : Set G) : Subgroup G) =>
          (⟨κ₀ c, ⟨hfix c c.2, hallH c c.2.1⟩, hκ₀x₀ c⟩ :
            (projFix p ρ.range ∩ {v | ∑ x, v x = 0} ∩ {v | v x₀ = 0} :
              Set (Fin n → ZMod p)))) ?_
      intro c c' h
      exact Subtype.ext (hκ₀inj c c.2.1 c' c'.2.1 (congrArg Subtype.val h))
    have hslice' := card_projFix_sumZero_evalZero_mul (p := p) (A := ρ.range)
      (by rw [Fintype.card_fin]; exact hpn) x₀
    have h1 : Nat.card (projFix p ρ.range ∩ {v | ∑ x, v x = 0} ∩ {v | v x₀ = 0} :
        Set (Fin n → ZMod p)) * Nat.card ρ.range * p * p < p ^ (n - 2) * p * p := by
      rw [← hpn2, ← hpn1]
      calc Nat.card (projFix p ρ.range ∩ {v | ∑ x, v x = 0} ∩ {v | v x₀ = 0} :
            Set (Fin n → ZMod p)) * Nat.card ρ.range * p * p
          = Nat.card (projFix p ρ.range ∩ {v | ∑ x, v x = 0} ∩ {v | v x₀ = 0} :
              Set (Fin n → ZMod p)) * p * Nat.card ρ.range * p := by ring
        _ = Nat.card (projFix p ρ.range ∩ {v | ∑ x, v x = 0} : Set (Fin n → ZMod p)) *
              Nat.card ρ.range * p := by rw [hslice']
        _ < p ^ n := hc2
    calc Nat.card (Bs ⊓ Subgroup.centralizer (E : Set G) : Subgroup G) * Nat.card ρ.range
        ≤ Nat.card (projFix p ρ.range ∩ {v | ∑ x, v x = 0} ∩ {v | v x₀ = 0} :
            Set (Fin n → ZMod p)) * Nat.card ρ.range := Nat.mul_le_mul_right _ hCle'
      _ < p ^ (n - 2) := Nat.lt_of_mul_lt_mul_right (Nat.lt_of_mul_lt_mul_right h1)
      _ ≤ Nat.card Bs := hHB
  have hpos : 0 < Nat.card (E ⊓ Subgroup.centralizer (Bs : Set G) : Subgroup G) := Nat.card_pos
  rw [← hE']
  calc Nat.card (Bs ⊓ Subgroup.centralizer (E : Set G) : Subgroup G) *
        (Nat.card ρ.ker * Nat.card ρ.range)
      ≤ Nat.card (Bs ⊓ Subgroup.centralizer (E : Set G) : Subgroup G) *
          (Nat.card (E ⊓ Subgroup.centralizer (Bs : Set G) : Subgroup G) * Nat.card ρ.range) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hkerC)
    _ = Nat.card (Bs ⊓ Subgroup.centralizer (E : Set G) : Subgroup G) * Nat.card ρ.range *
          Nat.card (E ⊓ Subgroup.centralizer (Bs : Set G) : Subgroup G) := by ring
    _ < Nat.card Bs * Nat.card (E ⊓ Subgroup.centralizer (Bs : Set G) : Subgroup G) :=
        Nat.mul_lt_mul_of_pos_right hmain hpos

end Main

end NoOffUO

end CFSG.StandardType
