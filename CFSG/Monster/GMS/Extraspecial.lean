module

public import CFSG.Monster.GMS.Facts.Leech

public section

namespace CFSG.Monster.GMS

open scoped commutatorElement

variable {H : Type*} [Group H]

structure ExtraspecialData (Q : Subgroup H) (w : H) : Prop where
  mem : w ∈ Q
  ne_one : w ≠ 1
  mul_self : w * w = 1
  central : ∀ q ∈ Q, q * w = w * q
  sq : ∀ q ∈ Q, q * q = 1 ∨ q * q = w
  comm : ∀ p ∈ Q, ∀ q ∈ Q, ⁅p, q⁆ = 1 ∨ ⁅p, q⁆ = w

namespace ExtraspecialData

variable {Q : Subgroup H} {w : H}

theorem commutatorElement_mul_left (hQ : ExtraspecialData Q w) {x x' y : H} (hx : x ∈ Q)
    (hx' : x' ∈ Q) (hy : y ∈ Q) : ⁅x * x', y⁆ = ⁅x, y⁆ * ⁅x', y⁆ := by
  have hc : ⁅x', y⁆ = 1 ∨ ⁅x', y⁆ = w := hQ.comm x' hx' y hy
  have hc2 : ⁅x, y⁆ = 1 ∨ ⁅x, y⁆ = w := hQ.comm x hx y hy
  have hxc : x * ⁅x', y⁆ = ⁅x', y⁆ * x := by
    rcases hc with h | h
    · rw [h]; simp
    · rw [h]; exact hQ.central x hx
  have hcc : ⁅x', y⁆ * ⁅x, y⁆ = ⁅x, y⁆ * ⁅x', y⁆ := by
    rcases hc with h | h <;> rcases hc2 with h2 | h2 <;> simp [h, h2]
  calc ⁅x * x', y⁆ = x * ⁅x', y⁆ * y * x⁻¹ * y⁻¹ := by
        simp only [commutatorElement_def]; group
    _ = ⁅x', y⁆ * ⁅x, y⁆ := by rw [hxc]; simp only [commutatorElement_def]; group
    _ = ⁅x, y⁆ * ⁅x', y⁆ := hcc

private def commHom (hQ : ExtraspecialData Q w) {C : Subgroup H} (hC : C ≤ Q) {y : H}
    (hy : y ∈ Q) : C →* H where
  toFun x := ⁅(x : H), y⁆
  map_one' := by simp
  map_mul' x x' := by
    rw [Subgroup.coe_mul]
    exact hQ.commutatorElement_mul_left (hC x.2) (hC x'.2) hy

theorem card_le_two_mul_card_inf_centralizer [Finite H] (hQ : ExtraspecialData Q w)
    {C : Subgroup H} (hC : C ≤ Q) {y : H} (hy : y ∈ Q) :
    Nat.card C ≤ 2 * Nat.card ↥(C ⊓ Subgroup.centralizer ({y} : Set H)) := by
  set f := hQ.commHom hC hy with hf
  have hker : f.ker = (Subgroup.centralizer ({y} : Set H)).subgroupOf C := by
    ext x
    simp only [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff]
    show ⁅(x : H), y⁆ = 1 ↔ (x : H) * y = y * (x : H)
    exact commutatorElement_eq_one_iff_mul_comm
  have hrange : Nat.card f.range ≤ 2 := by
    have hle : f.range ≤ Subgroup.zpowers w := by
      rintro _ ⟨x, rfl⟩
      rcases hQ.comm x (hC x.2) y hy with h | h
      · show ⁅(x : H), y⁆ ∈ _
        rw [h]; exact Subgroup.one_mem _
      · show ⁅(x : H), y⁆ ∈ _
        rw [h]; exact Subgroup.mem_zpowers w
    calc Nat.card f.range ≤ Nat.card (Subgroup.zpowers w) := Subgroup.card_le_of_le hle
      _ = orderOf w := Nat.card_zpowers w
      _ ≤ 2 := Nat.le_of_dvd (by norm_num)
          (orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hQ.mul_self))
  have h1 := Subgroup.relIndex_mul_card (Subgroup.centralizer ({y} : Set H)) C
  have h2 : (Subgroup.centralizer ({y} : Set H)).relIndex C ≤ 2 := by
    rw [Subgroup.relIndex, ← hker, Subgroup.index_ker]
    exact hrange
  rw [inf_comm] at h1
  calc Nat.card C = (Subgroup.centralizer ({y} : Set H)).relIndex C *
        Nat.card ↥(C ⊓ Subgroup.centralizer ({y} : Set H)) := h1.symm
    _ ≤ 2 * Nat.card ↥(C ⊓ Subgroup.centralizer ({y} : Set H)) := Nat.mul_le_mul_right _ h2

theorem exists_mul_self_eq_one [Finite H] (hQ : ExtraspecialData Q w) {C : Subgroup H}
    (hC : C ≤ Q) {U : Subgroup H} (h : 4 * Nat.card U < Nat.card C) :
    ∃ y ∈ C, y ∉ U ∧ y * y = 1 := by
  by_contra hno
  push Not at hno
  have hsq : ∀ y ∈ C, y ∉ U → y * y = w := fun y hy hyU =>
    (hQ.sq y (hC hy)).resolve_left (hno y hy hyU)
  obtain ⟨y1, hy1C, hy1U⟩ : ∃ y1 ∈ C, y1 ∉ U := by
    by_contra hall
    push Not at hall
    have hle : C ≤ U := fun y hy => hall y hy
    have := Subgroup.card_le_of_le hle
    omega
  have hy1w : y1 * y1 = w := hsq y1 hy1C hy1U
  set K := C ⊓ Subgroup.centralizer ({y1} : Set H) with hK
  have hKsub : ∀ y ∈ K, y ∈ U ∨ y1 * y ∈ U := by
    intro y hy
    by_contra hcon
    push Not at hcon
    obtain ⟨hyC, hyc⟩ := Subgroup.mem_inf.mp hy
    have hcomm : y * y1 = y1 * y := Subgroup.mem_centralizer_singleton_iff.mp hyc
    have hyw : y * y = w := hsq y hyC hcon.1
    have hy1yw : (y1 * y) * (y1 * y) = w := hsq _ (C.mul_mem hy1C hyC) hcon.2
    have : (y1 * y) * (y1 * y) = (y1 * y1) * (y * y) := by
      calc (y1 * y) * (y1 * y) = y1 * (y * y1) * y := by group
        _ = y1 * (y1 * y) * y := by rw [hcomm]
        _ = (y1 * y1) * (y * y) := by group
    rw [hy1yw, hy1w, hyw, hQ.mul_self] at this
    exact hQ.ne_one this
  have hK2 : Nat.card C ≤ 2 * Nat.card K := hQ.card_le_two_mul_card_inf_centralizer hC (hC hy1C)
  have hsub : (K : Set H) ⊆ (U : Set H) ∪ ((fun y => y1 * y) ⁻¹' (U : Set H)) := by
    intro y hy
    rcases hKsub y hy with h1 | h1
    · exact Or.inl h1
    · exact Or.inr h1
  have hfin : ((U : Set H) ∪ ((fun y => y1 * y) ⁻¹' (U : Set H))).Finite := Set.toFinite _
  have hKU : Nat.card K ≤ 2 * Nat.card U := by
    have h1 := Set.ncard_le_ncard hsub hfin
    have h2 := Set.ncard_union_le (U : Set H) ((fun y => y1 * y) ⁻¹' (U : Set H))
    have h3 : ((fun y => y1 * y) ⁻¹' (U : Set H)).ncard = (U : Set H).ncard :=
      Set.ncard_preimage_of_injective_subset_range (mul_right_injective y1)
        (by rintro g -; exact ⟨y1⁻¹ * g, by simp⟩)
    have h4 : Nat.card K = (K : Set H).ncard := Nat.card_coe_set_eq (K : Set H)
    have h5 : Nat.card U = (U : Set H).ncard := Nat.card_coe_set_eq (U : Set H)
    omega
  omega

end ExtraspecialData

theorem exists_subgroup_card_two_mul_of_mul_self_eq_one [Finite H] {U : Subgroup H} {y : H}
    (hy2 : y * y = 1) (hyU : y ∉ U) (hc : ∀ u ∈ U, y * u = u * y) :
    ∃ U' : Subgroup H, U ≤ U' ∧ y ∈ U' ∧ Nat.card U' = 2 * Nat.card U ∧
      ∀ g, g ∈ U' ↔ (g ∈ U ∨ y * g ∈ U) := by
  have hyy : ∀ g : H, y * (y * g) = g := fun g => by rw [← mul_assoc, hy2, one_mul]
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy2
  let U' : Subgroup H :=
    { carrier := {g | g ∈ U ∨ y * g ∈ U}
      one_mem' := Or.inl U.one_mem
      mul_mem' := by
        rintro g₁ g₂ (h₁ | h₁) (h₂ | h₂)
        · exact Or.inl (U.mul_mem h₁ h₂)
        · refine Or.inr ?_
          have : y * (g₁ * g₂) = g₁ * (y * g₂) := by
            calc y * (g₁ * g₂) = (y * g₁) * g₂ := by rw [mul_assoc]
              _ = (g₁ * y) * g₂ := by rw [hc g₁ h₁]
              _ = g₁ * (y * g₂) := by rw [mul_assoc]
          rw [this]
          exact U.mul_mem h₁ h₂
        · refine Or.inr ?_
          rw [← mul_assoc]
          exact U.mul_mem h₁ h₂
        · refine Or.inl ?_
          have hg₁ : g₁ = y * (y * g₁) := (hyy g₁).symm
          have hg₂ : g₂ = y * (y * g₂) := (hyy g₂).symm
          have : g₁ * g₂ = (y * g₁) * (y * g₂) := by
            calc g₁ * g₂ = y * (y * g₁) * (y * (y * g₂)) := by rw [← hg₁, ← hg₂]
              _ = (y * (y * g₁)) * y * (y * g₂) := by rw [mul_assoc _ y]
              _ = ((y * g₁) * y) * y * (y * g₂) := by
                  rw [← hc _ h₁, mul_assoc y (y * g₁) y, ← hc _ h₁, ← mul_assoc]
              _ = (y * g₁) * (y * g₂) := by
                  rw [mul_assoc (y * g₁) y y, hy2, mul_one]
          rw [this]
          exact U.mul_mem h₁ h₂
      inv_mem' := by
        rintro g (h | h)
        · exact Or.inl (U.inv_mem h)
        · refine Or.inr ?_
          have hc' := hc _ (U.inv_mem h)
          have hg : g⁻¹ = (y * g)⁻¹ * y := by
            rw [mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]
          have : y * g⁻¹ = (y * g)⁻¹ := by
            calc y * g⁻¹ = y * ((y * g)⁻¹ * y) := by rw [← hg]
              _ = (y * (y * g)⁻¹) * y := by rw [mul_assoc]
              _ = ((y * g)⁻¹ * y) * y := by rw [hc']
              _ = (y * g)⁻¹ := by rw [mul_assoc, hy2, mul_one]
          rw [this]
          exact U.inv_mem h }
  have hmem : ∀ g, g ∈ U' ↔ (g ∈ U ∨ y * g ∈ U) := fun g => Iff.rfl
  refine ⟨U', fun g hg => Or.inl hg, Or.inr (by rw [hy2]; exact U.one_mem), ?_, hmem⟩
  let f : U ⊕ U → U' := Sum.elim (fun u => ⟨(u : H), Or.inl u.2⟩)
    (fun u => ⟨y * (u : H), Or.inr (by rw [hyy]; exact u.2)⟩)
  have hf : Function.Bijective f := by
    constructor
    · rintro (u | u) (v | v) h
      · have h' : (u : H) = (v : H) := congrArg (fun z : U' => (z : H)) h
        exact congrArg Sum.inl (Subtype.ext h')
      · exfalso
        have h' : (u : H) = y * (v : H) := congrArg Subtype.val h
        apply hyU
        have : y = (u : H) * (v : H)⁻¹ := by rw [h']; group
        rw [this]
        exact U.mul_mem u.2 (U.inv_mem v.2)
      · exfalso
        have h' : y * (u : H) = (v : H) := congrArg Subtype.val h
        apply hyU
        have : y = (v : H) * (u : H)⁻¹ := by rw [← h']; group
        rw [this]
        exact U.mul_mem v.2 (U.inv_mem u.2)
      · have h' : y * (u : H) = y * (v : H) := congrArg Subtype.val h
        exact congrArg Sum.inr (Subtype.ext (mul_left_cancel h'))
    · rintro ⟨g, hg | hg⟩
      · exact ⟨Sum.inl ⟨g, hg⟩, rfl⟩
      · exact ⟨Sum.inr ⟨y * g, hg⟩, Subtype.ext (hyy g)⟩
  have hcard : Nat.card U' = Nat.card (U ⊕ U) := (Nat.card_congr (Equiv.ofBijective f hf)).symm
  rw [Nat.card_sum] at hcard
  omega

namespace ExtraspecialData

variable {Q : Subgroup H} {w : H}

theorem exists_elementary_card_eight [Finite H] (hQ : ExtraspecialData Q w) {X : Subgroup H}
    (hX : X ≤ Q) (hcard : 2 ^ 9 ≤ Nat.card X) :
    ∃ E : Subgroup H, E ≤ X ∧ w ∉ E ∧ Nat.card E = 8 ∧ ∀ e ∈ E, e * e = 1 := by
  have key : ∀ k : ℕ, k ≤ 3 → ∃ U C : Subgroup H, U ≤ X ∧ C ≤ X ∧ w ∉ U ∧
      (∀ u ∈ U, u * u = 1) ∧ (∀ c ∈ C, ∀ u ∈ U, c * u = u * c) ∧ Nat.card U = 2 ^ k ∧
      Nat.card X ≤ 2 ^ k * Nat.card C := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨⊥, X, bot_le, le_rfl, ?_, ?_, ?_, ?_, ?_⟩
      · rw [Subgroup.mem_bot]; exact hQ.ne_one
      · intro u hu; rw [Subgroup.mem_bot] at hu; simp [hu]
      · intro c _ u hu; rw [Subgroup.mem_bot] at hu; simp [hu]
      · simp
      · simp
    | succ k ih =>
      intro hk
      obtain ⟨U, C, hUX, hCX, hwU, hU2, hCU, hUcard, hXC⟩ := ih (by omega)
      obtain ⟨U₁, hUU₁, hwU₁, hU₁card, hU₁mem⟩ :=
        exists_subgroup_card_two_mul_of_mul_self_eq_one hQ.mul_self hwU
          (fun u hu => (hQ.central u (hX (hUX hu))).symm)
      have hCU₁ : 4 * Nat.card U₁ < Nat.card C := by
        rw [hU₁card, hUcard]
        have h9 : 2 ^ 9 ≤ 2 ^ k * Nat.card C := hcard.trans hXC
        have hk2 : k ≤ 2 := by omega
        interval_cases k <;> norm_num at h9 ⊢ <;> omega
      obtain ⟨y, hyC, hyU₁, hyy⟩ := hQ.exists_mul_self_eq_one (hCX.trans hX) hCU₁
      have hyU : y ∉ U := fun h => hyU₁ (hUU₁ h)
      have hyQ : y ∈ Q := hX (hCX hyC)
      obtain ⟨U₂, hUU₂, hyU₂, hU₂card, hU₂mem⟩ :=
        exists_subgroup_card_two_mul_of_mul_self_eq_one hyy hyU (fun u hu => hCU y hyC u hu)
      have hyy' : ∀ g : H, y * (y * g) = g := fun g => by rw [← mul_assoc, hyy, one_mul]
      refine ⟨U₂, C ⊓ Subgroup.centralizer ({y} : Set H), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro g hg
        rcases (hU₂mem g).mp hg with h | h
        · exact hUX h
        · rw [← hyy' g]
          exact X.mul_mem (hCX hyC) (hUX h)
      · exact inf_le_left.trans hCX
      · intro h
        rcases (hU₂mem w).mp h with h1 | h1
        · exact hwU h1
        · apply hyU₁
          refine (hU₁mem y).mpr (Or.inr ?_)
          rw [← hQ.central y hyQ]
          exact h1
      · intro g hg
        rcases (hU₂mem g).mp hg with h | h
        · exact hU2 g h
        · obtain ⟨a, ha⟩ : ∃ a, a = y * g := ⟨_, rfl⟩
          rw [← ha] at h
          have hga : g = y * a := by rw [ha, hyy' g]
          have hca : y * a = a * y := hCU y hyC a h
          rw [hga]
          calc y * a * (y * a) = y * (a * y) * a := by group
            _ = y * (y * a) * a := by rw [← hca]
            _ = (y * y) * (a * a) := by group
            _ = 1 := by rw [hyy, hU2 a h, one_mul]
      · intro c hc g hg
        obtain ⟨hcC, hcy⟩ := Subgroup.mem_inf.mp hc
        have hcy' : c * y = y * c := Subgroup.mem_centralizer_singleton_iff.mp hcy
        rcases (hU₂mem g).mp hg with h | h
        · exact hCU c hcC g h
        · have hcg := hCU c hcC _ h
          calc c * g = c * (y * (y * g)) := by rw [hyy' g]
            _ = (c * y) * (y * g) := by rw [mul_assoc]
            _ = y * (c * (y * g)) := by rw [hcy', mul_assoc]
            _ = y * ((y * g) * c) := by rw [hcg]
            _ = (y * (y * g)) * c := (mul_assoc _ _ _).symm
            _ = g * c := by rw [hyy' g]
      · rw [hU₂card, hUcard]; ring
      · calc Nat.card X ≤ 2 ^ k * Nat.card C := hXC
          _ ≤ 2 ^ k * (2 * Nat.card ↥(C ⊓ Subgroup.centralizer ({y} : Set H))) :=
              Nat.mul_le_mul_left _ (hQ.card_le_two_mul_card_inf_centralizer (hCX.trans hX) hyQ)
          _ = 2 ^ (k + 1) * Nat.card ↥(C ⊓ Subgroup.centralizer ({y} : Set H)) := by ring
  obtain ⟨U, C, hUX, -, hwU, hU2, -, hUcard, -⟩ := key 3 le_rfl
  exact ⟨U, hUX, hwU, by rw [hUcard]; norm_num, hU2⟩

theorem exists_elementary_card_sixteen [Finite H] (hQ : ExtraspecialData Q w) {X : Subgroup H}
    (hX : X ≤ Q) (hwX : w ∈ X) (hcard : 2 ^ 9 ≤ Nat.card X) :
    ∃ E : Subgroup H, E ≤ X ∧ w ∈ E ∧ Nat.card E = 16 ∧ ∀ e ∈ E, e * e = 1 := by
  obtain ⟨E, hEX, hwE, hEcard, hE2⟩ := hQ.exists_elementary_card_eight hX hcard
  obtain ⟨E₁, hEE₁, hwE₁, hE₁card, hE₁mem⟩ :=
    exists_subgroup_card_two_mul_of_mul_self_eq_one hQ.mul_self hwE
      (fun u hu => (hQ.central u (hX (hEX hu))).symm)
  refine ⟨E₁, ?_, hwE₁, by rw [hE₁card, hEcard], ?_⟩
  · intro g hg
    rcases (hE₁mem g).mp hg with h | h
    · exact hEX h
    · have : w * (w * g) = g := by rw [← mul_assoc, hQ.mul_self, one_mul]
      rw [← this]
      exact X.mul_mem hwX (hEX h)
  · intro g hg
    rcases (hE₁mem g).mp hg with h | h
    · exact hE2 g h
    · obtain ⟨a, ha⟩ : ∃ a, a = w * g := ⟨_, rfl⟩
      rw [← ha] at h
      have hga : g = w * a := by rw [ha, ← mul_assoc, hQ.mul_self, one_mul]
      have hca : w * a = a * w := (hQ.central a (hX (hEX h))).symm
      rw [hga]
      calc w * a * (w * a) = w * (a * w) * a := by group
        _ = w * (w * a) * a := by rw [← hca]
        _ = (w * w) * (a * a) := by group
        _ = 1 := by rw [hQ.mul_self, hE2 a h, one_mul]

end ExtraspecialData

private theorem prod_range_two_mul_pair {V : Type*} [CommGroup V] (f : ℕ → V) (N : ℕ) :
    ∏ k ∈ Finset.range N, (f (2 * k) * f (2 * k + 1)) = ∏ j ∈ Finset.range (2 * N), f j := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.prod_range_succ, ih, show 2 * (N + 1) = 2 * N + 1 + 1 by ring,
      Finset.prod_range_succ, Finset.prod_range_succ, mul_assoc]

private theorem exists_fixed_of_norm_eq_one {V : Type*} [CommGroup V] (hV : ∀ v : V, v * v = 1)
    (σ τ : MulAut V) {n : ℕ} (hσ : σ ^ (2 * n + 1) = 1) (hτσ : τ * σ * τ⁻¹ = σ⁻¹) {c : V}
    (hN : ∏ i ∈ Finset.range (2 * n + 1), (σ ^ i) c = 1) (hc : τ c = σ⁻¹ c) :
    ∃ b : V, b * (σ b)⁻¹ = c ∧ τ b = b := by
  have hinv : ∀ v : V, v⁻¹ = v := fun v => inv_eq_of_mul_eq_one_right (hV v)
  have hτj : ∀ j : ℕ, j ≤ 2 * n → τ ((σ ^ j) c) = (σ ^ (2 * n - j)) c := by
    intro j hj
    have h1 : τ * σ ^ j * τ⁻¹ = (σ⁻¹) ^ j := by rw [← conj_pow, hτσ]
    have h2 : τ * σ ^ j = (σ⁻¹) ^ j * τ := by
      calc τ * σ ^ j = (τ * σ ^ j * τ⁻¹) * τ := by group
        _ = (σ⁻¹) ^ j * τ := by rw [h1]
    have h3 : (σ⁻¹) ^ (j + 1) = σ ^ (2 * n - j) := by
      have : σ ^ (2 * n - j) * σ ^ (j + 1) = 1 := by
        rw [← pow_add, show 2 * n - j + (j + 1) = 2 * n + 1 by omega]; exact hσ
      rw [inv_pow]; exact (eq_inv_of_mul_eq_one_left this).symm
    calc τ ((σ ^ j) c) = (τ * σ ^ j) c := rfl
      _ = ((σ⁻¹) ^ j * τ) c := by rw [h2]
      _ = ((σ⁻¹) ^ j) (τ c) := rfl
      _ = ((σ⁻¹) ^ j) (σ⁻¹ c) := by rw [hc]
      _ = ((σ⁻¹) ^ (j + 1)) c := by rw [pow_succ]; rfl
      _ = (σ ^ (2 * n - j)) c := by rw [h3]
  refine ⟨∏ k ∈ Finset.range (n + 1), (σ ^ (2 * k)) c, ?_, ?_⟩
  · rw [hinv]
    have hσb : σ (∏ k ∈ Finset.range (n + 1), (σ ^ (2 * k)) c) =
        ∏ k ∈ Finset.range (n + 1), (σ ^ (2 * k + 1)) c := by
      rw [map_prod]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [pow_succ']; rfl
    rw [hσb, ← Finset.prod_mul_distrib]
    have := prod_range_two_mul_pair (fun j => (σ ^ j) c) (n + 1)
    rw [this, show 2 * (n + 1) = 2 * n + 1 + 1 by ring, Finset.prod_range_succ, hN, one_mul, hσ]
    rfl
  · rw [map_prod]
    have h1 : ∏ k ∈ Finset.range (n + 1), τ ((σ ^ (2 * k)) c) =
        ∏ k ∈ Finset.range (n + 1), (σ ^ (2 * (n + 1 - 1 - k))) c := by
      refine Finset.prod_congr rfl fun k hk => ?_
      rw [Finset.mem_range] at hk
      rw [hτj (2 * k) (by omega)]
      congr 2
      omega
    rw [h1]
    exact Finset.prod_range_reflect (fun k => (σ ^ (2 * k)) c) (n + 1)

namespace ExtraspecialData

variable {Q : Subgroup H} {w : H}

private def wSub (hQ : ExtraspecialData Q w) : Subgroup Q where
  carrier := {q | q = 1 ∨ (q : H) = w}
  one_mem' := Or.inl rfl
  mul_mem' := by
    rintro a b (ha | ha) (hb | hb)
    · left; rw [ha, hb, one_mul]
    · right; rw [ha, one_mul]; exact hb
    · right; rw [hb, mul_one]; exact ha
    · left
      apply Subtype.ext
      show (a : H) * b = 1
      rw [ha, hb]; exact hQ.mul_self
  inv_mem' := by
    rintro a (ha | ha)
    · left; rw [ha, inv_one]
    · right
      show ((a⁻¹ : Q) : H) = w
      rw [Subgroup.coe_inv, ha]
      exact inv_eq_of_mul_eq_one_right hQ.mul_self

private instance wSub_normal (hQ : ExtraspecialData Q w) : hQ.wSub.Normal where
  conj_mem := by
    rintro n (hn | hn) g
    · left; rw [hn]; simp
    · right
      show (g : H) * (n : H) * (g : H)⁻¹ = w
      rw [hn, mul_inv_eq_iff_eq_mul]
      exact hQ.central g g.2

private theorem bar_mul_comm (hQ : ExtraspecialData Q w) (a b : ↥Q ⧸ hQ.wSub) : a * b = b * a := by
  induction a using QuotientGroup.induction_on with
  | H p =>
  induction b using QuotientGroup.induction_on with
  | H r =>
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
  have hc := hQ.comm (r : H)⁻¹ (Q.inv_mem r.2) (p : H)⁻¹ (Q.inv_mem p.2)
  have e : (((p * r)⁻¹ * (r * p) : Q) : H) = ⁅(r : H)⁻¹, (p : H)⁻¹⁆ := by
    simp [commutatorElement_def, mul_assoc]
  rcases hc with h | h
  · left; apply Subtype.ext; rw [e, h]; rfl
  · right; rw [e, h]

private theorem bar_mul_self (hQ : ExtraspecialData Q w) (v : ↥Q ⧸ hQ.wSub) : v * v = 1 := by
  induction v using QuotientGroup.induction_on with
  | H q =>
    rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff]
    rcases hQ.sq q q.2 with h | h
    · left; exact Subtype.ext h
    · right; exact h

private def conjQ {M : Subgroup H} (hMn : ∀ g ∈ M, ∀ q ∈ Q, g * q * g⁻¹ ∈ Q) (g : M) :
    MulAut Q where
  toFun q := ⟨(g : H) * q * (g : H)⁻¹, hMn g g.2 q q.2⟩
  invFun q := ⟨(g : H)⁻¹ * q * (g : H), by simpa using hMn (g : H)⁻¹ (M.inv_mem g.2) q q.2⟩
  left_inv q := Subtype.ext (by simp [mul_assoc])
  right_inv q := Subtype.ext (by simp [mul_assoc])
  map_mul' a b := Subtype.ext (by simp [mul_assoc])

private theorem coe_conjQ {M : Subgroup H} (hMn : ∀ g ∈ M, ∀ q ∈ Q, g * q * g⁻¹ ∈ Q) (g : M)
    (q : Q) : ((conjQ hMn g q : Q) : H) = (g : H) * q * (g : H)⁻¹ :=
  rfl

private theorem map_wSub_conjQ (hQ : ExtraspecialData Q w) {M : Subgroup H}
    (hMn : ∀ g ∈ M, ∀ q ∈ Q, g * q * g⁻¹ ∈ Q) (hMw : ∀ g ∈ M, g * w = w * g) (g : M) :
    hQ.wSub.map (conjQ hMn g).toMonoidHom = hQ.wSub := by
  have hfix : ∀ q ∈ hQ.wSub, conjQ hMn g q = q := by
    rintro q (hq | hq)
    · rw [hq]; exact map_one _
    · apply Subtype.ext
      rw [coe_conjQ, hq, hMw g g.2, mul_inv_cancel_right]
  ext q
  constructor
  · rintro ⟨n, hn, rfl⟩
    have := hfix n hn
    show conjQ hMn g n ∈ hQ.wSub
    rw [this]; exact hn
  · intro hq
    exact ⟨q, hq, hfix q hq⟩

private noncomputable def barAut (hQ : ExtraspecialData Q w) {M : Subgroup H}
    (hMn : ∀ g ∈ M, ∀ q ∈ Q, g * q * g⁻¹ ∈ Q) (hMw : ∀ g ∈ M, g * w = w * g) (g : M) :
    MulAut (↥Q ⧸ hQ.wSub) :=
  QuotientGroup.congr hQ.wSub hQ.wSub (conjQ hMn g) (map_wSub_conjQ hQ hMn hMw g)

private theorem barAut_mk (hQ : ExtraspecialData Q w) {M : Subgroup H}
    (hMn : ∀ g ∈ M, ∀ q ∈ Q, g * q * g⁻¹ ∈ Q) (hMw : ∀ g ∈ M, g * w = w * g) (g : M) (q : Q) :
    barAut hQ hMn hMw g (QuotientGroup.mk q) = QuotientGroup.mk (conjQ hMn g q) :=
  rfl

private noncomputable def barHom (hQ : ExtraspecialData Q w) {M : Subgroup H}
    (hMn : ∀ g ∈ M, ∀ q ∈ Q, g * q * g⁻¹ ∈ Q) (hMw : ∀ g ∈ M, g * w = w * g) :
    M →* MulAut (↥Q ⧸ hQ.wSub) where
  toFun := barAut hQ hMn hMw
  map_one' := by
    refine MulEquiv.ext fun v => ?_
    induction v using QuotientGroup.induction_on with
    | H q =>
      rw [barAut_mk]
      show QuotientGroup.mk _ = QuotientGroup.mk q
      congr 1
      exact Subtype.ext (by simp [coe_conjQ])
  map_mul' a b := by
    refine MulEquiv.ext fun v => ?_
    induction v using QuotientGroup.induction_on with
    | H q =>
      show barAut hQ hMn hMw (a * b) (QuotientGroup.mk q) =
        barAut hQ hMn hMw a (barAut hQ hMn hMw b (QuotientGroup.mk q))
      rw [barAut_mk, barAut_mk, barAut_mk]
      congr 1
      exact Subtype.ext (by simp [coe_conjQ, mul_assoc])

theorem exists_conj_of_inverting (hQ : ExtraspecialData Q w) {M : Subgroup H}
    (hMn : ∀ g ∈ M, ∀ q ∈ Q, g * q * g⁻¹ ∈ Q) (hMw : ∀ g ∈ M, g * w = w * g)
    {x d u : H} (hx : x ∈ M) (hd : d ∈ M) (hu : u ∈ M) {m : ℕ} (hm : Odd m) (hdm : d ^ m = 1)
    (hum : u ^ m = 1) (hx2 : x * x = 1) (hxd : x * d * x = d⁻¹) (hxu : x * u * x = u⁻¹)
    (hdu : d⁻¹ * u ∈ Q) :
    ∃ q ∈ Q, q * d * q⁻¹ = u ∧ (q * x * q⁻¹ = x ∨ q * x * q⁻¹ = x * w) := by
  obtain ⟨n, rfl⟩ := hm
  let _ : CommGroup (↥Q ⧸ hQ.wSub) := { (inferInstance : Group (↥Q ⧸ hQ.wSub)) with
    mul_comm := bar_mul_comm hQ }
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  have hcQ : u * d⁻¹ ∈ Q := by
    have := hMn d hd _ hdu
    simpa [mul_assoc] using this
  let dM : M := ⟨d, hd⟩
  let xM : M := ⟨x, hx⟩
  let σ : MulAut (↥Q ⧸ hQ.wSub) := barHom hQ hMn hMw dM
  let τ : MulAut (↥Q ⧸ hQ.wSub) := barHom hQ hMn hMw xM
  let c : Q := ⟨u * d⁻¹, hcQ⟩
  have hσ : σ ^ (2 * n + 1) = 1 := by
    show barHom hQ hMn hMw dM ^ (2 * n + 1) = 1
    rw [← map_pow, show dM ^ (2 * n + 1) = 1 from Subtype.ext (by simpa using hdm), map_one]
  have hτσ : τ * σ * τ⁻¹ = σ⁻¹ := by
    show barHom hQ hMn hMw xM * barHom hQ hMn hMw dM * (barHom hQ hMn hMw xM)⁻¹ =
      (barHom hQ hMn hMw dM)⁻¹
    rw [← map_inv, ← map_mul, ← map_mul, ← map_inv]
    congr 1
    exact Subtype.ext (show x * d * x⁻¹ = d⁻¹ by rw [hxinv]; exact hxd)
  have hprod : ∀ k : ℕ, ∃ r : Q, (r : H) = u ^ k * (d ^ k)⁻¹ ∧
      ∏ i ∈ Finset.range k, (σ ^ i) (QuotientGroup.mk c) = QuotientGroup.mk r := by
    intro k
    induction k with
    | zero => exact ⟨1, by simp, by simp⟩
    | succ k ih =>
      obtain ⟨r, hr, hrk⟩ := ih
      have hσk : (σ ^ k) (QuotientGroup.mk c) = QuotientGroup.mk (conjQ hMn (dM ^ k) c) := by
        have : σ ^ k = barHom hQ hMn hMw (dM ^ k) := (map_pow _ _ _).symm
        rw [this]; rfl
      refine ⟨r * conjQ hMn (dM ^ k) c, ?_, ?_⟩
      · rw [Subgroup.coe_mul, hr, coe_conjQ]
        simp only [Subgroup.coe_pow, c, dM]
        rw [pow_succ, pow_succ, mul_inv_rev]
        group
      · rw [Finset.prod_range_succ, hrk, hσk, QuotientGroup.mk_mul]
  have hN : ∏ i ∈ Finset.range (2 * n + 1), (σ ^ i) (QuotientGroup.mk c) = 1 := by
    obtain ⟨r, hr, hrk⟩ := hprod (2 * n + 1)
    have hr1 : r = 1 := Subtype.ext (by rw [hr, hum, hdm]; simp)
    rw [hrk, hr1]; rfl
  have hxd' : x * d⁻¹ * x = d := by
    calc x * d⁻¹ * x = (x * d * x)⁻¹ := by rw [mul_inv_rev, mul_inv_rev, hxinv]; group
      _ = d := by rw [hxd, inv_inv]
  have hc : τ (QuotientGroup.mk c) = σ⁻¹ (QuotientGroup.mk c) := by
    have h1 : τ (QuotientGroup.mk c) = QuotientGroup.mk (conjQ hMn xM c) := rfl
    have h2 : σ⁻¹ (QuotientGroup.mk c) = QuotientGroup.mk (conjQ hMn dM⁻¹ c) := by
      show (barHom hQ hMn hMw dM)⁻¹ (QuotientGroup.mk c) = _
      rw [← map_inv]; rfl
    rw [h1, h2, QuotientGroup.eq]
    have he : (⟨d⁻¹ * u, hdu⟩ : Q) * ⟨d⁻¹ * u, hdu⟩ = (conjQ hMn xM c)⁻¹ * conjQ hMn dM⁻¹ c := by
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, coe_conjQ, coe_conjQ]
      simp only [c, xM, dM, Subgroup.coe_inv]
      have h3 : x * (u * d⁻¹) * x⁻¹ = u⁻¹ * d := by
        calc x * (u * d⁻¹) * x⁻¹ = (x * u * x) * (x * d⁻¹ * x) := by
              have h4 : (x * u * x) * (x * d⁻¹ * x) = x * u * (x * x) * d⁻¹ * x := by group
              rw [h4, hx2, hxinv]; group
          _ = u⁻¹ * d := by rw [hxu, hxd']
      rw [h3]
      group
    rw [← he]
    rcases hQ.sq (d⁻¹ * u) hdu with h | h
    · left; exact Subtype.ext h
    · right; exact h
  obtain ⟨b, hb1, hb2⟩ := exists_fixed_of_norm_eq_one (bar_mul_self hQ) σ τ hσ hτσ hN hc
  obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective b
  have hA : σ (QuotientGroup.mk q) = QuotientGroup.mk (conjQ hMn dM q) := rfl
  have hB : τ (QuotientGroup.mk q) = QuotientGroup.mk (conjQ hMn xM q) := rfl
  rw [hA, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, QuotientGroup.eq] at hb1
  rw [hB, QuotientGroup.eq] at hb2
  have hqQ : (q : H) ∈ Q := q.2
  have hwd : w * d = d * w := (hMw d hd).symm
  have hwx : w * x = x * w := (hMw x hx).symm
  have hwq : w * (q : H) = (q : H) * w := (hQ.central q hqQ).symm
  have hww : w * w = 1 := hQ.mul_self
  obtain ⟨z, hz, hz'⟩ : ∃ z : H, (z = 1 ∨ z = w) ∧
      ((q : H) * ((d * (q : H) * d⁻¹)⁻¹))⁻¹ * (u * d⁻¹) = z := by
    rcases hb1 with h | h
    · exact ⟨1, Or.inl rfl, congrArg Subtype.val h⟩
    · exact ⟨w, Or.inr rfl, h⟩
  obtain ⟨z', hz2, hz2'⟩ : ∃ z' : H, (z' = 1 ∨ z' = w) ∧
      (x * (q : H) * x⁻¹)⁻¹ * (q : H) = z' := by
    rcases hb2 with h | h
    · exact ⟨1, Or.inl rfl, congrArg Subtype.val h⟩
    · exact ⟨w, Or.inr rfl, h⟩
  generalize (q : H) = qq at hz' hz2' hqQ hwq
  have hzz : z * z = 1 := by rcases hz with h | h <;> simp [h, hww]
  have hzd : z * d = d * z := by rcases hz with h | h <;> simp [h, hwd]
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hzz
  have hP : qq * d * qq⁻¹ = u * z := by
    have e1 : d * ((qq * d * qq⁻¹)⁻¹ * u) * d⁻¹ = z := by rw [← hz']; group
    have e2 : (qq * d * qq⁻¹)⁻¹ * u = z := by
      calc (qq * d * qq⁻¹)⁻¹ * u = d⁻¹ * (d * ((qq * d * qq⁻¹)⁻¹ * u) * d⁻¹) * d := by group
        _ = d⁻¹ * z * d := by rw [e1]
        _ = z := by rw [mul_assoc, hzd, inv_mul_cancel_left]
    calc qq * d * qq⁻¹ = u * ((qq * d * qq⁻¹)⁻¹ * u)⁻¹ := by group
      _ = u * z := by rw [e2, hzinv]
  have hz2z : z' * z' = 1 := by rcases hz2 with h | h <;> simp [h, hww]
  have hz2q : z' * qq = qq * z' := by rcases hz2 with h | h <;> simp [h, hwq]
  have hz2x : z' * x = x * z' := by rcases hz2 with h | h <;> simp [h, hwx]
  have hz2inv : z'⁻¹ = z' := inv_eq_of_mul_eq_one_right hz2z
  have hz2'' : qq⁻¹ * (x * qq * x⁻¹) = z' := by
    have : qq⁻¹ * (x * qq * x⁻¹) = z'⁻¹ := by rw [← hz2']; group
    rw [this, hz2inv]
  have hX : qq * x * qq⁻¹ = x * z' := by
    have e : qq⁻¹ * x * qq = z' * x := by
      calc qq⁻¹ * x * qq = (qq⁻¹ * (x * qq * x⁻¹)) * x := by group
        _ = z' * x := by rw [hz2'']
    have e2 : x = z' * (qq * x * qq⁻¹) := by
      calc x = qq * (qq⁻¹ * x * qq) * qq⁻¹ := by group
        _ = qq * (z' * x) * qq⁻¹ := by rw [e]
        _ = (qq * z') * x * qq⁻¹ := by group
        _ = (z' * qq) * x * qq⁻¹ := by rw [← hz2q]
        _ = z' * (qq * x * qq⁻¹) := by group
    calc qq * x * qq⁻¹ = z'⁻¹ * x := (inv_mul_eq_iff_eq_mul.mpr e2).symm
      _ = x * z' := by rw [hz2inv, hz2x]
  refine ⟨qq, hqQ, ?_, ?_⟩
  · rcases hz with h | h
    · rw [h, mul_one] at hP; exact hP
    · exfalso
      rw [h] at hP
      have h1 : (qq * d * qq⁻¹) ^ (2 * n + 1) = 1 := by
        rw [conj_pow, hdm]; group
      rw [hP, (Commute.mul_pow (hMw u hu : u * w = w * u)), hum, one_mul] at h1
      have h2 : w ^ (2 * n + 1) = w := by
        rw [pow_succ, pow_mul, pow_two, hww, one_pow, one_mul]
      rw [h2] at h1
      exact hQ.ne_one h1
  · rcases hz2 with h | h
    · left; rw [h, mul_one] at hX; exact hX
    · right; rw [h] at hX; exact hX

end ExtraspecialData

theorem inv_pow_mul_pow_mem_of_conj_mem {Q M : Subgroup H} (hMn : ∀ g ∈ M, ∀ q ∈ Q, g * q * g⁻¹ ∈ Q)
    {g h : H} (hg : g ∈ M) (hgh : g⁻¹ * h ∈ Q) (k : ℕ) : (g ^ k)⁻¹ * h ^ k ∈ Q := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h1 := hMn g⁻¹ (M.inv_mem hg) _ ih
    have h2 := Q.mul_mem h1 hgh
    convert h2 using 1
    rw [pow_succ, pow_succ, mul_inv_rev]
    group

section LeechQ

variable {G : Type*} [Group G]

theorem GMSLeechCentralizer.card_leechQ {w : G} (h : GMSLeechCentralizer w) :
    Nat.card (leechQ w) = 2 ^ 25 := by
  unfold leechQ
  rw [Subgroup.card_map_of_injective (Subgroup.centralizer ({w} : Set G)).subtype_injective]
  exact h.2.2.1

theorem GMSLeechCentralizer.extraspecialData [Finite G] {w : G} (h : GMSLeechCentralizer w) :
    ExtraspecialData (leechQ w) w := by
  obtain ⟨hw2, ⟨hp, hcomm, hfrat, hcard⟩, -, -, hcent⟩ := h
  have hww : w * w = 1 := by rw [← sq, ← hw2, pow_orderOf_eq_one]
  have hw1 : w ≠ 1 := by
    rintro rfl
    simp at hw2
  set C := Subgroup.centralizer ({w} : Set G) with hC
  set P := CFSG.pCore 2 C with hP
  let w' : C := ⟨w, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  have hw'P : w' ∈ P := by
    apply hcent
    rw [Subgroup.mem_centralizer_iff]
    intro p _
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp p.2
  let w'' : P := ⟨w', hw'P⟩
  have hw''c : w'' ∈ Subgroup.center P := by
    rw [Subgroup.mem_center_iff]
    intro p
    apply Subtype.ext
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp p.1.2
  have hw''1 : w'' ≠ 1 := by
    intro h1
    apply hw1
    exact congrArg (fun z : P => ((z : C) : G)) h1
  have hcenter : ∀ c : P, c ∈ Subgroup.center P → c = 1 ∨ c = w'' := by
    intro c hc
    by_cases hc1 : c = 1
    · exact Or.inl hc1
    · right
      obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : Subgroup.center P)).1 hcard
      have h1 : (⟨c, hc⟩ : Subgroup.center P) = y := hy _ (fun h => hc1 (congrArg Subtype.val h))
      have h2 : (⟨w'', hw''c⟩ : Subgroup.center P) = y :=
        hy _ (fun h => hw''1 (congrArg Subtype.val h))
      exact congrArg Subtype.val (h1.trans h2.symm)
  have : Fact (IsPGroup 2 P) := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmap : ∀ q ∈ leechQ w, ∃ q'' : P, ((q'' : C) : G) = q := by
    intro q hq
    obtain ⟨q', hq', rfl⟩ := Subgroup.mem_map.mp hq
    exact ⟨⟨q', hq'⟩, rfl⟩
  refine ⟨⟨w', hw'P, rfl⟩, hw1, hww, ?_, ?_, ?_⟩
  · intro q hq
    have := Subgroup.map_subtype_le _ hq
    exact Subgroup.mem_centralizer_singleton_iff.mp this
  · intro q hq
    obtain ⟨q'', rfl⟩ := hmap q hq
    have hsq : q'' ^ 2 ∈ Subgroup.center P := by
      rw [← hfrat]
      exact CFSG.pth_power_mem_frattini_of_isPGroup (p := 2) q''
    rcases hcenter _ hsq with h1 | h1
    · left
      have := congrArg (fun z : P => ((z : C) : G)) h1
      simpa [pow_two] using this
    · right
      have := congrArg (fun z : P => ((z : C) : G)) h1
      simpa [pow_two] using this
  · intro p hp r hr
    obtain ⟨p'', rfl⟩ := hmap p hp
    obtain ⟨r'', rfl⟩ := hmap r hr
    have hc : ⁅p'', r''⁆ ∈ Subgroup.center P := by
      rw [← hcomm, _root_.commutator_def]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
    rcases hcenter _ hc with h1 | h1
    · left
      have := congrArg (fun z : P => ((z : C) : G)) h1
      simpa [commutatorElement_def] using this
    · right
      have := congrArg (fun z : P => ((z : C) : G)) h1
      simpa [commutatorElement_def] using this

end LeechQ

end CFSG.Monster.GMS
