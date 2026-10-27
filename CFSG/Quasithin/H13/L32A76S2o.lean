module

public import CFSG.Quasithin.H13.L32A76S2e

public section

namespace CFSG.Quasithin.H13.L32A.S2.E8

open CFSG.Open CFSG.Quasithin

variable {G : Type*} [Group G] {A : Subgroup G}

omit [Group G] in
theorem mem_zpowers_of_sq {X : Type*} [Group X] {v x : X} (hv : v * v = 1) :
    x ∈ Subgroup.zpowers v ↔ x = 1 ∨ x = v := by
  constructor
  · intro hx
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have h2 : v ^ (2 : ℤ) = 1 := by rw [zpow_two, hv]
    rw [zpow_eq_zpow_emod n h2]
    rcases Int.emod_two_eq_zero_or_one n with h | h
    · left
      rw [h, zpow_zero]
    · right
      rw [h, zpow_one]
  · rintro (h | h) <;> rw [h]
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers v

theorem eq_top_of_transitive (hA : IsElemAbelian 2 A) (h8 : Nat.card A = 8)
    {P : Subgroup (MulAut ↥A)} {v : ↥A} (hv : v ≠ 1)
    (hT : ∀ x : ↥A, x ≠ 1 → x ≠ v →
      ∃ α ∈ P, (∀ a, α a * a⁻¹ = 1 ∨ α a * a⁻¹ = v) ∧ α x = x * v)
    {ρ : MulAut ↥A} (hρ : ρ ∈ P) (hρv : ρ v = v) (hρ3 : ρ ^ 3 = 1)
    (hρf : ∀ a : ↥A, a ≠ 1 → a ≠ v → ρ a ≠ a ∧ ρ a ≠ a * v)
    {β : MulAut ↥A} (hβ : β ∈ P) (hβv : β v ≠ v) : P = ⊤ := by
  classical
  have hsq : ∀ a : ↥A, a * a = 1 := fun a => Subtype.ext (by
    have := hA.2 a a.2
    simpa [sq] using this)
  have hcomm : ∀ a b : ↥A, a * b = b * a := fun a b => Subtype.ext (by
    have := hA.1.is_comm.comm a b
    exact congrArg Subtype.val this)
  have hvv : v * v = 1 := hsq v
  have hρρρ : ∀ a : ↥A, ρ (ρ (ρ a)) = a := fun a => by
    have := congrArg (fun f : MulAut ↥A => f a) hρ3
    simpa [pow_succ, MulAut.mul_apply] using this
  set u := β v with hudef
  have hu1 : u ≠ 1 := fun h => hv (β.injective (h.trans (map_one β).symm))
  have huv : u ≠ v := hβv
  have hρne1 : ∀ a : ↥A, a ≠ 1 → ρ a ≠ 1 := fun a ha h =>
    ha (ρ.injective (h.trans (map_one ρ).symm))
  have hρnev : ∀ a : ↥A, a ≠ v → ρ a ≠ v := fun a ha h => ha (ρ.injective (h.trans hρv.symm))
  have h1 := hρf u hu1 huv
  have hρu1 := hρne1 u hu1
  have hρuv := hρnev u huv
  have h2 := hρf (ρ u) hρu1 hρuv
  have hρρu1 := hρne1 _ hρu1
  have hρρuv := hρnev _ hρuv
  have h3 : ρ (ρ u) ≠ u := fun h => h1.1 (by
    have e := hρρρ u
    rw [h] at e
    exact e)
  have h4 : ρ (ρ u) ≠ u * v := fun h => h1.2 (by
    have e := hρρρ u
    rw [h, map_mul, hρv] at e
    calc ρ u = ρ u * v * v := by rw [mul_assoc, hvv, mul_one]
      _ = u * v := by rw [e])
  have hfinA : Finite ↥A := Nat.finite_of_card_ne_zero (by rw [h8]; norm_num)
  have hzn : (Subgroup.zpowers v).Normal := ⟨fun n hn g => by
    rw [hcomm g n, mul_inv_cancel_right]
    exact hn⟩
  set Q := ↥A ⧸ Subgroup.zpowers v
  have hfinQ : Finite Q :=
    Finite.of_surjective _ (QuotientGroup.mk'_surjective (Subgroup.zpowers v))
  have : Fintype Q := Fintype.ofFinite Q
  have hne : ∀ x y : ↥A, y ≠ x → y ≠ x * v →
      (QuotientGroup.mk x : Q) ≠ QuotientGroup.mk y := by
    intro x y hxy hxyv h
    rw [QuotientGroup.eq, mem_zpowers_of_sq hvv] at h
    rcases h with h | h
    · exact hxy (by rw [← mul_inv_cancel_left x y, h, mul_one])
    · exact hxyv (by rw [← mul_inv_cancel_left x y, h])
  have hcardQ : Nat.card Q = 4 := by
    have hz : Nat.card (Subgroup.zpowers v) = 2 := by
      rw [Nat.card_zpowers]
      exact orderOf_eq_prime (by rw [sq, hvv]) hv
    have := Subgroup.card_mul_index (Subgroup.zpowers v)
    rw [hz, h8] at this
    rw [← Subgroup.index_eq_card]
    omega
  have hcover : ∀ a : ↥A, a ≠ 1 → a = v ∨ a = u ∨ a = u * v ∨ a = ρ u ∨ a = ρ u * v ∨
      a = ρ (ρ u) ∨ a = ρ (ρ u) * v := by
    intro a ha
    let s : Finset Q := {QuotientGroup.mk 1, QuotientGroup.mk u, QuotientGroup.mk (ρ u),
      QuotientGroup.mk (ρ (ρ u))}
    have hsc : (QuotientGroup.mk (ρ u) : Q) ≠ QuotientGroup.mk (ρ (ρ u)) := hne _ _ h2.1 h2.2
    have hsb : (QuotientGroup.mk u : Q) ∉
        ({QuotientGroup.mk (ρ u), QuotientGroup.mk (ρ (ρ u))} : Finset Q) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hne _ _ h1.1 h1.2, hne _ _ h3 h4⟩
    have hsa : (QuotientGroup.mk 1 : Q) ∉ ({QuotientGroup.mk u, QuotientGroup.mk (ρ u),
        QuotientGroup.mk (ρ (ρ u))} : Finset Q) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      refine ⟨hne _ _ hu1 (by rwa [one_mul]), hne _ _ hρu1 (by rwa [one_mul]),
        hne _ _ hρρu1 (by rwa [one_mul])⟩
    have hs : s.card = 4 := by
      rw [Finset.card_insert_of_notMem hsa, Finset.card_insert_of_notMem hsb, Finset.card_pair hsc]
    have huniv : s = Finset.univ :=
      Finset.eq_univ_of_card s (by rw [hs, ← Nat.card_eq_fintype_card, hcardQ])
    have hmem : (QuotientGroup.mk a : Q) ∈ s := huniv ▸ Finset.mem_univ _
    have key : ∀ r : ↥A, (QuotientGroup.mk a : Q) = QuotientGroup.mk r → a = r ∨ a = r * v := by
      intro r h
      rw [eq_comm, QuotientGroup.eq, mem_zpowers_of_sq hvv] at h
      rcases h with h | h
      · left
        rw [← mul_inv_cancel_left r a, h, mul_one]
      · right
        rw [← mul_inv_cancel_left r a, h]
    simp only [s, Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h | h | h
    · rcases key 1 h with h' | h'
      · exact absurd h' ha
      · left; rw [h', one_mul]
    · rcases key u h with h' | h' <;> simp [h']
    · rcases key (ρ u) h with h' | h' <;> simp [h']
    · rcases key (ρ (ρ u)) h with h' | h' <;> simp [h']
  have horb : ∀ a : ↥A, a ≠ 1 → a ∈ MulAction.orbit P v := by
    have hx : ∀ x : ↥A, x ∈ MulAction.orbit P v → x ≠ 1 → x ≠ v →
        x * v ∈ MulAction.orbit P v := by
      intro x hx hx1 hxv
      obtain ⟨α, hαP, -, hαx⟩ := hT x hx1 hxv
      obtain ⟨g, hg⟩ := hx
      have hg' : g • v = x := hg
      refine ⟨⟨α, hαP⟩ * g, ?_⟩
      show (⟨α, hαP⟩ * g) • v = x * v
      rw [mul_smul, hg']
      exact hαx
    have hρo : ∀ x : ↥A, x ∈ MulAction.orbit P v → ρ x ∈ MulAction.orbit P v := by
      rintro x ⟨g, hg⟩
      have hg' : g • v = x := hg
      refine ⟨⟨ρ, hρ⟩ * g, ?_⟩
      show (⟨ρ, hρ⟩ * g) • v = ρ x
      rw [mul_smul, hg']
      rfl
    have hu : u ∈ MulAction.orbit P v := ⟨⟨β, hβ⟩, rfl⟩
    have hρu := hρo _ hu
    have hρρu := hρo _ hρu
    intro a ha
    rcases hcover a ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact MulAction.mem_orbit_self _
    · exact hu
    · exact hx _ hu hu1 huv
    · exact hρu
    · exact hx _ hρu hρu1 hρuv
    · exact hρρu
    · exact hx _ hρρu hρρu1 hρρuv
  have horbeq : MulAction.orbit P v = {a | a ≠ 1} := by
    ext a
    refine ⟨fun ⟨g, hg⟩ => ?_, horb a⟩
    rw [← hg]
    show (g : MulAut ↥A) v ≠ 1
    intro h
    exact hv ((g : MulAut ↥A).injective (h.trans (map_one _).symm))
  have h7 : 7 ∣ Nat.card P := by
    have : Finite ↥A := Nat.finite_of_card_ne_zero (by rw [h8]; norm_num)
    have hcard : (MulAction.orbit P v).ncard = 7 := by
      have hs : ({a | a ≠ 1} : Set ↥A) = ({1} : Set ↥A)ᶜ := by
        ext a
        simp
      have h := Set.ncard_add_ncard_compl ({1} : Set ↥A)
      rw [Set.ncard_singleton, h8] at h
      rw [horbeq, hs]
      omega
    rw [← hcard, ← MulAction.index_stabilizer]
    exact Subgroup.index_dvd_card _
  have h3P : 3 ∣ Nat.card P := by
    have hρ1 : ρ ≠ 1 := fun h => h1.1 (by rw [h]; rfl)
    have ho : orderOf (⟨ρ, hρ⟩ : ↥P) = 3 := by
      have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
      exact orderOf_eq_prime (Subtype.ext (by simpa using hρ3))
        (fun h => hρ1 (congrArg Subtype.val h))
    exact ho ▸ orderOf_dvd_natCard _
  have h2P : 2 ∣ Nat.card P := by
    obtain ⟨α, hαP, hαt, hαu⟩ := hT u hu1 huv
    have hαv : α v = v := by
      rcases hαt v with h | h
      · exact mul_inv_eq_one.mp h
      · exfalso
        have : α v = 1 := calc α v = α v * v⁻¹ * v := (inv_mul_cancel_right _ _).symm
          _ = v * v := by rw [h]
          _ = 1 := hvv
        exact hv (α.injective (this.trans (map_one α).symm))
    have hα2 : α ^ 2 = 1 := by
      refine MulEquiv.ext fun a => ?_
      rw [sq, MulAut.mul_apply, MulAut.one_apply]
      rcases hαt a with h | h
      · rw [mul_inv_eq_one.mp h, mul_inv_eq_one.mp h]
      · have e : α a = a * v := by rw [← h, hcomm (α a) a⁻¹, mul_inv_cancel_left]
        rw [e, map_mul, e, hαv, mul_assoc, hvv, mul_one]
    have hα1 : α ≠ 1 := fun h => by
      rw [h, MulAut.one_apply] at hαu
      exact hv (by
        have := congrArg (u⁻¹ * ·) hαu
        simpa using this.symm)
    have ho : orderOf (⟨α, hαP⟩ : ↥P) = 2 := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      exact orderOf_eq_prime (Subtype.ext (by simpa using hα2))
        (fun h => hα1 (congrArg Subtype.val h))
    exact ho ▸ orderOf_dvd_natCard _
  have hsimp := isSimpleGroup_mulAut hA h8
  have hcard := card_mulAut hA h8
  have hidx : P.index ∣ 4 := by
    have h42 : 42 ∣ Nat.card P := by
      have := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 6 7)
        (Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 2 3) h2P h3P) h7
      simpa using this
    have hmul := Subgroup.card_mul_index P
    rw [hcard] at hmul
    obtain ⟨k, hk⟩ := h42
    rw [hk] at hmul
    exact ⟨k, by nlinarith⟩
  have hfin : P.FiniteIndex := ⟨by
    intro h
    rw [h] at hidx
    norm_num at hidx⟩
  have hcore := Subgroup.index_normalCore_dvd_factorial_index (H := P)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal P.normalCore with h | h
  · exfalso
    rw [h, Subgroup.index_bot, hcard] at hcore
    have hle : P.index ≤ 4 := Nat.le_of_dvd (by norm_num) hidx
    have : (P.index).factorial ∣ 24 := (Nat.factorial_dvd_factorial hle)
    have := Nat.dvd_trans hcore this
    norm_num at this
  · exact eq_top_iff.mpr (h ▸ Subgroup.normalCore_le P)

end CFSG.Quasithin.H13.L32A.S2.E8

end
