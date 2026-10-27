module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.A6FactsModel4

public section

namespace CFSG.QuasithinUnique.A6Facts

open Equiv

@[expose] def noRank4Check : Bool :=
  Core.p0Lit.all fun a => a == Core.cid || !(Core.cmul a a == Core.cid) ||
    Core.p0Lit.all fun b => b == Core.cid || b == a || !(Core.cmul b b == Core.cid) ||
      !(Core.cmul a b == Core.cmul b a) ||
      Core.p0Lit.all fun c => c == Core.cid || c == a || c == b || c == Core.cmul a b ||
        !(Core.cmul c c == Core.cid) || !(Core.cmul a c == Core.cmul c a) ||
        !(Core.cmul b c == Core.cmul c b) ||
        Core.p0Lit.all fun d =>
          !(Core.cmul d d == Core.cid) || !(Core.cmul a d == Core.cmul d a) ||
          !(Core.cmul b d == Core.cmul d b) || !(Core.cmul c d == Core.cmul d c) ||
          [Core.cid, a, b, Core.cmul a b, c, Core.cmul a c, Core.cmul b c,
            Core.cmul (Core.cmul a b) c].contains d

theorem noRank4 : noRank4Check = true := by decide +kernel

theorem noRank4_prop : ∀ a ∈ Core.p0Lit, ∀ b ∈ Core.p0Lit, ∀ c ∈ Core.p0Lit, ∀ d ∈ Core.p0Lit,
    a = Core.cid ∨ ¬ Core.cmul a a = Core.cid ∨ b = Core.cid ∨ b = a ∨ ¬ Core.cmul b b = Core.cid ∨
    ¬ Core.cmul a b = Core.cmul b a ∨ c = Core.cid ∨ c = a ∨ c = b ∨ c = Core.cmul a b ∨
    ¬ Core.cmul c c = Core.cid ∨ ¬ Core.cmul a c = Core.cmul c a ∨
    ¬ Core.cmul b c = Core.cmul c b ∨ ¬ Core.cmul d d = Core.cid ∨
    ¬ Core.cmul a d = Core.cmul d a ∨ ¬ Core.cmul b d = Core.cmul d b ∨
    ¬ Core.cmul c d = Core.cmul d c ∨
    d ∈ [Core.cid, a, b, Core.cmul a b, c, Core.cmul a c, Core.cmul b c,
      Core.cmul (Core.cmul a b) c] := by
  have h := noRank4
  unfold noRank4Check at h
  simp only [List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq,
    beq_eq_false_iff_ne, ne_eq, List.contains_iff_mem] at h
  intro a ha b hb c hc d hd
  by_contra hcon
  simp only [not_or, not_not] at hcon
  obtain ⟨ha1, ha2, hb1, hba, hb2, hab, hc1, hca, hcb, hcab, hc2, hac, hbc, hd2, had, hbd, hcd,
    hdl⟩ := hcon
  rcases h a ha with (h1 | h1) | h1
  · exact ha1 h1
  · exact h1 ha2
  rcases h1 b hb with (((h2 | h2) | h2) | h2) | h2
  · exact hb1 h2
  · exact hba h2
  · exact h2 hb2
  · exact h2 hab
  rcases h2 c hc with ((((((h3 | h3) | h3) | h3) | h3) | h3) | h3) | h3
  · exact hc1 h3
  · exact hca h3
  · exact hcb h3
  · exact hcab h3
  · exact h3 hc2
  · exact h3 hac
  · exact h3 hbc
  rcases h3 d hd with (((h4 | h4) | h4) | h4) | h4
  · exact h4 hd2
  · exact h4 had
  · exact h4 hbd
  · exact h4 hcd
  · exact hdl h4

theorem no_rank4 {a b c d : P10} (ha : a ∈ P0) (hb : b ∈ P0) (hc : c ∈ P0) (hd : d ∈ P0)
    (ha1 : a ≠ 1) (ha2 : a * a = 1) (hb1 : b ≠ 1) (hba : b ≠ a) (hb2 : b * b = 1)
    (hab : a * b = b * a) (hc1 : c ≠ 1) (hca : c ≠ a) (hcb : c ≠ b) (hcab : c ≠ a * b)
    (hc2 : c * c = 1) (hac : a * c = c * a) (hbc : b * c = c * b) (hd2 : d * d = 1)
    (had : a * d = d * a) (hbd : b * d = d * b) (hcd : c * d = d * c) :
    d = 1 ∨ d = a ∨ d = b ∨ d = a * b ∨ d = c ∨ d = a * c ∨ d = b * c ∨ d = a * b * c := by
  have h := noRank4_prop (code a) ((mem_P0_iff a).1 ha) (code b) ((mem_P0_iff b).1 hb)
    (code c) ((mem_P0_iff c).1 hc) (code d) ((mem_P0_iff d).1 hd)
  have hne : ∀ {x y : P10}, x ≠ y → ¬ code x = code y := fun hxy h => hxy (code_injective h)
  have hsq : ∀ {x : P10}, x * x = 1 → Core.cmul (code x) (code x) = Core.cid := by
    intro x hx
    rw [← code_mul, hx, code_one]
  have hcm : ∀ {x y : P10}, x * y = y * x →
      Core.cmul (code x) (code y) = Core.cmul (code y) (code x) :=
    fun h => code_comm_iff.mp h
  have h1c : ¬ code a = Core.cid := by
    rw [← code_one]; exact hne ha1
  have hb1c : ¬ code b = Core.cid := by
    rw [← code_one]; exact hne hb1
  have hc1c : ¬ code c = Core.cid := by
    rw [← code_one]; exact hne hc1
  have hcabc : ¬ code c = Core.cmul (code a) (code b) := by
    rw [← code_mul]; exact hne hcab
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact absurd h h1c
  · exact absurd (hsq ha2) h
  · exact absurd h hb1c
  · exact absurd h (hne hba)
  · exact absurd (hsq hb2) h
  · exact absurd (hcm hab) h
  · exact absurd h hc1c
  · exact absurd h (hne hca)
  · exact absurd h (hne hcb)
  · exact absurd h hcabc
  · exact absurd (hsq hc2) h
  · exact absurd (hcm hac) h
  · exact absurd (hcm hbc) h
  · exact absurd (hsq hd2) h
  · exact absurd (hcm had) h
  · exact absurd (hcm hbd) h
  · exact absurd (hcm hcd) h
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    have e1 : code (a * b) = Core.cmul (code a) (code b) := code_mul a b
    have e2 : code (a * c) = Core.cmul (code a) (code c) := code_mul a c
    have e3 : code (b * c) = Core.cmul (code b) (code c) := code_mul b c
    have e4 : code (a * b * c) = Core.cmul (Core.cmul (code a) (code b)) (code c) := by
      rw [code_mul, e1]
    rcases h with h | h | h | h | h | h | h | h
    · exact Or.inl (code_injective (h.trans code_one.symm))
    · exact Or.inr (Or.inl (code_injective h))
    · exact Or.inr (Or.inr (Or.inl (code_injective h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (code_injective (h.trans e1.symm)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (code_injective h)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (code_injective (h.trans e2.symm)))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        (code_injective (h.trans e3.symm))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (code_injective (h.trans e4.symm))))))))

theorem exists_not_mem_finset (Y : Subgroup P10) (F : Finset P10) (h : F.card < Nat.card Y) :
    ∃ y ∈ Y, y ∉ F := by
  by_contra hcon
  have hsub : (Y : Set P10) ⊆ (F : Set P10) := fun y hy =>
    Classical.byContradiction fun hn => hcon ⟨y, hy, hn⟩
  have h1 := Set.ncard_le_ncard hsub (Finset.finite_toSet F)
  rw [Set.ncard_coe_finset] at h1
  have h2 : (Y : Set P10).ncard = Nat.card Y := (Nat.card_coe_set_eq (Y : Set P10)).symm
  omega

theorem exists_not_mem_list (Y : Subgroup P10) (l : List P10) (h : l.length < Nat.card Y) :
    ∃ y ∈ Y, y ∉ l := by
  obtain ⟨y, hy, hn⟩ := exists_not_mem_finset Y l.toFinset
    (lt_of_le_of_lt (List.toFinset_card_le l) h)
  exact ⟨y, hy, fun hm => hn (List.mem_toFinset.mpr hm)⟩

theorem comm_of_sq {Y : Subgroup P10} (hsq : ∀ y ∈ Y, y * y = 1) {x y : P10} (hx : x ∈ Y)
    (hy : y ∈ Y) : x * y = y * x := by
  have h1 := hsq (x * y) (Y.mul_mem hx hy)
  have h2 : (x * y)⁻¹ = x * y := inv_eq_of_mul_eq_one_right h1
  have hx' : x⁻¹ = x := inv_eq_of_mul_eq_one_right (hsq x hx)
  have hy' : y⁻¹ = y := inv_eq_of_mul_eq_one_right (hsq y hy)
  rw [mul_inv_rev, hx', hy'] at h2
  exact h2.symm

theorem card_le_eight_of_exp_two_P0 {Y : Subgroup P10} (hY : Y ≤ P0) (hsq : ∀ y ∈ Y, y * y = 1) :
    Nat.card Y ≤ 8 := by
  by_contra hlt
  replace hlt : 8 < Nat.card Y := not_le.mp hlt
  obtain ⟨a, haY, ha⟩ := exists_not_mem_list Y [1] (by simp; omega)
  obtain ⟨b, hbY, hb⟩ := exists_not_mem_list Y [1, a] (by simp; omega)
  obtain ⟨c, hcY, hc⟩ := exists_not_mem_list Y [1, a, b, a * b] (by simp; omega)
  obtain ⟨d, hdY, hd⟩ := exists_not_mem_list Y [1, a, b, a * b, c, a * c, b * c, a * b * c]
    (by simp; omega)
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at ha hb hc hd
  have key := no_rank4 (hY haY) (hY hbY) (hY hcY) (hY hdY) ha (hsq a haY) hb.1 hb.2 (hsq b hbY)
    (comm_of_sq hsq haY hbY) hc.1 hc.2.1 hc.2.2.1 hc.2.2.2 (hsq c hcY) (comm_of_sq hsq haY hcY)
    (comm_of_sq hsq hbY hcY) (hsq d hdY) (comm_of_sq hsq haY hdY) (comm_of_sq hsq hbY hdY)
    (comm_of_sq hsq hcY hdY)
  rcases key with h | h | h | h | h | h | h | h
  · exact hd.1 h
  · exact hd.2.1 h
  · exact hd.2.2.1 h
  · exact hd.2.2.2.1 h
  · exact hd.2.2.2.2.1 h
  · exact hd.2.2.2.2.2.1 h
  · exact hd.2.2.2.2.2.2.1 h
  · exact hd.2.2.2.2.2.2.2 h

theorem card_le_eight_of_exp_two (X : Subgroup ↥A6Models.autA6) (hsq : ∀ x ∈ X, x * x = 1) :
    Nat.card X ≤ 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hX : IsPGroup 2 X := fun x => ⟨1, by
    show (x : ↥X) ^ (2 ^ 1) = 1
    rw [pow_one, pow_two]
    exact Subtype.ext (hsq x x.2)⟩
  have hfac : (1440 : ℕ).factorization 2 = 5 := by
    rw [Nat.factorization_def _ Nat.prime_two]
    decide +kernel
  have hcard : Nat.card (P0.subgroupOf A6Models.autA6) =
      2 ^ (Nat.card ↥A6Models.autA6).factorization 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe P0_le_autA6).toEquiv, card_P0, card_autA6,
      hfac]
    norm_num
  let P0S : Sylow 2 ↥A6Models.autA6 := Sylow.ofCard (P0.subgroupOf A6Models.autA6) hcard
  obtain ⟨Q, hXQ⟩ := hX.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥A6Models.autA6 P0S Q
  have hmem : ∀ x ∈ X, g⁻¹ * x * g ∈ P0.subgroupOf A6Models.autA6 := by
    intro x hx
    have h1 : x ∈ (Q : Subgroup ↥A6Models.autA6) := hXQ hx
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at h1
    obtain ⟨s, hs, hsx⟩ := h1
    have : s = g⁻¹ * x * g := by
      rw [← hsx]
      simp only [MulAut.smul_def, MulAut.conj_apply]
      group
    rw [← this]
    exact hs
  let φ : ↥A6Models.autA6 →* P10 :=
    A6Models.autA6.subtype.comp (MulAut.conj g⁻¹).toMonoidHom
  have hφ : Function.Injective φ := by
    intro x y h
    have h' : (MulAut.conj g⁻¹ x : ↥A6Models.autA6) = MulAut.conj g⁻¹ y := Subtype.ext h
    exact (MulAut.conj g⁻¹).injective h'
  have hφx : ∀ x : ↥A6Models.autA6, φ x = ((g⁻¹ * x * g : ↥A6Models.autA6) : P10) := by
    intro x
    simp [φ]
  have hle : X.map φ ≤ P0 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [hφx]
    exact (Subgroup.mem_subgroupOf.mp (hmem x hx))
  have hsq' : ∀ y ∈ X.map φ, y * y = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_mul]
    have : x * x = 1 := hsq x hx
    rw [this, map_one]
  calc Nat.card X = Nat.card (X.map φ) := (Subgroup.card_map_of_injective hφ).symm
    _ ≤ 8 := card_le_eight_of_exp_two_P0 hle hsq'

end CFSG.QuasithinUnique.A6Facts
