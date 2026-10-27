module

public import CFSG.Quasithin.Background.E6TwentyThreePA
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltAct
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentAlt

public section

namespace CFSG.Quasithin.E6

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1
open Equiv Equiv.Perm

section Alternating

variable {n : ℕ}

theorem two_mul_card_alt_inf_centralizer {π : Perm (Fin n)} (h2 : π * π = 1) {k : ℕ}
    (hk : 1 ≤ k) (hc : π.cycleType = Multiset.replicate k 2) :
    2 * Nat.card ↥(alternatingGroup (Fin n) ⊓ Subgroup.centralizer ({π} : Set (Perm (Fin n)))) =
      Nat.factorial (n - 2 * k) * 2 ^ k * Nat.factorial k := by
  set C := Subgroup.centralizer ({π} : Set (Perm (Fin n))) with hC
  have h1 : π ≠ 1 := by
    rintro rfl
    rw [Equiv.Perm.cycleType_one] at hc
    have := congrArg Multiset.card hc
    simp only [Multiset.card_zero, Multiset.card_replicate] at this
    omega
  obtain ⟨i, hi⟩ : ∃ i, π i ≠ i := by
    by_contra hall
    push Not at hall
    exact h1 (Equiv.ext hall)
  have hππ : π (π i) = i := by
    have := congrArg (fun f : Perm (Fin n) => f i) h2
    simpa using this
  have hτC : swap i (π i) ∈ C := by
    rw [hC, Subgroup.mem_centralizer_singleton_iff]
    have h3 := Equiv.swap_apply_apply π i (π i)
    rw [hππ, Equiv.swap_comm] at h3
    calc swap i (π i) * π = π * swap i (π i) * π⁻¹ * π := by rw [← h3]
      _ = π * swap i (π i) := by group
  have hτA : swap i (π i) ∉ alternatingGroup (Fin n) := by
    rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_swap (Ne.symm hi)]
    decide
  have hidx : (alternatingGroup (Fin n)).relIndex C = 2 := by
    have hdvd := Subgroup.relIndex_dvd_index_of_normal (alternatingGroup (Fin n)) C
    have hn2 : Nontrivial (Fin n) := ⟨⟨i, π i, Ne.symm hi⟩⟩
    rw [alternatingGroup.index_eq_two] at hdvd
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
    · exact absurd ((Subgroup.relIndex_eq_one).1 h hτC) hτA
    · exact h
  have hmul := Subgroup.relIndex_mul_card (H := alternatingGroup (Fin n)) (K := C)
  rw [hidx] at hmul
  rw [hmul, hC, Id2519.card_centralizer_involution hk hc]

end Alternating

section Action

variable {G : Type} [Group G] {Y : Subgroup G} {n : ℕ}

theorem card_inf_centralizer_eq_actPerm (ψ : ↥Y ≃* alternatingGroup (Fin n))
    (hn : n = 5 ∨ 7 ≤ n) (x : ↥(Subgroup.normalizer (Y : Set G))) :
    Nat.card ↥(Y ⊓ Subgroup.centralizer ({(x : G)} : Set G)) =
      Nat.card ↥(alternatingGroup (Fin n) ⊓
        Subgroup.centralizer ({CFSG.ComponentClassification.RankTwoAlt.actPerm ψ hn x} :
          Set (Perm (Fin n)))) := by
  set σ := CFSG.ComponentClassification.RankTwoAlt.actPerm ψ hn x with hσ
  have key : ∀ y : ↥Y, (y : G) ∈ Subgroup.centralizer ({(x : G)} : Set G) ↔
      (ψ y : Perm (Fin n)) ∈ Subgroup.centralizer ({σ} : Set (Perm (Fin n))) := by
    intro y
    have hs := CFSG.ComponentClassification.RankTwoAlt.actPerm_spec ψ hn x y
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro hyx
      have hxy : (⟨(x : G) * y * (x : G)⁻¹,
          (Subgroup.mem_normalizer_iff.mp x.2 y).mp y.2⟩ : ↥Y) = y :=
        Subtype.ext (show (x : G) * y * (x : G)⁻¹ = y by rw [← hyx]; group)
      rw [hxy] at hs
      calc (ψ y : Perm (Fin n)) * σ = (σ * (ψ y : Perm (Fin n)) * σ⁻¹) * σ := by rw [← hs]
        _ = σ * ψ y := by group
    · intro hyσ
      have h1 : σ * (ψ y : Perm (Fin n)) * σ⁻¹ = ψ y := by rw [← hyσ]; group
      rw [h1] at hs
      have h2 := congrArg Subtype.val (ψ.injective (Subtype.ext hs))
      calc (y : G) * x = ((x : G) * y * (x : G)⁻¹) * x := by
            rw [show ((x : G) * y * (x : G)⁻¹) = (y : G) from h2]
        _ = x * y := by group
  refine Nat.card_congr
    { toFun := fun y => ⟨ψ ⟨y, y.2.1⟩, (ψ ⟨y, y.2.1⟩).2, (key ⟨y, y.2.1⟩).1 y.2.2⟩
      invFun := fun w => ⟨ψ.symm ⟨w, w.2.1⟩, (ψ.symm ⟨w, w.2.1⟩).2, (key _).2 (by
        rw [MulEquiv.apply_symm_apply]; exact w.2.2)⟩
      left_inv := fun y => by simp
      right_inv := fun w => by simp }

end Action

namespace InspHyp

variable {G : Type} [Group G] [Finite G] {Y E X : Subgroup G} {a z : G}

private theorem le_factorization_two {m k : ℕ} (hm : m ≠ 0) (h : 2 ^ k ∣ m) :
    k ≤ m.factorization 2 :=
  (Nat.prime_two.pow_dvd_iff_le_factorization hm).1 h

theorem false_of_patA8 (h : InspHyp Y E X a z) (hA8 : Id2519.PatA8 Y X a)
    (h8 : (E ⊓ Subgroup.centralizer (Y : Set G)).relIndex E = 8) : False := by
  obtain ⟨-, ψ, -, -, -, -⟩ := hA8
  have hn : (8 : ℕ) = 5 ∨ 7 ≤ 8 := Or.inr (by norm_num)
  set N := Subgroup.normalizer (Y : Set G) with hN
  set σ := CFSG.ComponentClassification.RankTwoAlt.actPerm ψ hn with hσdef
  have hker : σ.ker = (Subgroup.centralizer (Y : Set G)).subgroupOf N := by
    ext n
    rw [MonoidHom.mem_ker, CFSG.ComponentClassification.RankTwoAlt.actPerm_eq_one_iff,
      Subgroup.mem_subgroupOf]
  set Ebar := (E.subgroupOf N).map σ with hEbar
  have hcard : Nat.card ↥Ebar = 8 := by
    refine Eq.trans ?_ h8
    rw [Subgroup.inf_relIndex_left, ← Subgroup.relIndex_subgroupOf h.norm, ← hker,
      Subgroup.relIndex_ker]
  have hA : 4 ≤ Nat.card ↥(alternatingGroup (Fin 8) ⊓ Ebar) := by
    have hdvd := Subgroup.relIndex_dvd_index_of_normal (alternatingGroup (Fin 8)) Ebar
    rw [alternatingGroup.index_eq_two] at hdvd
    have hmul := Subgroup.relIndex_mul_card (H := alternatingGroup (Fin 8)) (K := Ebar)
    rw [hcard] at hmul
    have hle := Nat.le_of_dvd (by norm_num) hdvd
    have hpos : 0 < (alternatingGroup (Fin 8)).relIndex Ebar :=
      Nat.pos_of_ne_zero fun h0 => by rw [h0, zero_mul] at hmul; exact absurd hmul (by norm_num)
    interval_cases hr : (alternatingGroup (Fin 8)).relIndex Ebar <;> omega
  obtain ⟨w, hw, hw1⟩ : ∃ w ∈ alternatingGroup (Fin 8) ⊓ Ebar, w ≠ 1 := by
    by_contra hall
    push Not at hall
    have hbot : alternatingGroup (Fin 8) ⊓ Ebar = ⊥ := (Subgroup.eq_bot_iff_forall _).2 hall
    rw [hbot, Subgroup.card_bot] at hA
    omega
  obtain ⟨e, heE, hew⟩ := hw.2
  have heE' : (e : G) ∈ E := heE
  have hσe1 : σ e ≠ 1 := by rw [hew]; exact hw1
  have hσeA : σ e ∈ alternatingGroup (Fin 8) := by rw [hew]; exact hw.1
  have hσe2 : σ e * σ e = 1 := by
    rw [← map_mul]
    have : e * e = 1 := Subtype.ext (h.mul_self_eq_one heE')
    rw [this, map_one]
  obtain ⟨k, hk1, hck⟩ := Id2519.involution_cycleType hσe2 hσe1
  have hk4 := Id2519.two_mul_le_of_cycleType hck
  have hsign := Id2519.sign_involution hck
  rw [Equiv.Perm.mem_alternatingGroup.mp hσeA] at hsign
  have hke : k = 2 ∨ k = 4 := by
    have hk' : k ≤ 4 := by omega
    interval_cases k
    · exact absurd hsign (by decide)
    · exact Or.inl rfl
    · exact absurd hsign (by decide)
    · exact Or.inr rfl
  have hCe := two_mul_card_alt_inf_centralizer hσe2 hk1 hck
  rw [← card_inf_centralizer_eq_actPerm ψ hn e] at hCe
  have heY : ¬ Y ≤ Subgroup.centralizer ({(e : G)} : Set G) := by
    intro hle
    apply hσe1
    rw [CFSG.ComponentClassification.RankTwoAlt.actPerm_eq_one_iff, Subgroup.mem_centralizer_iff]
    intro y hy
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hy)
  have hfle := h.factorization_le heE' heY
  set aN : ↥N := ⟨a, h.norm h.mem⟩ with haN
  have hσa2 : σ aN * σ aN = 1 := by
    rw [← map_mul]
    have : aN * aN = 1 := Subtype.ext (h.mul_self_eq_one h.mem)
    rw [this, map_one]
  have hσa1 : σ aN ≠ 1 := by
    intro h1
    rw [CFSG.ComponentClassification.RankTwoAlt.actPerm_eq_one_iff] at h1
    exact h.not_cent fun y hy => Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp h1 y hy)
  obtain ⟨j, hj1, hcj⟩ := Id2519.involution_cycleType hσa2 hσa1
  have hj4 := Id2519.two_mul_le_of_cycleType hcj
  have hCa := two_mul_card_alt_inf_centralizer hσa2 hj1 hcj
  rw [← card_inf_centralizer_eq_actPerm ψ hn aN] at hCa
  change 2 * Nat.card ↥(Y ⊓ Subgroup.centralizer ({a} : Set G)) = _ at hCa
  have h360 : 360 ∣ Nat.card ↥(Y ⊓ Subgroup.centralizer ({a} : Set G)) := by
    rw [← h.card_X]
    exact Subgroup.card_dvd_of_le h.comp.1
  have hCa720 : Nat.card ↥(Y ⊓ Subgroup.centralizer ({a} : Set G)) = 720 := by
    have hj' : j ≤ 4 := by omega
    generalize Nat.card ↥(Y ⊓ Subgroup.centralizer ({a} : Set G)) = c at hCa h360 ⊢
    interval_cases j <;> norm_num [Nat.factorial] at hCa <;> omega
  have ha4 : (Nat.card ↥(Y ⊓ Subgroup.centralizer ({a} : Set G))).factorization 2 < 5 := by
    rw [hCa720]
    by_contra hge
    push Not at hge
    have := (Nat.prime_two.pow_dvd_iff_le_factorization (by norm_num : (720 : ℕ) ≠ 0)).2 hge
    omega
  have he5 : 5 ≤ (Nat.card ↥(Y ⊓ Subgroup.centralizer ({(e : G)} : Set G))).factorization 2 := by
    apply le_factorization_two Nat.card_pos.ne'
    rcases hke with rfl | rfl
    · simp [Nat.factorial] at hCe
      exact ⟨3, by norm_num; omega⟩
    · simp [Nat.factorial] at hCe
      exact ⟨6, by norm_num; omega⟩
  omega

end InspHyp

end CFSG.Quasithin.E6
