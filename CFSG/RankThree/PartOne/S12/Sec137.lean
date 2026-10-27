module

public import CFSG.RankThree.PartOne.S12.Sec138Local
public import CFSG.RankThree.PartOne.S12.LinAlg
public import CFSG.RankThree.PartOne.S12.TerminalWeylDet

public section

namespace CFSG.RankThree.PartOne

open CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

@[expose] def KF134Pair : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec12Hyp G p A c L E → Sec12Facts G p A c L E → Sec13Facts G p A c L E →
    ¬ Outcome152Five p E A (lieGenerated p E) →
    (E ≠ A ∨ (E = A ∧ ∀ J : Subgroup G, J ∈ sectionTenZeroStar p A → IsLThreeTypeAt p J)) →
    ∀ t ∈ reflectionSet p E, ∀ s ∈ reflectionSet p E, t * s ≠ s * t →
      ∃ I ∈ thetaCompZeroStarE p E, t ∈ torusImage E I ∧ s ∈ torusImage E I

@[expose] def Node137Any : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec12Hyp G p A c L E → Sec12Facts G p A c L E → Sec13Facts G p A c L E →
    ¬ Outcome152Five p E A (lieGenerated p E) → E ≠ A → ThreeTranspD p E

namespace Sec137

open Equiv

theorem involution_four : ∀ σ : Perm (Fin 4), σ * σ = 1 → σ = 1 ∨ (∃ a b, a ≠ b ∧ σ = swap a b) ∨
    ∃ a b c d, a ≠ b ∧ c ≠ d ∧ σ = swap a b * swap c d := by
  decide +kernel

theorem involution_five : ∀ σ : Perm (Fin 5), σ * σ = 1 → σ = 1 ∨ (∃ a b, a ≠ b ∧ σ = swap a b) ∨
    ∃ a b c d, a ≠ b ∧ c ≠ d ∧ σ = swap a b * swap c d := by
  decide +kernel

theorem swap_mul_four : ∀ a b c d : Fin 4, a ≠ b → c ≠ d →
    (swap a b * swap c d) ^ 1 = 1 ∨ (swap a b * swap c d) ^ 2 = 1 ∨
      (swap a b * swap c d) ^ 3 = 1 := by
  decide +kernel

theorem swap_mul_five : ∀ a b c d : Fin 5, a ≠ b → c ≠ d →
    (swap a b * swap c d) ^ 1 = 1 ∨ (swap a b * swap c d) ^ 2 = 1 ∨
      (swap a b * swap c d) ^ 3 = 1 := by
  decide +kernel

theorem orderOf_swap_mul_le {n : ℕ} (hn : n = 4 ∨ n = 5) {a b c d : Fin n} (hab : a ≠ b)
    (hcd : c ≠ d) : orderOf (swap a b * swap c d) ≤ 3 := by
  have h : (swap a b * swap c d) ^ 1 = 1 ∨ (swap a b * swap c d) ^ 2 = 1 ∨
      (swap a b * swap c d) ^ 3 = 1 := by
    rcases hn with rfl | rfl
    · exact swap_mul_four a b c d hab hcd
    · exact swap_mul_five a b c d hab hcd
  rcases h with h | h | h
  · exact (orderOf_le_of_pow_eq_one (by norm_num) h).trans (by norm_num)
  · exact (orderOf_le_of_pow_eq_one (by norm_num) h).trans (by norm_num)
  · exact orderOf_le_of_pow_eq_one (by norm_num) h

theorem isSwap_of_ne_one {K : Type*} [CommGroup K] {n : ℕ} (hn : n = 4 ∨ n = 5)
    (χ : Perm (Fin n) →* K) {σ : Perm (Fin n)} (hσ : σ * σ = 1) (hχ : χ σ ≠ 1) :
    ∃ a b : Fin n, a ≠ b ∧ σ = swap a b := by
  have hcases : σ = 1 ∨ (∃ a b, a ≠ b ∧ σ = swap a b) ∨
      ∃ a b c d, a ≠ b ∧ c ≠ d ∧ σ = swap a b * swap c d := by
    rcases hn with rfl | rfl
    · exact involution_four σ hσ
    · exact involution_five σ hσ
  rcases hcases with h1 | hsw | ⟨a, b, c, d, hab, hcd, hprod⟩
  · exact absurd (by rw [h1, map_one]) hχ
  · exact hsw
  · exfalso
    apply hχ
    obtain ⟨g, hg⟩ := isConj_iff.mp (Perm.isConj_swap hab hcd)
    have hconj : χ (swap c d) = χ (swap a b) := by
      rw [← hg, map_mul, map_mul, map_inv, mul_comm (χ g), mul_assoc, mul_inv_cancel, mul_one]
    have hsq : χ (swap a b) * χ (swap a b) = 1 := by
      rw [← map_mul, Equiv.swap_mul_self, map_one]
    rw [hprod, map_mul, hconj, hsq]

section Det

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {p : ℕ} [Fact p.Prime] {G : Type} [Group G]

omit [Group G] in
theorem two_ne_zero (hp2 : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro h
  have h' : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).1 (by exact_mod_cast h)
  exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).1 h')

theorem det_reflection (hp2 : p ≠ 2) {E : Subgroup G} {m : ℕ}
    (f : Multiplicative (Fin m → ZMod p) ≃* E) {φ : MulAut E} (hφ : IsAutReflection p E φ) :
    LinearEquiv.det (LinAlg.coordHom f φ) = -1 := by
  obtain ⟨hord, hrk⟩ := (LinAlg.isAutReflection_iff f φ).1 hφ
  refine TerminalDet.det_neg_one_of_rank_one (LinAlg.coordHom f φ) ?_ (two_ne_zero hp2) hrk
  have h := pow_orderOf_eq_one (LinAlg.coordHom f φ)
  rw [hord, pow_two] at h
  exact h

theorem isSwap_of_reflection (hp2 : p ≠ 2) {E : Subgroup G} {m : ℕ}
    (f : Multiplicative (Fin m → ZMod p) ≃* E) (Γ : Subgroup (MulAut E)) {n : ℕ}
    (hn : n = 4 ∨ n = 5) (ψ : Γ ≃* Perm (Fin n)) {t : MulAut E} (htΓ : t ∈ Γ)
    (ht : IsAutReflection p E t) : ∃ a b : Fin n, a ≠ b ∧ ψ ⟨t, htΓ⟩ = swap a b := by
  let χ : Γ →* (ZMod p)ˣ := (LinearEquiv.det).comp ((LinAlg.coordHom f).comp Γ.subtype)
  let χ' : Perm (Fin n) →* (ZMod p)ˣ := χ.comp ψ.symm.toMonoidHom
  have hmul : t * t = 1 := RefFacts.mul_self_eq_one ht
  have hσ : ψ ⟨t, htΓ⟩ * ψ ⟨t, htΓ⟩ = 1 := by
    rw [← map_mul]
    have h : (⟨t, htΓ⟩ * ⟨t, htΓ⟩ : Γ) = 1 := Subtype.ext hmul
    rw [h, map_one]
  have hfact : Fact (2 < p) := ⟨by have := (Fact.out : p.Prime).two_le; omega⟩
  have hχ : χ' (ψ ⟨t, htΓ⟩) ≠ 1 := by
    have h1 : χ' (ψ ⟨t, htΓ⟩) = LinearEquiv.det (LinAlg.coordHom f t) := by
      simp [χ', χ]
    rw [h1, det_reflection hp2 f ht]
    intro h
    have h' := congrArg (fun u : (ZMod p)ˣ => (u : ZMod p)) h
    exact ZMod.neg_one_ne_one (by simpa using h')
  exact isSwap_of_ne_one hn χ' hσ hχ

end Det

end Sec137

theorem node137any_of_pair (hpair : KF134Pair) (h136 : Node136)
    (hSchreier : SchreierFor InCatalog)
    (hTwoAction : TwoActionInputs) (h106 : SectionTenMaximalMovingThetaComponentsQuasisimple)
    (h11 : Sec11One) (h122 : Node122) (h122b : Node122b) (h123 : Node123) (h124 : Node124)
    (h125 : Node125) (h126 : Node126) (h127 : Node127) (h128 : Node128) (h129 : Node129) :
    Node137Any := by
  intro G _ _ p A c L E h hF12 hF13 hT hEA s hs t ht
  have hpf : Fact p.Prime := ⟨h.prime⟩
  have hp2 : p ≠ 2 := by
    have := h.three_lt
    omega
  by_cases hcomm : s * t = t * s
  · have hs2 : s * s = 1 := RefFacts.mul_self_eq_one hs.1
    have ht2 : t * t = 1 := RefFacts.mul_self_eq_one ht.1
    have h2 : (s * t) ^ 2 = 1 := by
      rw [Commute.mul_pow hcomm, pow_two s, hs2, pow_two t, ht2, one_mul]
    exact (orderOf_le_of_pow_eq_one (by norm_num) h2).trans (by norm_num)
  · obtain ⟨I, hI, hsI, htI⟩ := hpair G p A c L E h hF12 hF13 hT (Or.inl hEA) s hs t ht hcomm
    obtain ⟨B, c', hB, hc'B, hc'1, h', hF'⟩ := hF13.reinstantiate I hI
    have hT' : ¬ Outcome152Five p E B (lieGenerated p E) := by
      rintro ⟨f, h1, h2, h3, h4, h5, -, h7⟩
      exact hT ⟨f, h1, h2, h3, h4, h5, hEA, h7⟩
    have hF13' : Sec13Facts G p B c' I E :=
      Sec13Facts.of_nodes hSchreier hTwoAction h106 h11 h122 h122b h123 h124 h125 h126 h127 h128
        h129 h' hT'
    obtain ⟨-, r, -, -, -, -, hr8, hr9⟩ := hF12.three
    have hr9' : 9 ≤ r := by
      by_contra hlt
      exact hEA (hr8 (by omega))
    have hcard : Nat.card E = p ^ 4 := hr9 hr9'
    have hEB : E ≠ B := by
      intro hEB'
      have h3 : Nat.card E = p ^ 3 := by
        rw [hEB']
        exact hB.2.2.1
      rw [hcard] at h3
      have := Nat.pow_right_injective (Fact.out : p.Prime).two_le h3
      omega
    obtain ⟨-, r', -, hr12', hmodel', hweyl', hr8', -⟩ := hF'.three
    have hr9'' : 9 ≤ r' := by
      by_contra hlt
      exact hEB (hr8' (by omega))
    have hnot10 := h136 G p B c' I E h' hF' hF13' hT' hEB
    have hr10 : r' ≠ 10 := fun hr => hnot10 (hr ▸ hmodel')
    obtain ⟨n, hn, ⟨ψ⟩⟩ : ∃ n : ℕ, (n = 4 ∨ n = 5) ∧
        Nonempty (↥(torusImage E I) ≃* Equiv.Perm (Fin n)) := by
      have hrows : r' = 9 ∨ r' = 11 ∨ r' = 12 := by omega
      rcases hrows with rfl | rfl | rfl
      · exact ⟨4, Or.inl rfl, hweyl'⟩
      · exact ⟨5, Or.inr rfl, hweyl'⟩
      · exact ⟨5, Or.inr rfl, hweyl'⟩
    have hel := h.E_elem
    obtain ⟨f⟩ := LinAlg.exists_coords (p := p) E hcard
    obtain ⟨a, b, hab, hψs⟩ := Sec137.isSwap_of_reflection hp2 f (torusImage E I) hn ψ hsI hs.1
    obtain ⟨a', b', hab', hψt⟩ := Sec137.isSwap_of_reflection hp2 f (torusImage E I) hn ψ htI ht.1
    have h1 : orderOf (s * t) =
        orderOf ((⟨s, hsI⟩ : ↥(torusImage E I)) * ⟨t, htI⟩) := by
      rw [← Subgroup.orderOf_coe]
      rfl
    rw [h1, ← MulEquiv.orderOf_eq ψ, map_mul, hψs, hψt]
    exact Sec137.orderOf_swap_mul_le hn hab hab'

theorem node137_of_pair (hpair : KF134Pair) (h136 : Node136) (hSchreier : SchreierFor InCatalog)
    (hTwoAction : TwoActionInputs) (h106 : SectionTenMaximalMovingThetaComponentsQuasisimple)
    (h11 : Sec11One) (h122 : Node122) (h122b : Node122b) (h123 : Node123) (h124 : Node124)
    (h125 : Node125) (h126 : Node126) (h127 : Node127) (h128 : Node128) (h129 : Node129) :
    Node137 := fun G _ _ p A c L E h hF12 hF13 hT hEA _ =>
  node137any_of_pair hpair h136 hSchreier hTwoAction h106 h11 h122 h122b h123 h124 h125 h126 h127
    h128 h129 G p A c L E h hF12 hF13 hT hEA

end CFSG.RankThree.PartOne
