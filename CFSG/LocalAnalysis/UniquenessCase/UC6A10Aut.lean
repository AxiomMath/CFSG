module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.GroupA10Cent
import all CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.GroupA10Cent
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointExoticSigAlt
public import CFSG.LocalAnalysis.UniquenessCase.UC6AutKernels
public import CFSG.LocalAnalysis.UniquenessCase.UC6A10Gen
public import CFSG.LocalAnalysis.UniquenessCase.UC6N588B11

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6.A10Aut

open Equiv Equiv.Perm Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
open CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.A10Perm
open CFSG.LocalAnalysis.UniquenessCase.UC6.A10Gen (O1 O2 O1_disj O2_disj)

theorem S₀_comm {x y : A10} (hx : x ∈ S₀) (hy : y ∈ S₀) : x * y = y * x := by
  obtain ⟨i, j, rfl⟩ := mem_S₀.1 hx
  obtain ⟨k, l, rfl⟩ := mem_S₀.1 hy
  rw [mul_aux, mul_aux, add_comm i k, add_comm j l]

theorem a₁a₂_mem : a₁ * a₂ ∈ S₀ := mem_S₀.2 ⟨1, 1, by simp⟩

theorem a₁a₂_not_line₁ : a₁ * a₂ ∉ line₁ := by
  intro h
  obtain ⟨n, hn⟩ := mem_zpowers_nat.1 (h : a₁ * a₂ ∈ zpowers a₁)
  have := exp_inj (i := n) (j := 0) (k := 1) (l := 1) (by simpa using hn)
  simp at this

theorem a₁a₂_not_line₂ : a₁ * a₂ ∉ line₂ := by
  intro h
  obtain ⟨n, hn⟩ := mem_zpowers_nat.1 (h : a₁ * a₂ ∈ zpowers a₂)
  have := exp_inj (i := 0) (j := n) (k := 1) (l := 1) (by simpa using hn)
  simp at this

theorem centralizer_a₁a₂ : centralizer ({a₁ * a₂} : Set A10) = S₀ := by
  have hcard := a10c_card_diag a₁a₂_mem a₁a₂_not_line₁ a₁a₂_not_line₂
  symm
  refine Subgroup.eq_of_le_of_card_ge (fun x hx => ?_) (by rw [hcard, card_S₀])
  rw [mem_centralizer_singleton_iff]
  exact (S₀_comm hx a₁a₂_mem)

theorem even_commute_mem {ρ : Perm (Fin 10)} (hρ : sign ρ = 1)
    (hc : ρ * ((a₁ * a₂ : A10) : Perm (Fin 10)) = ((a₁ * a₂ : A10) : Perm (Fin 10)) * ρ) :
    ∃ e ∈ S₀, (e : Perm (Fin 10)) = ρ := by
  let r : A10 := ⟨ρ, mem_alternatingGroup.2 hρ⟩
  have : r ∈ centralizer ({a₁ * a₂} : Set A10) := by
    rw [mem_centralizer_singleton_iff]
    exact Subtype.ext hc
  rw [centralizer_a₁a₂] at this
  exact ⟨r, this, rfl⟩

theorem perm_commute_S₀ (σ : Perm (Fin 10))
    (h : ∀ e ∈ S₀, σ * (e : Perm (Fin 10)) = (e : Perm (Fin 10)) * σ) :
    ∃ e ∈ S₀, (e : Perm (Fin 10)) = σ := by
  rcases Int.units_eq_one_or (sign σ) with h1 | h1
  · exact even_commute_mem h1 (h _ a₁a₂_mem)
  ·
    have hτs : a10c_swp5 * ((a₁ * a₂ : A10) : Perm (Fin 10)) =
        ((a₁ * a₂ : A10) : Perm (Fin 10)) * a10c_swp5 := a10c_swp5_comm
    have hsgn : sign (a10c_swp5 * σ) = 1 := by
      rw [Equiv.Perm.sign_mul, a10c_swp5_sign, h1]; rfl
    have hc : a10c_swp5 * σ * ((a₁ * a₂ : A10) : Perm (Fin 10)) =
        ((a₁ * a₂ : A10) : Perm (Fin 10)) * (a10c_swp5 * σ) := by
      rw [mul_assoc, h _ a₁a₂_mem, ← mul_assoc, hτs, mul_assoc]
    obtain ⟨e₀, he₀, he₀eq⟩ := even_commute_mem hsgn hc
    have hρ : Commute (a10c_swp5 * σ) (a₁ : Perm (Fin 10)) := by
      rw [← he₀eq]; exact congrArg Subtype.val (S₀_comm he₀ a₁_mem)
    have hσ : Commute σ (a₁ : Perm (Fin 10)) := h a₁ a₁_mem
    have hcτ : Commute a10c_swp5 (a₁ : Perm (Fin 10)) := by
      simpa using hρ.mul_left hσ.inv_left
    have hne : ¬ (a10c_swp5 * (a₁ : Perm (Fin 10)) = (a₁ : Perm (Fin 10)) * a10c_swp5) := by
      unfold a10c_swp5; decide +kernel
    exact absurd hcτ.eq hne

theorem aut_fix_S₀ (α : MulAut A10) (hα : ∀ e ∈ S₀, α e = e) : ∃ e ∈ S₀, α = MulAut.conj e := by
  obtain ⟨σ, hσ⟩ := CFSG.Milestones.alternating_automorphism_permutation (n := 10) (Or.inr (by norm_num)) α
  have hcomm : ∀ e ∈ S₀, σ * (e : Perm (Fin 10)) = (e : Perm (Fin 10)) * σ := by
    intro e he
    have h1 := hσ e
    rw [hα e he] at h1
    exact mul_inv_eq_iff_eq_mul.1 h1.symm
  obtain ⟨e₀, he₀, rfl⟩ := perm_commute_S₀ σ hcomm
  refine ⟨e₀, he₀, ?_⟩
  ext g
  simp [hσ g, MulAut.conj_apply]

theorem absKC_A10 (r : ℕ) : AbsKC A10 r S₀ := fun α _ hα => aut_fix_S₀ α hα

theorem absKInv_A10 : AbsKInv A10 S₀ := by
  intro x y hx hy hxE hyE hx1 hy1
  exfalso
  obtain ⟨e₀, he₀, hxe⟩ := aut_fix_S₀ x hxE
  obtain ⟨k, hk⟩ := hx
  have h25 : x ^ 25 = 1 := by
    have h : (⟨e₀, he₀⟩ : S₀) ^ Nat.card S₀ = 1 := pow_card_eq_one'
    rw [card_S₀] at h
    have h' : e₀ ^ 25 = 1 := congrArg Subtype.val h
    rw [hxe, ← map_pow, h', map_one]
  have hdvd : 2 ^ k ∣ 25 := hk ▸ orderOf_dvd_of_pow_eq_one h25
  have hk1 : 2 ^ k = 1 :=
    Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_left k (by norm_num)) hdvd
  rw [hk1] at hk
  exact hx1 (orderOf_eq_one_iff.1 hk)

noncomputable abbrev autEquiv : MulAut A10 ≃* Perm (Fin 10) := conjEquiv10.symm

theorem autEquiv_conj (e : A10) : autEquiv (MulAut.conj e) = (e : Perm (Fin 10)) :=
  (MulEquiv.symm_apply_eq _).2 (conjEquiv10_coe e).symm

theorem absKN_A10 {r : ℕ} (hr : r = 5) (isL34 : Prop) (E : Subgroup A10) (hE : Nat.card E = 25) :
    AbsKN A10 r E isL34 := by
  subst hr
  intro X hXE hX5
  have hXbot : X = ⊥ := by
    have hcop : Nat.Coprime 5 (Nat.card X) := by
      rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_five]
      intro hd
      haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
      obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 5 hd
      have h1 : (x : MulAut A10) = 1 := hX5 x x.2 ⟨1, by simpa using hx⟩
      have h2 : x = 1 := Subtype.ext h1
      rw [h2, orderOf_one] at hx
      omega
    have hinj : Function.Injective autEquiv.toMonoidHom := autEquiv.injective
    refine (Subgroup.map_eq_bot_iff_of_injective X (f := autEquiv.toMonoidHom) hinj).1 ?_
    refine CFSG.LocalAnalysis.RankFourTheoremC.SigAlt.eq_bot_of_card_ten (Ω := Fin 10) (by simp)
      (B := E.map (alternatingGroup (Fin 10)).subtype) ?_ ?_ ?_ ?_
    · rw [Subgroup.card_map_of_injective (alternatingGroup (Fin 10)).subtype_injective, hE]
    · haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
      have hc := IsPGroup.commutative_of_card_eq_prime_sq (p := 5) (G := E) (by rw [hE]; norm_num)
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      have := congrArg Subtype.val (hc ⟨a, ha⟩ ⟨b, hb⟩)
      exact congrArg Subtype.val this
    · rw [Subgroup.card_map_of_injective hinj]
      exact hcop
    · rintro _ ⟨e, he, rfl⟩
      refine Subgroup.mem_set_normalizer_iff.2 fun n => ?_
      obtain ⟨m, rfl⟩ := autEquiv.surjective n
      have hconj : ((alternatingGroup (Fin 10)).subtype e) * autEquiv.toMonoidHom m *
          ((alternatingGroup (Fin 10)).subtype e)⁻¹ =
          autEquiv.toMonoidHom (MulAut.conj e * m * (MulAut.conj e)⁻¹) := by
        simp [autEquiv_conj]
      rw [SetLike.mem_coe, SetLike.mem_coe]
      change autEquiv.toMonoidHom m ∈ X.map autEquiv.toMonoidHom ↔
        ((alternatingGroup (Fin 10)).subtype e * autEquiv.toMonoidHom m *
          ((alternatingGroup (Fin 10)).subtype e)⁻¹) ∈ X.map autEquiv.toMonoidHom
      rw [hconj, Subgroup.mem_map_iff_mem hinj, Subgroup.mem_map_iff_mem hinj]
      refine ⟨fun h => hXE e he m h, fun h => ?_⟩
      have := hXE e⁻¹ (E.inv_mem he) _ h
      simpa [map_inv, mul_assoc] using this
  subst hXbot
  refine ⟨fun x hx => ?_, Or.inl rfl⟩
  rw [Subgroup.mem_bot.1 hx]
  intro e _
  rfl

theorem a₁_moves_O1 : ∀ i : Fin 10, (a₁ : Perm (Fin 10)) i ≠ i → i ∈ O1 := by decide +kernel

theorem a₂_moves_O2 : ∀ i : Fin 10, (a₂ : Perm (Fin 10)) i ≠ i → i ∈ O2 := by decide +kernel

theorem commute_a₁_of_fix {x : A10} (hx : ∀ i, i ∉ O2 → (x : Perm (Fin 10)) i = i) :
    x * a₁ = a₁ * x := by
  apply Subtype.ext
  have hd : (x : Perm (Fin 10)).Disjoint (a₁ : Perm (Fin 10)) := fun i => by
    by_cases h : i ∈ O2
    · right
      by_contra hne
      exact O2_disj i h (a₁_moves_O1 i hne)
    · exact Or.inl (hx i h)
  exact hd.commute.eq

theorem commute_a₂_of_fix {x : A10} (hx : ∀ i, i ∉ O1 → (x : Perm (Fin 10)) i = i) :
    x * a₂ = a₂ * x := by
  apply Subtype.ext
  have hd : (x : Perm (Fin 10)).Disjoint (a₂ : Perm (Fin 10)) := fun i => by
    by_cases h : i ∈ O1
    · right
      by_contra hne
      exact O1_disj i h (a₂_moves_O2 i hne)
    · exact Or.inl (hx i h)
  exact hd.commute.eq

theorem isSylowOf_S₀ : CFSG.ABGLocalTools.IsSylowOf 5 S₀ ⊤ := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  refine CFSG.ABGLocalTools.isSylowOf_of_card le_top ?_
  rw [card_S₀, Subgroup.card_top, factorization_A10]
  norm_num

end CFSG.LocalAnalysis.UniquenessCase.UC6.A10Aut

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open Subgroup

theorem kMult_A10 (J : Type) [Group J] [Finite J] (hq : CFSG.Open.IsQuasisimple J)
    (N : Subgroup J) [N.Normal] (hN : N ≤ center J)
    (hA : CFSG.LocalAnalysis.UniquenessCase.UC22.IsAlt (J ⧸ N) 10)
    (hodd : Odd (Nat.card (center J))) : center J = ⊥ := by
  obtain ⟨e⟩ := hA
  haveI : Group.IsPerfect J := ⟨hq.1⟩
  let η : J →* alternatingGroup (Fin (8 + 2)) := e.toMonoidHom.comp (QuotientGroup.mk' N)
  have hη : Function.Surjective η := e.surjective.comp (QuotientGroup.mk'_surjective N)
  have hker : η.ker = N := by
    ext x
    simp [η, MonoidHom.mem_ker, QuotientGroup.eq_one_iff]
  have hK : η.ker ≤ center J := hker ▸ hN
  have hoddK : Odd (Nat.card η.ker) := by
    rw [hker]
    exact Odd.of_dvd_nat hodd (Subgroup.card_dvd_of_le hN)
  have h1 := CFSG.Alternating.Multipliers.card_ker_eq_one_of_odd (m := 8) (by norm_num) η hη hK hoddK
  have hNbot : N = ⊥ := by
    rw [← hker]
    exact Subgroup.eq_bot_of_card_eq _ h1
  rw [eq_bot_iff]
  intro x hx
  have hηx : η x ∈ center (alternatingGroup (Fin 10)) := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨x', rfl⟩ := hη y
    rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.1 hx x')]
  rw [alternatingGroup.center_eq_bot (by simp)] at hηx
  have : x ∈ η.ker := MonoidHom.mem_ker.2 (Subgroup.mem_bot.1 hηx)
  rw [hker, hNbot] at this
  exact this

end CFSG.LocalAnalysis.UniquenessCase.UCK
