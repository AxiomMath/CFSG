module

public import CFSG.Quasithin.Background.ONanE68Sp4Torus

public section

namespace CFSG.Quasithin

namespace E6

namespace E68Proof

namespace Sp4

open Matrix CFSG.ComponentClassification.UnbalancedCatalog.SpChain
  CFSG.QuasithinUnique.Setup.X7b CFSG.Quasithin.SteinbergBS

variable {K : Type} [Field K] [CharP K 2]

theorem coord_conj {u₀ v : antiSp K} (hu : u₀ ∈ antiUnipotent K) (hv : v ∈ antiUnipotent K) :
    glMat ((u₀ * v * u₀⁻¹ : antiSp K) : GL (Fin 4) K) 0 1 = glMat (v : GL (Fin 4) K) 0 1 ∧
      glMat ((u₀ * v * u₀⁻¹ : antiSp K) : GL (Fin 4) K) 1 2 = glMat (v : GL (Fin 4) K) 1 2 := by
  obtain ⟨a₀, b₀, c₀, d₀, rfl⟩ := hu
  obtain ⟨a, b, c, d, rfl⟩ := hv
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rw [uElt_inv, uElt_mul, uElt_mul]
  simp only [glMat_uElt, uMat_apply_zero_one, uMat_apply_one_two]
  exact ⟨by linear_combination a₀ * h2, by linear_combination d₀ * h2⟩

theorem eq_uElt_of_mem {w : antiSp K} (hw : w ∈ antiUnipotent K) :
    w = uElt (glMat (w : GL (Fin 4) K) 0 1) (glMat (w : GL (Fin 4) K) 0 2)
      (glMat (w : GL (Fin 4) K) 0 3) (glMat (w : GL (Fin 4) K) 1 2) := by
  obtain ⟨a, b, c, d, rfl⟩ := hw
  rfl

theorem fixed_ad {u₀ : antiSp K} (hu : u₀ ∈ antiUnipotent K) (α β : Kˣ) {w : antiSp K}
    (hw : w ∈ antiUnipotent K) (hcomm : (u₀ * tElt α β) * w = w * (u₀ * tElt α β)) :
    (α : K) * (β : K)⁻¹ * glMat (w : GL (Fin 4) K) 0 1 = glMat (w : GL (Fin 4) K) 0 1 ∧
      (β : K) ^ 2 * glMat (w : GL (Fin 4) K) 1 2 = glMat (w : GL (Fin 4) K) 1 2 := by
  obtain ⟨a, b, c, d, rfl⟩ := hw
  have h : (u₀ * tElt α β) * uElt a b c d * (u₀ * tElt α β)⁻¹ = uElt a b c d := by
    rw [mul_inv_eq_iff_eq_mul]
    exact hcomm
  have e : (u₀ * tElt α β) * uElt a b c d * (u₀ * tElt α β)⁻¹ =
      u₀ * (tElt α β * uElt a b c d * (tElt α β)⁻¹) * u₀⁻¹ := by group
  rw [e, tElt_conj_uElt] at h
  have hc := coord_conj hu (uElt_mem_antiUnipotent ((α : K) * (β : K)⁻¹ * a)
    ((α : K) * β * b) ((α : K) ^ 2 * c) ((β : K) ^ 2 * d))
  rw [h] at hc
  simp only [glMat_uElt, uMat_apply_zero_one, uMat_apply_one_two] at hc ⊢
  exact ⟨hc.1.symm, hc.2.symm⟩

theorem fixed_bc {u₀ : antiSp K} (hu : u₀ ∈ antiUnipotent K) (α β : Kˣ) (b c : K)
    (hcomm : (u₀ * tElt α β) * uElt 0 b c 0 = uElt 0 b c 0 * (u₀ * tElt α β)) :
    (α : K) * β * b = b ∧ (α : K) ^ 2 * c = c := by
  have h : (u₀ * tElt α β) * uElt 0 b c 0 * (u₀ * tElt α β)⁻¹ = uElt 0 b c 0 := by
    rw [mul_inv_eq_iff_eq_mul]
    exact hcomm
  have e : (u₀ * tElt α β) * uElt 0 b c 0 * (u₀ * tElt α β)⁻¹ =
      u₀ * (tElt α β * uElt 0 b c 0 * (tElt α β)⁻¹) * u₀⁻¹ := by group
  rw [e, tElt_conj_uElt] at h
  have hz : uElt (0 : K) ((α : K) * β * b) ((α : K) ^ 2 * c) 0 ∈ antiUnipotentCenter K :=
    ⟨_, _, rfl⟩
  have hcen := antiUnipotentCenter_comm hz hu
  simp only [mul_zero] at h
  have h' : u₀ * uElt (0 : K) ((α : K) * β * b) ((α : K) ^ 2 * c) 0 * u₀⁻¹ =
      uElt (0 : K) ((α : K) * β * b) ((α : K) ^ 2 * c) 0 := by
    rw [mul_inv_eq_iff_eq_mul]
    exact hcen.symm
  rw [h'] at h
  obtain ⟨-, h2, h3, -⟩ := uElt_inj h
  exact ⟨h2, h3⟩

abbrev Fx (l : K) : Type := {x : K // l * x = x}

omit [CharP K 2] in
theorem card_Fx_of_eq_one [Finite K] {l : K} (h : l = 1) : Nat.card (Fx l) = Nat.card K := by
  subst h
  exact Nat.card_congr (Equiv.subtypeUnivEquiv fun x => by simp)

omit [CharP K 2] in
theorem card_Fx_of_ne_one {l : K} (h : l ≠ 1) : Nat.card (Fx l) = 1 := by
  have : Unique (Fx l) := by
    refine ⟨⟨0, by simp⟩, fun x => Subtype.ext ?_⟩
    have hx : (l - 1) * x.1 = 0 := by linear_combination x.2
    exact (mul_eq_zero.1 hx).resolve_left (sub_ne_zero.2 h)
  exact Nat.card_unique

theorem eq_one_of_sq_eq_one {x : K} (h : x ^ 2 = 1) : x = 1 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have : (x - 1) ^ 2 = 0 := by linear_combination h + (1 - x) * h2
  exact sub_eq_zero.1 (pow_eq_zero_iff (by norm_num) |>.1 this)

theorem at_most_one_trivial {α β : Kˣ} (h : ¬ (α = 1 ∧ β = 1)) :
    ((α : K) * (β : K)⁻¹ = 1 → (α : K) * β = 1 → False) ∧
    ((α : K) * (β : K)⁻¹ = 1 → (α : K) ^ 2 = 1 → False) ∧
    ((α : K) * (β : K)⁻¹ = 1 → (β : K) ^ 2 = 1 → False) ∧
    ((α : K) * β = 1 → (α : K) ^ 2 = 1 → False) ∧
    ((α : K) * β = 1 → (β : K) ^ 2 = 1 → False) ∧
    ((α : K) ^ 2 = 1 → (β : K) ^ 2 = 1 → False) := by
  have hα : (α : K) ≠ 0 := α.ne_zero
  have hβ : (β : K) ≠ 0 := β.ne_zero
  have sα : (α : K) ^ 2 = 1 → α = 1 := fun h' => Units.ext (eq_one_of_sq_eq_one h')
  have sβ : (β : K) ^ 2 = 1 → β = 1 := fun h' => Units.ext (eq_one_of_sq_eq_one h')
  have eq_of : (α : K) * (β : K)⁻¹ = 1 → α = β := fun h' =>
    Units.ext (by field_simp at h'; exact h')
  refine ⟨fun h1 h2 => ?_, fun h1 h2 => ?_, fun h1 h2 => ?_, fun h1 h2 => ?_, fun h1 h2 => ?_,
    fun h1 h2 => ?_⟩
  · have e := eq_of h1
    subst e
    exact h ⟨sα (by linear_combination h2), sα (by linear_combination h2)⟩
  · have e := eq_of h1
    have e1 := sα h2
    subst e
    exact h ⟨e1, e1⟩
  · have e := eq_of h1
    have e1 := sβ h2
    subst e1
    exact h ⟨e, rfl⟩
  · have e1 := sα h2
    subst e1
    have : (β : K) = 1 := by simpa using h1
    exact h ⟨rfl, Units.ext this⟩
  · have e1 := sβ h2
    subst e1
    have : (α : K) = 1 := by simpa using h1
    exact h ⟨Units.ext this, rfl⟩
  · exact h ⟨sα h1, sβ h2⟩

section Count

variable [Finite K]

omit [CharP K 2] in
theorem card_Fx_prod_le {la lb lc ld : K} (hab : la = 1 → lb = 1 → False)
    (hac : la = 1 → lc = 1 → False) (had : la = 1 → ld = 1 → False)
    (hbc : lb = 1 → lc = 1 → False) (hbd : lb = 1 → ld = 1 → False)
    (hcd : lc = 1 → ld = 1 → False) :
    Nat.card (Fx lb) * Nat.card (Fx lc) * (Nat.card (Fx la) * Nat.card (Fx ld)) ≤
      Nat.card K := by
  have hq : 0 < Nat.card K := Nat.card_pos
  by_cases hA : la = 1
  · rw [card_Fx_of_eq_one hA, card_Fx_of_ne_one (fun h => hab hA h),
      card_Fx_of_ne_one (fun h => hac hA h), card_Fx_of_ne_one (fun h => had hA h)]
    simp
  · rw [card_Fx_of_ne_one hA]
    by_cases hB : lb = 1
    · rw [card_Fx_of_eq_one hB, card_Fx_of_ne_one (fun h => hbc hB h),
        card_Fx_of_ne_one (fun h => hbd hB h)]
      simp
    · rw [card_Fx_of_ne_one hB]
      by_cases hC : lc = 1
      · rw [card_Fx_of_eq_one hC, card_Fx_of_ne_one (fun h => hcd hC h)]
        simp
      · rw [card_Fx_of_ne_one hC]
        by_cases hD : ld = 1
        · rw [card_Fx_of_eq_one hD]
          simp
        · rw [card_Fx_of_ne_one hD]
          simpa using Nat.succ_le_of_lt hq

theorem card_inf_centralizer_le {u₀ : antiSp K} (hu : u₀ ∈ antiUnipotent K) {α β : Kˣ}
    (h1 : ¬ (α = 1 ∧ β = 1)) :
    Nat.card ↥(antiUnipotent K ⊓ Subgroup.centralizer ({u₀ * tElt α β} : Set (antiSp K))) ≤
      Nat.card K := by
  obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := at_most_one_trivial (K := K) h1
  set g := u₀ * tElt α β with hg
  set Cg := antiUnipotent K ⊓ Subgroup.centralizer ({g} : Set (antiSp K)) with hCg
  let f : ↥Cg →* Multiplicative (K × K) :=
    unipotentPair.comp (Subgroup.inclusion (inf_le_left : Cg ≤ antiUnipotent K))
  have hf : ∀ w : ↥Cg, f w = Multiplicative.ofAdd
      (glMat ((w : antiSp K) : GL (Fin 4) K) 0 1, glMat ((w : antiSp K) : GL (Fin 4) K) 1 2) :=
    fun w => rfl
  have hcomm : ∀ w : ↥Cg, g * (w : antiSp K) = (w : antiSp K) * g := fun w =>
    Subgroup.mem_centralizer_iff.1 w.2.2 g rfl
  have hwU : ∀ w : ↥Cg, (w : antiSp K) ∈ antiUnipotent K := fun w => w.2.1
  have hrange : Nat.card ↥f.range ≤
      Nat.card (Fx ((α : K) * (β : K)⁻¹)) * Nat.card (Fx ((β : K) ^ 2)) := by
    have hmem : ∀ p ∈ f.range, (α : K) * (β : K)⁻¹ * p.toAdd.1 = p.toAdd.1 ∧
        (β : K) ^ 2 * p.toAdd.2 = p.toAdd.2 := by
      rintro _ ⟨w, rfl⟩
      rw [hf]
      exact fixed_ad hu α β (hwU w) (hcomm w)
    rw [← Nat.card_prod]
    refine Nat.card_le_card_of_injective
      (fun p : ↥f.range => (⟨p.1.toAdd.1, (hmem p.1 p.2).1⟩, ⟨p.1.toAdd.2, (hmem p.1 p.2).2⟩))
      (fun p q hpq => ?_)
    have h1 := congrArg (fun z => z.1.1) hpq
    have h2 := congrArg (fun z => z.2.1) hpq
    exact Subtype.ext (Multiplicative.toAdd.injective (Prod.ext h1 h2))
  have hker0 : ∀ p ∈ f.ker, glMat ((p : antiSp K) : GL (Fin 4) K) 0 1 = 0 ∧
      glMat ((p : antiSp K) : GL (Fin 4) K) 1 2 = 0 := by
    intro p hp
    have := congrArg Multiplicative.toAdd (MonoidHom.mem_ker.1 hp)
    rw [hf] at this
    simpa [Prod.ext_iff] using this
  have hker1 : ∀ p ∈ f.ker, (p : antiSp K) = uElt 0 (glMat ((p : antiSp K) : GL (Fin 4) K) 0 2)
      (glMat ((p : antiSp K) : GL (Fin 4) K) 0 3) 0 := by
    intro p hp
    have e := eq_uElt_of_mem (hwU p)
    rwa [(hker0 p hp).1, (hker0 p hp).2] at e
  have hker : Nat.card ↥f.ker ≤
      Nat.card (Fx ((α : K) * β)) * Nat.card (Fx ((α : K) ^ 2)) := by
    have hmem : ∀ p ∈ f.ker, (α : K) * β * glMat ((p : antiSp K) : GL (Fin 4) K) 0 2 =
        glMat ((p : antiSp K) : GL (Fin 4) K) 0 2 ∧
        (α : K) ^ 2 * glMat ((p : antiSp K) : GL (Fin 4) K) 0 3 =
        glMat ((p : antiSp K) : GL (Fin 4) K) 0 3 := by
      intro p hp
      have hc := hcomm p
      rw [hker1 p hp] at hc
      exact fixed_bc hu α β _ _ hc
    rw [← Nat.card_prod]
    refine Nat.card_le_card_of_injective
      (fun p : ↥f.ker => (⟨glMat ((p.1 : antiSp K) : GL (Fin 4) K) 0 2, (hmem p.1 p.2).1⟩,
        ⟨glMat ((p.1 : antiSp K) : GL (Fin 4) K) 0 3, (hmem p.1 p.2).2⟩)) (fun p q hpq => ?_)
    have e1 := congrArg (fun z => z.1.1) hpq
    have e2 := congrArg (fun z => z.2.1) hpq
    simp only at e1 e2
    apply Subtype.ext
    apply Subtype.ext
    rw [hker1 p.1 p.2, hker1 q.1 q.2, e1, e2]
  have hcard := Subgroup.card_ker_mul_card_range f
  calc Nat.card ↥Cg = Nat.card ↥f.ker * Nat.card ↥f.range := hcard.symm
    _ ≤ (Nat.card (Fx ((α : K) * β)) * Nat.card (Fx ((α : K) ^ 2))) *
        (Nat.card (Fx ((α : K) * (β : K)⁻¹)) * Nat.card (Fx ((β : K) ^ 2))) :=
        Nat.mul_le_mul hker hrange
    _ ≤ Nat.card K := card_Fx_prod_le hab hac had hbc hbd hcd

theorem four_lt_relIndex {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n) {g : antiSp K}
    (hg : g ∈ Subgroup.normalizer (antiUnipotent K : Set (antiSp K))) (h3 : orderOf g = 3) :
    4 < (antiUnipotent K ⊓ Subgroup.centralizer ({g} : Set (antiSp K))).relIndex
      (antiUnipotent K) := by
  obtain ⟨hcardU, -⟩ := card_and_isSylowTwoOf_antiUnipotent (K := K)
  obtain ⟨u₀, hu₀, α, β, hgeq, -, -⟩ := exists_eq_mul_tElt (mem_normalizer_iff_upper.1 hg)
  have h1 : ¬ (α = 1 ∧ β = 1) := by
    rintro ⟨rfl, rfl⟩
    rw [tElt_one, mul_one] at hgeq
    have hdvd : orderOf g ∣ Nat.card (antiUnipotent K) :=
      Subgroup.orderOf_dvd_natCard _ (hgeq ▸ hu₀)
    rw [h3, hcardU, hK, ← pow_mul] at hdvd
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).1
      (Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd)
    omega
  have hc := card_inf_centralizer_le hu₀ h1
  rw [← hgeq] at hc
  rw [Subgroup.inf_relIndex_left]
  have hmul := Subgroup.relIndex_mul_card (H := Subgroup.centralizer ({g} : Set (antiSp K)))
    (K := antiUnipotent K)
  rw [inf_comm, hcardU] at hmul
  rw [hK] at hc hmul
  set r := (Subgroup.centralizer ({g} : Set (antiSp K))).relIndex (antiUnipotent K) with hr
  set c := Nat.card ↥(antiUnipotent K ⊓ Subgroup.centralizer ({g} : Set (antiSp K))) with hcdef
  have hq4 : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hle : (2 ^ n) ^ 3 * 2 ^ n ≤ r * 2 ^ n := by
    calc (2 ^ n) ^ 3 * 2 ^ n = (2 ^ n) ^ 4 := by ring
      _ = r * c := hmul.symm
      _ ≤ r * 2 ^ n := Nat.mul_le_mul_left r hc
  have hr3 := Nat.le_of_mul_le_mul_right hle (by positivity)
  have : 64 ≤ (2 ^ n) ^ 3 := by
    calc 64 = 4 ^ 3 := by norm_num
      _ ≤ (2 ^ n) ^ 3 := Nat.pow_le_pow_left hq4 3
  omega

end Count

end Sp4

end E68Proof

end E6

end CFSG.Quasithin
