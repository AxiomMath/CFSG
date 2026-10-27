module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34E9
public import CFSG.Quasithin.Vol2.Ch5Sec1L34SecChief
public import CFSG.Quasithin.Vol2.Ch5Sec1L34SecBurn
public import CFSG.Quasithin.Vol2.Ch5Sec1L34ParChief
public import CFSG.Quasithin.EmptyFaithful.S152He3Chief

public section

namespace CFSG.Quasithin.H13.SecFix

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open scoped commutatorElement

variable {G : Type*} [Group G]

namespace ElemSec

variable {A B : Subgroup G} (h : ElemSec A B)
include h

theorem sup_inf_eq {X C : Subgroup G} (hXC : X ≤ C) (hCA : C ≤ A) :
    (X ⊔ B) ⊓ C = X ⊔ (B ⊓ C) := by
  apply le_antisymm
  · rintro y ⟨hy, hyC⟩
    obtain ⟨x, hx, b, hb, rfl⟩ :=
      (F1.mem_sup_iff_exists_mul_of_le_normalizer ((hXC.trans hCA).trans h.normalizes)).mp hy
    have hbC : b ∈ C := by
      have := C.mul_mem (C.inv_mem (hXC hx)) hyC
      rwa [inv_mul_cancel_left] at this
    exact Subgroup.mul_mem_sup hx ⟨hb, hbC⟩
  · exact sup_le (le_inf le_sup_left hXC)
      (le_inf (inf_le_left.trans le_sup_right) inf_le_right)

theorem eq_inf_sup {K C : Subgroup G} (hBK : B ≤ K) (hKC : K ≤ C ⊔ B) (hCA : C ≤ A) :
    K = (K ⊓ C) ⊔ B := by
  apply le_antisymm
  · intro y hy
    obtain ⟨c, hc, b, hb, rfl⟩ :=
      (F1.mem_sup_iff_exists_mul_of_le_normalizer (hCA.trans h.normalizes)).mp (hKC hy)
    have hcK : c ∈ K := by
      have := K.mul_mem hy (K.inv_mem (hBK hb))
      rwa [mul_inv_cancel_right] at this
    exact Subgroup.mul_mem_sup ⟨hcK, hc⟩ hb
  · exact sup_le inf_le_left hBK

theorem series_sup {L C P : Subgroup G} (hLB : L ≤ Subgroup.normalizer (B : Set G))
    (hCA : C ≤ A) (hLC : L ≤ Subgroup.normalizer (C : Set G)) (hCP : C ≤ P) :
    ∀ {N : Subgroup G} {n : ℕ}, F112W.IsChiefSeriesBetween L P (C ⊓ B) N n → N ≤ C →
      F112W.IsChiefSeriesBetween (L ⊔ A) A B (N ⊔ B) n := by
  have hnorm : ∀ X : Subgroup G, X ≤ C → L ≤ Subgroup.normalizer (X : Set G) →
      IsNormalIn (L ⊔ A) A (X ⊔ B) := by
    intro X hXC hLX
    refine F112W.isNormalIn_of_le_normalizer (sup_le (hXC.trans hCA) h.le) ?_
    exact sup_le (F1.le_normalizer_sup hLX hLB)
      (h.le_normalizer le_sup_right (sup_le (hXC.trans hCA) h.le))
  have hstepmap : ∀ {L' N : Subgroup G}, C ⊓ B ≤ L' → N ≤ C → IsChiefStep L P L' N →
      IsChiefStep (L ⊔ A) A (L' ⊔ B) (N ⊔ B) := by
    intro L' N hCL' hNC hstep
    have hL'N := hstep.2.2.1
    have hL'C := hL'N.le.trans hNC
    have hLN := D14.le_normalizer_of_isNormalIn hstep.1
    have hLL' := D14.le_normalizer_of_isNormalIn hstep.2.1
    have hd1 : (L' ⊔ B) ⊓ C = L' := by
      rw [h.sup_inf_eq hL'C hCA, inf_comm]
      exact sup_eq_left.mpr hCL'
    have hd2 : (N ⊔ B) ⊓ C = N := by
      rw [h.sup_inf_eq hNC hCA, inf_comm]
      exact sup_eq_left.mpr (hCL'.trans hL'N.le)
    refine ⟨hnorm N hNC hLN, hnorm L' hL'C hLL', ?_, fun K' hK' hLK' hK'N => ?_⟩
    · refine lt_of_le_of_ne (sup_le_sup_right hL'N.le B) fun he => ?_
      have : N ≤ L' := by
        rw [← hd1, he, hd2]
      exact hL'N.not_ge this
    · have hK'C : IsNormalIn L P (K' ⊓ C) := by
        refine F112W.isNormalIn_of_le_normalizer (inf_le_right.trans hCP) ?_
        exact F7.le_normalizer_inf (le_sup_left.trans (D14.le_normalizer_of_isNormalIn hK')) hLC
      have h1 : L' ≤ K' ⊓ C := le_inf (le_sup_left.trans hLK') hL'C
      have h2 : K' ⊓ C ≤ N := by
        rw [← hd2]
        exact inf_le_inf_right C hK'N
      have hBK' : B ≤ K' := le_sup_right.trans hLK'
      have hK'CB : K' ≤ C ⊔ B := hK'N.trans (sup_le_sup_right hNC B)
      rcases hstep.2.2.2 (K' ⊓ C) hK'C h1 h2 with he | he
      · left
        rw [h.eq_inf_sup hBK' hK'CB hCA, he]
      · right
        rw [h.eq_inf_sup hBK' hK'CB hCA, he]
  have hcent : ∀ {L' N : Subgroup G}, C ⊓ B ≤ L' → N ≤ C → IsChiefStep L P L' N →
      (IsCentralStep L L' N ↔ IsCentralStep (L ⊔ A) (L' ⊔ B) (N ⊔ B)) := by
    intro L' N hCL' hNC hstep
    have hL'N := hstep.2.2.1
    have hL'C := hL'N.le.trans hNC
    have hLN := D14.le_normalizer_of_isNormalIn hstep.1
    have hLL' := D14.le_normalizer_of_isNormalIn hstep.2.1
    have hd1 : (L' ⊔ B) ⊓ C = L' := by
      rw [h.sup_inf_eq hL'C hCA, inf_comm]
      exact sup_eq_left.mpr hCL'
    constructor
    · intro hc
      have hsec : L ⊔ A ≤ secCent (N ⊔ B) (L' ⊔ B) := by
        refine sup_le (fun g hg => ⟨F1.le_normalizer_sup hLN hLB hg,
          F1.le_normalizer_sup hLL' hLB hg, fun x hx => ?_⟩) (fun a ha => ?_)
        · obtain ⟨n, hn, b, hb, rfl⟩ :=
            (F1.mem_sup_iff_exists_mul_of_le_normalizer ((hNC.trans hCA).trans h.normalizes)).mp hx
          have h1 : g * n * g⁻¹ * n⁻¹ ∈ L' := hc g hg n hn
          have h2 : g * b * g⁻¹ * b⁻¹ ∈ B :=
            B.mul_mem ((Subgroup.mem_normalizer_iff.mp (hLB hg) b).mp hb) (B.inv_mem hb)
          have h3 : n * (g * b * g⁻¹ * b⁻¹) * n⁻¹ ∈ B :=
            (Subgroup.mem_normalizer_iff.mp (h.normalizes (hCA (hNC hn))) _).mp h2
          have e : g * (n * b) * g⁻¹ * (n * b)⁻¹ =
              (g * n * g⁻¹ * n⁻¹) * (n * (g * b * g⁻¹ * b⁻¹) * n⁻¹) := by group
          rw [e]
          exact Subgroup.mul_mem_sup h1 h3
        · refine ⟨h.le_normalizer le_sup_right (sup_le (hNC.trans hCA) h.le) ha,
            h.le_normalizer le_sup_right (sup_le (hL'C.trans hCA) h.le) ha, fun x hx => ?_⟩
          exact Subgroup.mem_sup_right (h.comm a ha x (sup_le (hNC.trans hCA) h.le hx))
      exact fun g hg x hx => (hsec hg).2.2 x hx
    · intro hc g hg n hn
      have h1 := hc g (Subgroup.mem_sup_left hg) n (Subgroup.mem_sup_left hn)
      have h2 : g * n * g⁻¹ * n⁻¹ ∈ C :=
        C.mul_mem ((Subgroup.mem_normalizer_iff.mp (hLC hg) n).mp (hNC hn)) (C.inv_mem (hNC hn))
      rw [← hd1]
      exact ⟨h1, h2⟩
  intro N n hser
  induction hser with
  | refl =>
    intro _
    rw [show C ⊓ B ⊔ B = B from sup_eq_right.mpr inf_le_right]
    exact .refl
  | @central N' L' n' hstep hc hser ih =>
    intro hNC
    have hCL' := hser.le
    exact .central (hstepmap hCL' hNC hstep) ((hcent hCL' hNC hstep).mp hc)
      (ih (hstep.2.2.1.le.trans hNC))
  | @noncentral N' L' n' hstep hc hser ih =>
    intro hNC
    have hCL' := hser.le
    exact .noncentral (hstepmap hCL' hNC hstep) (fun h' => hc ((hcent hCL' hNC hstep).mpr h'))
      (ih (hstep.2.2.1.le.trans hNC))

omit h in
theorem not_nine_dvd_of_card [Finite G] {F : Subgroup G} (hA2 : IsPGroup 2 A) (hFA : F ≤ A)
    {c x : ℕ} (hF : Nat.card F = Nat.card B * c) (hA : Nat.card A = Nat.card B * x)
    (h1 : Nat.card A ≤ 16 * Nat.card F) (h2 : Nat.card F < Nat.card A) : ¬ 9 ∣ x + 8 * c := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨α, hα⟩ := hA2.exists_card_eq
  have hBpos : 0 < Nat.card B := Nat.card_pos
  have hxd : x ∣ 2 ^ α := ⟨Nat.card B, by rw [← hα, hA, mul_comm]⟩
  have hcd : c ∣ 2 ^ α := by
    have := Subgroup.card_dvd_of_le hFA
    rw [hF, hα] at this
    exact (Dvd.intro_left _ rfl).trans this
  obtain ⟨a, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hxd
  obtain ⟨b, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hcd
  rw [hF, hA] at h1 h2
  have hba : b < a := (pow_lt_pow_iff_right₀ (by norm_num : 1 < 2)).mp
    (Nat.lt_of_mul_lt_mul_left h2)
  have hab : a ≤ b + 4 := by
    have h1' : Nat.card B * 2 ^ a ≤ Nat.card B * 2 ^ (b + 4) :=
      calc Nat.card B * 2 ^ a ≤ 16 * (Nat.card B * 2 ^ b) := h1
        _ = Nat.card B * 2 ^ (b + 4) := by ring
    exact (pow_le_pow_iff_right₀ (by norm_num : 1 < 2)).mp (Nat.le_of_mul_le_mul_left h1' hBpos)
  intro h9
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hba
  have hd : d ≤ 3 := by omega
  have e : 2 ^ (b + d + 1) + 8 * 2 ^ b = 2 ^ b * (2 ^ (d + 1) + 8) := by ring
  rw [e] at h9
  have h9' := (Nat.Coprime.pow_right b (by norm_num : Nat.Coprime 9 2)).dvd_of_dvd_mul_left h9
  interval_cases d <;> norm_num at h9'

theorem two_le_of_series [Finite G] {U O L P : Subgroup G} {y : G} {m : ℕ}
    (hA2 : IsPGroup 2 A) (hU2 : IsPGroup 2 U)
    (hUA : U ≤ Subgroup.normalizer (A : Set G)) (hUB : U ≤ Subgroup.normalizer (B : Set G))
    (hOU : O ≤ U) (hO : ∀ o ∈ O, ∀ x ∈ A, o * x * o⁻¹ * x⁻¹ ∈ B)
    (hLA : L ≤ Subgroup.normalizer (A : Set G)) (hLB : L ≤ Subgroup.normalizer (B : Set G))
    (hLU : L ≤ Subgroup.normalizer (U : Set G)) (hLL : oTwoUpper L = L) (hUL : U ≤ L ⊔ O)
    (hyL : y ∈ L) (hy3 : ∀ x ∈ A, y ^ 3 * x * (y ^ 3)⁻¹ * x⁻¹ ∈ B)
    (hnorm : ∀ u ∈ U, u * (y * u * y⁻¹) * (y ^ 2 * u * (y ^ 2)⁻¹) ∈ O)
    (hsurj : ∀ u ∈ U, ∃ s ∈ U, u⁻¹ * (s * (y * s * y⁻¹)⁻¹) ∈ O)
    (hgen : ∃ u₁ ∈ U, ∃ u₂ ∈ U, ∃ u₃ ∈ U, ∃ u₄ ∈ U,
      U ≤ Subgroup.closure {u₁, u₂, u₃, u₄} ⊔ O)
    (hfaith : ¬ ∀ x ∈ A, ∀ u ∈ U, ⁅x, u⁆ ∈ B)
    (hburn : ∃ c x : ℕ, Nat.card (fixMod y A B) = Nat.card B * c ∧
      Nat.card A = Nat.card B * x ∧ 9 ∣ x + 8 * c)
    (hCP : ⁅A, L⁆ ≤ P) (hser : F112W.IsChiefSeriesBetween L P (⁅A, L⁆ ⊓ B) ⁅A, L⁆ m) :
    2 ≤ m := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hCA : ⁅A, L⁆ ≤ A := F112W.commutator_le_self_of_le_normalizer hLA
  have hLC : L ≤ Subgroup.normalizer ((⁅A, L⁆ : Subgroup G) : Set G) := fun g hg =>
    A4.mem_normalizer_commutator (hLA hg) (Subgroup.le_normalizer hg)
  have hser' := h.series_sup hLB hCA hLC hCP hser le_rfl
  have hBn : IsNormalIn (L ⊔ A) A B :=
    F112W.isNormalIn_of_le_normalizer h.le (sup_le hLB h.normalizes)
  have hadd := F112W.eta_eq_add le_sup_right hBn hser'
  have hLCB : L ≤ Subgroup.normalizer ((⁅A, L⁆ ⊔ B : Subgroup G) : Set G) :=
    F1.le_normalizer_sup hLC hLB
  have htop : F112W.eta (L ⊔ A) A A = F112W.eta (L ⊔ A) A (⁅A, L⁆ ⊔ B) :=
    (h.eta_eq_iff hLL hA2 hLA le_sup_right (sup_le hCA h.le) le_rfl hLA hLCB).mpr
      fun g hg x hx => mul_mem_of_commutator_le le_sup_left hg hx
  by_contra hm
  push Not at hm
  interval_cases m
  · have heq : F112W.eta (L ⊔ A) A A = F112W.eta (L ⊔ A) A B := by omega
    have hc := (h.eta_eq_iff hLL hA2 hLA le_rfl h.le le_rfl hLA hLB).mp heq
    have hsec : U ≤ secCent A B := hUL.trans (sup_le (fun g hg => ⟨hLA hg, hLB hg, hc g hg⟩)
      fun o ho => ⟨hUA (hOU ho), hUB (hOU ho), hO o ho⟩)
    exact hfaith fun x hx u hu =>
      commutator_le_of_le_secCent hsec (Subgroup.commutator_mem_commutator hx hu)
  · have hone : F112W.eta (L ⊔ A) A A = F112W.eta (L ⊔ A) A B + 1 := by omega
    obtain ⟨h1, h2⟩ := h.card_le_fixMod hA2 hU2 hUA hUB hOU hO hLA hLB hLU hLL hyL hy3 hnorm
      hsurj hgen hfaith hone
    obtain ⟨c, x, hF, hAx, h9⟩ := hburn
    exact not_nine_dvd_of_card hA2 (fixMod_le y A B) hF hAx h1 h2 h9

end ElemSec

theorem card_fix_conj {X : Type*} (σ ζ : Equiv.Perm X) :
    Nat.card {x // (ζ * σ * ζ⁻¹) x = x} = Nat.card {x // σ x = x} :=
  Nat.card_congr (Equiv.subtypeEquiv ζ⁻¹ fun a => by
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
    exact ⟨fun h => by simpa using congrArg (fun x => ζ⁻¹ x) h, fun h => by rw [h]; simp⟩)

theorem card_fix_inv {X : Type*} (σ : Equiv.Perm X) :
    Nat.card {x // σ⁻¹ x = x} = Nat.card {x // σ x = x} :=
  Nat.card_congr (Equiv.subtypeEquivRight fun x => by
    rw [Equiv.Perm.inv_def, Equiv.symm_apply_eq]
    exact eq_comm)

theorem card_fix_eq_of_conj {M X : Type*} [Group M] (ρ : M →* Equiv.Perm X) {y g : M}
    (hy : y ^ 3 = 1) (hg : ∃ t, g = t * y * t⁻¹ ∨ g = t * y ^ 2 * t⁻¹) :
    Nat.card {x // ρ g x = x} = Nat.card {x // ρ y x = x} := by
  have hy2 : y ^ 2 = y⁻¹ := (inv_eq_of_mul_eq_one_right (by rw [← pow_succ']; exact hy)).symm
  obtain ⟨t, rfl | rfl⟩ := hg
  · rw [map_mul, map_mul, map_inv]
    exact card_fix_conj _ _
  · rw [hy2, map_mul, map_mul, map_inv, map_inv, card_fix_conj, card_fix_inv]

theorem inf_le_normalizer_secCent (X Y : Subgroup G) :
    Subgroup.normalizer (X : Set G) ⊓ Subgroup.normalizer (Y : Set G) ≤
      Subgroup.normalizer (secCent X Y : Set G) := by
  refine ElemSec.le_normalizer_of_forall fun g hg s hs => ?_
  obtain ⟨hgX, hgY⟩ := hg
  obtain ⟨hsX, hsY, hs⟩ := hs
  refine ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hgX hsX) (Subgroup.inv_mem _ hgX),
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hgY hsY) (Subgroup.inv_mem _ hgY), fun x hx => ?_⟩
  have hx' : g⁻¹ * x * g⁻¹⁻¹ ∈ X :=
    (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgX) x).mp hx
  have h1 := (Subgroup.mem_normalizer_iff.mp hgY _).mp (hs _ hx')
  have e : g * s * g⁻¹ * x * (g * s * g⁻¹)⁻¹ * x⁻¹ =
      g * (s * (g⁻¹ * x * g⁻¹⁻¹) * s⁻¹ * (g⁻¹ * x * g⁻¹⁻¹)⁻¹) * g⁻¹ := by group
  rw [e]
  exact h1

end CFSG.Quasithin.H13.SecFix

namespace CFSG.Quasithin.H13.KGL34P

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.Quasithin CFSG.Quasithin.H13.SecFix

variable {k : Type} [Field k] [CharP k 2] {ω : k}

theorem exists_conj_torusDiag_cycSL (hω3 : ω ^ 3 = 1) (hω2 : ω ^ 2 + ω + 1 = 0) {a b : ℕ}
    (ha : a < 3) (hb : b < 3) (hab : ¬ (a = 0 ∧ b = 0)) :
    ∃ t : projectiveSL 3 k, proj 3 k (torusDiag ω hω3) ^ a * proj 3 k cycSL ^ b =
        t * proj 3 k (torusDiag ω hω3) * t⁻¹ ∨
      proj 3 k (torusDiag ω hω3) ^ a * proj 3 k cycSL ^ b =
        t * proj 3 k (torusDiag ω hω3) ^ 2 * t⁻¹ := by
  have h1 := proj_cycSL_conj hω3 hω2
  have h2 := proj_torusDiag_cycSL_conj hω3 hω2
  have h3 := proj_torusDiag_sq_cycSL_conj hω3 hω2
  have hyc : Commute (proj 3 k (torusDiag ω hω3)) (proj 3 k cycSL) :=
    (proj_cycSL_commute hω3 hω2).symm
  have hy3 : proj 3 k (torusDiag ω hω3) ^ 3 = 1 := by
    rw [← map_pow, torusDiag_pow_three, map_one]
  set y := proj 3 k (torusDiag ω hω3) with hy
  set c := proj 3 k (cycSL (k := k)) with hc
  have hy4 : (y ^ 2) ^ 2 = y := by
    rw [← pow_mul, show 2 * 2 = 3 + 1 from rfl, pow_succ, hy3, one_mul]
  interval_cases a <;> interval_cases b
  · exact absurd ⟨rfl, rfl⟩ hab
  · exact ⟨_, Or.inl (by rw [pow_zero, one_mul, pow_one]; exact h1)⟩
  · exact ⟨_, Or.inr (by rw [pow_zero, one_mul, h1, conj_pow])⟩
  · exact ⟨1, Or.inl (by group)⟩
  · exact ⟨_, Or.inl (by rw [pow_one, pow_one]; exact h2)⟩
  · refine ⟨proj 3 k (conjP3 hω2), Or.inr ?_⟩
    rw [← conj_pow, ← h3, (hyc.pow_left 2).mul_pow, hy4, pow_one]
  · exact ⟨1, Or.inr (by group)⟩
  · exact ⟨_, Or.inl (by rw [pow_one]; exact h3)⟩
  · refine ⟨proj 3 k (conjP2 hω2), Or.inr ?_⟩
    rw [← conj_pow, ← h2, hyc.mul_pow]

theorem nine_dvd_card_add_fix {X : Type*} [Finite X] (hω3 : ω ^ 3 = 1) (hω2 : ω ^ 2 + ω + 1 = 0)
    (ρ : projectiveSL 3 k →* Equiv.Perm X) :
    9 ∣ Nat.card X + 8 * Nat.card {x // ρ (proj 3 k (torusDiag ω hω3)) x = x} := by
  have hy3 : proj 3 k (torusDiag ω hω3) ^ 3 = 1 := by
    rw [← map_pow, torusDiag_pow_three, map_one]
  have hc3 : proj 3 k (cycSL (k := k)) ^ 3 = 1 := by
    rw [← map_pow, cycSL_pow_three, map_one]
  have hyc : Commute (proj 3 k (torusDiag ω hω3)) (proj 3 k cycSL) :=
    (proj_cycSL_commute hω3 hω2).symm
  refine nine_dvd_card_add (ρ.comp (hom33 _ _ hy3 hc3 hyc)) _ fun g hg => ?_
  obtain ⟨⟨i, j⟩, rfl⟩ : ∃ p, Multiplicative.ofAdd p = g := ⟨Multiplicative.toAdd g, rfl⟩
  rw [MonoidHom.comp_apply, hom33_apply]
  refine card_fix_eq_of_conj ρ hy3
    (exists_conj_torusDiag_cycSL hω3 hω2 (ZMod.val_lt i) (ZMod.val_lt j) fun hij => hg ?_)
  rw [(ZMod.val_eq_zero i).mp hij.1, (ZMod.val_eq_zero j).mp hij.2]
  rfl

end CFSG.Quasithin.H13.KGL34P

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.Quasithin.H13.SecFix
open scoped commutatorElement

variable {G : Type} [Group G]

theorem elemSec_of_isChiefStep [Finite G] {K A B : Subgroup G}
    (hstep : IsChiefStep K (pCoreOf 2 K) B A) : ElemSec A B := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hE := isElemAbelian_chiefMod hstep (pCoreOf_le 2 K) (pCoreOf_isPGroup 2 K)
  have hAN : A ≤ Subgroup.normalizer (B : Set G) :=
    (hstep.1.1.trans (pCoreOf_le 2 K)).trans (D14.le_normalizer_of_isNormalIn hstep.2.1)
  have hcomm : ∀ a b : ↥(Ch3z.chiefMod B A), a * b = b * a := fun a b => hE.1.is_comm.comm a b
  refine ⟨hstep.2.2.1.le, hAN, fun x hx y hy => ?_, fun x hx => ?_⟩
  · have h1 : Ch3z.chiefIota hAN (⟨x, hx⟩ * ⟨y, hy⟩ * ⟨x, hx⟩⁻¹ * ⟨y, hy⟩⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hcomm (Ch3z.chiefIota hAN ⟨x, hx⟩)]
      group
    exact (Ch3z.chiefIota_eq_one_iff hAN _).mp h1
  · have h1 : Ch3z.chiefIota hAN (⟨x, hx⟩ * ⟨x, hx⟩) = 1 := by
      rw [map_mul, ← sq]
      apply Subtype.ext
      exact hE.2 _ (Ch3z.chiefIota hAN ⟨x, hx⟩).2
    exact (Ch3z.chiefIota_eq_one_iff hAN _).mp h1

theorem cent_of_isChiefStep [Finite G] {K A B : Subgroup G}
    (hstep : IsChiefStep K (pCoreOf 2 K) B A) :
    ∀ o ∈ pCoreOf 2 K, ∀ x ∈ A, o * x * o⁻¹ * x⁻¹ ∈ B := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h16 := F112W.commutator_le_of_isChiefStep (pCoreOf_isPGroup 2 K) (pCoreOf_le 2 K)
    (le_normalizer_pCoreOf 2 K) hstep hstep.1.1
  exact fun o ho x hx => mul_mem_of_commutator_le h16 ho hx

theorem coe_mem_pCoreOf_iff {K : Subgroup G} (x : ↥K) :
    (x : G) ∈ pCoreOf 2 K ↔ (QuotientGroup.mk x : O2Q K) = 1 :=
  mem_pCoreOf_iff_mk_eq_one x.2

theorem exists_lift_of_mem_imgO2 {K R : Subgroup G} {x : O2Q K} (hx : x ∈ imgO2 K R) :
    ∃ r : ↥K, (r : G) ∈ R ∧ (QuotientGroup.mk r : O2Q K) = x := by
  obtain ⟨r, hr, rfl⟩ := hx
  exact ⟨r, hr, rfl⟩

theorem le_sup_pCoreOf_of_imgO2_le {K U L : Subgroup G} (hUK : U ≤ K)
    (h : imgO2 K U ≤ imgO2 K L) : U ≤ L ⊔ pCoreOf 2 K := by
  intro u hu
  obtain ⟨w, hwL, hw⟩ := exists_lift_of_mem_imgO2 (h (mk_mem_imgO2 (hUK hu) hu))
  have hO : ((w⁻¹ * ⟨u, hUK hu⟩ : ↥K) : G) ∈ pCoreOf 2 K := by
    rw [coe_mem_pCoreOf_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hw, inv_mul_cancel]
  have := Subgroup.mul_mem_sup hwL hO
  rwa [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left] at this

theorem not_forall_commutator_mem {K U A B : Subgroup G}
    (hKA : K ≤ Subgroup.normalizer (A : Set G)) (hKB : K ≤ Subgroup.normalizer (B : Set G))
    (hO : ∀ o ∈ pCoreOf 2 K, ∀ x ∈ A, o * x * o⁻¹ * x⁻¹ ∈ B) (hsimp : IsSimpleGroup (O2Q K))
    (hnc : ¬ IsCentralStep K B A) (hU : imgO2 K U ≠ ⊥) :
    ¬ ∀ x ∈ A, ∀ u ∈ U, ⁅x, u⁆ ∈ B := by
  intro hall
  set N : Subgroup ↥K := (secCent A B).subgroupOf K with hNdef
  have hKs : K ≤ Subgroup.normalizer (secCent A B : Set G) :=
    (le_inf hKA hKB).trans (inf_le_normalizer_secCent A B)
  have hNn : N.Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact (Subgroup.mem_normalizer_iff.mp (hKs g.2) n).mp hn⟩
  have hOs : pCoreOf 2 K ≤ secCent A B := fun o ho =>
    ⟨hKA (pCoreOf_le 2 K ho), hKB (pCoreOf_le 2 K ho), hO o ho⟩
  have := hNn.map (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) (QuotientGroup.mk'_surjective _)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map (QuotientGroup.mk' (CFSG.pCore 2 ↥K)))
    with hb | ht
  · apply hU
    rw [eq_bot_iff]
    rintro _ ⟨u, hu, rfl⟩
    have hu' : (u : G) ∈ U := hu
    have huN : u ∈ N := by
      rw [Subgroup.mem_subgroupOf]
      refine ⟨hKA u.2, hKB u.2, fun x hx => ?_⟩
      have := B.inv_mem (hall x hx u hu')
      rwa [commutatorElement_def,
        show ((x * u * x⁻¹ * (u : G)⁻¹)⁻¹ : G) = u * x * (u : G)⁻¹ * x⁻¹ by group] at this
    have hmem : QuotientGroup.mk' (CFSG.pCore 2 ↥K) u ∈
        N.map (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) := ⟨u, huN, rfl⟩
    rw [hb] at hmem
    exact hmem
  · apply hnc
    intro g hg x hx
    have hmem : QuotientGroup.mk' (CFSG.pCore 2 ↥K) ⟨g, hg⟩ ∈
        N.map (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) := by
      rw [ht]
      exact Subgroup.mem_top _
    obtain ⟨n, hn, hng⟩ := hmem
    have hno : ((n⁻¹ * ⟨g, hg⟩ : ↥K) : G) ∈ pCoreOf 2 K := by
      rw [coe_mem_pCoreOf_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply] at hng
      rw [hng, inv_mul_cancel]
    have hgs := (secCent A B).mul_mem (Subgroup.mem_subgroupOf.mp hn) (hOs hno)
    rw [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left] at hgs
    exact hgs.2.2 x hx

theorem exists_lift_torusDiag {K U K₂ : Subgroup G} (hOU : pCoreOf 2 K ≤ U) (hUK : U ≤ K)
    (hK₂img : imgO2 K K₂ = Subgroup.normalizer ((imgO2 K U : Subgroup (O2Q K)) : Set (O2Q K)))
    {k : Type} [Field k] [CharP k 2] (hk : Nat.card k = 4) {ω : k} (hω3 : ω ^ 3 = 1)
    (hω2 : ω ^ 2 + ω + 1 = 0) (e : O2Q K ≃* projectiveSL 3 k)
    (he : (imgO2 K U).map e.toMonoidHom = KGL34P.radP) :
    ∃ y : ↥K, (y : G) ∈ K₂ ∧ e (QuotientGroup.mk y) = proj 3 k (KGL34P.torusDiag ω hω3) ∧
      (y : G) ^ 3 ∈ pCoreOf 2 K ∧
      (∀ u ∈ U, u * (y * u * (y : G)⁻¹) * ((y : G) ^ 2 * u * ((y : G) ^ 2)⁻¹) ∈ pCoreOf 2 K) ∧
      (∀ u ∈ U, ∃ s ∈ U, u⁻¹ * (s * (y * s * (y : G)⁻¹)⁻¹) ∈ pCoreOf 2 K) ∧
      (∃ u₁ ∈ U, ∃ u₂ ∈ U, ∃ u₃ ∈ U, ∃ u₄ ∈ U,
        U ≤ Subgroup.closure {u₁, u₂, u₃, u₄} ⊔ pCoreOf 2 K) := by
  have hmemU : ∀ x : O2Q K, x ∈ imgO2 K U ↔ e x ∈ KGL34P.radP := fun x => by
    rw [← he, Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]
  have hy₀N : proj 3 k (KGL34P.torusDiag ω hω3) ∈
      Subgroup.normalizer (KGL34P.radP (k := k) : Set (projectiveSL 3 k)) := by
    rw [KGL34P.normalizer_radP hk]
    exact Subgroup.mem_map_of_mem _ (KGL34P.torusDiag_mem_stabilizer ω hω3)
  have hysN : e.symm (proj 3 k (KGL34P.torusDiag ω hω3)) ∈
      Subgroup.normalizer ((imgO2 K U : Subgroup (O2Q K)) : Set (O2Q K)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [hmemU, hmemU, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
    exact Subgroup.mem_normalizer_iff.mp hy₀N (e x)
  rw [← hK₂img] at hysN
  obtain ⟨y, hyK₂, hy⟩ := exists_lift_of_mem_imgO2 hysN
  have hey : e (QuotientGroup.mk y) = proj 3 k (KGL34P.torusDiag ω hω3) := by
    rw [hy, MulEquiv.apply_symm_apply]
  have hO : ∀ x : ↥K, e (QuotientGroup.mk x) = 1 → (x : G) ∈ pCoreOf 2 K := fun x hx => by
    rw [coe_mem_pCoreOf_iff]
    exact (MulEquiv.map_eq_one_iff e).mp hx
  have hU : ∀ u : ↥K, (u : G) ∈ U → e (QuotientGroup.mk u) ∈ KGL34P.radP := fun u hu =>
    (hmemU _).mp ((mk_mem_imgO2_iff hOU u).mpr hu)
  have hUinv : ∀ r ∈ KGL34P.radP (k := k), ∃ s : ↥K, (s : G) ∈ U ∧
      e (QuotientGroup.mk s) = r := fun r hr => by
    obtain ⟨s, hs, hs'⟩ := exists_lift_of_mem_imgO2
      ((hmemU (e.symm r)).mpr (by rwa [MulEquiv.apply_symm_apply]))
    exact ⟨s, hs, by rw [hs', MulEquiv.apply_symm_apply]⟩
  refine ⟨y, hyK₂, hey, ?_, fun u hu => ?_, fun u hu => ?_, ?_⟩
  · have := hO (y ^ 3) (by
      rw [QuotientGroup.mk_pow, map_pow, hey, ← map_pow, KGL34P.torusDiag_pow_three, map_one])
    exact this
  · have := hO (⟨u, hUK hu⟩ * (y * ⟨u, hUK hu⟩ * y⁻¹) * (y ^ 2 * ⟨u, hUK hu⟩ * (y ^ 2)⁻¹)) (by
      simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_pow, map_mul,
        map_inv, map_pow, hey]
      exact KGL34P.norm_radP hω3 hω2 (hU ⟨u, hUK hu⟩ hu))
    exact this
  · obtain ⟨s₀, hs₀, hs₀eq⟩ := KGL34P.exists_radP_eq hω3 hω2 (hU ⟨u, hUK hu⟩ hu)
    obtain ⟨s, hsU, hse⟩ := hUinv s₀ hs₀
    refine ⟨s, hsU, ?_⟩
    have := hO (⟨u, hUK hu⟩⁻¹ * (s * (y * s * y⁻¹)⁻¹)) (by
      simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv, map_mul, map_inv, hey, hse]
      exact hs₀eq)
    exact this
  · obtain ⟨s₁, hs₁, he₁⟩ := hUinv _ (KGL34P.mem_radP.mpr ⟨1, 0, rfl⟩)
    obtain ⟨s₂, hs₂, he₂⟩ := hUinv _ (KGL34P.mem_radP.mpr ⟨ω, 0, rfl⟩)
    obtain ⟨s₃, hs₃, he₃⟩ := hUinv _ (KGL34P.mem_radP.mpr ⟨0, 1, rfl⟩)
    obtain ⟨s₄, hs₄, he₄⟩ := hUinv _ (KGL34P.mem_radP.mpr ⟨0, ω, rfl⟩)
    refine ⟨s₁, hs₁, s₂, hs₂, s₃, hs₃, s₄, hs₄, fun u hu => ?_⟩
    set M : Subgroup ↥K := Subgroup.closure {s₁, s₂, s₃, s₄} with hM
    have hm : ∀ s ∈ ({s₁, s₂, s₃, s₄} : Set ↥K),
        e (QuotientGroup.mk s) ∈ (M.map (QuotientGroup.mk' (CFSG.pCore 2 ↥K))).map
          e.toMonoidHom := fun s hs =>
      ⟨QuotientGroup.mk s, ⟨s, Subgroup.subset_closure hs, rfl⟩, rfl⟩
    have hle : Subgroup.closure {proj 3 k (KGL34P.rad 1 0), proj 3 k (KGL34P.rad ω 0),
        proj 3 k (KGL34P.rad 0 1), proj 3 k (KGL34P.rad 0 ω)} ≤
        (M.map (QuotientGroup.mk' (CFSG.pCore 2 ↥K))).map e.toMonoidHom := by
      rw [Subgroup.closure_le]
      intro g hg
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl | rfl | rfl
      · rw [← he₁]
        exact hm s₁ (by simp)
      · rw [← he₂]
        exact hm s₂ (by simp)
      · rw [← he₃]
        exact hm s₃ (by simp)
      · rw [← he₄]
        exact hm s₄ (by simp)
    obtain ⟨z, ⟨w, hw, rfl⟩, hz⟩ :=
      hle (KGL34P.radP_le_closure hk hω3 hω2 (hU ⟨u, hUK hu⟩ hu))
    have hwu : (QuotientGroup.mk w : O2Q K) = QuotientGroup.mk ⟨u, hUK hu⟩ := e.injective hz
    have hwO : ((w⁻¹ * ⟨u, hUK hu⟩ : ↥K) : G) ∈ pCoreOf 2 K := by
      rw [coe_mem_pCoreOf_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hwu, inv_mul_cancel]
    have hle2 : M ≤ (Subgroup.closure ({(s₁ : G), (s₂ : G), (s₃ : G), (s₄ : G)} :
        Set G)).comap K.subtype := by
      rw [hM, Subgroup.closure_le]
      intro s hs
      rw [SetLike.mem_coe, Subgroup.mem_comap]
      apply Subgroup.subset_closure
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
      rcases hs with rfl | rfl | rfl | rfl <;> simp
    have hwG : (w : G) ∈ Subgroup.closure ({(s₁ : G), (s₂ : G), (s₃ : G), (s₄ : G)} : Set G) :=
      Subgroup.mem_comap.mp (hle2 hw)
    have := Subgroup.mul_mem_sup hwG hwO
    rwa [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left] at this

theorem l34IrredParabolicFact : L34IrredParabolicFact := by
  intro G _ _ K U A B hX hOU hUK hcomm hsq hcard hstep hnc m hm
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K₂ := oTwoUpper (K ⊓ Subgroup.normalizer (U : Set G)) with hK₂
  have hOK : pCoreOf 2 K ≤ K := pCoreOf_le 2 K
  have hO2 : IsPGroup 2 (pCoreOf 2 K) := pCoreOf_isPGroup 2 K
  have hKO : K ≤ Subgroup.normalizer (pCoreOf 2 K : Set G) := le_normalizer_pCoreOf 2 K
  have hK₂N₀ : K₂ ≤ K ⊓ Subgroup.normalizer (U : Set G) := oTwoUpper_le _
  have hK₂K : K₂ ≤ K := hK₂N₀.trans inf_le_left
  have hK₂U : K₂ ≤ Subgroup.normalizer (U : Set G) := hK₂N₀.trans inf_le_right
  have hK₂K₂ : oTwoUpper K₂ = K₂ := D14.oTwoUpper_oTwoUpper _
  have hOK₂ : pCoreOf 2 K ≤ Subgroup.normalizer (K₂ : Set G) :=
    (le_inf hOK (hOU.trans Subgroup.le_normalizer)).trans (le_normalizer_oTwoUpper _)
  have hU2 : IsPGroup 2 U := by
    obtain ⟨a, ha⟩ := hO2.exists_card_eq
    refine IsPGroup.of_card (n := a + 4) ?_
    rw [hcard, ha, pow_add]
    ring
  have hAO : A ≤ pCoreOf 2 K := hstep.1.1
  have hA2 : IsPGroup 2 A := hO2.to_le hAO
  have hKA : K ≤ Subgroup.normalizer (A : Set G) := D14.le_normalizer_of_isNormalIn hstep.1
  have hKB : K ≤ Subgroup.normalizer (B : Set G) := D14.le_normalizer_of_isNormalIn hstep.2.1
  have hE : ElemSec A B := elemSec_of_isChiefStep hstep
  have hOc := cent_of_isChiefStep hstep
  have hQN : K₂ ≤ Subgroup.normalizer ((pCoreOf 2 K ⊓ K₂ : Subgroup G) : Set G) :=
    F7.le_normalizer_inf (hK₂K.trans hKO) Subgroup.le_normalizer
  have hQP₂ : pCoreOf 2 K ⊓ K₂ ≤ pCoreOf 2 K₂ :=
    le_pCoreOf_of_le_normalizer 2 inf_le_right hQN (hO2.to_le inf_le_left)
  have hCA : ⁅A, K₂⁆ ≤ A := F112W.commutator_le_self_of_le_normalizer (hK₂K.trans hKA)
  have hCK₂ : ⁅A, K₂⁆ ≤ K₂ := by
    rw [Subgroup.commutator_comm]
    exact F112W.commutator_le_self_of_le_normalizer (hAO.trans hOK₂)
  have hCP : ⁅A, K₂⁆ ≤ pCoreOf 2 K₂ := (le_inf (hCA.trans hAO) hCK₂).trans hQP₂
  have hUe := isElemAbelian_imgO2_of hcomm hsq
  have hUc := card_imgO2_of hOU hUK hcard
  obtain ⟨k, _, hk, e, he⟩ := exists_mulEquiv_radP hX hUe hUc
  have := LinearFieldFour.charP_two_of_card_eq_four hk
  obtain ⟨ω, hω3, hω2⟩ := KGL34P.exists_primitive_cube_root hk
  have hK₂img : imgO2 K K₂ =
      Subgroup.normalizer ((imgO2 K U : Subgroup (O2Q K)) : Set (O2Q K)) := by
    obtain ⟨S₀, -, hTP, -⟩ := exists_twoParRad_of_isElemAbelian hX hUe hUc
    rw [hK₂, imgO2_oTwoUpper inf_le_left, imgO2_inf_normalizer_eq hOU hUK]
    exact hTP.2.2.2.2.2.1
  obtain ⟨y, hyK₂, hey, hy3, hnorm, hsurj, hgen⟩ :=
    exists_lift_torusDiag hOU hUK hK₂img hk hω3 hω2 e he
  have hUL : U ≤ K₂ ⊔ pCoreOf 2 K := le_sup_pCoreOf_of_imgO2_le hUK (by
    rw [hK₂img]
    exact Subgroup.le_normalizer)
  have hsimp : IsSimpleGroup (O2Q K) := by
    have := KGL34P.isSimpleGroup_projectiveSL_three (k := k)
    exact e.isSimpleGroup
  have hUne : imgO2 K U ≠ ⊥ := by
    intro hb
    rw [hb, Subgroup.card_bot] at hUc
    norm_num at hUc
  have hfaith := not_forall_commutator_mem hKA hKB hOc hsimp hnc hUne
  have hker : CFSG.pCore 2 ↥K ≤ (secPermHom A B K hKA hKB).ker := fun o ho => by
    rw [MonoidHom.mem_ker]
    have hoO : (o : G) ∈ pCoreOf 2 K := by
      exact ⟨_, ho, rfl⟩
    exact hE.secPermHom_eq_one hKA hKB (hOc _ hoO)
  have h9 := KGL34P.nine_dvd_card_add_fix hω3 hω2
    ((QuotientGroup.lift (CFSG.pCore 2 ↥K) (secPermHom A B K hKA hKB) hker).comp
      e.symm.toMonoidHom)
  rw [MonoidHom.comp_apply, ← hey, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply,
    QuotientGroup.lift_mk] at h9
  have hAcard : Nat.card A = Nat.card B * Nat.card (↥A ⧸ B.subgroupOf A) := by
    rw [mul_comm, ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE.le).toEquiv,
      ← Subgroup.card_eq_card_quotient_mul_card_subgroup]
  exact hE.two_le_of_series hA2 hU2 (hUK.trans hKA) (hUK.trans hKB) hOU hOc (hK₂K.trans hKA)
    (hK₂K.trans hKB) hK₂U hK₂K₂ hUL hyK₂ (fun x hx => hOc _ hy3 x hx) hnorm hsurj hgen hfaith
    ⟨_, _, hE.card_fixMod_eq hKA hKB y, hAcard, h9⟩ hCP hm

theorem l34ParabolicChiefFact : L34ParabolicChiefFact :=
  l34ParabolicChiefFact_of l34IrredParabolicFact

end CFSG.Quasithin.H13
