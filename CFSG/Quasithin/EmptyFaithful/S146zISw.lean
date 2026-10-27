module

public import CFSG.Quasithin.EmptyFaithful.S146zIAlg
public import CFSG.Quasithin.EmptyFaithful.S146zIGen

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7 CFSG.Quasithin.C1Pack
  CFSG.Quasithin.CosetGeom
open scoped commutatorElement Pointwise

section Rot

variable {G : Type} [Group G] [Finite G] {T M H : Subgroup G} {H₀ H₁ H₂ : Subgroup G} {t : G}

theorem IsDecP.exists_rot_of_card_four (S : Setting146 G T M) {PQ : Subgroup G}
    (hred : IsRedCE T M H PQ 3) (h : IsDecP T M H 3 H₀ H₁ H₂ t)
    (h91 : HypF91 T (VZ T M) (yOfL22 T M) (quasithinOmegaOneCenter T) (VZ T M) H)
    (hcard : Nat.card (Wsub h91 (uHi T M H H₁)) = 4) {w w' : UMod h91}
    (hw : w ∈ Wsub h91 (uHi T M H H₁)) (hw1 : w ≠ 1) (hw' : w' ∈ Wsub h91 (uHi T M H H₁))
    (hw'1 : w' ≠ 1) :
    ∃ c : ↥H, (c : G) ∈ H₁ ∧ rhoH h91 c w = w' := by
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have hH₁H : H₁ ≤ H := h.le₁.trans h.le
  have hi₁ : uHi T M H H₁ ≤ conjClosure (VZ T M) H := uHi_le_conjClosure hH₁H
  have : Fact (1 < 3) := ⟨by norm_num⟩
  have : NeZero 3 := ⟨by norm_num⟩
  obtain ⟨φ, hφs, hker⟩ := h.exists_phi_gen
  obtain ⟨a, ha⟩ := hφs (DihedralGroup.r 1)
  have haH : (a : G) ∈ H := h.le (h.le₁ a.2)
  have hapQ : (a : G) ^ 3 ∈ pCoreOf 2 H := by
    have h1 : φ (a ^ 3) = 1 := by rw [map_pow, ha]; exact DihedralGroup.r_one_pow_n
    simpa using (hker _).mp h1
  have hαinv : conjSub (a : G) (uHi T M H H₁) = uHi T M H H₁ :=
    conjSub_eq_of_mem_normalizer (h.le_normalizer_uHi₁ S hred (h.le₁ a.2))
  have hαW : ∀ w ∈ Wsub h91 (uHi T M H H₁),
      rhoH h91 ⟨(a : G), haH⟩ w ∈ Wsub h91 (uHi T M H H₁) :=
    fun w hw => rhoH_mem_Wsub h91 ⟨(a : G), haH⟩ hi₁ hαinv hw
  have hfixα : ∀ w ∈ Wsub h91 (uHi T M H H₁), rhoH h91 ⟨(a : G), haH⟩ w = w → w = 1 :=
    fun w hw hwf => h.eq_one_of_fix S hred h91 φ hker ha hw hwf
  have hpow : ∀ w ∈ Wsub h91 (uHi T M H H₁),
      (⇑(rhoH h91 ⟨(a : G), haH⟩))^[3] w = w := by
    intro w _
    rw [iterate_eq_pow_mulAut, ← map_pow]
    have h1 : rhoH h91 ((⟨(a : G), haH⟩ : ↥H) ^ 3) = 1 :=
      (rhoH_eq_one_iff h91 _).mpr (by simpa using hapQ)
    rw [h1]
    rfl
  obtain ⟨n, hn⟩ := exists_iterate_eq_of_card_four (rhoH h91 ⟨(a : G), haH⟩) _ hcard hαW hfixα hpow
    hw hw1 hw' hw'1
  refine ⟨(⟨(a : G), haH⟩ : ↥H) ^ n, ?_, ?_⟩
  · simpa using H₁.pow_mem a.2 n
  · rw [map_pow, ← iterate_eq_pow_mulAut]
    exact hn

theorem IsDecP.exists_refl_fixing (S : Setting146 G T M) {PQ : Subgroup G}
    (hred : IsRedCE T M H PQ 3) (h : IsDecP T M H 3 H₀ H₁ H₂ t)
    (h91 : HypF91 T (VZ T M) (yOfL22 T M) (quasithinOmegaOneCenter T) (VZ T M) H)
    (hcard : Nat.card (Wsub h91 (uHi T M H H₁)) = 4) {ζ₁ : UMod h91}
    (hζ : ζ₁ ∈ Wsub h91 (uHi T M H H₁)) (hζ1 : ζ₁ ≠ 1) :
    ∃ a₁ : ↥H, (a₁ : G) ∈ H₁ ∧ rhoH h91 a₁ ζ₁ = ζ₁ ∧
      ∃ u ∈ Wsub h91 (uHi T M H H₁), rhoH h91 a₁ u ≠ u := by
  have hH₁H : H₁ ≤ H := h.le₁.trans h.le
  have hi₁ : uHi T M H H₁ ≤ conjClosure (VZ T M) H := uHi_le_conjClosure hH₁H
  have : Fact (1 < 3) := ⟨by norm_num⟩
  have : NeZero 3 := ⟨by norm_num⟩
  obtain ⟨φ, hφs, hker⟩ := h.exists_phi_gen
  obtain ⟨b, hb⟩ := hφs (DihedralGroup.sr 0)
  have hbH : (b : G) ∈ H := h.le (h.le₁ b.2)
  have hbQ : (b : G) ∉ pCoreOf 2 H := by
    intro hQ
    have h1 := (hker b).mpr hQ
    rw [hb] at h1
    have h3 : DihedralGroup.sr (0 : ZMod 3) = DihedralGroup.r 0 := h1.trans DihedralGroup.one_def
    cases h3
  have hbb : (b : G) * (b : G) ∈ pCoreOf 2 H := by
    have h1 : φ (b * b) = 1 := by rw [map_mul, hb]; exact DihedralGroup.sr_mul_self 0
    simpa using (hker _).mp h1
  have hρbb : rhoH h91 ⟨(b : G), hbH⟩ * rhoH h91 ⟨(b : G), hbH⟩ = 1 := by
    rw [← map_mul]
    exact (rhoH_eq_one_iff h91 _).mpr hbb
  have hββ : ∀ v : UMod h91, rhoH h91 ⟨(b : G), hbH⟩ (rhoH h91 ⟨(b : G), hbH⟩ v) = v := by
    intro v
    have := congrArg (fun f : MulAut (UMod h91) => f v) hρbb
    simpa only [MulAut.mul_apply, MulAut.one_apply] using this
  have hinvb : conjSub (b : G) (uHi T M H H₁) = uHi T M H H₁ :=
    conjSub_eq_of_mem_normalizer (h.le_normalizer_uHi₁ S hred (h.le₁ b.2))
  have hexb : ∀ v ∈ Wsub h91 (uHi T M H H₁), rhoH h91 ⟨(b : G), hbH⟩ v ∈ Wsub h91 (uHi T M H H₁) :=
    fun v hv => rhoH_mem_Wsub h91 ⟨(b : G), hbH⟩ hi₁ hinvb hv
  have hmv : ∃ u ∈ Wsub h91 (uHi T M H H₁), rhoH h91 ⟨(b : G), hbH⟩ u ≠ u := by
    rcases h.exists_nontrivial_of_not_mem S hred hbH hbQ with ⟨u, hu, hn⟩ | ⟨u, hu, hn⟩
    · refine ⟨clsU h91 (hi₁ hu), clsU_mem_Wsub h91 (hi₁ hu) hu, fun e => hn ?_⟩
      exact (rhoH_clsU_eq_iff h91 ⟨(b : G), hbH⟩ (hi₁ hu)).mp e
    · exfalso
      apply hn
      have h1 : ⁅u, (b : G)⁆ ∈ quasithinOmegaOneCenter T :=
        h.cent₂ (Subgroup.commutator_mem_commutator hu b.2)
      have e : (b : G) * u * (b : G)⁻¹ * u⁻¹ = (⁅u, (b : G)⁆)⁻¹ := by
        rw [commutatorElement_def]; group
      rw [e]
      exact (quasithinOmegaOneCenter T).inv_mem h1
  obtain ⟨w₀, hw₀, hw₀1, hbw₀⟩ := exists_fixed_of_involution (rhoH h91 ⟨(b : G), hbH⟩) _ hββ hexb
    (fun v => by simpa [pow_two] using IntMod.sq_eq_one v) hmv
  obtain ⟨c, hcH₁, hcw⟩ := h.exists_rot_of_card_four S hred h91 hcard hw₀ hw₀1 hζ hζ1
  have hcH : (c : G) ∈ H := c.2
  have hcinv : conjSub (c : G) (uHi T M H H₁) = uHi T M H H₁ :=
    conjSub_eq_of_mem_normalizer (h.le_normalizer_uHi₁ S hred (h.le₁ hcH₁))
  have hexc : ∀ v ∈ Wsub h91 (uHi T M H H₁), rhoH h91 c v ∈ Wsub h91 (uHi T M H H₁) :=
    fun v hv => rhoH_mem_Wsub h91 c hi₁ hcinv hv
  refine ⟨c * ⟨(b : G), hbH⟩ * c⁻¹, ?_, ?_, ?_⟩
  · have h1 : (c : G) * (b : G) * (c : G)⁻¹ ∈ H₁ :=
      H₁.mul_mem (H₁.mul_mem hcH₁ b.2) (H₁.inv_mem hcH₁)
    simpa using h1
  · rw [map_mul, map_mul, map_inv, MulAut.mul_apply, MulAut.mul_apply, ← hcw]
    have : ((rhoH h91 c)⁻¹) (rhoH h91 c w₀) = w₀ := by simp
    rw [this, hbw₀]
  · obtain ⟨u, hu, hnu⟩ := hmv
    refine ⟨rhoH h91 c u, hexc u hu, fun e => hnu ?_⟩
    rw [map_mul, map_mul, map_inv, MulAut.mul_apply, MulAut.mul_apply] at e
    have e' : ((rhoH h91 c)⁻¹) (rhoH h91 c u) = u := by simp
    rw [e'] at e
    have := (rhoH h91 c).injective e
    exact this

end Rot

end CFSG.Quasithin
