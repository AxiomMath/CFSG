module

public import CFSG.Quasithin.EmptyFaithful.S146zHRank
public import CFSG.Quasithin.EmptyFaithful.S146zHOfour
public import CFSG.Quasithin.EmptyFaithful.S146zHFix
public import CFSG.Quasithin.EmptyFaithful.S146zHNon

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7 CFSG.Quasithin.C1Pack
  CFSG.Quasithin.CosetGeom
open scoped commutatorElement Pointwise

section Core

variable {G : Type} [Group G] [Finite G] {T M H : Subgroup G} {p : ℕ} {H₀ H₁ H₂ : Subgroup G} {t : G}

theorem IsDecP.case13One_of_tv (S : Setting146 G T M) {PQ : Subgroup G} (hred : IsRedCE T M H PQ p)
    (h : IsDecP T M H p H₀ H₁ H₂ t) {g : G} (tv : TvData T M H g) {x₀ u₀ : G}
    (hx₀ : x₀ ∈ conjSub g⁻¹ (conjClosure (VZ T M) H)) (hu₀ : u₀ ∈ uHi T M H H₁)
    (hn : x₀ * u₀ * x₀⁻¹ * u₀⁻¹ ∉ quasithinOmegaOneCenter T) : Case13One T M H p H₁ := by
  classical
  have hH : IsHTM T M H := hred.isHTM
  have hp : p.Prime := hred.prime
  have hp2 : p ≠ 2 := hred.odd
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  obtain ⟨-, h98⟩ := S.lemma_14_5_14 (S.isHz_iff.mpr hH)
  have h91 := h98.toHypF91
  have hHN : H ≤ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) :=
    (S.le_mcOf hH).trans S.normalizer_Z.ge
  have hUZ : conjClosure (VZ T M) H ≤ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) :=
    S.conjClosure_le_normalizer_Z hH
  have hHU : H ≤ Subgroup.normalizer (conjClosure (VZ T M) H : Set G) :=
    le_normalizer_conjClosure _ _
  have hUab : IsElemAbelian 2 (conjClosure (VZ T M) H) := S.lemma_14_5_15_two hH
  have hUp : IsPGroup 2 (conjClosure (VZ T M) H) := isPGroup_of_isElemAbelian hUab
  have hH₁H : H₁ ≤ H := h.le₁.trans h.le
  have hH₂H : H₂ ≤ H := h.le₂.trans h.le
  have hi₁ : uHi T M H H₁ ≤ conjClosure (VZ T M) H := uHi_le_conjClosure hH₁H
  have hi₂ : uHi T M H H₂ ≤ conjClosure (VZ T M) H := uHi_le_conjClosure hH₂H
  have hUgH : conjSub g⁻¹ (conjClosure (VZ T M) H) ≤ H := tv.le_H
  have hUgab : IsElemAbelian 2 (conjSub g⁻¹ (conjClosure (VZ T M) H)) := isElemAbelian_conjSub hUab
  have hZgU : conjSub g⁻¹ (quasithinOmegaOneCenter T) ≤ conjClosure (VZ T M) H := by
    rw [← tv.comm, Subgroup.commutator_comm]
    exact S145.commutator_le_of_le_normalizer (hUgH.trans hHU)
  obtain ⟨c', hc'1, hc'u⟩ := (Nat.card_eq_two_iff' (1 : ↥(conjSub g⁻¹ (quasithinOmegaOneCenter T)))).mp
    tv.card
  have hcU : (c' : G) ∈ conjClosure (VZ T M) H := hZgU c'.2
  have hF : ∀ (x : G) (hx : x ∈ conjSub g⁻¹ (conjClosure (VZ T M) H)) (w : UMod h91),
      rhoH h91 ⟨x, hUgH hx⟩ w * w⁻¹ = 1 ∨
        rhoH h91 ⟨x, hUgH hx⟩ w * w⁻¹ = clsU h91 hcU := by
    intro x hx w
    obtain ⟨u, hu, rfl⟩ := exists_clsU h91 w
    have hcomm : x * u * x⁻¹ * u⁻¹ ∈ conjSub g⁻¹ (quasithinOmegaOneCenter T) := by
      rw [← tv.comm]
      exact Subgroup.commutator_mem_commutator hx hu
    have hxu : x * u * x⁻¹ * u⁻¹ ∈ conjClosure (VZ T M) H := hZgU hcomm
    have e : rhoH h91 ⟨x, hUgH hx⟩ (clsU h91 hu) * (clsU h91 hu)⁻¹ = clsU h91 hxu := by
      rw [rhoH_clsU, clsU_inv h91 hu, clsU_mul]
    rw [e]
    by_cases h1 : (⟨x * u * x⁻¹ * u⁻¹, hcomm⟩ : ↥(conjSub g⁻¹ (quasithinOmegaOneCenter T))) = 1
    · left
      have h2 : x * u * x⁻¹ * u⁻¹ = 1 := congrArg Subtype.val h1
      rw [clsU_eq_one_iff, h2]
      exact (quasithinOmegaOneCenter T).one_mem
    · right
      have h2 := hc'u _ h1
      exact clsU_congr h91 _ _ (congrArg Subtype.val h2)
  have hZ₁ : quasithinOmegaOneCenter T ≤ uHi T M H H₁ := Z_le_uHi T M H H₁
  have hW₁₂ : Wsub h91 (uHi T M H H₁) ⊓ Wsub h91 (uHi T M H H₂) = ⊥ :=
    Wsub_inf_eq_bot h91 hi₁ hi₂ hZ₁ h.dir_inf.le
  have : Fact (1 < p) := ⟨hp.one_lt⟩
  have : NeZero p := ⟨by omega⟩
  obtain ⟨φ, hφs, hker⟩ := h.exists_phi_gen
  obtain ⟨a, ha⟩ := hφs (DihedralGroup.r 1)
  have haH : (a : G) ∈ H := h.le (h.le₁ a.2)
  have hapQ : (a : G) ^ p ∈ pCoreOf 2 H := by
    have h1 : φ (a ^ p) = 1 := by rw [map_pow, ha]; exact DihedralGroup.r_one_pow_n
    simpa using (hker _).mp h1
  have hαinv : conjSub (a : G) (uHi T M H H₁) = uHi T M H H₁ :=
    conjSub_eq_of_mem_normalizer (h.le_normalizer_uHi₁ S hred (h.le₁ a.2))
  have hαW : ∀ w ∈ Wsub h91 (uHi T M H H₁), rhoH h91 ⟨(a : G), haH⟩ w ∈ Wsub h91 (uHi T M H H₁) :=
    fun w hw => rhoH_mem_Wsub h91 ⟨(a : G), haH⟩ hi₁ hαinv hw
  have hfixα : ∀ w ∈ Wsub h91 (uHi T M H H₁), rhoH h91 ⟨(a : G), haH⟩ w = w → w = 1 :=
    fun w hw hwf => h.eq_one_of_fix S hred h91 φ hker ha hw hwf
  have hpow : ∀ w ∈ Wsub h91 (uHi T M H H₁), (⇑(rhoH h91 ⟨(a : G), haH⟩))^[p] w = w := by
    intro w _
    rw [iterate_eq_pow_mulAut, ← map_pow]
    have h1 : rhoH h91 ((⟨(a : G), haH⟩ : ↥H) ^ p) = 1 :=
      (rhoH_eq_one_iff h91 _).mpr (by simpa using hapQ)
    rw [h1]
    rfl
  have hu₀U : u₀ ∈ conjClosure (VZ T M) H := hi₁ hu₀
  have hw₁ : clsU h91 hu₀U ∈ Wsub h91 (uHi T M H H₁) := clsU_mem_Wsub h91 hu₀U hu₀
  have hx₀H : x₀ ∈ H := hUgH hx₀
  have hw₁ne : clsU h91 hu₀U ≠ 1 := by
    intro e
    have hu₀Z : u₀ ∈ quasithinOmegaOneCenter T := (clsU_eq_one_iff h91 hu₀U).mp e
    apply hn
    have h1 : x₀ * u₀ * x₀⁻¹ ∈ quasithinOmegaOneCenter T :=
      (Subgroup.mem_normalizer_iff.mp (hHN hx₀H) u₀).mp hu₀Z
    exact (quasithinOmegaOneCenter T).mul_mem h1 ((quasithinOmegaOneCenter T).inv_mem hu₀Z)
  have hpW : p < Nat.card (Wsub h91 (uHi T M H H₁)) :=
    prime_lt_card_of_free (rhoH h91 ⟨(a : G), haH⟩) _ hp hαW hfixα hpow ⟨_, hw₁, hw₁ne⟩
  have hns : ∀ x ∈ conjSub g⁻¹ (conjClosure (VZ T M) H),
      x ∈ Subgroup.normalizer (H₁ : Set G) ∧ conjSub x (uHi T M H H₁) = uHi T M H H₁ := by
    intro x hx
    rcases h.normalizer_or_swap S hred (hUgH hx) with ⟨hxN, h1, -⟩ | ⟨h1, -⟩
    · exact ⟨hxN, h1⟩
    · exfalso
      have hle : Nat.card (Wsub h91 (uHi T M H H₁)) ≤ 2 :=
        card_le_two_of_swap (rhoH h91 ⟨x, hUgH hx⟩) (Wsub h91 (uHi T M H H₁))
          (Wsub h91 (uHi T M H H₂)) (clsU h91 hcU) (hF x hx)
          (fun w hw => rhoH_mem_Wsub h91 ⟨x, hUgH hx⟩ hi₁ h1 hw) hW₁₂
      omega
  obtain ⟨hx₀N, hx₀inv⟩ := hns x₀ hx₀
  have hx₀2 : x₀ * x₀ ∈ pCoreOf 2 H := by
    have h1 := isElemAbelian_pow_eq_one hUgab hx₀
    rw [pow_two] at h1
    rw [h1]
    exact (pCoreOf 2 H).one_mem
  have hrel : (∀ w ∈ Wsub h91 (uHi T M H H₁),
        rhoH h91 ⟨(a : G), haH⟩ (rhoH h91 ⟨x₀, hx₀H⟩ (rhoH h91 ⟨(a : G), haH⟩ w)) =
          rhoH h91 ⟨x₀, hx₀H⟩ w) ∨
      (∀ w ∈ Wsub h91 (uHi T M H H₁),
        rhoH h91 ⟨x₀, hx₀H⟩ (rhoH h91 ⟨(a : G), haH⟩ w) =
          rhoH h91 ⟨(a : G), haH⟩ (rhoH h91 ⟨x₀, hx₀H⟩ w)) := by
    rcases h.conj_rotation_aux hp hp2 φ hker ha hx₀H hx₀N hx₀2 with h1 | h1
    · right
      have h2 : rhoH h91 ((⟨x₀, hx₀H⟩ : ↥H) * ⟨(a : G), haH⟩ * (⟨x₀, hx₀H⟩ : ↥H)⁻¹ *
          (⟨(a : G), haH⟩ : ↥H)⁻¹) = 1 := (rhoH_eq_one_iff h91 _).mpr (by simpa using h1)
      rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h2
      intro w _
      have h3 : rhoH h91 ⟨x₀, hx₀H⟩ * rhoH h91 ⟨(a : G), haH⟩ =
          rhoH h91 ⟨(a : G), haH⟩ * rhoH h91 ⟨x₀, hx₀H⟩ := by
        calc rhoH h91 ⟨x₀, hx₀H⟩ * rhoH h91 ⟨(a : G), haH⟩ =
            (rhoH h91 ⟨x₀, hx₀H⟩ * rhoH h91 ⟨(a : G), haH⟩ * (rhoH h91 ⟨x₀, hx₀H⟩)⁻¹ *
              (rhoH h91 ⟨(a : G), haH⟩)⁻¹) *
              (rhoH h91 ⟨(a : G), haH⟩ * rhoH h91 ⟨x₀, hx₀H⟩) := by group
          _ = _ := by rw [h2, one_mul]
      have h4 := congrArg (fun f : MulAut (UMod h91) => f w) h3
      simpa only [MulAut.mul_apply] using h4
    · left
      have h2 : rhoH h91 ((⟨x₀, hx₀H⟩ : ↥H) * ⟨(a : G), haH⟩ * (⟨x₀, hx₀H⟩ : ↥H)⁻¹ *
          ⟨(a : G), haH⟩) = 1 := (rhoH_eq_one_iff h91 _).mpr (by simpa using h1)
      rw [map_mul, map_mul, map_mul, map_inv] at h2
      intro w _
      have h2' : rhoH h91 ⟨x₀, hx₀H⟩ * rhoH h91 ⟨(a : G), haH⟩ * (rhoH h91 ⟨x₀, hx₀H⟩)⁻¹ =
          (rhoH h91 ⟨(a : G), haH⟩)⁻¹ := by
        calc rhoH h91 ⟨x₀, hx₀H⟩ * rhoH h91 ⟨(a : G), haH⟩ * (rhoH h91 ⟨x₀, hx₀H⟩)⁻¹ =
            (rhoH h91 ⟨x₀, hx₀H⟩ * rhoH h91 ⟨(a : G), haH⟩ * (rhoH h91 ⟨x₀, hx₀H⟩)⁻¹ *
              rhoH h91 ⟨(a : G), haH⟩) * (rhoH h91 ⟨(a : G), haH⟩)⁻¹ := by group
          _ = _ := by rw [h2, one_mul]
      have h3 : rhoH h91 ⟨(a : G), haH⟩ * rhoH h91 ⟨x₀, hx₀H⟩ * rhoH h91 ⟨(a : G), haH⟩ =
          rhoH h91 ⟨x₀, hx₀H⟩ := by
        calc rhoH h91 ⟨(a : G), haH⟩ * rhoH h91 ⟨x₀, hx₀H⟩ * rhoH h91 ⟨(a : G), haH⟩ =
            rhoH h91 ⟨(a : G), haH⟩ * (rhoH h91 ⟨x₀, hx₀H⟩ * rhoH h91 ⟨(a : G), haH⟩ *
              (rhoH h91 ⟨x₀, hx₀H⟩)⁻¹) * rhoH h91 ⟨x₀, hx₀H⟩ := by group
          _ = _ := by rw [h2']; group
      have h4 := congrArg (fun f : MulAut (UMod h91) => f w) h3
      simpa only [MulAut.mul_apply] using h4
  have hα2 : ∀ w ∈ Wsub h91 (uHi T M H H₁),
      rhoH h91 ⟨(a : G), haH⟩ (rhoH h91 ⟨(a : G), haH⟩ w) = w → w = 1 := by
    intro w hw hww
    obtain ⟨m, hm⟩ := hp.eq_two_or_odd'.resolve_left hp2
    have hper : Function.IsPeriodicPt (⇑(rhoH h91 ⟨(a : G), haH⟩)) 2 w := by
      show (⇑(rhoH h91 ⟨(a : G), haH⟩))^[2] w = w
      simpa using hww
    have h3 := hper.mul_const (m + 1)
    have e : 2 * (m + 1) = p + 1 := by omega
    rw [e] at h3
    have h4 : (⇑(rhoH h91 ⟨(a : G), haH⟩))^[p + 1] w = w := h3
    rw [Function.iterate_succ_apply] at h4
    rw [hpow _ (hαW w hw)] at h4
    exact hfixα w hw h4
  have hσW : ∀ w ∈ Wsub h91 (uHi T M H H₁), rhoH h91 ⟨x₀, hx₀H⟩ w ∈ Wsub h91 (uHi T M H H₁) :=
    fun w hw => rhoH_mem_Wsub h91 ⟨x₀, hx₀H⟩ hi₁ hx₀inv hw
  have hσ1 : ∃ w ∈ Wsub h91 (uHi T M H H₁), rhoH h91 ⟨x₀, hx₀H⟩ w ≠ w :=
    ⟨clsU h91 hu₀U, hw₁, fun e => hn ((rhoH_clsU_eq_iff h91 ⟨x₀, hx₀H⟩ hu₀U).mp e)⟩
  have hle4 : Nat.card (Wsub h91 (uHi T M H H₁)) ≤ 4 :=
    card_le_four_of_inv (rhoH h91 ⟨(a : G), haH⟩) (rhoH h91 ⟨x₀, hx₀H⟩)
      (Wsub h91 (uHi T M H H₁)) (clsU h91 hcU) (hF x₀ hx₀) hσW hfixα hα2 hrel hσ1
  have hp3' : p = 3 := by omega
  have hcard : Nat.card (Wsub h91 (uHi T M H H₁)) = 4 := by omega
  subst hp3'
  have hr : mIdx (uHi T M H H₁) (quasithinOmegaOneCenter T) = 2 := by
    have h1 : Nat.card (Wsub h91 (uHi T M H H₁)) =
        (quasithinOmegaOneCenter T).relIndex (uHi T M H H₁) := by
      rw [card_Wsub h91 hi₁]
      exact card_tildeOf_eq_relIndex hZ₁ (hi₁.trans hUZ)
    have h2 := HypF98.relIndex_eq_two_pow_mIdx (Y := quasithinOmegaOneCenter T) (hUp.to_le hi₁)
    rw [← h1, hcard] at h2
    have h3 : (2 : ℕ) ^ mIdx (uHi T M H H₁) (quasithinOmegaOneCenter T) = 2 ^ 2 := by
      rw [← h2]; norm_num
    exact Nat.pow_right_injective (le_refl 2) h3
  have hOF : IsOFourPlusOn T M H := h.isOFourPlusOn S hred hr
  refine ⟨rfl, hOF, g, tv.g_not, ?_, ?_, tv.U_le⟩
  · intro hle
    apply hn
    have h1 := hle (Subgroup.commutator_mem_commutator hu₀ hx₀)
    have e : x₀ * u₀ * x₀⁻¹ * u₀⁻¹ = (⁅u₀, x₀⁆)⁻¹ := by rw [commutatorElement_def]; group
    rw [e]
    exact (quasithinOmegaOneCenter T).inv_mem h1
  · intro x hx
    exact ⟨hUgH hx, mem_normalizer_of_conjSub_eq (hns x hx).2⟩

end Core

end CFSG.Quasithin
