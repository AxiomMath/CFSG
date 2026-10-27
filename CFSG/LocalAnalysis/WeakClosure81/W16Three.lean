module

public import CFSG.LocalAnalysis.WeakClosure81.W16Setup

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem le_preTil_fixV_actTil_mod {V₀ V C : Subgroup G} (hV : IsElemAbelian 2 V)
    {t : G} (hts : t ∈ stabTil V₀ V) (hCV : C ≤ V)
    (hCt : ∀ c ∈ C, t * c * t⁻¹ * c⁻¹ ∈ V₀) :
    C ≤ preTil V₀ V hV (fixV (Subgroup.zpowers (actTil V₀ V hV ⟨t, hts⟩))) := by
  intro c hc
  rw [mem_preTil_iff_of_mem V₀ V hV _ (hCV hc)]
  rw [mem_fixV_zpowers, actTil_mk, mkTil_eq_iff, actStab_apply_val]
  exact hCt c hc

theorem mem_cTilde_of_mQuot_lt_mod {M V₀ V : Subgroup G} (hV : IsElemAbelian 2 V) (hV₀ : V₀ ≤ V)
    (hM : M ≤ Subgroup.normalizer (V : Set G))
    (hM₀ : M ≤ Subgroup.normalizer (V₀ : Set G)) {t : G} (ht : t ∈ M)
    (ht2 : ∃ k : ℕ, orderOf t = 2 ^ k) {C : Subgroup G} (hCV : C ≤ V)
    (hCt : ∀ c ∈ C, t * c * t⁻¹ * c⁻¹ ∈ V₀)
    (hlt : (E3.mQuot V C : ℕ∞) < (mBar M V₀ V hV : ℕ∞)) :
    t ∈ F11.CTilde M V₀ V := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hMs : M ≤ stabTil V₀ V := le_inf hM hM₀
  have hts : t ∈ stabTil V₀ V := hMs ht
  by_contra hmem
  have hφ1 : actTil V₀ V hV ⟨t, hts⟩ ≠ 1 := by
    intro h1
    exact hmem ((mem_cTilde_iff hV hM).2 ⟨ht, hts, h1⟩)
  obtain ⟨k, hk⟩ := ht2
  have hgorder : orderOf (⟨t, hts⟩ : stabTil V₀ V) = 2 ^ k := by
    rw [← Subgroup.orderOf_coe (⟨t, hts⟩ : stabTil V₀ V), hk]
  have horder : orderOf (actTil V₀ V hV ⟨t, hts⟩) ∣ 2 ^ k := by
    rw [← hgorder]
    exact orderOf_map_dvd (actTil V₀ V hV) ⟨t, hts⟩
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 horder
  have hAp : IsPGroup 2 (Subgroup.zpowers (actTil V₀ V hV ⟨t, hts⟩)) :=
    IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
  have hφmem : actTil V₀ V hV ⟨t, hts⟩ ∈ Mbar M V₀ V hV :=
    actTil_mem_barSub V₀ V hV ht hts
  have hAle : Subgroup.zpowers (actTil V₀ V hV ⟨t, hts⟩) ≤ Mbar M V₀ V hV :=
    Subgroup.zpowers_le.2 hφmem
  have hA1 : Subgroup.zpowers (actTil V₀ V hV ⟨t, hts⟩) ≠ ⊥ := by
    intro hbot
    have : actTil V₀ V hV ⟨t, hts⟩ ∈ (⊥ : Subgroup (MulAut (Vtil V₀ V hV))) := by
      rw [← hbot]; exact Subgroup.mem_zpowers _
    exact hφ1 (Subgroup.mem_bot.1 this)
  have h1 : mBar M V₀ V hV ≤ rkIdx (fixV (Subgroup.zpowers (actTil V₀ V hV ⟨t, hts⟩))) :=
    E3.mParam_le_rkIdx_fixV hAle hAp hA1
  have h2 : rkIdx (fixV (Subgroup.zpowers (actTil V₀ V hV ⟨t, hts⟩))) ≤ E3.mQuot V C := by
    rw [← mQuot_preTil V₀ V hV (fixV (Subgroup.zpowers (actTil V₀ V hV ⟨t, hts⟩)))]
    exact E3.mQuot_mono (le_preTil_fixV_actTil_mod hV hts hCV hCt)
  have hbar : (mBar M V₀ V hV : ℕ∞) ≤ (E3.mQuot V C : ℕ∞) := by
    exact_mod_cast (h1.trans h2)
  exact absurd (lt_of_lt_of_le hlt hbar) (lt_irrefl _)

namespace Cex16

variable {M V₀ V U S : Subgroup G}

theorem comm_mem_V₀_of_mem_sup (h : Cex16 M V₀ V U S) {t : G} (ht : t ∈ M ⊓ centralizer (U : Set G))
    {c : G} (hc : c ∈ U ⊔ V₀) : t * c * t⁻¹ * c⁻¹ ∈ V₀ := by
  have hH := h.hyp
  obtain ⟨u, hu, w, hw, rfl⟩ := h.exists_mul_of_mem_sup hc
  have htN : t ∈ normalizer (V₀ : Set G) := hH.h6.le_normalizer₀ ht.1
  have htu : t * u * t⁻¹ = u := by
    rw [mul_inv_eq_iff_eq_mul]
    exact (Subgroup.mem_centralizer_iff.1 ht.2 u hu).symm
  have htw : t * w * t⁻¹ ∈ V₀ := (Subgroup.mem_normalizer_iff.1 htN w).1 hw
  have huN : u ∈ normalizer (V₀ : Set G) := hH.h6.le_normalizer₀ (hH.le_M (h.le hu))
  have e : t * (u * w) * t⁻¹ * (u * w)⁻¹ = u * ((t * w * t⁻¹) * w⁻¹) * u⁻¹ := by
    calc t * (u * w) * t⁻¹ * (u * w)⁻¹
        = (t * u * t⁻¹) * (t * w * t⁻¹) * w⁻¹ * u⁻¹ := by group
      _ = u * ((t * w * t⁻¹) * w⁻¹) * u⁻¹ := by rw [htu]; group
  rw [e]
  have hin : (t * w * t⁻¹) * w⁻¹ ∈ V₀ := V₀.mul_mem htw (V₀.inv_mem hw)
  have := (Subgroup.mem_normalizer_iff.1 huN _).1 hin
  exact this

theorem mem_cTilde_of_orderOf (h : Cex16 M V₀ V U S) {t : G}
    (ht : t ∈ M ⊓ centralizer (U : Set G)) (ht2 : ∃ k : ℕ, orderOf t = 2 ^ k) :
    t ∈ F11.CTilde M V₀ V := by
  have hlt : (E3.mQuot V (U ⊔ V₀) : ℕ∞) < (mBar M V₀ V h.hyp.h6.elemAbelian : ℕ∞) := by
    exact_mod_cast h.n_lt_mBar
  exact mem_cTilde_of_mQuot_lt_mod h.hyp.h6.elemAbelian h.hyp.h6.le
    h.hyp.h6.normalizer_eq.symm.le h.hyp.normalizer₀.symm.le ht.1 ht2 (sup_le h.le h.hyp.h6.le)
    (fun _ hc => h.comm_mem_V₀_of_mem_sup ht hc) hlt

theorem S_le_cTilde (h : Cex16 M V₀ V U S) : S ≤ F11.CTilde M V₀ V := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro t ht
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 h.sylow.isPGroup) ⟨t, ht⟩
  exact h.mem_cTilde_of_orderOf (h.sylow.le ht)
    ⟨k, by rw [← hk]; exact Subgroup.orderOf_coe (⟨t, ht⟩ : S)⟩

theorem comm_mem_V₀ (h : Cex16 M V₀ V U S) {s v : G} (hs : s ∈ S) (hv : v ∈ V) :
    s * v * s⁻¹ * v⁻¹ ∈ V₀ :=
  (FourteenTwo.mem_cTilde_iff_comm.1 (h.S_le_cTilde hs)).2.2 v hv

end Cex16

end CFSG.LocalAnalysis.WeakClosure81
