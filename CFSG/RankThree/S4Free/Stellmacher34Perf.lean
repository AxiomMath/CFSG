module

public import CFSG.RankThree.S4Free.Stellmacher34Core
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC165Lift
import CFSG.Quasithin.EmptyFaithful.S151V0

public section

namespace CFSG.RankThree.S4Free.Stell34

open Subgroup CFSG.Blueprint
open CFSG.RankThree.S4Free.Stell33 (LCfgCore)
open scoped commutatorElement Pointwise

variable {Λ : Type*} [Group Λ]

namespace SzCfg

variable [Finite Λ] {T W R : Subgroup Λ} {a : ℕ} {K : Type} [Field K] [Finite K]
  {φ : Λ →* suzukiGroup a K}

open CFSG.RankThree.S4Free.Stell33.LCfg (Wu A B X)

theorem comm_mem_A (h : SzCfg T W R φ) {r : Λ} (hr : r ∈ R) {w : Λ} (hw : w ∈ W) :
    r⁻¹ * w⁻¹ * r * w ∈ A W (oTwo Λ) := by
  have h1 : r⁻¹ * w⁻¹ * r * w ∈ W := by
    have hrN := h.ker_le_normalizer (inv_mem hr)
    have := (mem_normalizer_iff.mp hrN w⁻¹).mp (inv_mem hw)
    rw [inv_inv] at this
    exact mul_mem this hw
  have h2 : r⁻¹ * w⁻¹ * r * w ∈ R := by
    have := h.normal_R.conj_mem r hr w⁻¹
    rw [inv_inv] at this
    have h3 := mul_mem (inv_mem hr) this
    rwa [show r⁻¹ * (w⁻¹ * r * w) = r⁻¹ * w⁻¹ * r * w by group] at h3
  exact ⟨h1, h.inf_ker_le_oTwo ⟨h1, h2⟩⟩

theorem comm_mem_X (h : SzCfg T W R φ) {u : Λ} (hc : LCfgCore (⊤ : Subgroup Λ) W (oTwo Λ) u)
    {r : Λ} (hr : r ∈ R) (g : Λ) : r⁻¹ * g⁻¹ * r * g ∈ X W (oTwo Λ) u := by
  haveI : (X W (oTwo Λ) u).Normal :=
    normalizer_eq_top_iff.mp (top_le_iff.mp hc.L_le_normalizer_X)
  set C : Subgroup Λ := (centralizer {(QuotientGroup.mk' (X W (oTwo Λ) u) r)}).comap
    (QuotientGroup.mk' (X W (oTwo Λ) u)) with hC
  have hmem : ∀ g : Λ, g ∈ C ↔ r⁻¹ * g⁻¹ * r * g ∈ X W (oTwo Λ) u := by
    intro g
    rw [hC, mem_comap, mem_centralizer_singleton_iff, QuotientGroup.mk'_apply,
      QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    rw [show (g * r)⁻¹ * (r * g) = r⁻¹ * g⁻¹ * r * g by group]
  have hWC : W ≤ C := fun w hw => (hmem w).mpr (mem_sup_left (h.comm_mem_A hr hw))
  have hWuC : Wu W u ≤ C := by
    rintro _ ⟨w, hw, rfl⟩
    rw [hmem]
    have hr' : u⁻¹ * r * u ∈ R := by
      have := h.normal_R.conj_mem r hr u⁻¹
      rwa [inv_inv] at this
    have ha := h.comm_mem_A hr' hw
    have hb : u * ((u⁻¹ * r * u)⁻¹ * w⁻¹ * (u⁻¹ * r * u) * w) * u⁻¹ ∈ B W (oTwo Λ) u := by
      rw [← hc.map_conj_A]
      exact Stell33.conj_mem_map_conj ha
    have e : u * ((u⁻¹ * r * u)⁻¹ * w⁻¹ * (u⁻¹ * r * u) * w) * u⁻¹ =
        r⁻¹ * ((MulAut.conj u).toMonoidHom w)⁻¹ * r * (MulAut.conj u).toMonoidHom w := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [e] at hb
    exact mem_sup_right hb
  have htop : (⊤ : Subgroup Λ) ≤ C := by
    rw [← hc.sup_eq]
    exact sup_le hWC hWuC
  exact (hmem g).mp (htop (mem_top g))

theorem map_normalizer_T (h : SzCfg T W R φ) :
    normalizer ((T.map φ : Subgroup (suzukiGroup a K)) : Set (suzukiGroup a K)) =
      (normalizer (T : Set Λ)).map φ := by
  rw [CFSG.LocalAnalysis.UniquenessCase.PartTwo.Om8Lift.map_normalizer_sylow φ Nat.prime_two
    h.isPGroup_T h.not_dvd_index, MonoidHom.range_eq_top.mpr h.surjective, inf_top_eq]

theorem coe_sylowT_map (h : SzCfg T W R φ) :
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    ((h.sylowT.mapSurjective h.surjective : Sylow 2 (suzukiGroup a K)) :
      Subgroup (suzukiGroup a K)) = T.map φ := by
  rw [Sylow.coe_mapSurjective, h.coe_sylowT]

theorem map_W_eq_center (h : SzCfg T W R φ) :
    W.map φ = T.map φ ⊓ centralizer ((T.map φ : Subgroup (suzukiGroup a K)) : Set _) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set TS := h.sylowT.mapSurjective h.surjective with hTS
  have hcoe : (TS : Subgroup (suzukiGroup a K)) = T.map φ := h.coe_sylowT_map
  have hWS : W.map φ ≤ TS := hcoe ▸ map_mono h.W_le_T
  have hN : normalizer ((TS : Subgroup (suzukiGroup a K)) : Set (suzukiGroup a K)) ≤
      normalizer ((W.map φ : Subgroup (suzukiGroup a K)) : Set (suzukiGroup a K)) := by
    rw [hcoe, h.map_normalizer_T]
    exact (map_mono h.normalizer_le).trans (le_normalizer_map φ)
  rcases Suzuki.eq_bot_or_eq_center_or_eq_sylow h.one_le h.card_K (MulEquiv.refl _) TS hWS hN
    with h1 | h1 | h1
  · exfalso
    have hWR : W ≤ R := h.ker_eq ▸ (Subgroup.map_eq_bot_iff W).mp h1
    haveI := h.normal_R
    exact h.R_ne_top (h.eq_top_of_le hWR)
  · rw [h1, hcoe]
  · exfalso
    have hcard := Suzuki.card_sylow_and_center h.one_le h.card_K (MulEquiv.refl _) TS
    have hab : (TS : Subgroup (suzukiGroup a K)) ≤
        centralizer ((TS : Subgroup (suzukiGroup a K)) : Set (suzukiGroup a K)) := by
      rw [← h1]
      intro x hx
      rw [mem_centralizer_iff]
      intro y hy
      obtain ⟨v, hv, rfl⟩ := hx
      obtain ⟨w, hw, rfl⟩ := hy
      rw [← map_mul, ← map_mul, h.comm_W hw hv]
    rw [inf_eq_left.mpr hab, hcard.1] at hcard
    have h2 := hcard.2.1
    have : 2 ≤ 2 ^ (2 * a + 1) := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    nlinarith

theorem le_commutator_sup (h : SzCfg T W R φ) {u : Λ}
    (hc : LCfgCore (⊤ : Subgroup Λ) W (oTwo Λ) u) : W ≤ commutator Λ ⊔ X W (oTwo Λ) u := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set TS := h.sylowT.mapSurjective h.surjective with hTS
  have hcoe : (TS : Subgroup (suzukiGroup a K)) = T.map φ := h.coe_sylowT_map
  obtain ⟨c, hcN, hcfix⟩ := exists_fpf_center h.one_le h.card_K (MulEquiv.refl _) TS
  rw [hcoe] at hcN hcfix
  rw [h.map_normalizer_T] at hcN
  obtain ⟨k, hkN, rfl⟩ := hcN
  have hkW := h.normalizer_le hkN
  have hcN : φ k ∈ normalizer ((T.map φ : Subgroup (suzukiGroup a K)) : Set _) := by
    rw [h.map_normalizer_T]
    exact mem_map_of_mem φ hkN
  set E := T.map φ ⊓ centralizer ((T.map φ : Subgroup (suzukiGroup a K)) : Set _) with hE
  have hEc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    mem_centralizer_iff.mp hy.2 x hx.1
  have hcE : ∀ x ∈ E, φ k * x * (φ k)⁻¹ ∈ E := by
    intro x hx
    refine ⟨(mem_normalizer_iff.mp hcN x).mp hx.1, mem_centralizer_iff.mpr fun t ht => ?_⟩
    have ht' : (φ k)⁻¹ * t * (φ k)⁻¹⁻¹ ∈ T.map φ := (mem_normalizer_iff.mp (inv_mem hcN) t).mp ht
    rw [inv_inv] at ht'
    have hxt := mem_centralizer_iff.mp hx.2 _ ht'
    calc t * (φ k * x * (φ k)⁻¹) = φ k * ((φ k)⁻¹ * t * φ k * x) * (φ k)⁻¹ := by group
      _ = φ k * (x * ((φ k)⁻¹ * t * φ k)) * (φ k)⁻¹ := by rw [hxt]
      _ = φ k * x * (φ k)⁻¹ * t := by group
  have hsurj := (CFSG.Quasithin.fpf_iff_surj hEc hcE).mp hcfix
  intro w hw
  have hφw : φ w ∈ E := by
    rw [hE, ← h.map_W_eq_center]
    exact mem_map_of_mem φ hw
  obtain ⟨v, hvE, hv⟩ := hsurj (φ w) hφw
  rw [hE, ← h.map_W_eq_center] at hvE
  obtain ⟨w', hw', rfl⟩ := hvE
  have hcw : ⁅w', k⁆ ∈ W := by
    have h1 := (mem_normalizer_iff.mp hkW w'⁻¹).mp (inv_mem hw')
    rw [commutatorElement_def, show w' * k * w'⁻¹ * k⁻¹ = w' * (k * w'⁻¹ * k⁻¹) by group]
    exact mul_mem hw' h1
  have hρR : ⁅w', k⁆⁻¹ * w ∈ R := by
    rw [← h.ker_eq, MonoidHom.mem_ker, map_mul, map_inv, map_commutatorElement, hv,
      inv_mul_cancel]
  have hρW : ⁅w', k⁆⁻¹ * w ∈ W := mul_mem (inv_mem hcw) hw
  have hρX : ⁅w', k⁆⁻¹ * w ∈ X W (oTwo Λ) u :=
    mem_sup_left ⟨hρW, h.inf_ker_le_oTwo ⟨hρW, hρR⟩⟩
  have hcomm : ⁅w', k⁆ ∈ commutator Λ := by
    rw [_root_.commutator_def]
    exact commutator_mem_commutator (mem_top _) (mem_top _)
  have := mul_mem (mem_sup_left hcomm : ⁅w', k⁆ ∈ commutator Λ ⊔ X W (oTwo Λ) u)
    (mem_sup_right hρX)
  rwa [mul_inv_cancel_left] at this

theorem commutator_sup_eq_top (h : SzCfg T W R φ) {u : Λ}
    (hc : LCfgCore (⊤ : Subgroup Λ) W (oTwo Λ) u) : commutator Λ ⊔ X W (oTwo Λ) u = ⊤ := by
  haveI : (X W (oTwo Λ) u).Normal :=
    normalizer_eq_top_iff.mp (top_le_iff.mp hc.L_le_normalizer_X)
  haveI : (commutator Λ ⊔ X W (oTwo Λ) u).Normal := Subgroup.sup_normal _ _
  exact h.eq_top_of_le (h.le_commutator_sup hc)

theorem eq_oTwo_and_eq_X (h : SzCfg T W R φ) {u : Λ}
    (hc : LCfgCore (⊤ : Subgroup Λ) W (oTwo Λ) u) :
    R = oTwo Λ ∧ oTwo Λ = X W (oTwo Λ) u := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Xs := X W (oTwo Λ) u with hXs
  haveI hXn : Xs.Normal := normalizer_eq_top_iff.mp (top_le_iff.mp hc.L_le_normalizer_X)
  haveI hRn : R.Normal := h.normal_R
  have hXR : Xs ≤ R := hc.X_le_P.trans h.oTwo_le
  set π := QuotientGroup.mk' Xs with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective Xs
  haveI : (R.map π).Normal := hRn.map π hπs
  have hZc : R.map π ≤ center (Λ ⧸ Xs) := by
    rintro _ ⟨r, hr, rfl⟩
    rw [mem_center_iff]
    intro q
    obtain ⟨g, rfl⟩ := hπs q
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul,
      ← QuotientGroup.mk_mul, QuotientGroup.eq,
      show (g * r)⁻¹ * (r * g) = r⁻¹ * g⁻¹ * r * g by group]
    exact h.comm_mem_X hc hr g
  have hZd : R.map π ≤ commutator (Λ ⧸ Xs) := by
    have hc' : commutator (Λ ⧸ Xs) = ⊤ := by
      have h1 := congrArg (Subgroup.map π) (h.commutator_sup_eq_top hc)
      have h2 : Xs.map π = ⊥ := by rw [Subgroup.map_eq_bot_iff, hπ, QuotientGroup.ker_mk']
      rw [Subgroup.map_sup, map_top_of_surjective π hπs, h2, sup_bot_eq, map_commutator_eq,
        MonoidHom.range_eq_top.mpr hπs, ← _root_.commutator_def] at h1
      exact h1
    rw [hc']
    exact le_top
  let e : (Λ ⧸ Xs) ⧸ R.map π ≃* suzukiGroup a K :=
    (QuotientGroup.quotientQuotientEquivQuotient Xs R hXR).trans
      ((QuotientGroup.quotientMulEquivOfEq h.ker_eq.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective φ h.surjective))
  set S7 := h.sylowT.mapSurjective hπs with hS7
  have hS7c : (S7 : Subgroup (Λ ⧸ Xs)) = T.map π := by
    rw [hS7, Sylow.coe_mapSurjective, h.coe_sylowT]
  have hWS : W.map π ≤ S7 := hS7c ▸ map_mono h.W_le_T
  have hWN : normalizer ((S7 : Subgroup (Λ ⧸ Xs)) : Set (Λ ⧸ Xs)) ≤
      normalizer ((W.map π : Subgroup (Λ ⧸ Xs)) : Set (Λ ⧸ Xs)) := by
    have hm := CFSG.LocalAnalysis.UniquenessCase.PartTwo.Om8Lift.map_normalizer_sylow π
      Nat.prime_two h.isPGroup_T h.not_dvd_index
    rw [MonoidHom.range_eq_top.mpr hπs, inf_top_eq] at hm
    rw [hS7c, ← hm]
    exact (map_mono h.normalizer_le).trans (le_normalizer_map π)
  rcases Stell.le_or_le_of_mulEquiv_suzukiGroup hZc hZd h.one_le h.card_K e S7 hWS hWN with
    h1 | h1
  ·
    have hRle : R ≤ W ⊔ Xs := by
      intro r hr
      have h2 : π r ∈ W.map π := h1 (mem_map_of_mem π hr)
      rw [← mem_comap, comap_map_eq, hπ, QuotientGroup.ker_mk'] at h2
      exact h2
    have hWX2 : W ⊔ Xs ≤ T := sup_le h.W_le_T (hc.X_le_P.trans h.oTwo_le_T)
    have hR2 : IsPGroup 2 R := h.isPGroup_T.to_le (hRle.trans hWX2)
    have hReq : R = oTwo Λ := le_antisymm (Stell.le_oTwo hR2) h.oTwo_le
    refine ⟨hReq, le_antisymm ?_ hc.X_le_P⟩
    intro g hg
    have hg' : g ∈ W ⊔ Xs := hRle (h.oTwo_le hg)
    rw [← SetLike.mem_coe, Subgroup.mul_normal W Xs] at hg'
    obtain ⟨w, hw, x, hx, rfl⟩ := hg'
    have hwO : w ∈ oTwo Λ := by
      have := mul_mem hg (inv_mem (hc.X_le_P hx))
      rwa [mul_inv_cancel_right] at this
    exact mul_mem (mem_sup_left ⟨hw, hwO⟩) hx
  ·
    exfalso
    have hWR : W ≤ R := by
      intro w hw
      have h2 : π w ∈ R.map π := h1 (mem_map_of_mem π hw)
      rw [← mem_comap, comap_map_eq, hπ, QuotientGroup.ker_mk', sup_eq_left.mpr hXR] at h2
      exact h2
    exact h.R_ne_top (h.eq_top_of_le hWR)


end SzCfg

end CFSG.RankThree.S4Free.Stell34
