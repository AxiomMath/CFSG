module

public import CFSG.Quasithin.EmptyFaithful.S146zLDH
public import CFSG.Quasithin.EmptyFaithful.S146zLCnt

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7 CFSG.Quasithin.C1Pack
  CFSG.Quasithin.CosetGeom
open scoped commutatorElement Pointwise

section Mod

variable {G : Type} [Group G] [Finite G] {T M H : Subgroup G} {p : ℕ} {H₀ H₁ H₂ : Subgroup G} {t : G}

theorem IsDecP.rot_free (S : Setting146 G T M) {PQ : Subgroup G} (hred : IsRedCE T M H PQ p)
    (h : IsDecP T M H p H₀ H₁ H₂ t)
    (h91 : HypF91 T (VZ T M) (yOfL22 T M) (quasithinOmegaOneCenter T) (VZ T M) H)
    (φ : ↥H₁ →* DihedralGroup p) (hker : ∀ y : ↥H₁, φ y = 1 ↔ (y : G) ∈ pCoreOf 2 H)
    {a : ↥H₁} (ha : φ a = DihedralGroup.r 1) :
    (∀ w ∈ Wsub h91 (uHi T M H H₁),
      rhoH h91 ⟨(a : G), h.le (h.le₁ a.2)⟩ w ∈ Wsub h91 (uHi T M H H₁)) ∧
    (∀ w ∈ Wsub h91 (uHi T M H H₁),
      rhoH h91 ⟨(a : G), h.le (h.le₁ a.2)⟩ (rhoH h91 ⟨(a : G), h.le (h.le₁ a.2)⟩ w) = w →
        w = 1) := by
  have hp : p.Prime := hred.prime
  have hp2 : p ≠ 2 := hred.odd
  have haH : (a : G) ∈ H := h.le (h.le₁ a.2)
  have hi₁ : uHi T M H H₁ ≤ conjClosure (VZ T M) H := uHi_le_conjClosure (h.le₁.trans h.le)
  have hαinv : conjSub (a : G) (uHi T M H H₁) = uHi T M H H₁ :=
    conjSub_eq_of_mem_normalizer (h.le_normalizer_uHi₁ S hred (h.le₁ a.2))
  have hαW : ∀ w ∈ Wsub h91 (uHi T M H H₁),
      rhoH h91 ⟨(a : G), haH⟩ w ∈ Wsub h91 (uHi T M H H₁) :=
    fun w hw => rhoH_mem_Wsub h91 ⟨(a : G), haH⟩ hi₁ hαinv hw
  refine ⟨hαW, fun w hw hww => ?_⟩
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (1 < p) := ⟨hp.one_lt⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  have hfixα : ∀ w ∈ Wsub h91 (uHi T M H H₁), rhoH h91 ⟨(a : G), haH⟩ w = w → w = 1 :=
    fun w hw hwf => h.eq_one_of_fix S hred h91 φ hker ha hw hwf
  have hapQ : (a : G) ^ p ∈ pCoreOf 2 H := by
    have h1 : φ (a ^ p) = 1 := by rw [map_pow, ha]; exact DihedralGroup.r_one_pow_n
    simpa using (hker _).mp h1
  have hpow : ∀ w ∈ Wsub h91 (uHi T M H H₁),
      (⇑(rhoH h91 ⟨(a : G), haH⟩))^[p] w = w := by
    intro w _
    rw [iterate_eq_pow_mulAut, ← map_pow]
    have h1 : rhoH h91 ((⟨(a : G), haH⟩ : ↥H) ^ p) = 1 :=
      (rhoH_eq_one_iff h91 _).mpr (by simpa using hapQ)
    rw [h1]
    rfl
  have hP2 : Function.IsPeriodicPt (⇑(rhoH h91 ⟨(a : G), haH⟩)) 2 w := hww
  have hPp : Function.IsPeriodicPt (⇑(rhoH h91 ⟨(a : G), haH⟩)) p w := hpow w hw
  have hg := hP2.gcd hPp
  have hcop : Nat.gcd 2 p = 1 := (Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2)
  rw [hcop] at hg
  exact hfixα w hw hg

theorem IsDecP.card_fix_inv_le (S : Setting146 G T M) {PQ : Subgroup G}
    (hred : IsRedCE T M H PQ p) (h : IsDecP T M H p H₀ H₁ H₂ t)
    (h91 : HypF91 T (VZ T M) (yOfL22 T M) (quasithinOmegaOneCenter T) (VZ T M) H)
    (φ : ↥H₁ →* DihedralGroup p) (hker : ∀ y : ↥H₁, φ y = 1 ↔ (y : G) ∈ pCoreOf 2 H)
    {a : ↥H₁} (ha : φ a = DihedralGroup.r 1)
    (hcard : Nat.card (Wsub h91 (uHi T M H H₁)) = 16) {w : G} (hwH : w ∈ H)
    (hinv : w * (a : G) * w⁻¹ * (a : G) ∈ pCoreOf 2 H) :
    Nat.card ↥(fixSubOf (rhoH h91 ⟨w, hwH⟩) ⊓ Wsub h91 (uHi T M H H₁)) ≤ 4 := by
  have haH : (a : G) ∈ H := h.le (h.le₁ a.2)
  obtain ⟨hαW, hα2⟩ := h.rot_free S hred h91 φ hker ha
  have h3 : rhoH h91 ⟨w, hwH⟩ * rhoH h91 ⟨(a : G), haH⟩ * (rhoH h91 ⟨w, hwH⟩)⁻¹ *
      rhoH h91 ⟨(a : G), haH⟩ = 1 := by
    have h1 : rhoH h91 (⟨w, hwH⟩ * ⟨(a : G), haH⟩ * ⟨w, hwH⟩⁻¹ * ⟨(a : G), haH⟩) = 1 :=
      (rhoH_eq_one_iff h91 _).mpr hinv
    rw [map_mul, map_mul, map_mul, map_inv] at h1
    exact h1
  set α := rhoH h91 ⟨(a : G), haH⟩ with hα
  set σ := rhoH h91 ⟨w, hwH⟩ with hσ
  have h4 : σ * α * σ⁻¹ = α⁻¹ := eq_inv_of_mul_eq_one_left h3
  have h5 : σ * α = α⁻¹ * σ := by
    calc σ * α = (σ * α * σ⁻¹) * σ := by group
      _ = α⁻¹ * σ := by rw [h4]
  have h6 : α * σ * α = σ := by
    calc α * σ * α = α * (σ * α) := by group
      _ = α * (α⁻¹ * σ) := by rw [h5]
      _ = σ := by group
  have hinvpw : ∀ x ∈ Wsub h91 (uHi T M H H₁), α (σ (α x)) = σ x := by
    intro x _
    have := congrArg (fun f : MulAut (UMod h91) => f x) h6
    simpa [MulAut.mul_apply] using this
  have hsq := card_fix_sq_le α σ (Wsub h91 (uHi T M H H₁)) hαW hα2 hinvpw
  rw [hcard] at hsq
  by_contra hgt
  push Not at hgt
  nlinarith


theorem IsDecP.card_W_sup (h : IsDecP T M H p H₀ H₁ H₂ t)
    (h91 : HypF91 T (VZ T M) (yOfL22 T M) (quasithinOmegaOneCenter T) (VZ T M) H)
    (hcard₁ : Nat.card (Wsub h91 (uHi T M H H₁)) = 16)
    (hcard₂ : Nat.card (Wsub h91 (uHi T M H H₂)) = 16) :
    Wsub h91 (uHi T M H H₁) ⊓ Wsub h91 (uHi T M H H₂) = ⊥ ∧
      Nat.card ↥(Wsub h91 (uHi T M H H₁) ⊔ Wsub h91 (uHi T M H H₂)) = 256 := by
  have hi₁ : uHi T M H H₁ ≤ conjClosure (VZ T M) H := uHi_le_conjClosure (h.le₁.trans h.le)
  have hi₂ : uHi T M H H₂ ≤ conjClosure (VZ T M) H := uHi_le_conjClosure (h.le₂.trans h.le)
  have hinf : Wsub h91 (uHi T M H H₁) ⊓ Wsub h91 (uHi T M H H₂) = ⊥ :=
    Wsub_inf_eq_bot h91 hi₁ hi₂ (Z_le_uHi T M H H₁) h.dir_inf.le
  refine ⟨hinf, ?_⟩
  have h1 := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute (Wsub h91 (uHi T M H H₁))
    (Wsub h91 (uHi T M H H₂)) (fun x _ y _ => mul_comm x y)).1
  rw [hinf, Subgroup.card_bot, mul_one, hcard₁, hcard₂] at h1
  exact h1

theorem IsDecP.three_le_of_inv (S : Setting146 G T M) {PQ : Subgroup G}
    (hred : IsRedCE T M H PQ p) (h : IsDecP T M H p H₀ H₁ H₂ t)
    {δ δ' : F8.Geom T (yOfL22 T M) H} {k : ↥(((yOfL22 T M) ⊔ T) ⊔ H)}
    (sk : F8Setup T (VZ T M) (yOfL22 T M) H δ δ' k)
    (h91 : HypF91 T (VZ T M) (yOfL22 T M) (quasithinOmegaOneCenter T) (VZ T M) H)
    (hcard₁ : Nat.card (Wsub h91 (uHi T M H H₁)) = 16)
    (hcard₂ : Nat.card (Wsub h91 (uHi T M H H₂)) = 16)
    (φ₁ : ↥H₁ →* DihedralGroup p) (hker₁ : ∀ y : ↥H₁, φ₁ y = 1 ↔ (y : G) ∈ pCoreOf 2 H)
    {a₁ : ↥H₁} (ha₁ : φ₁ a₁ = DihedralGroup.r 1) (φ₂ : ↥H₂ →* DihedralGroup p)
    (hker₂ : ∀ y : ↥H₂, φ₂ y = 1 ↔ (y : G) ∈ pCoreOf 2 H) {a₂ : ↥H₂}
    (ha₂ : φ₂ a₂ = DihedralGroup.r 1) {w : G} (hw : w ∈ F8.Uγ (VZ T M) H (k : G)) (hwH : w ∈ H)
    (hinv₁ : w * (a₁ : G) * w⁻¹ * (a₁ : G) ∈ pCoreOf 2 H)
    (hinv₂ : w * (a₂ : G) * w⁻¹ * (a₂ : G) ∈ pCoreOf 2 H)
    (hw₁ : conjSub w (uHi T M H H₁) = uHi T M H H₁)
    (hw₂ : conjSub w (uHi T M H H₂) = uHi T M H H₂) :
    3 ≤ mIdx (conjClosure (VZ T M) H) (F8.DH (VZ T M) (quasithinOmegaOneCenter T) H (k : G)) := by
  have hH : IsHTM T M H := hred.isHTM
  have hi₁ : uHi T M H H₁ ≤ conjClosure (VZ T M) H := uHi_le_conjClosure (h.le₁.trans h.le)
  have hi₂ : uHi T M H H₂ ≤ conjClosure (VZ T M) H := uHi_le_conjClosure (h.le₂.trans h.le)
  obtain ⟨hinf, h256⟩ := h.card_W_sup h91 hcard₁ hcard₂
  have hC₁ := h.card_fix_inv_le S hred h91 φ₁ hker₁ ha₁ hcard₁ hwH hinv₁
  have hC₂ := h.swap.card_fix_inv_le S hred h91 φ₂ hker₂ ha₂ hcard₂ hwH hinv₂
  have hfix := card_fix_sup_le (rhoH h91 ⟨w, hwH⟩) _ _ hinf
    (fun x hx => rhoH_mem_Wsub h91 ⟨w, hwH⟩ hi₁ hw₁ hx)
    (fun x hx => rhoH_mem_Wsub h91 ⟨w, hwH⟩ hi₂ hw₂ hx)
  have hfix16 : Nat.card ↥(fixSubOf (rhoH h91 ⟨w, hwH⟩) ⊓
      (Wsub h91 (uHi T M H H₁) ⊔ Wsub h91 (uHi T M H H₂))) ≤ 16 :=
    hfix.trans (by nlinarith)
  have hidx := index_ge_of_inf_le (fixSubOf (rhoH h91 ⟨w, hwH⟩)) _ hfix16
  rw [h256] at hidx
  have hup := Setting146.index_fix_le S hH sk h91 hw hwH
  have h3 : 8 ≤ 2 ^ mIdx (conjClosure (VZ T M) H)
      (F8.DH (VZ T M) (quasithinOmegaOneCenter T) H (k : G)) := by omega
  exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp (by simpa using h3 : 2 ^ 3 ≤ _)

theorem IsDecP.three_le_of_swap (S : Setting146 G T M) {PQ : Subgroup G}
    (hred : IsRedCE T M H PQ p) (h : IsDecP T M H p H₀ H₁ H₂ t)
    {δ δ' : F8.Geom T (yOfL22 T M) H} {k : ↥(((yOfL22 T M) ⊔ T) ⊔ H)}
    (sk : F8Setup T (VZ T M) (yOfL22 T M) H δ δ' k)
    (h91 : HypF91 T (VZ T M) (yOfL22 T M) (quasithinOmegaOneCenter T) (VZ T M) H)
    (hcard₁ : Nat.card (Wsub h91 (uHi T M H H₁)) = 16)
    (hcard₂ : Nat.card (Wsub h91 (uHi T M H H₂)) = 16)
    {w : G} (hw : w ∈ F8.Uγ (VZ T M) H (k : G)) (hwH : w ∈ H)
    (hs₁ : conjSub w (uHi T M H H₁) = uHi T M H H₂)
    (hs₂ : conjSub w (uHi T M H H₂) = uHi T M H H₁) :
    3 ≤ mIdx (conjClosure (VZ T M) H) (F8.DH (VZ T M) (quasithinOmegaOneCenter T) H (k : G)) := by
  have hH : IsHTM T M H := hred.isHTM
  have hi₁ : uHi T M H H₁ ≤ conjClosure (VZ T M) H := uHi_le_conjClosure (h.le₁.trans h.le)
  have hi₂ : uHi T M H H₂ ≤ conjClosure (VZ T M) H := uHi_le_conjClosure (h.le₂.trans h.le)
  obtain ⟨hinf, h256⟩ := h.card_W_sup h91 hcard₁ hcard₂
  have hfix := card_fix_swap_le (rhoH h91 ⟨w, hwH⟩) _ _ hinf
    (fun x hx => rhoH_mem_Wsub h91 ⟨w, hwH⟩ hi₁ hs₁ hx)
    (fun x hx => rhoH_mem_Wsub h91 ⟨w, hwH⟩ hi₂ hs₂ hx)
  rw [hcard₂] at hfix
  have hidx := index_ge_of_inf_le (fixSubOf (rhoH h91 ⟨w, hwH⟩)) _ hfix
  rw [h256] at hidx
  have hup := Setting146.index_fix_le S hH sk h91 hw hwH
  have h3 : 8 ≤ 2 ^ mIdx (conjClosure (VZ T M) H)
      (F8.DH (VZ T M) (quasithinOmegaOneCenter T) H (k : G)) := by omega
  exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp (by simpa using h3 : 2 ^ 3 ≤ _)

theorem IsDecP.four_le_of_swap_inv (S : Setting146 G T M) {PQ : Subgroup G}
    (hred : IsRedCE T M H PQ p) (h : IsDecP T M H p H₀ H₁ H₂ t)
    {δ δ' : F8.Geom T (yOfL22 T M) H} {k : ↥(((yOfL22 T M) ⊔ T) ⊔ H)}
    (sk : F8Setup T (VZ T M) (yOfL22 T M) H δ δ' k)
    (h91 : HypF91 T (VZ T M) (yOfL22 T M) (quasithinOmegaOneCenter T) (VZ T M) H)
    (hcard₁ : Nat.card (Wsub h91 (uHi T M H H₁)) = 16)
    (hcard₂ : Nat.card (Wsub h91 (uHi T M H H₂)) = 16)
    (φ₂ : ↥H₂ →* DihedralGroup p) (hker₂ : ∀ y : ↥H₂, φ₂ y = 1 ↔ (y : G) ∈ pCoreOf 2 H)
    {a₂ : ↥H₂} (ha₂ : φ₂ a₂ = DihedralGroup.r 1)
    {w : G} (hw : w ∈ F8.Uγ (VZ T M) H (k : G)) (hwH : w ∈ H)
    (hs₁ : conjSub w (uHi T M H H₁) = uHi T M H H₂)
    (hs₂ : conjSub w (uHi T M H H₂) = uHi T M H H₁)
    {y : G} (hy : y ∈ F8.Uγ (VZ T M) H (k : G)) (hyH : y ∈ H)
    (hinv₂ : y * (a₂ : G) * y⁻¹ * (a₂ : G) ∈ pCoreOf 2 H)
    (hy₁ : conjSub y (uHi T M H H₁) = uHi T M H H₁)
    (hy₂ : conjSub y (uHi T M H H₂) = uHi T M H H₂) :
    4 ≤ mIdx (conjClosure (VZ T M) H) (F8.DH (VZ T M) (quasithinOmegaOneCenter T) H (k : G)) := by
  have hH : IsHTM T M H := hred.isHTM
  have hi₁ : uHi T M H H₁ ≤ conjClosure (VZ T M) H := uHi_le_conjClosure (h.le₁.trans h.le)
  have hi₂ : uHi T M H H₂ ≤ conjClosure (VZ T M) H := uHi_le_conjClosure (h.le₂.trans h.le)
  obtain ⟨hinf, h256⟩ := h.card_W_sup h91 hcard₁ hcard₂
  have hC₂ := h.swap.card_fix_inv_le S hred h91 φ₂ hker₂ ha₂ hcard₂ hyH hinv₂
  have hfix := card_fix_swap_inter_le (rhoH h91 ⟨w, hwH⟩) (rhoH h91 ⟨y, hyH⟩) _ _ hinf
    (fun x hx => rhoH_mem_Wsub h91 ⟨w, hwH⟩ hi₁ hs₁ hx)
    (fun x hx => rhoH_mem_Wsub h91 ⟨w, hwH⟩ hi₂ hs₂ hx)
    (fun x hx => rhoH_mem_Wsub h91 ⟨y, hyH⟩ hi₁ hy₁ hx)
    (fun x hx => rhoH_mem_Wsub h91 ⟨y, hyH⟩ hi₂ hy₂ hx)
  have hfix4 : Nat.card ↥(fixSubOf (rhoH h91 ⟨w, hwH⟩) ⊓ fixSubOf (rhoH h91 ⟨y, hyH⟩) ⊓
      (Wsub h91 (uHi T M H H₁) ⊔ Wsub h91 (uHi T M H H₂))) ≤ 4 := hfix.trans hC₂
  have hidx := index_ge_of_inf_le (fixSubOf (rhoH h91 ⟨w, hwH⟩) ⊓ fixSubOf (rhoH h91 ⟨y, hyH⟩)) _
    hfix4
  rw [h256] at hidx
  have hup := Setting146.index_fix_le₂ S hH sk h91 hw hwH hy hyH
  have h3 : 16 ≤ 2 ^ mIdx (conjClosure (VZ T M) H)
      (F8.DH (VZ T M) (quasithinOmegaOneCenter T) H (k : G)) := by omega
  exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp (by simpa using h3 : 2 ^ 4 ≤ _)

end Mod

end CFSG.Quasithin
