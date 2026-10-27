module

public import CFSG.Quasithin.EmptyFaithful.S146zHNon
public import CFSG.Quasithin.EmptyFaithful.S146zHWsub

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7 CFSG.Quasithin.C1Pack
  CFSG.Quasithin.CosetGeom
open scoped commutatorElement Pointwise

section Quad

variable {G : Type} [Group G] [Finite G] {T M H : Subgroup G} {p : ℕ} {H₀ H₁ H₂ : Subgroup G} {t : G}

theorem qcrit_module (h91 : HypF91 T (VZ T M) (yOfL22 T M) (quasithinOmegaOneCenter T) (VZ T M) H)
    {B : Subgroup G} (hq : QCrit (quasithinOmegaOneCenter T) (VZ T M) H B) {b₁ b₂ : G}
    (hb₁ : b₁ ∈ B) (hb₂ : b₂ ∈ B) (w : UMod h91) :
    rhoH h91 ⟨b₂, hq.1 hb₂⟩ (rhoH h91 ⟨b₁, hq.1 hb₁⟩ w * w⁻¹) =
      rhoH h91 ⟨b₁, hq.1 hb₁⟩ w * w⁻¹ := by
  obtain ⟨u, hu, rfl⟩ := exists_clsU h91 w
  have hxu : b₁ * u * b₁⁻¹ * u⁻¹ ∈ conjClosure (VZ T M) H :=
    (conjClosure (VZ T M) H).mul_mem (conj_mem_UH (hq.1 hb₁) hu)
      ((conjClosure (VZ T M) H).inv_mem hu)
  have e : rhoH h91 ⟨b₁, hq.1 hb₁⟩ (clsU h91 hu) * (clsU h91 hu)⁻¹ = clsU h91 hxu := by
    rw [rhoH_clsU, clsU_inv h91 hu, clsU_mul]
  rw [e]
  exact (rhoH_clsU_eq_iff h91 ⟨b₂, hq.1 hb₂⟩ hxu).mpr (hq.2.2.2.1 b₁ hb₁ b₂ hb₂ u hu)

theorem IsDecP.mem_pCore_of_nonswap (S : Setting146 G T M) {PQ : Subgroup G}
    (hred : IsRedCE T M H PQ p) (h : IsDecP T M H p H₀ H₁ H₂ t)
    (h91 : HypF91 T (VZ T M) (yOfL22 T M) (quasithinOmegaOneCenter T) (VZ T M) H)
    {B : Subgroup G} (hq : QCrit (quasithinOmegaOneCenter T) (VZ T M) H B) {y z : G}
    (hy : y ∈ B) (hz : z ∈ B) (hyy : y * y = 1)
    (hsw : conjSub y (uHi T M H H₁) = uHi T M H H₂)
    (hsw' : conjSub y (uHi T M H H₂) = uHi T M H H₁)
    (hz₁ : conjSub z (uHi T M H H₁) = uHi T M H H₁)
    (hz₂ : conjSub z (uHi T M H H₂) = uHi T M H H₂) : z ∈ pCoreOf 2 H := by
  classical
  have hH : IsHTM T M H := hred.isHTM
  have hHN : H ≤ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) :=
    (S.le_mcOf hH).trans S.normalizer_Z.ge
  have hUZ : conjClosure (VZ T M) H ≤ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) :=
    S.conjClosure_le_normalizer_Z hH
  have hi₁ : uHi T M H H₁ ≤ conjClosure (VZ T M) H := uHi_le_conjClosure (h.le₁.trans h.le)
  have hi₂ : uHi T M H H₂ ≤ conjClosure (VZ T M) H := uHi_le_conjClosure (h.le₂.trans h.le)
  have hW : Wsub h91 (uHi T M H H₁) ⊓ Wsub h91 (uHi T M H H₂) = ⊥ :=
    Wsub_inf_eq_bot h91 hi₁ hi₂ (Z_le_uHi T M H H₁) h.dir_inf.le
  have hyH : y ∈ H := hq.1 hy
  have hzH : z ∈ H := hq.1 hz
  have hρyy : ∀ v : UMod h91, rhoH h91 ⟨y, hyH⟩ (rhoH h91 ⟨y, hyH⟩ v) = v := by
    intro v
    have h1 : rhoH h91 ⟨y, hyH⟩ * rhoH h91 ⟨y, hyH⟩ = 1 := by
      rw [← map_mul]
      have : (⟨y, hyH⟩ : ↥H) * ⟨y, hyH⟩ = 1 := Subtype.ext hyy
      rw [this, map_one]
    have := congrArg (fun f : MulAut (UMod h91) => f v) h1
    simpa only [MulAut.mul_apply, MulAut.one_apply] using this
  have hfix₁ : ∀ w ∈ Wsub h91 (uHi T M H H₁), rhoH h91 ⟨z, hzH⟩ w = w ∧
      rhoH h91 ⟨z, hzH⟩ (rhoH h91 ⟨y, hyH⟩ w) = rhoH h91 ⟨y, hyH⟩ w := by
    intro w hw
    have hc := qcrit_module h91 hq hy hz w
    rw [map_mul, map_inv] at hc
    have hyw : rhoH h91 ⟨y, hyH⟩ w ∈ Wsub h91 (uHi T M H H₂) :=
      rhoH_mem_Wsub h91 ⟨y, hyH⟩ hi₁ hsw hw
    have hzyw : rhoH h91 ⟨z, hzH⟩ (rhoH h91 ⟨y, hyH⟩ w) ∈ Wsub h91 (uHi T M H H₂) :=
      rhoH_mem_Wsub h91 ⟨z, hzH⟩ hi₂ hz₂ hyw
    have hzw : rhoH h91 ⟨z, hzH⟩ w ∈ Wsub h91 (uHi T M H H₁) :=
      rhoH_mem_Wsub h91 ⟨z, hzH⟩ hi₁ hz₁ hw
    have hAB : rhoH h91 ⟨z, hzH⟩ (rhoH h91 ⟨y, hyH⟩ w) * (rhoH h91 ⟨y, hyH⟩ w)⁻¹ =
        rhoH h91 ⟨z, hzH⟩ w * w⁻¹ := by
      rw [← div_eq_mul_inv, ← div_eq_mul_inv, div_eq_div_iff_mul_eq_mul]
      rw [← div_eq_mul_inv, ← div_eq_mul_inv, div_eq_div_iff_mul_eq_mul] at hc
      rw [hc, mul_comm]
    have hm₁ : rhoH h91 ⟨z, hzH⟩ w * w⁻¹ ∈ Wsub h91 (uHi T M H H₁) :=
      (Wsub h91 (uHi T M H H₁)).mul_mem hzw ((Wsub h91 (uHi T M H H₁)).inv_mem hw)
    have hm₂ : rhoH h91 ⟨z, hzH⟩ (rhoH h91 ⟨y, hyH⟩ w) * (rhoH h91 ⟨y, hyH⟩ w)⁻¹ ∈
        Wsub h91 (uHi T M H H₂) :=
      (Wsub h91 (uHi T M H H₂)).mul_mem hzyw ((Wsub h91 (uHi T M H H₂)).inv_mem hyw)
    have hmem : rhoH h91 ⟨z, hzH⟩ w * w⁻¹ ∈
        Wsub h91 (uHi T M H H₁) ⊓ Wsub h91 (uHi T M H H₂) := ⟨hm₁, hAB ▸ hm₂⟩
    rw [hW, Subgroup.mem_bot] at hmem
    have h1 : rhoH h91 ⟨z, hzH⟩ w = w := mul_inv_eq_one.mp hmem
    rw [hmem, mul_inv_eq_one] at hAB
    exact ⟨h1, hAB⟩
  have hfix₂ : ∀ w ∈ Wsub h91 (uHi T M H H₂), rhoH h91 ⟨z, hzH⟩ w = w := by
    intro w hw
    have hyw : rhoH h91 ⟨y, hyH⟩ w ∈ Wsub h91 (uHi T M H H₁) :=
      rhoH_mem_Wsub h91 ⟨y, hyH⟩ hi₂ hsw' hw
    have := (hfix₁ _ hyw).2
    rwa [hρyy] at this
  rw [← S.centralizerMod_uK_eq hH]
  refine ⟨hzH, hHN hzH, fun k hk => ?_⟩
  obtain ⟨a, ha, b, hb, rfl⟩ := h.exists_decomp S hred hk
  have haU := hi₁ ha
  have hbU := hi₂ hb
  have h1 : z * a * z⁻¹ * a⁻¹ ∈ quasithinOmegaOneCenter T :=
    (rhoH_clsU_eq_iff h91 ⟨z, hzH⟩ haU).mp (hfix₁ _ (clsU_mem_Wsub h91 haU ha)).1
  have h2 : z * b * z⁻¹ * b⁻¹ ∈ quasithinOmegaOneCenter T :=
    (rhoH_clsU_eq_iff h91 ⟨z, hzH⟩ hbU).mp (hfix₂ _ (clsU_mem_Wsub h91 hbU hb))
  have e : z * (a * b) * z⁻¹ * (a * b)⁻¹ =
      (z * a * z⁻¹ * a⁻¹) * (a * (z * b * z⁻¹ * b⁻¹) * a⁻¹) := by group
  rw [e]
  refine (quasithinOmegaOneCenter T).mul_mem h1 ?_
  have := (Subgroup.mem_normalizer_iff.mp (hUZ haU) (z * b * z⁻¹ * b⁻¹)).mp h2
  simpa using this

theorem IsDecP.rho_eq_of_swap_quad (S : Setting146 G T M) {PQ : Subgroup G}
    (hred : IsRedCE T M H PQ p) (h : IsDecP T M H p H₀ H₁ H₂ t)
    (h91 : HypF91 T (VZ T M) (yOfL22 T M) (quasithinOmegaOneCenter T) (VZ T M) H)
    {B : Subgroup G} (hq : QCrit (quasithinOmegaOneCenter T) (VZ T M) H B) {y z : G}
    (hy : y ∈ B) (hz : z ∈ B) (hyy : y * y = 1)
    (hsw : conjSub y (uHi T M H H₁) = uHi T M H H₂)
    (hsw' : conjSub y (uHi T M H H₂) = uHi T M H H₁) :
    rhoH h91 ⟨z, hq.1 hz⟩ = 1 ∨ rhoH h91 ⟨z, hq.1 hz⟩ = rhoH h91 ⟨y, hq.1 hy⟩ := by
  have hzH := hq.1 hz
  have hyH := hq.1 hy
  rcases h.normalizer_or_swap S hred hzH with ⟨-, hz₁, hz₂⟩ | ⟨hz₁, hz₂⟩
  · left
    have := h.mem_pCore_of_nonswap S hred h91 hq hy hz hyy hsw hsw' hz₁ hz₂
    exact (rhoH_eq_one_iff h91 ⟨z, hzH⟩).mpr this
  · right
    have hzy : z * y ∈ B := B.mul_mem hz hy
    have hzy₁ : conjSub (z * y) (uHi T M H H₁) = uHi T M H H₁ := by
      rw [conjSub_mul, hsw, hz₂]
    have hzy₂ : conjSub (z * y) (uHi T M H H₂) = uHi T M H H₂ := by
      rw [conjSub_mul, hsw', hz₁]
    have hQ := h.mem_pCore_of_nonswap S hred h91 hq hy hzy hyy hsw hsw' hzy₁ hzy₂
    have h1 : rhoH h91 ⟨z * y, hq.1 hzy⟩ = 1 := (rhoH_eq_one_iff h91 _).mpr hQ
    have e1 : (⟨z * y, hq.1 hzy⟩ : ↥H) = ⟨z, hzH⟩ * ⟨y, hyH⟩ := rfl
    rw [e1, map_mul] at h1
    have hyy' : rhoH h91 ⟨y, hyH⟩ * rhoH h91 ⟨y, hyH⟩ = 1 := by
      rw [← map_mul]
      have : (⟨y, hyH⟩ : ↥H) * ⟨y, hyH⟩ = 1 := Subtype.ext hyy
      rw [this, map_one]
    calc rhoH h91 ⟨z, hzH⟩ = rhoH h91 ⟨z, hzH⟩ * (rhoH h91 ⟨y, hyH⟩ * rhoH h91 ⟨y, hyH⟩) := by
          rw [hyy', mul_one]
      _ = (rhoH h91 ⟨z, hzH⟩ * rhoH h91 ⟨y, hyH⟩) * rhoH h91 ⟨y, hyH⟩ := by rw [mul_assoc]
      _ = rhoH h91 ⟨y, hyH⟩ := by rw [h1, one_mul]

end Quad

end CFSG.Quasithin
