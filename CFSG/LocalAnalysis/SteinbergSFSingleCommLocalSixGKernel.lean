module

public import CFSG.LocalAnalysis.SteinbergSFSingleCommLocalSixGNormal

public section

namespace CFSG.LocalAnalysis.SymplecticFourStandard

namespace SixG

open Subgroup GomiFusion RootAxisTwoCore FullCenter FullCenterRadical FullCenterParabolic
  FullCenterTorus FullCenterWeyl SingleComm NextCores
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
  CFSG.RankThree.PartOne.KCRootAxis
open scoped Matrix Pointwise

section Kernel

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2]
  [Finite K] {n : ℕ} {φ : L ≃* antiSp K} {t : G}

local notation "𝐏" => pull φ (antiUnipotent K)
local notation "𝐐" => (pull φ (antiUnipotent K) ⊔ zpowers t : Subgroup G)
local notation "𝐙" => pull φ (antiUnipotentCenter K)
local notation "𝐁[" i "]" => (zpowers t ⊔ pull φ (rootA K i) : Subgroup G)
local notation "𝐕[" i "]" => (zpowers t ⊔ pull φ (rootU K i) : Subgroup G)
local notation "𝐀[" i "]" => pull φ (rootA K i)
local notation "𝐔[" i "]" => pull φ (rootU K i)
local notation "𝐍[" i "]" => normalizer (((zpowers t ⊔ pull φ (rootA K i) : Subgroup G) :
  Subgroup G) : Set G)
local notation "𝐌[" i "]" => normalizer (((zpowers t ⊔ pull φ (rootU K i) : Subgroup G) :
  Subgroup G) : Set G)
set_option quotPrecheck false in
local notation "𝐃[" i "]" => (CFSG.pCore 2 (normalizer
  (((zpowers t ⊔ pull φ (rootU K i) : Subgroup G) : Subgroup G) : Set G))).map
  (normalizer (((zpowers t ⊔ pull φ (rootU K i) : Subgroup G) : Subgroup G) : Set G)).subtype
set_option quotPrecheck false in
local notation "𝐄[" i "]" => (CFSG.pCore 2 (normalizer
  (((zpowers t ⊔ pull φ (rootA K i) : Subgroup G) : Subgroup G) : Set G))).map
  (normalizer (((zpowers t ⊔ pull φ (rootA K i) : Subgroup G) : Subgroup G) : Set G)).subtype
set_option quotPrecheck false in
local notation "𝐐[" i "]" => (pull φ (antiUnipotent K) ⊔ zpowers t ⊔ 𝐃[i] : Subgroup G)
set_option quotPrecheck false in
local notation "𝐑[" i "]" => (pull φ (antiUnipotent K) ⊔ zpowers t ⊔ 𝐄[i] : Subgroup G)
set_option quotPrecheck false in
local notation "𝐇" => (𝐐[Axis.one] ⊔ 𝐐[Axis.two] : Subgroup G)
set_option quotPrecheck false in
local notation "𝐄₀" => (𝐄[Axis.one] ⊓ 𝐄[Axis.two] : Subgroup G)
set_option quotPrecheck false in
local notation "𝐂" => centralizer ({t} : Set G)
local notation "𝐉" => pull φ (diagTorus K)
set_option quotPrecheck false in
local notation "𝐅" => closure {x : G | ∃ e ∈ 𝐄₀, ∃ j ∈ pull φ (diagTorus K),
  x = e⁻¹ * (j⁻¹ * e * j)}
local notation "𝐉[" i "]" => pull φ (axisTorus K i)
set_option quotPrecheck false in
local notation "𝐖[" i "]" => (𝐅 ⊓ centralizer (𝐉[i] : Set G) : Subgroup G)
set_option quotPrecheck false in
local notation "𝐊[" i "]" => (𝐀[i] ⊔ (𝐅 ⊓ 𝐃[i]) : Subgroup G)
set_option quotPrecheck false in
local notation "𝐊⋆" => (𝐊[Axis.one] ⊔ 𝐊[Axis.two] : Subgroup G)
set_option quotPrecheck false in
local notation "𝐋[" i "]" => (𝐅 ⊔ 𝐀[i] : Subgroup G)
local notation "𝐰[" i "]" => ((φ.symm (weylElt K i) : L) : G)
set_option quotPrecheck false in
local notation "𝐅ʷ[" i "]" => (𝐅.map (MulAut.conj 𝐰[i]⁻¹).toMonoidHom : Subgroup G)
set_option quotPrecheck false in
local notation "𝐗[" i "]" => (𝐅 ⊔ 𝐅ʷ[i] : Subgroup G)
set_option quotPrecheck false in
local notation "𝐍ₕ[" i "]" => (normalizer ((𝐇 : Subgroup G) : Set G) ⊓
  normalizer (𝐔[i] : Set G) : Subgroup G)
set_option quotPrecheck false in
local notation "𝐘[" i "," k "]" => (𝐍ₕ[i] ⊓ normalizer ((𝐇 ⊓ 𝐄[k] : Subgroup G) : Set G) :
  Subgroup G)
set_option quotPrecheck false in
local notation "𝐍𝐑[" k "]" => (normalizer (𝐑[k] : Set G) ⊓ normalizer (𝐁[k] : Set G) :
  Subgroup G)
set_option quotPrecheck false in
local notation "𝐃𝐧[" i "]" => normalizer ((𝐃[i] : Subgroup G) : Set G)
set_option quotPrecheck false in
local notation "𝐏₁[" i "]" => (CFSG.pCore 2 (normalizer ((𝐃[i] : Subgroup G) : Set G))).map
  (normalizer ((𝐃[i] : Subgroup G) : Set G)).subtype
set_option quotPrecheck false in
local notation "𝐄𝐧[" i "]" => (normalizer ((𝐄[i] : Subgroup G) : Set G) ⊓
  normalizer ((𝐊[i] : Subgroup G) : Set G) : Subgroup G)
set_option quotPrecheck false in
local notation "𝐏₂[" i "]" => (CFSG.pCore 2 𝐄𝐧[i]).map 𝐄𝐧[i].subtype
set_option quotPrecheck false in
local notation "𝐓₁[" i "]" => (𝐑[i] ⊔ 𝐏₁[i] : Subgroup G)
set_option quotPrecheck false in
local notation "𝐓₀[" j "]" => (𝐑[j] ⊔ 𝐏₂[j] : Subgroup G)
set_option quotPrecheck false in
local notation "𝐓₂[" j "]" => (𝐓₀[j] ⊓ normalizer (𝐑[j] : Set G) : Subgroup G)
set_option quotPrecheck false in
local notation "𝐓₃[" i "]" => (𝐓₁[i] ⊓ 𝐓₂[Axis.swap i] : Subgroup G)
set_option quotPrecheck false in
local notation "𝐓̄[" i "]" => (𝐓₁[i] ⊔ 𝐓₂[Axis.swap i] : Subgroup G)
set_option quotPrecheck false in
local notation "𝐏₀[" i "]" => (𝐏₁[i] ⊓ 𝐏₂[Axis.swap i] : Subgroup G)


set_option quotPrecheck false in
local notation "𝐌₀[" i "]" => closure {x : G | ∃ p ∈ 𝐏₀[i], ∃ j ∈ pull φ (diagTorus K),
  x = p⁻¹ * (j⁻¹ * p * j)}

set_option quotPrecheck false in
local notation "𝐁⋆[" i "]" => (𝐌₀[i] ⊔ 𝐊⋆ : Subgroup G)
set_option quotPrecheck false in
local notation "𝐂⋆[" i "]" => (𝐌₀[i] ⊔ 𝐅ʷ[Axis.swap i] : Subgroup G)
set_option quotPrecheck false in
local notation "𝐀⋆[" i "]" => (𝐌₀[i] ⊔ 𝐊⋆ ⊔ 𝐅ʷ[Axis.swap i] : Subgroup G)
set_option quotPrecheck false in
local notation "𝐗𝐧[" i "]" => (normalizer (𝐓₂[Axis.swap i] : Set G) ⊓
  normalizer (𝐊[Axis.swap i] : Set G) ⊓ normalizer (𝐁⋆[i] : Set G) ⊓
  normalizer (𝐂⋆[i] : Set G) : Subgroup G)
set_option quotPrecheck false in
local notation "𝐕𝐂[" i "]" => quotCent (normalizer (𝐓₂[Axis.swap i] : Set G) ⊓
  normalizer (𝐁⋆[i] : Set G)) 𝐓₂[Axis.swap i] 𝐁⋆[i]
  (fun _ hg _ hy => (mem_normalizer_iff.mp (mem_inf.mp hg).1 _).mp hy)
  (fun _ hg _ hb => (mem_normalizer_iff.mp (mem_inf.mp hg).2 _).mp hb)

theorem psiX_one_eq_zero_iff (h : FCHyp L K n φ t) (k : Axis) {e : G} (he : e ∈ 𝐄[k]) :
    psiX φ t k e 1 = 0 ↔ e ∈ 𝐇 := by
  rw [mem_H_iff_E h k he]
  exact psiG_one_eq_zero_iff h k (kappa_E_mem_A h k he)

theorem psiX_one_mul (h : FCHyp L K n φ t) (k : Axis) {x y : G} (hx : x ∈ 𝐄[k])
    (hy : y ∈ 𝐄[k]) : psiX φ t k (x * y) 1 = psiX φ t k x 1 + psiX φ t k y 1 := by
  rw [psiX_mul h k hx hy, Pi.add_apply]

theorem psiX_one_inv (h : FCHyp L K n φ t) (k : Axis) {x : G} (hx : x ∈ 𝐄[k]) :
    psiX φ t k x⁻¹ 1 = -psiX φ t k x 1 := by
  have h1 := psiX_one_mul h k hx (inv_mem hx)
  rw [mul_inv_cancel] at h1
  have h0 : psiX φ t k 1 1 = 0 := (psiX_one_eq_zero_iff h k (one_mem _)).mpr (one_mem _)
  rw [h0] at h1
  exact eq_neg_of_add_eq_zero_right h1.symm

theorem exists_psiX_one_eq (h : FCHyp L K n φ t) (k : Axis) (v : K) :
    ∃ x ∈ 𝐄[k], psiX φ t k x 1 = v := by
  obtain ⟨x, hx, hxv⟩ := exists_psiX_eq h k ![0, v]
  exact ⟨x, X_le_E h k hx, by rw [hxv]; rfl⟩

omit [Finite G] [Finite K] in
theorem torus_mem_C (h : FCHyp L K n φ t) {g : G} (hg : g ∈ 𝐉) : g ∈ 𝐂 :=
  mem_centralizer_iff.mpr fun _ hx => by
    rw [Set.mem_singleton_iff.mp hx]
    exact t_comm_torus h hg

theorem psiX_conj_torus (h : FCHyp L K n φ t) (k : Axis) {δ : antiSp K} {r s : K} (hr : r ≠ 0)
    (hs : s ≠ 0) (hδ : glMat (δ : GL (Fin 4) K) = diagMat r s) {e : G} (he : e ∈ 𝐄[k]) :
    psiX φ t k (((φ.symm δ : L) : G)⁻¹ * e * ((φ.symm δ : L) : G)) 1 =
      radChar k r s * psiX φ t k e 1 := by
  have hgJ : ((φ.symm δ : L) : G) ∈ 𝐉 := symm_mem_pull.mpr ⟨r, s, hr, hs, hδ⟩
  have hκ := kappa_conj_C (inv_mem (torus_mem_C h hgJ)) e
  rw [inv_inv] at hκ
  show psiG φ k (t⁻¹ * ((((φ.symm δ : L) : G)⁻¹ * e * ((φ.symm δ : L) : G))⁻¹ * t *
    (((φ.symm δ : L) : G)⁻¹ * e * ((φ.symm δ : L) : G)))) 1 = _
  rw [hκ]
  exact psiG_conj_torus h k hr hs hδ (kappa_E_mem_A h k he)

theorem E_le_of_psiX (h : FCHyp L K n φ t) (k : Axis) {S : Subgroup G} (hHS : 𝐇 ⊓ 𝐄[k] ≤ S)
    (hS : ∀ e ∈ 𝐄[k], ∃ s ∈ S, s ∈ 𝐄[k] ∧ psiX φ t k s 1 = psiX φ t k e 1) : 𝐄[k] ≤ S := by
  intro e he
  obtain ⟨s, hsS, hsE, hse⟩ := hS e he
  have h1 : s⁻¹ * e ∈ 𝐇 := (psiX_one_eq_zero_iff h k (mul_mem (inv_mem hsE) he)).mp (by
    rw [psiX_one_mul h k (inv_mem hsE) he, psiX_one_inv h k hsE, hse, neg_add_cancel])
  have h2 := mul_mem hsS (hHS (mem_inf.mpr ⟨h1, mul_mem (inv_mem hsE) he⟩))
  rwa [mul_inv_cancel_left] at h2

omit [Finite G] in
theorem exists_ne_zero_ne_one (h : FCHyp L K n φ t) : ∃ r : K, r ≠ 0 ∧ r ≠ 1 := by
  by_contra hcon
  have hsub : (Set.univ : Set K) ⊆ {0, 1} := fun x _ => by
    by_cases hx : x = 0
    · exact Or.inl hx
    · exact Or.inr (by_contra fun h1 => hcon ⟨x, hx, h1⟩)
  have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_univ, Set.ncard_pair zero_ne_one] at h1
  have := four_le_card_K h
  omega

omit [Finite G] in
theorem exists_radChar (h : FCHyp L K n φ t) (i : Axis) :
    ∃ r s : K, r ≠ 0 ∧ s ≠ 0 ∧ radChar i.swap r s = 1 ∧ radChar i r s ≠ 1 := by
  obtain ⟨r, hr0, hr1⟩ := exists_ne_zero_ne_one h
  cases i
  · exact ⟨r, r, hr0, hr0, by simp [radChar, Axis.swap, hr0], by simpa [radChar] using hr1⟩
  · exact ⟨r, 1, hr0, one_ne_zero, by simp [radChar, Axis.swap], by simpa [radChar] using hr1⟩

omit [CharP K 2] [Finite K] in
theorem exists_radChar_eq (i : Axis) {w : K} (hw : w ≠ 0) :
    ∃ r s : K, r ≠ 0 ∧ s ≠ 0 ∧ radChar i r s = w := by
  cases i
  · exact ⟨1, w, one_ne_zero, hw, rfl⟩
  · exact ⟨w, 1, hw, one_ne_zero, by simp [radChar]⟩

omit [Finite G] [Finite K] in
theorem E_le_Tbar (i : Axis) : 𝐄[i] ≤ 𝐓̄[i] :=
  ((le_sup_right : 𝐄[i] ≤ 𝐑[i]).trans le_sup_left).trans le_sup_left

theorem Tbar_eq_sup_E (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) : 𝐓̄[i] = 𝐓₂[i.swap] ⊔ 𝐄[i] := by
  refine le_antisymm ((R_sup_T₂ h i hne hbot).ge.trans (sup_le le_sup_left
    (sup_le ((Q_le_H.trans (H_le_T₂ h _)).trans le_sup_left) le_sup_right)))
    (sup_le le_sup_right (E_le_Tbar i))

theorem J_le_normalizer_E (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) (k : Axis) :
    𝐉 ≤ normalizer ((𝐄[k] : Subgroup G) : Set G) := fun _ hj =>
  (mem_inf.mp (N_le_En h k (mem_inf.mp (J_le_NRB h i hne hbot k hj)).2)).1

theorem J_le_normalizer_Tbar (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) : 𝐉 ≤ normalizer (𝐓̄[i] : Set G) := fun _ hj =>
  mem_normalizer_of_conj_le fun _ hx => conj_mem_Tbar h i hne hbot (J_le_Nhat h i hne hbot hj) hx

theorem J_le_normalizer_T₀ (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) (k : Axis) : 𝐉 ≤ normalizer (𝐓₀[k] : Set G) := fun _ hj =>
  mem_normalizer_of_conj_le fun _ hx => conj_mem_sup
    (fun _ hy => (mem_normalizer_iff.mp (mem_inf.mp (J_le_NRB h i hne hbot k hj)).1 _).mp hy)
    (fun _ hy => conj_mem_P₂ k (N_le_En h k (mem_inf.mp (J_le_NRB h i hne hbot k hj)).2) hy) hx

theorem T₂_le_VC (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) (hM2 : ∀ x ∈ 𝐌₀[i], x * x ∈ 𝐔[i]) :
    𝐓₂[i.swap] ≤ 𝐕𝐂[i] := fun _ hx =>
  mem_quotCent.mpr ⟨mem_inf.mpr ⟨le_normalizer hx, T₂_le_normalizer_Bstar h i hne hbot hx⟩,
    fun _ hy => comm_T₂_mem_Bstar h i hne hbot hM2 hx hy⟩

theorem Tbar_le_N' (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) (hM2 : ∀ x ∈ 𝐌₀[i], x * x ∈ 𝐔[i]) :
    𝐓̄[i] ≤ normalizer (𝐓₂[i.swap] : Set G) ⊓ normalizer (𝐁⋆[i] : Set G) := fun _ hg =>
  mem_inf.mpr ⟨Tbar_le_normalizer_T₂ h i hne hbot hg,
    (Tbar_le_normalizer_Bstar h i hne hbot hM2 hg).1⟩

theorem torus_mem_VC (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) {δ : antiSp K} {r s : K} (hr : r ≠ 0) (hs : s ≠ 0)
    (hδ : glMat (δ : GL (Fin 4) K) = diagMat r s) (hj : radChar i.swap r s = 1) :
    ((φ.symm δ : L) : G)⁻¹ ∈ 𝐕𝐂[i] := by
  have hgJ : ((φ.symm δ : L) : G)⁻¹ ∈ 𝐉 := inv_mem (symm_mem_pull.mpr ⟨r, s, hr, hs, hδ⟩)
  have hgB := J_le_normalizer_Bstar h i hne hbot hgJ
  refine mem_quotCent.mpr ⟨mem_inf.mpr ⟨J_le_normalizer_T₂ h i hne hbot hgJ, hgB⟩,
    fun x hx => ?_⟩
  have hT : (𝐁⋆[i] ⊔ 𝐗[i.swap]) ⊔ zpowers t ≤ normalizer (𝐁⋆[i] : Set G) :=
    (sup_le_sup_right (Astar_eq h i).ge _).trans ((Astar_sup_t h i hne hbot).1.le.trans
      (T₂_le_normalizer_Bstar h i hne hbot))
  have hx' : x ∈ (𝐁⋆[i] ⊔ 𝐗[i.swap]) ⊔ zpowers t :=
    sup_le_sup_right (Astar_eq h i).le _ ((Astar_sup_t h i hne hbot).1.ge hx)
  refine comm_mem_sup hT (comm_mem_sup (le_sup_left.trans hT)
    (fun b hb => comm_mem_of_mem_right hgB hb) (fun z hz => ?_)) (fun c hc => ?_) x hx'
  · have hzE := X_le_E h _ hz
    have hgz : ((φ.symm δ : L) : G)⁻¹ * z * ((φ.symm δ : L) : G)⁻¹⁻¹ ∈ 𝐗[i.swap] :=
      (mem_normalizer_iff.mp (J_le_normalizer_X h i hne hbot hgJ) z).mp hz
    have hψ : psiX φ t i.swap (((φ.symm δ : L) : G)⁻¹ * z * ((φ.symm δ : L) : G)⁻¹⁻¹ * z⁻¹) 1
        = 0 := by
      rw [psiX_one_mul h _ (X_le_E h _ hgz) (inv_mem hzE), psiX_one_inv h _ hzE, inv_inv,
        psiX_conj_torus h _ hr hs hδ hzE, hj, one_mul, add_neg_cancel]
    have hH := (psiX_one_eq_zero_iff h _ (mul_mem (X_le_E h _ hgz) (inv_mem hzE))).mp hψ
    exact (L_le_Ks h _).trans le_sup_right
      (SixF.mem_L_of_mem_X_of_mem_H h _ (mul_mem hgz (inv_mem hz)) hH)
  · rcases mem_zpowers_t h hc with hc1 | hct
    · rw [hc1, mul_one, inv_one, mul_one, mul_inv_cancel]
      exact one_mem _
    · have hc' : ((φ.symm δ : L) : G)⁻¹ * t * ((φ.symm δ : L) : G)⁻¹⁻¹ * t⁻¹ = 1 := by
        rw [← t_comm_torus h hgJ, mul_inv_cancel_right, mul_inv_cancel]
      rw [hct, hc']
      exact one_mem _

theorem E_le_VC (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) (hM2 : ∀ x ∈ 𝐌₀[i], x * x ∈ 𝐔[i]) :
    𝐄[i] ≤ 𝐕𝐂[i] := by
  obtain ⟨r, s, hr, hs, hj, hi⟩ := exists_radChar h i
  obtain ⟨δ, hδD, hδ⟩ := exists_diagTorus hr hs
  have ha := torus_mem_VC h i hne hbot hr hs hδ hj
  have hgJ : ((φ.symm δ : L) : G)⁻¹ ∈ 𝐉 := inv_mem (symm_mem_pull.mpr hδD)
  have hl : radChar i r s - 1 ≠ 0 := sub_ne_zero.mpr hi
  refine E_le_of_psiX h i (fun x hx => T₂_le_VC h i hne hbot hM2 (H_le_T₂ h _ (mem_inf.mp hx).1))
    fun e he => ?_
  obtain ⟨e', he', hψ⟩ := exists_psiX_one_eq h i ((radChar i r s - 1)⁻¹ * psiX φ t i e 1)
  have he'N := Tbar_le_N' h i hne hbot hM2 (E_le_Tbar i he')
  have hgE : ((φ.symm δ : L) : G)⁻¹ * e' * ((φ.symm δ : L) : G)⁻¹⁻¹ ∈ 𝐄[i] :=
    (mem_normalizer_iff.mp (J_le_normalizer_E h i hne hbot i hgJ) e').mp he'
  refine ⟨((φ.symm δ : L) : G)⁻¹ * e' * ((φ.symm δ : L) : G)⁻¹⁻¹ * e'⁻¹, ?_,
    mul_mem hgE (inv_mem he'), ?_⟩
  · have h1 := conj_mem_quotCent he'N (inv_mem ha)
    have e1 : ((φ.symm δ : L) : G)⁻¹ * e' * ((φ.symm δ : L) : G)⁻¹⁻¹ * e'⁻¹ =
        ((φ.symm δ : L) : G)⁻¹ * (e' * ((φ.symm δ : L) : G)⁻¹⁻¹ * e'⁻¹) := by group
    rw [e1]
    exact mul_mem ha h1
  · rw [psiX_one_mul h i hgE (inv_mem he'), psiX_one_inv h i he', inv_inv,
      psiX_conj_torus h i hr hs hδ he', hψ]
    have e2 : radChar i r s * ((radChar i r s - 1)⁻¹ * psiX φ t i e 1) +
        -((radChar i r s - 1)⁻¹ * psiX φ t i e 1) =
          (radChar i r s - 1) * (radChar i r s - 1)⁻¹ * psiX φ t i e 1 := by ring
    rw [e2, mul_inv_cancel₀ hl, one_mul]

theorem Tbar_le_VC (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) (hM2 : ∀ x ∈ 𝐌₀[i], x * x ∈ 𝐔[i]) :
    𝐓̄[i] ≤ 𝐕𝐂[i] :=
  (Tbar_eq_sup_E h i hne hbot).le.trans
    (sup_le (T₂_le_VC h i hne hbot hM2) (E_le_VC h i hne hbot hM2))

theorem VC_le_normalizer_T₃ (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) {y : G} (hy : y ∈ 𝐕𝐂[i]) :
    y ∈ normalizer (𝐓₃[i] : Set G) :=
  mem_normalizer_of_conj_le fun x hx => by
    have h1 := (mem_quotCent.mp hy).2 x (mem_inf.mp hx).2
    have h2 : y * x * y⁻¹ = (y * x * y⁻¹ * x⁻¹) * x := by group
    rw [h2]
    exact mul_mem (Bstar_le_T₃ h i hne hbot h1) hx

theorem R_le_normalizer_ZP (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) (k : Axis) : 𝐑[k] ≤ normalizer (𝐙 : Set G) :=
  le_normalizer_ZP_of_H h fun _ hg => (mem_inf.mp (R_le_Nhat h i hne hbot k hg)).1

theorem mem_Q_sup_J_of_VC (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) {c : G} (hcC : c ∈ 𝐂)
    (hcQ : c ∈ normalizer (𝐐 : Set G)) (hc : c ∈ 𝐕𝐂[i]) : c ∈ 𝐐 ⊔ 𝐉 := by
  refine mem_Q_sup_J h i hcC (fun m => normalizer_Q_le_N h i hne hbot m hcQ) fun a ha => ?_
  have hmem : t * a ∈ {x : G | ∃ a ∈ 𝐀[i.swap], x = t * a} := ⟨a, ha, rfl⟩
  rw [← orbit_E h i.swap] at hmem
  obtain ⟨e, he, hea⟩ := hmem
  have hκe : t⁻¹ * (e⁻¹ * t * e) = a := by rw [← hea]; group
  have hce : c * e * c⁻¹ ∈ 𝐄[i.swap] := conj_normalizer_Q_mem_E h i hne hbot _ hcQ he
  have hd : c * e * c⁻¹ * e⁻¹ ∈ 𝐇 ⊓ 𝐄[i.swap] := by
    rw [← T₃_inf_E_swap h i hne hbot]
    exact mem_inf.mpr ⟨Bstar_le_T₃ h i hne hbot ((mem_quotCent.mp hc).2 e
      ((le_sup_right : 𝐄[i.swap] ≤ 𝐑[i.swap]).trans (R_le_T₂ _) he)),
      mul_mem hce (inv_mem he)⟩
  have hdZ := (mem_H_iff_E h _ (mem_inf.mp hd).2).mp (mem_inf.mp hd).1
  have h1 := kappa_conj_C hcC e
  have key : c * a * c⁻¹ * a⁻¹ = a * (e⁻¹ * (t⁻¹ * ((c * e * c⁻¹ * e⁻¹)⁻¹ * t *
      (c * e * c⁻¹ * e⁻¹))) * e) * a⁻¹ := by
    rw [← hκe, ← h1]
    group
  rw [key]
  have hRZ := R_le_normalizer_ZP h i hne hbot i.swap
  have hz := conj_inv_mem (hRZ ((le_sup_right : 𝐄[i.swap] ≤ 𝐑[i.swap]) he)) hdZ
  have haR : a ∈ 𝐑[i.swap] :=
    (le_sup_left : 𝐏 ≤ 𝐏 ⊔ zpowers t).trans le_sup_left (pull_mono φ (rootA_le_antiUnipotent _) ha)
  exact (mem_normalizer_iff.mp (hRZ haR) _).mp hz

theorem Q_le_Tbar (h : FCHyp L K n φ t) (i : Axis) : 𝐐 ≤ 𝐓̄[i] :=
  (Q_le_H.trans (H_le_T₂ h _)).trans le_sup_right

theorem exists_Nhat_decomp (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) {y : G} (hyN : y ∈ 𝐍ₕ[i]) :
    ∃ τ ∈ 𝐓̄[i], ∃ c ∈ 𝐂 ⊓ normalizer (𝐐 : Set G), ∃ r ∈ 𝐓̄[i], y = τ * c * r := by
  obtain ⟨y', hy', r, hr, rfl⟩ := (first_index h i hne hbot i.swap).2 y hyN
  rw [swap_swap] at hr
  obtain ⟨τ, hτ, n', hn', rfl⟩ := Set.mem_mul.mp ((Y₂_mul h i hne hbot).le hy')
  obtain ⟨r', hr', c, hc, rfl⟩ := Set.mem_mul.mp ((NRB_eq' h i hne hbot i.swap).ge hn')
  refine ⟨τ * r', mul_mem (le_sup_right (a := 𝐓₁[i]) hτ)
    (le_sup_right (a := 𝐓₁[i]) (R_le_T₂ _ hr')), c, hc, r,
    ((le_sup_left : 𝐑[i] ≤ 𝐓₁[i]).trans le_sup_left) hr, by group⟩

theorem mem_Tbar_sup_J_of_decomp (h : FCHyp L K n φ t) (i : Axis)
    (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥) (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥)
    (hM2 : ∀ x ∈ 𝐌₀[i], x * x ∈ 𝐔[i]) {τ c r : G} (hτ : τ ∈ 𝐓̄[i])
    (hc : c ∈ 𝐂 ⊓ normalizer (𝐐 : Set G)) (hr : r ∈ 𝐓̄[i]) (hyV : τ * c * r ∈ 𝐕𝐂[i]) :
    τ * c * r ∈ 𝐓̄[i] ⊔ 𝐉 := by
  have hTV := Tbar_le_VC h i hne hbot hM2
  have hcV : c ∈ 𝐕𝐂[i] := by
    have h1 := mul_mem (mul_mem (inv_mem (hTV hτ)) hyV) (inv_mem (hTV hr))
    rwa [show τ⁻¹ * (τ * c * r) * r⁻¹ = c by group] at h1
  have hcTJ : c ∈ 𝐓̄[i] ⊔ 𝐉 := sup_le_sup_right (Q_le_Tbar h i) _
    (mem_Q_sup_J_of_VC h i hne hbot (mem_inf.mp hc).1 (mem_inf.mp hc).2 hcV)
  exact mul_mem (mul_mem (mem_sup_left hτ) hcTJ) (mem_sup_left hr)

theorem mem_Nhat_of_X_VC (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) (hM2 : ∀ x ∈ 𝐌₀[i], x * x ∈ 𝐔[i]) {y : G}
    (hyX : y ∈ 𝐗𝐧[i]) (hyV : y ∈ 𝐕𝐂[i]) : y ∈ 𝐍ₕ[i] :=
  mem_Nhat_of_normalizer_T₃ h i hne hbot hM2 (mem_inf.mp (mem_inf.mp (mem_inf.mp hyX).1).1).2
    (mem_inf.mp (mem_inf.mp hyX).1).2 (mem_inf.mp hyX).2 (VC_le_normalizer_T₃ h i hne hbot hyV)

theorem mem_Tbar_of_two_element (h : FCHyp L K n φ t) (i : Axis)
    (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥) (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥)
    (hM2 : ∀ x ∈ 𝐌₀[i], x * x ∈ 𝐔[i]) {y : G} (hyX : y ∈ 𝐗𝐧[i]) (hyV : y ∈ 𝐕𝐂[i]) {e : ℕ}
    (hye : y ^ 2 ^ e = 1) : y ∈ 𝐓̄[i] := by
  obtain ⟨τ, hτ, c, hc, r, hr, rfl⟩ :=
    exists_Nhat_decomp h i hne hbot (mem_Nhat_of_X_VC h i hne hbot hM2 hyX hyV)
  exact mem_of_two_pow (J_le_normalizer_Tbar h i hne hbot) (odd_card_sub_one h)
    (fun _ hj => torus_pow_card_sub_one hj)
    (mem_Tbar_sup_J_of_decomp h i hne hbot hM2 hτ hc hr hyV) hye

theorem Tbar_le_X (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) (hM2 : ∀ x ∈ 𝐌₀[i], x * x ∈ 𝐔[i]) :
    𝐓̄[i] ≤ 𝐗𝐧[i] := fun _ hg =>
  mem_inf.mpr ⟨mem_inf.mpr ⟨mem_inf.mpr ⟨Tbar_le_normalizer_T₂ h i hne hbot hg,
    Tbar_le_normalizer_K h i hne hbot hg⟩, (Tbar_le_normalizer_Bstar h i hne hbot hM2 hg).1⟩,
    (Tbar_le_normalizer_Bstar h i hne hbot hM2 hg).2⟩

theorem T₀_le_X (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) (hM2 : ∀ x ∈ 𝐌₀[i], x * x ∈ 𝐔[i]) :
    𝐓₀[i.swap] ≤ 𝐗𝐧[i] := fun _ hg =>
  mem_inf.mpr ⟨mem_inf.mpr ⟨mem_inf.mpr ⟨T₀_le_normalizer_T₂ h i hne hbot hg,
    T₀_le_normalizer_K h _ hg⟩, (T₀_le_normalizer_Bstar h i hne hbot hM2 hg).1⟩,
    (T₀_le_normalizer_Bstar h i hne hbot hM2 hg).2⟩

theorem Tbar_normal_X (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) (hM2 : ∀ x ∈ 𝐌₀[i], x * x ∈ 𝐔[i]) {g : G}
    (hg : g ∈ 𝐗𝐧[i]) {x : G} (hx : x ∈ 𝐓̄[i]) : g * x * g⁻¹ ∈ 𝐓̄[i] := by
  obtain ⟨e, he⟩ := exists_two_pow_eq_one (isPGroup_Tbar h i hne hbot) hx
  have hgN' : g ∈ normalizer (𝐓₂[i.swap] : Set G) ⊓ normalizer (𝐁⋆[i] : Set G) :=
    mem_inf.mpr ⟨(mem_inf.mp (mem_inf.mp (mem_inf.mp hg).1).1).1,
      (mem_inf.mp (mem_inf.mp hg).1).2⟩
  refine mem_Tbar_of_two_element h i hne hbot hM2
    (mul_mem (mul_mem hg (Tbar_le_X h i hne hbot hM2 hx)) (inv_mem hg))
    (conj_mem_quotCent hgN' (Tbar_le_VC h i hne hbot hM2 hx)) (e := e) ?_
  rw [conj_pow, he, mul_one, mul_inv_cancel]

theorem T₀_le_normalizer_Tbar (h : FCHyp L K n φ t) (i : Axis)
    (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥) (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥)
    (hM2 : ∀ x ∈ 𝐌₀[i], x * x ∈ 𝐔[i]) : 𝐓₀[i.swap] ≤ normalizer (𝐓̄[i] : Set G) := fun _ hg =>
  mem_normalizer_of_conj_le fun _ hx =>
    Tbar_normal_X h i hne hbot hM2 (T₀_le_X h i hne hbot hM2 hg) hx

end Kernel

end SixG

end CFSG.LocalAnalysis.SymplecticFourStandard
