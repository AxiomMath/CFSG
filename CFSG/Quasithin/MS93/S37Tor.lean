module

public import CFSG.Quasithin.MS93.S37Uniq
public import CFSG.Quasithin.MS93.MSPRankOne

public section

namespace CFSG.Quasithin.MS93.S37

open CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.Quasithin.MS93 CFSG.Quasithin.MS93.MSP
open CFSG.QuasithinUnique CFSG.Quasithin.MS93.S36 CFSG.Quasithin.Vol2
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix

section Field

variable {F : Type} [Field F]

theorem eq_zero_of_torus [Finite F] [CharP F 2] (hF : 8 ≤ Nat.card F) (f : F →+ F)
    (hf : ∀ μ : F, μ ≠ 0 → ∀ c : F, f (μ ^ 2 * c) = μ⁻¹ * f c) : f = 0 := by
  by_contra hne
  obtain ⟨c, hc⟩ : ∃ c, f c ≠ 0 := by
    by_contra h
    push Not at h
    exact hne (AddMonoidHom.ext h)
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hroot : ∀ μ : F, μ ≠ 0 → μ ≠ 1 → μ ^ 2 + μ + 1 = 0 := by
    intro μ h0 h1
    have h1' : μ + 1 ≠ 0 := fun h => h1 (by linear_combination h - h2)
    have e1 := hf (μ + 1) h1' c
    have e2 : (μ + 1) ^ 2 * c = μ ^ 2 * c + c := by linear_combination (μ * c) * h2
    rw [e2, map_add, hf μ h0] at e1
    have e3 : (μ⁻¹ + 1 - (μ + 1)⁻¹) * f c = 0 := by linear_combination e1
    have e4 := (mul_eq_zero.1 e3).resolve_right hc
    field_simp at e4
    linear_combination e4
  obtain ⟨μ₀, h0, h1⟩ := exists_ne_zero_ne_one (by omega : 2 < Nat.card F)
  have hsub : ∀ μ : F, μ = 0 ∨ μ = 1 ∨ μ = μ₀ ∨ μ = μ₀ + 1 := by
    intro μ
    by_cases hμ0 : μ = 0
    · exact Or.inl hμ0
    by_cases hμ1 : μ = 1
    · exact Or.inr (Or.inl hμ1)
    have e1 := hroot μ hμ0 hμ1
    have e2 := hroot μ₀ h0 h1
    have e3 : (μ - μ₀) * (μ + μ₀ + 1) = 0 := by linear_combination e1 - e2
    rcases mul_eq_zero.1 e3 with h | h
    · exact Or.inr (Or.inr (Or.inl (sub_eq_zero.1 h)))
    · exact Or.inr (Or.inr (Or.inr (by linear_combination h - (μ₀ + 1) * h2)))
  have hcard : Nat.card F ≤ 4 := by
    have hs : Function.Surjective (fun i : Fin 4 => ![(0 : F), 1, μ₀, μ₀ + 1] i) := by
      intro μ
      rcases hsub μ with h | h | h | h
      · exact ⟨0, by simp [h]⟩
      · exact ⟨1, by simp [h]⟩
      · exact ⟨2, by simp [h]⟩
      · exact ⟨3, by simp [h]⟩
    have := Nat.card_le_card_of_surjective _ hs
    simpa using this
  omega

theorem eq_smul_of_comm_sl2 (g : (Fin 2 → F) →+ (Fin 2 → F))
    (hU : ∀ (a : F) (w : Fin 2 → F), g ![w 0 + a * w 1, w 1] = ![g w 0 + a * g w 1, g w 1])
    (hL : ∀ (a : F) (w : Fin 2 → F), g ![w 0, a * w 0 + w 1] = ![g w 0, a * g w 0 + g w 1]) :
    ∀ w : Fin 2 → F, g w = g ![1, 0] 0 • w := by
  have hr : ∀ c : F, g ![c, 0] 1 = 0 := by
    intro c
    have h := congrFun (hU 1 ![c, 0]) 0
    simp at h
    exact h
  have hs : ∀ d : F, g ![0, d] 0 = 0 := by
    intro d
    have h := congrFun (hL 1 ![0, d]) 1
    simp at h
    exact h
  have ht : ∀ a c : F, g ![0, a * c] 1 = a * g ![c, 0] 0 := by
    intro a c
    have h := congrFun (hL a ![c, 0]) 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, add_zero] at h
    have e : (![c, a * c] : Fin 2 → F) = ![c, 0] + ![0, a * c] := by
      funext i; fin_cases i <;> simp
    rw [e, map_add, Pi.add_apply, hr, zero_add, add_zero] at h
    exact h
  intro w
  have hw : w = ![w 0, 0] + ![0, w 1] := by funext i; fin_cases i <;> simp
  have h1 : g ![w 0, 0] 0 = w 0 * g ![1, 0] 0 := by
    have e := ht 1 (w 0)
    have e2 := ht (w 0) 1
    simp only [one_mul] at e
    simp only [mul_one] at e2
    rw [← e, e2]
  have h2 : g ![0, w 1] 1 = w 1 * g ![1, 0] 0 := by
    have e := ht (w 1) 1
    rw [mul_one] at e
    exact e
  funext i
  rw [hw, map_add]
  fin_cases i
  · simp only [Pi.add_apply, Fin.zero_eta, Fin.isValue, Pi.smul_apply, smul_eq_mul,
      Matrix.cons_val_zero]
    rw [h1, hs, add_zero, mul_comm]
    simp
  · simp only [Pi.add_apply, Fin.mk_one, Fin.isValue, Pi.smul_apply, smul_eq_mul,
      Matrix.cons_val_one]
    rw [hr, h2, zero_add, mul_comm]
    simp

end Field

section Sp

variable {F : Type} [Field F]

theorem mem_X₂_of_sub_mem {g : Sp4 F} (h : ∀ v, mat g *ᵥ v - v ∈ pt₀ F) : g ∈ X₂ F := by
  have hc : ∀ v, mat g *ᵥ v = v + (mat g *ᵥ v - v) (.inl 0) • e₁ F := by
    intro v
    obtain ⟨h1, h2, h3⟩ := mem_pt₀.1 (h v)
    simp only [Pi.sub_apply] at h1 h2 h3
    refine ext4 ?_ ?_ ?_ ?_ <;> simp [e₁]
    · linear_combination h1
    · linear_combination h2
    · linear_combination h3
  intro v hv
  have hv0 : v (.inr 0) = 0 := mem_perp_pt₀.1 hv
  have key := form_mat g v (f₁ F)
  rw [hc v, hc (f₁ F)] at key
  simp only [form_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply] at key
  simp [e₁, f₁, hv0] at key
  rw [hc v]
  simp [key]

theorem qe_inv_mul_mem_X₂ [CharP F 2] (x y s s' : F) : (qe x y s)⁻¹ * qe x y s' ∈ X₂ F := by
  have e : qe x y s' = qe x y s * qe 0 0 (s' - s) := by
    rw [qe_mul]
    exact qe_congr (by ring) (by ring) (by ring)
  rw [e, inv_mul_cancel_left, qe_zero_zero]
  exact transv_mem_X₂ _

theorem mulVec_inl_one_of_mem_Q₂ [CharP F 2] {g : Sp4 F} (hg : g ∈ Q₂ F) {v : V4 F}
    (hv : v ∈ perp (pt₀ F)) :
    (mat g *ᵥ v) (.inl 1) = v (.inl 1) ∧ (mat g *ᵥ v) (.inr 1) = v (.inr 1) := by
  obtain ⟨x, y, s, rfl⟩ := exists_eq_qe_of_mem_Q₂ hg
  have hv0 : v (.inr 0) = 0 := mem_perp_pt₀.1 hv
  rw [qe_mulVec]
  constructor <;> simp [e₁, e₂, f₂, hv0]

theorem coord_eq_zero_of_fix [CharP F 2] {v : V4 F} (hv : v ∈ perp (pt₀ F))
    (h₁ : mat (qe 1 0 0) *ᵥ v = v) (h₂ : mat (qe 0 1 0) *ᵥ v = v) :
    v (.inl 1) = 0 ∧ v (.inr 1) = 0 := by
  have hv0 : v (.inr 0) = 0 := mem_perp_pt₀.1 hv
  rw [qe_mulVec] at h₁ h₂
  have e₁' := congrFun h₁ (.inl 0)
  have e₂' := congrFun h₂ (.inl 0)
  simp [e₁, e₂, f₂, hv0] at e₁' e₂'
  exact ⟨e₂', e₁'⟩

theorem qe_one_not_mem_X₂ [CharP F 2] : qe (1 : F) 0 0 ∉ X₂ F := by
  intro h
  have h1 := (mem_fixer.1 h) (f₂ F) (mem_perp_pt₀.2 (by simp [f₂]))
  rw [qe_mulVec] at h1
  have h2 := congrFun h1 (.inl 0)
  simp [e₁, e₂, f₂] at h2

theorem mem_pt₀_of_coord {v : V4 F} (hv : v ∈ perp (pt₀ F)) (h₁ : v (.inl 1) = 0)
    (h₂ : v (.inr 1) = 0) : v ∈ pt₀ F :=
  mem_pt₀.2 ⟨h₁, mem_perp_pt₀.1 hv, h₂⟩

theorem torusPt_conj_qe [CharP F 2] (μ : Fˣ) (x y s : F) :
    torusPt μ * qe x y s * (torusPt μ)⁻¹ = qe ((μ : F) * x) ((μ : F) * y) ((μ : F) ^ 2 * s) := by
  refine ext_mulVec fun v => ?_
  have hinv : mat (torusPt μ)⁻¹ *ᵥ v = (((μ⁻¹ : Fˣ) : F) * v (.inl 0)) • e₁ F +
      v (.inl 1) • e₂ F + ((μ : F) * v (.inr 0)) • f₁ F + v (.inr 1) • f₂ F := by
    have h1 : torusPt μ⁻¹ = (torusPt μ)⁻¹ := by
      refine inv_eq_of_mul_eq_one_right ?_ |>.symm
      refine ext_mulVec fun w => ?_
      rw [mat_mul_mulVec, torusPt_mulVec, torusPt_mulVec, mat_one, Matrix.one_mulVec]
      refine ext4 ?_ ?_ ?_ ?_ <;> simp [e₁, e₂, f₁, f₂]
    rw [← h1, torusPt_mulVec, inv_inv]
  rw [mat_mul_mulVec, mat_mul_mulVec, hinv, qe_mulVec, torusPt_mulVec, qe_mulVec]
  have hμ : (μ : F) ≠ 0 := μ.ne_zero
  refine ext4 ?_ ?_ ?_ ?_ <;> simp [e₁, e₂, f₁, f₂] <;> field_simp

end Sp

variable {G : Type} [Group G]

theorem Qt_le_sup {M T L : Subgroup G} (θ : MulAut ↥(T1 M T L)) : Qt M θ ≤ L ⊔ pCoreOf 2 M :=
  (tImage_le θ _).trans T1_le_sup

variable [Finite G]

namespace Cfg

variable {M T L : Subgroup G} {F : Type} [Field F] [Fintype F] (C : Cfg M T L F)
include C

theorem rho_mul_eq {x y : G} (hx : x ∈ L ⊔ pCoreOf 2 M) (hy : y ∈ L ⊔ pCoreOf 2 M)
    (h : x * y ∈ L ⊔ pCoreOf 2 M) : C.rho ⟨x * y, h⟩ = C.rho ⟨x, hx⟩ * C.rho ⟨y, hy⟩ := by
  rw [← map_mul]
  rfl

theorem rho_conj_eq {g y : G} (hg : g ∈ L ⊔ pCoreOf 2 M) (hy : y ∈ L ⊔ pCoreOf 2 M)
    (h : g * y * g⁻¹ ∈ L ⊔ pCoreOf 2 M) :
    C.rho ⟨g * y * g⁻¹, h⟩ = C.rho ⟨g, hg⟩ * C.rho ⟨y, hy⟩ * (C.rho ⟨g, hg⟩)⁻¹ := by
  rw [← map_inv, ← map_mul, ← map_mul]
  rfl

theorem rho_comm_eq {x y : G} (hx : x ∈ L ⊔ pCoreOf 2 M) (hy : y ∈ L ⊔ pCoreOf 2 M)
    (h : ⁅x, y⁆ ∈ L ⊔ pCoreOf 2 M) : C.rho ⟨⁅x, y⁆, h⟩ = ⁅C.rho ⟨x, hx⟩, C.rho ⟨y, hy⟩⁆ := by
  rw [← map_commutatorElement]
  rfl

theorem rho_lift (g : Sp4 F) : C.rho ⟨C.lift g, Subgroup.mem_sup_left (C.lift_mem g)⟩ = g := by
  rw [C.rho_of_mem_L (C.lift_mem g), C.alpha_lift]

section Proj

variable (hQUD : ∀ x ∈ pCoreOf 2 M, ∃ u ∈ Uq M T L, u⁻¹ * x ∈ Dq M L)

open Classical in
noncomputable def pr (x : G) : V4 F :=
  if hx : x ∈ pCoreOf 2 M then
    C.N.co ⟨Classical.choose (hQUD x hx), (Classical.choose_spec (hQUD x hx)).1⟩
  else 0

theorem pr_eq {x u : G} (hx : x ∈ pCoreOf 2 M) (hu : u ∈ Uq M T L) (hd : u⁻¹ * x ∈ Dq M L) :
    C.pr hQUD x = C.N.co ⟨u, hu⟩ := by
  have hs := Classical.choose_spec (hQUD x hx)
  simp only [pr, hx, ↓reduceDIte]
  rw [C.N.co_eq_co_iff]
  refine ⟨Subtype.prop _, ?_⟩
  have e : (Classical.choose (hQUD x hx))⁻¹ * u =
      ((Classical.choose (hQUD x hx))⁻¹ * x) * (u⁻¹ * x)⁻¹ := by group
  show (Classical.choose (hQUD x hx))⁻¹ * u ∈ Subgroup.centralizer (L : Set G)
  rw [e]
  exact Subgroup.mul_mem _ hs.2.2 (Subgroup.inv_mem _ hd.2)

theorem pr_mul {x y : G} (hx : x ∈ pCoreOf 2 M) (hy : y ∈ pCoreOf 2 M) :
    C.pr hQUD (x * y) = C.pr hQUD x + C.pr hQUD y := by
  obtain ⟨u, hu, hd⟩ := hQUD x hx
  obtain ⟨v, hv, he⟩ := hQUD y hy
  have hvM : v⁻¹ ∈ M :=
    M.inv_mem (pCoreOf_le' M ((C.h.Uq_le_Xq.trans (Xq_le_pCoreOf M)) hv))
  have hconj : v⁻¹ * (u⁻¹ * x) * v⁻¹⁻¹ ∈ Dq M L :=
    (Subgroup.mem_normalizer_iff.1 (le_normalizer_Dq C.h.le_normalizer hvM) _).1 hd
  have e : (u * v)⁻¹ * (x * y) = (v⁻¹ * (u⁻¹ * x) * v⁻¹⁻¹) * (v⁻¹ * y) := by group
  rw [C.pr_eq hQUD hx hu hd, C.pr_eq hQUD hy hv he,
    C.pr_eq hQUD ((pCoreOf 2 M).mul_mem hx hy) ((Uq M T L).mul_mem hu hv)
      (by rw [e]; exact (Dq M L).mul_mem hconj he)]
  exact C.N.co_mul ⟨u, hu⟩ ⟨v, hv⟩

theorem pr_one : C.pr hQUD 1 = 0 := by
  have h := C.pr_mul hQUD (pCoreOf 2 M).one_mem (pCoreOf 2 M).one_mem
  rw [mul_one] at h
  exact left_eq_add.1 h

theorem pr_inv {x : G} (hx : x ∈ pCoreOf 2 M) : C.pr hQUD x⁻¹ = -C.pr hQUD x := by
  have h := C.pr_mul hQUD hx ((pCoreOf 2 M).inv_mem hx)
  rw [mul_inv_cancel, C.pr_one hQUD] at h
  exact eq_neg_of_add_eq_zero_right h.symm

theorem pr_conj {g x : G} (hg : g ∈ L ⊔ pCoreOf 2 M) (hx : x ∈ pCoreOf 2 M) :
    C.pr hQUD (g * x * g⁻¹) = mat (C.rho ⟨g, hg⟩) *ᵥ C.pr hQUD x := by
  obtain ⟨u, hu, hd⟩ := hQUD x hx
  have hgM : g ∈ M := C.sup_le_M hg
  have hgu : g * u * g⁻¹ ∈ Uq M T L := (Subgroup.mem_normalizer_iff.1 (C.hMU hgM) u).1 hu
  have hgd : g * (u⁻¹ * x) * g⁻¹ ∈ Dq M L :=
    (Subgroup.mem_normalizer_iff.1 (le_normalizer_Dq C.h.le_normalizer hgM) _).1 hd
  have hgx : g * x * g⁻¹ ∈ pCoreOf 2 M :=
    (Subgroup.mem_normalizer_iff.1 (le_normalizer_pCoreOf M hgM) x).1 hx
  have e : (g * u * g⁻¹)⁻¹ * (g * x * g⁻¹) = g * (u⁻¹ * x) * g⁻¹ := by group
  rw [C.pr_eq hQUD hgx hgu (by rw [e]; exact hgd), C.pr_eq hQUD hx hu hd]
  exact C.co_conj ⟨g, hg⟩ rfl

theorem pr_comm_conj {h z y : G} (hh : h ∈ L ⊔ pCoreOf 2 M) (hc : ⁅z, y⁆ ∈ pCoreOf 2 M) :
    C.pr hQUD ⁅h * z * h⁻¹, h * y * h⁻¹⁆ = mat (C.rho ⟨h, hh⟩) *ᵥ C.pr hQUD ⁅z, y⁆ := by
  have e : ⁅h * z * h⁻¹, h * y * h⁻¹⁆ = h * ⁅z, y⁆ * h⁻¹ := by
    simp only [commutatorElement_def]
    group
  rw [e, C.pr_conj hQUD hh hc]

noncomputable def gam (z y : G) : Fin 2 → F :=
  ![C.pr hQUD ⁅z, y⁆ (.inl 1), C.pr hQUD ⁅z, y⁆ (.inr 1)]

section Good

variable (θ : MulAut ↥(T1 M T L))
  (hQQ : ∀ x ∈ pCoreOf 2 M ⊓ Qt M θ, ∃ u ∈ C.Usub (perp (pt₀ F)), u⁻¹ * x ∈ Dq M L)
  (hDtQ : Dt M L θ ≤ pCoreOf 2 M)

include hQQ in
theorem pr_mem_perp {x : G} (hx : x ∈ pCoreOf 2 M ⊓ Qt M θ) : C.pr hQUD x ∈ perp (pt₀ F) := by
  obtain ⟨u, hu, hd⟩ := hQQ x hx
  obtain ⟨huU, hco⟩ := (C.mem_Usub).1 hu
  rw [C.pr_eq hQUD hx.1 huU hd]
  exact hco

theorem rho_mem_X₂ (hN : C.rhoIm (Qt M θ) = X₂ F) {z : G} (hz : z ∈ Qt M θ)
    (hzK : z ∈ L ⊔ pCoreOf 2 M) : C.rho ⟨z, hzK⟩ ∈ X₂ F :=
  hN ▸ (C.mem_rhoIm).2 ⟨z, hzK, hz, rfl⟩

include hQUD hQQ hDtQ in
theorem comm_mem_inf_Qt (hE : C.rhoIm (Ut M T L θ) = X₂ F) (hN : C.rhoIm (Qt M θ) = X₂ F)
    (hDQt : Dq M L ≤ Qt M θ) {z y : G} (hz : z ∈ Qt M θ) (hy : y ∈ L ⊔ pCoreOf 2 M)
    (hyQ : C.rho ⟨y, hy⟩ ∈ Q₂ F) : ⁅z, y⁆ ∈ pCoreOf 2 M ⊓ Qt M θ := by
  have : CharP F 2 := charP_of_card_eq_prime_pow C.hF
  have hzK : z ∈ L ⊔ pCoreOf 2 M := Qt_le_sup θ hz
  have hyz : y * z⁻¹ * y⁻¹ ∈ Qt M θ :=
    C.conj_mem_Qt θ hQUD hQQ hDtQ hE hN hDQt hy (Q₂_le_P₂ hyQ) ((Qt M θ).inv_mem hz)
  have hc : ⁅z, y⁆ = z * (y * z⁻¹ * y⁻¹) := by
    rw [commutatorElement_def]
    group
  have hcQt : ⁅z, y⁆ ∈ Qt M θ := hc ▸ (Qt M θ).mul_mem hz hyz
  have hcK : ⁅z, y⁆ ∈ L ⊔ pCoreOf 2 M := Qt_le_sup θ hcQt
  refine ⟨(C.rho_eq_one_iff ⟨_, hcK⟩).1 ?_, hcQt⟩
  rw [C.rho_comm_eq hzK hy, commutatorElement_def,
    Q₂_comm (X₂_le_Q₂ (C.rho_mem_X₂ θ hN hz hzK)) hyQ]
  group

include hQUD hQQ hDtQ in
theorem gam_mul_left (hE : C.rhoIm (Ut M T L θ) = X₂ F) (hN : C.rhoIm (Qt M θ) = X₂ F)
    (hDQt : Dq M L ≤ Qt M θ) {z z' y : G} (hz : z ∈ Qt M θ) (hz' : z' ∈ Qt M θ)
    (hy : y ∈ L ⊔ pCoreOf 2 M) (hyQ : C.rho ⟨y, hy⟩ ∈ Q₂ F) :
    C.gam hQUD (z * z') y = C.gam hQUD z y + C.gam hQUD z' y := by
  have hzK : z ∈ L ⊔ pCoreOf 2 M := Qt_le_sup θ hz
  have h1 := C.comm_mem_inf_Qt hQUD θ hQQ hDtQ hE hN hDQt hz hy hyQ
  have h2 := C.comm_mem_inf_Qt hQUD θ hQQ hDtQ hE hN hDQt hz' hy hyQ
  have e : ⁅z * z', y⁆ = z * ⁅z', y⁆ * z⁻¹ * ⁅z, y⁆ := by
    simp only [commutatorElement_def]
    group
  have hc : z * ⁅z', y⁆ * z⁻¹ ∈ pCoreOf 2 M :=
    (Subgroup.mem_normalizer_iff.1 (le_normalizer_pCoreOf M (C.sup_le_M hzK)) _).1 h2.1
  have hp : C.pr hQUD ⁅z * z', y⁆ = C.pr hQUD ⁅z', y⁆ + C.pr hQUD ⁅z, y⁆ := by
    rw [e, C.pr_mul hQUD hc h1.1, C.pr_conj hQUD hzK h2.1,
      (mem_fixer.1 (C.rho_mem_X₂ θ hN hz hzK)) _ (C.pr_mem_perp hQUD θ hQQ h2)]
  simp only [gam, hp]
  funext i
  fin_cases i <;> simp [add_comm]

include hQUD hQQ hDtQ in
theorem gam_mul_right (hE : C.rhoIm (Ut M T L θ) = X₂ F) (hN : C.rhoIm (Qt M θ) = X₂ F)
    (hDQt : Dq M L ≤ Qt M θ) {z y y' : G} (hz : z ∈ Qt M θ) (hy : y ∈ L ⊔ pCoreOf 2 M)
    (hyQ : C.rho ⟨y, hy⟩ ∈ Q₂ F) (hy' : y' ∈ L ⊔ pCoreOf 2 M) (hyQ' : C.rho ⟨y', hy'⟩ ∈ Q₂ F) :
    C.gam hQUD z (y * y') = C.gam hQUD z y + C.gam hQUD z y' := by
  have : CharP F 2 := charP_of_card_eq_prime_pow C.hF
  have h1 := C.comm_mem_inf_Qt hQUD θ hQQ hDtQ hE hN hDQt hz hy hyQ
  have h2 := C.comm_mem_inf_Qt hQUD θ hQQ hDtQ hE hN hDQt hz hy' hyQ'
  have e : ⁅z, y * y'⁆ = ⁅z, y⁆ * (y * ⁅z, y'⁆ * y⁻¹) := by
    simp only [commutatorElement_def]
    group
  have hc : y * ⁅z, y'⁆ * y⁻¹ ∈ pCoreOf 2 M :=
    (Subgroup.mem_normalizer_iff.1 (le_normalizer_pCoreOf M (C.sup_le_M hy)) _).1 h2.1
  have hp : C.pr hQUD ⁅z, y * y'⁆ =
      C.pr hQUD ⁅z, y⁆ + mat (C.rho ⟨y, hy⟩) *ᵥ C.pr hQUD ⁅z, y'⁆ := by
    rw [e, C.pr_mul hQUD h1.1 hc, C.pr_conj hQUD hy h2.1]
  obtain ⟨c1, c2⟩ := mulVec_inl_one_of_mem_Q₂ hyQ (C.pr_mem_perp hQUD θ hQQ h2)
  simp only [gam, hp]
  funext i
  fin_cases i <;> simp [c1, c2]

theorem gam_of_mem_pCore (hN : C.rhoIm (Qt M θ) = X₂ F) {z x : G} (hz : z ∈ Qt M θ)
    (hx : x ∈ pCoreOf 2 M) : C.gam hQUD z x = 0 := by
  have hzK : z ∈ L ⊔ pCoreOf 2 M := Qt_le_sup θ hz
  obtain ⟨u, hu, hco, hd⟩ := C.comm_mem_of_X₂ hx hzK (C.rho_mem_X₂ θ hN hz hzK)
  have hc : ⁅z, x⁆ ∈ pCoreOf 2 M := by
    rw [commutatorElement_def]
    exact (pCoreOf 2 M).mul_mem ((Subgroup.mem_normalizer_iff.1
      (le_normalizer_pCoreOf M (C.sup_le_M hzK)) x).1 hx) ((pCoreOf 2 M).inv_mem hx)
  obtain ⟨h1, -, h3⟩ := mem_pt₀.1 hco
  simp only [gam, C.pr_eq hQUD hc hu hd, h1, h3]
  funext i
  fin_cases i <;> simp

include hQQ in
theorem gam_of_mem_inf {x y : G} (hx : x ∈ pCoreOf 2 M ⊓ Qt M θ) (hy : y ∈ L ⊔ pCoreOf 2 M)
    (hyQ : C.rho ⟨y, hy⟩ ∈ Q₂ F) : C.gam hQUD x y = 0 := by
  have : CharP F 2 := charP_of_card_eq_prime_pow C.hF
  have hxi : x⁻¹ ∈ pCoreOf 2 M := (pCoreOf 2 M).inv_mem hx.1
  have hc : y * x⁻¹ * y⁻¹ ∈ pCoreOf 2 M :=
    (Subgroup.mem_normalizer_iff.1 (le_normalizer_pCoreOf M (C.sup_le_M hy)) _).1 hxi
  have e : ⁅x, y⁆ = x * (y * x⁻¹ * y⁻¹) := by
    rw [commutatorElement_def]
    group
  have hp : C.pr hQUD ⁅x, y⁆ = C.pr hQUD x - mat (C.rho ⟨y, hy⟩) *ᵥ C.pr hQUD x := by
    rw [e, C.pr_mul hQUD hx.1 hc, C.pr_conj hQUD hy hxi, C.pr_inv hQUD hx.1, Matrix.mulVec_neg,
      sub_eq_add_neg]
  obtain ⟨c1, c2⟩ := mulVec_inl_one_of_mem_Q₂ hyQ (C.pr_mem_perp hQUD θ hQQ hx)
  simp only [gam, hp]
  funext i
  fin_cases i <;> simp [c1, c2]

include hQQ hDtQ in
theorem pr_Dt_coord (hN : C.rhoIm (Qt M θ) = X₂ F) (hT : Q₂ F ≤ C.T0bar) {d : G}
    (hd : d ∈ Dt M L θ) : C.pr hQUD d (.inl 1) = 0 ∧ C.pr hQUD d (.inr 1) = 0 := by
  have : CharP F 2 := charP_of_card_eq_prime_pow C.hF
  have hdQ : d ∈ pCoreOf 2 M := hDtQ hd
  have hdQt : d ∈ Qt M θ := tImage_mono' θ (inf_le_left : Dq M L ≤ pCoreOf 2 M) hd
  have hperp := C.pr_mem_perp hQUD θ hQQ ⟨hdQ, hdQt⟩
  have hfix : ∀ (t : G) (ht : t ∈ T1 M T L),
      mat (C.rho ⟨t, T1_le_sup ht⟩) *ᵥ C.pr hQUD d = C.pr hQUD d := by
    intro t ht
    obtain ⟨d₀, hd₀T, hd₀, hd₀e⟩ := mem_tImage.1 hd
    obtain ⟨l, hl, q, hq, e⟩ := C.exists_mul_of_mem_T1 (θ⁻¹ ⟨t, ht⟩).2
    have hlT : l ∈ T1 M T L := ⟨hl.1, Subgroup.mem_sup_left hl.2⟩
    have hqT : q ∈ T1 M T L := C.pCore_le_T1 hq
    have hts : (⟨t, ht⟩ : ↥(T1 M T L)) = θ ⟨l, hlT⟩ * θ ⟨q, hqT⟩ := by
      rw [← map_mul]
      have : (⟨l, hlT⟩ * ⟨q, hqT⟩ : ↥(T1 M T L)) = θ⁻¹ ⟨t, ht⟩ := Subtype.ext e
      rw [this, MulAut.apply_inv_self]
    have hl'K : ((θ ⟨l, hlT⟩ : ↥(T1 M T L)) : G) ∈ L ⊔ pCoreOf 2 M := T1_le_sup (θ ⟨l, hlT⟩).2
    have hq'K : ((θ ⟨q, hqT⟩ : ↥(T1 M T L)) : G) ∈ L ⊔ pCoreOf 2 M := T1_le_sup (θ ⟨q, hqT⟩).2
    have hq'X := C.rho_mem_X₂ θ hN (mem_tImage.2 ⟨q, hqT, hq, rfl⟩) hq'K
    have hcomm : ((θ ⟨l, hlT⟩ : ↥(T1 M T L)) : G) * d * ((θ ⟨l, hlT⟩ : ↥(T1 M T L)) : G)⁻¹ = d := by
      have h1 : l * d₀ = d₀ * l := Subgroup.mem_centralizer_iff.1 hd₀.2 l hl.2
      have h2 : (⟨l, hlT⟩ : ↥(T1 M T L)) * ⟨d₀, hd₀T⟩ = ⟨d₀, hd₀T⟩ * ⟨l, hlT⟩ := Subtype.ext h1
      have h3 := congrArg (fun x => ((θ x : ↥(T1 M T L)) : G)) h2
      simp only [map_mul, Subgroup.coe_mul] at h3
      rw [← hd₀e, h3]
      group
    have hte : t = ((θ ⟨l, hlT⟩ : ↥(T1 M T L)) : G) * ((θ ⟨q, hqT⟩ : ↥(T1 M T L)) : G) :=
      congrArg Subtype.val hts
    have hρ : C.rho ⟨t, T1_le_sup ht⟩ = C.rho ⟨_, hl'K⟩ * C.rho ⟨_, hq'K⟩ := by
      rw [← C.rho_mul_eq hl'K hq'K (hte ▸ T1_le_sup ht)]
      congr 1
      exact Subtype.ext hte
    rw [hρ, mat_mul_mulVec, (mem_fixer.1 hq'X) _ hperp, ← C.pr_conj hQUD hl'K hdQ, hcomm]
  have hfix' : ∀ g ∈ Q₂ F, mat g *ᵥ C.pr hQUD d = C.pr hQUD d := by
    intro g hg
    obtain ⟨t, ht⟩ := hT hg
    rw [← ht, C.rho1_apply]
    exact hfix t t.2
  exact coord_eq_zero_of_fix hperp (hfix' _ (qe_mem_Q₂ _ _ _)) (hfix' _ (qe_mem_Q₂ _ _ _))

include hQQ hDtQ in
theorem gam_congr_left (hE : C.rhoIm (Ut M T L θ) = X₂ F) (hN : C.rhoIm (Qt M θ) = X₂ F)
    (hDQt : Dq M L ≤ Qt M θ) {z z' y : G} (hz : z ∈ Qt M θ) (hz' : z' ∈ Qt M θ)
    (hρ : C.rho ⟨z, Qt_le_sup θ hz⟩ = C.rho ⟨z', Qt_le_sup θ hz'⟩)
    (hy : y ∈ L ⊔ pCoreOf 2 M) (hyQ : C.rho ⟨y, hy⟩ ∈ Q₂ F) :
    C.gam hQUD z y = C.gam hQUD z' y := by
  have hK : z⁻¹ * z' ∈ L ⊔ pCoreOf 2 M :=
    (L ⊔ pCoreOf 2 M).mul_mem ((L ⊔ pCoreOf 2 M).inv_mem (Qt_le_sup θ hz)) (Qt_le_sup θ hz')
  have hx : z⁻¹ * z' ∈ pCoreOf 2 M ⊓ Qt M θ := by
    refine ⟨(C.rho_eq_one_iff ⟨_, hK⟩).1 ?_, (Qt M θ).mul_mem ((Qt M θ).inv_mem hz) hz'⟩
    have e : (⟨z⁻¹ * z', hK⟩ : ↥(L ⊔ pCoreOf 2 M)) =
        (⟨z, Qt_le_sup θ hz⟩ : ↥(L ⊔ pCoreOf 2 M))⁻¹ * ⟨z', Qt_le_sup θ hz'⟩ := rfl
    rw [e, map_mul, map_inv, hρ, inv_mul_cancel]
  have e : z' = z * (z⁻¹ * z') := by group
  rw [e, C.gam_mul_left hQUD θ hQQ hDtQ hE hN hDQt hz hx.2 hy hyQ,
    C.gam_of_mem_inf hQUD θ hQQ hx hy hyQ, add_zero]

include hQQ hDtQ in
theorem gam_congr_right_of_rho (hE : C.rhoIm (Ut M T L θ) = X₂ F)
    (hN : C.rhoIm (Qt M θ) = X₂ F) (hDQt : Dq M L ≤ Qt M θ) {z y y' : G} (hz : z ∈ Qt M θ)
    (hy : y ∈ L ⊔ pCoreOf 2 M) (hyQ : C.rho ⟨y, hy⟩ ∈ Q₂ F) (hy' : y' ∈ L ⊔ pCoreOf 2 M)
    (hρ : C.rho ⟨y, hy⟩ = C.rho ⟨y', hy'⟩) : C.gam hQUD z y = C.gam hQUD z y' := by
  have hxK : y⁻¹ * y' ∈ L ⊔ pCoreOf 2 M :=
    (L ⊔ pCoreOf 2 M).mul_mem ((L ⊔ pCoreOf 2 M).inv_mem hy) hy'
  have hx1 : C.rho ⟨y⁻¹ * y', hxK⟩ = 1 := by
    have e : (⟨y⁻¹ * y', hxK⟩ : ↥(L ⊔ pCoreOf 2 M)) =
        (⟨y, hy⟩ : ↥(L ⊔ pCoreOf 2 M))⁻¹ * ⟨y', hy'⟩ := rfl
    rw [e, map_mul, map_inv, hρ, inv_mul_cancel]
  have hxQ : C.rho ⟨y⁻¹ * y', hxK⟩ ∈ Q₂ F := by
    rw [hx1]
    exact (Q₂ F).one_mem
  have e : y' = y * (y⁻¹ * y') := by group
  rw [e, C.gam_mul_right hQUD θ hQQ hDtQ hE hN hDQt hz hy hyQ hxK hxQ,
    C.gam_of_mem_pCore hQUD θ hN hz ((C.rho_eq_one_iff _).1 hx1), add_zero]

include hQQ hDtQ in
theorem gam_of_mem_Qt (hE : C.rhoIm (Ut M T L θ) = X₂ F) (hN : C.rhoIm (Qt M θ) = X₂ F)
    (hDQt : Dq M L ≤ Qt M θ) {z z' : G} (hz : z ∈ Qt M θ) (hz' : z' ∈ Qt M θ) :
    C.gam hQUD z z' = 0 := by
  have : CharP F 2 := charP_of_card_eq_prime_pow C.hF
  obtain ⟨ν, hν0, hν1⟩ := exists_ne_zero_ne_one (show 2 < Nat.card F by
    have := C.q_ge_four; omega)
  let A₀ : Matrix.SpecialLinearGroup (Fin 2) F :=
    ⟨!![ν, 0; 0, ν⁻¹], by simp [Matrix.det_fin_two, hν0]⟩
  have hgP : levHom₂ A₀ ∈ P₂ F := lev₂_le_P₂ (by rw [← range_levHom₂]; exact ⟨A₀, rfl⟩)
  have he₁ : mat (levHom₂ A₀) *ᵥ e₁ F = e₁ F := by
    rw [mat_levHom₂, iotaM_mulVec]
    refine ext4 ?_ ?_ ?_ ?_ <;> simp [e₁, e₂, f₁, f₂]
  set h := C.lift (levHom₂ A₀)
  have hhK : h ∈ L ⊔ pCoreOf 2 M := Subgroup.mem_sup_left (C.lift_mem _)
  have hhρ : C.rho ⟨h, hhK⟩ = levHom₂ A₀ := C.rho_lift _
  have hhP : C.rho ⟨h, hhK⟩ ∈ P₂ F := hhρ ▸ hgP
  have hzK := Qt_le_sup θ hz
  have hz'K := Qt_le_sup θ hz'
  have hz1 := C.conj_mem_Qt θ hQUD hQQ hDtQ hE hN hDQt hhK hhP hz
  have hz1' := C.conj_mem_Qt θ hQUD hQQ hDtQ hE hN hDQt hhK hhP hz'
  have hfix : ∀ {y : G} (hy : y ∈ Qt M θ) (hy' : h * y * h⁻¹ ∈ L ⊔ pCoreOf 2 M),
      C.rho ⟨h * y * h⁻¹, hy'⟩ = C.rho ⟨y, Qt_le_sup θ hy⟩ := by
    intro y hy hy'
    obtain ⟨s, hs⟩ := mem_X₂_iff.1 (C.rho_mem_X₂ θ hN hy (Qt_le_sup θ hy))
    rw [C.rho_conj_eq hhK (Qt_le_sup θ hy), hhρ, ← hs, transv_conj, he₁]
  have hz'Q : C.rho ⟨z', hz'K⟩ ∈ Q₂ F := X₂_le_Q₂ (C.rho_mem_X₂ θ hN hz' hz'K)
  have hz1'Q : C.rho ⟨h * z' * h⁻¹, Qt_le_sup θ hz1'⟩ ∈ Q₂ F :=
    X₂_le_Q₂ (C.rho_mem_X₂ θ hN hz1' (Qt_le_sup θ hz1'))
  have h1 : C.gam hQUD z z' = C.gam hQUD (h * z * h⁻¹) (h * z' * h⁻¹) := by
    rw [C.gam_congr_left hQUD θ hQQ hDtQ hE hN hDQt hz hz1 (hfix hz _).symm hz'K hz'Q]
    exact C.gam_congr_right_of_rho hQUD θ hQQ hDtQ hE hN hDQt hz1 hz'K hz'Q
      (Qt_le_sup θ hz1') (hfix hz' _).symm
  have hc := (C.comm_mem_inf_Qt hQUD θ hQQ hDtQ hE hN hDQt hz hz'K hz'Q).1
  have h2 : C.gam hQUD (h * z * h⁻¹) (h * z' * h⁻¹) =
      ![ν * C.gam hQUD z z' 0, ν⁻¹ * C.gam hQUD z z' 1] := by
    simp only [gam, C.pr_comm_conj hQUD hhK hc, hhρ, mat_levHom₂, iotaM_mulVec]
    funext i
    fin_cases i <;> simp [A₀, e₁, e₂, f₁, f₂]
  rw [h2] at h1
  have c0 := congrFun h1 0
  have c1 := congrFun h1 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at c0 c1
  have hν1' : ν⁻¹ ≠ 1 := fun h => hν1 (by rw [← inv_inv ν, h, inv_one])
  funext i
  fin_cases i
  · have : (ν - 1) * C.gam hQUD z z' 0 = 0 := by linear_combination -c0
    simpa [sub_ne_zero.2 hν1] using this
  · have : (ν⁻¹ - 1) * C.gam hQUD z z' 1 = 0 := by linear_combination -c1
    simpa [sub_ne_zero.2 hν1'] using this

include hQQ hDtQ in
theorem gam_congr_right (hE : C.rhoIm (Ut M T L θ) = X₂ F) (hN : C.rhoIm (Qt M θ) = X₂ F)
    (hDQt : Dq M L ≤ Qt M θ) {z y y' : G} (hz : z ∈ Qt M θ)
    (hy : y ∈ L ⊔ pCoreOf 2 M) (hyQ : C.rho ⟨y, hy⟩ ∈ Q₂ F) (hy' : y' ∈ L ⊔ pCoreOf 2 M)
    (hX : (C.rho ⟨y, hy⟩)⁻¹ * C.rho ⟨y', hy'⟩ ∈ X₂ F) :
    C.gam hQUD z y = C.gam hQUD z y' := by
  have hwK : y⁻¹ * y' ∈ L ⊔ pCoreOf 2 M :=
    (L ⊔ pCoreOf 2 M).mul_mem ((L ⊔ pCoreOf 2 M).inv_mem hy) hy'
  have hwρ : C.rho ⟨y⁻¹ * y', hwK⟩ = (C.rho ⟨y, hy⟩)⁻¹ * C.rho ⟨y', hy'⟩ := by
    rw [← map_inv, ← map_mul]
    rfl
  have hwX : C.rho ⟨y⁻¹ * y', hwK⟩ ∈ C.rhoIm (Qt M θ) := by
    rw [hN, hwρ]
    exact hX
  obtain ⟨z'', hz''K, hz'', hρ''⟩ := (C.mem_rhoIm).1 hwX
  have hxK : z''⁻¹ * (y⁻¹ * y') ∈ L ⊔ pCoreOf 2 M :=
    (L ⊔ pCoreOf 2 M).mul_mem ((L ⊔ pCoreOf 2 M).inv_mem hz''K) hwK
  have hxQ : z''⁻¹ * (y⁻¹ * y') ∈ pCoreOf 2 M := by
    refine (C.rho_eq_one_iff ⟨_, hxK⟩).1 ?_
    have e : (⟨z''⁻¹ * (y⁻¹ * y'), hxK⟩ : ↥(L ⊔ pCoreOf 2 M)) =
        (⟨z'', hz''K⟩ : ↥(L ⊔ pCoreOf 2 M))⁻¹ * ⟨y⁻¹ * y', hwK⟩ := rfl
    rw [e, map_mul, map_inv, hρ'', inv_mul_cancel]
  have hz''Q : C.rho ⟨z'', hz''K⟩ ∈ Q₂ F := X₂_le_Q₂ (C.rho_mem_X₂ θ hN hz'' hz''K)
  have hxQ₂ : C.rho ⟨_, hxK⟩ ∈ Q₂ F := by
    rw [(C.rho_eq_one_iff _).2 hxQ]
    exact (Q₂ F).one_mem
  have hpK : z'' * (z''⁻¹ * (y⁻¹ * y')) ∈ L ⊔ pCoreOf 2 M :=
    (L ⊔ pCoreOf 2 M).mul_mem hz''K hxK
  have hpQ : C.rho ⟨_, hpK⟩ ∈ Q₂ F := by
    rw [C.rho_mul_eq hz''K hxK]
    exact (Q₂ F).mul_mem hz''Q hxQ₂
  have e : y' = y * (z'' * (z''⁻¹ * (y⁻¹ * y'))) := by group
  rw [e, C.gam_mul_right hQUD θ hQQ hDtQ hE hN hDQt hz hy hyQ hpK hpQ,
    C.gam_mul_right hQUD θ hQQ hDtQ hE hN hDQt hz hz''K hz''Q hxK hxQ₂,
    C.gam_of_mem_Qt hQUD θ hQQ hDtQ hE hN hDQt hz hz'', C.gam_of_mem_pCore hQUD θ hN hz hxQ,
    add_zero, add_zero]

include hQQ hDtQ in
theorem gam_eq_zero (hE : C.rhoIm (Ut M T L θ) = X₂ F) (hN : C.rhoIm (Qt M θ) = X₂ F)
    (hDQt : Dq M L ≤ Qt M θ) (hq : 8 ≤ Nat.card F) {z y : G}
    (hz : z ∈ Qt M θ) (hy : y ∈ L ⊔ pCoreOf 2 M) (hyQ : C.rho ⟨y, hy⟩ ∈ Q₂ F) :
    C.gam hQUD z y = 0 := by
  have : CharP F 2 := charP_of_card_eq_prime_pow C.hF
  have hzs : ∀ s : F, ∃ z : G, ∃ hz : z ∈ Qt M θ,
      C.rho ⟨z, Qt_le_sup θ hz⟩ = transv (e₁ F) s := by
    intro s
    have hm : transv (e₁ F) s ∈ C.rhoIm (Qt M θ) := by
      rw [hN]
      exact transv_mem_X₂ s
    obtain ⟨z, hzK, hz, hρ⟩ := (C.mem_rhoIm).1 hm
    exact ⟨z, hz, hρ⟩
  choose zs hzs hzsρ using hzs
  let yw : (Fin 2 → F) → G := fun w => C.lift (qe (w 0) (w 1) 0)
  have hywK : ∀ w, yw w ∈ L ⊔ pCoreOf 2 M := fun w => Subgroup.mem_sup_left (C.lift_mem _)
  have hywρ : ∀ w, C.rho ⟨yw w, hywK w⟩ = qe (w 0) (w 1) 0 := fun w => C.rho_lift _
  have hywQ : ∀ w, C.rho ⟨yw w, hywK w⟩ ∈ Q₂ F := fun w => by
    rw [hywρ]
    exact qe_mem_Q₂ _ _ _
  have hadd : ∀ s w w', C.gam hQUD (zs s) (yw (w + w')) =
      C.gam hQUD (zs s) (yw w) + C.gam hQUD (zs s) (yw w') := by
    intro s w w'
    have hK := (L ⊔ pCoreOf 2 M).mul_mem (hywK w) (hywK w')
    rw [← C.gam_mul_right hQUD θ hQQ hDtQ hE hN hDQt (hzs s) (hywK w) (hywQ w) (hywK w')
      (hywQ w')]
    refine C.gam_congr_right hQUD θ hQQ hDtQ hE hN hDQt (hzs s) (hywK _) (hywQ _) hK ?_
    rw [C.rho_mul_eq (hywK w) (hywK w') hK, hywρ, hywρ, hywρ, qe_mul]
    simp only [Pi.add_apply]
    exact qe_inv_mul_mem_X₂ _ _ _ _
  have hadds : ∀ s s' w, C.gam hQUD (zs (s + s')) (yw w) =
      C.gam hQUD (zs s) (yw w) + C.gam hQUD (zs s') (yw w) := by
    intro s s' w
    rw [← C.gam_mul_left hQUD θ hQQ hDtQ hE hN hDQt (hzs s) (hzs s') (hywK w) (hywQ w)]
    refine C.gam_congr_left hQUD θ hQQ hDtQ hE hN hDQt (hzs _)
      ((Qt M θ).mul_mem (hzs s) (hzs s')) ?_ (hywK w) (hywQ w)
    rw [hzsρ, C.rho_mul_eq (Qt_le_sup θ (hzs s)) (Qt_le_sup θ (hzs s')) _, hzsρ, hzsρ,
      transv_mul]
  have hequiv : ∀ (g : Sp4 F), g ∈ P₂ F → ∀ (s s' : F) (w w' : Fin 2 → F),
      g * transv (e₁ F) s * g⁻¹ = transv (e₁ F) s' →
      g * qe (w 0) (w 1) 0 * g⁻¹ = qe (w' 0) (w' 1) 0 →
      C.gam hQUD (zs s') (yw w') = ![(mat g *ᵥ C.pr hQUD ⁅zs s, yw w⁆) (.inl 1),
        (mat g *ᵥ C.pr hQUD ⁅zs s, yw w⁆) (.inr 1)] := by
    intro g hg s s' w w' hzg hyg
    set h := C.lift g
    have hhK : h ∈ L ⊔ pCoreOf 2 M := Subgroup.mem_sup_left (C.lift_mem _)
    have hhρ : C.rho ⟨h, hhK⟩ = g := C.rho_lift _
    have hhP : C.rho ⟨h, hhK⟩ ∈ P₂ F := hhρ ▸ hg
    have hz1 : h * zs s * h⁻¹ ∈ Qt M θ :=
      C.conj_mem_Qt θ hQUD hQQ hDtQ hE hN hDQt hhK hhP (hzs s)
    have hy1K : h * yw w * h⁻¹ ∈ L ⊔ pCoreOf 2 M :=
      (L ⊔ pCoreOf 2 M).mul_mem ((L ⊔ pCoreOf 2 M).mul_mem hhK (hywK w))
        ((L ⊔ pCoreOf 2 M).inv_mem hhK)
    have hy1ρ : C.rho ⟨h * yw w * h⁻¹, hy1K⟩ = qe (w' 0) (w' 1) 0 := by
      rw [C.rho_conj_eq hhK (hywK w), hhρ, hywρ, hyg]
    have hz1ρ : C.rho ⟨h * zs s * h⁻¹, Qt_le_sup θ hz1⟩ =
        C.rho ⟨zs s', Qt_le_sup θ (hzs s')⟩ := by
      rw [C.rho_conj_eq hhK (Qt_le_sup θ (hzs s)), hhρ, hzsρ, hzg, hzsρ]
    have hc := (C.comm_mem_inf_Qt hQUD θ hQQ hDtQ hE hN hDQt (hzs s) (hywK w) (hywQ w)).1
    have h1 : C.gam hQUD (h * zs s * h⁻¹) (h * yw w * h⁻¹) =
        ![(mat g *ᵥ C.pr hQUD ⁅zs s, yw w⁆) (.inl 1),
          (mat g *ᵥ C.pr hQUD ⁅zs s, yw w⁆) (.inr 1)] := by
      simp only [gam, C.pr_comm_conj hQUD hhK hc, hhρ]
    have hy1Q : C.rho ⟨h * yw w * h⁻¹, hy1K⟩ ∈ Q₂ F := by
      rw [hy1ρ]
      exact qe_mem_Q₂ _ _ _
    have h2 := C.gam_congr_left hQUD θ hQQ hDtQ hE hN hDQt hz1 (hzs s') hz1ρ hy1K hy1Q
    have h3 : C.gam hQUD (zs s') (yw w') = C.gam hQUD (zs s') (h * yw w * h⁻¹) := by
      refine C.gam_congr_right hQUD θ hQQ hDtQ hE hN hDQt (hzs s') (hywK w') (hywQ w')
        hy1K ?_
      rw [hywρ, hy1ρ, inv_mul_cancel]
      exact (X₂ F).one_mem
    rw [h3, ← h2, h1]
  have hlev : ∀ (A : Matrix.SpecialLinearGroup (Fin 2) F) (s : F) (w : Fin 2 → F),
      C.gam hQUD (zs s) (yw ![A 0 0 * w 0 + A 0 1 * w 1, A 1 0 * w 0 + A 1 1 * w 1]) =
        ![A 0 0 * C.gam hQUD (zs s) (yw w) 0 + A 0 1 * C.gam hQUD (zs s) (yw w) 1,
          A 1 0 * C.gam hQUD (zs s) (yw w) 0 + A 1 1 * C.gam hQUD (zs s) (yw w) 1] := by
    intro A s w
    have he₁ : mat (levHom₂ A) *ᵥ e₁ F = e₁ F := by
      rw [mat_levHom₂, iotaM_mulVec]
      refine ext4 ?_ ?_ ?_ ?_ <;> simp [e₁, e₂, f₁, f₂]
    have hP : levHom₂ A ∈ P₂ F := lev₂_le_P₂ (by rw [← range_levHom₂]; exact ⟨A, rfl⟩)
    rw [hequiv (levHom₂ A) hP s s w ![A 0 0 * w 0 + A 0 1 * w 1, A 1 0 * w 0 + A 1 1 * w 1]
      (by rw [transv_conj, he₁]) (by rw [qe_conj_of_fix he₁, levMat_levHom₂]; simp)]
    simp only [gam, mat_levHom₂, iotaM_mulVec]
    funext i
    fin_cases i <;> simp [e₁, e₂, f₁, f₂]
  have htor : ∀ (μ : Fˣ) (s : F) (w : Fin 2 → F),
      C.gam hQUD (zs ((μ : F) ^ 2 * s)) (yw ![(μ : F) * w 0, (μ : F) * w 1]) =
        C.gam hQUD (zs s) (yw w) := by
    intro μ s w
    have he₁ : mat (torusPt μ) *ᵥ e₁ F = (μ : F) • e₁ F := by
      rw [torusPt_mulVec]
      refine ext4 ?_ ?_ ?_ ?_ <;> simp [e₁, e₂, f₁, f₂]
    rw [hequiv (torusPt μ) (torusPt_mem_P₂ μ) s _ w ![(μ : F) * w 0, (μ : F) * w 1]
      (by rw [transv_conj, he₁, transv_smul_vec]) (by rw [torusPt_conj_qe, mul_zero]; simp)]
    simp only [gam, torusPt_mulVec]
    funext i
    fin_cases i <;> simp [e₁, e₂, f₁, f₂]
  have hschur : ∀ s w, C.gam hQUD (zs s) (yw w) = C.gam hQUD (zs s) (yw ![1, 0]) 0 • w := by
    intro s
    let g : (Fin 2 → F) →+ (Fin 2 → F) :=
      AddMonoidHom.mk' (fun w => C.gam hQUD (zs s) (yw w)) (hadd s)
    have hU : ∀ (a : F) (w : Fin 2 → F),
        g ![w 0 + a * w 1, w 1] = ![g w 0 + a * g w 1, g w 1] := by
      intro a w
      simpa [sl2Up, g] using hlev (sl2Up a) s w
    have hL : ∀ (a : F) (w : Fin 2 → F),
        g ![w 0, a * w 0 + w 1] = ![g w 0, a * g w 0 + g w 1] := by
      intro a w
      simpa [sl2Low, g] using hlev (sl2Low a) s w
    exact eq_smul_of_comm_sl2 g hU hL
  let lam : F →+ F := AddMonoidHom.mk' (fun s => C.gam hQUD (zs s) (yw ![1, 0]) 0)
    (fun s s' => by simp only [hadds, Pi.add_apply])
  have hlam : lam = 0 := by
    refine eq_zero_of_torus hq lam fun μ hμ c => ?_
    have h := htor (Units.mk0 μ hμ) c ![1, 0]
    simp only [Units.val_mk0, Matrix.cons_val_zero, Matrix.cons_val_one, mul_one,
      mul_zero] at h
    rw [hschur (μ ^ 2 * c) ![μ, 0]] at h
    have h0 := congrFun h 0
    simp only [Pi.smul_apply, Matrix.cons_val_zero, smul_eq_mul] at h0
    show C.gam hQUD (zs (μ ^ 2 * c)) (yw ![1, 0]) 0 = μ⁻¹ * C.gam hQUD (zs c) (yw ![1, 0]) 0
    rw [← h0]
    field_simp
  have hzK := Qt_le_sup θ hz
  obtain ⟨s, hs⟩ := mem_X₂_iff.1 (C.rho_mem_X₂ θ hN hz hzK)
  obtain ⟨a, b, c, hc⟩ := exists_eq_qe_of_mem_Q₂ hyQ
  have e1 : C.gam hQUD z y = C.gam hQUD (zs s) y :=
    C.gam_congr_left hQUD θ hQQ hDtQ hE hN hDQt hz (hzs s) (by rw [hzsρ, hs]) hy hyQ
  have e2 : C.gam hQUD (zs s) (yw ![a, b]) = C.gam hQUD (zs s) y := by
    refine C.gam_congr_right hQUD θ hQQ hDtQ hE hN hDQt (hzs s) (hywK _) (hywQ _) hy ?_
    rw [hywρ, hc]
    exact qe_inv_mul_mem_X₂ _ _ _ _
  have hl : C.gam hQUD (zs s) (yw ![1, 0]) 0 = 0 := congrArg (fun f : F →+ F => f s) hlam
  rw [e1, ← e2, hschur, hl, zero_smul]

include hQUD hQQ hDtQ in
theorem exists_comm_mem (hE : C.rhoIm (Ut M T L θ) = X₂ F) (hN : C.rhoIm (Qt M θ) = X₂ F)
    (hDQt : Dq M L ≤ Qt M θ) (hq : 8 ≤ Nat.card F) {z y : G}
    (hz : z ∈ Qt M θ) (hy : y ∈ L ⊔ pCoreOf 2 M) (hyQ : C.rho ⟨y, hy⟩ ∈ Q₂ F) :
    ∃ u ∈ C.Usub (pt₀ F), u⁻¹ * ⁅z, y⁆ ∈ Dq M L := by
  have hc := C.comm_mem_inf_Qt hQUD θ hQQ hDtQ hE hN hDQt hz hy hyQ
  have hg := C.gam_eq_zero hQUD θ hQQ hDtQ hE hN hDQt hq hz hy hyQ
  have h1 : C.pr hQUD ⁅z, y⁆ (.inl 1) = 0 := by simpa [gam] using congrFun hg 0
  have h2 : C.pr hQUD ⁅z, y⁆ (.inr 1) = 0 := by simpa [gam] using congrFun hg 1
  have hmem := mem_pt₀_of_coord (C.pr_mem_perp hQUD θ hQQ hc) h1 h2
  obtain ⟨u, hu, hd⟩ := hQUD _ hc.1
  refine ⟨u, (C.mem_Usub).2 ⟨hu, ?_⟩, hd⟩
  rw [← C.pr_eq hQUD hc.1 hu hd]
  exact hmem

end Good

end Proj

structure IsGood (θ : MulAut ↥(T1 M T L)) : Prop where
  rhoIm_Ut : C.rhoIm (Ut M T L θ) = X₂ F
  rhoIm_Qt : C.rhoIm (Qt M θ) = X₂ F
  inf_Qt : ∀ x ∈ pCoreOf 2 M ⊓ Qt M θ, ∃ u ∈ C.Usub (perp (pt₀ F)), u⁻¹ * x ∈ Dq M L
  Dt_le : Dt M L θ ≤ pCoreOf 2 M
  Dq_le : Dq M L ≤ Qt M θ

theorem Uq_le_pCore : Uq M T L ≤ pCoreOf 2 M := C.h.Uq_le_Xq.trans (Xq_le_pCoreOf M)

theorem co_mem_pt₀_of_mem_Dt (hQUD : ∀ x ∈ pCoreOf 2 M, ∃ u ∈ Uq M T L, u⁻¹ * x ∈ Dq M L)
    (hT : Q₂ F ≤ C.T0bar) (θ : MulAut ↥(T1 M T L)) (hθ : C.IsGood θ) {d : G}
    (hd : d ∈ Uq M T L) (hdD : d ∈ Dt M L θ) : C.N.co ⟨d, hd⟩ ∈ pt₀ F := by
  have hdQ := hθ.Dt_le hdD
  have hdQt : d ∈ Qt M θ := tImage_mono' θ (inf_le_left : Dq M L ≤ pCoreOf 2 M) hdD
  have hpr := C.pr_eq hQUD hdQ hd (by rw [inv_mul_cancel]; exact (Dq M L).one_mem)
  obtain ⟨h1, h2⟩ := C.pr_Dt_coord hQUD θ hθ.inf_Qt hθ.Dt_le hθ.rhoIm_Qt hT hdD
  have hco := mem_pt₀_of_coord (C.pr_mem_perp hQUD θ hθ.inf_Qt ⟨hdQ, hdQt⟩) h1 h2
  rwa [hpr] at hco

theorem rho1_inv_mem_X₂ (hQUD : ∀ x ∈ pCoreOf 2 M, ∃ u ∈ Uq M T L, u⁻¹ * x ∈ Dq M L)
    (hq : 8 ≤ Nat.card F) (θ : MulAut ↥(T1 M T L)) (hθ : C.IsGood θ) (hθ' : C.IsGood θ⁻¹)
    (hD : ∀ (d : G) (hd : d ∈ Uq M T L), d ∈ Dt M L θ⁻¹ → C.N.co ⟨d, hd⟩ ∈ pt₀ F)
    (y : ↥(T1 M T L)) (hyQ : C.rho1 y ∈ Q₂ F) : C.rho1 (θ⁻¹ y) ∈ X₂ F := by
  have : CharP F 2 := charP_of_card_eq_prime_pow C.hF
  refine mem_X₂_of_sub_mem fun v => ?_
  obtain ⟨u₀, rfl⟩ := C.N.co_surj v
  have hu₀T : (u₀ : G) ∈ T1 M T L := C.Uq_le_T1 u₀.2
  have hz : ((θ ⟨u₀, hu₀T⟩ : ↥(T1 M T L)) : G) ∈ Qt M θ :=
    mem_tImage.2 ⟨u₀, hu₀T, C.Uq_le_pCore u₀.2, rfl⟩
  obtain ⟨u, hu, hd⟩ := C.exists_comm_mem hQUD θ hθ.inf_Qt hθ.Dt_le hθ.rhoIm_Ut hθ.rhoIm_Qt
    hθ.Dq_le hq hz (T1_le_sup y.2) hyQ
  obtain ⟨r, hr, ha⟩ := C.exists_Rt θ hθ.rhoIm_Ut hu
  set c := ⁅((θ ⟨u₀, hu₀T⟩ : ↥(T1 M T L)) : G), (y : G)⁆ with hc
  have he : r⁻¹ * c ∈ Dq M L := by
    have e : r⁻¹ * c = (r⁻¹ * u) * (u⁻¹ * c) := by group
    rw [e]
    exact (Dq M L).mul_mem ⟨C.Uq_le_pCore ha.1, ha.2⟩ hd
  have hrT : r ∈ T1 M T L := by
    refine (Subgroup.commutator_le.2 fun a ha b hb => ?_) hr
    have haT := C.Uq_le_T1 ha
    have hbT := tImage_le θ _ hb
    rw [commutatorElement_def]
    exact (T1 M T L).mul_mem ((T1 M T L).mul_mem ((T1 M T L).mul_mem haT hbT)
      ((T1 M T L).inv_mem haT)) ((T1 M T L).inv_mem hbT)
  have hcT : c ∈ T1 M T L := (⁅θ ⟨u₀, hu₀T⟩, y⁆ : ↥(T1 M T L)).2
  have heT : r⁻¹ * c ∈ T1 M T L := (T1 M T L).mul_mem ((T1 M T L).inv_mem hrT) hcT
  set w := θ⁻¹ y with hw
  have hcomm : ⁅(u₀ : G), (w : G)⁆ =
      ((θ⁻¹ ⟨r, hrT⟩ : ↥(T1 M T L)) : G) * ((θ⁻¹ ⟨r⁻¹ * c, heT⟩ : ↥(T1 M T L)) : G) := by
    have e1 : (⟨r, hrT⟩ : ↥(T1 M T L)) * ⟨r⁻¹ * c, heT⟩ = ⁅θ ⟨u₀, hu₀T⟩, y⁆ :=
      Subtype.ext (by show r * (r⁻¹ * c) = _; rw [mul_inv_cancel_left, hc]; rfl)
    rw [← Subgroup.coe_mul, ← map_mul, e1, map_commutatorElement, MulAut.inv_apply_self]
    rfl
  have hr' : ((θ⁻¹ ⟨r, hrT⟩ : ↥(T1 M T L)) : G) ∈ C.Usub (pt₀ F) := by
    refine C.Rt_le_Usub θ⁻¹ hθ'.rhoIm_Ut ?_
    have h := C.tImage_Rt θ⁻¹
    rw [inv_inv] at h
    rw [← h]
    exact mem_tImage.2 ⟨r, hrT, hr, rfl⟩
  obtain ⟨hr'U, hr'co⟩ := (C.mem_Usub).1 hr'
  have hd' : ((θ⁻¹ ⟨r⁻¹ * c, heT⟩ : ↥(T1 M T L)) : G) ∈ Dt M L θ⁻¹ :=
    mem_tImage.2 ⟨_, heT, he, rfl⟩
  have hwM : (w : G) ∈ M := C.sup_le_M (T1_le_sup w.2)
  have hcU : ⁅(u₀ : G), (w : G)⁆ ∈ Uq M T L := by
    have e : ⁅(u₀ : G), (w : G)⁆ = (u₀ : G) * ((w : G) * (u₀ : G)⁻¹ * (w : G)⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact (Uq M T L).mul_mem u₀.2
      ((Subgroup.mem_normalizer_iff.1 (C.hMU hwM) _).1 ((Uq M T L).inv_mem u₀.2))
  have hd'U : ((θ⁻¹ ⟨r⁻¹ * c, heT⟩ : ↥(T1 M T L)) : G) ∈ Uq M T L := by
    have e : ((θ⁻¹ ⟨r⁻¹ * c, heT⟩ : ↥(T1 M T L)) : G) =
        ((θ⁻¹ ⟨r, hrT⟩ : ↥(T1 M T L)) : G)⁻¹ * ⁅(u₀ : G), (w : G)⁆ := by
      rw [hcomm]
      group
    rw [e]
    exact (Uq M T L).mul_mem ((Uq M T L).inv_mem hr'U) hcU
  have hd'co := hD _ hd'U hd'
  have hco : C.N.co ⟨_, hcU⟩ ∈ pt₀ F := by
    have e : (⟨_, hcU⟩ : ↥(Uq M T L)) = ⟨_, hr'U⟩ * ⟨_, hd'U⟩ := Subtype.ext hcomm
    rw [e, C.N.co_mul]
    exact add_mem hr'co hd'co
  have hcU' : ⁅(w : G), (u₀ : G)⁆ ∈ Uq M T L := by
    have e : ⁅(w : G), (u₀ : G)⁆ = ⁅(u₀ : G), (w : G)⁆⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact (Uq M T L).inv_mem hcU
  have h3 := C.co_comm hwM u₀.2 hcU'
  rw [show C.act hwM = C.act (C.sup_le_M (T1_le_sup w.2)) from rfl,
    C.rho_spec ⟨(w : G), T1_le_sup w.2⟩] at h3
  have e : (⟨_, hcU'⟩ : ↥(Uq M T L)) = (⟨_, hcU⟩ : ↥(Uq M T L))⁻¹ :=
    Subtype.ext (by simp only [commutatorElement_def, Subgroup.coe_inv]; group)
  rw [e, C.N.co_inv] at h3
  have h4 : mat (C.rho1 w) *ᵥ C.N.co u₀ - C.N.co u₀ = -C.N.co ⟨_, hcU⟩ := by
    rw [C.rho1_apply, h3]
  rw [h4]
  exact neg_mem hco

theorem false_of_rho1_inv_mem_X₂ (θ : MulAut ↥(T1 M T L))
    (key : ∀ y : ↥(T1 M T L), C.rho1 y ∈ Q₂ F → C.rho1 (θ⁻¹ y) ∈ X₂ F) {t : ↥(T1 M T L)}
    (ht : C.rho1 t ∈ Q₂ F) (htX : C.rho1 t ∉ X₂ F) : False := by
  have hXH : (X₂ F).comap C.rho1 ≤ (Q₂ F).comap C.rho1 := Subgroup.comap_mono X₂_le_Q₂
  have hmap : ((Q₂ F).comap C.rho1).map (θ⁻¹ : MulAut ↥(T1 M T L)).toMonoidHom ≤
      (X₂ F).comap C.rho1 := by
    rintro _ ⟨y, hy, rfl⟩
    exact key y hy
  have hcard : Nat.card ((Q₂ F).comap C.rho1) ≤ Nat.card ((X₂ F).comap C.rho1) := by
    rw [← Subgroup.card_map_of_injective (f := (θ⁻¹ : MulAut ↥(T1 M T L)).toMonoidHom)
      (θ⁻¹).injective]
    exact Subgroup.card_le_of_le hmap
  have heq := Subgroup.eq_of_le_of_card_ge hXH hcard
  have htH : t ∈ (Q₂ F).comap C.rho1 := ht
  rw [← heq] at htH
  exact htX htH

theorem false_of_isGood (hQUD : ∀ x ∈ pCoreOf 2 M, ∃ u ∈ Uq M T L, u⁻¹ * x ∈ Dq M L)
    (hT : Q₂ F ≤ C.T0bar) (hq : 8 ≤ Nat.card F) (θ : MulAut ↥(T1 M T L)) (hθ : C.IsGood θ)
    (hθ' : C.IsGood θ⁻¹) : False := by
  have : CharP F 2 := charP_of_card_eq_prime_pow C.hF
  have key := C.rho1_inv_mem_X₂ hQUD hq θ hθ hθ'
    (fun d hd hdD => C.co_mem_pt₀_of_mem_Dt hQUD hT θ⁻¹ hθ' hd hdD)
  obtain ⟨t, ht⟩ := hT (qe_mem_Q₂ (1 : F) 0 0)
  refine C.false_of_rho1_inv_mem_X₂ θ key (t := t) (by rw [ht]; exact qe_mem_Q₂ _ _ _) ?_
  rw [ht]
  exact qe_one_not_mem_X₂

end Cfg

end CFSG.Quasithin.MS93.S37
