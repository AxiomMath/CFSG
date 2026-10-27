module

public import CFSG.Quasithin.MS93.S37Good

public section

namespace CFSG.Quasithin.MS93.S37

open CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.Quasithin.MS93 CFSG.Quasithin.MS93.MSP
open CFSG.QuasithinUnique CFSG.Quasithin.MS93.S36 CFSG.Quasithin.Vol2
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFour
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix

section Sp

variable {F : Type} [Field F]

theorem sylS_mulVec_perp {g : Sp4 F} (hg : g ∈ sylS F) {w : V4 F} (hw : w (.inr 0) = 0) :
    mat g *ᵥ w = w + (mat g (.inl 0) (.inl 1) * w (.inl 1) +
      mat g (.inl 0) (.inr 1) * w (.inr 1)) • e₁ F + (mat g (.inl 1) (.inr 1) * w (.inr 1)) •
        e₂ F := by
  obtain ⟨a, C, hC, hgC⟩ := exists_of_mem_sylS hg
  have hent : ∀ i j, mat g i j = (mat g *ᵥ Pi.single j 1) i := fun i j => by
    rw [mat_apply_eq]
  obtain ⟨e0, e1, e2, e3⟩ := mulVec_blockMat_unitri a C w
  obtain ⟨a0, -, -, -⟩ := mulVec_blockMat_unitri a C (Pi.single (.inl 1) 1)
  obtain ⟨b0, b1, -, -⟩ := mulVec_blockMat_unitri a C (Pi.single (.inr 1) 1)
  rw [hent, hent, hent, hgC, a0, b0, b1]
  refine ext4 ?_ ?_ ?_ ?_
  · rw [e0, hw]
    simp [e₁, e₂, add_assoc]
  · rw [e1, hw]
    simp [e₁, e₂]
  · rw [e2]
    simp [e₁, e₂]
  · rw [e3, hw]
    simp [e₁, e₂]

theorem sylS_mulVec_f₁ {g : Sp4 F} (hg : g ∈ sylS F) :
    (mat g *ᵥ f₁ F) (.inr 1) = -mat g (.inl 0) (.inl 1) := by
  obtain ⟨a, C, hC, hgC⟩ := exists_of_mem_sylS hg
  obtain ⟨-, -, -, e3⟩ := mulVec_blockMat_unitri a C (f₁ F)
  obtain ⟨a0, -, -, -⟩ := mulVec_blockMat_unitri a C (Pi.single (.inl 1) 1)
  rw [mat_apply_eq, hgC, a0, e3]
  simp [f₁]

theorem sylS_mulVec_e₂ {g : Sp4 F} (hg : g ∈ sylS F) :
    mat g *ᵥ e₂ F = e₂ F + mat g (.inl 0) (.inl 1) • e₁ F := by
  rw [sylS_mulVec_perp hg (by simp [e₂])]
  simp [e₂, e₁]

theorem sylS_entry_mul {g h : Sp4 F} (hg : g ∈ sylS F) (hh : h ∈ sylS F) :
    mat (g * h) (.inl 0) (.inl 1) = mat g (.inl 0) (.inl 1) + mat h (.inl 0) (.inl 1) := by
  have he₁ : mat g *ᵥ e₁ F = e₁ F := by
    rw [sylS_mulVec_perp hg (by simp [e₁])]
    simp [e₁]
  rw [mat_apply_eq, mat_mul_mulVec, sylS_mulVec_e₂ hh, Matrix.mulVec_add, Matrix.mulVec_smul,
    sylS_mulVec_e₂ hg, he₁]
  simp [e₁, e₂]

theorem mem_X₂_of_sylS {g : Sp4 F} (hg : g ∈ sylS F) (h1 : mat g (.inl 0) (.inl 1) = 0)
    (h2 : mat g (.inl 0) (.inr 1) = 0) (h3 : mat g (.inl 1) (.inr 1) = 0) : g ∈ X₂ F := by
  intro w hw
  rw [sylS_mulVec_perp hg (mem_perp_pt₀.1 hw), h1, h2, h3]
  simp

theorem sylS_mulVec_e₁ {g : Sp4 F} (hg : g ∈ sylS F) : mat g *ᵥ e₁ F = e₁ F := by
  rw [sylS_mulVec_perp hg (by simp [e₁])]
  simp [e₁]

theorem sylS_fix_pt₀ {g : Sp4 F} (hg : g ∈ sylS F) {p : V4 F} (hp : p ∈ pt₀ F) :
    mat g *ᵥ p = p := by
  rw [pt₀_eq_span] at hp
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hp
  rw [Matrix.mulVec_smul, sylS_mulVec_e₁ hg]

theorem sylS_entry_rel {g : Sp4 F} (hg : g ∈ sylS F) :
    mat g (.inl 0) (.inr 1) =
      mat g (.inl 1) (.inr 0) + mat g (.inl 0) (.inl 1) * mat g (.inl 1) (.inr 1) := by
  obtain ⟨a, C, hC, hgC⟩ := exists_of_mem_sylS hg
  have hent : ∀ i j, mat g i j = (mat g *ᵥ Pi.single j 1) i := fun i j => by
    rw [mat_apply_eq]
  obtain ⟨a0, -, -, -⟩ := mulVec_blockMat_unitri a C (Pi.single (.inl 1) 1)
  obtain ⟨b0, b1, -, -⟩ := mulVec_blockMat_unitri a C (Pi.single (.inr 1) 1)
  obtain ⟨-, c1, -, -⟩ := mulVec_blockMat_unitri a C (Pi.single (.inr 0) 1)
  have h10 : C 1 0 = C 0 1 := by
    have := congrFun₂ hC 0 1
    rwa [Matrix.transpose_apply] at this
  rw [hent, hent, hent, hent, hgC, a0, b0, b1, c1]
  simp [h10]

theorem qe_mulVec_f₁ [CharP F 2] (x y s : F) :
    (mat (qe x y s) *ᵥ f₁ F) (.inl 1) = x ∧ (mat (qe x y s) *ᵥ f₁ F) (.inr 1) = y := by
  rw [qe_mulVec]
  constructor <;> simp [e₁, e₂, f₁, f₂]

theorem qe_inj [CharP F 2] {x y s x' y' s' : F} (h : qe x y s = qe x' y' s') :
    x = x' ∧ y = y' := by
  obtain ⟨h1, h2⟩ := qe_mulVec_f₁ x y s
  obtain ⟨h1', h2'⟩ := qe_mulVec_f₁ x' y' s'
  rw [h] at h1 h2
  exact ⟨h1.symm.trans h1', h2.symm.trans h2'⟩

end Sp

variable {G : Type} [Group G]

theorem T_inf_L_le_T1 {M T L : Subgroup G} : T ⊓ L ≤ T1 M T L :=
  fun _ ht => ⟨ht.1, Subgroup.mem_sup_left ht.2⟩

variable [Finite G]

namespace Cfg

variable {M T L : Subgroup G} {F : Type} [Field F] [Fintype F] (C : Cfg M T L F)
include C

theorem exists_rho_eq_mul (θ : MulAut ↥(T1 M T L)) {g : Sp4 F} (hg : g ∈ C.T0bar) :
    ∃ (t : G) (ht : t ∈ T ⊓ L) (x : G) (hx : x ∈ pCoreOf 2 M),
      g = C.rho1 (θ ⟨t, T_inf_L_le_T1 ht⟩) * C.rho1 (θ ⟨x, C.pCore_le_T1 hx⟩) := by
  obtain ⟨s, rfl⟩ := hg
  obtain ⟨l, hl, q, hq, e⟩ := C.exists_mul_of_mem_T1 (θ⁻¹ s).2
  refine ⟨l, hl, q, hq, ?_⟩
  rw [← map_mul, ← map_mul]
  congr 1
  have : (⟨l, T_inf_L_le_T1 hl⟩ * ⟨q, C.pCore_le_T1 hq⟩ : ↥(T1 M T L)) = θ⁻¹ s :=
    Subtype.ext e
  rw [this, MulAut.apply_inv_self]

theorem fix_comm_Qt (hT : C.T0bar ≤ sylS F) (θ : MulAut ↥(T1 M T L))
    (hE : C.rhoIm (Ut M T L θ) = X₂ F) (hE' : C.rhoIm (Ut M T L θ⁻¹) = X₂ F) {t : G}
    (ht : t ∈ T ⊓ L) {z : G} (hz : z ∈ Qt M θ) (v : V4 F) :
    mat (C.rho1 (θ ⟨t, T_inf_L_le_T1 ht⟩)) *ᵥ
        (mat (C.rho ⟨z, Qt_le_sup θ hz⟩) *ᵥ v - v) =
      mat (C.rho ⟨z, Qt_le_sup θ hz⟩) *ᵥ v - v := by
  set t' := θ ⟨t, T_inf_L_le_T1 ht⟩ with ht'
  have hkS : C.rho1 t' ∈ sylS F := hT ⟨t', rfl⟩
  obtain ⟨u, rfl⟩ := C.N.co_surj v
  obtain ⟨r, hr, hd⟩ := C.comm_Qt_mem θ hE' u.2 hz
  have hrU : r ∈ C.Usub (pt₀ F) := C.Rt_le_Usub θ hE hr
  obtain ⟨hrU', hrco⟩ := (C.mem_Usub).1 hrU
  have hzM : z ∈ M := C.sup_le_M (Qt_le_sup θ hz)
  have hcU : ⁅(u : G), z⁆ ∈ Uq M T L := by
    have e : ⁅(u : G), z⁆ = (u : G) * (z * (u : G)⁻¹ * z⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact (Uq M T L).mul_mem u.2
      ((Subgroup.mem_normalizer_iff.1 (C.hMU hzM) _).1 ((Uq M T L).inv_mem u.2))
  have hwU : r⁻¹ * ⁅(u : G), z⁆ ∈ Uq M T L := (Uq M T L).mul_mem ((Uq M T L).inv_mem hrU') hcU
  have hcomm : (t' : G) * (r⁻¹ * ⁅(u : G), z⁆) * (t' : G)⁻¹ = r⁻¹ * ⁅(u : G), z⁆ := by
    obtain ⟨d, hdT, hdD, hde⟩ := mem_tImage.1 hd
    have h1 : t * d = d * t := Subgroup.mem_centralizer_iff.1 hdD.2 t ht.2
    have h2 : (⟨t, T_inf_L_le_T1 ht⟩ : ↥(T1 M T L)) * ⟨d, hdT⟩ =
        ⟨d, hdT⟩ * ⟨t, T_inf_L_le_T1 ht⟩ := Subtype.ext h1
    have h3 := congrArg (fun x => ((θ x : ↥(T1 M T L)) : G)) h2
    simp only [map_mul, Subgroup.coe_mul] at h3
    rw [← ht'] at h3
    rw [← hde, h3]
    group
  have hfix : mat (C.rho1 t') *ᵥ C.N.co ⟨_, hwU⟩ = C.N.co ⟨_, hwU⟩ := by
    have h := C.co_conj ⟨(t' : G), T1_le_sup t'.2⟩ (u := ⟨_, hwU⟩) (v := ⟨_, hwU⟩) hcomm.symm
    rw [← C.rho1_apply] at h
    exact h.symm
  have hcU' : ⁅z, (u : G)⁆ ∈ Uq M T L := by
    have e : ⁅z, (u : G)⁆ = ⁅(u : G), z⁆⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact (Uq M T L).inv_mem hcU
  have h1 := C.co_comm hzM u.2 hcU'
  rw [show C.act hzM = C.act (C.sup_le_M (Qt_le_sup θ hz)) from rfl,
    C.rho_spec ⟨z, Qt_le_sup θ hz⟩] at h1
  have e2 : (⟨_, hwU⟩ : ↥(Uq M T L)) = (⟨r, hrU'⟩ : ↥(Uq M T L))⁻¹ * (⟨_, hcU'⟩)⁻¹ :=
    Subtype.ext (by simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]; group)
  rw [e2, C.N.co_mul, C.N.co_inv, C.N.co_inv, h1] at hfix
  have hp := sylS_fix_pt₀ hkS hrco
  have e3 : mat (C.rho ⟨z, Qt_le_sup θ hz⟩) *ᵥ C.N.co u - C.N.co u =
      -(-C.N.co ⟨r, hrU'⟩ + -(mat (C.rho ⟨z, Qt_le_sup θ hz⟩) *ᵥ C.N.co ⟨(u : G), u.2⟩ -
        C.N.co ⟨(u : G), u.2⟩)) - C.N.co ⟨r, hrU'⟩ := by
    simp only [neg_add_rev, neg_neg, neg_sub]
    abel
  rw [e3, Matrix.mulVec_sub, Matrix.mulVec_neg, hfix, hp]

theorem rhoIm_Qt_or_Q₂ (hT : C.T0bar = Q₂ F) (θ : MulAut ↥(T1 M T L))
    (hE : C.rhoIm (Ut M T L θ) = X₂ F) (hE' : C.rhoIm (Ut M T L θ⁻¹) = X₂ F) :
    (∀ (z : G) (hz : z ∈ Qt M θ), C.rho ⟨z, Qt_le_sup θ hz⟩ ∈ X₂ F) ∨
      ∀ (t : G) (ht : t ∈ T ⊓ L), C.rho1 (θ ⟨t, T_inf_L_le_T1 ht⟩) ∈ X₂ F := by
  have : CharP F 2 := charP_of_card_eq_prime_pow C.hF
  have hTS : C.T0bar ≤ sylS F := hT ▸ Q₂_le_sylS
  have hQt : ∀ (z : G) (hz : z ∈ Qt M θ), C.rho ⟨z, Qt_le_sup θ hz⟩ ∈ Q₂ F := fun z hz => by
    rw [← hT]
    exact ⟨⟨z, tImage_le θ _ hz⟩, rfl⟩
  have hK : ∀ (t : G) (ht : t ∈ T ⊓ L), C.rho1 (θ ⟨t, T_inf_L_le_T1 ht⟩) ∈ Q₂ F :=
    fun t ht => hT ▸ ⟨_, rfl⟩
  have key : ∀ (t : G) (ht : t ∈ T ⊓ L) (z : G) (hz : z ∈ Qt M θ) (x y s x₀ y₀ s₀ : F),
      C.rho1 (θ ⟨t, T_inf_L_le_T1 ht⟩) = qe x y s → C.rho ⟨z, Qt_le_sup θ hz⟩ = qe x₀ y₀ s₀ →
        x * y₀ + y * x₀ = 0 := by
    intro t ht z hz x y s x₀ y₀ s₀ hk hn
    have h := C.fix_comm_Qt hTS θ hE hE' ht hz (f₁ F)
    rw [hk, hn] at h
    have h0 := congrFun h (.inl 0)
    rw [qe_mulVec, qe_mulVec] at h0
    simp [e₁, e₂, f₁, f₂] at h0
    linear_combination h0
  by_contra hcon
  simp only [not_or, not_forall] at hcon
  obtain ⟨⟨z₀, hz₀, hz₀X⟩, ⟨t₀, ht₀, ht₀X⟩⟩ := hcon
  obtain ⟨a₀, b₀, c₀, hn₀⟩ := exists_eq_qe_of_mem_Q₂ (hQt z₀ hz₀)
  obtain ⟨a, b, c, hk₀⟩ := exists_eq_qe_of_mem_Q₂ (hK t₀ ht₀)
  have hab : a ≠ 0 ∨ b ≠ 0 := by
    by_contra h
    push Not at h
    rw [hk₀, h.1, h.2, qe_zero_zero] at ht₀X
    exact ht₀X (transv_mem_X₂ _)
  have hab₀ : a₀ ≠ 0 ∨ b₀ ≠ 0 := by
    by_contra h
    push Not at h
    rw [hn₀, h.1, h.2, qe_zero_zero] at hz₀X
    exact hz₀X (transv_mem_X₂ _)
  obtain ⟨a', b', hω⟩ : ∃ a' b' : F, a * b' + b * a' = 1 := by
    rcases hab with ha | hb
    · exact ⟨0, a⁻¹, by rw [mul_inv_cancel₀ ha, mul_zero, add_zero]⟩
    · exact ⟨b⁻¹, 0, by rw [mul_inv_cancel₀ hb, mul_zero, zero_add]⟩
  obtain ⟨t, ht, x, hx, hg⟩ := C.exists_rho_eq_mul θ (hT ▸ qe_mem_Q₂ a' b' 0 :
    qe a' b' 0 ∈ C.T0bar)
  have hxQt : ((θ ⟨x, C.pCore_le_T1 hx⟩ : ↥(T1 M T L)) : G) ∈ Qt M θ :=
    mem_tImage.2 ⟨x, C.pCore_le_T1 hx, hx, rfl⟩
  obtain ⟨xk, yk, sk, hk⟩ := exists_eq_qe_of_mem_Q₂ (hK t ht)
  obtain ⟨xn, yn, sn, hn⟩ := exists_eq_qe_of_mem_Q₂ (hQt _ hxQt)
  have hn' : C.rho1 (θ ⟨x, C.pCore_le_T1 hx⟩) = qe xn yn sn := hn
  rw [hk, hn', qe_mul] at hg
  obtain ⟨hga, hgb⟩ := qe_inj hg
  have e1 := key t ht z₀ hz₀ xk yk sk a₀ b₀ c₀ hk hn₀
  have e2 := key t₀ ht₀ _ hxQt a b c xn yn sn hk₀ hn
  have e3 := key t₀ ht₀ z₀ hz₀ a b c a₀ b₀ c₀ hk₀ hn₀
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have e4 : a * yk + b * xk = 0 := by
    have f1 : b₀ * (a * yk + b * xk) = 0 := by
      linear_combination yk * e3 + b * e1 - (a₀ * b * yk) * h2
    have f2 : a₀ * (a * yk + b * xk) = 0 := by
      linear_combination xk * e3 + a * e1 - (a * b₀ * xk) * h2
    rcases hab₀ with h | h
    · exact (mul_eq_zero.1 f2).resolve_left h
    · exact (mul_eq_zero.1 f1).resolve_left h
  rw [hga, hgb] at hω
  apply one_ne_zero (α := F)
  rw [← hω]
  linear_combination e4 + e2

theorem rhoIm_Qt_or_S (hT : C.T0bar = sylS F) (θ : MulAut ↥(T1 M T L))
    (hE : C.rhoIm (Ut M T L θ) = X₂ F) (hE' : C.rhoIm (Ut M T L θ⁻¹) = X₂ F) :
    (∀ (z : G) (hz : z ∈ Qt M θ), C.rho ⟨z, Qt_le_sup θ hz⟩ ∈ X₂ F) ∨
      ∀ (t : G) (ht : t ∈ T ⊓ L), C.rho1 (θ ⟨t, T_inf_L_le_T1 ht⟩) ∈ X₂ F := by
  have hTS : C.T0bar ≤ sylS F := hT.le
  have hQt : ∀ (z : G) (hz : z ∈ Qt M θ), C.rho ⟨z, Qt_le_sup θ hz⟩ ∈ sylS F := fun z hz => by
    rw [← hT]
    exact ⟨⟨z, tImage_le θ _ hz⟩, rfl⟩
  have hK : ∀ (t : G) (ht : t ∈ T ⊓ L), C.rho1 (θ ⟨t, T_inf_L_le_T1 ht⟩) ∈ sylS F :=
    fun t ht => hT ▸ ⟨_, rfl⟩
  have key1 : ∀ (t : G) (ht : t ∈ T ⊓ L) (z : G) (hz : z ∈ Qt M θ),
      mat (C.rho1 (θ ⟨t, T_inf_L_le_T1 ht⟩)) (.inl 0) (.inl 1) *
        mat (C.rho ⟨z, Qt_le_sup θ hz⟩) (.inl 1) (.inr 1) = 0 := by
    intro t ht z hz
    have h := C.fix_comm_Qt hTS θ hE hE' ht hz (f₂ F)
    have hw : (mat (C.rho ⟨z, Qt_le_sup θ hz⟩) *ᵥ f₂ F - f₂ F) (.inr 0) = 0 := by
      rw [Pi.sub_apply, sylS_mulVec_perp (hQt z hz) (by simp [f₂])]
      simp [f₂, e₁, e₂]
    rw [sylS_mulVec_perp (hK t ht) hw] at h
    have h0 := congrFun h (.inl 0)
    rw [sylS_mulVec_perp (hQt z hz) (by simp [f₂])] at h0
    simp [f₂, e₁, e₂] at h0
    exact mul_eq_zero.2 h0
  have key2 : ∀ (t : G) (ht : t ∈ T ⊓ L) (z : G) (hz : z ∈ Qt M θ),
      mat (C.rho1 (θ ⟨t, T_inf_L_le_T1 ht⟩)) (.inl 1) (.inr 1) *
          mat (C.rho ⟨z, Qt_le_sup θ hz⟩) (.inl 0) (.inl 1) = 0 ∧
        mat (C.rho1 (θ ⟨t, T_inf_L_le_T1 ht⟩)) (.inl 0) (.inl 1) *
            mat (C.rho ⟨z, Qt_le_sup θ hz⟩) (.inl 1) (.inr 0) =
          mat (C.rho1 (θ ⟨t, T_inf_L_le_T1 ht⟩)) (.inl 0) (.inr 1) *
            mat (C.rho ⟨z, Qt_le_sup θ hz⟩) (.inl 0) (.inl 1) := by
    intro t ht z hz
    have h := C.fix_comm_Qt hTS θ hE hE' ht hz (f₁ F)
    set w := mat (C.rho ⟨z, Qt_le_sup θ hz⟩) *ᵥ f₁ F - f₁ F with hwdef
    have hw3 : w (.inr 0) = 0 := by
      obtain ⟨a, C', hC', hgC⟩ := exists_of_mem_sylS (hQt z hz)
      obtain ⟨-, -, e2, -⟩ := mulVec_blockMat_unitri a C' (f₁ F)
      rw [hwdef, Pi.sub_apply, hgC, e2]
      simp [f₁]
    have hw2 : w (.inl 1) = mat (C.rho ⟨z, Qt_le_sup θ hz⟩) (.inl 1) (.inr 0) := by
      rw [hwdef, Pi.sub_apply, ← mat_apply_eq]
      simp [f₁]
    have hw4 : w (.inr 1) = -mat (C.rho ⟨z, Qt_le_sup θ hz⟩) (.inl 0) (.inl 1) := by
      rw [hwdef, Pi.sub_apply, sylS_mulVec_f₁ (hQt z hz)]
      simp [f₁]
    rw [sylS_mulVec_perp (hK t ht) hw3] at h
    have h0 := congrFun h (.inl 0)
    have h1 := congrFun h (.inl 1)
    simp [e₁, e₂, hw2, hw4] at h0 h1
    refine ⟨?_, ?_⟩
    · rcases h1 with h1 | h1
      · rw [h1, zero_mul]
      · rw [h1, mul_zero]
    · linear_combination h0
  by_contra hcon
  simp only [not_or, not_forall] at hcon
  obtain ⟨⟨z₀, hz₀, hz₀X⟩, ⟨t₀, ht₀, ht₀X⟩⟩ := hcon
  by_cases hA : ∃ (z : G) (hz : z ∈ Qt M θ), mat (C.rho ⟨z, Qt_le_sup θ hz⟩) (.inl 0) (.inl 1) ≠ 0
  · obtain ⟨z, hz, hz12⟩ := hA
    have hk24 : ∀ (t : G) (ht : t ∈ T ⊓ L),
        mat (C.rho1 (θ ⟨t, T_inf_L_le_T1 ht⟩)) (.inl 1) (.inr 1) = 0 := fun t ht =>
      (mul_eq_zero.1 (key2 t ht z hz).1).resolve_right hz12
    obtain ⟨t, ht, x, hx, hg⟩ := C.exists_rho_eq_mul θ
      (hT ▸ tau_mem_unipotent (sym2_transpose (0 : F) 0 1) :
        tau (sym2_transpose (0 : F) 0 1) ∈ C.T0bar)
    have hxQt : ((θ ⟨x, C.pCore_le_T1 hx⟩ : ↥(T1 M T L)) : G) ∈ Qt M θ :=
      mem_tImage.2 ⟨x, C.pCore_le_T1 hx, hx, rfl⟩
    have hxS : C.rho1 (θ ⟨x, C.pCore_le_T1 hx⟩) ∈ sylS F := hT ▸ ⟨_, rfl⟩
    have hn24 : mat (C.rho1 (θ ⟨x, C.pCore_le_T1 hx⟩)) (.inl 1) (.inr 1) = 1 := by
      have h1 := congrArg (fun g => mat g (.inl 1) (.inr 1)) hg
      have h2 : mat (tau (sym2_transpose (0 : F) 0 1)) (.inl 1) (.inr 1) = 1 := by
        rw [mat_apply_eq, (mulVec_tau_sym2 0 0 1 _).2.1]
        simp
      have h3 := congrArg Multiplicative.toAdd (map_mul entryHom ⟨_, hK t ht⟩ ⟨_, hxS⟩)
      simp only [entryHom_apply, toAdd_mul, toAdd_ofAdd, Subgroup.coe_mul] at h3
      rw [h2, h3, hk24 t ht, zero_add] at h1
      exact h1.symm
    have hk12 : ∀ (t : G) (ht : t ∈ T ⊓ L),
        mat (C.rho1 (θ ⟨t, T_inf_L_le_T1 ht⟩)) (.inl 0) (.inl 1) = 0 := fun t ht => by
      have := key1 t ht _ hxQt
      have e : mat (C.rho ⟨_, Qt_le_sup θ hxQt⟩) (.inl 1) (.inr 1) = 1 := hn24
      rwa [e, mul_one] at this
    have hk14 : mat (C.rho1 (θ ⟨t₀, T_inf_L_le_T1 ht₀⟩)) (.inl 0) (.inr 1) = 0 := by
      have := (key2 t₀ ht₀ z hz).2
      rw [hk12 t₀ ht₀, zero_mul] at this
      exact (mul_eq_zero.1 this.symm).resolve_right hz12
    exact ht₀X (mem_X₂_of_sylS (hK t₀ ht₀) (hk12 t₀ ht₀) hk14 (hk24 t₀ ht₀))
  · push Not at hA
    obtain ⟨t, ht, x, hx, hg⟩ := C.exists_rho_eq_mul θ
      (hT ▸ lam_mem_sylS (1 : F) : lam (1 : F) ∈ C.T0bar)
    have hxQt : ((θ ⟨x, C.pCore_le_T1 hx⟩ : ↥(T1 M T L)) : G) ∈ Qt M θ :=
      mem_tImage.2 ⟨x, C.pCore_le_T1 hx, hx, rfl⟩
    have hxS : C.rho1 (θ ⟨x, C.pCore_le_T1 hx⟩) ∈ sylS F := hT ▸ ⟨_, rfl⟩
    have hk12 : mat (C.rho1 (θ ⟨t, T_inf_L_le_T1 ht⟩)) (.inl 0) (.inl 1) = 1 := by
      have h1 := congrArg (fun g => mat g (.inl 0) (.inl 1)) hg
      have h2 : mat (lam (1 : F)) (.inl 0) (.inl 1) = 1 := by
        rw [mat_apply_eq, (mulVec_lam 1 _).1]
        simp
      have hx0 : mat (C.rho1 (θ ⟨x, C.pCore_le_T1 hx⟩)) (.inl 0) (.inl 1) = 0 := hA _ hxQt
      rw [h2, sylS_entry_mul (hK t ht) hxS, hx0, add_zero] at h1
      exact h1.symm
    have hn24 : mat (C.rho ⟨z₀, Qt_le_sup θ hz₀⟩) (.inl 1) (.inr 1) = 0 := by
      have := key1 t ht z₀ hz₀
      rwa [hk12, one_mul] at this
    have hn23 : mat (C.rho ⟨z₀, Qt_le_sup θ hz₀⟩) (.inl 1) (.inr 0) = 0 := by
      have := (key2 t ht z₀ hz₀).2
      rwa [hk12, one_mul, hA z₀ hz₀, mul_zero] at this
    have hn14 : mat (C.rho ⟨z₀, Qt_le_sup θ hz₀⟩) (.inl 0) (.inr 1) = 0 := by
      rw [sylS_entry_rel (hQt z₀ hz₀), hn23, hA z₀ hz₀, zero_mul, add_zero]
    exact hz₀X (mem_X₂_of_sylS (hQt z₀ hz₀) (hA z₀ hz₀) hn14 hn24)

theorem rho_Dt_eq_one (θ : MulAut ↥(T1 M T L)) (hE : C.rhoIm (Ut M T L θ) = X₂ F)
    (hE' : C.rhoIm (Ut M T L θ⁻¹) = X₂ F) {d : G} (hd : d ∈ Dt M L θ)
    (hdK : d ∈ L ⊔ pCoreOf 2 M) (hX : C.rho ⟨d, hdK⟩ ∈ X₂ F) : C.rho ⟨d, hdK⟩ = 1 := by
  have hm : C.rho ⟨d, hdK⟩ ∈ C.rhoIm (Ut M T L θ) := by
    rw [hE]
    exact hX
  obtain ⟨u', hu'K, hu', hρ⟩ := (C.mem_rhoIm).1 hm
  have hdQt : d ∈ Qt M θ := tImage_mono' θ (inf_le_left : Dq M L ≤ pCoreOf 2 M) hd
  have hu'Qt : u' ∈ Qt M θ := tImage_mono' θ (C.Uq_le_pCore) hu'
  have hx₀K : u'⁻¹ * d ∈ L ⊔ pCoreOf 2 M := (L ⊔ pCoreOf 2 M).mul_mem
    ((L ⊔ pCoreOf 2 M).inv_mem hu'K) hdK
  have hx₀Q : u'⁻¹ * d ∈ pCoreOf 2 M := by
    refine (C.rho_eq_one_iff ⟨_, hx₀K⟩).1 ?_
    have e : (⟨u'⁻¹ * d, hx₀K⟩ : ↥(L ⊔ pCoreOf 2 M)) = (⟨u', hu'K⟩)⁻¹ * ⟨d, hdK⟩ := rfl
    rw [e, map_mul, map_inv, hρ, inv_mul_cancel]
  have hx₀Qt : u'⁻¹ * d ∈ Qt M θ := (Qt M θ).mul_mem ((Qt M θ).inv_mem hu'Qt) hdQt
  obtain ⟨u, huT, hu, rfl⟩ := mem_tImage.1 hu'
  obtain ⟨d₀, hd₀T, hd₀, rfl⟩ := mem_tImage.1 hd
  set x₀ := ((θ ⟨u, huT⟩ : ↥(T1 M T L)) : G)⁻¹ * ((θ ⟨d₀, hd₀T⟩ : ↥(T1 M T L)) : G)
  have hx₀T : x₀ ∈ T1 M T L := C.pCore_le_T1 hx₀Q
  have hy : ((θ⁻¹ ⟨x₀, hx₀T⟩ : ↥(T1 M T L)) : G) = u⁻¹ * d₀ := by
    have e : (⟨x₀, hx₀T⟩ : ↥(T1 M T L)) = θ (⟨u, huT⟩⁻¹ * ⟨d₀, hd₀T⟩) := by
      rw [map_mul, map_inv]
      rfl
    rw [e, MulAut.inv_apply_self]
    rfl
  have hyQ : u⁻¹ * d₀ ∈ pCoreOf 2 M ⊓ Qt M θ⁻¹ := by
    refine ⟨(pCoreOf 2 M).mul_mem ((pCoreOf 2 M).inv_mem (C.Uq_le_pCore hu)) hd₀.1, ?_⟩
    rw [← hy]
    exact mem_tImage.2 ⟨x₀, hx₀T, hx₀Q, rfl⟩
  obtain ⟨w, hw, hwd⟩ := C.inf_Qt_of_rhoIm θ⁻¹ hE' _ hyQ
  have huP : u ∈ (C.Usub (perp (pt₀ F)) ⊔ Dq M L) ⊓ Uq M T L := by
    refine ⟨?_, hu⟩
    have e : u = (w * (w⁻¹ * (u⁻¹ * d₀)) * d₀⁻¹)⁻¹ := by group
    rw [e]
    exact (C.Usub (perp (pt₀ F)) ⊔ Dq M L).inv_mem ((C.Usub (perp (pt₀ F)) ⊔ Dq M L).mul_mem
      (Subgroup.mul_mem_sup hw hwd) (Subgroup.mem_sup_right ((Dq M L).inv_mem hd₀)))
  rw [C.Usub_sup_inf_Uq] at huP
  have huQt := C.Usub_perp_le_Qt θ⁻¹ hE' huP
  obtain ⟨y, hyT, hyQ', hye⟩ := mem_tImage.1 huQt
  have hθu : ((θ ⟨u, huT⟩ : ↥(T1 M T L)) : G) ∈ pCoreOf 2 M := by
    have e : (⟨u, huT⟩ : ↥(T1 M T L)) = θ⁻¹ ⟨y, hyT⟩ := Subtype.ext hye.symm
    rw [e, MulAut.apply_inv_self]
    exact hyQ'
  rw [← hρ]
  exact (C.rho_eq_one_iff _).2 hθu

end Cfg

end CFSG.Quasithin.MS93.S37
