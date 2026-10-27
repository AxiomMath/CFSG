module

public import CFSG.Quasithin.MS93.S37GoodLine
public import CFSG.Quasithin.MS93.S37Bad3

public section

namespace CFSG.Quasithin.MS93.S37

open CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.Quasithin.MS93 CFSG.Quasithin.MS93.MSP
open CFSG.QuasithinUnique CFSG.Quasithin.MS93.S36 CFSG.Quasithin.Vol2
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix

section Sp

variable {F : Type} [Field F]

theorem entry_transv_of_mem_ln₀ {x : V4 F} (hx : x ∈ ln₀ F) (c : F) (i j : Fin 2) :
    mat (transv x c) (.inl i) (.inr j) = c * x (.inl i) * x (.inl j) := by
  obtain ⟨h0, h1⟩ := mem_ln₀.1 hx
  rw [mat_apply_eq, transv_mulVec, form_apply]
  fin_cases i <;> fin_cases j <;> simp [h0, h1] <;> ring

theorem exists_eq_transv_mul {μ : F} (hμ : μ ≠ 1) {g : Sp4 F} (hg : g ∈ Q₁ F) :
    ∃ a b c : F, g = transv (e₂ F) a * transv (e₁ F + e₂ F) b * transv (e₁ F + μ • e₂ F) c := by
  have hμ' : μ - 1 ≠ 0 := sub_ne_zero.2 hμ
  have hx₂ : e₁ F + e₂ F ∈ ln₀ F := mem_ln₀.2 ⟨by simp [e₁, e₂], by simp [e₁, e₂]⟩
  have hx₃ : e₁ F + μ • e₂ F ∈ ln₀ F := mem_ln₀.2 ⟨by simp [e₁, e₂], by simp [e₁, e₂]⟩
  have hx₁ : e₂ F ∈ ln₀ F := mem_ln₀.2 ⟨by simp [e₂], by simp [e₂]⟩
  obtain ⟨c, hc⟩ : ∃ c : F, (μ - 1) * c = mat g (.inl 0) (.inr 1) - mat g (.inl 0) (.inr 0) :=
    ⟨(mat g (.inl 0) (.inr 1) - mat g (.inl 0) (.inr 0)) / (μ - 1), by field_simp⟩
  refine ⟨mat g (.inl 1) (.inr 1) - (mat g (.inl 0) (.inr 0) - c) - μ ^ 2 * c,
    mat g (.inl 0) (.inr 0) - c, c, ?_⟩
  set a := mat g (.inl 1) (.inr 1) - (mat g (.inl 0) (.inr 0) - c) - μ ^ 2 * c with ha
  set b := mat g (.inl 0) (.inr 0) - c with hb
  have h1 : transv (e₂ F) a ∈ Q₁ F := transv_mem_qLine isLine_ln₀ hx₁ a
  have h2 : transv (e₁ F + e₂ F) b ∈ Q₁ F := transv_mem_qLine isLine_ln₀ hx₂ b
  have h3 : transv (e₁ F + μ • e₂ F) c ∈ Q₁ F := transv_mem_qLine isLine_ln₀ hx₃ c
  have h12 := (Q₁ F).mul_mem h1 h2
  have hent : ∀ i j : Fin 2, mat (transv (e₂ F) a * transv (e₁ F + e₂ F) b *
      transv (e₁ F + μ • e₂ F) c) (.inl i) (.inr j) =
      a * e₂ F (.inl i) * e₂ F (.inl j) + b * (e₁ F + e₂ F) (.inl i) * (e₁ F + e₂ F) (.inl j) +
        c * (e₁ F + μ • e₂ F) (.inl i) * (e₁ F + μ • e₂ F) (.inl j) := by
    intro i j
    rw [entry_mul_of_mem_Q₁ h12 h3, entry_mul_of_mem_Q₁ h1 h2, entry_transv_of_mem_ln₀ hx₁,
      entry_transv_of_mem_ln₀ hx₂, entry_transv_of_mem_ln₀ hx₃]
  have c0 : e₂ F (.inl 0) = 0 := by simp [e₂]
  have c1 : e₂ F (.inl 1) = 1 := by simp [e₂]
  have c2 : (e₁ F + e₂ F) (.inl 0) = 1 := by simp [e₁, e₂]
  have c3 : (e₁ F + e₂ F) (.inl 1) = 1 := by simp [e₁, e₂]
  have c4 : (e₁ F + μ • e₂ F) (.inl 0) = 1 := by simp [e₁, e₂]
  have c5 : (e₁ F + μ • e₂ F) (.inl 1) = μ := by simp [e₁, e₂]
  refine eq_of_mem_Q₁ hg ((Q₁ F).mul_mem h12 h3) ?_ ?_ ?_
  · rw [hent, c0, c2, c4, hb]
    ring
  · rw [hent, c0, c1, c2, c3, c4, c5, hb]
    linear_combination -hc
  · rw [hent, c1, c3, c5, ha, hb]
    ring

end Sp

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_tImage_inf {S : Subgroup G} (θ : MulAut ↥S) {K K' : Subgroup G} {x : G}
    (hx : x ∈ tImage θ K) (hx' : x ∈ tImage θ K') : x ∈ tImage θ (K ⊓ K') := by
  obtain ⟨y, hyS, hy, rfl⟩ := mem_tImage.1 hx
  obtain ⟨y', hy'S, hy', hyy⟩ := mem_tImage.1 hx'
  have e : (⟨y', hy'S⟩ : ↥S) = ⟨y, hyS⟩ := θ.injective (Subtype.ext hyy)
  have e' : y' = y := congrArg Subtype.val e
  subst e'
  exact mem_tImage.2 ⟨y', hyS, ⟨hy, hy'⟩, rfl⟩

namespace Cfg

variable {M T L : Subgroup G} {F : Type} [Field F] [Fintype F] (C : Cfg M T L F)
include C

theorem comm_mem_Uq_of_mem {x u : G} (hx : x ∈ M) (hu : u ∈ Uq M T L) : ⁅x, u⁆ ∈ Uq M T L := by
  rw [commutatorElement_def]
  exact (Uq M T L).mul_mem ((Subgroup.mem_normalizer_iff.1 (C.hMU hx) u).1 hu)
    ((Uq M T L).inv_mem hu)

theorem co_comm_rho {x : G} (hx : x ∈ L ⊔ pCoreOf 2 M) {u : G} (hu : u ∈ Uq M T L)
    (hc : ⁅x, u⁆ ∈ Uq M T L) :
    C.N.co ⟨⁅x, u⁆, hc⟩ = mat (C.rho ⟨x, hx⟩) *ᵥ C.N.co ⟨u, hu⟩ - C.N.co ⟨u, hu⟩ := by
  rw [C.co_comm (C.sup_le_M hx) hu hc, C.rho_spec ⟨x, hx⟩]

theorem Rt_le_inf (θ : MulAut ↥(T1 M T L)) : Rt M T L θ ≤ Uq M T L ⊓ Ut M T L θ := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  have h := C.comm_mem_inf C.pCore_le_T1 T1_le_T θ hb ha
  have e : ⁅a, b⁆ = ⁅b, a⁆⁻¹ := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact (Uq M T L ⊓ Ut M T L θ).inv_mem h

theorem T1_le_normalizer_Dt (θ : MulAut ↥(T1 M T L)) :
    T1 M T L ≤ Subgroup.normalizer (Dt M L θ : Set G) := by
  intro t ht
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨C.conj_mem_Dt_of_T1 θ ht, fun hx => ?_⟩
  have := C.conj_mem_Dt_of_T1 θ ((T1 M T L).inv_mem ht) hx
  simpa [mul_assoc] using this

theorem conj_mem_T0t (θ : MulAut ↥(T1 M T L)) {t x : G} (ht : t ∈ T1 M T L)
    (hx : x ∈ tImage θ (T ⊓ L)) : t * x * t⁻¹ ∈ tImage θ (T ⊓ L) := by
  obtain ⟨y, hyS, hy, rfl⟩ := mem_tImage.1 hx
  set s := θ.symm ⟨t, ht⟩
  have hsM : (s : G) ∈ M := C.h.le (T1_le_T s.2)
  have hs : (s : G) * y * (s : G)⁻¹ ∈ T ⊓ L :=
    ⟨T.mul_mem (T.mul_mem (T1_le_T s.2) hy.1) (T.inv_mem (T1_le_T s.2)),
      (Subgroup.mem_normalizer_iff.1 (C.h.le_normalizer hsM) y).1 hy.2⟩
  refine mem_tImage.2 ⟨_, (T1 M T L).mul_mem ((T1 M T L).mul_mem s.2 hyS)
    ((T1 M T L).inv_mem s.2), hs, ?_⟩
  have e : (⟨(s : G) * y * (s : G)⁻¹, (T1 M T L).mul_mem ((T1 M T L).mul_mem s.2 hyS)
      ((T1 M T L).inv_mem s.2)⟩ : ↥(T1 M T L)) = s * ⟨y, hyS⟩ * s⁻¹ := rfl
  rw [e, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  rfl

theorem comm_mem_sup_Dt (θ : MulAut ↥(T1 M T L)) (hE' : C.rhoIm (Ut M T L θ⁻¹) = X₂ F)
    {z u : G} (hz : z ∈ Qt M θ) (hu : u ∈ Uq M T L) : ⁅z, u⁆ ∈ Rt M T L θ ⊔ Dt M L θ := by
  obtain ⟨r, hr, hd⟩ := C.comm_Qt_mem θ hE' hu hz
  have e : ⁅z, u⁆ = (r * (r⁻¹ * ⁅u, z⁆))⁻¹ := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact (Rt M T L θ ⊔ Dt M L θ).inv_mem (Subgroup.mul_mem_sup hr hd)

theorem comm_T1_mem_of_ne (hT : C.T0bar = Q₁ F) (θ : MulAut ↥(T1 M T L))
    (hE : C.rhoIm (Ut M T L θ) = X₂ F) (hE' : C.rhoIm (Ut M T L θ⁻¹) = X₂ F)
    (hN : C.rhoIm (Qt M θ) ≠ X₂ F) {t u : G} (ht : t ∈ T1 M T L) (hu : u ∈ Uq M T L) :
    ⁅t, u⁆ ∈ Rt M T L θ ⊔ Dt M L θ := by
  have : CharP F 2 := charP_of_card_eq_prime_pow C.hF
  have hq : 2 < Nat.card F := by
    have := C.q_ge_four
    omega
  have hXN : X₂ F ≤ C.rhoIm (Qt M θ) := hE ▸ C.rhoIm_Ut_le θ
  obtain ⟨n, hnN, hnX⟩ : ∃ n ∈ C.rhoIm (Qt M θ), n ∉ X₂ F := by
    by_contra hcon
    push Not at hcon
    exact hN (le_antisymm hcon hXN)
  obtain ⟨z₀, hz₀K, hz₀, rfl⟩ := (C.mem_rhoIm).1 hnN
  have hnQ : C.rho ⟨z₀, hz₀K⟩ ∈ Q₁ F := by
    rw [← hT]
    exact ⟨⟨z₀, tImage_le θ _ hz₀⟩, rfl⟩
  set n := C.rho ⟨z₀, hz₀K⟩ with hn
  have htK := T1_le_sup ht
  have htQ : C.rho ⟨t, htK⟩ ∈ Q₁ F := by
    rw [← hT]
    exact ⟨⟨t, ht⟩, rfl⟩
  have hcU := C.comm_mem_Uq_of_mem (C.sup_le_M htK) hu
  set w := C.N.co ⟨_, hcU⟩ with hw
  have hw' : w = mat (C.rho ⟨t, htK⟩) *ᵥ C.N.co ⟨u, hu⟩ - C.N.co ⟨u, hu⟩ :=
    C.co_comm_rho htK hu hcU
  have hw2 : w (.inr 0) = 0 := by
    rw [hw', mulVec_of_mem_Q₁ htQ]
    simp [e₁, e₂]
  have hw3 : w (.inr 1) = 0 := by
    rw [hw', mulVec_of_mem_Q₁ htQ]
    simp [e₁, e₂]
  obtain ⟨v', hv'⟩ : ∃ v' : V4 F, mat n (.inl 0) (.inr 1) * v' (.inr 0) +
      mat n (.inl 1) (.inr 1) * v' (.inr 1) = w (.inl 1) := by
    by_cases h11 : mat n (.inl 1) (.inr 1) = 0
    · have h01 : mat n (.inl 0) (.inr 1) ≠ 0 := fun h01 => hnX (mem_X₂_of_mem_Q₁ hnQ h01 h11)
      refine ⟨(w (.inl 1) / mat n (.inl 0) (.inr 1)) • f₁ F, ?_⟩
      simp [f₁, h11]
      field_simp
    · refine ⟨(w (.inl 1) / mat n (.inl 1) (.inr 1)) • f₂ F, ?_⟩
      simp [f₂]
      field_simp
  obtain ⟨u₂, hu₂⟩ := C.N.co_surj v'
  have hy₂U := C.comm_mem_Uq_of_mem (C.sup_le_M hz₀K) u₂.2
  have hy₂ := C.co_comm_rho hz₀K u₂.2 hy₂U
  rw [show (⟨(u₂ : G), u₂.2⟩ : ↥(Uq M T L)) = u₂ from rfl, hu₂, ← hn,
    mulVec_of_mem_Q₁ hnQ] at hy₂
  set s := w (.inl 0) - C.N.co ⟨_, hy₂U⟩ (.inl 0) with hs
  obtain ⟨z₁, hz₁K, hz₁, hρz₁⟩ := (C.mem_rhoIm).1
    (hE.symm ▸ (transv_mem_X₂ s : transv (e₁ F) s ∈ X₂ F))
  obtain ⟨u₁, hu₁⟩ := C.N.co_surj (f₁ F)
  have hz₁Q : z₁ ∈ Qt M θ := tImage_mono' θ C.Uq_le_pCore hz₁
  have hy₁U := C.comm_mem_Uq_of_mem (C.sup_le_M hz₁K) u₁.2
  have hy₁ := C.co_comm_rho hz₁K u₁.2 hy₁U
  rw [show (⟨(u₁ : G), u₁.2⟩ : ↥(Uq M T L)) = u₁ from rfl, hu₁, hρz₁, transv_mulVec,
    form_e₁] at hy₁
  have hyU := (Uq M T L).mul_mem hy₁U hy₂U
  have hyw : C.N.co ⟨_, hyU⟩ = w := by
    have e : (⟨_, hyU⟩ : ↥(Uq M T L)) = ⟨_, hy₁U⟩ * ⟨_, hy₂U⟩ := rfl
    rw [e, C.N.co_mul]
    refine ext4 ?_ ?_ ?_ ?_
    · rw [Pi.add_apply, hy₁, hs]
      simp [f₁, e₁]
    · rw [Pi.add_apply, hy₁, hy₂, ← hv']
      simp [f₁, e₁, e₂]
    · rw [Pi.add_apply, hy₁, hy₂, hw2]
      simp [f₁, e₁, e₂]
    · rw [Pi.add_apply, hy₁, hy₂, hw3]
      simp [f₁, e₁, e₂]
  have ha : ((⟨_, hyU⟩ : ↥(Uq M T L))⁻¹ * ⟨_, hcU⟩ : ↥(Uq M T L)) ∈
      (Uq M T L ⊓ Subgroup.centralizer (L : Set G)).subgroupOf (Uq M T L) := by
    rw [Subgroup.mem_subgroupOf]
    exact (C.N.co_eq_co_iff _ _).1 hyw
  have haR := C.A_le_Rt hq θ hE ha
  have hyRD : ⁅z₁, (u₁ : G)⁆ * ⁅z₀, (u₂ : G)⁆ ∈ Rt M T L θ ⊔ Dt M L θ :=
    (Rt M T L θ ⊔ Dt M L θ).mul_mem (C.comm_mem_sup_Dt θ hE' hz₁Q u₁.2)
      (C.comm_mem_sup_Dt θ hE' hz₀ u₂.2)
  have e : ⁅t, u⁆ = (⁅z₁, (u₁ : G)⁆ * ⁅z₀, (u₂ : G)⁆) *
      ((⁅z₁, (u₁ : G)⁆ * ⁅z₀, (u₂ : G)⁆)⁻¹ * ⁅t, u⁆) := by group
  rw [e]
  exact (Rt M T L θ ⊔ Dt M L θ).mul_mem hyRD (Subgroup.mem_sup_left haR)

theorem rho_mem_X₂_of_comm (hq : 2 < Nat.card F) (θ : MulAut ↥(T1 M T L))
    (hE : C.rhoIm (Ut M T L θ) = X₂ F) (hE' : C.rhoIm (Ut M T L θ⁻¹) = X₂ F)
    (h : ∀ t ∈ T1 M T L, ∀ u ∈ Uq M T L, ⁅t, u⁆ ∈ Rt M T L θ ⊔ Dt M L θ)
    (t : G) (ht : t ∈ T ⊓ L) : C.rho1 (θ ⟨t, T_inf_L_le_T1 ht⟩) ∈ X₂ F := by
  set t' := θ ⟨t, T_inf_L_le_T1 ht⟩ with ht'
  have ht'K := T1_le_sup t'.2
  have hUL : Uq M T L ≤ T ⊓ L := le_inf C.Uq_le_T (Uq_le_L C.h)
  refine mem_X₂_of_sub_mem fun v => ?_
  obtain ⟨u, rfl⟩ := C.N.co_surj v
  have hcU := C.comm_mem_Uq_of_mem (C.sup_le_M ht'K) u.2
  have hR : ⁅(t' : G), (u : G)⁆ ∈ Rt M T L θ := by
    have h1 : ⁅(t' : G), (u : G)⁆ ∈ ((Rt M T L θ ⊔ Dt M L θ : Subgroup G) : Set G) :=
      h t' t'.2 u u.2
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _
      ((((C.Rt_le_inf θ).trans inf_le_right).trans (tImage_le θ _)).trans
        (C.T1_le_normalizer_Dt θ))] at h1
    obtain ⟨r, hr, d, hd, hrd⟩ := h1
    change r * d = _ at hrd
    have ht'T0 : (t' : G) ∈ tImage θ (T ⊓ L) := mem_tImage.2 ⟨t, T_inf_L_le_T1 ht, ht, rfl⟩
    have hT0 : ⁅(t' : G), (u : G)⁆ ∈ tImage θ (T ⊓ L) := by
      have e : ⁅(t' : G), (u : G)⁆ = (t' : G) * ((u : G) * (t' : G)⁻¹ * (u : G)⁻¹) := by
        rw [commutatorElement_def]
        group
      rw [e]
      exact (tImage θ (T ⊓ L)).mul_mem ht'T0
        (C.conj_mem_T0t θ (C.Uq_le_T1 u.2) ((tImage θ (T ⊓ L)).inv_mem ht'T0))
    have hrT0 : r ∈ tImage θ (T ⊓ L) := tImage_mono' θ hUL ((C.Rt_le_inf θ hr).2)
    have hdT0 : d ∈ tImage θ (T ⊓ L) := by
      have e : d = r⁻¹ * ⁅(t' : G), (u : G)⁆ := by
        rw [← hrd]
        group
      rw [e]
      exact (tImage θ (T ⊓ L)).mul_mem ((tImage θ (T ⊓ L)).inv_mem hrT0) hT0
    have hdA : d ∈ tImage θ (Uq M T L ⊓ Subgroup.centralizer (L : Set G)) := by
      refine tImage_mono' θ ?_ (mem_tImage_inf θ hdT0 hd)
      rintro y ⟨⟨hyT, hyL⟩, hyQ, hyC⟩
      refine ⟨?_, hyC⟩
      rw [← C.T_inf_L_inf_pCore]
      exact ⟨⟨hyT, hyL⟩, hyQ⟩
    have hdR : d ∈ Rt M T L θ := by
      rw [← C.tImage_Rt θ]
      exact tImage_mono' θ (C.A_le_Rt hq θ⁻¹ hE') hdA
    rw [← hrd]
    exact (Rt M T L θ).mul_mem hr hdR
  obtain ⟨hcU', hco⟩ := (C.mem_Usub).1 (C.Rt_le_Usub θ hE hR)
  rw [C.rho1_apply, show C.N.co u = C.N.co ⟨(u : G), u.2⟩ from rfl, ← C.co_comm_rho ht'K u.2 hcU]
  exact hco

theorem comm_mem_Dt_of_mem_inf (θ : MulAut ↥(T1 M T L)) (hE : C.rhoIm (Ut M T L θ) = X₂ F)
    (hK : ∀ (t : G) (ht : t ∈ T ⊓ L), C.rho1 (θ ⟨t, T_inf_L_le_T1 ht⟩) ∈ X₂ F) {u t : G}
    (hu : u ∈ Uq M T L) (huQ : u ∈ Qt M θ) (ht : t ∈ T1 M T L) : ⁅u, t⁆ ∈ Dt M L θ := by
  have hperp : C.N.co ⟨u, hu⟩ ∈ perp (pt₀ F) := by
    rw [← fixSp_X₂]
    refine mem_fixSp.2 fun g hg => ?_
    rw [← hE] at hg
    obtain ⟨z, hzK, hz, rfl⟩ := (C.mem_rhoIm).1 hg
    refine (C.co_conj ⟨z, hzK⟩ (u := ⟨u, hu⟩) (v := ⟨u, hu⟩) ?_).symm
    show u = z * u * z⁻¹
    rw [← C.comm_Qt_Ut θ huQ hz, mul_inv_cancel_right]
  have hcomm : ∀ (s : G) (hs : s ∈ T ⊓ L),
      ((θ ⟨s, T_inf_L_le_T1 hs⟩ : ↥(T1 M T L)) : G) * u = u *
        ((θ ⟨s, T_inf_L_le_T1 hs⟩ : ↥(T1 M T L)) : G) := by
    intro s hs
    have hfix := (mem_fixer.1 (hK s hs)) _ hperp
    rw [C.rho1_apply] at hfix
    have h1 := C.conj_eq_of_fix ⟨_, T1_le_sup (θ ⟨s, T_inf_L_le_T1 hs⟩).2⟩ hu hfix
    calc ((θ ⟨s, T_inf_L_le_T1 hs⟩ : ↥(T1 M T L)) : G) * u =
          ((θ ⟨s, T_inf_L_le_T1 hs⟩ : ↥(T1 M T L)) : G) * u *
            ((θ ⟨s, T_inf_L_le_T1 hs⟩ : ↥(T1 M T L)) : G)⁻¹ *
            ((θ ⟨s, T_inf_L_le_T1 hs⟩ : ↥(T1 M T L)) : G) := by group
      _ = u * ((θ ⟨s, T_inf_L_le_T1 hs⟩ : ↥(T1 M T L)) : G) := by rw [h1]
  obtain ⟨y, hyT, hyQ, hye⟩ := mem_tImage.1 huQ
  have hyc : ∀ (s : G) (hs : s ∈ T ⊓ L), s * y = y * s := by
    intro s hs
    have h1 := hcomm s hs
    rw [← hye] at h1
    have h2 : θ (⟨s, T_inf_L_le_T1 hs⟩ * ⟨y, hyT⟩) = θ (⟨y, hyT⟩ * ⟨s, T_inf_L_le_T1 hs⟩) := by
      rw [map_mul, map_mul]
      exact Subtype.ext h1
    exact congrArg Subtype.val (θ.injective h2)
  set t₀ := θ⁻¹ ⟨t, ht⟩ with ht₀
  obtain ⟨l, hl, q, hq, hlq⟩ := C.exists_mul_of_mem_T1 t₀.2
  have hcD : ⁅y, (t₀ : G)⁆ ∈ Dq M L := by
    have hyq : ⁅y, q⁆ ∈ Dq M L :=
      commutator_pCore_le_Dq C.h C.hVU (Subgroup.commutator_mem_commutator hyQ hq)
    have e : ⁅y, (t₀ : G)⁆ = l * ⁅y, q⁆ * l⁻¹ := by
      rw [← hlq]
      have h1 := hyc l hl
      calc ⁅y, l * q⁆ = (y * l) * q * y⁻¹ * q⁻¹ * l⁻¹ := by
            rw [commutatorElement_def]
            group
        _ = (l * y) * q * y⁻¹ * q⁻¹ * l⁻¹ := by rw [h1]
        _ = l * ⁅y, q⁆ * l⁻¹ := by
            rw [commutatorElement_def]
            group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.1 (le_normalizer_Dq C.h.le_normalizer
      (C.h.L_le hl.2)) _).1 hyq
  have hcT : ⁅y, (t₀ : G)⁆ ∈ T1 M T L := (⁅(⟨y, hyT⟩ : ↥(T1 M T L)), t₀⁆ : ↥(T1 M T L)).2
  refine mem_tImage.2 ⟨_, hcT, hcD, ?_⟩
  have e : (⟨⁅y, (t₀ : G)⁆, hcT⟩ : ↥(T1 M T L)) = ⁅(⟨y, hyT⟩ : ↥(T1 M T L)), t₀⁆ := rfl
  rw [e, map_commutatorElement, ht₀, MulAut.apply_inv_self]
  show ⁅((θ ⟨y, hyT⟩ : ↥(T1 M T L)) : G), t⁆ = ⁅u, t⁆
  rw [hye]

theorem Rt_le_Dt (hT : C.T0bar = Q₁ F) (hq : 2 < Nat.card F) (θ : MulAut ↥(T1 M T L))
    (hE : C.rhoIm (Ut M T L θ) = X₂ F)
    (h : ∀ u ∈ Uq M T L, u ∈ Qt M θ → ∀ t ∈ T1 M T L, ⁅u, t⁆ ∈ Dt M L θ) :
    Rt M T L θ ≤ Dt M L θ := by
  have : CharP F 2 := charP_of_card_eq_prime_pow C.hF
  let H : Subgroup G :=
    { carrier := {t | t ∈ T1 M T L ∧ ∀ u ∈ Uq M T L, ⁅u, t⁆ ∈ Dt M L θ}
      one_mem' := ⟨(T1 M T L).one_mem, fun u _ => by
        rw [commutatorElement_one_right]
        exact (Dt M L θ).one_mem⟩
      mul_mem' := fun {a b} ha hb => ⟨(T1 M T L).mul_mem ha.1 hb.1, fun u hu => by
        have e : ⁅u, a * b⁆ = ⁅u, a⁆ * (a * ⁅u, b⁆ * a⁻¹) := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact (Dt M L θ).mul_mem (ha.2 u hu) (C.conj_mem_Dt_of_T1 θ ha.1 (hb.2 u hu))⟩
      inv_mem' := fun {a} ha => ⟨(T1 M T L).inv_mem ha.1, fun u hu => by
        have e : ⁅u, a⁻¹⁆ = a⁻¹ * ⁅u, a⁆⁻¹ * a⁻¹⁻¹ := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact C.conj_mem_Dt_of_T1 θ ((T1 M T L).inv_mem ha.1)
          ((Dt M L θ).inv_mem (ha.2 u hu))⟩ }
  have hmemH : ∀ {t : G}, t ∈ H ↔ t ∈ T1 M T L ∧ ∀ u ∈ Uq M T L, ⁅u, t⁆ ∈ Dt M L θ :=
    Iff.rfl
  have hQH : ∀ q ∈ pCoreOf 2 M, q ∈ H := by
    intro q hq'
    refine hmemH.2 ⟨C.pCore_le_T1 hq', fun u hu => ?_⟩
    have e : ⁅u, q⁆ = 1 := by
      rw [commutatorElement_def, ← comm_of_mem_Uq C.h hu hq']
      group
    rw [e]
    exact (Dt M L θ).one_mem
  have hXH : ∀ (x : V4 F), x ∈ ln₀ F → x (.inl 1) ≠ 0 → ∀ (c : F) (t : ↥(T1 M T L)),
      C.rho1 t = transv x c → (t : G) ∈ H := by
    intro x hx hx1 c t htx
    obtain ⟨h0, h1⟩ := mem_ln₀.1 hx
    refine hmemH.2 ⟨t.2, fun u hu => ?_⟩
    set v := C.N.co ⟨u, hu⟩ with hv
    set v₂ : V4 F := (form F x v / x (.inl 1)) • f₂ F with hv₂
    obtain ⟨c₁, hc₁⟩ := C.N.co_surj (v - v₂)
    obtain ⟨w, hw⟩ := C.N.co_surj v₂
    have hfix : mat (C.rho ⟨t, T1_le_sup t.2⟩) *ᵥ C.N.co ⟨(c₁ : G), c₁.2⟩ =
        C.N.co ⟨(c₁ : G), c₁.2⟩ := by
      rw [show (⟨(c₁ : G), c₁.2⟩ : ↥(Uq M T L)) = c₁ from rfl, hc₁, ← C.rho1_apply, htx,
        transv_mulVec]
      have hf : form F x (v - v₂) = 0 := by
        rw [map_sub, hv₂, map_smul, form_apply x (f₂ F)]
        simp [f₂, h0, h1]
        field_simp
        ring
      rw [hf, mul_zero, zero_smul, add_zero]
    have htc := C.conj_eq_of_fix ⟨t, T1_le_sup t.2⟩ c₁.2 hfix
    have hwperp : (w : G) ∈ C.Usub (perp (pt₀ F)) := by
      refine (C.mem_Usub).2 ⟨w.2, ?_⟩
      rw [show (⟨(w : G), w.2⟩ : ↥(Uq M T L)) = w from rfl, hw, hv₂]
      exact mem_perp_pt₀.2 (by simp [f₂])
    have hwQ := C.Usub_perp_le_Qt θ hE hwperp
    set a : G := ((c₁ : G) * w)⁻¹ * u with hadef
    have haA : a ∈ Uq M T L ⊓ Subgroup.centralizer (L : Set G) := by
      have hco : C.N.co (c₁ * w) = C.N.co ⟨u, hu⟩ := by
        rw [C.N.co_mul, hc₁, hw, ← hv]
        abel
      have := (C.N.co_eq_co_iff _ _).1 hco
      exact this
    have hta := C.conj_eq_of_mem_A (T1_le_sup t.2) haA
    have hat : a * (t : G) * a⁻¹ = t := by
      have h2 : (t : G) * a = a * t := by
        calc (t : G) * a = (t : G) * a * (t : G)⁻¹ * t := by group
          _ = a * t := by rw [hta]
      calc a * (t : G) * a⁻¹ = (t : G) * a * a⁻¹ := by rw [h2]
        _ = t := by group
    have hct : (c₁ : G)⁻¹ * (t : G)⁻¹ = (t : G)⁻¹ * (c₁ : G)⁻¹ := by
      have h2 : (t : G) * c₁ = c₁ * t := by
        calc (t : G) * c₁ = (t : G) * c₁ * (t : G)⁻¹ * t := by group
          _ = c₁ * t := by rw [htc]
      rw [← mul_inv_rev, ← mul_inv_rev, h2]
    have e : u = (c₁ : G) * w * a := by
      rw [hadef]
      group
    have e2 : ⁅u, (t : G)⁆ = (c₁ : G) * ⁅(w : G), (t : G)⁆ * (c₁ : G)⁻¹ := by
      rw [e]
      calc ⁅(c₁ : G) * w * a, (t : G)⁆ =
            (c₁ : G) * w * (a * t * a⁻¹) * (w : G)⁻¹ * (c₁ : G)⁻¹ * (t : G)⁻¹ := by
            rw [commutatorElement_def]
            group
        _ = (c₁ : G) * w * t * (w : G)⁻¹ * ((c₁ : G)⁻¹ * (t : G)⁻¹) := by
            rw [hat]
            group
        _ = (c₁ : G) * w * t * (w : G)⁻¹ * ((t : G)⁻¹ * (c₁ : G)⁻¹) := by rw [hct]
        _ = (c₁ : G) * ⁅(w : G), (t : G)⁆ * (c₁ : G)⁻¹ := by
            rw [commutatorElement_def]
            group
    rw [e2]
    exact C.conj_mem_Dt_of_T1 θ (C.Uq_le_T1 c₁.2) (h w w.2 hwQ t t.2)
  obtain ⟨μ, hμ0, hμ1⟩ := exists_ne_zero_ne_one hq
  have hT1H : ∀ t ∈ T1 M T L, t ∈ H := by
    intro t ht
    have hg : C.rho1 ⟨t, ht⟩ ∈ Q₁ F := by
      rw [← hT]
      exact ⟨⟨t, ht⟩, rfl⟩
    obtain ⟨a, b, c, habc⟩ := exists_eq_transv_mul hμ1 hg
    have hpre : ∀ (x : V4 F), x ∈ ln₀ F → x (.inl 1) ≠ 0 → ∀ c : F,
        ∃ s : ↥(T1 M T L), (s : G) ∈ H ∧ C.rho1 s = transv x c := by
      intro x hx hx1 c
      have hm : transv x c ∈ C.T0bar := by
        rw [hT]
        exact transv_mem_qLine isLine_ln₀ hx c
      obtain ⟨s, hs⟩ := hm
      exact ⟨s, hXH x hx hx1 c s hs, hs⟩
    obtain ⟨s₁, hs₁H, hs₁⟩ := hpre (e₂ F) (mem_ln₀.2 ⟨by simp [e₂], by simp [e₂]⟩)
      (by simp [e₂]) a
    obtain ⟨s₂, hs₂H, hs₂⟩ := hpre (e₁ F + e₂ F) (mem_ln₀.2 ⟨by simp [e₁, e₂], by simp [e₁, e₂]⟩)
      (by simp [e₁, e₂]) b
    obtain ⟨s₃, hs₃H, hs₃⟩ := hpre (e₁ F + μ • e₂ F)
      (mem_ln₀.2 ⟨by simp [e₁, e₂], by simp [e₁, e₂]⟩) (by simp [e₁, e₂, hμ0]) c
    have hsH : ((s₁ * s₂ * s₃ : ↥(T1 M T L)) : G) ∈ H := H.mul_mem (H.mul_mem hs₁H hs₂H) hs₃H
    have hρ : C.rho1 (s₁ * s₂ * s₃) = C.rho1 ⟨t, ht⟩ := by
      rw [map_mul, map_mul, hs₁, hs₂, hs₃, habc]
    have hq' : ((s₁ * s₂ * s₃)⁻¹ * ⟨t, ht⟩ : ↥(T1 M T L)) ∈ (C.rho1).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hρ, inv_mul_cancel]
    have hqQ := (C.rho1_eq_one_iff _).1 hq'
    have e : t = ((s₁ * s₂ * s₃ : ↥(T1 M T L)) : G) *
        (((s₁ * s₂ * s₃)⁻¹ * ⟨t, ht⟩ : ↥(T1 M T L)) : G) := by
      rw [← Subgroup.coe_mul, mul_inv_cancel_left]
    rw [e]
    exact H.mul_mem hsH (hQH _ hqQ)
  rw [Subgroup.commutator_le]
  intro u hu z hz
  exact (hmemH.1 (hT1H z (tImage_le θ _ hz))).2 u hu

theorem not_Rt_le_Dt (hq : 2 < Nat.card F) (θ : MulAut ↥(T1 M T L))
    (hE : C.rhoIm (Ut M T L θ) = X₂ F) (h : Rt M T L θ ≤ Dt M L θ) : False := by
  set A := Uq M T L ⊓ Subgroup.centralizer (L : Set G) with hA
  have hRA : Rt M T L θ ≤ tImage θ A := by
    intro r hr
    refine tImage_mono' θ ?_ (mem_tImage_inf θ (C.Rt_le_inf θ hr).2 (h hr))
    rintro x ⟨hxU, -, hxC⟩
    exact ⟨hxU, hxC⟩
  have hcard : Nat.card ↥(Rt M T L θ) ≤ Nat.card ↥A := by
    calc Nat.card ↥(Rt M T L θ) ≤ Nat.card ↥(tImage θ A) := Subgroup.card_le_of_le hRA
      _ = Nat.card ↥A := card_tImage θ (inf_le_left.trans C.Uq_le_T1)
  have heq := Subgroup.eq_of_le_of_card_ge (C.A_le_Rt hq θ hE) hcard
  obtain ⟨u, hu⟩ := C.N.co_surj (e₁ F)
  have hup : (u : G) ∈ C.Usub (pt₀ F) := by
    refine (C.mem_Usub).2 ⟨u.2, ?_⟩
    rw [show (⟨(u : G), u.2⟩ : ↥(Uq M T L)) = u from rfl, hu, pt₀_eq_span]
    exact Submodule.mem_span_singleton_self _
  obtain ⟨r, hr, ha⟩ := C.exists_Rt θ hE hup
  rw [← heq] at hr
  have h1 : (u : G) ∈ A := by
    have e : (u : G) = r * (r⁻¹ * u) := by group
    rw [e]
    exact A.mul_mem hr ha
  have h2 := (C.N.co_eq_zero_iff u).2 h1
  rw [hu] at h2
  have h3 := congrFun h2 (.inl 0)
  simp [e₁] at h3

theorem false_of_bad_Q₁ (hT : C.T0bar = Q₁ F) (θ : MulAut ↥(T1 M T L))
    (hE : C.rhoIm (Ut M T L θ) = X₂ F)
    (hK : ∀ (t : G) (ht : t ∈ T ⊓ L), C.rho1 (θ ⟨t, T_inf_L_le_T1 ht⟩) ∈ X₂ F) : False := by
  have hq : 2 < Nat.card F := by
    have := C.q_ge_four
    omega
  exact C.not_Rt_le_Dt hq θ hE (C.Rt_le_Dt hT hq θ hE fun u hu huQ t ht =>
    C.comm_mem_Dt_of_mem_inf θ hE hK hu huQ ht)

theorem rhoIm_Qt_eq_X₂_of_Q₁ (hT : C.T0bar = Q₁ F) (θ : MulAut ↥(T1 M T L))
    (hE : C.rhoIm (Ut M T L θ) = X₂ F) (hE' : C.rhoIm (Ut M T L θ⁻¹) = X₂ F) :
    C.rhoIm (Qt M θ) = X₂ F := by
  by_contra hN
  have hq : 2 < Nat.card F := by
    have := C.q_ge_four
    omega
  exact C.false_of_bad_Q₁ hT θ hE (C.rho_mem_X₂_of_comm hq θ hE hE' fun t ht u hu =>
    C.comm_T1_mem_of_ne hT θ hE hE' hN ht hu)

theorem isGood_of_Q₁ (hT : C.T0bar = Q₁ F) (θ : MulAut ↥(T1 M T L))
    (hE : C.rhoIm (Ut M T L θ) = X₂ F) (hE' : C.rhoIm (Ut M T L θ⁻¹) = X₂ F) :
    C.IsGood θ ∧ C.IsGood θ⁻¹ := by
  have hE'' : C.rhoIm (Ut M T L θ⁻¹⁻¹) = X₂ F := by
    rw [inv_inv]
    exact hE
  have hN := C.rhoIm_Qt_eq_X₂_of_Q₁ hT θ hE hE'
  have hN' := C.rhoIm_Qt_eq_X₂_of_Q₁ hT θ⁻¹ hE' hE''
  have hN'' : C.rhoIm (Qt M θ⁻¹⁻¹) = X₂ F := by
    rw [inv_inv]
    exact hN
  exact ⟨C.isGood_of_rhoIm θ hE hN hE' hN', C.isGood_of_rhoIm θ⁻¹ hE' hN' hE'' hN''⟩

end Cfg

end CFSG.Quasithin.MS93.S37
