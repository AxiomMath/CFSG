module

public import CFSG.Quasithin.MS93.S5A53Sp
public import CFSG.Quasithin.MS93.S37Ex

public section

namespace CFSG.Quasithin.MS93.S37

open CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.Quasithin.MS93 CFSG.Quasithin.MS93.MSP
open CFSG.QuasithinUnique CFSG.Quasithin.MS93.S36 CFSG.Quasithin.Vol2
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFour CFSG.Quasithin.JonesParshall
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix

section Alg

variable {F : Type} [Field F] [Fintype F] [CharP F 2]

theorem eq_zero_of_sqrt_mul {B w : F} (hF : 2 < Nat.card F)
    (h : ∀ c : F, B * sqrtF c + c * w = 0) : B = 0 ∧ w = 0 := by
  obtain ⟨s, hs0, hs1⟩ := exists_ne_zero_ne_one hF
  have h1 := h 1
  rw [sqrtF_one, mul_one, one_mul] at h1
  have h2 := h (s ^ 2)
  have hs : sqrtF (s ^ 2) = s := by
    apply sq_inj
    rw [sqrtF_sq]
  rw [hs] at h2
  have hw : w = 0 := by
    have hB : B = -w := by linear_combination h1
    rw [hB] at h2
    have h3 : s * (s - 1) * w = 0 := by linear_combination h2
    rcases mul_eq_zero.1 h3 with h4 | h4
    · rcases mul_eq_zero.1 h4 with h5 | h5
      · exact absurd h5 hs0
      · exact absurd (sub_eq_zero.1 h5) hs1
    · exact h4
  refine ⟨?_, hw⟩
  rw [hw, add_zero] at h1
  exact h1

omit [Fintype F] [CharP F 2] in
theorem transv_e₁_eq_tau (c : F) : transv (e₁ F) c = tau (sym2_transpose c 0 0) := by
  refine ext_mulVec fun v => ?_
  obtain ⟨e0, e1, e2, e3⟩ := mulVec_tau_sym2 c 0 0 v
  rw [transv_mulVec, form_e₁]
  funext i
  rcases i with i | i <;> fin_cases i
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Fin.zero_eta, Fin.isValue] at e0 ⊢
    rw [e0]
    simp [e₁]
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Fin.mk_one, Fin.isValue] at e1 ⊢
    rw [e1]
    simp [e₁]
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Fin.zero_eta, Fin.isValue] at e2 ⊢
    rw [e2]
    simp [e₁]
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Fin.mk_one, Fin.isValue] at e3 ⊢
    rw [e3]
    simp [e₁]

theorem cform_transv_e₁ (B : F) (m : V4 F) (c : F) :
    S5.cform B m (transv (e₁ F) c) = (B * sqrtF c + c * m (.inr 0)) • e₁ F := by
  rw [transv_e₁_eq_tau]
  funext i
  rcases i with i | i <;> fin_cases i
  · show S5.cform B m (tau _) (.inl 0) = _
    rw [S5.cform_tau_inl0]
    simp [sym2, e₁]
  · show S5.cform B m (tau _) (.inl 1) = _
    rw [S5.cform_tau_inl1]
    simp [sym2, e₁, sqrtF_zero]
  · show S5.cform B m (tau _) (.inr 0) = _
    rw [S5.cform_tau_inr]
    simp [e₁]
  · show S5.cform B m (tau _) (.inr 1) = _
    rw [S5.cform_tau_inr]
    simp [e₁]

theorem eq_of_cform_eq (hF : 2 < Nat.card F) {B B' : F} {m m' : V4 F}
    (h : ∀ g, S5.cform B m g = S5.cform B' m' g) : B = B' := by
  have key : ∀ c : F, (B - B') * sqrtF c + c * (m (.inr 0) - m' (.inr 0)) = 0 := by
    intro c
    have h1 := congrFun (h (transv (e₁ F) c)) (.inl 0)
    rw [cform_transv_e₁, cform_transv_e₁] at h1
    simp only [Pi.smul_apply, smul_eq_mul, e₁, Pi.single_eq_same, mul_one] at h1
    linear_combination h1
  exact sub_eq_zero.1 (eq_zero_of_sqrt_mul hF key).1

theorem cform_add (B B' : F) (m m' : V4 F) (g : Sp4 F) :
    S5.cform (B + B') (m + m') g = S5.cform B m g + S5.cform B' m' g := by
  simp only [S5.cform, add_smul, Matrix.mulVec_add]
  abel

end Alg

variable {G : Type} [Group G] [Finite G]

namespace Cfg

variable {M T L : Subgroup G} {F : Type} [Field F] [Fintype F] (C : Cfg M T L F)
include C

theorem comm_mem_Uq' {x l : G} (hx : x ∈ pCoreOf 2 M) (hl : l ∈ L) : ⁅l, x⁆ ∈ Uq M T L := by
  have h := comm_mem_Uq C.hVU hx hl
  have e : ⁅l, x⁆ = ⁅x, l⁆⁻¹ := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact (Uq M T L).inv_mem h

noncomputable def lift (g : Sp4 F) : G := ((Classical.choose (C.hα g) : ↥L) : G)

theorem lift_mem (g : Sp4 F) : C.lift g ∈ L := (Classical.choose (C.hα g)).2

theorem alpha_lift (g : Sp4 F) : C.α ⟨C.lift g, C.lift_mem g⟩ = g :=
  Classical.choose_spec (C.hα g)

theorem mem_Uq_of_alpha_eq_one {l : G} (hl : l ∈ L) (h : C.α ⟨l, hl⟩ = 1) : l ∈ Uq M T L := by
  have h1 : C.rho ⟨l, Subgroup.mem_sup_left hl⟩ = 1 := by rw [C.rho_of_mem_L hl, h]
  rw [C.rho_eq_one_iff] at h1
  rw [← C.inf_pCore_eq_Uq]
  exact ⟨hl, h1⟩

theorem comm_lift_eq {x l : G} (hx : x ∈ pCoreOf 2 M) (hl : l ∈ L) :
    ⁅C.lift (C.α ⟨l, hl⟩), x⁆ = ⁅l, x⁆ := by
  set l' := C.lift (C.α ⟨l, hl⟩) with hl'
  have hk : l⁻¹ * l' ∈ Uq M T L := by
    refine C.mem_Uq_of_alpha_eq_one (L.mul_mem (L.inv_mem hl) (C.lift_mem _)) ?_
    have e : (⟨l⁻¹ * l', L.mul_mem (L.inv_mem hl) (C.lift_mem _)⟩ : ↥L) =
        (⟨l, hl⟩ : ↥L)⁻¹ * ⟨l', C.lift_mem _⟩ := rfl
    rw [e, map_mul, map_inv, C.alpha_lift, inv_mul_cancel]
  have hc := comm_of_mem_Uq C.h hk hx
  have e2 : l' = l * (l⁻¹ * l') := by group
  rw [e2]
  calc ⁅l * (l⁻¹ * l'), x⁆ = l * ((l⁻¹ * l') * x * (l⁻¹ * l')⁻¹) * l⁻¹ * x⁻¹ := by
        rw [commutatorElement_def]; group
    _ = ⁅l, x⁆ := by rw [← hc, mul_inv_cancel_right, commutatorElement_def]

noncomputable def coc {x : G} (hx : x ∈ pCoreOf 2 M) (g : Sp4 F) : V4 F :=
  C.N.co ⟨⁅C.lift g, x⁆, C.comm_mem_Uq' hx (C.lift_mem g)⟩

theorem coc_spec {x l : G} (hx : x ∈ pCoreOf 2 M) (hl : l ∈ L) :
    C.coc hx (C.α ⟨l, hl⟩) = C.N.co ⟨⁅l, x⁆, C.comm_mem_Uq' hx hl⟩ := by
  unfold coc
  congr 2
  exact C.comm_lift_eq hx hl

theorem co_conj_L {l : G} (hl : l ∈ L) {u : G} (hu : u ∈ Uq M T L)
    (hc : l * u * l⁻¹ ∈ Uq M T L) :
    C.N.co ⟨l * u * l⁻¹, hc⟩ = mat (C.α ⟨l, hl⟩) *ᵥ C.N.co ⟨u, hu⟩ := by
  rw [← C.rho_of_mem_L hl]
  exact C.co_conj ⟨l, Subgroup.mem_sup_left hl⟩ rfl

theorem coc_mul {x : G} (hx : x ∈ pCoreOf 2 M) (g h : Sp4 F) :
    C.coc hx (g * h) = C.coc hx g + mat g *ᵥ C.coc hx h := by
  set l₁ := C.lift g
  set l₂ := C.lift h
  have hl₁ := C.lift_mem g
  have hl₂ := C.lift_mem h
  have hgh : C.α ⟨l₁ * l₂, L.mul_mem hl₁ hl₂⟩ = g * h := by
    have e : (⟨l₁ * l₂, L.mul_mem hl₁ hl₂⟩ : ↥L) = ⟨l₁, hl₁⟩ * ⟨l₂, hl₂⟩ := rfl
    rw [e, map_mul, C.alpha_lift, C.alpha_lift]
  rw [← hgh, C.coc_spec hx]
  have hc2 := C.comm_mem_Uq' hx hl₂
  have hconj : l₁ * ⁅l₂, x⁆ * l₁⁻¹ ∈ Uq M T L :=
    (Subgroup.mem_normalizer_iff.1 (C.hMU (C.h.L_le hl₁)) _).1 hc2
  have e : (⟨⁅l₁ * l₂, x⁆, C.comm_mem_Uq' hx (L.mul_mem hl₁ hl₂)⟩ : ↥(Uq M T L)) =
      ⟨l₁ * ⁅l₂, x⁆ * l₁⁻¹, hconj⟩ * ⟨⁅l₁, x⁆, C.comm_mem_Uq' hx hl₁⟩ := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, commutatorElement_def]
    group
  rw [e, C.N.co_mul, C.co_conj_L hl₁ hc2 hconj, C.alpha_lift, add_comm]
  rfl

theorem exists_cform [CharP F 2] {x : G} (hx : x ∈ pCoreOf 2 M) :
    ∃ (B : F) (m : V4 F), ∀ g, C.coc hx g = S5.cform B m g := by
  obtain ⟨B, m, h⟩ := S5.exists_eq_sqf C.hF (by have := C.hk; omega) (C.coc_mul hx)
  exact ⟨B, m, h⟩

theorem exists_comm_eq {x : G} (hx : x ∈ pCoreOf 2 M) {t : G} (ht : t ∈ L ⊔ pCoreOf 2 M) :
    ∃ (u : G) (hu : u ∈ Uq M T L), C.N.co ⟨u, hu⟩ = C.coc hx (C.rho ⟨t, ht⟩) ∧
      u⁻¹ * ⁅t, x⁆ ∈ Dq M L := by
  obtain ⟨l, hl, q, hq, e⟩ := C.exists_mul_of_mem_sup ht
  have hte : (⟨t, ht⟩ : ↥(L ⊔ pCoreOf 2 M)) = ⟨l * q, e ▸ ht⟩ := Subtype.ext e.symm
  refine ⟨⁅l, x⁆, C.comm_mem_Uq' hx hl, ?_, ?_⟩
  · rw [hte, C.rho_mul hl hq, C.coc_spec hx hl]
  · rw [← e]
    have hd : ⁅x⁻¹, q⁆ ∈ Dq M L :=
      commutator_pCore_le_Dq C.h C.hVU (Subgroup.commutator_mem_commutator (inv_mem hx) hq)
    have hld : l * ⁅x⁻¹, q⁆ * l⁻¹ = ⁅x⁻¹, q⁆ := by
      rw [Subgroup.mem_centralizer_iff.1 hd.2 l hl, mul_inv_cancel_right]
    have hDn : x ∈ Subgroup.normalizer (Dq M L : Set G) :=
      le_normalizer_Dq C.h.le_normalizer (pCoreOf_le' M hx)
    have e2 : ⁅l, x⁆⁻¹ * ⁅l * q, x⁆ = x * (l * ⁅x⁻¹, q⁆ * l⁻¹) * x⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e2, hld]
    exact (Subgroup.mem_normalizer_iff.1 hDn _).1 hd

theorem comm_mem_of_X₂ {x : G} (hx : x ∈ pCoreOf 2 M) {t : G} (ht : t ∈ L ⊔ pCoreOf 2 M)
    (htX : C.rho ⟨t, ht⟩ ∈ X₂ F) :
    ∃ (u : G) (hu : u ∈ Uq M T L), C.N.co ⟨u, hu⟩ ∈ pt₀ F ∧ u⁻¹ * ⁅t, x⁆ ∈ Dq M L := by
  have : CharP F 2 := charP_of_card_eq_prime_pow C.hF
  obtain ⟨u, hu, hco, hD⟩ := C.exists_comm_eq hx ht
  obtain ⟨B, m, hBm⟩ := C.exists_cform hx
  obtain ⟨c, hc⟩ := mem_X₂_iff.1 htX
  refine ⟨u, hu, ?_, hD⟩
  have e : C.N.co ⟨u, hu⟩ = (B * sqrtF c + c * m (.inr 0)) • e₁ F := by
    rw [hco, hBm, ← hc, cform_transv_e₁]
  rw [e, mem_pt₀]
  simp [e₁]

theorem coc_mul_left {x y : G} (hx : x ∈ pCoreOf 2 M) (hy : y ∈ pCoreOf 2 M) (g : Sp4 F) :
    C.coc ((pCoreOf 2 M).mul_mem hx hy) g = C.coc hx g + C.coc hy g := by
  unfold coc
  set l := C.lift g
  have hl := C.lift_mem g
  have hcy := C.comm_mem_Uq' hy hl
  have e : (⟨⁅l, x * y⁆, C.comm_mem_Uq' ((pCoreOf 2 M).mul_mem hx hy) hl⟩ : ↥(Uq M T L)) =
      ⟨⁅l, x⁆, C.comm_mem_Uq' hx hl⟩ * ⟨⁅l, y⁆, hcy⟩ := by
    apply Subtype.ext
    have hxc : x * ⁅l, y⁆ * x⁻¹ = ⁅l, y⁆ := by
      rw [comm_of_mem_Uq C.h hcy hx, mul_inv_cancel_right]
    simp only [Subgroup.coe_mul]
    calc ⁅l, x * y⁆ = ⁅l, x⁆ * (x * ⁅l, y⁆ * x⁻¹) := by
          simp only [commutatorElement_def]; group
      _ = ⁅l, x⁆ * ⁅l, y⁆ := by rw [hxc]
  rw [e, C.N.co_mul]

theorem coc_of_mem_Uq {u : G} (hu : u ∈ Uq M T L) (hx : u ∈ pCoreOf 2 M) (g : Sp4 F) :
    C.coc hx g = mat g *ᵥ C.N.co ⟨u, hu⟩ - C.N.co ⟨u, hu⟩ := by
  have hl := C.lift_mem g
  have h := C.co_comm (C.h.L_le hl) hu (C.comm_mem_Uq' hx hl)
  have key : C.act (C.h.L_le hl) (C.N.co ⟨u, hu⟩) = mat g *ᵥ C.N.co ⟨u, hu⟩ := by
    have := C.N.act_of_mem C.hMU C.hMA (C.h.L_le hl) hl (C.N.co ⟨u, hu⟩)
    rw [C.N_α, C.alpha_lift] at this
    exact this
  unfold coc
  rw [h, key]

theorem mem_Dq_of_coc_eq_zero {x : G} (hx : x ∈ pCoreOf 2 M) (h : ∀ g, C.coc hx g = 0) :
    x ∈ Dq M L := by
  refine mem_Dq_of_comm C.h hx fun l hl => ?_
  have h1 := h (C.α ⟨l, hl⟩)
  rw [C.coc_spec hx hl, C.N.co_eq_zero_iff] at h1
  have e : ⁅x, l⁆ = ⁅l, x⁆⁻¹ := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact (Dq M L).inv_mem ⟨(C.h.Uq_le_Xq.trans (Xq_le_pCoreOf M)) h1.1, h1.2⟩

theorem coc_one (g : Sp4 F) : C.coc (pCoreOf 2 M).one_mem g = 0 := by
  unfold coc
  rw [C.N.co_eq_zero_iff]
  have e : ⁅C.lift g, (1 : G)⁆ = 1 := by simp [commutatorElement_def]
  show ⁅C.lift g, (1 : G)⁆ ∈ Uq M T L ⊓ Subgroup.centralizer (L : Set G)
  rw [e]
  exact (Uq M T L ⊓ Subgroup.centralizer (L : Set G)).one_mem

theorem mem_of_comm_X₂ {x : G} (hx : x ∈ pCoreOf 2 M)
    (h : ∀ (t : G) (ht : t ∈ L ⊔ pCoreOf 2 M), C.rho ⟨t, ht⟩ ∈ X₂ F → ⁅t, x⁆ ∈ Dq M L) :
    ∃ (u : G) (hu : u ∈ Uq M T L), C.N.co ⟨u, hu⟩ ∈ perp (pt₀ F) ∧ u⁻¹ * x ∈ Dq M L := by
  have : CharP F 2 := charP_of_card_eq_prime_pow C.hF
  obtain ⟨B, m, hBm⟩ := C.exists_cform hx
  have key : ∀ c : F, B * sqrtF c + c * m (.inr 0) = 0 := by
    intro c
    set l := C.lift (transv (e₁ F) c)
    have hl := C.lift_mem (transv (e₁ F) c)
    have hX : C.rho ⟨l, Subgroup.mem_sup_left hl⟩ ∈ X₂ F := by
      rw [C.rho_of_mem_L hl, C.alpha_lift]
      exact mem_X₂_iff.2 ⟨c, rfl⟩
    have hD := h l (Subgroup.mem_sup_left hl) hX
    have h0 : C.coc hx (transv (e₁ F) c) = 0 :=
      (C.N.co_eq_zero_iff _).2 ⟨C.comm_mem_Uq' hx hl, hD.2⟩
    rw [hBm, cform_transv_e₁] at h0
    have h1 := congrFun h0 (.inl 0)
    simpa [e₁] using h1
  obtain ⟨hB, hm⟩ := eq_zero_of_sqrt_mul (by have := C.q_ge_four; omega) key
  obtain ⟨u, hu⟩ := C.N.co_surj m
  refine ⟨u, u.2, ?_, ?_⟩
  · rw [hu, mem_perp_pt₀]
    exact hm
  · have huQ : (u : G)⁻¹ ∈ pCoreOf 2 M :=
      (pCoreOf 2 M).inv_mem ((C.h.Uq_le_Xq.trans (Xq_le_pCoreOf M)) u.2)
    have hux : (u : G)⁻¹ * x ∈ pCoreOf 2 M := (pCoreOf 2 M).mul_mem huQ hx
    refine C.mem_Dq_of_coc_eq_zero hux fun g => ?_
    rw [C.coc_mul_left huQ hx, C.coc_of_mem_Uq ((Uq M T L).inv_mem u.2) huQ, hBm, hB]
    have e : C.N.co ⟨(u : G)⁻¹, (Uq M T L).inv_mem u.2⟩ = -m := by
      rw [← hu, ← C.N.co_inv]
      rfl
    rw [e]
    simp only [S5.cform, zero_smul, zero_add, Matrix.mulVec_neg]
    abel

theorem relIndex_le_card : (Uq M T L ⊔ Dq M L).relIndex (pCoreOf 2 M) ≤ Nat.card F := by
  have : CharP F 2 := charP_of_card_eq_prime_pow C.hF
  have hq : 2 < Nat.card F := by have := C.q_ge_four; omega
  let Bx : ↥(pCoreOf 2 M) → F := fun x => Classical.choose (C.exists_cform x.2)
  have hBx : ∀ x : ↥(pCoreOf 2 M), ∃ m : V4 F, ∀ g, C.coc x.2 g = S5.cform (Bx x) m g :=
    fun x => Classical.choose_spec (C.exists_cform x.2)
  let bHom : ↥(pCoreOf 2 M) →* Multiplicative F :=
    { toFun := fun x => Multiplicative.ofAdd (Bx x)
      map_one' := by
        obtain ⟨m, hm⟩ := hBx 1
        have h0 : ∀ g, S5.cform (Bx 1) m g = S5.cform 0 0 g := by
          intro g
          rw [← hm]
          rw [show C.coc (1 : ↥(pCoreOf 2 M)).2 g = 0 from C.coc_one g]
          simp [S5.cform]
        show Multiplicative.ofAdd (Bx 1) = 1
        rw [eq_of_cform_eq hq h0]
        rfl
      map_mul' := fun x y => by
        obtain ⟨mx, hmx⟩ := hBx x
        obtain ⟨my, hmy⟩ := hBx y
        obtain ⟨mxy, hmxy⟩ := hBx (x * y)
        have h0 : ∀ g, S5.cform (Bx (x * y)) mxy g = S5.cform (Bx x + Bx y) (mx + my) g := by
          intro g
          rw [← hmxy, cform_add, ← hmx, ← hmy]
          exact C.coc_mul_left x.2 y.2 g
        show Multiplicative.ofAdd (Bx (x * y)) =
          Multiplicative.ofAdd (Bx x) * Multiplicative.ofAdd (Bx y)
        rw [eq_of_cform_eq hq h0]
        rfl }
  have hker : bHom.ker ≤ (Uq M T L ⊔ Dq M L).subgroupOf (pCoreOf 2 M) := by
    intro x hx
    have hB0 : Bx x = 0 := by
      have := congrArg Multiplicative.toAdd (MonoidHom.mem_ker.1 hx)
      exact this
    obtain ⟨m, hm⟩ := hBx x
    obtain ⟨u, hu⟩ := C.N.co_surj m
    have huQ : (u : G)⁻¹ ∈ pCoreOf 2 M :=
      (pCoreOf 2 M).inv_mem ((C.h.Uq_le_Xq.trans (Xq_le_pCoreOf M)) u.2)
    have hux : (u : G)⁻¹ * x ∈ pCoreOf 2 M := (pCoreOf 2 M).mul_mem huQ x.2
    have hD : (u : G)⁻¹ * x ∈ Dq M L := by
      refine C.mem_Dq_of_coc_eq_zero hux fun g => ?_
      rw [C.coc_mul_left huQ x.2, C.coc_of_mem_Uq ((Uq M T L).inv_mem u.2) huQ, hm, hB0]
      have e : C.N.co ⟨(u : G)⁻¹, (Uq M T L).inv_mem u.2⟩ = -m := by
        rw [← hu, ← C.N.co_inv]
        rfl
      rw [e]
      simp only [S5.cform, zero_smul, zero_add, Matrix.mulVec_neg]
      abel
    rw [Subgroup.mem_subgroupOf]
    have e : (x : G) = u * ((u : G)⁻¹ * x) := by group
    rw [e]
    exact Subgroup.mul_mem_sup u.2 hD
  have h1 : ((Uq M T L ⊔ Dq M L).subgroupOf (pCoreOf 2 M)).index ≤ bHom.ker.index :=
    Subgroup.index_antitone hker
  have h2 : bHom.ker.index = Nat.card bHom.range := Subgroup.index_ker bHom
  have h3 : Nat.card bHom.range ≤ Nat.card F := by
    calc Nat.card bHom.range ≤ Nat.card (Multiplicative F) := Subgroup.card_le_card_group _
      _ = Nat.card F := rfl
  calc (Uq M T L ⊔ Dq M L).relIndex (pCoreOf 2 M)
      = ((Uq M T L ⊔ Dq M L).subgroupOf (pCoreOf 2 M)).index := rfl
    _ ≤ Nat.card F := by omega

end Cfg

end CFSG.Quasithin.MS93.S37
