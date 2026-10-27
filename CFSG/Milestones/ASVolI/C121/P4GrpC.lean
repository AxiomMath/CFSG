module

public import CFSG.Milestones.ASVolI.C121.P4GrpB

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {Ω : Type} [Group Ω] [Finite Ω]

namespace burnsideC121_p4_Hyp

variable {X L T R V Y : Subgroup Ω} (h : burnsideC121_p4_Hyp X L T R V Y)
include h

@[expose] noncomputable def eps :
    ↥((baum T ⊔ pCoreOf 2 X) ⊔ Y) →* ↥(autI h.hV (Y ⊔ thompsonJ R)) :=
  (convHom h.hV _ h.H_le_NV).codRestrict (autI h.hV (Y ⊔ thompsonJ R)) (fun x => by
    rw [← h.autI_H, ← range_convHom h.hV _ h.H_le_NV]
    exact ⟨x, rfl⟩)

theorem eps_apply (x : ↥((baum T ⊔ pCoreOf 2 X) ⊔ Y)) :
    ((h.eps x : ↥(autI h.hV (Y ⊔ thompsonJ R))) : MulAut (IntMod V h.hV)) =
      convI h.hV ⟨x, h.H_le_NV x.2⟩ := rfl

theorem eps_surjective : Function.Surjective h.eps := by
  intro φ
  have hφ : (φ : MulAut (IntMod V h.hV)) ∈ autI h.hV ((baum T ⊔ pCoreOf 2 X) ⊔ Y) := by
    rw [h.autI_H]; exact φ.2
  rw [← range_convHom h.hV _ h.H_le_NV] at hφ
  obtain ⟨x, hx⟩ := hφ
  exact ⟨x, Subtype.ext hx⟩

@[expose] noncomputable def phi2 : ↥((baum T ⊔ pCoreOf 2 X) ⊔ Y) →*
    ↥(autI h.hV (Y ⊔ thompsonJ R)) ⧸ CFSG.pCore 2 ↥(autI h.hV (Y ⊔ thompsonJ R)) :=
  (QuotientGroup.mk' _).comp h.eps

theorem phi2_surjective : Function.Surjective h.phi2 :=
  (QuotientGroup.mk'_surjective _).comp h.eps_surjective

@[expose] noncomputable def K2 : Subgroup Ω := h.phi2.ker.map (Subgroup.subtype _)

theorem K2_le_H : h.K2 ≤ (baum T ⊔ pCoreOf 2 X) ⊔ Y := Subgroup.map_subtype_le _

theorem K2_subgroupOf : h.K2.subgroupOf ((baum T ⊔ pCoreOf 2 X) ⊔ Y) = h.phi2.ker :=
  A4.subgroupOf_map_subtype' _ _

theorem mem_K2 (x : ↥((baum T ⊔ pCoreOf 2 X) ⊔ Y)) :
    (x : Ω) ∈ h.K2 ↔ h.eps x ∈ CFSG.pCore 2 ↥(autI h.hV (Y ⊔ thompsonJ R)) := by
  have : (x : Ω) ∈ h.K2 ↔ x ∈ h.phi2.ker := by
    rw [← h.K2_subgroupOf, Subgroup.mem_subgroupOf]
  rw [this, MonoidHom.mem_ker]
  exact QuotientGroup.eq_one_iff _

theorem K2_two : IsPGroup 2 ↥h.K2 := by
  intro g
  obtain ⟨x, hx, hxg⟩ := Subgroup.mem_map.1 g.2
  have hxg' : (x : Ω) = g := hxg
  have hx' : h.eps x ∈ CFSG.pCore 2 ↥(autI h.hV (Y ⊔ thompsonJ R)) := by
    rw [← h.mem_K2, hxg']
    exact g.2
  obtain ⟨k, hk⟩ := CFSG.pCore_isPGroup (p := 2) ⟨h.eps x, hx'⟩
  have hk' : h.eps (x ^ 2 ^ k) = 1 := by
    rw [map_pow]
    exact congrArg Subtype.val hk
  have hC : ((x : Ω) ^ 2 ^ k) ∈ ((baum T ⊔ pCoreOf 2 X) ⊔ Y) ⊓
      Subgroup.centralizer (V : Set Ω) := by
    refine ⟨Subgroup.pow_mem _ x.2 _, ?_⟩
    have h1 := congrArg Subtype.val hk'
    rw [h.eps_apply] at h1
    have h2 := (convI_eq_one_iff h.hV _).1 h1
    simpa using h2
  rw [h.H_CV] at hC
  obtain ⟨m, hm⟩ := h.Q_two ⟨_, hC⟩
  refine ⟨k + m, Subtype.ext ?_⟩
  have hm' : ((x : Ω) ^ 2 ^ k) ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
  simp only [Subgroup.coe_pow, Subgroup.coe_one]
  rw [← hxg', pow_add, pow_mul, hm']

theorem H_le_NK2 : (baum T ⊔ pCoreOf 2 X) ⊔ Y ≤ Subgroup.normalizer (h.K2 : Set Ω) := by
  have hn : (h.K2.subgroupOf ((baum T ⊔ pCoreOf 2 X) ⊔ Y)).Normal := by
    rw [h.K2_subgroupOf]
    infer_instance
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer h.K2_le_H).1 hn

theorem K2_le_O2H : h.K2 ≤ pCoreOf 2 ((baum T ⊔ pCoreOf 2 X) ⊔ Y) :=
  le_pCoreOf_of_le_normalizer 2 h.K2_le_H h.H_le_NK2 h.K2_two

variable {W : Subgroup Ω} (hWm : IsTwoReducedIn ((baum T ⊔ pCoreOf 2 X) ⊔ Y) W ∧
  ∀ W' : Subgroup Ω, IsTwoReducedIn ((baum T ⊔ pCoreOf 2 X) ⊔ Y) W' → W' ≤ W)
include hWm

omit h in
theorem elemW : IsElemAbelian 2 W := hWm.1.2.2.1

theorem O2H_le_CW : pCoreOf 2 ((baum T ⊔ pCoreOf 2 X) ⊔ Y) ≤ Subgroup.centralizer (W : Set Ω) :=
  pCoreOf_le_centralizer_of_isTwoReducedIn hWm.1

theorem K2_le_CW : h.K2 ≤ Subgroup.centralizer (W : Set Ω) := h.K2_le_O2H.trans (h.O2H_le_CW hWm)

theorem ZV_le_W : V ⊓ Subgroup.centralizer (thompsonJ R : Set Ω) ≤ W := by
  set Z := V ⊓ Subgroup.centralizer (thompsonJ R : Set Ω) with hZ
  have hR0C : baum T ⊔ pCoreOf 2 X ≤ Subgroup.centralizer (Z : Set Ω) := by
    have hJZ : thompsonJ R ≤ Subgroup.centralizer (Z : Set Ω) :=
      Subgroup.le_centralizer_iff.1 inf_le_right
    have hCZ : Subgroup.centralizer (V : Set Ω) ≤ Subgroup.centralizer (Z : Set Ω) :=
      Subgroup.centralizer_le inf_le_left
    refine sup_le (h.S_le_JC.trans (sup_le hJZ (inf_le_right.trans hCZ))) (h.Q_le_CV.trans hCZ)
  have hZ1 : Z ≤ quasithinOmegaOneCenter (baum T ⊔ pCoreOf 2 X) := by
    intro z hz
    refine Subgroup.subset_closure ⟨⟨Subgroup.mem_sup_right (h.V_le_Q hz.1), ?_⟩,
      h.hV.2 z hz.1⟩
    exact Subgroup.le_centralizer_iff.1 hR0C hz
  have hZ2 : Z ≤ pCoreOf 2 ((baum T ⊔ pCoreOf 2 X) ⊔ Y) :=
    (inf_le_left.trans h.V_le_Q).trans h.Q_le_O2H
  have hred := B2_13_conjClosure h.sylow_R0H hZ1 hZ2
  exact (le_conjClosure Z _).trans (hWm.2 _ hred)

theorem WY_ne_bot : ⁅W, Y⁆ ≠ ⊥ := by
  intro hb
  apply h.hZY
  rw [eq_bot_iff, ← hb]
  exact Subgroup.commutator_mono (h.ZV_le_W hWm) le_rfl

theorem Y_not_le_CW : ¬ Y ≤ Subgroup.centralizer (W : Set Ω) := by
  intro hY
  apply h.WY_ne_bot hWm
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  exact Subgroup.le_centralizer_iff.1 hY

theorem CW_le_K2
    (hG : ∀ N : Subgroup (↥(autI h.hV (Y ⊔ thompsonJ R)) ⧸
        CFSG.pCore 2 ↥(autI h.hV (Y ⊔ thompsonJ R))),
      N.Normal → N = ⊥ ∨ ∀ τ, Odd (orderOf τ) → τ ∈ N) :
    ((baum T ⊔ pCoreOf 2 X) ⊔ Y) ⊓ Subgroup.centralizer (W : Set Ω) ≤ h.K2 := by
  set H := (baum T ⊔ pCoreOf 2 X) ⊔ Y with hHdef
  set N : Subgroup ↥H := (H ⊓ Subgroup.centralizer (W : Set Ω)).subgroupOf H with hN
  have hNn : N.Normal := by
    have hHW : H ≤ Subgroup.normalizer ((H ⊓ Subgroup.centralizer (W : Set Ω) : Subgroup Ω) :
        Set Ω) :=
      B2F.le_normalizer_inf Subgroup.le_normalizer (B2F.le_normalizer_centralizer hWm.1.2.1)
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).2 hHW
  have hNmap : (N.map h.phi2).Normal := Subgroup.Normal.map hNn h.phi2 h.phi2_surjective
  rcases hG _ hNmap with hb | hodd
  · intro x hx
    have hxN : (⟨x, hx.1⟩ : ↥H) ∈ N := hx
    have h1 : h.phi2 ⟨x, hx.1⟩ ∈ N.map h.phi2 := Subgroup.mem_map_of_mem _ hxN
    rw [hb, Subgroup.mem_bot] at h1
    have h2 : (⟨x, hx.1⟩ : ↥H) ∈ h.phi2.ker := h1
    rw [← h.K2_subgroupOf, Subgroup.mem_subgroupOf] at h2
    exact h2
  · exfalso
    apply h.Y_not_le_CW hWm
    rw [h.hYperf]
    refine (Subgroup.closure_le _).2 ?_
    rintro y ⟨hyY, hyo⟩
    have hyH : y ∈ H := h.Y_le_H hyY
    have h1 : Odd (orderOf (h.phi2 ⟨y, hyH⟩)) := by
      have h2 : orderOf (⟨y, hyH⟩ : ↥H) = orderOf y := Subgroup.orderOf_mk y hyH
      exact (h2 ▸ hyo).of_dvd_nat (orderOf_map_dvd h.phi2 _)
    obtain ⟨n, hn, hne⟩ := Subgroup.mem_map.1 (hodd _ h1)
    have h3 : n⁻¹ * ⟨y, hyH⟩ ∈ h.phi2.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hne, inv_mul_cancel]
    rw [← h.K2_subgroupOf, Subgroup.mem_subgroupOf] at h3
    have h4 : (n : Ω)⁻¹ * y ∈ Subgroup.centralizer (W : Set Ω) := by
      simpa using h.K2_le_CW hWm h3
    have h5 : (n : Ω) ∈ Subgroup.centralizer (W : Set Ω) := (Subgroup.mem_subgroupOf.1 hn).2
    have : y = (n : Ω) * ((n : Ω)⁻¹ * y) := by group
    rw [SetLike.mem_coe, this]
    exact Subgroup.mul_mem _ h5 h4

theorem CW_eq_K2
    (hG : ∀ N : Subgroup (↥(autI h.hV (Y ⊔ thompsonJ R)) ⧸
        CFSG.pCore 2 ↥(autI h.hV (Y ⊔ thompsonJ R))),
      N.Normal → N = ⊥ ∨ ∀ τ, Odd (orderOf τ) → τ ∈ N) :
    ((baum T ⊔ pCoreOf 2 X) ⊔ Y) ⊓ Subgroup.centralizer (W : Set Ω) = h.K2 :=
  le_antisymm (h.CW_le_K2 hWm hG) (le_inf h.K2_le_H (h.K2_le_CW hWm))

theorem YCW
    (hG : ∀ N : Subgroup (↥(autI h.hV (Y ⊔ thompsonJ R)) ⧸
        CFSG.pCore 2 ↥(autI h.hV (Y ⊔ thompsonJ R))),
      N.Normal → N = ⊥ ∨ ∀ τ, Odd (orderOf τ) → τ ∈ N) :
    Y ⊓ Subgroup.centralizer (W : Set Ω) = pCoreOf 2 Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := (baum T ⊔ pCoreOf 2 X) ⊔ Y with hHdef
  apply le_antisymm
  · have h1 : Y ⊓ Subgroup.centralizer (W : Set Ω) ≤ Y ⊓ pCoreOf 2 H :=
      le_inf inf_le_left ((inf_le_inf_right _ h.Y_le_H).trans ((h.CW_le_K2 hWm hG).trans
        h.K2_le_O2H))
    refine h1.trans (le_pCoreOf_of_le_normalizer 2 inf_le_left ?_ ?_)
    · exact B2F.le_normalizer_inf Subgroup.le_normalizer
        (h.Y_le_H.trans (le_normalizer_pCoreOf 2 H))
    · exact (pCoreOf_isPGroup 2 H).to_le inf_le_right
  · refine le_inf (pCoreOf_le 2 Y) ((le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 Y).trans
      h.Y_le_H) (h.H_le_NY.trans (normalizer_le_normalizer_pCoreOf 2 Y))
      (pCoreOf_isPGroup 2 Y)).trans (h.O2H_le_CW hWm))

theorem iota
    (hG : ∀ N : Subgroup (↥(autI h.hV (Y ⊔ thompsonJ R)) ⧸
        CFSG.pCore 2 ↥(autI h.hV (Y ⊔ thompsonJ R))),
      N.Normal → N = ⊥ ∨ ∀ τ, Odd (orderOf τ) → τ ∈ N) :
    Nonempty (↥(autI (elemW hWm) ((baum T ⊔ pCoreOf 2 X) ⊔ Y)) ≃*
      (↥(autI h.hV (Y ⊔ thompsonJ R)) ⧸ CFSG.pCore 2 ↥(autI h.hV (Y ⊔ thompsonJ R)))) := by
  set H := (baum T ⊔ pCoreOf 2 X) ⊔ Y with hHdef
  have hHW : H ≤ Subgroup.normalizer (W : Set Ω) := hWm.1.2.1
  let φ₁ : ↥H →* ↥(autI (elemW hWm) H) :=
    (convHom (elemW hWm) H hHW).codRestrict (autI (elemW hWm) H) (fun x => by
      rw [← range_convHom (elemW hWm) H hHW]
      exact ⟨x, rfl⟩)
  have hφ₁ : Function.Surjective φ₁ := by
    intro φ
    have hφ : (φ : MulAut (IntMod W (elemW hWm))) ∈ (convHom (elemW hWm) H hHW).range := by
      rw [range_convHom]; exact φ.2
    obtain ⟨x, hx⟩ := hφ
    exact ⟨x, Subtype.ext hx⟩
  have hker : φ₁.ker = h.phi2.ker := by
    have h1 : φ₁.ker = (convHom (elemW hWm) H hHW).ker := by
      ext x
      simp only [MonoidHom.mem_ker]
      constructor
      · intro hx
        exact congrArg Subtype.val hx
      · intro hx
        exact Subtype.ext hx
    rw [h1, ker_convHom, h.CW_eq_K2 hWm hG, h.K2_subgroupOf]
  exact ⟨(QuotientGroup.quotientKerEquivOfSurjective φ₁ hφ₁).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hker).trans
      (QuotientGroup.quotientKerEquivOfSurjective h.phi2 h.phi2_surjective))⟩

theorem J_not_le_CW
    (hG : ∀ N : Subgroup (↥(autI h.hV (Y ⊔ thompsonJ R)) ⧸
        CFSG.pCore 2 ↥(autI h.hV (Y ⊔ thompsonJ R))),
      N.Normal → N = ⊥ ∨ ∀ τ, Odd (orderOf τ) → τ ∈ N)
    (heven : Even (Nat.card (↥(autI h.hV (Y ⊔ thompsonJ R)) ⧸
      CFSG.pCore 2 ↥(autI h.hV (Y ⊔ thompsonJ R))))) :
    ¬ thompsonJ R ≤ Subgroup.centralizer (W : Set Ω) := by
  intro hJ
  set P := autI h.hV (Y ⊔ thompsonJ R) with hP
  have hJK : thompsonJ R ≤ h.K2 := (le_inf h.J_le_H hJ).trans (h.CW_le_K2 hWm hG)
  have hle : (autI h.hV (thompsonJ R)).subgroupOf P ≤ CFSG.pCore 2 ↥P := by
    intro φ hφ
    rw [Subgroup.mem_subgroupOf] at hφ
    obtain ⟨g, hgJ, hg⟩ := (mem_autI h.hV).1 hφ
    have hgH : (g : Ω) ∈ (baum T ⊔ pCoreOf 2 X) ⊔ Y := h.J_le_H hgJ
    have h1 := (h.mem_K2 ⟨g, hgH⟩).1 (hJK hgJ)
    have h2 : h.eps ⟨g, hgH⟩ = φ := by
      apply Subtype.ext
      rw [h.eps_apply, ← hg]
    rw [h2] at h1
    exact h1
  have hdvd := Subgroup.index_dvd_of_le hle
  have hodd := h.hsyl.2.2
  have hcard : Nat.card (↥P ⧸ CFSG.pCore 2 ↥P) = (CFSG.pCore 2 ↥P).index := rfl
  rw [hcard] at heven
  exact hodd (heven.two_dvd.trans hdvd)

theorem isFF
    (hG : ∀ N : Subgroup (↥(autI h.hV (Y ⊔ thompsonJ R)) ⧸
        CFSG.pCore 2 ↥(autI h.hV (Y ⊔ thompsonJ R))),
      N.Normal → N = ⊥ ∨ ∀ τ, Odd (orderOf τ) → τ ∈ N)
    (heven : Even (Nat.card (↥(autI h.hV (Y ⊔ thompsonJ R)) ⧸
      CFSG.pCore 2 ↥(autI h.hV (Y ⊔ thompsonJ R))))) :
    IsFFModule (autI (elemW hWm) ((baum T ⊔ pCoreOf 2 X) ⊔ Y)) := by
  have hJ := h.J_not_le_CW hWm hG heven
  obtain ⟨A, hA, hAC⟩ : ∃ A, IsMaxElemAbelian R A ∧ ¬ A ≤ Subgroup.centralizer (W : Set Ω) := by
    by_contra hc
    push Not at hc
    exact hJ (iSup₂_le fun A hA => hc A hA)
  have hWR : W ≤ R :=
    (le_pCoreOf_of_isTwoReducedIn hWm.1).trans (h.O2H_le_R0.trans (sup_le h.S_le_R h.hQR))
  exact isFFModule_autOn (elemW hWm) hWR hWm.1.2.1 ((B6.le_thompsonJ hA).trans h.J_le_H) hA hAC

theorem O2_bot : ∀ Q : Subgroup (MulAut (IntMod W (elemW hWm))),
    Q ≤ autI (elemW hWm) ((baum T ⊔ pCoreOf 2 X) ⊔ Y) →
    (Q.subgroupOf (autI (elemW hWm) ((baum T ⊔ pCoreOf 2 X) ⊔ Y))).Normal → IsPGroup 2 ↥Q →
      Q = ⊥ := by
  intro Q hQ hQn hQ2
  have h1 := C124.pCoreOf_autI_eq_bot (elemW hWm) hWm.1
  have h2 : Q ≤ pCoreOf 2 (autI (elemW hWm) ((baum T ⊔ pCoreOf 2 X) ⊔ Y)) :=
    le_pCoreOf 2 hQ hQn hQ2
  rw [h1] at h2
  exact le_bot_iff.1 h2

end burnsideC121_p4_Hyp

end CFSG.Quasithin
