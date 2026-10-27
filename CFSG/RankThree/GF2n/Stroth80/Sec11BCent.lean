module

public import CFSG.RankThree.GF2n.Stroth80.Sec11BStmt
public import CFSG.RankThree.GF2n.Stroth80.Sec12CaseVICoord

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank Matrix
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem centDvd_of_core (hc : Ctx M Q Z B) {n : ℕ} (hw : Width Q Z n) (hn : 2 < n)
    (hcore : CaseVICore M Q Z (Lgen M (LB M Q B)) n) :
    CentDvd M Q Z (Lgen M (LB M Q B)) := by
  classical
  obtain ⟨K, _, _, _, γ, M₀, h⟩ := stroth_globalModelData hc.hyp
  obtain ⟨φ, hφπ, hφker, hφiso⟩ := exists_actionHom_H0 hc.hyp h
  set S := Lgen M (LB M Q B) with hS
  have hSH : S ≤ H0 M Z := Lgen_le_H0 hc
  obtain ⟨F, _, _, hFcard, φ', hrange, hker, V₁, V₂, hZV₁, hV₁Q, hZV₂, hV₂Q, hinf, hsup, hact₁,
    hact₂, hx⟩ := hcore
  have hn3 : 3 ≤ n := hn
  have hq4 : 4 ≤ Nat.card Z := hc.hyp.q4
  obtain ⟨Φ, hΦ, -, -⟩ := exists_equivariant_coord M₀ (φ.comp (Subgroup.inclusion hSH))
    (fun s x hx => hφπ ⟨s, hSH s.2⟩ x hx) hZV₁ hV₁Q hZV₂ hV₂Q hinf hsup φ' hact₁ hact₂
  obtain ⟨C, -⟩ := exists_natDualCoord_of_equivariant (φ.comp (Subgroup.inclusion hSH)) φ'
    hn3 hrange (by rw [h.card, hFcard]) Φ hΦ
  haveI : CharP F 2 := charP_of_injective_ringHom C.θ₁.toRingHom.injective 2
  have hK : ∃ c : K, c ≠ 0 ∧ c ^ 2 ≠ 1 :=
    exists_ne_zero_sq_ne_one_of_two_lt_card K (by rw [h.card]; omega)
  let Qd : QuadDatum K M₀.E := quadDatumOfModel M₀
  have hQρ : ∀ (g : ↥S) (e : M₀.E), Qd.Qf ((φ.comp (Subgroup.inclusion hSH)) g e) = Qd.Qf e :=
    fun g e => hφiso _ e
  let Cc : Subgroup G :=
    { carrier := {y | y ∈ H0 M Z ∧ ∀ x ∈ S, ⁅y, x⁆ ∈ Q}
      mul_mem' := fun {u v} hu hv => by
        refine ⟨(H0 M Z).mul_mem hu.1 hv.1, fun x hx => ?_⟩
        have e : ⁅u * v, x⁆ = (u * ⁅v, x⁆ * u⁻¹) * ⁅u, x⁆ := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact Q.mul_mem ((Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hu.1.1) _).mp
          (hv.2 x hx)) (hu.2 x hx)
      one_mem' := ⟨(H0 M Z).one_mem, fun x _ => by simp [commutatorElement_def]⟩
      inv_mem' := fun {u} hu => by
        refine ⟨(H0 M Z).inv_mem hu.1, fun x hx => ?_⟩
        have e : ⁅u⁻¹, x⁆ = u⁻¹ * ⁅u, x⁆⁻¹ * u := by
          simp only [commutatorElement_def]
          group
        rw [e]
        have h1 := (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 (M.inv_mem hu.1.1)) _).mp
          (Q.inv_mem (hu.2 x hx))
        simpa using h1 }
  have hCH : Cc ≤ H0 M Z := fun y hy => hy.1
  have hQC : Q ≤ Cc := fun y hy =>
    ⟨⟨hc.hyp.Q_normal.1 hy, Subgroup.mem_centralizer_iff.mpr fun z hz =>
      hc.hyp.toHyp79.V_central hz hy⟩, fun x hx => by
      have hxM : x ∈ M := (hSH hx).1
      have e : ⁅y, x⁆ = y * (x * y⁻¹ * x⁻¹) := by
        rw [commutatorElement_def]
        group
      rw [e]
      exact Q.mul_mem hy ((Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hxM) y⁻¹).mp
        (Q.inv_mem hy))⟩
  let T : ↥Cc → (M₀.E ≃ₗ[K] M₀.E) := fun y => φ ⟨y, hCH y.2⟩
  have hTmul : ∀ y y' : ↥Cc, T (y * y') = T y * T y' := fun y y' =>
    map_mul φ ⟨y, hCH y.2⟩ ⟨y', hCH y'.2⟩
  have hT1 : T 1 = 1 := map_one φ
  have hTker : ∀ y : ↥Cc, T y = 1 ↔ (y : G) ∈ Q := fun y => hφker ⟨y, hCH y.2⟩
  have hTcomm : ∀ (y : ↥Cc) (s : ↥S) (e : M₀.E),
      T y (φ ⟨s, hSH s.2⟩ e) = φ ⟨s, hSH s.2⟩ (T y e) := by
    intro y s e
    have h1 : φ ⁅(⟨y, hCH y.2⟩ : ↥(H0 M Z)), ⟨s, hSH s.2⟩⁆ = 1 := by
      rw [hφker]
      show ⁅(y : G), (s : G)⁆ ∈ Q
      exact y.2.2 s s.2
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h1
    have := congrArg (fun f : M₀.E ≃ₗ[K] M₀.E => f e) h1
    simpa [LinearEquiv.mul_apply] using this
  let P : ↥Cc → ((Fin n → F) × (Fin n → F) →+ (Fin n → F) × (Fin n → F)) := fun y =>
    AddMonoidHom.mk' (fun p => C.Ψ (T y (C.Ψ.symm p))) (fun p q => by
      rw [map_add, map_add, map_add])
  have hP : ∀ (y : ↥Cc) (p : (Fin n → F) × (Fin n → F)), P y p = C.Ψ (T y (C.Ψ.symm p)) :=
    fun y p => rfl
  have hequiv : ∀ y : ↥Cc, ∀ g ∈ StatedSL n F, ∀ p : (Fin n → F) × (Fin n → F),
      P y ((g : Matrix (Fin n) (Fin n) F) *ᵥ p.1,
          ((tinvGL g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *ᵥ p.2) =
        ((g : Matrix (Fin n) (Fin n) F) *ᵥ (P y p).1,
          ((tinvGL g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *ᵥ (P y p).2) := by
    intro y g hg p
    obtain ⟨s, hs⟩ := NatDualCoord.exists_eq_of_mem_statedSL hrange hg
    have h1 := C.act s (C.Ψ.symm p)
    rw [hs, C.Ψ.apply_symm_apply] at h1
    have h2 := C.act s (T y (C.Ψ.symm p))
    rw [hs] at h2
    have h3 : T y ((φ.comp (Subgroup.inclusion hSH)) s (C.Ψ.symm p)) =
        (φ.comp (Subgroup.inclusion hSH)) s (T y (C.Ψ.symm p)) := hTcomm y s _
    rw [hP y, ← h1, AddEquiv.symm_apply_apply, h3, h2]
    rfl
  have hsc : ∀ y : ↥Cc, ∃ a b : F, ∀ p, P y p = (a • p.1, b • p.2) := fun y =>
    exists_scalars_of_equivariant hn3 (P y) (hequiv y)
  choose a b hab using hsc
  let i0 : Fin n := ⟨0, by omega⟩
  let v : Fin n → F := Pi.single i0 1
  have hv : v i0 = 1 := Pi.single_eq_same i0 1
  have hP1 : ∀ p, P 1 p = p := fun p => by rw [hP, hT1]; simp
  have hPmul : ∀ (y y' : ↥Cc) (p : (Fin n → F) × (Fin n → F)), P (y * y') p = P y (P y' p) :=
    fun y y' p => by
      rw [hP (y * y'), hTmul, hP y (P y' p), hP y' p, AddEquiv.symm_apply_apply]
      rfl
  have ha1 : a 1 = 1 := by
    have h1 := hab 1 (v, 0)
    rw [hP1] at h1
    have h2 := congrArg (fun q => q.1 i0) h1
    simp [hv] at h2
    exact h2.symm
  have hamul : ∀ y y' : ↥Cc, a (y * y') = a y * a y' := by
    intro y y'
    have h1 := hab (y * y') (v, 0)
    rw [hPmul, hab y' (v, 0), hab y] at h1
    have h2 := congrArg (fun q => q.1 i0) h1
    simp [hv, smul_smul] at h2
    exact h2.symm
  let ahom : ↥Cc →* F := { toFun := a, map_one' := ha1, map_mul' := hamul }
  let ahomU : ↥Cc →* Fˣ := ahom.toHomUnits
  have hTinl : ∀ (y : ↥Cc) (x : Fin n → F), T y (C.inl x) = C.inl (a y • x) := by
    intro y x
    apply C.Ψ.injective
    rw [C.Ψ_inl]
    have h1 := hab y (x, 0)
    rw [hP] at h1
    have e : C.Ψ.symm (x, 0) = C.inl x := rfl
    rw [e] at h1
    simpa using h1
  have hTinr : ∀ (y : ↥Cc) (w : Fin n → F), T y (C.inr w) = C.inr (b y • w) := by
    intro y w
    apply C.Ψ.injective
    rw [C.Ψ_inr]
    have h1 := hab y (0, w)
    rw [hP] at h1
    have e : C.Ψ.symm (0, w) = C.inr w := rfl
    rw [e] at h1
    simpa using h1
  have hBiso : ∀ (y : ↥Cc) (e f : M₀.E), M₀.B (T y e) (T y f) = M₀.B e f := fun y e f =>
    Tim79.QuadModel.B_iso (T := (T y : M₀.E →ₗ[K] M₀.E)) (fun e => hφiso ⟨y, hCH y.2⟩ e) e f
  have hb1 : ∀ y : ↥Cc, a y = 1 → b y = 1 := by
    intro y hy
    have hz : ∀ x w : Fin n → F, M₀.B (C.inl x) (C.inr (b y • w - w)) = 0 := by
      intro x w
      have h1 := hBiso y (C.inl x) (C.inr w)
      rw [hTinl, hTinr, hy, one_smul] at h1
      rw [map_sub, map_sub, h1, sub_self]
    have h2 : ∀ x w : Fin n → F, (b y • w - w) ⬝ᵥ x = 0 := fun x w =>
      C.dot_eq_zero_of_B_inl_inr_eq_zero Qd (by omega) hrange hQρ hK (hz x w)
    have h3 := h2 (Pi.single i0 1) (Pi.single i0 1)
    simp only [dotProduct_single, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.single_eq_same,
      mul_one] at h3
    exact sub_eq_zero.mp h3
  have hkerQ : ahomU.ker = Q.subgroupOf Cc := by
    ext y
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    have hcoe : ahomU y = 1 ↔ a y = 1 := by
      rw [Units.ext_iff]
      rfl
    rw [hcoe]
    constructor
    · intro ha
      have hb := hb1 y ha
      rw [← hTker]
      refine LinearEquiv.ext fun e => ?_
      apply C.Ψ.injective
      have h1 := hab y (C.Ψ e)
      rw [hP, AddEquiv.symm_apply_apply, ha, hb] at h1
      simpa using h1
    · intro hyQ
      have hT : T y = 1 := (hTker y).mpr hyQ
      have h1 := hab y (v, 0)
      rw [hP, hT] at h1
      have h2 := congrArg (fun q => q.1 i0) h1
      simp [hv] at h2
      exact h2.symm
  have hcardC : Nat.card Cc = Nat.card Q * Nat.card ahomU.range := by
    have h1 := Subgroup.card_mul_index ahomU.ker
    rw [Subgroup.index_ker, hkerQ] at h1
    rw [← h1]
    congr 1
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQC).toEquiv
  refine ⟨Cc, hQC, hCH, fun y => Iff.rfl, ?_⟩
  rw [hcardC]
  refine Nat.mul_dvd_mul_left _ ?_
  have h1 := Subgroup.card_subgroup_dvd_card ahomU.range
  rwa [Nat.card_units F, hFcard] at h1

theorem caseVI_of_core (hc : Ctx M Q Z B) {n : ℕ} (hw : Width Q Z n) (hn : 2 < n)
    (hcore : CaseVICore M Q Z (Lgen M (LB M Q B)) n) : CaseVI M Q Z (Lgen M (LB M Q B)) :=
  CaseVI.of_core hcore (centDvd_of_core hc hw hn hcore)

end CFSG.RankThree.GF2n.Stroth80
