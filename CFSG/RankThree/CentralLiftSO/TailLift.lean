module

public import CFSG.RankThree.CentralLiftSO.TailRho
import CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeylLift

public section

namespace CFSG.RankThree.CentralLiftSO.TailO

open QuadraticMap Matrix CFSG.ClassicalGroups.Orthogonal CFSG.LieType.CentralExt
open CFSG.RankThree.CentralLift
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
open CFSG.LocalAnalysis.ComponentInitial.NormTail
open CFSG.LocalAnalysis.ComponentInitial.NormTail renaming torusMap → tMap
open CFSG.LocalAnalysis.ComponentInitial (orthElementaryGroup)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl (sl2W sl2ConjDiag sl2Diag
  coe_sl2Diag sl2W_mul_sl2W sl2W_mul_sl2Diag sl2ConjDiag_inv_sl2W sl2ConjDiag_neg_one_sl2W
  conj_comp_eq)
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit (sl2ConjDiag_sl2Diag sl2Swap
  sl2Swap_sl2Diag neg_one_eq_sl2Diag)

section LiftOf

variable {E G H : Type*} [Group E] [Group G] [Group H]

open _root_.Classical in
@[expose] noncomputable def liftOf (π : E →* G) (φ : H →* G) : H →* E :=
  if h : ∃ ψ : H →* E, π.comp ψ = φ then h.choose else 1

theorem comp_liftOf {π : E →* G} {φ : H →* G} (h : ∃ ψ : H →* E, π.comp ψ = φ) :
    π.comp (liftOf π φ) = φ := by
  classical
  rw [liftOf, dite_eq_left h]
  exact h.choose_spec

variable [Finite E] {π : E →* G} {F F' : Type} [Field F] [Finite F] [Field F'] [Finite F']

theorem liftOf_eq_sl2Lift (hF : ringChar F ≠ 2) (hπ : IsLargeCentralExt π)
    (α : SpecialLinearGroup (Fin 2) F →* G) : liftOf π α = sl2Lift π α :=
  eq_sl2Lift_large hF hπ (comp_liftOf (existsUnique_lift_large hF hπ α).exists)

theorem map_liftOf (hF : ringChar F ≠ 2) (hπ : IsLargeCentralExt π)
    (α : SpecialLinearGroup (Fin 2) F →* G) (g : SpecialLinearGroup (Fin 2) F) :
    π (liftOf π α g) = α g := by
  rw [liftOf_eq_sl2Lift hF hπ]
  exact map_sl2Lift_large hF hπ α g

theorem liftOf_comp (hF : ringChar F ≠ 2) (hF' : ringChar F' ≠ 2) (hπ : IsLargeCentralExt π)
    (α : SpecialLinearGroup (Fin 2) F →* G)
    (γ : SpecialLinearGroup (Fin 2) F' →* SpecialLinearGroup (Fin 2) F) :
    (liftOf π α).comp γ = liftOf π (α.comp γ) := by
  rw [liftOf_eq_sl2Lift hF hπ, liftOf_eq_sl2Lift hF' hπ]
  exact sl2Lift_comp_large hF hF' hπ α γ

theorem conj_liftOf_apply (hF : ringChar F ≠ 2) (hπ : IsLargeCentralExt π) {e : E}
    {α β : SpecialLinearGroup (Fin 2) F →* G}
    {γ : SpecialLinearGroup (Fin 2) F →* SpecialLinearGroup (Fin 2) F}
    (h : (MulAut.conj (π e)).toMonoidHom.comp α = β.comp γ) (g : SpecialLinearGroup (Fin 2) F) :
    e * liftOf π α g * e⁻¹ = liftOf π β (γ g) := by
  rw [liftOf_eq_sl2Lift hF hπ, liftOf_eq_sl2Lift hF hπ, conj_sl2Lift_apply_large hF hπ α e g, h,
    ← sl2Lift_comp_large hF hF hπ]
  rfl

theorem commute_liftOf (hF : ringChar F ≠ 2) (hF' : ringChar F' ≠ 2) (hπ : IsLargeCentralExt π)
    (α : SpecialLinearGroup (Fin 2) F →* G) (α' : SpecialLinearGroup (Fin 2) F' →* G)
    (h : ∀ g g', Commute (α g) (α' g')) (g : SpecialLinearGroup (Fin 2) F)
    (g' : SpecialLinearGroup (Fin 2) F') : Commute (liftOf π α g) (liftOf π α' g') := by
  rw [liftOf_eq_sl2Lift hF hπ, liftOf_eq_sl2Lift hF' hπ]
  exact commute_sl2Lift_large hF hF' hπ α α' h g g'

end LiftOf

variable {K L : Type} [Field K] [Field L] [Algebra K L] (T : NormTailData K L) {r : ℕ}
  {E : Type*} [Group E]

section Defs

variable (π : E →* G0 T r)

@[expose] noncomputable def rhoLift (i : Fin r) : SpecialLinearGroup (Fin 2) L →* E :=
  liftOf π (rhoOG T i)

@[expose] noncomputable def etaLift {i j : Fin r} (hij : i ≠ j) :
    SpecialLinearGroup (Fin 2) K →* E :=
  liftOf π (etaG T hij)

@[expose] noncomputable def tauLift (i : Fin r) : Lˣ →* E :=
  (rhoLift T π i).comp sl2Diag

@[expose] noncomputable def hLift {i j : Fin r} (hij : i ≠ j) : Kˣ →* E :=
  (etaLift T π hij).comp sl2Diag

@[expose] noncomputable def wLift (i : Fin r) : E :=
  rhoLift T π i sl2W

@[expose] def hGens : Set E :=
  {x | (∃ (i : Fin r) (s : Lˣ), tauLift T π i s = x) ∨
    ∃ (i j : Fin r) (hij : i ≠ j) (a : Kˣ), hLift T π hij a = x}

@[expose] noncomputable def liftTorus : Subgroup E :=
  Subgroup.closure (hGens T π)

end Defs

theorem tauLift_apply (π : E →* G0 T r) (i : Fin r) (s : Lˣ) :
    tauLift T π i s = rhoLift T π i (sl2Diag s) :=
  rfl

theorem hLift_apply (π : E →* G0 T r) {i j : Fin r} (hij : i ≠ j) (a : Kˣ) :
    hLift T π hij a = etaLift T π hij (sl2Diag a) :=
  rfl

theorem tauLift_mem (π : E →* G0 T r) (i : Fin r) (s : Lˣ) : tauLift T π i s ∈ liftTorus T π :=
  Subgroup.subset_closure (Or.inl ⟨i, s, rfl⟩)

theorem hLift_mem (π : E →* G0 T r) {i j : Fin r} (hij : i ≠ j) (a : Kˣ) :
    hLift T π hij a ∈ liftTorus T π :=
  Subgroup.subset_closure (Or.inr ⟨i, j, hij, a, rfl⟩)

structure TailHyp (π : E →* G0 T r) : Prop where
  char : ringChar K ≠ 2
  ext : IsLargeCentralExt π
  finK : Finite K
  finL : Finite L

variable {T} [Finite E] {π : E →* G0 T r}

namespace TailHyp

variable (hS : TailHyp T π)
include hS

omit [Finite E] in
theorem charL : ringChar L ≠ 2 := by
  rw [← Algebra.ringChar_eq K L]
  exact hS.char

theorem map_rhoLift (i : Fin r) (A : SpecialLinearGroup (Fin 2) L) :
    π (rhoLift T π i A) = rhoOG T i A := by
  have := hS.finL
  exact map_liftOf hS.charL hS.ext _ A

theorem map_etaLift {i j : Fin r} (hij : i ≠ j) (A : SpecialLinearGroup (Fin 2) K) :
    π (etaLift T π hij A) = etaG T hij A := by
  have := hS.finK
  exact map_liftOf hS.char hS.ext _ A

theorem coe_map_rhoLift (i : Fin r) (A : SpecialLinearGroup (Fin 2) L) :
    ((π (rhoLift T π i A) : G0 T r) : ((Fin r ⊕ Fin r → K) × L) ≃ₗ[K] _) = rhoO T i A := by
  rw [hS.map_rhoLift]
  rfl

theorem coe_map_etaLift {i j : Fin r} (hij : i ≠ j) (A : SpecialLinearGroup (Fin 2) K) :
    ((π (etaLift T π hij A) : G0 T r) : ((Fin r ⊕ Fin r → K) × L) ≃ₗ[K] _) = eta L hij A := by
  rw [hS.map_etaLift]
  rfl

theorem conj_liftOf_L {e : E} {α β : SpecialLinearGroup (Fin 2) L →* G0 T r}
    {γ : SpecialLinearGroup (Fin 2) L →* SpecialLinearGroup (Fin 2) L}
    (h : (MulAut.conj (π e)).toMonoidHom.comp α = β.comp γ) (g : SpecialLinearGroup (Fin 2) L) :
    e * liftOf π α g * e⁻¹ = liftOf π β (γ g) := by
  have := hS.finL
  exact conj_liftOf_apply hS.charL hS.ext h g

theorem conj_liftOf_K {e : E} {α β : SpecialLinearGroup (Fin 2) K →* G0 T r}
    {γ : SpecialLinearGroup (Fin 2) K →* SpecialLinearGroup (Fin 2) K}
    (h : (MulAut.conj (π e)).toMonoidHom.comp α = β.comp γ) (g : SpecialLinearGroup (Fin 2) K) :
    e * liftOf π α g * e⁻¹ = liftOf π β (γ g) := by
  have := hS.finK
  exact conj_liftOf_apply hS.char hS.ext h g

theorem liftOf_comp_K (α : SpecialLinearGroup (Fin 2) K →* G0 T r)
    (γ : SpecialLinearGroup (Fin 2) K →* SpecialLinearGroup (Fin 2) K) :
    (liftOf π α).comp γ = liftOf π (α.comp γ) := by
  have := hS.finK
  exact liftOf_comp hS.char hS.char hS.ext α γ

theorem commute_liftOf_KL (α : SpecialLinearGroup (Fin 2) K →* G0 T r)
    (α' : SpecialLinearGroup (Fin 2) L →* G0 T r) (h : ∀ g g', Commute (α g) (α' g'))
    (g : SpecialLinearGroup (Fin 2) K) (g' : SpecialLinearGroup (Fin 2) L) :
    Commute (liftOf π α g) (liftOf π α' g') := by
  have := hS.finK
  have := hS.finL
  exact commute_liftOf hS.char hS.charL hS.ext α α' h g g'

end TailHyp

section Images

variable (hS : TailHyp T π)
include hS

theorem coe_map_tauLift (i : Fin r) (s : Lˣ) :
    ((π (tauLift T π i s) : G0 T r) : ((Fin r ⊕ Fin r → K) × L) ≃ₗ[K] _) =
      tMap L (Pi.mulSingle i (normUnits T s)) (barQuot T s) := by
  rw [tauLift_apply, hS.coe_map_rhoLift, ← diagSL_eq_sl2Diag, rhoO_diagSL]

theorem coe_map_hLift {i j : Fin r} (hij : i ≠ j) (a : Kˣ) :
    ((π (hLift T π hij a) : G0 T r) : ((Fin r ⊕ Fin r → K) × L) ≃ₗ[K] _) =
      tMap L (Pi.mulSingle i a * Pi.mulSingle j a⁻¹) 1 := by
  rw [hLift_apply, hS.coe_map_etaLift, ← diagSL_eq_sl2Diag, eta_diagSL]

theorem coe_map_wLift (i : Fin r) :
    ((π (wLift T π i) : G0 T r) : ((Fin r ⊕ Fin r → K) × L) ≃ₗ[K] _) = rhoO T i sl2W :=
  hS.coe_map_rhoLift i sl2W

omit hS [Finite E] in
theorem torusMap_mul (a a' : Fin r → Kˣ) (c c' : Lˣ) :
    tMap L a c * tMap L a' c' = tMap L (a * a') (c * c') :=
  ((torusHom L r).map_mul (a, c) (a', c')).symm

omit hS [Finite E] in
theorem torusMap_one : tMap (K := K) L (1 : Fin r → Kˣ) 1 = 1 :=
  (torusHom L r).map_one

omit hS [Finite E] in
theorem torusMap_inv (a : Fin r → Kˣ) (c : Lˣ) : (tMap L a c)⁻¹ = tMap L a⁻¹ c⁻¹ :=
  ((torusHom L r).map_inv (a, c)).symm

theorem exists_torusMap_of_mem {x : E} (hx : x ∈ liftTorus T π) :
    ∃ (a : Fin r → Kˣ) (c : Lˣ), c ∈ normOne T ∧
      ((π x : G0 T r) : ((Fin r ⊕ Fin r → K) × L) ≃ₗ[K] _) = tMap L a c := by
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with ⟨i, s, rfl⟩ | ⟨i, j, hij, a, rfl⟩
    · exact ⟨_, _, barQuot_mem T s, coe_map_tauLift hS i s⟩
    · exact ⟨_, _, one_mem _, coe_map_hLift hS hij a⟩
  | one => exact ⟨1, 1, one_mem _, by rw [map_one, torusMap_one]; rfl⟩
  | mul x y _ _ ihx ihy =>
    obtain ⟨a, c, hc, hx⟩ := ihx
    obtain ⟨a', c', hc', hy⟩ := ihy
    exact ⟨a * a', c * c', mul_mem hc hc', by
      rw [map_mul, Subgroup.coe_mul, hx, hy, torusMap_mul]⟩
  | inv x _ ihx =>
    obtain ⟨a, c, hc, hx⟩ := ihx
    exact ⟨a⁻¹, c⁻¹, inv_mem hc, by rw [map_inv, Subgroup.coe_inv, hx, torusMap_inv]⟩

theorem coe_map_mem_tailTorus {x : E} (hx : x ∈ liftTorus T π) :
    ((π x : G0 T r) : ((Fin r ⊕ Fin r → K) × L) ≃ₗ[K] _) ∈ tailTorus r (normForm T) := by
  obtain ⟨a, c, hc, h⟩ := exists_torusMap_of_mem hS hx
  have hE := (π x).2
  rw [h] at hE ⊢
  exact torusMap_mem_tailTorus T a hc hE

end Images

section Conj

variable (hS : TailHyp T π)
include hS

theorem conj_rhoLift_of_torusMap {x : E} {a : Fin r → Kˣ} {c : Lˣ} (hc : c ∈ normOne T)
    (hx : ((π x : G0 T r) : ((Fin r ⊕ Fin r → K) × L) ≃ₗ[K] _) = tMap L a c) (j : Fin r)
    {u : Lˣ} (hu : (Units.map (algebraMap K L : K →* L) (a j) * c)⁻¹ = u)
    (A : SpecialLinearGroup (Fin 2) L) :
    x * rhoLift T π j A * x⁻¹ = rhoLift T π j (sl2ConjDiag u A) := by
  subst hu
  exact hS.conj_liftOf_L (conj_comp_eq fun g => Subtype.ext (by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hx, MonoidHom.comp_apply, coe_rhoOG, coe_rhoOG]
    exact torusMap_mul_rhoO T a hc j g)) A

theorem conj_etaLift_of_torusMap {x : E} {a : Fin r → Kˣ} {c : Lˣ}
    (hx : ((π x : G0 T r) : ((Fin r ⊕ Fin r → K) × L) ≃ₗ[K] _) = tMap L a c) {i j : Fin r}
    (hij : i ≠ j) {u : Kˣ} (hu : (a i)⁻¹ * a j = u) (A : SpecialLinearGroup (Fin 2) K) :
    x * etaLift T π hij A * x⁻¹ = etaLift T π hij (sl2ConjDiag u A) := by
  subst hu
  exact hS.conj_liftOf_K (conj_comp_eq fun g => Subtype.ext (by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hx, MonoidHom.comp_apply, coe_etaG, coe_etaG]
    exact torusMap_mul_eta T a c hij g)) A

theorem commute_of_torusMap {x : E} {a : Fin r → Kˣ} {c : Lˣ} (hc : c ∈ normOne T)
    (hx : ((π x : G0 T r) : ((Fin r ⊕ Fin r → K) × L) ≃ₗ[K] _) = tMap L a c) {y : E}
    (hy : y ∈ hGens T π) : Commute x y := by
  rcases hy with ⟨j, s, rfl⟩ | ⟨i, j, hij, b, rfl⟩
  · have h := conj_rhoLift_of_torusMap hS hc hx j rfl (sl2Diag s)
    rw [sl2ConjDiag_sl2Diag] at h
    exact mul_inv_eq_iff_eq_mul.1 h
  · have h := conj_etaLift_of_torusMap hS hx hij rfl (sl2Diag b)
    rw [sl2ConjDiag_sl2Diag] at h
    exact mul_inv_eq_iff_eq_mul.1 h

theorem commute_of_mem_hGens {x y : E} (hx : x ∈ hGens T π) (hy : y ∈ hGens T π) :
    Commute x y := by
  obtain ⟨a, c, hc, h⟩ := exists_torusMap_of_mem hS (Subgroup.subset_closure hx)
  exact commute_of_torusMap hS hc h hy

theorem liftTorus_commute {x y : E} (hx : x ∈ liftTorus T π) (hy : y ∈ liftTorus T π) :
    Commute x y := by
  have hcomm := Subgroup.isMulCommutative_closure (k := hGens T π)
    (fun x hx y hy _ => commute_of_mem_hGens hS hx hy)
  exact congrArg Subtype.val (hcomm.is_comm.comm (⟨x, hx⟩ : liftTorus T π) ⟨y, hy⟩)

end Conj

section SL2

variable {F : Type} [Field F]

theorem sl2W_inv_eq : (sl2W : SpecialLinearGroup (Fin 2) F)⁻¹ = sl2Diag (-1) * sl2W := by
  refine Matrix.SpecialLinearGroup.ext _ _ fun a b => ?_
  rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.coe_sl2W_inv,
    Matrix.SpecialLinearGroup.coe_mul, coe_sl2Diag,
    CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.coe_sl2W]
  fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

end SL2

omit [Finite E] in
theorem hLift_mem_hGens (π : E →* G0 T r) {i j : Fin r} (hij : i ≠ j) (a : Kˣ) :
    hLift T π hij a ∈ hGens T π :=
  Or.inr ⟨i, j, hij, a, rfl⟩

omit [Finite E] in
theorem tauLift_mem_hGens (π : E →* G0 T r) (i : Fin r) (s : Lˣ) : tauLift T π i s ∈ hGens T π :=
  Or.inl ⟨i, s, rfl⟩

omit [Finite E] in
theorem wLift_mul_self (i : Fin r) : wLift T π i * wLift T π i = tauLift T π i (-1) := by
  rw [wLift, ← map_mul, sl2W_mul_sl2W]
  rfl

section RankOne

variable (hS : TailHyp T π)
include hS

theorem wLift_conj_rhoLift {i j : Fin r} (hij : i ≠ j) (A : SpecialLinearGroup (Fin 2) L) :
    wLift T π i * rhoLift T π j A * (wLift T π i)⁻¹ =
      rhoLift T π j (sl2ConjDiag (-1) (barSL T A)) :=
  hS.conj_liftOf_L (β := rhoOG T j) (γ := (sl2ConjDiag (-1)).comp (barSL T))
    (conj_comp_eq fun g => Subtype.ext (by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, coe_map_wLift hS, MonoidHom.comp_apply, coe_rhoOG,
        MonoidHom.comp_apply, coe_rhoOG]
      exact rhoO_sl2W_mul_rhoO T hij g)) A

theorem wLift_conj_wLift {i j : Fin r} (hij : i ≠ j) :
    wLift T π i * wLift T π j * (wLift T π i)⁻¹ = rhoLift T π j (-1) * wLift T π j := by
  rw [show wLift T π j = rhoLift T π j sl2W from rfl, wLift_conj_rhoLift hS hij, barSL_sl2W,
    sl2ConjDiag_neg_one_sl2W, sl2W_inv_eq, map_mul,
    neg_one_eq_sl2Diag]

theorem vLift_conj_rhoLift {i j : Fin r} (hij : i ≠ j) (A : SpecialLinearGroup (Fin 2) L) :
    etaLift T π hij sl2W * rhoLift T π j A * (etaLift T π hij sl2W)⁻¹ =
      rhoLift T π i (sl2ConjDiag (-1) A) :=
  hS.conj_liftOf_L (β := rhoOG T i) (γ := sl2ConjDiag (-1))
    (conj_comp_eq fun g => Subtype.ext (by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, hS.coe_map_etaLift, MonoidHom.comp_apply,
        coe_rhoOG, coe_rhoOG]
      exact eta_sl2W_mul_rhoO T hij g)) A

theorem vLift_conj_tauLift {i j : Fin r} (hij : i ≠ j) (s : Lˣ) :
    etaLift T π hij sl2W * tauLift T π j s * (etaLift T π hij sl2W)⁻¹ = tauLift T π i s := by
  rw [tauLift_apply, vLift_conj_rhoLift hS hij, sl2ConjDiag_sl2Diag]
  rfl

theorem vLift_conj_wLift {i j : Fin r} (hij : i ≠ j) :
    etaLift T π hij sl2W * wLift T π j * (etaLift T π hij sl2W)⁻¹ = (wLift T π i)⁻¹ := by
  rw [show wLift T π j = rhoLift T π j sl2W from rfl, vLift_conj_rhoLift hS hij,
    sl2ConjDiag_neg_one_sl2W, map_inv]
  rfl

theorem vLift_conj_etaLift {c d : Fin r} (hcd : c ≠ d) {a b a' b' : Fin r} (hab : a ≠ b)
    (hab' : a' ≠ b')
    (ha : (Equiv.swap (Sum.inl c : Fin r ⊕ Fin r) (Sum.inl d) *
      Equiv.swap (Sum.inl c : Fin r ⊕ Fin r).swap (Sum.inl d : Fin r ⊕ Fin r).swap)
        (Sum.inl a) = Sum.inl a')
    (hb : (Equiv.swap (Sum.inl c : Fin r ⊕ Fin r) (Sum.inl d) *
      Equiv.swap (Sum.inl c : Fin r ⊕ Fin r).swap (Sum.inl d : Fin r ⊕ Fin r).swap)
        (Sum.inl b) = Sum.inl b')
    {u : Kˣ} (hu : SplitO.wSign (k := K) (Sum.inl d) (Sum.inl a) * u =
      SplitO.wSign (Sum.inl d) (Sum.inl b))
    (g : SpecialLinearGroup (Fin 2) K) :
    etaLift T π hcd sl2W * etaLift T π hab g * (etaLift T π hcd sl2W)⁻¹ =
      etaLift T π hab' (sl2ConjDiag u g) :=
  hS.conj_liftOf_K (β := etaG T hab') (γ := sl2ConjDiag u)
    (conj_comp_eq fun g => Subtype.ext (by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, hS.coe_map_etaLift, MonoidHom.comp_apply,
        coe_etaG, coe_etaG]
      exact eta_sl2W_mul_eta T hcd hab hab' ha hb hu g)) g

theorem vLift_conj_hLift {i j l : Fin r} (hij : i ≠ j) (hjl : j ≠ l) (hil : i ≠ l) (a : Kˣ) :
    etaLift T π hij sl2W * hLift T π hjl a * (etaLift T π hij sl2W)⁻¹ = hLift T π hil a := by
  have hlj : Sum.inl l ≠ (Sum.inl j : Fin r ⊕ Fin r) := fun h => hjl (Sum.inl_injective h).symm
  rw [hLift_apply, vLift_conj_etaLift hS hij hjl hil (u := -1)
    (by simp [Equiv.swap_apply_of_ne_of_ne])
    (by simp [Equiv.swap_apply_of_ne_of_ne, hjl.symm, hil.symm])
    (by rw [SplitO.wSign_of_eq rfl, SplitO.wSign_of_ne hlj (by simp)]; simp),
    sl2ConjDiag_sl2Diag]
  rfl

theorem hLift_inv_conj_vLift {i j l : Fin r} (hij : i ≠ j) (hjl : j ≠ l) (hil : i ≠ l)
    (a : Kˣ) :
    (hLift T π hjl a)⁻¹ * etaLift T π hij sl2W * hLift T π hjl a =
      hLift T π hij a * etaLift T π hij sl2W := by
  have hx : ((π (hLift T π hjl a)⁻¹ : G0 T r) : ((Fin r ⊕ Fin r → K) × L) ≃ₗ[K] _) =
      tMap L (Pi.mulSingle j a * Pi.mulSingle l a⁻¹)⁻¹ 1⁻¹ := by
    rw [map_inv, Subgroup.coe_inv, coe_map_hLift hS, torusMap_inv]
  have h := conj_etaLift_of_torusMap hS hx hij (u := a⁻¹) (by simp [hij, hil, hjl]) sl2W
  rw [sl2ConjDiag_inv_sl2W, map_mul, inv_inv] at h
  exact h

theorem hLift_trans {i j l : Fin r} (hij : i ≠ j) (hjl : j ≠ l) (hil : i ≠ l) (a : Kˣ) :
    hLift T π hil a = hLift T π hij a * hLift T π hjl a := by
  have h1 := vLift_conj_hLift hS hij hjl hil a
  have h2 := hLift_inv_conj_vLift hS hij hjl hil a
  have h3 : etaLift T π hij sl2W * hLift T π hjl a =
      hLift T π hjl a * (hLift T π hij a * etaLift T π hij sl2W) := by
    rw [← h2]
    group
  rw [← h1, h3, mul_assoc, mul_assoc, mul_inv_cancel, mul_one]
  exact (commute_of_mem_hGens hS (hLift_mem_hGens π hjl a) (hLift_mem_hGens π hij a)).eq

omit hS [Finite E] in
theorem etaG_symm {i j : Fin r} (hij : i ≠ j) :
    etaG T hij.symm = (etaG T hij).comp sl2Swap :=
  MonoidHom.ext fun g => Subtype.ext (by
    rw [coe_etaG, MonoidHom.comp_apply, coe_etaG, eta_symm T hij]
    rfl)

theorem hLift_symm {i j : Fin r} (hij : i ≠ j) (a : Kˣ) :
    hLift T π hij.symm a = hLift T π hij a⁻¹ := by
  rw [hLift_apply, etaLift, etaG_symm, ← hS.liftOf_comp_K, MonoidHom.comp_apply, sl2Swap_sl2Diag]
  rfl

theorem tauLift_eq {i j : Fin r} (hij : i ≠ j) (s : Lˣ) :
    tauLift T π i s = hLift T π hij (normUnits T s) * tauLift T π j s := by
  have h1 := vLift_conj_tauLift hS hij s
  have hx : ((π (tauLift T π j s)⁻¹ : G0 T r) : ((Fin r ⊕ Fin r → K) × L) ≃ₗ[K] _) =
      tMap L (Pi.mulSingle j (normUnits T s))⁻¹ (barQuot T s)⁻¹ := by
    rw [map_inv, Subgroup.coe_inv, coe_map_tauLift hS, torusMap_inv]
  have h2 := conj_etaLift_of_torusMap hS hx hij (u := (normUnits T s)⁻¹) (by simp [hij]) sl2W
  rw [sl2ConjDiag_inv_sl2W, map_mul, inv_inv] at h2
  have h3 : etaLift T π hij sl2W * tauLift T π j s =
      tauLift T π j s * (hLift T π hij (normUnits T s) * etaLift T π hij sl2W) := by
    rw [hLift_apply, ← h2]
    group
  rw [← h1, h3, mul_assoc, mul_assoc, mul_inv_cancel, mul_one]
  exact (commute_of_mem_hGens hS (tauLift_mem_hGens π j s) (hLift_mem_hGens π hij _)).eq

omit hS [Finite E] in
theorem normUnits_neg_one : normUnits T (-1) = 1 := by
  refine Units.ext ?_
  rw [coe_normUnits, Units.val_neg, Units.val_one, Units.val_one, ← map_one (algebraMap K L),
    ← map_neg, normForm_algebraMap]
  norm_num

end RankOne

section Theta

@[expose] def adjL (m : Fin (r - 1)) : Fin r :=
  ⟨m.val, Nat.lt_of_lt_of_le m.isLt (Nat.sub_le r 1)⟩

@[expose] def adjR (m : Fin (r - 1)) : Fin r :=
  ⟨m.val + 1, by have := m.isLt; omega⟩

theorem adjL_ne_adjR (m : Fin (r - 1)) : adjL m ≠ adjR m :=
  Fin.ne_of_val_ne (by simp [adjL, adjR])

@[expose] def thetaDiag (u : Fin (r - 1) → Kˣ) (n : Kˣ) : Fin r → Kˣ := fun j =>
  (if h : j.val < r - 1 then u ⟨j.val, h⟩ else n) *
    (if h : 1 ≤ j.val then (u ⟨j.val - 1, by have := j.isLt; omega⟩)⁻¹ else 1)

theorem prod_mulSingle_adjL (u : Fin (r - 1) → Kˣ) (j : Fin r) :
    (∏ m, Pi.mulSingle (adjL m) (u m) : Fin r → Kˣ) j =
      if h : j.val < r - 1 then u ⟨j.val, h⟩ else 1 := by
  rw [Finset.prod_apply]
  split_ifs with h
  · rw [Finset.prod_eq_single ⟨j.val, h⟩]
    · rw [Pi.mulSingle_apply, ite_eq_left (show j = adjL ⟨j.val, h⟩ from Fin.ext rfl)]
    · intro m _ hm
      rw [Pi.mulSingle_apply, ite_eq_right]
      intro hjm
      rw [Fin.ext_iff] at hjm
      simp only [adjL, Fin.val_mk] at hjm
      exact hm (Fin.ext (by simp only; omega))
    · simp
  · refine Finset.prod_eq_one fun m _ => ?_
    rw [Pi.mulSingle_apply, ite_eq_right]
    intro hjm
    rw [Fin.ext_iff] at hjm
    simp only [adjL, Fin.val_mk] at hjm
    have := m.isLt
    omega

theorem prod_mulSingle_adjR (u : Fin (r - 1) → Kˣ) (j : Fin r) :
    (∏ m, Pi.mulSingle (adjR m) (u m)⁻¹ : Fin r → Kˣ) j =
      if h : 1 ≤ j.val then (u ⟨j.val - 1, by have := j.isLt; omega⟩)⁻¹ else 1 := by
  rw [Finset.prod_apply]
  split_ifs with h
  · rw [Finset.prod_eq_single ⟨j.val - 1, by have := j.isLt; omega⟩]
    · rw [Pi.mulSingle_apply, ite_eq_left (show j = adjR ⟨j.val - 1, by have := j.isLt; omega⟩
        from Fin.ext (by simp [adjR]; omega))]
    · intro m _ hm
      rw [Pi.mulSingle_apply, ite_eq_right]
      intro hjm
      rw [Fin.ext_iff] at hjm
      simp only [adjR, Fin.val_mk] at hjm
      exact hm (Fin.ext (by simp only; omega))
    · simp
  · refine Finset.prod_eq_one fun m _ => ?_
    rw [Pi.mulSingle_apply, ite_eq_right]
    intro hjm
    rw [Fin.ext_iff] at hjm
    simp only [adjR, Fin.val_mk] at hjm
    omega

theorem prod_adj_mul_mulSingle (hr : 1 ≤ r) (u : Fin (r - 1) → Kˣ) (n : Kˣ) :
    (∏ m, (Pi.mulSingle (adjL m) (u m) * Pi.mulSingle (adjR m) (u m)⁻¹ : Fin r → Kˣ)) *
      Pi.mulSingle ⟨r - 1, by omega⟩ n = thetaDiag u n := by
  funext j
  rw [Pi.mul_apply, Finset.prod_mul_distrib, Pi.mul_apply, prod_mulSingle_adjL,
    prod_mulSingle_adjR, Pi.mulSingle_apply, thetaDiag]
  have hj := j.isLt
  by_cases h1 : j.val < r - 1
  · rw [dite_eq_left h1, dite_eq_left h1, ite_eq_right (fun h => by rw [h] at h1; simp at h1),
      mul_one]
  · have hjr : j = ⟨r - 1, by omega⟩ := Fin.ext (by simp; omega)
    rw [dite_eq_right h1, dite_eq_right h1, ite_eq_left hjr, one_mul, mul_comm]

variable (hS : TailHyp T π)
include hS

theorem pairwise_commute_hAdj :
    Pairwise fun m n : Fin (r - 1) => ∀ x y : Kˣ,
      Commute (hLift T π (adjL_ne_adjR m) x) (hLift T π (adjL_ne_adjR n) y) :=
  fun _ _ _ x y => liftTorus_commute hS (hLift_mem T π _ x) (hLift_mem T π _ y)

theorem noncommPiCoprod_hAdj_mem (u : Fin (r - 1) → Kˣ) :
    MonoidHom.noncommPiCoprod (fun m => hLift T π (adjL_ne_adjR m)) (pairwise_commute_hAdj hS) u ∈
      liftTorus T π := by
  have hle : (MonoidHom.noncommPiCoprod (fun m => hLift T π (adjL_ne_adjR m))
      (pairwise_commute_hAdj hS)).range ≤ liftTorus T π := by
    rw [MonoidHom.noncommPiCoprod_range]
    refine iSup_le fun m => ?_
    rintro _ ⟨a, rfl⟩
    exact hLift_mem T π _ a
  exact hle ⟨u, rfl⟩

noncomputable def thetaHom (hr : 1 ≤ r) : (Fin (r - 1) → Kˣ) × Lˣ →* E :=
  (MonoidHom.noncommPiCoprod (fun m => hLift T π (adjL_ne_adjR m))
    (pairwise_commute_hAdj hS)).noncommCoprod (tauLift T π ⟨r - 1, by omega⟩)
    (fun u s => liftTorus_commute hS (noncommPiCoprod_hAdj_mem hS u) (tauLift_mem T π _ s))

theorem thetaHom_apply (hr : 1 ≤ r) (u : Fin (r - 1) → Kˣ) (s : Lˣ) :
    thetaHom hS hr (u, s) =
      (List.ofFn fun m => hLift T π (adjL_ne_adjR m) (u m)).prod *
        tauLift T π ⟨r - 1, by omega⟩ s := by
  rw [thetaHom, MonoidHom.noncommCoprod_apply, MonoidHom.noncommPiCoprod_apply]
  congr 1
  exact CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.noncommProd_univ_fin _ _

theorem thetaHom_mem (hr : 1 ≤ r) (p : (Fin (r - 1) → Kˣ) × Lˣ) :
    thetaHom hS hr p ∈ liftTorus T π := by
  rw [thetaHom, MonoidHom.noncommCoprod_apply]
  exact mul_mem (noncommPiCoprod_hAdj_mem hS _) (tauLift_mem T π _ _)

theorem hLift_adj_mem_range (hr : 1 ≤ r) (m : Fin (r - 1)) (a : Kˣ) :
    hLift T π (adjL_ne_adjR m) a ∈ (thetaHom hS hr).range :=
  ⟨(Pi.mulSingle m a, 1), by
    rw [thetaHom, MonoidHom.noncommCoprod_apply, MonoidHom.noncommPiCoprod_mulSingle, map_one,
      mul_one]⟩

theorem tauLift_last_mem_range (hr : 1 ≤ r) (s : Lˣ) :
    tauLift T π ⟨r - 1, by omega⟩ s ∈ (thetaHom hS hr).range :=
  ⟨(1, s), by rw [thetaHom, MonoidHom.noncommCoprod_apply, map_one, one_mul]⟩

omit hS [Finite E] in
theorem hLift_congr {i j i' j' : Fin r} (hi : i = i') (hj : j = j') (hij : i ≠ j)
    (hij' : i' ≠ j') (a : Kˣ) : hLift T π hij a = hLift T π hij' a := by
  subst hi hj
  rfl

theorem hLift_mem_range_of_lt (hr : 1 ≤ r) {i j : Fin r} (hij : i < j) (a : Kˣ) :
    hLift T π hij.ne a ∈ (thetaHom hS hr).range := by
  suffices h : ∀ m : ℕ, ∀ (i j : Fin r) (hij : i ≠ j), j.val = i.val + m + 1 →
      hLift T π hij a ∈ (thetaHom hS hr).range from
    h (j.val - i.val - 1) i j hij.ne (by have := Fin.lt_def.1 hij; omega)
  intro m
  induction m with
  | zero =>
    intro i j hij hj
    have hlt : i.val < r - 1 := by have := j.isLt; omega
    rw [hLift_congr (π := π) (i := i) (j := j) (i' := adjL ⟨i.val, hlt⟩)
      (j' := adjR ⟨i.val, hlt⟩) (Fin.ext rfl) (Fin.ext (by simp [adjR]; omega)) hij
      (adjL_ne_adjR _)]
    exact hLift_adj_mem_range hS hr _ a
  | succ m ih =>
    intro i j hij hj
    have hlt : i.val + m + 1 < r := by have := j.isLt; omega
    set j' : Fin r := ⟨i.val + m + 1, hlt⟩
    have hij' : i ≠ j' := Fin.ne_of_val_ne (by simp [j']; omega)
    have hj'j : j' ≠ j := Fin.ne_of_val_ne (by simp [j']; omega)
    have hlt' : j'.val < r - 1 := by have := j.isLt; simp [j']; omega
    rw [hLift_trans hS hij' hj'j hij]
    refine mul_mem (ih i j' hij' rfl) ?_
    rw [hLift_congr (π := π) (i := j') (j := j) (i' := adjL ⟨j'.val, hlt'⟩)
      (j' := adjR ⟨j'.val, hlt'⟩) (Fin.ext rfl) (Fin.ext (by simp [adjR, j']; omega)) hj'j
      (adjL_ne_adjR _)]
    exact hLift_adj_mem_range hS hr _ a

theorem hLift_mem_range (hr : 1 ≤ r) {i j : Fin r} (hij : i ≠ j) (a : Kˣ) :
    hLift T π hij a ∈ (thetaHom hS hr).range := by
  rcases lt_or_gt_of_ne hij with h | h
  · exact hLift_mem_range_of_lt hS hr h a
  · rw [show hLift T π hij a = hLift T π h.ne.symm a from rfl, hLift_symm hS h.ne a]
    exact hLift_mem_range_of_lt hS hr h _

theorem range_thetaHom (hr : 1 ≤ r) : (thetaHom hS hr).range = liftTorus T π := by
  apply le_antisymm
  · rintro _ ⟨p, rfl⟩
    exact thetaHom_mem hS hr p
  · rw [liftTorus, Subgroup.closure_le]
    rintro _ (⟨i, s, rfl⟩ | ⟨i, j, hij, a, rfl⟩)
    · by_cases hi : i = ⟨r - 1, by omega⟩
      · subst hi
        exact tauLift_last_mem_range hS hr s
      · rw [tauLift_eq hS hi s]
        exact mul_mem (hLift_mem_range hS hr hi _) (tauLift_last_mem_range hS hr s)
    · exact hLift_mem_range hS hr hij a

theorem coe_map_thetaHom (hr : 1 ≤ r) (u : Fin (r - 1) → Kˣ) (s : Lˣ) :
    ((π (thetaHom hS hr (u, s)) : G0 T r) : ((Fin r ⊕ Fin r → K) × L) ≃ₗ[K] _) =
      tMap L (thetaDiag u (normUnits T s)) (barQuot T s) := by
  set f := (orthElementaryGroup (quadTail r (normForm T))).subtype.comp π
  have key : ∀ m : Fin (r - 1), f (hLift T π (adjL_ne_adjR m) (u m)) =
      torusHom L r (Pi.mulSingle (adjL m) (u m) * Pi.mulSingle (adjR m) (u m)⁻¹, 1) :=
    fun m => coe_map_hLift hS _ _
  have key2 : f (tauLift T π ⟨r - 1, by omega⟩ s) =
      torusHom L r (Pi.mulSingle ⟨r - 1, by omega⟩ (normUnits T s), barQuot T s) :=
    coe_map_tauLift hS _ _
  change f (thetaHom hS hr (u, s)) = _
  rw [thetaHom_apply, map_mul, map_list_prod, List.map_ofFn, key2]
  have h3 : (f ∘ fun m => hLift T π (adjL_ne_adjR m) (u m)) = (torusHom L r) ∘
      fun m => (Pi.mulSingle (adjL m) (u m) * Pi.mulSingle (adjR m) (u m)⁻¹, (1 : Lˣ)) :=
    funext key
  rw [h3, ← List.map_ofFn, ← map_list_prod, ← map_mul, ← prod_adj_mul_mulSingle hr,
    List.prod_ofFn, torusHom_apply]
  congr 1
  · rw [Prod.fst_mul, Prod.fst_prod]
  · rw [Prod.snd_mul, Prod.snd_prod, Finset.prod_const_one, one_mul]

omit [Finite E] hS in
theorem eq_one_of_thetaDiag_eq_one (hr : 2 ≤ r) {u : Fin (r - 1) → Kˣ} {n : Kˣ}
    (h : thetaDiag u n = 1) : u = 1 ∧ n = 1 := by
  have hu : ∀ m (hm : m < r - 1), u ⟨m, hm⟩ = 1 := by
    intro m
    induction m with
    | zero =>
      intro hm
      have := congrFun h ⟨0, by omega⟩
      simpa [thetaDiag, hm] using this
    | succ m ih =>
      intro hm
      have h1 := congrFun h ⟨m + 1, by omega⟩
      simp only [thetaDiag, Pi.one_apply] at h1
      rw [dite_eq_left hm, dite_eq_left (by omega)] at h1
      have h2 := ih (by omega)
      simp only [Nat.add_sub_cancel] at h1
      rw [h2, inv_one, mul_one] at h1
      exact h1
  refine ⟨funext fun m => hu m.val m.isLt, ?_⟩
  have h1 := congrFun h ⟨r - 1, by omega⟩
  simp only [thetaDiag, Pi.one_apply] at h1
  rw [dite_eq_right (by omega), dite_eq_left (by omega), hu _ (by omega), inv_one,
    mul_one] at h1
  exact h1

omit [Finite E] hS in
theorem barQuot_neg_one : barQuot T (-1) = 1 :=
  Units.ext (by
    rw [coe_barQuot, Units.val_neg, Units.val_one, map_neg, map_one,
      div_self (neg_ne_zero.2 one_ne_zero)])

omit [Finite E] hS in
theorem eq_one_or_neg_one_of_barQuot {s : Lˣ} (h1 : barQuot T s = 1) (h2 : normUnits T s = 1) :
    s = 1 ∨ s = -1 := by
  have hb : T.bar (s : L) = s := by
    have := congrArg Units.val h1
    rw [coe_barQuot, Units.val_one, div_eq_one_iff_eq] at this
    · exact this.symm
    · exact (map_ne_zero T.bar).2 s.ne_zero
  obtain ⟨k, hk⟩ := T.exists_eq_of_bar_eq _ hb
  have hk2 : k ^ 2 = 1 := by
    have := congrArg Units.val h2
    rw [coe_normUnits, ← hk, normForm_algebraMap, Units.val_one] at this
    exact this
  rcases sq_eq_one_iff.1 hk2 with rfl | rfl
  · left
    exact Units.ext (by rw [← hk, map_one, Units.val_one])
  · right
    exact Units.ext (by rw [← hk, map_neg, map_one, Units.val_neg, Units.val_one])

theorem tauLift_neg_one_mem_ker (i : Fin r) : tauLift T π i (-1) ∈ π.ker := by
  rw [MonoidHom.mem_ker]
  apply Subtype.ext
  rw [coe_map_tauLift hS, normUnits_neg_one, barQuot_neg_one, Pi.mulSingle_one, torusMap_one]
  rfl

omit hS [Finite E] in
theorem tauLift_neg_one_sq (i : Fin r) : tauLift T π i (-1) ^ 2 = 1 := by
  rw [← map_pow, neg_one_sq, map_one]

theorem liftTorus_inf_ker (hr : 2 ≤ r) :
    liftTorus T π ⊓ π.ker = Subgroup.zpowers (tauLift T π ⟨r - 1, by omega⟩ (-1)) := by
  apply le_antisymm
  · rintro x ⟨hxH, hxK⟩
    rw [← range_thetaHom hS (by omega)] at hxH
    obtain ⟨⟨u, s⟩, rfl⟩ := hxH
    have h1 : torusHom L r (thetaDiag u (normUnits T s), barQuot T s) = torusHom L r 1 := by
      rw [map_one, torusHom_apply, ← coe_map_thetaHom hS (by omega), (MonoidHom.mem_ker).1 hxK]
      rfl
    have h2 := torusHom_injective h1
    obtain ⟨hu, hn⟩ := eq_one_of_thetaDiag_eq_one hr (congrArg Prod.fst h2)
    subst hu
    have hs := eq_one_or_neg_one_of_barQuot (congrArg Prod.snd h2) hn
    rw [thetaHom_apply]
    simp only [Pi.one_apply, map_one, List.ofFn_const, List.prod_replicate, one_pow, one_mul]
    rcases hs with rfl | rfl
    · rw [map_one]
      exact one_mem _
    · exact Subgroup.mem_zpowers _
  · rw [Subgroup.zpowers_le]
    exact ⟨tauLift_mem T π _ _, tauLift_neg_one_mem_ker hS _⟩

omit [Finite E] in
theorem eq_one_of_mem_ker_of_sq_eq_one {x : E} (hx : x ∈ π.ker) (hx2 : x ^ 2 = 1) : x = 1 := by
  obtain ⟨p, hp, hp3, hpk⟩ := hS.ext.large
  obtain ⟨n, hn⟩ := hpk ⟨x, hx⟩
  have hn' : x ^ p ^ n = 1 := congrArg Subtype.val hn
  have hcop : Nat.Coprime 2 (p ^ n) :=
    Nat.Coprime.pow_right n ((Nat.coprime_primes Nat.prime_two hp).2 (by omega))
  have h1 : x ^ Nat.gcd 2 (p ^ n) = 1 := pow_gcd_eq_one.2 ⟨hx2, hn'⟩
  rwa [Nat.Coprime.gcd_eq_one hcop, pow_one] at h1

theorem tauLift_neg_one_eq_one (i : Fin r) : tauLift T π i (-1) = 1 :=
  eq_one_of_mem_ker_of_sq_eq_one hS (tauLift_neg_one_mem_ker hS i) (tauLift_neg_one_sq i)

end Theta

end CFSG.RankThree.CentralLiftSO.TailO
