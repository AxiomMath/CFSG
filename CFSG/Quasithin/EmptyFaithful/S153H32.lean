module

public import CFSG.Quasithin.EmptyFaithful.S153D32
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Hypotheses

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

section Clauses

variable {G : Type} [Group G] [Finite G]

@[expose] def Preamble32 (T V₁ I L : Subgroup G) : Prop :=
  L ⊓ Subgroup.centralizer (UI153 T I : Set G) = pCoreOf 2 L ∧
    pCoreOf 2 I = I ⊓ Subgroup.centralizer (UL153 T I L : Set G) ∧
    I ⊓ Subgroup.centralizer (UL153 T I L : Set G) =
      Sgp153 T V₁ ⊓ Subgroup.centralizer (UL153 T I L : Set G)

@[expose] def Clause32One (T I L : Subgroup G) : Prop :=
  ∃ q : ↥(UL153 T I L) → ZMod 2, IsQuadraticFormOn q ∧ IsNondegQuadratic q ∧
    (∃ E : Subgroup ↥(UL153 T I L), Nat.card E = 2 ^ 3 ∧ ∀ e ∈ E, q e = 0) ∧
      Nat.card ↥(UL153 T I L) = 2 ^ 6 ∧ autOn I (UL153 T I L) = orthogonalGroupOf q

@[expose] def Clause32Two (T M V₁ L : Subgroup G) : Prop :=
  ZS153 T M V₁ ⊓ Subgroup.centralizer (L : Set G) = ZS153 T M V₁ ⊓ V₁ ∧
    Nat.card ↥(ZS153 T M V₁ ⊓ V₁) = 2

@[expose] def Clause32Three (T M V₁ L : Subgroup G) : Prop :=
  L = oPrimeResidualOf 3 (Subgroup.centralizer ((ZS153 T M V₁ ⊓ V₁ : Subgroup G) : Set G))

@[expose] def Clause32Four (T M V₁ I L : Subgroup G) : Prop :=
  ∃ K : Subgroup G, K ≤ L ∧ IsMaxParabolic2 (Star153 T I L) (Star153 T I K) ∧
    Sgp153 T V₁ ≤ Subgroup.normalizer (K : Set G) ∧ X153 T M V₁ = oPrimeResidualOf 3 K

@[expose] def Clause32Five (T M V₁ I L : Subgroup G) : Prop :=
  ∀ t' ∈ T, t' ∉ Sgp153 T V₁ →
    (⁅UL153 T I L, conjBy153 t' (UL153 T I L)⁆ = ⊥ ∧
      UL153 T I L ⊓ conjBy153 t' (UL153 T I L) = ⊥ ∧
      X153 T M V₁ ⊔ Sgp153 T V₁ ≤
        Subgroup.normalizer ((UL153 T I L ⊔ conjBy153 t' (UL153 T I L) : Subgroup G) : Set G))

@[expose] def Clause32FiveInter (T V₁ I L : Subgroup G) : Prop :=
  ∀ t' ∈ T, t' ∉ Sgp153 T V₁ → UL153 T I L ⊓ conjBy153 t' (UL153 T I L) = ⊥

@[expose] def Clause32SixP (T M V₁ I L : Subgroup G) : Prop :=
  ∀ t' ∈ T, t' ∉ Sgp153 T V₁ →
    pCoreOf 2 (X153 T M V₁ ⊔ Sgp153 T V₁) =
      (Sgp153 T V₁ ⊓ Subgroup.centralizer (UL153 T I L : Set G)) ⊔
        (Sgp153 T V₁ ⊓ Subgroup.centralizer (conjBy153 t' (UL153 T I L) : Set G))

end Clauses

@[expose] def Input32Preamble : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    Ctx15332 T Mc M V₁ V₂ Yp I L t → Preamble32 T V₁ I L

@[expose] def Input32One : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    Ctx15332 T Mc M V₁ V₂ Yp I L t → Preamble32 T V₁ I L → Clause32One T I L

@[expose] def Input32Two : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    Ctx15332 T Mc M V₁ V₂ Yp I L t → Clause32One T I L → Clause32Two T M V₁ L

@[expose] def Input32Three : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    Ctx15332 T Mc M V₁ V₂ Yp I L t → Clause32One T I L → Clause32Two T M V₁ L →
      Clause32Three T M V₁ L

@[expose] def Input32Four : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    Ctx15332 T Mc M V₁ V₂ Yp I L t → Clause32One T I L → Clause32Three T M V₁ L →
      Clause32Four T M V₁ I L

@[expose] def Input32FiveInter : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    Ctx15332 T Mc M V₁ V₂ Yp I L t → Clause32One T I L → Clause32Two T M V₁ L →
      Clause32Three T M V₁ L → Clause32Four T M V₁ I L → Clause32FiveInter T V₁ I L

@[expose] def Input32SixP : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    Ctx15332 T Mc M V₁ V₂ Yp I L t → Preamble32 T V₁ I L → Clause32One T I L →
      Clause32Four T M V₁ I L → Clause32Five T M V₁ I L → Clause32SixP T M V₁ I L

namespace S153H

section Routine

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}

omit [Finite G] in
theorem mem_normalizer_conjBy {t g : G} {X : Subgroup G}
    (h : t⁻¹ * g * t ∈ Subgroup.normalizer (X : Set G)) :
    g ∈ Subgroup.normalizer ((conjBy153 t X : Subgroup G) : Set G) := by
  have e1 : ∀ y : G, y ∈ conjBy153 t X ↔ t⁻¹ * y * t ∈ X := by
    intro y
    constructor
    · rintro ⟨x, hx, rfl⟩
      show t⁻¹ * (t * x * t⁻¹) * t ∈ X
      rwa [show t⁻¹ * (t * x * t⁻¹) * t = x by group]
    · intro hy
      exact ⟨t⁻¹ * y * t, hy, by simp [MulAut.conj_apply, mul_assoc]⟩
  rw [Subgroup.mem_normalizer_iff]
  intro y
  rw [e1, e1]
  have := (Subgroup.mem_normalizer_iff.mp h) (t⁻¹ * y * t)
  have e2 : (t⁻¹ * g * t) * (t⁻¹ * y * t) * (t⁻¹ * g * t)⁻¹ = t⁻¹ * (g * y * g⁻¹) * t := by group
  rw [e2] at this
  exact this

omit [Finite G] in
theorem mem_normalizer_sup {g : G} {A B : Subgroup G}
    (hA : g ∈ Subgroup.normalizer (A : Set G)) (hB : g ∈ Subgroup.normalizer (B : Set G)) :
    g ∈ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hA hB ⊢
  rw [Subgroup.map_sup, hA, hB]

omit [Finite G] in
theorem mem_normalizer_commutator {g : G} {A B : Subgroup G}
    (hA : g ∈ Subgroup.normalizer (A : Set G)) (hB : g ∈ Subgroup.normalizer (B : Set G)) :
    g ∈ Subgroup.normalizer ((⁅A, B⁆ : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hA hB ⊢
  rw [Subgroup.map_commutator, hA, hB]

omit [Finite G] in
theorem normalizer_le_normalizer_oPrimeResidualOf' (p : ℕ) (X : Subgroup G) :
    Subgroup.normalizer (X : Set G) ≤ Subgroup.normalizer (oPrimeResidualOf p X : Set G) := by
  have key : ∀ g ∈ Subgroup.normalizer (X : Set G), ∀ y ∈ oPrimeResidualOf p X,
      g * y * g⁻¹ ∈ oPrimeResidualOf p X := by
    intro g hg y hy
    induction hy using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨hxX, k, hk⟩ := hx
      refine Subgroup.subset_closure ⟨(Subgroup.mem_normalizer_iff.mp hg x).mp hxX, k, ?_⟩
      rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
      exact hk
    | one => simp
    | mul x y _ _ ihx ihy => simpa [mul_assoc] using (oPrimeResidualOf p X).mul_mem ihx ihy
    | inv x _ ih =>
      have e : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
      rw [e]
      exact (oPrimeResidualOf p X).inv_mem ih
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro y
  exact ⟨fun hy => key g hg y hy, fun hy => by
    have := key g⁻¹ (inv_mem hg) _ hy
    simpa [mul_assoc] using this⟩

theorem Sgp153_le_I (c : Ctx15332 T Mc M V₁ V₂ Yp I L t) : Sgp153 T V₁ ≤ I :=
  le_sup_right.trans c.ctx.inH.1.1

theorem I_le_normalizer_UL (c : Ctx15332 T Mc M V₁ V₂ Yp I L t) :
    I ≤ Subgroup.normalizer (UL153 T I L : Set G) :=
  fun _ hg => mem_normalizer_commutator (le_normalizer_conjClosure _ I hg) (c.c27.normal hg)

theorem UI_le_pCoreOf (c : Ctx15332 T Mc M V₁ V₂ Yp I L t) : UI153 T I ≤ pCoreOf 2 I := by
  have hS : Sgp153 T V₁ ≤ I := Sgp153_le_I c
  have hO : pCoreOf 2 I ≤ T := (S153D.pCoreOf_le_Sgp153' c.facts.toFacts153).trans inf_le_left
  have hV₁T : V₁ ≤ T := c.ctx.hyp.decomp.le₁.trans c.ctx.hyp.hyp.VZ_le_T
  refine conjClosure_le fun g hg z hz => ?_
  obtain ⟨hzT, hzC, -⟩ := mem_quasithinOmegaOneCenter_iff.mp hz
  have hzS : z ∈ Sgp153 T V₁ :=
    ⟨hzT, Subgroup.centralizer_le_normalizer _ (Subgroup.centralizer_le hV₁T hzC)⟩
  have hzO : z ∈ pCoreOf 2 I := by
    refine c.ctx.charTwo ⟨hS hzS, ?_⟩
    show z ∈ Subgroup.centralizer (pCoreOf 2 I : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact Subgroup.mem_centralizer_iff.mp hzC y (hO hy)
  exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 I hg) z).mp hzO

theorem L_le_I (c : Ctx15332 T Mc M V₁ V₂ Yp I L t) : L ≤ I :=
  le_of_mem_cComp (S153D.mem_cComp_of_mem_cComp_thompsonJ c.conc.1)

theorem UL_le_Sgp153 (c : Ctx15332 T Mc M V₁ V₂ Yp I L t) : UL153 T I L ≤ Sgp153 T V₁ := by
  have hLU : L ≤ Subgroup.normalizer (UI153 T I : Set G) :=
    (L_le_I c).trans (le_normalizer_conjClosure _ I)
  have hUL : UL153 T I L ≤ UI153 T I := Subgroup.le_normalizer_iff_commutator_le_left.mp hLU
  exact hUL.trans ((UI_le_pCoreOf c).trans (S153D.pCoreOf_le_Sgp153' c.facts.toFacts153))

theorem T_le_normalizer_X (c : Ctx15332 T Mc M V₁ V₂ Yp I L t) :
    T ≤ Subgroup.normalizer (X153 T M V₁ : Set G) := by
  have hh := c.ctx.hyp
  have hTS : T ≤ Subgroup.normalizer (Sgp153 T V₁ : Set G) :=
    Hyp153.T_le_normalizer_Sgp153 hh.hyp hh.decomp
  have hTV : T ≤ Subgroup.normalizer (VZ T M : Set G) := hh.hyp.T_le.trans hh.hyp.le_normalizer
  have hTZ : T ≤ Subgroup.normalizer (ZS153 T M V₁ : Set G) := fun g hg =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hTV hg, normalizer_le_normalizer_centralizer _ (hTS hg)⟩
  exact fun g hg => normalizer_le_normalizer_oPrimeResidualOf' 3 _
    (normalizer_le_normalizer_centralizer _ (hTZ hg))

omit [Finite G] in
theorem mem_centralizer_sup {x : G} {A B : Subgroup G}
    (hA : x ∈ Subgroup.centralizer (A : Set G)) (hB : x ∈ Subgroup.centralizer (B : Set G)) :
    x ∈ Subgroup.centralizer ((A ⊔ B : Subgroup G) : Set G) := by
  have h : A ⊔ B ≤ Subgroup.centralizer ({x} : Set G) := by
    refine sup_le (fun a ha => ?_) (fun b hb => ?_)
    · rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff.mp hh]
      exact (Subgroup.mem_centralizer_iff.mp hA a ha).symm
    · rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff.mp hh]
      exact (Subgroup.mem_centralizer_iff.mp hB b hb).symm
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact (Subgroup.mem_centralizer_iff.mp (h hy) x rfl).symm

omit [Finite G] in
theorem commutator_mem_centralizer_of_left {a b : G} {U : Subgroup G}
    (ha : a ∈ Subgroup.centralizer (U : Set G)) (hb : b ∈ Subgroup.normalizer (U : Set G)) :
    ⁅a, b⁆ ∈ Subgroup.centralizer (U : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  have hbinv : b⁻¹ * u * b ∈ U := by
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem hb) u).mp hu
    simpa using this
  have e1 : a⁻¹ * (b⁻¹ * u * b) * a = b⁻¹ * u * b := by
    have := Subgroup.mem_centralizer_iff.mp ha _ hbinv
    calc a⁻¹ * (b⁻¹ * u * b) * a = a⁻¹ * ((b⁻¹ * u * b) * a) := by group
      _ = a⁻¹ * (a * (b⁻¹ * u * b)) := by rw [this]
      _ = b⁻¹ * u * b := by group
  have e2 : a * u * a⁻¹ = u := by
    have := Subgroup.mem_centralizer_iff.mp ha u hu
    calc a * u * a⁻¹ = (a * u) * a⁻¹ := rfl
      _ = (u * a) * a⁻¹ := by rw [this]
      _ = u := by group
  have key : (a * b * a⁻¹ * b⁻¹) * u * (a * b * a⁻¹ * b⁻¹)⁻¹ = u := by
    calc (a * b * a⁻¹ * b⁻¹) * u * (a * b * a⁻¹ * b⁻¹)⁻¹
        = a * b * (a⁻¹ * (b⁻¹ * u * b) * a) * b⁻¹ * a⁻¹ := by group
      _ = a * b * (b⁻¹ * u * b) * b⁻¹ * a⁻¹ := by rw [e1]
      _ = a * u * a⁻¹ := by group
      _ = u := e2
  rw [commutatorElement_def]
  exact (mul_inv_eq_iff_eq_mul.mp key).symm

omit [Finite G] in
theorem commutator_mem_centralizer_of_right {a b : G} {U : Subgroup G}
    (ha : a ∈ Subgroup.normalizer (U : Set G)) (hb : b ∈ Subgroup.centralizer (U : Set G)) :
    ⁅a, b⁆ ∈ Subgroup.centralizer (U : Set G) := by
  have h := commutator_mem_centralizer_of_left (U := U) hb ha
  have e : ⁅a, b⁆ = ⁅b, a⁆⁻¹ := (commutatorElement_inv b a).symm
  rw [e]
  exact inv_mem h

theorem Sgp153_le_normalizer_ULt (c : Ctx15332 T Mc M V₁ V₂ Yp I L t) {t' : G} (ht' : t' ∈ T) :
    Sgp153 T V₁ ≤ Subgroup.normalizer ((conjBy153 t' (UL153 T I L) : Subgroup G) : Set G) := by
  have hh := c.ctx.hyp
  have hTS : T ≤ Subgroup.normalizer (Sgp153 T V₁ : Set G) :=
    Hyp153.T_le_normalizer_Sgp153 hh.hyp hh.decomp
  have hSUL : Sgp153 T V₁ ≤ Subgroup.normalizer (UL153 T I L : Set G) :=
    (Sgp153_le_I c).trans (I_le_normalizer_UL c)
  intro g hg
  refine mem_normalizer_conjBy (hSUL ?_)
  have := (Subgroup.mem_normalizer_iff.mp (hTS (inv_mem ht')) g).mp hg
  simpa using this

theorem clause32Six_of_P (c : Ctx15332 T Mc M V₁ V₂ Yp I L t) (hP : Clause32SixP T M V₁ I L) :
    ∀ t' ∈ T, t' ∉ Sgp153 T V₁ →
      (pCoreOf 2 (X153 T M V₁ ⊔ Sgp153 T V₁) =
          (Sgp153 T V₁ ⊓ Subgroup.centralizer (UL153 T I L : Set G)) ⊔
            (Sgp153 T V₁ ⊓ Subgroup.centralizer (conjBy153 t' (UL153 T I L) : Set G)) ∧
        ⁅Sgp153 T V₁ ⊓ Subgroup.centralizer (UL153 T I L : Set G),
            Sgp153 T V₁ ⊓ Subgroup.centralizer (conjBy153 t' (UL153 T I L) : Set G)⁆ ≤
          Subgroup.centralizer ((UL153 T I L ⊔ conjBy153 t' (UL153 T I L) : Subgroup G) : Set G)) := by
  intro t' ht' hnS
  refine ⟨hP t' ht' hnS, ?_⟩
  have hSUL : Sgp153 T V₁ ≤ Subgroup.normalizer (UL153 T I L : Set G) :=
    (Sgp153_le_I c).trans (I_le_normalizer_UL c)
  have hSULt := Sgp153_le_normalizer_ULt c ht'
  rw [Subgroup.commutator_le]
  rintro a ⟨haS, haC⟩ b ⟨hbS, hbC⟩
  exact mem_centralizer_sup (commutator_mem_centralizer_of_left haC (hSUL hbS))
    (commutator_mem_centralizer_of_right (hSULt haS) hbC)

theorem clause32Five_of_inter (c : Ctx15332 T Mc M V₁ V₂ Yp I L t) (h4 : Clause32Four T M V₁ I L)
    (hinter : Clause32FiveInter T V₁ I L) : Clause32Five T M V₁ I L := by
  intro t' ht' hnS
  have hh := c.ctx.hyp
  have hint := hinter t' ht' hnS
  have hTS : T ≤ Subgroup.normalizer (Sgp153 T V₁ : Set G) :=
    Hyp153.T_le_normalizer_Sgp153 hh.hyp hh.decomp
  have hSUL : Sgp153 T V₁ ≤ Subgroup.normalizer (UL153 T I L : Set G) :=
    (Sgp153_le_I c).trans (I_le_normalizer_UL c)
  have hSULt := Sgp153_le_normalizer_ULt c ht'
  have hULS : UL153 T I L ≤ Sgp153 T V₁ := UL_le_Sgp153 c
  have hULtS : conjBy153 t' (UL153 T I L) ≤ Sgp153 T V₁ := by
    rintro x ⟨u, hu, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp (hTS ht') u).mp (hULS hu)
  obtain ⟨K, hKL, -, -, hX⟩ := h4
  have hXL : X153 T M V₁ ≤ L :=
    hX ▸ (((Subgroup.closure_le _).mpr fun x hx => hx.1 : oPrimeResidualOf 3 K ≤ K).trans hKL)
  refine ⟨?_, hint, ?_⟩
  · refine le_bot_iff.mp (hint ▸ le_inf ?_ ?_)
    · exact Subgroup.le_normalizer_iff_commutator_le_left.mp (hULtS.trans hSUL)
    · rw [Subgroup.commutator_comm]
      exact Subgroup.le_normalizer_iff_commutator_le_left.mp (hULS.trans hSULt)
  · have hTX := T_le_normalizer_X c
    have hTXS : T ≤ Subgroup.normalizer ((X153 T M V₁ ⊔ Sgp153 T V₁ : Subgroup G) : Set G) :=
      fun g hg => mem_normalizer_sup (hTX hg) (hTS hg)
    intro g hg
    have hgI : g ∈ I := (sup_le (hXL.trans (L_le_I c)) (Sgp153_le_I c)) hg
    have hN1 : g ∈ Subgroup.normalizer (UL153 T I L : Set G) := I_le_normalizer_UL c hgI
    have hN2 : g ∈ Subgroup.normalizer ((conjBy153 t' (UL153 T I L) : Subgroup G) : Set G) := by
      refine mem_normalizer_conjBy ?_
      have h1 : t'⁻¹ * g * t' ∈ X153 T M V₁ ⊔ Sgp153 T V₁ := by
        have := (Subgroup.mem_normalizer_iff.mp (hTXS (inv_mem ht')) g).mp hg
        simpa using this
      exact I_le_normalizer_UL c ((sup_le (hXL.trans (L_le_I c)) (Sgp153_le_I c)) h1)
    exact mem_normalizer_sup hN1 hN2

end Routine

theorem input15332_of_named_inputs (hP : Input32Preamble) (h1 : Input32One) (h2 : Input32Two)
    (h3 : Input32Three) (h4 : Input32Four) (h5 : Input32FiveInter) (h6 : Input32SixP) :
    Input15332 := by
  intro G _ _ T Mc M V₁ V₂ Yp I L t c
  have hpre := hP G T Mc M V₁ V₂ Yp I L t c
  have c1 := h1 G T Mc M V₁ V₂ Yp I L t c hpre
  have c2 := h2 G T Mc M V₁ V₂ Yp I L t c c1
  have c3 := h3 G T Mc M V₁ V₂ Yp I L t c c1 c2
  have c4 := h4 G T Mc M V₁ V₂ Yp I L t c c1 c3
  have c5 := clause32Five_of_inter c c4 (h5 G T Mc M V₁ V₂ Yp I L t c c1 c2 c3 c4)
  have c6 := clause32Six_of_P c (h6 G T Mc M V₁ V₂ Yp I L t c hpre c1 c4 c5)
  exact ⟨c1, c2, c3, c4, c5, c6⟩

end S153H

end CFSG.Quasithin
