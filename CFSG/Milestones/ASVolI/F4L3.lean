module

public import CFSG.Milestones.ASVolI.F4
public import CFSG.Quasithin.Vol2.GoldschmidtF431L3LieOutModel
import all CFSG.Milestones.ASVolI.F4
public import CFSG.GH74.QTGen4.DSGen4.L34Generic
public import CFSG.RankThree.PartOne.KC.LinearSubfieldPointwise
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InComplement
public import CFSG.Quasithin.Vol2.GoldschmidtF431F45L3Main
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42Am

public section

namespace CFSG.ASVolI

section Y1

open CFSG.Open
open CFSG.ASVolI.ChF

open CFSG.ASVolI.ChF.ClassicalRoots CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.QuasithinUnique.Setup.X7a

theorem burnsideF4d_Y1_mem_rawStabilizer {index : Type} [Fintype index] [DecidableEq index]
    {K : Type} [Field K] (space : Set (index → K)) (g : GL index K) :
    g ∈ rawStabilizer space ↔
      ∀ vector : index → K, (g : Matrix index index K).mulVec vector ∈ space ↔ vector ∈ space := by
  let S : Subgroup (GL index K) :=
    { carrier := {actor | ∀ vector : index → K,
        (actor : Matrix index index K).mulVec vector ∈ space ↔ vector ∈ space}
      one_mem' := by
        intro vector
        simp
      mul_mem' := by
        intro a b ha hb vector
        have h1 := ha ((b : Matrix index index K).mulVec vector)
        have h2 := hb vector
        rw [Units.val_mul, ← Matrix.mulVec_mulVec]
        exact h1.trans h2
      inv_mem' := by
        intro a ha vector
        have h1 := ha (((a⁻¹ : GL index K) : Matrix index index K).mulVec vector)
        rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec] at h1
        exact h1.symm }
  have hS : rawStabilizer space = S := Subgroup.closure_eq S
  rw [hS]
  exact Iff.rfl

theorem burnsideF4d_Y1_mem_stabilizer_iff {n : ℕ} {K : Type} [Field K]
    (W : Submodule K (Fin n → K)) (A : Matrix.SpecialLinearGroup (Fin n) K) :
    A ∈ stabilizer W ↔
      ∀ v : Fin n → K, (A : Matrix (Fin n) (Fin n) K).mulVec v ∈ W ↔ v ∈ W := by
  have hinv : ((A⁻¹ : Matrix.SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      (A : Matrix (Fin n) (Fin n) K) = 1 := coe_inv_mul_coe A
  have hmul : (A : Matrix (Fin n) (Fin n) K) *
      ((A⁻¹ : Matrix.SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  rw [mem_stabilizer]
  constructor
  · intro h v
    constructor
    · intro hv
      rw [← h] at hv
      obtain ⟨w, hw, hwv⟩ := hv
      have h2 : (A : Matrix (Fin n) (Fin n) K).mulVec w = (A : Matrix (Fin n) (Fin n) K).mulVec v :=
        hwv
      have : w = v := by
        calc w = ((A⁻¹ : Matrix.SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K).mulVec
              ((A : Matrix (Fin n) (Fin n) K).mulVec w) := by
              rw [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
          _ = ((A⁻¹ : Matrix.SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K).mulVec
              ((A : Matrix (Fin n) (Fin n) K).mulVec v) := by rw [h2]
          _ = v := by rw [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
      rw [this] at hw
      exact hw
    · intro hv
      rw [← h]
      exact ⟨v, hv, rfl⟩
  · intro h
    ext x
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact (h w).2 hw
    · intro hx
      have hv : ((A⁻¹ : Matrix.SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K).mulVec x
          ∈ W := by
        refine (h _).1 ?_
        rw [Matrix.mulVec_mulVec, hmul, Matrix.one_mulVec]
        exact hx
      refine ⟨_, hv, ?_⟩
      show (A : Matrix (Fin n) (Fin n) K).mulVec
        (((A⁻¹ : Matrix.SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K).mulVec x) = x
      rw [Matrix.mulVec_mulVec, hmul, Matrix.one_mulVec]

theorem burnsideF4d_Y1_coordinateSpace_flag {K : Type} [Field K] (i : ℕ) (v : Fin 3 → K) :
    v ∈ coordinateSpace ({p : Fin 3 | (p : ℕ) < i} : Set (Fin 3)) ↔ v ∈ flagSpace 3 K i := by
  rw [mem_flagSpace]
  simp only [coordinateSpace, Set.mem_setOf_eq, not_lt]

theorem burnsideF4d_Y1_image_one {index : Type} [Fintype index] [DecidableEq index] {K : Type}
    [Field K] (S : Set (index → K)) :
    (fun vector => ((1 : GL index K) : Matrix index index K).mulVec vector) '' S = S := by
  simp

private theorem burnsideF4d_Y1_comap_nativeParabolic (q : ℕ) (K : Type) [Field K]
    (basis : GL (Fin 3) K) (hb : basis = 1) (b : Bool) :
    (nativeParabolic .L3 q K basis b).comap
        (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 K).toMonoidHom =
      Q3 K (if b then 1 else 0) := by
  subst hb
  ext A
  have h1 : A ∈ (nativeParabolic .L3 q K 1 b).comap
        (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 K).toMonoidHom ↔
      ((CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 K A : GL (Fin 3) K)) ∈
        rawStabilizer ((fun vector =>
            ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec vector) ''
          coordinateSpace (if b then flagTwo .L3 else flagOne .L3 : Set (Fin 3))) :=
    Iff.rfl
  refine h1.trans ?_
  rw [burnsideF4d_Y1_mem_rawStabilizer, burnsideF4d_Y1_image_one, Q3,
    burnsideF4d_Y1_mem_stabilizer_iff]
  have key : ∀ (S : Set (Fin 3)) (i : ℕ), S = {p : Fin 3 | (p : ℕ) < i} →
      ((∀ v : Fin 3 → K, (A : Matrix (Fin 3) (Fin 3) K).mulVec v ∈ coordinateSpace S ↔
          v ∈ coordinateSpace S) ↔
        ∀ v : Fin 3 → K, (A : Matrix (Fin 3) (Fin 3) K).mulVec v ∈ flagSpace 3 K i ↔
          v ∈ flagSpace 3 K i) := by
    intro S i hS
    subst hS
    simp only [burnsideF4d_Y1_coordinateSpace_flag]
  cases b
  · exact key _ 1 (by ext p; simp [flagOne] <;> omega)
  · exact key _ 2 (by ext p; simp [flagTwo] <;> omega)

private noncomputable def burnsideF4d_Y1_psi {f : ℕ} {H : Type} [Group H]
    (marking : ClassicalRoots.Marking .L3 2 f H) : H ≃* projectiveSL 3 marking.field :=
  marking.identification.symm.trans
    (CFSG.QuasithinUnique.Id2519.projectiveSLEquivStatedProj 3 marking.field).symm

private theorem burnsideF4d_Y1_psi_transport {f : ℕ} {H : Type} [Group H]
    (marking : ClassicalRoots.Marking .L3 2 f H)
    (A : Matrix.SpecialLinearGroup (Fin 3) marking.field) :
    burnsideF4d_Y1_psi marking (marking.transport
        (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 marking.field A)) =
      proj 3 marking.field A := by
  have h1 : CFSG.QuasithinUnique.Id2519.projectiveSLEquivStatedProj 3 marking.field
      (proj 3 marking.field A) =
      (QuotientGroup.mk
        (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 marking.field A) :
        StatedProj (StatedSL 3 marking.field)) := rfl
  show (CFSG.QuasithinUnique.Id2519.projectiveSLEquivStatedProj 3 marking.field).symm
      (marking.identification.symm (marking.identification (QuotientGroup.mk _))) = _
  rw [MulEquiv.symm_apply_apply]
  exact (MulEquiv.symm_apply_eq _).2 h1.symm

private theorem burnsideF4d_Y1_map_parabolic {f : ℕ} {H : Type} [Group H]
    (marking : ClassicalRoots.Marking .L3 2 f H) (b : Bool) :
    (marking.parabolic b).map (burnsideF4d_Y1_psi marking).toMonoidHom =
      (Q3 marking.field (if b then 1 else 0)).map (proj 3 marking.field) := by
  have hbasis : marking.basis = 1 := marking.basis_compatible
  have key := burnsideF4d_Y1_comap_nativeParabolic (2 ^ f) marking.field marking.basis hbasis b
  have hsurj := (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3
    marking.field).surjective
  ext x
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    obtain ⟨A, rfl⟩ := hsurj z
    refine ⟨A, ?_, (burnsideF4d_Y1_psi_transport marking A).symm⟩
    rw [← key]
    exact hz
  · rintro ⟨A, hA, rfl⟩
    rw [← key] at hA
    exact ⟨marking.transport (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3
      marking.field A), ⟨_, hA, rfl⟩, burnsideF4d_Y1_psi_transport marking A⟩

theorem burnsideF4d_Y1_noNormalTwo {F : Type} [Field F] [Finite F] :
    ∀ P : Subgroup (projectiveSL 3 F), P.Normal → IsPGroup 2 P → P = ⊥ := by
  intro P hP hp
  have hsimple : IsSimpleGroup (projectiveSL 3 F) :=
    CFSG.RankThree.PartOne.KCLinearSubfield.isSimpleGroup_projectiveSL (n := 3) (K := F) le_rfl
  rcases hP.eq_bot_or_eq_top with h | h
  · exact h
  · exfalso
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hp' : IsPGroup 2 (projectiveSL 3 F) := by
      rw [h] at hp
      exact hp.of_equiv Subgroup.topEquiv
    have hnt : Nontrivial (projectiveSL 3 F) := hsimple.toNontrivial
    have hc := hp'.center_nontrivial
    obtain ⟨⟨z, hz⟩, hz1⟩ := exists_ne (1 : Subgroup.center (projectiveSL 3 F))
    apply hz1
    apply Subtype.ext
    exact CFSG.QuasithinUnique.Fin257.L3.center_trivial_M z
      (fun y => (Subgroup.mem_center_iff.mp hz y).symm)

theorem burnsideF4d_Y1_yam_of_marking {f : ℕ} {H : Type} [Group H]
    (marking : ClassicalRoots.Marking .L3 2 f H) :
    ∃ TD : Subgroup H, CFSG.Quasithin.IsYAmalgamPair TD (marking.parabolic false)
      (marking.parabolic true) := by
  have hcard : Nat.card marking.field = 2 ^ f := by
    have := marking.field_card
    simpa using this
  have hchar : CharP marking.field 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have := Fintype.ofFinite marking.field
    exact charP_of_card_eq_prime_pow (p := 2) (f := f)
      (by rw [← Nat.card_eq_fintype_card]; exact hcard)
  have hBD := CFSG.QuasithinUnique.Borel252.L3.borelData_L3 (F := marking.field)
  have hOG := CFSG.QuasithinUnique.Borel252.L3.overgroupData_L3 (F := marking.field)
  have hY := CFSG.GH74.QTGen4.DSGen4.L34.isYAmalgamPair_of_borelData hBD
    burnsideF4d_Y1_noNormalTwo
  have e1 := hOG.eq_of_between hBD.lt₁ hBD.lt_top₁
  have e2 := hOG.eq_of_between hBD.lt₂ hBD.lt_top₂
  have hne := hBD.ne_norm
  have hY' : CFSG.Quasithin.IsYAmalgamPair (projUnitriangular 3 marking.field)
      ((Q3 marking.field 0).map (proj 3 marking.field))
      ((Q3 marking.field 1).map (proj 3 marking.field)) := by
    rcases e1 with e1 | e1 <;> rcases e2 with e2 | e2
    · exact absurd (e1.trans e2.symm) hne
    · rw [e1, e2] at hY
      exact hY
    · rw [e1, e2] at hY
      exact ⟨hY.1, hY.2.1.symm, fun M => (hY.2.2 M).trans or_comm⟩
    · exact absurd (e1.trans e2.symm) hne
  have hm0 := burnsideF4d_Y1_map_parabolic marking false
  have hm1 := burnsideF4d_Y1_map_parabolic marking true
  simp only [Bool.false_eq_true, if_false, if_true] at hm0 hm1
  refine ⟨(projUnitriangular 3 marking.field).map
    (burnsideF4d_Y1_psi marking).symm.toMonoidHom, ?_⟩
  have := hY'.map (burnsideF4d_Y1_psi marking).symm
  have hsymm : ∀ P : Subgroup H, ((P.map (burnsideF4d_Y1_psi marking).toMonoidHom).map
      (burnsideF4d_Y1_psi marking).symm.toMonoidHom) = P := by
    intro P
    ext x
    constructor
    · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
      simpa using hz
    · intro hx
      exact ⟨(burnsideF4d_Y1_psi marking) x, ⟨x, hx, rfl⟩, by simp⟩
  have h0 : Subgroup.map (burnsideF4d_Y1_psi marking).symm.toMonoidHom
      ((Q3 marking.field 0).map (proj 3 marking.field)) = marking.parabolic false := by
    rw [← hm0]
    exact hsymm _
  have h1 : Subgroup.map (burnsideF4d_Y1_psi marking).symm.toMonoidHom
      ((Q3 marking.field 1).map (proj 3 marking.field)) = marking.parabolic true := by
    rw [← hm1]
    exact hsymm _
  rw [h0, h1] at this
  exact this

theorem burnsideF4d_Y1_marking {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (h : CFSG.ASVolI.ChF.HypF_4_4g .L3 2 f Gp M₁ M₂) :
    ∃ marking : ClassicalRoots.Marking .L3 2 f Gp,
      M₁.subgroupOf Gp = marking.parabolic false ∧ M₂.subgroupOf Gp = marking.parabolic true := by
  obtain ⟨chart, -, hpts, hlines⟩ := h.lie_amalgam
  rcases chart.coordinates with
    ⟨c, hk, marking, h1, h2, h3, h4, h5⟩ | ⟨hk, -⟩ | ⟨hk, -⟩ | ⟨hk, -⟩ |
    ⟨-, exponent, K, fK, finK, charK, scope, ⟨hk, -⟩ | ⟨hk, -⟩⟩
  · have hc : c = .L3 := by
      cases c
      · rfl
      all_goals exact absurd hk (by decide)
    subst hc
    refine ⟨marking, ?_, ?_⟩
    · have : Gp ⊓ M₁ = (marking.parabolic false).map Gp.subtype := hpts.trans h2
      rw [← Subgroup.inf_subgroupOf_left M₁ Gp, this]
      exact Subgroup.comap_map_eq_self_of_injective Gp.subtype_injective _
    · have : Gp ⊓ M₂ = (marking.parabolic true).map Gp.subtype := hlines.trans h3
      rw [← Subgroup.inf_subgroupOf_left M₂ Gp, this]
      exact Subgroup.comap_map_eq_self_of_injective Gp.subtype_injective _
  all_goals exact absurd hk (by decide)

theorem burnsideF4d_Y1_lieModel {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (h : CFSG.ASVolI.ChF.HypF_4_4g .L3 2 f Gp M₁ M₂) :
    CFSG.Blueprint.LieModel (↥Gp) CFSG.Assembly.LowTwoRank.StatedLieTag.PSL 3 2 f := by
  obtain ⟨hp, hf, K, hK, hKfin, hcard, he⟩ := h.model
  refine (CFSG.Blueprint.LieModel.classical_iff (t := .PSL) (by decide)).2 ?_
  exact ⟨⟨hp, hf, by norm_num, by simp, by simp⟩, K, hK, hKfin, hcard, he⟩

theorem burnsideF4d_Y1_simple {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (h : CFSG.ASVolI.ChF.HypF_4_4g .L3 2 f Gp M₁ M₂) : IsSimpleGroup ↥Gp := by
  obtain ⟨-, -, K, hK, hKfin, -, ⟨e⟩⟩ := h.model
  haveI : IsSimpleGroup (projectiveSL 3 K) :=
    CFSG.RankThree.PartOne.KCLinearSubfield.isSimpleGroup_projectiveSL (n := 3) (K := K) le_rfl
  exact (e.trans (CFSG.QuasithinUnique.Id2519.projectiveSLEquivStatedProj 3 K).symm).isSimpleGroup

theorem burnsideF4d_Y1_yam {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (h : CFSG.ASVolI.ChF.HypF_4_4g .L3 2 f Gp M₁ M₂) :
    ∃ TD : Subgroup ↥Gp, CFSG.Quasithin.IsYAmalgamPair TD (M₁.subgroupOf Gp)
      (M₂.subgroupOf Gp) := by
  obtain ⟨marking, h1, h2⟩ := burnsideF4d_Y1_marking h
  rw [h1, h2]
  exact burnsideF4d_Y1_yam_of_marking marking

end Y1

section F4dBaseRest

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431

section Conj

variable {E : Type} [Group E] {Gp : Subgroup E}

noncomputable abbrev burnsideF4d_rho (Gp : Subgroup E) [Gp.Normal] : E →* MulAut ↥Gp :=
  MulAut.conjNormal

theorem burnsideF4d_rho_apply [Gp.Normal] (e : E) (x : ↥Gp) :
    ((burnsideF4d_rho Gp e x : ↥Gp) : E) = e * (x : E) * e⁻¹ :=
  MulAut.conjNormal_apply e x

theorem burnsideF4d_rho_injective [Gp.Normal]
    (hc : Subgroup.centralizer (Gp : Set E) = ⊥) : Function.Injective (burnsideF4d_rho Gp) := by
  rw [injective_iff_map_eq_one]
  intro e he
  have : e ∈ Subgroup.centralizer (Gp : Set E) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have h1 := congrArg (fun φ : MulAut ↥Gp => ((φ ⟨x, hx⟩ : ↥Gp) : E)) he
    simp only [burnsideF4d_rho_apply, MulAut.one_apply] at h1
    calc x * e = (e * x * e⁻¹) * e := by rw [h1]
      _ = e * x := by group
  rw [hc] at this
  exact Subgroup.mem_bot.mp this

theorem burnsideF4d_rho_mem_autStab [Gp.Normal] (P : Subgroup E) (e : E) :
    burnsideF4d_rho Gp e ∈ autStab (P.subgroupOf Gp) ↔
      ∀ x : ↥Gp, (x : E) ∈ P ↔ e * (x : E) * e⁻¹ ∈ P := by
  show (∀ x : ↥Gp, x ∈ P.subgroupOf Gp ↔ burnsideF4d_rho Gp e x ∈ P.subgroupOf Gp) ↔ _
  simp only [Subgroup.mem_subgroupOf, burnsideF4d_rho_apply]

theorem burnsideF4d_normalizer_iff [Gp.Normal] (P : Subgroup E) (e : E) :
    e ∈ Subgroup.normalizer ((Gp ⊓ P : Subgroup E) : Set E) ↔
      ∀ x : ↥Gp, (x : E) ∈ P ↔ e * (x : E) * e⁻¹ ∈ P := by
  rw [Subgroup.mem_normalizer_iff]
  constructor
  · intro h x
    have := h (x : E)
    simp only [Subgroup.mem_inf] at this
    constructor
    · intro hx
      exact (this.mp ⟨x.2, hx⟩).2
    · intro hx
      have hG : e * (x : E) * e⁻¹ ∈ Gp := Subgroup.Normal.conj_mem inferInstance (x : E) x.2 e
      exact (this.mpr ⟨hG, hx⟩).2
  · intro h y
    simp only [Subgroup.mem_inf]
    constructor
    · rintro ⟨hy, hyP⟩
      exact ⟨Subgroup.Normal.conj_mem inferInstance y hy e, (h ⟨y, hy⟩).mp hyP⟩
    · rintro ⟨hy, hyP⟩
      have hy' : y ∈ Gp := by
        have := Subgroup.Normal.conj_mem (inferInstance : Gp.Normal) _ hy e⁻¹
        simpa [mul_assoc] using this
      exact ⟨hy', (h ⟨y, hy'⟩).mpr hyP⟩

end Conj

section SelfNorm

variable {D : Type} [Group D] [Finite D]

theorem burnsideF4d_selfNorm {TD P1 P2 : Subgroup D} (h : IsYAmalgamPair TD P1 P2) (g : D)
    (hg : ∀ x : D, x ∈ P1 ↔ g * x * g⁻¹ ∈ P1) : g ∈ P1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmax : Quasithin.IsMaximalTwoLocal P1 := ((h.2.2 P1).mpr (Or.inl rfl)).1
  obtain ⟨⟨P, hPne, hPp, hP1⟩, hmaxi⟩ := hmax
  have hPle : P ≤ P1 := hP1 ▸ Subgroup.le_normalizer
  have hPcore : P ≤ pCoreOf 2 P1 :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hPle hP1.le hPp
  have hQne : pCoreOf 2 P1 ≠ ⊥ := by
    intro hb
    rw [hb] at hPcore
    exact hPne (le_bot_iff.mp hPcore)
  have hloc : CFSG.Open.IsTwoLocal (Subgroup.normalizer (pCoreOf 2 P1 : Set D)) :=
    ⟨pCoreOf 2 P1, hQne, CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 P1, rfl⟩
  have heq := hmaxi _ hloc (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 P1)
  have hgN : g ∈ Subgroup.normalizer (P1 : Set D) := Subgroup.mem_normalizer_iff.mpr hg
  have := CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 P1 hgN
  rwa [heq] at this

end SelfNorm

section Ext

variable {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E} {κ : ChF.GLKind} {p f : ℕ}

theorem burnsideF4d_inf_subgroupOf (Gp M₁ M₂ : Subgroup E) :
    (M₁ ⊓ M₂).subgroupOf Gp = M₁.subgroupOf Gp ⊓ M₂.subgroupOf Gp := by
  ext x; simp [Subgroup.mem_subgroupOf]

@[expose] noncomputable def burnsideF4d_amalgamExt (hyp : ChF.HypF_4_4g κ p f Gp M₁ M₂) (TD : Subgroup ↥Gp)
    (hyam : IsYAmalgamPair TD (M₁.subgroupOf Gp) (M₂.subgroupOf Gp)) :
    LieAmalgamExt ↥Gp :=
  haveI := hyp.normal
  { Mbar := (burnsideF4d_rho Gp).range
    TD := TD
    P1 := M₁.subgroupOf Gp
    P2 := M₂.subgroupOf Gp
    inn_le := by
      rintro _ ⟨d, rfl⟩
      refine ⟨(d : E), ?_⟩
      ext x
      simp [burnsideF4d_rho_apply]
    yam := hyam
    diag := by
      rintro φ ⟨e, rfl⟩ hφ
      rw [← burnsideF4d_inf_subgroupOf, burnsideF4d_rho_mem_autStab] at hφ
      have h1 := (burnsideF4d_normalizer_iff (Gp := Gp) (M₁ ⊓ M₂) e).mpr hφ
      have h2 := hyp.dynkin e h1
      exact (burnsideF4d_rho_mem_autStab M₁ e).mpr
        ((burnsideF4d_normalizer_iff (Gp := Gp) M₁ e).mp h2) }

theorem burnsideF4d_conj_mem_iff {M : Subgroup E} {h : E} (hh : h ∈ M) (x : E) :
    h⁻¹ * x * h ∈ M ↔ x ∈ M := by
  constructor
  · intro hx
    have := M.mul_mem (M.mul_mem hh hx) (M.inv_mem hh)
    simpa [mul_assoc] using this
  · intro hx
    exact M.mul_mem (M.mul_mem (M.inv_mem hh) hx) hh

theorem burnsideF4d_rho_mem_stab_iff [Gp.Normal] (M : Subgroup E)
    (hsplit : ∀ e : E, ∃ n ∈ Gp, ∃ h ∈ M, e = n * h)
    (hself : ∀ g : ↥Gp, (∀ x : ↥Gp, x ∈ M.subgroupOf Gp ↔ g * x * g⁻¹ ∈ M.subgroupOf Gp) →
      g ∈ M.subgroupOf Gp) (e : E) :
    burnsideF4d_rho Gp e ∈ autStab (M.subgroupOf Gp) ↔ e ∈ M := by
  constructor
  · intro H
    have H' := (burnsideF4d_rho_mem_autStab M e).mp H
    obtain ⟨n, hn, h, hhM, rfl⟩ := hsplit e
    have hnM : ((⟨n, hn⟩ : ↥Gp) : E) ∈ M := by
      refine hself ⟨n, hn⟩ (fun x => ?_)
      have hy : h⁻¹ * (x : E) * h ∈ Gp := by
        have := Subgroup.Normal.conj_mem (inferInstance : Gp.Normal) _ x.2 h⁻¹
        simpa using this
      have h1 := H' ⟨_, hy⟩
      simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, InvMemClass.coe_inv]
      rw [show n * (x : E) * n⁻¹ = n * h * (h⁻¹ * (x : E) * h) * (n * h)⁻¹ by group, ← h1]
      exact (burnsideF4d_conj_mem_iff hhM _).symm
    exact M.mul_mem hnM hhM
  · intro hM
    refine (burnsideF4d_rho_mem_autStab M e).mpr (fun x => ?_)
    constructor
    · intro hx
      exact M.mul_mem (M.mul_mem hM hx) (M.inv_mem hM)
    · intro hx
      have := M.mul_mem (M.mul_mem (M.inv_mem hM) hx) hM
      simpa [mul_assoc] using this

theorem burnsideF4d_N1_eq [Finite E] [Gp.Normal] (hyp : ChF.HypF_4_4g κ p f Gp M₁ M₂)
    {TD : Subgroup ↥Gp} (hyam : IsYAmalgamPair TD (M₁.subgroupOf Gp) (M₂.subgroupOf Gp)) :
    (burnsideF4d_rho Gp).range ⊓ autStab (M₁.subgroupOf Gp) = M₁.map (burnsideF4d_rho Gp) := by
  have hiff := burnsideF4d_rho_mem_stab_iff (Gp := Gp) M₁
    (fun e => by
      obtain ⟨n, hn, h, hh, he⟩ := hyp.split e
      exact ⟨n, hn, h, hh.1, he⟩)
    (fun g hg => burnsideF4d_selfNorm hyam g hg)
  ext φ
  constructor
  · rintro ⟨⟨e, rfl⟩, h2⟩
    exact ⟨e, (hiff e).mp h2, rfl⟩
  · rintro ⟨e, he, rfl⟩
    exact ⟨⟨e, rfl⟩, (hiff e).mpr he⟩

theorem burnsideF4d_N2_eq [Finite E] [Gp.Normal] (hyp : ChF.HypF_4_4g κ p f Gp M₁ M₂)
    {TD : Subgroup ↥Gp} (hyam : IsYAmalgamPair TD (M₁.subgroupOf Gp) (M₂.subgroupOf Gp)) :
    (burnsideF4d_rho Gp).range ⊓ autStab (M₂.subgroupOf Gp) = M₂.map (burnsideF4d_rho Gp) := by
  have hyam' : IsYAmalgamPair TD (M₂.subgroupOf Gp) (M₁.subgroupOf Gp) := by
    refine ⟨hyam.1, hyam.2.1.symm, fun X => ?_⟩
    rw [hyam.2.2 X, or_comm]
  have hiff := burnsideF4d_rho_mem_stab_iff (Gp := Gp) M₂
    (fun e => by
      obtain ⟨n, hn, h, hh, he⟩ := hyp.split e
      exact ⟨n, hn, h, hh.2, he⟩)
    (fun g hg => burnsideF4d_selfNorm hyam' g hg)
  ext φ
  constructor
  · rintro ⟨⟨e, rfl⟩, h2⟩
    exact ⟨e, (hiff e).mp h2, rfl⟩
  · rintro ⟨e, he, rfl⟩
    exact ⟨⟨e, rfl⟩, (hiff e).mpr he⟩

@[expose] noncomputable def burnsideF4d_isoSub {A B : Type} [Group A] [Group B] (g : A →* B)
    (hg : Function.Injective g) (H : Subgroup B) (h : g.range = H) : A ≃* ↥H :=
  (MonoidHom.ofInjective hg).trans (MulEquiv.subgroupCongr h)

theorem burnsideF4d_K_eq [Finite E] (hyp : ChF.HypF_4_4g κ p f Gp M₁ M₂) {TD : Subgroup ↥Gp}
    (hyam : IsYAmalgamPair TD (M₁.subgroupOf Gp) (M₂.subgroupOf Gp)) :
    (burnsideF4d_amalgamExt hyp TD hyam).K = (haveI := hyp.normal; burnsideF4d_rho Gp).range := by
  haveI := hyp.normal
  have h1 := burnsideF4d_N1_eq hyp hyam
  have h2 := burnsideF4d_N2_eq hyp hyam
  show (burnsideF4d_rho Gp).range ⊓ autStab (M₁.subgroupOf Gp) ⊔
    (burnsideF4d_rho Gp).range ⊓ autStab (M₂.subgroupOf Gp) = _
  rw [h1, h2, ← Subgroup.map_sup, hyp.gen, ← MonoidHom.range_eq_map]

@[expose] noncomputable def burnsideF4d_lieExtE [Finite E] (hyp : ChF.HypF_4_4g κ p f Gp M₁ M₂)
    {TD : Subgroup ↥Gp} (hyam : IsYAmalgamPair TD (M₁.subgroupOf Gp) (M₂.subgroupOf Gp)) :
    LieExt ↥Gp M₁ M₂ :=
  haveI := hyp.normal
  have hinj : Function.Injective (burnsideF4d_rho Gp) :=
    burnsideF4d_rho_injective hyp.centralizer_trivial
  have h1 := burnsideF4d_N1_eq hyp hyam
  have h2 := burnsideF4d_N2_eq hyp hyam
  { toLieAmalgamExt := burnsideF4d_amalgamExt hyp TD hyam
    iso :=
      { φ1 := burnsideF4d_isoSub ((burnsideF4d_rho Gp).comp M₁.subtype)
          (hinj.comp M₁.subtype_injective) _ (by
            rw [MonoidHom.range_comp, Subgroup.range_subtype]; exact h1.symm)
        φ12 := burnsideF4d_isoSub ((burnsideF4d_rho Gp).comp (M₁ ⊓ M₂).subtype)
          (hinj.comp (M₁ ⊓ M₂).subtype_injective) _ (by
            rw [MonoidHom.range_comp, Subgroup.range_subtype, Subgroup.map_inf _ _ _ hinj]
            exact (congrArg₂ (· ⊓ ·) h1 h2).symm)
        φ2 := burnsideF4d_isoSub ((burnsideF4d_rho Gp).comp M₂.subtype)
          (hinj.comp M₂.subtype_injective) _ (by
            rw [MonoidHom.range_comp, Subgroup.range_subtype]; exact h2.symm)
        comm1 := fun g => rfl
        comm2 := fun g => rfl } }

end Ext

section MSide

open CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion CFSG.ASVolI.ChF
  CFSG.Quasithin.H13.F431.L3

variable {E : Type} [Group E] {M₁ M₂ : Subgroup E} {Y : Type} [Group Y] {M : Type} [Group M]

@[expose] noncomputable def burnsideF4d_bOne (β : Cpl M₁ M₂ Y) (ε : Y →* M) : ↥M₁ →* M :=
  (epsG β ε).comp (f1 (c := β))

@[expose] noncomputable def burnsideF4d_bTwo (β : Cpl M₁ M₂ Y) (ε : Y →* M) : ↥M₂ →* M :=
  (epsG β ε).comp (f2 (c := β))

@[expose] noncomputable def burnsideF4d_amalgIsoM (β : Cpl M₁ M₂ Y) (hβ : β.IsFaithful)
    (ε : Y →* M) (hε : Function.Injective (epsG β ε)) :
    AmalgIso M₁ M₂ (MiOne β ε) (MiTwo β ε) where
  b₁ := burnsideF4d_bOne β ε
  b₂ := burnsideF4d_bTwo β ε
  inj₁ := hε.comp (f1_injective β hβ)
  inj₂ := hε.comp (f2_injective β hβ)
  agree := fun g h1 h2 => by
    have e1 : β.φ1 (⟨g, h1⟩ : ↥M₁) = β.φ2 (⟨g, h2⟩ : ↥M₂) := by
      have a1 := β.comm1 (⟨g, h1, h2⟩ : ↥(M₁ ⊓ M₂))
      have a2 := β.comm2 (⟨g, h1, h2⟩ : ↥(M₁ ⊓ M₂))
      exact a1.trans a2.symm
    show epsG β ε (f1 (c := β) ⟨g, h1⟩) = epsG β ε (f2 (c := β) ⟨g, h2⟩)
    congr 1
    exact Subtype.ext e1
  range₁ := by
    show (burnsideF4d_bOne β ε).range = (f1 (c := β)).range.map (epsG β ε)
    exact MonoidHom.range_comp _ _
  range₂ := by
    show (burnsideF4d_bTwo β ε).range = (f2 (c := β)).range.map (epsG β ε)
    exact MonoidHom.range_comp _ _
  inter := fun x hx => by
    obtain ⟨_, ⟨a, rfl⟩, ha⟩ := hx.1
    obtain ⟨_, ⟨b, rfl⟩, hb⟩ := hx.2
    have hab : f1 (c := β) a = f2 (c := β) b := hε (ha.trans hb.symm)
    have hφ : β.φ1 a = β.φ2 b := congrArg Subtype.val hab
    have hmem : β.φ1 a ∈ β.φ1.range ⊓ β.φ2.range := ⟨⟨a, rfl⟩, ⟨b, hφ.symm⟩⟩
    rw [β.inter] at hmem
    obtain ⟨c0, hc⟩ := hmem
    have hca : (RankTwoAmalgam.ofSubgroups M₁ M₂).α1 c0 = a := hβ.1 (by rw [β.comm1]; exact hc)
    let c : ↥(M₁ ⊓ M₂) := c0
    refine ⟨(c : E), c.2.1, c.2.2, ?_⟩
    have h1 : (⟨(c : E), c.2.1⟩ : ↥M₁) = a := hca
    show epsG β ε (f1 (c := β) ⟨(c : E), c.2.1⟩) = x
    rw [h1]
    exact ha

end MSide

section Datum

open CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion CFSG.ASVolI.ChF
  CFSG.Quasithin.H13.F431.L3

theorem burnsideF4d_L3_datumE {f : ℕ} (hf : 2 ≤ f) {E : Type} [Group E] [Finite E]
    {Gp M₁ M₂ : Subgroup E} (hyp : HypF_4_4g .L3 2 f Gp M₁ M₂) (hodd : Odd Gp.index) :
    Nonempty (L3Datum M₁ M₂) := by
  obtain ⟨TD, hyam⟩ := burnsideF4d_Y1_yam hyp
  have hmodel := burnsideF4d_Y1_lieModel hyp
  haveI := hyp.normal
  have hinj : Function.Injective (burnsideF4d_rho Gp) :=
    burnsideF4d_rho_injective hyp.centralizer_trivial
  let X := burnsideF4d_lieExtE hyp hyam
  have hK : Nat.card ↥X.K = Nat.card E := by
    have : X.K = (burnsideF4d_rho Gp).range := burnsideF4d_K_eq hyp hyam
    rw [this, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
  have hodd' : Odd (Nat.card ↥X.K / Nat.card ↥Gp) := by
    rw [hK]
    have := Subgroup.card_mul_index Gp
    have hpos : 0 < Nat.card ↥Gp := Nat.card_pos
    rw [show Nat.card E / Nat.card ↥Gp = Gp.index by
      rw [← this, Nat.mul_div_cancel_left _ hpos]]
    exact hodd
  obtain ⟨D⟩ := f431L3Lie f hf ↥Gp hmodel X.toLieAmalgamExt hodd'
  exact D.nonempty_transport X.amalgIso

theorem burnsideF4d_L3_datumM {f : ℕ} (hf : 2 ≤ f) {E : Type} [Group E]
    {Gp M₁ M₂ : Subgroup E} {Y : Type} [Group Y] {β : Cpl M₁ M₂ Y} {M : Type} [Group M]
    {ε : Y →* M} {z : M} (hyp : HypF_4_31 .L3 f Gp M₁ M₂ β ε z) (hodd : Odd Gp.index) :
    Nonempty (L3Datum (MiOne β ε) (MiTwo β ε)) := by
  haveI := hyp.amalgam.finite
  obtain ⟨D⟩ := burnsideF4d_L3_datumE hf hyp.amalgam.toHypF_4_4g hodd
  exact D.nonempty_transport (burnsideF4d_amalgIsoM β hyp.faithful ε hyp.inj)

end Datum

section Out

open CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion CFSG.ASVolI.ChF
  CFSG.Quasithin.H13.F431.L3

theorem burnsideF4d_Out_not_mem_commutator {G : Type} [Group G] [Finite G] {M₁ M₂ : Subgroup G}
    (O : L3OutDatum M₁ M₂) {z : G}
    (hz : z ∈ centerOf O.S) (hz1 : z ≠ 1) (hC : Subgroup.centralizer ({z} : Set G) ≤ M₁) :
    O.f ∉ commutator G := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcentG := O.centZ hz hz1 hC
  have hT1 : O.T ≤ M₁ := O.T_le.trans inf_le_left
  have hzT : z ∈ O.T := O.S_le_T ((L3OutDatum.mem_centerOf.mp hz).1)
  have hTw : ∃ w ∈ centerOf O.T, w ≠ 1 := by
    have hnt : Nontrivial O.T := ⟨⟨⟨z, hzT⟩, 1, fun h => hz1 (congrArg Subtype.val h)⟩⟩
    have := O.T_pgroup.center_nontrivial
    obtain ⟨w0, hw0⟩ := exists_ne (1 : Subgroup.center O.T)
    refine ⟨((w0 : O.T) : G), L3OutDatum.mem_centerOf.mpr ⟨(w0 : O.T).2, fun s hs => ?_⟩, ?_⟩
    · have := Subgroup.mem_center_iff.mp w0.2 ⟨s, hs⟩
      exact congrArg Subtype.val this
    · intro h
      apply hw0
      apply Subtype.ext
      apply Subtype.ext
      exact h
  have hTsyl : IsSylowTwoOf O.T ⊤ :=
    isSylowTwoOf_top_of_centralizer_le ⟨hT1, O.T_pgroup, O.T_index⟩ hTw (fun w hw hw1 y hy =>
      (hcentG w (O.ZT w hw) hw1 y (Subgroup.mem_centralizer_singleton_iff.mp hy)).1)
  have hconj : ∀ x ∈ O.S, x * x = 1 → x ≠ 1 → ∃ g : G, g * z * g⁻¹ = x := by
    intro x hx hx2 hx1
    obtain ⟨m, -, hmz⟩ := O.invS x hx hx2 hx1
    have hmx1 : m * x * m⁻¹ ≠ 1 := by
      intro h; apply hx1
      have := congrArg (fun y => m⁻¹ * y * m) h
      simpa [mul_assoc] using this
    obtain ⟨b, -, hbz⟩ := O.trans z hz hz1 _ hmz hmx1
    refine ⟨m⁻¹ * b, ?_⟩
    calc m⁻¹ * b * z * (m⁻¹ * b)⁻¹ = m⁻¹ * (b * z * b⁻¹) * m := by group
      _ = m⁻¹ * (m * x * m⁻¹) * m := by rw [hbz]
      _ = x := by group
  have hTf_le : O.T ⊓ Subgroup.centralizer ({O.f} : Set G) ≤ Subgroup.centralizer ({O.f} : Set G) :=
    inf_le_right
  have hZfS : centerOf (O.T ⊓ Subgroup.centralizer ({O.f} : Set G)) ⊓
      ⁅O.T ⊓ Subgroup.centralizer ({O.f} : Set G), O.T ⊓ Subgroup.centralizer ({O.f} : Set G)⁆ ≤
      O.T ⊓ Subgroup.centralizer ({O.f} : Set G) := inf_le_left.trans inf_le_left
  have hZfw : ∃ w ∈ centerOf (O.T ⊓ Subgroup.centralizer ({O.f} : Set G)) ⊓
      ⁅O.T ⊓ Subgroup.centralizer ({O.f} : Set G), O.T ⊓ Subgroup.centralizer ({O.f} : Set G)⁆,
      w ≠ 1 := by
    obtain ⟨a, ha⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp O.Zf_ne
    refine ⟨(a : G), a.2, fun h => ha (Subtype.ext h)⟩
  have hchar : ∀ n ∈ Subgroup.centralizer ({O.f} : Set G),
      n ∈ Subgroup.normalizer ((O.T ⊓ Subgroup.centralizer ({O.f} : Set G) : Subgroup G) : Set G) →
      ∀ x ∈ centerOf (O.T ⊓ Subgroup.centralizer ({O.f} : Set G)) ⊓
        ⁅O.T ⊓ Subgroup.centralizer ({O.f} : Set G), O.T ⊓ Subgroup.centralizer ({O.f} : Set G)⁆,
        n * x * n⁻¹ ∈ centerOf (O.T ⊓ Subgroup.centralizer ({O.f} : Set G)) ⊓
        ⁅O.T ⊓ Subgroup.centralizer ({O.f} : Set G),
          O.T ⊓ Subgroup.centralizer ({O.f} : Set G)⁆ := by
    intro n _ hn x hx
    have hcn := conjSub_eq_of_mem_normalizer hn
    have e : conjSub n (centerOf (O.T ⊓ Subgroup.centralizer ({O.f} : Set G)) ⊓
        ⁅O.T ⊓ Subgroup.centralizer ({O.f} : Set G),
          O.T ⊓ Subgroup.centralizer ({O.f} : Set G)⁆) =
        centerOf (O.T ⊓ Subgroup.centralizer ({O.f} : Set G)) ⊓
        ⁅O.T ⊓ Subgroup.centralizer ({O.f} : Set G),
          O.T ⊓ Subgroup.centralizer ({O.f} : Set G)⁆ := by
      rw [conjSub_inf, ← centerOf_conjSub, ← conjSub_commutator, hcn]
    rw [← e]
    exact mul_mem_conjSub hx
  have hmax := maximal_two_of_char (S := O.T ⊓ Subgroup.centralizer ({O.f} : Set G))
    (M := M₁ ⊓ M₂ ⊓ Subgroup.centralizer ({O.f} : Set G))
    (H := Subgroup.centralizer ({O.f} : Set G)) (Z' := centerOf (O.T ⊓ Subgroup.centralizer
      ({O.f} : Set G)) ⊓ ⁅O.T ⊓ Subgroup.centralizer ({O.f} : Set G),
        O.T ⊓ Subgroup.centralizer ({O.f} : Set G)⁆)
    O.Tf_sylow hZfS hZfw hchar (fun w hw hw1 y hy hyw => ⟨hcentG w (O.Zf_le hw) hw1 y hyw, hy⟩)
  have hTfSyl : IsSylowTwoOf (O.T ⊓ Subgroup.centralizer ({O.f} : Set G))
      (Subgroup.centralizer ({O.f} : Set G)) :=
    isSylowTwoOf_of_max hTf_le (O.T_pgroup.to_le inf_le_left) hmax
  have hf1 : O.f ≠ 1 := fun h => O.f_not (h ▸ O.S.one_mem)
  have hfG : ∀ g : G, g⁻¹ * O.f * g ∉ O.S := by
    intro g hg
    have hj2 : g⁻¹ * O.f * g * (g⁻¹ * O.f * g) = 1 := by
      calc g⁻¹ * O.f * g * (g⁻¹ * O.f * g) = g⁻¹ * (O.f * O.f) * g := by group
        _ = 1 := by rw [O.f_sq]; group
    obtain ⟨h, hh⟩ := hconj _ hg hj2 (conj_ne_one' hf1)
    have hfeq : O.f = (g * h) * z * (g * h)⁻¹ := by
      calc O.f = g * (g⁻¹ * O.f * g) * g⁻¹ := by group
        _ = g * (h * z * h⁻¹) * g⁻¹ := by rw [hh]
        _ = (g * h) * z * (g * h)⁻¹ := by group
    have hPp : IsPGroup 2 (conjSub (g * h) O.S) := F7.isPGroup_conjSub O.S_pgroup
    have hPH : conjSub (g * h) O.S ≤ Subgroup.centralizer ({O.f} : Set G) := by
      intro p hp
      rw [mem_conjSub] at hp
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hc := (L3OutDatum.mem_centerOf.mp hz).2 _ hp
      calc p * O.f = (g * h) * (((g * h)⁻¹ * p * (g * h)) * z) * (g * h)⁻¹ := by rw [hfeq]; group
        _ = (g * h) * (z * ((g * h)⁻¹ * p * (g * h))) * (g * h)⁻¹ := by rw [hc]
        _ = O.f * p := by rw [hfeq]; group
    obtain ⟨x, -, hPx⟩ := F7.isSylowTwoOf_exists_conj_le hTfSyl hPH hPp
    have h1 : Nat.card (conjSub (g * h) O.S) ≤ Nat.card (conjSub x
        (O.T ⊓ Subgroup.centralizer ({O.f} : Set G))) := Subgroup.card_le_of_le hPx
    rw [card_conjSub, card_conjSub] at h1
    exact absurd O.Tf_lt (not_lt.mpr h1)
  have hT2 : Nat.Coprime 2 O.T.index := by
    have h := hTsyl.2.2
    have h' : ¬ 2 ∣ O.T.index := by
      rw [← Subgroup.relIndex_top_right]; exact h
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr h'
  have hTnorm : O.T ≤ Subgroup.normalizer (O.S : Set G) := O.T_le.trans O.H_le_normalizer_S
  have hnotcomm : O.f ∉ commutator G := by
    refine generalized_thompson_transfer_two (H := O.T) (K := O.S) hT2
      ⟨O.S_le_T, Subgroup.normal_subgroupOf_of_le_normalizer hTnorm⟩ ?_ O.f_mem O.f_not
      (orderOf_eq_prime (by rw [pow_two]; exact O.f_sq) hf1) ?_
    · exact Subgroup.commutator_le.mpr (fun x hx y hy => O.T_comm x hx y hy)
    · intro a ha
      exact O.T_cyc _ O.f_mem _ ha O.f_not (hfG a) (by rw [O.f_sq]; exact O.S.one_mem)
        (by
          have : a⁻¹ * O.f * a * (a⁻¹ * O.f * a) = 1 := by
            calc a⁻¹ * O.f * a * (a⁻¹ * O.f * a) = a⁻¹ * (O.f * O.f) * a := by group
              _ = 1 := by rw [O.f_sq]; group
          rw [this]; exact O.S.one_mem)
  exact hnotcomm

theorem burnsideF4d_mem_commutator_of_oTwoRes {G : Type} [Group G]
    (hO2 : oTwoRes (⊤ : Subgroup G) = ⊤) {x : G} (hx : x * x = 1) : x ∈ commutator G := by
  let T : Subgroup (Abelianization G) :=
    { carrier := {a | ∃ n : ℕ, Odd n ∧ a ^ n = 1}
      one_mem' := ⟨1, odd_one, one_pow 1⟩
      mul_mem' := by
        rintro a b ⟨m, hm, ha⟩ ⟨n, hn, hb⟩
        refine ⟨m * n, hm.mul hn, ?_⟩
        rw [mul_pow, pow_mul a m n, ha, one_pow, mul_comm m n, pow_mul b n m, hb, one_pow, one_mul]
      inv_mem' := by
        rintro a ⟨m, hm, ha⟩
        exact ⟨m, hm, by rw [inv_pow, ha, inv_one]⟩ }
  have hle : oTwoRes (⊤ : Subgroup G) ≤ T.comap (Abelianization.of : G →* Abelianization G) := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro y ⟨-, m, hm, hy⟩
    exact ⟨m, hm, by rw [← map_pow, hy, map_one]⟩
  rw [hO2] at hle
  obtain ⟨n, hn, hxn⟩ := hle (Subgroup.mem_top x)
  have h2 : (Abelianization.of x) ^ 2 = 1 := by rw [pow_two, ← map_mul, hx, map_one]
  have hg : Nat.gcd 2 n = 1 := (Nat.coprime_two_left.mpr hn)
  have h1 : (Abelianization.of x) ^ (Nat.gcd 2 n) = 1 := pow_gcd_eq_one.mpr ⟨h2, hxn⟩
  rw [hg, pow_one] at h1
  rw [← Abelianization.ker_of (G := G), MonoidHom.mem_ker]
  exact h1

end Out

section Y2

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431
  CFSG.Quasithin.H13.F431.L3 CFSG.QuasithinUnique.Borel252 CFSG.QuasithinUnique.Fin257.L3
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour
  CFSG.ASVolI.ChF

theorem burnsideF4d_Y2_pCore_eq {P E : Type} [Group P] [Group E] [Finite P] [Finite E]
    (Φ : P →* E) (hΦ : Function.Injective Φ) [hΦn : Φ.range.Normal]
    {U R₁ R₂ B₀ : Subgroup P} {s₁ s₂ : P} (hD : L3DData U R₁ R₂ B₀ s₁ s₂) {q : ℕ}
    (hO : L3OutHyp Φ U R₁ R₂ q) {N₁ N₂ : Subgroup E}
    (h₁ : N₁ = Subgroup.normalizer ((R₁.map Φ : Subgroup E) : Set E))
    (h₂ : N₂ = Subgroup.normalizer ((R₂.map Φ : Subgroup E) : Set E)) :
    N₁ ⊓ N₂ = Subgroup.normalizer ((U.map Φ : Subgroup E) : Set E) ∧
      pCoreOf 2 (N₁ ⊓ N₂) = U.map Φ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set I : Subgroup E := Φ.range with hI
  set T0 : Subgroup E := U.map Φ with hT0
  set Q₁ : Subgroup E := R₁.map Φ with hQ₁
  set Q₂ : Subgroup E := R₂.map Φ with hQ₂
  set B₀' : Subgroup E := B₀.map Φ with hB₀'
  have hIn : I.Normal := hΦn
  have hSylI : IsSylowTwoOf T0 I := isSylowTwoOf_map_range Φ hΦ hD.borel.sylow
  have hTp : IsPGroup 2 T0 := hSylI.2.1
  have hcenT : CFSG.Quasithin.centerOf T0 = (CFSG.Quasithin.centerOf U).map Φ :=
    centerOf_map_of_injective Φ hΦ U
  have hcardZ : Nat.card (CFSG.Quasithin.centerOf T0) = q := by
    rw [hcenT, Subgroup.card_map_of_injective hΦ]; exact hO.card_Z
  have hUN₁ : U ≤ Subgroup.normalizer (R₁ : Set P) :=
    Subgroup.le_normalizer.trans hD.borel.lt₁.le
  have hUN₂ : U ≤ Subgroup.normalizer (R₂ : Set P) :=
    Subgroup.le_normalizer.trans hD.borel.lt₂.le
  have hTN₁ : T0 ≤ N₁ := by
    rintro _ ⟨u, hu, rfl⟩
    rw [h₁]; exact map_mem_normalizer_map Φ (hUN₁ hu)
  have hTN₂ : T0 ≤ N₂ := by
    rintro _ ⟨u, hu, rfl⟩
    rw [h₂]; exact map_mem_normalizer_map Φ (hUN₂ hu)
  have hTsup : T0 = Q₁ ⊔ Q₂ := by rw [hT0, hQ₁, hQ₂, ← Subgroup.map_sup, hD.borel.sup]
  have hN_eq : N₁ ⊓ N₂ = Subgroup.normalizer (T0 : Set E) := by
    apply le_antisymm
    · intro n hn
      rw [hTsup]
      exact mem_normalizer_sup (h₁ ▸ hn.1) (h₂ ▸ hn.2)
    · intro n hn
      obtain ⟨hn1, hn2⟩ := hO.noswap n hn
      exact ⟨by rw [h₁]; exact hn1, by rw [h₂]; exact hn2⟩
  have hB₀N : B₀' ≤ Subgroup.normalizer (T0 : Set E) := by
    rintro _ ⟨b, hb, rfl⟩
    exact map_mem_normalizer_map Φ (hD.B₀_le hb)
  have hB₀I : B₀' ≤ I := Subgroup.map_le_range Φ B₀
  have hodd₀ : Odd (Nat.card B₀') := by
    rw [hB₀', Subgroup.card_map_of_injective hΦ]; exact hD.B₀_odd
  have hC : ∀ x ∈ T0, (∀ b ∈ B₀', x * b = b * x) → x = 1 := by
    rintro _ ⟨u, hu, rfl⟩ hcomm
    have : u = 1 := hD.centS u hu (fun b hb => hΦ (by
      rw [map_mul, map_mul]; exact hcomm _ (Subgroup.mem_map_of_mem Φ hb)))
    rw [this, map_one]
  have hUp : IsPGroup 2 U := hD.borel.sylow.2.1
  have hcardP : Nat.card (Subgroup.normalizer (U : Set P)) = Nat.card U * Nat.card B₀ :=
    card_eq_mul_of_split Subgroup.le_normalizer hD.B₀_le
      (fun x hx hxB => eq_one_of_pgroup_of_odd hUp hD.B₀_odd hx hxB) hD.mul
  have hcard : Nat.card ↥(Subgroup.normalizer (T0 : Set E) ⊓ I) =
      Nat.card T0 * Nat.card B₀' := by
    rw [hT0, normalizer_map_inf_range Φ hΦ U, Subgroup.card_map_of_injective hΦ, hcardP,
      Subgroup.card_map_of_injective hΦ, hB₀', Subgroup.card_map_of_injective hΦ]
  have hSk : OutSkel I T0 B₀' := ⟨hSylI, hB₀I, hB₀N, hodd₀, hC, hcard⟩
  have hZne : ∃ x ∈ CFSG.Quasithin.centerOf T0, x ≠ 1 := by
    obtain ⟨x, hx, -, -, hx1, -, -⟩ := hD.Z_big
    exact ⟨Φ x, by rw [hcenT]; exact Subgroup.mem_map_of_mem Φ hx,
      fun h => hx1 (hΦ (by rw [h, map_one]))⟩
  have hZtrans : ∀ x ∈ CFSG.Quasithin.centerOf T0, x ≠ 1 → ∀ y ∈ CFSG.Quasithin.centerOf T0,
      y ≠ 1 → ∃ c ∈ B₀', c * x * c⁻¹ = y := by
    intro x hx hx1 y hy hy1
    rw [hcenT] at hx hy
    obtain ⟨x', hx', rfl⟩ := hx
    obtain ⟨y', hy', rfl⟩ := hy
    have hx1' : x' ≠ 1 := fun h => hx1 (by rw [h, map_one])
    have hy1' : y' ≠ 1 := fun h => hy1 (by rw [h, map_one])
    obtain ⟨b, hb, hbxy⟩ := hD.trans x' hx' hx1' y' hy' hy1'
    exact ⟨Φ b, Subgroup.mem_map_of_mem Φ hb, by rw [← map_mul, ← map_inv, ← map_mul, hbxy]⟩
  have hq2 := hO.two_le
  have hout : ∀ b ∈ Subgroup.normalizer (T0 : Set E), (∃ k : ℕ, orderOf b = 2 ^ k) → b ∉ I →
      ¬ ∀ z ∈ CFSG.Quasithin.centerOf T0, b * z = z * b := by
    intro b hb hk hbI hcentr
    have h3 := (hO.bound b hb hk hbI).2.2 (CFSG.Quasithin.centerOf T0) hcenT.le hcentr
    rw [hcardZ] at h3
    nlinarith
  have hpc : pCoreOf 2 (N₁ ⊓ N₂) ≤ T0 := by
    rw [hN_eq]; exact hSk.pCore_le rfl hZtrans hZne hout
  exact ⟨hN_eq, le_antisymm hpc
    (CFSG.QuasithinUnique.le_pCoreOf_of_le_normalizer (le_inf hTN₁ hTN₂) hN_eq.le hTp)⟩

theorem burnsideF4d_Y2_card_U {P H : Type} [Group P] [Finite P] [Group H] (Φ : P →* H)
    {U R₁ R₂ B₀ : Subgroup P} {s₁ s₂ : P} (hD : L3DData U R₁ R₂ B₀ s₁ s₂) {q : ℕ}
    (hO : L3OutHyp Φ U R₁ R₂ q) : Nat.card U = q ^ 3 := by
  have hF := hD.frame
  have hcardQ₂ : Nat.card R₂ = q ^ 2 := by rw [← hF.card_eq]; exact hO.card_R₁
  have hUsup : U = R₁ ⊔ R₂ := hD.borel.sup.symm
  have hUN₁ : U ≤ Subgroup.normalizer (R₁ : Set P) :=
    Subgroup.le_normalizer.trans hD.borel.lt₁.le
  have hQ₂N : R₂ ≤ Subgroup.normalizer (R₁ : Set P) := hF.Q₂_le.trans hUN₁
  have h1 := A4.relIndex_sup_eq_of_le_normalizer' hQ₂N
  rw [sup_comm, ← hUsup] at h1
  have h2 := Subgroup.relIndex_mul_card R₁ R₂
  rw [hF.inter, hO.card_Z, hcardQ₂] at h2
  have hrel : R₁.relIndex U = q := by
    rw [h1]
    have hpos : 0 < q := by have := hO.two_le; omega
    have : R₁.relIndex R₂ * q = q * q := by rw [h2]; ring
    exact Nat.eq_of_mul_eq_mul_right hpos this
  have h := Subgroup.relIndex_mul_card R₁ U
  rw [inf_of_le_left hF.Q₁_le, hrel, hO.card_R₁] at h
  rw [← h]; ring

theorem burnsideF4d_Y2_cards {P E : Type} [Group P] [Finite P] [Group E]
    (Φ : P →* E) (hΦ : Function.Injective Φ)
    {U R₁ R₂ B₀ : Subgroup P} {s₁ s₂ : P} (hD : L3DData U R₁ R₂ B₀ s₁ s₂) {q : ℕ}
    (hO : L3OutHyp Φ U R₁ R₂ q) {N₁ N₂ : Subgroup E}
    (hN : N₁ ⊓ N₂ = Subgroup.normalizer ((U.map Φ : Subgroup E) : Set E))
    (h₁ : N₁ = Subgroup.normalizer ((R₁.map Φ : Subgroup E) : Set E))
    (h₂ : N₂ = Subgroup.normalizer ((R₂.map Φ : Subgroup E) : Set E)) :
    Nat.card ↥(ctr (pCoreOf 2 (Φ.range ⊓ (N₁ ⊓ N₂)))) = q ∧
      Nat.card ↥(pCoreOf 2 (Φ.range ⊓ N₁)) = q ^ 2 ∧
      Nat.card ↥(pCoreOf 2 (Φ.range ⊓ N₂)) = q ^ 2 ∧
      Nat.card ↥(pCoreOf 2 (Φ.range ⊓ (N₁ ⊓ N₂))) = q ^ 3 := by
  have e1 : Φ.range ⊓ (N₁ ⊓ N₂) = (Subgroup.normalizer (U : Set P)).map Φ := by
    rw [hN, inf_comm]; exact normalizer_map_inf_range Φ hΦ U
  have e2 : pCoreOf 2 (Φ.range ⊓ (N₁ ⊓ N₂)) = U.map Φ := by
    rw [e1, CFSG.Quasithin.H13.F431.pCoreOf_map_of_injective Φ hΦ,
      pCoreOf_normalizer_sylow hD.borel.sylow]
  refine ⟨?_, ?_, ?_, ?_⟩
  · show Nat.card ↥(CFSG.Quasithin.centerOf (pCoreOf 2 (Φ.range ⊓ (N₁ ⊓ N₂)))) = q
    rw [e2, centerOf_map_of_injective Φ hΦ, Subgroup.card_map_of_injective hΦ]
    exact hO.card_Z
  · have e3 : Φ.range ⊓ N₁ = (Subgroup.normalizer (R₁ : Set P)).map Φ := by
      rw [h₁, inf_comm]; exact normalizer_map_inf_range Φ hΦ R₁
    rw [e3, CFSG.Quasithin.H13.F431.pCoreOf_map_of_injective Φ hΦ, hD.borel.core₁,
      Subgroup.card_map_of_injective hΦ]
    exact hO.card_R₁
  · have e3 : Φ.range ⊓ N₂ = (Subgroup.normalizer (R₂ : Set P)).map Φ := by
      rw [h₂, inf_comm]; exact normalizer_map_inf_range Φ hΦ R₂
    rw [e3, CFSG.Quasithin.H13.F431.pCoreOf_map_of_injective Φ hΦ, hD.borel.core₂,
      Subgroup.card_map_of_injective hΦ, ← hD.frame.card_eq]
    exact hO.card_R₁
  · rw [e2, Subgroup.card_map_of_injective hΦ]
    exact burnsideF4d_Y2_card_U Φ hD hO

theorem burnsideF4d_Y2_mem_iff_stab {E : Type} [Group E] {Gp : Subgroup E} [Gp.Normal]
    (hinj : Function.Injective (burnsideF4d_rho Gp)) (M : Subgroup E)
    (hM : (burnsideF4d_rho Gp).range ⊓ autStab (M.subgroupOf Gp) = M.map (burnsideF4d_rho Gp))
    (e : E) : e ∈ M ↔ burnsideF4d_rho Gp e ∈ autStab (M.subgroupOf Gp) := by
  constructor
  · intro he
    have : burnsideF4d_rho Gp e ∈ M.map (burnsideF4d_rho Gp) := ⟨e, he, rfl⟩
    rw [← hM] at this
    exact this.2
  · intro he
    have : burnsideF4d_rho Gp e ∈
        (burnsideF4d_rho Gp).range ⊓ autStab (M.subgroupOf Gp) := ⟨⟨e, rfl⟩, he⟩
    rw [hM] at this
    exact (Subgroup.mem_map_iff_mem hinj).mp this

theorem burnsideF4d_Y2_setup {f : ℕ} (hf : 2 ≤ f) {E : Type} [Group E] [Finite E]
    {Gp M₁ M₂ : Subgroup E} (h : HypF_4_4g .L3 2 f Gp M₁ M₂) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2) (Φ : projectiveSL 3 F →* E)
      (R₁ R₂ : Subgroup (projectiveSL 3 F)) (s₁ s₂ : projectiveSL 3 F),
      Nat.card F = 2 ^ f ∧ Function.Injective Φ ∧ Φ.range = Gp ∧
      L3DData (projUnitriangular 3 F) R₁ R₂ (P3.torus3 F) s₁ s₂ ∧
      L3OutHyp Φ (projUnitriangular 3 F) R₁ R₂ (Nat.card F) ∧
      M₁ = Subgroup.normalizer ((R₁.map Φ : Subgroup E) : Set E) ∧
      M₂ = Subgroup.normalizer ((R₂.map Φ : Subgroup E) : Set E) := by
  obtain ⟨TD, hyam⟩ := burnsideF4d_Y1_yam h
  have hmodel := burnsideF4d_Y1_lieModel h
  haveI := h.normal
  have hinj : Function.Injective (burnsideF4d_rho Gp) :=
    burnsideF4d_rho_injective h.centralizer_trivial
  obtain ⟨F, hFf, hFfin, hFchar, E', hFcard, hP⟩ :=
    l3Amalgam_borel hmodel (burnsideF4d_amalgamExt h TD hyam)
  have hq4 : 4 ≤ Nat.card F := by
    rw [hFcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hdata := l3DData_projectiveSL hq4
  obtain ⟨R₁, R₂, s₁, s₂, hdat, hRv, h1, h2⟩ : ∃ (R₁ R₂ : Subgroup (projectiveSL 3 F))
      (s₁ s₂ : projectiveSL 3 F), L3DData (projUnitriangular 3 F) R₁ R₂ (P3.torus3 F) s₁ s₂ ∧
      ((R₁ = V1 ∧ R₂ = V2) ∨ (R₁ = V2 ∧ R₂ = V1)) ∧
      (M₁.subgroupOf Gp).map E'.toMonoidHom = Subgroup.normalizer (R₁ : Set (projectiveSL 3 F)) ∧
      (M₂.subgroupOf Gp).map E'.toMonoidHom =
        Subgroup.normalizer (R₂ : Set (projectiveSL 3 F)) := by
    rcases hP with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨_, _, _, _, hdata, Or.inl ⟨rfl, rfl⟩, h1, h2⟩
    · exact ⟨_, _, _, _, hdata.swap, Or.inr ⟨rfl, rfl⟩, h1, h2⟩
  haveI : Finite (projectiveSL 3 F) := Finite.of_equiv ↥Gp E'.toEquiv
  obtain ⟨Φ, hΦdef⟩ : ∃ Φ : projectiveSL 3 F →* E, ∀ p, Φ p = ((E'.symm p : ↥Gp) : E) :=
    ⟨Gp.subtype.comp E'.symm.toMonoidHom, fun p => rfl⟩
  have hΦinj : Function.Injective Φ := fun a b hab =>
    E'.symm.injective (Subtype.ext ((hΦdef a).symm.trans (hab.trans (hΦdef b))))
  have hΦapp : ∀ d : ↥Gp, Φ (E' d) = (d : E) := fun d => by
    rw [hΦdef, MulEquiv.symm_apply_apply]
  have hrange : Φ.range = Gp := by
    ext x
    constructor
    · rintro ⟨p, rfl⟩
      rw [hΦdef]
      exact (E'.symm p).2
    · intro hx
      exact ⟨E' ⟨x, hx⟩, hΦapp ⟨x, hx⟩⟩
  obtain ⟨ρ, hρcongr, hρinj⟩ : ∃ ρ : E →* MulAut (projectiveSL 3 F),
      (∀ e, ρ e = MulAut.congr E' (burnsideF4d_rho Gp e)) ∧ Function.Injective ρ :=
    ⟨(MulAut.congr E').toMonoidHom.comp (burnsideF4d_rho Gp), fun e => rfl,
      (MulAut.congr E').injective.comp hinj⟩
  have hρapp : ∀ (e : E) (p : projectiveSL 3 F),
      ρ e p = E' (burnsideF4d_rho Gp e (E'.symm p)) := fun e p => by
    rw [hρcongr]; rfl
  have hΦρ : ∀ (e : E) (p : projectiveSL 3 F), Φ (ρ e p) = e * Φ p * e⁻¹ := by
    intro e p
    rw [hρapp, hΦapp, burnsideF4d_rho_apply, hΦdef]
  have hN1 := burnsideF4d_N1_eq h hyam
  have hN2 := burnsideF4d_N2_eq h hyam
  have hiff1 := burnsideF4d_Y2_mem_iff_stab hinj M₁ hN1
  have hiff2 := burnsideF4d_Y2_mem_iff_stab hinj M₂ hN2
  have hsemi1 : ∀ e ∈ M₁, ρ e ∈ semilinearAutGroup 3 F := by
    intro e he
    have hst := autStab_transport E' h1 hdat.borel.core₁ ((hiff1 e).mp he)
    rw [hρcongr]
    rcases hRv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact P3.mem_semilinear_of_map_V1 fun g hg => (hst g).mp hg
    · exact P3.mem_semilinear_of_map_V2 fun g hg => (hst g).mp hg
  have hsemi2 : ∀ e ∈ M₂, ρ e ∈ semilinearAutGroup 3 F := by
    intro e he
    have hst := autStab_transport E' h2 hdat.borel.core₂ ((hiff2 e).mp he)
    rw [hρcongr]
    rcases hRv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact P3.mem_semilinear_of_map_V2 fun g hg => (hst g).mp hg
    · exact P3.mem_semilinear_of_map_V1 fun g hg => (hst g).mp hg
  have hE : ∀ e : E, ρ e ∈ semilinearAutGroup 3 F := by
    have hle : (⊤ : Subgroup E) ≤ (semilinearAutGroup 3 F).comap ρ := by
      rw [← h.gen]
      exact sup_le (fun e he => hsemi1 e he) (fun e he => hsemi2 e he)
    exact fun e => hle (Subgroup.mem_top e)
  have hO := P3.l3OutHyp_of_action hf hFcard ρ hρinj Φ hΦinj hΦρ hE hRv
  have hconj : ∀ (e : E) (X : Subgroup (projectiveSL 3 F)),
      e ∈ Subgroup.normalizer ((X.map Φ : Subgroup E) : Set E) ↔ ∀ p, p ∈ X ↔ ρ e p ∈ X := by
    intro e X
    rw [Subgroup.mem_normalizer_iff]
    constructor
    · intro hh p
      have := hh (Φ p)
      rw [Subgroup.mem_map_iff_mem hΦinj, ← hΦρ, Subgroup.mem_map_iff_mem hΦinj] at this
      exact this
    · intro hh y
      by_cases hy : y ∈ Φ.range
      · obtain ⟨p, rfl⟩ := hy
        rw [Subgroup.mem_map_iff_mem hΦinj, ← hΦρ, Subgroup.mem_map_iff_mem hΦinj]
        exact hh p
      · have h1 : y ∉ X.map Φ := fun hyX => hy (Subgroup.map_le_range Φ X hyX)
        have h2 : e * y * e⁻¹ ∉ X.map Φ := by
          intro hmem
          obtain ⟨q', -, hq'⟩ := hmem
          apply hy
          refine ⟨ρ e⁻¹ q', ?_⟩
          rw [hΦρ, hq']
          group
        exact ⟨fun hh' => absurd hh' h1, fun hh' => absurd hh' h2⟩
  have key : ∀ (M : Subgroup E) (r : Subgroup (projectiveSL 3 F)),
      (∀ e : E, e ∈ M ↔ burnsideF4d_rho Gp e ∈ autStab (M.subgroupOf Gp)) →
      (M.subgroupOf Gp).map E'.toMonoidHom = Subgroup.normalizer (r : Set (projectiveSL 3 F)) →
      pCoreOf 2 (Subgroup.normalizer (r : Set (projectiveSL 3 F))) = r →
      M = Subgroup.normalizer ((r.map Φ : Subgroup E) : Set E) := by
    intro M r hM hP hcore
    set S : Subgroup ↥Gp := r.map E'.symm.toMonoidHom with hS
    have hnS : (Subgroup.normalizer (r : Set (projectiveSL 3 F))).map E'.symm.toMonoidHom =
        Subgroup.normalizer (S : Set ↥Gp) := by
      ext g
      rw [Subgroup.mem_map_equiv, hS, mem_normalizer_map_equiv E'.symm r g]
    have hPS : M.subgroupOf Gp = Subgroup.normalizer (S : Set ↥Gp) := by
      rw [← hnS, ← hP, Subgroup.map_map]
      ext g
      simp
    have hcoreS : pCoreOf 2 (Subgroup.normalizer (S : Set ↥Gp)) = S := by
      rw [← hnS, CFSG.Quasithin.H13.F431.pCoreOf_map_of_injective E'.symm.toMonoidHom
        E'.symm.injective, hcore]
    have hmemS : ∀ x : ↥Gp, x ∈ S ↔ E' x ∈ r := fun x => by
      rw [hS, Subgroup.mem_map_equiv]
      simp
    ext e
    rw [hM e, hPS, mem_autStab_iff_of_normalizer hcoreS, hconj]
    constructor
    · intro H p
      have h3 := H (E'.symm p)
      rw [hmemS, hmemS, MulEquiv.apply_symm_apply, ← hρapp] at h3
      exact h3
    · intro H x
      have h3 := H (E' x)
      rw [hρapp, MulEquiv.symm_apply_apply] at h3
      rw [hmemS, hmemS]
      exact h3
  exact ⟨F, hFf, hFfin, hFchar, Φ, R₁, R₂, s₁, s₂, hFcard, hΦinj, hrange, hdat, hO,
    key M₁ R₁ hiff1 h1 hdat.borel.core₁, key M₂ R₂ hiff2 h2 hdat.borel.core₂⟩

theorem burnsideF4d_Y2_pCore_le {f : ℕ} (hf : 2 ≤ f) {E : Type} [Group E] [Finite E]
    {Gp M₁ M₂ : Subgroup E} (h : CFSG.ASVolI.ChF.HypF_4_4g .L3 2 f Gp M₁ M₂) :
    pCoreOf 2 (M₁ ⊓ M₂) ≤ Gp := by
  obtain ⟨F, hFf, hFfin, hFchar, Φ, R₁, R₂, s₁, s₂, hFcard, hΦ, hrange, hD, hO, h₁, h₂⟩ :=
    burnsideF4d_Y2_setup hf h
  haveI : Finite (projectiveSL 3 F) := Finite.of_injective Φ hΦ
  haveI := h.normal
  haveI : Φ.range.Normal := by rw [hrange]; infer_instance
  rw [(burnsideF4d_Y2_pCore_eq Φ hΦ hD hO h₁ h₂).2, ← hrange]
  exact Subgroup.map_le_range Φ _

theorem burnsideF4d_Y2_card_Z {f : ℕ} (hf : 2 ≤ f) {E : Type} [Group E] [Finite E]
    {Gp M₁ M₂ : Subgroup E} (h : CFSG.ASVolI.ChF.HypF_4_4g .L3 2 f Gp M₁ M₂) :
    Nat.card ↥(CFSG.ASVolI.ChF.ctr (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)))) = 2 ^ f := by
  obtain ⟨F, hFf, hFfin, hFchar, Φ, R₁, R₂, s₁, s₂, hFcard, hΦ, hrange, hD, hO, h₁, h₂⟩ :=
    burnsideF4d_Y2_setup hf h
  haveI : Finite (projectiveSL 3 F) := Finite.of_injective Φ hΦ
  haveI := h.normal
  haveI : Φ.range.Normal := by rw [hrange]; infer_instance
  have hN := (burnsideF4d_Y2_pCore_eq Φ hΦ hD hO h₁ h₂).1
  have := (burnsideF4d_Y2_cards Φ hΦ hD hO hN h₁ h₂).1
  rw [hrange] at this
  exact this.trans hFcard

theorem burnsideF4d_Y2_card_S {f : ℕ} (hf : 2 ≤ f) {E : Type} [Group E] [Finite E]
    {Gp M₁ M₂ : Subgroup E} (h : CFSG.ASVolI.ChF.HypF_4_4g .L3 2 f Gp M₁ M₂) :
    Nat.card ↥(pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) = (2 ^ f) ^ 3 := by
  obtain ⟨F, hFf, hFfin, hFchar, Φ, R₁, R₂, s₁, s₂, hFcard, hΦ, hrange, hD, hO, h₁, h₂⟩ :=
    burnsideF4d_Y2_setup hf h
  haveI : Finite (projectiveSL 3 F) := Finite.of_injective Φ hΦ
  haveI := h.normal
  haveI : Φ.range.Normal := by rw [hrange]; infer_instance
  have hN := (burnsideF4d_Y2_pCore_eq Φ hΦ hD hO h₁ h₂).1
  have := (burnsideF4d_Y2_cards Φ hΦ hD hO hN h₁ h₂).2.2.2
  rw [hrange, hFcard] at this
  exact this

theorem burnsideF4d_Y2_card_Q1 {f : ℕ} (hf : 2 ≤ f) {E : Type} [Group E] [Finite E]
    {Gp M₁ M₂ : Subgroup E} (h : CFSG.ASVolI.ChF.HypF_4_4g .L3 2 f Gp M₁ M₂) :
    Nat.card ↥(pCoreOf 2 (Gp ⊓ M₁)) = (2 ^ f) ^ 2 := by
  obtain ⟨F, hFf, hFfin, hFchar, Φ, R₁, R₂, s₁, s₂, hFcard, hΦ, hrange, hD, hO, h₁, h₂⟩ :=
    burnsideF4d_Y2_setup hf h
  haveI : Finite (projectiveSL 3 F) := Finite.of_injective Φ hΦ
  haveI := h.normal
  haveI : Φ.range.Normal := by rw [hrange]; infer_instance
  have hN := (burnsideF4d_Y2_pCore_eq Φ hΦ hD hO h₁ h₂).1
  have := (burnsideF4d_Y2_cards Φ hΦ hD hO hN h₁ h₂).2.1
  rw [hrange, hFcard] at this
  exact this

theorem burnsideF4d_Y2_card_Q2 {f : ℕ} (hf : 2 ≤ f) {E : Type} [Group E] [Finite E]
    {Gp M₁ M₂ : Subgroup E} (h : CFSG.ASVolI.ChF.HypF_4_4g .L3 2 f Gp M₁ M₂) :
    Nat.card ↥(pCoreOf 2 (Gp ⊓ M₂)) = (2 ^ f) ^ 2 := by
  obtain ⟨F, hFf, hFfin, hFchar, Φ, R₁, R₂, s₁, s₂, hFcard, hΦ, hrange, hD, hO, h₁, h₂⟩ :=
    burnsideF4d_Y2_setup hf h
  haveI : Finite (projectiveSL 3 F) := Finite.of_injective Φ hΦ
  haveI := h.normal
  haveI : Φ.range.Normal := by rw [hrange]; infer_instance
  have hN := (burnsideF4d_Y2_pCore_eq Φ hΦ hD hO h₁ h₂).1
  have := (burnsideF4d_Y2_cards Φ hΦ hD hO hN h₁ h₂).2.2.1
  rw [hrange, hFcard] at this
  exact this

end Y2

section PCore

variable {E : Type} [Group E] [Finite E] {Gp : Subgroup E} [Gp.Normal]

theorem burnsideF4d_pCoreOf_inf_eq (K : Subgroup E) (hle : pCoreOf 2 K ≤ Gp) :
    pCoreOf 2 (Gp ⊓ K) = pCoreOf 2 K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply le_antisymm
  · have hKN : K ≤ Subgroup.normalizer ((Gp ⊓ K : Subgroup E) : Set E) := by
      intro k hk
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · rintro ⟨hx, hxK⟩
        exact ⟨Subgroup.Normal.conj_mem inferInstance x hx k, K.mul_mem (K.mul_mem hk hxK) (K.inv_mem hk)⟩
      · rintro ⟨hx, hxK⟩
        refine ⟨?_, ?_⟩
        · have := Subgroup.Normal.conj_mem (inferInstance : Gp.Normal) _ hx k⁻¹
          simpa [mul_assoc] using this
        · have := K.mul_mem (K.mul_mem (K.inv_mem hk) hxK) hk
          simpa [mul_assoc] using this
    exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      (CFSG.LieType.BorelTits.pCoreOf_le 2 _ |>.trans inf_le_right)
      (hKN.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
  · exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      (le_inf hle (CFSG.LieType.BorelTits.pCoreOf_le 2 K))
      ((inf_le_right).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K)

theorem burnsideF4d_pCoreOf_le_of_odd (hodd : Odd Gp.index) (K : Subgroup E) :
    pCoreOf 2 K ≤ Gp := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro x hx
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K))
    ⟨x, hx⟩
  have hx2 : orderOf x = 2 ^ k := by
    rw [← Subgroup.orderOf_mk x hx]; exact hk
  have h1 : orderOf (QuotientGroup.mk x : E ⧸ Gp) ∣ 2 ^ k :=
    hx2 ▸ orderOf_dvd_of_pow_eq_one (by rw [← QuotientGroup.mk_pow, pow_orderOf_eq_one]; rfl)
  have h2 : orderOf (QuotientGroup.mk x : E ⧸ Gp) ∣ Gp.index := by
    rw [Subgroup.index]
    exact orderOf_dvd_natCard _
  have h3 : Nat.Coprime (2 ^ k) Gp.index := Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hodd)
  have h4 : orderOf (QuotientGroup.mk x : E ⧸ Gp) = 1 :=
    Nat.eq_one_of_dvd_coprimes h3 h1 h2
  exact (QuotientGroup.eq_one_iff x).mp (orderOf_eq_one_iff.mp h4)

end PCore

section Trans

open CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion CFSG.ASVolI.ChF
  CFSG.Quasithin.H13.F431.L3

variable {E : Type} [Group E] {M₁ M₂ : Subgroup E} {Y : Type} [Group Y] {M : Type} [Group M]

theorem burnsideF4d_GiOne_eq (Gp : Subgroup E) (β : Cpl M₁ M₂ Y) (ε : Y →* M) :
    GiOne Gp β ε = subImg (burnsideF4d_bOne β ε) (Gp ⊓ M₁) := by
  unfold GiOne subImg burnsideF4d_bOne
  exact Subgroup.map_map ((Gp ⊓ M₁).subgroupOf M₁) (epsG β ε) (f1 (c := β))

theorem burnsideF4d_GiTwo_eq (Gp : Subgroup E) (β : Cpl M₁ M₂ Y) (ε : Y →* M) :
    GiTwo Gp β ε = subImg (burnsideF4d_bTwo β ε) (Gp ⊓ M₂) := by
  unfold GiTwo subImg burnsideF4d_bTwo
  exact Subgroup.map_map ((Gp ⊓ M₂).subgroupOf M₂) (epsG β ε) (f2 (c := β))

theorem burnsideF4d_MiOne_eq (β : Cpl M₁ M₂ Y) (ε : Y →* M) :
    MiOne β ε = subImg (burnsideF4d_bOne β ε) M₁ := by
  rw [subImg_self]
  unfold MiOne burnsideF4d_bOne
  exact (MonoidHom.range_comp _ _).symm

theorem burnsideF4d_MiTwo_eq (β : Cpl M₁ M₂ Y) (ε : Y →* M) :
    MiTwo β ε = subImg (burnsideF4d_bTwo β ε) M₂ := by
  rw [subImg_self]
  unfold MiTwo burnsideF4d_bTwo
  exact (MonoidHom.range_comp _ _).symm

theorem burnsideF4d_inter_eq (β : Cpl M₁ M₂ Y) (hβ : β.IsFaithful) (ε : Y →* M)
    (hε : Function.Injective (epsG β ε)) :
    MiOne β ε ⊓ MiTwo β ε = subImg (burnsideF4d_bOne β ε) (M₁ ⊓ M₂) := by
  let T := burnsideF4d_amalgIsoM β hβ ε hε
  ext x
  change x ∈ MiOne β ε ⊓ MiTwo β ε ↔ x ∈ subImg T.b₁ (M₁ ⊓ M₂)
  rw [T.mem_H, mem_subImg]
  constructor
  · rintro ⟨g, h1, h2, rfl⟩
    exact ⟨g, h1, ⟨h1, h2⟩, rfl⟩
  · rintro ⟨g, h1, ⟨h1', h2⟩, rfl⟩
    exact ⟨g, h1, h2, rfl⟩

end Trans

section Trans2

open CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion CFSG.ASVolI.ChF
  CFSG.Quasithin.H13.F431.L3

variable {E : Type} [Group E] {M₁ M₂ : Subgroup E} {Y : Type} [Group Y] {M : Type} [Group M]

theorem burnsideF4d_map_inclusion_subgroupOf (Y' : Subgroup E) (hY : Y' ≤ M₁ ⊓ M₂) :
    (Y'.subgroupOf (M₁ ⊓ M₂)).map (RankTwoAmalgam.ofSubgroups M₁ M₂).α1 = Y'.subgroupOf M₁ := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    let x' : ↥M₁ := x
    exact ⟨⟨(x' : E), ⟨x'.2, (hY hx).2⟩⟩, hx, rfl⟩

theorem burnsideF4d_SinM_eq (Gp : Subgroup E) (β : Cpl M₁ M₂ Y) (ε : Y →* M) :
    SinM Gp β ε = subImg (burnsideF4d_bOne β ε) (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) := by
  have hY : pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ≤ M₁ ⊓ M₂ :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans inf_le_right
  unfold SinM Sp subImg burnsideF4d_bOne
  rw [burnsideF4d_map_inclusion_subgroupOf _ hY]
  exact Subgroup.map_map ((pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))).subgroupOf M₁) (epsG β ε) (f1 (c := β))

theorem burnsideF4d_SinM_eq_pCore [Finite E] (Gp : Subgroup E) [Gp.Normal] (β : Cpl M₁ M₂ Y)
    (hβ : β.IsFaithful) (ε : Y →* M) (hε : Function.Injective (epsG β ε))
    (hle : pCoreOf 2 (M₁ ⊓ M₂) ≤ Gp) :
    SinM Gp β ε = pCoreOf 2 (MiOne β ε ⊓ MiTwo β ε) := by
  rw [burnsideF4d_SinM_eq, burnsideF4d_inter_eq β hβ ε hε,
    burnsideF4d_pCoreOf_inf_eq (Gp := Gp) (M₁ ⊓ M₂) hle]
  exact (subImg_pCoreOf (burnsideF4d_amalgIsoM β hβ ε hε).inj₁ (inf_le_left : M₁ ⊓ M₂ ≤ M₁)).symm

end Trans2

section OddL3

open CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion CFSG.ASVolI.ChF
  CFSG.Quasithin.H13.F431.L3

theorem burnsideF4d_L3_odd {f : ℕ} (hf : 2 ≤ f) {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    {Y : Type} [Group Y] {β : Cpl M₁ M₂ Y} {M : Type} [Group M] {ε : Y →* M} {z : M}
    (hyp : HypF_4_31 .L3 f Gp M₁ M₂ β ε z) : Odd Gp.index := by
  by_contra hnodd
  haveI := hyp.amalgam.finite
  haveI := hyp.finite_M
  have hyp4 := hyp.amalgam.toHypF_4_4g
  haveI := hyp4.normal
  obtain ⟨TD, hyam⟩ := burnsideF4d_Y1_yam hyp4
  have hmodel := burnsideF4d_Y1_lieModel hyp4
  have hinj : Function.Injective (burnsideF4d_rho Gp) :=
    burnsideF4d_rho_injective hyp4.centralizer_trivial
  let X := burnsideF4d_lieExtE hyp4 hyam
  have hK : Nat.card ↥X.K = Nat.card E := by
    have : X.K = (burnsideF4d_rho Gp).range := burnsideF4d_K_eq hyp4 hyam
    rw [this, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
  have hnodd' : ¬ Odd (Nat.card ↥X.K / Nat.card ↥Gp) := by
    rw [hK]
    have := Subgroup.card_mul_index Gp
    have hpos : 0 < Nat.card ↥Gp := Nat.card_pos
    rw [show Nat.card E / Nat.card ↥Gp = Gp.index by
      rw [← this, Nat.mul_div_cancel_left _ hpos]]
    exact hnodd
  obtain ⟨O⟩ := f431L3OutLie f hf ↥Gp hmodel X.toLieAmalgamExt hnodd'
  obtain ⟨O1⟩ := O.nonempty_transport X.amalgIso
  obtain ⟨Og⟩ := O1.nonempty_transport (burnsideF4d_amalgIsoM β hyp.faithful ε hyp.inj)
  have hle : pCoreOf 2 (M₁ ⊓ M₂) ≤ Gp := burnsideF4d_Y2_pCore_le hf hyp4
  have hS : SinM Gp β ε = pCoreOf 2 (MiOne β ε ⊓ MiTwo β ε) :=
    burnsideF4d_SinM_eq_pCore Gp β hyp.faithful ε hyp.inj hle
  have hz : z ∈ centerOf Og.S := by
    have h1 := hyp.z_mem.2 rfl
    rw [Og.S_eq, ← hS]
    exact h1
  have hz1 : z ≠ 1 := hyp.z_inv.1
  have hnc := burnsideF4d_Out_not_mem_commutator Og hz hz1 hyp.hb
  have hO2 : oTwoRes (⊤ : Subgroup M) = ⊤ :=
    hyp.he.resolve_right (by rintro ⟨h1, -⟩; omega)
  exact hnc (burnsideF4d_mem_commutator_of_oTwoRes hO2 Og.f_sq)

end OddL3

section OPP

open CFSG.ASVolI.ChF

variable {E : Type} [Group E]

theorem burnsideF4d_oPPrime_map {A B : Type} [Group A] [Group B] (φ : A →* B)
    (hφ : Function.Injective φ) (p : ℕ) (X : Subgroup A) :
    oPPrime p (X.map φ) = (oPPrime p X).map φ := by
  unfold oPPrime
  rw [MonoidHom.map_closure]
  congr 1
  ext y
  constructor
  · rintro ⟨hy, k, hk⟩
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    exact ⟨x, ⟨hx, k, by rw [← hk, orderOf_injective φ hφ x]⟩, rfl⟩
  · rintro ⟨x, ⟨hx, k, hk⟩, rfl⟩
    exact ⟨Subgroup.mem_map_of_mem φ hx, k, by rw [orderOf_injective φ hφ x, hk]⟩

theorem burnsideF4d_subImg_oPPrime {Mb G : Type} [Group Mb] [Group G] {N : Subgroup Mb}
    (b : ↥N →* G) (hb : Function.Injective b) {X : Subgroup Mb} (hX : X ≤ N) (p : ℕ) :
    oPPrime p (subImg b X) = subImg b (oPPrime p X) := by
  unfold subImg
  rw [burnsideF4d_oPPrime_map b hb]
  congr 1
  have h1 : oPPrime p X = (oPPrime p (X.subgroupOf N)).map N.subtype := by
    rw [← burnsideF4d_oPPrime_map N.subtype N.subtype_injective,
      Subgroup.map_subgroupOf_eq_of_le hX]
  rw [h1, CFSG.Quasithin.H13.F431.L3.subgroupOf_map_subtype_self]

theorem burnsideF4d_le_normalizer_oPPrime (H : Subgroup E) :
    H ≤ Subgroup.normalizer (oPPrime 2 H : Set E) := by
  have key : ∀ g ∈ H, ∀ x ∈ oPPrime 2 H, g * x * g⁻¹ ∈ oPPrime 2 H := by
    intro g hg x hx
    unfold oPPrime at hx ⊢
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨hyH, k, hk⟩ := hy
      refine Subgroup.subset_closure ⟨H.mul_mem (H.mul_mem hg hyH) (H.inv_mem hg), k, ?_⟩
      rw [← hk]
      exact (MulEquiv.orderOf_eq (MulAut.conj g) y)
    | one => simpa using Subgroup.one_mem _
    | mul a b _ _ ha hb =>
      have : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
      rw [this]; exact Subgroup.mul_mem _ ha hb
    | inv a _ ha =>
      have : g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by group
      rw [this]; exact Subgroup.inv_mem _ ha
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact key g hg x
  · intro hx
    have := key g⁻¹ (H.inv_mem hg) _ hx
    simpa [mul_assoc] using this

theorem burnsideF4d_oPPrime_le (H : Subgroup E) : oPPrime 2 H ≤ H :=
  (Subgroup.closure_le H).mpr fun _ hx => hx.1

variable [Finite E]

theorem burnsideF4d_pCoreOf_oPPrime (H : Subgroup E) :
    pCoreOf 2 (oPPrime 2 H) = pCoreOf 2 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply le_antisymm
  · exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans (burnsideF4d_oPPrime_le H))
      ((burnsideF4d_le_normalizer_oPPrime H).trans
        (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
  · have hle : pCoreOf 2 H ≤ oPPrime 2 H := by
      intro y hy
      obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H) ⟨y, hy⟩
      exact Subgroup.subset_closure ⟨CFSG.LieType.BorelTits.pCoreOf_le 2 H hy, k, by
        rw [← Subgroup.orderOf_mk y hy]; exact hk⟩
    exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hle
      ((burnsideF4d_oPPrime_le H).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H)

end OPP

section DatumFacts

open CFSG.Quasithin.H13.F431.L3

variable {G : Type} [Group G] [Finite G] {M₁ M₂ : Subgroup G}

theorem burnsideF4d_exists_Q₁_not_Z (D : L3Datum M₁ M₂) : ∃ x ∈ D.Q₁, x ∉ D.Z := by
  by_contra h
  push Not at h
  have hle : D.Q₁ ≤ D.Q₂ := fun x hx => by
    have hxZ := h x hx
    have : x ∈ D.Q₁ ⊓ D.Q₂ := by rw [D.frame.inter]; exact hxZ
    exact this.2
  exact D.frame.Q_ne (Subgroup.eq_of_le_of_card_ge hle (le_of_eq D.frame.card_eq.symm))

theorem burnsideF4d_exists_Q₂_not_Z (D : L3Datum M₁ M₂) : ∃ x ∈ D.Q₂, x ∉ D.Z := by
  by_contra h
  push Not at h
  have hle : D.Q₂ ≤ D.Q₁ := fun x hx => by
    have hxZ := h x hx
    have : x ∈ D.Q₁ ⊓ D.Q₂ := by rw [D.frame.inter]; exact hxZ
    exact this.1
  exact D.frame.Q_ne (Subgroup.eq_of_le_of_card_ge hle (le_of_eq D.frame.card_eq)).symm

theorem burnsideF4d_Q₁_eq (D : L3Datum M₁ M₂) : D.Q₁ = pCoreOf 2 M₁ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply le_antisymm
  · refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (D.frame.Q₁_le.trans D.S_le_M₁) ?_
      (D.S_pgroup.to_le D.frame.Q₁_le)
    intro m hm
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact fun hx => D.Q₁_norm m hm x hx
    · intro hx
      have := D.Q₁_norm m⁻¹ (M₁.inv_mem hm) _ hx
      simpa [mul_assoc] using this
  · intro r hr
    have hSyl : IsSylowTwoOf D.S M₁ := ⟨D.S_le_M₁, D.S_pgroup, D.S_index⟩
    have hrS : r ∈ D.S := F7.isSylowTwoOf_pCoreOf_le hSyl hr
    obtain ⟨x₀, hx₀Q, hx₀Z⟩ := burnsideF4d_exists_Q₁_not_Z D
    have hx₀1 : x₀ ≠ 1 := fun h => hx₀Z (h ▸ D.Z.one_mem)
    obtain ⟨m, hm, hmz⟩ := D.cov₁ x₀ hx₀Q hx₀1
    have hrm : m * r * m⁻¹ ∈ pCoreOf 2 M₁ :=
      (Subgroup.mem_normalizer_iff.mp (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M₁ hm) r).mp hr
    have hrmS : m * r * m⁻¹ ∈ D.S := F7.isSylowTwoOf_pCoreOf_le hSyl hrm
    have h' : (m * r * m⁻¹) * (m * x₀ * m⁻¹) = (m * x₀ * m⁻¹) * (m * r * m⁻¹) :=
      (D.mem_Z.mp hmz).2 _ hrmS
    have hcomm : r * x₀ = x₀ * r := by
      calc r * x₀ = m⁻¹ * ((m * r * m⁻¹) * (m * x₀ * m⁻¹)) * m := by group
        _ = m⁻¹ * ((m * x₀ * m⁻¹) * (m * r * m⁻¹)) * m := by rw [h']
        _ = x₀ * r := by group
    exact D.frame.cent₁ x₀ hx₀Q hx₀Z r hrS hcomm

theorem burnsideF4d_Q₂_eq (D : L3Datum M₁ M₂) (hSyl : IsSylowTwoOf D.S M₂) :
    D.Q₂ = pCoreOf 2 M₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply le_antisymm
  · refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (D.frame.Q₂_le.trans D.S_le_M₂) ?_
      (D.S_pgroup.to_le D.frame.Q₂_le)
    intro m hm
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact fun hx => D.Q₂_norm m hm x hx
    · intro hx
      have := D.Q₂_norm m⁻¹ (M₂.inv_mem hm) _ hx
      simpa [mul_assoc] using this
  · intro r hr
    have hrS : r ∈ D.S := F7.isSylowTwoOf_pCoreOf_le hSyl hr
    obtain ⟨x₀, hx₀Q, hx₀Z⟩ := burnsideF4d_exists_Q₂_not_Z D
    have hx₀1 : x₀ ≠ 1 := fun h => hx₀Z (h ▸ D.Z.one_mem)
    obtain ⟨m, hm, hmz⟩ := D.cov₂ x₀ hx₀Q hx₀1
    have hrm : m * r * m⁻¹ ∈ pCoreOf 2 M₂ :=
      (Subgroup.mem_normalizer_iff.mp (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M₂ hm) r).mp hr
    have hrmS : m * r * m⁻¹ ∈ D.S := F7.isSylowTwoOf_pCoreOf_le hSyl hrm
    have h' : (m * r * m⁻¹) * (m * x₀ * m⁻¹) = (m * x₀ * m⁻¹) * (m * r * m⁻¹) :=
      (D.mem_Z.mp hmz).2 _ hrmS
    have hcomm : r * x₀ = x₀ * r := by
      calc r * x₀ = m⁻¹ * ((m * r * m⁻¹) * (m * x₀ * m⁻¹)) * m := by group
        _ = m⁻¹ * ((m * x₀ * m⁻¹) * (m * r * m⁻¹)) * m := by rw [h']
        _ = x₀ * r := by group
    exact D.frame.cent₂ x₀ hx₀Q hx₀Z r hrS hcomm

theorem burnsideF4d_sylow_eq_S (D : L3Datum M₁ M₂) {T : Subgroup G}
    (hT : IsSylowTwoOf T (M₁ ⊓ M₂)) : T = D.S := by
  apply le_antisymm
  · intro t ht
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hT.2.1 ⟨t, ht⟩
    have hk' : orderOf t = 2 ^ k := by rw [← Subgroup.orderOf_mk t ht]; exact hk
    have h1 : t ^ (2 ^ k) = 1 := by
      rw [← hk']; exact pow_orderOf_eq_one t
    exact D.two_elt_mem_S (hT.1 ht) h1
  · rw [D.S_eq]
    exact F7.isSylowTwoOf_pCoreOf_le hT

end DatumFacts

section Setup

open CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion CFSG.ASVolI.ChF
  CFSG.Quasithin.H13.F431.L3

variable {E : Type} [Group E] [Finite E] {Gp M₁ M₂ : Subgroup E} [Gp.Normal]
  {Y : Type} [Group Y] {M : Type} [Group M]

theorem burnsideF4d_Qhat_one (hodd : Odd Gp.index) (β : Cpl M₁ M₂ Y) (hβ : β.IsFaithful)
    (ε : Y →* M) (hε : Function.Injective (epsG β ε)) :
    pCoreOf 2 (oPPrime 2 (GiOne Gp β ε)) = pCoreOf 2 (MiOne β ε) := by
  have hb : Function.Injective (burnsideF4d_bOne β ε) := hε.comp (f1_injective β hβ)
  have hle : pCoreOf 2 M₁ ≤ Gp := burnsideF4d_pCoreOf_le_of_odd hodd M₁
  have hE : pCoreOf 2 (oPPrime 2 (Gp ⊓ M₁)) = pCoreOf 2 M₁ := by
    rw [burnsideF4d_pCoreOf_oPPrime, burnsideF4d_pCoreOf_inf_eq M₁ hle]
  rw [burnsideF4d_GiOne_eq, burnsideF4d_MiOne_eq,
    burnsideF4d_subImg_oPPrime _ hb (inf_le_right : Gp ⊓ M₁ ≤ M₁),
    subImg_pCoreOf hb ((burnsideF4d_oPPrime_le _).trans inf_le_right),
    subImg_pCoreOf hb (le_refl M₁), hE]

theorem burnsideF4d_Qhat_two (hodd : Odd Gp.index) (β : Cpl M₁ M₂ Y) (hβ : β.IsFaithful)
    (ε : Y →* M) (hε : Function.Injective (epsG β ε)) :
    pCoreOf 2 (oPPrime 2 (GiTwo Gp β ε)) = pCoreOf 2 (MiTwo β ε) := by
  have hb : Function.Injective (burnsideF4d_bTwo β ε) := hε.comp (f2_injective β hβ)
  have hle : pCoreOf 2 M₂ ≤ Gp := burnsideF4d_pCoreOf_le_of_odd hodd M₂
  have hE : pCoreOf 2 (oPPrime 2 (Gp ⊓ M₂)) = pCoreOf 2 M₂ := by
    rw [burnsideF4d_pCoreOf_oPPrime, burnsideF4d_pCoreOf_inf_eq M₂ hle]
  rw [burnsideF4d_GiTwo_eq, burnsideF4d_MiTwo_eq,
    burnsideF4d_subImg_oPPrime _ hb (inf_le_right : Gp ⊓ M₂ ≤ M₂),
    subImg_pCoreOf hb ((burnsideF4d_oPPrime_le _).trans inf_le_right),
    subImg_pCoreOf hb (le_refl M₂), hE]

end Setup

section Setup2

open CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion CFSG.ASVolI.ChF
  CFSG.Quasithin.H13.F431.L3

theorem burnsideF4d_L3_setup {f : ℕ} (hf : 2 ≤ f) {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    {Y : Type} [Group Y] {β : Cpl M₁ M₂ Y} {M : Type} [Group M] {ε : Y →* M} {z : M}
    (hyp : HypF_4_31 .L3 f Gp M₁ M₂ β ε z) :
    ∃ D : L3Datum (MiOne β ε) (MiTwo β ε), D.Good ∧ z ∈ D.Z ∧ D.S = SinM Gp β ε ∧
      D.Q₁ = pCoreOf 2 (oPPrime 2 (GiOne Gp β ε)) ∧
      D.Q₂ = pCoreOf 2 (oPPrime 2 (GiTwo Gp β ε)) := by
  haveI := hyp.amalgam.finite
  haveI := hyp.finite_M
  haveI := hyp.amalgam.toHypF_4_4g.normal
  have hodd : Odd Gp.index := burnsideF4d_L3_odd hf hyp
  obtain ⟨D⟩ := burnsideF4d_L3_datumM hf hyp hodd
  have hS : SinM Gp β ε = pCoreOf 2 (MiOne β ε ⊓ MiTwo β ε) :=
    burnsideF4d_SinM_eq_pCore Gp β hyp.faithful ε hyp.inj
      (burnsideF4d_pCoreOf_le_of_odd hodd _)
  have hDS : D.S = SinM Gp β ε := by rw [D.S_eq, hS]
  have hz : z ∈ D.Z := by
    have h1 := hyp.z_mem.2 rfl
    show z ∈ centerOf D.S
    rw [hDS]
    exact h1
  have hz1 : z ≠ 1 := hyp.z_inv.1
  have hG : D.Good := L3Datum.Good.of_hyp hz hz1 hyp.hb
  refine ⟨D, hG, hz, hDS, ?_, ?_⟩
  · rw [burnsideF4d_Qhat_one hodd β hyp.faithful ε hyp.inj, burnsideF4d_Q₁_eq D]
  · rw [burnsideF4d_Qhat_two hodd β hyp.faithful ε hyp.inj,
      burnsideF4d_Q₂_eq D (F7.isSylowTwoOf_mono_right hG.sylow_top D.S_le_M₂ le_top)]

end Setup2

section Cards

open CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion CFSG.ASVolI.ChF
  CFSG.Quasithin.H13.F431.L3

theorem burnsideF4d_L3_cards {f : ℕ} (hf : 2 ≤ f) {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    {Y : Type} [Group Y] {β : Cpl M₁ M₂ Y} {M : Type} [Group M] {ε : Y →* M} {z : M}
    (hyp : HypF_4_31 .L3 f Gp M₁ M₂ β ε z) (D : L3Datum (MiOne β ε) (MiTwo β ε))
    (hDS : D.S = SinM Gp β ε) (hQ₁ : D.Q₁ = pCoreOf 2 (oPPrime 2 (GiOne Gp β ε)))
    (hQ₂ : D.Q₂ = pCoreOf 2 (oPPrime 2 (GiTwo Gp β ε))) :
    Nat.card D.S = (2 ^ f) ^ 3 ∧ Nat.card D.Z = 2 ^ f ∧ Nat.card D.Q₁ = (2 ^ f) ^ 2 ∧
      Nat.card D.Q₂ = (2 ^ f) ^ 2 := by
  haveI := hyp.amalgam.finite
  haveI := hyp.finite_M
  haveI := hyp.amalgam.toHypF_4_4g.normal
  have hyp4 := hyp.amalgam.toHypF_4_4g
  have hodd : Odd Gp.index := burnsideF4d_L3_odd hf hyp
  have hb1 : Function.Injective (burnsideF4d_bOne β ε) := hyp.inj.comp (f1_injective β hyp.faithful)
  have hb2 : Function.Injective (burnsideF4d_bTwo β ε) := hyp.inj.comp (f2_injective β hyp.faithful)
  have hY1 : pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ≤ M₁ :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans (inf_le_right.trans inf_le_left)
  have hSd : D.S = subImg (burnsideF4d_bOne β ε) (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) := by
    rw [hDS, burnsideF4d_SinM_eq]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hSd, card_subImg _ hb1 hY1]
    exact burnsideF4d_Y2_card_S hf hyp4
  · show Nat.card (centerOf D.S) = _
    rw [hSd, subImg_centerOf hb1 hY1, card_subImg _ hb1
      (show centerOf (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) ≤ M₁ from inf_le_left.trans hY1)]
    exact burnsideF4d_Y2_card_Z hf hyp4
  · rw [hQ₁, burnsideF4d_Qhat_one hodd β hyp.faithful ε hyp.inj, burnsideF4d_MiOne_eq,
      subImg_pCoreOf hb1 (le_refl M₁), card_subImg _ hb1 (CFSG.LieType.BorelTits.pCoreOf_le 2 _),
      ← burnsideF4d_pCoreOf_inf_eq M₁ (burnsideF4d_pCoreOf_le_of_odd hodd M₁)]
    exact burnsideF4d_Y2_card_Q1 hf hyp4
  · rw [hQ₂, burnsideF4d_Qhat_two hodd β hyp.faithful ε hyp.inj, burnsideF4d_MiTwo_eq,
      subImg_pCoreOf hb2 (le_refl M₂), card_subImg _ hb2 (CFSG.LieType.BorelTits.pCoreOf_le 2 _),
      ← burnsideF4d_pCoreOf_inf_eq M₂ (burnsideF4d_pCoreOf_le_of_odd hodd M₂)]
    exact burnsideF4d_Y2_card_Q2 hf hyp4

end Cards

section TwoLeF

open CFSG.ASVolI.ChF

theorem burnsideF4d_L3_two_le_f {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    {Y : Type} [Group Y] {β : Cpl M₁ M₂ Y} {M : Type} [Group M] {ε : Y →* M} {z : M}
    (hyp : HypF_4_31 .L3 f Gp M₁ M₂ β ε z) : 2 ≤ f := by
  have h1 : 1 ≤ f := by
    have := hyp.amalgam.model
    exact this.2.1
  have h2 : f ≠ 1 := fun h => hyp.not_L32 ⟨rfl, h⟩
  omega

end TwoLeF

section TwoElt

variable {E : Type} [Group E] [Finite E] {Gp : Subgroup E} [Gp.Normal]

theorem burnsideF4d_two_elt_mem (hodd : Odd Gp.index) {x : E} {k : ℕ} (hx : x ^ (2 ^ k) = 1) :
    x ∈ Gp := by
  have h1 : orderOf (QuotientGroup.mk x : E ⧸ Gp) ∣ 2 ^ k :=
    orderOf_dvd_of_pow_eq_one (by rw [← QuotientGroup.mk_pow, hx]; rfl)
  have h2 : orderOf (QuotientGroup.mk x : E ⧸ Gp) ∣ Gp.index := by
    rw [Subgroup.index]
    exact orderOf_dvd_natCard _
  have h3 : Nat.Coprime (2 ^ k) Gp.index := Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hodd)
  have h4 : orderOf (QuotientGroup.mk x : E ⧸ Gp) = 1 := Nat.eq_one_of_dvd_coprimes h3 h1 h2
  exact (QuotientGroup.eq_one_iff x).mp (orderOf_eq_one_iff.mp h4)

end TwoElt

end F4dBaseRest

section F4dPartZ1

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431
  CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion CFSG.ASVolI.ChF
  CFSG.Quasithin.H13.F431.L3

section Z1Basic

variable {G : Type} [Group G]

theorem burnsideF4d_Z1_centralizer_conj (a x : G) :
    Subgroup.centralizer ({a * x * a⁻¹} : Set G) =
      conjSub a (Subgroup.centralizer ({x} : Set G)) := by
  ext y
  rw [Subgroup.mem_centralizer_singleton_iff, mem_conjSub,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    calc a⁻¹ * y * a * x = a⁻¹ * (y * (a * x * a⁻¹)) * a := by group
      _ = a⁻¹ * ((a * x * a⁻¹) * y) * a := by rw [h]
      _ = x * (a⁻¹ * y * a) := by group
  · intro h
    calc y * (a * x * a⁻¹) = a * ((a⁻¹ * y * a) * x) * a⁻¹ := by group
      _ = a * (x * (a⁻¹ * y * a)) * a⁻¹ := by rw [h]
      _ = a * x * a⁻¹ * y := by group

theorem burnsideF4d_Z1_orderOf_of_mem {P : Subgroup G} (hP : IsPGroup 2 P) {x : G} (hx : x ∈ P) :
    ∃ k : ℕ, orderOf x = 2 ^ k := by
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hP) ⟨x, hx⟩
  exact ⟨k, by rw [← Subgroup.orderOf_mk x hx]; exact hk⟩

theorem burnsideF4d_Z1_le_oPPrime {P K : Subgroup G} (hP : IsPGroup 2 P) (hPK : P ≤ K) :
    P ≤ oPPrime 2 K := by
  intro x hx
  obtain ⟨k, hk⟩ := burnsideF4d_Z1_orderOf_of_mem hP hx
  exact Subgroup.subset_closure ⟨hPK hx, k, hk⟩

theorem burnsideF4d_Z1_normalizer_oPPrime {K : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (K : Set G)) :
    g ∈ Subgroup.normalizer (oPPrime 2 K : Set G) := by
  apply mem_normalizer_of_conjSub_eq
  have h1 : conjSub g (oPPrime 2 K) = oPPrime 2 (conjSub g K) :=
    (burnsideF4d_oPPrime_map (MulAut.conj g).toMonoidHom (MulAut.conj g).injective 2 K).symm
  rw [h1, conjSub_eq_of_mem_normalizer hg]

theorem burnsideF4d_Z1_mem_normalizer_inf (Gp : Subgroup G) [Gp.Normal] {N : Subgroup G} {n : G}
    (hn : n ∈ N) : n ∈ Subgroup.normalizer ((Gp ⊓ N : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  simp only [Subgroup.mem_inf]
  constructor
  · rintro ⟨hy, hyN⟩
    exact ⟨Subgroup.Normal.conj_mem inferInstance y hy n,
      N.mul_mem (N.mul_mem hn hyN) (N.inv_mem hn)⟩
  · rintro ⟨hy, hyN⟩
    refine ⟨?_, ?_⟩
    · have := Subgroup.Normal.conj_mem (inferInstance : Gp.Normal) _ hy n⁻¹
      simpa [mul_assoc] using this
    · have := N.mul_mem (N.mul_mem (N.inv_mem hn) hyN) hn
      simpa [mul_assoc] using this

end Z1Basic

section Z1Datum

variable {G : Type} [Group G] [Finite G] {M₁ M₂ : Subgroup G} {D : L3Datum M₁ M₂}

theorem burnsideF4d_Z1_cent_pCore (hG : D.Good) {x : G} (hx : x ∈ D.Z) (hx1 : x ≠ 1) :
    pCoreOf 2 (Subgroup.centralizer ({x} : Set G)) = D.S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hCle : Subgroup.centralizer ({x} : Set G) ≤ M₁ ⊓ M₂ := fun y hy =>
    hG.cent x hx hx1 y (Subgroup.mem_centralizer_singleton_iff.mp hy)
  have hSC : D.S ≤ Subgroup.centralizer ({x} : Set G) := fun s hs => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (D.mem_Z.mp hx).2 s hs
  apply le_antisymm
  · intro y hy
    obtain ⟨k, hk⟩ := exists_pow_two_eq_one (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _) hy
    exact L3Datum.two_elt_mem_S (D := D) (hCle (CFSG.LieType.BorelTits.pCoreOf_le 2 _ hy)) hk
  · refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hSC ?_ D.S_pgroup
    intro y hy
    rw [L3Datum.normalizer_S_eq hG]
    exact hCle hy

theorem burnsideF4d_Z1_cent_oPPrime (hG : D.Good) {x : G} (hx : x ∈ D.Z) (hx1 : x ≠ 1) :
    oPPrime 2 (Subgroup.centralizer ({x} : Set G)) = D.S := by
  have hCle : Subgroup.centralizer ({x} : Set G) ≤ M₁ ⊓ M₂ := fun y hy =>
    hG.cent x hx hx1 y (Subgroup.mem_centralizer_singleton_iff.mp hy)
  have hSC : D.S ≤ Subgroup.centralizer ({x} : Set G) := fun s hs => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (D.mem_Z.mp hx).2 s hs
  apply le_antisymm
  · refine (Subgroup.closure_le D.S).mpr ?_
    rintro y ⟨hyC, k, hk⟩
    refine L3Datum.two_elt_mem_S (D := D) (hCle hyC) (k := k) ?_
    rw [← hk]
    exact pow_orderOf_eq_one y
  · intro y hy
    obtain ⟨k, hk⟩ := burnsideF4d_Z1_orderOf_of_mem D.S_pgroup hy
    exact Subgroup.subset_closure ⟨hSC hy, k, hk⟩

theorem burnsideF4d_Z1_involution_centralizer (hG : D.Good) {j : G} (hj1 : j ≠ 1)
    (hj2 : j * j = 1) :
    oPPrime 2 (Subgroup.centralizer ({j} : Set G)) =
        pCoreOf 2 (Subgroup.centralizer ({j} : Set G)) ∧
      IsSylowOf 2 (pCoreOf 2 (Subgroup.centralizer ({j} : Set G))) ⊤ := by
  obtain ⟨a, ha⟩ := hG.inv_conj_Z (by rw [pow_two]; exact hj2) hj1
  have hx1 : a⁻¹ * j * a ≠ 1 := conj_ne_one' hj1
  have hC : Subgroup.centralizer ({j} : Set G) =
      conjSub a (Subgroup.centralizer ({a⁻¹ * j * a} : Set G)) := by
    have := burnsideF4d_Z1_centralizer_conj a (a⁻¹ * j * a)
    rwa [show a * (a⁻¹ * j * a) * a⁻¹ = j by group] at this
  have h1 := burnsideF4d_Z1_cent_pCore hG ha hx1
  have h2 := burnsideF4d_Z1_cent_oPPrime hG ha hx1
  have e1 : pCoreOf 2 (conjSub a (Subgroup.centralizer ({a⁻¹ * j * a} : Set G))) =
      conjSub a D.S := by
    rw [pCoreOf_conjSub, h1]
  have e2 : oPPrime 2 (conjSub a (Subgroup.centralizer ({a⁻¹ * j * a} : Set G))) =
      conjSub a D.S := by
    rw [← h2]
    exact burnsideF4d_oPPrime_map (MulAut.conj a).toMonoidHom (MulAut.conj a).injective 2 _
  rw [hC]
  refine ⟨e2.trans e1.symm, ?_⟩
  rw [e1]
  have := F7.isSylowTwoOf_conj hG.sylow_top a
  rw [conjSub_top] at this
  exact ⟨this.1, this.2.1, this.2.2⟩

theorem burnsideF4d_Z1_weak (hG : D.Good) {Q Q' Mi : Subgroup G}
    (hF : Frame D.S Q Q') (hnc : ∀ x : G, conjSub x Q ≠ Q') (hSyl : IsSylowTwoOf D.S Mi)
    (hnorm : ∀ n : G, (∀ x ∈ Q, n * x * n⁻¹ ∈ Q) → n ∈ Mi)
    (hMi : ∀ m ∈ Mi, conjSub m Q = Q) {g : G} (hg : conjSub g Q ≤ Mi) :
    conjSub g Q = Q := by
  have hpg : IsPGroup 2 (conjSub g Q) := F7.isPGroup_conjSub (D.S_pgroup.to_le hF.Q₁_le)
  obtain ⟨x, hxMi, hx⟩ := F7.isSylowTwoOf_exists_conj_le hSyl hg hpg
  have hB : conjSub (x⁻¹ * g) Q ≤ D.S := by
    rw [conjSub_mul]
    have := conjSub_mono x⁻¹ hx
    rwa [conjSub_conjSub_inv] at this
  have hBea : IsElemAbelian 2 (conjSub (x⁻¹ * g) Q) := F7.isElemAbelian_conjSub hF.Q₁_ea
  have hcard : Nat.card Q ≤ Nat.card (conjSub (x⁻¹ * g) Q) := by rw [card_conjSub]
  rcases hF.maxea _ hB hBea hcard with h | h
  · have hn : x⁻¹ * g ∈ Mi := hnorm _ (fun y hy => by
      have := mul_mem_conjSub (g := x⁻¹ * g) hy
      rwa [h] at this)
    have hg' : g ∈ Mi := by
      have := Mi.mul_mem hxMi hn
      simpa using this
    exact hMi g hg'
  · exact absurd h (hnc _)

theorem burnsideF4d_Z1_normalizer_Q (hG : D.Good) :
    M₁ = Subgroup.normalizer (D.Q₁ : Set G) ∧ M₂ = Subgroup.normalizer (D.Q₂ : Set G) := by
  refine ⟨le_antisymm (fun m hm => mem_normalizer_of_conjSub_eq (L3Datum.conjSub_Q₁_eq hm))
    (fun n hn => hG.normalizer_Q₁ (fun x hx => (Subgroup.mem_normalizer_iff.mp hn x).mp hx)),
    le_antisymm (fun m hm => mem_normalizer_of_conjSub_eq (L3Datum.conjSub_Q₂_eq hm))
    (fun n hn => hG.normalizer_Q₂ (fun x hx => (Subgroup.mem_normalizer_iff.mp hn x).mp hx))⟩

theorem burnsideF4d_Z1_frattini (hG : D.Good) {Mi L : Subgroup G}
    (hSyl : IsSylowTwoOf D.S Mi) (hLM : L ≤ Mi) (hSL : D.S ≤ L)
    (hLnorm : ∀ m ∈ Mi, ∀ x ∈ L, m * x * m⁻¹ ∈ L) :
    ∀ m ∈ Mi, ∃ l ∈ L, l⁻¹ * m ∈ M₁ ⊓ M₂ := by
  intro m hm
  have hSylL : IsSylowTwoOf D.S L := F7.isSylowTwoOf_mono_right hSyl hSL hLM
  have hle : conjSub m D.S ≤ L := by
    intro y hy
    have h1 : m⁻¹ * y * m ∈ D.S := mem_conjSub.mp hy
    have h2 := hLnorm m hm _ (hSL h1)
    simpa [mul_assoc] using h2
  obtain ⟨l, hlL, hl⟩ :=
    F7.isSylowTwoOf_exists_conj_le hSylL hle (F7.isPGroup_conjSub D.S_pgroup)
  have heq : conjSub m D.S = conjSub l D.S :=
    Subgroup.eq_of_le_of_card_ge hl (by rw [card_conjSub, card_conjSub])
  refine ⟨l, hlL, ?_⟩
  rw [← L3Datum.normalizer_S_eq hG]
  apply mem_normalizer_of_conjSub_eq
  rw [conjSub_mul, heq, conjSub_conjSub_inv]

theorem burnsideF4d_Z1_members_eq (hG : D.Good) {Mi L Q : Subgroup G}
    (hSyl : IsSylowTwoOf D.S Mi) (hLM : L ≤ Mi) (hSL : D.S ≤ L)
    (hLnorm : ∀ m ∈ Mi, ∀ x ∈ L, m * x * m⁻¹ ∈ L)
    (hcov : ∀ x ∈ Q, x ≠ 1 → ∃ m ∈ Mi, m * x * m⁻¹ ∈ D.Z)
    (hZQ : D.Z ≤ Q) (hQnorm : ∀ m ∈ Mi, conjSub m Q = Q) :
    {W : Subgroup G | (∃ g : G, W = conjSub g D.Z) ∧ W ≤ Q} =
      {W : Subgroup G | ∃ l ∈ L, W = conjSub l D.Z} := by
  ext W
  constructor
  · rintro ⟨⟨a, rfl⟩, hWQ⟩
    obtain ⟨m, hm, hmeq⟩ := hG.members_in_Q hcov hWQ
    obtain ⟨l, hlL, hlm⟩ := burnsideF4d_Z1_frattini hG hSyl hLM hSL hLnorm m hm
    refine ⟨l, hlL, ?_⟩
    rw [← hmeq]
    have : conjSub m D.Z = conjSub l (conjSub (l⁻¹ * m) D.Z) := by
      rw [← conjSub_mul]
      congr 1
      group
    rw [this, L3Datum.conjSub_Z_eq (D := D) hlm]
  · rintro ⟨l, hlL, rfl⟩
    refine ⟨⟨l, rfl⟩, ?_⟩
    have := conjSub_mono l hZQ
    rwa [hQnorm l (hLM hlL)] at this

end Z1Datum

section Z1Count

variable {G : Type} [Group G] [Finite G]

theorem burnsideF4d_Z1_card_ne_one (W : Subgroup G) :
    Nat.card {x : G // x ∈ W ∧ x ≠ 1} = Nat.card W - 1 := by
  have h1 : Nat.card {x : G // x ∈ W ∧ x ≠ 1} = ((W : Set G) \ {1}).ncard := by
    rw [← Nat.card_coe_set_eq]
    exact Nat.card_congr (Equiv.subtypeEquivRight (fun x => by simp))
  have h2 : (W : Set G).ncard = Nat.card W := (Nat.card_coe_set_eq (W : Set G)).symm
  rw [h1, Set.ncard_diff_singleton_of_mem (show (1 : G) ∈ (W : Set G) from W.one_mem), h2]

theorem burnsideF4d_Z1_count (𝒲 : Set (Subgroup G)) (Q : Subgroup G) {q : ℕ}
    (hq : 2 ≤ q) (hQ : Nat.card Q = q ^ 2)
    (hW : ∀ W ∈ 𝒲, W ≤ Q ∧ Nat.card W = q)
    (hcov : ∀ x ∈ Q, x ≠ 1 → ∃ W ∈ 𝒲, x ∈ W)
    (huniq : ∀ W ∈ 𝒲, ∀ W' ∈ 𝒲, ∀ x : G, x ∈ W → x ∈ W' → x ≠ 1 → W = W') :
    𝒲.ncard = q + 1 := by
  classical
  haveI : Finite (Subgroup G) :=
    Finite.of_injective (SetLike.coe : Subgroup G → Set G) SetLike.coe_injective
  haveI : Fintype 𝒲 := Fintype.ofFinite _
  let φ : (Σ W : 𝒲, {x : G // x ∈ (W : Subgroup G) ∧ x ≠ 1}) → {x : G // x ∈ Q ∧ x ≠ 1} :=
    fun p => ⟨p.2.1, (hW p.1 p.1.2).1 p.2.2.1, p.2.2.2⟩
  have hinj : Function.Injective φ := by
    rintro ⟨⟨W, hW1⟩, ⟨x, hxW, hx1⟩⟩ ⟨⟨W', hW'1⟩, ⟨x', hxW', hx1'⟩⟩ h
    have hxx : x = x' := congrArg Subtype.val h
    subst hxx
    have : W = W' := huniq W hW1 W' hW'1 x hxW hxW' hx1
    subst this
    rfl
  have hsurj : Function.Surjective φ := by
    rintro ⟨x, hxQ, hx1⟩
    obtain ⟨W, hW1, hxW⟩ := hcov x hxQ hx1
    exact ⟨⟨⟨W, hW1⟩, ⟨x, hxW, hx1⟩⟩, rfl⟩
  have hcW : ∀ W : 𝒲, Nat.card {x : G // x ∈ (W : Subgroup G) ∧ x ≠ 1} = q - 1 := fun W => by
    rw [burnsideF4d_Z1_card_ne_one, (hW W W.2).2]
  have h1 : Nat.card (Σ W : 𝒲, {x : G // x ∈ (W : Subgroup G) ∧ x ≠ 1}) =
      Nat.card 𝒲 * (q - 1) := by
    rw [Nat.card_sigma]
    simp only [hcW, Finset.sum_const, Finset.card_univ, smul_eq_mul]
    rw [Nat.card_eq_fintype_card]
  have h2 : Nat.card {x : G // x ∈ Q ∧ x ≠ 1} = q ^ 2 - 1 := by
    rw [burnsideF4d_Z1_card_ne_one, hQ]
  have h3 := Nat.card_congr (Equiv.ofBijective φ ⟨hinj, hsurj⟩)
  rw [h1, h2] at h3
  rw [← Nat.card_coe_set_eq]
  obtain ⟨r, rfl⟩ : ∃ r, q = r + 2 := ⟨q - 2, by omega⟩
  have h4 : (r + 2) ^ 2 - 1 = (r + 3) * (r + 1) := by
    have : (r + 2) ^ 2 = (r + 3) * (r + 1) + 1 := by ring
    exact Nat.sub_eq_of_eq_add this
  have h5 : r + 2 - 1 = r + 1 := by omega
  rw [h4, h5] at h3
  have := Nat.eq_of_mul_eq_mul_right (Nat.succ_pos r) h3
  omega

variable {M₁ M₂ : Subgroup G} {D : L3Datum M₁ M₂}

theorem burnsideF4d_Z1_ncard (hG : D.Good) {Mi Q : Subgroup G} {q : ℕ} (hq : 2 ≤ q)
    (hZ : Nat.card D.Z = q) (hQc : Nat.card Q = q ^ 2)
    (hcov : ∀ x ∈ Q, x ≠ 1 → ∃ m ∈ Mi, m * x * m⁻¹ ∈ D.Z) (hZQ : D.Z ≤ Q)
    (hQnorm : ∀ m ∈ Mi, conjSub m Q = Q) :
    Set.ncard {W : Subgroup G | (∃ g : G, W = conjSub g D.Z) ∧ W ≤ Q} = q + 1 := by
  refine burnsideF4d_Z1_count _ Q hq hQc ?_ ?_ ?_
  · rintro W ⟨⟨g, rfl⟩, hWQ⟩
    exact ⟨hWQ, by rw [card_conjSub, hZ]⟩
  · intro x hxQ hx1
    obtain ⟨m, hm, hmx⟩ := hcov x hxQ hx1
    refine ⟨conjSub m⁻¹ D.Z, ⟨⟨m⁻¹, rfl⟩, ?_⟩, ?_⟩
    · have := conjSub_mono m⁻¹ hZQ
      rwa [hQnorm m⁻¹ (Mi.inv_mem hm)] at this
    · rw [mem_conjSub, inv_inv]
      exact hmx
  · rintro W ⟨⟨a, rfl⟩, -⟩ W' ⟨⟨b, rfl⟩, -⟩ x hxa hxb hx1
    exact hG.TI hxa hxb hx1

end Z1Count

section Z1Transport

variable {X M : Type} [Group X] [Group M] {N : Subgroup X}

theorem burnsideF4d_Z1_L_norm (Gp : Subgroup X) [Gp.Normal] (b : ↥N →* M)
    (hb : Function.Injective b) :
    ∀ m ∈ subImg b N, ∀ x ∈ oPPrime 2 (subImg b (Gp ⊓ N)),
      m * x * m⁻¹ ∈ oPPrime 2 (subImg b (Gp ⊓ N)) := by
  intro m hm x hx
  have hrw := burnsideF4d_subImg_oPPrime b hb (inf_le_right : Gp ⊓ N ≤ N) 2
  rw [hrw] at hx ⊢
  obtain ⟨n, hnN, -, rfl⟩ := mem_subImg.mp hm
  obtain ⟨y, hyN, hyL, rfl⟩ := mem_subImg.mp hx
  have hnorm : n ∈ Subgroup.normalizer (oPPrime 2 (Gp ⊓ N) : Set X) :=
    burnsideF4d_Z1_normalizer_oPPrime (burnsideF4d_Z1_mem_normalizer_inf Gp hnN)
  have hyL' : n * y * n⁻¹ ∈ oPPrime 2 (Gp ⊓ N) :=
    (Subgroup.mem_normalizer_iff.mp hnorm y).mp hyL
  have hyN' : n * y * n⁻¹ ∈ N := N.mul_mem (N.mul_mem hnN hyN) (N.inv_mem hnN)
  have e : b ⟨n * y * n⁻¹, hyN'⟩ = b ⟨n, hnN⟩ * b ⟨y, hyN⟩ * (b ⟨n, hnN⟩)⁻¹ := by
    rw [show (⟨n * y * n⁻¹, hyN'⟩ : ↥N) = ⟨n, hnN⟩ * ⟨y, hyN⟩ * ⟨n, hnN⟩⁻¹ from rfl,
      map_mul, map_mul, map_inv]
  rw [← e]
  exact mem_subImg_of_mem b hyN' hyL'

theorem burnsideF4d_Z1_subImg_le_oPPrime (b : ↥N →* M) (hb : Function.Injective b)
    {P K : Subgroup X} (hKN : K ≤ N) (hPK : P ≤ K) (hP : IsPGroup 2 P) :
    subImg b P ≤ oPPrime 2 (subImg b K) := by
  rw [burnsideF4d_subImg_oPPrime b hb hKN 2]
  exact subImg_mono b (burnsideF4d_Z1_le_oPPrime hP hPK)

end Z1Transport

section Z1Main

theorem as_F_4_46 : F_4_46 := by
  intro κ f E _ Gp M₁ M₂ Y _ β M _ ε z hyp hnotL43 hκ T hT
  subst hκ
  have hf : 2 ≤ f := burnsideF4d_L3_two_le_f hyp
  haveI : Finite E := hyp.amalgam.finite
  haveI : Finite M := hyp.finite_M
  haveI : Gp.Normal := hyp.amalgam.toHypF_4_4g.normal
  obtain ⟨D, hG, hzD, hDS, hQ₁, hQ₂⟩ := burnsideF4d_L3_setup hf hyp
  obtain ⟨-, hcZ, hcQ₁, hcQ₂⟩ := burnsideF4d_L3_cards hf hyp D hDS hQ₁ hQ₂
  have hT' : IsSylowTwoOf T (MiOne β ε ⊓ MiTwo β ε) := hT
  have hTS : T = D.S := burnsideF4d_sylow_eq_S D hT'
  have hz1 : z ≠ 1 := hyp.z_inv.1
  have hb₁ : Function.Injective (burnsideF4d_bOne β ε) :=
    hyp.inj.comp (f1_injective β hyp.faithful)
  have hb₂ : Function.Injective (burnsideF4d_bTwo β ε) :=
    hyp.inj.comp (f2_injective β hyp.faithful)
  have hSyl₁ : IsSylowTwoOf D.S (MiOne β ε) := ⟨D.S_le_M₁, D.S_pgroup, D.S_index⟩
  have hSyl₂ : IsSylowTwoOf D.S (MiTwo β ε) :=
    F7.isSylowTwoOf_mono_right hG.sylow_top D.S_le_M₂ le_top
  have hq : 2 ≤ 2 ^ f := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hL₁M : oPPrime 2 (GiOne Gp β ε) ≤ MiOne β ε := by
    refine (burnsideF4d_oPPrime_le _).trans ?_
    rw [burnsideF4d_GiOne_eq, burnsideF4d_MiOne_eq]
    exact subImg_mono _ inf_le_right
  have hL₂M : oPPrime 2 (GiTwo Gp β ε) ≤ MiTwo β ε := by
    refine (burnsideF4d_oPPrime_le _).trans ?_
    rw [burnsideF4d_GiTwo_eq, burnsideF4d_MiTwo_eq]
    exact subImg_mono _ inf_le_right
  have hP₁ : pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ≤ M₁ :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans (inf_le_right.trans inf_le_left)
  have hP₂ : pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ≤ M₂ :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans (inf_le_right.trans inf_le_right)
  have hP2g : IsPGroup 2 (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hSL₁ : D.S ≤ oPPrime 2 (GiOne Gp β ε) := by
    rw [hDS, burnsideF4d_SinM_eq, burnsideF4d_GiOne_eq]
    exact burnsideF4d_Z1_subImg_le_oPPrime _ hb₁ (inf_le_right : Gp ⊓ M₁ ≤ M₁)
      (le_trans (CFSG.LieType.BorelTits.pCoreOf_le 2 _) (inf_le_inf_left Gp inf_le_left)) hP2g
  have hSL₂ : D.S ≤ oPPrime 2 (GiTwo Gp β ε) := by
    have hagree : ∀ g (h1 : g ∈ M₁) (h2 : g ∈ M₂),
        burnsideF4d_bOne β ε ⟨g, h1⟩ = burnsideF4d_bTwo β ε ⟨g, h2⟩ :=
      (burnsideF4d_amalgIsoM β hyp.faithful ε hyp.inj).agree
    have hSb : subImg (burnsideF4d_bOne β ε) (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) =
        subImg (burnsideF4d_bTwo β ε) (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) :=
      subImg_eq_of_agree hagree hP₁ hP₂
    rw [hDS, burnsideF4d_SinM_eq, hSb, burnsideF4d_GiTwo_eq]
    exact burnsideF4d_Z1_subImg_le_oPPrime _ hb₂ (inf_le_right : Gp ⊓ M₂ ≤ M₂)
      (le_trans (CFSG.LieType.BorelTits.pCoreOf_le 2 _) (inf_le_inf_left Gp inf_le_right)) hP2g
  have hLnorm₁ : ∀ m ∈ MiOne β ε, ∀ x ∈ oPPrime 2 (GiOne Gp β ε),
      m * x * m⁻¹ ∈ oPPrime 2 (GiOne Gp β ε) := by
    rw [burnsideF4d_GiOne_eq, burnsideF4d_MiOne_eq]
    exact burnsideF4d_Z1_L_norm Gp _ hb₁
  have hLnorm₂ : ∀ m ∈ MiTwo β ε, ∀ x ∈ oPPrime 2 (GiTwo Gp β ε),
      m * x * m⁻¹ ∈ oPPrime 2 (GiTwo Gp β ε) := by
    rw [burnsideF4d_GiTwo_eq, burnsideF4d_MiTwo_eq]
    exact burnsideF4d_Z1_L_norm Gp _ hb₂
  rw [← hQ₁, ← hQ₂, hTS]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  ·
    intro j hj1 hj2
    have hjsq : j ^ 2 = 1 := by rw [pow_two]; exact hj2
    obtain ⟨a, ha⟩ := hG.inv_conj_Z hjsq hj1
    have hx1 : a⁻¹ * j * a ≠ 1 := conj_ne_one' hj1
    obtain ⟨b, -, hb⟩ := D.trans _ ha hx1 z hzD hz1
    rw [isConj_iff]
    refine ⟨a * b⁻¹, ?_⟩
    calc a * b⁻¹ * z * (a * b⁻¹)⁻¹
        = a * b⁻¹ * (b * (a⁻¹ * j * a) * b⁻¹) * (a * b⁻¹)⁻¹ := by rw [hb]
      _ = j := by group
  ·
    intro j hj1 hj2
    exact burnsideF4d_Z1_involution_centralizer hG hj1 hj2
  ·
    refine ⟨fun g hg => ?_, fun g hg => ?_⟩
    · exact burnsideF4d_Z1_weak hG D.frame (fun x => hG.Q_not_conj x) hSyl₁
        (fun n hn => hG.normalizer_Q₁ hn) (fun m hm => L3Datum.conjSub_Q₁_eq hm) hg
    · exact burnsideF4d_Z1_weak hG D.frame.symm (fun x => hG.Q_not_conj' x) hSyl₂
        (fun n hn => hG.normalizer_Q₂ hn) (fun m hm => L3Datum.conjSub_Q₂_eq hm) hg
  ·
    obtain ⟨hN₁, hN₂⟩ := burnsideF4d_Z1_normalizer_Q hG
    refine ⟨hN₁, hN₂, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact burnsideF4d_Z1_members_eq hG hSyl₁ hL₁M hSL₁ hLnorm₁ D.cov₁ D.Z_le_Q₁
        (fun m hm => L3Datum.conjSub_Q₁_eq hm)
    · exact burnsideF4d_Z1_ncard hG hq hcZ hcQ₁ D.cov₁ D.Z_le_Q₁ (fun m hm => L3Datum.conjSub_Q₁_eq hm)
    · exact burnsideF4d_Z1_members_eq hG hSyl₂ hL₂M hSL₂ hLnorm₂ D.cov₂ D.Z_le_Q₂
        (fun m hm => L3Datum.conjSub_Q₂_eq hm)
    · exact burnsideF4d_Z1_ncard hG hq hcZ hcQ₂ D.cov₂ D.Z_le_Q₂ (fun m hm => L3Datum.conjSub_Q₂_eq hm)
  ·
    exact L3Datum.normalizer_S_eq hG

end Z1Main

end F4dPartZ1

section F4dPartZ2

open CFSG.Open CFSG.ASVolI.ChF CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431
  CFSG.Quasithin.H13.F431.L3

section Dihedral

variable {G : Type} [Group G]

theorem burnsideF4d_Z2_comm_pow {w u : G} (hw : w * u * w⁻¹ = u⁻¹) (m : ℕ)
    (hm : u ^ m * u ^ m = 1) : w * u ^ m = u ^ m * w := by
  have h1 : w * u ^ m * w⁻¹ = u ^ m := by
    rw [← conj_pow, hw, inv_pow]
    exact inv_eq_of_mul_eq_one_right hm
  exact mul_inv_eq_iff_eq_mul.mp h1

theorem burnsideF4d_Z2_dihedral [Finite G] {x y : G} (hx : x * x = 1) (hy : y * y = 1)
    (heven : Even (orderOf (x * y))) :
    ∃ j : G, orderOf j = 2 ∧ x * j = j * x ∧ y * j = j * y := by
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy
  have hxu : x * (x * y) * x⁻¹ = (x * y)⁻¹ := by
    rw [mul_inv_rev, hxi, hyi]
    calc x * (x * y) * x = (x * x) * y * x := by group
      _ = y * x := by rw [hx, one_mul]
  have hyu : y * (x * y) * y⁻¹ = (x * y)⁻¹ := by
    rw [mul_inv_rev, hxi, hyi]
    calc y * (x * y) * y = y * x * (y * y) := by group
      _ = y * x := by rw [hy, mul_one]
  obtain ⟨k, hk⟩ := heven
  have hpos : 0 < orderOf (x * y) := orderOf_pos _
  have hdvd : 2 ∣ orderOf (x * y) := ⟨k, by omega⟩
  have hk2 : orderOf (x * y) / 2 = k := by omega
  have hm : (x * y) ^ k * (x * y) ^ k = 1 := by
    rw [← pow_add, ← hk]
    exact pow_orderOf_eq_one _
  refine ⟨(x * y) ^ k, ?_, burnsideF4d_Z2_comm_pow hxu k hm, burnsideF4d_Z2_comm_pow hyu k hm⟩
  have := orderOf_pow_orderOf_div (x := x * y) (n := 2) hpos.ne' hdvd
  rwa [hk2] at this

end Dihedral

section Cases

variable {G : Type} [Group G] [Finite G] {M₁ M₂ : Subgroup G} {D : L3Datum M₁ M₂}

theorem burnsideF4d_Z2_case_a (hG : D.Good) {z z' g : G} (hz : z ∈ D.Z) (hz1 : z ≠ 1)
    (hz' : z' ∈ conjSub g D.Z) (hz'1 : z' ≠ 1) (hbot : D.S ⊓ conjSub g D.S = ⊥) :
    Odd (orderOf (z * z')) := by
  by_contra hodd
  have heven : Even (orderOf (z * z')) := Nat.not_odd_iff_even.mp hodd
  have hz2 : z * z = 1 := by rw [← pow_two]; exact D.Z_sq hz
  have hz'2p : z' ^ 2 = 1 := sq_of_conj_sq (D.Z_sq (mem_conjSub.mp hz'))
  have hz'2 : z' * z' = 1 := by rw [← pow_two]; exact hz'2p
  obtain ⟨j, hj, hjz, hjz'⟩ := burnsideF4d_Z2_dihedral hz2 hz'2 heven
  have hj2 : j ^ 2 = 1 := by
    have := pow_orderOf_eq_one j
    rwa [hj] at this
  have hjS : j ∈ D.S :=
    L3Datum.two_elt_mem_S (D := D) (hG.cent z hz hz1 j hjz.symm) (k := 1) (by simpa using hj2)
  have hjP : j ∈ conjSub g D.S :=
    hG.two_elt_conj hz' hz'1 hjz'.symm (k := 1) (by simpa using hj2)
  have hjmem : j ∈ D.S ⊓ conjSub g D.S := Subgroup.mem_inf.mpr ⟨hjS, hjP⟩
  rw [hbot, Subgroup.mem_bot] at hjmem
  rw [hjmem, orderOf_one] at hj
  omega

theorem burnsideF4d_Z2_case_b (hG : D.Good)
    (hQZ : Nat.card D.Q₁ = Nat.card D.Z * Nat.card D.Z) {z z' g : G} (hg : g ∉ M₁ ⊓ M₂)
    (hz : z ∈ D.Z) (hz' : z' ∈ conjSub g D.Z) (hz'1 : z' ≠ 1) {Q : Subgroup G}
    (hQ : Q = D.Q₁ ∨ Q = D.Q₂) (hQg : Q = conjSub g D.Q₁ ∨ Q = conjSub g D.Q₂) :
    Q = D.Z ⊔ conjSub g D.Z ∧ orderOf (z * z') = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZQ : D.Z ≤ Q := by
    rcases hQ with rfl | rfl
    · exact D.Z_le_Q₁
    · exact D.Z_le_Q₂
  have hZgQ : conjSub g D.Z ≤ Q := by
    rcases hQg with h | h
    · rw [h]; exact conjSub_mono g D.Z_le_Q₁
    · rw [h]; exact conjSub_mono g D.Z_le_Q₂
  have hQea : IsElemAbelian 2 Q := by
    rcases hQ with rfl | rfl
    · exact D.frame.Q₁_ea
    · exact D.frame.Q₂_ea
  have hQcard : Nat.card Q = Nat.card D.Z * Nat.card D.Z := by
    rcases hQ with rfl | rfl
    · exact hQZ
    · rw [← D.frame.card_eq]; exact hQZ
  have hcomm : ∀ x ∈ D.Z, ∀ y ∈ conjSub g D.Z, x * y = y * x := fun x hx y hy =>
    F7.isElemAbelian_comm hQea (hZQ hx) (hZgQ hy)
  have hinf : D.Z ⊓ conjSub g D.Z = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    obtain ⟨hw1, hw2⟩ := Subgroup.mem_inf.mp hw
    exact Subgroup.mem_bot.mpr (hG.Z_inf_conj hg hw1 hw2)
  have hprod := B2F.card_sup_mul_card_inf_of_commute hcomm
  rw [hinf, Subgroup.card_bot, mul_one, card_conjSub] at hprod
  have hsup : D.Z ⊔ conjSub g D.Z = Q :=
    Subgroup.eq_of_le_of_card_ge (sup_le hZQ hZgQ) (by rw [hprod, hQcard])
  refine ⟨hsup.symm, ?_⟩
  have hzQ : z ∈ Q := hZQ hz
  have hz'Q : z' ∈ Q := hZgQ hz'
  have hz2 : z * z = 1 := by rw [← pow_two]; exact D.Z_sq hz
  have hz'2 : z' * z' = 1 := by
    rw [← pow_two]; exact sq_of_conj_sq (D.Z_sq (mem_conjSub.mp hz'))
  have hzz' : z' * z = z * z' := (F7.isElemAbelian_comm hQea hzQ hz'Q).symm
  have hu2 : (z * z') ^ 2 = 1 := by
    calc (z * z') ^ 2 = z * z' * (z * z') := by rw [pow_two]
      _ = z * (z' * z) * z' := by group
      _ = z * (z * z') * z' := by rw [hzz']
      _ = (z * z) * (z' * z') := by group
      _ = 1 := by rw [hz2, hz'2, one_mul]
  have hu1 : z * z' ≠ 1 := by
    intro h
    apply hz'1
    have h1 : z' = z⁻¹ := eq_inv_of_mul_eq_one_right h
    have h2 : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
    exact hG.Z_inf_conj hg ((h1.trans h2) ▸ hz) hz'
  exact orderOf_eq_prime hu2 hu1

theorem burnsideF4d_Z2_case_c (hG : D.Good) {z z' g a : G} (hz : z ∈ D.Z) (hz1 : z ≠ 1)
    (hz' : z' ∈ conjSub g D.Z) (hz'1 : z' ≠ 1) (hS : D.S ⊓ conjSub g D.S = conjSub a D.Z)
    (hne : conjSub a D.Z ≠ conjSub g D.Z) : orderOf (z * z') = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hz2p : z ^ 2 = 1 := D.Z_sq hz
  have hz2 : z * z = 1 := by rw [← pow_two]; exact hz2p
  have hz'2p : z' ^ 2 = 1 := sq_of_conj_sq (D.Z_sq (mem_conjSub.mp hz'))
  have hz'2 : z' * z' = 1 := by rw [← pow_two]; exact hz'2p
  obtain ⟨j, hjA, hj1⟩ := L3Datum.Z_ne_one_mem hG a
  have hj : j ∈ D.S ⊓ conjSub g D.S := by rw [hS]; exact hjA
  obtain ⟨hjS, hjP⟩ := Subgroup.mem_inf.mp hj
  have hzP : z ∈ conjSub a D.S :=
    hG.two_elt_conj hjA hj1 ((D.mem_Z.mp hz).2 j hjS).symm (k := 1) (by simpa using hz2p)
  have hz'P : z' ∈ conjSub a D.S :=
    hG.two_elt_conj hjA hj1 (L3Datum.commute_of_mem_conj (D := D) hz' hjP).symm (k := 1)
      (by simpa using hz'2p)
  have hc : z * z' * z⁻¹ * z'⁻¹ ∈ conjSub a D.Z := by
    have h := (D.frame.conj a).comm z hzP z' hz'P
    rwa [centerOf_conjSub] at h
  have hc2 : (z * z' * z⁻¹ * z'⁻¹) ^ 2 = 1 := sq_of_conj_sq (D.Z_sq (mem_conjSub.mp hc))
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  have hz'i : z'⁻¹ = z' := inv_eq_of_mul_eq_one_right hz'2
  rw [hzi, hz'i] at hc2
  have hu2 : (z * z') ^ 2 = z * z' * z * z' := by rw [pow_two]; group
  have hu4 : (z * z') ^ 2 ^ (1 + 1) = 1 := by
    have e : (2 : ℕ) ^ (1 + 1) = 2 * 2 := by norm_num
    rw [e, pow_mul, hu2]
    exact hc2
  have hnot : ¬ (z * z') ^ 2 ^ 1 = 1 := by
    rw [pow_one, hu2]
    intro h
    have h1 : z * z' * z = z' := by
      have := mul_eq_one_iff_eq_inv.mp h
      rw [this, hz'i]
    have hcomm : z' * z = z * z' := by
      calc z' * z = (z * z' * z) * z := by rw [h1]
        _ = z * z' * (z * z) := by group
        _ = z * z' := by rw [hz2, mul_one]
    have hH : z' ∈ M₁ ⊓ M₂ := hG.cent z hz hz1 z' hcomm
    have hz'S : z' ∈ D.S := L3Datum.two_elt_mem_S (D := D) hH (k := 1) (by simpa using hz'2p)
    have hz'P' : z' ∈ conjSub g D.S := conjSub_mono g D.Z_le_S hz'
    have hmem : z' ∈ D.S ⊓ conjSub g D.S := Subgroup.mem_inf.mpr ⟨hz'S, hz'P'⟩
    rw [hS] at hmem
    exact hne (hG.TI hmem hz' hz'1)
  have := orderOf_eq_prime_pow hnot hu4
  rw [this]
  norm_num

theorem burnsideF4d_Z2_main (hG : D.Good)
    (hQZ : Nat.card D.Q₁ = Nat.card D.Z * Nat.card D.Z) {z : G} (hz : z ∈ D.Z) (hz1 : z ≠ 1)
    {g : G} (hg : g ∉ M₁ ⊓ M₂) :
    (D.S ⊓ conjSub g D.S = ⊥ ∧ Odd (orderOf (z * (g * z * g⁻¹)))) ∨
    (D.S ⊓ conjSub g D.S = D.Z ⊔ conjSub g D.Z ∧
      (D.S ⊓ conjSub g D.S = D.Q₁ ∨ D.S ⊓ conjSub g D.S = D.Q₂) ∧
      orderOf (z * (g * z * g⁻¹)) = 2) ∨
    (D.Z ≠ D.S ⊓ conjSub g D.S ∧ conjSub g D.Z ≠ D.S ⊓ conjSub g D.S ∧
      (∃ h : G, D.S ⊓ conjSub g D.S = conjSub h D.Z) ∧ orderOf (z * (g * z * g⁻¹)) = 4) := by
  have hz' : g * z * g⁻¹ ∈ conjSub g D.Z := mul_mem_conjSub hz
  have hz'1 : g * z * g⁻¹ ≠ 1 := by
    intro h
    apply hz1
    calc z = g⁻¹ * (g * z * g⁻¹) * g := by group
      _ = 1 := by rw [h]; group
  rcases hG.trichotomy hg with hbot | ⟨Q, hQ, hS, hQg⟩ | ⟨a, hS, hne1, hne2⟩
  · exact Or.inl ⟨hbot, burnsideF4d_Z2_case_a hG hz hz1 hz' hz'1 hbot⟩
  · obtain ⟨hsup, hord⟩ := burnsideF4d_Z2_case_b hG hQZ hg hz hz' hz'1 hQ hQg
    refine Or.inr (Or.inl ⟨hS.trans hsup, ?_, hord⟩)
    rw [hS]
    exact hQ
  · refine Or.inr (Or.inr ⟨?_, ?_, ⟨a, hS⟩, burnsideF4d_Z2_case_c hG hz hz1 hz' hz'1 hS hne2⟩)
    · intro h
      rw [hS] at h
      exact hne1 h.symm
    · intro h
      rw [hS] at h
      exact hne2 h.symm

end Cases

theorem as_F_4_48 : F_4_48 := by
  intro κ f E _ Gp M₁ M₂ Y _ β M _ ε z hyp hnotL43 hκ T hT g hg
  subst hκ
  have hf := burnsideF4d_L3_two_le_f hyp
  obtain ⟨D, hG, hzD, hDS, hQ₁, hQ₂⟩ := burnsideF4d_L3_setup hf hyp
  haveI := hyp.finite_M
  have hTS : T = D.S := burnsideF4d_sylow_eq_S D hT
  subst hTS
  obtain ⟨-, hZ, hQ1, -⟩ := burnsideF4d_L3_cards hf hyp D hDS hQ₁ hQ₂
  have hQZ : Nat.card D.Q₁ = Nat.card D.Z * Nat.card D.Z := by
    rw [hQ1, hZ]
    ring
  have key := burnsideF4d_Z2_main hG hQZ hzD hyp.z_inv.1 hg
  rw [← hQ₁, ← hQ₂]
  exact key

end F4dPartZ2

section F4dPartZ3

section Z3Group

theorem burnsideF4d_Z3_card_mul_le {G : Type*} [Group G] [Finite G] (A B : Subgroup G) :
    Nat.card A * Nat.card B ≤ Nat.card ↥(A ⊔ B) * Nat.card ↥(A ⊓ B) := by
  have e1 : A.relIndex B * Nat.card ↥(A ⊓ B) = Nat.card B := by
    rw [Subgroup.relIndex_mul_card]
  have e2 : A.relIndex (A ⊔ B) * Nat.card A = Nat.card ↥(A ⊔ B) := by
    have := Subgroup.relIndex_mul_card A (A ⊔ B)
    rwa [inf_eq_left.mpr le_sup_left] at this
  have hne0 : A.relIndex (A ⊔ B) ≠ 0 := by
    intro h
    rw [h] at e2
    have : 0 < Nat.card ↥(A ⊔ B) := Nat.card_pos
    omega
  have hle : A.relIndex B ≤ A.relIndex (A ⊔ B) :=
    Subgroup.relIndex_le_of_le_right le_sup_right hne0
  calc Nat.card A * Nat.card B = Nat.card A * (A.relIndex B * Nat.card ↥(A ⊓ B)) := by rw [e1]
    _ ≤ Nat.card A * (A.relIndex (A ⊔ B) * Nat.card ↥(A ⊓ B)) := by gcongr
    _ = Nat.card ↥(A ⊔ B) * Nat.card ↥(A ⊓ B) := by rw [← e2]; ring

theorem burnsideF4d_Z3_solvable_of_normal {G : Type} [Group G] [Finite G] {A N : Subgroup G}
    [N.Normal] (hN : Group.IsSolvable ↥(A ⊓ N)) (hodd : Odd (N.relIndex A)) :
    Group.IsSolvable ↥A := by
  let ι : ↥(N.subgroupOf A) →* ↥(A ⊓ N) :=
    { toFun := fun x => ⟨(x.1 : G), x.1.2, x.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hι : Function.Injective ι := by
    intro a b h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun x : ↥(A ⊓ N) => (x : G)) h
  haveI : Group.IsSolvable ↥(N.subgroupOf A) := Group.isSolvable_of_isSolvable_injective hι
  haveI : Group.IsSolvable (↥A ⧸ N.subgroupOf A) := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  exact Group.isSolvable_of_ker_le_range (N.subgroupOf A).subtype
    (QuotientGroup.mk' (N.subgroupOf A))
    (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])

end Z3Group

section Z3Core

open CFSG.BenderSuzuki

theorem burnsideF4d_Z3_solvable_of_borel {G : Type} [Group G] [Finite G] {M₀ K : Subgroup G}
    (hK : K ≤ M₀ ⊓ involutionCore G)
    (hB : Group.IsSolvable ↥(((M₀ ⊓ involutionCore G).subgroupOf (involutionCore G)).map
      (QuotientGroup.mk' (twoPrimeCore (involutionCore G))))) : Group.IsSolvable ↥K := by
  set L := involutionCore G
  set T := twoPrimeCore L
  have hTsolv : Group.IsSolvable ↥T := by
    have hodd : Odd (Nat.card T) :=
      Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := L))
    exact CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  let g : ↥K →* ↥(((M₀ ⊓ L).subgroupOf L).map (QuotientGroup.mk' T)) :=
    { toFun := fun c => ⟨QuotientGroup.mk' T ⟨c, (hK c.2).2⟩,
        ⟨⟨c, (hK c.2).2⟩, ⟨(hK c.2).1, (hK c.2).2⟩, rfl⟩⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hmem : ∀ k : ↥g.ker, (⟨k.1.1, (hK k.1.2).2⟩ : L) ∈ T := by
    intro k
    have h := k.2
    rw [MonoidHom.mem_ker] at h
    have h' := congrArg Subtype.val h
    exact (QuotientGroup.eq_one_iff _).mp h'
  let θ : ↥g.ker →* ↥T :=
    { toFun := fun k => ⟨⟨k.1.1, (hK k.1.2).2⟩, hmem k⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hθ : Function.Injective θ := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun x : T => ((x : L) : G)) hab
  haveI : Group.IsSolvable ↥g.ker := Group.isSolvable_of_isSolvable_injective hθ
  exact Group.isSolvable_of_ker_le_range g.ker.subtype g (by rw [Subgroup.range_subtype])

theorem burnsideF4d_Z3_elemAbelian_le_core {G : Type} [Group G] {Q : Subgroup G}
    (hQ : CFSG.Open.IsElemAbelian 2 Q) : Q ≤ involutionCore G := by
  intro x hx
  by_cases hx1 : x = 1
  · rw [hx1]
    exact Subgroup.one_mem _
  · exact Subgroup.subset_closure ⟨hx1, CFSG.Quasithin.F7.isElemAbelian_pow_eq_one hQ hx⟩

end Z3Core

section Z3Datum

open CFSG.BenderSuzuki CFSG.Quasithin.H13.F431.L3 CFSG.Semidihedral.ParameterFive

theorem burnsideF4d_Z3_S_le_core {G : Type} [Group G] [Finite G] {M₁ M₂ : Subgroup G}
    (D : L3Datum M₁ M₂) {r : ℕ} (hS : Nat.card D.S = r ^ 3) (hZ : Nat.card D.Z = r)
    (hQ₁ : Nat.card D.Q₁ = r ^ 2) (hQ₂ : Nat.card D.Q₂ = r ^ 2) :
    D.S ≤ involutionCore G := by
  have hr : 0 < r := by
    rw [← hZ]
    exact Nat.card_pos
  have h1 := burnsideF4d_Z3_card_mul_le D.Q₁ D.Q₂
  have hinf : D.Q₁ ⊓ D.Q₂ = D.Z := D.frame.inter
  rw [hinf, hZ, hQ₁, hQ₂] at h1
  have h2 : r ^ 3 ≤ Nat.card ↥(D.Q₁ ⊔ D.Q₂) := by
    have h3 : r ^ 3 * r ≤ Nat.card ↥(D.Q₁ ⊔ D.Q₂) * r := by
      calc r ^ 3 * r = r ^ 2 * r ^ 2 := by ring
        _ ≤ _ := h1
    exact Nat.le_of_mul_le_mul_right h3 hr
  have hle : D.Q₁ ⊔ D.Q₂ ≤ D.S := sup_le D.frame.Q₁_le D.frame.Q₂_le
  have heq : D.Q₁ ⊔ D.Q₂ = D.S :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hS]; exact h2)
  rw [← heq]
  exact sup_le (burnsideF4d_Z3_elemAbelian_le_core D.frame.Q₁_ea)
    (burnsideF4d_Z3_elemAbelian_le_core D.frame.Q₂_ea)

theorem burnsideF4d_Z3_sup_eq_top {G : Type} [Group G] [Finite G]
    {M₁ M₂ : Subgroup G} (D : L3Datum M₁ M₂) (hG : D.Good) {z : G} (hz : z ∈ D.Z) (hz1 : z ≠ 1)
    (hC : Subgroup.centralizer ({z} : Set G) ≤ M₁) {r : ℕ} (hS : Nat.card D.S = r ^ 3)
    (hZ : Nat.card D.Z = r) (hQ₁ : Nat.card D.Q₁ = r ^ 2) (hQ₂ : Nat.card D.Q₂ = r ^ 2) :
    M₁ ⊔ M₂ = ⊤ := by
  by_contra hne
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : orderOf z = 2 := orderOf_eq_prime (D.Z_sq hz) hz1
  have hM : BenderSuzuki.IsStronglyEmbedded (M₁ ⊔ M₂) :=
    isStronglyEmbedded_of_conj hord hne (hC.trans le_sup_left)
      (fun (x : G) (hx : x ∈ M₁ ⊔ M₂) (hx2 : orderOf x = 2) => by
        have hx2' : x ^ 2 = 1 := by
          have := pow_orderOf_eq_one x
          rwa [hx2] at this
        have hx1 : x ≠ 1 := by
          intro h
          rw [h, orderOf_one] at hx2
          omega
        exact hG.inv_conj_in_M0 hz hz1 hx hx2' hx1)
  have hSL : D.S ≤ involutionCore G := burnsideF4d_Z3_S_le_core D hS hZ hQ₁ hQ₂
  rcases theorem_SE (M₁ ⊔ M₂) hM with hlow | hB
  · apply hlow
    obtain ⟨E, hE4, hE2⟩ := CFSG.Quasithin.H13.F431.L3.exists_klein_four D.frame.Q₁_ea
      D.frame.four_le
    have hEL : E ≤ involutionCore G := by
      intro x hx
      by_cases hx1 : x = 1
      · rw [hx1]
        exact Subgroup.one_mem _
      · exact Subgroup.subset_closure ⟨hx1, hE2 x hx⟩
    refine ⟨E.subgroupOf (involutionCore G), ?_, ?_⟩
    · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEL).toEquiv, hE4]
    · rintro ⟨⟨x, hxL⟩, hxE⟩
      apply Subtype.ext
      apply Subtype.ext
      exact hE2 x hxE
  · obtain ⟨-, -, hsolv, -⟩ := hB
    have hK : Group.IsSolvable ↥(M₁ ⊓ involutionCore G) :=
      burnsideF4d_Z3_solvable_of_borel (K := M₁ ⊓ involutionCore G)
        (fun x hx => ⟨Subgroup.mem_sup_left hx.1, hx.2⟩) hsolv
    have hdvd : (involutionCore G).relIndex M₁ ∣ D.S.relIndex M₁ :=
      Subgroup.relIndex_dvd_of_le_left M₁ hSL
    have h2 : ¬ 2 ∣ (involutionCore G).relIndex M₁ := fun h => D.S_index (dvd_trans h hdvd)
    have hodd : Odd ((involutionCore G).relIndex M₁) := by
      rcases Nat.even_or_odd ((involutionCore G).relIndex M₁) with h | h
      · exact absurd (even_iff_two_dvd.mp h) h2
      · exact h
    exact D.nonsolv (burnsideF4d_Z3_solvable_of_normal hK hodd)

end Z3Datum

section Z3Range

open CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion CFSG.ASVolI.ChF

theorem burnsideF4d_Z3_f1_sup_f2 {E : Type} [Group E] {M₁ M₂ : Subgroup E} {Y : Type} [Group Y]
    (β : Cpl M₁ M₂ Y) : (f1 (c := β)).range ⊔ (f2 (c := β)).range = ⊤ := by
  have h1 : (f1 (c := β)).range.map (β.φ1.range ⊔ β.φ2.range).subtype = β.φ1.range := by
    ext y
    constructor
    · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
      exact ⟨a, rfl⟩
    · rintro ⟨a, rfl⟩
      exact ⟨_, ⟨a, rfl⟩, rfl⟩
  have h2 : (f2 (c := β)).range.map (β.φ1.range ⊔ β.φ2.range).subtype = β.φ2.range := by
    ext y
    constructor
    · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
      exact ⟨a, rfl⟩
    · rintro ⟨a, rfl⟩
      exact ⟨_, ⟨a, rfl⟩, rfl⟩
  refine Subgroup.map_injective (f := (β.φ1.range ⊔ β.φ2.range).subtype)
    (Subgroup.subtype_injective _) ?_
  rw [Subgroup.map_sup, h1, h2, Subgroup.map_top, Subgroup.range_subtype]

theorem burnsideF4d_Z3_range_epsG {E : Type} [Group E] {M₁ M₂ : Subgroup E} {Y : Type} [Group Y]
    {M : Type} [Group M] (β : Cpl M₁ M₂ Y) (ε : Y →* M) :
    (epsG β ε).range = MiOne β ε ⊔ MiTwo β ε := by
  rw [MonoidHom.range_eq_map, ← burnsideF4d_Z3_f1_sup_f2 β, Subgroup.map_sup]
  rfl

end Z3Range

section Z3Final

open CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion CFSG.ASVolI.ChF
  CFSG.Quasithin.H13.F431.L3

theorem as_F_4_45 : F_4_45 := by
  intro κ f E _ Gp M₁ M₂ Y _ β M _ ε z hyp _ hκ
  subst hκ
  haveI := hyp.finite_M
  have hf : 2 ≤ f := burnsideF4d_L3_two_le_f hyp
  obtain ⟨D, hG, hz, hDS, hQ₁, hQ₂⟩ := burnsideF4d_L3_setup hf hyp
  obtain ⟨hS, hZ, hQ1, hQ2⟩ := burnsideF4d_L3_cards hf hyp D hDS hQ₁ hQ₂
  have hz1 : z ≠ 1 := hyp.z_inv.1
  have htop := burnsideF4d_Z3_sup_eq_top D hG hz hz1 hyp.hb hS hZ hQ1 hQ2
  rw [burnsideF4d_Z3_range_epsG]
  exact htop

end Z3Final

end F4dPartZ3

section F4dPartZ4

open CFSG.Open CFSG.ASVolI.ChF CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431
  CFSG.Quasithin.H13.F431.L3

section ConjDatum

variable {M : Type} [Group M] [Finite M] {M₁ M₂ : Subgroup M}

theorem burnsideF4d_Z4_mem_conjSub_inv_mul {n m x : M} {K : Subgroup M} :
    x ∈ conjSub (n⁻¹ * m) K ↔ n * x * n⁻¹ ∈ conjSub m K := by
  rw [mem_conjSub, mem_conjSub]
  rw [show (n⁻¹ * m)⁻¹ * x * (n⁻¹ * m) = m⁻¹ * (n * x * n⁻¹) * m by group]

@[expose] def burnsideF4d_Z4_conjDatum (D : L3Datum M₁ M₂) {n : M} (hn : n ∈ M₁ ⊓ M₂) :
    L3Datum M₁ M₂ where
  S := D.S
  B := conjSub n D.B
  Q₁ := D.Q₁
  Q₂ := D.Q₂
  s₁ := n * D.s₁ * n⁻¹
  s₂ := n * D.s₂ * n⁻¹
  S_eq := D.S_eq
  B_le := by
    intro x hx
    rw [mem_conjSub] at hx
    have h1 := (M₁ ⊓ M₂).mul_mem ((M₁ ⊓ M₂).mul_mem hn (D.B_le hx)) ((M₁ ⊓ M₂).inv_mem hn)
    rwa [show n * (n⁻¹ * x * n) * n⁻¹ = x by group] at h1
  B_odd := by
    rw [card_conjSub]
    exact D.B_odd
  mul_SB := by
    intro h hh
    have hh' : n⁻¹ * h * n ∈ M₁ ⊓ M₂ :=
      (M₁ ⊓ M₂).mul_mem ((M₁ ⊓ M₂).mul_mem ((M₁ ⊓ M₂).inv_mem hn) hh) hn
    obtain ⟨s, hs, b, hb, hsb⟩ := D.mul_SB _ hh'
    refine ⟨n * s * n⁻¹, D.S_norm n hn s hs, n * b * n⁻¹, mul_mem_conjSub hb, ?_⟩
    calc h = n * (n⁻¹ * h * n) * n⁻¹ := by group
      _ = n * (s * b) * n⁻¹ := by rw [hsb]
      _ = n * s * n⁻¹ * (n * b * n⁻¹) := by group
  S_index := D.S_index
  frame := D.frame
  Q₁_norm := D.Q₁_norm
  Q₂_norm := D.Q₂_norm
  trans := by
    intro x hx hx1 y hy hy1
    have hx' : n⁻¹ * x * n ∈ D.Z := by
      have := D.Z_norm ((M₁ ⊓ M₂).inv_mem hn) hx
      simpa using this
    have hy' : n⁻¹ * y * n ∈ D.Z := by
      have := D.Z_norm ((M₁ ⊓ M₂).inv_mem hn) hy
      simpa using this
    obtain ⟨b, hb, hbxy⟩ := D.trans _ hx' (conj_ne_one' hx1) _ hy' (conj_ne_one' hy1)
    refine ⟨n * b * n⁻¹, mul_mem_conjSub hb, ?_⟩
    calc n * b * n⁻¹ * x * (n * b * n⁻¹)⁻¹ = n * (b * (n⁻¹ * x * n) * b⁻¹) * n⁻¹ := by group
      _ = n * (n⁻¹ * y * n) * n⁻¹ := by rw [hbxy]
      _ = y := by group
  cent := D.cent
  cov₁ := D.cov₁
  cov₂ := D.cov₂
  nonsolv := D.nonsolv
  s₁_mem := M₁.mul_mem (M₁.mul_mem hn.1 D.s₁_mem) (M₁.inv_mem hn.1)
  s₁_not := by
    intro h
    apply D.s₁_not
    have := M₂.mul_mem (M₂.mul_mem (M₂.inv_mem hn.2) h) hn.2
    rwa [show n⁻¹ * (n * D.s₁ * n⁻¹) * n = D.s₁ by group] at this
  s₁_sq := by
    calc n * D.s₁ * n⁻¹ * (n * D.s₁ * n⁻¹) = n * (D.s₁ * D.s₁) * n⁻¹ := by group
      _ = 1 := by rw [D.s₁_sq]; group
  s₁_norm := by
    intro b hb
    rw [mem_conjSub] at hb ⊢
    have h := D.s₁_norm _ hb
    rwa [show n⁻¹ * (n * D.s₁ * n⁻¹ * b * (n * D.s₁ * n⁻¹)⁻¹) * n =
      D.s₁ * (n⁻¹ * b * n) * D.s₁⁻¹ by group]
  s₂_mem := M₂.mul_mem (M₂.mul_mem hn.2 D.s₂_mem) (M₂.inv_mem hn.2)
  s₂_not := by
    intro h
    apply D.s₂_not
    have := M₁.mul_mem (M₁.mul_mem (M₁.inv_mem hn.1) h) hn.1
    rwa [show n⁻¹ * (n * D.s₂ * n⁻¹) * n = D.s₂ by group] at this
  s₂_sq := by
    calc n * D.s₂ * n⁻¹ * (n * D.s₂ * n⁻¹) = n * (D.s₂ * D.s₂) * n⁻¹ := by group
      _ = 1 := by rw [D.s₂_sq]; group
  s₂_norm := by
    intro b hb
    rw [mem_conjSub] at hb ⊢
    have h := D.s₂_norm _ hb
    rwa [show n⁻¹ * (n * D.s₂ * n⁻¹ * b * (n * D.s₂ * n⁻¹)⁻¹) * n =
      D.s₂ * (n⁻¹ * b * n) * D.s₂⁻¹ by group]
  fix₁ := by
    intro m hm hNB'
    have hNB : NormedBy D.B (conjSub (n⁻¹ * m) D.Z) := by
      intro b hb x hx
      rw [burnsideF4d_Z4_mem_conjSub_inv_mul] at hx ⊢
      have := hNB' (n * b * n⁻¹) (mul_mem_conjSub hb) (n * x * n⁻¹) hx
      rwa [show n * b * n⁻¹ * (n * x * n⁻¹) * (n * b * n⁻¹)⁻¹ = n * (b * x * b⁻¹) * n⁻¹ by
        group] at this
    have hmn : conjSub m D.Z = conjSub n (conjSub (n⁻¹ * m) D.Z) := by
      rw [← conjSub_mul, mul_inv_cancel_left]
    have hnZ : conjSub n D.Z = D.Z := L3Datum.conjSub_Z_eq (D := D) hn
    rcases D.fix₁ (n⁻¹ * m) (M₁.mul_mem (M₁.inv_mem hn.1) hm) hNB with h | h
    · left
      rw [hmn, h, hnZ]
    · right
      have e : conjSub (n * D.s₁ * n⁻¹) D.Z = conjSub n (conjSub D.s₁ D.Z) := by
        rw [← conjSub_mul]
        conv_lhs => rw [← hnZ, ← conjSub_mul]
        rw [show n * D.s₁ * n⁻¹ * n = n * D.s₁ by group]
      show conjSub m D.Z = conjSub (n * D.s₁ * n⁻¹) D.Z
      rw [e, hmn, h]
  fix₂ := by
    intro m hm hNB'
    have hNB : NormedBy D.B (conjSub (n⁻¹ * m) D.Z) := by
      intro b hb x hx
      rw [burnsideF4d_Z4_mem_conjSub_inv_mul] at hx ⊢
      have := hNB' (n * b * n⁻¹) (mul_mem_conjSub hb) (n * x * n⁻¹) hx
      rwa [show n * b * n⁻¹ * (n * x * n⁻¹) * (n * b * n⁻¹)⁻¹ = n * (b * x * b⁻¹) * n⁻¹ by
        group] at this
    have hmn : conjSub m D.Z = conjSub n (conjSub (n⁻¹ * m) D.Z) := by
      rw [← conjSub_mul, mul_inv_cancel_left]
    have hnZ : conjSub n D.Z = D.Z := L3Datum.conjSub_Z_eq (D := D) hn
    rcases D.fix₂ (n⁻¹ * m) (M₂.mul_mem (M₂.inv_mem hn.2) hm) hNB with h | h
    · left
      rw [hmn, h, hnZ]
    · right
      have e : conjSub (n * D.s₂ * n⁻¹) D.Z = conjSub n (conjSub D.s₂ D.Z) := by
        rw [← conjSub_mul]
        conv_lhs => rw [← hnZ, ← conjSub_mul]
        rw [show n * D.s₂ * n⁻¹ * n = n * D.s₂ by group]
      show conjSub m D.Z = conjSub (n * D.s₂ * n⁻¹) D.Z
      rw [e, hmn, h]
  centS := by
    intro x hx hcomm
    have hx' : n⁻¹ * x * n ∈ D.S := by
      have := D.S_norm n⁻¹ ((M₁ ⊓ M₂).inv_mem hn) x hx
      simpa using this
    have h1 : n⁻¹ * x * n = 1 := by
      refine D.centS _ hx' (fun b hb => ?_)
      have := hcomm (n * b * n⁻¹) (mul_mem_conjSub hb)
      calc n⁻¹ * x * n * b = n⁻¹ * (x * (n * b * n⁻¹)) * n := by group
        _ = n⁻¹ * ((n * b * n⁻¹) * x) * n := by rw [this]
        _ = b * (n⁻¹ * x * n) := by group
    calc x = n * (n⁻¹ * x * n) * n⁻¹ := by group
      _ = 1 := by rw [h1]; group
  Z_big := D.Z_big
  rot := by
    obtain ⟨b₃, hb₃, hrot⟩ := D.rot
    refine ⟨n * b₃ * n⁻¹, mul_mem_conjSub hb₃, fun x hx => ?_⟩
    rw [mem_conjSub] at hx
    have e : n * D.s₁ * n⁻¹ * (n * D.s₂ * n⁻¹) = n * (D.s₁ * D.s₂) * n⁻¹ := by group
    rw [e, conj_pow]
    have := hrot _ hx
    generalize (D.s₁ * D.s₂) ^ 3 = r at this ⊢
    calc n * r * n⁻¹ * x * (n * r * n⁻¹)⁻¹ = n * (r * (n⁻¹ * x * n) * r⁻¹) * n⁻¹ := by group
      _ = n * (b₃ * (n⁻¹ * x * n) * b₃⁻¹) * n⁻¹ := by rw [this]
      _ = n * b₃ * n⁻¹ * x * (n * b₃ * n⁻¹)⁻¹ := by group

end ConjDatum

section ExistsConj

variable {M : Type} [Group M] [Finite M] {M₁ M₂ : Subgroup M}

theorem burnsideF4d_Z4_exists_conj (D : L3Datum M₁ M₂) (hG : D.Good) {B' : Subgroup M}
    (hB'H : B' ≤ M₁ ⊓ M₂) (hB'odd : Odd (Nat.card ↥B'))
    (hcard : ∃ k : ℕ, Nat.card ↥(M₁ ⊓ M₂) = 2 ^ k * Nat.card ↥B') :
    ∃ n ∈ D.S, B' = conjSub n D.B := by
  have hdisj : ∀ x ∈ D.S, x ∈ B' → x = 1 := fun x hx hxB =>
    eq_one_of_pgroup_of_odd D.S_pgroup hB'odd hx hxB
  have hcardH : Nat.card ↥(M₁ ⊓ M₂) = Nat.card ↥D.S * Nat.card ↥B' := by
    obtain ⟨k, hk⟩ := hcard
    obtain ⟨a, ha⟩ := D.S_pgroup.exists_card_eq
    have h1 : Nat.card ↥(M₁ ⊓ M₂) = Nat.card ↥D.S * Nat.card ↥D.B := D.card_H
    rw [ha] at h1 ⊢
    have h2 : 2 ^ a * Nat.card ↥D.B = 2 ^ k * Nat.card ↥B' := h1.symm.trans hk
    have hcB : Nat.Coprime (2 ^ k) (Nat.card ↥D.B) :=
      Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr D.B_odd)
    have hcB' : Nat.Coprime (2 ^ a) (Nat.card ↥B') :=
      Nat.Coprime.pow_left a (Nat.coprime_two_left.mpr hB'odd)
    have hka : k ≤ a :=
      (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)).mp
        (hcB.dvd_of_dvd_mul_right (Dvd.intro _ h2.symm))
    have hak : a ≤ k :=
      (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)).mp
        (hcB'.dvd_of_dvd_mul_right (Dvd.intro _ h2))
    have hkeq : k = a := le_antisymm hka hak
    subst hkeq
    rw [h1]
    exact h2
  have hodd : ¬ 2 ∣ D.S.relIndex (M₁ ⊓ M₂) := by
    intro h2
    apply D.S_index
    rw [← Subgroup.relIndex_mul_relIndex D.S (M₁ ⊓ M₂) M₁ D.S_le_H inf_le_left]
    exact h2.mul_right _
  obtain ⟨r, hr, hB'r⟩ := Lin2.exists_conj_of_complements D.S_le_H
    (L3Datum.normalizer_S_eq hG).ge D.S_pgroup hodd D.B_le hB'H
    ((Subgroup.eq_bot_iff_forall _).mpr fun x hx => D.B_inf_S hx.1 hx.2)
    ((Subgroup.eq_bot_iff_forall _).mpr fun x hx => hdisj x hx.1 hx.2)
    D.mul_SB (exists_mul_eq_of_card D.S_le_H hB'H hdisj hcardH)
  refine ⟨r⁻¹, D.S.inv_mem hr, ?_⟩
  ext y
  rw [hB'r, Lin2.mem_conjR, mem_conjSub, inv_inv]

end ExistsConj

section HallTransport

open CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion

variable {E : Type} [Group E] {M₁ M₂ : Subgroup E} {Y : Type} [Group Y] {M : Type} [Group M]

theorem burnsideF4d_Z4_imB_eq (β : Cpl M₁ M₂ Y) (ε : Y →* M) {K : Subgroup E}
    (hK : K ≤ M₁ ⊓ M₂) : imB β ε K = subImg (burnsideF4d_bOne β ε) K := by
  unfold imB subImg bM bmap burnsideF4d_bOne
  rw [← burnsideF4d_map_inclusion_subgroupOf K hK]
  exact (Subgroup.map_map (K.subgroupOf (M₁ ⊓ M₂)) ((epsG β ε).comp (f1 (c := β)))
    (RankTwoAmalgam.ofSubgroups M₁ M₂).α1).symm

theorem burnsideF4d_Z4_imB_hall (β : Cpl M₁ M₂ Y) (hβ : β.IsFaithful) (ε : Y →* M)
    (hε : Function.Injective (epsG β ε)) {Bbar : Subgroup E}
    (hB : IsHallTwoPrime Bbar (M₁ ⊓ M₂)) :
    imB β ε Bbar ≤ MiOne β ε ⊓ MiTwo β ε ∧ Odd (Nat.card ↥(imB β ε Bbar)) ∧
      ∃ k : ℕ, Nat.card ↥(MiOne β ε ⊓ MiTwo β ε) = 2 ^ k * Nat.card ↥(imB β ε Bbar) := by
  obtain ⟨hle, hodd, k, hk⟩ := hB
  have hb : Function.Injective (burnsideF4d_bOne β ε) := hε.comp (f1_injective β hβ)
  have e1 : imB β ε Bbar = subImg (burnsideF4d_bOne β ε) Bbar := burnsideF4d_Z4_imB_eq β ε hle
  have e2 := burnsideF4d_inter_eq β hβ ε hε
  have hBM : Bbar ≤ M₁ := hle.trans inf_le_left
  refine ⟨?_, ?_, k, ?_⟩
  · rw [e1, e2]
    exact subImg_mono _ hle
  · rw [e1, card_subImg _ hb hBM]
    exact hodd
  · rw [e1, e2, card_subImg _ hb hBM, card_subImg _ hb (inf_le_left : M₁ ⊓ M₂ ≤ M₁)]
    have := Subgroup.relIndex_mul_card Bbar (M₁ ⊓ M₂)
    rw [inf_of_le_left hle, hk] at this
    exact this.symm

end HallTransport

section Parts

open CFSG.Quasithin.H13.F431.L3.L3Datum

variable {M : Type} [Group M] [Finite M] {M₁ M₂ : Subgroup M}

theorem burnsideF4d_Z4_conjSub_eq_of_normedBy {B K : Subgroup M} (h : NormedBy B K) {b : M}
    (hb : b ∈ B) : conjSub b K = K := by
  refine le_antisymm (fun x hx => ?_) (fun x hx => ?_)
  · rw [mem_conjSub] at hx
    have := h b hb _ hx
    rwa [show b * (b⁻¹ * x * b) * b⁻¹ = x by group] at this
  · rw [mem_conjSub]
    have := h b⁻¹ (B.inv_mem hb) x hx
    rwa [inv_inv] at this

theorem burnsideF4d_Z4_pow_mul {B : Subgroup M} {ρ : M} (hρ : ρ ∈ Subgroup.normalizer (B : Set M))
    {c : M} (hc : c ∈ B) (n : ℕ) : ∃ c' ∈ B, (c * ρ) ^ n = c' * ρ ^ n := by
  induction n with
  | zero => exact ⟨1, B.one_mem, by simp⟩
  | succ n ih =>
    obtain ⟨c', hc', h⟩ := ih
    have hρn : ρ ^ n ∈ Subgroup.normalizer (B : Set M) := Subgroup.pow_mem _ hρ n
    refine ⟨c' * (ρ ^ n * c * (ρ ^ n)⁻¹),
      B.mul_mem hc' ((Subgroup.mem_normalizer_iff.mp hρn c).mp hc), ?_⟩
    rw [pow_succ, h, pow_succ]
    group

theorem burnsideF4d_Z4_parts_datum (D : L3Datum M₁ M₂) (hG : D.Good) {B' : Subgroup M}
    (hB' : D.B = B') {s₁ s₂ : M}
    (h1 : s₁ ∈ M₁) (h1N : s₁ ∈ Subgroup.normalizer (B' : Set M)) (h1H : s₁ ∉ M₁ ⊓ M₂)
    (h1sq : s₁ * s₁ = 1)
    (h2 : s₂ ∈ M₂) (h2N : s₂ ∈ Subgroup.normalizer (B' : Set M)) (h2H : s₂ ∉ M₁ ⊓ M₂)
    (h2sq : s₂ * s₂ = 1) :
    ((cj s₁ D.Z ∈ BInvMembers B' D.Z D.Q₁ ∧ ∀ W ∈ BInvMembers B' D.Z D.Q₁, W = cj s₁ D.Z) ∧
      (cj s₂ D.Z ∈ BInvMembers B' D.Z D.Q₂ ∧ ∀ W ∈ BInvMembers B' D.Z D.Q₂, W = cj s₂ D.Z)) ∧
    (∀ g ∈ Subgroup.normalizer (B' : Set M),
      (∃ b ∈ B', b * g ≠ 1 ∧ (b * g) * (b * g) = 1) ∨ D.S ⊓ cj g D.S = D.S ∨
        D.S ⊓ cj g D.S = cj s₁ D.Z ∨ D.S ⊓ cj g D.S = cj s₂ D.Z) ∧
    ((s₁ * s₂) ^ 3 ∈ B' ∧ s₁ * s₂ ∉ B') := by
  subst hB'
  have hW1 : s₁ ∈ D.Wn := h1N
  have hW2 : s₂ ∈ D.Wn := h2N
  have hne1 : conjSub s₁ D.Z ≠ D.Z := fun h => h1H (hG.conj_Z_eq_Z h)
  have hne2 : conjSub s₂ D.Z ≠ D.Z := fun h => h2H (hG.conj_Z_eq_Z h)
  have hB1 : NormedBy D.B (conjSub s₁ D.Z) := normedBy_conj normedBy_Z hW1
  have hB2 : NormedBy D.B (conjSub s₂ D.Z) := normedBy_conj normedBy_Z hW2
  have hle1 : conjSub s₁ D.Z ≤ D.Q₁ :=
    (conjSub_mono s₁ D.Z_le_Q₁).trans (conjSub_Q₁_eq h1).le
  have hle2 : conjSub s₂ D.Z ≤ D.Q₂ :=
    (conjSub_mono s₂ D.Z_le_Q₂).trans (conjSub_Q₂_eq h2).le
  have heq1 : conjSub s₁ D.Z = conjSub D.s₁ D.Z := by
    rcases hG.fixedZ_of_le_Q D.cov₁ D.fix₁ hle1 hB1 with h | h
    · exact absurd h hne1
    · exact h
  have heq2 : conjSub s₂ D.Z = conjSub D.s₂ D.Z := by
    rcases hG.fixedZ_of_le_Q D.cov₂ D.fix₂ hle2 hB2 with h | h
    · exact absurd h hne2
    · exact h
  refine ⟨⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, ?_, ?_⟩
  · exact ⟨⟨s₁, rfl⟩, hle1, hne1, fun b hb => burnsideF4d_Z4_conjSub_eq_of_normedBy hB1 hb⟩
  · rintro W ⟨⟨g, rfl⟩, hWQ, hWne, hWinv⟩
    have hWB : NormedBy D.B (conjSub g D.Z) := by
      intro b hb x hx
      have e : conjSub b (conjSub g D.Z) = conjSub g D.Z := hWinv b hb
      have := mul_mem_conjSub (g := b) hx
      rwa [e] at this
    rcases hG.fixedZ_of_le_Q D.cov₁ D.fix₁ hWQ hWB with h | h
    · exact absurd h hWne
    · exact h.trans heq1.symm
  · exact ⟨⟨s₂, rfl⟩, hle2, hne2, fun b hb => burnsideF4d_Z4_conjSub_eq_of_normedBy hB2 hb⟩
  · rintro W ⟨⟨g, rfl⟩, hWQ, hWne, hWinv⟩
    have hWB : NormedBy D.B (conjSub g D.Z) := by
      intro b hb x hx
      have e : conjSub b (conjSub g D.Z) = conjSub g D.Z := hWinv b hb
      have := mul_mem_conjSub (g := b) hx
      rwa [e] at this
    rcases hG.fixedZ_of_le_Q D.cov₂ D.fix₂ hWQ hWB with h | h
    · exact absurd h hWne
    · exact h.trans heq2.symm
  · intro g hgW
    by_cases hgH : g ∈ M₁ ⊓ M₂
    · right
      left
      have hgS : g ∈ Subgroup.normalizer (D.S : Set M) := (normalizer_S_eq hG).ge hgH
      have e : conjSub g D.S = D.S := conjSub_eq_of_mem_normalizer hgS
      show D.S ⊓ conjSub g D.S = D.S
      rw [e, inf_idem]
    · have hinv : ∀ w : M, w * w = 1 → w * g⁻¹ ∈ D.B →
          ∃ b ∈ D.B, b * g ≠ 1 ∧ (b * g) * (b * g) = 1 := by
        intro w hww hwB
        refine ⟨w * g⁻¹, hwB, ?_, ?_⟩
        · rw [show w * g⁻¹ * g = w by group]
          intro hw1
          rw [hw1] at hwB
          apply hgH
          have := D.B_le (D.B.inv_mem hwB)
          simpa using this
        · rw [show w * g⁻¹ * g = w by group]
          exact hww
      rcases hG.trichotomy hgH with hbot | ⟨Q, hQ, hSP, hQc⟩ | ⟨a, hSP, hne1', -⟩
      · obtain ⟨w, hww, hwB⟩ := hG.caseT1 hgW hbot
        exact Or.inl (hinv w hww hwB)
      · obtain ⟨w, hww, hwB⟩ := hG.caseT2 hgW hgH hQ hSP hQc
        exact Or.inl (hinv w hww hwB)
      · right
        right
        rcases hG.caseT3 hgW hSP hne1' with h | h
        · exact Or.inl (h.trans heq1.symm)
        · exact Or.inr (h.trans heq2.symm)
  · have hb1 : s₁ * D.s₁⁻¹ ∈ D.B := hG.inv_coset s₁_W hW1 heq1.symm
    have hb2 : s₂ * D.s₂⁻¹ ∈ D.B := hG.inv_coset s₂_W hW2 heq2.symm
    have hr : D.s₁ * D.s₂ ∈ D.Wn := r_W
    have hc : s₁ * D.s₁⁻¹ * (D.s₁ * (s₂ * D.s₂⁻¹) * D.s₁⁻¹) ∈ D.B :=
      D.B.mul_mem hb1 (D.s₁_norm _ hb2)
    obtain ⟨c', hc', hpow⟩ := burnsideF4d_Z4_pow_mul hr hc 3
    have hrs : s₁ * s₂ =
        s₁ * D.s₁⁻¹ * (D.s₁ * (s₂ * D.s₂⁻¹) * D.s₁⁻¹) * (D.s₁ * D.s₂) := by group
    refine ⟨?_, ?_⟩
    · rw [hrs, hpow]
      exact D.B.mul_mem hc' hG.r_cube_mem_B
    · intro hmem
      apply h1H
      have hH : s₁ * s₂ ∈ M₁ ⊓ M₂ := D.B_le hmem
      refine ⟨h1, ?_⟩
      have := M₂.mul_mem hH.2 h2
      rwa [show s₁ * s₂ * s₂ = s₁ by rw [mul_assoc, h2sq, mul_one]] at this

end Parts

section Main

open CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion

theorem burnsideF4d_Z4_datum {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E} {Y : Type}
    [Group Y] {β : Cpl M₁ M₂ Y} {M : Type} [Group M] {ε : Y →* M} {z : M}
    (hyp : HypF_4_31 .L3 f Gp M₁ M₂ β ε z) {Bbar : Subgroup E}
    (hB : IsHallTwoPrime Bbar (M₁ ⊓ M₂)) :
    ∃ D : L3Datum (MiOne β ε) (MiTwo β ε), D.Good ∧ D.B = imB β ε Bbar ∧
      D.S = SinM Gp β ε ∧ D.Q₁ = pCoreOf 2 (oPPrime 2 (GiOne Gp β ε)) ∧
      D.Q₂ = pCoreOf 2 (oPPrime 2 (GiTwo Gp β ε)) := by
  haveI := hyp.finite_M
  obtain ⟨D, hG, -, hDS, hQ₁, hQ₂⟩ := burnsideF4d_L3_setup (burnsideF4d_L3_two_le_f hyp) hyp
  obtain ⟨hBH, hBodd, hBcard⟩ := burnsideF4d_Z4_imB_hall β hyp.faithful ε hyp.inj hB
  obtain ⟨n, hn, hBn⟩ := burnsideF4d_Z4_exists_conj D hG hBH hBodd hBcard
  exact ⟨burnsideF4d_Z4_conjDatum D (D.S_le_H hn), ⟨hG.cent, hG.ex⟩, hBn.symm, hDS, hQ₁, hQ₂⟩

theorem burnsideF4d_Z4_parts {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E} {Y : Type}
    [Group Y] {β : Cpl M₁ M₂ Y} {M : Type} [Group M] {ε : Y →* M} {z : M}
    (hyp : HypF_4_31 .L3 f Gp M₁ M₂ β ε z) (T : Subgroup M)
    (hT : IsSylowOf 2 T (MiOne β ε ⊓ MiTwo β ε)) (Bbar : Subgroup E)
    (hB : IsHallTwoPrime Bbar (M₁ ⊓ M₂)) (s₁ s₂ : M)
    (h1 : s₁ ∈ MiOne β ε)
    (h2 : s₁ ∈ Subgroup.normalizer ((imB β ε Bbar : Subgroup M) : Set M))
    (h3 : s₁ ∉ MiOne β ε ⊓ MiTwo β ε) (h4 : s₁ * s₁ = 1)
    (h5 : s₂ ∈ MiTwo β ε)
    (h6 : s₂ ∈ Subgroup.normalizer ((imB β ε Bbar : Subgroup M) : Set M))
    (h7 : s₂ ∉ MiOne β ε ⊓ MiTwo β ε) (h8 : s₂ * s₂ = 1) :
    ((cj s₁ (ctr T) ∈ BInvMembers (imB β ε Bbar) (ctr T) (pCoreOf 2 (oPPrime 2 (GiOne Gp β ε))) ∧
        ∀ W ∈ BInvMembers (imB β ε Bbar) (ctr T) (pCoreOf 2 (oPPrime 2 (GiOne Gp β ε))),
          W = cj s₁ (ctr T)) ∧
      (cj s₂ (ctr T) ∈ BInvMembers (imB β ε Bbar) (ctr T) (pCoreOf 2 (oPPrime 2 (GiTwo Gp β ε))) ∧
        ∀ W ∈ BInvMembers (imB β ε Bbar) (ctr T) (pCoreOf 2 (oPPrime 2 (GiTwo Gp β ε))),
          W = cj s₂ (ctr T))) ∧
    (∀ g ∈ Subgroup.normalizer ((imB β ε Bbar : Subgroup M) : Set M),
      (∃ b ∈ imB β ε Bbar, b * g ≠ 1 ∧ (b * g) * (b * g) = 1) ∨ T ⊓ cj g T = T ∨
        T ⊓ cj g T = cj s₁ (ctr T) ∨ T ⊓ cj g T = cj s₂ (ctr T)) ∧
    ((s₁ * s₂) ^ 3 ∈ imB β ε Bbar ∧ s₁ * s₂ ∉ imB β ε Bbar) := by
  haveI := hyp.finite_M
  obtain ⟨D, hG, hDB, hDS, hQ₁, hQ₂⟩ := burnsideF4d_Z4_datum hyp hB
  have hTS : T = D.S := burnsideF4d_sylow_eq_S D hT
  rw [← hQ₁, ← hQ₂, hTS]
  exact burnsideF4d_Z4_parts_datum D hG hDB h1 h2 h3 h4 h5 h6 h7 h8

theorem burnsideF4d_Z4_exists {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E} {Y : Type}
    [Group Y] {β : Cpl M₁ M₂ Y} {M : Type} [Group M] {ε : Y →* M} {z : M}
    (hyp : HypF_4_31 .L3 f Gp M₁ M₂ β ε z) (Bbar : Subgroup E)
    (hB : IsHallTwoPrime Bbar (M₁ ⊓ M₂)) :
    ∃ s₁ s₂ : M,
      s₁ ∈ MiOne β ε ∧ s₁ ∈ Subgroup.normalizer ((imB β ε Bbar : Subgroup M) : Set M) ∧
      s₁ ∉ MiOne β ε ⊓ MiTwo β ε ∧ s₁ * s₁ = 1 ∧
      s₂ ∈ MiTwo β ε ∧ s₂ ∈ Subgroup.normalizer ((imB β ε Bbar : Subgroup M) : Set M) ∧
      s₂ ∉ MiOne β ε ⊓ MiTwo β ε ∧ s₂ * s₂ = 1 := by
  haveI := hyp.finite_M
  obtain ⟨D, -, hDB, -, -, -⟩ := burnsideF4d_Z4_datum hyp hB
  refine ⟨D.s₁, D.s₂, D.s₁_mem, ?_, fun h => D.s₁_not h.2, D.s₁_sq, D.s₂_mem, ?_,
    fun h => D.s₂_not h.1, D.s₂_sq⟩
  · rw [← hDB]
    exact L3Datum.s₁_W
  · rw [← hDB]
    exact L3Datum.s₂_W

@[expose] def burnsideF4d_Z4_apartment : Prop :=
  ∀ (f : ℕ) (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E) (Y : Type) [Group Y]
    (β : Cpl M₁ M₂ Y) (M : Type) [Group M] (ε : Y →* M) (z : M),
    HypF_4_31 .L3 f Gp M₁ M₂ β ε z → ¬ IsL43 M →
    ∀ T : Subgroup M, IsSylowOf 2 T (MiOne β ε ⊓ MiTwo β ε) →
    ∀ Bbar : Subgroup E, IsHallTwoPrime Bbar (M₁ ⊓ M₂) →
    ∀ s₁ s₂ : M,
      s₁ ∈ MiOne β ε → s₁ ∈ Subgroup.normalizer ((imB β ε Bbar : Subgroup M) : Set M) →
      s₁ ∉ MiOne β ε ⊓ MiTwo β ε → s₁ * s₁ = 1 →
      s₂ ∈ MiTwo β ε → s₂ ∈ Subgroup.normalizer ((imB β ε Bbar : Subgroup M) : Set M) →
      s₂ ∉ MiOne β ε ⊓ MiTwo β ε → s₂ * s₂ = 1 →
      β.IsApartment GLKind.L3.m {u : β.Γ | ∃ w : β.G0,
        epsG β ε w ∈ Subgroup.closure {s₁, s₂} ⊔ imB β ε Bbar ∧ (u = w • β.xv ∨ u = w • β.lv)}

theorem burnsideF4d_Z4_conditional (h4 : burnsideF4d_Z4_apartment) : F_4_49_conditional := by
  intro κ f E _ Gp M₁ M₂ Y _ β M _ ε z hyp hL43 hκ T hT Bbar hB s₁ s₂ h1 h2 h3 h4' h5 h6 h7 h8
  subst hκ
  obtain ⟨⟨a, b⟩, c, d⟩ := burnsideF4d_Z4_parts hyp T hT Bbar hB s₁ s₂ h1 h2 h3 h4' h5 h6 h7 h8
  exact ⟨a, b, c, d, h4 f E Gp M₁ M₂ Y β M ε z hyp hL43 T hT Bbar hB s₁ s₂ h1 h2 h3 h4' h5 h6 h7 h8⟩

theorem burnsideF4d_Z4_F_4_49 (h4 : burnsideF4d_Z4_apartment) : F_4_49 := by
  refine ⟨burnsideF4d_Z4_conditional h4, ?_⟩
  intro κ f E _ Gp M₁ M₂ Y _ β M _ ε z hyp _ hκ Bbar hB
  subst hκ
  exact burnsideF4d_Z4_exists hyp Bbar hB

end Main

end F4dPartZ4

section F4dPartZ5

section Z5

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431
  CFSG.Quasithin.H13.F431.U42.Am CFSG.Quasithin.RankTwoAmalgam
  CFSG.Quasithin.RankTwoAmalgam.Completion CFSG.ASVolI.ChF

variable {E : Type} [Group E] {M₁ M₂ : Subgroup E} {Y : Type} [Group Y] {M : Type} [Group M]

theorem burnsideF4d_Z5_uniqueGeod_congr {G : Type} [Group G] {A B A' B' : Subgroup G}
    (hA : A = A') (hB : B = B') {m : ℕ}
    (h : UniqueGeod (CosetGeom.graph (A' ⊔ B') A' B') m) :
    UniqueGeod (CosetGeom.graph (A ⊔ B) A B) m := by
  subst hA hB
  exact h

theorem burnsideF4d_Z5_uniqueGeod {f : ℕ} {Gp : Subgroup E} {β : Cpl M₁ M₂ Y} {ε : Y →* M}
    {z : M} (hyp : HypF_4_31 .L3 f Gp M₁ M₂ β ε z) : UniqueGeod β.graph 3 := by
  haveI := hyp.amalgam.finite
  haveI := hyp.finite_M
  have hyp4 := hyp.amalgam.toHypF_4_4g
  haveI := hyp4.normal
  obtain ⟨TD, hyam⟩ := burnsideF4d_Y1_yam hyp4
  have hmodel := burnsideF4d_Y1_lieModel hyp4
  let X := burnsideF4d_lieExtE hyp4 hyam
  have hS := f431Facts45_psl f (f431ModelFacts_psl3 f) ↥Gp hmodel X.toLieAmalgamExt
  haveI : Finite β.G0 := Finite.of_injective _ hyp.inj
  haveI : Finite Y := Finite.of_injective
    (fun y : Y => (⟨y, by rw [β.gen]; exact Subgroup.mem_top y⟩ : β.G0))
    (fun a b h => congrArg Subtype.val h)
  let β' : (RankTwoAmalgam.ofSubgroups X.N1 X.N2).Completion Y := precompIso (isoSymm X.iso) β
  have hβ' : β'.IsFaithful := precompIso_isFaithful _ hyp.faithful
  have F := hS.facts46 β' hβ'
  have hU : UniqueGeod β'.graph 3 := F.uniqueGeod
  have e1 : β'.φ1.range = β.φ1.range := range_comp_mulEquiv _ _
  have e2 : β'.φ2.range = β.φ2.range := range_comp_mulEquiv _ _
  exact burnsideF4d_Z5_uniqueGeod_congr e1.symm e2.symm hU

theorem burnsideF4d_Z5_mem_MiOne_iff (β : Cpl M₁ M₂ Y) {ε : Y →* M}
    (hinj : Function.Injective (epsG β ε)) (x : β.G0) :
    epsG β ε x ∈ MiOne β ε ↔ (x : Y) ∈ β.φ1.range := by
  constructor
  · intro h
    obtain ⟨_, ⟨a, rfl⟩, hx⟩ := Subgroup.mem_map.mp h
    have : f1 (c := β) a = x := hinj hx
    exact ⟨a, by rw [← this]; rfl⟩
  · rintro ⟨a, ha⟩
    exact Subgroup.mem_map.mpr ⟨f1 (c := β) a, ⟨a, rfl⟩, by congr 1; exact Subtype.ext ha⟩

theorem burnsideF4d_Z5_mem_MiTwo_iff (β : Cpl M₁ M₂ Y) {ε : Y →* M}
    (hinj : Function.Injective (epsG β ε)) (x : β.G0) :
    epsG β ε x ∈ MiTwo β ε ↔ (x : Y) ∈ β.φ2.range := by
  constructor
  · intro h
    obtain ⟨_, ⟨a, rfl⟩, hx⟩ := Subgroup.mem_map.mp h
    have : f2 (c := β) a = x := hinj hx
    exact ⟨a, by rw [← this]; rfl⟩
  · rintro ⟨a, ha⟩
    exact Subgroup.mem_map.mpr ⟨f2 (c := β) a, ⟨a, rfl⟩, by congr 1; exact Subtype.ext ha⟩

theorem burnsideF4d_Z5_bmap_smul_xv (β : Cpl M₁ M₂ Y) (c : ↥(M₁ ⊓ M₂)) :
    bmap β c • β.xv = β.xv :=
  f1_smul_xv _

theorem burnsideF4d_Z5_bmap_smul_lv (β : Cpl M₁ M₂ Y) (c : ↥(M₁ ⊓ M₂)) :
    bmap β c • β.lv = β.lv := by
  have h : bmap β c = f2 (c := β) ((RankTwoAmalgam.ofSubgroups M₁ M₂).α2 c) :=
    Subtype.ext ((β.comm1 c).trans (β.comm2 c).symm)
  rw [h]
  exact f2_smul_lv _

theorem burnsideF4d_Z5_imB_le (β : Cpl M₁ M₂ Y) (ε : Y →* M) (K : Subgroup E) :
    imB β ε K ≤ MiOne β ε ⊓ MiTwo β ε := by
  intro b hb
  obtain ⟨c, -, rfl⟩ := Subgroup.mem_map.mp hb
  refine ⟨Subgroup.mem_map.mpr ⟨f1 (c := β) ((RankTwoAmalgam.ofSubgroups M₁ M₂).α1 c),
    ⟨_, rfl⟩, rfl⟩, Subgroup.mem_map.mpr ⟨f2 (c := β) ((RankTwoAmalgam.ofSubgroups M₁ M₂).α2 c),
    ⟨_, rfl⟩, ?_⟩⟩
  show epsG β ε (f2 (c := β) ((RankTwoAmalgam.ofSubgroups M₁ M₂).α2 c)) =
    epsG β ε (bmap β c)
  congr 1
  exact Subtype.ext ((β.comm2 c).trans (β.comm1 c).symm)

theorem burnsideF4d_Z5_imB_fix (β : Cpl M₁ M₂ Y) (ε : Y →* M) (K : Subgroup E) :
    ∀ b ∈ imB β ε K, ∃ g : β.G0, epsG β ε g = b ∧ g • β.xv = β.xv ∧ g • β.lv = β.lv := by
  intro b hb
  obtain ⟨c, -, rfl⟩ := Subgroup.mem_map.mp hb
  exact ⟨bmap β c, rfl, burnsideF4d_Z5_bmap_smul_xv β c, burnsideF4d_Z5_bmap_smul_lv β c⟩

theorem burnsideF4d_Z5_apartment_of_uniqueGeod {β : Cpl M₁ M₂ Y} {ε : Y →* M}
    (hinj : Function.Injective (epsG β ε)) (hU : UniqueGeod β.graph 3) {B : Subgroup M}
    (hB : ∀ b ∈ B, ∃ g : β.G0, epsG β ε g = b ∧ g • β.xv = β.xv ∧ g • β.lv = β.lv)
    {s₁ s₂ : M} (h₁ : s₁ ∈ MiOne β ε) (hn₁ : s₁ ∈ Subgroup.normalizer (B : Set M))
    (h₁' : s₁ ∉ MiOne β ε ⊓ MiTwo β ε) (hs₁ : s₁ * s₁ = 1)
    (h₂ : s₂ ∈ MiTwo β ε) (hn₂ : s₂ ∈ Subgroup.normalizer (B : Set M))
    (h₂' : s₂ ∉ MiOne β ε ⊓ MiTwo β ε) (hs₂ : s₂ * s₂ = 1)
    (hr : (s₁ * s₂) ^ 3 ∈ MiOne β ε ⊓ MiTwo β ε) :
    β.IsApartment 3 {u : β.Γ | ∃ w : β.G0,
      epsG β ε w ∈ Subgroup.closure {s₁, s₂} ⊔ B ∧ (u = w • β.xv ∨ u = w • β.lv)} := by
  obtain ⟨s₀, hs₀⟩ : ∃ s₀ : β.G0, epsG β ε s₀ = s₁ := by
    obtain ⟨x, -, hx⟩ := Subgroup.mem_map.mp h₁
    exact ⟨x, hx⟩
  obtain ⟨t₀, ht₀⟩ : ∃ t₀ : β.G0, epsG β ε t₀ = s₂ := by
    obtain ⟨x, -, hx⟩ := Subgroup.mem_map.mp h₂
    exact ⟨x, hx⟩
  have hs : s₀ * s₀ = 1 := hinj (by rw [map_mul, hs₀, hs₁, map_one])
  have ht : t₀ * t₀ = 1 := hinj (by rw [map_mul, ht₀, hs₂, map_one])
  have h1s : (s₀ : Y) ∈ β.φ1.range := by
    rw [← hs₀] at h₁
    exact (burnsideF4d_Z5_mem_MiOne_iff β hinj s₀).mp h₁
  have h2t : (t₀ : Y) ∈ β.φ2.range := by
    rw [← ht₀] at h₂
    exact (burnsideF4d_Z5_mem_MiTwo_iff β hinj t₀).mp h₂
  have hs12 : (s₀ : Y) ∉ β.φ1.range ⊓ β.φ2.range := by
    intro h
    apply h₁'
    refine ⟨h₁, ?_⟩
    rw [← hs₀]
    exact (burnsideF4d_Z5_mem_MiTwo_iff β hinj s₀).mpr h.2
  have ht12 : (t₀ : Y) ∉ β.φ1.range ⊓ β.φ2.range := by
    intro h
    apply h₂'
    refine ⟨?_, h₂⟩
    rw [← ht₀]
    exact (burnsideF4d_Z5_mem_MiOne_iff β hinj t₀).mpr h.1
  have hst : (((s₀ * t₀) ^ 3 : β.G0) : Y) ∈ β.φ1.range ⊓ β.φ2.range := by
    have e : epsG β ε ((s₀ * t₀) ^ 3) = (s₁ * s₂) ^ 3 := by
      rw [map_pow, map_mul, hs₀, ht₀]
    have hr1 := hr.1
    have hr2 := hr.2
    rw [← e] at hr1 hr2
    exact ⟨(burnsideF4d_Z5_mem_MiOne_iff β hinj _).mp hr1,
      (burnsideF4d_Z5_mem_MiTwo_iff β hinj _).mp hr2⟩
  have key := CosetGeom.lemma_F36 (G₁ := β.φ1.range) (G₂ := β.φ2.range) (m := 3) (by norm_num) hU
    hs ht h1s hs12 h2t ht12 (n := 3) (by norm_num) le_rfl hst
  have hcl : Subgroup.closure {s₁, s₂} = (Subgroup.closure {s₀, t₀}).map (epsG β ε) := by
    rw [MonoidHom.map_closure, Set.image_pair, hs₀, ht₀]
  have hle : Subgroup.closure {s₁, s₂} ≤ Subgroup.normalizer (B : Set M) := by
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | hx
    · exact hn₁
    · rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact hn₂
  have hmul := Subgroup.coe_mul_of_left_le_normalizer_right (Subgroup.closure {s₁, s₂}) B hle
  have hset : {u : β.Γ | ∃ w : β.G0, epsG β ε w ∈ Subgroup.closure {s₁, s₂} ⊔ B ∧
      (u = w • β.xv ∨ u = w • β.lv)} =
      MulAction.orbit (Subgroup.closure {s₀, t₀}) β.xv ∪
        MulAction.orbit (Subgroup.closure {s₀, t₀}) β.lv := by
    ext u
    constructor
    · rintro ⟨w, hw, hu⟩
      have hw' : epsG β ε w ∈ ((Subgroup.closure {s₁, s₂} ⊔ B : Subgroup M) : Set M) := hw
      rw [hmul] at hw'
      obtain ⟨c, hc, b, hb, hcb⟩ := hw'
      rw [hcl] at hc
      obtain ⟨h, hh, hhc⟩ := Subgroup.mem_map.mp hc
      obtain ⟨g, hg, hgx, hgl⟩ := hB b hb
      have hw_eq : w = h * g := hinj (by rw [map_mul, hhc, hg]; exact hcb.symm)
      rcases hu with rfl | rfl
      · left
        refine ⟨⟨h, hh⟩, ?_⟩
        show h • β.xv = w • β.xv
        rw [hw_eq, mul_smul, hgx]
      · right
        refine ⟨⟨h, hh⟩, ?_⟩
        show h • β.lv = w • β.lv
        rw [hw_eq, mul_smul, hgl]
    · rintro (⟨⟨h, hh⟩, rfl⟩ | ⟨⟨h, hh⟩, rfl⟩)
      · refine ⟨h, Subgroup.mem_sup_left ?_, Or.inl rfl⟩
        rw [hcl]
        exact ⟨h, hh, rfl⟩
      · refine ⟨h, Subgroup.mem_sup_left ?_, Or.inr rfl⟩
        rw [hcl]
        exact ⟨h, hh, rfl⟩
  rw [hset]
  exact key.2.1

theorem burnsideF4d_Z5_apartment {f : ℕ} {Gp : Subgroup E} {β : Cpl M₁ M₂ Y} {ε : Y →* M}
    {z : M} (hyp : HypF_4_31 .L3 f Gp M₁ M₂ β ε z) (K : Subgroup E)
    {s₁ s₂ : M} (h₁ : s₁ ∈ MiOne β ε) (hn₁ : s₁ ∈ Subgroup.normalizer ((imB β ε K : Subgroup M) : Set M))
    (h₁' : s₁ ∉ MiOne β ε ⊓ MiTwo β ε) (hs₁ : s₁ * s₁ = 1)
    (h₂ : s₂ ∈ MiTwo β ε) (hn₂ : s₂ ∈ Subgroup.normalizer ((imB β ε K : Subgroup M) : Set M))
    (h₂' : s₂ ∉ MiOne β ε ⊓ MiTwo β ε) (hs₂ : s₂ * s₂ = 1)
    (hr : (s₁ * s₂) ^ 3 ∈ imB β ε K) :
    β.IsApartment GLKind.L3.m {u : β.Γ | ∃ w : β.G0,
      epsG β ε w ∈ Subgroup.closure {s₁, s₂} ⊔ imB β ε K ∧ (u = w • β.xv ∨ u = w • β.lv)} :=
  burnsideF4d_Z5_apartment_of_uniqueGeod hyp.inj (burnsideF4d_Z5_uniqueGeod hyp)
    (burnsideF4d_Z5_imB_fix β ε K) h₁ hn₁ h₁' hs₁ h₂ hn₂ h₂' hs₂
    (burnsideF4d_Z5_imB_le β ε K hr)

end Z5

end F4dPartZ5

section F4dPartZ6

section Z6

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431
  CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion CFSG.ASVolI.ChF
  CFSG.Quasithin.H13.F431.L3

variable {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    {Y : Type} [Group Y] {β : Cpl M₁ M₂ Y} {M : Type} [Group M] {ε : Y →* M} {z : M}

theorem burnsideF4d_Z6_F_4_33_L3 (hyp : HypF_4_31 .L3 f Gp M₁ M₂ β ε z) {T : Subgroup M}
    (hT : IsSylowOf 2 T (MiOne β ε ⊓ MiTwo β ε)) : IsSylowOf 2 T ⊤ := by
  haveI := hyp.finite_M
  obtain ⟨D, hG, -, -, -, -⟩ := burnsideF4d_L3_setup (burnsideF4d_L3_two_le_f hyp) hyp
  have hT' : IsSylowTwoOf T (MiOne β ε ⊓ MiTwo β ε) := hT
  have hTS : T = D.S := burnsideF4d_sylow_eq_S D hT'
  rw [hTS]
  exact hG.sylow_top

theorem burnsideF4d_Z6_F_4_34_L3 (hyp : HypF_4_31 .L3 f Gp M₁ M₂ β ε z) :
    IsTISet (ctr (SinM Gp β ε)) ∧
      MiOne β ε ⊓ MiTwo β ε = Subgroup.normalizer ((ctr (SinM Gp β ε) : Subgroup M) : Set M) := by
  haveI := hyp.finite_M
  obtain ⟨D, hG, -, hDS, -, -⟩ := burnsideF4d_L3_setup (burnsideF4d_L3_two_le_f hyp) hyp
  rw [← hDS]
  have hctr : ctr D.S = D.Z := rfl
  rw [hctr]
  refine ⟨fun g => ?_, le_antisymm
    (fun h hh => mem_normalizer_of_conjSub_eq (L3Datum.conjSub_Z_eq hh))
    (fun n hn => hG.normalizer_Z (fun x hx => (Subgroup.mem_normalizer_iff.mp hn x).mp hx))⟩
  by_cases hbot : D.Z ⊓ cj g D.Z = ⊥
  · exact Or.inr hbot
  · left
    have hex : ∃ x ∈ D.Z ⊓ cj g D.Z, x ≠ 1 := by
      by_contra hcon
      push Not at hcon
      exact hbot ((Subgroup.eq_bot_iff_forall _).mpr hcon)
    obtain ⟨x, hx, hx1⟩ := hex
    have h1 : x ∈ conjSub 1 D.Z := by
      rw [conjSub_one]
      exact hx.1
    have h2 : conjSub 1 D.Z = conjSub g D.Z := hG.TI h1 hx.2 hx1
    exact (h2.symm.trans (conjSub_one _))

end Z6

end F4dPartZ6

section F4dPartZ7

section Z7

open CFSG.Open CFSG.ASVolI.ChF

theorem burnsideF4d_Z7_apartment : burnsideF4d_Z4_apartment := by
  intro f E _ Gp M₁ M₂ Y _ β M _ ε z hyp _ T hT Bbar hB s₁ s₂ h1 h2 h3 h4 h5 h6 h7 h8
  obtain ⟨-, -, hd, -⟩ := burnsideF4d_Z4_parts hyp T hT Bbar hB s₁ s₂ h1 h2 h3 h4 h5 h6 h7 h8
  exact burnsideF4d_Z5_apartment hyp Bbar h1 h2 h3 h4 h5 h6 h7 h8 hd

theorem as_F_4_49 : F_4_49 := by
  exact burnsideF4d_Z4_F_4_49 burnsideF4d_Z7_apartment

end Z7

end F4dPartZ7

end CFSG.ASVolI

