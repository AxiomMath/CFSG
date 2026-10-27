module

public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortP9U7
public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortP9U1PeelGrp
public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortP9U1Lift
import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortP9U1Bound
import CFSG.LocalAnalysis.StandardType.GGTwE6SCFourCover

public section

namespace CFSG.StandardType.FrameRoute

open Matrix CFSG.Assembly CFSG.Open CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.StandardType.LineU
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram)
open CFSG.LocalAnalysis.GLTheoremA.KD264Lie.RowXUn.Struct

variable {L : Type} [Group L] {F : Type} [Field F] {m : ℕ}

open scoped commutatorElement

private theorem p9u1t_isGoodIn_mono {G : Type*} [Group G] {Z Q Q₁ : Subgroup G}
    (hle : Q₁ ≤ Q) (hQ : IsGoodIn Z Q) : IsGoodIn Z Q₁ :=
  ⟨fun x hx y hy => hQ.1 x (hle hx) y (hle hy), fun x hx => hQ.2 x (hle hx)⟩

theorem exists_card_eq_three_pow_two_mul_card_center_of_isGoodIn {G : Type*} [Group G]
    [Finite G] {Z Q : Subgroup G} (hZ : ScalarLike Z) (hQ : IsGoodIn Z Q) :
    ∃ s : ℕ, Nat.card Q = 3 ^ (2 * s) * Nat.card (Subgroup.center ↥Q) := by
  classical
  have key : ∀ (n : ℕ) (Q : Subgroup G), Nat.card Q = n → IsGoodIn Z Q →
      ∃ s : ℕ, Nat.card Q = 3 ^ (2 * s) * Nat.card (Subgroup.center ↥Q) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro Q hn hQ
      by_cases hcent : Subgroup.center ↥Q = ⊤
      · refine ⟨0, ?_⟩; rw [hcent, Subgroup.card_top]; simp
      · obtain ⟨x, hx⟩ : ∃ x : ↥Q, x ∉ Subgroup.center ↥Q := by
          by_contra h
          exact hcent ((Subgroup.eq_top_iff' (Subgroup.center ↥Q)).2 fun x => by
            by_contra hx; exact h ⟨x, hx⟩)
        obtain ⟨y, hy⟩ : ∃ y : ↥Q, y * x ≠ x * y := by
          by_contra h
          exact hx (Subgroup.mem_center_iff.2 fun y => by
            by_contra hxy; exact h ⟨y, hxy⟩)
        set Q₁ : Subgroup G := Q ⊓ Subgroup.centralizer ({(y : G), (x : G)} : Set G) with hQ₁def
        have hg : (y : G) ∈ Q := y.2
        have hh : (x : G) ∈ Q := x.2
        have hgh : (y : G) * (x : G) ≠ (x : G) * (y : G) := fun h => hy (Subtype.ext h)
        have hQ₁ : IsGoodIn Z Q₁ :=
          p9u1t_isGoodIn_mono (by rw [hQ₁def]; exact inf_le_left) hQ
        have hcard : Nat.card Q = 9 * Nat.card Q₁ := by
          simpa [hQ₁def] using card_eq_nine_mul_card_inf_centralizer_pair hZ hQ hg hh hgh
        have hcenter : Nat.card (Subgroup.center ↥Q₁) = Nat.card (Subgroup.center ↥Q) := by
          simpa [hQ₁def] using card_center_inf_centralizer_pair hZ hQ hg hh hgh
        have hpos : 0 < Nat.card Q₁ := by
          haveI : Nonempty ↥Q₁ := ⟨1⟩
          exact Nat.card_pos
        have hlt : Nat.card Q₁ < Nat.card Q := by rw [hcard]; omega
        obtain ⟨s₁, hs₁⟩ := ih (Nat.card Q₁) (hn ▸ hlt) Q₁ rfl hQ₁
        refine ⟨s₁ + 1, ?_⟩
        rw [hcard, hs₁, ← hcenter,
          show 2 * (s₁ + 1) = 2 * s₁ + 2 by ring, pow_add]
        ring
  exact key (Nat.card Q) Q rfl hQ

private noncomputable def p9u1t_guAct (h : UnitaryFieldData 2 1 F) (m : ℕ) :
    ↥(primeFormUnitary h (idGram F m)) →* MulAut (LargeEvenProj (unitarySU 2 1 F m)) :=
  (TableB.projConj (unitarySU 2 1 F m)).comp
    (Subgroup.inclusion (fun _ hP => primeForm_mem_normalizer h hP))

private lemma p9u1t_guAct_apply (h : UnitaryFieldData 2 1 F) (m : ℕ)
    (X : ↥(primeFormUnitary h (idGram F m))) (s : ↥(unitarySU 2 1 F m)) :
    p9u1t_guAct h m X (LargeEvenProjMk (unitarySU 2 1 F m) s) =
      LargeEvenProjMk (unitarySU 2 1 F m)
        (conjN (X : GL (Fin m) F) (primeForm_mem_normalizer h X.2) s) := by
  rw [p9u1t_guAct, MonoidHom.comp_apply]
  have hincl : Subgroup.inclusion (fun _ hP => primeForm_mem_normalizer h hP) X =
      ⟨(X : GL (Fin m) F), primeForm_mem_normalizer h X.2⟩ := Subtype.ext rfl
  rw [hincl]
  exact projConj_mk_eq (X : GL (Fin m) F) (primeForm_mem_normalizer h X.2) s

private lemma p9u1t_guAct_scalar (h : UnitaryFieldData 2 1 F) (m : ℕ)
    {X : ↥(primeFormUnitary h (idGram F m))}
    (hX : X ∈ (LargeEvenScalars (Fin m) F).subgroupOf (primeFormUnitary h (idGram F m))) :
    p9u1t_guAct h m X = 1 := by
  rw [p9u1t_guAct, MonoidHom.comp_apply]
  have hX' : (X : GL (Fin m) F) ∈ LargeEvenScalars (Fin m) F :=
    Subgroup.mem_subgroupOf.1 hX
  have hnorm : Subgroup.inclusion (fun _ hP => primeForm_mem_normalizer h hP) X =
      ⟨(X : GL (Fin m) F), TableB.scalar_mem_normalizer (unitarySU 2 1 F m) hX'⟩ :=
    Subtype.ext rfl
  rw [hnorm]
  exact TableB.projConj_of_scalar (unitarySU 2 1 F m) hX'

private noncomputable def p9u1t_pguAct (h : UnitaryFieldData 2 1 F) (m : ℕ) :
    LargeEvenProj (primeFormUnitary h (idGram F m)) →*
      MulAut (LargeEvenProj (unitarySU 2 1 F m)) :=
  QuotientGroup.lift ((LargeEvenScalars (Fin m) F).subgroupOf (primeFormUnitary h (idGram F m)))
    (p9u1t_guAct h m) (fun _ hx => MonoidHom.mem_ker.2 (p9u1t_guAct_scalar h m hx))

private lemma p9u1t_pguAct_mk (h : UnitaryFieldData 2 1 F) (m : ℕ)
    (X : ↥(primeFormUnitary h (idGram F m))) :
    p9u1t_pguAct h m (LargeEvenProjMk (primeFormUnitary h (idGram F m)) X) =
      p9u1t_guAct h m X := by
  rw [p9u1t_pguAct]
  rfl

private lemma p9u1t_pguAct_injective (h : UnitaryFieldData 2 1 F) (hm : 3 ≤ m) :
    Function.Injective (p9u1t_pguAct h m) := by
  rw [injective_iff_map_eq_one]
  intro x
  refine QuotientGroup.induction_on x ?_
  intro X hx
  have hx' : p9u1t_guAct h m X = 1 := by
    rw [← p9u1t_pguAct_mk h m X]
    exact hx
  change (LargeEvenProjMk (primeFormUnitary h (idGram F m))) X = 1
  rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk', Subgroup.mem_subgroupOf]
  have hcomm : ∀ s : ↥(unitarySU 2 1 F m),
      ∃ c : F, (((X : GL (Fin m) F) * s * (X : GL (Fin m) F)⁻¹ * s⁻¹ :
        GL (Fin m) F) : Matrix (Fin m) (Fin m) F) = diagonal (fun _ => c) := by
    intro s
    have h1 : LargeEvenProjMk (unitarySU 2 1 F m)
        (conjN (X : GL (Fin m) F) (primeForm_mem_normalizer h X.2) s) =
        LargeEvenProjMk (unitarySU 2 1 F m) s := by
      rw [← p9u1t_guAct_apply h m X s, hx']
      rfl
    have h2 : conjN (X : GL (Fin m) F) (primeForm_mem_normalizer h X.2) s * s⁻¹ ∈
        (LargeEvenScalars (Fin m) F).subgroupOf (unitarySU 2 1 F m) := by
      have hker : (LargeEvenProjMk (unitarySU 2 1 F m))
          (conjN (X : GL (Fin m) F) (primeForm_mem_normalizer h X.2) s * s⁻¹) = 1 := by
        rw [map_mul, map_inv, h1, mul_inv_cancel]
      rwa [← MonoidHom.mem_ker, QuotientGroup.ker_mk'] at hker
    have h3 : ((conjN (X : GL (Fin m) F) (primeForm_mem_normalizer h X.2) s * s⁻¹ :
        ↥(unitarySU 2 1 F m)) : GL (Fin m) F) ∈ LargeEvenScalars (Fin m) F :=
      Subgroup.mem_subgroupOf.1 h2
    rw [largeEvenScalars_def, MonoidHom.mem_range] at h3
    obtain ⟨c, hc⟩ := h3
    refine ⟨(c : F), ?_⟩
    calc (((X : GL (Fin m) F) * s * (X : GL (Fin m) F)⁻¹ * s⁻¹ : GL (Fin m) F) :
          Matrix (Fin m) (Fin m) F)
        = ((conjN (X : GL (Fin m) F) (primeForm_mem_normalizer h X.2) s * s⁻¹ :
            ↥(unitarySU 2 1 F m)) : GL (Fin m) F) := by
          rw [Subgroup.coe_mul, Subgroup.coe_inv, coe_conjN]
      _ = ((Matrix.GeneralLinearGroup.scalar (Fin m) c : GL (Fin m) F) :
            Matrix (Fin m) (Fin m) F) := by rw [hc]
      _ = diagonal (fun _ => (c : F)) := by
          rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
  obtain ⟨c, hc⟩ := P9_U7a_eq_scalar_of_comm h hm (X : GL (Fin m) F)
    (fun s hs => hcomm ⟨s, hs⟩)
  rw [largeEvenScalars_def, ← Matrix.GeneralLinearGroup.center_eq_range_scalar]
  rw [Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar]
  exact ⟨c, by rw [Matrix.scalar_apply]; exact hc.symm⟩

private lemma p9u1t_mem_primeFormUnitary_of_mem_guSet (h : UnitaryFieldData 2 1 F) {m : ℕ}
    {X : GL (Fin m) F} (hX : X ∈ LargeEvenGUSet (Fin m) F (2 ^ 1)) :
    X ∈ primeFormUnitary h (idGram F m) := by
  obtain ⟨μ, hμ0, hμq, hXeq⟩ := hX
  have hμ : μ = 1 := by
    have h2 : μ ^ 2 = μ := by simpa using hμq
    have h : μ * μ = μ * 1 := by rw [mul_one, ← pow_two]; exact h2
    exact mul_left_cancel₀ hμ0 h
  have hmap : (X : Matrix (Fin m) (Fin m) F).map (· ^ 2 ^ 1) =
      (X : Matrix (Fin m) (Fin m) F).map h.bar := by
    have hfun : (fun c : F => c ^ 2 ^ 1) = h.bar := by
      funext c
      rw [h.bar_apply]
    rw [hfun]
  rw [mem_primeFormUnitary]
  simp only [idGram, Units.val_one, Matrix.mul_one, ← hmap]
  simpa [hμ] using hXeq

private lemma p9u1t_mem_range_pguAct (h : UnitaryFieldData 2 1 F) {m : ℕ}
    {φ : MulAut (LargeEvenProj (unitarySU 2 1 F m))}
    (hφ : φ ∈ LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 1 F m))
      (LargeEvenGUSet (Fin m) F (2 ^ 1))) :
    ∃ X : ↥(primeFormUnitary h (idGram F m)),
      φ = p9u1t_pguAct h m (LargeEvenProjMk (primeFormUnitary h (idGram F m)) X) := by
  obtain ⟨X, hXGU, hφX⟩ := TableB.exists_eq_projConj
    (TableBUE.gu_subset_normalizer (n := 1) (d := m) h) hφ
  have hXmem : X ∈ primeFormUnitary h (idGram F m) :=
    p9u1t_mem_primeFormUnitary_of_mem_guSet h hXGU
  refine ⟨⟨X, hXmem⟩, ?_⟩
  rw [p9u1t_pguAct_mk, p9u1t_guAct, MonoidHom.comp_apply, hφX]
  congr 1

private lemma p9u1t_exists_tau (h : UnitaryFieldData 2 1 F) (hm : 3 ≤ m)
    {L : Type} [Group L] {ψ : L →* LargeEvenProj (unitarySU 2 1 F m)}
    {A : Subgroup (MulAut L)}
    (hψ : Function.Surjective ψ)
    (hI : ∀ a ∈ A, ∃ φ ∈ LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 1 F m))
      (LargeEvenGUSet (Fin m) F (2 ^ 1)), ∀ l, φ (ψ l) = ψ (a l)) :
    ∀ a : ↥A, ∃ x : LargeEvenProj (primeFormUnitary h (idGram F m)),
      ∀ l : L, p9u1t_pguAct h m x (ψ l) = ψ ((a : MulAut L) l) := by
  intro a
  obtain ⟨φ, hφ, hφa⟩ := hI a a.2
  obtain ⟨X, hXφ⟩ := p9u1t_mem_range_pguAct h hφ
  refine ⟨LargeEvenProjMk (primeFormUnitary h (idGram F m)) X, ?_⟩
  intro l
  rw [← hXφ]
  exact hφa l

private noncomputable def p9u1t_tauFun (h : UnitaryFieldData 2 1 F) (hm : 3 ≤ m)
    {L : Type} [Group L] {ψ : L →* LargeEvenProj (unitarySU 2 1 F m)}
    {A : Subgroup (MulAut L)}
    (hψ : Function.Surjective ψ)
    (hI : ∀ a ∈ A, ∃ φ ∈ LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 1 F m))
      (LargeEvenGUSet (Fin m) F (2 ^ 1)), ∀ l, φ (ψ l) = ψ (a l))
    (a : ↥A) : LargeEvenProj (primeFormUnitary h (idGram F m)) :=
  Classical.choose (p9u1t_exists_tau h hm hψ hI a)

private lemma p9u1t_tauFun_spec (h : UnitaryFieldData 2 1 F) (hm : 3 ≤ m)
    {L : Type} [Group L] {ψ : L →* LargeEvenProj (unitarySU 2 1 F m)}
    {A : Subgroup (MulAut L)}
    (hψ : Function.Surjective ψ)
    (hI : ∀ a ∈ A, ∃ φ ∈ LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 1 F m))
      (LargeEvenGUSet (Fin m) F (2 ^ 1)), ∀ l, φ (ψ l) = ψ (a l))
    (a : ↥A) (l : L) :
    p9u1t_pguAct h m (p9u1t_tauFun h hm hψ hI a) (ψ l) = ψ ((a : MulAut L) l) :=
  Classical.choose_spec (p9u1t_exists_tau h hm hψ hI a) l

private lemma p9u1t_tau_unique (h : UnitaryFieldData 2 1 F) (hm : 3 ≤ m)
    {L : Type} [Group L] {ψ : L →* LargeEvenProj (unitarySU 2 1 F m)}
    {A : Subgroup (MulAut L)} (hψ : Function.Surjective ψ) {a : ↥A}
    {x₁ x₂ : LargeEvenProj (primeFormUnitary h (idGram F m))}
    (h₁ : ∀ l : L, p9u1t_pguAct h m x₁ (ψ l) = ψ ((a : MulAut L) l))
    (h₂ : ∀ l : L, p9u1t_pguAct h m x₂ (ψ l) = ψ ((a : MulAut L) l)) :
    x₁ = x₂ := by
  apply p9u1t_pguAct_injective h hm
  ext r
  obtain ⟨l, rfl⟩ := hψ r
  rw [h₁ l, h₂ l]

private noncomputable def p9u1t_tau (h : UnitaryFieldData 2 1 F) (hm : 3 ≤ m)
    {L : Type} [Group L] {ψ : L →* LargeEvenProj (unitarySU 2 1 F m)}
    {A : Subgroup (MulAut L)}
    (hψ : Function.Surjective ψ)
    (hI : ∀ a ∈ A, ∃ φ ∈ LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 1 F m))
      (LargeEvenGUSet (Fin m) F (2 ^ 1)), ∀ l, φ (ψ l) = ψ (a l)) :
    ↥A →* LargeEvenProj (primeFormUnitary h (idGram F m)) where
  toFun := p9u1t_tauFun h hm hψ hI
  map_one' := p9u1t_tau_unique h hm hψ (a := 1)
    (p9u1t_tauFun_spec h hm hψ hI 1)
    (by intro l; simp)
  map_mul' a b := p9u1t_tau_unique h hm hψ (a := a * b)
    (p9u1t_tauFun_spec h hm hψ hI (a * b))
    (by
      intro l
      calc p9u1t_pguAct h m (p9u1t_tauFun h hm hψ hI a * p9u1t_tauFun h hm hψ hI b)
            (ψ l)
          = p9u1t_pguAct h m (p9u1t_tauFun h hm hψ hI a)
              (p9u1t_pguAct h m (p9u1t_tauFun h hm hψ hI b) (ψ l)) := by
            rw [map_mul, MulAut.mul_apply]
        _ = p9u1t_pguAct h m (p9u1t_tauFun h hm hψ hI a) (ψ ((b : MulAut L) l)) := by
            rw [p9u1t_tauFun_spec h hm hψ hI b l]
        _ = ψ ((a : MulAut L) ((b : MulAut L) l)) :=
            p9u1t_tauFun_spec h hm hψ hI a ((b : MulAut L) l)
        _ = ψ (((a * b : ↥A) : MulAut L) l) := rfl)

private lemma p9u1t_tau_injective (h : UnitaryFieldData 2 1 F) (hm : 3 ≤ m)
    {L : Type} [Group L] {ψ : L →* LargeEvenProj (unitarySU 2 1 F m)}
    {A : Subgroup (MulAut L)}
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L)
    (hperf : commutator L = ⊤)
    (hI : ∀ a ∈ A, ∃ φ ∈ LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 1 F m))
      (LargeEvenGUSet (Fin m) F (2 ^ 1)), ∀ l, φ (ψ l) = ψ (a l)) :
    Function.Injective (p9u1t_tau h hm hψ hI) := by
  intro a b hab
  have hψeq : ∀ l : L, ψ ((a : MulAut L) l) = ψ ((b : MulAut L) l) := by
    intro l
    rw [← p9u1t_tauFun_spec h hm hψ hI a l,
      ← p9u1t_tauFun_spec h hm hψ hI b l]
    have h : p9u1t_tauFun h hm hψ hI a = p9u1t_tauFun h hm hψ hI b := hab
    rw [h]
  have hc : (a : MulAut L) * (b : MulAut L)⁻¹ = 1 := by
    refine (SCFourCover.induced_eq_one_iff hψ hker hperf
      (a := (a : MulAut L) * (b : MulAut L)⁻¹) (φ := 1) ?_).1 rfl
    intro l
    rw [MulAut.one_apply, MulAut.mul_apply]
    have h := hψeq ((b : MulAut L)⁻¹ l)
    simpa using h.symm
  exact Subtype.ext (by
    calc (a : MulAut L) = (a : MulAut L) * (b : MulAut L)⁻¹ * (b : MulAut L) := by group
      _ = 1 * (b : MulAut L) := by rw [hc]
      _ = (b : MulAut L) := one_mul _)

theorem P9_U1t_exists_pgu [Finite L] (h : UnitaryFieldData 2 1 F) (hm : 3 ≤ m) {r : ℕ}
    {ψ : L →* LargeEvenProj (unitarySU 2 1 F m)} {A : Subgroup (MulAut L)}
    (hTB : GGTorusTBGroup 3 r (LargeEvenProj (unitarySU 2 1 F m))
      (LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 1 F m))
        (LargeEvenGUSet (Fin m) F (2 ^ 1))) L ψ A) :
    ∃ A' : Subgroup (LargeEvenProj (primeFormUnitary h (idGram F m))),
      CFSG.Open.IsElemAbelian 3 A' ∧ Nat.card A' = Nat.card A := by
  obtain ⟨hψ, hker, hperf, hAelem, hI, -, -, -⟩ := hTB
  let τ := p9u1t_tau h hm hψ hI
  have hτinj : Function.Injective τ := p9u1t_tau_injective h hm hψ hker hperf hI
  refine ⟨τ.range, ?_, ?_⟩
  · refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
    · obtain ⟨a, ha⟩ := x.2
      obtain ⟨b, hb⟩ := y.2
      apply Subtype.ext
      change (↑x : LargeEvenProj (primeFormUnitary h (idGram F m))) * ↑y = ↑y * ↑x
      rw [← ha, ← hb, ← map_mul, ← map_mul, hAelem.1.is_comm.comm a b]
    · obtain ⟨a, rfl⟩ := hx
      rw [← map_pow, show a ^ 3 = 1 from Subtype.ext (hAelem.2 a a.2), map_one]
  · exact (Nat.card_congr (MonoidHom.ofInjective hτinj).toEquiv).symm

private lemma p9u1t_two_mul_add_one_le_three_pow (s : ℕ) : 2 * s + 1 ≤ 3 ^ s := by
  induction s with
  | zero => norm_num
  | succ s ih =>
    rw [pow_succ]
    have h2 : 3 * (2 * s + 1) ≤ 3 ^ s * 3 := by
      rw [mul_comm (3 ^ s) 3]
      exact Nat.mul_le_mul_left 3 ih
    have h1 : 2 * (s + 1) + 1 = 2 * s + 3 := by ring
    rw [h1]
    omega

private lemma p9u1t_arith {r s t : ℕ} (ht : 1 ≤ t) (hr : r ≤ 2 * s + t - 1) :
    r + 1 ≤ 3 ^ s * t := by
  have hs : 2 * s + 1 ≤ 3 ^ s := p9u1t_two_mul_add_one_le_three_pow s
  have h2 : 2 * s ≤ (3 ^ s - 1) * t := by
    calc 2 * s ≤ 3 ^ s - 1 := by omega
      _ ≤ (3 ^ s - 1) * t := Nat.le_mul_of_pos_right (3 ^ s - 1) (by omega)
  have h1 : 2 * s + t ≤ 3 ^ s * t := by
    calc 2 * s + t ≤ (3 ^ s - 1) * t + t := Nat.add_le_add_right h2 t
      _ = 3 ^ s * t := by
        conv_rhs => rw [← Nat.sub_add_cancel (by omega : 1 ≤ 3 ^ s)]
        rw [add_mul, one_mul]
  omega

private theorem p9u1t_finite_linearEquiv [Finite F] (m : ℕ) :
    Finite ((Fin m → F) ≃ₗ[F] (Fin m → F)) := by
  haveI : Fintype F := Fintype.ofFinite F
  haveI : Fintype (Fin m → F) := inferInstance
  exact Finite.of_injective (fun e : (Fin m → F) ≃ₗ[F] (Fin m → F) => e.toEquiv)
    (fun _ _ h => LinearEquiv.toEquiv_injective h)

theorem P9_U1t_succ_le [Finite L] [Finite F] (hF : Nat.card F = 4) (hm : 3 ≤ m) {r : ℕ}
    {ψ : L →* LargeEvenProj (unitarySU 2 1 F m)} {A : Subgroup (MulAut L)}
    (hTB : GGTorusTBGroup 3 r (LargeEvenProj (unitarySU 2 1 F m))
      (LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 1 F m))
        (LargeEvenGUSet (Fin m) F (2 ^ 1))) L ψ A)
    (hAr : Nat.card A = 3 ^ r) : r + 1 ≤ m := by
  classical
  have h : UnitaryFieldData 2 1 F :=
    ⟨Nat.prime_two, le_rfl, by rw [hF]; norm_num⟩
  obtain ⟨A', hA', hcardA'⟩ := P9_U1t_exists_pgu h hm hTB
  have hcardA'r : Nat.card A' = 3 ^ r := by rw [hcardA', hAr]
  obtain ⟨Q, hQ, -, hQcard⟩ :=
    exists_isGoodIn_mulEquiv_preimage h (by omega) (idGram F m) hA'
  have hQcard' : Nat.card Q = 3 ^ (r + 1) := by
    rw [hQcard, hcardA'r, pow_succ]
    ring
  haveI : Finite ((Fin m → F) ≃ₗ[F] (Fin m → F)) := p9u1t_finite_linearEquiv m
  obtain ⟨s, hs⟩ := exists_card_eq_three_pow_two_mul_card_center_of_isGoodIn
    (scalarLike_scalars hF) hQ
  obtain ⟨hdvd, hle⟩ :=
    three_pow_dvd_finrank_and_rank_le_of_isGoodIn hF hQ (a := r) hQcard' hs
  rw [Module.finrank_fin_fun] at hdvd hle
  have hmdiv : m = 3 ^ s * (m / 3 ^ s) := (Nat.mul_div_cancel' hdvd).symm
  have ht : 1 ≤ m / 3 ^ s := by
    by_contra h0
    have h0' : m / 3 ^ s = 0 := Nat.eq_zero_of_le_zero (by omega)
    rw [h0', mul_zero] at hmdiv
    omega
  calc r + 1 ≤ 3 ^ s * (m / 3 ^ s) := p9u1t_arith ht hle
    _ = m := hmdiv.symm

end CFSG.StandardType.FrameRoute

end
