module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarNoOffenderOmegaSUFrame
public import CFSG.LocalAnalysis.StandardType.GGSixBstarNoOffenderUOSU
public import CFSG.LocalAnalysis.StandardType.GGSUNonsplitTwoBlock

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank Matrix
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.LieType.Universal.Unitary (SU antidiag conjTr)
open CFSG.LieType.BorelTits (unitaryInvolution)
open CFSG.ClassicalGroups.UnitaryFlag (unitarySU mem_unitarySU_iff)

namespace NoOffOm

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Aut

open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (primeFormConjHom primeFormConjHom_mk
  primeFormUnitary primeFormFieldHom primeFormFieldAut primeFormFieldAut_mk primeFormPsi
  primeFormPsi_apply primeFormPsi_surjective glAut coe_glAut conj_mem_gramSU glAut_mem_gramSU)

variable {f : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2] (h : UnitaryFieldData 2 f K) {n : ℕ}
  {G : Type} [Group G]

include h in
theorem exists_semilinear_conj (hn : 4 ≤ n) {ψ : SU (unitaryInvolution K 2 f) n →* G}
    (hker : ψ.ker ≤ Subgroup.center (SU (unitaryInvolution K 2 f) n))
    (hC : Subgroup.centralizer (ψ.range : Set G) = ⊥) {g : G}
    (hg : g ∈ Subgroup.normalizer (ψ.range : Set G)) :
    ∃ (A : GL (Fin n) K) (θ : K ≃+* K), ∀ u : SU (unitaryInvolution K 2 f) n,
      ∃ u' : SU (unitaryInvolution K 2 f) n,
        (u' : GL (Fin n) K) = A * glAut θ (u : GL (Fin n) K) * A⁻¹ ∧ ψ u' = g⁻¹ * ψ u * g := by
  have hq : ¬(n = 3 ∧ 2 ^ f = 2) := fun h' => by omega
  obtain ⟨⟨A, θ⟩, hAθ⟩ := primeFormPsi_surjective h AutPSU.isPrimeFormGram_gramJ (by omega) hq
    (NoOffUO.inducedAut h hn hker hC
      ⟨g⁻¹, (Subgroup.normalizer (ψ.range : Set G)).inv_mem hg⟩)
  rw [primeFormPsi_apply] at hAθ
  refine ⟨A, θ, fun u => ?_⟩
  set w : AutPSU.XJ h n := ⟨(A : GL (Fin n) K) * glAut θ (AutPSU.suEquiv h u : GL (Fin n) K) *
      (A : GL (Fin n) K)⁻¹, conj_mem_gramSU h _ A.2
        (glAut_mem_gramSU h AutPSU.isPrimeFormGram_gramJ θ (AutPSU.suEquiv h u).2)⟩ with hw
  set u' := (AutPSU.suEquiv h).symm w with hu'
  have hu'w : AutPSU.suEquiv h u' = w := MulEquiv.apply_symm_apply _ w
  refine ⟨u', ?_, ?_⟩
  · have e := congrArg (fun z : AutPSU.XJ h n => (z : GL (Fin n) K)) hu'w
    simp only [AutPSU.coe_suEquiv] at e
    rw [e, hw]
    rfl
  · have hα : ((primeFormConjHom h _ A * primeFormFieldHom h AutPSU.isPrimeFormGram_gramJ θ :
        MulAut (AutPSU.PJ h n)) (AutPSU.projU h u)) = AutPSU.projU h u' := by
      rw [MulAut.mul_apply, AutPSU.projU_apply, AutPSU.projU_apply, hu'w]
      change primeFormConjHom h _ A (primeFormFieldAut h AutPSU.isPrimeFormGram_gramJ θ
        ((AutPSU.suEquiv h u : AutPSU.XJ h n) : AutPSU.PJ h n)) = _
      rw [primeFormFieldAut_mk, primeFormConjHom_mk]
      rfl
    have hspec := NoOffUO.inducedAut_spec h hn hker hC
      ⟨g⁻¹, (Subgroup.normalizer (ψ.range : Set G)).inv_mem hg⟩ (AutPSU.projU h u)
    rw [← hAθ, hα, AutPSU.projEquivU_projU, AutPSU.projEquivU_projU, inv_inv] at hspec
    exact hspec

variable [Fact (Nat.Prime 2)]

include h in
theorem exists_semilinear_conj_frame (hF : Nat.card K = (2 ^ f) ^ 2) (hn : 4 ≤ n)
    {ψ : SU (unitaryInvolution K 2 f) n →* G}
    (hker : ψ.ker ≤ Subgroup.center (SU (unitaryInvolution K 2 f) n))
    (hC : Subgroup.centralizer (ψ.range : Set G) = ⊥) (P₀ : GL (Fin n) K)
    (hP₀ : conjTr (unitaryInvolution K 2 f) (P₀ : Matrix (Fin n) (Fin n) K) *
      (P₀ : Matrix (Fin n) (Fin n) K) = antidiag n) {g : G}
    (hg : g ∈ Subgroup.normalizer (ψ.range : Set G)) :
    ∃ (A' : GL (Fin n) K) (θ : K ≃+* K), ∀ s : ↥(unitarySU 2 f K n),
      ∃ s' : ↥(unitarySU 2 f K n), (s' : GL (Fin n) K) = A' * glAut θ (s : GL (Fin n) K) * A'⁻¹ ∧
        SURep.ggFrameU hF ψ P₀ hP₀ s' = g⁻¹ * SURep.ggFrameU hF ψ P₀ hP₀ s * g := by
  obtain ⟨A, θ, hAθ⟩ := exists_semilinear_conj h hn hker hC hg
  refine ⟨P₀ * A * (glAut θ P₀)⁻¹, θ, fun s => ?_⟩
  set E := SURep.ggFrameEquiv hF P₀ hP₀ with hE
  obtain ⟨u', hu'c, hu'ψ⟩ := hAθ (E.symm s)
  refine ⟨E u', ?_, ?_⟩
  · have h1 : ((E.symm (E u') : SU (unitaryInvolution K 2 f) n) : GL (Fin n) K) =
        P₀⁻¹ * (E u' : GL (Fin n) K) * P₀ := SURep.coe_ggFrameEquiv_symm hF P₀ hP₀ _
    rw [MulEquiv.symm_apply_apply, hu'c, SURep.coe_ggFrameEquiv_symm hF P₀ hP₀ s] at h1
    have h2 : (E u' : GL (Fin n) K) = P₀ * ((A : GL (Fin n) K) *
        glAut θ (P₀⁻¹ * (s : GL (Fin n) K) * P₀) * A⁻¹) * P₀⁻¹ := by
      rw [h1]
      group
    rw [h2, map_mul, map_mul, map_inv]
    group
  · rw [SURep.ggFrameU_apply, SURep.ggFrameU_apply, MulEquiv.symm_apply_apply, hu'ψ]

end Aut

section Fix

open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut)

variable {f n : ℕ} {K : Type} [Field K]

theorem lin_eq_self_iff_of_conj {s s' : ↥(unitarySU 2 f K n)} {A' : GL (Fin n) K} {θ : K ≃+* K}
    (hs' : (s' : GL (Fin n) K) = A' * glAut θ (s : GL (Fin n) K) * A'⁻¹) (v : Fin n → K) :
    SUTB.lin s' v = v ↔
      SUTB.lin s (fun i => θ.symm ((((A'⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v) i)) =
        fun i => θ.symm ((((A'⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v) i) := by
  set w : Fin n → K := fun i => θ.symm ((((A'⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v) i)
    with hw
  have hθw : (fun i => θ (w i)) = ((A'⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v := by
    funext i
    simp [hw]
  have hAA : ((A' : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      ((A'⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hv : v = ((A' : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ (fun i => θ (w i)) := by
    rw [hθw, Matrix.mulVec_mulVec, hAA, Matrix.one_mulVec]
  have hlin : SUTB.lin s' v = ((A' : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
      (fun i => θ ((SUTB.mx s *ᵥ w) i)) := by
    rw [SUTB.lin_apply, SUTB.mx, hs', Units.val_mul, Units.val_mul, coe_glAut,
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← hθw]
    congr 1
    funext i
    exact (RingHom.map_mulVec (θ : K →+* K) _ _ i).symm
  have hinjA : Function.Injective fun x : Fin n → K =>
      ((A' : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ x := by
    intro x y hxy
    have h1 := congrArg (fun z => ((A'⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ z) hxy
    simp only [Matrix.mulVec_mulVec] at h1
    rwa [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec,
      Matrix.one_mulVec] at h1
  rw [hlin, SUTB.lin_apply]
  constructor
  · intro h1
    conv_rhs at h1 => rw [hv]
    have h2 := hinjA h1
    funext i
    exact θ.injective (congrFun h2 i)
  · intro h1
    conv_rhs => rw [hv]
    rw [h1]

end Fix

end NoOffOm

section Final

open CFSG.RankThree.PartTwo.Sec21 Multiplicative
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (primeFormUnitary mem_primeFormUnitary glAut
  coe_glAut)
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram)

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggSixBstarMonoFrameOn_PSUNonsplit : GGSixBstarMonoFrameOn GGPSUNonsplit := by
  intro G _ _ p B Bs x L D J t n f ψ hP hctx hC
  obtain ⟨rfl, hns⟩ := hP
  have hf1 : 1 ≤ f := hctx.2.2.2.1.1.2.1
  obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
  classical
  have hF : Nat.card (GaloisField 2 (2 * (f + 1))) = (2 ^ (f + 1)) ^ 2 :=
    card_galoisField_two_mul 2 (f + 1) (Nat.le_add_left 1 f)
  have h : UnitaryFieldData 2 (f + 1) (GaloisField 2 (2 * (f + 1))) :=
    ⟨Nat.prime_two, by omega, by rw [hF, ← pow_mul, mul_comm]⟩
  have hβ := hctx.1.2.2.2.2.2.1
  have hp : p.Prime := hβ.1
  have : Fact p.Prime := ⟨hp⟩
  have hrank : 2 ≤ n / 2 := hctx.2.2.2.1.2
  have hn4 : 4 ≤ n := by omega
  obtain ⟨hrange, hker⟩ := hctx.2.2.2.2.1
  have hnq : (n, 2 ^ (f + 1)) ≠ (3, 2) := fun h' => by
    have : n = 3 := congrArg Prod.fst h'
    omega
  obtain ⟨P₀, hP₀⟩ := CFSG.LieType.Universal.Unitary.exists_wittMatrix hF n
  set ψ₁ := SURep.ggFrameU hF ψ P₀ hP₀ with hψ₁
  have hr₁ : ψ₁.range = ψ.range := SURep.range_ggFrameU hF ψ P₀ hP₀
  have hker₁ : ψ₁.ker ≤ Subgroup.center ↥(unitarySU 2 (f + 1) (GaloisField 2 (2 * (f + 1))) n) :=
    SURep.ker_ggFrameU_le hF ψ P₀ hP₀ hker
  have hFk₁ : SURep.GGFrameKer ψ₁ := SURep.ggFrameKer_of_ker_le_center hF (by omega) hnq hker₁
  have hC₁ : Subgroup.centralizer (ψ₁.range : Set G) = ⊥ := by
    rw [hr₁, hrange]
    exact hC
  have hCψ : Subgroup.centralizer (ψ.range : Set G) = ⊥ := by
    rw [hrange]
    exact hC
  have hBsel : IsElemAbelian p Bs := hctx.2.1.2.1
  have hEB : ∀ b ∈ Bs, ∃ B', B' ∈ primeFormUnitary h (idGram (GaloisField 2 (2 * (f + 1))) n) ∧
      (b, B') ∈ SUTorus.suPairs ψ₁ := by
    intro b hb
    obtain ⟨A, hA, hAc⟩ := InnerDiagSU.suInnerDiagConj hF hn4 G ψ hker b⁻¹
      (hctx.2.2.2.2.2.2.1.2 b⁻¹ (Bs.inv_mem hb))
    refine ⟨P₀ * A * P₀⁻¹,
      SUTorus.mem_primeFormUnitary_of_isIdUnitary h (InnerDiagSU.isIdUnitary_conj hP₀ hA),
      SUTorus.mem_suPairs_transfer P₀ hP₀ (CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hF n)
        hA fun u => ?_⟩
    have := hAc u
    rwa [inv_inv] at this
  have hlift : ∀ b ∈ Bs, ∃ X : ↥(unitarySU 2 (f + 1) (GaloisField 2 (2 * (f + 1))) n),
      X ^ p = 1 ∧ ψ₁ X = b := fun b hb => by
    obtain ⟨B', hB'U, hB'⟩ := hEB b hb
    exact SUTB.exists_lift h (by omega) hnq hp hns hker₁ hC₁ (hBsel.2 b hb) hB'U hB'
  have hcomm : ∀ X Y : ↥(unitarySU 2 (f + 1) (GaloisField 2 (2 * (f + 1))) n), X ^ p = 1 →
      ψ₁ X ∈ Bs → ψ₁ Y ∈ Bs → X * Y = Y * X := fun X Y hXp hX hY =>
    SUNS.commute_of_frame_commute h hFk₁ hp hns hXp (TableB.IsElemAbelian.comm hBsel hX hY)
  let A : Subgroup ↥(unitarySU 2 (f + 1) (GaloisField 2 (2 * (f + 1))) n) :=
    { carrier := {X | X ^ p = 1 ∧ ψ₁ X ∈ Bs}
      mul_mem' := fun {X Y} hX hY => ⟨by
        rw [(show Commute X Y from hcomm X Y hX.1 hX.2 hY.2).mul_pow, hX.1, hY.1, one_mul], by
          rw [map_mul]; exact Bs.mul_mem hX.2 hY.2⟩
      one_mem' := ⟨one_pow p, by rw [map_one]; exact Bs.one_mem⟩
      inv_mem' := fun {X} hX => ⟨by rw [inv_pow, hX.1, inv_one], by
        rw [map_inv]; exact Bs.inv_mem hX.2⟩ }
  have hmemA : ∀ X, X ∈ A ↔ X ^ p = 1 ∧ ψ₁ X ∈ Bs := fun X => Iff.rfl
  have hA : SUTB.MaxElemAb p A :=
    { prime := hp
      ne_two := hβ.2.1
      not_dvd := hns
      pow := fun a ha => ((hmemA a).mp ha).1
      comm := fun a ha b hb => hcomm a b ((hmemA a).mp ha).1 ((hmemA a).mp ha).2
        ((hmemA b).mp hb).2
      max := fun g hgp hga => by
        refine (hmemA g).mpr ⟨hgp, hctx.2.1.2.2.2 (ψ₁ g) ?_ (by rw [← map_pow, hgp, map_one])⟩
        rw [Subgroup.mem_centralizer_iff]
        intro b hb
        obtain ⟨X, hXp, rfl⟩ := hlift b hb
        rw [← map_mul, ← map_mul, hga X ((hmemA X).mpr ⟨hXp, hb⟩)] }
  have huniq : ∀ X ∈ A, ∀ X' ∈ A, ψ₁ X = ψ₁ X' → X = X' := by
    intro X hX X' hX' hXX'
    have hz : ψ₁ (X⁻¹ * X') = 1 := by rw [map_mul, map_inv, hXX', inv_mul_cancel]
    obtain ⟨c, hc⟩ := hFk₁ _ hz
    have hzp : (X⁻¹ * X') ^ p = 1 := hA.pow _ (A.mul_mem (A.inv_mem hX) hX')
    exact inv_mul_eq_one.mp (SUNS.eq_one_of_scalar_mem h hp hns ⟨0, by omega⟩ hc hzp)
  obtain ⟨r, ι₀, hinj₀, hrange₀, hsupp₀⟩ := NoOffOm.exists_pieceFrame h hA
  have hι₀A : ∀ s, ι₀ s ∈ A := fun s => hrange₀ ▸ MonoidHom.mem_range.mpr ⟨s, rfl⟩
  have hinj : Function.Injective (ψ₁.comp ι₀) := fun s t hst =>
    hinj₀ (huniq _ (hι₀A s) _ (hι₀A t) hst)
  have hrangeι : (ψ₁.comp ι₀).range = Bs := by
    ext b
    constructor
    · rintro ⟨s, rfl⟩
      exact ((hmemA _).mp (hι₀A s)).2
    · intro hb
      obtain ⟨X, hXp, hXb⟩ := hlift b hb
      have hXA : X ∈ ι₀.range := by rw [hrange₀]; exact (hmemA X).mpr ⟨hXp, hXb ▸ hb⟩
      obtain ⟨s, hs⟩ := hXA
      exact ⟨s, by rw [MonoidHom.comp_apply, hs, hXb]⟩
  refine ⟨r, ψ₁.comp ι₀, hinj, hrangeι, fun g hgM hgB _ => ?_⟩
  have hgN : g ∈ Subgroup.normalizer (ψ.range : Set G) := by
    rw [hrange]
    exact hgM
  obtain ⟨A', θ, hAθ⟩ := NoOffOm.exists_semilinear_conj_frame h hF hn4 hker hCψ P₀ hP₀ hgN
  set R : G → G → Prop := fun b b' => ∀ X ∈ A, ∀ X' ∈ A, ψ₁ X = b → ψ₁ X' = b' →
    ∀ v, SUTB.lin X' v = v → SUTB.lin X v = v with hR
  have hRiff : ∀ X ∈ A, ∀ X' ∈ A,
      R (ψ₁ X) (ψ₁ X') ↔ ∀ v, SUTB.lin X' v = v → SUTB.lin X v = v := by
    intro X hX X' hX'
    constructor
    · intro hR' v hv
      exact hR' X hX X' hX' rfl rfl v hv
    · intro hfix Y hY Y' hY' hYX hY'X' v hv
      rw [huniq Y hY X hX hYX]
      rw [huniq Y' hY' X' hX' hY'X'] at hv
      exact hfix v hv
  have hRι : ∀ s s', R (ψ₁.comp ι₀ (ofAdd s)) (ψ₁.comp ι₀ (ofAdd s')) ↔ NoOffOm.SuppLE s s' :=
    fun s s' => (hRiff _ (hι₀A _) _ (hι₀A _)).trans (hsupp₀ s s')
  have htr : ∀ X ∈ A, ∃ Y ∈ A, ψ₁ Y = g⁻¹ * ψ₁ X * g ∧
      ((Y : GL (Fin n) (GaloisField 2 (2 * (f + 1)))) =
        A' * glAut θ (X : GL (Fin n) (GaloisField 2 (2 * (f + 1)))) * A'⁻¹) := by
    intro X hX
    obtain ⟨Y, hYc, hYψ⟩ := hAθ X
    refine ⟨Y, (hmemA Y).mpr ⟨?_, ?_⟩, hYψ, hYc⟩
    · apply Subtype.ext
      rw [SubgroupClass.coe_pow, hYc, conj_pow, ← map_pow, ← SubgroupClass.coe_pow,
        ((hmemA X).mp hX).1, OneMemClass.coe_one, map_one, mul_one, mul_inv_cancel]
    · rw [hYψ]
      exact NoOffOm.inv_mul_mul_mem hgB ((hmemA X).mp hX).2
  have hTsurj : ∀ w : Fin n → GaloisField 2 (2 * (f + 1)), ∃ v,
      (fun i => θ.symm ((((A'⁻¹ : GL (Fin n) (GaloisField 2 (2 * (f + 1)))) :
        Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (f + 1)))) *ᵥ v) i)) = w := by
    intro w
    refine ⟨((A' : GL (Fin n) (GaloisField 2 (2 * (f + 1)))) :
      Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (f + 1)))) *ᵥ fun i => θ (w i), ?_⟩
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
    funext i
    simp
  have hRg : ∀ s s', R (g⁻¹ * ψ₁.comp ι₀ (ofAdd s) * g) (g⁻¹ * ψ₁.comp ι₀ (ofAdd s') * g) ↔
      R (ψ₁.comp ι₀ (ofAdd s)) (ψ₁.comp ι₀ (ofAdd s')) := by
    intro s s'
    obtain ⟨Y, hYA, hYψ, hYc⟩ := htr _ (hι₀A (ofAdd s))
    obtain ⟨Y', hY'A, hY'ψ, hY'c⟩ := htr _ (hι₀A (ofAdd s'))
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, ← hYψ, ← hY'ψ, hRiff _ hYA _ hY'A,
      hRiff _ (hι₀A _) _ (hι₀A _)]
    constructor
    · intro himp w hw
      obtain ⟨v, rfl⟩ := hTsurj w
      exact (NoOffOm.lin_eq_self_iff_of_conj hYc v).mp
        (himp v ((NoOffOm.lin_eq_self_iff_of_conj hY'c v).mpr hw))
    · intro himp v hv
      exact (NoOffOm.lin_eq_self_iff_of_conj hYc v).mpr
        (himp _ ((NoOffOm.lin_eq_self_iff_of_conj hY'c v).mp hv))
  exact NoOffOm.monoAct_of_suppRel hinj (hrangeι ▸ hgB) R hRι hRg

theorem ggSixBstarNoOffenderOn_PSUNonsplit : GGSixBstarNoOffenderOn GGPSUNonsplit :=
  ggNoOffender_of_monoFrameOn ggSixBstarMonoFrameOn_PSUNonsplit

theorem ggSixBstarNoOffenderAt_PSU : GGSixBstarNoOffenderAt .PSU :=
  ggSixBstarNoOffenderAt_PSU_of_nonsplit ggSixBstarNoOffenderOn_PSUNonsplit

end Final

end CFSG.StandardType
