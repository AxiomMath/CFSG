module

public import CFSG.RankThree.PartOne.KE6.Phi6Embed
public import CFSG.RankThree.PartOne.KE6.Phi6Eps
public import CFSG.RankThree.PartOne.KE.E6TwThreeAbstract
public import CFSG.RankThree.PartOne.KE6.Phi6Abstract
public import CFSG.RankThree.PartOne.KE6.Phi6Actor
public import CFSG.RankThree.PartOne.KE6.Phi6Excl
public import CFSG.RankThree.PartOne.KE6.Phi6Layer
public import CFSG.RankThree.PartOne.KE6.Phi6Std

public noncomputable section

namespace CFSG.RankThree.PartOne.KE6

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.RankThree.E6 CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.Classical2 CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.RankThree.PartOne CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.RankThree.PartOne.KE (twistedTorus mem_twistedTorus adjEmb adjEmb_injective adjEmb_mem
  adjEmb_frobenius twistedFixedPoints mem_twistedFixedPoints)
open scoped Matrix MatrixGroups Pointwise commutatorElement

theorem torusGroup_comm {Ω : Type} [Field Ω] :
    ∀ a ∈ torusGroup Tag.E6 Ω, ∀ b ∈ torusGroup Tag.E6 Ω, a * b = b * a := by
  intro a ha b hb
  obtain ⟨a', rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ha
  obtain ⟨b', rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hb
  rw [← rootDiagUnit_mul, ← rootDiagUnit_mul, mul_comm]

theorem e6_six_core_odd (K : Type) [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime]
    [CharP K ℓ] (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpq : (p : ℤ) ∣ (Nat.card K : ℤ) ^ 2 - (Nat.card K : ℤ) + 1)
    (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ]
    {g0 : ModGL Tag.E6 L} (hg0C : g0 ∈ adjointGroup Tag.E6 L)
    (hg0 : Units.map (entrywiseHom (iterateFrobenius L ℓ f)) g0 = g0 * phi6N L)
    (hperf : ∀ P : Subgroup (ModGL Tag.E6 L), Finite P → P ≤ adjointGroup Tag.E6 L →
      (∀ x ∈ P, Units.map (entrywiseHom (iterateFrobenius L ℓ f)) x = x) → ⁅P, P⁆ = P →
        P ≤ (adjEmb Tag.E6 K L).range)
    {x : adjointGroup Tag.E6 K} (hxp : orderOf x = p)
    (hh : g0⁻¹ * adjEmb Tag.E6 K L x * g0 ∈
      twistedTorus (phi6N L) (iterateFrobenius L ℓ f))
    (hA2A2 : ∃ w : WeylGroup Tag.E6,
      (w • ·) '' torusRootKernel (g0⁻¹ * adjEmb Tag.E6 K L x * g0) =
        parabolicRoots Tag.E6 supportA2A2)
    {B : Subgroup (MulAut (adjointGroup Tag.E6 K))}
    (hB : (MulAut.conj : adjointGroup Tag.E6 K →* MulAut (adjointGroup Tag.E6 K)).range ≤ B) :
    Odd (Nat.card ↥(inSubgroup (aschbacherSolvableCore p) (B ⊓ Subgroup.centralizer
      ({(MulAut.conj x : MulAut (adjointGroup Tag.E6 K))} :
        Set (MulAut (adjointGroup Tag.E6 K)))))) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have : Fintype K := Fintype.ofFinite K
  have hℓ : ℓ.Prime := Fact.out
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  have hFr : ∀ c, Fr c = c ^ (ℓ ^ f) := fun c => iterateFrobenius_def ℓ f c
  have hFrK : ∀ c, Fr c = c ^ Nat.card K := fun c => by
    rw [hK]
    exact hFr c
  have hq0 : ((ℓ ^ f : ℕ) : L) = 0 := by
    rw [Nat.cast_pow, CharP.cast_eq_zero, zero_pow (by omega)]
  have hpq' : (p : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) ^ 2 - ((ℓ ^ f : ℕ) : ℤ) + 1 := by
    rw [hK] at hpq
    exact hpq
  obtain ⟨hpL, ⟨ζ, hζ⟩, hr⟩ := phi6_prime_setup hq0 hp hpq'
  have hp7 : 7 ≤ p := (e6Six_data hp hp3 hpq').2.2.2.2.1
  have hC : Subgroup.center (adjointGroup Tag.E6 K) = ⊥ := center_adjointGroup_eq_bot
  set ι : adjointGroup Tag.E6 K →* ModGL Tag.E6 L := adjEmb Tag.E6 K L with hιdef
  set y : ModGL Tag.E6 L := g0⁻¹ * ι x * g0 with hydef
  have hyH : y ∈ torusGroup Tag.E6 L := (mem_twistedTorus.1 hh).1
  have hordy : orderOf y = p := by
    have e1 : orderOf y = orderOf (ι x) := by
      have := orderOf_injective (MulAut.conj g0⁻¹).toMonoidHom (MulAut.conj g0⁻¹).injective (ι x)
      rw [hydef]
      simpa [MulAut.conj_apply] using this
    rw [e1, orderOf_injective ι adjEmb_injective x, hxp]
  have hyp : y ^ p = 1 := hordy ▸ pow_orderOf_eq_one y
  have hy1 : y ≠ 1 := fun h1 => by
    rw [h1, orderOf_one] at hordy
    exact hp.one_lt.ne hordy
  set D : Subgroup (adjointGroup Tag.E6 K) := Subgroup.centralizer ({x} :
    Set (adjointGroup Tag.E6 K)) with hD
  obtain ⟨ψ, hψinj, hψdef, hψHQ, hψfix, hPψ, hPq, hC6⟩ := phi6_embedding_A2A2 K hf hK hp hp3 hpq L
    hg0C hg0 hperf hxp hh hA2A2
  set P : Subgroup (ModGL Tag.E6 L) := phi6P L Fr (torusRootKernel y) with hPdef
  have hHN : torusGroup Tag.E6 L ≤
      Subgroup.normalizer (rootSpan Tag.E6 L (torusRootKernel y) : Set (ModGL Tag.E6 L)) :=
    CFSG.RankThree.Classical2.torusGroup_le_normalizer_rootSpan fun α hα => hα.1
  have hcomm := commutator_sup_le_of_comm (torusGroup_comm (Ω := L)) hHN
  have hψR : ψ.range ≤ torusGroup Tag.E6 L ⊔ rootSpan Tag.E6 L (torusRootKernel y) := by
    rintro _ ⟨d, rfl⟩
    exact hψHQ d
  have hc1 : ⁅ψ.range, ψ.range⁆ ≤ phi6Qθ L Fr (torusRootKernel y) := by
    refine le_inf ((Subgroup.commutator_mono hψR hψR).trans hcomm) ?_
    refine Subgroup.commutator_le.2 fun a ha b hb => ?_
    obtain ⟨da, rfl⟩ := ha
    obtain ⟨db, rfl⟩ := hb
    show phi6Theta L Fr ⁅ψ da, ψ db⁆ = ⁅ψ da, ψ db⁆
    have h1 : phi6Theta L Fr (ψ da) = ψ da := hψfix da
    have h2 : phi6Theta L Fr (ψ db) = ψ db := hψfix db
    rw [map_commutatorElement, h1, h2]
  have hD2 : ⁅⁅ψ.range, ψ.range⁆, ⁅ψ.range, ψ.range⁆⁆ ≤ P := Subgroup.commutator_mono hc1 hc1
  have hPperf : ⁅P, P⁆ = P := by
    exact Subgroup.isPerfect_iff.1 hPq.1
  have hmapD : (CFSG.perfectResidual D).map ψ = P :=
    perfectResidual_map_eq ψ hψinj P hPψ hPperf hD2
  have hDq : CFSG.IsQuasisimple ↥((CFSG.perfectResidual D).map D.subtype) :=
    isQuasisimple_perfectResidual D ψ hψinj P hPq hmapD
  set ψ0 : adjointGroup Tag.E6 K →* ModGL Tag.E6 L :=
    (MulAut.conj g0⁻¹).toMonoidHom.comp ι with hψ0def
  have hψ0 : ∀ d, ψ0 d = g0⁻¹ * ι d * g0 := fun d => by simp [ψ0]
  have hψ0inj : Function.Injective ψ0 := (MulAut.conj g0⁻¹).injective.comp adjEmb_injective
  obtain ⟨-, hTodd⟩ := natCard_phi6Torus (L := L) hFr hq0
  refine odd_card_of_conj ψ0 hψ0inj (twistedTorus (phi6N L) Fr) hTodd _ (fun η hη => ?_)
  obtain ⟨hηx, hηD⟩ := CFSG.RankThree.PartOne.KETw3.core_fixes_perfectResidual hp hC hB hDq hη
  obtain ⟨j, hj, ε, hε, g, a, hnf⟩ := phi6_normal_form_L hf hK L η
  obtain ⟨G₃, hG₃, hG₃eq, hψη⟩ := phi6_frame_transport (iterateFrobenius L ℓ j) hε hg0C g a η hnf
  obtain ⟨πε, hπc, hQd, hQG, hQroot, hπ0, hπ1⟩ := epsilon_data (Ω := L) hε
  have hςbij : Function.Bijective (iterateFrobenius L ℓ j) := bijective_iterateFrobenius L ℓ j
  have hFrbij : Function.Bijective Fr := bijective_iterateFrobenius L ℓ f
  have hp5 : 5 < p := by omega
  have hfixy : (G₃ * (diagQ L) ^ ε) * Units.map (entrywiseHom (iterateFrobenius L ℓ j)) y *
      (G₃ * (diagQ L) ^ ε)⁻¹ = y := by
    have h1 := hψη x
    rw [hηx] at h1
    exact h1.symm
  have hPfix : ∀ q ∈ P, (G₃ * (diagQ L) ^ ε) * Units.map (entrywiseHom (iterateFrobenius L ℓ j)) q *
      (G₃ * (diagQ L) ^ ε)⁻¹ = q := by
    intro q hq
    rw [← hmapD] at hq
    obtain ⟨d', hd', rfl⟩ := hq
    have hdD : (d' : adjointGroup Tag.E6 K) ∈ (CFSG.perfectResidual D).map D.subtype :=
      ⟨d', hd', rfl⟩
    have hηd := hηD _ hdD
    have h1 := hψη (d' : adjointGroup Tag.E6 K)
    rw [hηd] at h1
    rw [hψdef d']
    exact h1.symm
  obtain ⟨w, k₂, h₁, h₂, hwker, hk₂, hlayer⟩ := phi6_A2A2_layer (K := K) hℓ hf hK hFr hp hp3 hpq'
    hh hordy hA2A2
  set nw : ModGL Tag.E6 L := canonicalRep (coxeterSystem Tag.E6) L w with hnw
  obtain ⟨hy'H, hy'ker⟩ := torusRootKernel_conj_canonicalRep hyH w
  rw [hwker] at hy'ker
  have hy'p : (nw * y * nw⁻¹) ^ p = 1 := by
    rw [← MulAut.conj_apply, ← map_pow, hyp, map_one]
  have hy'1 : nw * y * nw⁻¹ ≠ 1 := fun h => hy1 (by
    have : y = nw⁻¹ * (nw * y * nw⁻¹) * nw := by group
    rw [this, h]
    group)
  obtain ⟨G₃', hG₃'A, hG₃'eq, hstd⟩ := phi6_std_position (iterateFrobenius L ℓ j) hςbij w hQG hG₃
  have hfix' := hstd y hfixy
  have hlayer' : ∀ A : SL(3, k₂), ((G₃' * (diagQ L) ^ ε) *
      Units.map (entrywiseHom (iterateFrobenius L ℓ j)) (twoA2Mul L (h₁ *
        Matrix.SpecialLinearGroup.map k₂.subtype A * h₁⁻¹, h₂ * Matrix.SpecialLinearGroup.map Fr
          (Matrix.SpecialLinearGroup.map k₂.subtype A) * h₂⁻¹)) * (G₃' * (diagQ L) ^ ε)⁻¹ =
      twoA2Mul L (h₁ * Matrix.SpecialLinearGroup.map k₂.subtype A * h₁⁻¹, h₂ *
        Matrix.SpecialLinearGroup.map Fr (Matrix.SpecialLinearGroup.map k₂.subtype A) * h₂⁻¹)) :=
    fun A => by
    have hq := hlayer A
    have h1 := hstd _ (hPfix _ hq)
    have e : nw * (nw⁻¹ * twoA2Mul L (h₁ * Matrix.SpecialLinearGroup.map k₂.subtype A * h₁⁻¹,
        h₂ * Matrix.SpecialLinearGroup.map Fr (Matrix.SpecialLinearGroup.map k₂.subtype A) *
          h₂⁻¹) * nw) * nw⁻¹ = twoA2Mul L (h₁ * Matrix.SpecialLinearGroup.map k₂.subtype A * h₁⁻¹,
        h₂ * Matrix.SpecialLinearGroup.map Fr (Matrix.SpecialLinearGroup.map k₂.subtype A) *
          h₂⁻¹) := by group
    rw [e] at h1
    exact h1
  obtain ⟨w', hrc, hcase⟩ := R_main hp5 hpL hy'H hy'p hy'ker ((diagQ L) ^ ε) πε hπc hQd hQroot
    (iterateFrobenius L ℓ j) Fr hςbij hFrbij k₂ h₁ h₂ hG₃'A hfix' hlayer'
  have hFrt : ∀ t : L, (iterateFrobenius L ℓ j) (Fr t) = t ^ ℓ ^ (f + j) := fun t => by
    rw [iterateFrobenius_def, hFr, ← pow_mul, ← pow_add]
  have hj0ε0 : j = 0 ∧ ε = 0 := by
    rcases hcase with ⟨hpres, hςid⟩ | ⟨hexch, hςFr⟩
    · have hj0 : j = 0 := by
        by_contra hjne
        have h := two_mul_le_of_pow_eq hf k₂ hk₂ (n := j) hjne (fun t ht => by
          rw [← iterateFrobenius_def ℓ j t]
          exact hςid t ht)
        omega
      refine ⟨hj0, ?_⟩
      by_contra hεne
      have hε1 : ε = 1 := by omega
      have hπ := hπ1 hε1
      refine graph_not_preserve hp5 hζ hy'H hy'p hy'1 hy'ker w' (fun b hb v => ?_)
        (fun α hα => ?_)
      · have h := hrc b hb v
        rw [hπ, hj0] at h
        rw [h]
        exact units_map_iterateFrobenius_zero _
      · have h := hpres.1 α hα
        rwa [hπ] at h
    · exfalso
      have h := two_mul_le_of_pow_eq hf k₂ hk₂ (n := f + j) (by omega) (fun t ht => by
        rw [← hFrt t]
        exact hςFr t ht)
      omega
  obtain ⟨hj0, hε0⟩ := hj0ε0
  have hQ1 : (diagQ L) ^ ε = 1 := by rw [hε0, pow_zero]
  have hΦ0 : ∀ u : ModGL Tag.E6 L, Units.map (entrywiseHom (iterateFrobenius L ℓ j)) u = u :=
    fun u => by
      rw [hj0]
      exact entrywise_iterateFrobenius_zero u
  have hG₃fix : G₃ * y * G₃⁻¹ = y := by simpa [hQ1, hΦ0] using hfixy
  have hG₃P : ∀ q ∈ P, G₃ * q * G₃⁻¹ = q := fun q hq => by
    simpa [hQ1, hΦ0] using hPfix q hq
  have hG₃HQ : G₃ ∈ torusGroup Tag.E6 L ⊔ rootSpan Tag.E6 L (torusRootKernel y) := by
    rw [← centralizer_eq_sup_of_pow_eq_one hp5 hpL hyH hyp]
    refine Subgroup.mem_inf.2 ⟨hG₃, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    calc G₃ * y = (G₃ * y * G₃⁻¹) * G₃ := by group
      _ = y * G₃ := by rw [hG₃fix]
  have hG₃H : G₃ ∈ torusGroup Tag.E6 L := hC6 ⟨hG₃HQ, Subgroup.mem_centralizer_iff.2 fun q hq => by
    calc q * G₃ = (G₃ * q * G₃⁻¹) * G₃ := by rw [hG₃P q hq]
      _ = G₃ * q := by group⟩
  have hΦι : Units.map (entrywiseHom Fr) (ι g) = ι g := adjEmb_frobenius Fr hFrK g
  have hFrc : ∀ c : K, Fr (algebraMap K L c) = algebraMap K L c := fun c => by
    rw [hFrK, ← map_pow, Nat.card_eq_fintype_card, FiniteField.pow_card]
  have hΦdiag : Units.map (entrywiseHom Fr) (diagL L a) = diagL L a := by
    unfold diagL
    rw [units_map_entrywise_rootDiagUnit]
    congr 1
    funext i
    apply Units.ext
    exact hFrc (a i)
  have hG₃form : G₃ = g0⁻¹ * (ι g * diagL L a) * g0 := by
    have h := hG₃eq
    rw [hQ1, hΦ0] at h
    simpa using h
  have hθ : phi6N L * Units.map (entrywiseHom Fr) G₃ * (phi6N L)⁻¹ = G₃ := by
    rw [hG₃form]
    simp only [map_mul, map_inv, hΦι, hΦdiag, hg0]
    group
  refine ⟨G₃, mem_twistedTorus.2 ⟨hG₃H, hθ⟩, fun d => ?_⟩
  have h := hψη d
  rw [hQ1, hΦ0] at h
  rw [hψ0 (η d), hψ0 d]
  simpa using h

end CFSG.RankThree.PartOne.KE6
