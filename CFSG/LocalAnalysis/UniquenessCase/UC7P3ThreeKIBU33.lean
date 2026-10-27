module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.KInputs
import CFSG.LocalAnalysis.UniquenessCase.UC7P3ThreeKIBWeights
import CFSG.HardMathSupport.Dickson.Bal207.SmallU33
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.UnitaryTorus
import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Proving.QuasisimpleOfCentralKer
import CFSG.RankThree.PartTwo.Sec4.RonanK432SylowCount

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.ThreeKIB

open Module Module.End
open scoped commutatorElement

theorem heis_pow {K W : Type*} [Field K] [AddCommGroup W] [Module K W] {S R X : End K W}
    (hSX : ∀ w, S (X w) = X (S w)) (hRX : ∀ w, R (X w) = X (S (R w))) {w : W} {μ ν : K}
    (hS : S w = μ • w) (hR : R w = ν • w) (j : ℕ) :
    S ((X ^ j) w) = μ • (X ^ j) w ∧ R ((X ^ j) w) = (μ ^ j * ν) • (X ^ j) w := by
  induction j with
  | zero => simpa using ⟨hS, hR⟩
  | succ j ih =>
    rw [pow_succ', mul_apply]
    refine ⟨by rw [hSX, ih.1, map_smul], ?_⟩
    rw [hRX, ih.2, map_smul, ih.1, smul_smul, map_smul]
    congr 1
    ring

theorem coverActsTriviallyOnSmall_of_heis {L : Type*} [Group L] [Finite L] [IsSimpleGroup L]
    {U : Subgroup L} (hU : IsPGroup 3 U) {r x c : L} (hr : r ∈ U) (hx : x ∈ U)
    (hsr : ⁅r, x⁆ * r = r * ⁅r, x⁆) (hsx : ⁅r, x⁆ * x = x * ⁅r, x⁆) (hs1 : ⁅r, x⁆ ≠ 1)
    (hs3 : ⁅r, x⁆ ^ 3 = 1) (hcN : c ∈ Subgroup.normalizer (U : Set L))
    (hcs : c * ⁅r, x⁆⁻¹ * c⁻¹ = ⁅r, x⁆) : CoverActsTriviallyOnSmall 3 L := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let r' : U := ⟨r, hr⟩
  let x' : U := ⟨x, hx⟩
  let s : U := ⁅r', x'⁆
  have hsx' : s * x' = x' * s := Subtype.ext hsx
  have hsr' : Commute s r' := Subtype.ext hsr
  have hrx' : r' * x' = x' * (s * r') := Subtype.ext <| by
    change r * x = x * (⁅r, x⁆ * r)
    rw [← mul_assoc, ← hsx, commutatorElement_def]
    group
  have hs3' : s ^ 3 = 1 := Subtype.ext hs3
  have hsinv : s⁻¹ = s * s := inv_eq_iff_mul_eq_one.2 (by rw [← pow_three, hs3'])
  refine coverActsTriviallyOnSmall_of_rep Nat.prime_three
    fun J _ _ φ hφ hcop K _ _ _ h3K W _ _ _ hW τ hτ => ?_
  obtain ⟨f', ĉ, hf', rfl, hĉ⟩ := exists_lift_hom φ hφ
    (Nat.Coprime.of_dvd_left (dvd_mul_left 3 2) hcop.symm) hU U.subtype
    fun a => ⟨⟨_, (Subgroup.mem_normalizer_iff.1 hcN a).1 a.2⟩, rfl⟩
  set ρ := τ.comp f'
  have hρ1 : ∀ m, ρ m = 1 → m = 1 := fun m hm => Subtype.ext (by simpa [hf'] using hτ _ hm)
  have hS3 : ρ s ^ 3 = 1 := by rw [← map_pow, hs3', map_one]
  obtain ⟨v, hv0, σ, ν, hσ1, hσ3, hSv, hRv⟩ :=
    exists_jointEigen h3K hS3 (fun h => hs1 (congrArg Subtype.val (hρ1 s h))) (hsr'.map ρ)
  have hCv : ρ s (τ ĉ v) = (σ * σ) • τ ĉ v := by
    have h := conj_lift (f := U.subtype) (Subgroup.subtype_injective _) hf' hĉ (a := s⁻¹) (b := s)
      hcs
    rw [show ρ s = τ (f' s) from rfl, apply_of_conj τ h, show τ (f' s⁻¹) = ρ s⁻¹ from rfl,
      hsinv, map_mul, mul_apply, hSv, map_smul, hSv, smul_smul, map_smul]
  obtain ⟨v', hv'0, hSv', ν', hRv'⟩ := exists_eigen_of_commute (hsr'.map ρ) (c := σ * σ)
    fun h => apply_ne_zero τ ĉ hv0 ((Submodule.eq_bot_iff _).1 h _ (mem_eigenspace_iff.2 hCv))
  have hσ0 : σ ≠ 0 := by rintro rfl; norm_num at hσ3
  have hσσ : σ ≠ σ * σ := fun h => hσ1 (mul_left_cancel₀ hσ0 (h.symm.trans (mul_one σ).symm))
  let w : Fin 2 → W := ![v, v']
  let μ : Fin 2 → K := ![σ, σ * σ]
  let ν₀ : Fin 2 → K := ![ν, ν']
  have hw : ∀ i, w i ≠ 0 ∧ ρ s (w i) = μ i • w i ∧ ρ r' (w i) = ν₀ i • w i ∧ μ i ≠ 1 ∧
      μ i ^ 3 = 1 := by
    intro i
    fin_cases i
    · exact ⟨hv0, hSv, hRv, hσ1, hσ3⟩
    · refine ⟨hv'0, hSv', hRv', fun h => hσσ ?_, ?_⟩
      · change σ * σ = 1 at h
        rw [h, ← hσ3, pow_three, h, mul_one]
      · change (σ * σ) ^ 3 = 1
        rw [mul_pow, hσ3, one_mul]
  have hν : ∀ i, ν₀ i ≠ 0 := fun i h => apply_ne_zero ρ r' (hw i).1 (by
    rw [(hw i).2.2.1, h, zero_smul])
  have hSX : ∀ w, ρ s (ρ x' w) = ρ x' (ρ s w) := apply_comm ρ hsx'
  have hRX : ∀ w, ρ r' (ρ x' w) = ρ x' (ρ s (ρ r' w)) := fun w =>
    (apply_comm ρ hrx' w).trans (by rw [map_mul, mul_apply])
  have hli := linearIndependent_of_eigen₂ (ρ s) (ρ r') (fun k : Fin 2 × Fin 3 => μ k.1)
    (fun k => μ k.1 ^ (k.2 : ℕ) * ν₀ k.1) ?_ (fun k => (ρ x' ^ (k.2 : ℕ)) (w k.1))
    (fun k => by rw [← map_pow]; exact apply_ne_zero ρ _ (hw k.1).1)
    (fun k => (heis_pow hSX hRX (hw k.1).2.1 (hw k.1).2.2.1 k.2).1)
    (fun k => (heis_pow hSX hRX (hw k.1).2.1 (hw k.1).2.2.1 k.2).2)
  · have := hli.fintype_card_le_finrank
    simp only [Fintype.card_prod, Fintype.card_fin] at this
    omega
  · rintro ⟨i, j⟩ ⟨i', j'⟩ h1 h2
    obtain rfl : i = i' := by
      fin_cases i <;> fin_cases i'
      exacts [rfl, absurd h1 hσσ, absurd h1.symm hσσ, rfl]
    have hμ : IsOfFinOrder (μ i) := isOfFinOrder_iff_pow_eq_one.2 ⟨3, by norm_num, (hw i).2.2.2.2⟩
    have hjj := hμ.pow_inj_mod.1 (mul_right_cancel₀ (hν i) h2)
    rw [orderOf_eq_prime (hw i).2.2.2.2 (hw i).2.2.2.1, Nat.mod_eq_of_lt j.2,
      Nat.mod_eq_of_lt j'.2] at hjj
    exact Prod.ext rfl (Fin.ext hjj)

theorem coverActsTriviallyOnSmall_of_isoU33 {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.twistedA 2 q).Valid) (hq3 : q.p = 3) (hq1 : q.exponent = 1)
    {L : Type} [Group L] [Finite L] [IsSimpleGroup L]
    (e : L ≃* (TauCeti.CFSGIndex.lie ⟨.twistedA 2 q, hv⟩).Group) :
    CoverActsTriviallyOnSmall 3 L := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨U⟩ := Sylow.nonempty (p := 3) (G := L)
  have hU : Nat.card U = 3 ^ 3 := CFSG.RankThree.PartTwo.Sec4.RonanK432.card_sylow_eq_27
    (g' := 224) ((Nat.card_congr e.toEquiv).trans
      (CFSG.HardMathSupport.Dickson.Bal207.Small.card_u33 hv hq3 hq1)) rfl U
  obtain ⟨ψ, hψ, hrange, hc⟩ := CFSG.AGLEmbedding.kFactUnitarySylowCenterTorus L 3
    ⟨.twistedA 2 q, hv⟩ ⟨q, hq3, rfl⟩ ⟨e⟩ U
  have hfe : (⟨.twistedA 2 q, hv⟩ : TauCeti.ValidLieTypeIndex).1.fieldExponent = 1 :=
    (TauCeti.LieTypeIndex.fieldExponent_twistedA 2 q).trans hq1
  have h3 : Nat.card (Multiplicative (GaloisField 3
      (⟨.twistedA 2 q, hv⟩ : TauCeti.ValidLieTypeIndex).1.fieldExponent)) = 3 :=
    (GaloisField.card 3 _ (by rw [hfe]; exact one_ne_zero)).trans (by rw [hfe, pow_one])
  obtain ⟨r, hr, x, hx, hrx⟩ : ∃ r ∈ (U : Subgroup L), ∃ x ∈ (U : Subgroup L), r * x ≠ x * r := by
    by_contra! hcon
    have hle : (U : Subgroup L) ≤ Subgroup.centralizer ((U : Subgroup L) : Set L) :=
      fun y hy => Subgroup.mem_centralizer_iff.2 fun z hz => hcon z hz y hy
    have := Nat.card_congr (MonoidHom.ofInjective hψ).toEquiv
    rw [h3, hrange, inf_eq_left.2 hle, hU] at this
    norm_num at this
  have hsZ := CFSG.AGLEmbeddingD2.Wilson.Proving.commutatorElement_mem_center_of_card_eq_prime_cube
    hU (⟨r, hr⟩ : (U : Subgroup L)) ⟨x, hx⟩
  have hcomm : ∀ g ∈ (U : Subgroup L), g * ⁅r, x⁆ = ⁅r, x⁆ * g := fun g hg =>
    congrArg Subtype.val (Subgroup.mem_center_iff.1 hsZ ⟨g, hg⟩)
  obtain ⟨a, ha⟩ : ⁅r, x⁆ ∈ ψ.range :=
    hrange ▸ ⟨(⟨r, hr⟩ * ⟨x, hx⟩ * (⟨r, hr⟩ : (U : Subgroup L))⁻¹ * (⟨x, hx⟩ : (U : Subgroup L))⁻¹ :
      (U : Subgroup L)).2, Subgroup.mem_centralizer_iff.2 hcomm⟩
  obtain ⟨c, hcN, hcs⟩ := hc (-1)
  have h := hcs a
  rw [Units.val_neg, Units.val_one, neg_one_mul, ofAdd_neg, ofAdd_toAdd, map_inv, ha] at h
  refine coverActsTriviallyOnSmall_of_heis U.isPGroup' hr hx (hcomm r hr).symm (hcomm x hx).symm
    (fun h1 => hrx (commutatorElement_eq_one_iff_mul_comm.1 h1)) ?_ hcN ?_
  · rw [← ha, ← map_pow, (congrArg (a ^ ·) h3.symm).trans pow_card_eq_one', map_one]
  · calc c * ⁅r, x⁆⁻¹ * c⁻¹ = (c * ⁅r, x⁆ * c⁻¹)⁻¹ := by group
      _ = ⁅r, x⁆ := by rw [h, inv_inv]

theorem coverActsTriviallyOnSmall_u33 {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.twistedA 2 q).Valid) (hq3 : q.p = 3) (hq1 : q.exponent = 1) :
    CoverActsTriviallyOnSmall 3 (TauCeti.CFSGIndex.lie ⟨.twistedA 2 q, hv⟩).Group := by
  obtain ⟨_, _, -⟩ := CFSG.HardMathSupport.Dickson.DefCharOuter.Export.carrier_twistedA 2 q hv
  exact coverActsTriviallyOnSmall_of_isoU33 hv hq3 hq1 (MulEquiv.refl _)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.ThreeKIB
