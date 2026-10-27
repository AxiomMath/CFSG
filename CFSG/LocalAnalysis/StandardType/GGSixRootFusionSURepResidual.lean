module

public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionSURepToral

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21 Matrix
open CFSG.SectionRank.OddCover (diagHom coe_diagHom det_diagHom diagHom_injective)
open CFSG.ClassicalGroups.UnitaryFlag (unitarySU mem_unitarySU_iff)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.LieType.Universal.Unitary (SU antidiag conjTr)
open CFSG.LieType.BorelTits (unitaryInvolution)

@[expose] def GGSUBlockNotExcludedInput : Prop :=
  ∀ (G : Type) [Group G] (p f m : ℕ) (L₁ : Subgroup G), 1 ≤ f → 6 ≤ m →
    Nonempty (↥L₁ ≃* ↥(unitarySU 2 f (GaloisField 2 (2 * f)) m)) →
      ¬ GGSixSeventeenExcluded p .PSU f L₁

@[expose] def GGSUSixAlphaInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (f n : ℕ), n = 6 →
    ∀ ψ : SU (unitaryInvolution (GaloisField 2 (2 * (f + 1))) 2 (f + 1)) n →* G,
    ψ.ker ≤ Subgroup.center (SU (unitaryInvolution (GaloisField 2 (2 * (f + 1))) 2 (f + 1)) n) →
      ∀ a : SU (unitaryInvolution (GaloisField 2 (2 * (f + 1))) 2 (f + 1)) n,
        ¬ ∃ φ : ↥(ggCentOTwoPrime ψ.range
            (ψ (ggInvSU (unitaryInvolution (GaloisField 2 (2 * (f + 1))) 2 (f + 1)) n 3))) →*
          ↥(ggCentOTwoPrime ψ.range (ψ (a * ggInvSU
            (unitaryInvolution (GaloisField 2 (2 * (f + 1))) 2 (f + 1)) n 1 * a⁻¹))),
          Function.Injective φ

namespace SURep

variable {G : Type} [Group G] {n f : ℕ} {F : Type} [Field F]

theorem nonempty_map_blockSU_equiv (h : UnitaryFieldData 2 f F) {φ : ↥(unitarySU 2 f F n) →* G}
    (hker : GGFrameKer φ) {S : Finset (Fin n)} {i₀ : Fin n} (hi₀ : i₀ ∉ S) :
    Nonempty (↥((TableBUE.blockSU (K := F) (n := f) S).map φ) ≃*
      ↥(unitarySU 2 f F S.card)) := by
  set J₀ := TableBUE.blockSU (K := F) (n := f) S with hJ₀
  have hinj : Function.Injective (φ.comp J₀.subtype) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    obtain ⟨c, hc⟩ := hker x hx
    have hii := x.2 i₀ i₀ (Or.inl hi₀)
    rw [hc, Matrix.scalar_apply, diagonal_apply_eq, Matrix.one_apply_eq] at hii
    apply Subtype.ext
    apply Subtype.ext
    apply Units.ext
    change (((x : ↥(unitarySU 2 f F n)) : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = 1
    rw [hc, hii, map_one]
  have hrange : (φ.comp J₀.subtype).range = J₀.map φ := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  exact ⟨((MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)).symm.trans
    (TableBUE.blockSUEquiv S h).symm⟩

end SURep

section Inputs

theorem ggSixRootFusionSURepResidualInput_of_known (h1 : GGSUBlockNotExcludedInput)
    (h2 : GGSUSixAlphaInput) : GGSixRootFusionSURepResidualInput := by
  intro G _ _ p B Bs x L D J n f ψ hctx s1 s2 E r hch hC hodd hsplit hpn P hP hframe hns l hl2 hn
  have hβ := hctx.1.2.2.2.2.2.1
  have hp : p.Prime := hβ.1
  have hp2 : p ≠ 2 := hβ.2.1
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  obtain ⟨hrange, hker⟩ := hctx.2.2.2.2.1
  have hpl : p ∣ l := by
    have h2l : p ∣ 2 * l := hn ▸ hpn
    exact Nat.Coprime.dvd_of_dvd_mul_left ((Nat.coprime_primes hp Nat.prime_two).mpr hp2) h2l
  have hl3 : l = 3 ∨ 5 ≤ l := by
    have hle := Nat.le_of_dvd (by omega) hpl
    rcases (show l = 3 ∨ l = 4 ∨ 5 ≤ l by omega) with h | h | h
    · exact Or.inl h
    · exfalso
      subst h
      have hp4 : p ≤ 4 := Nat.le_of_dvd (by norm_num) hpl
      rcases (show p = 3 ∨ p = 4 by omega) with rfl | rfl
      · norm_num at hpl
      · norm_num at hp
    · exact Or.inr h
  have hr : ∃ v a : SU (unitaryInvolution (GaloisField 2 (2 * (f + 1))) 2 (f + 1)) n,
      r = ψ (v * (a * ggInvSU (unitaryInvolution (GaloisField 2 (2 * (f + 1))) 2 (f + 1)) n 1 *
        a⁻¹) * v⁻¹) := by
    obtain ⟨-, -, -, -, hr2, γ, hγ, v, -, hrv⟩ := hch
    obtain ⟨_, ⟨z, hz, rfl⟩, rfl⟩ := hrv
    have hz1 : z ≠ 1 := by
      rintro rfl
      rw [map_one, map_one, orderOf_one] at hr2
      exact absurd hr2 (by norm_num)
    obtain ⟨a, ha⟩ := ggSURootClassInput n f γ hγ z hz hz1
    subst ha
    exact ⟨v, a, rfl⟩
  rcases hl3 with rfl | hl5
  ·
    refine Or.inr (Or.inr ?_)
    obtain ⟨v, a, hra⟩ := hr
    have hconj : v * (a * ggInvSU (unitaryInvolution (GaloisField 2 (2 * (f + 1))) 2 (f + 1)) n 1 *
        a⁻¹) * v⁻¹ = (v * a) * ggInvSU (unitaryInvolution (GaloisField 2 (2 * (f + 1))) 2 (f + 1))
          n 1 * (v * a)⁻¹ := by group
    rw [hconj] at hra
    rw [hra, ← hrange]
    exact h2 G f n (by omega) ψ hker (v * a)
  ·
    have hn10 : 10 ≤ n := by omega
    have hF : Nat.card (GaloisField 2 (2 * (f + 1))) = (2 ^ (f + 1)) ^ 2 :=
      card_galoisField_two_mul 2 (f + 1) (Nat.le_add_left 1 f)
    have hdata : UnitaryFieldData 2 (f + 1) (GaloisField 2 (2 * (f + 1))) :=
      ⟨Nat.prime_two, by omega, by rw [hF, ← pow_mul, mul_comm]⟩
    have hc : SURep.FrameCtxU p B Bs (ggG0 p B x L D J) hF ψ P hP :=
      ⟨hdata, hctx.2.1, hker, hrange, s1.1, hframe, hp, hp2, hsplit, by omega⟩
    obtain ⟨ζ, hζ, -⟩ := CFSG.RankThree.Classical2.exists_orderOf_eq_norm_one hdata hp hsplit
    have hζp : ζ ^ p = 1 := hζ ▸ pow_orderOf_eq_one ζ
    have hζ1 : ζ ≠ 1 := fun h => by
      rw [h, orderOf_one] at hζ
      exact hp.one_lt.ne hζ
    set i0 : Fin n := ⟨0, by omega⟩ with hi0
    set i1 : Fin n := ⟨1, by omega⟩ with hi1
    set i2 : Fin n := ⟨n - 2, by omega⟩ with hi2
    set i3 : Fin n := ⟨n - 1, by omega⟩ with hi3
    set δ : Fin n → (GaloisField 2 (2 * (f + 1)))ˣ := Pi.mulSingle i0 ζ * Pi.mulSingle i3 ζ *
      Pi.mulSingle i1 ζ⁻¹ * Pi.mulSingle i2 ζ⁻¹ with hδdef
    have hδval : ∀ k : Fin n, δ k = if (k : ℕ) = 0 ∨ (k : ℕ) = n - 1 then ζ else
        if (k : ℕ) = 1 ∨ (k : ℕ) = n - 2 then ζ⁻¹ else 1 := by
      intro k
      have := k.isLt
      simp only [hδdef, Pi.mul_apply, Pi.mulSingle_apply, Fin.ext_iff, hi0, hi1, hi2, hi3]
      split_ifs <;> first | (exfalso; omega) | simp
    have hδ : ∏ k, δ k = 1 := by
      simp only [hδdef, Pi.mul_apply, Finset.prod_mul_distrib, Finset.prod_pi_mulSingle',
        Finset.mem_univ, ite_true]
      group
    have hδp : ∀ k, δ k ^ p = 1 := by
      intro k
      rw [hδval k]
      split_ifs
      · exact hζp
      · rw [inv_pow, hζp, inv_one]
      · exact one_pow p
    have hnorm : ∀ k, ((δ k : (GaloisField 2 (2 * (f + 1)))ˣ) : GaloisField 2 (2 * (f + 1))) ^
        (2 ^ (f + 1) + 1) = 1 := fun k => hc.norm_of_pow_eq_one (hδp k)
    set d : ↥(unitarySU 2 (f + 1) (GaloisField 2 (2 * (f + 1))) n) :=
      ⟨diagHom n δ, SURep.diagHom_mem_unitarySU' hdata hnorm hδ⟩ with hd
    have hdδ : (d : GL (Fin n) (GaloisField 2 (2 * (f + 1)))) = diagHom n δ := rfl
    have hdp : d ^ p = 1 := by
      apply Subtype.ext
      rw [SubmonoidClass.coe_pow, hdδ, ← map_pow]
      have : δ ^ p = 1 := funext hδp
      rw [this, map_one, Subgroup.coe_one]
    have hbBs := SURep.mem_of_frame_inner hc.bstar hdata hc.frame hdδ hdp
    have hb := SURep.frameActs_map (SURep.ggFrameU hF ψ P hP) hdδ hnorm
    set S : Finset (Fin n) := ({i0, i1, i2, i3} : Finset (Fin n))ᶜ with hS
    have hmemS : ∀ k : Fin n, k ∈ S ↔ ¬ ((k : ℕ) = 0 ∨ (k : ℕ) = n - 1 ∨ (k : ℕ) = 1 ∨
        (k : ℕ) = n - 2) := by
      intro k
      simp only [hS, Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff, hi0,
        hi1, hi2, hi3]
      tauto
    have hT4 : ({i0, i1, i2, i3} : Finset (Fin n)).card = 4 := by
      rw [Finset.card_insert_of_notMem (by simp [hi0, hi1, hi2, hi3, Fin.ext_iff]; omega),
        Finset.card_insert_of_notMem (by simp [hi1, hi2, hi3, Fin.ext_iff]; omega),
        Finset.card_pair (by simp [hi2, hi3, Fin.ext_iff]; omega)]
    have hScard : S.card = n - 4 := by rw [hS, Finset.card_compl, Fintype.card_fin, hT4]
    have hSc : Sᶜ.card = 4 := by rw [hS, compl_compl, hT4]
    have hδS : ∀ k ∈ S, δ k = 1 := by
      intro k hk
      rw [hmemS] at hk
      rw [hδval k, ite_eq_right (by omega), ite_eq_right (by omega)]
    have hδSc : ∀ k ∉ S, δ k ≠ 1 := by
      intro k hk
      rw [hmemS, not_not] at hk
      rw [hδval k]
      split_ifs with h₁ h₂
      · exact hζ1
      · exact inv_ne_one.mpr hζ1
      · exfalso
        omega
    have hi0S : i0 ∉ S := by rw [hmemS]; simp [hi0]
    have h2S : (⟨2, by omega⟩ : Fin n) ∈ S := by
      rw [hmemS]
      show ¬ (2 = 0 ∨ 2 = n - 1 ∨ 2 = 1 ∨ 2 = n - 2)
      omega
    have hb1 := SURep.ne_one_of_frameActs hc.frameKer hdata (by omega) hb (i := i0)
      (j := ⟨2, by omega⟩) (by
        rw [hδS _ h2S, hδval i0, ite_eq_left (Or.inl rfl)]
        exact hζ1)
    have hcomp := SURep.isComponentOf_map_blockSU hF hdata hc.frameKer hb hδS hδSc
      (by rw [hSc, hScard]; omega) (by rw [hScard]; omega)
      (fun h' => by have h3 : S.card = 3 := congrArg Prod.fst h'; omega) hi0S
    rw [hc.rangeφ] at hcomp
    have hnex := h1 G p (f + 1) S.card _ (by omega) (by rw [hScard]; omega)
      (SURep.nonempty_map_blockSU_equiv hdata hc.frameKer hi0S)
    have hW : GGSixFusionWitness p Bs D E (ggG0 p B x L D J) .PSU (f + 1)
        (SURep.ggFrameU hF ψ P hP d) := ⟨hb1, Or.inr (Or.inr ⟨hbBs, _, hcomp, Or.inr hnex⟩)⟩
    refine SURep.ggRootFusionWitnessAlt_of_frameU hF hdata (by omega) (by omega)
      (fun y hy => Subgroup.le_normalizer (hrange ▸ hy)) hb hW 1 fun c hcl => ?_
    simp only [Equiv.Perm.one_apply]
    have hcn := c.isLt
    rw [hδval c, hδval (Fin.rev c)]
    simp only [Fin.val_rev]
    split_ifs <;> first | rfl | (exfalso; omega)

theorem ggSixRootFusionSURepInput_of_nonsplit_known (hN : GGSixRootFusionSURepNonsplitInput)
    (h1 : GGSUBlockNotExcludedInput) (h2 : GGSUSixAlphaInput) : GGSixRootFusionSURepInput :=
  ggSixRootFusionSURepInput_of_nonsplit_residual hN
    (ggSixRootFusionSURepResidualInput_of_known h1 h2)

end Inputs

end CFSG.StandardType
