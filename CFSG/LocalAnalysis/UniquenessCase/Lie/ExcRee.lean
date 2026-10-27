module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P20o
import CFSG.LieType.Ree.LargeReeInvolutionCentralizersRankOne
import CFSG.LocalAnalysis.UniquenessCase.Lie.ExcShared

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley CFSG.LieType.Ree Subgroup
open CFSG.Blueprint (LieModel)

section Coordinates


theorem uc22pwex_reeTorus_coe {K : Type} [Field K] (a : ℕ) (j : Fin ReeTag.F4.tag.rank) (u : Kˣ) :
    ((ReeTag.F4.reeTorus a j u : adjointGroup ReeTag.F4.tag K) : ModGL ReeTag.F4.tag K) =
      (torusCoordHom ReeTag.F4.tag K (Pi.mulSingle j u *
        Pi.mulSingle (ReeTag.F4.perm j) (u ^ (2 ^ a))) : ModGL ReeTag.F4.tag K) := by
  rw [map_mul, Subgroup.coe_mul, coe_torusCoordHom_mulSingle, coe_torusCoordHom_mulSingle]
  rfl

end Coordinates

section Witness


theorem uc22pwex_f4_borelWit {G : Type} [Group G] [Finite G] {n : ℕ}
    (hG : LieModel G .twistedF4 0 2 n) {p : ℕ} (hp : p.Prime) (hpn : p ∣ 2 ^ n - 1) :
    uc22p20oBorelWit G p 2 := by
  obtain ⟨-, a, ha1, hna, K, _, _, _, hK, ⟨e⟩⟩ :=
    CFSG.RankThree.PartTwo.Sec4.exists_mulEquiv_reeGamma (hG.reeTitsModel (by decide)).2
  have hpF : p ∣ Nat.card K - 1 := by rw [hK, ← hna]; exact hpn
  obtain ⟨μ, hμc, hμp⟩ := uc22pwex_exists_mu hp hpF
  let j0 : Fin ReeTag.F4.tag.rank := ⟨0, by decide⟩
  let j1 : Fin ReeTag.F4.tag.rank := ⟨1, by decide⟩
  have hj0 : j0 ∈ ReeTag.F4.longSet := by decide
  have hj1 : j1 ∈ ReeTag.F4.longSet := by decide
  have h01 : j1 ≠ j0 := by decide
  have h0p0 : ReeTag.F4.perm j0 ≠ j0 := by decide
  have h0p1 : ReeTag.F4.perm j1 ≠ j0 := by decide
  have h1p0 : ReeTag.F4.perm j0 ≠ j1 := by decide
  have h1p1 : ReeTag.F4.perm j1 ≠ j1 := by decide
  let ι : (μ × μ) →* (Fin ReeTag.F4.tag.rank → Kˣ) := MonoidHom.mk'
    (fun x => (Pi.mulSingle j0 (x.1 : Kˣ) *
        Pi.mulSingle (ReeTag.F4.perm j0) ((x.1 : Kˣ) ^ 2 ^ a)) *
      (Pi.mulSingle j1 (x.2 : Kˣ) * Pi.mulSingle (ReeTag.F4.perm j1) ((x.2 : Kˣ) ^ 2 ^ a)))
    (by
      intro x y
      simp only [Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul, Pi.mulSingle_mul, mul_pow]
      ac_rfl)
  let Φ0 : (μ × μ) →* ModGL ReeTag.F4.tag K :=
    (torusGroup ReeTag.F4.tag K).subtype.comp ((torusCoordHom ReeTag.F4.tag K).comp ι)
  have hK' : Nat.card K = ReeTag.F4.prime ^ (2 * a + 1) := hK
  have hid : ∀ x : μ × μ, Φ0 x = ((ReeTag.F4.reeTorus a j0 (x.1 : Kˣ) *
      ReeTag.F4.reeTorus a j1 (x.2 : Kˣ) : adjointGroup ReeTag.F4.tag K) :
        ModGL ReeTag.F4.tag K) := by
    intro x
    rw [Subgroup.coe_mul, uc22pwex_reeTorus_coe, uc22pwex_reeTorus_coe]
    show (torusCoordHom ReeTag.F4.tag K (ι x) : ModGL ReeTag.F4.tag K) = _
    have hιx : ι x = (Pi.mulSingle j0 (x.1 : Kˣ) *
        Pi.mulSingle (ReeTag.F4.perm j0) ((x.1 : Kˣ) ^ 2 ^ a)) *
        (Pi.mulSingle j1 (x.2 : Kˣ) * Pi.mulSingle (ReeTag.F4.perm j1) ((x.2 : Kˣ) ^ 2 ^ a)) := rfl
    rw [hιx, map_mul, Subgroup.coe_mul]
  have hmem : ∀ x : μ × μ, Φ0 x ∈ ReeTag.F4.reeGamma K a := by
    intro x
    rw [hid x, ← LargeReeInvolution.map_reeFixed_eq_reeGamma]
    exact ⟨_, mul_mem (ReeTag.reeTorus_mem_reeFixed ReeTag.F4 a hK' hj0 _)
      (ReeTag.reeTorus_mem_reeFixed ReeTag.F4 a hK' hj1 _), rfl⟩
  let Φ : (μ × μ) →* ↥(ReeTag.F4.reeGamma K a) := Φ0.codRestrict _ hmem
  have hinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have h1 : torusCoordHom ReeTag.F4.tag K (ι x) = 1 := by
      have := congrArg (fun y : ↥(ReeTag.F4.reeGamma K a) => (y : ModGL ReeTag.F4.tag K)) hx
      exact Subtype.ext this
    have h2 : ι x = 1 := torusCoordHom_injective_of_mul_eq_one cartan_mul_cartanInv_F4
      (h1.trans (map_one _).symm)
    have e0 := congrFun h2 j0
    have e1 := congrFun h2 j1
    simp [ι, Pi.mul_apply, Pi.mulSingle_apply, h01, h01.symm, h0p0, h0p0.symm, h0p1, h0p1.symm,
      h1p0, h1p0.symm, h1p1, h1p1.symm] at e0 e1
    exact Prod.ext e0 e1
  have hA : Nat.card (μ × μ) = p ^ 2 := by rw [Nat.card_prod, hμc, sq]
  obtain ⟨hE, hc⟩ := uc22pwex_elemAbelian_range Φ hinj (fun a b => mul_comm a b)
    (fun a => Prod.ext (Subtype.ext (hμp a.1)) (Subtype.ext (hμp a.2))) hA
  have hN : Φ.range ≤ normalizer (((ReeTag.F4.reeFixedPosUnipotent K a).subgroupOf
      (ReeTag.F4.reeGamma K a) : Subgroup ↥(ReeTag.F4.reeGamma K a)) :
        Set ↥(ReeTag.F4.reeGamma K a)) := by
    rintro _ ⟨x, rfl⟩
    rw [mem_normalizer_iff]
    intro y
    have hx : ((Φ x : ↥(ReeTag.F4.reeGamma K a)) : ModGL ReeTag.F4.tag K) ∈
        normalizer (posUnipotent ReeTag.F4.tag K : Set (ModGL ReeTag.F4.tag K)) :=
      torusGroup_le_normalizer_posUnipotent (torusCoordHom ReeTag.F4.tag K (ι x)).2
    have hx' := mem_normalizer_iff.1 hx (y : ModGL ReeTag.F4.tag K)
    have hz2 := (Φ x * y * (Φ x)⁻¹).2
    simp only [Subgroup.mem_subgroupOf, ReeTag.reeFixedPosUnipotent, Subgroup.mem_inf,
      Subgroup.coe_mul, Subgroup.coe_inv] at hz2 ⊢
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨hx'.1 h1, hz2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨hx'.2 h1, y.2⟩
  haveI : CharP K 2 := uc22pwex_charP_two hK
  exact uc22pwex_borelWit_of_equiv e _
    (ReeTag.isPGroup_reeFixedPosUnipotent_subgroupOf (t := ReeTag.F4) (K := K) (a := a))
    (ReeTag.not_dvd_index_reeFixedPosUnipotent (t := ReeTag.F4) (K := K) (a := a)) Φ.range hN hE hc

end Witness

end CFSG.LocalAnalysis.UniquenessCase.UC22
