module

public import CFSG.LieType.Steinberg.CentralExt.PSLSmall
public import CFSG.RankThree.PartTwo.Sec20.Item20Res2ProofSL3

public section

namespace CFSG.RankThree.PartTwo.Sec20.Res3

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open Matrix
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem center_sl3_eq_bot_of_card_two {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2) :
    Subgroup.center (SpecialLinearGroup (Fin 3) F) = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  obtain ⟨r, hr3, hrg⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hg
  have hr : r = 1 := by
    rcases Sec20.Res2.eq_zero_or_eq_one_of_card_two hF r with h | h
    · rw [h] at hr3
      simp at hr3
    · exact h
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  rw [← hrg, hr]
  simp

@[expose] noncomputable def slEquivPSLGaloisTwoOne {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 2) :
    SpecialLinearGroup (Fin 3) F ≃* ProjectiveSpecialLinearGroup (Fin 3) (GaloisField 2 1) :=
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  ((QuotientGroup.quotientBot.symm.trans
      (QuotientGroup.quotientMulEquivOfEq (center_sl3_eq_bot_of_card_two hF).symm)).trans
    (CFSG.ClassicalModels.projectiveSpecialLinearFieldEquiv
      (CFSG.ClassicalModels.finiteFieldEquivGaloisField F 2 1 (by norm_num)
        (by rw [hF, pow_one])) (Fin 3)))

omit [Finite G] in
theorem card_ker_le_two_of_sl3_two
    {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2)
    {E : Type} [Group E] [Group.IsPerfect E] (π : E →* SpecialLinearGroup (Fin 3) F)
    (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E) :
    Nat.card π.ker ≤ 2 := by
  set X := ProjectiveSpecialLinearGroup (Fin 3) (GaloisField 2 1)
  set e := slEquivPSLGaloisTwoOne hF with he
  set q : E →* X := e.toMonoidHom.comp π with hq
  have hqs : Function.Surjective q := e.surjective.comp hπ
  have hqk : q.ker = π.ker := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, hq, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      map_eq_one_iff e e.injective]
  have hqc : q.ker ≤ Subgroup.center E := hqk ▸ hcen
  obtain ⟨-, ⟨eM⟩⟩ := CFSG.LieType.Steinberg.CentralExt.SLClosed.psl_three_two_hopfMultiplier
  have : Finite (CFSG.Open.griessHopfMultiplier X) := Finite.of_equiv _ eM.symm.toEquiv
  have hM : Nat.card (CFSG.Open.griessHopfMultiplier X) = 2 := by
    rw [Nat.card_congr eM.toEquiv, Nat.card_eq_fintype_card, Fintype.card_multiplicative,
      ZMod.card]
  let ψ : CFSG.Open.griessHopfMultiplier X →* q.ker :=
    (CFSG.RankThree.PerfectCover.hopfMultiplierToKer q hqs hqc).comp
      (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess X).toMonoidHom
  have hψ : Function.Surjective ψ :=
    (CFSG.RankThree.PerfectCover.hopfMultiplierToKer_surjective q hqs hqc).comp
      (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess X).surjective
  have hle := Nat.card_le_card_of_surjective ψ hψ
  rw [hM] at hle
  rw [← hqk]
  exact hle

theorem card_pCoreOf_le_two_mul
    {K Q : Subgroup G} {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 2) [Group.IsPerfect ↥K]
    (α : ↥K →* SpecialLinearGroup (Fin 3) F) (hαs : Function.Surjective α)
    (hαk : ∀ k : ↥K, α k = 1 ↔ (k : G) ∈ CFSG.Open.pCoreOf 2 K)
    (hQK : Q ≤ K) (hKQ : K ≤ Subgroup.normalizer (Q : Set G))
    (hQO : Q ≤ CFSG.Open.pCoreOf 2 K) (hcomm : ⁅CFSG.Open.pCoreOf 2 K, K⁆ ≤ Q) :
    Nat.card (CFSG.Open.pCoreOf 2 K) ≤ 2 * Nat.card Q := by
  set Q' := Q.subgroupOf K with hQ'
  have : Q'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hQK).mpr hKQ
  have hle : Q' ≤ α.ker := fun x hx =>
    MonoidHom.mem_ker.mpr ((hαk x).mpr (hQO (Subgroup.mem_subgroupOf.mp hx)))
  set π : (↥K ⧸ Q') →* SpecialLinearGroup (Fin 3) F := QuotientGroup.lift Q' α hle with hπ
  have hπmk : ∀ k : ↥K, π (k : ↥K ⧸ Q') = α k := fun k => by
    rw [hπ, QuotientGroup.lift_mk]
  have hπs : Function.Surjective π := by
    intro g
    obtain ⟨k, rfl⟩ := hαs g
    exact ⟨(k : ↥K ⧸ Q'), hπmk k⟩
  have : Group.IsPerfect (↥K ⧸ Q') :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' Q') (QuotientGroup.mk'_surjective _)
  have hcen : π.ker ≤ Subgroup.center (↥K ⧸ Q') := by
    intro y hy
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective y
    have hk : (k : G) ∈ CFSG.Open.pCoreOf 2 K := by
      rw [← hαk, ← hπmk]
      exact hy
    rw [Subgroup.mem_center_iff]
    intro z
    obtain ⟨k', rfl⟩ := QuotientGroup.mk_surjective z
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have h := Subgroup.commutator_mem_commutator (inv_mem hk) (inv_mem k'.2)
    have e : (((k' * k)⁻¹ * (k * k') : ↥K) : G) = ⁅(k : G)⁻¹, (k' : G)⁻¹⁆ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def, inv_inv]
      group
    rw [e]
    exact hcomm h
  have hker := card_ker_le_two_of_sl3_two hF π hπs hcen
  set O' := (CFSG.Open.pCoreOf 2 K).subgroupOf K with hO'
  set f : ↥O' →* ↥K ⧸ Q' := (QuotientGroup.mk' Q').comp O'.subtype with hf
  have hrange : f.range ≤ π.ker := by
    rintro _ ⟨o, rfl⟩
    rw [MonoidHom.mem_ker, hf, MonoidHom.comp_apply, QuotientGroup.mk'_apply, hπmk]
    exact (hαk o).mpr (Subgroup.mem_subgroupOf.mp o.2)
  have hkerf : Nat.card f.ker = Nat.card Q := by
    have hfk : f.ker = Q'.subgroupOf O' := by
      ext o
      rw [MonoidHom.mem_ker, hf, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      rfl
    have hQO' : Q' ≤ O' := fun x hx =>
      Subgroup.mem_subgroupOf.mpr (hQO (Subgroup.mem_subgroupOf.mp hx))
    rw [hfk, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQO').toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQK).toEquiv]
  have hO'card : Nat.card O' = Nat.card (CFSG.Open.pCoreOf 2 K) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (CFSG.LieType.BorelTits.pCoreOf_le 2 K)).toEquiv
  have h1 := Subgroup.card_ker_mul_card_range f
  have h2 : Nat.card f.range ≤ Nat.card π.ker := Subgroup.card_le_of_le hrange
  rw [hkerf, hO'card] at h1
  rw [← h1]
  calc Nat.card Q * Nat.card f.range ≤ Nat.card Q * 2 :=
        Nat.mul_le_mul_left _ (h2.trans hker)
    _ = 2 * Nat.card Q := mul_comm _ _

end CFSG.RankThree.PartTwo.Sec20.Res3
