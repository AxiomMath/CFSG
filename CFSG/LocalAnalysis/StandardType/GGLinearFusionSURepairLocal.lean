module

public import CFSG.LocalAnalysis.StandardType.GGLinearFusionSURepairPair
public import CFSG.LocalAnalysis.StandardType.GGSixAutStructurePSUHolds

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank Matrix
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (primeFormConjHom primeFormConjHom_mk
  primeFormUnitary mem_primeFormUnitary)
open CFSG.LieType.Universal.Unitary (SU antidiag conjTr)
open CFSG.LieType.BorelTits (unitaryInvolution)
open scoped commutatorElement

namespace SURepair

theorem commutator_le_left_of_le_normalizer {G : Type} [Group G] {T B : Subgroup G}
    (hBT : B ≤ Subgroup.normalizer (T : Set G)) : ⁅T, B⁆ ≤ T := by
  rw [Subgroup.commutator_le]
  intro t ht b hb
  rw [commutatorElement_def]
  have h1 : b * t⁻¹ * b⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.mp (hBT hb) _).mp (T.inv_mem ht)
  have h2 := T.mul_mem ht h1
  rwa [show t * (b * t⁻¹ * b⁻¹) = t * b * t⁻¹ * b⁻¹ by group] at h2

section Aut

variable {f : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2] (h : UnitaryFieldData 2 f K)
  {n : ℕ} {G : Type} [Group G]

theorem mem_primeFormUnitary_of_isJUnitary {A : GL (Fin n) K}
    (hA : InnerDiagSU.IsJUnitary (unitaryInvolution K 2 f) A) :
    A ∈ primeFormUnitary h ((AutPSU.gramJ n : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [mem_primeFormUnitary, AutPSU.coe_gramJ, ← SURep.conjTr_eq_bar h]
  exact hA

include h in
theorem commutator_le_range (hn : 4 ≤ n) {ψ : SU (unitaryInvolution K 2 f) n →* G}
    (hker : ψ.ker ≤ Subgroup.center (SU (unitaryInvolution K 2 f) n))
    (hC : Subgroup.centralizer (ψ.range : Set G) = ⊥) {T B : Subgroup G}
    (hT2 : IsPGroup 2 T) (hTN : T ≤ Subgroup.normalizer (ψ.range : Set G))
    (hBT : B ≤ Subgroup.normalizer (T : Set G))
    (hB : ∀ b ∈ B, ∃ A : GL (Fin n) K, (b, A) ∈ UFusion.suInducedPairs ψ) :
    ⁅T, B⁆ ≤ ψ.range := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R := ψ.range with hR
  set Θ := AutPSU.projEquivU h hn hker hC with hΘ
  set N := Subgroup.normalizer (R : Set G) with hN
  set a : ↥N →* MulAut (AutPSU.PJ h n) :=
    (MulAut.congr Θ.symm).toMonoidHom.comp R.normalizerMonoidHom with ha
  have hΘu : ∀ u, Θ (AutPSU.projU h u) = ⟨ψ u, MonoidHom.mem_range.mpr ⟨u, rfl⟩⟩ := fun u =>
    Subtype.ext (AutPSU.projEquivU_projU h hn hker hC u)
  have haΘ : ∀ (g : N) (z : AutPSU.PJ h n),
      ((Θ (a g z) : R) : G) = (g : G) * (Θ z : G) * (g : G)⁻¹ := by
    intro g z
    simp only [ha, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.congr_apply,
      MulEquiv.trans_apply, MulEquiv.symm_symm, MulEquiv.apply_symm_apply]
    rfl
  have hBN : ∀ b ∈ B, b ∈ N := by
    intro b hb
    obtain ⟨A, hA⟩ := hB b hb
    have hA' := (UFusion.suInducedPairs ψ).inv_mem hA
    rw [Prod.inv_mk] at hA'
    refine Subgroup.mem_normalizer_iff.mpr fun r => ⟨?_, ?_⟩
    · rintro ⟨u, rfl⟩
      obtain ⟨hJ, hu⟩ := hA
      exact ⟨_, (hu u).symm⟩
    · rintro ⟨u, hu⟩
      obtain ⟨hJ', hu'⟩ := hA'
      refine ⟨InnerDiagSU.conjSU A⁻¹ hJ' u, ?_⟩
      rw [← hu' u, hu]
      group
  have hBI : ∀ b (hb : b ∈ B), a ⟨b, hBN b hb⟩ ∈ AutPSU.inndiag h := by
    intro b hb
    obtain ⟨A, hJ, hA⟩ := hB b hb
    refine ⟨⟨A, mem_primeFormUnitary_of_isJUnitary h hJ⟩, ?_⟩
    apply MulEquiv.ext
    intro z
    induction z using QuotientGroup.induction_on with
    | H x =>
      set u := (AutPSU.suEquiv h).symm x with hu
      have hxu : (x : AutPSU.PJ h n) = AutPSU.projU h u := by
        rw [AutPSU.projU_apply, hu, MulEquiv.apply_symm_apply]
      have e : ((⟨(A : GL (Fin n) K) * (x : GL (Fin n) K) * A⁻¹,
          CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.conj_mem_gramSU h _
            (mem_primeFormUnitary_of_isJUnitary h hJ) x.2⟩ :
            ↥(AutPSU.XJ h n)) : AutPSU.PJ h n) =
          AutPSU.projU h (InnerDiagSU.conjSU A hJ u) := by
        rw [AutPSU.projU_apply]
        congr 1
      apply Θ.injective
      apply Subtype.ext
      rw [primeFormConjHom_mk, e, hΘu, haΘ, hxu, hΘu]
      exact (hA u).symm
  have hIn := AutPSU.inndiag_normal h hn
  have hTB : ⁅T, B⁆ ≤ ((AutPSU.inndiag h).comap a).map N.subtype := by
    rw [Subgroup.commutator_le]
    intro t ht b hb
    refine ⟨⁅(⟨t, hTN ht⟩ : N), ⟨b, hBN b hb⟩⁆, ?_, rfl⟩
    show a ⁅_, _⁆ ∈ AutPSU.inndiag h
    rw [map_commutatorElement, commutatorElement_def]
    exact (AutPSU.inndiag h).mul_mem (hIn.conj_mem _ (hBI b hb) _)
      ((AutPSU.inndiag h).inv_mem (hBI b hb))
  intro y hy
  obtain ⟨⟨y, hyN⟩, hyI, rfl⟩ := hTB hy
  have hyT : y ∈ T := commutator_le_left_of_le_normalizer hBT hy
  obtain ⟨k, hk⟩ := hT2 ⟨y, hyT⟩
  have hyk : y ^ 2 ^ k = 1 := by
    have h1 := congrArg Subtype.val hk
    rwa [Subgroup.coe_pow, Subgroup.coe_one] at h1
  have hak : a ⟨y, hyN⟩ ^ 2 ^ k = 1 := by
    rw [← map_pow]
    have h1 : (⟨y, hyN⟩ : N) ^ 2 ^ k = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hyk)
    rw [h1, map_one]
  have hinn : a ⟨y, hyN⟩ ∈ (MulAut.conj : AutPSU.PJ h n →* MulAut (AutPSU.PJ h n)).range := by
    set I := AutPSU.inndiag h (n := n) with hI
    set H : Subgroup ↥I :=
      (MulAut.conj : AutPSU.PJ h n →* MulAut (AutPSU.PJ h n)).range.subgroupOf I with hH
    have hHn : H.Normal := Subgroup.normal_subgroupOf
    have hodd : Odd H.index := AutPSU.odd_relIndex_inn_inndiag h
    set g : ↥I := ⟨a ⟨y, hyN⟩, hyI⟩ with hg
    have hgk : g ^ 2 ^ k = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hak)
    have h1 : orderOf (QuotientGroup.mk' H g) ∣ 2 ^ k :=
      orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hgk, map_one])
    have h2 : orderOf (QuotientGroup.mk' H g) ∣ H.index := orderOf_dvd_natCard _
    have hcop : Nat.Coprime (2 ^ k) H.index := (Nat.coprime_two_left.mpr hodd).pow_left k
    have h3 : orderOf (QuotientGroup.mk' H g) = 1 :=
      Nat.dvd_one.mp (by rw [← Nat.Coprime.gcd_eq_one hcop]; exact Nat.dvd_gcd h1 h2)
    rw [orderOf_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h3
    exact h3
  obtain ⟨z, hz⟩ := hinn
  have hyz : ((Θ z : R) : G)⁻¹ * y ∈ Subgroup.centralizer (R : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨u, rfl⟩
    have e1 := haΘ ⟨y, hyN⟩ (AutPSU.projU h u)
    rw [← hz, MulAut.conj_apply, map_mul, map_mul, map_inv, hΘu] at e1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at e1
    calc ψ u * (((Θ z : R) : G)⁻¹ * y) =
        ((Θ z : R) : G)⁻¹ * (((Θ z : R) : G) * ψ u * ((Θ z : R) : G)⁻¹) * y := by group
      _ = ((Θ z : R) : G)⁻¹ * (y * ψ u * y⁻¹) * y := by rw [e1]
      _ = ((Θ z : R) : G)⁻¹ * y * ψ u := by group
  rw [hC, Subgroup.mem_bot, inv_mul_eq_one] at hyz
  change y ∈ R
  rw [← hyz]
  exact (Θ z).2

end Aut

end SURepair

section Inputs

theorem ggUnitaryBTwoLocalInput_holds : GGUnitaryBTwoLocalInput := by
  intro G _ _ p B Bs x L D J n f ψ hctx s1 hp
  have hf : 1 ≤ f := hctx.2.2.2.1.1.2.1
  obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
  have hrank : 2 ≤ n / 2 := hctx.2.2.2.1.2
  have hn4 : 4 ≤ n := by omega
  have hF : Nat.card (GaloisField 2 (2 * (f + 1))) = (2 ^ (f + 1)) ^ 2 :=
    card_galoisField_two_mul 2 (f + 1) (Nat.le_add_left 1 f)
  have h : UnitaryFieldData 2 (f + 1) (GaloisField 2 (2 * (f + 1))) :=
    ⟨Nat.prime_two, by omega, by rw [hF, ← pow_mul, mul_comm]⟩
  obtain ⟨hrange, hker⟩ := hctx.2.2.2.2.1
  have hC : Subgroup.centralizer ((ψ.range : Subgroup G) : Set G) = ⊥ := by
    rw [hrange]
    exact s1.1
  have hS : LargeEvenSStar p B x L := hctx.1.2.2.2.2.2.2.1
  have hD := hctx.2.2.1.1
  have hxD : x ∈ D := hD.2.2.2.1
  obtain ⟨T, hTx, hT2, hBT, hTB⟩ := hctx.1.2.2.2.2.2.2.2.2.1
  have hTN : T ≤ Subgroup.normalizer ((ψ.range : Subgroup G) : Set G) := by
    intro t ht
    rw [hrange]
    have hfus := (ggControlsStrongFusion_iff.mp s1.2.1).2 x hxD hS.2.2.1 t
    refine hfus ?_
    have htx : t⁻¹ * x * t = x := by
      have h1 := Subgroup.mem_centralizer_singleton_iff.mp (hTx ht)
      calc t⁻¹ * x * t = t⁻¹ * (x * t) := by group
        _ = t⁻¹ * (t * x) := by rw [h1]
        _ = x := by group
    rw [htx]
    exact s1.2.1.1 hxD
  have hB : ∀ b ∈ B, ∃ A : GL (Fin n) (GaloisField 2 (2 * (f + 1))),
      (b, A) ∈ UFusion.suInducedPairs ψ := by
    intro b hb
    have hbBs : b ∈ Bs := hctx.2.1.1 hb
    obtain ⟨A, hA, hAc⟩ := InnerDiagSU.suInnerDiagConj hF hn4 G ψ hker b⁻¹
      (hctx.2.2.2.2.2.2.1.2 b⁻¹ (Bs.inv_mem hbBs))
    refine ⟨A, hA, fun u => ?_⟩
    have := hAc u
    rwa [inv_inv] at this
  have hle := SURepair.commutator_le_range h hn4 hker hC hT2 hTN hBT hB
  have hTBT := SURepair.commutator_le_left_of_le_normalizer hBT
  refine ⟨T ⊓ ggG0 p B x L D J, inf_le_right, ?_, hT2.to_le inf_le_left, fun b hb => ?_⟩
  · intro hbot
    apply hTB
    rw [eq_bot_iff, ← hbot]
    exact le_inf hTBT (hrange ▸ hle)
  · have hbG : b ∈ Subgroup.normalizer (ggG0 p B x L D J : Set G) :=
      hctx.2.2.2.2.2.2.1.1 (hctx.2.1.1 hb)
    refine Subgroup.mem_normalizer_iff.mpr fun v => ⟨fun hv => ⟨?_, ?_⟩, fun hv => ⟨?_, ?_⟩⟩
    · exact (Subgroup.mem_normalizer_iff.mp (hBT hb) v).mp hv.1
    · exact (Subgroup.mem_normalizer_iff.mp hbG v).mp hv.2
    · exact (Subgroup.mem_normalizer_iff.mp (hBT hb) v).mpr hv.1
    · exact (Subgroup.mem_normalizer_iff.mp hbG v).mpr hv.2

theorem ggUnitaryBFramePairInput_holds : GGUnitaryBFramePairInput :=
  ggUnitaryBFramePairInput_of_twoLocal ggUnitaryBTwoLocalInput_holds

theorem ggUnitaryBstarCentralizerInput_holds : GGUnitaryBstarCentralizerInput :=
  ggUnitaryBstarCentralizerInput_of_twoLocal ggUnitaryBTwoLocalInput_holds

theorem ggStepTwoUnitaryFusionLargeInput_holds : GGStepTwoUnitaryFusionLargeInput :=
  ggStepTwoUnitaryFusionLargeInput_of_twoLocal ggUnitaryBTwoLocalInput_holds

theorem ggStepTwoUnitaryFusionRepairInput_holds :
    ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
      (n f : ℕ) (ψ : (ggU .PSU n f).K →* G),
      GGSixCtxV2 p B Bs x L D J (ggU .PSU n f).D .PSU n f ψ → GGSixStepOne p B Bs x L D J →
      p ∣ 2 ^ f + 1 → (2 ≤ f ∨ Bs ⊓ Subgroup.centralizer (J : Set G) ≤ D) →
        ∀ (b : G) (L₁ : Subgroup G), GGStepTwoPair p B Bs x L D J b L₁ →
          ∃ m ∈ Subgroup.normalizer (Bs : Set G), m⁻¹ * b * m ∈ D := by
  intro G _ _ p B Bs x L D J n f ψ hctx s1 hp hcase
  rcases hcase with hf | hDJ
  · exact ggStepTwoUnitaryFusionLargeInput_holds G p B Bs x L D J n f ψ hctx s1 hp hf
  · exact ggStepTwoUnitaryFusionEqInput_holds G p B Bs x L D J n f ψ hctx s1 hp hDJ

end Inputs

end CFSG.StandardType
