module

public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsSp
public import CFSG.LocalAnalysis.StandardType.GGLinearTorusCompSU

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank Matrix CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.SectionRank.OddCover CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits InnerDiagSU CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.RankThree.PartOne.KCUnitaryModel
open scoped commutatorElement

@[expose] def GGSUCentralizerCoreInput : Prop :=
  ∀ (K : Type) [Field K] (f : ℕ), UnitaryFieldData 2 f K → ∀ n : ℕ, 4 ≤ n →
    ∀ A : Subgroup (GL (Fin n) K), (Nat.card A : K) ≠ 0 →
      A ≤ Subgroup.normalizer (unitarySU 2 f K n : Set (GL (Fin n) K)) →
      ∃ (β : Type) (S : β → Subgroup ↥(unitarySU 2 f K n)),
        (∀ b, S b ≤ (Subgroup.centralizer (A : Set (GL (Fin n) K))).comap
          (unitarySU 2 f K n).subtype) ∧
        (∀ b, ∀ c ∈ (Subgroup.centralizer (A : Set (GL (Fin n) K))).comap
          (unitarySU 2 f K n).subtype, ∀ s ∈ S b, c * s * c⁻¹ ∈ S b) ∧
        (∀ b, CFSG.IsQuasisimple (S b)) ∧
        (∃ k, LayerFacts.ggDer ((Subgroup.centralizer (A : Set (GL (Fin n) K))).comap
          (unitarySU 2 f K n).subtype) k ≤ ⨆ b, S b) ∧
        ∀ z ∈ ⨆ b, S b, (∀ y ∈ ⨆ b, S b, z * y = y * z) → z ^ 2 = 1 → z = 1

namespace LayerFacts

section Lift

variable {K : Type} [Field K] {f n : ℕ} {G : Type*} [Group G]
  {ψ : ↥(unitarySU 2 f K n) →* G} {E : Subgroup G}

variable (ψ E) in
@[expose] def ggSUCent : Subgroup ↥(unitarySU 2 f K n) :=
  (Subgroup.centralizer (SUTorus.inducedMatrices ψ E : Set (GL (Fin n) K))).comap
    (unitarySU 2 f K n).subtype

theorem mem_ggSUCent {u : ↥(unitarySU 2 f K n)} :
    u ∈ ggSUCent ψ E ↔ ∀ B ∈ SUTorus.inducedMatrices ψ E, B * u = u * B := by
  simp only [ggSUCent, Subgroup.mem_comap, Subgroup.coe_subtype, Subgroup.mem_centralizer_iff,
    SetLike.mem_coe]

theorem conj_eq_mul_of_mem_centralizer_su
    (hker : ψ.ker ≤ Subgroup.center ↥(unitarySU 2 f K n)) {u : ↥(unitarySU 2 f K n)}
    (hu : ψ u ∈ Subgroup.centralizer (E : Set G)) {B : GL (Fin n) K}
    (hB : B ∈ SUTorus.inducedMatrices ψ E) :
    ∃ z ∈ Subgroup.center ↥(unitarySU 2 f K n),
      B * (u : GL (Fin n) K) * B⁻¹ = ((z * u : ↥(unitarySU 2 f K n)) : GL (Fin n) K) := by
  obtain ⟨e, he, hpair⟩ := SUTorus.mem_inducedMatrices.mp hB
  let v : ↥(unitarySU 2 f K n) :=
    ⟨B * u * B⁻¹, (Subgroup.mem_normalizer_iff.mp hpair.1 u).mp u.2⟩
  have h1 := hpair.2 u v rfl
  have h2 : e * ψ u = ψ u * e := Subgroup.mem_centralizer_iff.mp hu e he
  refine ⟨v * u⁻¹, hker ?_, by simp [v]⟩
  rw [MonoidHom.mem_ker, map_mul, map_inv, ← h1, h2, mul_inv_cancel_right, mul_inv_cancel]

theorem map_ggSUCent_le (hEA : ∀ e ∈ E, ∃ B, (e, B) ∈ SUTorus.suPairs ψ) :
    (ggSUCent ψ E).map ψ ≤ ψ.range ⊓ Subgroup.centralizer (E : Set G) := by
  rintro _ ⟨c, hc, rfl⟩
  refine Subgroup.mem_inf.mpr ⟨⟨c, rfl⟩, Subgroup.mem_centralizer_iff.mpr fun e he => ?_⟩
  obtain ⟨B, hB⟩ := hEA e he
  have hBc := mem_ggSUCent.mp hc B (SUTorus.mem_inducedMatrices.mpr ⟨e, he, hB⟩)
  have h1 := hB.2 c c (by rw [hBc, mul_inv_cancel_right])
  calc e * ψ c = e * ψ c * e⁻¹ * e := by group
    _ = ψ c * e := by rw [h1]

theorem commutator_le_map_ggSUCent (hker : ψ.ker ≤ Subgroup.center ↥(unitarySU 2 f K n)) :
    ⁅ψ.range ⊓ Subgroup.centralizer (E : Set G), ψ.range ⊓ Subgroup.centralizer (E : Set G)⁆ ≤
      (ggSUCent ψ E).map ψ := by
  rw [Subgroup.commutator_le]
  rintro x hx y hy
  obtain ⟨⟨u, rfl⟩, hu⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨⟨v, rfl⟩, hv⟩ := Subgroup.mem_inf.mp hy
  refine ⟨⁅u, v⁆, mem_ggSUCent.mpr fun B hB => ?_, map_commutatorElement ψ u v⟩
  obtain ⟨z, hz, hzu⟩ := conj_eq_mul_of_mem_centralizer_su hker hu hB
  obtain ⟨w, hw, hwv⟩ := conj_eq_mul_of_mem_centralizer_su hker hv hB
  have hc : B * ((⁅u, v⁆ : ↥(unitarySU 2 f K n)) : GL (Fin n) K) * B⁻¹ =
      ((⁅u, v⁆ : ↥(unitarySU 2 f K n)) : GL (Fin n) K) := by
    have e1 : B * ((⁅u, v⁆ : ↥(unitarySU 2 f K n)) : GL (Fin n) K) * B⁻¹ =
        ⁅B * (u : GL (Fin n) K) * B⁻¹, B * (v : GL (Fin n) K) * B⁻¹⁆ := by
      simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]
      group
    have e2 : ⁅((z * u : ↥(unitarySU 2 f K n)) : GL (Fin n) K),
        ((w * v : ↥(unitarySU 2 f K n)) : GL (Fin n) K)⁆ =
        ((⁅z * u, w * v⁆ : ↥(unitarySU 2 f K n)) : GL (Fin n) K) := by
      simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [e1, hzu, hwv, e2, ggCommutatorElement_center_mul hz hw]
  calc B * ((⁅u, v⁆ : ↥(unitarySU 2 f K n)) : GL (Fin n) K)
      = B * ((⁅u, v⁆ : ↥(unitarySU 2 f K n)) : GL (Fin n) K) * B⁻¹ * B := by group
    _ = _ := by rw [hc]

theorem normal_map_ggSUCent (hker : ψ.ker ≤ Subgroup.center ↥(unitarySU 2 f K n)) :
    (((ggSUCent ψ E).map ψ).subgroupOf (ψ.range ⊓ Subgroup.centralizer (E : Set G))).Normal := by
  constructor
  intro x hx h
  rw [Subgroup.mem_subgroupOf] at hx ⊢
  obtain ⟨c, hc, hcx⟩ := hx
  obtain ⟨⟨v, hv⟩, hvc⟩ := Subgroup.mem_inf.mp h.2
  refine ⟨v * c * v⁻¹, mem_ggSUCent.mpr fun B hB => ?_, ?_⟩
  · obtain ⟨z, hz, hzv⟩ := conj_eq_mul_of_mem_centralizer_su hker (hv ▸ hvc) hB
    have hzc : ∀ g : ↥(unitarySU 2 f K n), z * g = g * z := fun g =>
      (Subgroup.mem_center_iff.mp hz g).symm
    have hBc := mem_ggSUCent.mp hc B hB
    have hcB : B * (c : GL (Fin n) K) * B⁻¹ = c := by rw [hBc, mul_inv_cancel_right]
    have key : B * ((v * c * v⁻¹ : ↥(unitarySU 2 f K n)) : GL (Fin n) K) * B⁻¹ =
        ((v * c * v⁻¹ : ↥(unitarySU 2 f K n)) : GL (Fin n) K) := by
      have e1 : B * ((v * c * v⁻¹ : ↥(unitarySU 2 f K n)) : GL (Fin n) K) * B⁻¹ =
          (B * (v : GL (Fin n) K) * B⁻¹) * (B * (c : GL (Fin n) K) * B⁻¹) *
            (B * (v : GL (Fin n) K) * B⁻¹)⁻¹ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group
      rw [e1, hzv, hcB]
      have e2 : z * v * c * (z * v)⁻¹ = v * c * v⁻¹ := by
        calc z * v * c * (z * v)⁻¹ = z * (v * c * v⁻¹) * z⁻¹ := by group
          _ = v * c * v⁻¹ := by rw [hzc, mul_inv_cancel_right]
      rw [← Subgroup.coe_mul, ← Subgroup.coe_inv, ← Subgroup.coe_mul, e2]
    calc B * ((v * c * v⁻¹ : ↥(unitarySU 2 f K n)) : GL (Fin n) K)
        = B * ((v * c * v⁻¹ : ↥(unitarySU 2 f K n)) : GL (Fin n) K) * B⁻¹ * B := by group
      _ = _ := by rw [key]
  · simp only [map_mul, map_inv, hcx, hv, Subgroup.coe_mul, Subgroup.coe_inv]

end Lift

section SU

variable {G : Type} [Group G]

theorem ggLayer_su_field (hcore : GGSUCentralizerCoreInput) {F : Type} [Field F] [Finite F] [CharP F 2]
    {f m : ℕ} (h : UnitaryFieldData 2 f F) (hF : Nat.card F = (2 ^ f) ^ 2) (hn : 4 ≤ m + 1)
    {ψ : SU (unitaryInvolution F 2 f) (m + 1) →* G}
    (hker : ψ.ker ≤ Subgroup.center (SU (unitaryInvolution F 2 f) (m + 1)))
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {E : Subgroup G} (hE : IsPGroup p E)
    (hdiag : ∀ e ∈ E, GGPsiInnerDiag (Unitary.rootDatum hF (m + 1)) ψ e) :
    Odd (Nat.card (Subgroup.center
        ↥(LargeEvenLayer (ψ.range ⊓ Subgroup.centralizer (E : Set G))))) ∧
      ∀ X : Subgroup G, X ≤ ψ.range ⊓ Subgroup.centralizer (E : Set G) → ⁅X, X⁆ = X →
        X ≤ LargeEvenLayer (ψ.range ⊓ Subgroup.centralizer (E : Set G)) := by
  classical
  obtain ⟨P, hP⟩ := exists_wittMatrix hF (m + 1)
  have hSU : SUid (unitaryInvolution F 2 f) (m + 1) =
      unitarySU 2 f F (m + 1) := SUid_eq_statedSU hF (m + 1)
  set Φ := (conjEquiv P hP).trans (MulEquiv.subgroupCongr hSU) with hΦ
  set ψ₁ := ψ.comp Φ.symm.toMonoidHom with hψ₁
  have hr₁ : ψ₁.range = ψ.range := SUTorus.range_comp_symm ψ Φ
  have hker₁ : ψ₁.ker ≤ Subgroup.center ↥(unitarySU 2 f F (m + 1)) :=
    SUTorus.ker_comp_symm_le hker Φ
  have hEA : ∀ e ∈ E, ∃ B, (e, B) ∈ SUTorus.suPairs ψ₁ := by
    intro e he
    obtain ⟨A, hA, hAc⟩ := suInnerDiagConj hF hn G ψ hker e⁻¹ (hdiag e⁻¹ (E.inv_mem he))
    refine ⟨P * A * P⁻¹, SUTorus.mem_suPairs_transfer P hP hSU hA fun u => ?_⟩
    have := hAc u
    rwa [inv_inv] at this
  obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd
    (show 2 ^ f + 1 ≠ 1 by have := Nat.one_le_two_pow (n := f); omega)
  have hn3 : 3 ≤ m + 1 := by omega
  have hnq : (m + 1, 2 ^ f) ≠ (3, 2) := fun h' => by
    have := congrArg Prod.fst h'
    simp only at this
    omega
  have hodd : (Nat.card (SUTorus.inducedMatrices ψ₁ E) : F) ≠ 0 := by
    intro h0
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 ((CharP.cast_eq_zero_iff _ 2 _).mp h0)
    obtain ⟨e, he, hpair⟩ := SUTorus.mem_inducedMatrices.mp x.2
    obtain ⟨k, hk⟩ := hE ⟨e, he⟩
    have hek : e ^ (p ^ k) = 1 := by simpa using congrArg Subtype.val hk
    have h1 := (SUTorus.suPairs ψ₁).pow_mem hpair (p ^ k)
    rw [Prod.pow_mk, hek] at h1
    obtain ⟨c, hc⟩ := SUTorus.exists_scalar_of_mem_suPairs_one h hn3 hnq hq hqd hker₁ h1
    have hx2 : (x : GL (Fin (m + 1)) F) ^ 2 = 1 := by
      have := pow_orderOf_eq_one x
      rw [hx] at this
      simpa using congrArg Subtype.val this
    obtain ⟨j, hj⟩ := (hp.odd_of_ne_two hp2).pow (n := k)
    have hxx : (x : GL (Fin (m + 1)) F) ^ (p ^ k) = x := by
      rw [hj, pow_succ, pow_mul, hx2, one_pow, one_mul]
    rw [hxx] at hc
    rw [hc] at hx2
    have hx1 : x = 1 := Subtype.ext (by simp [hc, eq_one_of_scalar_sq_eq_one hx2])
    rw [hx1, orderOf_one] at hx
    exact absurd hx (by norm_num)
  have hnorm : SUTorus.inducedMatrices ψ₁ E ≤
      Subgroup.normalizer (unitarySU 2 f F (m + 1) : Set (GL (Fin (m + 1)) F)) := by
    intro B hB
    obtain ⟨e, -, hpair⟩ := SUTorus.mem_inducedMatrices.mp hB
    exact hpair.1
  obtain ⟨β, S, hSC, hSn, hSq, hder, hZ⟩ := hcore F f h (m + 1) hn _ hodd hnorm
  rw [← hr₁]
  exact (ggLayer_of_core ψ₁ hker₁ (map_ggSUCent_le hEA) (normal_map_ggSUCent hker₁)
    (commutator_le_map_ggSUCent hker₁) S hSC hSn hSq hder hZ).2

theorem ggLayer_su (hcore : GGSUCentralizerCoreInput) {f m : ℕ} (hf : 1 ≤ f) (hn : 4 ≤ m + 1)
    {ψ : SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) (m + 1) →* G}
    (hker : ψ.ker ≤ Subgroup.center (SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) (m + 1)))
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {E : Subgroup G} (hE : IsPGroup p E)
    (hdiag : ∀ e ∈ E,
      GGPsiInnerDiag (Unitary.rootDatum (card_galoisField_two_mul 2 f hf) (m + 1)) ψ e) :
    Odd (Nat.card (Subgroup.center
        ↥(LargeEvenLayer (ψ.range ⊓ Subgroup.centralizer (E : Set G))))) ∧
      ∀ X : Subgroup G, X ≤ ψ.range ⊓ Subgroup.centralizer (E : Set G) → ⁅X, X⁆ = X →
        X ≤ LargeEvenLayer (ψ.range ⊓ Subgroup.centralizer (E : Set G)) := by
  classical
  have hF : Nat.card (GaloisField 2 (2 * f)) = (2 ^ f) ^ 2 := card_galoisField_two_mul 2 f hf
  have h : UnitaryFieldData 2 f (GaloisField 2 (2 * f)) :=
    ⟨Nat.prime_two, hf, by rw [hF, ← pow_mul, mul_comm]⟩
  exact ggLayer_su_field hcore h hF hn hker hp hp2 hE hdiag

end SU

end LayerFacts

section Tags

theorem ggLayerTags_PSU_of_core (hcore : GGSUCentralizerCoreInput) :
    GGLayerCentreOddTag .PSU ∧ GGLayerPerfectTag .PSU := by
  constructor <;>
  · intro G _ _ n f
    by_cases hf : 1 ≤ f
    · have hU : ggU .PSU n f =
          ⟨Unitary.SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) n,
            Unitary.rootDatum (card_galoisField_two_mul 2 f hf) n⟩ := by
        simp only [ggU, lieUniversal, hf, ↓reduceDIte]
      rw [hU]
      intro ψ G₀ hpres _ p hp hp2 E hE _ _ hdiag
      obtain ⟨⟨-, hrk⟩, ⟨hrange, hker⟩, -, -⟩ := hpres
      have hn : 4 ≤ n := by
        have : 2 ≤ n / 2 := hrk
        omega
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      rw [← hrange]
      first
      | exact (LayerFacts.ggLayer_su hcore hf hn hker hp hp2 hE hdiag).1
      | exact (LayerFacts.ggLayer_su hcore hf hn hker hp hp2 hE hdiag).2
    · intro ψ G₀ hpres
      exact absurd hpres.1.1.2.1 hf

theorem ggLayerInputs_of_remaining_cores (hSU : GGSUCentralizerCoreInput)
    (hSp : GGSpCentralizerCoreInput)
    (hPlus : GGLayerCentreOddTag .POmegaPlus ∧ GGLayerPerfectTag .POmegaPlus)
    (hMinus : GGLayerCentreOddTag .POmegaMinus ∧ GGLayerPerfectTag .POmegaMinus)
    (hF4 : GGLayerCentreOddTag .F4 ∧ GGLayerPerfectTag .F4)
    (hE6 : GGLayerCentreOddTag .E6 ∧ GGLayerPerfectTag .E6)
    (hE7 : GGLayerCentreOddTag .E7 ∧ GGLayerPerfectTag .E7)
    (hE8 : GGLayerCentreOddTag .E8 ∧ GGLayerPerfectTag .E8)
    (hTwE6 : GGLayerCentreOddTag .twistedE6 ∧ GGLayerPerfectTag .twistedE6) :
    GGLayerCentreOddInput ∧ GGLayerPerfectInput :=
  ggLayerInputs_of_remaining (ggLayerTags_PSU_of_core hSU) (ggLayerTags_PSp_of_core hSp) hPlus
    hMinus hF4 hE6 hE7 hE8 hTwE6

end Tags

end CFSG.StandardType
