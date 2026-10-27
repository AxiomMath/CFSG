module

public import CFSG.LocalAnalysis.SectionRank.AmbientRank
public import CFSG.Quasithin.Recognition.Stroth.BenderDisplacement
public import CFSG.Quasithin.Recognition.Stroth.BenderJn
public import CFSG.Quasithin.Vol2.Ch5Sec1L34DSSz
public import CFSG.Adapters.QiuzhenLegacy.Glauberman.RelIndexSup
public import CFSG.Quasithin.H13.AS91Sec4Defs
public import CFSG.Quasithin.Recognition.GoldschmidtF112RLeaves
public import CFSG.Quasithin.Recognition.Stroth.BenderCaseIIFacts
public import CFSG.RankThree.GF2n.Tim81.Sec2.SzThreeGen

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R
open CFSG.LieType.BorelTits CFSG.RankThree.GF2n.Tim81.Sec2
open CFSG.QuasithinUnique.Setup.X7 CFSG.Quasithin.H13 CFSG.Quasithin.H13.AS91
open scoped Pointwise commutatorElement MatrixGroups

variable {G : Type} [Group G] [Finite G]
variable {L1 L2 S : Subgroup G} {a : ℕ}

theorem str83_partTwo_centralizer_sup_z1_eq_bot
    (hF : F112HypW L1 L2 S) (hB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (ha : 1 ≤ a) (hSz : Nonempty (oTwoQuot ↥L1 ≃* Sz a))
    (hL2 : IsL2Quot (2 * a + 1) (oTwoQuot ↥L2))
    (hZ2 : L2 ⊔ S ≤ Subgroup.centralizer (Z2 L1 L2 S : Set G)) :
    Z1 L1 L2 S ⊓ Subgroup.centralizer ((L1 ⊔ S : Subgroup G) : Set G) = ⊥ := by
  classical
  have hS1 : S = (S ⊓ L1) ⊔ Q1 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_left hF.1 hB (Or.inl ⟨a, ha, hSz⟩)
  have hS2 : S = (S ⊓ L2) ⊔ Q2 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_right hF.1 hB
      (Or.inr (Or.inr ⟨2 * a + 1, by omega, hL2⟩))
  have hQ1S : Q1 L1 L2 S ≤ S := by
    conv_rhs => rw [hS1]
    exact le_sup_right
  have hZ1Q1 : Z1 L1 L2 S ≤ Q1 L1 L2 S := omegaOneCenterOf_le _
  have hZ1S : Z1 L1 L2 S ≤ S := hZ1Q1.trans hQ1S
  have hZ1ea : IsElemAbelian 2 (Z1 L1 L2 S) :=
    SmithC27.isElemAbelian_omegaOneCenterOf (Q1 L1 L2 S)
  have hN : Q1 L1 L2 S ≤ Subgroup.normalizer ((S ⊓ L1 : Subgroup G) : Set G) := by
    intro q hq
    have hqS : q ∈ S := hQ1S hq
    have hqL1 : q ∈ Subgroup.normalizer (L1 : Set G) := hF.1.h1.normalizes hqS
    rw [Subgroup.mem_normalizer_iff] at hqL1 ⊢
    intro x
    constructor
    · intro hx
      exact ⟨S.mul_mem (S.mul_mem hqS hx.1) (S.inv_mem hqS), (hqL1 x).mp hx.2⟩
    · intro hx
      refine ⟨?_, (hqL1 x).mpr hx.2⟩
      have h1 : q⁻¹ * (q * x * q⁻¹) * q = x := by group
      rw [← h1]
      exact S.mul_mem (S.mul_mem (S.inv_mem hqS) hx.1) hqS
  rw [eq_bot_iff]
  intro z hz
  obtain ⟨hzZ1, hzC⟩ := Subgroup.mem_inf.mp hz
  have hzCS : z ∈ Subgroup.centralizer (S : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    obtain ⟨a₁, ha₁, q, hq, rfl⟩ :=
      (F1.mem_sup_iff_exists_mul_of_normalizes hN).mp (by rw [← hS1]; exact hs)
    have hza : a₁ * z = z * a₁ :=
      (Subgroup.mem_centralizer_iff.mp hzC) a₁ ((le_sup_left : L1 ≤ L1 ⊔ S) ha₁.2)
    have hzq : q * z = z * q :=
      (Subgroup.mem_centralizer_iff.mp (Z1_le_centralizer_Q1 L1 L2 S hzZ1)) q hq
    calc (a₁ * q) * z = a₁ * (q * z) := by group
      _ = a₁ * (z * q) := by rw [hzq]
      _ = (a₁ * z) * q := by group
      _ = (z * a₁) * q := by rw [hza]
      _ = z * (a₁ * q) := by group
  have hz2 : z ^ 2 = 1 := hZ1ea.2 z hzZ1
  have hzZ : z ∈ omegaOneCenterOf S := by
    rw [omegaOneCenterOf]
    exact Subgroup.subset_closure ⟨Subgroup.mem_inf.mpr ⟨hZ1S hzZ1, hzCS⟩, hz2⟩
  have hzZ2 : z ∈ Z2 L1 L2 S := (omegaOneCenterOf_S_le_caseII hF.1 hS1 hS2 hzZ).2
  have hzC1 : z ∈ Subgroup.centralizer (L1 : Set G) :=
    Subgroup.centralizer_le (le_sup_left : L1 ≤ L1 ⊔ S) hzC
  have hzC2 : z ∈ Subgroup.centralizer (L2 : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact ((Subgroup.mem_centralizer_iff.mp
      (hZ2 ((le_sup_left : L2 ≤ L2 ⊔ S) hl))) z hzZ2).symm
  have hzCG0 : z ∈ Subgroup.centralizer ((L1 ⊔ L2 ⊔ S : Subgroup G) : Set G) := by
    have h1 : Subgroup.zpowers z ≤ Subgroup.centralizer (L1 : Set G) :=
      Subgroup.zpowers_le.mpr hzC1
    have h2 : Subgroup.zpowers z ≤ Subgroup.centralizer (L2 : Set G) :=
      Subgroup.zpowers_le.mpr hzC2
    have h3 : Subgroup.zpowers z ≤ Subgroup.centralizer (S : Set G) :=
      Subgroup.zpowers_le.mpr hzCS
    have h12 : Subgroup.zpowers z ≤ Subgroup.centralizer ((L1 ⊔ L2 : Subgroup G) : Set G) :=
      CFSG.GorensteinWalter.le_centralizer_sup_of_le_centralizers h1 h2
    have h123 : Subgroup.zpowers z ≤
        Subgroup.centralizer ((L1 ⊔ L2 ⊔ S : Subgroup G) : Set G) :=
      CFSG.GorensteinWalter.le_centralizer_sup_of_le_centralizers h12 h3
    exact Subgroup.zpowers_le.mp h123
  have hzG0 : z ∈ L1 ⊔ L2 ⊔ S :=
    (le_sup_right : S ≤ L1 ⊔ L2 ⊔ S) (hZ1S hzZ1)
  have hconj : ∀ (u : G), u * z = z * u → ∀ k : ℤ, u * z ^ k * u⁻¹ = z ^ k := by
    intro u hu k
    have hu' : u * z * u⁻¹ = z := by rw [hu]; group
    calc u * z ^ k * u⁻¹ = (MulAut.conj u) (z ^ k) := rfl
      _ = ((MulAut.conj u) z) ^ k := map_zpow _ _ _
      _ = z ^ k := by rw [MulAut.conj_apply, hu']
  have hnorm : (L1 ⊔ L2 ⊔ S : Subgroup G) ≤
      Subgroup.normalizer (Subgroup.zpowers z : Set G) := by
    intro x hx
    have hxz : x * z = z * x := (Subgroup.mem_centralizer_iff.mp hzCG0) x hx
    have hxz' : x⁻¹ * z = z * x⁻¹ := by
      have h := congrArg (fun t => x⁻¹ * t * x⁻¹) hxz
      simpa [mul_assoc] using h.symm
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      rw [hconj x hxz k]
      exact Subgroup.zpow_mem_zpowers z k
    · intro hy
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hy
      have h1 : y = x⁻¹ * z ^ k * x := by
        rw [hk]
        group
      rw [h1, show x⁻¹ * z ^ k * x = z ^ k from by simpa using hconj x⁻¹ hxz' k]
      exact Subgroup.zpow_mem_zpowers z k
  have h2 : IsPGroup 2 (Subgroup.zpowers z) := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    by_cases hz1 : z = 1
    · rw [hz1, Subgroup.zpowers_one_eq_bot]
      exact IsPGroup.of_bot
    · refine IsPGroup.of_card (n := 1) ?_
      rw [Nat.card_zpowers, orderOf_eq_prime hz2 hz1, pow_one]
  have hzO : z ∈ pCoreOf 2 (L1 ⊔ L2 ⊔ S) :=
    le_pCoreOf_of_le_normalizer (Subgroup.zpowers_le.mpr hzG0) hnorm h2
      (Subgroup.mem_zpowers z)
  rw [hF.1.o2] at hzO
  simpa using hzO

theorem str83_partTwo_generator_data
    (hF : F112HypW L1 L2 S) (hB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (ha : 1 ≤ a) (hSz : Nonempty (oTwoQuot ↥L1 ≃* Sz a))
    (hL2 : IsL2Quot (2 * a + 1) (oTwoQuot ↥L2))
    (hII : ¬ L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G))
    (hJ : ¬ jAtLeast (2 ^ pRank 2 S) (2 ^ (2 * a + 1)) S ≤ Q1 L1 L2 S) :
    ∃ E X0 : Subgroup G,
      E ≤ S ∧ IsElemAbelian 2 E ∧ ¬ E ≤ Q1 L1 L2 S ∧
      Q1 L1 L2 S ≤ X0 ∧ X0 ≤ S ∧ E ⊔ Q1 L1 L2 S = X0 ∧
      (Q1 L1 L2 S).relIndex X0 = 2 ^ (2 * a + 1) ∧
      (Z1 L1 L2 S ⊓ Subgroup.centralizer (X0 : Set G)) =
        (Z1 L1 L2 S ⊓ Subgroup.centralizer (E : Set G)) ∧
      (Z1 L1 L2 S ⊓ Subgroup.centralizer (E : Set G)).relIndex (Z1 L1 L2 S) =
        (2 ^ (2 * a + 1)) ^ 2 := by
  classical
  obtain ⟨eSz⟩ := hSz
  have hS1 : S = (S ⊓ L1) ⊔ Q1 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_left hF.1 hB (Or.inl ⟨a, ha, ⟨eSz⟩⟩)
  have hsup1 : L1 ⊔ S = L1 ⊔ Q1 L1 L2 S := sup_eq_of_S_eq hS1
  have hpCore1 : pCoreOf 2 (L1 ⊔ S) = Q1 L1 L2 S := by
    rw [hsup1]
    exact pCoreOf_sup_pCoreOf hF.1
  have hSyl1 : IsSylowTwoOf S (L1 ⊔ S) := by
    rw [hsup1]
    exact isSylowTwoOf_sup_pCoreOf hF.1 hS1
  have hC : S ⊓ Subgroup.centralizer (Z1 L1 L2 S : Set G) = Q1 L1 L2 S :=
    inf_centralizer_z1_eq_q1_of_caseII hF hB (Or.inl ⟨a, ha, ⟨eSz⟩⟩) hII
  have hZ1ea : IsElemAbelian 2 (Z1 L1 L2 S) :=
    SmithC27.isElemAbelian_omegaOneCenterOf (Q1 L1 L2 S)
  have hQ1S : Q1 L1 L2 S ≤ S := by
    conv_rhs => rw [hS1]
    exact le_sup_right
  have hZ1S : Z1 L1 L2 S ≤ S := (omegaOneCenterOf_le _).trans hQ1S
  have hHZ1 : L1 ⊔ S ≤ Subgroup.normalizer (Z1 L1 L2 S : Set G) := by
    have hP1 : L1 ⊔ S ≤ P1 L1 L2 S :=
      sup_le le_sup_left ((le_sup_right : S ≤ bigB L1 L2 S).trans le_sup_right)
    exact hP1.trans ((le_normalizer_pCoreOf 2 (P1 L1 L2 S)).trans
      (A4.normalizer_le_normalizer_omegaOneCenterOf (Q1 L1 L2 S)))
  obtain ⟨E, hES, hEea, hmE, hEnotQ⟩ := exists_not_le_of_not_jAtLeast_le hJ
  have hpReq : CFSG.Open.pRank 2 (S : Subgroup G) = CFSG.pRank 2 ↥S :=
    (CFSG.SectionRank.pRank_coe_eq_openPRank 2 S).symm
  have hmE' : 2 ^ CFSG.Open.pRank 2 S ≤ 2 ^ (2 * a + 1) * Nat.card E := by
    rw [hpReq]
    exact hmE
  have hR := relIndex_centralizer_le_mul (S := S) (V := Z1 L1 L2 S) (F := E)
    (k := 2 ^ (2 * a + 1)) hZ1ea hZ1S hEea hES hmE'
  have hCE : E ⊓ Subgroup.centralizer (Z1 L1 L2 S : Set G) = E ⊓ Q1 L1 L2 S := by
    have h1 : E ⊓ S = E := le_antisymm inf_le_left (le_inf le_rfl hES)
    calc E ⊓ Subgroup.centralizer (Z1 L1 L2 S : Set G)
        = (E ⊓ S) ⊓ Subgroup.centralizer (Z1 L1 L2 S : Set G) := by rw [h1]
      _ = E ⊓ (S ⊓ Subgroup.centralizer (Z1 L1 L2 S : Set G)) := by rw [inf_assoc]
      _ = E ⊓ Q1 L1 L2 S := by rw [hC]
  have hszU3 : IsSzU3Quot (oTwoQuot ↥(L1 ⊔ S)) (2 ^ (2 * a + 1)) :=
    Or.inl ⟨a, ha, rfl, ⟨(oTwoQuotCongr (MulEquiv.subgroupCongr hsup1)).trans
      ((oTwoQuotSupEquiv hF.1).trans eSz)⟩⟩
  have hM5 : (E ⊓ Q1 L1 L2 S).relIndex E ≤ 2 ^ (2 * a + 1) := by
    have h := relIndex_inf_pCoreOf_le (L := L1 ⊔ S) (T := S) (A := E)
      (q := 2 ^ (2 * a + 1)) hszU3 hSyl1 hES (fun e he => ?_)
    · rwa [hpCore1] at h
    · rw [hEea.2 e he]
      exact (pCoreOf 2 (L1 ⊔ S)).one_mem
  have hupper : (Subgroup.centralizer (E : Set G)).relIndex (Z1 L1 L2 S) ≤
      (2 ^ (2 * a + 1)) ^ 2 := by
    have h1 : (Subgroup.centralizer (E : Set G)).relIndex (Z1 L1 L2 S) ≤
        2 ^ (2 * a + 1) *
          (Subgroup.centralizer (Z1 L1 L2 S : Set G)).relIndex E := hR
    have h2 : (Subgroup.centralizer (Z1 L1 L2 S : Set G)).relIndex E =
        (E ⊓ Q1 L1 L2 S).relIndex E := by
      rw [← hCE]
      exact (Subgroup.inf_relIndex_left E
        (Subgroup.centralizer (Z1 L1 L2 S : Set G))).symm
    rw [h2] at h1
    calc (Subgroup.centralizer (E : Set G)).relIndex (Z1 L1 L2 S)
        ≤ 2 ^ (2 * a + 1) * (E ⊓ Q1 L1 L2 S).relIndex E := h1
      _ ≤ 2 ^ (2 * a + 1) * 2 ^ (2 * a + 1) := Nat.mul_le_mul_left _ hM5
      _ = (2 ^ (2 * a + 1)) ^ 2 := (sq _).symm
  have hM7 : ∀ e ∈ E, e ∉ Q1 L1 L2 S →
      (2 ^ (2 * a + 1)) ^ 2 ≤
        (Z1 L1 L2 S ⊓ Subgroup.centralizer ({e} : Set G)).relIndex (Z1 L1 L2 S) := by
    intro e he heQ
    have hX : (∃ b : ℕ, 1 ≤ b ∧ 2 ^ (2 * a + 1) = 2 ^ (2 * b + 1) ∧
        Nonempty (oTwoQuot ↥(L1 ⊔ S) ≃* CFSG.Open.Sz b)) ∨
        (∃ n : ℕ, 2 ≤ n ∧ 2 ^ (2 * a + 1) = 2 ^ n ∧
          ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = (2 ^ n) ^ 2 ∧
            (Nonempty (oTwoQuot ↥(L1 ⊔ S) ≃* CFSG.Open.StatedSU 3 (2 ^ n) F) ∨
              Nonempty (oTwoQuot ↥(L1 ⊔ S) ≃*
                CFSG.Open.StatedProj (CFSG.Open.StatedSU 3 (2 ^ n) F)))) :=
      Or.inl ⟨a, ha, rfl, ⟨(oTwoQuotCongr (MulEquiv.subgroupCongr hsup1)).trans
        ((oTwoQuotSupEquiv hF.1).trans eSz)⟩⟩
    have hV : ∀ v ∈ Z1 L1 L2 S, v * v = 1 := by
      intro v hv
      have h := hZ1ea.2 v hv
      rwa [pow_two] at h
    have hHc : ¬ L1 ⊔ S ≤
        ((L1 ⊔ S) ⊓ Subgroup.centralizer (Z1 L1 L2 S : Set G)) ⊔
          pCoreOf 2 (L1 ⊔ S) := by
      rw [hpCore1]
      intro hle
      have hQ1C : Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G) :=
        Q1_le_centralizer_Z1 L1 L2 S
      have hHleC : L1 ⊔ S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G) :=
        hle.trans (sup_le inf_le_right hQ1C)
      exact hII (by rwa [hsup1] at hHleC)
    exact sq_le_relIndex_centralizer_of_sq_mem hX hV hHZ1 hHc
      ((le_sup_right : S ≤ L1 ⊔ S) (hES he))
      (by
        rw [hpCore1]
        have h := hEea.2 e he
        rw [pow_two] at h
        rw [h]
        exact (Q1 L1 L2 S).one_mem)
      (by rwa [hpCore1])
  have hlower : (2 ^ (2 * a + 1)) ^ 2 ≤
      (Subgroup.centralizer (E : Set G)).relIndex (Z1 L1 L2 S) := by
    obtain ⟨e, he, heQ⟩ : ∃ e ∈ E, e ∉ Q1 L1 L2 S := by
      by_contra hcon
      push Not at hcon
      exact hEnotQ hcon
    have h1 : Subgroup.centralizer (E : Set G) ≤
        Subgroup.centralizer ({e} : Set G) :=
      Subgroup.centralizer_le (by
        intro x hx
        rw [Set.mem_singleton_iff] at hx
        rw [hx]
        exact he)
    have h2 : (Z1 L1 L2 S ⊓ Subgroup.centralizer ({e} : Set G)).relIndex
        (Z1 L1 L2 S) ≤ (Subgroup.centralizer (E : Set G)).relIndex (Z1 L1 L2 S) := by
      rw [Subgroup.inf_relIndex_left]
      exact Subgroup.relIndex_le_of_le_left (L := Z1 L1 L2 S) h1
        (Subgroup.index_ne_zero_of_finite)
    exact (hM7 e he heQ).trans h2
  have hEq : (Subgroup.centralizer (E : Set G)).relIndex (Z1 L1 L2 S) =
      (2 ^ (2 * a + 1)) ^ 2 := le_antisymm hupper hlower
  have hIdx : (E ⊓ Q1 L1 L2 S).relIndex E = 2 ^ (2 * a + 1) := by
    have hqpos : 0 < 2 ^ (2 * a + 1) := Nat.pos_of_ne_zero (by positivity)
    have h2 : (Subgroup.centralizer (Z1 L1 L2 S : Set G)).relIndex E =
        (E ⊓ Q1 L1 L2 S).relIndex E := by
      rw [← hCE]
      exact (Subgroup.inf_relIndex_left E
        (Subgroup.centralizer (Z1 L1 L2 S : Set G))).symm
    have hchain : 2 ^ (2 * a + 1) * (E ⊓ Q1 L1 L2 S).relIndex E =
        (2 ^ (2 * a + 1)) ^ 2 := by
      apply le_antisymm
      · calc 2 ^ (2 * a + 1) * (E ⊓ Q1 L1 L2 S).relIndex E
            ≤ 2 ^ (2 * a + 1) * 2 ^ (2 * a + 1) := Nat.mul_le_mul_left _ hM5
          _ = (2 ^ (2 * a + 1)) ^ 2 := (sq _).symm
      · calc (2 ^ (2 * a + 1)) ^ 2
            = (Subgroup.centralizer (E : Set G)).relIndex (Z1 L1 L2 S) := hEq.symm
          _ ≤ 2 ^ (2 * a + 1) * (E ⊓ Q1 L1 L2 S).relIndex E := by
              have h := hR
              rwa [h2] at h
    have hsq : 2 ^ (2 * a + 1) * 2 ^ (2 * a + 1) =
        2 ^ (2 * a + 1) * (E ⊓ Q1 L1 L2 S).relIndex E := by
      rw [hchain, sq]
    exact Nat.eq_of_mul_eq_mul_left hqpos hsq.symm
  obtain ⟨X0, hX0mem, hQ1X0, hX0rel, -⟩ :=
    exists_X0 (q := 2 ^ (2 * a + 1)) hszU3 hSyl1
  have hX0S : X0 ≤ S := fun x hx => ((hX0mem x).mp hx).1
  have hQ1X0' : Q1 L1 L2 S ≤ X0 := by
    rwa [← hpCore1]
  have hX0rel' : (Q1 L1 L2 S).relIndex X0 = 2 ^ (2 * a + 1) := by
    rwa [← hpCore1]
  have hEX0 : E ≤ X0 := by
    intro e he
    rw [hX0mem e]
    refine ⟨hES he, ?_⟩
    rw [hEea.2 e he]
    exact (pCoreOf 2 (L1 ⊔ S)).one_mem
  have hsupX0 : E ⊔ Q1 L1 L2 S ≤ X0 := sup_le hEX0 hQ1X0'
  have hEN : E ≤ Subgroup.normalizer (Q1 L1 L2 S : Set G) := by
    intro e he
    exact (le_normalizer_pCoreOf 2 (P1 L1 L2 S))
      ((sup_le le_sup_left ((le_sup_right : S ≤ bigB L1 L2 S).trans le_sup_right))
        ((le_sup_right : S ≤ L1 ⊔ S) (hES he)))
  have hrelX0 : (Q1 L1 L2 S).relIndex (E ⊔ Q1 L1 L2 S) = 2 ^ (2 * a + 1) :=
    (CFSG.GroupTheory.relIndex_sup_eq_relIndex_inf_of_le_normalizer hEN).2.trans hIdx
  have hsupEq : E ⊔ Q1 L1 L2 S = X0 := by
    refine Subgroup.eq_of_le_of_card_ge hsupX0 ?_
    have hcard : Nat.card (E ⊔ Q1 L1 L2 S : Subgroup G) =
        Nat.card (X0 : Subgroup G) := by
      have h1 := Subgroup.relIndex_mul_card (Q1 L1 L2 S) (E ⊔ Q1 L1 L2 S)
      have h2 := Subgroup.relIndex_mul_card (Q1 L1 L2 S) X0
      have h1' : 2 ^ (2 * a + 1) *
          Nat.card ↥(Q1 L1 L2 S ⊓ (E ⊔ Q1 L1 L2 S) : Subgroup G) =
          Nat.card ↥(E ⊔ Q1 L1 L2 S : Subgroup G) := by
        simpa [hrelX0] using h1
      have h2' : 2 ^ (2 * a + 1) * Nat.card ↥(Q1 L1 L2 S ⊓ X0 : Subgroup G) =
          Nat.card ↥(X0 : Subgroup G) := by
        simpa [hX0rel'] using h2
      have hinf1 : Q1 L1 L2 S ⊓ (E ⊔ Q1 L1 L2 S) = Q1 L1 L2 S :=
        le_antisymm inf_le_left (le_inf le_rfl (le_sup_right :
          Q1 L1 L2 S ≤ E ⊔ Q1 L1 L2 S))
      have hinf2 : Q1 L1 L2 S ⊓ X0 = Q1 L1 L2 S :=
        le_antisymm inf_le_left (le_inf le_rfl hQ1X0')
      have h1'' : Nat.card ↥(E ⊔ Q1 L1 L2 S : Subgroup G) =
          2 ^ (2 * a + 1) * Nat.card ↥(Q1 L1 L2 S : Subgroup G) := by
        rw [hinf1] at h1'
        exact h1'.symm
      have h2'' : Nat.card ↥(X0 : Subgroup G) =
          2 ^ (2 * a + 1) * Nat.card ↥(Q1 L1 L2 S : Subgroup G) := by
        rw [hinf2] at h2'
        exact h2'.symm
      exact h1''.trans h2''.symm
    rwa [hcard]
  have hCX0 : Z1 L1 L2 S ⊓ Subgroup.centralizer (X0 : Set G) =
      Z1 L1 L2 S ⊓ Subgroup.centralizer (E : Set G) := by
    rw [← hsupEq]
    ext z
    simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
    constructor
    · rintro ⟨hz, hzX⟩
      exact ⟨hz, fun e he => hzX e (Subgroup.mem_sup_left he)⟩
    · rintro ⟨hz, hzE⟩
      refine ⟨hz, fun x hx => ?_⟩
      have hx' : x ∈ (Q1 L1 L2 S ⊔ E : Subgroup G) := by
        rwa [sup_comm]
      rcases (F1.mem_sup_iff_exists_mul_of_normalizes
        (H := Q1 L1 L2 S) (K := E) hEN).mp hx' with ⟨q, hqQ, y, hyE, rfl⟩
      have hzy : y * z = z * y := hzE y hyE
      have hzq : q * z = z * q :=
        Subgroup.mem_centralizer_iff.mp (Z1_le_centralizer_Q1 L1 L2 S hz) q hqQ
      calc (q * y) * z = q * (y * z) := by group
        _ = q * (z * y) := by rw [hzy]
        _ = (q * z) * y := by group
        _ = (z * q) * y := by rw [hzq]
        _ = z * (q * y) := by group
  have hEq' : (Z1 L1 L2 S ⊓ Subgroup.centralizer (E : Set G)).relIndex
      (Z1 L1 L2 S) = (2 ^ (2 * a + 1)) ^ 2 := by
    rw [Subgroup.inf_relIndex_left (Z1 L1 L2 S) (Subgroup.centralizer (E : Set G))]
    exact hEq
  exact ⟨E, X0, hES, hEea, hEnotQ, hQ1X0', hX0S, hsupEq, hX0rel', hCX0, hEq'⟩

end CFSG.Quasithin.Stroth

end
