module

public import CFSG.RankThree.PartTwo.Sec15.SimsBaumannCases
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CharacteristicPrimeInheritance
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.SubnormalPrimeCores

public section

namespace CFSG.RankThree.PartTwo.Sec15.SimsBaumann

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.GH74.GLS
open scoped Pointwise

variable {X : Type} [Group X] [Finite X]

private instance sbBasic_normal_oResidual (Y : Type) [Group Y] : (oResidual 2 Y).Normal := by
  refine ⟨fun n hn g => ?_⟩
  unfold oResidual at hn ⊢
  have key : Subgroup.map (MulAut.conj g).toMonoidHom
      (Subgroup.closure {x : Y | Nat.Coprime (orderOf x) 2}) ≤
      Subgroup.closure {x : Y | Nat.Coprime (orderOf x) 2} := by
    rw [MonoidHom.map_closure]
    apply Subgroup.closure_mono
    rintro _ ⟨x, hx, rfl⟩
    show Nat.Coprime (orderOf (MulAut.conj g x)) 2
    rwa [MulEquiv.orderOf_eq]
  exact key ⟨n, hn, rfl⟩

private theorem sbBasic_exists_pow_mem_oResidual (x : X) :
    ∃ k : ℕ, x ^ 2 ^ k ∈ oResidual 2 X := by
  obtain ⟨k, m, hm, hn⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x).ne'
  refine ⟨k, Subgroup.subset_closure ?_⟩
  show Nat.Coprime (orderOf (x ^ 2 ^ k)) 2
  rw [orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero) ⟨m, hn⟩, hn,
    Nat.mul_div_cancel_left _ (by positivity)]
  exact hm.coprime_two_right

private theorem sbBasic_isPGroup_quotient : IsPGroup 2 (X ⧸ oResidual 2 X) := by
  intro g
  induction g using QuotientGroup.induction_on with
  | H x =>
    obtain ⟨k, hk⟩ := sbBasic_exists_pow_mem_oResidual x
    exact ⟨k, by rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]; exact hk⟩

private theorem sbBasic_index_oResidual : ∃ n : ℕ, (oResidual 2 X).index = 2 ^ n := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact IsPGroup.iff_card.mp (sbBasic_isPGroup_quotient (X := X))

private theorem sbBasic_isCharacteristicP (hF : generalizedFitting X = CFSG.pCore 2 X) :
    IsCharacteristicP 2 X := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact (isCharacteristicP_iff_generalizedFitting_eq_pCore X 2).mpr hF

theorem charTwo_top_of_hF (hF : generalizedFitting X = CFSG.pCore 2 X) :
    CFSG.QuasithinUnique.CharTwo (⊤ : Subgroup X) := by
  have hchar := sbBasic_isCharacteristicP hF
  intro x hx
  rw [CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_top_eq_pCore] at hx ⊢
  exact hchar hx.2

theorem pCoreOf_top_le {S : Subgroup X} (h : CFSG.pCore 2 X ≤ S) :
    CFSG.Open.pCoreOf 2 (⊤ : Subgroup X) ≤ S := by
  rwa [CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_top_eq_pCore]

theorem exists_sylow_le {S : Subgroup X} (hS2 : IsPGroup 2 S) :
    ∃ T : Subgroup X, CFSG.QuasithinUnique.IsSylowTwoOf T ⊤ ∧ S ≤ T := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := hS2.exists_le_sylow
  refine ⟨P, ⟨le_top, P.isPGroup', ?_⟩, hP⟩
  have h := P.not_dvd_index
  change ¬ 2 ∣ (P : Subgroup X).relIndex ⊤
  rwa [Subgroup.relIndex_top_right]

theorem top_eq_mul_of_sylow {T : Subgroup X} (hT : CFSG.QuasithinUnique.IsSylowTwoOf T ⊤) :
    ((⊤ : Subgroup X) : Set X) = (oResidual 2 X : Set X) * (T : Set X) := by
  obtain ⟨n, hn⟩ := sbBasic_index_oResidual (X := X)
  have hTodd : ¬ 2 ∣ T.index := by
    have h := hT.2.2
    change ¬ 2 ∣ T.relIndex ⊤ at h
    rwa [Subgroup.relIndex_top_right] at h
  have hd1 : (oResidual 2 X ⊔ T).index ∣ 2 ^ n :=
    hn ▸ Subgroup.index_dvd_of_le (le_sup_left : oResidual 2 X ≤ oResidual 2 X ⊔ T)
  have hd2 : (oResidual 2 X ⊔ T).index ∣ T.index :=
    Subgroup.index_dvd_of_le (le_sup_right : T ≤ oResidual 2 X ⊔ T)
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd1
  have hj0 : j = 0 := by
    by_contra hj0
    exact hTodd (((dvd_pow_self 2 hj0).trans (hj ▸ dvd_rfl)).trans hd2)
  have htop : oResidual 2 X ⊔ T = ⊤ := by
    rw [← Subgroup.index_eq_one, hj, hj0, pow_zero]
  rw [← Subgroup.normal_mul, htop]

theorem charTwo_oResidual (hF : generalizedFitting X = CFSG.pCore 2 X) :
    CFSG.QuasithinUnique.CharTwo (oResidual 2 X) := by
  have hint := CFSG.RankThreeCoreUniqueness.Helpers.normal_subgroup_self_centralizing_pCore
    2 Nat.prime_two (sbBasic_isCharacteristicP hF) (oResidual 2 X) inferInstance
  rintro x ⟨hxL, hxC⟩
  have hx : (⟨x, hxL⟩ : ↥(oResidual 2 X)) ∈ pCore 2 (oResidual 2 X) := by
    apply hint
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hxC (c : X) (Subgroup.mem_map_of_mem _ hc))
  exact ⟨_, hx, rfl⟩

private theorem sbBasic_W_le_centralizer :
    W315 X ≤ Subgroup.centralizer (CFSG.pCore 2 X : Set X) := by
  unfold W315 CFSG.Quasithin.omegaOneCenterOf CFSG.Quasithin.omegaOneOf
  rw [Subgroup.closure_le]
  exact fun x hx => hx.1.2

private theorem sbBasic_conjAct_apply (V : Subgroup X) (g : Subgroup.normalizer (V : Set X))
    (v : V) : ((CFSG.Quasithin.conjAct V g v : V) : X) = (g : X) * v * (g : X)⁻¹ := rfl

theorem autOn_le_of_le_sup {S : Subgroup X} (hS : S ≤ oResidual 2 X ⊔ CFSG.pCore 2 X) :
    CFSG.Quasithin.autOn S (W315 X) ≤ CFSG.Quasithin.autOn (oResidual 2 X) (W315 X) := by
  rintro φ ⟨⟨s, hsN⟩, hsS, rfl⟩
  have hsLQ : s ∈ ((oResidual 2 X ⊔ CFSG.pCore 2 X : Subgroup X) : Set X) := hS hsS
  rw [Subgroup.normal_mul] at hsLQ
  obtain ⟨l, hl, q, hq, hs⟩ := hsLQ
  have hs' : l * q = s := hs
  subst hs'
  have hqW : ∀ w ∈ W315 X, q * w * q⁻¹ = w := fun w hw => by
    rw [mul_inv_eq_iff_eq_mul]
    exact (Subgroup.mem_centralizer_iff.mp (sbBasic_W_le_centralizer hw) q hq)
  have hqC : q ∈ Subgroup.centralizer (W315 X : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact (Subgroup.mem_centralizer_iff.mp (sbBasic_W_le_centralizer hw) q hq).symm
  have hqN : q ∈ Subgroup.normalizer (W315 X : Set X) :=
    Subgroup.centralizer_le_normalizer (W315 X : Set X) hqC
  have hlN : l ∈ Subgroup.normalizer (W315 X : Set X) := by
    have := Subgroup.mul_mem _ hsN (Subgroup.inv_mem _ hqN)
    simpa using this
  refine ⟨⟨l, hlN⟩, hl, ?_⟩
  ext w
  rw [sbBasic_conjAct_apply, sbBasic_conjAct_apply]
  have := hqW w w.2
  calc l * (w : X) * l⁻¹ = l * (q * w * q⁻¹) * l⁻¹ := by rw [this]
    _ = (l * q) * w * (l * q)⁻¹ := by group

end CFSG.RankThree.PartTwo.Sec15.SimsBaumann
