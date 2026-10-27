module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10EndPhi
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10EndSylow
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10EndFStar
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10EndAFour
import CFSG.ClassicalInvolution.Q3.Q3TLTLayer

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3

open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)

variable {G : Type} [Group G] [Finite G] {D : Data G}

namespace Ctx82E3.A10Frame

open CFSG.GH74.Uniqueness.SU.SU13.TA.L10
open scoped commutatorElement

variable {c : Ctx82E3 D}

private theorem A_le_centralizer (F : A10Frame c) {B : Subgroup G} (hBA : B ≤ F.A) :
    F.A ≤ Subgroup.centralizer (B : Set G) := by
  haveI : IsMulCommutative ↥F.A := F.elemAbelian.1
  intro a haA
  rw [Subgroup.mem_centralizer_iff]
  intro b hbB
  exact congrArg Subtype.val ((IsMulCommutative.is_comm (M := ↥F.A)).comm
    ⟨b, hBA hbB⟩ ⟨a, haA⟩)

private theorem exists_mem_A_deg_three (F : A10Frame c) {x : Equiv.Perm (Fin 10)}
    (hx : x ∈ A10Perm.atilde) (hx3 : x.support.card = 3) :
    ∃ (e : G) (he : e ∈ F.A), F.deg (Subgroup.zpowers e) = 3 ∧
      F.phiA ⟨e, F.A_le_M he⟩ = x := by
  have hx' : x ∈ (F.A.subgroupOf D.M).map F.phiA := by
    rw [F.map_A_phiA]
    exact hx
  obtain ⟨⟨e, heM⟩, heA, heeq⟩ := Subgroup.mem_map.mp hx'
  refine ⟨e, heA, ?_, ?_⟩
  · have hdeg := F.deg_zpowers_eq (b := e) (F.P_le_L (F.A_le heA))
    rw [hdeg]
    have hsupp : (F.phiA ⟨e, heM⟩).support.card = 3 := by rw [heeq, hx3]
    simpa [Subtype.ext_iff] using hsupp
  · show F.phiA ⟨e, F.A_le_M heA⟩ = x
    rw [show (⟨e, F.A_le_M heA⟩ : ↥D.M) = ⟨e, heM⟩ from rfl]
    exact heeq

private theorem phiA_eq_one_on_A (F : A10Frame c) {x : ↥D.M}
    (hx : x ∈ F.A.subgroupOf D.M) (hx1 : F.phiA x = 1) : x = 1 := by
  have hmemker : x ∈ F.phiA.ker := hx1
  have hn : orderOf x ∣ Nat.card F.phiA.ker := by
    have h := orderOf_dvd_natCard (⟨x, hmemker⟩ : ↥F.phiA.ker)
    have h2 : orderOf (⟨x, hmemker⟩ : ↥F.phiA.ker) = orderOf x := by
      rw [← Subgroup.orderOf_coe (a := (⟨x, hmemker⟩ : ↥F.phiA.ker))]
    rwa [h2] at h
  have h3 : x ^ 3 = 1 := by
    apply Subtype.ext
    simpa using F.elemAbelian.2 (x : G) (Subgroup.mem_subgroupOf.mp hx)
  have hord : orderOf x = 1 :=
    Nat.eq_one_of_dvd_coprimes F.coprime_card_ker_phiA.symm
      (orderOf_dvd_of_pow_eq_one h3) hn
  exact orderOf_eq_one_iff.mp hord

private theorem le_centralizer_pCoreOf_three (F : A10Frame c) (hF : A10Facts F)
    {V : Subgroup G} (hV : UC22.InCalV D.M V) {B : Subgroup G} (hBA : B ≤ F.A)
    (hO : CFSG.Open.pCoreOf 2 (Subgroup.centralizer (B : Set G)) = ⊥)
    {e : G} (heA : e ∈ F.A) :
    ⁅V ⊓ Subgroup.centralizer (B : Set G), Subgroup.zpowers e⁆ ≤
      Subgroup.centralizer
        (CFSG.Open.pCoreOf 3 (Subgroup.centralizer (B : Set G)) : Set G) := by
  classical
  let H : Subgroup G := Subgroup.centralizer (B : Set G)
  let W₀ : Subgroup G := V ⊓ H
  have hO' : CFSG.Open.pCoreOf 2 H = ⊥ := hO
  have hAH : F.A ≤ H := A_le_centralizer F hBA
  have hAV : F.A ≤ Subgroup.normalizer (V : Set G) := F.A_le_M.trans hV.2.2.1
  have hAW : F.A ≤ Subgroup.normalizer (W₀ : Set G) :=
    CFSG.Walter.Transitivity.le_normalizer_inf hAV (hAH.trans Subgroup.le_normalizer)
  have hV2 : IsPGroup 2 V := hV.2.2.2.isPGroup
  have hW₀V : W₀ ≤ V := inf_le_left
  have hW₀H : W₀ ≤ H := inf_le_right
  have hWle : ⁅W₀, Subgroup.zpowers e⁆ ≤ W₀ := by
    rw [← Subgroup.le_normalizer_iff_commutator_le_left]
    exact Subgroup.zpowers_le.mpr (hAW heA)
  have hXH : CFSG.Open.pCoreOf 3 H ≤ H := CFSG.LieType.BorelTits.pCoreOf_le (r := 3) H
  have hXn : ((CFSG.Open.pCoreOf 3 H).subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hXH).mpr
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf (r := 3) H)
  have hAX : F.A ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 3 H : Set G) :=
    hAH.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf (r := 3) H)
  have hjoin : IsPGroup 3 (F.A ⊔ CFSG.Open.pCoreOf 3 H : Subgroup G) :=
    IsPGroup.to_sup_of_normal_right' F.elemAbelian.isPGroup
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 3) H) hAX
  have hXM : CFSG.Open.pCoreOf 3 H ≤ D.M :=
    le_sup_right.trans (F.le_M_of_isPGroup hF.normalizer_A hjoin le_sup_left)
  exact A10Gen.le_centralizer_of_pCoreOf_eq_bot hXH hXn (hXM.trans hV.2.2.1)
    hV2 (hWle.trans hW₀V) (hWle.trans hW₀H) hO'

private theorem fixed_le_centralizer_of_deg_three (F : A10Frame c) (hF : A10Facts F)
    {V : Subgroup G} (hV : UC22.InCalV D.M V) {B : Subgroup G} (hBA : B ≤ F.A)
    {e : G} (heA : e ∈ F.A) (he3 : F.deg (Subgroup.zpowers e) = 3)
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    CFSG.Open.pCoreOf p (Subgroup.centralizer (B : Set G)) ⊓
        Subgroup.centralizer ({e} : Set G) ≤
      Subgroup.centralizer (V ⊓ Subgroup.centralizer (B : Set G) : Subgroup G) := by
  classical
  let H : Subgroup G := Subgroup.centralizer (B : Set G)
  let W₀ : Subgroup G := V ⊓ H
  have hV2 : IsPGroup 2 V := hV.2.2.2.isPGroup
  have hW₀V : W₀ ≤ V := inf_le_left
  have hW₀H : W₀ ≤ H := inf_le_right
  have hHX : H ≤ Subgroup.normalizer (CFSG.Open.pCoreOf p H : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf (r := p) H
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  have hxM : x ∈ D.M := F.centralizer_le_M_of_deg_three hF heA he3 hx.2
  have hxN : x ∈ Subgroup.normalizer (V : Set G) := hV.2.2.1 hxM
  have hcommX : ⁅x, w⁆ ∈ CFSG.Open.pCoreOf p H := by
    have hxn : w * x⁻¹ * w⁻¹ ∈ CFSG.Open.pCoreOf p H :=
      (Subgroup.mem_normalizer_iff.mp (hHX (hW₀H hw)) x⁻¹).mp (Subgroup.inv_mem _ hx.1)
    have hmem := (CFSG.Open.pCoreOf p H).mul_mem hx.1 hxn
    simpa [commutatorElement_def, mul_assoc] using hmem
  have hcommV : ⁅x, w⁆ ∈ V := by
    have hxw : x * w * x⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hxN w).mp (hW₀V hw)
    have hmem := V.mul_mem hxw (V.inv_mem (hW₀V hw))
    simpa [commutatorElement_def] using hmem
  have hdisj : Disjoint (CFSG.Open.pCoreOf p H) V :=
    IsPGroup.disjoint_of_ne p 2 hp2 _ _
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := p) H) hV2
  have h1 : ⁅x, w⁆ = 1 := by
    have hbot := hdisj.le_bot ⟨hcommX, hcommV⟩
    simpa using hbot
  exact (commutatorElement_eq_one_iff_mul_comm.mp h1).symm

private theorem centralizes_pCoreOf_of_deg_three (F : A10Frame c) (hF : A10Facts F)
    {V : Subgroup G} (hV : UC22.InCalV D.M V) {B : Subgroup G} (hBA : B ≤ F.A)
    (hO : CFSG.Open.pCoreOf 2 (Subgroup.centralizer (B : Set G)) = ⊥)
    {e : G} (heA : e ∈ F.A) (he3 : F.deg (Subgroup.zpowers e) = 3) :
    ∀ p : ℕ, p.Prime →
      ⁅V ⊓ Subgroup.centralizer (B : Set G), Subgroup.zpowers e⁆ ≤
        Subgroup.centralizer
          (CFSG.Open.pCoreOf p (Subgroup.centralizer (B : Set G)) : Set G) := by
  classical
  let H : Subgroup G := Subgroup.centralizer (B : Set G)
  let W₀ : Subgroup G := V ⊓ H
  have hO' : CFSG.Open.pCoreOf 2 H = ⊥ := hO
  have hAH : F.A ≤ H := A_le_centralizer F hBA
  have hAV : F.A ≤ Subgroup.normalizer (V : Set G) := F.A_le_M.trans hV.2.2.1
  have hAW : F.A ≤ Subgroup.normalizer (W₀ : Set G) :=
    CFSG.Walter.Transitivity.le_normalizer_inf hAV (hAH.trans Subgroup.le_normalizer)
  have hW₀H : W₀ ≤ H := inf_le_right
  have hWle : ⁅W₀, Subgroup.zpowers e⁆ ≤ W₀ := by
    rw [← Subgroup.le_normalizer_iff_commutator_le_left]
    exact Subgroup.zpowers_le.mpr (hAW heA)
  intro p hp
  by_cases hp2 : p = 2
  · subst hp2
    rw [hO']
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Subgroup.mem_bot.mp hy]
    simp
  · by_cases hp3 : p = 3
    · subst hp3
      exact le_centralizer_pCoreOf_three F hF hV hBA hO heA
    · haveI : Fact p.Prime := ⟨hp⟩
      have hcop : Nat.Coprime p 6 := by
        have h2 : Nat.Coprime p 2 := (Nat.coprime_primes hp Nat.prime_two).mpr hp2
        have h3 : Nat.Coprime p 3 := (Nat.coprime_primes hp Nat.prime_three).mpr hp3
        have h6 : (6 : ℕ) = 2 * 3 := by norm_num
        rw [h6]
        exact h2.mul_right h3
      have hHX : H ≤ Subgroup.normalizer (CFSG.Open.pCoreOf p H : Set G) :=
        CFSG.LieType.BorelTits.le_normalizer_pCoreOf (r := p) H
      exact A10Gen.commutator_zpowers_le_centralizer hcop
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := p) H) (hV.2.2.2.mono inf_le_left)
        (F.elemAbelian.2 e heA) (hAW heA) ((hAH.trans hHX) heA) (hW₀H.trans hHX)
        (fixed_le_centralizer_of_deg_three F hF hV hBA heA he3 hp2)

private theorem mem_centralizer_inf_of_deg_three (F : A10Frame c) (hF : A10Facts F)
    {V : Subgroup G} (hV : UC22.InCalV D.M V) {B : Subgroup G} (hBA : B ≤ F.A)
    (hO : CFSG.Open.pCoreOf 2 (Subgroup.centralizer (B : Set G)) = ⊥)
    (hE : CFSG.GorensteinWalter.componentLayerOf (Subgroup.centralizer (B : Set G)) ≤ D.M)
    {e : G} (heA : e ∈ F.A) (he3 : F.deg (Subgroup.zpowers e) = 3) :
    e ∈ Subgroup.centralizer (V ⊓ Subgroup.centralizer (B : Set G) : Subgroup G) := by
  classical
  let H : Subgroup G := Subgroup.centralizer (B : Set G)
  let W₀ : Subgroup G := V ⊓ H
  have hO' : CFSG.Open.pCoreOf 2 H = ⊥ := hO
  have hE' : CFSG.GorensteinWalter.componentLayerOf H ≤ D.M := hE
  have hAH : F.A ≤ H := A_le_centralizer F hBA
  have hAV : F.A ≤ Subgroup.normalizer (V : Set G) := F.A_le_M.trans hV.2.2.1
  have hAW : F.A ≤ Subgroup.normalizer (W₀ : Set G) :=
    CFSG.Walter.Transitivity.le_normalizer_inf hAV (hAH.trans Subgroup.le_normalizer)
  have hV2 : IsPGroup 2 V := hV.2.2.2.isPGroup
  have hW₀ea : CFSG.Open.IsElemAbelian 2 W₀ := hV.2.2.2.mono inf_le_left
  have hW₀2 : IsPGroup 2 W₀ := hW₀ea.isPGroup
  have hW₀V : W₀ ≤ V := inf_le_left
  have hW₀H : W₀ ≤ H := inf_le_right
  have hWle : ⁅W₀, Subgroup.zpowers e⁆ ≤ W₀ := by
    rw [← Subgroup.le_normalizer_iff_commutator_le_left]
    exact Subgroup.zpowers_le.mpr (hAW heA)
  have hWH : ⁅W₀, Subgroup.zpowers e⁆ ≤ H := hWle.trans hW₀H
  have hW2 : IsPGroup 2 (⁅W₀, Subgroup.zpowers e⁆ : Subgroup G) := hW₀2.to_le hWle
  have hcent : ∀ p : ℕ, p.Prime →
      ⁅W₀, Subgroup.zpowers e⁆ ≤ Subgroup.centralizer (CFSG.Open.pCoreOf p H : Set G) :=
    centralizes_pCoreOf_of_deg_three F hF hV hBA hO heA he3
  have hlayer : ⁅W₀, Subgroup.zpowers e⁆ ≤
      Subgroup.centralizer (CFSG.GorensteinWalter.componentLayerOf H : Set G) := by
    have hEH : CFSG.GorensteinWalter.componentLayerOf H ≤ H :=
      (CFSG.GorensteinWalter.componentLayerOf_isNormalIn H).1
    have hEn : ((CFSG.GorensteinWalter.componentLayerOf H).subgroupOf H).Normal :=
      CFSG.ClassicalInvolution.Q3.componentLayerOf_subgroupOf_normal H
    exact A10Gen.le_centralizer_of_pCoreOf_eq_bot hEH hEn (hE'.trans hV.2.2.1)
      hV2 (hWle.trans hW₀V) hWH hO'
  have hbot : ⁅W₀, Subgroup.zpowers e⁆ = ⊥ :=
    A10Gen.eq_bot_of_le_centralizer_pCoreOf hW2 hWH hO' hcent hlayer
  have hcent' : W₀ ≤ Subgroup.centralizer (Subgroup.zpowers e : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  have hw' : w ∈ Subgroup.centralizer (Subgroup.zpowers e : Set G) := hcent' hw
  exact (Subgroup.mem_centralizer_iff.mp hw' e (Subgroup.mem_zpowers e)).symm

private theorem support_card_generators :
    pa.support.card = 3 ∧ pb.support.card = 3 ∧ pc.support.card = 3 := by
  have ha : pa = toP 1 0 0 := by simp [toP]
  have hb : pb = toP 0 1 0 := by simp [toP]
  have hc : pc = toP 0 0 1 := by simp [toP]
  rw [ha, hb, hc, A10Perm.support_toP, A10Perm.support_toP, A10Perm.support_toP]
  decide +kernel

private theorem A_le_centralizer_inf (F : A10Frame c) (hF : A10Facts F)
    {V : Subgroup G} (hV : UC22.InCalV D.M V) {B : Subgroup G} (hBA : B ≤ F.A)
    (hO : CFSG.Open.pCoreOf 2 (Subgroup.centralizer (B : Set G)) = ⊥)
    (hE : CFSG.GorensteinWalter.componentLayerOf (Subgroup.centralizer (B : Set G)) ≤ D.M) :
    F.A ≤ Subgroup.centralizer (V ⊓ Subgroup.centralizer (B : Set G) : Subgroup G) := by
  classical
  let H : Subgroup G := Subgroup.centralizer (B : Set G)
  let W₀ : Subgroup G := V ⊓ H
  obtain ⟨hpas, hpbs, hpcs⟩ := support_card_generators
  obtain ⟨ea, heaA, hea3, heaeq⟩ := exists_mem_A_deg_three F
    (A10Perm.mem_atilde_iff.mpr ⟨1, 0, 0, by decide +kernel⟩) hpas
  obtain ⟨eb, hebA, heb3, hebeq⟩ := exists_mem_A_deg_three F
    (A10Perm.mem_atilde_iff.mpr ⟨0, 1, 0, by decide +kernel⟩) hpbs
  obtain ⟨ec, hecA, hec3, heceq⟩ := exists_mem_A_deg_three F
    (A10Perm.mem_atilde_iff.mpr ⟨0, 0, 1, by decide +kernel⟩) hpcs
  have heaC : ea ∈ Subgroup.centralizer (W₀ : Set G) :=
    mem_centralizer_inf_of_deg_three F hF hV hBA hO hE heaA hea3
  have hebC : eb ∈ Subgroup.centralizer (W₀ : Set G) :=
    mem_centralizer_inf_of_deg_three F hF hV hBA hO hE hebA heb3
  have hecC : ec ∈ Subgroup.centralizer (W₀ : Set G) :=
    mem_centralizer_inf_of_deg_three F hF hV hBA hO hE hecA hec3
  intro a haA
  have hmemA : (⟨a, F.A_le_M haA⟩ : ↥D.M) ∈ F.A.subgroupOf D.M := haA
  have hphi : F.phiA ⟨a, F.A_le_M haA⟩ ∈ A10Perm.atilde := by
    have h := Subgroup.mem_map_of_mem F.phiA hmemA
    rwa [F.map_A_phiA] at h
  obtain ⟨i, j, k, hijk⟩ := A10Perm.mem_atilde_iff.mp hphi
  let d : ↥D.M := ⟨ea, F.A_le_M heaA⟩ ^ (i : ℕ) * ⟨eb, F.A_le_M hebA⟩ ^ (j : ℕ) *
    ⟨ec, F.A_le_M hecA⟩ ^ (k : ℕ)
  have hmem : ∀ (x : G) (hx : x ∈ F.A), (⟨x, F.A_le_M hx⟩ : ↥D.M) ∈ F.A.subgroupOf D.M :=
    fun x hx => hx
  have hdA : d ∈ F.A.subgroupOf D.M := by
    dsimp only [d]
    exact (F.A.subgroupOf D.M).mul_mem ((F.A.subgroupOf D.M).mul_mem
      (Subgroup.pow_mem _ (hmem ea heaA) _) (Subgroup.pow_mem _ (hmem eb hebA) _))
      (Subgroup.pow_mem _ (hmem ec hecA) _)
  have hdphi : F.phiA d = toP i j k := by
    dsimp only [d]
    rw [map_mul, map_mul, map_pow, map_pow, map_pow, heaeq, hebeq, heceq]
    rfl
  have heq : (⟨a, F.A_le_M haA⟩ : ↥D.M) = d := by
    refine mul_inv_eq_one.mp (phiA_eq_one_on_A F ?_ ?_)
    · exact (F.A.subgroupOf D.M).mul_mem (hmem a haA) (Subgroup.inv_mem _ hdA)
    · rw [map_mul, map_inv, hijk, hdphi, mul_inv_cancel]
  have hval : a = ea ^ (i : ℕ) * eb ^ (j : ℕ) * ec ^ (k : ℕ) := by
    simpa [d] using congrArg Subtype.val heq
  rw [hval]
  exact (Subgroup.centralizer (W₀ : Set G)).mul_mem
    ((Subgroup.centralizer (W₀ : Set G)).mul_mem
      (Subgroup.pow_mem _ heaC _) (Subgroup.pow_mem _ hebC _))
    (Subgroup.pow_mem _ hecC _)

theorem inf_centralizer_le_centralizer_A (F : A10Frame c) (hF : A10Facts F)
    {V : Subgroup G} (hV : UC22.InCalV D.M V) {B : Subgroup G} (hBA : B ≤ F.A)
    (hB3 : Nat.card B = 3)
    (hO : CFSG.Open.pCoreOf 2 (Subgroup.centralizer (B : Set G)) = ⊥)
    (hE : CFSG.GorensteinWalter.componentLayerOf (Subgroup.centralizer (B : Set G)) ≤ D.M) :
    V ⊓ Subgroup.centralizer (B : Set G) ≤ Subgroup.centralizer (F.A : Set G) :=
  Subgroup.le_centralizer_iff.mp (A_le_centralizer_inf F hF hV hBA hO hE)

end Ctx82E3.A10Frame

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3
