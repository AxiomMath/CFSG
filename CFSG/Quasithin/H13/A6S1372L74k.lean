module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.H13.A6S1372L19b
public import CFSG.Quasithin.H13.A6S1372L74e
public import CFSG.Quasithin.H13.U3L14Blk

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.QuasithinUnique.Bridge
open scoped Pointwise IsMulCommutative

namespace A6L74

variable {G : Type} [Group G]

theorem exists_two_pow_mem_of_mem_sup {A Q : Subgroup G} (hQ : IsPGroup 2 Q)
    (hQA : Q ≤ Subgroup.normalizer (A : Set G)) {x : G} (hx : x ∈ A ⊔ Q) :
    ∃ a : ℕ, x ^ 2 ^ a ∈ A := by
  rw [sup_comm] at hx
  obtain ⟨q, hq, n, hn, rfl⟩ := (A6L19.mem_sup_iff hQA).1 hx
  have hn' : q * n * q⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp (hQA hq) n).mp hn
  obtain ⟨a, ha⟩ := hQ ⟨q, hq⟩
  have hqa : q ^ 2 ^ a = 1 := by simpa using congrArg Subtype.val ha
  obtain ⟨n', hn'', he⟩ := U3.pow_mem_mul_of_normalizes' hn' (hQA hq) (2 ^ a)
  refine ⟨a, ?_⟩
  have e : q * n = q * n * q⁻¹ * q := by group
  rw [e, he, hqa, mul_one]
  exact hn''

theorem mem_pCoreOf_of_two_pow {K : Subgroup G} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hexp : ∀ k ∈ K, k ^ p ∈ pCoreOf 2 K) {k : G} (hk : k ∈ K) {a : ℕ}
    (ha : k ^ 2 ^ a ∈ pCoreOf 2 K) : k ∈ pCoreOf 2 K := by
  have hcop : Nat.Coprime (2 ^ a) p :=
    Nat.Coprime.pow_left a ((Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2))
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.mpr hcop
  have e : k = (k ^ 2 ^ a) ^ u * (k ^ p) ^ v := by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add,
      mul_comm ((2 ^ a : ℕ) : ℤ) u, mul_comm (p : ℤ) v, huv, zpow_one]
  rw [e]
  exact (pCoreOf 2 K).mul_mem ((pCoreOf 2 K).zpow_mem ha u)
    ((pCoreOf 2 K).zpow_mem (hexp k hk) v)

variable [Finite G]

theorem isSylowTwoOf_sup {K R : Subgroup G} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hexp : ∀ k ∈ K, k ^ p ∈ pCoreOf 2 K) (hR : IsPGroup 2 R)
    (hRK : R ≤ Subgroup.normalizer (K : Set G)) (hOR : pCoreOf 2 K ≤ R) :
    IsSylowTwoOf R (K ⊔ R) := by
  rw [A4.isSylowTwoOf_iff_maximal]
  refine ⟨le_sup_right, hR, fun P hPX hP hRP y hy => ?_⟩
  have hyX := hPX hy
  rw [sup_comm] at hyX
  obtain ⟨r, hr, k, hk, rfl⟩ := (A6L19.mem_sup_iff hRK).1 hyX
  have hkP : k ∈ P := by
    have e : k = r⁻¹ * (r * k) := by group
    rw [e]
    exact P.mul_mem (P.inv_mem (hRP hr)) hy
  obtain ⟨a, ha⟩ := hP ⟨k, hkP⟩
  have hka : k ^ 2 ^ a = 1 := by simpa using congrArg Subtype.val ha
  have hkO : k ∈ pCoreOf 2 K :=
    mem_pCoreOf_of_two_pow hp hp2 hexp hk (by rw [hka]; exact Subgroup.one_mem _)
  exact R.mul_mem hr (hOR hkO)

theorem inf_centralizer_le_pCoreOf {K R V : Subgroup G} (hR : IsPGroup 2 R)
    (hRK : R ≤ Subgroup.normalizer (K : Set G)) (hXV : K ⊔ R ≤ Subgroup.normalizer (V : Set G))
    (hCK : K ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 K) :
    (K ⊔ R) ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 (K ⊔ R) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_pCoreOf_of_le_normalizer 2 inf_le_left (fun x hx => mem_normalizer_inf_of
    (Subgroup.le_normalizer hx) (InternalSec.le_normalizer_centralizer hXV hx)) ?_
  rintro ⟨c, hcX, hcV⟩
  obtain ⟨a, ha⟩ := exists_two_pow_mem_of_mem_sup hR hRK hcX
  have h1 : c ^ 2 ^ a ∈ pCoreOf 2 K := hCK ⟨ha, (Subgroup.centralizer _).pow_mem hcV _⟩
  obtain ⟨b, hb⟩ := pCoreOf_isPGroup 2 K ⟨_, h1⟩
  have hcb : (c ^ 2 ^ a) ^ 2 ^ b = 1 := by simpa using congrArg Subtype.val hb
  have hc : c ^ 2 ^ (a + b) = 1 := by rw [pow_add, pow_mul, hcb]
  exact ⟨a + b, Subtype.ext (by simpa using hc)⟩

theorem isSolvable_sup {K R : Subgroup G}
    (hcomm : ∀ a ∈ K, ∀ b ∈ K, a * b * a⁻¹ * b⁻¹ ∈ pCoreOf 2 K) (hR : IsPGroup 2 R)
    (hRK : R ≤ Subgroup.normalizer (K : Set G)) : Group.IsSolvable ↥(K ⊔ R) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK : Group.IsSolvable ↥K := by
    have : Group.IsNilpotent ↥(CFSG.pCore 2 ↥K) := (CFSG.pCore_isPGroup (p := 2)).isNilpotent
    have : Group.IsSolvable (↥K ⧸ CFSG.pCore 2 ↥K) := by
      refine Group.isSolvable_of_comm fun x y => ?_
      induction x using QuotientGroup.induction_on with
      | H a =>
        induction y using QuotientGroup.induction_on with
        | H b =>
          have h1 : a * b * a⁻¹ * b⁻¹ ∈ CFSG.pCore 2 ↥K :=
            (mem_pCoreOf_iff (a * b * a⁻¹ * b⁻¹)).1 (hcomm a a.2 b b.2)
          rw [← QuotientGroup.eq_one_iff (N := CFSG.pCore 2 ↥K)] at h1
          simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv] at h1
          rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h1
          exact h1
    exact Group.isSolvable_of_ker_le_range (CFSG.pCore 2 ↥K).subtype
      (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) (by
        rw [QuotientGroup.ker_mk', Subgroup.range_subtype])
  set X := K ⊔ R with hX
  have hXK : X ≤ Subgroup.normalizer (K : Set G) := sup_le Subgroup.le_normalizer hRK
  have hn : (K.subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr hXK
  have h2 : IsPGroup 2 (↥X ⧸ K.subgroupOf X) := by
    intro y
    induction y using QuotientGroup.induction_on with
    | H x =>
      obtain ⟨a, ha⟩ := exists_two_pow_mem_of_mem_sup hR hRK x.2
      refine ⟨a, ?_⟩
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      simpa using ha
  have : Group.IsNilpotent (↥X ⧸ K.subgroupOf X) := h2.isNilpotent
  have : Group.IsSolvable ↥(K.subgroupOf X) :=
    Group.isSolvable_of_surjective
      (f := (Subgroup.subgroupOfEquivOfLe (le_sup_left : K ≤ X)).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe (le_sup_left : K ≤ X)).symm.surjective
  exact Group.isSolvable_of_ker_le_range (K.subgroupOf X).subtype
    (QuotientGroup.mk' (K.subgroupOf X))
    (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])

theorem isTwoReducedIn_twoReducedProduct (X : Subgroup G) :
    IsTwoReducedIn X (twoReducedProduct X) := by
  have hle : twoReducedProduct X ≤ X := iSup₂_le fun _ hV => hV.1
  rw [isTwoReducedIn_iff_isPrimeReduced_subgroupOf]
  refine ⟨hle, ?_⟩
  have e : (twoReducedProduct X).subgroupOf X = primeReducedAggregate X 2 := by
    have h := primeReducedAggregate_map_subtype_eq_twoReducedJoin X
    rw [show twoReducedProduct X = twoReducedJoin X from rfl, ← h]
    exact BlueprintB2.subgroupOf_map_subtype_self _
  rw [e]
  exact isPrimeReduced_primeReducedAggregate 2

theorem mem_normalizer_twoReducedProduct {X : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (X : Set G)) :
    g ∈ Subgroup.normalizer ((twoReducedProduct X : Subgroup G) : Set G) := by
  have hP := primeReducedAggregate_characteristic (E := ↥X) 2
  have hmap := Subgroup.characteristic_iff_map_eq.mp hP (X.normalizerMonoidHom ⟨g, hg⟩)
  have e : twoReducedProduct X = (primeReducedAggregate ↥X 2).map X.subtype :=
    (primeReducedAggregate_map_subtype_eq_twoReducedJoin X).symm
  refine A6L19.mem_normalizer_of_conj fun v hv => ?_
  rw [e] at hv ⊢
  obtain ⟨w, hw, rfl⟩ := hv
  refine ⟨X.normalizerMonoidHom ⟨g, hg⟩ w, ?_, ?_⟩
  · rw [← hmap]
    exact ⟨w, hw, rfl⟩
  · exact Subgroup.normalizerMonoidHom_apply_apply_coe X ⟨g, hg⟩ w

end A6L74

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} {S : Setting4 G T L V}

theorem QH_le_R1 {H : Subgroup G} (hH : H ∈ S.Hz) :
    pCoreOf 2 H ≤ pCoreOf 2 (S.L1 ⊔ T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTH : T ≤ H := le_sup_right.trans hH.1.1
  have hQT : pCoreOf 2 H ≤ T := pCoreOf_le_of_sylow S.h13.sylow hTH
  exact le_pCoreOf_of_le_normalizer 2 (hQT.trans le_sup_right)
    (hH.1.1.trans (le_normalizer_pCoreOf 2 H)) (pCoreOf_isPGroup 2 H)

theorem normalizer_baum_R1_le_M
    (hC : U3.CharNormal (baum (pCoreOf 2 (S.L1 ⊔ T))) (L ⊔ T)) :
    Subgroup.normalizer (baum (pCoreOf 2 (S.L1 ⊔ T)) : Set G) ≤
      Subgroup.normalizer (L : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨C₀, hCB, hC1, hchar, hLT⟩ := hC
  have hC2 : IsPGroup 2 C₀ := (pCoreOf_isPGroup 2 _).to_le (hCB.trans inf_le_left)
  obtain ⟨M', hM', hM'le⟩ := exists_maxTwoLocal_ge
    (⟨C₀, hC1, hC2, rfl⟩ : IsTwoLocal (Subgroup.normalizer (C₀ : Set G)))
  have hM := S.uniqueM.2 M' ⟨hM', hLT.trans hM'le⟩
  intro g hgB
  have hgC : g ∈ Subgroup.normalizer (C₀ : Set G) := by
    have := hchar
    have h1 := normalizer_le_normalizer_map_of_characteristic
      (C₀.subgroupOf (baum (pCoreOf 2 (S.L1 ⊔ T)))) hgB
    rwa [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hCB] at h1
  rw [← hM]
  exact hM'le hgC

end Setting4

end CFSG.Quasithin.H13.A6
