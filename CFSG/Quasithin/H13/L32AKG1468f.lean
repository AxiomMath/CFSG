module

public import CFSG.Quasithin.Background.A4Defs
public import CFSG.LocalAnalysis.ComponentClassification.Quasisimple
import CFSG.GroupTheory.PCore.OpenTransport
public import CFSG.Foundations.Basic

public section

namespace CFSG.Quasithin.H13.KGRu

open CFSG.Open CFSG.LieType.BorelTits

theorem pCore_le_center_of_quasisimple {X : Type} [Group X] [Finite X]
    (hq : CFSG.IsQuasisimple X) : CFSG.pCore 2 X ≤ Subgroup.center X := by
  have hq' : CFSG.Open.IsQuasisimple X := ⟨hq.1.commutator_eq_top, hq.2.1⟩
  rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top hq'
      (CFSG.pCore 2 X) with h | h
  · exact h
  · exfalso
    have hp : IsPGroup 2 (⊤ : Subgroup X) := h ▸ CFSG.pCore_isPGroup (p := 2) (G := X)
    have := (hp.of_equiv Subgroup.topEquiv).isNilpotent
    have : Group.IsPerfect X := hq.1
    have : Nontrivial X := CFSG.ComponentClassification.Quasisimple.nontrivial hq'
    exact Group.IsPerfect.not_isSolvable X inferInstance

variable {G : Type} [Group G]

theorem map_centralizer_singleton_subtype {Y : Subgroup G} (z : ↥Y) :
    (Subgroup.centralizer ({z} : Set ↥Y)).map Y.subtype =
      Y ⊓ Subgroup.centralizer ({(z : G)} : Set G) := by
  ext g
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' : x * z = z * x := Subgroup.mem_centralizer_singleton_iff.mp (SetLike.mem_coe.mp hx)
    exact Subgroup.mem_inf.mpr ⟨x.2, Subgroup.mem_centralizer_singleton_iff.mpr
      (by simpa using congrArg Subtype.val hx')⟩
  · intro hg
    obtain ⟨hgY, hgz⟩ := Subgroup.mem_inf.mp hg
    rw [Subgroup.mem_centralizer_singleton_iff] at hgz
    exact ⟨⟨g, hgY⟩, SetLike.mem_coe.mpr (Subgroup.mem_centralizer_singleton_iff.mpr
      (Subtype.ext hgz)), rfl⟩

theorem map_normalizer_subtype {Y E : Subgroup G} (hEY : E ≤ Y) :
    (Subgroup.normalizer ((E.subgroupOf Y : Subgroup ↥Y) : Set ↥Y)).map Y.subtype =
      Y ⊓ Subgroup.normalizer (E : Set G) := by
  ext g
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine Subgroup.mem_inf.mpr ⟨x.2, Subgroup.mem_normalizer_iff.mpr fun e => ?_⟩
    constructor
    · intro he
      have h1 := (Subgroup.mem_normalizer_iff.mp hx ⟨e, hEY he⟩).mp
        (Subgroup.mem_subgroupOf.mpr he)
      exact Subgroup.mem_subgroupOf.mp h1
    · intro he
      have heY : e ∈ Y := by
        have h0 := hEY he
        have e1 : e = (x : G)⁻¹ * ((x : G) * e * (x : G)⁻¹) * (x : G) := by group
        rw [e1]
        exact mul_mem (mul_mem (inv_mem x.2) h0) x.2
      have h1 := (Subgroup.mem_normalizer_iff.mp hx ⟨e, heY⟩).mpr
        (Subgroup.mem_subgroupOf.mpr he)
      exact Subgroup.mem_subgroupOf.mp h1
  · intro hg
    obtain ⟨hgY, hgN⟩ := Subgroup.mem_inf.mp hg
    refine ⟨⟨g, hgY⟩, Subgroup.mem_normalizer_iff.mpr fun e => ?_, rfl⟩
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact Subgroup.mem_normalizer_iff.mp hgN e

theorem oTwoUpper_normal (X : Subgroup G) : ((oTwoUpper X).subgroupOf X).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (oTwoUpper_le X)).mpr (le_normalizer_oTwoUpper X)

theorem isPGroup_quot_oTwoUpper [Finite G] (X : Subgroup G)
    [((oTwoUpper X).subgroupOf X).Normal] :
    IsPGroup 2 (↥X ⧸ (oTwoUpper X).subgroupOf X) := by
  intro q
  obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨k, hk⟩ := exists_pow_mem_oTwoUpper X c.2
  refine ⟨k, ?_⟩
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  simpa using hk

section Central

variable {Y Q : Type} [Group Y] [Group Q] (φ : Y →* Q)

theorem mem_centralizer_of_odd (hker : φ.ker ≤ Subgroup.center Y) (hker2 : IsPGroup 2 φ.ker)
    {y g : Y} (hg : φ g * φ y = φ y * φ g) (hodd : Odd (orderOf g)) :
    g * y = y * g := by
  obtain ⟨c, hc⟩ : ∃ c, c = g * y * g⁻¹ * y⁻¹ := ⟨_, rfl⟩
  have hcK : c ∈ φ.ker := by
    rw [MonoidHom.mem_ker, hc, map_mul, map_mul, map_mul, map_inv, map_inv, hg]
    group
  have hcZ := hker hcK
  have hgy : g * y * g⁻¹ = c * y := by rw [hc]; group
  have hpow : ∀ n : ℕ, g ^ n * y * (g ^ n)⁻¹ = c ^ n * y := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      calc g ^ (n + 1) * y * (g ^ (n + 1))⁻¹ = g * (g ^ n * y * (g ^ n)⁻¹) * g⁻¹ := by
            rw [pow_succ']; group
        _ = g * (c ^ n * y) * g⁻¹ := by rw [ih]
        _ = c ^ n * (g * y * g⁻¹) := by
            rw [show g * (c ^ n * y) * g⁻¹ = (g * c ^ n * g⁻¹) * (g * y * g⁻¹) by group,
              show g * c ^ n * g⁻¹ = c ^ n by
                rw [Subgroup.mem_center_iff.mp (pow_mem hcZ n) g]; group]
        _ = c ^ (n + 1) * y := by rw [hgy, pow_succ, mul_assoc]
  have hcn : c ^ orderOf g = 1 := by
    have := hpow (orderOf g)
    rw [pow_orderOf_eq_one, one_mul, inv_one, mul_one] at this
    exact (mul_eq_right.mp this.symm)
  obtain ⟨k, hk⟩ := hker2 ⟨c, hcK⟩
  have hc2 : c ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have h1 : orderOf c = 1 := Nat.Coprime.eq_one_of_dvd
    (Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hcn)
      (Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hodd)))
    (orderOf_dvd_of_pow_eq_one hc2)
  have hc1 : c = 1 := orderOf_eq_one_iff.mp h1
  calc g * y = c * (y * g) := by rw [hc]; group
    _ = y * g := by rw [hc1, one_mul]

theorem exists_odd_preimage (hφs : Function.Surjective φ) (hker2 : IsPGroup 2 φ.ker) {x : Q}
    (hodd : Odd (orderOf x)) : ∃ g : Y, φ g = x ∧ Odd (orderOf g) := by
  obtain ⟨g₀, rfl⟩ := hφs x
  have hm : g₀ ^ orderOf (φ g₀) ∈ φ.ker := by
    rw [MonoidHom.mem_ker, map_pow, pow_orderOf_eq_one]
  obtain ⟨k, hk⟩ := hker2 ⟨_, hm⟩
  have hk' : (g₀ ^ orderOf (φ g₀)) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  set g₁ := g₀ ^ 2 ^ k with hg₁
  have hg₁o : orderOf g₁ ∣ orderOf (φ g₀) := by
    refine orderOf_dvd_of_pow_eq_one ?_
    rw [hg₁, ← pow_mul, mul_comm, pow_mul, hk']
  have hcop : Nat.Coprime (2 ^ k) (orderOf (φ g₀)) :=
    Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hodd)
  obtain ⟨b, hb⟩ := exists_pow_eq_self_of_coprime hcop
  refine ⟨g₁ ^ b, by rw [map_pow, hg₁, map_pow, hb], ?_⟩
  exact (hodd.of_dvd_nat hg₁o).of_dvd_nat (orderOf_pow_dvd b)

theorem oTwoUpper_centralizer_map (hφs : Function.Surjective φ)
    (hker : φ.ker ≤ Subgroup.center Y) (hker2 : IsPGroup 2 φ.ker) (y : Y) :
    oTwoUpper (Subgroup.centralizer ({φ y} : Set Q)) =
      (oTwoUpper (Subgroup.centralizer ({y} : Set Y))).map φ := by
  apply le_antisymm
  · refine (Subgroup.closure_le _).mpr ?_
    rintro x ⟨hxC, hodd⟩
    obtain ⟨g, rfl, hgo⟩ := exists_odd_preimage φ hφs hker2 hodd
    have hgC : g ∈ Subgroup.centralizer ({y} : Set Y) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact mem_centralizer_of_odd φ hker hker2
        (Subgroup.mem_centralizer_singleton_iff.mp hxC) hgo
    exact ⟨g, mem_oTwoUpper_of_odd hgC hgo, rfl⟩
  · rw [Subgroup.map_le_iff_le_comap]
    refine (Subgroup.closure_le _).mpr ?_
    rintro g ⟨hgC, hodd⟩
    refine mem_oTwoUpper_of_odd ?_ (hodd.of_dvd_nat (orderOf_map_dvd φ g))
    rw [Subgroup.mem_centralizer_singleton_iff] at hgC ⊢
    rw [← map_mul, hgC, map_mul]

theorem mem_normalizer_inf {X : Type} [Group X] {g : X} {B C : Subgroup X}
    (hB : g ∈ Subgroup.normalizer (B : Set X)) (hC : g ∈ Subgroup.normalizer (C : Set X)) :
    g ∈ Subgroup.normalizer ((B ⊓ C : Subgroup X) : Set X) := by
  rw [Subgroup.mem_normalizer_iff] at hB hC ⊢
  intro h
  rw [Subgroup.mem_inf, Subgroup.mem_inf, hB h, hC h]

theorem pCoreOf_map_eq [Finite Y] [Finite Q] (hker2 : IsPGroup 2 φ.ker) (B : Subgroup Y) :
    pCoreOf 2 (B.map φ) = (pCoreOf 2 B).map φ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply le_antisymm
  · set P := B ⊓ (pCoreOf 2 (B.map φ)).comap φ with hP
    have hPB : P ≤ pCoreOf 2 B := by
      refine le_pCoreOf_of_le_normalizer 2 inf_le_left (fun b hb => ?_) fun p => ?_
      · exact mem_normalizer_inf (Subgroup.le_normalizer hb)
          (Subgroup.le_normalizer_comap φ (le_normalizer_pCoreOf 2 (B.map φ) ⟨b, hb, rfl⟩))
      · obtain ⟨k, hk⟩ := (pCoreOf_isPGroup 2 (B.map φ)) ⟨φ p, (Subgroup.mem_inf.mp p.2).2⟩
        have h1 : (p : Y) ^ 2 ^ k ∈ φ.ker := by
          rw [MonoidHom.mem_ker, map_pow]
          simpa using congrArg Subtype.val hk
        obtain ⟨j, hj⟩ := hker2 ⟨_, h1⟩
        have hj' : ((p : Y) ^ 2 ^ k) ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
        refine ⟨k + j, Subtype.ext ?_⟩
        rw [SubgroupClass.coe_pow, OneMemClass.coe_one, pow_add, pow_mul, hj']
    intro x hx
    obtain ⟨b, hb, rfl⟩ := (pCoreOf_le 2 (B.map φ)) hx
    exact ⟨b, hPB (Subgroup.mem_inf.mpr ⟨hb, hx⟩), rfl⟩
  · refine le_pCoreOf_of_le_normalizer 2 (Subgroup.map_mono (pCoreOf_le 2 B)) ?_
      ((pCoreOf_isPGroup 2 B).map φ)
    rintro _ ⟨b, hb, rfl⟩
    exact Subgroup.le_normalizer_map φ ⟨b, le_normalizer_pCoreOf 2 B hb, rfl⟩

theorem pCoreOf_subgroupOf_self' (B : Subgroup Y) :
    (pCoreOf 2 B).subgroupOf B = CFSG.pCore 2 ↥B := CFSG.openPCoreOf_subgroupOf 2 B

theorem nonempty_quot_map_equiv [Finite Y] [Finite Q] (hker2 : IsPGroup 2 φ.ker) (B : Subgroup Y) :
    Nonempty (↥(B.map φ) ⧸ CFSG.pCore 2 ↥(B.map φ) ≃* ↥B ⧸ CFSG.pCore 2 ↥B) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set ψ : ↥B →* ↥(B.map φ) ⧸ CFSG.pCore 2 ↥(B.map φ) :=
    (QuotientGroup.mk' _).comp (φ.subgroupMap B) with hψ
  have hψs : Function.Surjective ψ :=
    (QuotientGroup.mk'_surjective _).comp (φ.subgroupMap_surjective B)
  have hKB : B ⊓ φ.ker ≤ pCoreOf 2 B :=
    le_pCoreOf_of_le_normalizer 2 inf_le_left
      (fun b hb => mem_normalizer_inf (Subgroup.le_normalizer hb)
        (by rw [Subgroup.normalizer_eq_top_iff.mpr inferInstance]; exact Subgroup.mem_top b))
      (hker2.to_le inf_le_right)
  have hψk : ψ.ker = CFSG.pCore 2 ↥B := by
    ext b
    rw [MonoidHom.mem_ker, hψ, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, ← pCoreOf_subgroupOf_self', ← pCoreOf_subgroupOf_self',
      Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, pCoreOf_map_eq φ hker2 B]
    constructor
    · rintro ⟨p, hp, hpb⟩
      have hm : p⁻¹ * b ∈ B ⊓ φ.ker := by
        refine Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem (pCoreOf_le 2 B hp)) b.2, ?_⟩
        rw [MonoidHom.mem_ker, map_mul, map_inv, hpb]
        exact inv_mul_cancel _
      have := mul_mem hp (hKB hm)
      rwa [mul_inv_cancel_left] at this
    · intro hb
      exact ⟨b, hb, rfl⟩
  exact ⟨(QuotientGroup.quotientKerEquivOfSurjective ψ hψs).symm.trans
    (QuotientGroup.quotientMulEquivOfEq hψk)⟩

end Central

end CFSG.Quasithin.H13.KGRu
