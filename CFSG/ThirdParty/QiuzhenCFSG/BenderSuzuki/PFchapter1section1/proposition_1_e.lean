module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_1_b
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_1_c
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConjAction

namespace CFSG
end CFSG
open CFSG

namespace CFSG.BenderSuzuki
namespace PFchapter1section1

/-!
# Peterfalvi, Part II, Chapter I, Section 1, Proposition 1(e)
-/

private theorem pointStabilizerCore_normal
    {G Ω : Type*} [Group G] [MulAction G Ω] :
    (pointStabilizerCore G Ω).Normal := by
  refine ⟨?_⟩
  intro n hn g
  rw [pointStabilizerCore, Subgroup.mem_iInf] at hn ⊢
  intro ω
  change (g * n * g⁻¹) • ω = ω
  calc
    (g * n * g⁻¹) • ω = g • (n • (g⁻¹ • ω)) := by
      simp [mul_assoc, smul_smul]
    _ = g • (g⁻¹ • ω) := by rw [hn (g⁻¹ • ω)]
    _ = ω := by simp [smul_smul]

private theorem le_pPrimeCore_two_of_normal_coprime
    {G : Type*} [Group G] {K : Subgroup G}
    (hK_normal : K.Normal) (hK_coprime : Nat.Coprime 2 (Nat.card K)) :
    K ≤ (pPrimeCore 2 G) := by
  exact le_sSup ⟨hK_normal, hK_coprime⟩

private theorem pointStabilizerCore_le_pPrimeCore_two
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q : Subgroup G) (t : G)
    (hA1 : HypothesisA1 G Ω H D Q t) :
    pointStabilizerCore G Ω ≤ (pPrimeCore 2 G) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let K : Subgroup G := pointStabilizerCore G Ω
  obtain ⟨α, hH⟩ := hA1.point_stabilizer
  have hKleD : K ≤ D := by
    intro x hxK
    have hxall : ∀ ω : Ω, x ∈ MulAction.stabilizer G ω := by
      intro ω
      exact ((le_pointStabilizerCore_iff (G := G) (Ω := Ω) (K := K)).mp le_rfl ω) hxK
    rw [hA1.D_eq]
    constructor
    · rw [hH]
      exact hxall α
    · have hright :
          rightConjugate H t = MulAction.stabilizer G (t⁻¹ • α) := by
        rw [hH]
        exact rightConjugate_stabilizer α t
      rw [hright]
      exact hxall (t⁻¹ • α)
  have hK_odd : Odd (Nat.card K) :=
    hA1.D_odd.of_dvd_nat (Subgroup.card_dvd_of_le hKleD)
  have hK_coprime : Nat.Coprime 2 (Nat.card K) :=
    (Nat.prime_two.coprime_iff_not_dvd).2 hK_odd.not_two_dvd_nat
  exact le_pPrimeCore_two_of_normal_coprime
    (K := K) pointStabilizerCore_normal hK_coprime

private theorem isMulCommutative_of_forall_sq_one
    {A : Type*} [Group A] (hA : ∀ x : A, x ^ 2 = 1) :
    IsMulCommutative A := by
  refine IsMulCommutative.mk <| Std.Commutative.mk ?_
  intro a b
  have hinv : ∀ x : A, x⁻¹ = x := by
    intro x
    have hx : x * x = 1 := by
      simpa [pow_two] using hA x
    calc
      x⁻¹ = x⁻¹ * 1 := by simp
      _ = x⁻¹ * (x * x) := by rw [hx]
      _ = x := by simp
  calc
    a * b = (a * b)⁻¹ := (hinv (a * b)).symm
    _ = b⁻¹ * a⁻¹ := by simp
    _ = b * a := by rw [hinv a, hinv b]

private theorem noncyclic_of_card_four_and_sq_one
    {A : Type*} [Group A] [Finite A]
    (hcard : Nat.card A = 4) (hsq : ∀ x : A, x ^ 2 = 1) :
    ¬ IsCyclic A := by
  intro hcyc
  rcases (isCyclic_iff_exists_orderOf_eq_natCard (α := A)).mp hcyc with ⟨a, ha⟩
  have horder_dvd : orderOf a ∣ 2 :=
    orderOf_dvd_iff_pow_eq_one.mpr (hsq a)
  rw [hcard] at ha
  rw [ha] at horder_dvd
  norm_num at horder_dvd

private theorem exists_rank_two_subgroup_le_Q
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q : Subgroup G) (t : G)
    (hA1 : HypothesisA1 G Ω H D Q t)
    (h2rank : TwoRankAtLeastTwo G) :
    ∃ A : Subgroup G, A ≤ Q ∧ Nat.card A = 4 ∧ ∀ x : A, x ^ 2 = 1 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨E₀, hE₀card, hE₀sq⟩ := TwoRankAtLeastTwo.exists_subgroup h2rank
  have hE₀p : IsPGroup 2 E₀ := by
    refine IsPGroup.of_card (p := 2) (G := E₀) (n := 2) ?_
    norm_num [hE₀card]
  obtain ⟨T, hE₀T⟩ := IsPGroup.exists_le_sylow (G := G) (p := 2) hE₀p
  obtain ⟨S, hSQ⟩ := proposition_1_c H D Q t hA1
  obtain ⟨g, hgTS⟩ := MulAction.exists_smul_eq G T S
  let A : Subgroup G := E₀.map (MulAut.conj g).toMonoidHom
  have hA_le_S : A ≤ (S : Subgroup G) := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hyE, rfl⟩
    have hyT : y ∈ (T : Subgroup G) := hE₀T hyE
    rw [← hgTS, Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul y (MulAut.conj g) (T : Subgroup G) hyT
  have hAcard : Nat.card A = 4 := by
    have hcard_map :
        Nat.card A = Nat.card E₀ := by
      exact Subgroup.card_map_of_injective
        (K := E₀) (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective
    rw [hcard_map, hE₀card]
  have hAsq : ∀ x : A, x ^ 2 = 1 := by
    intro x
    apply Subtype.ext
    change (x : G) ^ 2 = 1
    rcases Subgroup.mem_map.mp x.property with ⟨y, hyE, hyx⟩
    have hy2 : y ^ 2 = (1 : G) := by
      exact congrArg Subtype.val (hE₀sq ⟨y, hyE⟩)
    rw [← hyx]
    simpa [pow_two] using congrArg (fun z : G => (MulAut.conj g) z) hy2
  exact ⟨A, hA_le_S.trans hSQ, hAcard, hAsq⟩

private theorem pPrimeCore_two_le_pointStabilizerCore_of_le_stabilizer
    {G Ω : Type*} [Group G] [MulAction G Ω]
    {α : Ω}
    (htrans : MulAction.IsPretransitive G Ω)
    (hOH : (pPrimeCore 2 G) ≤ MulAction.stabilizer G α) :
    (pPrimeCore 2 G) ≤ pointStabilizerCore G Ω := by
  classical
  let O : Subgroup G := (pPrimeCore 2 G)
  rw [le_pointStabilizerCore_iff]
  intro ω x hxO
  obtain ⟨g, hg⟩ := htrans.exists_smul_eq α ω
  change x • ω = ω
  have hconjO : g⁻¹ * x * g ∈ O := by
    simpa [O] using (pPrimeCore_normal (p := 2) (G := G)).conj_mem x hxO g⁻¹
  have hfix : (g⁻¹ * x * g) • α = α := hOH hconjO
  calc
    x • ω = x • (g • α) := by rw [hg]
    _ = g • ((g⁻¹ * x * g) • α) := by
      simp [mul_assoc, smul_smul]
    _ = g • α := by rw [hfix]
    _ = ω := hg

private theorem fixedPoint_zpowers_le_H
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q A O : Subgroup G) (t : G)
    (hA1 : HypothesisA1 G Ω H D Q t)
    (hAQ : A ≤ Q) [O.Normal]
    (a : A) (ha : a ≠ 1) :
    fixedPointSubgroup (↥(Subgroup.zpowers a)) O ≤ H.comap O.subtype := by
  classical
  intro y hy
  let X : Subgroup G := Subgroup.zpowers (a : G)
  have haG_ne : (a : G) ≠ 1 := by
    intro haG
    exact ha (Subtype.ext haG)
  have hXne : X ≠ ⊥ := by
    simpa [X] using (Subgroup.zpowers_ne_bot.mpr haG_ne)
  have hXQ : X ≤ Q := by
    exact Subgroup.zpowers_le_of_mem (hAQ a.property)
  have hyconj : (a : G) * (y : G) * (a : G)⁻¹ = (y : G) := by
    have hyfix : (⟨a, Subgroup.mem_zpowers a⟩ : Subgroup.zpowers a) • y = y :=
      hy ⟨a, Subgroup.mem_zpowers a⟩
    simpa [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe] using
      congrArg Subtype.val hyfix
  have hacomm : (a : G) * (y : G) = (y : G) * (a : G) := by
    have := congrArg (fun z : G => z * (a : G)) hyconj
    simpa [mul_assoc] using this
  have hyCentralX : (y : G) ∈ Subgroup.centralizer (X : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have ha_mem_centy : (a : G) ∈ Subgroup.centralizer ({(y : G)} : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      rw [Set.mem_singleton_iff.mp hu]
      exact hacomm.symm
    have hz_mem_centy : z ∈ Subgroup.centralizer ({(y : G)} : Set G) :=
      (Subgroup.zpowers_le_of_mem ha_mem_centy) hz
    have hyz : (y : G) * z = z * (y : G) :=
      (Subgroup.mem_centralizer_iff.mp hz_mem_centy) (y : G) (by simp)
    exact hyz.symm
  have hynorm : (y : G) ∈ Subgroup.normalizer (X : Set G) :=
    centralizer_le_normalizer X hyCentralX
  exact (proposition_1_b H D Q t hA1 X hXne hXQ) hynorm

private theorem pPrimeCore_two_le_pointStabilizerCore
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q : Subgroup G) (t : G)
    (hA1 : HypothesisA1 G Ω H D Q t)
    (h2rank : TwoRankAtLeastTwo G) :
    (pPrimeCore 2 G) ≤ pointStabilizerCore G Ω := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨A, hAQ, hAcard, hAsq⟩ :=
    exists_rank_two_subgroup_le_Q H D Q t hA1 h2rank
  let O : Subgroup G := (pPrimeCore 2 G)
  letI : O.Normal := by
    simpa [O] using (pPrimeCore_normal (p := 2) (G := G))
  have hAcomm : IsMulCommutative A := isMulCommutative_of_forall_sq_one hAsq
  letI : IsMulCommutative A := hAcomm
  letI : CommGroup A := IsMulCommutative.instCommGroup
  haveI : Fact (IsPGroup 2 A) := by
    refine ⟨IsPGroup.of_card (p := 2) (G := A) (n := 2) ?_⟩
    norm_num [hAcard]
  have hncyc : ¬ IsCyclic A :=
    noncyclic_of_card_four_and_sq_one hAcard hAsq
  have hOcop : Nat.Coprime 2 (Nat.card O) := by
    simpa [O] using (pPrimeCore_coprime_card (G := G) (p := 2))
  have hgen :
      (⨆ (a : A) (_ : a ≠ 1), fixedPointSubgroup (↥(Subgroup.zpowers a)) O) =
        ⊤ := by
    exact proposition_1_16_a (G := O) (A := A) 2 hOcop hncyc
  have hsup_le :
      (⨆ (a : A) (_ : a ≠ 1), fixedPointSubgroup (↥(Subgroup.zpowers a)) O) ≤
        H.comap O.subtype := by
    refine iSup_le ?_
    intro a
    refine iSup_le ?_
    intro ha
    exact fixedPoint_zpowers_le_H H D Q A O t hA1 hAQ a ha
  have hO_le_H : O ≤ H := by
    intro x hxO
    have hxTop : (⟨x, hxO⟩ : O) ∈ (⊤ : Subgroup O) := trivial
    have hxComap : (⟨x, hxO⟩ : O) ∈ H.comap O.subtype := by
      exact hsup_le (by simp [hgen])
    exact hxComap
  obtain ⟨α, hH⟩ := hA1.point_stabilizer
  haveI : MulAction.IsMultiplyPretransitive G Ω 2 := hA1.two_transitive
  have htrans : MulAction.IsPretransitive G Ω :=
    MulAction.isPretransitive_of_is_two_pretransitive
  have hO_le_stab : (pPrimeCore 2 G) ≤ MulAction.stabilizer G α := by
    simpa [O, hH] using hO_le_H
  exact pPrimeCore_two_le_pointStabilizerCore_of_le_stabilizer htrans hO_le_stab

-- Since H is a stablizer of a point, the pointStablizerCore is equivalent to the intersection of all conjugates of H.
public theorem proposition_1_e
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q : Subgroup G) (t : G)
    (hA1 : HypothesisA1 G Ω H D Q t) :
    TwoRankAtLeastTwo G → (pPrimeCore 2 G) = pointStabilizerCore G Ω := by
  intro h2rank
  exact le_antisymm
    (pPrimeCore_two_le_pointStabilizerCore H D Q t hA1 h2rank)
    (pointStabilizerCore_le_pPrimeCore_two H D Q t hA1)

end PFchapter1section1
end CFSG.BenderSuzuki
