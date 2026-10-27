module

public import CFSG.RankThree.PartOne.F106.OddRadTools
public import CFSG.RankThree.PartOne.K133H.SylowTorus
public import CFSG.RankThree.PartOne.K128.G2Syl

public section

namespace CFSG.RankThree.PartOne.F106

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.RankThree.PartOne.K128 CFSG.Timmesfeld.ExceptionalOrders
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

set_option linter.unusedSectionVars false

theorem factorization_card_adjointGroup_G2 {K : Type} [Field K] [Finite K] {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ Nat.card K - 1) :
    (Nat.card ↥(adjointGroup .G2 K)).factorization p =
      (Nat.card ↥(torusGroup .G2 K)).factorization p := by
  have hQ : 2 ≤ Nat.card K := Finite.one_lt_card
  have hpK : ¬ p ∣ Nat.card K := by
    intro h
    have h1 : p ∣ Nat.card K - (Nat.card K - 1) := Nat.dvd_sub h hpq
    rw [show Nat.card K - (Nat.card K - 1) = 1 by omega] at h1
    exact hp.one_lt.ne' (Nat.dvd_one.1 h1)
  have hdQ : p ∣ Nat.card K ^ 2 - 1 := by
    rw [sq_sub_one_eq _ (by omega)]
    exact hpq.mul_right _
  have hnQ1 : ¬ p ∣ Nat.card K + 1 := by
    intro h
    have h1 : p ∣ (Nat.card K + 1) - (Nat.card K - 1) := Nat.dvd_sub h hpq
    rw [show (Nat.card K + 1) - (Nat.card K - 1) = 2 by omega] at h1
    have := Nat.le_of_dvd (by norm_num) h1
    omega
  have hvp : (Nat.card K ^ 2 - 1).factorization p = (Nat.card K - 1).factorization p := by
    rw [sq_sub_one_eq _ (by omega), Nat.factorization_mul (by omega) (by omega),
      Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hnQ1, add_zero]
  rw [card_adjointGroup_G2, card_torusGroup_G2, factorization_ordG2 hp hp5 hQ hpK hdQ, hvp,
    Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]

theorem oddRad_G2_split {K : Type} [Field K] [Finite K] [CharP K 2] (hq : 5 ∣ Nat.card K - 1)
    (x : adjointGroup .G2 K) (hx : orderOf x = 5) :
    Odd (Nat.card ↥(solvableRadical ↥(perfectResidual ↥(Subgroup.centralizer {x})))) := by
  classical
  have hp : (5 : ℕ).Prime := by norm_num
  have : Fact (5 : ℕ).Prime := ⟨hp⟩
  have : Finite (ModGL .G2 K) := finite_modGL
  have hq4 : 4 ≤ Nat.card K := by
    have := EvenG2.six_le_card_of_dvd (K := K) hp (by norm_num) hq
    omega
  have hxM : ((x : adjointGroup .G2 K) : ModGL .G2 K) ^ 5 = 1 := by
    have := pow_orderOf_eq_one x
    rw [hx] at this
    exact congrArg Subtype.val this
  obtain ⟨γ, hγC, hγ⟩ := K133H.exists_conj_le_of_sylow (p := 5) (Y := adjointGroup .G2 K)
    (H := torusGroup .G2 K) (A := Subgroup.zpowers ((x : adjointGroup .G2 K) : ModGL .G2 K))
    torusGroup_le_adjointGroup' (Subgroup.zpowers_le.2 x.2)
    (fun y hy => by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hxM, one_zpow])
    (factorization_card_adjointGroup_G2 hp le_rfl hq)
  have hx'T : γ * ((x : adjointGroup .G2 K) : ModGL .G2 K) * γ⁻¹ ∈ torusGroup .G2 K :=
    hγ (Subgroup.mem_map.2 ⟨_, Subgroup.mem_zpowers _, rfl⟩)
  obtain ⟨a, ha⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hx'T
  have hord : orderOf (rootDiagUnit .G2 a) = 5 := by
    rw [← ha, ← MulAut.conj_apply, ← MulEquiv.coe_toMonoidHom,
      orderOf_injective _ (MulAut.conj γ).injective, Subgroup.orderOf_coe, hx]
  have h1 := card_radical_residual_of_embedding (adjointGroup .G2 K).subtype
    Subtype.val_injective x
  rw [Subgroup.range_subtype] at h1
  have h2 := card_radical_residual_conj (adjointGroup .G2 K) hγC
    ((x : adjointGroup .G2 K) : ModGL .G2 K)
  have h3 : Subgroup.centralizer ({γ * ((x : adjointGroup .G2 K) : ModGL .G2 K) * γ⁻¹} :
      Set (ModGL .G2 K)) = Subgroup.centralizer {rootDiagUnit .G2 a} := by rw [ha]
  rw [Subgroup.coe_subtype] at h1
  rw [h1, ← h2, ha]
  refine odd_card_radical_residual_of_dichotomy (toralCentralizer .G2 K a) ?_
  rcases EvenG2.toral_centralizer_cases_G2_of_charTwo K hp (by norm_num) hq a hord with
    ⟨-, hX⟩ | ⟨α, hα, -, -, -, hcomm, -, -⟩
  · left
    rw [hX]
    exact fun u hu v hv => (triangular_borel_structure.{0, 0} .G2 K).1 u hu v hv
  · right
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hfin⟩ := even_Chevalley_pinned_root_SL2_maps .G2 K hα
    obtain ⟨hs, hper, -⟩ := hfin inferInstance hq4
    exact ⟨_, hcomm, hs, hper⟩

theorem oddRad_G2_qplus {K : Type} [Field K] [Finite K] [CharP K 2] (hq : 5 ∣ Nat.card K + 1)
    (x : adjointGroup .G2 K) (hx : orderOf x = 5) :
    Odd (Nat.card ↥(solvableRadical ↥(perfectResidual ↥(Subgroup.centralizer {x})))) := by
  classical
  have hp : (5 : ℕ).Prime := by norm_num
  have : Fact (5 : ℕ).Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdeg : Module.finrank K (FiniteField.Extension K 2 2) = 2 :=
    FiniteField.finrank_extension K 2 2
  let σ : FiniteField.Extension K 2 2 ≃+* FiniteField.Extension K 2 2 :=
    (FiniteField.Extension.frob K 2 2).toRingEquiv
  have hσ : ∀ c, σ c = c ^ Nat.card K := fun c => FiniteField.Extension.frob_apply K 2 2 (x := c)
  obtain ⟨g, z, hg, hzC, hzdef, hz, hΓ, hF2, ⟨φT⟩, hTodd, ⟨S, hS⟩, ⟨E, hE⟩, hrank1, huniq, hcent⟩ :=
    even_G2_qplus_torus_and_fixed_root_centralizers K hp (by norm_num) hq
      (FiniteField.Extension K 2 2) hdeg σ hσ
  have : Finite (ModGL .G2 (FiniteField.Extension K 2 2)) := finite_modGL
  have hord5 := factorization_eq_of_sylow_le (p := 5)
    (inf_le_right : torusGroup .G2 (FiniteField.Extension K 2 2) ⊓ conjEntrywiseImage K g ≤
      conjEntrywiseImage K g) S hS
  set Γ := conjEntrywiseImage K g with hΓdef
  have hTΓ : torusGroup .G2 (FiniteField.Extension K 2 2) ⊓ Γ ≤ Γ := inf_le_right
  let ψ : ModGL .G2 K →* ModGL .G2 (FiniteField.Extension K 2 2) :=
    (MulAut.conj g).toMonoidHom.comp (baseChangeGL (algebraMap K (FiniteField.Extension K 2 2)))
  have hψ : Function.Injective ψ :=
    (MulAut.conj g).injective.comp (baseChangeGL_injective (τ := .G2) _)
  let ι : ↥(adjointGroup .G2 K) →* ModGL .G2 (FiniteField.Extension K 2 2) :=
    ψ.comp (adjointGroup .G2 K).subtype
  have hι : Function.Injective ι := hψ.comp Subtype.val_injective
  have hrange : ι.range = Γ := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rfl
  have hιx : ι x ∈ Γ := hrange ▸ ⟨x, rfl⟩
  have hιxM : (ι x) ^ 5 = 1 := by
    have := pow_orderOf_eq_one x
    rw [hx] at this
    rw [← map_pow, this, map_one]
  obtain ⟨γ, hγΓ, hγ⟩ := K133H.exists_conj_le_of_sylow (p := 5) (Y := Γ)
    (H := torusGroup .G2 (FiniteField.Extension K 2 2) ⊓ Γ) (A := Subgroup.zpowers (ι x)) hTΓ
    (Subgroup.zpowers_le.2 hιx)
    (fun y hy => by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hιxM, one_zpow])
    hord5
  have hx'T : γ * ι x * γ⁻¹ ∈ torusGroup .G2 (FiniteField.Extension K 2 2) ⊓ Γ :=
    hγ (Subgroup.mem_map.2 ⟨_, Subgroup.mem_zpowers _, rfl⟩)
  obtain ⟨a, ha, -⟩ := huniq _ hx'T
  have hord : orderOf (rootDiagUnit .G2 a) = 5 := by
    rw [ha, ← MulAut.conj_apply, ← MulEquiv.coe_toMonoidHom,
      orderOf_injective _ (MulAut.conj γ).injective, orderOf_injective _ hι, hx]
  have haT : rootDiagUnit .G2 a ∈ torusGroup .G2 (FiniteField.Extension K 2 2) ⊓ Γ := ha ▸ hx'T
  have h1 := card_radical_residual_of_embedding ι hι x
  rw [hrange] at h1
  have h2 := card_radical_residual_conj Γ hγΓ (ι x)
  rw [h1, ← h2, ← ha]
  refine odd_card_radical_residual_of_dichotomy
    (Γ ⊓ Subgroup.centralizer {rootDiagUnit .G2 a}) ?_
  obtain ⟨hreg, hsing, -⟩ := hcent a haT hord
  by_cases hk : rootCharKernel a = ∅
  · left
    rw [hreg hk]
    exact fun u hu v hv => (triangular_borel_structure.{0, 0} .G2
      (FiniteField.Extension K 2 2)).1 u hu.1 v hv.1
  · right
    obtain ⟨α, hα, -, hcomm, -, -⟩ := hsing hk
    obtain ⟨-, -, hs, hper, -⟩ := hrank1 α hα
    exact ⟨_, hcomm, hs, hper⟩

end CFSG.RankThree.PartOne.F106
