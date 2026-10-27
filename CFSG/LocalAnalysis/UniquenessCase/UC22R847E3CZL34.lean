module

public import CFSG.LocalAnalysis.UniquenessCase.UC22InE229L34Row
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.L34AutModel
import CFSG.HardMathSupport.Meierfrankenfeld.L34Offender.L34Exclusion
import CFSG.Sporadic.FischerOddCore.AlmostSimple
import CFSG.Adapters.LinearCatalogStated
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229Z3Inv
public import CFSG.Quasithin.Background.A3StructureDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
open CFSG.RankThree.PartOne.Census3 (IsoLie)
open CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree
  (Gls3StronglyThreeEmbeddedPlus)

variable {G : Type} [Group G] [Finite G]

theorem R847E3.le_generalizedFitting_of_l34 (hG3 : Gls3StronglyThreeEmbeddedPlus)
    (hRee : CFSG.AGLEmbedding.KFactReeInvolution) (k : Sec7Core4 G) (hp3 : k.p = 3)
    {H : Subgroup G} (hH : Sec7Core4.Config k H)
    (hF : IsoLie ↥(CFSG.generalizedFitting (↥H ⧸ CFSG.pPrimeCore k.p ↥H))
      (.A 2 ⟨2, 2, Nat.prime_two, by norm_num⟩))
    {R : Subgroup (↥H ⧸ CFSG.pPrimeCore k.p ↥H)} (hR : IsPGroup 3 R) :
    R ≤ CFSG.generalizedFitting (↥H ⧸ CFSG.pPrimeCore k.p ↥H) := by
  have : Fact k.p.Prime := ⟨k.prime⟩
  have : (CFSG.generalizedFitting (↥H ⧸ CFSG.pPrimeCore k.p ↥H)).Normal :=
    CFSG.LocalCores.generalized_fitting_characteristic.2
  obtain ⟨P₀⟩ : Nonempty (Sylow k.p ↥(H ⊓ k.M)) := inferInstance
  obtain ⟨P', -, hP'N⟩ := k.exists_sylow_map_of_isSylowOf hH
    (P := (P₀ : Subgroup ↥(H ⊓ k.M)).map (H ⊓ k.M).subtype) ⟨P₀, rfl⟩
  obtain ⟨hrows, hNoRee, -⟩ := k.rows3_of_config hG3 hRee hp3 hH P'
  obtain ⟨⟨e, he⟩, -, -⟩ := uc22ine229_l34_rows (uc22ine229_l34_card hF) hrows
    (k.inf_eq_and_le_normalizer_quotient hG3 hp3 hH P' hP'N).1 hNoRee
  intro z hz
  obtain ⟨a, ha⟩ := hR ⟨z, hz⟩
  have hza : z ^ (3 ^ a) = 1 := by simpa using congrArg Subtype.val ha
  have hcop : Nat.Coprime (CFSG.generalizedFitting (↥H ⧸ CFSG.pPrimeCore k.p ↥H)).index
      (orderOf z) := by
    rw [he]
    exact Nat.Coprime.pow_left e (Nat.Coprime.coprime_dvd_right
      (orderOf_dvd_of_pow_eq_one hza) (Nat.Coprime.pow_right a (by decide)))
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  rw [← hm]
  exact Subgroup.pow_mem _ (Subgroup.pow_index_mem _ z) m

theorem R847E3.card_le_two_of_le_normalizer_l34
    (hG3 : Gls3StronglyThreeEmbeddedPlus) (hRee : CFSG.AGLEmbedding.KFactReeInvolution)
    (k : Sec7Core4 G) (hp3 : k.p = 3) {H : Subgroup G} (hH : Sec7Core4.Config k H)
    (hF : IsoLie ↥(CFSG.generalizedFitting (↥H ⧸ CFSG.pPrimeCore k.p ↥H))
      (.A 2 ⟨2, 2, Nat.prime_two, by norm_num⟩))
    {T B : Subgroup (↥H ⧸ CFSG.pPrimeCore k.p ↥H)} (hT : IsPGroup 2 T)
    (hB : IsElemAbelian 3 B) (hBc : Nat.card B = 3 ^ 2)
    (hBT : B ≤ normalizer (T : Set (↥H ⧸ CFSG.pPrimeCore k.p ↥H))) :
    Nat.card T ≤ 2 := by
  have hBF := R847E3.le_generalizedFitting_of_l34 hG3 hRee k hp3 hH hF hB.isPGroup
  set F := CFSG.generalizedFitting (↥H ⧸ CFSG.pPrimeCore k.p ↥H)
  have : F.Normal := CFSG.LocalCores.generalized_fitting_characteristic.2
  have hPSL : CFSG.Quasithin.IsPSL 3 2 2 ↥F := by
    obtain ⟨hv, ⟨ε⟩⟩ := hF
    exact CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv_typeA hv ε
  have hL : CFSG.AGLEmbedding.IsLinThreeFour ↥F := by
    obtain ⟨hv, hε⟩ := hF
    exact ⟨⟨_, hv⟩, ⟨⟨2, 2, Nat.prime_two, by norm_num⟩, rfl, rfl, rfl⟩, hε⟩
  have hC : centralizer (F : Set (↥H ⧸ CFSG.pPrimeCore k.p ↥H)) = ⊥ :=
    CFSG.Sporadic.FischerOddCore.centralizer_generalizedFitting_eq_bot_of_center
      (CFSG.HardMathSupport.Meierfrankenfeld.L34Offender.center_eq_bot_of_isLinThreeFour hL)
  let c : (↥H ⧸ CFSG.pPrimeCore k.p ↥H) →* MulAut ↥F := MulAut.conjNormal
  have hinj : Function.Injective c := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff, ← hC]
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h := congrArg (fun α : MulAut ↥F => ((α ⟨y, hy⟩ : ↥F) : ↥H ⧸ CFSG.pPrimeCore k.p ↥H))
      (MonoidHom.mem_ker.1 hx)
    simp only [c, MulAut.conjNormal_apply, MulAut.one_apply] at h
    calc y * x = x * y * x⁻¹ * x := by rw [h]
      _ = x * y := by group
  have hS₃ : Nat.card (B.subgroupOf F) = 9 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBF).toEquiv, hBc]
    norm_num
  have hnorm : ∀ s ∈ B.subgroupOf F, ∀ b ∈ T.map c,
      MulAut.conj s * b * (MulAut.conj s)⁻¹ ∈ T.map c := by
    intro s hs b hb
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.1 hb
    have hsN : (s : ↥H ⧸ CFSG.pPrimeCore k.p ↥H) ∈ normalizer (T : Set _) :=
      hBT (Subgroup.mem_subgroupOf.1 hs)
    refine ⟨(s : ↥H ⧸ CFSG.pPrimeCore k.p ↥H) * t * (s : ↥H ⧸ CFSG.pPrimeCore k.p ↥H)⁻¹,
      (Subgroup.mem_normalizer_iff.1 hsN t).1 ht, ?_⟩
    rw [show MulAut.conj s = c (s : ↥H ⧸ CFSG.pPrimeCore k.p ↥H) from
      (MulAut.conjNormal_val (h := s)).symm, ← map_mul, ← map_inv, ← map_mul]
  have h2 := (CFSG.LocalAnalysis.AGL81TheoremCD.Section14.l34_aut_two_subgroup hPSL (hT.map c)
    hS₃ (hB.subgroupOf F) hnorm).1
  rwa [Subgroup.card_map_of_injective hinj] at h2

theorem R847E3.eq_one_or_eq_of_l34
    (hG3 : Gls3StronglyThreeEmbeddedPlus) (hRee : CFSG.AGLEmbedding.KFactReeInvolution)
    (k : Sec7Core4 G) (hp3 : k.p = 3) {H : Subgroup G} (hH : Sec7Core4.Config k H)
    (hF : IsoLie ↥(CFSG.generalizedFitting (↥H ⧸ CFSG.pPrimeCore k.p ↥H))
      (.A 2 ⟨2, 2, Nat.prime_two, by norm_num⟩))
    {B₁ : Subgroup G} (hB₁H : B₁ ≤ H) (hB₁ : IsElemAbelian 3 B₁) (hB₁c : Nat.card B₁ = 3 ^ 2)
    {u s : G} (huH : u ∈ H) (hsH : s ∈ H) (hu : ∃ a : ℕ, u ^ 2 ^ a = 1)
    (hs : ∃ b : ℕ, s ^ 2 ^ b = 1) (hs1 : s ≠ 1) (hus : Commute u s)
    (hBu : ∀ b ∈ B₁, Commute b u) (hBs : ∀ b ∈ B₁, Commute b s) :
    u = 1 ∨ u = s := by
  have : Fact k.p.Prime := ⟨k.prime⟩
  obtain ⟨a, ha⟩ := hu
  obtain ⟨b, hb⟩ := hs
  obtain ⟨u', rfl⟩ : ∃ u' : ↥H, (u' : G) = u := ⟨⟨u, huH⟩, rfl⟩
  obtain ⟨s', rfl⟩ : ∃ s' : ↥H, (s' : G) = s := ⟨⟨s, hsH⟩, rfl⟩
  set K := CFSG.pPrimeCore k.p ↥H
  have hodd : Odd (Nat.card K) := k.odd_card_pPrimeCore_of_not_le hH.not_le hH.two_le_pRank
  have hK2 : ∀ x : ↥H, x ∈ K → ∀ n : ℕ, x ^ 2 ^ n = 1 → x = 1 := by
    intro x hx n hn
    have h1 : Odd (orderOf x) := hodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard K hx)
    exact orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd
      (Nat.Coprime.pow_right n h1.coprime_two_right) (orderOf_dvd_of_pow_eq_one hn))
  have ha' : u' ^ 2 ^ a = 1 := Subtype.ext (by simpa using ha)
  have hb' : s' ^ 2 ^ b = 1 := Subtype.ext (by simpa using hb)
  have hus' : Commute u' s' := Subtype.ext hus.eq
  have hU : IsPGroup 2 (zpowers u') := by
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one ha')
    exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
  have hS : IsPGroup 2 (zpowers s') := by
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hb')
    exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
  have hUS : zpowers u' ≤ normalizer ((zpowers s' : Subgroup ↥H) : Set ↥H) := by
    refine Subgroup.zpowers_le.2 (Subgroup.centralizer_le_normalizer _ ?_)
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure,
      Subgroup.mem_centralizer_singleton_iff]
    exact hus'.eq
  set π := QuotientGroup.mk' K
  set T : Subgroup (↥H ⧸ K) := (zpowers u' ⊔ zpowers s').map π
  have hT : IsPGroup 2 T := (IsPGroup.to_sup_of_normal_right' hU hS hUS).map π
  set B : Subgroup (↥H ⧸ K) := (B₁.subgroupOf H).map π
  have hB : IsElemAbelian 3 B := (hB₁.subgroupOf H).map π
  have hBc : Nat.card B = 3 ^ 2 := by
    have hker : ¬ 3 ∣ Nat.card π.ker := by
      rw [QuotientGroup.ker_mk']
      have h : Nat.Coprime k.p (Nat.card ↥K) := CFSG.pPrimeCore_coprime_card
      rw [hp3] at h
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 h
    rw [CFSG.RankThree.PartOne.N143.card_map_of_disjoint_ker _
      (CFSG.RankThree.PartOne.N143.disjoint_ker_of_isPGroup π Nat.prime_three
        (hB₁.subgroupOf H).isPGroup hker),
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hB₁H).toEquiv, hB₁c]
  have hBT : B ≤ normalizer (T : Set (↥H ⧸ K)) := by
    intro z hz
    obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.1 hz
    have hcB : (c : G) ∈ B₁ := Subgroup.mem_subgroupOf.1 hc
    have hle : zpowers u' ⊔ zpowers s' ≤ centralizer ({c} : Set ↥H) := by
      refine sup_le (Subgroup.zpowers_le.2 ?_) (Subgroup.zpowers_le.2 ?_)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact Subtype.ext (hBu _ hcB).eq.symm
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact Subtype.ext (hBs _ hcB).eq.symm
    refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 fun y hy => ?_)
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hy
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.1 (hle hx)]
  have hT2 := R847E3.card_le_two_of_le_normalizer_l34 hG3 hRee k hp3 hH hF hT hB hBc hBT
  have huT : π u' ∈ T :=
    Subgroup.mem_map_of_mem π (Subgroup.mem_sup_left (Subgroup.mem_zpowers u'))
  have hsT : π s' ∈ T :=
    Subgroup.mem_map_of_mem π (Subgroup.mem_sup_right (Subgroup.mem_zpowers s'))
  have hs1' : π s' ≠ 1 := fun h =>
    hs1 (congrArg Subtype.val (hK2 s' ((QuotientGroup.eq_one_iff _).1 h) b hb'))
  by_cases hu1 : π u' = 1
  · exact Or.inl (congrArg Subtype.val (hK2 u' ((QuotientGroup.eq_one_iff _).1 hu1) a ha'))
  refine Or.inr (congrArg Subtype.val ?_)
  have h : π u' = π s' := congrArg Subtype.val
    (uc22ine229_eq_of_ne_one hT2 (c := ⟨π u', huT⟩) (d := ⟨π s', hsT⟩)
      (fun h => hu1 (congrArg Subtype.val h)) fun h => hs1' (congrArg Subtype.val h))
  have hmem : u'⁻¹ * s' ∈ K := QuotientGroup.eq.1 h
  have hu2 : u' ^ 2 ^ (a + b) = 1 := by rw [pow_add, pow_mul, ha', one_pow]
  have hs2 : s' ^ 2 ^ (a + b) = 1 := by rw [pow_add, mul_comm, pow_mul, hb', one_pow]
  have hpow : (u'⁻¹ * s') ^ 2 ^ (a + b) = 1 := by
    rw [hus'.inv_left.mul_pow, inv_pow, hu2, hs2, inv_one, one_mul]
  exact inv_mul_eq_one.1 (hK2 _ hmem (a + b) hpow)

end CFSG.LocalAnalysis.UniquenessCase.UC22
