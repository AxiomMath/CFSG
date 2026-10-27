module

public import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherClassicalRk2LU4Weyl
public import CFSG.LieType.Ree.FixedSubgroupData
public import CFSG.LieType.Ree.ReeHolds
public import CFSG.RankThree.PartOne.SEITZ3.PlaneCount
public import Certificates.Certificate117
import CFSG.LieType.Ree.LargeReeFixedGroupOddCore
import CFSG.RankThree.PartTwo.Sec19.SeitzG2F4ReeF4Conj
import CFSG.RankThree.PartTwo.Sec21.ReeF4ThreeLocalProofRank
import CFSG.RankThree.PartTwo.Sec8.Steps

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.LieType.Ree
open CFSG.RankThree.PartOne.SEITZ3 (cj mem_cj card_cj cj_cj pow_eq_one_of_mem_cj
  mem_normalizer_iff_cj)


theorem eq_bot_or_eq_of_conj_twF4Three {G : Type*} [Group G] {D : Subgroup G}
    (hD : ∀ g g' : G, g ∉ D → g' ∉ D → g⁻¹ * g' ∈ D) {E E' : Subgroup G} (hE'E : E' ≤ E)
    (htrans : ∀ x ∈ E, ∀ x' ∈ E, x ≠ 1 → x' ≠ 1 →
      ∃ h ∈ Subgroup.normalizer (E : Set G), h * x * h⁻¹ = x')
    (hinv : ∀ h ∈ D, h ∈ Subgroup.normalizer (E : Set G) → ∀ e ∈ E', h * e * h⁻¹ ∈ E') :
    E' = ⊥ ∨ E' = E := by
  by_contra hne
  push Not at hne
  obtain ⟨hbot, htop⟩ := hne
  obtain ⟨⟨x, hxE'⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hbot
  have hx1' : x ≠ 1 := fun h => hx1 (Subtype.ext h)
  obtain ⟨x', hx'E, hx'E'⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hE'E htop)
  have hx'1 : x' ≠ 1 := fun h => hx'E' (h ▸ E'.one_mem)
  obtain ⟨h, hhN, hhx⟩ := htrans x (hE'E hxE') x' hx'E hx1' hx'1
  have hhD : h ∉ D := fun hD' => hx'E' (hhx ▸ hinv h hD' hhN x hxE')
  have hx'' : h⁻¹ * x' * h = x := by rw [← hhx]; group
  obtain ⟨c, hcE, hcE', hcE''⟩ : ∃ c ∈ E, c ∉ E' ∧ h⁻¹ * c * h ∉ E' := by
    have hbE : h * x' * h⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.1 hhN x').1 hx'E
    have hb : h⁻¹ * (h * x' * h⁻¹) * h ∉ E' := by
      have e : h⁻¹ * (h * x' * h⁻¹) * h = x' := by group
      rw [e]
      exact hx'E'
    by_cases hbE' : h * x' * h⁻¹ ∈ E'
    · refine ⟨x' * (h * x' * h⁻¹), E.mul_mem hx'E hbE, fun hm => hx'E' ?_, fun hm => hb ?_⟩
      · have e : x' * (h * x' * h⁻¹) * (h * x' * h⁻¹)⁻¹ = x' := by group
        rw [← e]
        exact E'.mul_mem hm (E'.inv_mem hbE')
      · have e : h⁻¹ * (h * x' * h⁻¹) * h =
            (h⁻¹ * x' * h)⁻¹ * (h⁻¹ * (x' * (h * x' * h⁻¹)) * h) := by group
        rw [e, hx'']
        exact E'.mul_mem (E'.inv_mem hxE') hm
    · exact ⟨h * x' * h⁻¹, hbE, hbE', hb⟩
  have hc1 : c ≠ 1 := fun h1 => hcE' (h1 ▸ E'.one_mem)
  obtain ⟨k, hkN, hkx⟩ := htrans x (hE'E hxE') c hcE hx1' hc1
  by_cases hkD : k ∈ D
  · exact hcE' (hkx ▸ hinv k hkD hkN x hxE')
  · have hm := hinv _ (hD h k hhD hkD) (mul_mem (inv_mem hhN) hkN) x hxE'
    apply hcE''
    have e : h⁻¹ * k * x * (h⁻¹ * k)⁻¹ = h⁻¹ * (k * x * k⁻¹) * h := by group
    rwa [e, hkx] at hm

theorem ggWeylIrred_of_conj_twF4Three {G : Type} [Group G] {D : Subgroup G}
    (hD : ∀ g g' : G, g ∉ D → g' ∉ D → g⁻¹ * g' ∈ D) {E : Subgroup D}
    (htrans : ∀ x ∈ E.map D.subtype, ∀ x' ∈ E.map D.subtype, x ≠ 1 → x' ≠ 1 →
      ∃ h ∈ Subgroup.normalizer ((E.map D.subtype : Subgroup G) : Set G), h * x * h⁻¹ = x') :
    GGWeylIrred E := by
  intro E' hE'E hinv
  have hinv' : ∀ h ∈ D, h ∈ Subgroup.normalizer ((E.map D.subtype : Subgroup G) : Set G) →
      ∀ e ∈ E'.map D.subtype, h * e * h⁻¹ ∈ E'.map D.subtype := by
    intro h hhD hhN e he
    obtain ⟨e₀, he₀, rfl⟩ := Subgroup.mem_map.1 he
    have hN : (⟨h, hhD⟩ : D) ∈ Subgroup.normalizer (E : Set D) := by
      rw [Subgroup.mem_normalizer_iff]
      intro z
      have hz := Subgroup.mem_normalizer_iff.1 hhN (z : G)
      have h1 : (z : G) ∈ E.map D.subtype ↔ z ∈ E :=
        Subgroup.mem_map_iff_mem D.subtype_injective
      have h2 : h * (z : G) * h⁻¹ ∈ E.map D.subtype ↔ (⟨h, hhD⟩ * z * ⟨h, hhD⟩⁻¹ : D) ∈ E :=
        Subgroup.mem_map_iff_mem (x := (⟨h, hhD⟩ * z * ⟨h, hhD⟩⁻¹ : D)) D.subtype_injective
      rw [← h1, hz, h2]
    exact Subgroup.mem_map.2 ⟨_, hinv _ hN e₀ he₀, rfl⟩
  have hinj := Subgroup.map_injective D.subtype_injective
  obtain h | h := eq_bot_or_eq_of_conj_twF4Three hD (Subgroup.map_mono hE'E) htrans hinv'
  · left
    apply hinj
    rw [h, Subgroup.map_bot]
  · exact Or.inr (hinj h)

open CFSG.RankThree.PartTwo.Sec8 CFSG.RankThree.PartTwo.Sec19 CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial in
theorem exists_cj_eq_conj_twF4Three
    (a : ℕ) {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {E : Subgroup (ReeTag.F4.reeGamma K a)}
    (hE : IsElemAbelian 3 E) (hc : Nat.card E = 9) {x x' : ReeTag.F4.reeGamma K a}
    (hx : x ∈ E) (hx' : x' ∈ E) (hx1 : x ≠ 1) (hx1' : x' ≠ 1) :
    ∃ h : ReeTag.F4.reeGamma K a, cj E h = E ∧ h * x * h⁻¹ = x' := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨y, hy3, ⟨φ⟩⟩ := Item8KFacts2Proof.exists_centralizer_mulEquiv_unitarySU a K hK
  set C := Subgroup.centralizer ({y} : Set (ReeTag.F4.reeGamma K a)) with hC
  set K' := GaloisField 2 (2 * (2 * a + 1)) with hK'
  have h : UnitaryFieldData 2 (2 * a + 1) K' :=
    ⟨Nat.prime_two, by omega, GaloisField.card 2 _ (by omega)⟩
  have hcomm : ∀ u ∈ E, ∀ v ∈ E, u * v = v * u := by
    have := hE.1
    intro u hu v hv
    exact congrArg Subtype.val (IsMulCommutative.is_comm.comm (⟨u, hu⟩ : E) ⟨v, hv⟩)
  have key : ∀ z ∈ E, z ≠ 1 → ∃ g : ReeTag.F4.reeGamma K a, g * z * g⁻¹ = y ∧ cj E g ≤ C ∧
      ∃ S : Subgroup (unitarySU 2 (2 * a + 1) K' 3),
        (∀ u ∈ S, ∀ v ∈ S, u * v = v * u) ∧ (∀ u ∈ S, u ^ 3 = 1) ∧ Nat.card S = 9 ∧
        S = ((cj E g).subgroupOf C).map φ.toMonoidHom := by
    intro z hzE hz1
    obtain ⟨g, hg⟩ := Item8KFacts3Ree.reeGamma_orderThree_conj a K hK z y
      (orderOf_eq_prime (hE.2 z hzE) hz1) hy3
    have hFcomm : ∀ u ∈ cj E g, ∀ v ∈ cj E g, u * v = v * u := by
      intro u hu v hv
      have h1 := hcomm _ (mem_cj.1 hu) _ (mem_cj.1 hv)
      have h2 : g * ((g⁻¹ * u * g) * (g⁻¹ * v * g)) * g⁻¹ = u * v := by group
      have h3 : g * ((g⁻¹ * v * g) * (g⁻¹ * u * g)) * g⁻¹ = v * u := by group
      rw [← h2, ← h3, h1]
    have hFC : cj E g ≤ C := by
      intro w hw
      rw [hC, Subgroup.mem_centralizer_singleton_iff]
      have hy : y ∈ cj E g := by
        rw [mem_cj, ← hg]
        have e : g⁻¹ * (g * z * g⁻¹) * g = z := by group
        rw [e]
        exact hzE
      exact hFcomm _ hw _ hy
    refine ⟨g, hg, hFC, ((cj E g).subgroupOf C).map φ.toMonoidHom, ?_, ?_, ?_, rfl⟩
    · rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hFcomm _ hu _ hv)
    · rintro _ ⟨u, hu, rfl⟩
      rw [← map_pow]
      have : u ^ 3 = 1 := Subtype.ext (pow_eq_one_of_mem_cj hE.2 hu)
      rw [this, map_one]
    · rw [Subgroup.card_map_of_injective φ.injective,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFC).toEquiv, card_cj, hc]
  obtain ⟨g, hgy, hgC, S, hSc, hSe, hSn, hSdef⟩ := key x hx hx1
  obtain ⟨g', hgy', hgC', S', hSc', hSe', hSn', hSdef'⟩ := key x' hx' hx1'
  obtain ⟨s, hs⟩ := su3_planes_conj h (odd_two_mul_add_one a) S S' hSc hSe hSn hSc' hSe' hSn'
  set t : C := φ.symm s with ht
  have hmap : cj ((cj E g).subgroupOf C) t = (cj E g').subgroupOf C := by
    apply Subgroup.map_injective (f := φ.toMonoidHom) φ.injective
    rw [cj_map_equiv, ← hSdef, ht, MulEquiv.apply_symm_apply, hs, hSdef']
  have hFF : cj (cj E g) (t : ReeTag.F4.reeGamma K a) = cj E g' := by
    have h1 := congrArg (Subgroup.map C.subtype) hmap
    rw [cj_map_subtype, Subgroup.map_subgroupOf_eq_of_le hgC,
      Subgroup.map_subgroupOf_eq_of_le hgC'] at h1
    exact h1
  have hty : (t : ReeTag.F4.reeGamma K a) * y = y * t :=
    Subgroup.mem_centralizer_singleton_iff.1 t.2
  set τ : ReeTag.F4.reeGamma K a := (t : ReeTag.F4.reeGamma K a) with hτ
  refine ⟨g'⁻¹ * τ * g, ?_, ?_⟩
  · calc cj E (g'⁻¹ * τ * g) = cj (cj E (τ * g)) g'⁻¹ := by rw [su3_cj_mul_cj, mul_assoc]
      _ = cj (cj (cj E g) τ) g'⁻¹ := by rw [su3_cj_mul_cj E g τ]
      _ = cj (cj E g') g'⁻¹ := by rw [hFF]
      _ = E := cj_cj
  · have e1 : g'⁻¹ * τ * g * x * (g'⁻¹ * τ * g)⁻¹ =
        g'⁻¹ * ((τ * (g * x * g⁻¹)) * τ⁻¹) * g' := by group
    rw [e1, hgy, hty, mul_inv_cancel_right, ← hgy']
    group

open CFSG.RankThree.PartTwo.Sec19 (cj_map_equiv) 
in
theorem exists_normalizer_conj_twF4Three
    (a : ℕ) {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {G : Type*} [Group G] (e : G ≃* ReeTag.F4.reeGamma K a)
    {E : Subgroup G} (hE : IsElemAbelian 3 E) (h9 : 9 ≤ Nat.card E) {x x' : G} (hx : x ∈ E)
    (hx' : x' ∈ E) (hx1 : x ≠ 1) (hx1' : x' ≠ 1) :
    ∃ h ∈ Subgroup.normalizer (E : Set G), h * x * h⁻¹ = x' := by
  have hcard : Nat.card (E.map e.toMonoidHom) = Nat.card E :=
    Subgroup.card_map_of_injective e.injective
  have hc : Nat.card (E.map e.toMonoidHom) = 9 :=
    le_antisymm (CFSG.RankThree.PartTwo.Sec21.ReeF4ThreeLocalProof.card_le_nine_of_reeGamma a K hK
      _ (hE.map e.toMonoidHom)) (hcard ▸ h9)
  obtain ⟨h, hhE, hhx⟩ := exists_cj_eq_conj_twF4Three a hK (hE.map e.toMonoidHom) hc
    (Subgroup.mem_map_of_mem e.toMonoidHom hx) (Subgroup.mem_map_of_mem e.toMonoidHom hx')
    (by simpa using hx1) (by simpa using hx1')
  refine ⟨e.symm h, ?_, ?_⟩
  · rw [mem_normalizer_iff_cj]
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    rw [cj_map_equiv, MulEquiv.apply_symm_apply, hhE]
  · apply e.injective
    simpa using hhx

theorem ggSCWeylIrredTwoLU4_reeGamma_twF4Three
    (a : ℕ) {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    GGSCWeylIrredTwoLU4 3 ↥(ReeTag.F4.reeGamma K a) := by
  intro E hE h9 _ E' hE'E hinv
  exact eq_bot_or_eq_of_conj_twF4Three (D := ⊤) (fun g _ hg => absurd (Subgroup.mem_top g) hg)
    hE'E (fun x hx x' hx' hx1 hx1' => exists_normalizer_conj_twF4Three a hK (MulEquiv.refl _) hE
      (by simpa using h9) hx hx' hx1 hx1') (fun h _ hN e he => hinv h hN e he)

theorem inv_mul_mem_commutator_twF4Three
    {k : Type} [Field k] [Finite k] [CharP k ReeTag.F4.prime] (hk : Nat.card k = 2)
    {g g' : reeFixed ReeTag.F4 k 0} (hg : g ∉ commutator (reeFixed ReeTag.F4 k 0))
    (hg' : g' ∉ commutator (reeFixed ReeTag.F4 k 0)) :
    g⁻¹ * g' ∈ commutator (reeFixed ReeTag.F4 k 0) := by
  set T := CFSG.LieType.Simplicity.titsData k hk
  set N := commutator (reeFixed ReeTag.F4 k 0) with hN
  set Q := QuotientGroup.mk' N with hQ
  have hQ1 : ∀ u, Q u = 1 ↔ u ∈ N := fun u => by
    rw [hQ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hg1 : Q T.g₁ ^ 2 = 1 := by
    rw [← map_pow, hQ1]
    exact T.g₁_sq_mem
  have hmem : ∀ u, u ∉ N → Q u = Q T.g₁ := by
    intro u hu
    have hzp : Q u ∈ Subgroup.zpowers (Q T.g₁) := by
      have h1 : Q u ∈ (N ⊔ Subgroup.zpowers T.g₁).map Q :=
        Subgroup.mem_map_of_mem Q ((T.commutator_sup_zpowers_eq_top hk) ▸ Subgroup.mem_top u)
      rwa [Subgroup.map_sup, hQ, QuotientGroup.map_mk'_self, bot_sup_eq,
        MonoidHom.map_zpowers] at h1
    obtain ⟨z, hz⟩ := Subgroup.mem_zpowers_iff.mp hzp
    have hz2 : Q T.g₁ ^ z = Q T.g₁ ^ (z % 2) := by
      have := zpow_eq_zpow_emod' z hg1
      rwa [Nat.cast_ofNat] at this
    rcases Int.emod_two_eq_zero_or_one z with h0 | h1
    · rw [← hQ1, ← hz, hz2, h0, zpow_zero] at hu
      exact absurd rfl hu
    · rw [← hz, hz2, h1, zpow_one]
  rw [← hQ1, map_mul, map_inv, hmem g hg, hmem g' hg', inv_mul_cancel]

theorem ggSCWeylIrredTwoLU4_tits_twF4Three
    {k : Type} [Field k] [Finite k] [CharP k ReeTag.F4.prime] (hk : Nat.card k = 2) :
    GGSCWeylIrredTwoLU4 3 ↥(commutator ↥(reeFixed ReeTag.F4 k 0)) := by
  intro E hE h9 _
  refine ggWeylIrred_of_conj_twF4Three
    (fun g g' hg hg' => inv_mul_mem_commutator_twF4Three hk hg hg') ?_
  intro x hx x' hx' hx1 hx1'
  refine exists_normalizer_conj_twF4Three 0 (by simpa using hk)
    (ReeTag.reeFixedEquivReeGamma k 0) (hE.map _) ?_ hx hx' hx1 hx1'
  rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
  simpa using h9

end CFSG.StandardType
