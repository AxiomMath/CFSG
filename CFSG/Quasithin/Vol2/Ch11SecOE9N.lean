module

public import CFSG.Quasithin.Vol2.Ch11SecOE9M
public import CFSG.Quasithin.Vol2.Ch11SecE3Sz
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bCent
public import CFSG.Quasithin.Vol2.Ch11SecOE7G
public import CFSG.Quasithin.Vol2.Ch11SecOE9I
public import CFSG.Quasithin.Vol2.Ch11SecU1Crit

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE3.Lie3.Sp4

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
open CFSG.Quasithin CFSG.Open CFSG.Blueprint

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem exists_member_of_not_le_odd {G : Type} [Group G]
    [Finite G] {L T : Subgroup G} (hAS : AlmostSimple L) (hT : IsSylowIn 2 T ⊤) {m : ℕ}
    (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ (2 * m + 1)) (ψ : antiSp K ≃* ↥L) {A : Subgroup G}
    (hA : IsElemAbelian 2 A) (hcA : 2 ^ (2 * m + 1) < Nat.card A) (hAL : ¬ A ≤ L) :
    ∃ g : G, A1b.conjSub g A ≤ T ∧ ∃ X : Subgroup G,
      E1.IsE (2 * m + 1) ⊤ T (A1b.conjSub g A) X ∧ ¬ Group.IsSolvable ↥X := by
  have hLn := hAS.normal
  have hC := hAS.centralizer_eq
  obtain ⟨a, haA, haL⟩ := IsConcreteLE.not_le_iff_exists.mp hAL
  obtain ⟨g, hgT, hsyl⟩ := SecU1.exists_conj_le_sylow hT hA haA
  set A' := A1b.conjSub g A with hA'def
  set a' := g * a * g⁻¹ with ha'def
  have ha'A : a' ∈ A' := by
    rw [hA'def, A1b.mem_conjSub_iff, ha'def, show g⁻¹ * (g * a * g⁻¹) * g = a by group]
    exact haA
  have ha'L : a' ∉ L := fun h' => haL (by
    have := hLn.conj_mem _ h' g⁻¹
    rwa [ha'def, show g⁻¹ * (g * a * g⁻¹) * g⁻¹⁻¹ = a by group] at this)
  have hA' : IsElemAbelian 2 A' := SecU1.isElemAbelian_conjSub hA g
  have hcA' : 2 ^ (2 * m + 1) < Nat.card A' := by
    rwa [hA'def, A1b.conjSub, Subgroup.card_map_of_injective (MulAut.conj g).injective]
  have h2 : ∀ x ∈ A', x * x = 1 := fun x hx => by rw [← pow_two]; exact hA'.2 x hx
  set θ := autHom ψ a' with hθ
  have hθ2 : θ * θ = 1 := by rw [hθ, ← map_mul, h2 a' ha'A, map_one]
  have hθi : θ ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner (antiSp K) := by
    intro hin
    obtain ⟨y, hy⟩ := MonoidHom.mem_range.mp hin
    exact ha'L ((eq_emb_of_autHom_eq ψ hC hy.symm) ▸ emb_mem ψ y)
  obtain ⟨c, hc⟩ := outer_involution_conj_odd hK θ hθ2 hθi
  set L₀ := (fixedSubgroup θ).map (emb ψ) with hL₀
  have hmemL₀ : ∀ y : G, y ∈ L₀ ↔ y ∈ L ∧ a' * y = y * a' := by
    intro y
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨emb_mem ψ x, ?_⟩
      have h1 := emb_autHom ψ a' x
      rw [← hθ, show θ x = x from hx] at h1
      calc a' * emb ψ x = a' * emb ψ x * a'⁻¹ * a' := by group
        _ = emb ψ x * a' := by rw [← h1]
    · rintro ⟨hyL, hy⟩
      obtain ⟨x, rfl⟩ := exists_emb_eq ψ hyL
      refine ⟨x, emb_injective ψ ?_, rfl⟩
      rw [hθ, emb_autHom, hy, mul_inv_cancel_right]
  have eL₀ : ↥L₀ ≃* suzukiGroup m K :=
    (((fixedSubgroup θ).equivMapOfInjective (emb ψ) (emb_injective ψ)).symm.trans
      (MulEquiv.subgroupCongr (by rw [hc]))).trans
      ((fixedSubgroupConjEquiv (MulAut.conj c) (minorAut K ^ (2 * m + 1))).symm.trans
        (fixedSubgroupEtaEquiv hK))
  have := (CFSG.LieType.Ree.suzuki_simple hm hK).2.2
  have hs : IsSimpleGroup ↥L₀ := eL₀.isSimpleGroup
  have hnab : ∃ x y : ↥L₀, x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ := SecE3.suzuki_nonabelian hm hK
    exact ⟨eL₀.symm x, eL₀.symm y, fun h => hxy (eL₀.symm.injective (by
      rw [map_mul, map_mul, h]))⟩
  have hZ := SecE3.center_eq_bot_of_simple hnab
  have hstep : ∀ t : G, t * a' = a' * t → ∀ y : G, y ∈ L₀ → t * y * t⁻¹ ∈ L₀ := by
    intro t ht y hy
    obtain ⟨hyL, hy⟩ := (hmemL₀ y).mp hy
    refine (hmemL₀ _).mpr ⟨hLn.conj_mem y hyL t, ?_⟩
    have ht' : t⁻¹ * a' = a' * t⁻¹ := by
      calc t⁻¹ * a' = t⁻¹ * (a' * t) * t⁻¹ := by group
        _ = t⁻¹ * (t * a') * t⁻¹ := by rw [ht]
        _ = a' * t⁻¹ := by group
    calc a' * (t * y * t⁻¹) = (a' * t) * y * t⁻¹ := by group
      _ = (t * a') * y * t⁻¹ := by rw [← ht]
      _ = t * (a' * y) * t⁻¹ := by group
      _ = t * (y * a') * t⁻¹ := by rw [hy]
      _ = t * y * (a' * t⁻¹) := by group
      _ = t * y * (t⁻¹ * a') := by rw [ht']
      _ = t * y * t⁻¹ * a' := by group
  have hCN : Subgroup.centralizer {a'} ≤ Subgroup.normalizer (L₀ : Set G) := by
    intro t ht
    rw [Subgroup.mem_centralizer_singleton_iff] at ht
    have hti : t⁻¹ * a' = a' * t⁻¹ := by
      calc t⁻¹ * a' = t⁻¹ * (a' * t) * t⁻¹ := by group
        _ = t⁻¹ * (t * a') * t⁻¹ := by rw [ht]
        _ = a' * t⁻¹ := by group
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨hstep t ht y, fun hy => ?_⟩
    have := hstep t⁻¹ hti _ hy
    rwa [show t⁻¹ * (t * y * t⁻¹) * t⁻¹⁻¹ = y by group] at this
  have hτN : E1.tauOf ⊤ T A' ≤ Subgroup.normalizer (L₀ : Set G) :=
    (tauOf_le_centralizer hAS ha'A).trans hCN
  have hL₀C : L₀ ≤ Subgroup.centralizer {a'} := fun y hy => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact ((hmemL₀ y).mp hy).2.symm
  have hL₀syl : IsSylowIn 2 (T ⊓ L₀) L₀ := by
    have h1 := B6.isSylowTwoOf_inf_normal (⟨hsyl.1, hsyl.2.1, hsyl.2.2⟩ :
      QuasithinUnique.IsSylowTwoOf (T ⊓ Subgroup.centralizer {a'}) (Subgroup.centralizer {a'}))
      hL₀C hCN
    rw [inf_assoc, inf_eq_right.mpr hL₀C] at h1
    exact ⟨h1.1, h1.2.1, h1.2.2⟩
  have ha'C : a' ∈ Subgroup.centralizer (L₀ : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact ((hmemL₀ y).mp hy).2.symm
  have hAL₀ : ∀ b ∈ A', b ∈ L → b ∈ L₀ := fun b hb hbL =>
    (hmemL₀ b).mpr ⟨hbL, E1.commute_of_isElemAbelian hA' ha'A hb⟩
  have hAL' : ∀ b ∈ A', ∃ l ∈ L₀, l⁻¹ * b ∈ Subgroup.centralizer (L₀ : Set G) := by
    intro b hb
    by_cases hbL : b ∈ L
    · exact ⟨b, hAL₀ b hb hbL, by rw [inv_mul_cancel]; exact Subgroup.one_mem _⟩
    · have hl : b * a'⁻¹ ∈ L := mul_inv_mem (by omega) hK ψ hC (h2 b hb) (h2 a' ha'A) hbL ha'L
      refine ⟨b * a'⁻¹, hAL₀ _ (A'.mul_mem hb (A'.inv_mem ha'A)) hl, ?_⟩
      rw [mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel, mul_one]
      exact ha'C
  have hAC : ¬ A' ≤ Subgroup.centralizer (L₀ : Set G) := by
    intro hle
    have hcard := card_le_two_mul_inf (by omega) hK ψ hC h2
    have hbot : A' ⊓ L ≠ ⊥ := by
      intro h
      rw [h, Subgroup.card_bot] at hcard
      have : 1 < 2 ^ (2 * m + 1) := Nat.one_lt_two_pow (by omega)
      omega
    obtain ⟨b, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hbot
    apply hb1
    have hbL₀ := hAL₀ b (Subgroup.mem_inf.mp b.2).1 (Subgroup.mem_inf.mp b.2).2
    have hz : (⟨b, hbL₀⟩ : ↥L₀) ∈ Subgroup.center ↥L₀ := Subgroup.mem_center_iff.mpr fun y =>
      Subtype.ext (Subgroup.mem_centralizer_iff.mp (hle (Subgroup.mem_inf.mp b.2).1) y y.2)
    rw [hZ, Subgroup.mem_bot] at hz
    have h3 : (b : G) = 1 := by simpa using congrArg Subtype.val hz
    exact Subtype.ext h3
  have hcardL₀ : ∀ E : Subgroup G, E ≤ L₀ → IsElemAbelian 2 E →
      Nat.card E ≤ 2 ^ (2 * m + 1) := by
    intro E hEL hE
    have h1 := SecE3.card_le_of_isElemAbelian_suzuki hK
      (SecE3.isElemAbelian_map eL₀.toMonoidHom (SecE3.isElemAbelian_subgroupOf hE L₀))
    rw [Subgroup.card_map_of_injective eL₀.injective, hK] at h1
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEL).toEquiv] at h1
  refine ⟨g, hgT, L₀ ⊔ E1.tauOf ⊤ T A', isE_sup_tauOf_of_simple hT hgT hA' hs hnab hτN hL₀syl
    hAC hAL' hcardL₀, fun hsol => ?_⟩
  exact SecU1.not_isSolvable_of_simple hnab (Group.isSolvable_of_isSolvable_injective
    (Subgroup.inclusion_injective (le_sup_left : L₀ ≤ L₀ ⊔ E1.tauOf ⊤ T A')))

end CFSG.Quasithin.Vol2.Ch11.SecE3.Lie3.Sp4
