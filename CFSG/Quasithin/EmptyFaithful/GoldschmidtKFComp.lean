module

public import CFSG.GroupTheory.LocalCores.Layer
public import CFSG.RankThree.PartTwo.Sec5.Tools
public import CFSG.RankThree.GroupTheory.SteinbergBYAschCoreConjugacy
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.GroupTheory.LocalCores.PrimeSetCore

public section

namespace CFSG.Quasithin.SBd19F

open CFSG CFSG.LocalCores

variable {H : Type*} [Group H] [Finite H]

theorem layer_le_sup_centralizer {C : Subgroup H} (hC : IsComponent C) :
    layer H ≤ C ⊔ Subgroup.centralizer (C : Set H) := by
  refine sSup_le fun K hK => ?_
  rcases distinct_components_commute hK hC with rfl | h
  · exact le_sup_left
  · exact le_sup_of_le_right (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h)

omit [Finite H] in
theorem isComponent_conj {K : Subgroup H} (hK : IsComponent K) (g : H) :
    IsComponent (K.map (MulAut.conj g).toMonoidHom) :=
  ((component_isomorphism (MulAut.conj g)).1 K).1 hK

theorem commutator_eq_bot_of_not_three_dvd {Q C : Subgroup H} (hQ : IsQuasisimple ↥Q)
    (hQE : Q ≤ layer H) (hC : IsComponent C) (h3 : 3 ∣ (Subgroup.center ↥Q).index)
    (hC3 : ¬ 3 ∣ Nat.card ↥C) : ⁅Q, C⁆ = ⊥ := by
  classical
  have hQN : Q ≤ Subgroup.normalizer (C : Set H) := hQE.trans (layer_le_normalizer hC)
  let φ : ↥Q →* MulAut ↥C := C.normalizerMonoidHom.comp (Subgroup.inclusion hQN)
  have hφ : ∀ (g : ↥Q) (x : ↥C), ((φ g x : ↥C) : H) = (g : H) * (x : H) * (g : H)⁻¹ := fun g x =>
    C.normalizerMonoidHom_apply_apply_coe ⟨(g : H), hQN g.2⟩ x
  rcases quasisimple_normal_subgroups hQ φ.normal_ker with hN | hN
  · rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro g hg
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    have h1 : φ ⟨g, hg⟩ = 1 := by
      have : (⟨g, hg⟩ : ↥Q) ∈ φ.ker := by rw [hN]; exact Subgroup.mem_top _
      exact this
    have h2 := congrArg (fun e : MulAut ↥C => ((e ⟨c, hc⟩ : ↥C) : H)) h1
    simp only [hφ, MulAut.one_apply] at h2
    calc c * g = (g * c * g⁻¹) * g := by rw [h2]
      _ = g * c := by group
  · exfalso
    have hidx : (Subgroup.center ↥Q).index ∣ φ.ker.index := Subgroup.index_dvd_of_le hN
    rw [Subgroup.index_ker] at hidx
    have hrange : φ.range ≤ (MulAut.conj : ↥C →* MulAut ↥C).range := by
      rintro _ ⟨g, rfl⟩
      have hg : (g : H) ∈ C ⊔ Subgroup.centralizer (C : Set H) :=
        layer_le_sup_centralizer hC (hQE g.2)
      rw [sup_comm] at hg
      have hset := Subgroup.coe_mul_of_left_le_normalizer_right (Subgroup.centralizer (C : Set H)) C
        (Subgroup.centralizer_le_normalizer (C : Set H) |> fun h => by simpa using h)
      have hg' : (g : H) ∈ ((Subgroup.centralizer (C : Set H) ⊔ C : Subgroup H) : Set H) := hg
      rw [hset] at hg'
      obtain ⟨z, hz, c, hc, hgzc⟩ := hg'
      refine ⟨⟨c, hc⟩, ?_⟩
      ext x
      rw [hφ, MulAut.conj_apply]
      have hzc : ∀ w ∈ C, z * w = w * z := fun w hw =>
        (Subgroup.mem_centralizer_iff.mp hz w hw).symm
      have hcxc : c * (x : H) * c⁻¹ ∈ C := C.mul_mem (C.mul_mem hc x.2) (C.inv_mem hc)
      change c * (x : H) * c⁻¹ = (g : H) * (x : H) * (g : H)⁻¹
      rw [← hgzc]
      calc c * (x : H) * c⁻¹ = (c * (x : H) * c⁻¹) * z * z⁻¹ := by group
        _ = z * (c * (x : H) * c⁻¹) * z⁻¹ := by rw [hzc _ hcxc]
        _ = z * c * (x : H) * (z * c)⁻¹ := by group
    have hdvd1 : Nat.card φ.range ∣ Nat.card (MulAut.conj : ↥C →* MulAut ↥C).range :=
      Subgroup.card_dvd_of_le hrange
    have hdvd2 : Nat.card (MulAut.conj : ↥C →* MulAut ↥C).range ∣ Nat.card ↥C :=
      Dvd.intro_left _ (Subgroup.card_ker_mul_card_range _)
    exact hC3 (((h3.trans hidx).trans hdvd1).trans hdvd2)

omit [Finite H] in
theorem isPGroup_zpowers_of_cube {G : Type*} [Group G] {x : G} (hx : x ^ 3 = 1) :
    IsPGroup 3 (Subgroup.zpowers x) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp
    (show orderOf x ∣ 3 ^ 1 by rw [pow_one]; exact orderOf_dvd_of_pow_eq_one hx)
  exact IsPGroup.of_card (n := i) (by rw [Nat.card_zpowers, hi])

omit [Finite H] in
theorem isElemAbelian_zpowers_of_cube {G : Type*} [Group G] {a : G} (ha : a ^ 3 = 1) :
    CFSG.Assembly.IsElemAbelian 3 (Subgroup.zpowers a) := CFSG.Open.isElemAbelian_zpowers ha

omit [Finite H] in
theorem pRank_map_conj [Finite H] (K : Subgroup H) (g : H) :
    CFSG.Open.pRank 3 (K.map (MulAut.conj g).toMonoidHom) = CFSG.Open.pRank 3 K :=
  CFSG.RankThree.GroupTheory.SteinbergBY.assembly_pRank_map_mulEquiv (by norm_num)
    (MulAut.conj g) K

omit [Finite H] in
theorem not_three_dvd_card_of_pRank_eq_zero [Finite H] {C : Subgroup H}
    (h0 : CFSG.Open.pRank 3 C = 0) : ¬ 3 ∣ Nat.card C := by
  intro hdvd
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥C) 3 hdvd
  have hx3 : (x : H) ^ 3 = 1 := by
    have := pow_orderOf_eq_one x
    rw [hx] at this
    simpa using congrArg Subtype.val this
  have h1 : 1 ≤ CFSG.Open.pRank 3 C :=
    CFSG.RankThree.PartTwo.Sec5.le_pRank_of_elemAbelian Nat.prime_three
      (Subgroup.zpowers_le.mpr x.2) (isElemAbelian_zpowers_of_cube hx3) (k := 1) (by
        rw [Nat.card_zpowers, Subgroup.orderOf_coe, hx, pow_one])
  omega

end CFSG.Quasithin.SBd19F
