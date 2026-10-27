module

public import CFSG.RankThree.GF2n.Basic
import CFSG.GroupTheory.Fitting.CharacteristicP
import CFSG.RankThree.PartTwo.Sec5.Tools
import CFSG.RankThree.PartTwo.Source.NormalizedElementarySubgroup
import CFSG.Permutation.FiveTransitive.AbelianTwoCyclic
public import CFSG.Open.GLADefs

public section

namespace CFSG.RankThree.GF2n

open CFSG

variable {G : Type} [Group G]

theorem eq_of_mem_of_card_eq_two {B : Subgroup G} (hB : Nat.card B = 2) {a b : G}
    (ha : a ∈ B) (hb : b ∈ B) (ha1 : a ≠ 1) (hb1 : b ≠ 1) : a = b := by
  obtain ⟨y, -, huniq⟩ := (Nat.card_eq_two_iff' (1 : B)).mp hB
  have h1 : (⟨a, ha⟩ : B) = y := huniq _ fun h => ha1 (congrArg Subtype.val h)
  have h2 : (⟨b, hb⟩ : B) = y := huniq _ fun h => hb1 (congrArg Subtype.val h)
  exact congrArg Subtype.val (h1.trans h2.symm)

variable [Finite G]

theorem exists_eq_centralizer_of_card_eq_two {M B : Subgroup G} (hM : IsMaximalTwoLocal M)
    (hB : Maximal (fun W : Subgroup G => W ≤ M ∧ M ≤ Subgroup.normalizer (W : Set G) ∧
      Assembly.IsElemAbelian 2 W) B) (hB2 : Nat.card B = 2) :
    ∃ z : G, orderOf z = 2 ∧ B = Subgroup.zpowers z ∧
      M = Subgroup.centralizer ({z} : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hBM, hMB, hBab⟩ := hB.prop
  have hBne : B ≠ ⊥ := (Subgroup.one_lt_card_iff_ne_bot B).mp (by omega)
  obtain ⟨⟨z, hzB⟩, hz1'⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hBne
  have hz1 : z ≠ 1 := fun h => hz1' (Subtype.ext h)
  have hz2 : z ^ 2 = 1 := hBab.2 z hzB
  have hzo : orderOf z = 2 := orderOf_eq_prime hz2 hz1
  have hBz : B = Subgroup.zpowers z := by
    refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hzB) ?_).symm
    rw [Nat.card_zpowers, hzo, hB2]
  refine ⟨z, hzo, hBz, ?_⟩
  have hNC : ∀ c ∈ Subgroup.normalizer (B : Set G), c ∈ Subgroup.centralizer ({z} : Set G) := by
    intro c hc
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hcz : c * z * c⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.mp hc z).mp hzB
    have hcz1 : c * z * c⁻¹ ≠ 1 := by
      intro h
      apply hz1
      calc z = c⁻¹ * (c * z * c⁻¹) * c := by group
        _ = 1 := by rw [h]; group
    have := eq_of_mem_of_card_eq_two hB2 hcz hzB hcz1 hz1
    calc c * z = c * z * c⁻¹ * c := by group
      _ = z * c := by rw [this]
  have hCN : Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (B : Set G) := by
    intro c hc
    rw [Subgroup.mem_centralizer_singleton_iff] at hc
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have hcx : ∀ y ∈ B, c * y * c⁻¹ = y := by
      intro y hy
      rw [hBz] at hy
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      have hcz : c * z * c⁻¹ = z := by rw [hc]; group
      rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply, hcz]
    constructor
    · intro hx
      rw [hcx x hx]
      exact hx
    · intro hx
      have h := hcx _ hx
      have hyx : c * x * c⁻¹ = x := by
        calc c * x * c⁻¹ = c⁻¹ * (c * (c * x * c⁻¹) * c⁻¹) * c := by group
          _ = c⁻¹ * (c * x * c⁻¹) * c := by rw [h]
          _ = x := by group
      rw [← hyx]
      exact hx
  have hloc : IsPLocal 2 (Subgroup.centralizer ({z} : Set G)) :=
    ⟨B, hBne, PartTwo.Sec5.isPGroup_of_isElemAbelian hBab, le_antisymm hCN hNC⟩
  have hMC : M ≤ Subgroup.centralizer ({z} : Set G) := fun m hm => hNC m (hMB hm)
  by_contra hne
  exact hM.2 _ (lt_of_le_of_ne hMC hne) hloc

theorem glaSymplecticType_of_card_eq_two {M B : Subgroup G} {z : G}
    (hB : Maximal (fun W : Subgroup G => W ≤ M ∧ M ≤ Subgroup.normalizer (W : Set G) ∧
      Assembly.IsElemAbelian 2 W) B) (hB2 : Nat.card B = 2) (hBz : B = Subgroup.zpowers z)
    (hMz : M ≤ Subgroup.centralizer ({z} : Set G)) :
    CFSG.Open.GLASymplecticType (inSubgroup (pCore 2) M) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := inSubgroup (pCore 2) M with hQdef
  have hQ2 : IsPGroup 2 Q := IsPGroup.map (pCore_isPGroup (p := 2) (G := M)) M.subtype
  have hQM : Q ≤ M := Subgroup.map_subtype_le _
  have hMQ : M ≤ Subgroup.normalizer (Q : Set G) := le_normalizer_map_subtype M (pCore 2 M)
  have hz2 : z ^ 2 = 1 := hB.prop.2.2.2 z (hBz ▸ Subgroup.mem_zpowers z)
  refine ⟨hQ2, fun A hAchar hAc => ?_⟩
  set AG : Subgroup G := A.map Q.subtype with hAGdef
  have hAGc : IsMulCommutative AG := by
    refine ⟨⟨fun x y => ?_⟩⟩
    obtain ⟨x, hx⟩ := x
    obtain ⟨y, hy⟩ := y
    obtain ⟨x', hx', rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨y', hy', rfl⟩ := Subgroup.mem_map.mp hy
    apply Subtype.ext
    have := congrArg (fun t : A => ((t : Q) : G)) (hAc.is_comm.comm ⟨x', hx'⟩ ⟨y', hy'⟩)
    simpa using this
  have hMA : M ≤ Subgroup.normalizer (AG : Set G) := fun m hm =>
    mem_normalizer_map_subtype_of_characteristic (hMQ hm) A
  set E := RankThree.PartTwo.Source.omegaSubgroup AG hAGc 2 with hEdef
  have hEab : Assembly.IsElemAbelian 2 E := by
    refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun x hx => hx.2⟩
    have h := hAGc.is_comm.comm (⟨x, x.2.1⟩ : AG) ⟨y, y.2.1⟩
    rw [Subtype.ext_iff] at h
    exact h
  have hEM : E ≤ M := fun x hx => hQM (Subgroup.map_subtype_le A hx.1)
  have hME : M ≤ Subgroup.normalizer (E : Set G) := fun m hm =>
    RankThree.PartTwo.Source.mem_normalizer_omegaSubgroup hAGc 2 (hMA hm)
  have hEB : E ≤ B := by
    by_cases hzE : z ∈ E
    · exact hB.le_of_ge ⟨hEM, hME, hEab⟩ (hBz ▸ Subgroup.zpowers_le.mpr hzE)
    · have hcomm : ∀ a ∈ E, a * z = z * a := fun a ha =>
        Subgroup.mem_centralizer_singleton_iff.mp (hMz (hEM ha))
      obtain ⟨hW, -⟩ := PartTwo.Sec5.isElemAbelian_sup_zpowers hEab hzE hz2 hcomm
      have hWM : E ⊔ Subgroup.zpowers z ≤ M := sup_le hEM (hBz ▸ hB.prop.1)
      have hMW : M ≤ Subgroup.normalizer ((E ⊔ Subgroup.zpowers z : Subgroup G) : Set G) :=
        fun m hm => mem_normalizer_sup (hME hm) (hBz ▸ hB.prop.2.1 hm)
      exact le_sup_left.trans (hB.le_of_ge ⟨hWM, hMW, hW⟩ (hBz ▸ le_sup_right))
  let _ : CommGroup A := IsMulCommutative.instCommGroup
  refine FiveTransitive.AbelianTwoCyclic.isCyclic_of_square_kernel_card_le_two
    (hQ2.to_subgroup A) ?_
  let f : {a : A // a ^ 2 = 1} → B := fun a => ⟨((a.1 : Q) : G), hEB
    ⟨Subgroup.mem_map_of_mem Q.subtype a.1.2, by
      simpa using congrArg (fun t : A => ((t : Q) : G)) a.2⟩⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    have h := congrArg Subtype.val hab
    simpa [f] using h
  calc Nat.card {a : A // a ^ 2 = 1} ≤ Nat.card B := Nat.card_le_card_of_injective f hf
    _ = 2 := hB2

theorem generalizedFitting_eq_pCore (hchar : IsCharacteristicPType G 2) {M : Subgroup G}
    (hM : IsPLocal 2 M) : generalizedFitting M = pCore 2 M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact (isCharacteristicP_iff_generalizedFitting_eq_pCore M 2).mp (hchar M hM)

end CFSG.RankThree.GF2n
