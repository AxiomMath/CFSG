module

public import CFSG.RankThree.PartTwo.Sec14.Item1413Res3ProofDefs
import CFSG.RankThree.PartTwo.Sec14.Concl142NHJM22

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.KFacts.KP4 (G22 V lineE exists_centralizer_eq V_le_centralizer
  conj_mem_V card_V)

theorem ks1422M22Cent :
    KS1422M22Cent := by
  intro d hd3
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hd3' : d ^ 3 = 1 := by rw [← hd3]; exact pow_orderOf_eq_one d
  have hd1 : d ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hd3
    omega
  obtain ⟨g, hg⟩ := exists_conj_mem_P0 hd3' hd1
  have hg1 : g * d * g⁻¹ ≠ 1 := by
    intro h
    apply hd1
    calc d = g⁻¹ * (g * d * g⁻¹) * g := by group
      _ = 1 := by rw [h]; group
  obtain ⟨i, hi⟩ := exists_centralizer_eq hg hg1
  set φ : G22 ≃* G22 := MulAut.conj g with hφ
  have hφd : φ d = g * d * g⁻¹ := rfl
  have hcen : (Subgroup.centralizer ({d} : Set G22)).map φ.toMonoidHom =
      Subgroup.centralizer ({lineE i} : Set G22) := by
    rw [CFSG.RankThree.PartTwo.map_centralizer_singleton φ d, hφd, hi]
  have hφφ : ∀ x : G22, φ.symm (φ x) = x := fun x => φ.symm_apply_apply x
  refine ⟨(V i).map φ.symm.toMonoidHom, ?_, ?_, ?_, ?_⟩
  · intro h0
    have h1 : Nat.card ((V i).map φ.symm.toMonoidHom) = Nat.card (V i) :=
      Subgroup.card_map_of_injective φ.symm.injective
    rw [h0, Subgroup.card_bot, card_V] at h1
    omega
  · exact IsPGroup.of_card (n := 2)
      (by rw [Subgroup.card_map_of_injective φ.symm.injective, card_V]; norm_num)
  ·
    have h1 : (V i).map φ.symm.toMonoidHom ≤
        (Subgroup.centralizer ({lineE i} : Set G22)).map φ.symm.toMonoidHom :=
      Subgroup.map_mono (V_le_centralizer i)
    rw [← hcen, Subgroup.map_map] at h1
    have h2 : (φ.symm.toMonoidHom.comp φ.toMonoidHom) = MonoidHom.id G22 :=
      MonoidHom.ext fun x => hφφ x
    rwa [h2, Subgroup.map_id] at h1
  ·
    intro x hx
    have hφx : φ x ∈ Subgroup.centralizer ({lineE i} : Set G22) :=
      hcen ▸ Subgroup.mem_map_of_mem φ.toMonoidHom hx
    have hN : φ x ∈ Subgroup.normalizer ((V i : Subgroup G22) : Set G22) :=
      Subgroup.mem_normalizer_fintype fun v hv => conj_mem_V hφx hv
    have hN' : φ.symm (φ x) ∈ (Subgroup.normalizer ((V i : Subgroup G22) : Set G22)).map
        φ.symm.toMonoidHom := Subgroup.mem_map_of_mem φ.symm.toMonoidHom hN
    rw [Subgroup.map_equiv_normalizer_eq, hφφ] at hN'
    exact hN'

end CFSG.RankThree.PartTwo.Sec14
