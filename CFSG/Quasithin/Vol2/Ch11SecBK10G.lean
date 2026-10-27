module

public import CFSG.Quasithin.Vol2.Ch11SecBK10F
public import CFSG.Quasithin.Vol2.Ch11SecBK10E
public import CFSG.Quasithin.Vol2.Ch1Comm

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecD

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped commutatorElement

namespace BK10

variable {G : Type} [Group G]

theorem map_conj_mul (J : Subgroup G) (x y : G) :
    J.map (MulAut.conj (x * y)).toMonoidHom =
      (J.map (MulAut.conj y).toMonoidHom).map (MulAut.conj x).toMonoidHom := by
  rw [Subgroup.map_map, map_mul]
  rfl

theorem map_conj_one (J : Subgroup G) : J.map (MulAut.conj (1 : G)).toMonoidHom = J := by
  ext x
  rw [mem_map_conj_iff]
  simp

theorem conj_mem_centralizer {D : Subgroup G} {g a : G}
    (ha : a ∈ Subgroup.centralizer ((D.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G)) :
    ∀ d ∈ D, (g⁻¹ * a * g) * d * (g⁻¹ * a * g)⁻¹ = d := by
  intro d hd
  have h1 := Subgroup.mem_centralizer_iff.mp ha (g * d * g⁻¹) ⟨d, hd, rfl⟩
  calc (g⁻¹ * a * g) * d * (g⁻¹ * a * g)⁻¹ = g⁻¹ * (a * (g * d * g⁻¹)) * a⁻¹ * g := by group
    _ = g⁻¹ * (g * d * g⁻¹ * a) * a⁻¹ * g := by rw [h1]
    _ = d := by group

theorem isCoprimePrimeAut_rhoX_conj {J : Subgroup G} {a g : G}
    (ha : a ∈ Subgroup.normalizer (J : Set G)) (hg : g ∈ Subgroup.normalizer (J : Set G))
    (h : IsCoprimePrimeAut (rhoX J ⟨a, ha⟩)) :
    IsCoprimePrimeAut (rhoX J ⟨g⁻¹ * a * g, mul_mem (mul_mem (inv_mem hg) ha) hg⟩) := by
  have h1 := h.conj (rhoX J ⟨g⁻¹, inv_mem hg⟩)
  have h2 : rhoX J ⟨g⁻¹, inv_mem hg⟩ * rhoX J ⟨a, ha⟩ * (rhoX J ⟨g⁻¹, inv_mem hg⟩)⁻¹ =
      rhoX J ⟨g⁻¹ * a * g, mul_mem (mul_mem (inv_mem hg) ha) hg⟩ := by
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (by simp)
  rwa [h2] at h1

theorem conjClosure_eq_of_le_normalizer {J S : Subgroup G}
    (hSJ : S ≤ Subgroup.normalizer (J : Set G)) : conjClosure J S = J := by
  apply le_antisymm
  · change Subgroup.closure _ ≤ J
    rw [Subgroup.closure_le]
    rintro _ ⟨s, hs, j, hj, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp (hSJ hs) j).mp hj
  · intro j hj
    exact Subgroup.subset_closure ⟨1, S.one_mem, j, hj, by group⟩

variable [Finite G]

theorem commutator_le_of_torusRigid {H S J A D : Subgroup G}
    (h37 : A37Statement (↥H ⧸ CFSG.pCore 2 ↥H)) (h38 : A38Part3 (↥H ⧸ CFSG.pCore 2 ↥H))
    (hS : IsSylowTwoOf S H) (hJ : J ∈ cComp H)
    (hJq : CFSG.IsQuasisimple (↥J ⧸ CFSG.pCore 2 ↥J)) (hT : TorusRigid (XCls J))
    (hcop : Nat.Coprime (Nat.card A) (2 * Nat.card J))
    (hAS : ∀ s ∈ S, A ≤ Subgroup.normalizer (CFSG.conjugate J s : Set G))
    (hD : Lin2.IsHallTwoPrimeOf D (conjClosure J S ⊓ Subgroup.normalizer (S : Set G)))
    (hg : ∃ g ∈ conjClosure J S,
      A ≤ Subgroup.centralizer ((D.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G)) :
    ⁅J, A⁆ ≤ pCoreOf 2 J := by
  by_contra hnot
  have hconj : ∀ s : G, CFSG.conjugate J s = J.map (MulAut.conj s⁻¹).toMonoidHom := fun s => rfl
  have hAJ : A ≤ Subgroup.normalizer (J : Set G) := by
    have h1 := hAS 1 S.one_mem
    rwa [hconj, inv_one, map_conj_one] at h1
  obtain ⟨a, ha, hβ⟩ := exists_isCoprimePrimeAut hJq hAJ hcop hnot
  obtain ⟨g, hgcl, hgD⟩ := hg
  have haD := conj_mem_centralizer (hgD ha)
  have hS2 : IsPGroup 2 S := hS.2.1
  have hJH : J ≤ H := le_of_mem_cComp hJ
  have hQ : IsSylowTwoOf (S ⊓ J) J := isSylowTwoOf_inf_of_subnormal (subnormal_of_mem_cComp hJ) hS
  by_cases hSJ : S ≤ Subgroup.normalizer (J : Set G)
  · have hcl := conjClosure_eq_of_le_normalizer hSJ
    rw [hcl] at hD hgcl
    have hgJ : g ∈ Subgroup.normalizer (J : Set G) := Subgroup.le_normalizer hgcl
    exact not_isCoprimePrimeAut_of_invariant hS2 hSJ hQ hD hT _ haD
      (isCoprimePrimeAut_rhoX_conj (hAJ ha) hgJ hβ)
  obtain ⟨t, ht, htJ⟩ := Set.not_subset.mp hSJ
  have htH : t ∈ H := hS.1 ht
  have hM : J.map (MulAut.conj t).toMonoidHom ∈ cComp H := map_conj_mem_cComp hJ htH
  set M := J.map (MulAut.conj t).toMonoidHom with hMdef
  have hne : J ≠ M := fun h => htJ (A38.map_conj_eq_iff.mp h.symm)
  have hJM : J ≤ Subgroup.normalizer (M : Set G) := le_normalizer_of_mem_cComp hM hJ
  have hMJ : M ≤ Subgroup.normalizer (J : Set G) := le_normalizer_of_mem_cComp hJ hM
  obtain ⟨hcomm, -⟩ := lemma_1_2_1_two_of_a3 h37 hJ hM hne
  rcases lemma_1_2_1_three_of_a3_sq h37 h38 hJ with hn | ⟨hcard, -⟩
  · exact hSJ (hS.1.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hJH).mp hn))
  have hJmem : J ∈ conjSubgroupsBy H J := ⟨1, H.one_mem, (map_conj_one J).symm⟩
  have hMmem : M ∈ conjSubgroupsBy H J := ⟨t, htH, rfl⟩
  have hset : conjSubgroupsBy H J = {J, M} := by
    symm
    apply Set.eq_of_subset_of_ncard_le
    · intro K hK
      rcases hK with rfl | rfl
      · exact hJmem
      · exact hMmem
    · rw [hcard, Set.ncard_pair hne]
    · exact Set.finite_of_ncard_ne_zero (by rw [hcard]; norm_num)
  have hconjmem : ∀ h ∈ H, J.map (MulAut.conj h).toMonoidHom = J ∨
      J.map (MulAut.conj h).toMonoidHom = M := by
    intro h hh
    have h1 : J.map (MulAut.conj h).toMonoidHom ∈ conjSubgroupsBy H J := ⟨h, hh, rfl⟩
    rw [hset] at h1
    exact h1
  have hSorb : ∀ s ∈ S, s ∈ Subgroup.normalizer (J : Set G) ∨
      t⁻¹ * s ∈ Subgroup.normalizer (J : Set G) := by
    intro s hs
    rcases hconjmem s (hS.1 hs) with h | h
    · exact Or.inl (A38.map_conj_eq_iff.mp h)
    · right
      apply A38.map_conj_eq_iff.mp
      rw [map_conj_mul, h, hMdef, ← map_conj_mul, inv_mul_cancel, map_conj_one]
  have hcl : conjClosure J S = J ⊔ M := by
    apply le_antisymm
    · change Subgroup.closure _ ≤ J ⊔ M
      rw [Subgroup.closure_le]
      rintro _ ⟨s, hs, j, hj, rfl⟩
      rcases hSorb s hs with hsJ | hsJ
      · exact Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp hsJ j).mp hj)
      · apply Subgroup.mem_sup_right
        rw [hMdef, mem_map_conj_iff]
        have h1 := (Subgroup.mem_normalizer_iff.mp hsJ j).mp hj
        have h2 : t⁻¹ * s * j * (t⁻¹ * s)⁻¹ = t⁻¹ * (s * j * s⁻¹) * t := by group
        rwa [h2] at h1
    · refine sup_le (fun j hj => Subgroup.subset_closure ⟨1, S.one_mem, j, hj, by group⟩) ?_
      rintro _ ⟨j, hj, rfl⟩
      exact Subgroup.subset_closure ⟨t, ht, j, hj, rfl⟩
  have hJMK : ∀ z (hz : z ∈ J), z ∈ M → piX J ⟨z, hz⟩ = 1 := by
    intro z hz hzM
    change QuotientGroup.mk' (Subgroup.center (JBar J))
      (QuotientGroup.mk' (CFSG.pCore 2 ↥J) (⟨z, hz⟩ : ↥J)) = 1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_center_iff]
    intro w
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥J) w
    rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    have hc : ⁅(z : G)⁻¹, (x : G)⁻¹⁆ ∈ pCoreOf 2 J := by
      have h1 : ⁅(z : G)⁻¹, (x : G)⁻¹⁆ ∈ ⁅M, J⁆ :=
        Subgroup.commutator_mem_commutator (M.inv_mem hzM) (J.inv_mem x.2)
      rw [Subgroup.commutator_comm] at h1
      exact (hcomm h1).1
    obtain ⟨y, hy, hyeq⟩ := hc
    have h2 : (x * ⟨z, hz⟩)⁻¹ * (⟨z, hz⟩ * x) = y := Subtype.ext (by
      rw [show ((y : ↥J) : G) = ⁅(z : G)⁻¹, (x : G)⁻¹⁆ from hyeq, commutatorElement_def]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group)
    rw [h2]
    exact hy
  have hHJ₀ : H ≤ Subgroup.normalizer ((J ⊔ M : Subgroup G) : Set G) := by
    intro h hh
    apply A38.map_conj_eq_iff.mp
    rw [Subgroup.map_sup]
    have hMh : M.map (MulAut.conj h).toMonoidHom = J.map (MulAut.conj (h * t)).toMonoidHom := by
      rw [map_conj_mul]
    have hinj : J.map (MulAut.conj h).toMonoidHom ≠ M.map (MulAut.conj h).toMonoidHom :=
      fun e => hne (Subgroup.map_injective (MulAut.conj h).injective e)
    rcases hconjmem h hh with h1 | h1 <;>
      rcases hconjmem (h * t) (H.mul_mem hh htH) with h2 | h2
    · exact absurd (h1.trans (h2.symm.trans hMh.symm)) hinj
    · rw [h1, hMh, h2]
    · rw [h1, hMh, h2, sup_comm]
    · exact absurd (h1.trans (h2.symm.trans hMh.symm)) hinj
  have hQ₀ : IsSylowTwoOf (S ⊓ (J ⊔ M)) (J ⊔ M) :=
    CFSG.Quasithin.A4.isSylowTwoOf_inf_normal hS (sup_le hJH (le_of_mem_cComp hM)) hHJ₀
  rw [hcl] at hD hgcl
  have hgJ : g ∈ Subgroup.normalizer (J : Set G) := sup_le Subgroup.le_normalizer hMJ hgcl
  have hgM : g ∈ Subgroup.normalizer (M : Set G) := sup_le hJM Subgroup.le_normalizer hgcl
  have haM : a ∈ Subgroup.normalizer (M : Set G) := by
    have h1 := hAS t⁻¹ (S.inv_mem ht) ha
    rwa [hconj, inv_inv] at h1
  have hcM : g⁻¹ * a * g ∈ Subgroup.normalizer (M : Set G) :=
    mul_mem (mul_mem (inv_mem hgM) haM) hgM
  exact not_isCoprimePrimeAut_of_pair hS2 ht htJ hSorb hJM hJMK hQ hQ₀ hD hT _ hcM haD
    (isCoprimePrimeAut_rhoX_conj (hAJ ha) hgJ hβ)

end BK10

end CFSG.Quasithin.Vol2.Ch11.SecD
