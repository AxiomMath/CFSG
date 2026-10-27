module

public import CFSG.Quasithin.Vol2.Ch4Sec3C53Gen
public import CFSG.Quasithin.Vol2.Ch3xC58NSLocal
public import CFSG.Quasithin.Vol2.Ch3xC58NSBlocks
public import CFSG.Quasithin.Vol2.Ch4Sec3Lem431

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.C5 Subgroup

variable {G : Type} [Group G] [Finite G]

namespace C53

theorem exists_two_blocks {H T K₁ : Subgroup G} (hTH : T ≤ H) (hs : IsShort2 K₁) (hK₁H : K₁ ≤ H)
    (hperm : ∀ g ∈ T, conjSubgroup K₁ g = K₁ ∨ ∀ a ∈ K₁, ∀ b ∈ conjSubgroup K₁ g, a * b = b * a)
    (hindex : (T ⊓ normalizer (K₁ : Set G)).relIndex T ≤ 2)
    (hgen : oTwoUpper H ≤ ⨆ (g : G) (_ : g ∈ T), conjSubgroup K₁ g)
    (hns : ¬ T ≤ normalizer (K₁ : Set G)) :
    ∃ K₂ : Subgroup G, K₁ ≠ K₂ ∧ IsBlock2 H K₁ ∧ IsBlock2 H K₂ ∧
      (∃ t ∈ T, K₁.map (MulAut.conj t).toMonoidHom = K₂) ∧ oTwoUpper H = K₁ ⊔ K₂ := by
  obtain ⟨t, htT, htN⟩ := IsConcreteLE.not_le_iff_exists.mp hns
  have hle_K : ∀ L : Subgroup G, IsShort2 L → L ≤ H → L ≤ oTwoUpper H := fun L hL hLH =>
    calc L = oTwoUpper L := C1Pack.isShort2_eq_oTwoUpper hL
      _ ≤ oTwoUpper H := oTwoUpper_mono hLH
  have hK₁K : K₁ ≤ oTwoUpper H := hle_K K₁ hs hK₁H
  have hconjN : ∀ g ∈ T, conjSubgroup K₁ g ≤ normalizer (K₁ : Set G) := by
    intro g hg
    rcases hperm g hg with h | h
    · rw [h]; exact Subgroup.le_normalizer
    · exact le_normalizer_of_commute fun a ha b hb => (h b hb a ha).symm
  have hKN : oTwoUpper H ≤ normalizer (K₁ : Set G) := hgen.trans (iSup₂_le hconjN)
  have hB₁ : IsBlock2 H K₁ := ⟨hs, hK₁H, C58.isSubnormal_subgroupOf_trans hK₁K
    (C58.isSubnormal_subgroupOf_of_le_normalizer hK₁K hKN)
    (C58.isSubnormal_subgroupOf_of_le_normalizer (oTwoUpper_le H) (le_normalizer_oTwoUpper H))⟩
  set K₂ := K₁.map (MulAut.conj t).toMonoidHom with hK₂
  have hK₂c : K₂ = conjSubgroup K₁ t⁻¹ := by
    ext x
    rw [hK₂, Subgroup.mem_map_equiv, mem_conjSubgroup_iff, MulAut.conj_symm_apply, inv_inv]
  have hB₂ : IsBlock2 H K₂ := hK₂c ▸ C58.isBlock2_conjSubgroup hB₁ (inv_mem (hTH htT))
  have hne : K₁ ≠ K₂ := by
    intro h
    have h1 : conjSubgroup K₁ t⁻¹ = K₁ := hK₂c.symm.trans h.symm
    exact htN (by simpa using inv_mem (conjSubgroup_eq_iff_mem_normalizer.mp h1))
  have hidx : ((T ⊓ normalizer (K₁ : Set G)).subgroupOf T).index = 2 := by
    have h1 : (T ⊓ normalizer (K₁ : Set G)).relIndex T ≠ 1 := fun h =>
      htN (((Subgroup.relIndex_eq_one.mp h).trans inf_le_right) htT)
    have h0 : (T ⊓ normalizer (K₁ : Set G)).relIndex T ≠ 0 :=
      Subgroup.index_ne_zero_of_finite (H := (T ⊓ normalizer (K₁ : Set G)).subgroupOf T)
    show (T ⊓ normalizer (K₁ : Set G)).relIndex T = 2
    omega
  refine ⟨K₂, hne, hB₁, hB₂, ⟨t, htT, rfl⟩,
    le_antisymm ?_ (sup_le hK₁K (hle_K K₂ hB₂.1 hB₂.2.1))⟩
  refine hgen.trans (iSup₂_le fun g hg => ?_)
  by_cases hgN : g ∈ normalizer (K₁ : Set G)
  · rw [conjSubgroup_eq_iff_mem_normalizer.mpr hgN]
    exact le_sup_left
  · have hgt : g * t ∈ normalizer (K₁ : Set G) := by
      have := (Subgroup.mul_mem_iff_of_index_two hidx (a := ⟨g, hg⟩) (b := ⟨t, htT⟩)).mpr
      simp only [mem_subgroupOf, coe_mul, mem_inf] at this
      exact (this (iff_of_false (fun h => hgN h.2) (fun h => htN h.2))).2
    have e : g = (g * t) * t⁻¹ := by group
    rw [e, ← conjSubgroup_conjSubgroup, conjSubgroup_eq_iff_mem_normalizer.mpr hgt, ← hK₂c]
    exact le_sup_right

end C53

theorem lemmaC53C56Six_of (h126 : TheoremC126) (hMPB : C58NS.MinParabolicBlockSubnormal) :
    LemmaC53C56Six := by
  intro G _ _ H M₀ R T hHyp hR1 hNC hTsylM₀
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTsylH : IsSylowTwoOf T H := hHyp.sylow_TH
  have hTH : T ≤ H := hTsylH.1
  have hT2 : IsPGroup 2 T := hTsylH.2.1
  have hRT : R ≤ T := hHyp.R_le
  have hRsyl : IsSylowTwoOf R (oTwoUpper H ⊔ R) := hHyp.sylow_R
  have hM₀R : M₀ ≤ normalizer (R : Set G) := hHyp.normal_R
  have hTR : T ≤ normalizer (R : Set G) := hHyp.TH_le.trans hM₀R
  obtain ⟨N, hN⟩ := hHyp.unique_max
  set K := oTwoUpper H with hK
  have hKH : K ≤ H := oTwoUpper_le H
  have hKT : K ⊔ T = H := by
    rw [sup_comm, hK, ← F6.twoResidual_eq_oTwoUpper]; exact sup_twoResidual_eq hTsylH
  have hTn : ¬ H ≤ normalizer (T : Set G) := by
    intro hTn
    have hHKR : H ≤ normalizer ((K ⊔ R : Subgroup G) : Set G) := by
      calc H = K ⊔ T := hKT.symm
        _ ≤ _ := sup_le (le_sup_left.trans Subgroup.le_normalizer)
          (fun t ht => C1.mem_normalizer_sup (le_normalizer_oTwoUpper H (hTH ht)) (hTR ht))
    have hle : T ⊓ (K ⊔ R) ≤ R := by
      refine IsSylowIn.le_of_normal (p := 2) hRsyl inf_le_right ?_ (hT2.to_le inf_le_left)
      refine (normal_subgroupOf_iff_le_normalizer inf_le_right).mpr fun y hy => ?_
      exact C5.mem_normalizer_inf (hTn ((sup_le hKH (hRT.trans hTH)) hy))
        (Subgroup.le_normalizer hy)
    have hReq : R = T ⊓ (K ⊔ R) := le_antisymm (le_inf hRT le_sup_right) hle
    refine hNC R le_rfl hR1 ?_ hM₀R
    rw [hReq]
    exact fun h hh => C5.mem_normalizer_inf (hTn hh) (hHKR hh)
  have hSQ : IsSQTKTC H := hHyp.sqtk_H
  by_cases hsolv : Group.IsSolvable H
  ·
    obtain ⟨K₁, hcfg⟩ := C53.exists_blockConfig_of_isSylowTwoOf hTsylH hHyp.charTwo_H hN hTn
      hsolv (C1Pack.pRank_le_two_of_isSQTKTC hSQ) hR1 hRT hRsyl hHyp.TH_le hM₀R hNC
    obtain ⟨hns, -⟩ := C53.blockConfig_exists_good_elt hcfg hNC hTsylM₀ hM₀R hRT hTH hKT.ge
    obtain ⟨K₂, hne, hB₁, hB₂, ht, hKeq⟩ :=
      C53.exists_two_blocks hTH hcfg.short hcfg.le_H hcfg.perm hcfg.index hcfg.gen hns
    exact ⟨K₁, K₂, hne, hB₁, hB₂, Or.inr (Or.inl hcfg.alt), ht, hKeq⟩
  ·
    obtain ⟨K₁, hcfg⟩ := C58NS.exists_blockConfigNS h126 hMPB hTsylH hHyp.charTwo_H hSQ hN hTn
      hsolv hR1 hRT hRsyl hHyp.TH_le hM₀R hNC
    obtain ⟨hns, -⟩ := hcfg.exists_good_elt hNC hTsylM₀ hM₀R hRT hTH hRsyl hKT.ge
    obtain ⟨K₂, hne, hB₁, hB₂, ht, hKeq⟩ :=
      C53.exists_two_blocks hTH hcfg.short hcfg.le_H hcfg.perm hcfg.index hcfg.gen hns
    refine ⟨K₁, K₂, hne, hB₁, hB₂, ?_, ht, hKeq⟩
    rcases hcfg.typ with ⟨n, -, hn⟩ | h5
    · exact Or.inl ⟨n, hn⟩
    · exact Or.inr (Or.inr h5)

end CFSG.Quasithin.H13.Ch4
