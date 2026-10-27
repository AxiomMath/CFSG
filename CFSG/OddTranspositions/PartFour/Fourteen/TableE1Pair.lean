module

public import CFSG.OddTranspositions.O4Minus5Pair
public import CFSG.RankThree.GF2n.Tim79aSec23NoSq
import CFSG.OddTranspositions.FixKS5
import CFSG.OddTranspositions.SymNoSqE1

public section

namespace CFSG.OddTranspositions.PartFour

open CFSG.OddTranspositions.QZ CFSG.GorensteinWalter CFSG.RankThree.GF2n.Tim79a

private theorem ringAut_eq_one_or_frob25 (σ : K25 ≃+* K25) : σ = 1 ∨ σ = frob25 := by
  obtain ⟨_, -, huniq⟩ := (Nat.card_eq_two_iff' (1 : K25 ≃+* K25)).mp card_ringAut
  by_cases h : σ = 1
  · exact Or.inl h
  · exact Or.inr ((huniq σ h).trans (huniq frob25 frob25_ne_one).symm)

private theorem left_mem_FixK_of_mem_centralizer {x : PSigmaL225}
    (hx : x ∈ Subgroup.centralizer ({SemidirectProduct.inr frob25} : Set PSigmaL225)) :
    x.left ∈ FixK :=
  (mem_centralizer_inr_frob25_iff x.left x.right).mp hx

private noncomputable def centralizerToFixK :
    Subgroup.centralizer ({SemidirectProduct.inr frob25} : Set PSigmaL225) →* FixK where
  toFun x := ⟨(x : PSigmaL225).left, left_mem_FixK_of_mem_centralizer x.2⟩
  map_one' := rfl
  map_mul' a b := by
    apply Subtype.ext
    change (a : PSigmaL225).left *
        psl2FieldAut K25 (a : PSigmaL225).right (b : PSigmaL225).left =
      (a : PSigmaL225).left * (b : PSigmaL225).left
    have hb : (b : PSigmaL225).left = psl2FieldAut K25 frob25 (b : PSigmaL225).left :=
      left_mem_FixK_of_mem_centralizer b.2
    rcases ringAut_eq_one_or_frob25 (a : PSigmaL225).right with h | h
    · rw [h, map_one, MulAut.one_apply]
    · rw [h, ← hb]

private theorem mem_zpowers_of_centralizerToFixK_eq_one
    {x : Subgroup.centralizer ({SemidirectProduct.inr frob25} : Set PSigmaL225)}
    (hx : centralizerToFixK x = 1) :
    (x : PSigmaL225) ∈ Subgroup.zpowers (SemidirectProduct.inr frob25) := by
  have hleft : (x : PSigmaL225).left = 1 := congrArg Subtype.val hx
  rcases ringAut_eq_one_or_frob25 (x : PSigmaL225).right with h | h
  · rw [show (x : PSigmaL225) = 1 from SemidirectProduct.ext hleft h]
    exact Subgroup.one_mem _
  · rw [show (x : PSigmaL225) = SemidirectProduct.inr frob25 from SemidirectProduct.ext hleft h]
    exact Subgroup.mem_zpowers _

private theorem pCore_two_FixK_eq_bot : CFSG.pCore 2 FixK = ⊥ := by
  obtain ⟨e, -⟩ := fixK_equiv_s5
  have h := CFSG.pCore_map_iso 2 e
  rw [pCore_two_perm_eq_bot_of_three_or_five_le (Or.inr le_rfl)] at h
  exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp h

private theorem inSubgroup_pCore_cenGen_class65_le :
    CFSG.inSubgroup (CFSG.pCore 2) (cenGen class65 (SemidirectProduct.inr frob25)) ≤
      Subgroup.zpowers (SemidirectProduct.inr frob25 : PSigmaL225) := by
  set K : Subgroup PSigmaL225 := cenGen class65 (SemidirectProduct.inr frob25) with hK
  have hKC : K ≤ Subgroup.centralizer ({SemidirectProduct.inr frob25} : Set PSigmaL225) := by
    rw [hK, cenGen, Subgroup.closure_le]
    exact Set.inter_subset_right
  let ψ : K →* FixK := centralizerToFixK.comp (Subgroup.inclusion hKC)
  have hsurj : Function.Surjective ψ := by
    have hle : FixK ≤ ψ.range.map FixK.subtype := by
      refine closure_left_y_eq_FixK.symm.le.trans ?_
      rw [Subgroup.closure_le]
      rintro _ ⟨i, rfl⟩
      have hyK : y i ∈ K := by
        rw [hK, cenGen]
        exact Subgroup.subset_closure
          ⟨y_mem_class65 i, Subgroup.mem_centralizer_singleton_iff.mpr (y_commute_base i).eq⟩
      exact ⟨ψ ⟨y i, hyK⟩, ⟨⟨y i, hyK⟩, rfl⟩, rfl⟩
    intro q
    obtain ⟨r, ⟨k, hk⟩, hrq⟩ := hle q.2
    exact ⟨k, hk.trans (Subtype.ext hrq)⟩
  have hbot : (CFSG.pCore 2 K).map ψ = ⊥ := by
    have hle : (CFSG.pCore 2 K).map ψ ≤ CFSG.pCore 2 FixK :=
      le_sSup ⟨CFSG.pCore_normal.map ψ hsurj, CFSG.pCore_isPGroup.map ψ⟩
    rwa [pCore_two_FixK_eq_bot, le_bot_iff] at hle
  intro z hz
  rw [CFSG.inSubgroup, Subgroup.mem_map] at hz
  obtain ⟨x, hx, rfl⟩ := hz
  have hx1 : ψ x = 1 := by
    have hmem : ψ x ∈ (CFSG.pCore 2 K).map ψ := Subgroup.mem_map_of_mem ψ hx
    rwa [hbot, Subgroup.mem_bot] at hmem
  exact mem_zpowers_of_centralizerToFixK_eq_one (x := Subgroup.inclusion hKC x) hx1

private theorem image_conj_class65 (g : PSigmaL225) : MulAut.conj g '' class65 = class65 := by
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact IsConj.trans hz (isConj_iff.mpr ⟨g, (MulAut.conj_apply g z).symm⟩)
  · intro hx
    refine ⟨g⁻¹ * x * g, IsConj.trans hx (isConj_iff.mpr ⟨g⁻¹, by group⟩), ?_⟩
    rw [MulAut.conj_apply]
    group

theorem noSqE1_class65 : NoSqE1 class65 := by
  intro d hd
  obtain ⟨g, rfl⟩ := isConj_iff.mp hd
  have h := Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom)
    inSubgroup_pCore_cenGen_class65_le
  rw [map_inSubgroup_pCore_map, map_cenGen, image_conj_class65, MonoidHom.map_zpowers,
    MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h
  exact h.trans le_sup_left

theorem noSqE1_of_isO4Minus5Pair {G : Type} [Group G] {D : Set G} (hP : QZ.IsO4Minus5Pair G D) :
    CFSG.RankThree.GF2n.Tim79a.NoSqE1 D := by
  obtain ⟨e, he⟩ := hP
  exact noSqE1_of_map_mulEquiv e he.symm noSqE1_class65

end CFSG.OddTranspositions.PartFour

end
