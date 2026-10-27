module

public import CFSG.Open.SplitBNPair
public import CFSG.GroupTheory.ABGLocalTools.Basic
import CFSG.LocalAnalysis.UniquenessCase.UC22K108BigRow
import CFSG.LocalAnalysis.UniquenessCase.UC22K108BigFix
import CFSG.LocalAnalysis.UniquenessCase.UC22K108BigCell
import CFSG.LocalAnalysis.UniquenessCase.UC22K108BN
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Chev2StarHolds
import CFSG.LocalAnalysis.ABGTheoremB.IV1
import CFSG.Milestones.ASVolI.I2
import CFSG.Milestones.ASVolI.I2BNWeakClosure

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F10

open Subgroup CFSG.ASVolI.ChIJK
open CFSG.GH74.BNPair CFSG.GroupTheory.TitsSystem

theorem exists_conj_splitBNPair_of_isSylowOf {G : Type} [Group G] [Finite G]
    {L : Subgroup G} {p : ℕ} (hp : p.Prime) {B N : Subgroup ↥L}
    (hBN : IsSplitBNPair p B N) {S : Subgroup G}
    (hS : CFSG.ABGLocalTools.IsSylowOf p S L) :
    ∃ B' N' : Subgroup ↥L, IsSplitBNPair p B' N' ∧ S.subgroupOf L ≤ B' ∧
      Subgroup.normalizer ((S.subgroupOf L : Subgroup ↥L) : Set ↥L) = B' ∧
      B' ≤ S.subgroupOf L ⊔ (B' ⊓ N') := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hUmap : (S.subgroupOf L).map L.subtype = S := by
    rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hS.le]
  have hU_syl : CFSG.ABGLocalTools.IsSylowOf p (S.subgroupOf L) ⊤ := by
    rw [← CFSG.ABGLocalTools.isSylowOf_map_subtype_iff L]
    rw [hUmap, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    exact hS
  obtain ⟨-, hUp, hUi⟩ := CFSG.ABGLocalTools.isSylowOf_iff.mp hU_syl
  rw [Subgroup.relIndex_top_right] at hUi
  obtain ⟨U₀, hU₀B, hU₀n, hU₀p, hU₀i, -, hU₀H, -⟩ := hBN.split
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq ↥L (hU₀p.toSylow hU₀i) (hUp.toSylow hUi)
  have hc' : U₀.map (MulAut.conj c).toMonoidHom = S.subgroupOf L := by
    have h := congrArg (fun P : Sylow p ↥L => (P : Subgroup ↥L)) hc
    rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] at h
    have hmap : U₀.map (MulAut.conj c).toMonoidHom =
        U₀.map (MulDistribMulAction.toMonoidEnd (M := MulAut ↥L) (A := ↥L)
          (MulAut.conj c)) := by
      congr 1
    rwa [hmap]
  have hfinj : Function.Injective (MulAut.conj c).toMonoidHom := (MulAut.conj c).injective
  have hBN' : IsSplitBNPair p (B.map (MulAut.conj c).toMonoidHom)
      (N.map (MulAut.conj c).toMonoidHom) :=
    burnsideI2BN_map hBN _ (MulAut.conj c).surjective
      (by rw [(MonoidHom.ker_eq_bot_iff _).2 hfinj]; exact bot_le)
  have hUB : S.subgroupOf L ≤ B.map (MulAut.conj c).toMonoidHom := by
    rw [← hc']
    exact Subgroup.map_mono hU₀B
  have hBU₀ : B ≤ Subgroup.normalizer (U₀ : Set ↥L) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hU₀B).1 hU₀n
  have hB'U : B.map (MulAut.conj c).toMonoidHom ≤
      Subgroup.normalizer ((S.subgroupOf L : Subgroup ↥L) : Set ↥L) := by
    rw [← hc', ← Subgroup.map_equiv_normalizer_eq U₀ (MulAut.conj c)]
    exact Subgroup.map_mono hBU₀
  have hUn : ((S.subgroupOf L).subgroupOf (B.map (MulAut.conj c).toMonoidHom)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hUB).2 hB'U
  have hNU : Subgroup.normalizer ((S.subgroupOf L : Subgroup ↥L) : Set ↥L) =
      B.map (MulAut.conj c).toMonoidHom :=
    uc22k108bn_normalizer_eq hp hBN' hUB hUn hUp hUi
  have hBUH : B.map (MulAut.conj c).toMonoidHom ≤
      S.subgroupOf L ⊔ (B.map (MulAut.conj c).toMonoidHom ⊓
        N.map (MulAut.conj c).toMonoidHom) := by
    rw [← hc', ← Subgroup.map_inf_eq _ _ _ hfinj, ← Subgroup.map_sup, hU₀H]
  exact ⟨_, _, hBN', hUB, hNU, hBUH⟩

theorem exists_conj_sylow_sup_eq_top_of_splitBNPair {G : Type} [Group G] [Finite G]
    {L A S : Subgroup G} [IsSimpleGroup ↥L] {p : ℕ} (hp : p.Prime)
    (hA : (Nat.card A).Prime) (hAL : A ≤ normalizer (L : Set G))
    (hcop : ¬ Nat.card A ∣ Nat.card L) (hS : CFSG.ABGLocalTools.IsSylowOf p S L)
    (hAS : A ≤ normalizer (S : Set G)) {B N : Subgroup ↥L} (hBN : IsSplitBNPair p B N)
    (hpL : p ∣ Nat.card L) (hUB : S.subgroupOf L ≤ B)
    (hNU : Subgroup.normalizer ((S.subgroupOf L : Subgroup ↥L) : Set ↥L) = B)
    (hBUH : B ≤ S.subgroupOf L ⊔ (B ⊓ N)) :
    ∃ T : Subgroup G, CFSG.ABGLocalTools.IsSylowOf p T L ∧
      A ≤ normalizer (T : Set G) ∧ S ⊔ T = L := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.card A).Prime := ⟨hA⟩
  set U : Subgroup ↥L := S.subgroupOf L with hUdef
  have hUmap : U.map L.subtype = S := by
    rw [hUdef, Subgroup.subgroupOf_map_subtype, inf_of_le_left hS.le]
  have hU_syl : CFSG.ABGLocalTools.IsSylowOf p U ⊤ := by
    rw [← CFSG.ABGLocalTools.isSylowOf_map_subtype_iff L]
    rw [hUmap, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    exact hS
  have hUp : IsPGroup p U := hU_syl.isPGroup
  have hUH : U ⊔ (B ⊓ N) = B := le_antisymm (sup_le hUB inf_le_left) hBUH
  have hBne : B ≠ ⊤ :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.chev2star_ne_top_of_dvd_card hBN hpL
  have hUne : U ≠ ⊥ := k108big_split_ne_bot hBN hBne hUH
  have : (cartan B N).Normal := hBN.normal_inter
  obtain ⟨W, hW⟩ := burnsideI2BN_exists_isBNPair (burnsideI2BN_toPre hBN)
  obtain ⟨n₀, -, hmax⟩ := CFSG.ASVolI.burnsideI25b_exists_max (B := B) (N := N) W W
  have hmax' : ∀ w, wordLength W w ≤ wordLength W (n₀ : WeylGroup B N) :=
    fun w => hmax w (hW.mem_closure w)
  let φ : ↥A →* MulAut ↥L := L.normalizerMonoidHom.comp (Subgroup.inclusion hAL)
  have hφapp : ∀ (a : ↥A) (y : ↥L),
      ((φ a y : ↥L) : G) = (a : G) * (y : G) * (a : G)⁻¹ := fun _ _ => rfl
  have hφmem : ∀ (a : ↥A) (y : ↥L), φ a y ∈ U ↔ y ∈ U := fun a y => by
    rw [hUdef, Subgroup.mem_subgroupOf, hφapp a y]
    exact (Subgroup.mem_normalizer_iff.1 (hAS a.2) (y : G)).symm
  have hφU : ∀ a, U.map (φ a).toMonoidHom = U := fun a => by
    ext y
    rw [Subgroup.mem_map_equiv]
    simpa using (hφmem a ((φ a).symm y)).symm
  have hφB : ∀ (a : ↥A) (y : ↥L), φ a y ∈ B ↔ y ∈ B := fun a y => by
    rw [← hNU]
    have h1 := Subgroup.map_equiv_normalizer_eq U (φ a)
    rw [hφU a] at h1
    constructor
    · intro h
      rw [← h1, Subgroup.mem_map_equiv] at h
      simpa using h
    · intro h
      rw [← h1]
      exact ⟨y, h, rfl⟩
  have hAq : IsPGroup (Nat.card A) ↥A := IsPGroup.of_card (n := 1) (by rw [pow_one])
  have hpA : p ≠ Nat.card A := fun h => hcop (h ▸ hpL)
  obtain ⟨g, hg, hfix⟩ := k108big_exists_conj_fixed hW hpA hUp hUB hNU.ge hBUH hmax' hAq φ
    hφB hφU
  have htop : U ⊔ U.map (MulAut.conj g).toMonoidHom = ⊤ :=
    k108big_sup_conj_eq_top hW hUne hNU.ge hBUH hmax' hg
  set V : Subgroup ↥L := U.map (MulAut.conj g).toMonoidHom with hVdef
  have hV_syl : CFSG.ABGLocalTools.IsSylowOf p V ⊤ := by
    have h1 := hU_syl
    rw [CFSG.ABGLocalTools.isSylowOf_iff] at h1
    obtain ⟨-, hUp', hUi'⟩ := h1
    rw [Subgroup.relIndex_top_right] at hUi'
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    refine ⟨le_top, ?_, ?_⟩
    · rw [hVdef]
      exact hUp'.map _
    · rw [Subgroup.relIndex_top_right, hVdef,
        Subgroup.index_map_of_bijective (MulAut.conj g).bijective U]
      exact hUi'
  have hmap_top : (⊤ : Subgroup ↥L).map L.subtype = L := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  set T : Subgroup G := V.map L.subtype with hTdef
  have hT_syl : CFSG.ABGLocalTools.IsSylowOf p T L := by
    have h := (CFSG.ABGLocalTools.isSylowOf_map_subtype_iff L (A := V) (B := ⊤)).2 hV_syl
    rw [hmap_top] at h
    rwa [← hTdef] at h
  have htrans : ∀ (K : Subgroup ↥L) (a : ↥A),
      (K.map L.subtype).map (MulAut.conj (a : G)).toMonoidHom =
        (K.map (φ a).toMonoidHom).map L.subtype := fun K a => by
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
  have hAT : A ≤ Subgroup.normalizer (T : Set G) := by
    intro a ha
    have h1 : T.map (MulAut.conj (a : G)).toMonoidHom = T := by
      rw [hTdef, htrans V ⟨a, ha⟩, hfix ⟨a, ha⟩]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.2 h1
  have htopG : S ⊔ T = L := by
    have h := congrArg (Subgroup.map L.subtype) htop
    rw [Subgroup.map_sup, hmap_top, hUmap, ← hTdef] at h
    exact h
  exact ⟨T, hT_syl, hAT, htopG⟩

theorem exists_conj_sylow_sup_eq_top_and_normalized {G : Type} [Group G] [Finite G]
    {L A S : Subgroup G} [IsSimpleGroup ↥L] {p : ℕ} (hp : p.Prime)
    (hBN : ∃ B N : Subgroup ↥L, IsSplitBNPair p B N) (hpL : p ∣ Nat.card L)
    (hA : (Nat.card A).Prime) (hAL : A ≤ normalizer (L : Set G))
    (hcop : ¬ Nat.card A ∣ Nat.card L) (hS : CFSG.ABGLocalTools.IsSylowOf p S L)
    (hAS : A ≤ normalizer (S : Set G)) :
    ∃ T : Subgroup G, CFSG.ABGLocalTools.IsSylowOf p T L ∧
      A ≤ normalizer (T : Set G) ∧ S ⊔ T = L := by
  obtain ⟨B, N, hBN⟩ := hBN
  obtain ⟨B', N', hBN', hUB, hNU, hBUH⟩ := exists_conj_splitBNPair_of_isSylowOf hp hBN hS
  exact exists_conj_sylow_sup_eq_top_of_splitBNPair hp hA hAL hcop hS hAS hBN' hpL hUB hNU hBUH

theorem sup_centralizer_eq_of_isSylowOf_normalized {G : Type} [Group G] [Finite G]
    {L A S T : Subgroup G} {p : ℕ} (hp : p.Prime) (hA : (Nat.card A).Prime)
    (hAL : A ≤ normalizer (L : Set G)) (hcop : ¬ Nat.card A ∣ Nat.card L)
    (hS : CFSG.ABGLocalTools.IsSylowOf p S L) (hT : CFSG.ABGLocalTools.IsSylowOf p T L)
    (hAS : A ≤ normalizer (S : Set G)) (hAT : A ≤ normalizer (T : Set G))
    (htop : S ⊔ T = L) :
    S ⊔ (centralizer (A : Set G) ⊓ L) = L := by
  classical
  have : Fact (Nat.card A).Prime := ⟨hA⟩
  have hAq : IsPGroup (Nat.card A) ↥A := IsPGroup.of_card (n := 1) (by rw [pow_one])
  obtain ⟨c, hc, hceq⟩ :=
    CFSG.ABGTheoremB.exists_conj_eq_of_isSylowOf_normalized_of_coprime
      (p := Nat.card A) (r := p) hA hp hAq hAL hcop hS hT hAS hAT
  have hcL : c ∈ L := (Subgroup.mem_inf.1 hc).1
  have hcC : c ∈ centralizer (A : Set G) := (Subgroup.mem_inf.1 hc).2
  have hcCL : c ∈ centralizer (A : Set G) ⊓ L := Subgroup.mem_inf.2 ⟨hcC, hcL⟩
  refine le_antisymm (sup_le hS.le inf_le_right) ?_
  calc L = S ⊔ T := htop.symm
    _ = S ⊔ S.map (MulAut.conj c).toMonoidHom := by rw [hceq]
    _ ≤ S ⊔ (centralizer (A : Set G) ⊓ L) := by
        refine sup_le le_sup_left ?_
        rintro x ⟨s, hs, rfl⟩
        exact Subgroup.mul_mem _
          (Subgroup.mul_mem _ (Subgroup.mem_sup_right hcCL) (Subgroup.mem_sup_left hs))
          (Subgroup.inv_mem _ (Subgroup.mem_sup_right hcCL))

theorem sylow_sup_centralizer_eq_of_splitBNPair {G : Type} [Group G] [Finite G]
    {L A S : Subgroup G} [IsSimpleGroup ↥L] {p : ℕ}
    (hp : p.Prime) (hBN : ∃ B N : Subgroup ↥L, IsSplitBNPair p B N) (hpL : p ∣ Nat.card L)
    (hA : (Nat.card A).Prime) (hAL : A ≤ normalizer (L : Set G))
    (hcop : ¬ Nat.card A ∣ Nat.card L) (hS : CFSG.ABGLocalTools.IsSylowOf p S L)
    (hAS : A ≤ normalizer (S : Set G)) :
    S ⊔ (centralizer (A : Set G) ⊓ L) = L := by
  obtain ⟨T, hT, hAT, htop⟩ :=
    exists_conj_sylow_sup_eq_top_and_normalized hp hBN hpL hA hAL hcop hS hAS
  exact sup_centralizer_eq_of_isSylowOf_normalized hp hA hAL hcop hS hT hAS hAT htop

end CFSG.LocalAnalysis.UniquenessCase.UC22.F10
