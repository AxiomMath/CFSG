module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148QDefs
public import CFSG.RankThree.PartTwo.Sec14.Ronan148DInvSyl
public import CFSG.RankThree.PartTwo.Sec14.Ronan148DTwoON
public import CFSG.RankThree.PartTwo.Sec14.Ronan148DTwoMain
import CFSG.RankThree.PartTwo.Sec14.Ronan148DRank
import CFSG.RankThree.PartTwo.Sec14.Ronan148DM24
import CFSG.RankThree.PartTwo.Sec14.Item143DescProofGen
import CFSG.RankThree.PartTwo.Sec14.Item148HJProofLB
import CFSG.RankThree.PartTwo.Sec6.Item68
import CFSG.RankThree.PartTwo.Sec14.Item145Bot
public import CFSG.RankThree.PartTwo.Sec14.Item143DescProofFix
public import CFSG.RankThree.PartTwo.Sec14.Ronan148DTwoPair
public import CFSG.RankThree.PartTwo.Sec4.Item41Narrow
public import CFSG.RankThree.PartTwo.Sec6.BThreeFromLBalance

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148Q

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS
open Ronan148D

variable {G : Type} [Group G] [Finite G]

theorem map_conj_mem_lbMembers_of_mem_normalizer {A : Subgroup G} {a g : G}
    (hga : g ∈ Subgroup.centralizer ({a} : Set G)) (hgA : g ∈ Subgroup.normalizer (A : Set G))
    {K : Subgroup G} (hK : K ∈ lbMembers A a) :
    K.map (MulAut.conj g).toMonoidHom ∈ lbMembers A a := by
  obtain ⟨hKa, D, b, d, Lb, hD, haD, hc, hDK⟩ := hK
  refine ⟨Sec6.map_conj_mem_thetaComponentsAt hga hKa, D.map (MulAut.conj g).toMonoidHom,
    MulAut.conj g b, MulAut.conj g d, Lb.map (MulAut.conj g).toMonoidHom, hD.map_conj hgA, ?_, ?_,
    ?_⟩
  · have hag : (MulAut.conj g) a = a := by
      rw [MulAut.conj_apply, Subgroup.mem_centralizer_singleton_iff.mp hga]
      group
    exact ⟨a, haD, hag⟩
  · have h1 := hc.map (MulAut.conj g)
    rwa [map_conj_eq_of_mem_normalizer' hgA] at h1
  · rw [← isNaturalFamily_lB A g hgA D hD]
    exact Subgroup.map_mono hDK

theorem inf_normalizer_le_normalizer_sup_sSup {A : Subgroup G} {a : G} :
    Subgroup.centralizer ({a} : Set G) ⊓ Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer
      ((pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔ sSup (lbMembers A a) :
        Subgroup G) : Set G) := by
  rintro g ⟨hga, hgA⟩
  refine Desc143X.mem_normalizer_sup (le_normalizer_pPrimeCoreOf 3 _ hga) ?_
  refine mem_normalizer_of_conj_mem fun x hx => ?_
  have hle : (sSup (lbMembers A a)).map (MulAut.conj g).toMonoidHom ≤ sSup (lbMembers A a) := by
    rw [Subgroup.map_le_iff_le_comap]
    refine sSup_le fun K hK y hy => ?_
    exact le_sSup (map_conj_mem_lbMembers_of_mem_normalizer hga hgA hK) ⟨y, hy, rfl⟩
  exact hle ⟨x, hx, rfl⟩

theorem le_normalizer_sup_sSup_of {A : Subgroup G} {a : G}
    (hall : ∀ K ∈ lbMembers A a, ∀ g ∈ Subgroup.centralizer ({a} : Set G),
      K.map (MulAut.conj g).toMonoidHom ∈ lbMembers A a) :
    Subgroup.centralizer ({a} : Set G) ≤ Subgroup.normalizer
      ((pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔ sSup (lbMembers A a) :
        Subgroup G) : Set G) := by
  intro g hg
  refine Desc143X.mem_normalizer_sup (le_normalizer_pPrimeCoreOf 3 _ hg) ?_
  refine mem_normalizer_of_conj_mem fun x hx => ?_
  have hle : (sSup (lbMembers A a)).map (MulAut.conj g).toMonoidHom ≤ sSup (lbMembers A a) := by
    rw [Subgroup.map_le_iff_le_comap]
    refine sSup_le fun K hK y hy => ?_
    exact le_sSup (hall K hK g hg) ⟨y, hy, rfl⟩
  exact hle ⟨x, hx, rfl⟩

section Certificates

theorem map_mem_lbMembers_or_single (h134 : Item134) {A L : Subgroup G} {c a : G}
    (hS : Sec14Std G A c L) (ha : a ∈ A) (ha1 : a ≠ 1) (hΩ : Subgroup.zpowers a ∉ omegaA A)
    (hII : ∀ (D : Subgroup G) (b d : G) (Lb : Subgroup G), IsHyperplane A D → a ∈ D →
      IsLBConfig A D b d Lb → Subgroup.zpowers a = Subgroup.zpowers d)
    {K : Subgroup G} (hKX : K ∈ lbMembers A a) {g : G}
    (hg : g ∈ Subgroup.centralizer ({a} : Set G)) :
    K.map (MulAut.conj g).toMonoidHom ∈ lbMembers A a ∨
      ((∀ K' ∈ lbMembers A a, K' = K) ∧
        Sec4.IsTripleCover (↥K ⧸ aschbacherSolvableCore 3 ↥K) (alternatingGroup (Fin 6))) := by
  set K' := K.map (MulAut.conj g).toMonoidHom with hK'def
  by_cases hK'X : K' ∈ lbMembers A a
  · exact Or.inl hK'X
  have hKX' := hKX
  obtain ⟨hK, D, b, d, Lb, hD, haD, hc, hDK⟩ := hKX'
  have hne : K' ≠ K := fun heq => hK'X (heq ▸ hKX)
  have hK' : K' ∈ thetaComponentsAt 3 a := Sec6.map_conj_mem_thetaComponentsAt hg hK
  have hKC : K ≤ Subgroup.centralizer ({a} : Set G) := le_centralizer_of_mem_thetaComponentsAt hK
  by_cases htwo : ∃ K₁ ∈ lbMembers A a, K₁ ≠ K
  ·
    exfalso
    obtain ⟨K₁, hK₁, hne₁⟩ := htwo
    have hK₁X := hK₁
    obtain ⟨hK₁a, D₁, b₁, d₁, L₁, hD₁, haD₁, hc₁, hD₁K⟩ := hK₁
    have hAS := le_sup_of_ne hS hK hK₁a (Ne.symm hne₁) hD haD hc hDK hD₁ haD₁ hc₁ hD₁K
    have hne₁' : K' ≠ K₁ := fun heq => hK'X (heq ▸ hK₁X)
    exact false_of_le_commute hS hD hc hK hDK hg hAS
      (sup_le hKC (le_centralizer_of_mem_thetaComponentsAt hK₁a))
      fun s hs k hk => commutator_mem_theta_of_ne_sup hK' hK hK₁a hne hne₁' hk hs
  push Not at htwo
  rcases member_cases h134 hS hD hc (hII D b d Lb hD haD hc) hK hDK with
    ⟨-, htc, -⟩ | ⟨htc, -⟩
  ·
    by_cases hΩ1 : omegaA A = {Subgroup.zpowers b}
    · exfalso
      obtain ⟨P, hP, hAP, hPb⟩ :=
        exists_isSylowOf_le_centralizer_b hS ha hD hc (hII D b d Lb hD haD hc) hΩ1
      exact false_of_isSylowOf_le_centralizer_b hS hD hc hP hAP hPb hK hDK hg hne
    · exact Or.inr ⟨htwo, htc⟩
  ·
    exfalso
    have hAK := le_of_on hS ha ha1 hD haD hc (hII D b d Lb hD haD hc) hK hDK htc
    exact false_of_le_commute hS hD hc hK hDK hg hAK hKC fun s hs k hk =>
      Sec6.commutator_le_theta_of_ne_mem_thetaComponentsAt hK' hK hne
        (Subgroup.commutator_mem_commutator hk hs)

theorem inv143Q_sSup (h134 : Item134) {A L : Subgroup G} {c a d : G}
    (hS : Sec14Std G A c L) (ha : a ∈ A) (ha1 : a ≠ 1) (hΩ : Subgroup.zpowers a ∉ omegaA A)
    (hII : ∀ (D : Subgroup G) (b d : G) (Lb : Subgroup G), IsHyperplane A D → a ∈ D →
      IsLBConfig A D b d Lb → Subgroup.zpowers a = Subgroup.zpowers d)
    (hda : Subgroup.zpowers a = Subgroup.zpowers d) :
    Inv143Q A a d (sSup (lbMembers A a)) := by
  by_cases hall : ∀ K ∈ lbMembers A a, ∀ g ∈ Subgroup.centralizer ({a} : Set G),
      K.map (MulAut.conj g).toMonoidHom ∈ lbMembers A a
  · exact Or.inl (le_normalizer_sup_sSup_of hall)
  push Not at hall
  obtain ⟨K, hK, g, hg, hKg⟩ := hall
  rcases map_mem_lbMembers_or_single h134 hS ha ha1 hΩ hII hK hg with h1 | ⟨hsingle, htc⟩
  · exact absurd h1 hKg
  have hX1 : sSup (lbMembers A a) = K := by
    rw [Set.eq_singleton_iff_unique_mem.mpr ⟨hK, hsingle⟩, sSup_singleton]
  refine Or.inr ⟨hda, hX1 ▸ hK.1, hX1 ▸ htc, ?_⟩
  exact inf_normalizer_le_normalizer_sup_sSup

theorem step143HJDescTwoQ_of (h425 : Sec4.Item4_25Fix) (h134 : Item134) (h48 : Sec4.Item4_8)
    (h41 : Sec4.Item4_1LargePrime) (hGW : Sec6.GWLBalanceStatement)
    (hON : ONTripleGenE27) : Step143HJDescTwoQ := by
  intro G _ _ A c L hS a ha ha1 hΩ B b d Lb hB haB hc hda
  have hA := hS.isE27'
  by_cases hI : ∃ (D : Subgroup G) (b' d' : G) (L' : Subgroup G), IsHyperplane A D ∧ a ∈ D ∧
      IsLBConfig A D b' d' L' ∧ Subgroup.zpowers a ≠ Subgroup.zpowers d'
  ·
    obtain ⟨D, b', d', L', hD, haD, hc', hne⟩ := hI
    have hOne : Desc143X.One A c L a b' d' D L' := ⟨hS, ha, ha1, hΩ, hD, haD, hc', hne⟩
    have hcomp := step143HJCompOne_of_item4_25Fix' h425 h134 h48 h41 hGW
    obtain ⟨X, hXΔ, hLD, hN, hX, hXeq, hne'⟩ :=
      hOne.descX h48 hcomp (Desc143X.lB_le_delta hS hD hc' haD)
    obtain ⟨-, hd'1⟩ := hc'.ne_one hD hA
    refine ⟨b', d', L', hc'.2.1, hc'.2.2.1 ▸ Set.mem_singleton L',
      Item148HJ.j2_of_isLBConfig hc',
      hD.1 (hc'.1 ▸ Subgroup.subset_closure (Set.mem_insert_of_mem b' rfl)), hd'1,
      hc'.2.2.2.2, hc'.1 ▸ haD, X, hXΔ, hLD, Or.inl hN, Or.inl ⟨hX, hXeq, hne'⟩⟩
  push Not at hI
  set 𝒳 := lbMembers A a with h𝒳def
  set X := sSup 𝒳 with hXdef
  obtain ⟨-, hd1⟩ := hc.ne_one hB hA
  have hdA : d ∈ A := hB.1 (hc.1 ▸ Subgroup.subset_closure (Set.mem_insert_of_mem b rfl))
  have ha3 : a ^ 3 = 1 := hA.1.2 a ha
  obtain ⟨K₀, hK₀, hBK₀⟩ := exists_mem_lbMembers h48 hS ha ha1 hΩ hB haB hc
  have hXΔ : X ≤ delta A (lB A) (Subgroup.centralizer ({a} : Set G)) := by
    refine sSup_le fun K hK => ?_
    obtain ⟨hKa, D, b', d', L', hD, haD, hc', hDK⟩ := hK
    rcases member_cases h134 hS hD hc' (hI D b' d' L' hD haD hc') hKa hDK with
      ⟨hKeq, -, -⟩ | ⟨htc, h12⟩
    · rw [hKeq]
      refine sup_le (Desc143X.lB_le_delta hS hD hc' haD) ?_
      have hθO : inSubgroup (aschbacherSolvableCore 3) K ≤
          pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) := by
        rw [Sec6.theta_eq_inf_of_mem_thetaComponentsAt hKa]
        exact inf_le_right.trans (inSubgroup_theta_le_pPrimeCoreOf _)
      have hmem := sup_pPrimeCoreOf_mem_scriptQ (LB := lB A) hA hS.maximal_isElemAbelian ha
      exact hθO.trans (le_sup_left.trans (le_delta hmem.1 hmem.2))
    · exact le_delta_of_on hON h134 h48 hS ha ha1 hΩ hD haD hc' (hI D b' d' L' hD haD hc') h12
        hKa hDK htc
  have hLD : ∀ D : Subgroup G, IsHyperplane A D → a ∈ D →
      lB A D ≤ pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔ X :=
    fun D hD haD => (lB_le_sSup h48 hS ha ha1 hΩ hD haD).trans le_sup_right
  have hN : Inv143Q A a d X := inv143Q_sSup h134 hS ha ha1 hΩ hI hda
  refine ⟨b, d, Lb, hc.2.1, hc.2.2.1 ▸ Set.mem_singleton Lb, Item148HJ.j2_of_isLBConfig hc, hdA,
    hd1, hc.2.2.2.2, hc.1 ▸ haB, X, hXΔ, hLD, hN, Or.inr ⟨hda, ⟨𝒳, fun K hK => hK.1, ⟨K₀, hK₀⟩,
    rfl⟩, ?_⟩⟩
  have haK₀ : a ∈ K₀ := mem_of_mem_lbMembers hS hB hc hda hBK₀
  by_cases hsingle : ∀ K ∈ 𝒳, K = K₀
  · have h𝒳1 : 𝒳 = {K₀} := Set.eq_singleton_iff_unique_mem.mpr ⟨hK₀, hsingle⟩
    have hX1 : X = K₀ := by rw [hXdef, h𝒳1, sSup_singleton]
    rw [hX1]
    rcases member_cases h134 hS hB hc hda hK₀.1 hBK₀ with ⟨-, htc, -⟩ | ⟨htc, -⟩
    · exact Or.inr (Or.inl htc)
    · exact Or.inl htc
  · push Not at hsingle
    obtain ⟨K₁, hK₁, hne⟩ := hsingle
    obtain ⟨hK₁a, D₁, b₁, d₁, L₁, hD₁, haD₁, hc₁, hD₁K⟩ := hK₁
    have hK₁' : K₁ ∈ 𝒳 := ⟨hK₁a, D₁, b₁, d₁, L₁, hD₁, haD₁, hc₁, hD₁K⟩
    have h𝒳2 : 𝒳 = {K₀, K₁} := by
      ext K
      constructor
      · intro hK
        rcases eq_or_eq_of_mem_lbMembers hS hK₀ hK₁' hK (Ne.symm hne) with rfl | rfl
        · exact Set.mem_insert _ _
        · exact Set.mem_insert_of_mem _ rfl
      · rintro (rfl | rfl)
        · exact hK₀
        · exact hK₁'
    have hX2 : X = K₀ ⊔ K₁ := by rw [hXdef, h𝒳2, sSup_pair]
    rw [hX2]
    refine Or.inr (Or.inr ?_)
    rcases member_cases h134 hS hB hc hda hK₀.1 hBK₀ with ⟨-, htc₀, h12⟩ | ⟨htc₀, -⟩
    · rcases member_cases h134 hS hD₁ hc₁ (hI D₁ b₁ d₁ L₁ hD₁ haD₁ hc₁) hK₁a hD₁K with
        ⟨-, htc₁, -⟩ | ⟨-, h12'⟩
      · exact isCentralProductA6Covers_sup ha3 ha1 hK₀.1 hK₁a (Ne.symm hne) haK₀
          (mem_of_mem_lbMembers hS hD₁ hc₁ (hI D₁ b₁ d₁ L₁ hD₁ haD₁ hc₁) hD₁K) htc₀ htc₁
      · exact absurd h12' h12
    ·
      have hAK₀ := le_of_on hS ha ha1 hB haB hc hda hK₀.1 hBK₀ htc₀
      exact absurd (eq_of_mem_lbMembers_of_le hS hK₀.1 hAK₀ hK₁') hne

end Certificates

end CFSG.RankThree.PartTwo.Sec14.Ronan148Q
