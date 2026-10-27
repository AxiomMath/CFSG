module

public import CFSG.Quasithin.Vol2.Ch9Sec3L34Diag
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5112M23

public section

namespace CFSG.Quasithin.H13.Ch9

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H

variable {G : Type} [Group G] [Finite G]

namespace L34

theorem isPSL_of_star {H X K : Subgroup G} (hKH : K ≤ H) (hJ : IsPGroup 2 (kerIn X H))
    (hKL : IsPSL 3 2 2 ↥(E2.star X H K)) : IsPSL 3 2 2 (O2Q K) := by
  have hS : IsSimpleGroup ↥(E2.star X H K) :=
    (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 3 2 2 hKL).2
  have hnab : ∃ a b : ↥(E2.star X H K), a * b ≠ b * a :=
    Vol2Native.A312L.Seven.nonabelian_of_card_not_prime (by
      rw [Ch1Four.card_of_isPSL_three_four hKL]; norm_num)
  set φ := QuotientGroup.mk' ((kerIn X H).subgroupOf H) with hφ
  let ρ : ↥K →* ↥(E2.star X H K) :=
    (φ.comp (Subgroup.inclusion hKH)).codRestrict (E2.star X H K)
      (fun k => ⟨Subgroup.inclusion hKH k, Subgroup.mem_subgroupOf.mpr k.2, rfl⟩)
  have hρ : Function.Surjective ρ := by
    rintro ⟨_, ⟨h, hh, rfl⟩⟩
    exact ⟨⟨h, Subgroup.mem_subgroupOf.mp hh⟩, rfl⟩
  have hker : IsPGroup 2 ρ.ker := by
    rintro ⟨k, hk⟩
    have h1 : ρ k = 1 := hk
    have h2 : φ (Subgroup.inclusion hKH k) = 1 := congrArg Subtype.val h1
    have h3 : (k : G) ∈ kerIn X H := by
      have h4 : Subgroup.inclusion hKH k ∈ (kerIn X H).subgroupOf H := by
        rw [← QuotientGroup.ker_mk' ((kerIn X H).subgroupOf H)]
        exact h2
      exact Subgroup.mem_subgroupOf.mp h4
    obtain ⟨m, hm⟩ := hJ ⟨k, h3⟩
    refine ⟨m, Subtype.ext (Subtype.ext ?_)⟩
    simpa using congrArg Subtype.val hm
  have e : ModO2 K ≃* ↥(E2.star X H K) := Vol2Native.A312L.modO2EquivOfHom hnab ρ hρ hker
  exact CFSG.LieType.CurtisTits.statedClassicalModel_of_mulEquiv e.symm hKL

theorem isSL3Ch5_of_star {H X K : Subgroup G} (hKH : K ≤ H) (hJ : IsPGroup 2 (kerIn X H))
    (hKL : IsPSL 3 2 2 ↥(E2.star X H K)) : IsSL3Ch5 2 (O2Q K) :=
  Or.inl (Or.inl ⟨by decide, isPSL_of_star hKH hJ hKL⟩)

end L34

variable {T L I : Subgroup G} {n : ℕ}

namespace Setup

variable (S : Setup T L I n)
include S

theorem isMaximalLocal_of_l34 (hM : Vol2.Ch11.SecB.FactMathieuOrders)
    (hM23 : FactM23L34) (h312 : A312ForSQTK) (h37c : Vol2Native.A37ForSQTKCat)
    (hE22 : E2.E22StatementC) (h331 : Stmt3_3_1) {H K : Subgroup G}
    (hH : IsHStar T (fsuM T L) H) (hn1 : 1 < E1.nParam H) (hHK : H = K ⊔ T)
    (hKc : K ∈ cComp H) (hTK : T ≤ Subgroup.normalizer (K : Set G))
    (hJ : IsPGroup 2 (kerIn (H ⊓ fsuM T L) H))
    (hKL : IsPSL 3 2 2 ↥(E2.star (H ⊓ fsuM T L) H K)) : quasithinIsMaximalLocal T K := by
  have hfsu := S.hyp.fsu
  have hD := S.isDiagramNontrivial_of_l34 hE22 h331 hH hn1 hHK hKc hTK hJ hKL
  have hKH : K ≤ H := le_of_mem_cComp hKc
  have hSL := L34.isSL3Ch5_of_star hKH hJ hKL
  have hTH : T ≤ H := hH.1.1
  have hTHs : IsSylowTwoOf T H :=
    CFSG.Quasithin.isSylowTwoOf_of_quasithinIsSylowTwo hfsu.sylow hTH
  have hKl : K ∈ lFamily T := by
    show K ∈ cComp (K ⊔ T)
    rw [← hHK]
    exact hKc
  have : IsSimpleGroup G := hfsu.simple
  have hloc : LocalSQTK G := (QuasithinUnique.qtkeCore_of_cat hfsu.nonabelian hfsu.qtke).1
  refine ⟨⟨hTHs.2.1, hKl, ?_, ?_⟩, fun K' hK' hKK' => ?_⟩
  · rw [← hHK]
    exact hTHs.2.2
  · rw [← hHK]
    exact hH.1.2
  · by_contra hne
    have l : EmbLoc G T (K' ⊔ T) K K' :=
      { simple := hfsu.simple
        nonabelian := hfsu.nonabelian
        qtke := hfsu.qtke
        pCoreX := hK'.2.2.2
        sylowX := ⟨le_sup_right, hK'.1, hK'.2.2.1⟩
        le_X := hKK'.trans le_sup_left
        mem_lFamily := hKl
        normalizes := hTK
        hat := ⟨hK'.2.1, hKK', fun Y hY hKY => Vol2Native.lemma_1_2_4_unique hloc h37c
          hK'.2.2.2 hKl hY hK'.2.1 hKY hKK'⟩
        lt := lt_of_le_of_ne hKK' (Ne.symm hne) }
    exact l.false_of_l34 hM hM23 h312 hSL hD

theorem isUniqueM_normalizer_of_l34
    (hM : Vol2.Ch11.SecB.FactMathieuOrders) (hM23 : FactM23L34) (h312 : A312ForSQTK)
    (h37c : Vol2Native.A37ForSQTKCat) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (hE22 : E2.E22StatementC) (h331 : Stmt3_3_1) {H K : Subgroup G} (hH : IsHStar T (fsuM T L) H)
    (hn1 : 1 < E1.nParam H) (hHK : H = K ⊔ T) (hKc : K ∈ cComp H)
    (hTK : T ≤ Subgroup.normalizer (K : Set G)) (hJ : IsPGroup 2 (kerIn (H ⊓ fsuM T L) H))
    (hKL : IsPSL 3 2 2 ↥(E2.star (H ⊓ fsuM T L) H K)) :
    IsUniqueM H (Subgroup.normalizer (K : Set G)) := by
  have hfsu := S.hyp.fsu
  have hmax := S.isMaximalLocal_of_l34 hM hM23 h312 h37c hE22 h331 hH hn1 hHK hKc hTK hJ hKL
  have hU := lemma_1_2_7_three hfsu.qtke hfsu.simple hfsu.nonabelian h37 h38 h39 hfsu.sylow hmax
  have hcl : conjClosure K T = K :=
    le_antisymm (conjClosure_le fun t ht k hk => (Subgroup.mem_normalizer_iff.mp (hTK ht) k).mp hk)
      (le_conjClosure K T)
  rw [hcl, ← hHK] at hU
  exact hU

end Setup

end CFSG.Quasithin.H13.Ch9
