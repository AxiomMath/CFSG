module

public import CFSG.Quasithin.H13.StatementsL6
public import CFSG.Quasithin.Vol2.Ch3Sec2Lem323
public import CFSG.Quasithin.Vol2.Ch3Sec2Lem322Eight
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.ReducedChar
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesExtraBasic

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

namespace Prop3210

variable {G : Type} [Group G] [Finite G] {T L V₀ Vp : Subgroup G}

omit [Finite G] in
theorem conjClosure_le_vplus (hV : IsVplus T L V₀ Vp) : conjClosure V₀ T ≤ Vp := by
  rcases hV with ⟨-, -, rfl⟩ | ⟨-, rfl⟩
  · exact le_conjClosure _ _
  · exact le_rfl

theorem ne_bot (h3228 : Stmt3_2_2_eight) (h : FSU G T L V₀) : T ≠ ⊥ := by
  intro hT
  obtain ⟨-, -, hR⟩ := h3228 G T L V₀ h
  have hI := h.irrPlus
  have h2 : reducedAggregate (L ⊔ T) ≤ T := by
    have := Lem3228.reducedAggregate_le_pCoreOf' (L ⊔ T)
    rw [← conjClosure_sup_eq L T] at this ⊢
    rw [hR] at this
    exact this.trans inf_le_left
  have hle : V₀ ≤ T := hI.1.trans h2
  rw [hT] at hle
  exact hI.2.1 (le_bot_iff.mp hle)

theorem normalizer_thompsonJ_le_of_V (h323 : Stmt3_2_3) (h3228 : Stmt3_2_2_eight)
    (h : FSU G T L V₀) (hJ : thompsonJ T ≤ Subgroup.centralizer (conjClosure V₀ T : Set G)) :
    Subgroup.normalizer (thompsonJ T : Set G) ≤
      Subgroup.normalizer (conjClosure L T : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, hR⟩ := h3228 G T L V₀ h
  have hJR : thompsonJ T ≤ pCoreOf 2 (conjClosure L T ⊔ T) := by
    rw [hR]
    exact le_inf (GammaExtra.thompsonJ_le_self T) hJ
  have hRT : pCoreOf 2 (conjClosure L T ⊔ T) ≤ T := by
    rw [hR]
    exact inf_le_left
  have hJeq := GammaExtra.thompsonJ_eq_of_le hJR hRT
  have hLT : conjClosure L T ⊔ T ≤ Subgroup.normalizer (thompsonJ T : Set G) := by
    rw [← hJeq]
    exact (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _).trans
      (GammaExtra.normalizer_le_normalizer_thompsonJ _)
  have hloc : IsTwoLocal (Subgroup.normalizer (thompsonJ T : Set G)) :=
    ⟨thompsonJ T, Setup.thompsonJ_ne_bot h.sylow.1 (ne_bot h3228 h),
      GammaExtra.isPGroup_thompsonJ h.sylow.1, rfl⟩
  obtain ⟨M', hM', hle⟩ := exists_quasithinIsMaxTwoLocal_ge hloc
  obtain ⟨-, ⟨-, huniq⟩, -⟩ := h323 G T L h.simple h.nonabelian h.qtke h.sylow h.maximal
    h.faithful h.quasisimple
  rw [← huniq M' ⟨hM'.1, hM'.2⟩ (hLT.trans hle)]
  exact hle

theorem normalizer_thompsonJ_le (h323 : Stmt3_2_3) (h3228 : Stmt3_2_2_eight)
    (h : FSU G T L V₀) (hV : IsVplus T L V₀ Vp)
    (hJ : thompsonJ T ≤ Subgroup.centralizer (Vp : Set G)) :
    Subgroup.normalizer (thompsonJ T : Set G) ≤
      Subgroup.normalizer (conjClosure L T : Set G) :=
  normalizer_thompsonJ_le_of_V h323 h3228 h
    (hJ.trans (Subgroup.centralizer_le (conjClosure_le_vplus hV)))

end Prop3210

theorem stmt3_2_10_eight_of_V (h323 : Stmt3_2_3) (h3228 : Stmt3_2_2_eight) :
    ∀ (G : Type) [Group G] [Finite G] (T L V₀ : Subgroup G), FSU G T L V₀ →
      thompsonJ T ≤ Subgroup.centralizer (conjClosure V₀ T : Set G) →
      ∀ S : Subgroup G, IsPGroup 2 ↥S → thompsonJ T ≤ S →
        thompsonJ T = thompsonJ S ∧
          Subgroup.normalizer (S : Set G) ≤ Subgroup.normalizer (conjClosure L T : Set G) := by
  intro G _ _ T L V₀ h hJ S hS hJS
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hNJ := Prop3210.normalizer_thompsonJ_le_of_V h323 h3228 h hJ
  let P : Sylow 2 G := h.sylow.1.toSylow h.sylow.2
  obtain ⟨Q, hSQ⟩ := hS.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P Q
  have hQ : (Q : Subgroup G) = T.map (MulAut.conj g).toMonoidHom := by
    rw [← hg, Sylow.coe_subgroup_smul]
    rfl
  have hSTg : S ≤ T.map (MulAut.conj g).toMonoidHom := hQ ▸ hSQ
  have h1 : thompsonJ T ≤ thompsonJ (T.map (MulAut.conj g).toMonoidHom) := by
    refine GammaExtra.thompsonJ_le fun A hA =>
      GammaExtra.le_thompsonJ ⟨(GammaExtra.le_thompsonJ hA).trans (hJS.trans hSTg), hA.2.1,
        fun B hB hBe => ?_⟩
    have := (GammaExtra.isMaxElemAbelian_map_equiv (MulAut.conj g) hA).2.2 B hB hBe
    rwa [Subgroup.card_map_of_injective (MulAut.conj g).injective] at this
  have h2 := GammaExtra.thompsonJ_map_equiv (MulAut.conj g) T
  have h3 : thompsonJ T = (thompsonJ T).map (MulAut.conj g).toMonoidHom :=
    Subgroup.eq_of_le_of_card_ge (h2 ▸ h1)
      (by rw [Subgroup.card_map_of_injective (MulAut.conj g).injective])
  have hJTg : thompsonJ (T.map (MulAut.conj g).toMonoidHom) = thompsonJ T := h2.trans h3.symm
  have hJS' : thompsonJ S = thompsonJ T := by
    rw [GammaExtra.thompsonJ_eq_of_le (hJTg ▸ hJS) hSTg, hJTg]
  refine ⟨hJS'.symm, ?_⟩
  calc Subgroup.normalizer (S : Set G) ≤ Subgroup.normalizer (thompsonJ S : Set G) :=
        GammaExtra.normalizer_le_normalizer_thompsonJ S
    _ = Subgroup.normalizer (thompsonJ T : Set G) := by rw [hJS']
    _ ≤ _ := hNJ

theorem stmt3_2_10_eight_of (h323 : Stmt3_2_3) (h3228 : Stmt3_2_2_eight) : Stmt3_2_10_eight :=
  fun G _ _ T L V₀ _ h hV hJ S hS hJS => stmt3_2_10_eight_of_V h323 h3228 G T L V₀ h
    (hJ.trans (Subgroup.centralizer_le (Prop3210.conjClosure_le_vplus hV))) S hS hJS

namespace Prop3210

variable {G : Type} [Group G] [Finite G] {T L V₀ Vp : Subgroup G}

theorem exists_isSylowTwoOf_normalizer (h323 : Stmt3_2_3) (h3228 : Stmt3_2_2_eight)
    (h : FSU G T L V₀) (hV : IsVplus T L V₀ Vp)
    (hJ : thompsonJ T ≤ Subgroup.centralizer (Vp : Set G)) {U : Subgroup G} (hU : U ≤ Vp) :
    ∃ S : Subgroup G, thompsonJ T ≤ S ∧
      S ≤ Subgroup.normalizer (conjClosure L T : Set G) ⊓ Subgroup.normalizer (U : Set G) ∧
      IsSylowTwoOf S (Subgroup.normalizer (U : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M := Subgroup.normalizer (conjClosure L T : Set G) with hM
  set NU := Subgroup.normalizer (U : Set G) with hNU
  have h8 := stmt3_2_10_eight_of h323 h3228 G T L V₀ Vp h hV hJ
  obtain ⟨⟨-, hTM⟩, -, -⟩ := h323 G T L h.simple h.nonabelian h.qtke h.sylow h.maximal
    h.faithful h.quasisimple
  have hJK : thompsonJ T ≤ M ⊓ NU :=
    le_inf ((GammaExtra.thompsonJ_le_self T).trans hTM)
      ((hJ.trans (Subgroup.centralizer_le hU)).trans (Subgroup.centralizer_le_normalizer _))
  obtain ⟨S, hJS, hS⟩ := exists_isSylowTwoOf_of_le hJK (GammaExtra.isPGroup_thompsonJ h.sylow.1)
  have hNS : Subgroup.normalizer (S : Set G) ≤ M := (h8 S hS.isPGroup hJS).2
  obtain ⟨S', hSS', hS'⟩ := exists_isSylowTwoOf_of_le (hS.le.trans inf_le_right) hS.isPGroup
  have hSeq : S = S' := by
    by_contra hne
    obtain ⟨x, ⟨hxS', hxN⟩, hxS⟩ := exists_mem_inf_normalizer_of_ne hS'.isPGroup hSS' hne
    have hXK : S' ⊓ Subgroup.normalizer (S : Set G) ≤ M ⊓ NU :=
      le_inf (inf_le_right.trans hNS) (inf_le_left.trans hS'.le)
    have hX := hS.eq_of_le (le_inf hSS' Subgroup.le_normalizer) hXK
      (hS'.isPGroup.to_le inf_le_left)
    exact hxS (hX ▸ ⟨hxS', hxN⟩)
  exact ⟨S, hJS, hS.le, hSeq ▸ hS'⟩

theorem not_two_dvd_relIndex (h323 : Stmt3_2_3) (h3228 : Stmt3_2_2_eight)
    (h : FSU G T L V₀) (hV : IsVplus T L V₀ Vp)
    (hJ : thompsonJ T ≤ Subgroup.centralizer (Vp : Set G)) {U : Subgroup G} (hU : U ≤ Vp) :
    ¬ 2 ∣ (Subgroup.normalizer (conjClosure L T : Set G) ⊓
      Subgroup.normalizer (U : Set G)).relIndex (Subgroup.normalizer (U : Set G)) := by
  obtain ⟨S, -, hSK, hS⟩ := exists_isSylowTwoOf_normalizer h323 h3228 h hV hJ hU
  have hdvd : ((Subgroup.normalizer (conjClosure L T : Set G) ⊓
      Subgroup.normalizer (U : Set G)).subgroupOf (Subgroup.normalizer (U : Set G))).index ∣
        (S.subgroupOf (Subgroup.normalizer (U : Set G))).index :=
    Subgroup.index_dvd_of_le fun x hx => hSK hx
  exact fun h2 => hS.2.2 (h2.trans hdvd)

end Prop3210

theorem stmt3_2_10_eight_holds
    (h38 : CFSG.QuasithinUnique.Vol2Native.A38ForSQTKCat)
    (h39 : CFSG.QuasithinUnique.Vol2Native.A39ForSQTKCat) : Stmt3_2_10_eight :=
  stmt3_2_10_eight_of (stmt3_2_3_of_a38_a39 h38 h39) stmt3_2_2_eight_proved

theorem stmt3_2_10_eight_V_holds
    (h38 : CFSG.QuasithinUnique.Vol2Native.A38ForSQTKCat)
    (h39 : CFSG.QuasithinUnique.Vol2Native.A39ForSQTKCat) :
    ∀ (G : Type) [Group G] [Finite G] (T L V₀ : Subgroup G), FSU G T L V₀ →
      thompsonJ T ≤ Subgroup.centralizer (conjClosure V₀ T : Set G) →
      ∀ S : Subgroup G, IsPGroup 2 ↥S → thompsonJ T ≤ S →
        thompsonJ T = thompsonJ S ∧
          Subgroup.normalizer (S : Set G) ≤ Subgroup.normalizer (conjClosure L T : Set G) :=
  stmt3_2_10_eight_of_V (stmt3_2_3_of_a38_a39 h38 h39) stmt3_2_2_eight_proved

end CFSG.Quasithin.H13
