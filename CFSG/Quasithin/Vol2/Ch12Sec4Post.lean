module

public import CFSG.Quasithin.Vol2.Ch12Sec4Statements
public import CFSG.Quasithin.Vol2.Ch12Sec8OneLemma8

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint

@[expose] def MParam1244 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G), Cx1242 G T L V →
    (Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) ∨
        LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1) →
      ∃ hV : IsElemAbelian 2 V, E3.mParam (autI hV ⊤) = 2

variable {G : Type} [Group G]

theorem post1244_core (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (hpre : Pre1242) [Finite G]
    {T L V : Subgroup G} (hcx : Cx1242 G T L V)
    (hq : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) ∨
      LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1) :
    ∃ z : G, orderOf z = 2 ∧ V ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers z ∧
      Subgroup.normalizer (L : Set G) = Subgroup.centralizer ({z} : Set G) ∧
      Subgroup.normalizer (L : Set G) = Subgroup.normalizer (V : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hyp := hcx.hyp
  rcases h1222 G T hyp.simple hyp.nonabelian hyp.qtke hyp.sylow with hAlt | h3
  · exact absurd hAlt hyp.notAlt
  obtain ⟨-, -, hall⟩ := h3 L hyp.maximal hyp.faithful hyp.quasisimple
  obtain ⟨⟨hVT, hTV, -, -⟩, -, hnorm, -, -⟩ := hall V hyp.irrPlus
  obtain ⟨-, h331B⟩ := h331 G T hyp.simple hyp.nonabelian hyp.qtke hyp.sylow
  obtain ⟨⟨hMmax, -, -⟩, -, -, -, -⟩ := h331B L hyp.maximal hyp.quasisimple
  rw [hyp.conjClosure_eq] at hMmax
  have hZV : V ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥ := by
    rcases hcx.cx with ⟨-, h⟩ | ⟨⟨e5⟩, -, -⟩
    · exact h
    · exfalso
      have h5 : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 9999360 := by
        rw [Nat.card_congr e5.toEquiv, card_sl_five_zmod_two]
      rcases hq with he | hU
      · obtain ⟨e⟩ := he
        rw [Nat.card_congr e.toEquiv, card_sl_three_zmod_two] at h5
        norm_num at h5
      · rw [card_of_lieModel_psu_three_three hU] at h5
        norm_num at h5
  obtain ⟨z, hzVZ, hz2, hGz, hzeq, -⟩ := hpre G T L V hcx
  have hzeq := hzeq hq
  have hz1 : z ≠ 1 := fun h => by
    rw [h, orderOf_one] at hz2
    norm_num at hz2
  have hMV : Subgroup.normalizer (L : Set G) ≤ Subgroup.normalizer (V : Set G) :=
    hnorm.resolve_right hZV
  have hMz : Subgroup.normalizer (L : Set G) ≤ Subgroup.centralizer ({z} : Set G) := by
    intro m hm
    have hZ2 : Nat.card ↥(V ⊓ Subgroup.centralizer (L : Set G)) = 2 := by
      rw [hzeq, Nat.card_zpowers, hz2]
    have hmZ : m ∈ Subgroup.normalizer
        ((V ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) : Set G) :=
      Subgroup.inf_normalizer_le_normalizer_inf
        ⟨hMV hm, F7.normalizer_le_normalizer_centralizer L hm⟩
    have hzZ : z ∈ V ⊓ Subgroup.centralizer (L : Set G) := by
      rw [hzeq]
      exact Subgroup.mem_zpowers z
    have h1 := Subgroup.mem_centralizer_iff.1
      (le_centralizer_normalizer_of_card_eq_two hZ2 hzZ) m hmZ
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact h1
  have hVM : Subgroup.normalizer (V : Set G) ≤ Subgroup.normalizer (L : Set G) := by
    have hV1 : V ≠ ⊥ := hyp.irrPlus.2.1
    have hVp : IsPGroup 2 V := hyp.sylow.1.to_le hVT
    have hVO : V ≤ pCoreOf 2 (Subgroup.normalizer (V : Set G)) :=
      LieType.BorelTits.le_pCoreOf_normalizer 2 V hVp
    obtain ⟨M', hM', hle⟩ := exists_inM_of_pCoreOf_ne_bot (H := Subgroup.normalizer (V : Set G))
      (fun h => hV1 (le_bot_iff.1 (h ▸ hVO)))
    have h1 := hMmax.2 M' hM'.1 (hMV.trans hle)
    rw [← h1]
    exact hle
  exact ⟨z, hz2, hzeq, le_antisymm hMz hGz, le_antisymm hMV hVM⟩

theorem post1244_of (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (hpre : Pre1242)
    (hm : MParam1244) : Post1244 := by
  intro G _ _ T L V hcx hq
  obtain ⟨z, h1, h2, h3, h4⟩ := post1244_core h331 h1222 hpre hcx hq
  exact ⟨z, h1, h2, h3, h4, hm G T L V hcx hq⟩

end CFSG.Quasithin.H13
