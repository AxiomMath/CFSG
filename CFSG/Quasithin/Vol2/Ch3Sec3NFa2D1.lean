module

public import CFSG.Quasithin.Vol2.Ch3Sec3NFa2Basic

public section

namespace CFSG.Quasithin.H13.NFa2

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Quasithin
open CFSG.Quasithin.CosetGeom CFSG.ASVolI.ChF
open CFSG.Quasithin.H13.Ch3Sec3
open scoped IsMulCommutative

theorem leaf_D1_of_LS1 (hLS1 : Leaf_LS1) (h9 : Stmt3_3_9) :
    ∀ (G : Type) [Group G] [Finite G] (T M L D H K : Subgroup G) (q : ℕ),
      A2Cfg G T M L D H K q →
        ∀ A : Subgroup G, A ≤ pCoreOf 2 (a2G1 L T ⊓ a2G2 K T) →
          ¬ A ≤ Subgroup.centralizer (a2V L T : Set G) →
            mIdx A (A ⊓ Subgroup.centralizer (a2V L T : Set G)) <
              mIdx (a2V L T) (a2V L T ⊓ Subgroup.centralizer (A : Set G)) := by
  intro G _ _ T M L D H K q c A hA hAV
  have hA2 : IsPGroup 2 A := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _).to_le hA
  rw [hLS1 G T M L D H K q c, ← c.rD_eq] at hA
  obtain ⟨-, -, hTV, -, -, hRT, -⟩ := L3321.setting_facts c.nf.hyp c.TL
  have hAN : A ≤ Subgroup.normalizer (vPlus L T : Set G) := hA.trans (hRT.trans hTV)
  obtain ⟨-, ⟨e⟩, hc, hmodE, -, -⟩ := c.site
  have hne : ∃ k ∈ autOn L (vPlus L T), k ≠ 1 := by
    have hcard : Nat.card ↥(autOn L (vPlus L T)) = 20160 := by
      rw [Nat.card_congr e.toEquiv, Ln2.card_specialLinear 4 (Or.inl rfl)]
      rfl
    have : Nontrivial ↥(autOn L (vPlus L T)) :=
      Finite.one_lt_card_iff_nontrivial.1 (by rw [hcard]; norm_num)
    obtain ⟨k, hk⟩ := exists_ne (1 : ↥(autOn L (vPlus L T)))
    exact ⟨k, k.2, fun h1 => hk (Subtype.ext h1)⟩
  have hAR : autOn A (vPlus L T) ≤ autOn (L3321.rD T L) (vPlus L T) :=
    CFSG.Quasithin.AutOn.autOn_mono hA
  have hA' : autOn A (vPlus L T) ≠ ⊥ :=
    CFSG.Quasithin.AutOn.autOn_ne_bot_of_not_le_centralizer hAN hAV
  have hoff := L3321.no_offender_ext h9 c.nf.hyp c.mPlus_eq c.TL hne hmodE hAR hA'
  rw [CFSG.Quasithin.AutOn.card_autOn_eq_relIndex hAN] at hoff
  have hfix := CFSG.Quasithin.AutOn.fixV_autOn_eq (L := A) hAN
  have hidx : (vPlus L T ⊓ Subgroup.centralizer (A : Set G)).relIndex (vPlus L T) *
      Nat.card ↥(fixV (autOn A (vPlus L T))) = Nat.card ↥(vPlus L T) := by
    rw [Subgroup.inf_relIndex_left, hfix]
    exact Subgroup.index_mul_card _
  rw [← hidx] at hoff
  have hlt := Nat.lt_of_mul_lt_mul_right hoff
  have hpA := HypF98.relIndex_eq_two_pow_mIdx (Y := A ⊓ Subgroup.centralizer (vPlus L T : Set G)) hA2
  have hpV := HypF98.relIndex_eq_two_pow_mIdx
    (Y := vPlus L T ⊓ Subgroup.centralizer (A : Set G))
    ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (L ⊔ T)).to_le c.V_le_Q)
  rw [hpA, hpV] at hlt
  exact (Nat.pow_lt_pow_iff_right (by norm_num)).1 hlt

end CFSG.Quasithin.H13.NFa2
