module

public import CFSG.Quasithin.Vol2.Ch12Sec1Lem4X

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin.E3 CFSG.LieType.BorelTits
  CFSG.Assembly.LowTwoRank EmptyFaithfulMultiple
open scoped IsMulCommutative

namespace Sec1214

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V V₁ V₂ T₀ : Subgroup G} {v : G}
  (c : Setting T L V V₁ V₂ v T₀)
include c

theorem sup_le_normalizer_thompsonJ (hFF : LemH9FF4) {X : Subgroup G}
    (hX : IsXSub T L V V₁ X) :
    T₀ ⊔ X ⊔ T ≤ Subgroup.normalizer (thompsonJ T : Set G) :=
  sup_le (sup_le (c.T₀_le_normalizer_thompsonJ hFF) hX.le_normalizer)
    (Subgroup.le_normalizer.trans (normalizer_le_normalizer_thompsonJ T))

theorem pCoreOf_ne_bot_H (hFF : LemH9FF4) {X : Subgroup G} (hX : IsXSub T L V V₁ X) :
    pCoreOf 2 (T₀ ⊔ X ⊔ T) ≠ ⊥ := by
  have hJ2 : IsPGroup 2 ↥(thompsonJ T) :=
    c.S.ctx.hyp.sylow.1.to_le (B6.thompsonJ_le T)
  have h1 : thompsonJ T ≤ pCoreOf 2 (T₀ ⊔ X ⊔ T) :=
    le_pCoreOf_of_le_normalizer 2 ((B6.thompsonJ_le T).trans le_sup_right)
      (c.sup_le_normalizer_thompsonJ hFF hX) hJ2
  intro hb
  exact c.thompsonJ_ne_bot (le_bot_iff.mp (hb ▸ h1))

theorem isSQTKCat_H (hFF : LemH9FF4) {X : Subgroup G} (hX : IsXSub T L V V₁ X) :
    CFSG.SectionRank.IsSQTKCat ↥(T₀ ⊔ X ⊔ T) := by
  have h := sqtkGroup_of_pCoreOf_ne_bot c.S.ctx.hyp.qtke c.S.ctx.hyp.simple
    c.S.ctx.hyp.nonabelian (c.pCoreOf_ne_bot_H hFF hX)
  exact ⟨CFSG.SectionRank.isStronglyQuasithin_iff.mpr h.1, h.2⟩

theorem le_normalizer_K (hFF : LemH9FF4) (h323 : Stmt3_2_3) {X : Subgroup G}
    (hX : IsXSub T L V V₁ X) {K : Subgroup G} (hK : K ∈ cComp (T₀ ⊔ X ⊔ T))
    (hq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K)) (hmax : quasithinIsMaximalLocal T K)
    (hfaith : quasithinIsFaithfulLocal T K) (hTK : T ≤ Subgroup.normalizer (K : Set G)) :
    T₀ ⊔ X ⊔ T ≤ Subgroup.normalizer (K : Set G) := by
  obtain ⟨-, ⟨-, huniq⟩, -⟩ := h323 G T K c.S.ctx.hyp.simple c.S.ctx.hyp.nonabelian
    c.S.ctx.hyp.qtke c.S.ctx.hyp.sylow hmax hfaith hq
  have hKT : conjClosure K T = K := le_antisymm (conjClosure_le fun t ht k hk =>
    (Subgroup.mem_normalizer_iff.mp (hTK ht) k).mp hk) (le_conjClosure K T)
  rw [hKT] at huniq
  have hJ2 : IsPGroup 2 ↥(thompsonJ T) :=
    c.S.ctx.hyp.sylow.1.to_le (B6.thompsonJ_le T)
  obtain ⟨M'', hM'', hle⟩ := exists_maxTwoLocal_ge ⟨thompsonJ T, c.thompsonJ_ne_bot, hJ2, rfl⟩
  have hHJ := c.sup_le_normalizer_thompsonJ hFF hX
  have hKH : K ≤ T₀ ⊔ X ⊔ T := le_of_mem_cComp hK
  rw [← huniq M'' hM'' ((sup_le hKH le_sup_right).trans (hHJ.trans hle))]
  exact hHJ.trans hle

theorem not_sp4 (h1101 : Stmt11_0_1) {K : Subgroup G} (hmax : quasithinIsMaximalLocal T K)
    (hfaith : quasithinIsFaithfulLocal T K)
    (h : ∃ n : ℕ, Even n ∧
      CFSG.Assembly.LowTwoRank.StatedClassicalModel (↥K ⧸ CFSG.pCore 2 ↥K) .PSp 2 2 n) : False := by
  obtain ⟨n, hn, hm⟩ := h
  have hn1 : 1 ≤ n := hm.1.2.1
  obtain ⟨k, rfl⟩ := hn
  exact h1101 G T K c.S.ctx.hyp.simple c.S.ctx.hyp.nonabelian c.S.ctx.hyp.qtke
    c.S.ctx.hyp.sylow hmax hfaith ⟨k + k, by omega, Or.inr (Or.inr (Or.inl
      (Or.inl ⟨by decide, hm⟩)))⟩

end Setting

end Sec1214

end CFSG.Quasithin.H13
