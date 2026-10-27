module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec118Center
public import CFSG.ClassicalGroups.Symplectic.StatedSpTransport
import CFSG.RankThree.GF2n.Stroth80.Sec118FieldEqA2
public import CFSG.RankThree.GF2n.Stroth80.Sec11CM

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalGroups.Alternating CFSG.ClassicalGroups.Symplectic
open scoped Matrix

variable {G : Type} [Group G] {M Q Z B : Subgroup G}

section Certificates


theorem Ctx.card_Z_le_two_pow_of_not_transvAt [Finite G]
    [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) {n m x : ℕ} (hw : Width Q Z n) (hn : 2 < n)
    (hLm : CFSG.Blueprint.LieModel (XbarMod M Q Z B) .PSp m 2 x)
    {a : ↥M} {h : (a : G) ∈ LB M Q B ∧ IsA2 Q Z (a : G)}
    (hA : ∀ {K : Type} [Field K] [Finite K] [CharP K 2], Nat.card K = 2 ^ x →
      ∀ ψ : ↥(Xbar M Q Z B) ≃* StatedSp m K, 3 ≤ m ∧
        ∃ a₁ c₁ : Fin m ⊕ Fin m → K, spForm m K a₁ c₁ = 0 ∧ LinearIndependent K ![a₁, c₁] ∧
          ∀ v : Fin m ⊕ Fin m → K,
            (((ψ ⟨QuotientGroup.mk a, mk_mem_Xbar_of_LB M Q Z B a h.1 h.2⟩ : StatedSp m K) :
              GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ v =
              v + spForm m K v a₁ • c₁ + spForm m K v c₁ • a₁) :
    Nat.card Z ≤ 2 ^ x := by
  obtain ⟨K, hKf, hKfin, hK, hchar, ⟨ψ⟩⟩ := hc.exists_mulEquiv_statedSp_of_lieModel_psp hLm
  obtain ⟨hm3, a₁, c₁, hac, hind, hmat⟩ := hA hK ψ
  set φ : ↥(Xbar M Q Z B) →* GL (Fin m ⊕ Fin m) K :=
    (StatedSp m K).subtype.comp ψ.toMonoidHom with hφdef
  have hφrange : φ.range = StatedSp m K := by
    rw [hφdef, MonoidHom.range_comp, MonoidHom.range_eq_top.mpr ψ.surjective,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hφinj : Function.Injective φ := Subtype.val_injective.comp ψ.injective
  have hρbij : Function.Bijective (toGsp φ hφrange) := by
    refine ⟨?_, toGsp_surjective φ hφrange⟩
    rw [← MonoidHom.ker_eq_bot_iff, ker_toGsp, (MonoidHom.ker_eq_bot_iff φ).mpr hφinj]
  have hρa : toGsp φ hφrange ⟨QuotientGroup.mk a, mk_mem_Xbar_of_LB M Q Z B a h.1 h.2⟩ =
      lineElt (spForm_isAlt (m := m) (K := K)) a₁ c₁ := by
    refine Gsp.ext' fun v => ?_
    rw [toGsp_app, lineElt_app (spForm_isAlt (m := m) (K := K)) hac]
    exact hmat v
  have h6 : 6 ≤ Module.finrank K (Fin m ⊕ Fin m → K) := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
    omega
  have := hc.card_Z_le_card_of_lineElt (a := a) (h := h) hw hn spForm_isAlt spForm_nondegenerate h6
    (toGsp φ hφrange) hρbij hac hind hρa
  rw [hK] at this
  exact this

end Certificates

end CFSG.RankThree.GF2n.Stroth80
