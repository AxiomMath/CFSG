module

public import CFSG.RankThree.GF2n.Stroth80.Sec11CM
import CFSG.RankThree.GF2n.Stroth80.GuralnickSec1110Transport
import CFSG.RankThree.GF2n.Stroth80.GuralnickSec1110Rho
import CFSG.RankThree.GF2n.Stroth80.GuralnickSec1110Count
import CFSG.RankThree.GF2n.Stroth80.GuralnickSec1110I1
import CFSG.ClassicalGroups.Orthogonal.SiegelSL
import CFSG.Adapters.RankTwoModelTransports
public import CFSG.RankThree.GF2n.Stroth80.Sec3Action

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.Adapters.RankTwoModelTransports
open CFSG.ClassicalGroups.Orthogonal.SiegelSL
open CFSG.HardMathSupport.Kantor79
open scoped MatrixGroups

private theorem nonempty_statedProjEquiv_galoisField {G : Type} [Group G]
    {M Q Z B : Subgroup G} [(Q.subgroupOf M).Normal] {m x n₀ : ℕ}
    (hL : CFSG.Blueprint.LieModel (XbarMod M Q Z B) .PSL m 2 x)
    (hxZ : 2 ^ x = Nat.card Z) (hcard : Nat.card (GaloisField 2 n₀) = Nat.card Z) :
    Nonempty (XbarMod M Q Z B ≃* StatedProj (StatedSL m (GaloisField 2 n₀))) := by
  classical
  have hCM := hL.statedClassicalModel (by simp [CFSG.Blueprint.classicalTags])
  obtain ⟨-, F, hF, hFfin, hFcard, ⟨eF⟩⟩ := hCM
  letI : Field F := hF
  letI : Finite F := hFfin
  letI : Fintype F := Fintype.ofFinite F
  letI : Fintype (GaloisField 2 n₀) := Fintype.ofFinite _
  have hcardF : Fintype.card F = Fintype.card (GaloisField 2 n₀) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    exact hFcard.trans (hxZ.trans hcard.symm)
  let ψ : F ≃+* GaloisField 2 n₀ := FiniteField.ringEquivOfCardEq hcardF
  exact ⟨eF.trans (statedProjCongr (glCongr (ι := Fin m) ψ)
    (glCongr_statedSL (φ := ψ) m) (glCongr_statedScalars (ι := Fin m) ψ))⟩

theorem cmLmChain_holds : CMLmChain := by
  rintro G _ _ M Q Z B _ hc n m x hw hn ha2 hL hm
  obtain ⟨n₀, γ, M₀, -, hD⟩ := stroth_globalModelDataGF hc.hyp
  obtain ⟨φ, hφπ, hφk, hφQ⟩ := exists_actionHom_H0 hc.hyp hD
  have hxZ : 2 ^ x = Nat.card Z := Ctx.two_pow_eq_card_Z_of_psl hc hw ha2 hL hm
  obtain ⟨e⟩ := nonempty_statedProjEquiv_galoisField (n₀ := n₀) hL hxZ hD.card
  obtain ⟨σ₀, hσ₀⟩ := Ctx.exists_slHom_Xbar hc hm e
  obtain ⟨ρ, hρ, hρQ, hlong, hS₀, hV⟩ :=
    Ctx.exists_slAct_cmComm hc ha2 hD φ hφπ hφk hφQ hm hσ₀
  have hsurj : Function.Surjective σ₀ := Ctx.slHom_Xbar_surjective hc hm hσ₀
  have hnd := Ctx.cmCommQf_nondegenerate hc hD φ hφπ
  have hlift : ∀ t : SL(m, GaloisField 2 n₀), IsTransvection t →
      ∀ s, IsLongRootElement (cmCommQf B φ) s → movedSpace s = movedSpace (ρ t) →
        ∃ g, ρ g = s := by
    intro t ht s hs hst
    obtain ⟨g, -, -, hg⟩ := exists_isTransvection_eq_of_movedSpace_eq hm (cmCommQf B φ) hnd
      ρ hρQ hS₀ ht hs hst
    exact ⟨g, hg⟩
  rcases exists_natural_or_dim_six_of_siegel hm (cmCommQf B φ) hnd ρ hρQ hS₀ hV with
    ⟨W₁, W₂, hW, hW₁s, hW₂s, hW₁, hW₂, hdim₁, hdim, ⟨σ, F, hFσ, hFinj, hFW, hFsurj, hFeq⟩,
      ⟨σ', F', hF'σ, hF'inj, hF'W, hF'surj, hF'eq⟩⟩ |
    ⟨-, -, t₁, t₂, ht₁, ht₂, -, hmeet, hno⟩
  · obtain ⟨-, htop⟩ := Ctx.cmComm_eq_top_of_rt1 hc ha2 hD φ hφπ hφk hw (by omega) hm hsurj
      hρ hW hW₁s hW₂s hdim₁ hdim hFσ hFinj hFW hFsurj hFeq hF'σ hF'inj hF'W hF'surj hF'eq
    exact Or.inl (Ctx.cmLmChain_chain_of_rt1 hc hD φ hφπ hm hsurj hρ htop hW hW₁ hW₂ hFinj
      hFW hFsurj hFeq hF'inj hF'W hF'surj hF'eq)
  · exact (Ctx.false_of_siegel_axes hc hD φ hφπ hρ (hlong t₁ ht₁) (hlong t₂ ht₂) hmeet hno
      (hlift t₁ ht₁) (hlift t₂ ht₂)).elim

end CFSG.RankThree.GF2n.Stroth80
