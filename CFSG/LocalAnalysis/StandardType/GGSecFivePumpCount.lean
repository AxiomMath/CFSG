module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosDefs
import CFSG.LocalAnalysis.StandardType.GGSpJoinReflPairing
import CFSG.LocalAnalysis.StandardType.GGSpJoinReflAlgebra
import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelAut
import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelTypeAAssembly
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosBridge
import CFSG.LocalAnalysis.StandardType.GGTableBTransport

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal

theorem ggDk_card_bstar_ge {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e) {k : ℕ} (hk : 4 ≤ k)
    {σ : Fin k ≃ ι} (hM : M = (ggCoxeterMatrixD k).reindex σ) : p ^ k ≤ Nat.card Bs := by
  have hp : p.Prime := hcfg.1.1.1.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hcfg.1.1.1.2.2.2.2.2.1.2.1
  have : Fact p.Prime := ⟨hp⟩
  have hBs : IsElemAbelian p Bs := hcfg.1.1.2.1.2.1
  have hW : GGWeylOfType p (ggCoxeterMatrixD k) (ggAutomizerJoin L Bs 𝒦) := by
    subst hM
    exact GGWeylOfType.of_reindex ⟨e, hpres.2⟩
  have hind : ∀ φ ∈ ggAutomizerJoin L Bs 𝒦, φ ∈ ggInduced ⊤ Bs := fun φ hφ =>
    mem_ggInduced_top_of_mem_ggAutomizer (ggAutomizerJoin_le_top L Bs 𝒦 hφ)
  obtain ⟨V, _, _, ⟨ιV⟩⟩ := exists_ggLinData (p := p) hBs
  have : Finite V := Finite.of_equiv _ (Additive.ofMul.trans ιV.toEquiv)
  have : Module.Finite (ZMod p) V := Module.Finite.of_finite
  obtain ⟨h, α, hP⟩ :=
    SpJoinRefl.exists_cartan_pairing_D hp2 (ggRouteCfg_noTransvection hcfg) hk hW hind ιV
  have hkV := SpJoinRefl.le_finrank_of_cartanD hp2 (by omega) h α hP
  have hcardV : Nat.card Bs = p ^ Module.finrank (ZMod p) V := by
    rw [card_eq_of_ggLin ιV, Module.natCard_eq_pow_finrank (K := ZMod p) (V := V), Nat.card_zmod]
  exact hcardV ▸ Nat.pow_le_pow_right hp.pos hkV

theorem ggDk_card_bstar_bounds
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {ι : Type}
    {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e) {k : ℕ} (hk : 4 ≤ k)
    {σ : Fin k ≃ ι} (hM : M = (ggCoxeterMatrixD k).reindex σ) {t : StatedLieTag} {n f : ℕ}
    {ψ : (ggU t n f).K →* G} (hTB : GGTableBPos p Bs L t n f ψ) :
    p ^ k ≤ Nat.card Bs ∧ Nat.card Bs ≤ p ^ ((ggU t n f).D.rank + 1) ∧
      k ≤ (ggU t n f).D.rank + 1 := by
  have hp : p.Prime := hcfg.1.1.1.2.2.2.2.2.1.1
  have hBs : IsElemAbelian p Bs := hcfg.1.1.2.1.2.1
  have hlow : p ^ k ≤ Nat.card Bs := ggDk_card_bstar_ge hcfg hpres hk hM
  obtain ⟨-, -, -, hTBc⟩ := hTB
  obtain ⟨-, -, -, -, hcyc⟩ := hcfg.1.1.1.2.2.2.2.2.2.1
  have hE : IsElemAbelian p (Bs ⊓ Subgroup.centralizer (L : Set G)) :=
    TableB.isElemAbelian_mono hBs inf_le_left
  have hCp : Nat.card ↥(Bs ⊓ Subgroup.centralizer (L : Set G)) ≤ p :=
    TableB.card_le_of_isCyclic hp.pos (hcyc _ inf_le_right (TableB.isPGroup_of_isElemAbelian hE))
      hE.2
  have hup : Nat.card Bs ≤ p ^ ((ggU t n f).D.rank + 1) := by
    rw [pow_succ]
    exact hTBc.trans (Nat.mul_le_mul_left _ hCp)
  exact ⟨hlow, hup, (Nat.pow_le_pow_iff_right hp.one_lt).mp (hlow.trans hup)⟩

end CFSG.StandardType

end
