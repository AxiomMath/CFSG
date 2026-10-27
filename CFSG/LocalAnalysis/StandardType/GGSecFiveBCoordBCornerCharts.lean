module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveDataSpSpTwo
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBCornerDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSpPlaneFrameDefs
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSpPlaneCharts
import CFSG.LocalAnalysis.StandardType.GGSecFiveBNbrCompare
import CFSG.ClassicalInvolution.WeakCT.SpSpGlue
import CFSG.Assembly.Subnormal

public section

namespace CFSG.StandardType

open CFSG.Open

variable {G : Type} [Group G]

theorem exists_swap_lift_of_bSignedFull {L Bs : Subgroup G} {𝒦 : Finset (Subgroup G)} {n p : ℕ}
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))}
    (hEta : (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull n p)
    {a b : Fin n} (hab : a ≠ b) :
    ∃ g ∈ L ⊔ ⨆ K ∈ 𝒦, K, ∃ hg : g ∈ Subgroup.normalizer (Bs : Set G),
      MulAut.congr eta (ggConjAut Bs hg) = SpCoord.permAut (Equiv.swap a b) := by
  have hle : ggAutomizerJoin L Bs 𝒦 ≤ ggAutomizer (L ⊔ ⨆ K ∈ 𝒦, K) Bs := by
    refine sup_le (ggAutomizer_mono Bs le_sup_left) (iSup_le fun K => iSup_le fun hK => ?_)
    exact ggAutomizer_mono Bs
      (le_sup_of_le_right (le_iSup₂ (f := fun K (_ : K ∈ 𝒦) => K) K hK))
  have hmem : SpCoord.permAut (Equiv.swap a b) ∈
      (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom := by
    rw [hEta]
    exact Subgroup.subset_closure (Or.inr ⟨a, b, hab, rfl⟩)
  obtain ⟨g, hg, hgW, hgτ⟩ := exists_mem_of_mem_map_congr eta (Subgroup.map_mono hle hmem)
  exact ⟨g, hgW, hg, hgτ⟩

section Inputs


theorem GGSecFiveRouteCfg.ggSecFiveData_of_corner_charts [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)} (hR : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦)
    {s : ℕ} (hs : 2 ≤ s) {eta : ↥Bs ≃* (Fin (s + 3) → Multiplicative (ZMod 3))}
    {π : Fin (s + 3) ≃ Fin (s + 3)} {κ : StatedSp (s + 2) (GaloisField 2 1) →* G}
    {ζ : Multiplicative (ZMod 3) →* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 1)}
    (hκ : GGSecFiveBPermSpPlaneFrame Bs L eta π κ ζ) {g w : G}
    (hg : g ∈ Subgroup.normalizer (Bs : Set G))
    (hgη : MulAut.congr eta (ggConjAut Bs hg) = SpCoord.permAut (Equiv.swap (π 0) (π 1)))
    (hw : w ∈ Subgroup.normalizer (Bs : Set G))
    (hwη : MulAut.congr eta (ggConjAut Bs hw) = SpCoord.permAut (Equiv.swap (π 0) (π 3)))
    (hG0 : ggG0 3 B x L D J = L ⊔ ⨆ K ∈ 𝒦, K) (hgG : g ∈ ggG0 3 B x L D J)
    (habs : ∀ K ∈ 𝒦, K ≤ L ⊔ L.map (MulAut.conj g).toMonoidHom) :
    GGSecFiveData 3 B x L D J := by
  obtain ⟨hstar, -⟩ := hR.1.1.2
  obtain ⟨hBle, -, -, hBsC⟩ := hstar
  obtain ⟨-, hxB, -, hLc₀, -⟩ := hR.1.1.1.2.2.2.2.2.2.1
  have hxBs : x ∈ Bs := hBle hxB
  have hLc : CFSG.Open.IsComponentOf L (Subgroup.centralizer ({x} : Set G)) :=
    CFSG.Assembly.isComponentOf_iff_open.mp hLc₀
  obtain ⟨κ₂, hκ₂, hκ₂r, hov, hlong, hcross⟩ :=
    ggSecFiveBPermZeta_overlap_of_swap_charTwo (s := s) (p := 3) (n := s + 3)
      (F := GaloisField 2 1) (K := L) (y := x) (by omega) hs hBsC hxBs hLc hκ hg hgη hw hwη
  obtain ⟨κ₂', hκ₂', hκ₂'r, hsh, hlo, hc1, hc2⟩ :=
    CFSG.ClassicalInvolution.WeakCT.exists_spSpCharts_of_overlap (s := s)
      (F := GaloisField 2 1) (κ₁ := κ) (κ₂ := κ₂) (by omega) hκ.1 hκ₂ hov hlong hcross
  have hLle : L ≤ ggG0 3 B x L D J := by
    rw [hG0]
    exact le_sup_left
  have hconjL : L.map (MulAut.conj g).toMonoidHom ≤ ggG0 3 B x L D J := by
    rintro _ ⟨l, hl, rfl⟩
    show MulAut.conj g l ∈ ggG0 3 B x L D J
    rw [MulAut.conj_apply]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hgG (hLle hl)) (Subgroup.inv_mem _ hgG)
  have hGG : ggG0 3 B x L D J = L ⊔ L.map (MulAut.conj g).toMonoidHom := by
    refine le_antisymm ?_ (sup_le hLle hconjL)
    rw [hG0]
    exact sup_le le_sup_left (iSup_le fun K => iSup_le fun hK => habs K hK)
  refine ggSecFiveData_of_spSpCharts_two (s := s) (by omega) κ κ₂' hκ.1 hκ₂' hsh hlo hc1 hc2 ?_
  rw [hGG, hκ.2.1, hκ₂'r, hκ₂r]

end Inputs

end CFSG.StandardType

end
