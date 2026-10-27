module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1ShortCore
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1ShortPSUAux

public section

namespace CFSG.StandardType.RCKC1

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank CFSG.StandardType
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.LieKnownR2.Short
  CFSG.StandardType.LieKnownR2.Geo CFSG.Open

theorem rckLemmaHCore_PSU
    {m g : ℕ} (hg : 1 ≤ g) {β : Fin (ggU .PSU m g).D.rank → ℤ}
    (hβ : β ∈ (ggU .PSU m g).D.roots) (hL : ¬ GGLongRoot (ggU .PSU m g).D β)
    (h2 : 2 • β ∉ (ggU .PSU m g).D.roots) : RCKLemmaHCore (ggU .PSU m g) β := by
  have e : ggU .PSU m g =
      ⟨SU (unitaryInvolution (GaloisField 2 (2 * g)) 2 g) m,
        Unitary.rootDatum (card_galoisField_two_mul 2 g hg) m⟩ := by
    simp only [ggU, lieUniversal, hg, ↓reduceDIte]
  revert β
  rw [e]
  intro β hβ hL h2
  intro x hx hx1
  obtain ⟨v, w, v', w', hfr, hmap, -⟩ :=
    exists_unitPairGroup_eq_conj_rootGroup_SU (card_galoisField_two_mul 2 g hg) m hβ hL h2
      (1 : SU (unitaryInvolution (GaloisField 2 (2 * g)) 2 g) m)
  have hconj1 : (MulAut.conj
      (1 : SU (unitaryInvolution (GaloisField 2 (2 * g)) 2 g) m)).toMonoidHom =
      MonoidHom.id (SU (unitaryInvolution (GaloisField 2 (2 * g)) 2 g) m) := by
    ext g; simp [MulAut.conj_apply]
  rw [hconj1, Subgroup.map_id] at hmap
  rw [hmap] at hx
  have h := rckSPSU_suPair_core m g hg hfr hx hx1
  simpa [hmap] using h

theorem rckK2NbrRootSubShortAt_PSU
    : RCKK2NbrRootSubShortAt .PSU := by
  intro X _ _ K R m g β ht hg hβ hL hS h2 hvia r hr hr1
  exact rckGL1_of_core ht hg (fun h => by first | exact absurd h (by decide) | omega)
    (rckLemmaHCore_PSU hg hβ hL h2) hvia hr hr1

end CFSG.StandardType.RCKC1
