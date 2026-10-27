module

public import CFSG.LocalAnalysis.StandardType.GGL45NtGlue
public import CFSG.LocalAnalysis.StandardType.GGL45NtHFourAut
public import CFSG.LocalAnalysis.StandardType.GGL45NtVacRaw
public import CFSG.LocalAnalysis.StandardType.GGL45NtHFourD4

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggL45TorusHRaw_of_nt {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel} {R : Type} [Group R]
    {I F : Set (MulAut R)} (hsimp : GGL45NtSimp R I F) (hrec : GGL45NtRec p R I F)
    (hcore : GGL45NtCore p R I F) (h4 : GGL45H4Raw p lab R I F) : GGL45TorusHRaw p lab R I F :=
  fun K _ _ θ hK _ ψ E hyp =>
    ggL45TorusH_of_parts (ggL45TorusH123_of_core hp hsimp hrec hcore θ hK hyp) (h4 K θ hK ψ E hyp)

theorem ggL45TorusHKnownFormsOn_of_nt {S : ℕ → LargeEvenLabel → Prop} (hsimp : GGL45NtSimpOn S)
    (hrec : GGL45NtRecOn S) (hcore : GGL45NtCoreOn S) (h4 : GGL45NtH4On S) :
    GGL45TorusHKnownFormsOn S :=
  (((hsimp.and hrec).and hcore).and h4).mono fun _ hp _ _ _ _ _ h =>
    ggL45TorusHRaw_of_nt hp h.1.1.1 h.1.1.2 h.1.2 h.2

theorem ggL45TorusHKnownFormsOn_of_vac {S : ℕ → LargeEvenLabel → Prop} (h : GGL45NtVacOn S) :
    GGL45TorusHKnownFormsOn S :=
  h.mono fun _ _ _ _ _ _ _ h => ggL45TorusHRaw_of_vac h

theorem ggL45NtH4On_of_aut {S : ℕ → LargeEvenLabel → Prop} (hsimp : GGL45NtSimpOn S)
    (h : GGL45NtAutOn S) : GGL45NtH4On S :=
  (hsimp.and h).mono fun _ hp _ _ _ _ _ h => ggL45H4Raw_of_aut hp h.1 h.2

theorem ggL45NtH4On_d4_three : GGL45NtH4On GGL45NtD43 := by
  rintro p _ _ lab _ _ ⟨_, ht, h4, rfl⟩
  exact ggL45H4Raw_d4_three ht h4

theorem ggL45TorusHKnownFormsOn_cl_of_nt (hsimp : GGL45NtSimpOn GGL45NtFamCl)
    (hrec : GGL45NtRecOn GGL45NtFamCl) (hcore : GGL45NtCoreOn GGL45NtFamCl)
    (haut : GGL45NtAutOn GGL45NtFamClAut) : GGL45TorusHKnownFormsOn GGL45NtFamCl :=
  ggL45TorusHKnownFormsOn_of_nt hsimp hrec hcore
    ((ggL45NtH4On_of_aut (hsimp.antitone fun _ _ h => h.1) haut |>.union
      ggL45NtH4On_d4_three).antitone ggL45NtFamCl_split)

theorem ggL45TorusHKnownFormsOn_nonTorsion_of_nt
    (hsimp : GGL45NtSimpOn GGL45FamNonTorsion) (hvac : GGL45NtVacOn GGL45NtFamVac)
    (hrecCl : GGL45NtRecOn GGL45NtFamCl) (hcoreCl : GGL45NtCoreOn GGL45NtFamCl)
    (hautCl : GGL45NtAutOn GGL45NtFamClAut)
    (hrecEx : GGL45NtRecOn GGL45NtFamEx) (hcoreEx : GGL45NtCoreOn GGL45NtFamEx)
    (hautEx : GGL45NtAutOn GGL45NtFamEx) :
    GGL45TorusHKnownFormsOn GGL45FamNonTorsion :=
  ggL45TorusHKnownFormsOn_of_split _ GGL45NtFamVac
    (fun p lab => GGL45NtFamCl p lab ∨ GGL45NtFamEx p lab) ggL45NtFam_cover
    (ggL45TorusHKnownFormsOn_of_vac hvac)
    (ggL45TorusHKnownFormsOn_of_split _ GGL45NtFamCl GGL45NtFamEx (fun _ _ h => h)
      (ggL45TorusHKnownFormsOn_cl_of_nt (hsimp.antitone fun _ _ h => h.1) hrecCl hcoreCl hautCl)
      (ggL45TorusHKnownFormsOn_of_nt (hsimp.antitone fun _ _ h => h.1) hrecEx hcoreEx
        (ggL45NtH4On_of_aut (hsimp.antitone fun _ _ h => h.1) hautEx)))

end CFSG.StandardType
