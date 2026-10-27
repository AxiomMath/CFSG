module

public import CFSG.Quasithin.Background.F7TwoInvSQTKList
public import CFSG.Milestones.CL_LIT_SQTK_simple_list

public section

namespace CFSG.Quasithin.F7Two

open CFSG.Milestones

theorem invAutGenSQTK_of_section
    (hsec : ∀ (X : Type) [Group X] [Finite X], CFSG.SectionRank.IsSQTKCat X →
      ∀ (H : Subgroup X) (N : Subgroup H) [N.Normal] [IsSimpleGroup (H ⧸ N)],
        (∃ a b : H ⧸ N, a * b ≠ b * a) → SQTKSimpleList (H ⧸ N))
    (hL3Odd : InvAutGenFamL3Odd) (hU3Odd : InvAutGenFamU3Odd)
    (hL3Even : InvAutGenFamL3Even) (hU3Even : InvAutGenFamU3Even)
    (hSp4 : InvAutGenFamSp4Even) (hG2 : InvAutGenFamG2Even) (h3D4 : InvAutGenFam3D4Even)
    (h2F4 : InvAutGenFam2F4) (hSz : InvAutGenFamSz) (hTits : InvAutGenFamTits)
    (hL5 : InvAutGenFamL5Two) (hSpor : InvAutGenFamSporadic) :
    InvAutGenSQTK := by
  intro X _ _ hSQTK H N _ hsimple hnonab φ hφ2 hφ1
  have := hsimple
  exact invAutGen_of_sqtkSimpleList hL3Odd hU3Odd hL3Even hU3Even hSp4 hG2 h3D4 h2F4 hSz hTits
    hL5 hSpor (hsec X hSQTK H N hnonab) φ hφ2 hφ1

theorem invAutGenSQTK_of_families
    (hL3Odd : InvAutGenFamL3Odd) (hU3Odd : InvAutGenFamU3Odd)
    (hL3Even : InvAutGenFamL3Even) (hU3Even : InvAutGenFamU3Even)
    (hSp4 : InvAutGenFamSp4Even) (hG2 : InvAutGenFamG2Even) (h3D4 : InvAutGenFam3D4Even)
    (h2F4 : InvAutGenFam2F4) (hSz : InvAutGenFamSz) (hTits : InvAutGenFamTits)
    (hL5 : InvAutGenFamL5Two) (hSpor : InvAutGenFamSporadic) :
    InvAutGenSQTK :=
  invAutGenSQTK_of_section (fun X _ _ hSQTK H N _ _ hnonab =>
    cl_lit_sqtk_simple_list_section X hSQTK H N hnonab)
    hL3Odd hU3Odd hL3Even hU3Even hSp4 hG2 h3D4 h2F4 hSz hTits hL5 hSpor

end CFSG.Quasithin.F7Two
