module

public import CFSG.RankThree.PartTwo.Sec11.AutThree1129.L3
public import CFSG.RankThree.PartTwo.Sec11.AutThree1129.PGL
public import CFSG.RankThree.PartTwo.Sec11.AutThree1129.G2
public import CFSG.RankThree.PartTwo.Sec11.Item1117Res4ProofImage

public section

namespace CFSG.RankThree.PartTwo.Sec11.AutThree1129

open CFSG.RankThree.PartTwo

theorem autThreeAut_or {F G : ∀ (X : Type) [Group X], Prop} (hF : AutThreeAut F)
    (hG : AutThreeAut G) : AutThreeAut (fun (X : Type) [Group X] => F X ∨ G X) := by
  intro Z _ _ hZ α J hα3 hJ hJT hJ3 P hP
  obtain ⟨X, hX, hFG, hE⟩ := hZ
  rcases hFG with hFX | hGX
  · exact hF Z ⟨X, hX, hFX, hE⟩ α J hα3 hJ hJT hJ3 P hP
  · exact hG Z ⟨X, hX, hGX, hE⟩ α J hα3 hJ hJT hJ3 P hP

section Families

theorem autThree1129_of_d4 (hD4 : AutThreeAut (fun (X : Type) [Group X] =>
    ∃ (q : TauCeti.PrimePower) (hq : (TauCeti.LieTypeIndex.trialityD4 q).Valid),
      Nonempty (X ≃* (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hq⟩).Group))) :
    CFSG.RankThree.PartTwo.Sec11.AutThree1129 := by
  have hL3 : AutThreeAut Sec13.IsLThreePi := autThreeAut_l3
  have hPGL : AutThreeAut CFSG.RankThree.PartTwo.Sec11.IsPGL3PiFamily :=
    autThree_pgl_of_l3 autThreeAut_l3
  have hAll : AutThreeAut (fun (X : Type) [Group X] =>
      CFSG.RankThree.PartTwo.Sec11.IsList119 X) :=
    autThreeAut_or autThreeAut_g2 (autThreeAut_or hD4 (autThreeAut_or hL3
      (autThreeAut_or hPGL autThreeAut_spor)))
  have hFor : CFSG.RankThree.PartTwo.Sec11.AutThree1129For (fun (X : Type) [Group X] =>
      CFSG.RankThree.PartTwo.Sec11.IsList119 X) :=
    CFSG.RankThree.PartTwo.Sec11.autThree1129For_of_autThree hAll
  exact hFor

end Families

end CFSG.RankThree.PartTwo.Sec11.AutThree1129

end
