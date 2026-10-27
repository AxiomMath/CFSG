module

public import CFSG.Quasithin.Recognition.Stroth.Str83Moufang
public import CFSG.Quasithin.Recognition.Stroth.LieExtInner
public import CFSG.Quasithin.EmptyFaithful.S1421QNSSurv
public import CFSG.Quasithin.Recognition.Stroth.IdSzL2W

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F112R

theorem idSzL2W_of_moufang (hM : Str83Moufang) (hO : Str83Orders) (hK : Str83Kernel)
    (hW : Weiss80Octagon) : IdSzL2W := by
  intro G _ _ L1 L2 S a hF ha hSz hBig hL2
  obtain ⟨e⟩ := hSz
  obtain ⟨hm, -, -, hS⟩ := hO G L1 L2 S a hF ha ⟨e⟩ hBig hL2
  obtain ⟨hK1, hK2⟩ := hK G L1 L2 S a hF ha ⟨e⟩ hBig hL2
  have hWM := hM G L1 L2 S a hF ha ⟨e⟩ hBig hL2
  have hsimp1 : IsSimpleGroup (oTwoQuot ↥L1) := by
    haveI := CFSG.SignalizerFunctorTheorem.McBride.SzModel.sz_isSimpleGroup ha
    exact e.isSimpleGroup
  have hsimp2 : IsSimpleGroup (oTwoQuot ↥L2) :=
    CFSG.Quasithin.S1421NS.isSimpleGroup_of_isL2Quot (by omega) hm
  have hN1 : HasNormalCopy (Subconst (L1 ⊔ bigB L1 L2 S) (L2 ⊔ bigB L1 L2 S)) ↥(Sz a) := by
    obtain ⟨N, hN, ⟨f⟩⟩ := f112_exists_normal_iso_oTwoQuot_left hF hsimp1
    exact ⟨N, hN, ⟨f.trans e⟩⟩
  have hN2 : HasNormalCopy (Subconst (L2 ⊔ bigB L1 L2 S) (L1 ⊔ bigB L1 L2 S))
      (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 (2 * a + 1))) := by
    obtain ⟨N, hN, ⟨f⟩⟩ := f112_exists_normal_iso_oTwoQuot_right hF hsimp2
    obtain ⟨g⟩ := hm
    exact ⟨N, hN, ⟨f.trans g⟩⟩
  obtain ⟨-, D, _, hD, hE⟩ :=
    hW G (L1 ⊔ bigB L1 L2 S) (L2 ⊔ bigB L1 L2 S) a (2 * a + 1) ha (by omega) hWM hK1 hK2 hN1
      hN2
      ⟨2 * (2 * a + 1), by omega, by
        rw [f112_parabolic_inf_eq_bigB hF]
        exact f112_relIndex_left_sz hF ha ⟨e⟩⟩
      ⟨2 * a + 1, by omega, by
        rw [f112_parabolic_inf_eq_bigB hF]
        exact f112_relIndex_right_l2 hF (by omega) hm⟩
  exact ⟨hm, isAmalgamOfGroup_twistedF4_of_ext hF ha ⟨e⟩ hm hS hD hE⟩

end CFSG.Quasithin.Stroth
