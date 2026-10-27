module

public import CFSG.Fischer.Classification.Unitary.Model
public import CFSG.RankThree.GF2n.Tim79aSUStatements

public section

namespace CFSG.RankThree.GF2n.Stroth78

open CFSG.Fischer.Classification CFSG.Fischer.Classification.Unitary
open CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary
open CFSG.Blueprint.Fischer (K)

variable {m : ℕ}

section Witt

open Matrix CFSG.Timmesfeld.LieEmbed

theorem herm_mulVec_mulVec_of_witt {P : Matrix (Fin m) (Fin m) K}
    (hP : conjTr frob P * P = antidiag m) (x y : Fin m → K) :
    herm frob (P *ᵥ x) (P *ᵥ y) = uForm frob x y := by
  have h1 : herm frob (P *ᵥ x) (P *ᵥ y) = (fun i => frob ((P *ᵥ x) i)) ⬝ᵥ (P *ᵥ y) := rfl
  have h2 : uForm frob x y = (fun i => frob (x i)) ⬝ᵥ (antidiag m *ᵥ y) := rfl
  rw [h1, h2, map_mulVec_sigma, ← hP, ← Matrix.mulVec_mulVec, conjTr,
    Matrix.dotProduct_mulVec (fun i => frob (x i)) (P.map frob)ᵀ (P *ᵥ y),
    Matrix.vecMul_transpose]

theorem rootS2Model_U2 (hm : 4 ≤ m) {v : Fin m → K} (hv0 : v ≠ 0) (hv : herm frob v v = 0) :
    CFSG.RankThree.GF2n.Tim79a.RootS2Model (U2 m) (Subgroup.zpowers (tqU v)) := by
  classical
  obtain ⟨P, hP⟩ := exists_wittMatrix card_K m
  set e : SU frob m ≃* SUid frob m := conjEquiv P hP with he
  set Φ : SU frob m →* U2 m := ((u2Equiv m).symm.toMonoidHom.comp
    (QuotientGroup.mk' (Subgroup.center (SUid frob m)))).comp e.toMonoidHom with hΦ
  have hsurj : Function.Surjective Φ :=
    (u2Equiv m).symm.surjective.comp ((QuotientGroup.mk'_surjective _).comp e.surjective)
  have hker : Φ.ker ≤ Subgroup.center (SU frob m) := by
    intro x hx
    simpa [Φ] using hx
  set Pm : Matrix (Fin m) (Fin m) K := (P : Matrix (Fin m) (Fin m) K)
  set Pi : Matrix (Fin m) (Fin m) K := ((P⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K)
  have hPPi : Pm * Pi = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hPPi' : ∀ y, Pm *ᵥ (Pi *ᵥ y) = y := fun y => by
    rw [Matrix.mulVec_mulVec, hPPi, Matrix.one_mulVec]
  set a : Fin m → K := Pi *ᵥ v
  have hPa : Pm *ᵥ a = v := hPPi' v
  have haa : uForm frob a a = 0 := by
    rw [← herm_mulVec_mulVec_of_witt hP, hPa, hv]
  have ha0 : a ≠ 0 := by
    intro h
    apply hv0
    rw [← hPa, h, Matrix.mulVec_zero]
  obtain ⟨T, hT⟩ := CFSG.Timmesfeld.Transvection.ModelRank.exists_isUTransGroup frob_frob haa
  have hconj : ∀ (x : SU frob m) (c : K), suMat frob m x = uTrans frob a c →
      ∀ y : Fin m → K, e x • y = y + (c * herm frob v y) • v := by
    intro x c hx y
    rw [smul_def, he, coe_conjEquiv, Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec]
    have hxm : ((x : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) = uTrans frob a c := hx
    rw [hxm, uTrans_mulVec, Matrix.mulVec_add, Matrix.mulVec_smul, hPa, hPPi',
      ← herm_mulVec_mulVec_of_witt hP, hPa, hPPi']
  have hΦ1 : ∀ x : SU frob m, suMat frob m x = uTrans frob a 1 → Φ x = tqU v := by
    intro x hx
    have hex : e x = tvU v := ext_smul frob fun y => by
      rw [hconj x 1 hx y, one_mul, tvU_smul hv]
    simp only [Φ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hex]
    rfl
  have hΦ0 : ∀ x : SU frob m, suMat frob m x = uTrans frob a 0 → Φ x = 1 := by
    intro x hx
    have hx1 : x = 1 := suMat_injective frob (by rw [hx, uTrans_zero, map_one])
    rw [hx1, map_one]
  have hmap : T.map Φ = Subgroup.zpowers (tqU v) := by
    apply le_antisymm
    · rintro _ ⟨x, hxT, rfl⟩
      obtain ⟨c, hc, hxc⟩ := (hT.1 x).1 hxT
      rcases (add_frob_eq_zero_iff c).1 hc with rfl | rfl
      · rw [hΦ0 x hxc]
        exact Subgroup.one_mem _
      · rw [hΦ1 x hxc]
        exact Subgroup.mem_zpowers _
    · rw [Subgroup.zpowers_le]
      obtain ⟨x₁, hx₁⟩ := hT.2 1 one_add_frob_one
      exact ⟨x₁, (hT.1 x₁).2 ⟨1, one_add_frob_one, hx₁⟩, hΦ1 x₁ hx₁⟩
  have h := CFSG.RankThree.GF2n.Tim79a.suModelS2_holds m K 1 card_K hm (U2 m) Φ hsurj hker a T
    ha0 haa hT
  rwa [hmap] at h

end Witt

theorem not_isSymplecticType_DU (hm : 3 ≤ m) : ¬ IsSymplecticType (DU m) := by
  classical
  set i₀ : Fin m := ⟨0, by omega⟩
  set i₁ : Fin m := ⟨1, by omega⟩
  set i₂ : Fin m := ⟨2, by omega⟩
  have h01 : i₀ ≠ i₁ := by simp [i₀, i₁, Fin.ext_iff]
  have h02 : i₀ ≠ i₂ := by simp [i₀, i₂, Fin.ext_iff]
  have h12 : i₁ ≠ i₂ := by simp [i₁, i₂, Fin.ext_iff]
  set vd : Fin m → K := Pi.single i₀ 1 + Pi.single i₁ 1
  set ve : Fin m → K := Pi.single i₀ 1 + Pi.single i₂ 1
  set vf : Fin m → K := Pi.single i₀ 1 + Pi.single i₁ ω
  have hm2 : 2 ≤ m := by omega
  have hvd : herm frob vd vd = 0 := isotropic_single_add_single h01 one_ne_zero
  have hve : herm frob ve ve = 0 := isotropic_single_add_single h02 one_ne_zero
  have hvf : herm frob vf vf = 0 := isotropic_single_add_single h01 omega_ne_zero
  have hne : ∀ {j : Fin m} {t : K}, i₀ ≠ j → (Pi.single i₀ 1 + Pi.single j t : Fin m → K) ≠ 0 :=
    fun {j t} hj h => by
      have := congrFun h i₀
      simp [Pi.single_apply, hj.symm] at this
  have hvd0 : vd ≠ 0 := hne h01
  have hve0 : ve ≠ 0 := hne h02
  have hvf0 : vf ≠ 0 := hne h01
  have hde : herm frob vd ve = 1 := by
    rw [herm_single_add_single_left]
    simp [ve, Pi.single_apply, h01.symm, h12, h02]
  have hfd : herm frob vf vd = 1 + frob ω := by
    rw [herm_single_add_single_left]
    simp [vd, Pi.single_apply, h01.symm, h01]
  have hfe : herm frob vf ve = 1 := by
    rw [herm_single_add_single_left]
    simp [ve, Pi.single_apply, h01.symm, h12, h02]
  set u : Fin m → K := tvU vd • ve
  have hu : u = ve + vd := by
    simp only [u]
    rw [tvU_smul hvd, hde, one_smul]
  have huu : herm frob u u = 0 := by
    simp only [u]
    rw [herm_smul_smul, hve]
  have hu0 : u ≠ 0 := by
    simp only [u]
    intro h
    exact hve0 ((smul_eq_zero_iff_eq (tvU vd)).1 h)
  have hfu : herm frob vf u = frob ω := by
    rw [hu, herm_add_right, hfe, hfd, ← add_assoc, add_self_K, zero_add]
  have hfω : frob ω ≠ 0 := frob_ne_zero omega_ne_zero
  have hfd0 : (1 : K) + frob ω ≠ 0 := by
    rw [frob_omega, add_comm ω 1, ← add_assoc, add_self_K, zero_add]
    exact omega_ne_zero
  intro hsymp
  have hd := tqU_mem_DU hvd0 hvd
  have he := tqU_mem_DU hve0 hve
  have hf := tqU_mem_DU hvf0 hvf
  have hncomm : tqU vd * tqU ve ≠ tqU ve * tqU vd := by
    rw [Ne, tqU_commute_iff hm hvd0 hvd hve0 hve, hde]
    exact one_ne_zero
  rcases hsymp _ hd _ he _ hf hncomm with h | h | h
  · rw [tqU_commute_iff hm hvf0 hvf hvd0 hvd, hfd] at h
    exact hfd0 h
  · rw [tqU_commute_iff hm hvf0 hvf hve0 hve, hfe] at h
    exact one_ne_zero h
  · rw [tqU_mul_tqU_mul_tqU hvd hve, tqU_commute_iff hm hvf0 hvf hu0 huu, hfu] at h
    exact hfω h

end CFSG.RankThree.GF2n.Stroth78
