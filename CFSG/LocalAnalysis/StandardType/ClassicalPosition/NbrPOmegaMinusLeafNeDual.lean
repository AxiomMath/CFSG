module

public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.NbrPOmegaMinusLeafGen

public section

namespace CFSG.StandardType.ClassicalPosition.NbrLeaf

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.StandardType CFSG.StandardType.S2MathFi1035Pos
  CFSG.StandardType.ClassicalPosition

open scoped commutatorElement

local notation "Ix" n:max => (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)
local notation "Mx" n:max f:max => Matrix (Ix n) (Ix n) (GaloisField 2 f)
set_option quotPrecheck false in
local notation "UK" n:max f:max => (ggU .POmegaMinus n f).K
set_option quotPrecheck false in
local notation "ρm" n:max f:max => Spin.spinMatrix
  (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)
set_option quotPrecheck false in
local notation "Gm" n:max f:max => LinearMap.toMatrix₂' (GaloisField 2 f) (QuadraticMap.polarBilin
  (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2))
local notation "AdS" f:max S:max => Algebra.adjoin (GaloisField 2 f) (Units.val '' S)
local notation "Fadj" n:max f:max e:max => formAdj (RingHom.id (GaloisField 2 f)) (Gm n f) e
local notation "BlkC" n:max f:max S:max ε:max =>
  (glBlockCentralizer (ρm n f) S ε : Subgroup (UK n f))
local notation "rk" f:max e:max =>
  Module.finrank (GaloisField 2 f) (LinearMap.range (Matrix.toLin' e))


theorem nbrpmmx_ne_dual {X : Type} [Group X] (n f : ℕ) (ψ : UK n f →* X)
    (S S' : Set (GL (Ix n) (GaloisField 2 f))) (hSe : S' ⊆ S)
    (hSU : ∀ s ∈ S, s ∈ (ρm n f).range) (hSU' : ∀ s ∈ S', s ∈ (ρm n f).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {K' : Subgroup (UK n f)} {K : Subgroup X} (hK'map : K'.map ψ = K)
    (J : Subgroup X) {J' : Subgroup (UK n f)} (hJ'map : J'.map ψ = J)
    (hJ'comp : IsComponentOf J' ((Subgroup.centralizer S).comap (ρm n f)))
    (hK'comp : IsComponentOf K' ((Subgroup.centralizer S').comap (ρm n f)))
    (hJ'K' : J' ≤ K') (hKne : K ≠ J) {ε e_J e' : Mx n f}
    (hK'ε : IsComponentOf K' ⁅BlkC n f S' ε, BlkC n f S' ε⁆)
    (heJ : IsPrimIdemIn (AdS f S) e_J) (hdegJ : blockDegree (AdS f S) e_J < 2)
    (hdual' : e' ≠ ε ∧ Fadj n f e' ≠ e' ∧ ε = e' + Fadj n f e')
    (he' : IsPrimIdemIn (AdS f S') e') :
    e_J ≠ e' := by
  have hG : IsUnit (Gm n f).det := gram_det n f
  have hSU_iso : ∀ s ∈ S, Matrix.transpose (((s : GL (Ix n) (GaloisField 2 f)) :
      Mx n f).map (RingHom.id (GaloisField 2 f))) * Gm n f *
      ((s : GL (Ix n) (GaloisField 2 f)) : Mx n f) = Gm n f := by
    intro s hs
    exact gram_iso n f (hSU s hs)
  have hSU'_iso : ∀ s ∈ S', Matrix.transpose (((s : GL (Ix n) (GaloisField 2 f)) :
      Mx n f).map (RingHom.id (GaloisField 2 f))) * Gm n f *
      ((s : GL (Ix n) (GaloisField 2 f)) : Mx n f) = Gm n f := by
    intro s hs
    exact gram_iso n f (hSU' s hs)
  intro heq
  have heJ' : IsPrimIdemIn (AdS f S) e' := by rw [← heq]; exact heJ
  have hdegJ' : blockDegree (AdS f S) e' < 2 := by rw [← heq]; exact hdegJ
  have hK'H : K' ≤ (Subgroup.centralizer S).comap (ρm n f) := by
    intro u hu
    have huG : (ρm n f) u ∈ Subgroup.centralizer S' ⊓ glFixing (1 - ε) :=
      Subgroup.mem_comap.mp (le_trans hK'ε.1 (Subgroup.commutator_le_self _) hu)
    obtain ⟨hcent_e, hfix⟩ := huG
    refine Subgroup.mem_comap.mpr (Subgroup.mem_centralizer_iff.mpr ?_)
    intro s hs
    have hse : (s : Mx n f) ∈ AdS f S := Algebra.subset_adjoin ⟨s, hs, rfl⟩
    obtain ⟨c_s, hc_s⟩ := mul_e_eq_smul heJ' hdegJ' _ hse
    have hsE : (s : Mx n f) * e' = e' * (s : Mx n f) :=
      (adjoin_comm (S := S) hS _ hse _ heJ'.1).eq
    have hformAdj_mem_S : Fadj n f e' ∈ AdS f S :=
      Geo.formAdj_mem_adjoin (RingHom.id (GaloisField 2 f)) hG hSU_iso heJ'.1
    have hsF : (s : Mx n f) * Fadj n f e' = Fadj n f e' * (s : Mx n f) :=
      (adjoin_comm (S := S) hS _ hse _ hformAdj_mem_S).eq
    have hε_mem_S : ε ∈ AdS f S := by
      rw [hdual'.2.2]; exact add_mem heJ'.1 hformAdj_mem_S
    have hs_eps : (s : Mx n f) * ε = ε * (s : Mx n f) :=
      (adjoin_comm (S := S) hS _ hse _ hε_mem_S).eq
    have hs1e : (s : Mx n f) * (1 - ε) = (1 - ε) * (s : Mx n f) := by
      rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, Matrix.one_mul, hs_eps]
    have huE : ((ρm n f) u : Mx n f) * e' = e' * ((ρm n f) u : Mx n f) :=
      commute_adjoin (S := S') hcent_e he'.1
    have hformAdj_mem_se : Fadj n f e' ∈ AdS f S' :=
      Geo.formAdj_mem_adjoin (RingHom.id (GaloisField 2 f)) hG hSU'_iso he'.1
    have huF : ((ρm n f) u : Mx n f) * Fadj n f e' =
        Fadj n f e' * ((ρm n f) u : Mx n f) :=
      commute_adjoin (S := S') hcent_e hformAdj_mem_se
    have hisom : Matrix.transpose (((s : GL (Ix n) (GaloisField 2 f)) :
        Mx n f).map (RingHom.id (GaloisField 2 f))) * Gm n f *
        (s : Mx n f) = Gm n f := hSU_iso s hs
    have hss : (((s⁻¹ : GL (Ix n) (GaloisField 2 f)) : Mx n f) * (s : Mx n f)) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have hc_ne : c_s ≠ 0 := by
      intro h0
      have h1 : (s : Mx n f) * e' = 0 := by rw [hc_s, h0, zero_smul]
      have h2 := congrArg (fun M : Mx n f =>
        (((s⁻¹ : GL (Ix n) (GaloisField 2 f)) : Mx n f)) * M) h1
      rw [Matrix.mul_zero, ← Matrix.mul_assoc, hss, Matrix.one_mul] at h2
      exact heJ'.2.2.1 h2
    have h2 : Fadj n f e' = c_s • ((s : Mx n f) * Fadj n f e') := by
      have h := congrArg (fun M : Mx n f => M * (s : Mx n f))
        (show Fadj n f ((s : Mx n f) * e') = Fadj n f (c_s • e') from by rw [hc_s])
      rw [Geo.formAdj_mul (RingHom.id (GaloisField 2 f)) hG,
        Geo.formAdj_eq_inv_of_isometry (RingHom.id (GaloisField 2 f)) hG s hisom,
        Geo.formAdj_smul, Matrix.mul_assoc, hss, Matrix.mul_one, Matrix.smul_mul, ← hsF] at h
      exact h
    have hd_s : (s : Mx n f) * Fadj n f e' = c_s⁻¹ • Fadj n f e' := by
      have h3 := congrArg (fun M : Mx n f => c_s⁻¹ • M) h2
      rw [smul_smul, inv_mul_cancel₀ hc_ne, one_smul] at h3
      exact h3.symm
    have hkill1 : ((((ρm n f) u : Mx n f) * (s : Mx n f) -
        (s : Mx n f) * ((ρm n f) u : Mx n f))) * e' = 0 := by
      rw [Matrix.sub_mul, Matrix.mul_assoc, Matrix.mul_assoc, hc_s, Matrix.mul_smul, huE,
        ← Matrix.mul_assoc, hc_s, Matrix.smul_mul, sub_self]
    have hkill2 : ((((ρm n f) u : Mx n f) * (s : Mx n f) -
        (s : Mx n f) * ((ρm n f) u : Mx n f))) * Fadj n f e' = 0 := by
      rw [Matrix.sub_mul, Matrix.mul_assoc, Matrix.mul_assoc, hd_s, Matrix.mul_smul, huF,
        ← Matrix.mul_assoc, hd_s, Matrix.smul_mul, sub_self]
    have hkill3 : ((((ρm n f) u : Mx n f) * (s : Mx n f) -
        (s : Mx n f) * ((ρm n f) u : Mx n f))) * (1 - ε) = 0 := by
      rw [Matrix.sub_mul, Matrix.mul_assoc, Matrix.mul_assoc, hs1e, ← Matrix.mul_assoc, hfix,
        hs1e, sub_self]
    have hsum : e' + Fadj n f e' + (1 - ε) = 1 := by
      rw [hdual'.2.2]; abel
    have hzero : (((ρm n f) u : Mx n f) * (s : Mx n f) -
        (s : Mx n f) * ((ρm n f) u : Mx n f)) = 0 := by
      calc (((ρm n f) u : Mx n f) * (s : Mx n f) -
          (s : Mx n f) * ((ρm n f) u : Mx n f))
          = _ * 1 := by rw [Matrix.mul_one]
        _ = _ * (e' + Fadj n f e' + (1 - ε)) := by rw [hsum]
        _ = _ * e' + _ * Fadj n f e' + _ * (1 - ε) := by rw [Matrix.mul_add, Matrix.mul_add]
        _ = 0 := by rw [hkill1, hkill2, hkill3]; abel
    apply Units.ext
    rw [Units.val_mul, Units.val_mul]
    exact (sub_eq_zero.mp hzero).symm
  have hSe' : (Subgroup.centralizer S).comap (ρm n f) ≤
      (Subgroup.centralizer S').comap (ρm n f) :=
    Subgroup.comap_mono (Subgroup.centralizer_le hSe)
  haveI : Finite (UK n f) :=
    Finite.of_injective (ρm n f) (nbrpom_spinMatrix_injective n f)
  have hK'compS : IsComponentOf K' ((Subgroup.centralizer S).comap (ρm n f)) :=
    IsComponentOf.of_le_of_le hK'comp hK'H hSe'
  have hJK' : J' = K' :=
    CFSG.LocalAnalysis.ComponentInitial.eq_of_isComponentOf_le hJ'comp hK'compS hJ'K'
  exact hKne (by rw [← hK'map, ← hJ'map, hJK'])

end CFSG.StandardType.ClassicalPosition.NbrLeaf
