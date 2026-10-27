module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDOrthTorConj
public import CFSG.LocalAnalysis.StandardType.GGQTwoDOrthTorIso
public import CFSG.LocalAnalysis.StandardType.GGQTwoDOrthTorModelU
public import CFSG.LocalAnalysis.StandardType.GGQTwoDOrthTorModelO
public import CFSG.LocalAnalysis.StandardType.GGQTwoDOrthStd

public section

namespace CFSG.StandardType

namespace OrthTorus

open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.StandardType.QTwo
open CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.PhanDn
open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Unitary
open CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary CFSG.LieType.Steinberg
open TauCeti.QuadraticMap Multiplicative

section Factor

private theorem plh_omPlusRefl_chain_ne {p r : ℕ} (hp : p.Prime) (hr : 2 ≤ r)
    {k k' : Fin r} (hk : k.val + 1 = k'.val) (hk1 : k.val + 1 < r) (hk2 : k'.val + 1 < r) :
    omPlusRefl p (omStd r hr k) * omPlusRefl p (omStd r hr k') ≠
      omPlusRefl p (omStd r hr k') * omPlusRefl p (omStd r hr k) := by
  intro hcomm
  have h := (omPlusRefl_commute_iff_supports hp (omStd r hr k) (omStd r hr k')).mp hcomm
  unfold omStd at h
  rw [dif_pos hk1, dif_pos hk2] at h
  rcases h with hpair | hdisj
  · have h1 : k.val = k'.val := by
      have := congrArg (fun z : {ij : Fin r × Fin r // ij.1 < ij.2} => z.1.1.val) hpair
      simpa using this
    omega
  · have hmem1 : k' ∈ ({k, ⟨k.val + 1, hk1⟩} : Finset (Fin r)) := by
      rw [Finset.mem_insert, Finset.mem_singleton]
      exact Or.inr (Fin.ext hk.symm)
    have hmem2 : k' ∈ ({k', ⟨k'.val + 1, hk2⟩} : Finset (Fin r)) := by simp
    exact (Finset.disjoint_left.mp hdisj hmem1) hmem2

variable {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {Bs X : Subgroup G}
  (Φ : OrthFrameCore p Bs X)

private theorem plh_autCongr_torStd_eq_torStdM (hF : Nat.card Φ.F = 2) {a₀ : ℕ}
    {m : ℕ} (hm : 3 ≤ m) (hr : Φ.r = m + 1)
    [inst : Algebra Φ.F (GaloisField 2 2)]
    (E : QuadExt Φ.F (GaloisField 2 2) (unitaryInvolution (GaloisField 2 2) 2 1))
    (χ : Φ.V ≃ₗ[Φ.F] (Fin (m + 1) → GaloisField 2 2))
    (ζ : normOne (unitaryInvolution (GaloisField 2 2) 2 1))
    (hχτ : ∀ (g : Fin Φ.r → Multiplicative (ZMod p)) (v : Φ.V),
      χ (Φ.Δ.τ g v) = diagHom Φ.F (unitaryInvolution (GaloisField 2 2) 2 1) (m + 1)
        (fun i => ζ ^ (toAdd (g (Fin.cast hr.symm i))).val) (χ v)) :
    LinearEquiv.autCongr χ (Φ.Δ.τ (torStd p Φ.r a₀)) = torStdM (F := Φ.F) ζ m a₀ := by
  have hfun : (fun i : Fin (m + 1) =>
      ζ ^ (toAdd ((torStd p Φ.r a₀) (Fin.cast hr.symm i))).val) =
      (fun i : Fin (m + 1) => if i.val < a₀ then 1 else ζ) := by
    funext i
    have hcast : (Fin.cast hr.symm i).val = i.val := by rw [Fin.val_cast]
    have hg : (torStd p Φ.r a₀) (Fin.cast hr.symm i) =
        (if i.val < a₀ then (1 : Multiplicative (ZMod p))
          else Multiplicative.ofAdd (1 : ZMod p)) := by
      unfold torStd
      rw [hcast]
    rw [hg]
    by_cases hi : i.val < a₀
    · rw [if_pos hi, toAdd_one, ZMod.val_zero, pow_zero, if_pos hi]
    · rw [if_neg hi, toAdd_ofAdd,
        ZMod.val_one'' (Fact.out : p.Prime).ne_one, pow_one, if_neg hi]
  calc LinearEquiv.autCongr χ (Φ.Δ.τ (torStd p Φ.r a₀))
      = diagHom Φ.F (unitaryInvolution (GaloisField 2 2) 2 1) (m + 1)
          (fun i => ζ ^ (toAdd ((torStd p Φ.r a₀) (Fin.cast hr.symm i))).val) := by
        apply LinearEquiv.ext
        intro v
        rw [LinearEquiv.autCongr_apply_apply,
          hχτ (torStd p Φ.r a₀) (χ.symm v), χ.apply_symm_apply]
    _ = torStdM (F := Φ.F) ζ m a₀ := by
        rw [hfun]
        rfl

theorem OrthFrameCore.torFactor_P₁_std (hF : Nat.card Φ.F = 2) {a₀ : ℕ} (ha : a₀ ≤ Φ.r) :
    Φ.TorFactor (torP₁ Φ.Q (Φ.Δ.τ (torStd p Φ.r a₀))) := by
  classical
  set m : ℕ := Φ.r - 1 with hm_def
  have hr : Φ.r = m + 1 := by
    rw [hm_def]
    exact (Nat.sub_add_cancel (by have := Φ.hr; omega : 1 ≤ Φ.r)).symm
  have hm : 3 ≤ m := by
    rw [hm_def]
    have := Φ.hr
    omega
  obtain ⟨inst, E, χ, ζ, hζ1, hχQ, hχτ, -, hχ2⟩ := qtwoOrth_std_torus Φ hF m hm hr
  letI := inst
  have hK : Nat.card (GaloisField 2 2) = 4 := by
    rw [GaloisField.card 2 2 (by norm_num)]
    norm_num
  have hC1 : LinearEquiv.autCongr χ (Φ.Δ.τ (torStd p Φ.r a₀)) =
      torStdM (F := Φ.F) ζ m a₀ :=
    plh_autCongr_torStd_eq_torStdM Φ hF hm hr E χ ζ hχτ
  have hmap : (torP₁ Φ.Q (Φ.Δ.τ (torStd p Φ.r a₀))).map
        (LinearEquiv.autCongr χ).toMonoidHom =
      torP₁ (Qn E (m + 1)) (torStdM (F := Φ.F) ζ m a₀) := by
    rw [torP₁_map_autCongr χ (Φ.Δ.τ (torStd p Φ.r a₀)) hχQ, hC1]
  by_cases hb : m + 1 - a₀ ≤ 3
  · left
    have ha' : a₀ ≤ m + 1 := by omega
    let W : Subgroup ((Fin (m + 1) → GaloisField 2 2) ≃ₗ[Φ.F]
        (Fin (m + 1) → GaloisField 2 2)) :=
      (qtwoStdWin (F := Φ.F) (K := GaloisField 2 2) m a₀ (m + 1 - a₀) (by omega)).range
    have hle : torP₁ (Qn E (m + 1)) (torStdM (F := Φ.F) ζ m a₀) ≤ W :=
      torStdM_P₁_le_win E hF hζ1 m a₀ ha'
    obtain ⟨eSU⟩ := qtwoStdWin_range_equiv_statedSU (F := Φ.F) (K := GaloisField 2 2)
      hK m a₀ (m + 1 - a₀) (by omega)
    haveI : Group.IsSolvable W := torSU_isSolvable hK hb eSU
    haveI : Group.IsSolvable ↥(torP₁ (Qn E (m + 1)) (torStdM (F := Φ.F) ζ m a₀)) :=
      Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hle)
        (Subgroup.inclusion_injective hle)
    let e : ↥(torP₁ Φ.Q (Φ.Δ.τ (torStd p Φ.r a₀))) ≃*
        ↥(torP₁ (Qn E (m + 1)) (torStdM (F := Φ.F) ζ m a₀)) :=
      (Subgroup.equivMapOfInjective _ (LinearEquiv.autCongr χ).toMonoidHom
        (LinearEquiv.autCongr χ).injective).trans (MulEquiv.subgroupCongr hmap)
    exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  · right
    have hb4 : 4 ≤ m + 1 - a₀ := by omega
    have ha' : a₀ ≤ m + 1 := by omega
    let A : Subgroup ((Fin (m + 1) → GaloisField 2 2) ≃ₗ[Φ.F]
        (Fin (m + 1) → GaloisField 2 2)) :=
      torP₁ (Qn E (m + 1)) (torStdM (F := Φ.F) ζ m a₀)
    let W : Subgroup ((Fin (m + 1) → GaloisField 2 2) ≃ₗ[Φ.F]
        (Fin (m + 1) → GaloisField 2 2)) :=
      (qtwoStdWin (F := Φ.F) (K := GaloisField 2 2) m a₀ (m + 1 - a₀) (by omega)).range
    have hleW : A ≤ W := torStdM_P₁_le_win E hF hζ1 m a₀ ha'
    have hgeW : W ≤ A := torStdM_win_le_P₁ E hF hζ1 m a₀ ha' hb4
    have hEq : A = W := le_antisymm hleW hgeW
    obtain ⟨eSU⟩ := qtwoStdWin_range_equiv_statedSU (F := Φ.F) (K := GaloisField 2 2)
      hK m a₀ (m + 1 - a₀) (by omega)
    obtain ⟨hqW, lab, hΛ, hlab, hn, htag, htwD⟩ :=
      torSU_isQuasisimple_label hK hb4 eSU
    let e1 : ↥(torP₁ Φ.Q (Φ.Δ.τ (torStd p Φ.r a₀))) ≃* ↥A :=
      (Subgroup.equivMapOfInjective _ (LinearEquiv.autCongr χ).toMonoidHom
        (LinearEquiv.autCongr χ).injective).trans (MulEquiv.subgroupCongr hmap)
    have hqA : CFSG.IsQuasisimple ↥A :=
      CFSG.IsQuasisimple.of_mulEquiv (MulEquiv.subgroupCongr hEq) hqW
    have hlabA : GGHasLabel lab (↥A ⧸ Subgroup.center ↥A) := by
      let eWA : ↥W ≃* ↥A := (MulEquiv.subgroupCongr hEq).symm
      exact ggHasLabel_of_mulEquiv
        (QuotientGroup.congr (Subgroup.center ↥W) (Subgroup.center ↥A) eWA
          (Subgroup.map_center_eq eWA)) hlab
    refine ⟨?_, ⟨⟨lab, hΛ, ?_, hn, htag, htwD⟩, ?_⟩⟩
    · exact CFSG.IsQuasisimple.of_mulEquiv e1 hqA
    · exact ggHasLabel_of_mulEquiv
        (QuotientGroup.congr (Subgroup.center ↥(torP₁ Φ.Q (Φ.Δ.τ (torStd p Φ.r a₀))))
          (Subgroup.center ↥A) e1 (Subgroup.map_center_eq e1)).symm hlabA
    · have hr2 : 2 ≤ Φ.r := by omega
      let kx : Fin Φ.r := ⟨a₀, by omega⟩
      let ky : Fin Φ.r := ⟨a₀ + 1, by omega⟩
      refine ⟨omStd Φ.r hr2 kx, omStd Φ.r hr2 ky, ?_, ?_⟩
      · exact plh_omPlusRefl_chain_ne (Fact.out : p.Prime) hr2 (by simp [kx, ky])
          (by simp only [kx]; omega) (by simp only [ky]; omega)
      · have h3 : ggCoxeterMatrixD (m + 1) (Fin.cast hr kx) (Fin.cast hr ky) = 3 := by
          rw [qtwoLabel_three_iff hm]
          left
          refine ⟨?_, ?_⟩
          · simp only [Fin.val_cast, kx, ky]
          · simp only [Fin.val_cast, ky]
            omega
        have hW3 : (Φ.rank2 (omStd Φ.r hr2 kx) (omStd Φ.r hr2 ky)).map
              (LinearEquiv.autCongr χ).toMonoidHom =
            (qtwoStdWin (F := Φ.F) (K := GaloisField 2 2) m a₀ 3 (by omega)).range := by
          rw [hχ2 kx ky h3, qtwoStdW_chain E m hm a₀ (by omega)
            (Fin.cast hr kx) (Fin.cast hr ky)
            (by simp only [Fin.val_cast, kx]) (by simp only [Fin.val_cast, ky])]
        have hle3 : (qtwoStdWin (F := Φ.F) (K := GaloisField 2 2) m a₀ 3 (by omega)).range ≤ W :=
          qtwoStdWin_range_mono (F := Φ.F) (K := GaloisField 2 2) m a₀ (by omega) (by omega)
        have hleP : (Φ.rank2 (omStd Φ.r hr2 kx) (omStd Φ.r hr2 ky)).map
              (LinearEquiv.autCongr χ).toMonoidHom ≤
            (torP₁ Φ.Q (Φ.Δ.τ (torStd p Φ.r a₀))).map
              (LinearEquiv.autCongr χ).toMonoidHom := by
          rw [hW3, hmap]
          change (qtwoStdWin (F := Φ.F) (K := GaloisField 2 2) m a₀ 3 (by omega)).range ≤ A
          rw [hEq]
          exact hle3
        exact (Subgroup.map_le_map_iff_of_injective
          (LinearEquiv.autCongr χ).injective).mp hleP

theorem OrthFrameCore.torFactor_P₀_std (hF : Nat.card Φ.F = 2) {a₀ : ℕ} (ha : a₀ ≤ Φ.r) :
    Φ.TorFactor (torP₀ Φ.Q (Φ.Δ.τ (torStd p Φ.r a₀))) := by
  classical
  set m : ℕ := Φ.r - 1 with hm_def
  have hr : Φ.r = m + 1 := by
    rw [hm_def]
    exact (Nat.sub_add_cancel (by have := Φ.hr; omega : 1 ≤ Φ.r)).symm
  have hm : 3 ≤ m := by
    rw [hm_def]
    have := Φ.hr
    omega
  obtain ⟨inst, E, χ, ζ, hζ1, hχQ, hχτ, -, hχ2⟩ := qtwoOrth_std_torus Φ hF m hm hr
  letI := inst
  have hK : Nat.card (GaloisField 2 2) = 4 := by
    rw [GaloisField.card 2 2 (by norm_num)]
    norm_num
  have hC1 : LinearEquiv.autCongr χ (Φ.Δ.τ (torStd p Φ.r a₀)) =
      torStdM (F := Φ.F) ζ m a₀ :=
    plh_autCongr_torStd_eq_torStdM Φ hF hm hr E χ ζ hχτ
  have hmap : (torP₀ Φ.Q (Φ.Δ.τ (torStd p Φ.r a₀))).map
        (LinearEquiv.autCongr χ).toMonoidHom =
      torP₀ (Qn E (m + 1)) (torStdM (F := Φ.F) ζ m a₀) := by
    rw [torP₀_map_autCongr χ (Φ.Δ.τ (torStd p Φ.r a₀)) hχQ, hC1]
  by_cases ha2 : a₀ ≤ 2
  · left
    have ha' : a₀ ≤ m + 1 := by omega
    obtain ⟨e0⟩ := torStdM_P₀_equiv E hF hζ1 m a₀ ha'
    haveI : Group.IsSolvable ↥(orthDerived (Qn E a₀)) := torOmega_isSolvable_of_le_two E hF ha2
    haveI : Group.IsSolvable ↥(torP₀ (Qn E (m + 1)) (torStdM (F := Φ.F) ζ m a₀)) :=
      Group.isSolvable_of_isSolvable_injective (f := e0.toMonoidHom) e0.injective
    let e : ↥(torP₀ Φ.Q (Φ.Δ.τ (torStd p Φ.r a₀))) ≃*
        ↥(torP₀ (Qn E (m + 1)) (torStdM (F := Φ.F) ζ m a₀)) :=
      (Subgroup.equivMapOfInjective _ (LinearEquiv.autCongr χ).toMonoidHom
        (LinearEquiv.autCongr χ).injective).trans (MulEquiv.subgroupCongr hmap)
    exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  · have ha3 : 3 ≤ a₀ := by omega
    have ha' : a₀ ≤ m + 1 := by omega
    obtain ⟨e0⟩ := torStdM_P₀_equiv E hF hζ1 m a₀ ha'
    rcases torOmega_factor E hF a₀ with hsolvΩ | ⟨hqΩ, lab, hΛ, hlabΩ, hn, htag, htwD⟩
    · left
      haveI : Group.IsSolvable ↥(orthDerived (Qn E a₀)) := hsolvΩ
      haveI : Group.IsSolvable ↥(torP₀ (Qn E (m + 1)) (torStdM (F := Φ.F) ζ m a₀)) :=
        Group.isSolvable_of_isSolvable_injective (f := e0.toMonoidHom) e0.injective
      let e : ↥(torP₀ Φ.Q (Φ.Δ.τ (torStd p Φ.r a₀))) ≃*
          ↥(torP₀ (Qn E (m + 1)) (torStdM (F := Φ.F) ζ m a₀)) :=
        (Subgroup.equivMapOfInjective _ (LinearEquiv.autCongr χ).toMonoidHom
          (LinearEquiv.autCongr χ).injective).trans (MulEquiv.subgroupCongr hmap)
      exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
    · right
      let A : Subgroup ((Fin (m + 1) → GaloisField 2 2) ≃ₗ[Φ.F]
          (Fin (m + 1) → GaloisField 2 2)) :=
        torP₀ (Qn E (m + 1)) (torStdM (F := Φ.F) ζ m a₀)
      let e1 : ↥(torP₀ Φ.Q (Φ.Δ.τ (torStd p Φ.r a₀))) ≃* ↥A :=
        (Subgroup.equivMapOfInjective _ (LinearEquiv.autCongr χ).toMonoidHom
          (LinearEquiv.autCongr χ).injective).trans (MulEquiv.subgroupCongr hmap)
      have hqA : CFSG.IsQuasisimple ↥A :=
        CFSG.IsQuasisimple.of_mulEquiv e0 hqΩ
      let eOA : ↥(orthDerived (Qn E a₀)) ≃* ↥A := e0.symm
      have hlabA : GGHasLabel lab (↥A ⧸ Subgroup.center ↥A) :=
        ggHasLabel_of_mulEquiv
          (QuotientGroup.congr (Subgroup.center ↥(orthDerived (Qn E a₀)))
            (Subgroup.center ↥A) eOA (Subgroup.map_center_eq eOA)) hlabΩ
      refine ⟨?_, ⟨⟨lab, hΛ, ?_, hn, htag, htwD⟩, ?_⟩⟩
      · exact CFSG.IsQuasisimple.of_mulEquiv e1 hqA
      · exact ggHasLabel_of_mulEquiv
          (QuotientGroup.congr (Subgroup.center ↥(torP₀ Φ.Q (Φ.Δ.τ (torStd p Φ.r a₀))))
            (Subgroup.center ↥A) e1 (Subgroup.map_center_eq e1)).symm hlabA
      · have hr2 : 2 ≤ Φ.r := by omega
        let kx : Fin Φ.r := ⟨0, by omega⟩
        let ky : Fin Φ.r := ⟨1, by omega⟩
        refine ⟨omStd Φ.r hr2 kx, omStd Φ.r hr2 ky, ?_, ?_⟩
        · exact plh_omPlusRefl_chain_ne (Fact.out : p.Prime) hr2 (by simp [kx, ky])
            (by simp only [kx]; omega) (by simp only [ky]; omega)
        · have h3 : ggCoxeterMatrixD (m + 1) (Fin.cast hr kx) (Fin.cast hr ky) = 3 := by
            rw [qtwoLabel_three_iff hm]
            left
            refine ⟨?_, ?_⟩
            · simp only [Fin.val_cast, kx, ky]
            · simp only [Fin.val_cast, ky]
              omega
          have hW3 : (Φ.rank2 (omStd Φ.r hr2 kx) (omStd Φ.r hr2 ky)).map
                (LinearEquiv.autCongr χ).toMonoidHom =
              (qtwoStdWin (F := Φ.F) (K := GaloisField 2 2) m 0 3 (by omega)).range := by
            rw [hχ2 kx ky h3, qtwoStdW_chain E m hm 0 (by omega)
              (Fin.cast hr kx) (Fin.cast hr ky)
              (by simp only [Fin.val_cast, kx]) (by simp only [Fin.val_cast, ky])]
          have hle3 : (qtwoStdWin (F := Φ.F) (K := GaloisField 2 2) m 0 3 (by omega)).range ≤ A :=
            torStdM_win_zero_le_P₀ E hF hζ1 m a₀ ha3 ha'
          have hleP : (Φ.rank2 (omStd Φ.r hr2 kx) (omStd Φ.r hr2 ky)).map
                (LinearEquiv.autCongr χ).toMonoidHom ≤
              (torP₀ Φ.Q (Φ.Δ.τ (torStd p Φ.r a₀))).map
                (LinearEquiv.autCongr χ).toMonoidHom := by
            rw [hW3, hmap]
            exact hle3
          exact (Subgroup.map_le_map_iff_of_injective
            (LinearEquiv.autCongr χ).injective).mp hleP

end Factor

end OrthTorus

end CFSG.StandardType

end
