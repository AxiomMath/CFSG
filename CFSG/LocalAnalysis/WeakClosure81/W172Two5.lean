module

public import CFSG.LocalAnalysis.WeakClosure81.W172Local
public import CFSG.LocalAnalysis.WeakClosure81.W172Single13
public import CFSG.LocalAnalysis.WeakClosure81.W18PackMod

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Quasithin CFSG.Open
  CFSG.QuasithinUnique Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped commutatorElement

private theorem w172_two5_mem_normalizer_iff_cj_eq {W : Type} [AddCommGroup W]
    [Module (ZMod 2) W] {g : LGL 2 W} {A : Subgroup (LGL 2 W)} :
    g ∈ Subgroup.normalizer (A : Set (LGL 2 W)) ↔ cj g A = A :=
  Subgroup.mem_normalizer_iff_map_conj_eq

theorem w172_exists_odd_faithful {Γ : Type} [Group Γ] [Finite Γ] {L : Subgroup Γ}
    (hsolv : Group.IsSolvable ↥L) (hO2 : pCoreOf 2 L = ⊥) :
    ∃ X : Subgroup Γ, X ≤ L ∧ L ≤ Subgroup.normalizer (X : Set Γ) ∧ Odd (Nat.card X) ∧
      ∀ a ∈ L, a ∈ Subgroup.centralizer (X : Set Γ) → a ∈ X := by
  classical
  refine ⟨CFSG.fittingSubgroupOf L, Subgroup.map_subtype_le _, ?_, ?_, ?_⟩
  · exact CFSG.GorensteinWalter.le_normalizer_of_isNormalIn
      (CFSG.GorensteinWalter.fittingSubgroupOf_isNormalIn L)
  · haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    set F : Subgroup ↥L := CFSG.fittingSubgroup ↥L with hF
    have hcard : Nat.card (CFSG.fittingSubgroupOf L) = Nat.card F :=
      Subgroup.card_map_of_injective (K := CFSG.fittingSubgroup ↥L) (f := L.subtype)
        L.subtype_injective
    rw [hcard]
    have hcore : CFSG.pCore 2 ↥L = ⊥ := by
      have h := hO2
      change (CFSG.pCore 2 ↥L).map L.subtype = ⊥ at h
      exact (Subgroup.map_eq_bot_iff_of_injective (CFSG.pCore 2 ↥L) L.subtype_injective).mp h
    by_contra hodd
    have heven : 2 ∣ Nat.card F := even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hodd)
    have hnil : Group.IsNilpotent F := (CFSG.LocalCores.fitting_nilpotent (G := ↥L)).1
    have hFnorm : F.Normal := (CFSG.LocalCores.fitting_nilpotent (G := ↥L)).2.1
    let S : Sylow 2 F := default
    have hSnorm : (S : Subgroup F).Normal := inferInstance
    have hSchar : (S : Subgroup F).Characteristic := Sylow.characteristic_of_normal S hSnorm
    set N : Subgroup ↥L := (S : Subgroup F).map F.subtype with hNdef
    have hNnorm : N.Normal := by
      rw [hNdef, ← Subgroup.normalizer_eq_top_iff, eq_top_iff]
      have hFtop : Subgroup.normalizer (F : Set ↥L) = ⊤ :=
        Subgroup.normalizer_eq_top_iff.mpr hFnorm
      haveI : (S : Subgroup F).Characteristic := hSchar
      calc (⊤ : Subgroup ↥L) = Subgroup.normalizer (F : Set ↥L) := hFtop.symm
        _ ≤ Subgroup.normalizer (((S : Subgroup F).map F.subtype : Subgroup ↥L) :
              Set ↥L) :=
            CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic (S : Subgroup F)
    have hN2 : IsPGroup 2 N := by
      rw [hNdef]
      exact S.isPGroup'.map F.subtype
    have hNcore : N ≤ CFSG.pCore 2 ↥L := CFSG.LieType.BorelTits.le_pCore 2 hNnorm hN2
    have hNbot : N = ⊥ := by
      rw [hcore] at hNcore
      exact le_bot_iff.mp hNcore
    have hSbot : (S : Subgroup F) = ⊥ := by
      rw [hNdef] at hNbot
      exact (Subgroup.map_eq_bot_iff_of_injective (S : Subgroup F) F.subtype_injective).mp hNbot
    have hcardS : Nat.card (S : Subgroup F) = 1 := by rw [hSbot, Subgroup.card_bot]
    have hmult := Sylow.card_eq_multiplicity S
    rw [hcardS] at hmult
    have hpos : 0 < (Nat.card F).factorization 2 :=
      Nat.Prime.factorization_pos_of_dvd Nat.prime_two Nat.card_pos.ne' heven
    have hgt : 1 < 2 ^ (Nat.card F).factorization 2 :=
      Nat.one_lt_pow hpos.ne' (by norm_num)
    omega
  · intro a ha hacent
    exact CFSG.GorensteinWalter.fact_1_2_centralizer_fitting_le_fitting L hsolv ⟨ha, hacent⟩

variable {G : Type} [Group G] [Finite G]

namespace MinCex172

variable {D : Data G} {V₀ V H : Subgroup G}

theorem w172_two5_hyps (h162 : W3Thm162Gt2 G) (c : MinCex172 D V₀ V H) {g : G}
    (hg : Gam183 V H (eOmegaZ H D.T) 1 g) (M : ModDataE H (eOmegaZ H D.T)) :
    commSpace (M.img (vInH V H g)) (commSub (M.img (vInH V H g))) = ⊥ ∧
      (∀ B : Subgroup (LGL 2 M.W), B ≤ M.img (vInH V H g) → mOf (M.img (vInH V H g)) B ≤ 1 →
        commSpace (M.img (vInH V H g)) (fixSub B) ≤ M.sp (conjSubgroup V₀ g)) ∧
      ∀ x ∈ M.img H, M.sp (conjSubgroup V₀ g) ⊓ conjSub x (M.sp (conjSubgroup V₀ g)) ≠ ⊥ →
        x ∈ Subgroup.normalizer ((M.img (vInH V H g) : Subgroup (LGL 2 M.W)) :
          Set (LGL 2 M.W)) := by
  classical
  have hAH : vInH V H g ≤ H := inf_le_right
  have hAab : IsElemAbelian 2 (vInH V H g) :=
    (E3.isElemAbelian_conjSubgroup c.hyp.setting.isElemAbelian g).mono inf_le_left
  refine ⟨?_, ?_, ?_⟩
  · exact M.commSpace_commSub_img_eq_bot hAH (w172_quadratic h162 c hg)
  · intro B hBA hmB
    obtain ⟨B₀, hB₀A, hB₀le, hB₀img⟩ :=
      M.exists_preimage (A := vInH V H g) hAH (B' := B) hBA
    have hB₀H : B₀ ≤ H := hB₀A.trans hAH
    have hmq : E3.mQuot (vInH V H g) B₀ ≤ 1 := by
      have h := M.mOf_img (A := vInH V H g) (B := B₀) hAH hAab hB₀A hB₀le
      rw [← h, hB₀img]
      exact hmB
    have hk : 1 + 1 < mBar D.M V₀ V (c.ctx188 h162).hyp.setting.isElemAbelian := by
      have := (c.ctx188 h162).bound
      omega
    have hcomm := (c.ctx188 h162).comm_le (k := 1) hk hg (B := B₀) hB₀A hmq
    have hcomm' : ⁅Subgroup.centralizer (B₀ : Set G) ⊓ eOmegaZ H D.T, vInH V H g⁆ ≤
        conjSubgroup V₀ g := by
      rw [inf_comm]
      exact hcomm.trans inf_le_right
    have hspace := M.commSpace_img_sp_le (A := vInH V H g)
      (X := Subgroup.centralizer (B₀ : Set G)) (S := conjSubgroup V₀ g) hAH hcomm'
    have hfix : fixSub B = M.sp (Subgroup.centralizer (B₀ : Set G)) := by
      rw [← hB₀img]
      exact M.fixSub_img hB₀H
    rw [hfix]
    exact hspace
  · intro x hx hne
    obtain ⟨y, -, hxy⟩ := M.mem_img.1 hx
    have hsp_ne : M.sp (conjSubgroup V₀ g ⊓
        conjSubgroup (conjSubgroup V₀ g) (y : G)⁻¹) ≠ ⊥ := by
      rw [M.sp_inf]
      have h1 : M.sp (conjSubgroup (conjSubgroup V₀ g) (y : G)⁻¹) =
          conjSub (M.ρ y) (M.sp (conjSubgroup V₀ g)) :=
        (M.conjSub_sp (conjSubgroup V₀ g) y).symm
      rw [h1, hxy]
      exact hne
    have hCne : (conjSubgroup V₀ g ⊓
        conjSubgroup (conjSubgroup V₀ g) (y : G)⁻¹) ⊓ eOmegaZ H D.T ≠ ⊥ :=
      fun hbot => hsp_ne (M.sp_eq_bot_iff.mpr hbot)
    have hne' : (eOmegaZ H D.T ⊓ conjSubgroup V₀ g) ⊓
        conjSubgroup (eOmegaZ H D.T ⊓ conjSubgroup V₀ g) (y : G)⁻¹ ≠ ⊥ := by
      have hEq : (eOmegaZ H D.T ⊓ conjSubgroup V₀ g) ⊓
            conjSubgroup (eOmegaZ H D.T ⊓ conjSubgroup V₀ g) (y : G)⁻¹ =
          (conjSubgroup V₀ g ⊓
            conjSubgroup (conjSubgroup V₀ g) (y : G)⁻¹) ⊓ eOmegaZ H D.T := by
        rw [E3.conjSubgroup_inf, conjSubgroup_eq_iff_mem_normalizer.mpr
          (Hyp183.normalizer_eOmegaZ H D.T (H.inv_mem y.2))]
        ac_rfl
      rw [hEq]
      exact hCne
    have hyinv : (y : G)⁻¹ ∈ conjSubgroup D.M g :=
      w172_mem_conj_of_inf_ne_bot c (H.inv_mem y.2) hne'
    have hyM : (y : G) ∈ conjSubgroup D.M g := by
      simpa using (conjSubgroup D.M g).inv_mem hyinv
    have hMnV : Subgroup.normalizer (conjSubgroup V g : Set G) = conjSubgroup D.M g := by
      rw [← E3.conjSubgroup_normalizer, c.hyp.setting.normalizer_eq]
    have hconjV : conjSubgroup (conjSubgroup V g) (y : G)⁻¹ = conjSubgroup V g := by
      rw [conjSubgroup_eq_iff_mem_normalizer, hMnV]
      exact (conjSubgroup D.M g).inv_mem hyM
    have hconjH : conjSubgroup H (y : G)⁻¹ = H :=
      conjSubgroup_eq_iff_mem_normalizer.mpr (H.le_normalizer (H.inv_mem y.2))
    have hconjA : conjSubgroup (vInH V H g) (y : G)⁻¹ = vInH V H g := by
      unfold vInH
      rw [E3.conjSubgroup_inf, hconjV, hconjH]
    have hcj : cj (M.ρ y) (M.img (vInH V H g)) = M.img (vInH V H g) := by
      rw [M.img_conj (A := vInH V H g) hAH y, hconjA]
    have hnorm : M.ρ y ∈ Subgroup.normalizer
        ((M.img (vInH V H g) : Subgroup (LGL 2 M.W)) : Set (LGL 2 M.W)) :=
      w172_two5_mem_normalizer_iff_cj_eq.mpr hcj
    rw [hxy] at hnorm
    exact hnorm

theorem w172_two5 (h162 : W3Thm162Gt2 G) (c : MinCex172 D V₀ V H) {g : G}
    (hg : Gam183 V H (eOmegaZ H D.T) 1 g) :
    E3.mQuot (vInH V H g) (vInH V H g ⊓ Subgroup.centralizer (eOmegaZ H D.T : Set G)) ≤ 1 := by
  classical
  obtain ⟨M⟩ := exists_modDataE c.hyp.isElemAbelian_eOmegaZ (Hyp183.normalizer_eOmegaZ H D.T)
  have hAH : vInH V H g ≤ H := inf_le_right
  have hAab : IsElemAbelian 2 (vInH V H g) :=
    (E3.isElemAbelian_conjSubgroup c.hyp.setting.isElemAbelian g).mono inf_le_left
  obtain ⟨hquad, hcond, hTI⟩ := w172_two5_hyps h162 c hg M
  haveI : Group.IsSolvable ↥H := c.solv
  have hsolv : Group.IsSolvable ↥(M.img H) := by
    have h : M.img H = M.ρ.range := by
      unfold ModDataE.img
      rw [Subgroup.subgroupOf_self, ← MonoidHom.range_eq_map]
    rw [h]
    exact solvable_of_surjective (MonoidHom.rangeRestrict_surjective M.ρ)
  have hZcent : D.T ≤ Subgroup.centralizer (omegaOneCenterOf D.T : Set G) := by
    intro t ht
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hΩ : omegaOneCenterOf D.T ≤ centerOf D.T := by
      rw [omegaOneCenterOf, omegaOneOf]
      exact (Subgroup.closure_le _).mpr fun u hu => hu.1
    have hz' : z ∈ centerOf D.T := hΩ hz
    exact (Subgroup.mem_centralizer_iff.1 hz'.2 t ht).symm
  have hO2 : pCoreOf 2 (M.img H) = ⊥ :=
    M.pCoreOf_img_eq_bot (J := H) (T := D.T) (Z := omegaOneCenterOf D.T)
      c.hyp.isSylowIn_T (Hyp183.omegaOneCenterOf_le_eOmegaZ H D.T) hZcent (le_refl _)
  obtain ⟨X, hXL, hXn, hXodd, hXc⟩ := w172_exists_odd_faithful hsolv hO2
  have hAL : M.img (vInH V H g) ≤ M.img H := M.img_mono hAH
  have hAab' : IsElemAbelian 2 (M.img (vInH V H g)) := M.isElemAbelian_img hAab
  have hidx := w172_index_centralizer_le_two (A := M.img (vInH V H g)) (X := X)
    (VA := M.sp (conjSubgroup V₀ g)) hAab' hquad hcond
    (fun x hx => hTI x (hXL hx)) hXodd (fun a ha => hXn (hAL ha))
  have hbot : M.img (vInH V H g) ⊓ Subgroup.centralizer (X : Set (LGL 2 M.W)) = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro a ha
    have haX : a ∈ X := hXc a (hAL ha.1) ha.2
    have ha2 : a ^ 2 = 1 := hAab'.2 a ha.1
    have hdvd : orderOf a ∣ Nat.card X := Subgroup.orderOf_dvd_natCard X haX
    have hodd : Odd (orderOf a) := Odd.of_dvd_nat hXodd hdvd
    have hdvd2 : orderOf a ∣ 2 := orderOf_dvd_of_pow_eq_one ha2
    exact orderOf_eq_one_iff.mp (odd_dvd_two hodd hdvd2)
  rw [hbot, Subgroup.bot_subgroupOf, Subgroup.index_bot] at hidx
  have hcard : Nat.card (M.img (vInH V H g)) =
      (Subgroup.centralizer (eOmegaZ H D.T : Set G)).relIndex (vInH V H g) :=
    M.card_img hAH
  have hrel : (vInH V H g ⊓ Subgroup.centralizer (eOmegaZ H D.T : Set G)).relIndex
      (vInH V H g) ≤ 2 := by
    rw [inf_comm, Subgroup.inf_relIndex_right, ← hcard]
    exact hidx
  rw [E3.relIndex_eq_two_pow hAab.isPGroup] at hrel
  by_contra hlt
  have h2 : 2 ^ 2 ≤ 2 ^ E3.mQuot (vInH V H g)
      (vInH V H g ⊓ Subgroup.centralizer (eOmegaZ H D.T : Set G)) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

end MinCex172

end CFSG.LocalAnalysis.WeakClosure81

end
