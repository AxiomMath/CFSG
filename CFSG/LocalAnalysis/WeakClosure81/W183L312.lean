module

public import CFSG.LocalAnalysis.WeakClosure81.W183L31Pair
import CFSG.LocalAnalysis.WeakClosure81.W183L312Aux1
public import CFSG.LocalAnalysis.WeakClosure81.W183L31End

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Quasithin CFSG.Open
  CFSG.QuasithinUnique Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo

variable {G : Type} [Group G] [Finite G]

open scoped commutatorElement

theorem w183l312_sylow_pair {Y : Type} [Group Y] {L S S' : Subgroup Y} (hshape : IsL2 ↥L 2)
    (hS : IsSylowIn 2 S L) (hS' : IsSylowIn 2 S' L) (hne : S ≠ S') :
    Nat.card ↥S = 4 ∧ S ⊓ Subgroup.normalizer (S' : Set Y) = ⊥ ∧
      S' ⊓ Subgroup.normalizer (S : Set Y) = ⊥ ∧ S ⊔ S' = L := by
  classical
  let X := ↥L
  let P : Subgroup X := S.subgroupOf L
  obtain ⟨e⟩ := nonempty_psl_equiv_of_isL2 (r := 2) (by norm_num) hshape
  have hP : CFSG.CGT.Timmesfeld75.IsL2Pair X P (2 ^ 2) := by
    simpa [P] using CFSG.CGT.Timmesfeld75.IsL2Pair.of_psl_sylow
      (f := 2) (by norm_num) ⟨e⟩ hS.toSylow
  have hcardP : Nat.card ↥P = 4 := by
    simpa using hP.card_eq
  have hcard : Nat.card ↥S = 4 := by
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS.le).toEquiv]
    exact hcardP
  exact ⟨hcard, w183l312_ordered_inf hshape hS hS' hne,
    w183l312_ordered_inf hshape hS' hS (Ne.symm hne),
    w183l312_sup_of_sylow hshape hS hS' hne⟩

section Certified


theorem w183l312_NOf_eq_inf_centralizer {n : ℕ} {M V₀ V : Subgroup G} {g : G}
    (h : Hyp64 n M V₀ V g) :
    NOf M V g = V ⊓ Subgroup.centralizer (LOf V g : Set G) := by
  refine le_antisymm ?_ ?_
  · intro u hu
    exact Subgroup.mem_inf.mpr
      ⟨(Subgroup.mem_inf.mp hu).1.1, NOf_le_centralizer_L h hu⟩
  · intro u hu
    obtain ⟨huV, huCent⟩ := Subgroup.mem_inf.mp hu
    have huCentVg : u ∈ Subgroup.centralizer (conjSubgroup V g : Set G) :=
      Subgroup.centralizer_le
        (SetLike.coe_subset_coe.mpr (le_sup_right : conjSubgroup V g ≤ LOf V g)) huCent
    have huNormVg : u ∈ Subgroup.normalizer (conjSubgroup V g : Set G) :=
      Subgroup.centralizer_le_normalizer _ huCentVg
    have hnormEq : Subgroup.normalizer (conjSubgroup V g : Set G) = conjSubgroup M g := by
      rw [← E3.conjSubgroup_normalizer V g, h.normalizer_eq]
    have huMg : u ∈ conjSubgroup M g := by
      rwa [hnormEq] at huNormVg
    have huU : u ∈ UOf M V g := Subgroup.mem_inf.mpr ⟨huV, huMg⟩
    obtain ⟨x, hxVg, hxM⟩ := SetLike.not_le_iff_exists.mp h.inCalOStar.1.1.1
    have hxB : x ∉ BOf M V g := by
      intro hxB
      exact hxM (Subgroup.mem_inf.mp hxB).2
    have hxL : x ∈ LOf V g := Subgroup.mem_sup_right hxVg
    have hcomm : ⁅u, x⁆ = 1 := by
      rw [commutatorElement_eq_one_iff_mul_comm]
      exact (Subgroup.mem_centralizer_iff.mp huCent x hxL).symm
    exact U_centralizesMod_le_N h (genHyp_of_hyp64 h) hxVg hxB u huU
      (by rw [hcomm]; exact one_mem _)

end Certified

namespace Ctx188

variable {D : Data G} {V₀ V H : Subgroup G} {i : ℕ}

theorem w183l312_two_points (x : Ctx188 D V₀ V H i 3) (M : ModDataE H (eOmegaZ H D.T))
    {L : Subgroup G} (hLH : L ≤ H) (hLn : H ≤ Subgroup.normalizer (L : Set G))
    (hshape : IsL2 ↥(M.img L) 2) (hV1 : Gam183 V H (eOmegaZ H D.T) i 1)
    (hVL : IsSylowIn 2 (M.img V) (M.img L)) {h : G} (hhL : h ∈ L) (hhM : h ∉ D.M) :
    Nat.card ↥(M.img V) = 4 ∧
      M.img V ⊓ Subgroup.normalizer
        ((M.img (conjSubgroup V h) : Subgroup (LGL 2 M.W)) : Set (LGL 2 M.W)) = ⊥ ∧
      M.img (conjSubgroup V h) ⊓ Subgroup.normalizer
        ((M.img V : Subgroup (LGL 2 M.W)) : Set (LGL 2 M.W)) = ⊥ ∧
      M.img V ⊔ M.img (conjSubgroup V h) = M.img L := by
  classical
  have hTH : D.T ≤ H := x.hyp.hyp171.2.1
  have hVH : V ≤ H := x.hyp.V_le_T.trans hTH
  have hhH : h ∈ H := hLH hhL
  let j : ↥H := ⟨h⁻¹, H.inv_mem hhH⟩
  have hkey : cj (M.ρ j) (M.img V) = M.img (conjSubgroup V h) := by
    simpa [j] using M.img_conj (A := V) hVH j
  have hgWmem : M.ρ j ∈ M.img L := M.mem_img.mpr ⟨j, L.inv_mem hhL, rfl⟩
  have hgWnormL : M.ρ j ∈
      Subgroup.normalizer (M.img L : Set (LGL 2 M.W)) := Subgroup.le_normalizer hgWmem
  have hcjL : cj (M.ρ j) (M.img L) = M.img L := cj_eq_of_mem_normalizer hgWnormL
  have hcjL' : (M.img L).map (MulAut.conj (M.ρ j)).toMonoidHom = M.img L := by
    simpa [cj] using hcjL
  have hsyl : IsSylowIn 2 (M.img (conjSubgroup V h)) (M.img L) := by
    have hmap := (E1.isSylowIn_map_of_injective (p := 2)
      (f := (MulAut.conj (M.ρ j)).toMonoidHom) (MulAut.conj (M.ρ j)).injective).mpr hVL
    rw [hcjL'] at hmap
    rw [← hkey]
    simpa [cj] using hmap
  have hne : M.img V ≠ M.img (conjSubgroup V h) := by
    intro hEq
    have hcjV : cj (M.ρ j) (M.img V) = M.img V := by
      rw [hkey, ← hEq]
    have hinv : (M.ρ j)⁻¹ ∈
        Subgroup.normalizer (M.img V : Set (LGL 2 M.W)) := by
      rw [Subgroup.mem_normalizer_iff]
      intro a
      have hmem := (mem_cj (g := M.ρ j) (A := M.img V) (x := a))
      rw [hcjV] at hmem
      simpa using hmem
    have hnorm : M.ρ j ∈ Subgroup.normalizer (M.img V : Set (LGL 2 M.W)) := by
      simpa using inv_mem hinv
    have hv1 : vInH V H 1 = V := by
      unfold vInH
      rw [conjSubgroup_one, inf_eq_left.2 hVH]
    have hnorm1 : M.ρ ⟨h⁻¹, H.inv_mem hhH⟩ ∈
        Subgroup.normalizer (M.img (vInH V H 1) : Set (LGL 2 M.W)) := by
      simpa [j, hv1] using hnorm
    have hhm : h⁻¹ ∈ conjSubgroup D.M 1 :=
      x.mem_conj_M_of_img_normalizer M hV1 (H.inv_mem hhH) hnorm1
    have hhmM : h⁻¹ ∈ D.M := by
      rw [conjSubgroup_one] at hhm
      exact hhm
    exact hhM (by simpa using D.M.inv_mem hhmM)
  exact w183l312_sylow_pair hshape hVL hsyl hne

theorem w183l312_exists_h (x : Ctx188 D V₀ V H i 3) {L : Subgroup G} (hLT : L ⊔ D.T = H) :
    ∃ h ∈ L, h ∉ D.M := by
  by_contra hcon
  have hLM : L ≤ D.M := by
    intro l hl
    by_contra hlM
    exact hcon ⟨l, hl, hlM⟩
  have hHM : H ≤ D.M := by
    rw [← hLT]
    exact sup_le hLM D.sylowM.le
  exact x.hyp.notLe hHM

theorem w183l312_conj_le_sup (x : Ctx188 D V₀ V H i 3) (M : ModDataE H (eOmegaZ H D.T))
    {L : Subgroup G} (hLH : L ≤ H) (hV1 : Gam183 V H (eOmegaZ H D.T) i 1) {h : G} (hh : h ∈ H)
    (hsup : M.img V ⊔ M.img (conjSubgroup V h) = M.img L) {l : G} (hl : l ∈ L) :
    conjSubgroup V l ≤ V ⊔ conjSubgroup V h := by
  classical
  have hTH : D.T ≤ H := x.hyp.hyp171.2.1
  have hVH : V ≤ H := x.hyp.V_le_T.trans hTH
  have hVhH : conjSubgroup V h ≤ H := by
    intro y hy
    rw [mem_conjSubgroup_iff] at hy
    have hyH : y = h⁻¹ * (h * y * h⁻¹) * h := by group
    rw [hyH]
    exact H.mul_mem (H.mul_mem (H.inv_mem hh) (hVH hy)) hh
  have himg : M.img (V ⊔ conjSubgroup V h) = M.img L := by
    rw [M.img_sup hVH hVhH, hsup]
  have hlH : l ∈ H := hLH hl
  have hρl : M.ρ ⟨l, hlH⟩ ∈ M.img L := M.mem_img.mpr ⟨⟨l, hlH⟩, hl, rfl⟩
  have hρlLL : M.ρ ⟨l, hlH⟩ ∈ M.img (V ⊔ conjSubgroup V h) := by
    rw [himg]
    exact hρl
  obtain ⟨l₁, hl₁LL, hρl₁⟩ := M.mem_img.mp hρlLL
  let c : G := (l₁ : G)⁻¹ * l
  have hcH : c ∈ H := H.mul_mem (H.inv_mem l₁.2) hlH
  have hρc : M.ρ ⟨c, hcH⟩ = 1 := by
    have hsub : (⟨c, hcH⟩ : ↥H) = (⟨(l₁ : G), l₁.2⟩ : ↥H)⁻¹ * ⟨l, hlH⟩ := by
      apply Subtype.ext
      simp [c]
    rw [hsub, map_mul, map_inv, hρl₁]
    simp
  have hcCent : c ∈ Subgroup.centralizer (eOmegaZ H D.T : Set G) :=
    (M.ρ_eq_one_iff ⟨c, hcH⟩).mp hρc
  have hGam : Gam183 V H (eOmegaZ H D.T) i (l₁ : G) :=
    Ctx188.w183l31_gam183_conj hV1 l₁.2
  have hcM : c ∈ conjSubgroup D.M (l₁ : G) :=
    (x.w183l31_centralizer_le_conj hGam) hcCent
  have hnormEq : conjSubgroup D.M (l₁ : G) =
      Subgroup.normalizer (conjSubgroup V (l₁ : G) : Set G) := by
    rw [← E3.conjSubgroup_normalizer V (l₁ : G), x.hyp.setting.normalizer_eq]
  have hcNorm : c ∈ Subgroup.normalizer (conjSubgroup V (l₁ : G) : Set G) := by
    rwa [hnormEq] at hcM
  have hfix : conjSubgroup (conjSubgroup V (l₁ : G)) c = conjSubgroup V (l₁ : G) :=
    conjSubgroup_eq_iff_mem_normalizer.mpr hcNorm
  have hcl : conjSubgroup V l = conjSubgroup V (l₁ : G) := by
    have hl_eq : l = (l₁ : G) * c := by simp [c]
    rw [hl_eq, ← conjSubgroup_conjSubgroup, hfix]
  rw [hcl]
  intro y hy
  rw [mem_conjSubgroup_iff] at hy
  have hyLL : (l₁ : G) * y * (l₁ : G)⁻¹ ∈ V ⊔ conjSubgroup V h :=
    Subgroup.mem_sup_left hy
  have hy_eq : y = (l₁ : G)⁻¹ * ((l₁ : G) * y * (l₁ : G)⁻¹) * (l₁ : G) := by group
  rw [hy_eq]
  exact (V ⊔ conjSubgroup V h).mul_mem
    ((V ⊔ conjSubgroup V h).mul_mem ((V ⊔ conjSubgroup V h).inv_mem hl₁LL) hyLL) hl₁LL

theorem w183l312_normalizes_sup (x : Ctx188 D V₀ V H i 3) (M : ModDataE H (eOmegaZ H D.T))
    {L : Subgroup G} (hLH : L ≤ H) (hLn : H ≤ Subgroup.normalizer (L : Set G))
    (hV1 : Gam183 V H (eOmegaZ H D.T) i 1) {h : G} (hhL : h ∈ L)
    (hsup : M.img V ⊔ M.img (conjSubgroup V h) = M.img L) :
    D.T ≤ Subgroup.normalizer ((V ⊔ conjSubgroup V h : Subgroup G) : Set G) := by
  classical
  have hTH : D.T ≤ H := x.hyp.hyp171.2.1
  have hhH : h ∈ H := hLH hhL
  intro t ht
  have htH : t ∈ H := hTH ht
  have hmap : ∀ s ∈ D.T, conjSubgroup (V ⊔ conjSubgroup V h) s ≤ V ⊔ conjSubgroup V h := by
    intro s hs
    have hsH : s ∈ H := hTH hs
    have hVnorm : s ∈ Subgroup.normalizer (V : Set G) := by
      rw [x.hyp.setting.normalizer_eq]
      exact D.sylowM.le hs
    have hVs : conjSubgroup V s = V := conjSubgroup_eq_iff_mem_normalizer.mpr hVnorm
    let h' : G := s⁻¹ * h * s
    have hh' : h' ∈ L := by
      have hsn : s⁻¹ ∈ Subgroup.normalizer (L : Set G) := hLn (H.inv_mem hsH)
      have := (Subgroup.mem_normalizer_iff.mp hsn h).mp hhL
      simpa [h'] using this
    have hconj : conjSubgroup (conjSubgroup V h) s = conjSubgroup V h' := by
      calc conjSubgroup (conjSubgroup V h) s = conjSubgroup V (h * s) :=
            conjSubgroup_conjSubgroup V h s
        _ = conjSubgroup V (s * h') := by
            rw [show h * s = s * h' by dsimp [h']; group]
        _ = conjSubgroup (conjSubgroup V s) h' :=
            (conjSubgroup_conjSubgroup V s h').symm
        _ = conjSubgroup V h' := by rw [hVs]
    rw [conjSubgroup_sup, hVs, hconj]
    exact sup_le le_sup_left (x.w183l312_conj_le_sup M hLH hV1 hhH hsup hh')
  have hleft := hmap t ht
  have hright := hmap t⁻¹ (D.T.inv_mem ht)
  have hge : V ⊔ conjSubgroup V h ≤ conjSubgroup (V ⊔ conjSubgroup V h) t := by
    have hmono := E3.conjSubgroup_mono_left t hright
    rwa [E3.conjSubgroup_inv_conj] at hmono
  exact conjSubgroup_eq_iff_mem_normalizer.mp (le_antisymm hleft hge)

section Certified


theorem w183l312_T_normalizes (x : Ctx188 D V₀ V H i 3) (M : ModDataE H (eOmegaZ H D.T))
    {L : Subgroup G} (hLH : L ≤ H) (hLn : H ≤ Subgroup.normalizer (L : Set G))
    (hV1 : Gam183 V H (eOmegaZ H D.T) i 1) {h : G} (hhL : h ∈ L)
    (hyp : Hyp64 2 D.M V₀ V h)
    (hsup : M.img V ⊔ M.img (conjSubgroup V h) = M.img L) :
    D.T ≤ Subgroup.normalizer ((NOf D.M V h : Subgroup G) : Set G) := by
  intro t ht
  have hVnorm : t ∈ Subgroup.normalizer (V : Set G) := by
    rw [x.hyp.setting.normalizer_eq]
    exact D.sylowM.le ht
  have hVt : conjSubgroup V t = V := conjSubgroup_eq_iff_mem_normalizer.mpr hVnorm
  have hLLnorm : t ∈
      Subgroup.normalizer ((V ⊔ conjSubgroup V h : Subgroup G) : Set G) :=
    x.w183l312_normalizes_sup M hLH hLn hV1 hhL hsup ht
  have hLLt : conjSubgroup (V ⊔ conjSubgroup V h) t = V ⊔ conjSubgroup V h :=
    conjSubgroup_eq_iff_mem_normalizer.mpr hLLnorm
  have hN : NOf D.M V h = V ⊓ Subgroup.centralizer (LOf V h : Set G) :=
    w183l312_NOf_eq_inf_centralizer hyp
  have hLOf : LOf V h = V ⊔ conjSubgroup V h := rfl
  rw [← conjSubgroup_eq_iff_mem_normalizer, hN, E3.conjSubgroup_inf,
    E3.conjSubgroup_centralizer, hVt, hLOf, hLLt]

end Certified

end Ctx188

section Certified


theorem false_of_L24_member {D : Data G} {V₀ V H : Subgroup G} {i : ℕ}
    (x : Ctx188 D V₀ V H i 3) (M : ModDataE H (eOmegaZ H D.T)) {L : Subgroup G}
    (hLH : L ≤ H) (hLn : H ≤ Subgroup.normalizer (L : Set G)) (hLT : L ⊔ D.T = H)
    (hshape : IsL2 ↥(M.img L) 2) {g : G} (hg : Gam183 V H (eOmegaZ H D.T) i g)
    (hgT : vInH V H g ≤ D.T)
    (hsyl : IsSylowIn 2 (M.img (vInH V H g)) (M.img L)) : False := by
  have hTH : D.T ≤ H := x.hyp.hyp171.2.1
  have hTp : IsPGroup 2 (M.img D.T) :=
    M.isPGroup_img (isSylowOf_two_iff_isSylowIn.mp D.sylowM).2.1
  have hnormL : ∀ t ∈ M.img D.T, ∀ l ∈ M.img L, t * l * t⁻¹ ∈ M.img L :=
    fun t ht l hl => Ctx188.w183l31_img_normal M hLH hLn t (M.img_mono hTH ht) l hl
  have hAT : M.img (vInH V H g) ≤ M.img D.T := M.img_mono hgT
  have hnorm := w183l31_normalizes_of_sylow hTp hnormL hAT hsyl
  have hgM : g ∈ D.M := x.w183l31_mem_M_of_normal M hg hgT hnorm
  obtain ⟨hvV, hV1⟩ := x.w183l31_member_eq_V hg hgM
  rw [hvV] at hsyl
  obtain ⟨h, hhL, hhM⟩ := x.w183l312_exists_h hLT
  have hhH : h ∈ H := hLH hhL
  obtain ⟨hcard, hK, hK', hsup⟩ := x.w183l312_two_points M hLH hLn hshape hV1 hsyl hhL hhM
  have hyp := x.w183l31_hyp64 M hV1 hhH hcard hK hK'
  obtain ⟨-, hU⟩ := x.w183l31_U_eq M hV1 hhH hcard hK
  have hm : 2 < mBar D.M V₀ V hyp.elemAbelian := by
    have := x.bound
    omega
  have hN := w183l31_N_ne_bot hyp hm hU
  have hTN := x.w183l312_T_normalizes M hLH hLn hV1 hhL hyp hsup
  exact w183l31_false_of_normalizes x.hyp.setting x.hyp.ne_bot hyp hyp.inCalOStar.1.2.1 hN hTN

end Certified

end CFSG.LocalAnalysis.WeakClosure81

end
