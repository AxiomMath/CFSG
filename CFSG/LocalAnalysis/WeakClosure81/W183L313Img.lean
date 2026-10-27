module

public import CFSG.LocalAnalysis.WeakClosure81.W183L31Pair
public import CFSG.LocalAnalysis.WeakClosure81.W183L313Borel
public import CFSG.LocalAnalysis.WeakClosure81.W183L313End
public import CFSG.LocalAnalysis.WeakClosure81.W16Gt2NOneC

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Quasithin CFSG.Open
  CFSG.QuasithinUnique Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.ComponentClassification.AschbacherToolkit.Bender (sylowCenter)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem ModDataE.w183l313_img_conjSubgroup {J E : Subgroup G} (M : ModDataE J E) {A : Subgroup G}
    (hA : A ≤ J) {y : G} (hy : y ∈ J) :
    M.img (conjSubgroup A y) = conjSubgroup (M.img A) (M.ρ ⟨y, hy⟩) := by
  have h := M.img_conj (A := A) hA (⟨y, hy⟩⁻¹ : ↥J)
  rw [map_inv] at h
  simpa [conjSubgroup, cj] using h.symm

namespace Ctx188

variable {D : Data G} {V₀ V H : Subgroup G} {i : ℕ}

theorem w183l313_exists_h (x : Ctx188 D V₀ V H i 3) {L : Subgroup G} (hLT : L ⊔ D.T = H) :
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

theorem w183l313_exists_preimage (x : Ctx188 D V₀ V H i 3) (M : ModDataE H (eOmegaZ H D.T))
    (hV1 : Gam183 V H (eOmegaZ H D.T) i 1) {n : LGL 2 M.W} (hn : n ∈ M.img H)
    (hnZ : n ∈ Subgroup.normalizer ((M.img V : Subgroup (LGL 2 M.W)) : Set (LGL 2 M.W))) :
    ∃ y : G, ∃ hy : y ∈ H, y ∈ D.M ∧ M.ρ ⟨y, hy⟩ = n := by
  obtain ⟨j, -, hjn⟩ := M.mem_img.1 hn
  have hVH : V ≤ H := x.hyp.V_le_T.trans x.hyp.hyp171.2.1
  have hv1 : vInH V H 1 = V := by
    unfold vInH
    rw [conjSubgroup_one, inf_eq_left.2 hVH]
  have hnorm : M.ρ j ∈
      Subgroup.normalizer ((M.img (vInH V H 1) : Subgroup (LGL 2 M.W)) : Set (LGL 2 M.W)) := by
    rw [hv1, hjn]
    exact hnZ
  have hjm : (j : G) ∈ D.M := by
    have h := x.mem_conj_M_of_img_normalizer M hV1 j.2 (g := 1) hnorm
    rwa [conjSubgroup_one] at h
  exact ⟨(j : G), j.2, hjm, hjn⟩

section Certified


theorem w183l313_step0 (x : Ctx188 D V₀ V H i 3) (M : ModDataE H (eOmegaZ H D.T))
    {L : Subgroup G} (hLH : L ≤ H) (hLn : H ≤ Subgroup.normalizer (L : Set G))
    (hshape : IsU3 ↥(M.img L) 2) {g : G} (hg : Gam183 V H (eOmegaZ H D.T) i g)
    (hgT : vInH V H g ≤ D.T) {S : Subgroup (LGL 2 M.W)} (hS : IsSylowIn 2 S (M.img L))
    (hcen : M.img (vInH V H g) = sylowCenter S) :
    g ∈ D.M ∧ S = M.img D.T ⊓ M.img L := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTH : D.T ≤ H := x.hyp.hyp171.2.1
  have hT : IsSylowIn 2 (M.img D.T) (M.img H) := M.isSylowIn_img_of_isSylowIn x.hyp.isSylowIn_T
  have hnorm : ∀ y ∈ M.img H, ∀ l ∈ M.img L, y * l * y⁻¹ ∈ M.img L :=
    Ctx188.w183l31_img_normal M hLH hLn
  have hQn : ((M.img L).subgroupOf (M.img H)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (M.img_mono hLH)).2 (by
      intro y hy
      rw [Subgroup.mem_normalizer_iff]
      intro l
      exact ⟨fun hl => hnorm y hy l hl, fun hl => by
        have h2 := hnorm y⁻¹ ((M.img H).inv_mem hy) (y * l * y⁻¹) hl
        have h3 : y⁻¹ * (y * l * y⁻¹) * y⁻¹⁻¹ = l := by group
        rwa [h3] at h2⟩)
  have hTQ : IsSylowIn 2 (M.img D.T ⊓ M.img L) (M.img L) := hT.inf_normal (M.img_mono hLH) hQn
  have hZT : sylowCenter S ≤ M.img D.T := hcen ▸ M.img_mono hgT
  have hTn : ∀ t ∈ M.img D.T, ∀ q ∈ M.img L, t * q * t⁻¹ ∈ M.img L :=
    fun t ht q hq => hnorm t (M.img_mono hTH ht) q hq
  obtain ⟨hSeq, hnormZ⟩ := w183l313_center_normalized hshape hS hTQ hZT hTn
  refine ⟨?_, hSeq⟩
  refine x.w183l31_mem_M_of_normal M hg hgT ?_
  intro t ht
  have h := hnormZ t ht
  rwa [← hcen] at h

theorem w183l313_two_points (x : Ctx188 D V₀ V H i 3) (M : ModDataE H (eOmegaZ H D.T))
    {L : Subgroup G} (hLH : L ≤ H) (hshape : IsU3 ↥(M.img L) 2)
    (hV1 : Gam183 V H (eOmegaZ H D.T) i 1) {S : Subgroup (LGL 2 M.W)}
    (hS : IsSylowIn 2 S (M.img L)) (hcen : M.img V = sylowCenter S) {h : G} (hhL : h ∈ L)
    (hhM : h ∉ D.M) :
    Nat.card ↥(M.img V) = 4 ∧
      M.img V ⊓ Subgroup.normalizer
        ((M.img (conjSubgroup V h) : Subgroup (LGL 2 M.W)) : Set (LGL 2 M.W)) = ⊥ ∧
      M.img (conjSubgroup V h) ⊓ Subgroup.normalizer
        ((M.img V : Subgroup (LGL 2 M.W)) : Set (LGL 2 M.W)) = ⊥ := by
  classical
  have hTH : D.T ≤ H := x.hyp.hyp171.2.1
  have hVH : V ≤ H := x.hyp.V_le_T.trans hTH
  have hhH : h ∈ H := hLH hhL
  let g₀ : LGL 2 M.W := M.ρ ⟨h, hhH⟩
  have hg₀L : g₀ ∈ M.img L := M.mem_img.mpr ⟨⟨h, hhH⟩, hhL, rfl⟩
  set S' : Subgroup (LGL 2 M.W) := conjSubgroup S g₀ with hS'def
  have hfixL : (M.img L).map (MulAut.conj g₀⁻¹).toMonoidHom = M.img L := by
    have h1 : conjSubgroup (M.img L) g₀ = M.img L :=
      conjSubgroup_eq_iff_mem_normalizer.mpr (Subgroup.le_normalizer hg₀L)
    simpa only [conjSubgroup] using h1
  have hS'syl : IsSylowIn 2 S' (M.img L) := by
    have hmap := (E1.isSylowIn_map_of_injective (p := 2)
      (f := (MulAut.conj g₀⁻¹).toMonoidHom) (MulAut.conj g₀⁻¹).injective).mpr hS
    rw [hfixL] at hmap
    simpa only [S', conjSubgroup] using hmap
  have hne : S ≠ S' := by
    intro heq
    have hconj : conjSubgroup S g₀ = S := by rw [← hS'def, heq]
    have hnormS : g₀ ∈ Subgroup.normalizer (S : Set (LGL 2 M.W)) :=
      conjSubgroup_eq_iff_mem_normalizer.mp hconj
    have hnormZ : g₀ ∈ Subgroup.normalizer
        ((sylowCenter S : Subgroup (LGL 2 M.W)) : Set (LGL 2 M.W)) :=
      w183l313_normalizes_center hnormS
    have hnormV : g₀ ∈ Subgroup.normalizer
        ((M.img V : Subgroup (LGL 2 M.W)) : Set (LGL 2 M.W)) := by
      rwa [← hcen] at hnormZ
    have hv1 : vInH V H 1 = V := by
      unfold vInH
      rw [conjSubgroup_one, inf_eq_left.2 hVH]
    have hnormV' : M.ρ ⟨h, hhH⟩ ∈ Subgroup.normalizer
        ((M.img (vInH V H 1) : Subgroup (LGL 2 M.W)) : Set (LGL 2 M.W)) := by
      rw [hv1]
      exact hnormV
    have hhm : h ∈ conjSubgroup D.M 1 :=
      x.mem_conj_M_of_img_normalizer M hV1 hhH (g := 1) hnormV'
    rw [conjSubgroup_one] at hhm
    exact hhM hhm
  have hconjZ : conjSubgroup (sylowCenter S) g₀ = sylowCenter S' := by
    simp only [hS'def, sylowCenter, E3.conjSubgroup_inf, E3.conjSubgroup_centralizer]
  have himg : conjSubgroup (sylowCenter S) g₀ = M.img (conjSubgroup V h) := by
    rw [← hcen, ModDataE.w183l313_img_conjSubgroup M hVH hhH]
  have hSylS' : sylowCenter S' = M.img (conjSubgroup V h) := hconjZ.symm.trans himg
  obtain ⟨hcard, hbot1, hbot2⟩ := w183l313_center_pair hshape hS hS'syl hne
  refine ⟨?_, ?_, ?_⟩
  · rw [hcen]; exact hcard
  · rw [hcen, ← hSylS']; exact hbot1
  · rw [hcen, ← hSylS']; exact hbot2

end Certified

theorem w183l313_odd_mem (x : Ctx188 D V₀ V H i 3) (M : ModDataE H (eOmegaZ H D.T))
    {k : LGL 2 M.W} (hk : k ∈ M.img (H ⊓ FourteenTwo.PSub D.M V₀ V)) (hodd : Odd (orderOf k)) :
    k ∈ M.img (H ⊓ Subgroup.centralizer (V : Set G)) := by
  classical
  obtain ⟨y, hyPH, hρy⟩ := M.mem_img.1 hk
  have hyP : (y : G) ∈ FourteenTwo.PSub D.M V₀ V := hyPH.2
  obtain ⟨a, m, hmodd, hyn⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos y).ne'
  have hcop : Nat.Coprime (2 ^ a) (orderOf k) := (hodd.coprime_two_right.pow_right a).symm
  haveI : NeZero (orderOf k) := ⟨hodd.pos.ne'⟩
  let u0 : (ZMod (orderOf k))ˣ := ZMod.unitOfCoprime (2 ^ a) hcop
  have hu0 : (u0 : ZMod (orderOf k)) = ((2 ^ a : ℕ) : ZMod (orderOf k)) := rfl
  obtain ⟨u, hu⟩ : ∃ u : ℕ, 2 ^ a * u ≡ 1 [MOD orderOf k] := by
    refine ⟨(↑(u0⁻¹) : ZMod (orderOf k)).val, ?_⟩
    rw [← ZMod.natCast_eq_natCast_iff, Nat.cast_mul, Nat.cast_one, ZMod.natCast_zmod_val,
      ← hu0, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  set z : ↥H := y ^ (2 ^ a * u) with hzdef
  have hρz : M.ρ z = k := by
    have h1 : k ^ (2 ^ a * u) = k ^ 1 := by
      rw [pow_eq_pow_iff_modEq]
      exact hu
    rw [hzdef, map_pow, hρy, h1, pow_one]
  have hzm : z ^ m = 1 := by
    have he : (2 ^ a * u) * m = orderOf y * u := by
      rw [show (2 ^ a * u) * m = u * (2 ^ a * m) by ring, ← hyn, Nat.mul_comm]
    rw [hzdef, ← pow_mul y (2 ^ a * u) m, he, pow_mul, pow_orderOf_eq_one, one_pow]
  have hoddz : Odd (orderOf z) := hmodd.of_dvd_nat (orderOf_dvd_iff_pow_eq_one.mpr hzm)
  have hzP : (z : G) ∈ FourteenTwo.PSub D.M V₀ V := by
    have hyP' : (y : G) ∈ FourteenTwo.PSub D.M V₀ V := hyP
    simpa [hzdef] using (FourteenTwo.PSub D.M V₀ V).pow_mem hyP' (2 ^ a * u)
  have hzP' : (z : G) ∈ F11.CTilde D.M V₀ V ⊓
      (D.M ⊓ Subgroup.centralizer (V₀ : Set G)) := hzP
  have hzCT : (z : G) ∈ F11.CTilde D.M V₀ V := (Subgroup.mem_inf.mp hzP').1
  have hzCent₀ : (z : G) ∈ Subgroup.centralizer (V₀ : Set G) :=
    (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hzP').2).2
  have hzV : ∀ v ∈ V, (z : G) * v * (z : G)⁻¹ * v⁻¹ ∈ V₀ :=
    (FourteenTwo.mem_cTilde_iff_comm.mp hzCT).2.2
  have hzV₀ : ∀ w ∈ V₀, (z : G) * w = w * (z : G) :=
    fun w hw => ((Subgroup.mem_centralizer_iff.mp hzCent₀) w hw).symm
  have hoddG : Odd (orderOf (z : G)) := by
    rw [Subgroup.orderOf_coe]
    exact hoddz
  have hcent : (z : G) ∈ Subgroup.centralizer (V : Set G) :=
    w183l313_mem_centralizer_of_odd x.hyp.setting.pair.elemAbelian x.hyp.setting.pair.le
      hzV hzV₀ hoddG
  exact M.mem_img.2 ⟨z, ⟨z.2, hcent⟩, hρz⟩

end Ctx188

end CFSG.LocalAnalysis.WeakClosure81

end
