module

public import CFSG.LocalAnalysis.WeakClosure81.W183K3Img
import CFSG.CGT.PushingUpLit.BHS7.QuotInv

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Quasithin CFSG.Open
  CFSG.QuasithinUnique Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Ctx188

open W183K3

variable {D : Data G} {V₀ V H : Subgroup G} {i j : ℕ}

theorem br3_oneCore (x : Ctx188 D V₀ V H i j) (M : ModDataE H (eOmegaZ H D.T))
    {Kk F : Subgroup ↥(M.img H)} (hker : KStarData Kk F)
    (hKk : ∀ (j : ↥H) (r : ↥(M.img H)), (r : LGL 2 M.W) = M.ρ j →
      (r ∈ Kk ↔ (j : G) ∈ kerMV V H))
    {L : Subgroup G} (hLc : IsComponentModN (kerMV V H) H L)
    (hLn : H ≤ Subgroup.normalizer (L : Set G)) (hLT : L ⊔ D.T = H)
    (hQ : HasQuotShape L (kerMV V H : Set G)
      (fun X _ => IsSimpleGroup X ∧ ∃ a b : X, a * b ≠ b * a)) :
    ∃ L' : Subgroup (LGL 2 M.W), QuasiCore (M.img H) L' (quasiCentre L') ∧
      quasiCentre L' = Kk.map (M.img H).subtype ∧
      ∀ {P : ∀ (X : Type) [Group X], Prop},
        (∀ (X Y : Type) [Group X] [Group Y], X ≃* Y → P X → P Y) →
          HasQuotShape L (kerMV V H : Set G) P → P (↥L' ⧸ Subgroup.center ↥L') := by
  classical
  have hKL : kerMV V H ≤ L := hLc.2.1
  have hLH : L ≤ H := hLc.2.2.1
  have hDT : D.T ≤ H := x.hyp.hyp171.2.1
  have hρker : ∀ j : ↥H, M.ρ j = 1 → (j : G) ∈ kerMV V H := by
    intro j hj
    rw [M.ρ_eq_one_iff j] at hj
    exact x.hyp.inf_centralizer_eOmegaZ_le_kerMV ⟨j.2, hj⟩
  set A : Subgroup ↥(M.img H) := (M.img L).subgroupOf (M.img H) with hA
  set Z : Subgroup (LGL 2 M.W) := Kk.map (M.img H).subtype with hZ
  have hKk' : ∀ j : ↥H, (M.ρ j : LGL 2 M.W) ∈ Z ↔ (j : G) ∈ kerMV V H := by
    intro j
    have hYj : M.ρ j ∈ M.img H := M.mem_img.mpr ⟨j, j.2, rfl⟩
    rw [hZ]
    constructor
    · intro hmem
      rw [Subgroup.mem_map] at hmem
      obtain ⟨k, hkK, hkz⟩ := hmem
      exact (hKk j k hkz).1 hkK
    · intro hjK
      exact Subgroup.mem_map.mpr ⟨⟨M.ρ j, hYj⟩, (hKk j ⟨M.ρ j, hYj⟩ rfl).2 hjK, rfl⟩
  have hnormLe : M.img H ≤ Subgroup.normalizer
      ((M.img L : Subgroup (LGL 2 M.W)) : Set _) :=
    M.img_le_normalizer (A := H) (S := L) le_rfl hLH hLn
  have hnorm : ∀ y ∈ M.img H, ∀ l ∈ M.img L, y * l * y⁻¹ ∈ M.img L := by
    intro y hy l hl
    exact (Subgroup.mem_normalizer_iff.mp (hnormLe hy) l).1 hl
  have hAn : A.Normal := by
    rw [hA]
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer (M.img_mono hLH)).mpr hnormLe
  have hsup : A ⊔ (M.img D.T).subgroupOf (M.img H) = ⊤ := by
    rw [hA, ← Subgroup.subgroupOf_sup (M.img_mono hLH) (M.img_mono hDT),
      ← M.img_sup hLH hDT, hLT, Subgroup.subgroupOf_self]
  have hT2 : IsPGroup 2 ↥((M.img D.T).subgroupOf (M.img H)) :=
    (M.isPGroup_img x.hyp.isSylowIn_T.isPGroup).of_equiv
      (Subgroup.subgroupOfEquivOfLe (M.img_mono hDT)).symm
  have hFleA : F ≤ A := by
    have hle := CFSG.CGT.PushingUpLit.BHS7.opResidual_le_of_le_sup (Γ := ↥(M.img H))
      (G := ⊤) (N := A) (T := (M.img D.T).subgroupOf (M.img H)) hT2
      (by rw [Subgroup.normalizer_eq_top_iff.mpr hAn]; exact le_top)
      (by rw [sup_comm]; exact le_of_eq hsup.symm)
    rwa [hker.eq_F] at hle
  have hKkF : Kk ≤ F := hker.eq_F ▸ hker.le
  let ψ : ↥L →* LGL 2 M.W := M.ρ.comp (Subgroup.inclusion hLH)
  have hψ : ∀ k : ↥L, ψ k = M.ρ (Subgroup.inclusion hLH k) := fun _ => rfl
  let ψ' : ↥L →* ↥(M.img L) := ψ.codRestrict (M.img L) fun k => by
    rw [hψ k]
    exact M.mem_img.2 ⟨Subgroup.inclusion hLH k, k.2, rfl⟩
  have hψ'coe : ∀ k : ↥L, (ψ' k : LGL 2 M.W) = ψ k := fun _ => rfl
  have hψ's : Function.Surjective ψ' := by
    intro y
    obtain ⟨j, hj, hjρ⟩ := M.mem_img.1 y.2
    refine ⟨⟨(j : G), hj⟩, Subtype.ext ?_⟩
    show (ψ' ⟨(j : G), hj⟩ : LGL 2 M.W) = (y : LGL 2 M.W)
    rw [hψ'coe, hψ]
    have hinc : Subgroup.inclusion hLH ⟨(j : G), hj⟩ = j := Subtype.ext rfl
    rw [hinc, hjρ]
  have hbuild : ∀ {X : Type} [Group X] (φ : ↥L →* X), Function.Surjective φ →
      (∀ k : ↥L, φ k = 1 ↔ (k : G) ∈ kerMV V H) →
      ∃ θ : ↥(M.img L) →* X, Function.Surjective θ ∧
        ∀ r : ↥(M.img L), θ r = 1 ↔ (r : LGL 2 M.W) ∈ Z := by
    intro X hXgrp φ hφs hφk
    letI : Group X := hXgrp
    have hle : ψ'.ker ≤ φ.ker := by
      intro k hk
      rw [MonoidHom.mem_ker] at hk ⊢
      have h2 : M.ρ (Subgroup.inclusion hLH k) = 1 := by
        rw [← hψ k, ← hψ'coe k, congrArg Subtype.val hk]
        rfl
      exact (hφk k).2 (by simpa using hρker (Subgroup.inclusion hLH k) h2)
    let θ : ↥(M.img L) →* X := MonoidHom.liftOfSurjective ψ' hψ's ⟨φ, hle⟩
    have hθ : ∀ l : ↥L, θ (ψ' l) = φ l := fun l =>
      MonoidHom.liftOfRightInverse_comp_apply ψ' _ _ ⟨φ, hle⟩ l
    have hθs : Function.Surjective θ := by
      intro y
      obtain ⟨l, hl⟩ := hφs y
      exact ⟨ψ' l, by rw [hθ l, hl]⟩
    refine ⟨θ, hθs, ?_⟩
    intro r
    obtain ⟨l, hl⟩ := hψ's r
    have hθl : θ r = φ l := by rw [← hl, hθ l]
    rw [hθl, hφk l, ← hl]
    have hρj : (ψ' l : LGL 2 M.W) = M.ρ (Subgroup.inclusion hLH l) := by
      rw [hψ'coe l, hψ l]
    rw [hρj]
    exact (hKk' (Subgroup.inclusion hLH l)).symm
  obtain ⟨X, hX, φ, hφs, hφk, hXsimple⟩ := hQ
  letI : Group X := hX
  obtain ⟨θ, hθs, hθker⟩ := hbuild φ hφs hφk
  let eA := Subgroup.subgroupOfEquivOfLe (M.img_mono hLH)
  set FL : Subgroup ↥(M.img L) := (F.subgroupOf A).map eA.toMonoidHom with hFL
  have hFLnorm : FL.Normal := by
    rw [hFL]
    exact (hker.soc.normal_right.subgroupOf A).map eA.toMonoidHom eA.surjective
  have hcase : FL.map θ = ⊥ ∨ FL.map θ = ⊤ := by
    haveI : IsSimpleGroup X := hXsimple.1
    haveI : (FL.map θ).Normal := hFLnorm.map θ hθs
    exact IsSimpleGroup.eq_bot_or_eq_top_of_normal (FL.map θ)
  have hFA : F = A := by
    rcases hcase with hbot | htop
    · exfalso
      apply hker.soc.not_le
      intro x hxF
      have hxA : x ∈ A := hFleA hxF
      have hxLFL : eA ⟨x, hxA⟩ ∈ FL := by
        rw [hFL]
        exact Subgroup.mem_map.mpr ⟨⟨x, hxA⟩, Subgroup.mem_subgroupOf.mpr hxF, rfl⟩
      have hxLbot : θ (eA ⟨x, hxA⟩) ∈ FL.map θ :=
        Subgroup.mem_map.mpr ⟨eA ⟨x, hxA⟩, hxLFL, rfl⟩
      rw [hbot] at hxLbot
      have h1 : θ (eA ⟨x, hxA⟩) = 1 := Subgroup.mem_bot.mp hxLbot
      have hmemZ : (eA ⟨x, hxA⟩ : LGL 2 M.W) ∈ Z := (hθker _).1 h1
      rw [show (eA ⟨x, hxA⟩ : LGL 2 M.W) = (x : LGL 2 M.W) from rfl] at hmemZ
      rw [hZ, Subgroup.mem_map] at hmemZ
      obtain ⟨k, hkK, hkz⟩ := hmemZ
      have hkx : k = x := Subtype.ext hkz
      rwa [hkx] at hkK
    · refine le_antisymm hFleA ?_
      have hkerleFL : θ.ker ≤ FL := by
        intro r hr
        rw [MonoidHom.mem_ker] at hr
        have hmemZ : (r : LGL 2 M.W) ∈ Z := (hθker r).1 hr
        rw [hZ, Subgroup.mem_map] at hmemZ
        obtain ⟨k, hkK, hkz⟩ := hmemZ
        have hkF : k ∈ F := hKkF hkK
        refine Subgroup.mem_map.mpr ⟨eA.symm r, ?_, eA.apply_symm_apply r⟩
        rw [Subgroup.mem_subgroupOf]
        have hsymm : ((eA.symm r : ↥A) : ↥(M.img H)) = k :=
          Subtype.ext ((show (eA.symm r : LGL 2 M.W) = (r : LGL 2 M.W) from rfl).trans
            hkz.symm)
        rw [hsymm]
        exact hkF
      have hsupker : FL ⊔ θ.ker = ⊤ := by
        rw [eq_top_iff]
        intro x _
        have hx : θ x ∈ FL.map θ := by rw [htop]; exact Subgroup.mem_top _
        obtain ⟨f, hfFL, hfeq⟩ := Subgroup.mem_map.mp hx
        have hxfinv : x * f⁻¹ ∈ θ.ker := by
          rw [MonoidHom.mem_ker, map_mul, map_inv, hfeq]
          group
        have hxeq : x = (x * f⁻¹) * f := by group
        rw [hxeq]
        exact (FL ⊔ θ.ker).mul_mem
          (Subgroup.mem_sup_right (S := FL) (T := θ.ker) hxfinv)
          (Subgroup.mem_sup_left (S := FL) (T := θ.ker) hfFL)
      have hFLtop : FL = ⊤ := by
        rw [← hsupker]
        exact (sup_eq_left.mpr hkerleFL).symm
      intro a ha
      have hmemA : eA ⟨a, ha⟩ ∈ FL := by rw [hFLtop]; exact Subgroup.mem_top _
      rw [hFL] at hmemA
      obtain ⟨b, hb, hbeq⟩ := Subgroup.mem_map.mp hmemA
      have hba : b = ⟨a, ha⟩ := eA.injective hbeq
      rw [hba] at hb
      simpa using Subgroup.mem_subgroupOf.mp hb
  have hL'eq : M.img L = F.map (M.img H).subtype := by
    rw [hFA, hA]
    exact (Subgroup.map_subgroupOf_eq_of_le (M.img_mono hLH)).symm
  have hZle : Z ≤ M.img L := by
    rw [hZ, hL'eq]
    exact Subgroup.map_mono hKkF
  have hZc : ∀ z ∈ Z, ∀ f ∈ M.img L, z * f = f * z := by
    intro z hz f hf
    rw [hZ, Subgroup.mem_map] at hz
    obtain ⟨k, hkK, hkz⟩ := hz
    rw [hL'eq, Subgroup.mem_map] at hf
    obtain ⟨g, hgF, hgf⟩ := hf
    have hcomm : k * g = g * k := by
      have hcent : k ∈ Subgroup.centralizer (F : Set ↥(M.img H)) := by
        have hmemc : k ∈ Subgroup.centralizer
            (opResidual 2 (⊤ : Subgroup ↥(M.img H)) : Set ↥(M.img H)) := by
          rw [← hker.cent]
          exact hkK
        rwa [hker.eq_F] at hmemc
      exact (Subgroup.mem_centralizer_iff.mp hcent g hgF).symm
    have hcomm' : (M.img H).subtype k * (M.img H).subtype g =
        (M.img H).subtype g * (M.img H).subtype k := by
      rw [← map_mul, ← map_mul, hcomm]
    rw [hkz, hgf] at hcomm'
    exact hcomm'
  have hFF : ⁅F, F⁆ = F := by
    rw [← hker.eq_F]
    exact hker.perfect
  have hperfect : ⁅M.img L, M.img L⁆ = M.img L := by
    rw [hL'eq, ← Subgroup.map_commutator, hFF]
  have hnormalZ : (Z.subgroupOf (M.img L)).Normal :=
    Subgroup.normal_of_le_center fun z hz => by
      rw [Subgroup.mem_center_iff]
      intro w
      exact Subtype.ext (hZc (z : LGL 2 M.W) hz (w : LGL 2 M.W) w.2).symm
  have hkerθ : θ.ker = Z.subgroupOf (M.img L) := by
    ext r
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact hθker r
  have hsimple : IsSimpleGroup (↥(M.img L) ⧸ Z.subgroupOf (M.img L)) := by
    haveI : (Z.subgroupOf (M.img L)).Normal := hnormalZ
    let e : (↥(M.img L) ⧸ Z.subgroupOf (M.img L)) ≃* X :=
      (QuotientGroup.quotientMulEquivOfEq hkerθ.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective θ hθs)
    exact (MulEquiv.isSimpleGroup_congr e).mpr hXsimple.1
  haveI : (Z.subgroupOf (M.img L)).Normal := hnormalZ
  have hquasi : CFSG.Open.IsQuasisimple ↥(M.img L) ∧ quasiCentre (M.img L) = Z :=
    isQuasisimple_of_central_simple_quot (F := M.img L) (Z := Z)
      hperfect hZle hZc hsimple
  refine ⟨M.img L, ?_, ?_, ?_⟩
  · refine ⟨M.img_mono hLH, hnorm, hquasi.1, ?_, ?_⟩
    · rw [hquasi.2, hZ, ← Nat.card_congr
        (Subgroup.equivMapOfInjective Kk (M.img H).subtype
          (M.img H).subtype_injective).toEquiv]
      exact hker.odd
    · intro y hy hcomm
      have hyK : (⟨y, hy⟩ : ↥(M.img H)) ∈ Kk := by
        rw [hker.cent, Subgroup.mem_centralizer_iff]
        intro f hf
        apply Subtype.ext
        have hfF : f ∈ F := by rwa [hker.eq_F] at hf
        have hfL : (f : LGL 2 M.W) ∈ M.img L := by
          rw [hL'eq]
          exact Subgroup.mem_map.mpr ⟨f, hfF, rfl⟩
        exact (hcomm (f : LGL 2 M.W) hfL).symm
      rw [hquasi.2, hZ]
      exact Subgroup.mem_map.mpr ⟨⟨y, hy⟩, hyK, rfl⟩
  · exact hquasi.2.trans hZ
  · intro P hP hQ'
    obtain ⟨X', hX', φ', hφ's, hφ'k, hPX'⟩ := hQ'
    letI : Group X' := hX'
    obtain ⟨θ', hθ's, hθ'ker⟩ := hbuild φ' hφ's hφ'k
    have hkerθ' : θ'.ker = Z.subgroupOf (M.img L) := by
      ext r
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      exact hθ'ker r
    have hcenter : Z.subgroupOf (M.img L) = Subgroup.center ↥(M.img L) := by
      apply Subgroup.map_subtype_inj.mp
      rw [Subgroup.map_subgroupOf_eq_of_le hZle]
      show Z = quasiCentre (M.img L)
      exact hquasi.2.symm
    haveI : (Z.subgroupOf (M.img L)).Normal := hnormalZ
    let e : (↥(M.img L) ⧸ Subgroup.center ↥(M.img L)) ≃* X' :=
      (QuotientGroup.quotientMulEquivOfEq hcenter.symm).trans
        ((QuotientGroup.quotientMulEquivOfEq hkerθ'.symm).trans
          (QuotientGroup.quotientKerEquivOfSurjective θ' hθ's))
    exact hP X' (↥(M.img L) ⧸ Subgroup.center ↥(M.img L)) e.symm hPX'

end Ctx188

end CFSG.LocalAnalysis.WeakClosure81

end
