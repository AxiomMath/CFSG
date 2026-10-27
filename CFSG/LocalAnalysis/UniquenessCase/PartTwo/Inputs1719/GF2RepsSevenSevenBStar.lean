module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsSevenSevenB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsSevenSevenC
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.DirectProduct

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit
open scoped commutatorElement Pointwise

variable {W : Type} [CommGroup W] [Finite W]

namespace SevenSevenBStar

open SevenSevenB

section Data

variable {Y K A D : Subgroup (MulAut W)} {k : ℕ} [Fintype ↥D] [DecidableEq ↥D]

theorem mem_center_of_diag_mem_center_77 (hK : IsComponentOf K Y) (hDY : D ≤ Y)
    (hDreg : D ⊓ Subgroup.normalizer (K : Set (MulAut W)) = ⊥) {x : ↥K}
    (hx : (⟨diagHom77 hK hDY hDreg x, MonoidHom.mem_range.mpr ⟨x, rfl⟩⟩ :
      ↥(diagHom77 hK hDY hDreg).range) ∈ Subgroup.center ↥(diagHom77 hK hDY hDreg).range) :
    x ∈ Subgroup.center ↥K := by
  classical
  have hKq : CFSG.IsQuasisimple ↥K := (CFSG.Quasithin.A3.isQuasisimple_iff_open).2 hK.2.2
  have hperf : Group.IsPerfect ↥K := hKq.1
  have hker := diagHom_ker_le_center77 hK hDY hDreg
  have hxN : (x : MulAut W) ∈ Subgroup.normalizer (K : Set (MulAut W)) := Subgroup.le_normalizer x.2
  have hcent : ∀ y : ↥K,
      (CFSG.QuasithinUnique.Setup.X5.conjOn K ⟨(x : MulAut W), hxN⟩ y) * y⁻¹ ∈
        Subgroup.center ↥K := by
    intro y
    have hdecomp : CFSG.QuasithinUnique.Setup.X5.conjOn K ⟨(x : MulAut W), hxN⟩ y =
        (⟨(x : MulAut W), x.2⟩ : ↥K) * y * (⟨(x : MulAut W), x.2⟩ : ↥K)⁻¹ := by
      apply Subtype.ext
      rw [CFSG.QuasithinUnique.Setup.X5.coe_conjOn]
      rfl
    have hcomm := Subgroup.mem_center_iff.mp hx
      (⟨(diagHom77 hK hDY hDreg) y, MonoidHom.mem_range.mpr ⟨y, rfl⟩⟩ :
        ↥(diagHom77 hK hDY hDreg).range)
    have hcomm' : (diagHom77 hK hDY hDreg) y *
        (diagHom77 hK hDY hDreg) (⟨(x : MulAut W), x.2⟩ : ↥K) =
        (diagHom77 hK hDY hDreg) (⟨(x : MulAut W), x.2⟩ : ↥K) * (diagHom77 hK hDY hDreg) y := by
      have := congrArg Subtype.val hcomm
      simpa using this
    have hmem : (CFSG.QuasithinUnique.Setup.X5.conjOn K ⟨(x : MulAut W), hxN⟩ y) * y⁻¹ ∈
        (diagHom77 hK hDY hDreg).ker := by
      rw [MonoidHom.mem_ker, hdecomp]
      simp only [map_mul, map_inv]
      rw [← hcomm']
      group
    exact hker hmem
  have hxc : (x : MulAut W) ∈ Subgroup.centralizer (K : Set (MulAut W)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hone : CFSG.QuasithinUnique.Setup.X5.conjOn K ⟨(x : MulAut W), hxN⟩ = 1 :=
      CFSG.GroupTheory.MulAut.eq_one_of_mul_mem_center hperf _ hcent
    have happ : (CFSG.QuasithinUnique.Setup.X5.conjOn K ⟨(x : MulAut W), hxN⟩
        ⟨y, hy⟩ : ↥K) = ⟨y, hy⟩ := by
      rw [hone]
      rfl
    have hval : (x : MulAut W) * y * (x : MulAut W)⁻¹ = y := by
      have := congrArg Subtype.val happ
      rwa [CFSG.QuasithinUnique.Setup.X5.coe_conjOn] at this
    calc (y : MulAut W) * x = ((x : MulAut W) * y * (x : MulAut W)⁻¹) * x := by rw [hval]
      _ = (x : MulAut W) * y := by group
  exact Subgroup.mem_center_iff.mpr fun g => by
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp hxc (g : MulAut W) g.2

theorem ker_actY_le_center_77 (hW : ∀ w : W, w ^ 2 = 1) (hK : IsComponentOf K Y)
    (hA : A ∈ E3.aSet k Y) (hDY : D ≤ Y) (hDA : D ≤ A)
    (hAD : A = normalizerInA A K ⊔ D)
    (hDreg : D ⊓ Subgroup.normalizer (K : Set (MulAut W)) = ⊥) :
    (actOnSub (stableUnder_fixVProduct_diag_77 hK hA hDA hAD hDreg)).ker ≤
      Subgroup.center ↥(diagHom77 hK hDY hDreg).range :=
  SevenSevenC.ker_actOnSub_fixV_le_center hW (diagHom_range_isQuasisimple hK hDY hDreg)
    (isPGroup_centralizerProductD_77 hA hDA)
    (centralizerProductD_le_centralizer_diag_77 hK hA hDY hDA hDreg)
    (diagHom_range_le_normalizer_centralizerProductD_77 hK hA hDY hDA hDreg)

theorem isQuasisimple_actY_range_77 (hW : ∀ w : W, w ^ 2 = 1) (hK : IsComponentOf K Y)
    (hA : A ∈ E3.aSet k Y) (hDY : D ≤ Y) (hDA : D ≤ A)
    (hAD : A = normalizerInA A K ⊔ D)
    (hDreg : D ⊓ Subgroup.normalizer (K : Set (MulAut W)) = ⊥) :
    CFSG.IsQuasisimple
      ↥(actOnSub (stableUnder_fixVProduct_diag_77 hK hA hDA hAD hDreg)).range :=
  SevenSevenC.isQuasisimple_actOnSub_fixV_range hW
    (diagHom_range_isQuasisimple hK hDY hDreg)
    (isPGroup_centralizerProductD_77 hA hDA)
    (centralizerProductD_le_centralizer_diag_77 hK hA hDY hDA hDreg)
    (diagHom_range_le_normalizer_centralizerProductD_77 hK hA hDY hDA hDreg)

theorem actA_range_not_le_centralizer_actY_77 (hW : ∀ w : W, w ^ 2 = 1)
    (hK : IsComponentOf K Y) (hA : A ∈ E3.aSet k Y) (hDY : D ≤ Y) (hDA : D ≤ A)
    (hAD : A = normalizerInA A K ⊔ D)
    (hDreg : D ⊓ Subgroup.normalizer (K : Set (MulAut W)) = ⊥)
    (hNC : ¬ normalizerInA A K ≤ Subgroup.centralizer (K : Set (MulAut W))) :
    ¬ (actOnSub (stableUnder_fixVProduct_77 (K := K) hA hDA)).range ≤
      Subgroup.centralizer
        ((actOnSub (stableUnder_fixVProduct_diag_77 hK hA hDA hAD hDreg)).range :
          Set (MulAut ↥(fixVProduct A K D))) := by
  classical
  intro hle
  obtain ⟨b, hbB, hbC⟩ : ∃ b ∈ normalizerInA A K,
      b ∉ Subgroup.centralizer (K : Set (MulAut W)) := by
    by_contra h
    exact hNC fun x hx => by
      by_contra hxc
      exact h ⟨x, hx, hxc⟩
  have hbA : b ∈ A := hbB.1
  have hbN : b ∈ Subgroup.normalizer (K : Set (MulAut W)) := (Subgroup.mem_inf.mp hbB).2
  have hstab := stableUnder_fixVProduct_diag_77 hK hA hDA hAD hDreg
  have hker := ker_actY_le_center_77 hW hK hA hDY hDA hAD hDreg
  have hcommU : ∀ x : ↥K, ∀ u ∈ fixVProduct A K D,
      b⁻¹ ((diagHom77 hK hDY hDreg) x u) = (diagHom77 hK hDY hDreg) x (b⁻¹ u) := by
    intro x u hu
    have hmem := hle (MonoidHom.mem_range.mpr ⟨⟨b⁻¹, A.inv_mem hbA⟩, rfl⟩)
    have hcomm : (actOnSub (stableUnder_fixVProduct_77 (K := K) hA hDA)) ⟨b⁻¹, A.inv_mem hbA⟩ *
        (actOnSub (stableUnder_fixVProduct_diag_77 hK hA hDA hAD hDreg))
          ⟨diagHom77 hK hDY hDreg x, MonoidHom.mem_range.mpr ⟨x, rfl⟩⟩ =
        (actOnSub (stableUnder_fixVProduct_diag_77 hK hA hDA hAD hDreg))
          ⟨diagHom77 hK hDY hDreg x, MonoidHom.mem_range.mpr ⟨x, rfl⟩⟩ *
        (actOnSub (stableUnder_fixVProduct_77 (K := K) hA hDA)) ⟨b⁻¹, A.inv_mem hbA⟩ :=
      (Subgroup.mem_centralizer_iff.mp hmem
        ((actOnSub (stableUnder_fixVProduct_diag_77 hK hA hDA hAD hDreg))
          ⟨diagHom77 hK hDY hDreg x, MonoidHom.mem_range.mpr ⟨x, rfl⟩⟩)
        (MonoidHom.mem_range.mpr
          ⟨⟨diagHom77 hK hDY hDreg x, MonoidHom.mem_range.mpr ⟨x, rfl⟩⟩, rfl⟩)).symm
    have h2 := congrArg (fun f : MulAut ↥(fixVProduct A K D) => f ⟨u, hu⟩) hcomm
    have h3 := congrArg Subtype.val h2
    simpa [MulAut.mul_apply, actOnSub_apply] using h3
  have hbUfix : ∀ x : ↥K, ∀ u ∈ fixVProduct A K D,
      b ((diagHom77 hK hDY hDreg) x (b⁻¹ (((diagHom77 hK hDY hDreg) x)⁻¹ u))) = u := by
    intro x u hu
    have hv : ((diagHom77 hK hDY hDreg) x)⁻¹ u ∈ fixVProduct A K D :=
      hstab _ ((diagHom77 hK hDY hDreg).range.inv_mem (MonoidHom.mem_range.mpr ⟨x, rfl⟩)) u hu
    have h1 := hcommU x _ hv
    rw [show (diagHom77 hK hDY hDreg) x (((diagHom77 hK hDY hDreg) x)⁻¹ u) = u from by
      rw [← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply]] at h1
    calc b ((diagHom77 hK hDY hDreg) x (b⁻¹ (((diagHom77 hK hDY hDreg) x)⁻¹ u)))
        = b (b⁻¹ u) := by rw [← h1]
      _ = u := by rw [← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply]
  have hbcent : ∀ x : ↥K,
      (CFSG.QuasithinUnique.Setup.X5.conjOn K ⟨b, hbN⟩ x) * x⁻¹ ∈
        Subgroup.center ↥K := by
    intro x
    have hconj := diagHom_conj_mem_normalizer hK hDY hDreg (b := b) hbN
      (fun e he => hA.2.2.1.1 b hbA e (hDA he)) x
    rw [MulAut.conj_apply] at hconj
    obtain ⟨y, hy⟩ : ∃ y : ↥K,
        (y : MulAut W) = b * (x : MulAut W) * b⁻¹ * (x : MulAut W)⁻¹ :=
      ⟨⟨_, K.mul_mem ((Subgroup.mem_normalizer_iff.mp hbN (x : MulAut W)).mp x.2)
        (K.inv_mem x.2)⟩, rfl⟩
    have hyval : y = (CFSG.QuasithinUnique.Setup.X5.conjOn K ⟨b, hbN⟩ x) * x⁻¹ := Subtype.ext hy
    have hδy : (diagHom77 hK hDY hDreg) y =
        b * diagHom77 hK hDY hDreg x * b⁻¹ * (diagHom77 hK hDY hDreg x)⁻¹ := by
      have hdecomp : y = CFSG.QuasithinUnique.Setup.X5.conjOn K ⟨b, hbN⟩ x * x⁻¹ := Subtype.ext hy
      rw [hdecomp, map_mul, map_inv]
      have hconj' : (diagHom77 hK hDY hDreg) (CFSG.QuasithinUnique.Setup.X5.conjOn K ⟨b, hbN⟩ x) =
          b * diagHom77 hK hDY hDreg x * b⁻¹ := hconj.symm
      rw [hconj']
    have hzker : (⟨(diagHom77 hK hDY hDreg) y, MonoidHom.mem_range.mpr ⟨y, rfl⟩⟩ :
        ↥(diagHom77 hK hDY hDreg).range) ∈ (actOnSub hstab).ker := by
      rw [MonoidHom.mem_ker]
      ext u
      simp only [MulAut.one_apply]
      rw [actOnSub_apply]
      change (diagHom77 hK hDY hDreg) y u = u
      rw [hδy]
      simp only [MulAut.mul_apply]
      exact hbUfix x u u.2
    have hcy : y ∈ Subgroup.center ↥K :=
      mem_center_of_diag_mem_center_77 hK hDY hDreg (hker hzker)
    rwa [hyval] at hcy
  have hperf : Group.IsPerfect ↥K :=
    ((CFSG.Quasithin.A3.isQuasisimple_iff_open).2 hK.2.2).1
  have hbK : b ∈ Subgroup.centralizer (K : Set (MulAut W)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hone : CFSG.QuasithinUnique.Setup.X5.conjOn K ⟨b, hbN⟩ = 1 :=
      CFSG.GroupTheory.MulAut.eq_one_of_mul_mem_center hperf _ hbcent
    have happ : (CFSG.QuasithinUnique.Setup.X5.conjOn K ⟨b, hbN⟩ ⟨y, hy⟩ : ↥K) =
        ⟨y, hy⟩ := by
      rw [hone]
      rfl
    have hval : b * y * b⁻¹ = y := by
      have := congrArg Subtype.val happ
      rwa [CFSG.QuasithinUnique.Setup.X5.coe_conjOn] at this
    calc (y : MulAut W) * b = (b * y * b⁻¹) * b := by rw [hval]
      _ = b * y := by group
  exact hbC hbK

theorem actA_range_ne_bot_77 (hW : ∀ w : W, w ^ 2 = 1) (hK : IsComponentOf K Y)
    (hA : A ∈ E3.aSet k Y) (hDY : D ≤ Y) (hDA : D ≤ A)
    (hAD : A = normalizerInA A K ⊔ D)
    (hDreg : D ⊓ Subgroup.normalizer (K : Set (MulAut W)) = ⊥)
    (hNC : ¬ normalizerInA A K ≤ Subgroup.centralizer (K : Set (MulAut W))) :
    (actOnSub (stableUnder_fixVProduct_77 (K := K) hA hDA)).range ≠ ⊥ := by
  intro hbot
  exact actA_range_not_le_centralizer_actY_77 hW hK hA hDY hDA hAD hDreg hNC (by
    rw [hbot]
    exact bot_le)



theorem a_le_normalizer_diag_77 (hK : IsComponentOf K Y) (hA : A ∈ E3.aSet k Y)
    (hDY : D ≤ Y) (hDA : D ≤ A) (hAD : A = normalizerInA A K ⊔ D)
    (hDreg : D ⊓ Subgroup.normalizer (K : Set (MulAut W)) = ⊥) :
    A ≤ Subgroup.normalizer ((diagHom77 hK hDY hDreg).range : Set (MulAut W)) := by
  classical
  have hcommBD : ∀ x ∈ normalizerInA A K, ∀ y ∈ D, Commute x y := by
    intro x hx y hy
    exact hA.2.2.1.1 x hx.1 y (hDA hy)
  have hBnorm : normalizerInA A K ≤
      Subgroup.normalizer ((diagHom77 hK hDY hDreg).range : Set (MulAut W)) := by
    intro b hb
    have hbN : b ∈ Subgroup.normalizer (K : Set (MulAut W)) := (Subgroup.mem_inf.mp hb).2
    have hmem : ∀ x : ↥K,
        b * diagHom77 hK hDY hDreg x * b⁻¹ ∈ (diagHom77 hK hDY hDreg).range := by
      intro x
      have hconj := diagHom_conj_mem_normalizer hK hDY hDreg (b := b) hbN
        (fun e he => hcommBD b hb e he) x
      rw [MulAut.conj_apply] at hconj
      exact ⟨_, hconj.symm⟩
    rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · rintro ⟨x, rfl⟩
      exact hmem x
    · rintro ⟨x, hx⟩
      have hbN' : b⁻¹ ∈ Subgroup.normalizer (K : Set (MulAut W)) :=
        (Subgroup.normalizer (K : Set (MulAut W))).inv_mem hbN
      have hconj := diagHom_conj_mem_normalizer hK hDY hDreg (b := b⁻¹) hbN'
        (fun e he => (hcommBD b hb e he).inv_left) x
      rw [MulAut.conj_apply] at hconj
      refine ⟨⟨b⁻¹ * (x : MulAut W) * b,
        (Subgroup.mem_normalizer_iff.mp hbN' (x : MulAut W)).mp x.2⟩, ?_⟩
      have h1 : z = b⁻¹ * diagHom77 hK hDY hDreg x * b := by
        calc z = b⁻¹ * (b * z * b⁻¹) * b := by group
          _ = b⁻¹ * diagHom77 hK hDY hDreg x * b := by rw [hx]
      rw [h1]
      calc (diagHom77 hK hDY hDreg) ⟨b⁻¹ * (x : MulAut W) * b,
            (Subgroup.mem_normalizer_iff.mp hbN' (x : MulAut W)).mp x.2⟩
          = b⁻¹ * diagHom77 hK hDY hDreg x * (b⁻¹)⁻¹ := hconj.symm
        _ = b⁻¹ * diagHom77 hK hDY hDreg x * b := by group
  have hDnorm : D ≤
      Subgroup.normalizer ((diagHom77 hK hDY hDreg).range : Set (MulAut W)) :=
    fun d hd => Subgroup.centralizer_le_normalizer _
      (D_le_centralizer_diag_77 hK hDY hDreg hd)
  intro a ha
  have ha' : a ∈ normalizerInA A K ⊔ D := hAD ▸ ha
  obtain ⟨b, hbB, d, hdD, hbd⟩ :=
    (CFSG.SignalizerFunctorTheorem.McBride.mem_sup_iff_of_commute hcommBD).mp ha'
  rw [← hbd]
  exact (Subgroup.normalizer _).mul_mem (hBnorm hbB) (hDnorm hdD)

theorem actA_range_le_normalizer_actY_77 (hW : ∀ w : W, w ^ 2 = 1) (hK : IsComponentOf K Y)
    (hA : A ∈ E3.aSet k Y) (hDY : D ≤ Y) (hDA : D ≤ A)
    (hAD : A = normalizerInA A K ⊔ D)
    (hDreg : D ⊓ Subgroup.normalizer (K : Set (MulAut W)) = ⊥) :
    (actOnSub (stableUnder_fixVProduct_77 (K := K) hA hDA)).range ≤
      Subgroup.normalizer
        ((actOnSub (stableUnder_fixVProduct_diag_77 hK hA hDA hAD hDreg)).range :
          Set (MulAut ↥(fixVProduct A K D))) :=
  CFSG.Quasithin.E3.actOnSub_range_le_normalizer
    (stableUnder_fixVProduct_diag_77 hK hA hDA hAD hDreg)
    (stableUnder_fixVProduct_77 (K := K) hA hDA)
    (a_le_normalizer_diag_77 hK hA hDY hDA hAD hDreg)

theorem actA_range_mem_aSet_77 (hW : ∀ w : W, w ^ 2 = 1) (hK : IsComponentOf K Y)
    (hA : A ∈ E3.aSet k Y) (hDY : D ≤ Y) (hDA : D ≤ A)
    (hAD : A = normalizerInA A K ⊔ D)
    (hDreg : D ⊓ Subgroup.normalizer (K : Set (MulAut W)) = ⊥)
    (hNC : ¬ normalizerInA A K ≤ Subgroup.centralizer (K : Set (MulAut W))) :
    (actOnSub (stableUnder_fixVProduct_77 (K := K) hA hDA)).range ∈
      E3.aSet k ((actOnSub (stableUnder_fixVProduct_diag_77 hK hA hDA hAD hDreg)).range ⊔
        (actOnSub (stableUnder_fixVProduct_77 (K := K) hA hDA)).range) :=
  E3.mem_aSet_actOnSub hA (stableUnder_fixVProduct_77 (K := K) hA hDA) le_sup_right
    (actA_range_ne_bot_77 hW hK hA hDY hDA hAD hDreg hNC)

noncomputable def surjDiag_77 (hK : IsComponentOf K Y) (hDY : D ≤ Y)
    (hDreg : D ⊓ Subgroup.normalizer (K : Set (MulAut W)) = ⊥) :
    ↥K →* ↥(diagHom77 hK hDY hDreg).range :=
  (diagHom77 hK hDY hDreg).rangeRestrict

theorem surjDiag_surjective_77 (hK : IsComponentOf K Y) (hDY : D ≤ Y)
    (hDreg : D ⊓ Subgroup.normalizer (K : Set (MulAut W)) = ⊥) :
    Function.Surjective (surjDiag_77 hK hDY hDreg) :=
  MonoidHom.rangeRestrict_surjective _

noncomputable def surjYstar_77 (hK : IsComponentOf K Y) (hA : A ∈ E3.aSet k Y)
    (hDY : D ≤ Y) (hDA : D ≤ A) (hAD : A = normalizerInA A K ⊔ D)
    (hDreg : D ⊓ Subgroup.normalizer (K : Set (MulAut W)) = ⊥) :
    ↥K →* ↥(actOnSub (stableUnder_fixVProduct_diag_77 hK hA hDA hAD hDreg)).range :=
  (MonoidHom.codRestrict (actOnSub (stableUnder_fixVProduct_diag_77 hK hA hDA hAD hDreg))
    _ (fun y => MonoidHom.mem_range.mpr ⟨y, rfl⟩)).comp (surjDiag_77 hK hDY hDreg)

theorem surjYstar_surjective_77 (hK : IsComponentOf K Y) (hA : A ∈ E3.aSet k Y)
    (hDY : D ≤ Y) (hDA : D ≤ A) (hAD : A = normalizerInA A K ⊔ D)
    (hDreg : D ⊓ Subgroup.normalizer (K : Set (MulAut W)) = ⊥) :
    Function.Surjective (surjYstar_77 hK hA hDY hDA hAD hDreg) := by
  intro z
  obtain ⟨y, hy⟩ := MonoidHom.mem_range.mp z.2
  obtain ⟨x, hx⟩ := surjDiag_surjective_77 hK hDY hDreg y
  refine ⟨x, ?_⟩
  apply Subtype.ext
  show (actOnSub (stableUnder_fixVProduct_diag_77 hK hA hDA hAD hDreg))
    (surjDiag_77 hK hDY hDreg x) = ↑z
  rw [hx]
  exact hy



theorem w4Lem7_7_caseB_data {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {Y K A : Subgroup (MulAut W)} {k : ℕ} [Finite ↥K]
    (hK : IsComponentOf K Y) (hA : A ∈ E3.aSet k Y)
    (hNC : ¬ A ⊓ Subgroup.normalizer (K : Set (MulAut W)) ≤
      Subgroup.centralizer (K : Set (MulAut W))) :
    ∃ (U : Type) (_ : CommGroup U) (_ : Finite U), (∀ u : U, u ^ 2 = 1) ∧
      ∃ (Y' : Subgroup (MulAut U)) (hLn : (fstarSubOf Y').Normal),
        IsQuasisimple ↥(fstarSubOf Y') ∧
        (∃ f : ↥K →* ↥(fstarSubOf Y'), Function.Surjective f) ∧ k ≤ E3.aParam Y' := by
  classical
  obtain ⟨D, hDA, hDB, hBD⟩ := exists_compl_normalizerInA_77 (K := K) hA
  haveI : Fintype ↥D := Fintype.ofFinite _
  have hDY : D ≤ Y := le_y_of_le_a_77 hA hDA
  have hAD : A = normalizerInA A K ⊔ D := hBD.symm
  have hDreg : D ⊓ Subgroup.normalizer (K : Set (MulAut W)) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have h1 : x ∈ D ⊓ normalizerInA A K := ⟨hx.1, hDA hx.1, hx.2⟩
    rw [hDB] at h1
    exact h1
  obtain ⟨U₁, i₁, f₁, hU₁, Y₁, hLn, hLq, ⟨f, hf⟩, hk⟩ :=
    SevenSevenC.caseB_data_of_normalizes (U := ↥(fixVProduct A K D))
      (fun u => Subtype.ext (by simpa using hW (u : W)))
      (isQuasisimple_actY_range_77 hW hK hA hDY hDA hAD hDreg)
      (actA_range_le_normalizer_actY_77 hW hK hA hDY hDA hAD hDreg)
      (actA_range_mem_aSet_77 hW hK hA hDY hDA hAD hDreg hNC)
      (actA_range_not_le_centralizer_actY_77 hW hK hA hDY hDA hAD hDreg hNC)
  exact ⟨U₁, i₁, f₁, hU₁, Y₁, hLn, hLq,
    ⟨f.comp (surjYstar_77 hK hA hDY hDA hAD hDreg),
      hf.comp (surjYstar_surjective_77 hK hA hDY hDA hAD hDreg)⟩, hk⟩

end Data

end SevenSevenBStar

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
