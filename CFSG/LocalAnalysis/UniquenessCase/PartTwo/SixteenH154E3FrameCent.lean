module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3Frame
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3A5TwoKA
public import CFSG.Quasithin.EmptyFaithful.S151bModule

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

private theorem s16h_e3_le_stabSub_commSub_of_cent {W : Type} [CommGroup W]
    {A B : Subgroup (MulAut W)}
    (h : A ≤ Subgroup.centralizer (B : Set (MulAut W))) :
    A ≤ stabSub (commSub (⊤ : Subgroup W) B) := by
  intro a ha
  rw [mem_stabSub]
  intro u
  constructor
  · intro hu
    have h1 : a⁻¹ (a u) ∈ commSub (⊤ : Subgroup W) B :=
      commSub_top_stable151b (X := B) (g := a⁻¹)
        (fun x hx => by
          have hc := Subgroup.mem_centralizer_iff.mp (h (A.inv_mem ha)) x hx
          have h2 : a⁻¹ * x * (a⁻¹)⁻¹ = x := by
            rw [inv_inv, hc.symm, mul_assoc, inv_mul_cancel, mul_one]
          rw [h2]; exact hx)
        (a u) hu
    simpa using h1
  · intro hu
    exact commSub_top_stable151b (X := B) (g := a)
      (fun x hx => by
        have hc := Subgroup.mem_centralizer_iff.mp (h ha) x hx
        have h2 : a * x * a⁻¹ = x := by
          rw [hc.symm, mul_assoc, mul_inv_cancel, mul_one]
        rw [h2]; exact hx)
      u hu

private theorem s16h_e3_stabSub_commSub_self {W : Type} [CommGroup W] [Finite W]
    (L : Subgroup (MulAut W)) : L ≤ stabSub (commSub (⊤ : Subgroup W) L) := by
  intro l hl
  rw [mem_stabSub]
  intro u
  constructor
  · intro hu
    have h1 : l⁻¹ (l u) ∈ commSub (⊤ : Subgroup W) L :=
      commSub_top_stable151b (X := L) (g := l⁻¹)
        (fun x hx => L.mul_mem (L.mul_mem (L.inv_mem hl) hx) (L.inv_mem (L.inv_mem hl)))
        (l u) hu
    simpa using h1
  · intro hu
    exact commSub_top_stable151b (X := L) (g := l)
      (fun x hx => L.mul_mem (L.mul_mem hl hx) (L.inv_mem hl)) u hu

private theorem s16h_e3_range_le_centralizer_range {A B H : Type*} [Group A] [Group B] [Group H]
    (f : A →* H) (g : B →* H) (h : ∀ x y, f x * g y = g y * f x) :
    f.range ≤ Subgroup.centralizer (g.range : Set H) := by
  intro z hz
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  obtain ⟨x, rfl⟩ := hz
  obtain ⟨y, rfl⟩ := hw
  exact (h x y).symm

private theorem s16h_e3_secHom_comp_inclusion {W : Type} [CommGroup W]
    {A B : Subgroup (MulAut W)} {U : Subgroup W} (hAB : A ≤ B)
    (hBU : B ≤ stabSub U) (hBbot : B ≤ stabSub (⊥ : Subgroup W)) :
    (CFSG.Quasithin.B5.secHom B hBU hBbot).comp (Subgroup.inclusion hAB) =
      CFSG.Quasithin.B5.secHom A (hAB.trans hBU) (hAB.trans hBbot) := by
  refine MonoidHom.ext fun a => MulEquiv.ext fun s => ?_
  obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective s
  simp only [MonoidHom.comp_apply, CFSG.Quasithin.B5.secHom_mk]
  congr 1

theorem s16h_e3_frame_cent_hom {W : Type} [CommGroup W] [Finite W]
    {X L L' T : Subgroup (MulAut W)} {U U' : Subgroup W} (F : s16h_E3Frame X L L' T U U')
    {N : Subgroup (MulAut W) → Subgroup W → Subgroup W → Prop} {k : ℕ}
    (hN : ∀ I : Subgroup W, N L I ⊥ → s16h_SimpleScalar L I ⊥)
    (hN' : ∀ I : Subgroup W, N L' I ⊥ → s16h_SimpleScalar L' I ⊥)
    (hS : SumOfNat N L U ⊥ k) (hS' : SumOfNat N L' U' ⊥ k) :
    ∃ π₁ π₂ : ↥(X ⊓ Subgroup.centralizer ((L ⊔ L' : Subgroup (MulAut W)) : Set (MulAut W))) →*
        GL (Fin k) (ZMod 2),
      (∀ x, π₁ x = 1 ↔ ∀ u ∈ U, (x : MulAut W) u = u) ∧
      (∀ x, π₂ x = 1 ↔ ∀ u ∈ U', (x : MulAut W) u = u) := by
  classical
  let K : Subgroup (MulAut W) :=
    X ⊓ Subgroup.centralizer ((L ⊔ L' : Subgroup (MulAut W)) : Set (MulAut W))
  have hKM : K ≤ Subgroup.centralizer ((L ⊔ L' : Subgroup (MulAut W)) : Set (MulAut W)) :=
    inf_le_right
  have hKcentL : K ≤ Subgroup.centralizer (L : Set (MulAut W)) := by
    intro x hx
    exact Subgroup.mem_centralizer_iff.mpr fun y hy =>
      Subgroup.mem_centralizer_iff.mp (hKM hx) y (Subgroup.mem_sup_left hy)
  have hKcentL' : K ≤ Subgroup.centralizer (L' : Set (MulAut W)) := by
    intro x hx
    exact Subgroup.mem_centralizer_iff.mpr fun y hy =>
      Subgroup.mem_centralizer_iff.mp (hKM hx) y (Subgroup.mem_sup_right hy)
  have hLU : L ≤ stabSub U := by rw [F.u_eq]; exact s16h_e3_stabSub_commSub_self L
  have hL'U' : L' ≤ stabSub U' := by rw [F.u'_eq]; exact s16h_e3_stabSub_commSub_self L'
  have hbot : ∀ g : MulAut W, g ∈ stabSub (⊥ : Subgroup W) := by
    intro g
    rw [mem_stabSub]
    intro u
    rw [Subgroup.mem_bot, Subgroup.mem_bot]
    exact MulEquiv.map_eq_one_iff g
  have hKU : K ≤ stabSub U := by
    rw [F.u_eq]
    exact s16h_e3_le_stabSub_commSub_of_cent hKcentL
  have hKU' : K ≤ stabSub U' := by
    rw [F.u'_eq]
    exact s16h_e3_le_stabSub_commSub_of_cent hKcentL'
  have hKbot : K ≤ stabSub (⊥ : Subgroup W) := fun x _ => hbot (x : MulAut W)
  let XU : Subgroup (MulAut W) := K ⊔ L
  have hKXU : K ≤ XU := le_sup_left
  have hLXU : L ≤ XU := le_sup_right
  have hXUU : XU ≤ stabSub U := sup_le hKU hLU
  have hXUbot : XU ≤ stabSub (⊥ : Subgroup W) := sup_le hKbot fun _ _ => hbot _
  let fK : ↥K →* MulAut (Sec U ⊥) :=
    (CFSG.Quasithin.B5.secHom XU hXUU hXUbot).comp (Subgroup.inclusion hKXU)
  let fL : ↥L →* MulAut (Sec U ⊥) :=
    (CFSG.Quasithin.B5.secHom XU hXUU hXUbot).comp (Subgroup.inclusion hLXU)
  have hcomm₁ : ∀ x : ↥K, ∀ l : ↥L, fK x * fL l = fL l * fK x := by
    intro x l
    simp only [fK, fL, MonoidHom.comp_apply]
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hKcentL x.2 (l : MulAut W) l.2).symm
  have hfL₁ : fL.range = autSec L U ⊥ := by
    rw [show fL = CFSG.Quasithin.B5.secHom L (hLXU.trans hXUU) (hLXU.trans hXUbot) from
      s16h_e3_secHom_comp_inclusion hLXU hXUU hXUbot]
    exact CFSG.Quasithin.B5.range_secHom L (hLXU.trans hXUU) (hLXU.trans hXUbot)
  have hF₁ : fK.range ≤ Subgroup.centralizer (autSec L U ⊥ : Set (MulAut (Sec U ⊥))) := by
    rw [← hfL₁]
    exact s16h_e3_range_le_centralizer_range fK fL hcomm₁
  obtain ⟨M₁, hM₁⟩ := s16h_sum_cent_sec_matrix_embed (F := fK.range) F.exp2 hN hS
    (hLXU.trans hXUU) (hLXU.trans hXUbot) hF₁
  let XU' : Subgroup (MulAut W) := K ⊔ L'
  have hKXU' : K ≤ XU' := le_sup_left
  have hL'XU' : L' ≤ XU' := le_sup_right
  have hXU'U' : XU' ≤ stabSub U' := sup_le hKU' hL'U'
  have hXU'bot : XU' ≤ stabSub (⊥ : Subgroup W) := sup_le hKbot fun _ _ => hbot _
  let fK' : ↥K →* MulAut (Sec U' ⊥) :=
    (CFSG.Quasithin.B5.secHom XU' hXU'U' hXU'bot).comp (Subgroup.inclusion hKXU')
  let fL' : ↥L' →* MulAut (Sec U' ⊥) :=
    (CFSG.Quasithin.B5.secHom XU' hXU'U' hXU'bot).comp (Subgroup.inclusion hL'XU')
  have hcomm₂ : ∀ x : ↥K, ∀ l : ↥L', fK' x * fL' l = fL' l * fK' x := by
    intro x l
    simp only [fK', fL', MonoidHom.comp_apply]
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hKcentL' x.2 (l : MulAut W) l.2).symm
  have hfL₂ : fL'.range = autSec L' U' ⊥ := by
    rw [show fL' = CFSG.Quasithin.B5.secHom L' (hL'XU'.trans hXU'U')
        (hL'XU'.trans hXU'bot) from
      s16h_e3_secHom_comp_inclusion hL'XU' hXU'U' hXU'bot]
    exact CFSG.Quasithin.B5.range_secHom L' (hL'XU'.trans hXU'U') (hL'XU'.trans hXU'bot)
  have hF₂ : fK'.range ≤ Subgroup.centralizer (autSec L' U' ⊥ : Set (MulAut (Sec U' ⊥))) := by
    rw [← hfL₂]
    exact s16h_e3_range_le_centralizer_range fK' fL' hcomm₂
  obtain ⟨M₂, hM₂⟩ := s16h_sum_cent_sec_matrix_embed (F := fK'.range) F.exp2 hN' hS'
    (hL'XU'.trans hXU'U') (hL'XU'.trans hXU'bot) hF₂
  have hker₁ : ∀ x : ↥K, fK x = 1 ↔ ∀ u ∈ U, (x : MulAut W) u = u := by
    intro x
    change (CFSG.Quasithin.B5.secHom XU hXUU hXUbot) (Subgroup.inclusion hKXU x) = 1 ↔
      ∀ u ∈ U, (x : MulAut W) u = u
    rw [← MonoidHom.mem_ker, CFSG.Quasithin.B5.mem_ker_secHom XU hXUU hXUbot
      (Subgroup.inclusion hKXU x)]
    rw [CFSG.Quasithin.mem_centSec]
    constructor
    · rintro ⟨-, h⟩ u hu
      have h2 := h u hu
      rwa [Subgroup.mem_bot, mul_inv_eq_one] at h2
    · intro h
      refine ⟨hXUU (Subgroup.inclusion hKXU x).2, fun u hu => ?_⟩
      rw [Subgroup.mem_bot, mul_inv_eq_one]
      exact h u hu
  have hker₂ : ∀ x : ↥K, fK' x = 1 ↔ ∀ u ∈ U', (x : MulAut W) u = u := by
    intro x
    change (CFSG.Quasithin.B5.secHom XU' hXU'U' hXU'bot) (Subgroup.inclusion hKXU' x) = 1 ↔
      ∀ u ∈ U', (x : MulAut W) u = u
    rw [← MonoidHom.mem_ker, CFSG.Quasithin.B5.mem_ker_secHom XU' hXU'U' hXU'bot
      (Subgroup.inclusion hKXU' x)]
    rw [CFSG.Quasithin.mem_centSec]
    constructor
    · rintro ⟨-, h⟩ u hu
      have h2 := h u hu
      rwa [Subgroup.mem_bot, mul_inv_eq_one] at h2
    · intro h
      refine ⟨hXU'U' (Subgroup.inclusion hKXU' x).2, fun u hu => ?_⟩
      rw [Subgroup.mem_bot, mul_inv_eq_one]
      exact h u hu
  have hM₁eq : ∀ a : ↥fK.range, M₁ a = 1 ↔ a = 1 := by
    intro a
    constructor
    · intro ha
      exact hM₁ (ha.trans (map_one M₁).symm)
    · intro ha; rw [ha, map_one]
  have hM₂eq : ∀ a : ↥fK'.range, M₂ a = 1 ↔ a = 1 := by
    intro a
    constructor
    · intro ha
      exact hM₂ (ha.trans (map_one M₂).symm)
    · intro ha; rw [ha, map_one]
  have hfr₁ : ∀ x : ↥K, fK.rangeRestrict x = 1 ↔ fK x = 1 := by
    intro x
    constructor
    · intro h
      simpa [MonoidHom.coe_rangeRestrict] using congrArg (Subtype.val) h
    · intro h
      apply Subtype.ext
      simpa [MonoidHom.coe_rangeRestrict] using h
  have hfr₂ : ∀ x : ↥K, fK'.rangeRestrict x = 1 ↔ fK' x = 1 := by
    intro x
    constructor
    · intro h
      simpa [MonoidHom.coe_rangeRestrict] using congrArg (Subtype.val) h
    · intro h
      apply Subtype.ext
      simpa [MonoidHom.coe_rangeRestrict] using h
  exact ⟨M₁.comp fK.rangeRestrict, M₂.comp fK'.rangeRestrict,
    fun x => by rw [MonoidHom.comp_apply, hM₁eq, hfr₁ x, hker₁ x],
    fun x => by rw [MonoidHom.comp_apply, hM₂eq, hfr₂ x, hker₂ x]⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
