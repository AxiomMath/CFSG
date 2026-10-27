module

public import CFSG.Quasithin.Background.F918Z8d
import CFSG.Quasithin.Background.B4L3Fin
import CFSG.Quasithin.EmptyFaithful.S146F3
public import CFSG.LinearAlgebra.LinearGroups.Perfect

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.QuasithinUnique.Bridge
open scoped commutatorElement

theorem d321g_perfect_le {G : Type*} [Group G] {L C : Subgroup G} (hperf : ⁅L, L⁆ = L) {c : G}
    (hc : ∀ l ∈ L, c * l = l * c) {s : Set G} (hs : Subgroup.closure s = L)
    (hsC : ∀ x ∈ s, x * c ∈ C) : L ≤ C := by
  have hcom : ∀ l ∈ L, ∀ k : ℤ, c ^ k * l = l * c ^ k := fun l hl k =>
    (Commute.zpow_left (show Commute c l from hc l hl) k).eq
  have hall : ∀ l ∈ L, ∃ k : ℤ, l * c ^ k ∈ C := by
    intro l hl
    rw [← hs] at hl
    induction hl using Subgroup.closure_induction with
    | mem x hx => exact ⟨1, by simpa using hsC x hx⟩
    | one => exact ⟨0, by simp⟩
    | mul x y hx hy ihx ihy =>
      obtain ⟨k₁, hk₁⟩ := ihx
      obtain ⟨k₂, hk₂⟩ := ihy
      refine ⟨k₁ + k₂, ?_⟩
      have hy' : y ∈ L := hs ▸ hy
      have h := hcom y hy' k₁
      have e : x * y * c ^ (k₁ + k₂) = (x * c ^ k₁) * (y * c ^ k₂) := by
        calc x * y * c ^ (k₁ + k₂) = x * (y * c ^ k₁) * c ^ k₂ := by
              rw [zpow_add]; simp only [mul_assoc]
          _ = x * (c ^ k₁ * y) * c ^ k₂ := by rw [h]
          _ = (x * c ^ k₁) * (y * c ^ k₂) := by simp only [mul_assoc]
      rw [e]
      exact C.mul_mem hk₁ hk₂
    | inv x hx ihx =>
      obtain ⟨k, hk⟩ := ihx
      refine ⟨-k, ?_⟩
      have hx' : x⁻¹ ∈ L := L.inv_mem (hs ▸ hx)
      have e : x⁻¹ * c ^ (-k) = (x * c ^ k)⁻¹ := by
        rw [mul_inv_rev, zpow_neg, ← zpow_neg, ← hcom x⁻¹ hx' (-k)]
      rw [e]
      exact C.inv_mem hk
  have hcomm : ⁅L, L⁆ ≤ C := by
    rw [Subgroup.commutator_le]
    intro l₁ hl₁ l₂ hl₂
    obtain ⟨k₁, hk₁⟩ := hall l₁ hl₁
    obtain ⟨k₂, hk₂⟩ := hall l₂ hl₂
    have e : ⁅l₁, l₂⁆ = ⁅l₁ * c ^ k₁, l₂ * c ^ k₂⁆ :=
      (B5.comm_mul_central (hcom l₂ hl₂ k₁) (Commute.zpow_zpow_self c k₁ k₂).eq
        (hcom l₁ hl₁ k₂)).symm
    rw [e, commutatorElement_def]
    exact C.mul_mem (C.mul_mem (C.mul_mem hk₁ hk₂) (C.inv_mem hk₁)) (C.inv_mem hk₂)
  rw [hperf] at hcomm
  exact hcomm

theorem d321g_exists_conj_gens_grp {G : Type} [Group G] (hG : IsPSL 3 2 1 G) {b : G}
    (hb1 : b ≠ 1) (hbb : b * b = 1) :
    ∃ g₁ g₂ g₃ : G,
      Subgroup.closure ({g₁ * b * g₁⁻¹, g₂ * b * g₂⁻¹, g₃ * b * g₃⁻¹} : Set G) = ⊤ := by
  obtain ⟨e⟩ := nonempty_mulEquiv_slThree_of_isPSL hG
  have hinv : L3.IsInvol (e b) :=
    ⟨by rw [← map_mul, hbb, map_one], fun h => hb1 (e.injective (by rw [h, map_one]))⟩
  obtain ⟨x₁, hx₁⟩ := L3.conj_invol hinv L3.x12_invol
  obtain ⟨x₂, hx₂⟩ := L3.conj_invol hinv L3.x23_invol
  obtain ⟨x₃, hx₃⟩ := L3.conj_invol hinv L3.x31_invol
  refine ⟨e.symm x₁, e.symm x₂, e.symm x₃, ?_⟩
  have key : ∀ x y : L3.Γ, x * e b * x⁻¹ = y → e.symm x * b * (e.symm x)⁻¹ = e.symm y := by
    intro x y h
    rw [← h]
    simp
  rw [key _ _ hx₁, key _ _ hx₂, key _ _ hx₃]
  have himg : ({e.symm L3.x12, e.symm L3.x23, e.symm L3.x31} : Set G) =
      e.symm.toMonoidHom '' {L3.x12, L3.x23, L3.x31} := by
    simp [Set.image_insert_eq]
  rw [himg, ← MonoidHom.map_closure, L3.closure_gens]
  exact Subgroup.map_top_of_surjective _ e.symm.surjective

theorem d321g_exists_conj_gens {Ω : Type} [Group Ω] {L : Subgroup Ω} (hL : IsPSL 3 2 1 ↥L)
    {b : Ω} (hb : b ∈ L) (hb1 : b ≠ 1) (hbb : b * b = 1) :
    ∃ g₁ ∈ L, ∃ g₂ ∈ L, ∃ g₃ ∈ L,
      Subgroup.closure ({g₁ * b * g₁⁻¹, g₂ * b * g₂⁻¹, g₃ * b * g₃⁻¹} : Set Ω) = L := by
  obtain ⟨g₁, g₂, g₃, hgen⟩ := d321g_exists_conj_gens_grp hL (b := ⟨b, hb⟩)
    (fun h => hb1 (congrArg Subtype.val h)) (Subtype.ext hbb)
  refine ⟨g₁, g₁.2, g₂, g₂.2, g₃, g₃.2, ?_⟩
  have h := congrArg (Subgroup.map L.subtype) hgen
  rw [MonoidHom.map_closure, Subgroup.map_top, Subgroup.range_subtype] at h
  have himg : L.subtype '' ({g₁ * ⟨b, hb⟩ * g₁⁻¹, g₂ * ⟨b, hb⟩ * g₂⁻¹, g₃ * ⟨b, hb⟩ * g₃⁻¹} :
      Set ↥L) = ({(g₁ : Ω) * b * (g₁ : Ω)⁻¹, (g₂ : Ω) * b * (g₂ : Ω)⁻¹,
        (g₃ : Ω) * b * (g₃ : Ω)⁻¹} : Set Ω) := by
    simp [Set.image_insert_eq]
  rw [himg] at h
  exact h

theorem d321g_commutator_eq_of_isPSL {Ω : Type} [Group Ω] {L : Subgroup Ω}
    (hL : IsPSL 3 2 1 ↥L) : ⁅L, L⁆ = L := by
  obtain ⟨e⟩ := nonempty_mulEquiv_slThree_of_isPSL hL
  have h1 : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :=
    CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect le_rfl
  have h2 : Group.IsPerfect ↥L :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  exact Subgroup.isPerfect_iff.mp h2

section Ranks

variable {W : Type} [CommGroup W]

theorem d321g_mem_centSec {U S : Subgroup W} {a : MulAut W} (ha : a ∈ stabSub U)
    (hS : U.map (commHom a) ≤ S) : a ∈ centSec U S :=
  ⟨ha, fun u hu => hS ⟨u, hu, rfl⟩⟩

theorem d321g_rk_sup_add_le [Finite W] {P Q Z : Subgroup W} (hP : Z ≤ P) (hQ : Z ≤ Q) :
    rk ↥(P ⊔ Q) + rk ↥Z ≤ rk ↥P + rk ↥Q := by
  have h := rk_sup_add_rk_inf P Q
  have h2 : rk ↥Z ≤ rk ↥(P ⊓ Q) := rk_mono (le_inf hP hQ)
  omega

theorem d321g_rk_commImg_sup [Finite W] {U Z : Subgroup W} {a : MulAut W} (hZU : Z ≤ U)
    (haU : a ∈ stabSub U) (haZ : a ∈ stabSub Z) :
    rk ↥(U.map (commHom a) ⊔ Z) ≤ rk ↥Z + rkIdx (fixV (autSec (Subgroup.zpowers a) U Z)) := by
  have hAU : Subgroup.zpowers a ≤ stabSub U := Subgroup.zpowers_le.2 haU
  have hAZ : Subgroup.zpowers a ≤ stabSub Z := Subgroup.zpowers_le.2 haZ
  have h0 := d321d_rkIdx_add_rk_commModSub hZU hAU hAZ
  set φ : W →* W ⧸ Z := (QuotientGroup.mk' Z).comp (commHom a)
  have h1 := rk_map_add_rk_inf_ker φ U
  have h2 := rk_map_add_rk_inf_ker (QuotientGroup.mk' Z) (U.map (commHom a) ⊔ Z)
  rw [QuotientGroup.ker_mk', inf_eq_right.2 le_sup_right] at h2
  have h3 : (U.map (commHom a) ⊔ Z).map (QuotientGroup.mk' Z) = U.map φ := by
    rw [Subgroup.map_sup, QuotientGroup.map_mk'_self, sup_bot_eq, Subgroup.map_map]
  rw [h3] at h2
  have h4 : commModSub U (Subgroup.zpowers a) Z ≤ U ⊓ φ.ker := by
    intro u hu
    refine ⟨hu.1, MonoidHom.mem_ker.2 ?_⟩
    exact (QuotientGroup.eq_one_iff _).2 (hu.2 a (Subgroup.mem_zpowers a))
  have h5 := rk_mono h4
  omega

theorem d321g_rkIdx_conj [Finite W] {U Z : Subgroup W} {a g : MulAut W} (hZU : Z ≤ U)
    (hgU : g ∈ stabSub U) (hgZ : g ∈ stabSub Z) (haU : a ∈ stabSub U) (haZ : a ∈ stabSub Z) :
    rkIdx (fixV (autSec (Subgroup.zpowers (g * a * g⁻¹)) U Z)) =
      rkIdx (fixV (autSec (Subgroup.zpowers a) U Z)) := by
  have hEU : Subgroup.zpowers a ≤ stabSub U := Subgroup.zpowers_le.2 haU
  have hEZ : Subgroup.zpowers a ≤ stabSub Z := Subgroup.zpowers_le.2 haZ
  have h := d321d_rkIdx_fixV_autSec_conj g hZU hEU hEZ
  have hz : conjAutSub g (Subgroup.zpowers a) = Subgroup.zpowers (g * a * g⁻¹) := by
    unfold conjAutSub
    rw [MonoidHom.map_zpowers]
    congr 1
  rw [map_eq_of_mem_stabSub hgU, map_eq_of_mem_stabSub hgZ, hz] at h
  exact h

end Ranks

set_option linter.unusedVariables false in
theorem d321x_gen_sec {W : Type} [CommGroup W] [Finite W] (hexp : ∀ w : W, w ^ 2 = 1)
    {L : Subgroup (MulAut W)} {U Z : Subgroup W} (hZU : Z ≤ U)
    (hLU : L ≤ stabSub U) (hLZ : L ≤ stabSub Z) (hf : L ⊓ centSec U Z = ⊥)
    (hpsl : IsPSL 3 2 1 ↥L) (hperf : commSub U L ⊔ Z = U)
    {b c : MulAut W} (hb : b ∈ L) (hb1 : b ≠ 1) (hbb : b * b = 1)
    (hc : ∀ l ∈ L, c * l = l * c) (hcU : c ∈ stabSub U) (hcZ : c ∈ stabSub Z) :
    rk (Sec U Z) ≤ 3 * rkIdx (fixV (autSec (Subgroup.zpowers (b * c)) U Z)) := by
  obtain ⟨g₁, hg₁, g₂, hg₂, g₃, hg₃, hgen⟩ := d321g_exists_conj_gens hpsl hb hb1 hbb
  have hperfL : ⁅L, L⁆ = L := d321g_commutator_eq_of_isPSL hpsl
  have haU : b * c ∈ stabSub U := (stabSub U).mul_mem (hLU hb) hcU
  have haZ : b * c ∈ stabSub Z := (stabSub Z).mul_mem (hLZ hb) hcZ
  have hconj : ∀ g ∈ L, g * b * g⁻¹ * c = g * (b * c) * g⁻¹ := by
    intro g hg
    have h := (Commute.inv_right (show Commute c g from hc g hg)).eq
    calc g * b * g⁻¹ * c = g * b * (g⁻¹ * c) := by rw [mul_assoc (g * b)]
      _ = g * b * (c * g⁻¹) := by rw [h]
      _ = g * (b * c) * g⁻¹ := by group
  have hrk : ∀ g ∈ L, rk ↥(U.map (commHom (g * b * g⁻¹ * c)) ⊔ Z) ≤
      rk ↥Z + rkIdx (fixV (autSec (Subgroup.zpowers (b * c)) U Z)) := by
    intro g hg
    rw [hconj g hg]
    have h1 := d321g_rk_commImg_sup hZU ((stabSub U).mul_mem ((stabSub U).mul_mem (hLU hg)
      haU) ((stabSub U).inv_mem (hLU hg))) ((stabSub Z).mul_mem ((stabSub Z).mul_mem (hLZ hg)
      haZ) ((stabSub Z).inv_mem (hLZ hg)))
    have h2 := d321g_rkIdx_conj hZU (hLU hg) (hLZ hg) haU haZ
    rw [h2] at h1
    exact h1
  set P₁ := U.map (commHom (g₁ * b * g₁⁻¹ * c)) ⊔ Z
  set P₂ := U.map (commHom (g₂ * b * g₂⁻¹ * c)) ⊔ Z
  set P₃ := U.map (commHom (g₃ * b * g₃⁻¹ * c)) ⊔ Z
  have hZP₁ : Z ≤ P₁ := le_sup_right
  have hZP₂ : Z ≤ P₂ := le_sup_right
  have hZP₃ : Z ≤ P₃ := le_sup_right
  set S := P₁ ⊔ P₂ ⊔ P₃
  have hmemC : ∀ g ∈ L, g * b * g⁻¹ * c ∈ stabSub U := fun g hg =>
    (stabSub U).mul_mem (hLU (L.mul_mem (L.mul_mem hg hb) (L.inv_mem hg))) hcU
  have hLC : L ≤ centSec U S := by
    refine d321g_perfect_le hperfL hc hgen ?_
    rintro x (rfl | rfl | rfl)
    · exact d321g_mem_centSec (hmemC g₁ hg₁)
        (le_sup_left.trans (le_sup_left.trans le_sup_left))
    · exact d321g_mem_centSec (hmemC g₂ hg₂)
        (le_sup_left.trans (le_sup_right.trans le_sup_left))
    · exact d321g_mem_centSec (hmemC g₃ hg₃) (le_sup_left.trans le_sup_right)
  have hUS : U ≤ S := by
    rw [← hperf]
    refine sup_le ?_ (hZP₁.trans (le_sup_left.trans le_sup_left))
    rw [commSub, Subgroup.closure_le]
    rintro _ ⟨x, hx, w, hw, rfl⟩
    exact (hLC hx).2 w hw
  have h1 : rk ↥P₁ ≤ rk ↥Z + rkIdx (fixV (autSec (Subgroup.zpowers (b * c)) U Z)) :=
    hrk g₁ hg₁
  have h2 : rk ↥P₂ ≤ rk ↥Z + rkIdx (fixV (autSec (Subgroup.zpowers (b * c)) U Z)) :=
    hrk g₂ hg₂
  have h3 : rk ↥P₃ ≤ rk ↥Z + rkIdx (fixV (autSec (Subgroup.zpowers (b * c)) U Z)) :=
    hrk g₃ hg₃
  have h12 := d321g_rk_sup_add_le (Z := Z) hZP₁ hZP₂
  have h123 := d321g_rk_sup_add_le (P := P₁ ⊔ P₂) (Q := P₃) (Z := Z)
    (hZP₁.trans le_sup_left) hZP₃
  have hU : rk ↥U ≤ rk ↥(P₁ ⊔ P₂ ⊔ P₃) := rk_mono hUS
  have hsec := B5.rk_sec_add hZU
  omega

end CFSG.Quasithin
