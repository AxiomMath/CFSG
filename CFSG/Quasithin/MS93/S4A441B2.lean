module

public import CFSG.Quasithin.MS93.S4A441B1
public import CFSG.Quasithin.MS93.S4A441C2
public import CFSG.Quasithin.MS93.S4AFSec
public import CFSG.Quasithin.MS93.S4A432H
public import CFSG.Quasithin.Background.HConj
public import CFSG.Quasithin.Background.SmithB51SL3A
public import CFSG.Quasithin.MS93.S4A441C3
public import CFSG.Quasithin.MS93.S4A44Stmt
public import CFSG.Quasithin.MS93.S4A44U

public section

namespace CFSG.Quasithin.MS93.S4A.C441

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Quasithin.MS93 CFSG.Quasithin.MS93.S4A
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

theorem exists_lift_of_ker_le {A B C : Type*} [Group A] [Group B] [Group C] {f : A →* B}
    (hf : Function.Surjective f) {g : A →* C} (hker : f.ker ≤ g.ker) :
    ∃ g' : B →* C, ∀ a, g' (f a) = g a :=
  ⟨f.liftOfRightInverse (Function.surjInv hf) (Function.rightInverse_surjInv hf) ⟨g, hker⟩,
    fun a => MonoidHom.liftOfRightInverse_comp_apply f _ _ ⟨g, hker⟩ a⟩

section Perfect

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
include h

theorem commutator_mem_zm_of_mem_zm_sup_dloc {α : Vtx (puAmalgam h.le)} (hα : IsMVtx _ α)
    {W : Subgroup (puAmalgam h.le).Universal} (hWab : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a)
    (hWs : W ≤ stab (puAmalgam h.le) α)
    (hWn : stab (puAmalgam h.le) α ≤ Subgroup.normalizer (W : Set (puAmalgam h.le).Universal))
    {z : (puAmalgam h.le).Universal} (hz : z ∈ W)
    (hzl : ∀ l ∈ Ltil h.le L α, ⁅z, l⁆ ∈ ZM (puAmalgam h.le) α ⊔ Dloc h.le L α) :
    ∀ l ∈ Ltil h.le L α, ⁅z, l⁆ ∈ ZM (puAmalgam h.le) α := by
  have hLs : Ltil h.le L α ≤ stab (puAmalgam h.le) α := ltil_le_stab h α
  have hZn := stab_le_normalizer_zm (puAmalgam h.le) α
  have hDn : stab (puAmalgam h.le) α ≤
      Subgroup.normalizer (Dloc h.le L α : Set (puAmalgam h.le).Universal) :=
    stab_le_normalizer_dloc h α
  have hDc := dloc_le_centralizer_ltil h hα
  have hZs : ZM (puAmalgam h.le) α ≤ stab (puAmalgam h.le) α :=
    (zm_le_qv_self _ hα h.critDist_pos).trans (qv_le_stab _ α)
  have hcW : ∀ l ∈ Ltil h.le L α, ⁅z, l⁆ ∈ W := by
    intro l hl
    rw [commutatorElement_def]
    have h1 : l * z⁻¹ * l⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp (hWn (hLs hl)) _).mp
      (W.inv_mem hz)
    have : z * l * z⁻¹ * l⁻¹ = z * (l * z⁻¹ * l⁻¹) := by group
    rw [this]
    exact W.mul_mem hz h1
  have htriv : ∀ l ∈ Ltil h.le L α, ∀ e ∈ ZM (puAmalgam h.le) α ⊔ Dloc h.le L α,
      l * e * l⁻¹ * e⁻¹ ∈ ZM (puAmalgam h.le) α := by
    intro l hl e he
    have he' : e ∈ ((ZM (puAmalgam h.le) α ⊔ Dloc h.le L α : Subgroup _) :
        Set (puAmalgam h.le).Universal) := he
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ (hZs.trans hDn)] at he'
    obtain ⟨a, ha, b, hb, rfl⟩ := he'
    have hbl : b * l⁻¹ = l⁻¹ * b :=
      (Subgroup.mem_centralizer_iff.mp (hDc hb) l⁻¹ ((Ltil h.le L α).inv_mem hl)).symm
    have : l * (a * b) * l⁻¹ * (a * b)⁻¹ = l * a * l⁻¹ * a⁻¹ := by
      calc l * (a * b) * l⁻¹ * (a * b)⁻¹ = l * a * (b * l⁻¹) * b⁻¹ * a⁻¹ := by group
        _ = l * a * (l⁻¹ * b) * b⁻¹ * a⁻¹ := by rw [hbl]
        _ = l * a * l⁻¹ * a⁻¹ := by group
    change l * (a * b) * l⁻¹ * (a * b)⁻¹ ∈ _
    rw [this]
    exact (ZM (puAmalgam h.le) α).mul_mem
      ((Subgroup.mem_normalizer_iff.mp (hZn (hLs hl)) a).mp ha) ((ZM _ α).inv_mem ha)
  set N := (ZM (puAmalgam h.le) α).subgroupOf W with hN
  have hNn : N.Normal := ⟨fun n hn g => by
    have e : g * n * g⁻¹ = n := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [hWab g g.2 n n.2]
      group
    rw [e]
    exact hn⟩
  let f : ↥(Ltil h.le L α) →* ↥W ⧸ N := MonoidHom.mk' (fun l => QuotientGroup.mk
      (⟨⁅z, (l : (puAmalgam h.le).Universal)⁆, hcW l l.2⟩ : ↥W)) (by
    rintro ⟨a, ha⟩ ⟨b, hb⟩
    rw [← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    change (⁅z, a * b⁆)⁻¹ * (⁅z, a⁆ * ⁅z, b⁆) ∈ ZM (puAmalgam h.le) α
    have hB := htriv a ha ⁅z, b⁆ (hzl b hb)
    have e : (⁅z, a * b⁆)⁻¹ * (⁅z, a⁆ * ⁅z, b⁆) =
        (⁅z, b⁆)⁻¹ * (a * ⁅z, b⁆ * a⁻¹ * (⁅z, b⁆)⁻¹)⁻¹ * ⁅z, b⁆ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    have h1 : (a * ⁅z, b⁆ * a⁻¹ * (⁅z, b⁆)⁻¹)⁻¹ ∈ ZM (puAmalgam h.le) α := (ZM _ α).inv_mem hB
    have hBs : (⁅z, b⁆)⁻¹ ∈ stab (puAmalgam h.le) α := (stab _ α).inv_mem (hWs (hcW b hb))
    have h2 := (Subgroup.mem_normalizer_iff.mp (hZn hBs) _).mp h1
    simpa using h2)
  have hf : ∀ l : ↥(Ltil h.le L α), f l = QuotientGroup.mk
      (⟨⁅z, (l : (puAmalgam h.le).Universal)⁆, hcW l l.2⟩ : ↥W) := fun _ => rfl
  have hcomm : ∀ a b : ↥(Ltil h.le L α), f a * f b = f b * f a := by
    intro a b
    rw [hf, hf, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext (hWab _ (hcW a a.2) _ (hcW b b.2))
  have hker : ∀ l ∈ ⁅Ltil h.le L α, Ltil h.le L α⁆, ∀ hl : l ∈ Ltil h.le L α, f ⟨l, hl⟩ = 1 := by
    intro l hl'
    rw [Subgroup.commutator_def] at hl'
    induction hl' using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨a, ha, b, hb, rfl⟩ := hx
      intro hl
      have e : (⟨⁅a, b⁆, hl⟩ : ↥(Ltil h.le L α)) =
          ⟨a, ha⟩ * ⟨b, hb⟩ * (⟨a, ha⟩ : ↥(Ltil h.le L α))⁻¹ * (⟨b, hb⟩ : ↥(Ltil h.le L α))⁻¹ := by
        apply Subtype.ext
        simp [commutatorElement_def]
      rw [e, map_mul, map_mul, map_mul, map_inv, map_inv, hcomm ⟨a, ha⟩ ⟨b, hb⟩]
      group
    | one => intro hl; exact map_one f
    | mul x y hx hy ihx ihy =>
      intro hl
      have hxL : x ∈ Ltil h.le L α := by
        rw [← ltil_perfect h hα]
        rw [← Subgroup.commutator_def] at hx
        exact hx
      have hyL : y ∈ Ltil h.le L α := by
        rw [← ltil_perfect h hα]
        rw [← Subgroup.commutator_def] at hy
        exact hy
      have e : (⟨x * y, hl⟩ : ↥(Ltil h.le L α)) = ⟨x, hxL⟩ * ⟨y, hyL⟩ := rfl
      rw [e, map_mul, ihx hxL, ihy hyL, one_mul]
    | inv x hx ihx =>
      intro hl
      have hxL : x ∈ Ltil h.le L α := by
        rw [← ltil_perfect h hα]
        rw [← Subgroup.commutator_def] at hx
        exact hx
      have e : (⟨x⁻¹, hl⟩ : ↥(Ltil h.le L α)) = (⟨x, hxL⟩ : ↥(Ltil h.le L α))⁻¹ := rfl
      rw [e, map_inv, ihx hxL, inv_one]
  intro l hl
  have hl' : l ∈ ⁅Ltil h.le L α, Ltil h.le L α⁆ := by rw [ltil_perfect h hα]; exact hl
  have h1 := hker l hl' hl
  rw [hf, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
  exact h1

end Perfect

end CFSG.Quasithin.MS93.S4A.C441
