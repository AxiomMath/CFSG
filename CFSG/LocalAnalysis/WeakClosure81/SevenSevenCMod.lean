module

public import CFSG.LocalAnalysis.WeakClosure81.SevenCommI
public import CFSG.LocalAnalysis.WeakClosure81.SevenSix
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.WeakClosure81.SevenKDefs
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup
open CFSG.LocalAnalysis.WeakClosure81.SevenK
open scoped commutatorElement

section Cfg

variable {G : Type} [Group G]

structure SevenSevenCfg (V H E V₁ V₂ V₃ : Subgroup G) : Prop where
  mem₁ : V₁ ∈ omegaSet V H E
  mem₂ : V₂ ∈ omegaSet V H E
  mem₃ : V₃ ∈ omegaSet V H E
  small : ∀ U ∈ omegaSet V H E, ∀ u ∈ U, ∀ w ∈ U, u ∉ iSub V H E → w ∉ iSub V H E →
    u * w ∈ iSub V H E
  comm₁₂ : ⁅V₁, V₂⁆ = ⊥
  ne₁₂ : V₁ ≠ V₂
  norm₁₃ : ∀ v ∈ V₁, v ∈ Subgroup.normalizer (V₃ : Set G) → v ∈ iSub V H E
  norm₂₃ : ∀ v ∈ V₂, v ∈ Subgroup.normalizer (V₃ : Set G) → v ∈ iSub V H E
  norm₃₁ : ∀ v ∈ V₃, v ∈ Subgroup.normalizer (V₁ : Set G) → v ∈ iSub V H E
  norm₃₂ : ∀ v ∈ V₃, v ∈ Subgroup.normalizer (V₂ : Set G) → v ∈ iSub V H E

structure SevenSevenModule (V H E V₁ V₂ V₃ A : Subgroup G) : Prop where
  le_iSub : A ≤ iSub V H E
  normalizes : V₁ ⊔ V₂ ⊔ V₃ ≤ Subgroup.normalizer (A : Set G)
  commutator_eq : ⁅A, V₁ ⊔ V₂ ⊔ V₃⁆ = A
  ne_bot : A ≠ ⊥

end Cfg

section Mod

variable {G : Type} [Group G] [Finite G]

variable {V H E J V₁ V₂ V₃ A : Subgroup G}

private theorem seven_seven_c_mod_iSub_comm (h : Hyp73 V H E J) {a b : G}
    (ha : a ∈ iSub V H E) (hb : b ∈ iSub V H E) : a * b = b * a :=
  congrArg Subtype.val
    ((seven_two_iSub_isElemAbelian_uncond h.elemAbelian h.ti h.abelian h.omega_le).1.is_comm.comm
      ⟨a, ha⟩ ⟨b, hb⟩)

private theorem seven_seven_c_mod_exists_mem_notMem_iSub (h : Hyp73 V H E J) {U : Subgroup G}
    (hU : U ∈ omegaSet V H E) : ∃ v ∈ U, v ∉ iSub V H E := by
  by_contra hcon
  push Not at hcon
  exact (mem_omegaSet.mp hU).choose_spec.2.2
    (le_trans (fun v hv => hcon v hv) (h.iSub_le.trans h.pcore_le))

private theorem seven_seven_c_mod_comm_of_mem (h : Hyp73 V H E J) {U : Subgroup G}
    (hU : U ∈ omegaSet V H E) {x y : G} (hx : x ∈ U) (hy : y ∈ U) : x * y = y * x :=
  congrArg Subtype.val
    ((isElemAbelian_of_mem_omegaSet h.elemAbelian hU).1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)

private theorem seven_seven_c_mod_inf_V₁_V₂_eq_bot (h : Hyp73 V H E J)
    (hc : SevenSevenCfg V H E V₁ V₂ V₃) : V₁ ⊓ V₂ = ⊥ := by
  obtain ⟨g₁, hg₁, -, -⟩ := mem_omegaSet.mp hc.mem₁
  obtain ⟨g₂, hg₂, -, -⟩ := mem_omegaSet.mp hc.mem₂
  rcases inf_conjSubgroup_eq_bot_or_eq h.ti g₁ g₂ with hbot | heq
  · rwa [hg₁, hg₂]
  · exact absurd (by rw [hg₁, hg₂]; exact heq) hc.ne₁₂

private theorem seven_seven_c_mod_comm_V₁_V₂ (hc : SevenSevenCfg V H E V₁ V₂ V₃)
    {x y : G} (hx : x ∈ V₁) (hy : y ∈ V₂) : x * y = y * x := by
  have hmem : ⁅x, y⁆ ∈ ⁅V₁, V₂⁆ := Subgroup.commutator_mem_commutator hx hy
  rw [hc.comm₁₂] at hmem
  exact (commute_iff_eq x y).mp
    ((commutatorElement_eq_one_iff_commute).mp (Subgroup.mem_bot.mp hmem))

private theorem seven_seven_c_mod_V₁_le_normalizer (hA : SevenSevenModule V H E V₁ V₂ V₃ A) :
    V₁ ≤ Subgroup.normalizer (A : Set G) :=
  (le_sup_left.trans le_sup_left).trans hA.normalizes

private theorem seven_seven_c_mod_V₂_le_normalizer (hA : SevenSevenModule V H E V₁ V₂ V₃ A) :
    V₂ ≤ Subgroup.normalizer (A : Set G) :=
  (le_sup_right.trans le_sup_left).trans hA.normalizes

private theorem seven_seven_c_mod_V₃_le_normalizer (hA : SevenSevenModule V H E V₁ V₂ V₃ A) :
    V₃ ≤ Subgroup.normalizer (A : Set G) :=
  le_sup_right.trans hA.normalizes

private theorem seven_seven_c_mod_commutator_mem_of_mem_normalizer {x a : G}
    (hx : x ∈ Subgroup.normalizer (A : Set G)) (ha : a ∈ A) : ⁅a, x⁆ ∈ A := by
  have hmem : x * a⁻¹ * x⁻¹ ∈ A :=
    (Subgroup.mem_normalizer_iff.mp hx a⁻¹).mp (A.inv_mem ha)
  rw [commutatorElement_def]
  rw [show a * x * a⁻¹ * x⁻¹ = a * (x * a⁻¹ * x⁻¹) by group]
  exact A.mul_mem ha hmem

private theorem seven_seven_c_mod_commutator_le_of_le_normalizer {W : Subgroup G}
    (hW : W ≤ Subgroup.normalizer (A : Set G)) : ⁅A, W⁆ ≤ A :=
  Subgroup.commutator_le.mpr fun a ha x hx =>
    seven_seven_c_mod_commutator_mem_of_mem_normalizer (hW hx) ha

private theorem seven_seven_c_mod_mem_sup_of_commute {B C : Subgroup G}
    (hB : B ≤ A) (hC : C ≤ A) (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    {x : G} (hx : x ∈ B ⊔ C) : ∃ b ∈ B, ∃ c ∈ C, b * c = x := by
  rw [Subgroup.sup_eq_closure] at hx
  refine Subgroup.closure_induction (p := fun y _ => ∃ b ∈ B, ∃ c ∈ C, b * c = y)
    ?_ ?_ ?_ ?_ hx
  · rintro y (hy | hy)
    · exact ⟨y, hy, 1, C.one_mem, by simp⟩
    · exact ⟨1, B.one_mem, y, hy, by simp⟩
  · exact ⟨1, B.one_mem, 1, C.one_mem, by simp⟩
  · rintro x y hx hy ⟨b₁, hb₁, c₁, hc₁, rfl⟩ ⟨b₂, hb₂, c₂, hc₂, rfl⟩
    refine ⟨b₁ * b₂, B.mul_mem hb₁ hb₂, c₁ * c₂, C.mul_mem hc₁ hc₂, ?_⟩
    calc b₁ * b₂ * (c₁ * c₂)
        = b₁ * (b₂ * c₁) * c₂ := by group
      _ = b₁ * (c₁ * b₂) * c₂ := by rw [hcomm b₂ (hB hb₂) c₁ (hC hc₁)]
      _ = b₁ * c₁ * (b₂ * c₂) := by group
  · rintro x _ ⟨b, hb, c, hc, rfl⟩
    refine ⟨b⁻¹, B.inv_mem hb, c⁻¹, C.inv_mem hc, ?_⟩
    rw [mul_inv_rev]
    have hbA : b⁻¹ ∈ A := hB (B.inv_mem hb)
    have hcA : c⁻¹ ∈ A := hC (C.inv_mem hc)
    exact hcomm b⁻¹ hbA c⁻¹ hcA

theorem commutator_le_inf_of_mem_omegaSet (h : Hyp73 V H E J) {U : Subgroup G}
    (hU : U ∈ omegaSet V H E) (hA : A ≤ iSub V H E) (hN : U ≤ Subgroup.normalizer (A : Set G)) :
    ⁅A, U⁆ ≤ A ⊓ U := by
  refine Subgroup.commutator_le.mpr fun a ha u hu => ?_
  have hmem : ⁅a, u⁆ ∈ U ⊓ iSub U H E := by
    refine commutator_mem_inf_iSub (V := U) (H := H) (E := E)
      (isElemAbelian_of_mem_omegaSet h.elemAbelian hU)
      (isTI_of_mem_omegaSet hU h.ti) h.abelian h.le h.normal ?_ ?_ ?_ hu
    · intro W hW
      rw [omegaSet_eq_of_mem hU] at hW
      exact h.omega_le W hW
    · rw [omegaSet_eq_of_mem hU]
      exact hU
    · rw [iSub_eq_of_mem hU]
      exact hA ha
  exact ⟨seven_seven_c_mod_commutator_mem_of_mem_normalizer (hN hu) ha,
    (Subgroup.mem_inf.mp hmem).1⟩

private theorem seven_seven_c_mod_commutator_le_inf₁ (h : Hyp73 V H E J)
    (hc : SevenSevenCfg V H E V₁ V₂ V₃) (hA : SevenSevenModule V H E V₁ V₂ V₃ A) :
    ⁅A, V₁⁆ ≤ A ⊓ V₁ :=
  commutator_le_inf_of_mem_omegaSet h hc.mem₁ hA.le_iSub (seven_seven_c_mod_V₁_le_normalizer hA)

private theorem seven_seven_c_mod_commutator_le_inf₂ (h : Hyp73 V H E J)
    (hc : SevenSevenCfg V H E V₁ V₂ V₃) (hA : SevenSevenModule V H E V₁ V₂ V₃ A) :
    ⁅A, V₂⁆ ≤ A ⊓ V₂ :=
  commutator_le_inf_of_mem_omegaSet h hc.mem₂ hA.le_iSub (seven_seven_c_mod_V₂_le_normalizer hA)

private theorem seven_seven_c_mod_commutator_le_inf₃ (h : Hyp73 V H E J)
    (hc : SevenSevenCfg V H E V₁ V₂ V₃) (hA : SevenSevenModule V H E V₁ V₂ V₃ A) :
    ⁅A, V₃⁆ ≤ A ⊓ V₃ :=
  commutator_le_inf_of_mem_omegaSet h hc.mem₃ hA.le_iSub (seven_seven_c_mod_V₃_le_normalizer hA)

theorem le_sup_commutator (h : Hyp73 V H E J) (hc : SevenSevenCfg V H E V₁ V₂ V₃)
    (hA : SevenSevenModule V H E V₁ V₂ V₃ A) : A ≤ ⁅A, V₁⁆ ⊔ ⁅A, V₂⁆ ⊔ ⁅A, V₃⁆ := by
  let S : Subgroup G := ⁅A, V₁⁆ ⊔ ⁅A, V₂⁆ ⊔ ⁅A, V₃⁆
  have hS_eq : S = ⁅A, V₁⁆ ⊔ ⁅A, V₂⁆ ⊔ ⁅A, V₃⁆ := rfl
  have hSA : S ≤ A := by
    rw [hS_eq]
    exact sup_le (sup_le
      (seven_seven_c_mod_commutator_le_of_le_normalizer (seven_seven_c_mod_V₁_le_normalizer hA))
      (seven_seven_c_mod_commutator_le_of_le_normalizer (seven_seven_c_mod_V₂_le_normalizer hA)))
      (seven_seven_c_mod_commutator_le_of_le_normalizer (seven_seven_c_mod_V₃_le_normalizer hA))
  let T : Subgroup G :=
    { carrier := {x | x ∈ Subgroup.normalizer (A : Set G) ∧ ∀ a ∈ A, ⁅a, x⁆ ∈ S}
      one_mem' := ⟨by simp, by intro a ha; simp [commutatorElement_def]⟩
      mul_mem' := by
        rintro x y ⟨hxA, hxS⟩ ⟨hyA, hyS⟩
        refine ⟨(Subgroup.normalizer (A : Set G)).mul_mem hxA hyA, fun a ha => ?_⟩
        have h2 : x * ⁅a, y⁆ * x⁻¹ ∈ S := by
          have hcommS : ⁅⁅a, y⁆, x⁆ ∈ S := hxS ⁅a, y⁆ (hSA (hyS a ha))
          have h3 : ⁅x, ⁅a, y⁆⁆ ∈ S := by
            rw [← commutatorElement_inv]
            exact S.inv_mem hcommS
          rw [show x * ⁅a, y⁆ * x⁻¹ = ⁅x, ⁅a, y⁆⁆ * ⁅a, y⁆ by
                simp only [commutatorElement_def]; group]
          exact S.mul_mem h3 (hyS a ha)
        rw [show ⁅a, x * y⁆ = ⁅a, x⁆ * (x * ⁅a, y⁆ * x⁻¹) by
              simp only [commutatorElement_def]; group]
        exact S.mul_mem (hxS a ha) h2
      inv_mem' := by
        rintro x ⟨hxA, hxS⟩
        refine ⟨(Subgroup.normalizer (A : Set G)).inv_mem hxA, fun a ha => ?_⟩
        have ha' : x⁻¹ * a * x ∈ A := (Subgroup.mem_normalizer_iff''.mp hxA a).mp ha
        have h2 : ⁅x⁻¹ * a * x, x⁆ ∈ S := hxS _ ha'
        rw [show ⁅a, x⁻¹⁆ = ⁅x⁻¹ * a * x, x⁆⁻¹ by
              simp only [commutatorElement_def]; group]
        exact S.inv_mem h2 }
  have hle₁ : ⁅A, V₁⁆ ≤ S := by
    rw [hS_eq]
    exact le_sup_left.trans le_sup_left
  have hle₂ : ⁅A, V₂⁆ ≤ S := by
    rw [hS_eq]
    exact le_sup_right.trans le_sup_left
  have hle₃ : ⁅A, V₃⁆ ≤ S := by
    rw [hS_eq]
    exact le_sup_right
  have hVT : V₁ ⊔ V₂ ⊔ V₃ ≤ T := by
    refine sup_le (sup_le ?_ ?_) ?_
    · intro x hx
      refine ⟨seven_seven_c_mod_V₁_le_normalizer hA hx, fun a ha => ?_⟩
      exact hle₁ (Subgroup.commutator_mem_commutator ha hx)
    · intro x hx
      refine ⟨seven_seven_c_mod_V₂_le_normalizer hA hx, fun a ha => ?_⟩
      exact hle₂ (Subgroup.commutator_mem_commutator ha hx)
    · intro x hx
      refine ⟨seven_seven_c_mod_V₃_le_normalizer hA hx, fun a ha => ?_⟩
      exact hle₃ (Subgroup.commutator_mem_commutator ha hx)
  have hle : ⁅A, V₁ ⊔ V₂ ⊔ V₃⁆ ≤ S := by
    refine Subgroup.commutator_le.mpr fun a ha x hx => ?_
    have hxT := hVT hx
    have hxT' : x ∈ Subgroup.normalizer (A : Set G) ∧ ∀ a ∈ A, ⁅a, x⁆ ∈ S := hxT
    exact hxT'.2 a ha
  rwa [hA.commutator_eq] at hle

theorem exists_commutator_factorization (h : Hyp73 V H E J)
    (hc : SevenSevenCfg V H E V₁ V₂ V₃) (hA : SevenSevenModule V H E V₁ V₂ V₃ A) :
    ∀ a ∈ A, ∃ a₁ ∈ ⁅A, V₁⁆, ∃ a₂ ∈ ⁅A, V₂⁆, ∃ a₃ ∈ ⁅A, V₃⁆, a₁ * a₂ * a₃ = a := by
  intro a ha
  have hA₁A : ⁅A, V₁⁆ ≤ A := (seven_seven_c_mod_commutator_le_inf₁ h hc hA).trans inf_le_left
  have hA₂A : ⁅A, V₂⁆ ≤ A := (seven_seven_c_mod_commutator_le_inf₂ h hc hA).trans inf_le_left
  have hA₃A : ⁅A, V₃⁆ ≤ A := (seven_seven_c_mod_commutator_le_inf₃ h hc hA).trans inf_le_left
  have hcommA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    seven_seven_c_mod_iSub_comm h (hA.le_iSub hx) (hA.le_iSub hy)
  have hle : A ≤ ⁅A, V₁⁆ ⊔ ⁅A, V₂⁆ ⊔ ⁅A, V₃⁆ := le_sup_commutator h hc hA
  have hle12 : ⁅A, V₁⁆ ⊔ ⁅A, V₂⁆ ≤ A := sup_le hA₁A hA₂A
  have hxA : a ∈ ⁅A, V₁⁆ ⊔ ⁅A, V₂⁆ ⊔ ⁅A, V₃⁆ := hle ha
  obtain ⟨b, hb, a₃, ha₃, hba₃⟩ :=
    seven_seven_c_mod_mem_sup_of_commute hle12 hA₃A hcommA hxA
  obtain ⟨a₁, ha₁, a₂, ha₂, ha₁a₂⟩ :=
    seven_seven_c_mod_mem_sup_of_commute hA₁A hA₂A hcommA hb
  refine ⟨a₁, ha₁, a₂, ha₂, a₃, ha₃, ?_⟩
  rw [ha₁a₂]
  exact hba₃

theorem eq_one_of_mem_commutator_of_commute (h : Hyp73 V H E J)
    (hc : SevenSevenCfg V H E V₁ V₂ V₃) (hA : SevenSevenModule V H E V₁ V₂ V₃ A) :
    (∀ v ∈ V₁, v ∉ iSub V H E → ∀ a ∈ ⁅A, V₃⁆, v * a = a * v → a = 1) ∧
      (∀ v ∈ V₂, v ∉ iSub V H E → ∀ a ∈ ⁅A, V₃⁆, v * a = a * v → a = 1) := by
  have hmem₃ : ⁅A, V₃⁆ ≤ A ⊓ V₃ := seven_seven_c_mod_commutator_le_inf₃ h hc hA
  constructor
  · intro v hv hvI a ha hcomm
    by_contra ha1
    have haV₃ : a ∈ V₃ := (Subgroup.mem_inf.mp (hmem₃ ha)).2
    obtain ⟨g, hg, -, -⟩ := mem_omegaSet.mp hc.mem₃
    have hC : Subgroup.centralizer ({a} : Set G) ≤
        Subgroup.normalizer (conjSubgroup V g : Set G) :=
      centralizer_le_normalizer_conj h.ti g (show a ∈ conjSubgroup V g from hg ▸ haV₃) ha1
    have hvC : v ∈ Subgroup.centralizer ({a} : Set G) :=
      Subgroup.mem_centralizer_iff.mpr fun b hb => by
        rw [Set.mem_singleton_iff] at hb
        subst hb
        exact hcomm.symm
    have hvN : v ∈ Subgroup.normalizer (V₃ : Set G) := by
      rw [hg]
      exact hC hvC
    exact hvI (hc.norm₁₃ v hv hvN)
  · intro v hv hvI a ha hcomm
    by_contra ha1
    have haV₃ : a ∈ V₃ := (Subgroup.mem_inf.mp (hmem₃ ha)).2
    obtain ⟨g, hg, -, -⟩ := mem_omegaSet.mp hc.mem₃
    have hC : Subgroup.centralizer ({a} : Set G) ≤
        Subgroup.normalizer (conjSubgroup V g : Set G) :=
      centralizer_le_normalizer_conj h.ti g (show a ∈ conjSubgroup V g from hg ▸ haV₃) ha1
    have hvC : v ∈ Subgroup.centralizer ({a} : Set G) :=
      Subgroup.mem_centralizer_iff.mpr fun b hb => by
        rw [Set.mem_singleton_iff] at hb
        subst hb
        exact hcomm.symm
    have hvN : v ∈ Subgroup.normalizer (V₃ : Set G) := by
      rw [hg]
      exact hC hvC
    exact hvI (hc.norm₂₃ v hv hvN)

theorem commutator_inf_commutator_eq_bot (h : Hyp73 V H E J)
    (hc : SevenSevenCfg V H E V₁ V₂ V₃) (hA : SevenSevenModule V H E V₁ V₂ V₃ A) :
    ⁅A, V₁⁆ ⊓ ⁅A, V₂⁆ = ⊥ ∧ ⁅A, V₃⁆ ⊓ (⁅A, V₁⁆ ⊔ ⁅A, V₂⁆) = ⊥ := by
  have hmem₁ : ⁅A, V₁⁆ ≤ A ⊓ V₁ := seven_seven_c_mod_commutator_le_inf₁ h hc hA
  have hmem₂ : ⁅A, V₂⁆ ≤ A ⊓ V₂ := seven_seven_c_mod_commutator_le_inf₂ h hc hA
  constructor
  · rw [Subgroup.eq_bot_iff_forall]
    intro a ha
    have hmemV : a ∈ V₁ ⊓ V₂ :=
      ⟨(hmem₁ (Subgroup.mem_inf.mp ha).1).2, (hmem₂ (Subgroup.mem_inf.mp ha).2).2⟩
    rw [seven_seven_c_mod_inf_V₁_V₂_eq_bot h hc] at hmemV
    exact Subgroup.mem_bot.mp hmemV
  · rw [Subgroup.eq_bot_iff_forall]
    intro a ha
    obtain ⟨v₁, hv₁V, hv₁I⟩ := seven_seven_c_mod_exists_mem_notMem_iSub h hc.mem₁
    have ha₃ : a ∈ ⁅A, V₃⁆ := (Subgroup.mem_inf.mp ha).1
    have ha₁₂ : a ∈ ⁅A, V₁⁆ ⊔ ⁅A, V₂⁆ := (Subgroup.mem_inf.mp ha).2
    have hcent₁ : ⁅A, V₁⁆ ≤ Subgroup.centralizer (V₁ : Set G) := by
      intro x hx
      refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
      exact seven_seven_c_mod_comm_of_mem h hc.mem₁ hy (hmem₁ hx).2
    have hcent₂ : ⁅A, V₂⁆ ≤ Subgroup.centralizer (V₁ : Set G) := by
      intro x hx
      refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
      exact seven_seven_c_mod_comm_V₁_V₂ hc hy (hmem₂ hx).2
    have hcent : ⁅A, V₁⁆ ⊔ ⁅A, V₂⁆ ≤ Subgroup.centralizer (V₁ : Set G) :=
      sup_le hcent₁ hcent₂
    have hcomm : v₁ * a = a * v₁ :=
      Subgroup.mem_centralizer_iff.mp (hcent ha₁₂) v₁ hv₁V
    exact (eq_one_of_mem_commutator_of_commute h hc hA).1 v₁ hv₁V hv₁I a ha₃ hcomm

theorem commutator_eq_inf (h : Hyp73 V H E J) (hc : SevenSevenCfg V H E V₁ V₂ V₃)
    (hA : SevenSevenModule V H E V₁ V₂ V₃ A) :
    ⁅A, V₁⁆ = A ⊓ V₁ ∧ ⁅A, V₂⁆ = A ⊓ V₂ ∧ ⁅A, V₃⁆ = A ⊓ V₃ := by
  have hmem₁ : ⁅A, V₁⁆ ≤ A ⊓ V₁ := seven_seven_c_mod_commutator_le_inf₁ h hc hA
  have hmem₂ : ⁅A, V₂⁆ ≤ A ⊓ V₂ := seven_seven_c_mod_commutator_le_inf₂ h hc hA
  have hmem₃ : ⁅A, V₃⁆ ≤ A ⊓ V₃ := seven_seven_c_mod_commutator_le_inf₃ h hc hA
  refine ⟨le_antisymm hmem₁ ?_, le_antisymm hmem₂ ?_, le_antisymm hmem₃ ?_⟩
  · intro a ha
    obtain ⟨haA, haV₁⟩ := Subgroup.mem_inf.mp ha
    obtain ⟨a₁, ha₁, a₂, ha₂, a₃, ha₃, hfac⟩ := exists_commutator_factorization h hc hA a haA
    obtain ⟨v₁, hv₁V, hv₁I⟩ := seven_seven_c_mod_exists_mem_notMem_iSub h hc.mem₁
    have ha₁V₁ : a₁ ∈ V₁ := (hmem₁ ha₁).2
    have ha₂V₂ : a₂ ∈ V₂ := (hmem₂ ha₂).2
    have ha₃_eq : a₃ = a₂⁻¹ * a₁⁻¹ * a := by rw [← hfac]; group
    have hcommC : Commute v₁ (a₂⁻¹ * a₁⁻¹ * a) :=
      (Commute.mul_right
        (show Commute v₁ a₂⁻¹ from seven_seven_c_mod_comm_V₁_V₂ hc hv₁V (V₂.inv_mem ha₂V₂))
        (show Commute v₁ a₁⁻¹ from
          seven_seven_c_mod_comm_of_mem h hc.mem₁ hv₁V (V₁.inv_mem ha₁V₁))).mul_right
        (show Commute v₁ a from seven_seven_c_mod_comm_of_mem h hc.mem₁ hv₁V haV₁)
    have ha₃1 : a₃ = 1 :=
      (eq_one_of_mem_commutator_of_commute h hc hA).1 v₁ hv₁V hv₁I a₃ ha₃
        (by rw [ha₃_eq]; exact hcommC)
    have hfac' : a₁ * a₂ = a := by simpa [ha₃1] using hfac
    have ha₂_eq : a₂ = a₁⁻¹ * a := by rw [← hfac']; group
    have ha₂bot : a₂ = 1 := by
      have hmem : a₂ ∈ V₁ ⊓ V₂ := by
        refine ⟨?_, ha₂V₂⟩
        rw [ha₂_eq]
        exact V₁.mul_mem (V₁.inv_mem ha₁V₁) haV₁
      rw [seven_seven_c_mod_inf_V₁_V₂_eq_bot h hc] at hmem
      exact Subgroup.mem_bot.mp hmem
    have ha_eq : a = a₁ := by rw [← hfac', ha₂bot, mul_one]
    rw [ha_eq]
    exact ha₁
  · intro a ha
    obtain ⟨haA, haV₂⟩ := Subgroup.mem_inf.mp ha
    obtain ⟨a₁, ha₁, a₂, ha₂, a₃, ha₃, hfac⟩ := exists_commutator_factorization h hc hA a haA
    obtain ⟨v₂, hv₂V, hv₂I⟩ := seven_seven_c_mod_exists_mem_notMem_iSub h hc.mem₂
    have ha₁V₁ : a₁ ∈ V₁ := (hmem₁ ha₁).2
    have ha₂V₂ : a₂ ∈ V₂ := (hmem₂ ha₂).2
    have ha₃_eq : a₃ = a₂⁻¹ * a₁⁻¹ * a := by rw [← hfac]; group
    have hcommC : Commute v₂ (a₂⁻¹ * a₁⁻¹ * a) :=
      (Commute.mul_right
        (show Commute v₂ a₂⁻¹ from
          seven_seven_c_mod_comm_of_mem h hc.mem₂ hv₂V (V₂.inv_mem ha₂V₂))
        (show Commute v₂ a₁⁻¹ from (show Commute a₁⁻¹ v₂ from
          seven_seven_c_mod_comm_V₁_V₂ hc (V₁.inv_mem ha₁V₁) hv₂V).symm)).mul_right
        (show Commute v₂ a from seven_seven_c_mod_comm_of_mem h hc.mem₂ hv₂V haV₂)
    have ha₃1 : a₃ = 1 :=
      (eq_one_of_mem_commutator_of_commute h hc hA).2 v₂ hv₂V hv₂I a₃ ha₃
        (by rw [ha₃_eq]; exact hcommC)
    have hfac' : a₁ * a₂ = a := by simpa [ha₃1] using hfac
    have ha₁_eq : a₁ = a * a₂⁻¹ := by rw [← hfac']; group
    have ha₁bot : a₁ = 1 := by
      have hmem : a₁ ∈ V₁ ⊓ V₂ := by
        refine ⟨ha₁V₁, ?_⟩
        rw [ha₁_eq]
        exact V₂.mul_mem haV₂ (V₂.inv_mem ha₂V₂)
      rw [seven_seven_c_mod_inf_V₁_V₂_eq_bot h hc] at hmem
      exact Subgroup.mem_bot.mp hmem
    have ha_eq : a = a₂ := by rw [← hfac', ha₁bot, one_mul]
    rw [ha_eq]
    exact ha₂
  · intro a ha
    obtain ⟨haA, haV₃⟩ := Subgroup.mem_inf.mp ha
    obtain ⟨a₁, ha₁, a₂, ha₂, a₃, ha₃, hfac⟩ := exists_commutator_factorization h hc hA a haA
    have ha₁V₁ : a₁ ∈ V₁ := (hmem₁ ha₁).2
    have ha₂V₂ : a₂ ∈ V₂ := (hmem₂ ha₂).2
    have ha₃V₃ : a₃ ∈ V₃ := (hmem₃ ha₃).2
    obtain ⟨v₁, hv₁V, hv₁I⟩ := seven_seven_c_mod_exists_mem_notMem_iSub h hc.mem₁
    have hx_eq : a₁ * a₂ = a * a₃⁻¹ := by rw [← hfac]; group
    have hxV₃ : a * a₃⁻¹ ∈ V₃ := V₃.mul_mem haV₃ (V₃.inv_mem ha₃V₃)
    have hv₁a₁ : v₁ * a₁ = a₁ * v₁ := seven_seven_c_mod_comm_of_mem h hc.mem₁ hv₁V ha₁V₁
    have hv₁a₂ : v₁ * a₂ = a₂ * v₁ := seven_seven_c_mod_comm_V₁_V₂ hc hv₁V ha₂V₂
    have hxcomm : (a₁ * a₂) * v₁ = v₁ * (a₁ * a₂) :=
      Commute.mul_left (show Commute a₁ v₁ from hv₁a₁.symm)
        (show Commute a₂ v₁ from hv₁a₂.symm)
    have hx1 : a * a₃⁻¹ = 1 := by
      by_contra hxne
      obtain ⟨g, hg, -, -⟩ := mem_omegaSet.mp hc.mem₃
      have hxcomm' : (a * a₃⁻¹) * v₁ = v₁ * (a * a₃⁻¹) := by
        rw [← hx_eq]
        exact hxcomm
      have hC : Subgroup.centralizer ({a * a₃⁻¹} : Set G) ≤
          Subgroup.normalizer (conjSubgroup V g : Set G) :=
        centralizer_le_normalizer_conj h.ti g
          (show a * a₃⁻¹ ∈ conjSubgroup V g from hg ▸ hxV₃) hxne
      have hvC : v₁ ∈ Subgroup.centralizer ({a * a₃⁻¹} : Set G) :=
        Subgroup.mem_centralizer_iff.mpr fun b hb => by
          rw [Set.mem_singleton_iff] at hb
          subst hb
          exact hxcomm'
      have hvN : v₁ ∈ Subgroup.normalizer (V₃ : Set G) := by
        rw [hg]
        exact hC hvC
      exact hv₁I (hc.norm₁₃ v₁ hv₁V hvN)
    have ha_eq : a = a₃ := by
      have : a = (a * a₃⁻¹) * a₃ := by group
      rw [this, hx1, one_mul]
    rw [ha_eq]
    exact ha₃

end Mod

end CFSG.LocalAnalysis.WeakClosure81
