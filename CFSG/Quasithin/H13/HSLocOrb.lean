module

public import CFSG.Quasithin.H13.HSLocLists
public import CFSG.Quasithin.H13.HSLocBase

public section

namespace CFSG.Quasithin.H13.LocDbl.HSLoc

open CFSG.QuasithinUnique.K1.SporadicPerm hiding img keyNat
open CFSG.Quasithin.H13.LocDbl.DcNative CFSG.Quasithin.H13.LocDbl.DcRank CFSG.Quasithin.H13.LocDbl.Dc
open CFSG.RankThree.Native

theorem F0_lt : ∀ f ∈ F0, f < 100 := by decide

section Generic

variable {Γ : Type} [Group Γ] [MulAction Γ (Fin 100)] [FaithfulSMul Γ (Fin 100)]

@[expose] def Pres (g : Γ) : Prop := ∀ f ∈ F0, act 100 g f ∈ F0

theorem Pres.one : Pres (1 : Γ) := fun f hf => by rw [act_one (F0_lt f hf)]; exact hf

theorem Pres.mul {g h : Γ} (hg : Pres g) (hh : Pres h) : Pres (g * h) := fun f hf => by
  rw [act_mul _ _ (F0_lt f hf)]
  exact hg _ (hh f hf)

theorem Pres.inv {g : Γ} (hg : Pres g) : Pres g⁻¹ := by
  classical
  let S : Finset ℕ := F0.toFinset
  have hS : ∀ x, x ∈ S ↔ x ∈ F0 := fun x => List.mem_toFinset
  have hinj : Set.InjOn (act 100 g) (S : Set ℕ) := by
    intro a ha b hb hab
    rw [Finset.mem_coe, hS] at ha hb
    have := congrArg (act 100 g⁻¹) hab
    rwa [← act_mul _ _ (F0_lt a ha), ← act_mul _ _ (F0_lt b hb), inv_mul_cancel,
      act_one (F0_lt a ha), act_one (F0_lt b hb)] at this
  have himg : S.image (act 100 g) ⊆ S := by
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    rw [hS] at ha ⊢
    exact hg a ha
  have heq : S.image (act 100 g) = S :=
    Finset.eq_of_subset_of_card_le himg (by rw [Finset.card_image_of_injOn hinj])
  intro f hf
  have hfS : f ∈ S.image (act 100 g) := by rw [heq, hS]; exact hf
  obtain ⟨a, ha, hafe⟩ := Finset.mem_image.mp hfS
  have haF := (hS a).mp ha
  rw [← hafe, ← act_mul _ _ (F0_lt a haF), inv_mul_cancel, act_one (F0_lt a haF)]
  exact haF

end Generic

@[expose] def Hs : Subgroup PG where
  carrier := {g | Pres g}
  one_mem' := Pres.one
  mul_mem' := Pres.mul
  inv_mem' := Pres.inv


@[expose] noncomputable def treeElt (k : ℕ) : PG := enumElt [ga, gb, ga⁻¹, gb⁻¹] treeF.1 treeF.2 k

theorem AB_hG : ∀ t < AB.size, ∀ p < 100,
    img (AB.getD t #[]) p = act 100 ([ga, gb, ga⁻¹, gb⁻¹].getD t 1) p := fun t ht p hp =>
  ABOK_ab t (by simpa [AB] using ht) p hp

theorem tree_enumOK : enumOK 3850 AB treeF.1 treeF.2 = true := by
  obtain ⟨-, htree, -⟩ := Certificates.certificate589206
  simp only [treeOK, Bool.and_eq_true] at htree
  exact htree.1

theorem orbF_nodup : orbF.Nodup := by
  obtain ⟨-, htree, -⟩ := Certificates.certificate589206
  simp only [treeOK, Bool.and_eq_true, decide_eq_true_eq] at htree
  exact htree.2

theorem treeElems_getD {k : ℕ} (hk : k < 3850) : treeElems.getD k #[] = T (treeElt k) :=
  enumTabs_getD AB_hG tree_enumOK hk

theorem orbRows_getD (N : ℕ) (PA : List (Array ℕ)) {k : ℕ} (hk : k < N) :
    (orbRows N PA).getD k [] = maskOf (PA.map fun A => A.getD k 0) := by
  unfold orbRows
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk]
  rfl

theorem orb_key {k : ℕ} (hk : k < 3850) :
    (F0.map (ptsArr AB treeF.1 treeF.2 3850)).map (fun A => A.getD k 0) =
      F0.map (act 100 (treeElt k)) := by
  rw [List.map_map]
  apply List.map_congr_left
  intro f hf
  have := (ptsArr_spec AB [ga, gb, ga⁻¹, gb⁻¹] treeF.1 treeF.2 3850 f (F0_lt f hf) AB_hG
    tree_enumOK).2 k hk
  rw [Function.comp_apply]
  unfold treeElt
  rw [← this]

theorem orbRows_length (N : ℕ) (PA : List (Array ℕ)) : (orbRows N PA).length = N := by
  simp [orbRows]

theorem orbF_getD {k : ℕ} (hk : k < 3850) :
    orbF.getD k [] = maskOf (F0.map (act 100 (treeElt k))) :=
  (orbRows_getD 3850 _ hk).trans (congrArg maskOf (orb_key hk))

theorem orbF_inj {k l : ℕ} (hk : k < 3850) (hl : l < 3850) (h : orbF.getD k [] = orbF.getD l []) :
    k = l := by
  have hlen : orbF.length = 3850 := orbRows_length _ _
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (by omega : k < orbF.length),
    List.getElem?_eq_getElem (by omega : l < orbF.length), Option.getD_some, Option.getD_some] at h
  exact (orbF_nodup.getElem_inj_iff).mp h

theorem treeElt_inv_mul_mem {k l : ℕ} (hk : k < 3850) (hl : l < 3850)
    (h : (treeElt k)⁻¹ * treeElt l ∈ Hs) : k = l := by
  apply orbF_inj hk hl
  rw [orbF_getD hk, orbF_getD hl]
  apply maskOf_eq_of_mem_iff
  intro x hx
  have hh : Pres ((treeElt k)⁻¹ * treeElt l) := h
  have hh' : Pres ((treeElt l)⁻¹ * treeElt k) := by
    have := Pres.inv hh
    rwa [mul_inv_rev, inv_inv] at this
  simp only [List.mem_map]
  constructor
  · rintro ⟨f, hf, rfl⟩
    refine ⟨act 100 (treeElt l)⁻¹ (act 100 (treeElt k) f), ?_, ?_⟩
    · have := hh' f hf
      rwa [act_mul _ _ (F0_lt f hf)] at this
    · rw [← act_mul _ _ (act_lt _ (F0_lt f hf)), mul_inv_cancel, act_one (act_lt _ (F0_lt f hf))]
  · rintro ⟨f, hf, rfl⟩
    refine ⟨act 100 (treeElt k)⁻¹ (act 100 (treeElt l) f), ?_, ?_⟩
    · have := hh f hf
      rwa [act_mul _ _ (F0_lt f hf)] at this
    · rw [← act_mul _ _ (act_lt _ (F0_lt f hf)), mul_inv_cancel, act_one (act_lt _ (F0_lt f hf))]

theorem Hs_card_le : Nat.card Hs ≤ 11520 := by
  classical
  have hinj : Function.Injective fun k : Fin 3850 => (QuotientGroup.mk (treeElt k) : PG ⧸ Hs) := by
    intro k l hkl
    have := QuotientGroup.eq.mp hkl
    exact Fin.ext (treeElt_inv_mul_mem k.2 l.2 this)
  have hcard : 3850 ≤ Nat.card (PG ⧸ Hs) := by
    have := Nat.card_le_card_of_injective _ hinj
    simpa using this
  have hmul := Hs.card_mul_index
  rw [Subgroup.index_eq_card, show Nat.card PG = 44352000 from card_hs100P] at hmul
  nlinarith [Nat.card_pos (α := ↥Hs)]

theorem gen_mem_mTabs {g : PG} (hg : g ∈ gensOf mWords) : T g ∈ mTabs := by
  unfold gensOf at hg
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hg
  rw [T_wAB (mWords_lt w hw)]
  unfold mTabs tabsOf
  rw [List.mem_toArray]
  exact List.mem_map_of_mem hw

theorem mPres_gen {g : PG} (hg : g ∈ gensOf mWords) :
    Pres g ∧ ((act 100 g 0 = 0 ∧ act 100 g 1 = 1) ∨ (act 100 g 0 = 1 ∧ act 100 g 1 = 0)) := by
  obtain ⟨-, -, hmp, -⟩ := Certificates.certificate589206
  simp only [mPres, Array.all_eq_true', Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true,
    beq_iff_eq, List.contains_iff_mem] at hmp
  obtain ⟨h1, h2⟩ := hmp _ (gen_mem_mTabs hg)
  simp only [img_T] at h1 h2
  exact ⟨h1, h2⟩

theorem Mg_le_Hs : Mg ≤ Hs := by
  rw [Mg, Subgroup.closure_le]
  intro g hg
  exact (mPres_gen hg).1

theorem Mg_eq_Hs : Mg = Hs :=
  Subgroup.eq_of_le_of_card_ge Mg_le_Hs (by rw [mSpec.card]; exact Hs_card_le)

theorem mem_Mg_iff {g : PG} : g ∈ Mg ↔ Pres g := by
  rw [Mg_eq_Hs]; exact Iff.rfl

end CFSG.Quasithin.H13.LocDbl.HSLoc
