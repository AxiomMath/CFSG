module

public import CFSG.LocalAnalysis.StandardType.GGLevTwoS2aCase

public section

namespace CFSG.StandardType.LevTwo

open CFSG.LieType.RootSystem CFSG.LieType.Universal.SpecialLinear
open scoped Matrix

theorem levTwoS2a_comp_swap_gen (n : ℕ) {i j c d : Fin (n+1)} (_hij : i ≠ j) :
    (Pi.single c 1 - Pi.single d 1 : Fin (n+1) → ℤ) ∘ (Equiv.swap i j) =
      (Pi.single (Equiv.swap i j c) 1 - Pi.single (Equiv.swap i j d) 1 :
        Fin (n+1) → ℤ) := by
  funext k
  simp only [Function.comp_apply, Pi.sub_apply, Pi.single_apply,
    Equiv.apply_eq_iff_eq_symm_apply]
  rfl

theorem levTwoS2a_Wapply_eps_swap (n : ℕ) (hn : 1 ≤ n) {α x : Fin n → ℤ}
    {i j c d : Fin (n+1)} (hαrt : IsRt (isFiniteType_A n) α) (hij : i ≠ j)
    (hαc : toStd n α = Pi.single i 1 - Pi.single j 1)
    (hxc : toStd n x = Pi.single c 1 - Pi.single d 1) :
    toStd n (weylAction (isFiniteType_A n) (rRefl (isFiniteType_A n) α) x) =
      Pi.single (Equiv.swap i j c) 1 - Pi.single (Equiv.swap i j d) 1 := by
  rw [levTwoS2a_rRefl_coord n hn hαrt hij hαc, hxc, levTwoS2a_comp_swap_gen n hij]

theorem levTwoS2a_classA_of_not_mem_Phi (n : ℕ) (hn : 1 ≤ n) (p : ℕ) (hp : p.Prime)
    (hp2 : p ≠ 2) (c : Fin n → ZMod p) (Φ : Set (Fin n → ℤ))
    (h : LevTwoData (isFiniteType_A n) p c Φ) {a B : Fin (n+1)}
    (hcomp : ∀ k : Fin (n+1), levTwoS2a_D n p c k = levTwoS2a_D n p c B ∨ k = a)
    {β : Fin n → ℤ} (hβrt : IsRt (isFiniteType_A n) β) (hβ : β ∉ Φ) :
    levTwoS2a_classA n p c B a β := by
  obtain ⟨u, v, huv, hcu⟩ := (levTwoS2a_isRt_iff_coord n hn β).mp hβrt
  have hDuv : levTwoS2a_D n p c u ≠ levTwoS2a_D n p c v := by
    intro hh
    apply hβ
    rw [levTwoS2a_Phi_fibre n hn p hp hp2 c Φ h]
    exact ⟨u, v, huv, hcu, hh⟩
  rcases hcomp u with hu | hu
  · rcases hcomp v with hv | hv
    · exact absurd (hu.trans hv.symm) hDuv
    · left
      refine ⟨u, hu, ?_⟩
      rw [hv] at hcu; exact hcu
  · rcases hcomp v with hv | hv
    · right
      refine ⟨v, hv, ?_⟩
      rw [hu] at hcu; exact hcu
    · exact absurd (by rw [hu, hv]) hDuv

theorem levTwoS2a_tcRoot_allRoots (n : ℕ) (hn : 1 ≤ n) (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (c : Fin n → ZMod p) (Φ : Set (Fin n → ℤ))
    (h : LevTwoData (isFiniteType_A n) p c Φ) {B : Fin (n+1)}
    (hcomp : ∀ k : Fin (n+1), levTwoS2a_D n p c k = levTwoS2a_D n p c B) :
    TCRoot (isFiniteType_A n) Φ := by
  intro S hS
  refine ⟨∅, by simp, by simp, ?_⟩
  rw [Finset.coe_empty]
  apply levTwoS2b_cl_eq_of_subset (isFiniteType_A n) (S' := (∅ : Set (Fin n → ℤ)))
    (by simp)
  intro β hβ
  refine Cl.base (Or.inl ?_)
  rw [levTwoS2a_Phi_fibre n hn p hp hp2 c Φ h]
  obtain ⟨u, v, huv, hcu⟩ := (levTwoS2a_isRt_iff_coord n hn β).mp (hS β hβ)
  exact ⟨u, v, huv, hcu, (hcomp u).trans (hcomp v).symm⟩

theorem levTwoS2a_tcRoot_oneComp (n : ℕ) (hn : 1 ≤ n) (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (c : Fin n → ZMod p) (Φ : Set (Fin n → ℤ))
    (h : LevTwoData (isFiniteType_A n) p c Φ) {a B : Fin (n+1)}
    (haD : levTwoS2a_D n p c a ≠ levTwoS2a_D n p c B)
    (hcomp : ∀ k : Fin (n+1), levTwoS2a_D n p c k = levTwoS2a_D n p c B ∨ k = a) :
    TCRoot (isFiniteType_A n) Φ := by
  intro S hS
  by_cases hSout : ∃ x ∈ S, x ∉ Φ
  · obtain ⟨x, hxS, hxΦ⟩ := hSout
    refine ⟨{x}, ?_, by simp, ?_⟩
    · intro y hy
      rw [Finset.mem_coe, Finset.mem_singleton] at hy
      rw [hy]; exact hxS
    · rw [Finset.coe_singleton]
      apply levTwoS2b_cl_eq_of_subset (isFiniteType_A n)
        (S' := ({x} : Set (Fin n → ℤ)))
      · intro y hy
        rw [Set.mem_singleton_iff] at hy
        rw [hy]; exact hxS
      · intro β hβ
        by_cases hβΦ : β ∈ Φ
        · exact Cl.base (Or.inl hβΦ)
        · exact levTwoS2a_Cl_classA n hn p hp hp2 c Φ h haD
            (levTwoS2a_classA_of_not_mem_Phi n hn p hp hp2 c Φ h hcomp (hS x hxS) hxΦ)
            (levTwoS2a_classA_of_not_mem_Phi n hn p hp hp2 c Φ h hcomp (hS β hβ) hβΦ)
  · refine ⟨∅, by simp, by simp, ?_⟩
    rw [Finset.coe_empty]
    apply levTwoS2b_cl_eq_of_subset (isFiniteType_A n) (S' := (∅ : Set (Fin n → ℤ)))
      (by simp)
    intro β hβ
    refine Cl.base (Or.inl ?_)
    by_contra hb
    exact hSout ⟨β, hβ, hb⟩

theorem levTwoS2a_Wapply_eps_ab (n : ℕ) (hn : 1 ≤ n) {i a b : Fin (n+1)}
    (hia : i ≠ a) (hib : i ≠ b) (hab : a ≠ b) :
    weylAction (isFiniteType_A n) (rRefl (isFiniteType_A n) (levTwoS2a_eps n i a))
      (levTwoS2a_eps n i b) = levTwoS2a_eps n a b := by
  apply toStd_injective n
  rw [levTwoS2a_Wapply_eps_swap n hn
      ((levTwoS2a_isRt_iff_coord n hn _).mpr ⟨i, a, hia, levTwoS2a_toStd_eps n i a⟩) hia
      (levTwoS2a_toStd_eps n i a) (levTwoS2a_toStd_eps n i b),
    levTwoS2a_toStd_eps]
  simp only [Equiv.swap_apply_def]
  split_ifs <;> simp_all [Fin.ext_iff]

theorem levTwoS2a_class_or_ab (n : ℕ) (hn : 1 ≤ n) (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (c : Fin n → ZMod p) (Φ : Set (Fin n → ℤ))
    (h : LevTwoData (isFiniteType_A n) p c Φ) {a b B : Fin (n+1)} (_hab : a ≠ b)
    (hcomp : ∀ k : Fin (n+1), levTwoS2a_D n p c k = levTwoS2a_D n p c B ∨ k = a ∨ k = b)
    {β : Fin n → ℤ} (hβrt : IsRt (isFiniteType_A n) β) (hβ : β ∉ Φ) :
    levTwoS2a_classA n p c B a β ∨ levTwoS2a_classA n p c B b β ∨
      (toStd n β = Pi.single a 1 - Pi.single b 1 ∨
        toStd n β = Pi.single b 1 - Pi.single a 1) := by
  obtain ⟨u, v, huv, hcu⟩ := (levTwoS2a_isRt_iff_coord n hn β).mp hβrt
  have hDuv : levTwoS2a_D n p c u ≠ levTwoS2a_D n p c v := by
    intro hh
    apply hβ
    rw [levTwoS2a_Phi_fibre n hn p hp hp2 c Φ h]
    exact ⟨u, v, huv, hcu, hh⟩
  rcases hcomp u with hu | hu | hu <;> rcases hcomp v with hv | hv | hv
  · exact absurd (hu.trans hv.symm) hDuv
  · left; left; refine ⟨u, hu, ?_⟩; rw [hv] at hcu; exact hcu
  · right; left; left; refine ⟨u, hu, ?_⟩; rw [hv] at hcu; exact hcu
  · left; right; refine ⟨v, hv, ?_⟩; rw [hu] at hcu; exact hcu
  · exact absurd (by rw [hu, hv]) hDuv
  · right; right; left; rw [hu, hv] at hcu; exact hcu
  · right; left; right; refine ⟨v, hv, ?_⟩; rw [hu] at hcu; exact hcu
  · right; right; right; rw [hu, hv] at hcu; exact hcu
  · exact absurd (by rw [hu, hv]) hDuv

theorem levTwoS2a_Cl_classAB_of_classes (n : ℕ) (hn : 1 ≤ n) (p : ℕ) (hp : p.Prime)
    (hp2 : p ≠ 2) (c : Fin n → ZMod p) (Φ : Set (Fin n → ℤ))
    (h : LevTwoData (isFiniteType_A n) p c Φ) {a b B : Fin (n+1)} {x y : Fin n → ℤ}
    (haD : levTwoS2a_D n p c a ≠ levTwoS2a_D n p c B)
    (hbD : levTwoS2a_D n p c b ≠ levTwoS2a_D n p c B) (hab : a ≠ b)
    (hxa : levTwoS2a_classA n p c B a x) (hyb : levTwoS2a_classA n p c B b y)
    {β : Fin n → ℤ} (hβab : toStd n β = Pi.single a 1 - Pi.single b 1 ∨
      toStd n β = Pi.single b 1 - Pi.single a 1) :
    Cl (isFiniteType_A n) (Φ ∪ ({x} ∪ {y} : Set (Fin n → ℤ))) β := by
  have ha_of : ∀ {k : Fin (n+1)}, levTwoS2a_D n p c k = levTwoS2a_D n p c B → a ≠ k :=
    fun hk hh => haD (hh.symm ▸ hk)
  have hb_of : ∀ {k : Fin (n+1)}, levTwoS2a_D n p c k = levTwoS2a_D n p c B → b ≠ k :=
    fun hk hh => hbD (hh.symm ▸ hk)
  have hkey : ∃ i : Fin (n+1), levTwoS2a_D n p c i = levTwoS2a_D n p c B := by
    rcases hxa with ⟨i, hiB, hxi⟩ | ⟨i, hiB, hxi⟩
    · exact ⟨i, hiB⟩
    · exact ⟨i, hiB⟩
  obtain ⟨i, hiB⟩ := hkey
  have hai : a ≠ i := ha_of hiB
  have hbi : b ≠ i := hb_of hiB
  have hCia0 : Cl (isFiniteType_A n) (Φ ∪ ({x} : Set (Fin n → ℤ))) (levTwoS2a_eps n i a) :=
    levTwoS2a_Cl_classA n hn p hp hp2 c Φ h haD hxa (Or.inl ⟨i, hiB, levTwoS2a_toStd_eps n i a⟩)
  have hCib0 : Cl (isFiniteType_A n) (Φ ∪ ({y} : Set (Fin n → ℤ))) (levTwoS2a_eps n i b) :=
    levTwoS2a_Cl_classA n hn p hp hp2 c Φ h hbD hyb (Or.inl ⟨i, hiB, levTwoS2a_toStd_eps n i b⟩)
  have hsubx : Φ ∪ ({x} : Set (Fin n → ℤ)) ⊆ Φ ∪ ({x} ∪ {y} : Set (Fin n → ℤ)) :=
    Set.union_subset_union (Set.Subset.refl Φ) Set.subset_union_left
  have hsuby : Φ ∪ ({y} : Set (Fin n → ℤ)) ⊆ Φ ∪ ({x} ∪ {y} : Set (Fin n → ℤ)) :=
    Set.union_subset_union (Set.Subset.refl Φ) Set.subset_union_right
  have hCia := levTwoS2b_cl_mono (isFiniteType_A n) hsubx hCia0
  have hCib := levTwoS2b_cl_mono (isFiniteType_A n) hsuby hCib0
  have hCab : Cl (isFiniteType_A n) (Φ ∪ ({x} ∪ {y} : Set (Fin n → ℤ)))
      (levTwoS2a_eps n a b) := by
    have hh := Cl.refl hCia hCib
    rwa [levTwoS2a_Wapply_eps_ab n hn hai.symm hbi.symm hab] at hh
  rcases hβab with hβab | hβab
  · have hβeq : β = levTwoS2a_eps n a b :=
      toStd_injective n (by rw [hβab, levTwoS2a_toStd_eps])
    rw [hβeq]; exact hCab
  · have hrt : IsRt (isFiniteType_A n) (levTwoS2a_eps n a b) :=
      (levTwoS2a_isRt_iff_coord n hn _).mpr ⟨a, b, hab, levTwoS2a_toStd_eps n a b⟩
    have hflip := Cl.refl hCab hCab
    rw [levTwoS2a_weylAction_rRefl_self n hn hrt] at hflip
    have hβeq : β = -levTwoS2a_eps n a b := by
      apply toStd_injective
      rw [toStd_neg, hβab, levTwoS2a_toStd_eps]
      simp
    rw [hβeq]; exact hflip

theorem levTwoS2a_Cl_classAB_of_one (n : ℕ) (hn : 1 ≤ n) {a b : Fin (n+1)} (hab : a ≠ b)
    (Φ : Set (Fin n → ℤ)) {T : Set (Fin n → ℤ)} {x β : Fin n → ℤ} (hxT : x ∈ T)
    (hxab : toStd n x = Pi.single a 1 - Pi.single b 1 ∨
      toStd n x = Pi.single b 1 - Pi.single a 1)
    (hβab : toStd n β = Pi.single a 1 - Pi.single b 1 ∨
      toStd n β = Pi.single b 1 - Pi.single a 1) :
    Cl (isFiniteType_A n) (Φ ∪ T) β := by
  have hxcl : Cl (isFiniteType_A n) (Φ ∪ T) x := Cl.base (Or.inr hxT)
  have hxrt : IsRt (isFiniteType_A n) x :=
    (levTwoS2a_isRt_iff_coord n hn x).mpr (by
      rcases hxab with hx | hx
      · exact ⟨a, b, hab, hx⟩
      · exact ⟨b, a, hab.symm, hx⟩)
  have hflip : Cl (isFiniteType_A n) (Φ ∪ T) (weylAction (isFiniteType_A n)
      (rRefl (isFiniteType_A n) x) x) := Cl.refl hxcl hxcl
  rw [levTwoS2a_weylAction_rRefl_self n hn hxrt] at hflip
  rcases hxab with hx | hx <;> rcases hβab with hβ | hβ
  · have : β = x := toStd_injective n (by rw [hβ, hx])
    rw [this]; exact hxcl
  · have hxeq : x = levTwoS2a_eps n a b :=
      toStd_injective n (by rw [hx, levTwoS2a_toStd_eps])
    have hβeq : β = -levTwoS2a_eps n a b := by
      apply toStd_injective
      rw [toStd_neg, hβ, levTwoS2a_toStd_eps, neg_sub]
    rw [hβeq, ← hxeq]; exact hflip
  · have hxeq : x = levTwoS2a_eps n b a :=
      toStd_injective n (by rw [hx, levTwoS2a_toStd_eps])
    have hβeq : β = -levTwoS2a_eps n b a := by
      apply toStd_injective
      rw [toStd_neg, hβ, levTwoS2a_toStd_eps, neg_sub]
    rw [hβeq, ← hxeq]; exact hflip
  · have : β = x := toStd_injective n (by rw [hβ, hx])
    rw [this]; exact hxcl

theorem levTwoS2a_tcRoot_twoComp (n : ℕ) (hn : 1 ≤ n) (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (c : Fin n → ZMod p) (Φ : Set (Fin n → ℤ))
    (h : LevTwoData (isFiniteType_A n) p c Φ) {a b B : Fin (n+1)}
    (haD : levTwoS2a_D n p c a ≠ levTwoS2a_D n p c B)
    (hbD : levTwoS2a_D n p c b ≠ levTwoS2a_D n p c B) (hab : a ≠ b)
    (hcomp : ∀ k : Fin (n+1), levTwoS2a_D n p c k = levTwoS2a_D n p c B ∨ k = a ∨ k = b) :
    TCRoot (isFiniteType_A n) Φ := by
  intro S hS
  have key : ∀ β ∈ S, β ∈ Φ ∨ levTwoS2a_classA n p c B a β ∨ levTwoS2a_classA n p c B b β ∨
      (toStd n β = Pi.single a 1 - Pi.single b 1 ∨
        toStd n β = Pi.single b 1 - Pi.single a 1) := by
    intro β hβ
    by_cases hβΦ : β ∈ Φ
    · exact Or.inl hβΦ
    · rcases levTwoS2a_class_or_ab n hn p hp hp2 c Φ h hab hcomp (hS β hβ) hβΦ with h1 | h2 | h3
      · exact Or.inr (Or.inl h1)
      · exact Or.inr (Or.inr (Or.inl h2))
      · exact Or.inr (Or.inr (Or.inr h3))
  by_cases hSa : ∃ x ∈ S, levTwoS2a_classA n p c B a x
  · obtain ⟨xa, hxaS, hxaa⟩ := hSa
    by_cases hSb : ∃ x ∈ S, levTwoS2a_classA n p c B b x
    · obtain ⟨xb, hxbS, hxbb⟩ := hSb
      let T : Finset (Fin n → ℤ) := {xa, xb}
      have hsub : (T : Set (Fin n → ℤ)) ⊆ S := by
        intro y hy
        rw [Finset.mem_coe] at hy
        simp only [T, Finset.mem_insert, Finset.mem_singleton] at hy
        rcases hy with rfl | rfl <;> assumption
      refine ⟨T, hsub, ?_, ?_⟩
      · show ({xa, xb} : Finset (Fin n → ℤ)).card ≤ 2
        exact le_trans (Finset.card_insert_le xa ({xb} : Finset (Fin n → ℤ))) (by simp)
      · apply levTwoS2b_cl_eq_of_subset (isFiniteType_A n) (S' := (T : Set (Fin n → ℤ))) hsub
        intro β hβ
        have hsubxa : Φ ∪ ({xa} : Set (Fin n → ℤ)) ⊆ Φ ∪ (T : Set (Fin n → ℤ)) :=
          Set.union_subset_union (Set.Subset.refl Φ)
            (by intro z hz; rw [hz]
                exact Finset.mem_coe.mpr (by simp [T]))
        have hsubxb : Φ ∪ ({xb} : Set (Fin n → ℤ)) ⊆ Φ ∪ (T : Set (Fin n → ℤ)) :=
          Set.union_subset_union (Set.Subset.refl Φ)
            (by intro z hz; rw [hz]
                exact Finset.mem_coe.mpr (by simp [T]))
        rcases key β hβ with hΦ | ha | hb | hab'
        · exact Cl.base (Or.inl hΦ)
        · exact levTwoS2b_cl_mono (isFiniteType_A n) hsubxa
            (levTwoS2a_Cl_classA n hn p hp hp2 c Φ h haD hxaa ha)
        · exact levTwoS2b_cl_mono (isFiniteType_A n) hsubxb
            (levTwoS2a_Cl_classA n hn p hp hp2 c Φ h hbD hxbb hb)
        · exact levTwoS2b_cl_mono (isFiniteType_A n)
            (by
              intro z hz
              rcases hz with hz | hz
              · exact Or.inl hz
              · simp only [Set.mem_union, Set.mem_singleton_iff] at hz
                rcases hz with rfl | rfl <;> exact Or.inr (Finset.mem_coe.mpr (by simp [T])))
            (levTwoS2a_Cl_classAB_of_classes n hn p hp hp2 c Φ h haD hbD hab hxaa hxbb hab')
    · by_cases hSab : ∃ x ∈ S, (toStd n x = Pi.single a 1 - Pi.single b 1 ∨
          toStd n x = Pi.single b 1 - Pi.single a 1)
      · obtain ⟨xab, hxabS, hxabab⟩ := hSab
        let T : Finset (Fin n → ℤ) := {xa, xab}
        have hsub : (T : Set (Fin n → ℤ)) ⊆ S := by
          intro y hy
          rw [Finset.mem_coe] at hy
          simp only [T, Finset.mem_insert, Finset.mem_singleton] at hy
          rcases hy with rfl | rfl <;> assumption
        refine ⟨T, hsub, ?_, ?_⟩
        · show ({xa, xab} : Finset (Fin n → ℤ)).card ≤ 2
          exact le_trans (Finset.card_insert_le xa ({xab} : Finset (Fin n → ℤ))) (by simp)
        · apply levTwoS2b_cl_eq_of_subset (isFiniteType_A n) (S' := (T : Set (Fin n → ℤ))) hsub
          intro β hβ
          have hsubxa : Φ ∪ ({xa} : Set (Fin n → ℤ)) ⊆ Φ ∪ (T : Set (Fin n → ℤ)) :=
            Set.union_subset_union (Set.Subset.refl Φ)
              (by rintro z rfl; exact Finset.mem_coe.mpr (by simp [T]))
          rcases key β hβ with hΦ | ha | hb | hab'
          · exact Cl.base (Or.inl hΦ)
          · exact levTwoS2b_cl_mono (isFiniteType_A n) hsubxa
              (levTwoS2a_Cl_classA n hn p hp hp2 c Φ h haD hxaa ha)
          · exact absurd ⟨β, hβ, hb⟩ hSb
          · exact levTwoS2a_Cl_classAB_of_one n hn hab Φ (T := (T : Set (Fin n → ℤ)))
              (Finset.mem_coe.mpr (by simp [T]))
              hxabab hab'
      · let T : Finset (Fin n → ℤ) := {xa}
        have hsub : (T : Set (Fin n → ℤ)) ⊆ S := by
          intro y hy
          rw [Finset.mem_coe] at hy
          simp only [T, Finset.mem_singleton] at hy
          rw [hy]; exact hxaS
        refine ⟨T, hsub, ?_, ?_⟩
        · show ({xa} : Finset (Fin n → ℤ)).card ≤ 2; simp
        · apply levTwoS2b_cl_eq_of_subset (isFiniteType_A n) (S' := (T : Set (Fin n → ℤ))) hsub
          intro β hβ
          rcases key β hβ with hΦ | ha | hb | hab'
          · exact Cl.base (Or.inl hΦ)
          · exact levTwoS2b_cl_mono (isFiniteType_A n)
              (by
                intro z hz
                rcases hz with hz | hz
                · exact Or.inl hz
                · simp only [Set.mem_singleton_iff] at hz; rw [hz]
                  exact Or.inr (Finset.mem_coe.mpr (by simp [T])))
              (levTwoS2a_Cl_classA n hn p hp hp2 c Φ h haD hxaa ha)
          · exact absurd ⟨β, hβ, hb⟩ hSb
          · exact absurd ⟨β, hβ, hab'⟩ hSab
  · by_cases hSb : ∃ x ∈ S, levTwoS2a_classA n p c B b x
    · obtain ⟨xb, hxbS, hxbb⟩ := hSb
      by_cases hSab : ∃ x ∈ S, (toStd n x = Pi.single a 1 - Pi.single b 1 ∨
            toStd n x = Pi.single b 1 - Pi.single a 1)
      · obtain ⟨xab, hxabS, hxabab⟩ := hSab
        let T : Finset (Fin n → ℤ) := {xb, xab}
        have hsub : (T : Set (Fin n → ℤ)) ⊆ S := by
          intro y hy
          rw [Finset.mem_coe] at hy
          simp only [T, Finset.mem_insert, Finset.mem_singleton] at hy
          rcases hy with rfl | rfl <;> assumption
        refine ⟨T, hsub, ?_, ?_⟩
        · show ({xb, xab} : Finset (Fin n → ℤ)).card ≤ 2
          exact le_trans (Finset.card_insert_le xb ({xab} : Finset (Fin n → ℤ))) (by simp)
        · apply levTwoS2b_cl_eq_of_subset (isFiniteType_A n) (S' := (T : Set (Fin n → ℤ))) hsub
          intro β hβ
          have hsubxb : Φ ∪ ({xb} : Set (Fin n → ℤ)) ⊆ Φ ∪ (T : Set (Fin n → ℤ)) :=
            Set.union_subset_union (Set.Subset.refl Φ)
              (by rintro z rfl; exact Finset.mem_coe.mpr (by simp [T]))
          rcases key β hβ with hΦ | ha | hb | hab'
          · exact Cl.base (Or.inl hΦ)
          · exact absurd ⟨β, hβ, ha⟩ hSa
          · exact levTwoS2b_cl_mono (isFiniteType_A n) hsubxb
              (levTwoS2a_Cl_classA n hn p hp hp2 c Φ h hbD hxbb hb)
          · exact levTwoS2a_Cl_classAB_of_one n hn hab Φ (T := (T : Set (Fin n → ℤ)))
              (Finset.mem_coe.mpr (by simp [T]))
              hxabab hab'
      · let T : Finset (Fin n → ℤ) := {xb}
        have hsub : (T : Set (Fin n → ℤ)) ⊆ S := by
          intro y hy
          rw [Finset.mem_coe] at hy
          simp only [T, Finset.mem_singleton] at hy
          rw [hy]; exact hxbS
        refine ⟨T, hsub, ?_, ?_⟩
        · show ({xb} : Finset (Fin n → ℤ)).card ≤ 2; simp
        · apply levTwoS2b_cl_eq_of_subset (isFiniteType_A n) (S' := (T : Set (Fin n → ℤ))) hsub
          intro β hβ
          rcases key β hβ with hΦ | ha | hb | hab'
          · exact Cl.base (Or.inl hΦ)
          · exact absurd ⟨β, hβ, ha⟩ hSa
          · exact levTwoS2b_cl_mono (isFiniteType_A n)
              (by
                intro z hz
                rcases hz with hz | hz
                · exact Or.inl hz
                · simp only [Set.mem_singleton_iff] at hz; rw [hz]
                  exact Or.inr (Finset.mem_coe.mpr (by simp [T])))
              (levTwoS2a_Cl_classA n hn p hp hp2 c Φ h hbD hxbb hb)
          · exact absurd ⟨β, hβ, hab'⟩ hSab
    · by_cases hSab : ∃ x ∈ S, (toStd n x = Pi.single a 1 - Pi.single b 1 ∨
          toStd n x = Pi.single b 1 - Pi.single a 1)
      · obtain ⟨xab, hxabS, hxabab⟩ := hSab
        let T : Finset (Fin n → ℤ) := {xab}
        have hsub : (T : Set (Fin n → ℤ)) ⊆ S := by
          intro y hy
          rw [Finset.mem_coe] at hy
          simp only [T, Finset.mem_singleton] at hy
          rw [hy]; exact hxabS
        refine ⟨T, hsub, ?_, ?_⟩
        · show ({xab} : Finset (Fin n → ℤ)).card ≤ 2; simp
        · apply levTwoS2b_cl_eq_of_subset (isFiniteType_A n) (S' := (T : Set (Fin n → ℤ))) hsub
          intro β hβ
          rcases key β hβ with hΦ | ha | hb | hab'
          · exact Cl.base (Or.inl hΦ)
          · exact absurd ⟨β, hβ, ha⟩ hSa
          · exact absurd ⟨β, hβ, hb⟩ hSb
          · exact levTwoS2a_Cl_classAB_of_one n hn hab Φ (T := (T : Set (Fin n → ℤ)))
              (Finset.mem_coe.mpr (by simp [T]))
              hxabab hab'
      · have hsub : (↑(∅ : Finset (Fin n → ℤ)) : Set (Fin n → ℤ)) ⊆ S := by simp
        refine ⟨∅, hsub, by simp, ?_⟩
        apply levTwoS2b_cl_eq_of_subset (isFiniteType_A n)
          (S' := (↑(∅ : Finset (Fin n → ℤ)) : Set (Fin n → ℤ))) hsub
        intro β hβ
        rcases key β hβ with hΦ | ha | hb | hab'
        · exact Cl.base (Or.inl hΦ)
        · exact absurd ⟨β, hβ, ha⟩ hSa
        · exact absurd ⟨β, hβ, hb⟩ hSb
        · exact absurd ⟨β, hβ, hab'⟩ hSab

end CFSG.StandardType.LevTwo
