module

public import CFSG.LocalAnalysis.GLTheoremB.Prop95I1921Perm

public section

namespace CFSG.Permutation.SylowTwoNormalizer

open Equiv Subgroup
open CFSG.LocalAnalysis.GLTheoremB.Prop95I1921 (eq_one_of_forall_commute)
open scoped commutatorElement

variable {r m : ℕ}

theorem isSimpleGroup_alternatingGroup_fin {k : ℕ} (h3 : 3 ≤ k) (h4 : k ≠ 4) :
    IsSimpleGroup ↥(alternatingGroup (Fin k)) := by
  rcases eq_or_lt_of_le h3 with h | h
  · subst h
    exact isSimpleGroup_of_prime_card (p := 3)
      (by rw [nat_card_alternatingGroup, Nat.card_fin]; decide)
  · exact alternatingGroup.isSimpleGroup (by rw [Nat.card_fin]; omega)

theorem mem_prod_commutator_iff_left {G N : Type*} [Group G] [Group N] {A : Subgroup G}
    (hA : ∀ a x : G, ⁅a, x⁆ ∈ A) (hZ : ∀ s : N, (∀ y : N, s * y = y * s) → s = 1) (g : G × N) :
    (∀ h : G × N, ⁅g, h⁆ ∈ A.prod (⊥ : Subgroup N)) ↔
      g ∈ (⊤ : Subgroup G).prod (⊥ : Subgroup N) := by
  constructor
  · intro h
    have h2 : g.2 = 1 := by
      refine hZ g.2 (fun y => ?_)
      have hy : ⁅g.2, y⁆ = 1 := by
        have hmem := (Subgroup.mem_prod.mp (h (1, y))).2
        simpa [commutatorElement_def, Subgroup.mem_bot] using hmem
      have hy' : g.2 * y * g.2⁻¹ * y⁻¹ = 1 := by simpa [commutatorElement_def] using hy
      calc g.2 * y = g.2 * y * g.2⁻¹ * y⁻¹ * (y * g.2) := by group
        _ = 1 * (y * g.2) := by rw [hy']
        _ = y * g.2 := one_mul _
    exact Subgroup.mem_prod.mpr ⟨Subgroup.mem_top _, by simp [h2]⟩
  · rintro hg h
    obtain ⟨-, hg2⟩ := Subgroup.mem_prod.mp hg
    have hg2' : g.2 = 1 := Subgroup.mem_bot.mp hg2
    have hval : ⁅g, h⁆ = (⁅g.1, h.1⁆, (1 : N)) := by
      rw [show g = (g.1, 1) from Prod.ext rfl hg2', commutatorElement_def]
      ext <;> simp [commutatorElement_def]
    rw [hval]
    exact Subgroup.mem_prod.mpr ⟨hA g.1 h.1, by simp⟩

theorem mem_prod_top_bot_iff (hm : 3 ≤ m) (g : Perm (Fin r) × Perm (Fin m)) :
    (∀ h : Perm (Fin r) × Perm (Fin m),
        ⁅g, h⁆ ∈ (alternatingGroup (Fin r)).prod (⊥ : Subgroup (Perm (Fin m)))) ↔
      g ∈ (⊤ : Subgroup (Perm (Fin r))).prod (⊥ : Subgroup (Perm (Fin m))) :=
  mem_prod_commutator_iff_left
    (fun a x => alternatingGroup.commutator_perm_le
      (Subgroup.commutator_mem_commutator (H₁ := ⊤) (H₂ := ⊤) (Subgroup.mem_top a)
        (Subgroup.mem_top x)))
    (fun s hs => eq_one_of_forall_commute (by rw [Fintype.card_fin]; exact hm) hs) g

theorem map_alt_prod_bot_eq_or (hr : 3 ≤ r) (hr4 : r ≠ 4) (hm : 3 ≤ m) (hm4 : m ≠ 4)
    (α : MulAut (Perm (Fin r) × Perm (Fin m))) :
    ((alternatingGroup (Fin r)).prod (⊥ : Subgroup (Perm (Fin m)))).map α.toMonoidHom =
        (alternatingGroup (Fin r)).prod ⊥ ∨
      ((alternatingGroup (Fin r)).prod (⊥ : Subgroup (Perm (Fin m)))).map α.toMonoidHom =
        (⊥ : Subgroup (Perm (Fin r))).prod (alternatingGroup (Fin m)) := by
  classical
  haveI hAr : IsSimpleGroup ↥(alternatingGroup (Fin r)) := isSimpleGroup_alternatingGroup_fin hr hr4
  haveI hAm : IsSimpleGroup ↥(alternatingGroup (Fin m)) := isSimpleGroup_alternatingGroup_fin hm hm4
  haveI hnr : Nontrivial (Fin r) := by
    rw [← Fintype.one_lt_card_iff_nontrivial, Fintype.card_fin]
    omega
  haveI hnm : Nontrivial (Fin m) := by
    rw [← Fintype.one_lt_card_iff_nontrivial, Fintype.card_fin]
    omega
  set N1 : Subgroup (Perm (Fin r) × Perm (Fin m)) :=
    (alternatingGroup (Fin r)).prod (⊥ : Subgroup (Perm (Fin m))) with hN1
  set F1 : Subgroup (Perm (Fin r) × Perm (Fin m)) :=
    (⊤ : Subgroup (Perm (Fin r))).prod (⊥ : Subgroup (Perm (Fin m))) with hF1
  set ψ : ↥(alternatingGroup (Fin r)) →* Perm (Fin m) :=
    (MonoidHom.snd _ _).comp
      (α.toMonoidHom.comp ((MonoidHom.inl _ _).comp (alternatingGroup (Fin r)).subtype)) with hψ
  have hψapply : ∀ a : ↥(alternatingGroup (Fin r)), ψ a = (α ((a : Perm (Fin r)), 1)).2 := by
    intro a; rw [hψ]; rfl
  have hNnormal : (N1.map α.toMonoidHom).Normal := by
    rw [hN1]
    exact (Subgroup.prod_normal (alternatingGroup (Fin r)) (⊥ : Subgroup (Perm (Fin m)))).map
      α.toMonoidHom α.surjective
  rcases Subgroup.Normal.eq_bot_or_eq_top ψ.ker with hbot | htop
  ·
    have hψinj : Function.Injective ψ := (MonoidHom.ker_eq_bot_iff ψ).mp hbot
    have hF1normal : F1.Normal := by
      rw [hF1]; exact Subgroup.prod_normal ⊤ ⊥
    have hdisj : N1.map α.toMonoidHom ⊓ F1 = ⊥ := by
      rw [eq_bot_iff]
      rintro x ⟨hxN, hxF⟩
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hxN
      obtain ⟨hy1, hy2⟩ := Subgroup.mem_prod.mp hy
      have hy2' : y.2 = 1 := Subgroup.mem_bot.mp hy2
      have hy_eq : y = ((y.1, 1) : Perm (Fin r) × Perm (Fin m)) := Prod.ext rfl hy2'
      have hx2 : (α y).2 = 1 := by
        have h := (Subgroup.mem_prod.mp hxF).2
        rwa [Subgroup.mem_bot] at h
      have hx2' : (α ((y.1, 1) : Perm (Fin r) × Perm (Fin m))).2 = 1 := by
        rw [← hy_eq]; exact hx2
      have hψy : ψ ⟨y.1, hy1⟩ = 1 := by
        rw [hψapply]
        show (α ((y.1, 1) : Perm (Fin r) × Perm (Fin m))).2 = 1
        exact hx2'
      have hy1' : y.1 = 1 := by
        have h1 : (⟨y.1, hy1⟩ : ↥(alternatingGroup (Fin r))) = 1 := by
          refine hψinj ?_
          rw [hψy, map_one]
        simpa using congrArg Subtype.val h1
      have hy1'' : y = 1 := by
        rw [hy_eq, hy1']
        rfl
      rw [hy1'', map_one]
      exact Subgroup.mem_bot.mpr rfl
    have hcomm : N1.map α.toMonoidHom ≤ (⊥ : Subgroup (Perm (Fin r))).prod ⊤ := by
      intro x hx
      have hxcomm : ∀ y ∈ F1, Commute x y := fun y hy =>
        Subgroup.commute_of_normal_of_disjoint _ _ hNnormal hF1normal (disjoint_iff.mpr hdisj)
          x y hx hy
      have hx1 : x.1 = 1 := by
        refine eq_one_of_forall_commute (by rw [Fintype.card_fin]; exact hr) (fun t => ?_)
        have h := hxcomm (t, 1) (Subgroup.mem_prod.mpr ⟨Subgroup.mem_top _, by simp⟩)
        simpa using congrArg Prod.fst h
      rw [Subgroup.mem_prod]
      exact ⟨by simpa using hx1, Subgroup.mem_top _⟩
    have hN_eq : N1.map α.toMonoidHom = (⊥ : Subgroup (Perm (Fin r))).prod ψ.range := by
      ext x
      constructor
      · intro hx
        obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
        obtain ⟨hy1, hy2⟩ := Subgroup.mem_prod.mp hy
        have hy2' : y.2 = 1 := Subgroup.mem_bot.mp hy2
        have hy_eq : y = ((y.1, 1) : Perm (Fin r) × Perm (Fin m)) := Prod.ext rfl hy2'
        rw [Subgroup.mem_prod]
        refine ⟨(Subgroup.mem_prod.mp (hcomm (Subgroup.mem_map.mpr ⟨y, hy, rfl⟩))).1, ?_⟩
        rw [MonoidHom.mem_range]
        refine ⟨⟨y.1, hy1⟩, ?_⟩
        rw [hψapply]
        show (α ((y.1, 1) : Perm (Fin r) × Perm (Fin m))).2 = (α y).2
        rw [hy_eq]
      · intro hx
        obtain ⟨hx1, hx2⟩ := Subgroup.mem_prod.mp hx
        have hx1' : x.1 = 1 := Subgroup.mem_bot.mp hx1
        obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp hx2
        have hmemN : α ((a : Perm (Fin r)), 1) ∈ N1.map α.toMonoidHom :=
          Subgroup.mem_map.mpr ⟨_, Subgroup.mem_prod.mpr ⟨a.2, by simp⟩, rfl⟩
        have hfirst : (α ((a : Perm (Fin r)), 1)).1 = 1 :=
          (Subgroup.mem_prod.mp (hcomm hmemN)).1
        refine Subgroup.mem_map.mpr ⟨((a : Perm (Fin r)), 1),
          Subgroup.mem_prod.mpr ⟨a.2, by simp⟩, ?_⟩
        rw [Prod.ext_iff]
        refine ⟨?_, ?_⟩
        · show (α ((a : Perm (Fin r)), 1)).1 = x.1
          rw [hfirst, hx1']
        · show (α ((a : Perm (Fin r)), 1)).2 = x.2
          rw [← hψapply a]
          exact ha
    have hM'normal : ψ.range.Normal := by
      refine Subgroup.Normal.mk (fun s hs g => ?_)
      have hNs : ((1, s) : Perm (Fin r) × Perm (Fin m)) ∈ N1.map α.toMonoidHom := by
        rw [hN_eq]; exact Subgroup.mem_prod.mpr ⟨by simp, hs⟩
      have hconj := hNnormal.conj_mem _ hNs (1, g)
      rw [hN_eq] at hconj
      have h2 := (Subgroup.mem_prod.mp hconj).2
      have heq : (((1, g) : Perm (Fin r) × Perm (Fin m)) * (1, s) * (1, g)⁻¹).2 = g * s * g⁻¹ := by
        simp
      rwa [heq] at h2
    have hM'simple : IsSimpleGroup ↥ψ.range := by
      have hbij : Function.Bijective (MonoidHom.rangeRestrict ψ) :=
        ⟨fun p q h => hψinj (Subtype.ext_iff.mp h), MonoidHom.rangeRestrict_surjective ψ⟩
      exact MulEquiv.isSimpleGroup (MulEquiv.ofBijective (MonoidHom.rangeRestrict ψ) hbij).symm
    have hM' : ψ.range = alternatingGroup (Fin m) := by
      haveI := hM'simple
      rcases eq_or_lt_of_le hm with hm3 | hm5
      · subst hm3
        have hbij : Function.Bijective (MonoidHom.rangeRestrict ψ) :=
          ⟨fun p q h => hψinj (Subtype.ext_iff.mp h), MonoidHom.rangeRestrict_surjective ψ⟩
        have hcard : Nat.card ↥ψ.range = Nat.card ↥(alternatingGroup (Fin r)) :=
          Nat.card_congr (MulEquiv.ofBijective (MonoidHom.rangeRestrict ψ) hbij).toEquiv.symm
        have hdvd : Nat.card ↥ψ.range ∣ 6 := by
          have h := Subgroup.card_subgroup_dvd_card ψ.range
          rwa [Nat.card_perm, Nat.card_fin, show Nat.factorial 3 = 6 from by decide] at h
        have hr3 : r = 3 := by
          by_contra hne
          have h5 : 5 ≤ r := by omega
          have h120 : 120 ≤ Nat.factorial r := by
            have h := Nat.factorial_le h5
            rwa [show Nat.factorial 5 = 120 from by decide] at h
          have hle6 : Nat.card ↥(alternatingGroup (Fin r)) ≤ 6 := by
            rw [← hcard]
            exact Nat.le_of_dvd (by norm_num) hdvd
          have hfac : Nat.card ↥(alternatingGroup (Fin r)) = Nat.factorial r / 2 := by
            rw [nat_card_alternatingGroup, Nat.card_fin]
          have h60 : 60 ≤ Nat.factorial r / 2 := by
            have h := Nat.div_le_div_right h120 (c := 2)
            simpa using h
          omega
        subst hr3
        have hcard3 : Nat.card ↥ψ.range = 3 := by
          rw [hcard, nat_card_alternatingGroup, Nat.card_fin]
          decide
        have hindex : ψ.range.index = 2 := by
          have h := Subgroup.index_mul_card ψ.range
          rw [hcard3, Nat.card_perm, Nat.card_fin,
            show Nat.factorial 3 = 6 from by decide] at h
          omega
        exact Equiv.Perm.eq_alternatingGroup_of_index_eq_two hindex
      · have h5 : 5 ≤ m := by omega
        haveI : ψ.range.Normal := hM'normal
        have hle : alternatingGroup (Fin m) ≤ ψ.range :=
          Equiv.Perm.alternatingGroup_le_of_normal (α := Fin m) (by rw [Nat.card_fin]; omega)
            inferInstance
        haveI hAmsub : ((alternatingGroup (Fin m)).subgroupOf ψ.range).Normal :=
          (inferInstance : (alternatingGroup (Fin m)).Normal).subgroupOf ψ.range
        rcases Subgroup.Normal.eq_bot_or_eq_top ((alternatingGroup (Fin m)).subgroupOf ψ.range)
          with hsub | hsub
        · exfalso
          obtain ⟨x, hx⟩ := exists_ne (1 : ↥(alternatingGroup (Fin m)))
          have hmem : (⟨x.1, hle x.2⟩ : ↥ψ.range) ∈ (alternatingGroup (Fin m)).subgroupOf ψ.range :=
            Subgroup.mem_subgroupOf.mpr x.2
          rw [hsub] at hmem
          have hx1 : (⟨x.1, hle x.2⟩ : ↥ψ.range) = 1 := Subgroup.mem_bot.mp hmem
          exact hx (Subtype.ext (by simpa using congrArg Subtype.val hx1))
        · refine le_antisymm ?_ hle
          intro y hy
          have hmem : (⟨y, hy⟩ : ↥ψ.range) ∈ (alternatingGroup (Fin m)).subgroupOf ψ.range := by
            rw [hsub]; exact Subgroup.mem_top _
          exact Subgroup.mem_subgroupOf.mp hmem
    refine Or.inr ?_
    rw [hN_eq, hM']
  ·
    have hsec : ∀ a : ↥(alternatingGroup (Fin r)), (α ((a : Perm (Fin r)), 1)).2 = 1 := by
      intro a
      rw [← hψapply a, ← MonoidHom.mem_ker, htop]
      exact Subgroup.mem_top a
    set ρ : ↥(alternatingGroup (Fin r)) →* Perm (Fin r) :=
      (MonoidHom.fst _ _).comp
        (α.toMonoidHom.comp ((MonoidHom.inl _ _).comp (alternatingGroup (Fin r)).subtype)) with hρ
    have hρapply : ∀ a, ρ a = (α ((a : Perm (Fin r)), 1)).1 := by intro a; rw [hρ]; rfl
    have hρinj : Function.Injective ρ := by
      intro a b hab
      have h1 : α ((a : Perm (Fin r)), 1) = α ((b : Perm (Fin r)), 1) := by
        refine Prod.ext_iff.mpr ⟨?_, ?_⟩
        · simpa [hρapply] using hab
        · rw [hsec a, hsec b]
      exact Subtype.ext (Prod.ext_iff.mp (α.injective h1)).1
    set M : Subgroup (Perm (Fin r)) := Subgroup.map ρ ⊤ with hM
    have hNfst : M = (N1.map α.toMonoidHom).map (MonoidHom.fst _ _) := by
      rw [hM, hN1]
      ext x
      constructor
      · rintro hx
        rw [Subgroup.mem_map] at hx
        obtain ⟨a, -, ha⟩ := hx
        refine Subgroup.mem_map.mpr ⟨α ((a : Perm (Fin r)), 1), ?_, ?_⟩
        · exact Subgroup.mem_map.mpr ⟨((a : Perm (Fin r)), 1),
            Subgroup.mem_prod.mpr ⟨a.2, by simp⟩, rfl⟩
        · show (α ((a : Perm (Fin r)), 1)).1 = x
          rw [← hρapply a]
          exact ha
      · rintro hx
        obtain ⟨z, hz, hzx⟩ := Subgroup.mem_map.mp hx
        obtain ⟨y, hy, hyz⟩ := Subgroup.mem_map.mp hz
        obtain ⟨hy1, hy2⟩ := Subgroup.mem_prod.mp hy
        have hy2' : y.2 = 1 := Subgroup.mem_bot.mp hy2
        rw [show y = ((y.1, 1) : Perm (Fin r) × Perm (Fin m)) from Prod.ext rfl hy2'] at hyz
        refine Subgroup.mem_map.mpr ⟨⟨y.1, hy1⟩, Subgroup.mem_top _, ?_⟩
        rw [hρapply]
        show (α (y.1, 1)).1 = x
        have hyz' : α (y.1, 1) = z := hyz
        rw [hyz']
        exact hzx
    have hMnormal : M.Normal := by
      rw [hNfst]
      exact hNnormal.map (MonoidHom.fst _ _) (fun a => ⟨(a, 1), rfl⟩)
    have hcardM : Nat.card ↥M = Nat.card ↥(alternatingGroup (Fin r)) := by
      rw [hM, Subgroup.card_map_of_injective (K := ⊤) hρinj, Subgroup.card_top]
    have hindex : M.index = 2 := by
      have h1 : M.index * Nat.card ↥M = Nat.card (Perm (Fin r)) := Subgroup.index_mul_card M
      have h3 : 2 * Nat.card ↥(alternatingGroup (Fin r)) = Nat.card (Perm (Fin r)) :=
        two_mul_nat_card_alternatingGroup
      have hpos : 0 < Nat.card ↥M := by rw [hcardM]; exact Nat.card_pos
      rw [← Nat.mul_right_cancel_iff hpos, h1, hcardM, h3]
    have hMA : M = alternatingGroup (Fin r) := Equiv.Perm.eq_alternatingGroup_of_index_eq_two hindex
    have hle : N1.map α.toMonoidHom ≤ N1 := by
      rintro x hx
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
      obtain ⟨hy1, hy2⟩ := Subgroup.mem_prod.mp hy
      have hy2' : y.2 = 1 := Subgroup.mem_bot.mp hy2
      rw [show y = (y.1, 1) from Prod.ext rfl hy2'] at hy1 ⊢
      refine Subgroup.mem_prod.mpr ⟨?_, hsec ⟨y.1, hy1⟩⟩
      rw [← hMA, hM]
      exact Subgroup.mem_map.mpr ⟨⟨y.1, hy1⟩, Subgroup.mem_top _, by simp [hρapply]⟩
    have hcard : Nat.card ↥(N1.map α.toMonoidHom) = Nat.card ↥N1 :=
      Subgroup.card_map_of_injective α.injective
    exact Or.inl (Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard.symm))

theorem map_alt_prod_bot_eq (hr : 3 ≤ r) (hr4 : r ≠ 4) (hm : 3 ≤ m) (hm4 : m ≠ 4)
    (α : MulAut (Perm (Fin r) × Perm (Fin m))) (hα : Odd (orderOf α)) :
    ((alternatingGroup (Fin r)).prod (⊥ : Subgroup (Perm (Fin m)))).map α.toMonoidHom =
      (alternatingGroup (Fin r)).prod (⊥ : Subgroup (Perm (Fin m))) := by
  classical
  set N1 : Subgroup (Perm (Fin r) × Perm (Fin m)) :=
    (alternatingGroup (Fin r)).prod (⊥ : Subgroup (Perm (Fin m))) with hN1
  set N2 : Subgroup (Perm (Fin r) × Perm (Fin m)) :=
    (⊥ : Subgroup (Perm (Fin r))).prod (alternatingGroup (Fin m)) with hN2
  haveI hntAr : Nontrivial ↥(alternatingGroup (Fin r)) :=
    alternatingGroup.nontrivial_of_three_le_card (by rw [Nat.card_fin]; exact hr)
  have hne : N1 ≠ N2 := by
    intro h
    obtain ⟨a, ha⟩ := exists_ne (1 : ↥(alternatingGroup (Fin r)))
    have hmem : ((a : Perm (Fin r)), 1) ∈ N1 := by
      rw [hN1]; exact Subgroup.mem_prod.mpr ⟨a.2, by simp⟩
    rw [h] at hmem
    have h1 : (a : Perm (Fin r)) = 1 := Subgroup.mem_bot.mp (Subgroup.mem_prod.mp hmem).1
    exact ha (Subtype.ext h1)
  obtain ⟨t, ht⟩ := hα
  set β : MulAut (Perm (Fin r) × Perm (Fin m)) := α ^ (t + 1) with hβdef
  have hβ : β * β = α := by
    rw [hβdef, ← pow_add]
    have h2 : t + 1 + (t + 1) = orderOf α + 1 := by omega
    rw [h2, pow_succ, pow_orderOf_eq_one, one_mul]
  have hstep : N1.map α.toMonoidHom = (N1.map β.toMonoidHom).map β.toMonoidHom := by
    rw [← hβ]
    rw [show (β * β).toMonoidHom = β.toMonoidHom.comp β.toMonoidHom from rfl]
    rw [← Subgroup.map_map]
  rcases map_alt_prod_bot_eq_or hr hr4 hm hm4 β with h | h
  · rw [← hN1] at h
    rw [hstep, h, h]
  · rw [← hN1, ← hN2] at h
    have hcomp_id : β.toMonoidHom.comp β.symm.toMonoidHom = MonoidHom.id _ :=
      MonoidHom.ext (fun x => β.apply_symm_apply x)
    have hβinv : N1.map β.symm.toMonoidHom = N2 := by
      rcases map_alt_prod_bot_eq_or hr hr4 hm hm4 β.symm with h' | h'
      · exfalso
        have h2 : (N1.map β.symm.toMonoidHom).map β.toMonoidHom = N1 := by
          rw [Subgroup.map_map, hcomp_id]
          exact Subgroup.map_id N1
        rw [h'] at h2
        exact hne (h2.symm.trans h)
      · exact h'
    have hN2 : N2.map β.toMonoidHom = N1 := by
      have h2 : (N1.map β.symm.toMonoidHom).map β.toMonoidHom = N1 := by
        rw [Subgroup.map_map, hcomp_id]
        exact Subgroup.map_id N1
      rwa [hβinv] at h2
    rw [hstep, h, hN2]

theorem centralizer_prod_top_bot (hr : 3 ≤ r) :
    Subgroup.centralizer ((⊤ : Subgroup (Perm (Fin r))).prod (⊥ : Subgroup (Perm (Fin m))) :
      Set (Perm (Fin r) × Perm (Fin m))) =
      (⊥ : Subgroup (Perm (Fin r))).prod (⊤ : Subgroup (Perm (Fin m))) := by
  ext x
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_prod]
  constructor
  · intro h
    have hx1 : x.1 = 1 := by
      refine eq_one_of_forall_commute (by rw [Fintype.card_fin]; exact hr) (fun t => ?_)
      have hmem : ((t, 1) : Perm (Fin r) × Perm (Fin m)) ∈
          ((⊤ : Subgroup (Perm (Fin r))).prod (⊥ : Subgroup (Perm (Fin m))) :
            Set (Perm (Fin r) × Perm (Fin m))) :=
        Subgroup.mem_prod.mpr ⟨Subgroup.mem_top _, by simp⟩
      simpa using (congrArg Prod.fst (h (t, 1) hmem)).symm
    exact ⟨by simp [hx1], Subgroup.mem_top _⟩
  · rintro ⟨hx1, -⟩ y hy
    have hy2 : y.2 = 1 := Subgroup.mem_bot.mp (Subgroup.mem_prod.mp hy).2
    have hx1' : x.1 = 1 := Subgroup.mem_bot.mp hx1
    rw [Prod.ext_iff]
    exact ⟨by simp [hx1'], by simp [hy2]⟩

theorem map_centralizer_mulAut {G : Type*} [Group G] (α : MulAut G) (s : Set G) :
    (Subgroup.centralizer s).map α.toMonoidHom = Subgroup.centralizer (α '' s) := by
  refine le_antisymm (Subgroup.map_centralizer_le_centralizer_image s α.toMonoidHom) ?_
  intro x hx
  rw [Subgroup.mem_map]
  refine ⟨α.symm x, ?_, α.apply_symm_apply x⟩
  rw [Subgroup.mem_centralizer_iff] at hx ⊢
  intro y hy
  have h := hx (α y) (Set.mem_image_of_mem (⇑α) hy)
  apply α.injective
  simp only [map_mul, MulEquiv.apply_symm_apply]
  exact h

theorem map_prod_top_bot_le_of_map_alt (hm : 3 ≤ m)
    (α : MulAut (Perm (Fin r) × Perm (Fin m)))
    (hN1 : ((alternatingGroup (Fin r)).prod (⊥ : Subgroup (Perm (Fin m)))).map α.toMonoidHom =
      (alternatingGroup (Fin r)).prod (⊥ : Subgroup (Perm (Fin m)))) :
    ((⊤ : Subgroup (Perm (Fin r))).prod (⊥ : Subgroup (Perm (Fin m)))).map α.toMonoidHom ≤
      (⊤ : Subgroup (Perm (Fin r))).prod (⊥ : Subgroup (Perm (Fin m))) := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
  refine (mem_prod_top_bot_iff hm (α x)).mp (fun h => ?_)
  have h1 : ⁅x, α.symm h⁆ ∈ (alternatingGroup (Fin r)).prod (⊥ : Subgroup (Perm (Fin m))) :=
    (mem_prod_top_bot_iff hm x).mpr hx (α.symm h)
  have h2 : α ⁅x, α.symm h⁆ ∈
      ((alternatingGroup (Fin r)).prod (⊥ : Subgroup (Perm (Fin m)))).map α.toMonoidHom :=
    Subgroup.mem_map.mpr ⟨_, h1, rfl⟩
  rw [hN1] at h2
  rwa [show α ⁅x, α.symm h⁆ = ⁅α x, h⁆ from by simp [commutatorElement_def]] at h2

theorem map_prod_top_bot_eq_of_three_le (hr : 3 ≤ r) (hr4 : r ≠ 4) (hm : 3 ≤ m) (hm4 : m ≠ 4)
    (α : MulAut (Perm (Fin r) × Perm (Fin m))) (hα : Odd (orderOf α)) :
    ((⊤ : Subgroup (Perm (Fin r))).prod (⊥ : Subgroup (Perm (Fin m)))).map α.toMonoidHom =
      (⊤ : Subgroup (Perm (Fin r))).prod (⊥ : Subgroup (Perm (Fin m))) := by
  have hN1 := map_alt_prod_bot_eq hr hr4 hm hm4 α hα
  have hle := map_prod_top_bot_le_of_map_alt hm α hN1
  have hN1inv : ((alternatingGroup (Fin r)).prod (⊥ : Subgroup (Perm (Fin m)))).map
        α.symm.toMonoidHom =
      (alternatingGroup (Fin r)).prod (⊥ : Subgroup (Perm (Fin m))) := by
    calc ((alternatingGroup (Fin r)).prod (⊥ : Subgroup (Perm (Fin m)))).map α.symm.toMonoidHom
        = (((alternatingGroup (Fin r)).prod (⊥ : Subgroup (Perm (Fin m)))).map
            α.toMonoidHom).map α.symm.toMonoidHom := by rw [hN1]
      _ = ((alternatingGroup (Fin r)).prod (⊥ : Subgroup (Perm (Fin m)))).map
            (α.symm.toMonoidHom.comp α.toMonoidHom) := by rw [Subgroup.map_map]
      _ = (alternatingGroup (Fin r)).prod (⊥ : Subgroup (Perm (Fin m))) := by
            rw [show α.symm.toMonoidHom.comp α.toMonoidHom = MonoidHom.id _ from
              MonoidHom.ext (fun x => α.symm_apply_apply x), Subgroup.map_id]
  have hle' := map_prod_top_bot_le_of_map_alt hm α.symm hN1inv
  refine le_antisymm hle (fun x hx => ?_)
  exact Subgroup.mem_map.mpr ⟨α.symm x, hle' (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩), by simp⟩

theorem map_prod_bot_top_eq_of_three_le (hr : 3 ≤ r) (hr4 : r ≠ 4) (hm : 3 ≤ m) (hm4 : m ≠ 4)
    (α : MulAut (Perm (Fin r) × Perm (Fin m))) (hα : Odd (orderOf α)) :
    ((⊥ : Subgroup (Perm (Fin r))).prod (⊤ : Subgroup (Perm (Fin m)))).map α.toMonoidHom =
      (⊥ : Subgroup (Perm (Fin r))).prod (⊤ : Subgroup (Perm (Fin m))) := by
  have hF1 := map_prod_top_bot_eq_of_three_le hr hr4 hm hm4 α hα
  have hcent := centralizer_prod_top_bot (r := r) (m := m) hr
  have hset : (⇑α) '' ((⊤ : Subgroup (Perm (Fin r))).prod (⊥ : Subgroup (Perm (Fin m))) :
      Set (Perm (Fin r) × Perm (Fin m))) =
      ((⊤ : Subgroup (Perm (Fin r))).prod (⊥ : Subgroup (Perm (Fin m))) :
        Set (Perm (Fin r) × Perm (Fin m))) := by
    have h' := congrArg (fun H : Subgroup (Perm (Fin r) × Perm (Fin m)) =>
      (↑H : Set (Perm (Fin r) × Perm (Fin m)))) hF1
    simpa using h'
  calc ((⊥ : Subgroup (Perm (Fin r))).prod (⊤ : Subgroup (Perm (Fin m)))).map α.toMonoidHom
      = (Subgroup.centralizer ((⊤ : Subgroup (Perm (Fin r))).prod
          (⊥ : Subgroup (Perm (Fin m))) : Set (Perm (Fin r) × Perm (Fin m)))).map
          α.toMonoidHom := by rw [hcent]
    _ = Subgroup.centralizer (⇑α '' ((⊤ : Subgroup (Perm (Fin r))).prod
          (⊥ : Subgroup (Perm (Fin m))) : Set (Perm (Fin r) × Perm (Fin m)))) :=
          map_centralizer_mulAut α _
    _ = Subgroup.centralizer ((⊤ : Subgroup (Perm (Fin r))).prod
          (⊥ : Subgroup (Perm (Fin m))) : Set (Perm (Fin r) × Perm (Fin m))) := by rw [hset]
    _ = (⊥ : Subgroup (Perm (Fin r))).prod (⊤ : Subgroup (Perm (Fin m))) := hcent

theorem subsingleton_perm_fin {k : ℕ} (hk : k ≤ 1) : Subsingleton (Perm (Fin k)) := by
  rw [← Fintype.card_le_one_iff_subsingleton, Fintype.card_perm, Fintype.card_fin,
    Nat.factorial_eq_one.mpr hk]

theorem map_prod_top_bot_eq (hr2 : r ≠ 2) (hr4 : r ≠ 4) (hm2 : m ≠ 2) (hm4 : m ≠ 4)
    (α : MulAut (Perm (Fin r) × Perm (Fin m))) (hα : Odd (orderOf α)) :
    ((⊤ : Subgroup (Perm (Fin r))).prod (⊥ : Subgroup (Perm (Fin m)))).map α.toMonoidHom =
      (⊤ : Subgroup (Perm (Fin r))).prod (⊥ : Subgroup (Perm (Fin m))) := by
  by_cases hr : r ≤ 1
  ·
    haveI : Subsingleton (Perm (Fin r)) := subsingleton_perm_fin hr
    have hbot : (⊤ : Subgroup (Perm (Fin r))) = ⊥ := Subsingleton.elim _ _
    have hF1 : ((⊤ : Subgroup (Perm (Fin r))).prod (⊥ : Subgroup (Perm (Fin m)))) = ⊥ := by
      rw [hbot, Subgroup.bot_prod_bot]
    rw [hF1, Subgroup.map_bot]
  by_cases hm : m ≤ 1
  ·
    haveI : Subsingleton (Perm (Fin m)) := subsingleton_perm_fin hm
    have htop : (⊥ : Subgroup (Perm (Fin m))) = ⊤ := Subsingleton.elim _ _
    have hF1 : ((⊤ : Subgroup (Perm (Fin r))).prod (⊥ : Subgroup (Perm (Fin m)))) = ⊤ := by
      rw [htop]
      exact Subgroup.ext (fun x => by simp)
    rw [hF1, Subgroup.map_top, MonoidHom.range_eq_top.mpr α.surjective]
  exact map_prod_top_bot_eq_of_three_le (by omega) hr4 (by omega) hm4 α hα

theorem map_prod_bot_top_eq (hr2 : r ≠ 2) (hr4 : r ≠ 4) (hm2 : m ≠ 2) (hm4 : m ≠ 4)
    (α : MulAut (Perm (Fin r) × Perm (Fin m))) (hα : Odd (orderOf α)) :
    ((⊥ : Subgroup (Perm (Fin r))).prod (⊤ : Subgroup (Perm (Fin m)))).map α.toMonoidHom =
      (⊥ : Subgroup (Perm (Fin r))).prod (⊤ : Subgroup (Perm (Fin m))) := by
  by_cases hr : r ≤ 1
  ·
    haveI : Subsingleton (Perm (Fin r)) := subsingleton_perm_fin hr
    have htop : (⊥ : Subgroup (Perm (Fin r))) = ⊤ := Subsingleton.elim _ _
    have hF2 : ((⊥ : Subgroup (Perm (Fin r))).prod (⊤ : Subgroup (Perm (Fin m)))) = ⊤ := by
      rw [htop]
      exact Subgroup.ext (fun x => by simp)
    rw [hF2, Subgroup.map_top, MonoidHom.range_eq_top.mpr α.surjective]
  by_cases hm : m ≤ 1
  ·
    haveI : Subsingleton (Perm (Fin m)) := subsingleton_perm_fin hm
    have hbot : (⊤ : Subgroup (Perm (Fin m))) = ⊥ := Subsingleton.elim _ _
    have hF2 : ((⊥ : Subgroup (Perm (Fin r))).prod (⊤ : Subgroup (Perm (Fin m)))) = ⊥ := by
      rw [hbot, Subgroup.bot_prod_bot]
    rw [hF2, Subgroup.map_bot]
  exact map_prod_bot_top_eq_of_three_le (by omega) hr4 (by omega) hm4 α hα

theorem exists_mulAut_eq_prod (hr2 : r ≠ 2) (hr4 : r ≠ 4) (hm2 : m ≠ 2) (hm4 : m ≠ 4)
    (α : MulAut (Perm (Fin r) × Perm (Fin m))) (hα : Odd (orderOf α)) :
    ∃ (α₁ : MulAut (Perm (Fin r))) (α₂ : MulAut (Perm (Fin m))),
      (∀ x y, α (x, y) = (α₁ x, α₂ y)) ∧ orderOf α₁ ∣ orderOf α ∧ orderOf α₂ ∣ orderOf α := by
  classical
  have hF1 := map_prod_top_bot_eq hr2 hr4 hm2 hm4 α hα
  have hF2 := map_prod_bot_top_eq hr2 hr4 hm2 hm4 α hα
  have hsec : ∀ x : Perm (Fin r), (α (x, 1)).2 = 1 := by
    intro x
    have hmem : α (x, 1) ∈ ((⊤ : Subgroup (Perm (Fin r))).prod
        (⊥ : Subgroup (Perm (Fin m)))) := by
      rw [← hF1]
      exact Subgroup.mem_map.mpr ⟨(x, 1), Subgroup.mem_prod.mpr ⟨Subgroup.mem_top _, by simp⟩, rfl⟩
    exact Subgroup.mem_bot.mp (Subgroup.mem_prod.mp hmem).2
  have hfst : ∀ y : Perm (Fin m), (α (1, y)).1 = 1 := by
    intro y
    have hmem : α (1, y) ∈ ((⊥ : Subgroup (Perm (Fin r))).prod
        (⊤ : Subgroup (Perm (Fin m)))) := by
      rw [← hF2]
      exact Subgroup.mem_map.mpr ⟨(1, y), Subgroup.mem_prod.mpr ⟨by simp, Subgroup.mem_top _⟩, rfl⟩
    exact Subgroup.mem_bot.mp (Subgroup.mem_prod.mp hmem).1
  set φ₁ : Perm (Fin r) →* Perm (Fin r) :=
    (MonoidHom.fst _ _).comp (α.toMonoidHom.comp (MonoidHom.inl _ _)) with hφ₁
  set φ₂ : Perm (Fin m) →* Perm (Fin m) :=
    (MonoidHom.snd _ _).comp (α.toMonoidHom.comp (MonoidHom.inr _ _)) with hφ₂
  have hφ₁apply : ∀ x, φ₁ x = (α (x, 1)).1 := by intro x; rw [hφ₁]; rfl
  have hφ₂apply : ∀ y, φ₂ y = (α (1, y)).2 := by intro y; rw [hφ₂]; rfl
  have hφ₁inj : Function.Injective φ₁ := by
    intro x y hxy
    have h1 : α (x, 1) = α (y, 1) := by
      rw [Prod.ext_iff]
      exact ⟨by rw [← hφ₁apply, ← hφ₁apply]; exact hxy, by rw [hsec x, hsec y]⟩
    exact (Prod.ext_iff.mp (α.injective h1)).1
  have hφ₂inj : Function.Injective φ₂ := by
    intro x y hxy
    have h1 : α (1, x) = α (1, y) := by
      rw [Prod.ext_iff]
      exact ⟨by rw [hfst x, hfst y], by rw [← hφ₂apply, ← hφ₂apply]; exact hxy⟩
    exact (Prod.ext_iff.mp (α.injective h1)).2
  set α₁ : MulAut (Perm (Fin r)) :=
    MulEquiv.ofBijective φ₁ ⟨hφ₁inj, Finite.surjective_of_injective hφ₁inj⟩ with hα₁
  set α₂ : MulAut (Perm (Fin m)) :=
    MulEquiv.ofBijective φ₂ ⟨hφ₂inj, Finite.surjective_of_injective hφ₂inj⟩ with hα₂
  have hα₁apply : ∀ x, α₁ x = (α (x, 1)).1 := by
    intro x; rw [hα₁]; exact hφ₁apply x
  have hα₂apply : ∀ y, α₂ y = (α (1, y)).2 := by
    intro y; rw [hα₂]; exact hφ₂apply y
  have hdecomp : ∀ x y, α (x, y) = (α₁ x, α₂ y) := by
    intro x y
    have hx1 : α (x, 1) = (α₁ x, 1) := Prod.ext (hα₁apply x).symm (hsec x)
    have hy1 : α (1, y) = (1, α₂ y) := Prod.ext (hfst y) (hα₂apply y).symm
    have hxy : ((x, 1) * (1, y) : Perm (Fin r) × Perm (Fin m)) = (x, y) := by simp
    calc α (x, y) = α ((x, 1) * (1, y)) := by rw [hxy]
      _ = α (x, 1) * α (1, y) := map_mul α (x, 1) (1, y)
      _ = (α₁ x, α₂ y) := by rw [hx1, hy1]; rfl
  have hpow : ∀ (k : ℕ) (x : Perm (Fin r)) (y : Perm (Fin m)),
      (α ^ k) (x, y) = ((α₁ ^ k) x, (α₂ ^ k) y) := by
    intro k
    induction k with
    | zero => intro x y; simp
    | succ k ih =>
        intro x y
        rw [pow_succ']
        show α ((α ^ k) (x, y)) = _
        rw [ih x y, hdecomp, pow_succ', pow_succ']
        rfl
  refine ⟨α₁, α₂, hdecomp, ?_, ?_⟩
  · have h1 : α₁ ^ orderOf α = 1 := by
      refine MulEquiv.ext (fun x => ?_)
      have h := hpow (orderOf α) x 1
      rw [pow_orderOf_eq_one] at h
      simpa using (congrArg Prod.fst h).symm
    exact orderOf_dvd_iff_pow_eq_one.mpr h1
  · have h1 : α₂ ^ orderOf α = 1 := by
      refine MulEquiv.ext (fun y => ?_)
      have h := hpow (orderOf α) 1 y
      rw [pow_orderOf_eq_one] at h
      simpa using (congrArg Prod.snd h).symm
    exact orderOf_dvd_iff_pow_eq_one.mpr h1

end CFSG.Permutation.SylowTwoNormalizer
