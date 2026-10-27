module

public import CFSG.Monster.GMS.Fi23LocalBasic
public import CFSG.Monster.GMS.Facts.BabyFi22
public import CFSG.Blueprint.FischerDefs

public section

namespace CFSG.Monster.GMS.Fi23Local

open CFSG.Blueprint.NativeSporadic
open CFSG.Blueprint.Fischer (LocalClass)

section Star

variable {G : Type} [Group G] [Finite G] {d₀ : B} {a z₀ : G}

theorem mem_twoANbr_of_mem_localClass
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀)
    {b x : G} (hb : IsConj a b) (hx : IsConj a x) (hbx : orderOf (b * x) = 3) {d f : G}
    (hd : d ∈ twoANbr a b ∩ twoANbr a x)
    (hf : f ∈ LocalClass (twoANbr a b ∩ twoANbr a x) d) : f ∈ twoANbr a d :=
  ⟨hf.1.1.1, by
    rw [← hf.2.2]
    exact commute_mem_twoANbr I hG hb hx hbx hd hf.1 hf.2.1 hf.2.2⟩

omit [Finite G] in
theorem mem_centralizer_of_mem_localClass {D : Set G} {d f : G} (hf : f ∈ LocalClass D d) :
    f ∈ Subgroup.centralizer ({d} : Set G) :=
  Subgroup.mem_centralizer_singleton_iff.mpr hf.2.2

theorem mem_tableVISet_of_mem_localClass
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀)
    {b x : G} (hb : IsConj a b) (hx : IsConj a x) (hbx : orderOf (b * x) = 3) {d f y : G}
    (hy : y = b ∨ y = x) (hd : d ∈ twoANbr a b ∩ twoANbr a x)
    (hf : f ∈ LocalClass (twoANbr a b ∩ twoANbr a x) d) : f ∈ tableVISet a y d := by
  obtain ⟨b₀, z, u, h⟩ := exists_twoClasses I.sls I.tableV I.leech hG
  have hncomm : b * x ≠ x * b := not_comm_of_orderOf_eq_three hbx
    (mul_self_eq_one_of_isConj_a h hb) (mul_self_eq_one_of_isConj_a h hx)
  have hfH := mem_inf_of_mem h hb hx hf.1
  have hdH := mem_inf_of_mem h hb hx hd
  have hdd := mul_self_eq_one_of_isConj_a h hd.1.1
  refine ⟨mem_twoANbr_of_mem_localClass I hG hb hx hbx hd hf, ?_, ?_⟩
  · rintro rfl
    exact false_of_mem_inf hncomm hy hfH
  · intro e
    have e' : f * d = y := by rw [e, mul_assoc, hdd, mul_one]
    have hH := Subgroup.mul_mem _ hfH hdH
    rw [e'] at hH
    exact false_of_mem_inf hncomm hy hH

theorem babyInv_of_mem_localClass
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀) {b x : G}
    (hb : IsConj a b) (hx : IsConj a x) (hbx : orderOf (b * x) = 3) {d f y : G}
    (hy : y = b ∨ y = x) (hd : d ∈ twoANbr a b ∩ twoANbr a x)
    {φ : Subgroup.centralizer ({d} : Set G) →* B} (hφ : IsBabyCover d φ)
    (hf : f ∈ LocalClass (twoANbr a b ∩ twoANbr a x) d) :
    BabyInv 0 (coverMap φ f) ∧ BabyInv 1 (coverMap φ y * coverMap φ f) := by
  obtain ⟨b₀, z, u, h⟩ := exists_twoClasses I.sls I.tableV I.leech hG
  have hyA : IsConj a y := by
    rcases hy with rfl | rfl
    · exact hb
    · exact hx
  have hdy : d ∈ twoANbr a y := by
    rcases hy with rfl | rfl
    · exact hd.1
    · exact hd.2
  have C : TableVICtx a z₀ b₀ z u y d φ := ⟨h, I.tableIII, I.tableIVBaby, hyA, hdy, hφ⟩
  have hc := mem_tableVISet_of_mem_localClass I hG hb hx hbx hy hd hf
  obtain ⟨-, hf0, -⟩ := C.mem_tableVISet_iff.mp hc
  have hyf : IsConj a (y * f) := by
    rcases hy with rfl | rfl
    · exact hf.1.1.2
    · exact hf.1.2.2
  exact ⟨hf0, C.cond_to_orbit hc (K := .two_A) hyf⟩

theorem babyInv_zero_of_mem_twoANbr
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀) {d y : G}
    (hd : IsConj a d) {φ : Subgroup.centralizer ({d} : Set G) →* B} (hφ : IsBabyCover d φ)
    (hy : y ∈ twoANbr a d) : BabyInv 0 (coverMap φ y) := by
  obtain ⟨b₀, z, u, h⟩ := exists_twoClasses I.sls I.tableV I.leech hG
  exact ((h.mem_twoANbr_iff I.tableIII hd hφ).mp hy).2

theorem coverMap_injOn
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀) {b x : G}
    (hb : IsConj a b) (hx : IsConj a x) (hbx : orderOf (b * x) = 3) {d : G}
    (hd : d ∈ twoANbr a b ∩ twoANbr a x) {φ : Subgroup.centralizer ({d} : Set G) →* B}
    (hφ : IsBabyCover d φ) {f f' : G} (hf : f ∈ LocalClass (twoANbr a b ∩ twoANbr a x) d)
    (hf' : f' ∈ LocalClass (twoANbr a b ∩ twoANbr a x) d)
    (he : coverMap φ f = coverMap φ f') : f = f' := by
  obtain ⟨b₀, z, u, h⟩ := exists_twoClasses I.sls I.tableV I.leech hG
  have hfC := mem_centralizer_of_mem_localClass hf
  have hf'C := mem_centralizer_of_mem_localClass hf'
  have hbd : b * d = d * b := comm_of_mem_twoANbr h hb hd.1
  have hbC : b ∈ Subgroup.centralizer ({d} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hbd
  rcases (hφ.coverMap_eq_iff hfC hf'C).mp he with e | e
  · exact e.symm
  exfalso
  obtain ⟨-, hW⟩ := babyInv_of_mem_localClass I hG hb hx hbx (Or.inl rfl) hd hφ hf
  have h1 : BabyInv 1 (coverMap φ (b * f)) := by rw [coverMap_mul hbC hfC]; exact hW
  obtain ⟨-, hcase⟩ := h.babyInv_one_cases I.tableIII hd.1.1 hφ (Subgroup.mul_mem _ hbC hfC) h1
  have hbf : IsConj a (b * f) := hf.1.1.2
  have hbf' : IsConj a (d * (b * f)) := by
    have : b * f' = d * (b * f) := by
      rw [e, ← mul_assoc, hbd, mul_assoc]
    rw [← this]
    exact hf'.1.1.2
  rcases hcase with ⟨h2, -⟩ | ⟨-, h2⟩
  · exact h.not_isConj (hbf.trans h2.symm)
  · exact h.not_isConj (hbf'.trans h2.symm)

omit [Finite G] in
theorem isConj_mul_of_isConj_mul {b x f : G} (hbb : b * b = 1) (hxx : x * x = 1)
    (hbx : orderOf (b * x) = 3) (hfb : f * b = b * f) (hfx : f * x = x * f) {a : G}
    (h : IsConj a (b * f)) : IsConj a (x * f) := by
  have h3 : b * x * (b * x) * (b * x) = 1 := by
    have := pow_orderOf_eq_one (b * x)
    rw [hbx, pow_three'] at this
    exact this
  have key : b * x * b * x * b = x := by
    calc b * x * b * x * b = (b * x * (b * x) * (b * x)) * x⁻¹ := by group
      _ = x⁻¹ := by rw [h3, one_mul]
      _ = x := inv_eq_of_mul_eq_one_right hxx
  have hinv : (b * x)⁻¹ = x * b := by
    rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hxx, inv_eq_of_mul_eq_one_right hbb]
  have e : (b * x) * (b * f) * (b * x)⁻¹ = x * f := by
    rw [hinv]
    calc b * x * (b * f) * (x * b) = b * x * b * (f * x) * b := by group
      _ = b * x * b * (x * f) * b := by rw [hfx]
      _ = b * x * b * x * (f * b) := by group
      _ = b * x * b * x * (b * f) := by rw [hfb]
      _ = (b * x * b * x * b) * f := by group
      _ = x * f := by rw [key]
  rw [← e]
  exact h.trans (isConj_conj_self _ _)

theorem exists_mem_localClass_of_mem_babyStar
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀)
    {b x : G} (hb : IsConj a b) (hx : IsConj a x) (hbx : orderOf (b * x) = 3) {d : G}
    (hd : d ∈ twoANbr a b ∩ twoANbr a x) {φ : Subgroup.centralizer ({d} : Set G) →* B}
    (hφ : IsBabyCover d φ) {t : B} (ht : t ∈ babyStar (coverMap φ b) (coverMap φ x)) :
    ∃ f ∈ LocalClass (twoANbr a b ∩ twoANbr a x) d, coverMap φ f = t := by
  obtain ⟨ht0, htb, htx⟩ := ht
  obtain ⟨b₀, z, u, h⟩ := exists_twoClasses I.sls I.tableV I.leech hG
  have hbb := mul_self_eq_one_of_isConj_a h hb
  have hxx := mul_self_eq_one_of_isConj_a h hx
  have hbd : b * d = d * b := comm_of_mem_twoANbr h hb hd.1
  have hxd : x * d = d * x := comm_of_mem_twoANbr h hx hd.2
  have hbC : b ∈ Subgroup.centralizer ({d} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hbd
  have hxC : x ∈ Subgroup.centralizer ({d} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hxd
  have hdC : d ∈ Subgroup.centralizer ({d} : Set G) := mem_centralizer_self d
  obtain ⟨f₀, hf₀C, hf₀⟩ := hφ.exists_coverMap_eq t
  have hf₀nbr : f₀ ∈ twoANbr a d :=
    (h.mem_twoANbr_iff I.tableIII hd.1.1 hφ).mpr ⟨hf₀C, by rw [hf₀]; exact ht0⟩
  have hf₀f₀ := mul_self_eq_one_of_isConj_a h hf₀nbr.1
  have hb1 : BabyInv 1 (coverMap φ (b * f₀)) := by
    rw [coverMap_mul hbC hf₀C, hf₀]
    exact htb
  have hx1 : BabyInv 1 (coverMap φ (x * f₀)) := by
    rw [coverMap_mul hxC hf₀C, hf₀]
    exact htx
  obtain ⟨hsqb, hcaseb⟩ :=
    h.babyInv_one_cases I.tableIII hd.1.1 hφ (Subgroup.mul_mem _ hbC hf₀C) hb1
  obtain ⟨hsqx, -⟩ := h.babyInv_one_cases I.tableIII hd.1.1 hφ (Subgroup.mul_mem _ hxC hf₀C) hx1
  have hcb : b * f₀ = f₀ * b := mul_comm_of_mul_self_eq_one hbb hf₀f₀ hsqb
  have hcx : x * f₀ = f₀ * x := mul_comm_of_mul_self_eq_one hxx hf₀f₀ hsqx
  obtain ⟨f, hfcases, hbf⟩ : ∃ f, (f = f₀ ∨ f = d * f₀) ∧ IsConj a (b * f) := by
    rcases hcaseb with ⟨-, h2⟩ | ⟨h2, -⟩
    · refine ⟨d * f₀, Or.inr rfl, ?_⟩
      have : b * (d * f₀) = d * (b * f₀) := by rw [← mul_assoc, hbd, mul_assoc]
      rw [this]
      exact h2
    · exact ⟨f₀, Or.inl rfl, h2⟩
  have hfC : f ∈ Subgroup.centralizer ({d} : Set G) := by
    rcases hfcases with hf | hf <;> rw [hf]
    · exact hf₀C
    · exact Subgroup.mul_mem _ hdC hf₀C
  have hfb : f * b = b * f := by
    rcases hfcases with hf | hf <;> rw [hf]
    · exact hcb.symm
    · calc d * f₀ * b = d * (f₀ * b) := mul_assoc _ _ _
        _ = d * (b * f₀) := by rw [hcb]
        _ = (d * b) * f₀ := (mul_assoc _ _ _).symm
        _ = (b * d) * f₀ := by rw [hbd]
        _ = b * (d * f₀) := mul_assoc _ _ _
  have hfx : f * x = x * f := by
    rcases hfcases with hf | hf <;> rw [hf]
    · exact hcx.symm
    · calc d * f₀ * x = d * (f₀ * x) := mul_assoc _ _ _
        _ = d * (x * f₀) := by rw [hcx]
        _ = (d * x) * f₀ := (mul_assoc _ _ _).symm
        _ = (x * d) * f₀ := by rw [hxd]
        _ = x * (d * f₀) := mul_assoc _ _ _
  have hfA : IsConj a f := by
    rcases hfcases with hf | hf <;> rw [hf]
    · exact hf₀nbr.1
    · exact hf₀nbr.2
  have hxf : IsConj a (x * f) := isConj_mul_of_isConj_mul hbb hxx hbx hfb hfx hbf
  have hcf : coverMap φ f = t := by
    rcases hfcases with hf | hf <;> rw [hf]
    · exact hf₀
    · rw [hφ.coverMap_mul_b hf₀C, hf₀]
  refine ⟨f, ⟨⟨⟨hfA, hbf⟩, ⟨hfA, hxf⟩⟩, ?_, ?_⟩, hcf⟩
  · intro hfd
    rw [hfd, hφ.coverMap_b] at hcf
    rw [← hcf] at ht0
    have h1 := ht0.1
    rw [orderOf_one] at h1
    omega
  · exact Subgroup.mem_centralizer_singleton_iff.mp hfC

theorem babyStar_bijOn
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀) {b x : G}
    (hb : IsConj a b) (hx : IsConj a x) (hbx : orderOf (b * x) = 3) {d : G}
    (hd : d ∈ twoANbr a b ∩ twoANbr a x) {φ : Subgroup.centralizer ({d} : Set G) →* B}
    (hφ : IsBabyCover d φ) :
    Set.BijOn (coverMap φ) (LocalClass (twoANbr a b ∩ twoANbr a x) d)
      (babyStar (coverMap φ b) (coverMap φ x)) := by
  refine ⟨fun f hf => ?_, fun f hf f' hf' he => coverMap_injOn I hG hb hx hbx hd hφ hf hf' he,
    fun t ht => ?_⟩
  · obtain ⟨h0, hbf⟩ := babyInv_of_mem_localClass I hG hb hx hbx (Or.inl rfl) hd hφ hf
    obtain ⟨-, hxf⟩ := babyInv_of_mem_localClass I hG hb hx hbx (Or.inr rfl) hd hφ hf
    exact ⟨h0, hbf, hxf⟩
  · obtain ⟨f, hf, rfl⟩ := exists_mem_localClass_of_mem_babyStar I hG hb hx hbx hd hφ ht
    exact ⟨f, hf, rfl⟩

theorem commute_iff_coverMap
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀) {b x : G}
    (hb : IsConj a b) (hx : IsConj a x) (hbx : orderOf (b * x) = 3) {d : G}
    (hd : d ∈ twoANbr a b ∩ twoANbr a x) {φ : Subgroup.centralizer ({d} : Set G) →* B}
    (hφ : IsBabyCover d φ) {f g : G} (hf : f ∈ LocalClass (twoANbr a b ∩ twoANbr a x) d)
    (hg : g ∈ LocalClass (twoANbr a b ∩ twoANbr a x) d) :
    f * g = g * f ↔ coverMap φ f * coverMap φ g = coverMap φ g * coverMap φ f := by
  have hfC := mem_centralizer_of_mem_localClass hf
  have hgC := mem_centralizer_of_mem_localClass hg
  rw [← coverMap_mul hfC hgC, ← coverMap_mul hgC hfC]
  constructor
  · intro e
    rw [e]
  · intro e
    rcases (hφ.coverMap_eq_iff (Subgroup.mul_mem _ hfC hgC) (Subgroup.mul_mem _ hgC hfC)).mp e
      with e' | e'
    · exact e'.symm
    exfalso
    obtain ⟨b₀, z, u, h⟩ := exists_twoClasses I.sls I.tableV I.leech hG
    have hdd := mul_self_eq_one_of_isConj_a h hd.1.1
    have hff := mul_self_eq_one_of_isConj_a h hf.1.1.1
    have hgg := mul_self_eq_one_of_isConj_a h hg.1.1.1
    have hdc : (f * g) * d = d * (f * g) :=
      Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mul_mem _ hfC hgC)
    have h1 : (f * g) * (d * (f * g)) = 1 := by
      rw [← e']
      calc (f * g) * (g * f) = f * (g * g) * f := by group
        _ = 1 := by rw [hgg, mul_one, hff]
    have h2 : d * ((f * g) * (f * g)) = 1 := by
      calc d * ((f * g) * (f * g)) = (d * (f * g)) * (f * g) := (mul_assoc _ _ _).symm
        _ = ((f * g) * d) * (f * g) := by rw [hdc]
        _ = (f * g) * (d * (f * g)) := mul_assoc _ _ _
        _ = 1 := h1
    have hsq : (f * g) * (f * g) = d := by
      calc (f * g) * (f * g) = (d * d) * ((f * g) * (f * g)) := by rw [hdd, one_mul]
        _ = d * (d * ((f * g) * (f * g))) := mul_assoc _ _ _
        _ = d := by rw [h2, mul_one]
    have hord : orderOf (f * g) = 4 := by
      apply orderOf_eq_four_of_mul_self
      · rw [hsq]
        exact ne_one_of_orderOf (orderOf_eq_two_of_isConj_a h hd.1.1)
      · rw [hsq, hdd]
    have := threeTransposition I hG hb hx hbx hf.1 hg.1
    rw [hord] at this
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this
    omega

omit [Finite G] in
theorem coverMap_mul_mul {d f g : G} {φ : Subgroup.centralizer ({d} : Set G) →* B}
    (hf : f ∈ Subgroup.centralizer ({d} : Set G)) (hg : g ∈ Subgroup.centralizer ({d} : Set G)) :
    coverMap φ (f * g * f) = coverMap φ f * coverMap φ g * coverMap φ f := by
  rw [coverMap_mul (Subgroup.mul_mem _ hf hg) hf, coverMap_mul hf hg]

end Star

end CFSG.Monster.GMS.Fi23Local
