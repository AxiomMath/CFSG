module

public import CFSG.LocalAnalysis.StandardType.GGTypeAEndInputsBlock
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeACover

public section

namespace CFSG.StandardType

open Matrix CFSG.RankThree.CALinearPlane CFSG.LieType.Universal.SpecialLinear
open scoped commutatorElement

theorem commute_inv_mul_mul_of_commute {G : Type*} [Group G] {a b u : G}
    (h : Commute a (u * b * u⁻¹)) : Commute (u⁻¹ * a * u) b := by
  show u⁻¹ * a * u * b = b * (u⁻¹ * a * u)
  have h' := h.eq
  calc u⁻¹ * a * u * b = u⁻¹ * (a * (u * b * u⁻¹)) * u := by group
    _ = u⁻¹ * (u * b * u⁻¹ * a) * u := by rw [h']
    _ = b * (u⁻¹ * a * u) := by group

section Key

variable {n : ℕ} {F : Type} [Field F] {X : Type*} [Group X]
  {φ₁ φ₂ : SpecialLinearGroup (Fin (n + 1)) F →* X}

theorem slCompat_commute_blocks (h2 : (2 : F) = 0) (hn : 3 ≤ n)
    (hc : φ₁.comp (slLowerBlockHom n F) = φ₂.comp (slUpperBlockHom n F))
    (hfar : Commute (φ₂ (weylRep n F ⟨n - 1, by omega⟩)) (φ₁ (weylRep n F ⟨0, by omega⟩)))
    {J₀ J₁ : Finset (Fin (n + 1))} (hJ₀ : ∀ i ∈ J₀, i.val < 2) (hJ₁ : ∀ i ∈ J₁, n - 1 ≤ i.val)
    {g g' : SpecialLinearGroup (Fin (n + 1)) F} (hg : g ∈ coordBlockSL F J₀)
    (hg' : g' ∈ coordBlockSL F J₁) :
    Commute (φ₁ g) (φ₂ g') := by
  set T := φ₂ (weylRep n F ⟨n - 1, by omega⟩) with hT
  have hTnode := ggTypeAEndNode_of_compat h2 hn hc hfar
  have hTg : Commute (φ₁ g) T := by
    refine (commute_of_mem_closure φ₁ ?_ (coordBlockSL_le_closure J₀ hg)).symm
    rintro _ ⟨a, b, hab, ha, hb, c, rfl⟩
    have ha' := hJ₀ a ha
    have hb' := hJ₀ b hb
    exact hTnode.2.2 a b hab (by omega) (by omega) c
  have hgkl : ∀ {k l : Fin (n + 1)} (hkl : k ≠ l), 2 ≤ k.val → 2 ≤ l.val → ∀ d : F,
      Commute (φ₁ g) (φ₁ (SpecialLinearGroup.transvection hkl d)) := by
    intro k l hkl hk hl d
    have h1 : Commute (SpecialLinearGroup.transvection hkl d) g := by
      refine commute_of_mem_closure (MonoidHom.id _) ?_ (coordBlockSL_le_closure J₀ hg)
      rintro _ ⟨a, b, hab, ha, hb, c, rfl⟩
      have ha' := hJ₀ a ha
      have hb' := hJ₀ b hb
      exact (commute_transvection_of_ne hab hkl (Fin.ne_of_val_ne (by omega))
        (Fin.ne_of_val_ne (by omega)) c d).symm
    exact h1.symm.map φ₁
  let one : Fin (n + 1) := ⟨1, by omega⟩
  let two : Fin (n + 1) := ⟨2, by omega⟩
  let pen : Fin (n + 1) := ⟨n - 1, by omega⟩
  have h1p : one ≠ pen := Fin.ne_of_val_ne (by simp [one, pen]; omega)
  have h1l : one ≠ Fin.last n := Fin.ne_of_val_ne (by simp [one]; omega)
  have h2l : two ≠ Fin.last n := Fin.ne_of_val_ne (by simp [two]; omega)
  have hpl : pen ≠ Fin.last n := Fin.ne_of_val_ne (by simp [pen]; omega)
  have hj : (⟨n - 1, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := Fin.ne_of_val_ne (by simp; omega)
  have e1 : ∀ c : F, φ₂ (SpecialLinearGroup.transvection h1p.symm c) =
      φ₁ (SpecialLinearGroup.transvection h2l.symm c) := fun c =>
    (slCompat_transvection hc h2l.symm h1p.symm hj (Fin.ext (by simp; omega)) (Fin.ext rfl)
      (Fin.ext rfl) (Fin.ext rfl) c).symm
  have e2 : ∀ c : F, φ₂ (SpecialLinearGroup.transvection h1p c) =
      φ₁ (SpecialLinearGroup.transvection h2l c) := fun c =>
    (slCompat_transvection hc h2l h1p hj.symm (Fin.ext rfl) (Fin.ext (by simp; omega))
      (Fin.ext rfl) (Fin.ext rfl) c).symm
  have F1 : ∀ c : F, Commute (φ₁ g) (φ₂ (SpecialLinearGroup.transvection h1p.symm c)) :=
    fun c => by rw [e1]; exact hgkl _ (by simp; omega) (by simp [two]) c
  have F2 : ∀ c : F, Commute (φ₁ g) (φ₂ (SpecialLinearGroup.transvection h1p c)) :=
    fun c => by rw [e2]; exact hgkl _ (by simp [two]) (by simp; omega) c
  have hk : ((⟨n - 1, by omega⟩ : Fin n).castSucc : Fin (n + 1)) = pen := Fin.ext rfl
  have hk' : ((⟨n - 1, by omega⟩ : Fin n).succ : Fin (n + 1)) = Fin.last n :=
    Fin.ext (by simp; omega)
  have hsw1 : Equiv.swap pen (Fin.last n) one = one :=
    Equiv.swap_apply_of_ne_of_ne h1p h1l
  have F3 : ∀ c : F, Commute (φ₁ g) (φ₂ (SpecialLinearGroup.transvection h1l.symm c)) := by
    intro c
    have h : weylRep n F ⟨n - 1, by omega⟩ * SpecialLinearGroup.transvection h1p.symm c *
        (weylRep n F ⟨n - 1, by omega⟩)⁻¹ = SpecialLinearGroup.transvection h1l.symm c := by
      rw [weylRep_conj_transvection_of_two h2 (⟨n - 1, by omega⟩ : Fin n) h1p.symm c]
      exact transvection_eq_of_eq _ _ (by rw [hk, hk', Equiv.swap_apply_left])
        (by rw [hk, hk', hsw1]) c
    rw [← h, map_mul, map_mul, map_inv]
    exact commute_mul_mul_inv_of_commute hTg (F1 c)
  have F4 : ∀ c : F, Commute (φ₁ g) (φ₂ (SpecialLinearGroup.transvection h1l c)) := by
    intro c
    have h : weylRep n F ⟨n - 1, by omega⟩ * SpecialLinearGroup.transvection h1p c *
        (weylRep n F ⟨n - 1, by omega⟩)⁻¹ = SpecialLinearGroup.transvection h1l c := by
      rw [weylRep_conj_transvection_of_two h2 (⟨n - 1, by omega⟩ : Fin n) h1p c]
      exact transvection_eq_of_eq _ _ (by rw [hk, hk', hsw1])
        (by rw [hk, hk', Equiv.swap_apply_left]) c
    rw [← h, map_mul, map_mul, map_inv]
    exact commute_mul_mul_inv_of_commute hTg (F2 c)
  refine commute_of_mem_closure φ₂ ?_ (coordBlockSL_le_closure J₁ hg')
  rintro _ ⟨a, b, hab, ha, hb, c, rfl⟩
  have ha' := hJ₁ a ha
  have hb' := hJ₁ b hb
  have hab' : a.val ≠ b.val := fun h => hab (Fin.ext h)
  have hav := a.isLt
  have hbv := b.isLt
  have ha1 : a ≠ one := Fin.ne_of_val_ne (by simp [one]; omega)
  have hb1 : one ≠ b := Fin.ne_of_val_ne (by simp [one]; omega)
  have hcomm := SpecialLinearGroup.commutatorElement_transvection ha1 hb1 hab c 1
  rw [mul_one] at hcomm
  rw [← hcomm, map_commutatorElement]
  rcases Nat.lt_or_ge a.val n with han | han
  ·
    obtain rfl : a = pen := Fin.ext (by simp [pen]; omega)
    obtain rfl : b = Fin.last n := Fin.ext (by simp; omega)
    exact commute_commutatorElement_of_commute (F1 c) (F4 1)
  ·
    obtain rfl : a = Fin.last n := Fin.ext (by simp; omega)
    obtain rfl : b = pen := Fin.ext (by simp [pen]; omega)
    exact commute_commutatorElement_of_commute (F3 c) (F2 1)

end Key

section Unique

variable {n : ℕ} {F : Type} [Field F] {X : Type*} [Group X]

theorem slCompat_far_of_far [Finite F] (h2 : (2 : F) = 0) (hn : 3 ≤ n)
    {φ₁ φ₂ ψ₁ ψ₂ : SpecialLinearGroup (Fin (n + 1)) F →* X}
    (hk₁ : φ₁.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (n + 1)) F))
    (hk₂ : φ₂.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (n + 1)) F))
    (hl₁ : ψ₁.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (n + 1)) F))
    (hl₂ : ψ₂.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (n + 1)) F))
    (hr₁ : φ₁.range = ψ₁.range) (hr₂ : φ₂.range = ψ₂.range)
    (hc : φ₁.comp (slLowerBlockHom n F) = φ₂.comp (slUpperBlockHom n F))
    (hc' : ψ₁.comp (slLowerBlockHom n F) = ψ₂.comp (slUpperBlockHom n F))
    (hJ : (ψ₁.comp (slLowerBlockHom n F)).range = (φ₁.comp (slLowerBlockHom n F)).range)
    (hfar : Commute (φ₂ (weylRep n F ⟨n - 1, by omega⟩)) (φ₁ (weylRep n F ⟨0, by omega⟩))) :
    Commute (ψ₂ (weylRep n F ⟨n - 1, by omega⟩)) (ψ₁ (weylRep n F ⟨0, by omega⟩)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨α₁, hα₁⟩ := exists_mulAut_of_slLift (by omega : 3 ≤ m + 1 + 1) hr₁ hk₁ hl₁
  obtain ⟨α₂, hα₂⟩ := exists_mulAut_of_slLift (by omega : 3 ≤ m + 1 + 1) hr₂ hk₂ hl₂
  have hψ₁ : ∀ x, ψ₁ x = φ₁ (α₁ x) := fun x => by rw [hα₁]; rfl
  have hψ₂ : ∀ x, ψ₂ x = φ₂ (α₂ x) := fun x => by rw [hα₂]; rfl
  have hθ := injective_comp_slLowerBlockHom hk₁
  have hθ' := injective_comp_slLowerBlockHom hl₁
  let β : MulAut (SpecialLinearGroup (Fin (m + 1)) F) :=
    ((MonoidHom.ofInjective hθ').trans (MulEquiv.subgroupCongr hJ)).trans
      (MonoidHom.ofInjective hθ).symm
  have hβ : ∀ g, φ₁ (slLowerBlockHom (m + 1) F (β g)) = ψ₁ (slLowerBlockHom (m + 1) F g) := by
    intro g
    have e := MulEquiv.apply_symm_apply (MonoidHom.ofInjective hθ)
      ((MulEquiv.subgroupCongr hJ) (MonoidHom.ofInjective hθ' g))
    have e' := congrArg Subtype.val e
    rw [MonoidHom.ofInjective_apply] at e'
    exact e'.trans (by rw [MulEquiv.subgroupCongr_apply, MonoidHom.ofInjective_apply]; rfl)
  have hperf : commutator (SpecialLinearGroup (Fin (m + 1)) F) = ⊤ := by
    have := CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect (K := F)
      (by omega : 3 ≤ m + 1)
    exact Group.IsPerfect.commutator_eq_top
  have hL : ∀ g, α₁ (slLowerBlockHom (m + 1) F g) = slLowerBlockHom (m + 1) F (β g) := by
    have h := TypeA.eq_of_inv_mul_mem_center hperf
      (α₁.toMonoidHom.comp (slLowerBlockHom (m + 1) F))
      ((slLowerBlockHom (m + 1) F).comp β.toMonoidHom) fun g => hk₁ (by
        rw [MonoidHom.mem_ker, map_mul, map_inv]
        simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
        rw [hβ, ← hψ₁, inv_mul_cancel])
    exact fun g => DFunLike.congr_fun h g
  have hU : ∀ g, α₂ (slUpperBlockHom (m + 1) F g) = slUpperBlockHom (m + 1) F (β g) := by
    have h := TypeA.eq_of_inv_mul_mem_center hperf
      (α₂.toMonoidHom.comp (slUpperBlockHom (m + 1) F))
      ((slUpperBlockHom (m + 1) F).comp β.toMonoidHom) fun g => hk₂ (by
        rw [MonoidHom.mem_ker, map_mul, map_inv]
        simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
        have e1 : φ₂ (α₂ (slUpperBlockHom (m + 1) F g)) = ψ₁ (slLowerBlockHom (m + 1) F g) := by
          rw [← hψ₂]
          exact (DFunLike.congr_fun hc' g).symm
        have e2 : φ₂ (slUpperBlockHom (m + 1) F (β g)) =
            φ₁ (slLowerBlockHom (m + 1) F (β g)) := (DFunLike.congr_fun hc (β g)).symm
        rw [e1, e2, hβ, inv_mul_cancel])
    exact fun g => DFunLike.congr_fun h g
  obtain ⟨s, hsL, hsU⟩ := exists_conj_slBlocks_of_mulAut (by omega : 2 ≤ m) β
  set ιL := slLowerBlockHom (m + 1) F with hιL
  set ιU := slUpperBlockHom (m + 1) F with hιU
  set n₀ := weylRep (m + 1) F ⟨0, by omega⟩ with hn₀
  set nl := weylRep (m + 1) F ⟨m + 1 - 1, by omega⟩ with hnl
  have hn₀' : n₀ = weylRep (m + 1) F 0 := rfl
  have hnl' : nl = weylRep (m + 1) F (Fin.last m) := by
    rw [hnl]
    congr 1
  set a' := (ιL s)⁻¹ * α₁ n₀ * ιL s with ha'
  set b' := (ιU s)⁻¹ * α₂ nl * ιU s with hb'
  have ha2 : a' * a' = 1 := by
    have h1 : α₁ n₀ * α₁ n₀ = 1 := by
      rw [← map_mul, hn₀', weylRep_mul_self (m + 1) h2, map_one]
    calc a' * a' = (ιL s)⁻¹ * (α₁ n₀ * α₁ n₀) * ιL s := by rw [ha']; group
      _ = 1 := by rw [h1]; group
  have hb2 : b' * b' = 1 := by
    have h1 : α₂ nl * α₂ nl = 1 := by
      rw [← map_mul, hnl', weylRep_mul_self (m + 1) h2, map_one]
    calc b' * b' = (ιU s)⁻¹ * (α₂ nl * α₂ nl) * ιU s := by rw [hb']; group
      _ = 1 := by rw [h1]; group
  have hcommA : ∀ (i j : Fin (m + 1 + 1)) (hij : i ≠ j), 2 ≤ i.val → 2 ≤ j.val →
      Commute a' (SpecialLinearGroup.transvection hij 1) := by
    intro i j hij hi hj
    have hiv := i.isLt
    have hjv := j.isLt
    let i₀ : Fin m := ⟨i.val - 2, by omega⟩
    let j₀ : Fin m := ⟨j.val - 2, by omega⟩
    have hij₀ : i₀ ≠ j₀ := fun h => hij (Fin.ext (by
      have h' := congrArg Fin.val h
      simp only [i₀, j₀] at h'
      omega))
    set h : SpecialLinearGroup (Fin (m + 1)) F :=
      slLowerBlockHom m F (SpecialLinearGroup.transvection hij₀ 1) with hh
    have ht : SpecialLinearGroup.transvection hij 1 = ιL h := by
      rw [hh, hιL, slLowerBlockHom_transvection, slLowerBlockHom_transvection]
      exact transvection_eq_of_eq _ _ (Fin.ext (by simp [i₀]; omega))
        (Fin.ext (by simp [j₀]; omega)) 1
    have hmem : s * h * s⁻¹ ∈ (slLowerBlockHom m F).range.map (MulAut.conj s).toMonoidHom :=
      Subgroup.mem_map.mpr ⟨h, ⟨_, hh.symm⟩, rfl⟩
    rw [← hsL] at hmem
    obtain ⟨_, ⟨k, rfl⟩, hk⟩ := Subgroup.mem_map.mp hmem
    rw [MulEquiv.coe_toMonoidHom] at hk
    have c1 := (commute_weylRep_zero_slLowerBlockHom₂ h2 k).map α₁
    rw [← hn₀', ← hιL, hL, hk, map_mul, map_mul, map_inv] at c1
    rw [ht]
    exact commute_inv_mul_mul_of_commute c1
  have hcommB : ∀ (i j : Fin (m + 1 + 1)) (hij : i ≠ j), i.val < m → j.val < m →
      Commute b' (SpecialLinearGroup.transvection hij 1) := by
    intro i j hij hi hj
    let i₀ : Fin m := ⟨i.val, hi⟩
    let j₀ : Fin m := ⟨j.val, hj⟩
    have hij₀ : i₀ ≠ j₀ := fun h => hij (Fin.ext (by
      have h' := congrArg Fin.val h
      simp only [i₀, j₀] at h'
      omega))
    set h : SpecialLinearGroup (Fin (m + 1)) F :=
      slUpperBlockHom m F (SpecialLinearGroup.transvection hij₀ 1) with hh
    have ht : SpecialLinearGroup.transvection hij 1 = ιU h := by
      rw [hh, hιU, slUpperBlockHom_transvection, slUpperBlockHom_transvection]
    have hmem : s * h * s⁻¹ ∈ (slUpperBlockHom m F).range.map (MulAut.conj s).toMonoidHom :=
      Subgroup.mem_map.mpr ⟨h, ⟨_, hh.symm⟩, rfl⟩
    rw [← hsU] at hmem
    obtain ⟨_, ⟨k, rfl⟩, hk⟩ := Subgroup.mem_map.mp hmem
    rw [MulEquiv.coe_toMonoidHom] at hk
    have c1 := (commute_weylRep_last_slUpperBlockHom₂ h2 k).map α₂
    rw [← hnl', ← hιU, hU, hk, map_mul, map_mul, map_inv] at c1
    rw [ht]
    exact commute_inv_mul_mul_of_commute c1
  have hA : a' ∈ coordBlockSL F (Finset.univ.filter fun i : Fin (m + 1 + 1) => i.val < 2) := by
    refine mem_coordBlockSL_of_commute h2 ha2 _ fun i hi => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hi
    by_cases hi2 : i.val = 2
    · exact ⟨⟨3, by omega⟩, Fin.ne_of_val_ne (by simp; omega),
        hcommA _ _ _ hi (by simp), hcommA _ _ _ (by simp) hi⟩
    · exact ⟨⟨2, by omega⟩, Fin.ne_of_val_ne (by simp; omega),
        hcommA _ _ _ hi (by simp), hcommA _ _ _ (by simp) hi⟩
  have hB : b' ∈ coordBlockSL F (Finset.univ.filter fun i : Fin (m + 1 + 1) => m ≤ i.val) := by
    refine mem_coordBlockSL_of_commute h2 hb2 _ fun i hi => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hi
    by_cases hi0 : i.val = 0
    · exact ⟨⟨1, by omega⟩, Fin.ne_of_val_ne (by show i.val ≠ 1; omega),
        hcommB _ _ _ hi (by show 1 < m; omega), hcommB _ _ _ (by show 1 < m; omega) hi⟩
    · exact ⟨⟨0, by omega⟩, Fin.ne_of_val_ne (by show i.val ≠ 0; omega),
        hcommB _ _ _ hi (by show 0 < m; omega), hcommB _ _ _ (by show 0 < m; omega) hi⟩
  have hkey := slCompat_commute_blocks h2 hn hc hfar
    (fun i hi => by simpa using hi) (fun i hi => by simp at hi; omega) hA hB
  have hu : φ₂ (ιU s) = φ₁ (ιL s) := (DFunLike.congr_fun hc s).symm
  have e1 : ψ₁ n₀ = φ₁ (ιL s) * φ₁ a' * (φ₁ (ιL s))⁻¹ := by
    rw [hψ₁, ← map_inv, ← map_mul, ← map_mul, ha']
    congr 1
    group
  have e2 : ψ₂ nl = φ₁ (ιL s) * φ₂ b' * (φ₁ (ιL s))⁻¹ := by
    rw [hψ₂, ← hu, ← map_inv, ← map_mul, ← map_mul, hb']
    congr 1
    group
  rw [e1, e2]
  exact (Commute.conj_iff _).mpr hkey.symm

end Unique

end CFSG.StandardType
