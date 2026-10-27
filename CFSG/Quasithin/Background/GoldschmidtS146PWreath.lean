module

public import CFSG.Quasithin.Background.GoldschmidtS146PPerf

public section

namespace CFSG.Quasithin.GoldS146P

open Subgroup RegularWreathProduct

variable {W Q : Type*} [Group W] [Group Q] [DecidableEq Q]

@[expose] def embW (q : Q) : W →* W ≀ᵣ Q where
  toFun w := ⟨Pi.mulSingle q w, 1⟩
  map_one' := by
    refine RegularWreathProduct.ext ?_ rfl
    funext x
    simp
  map_mul' a b := by
    refine RegularWreathProduct.ext ?_ (by simp)
    funext x
    by_cases hx : x = q
    · subst hx
      simp [RegularWreathProduct.mul_left]
    · simp [RegularWreathProduct.mul_left, Pi.mulSingle_eq_of_ne hx]

@[simp] theorem embW_left (q : Q) (w : W) (x : Q) :
    (embW q w).left x = (Pi.mulSingle q w : Q → W) x := rfl

@[simp] theorem embW_right (q : Q) (w : W) : (embW q w).right = 1 := rfl

theorem embW_injective (q : Q) : Function.Injective (embW (W := W) q) := by
  intro a b h
  have := congrFun (congrArg RegularWreathProduct.left h) q
  simpa using this

omit [DecidableEq Q] in
theorem left_mul_of_right_eq_one {a b : W ≀ᵣ Q} (ha : a.right = 1) (x : Q) :
    (a * b).left x = a.left x * b.left x := by
  simp [RegularWreathProduct.mul_left, ha]

omit [DecidableEq Q] in
theorem left_inv_of_right_eq_one {a : W ≀ᵣ Q} (ha : a.right = 1) (x : Q) :
    (a⁻¹).left x = (a.left x)⁻¹ := by
  simp [RegularWreathProduct.inv_left, ha]

theorem mem_map_embW_iff {N : Subgroup W} {q : Q} {x : W ≀ᵣ Q} :
    x ∈ N.map (embW q) ↔ x.right = 1 ∧ (∀ y, y ≠ q → x.left y = 1) ∧ x.left q ∈ N := by
  constructor
  · rintro ⟨n, hn, rfl⟩
    refine ⟨rfl, fun y hy => ?_, ?_⟩
    · simp [Pi.mulSingle_eq_of_ne hy]
    · simpa using hn
  · rintro ⟨hr, hy, hq⟩
    refine ⟨x.left q, hq, RegularWreathProduct.ext (funext fun y => ?_) hr.symm⟩
    by_cases hyq : y = q
    · subst hyq
      simp
    · simp [Pi.mulSingle_eq_of_ne hyq, hy y hyq]

@[expose] def baseGrp (W Q : Type*) [Group W] [Group Q] : Subgroup (W ≀ᵣ Q) :=
  (RegularWreathProduct.rightHom : W ≀ᵣ Q →* Q).ker

omit [DecidableEq Q] in
theorem mem_baseGrp {x : W ≀ᵣ Q} : x ∈ baseGrp W Q ↔ x.right = 1 :=
  MonoidHom.mem_ker.trans Iff.rfl

variable (N : Subgroup W) [N.Normal]

theorem normal_map_embW_subgroupOf (q : Q) :
    ((N.map (embW q)).subgroupOf (baseGrp W Q)).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  have hg : (g : W ≀ᵣ Q).right = 1 := mem_baseGrp.mp g.2
  have hn' : (n : W ≀ᵣ Q).right = 1 := mem_baseGrp.mp n.2
  rw [mem_map_embW_iff] at hn ⊢
  obtain ⟨-, hy, hq⟩ := hn
  have hgn : ((g : W ≀ᵣ Q) * (n : W ≀ᵣ Q)).right = 1 := by simp [hg, hn']
  have hleft : ∀ y, ((g : W ≀ᵣ Q) * (n : W ≀ᵣ Q) * (g : W ≀ᵣ Q)⁻¹).left y =
      (g : W ≀ᵣ Q).left y * (n : W ≀ᵣ Q).left y * ((g : W ≀ᵣ Q).left y)⁻¹ := fun y => by
    rw [left_mul_of_right_eq_one hgn, left_mul_of_right_eq_one hg, left_inv_of_right_eq_one hg]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  refine ⟨by simp [hg, hn'], fun y hyq => ?_, ?_⟩
  · rw [hleft, hy y hyq]
    simp
  · rw [hleft]
    exact ‹N.Normal›.conj_mem _ hq _

theorem isComponent_map_embW (hN : CFSG.IsQuasisimple ↥N) (q : Q) :
    CFSG.IsComponent (N.map (embW q)) := by
  refine ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv
    (N.equivMapOfInjective (embW q) (embW_injective q)) hN, ?_⟩
  refine Subgroup.IsSubnormal.step _ (baseGrp W Q) ?_
    (MonoidHom.normal_ker (RegularWreathProduct.rightHom : W ≀ᵣ Q →* Q)).isSubnormal
    (normal_map_embW_subgroupOf N q)
  intro x hx
  exact mem_baseGrp.mpr (mem_map_embW_iff.mp hx).1

omit [DecidableEq Q] in
theorem perfInLayer_wreath (hQ : Nat.card Q = 2) [Group.IsSolvable (W ⧸ N)]
    (hN : CFSG.IsQuasisimple ↥N) : PerfInLayer (W ≀ᵣ Q) := by
  classical
  intro P hP
  have : Group.IsPerfect P := Subgroup.isPerfect_iff.mpr hP
  obtain ⟨g, hg1, hall⟩ : ∃ g : Q, g ≠ 1 ∧ ∀ y : Q, y = 1 ∨ y = g := by
    obtain ⟨g, hg, hu⟩ := (Nat.card_eq_two_iff' (1 : Q)).mp hQ
    exact ⟨g, hg, fun y => by
      by_cases hy : y = 1
      · exact Or.inl hy
      · exact Or.inr (hu y hy)⟩
  have hcomm : ∀ a b : Q, a * b = b * a := by
    intro a b
    rcases hall a with rfl | rfl <;> rcases hall b with rfl | rfl <;> simp
  have : Group.IsSolvable Q := Group.isSolvable_of_comm hcomm
  have hR : ∀ x ∈ P, x.right = 1 := by
    have h := CFSG.ComponentClassification.SolvableKernelContainment.hom_eq_one
      ((RegularWreathProduct.rightHom : W ≀ᵣ Q →* Q).comp P.subtype)
    intro x hx
    exact DFunLike.congr_fun h ⟨x, hx⟩
  have hL : ∀ x ∈ P, ∀ y : Q, x.left y ∈ N := by
    intro x hx y
    let φ : P →* W ⧸ N := MonoidHom.mk' (fun p => QuotientGroup.mk' N ((p : W ≀ᵣ Q).left y))
      (by
        intro a b
        have ha := hR (a : W ≀ᵣ Q) a.2
        rw [Subgroup.coe_mul, left_mul_of_right_eq_one ha, map_mul])
    have h := CFSG.ComponentClassification.SolvableKernelContainment.hom_eq_one φ
    have := DFunLike.congr_fun h ⟨x, hx⟩
    exact (QuotientGroup.eq_one_iff _).mp this
  intro x hx
  have hdec : x = embW 1 (x.left 1) * embW g (x.left g) := by
    refine RegularWreathProduct.ext (funext fun y => ?_) (by simp [hR x hx])
    rcases hall y with rfl | rfl
    · simp [Pi.mulSingle_eq_of_ne hg1.symm]
    · simp [Pi.mulSingle_eq_of_ne hg1]
  rw [hdec]
  exact (CFSG.layer _).mul_mem
    (CFSG.LocalCores.component_le_layer (isComponent_map_embW N hN 1)
      (Subgroup.mem_map_of_mem _ (hL x hx 1)))
    (CFSG.LocalCores.component_le_layer (isComponent_map_embW N hN g)
      (Subgroup.mem_map_of_mem _ (hL x hx g)))

end CFSG.Quasithin.GoldS146P
