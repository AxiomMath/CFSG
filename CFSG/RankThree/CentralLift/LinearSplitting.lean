module

public import CFSG.RankThree.CentralLift.LinearTorusMonomial
public import CFSG.RankThree.CentralExtension.BruhatLiftSplitting

public section

namespace CFSG.RankThree.CentralLift

namespace LinearRoots

open Matrix CFSG.LieType.CentralExt CFSG.LieType.Universal.SpecialLinear
open scoped commutatorElement Pointwise
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl (sl2Diag coe_sl2Diag IsLinePerm)
open CFSG.LieType.Chevalley (uSL vSL coe_uSL coe_vSL)
open CFSG.LocalAnalysis.ComponentInitial.LinearCover (rootElt rootElt_of_ne)
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (unitriangular mem_unitriangular)

variable {k : Type} [Field k] {n : ℕ}

theorem uSL_mul_wSL_one (a : kˣ) :
    uSL (a : k) * wSL 1 = vSL ((a⁻¹ : kˣ) : k) * sl2Diag (-a) * uSL (-((a⁻¹ : kˣ) : k)) := by
  refine Matrix.SpecialLinearGroup.ext _ _ fun x y => ?_
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_uSL, coe_vSL, coe_wSL, coe_sl2Diag]
  fin_cases x <;> fin_cases y <;> simp [mul_apply, Fin.sum_univ_two]

theorem conj_mem_closure_of_forall {G : Type*} [Group G] {S T : Set G} {g : G}
    (h : ∀ x ∈ S, g * x * g⁻¹ ∈ Subgroup.closure T) {x : G} (hx : x ∈ Subgroup.closure S) :
    g * x * g⁻¹ ∈ Subgroup.closure T := by
  have hle : (Subgroup.closure S).map (MulAut.conj g).toMonoidHom ≤ Subgroup.closure T := by
    rw [MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨y, hy, rfl⟩
    exact h y hy
  exact hle ⟨x, hx, rfl⟩

theorem perm_eq_one_of_forall_le {σ : Equiv.Perm (Fin n)} (h : ∀ x, σ x ≤ x) : σ = 1 := by
  have hsum : ∑ x : Fin n, ((σ x : Fin n) : ℕ) = ∑ x : Fin n, (x : ℕ) :=
    Equiv.sum_comp σ (fun x : Fin n => (x : ℕ))
  have hall := (Finset.sum_eq_sum_iff_of_le fun x _ => Fin.le_iff_val_le_val.1 (h x)).1 hsum
  exact Equiv.ext fun x => Fin.ext (hall x (Finset.mem_univ x))

theorem swap_lt_swap {m : ℕ} {i : Fin m} {a b : Fin (m + 1)} (hab : a < b)
    (hne : ¬(a = i.castSucc ∧ b = i.succ)) :
    Equiv.swap i.castSucc i.succ a < Equiv.swap i.castSucc i.succ b := by
  have hval : ∀ x : Fin (m + 1), ((Equiv.swap i.castSucc i.succ x : Fin (m + 1)) : ℕ) =
      if (x : ℕ) = (i : ℕ) then (i : ℕ) + 1 else if (x : ℕ) = (i : ℕ) + 1 then (i : ℕ)
        else (x : ℕ) := by
    intro x
    rw [Equiv.swap_apply_def]
    split_ifs with h1 h2 h3 h4 <;> simp_all [Fin.ext_iff]
  rw [Fin.lt_def] at hab ⊢
  rw [hval, hval]
  simp only [Fin.ext_iff, Fin.val_castSucc, Fin.val_succ] at hne
  split_ifs <;> omega

theorem eq_signedPerm_one_of_mem_diagonalSL {A : SpecialLinearGroup (Fin n) k}
    (hA : A ∈ diagonalSL k n) :
    (A : Matrix (Fin n) (Fin n) k) = signedPerm 1 fun x =>
      ((Units.mk0 _ (apply_self_ne_zero_of_mem_diagonalSL hA x) : kˣ) : k) := by
  rw [signedPerm_one]
  simp only [Units.val_mk0]
  exact eq_diagonal_of_mem_diagonalSL hA

section Roots

variable {E : Type*} [Group E] (π : E →* SpecialLinearGroup (Fin n) k)

@[expose] noncomputable def rootLift (i j : Fin n) : Subgroup E :=
  ((rhoLift π i j).comp uSLHom).range

theorem mem_rootLift {i j : Fin n} {x : E} : x ∈ rootLift π i j ↔ ∃ a : k, xLift π i j a = x := by
  rw [rootLift, MonoidHom.mem_range]
  exact ⟨fun ⟨a, ha⟩ => ⟨a.toAdd, ha⟩, fun ⟨a, ha⟩ => ⟨Multiplicative.ofAdd a, ha⟩⟩

theorem xLift_mem_rootLift (i j : Fin n) (a : k) : xLift π i j a ∈ rootLift π i j :=
  (mem_rootLift π).2 ⟨a, rfl⟩

@[expose] noncomputable def unipotentLiftExcept (i j : Fin n) : Subgroup E :=
  Subgroup.closure {x | ∃ (a b : Fin n) (c : k), a < b ∧ (a, b) ≠ (i, j) ∧ xLift π a b c = x}

@[expose] noncomputable def borelLift : Subgroup E := unipotentLift π ⊔ torusLin π

theorem xLift_mem_unipotentLift {a b : Fin n} (hab : a < b) (c : k) :
    xLift π a b c ∈ unipotentLift π :=
  Subgroup.subset_closure ⟨a, b, c, hab, rfl⟩

theorem rootLift_le_unipotentLift {i j : Fin n} (hij : i < j) :
    rootLift π i j ≤ unipotentLift π := by
  intro x hx
  obtain ⟨a, rfl⟩ := (mem_rootLift π).1 hx
  exact xLift_mem_unipotentLift π hij a

theorem unipotentLiftExcept_le (i j : Fin n) : unipotentLiftExcept π i j ≤ unipotentLift π := by
  rw [unipotentLiftExcept, Subgroup.closure_le]
  rintro _ ⟨a, b, c, hab, -, rfl⟩
  exact xLift_mem_unipotentLift π hab c

end Roots

section Sections

variable [Finite k] {E : Type*} [Group E] [Finite E] {π : E →* SpecialLinearGroup (Fin n) k}
  (hk : ringChar k ≠ 2) (hπ : IsLargeCentralExt π)
include hk hπ

theorem section_transvection {σ : SpecialLinearGroup (Fin n) k →* E}
    (hσ : π.comp σ = MonoidHom.id _) {i j : Fin n} (hij : i ≠ j) (c : k) :
    σ (SpecialLinearGroup.transvection hij c) = xLift π i j c := by
  have hlift : π.comp (σ.comp (rhoSL k i j)) = rhoSL k i j := by
    rw [← MonoidHom.comp_assoc, hσ, MonoidHom.id_comp]
  have h := eq_sl2Lift_large hk hπ hlift
  rw [← rootElt_of_ne hij, ← rhoSL_uSL hij]
  exact DFunLike.congr_fun h (uSL c)

theorem section_unique {σ σ' : SpecialLinearGroup (Fin n) k →* E}
    (hσ : π.comp σ = MonoidHom.id _) (hσ' : π.comp σ' = MonoidHom.id _) : σ = σ' := by
  refine MonoidHom.eq_of_eqOn_dense CFSG.LinearGroups.special_linear_elementary_generation ?_
  rintro _ ⟨i, j, hij, c, rfl⟩
  rw [section_transvection hk hπ hσ hij c, section_transvection hk hπ hσ' hij c]

end Sections

theorem exists_mulEquiv_prod_of_section {E S : Type*} [Group E] [Group S] {π : E →* S}
    (hC : π.ker ≤ Subgroup.center E) {σ : S →* E} (hσ : π.comp σ = MonoidHom.id S) :
    ∃ e : π.ker × σ.range ≃* E, ∀ c g, e (c, g) = (c : E) * g := by
  have hσx : ∀ x, π (σ x) = x := fun x => DFunLike.congr_fun hσ x
  let f : π.ker × σ.range →* E := MonoidHom.noncommCoprod π.ker.subtype σ.range.subtype
    fun c g => (Subgroup.mem_center_iff.1 (hC c.2) g).symm
  have hf : ∀ c g, f (c, g) = (c : E) * g := fun _ _ => rfl
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    rintro ⟨c, ⟨g, x, rfl⟩⟩ h
    rw [hf] at h
    have hx : x = 1 := by
      have h' := congrArg π h
      rwa [map_mul, MonoidHom.mem_ker.1 c.2, one_mul, hσx, map_one] at h'
    subst hx
    have hc : (c : E) = 1 := by simpa using h
    exact Prod.ext (Subtype.ext hc) (Subtype.ext (map_one σ))
  have hsurj : Function.Surjective f := by
    intro e
    refine ⟨(⟨e * (σ (π e))⁻¹, ?_⟩, ⟨σ (π e), π e, rfl⟩), ?_⟩
    · rw [MonoidHom.mem_ker, map_mul, map_inv, hσx, mul_inv_cancel]
    · rw [hf]
      exact inv_mul_cancel_right e (σ (π e))
  exact ⟨MulEquiv.ofBijective f ⟨hinj, hsurj⟩, hf⟩

section Bruhat

variable {m : ℕ} [Finite k] {E : Type*} [Group E] [Finite E]
  {π : E →* SpecialLinearGroup (Fin (m + 1)) k} (hk : ringChar k ≠ 2) (hπ : IsLargeCentralExt π)
include hk hπ

theorem xLift_mul_wLift_one {i j : Fin (m + 1)} (hij : i ≠ j) (a : kˣ) :
    xLift π i j a * wLift π i j 1 =
      xLift π j i ((a⁻¹ : kˣ) : k) * hLin π i j (-a) * xLift π i j (-((a⁻¹ : kˣ) : k)) := by
  rw [xLift, wLift_eq hk hπ hij, ← map_mul, uSL_mul_wSL_one, map_mul, map_mul,
    xLift_swap hk hπ hij, hLin_eq hk hπ hij, xLift]

theorem conj_mem_unipotentLift {g : E} {σ : Equiv.Perm (Fin (m + 1))} {c : Fin (m + 1) → kˣ}
    (hg : ((π g : SpecialLinearGroup (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k) =
      signedPerm σ fun x => (c x : k)) (hσ : ∀ a b, a < b → σ a < σ b) {u : E}
    (hu : u ∈ unipotentLift π) : g * u * g⁻¹ ∈ unipotentLift π := by
  refine conj_mem_closure_of_forall (fun x hx => ?_) hu
  obtain ⟨a, b, c', hab, rfl⟩ := hx
  rw [conj_xLift_of_signedPerm hk hπ hab.ne hg]
  exact Subgroup.subset_closure ⟨σ a, σ b, _, hσ a b hab, rfl⟩

theorem torusLin_le_normalizer :
    torusLin π ≤ Subgroup.normalizer (unipotentLift π : Set E) := by
  have key : ∀ t ∈ torusLin π, ∀ u ∈ unipotentLift π, t * u * t⁻¹ ∈ unipotentLift π :=
    fun t ht u hu => conj_mem_unipotentLift hk hπ
      (eq_signedPerm_one_of_mem_diagonalSL (torusLin_le_comap_diagonalSL hk hπ ht))
      (fun a b h => h) hu
  intro t ht
  rw [Subgroup.mem_normalizer_iff]
  intro u
  refine ⟨key t ht u, fun hu => ?_⟩
  have h := key t⁻¹ (inv_mem ht) _ hu
  rwa [show t⁻¹ * (t * u * t⁻¹) * t⁻¹⁻¹ = u by group] at h

theorem coe_borelLift :
    (borelLift π : Set E) = (unipotentLift π : Set E) * (torusLin π : Set E) :=
  Subgroup.coe_mul_of_right_le_normalizer_left _ _ (torusLin_le_normalizer hk hπ)

theorem pi_mem_unitriangular {u : E} (hu : u ∈ unipotentLift π) :
    π u ∈ unitriangular (m + 1) k := by
  rw [← map_unipotentLift hk hπ]
  exact Subgroup.mem_map_of_mem π hu

theorem injOn_borelLift : Set.InjOn π (borelLift π) := by
  have hker : ∀ b ∈ borelLift π, π b = 1 → b = 1 := by
    intro b hb h1
    have hb' : b ∈ (borelLift π : Set E) := hb
    rw [coe_borelLift hk hπ] at hb'
    obtain ⟨u, hu, t, ht, rfl⟩ := hb'
    rw [map_mul] at h1
    have hut : π u = (π t)⁻¹ := eq_inv_of_mul_eq_one_left h1
    have hdiag : π u ∈ diagonalSL k (m + 1) := by
      rw [hut]
      exact inv_mem (torusLin_le_comap_diagonalSL hk hπ ht)
    have hU := mem_unitriangular.1 (pi_mem_unitriangular hk hπ hu)
    have hu1 : π u = 1 := by
      refine Matrix.SpecialLinearGroup.ext _ _ fun r c => ?_
      by_cases hrc : r = c
      · subst hrc
        rw [hU.2 r, Matrix.SpecialLinearGroup.coe_one, one_apply_eq]
      · rw [mem_diagonalSL.1 hdiag r c hrc, Matrix.SpecialLinearGroup.coe_one,
          one_apply_ne hrc]
    have ht1 : π t = 1 := by rwa [hu1, one_mul] at h1
    have hu1' : u = 1 := by
      have h := injective_unipotentLift hk hπ (a₁ := ⟨u, hu⟩) (a₂ := 1) (by
        change π u = π 1
        rw [hu1, map_one])
      exact congrArg Subtype.val h
    have ht1' : t = 1 := by
      have h := injective_torusLin hk hπ 0 (a₁ := ⟨t, ht⟩) (a₂ := 1) (by
        change π t = π 1
        rw [ht1, map_one])
      exact congrArg Subtype.val h
    show u * t = 1
    rw [hu1', ht1', one_mul]
  intro x hx y hy hxy
  have h := hker (x⁻¹ * y) (mul_mem (inv_mem hx) hy) (by
    rw [map_mul, map_inv, hxy, inv_mul_cancel])
  exact inv_mul_eq_one.1 h

theorem blockTriangular_of_mem_borelLift {b : E} (hb : b ∈ borelLift π) :
    ((π b : SpecialLinearGroup (Fin (m + 1)) k) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) k).BlockTriangular id := by
  have hb' : b ∈ (borelLift π : Set E) := hb
  rw [coe_borelLift hk hπ] at hb'
  obtain ⟨u, hu, t, ht, rfl⟩ := hb'
  rw [map_mul, Matrix.SpecialLinearGroup.coe_mul]
  refine Matrix.BlockTriangular.mul ?_ ?_
  · intro r c hrc
    exact (mem_unitriangular.1 (pi_mem_unitriangular hk hπ hu)).1 r c hrc
  · intro r c hrc
    exact mem_diagonalSL.1 (torusLin_le_comap_diagonalSL hk hπ ht) r c hrc.ne'

theorem rootLift_le_normalizer (i : Fin m) :
    rootLift π i.castSucc i.succ ≤
      Subgroup.normalizer (unipotentLiftExcept π i.castSucc i.succ : Set E) := by
  have hi : i.castSucc < i.succ := Fin.castSucc_lt_succ
  have key : ∀ t : k, ∀ y ∈ unipotentLiftExcept π i.castSucc i.succ,
      xLift π i.castSucc i.succ t * y * (xLift π i.castSucc i.succ t)⁻¹ ∈
        unipotentLiftExcept π i.castSucc i.succ := by
    intro t y hy
    refine conj_mem_closure_of_forall (fun x hx => ?_) hy
    obtain ⟨a, b, c, hab, hne, rfl⟩ := hx
    have e : xLift π i.castSucc i.succ t * xLift π a b c * (xLift π i.castSucc i.succ t)⁻¹ =
        ⁅xLift π i.castSucc i.succ t, xLift π a b c⁆ * xLift π a b c := by
      simp only [commutatorElement_def]
      group
    have hy' : xLift π a b c ∈ unipotentLiftExcept π i.castSucc i.succ :=
      Subgroup.subset_closure ⟨a, b, c, hab, hne, rfl⟩
    rw [e]
    by_cases ha : a = i.succ
    · subst ha
      have hib : i.castSucc < b := hi.trans hab
      rw [commutatorElement_xLift hk hπ hi.ne hab.ne hib.ne]
      refine mul_mem (Subgroup.subset_closure ⟨i.castSucc, b, t * c, hib, ?_, rfl⟩) hy'
      intro h
      exact hab.ne (Prod.mk.inj h).2.symm
    by_cases hb : b = i.castSucc
    · subst hb
      have hai : a < i.succ := hab.trans hi
      rw [← commutatorElement_inv, commutatorElement_xLift hk hπ hab.ne hi.ne hai.ne,
        ← xLift_neg]
      refine mul_mem (Subgroup.subset_closure ⟨a, i.succ, -(c * t), hai, ?_, rfl⟩) hy'
      intro h
      exact hab.ne (Prod.mk.inj h).1
    · rw [commutatorElement_xLift_eq_one hk hπ hi.ne hab.ne (Ne.symm ha) (Ne.symm hb), one_mul]
      exact hy'
  intro g hg
  obtain ⟨t, rfl⟩ := (mem_rootLift π).1 hg
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨key t y, fun hy => ?_⟩
  have h := key (-t) _ hy
  rw [xLift_neg, inv_inv] at h
  rwa [show (xLift π i.castSucc i.succ t)⁻¹ *
      (xLift π i.castSucc i.succ t * y * (xLift π i.castSucc i.succ t)⁻¹) *
        xLift π i.castSucc i.succ t = y by group] at h

theorem coe_unipotentLift_eq (i : Fin m) :
    (unipotentLift π : Set E) = (rootLift π i.castSucc i.succ : Set E) *
      (unipotentLiftExcept π i.castSucc i.succ : Set E) := by
  have hsup : unipotentLift π =
      rootLift π i.castSucc i.succ ⊔ unipotentLiftExcept π i.castSucc i.succ := by
    apply le_antisymm
    · rw [unipotentLift, Subgroup.closure_le]
      rintro _ ⟨a, b, c, hab, rfl⟩
      by_cases h : (a, b) = (i.castSucc, i.succ)
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
        exact Subgroup.mem_sup_left (xLift_mem_rootLift π _ _ c)
      · exact Subgroup.mem_sup_right (Subgroup.subset_closure ⟨a, b, c, hab, h, rfl⟩)
    · exact sup_le (rootLift_le_unipotentLift π Fin.castSucc_lt_succ)
        (unipotentLiftExcept_le π _ _)
  rw [hsup]
  exact Subgroup.coe_mul_of_left_le_normalizer_right _ _ (rootLift_le_normalizer hk hπ i)

theorem coe_borelLift_eq (i : Fin m) :
    (borelLift π : Set E) = (rootLift π i.castSucc i.succ : Set E) *
      (unipotentLiftExcept π i.castSucc i.succ : Set E) * (torusLin π : Set E) := by
  rw [coe_borelLift hk hπ, coe_unipotentLift_eq hk hπ i]

theorem conj_wLift_mem_unipotentLift (i : Fin m) {u : E}
    (hu : u ∈ unipotentLiftExcept π i.castSucc i.succ) :
    (wLift π i.castSucc i.succ 1)⁻¹ * u * wLift π i.castSucc i.succ 1 ∈ unipotentLift π := by
  have hw : wLift π i.castSucc i.succ 1 * u * (wLift π i.castSucc i.succ 1)⁻¹ ∈
      unipotentLift π := by
    refine conj_mem_closure_of_forall (fun x hx => ?_) hu
    obtain ⟨a, b, c, hab, hne, rfl⟩ := hx
    rw [conj_xLift_of_signedPerm hk hπ hab.ne (pi_wLift_one hk hπ Fin.castSucc_lt_succ.ne)]
    exact Subgroup.subset_closure ⟨_, _, _, swap_lt_swap hab fun h => hne (by rw [h.1, h.2]),
      rfl⟩
  have hh : wLift π i.castSucc i.succ 1 * wLift π i.castSucc i.succ 1 ∈ torusLin π := by
    rw [wLift_one_mul_self hk hπ Fin.castSucc_lt_succ.ne]
    exact hLin_mem_torusLin π Fin.castSucc_lt_succ.ne _
  have h := (Subgroup.mem_normalizer_iff.1 (torusLin_le_normalizer hk hπ (inv_mem hh)) _).1 hw
  rwa [show (wLift π i.castSucc i.succ 1 * wLift π i.castSucc i.succ 1)⁻¹ *
      (wLift π i.castSucc i.succ 1 * u * (wLift π i.castSucc i.succ 1)⁻¹) *
        (wLift π i.castSucc i.succ 1 * wLift π i.castSucc i.succ 1)⁻¹⁻¹ =
      (wLift π i.castSucc i.succ 1)⁻¹ * u * wLift π i.castSucc i.succ 1 by group] at h

theorem mul_wLift_mem (i : Fin m) {x : E} (hx : x ∈ rootLift π i.castSucc i.succ)
    (hx1 : x ≠ 1) : x * wLift π i.castSucc i.succ 1 ∈
      (rootLift π i.succ i.castSucc : Set E) * (torusLin π : Set E) *
        (rootLift π i.castSucc i.succ : Set E) := by
  obtain ⟨a, rfl⟩ := (mem_rootLift π).1 hx
  have ha : a ≠ 0 := fun h => hx1 (by rw [h, xLift_zero])
  have e := xLift_mul_wLift_one hk hπ (Fin.castSucc_lt_succ (i := i)).ne (Units.mk0 a ha)
  rw [Units.val_mk0] at e
  rw [e]
  exact ⟨_, ⟨_, xLift_mem_rootLift π _ _ _, _,
    hLin_mem_torusLin π Fin.castSucc_lt_succ.ne _, rfl⟩, _, xLift_mem_rootLift π _ _ _, rfl⟩

theorem sign_cases {g : E} (hg : π g ∈ monomialSL k (m + 1)) (i : Fin m) :
    (∀ x ∈ rootLift π i.castSucc i.succ, g * x * g⁻¹ ∈ unipotentLift π) ∨
      (∀ y ∈ rootLift π i.succ i.castSucc, g * y * g⁻¹ ∈ unipotentLift π) := by
  obtain ⟨σ, c, hc⟩ := exists_signedPerm_of_mem_monomialSL hg
  rcases lt_or_gt_of_ne (σ.injective.ne (Fin.castSucc_lt_succ (i := i)).ne) with h | h
  · left
    intro x hx
    obtain ⟨a, rfl⟩ := (mem_rootLift π).1 hx
    rw [conj_xLift_of_signedPerm hk hπ Fin.castSucc_lt_succ.ne hc]
    exact xLift_mem_unipotentLift π h _
  · right
    intro y hy
    obtain ⟨a, rfl⟩ := (mem_rootLift π).1 hy
    rw [conj_xLift_of_signedPerm hk hπ Fin.castSucc_lt_succ.ne' hc]
    exact xLift_mem_unipotentLift π h _

theorem mem_torusLin_of_mem_map {g : E} (hg : g ∈ monoLin π)
    (hgB : π g ∈ (borelLift π).map π) : g ∈ torusLin π := by
  obtain ⟨b, hb, hbg⟩ := hgB
  have htri := blockTriangular_of_mem_borelLift hk hπ hb
  rw [hbg] at htri
  have hσ := isLinePerm_weylPerm hk hπ ⟨g, hg⟩
  have h1 : weylPerm hk hπ ⟨g, hg⟩ = 1 := by
    refine perm_eq_one_of_forall_le fun x => ?_
    by_contra hlt
    exact hσ.apply_ne_zero x (htri (not_le.1 hlt))
  have h2 : (⟨g, hg⟩ : monoLin π) ∈ (weylPerm hk hπ).ker := h1
  rw [ker_weylPerm hk hπ] at h2
  exact Subgroup.mem_subgroupOf.1 h2

theorem map_borelLift_sup_map_monoLin : (borelLift π).map π ⊔ (monoLin π).map π = ⊤ := by
  have hU : ∀ {a b : Fin (m + 1)}, a < b → ∀ c : k, π (xLift π a b c) ∈ (borelLift π).map π :=
    fun hab c => Subgroup.mem_map_of_mem π
      (Subgroup.mem_sup_left (xLift_mem_unipotentLift π hab c))
  rw [eq_top_iff, ← CFSG.LinearGroups.special_linear_elementary_generation, Subgroup.closure_le]
  rintro _ ⟨i, j, hij, c, rfl⟩
  rw [SetLike.mem_coe]
  rcases lt_or_gt_of_ne hij with h | h
  · rw [← rootElt_of_ne hij, ← pi_xLift hk hπ hij]
    exact Subgroup.mem_sup_left (hU h c)
  · have hw := conj_xLift_of_signedPerm hk hπ hij.symm (pi_wLift_one hk hπ hij) (-c)
    rw [Equiv.swap_apply_right, Equiv.swap_apply_left] at hw
    have hcoef : ((wSign (k := k) i j : kˣ) : k) / (wSign i i : kˣ) * -c = c := by
      simp [wSign, hij.symm]
    rw [hcoef] at hw
    have hmem : π (wLift π i j 1) ∈ (monoLin π).map π := by
      rw [map_monoLin hk hπ]
      exact pi_wLift_mem hk hπ hij 1
    have e : SpecialLinearGroup.transvection hij c =
        π (wLift π i j 1) * π (xLift π j i (-c)) * (π (wLift π i j 1))⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul, hw, pi_xLift hk hπ hij, rootElt_of_ne hij]
    rw [e]
    exact mul_mem (mul_mem (Subgroup.mem_sup_right hmem) (Subgroup.mem_sup_left (hU h (-c))))
      (inv_mem (Subgroup.mem_sup_right hmem))

omit [Finite k] [Finite E] hk hπ in
theorem monoLin_eq_closure : monoLin π = Subgroup.closure ((torusLin π : Set E) ∪
    Set.range fun i : Fin m => wLift π i.castSucc i.succ 1) := by
  apply le_antisymm
  · rw [monoLin, Subgroup.closure_le]
    rintro x (hx | ⟨i, rfl⟩)
    · exact Subgroup.subset_closure (Or.inl hx)
    · by_cases hi : i = Fin.last m
      · subst hi
        rw [SetLike.mem_coe, wAdj_last]
        exact one_mem _
      · obtain ⟨j, rfl⟩ : ∃ j : Fin m, j.castSucc = i :=
          ⟨i.castPred hi, Fin.castSucc_castPred i hi⟩
        rw [wAdj_castSucc]
        exact Subgroup.subset_closure (Or.inr ⟨j, rfl⟩)
  · rw [Subgroup.closure_le]
    rintro x (hx | ⟨i, rfl⟩)
    · exact torusLin_le_monoLin π hx
    · show wLift π i.castSucc i.succ 1 ∈ monoLin π
      rw [← wAdj_castSucc]
      exact wAdj_mem_monoLin π _

theorem exists_section :
    ∃ σ : SpecialLinearGroup (Fin (m + 1)) k →* E, π.comp σ = MonoidHom.id _ :=
  (CFSG.RankThree.CentralExtension.central_extension_faithful_bruhat_lift_splitting π hπ.cen
    (coe_borelLift hk hπ) (injOn_borelLift hk hπ) (normal_torusLin_subgroupOf hk hπ)
    (fun i : Fin m => wLift π i.castSucc i.succ 1) monoLin_eq_closure
    (fun i => by
      rw [pow_two, wLift_one_mul_self hk hπ Fin.castSucc_lt_succ.ne]
      exact hLin_mem_torusLin π Fin.castSucc_lt_succ.ne _)
    (fun i => rootLift π i.castSucc i.succ) (fun i => rootLift π i.succ i.castSucc)
    (fun i => unipotentLiftExcept π i.castSucc i.succ)
    (fun _ => rootLift_le_unipotentLift π Fin.castSucc_lt_succ)
    (fun i => coe_borelLift_eq hk hπ i)
    (fun i _ hu => conj_wLift_mem_unipotentLift hk hπ i hu)
    (fun i _ hx hx1 => mul_wLift_mem hk hπ i hx hx1)
    (fun _ hg i => sign_cases hk hπ (monoLin_le_comap hk hπ hg) i)
    (fun _ hg hgB => mem_torusLin_of_mem_map hk hπ hg hgB)
    (map_borelLift_sup_map_monoLin hk hπ)).2.2

end Bruhat

theorem odd_field_linear_central_large_prime_extension_splitting {p ℓ f : ℕ}
    (hp : p.Prime) (hp3 : 3 < p) (hℓ : ℓ.Prime) (hℓodd : Odd ℓ) (_hf : 1 ≤ f) {k : Type}
    [Field k] (hk : Nat.card k = ℓ ^ f) {n : ℕ} (hn : 2 ≤ n) {E : Type*} [Group E] [Finite E]
    (π : E →* SpecialLinearGroup (Fin n) k) (hπ : Function.Surjective π)
    (hC : π.ker ≤ Subgroup.center E) (hCp : IsPGroup p π.ker) :
    (∃! s : SpecialLinearGroup (Fin n) k →* E, π.comp s = MonoidHom.id _) ∧
    ∀ s : SpecialLinearGroup (Fin n) k →* E, π.comp s = MonoidHom.id _ →
      ∃ e : π.ker × s.range ≃* E, ∀ c g, e (c, g) = (c : E) * g := by
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; exact pow_ne_zero f hℓ.ne_zero)
  have hk2 := ringChar_ne_two_of_card hℓ hℓodd hk
  have hπ' : IsLargeCentralExt π := ⟨hπ, hC, p, hp, hp3, hCp⟩
  refine ⟨?_, fun s hs => exists_mulEquiv_prod_of_section hC hs⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨σ, hσ⟩ := exists_section hk2 hπ'
  exact ⟨σ, hσ, fun σ' hσ' => section_unique hk2 hπ' hσ' hσ⟩

end LinearRoots

end CFSG.RankThree.CentralLift
