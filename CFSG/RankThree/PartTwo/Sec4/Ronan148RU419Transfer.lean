module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148RU419Defs
public import CFSG.RankThree.PartTwo.Sec4.Ronan138P5Census
import CFSG.RankThree.PartTwo.Sec4.RonanK429CfgTools

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148R

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.KFacts
open CFSG.Assembly.RankThreeEven (projSU)

section Factor

theorem exists_surj_factor {A B U : Type*} [Group A] [Group B] [Group U] [Finite A] [Finite U]
    (f : A →* B) (hf : Function.Surjective f) (π : A →* U) (hπ : Function.Surjective π)
    (hle : f.ker ≤ π.ker) :
    ∃ π' : B →* U, Function.Surjective π' ∧ Nat.card π'.ker ∣ Nat.card π.ker := by
  have : Finite B := Finite.of_surjective f hf
  set e : A ⧸ f.ker ≃* B := QuotientGroup.quotientKerEquivOfSurjective f hf with he
  set π' : B →* U := (QuotientGroup.lift f.ker π hle).comp e.symm.toMonoidHom with hπ'
  have hπ'f : ∀ a : A, π' (f a) = π a := by
    intro a
    have h1 : e.symm (f a) = (a : A ⧸ f.ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    rw [hπ', MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, h1, QuotientGroup.lift_mk]
  have hs : Function.Surjective π' := by
    intro u
    obtain ⟨a, rfl⟩ := hπ u
    exact ⟨f a, hπ'f a⟩
  refine ⟨π', hs, ?_⟩
  have hA : Nat.card A = Nat.card U * Nat.card π.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup π.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective π hπ).toEquiv]
  have hB : Nat.card B = Nat.card U * Nat.card π'.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup π'.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective π' hs).toEquiv]
  have hdvd : Nat.card B ∣ Nat.card A := by
    rw [← Nat.card_congr e.toEquiv]
    exact Subgroup.card_quotient_dvd_card _
  rw [hA, hB] at hdvd
  exact Nat.dvd_of_mul_dvd_mul_left Nat.card_pos hdvd

theorem eq_one_of_central {A U : Type*} [Group A] [Group U] (π : A →* U)
    (hπ : Function.Surjective π) (hU : Subgroup.center U = ⊥) {x : A}
    (hx : ∀ y : A, x * y = y * x) : π x = 1 := by
  have hc : π x ∈ Subgroup.center U := by
    rw [Subgroup.mem_center_iff]
    intro u
    obtain ⟨y, rfl⟩ := hπ u
    rw [← map_mul, ← map_mul, hx y]
  rw [hU] at hc
  exact (Subgroup.mem_bot).mp hc

end Factor

theorem two_pow_mod_three_of_odd {m : ℕ} (hm : Odd m) : 2 ^ m % 3 = 2 := by
  obtain ⟨k, rfl⟩ := hm
  rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
  norm_num

theorem two_lt_two_pow {m : ℕ} (hm : 1 < m) : 2 < 2 ^ m := by
  calc 2 < 2 ^ 2 := by norm_num
    _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm

theorem center_projSU_three_two {m : ℕ} (hm : Odd m) (hm1 : 1 < m) :
    Subgroup.center (projSU 3 2 m) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact (Sec13.isPerfect_center_projSU 2 m (by omega) (two_pow_mod_three_of_odd hm)
    (two_lt_two_pow hm1)).2

section Central

variable {H : Type} [Group H] {N : Subgroup H} [N.Normal]

theorem map_le_autFix_of_mk {α : MulAut H} {β : MulAut (H ⧸ N)}
    (hβ : ∀ h : H, β (h : H ⧸ N) = ((α h : H) : H ⧸ N)) {Y : Subgroup H} (hY : Y ≤ autFix α) :
    Y.map (QuotientGroup.mk' N) ≤ autFix β := by
  rintro _ ⟨y, hy, rfl⟩
  change β (y : H ⧸ N) = (y : H ⧸ N)
  rw [hβ, (hY hy : α y = y)]

theorem isSubnormal_map_of_mk (hN : N ≤ Subgroup.center H) {α : MulAut H} {β : MulAut (H ⧸ N)}
    (hβ : ∀ h : H, β (h : H ⧸ N) = ((α h : H) : H ⧸ N)) {Y : Subgroup H} (hY : Y ≤ autFix α)
    (hsub : (Y.subgroupOf (autFix α)).IsSubnormal) :
    ((Y.map (QuotientGroup.mk' N)).subgroupOf (autFix β)).IsSubnormal := by
  set C : Subgroup H := autFix α with hC
  set D : Subgroup H := (autFix β).comap (QuotientGroup.mk' N) with hD
  have hCD : C ≤ D := fun x hx => by
    change β (x : H ⧸ N) = (x : H ⧸ N)
    rw [hβ, (hx : α x = x)]
  have hCnD : (C.subgroupOf D).Normal := by
    constructor
    intro x hx d
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    have hd : β ((d : H) : H ⧸ N) = ((d : H) : H ⧸ N) := d.2
    rw [hβ, QuotientGroup.eq] at hd
    set w : H := (α (d : H))⁻¹ * (d : H) with hw
    have hwx : w * ((x : D) : H) = ((x : D) : H) * w :=
      (Subgroup.mem_center_iff.mp (hN hd) ((x : D) : H)).symm
    have hx' : α ((x : D) : H) = ((x : D) : H) := hx
    have had : α (d : H) = (d : H) * w⁻¹ := by rw [hw]; group
    change α ((d : H) * ((x : D) : H) * (d : H)⁻¹) = (d : H) * ((x : D) : H) * (d : H)⁻¹
    rw [map_mul, map_mul, map_inv, hx', had]
    calc (d : H) * w⁻¹ * ((x : D) : H) * ((d : H) * w⁻¹)⁻¹ =
        (d : H) * (w⁻¹ * (((x : D) : H) * w)) * (d : H)⁻¹ := by group
      _ = (d : H) * (w⁻¹ * (w * ((x : D) : H))) * (d : H)⁻¹ := by rw [hwx]
      _ = (d : H) * ((x : D) : H) * (d : H)⁻¹ := by group
  have h₁ : (Y.subgroupOf D).IsSubnormal :=
    RonanK429.isSubnormal_subgroupOf_trans hY hCD hsub hCnD.isSubnormal
  set ψ : D →* autFix β := ((QuotientGroup.mk' N).comp D.subtype).codRestrict (autFix β)
    (fun d => d.2) with hψ
  have hψs : Function.Surjective ψ := by
    intro y
    obtain ⟨l, hl⟩ := QuotientGroup.mk_surjective (y : H ⧸ N)
    have hlD : l ∈ D := by
      change ((l : H ⧸ N)) ∈ autFix β
      rw [hl]
      exact y.2
    exact ⟨⟨l, hlD⟩, Subtype.ext hl⟩
  have heq : (Y.subgroupOf D).map ψ = (Y.map (QuotientGroup.mk' N)).subgroupOf (autFix β) := by
    ext y
    constructor
    · rintro ⟨d, hd, rfl⟩
      exact ⟨d, hd, rfl⟩
    · rintro ⟨l, hl, hly⟩
      have hlD : l ∈ D := by
        change ((l : H ⧸ N)) ∈ autFix β
        rw [show ((l : H ⧸ N)) = (y : H ⧸ N) from hly]
        exact y.2
      exact ⟨⟨l, hlD⟩, hl, Subtype.ext hly⟩
  rw [← heq]
  exact h₁.map hψs

theorem pow_three_of_mk {α : MulAut H} {β : MulAut (H ⧸ N)}
    (hβ : ∀ h : H, β (h : H ⧸ N) = ((α h : H) : H ⧸ N)) (hα : α ^ 3 = 1) : β ^ 3 = 1 := by
  have hk : ∀ (k : ℕ) (h : H), (β ^ k) (h : H ⧸ N) = (((α ^ k) h : H) : H ⧸ N) := by
    intro k
    induction k with
    | zero => intro h; rfl
    | succ k ih =>
      intro h
      rw [pow_succ', MulAut.mul_apply, ih, hβ, ← MulAut.mul_apply, ← pow_succ']
  ext x
  induction x using QuotientGroup.induction_on with
  | H h => rw [hk 3 h, hα]; rfl

theorem ne_one_of_mk [Group.IsPerfect H] (hN : N ≤ Subgroup.center H) {α : MulAut H}
    {β : MulAut (H ⧸ N)} (hβ : ∀ h : H, β (h : H ⧸ N) = ((α h : H) : H ⧸ N)) (hα : α ≠ 1) :
    β ≠ 1 := by
  intro h1
  apply hα
  have hcent : ∀ l : H, l⁻¹ * α.toMonoidHom l ∈ Subgroup.center H := by
    intro l
    apply hN
    have h2 := hβ l
    rw [h1, MulAut.one_apply] at h2
    exact QuotientGroup.eq.mp h2
  have hid := CFSG.ComponentClassification.PerfectAutomorphisms.hom_eq_id_of_central_displacement
    α.toMonoidHom hcent
  ext l
  exact congrArg (fun f : H →* H => f l) hid

theorem cfgU419_map [Finite H] [Group.IsPerfect H] (hN : N ≤ Subgroup.center H) {α : MulAut H}
    {β : MulAut (H ⧸ N)} (hβ : ∀ h : H, β (h : H ⧸ N) = ((α h : H) : H ⧸ N)) {Y : Subgroup H}
    {m : ℕ} (hc : CfgU419 H α Y m) : CfgU419 (H ⧸ N) β (Y.map (QuotientGroup.mk' N)) m := by
  haveI := hc.isPerfect
  obtain ⟨π, hπ, hker⟩ := hc.cover
  set f : Y →* Y.map (QuotientGroup.mk' N) := (QuotientGroup.mk' N).subgroupMap Y with hf
  have hfs : Function.Surjective f := (QuotientGroup.mk' N).subgroupMap_surjective Y
  have hle : f.ker ≤ π.ker := by
    intro y hy
    rw [MonoidHom.mem_ker] at hy ⊢
    have hyN : (y : H) ∈ N := by
      have h1 := congrArg Subtype.val hy
      rw [hf, MonoidHom.subgroupMap_apply_coe] at h1
      exact (QuotientGroup.eq_one_iff (y : H)).mp h1
    refine eq_one_of_central π hπ (center_projSU_three_two hc.odd hc.one_lt) (fun z => ?_)
    exact Subtype.ext ((Subgroup.mem_center_iff.mp (hN hyN) (z : H)).symm)
  obtain ⟨π', hπ', hdvd⟩ := exists_surj_factor f hfs π hπ hle
  exact ⟨pow_three_of_mk hβ hc.pow_three, ne_one_of_mk hN hβ hc.ne_one,
    map_le_autFix_of_mk hβ hc.le_autFix, isSubnormal_map_of_mk hN hβ hc.le_autFix hc.isSubnormal,
    Group.IsPerfect.ofSurjective hfs, hc.odd, hc.one_lt,
    ⟨π', hπ', Nat.Coprime.coprime_dvd_left hdvd hker⟩⟩

end Central

section Component

variable {G : Type} [Group G] [Finite G]

theorem autFix_compAction {L : Subgroup G} {a : G} (ha : a ∈ Subgroup.normalizer (L : Set G)) :
    autFix (compAction L ⟨a, ha⟩) = (L ⊓ Subgroup.centralizer ({a} : Set G)).subgroupOf L := by
  ext l
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  change compAction L ⟨a, ha⟩ l = l ↔ _
  constructor
  · intro h
    refine ⟨l.2, ?_⟩
    have h1 : a * (l : G) * a⁻¹ = l := congrArg Subtype.val h
    calc (l : G) * a = a * (l : G) * a⁻¹ * a := by rw [h1]
      _ = a * l := by group
  · rintro ⟨-, h⟩
    apply Subtype.ext
    change a * (l : G) * a⁻¹ = l
    rw [← h, mul_inv_cancel_right]

theorem cfgU419_component {L : Subgroup G} (hL : IsComponent L) {a : G}
    (haN : a ∈ Subgroup.normalizer (L : Set G)) (ha3 : orderOf a = 3)
    (haC : a ∉ Subgroup.centralizer (L : Set G)) {Y : Subgroup G}
    (hYle : Y ≤ L ⊓ Subgroup.centralizer ({a} : Set G)) (hYp : Group.IsPerfect Y)
    (hYsub : (Y.subgroupOf (L ⊓ Subgroup.centralizer ({a} : Set G))).IsSubnormal)
    {m : ℕ} (π : Y →* projSU 3 2 m) (hmo : Odd m) (hm1 : 1 < m) (hπ : Function.Surjective π)
    (hker : Nat.Coprime (Nat.card π.ker) 3) :
    CfgU419 L (compAction L ⟨a, haN⟩) (Y.subgroupOf L) m := by
  have hYL : Y ≤ L := hYle.trans inf_le_left
  set M : Subgroup G := L ⊓ Subgroup.centralizer ({a} : Set G) with hM
  set eY : Y.subgroupOf L ≃* Y := Subgroup.subgroupOfEquivOfLe hYL with heY
  have hfix := autFix_compAction haN
  refine ⟨?_, ?_, ?_, ?_, ?_, hmo, hm1, ?_⟩
  · rw [← map_pow]
    have : (⟨a, haN⟩ : Subgroup.normalizer (L : Set G)) ^ 3 = 1 :=
      Subtype.ext (by rw [Subgroup.coe_pow, ← ha3, pow_orderOf_eq_one]; rfl)
    rw [this, map_one]
  · intro h1
    apply haC
    have hker' : (⟨a, haN⟩ : Subgroup.normalizer (L : Set G)) ∈ (compAction L).ker := h1
    rw [compAction_ker, Subgroup.mem_subgroupOf] at hker'
    exact hker'
  · rw [hfix]
    exact Subgroup.subgroupOf_mono L hYle
  · rw [hfix]
    set e : M.subgroupOf L ≃* M := Subgroup.subgroupOfEquivOfLe inf_le_left with he
    have heq : (Y.subgroupOf L).subgroupOf (M.subgroupOf L) =
        (Y.subgroupOf M).comap e.toMonoidHom := by
      ext x
      simp only [Subgroup.mem_subgroupOf, Subgroup.mem_comap]
      rfl
    rw [heq]
    exact hYsub.comap _
  · exact Group.IsPerfect.ofSurjective (f := eY.symm.toMonoidHom) eY.symm.surjective
  · have hle : (eY.symm.toMonoidHom).ker ≤ π.ker := by
      intro y hy
      rw [MonoidHom.mem_ker] at hy
      have : y = 1 := eY.symm.injective (by rw [map_one]; exact hy)
      rw [this]
      exact one_mem _
    obtain ⟨π', hπ', hdvd⟩ := exists_surj_factor eY.symm.toMonoidHom eY.symm.surjective π hπ hle
    exact ⟨π', hπ', Nat.Coprime.coprime_dvd_left hdvd hker⟩

end Component

section Census


theorem k419UnitaryCensusCover_of_rowU419
    (hrow : ∀ (X : Type) [Group X] [Finite X], IsQuasisimple X →
      IsPGroup 3 (Subgroup.center X) → IsList46 X → RowU419 X) :
    K419UnitaryCensusCover := by
  intro G _ _ L hL hL46 a haN ha3 haC Y hYle hYp hYsub m π hmo hm1 hπ hker
  have hq : IsQuasisimple L := hL.1
  haveI : Group.IsPerfect L := hq.1
  have hθ : aschbacherSolvableCore 3 L ≤ Subgroup.center L := aschbacherSolvableCore_le_center hq
  have hc := cfgU419_component hL haN ha3 haC hYle hYp hYsub π hmo hm1 hπ hker
  have hcX := cfgU419_map hθ (β := thetaQuotMulAut L (compAction L ⟨a, haN⟩))
    (fun h => thetaQuotMulAut_mk _ h) hc
  have hXq : IsQuasisimple (L ⧸ aschbacherSolvableCore 3 L) :=
    (CFSG.LocalCores.quasisimple_central_quotient hq _ hθ).1
  rcases hrow _ hXq (Census.isPGroup_center_thetaQuotient L) hL46 _ _ m hcX with
    ⟨K, hK, h, e, hk⟩ | ⟨K, hK, hKf, hKc, σ, hσ, e, hk⟩
  · exact Or.inl ⟨K, hK, h, e, haN, hk⟩
  · exact Or.inr ⟨K, hK, hKf, hKc, σ, hσ, e, haN, hk⟩

theorem k419UnitaryCensusCover_of_rows (h1 : RowsU419One) (h2 : RowsU419Two)
    (h3 : RowsU419Three) (h4 : RowsU419Four) (h5 : RowsU419Five) (h6 : RowsU419Six)
    (h7 : RowsU419Seven) (h8 : RowsU419Eight) : K419UnitaryCensusCover := by
  refine k419UnitaryCensusCover_of_rowU419 (fun X _ _ hq hZ h46 => ?_)
  rcases (isList46_iff X).mp h46 with h | h | h | h | h | h | h | h
  · exact h1 X hq hZ h
  · exact h2 X hq hZ h
  · exact h3 X hq hZ h
  · exact h4 X hq hZ h
  · exact h5 X hq hZ h
  · exact h6 X hq hZ h
  · exact h7 X hq hZ h
  · exact h8 X hq hZ h

end Census

end CFSG.RankThree.PartTwo.Sec4.Ronan148R
