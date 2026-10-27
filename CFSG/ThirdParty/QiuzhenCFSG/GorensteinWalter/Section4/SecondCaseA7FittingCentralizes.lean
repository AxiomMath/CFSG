module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.GW1965
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.A7SylowCentralizer
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# The `A₇` Fact 1.10(ii) endpoint

An odd subgroup normalizing a component induces an odd-order automorphism on
the component quotient.  In the `A₇` model, all such automorphisms are inner;
the fixed Sylow-2 image then forces the inner element to be trivial.  A
perfectness argument lifts triviality from the quotient to the component.
-/

universe u

noncomputable section

namespace CFSG.GorensteinWalter

private def conjOn {G : Type u} [Group G]
    (E M : Subgroup G) (f : G) (hf : f ∈ M)
    (hE : IsNormalIn E M) : E →* E :=
  { toFun := fun x => ⟨f * (x : G) * f⁻¹, hE.2 f hf (x : G) x.2⟩
    map_one' := by
      apply Subtype.ext
      simp
    map_mul' := by
      intro x y
      apply Subtype.ext
      change f * ((x : G) * (y : G)) * f⁻¹ =
        (f * (x : G) * f⁻¹) * (f * (y : G) * f⁻¹)
      group }

private def conjOnInv {G : Type u} [Group G]
    (E M : Subgroup G) (f : G) (hf : f ∈ M)
    (hE : IsNormalIn E M) : E →* E :=
  conjOn E M f⁻¹ (M.inv_mem hf) hE

private theorem conjOn_left {G : Type u} [Group G]
    (E M : Subgroup G) (f : G) (hf : f ∈ M)
    (hE : IsNormalIn E M) (x : E) :
    conjOnInv E M f hf hE (conjOn E M f hf hE x) = x := by
  apply Subtype.ext
  simp [conjOnInv, conjOn]
  group

private theorem conjOn_right {G : Type u} [Group G]
    (E M : Subgroup G) (f : G) (hf : f ∈ M)
    (hE : IsNormalIn E M) (x : E) :
    conjOn E M f hf hE (conjOnInv E M f hf hE x) = x := by
  apply Subtype.ext
  simp [conjOnInv, conjOn]
  group

private def conjOnEquiv {G : Type u} [Group G]
    (E M : Subgroup G) (f : G) (hf : f ∈ M)
    (hE : IsNormalIn E M) : E ≃* E :=
  MulEquiv.ofBijective (conjOn E M f hf hE) ⟨
    (Function.LeftInverse.injective (conjOn_left E M f hf hE)),
    (fun y => ⟨conjOnInv E M f hf hE y, conjOn_right E M f hf hE y⟩)⟩

private theorem map_center_local {E : Type u} [Group E] (e : E ≃* E) :
    (Subgroup.center E).map e.toMonoidHom = Subgroup.center E := by
  apply le_antisymm
  · rintro z ⟨x, hx, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro y
    have hxy := Subgroup.mem_center_iff.mp hx (e.symm y)
    simpa [map_mul] using congrArg e hxy
  · intro z hz
    refine Subgroup.mem_map.mpr ⟨e.symm z, ?_, ?_⟩
    · rw [Subgroup.mem_center_iff]
      intro y
      have hxy := Subgroup.mem_center_iff.mp hz (e y)
      simpa [map_mul] using congrArg e.symm hxy
    · simp

private theorem conjOn_pow {G : Type u} [Group G]
    (E M : Subgroup G) (f : G) (hf : f ∈ M)
    (hE : IsNormalIn E M) (n : ℕ) (x : E) :
    ((conjOnEquiv E M f hf hE) ^ n) x =
      ⟨f ^ n * (x : G) * (f ^ n)⁻¹,
        hE.2 (f ^ n) (by
          induction n with
          | zero => simpa using M.one_mem
          | succ n ih => simpa [pow_succ] using M.mul_mem ih hf) (x : G) x.2⟩ := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]
    change ((conjOnEquiv E M f hf hE) ^ n)
      (conjOnEquiv E M f hf hE x) = _
    rw [ih]
    apply Subtype.ext
    simp [conjOnEquiv, conjOn]
    group

private theorem quotient_congr_pow_mk {E : Type u} [Group E]
    (Z : Subgroup E) [Z.Normal] (e : E ≃* E)
    (he : Z.map (↑e) = Z) (n : ℕ) (x : E) :
    ((QuotientGroup.congr Z Z e he) ^ n) (QuotientGroup.mk' Z x) =
      QuotientGroup.mk' Z ((e ^ n) x) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]
    have hcomp :
        ((QuotientGroup.congr Z Z e he) ^ n *
            QuotientGroup.congr Z Z e he) (QuotientGroup.mk' Z x) =
          ((QuotientGroup.congr Z Z e he) ^ n)
            ((QuotientGroup.congr Z Z e he) (QuotientGroup.mk' Z x)) := by
      rfl
    rw [hcomp]
    have hmk :
        (QuotientGroup.congr Z Z e he) (QuotientGroup.mk' Z x) =
          QuotientGroup.mk' Z (e x) := by
      simp [QuotientGroup.congr, QuotientGroup.map_mk']
    rw [hmk, ih]
    rw [pow_succ]
    simp [QuotientGroup.congr, QuotientGroup.map_mk']

private theorem quotient_conj_pow_eq_one {G : Type u} [Group G] [Finite G]
    (E M : Subgroup G) (f : G) (hf : f ∈ M)
    (hE : IsNormalIn E M) (n : ℕ) (hn : f ^ n = 1) :
    (QuotientGroup.congr (Subgroup.center E) (Subgroup.center E)
      (conjOnEquiv E M f hf hE)
      (by simpa only [MulEquiv.toMonoidHom_eq_coe] using
        map_center_local (conjOnEquiv E M f hf hE))) ^ n = 1 := by
  apply MulEquiv.ext
  intro q
  refine QuotientGroup.induction_on q ?_
  intro x
  have he' : Subgroup.map (↑(conjOnEquiv E M f hf hE))
      (Subgroup.center E) = Subgroup.center E := by
    simpa only [MulEquiv.toMonoidHom_eq_coe] using
      (map_center_local (conjOnEquiv E M f hf hE))
  change ((QuotientGroup.congr (Subgroup.center E) (Subgroup.center E)
      (conjOnEquiv E M f hf hE) he') ^ n) (QuotientGroup.mk' _ x) = _
  rw [quotient_congr_pow_mk]
  have hpow : ((conjOnEquiv E M f hf hE) ^ n) x =
      ⟨f ^ n * (x : G) * (f ^ n)⁻¹, by
        exact hE.2 (f ^ n) (M.pow_mem hf n) (x : G) x.2⟩ :=
    conjOn_pow E M f hf hE n x
  have hpow' : ((conjOnEquiv E M f hf hE) ^ n) x = x := by
    apply Subtype.ext
    calc
      (((conjOnEquiv E M f hf hE) ^ n) x : G) =
          f ^ n * (x : G) * (f ^ n)⁻¹ := congrArg Subtype.val hpow
      _ = (x : G) := by simp [hn]
  rw [hpow']
  simp

private theorem monoidHom_eq_one_of_perfect_abelian_local
    {A B : Type u} [Group A] [Group B]
    (hA : Group.IsPerfect A) (hB : IsMulCommutative B) (f : A →* B) :
    f = 1 := by
  apply MonoidHom.ext
  intro x
  have hx : x ∈ ⁅(⊤ : Subgroup A), (⊤ : Subgroup A)⁆ := by
    have htop : Group.IsPerfect (↥(⊤ : Subgroup A)) := by
      let : Group.IsPerfect A := hA
      infer_instance
    have hcomm : ⁅(⊤ : Subgroup A), (⊤ : Subgroup A)⁆ = ⊤ :=
      (Subgroup.isPerfect_iff (H := (⊤ : Subgroup A))).mp htop
    rw [hcomm]
    trivial
  rw [Subgroup.commutator_def] at hx
  refine Subgroup.closure_induction (p := fun y _hy => f y = 1) ?_ ?_ ?_ ?_ hx
  · intro y hy
    rcases hy with ⟨g₁, _hg₁, g₂, _hg₂, rfl⟩
    rw [map_commutatorElement]
    exact (commutatorElement_eq_one_iff_mul_comm).2
      ((IsMulCommutative.is_comm (M := B)).comm (f g₁) (f g₂))
  · simp
  · intro a b _ha _hb ha hb
    rw [map_mul, ha, hb, mul_one]
  · intro a _ha ha
    rw [map_inv, ha, inv_one]

private theorem central_automorphism_eq_one_local
    {E : Type u} [Group E]
    (hperf : Group.IsPerfect E) (α β : E ≃* E)
    (hdelta : ∀ x : E, α x * (β x)⁻¹ ∈ Subgroup.center E) :
    α = β := by
  apply MulEquiv.ext
  intro x
  let : Bracket E E := commutatorElement
  have hcomm : ∀ a b : E, α ⁅a, b⁆ = β ⁅a, b⁆ := by
    intro a b
    have hza := Subgroup.mem_center_iff.mp (hdelta a)
    have hzb := Subgroup.mem_center_iff.mp (hdelta b)
    have ha : α a = (α a * (β a)⁻¹) * β a := by group
    have hb : α b = (α b * (β b)⁻¹) * β b := by group
    have htarget : ⁅α a, α b⁆ = ⁅β a, β b⁆ := by
      rw [show α a = (α a * (β a)⁻¹) * β a by group,
        show α b = (α b * (β b)⁻¹) * β b by group]
      -- the two deviations are central, so they disappear from the commutator
      let za : E := α a * (β a)⁻¹
      let zb : E := α b * (β b)⁻¹
      have hza_center : za ∈ Subgroup.center E := by simpa [za] using hdelta a
      have hzb_center : zb ∈ Subgroup.center E := by simpa [zb] using hdelta b
      have hleft : ∀ z x y : E, z ∈ Subgroup.center E →
        ⁅z * x, y⁆ = ⁅x, y⁆ := by
        intro z x y hz
        rw [commutatorElement_mul_left_eq_conj_mul]
        have hzy : ⁅z, y⁆ = 1 := by
          rw [commutatorElement_eq_one_iff_mul_comm]
          exact (Subgroup.mem_center_iff.mp hz y).symm
        have hzc : z * ⁅x, y⁆ * z⁻¹ = ⁅x, y⁆ := by
          rw [(Subgroup.mem_center_iff.mp hz ⁅x, y⁆).symm]
          simp
        rw [hzy, hzc]
        simp
      have hright : ∀ z x y : E, z ∈ Subgroup.center E →
        ⁅x, y * z⁆ = ⁅x, y⁆ := by
        intro z x y hz
        rw [commutatorElement_mul_right_eq_mul_conj]
        have hxy : ⁅x, z⁆ = 1 := by
          rw [commutatorElement_eq_one_iff_mul_comm]
          exact Subgroup.mem_center_iff.mp hz x
        have hzc : z * ⁅x, y⁆ * z⁻¹ = ⁅x, y⁆ := by
          rw [(Subgroup.mem_center_iff.mp hz ⁅x, y⁆).symm]
          simp
        rw [hxy]
        simpa [mul_assoc] using hzc
      rw [hleft za (β a) (zb * β b) hza_center]
      rw [show zb * β b = β b * zb by
        exact (Subgroup.mem_center_iff.mp hzb_center (β b)).symm]
      rw [hright zb (β a) (β b) hzb_center]
    simpa only [map_commutatorElement] using htarget
  have hx : x ∈ ⁅(⊤ : Subgroup E), (⊤ : Subgroup E)⁆ := by
    have htop : Group.IsPerfect (↥(⊤ : Subgroup E)) := by
      let : Group.IsPerfect E := hperf
      infer_instance
    have hcommtop : ⁅(⊤ : Subgroup E), (⊤ : Subgroup E)⁆ = ⊤ :=
      (Subgroup.isPerfect_iff (H := (⊤ : Subgroup E))).mp htop
    rw [hcommtop]
    trivial
  rw [Subgroup.commutator_def] at hx
  refine Subgroup.closure_induction (p := fun y _hy => α y = β y) ?_ ?_ ?_ ?_ hx
  · intro y hy
    rcases hy with ⟨a, _ha, b, _hb, rfl⟩
    exact hcomm a b
  · simp
  · intro a b _ha _hb ha hb
    rw [map_mul, ha, hb, map_mul]
  · intro a _ha ha
    rw [map_inv, ha, map_inv]

private theorem orderOf_element_dvd_of_conj_pow_eq_one
    {Q : Type u} [Group Q]
    (hcenter : Subgroup.center Q = ⊥)
    (a : Q) {n : ℕ} (hpow : (MulAut.conj a) ^ n = 1) :
    orderOf a ∣ n := by
  have hconjpow : MulAut.conj (a ^ n) = 1 := by
    simpa [map_pow] using hpow
  have hacent : a ^ n ∈ Subgroup.center Q := by
    rw [Subgroup.mem_center_iff]
    intro x
    have hx := DFunLike.congr_fun hconjpow x
    change a ^ n * x * (a ^ n)⁻¹ = x at hx
    exact (mul_inv_eq_iff_eq_mul.mp (by simpa [mul_assoc] using hx)).symm
  have haneq : a ^ n = 1 := by
    rw [hcenter] at hacent
    exact Subgroup.mem_bot.mp hacent
  exact (orderOf_dvd_iff_pow_eq_one).2 haneq

/-- In the `A₇` component model, an odd subgroup of `M` that centralizes a
Sylow `2`-subgroup of the component induces an inner automorphism on the
component quotient and therefore centralizes the component itself. -/
public theorem secondCase_a7_odd_subgroup_centralizes_component
    {G : Type u} [Group G] [Finite G]
    (E M F S : Subgroup G)
    (hEcomp : IsComponentOf E M)
    (hEnorm : IsNormalIn E M)
    (hFleM : F ≤ M)
    (hFodd : Odd (Nat.card F))
    (hFcentS : F ≤ Subgroup.centralizer (S : Set G))
    (eQ : Nonempty ((E ⧸ Subgroup.center E) ≃*
      alternatingGroup (Fin 7)))
    (Sbar : Sylow 2 (alternatingGroup (Fin 7)))
    (hSmap :
      ((S.subgroupOf E).map (QuotientGroup.mk' (Subgroup.center E))).map
        eQ.some.toMonoidHom = (Sbar : Subgroup (alternatingGroup (Fin 7)))) :
    F ≤ Subgroup.centralizer (E : Set G) := by
  classical
  let : Group.IsPerfect E := (Group.isPerfect_def).2 hEcomp.2.2.2.1
  let A7 := alternatingGroup (Fin 7)
  let q : E →* E ⧸ Subgroup.center E := QuotientGroup.mk' (Subgroup.center E)
  intro f hfF
  have hfM : f ∈ M := hFleM hfF
  let α : E ≃* E := conjOnEquiv E M f hfM hEnorm
  have hαcenter : Subgroup.map (↑α) (Subgroup.center E) =
      Subgroup.center E := by
    simpa only [MulEquiv.toMonoidHom_eq_coe] using map_center_local α
  let φ : E ⧸ Subgroup.center E ≃* E ⧸ Subgroup.center E :=
    QuotientGroup.congr (Subgroup.center E) (Subgroup.center E) α hαcenter
  let n : ℕ := orderOf f
  have hfn : f ^ n = 1 := by
    exact pow_orderOf_eq_one f
  have hφpow : φ ^ n = 1 := by
    dsimp [φ, n]
    exact quotient_conj_pow_eq_one E M f hfM hEnorm (orderOf f) hfn
  let eQ' : E ⧸ Subgroup.center E ≃* A7 := eQ.some
  let φA : MulAut A7 := MulAut.congr eQ' φ
  have hφApow : φA ^ n = 1 := by
    calc
      φA ^ n = (MulAut.congr eQ') (φ ^ n) := by simp [φA, map_pow]
      _ = (MulAut.congr eQ') 1 := by rw [hφpow]
      _ = 1 := by
        apply MulEquiv.ext
        intro x
        simp [MulAut.congr_apply]
  have hFodd_order : Odd n := by
    have hdvd : orderOf f ∣ Nat.card F := Subgroup.orderOf_dvd_natCard F hfF
    exact Odd.of_dvd_nat hFodd (by simpa [n] using hdvd)
  have hφAodd : Odd (orderOf φA) := by
    have hdvd : orderOf φA ∣ n := (orderOf_dvd_iff_pow_eq_one).2 hφApow
    exact Odd.of_dvd_nat hFodd_order hdvd
  obtain ⟨a, ha⟩ := gw_lemma_3_2_ix_a7_no_outer_automorphisms_odd_order φA hφAodd
  let z0 : E ⧸ Subgroup.center E := eQ'.symm a
  have hφinner : φ = MulAut.conj z0 := by
    apply (MulAut.congr eQ').injective
    calc
      (MulAut.congr eQ') φ = φA := rfl
      _ = MulAut.conj a := ha
      _ = (MulAut.congr eQ') (MulAut.conj z0) := by
        apply MulEquiv.ext
        intro x
        simp [z0, MulAut.congr_apply, MulAut.conj_apply]
  have ha_conj_pow : (MulAut.conj a) ^ n = 1 := by
    rw [← ha]
    exact hφApow
  have hcenterA7 : Subgroup.center A7 = ⊥ := by
    exact alternatingGroup.center_eq_bot (by norm_num)
  have ha_order_dvd : orderOf a ∣ n :=
    orderOf_element_dvd_of_conj_pow_eq_one hcenterA7 a ha_conj_pow
  have ha_odd : Odd (orderOf a) := Odd.of_dvd_nat hFodd_order ha_order_dvd
  let P0 : Subgroup A7 := Subgroup.zpowers a
  have hP0odd : Odd (Nat.card P0) := by
    rw [Nat.card_zpowers]
    exact ha_odd
  have ha_cent_Sbar : a ∈ Subgroup.centralizer (Sbar : Set A7) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hy' : y ∈
        ((S.subgroupOf E).map q).map eQ'.toMonoidHom := by
      rw [hSmap]
      exact hy
    rcases Subgroup.mem_map.mp hy' with ⟨yq, hyq, rfl⟩
    rcases Subgroup.mem_map.mp hyq with ⟨x, hxS, rfl⟩
    have hxG : (x : G) ∈ S := Subgroup.mem_subgroupOf.mp hxS
    have hcomm : f * (x : G) = (x : G) * f := by
      exact (Subgroup.mem_centralizer_iff.mp (hFcentS hfF)) (x : G) hxG |>.symm
    have hαx : α x = x := by
      apply Subtype.ext
      change f * (x : G) * f⁻¹ = (x : G)
      rw [hcomm]
      group
    have hφx : φ (q x) = q x := by
      change q (α x) = q x
      rw [hαx]
    have hinnerx := congrArg (fun ψ : MulAut (E ⧸ Subgroup.center E) =>
      ψ (q x)) hφinner
    have hinnerx' : z0 * q x * z0⁻¹ = q x := by
      simpa [MulAut.conj_apply, hφx] using hinnerx.symm
    have hinnerA := congrArg eQ' hinnerx'
    have hinnerA' : a * eQ' (q x) * a⁻¹ = eQ' (q x) := by
      simpa [z0, map_mul, map_inv] using hinnerA
    exact (mul_inv_eq_iff_eq_mul.mp (by simpa [mul_assoc] using hinnerA')).symm
  have hP0cent : P0 ≤ Subgroup.centralizer (Sbar : Set A7) := by
    apply Subgroup.zpowers_le.mpr
    exact ha_cent_Sbar
  have hkerA : P0 ≤ (MonoidHom.id A7).ker := by
    exact a7rho_centralizer_odd_trivial_of_sylow_image
      (MonoidHom.id A7) P0 (Sbar : Subgroup A7) hP0odd hP0cent Sbar
        (Subgroup.map_id _)
  have ha_one : a = 1 := by
    have haP : a ∈ P0 := Subgroup.mem_zpowers a
    have := hkerA haP
    simpa using this
  have hz0_one : z0 = 1 := by
    apply eQ'.injective
    simpa [z0] using ha_one
  have hφ_one : φ = 1 := by
    rw [hφinner, hz0_one]
    simp
  have hdelta : ∀ x : E, α x * x⁻¹ ∈ Subgroup.center E := by
    intro x
    have hqx : φ (q x) = q x := by
      rw [hφ_one]
      rfl
    have hqα : q (α x) = q x := by
      exact hqx
    have hqcomm : q (α x * x⁻¹) = 1 := by
      rw [map_mul, hqα]
      simp
    exact (QuotientGroup.eq_one_iff (N := Subgroup.center E)
      (α x * x⁻¹)).mp hqcomm
  have hαeq : α = MulEquiv.refl E :=
    central_automorphism_eq_one_local inferInstance α (MulEquiv.refl E) hdelta
  intro x hxE
  have hαx := congrArg (fun ψ : E ≃* E => ψ ⟨x, hxE⟩) hαeq
  have hαx' : f * x * f⁻¹ = x := by
    simpa [α, conjOnEquiv, conjOn] using hαx
  exact (mul_inv_eq_iff_eq_mul.mp (by simpa [mul_assoc] using hαx')).symm

/-! The source equation (3) gives a slightly weaker-looking, but sufficient,
interface than centralizing the whole component Sylow: the subgroup `F` lies
in `U`, hence centralizes the distinguished involution `t`, and equation (3)
also gives that it centralizes the chosen reflection `s`.  In the `A₇`
quotient this already kills the induced odd automorphism. -/

/-- The `A₇` Fact 1.10(ii) endpoint using the equation-(3) reflection.

An odd subgroup normalizing `E` and centralizing both the distinguished
involution and the reflected-torus involution induces an odd-order inner
automorphism on `E / Z(E)`.  Its inner representative lies in the odd
centralizer of the distinguished involution, hence in the reflected torus;
the reflection then inverts it, while centralization fixes it. -/
public theorem secondCase_a7_odd_subgroup_centralizes_component_of_reflection
    {G : Type u} [Group G] [Finite G]
    (E M F : Subgroup G)
    (hEcomp : IsComponentOf E M)
    (hEnorm : IsNormalIn E M)
    (hFleM : F ≤ M)
    (hFodd : Odd (Nat.card F))
    (t s : E)
    (hFcentT : F ≤ Subgroup.centralizer ({(t : G)} : Set G))
    (hFcentS : F ≤ Subgroup.centralizer ({(s : G)} : Set G))
    (T : Subgroup (E ⧸ Subgroup.center E))
    (hTinv : ∀ x : E ⧸ Subgroup.center E, x ∈ T →
      QuotientGroup.mk' (Subgroup.center E) s * x *
        (QuotientGroup.mk' (Subgroup.center E) s)⁻¹ = x⁻¹)
    (hTcontain : ∀ X : Subgroup (E ⧸ Subgroup.center E),
      (∀ x : E ⧸ Subgroup.center E, x ∈ X → Odd (orderOf x)) →
        X ≤ Subgroup.centralizer
          ({QuotientGroup.mk' (Subgroup.center E) t} :
            Set (E ⧸ Subgroup.center E)) → X ≤ T)
    (eQ : Nonempty ((E ⧸ Subgroup.center E) ≃*
      alternatingGroup (Fin 7))) :
    F ≤ Subgroup.centralizer (E : Set G) := by
  classical
  let : Group.IsPerfect E := (Group.isPerfect_def).2 hEcomp.2.2.2.1
  let A7 := alternatingGroup (Fin 7)
  let q : E →* E ⧸ Subgroup.center E :=
    QuotientGroup.mk' (Subgroup.center E)
  intro f hfF
  have hfM : f ∈ M := hFleM hfF
  let α : E ≃* E := conjOnEquiv E M f hfM hEnorm
  have hαcenter : Subgroup.map (↑α) (Subgroup.center E) =
      Subgroup.center E := by
    simpa only [MulEquiv.toMonoidHom_eq_coe] using map_center_local α
  let φ : E ⧸ Subgroup.center E ≃* E ⧸ Subgroup.center E :=
    QuotientGroup.congr (Subgroup.center E) (Subgroup.center E) α hαcenter
  let n : ℕ := orderOf f
  have hfn : f ^ n = 1 := by exact pow_orderOf_eq_one f
  have hφpow : φ ^ n = 1 := by
    dsimp [φ, n]
    exact quotient_conj_pow_eq_one E M f hfM hEnorm (orderOf f) hfn
  let eQ' : E ⧸ Subgroup.center E ≃* A7 := eQ.some
  let φA : MulAut A7 := MulAut.congr eQ' φ
  have hφApow : φA ^ n = 1 := by
    calc
      φA ^ n = (MulAut.congr eQ') (φ ^ n) := by simp [φA, map_pow]
      _ = (MulAut.congr eQ') 1 := by rw [hφpow]
      _ = 1 := by
        apply MulEquiv.ext
        intro x
        simp [MulAut.congr_apply]
  have hFodd_order : Odd n := by
    have hdvd : orderOf f ∣ Nat.card F := Subgroup.orderOf_dvd_natCard F hfF
    exact Odd.of_dvd_nat hFodd (by simpa [n] using hdvd)
  have hφAodd : Odd (orderOf φA) := by
    have hdvd : orderOf φA ∣ n := (orderOf_dvd_iff_pow_eq_one).2 hφApow
    exact Odd.of_dvd_nat hFodd_order hdvd
  obtain ⟨a, ha⟩ := gw_lemma_3_2_ix_a7_no_outer_automorphisms_odd_order φA hφAodd
  let z0 : E ⧸ Subgroup.center E := eQ'.symm a
  have hφinner : φ = MulAut.conj z0 := by
    apply (MulAut.congr eQ').injective
    calc
      (MulAut.congr eQ') φ = φA := rfl
      _ = MulAut.conj a := ha
      _ = (MulAut.congr eQ') (MulAut.conj z0) := by
        apply MulEquiv.ext
        intro x
        simp [z0, MulAut.congr_apply, MulAut.conj_apply]
  have hαt : α t = t := by
    apply Subtype.ext
    change f * (t : G) * f⁻¹ = (t : G)
    have hcomm := Subgroup.mem_centralizer_singleton_iff.mp (hFcentT hfF)
    calc
      f * (t : G) * f⁻¹ = ((t : G) * f) * f⁻¹ := by rw [hcomm]
      _ = (t : G) := by simp
  have hαs : α s = s := by
    apply Subtype.ext
    change f * (s : G) * f⁻¹ = (s : G)
    have hcomm := Subgroup.mem_centralizer_singleton_iff.mp (hFcentS hfF)
    calc
      f * (s : G) * f⁻¹ = ((s : G) * f) * f⁻¹ := by rw [hcomm]
      _ = (s : G) := by simp
  have hφt : φ (q t) = q t := by
    change q (α t) = q t
    rw [hαt]
  have hφs : φ (q s) = q s := by
    change q (α s) = q s
    rw [hαs]
  have hinner_t := congrArg
      (fun ψ : MulAut (E ⧸ Subgroup.center E) => ψ (q t)) hφinner
  have hz0_cent_t : z0 * q t * z0⁻¹ = q t := by
    simpa [MulAut.conj_apply, hφt] using hinner_t.symm
  have hinner_s := congrArg
      (fun ψ : MulAut (E ⧸ Subgroup.center E) => ψ (q s)) hφinner
  have hz0_cent_s : z0 * q s * z0⁻¹ = q s := by
    simpa [MulAut.conj_apply, hφs] using hinner_s.symm
  have hcenterA7 : Subgroup.center A7 = ⊥ := by
    exact alternatingGroup.center_eq_bot (by norm_num)
  have ha_conj_pow : (MulAut.conj a) ^ n = 1 := by
    rw [← ha]
    exact hφApow
  have ha_order_dvd : orderOf a ∣ n :=
    orderOf_element_dvd_of_conj_pow_eq_one hcenterA7 a ha_conj_pow
  have ha_odd : Odd (orderOf a) := Odd.of_dvd_nat hFodd_order ha_order_dvd
  have hz0_order : orderOf z0 = orderOf a := by
    exact eQ'.symm.orderOf_eq a
  let P0 : Subgroup (E ⧸ Subgroup.center E) := Subgroup.zpowers z0
  have hP0odd : Odd (Nat.card P0) := by
    rw [Nat.card_zpowers]
    simpa [hz0_order] using ha_odd
  have hP0odd_el : ∀ x : E ⧸ Subgroup.center E, x ∈ P0 →
      Odd (orderOf x) := by
    intro x hx
    exact Odd.of_dvd_nat hP0odd
      (Subgroup.orderOf_dvd_natCard P0 hx)
  have hP0cent : P0 ≤ Subgroup.centralizer
      ({q t} : Set (E ⧸ Subgroup.center E)) := by
    rw [Subgroup.zpowers_le]
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact mul_inv_eq_iff_eq_mul.mp (by simpa [mul_assoc] using hz0_cent_t)
  have hP0leT : P0 ≤ T := hTcontain P0 hP0odd_el hP0cent
  have hz0leT : z0 ∈ T := hP0leT (Subgroup.mem_zpowers z0)
  have hz0eq : z0 = z0⁻¹ := by
    have hcomm : z0 * q s = q s * z0 :=
      mul_inv_eq_iff_eq_mul.mp (by simpa [mul_assoc] using hz0_cent_s)
    calc
      z0 = (z0 * q s) * (q s)⁻¹ := by group
      _ = (q s * z0) * (q s)⁻¹ := by rw [hcomm]
      _ = z0⁻¹ := by simpa [q, mul_assoc] using hTinv z0 hz0leT
  have hz0sq : z0 ^ 2 = 1 := by
    rw [pow_two]
    calc
      z0 * z0 = z0⁻¹ * z0 := congrArg (fun x => x * z0) hz0eq
      _ = 1 := by simp
  have hz0_one : z0 = 1 := by
    have hz0P : z0 ∈ P0 := Subgroup.mem_zpowers z0
    have horderTwo : orderOf z0 ∣ 2 :=
      (orderOf_dvd_iff_pow_eq_one (x := z0) (n := 2)).2 hz0sq
    have horderCard : orderOf z0 ∣ Nat.card P0 :=
      Subgroup.orderOf_dvd_natCard P0 hz0P
    have hdivGcd : orderOf z0 ∣ Nat.gcd 2 (Nat.card P0) :=
      Nat.dvd_gcd horderTwo horderCard
    have horderOne : orderOf z0 ∣ 1 := by
      simpa [(Nat.coprime_two_left.mpr hP0odd).gcd_eq_one] using hdivGcd
    exact (orderOf_eq_one_iff (x := z0)).1 (Nat.dvd_one.mp horderOne)
  have hφ_one : φ = 1 := by
    rw [hφinner, hz0_one]
    simp
  have hdelta : ∀ x : E, α x * x⁻¹ ∈ Subgroup.center E := by
    intro x
    have hqx : φ (q x) = q x := by
      rw [hφ_one]
      rfl
    have hqα : q (α x) = q x := hqx
    have hqcomm : q (α x * x⁻¹) = 1 := by
      rw [map_mul, hqα]
      simp
    exact (QuotientGroup.eq_one_iff (N := Subgroup.center E)
      (α x * x⁻¹)).mp hqcomm
  have hαeq : α = MulEquiv.refl E :=
    central_automorphism_eq_one_local inferInstance α (MulEquiv.refl E) hdelta
  intro x hxE
  have hαx := congrArg (fun ψ : E ≃* E => ψ ⟨x, hxE⟩) hαeq
  have hαx' : f * x * f⁻¹ = x := by
    simpa [α, conjOnEquiv, conjOn] using hαx
  exact (mul_inv_eq_iff_eq_mul.mp (by simpa [mul_assoc] using hαx')).symm

end CFSG.GorensteinWalter
