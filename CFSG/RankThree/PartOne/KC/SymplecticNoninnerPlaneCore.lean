module

public import CFSG.RankThree.PartOne.KC.SymplecticNoninnerPlaneDescent
public import CFSG.RankThree.PartOne.KC.PlaneReduction

public section

namespace CFSG.RankThree.PartOne.KCSpComm

open Polynomial CFSG CFSG.RankThree.LocalRank CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.ComponentClassification.OuterAutomorphisms (inner inner_normal)

@[expose] def spFixedGroup {T : Type*} [Group T] (a : MulAut T) : Subgroup T where
  carrier := {x | a x = x}
  mul_mem' {x y} hx hy := by
    have hx' : a x = x := hx
    have hy' : a y = y := hy
    show a (x * y) = x * y
    rw [map_mul, hx', hy']
  one_mem' := map_one a
  inv_mem' {x} hx := by
    have hx' : a x = x := hx
    show a x⁻¹ = x⁻¹
    rw [map_inv, hx']

theorem mem_spFixedGroup {T : Type*} [Group T] {a : MulAut T} {x : T} :
    x ∈ spFixedGroup a ↔ a x = x := Iff.rfl

@[expose] def SymplecticSubfieldClause : Prop :=
  ∀ (ℓ f r p : ℕ) (K : Type) [Field K] [Finite K], ℓ.Prime → p.Prime → 3 < p → p ≠ ℓ → 1 ≤ f →
    2 ≤ r → Nat.card K = ℓ ^ f → ∀ σ : K ≃+* K, orderOf σ = p →
      solvableRadical ↥(spFixedGroup (fieldAut r K σ)) = ⊥ ∧
      Subgroup.centralizer (((spFixedGroup (fieldAut r K σ)).map
        (MulAut.conj : StatedProj (StatedSp r K) →* MulAut (StatedProj (StatedSp r K))) :
          Subgroup (MulAut (StatedProj (StatedSp r K)))) :
            Set (MulAut (StatedProj (StatedSp r K)))) = Subgroup.zpowers (fieldAut r K σ)

theorem conj_mem_inner {T : Type*} [Group T] (g : T) : (MulAut.conj g : MulAut T) ∈ inner T :=
  MonoidHom.mem_range.mpr ⟨g, rfl⟩

theorem mulAut_conj_apply_conj {T : Type*} [Group T] (a : MulAut T) (g : T) :
    a * MulAut.conj g * a⁻¹ = MulAut.conj (a g) := by
  ext x
  simp [MulAut.mul_apply, MulAut.conj_apply]

theorem conj_mem_centralizer_iff {T : Type*} [Group T]
    (hinj : Function.Injective (MulAut.conj : T →* MulAut T)) (a : MulAut T) (g : T) :
    (MulAut.conj g : MulAut T) ∈ Subgroup.centralizer ({a} : Set (MulAut T)) ↔ a g = g := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have h1 : a * MulAut.conj g * a⁻¹ = MulAut.conj g := by
      rw [← h]
      group
    rw [mulAut_conj_apply_conj] at h1
    exact hinj h1
  · intro h
    have h1 := mulAut_conj_apply_conj a g
    rw [h] at h1
    calc MulAut.conj g * a = (a * MulAut.conj g * a⁻¹) * a := by rw [h1]
      _ = a * MulAut.conj g := by group

section Core

variable {r : ℕ} {K : Type} [Field K] [Finite K]

theorem core_fieldAut_eq_bot (hsub : SymplecticSubfieldClause) {ℓ f p : ℕ} (hℓ : ℓ.Prime)
    (hf : 1 ≤ f) (hr : 2 ≤ r) (hK : Nat.card K = ℓ ^ f) (hp : p.Prime) (hp3 : 3 < p)
    (hpℓ : p ≠ ℓ) (hq : 4 ≤ Nat.card K) (hinjF : Function.Injective (fieldAut r K))
    {σ : K ≃+* K} (hσ : orderOf σ = p) {B : Subgroup (MulAut (StatedProj (StatedSp r K)))}
    (hB : inner (StatedProj (StatedSp r K)) ≤ B) :
    inSubgroup (aschbacherSolvableCore p)
      (B ⊓ Subgroup.centralizer {fieldAut r K σ}) = ⊥ := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hrad, hcent⟩ := hsub ℓ f r p K hℓ hp hp3 hpℓ hf hr hK σ hσ
  have hinj := KCSymplectic.conj_injective_statedProj_statedSp (r := r) (K := K) hr hq
  set a : MulAut (StatedProj (StatedSp r K)) := fieldAut r K σ with ha
  have haord : orderOf a = p := by
    rw [ha, orderOf_injective _ hinjF σ, hσ]
  set C : Subgroup (MulAut (StatedProj (StatedSp r K))) := B ⊓ Subgroup.centralizer {a} with hC
  set S : Subgroup (MulAut (StatedProj (StatedSp r K))) :=
    inSubgroup (aschbacherSolvableCore p) C with hS
  obtain ⟨hsolv, -, hpS, -⟩ := solvable_prime_complement_core_characterization (H := ↥C) hp
  have hSsolv : Group.IsSolvable ↥S := by
    have e := (aschbacherSolvableCore p ↥C).equivMapOfInjective C.subtype C.subtype_injective
    exact Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective
  have hSord : ∀ s ∈ S, ¬ p ∣ orderOf s := by
    intro s hs hdvd
    have h1 : orderOf s ∣ Nat.card ↥S := Subgroup.orderOf_dvd_natCard S hs
    have h2 : Nat.card ↥S = Nat.card ↥(aschbacherSolvableCore p ↥C) := by
      rw [hS, inSubgroup, Subgroup.card_map_of_injective C.subtype_injective]
    exact hpS (h2 ▸ hdvd.trans h1)
  have hSnorm : ∀ c ∈ C, ∀ s ∈ S, c * s * c⁻¹ ∈ S := fun c hc s hs =>
    conj_mem_inSubgroup_core p C hc hs
  let Fix : Subgroup (StatedProj (StatedSp r K)) := spFixedGroup a
  let φ0 : ↥Fix →* MulAut (StatedProj (StatedSp r K)) :=
    (MulAut.conj : StatedProj (StatedSp r K) →* MulAut (StatedProj (StatedSp r K))).comp
      Fix.subtype
  have hφ0inj : Function.Injective φ0 := fun x y h => Subtype.ext (hinj h)
  have hφ0C : ∀ g : ↥Fix, φ0 g ∈ C := fun g =>
    ⟨hB (conj_mem_inner (g : StatedProj (StatedSp r K))),
      (conj_mem_centralizer_iff hinj a g).mpr g.2⟩
  let N0 : Subgroup ↥Fix := S.comap φ0
  have hN0normal : N0.Normal :=
    ⟨fun n hn g => by
      show φ0 (g * n * g⁻¹) ∈ S
      rw [map_mul, map_mul, map_inv]
      exact hSnorm _ (hφ0C g) _ hn⟩
  have hN0solv : Group.IsSolvable ↥N0 := by
    let ψ : ↥N0 →* ↥S := (φ0.comp N0.subtype).codRestrict S (fun n => n.2)
    have hψ : Function.Injective ψ := fun x y h =>
      Subtype.ext (hφ0inj (congrArg Subtype.val h))
    exact Group.isSolvable_of_isSolvable_injective hψ
  have hN0bot : N0 = ⊥ := by
    have h1 : N0 ≤ solvableRadical ↥Fix := le_sSup ⟨hN0normal, hN0solv⟩
    rw [hrad] at h1
    exact le_bot_iff.mp h1
  have hScent : ∀ s ∈ S, s ∈ Subgroup.centralizer
      ((Fix.map (MulAut.conj : StatedProj (StatedSp r K) →*
        MulAut (StatedProj (StatedSp r K))) : Subgroup (MulAut (StatedProj (StatedSp r K)))) :
          Set (MulAut (StatedProj (StatedSp r K)))) := by
    intro s hs
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨g, hg, rfl⟩
    have hsC : s ∈ C := inSubgroup_core_le p C hs
    have hgC : (MulAut.conj g : MulAut (StatedProj (StatedSp r K))) ∈ C :=
      hφ0C ⟨g, hg⟩
    have hhinner : s * MulAut.conj g * s⁻¹ ∈ inner (StatedProj (StatedSp r K)) :=
      (inner_normal (StatedProj (StatedSp r K))).conj_mem _ (conj_mem_inner g) s
    obtain ⟨g', hg'⟩ := hhinner
    have hg'fix : a g' = g' := by
      refine (conj_mem_centralizer_iff hinj a g').mp ?_
      rw [hg']
      exact mul_mem (mul_mem hsC.2 hgC.2) (inv_mem hsC.2)
    have hcomm : (MulAut.conj (g' * g⁻¹) : MulAut (StatedProj (StatedSp r K))) =
        s * (MulAut.conj g * s⁻¹ * (MulAut.conj g)⁻¹) := by
      rw [map_mul, map_inv, hg']
      group
    have hmem : (⟨g' * g⁻¹, Fix.mul_mem hg'fix (Fix.inv_mem hg)⟩ : ↥Fix) ∈ N0 := by
      show MulAut.conj (g' * g⁻¹) ∈ S
      rw [hcomm]
      exact mul_mem hs (hSnorm _ hgC _ (inv_mem hs))
    rw [hN0bot, Subgroup.mem_bot] at hmem
    have hgg : g' = g := by
      have := congrArg Subtype.val hmem
      simpa [mul_inv_eq_one] using this
    rw [hgg] at hg'
    show MulAut.conj g * s = s * MulAut.conj g
    have h2 : s * MulAut.conj g * s⁻¹ = MulAut.conj g := hg'.symm
    calc MulAut.conj g * s = (s * MulAut.conj g * s⁻¹) * s := by rw [h2]
      _ = s * MulAut.conj g := by group
  refine eq_bot_iff.mpr fun s hs => ?_
  have hsz : s ∈ Subgroup.zpowers a := by
    rw [← hcent]
    exact hScent s hs
  have hdvd : orderOf s ∣ p := by
    have := orderOf_dvd_of_mem_zpowers hsz
    rwa [haord] at this
  rcases (Nat.dvd_prime hp).mp hdvd with h1 | h1
  · exact Subgroup.mem_bot.mpr (orderOf_eq_one_iff.mp h1)
  · exact absurd (h1 ▸ dvd_refl p) (hSord s hs)

end Core

theorem core_eq_bot_of_conjugate {M : Type*} [Group M] [Finite M] {p : ℕ} (hp : p.Prime)
    {H : Subgroup M} [H.Normal] {B : Subgroup M} (hB : H ≤ B) {a b h : M}
    (hab : a = h * b * h⁻¹)
    (hcore : ∀ B' : Subgroup M, H ≤ B' →
      inSubgroup (aschbacherSolvableCore p) (B' ⊓ Subgroup.centralizer {b}) = ⊥) :
    inSubgroup (aschbacherSolvableCore p) (B ⊓ Subgroup.centralizer {a}) = ⊥ := by
  set φ : M ≃* M := MulAut.conj h⁻¹ with hφ
  have hφa : φ a = b := by
    rw [hφ, MulAut.conj_apply, hab]
    group
  have h1 := map_inSubgroup_theta_centralizer_mulEquiv hp φ B a
  rw [hφa, hcore (B.map φ.toMonoidHom) ?_] at h1
  · exact (Subgroup.map_eq_bot_iff_of_injective _ φ.injective).mp h1
  · intro y hy
    refine ⟨h * y * h⁻¹, hB ((inferInstance : H.Normal).conj_mem y hy h), ?_⟩
    show h⁻¹ * (h * y * h⁻¹) * h⁻¹⁻¹ = y
    group

section Noninner

variable {r : ℕ} {K : Type} [Field K] [Finite K] {ℓ f p : ℕ}

theorem core_eq_bot_of_noninner (hsub : SymplecticSubfieldClause) (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hr : 2 ≤ r) (hK : Nat.card K = ℓ ^ f) (O : SpOuter ℓ f r K) (hp : p.Prime) (hp3 : 3 < p)
    (hpℓ : p ≠ ℓ) {A : Subgroup (MulAut (StatedProj (StatedSp r K)))}
    [IsElementaryAbelian p A] {B : Subgroup (MulAut (StatedProj (StatedSp r K)))}
    (hB : inner (StatedProj (StatedSp r K)) ≤ B)
    {a : MulAut (StatedProj (StatedSp r K))} (ha : a ∈ A)
    (haH : a ∉ inner (StatedProj (StatedSp r K))) :
    inSubgroup (aschbacherSolvableCore p) (B ⊓ Subgroup.centralizer {a}) = ⊥ := by
  have : NeZero r := ⟨by omega⟩
  obtain ⟨hpf, σ, hσ, h, -, hah⟩ := noninner_element_data O hp (by omega) ha haH
  have hq : 4 ≤ Nat.card K := by
    have hfp : p ≤ f := Nat.le_of_dvd (by omega) hpf
    rw [hK]
    calc 4 ≤ 2 ^ p := by
          calc 4 = 2 ^ 2 := by norm_num
            _ ≤ 2 ^ p := Nat.pow_le_pow_right (by norm_num) hp.two_le
      _ ≤ ℓ ^ p := Nat.pow_le_pow_left hℓ.two_le p
      _ ≤ ℓ ^ f := Nat.pow_le_pow_right hℓ.pos hfp
  have := inner_normal (StatedProj (StatedSp r K))
  exact core_eq_bot_of_conjugate hp hB hah fun B' hB' =>
    core_fieldAut_eq_bot hsub hℓ hf hr hK hp hp3 hpℓ hq O.fieldAut_injective hσ hB'

end Noninner

end CFSG.RankThree.PartOne.KCSpComm
