module

public import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Tactic.Group

public section

namespace CFSG.RankThree.GroupTheory

open Subgroup

variable {X : Type*} [Group X]

theorem central_quotient_fixed_group_exact_sequence (Z : Subgroup X) (hZ : Z ≤ center X)
    (α : MulAut X) (hαZ : Z.map (α : X →* X) = Z) :
    haveI : Z.Normal := normal_of_le_center hZ
    let π : X →* X ⧸ Z := QuotientGroup.mk' Z
    let Q : Subgroup (X ⧸ Z) :=
      (QuotientGroup.congr Z Z α hαZ : X ⧸ Z →* X ⧸ Z).eqLocus (MonoidHom.id _)
    let H : Subgroup X := Q.comap π
    let C : Subgroup X := (α : X →* X).eqLocus (MonoidHom.id X)
    let ZA : Subgroup X := closure {w | ∃ z ∈ Z, w = z⁻¹ * α z}
    ∃ (_ : ZA.Normal) (δ : H →* Z), (∀ x : H, (δ x : X) = (x : X)⁻¹ * α x) ∧
      δ.ker.map H.subtype = C ∧ Z ≤ H ∧ ((Z.subgroupOf H).map δ).map Z.subtype = ZA ∧
      let Δ : Subgroup X := δ.range.map Z.subtype
      ZA ≤ Δ ∧ (π.comp C.subtype).ker = Z.subgroupOf C ∧ Z.subgroupOf C ≤ center C ∧
      C.map π ≤ Q ∧
      ∃ (_ : ((C.map π).subgroupOf Q).Normal) (ε : Q →* Δ ⧸ ZA.subgroupOf Δ),
        (∀ (q : Q) (x : X) (y : Δ), π x = q → (y : X) = x⁻¹ * α x →
          ε q = (y : Δ ⧸ ZA.subgroupOf Δ)) ∧
        ε.ker = (C.map π).subgroupOf Q ∧ Function.Surjective ε ∧
        (∃ e : Q ⧸ (C.map π).subgroupOf Q ≃* Δ ⧸ ZA.subgroupOf Δ,
          ∀ q : Q, e q = ε q) ∧
        (∀ a b : Δ ⧸ ZA.subgroupOf Δ, a * b = b * a) ∧
        ∀ m : ℕ, α ^ m = 1 → ∀ y : Δ ⧸ ZA.subgroupOf Δ, y ^ m = 1 := by
  have : Z.Normal := normal_of_le_center hZ
  intro π Q H C ZA
  have hαmem : ∀ z ∈ Z, α z ∈ Z := fun z hz => hαZ ▸ mem_map_of_mem (α : X →* X) hz
  have hcent : ∀ z ∈ Z, ∀ g : X, z * g = g * z := fun z hz g =>
    (mem_center_iff.mp (hZ hz) g).symm
  have hH : ∀ x : X, x ∈ H ↔ x⁻¹ * α x ∈ Z := by
    intro x
    change QuotientGroup.congr Z Z α hαZ (x : X ⧸ Z) = (x : X ⧸ Z) ↔ _
    rw [QuotientGroup.congr_mk, eq_comm, QuotientGroup.eq]
  let δ : H →* Z :=
    { toFun := fun x => ⟨(x : X)⁻¹ * α x, (hH x).mp x.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => by
        apply Subtype.ext
        change ((x : X) * y)⁻¹ * α ((x : X) * y) = ((x : X)⁻¹ * α x) * ((y : X)⁻¹ * α y)
        have h := hcent _ ((hH x).mp x.2) (y : X)⁻¹
        calc ((x : X) * y)⁻¹ * α ((x : X) * y) = (y : X)⁻¹ * ((x : X)⁻¹ * α x) * α y := by
              rw [map_mul]; group
          _ = ((x : X)⁻¹ * α x) * ((y : X)⁻¹ * α y) := by rw [← h]; group }
  have hδ : ∀ x : H, (δ x : X) = (x : X)⁻¹ * α x := fun _ => rfl
  have hδker : δ.ker.map H.subtype = C := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have h1 : (y : X)⁻¹ * α y = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hy)
      rw [inv_mul_eq_one] at h1
      exact h1.symm
    · intro hx
      have hx' : α x = x := hx
      have hxH : x ∈ H := (hH x).mpr (by rw [hx', inv_mul_cancel]; exact one_mem Z)
      refine ⟨⟨x, hxH⟩, MonoidHom.mem_ker.mpr (Subtype.ext ?_), rfl⟩
      change x⁻¹ * α x = 1
      rw [hx', inv_mul_cancel]
  have hZH : Z ≤ H := fun z hz => (hH z).mpr (mul_mem (inv_mem hz) (hαmem z hz))
  have hδZ : ((Z.subgroupOf H).map δ).map Z.subtype = ZA := by
    apply le_antisymm
    · rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      exact subset_closure ⟨y, hy, rfl⟩
    · refine (closure_le _).mpr ?_
      rintro _ ⟨z, hz, rfl⟩
      exact ⟨δ ⟨z, hZH hz⟩, ⟨⟨z, hZH hz⟩, hz, rfl⟩, rfl⟩
  have hZAZ : ZA ≤ Z := (closure_le _).mpr (by
    rintro _ ⟨z, hz, rfl⟩
    exact mul_mem (inv_mem hz) (hαmem z hz))
  have hZAn : ZA.Normal := normal_of_le_center (hZAZ.trans hZ)
  refine ⟨hZAn, δ, hδ, hδker, hZH, hδZ, ?_⟩
  intro Δ
  have hΔZ : Δ ≤ Z := map_subtype_le _
  have hZAΔ : ZA ≤ Δ := by
    rw [← hδZ]
    exact map_mono (map_le_range _ _)
  have hker : (π.comp C.subtype).ker = Z.subgroupOf C := by
    ext x
    exact QuotientGroup.eq_one_iff (x : X)
  have hcenter : Z.subgroupOf C ≤ center C := by
    intro x hx
    rw [mem_center_iff]
    intro g
    exact Subtype.ext (hcent _ hx g).symm
  have hCQ : C.map π ≤ Q := by
    rintro _ ⟨x, hx, rfl⟩
    have hx' : α x = x := hx
    change QuotientGroup.congr Z Z α hαZ (x : X ⧸ Z) = (x : X ⧸ Z)
    rw [QuotientGroup.congr_mk, hx']
  let πH : H →* Q := (π.comp H.subtype).codRestrict Q fun x => x.2
  have hπH : Function.Surjective πH := by
    rintro ⟨q, hq⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective Z q
    exact ⟨⟨x, hq⟩, rfl⟩
  let δΔ : H →* Δ := (Z.subtype.comp δ).codRestrict Δ fun x => ⟨δ x, ⟨x, rfl⟩, rfl⟩
  let δbar : H →* Δ ⧸ ZA.subgroupOf Δ := (QuotientGroup.mk' _).comp δΔ
  have hδbar : ∀ x : H, δbar x = 1 ↔ (x : X)⁻¹ * α x ∈ ZA := fun x =>
    QuotientGroup.eq_one_iff (δΔ x)
  have hkerle : πH.ker ≤ δbar.ker := by
    intro x hx
    have hxZ : (x : X) ∈ Z :=
      (QuotientGroup.eq_one_iff (x : X)).mp (congrArg Subtype.val (MonoidHom.mem_ker.mp hx))
    exact MonoidHom.mem_ker.mpr ((hδbar x).mpr (subset_closure ⟨x, hxZ, rfl⟩))
  let ε : Q →* Δ ⧸ ZA.subgroupOf Δ :=
    πH.liftOfRightInverse (Function.surjInv hπH) (Function.rightInverse_surjInv hπH)
      ⟨δbar, hkerle⟩
  have hε : ∀ x : H, ε (πH x) = δbar x := fun x =>
    πH.liftOfRightInverse_comp_apply _ _ ⟨δbar, hkerle⟩ x
  have hεker : ε.ker = (C.map π).subgroupOf Q := by
    ext q
    obtain ⟨x, rfl⟩ := hπH q
    rw [MonoidHom.mem_ker, hε, hδbar, mem_subgroupOf]
    constructor
    · intro h
      rw [← hδZ] at h
      obtain ⟨_, ⟨z, hz, rfl⟩, hzx⟩ := h
      have hδeq : δ z = δ x := Subtype.ext hzx
      refine ⟨(x : X) * (z : X)⁻¹, ?_, ?_⟩
      · have hmem : x * z⁻¹ ∈ δ.ker := by
          rw [MonoidHom.mem_ker, map_mul, map_inv, ← hδeq, mul_inv_cancel]
        have h2 := mem_map_of_mem H.subtype hmem
        rwa [hδker] at h2
      · have hπz : π (z : X) = 1 := (QuotientGroup.eq_one_iff (z : X)).mpr hz
        change π ((x : X) * (z : X)⁻¹) = π x
        rw [map_mul, map_inv, hπz, inv_one, mul_one]
    · rintro ⟨c, hc, hcx⟩
      have hc' : α c = c := hc
      have hcH : c ∈ H := (hH c).mpr (by rw [hc', inv_mul_cancel]; exact one_mem Z)
      have hq : πH x = πH ⟨c, hcH⟩ := Subtype.ext hcx.symm
      rw [← hδbar, ← hε, hq, hε, hδbar]
      change c⁻¹ * α c ∈ ZA
      rw [hc', inv_mul_cancel]
      exact one_mem ZA
  have hεsurj : Function.Surjective ε := by
    intro w
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective _ w
    obtain ⟨_, ⟨x, rfl⟩, hyx⟩ := y.2
    refine ⟨πH x, ?_⟩
    rw [hε]
    change QuotientGroup.mk' _ (δΔ x) = QuotientGroup.mk' _ y
    congr 1
    exact Subtype.ext hyx
  have hεformula : ∀ (q : Q) (x : X) (y : Δ), π x = q → (y : X) = x⁻¹ * α x →
      ε q = (y : Δ ⧸ ZA.subgroupOf Δ) := by
    intro q x y hxq hy
    have hxH : x ∈ H := by
      change π x ∈ Q
      rw [hxq]
      exact q.2
    have hq : q = πH ⟨x, hxH⟩ := Subtype.ext hxq.symm
    rw [hq, hε]
    change QuotientGroup.mk' _ (δΔ ⟨x, hxH⟩) = QuotientGroup.mk' _ y
    congr 1
    exact Subtype.ext hy.symm
  have hMn : ((C.map π).subgroupOf Q).Normal := hεker ▸ ε.normal_ker
  refine ⟨hZAΔ, hker, hcenter, hCQ, hMn, ε, hεformula, hεker, hεsurj,
    ⟨(QuotientGroup.quotientMulEquivOfEq hεker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective ε hεsurj), fun q => rfl⟩, ?_, ?_⟩
  · intro a b
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective _ a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective _ b
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hcent _ (hΔZ a.2) b)
  · intro m hm y
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective _ y
    obtain ⟨_, ⟨x, rfl⟩, hyx⟩ := y.2
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_subgroupOf, coe_pow,
      ← hyx]
    let ρ : X →* X ⧸ ZA := QuotientGroup.mk' ZA
    have hρZ : ∀ w ∈ Z, ρ (α w) = ρ w := by
      intro w hw
      have hgen : w⁻¹ * α w ∈ ZA := subset_closure ⟨w, hw, rfl⟩
      exact (QuotientGroup.eq.mpr hgen).symm
    have hρpow : ∀ i : ℕ, ∀ w ∈ Z, ρ ((α ^ i) w) = ρ w := by
      intro i
      induction i with
      | zero => intro w _; rw [pow_zero, MulAut.one_apply]
      | succ i ih =>
        intro w hw
        rw [pow_succ, MulAut.mul_apply, ih _ (hαmem w hw), hρZ w hw]
    have key : ∀ i : ℕ, ρ ((α ^ i) (x : X)) = ρ x * ρ (δ x) ^ i := by
      intro i
      induction i with
      | zero => rw [pow_zero, MulAut.one_apply, pow_zero, mul_one]
      | succ i ih =>
        have hαx : α (x : X) = x * (δ x : X) := by
          rw [hδ]
          group
        rw [pow_succ, MulAut.mul_apply, hαx, map_mul, map_mul, ih, hρpow i _ (δ x).2,
          pow_succ, mul_assoc]
    have h := key m
    rw [hm, MulAut.one_apply, left_eq_mul, ← map_pow] at h
    exact (QuotientGroup.eq_one_iff _).mp h

end CFSG.RankThree.GroupTheory
