module

public import CFSG.LocalAnalysis.StandardType.GGForkJrPumpDefs
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelAut

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Internal

variable {G : Type} [Group G] [Finite G]

section CartanHelpers

variable {p : ℕ} [Fact p.Prime] {Bs : Subgroup G} {V : Type*} [AddCommGroup V]
  [Module (ZMod p) V]

private def ggZbar (ι : Additive ↥Bs ≃+ V) (X : Subgroup G) : Submodule (ZMod p) V :=
  AddSubgroup.toZModSubmodule p
    { carrier := {v | ∃ b : ↥Bs, (b : G) ∈ Subgroup.centralizer (X : Set G) ∧
        ι (Additive.ofMul b) = v}
      add_mem' := by
        rintro v w ⟨b, hb, rfl⟩ ⟨c, hc, rfl⟩
        refine ⟨b * c, ?_, ?_⟩
        · rw [Subgroup.coe_mul]
          exact Subgroup.mul_mem _ hb hc
        · rw [ofMul_mul, map_add]
      zero_mem' := by
        refine ⟨1, Subgroup.one_mem _, ?_⟩
        rw [ofMul_one, map_zero]
      neg_mem' := by
        rintro v ⟨b, hb, rfl⟩
        refine ⟨b⁻¹, ?_, ?_⟩
        · rw [Subgroup.coe_inv]
          exact Subgroup.inv_mem _ hb
        · rw [ofMul_inv, map_neg] }

private theorem mem_ggZbar_iff (ι : Additive ↥Bs ≃+ V) (X : Subgroup G) (v : V) :
    v ∈ ggZbar (p := p) ι X ↔ ∃ b : ↥Bs, (b : G) ∈ Subgroup.centralizer (X : Set G) ∧
        ι (Additive.ofMul b) = v := by
  rw [ggZbar, AddSubgroup.mem_toZModSubmodule]
  rfl

private theorem ggZbar_iff (hBs : IsElemAbelian p Bs) (ι : Additive ↥Bs ≃+ V) (X : Subgroup G)
    (b b' : ↥Bs) :
    ((b : G))⁻¹ * (b' : G) ∈ Subgroup.centralizer (X : Set G) ↔
      ι (Additive.ofMul b') - ι (Additive.ofMul b) ∈ ggZbar (p := p) ι X := by
  rw [mem_ggZbar_iff]
  constructor
  · intro h
    refine ⟨b⁻¹ * b', ?_, ?_⟩
    · have hc : ((b⁻¹ * b' : ↥Bs) : G) = (b : G)⁻¹ * (b' : G) := by
        rw [Subgroup.coe_mul, Subgroup.coe_inv]
      rwa [hc]
    · rw [ofMul_mul, ofMul_inv, map_add, map_neg]
      abel
  · rintro ⟨c, hc, hcv⟩
    have hcc : Additive.ofMul c = Additive.ofMul b' - Additive.ofMul b := by
      apply ι.injective
      rw [map_sub]
      exact hcv
    have hcc' : c = b' * b⁻¹ := by
      apply Additive.ofMul.injective
      rw [ofMul_mul, ofMul_inv, ← sub_eq_add_neg]
      exact hcc
    have hcb : c = b⁻¹ * b' := by
      rw [hcc']
      exact hBs.1.is_comm.comm b' b⁻¹
    have hc'' : ((c : ↥Bs) : G) = (b : G)⁻¹ * (b' : G) := by
      rw [hcb, Subgroup.coe_mul, Subgroup.coe_inv]
    rwa [← hc'']

private theorem ggLin_fix_ggZbar (ι : Additive ↥Bs ≃+ V) {X : Subgroup G} {t : MulAut ↥Bs}
    (ht : t ∈ ggInduced X Bs) {v : V} (hv : v ∈ ggZbar (p := p) ι X) :
    ggLin (p := p) ι t v = v := by
  rw [mem_ggZbar_iff] at hv
  obtain ⟨b, hb, rfl⟩ := hv
  obtain ⟨g, hgX, -, hgt⟩ := ht
  have hgb : g * (b : G) = (b : G) * g := (Subgroup.mem_centralizer_iff.mp hb) g hgX
  have htb : t b = b := by
    apply Subtype.ext
    rw [hgt b, hgb]
    group
  rw [ggLin_apply_ofMul, htb]

private theorem ggCartan_scale {K : Type*} [Field K] (h2 : (2 : K) ≠ 0) {V' : Type*}
    [AddCommGroup V'] [Module K V'] (Z : Submodule K V') {Y : Type*} (P : Y → V') (a : Y → K)
    {w : Y} (hw : a w = 2) (hsurj : ∀ v : V', ∃ y, v - P y ∈ Z) {h : V'} {α : Module.Dual K V'}
    (hαh : α h = 2) (hαZ : ∀ z ∈ Z, α z = 0)
    (hrel : ∀ y, a y • P w - α (P y) • h ∈ Z) :
    ∃ μ : K, μ ≠ 0 ∧ (∀ y, α (P y) = μ * a y) ∧ P w - μ • h ∈ Z := by
  let μ : K := α (P w) * (2 : K)⁻¹
  have hhZ : h ∉ Z := by
    intro hh
    have hz := hαZ h hh
    rw [hαh] at hz
    exact h2 hz
  have hrelw : (2 : K) • P w - α (P w) • h ∈ Z := by
    have hh := hrel w
    rwa [hw] at hh
  have hcne : α (P w) ≠ 0 := by
    intro hc0
    have h2P : (2 : K) • P w ∈ Z := by
      have hh := hrelw
      rwa [hc0, zero_smul, sub_zero] at hh
    have hP : P w ∈ Z := by
      have hh := Z.smul_mem ((2 : K)⁻¹) h2P
      rwa [smul_smul, inv_mul_cancel₀ h2, one_smul] at hh
    have hαyZ : ∀ y, α (P y) • h ∈ Z := by
      intro y
      have hy := hrel y
      have hay : a y • P w ∈ Z := Z.smul_mem (a y) hP
      have hh := Z.sub_mem hay hy
      convert hh using 1
      abel
    obtain ⟨y, hy⟩ := hsurj h
    have hαPy0 : α (P y) = 0 := by
      by_contra hne
      have hhZ' : h ∈ Z := by
        have hh := Z.smul_mem ((α (P y))⁻¹) (hαyZ y)
        rwa [smul_smul, inv_mul_cancel₀ hne, one_smul] at hh
      exact hhZ hhZ'
    have hz := hαZ (h - P y) hy
    rw [map_sub, hαPy0, sub_zero] at hz
    rw [hαh] at hz
    exact h2 hz
  refine ⟨μ, ?_, ?_, ?_⟩
  · exact mul_ne_zero hcne (inv_ne_zero h2)
  · intro y
    have hPw : P w - μ • h ∈ Z := by
      have hh := Z.smul_mem ((2 : K)⁻¹) hrelw
      have heq : (2 : K)⁻¹ • ((2 : K) • P w - α (P w) • h) = P w - μ • h := by
        rw [smul_sub, smul_smul, smul_smul, inv_mul_cancel₀ h2, one_smul, mul_comm]
      rwa [heq] at hh
    have hy := hrel y
    have h1 : a y • (P w - μ • h) ∈ Z := Z.smul_mem (a y) hPw
    have h2' := Z.sub_mem h1 hy
    have hz : (α (P y) - a y * μ) • h ∈ Z := by
      convert h2' using 1
      rw [smul_sub, smul_smul, sub_smul]
      abel
    have hcoef : α (P y) - a y * μ = 0 := by
      by_contra hne
      have hhZ' : h ∈ Z := by
        have hh := Z.smul_mem ((α (P y) - a y * μ)⁻¹) hz
        rwa [smul_smul, inv_mul_cancel₀ hne, one_smul] at hh
      exact hhZ hhZ'
    have hcoef' : α (P y) = a y * μ := sub_eq_zero.mp hcoef
    rw [hcoef', mul_comm]
  · have hh := Z.smul_mem ((2 : K)⁻¹) hrelw
    have heq : (2 : K)⁻¹ • ((2 : K) • P w - α (P w) • h) = P w - μ • h := by
      rw [smul_sub, smul_smul, smul_smul, inv_mul_cancel₀ h2, one_smul, mul_comm]
    rwa [heq] at hh

end CartanHelpers

theorem ggAutLattice_cartan {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {Bs X : Subgroup G}
    (hBs : IsElemAbelian p Bs) {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    (ι : Additive ↥Bs ≃+ V) (hX : GGAutLattice p Bs X) {κ : Type*} {t : κ → MulAut ↥Bs}
    {h : κ → V} {α : κ → Module.Dual (ZMod p) V} (ht : ∀ k, t k ∈ ggInduced X Bs)
    (hα : ∀ k, α k (h k) = 2) (hlin : ∀ k w, ggLin (p := p) ι (t k) w = w - α k w • h k) :
    ∃ (m : ℕ) (Q : Matrix (Fin m) (Fin m) ℤ) (v : κ → Fin m → ℤ) (μ : κ → ZMod p),
      GGLatForm Q ∧ (∀ k, GGLatRoot Q (v k)) ∧ (∀ k, μ k ≠ 0) ∧
      (∀ j k, α j (h k) * μ k = μ j * (ggLatCartan Q (v k) (v j) : ZMod p)) ∧
      (∀ j k, (∀ y, ggLatRefl Q (v j) y = ggLatRefl Q (v k) y) →
        ∀ b : ↥Bs, ((t j b : ↥Bs) : G)⁻¹ * ((t k b : ↥Bs) : G) ∈
          Subgroup.centralizer (X : Set G)) ∧
      (∀ i j k, (∀ y, ggLatRefl Q (v j) y =
          ggLatRefl Q (v i) (ggLatRefl Q (v k) (ggLatRefl Q (v i) y))) →
        ∀ b : ↥Bs, ((t j b : ↥Bs) : G)⁻¹ * (((t i * t k * t i) b : ↥Bs) : G) ∈
          Subgroup.centralizer (X : Set G)) := by
  obtain ⟨m, Q, π, hQ, hsurj, hrefl⟩ := hX
  let P : (Fin m → ℤ) →+ V := ι.toAddMonoidHom.comp π
  have hP : ∀ y, P y = ι (π y) := fun _ => rfl
  have hsurjZ : ∀ v : V, ∃ y : Fin m → ℤ, v - P y ∈ ggZbar (p := p) ι X := by
    intro v
    obtain ⟨y, hy⟩ := hsurj (Additive.toMul (ι.symm v))
    refine ⟨y, ?_⟩
    have hh := (ggZbar_iff (p := p) hBs ι X (Additive.toMul (π y))
      (Additive.toMul (ι.symm v))).mp hy
    rw [ofMul_toMul, ofMul_toMul, AddEquiv.apply_symm_apply] at hh
    simpa [P, hP] using hh
  have hreflect : ∀ k, GGIsReflection p (t k) := fun k =>
    ggIsReflection_of_eq_reflection hp2 ι (hα k) (ggLin_eq_reflection ι (hα k) (hlin k))
  have hchoose : ∀ k, ∃ w : Fin m → ℤ, GGLatRoot Q w ∧
      ∀ y, ((t k (Additive.toMul (π y)) : ↥Bs) : G)⁻¹ *
        ((Additive.toMul (π (ggLatRefl Q w y)) : ↥Bs) : G) ∈
        Subgroup.centralizer (X : Set G) :=
    fun k => hrefl (t k) (ht k) (hreflect k)
  choose w hw using hchoose
  have hwroot : ∀ k, GGLatRoot Q (w k) := fun k => (hw k).1
  have hwrel : ∀ k y, ((t k (Additive.toMul (π y)) : ↥Bs) : G)⁻¹ *
      ((Additive.toMul (π (ggLatRefl Q (w k) y)) : ↥Bs) : G) ∈
      Subgroup.centralizer (X : Set G) := fun k => (hw k).2
  have hR : ∀ k y, P (ggLatRefl Q (w k) y) - ggLin (p := p) ι (t k) (P y) ∈
      ggZbar (p := p) ι X := by
    intro k y
    have hh := (ggZbar_iff (p := p) hBs ι X (t k (Additive.toMul (π y)))
      (Additive.toMul (π (ggLatRefl Q (w k) y)))).mp (hwrel k y)
    rw [ofMul_toMul] at hh
    have hP1 : P (ggLatRefl Q (w k) y) = ι (π (ggLatRefl Q (w k) y)) := hP _
    have hP2 : P y = ι (Additive.ofMul (Additive.toMul (π y))) := by rw [hP, ofMul_toMul]
    rw [hP1, hP2, ggLin_apply_ofMul]
    exact hh
  have hCong : ∀ k (v : V) (y : Fin m → ℤ), v - P y ∈ ggZbar (p := p) ι X →
      ggLin (p := p) ι (t k) v - P (ggLatRefl Q (w k) y) ∈ ggZbar (p := p) ι X := by
    intro k v y hvy
    have h1 : ggLin (p := p) ι (t k) (v - P y) = v - P y :=
      ggLin_fix_ggZbar (p := p) ι (ht k) hvy
    rw [map_sub] at h1
    have h3 : ggLin (p := p) ι (t k) v - ggLin (p := p) ι (t k) (P y) ∈
        ggZbar (p := p) ι X := by
      rw [h1]
      exact hvy
    have h4 := (ggZbar (p := p) ι X).sub_mem h3 (hR k y)
    convert h4 using 1
    abel
  have hw2 : ∀ k, (ggLatCartan Q (w k) (w k) : ZMod p) = 2 := by
    intro k
    have hpos : 0 < dotProduct (w k) (Q.mulVec (w k)) := hQ.2 (w k) (hwroot k).1
    have hcart : ggLatCartan Q (w k) (w k) = 2 := by
      unfold ggLatCartan
      exact Int.mul_ediv_cancel 2 hpos.ne'
    rw [hcart]
    norm_num
  have hk0 : ∀ k, h k ≠ 0 := by
    intro k hk
    have hh := hα k
    rw [hk, map_zero] at hh
    exact zmod_two_ne_zero hp2 hh.symm
  have hαZ : ∀ k z, z ∈ ggZbar (p := p) ι X → α k z = 0 := by
    intro k z hz
    have hfix := ggLin_fix_ggZbar (p := p) ι (ht k) hz
    have hz2 := hlin k z
    rw [hfix] at hz2
    have hz0 : α k z • h k = 0 := by
      have h3 : z - (z - α k z • h k) = 0 := sub_eq_zero.mpr hz2
      rw [sub_sub_cancel] at h3
      exact h3
    exact (smul_eq_zero.mp hz0).resolve_right (hk0 k)
  have hrelK : ∀ k y, (ggLatCartan Q y (w k) : ZMod p) • P (w k) - α k (P y) • h k ∈
      ggZbar (p := p) ι X := by
    intro k y
    have hPs : P (ggLatRefl Q (w k) y) =
        P y - (ggLatCartan Q y (w k) : ZMod p) • P (w k) := by
      rw [ggLatRefl, map_sub, map_zsmul, Int.cast_smul_eq_zsmul]
    have hRk := hR k y
    rw [hPs, hlin k (P y)] at hRk
    convert (ggZbar (p := p) ι X).neg_mem hRk using 1
    abel
  have hscale : ∀ k, ∃ μ : ZMod p, μ ≠ 0 ∧
      (∀ y, α k (P y) = μ * (ggLatCartan Q y (w k) : ZMod p)) ∧
      P (w k) - μ • h k ∈ ggZbar (p := p) ι X := fun k =>
    ggCartan_scale (zmod_two_ne_zero hp2) (ggZbar (p := p) ι X) P
      (fun y => (ggLatCartan Q y (w k) : ZMod p)) (hw2 k) hsurjZ (hα k) (hαZ k) (hrelK k)
  choose μ hμ0 using hscale
  have hμ : ∀ k, μ k ≠ 0 := fun k => (hμ0 k).1
  have hS1 : ∀ k y, α k (P y) = μ k * (ggLatCartan Q y (w k) : ZMod p) :=
    fun k => (hμ0 k).2.1
  have hS2 : ∀ k, P (w k) - μ k • h k ∈ ggZbar (p := p) ι X := fun k => (hμ0 k).2.2
  have hcart : ∀ j k, α j (h k) * μ k = μ j * (ggLatCartan Q (w k) (w j) : ZMod p) := by
    intro j k
    have h1 := hS1 j (w k)
    have hz := hαZ j (P (w k) - μ k • h k) (hS2 k)
    have hz' : α j (P (w k)) - μ k * α j (h k) = 0 := by
      rw [map_sub, map_smul, smul_eq_mul] at hz
      exact hz
    have heq : μ j * (ggLatCartan Q (w k) (w j) : ZMod p) = μ k * α j (h k) := by
      rw [← h1]
      exact sub_eq_zero.mp hz'
    rw [mul_comm (α j (h k)) (μ k), ← heq]
  have hc4 : ∀ j k, (∀ y, ggLatRefl Q (w j) y = ggLatRefl Q (w k) y) →
      ∀ b : ↥Bs, ((t j b : ↥Bs) : G)⁻¹ * ((t k b : ↥Bs) : G) ∈
        Subgroup.centralizer (X : Set G) := by
    intro j k hs b
    apply (ggZbar_iff (p := p) hBs ι X (t j b) (t k b)).mpr
    set v : V := ι (Additive.ofMul b) with hv
    obtain ⟨y, hy⟩ := hsurjZ v
    have hj := hCong j v y hy
    have hk := hCong k v y hy
    have hmem : ggLin (p := p) ι (t k) v - ggLin (p := p) ι (t j) v ∈
        ggZbar (p := p) ι X := by
      convert (ggZbar (p := p) ι X).sub_mem hk hj using 1
      rw [hs y]
      abel
    rw [← ggLin_apply_ofMul (p := p) ι (t k) b,
        ← ggLin_apply_ofMul (p := p) ι (t j) b, ← hv]
    exact hmem
  have hc5 : ∀ i j k, (∀ y, ggLatRefl Q (w j) y =
        ggLatRefl Q (w i) (ggLatRefl Q (w k) (ggLatRefl Q (w i) y))) →
      ∀ b : ↥Bs, ((t j b : ↥Bs) : G)⁻¹ * (((t i * t k * t i) b : ↥Bs) : G) ∈
        Subgroup.centralizer (X : Set G) := by
    intro i j k hs b
    apply (ggZbar_iff (p := p) hBs ι X (t j b) ((t i * t k * t i) b)).mpr
    set v : V := ι (Additive.ofMul b) with hv
    obtain ⟨y, hy⟩ := hsurjZ v
    have h1 : ggLin (p := p) ι (t i) v - P (ggLatRefl Q (w i) y) ∈
        ggZbar (p := p) ι X := hCong i v y hy
    have h2 : ggLin (p := p) ι (t k) (ggLin (p := p) ι (t i) v) -
        P (ggLatRefl Q (w k) (ggLatRefl Q (w i) y)) ∈ ggZbar (p := p) ι X :=
      hCong k (ggLin (p := p) ι (t i) v) (ggLatRefl Q (w i) y) h1
    have h3 : ggLin (p := p) ι (t i)
          (ggLin (p := p) ι (t k) (ggLin (p := p) ι (t i) v)) -
        P (ggLatRefl Q (w i) (ggLatRefl Q (w k) (ggLatRefl Q (w i) y))) ∈
        ggZbar (p := p) ι X :=
      hCong i (ggLin (p := p) ι (t k) (ggLin (p := p) ι (t i) v))
        (ggLatRefl Q (w k) (ggLatRefl Q (w i) y)) h2
    have hj : ggLin (p := p) ι (t j) v - P (ggLatRefl Q (w j) y) ∈
        ggZbar (p := p) ι X := hCong j v y hy
    have hmem : ggLin (p := p) ι (t i)
          (ggLin (p := p) ι (t k) (ggLin (p := p) ι (t i) v)) -
        ggLin (p := p) ι (t j) v ∈ ggZbar (p := p) ι X := by
      convert (ggZbar (p := p) ι X).sub_mem h3 hj using 1
      rw [hs y]
      abel
    rw [← ggLin_apply_ofMul (p := p) ι (t i * t k * t i) b,
        ← ggLin_apply_ofMul (p := p) ι (t j) b, ← hv]
    convert hmem using 1
    rw [map_mul, map_mul]
    simp only [LinearEquiv.mul_apply]
  exact ⟨m, Q, w, μ, hQ, hwroot, hμ, hcart, hc4, hc5⟩

end Internal

end CFSG.StandardType
