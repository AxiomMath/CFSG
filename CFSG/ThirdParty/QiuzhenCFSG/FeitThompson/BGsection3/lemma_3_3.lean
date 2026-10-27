module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection3.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection3.lemma_3_1

namespace CFSG
end CFSG
open CFSG


public noncomputable def CFSG.subgroupSum {G : Type*} [Group G] [Finite G] {F : Type*} [Field F]
    {V : Type*} [AddCommGroup V] [Module F V] (ρ : Representation F G V) (H : Subgroup G) (v : V) :
    V := by
  let _ : Fintype H := Fintype.ofFinite H
  exact ∑ h : H, ρ h v

public theorem CFSG.subgroupSum_eq_sum {G : Type*} [Group G] [Finite G] {F : Type*} [Field F]
    {V : Type*} [AddCommGroup V] [Module F V] (ρ : Representation F G V)
    (H : Subgroup G) (v : V) :
    subgroupSum ρ H v =
      (by
        let _ : Fintype H := Fintype.ofFinite H
        exact ∑ h : H, ρ h v) := by
  rfl

private noncomputable def CFSG.conjByEquiv {G : Type*} [Group G] (R : Subgroup G) (x : G) :
    R ≃ R.conjBy x := by
  simpa only [Subgroup.conjBy, MulEquiv.toMonoidHom_eq_coe] using
    (MulEquiv.subgroupMap (MulAut.conj x) R).toEquiv

private theorem CFSG.conjByEquiv_apply_coe {G : Type*} [Group G] (R : Subgroup G) (x : G) (r : R) :
    (((conjByEquiv R x) r : R.conjBy x) : G) = x * (r : G) * x⁻¹ := by
  change (MulAut.conj x) (r : G) = x * (r : G) * x⁻¹
  simp [MulAut.conj_apply, mul_assoc]

private theorem CFSG.fixed_mem_of_fixed_conjBy {G : Type*} [Group G] {F : Type*} [Field F]
    {V : Type*} [AddCommGroup V] [Module F V] (ρ : Representation F G V) (R : Subgroup G)
    (x : G) {v : V} (hv : v ∈ ρ.fixedSubspace (R.conjBy x)) :
    ρ x⁻¹ v ∈ ρ.fixedSubspace R := by
  rw [Representation.fixedSubspace, Representation.mem_invariants] at hv ⊢
  intro r
  have hmem : x * (r : G) * x⁻¹ ∈ R.conjBy x := by
    rw [Subgroup.conjBy, Subgroup.mem_map]
    refine ⟨(r : G), r.property, ?_⟩
    simp [MulAut.conj_apply, mul_assoc]
  have hfix : ρ (x * (r : G) * x⁻¹) v = v := hv ⟨x * (r : G) * x⁻¹, hmem⟩
  have hfix' := congrArg (ρ x⁻¹) hfix
  simpa [← Module.End.mul_apply, ← map_mul, mul_assoc] using hfix'

private theorem CFSG.sum_eq_one_part_add_ne_part_subgroup {G : Type*} [Group G] [Finite G]
    {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V]
    (ρ : Representation F G V) (R : Subgroup G) (x : G) (v : V) :
    (by
      let _ : Fintype R := Fintype.ofFinite R
      exact ∑ r : R, ρ (x * (r : G) * x⁻¹) v) =
      (by
        let _ : Fintype R := Fintype.ofFinite R
        let _ : Fintype {r : R // r ≠ 1} := Fintype.ofFinite {r : R // r ≠ 1}
        exact v + ∑ r : {r : R // r ≠ 1}, ρ (x * (r.1 : G) * x⁻¹) v) := by
  classical
  let _ : Fintype R := Fintype.ofFinite R
  let _ : Fintype {r : R // r ≠ 1} := Fintype.ofFinite {r : R // r ≠ 1}
  let _ : Fintype {r : R // r = 1} := Fintype.ofFinite {r : R // r = 1}
  letI : Unique {r : R // r = 1} :=
    ⟨⟨1, rfl⟩, by
      intro r
      apply Subtype.ext
      simpa using r.2⟩
  let e : {r : R // r = 1} ⊕ {r : R // r ≠ 1} ≃ R := Equiv.sumCompl (fun r : R => r = 1)
  have hsum :=
    Fintype.sum_equiv e
      (fun s : {r : R // r = 1} ⊕ {r : R // r ≠ 1} =>
        match s with
        | Sum.inl r => ρ (x * ((r : R) : G) * x⁻¹) v
        | Sum.inr r => ρ (x * ((r : R) : G) * x⁻¹) v)
      (fun r : R => ρ (x * (r : G) * x⁻¹) v)
      (by
        intro s
        cases s <;> simp [e, Equiv.sumCompl_apply_inl, Equiv.sumCompl_apply_inr])
  have hone :
      (∑ r : {r : R // r = 1}, ρ (x * ((r : R) : G) * x⁻¹) v) = v := by
    rw [Fintype.sum_unique]
    have hdefault : (((default : {r : R // r = 1}) : R) : G) = 1 := by
      simpa using (default : {r : R // r = 1}).2
    simp [hdefault]
  calc
    ∑ r : R, ρ (x * (r : G) * x⁻¹) v =
        (∑ r : {r : R // r = 1}, ρ (x * ((r : R) : G) * x⁻¹) v) +
          ∑ r : {r : R // r ≠ 1}, ρ (x * ((r : R) : G) * x⁻¹) v := by
            simpa using hsum.symm
    _ = v + ∑ r : {r : R // r ≠ 1}, ρ (x * ((r : R) : G) * x⁻¹) v := by rw [hone]

private theorem CFSG.sum_eq_subgroup_part_add_not_mem_part {G : Type*} [Group G] [Finite G]
    {α : Type*} [AddCommMonoid α] (K : Subgroup G) (f : G → α) :
    (by
      let _ : Fintype G := Fintype.ofFinite G
      exact ∑ g : G, f g) =
      (by
        classical
        let _ : Fintype K := Fintype.ofFinite K
        let _ : Fintype {g : G // g ∉ K} := Fintype.ofFinite {g : G // g ∉ K}
        exact ∑ k : K, f k + ∑ g : {g : G // g ∉ K}, f g.1) := by
  classical
  let _ : Fintype G := Fintype.ofFinite G
  let _ : Fintype K := Fintype.ofFinite K
  let _ : Fintype {g : G // g ∉ K} := Fintype.ofFinite {g : G // g ∉ K}
  let e : K ⊕ {g : G // g ∉ K} ≃ G := Equiv.sumCompl (fun g : G => g ∈ K)
  have hsum :=
    Fintype.sum_equiv e
      (fun s : K ⊕ {g : G // g ∉ K} =>
        match s with
        | Sum.inl k => f k
        | Sum.inr g => f g.1)
      f
      (by
        intro s
        cases s <;> simp [e, Equiv.sumCompl_apply_inl, Equiv.sumCompl_apply_inr])
  calc
    ∑ g : G, f g = ∑ s : K ⊕ {g : G // g ∉ K},
        match s with
        | Sum.inl k => f k
        | Sum.inr g => f g.1 := by
          simpa using hsum.symm
    _ = (∑ k : K, f k) + ∑ g : {g : G // g ∉ K}, f g.1 := by
          simp

theorem CFSG.subgroupSum_mem_fixedSubspace {G : Type*} [Group G] [Finite G] {F : Type*} [Field F]
    {V : Type*} [AddCommGroup V] [Module F V] (ρ : Representation F G V) (H : Subgroup G) (v : V) :
    subgroupSum ρ H v ∈ ρ.fixedSubspace H := by
  let _ : Fintype H := Fintype.ofFinite H
  rw [Representation.fixedSubspace, Representation.mem_invariants]
  intro x
  calc
    ρ x (subgroupSum ρ H v) = ∑ h : H, ρ (x * h) v := by
      simp [subgroupSum, map_sum, ← Module.End.mul_apply, ← map_mul]
    _ = ∑ h : H, ρ h v := by
      exact Fintype.sum_bijective (fun h : H => x * h) (Group.mulLeft_bijective x)
        (fun h : H => ρ (x * h) v) (fun h : H => ρ h v) fun _ => rfl
    _ = subgroupSum ρ H v := by
      simp [subgroupSum]

theorem CFSG.subgroupSum_eq_zero_of_fixedSubspace_eq_bot {G : Type*} [Group G] [Finite G]
    {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V] (ρ : Representation F G V)
    (H : Subgroup G) (hH : ρ.fixedSubspace H = ⊥) (v : V) :
    subgroupSum ρ H v = 0 := by
  have hmem : subgroupSum ρ H v ∈ ρ.fixedSubspace H := subgroupSum_mem_fixedSubspace ρ H v
  rw [hH] at hmem
  simpa using hmem


theorem CFSG.fixedSubspace_conjBy_eq_bot {G : Type*} [Group G] {F : Type*} [Field F]
    {V : Type*} [AddCommGroup V] [Module F V] (ρ : Representation F G V) (R : Subgroup G)
    (hR : ρ.fixedSubspace R = ⊥) (x : G) :
    ρ.fixedSubspace (R.conjBy x) = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro v hv
  have hxinv_mem : ρ x⁻¹ v ∈ ρ.fixedSubspace R := fixed_mem_of_fixed_conjBy ρ R x hv
  have hxinv_zero : ρ x⁻¹ v = 0 := by
    have hxbot : ρ x⁻¹ v ∈ (⊥ : Submodule F V) := by
      rw [hR] at hxinv_mem
      simpa using hxinv_mem
    simpa using hxbot
  have := congrArg (ρ x) hxinv_zero
  simpa [← Module.End.mul_apply, ← map_mul, mul_assoc] using this

theorem CFSG.fixedSubspace_top_eq_bot_of_fixedSubspace_eq_bot {G : Type*} [Group G]
    {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V] (ρ : Representation F G V)
    (R : Subgroup G) (hR : ρ.fixedSubspace R = ⊥) :
    ρ.fixedSubspace (⊤ : Subgroup G) = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro v hv
  have hvR : v ∈ ρ.fixedSubspace R := by
    rw [Representation.fixedSubspace, Representation.mem_invariants] at hv ⊢
    intro r
    simpa using hv ⟨(r : G), Subgroup.mem_top (r : G)⟩
  rw [hR] at hvR
  simpa using hvR

public theorem CFSG.subgroupSum_conjBy_eq {G : Type*} [Group G] [Finite G] {F : Type*} [Field F]
    {V : Type*} [AddCommGroup V] [Module F V] (ρ : Representation F G V) (R : Subgroup G)
    (x : G) (v : V) :
    subgroupSum ρ (R.conjBy x) v =
      (by
        let _ : Fintype R := Fintype.ofFinite R
        exact ∑ r : R, ρ (x * (r : G) * x⁻¹) v) := by
  let _ : Fintype R := Fintype.ofFinite R
  let _ : Fintype (R.conjBy x) := Fintype.ofFinite (R.conjBy x)
  let e : R ≃ R.conjBy x := conjByEquiv R x
  have hsum :=
    Fintype.sum_equiv e
      (fun r : R => ρ (x * (r : G) * x⁻¹) v)
      (fun s : R.conjBy x => ρ s v)
      (by
        intro r
        rw [conjByEquiv_apply_coe])
  simpa [subgroupSum] using hsum.symm

public theorem CFSG.subgroupSum_conjBy_eq_add {G : Type*} [Group G] [Finite G] {F : Type*} [Field F]
    {V : Type*} [AddCommGroup V] [Module F V] (ρ : Representation F G V) (R : Subgroup G)
    (x : G) (v : V) :
    letI : Fintype {r : R // r ≠ 1} := Fintype.ofFinite {r : R // r ≠ 1}
    subgroupSum ρ (R.conjBy x) v =
      v + ∑ r : {r : R // r ≠ 1}, ρ (x * (r.1 : G) * x⁻¹) v := by
  classical
  let _ : Fintype R := Fintype.ofFinite R
  let _ : Fintype {r : R // r ≠ 1} := Fintype.ofFinite {r : R // r ≠ 1}
  rw [subgroupSum_conjBy_eq ρ R x v]
  simpa using sum_eq_one_part_add_ne_part_subgroup ρ R x v

public theorem CFSG.norm_eq_subgroupSum_add_sum_not_mem {G : Type*} [Group G] [Finite G]
    {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V] (ρ : Representation F G V)
    (K : Subgroup G) (v : V) :
    letI : Fintype G := Fintype.ofFinite G
    letI : Fintype {g : G // g ∉ K} := Fintype.ofFinite {g : G // g ∉ K}
    ρ.norm v = subgroupSum ρ K v + ∑ g : {g : G // g ∉ K}, ρ g.1 v := by
  classical
  let _ : Fintype G := Fintype.ofFinite G
  let _ : Fintype K := Fintype.ofFinite K
  let _ : Fintype {g : G // g ∉ K} := Fintype.ofFinite {g : G // g ∉ K}
  simpa [Representation.norm, subgroupSum] using
    sum_eq_subgroup_part_add_not_mem_part (K := K) (f := fun g : G => ρ g v)

public theorem CFSG.frobeniusConjPair_bijective {G : Type*} [Group G] [Finite G] (K R : Subgroup G)
    (hfrob : IsFrobeniusGroupWithKernelComplement K R) (hK_ne : K ≠ ⊥) (hR_ne : R ≠ ⊥) :
    Function.Bijective
      (fun xr : K × {r : R // r ≠ 1} =>
        (⟨(xr.1 : G) * (xr.2.1 : G) * (xr.1 : G)⁻¹, by
          intro hmemK
          have hr_memK : (xr.2.1 : G) ∈ K := by
            have hxconj :=
              hfrob.normal.conj_mem ((xr.1 : G) * (xr.2.1 : G) * (xr.1 : G)⁻¹) hmemK
                (xr.1 : G)⁻¹
            simpa [mul_assoc] using hxconj
          have hr_eq_one : (xr.2.1 : G) = 1 := by
            have hr_bot : (xr.2.1 : G) ∈ (⊥ : Subgroup G) :=
              (Subgroup.disjoint_def.mp hfrob.isComplement'.disjoint) hr_memK xr.2.1.property
            simpa using hr_bot
          exact xr.2.2 (Subtype.ext hr_eq_one)⟩ : {g : G // g ∉ K})) := by
  have hcent :
      ∀ x : R, x ≠ 1 → elementCentralizerIn K (x : G) = ⊥ :=
    (lemma_3_1 (K := K) (R := R) hK_ne hR_ne hfrob.normal hfrob.isComplement').1 hfrob
  constructor
  · intro a b hab
    rcases a with ⟨x, r⟩
    rcases b with ⟨y, s⟩
    have hxy_sub : x = y := by
      apply Subtype.ext
      by_contra hxy_ne
      have hab_val :
          (x : G) * (r.1 : G) * (x : G)⁻¹ = (y : G) * (s.1 : G) * (y : G)⁻¹ :=
        congrArg Subtype.val hab
      let d : G := (y : G)⁻¹ * x
      have hdK : d ∈ K := by
        dsimp [d]
        exact K.mul_mem (K.inv_mem y.property) x.property
      have hd_not_mem_R : d ∉ R := by
        intro hdR
        have hd_eq_one : d = 1 := by
          have hd_bot : d ∈ (⊥ : Subgroup G) :=
            (Subgroup.disjoint_def.mp hfrob.isComplement'.disjoint) hdK hdR
          simpa using hd_bot
        have hxy : (x : G) = y := by
          have := congrArg (fun t : G => (y : G) * t) hd_eq_one
          simpa [d, mul_assoc] using this
        exact hxy_ne hxy
      have hs_mem_conj : (s.1 : G) ∈ R.conjBy d := by
        rw [Subgroup.conjBy, Subgroup.mem_map]
        refine ⟨(r.1 : G), r.1.property, ?_⟩
        have := congrArg (fun t : G => (y : G)⁻¹ * t * (y : G)) hab_val
        simpa [d, mul_assoc] using this
      have hs_eq_one : (s.1 : G) = 1 := by
        exact (Subgroup.disjoint_def.mp (hfrob.disjoint_conjBy d hd_not_mem_R)) s.1.property
          hs_mem_conj
      exact s.2 (Subtype.ext hs_eq_one)
    subst hxy_sub
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      have hab_val :
          (x : G) * (r.1 : G) * (x : G)⁻¹ = (x : G) * (s.1 : G) * (x : G)⁻¹ := by
        simpa using congrArg Subtype.val hab
      have := congrArg (fun t : G => (x : G)⁻¹ * t * (x : G)) hab_val
      simpa [mul_assoc] using this
  · intro g
    rcases hfrob.isComplement'.2 g.1 with ⟨⟨⟨k, hkK⟩, ⟨r, hrR⟩⟩, hkr⟩
    have hkr' : (k : G) * r = g := by
      simpa using hkr
    have hr_ne_one : (r : G) ≠ 1 := by
      intro hr_eq_one
      apply g.2
      rw [← hkr']
      simpa [hr_eq_one] using hkK
    have hr_sub_ne : (⟨r, hrR⟩ : R) ≠ 1 := by
      intro hr_eq_one
      exact hr_ne_one (congrArg Subtype.val hr_eq_one)
    have hcent_r : elementCentralizerIn K (r : G) = ⊥ := hcent ⟨r, hrR⟩ hr_sub_ne
    let f : K → K := fun a =>
      ⟨(a : G) * r * (a : G)⁻¹ * r⁻¹, by
        have hconj : r * (a : G)⁻¹ * r⁻¹ ∈ K :=
          hfrob.normal.conj_mem (a : G)⁻¹ (K.inv_mem a.property) r
        simpa [mul_assoc] using K.mul_mem a.property hconj⟩
    have hf_inj : Function.Injective f := by
      intro a b hab
      apply Subtype.ext
      have hab_val :
          (a : G) * r * (a : G)⁻¹ * r⁻¹ = (b : G) * r * (b : G)⁻¹ * r⁻¹ :=
        congrArg Subtype.val hab
      have hab_mul : (a : G) * r * (a : G)⁻¹ = (b : G) * r * (b : G)⁻¹ := by
        have := congrArg (fun t : G => t * r) hab_val
        simpa [mul_assoc] using this
      have hcomm : (b : G)⁻¹ * (a : G) * r = r * ((b : G)⁻¹ * (a : G)) := by
        have := congrArg (fun t : G => (b : G)⁻¹ * t * (a : G)) hab_mul
        simpa [mul_assoc] using this
      have hba_cent : (b : G)⁻¹ * (a : G) ∈ elementCentralizerIn K (r : G) := by
        refine ⟨K.mul_mem (K.inv_mem b.property) a.property, ?_⟩
        exact Subgroup.mem_centralizer_singleton_iff.mpr hcomm
      have hba_eq_one : (b : G)⁻¹ * (a : G) = 1 := by
        have hbot : (b : G)⁻¹ * (a : G) ∈ (⊥ : Subgroup G) := by
          rw [hcent_r] at hba_cent
          simpa using hba_cent
        simpa using hbot
      have := congrArg (fun t : G => (b : G) * t) hba_eq_one
      simpa [mul_assoc] using this
    have hf_surj : Function.Surjective f := Finite.surjective_of_injective hf_inj
    obtain ⟨y, hy⟩ := hf_surj ⟨k, hkK⟩
    have hy_val : (y : G) * r * (y : G)⁻¹ * r⁻¹ = k := congrArg Subtype.val hy
    refine ⟨⟨y, ⟨⟨r, hrR⟩, hr_sub_ne⟩⟩, ?_⟩
    apply Subtype.ext
    calc
      ((y : K) : G) * (((⟨r, hrR⟩ : R) : G)) * ((y : K) : G)⁻¹ =
          (((y : G) * r * (y : G)⁻¹ * r⁻¹) : G) * r := by
            simp [mul_assoc]
      _ = k * r := by rw [hy_val]
      _ = g := hkr'

public theorem CFSG.lemma_3_3 {G : Type*} [Group G] [Finite G] {F : Type*} [Field F] {V : Type*}
    [AddCommGroup V] [Module F V] (K R : Subgroup G) (ρ : Representation F G V)
    (hfrob : IsFrobeniusGroupWithKernelComplement K R)
    (hchar : ringChar F = 0 ∨
      (Nat.Prime (ringChar F) ∧ Nat.Coprime (ringChar F) (Nat.card K)))
    (hK_nontrivial : ¬ K ≤ ρ.ker) :
    ρ.fixedSubspace R ≠ ⊥ := by
  classical
  intro hfixR
  have hK_ne : K ≠ ⊥ := hfrob.kernel_ne_bot
  have hR_ne : R ≠ ⊥ := hfrob.complement_ne_bot
  have hfixTop : ρ.fixedSubspace (⊤ : Subgroup G) = ⊥ :=
    fixedSubspace_top_eq_bot_of_fixedSubspace_eq_bot ρ R hfixR
  let _ : Fintype G := Fintype.ofFinite G
  let _ : Fintype K := Fintype.ofFinite K
  let _ : Fintype R := Fintype.ofFinite R
  have hsum_not_mem_eq (v : V) :
      subgroupSum ρ K v = (Nat.card K : F) • v := by
    let _ : Fintype {g : G // g ∉ K} := Fintype.ofFinite {g : G // g ∉ K}
    let _ : Fintype {r : R // r ≠ 1} := Fintype.ofFinite {r : R // r ≠ 1}
    let s : V := ∑ g : {g : G // g ∉ K}, ρ g.1 v
    have hdouble :
        ∑ x : K, ∑ r : {r : R // r ≠ 1}, ρ ((x : G) * (r.1 : G) * (x : G)⁻¹) v = s := by
      rw [← Fintype.sum_prod_type']
      simpa [s] using
        (Fintype.sum_bijective
          (fun xr : K × {r : R // r ≠ 1} =>
            (⟨(xr.1 : G) * (xr.2.1 : G) * (xr.1 : G)⁻¹, by
              intro hmemK
              have hr_memK : (xr.2.1 : G) ∈ K := by
                have hxconj :=
                  hfrob.normal.conj_mem ((xr.1 : G) * (xr.2.1 : G) * (xr.1 : G)⁻¹) hmemK
                    (xr.1 : G)⁻¹
                simpa [mul_assoc] using hxconj
              have hr_eq_one : (xr.2.1 : G) = 1 := by
                have hr_bot : (xr.2.1 : G) ∈ (⊥ : Subgroup G) :=
                  (Subgroup.disjoint_def.mp hfrob.isComplement'.disjoint) hr_memK xr.2.1.property
                simpa using hr_bot
              exact xr.2.2 (Subtype.ext hr_eq_one)⟩ : {g : G // g ∉ K}))
          (frobeniusConjPair_bijective K R hfrob hK_ne hR_ne)
          (fun xr => ρ ((xr.1 : G) * (xr.2.1 : G) * (xr.1 : G)⁻¹) v)
          (fun g => ρ g.1 v)
          (fun _ => rfl))
    have hconj_zero : ∀ x : K, subgroupSum ρ (R.conjBy (x : G)) v = 0 := by
      intro x
      exact subgroupSum_eq_zero_of_fixedSubspace_eq_bot ρ (R.conjBy (x : G))
        (fixedSubspace_conjBy_eq_bot ρ R hfixR (x : G)) v
    have hconj_expand :
        ∑ x : K, subgroupSum ρ (R.conjBy (x : G)) v = (Nat.card K : F) • v + s := by
      have hsum_rewrite :
          (fun x : K => subgroupSum ρ (R.conjBy (x : G)) v) =
            fun x : K => v + ∑ r : {r : R // r ≠ 1}, ρ ((x : G) * (r.1 : G) * (x : G)⁻¹) v := by
        funext x
        exact subgroupSum_conjBy_eq_add ρ R (x : G) v
      have hconst : (∑ _ : K, v) = (Nat.card K : F) • v := by
        simp [Nat.card_eq_fintype_card, Nat.cast_smul_eq_nsmul]
      calc
        ∑ x : K, subgroupSum ρ (R.conjBy (x : G)) v
            = ∑ x : K,
                (v + ∑ r : {r : R // r ≠ 1}, ρ ((x : G) * (r.1 : G) * (x : G)⁻¹) v) := by
                  rw [hsum_rewrite]
        _ = (∑ _ : K, v) + ∑ x : K, ∑ r : {r : R // r ≠ 1},
              ρ ((x : G) * (r.1 : G) * (x : G)⁻¹) v := by
                simp [Finset.sum_add_distrib]
        _ = (Nat.card K : F) • v + ∑ x : K, ∑ r : {r : R // r ≠ 1},
              ρ ((x : G) * (r.1 : G) * (x : G)⁻¹) v := by
                rw [hconst]
        _ = (Nat.card K : F) • v + s := by
              rw [hdouble]
    have hpartition : (Nat.card K : F) • v + s = 0 := by
      rw [← hconj_expand]
      have hsum_zero :
          ∑ x : K, subgroupSum ρ (R.conjBy (x : G)) v = ∑ _ : K, (0 : V) := by
        simp [hconj_zero]
      rw [hsum_zero]
      simp
    have hnorm_mem : ρ.norm v ∈ ρ.fixedSubspace (⊤ : Subgroup G) := by
      rw [Representation.fixedSubspace, Representation.mem_invariants]
      intro g
      simp
    have hnorm_zero : ρ.norm v = 0 := by
      rw [hfixTop] at hnorm_mem
      simpa using hnorm_mem
    have hnorm_split : ρ.norm v = subgroupSum ρ K v + s := by
      simpa [s] using norm_eq_subgroupSum_add_sum_not_mem ρ K v
    have hKsum : subgroupSum ρ K v + s = 0 := by
      rw [← hnorm_split, hnorm_zero]
    have hEq : subgroupSum ρ K v + s = (Nat.card K : F) • v + s := by
      rw [hKsum, hpartition]
    exact add_right_cancel hEq
  have hcard_ne_zero : (Nat.card K : F) ≠ 0 := by
    intro hzero
    cases hchar with
    | inl hchar0 =>
        have hdiv : ringChar F ∣ Nat.card K := ringChar.dvd hzero
        rw [hchar0] at hdiv
        have hcard_eq_zero : Nat.card K = 0 := by
          simp at hdiv
        have hcard_pos : 0 < Nat.card K := Nat.card_pos
        exact (Nat.ne_of_gt hcard_pos) hcard_eq_zero
    | inr hcharp =>
        have hdiv : ringChar F ∣ Nat.card K := ringChar.dvd hzero
        exact (hcharp.1.coprime_iff_not_dvd.mp hcharp.2) hdiv
  have hfixed_all : ∀ v : V, v ∈ ρ.fixedSubspace K := by
    intro v
    have hscalar_mem : (Nat.card K : F) • v ∈ ρ.fixedSubspace K := by
      rw [← hsum_not_mem_eq v]
      exact subgroupSum_mem_fixedSubspace ρ K v
    rcases isUnit_iff_ne_zero.mpr hcard_ne_zero with ⟨u, hu⟩
    have hu_mem : (↑u⁻¹ : F) • ((Nat.card K : F) • v) ∈ ρ.fixedSubspace K :=
      (ρ.fixedSubspace K).smul_mem (↑u⁻¹ : F) hscalar_mem
    have hu' : (↑u⁻¹ : F) * (Nat.card K : F) = 1 := by
      calc
        (↑u⁻¹ : F) * (Nat.card K : F) = (↑u⁻¹ : F) * (u : F) := by rw [hu]
        _ = 1 := by simp
    have hcard_cast : ((Fintype.card K : ℕ) : F) = (Nat.card K : F) := by
      simp [Nat.card_eq_fintype_card]
    have hv_memF : (((↑u⁻¹ : F) * (Fintype.card K : F)) • v) ∈ ρ.fixedSubspace K := by
      simpa [smul_smul] using hu_mem
    have huF : (↑u⁻¹ : F) * (Fintype.card K : F) = 1 := by
      calc
        (↑u⁻¹ : F) * (Fintype.card K : F) = (↑u⁻¹ : F) * (Nat.card K : F) := by rw [hcard_cast]
        _ = 1 := hu'
    have hv_eq : (((↑u⁻¹ : F) * (Fintype.card K : F)) • v) = v := by
      rw [huF, one_smul]
    exact hv_eq ▸ hv_memF
  have hK_le_ker : K ≤ ρ.ker := by
    intro k hk
    ext v
    have hv : v ∈ ρ.fixedSubspace K := hfixed_all v
    rw [Representation.fixedSubspace, Representation.mem_invariants] at hv
    simpa using hv ⟨k, hk⟩
  exact hK_nontrivial hK_le_ker
