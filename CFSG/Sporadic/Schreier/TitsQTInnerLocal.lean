module

public import CFSG.Sporadic.Schreier.TitsQTInnerCore

public noncomputable section

namespace CFSG.Sporadic.Schreier.TitsQT

@[expose] def restrictAut {G : Type*} [Group G] (H : Subgroup G) (α : MulAut G)
    (h : ∀ x, α x ∈ H ↔ x ∈ H) : MulAut H where
  toFun u := ⟨α (u : G), (h u).2 u.2⟩
  invFun u := ⟨α.symm (u : G), (h _).1 (by simp)⟩
  left_inv u := Subtype.ext (α.symm_apply_apply (u : G))
  right_inv u := Subtype.ext (α.apply_symm_apply (u : G))
  map_mul' u v := Subtype.ext (map_mul α (u : G) (v : G))

theorem restrictAut_apply {G : Type*} [Group G] (H : Subgroup G) (α : MulAut G)
    (h : ∀ x, α x ∈ H ↔ x ∈ H) (u : H) : ((restrictAut H α h) u : G) = α (u : G) := rfl

theorem apply_mem_centralizer_iff {G : Type*} [Group G] (Z : Set G) (α : MulAut G)
    (hα : ∀ z ∈ Z, α z = z) (x : G) :
    α x ∈ Subgroup.centralizer Z ↔ x ∈ Subgroup.centralizer Z := by
  simp only [Subgroup.mem_centralizer_iff]
  constructor
  · intro h z hz
    apply α.injective
    rw [map_mul, map_mul, hα z hz]
    exact h z hz
  · intro h z hz
    rw [← hα z hz, ← map_mul, ← map_mul, h z hz]

theorem apply_mem_normalizer_iff {G : Type*} [Group G] (K : Subgroup G) (α : MulAut G)
    (hα : ∀ k ∈ K, α k = k) (x : G) :
    α x ∈ Subgroup.normalizer (K : Set G) ↔ x ∈ Subgroup.normalizer (K : Set G) := by
  have hK : ∀ y, α y ∈ K ↔ y ∈ K := by
    intro y
    constructor
    · intro hy
      have h1 : α (α y) = α y := hα _ hy
      have h2 : α y = y := α.injective h1
      rw [← h2]
      exact hy
    · intro hy
      rw [hα y hy]
      exact hy
  have e : ∀ y, α x * α y * (α x)⁻¹ = α (x * y * x⁻¹) := by
    intro y
    simp [map_mul, map_inv]
  simp only [Subgroup.mem_normalizer_iff]
  constructor
  · intro h y
    have h1 := h (α y)
    rw [e, hK, hK] at h1
    exact h1
  · intro h y
    obtain ⟨z, rfl⟩ := α.surjective y
    rw [e, hK, hK]
    exact h z

theorem sylow_local_pointwise_inner {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (S : Sylow p G) (H : Subgroup G)
    (hH : H = Subgroup.centralizer
      (((Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype : Subgroup G) : Set G))
    (K : Subgroup G) (hKS : K ≤ S) (N : Subgroup G) (hN : N = Subgroup.normalizer (K : Set G))
    (hSN : (S : Subgroup G) ≤ N)
    (J : Subgroup G) (hJp : IsPGroup p J) (hJS : J ≤ S) (hJH : J ≤ H)
    (hJn : (J.subgroupOf H).Normal) (hCJ : H ⊓ Subgroup.centralizer (J : Set G) ≤ J)
    (hCK : N ⊓ Subgroup.centralizer (K : Set G) ≤ K) (hgen : H ⊔ N = ⊤)
    (α : MulAut G) (hα : ∀ s ∈ (S : Subgroup G), α s = s) :
    ∃ b : G, (∀ s ∈ (S : Subgroup G), b * s = s * b) ∧ ∀ g : G, α g = b * g * b⁻¹ := by
  set Zs : Subgroup G := (Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype with hZs
  have hZsS : Zs ≤ S := Subgroup.map_subtype_le _
  have hcen : ∀ a : G, a ∈ (S : Subgroup G) → (∀ s ∈ (S : Subgroup G), a * s = s * a) →
      a ∈ Zs := by
    intro a ha hcomm
    refine ⟨⟨a, ha⟩, Subgroup.mem_center_iff.2 fun s => ?_, rfl⟩
    exact Subtype.ext (hcomm s s.2).symm
  have hSH : (S : Subgroup G) ≤ H := by
    intro s hs
    rw [hH, Subgroup.mem_centralizer_iff]
    rintro z ⟨z', hz', rfl⟩
    have := Subgroup.mem_center_iff.1 hz' ⟨s, hs⟩
    exact (congrArg Subtype.val this).symm
  have hZfix : ∀ z ∈ (Zs : Set G), α z = z := fun z hz => hα z (hZsS hz)
  have hαH : ∀ x, α x ∈ H ↔ x ∈ H := by
    intro x
    rw [hH]
    exact apply_mem_centralizer_iff _ α hZfix x
  have hKfix : ∀ k ∈ K, α k = k := fun k hk => hα k (hKS hk)
  have hαN : ∀ x, α x ∈ N ↔ x ∈ N := by
    intro x
    rw [hN]
    exact apply_mem_normalizer_iff K α hKfix x
  have hJH' : IsPGroup p (J.subgroupOf H) :=
    hJp.of_equiv (Subgroup.subgroupOfEquivOfLe hJH).symm
  have hCJ' : Subgroup.centralizer ((J.subgroupOf H : Subgroup H) : Set H) ≤ J.subgroupOf H := by
    intro x hx
    rw [Subgroup.mem_subgroupOf]
    refine hCJ (Subgroup.mem_inf.2 ⟨x.2, Subgroup.mem_centralizer_iff.2 fun j hj => ?_⟩)
    have := Subgroup.mem_centralizer_iff.1 hx ⟨j, hJH hj⟩ (Subgroup.mem_subgroupOf.2 hj)
    exact congrArg Subtype.val this
  have hKN : K ≤ N := hN ▸ Subgroup.le_normalizer
  have hKn : (K.subgroupOf N).Normal := by
    subst hN
    exact Subgroup.normal_in_normalizer
  have hKp : IsPGroup p K := S.isPGroup'.to_le hKS
  have hKN' : IsPGroup p (K.subgroupOf N) :=
    hKp.of_equiv (Subgroup.subgroupOfEquivOfLe hKN).symm
  have hCK' : Subgroup.centralizer ((K.subgroupOf N : Subgroup N) : Set N) ≤ K.subgroupOf N := by
    intro x hx
    rw [Subgroup.mem_subgroupOf]
    refine hCK (Subgroup.mem_inf.2 ⟨x.2, Subgroup.mem_centralizer_iff.2 fun j hj => ?_⟩)
    have := Subgroup.mem_centralizer_iff.1 hx ⟨j, hKN hj⟩ (Subgroup.mem_subgroupOf.2 hj)
    exact congrArg Subtype.val this
  have hH' : ∀ g ∈ H, α g = g := by
    have : (J.subgroupOf H).Normal := hJn
    obtain ⟨aH, haJ, -, haT, haα⟩ := selfCentralizing_sylow_pointwise_inner p (J.subgroupOf H)
      hJH' hCJ' (S.subtype hSH) (restrictAut H α hαH) (by
        intro t ht
        exact Subtype.ext (hα t (Subgroup.mem_subgroupOf.1 ht)))
    have haS : (aH : G) ∈ (S : Subgroup G) := hJS (Subgroup.mem_subgroupOf.1 haJ)
    have hcomm : ∀ s ∈ (S : Subgroup G), (aH : G) * s = s * aH := fun s hs =>
      congrArg Subtype.val (haT ⟨s, hSH hs⟩ (Subgroup.mem_subgroupOf.2 hs))
    have haZ : (aH : G) ∈ Zs := hcen _ haS hcomm
    intro g hg
    have h1 := congrArg Subtype.val (haα ⟨g, hg⟩)
    rw [restrictAut_apply] at h1
    have hgc : (aH : G) * g = g * aH := by
      have : g ∈ Subgroup.centralizer (Zs : Set G) := hH ▸ hg
      exact Subgroup.mem_centralizer_iff.1 this _ haZ
    rw [h1]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hgc]
    group
  obtain ⟨b, hbK, hbcomm, hN'⟩ : ∃ b : G, b ∈ K ∧ (∀ s ∈ (S : Subgroup G), b * s = s * b) ∧
      ∀ g ∈ N, α g = b * g * b⁻¹ := by
    have : (K.subgroupOf N).Normal := hKn
    obtain ⟨bN, hbK, -, hbT, hbα⟩ := selfCentralizing_sylow_pointwise_inner p (K.subgroupOf N)
      hKN' hCK' (S.subtype hSN) (restrictAut N α hαN) (by
        intro t ht
        exact Subtype.ext (hα t (Subgroup.mem_subgroupOf.1 ht)))
    refine ⟨(bN : G), Subgroup.mem_subgroupOf.1 hbK, fun s hs =>
      congrArg Subtype.val (hbT ⟨s, hSN hs⟩ (Subgroup.mem_subgroupOf.2 hs)), fun g hg => ?_⟩
    have h1 := congrArg Subtype.val (hbα ⟨g, hg⟩)
    rw [restrictAut_apply] at h1
    rw [h1]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  have hbS : b ∈ (S : Subgroup G) := hKS hbK
  have hbZ : b ∈ Zs := hcen _ hbS hbcomm
  refine ⟨b, hbcomm, fun g => ?_⟩
  have hle : H ⊔ N ≤ MonoidHom.eqLocus α.toMonoidHom (MulAut.conj b).toMonoidHom := by
    refine sup_le (fun g hg => ?_) fun g hg => ?_
    · have hgc : b * g = g * b := by
        have : g ∈ Subgroup.centralizer (Zs : Set G) := hH ▸ hg
        exact Subgroup.mem_centralizer_iff.1 this _ hbZ
      show α g = b * g * b⁻¹
      rw [hH' g hg, hgc]
      group
    · exact hN' g hg
  rw [hgen] at hle
  exact hle (Subgroup.mem_top g)

end CFSG.Sporadic.Schreier.TitsQT
