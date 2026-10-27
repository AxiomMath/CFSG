module

public import CFSG.Quasithin.H13.AS91Sec8SimA
public import CFSG.Quasithin.H13.AS91Sec8SimB
public import CFSG.Quasithin.H13.AS91Sec8SimC
public import CFSG.Quasithin.H13.AS91Sec8SimD
public import CFSG.Quasithin.H13.AS91Sec8SimE
public import CFSG.Quasithin.Recognition.UniquenessSystemRecognition

public section

namespace CFSG.Quasithin.H13.AS91

open CFSG.Quasithin.Asc94 MulAction
open scoped Pointwise

theorem mem_autImage_iff {G : Type*} [Group G] {A : Subgroup G} (ψ : ↥A ≃* ↥A) (C : Subgroup G)
    (g : ↥A) : (g : G) ∈ autImage ψ C ↔ ((ψ.symm g : ↥A) : G) ∈ C := by
  simp only [autImage, Subgroup.mem_map, Subgroup.mem_subgroupOf, Subgroup.coe_subtype,
    MulEquiv.coe_toMonoidHom]
  constructor
  · rintro ⟨c', ⟨c, hc, rfl⟩, hg⟩
    have h1 : ψ c = g := Subtype.ext hg
    rw [← h1, MulEquiv.symm_apply_apply]
    exact hc
  · intro h
    exact ⟨ψ (ψ.symm g), ⟨ψ.symm g, h, rfl⟩, by rw [MulEquiv.apply_symm_apply]⟩

theorem mem_conjSub_iff {G : Type*} [Group G] (j g : G) (C : Subgroup G) :
    g ∈ conjSub j C ↔ j⁻¹ * g * j ∈ C := by
  unfold conjSub
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨c, hc, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hc
  · intro h
    exact ⟨j⁻¹ * g * j, h, by simp [MulAut.conj_apply, mul_assoc]⟩

theorem mem_stab_pair_conj {G : Type*} [Group G] {X : Type*} [MulAction G X] {x y : X} {q : G}
    (hq : q • x = x) (g : G) :
    g ∈ stabilizer G ({x, q • y} : Set X) ↔ q⁻¹ * g * q ∈ stabilizer G ({x, y} : Set X) := by
  have e : ({x, q • y} : Set X) = q • ({x, y} : Set X) := by
    rw [Set.smul_set_insert, Set.smul_set_singleton, hq]
  rw [mem_stabilizer_iff, mem_stabilizer_iff, e, mul_smul, mul_smul, inv_smul_eq_iff]

theorem as92Thm4 :
    ∀ (G X Gb Xb : Type) [Group G] [Finite G] [MulAction G X] [Group Gb] [Finite Gb]
      [MulAction Gb Xb] (Γ : SimpleGraph X) (I : Subgroup G) (ΓI : Γ.Subgraph) (x y : X)
      (Γb : SimpleGraph Xb) (Ib : Subgroup Gb) (ΓIb : Γb.Subgraph) (xb yb : Xb),
      IsUniquenessSystem Γ I ΓI x y → IsUniquenessSystem Γb Ib ΓIb xb yb →
      HypV I x y → HypV Ib xb yb →
      ∀ (a : ↥(stabilizer G x) ≃* ↥(stabilizer Gb xb)) (z : ↥I ≃* ↥Ib),
        ((stabilizer G y).subgroupOf (stabilizer G x)).map a.toMonoidHom =
          (stabilizer Gb yb).subgroupOf (stabilizer Gb xb) →
        ((stabilizer G x).subgroupOf I).map z.toMonoidHom =
          (stabilizer Gb xb).subgroupOf Ib →
        (I.subgroupOf (stabilizer G x)).map a.toMonoidHom = Ib.subgroupOf (stabilizer Gb xb) →
        ((stabilizer G ({x, y} : Set X)).subgroupOf I).map z.toMonoidHom =
          (stabilizer Gb ({xb, yb} : Set Xb)).subgroupOf Ib →
        ∃ (β : ↥(stabilizer G x) ≃* ↥(stabilizer Gb xb)) (ζ : ↥I ≃* ↥Ib),
          IsSimilarity I x y Ib xb yb β ζ := by
  intro G X Gb Xb _ _ _ _ _ _ Γ I ΓI x y Γb Ib ΓIb xb yb hU hUb hV hVb a z hA1 hZ1 hA2 hZ2
  have hA1' := (map_subgroupOf_eq_iff a (stabilizer G y) (stabilizer Gb yb)).mp hA1
  have hZ1' := (map_subgroupOf_eq_iff z (stabilizer G x) (stabilizer Gb xb)).mp hZ1
  have hA2' := (map_subgroupOf_eq_iff a I Ib).mp hA2
  have hZ2' := (map_subgroupOf_eq_iff z (stabilizer G ({x, y} : Set X))
    (stabilizer Gb ({xb, yb} : Set Xb))).mp hZ2
  obtain ⟨θ, hθ⟩ := exists_theta a z hZ1 hA2
  obtain ⟨φ, ψ, hφ, hψ, hθφψ, hD, hGψ⟩ := exists_phi_psi hV θ
  obtain ⟨p, hp, hpair⟩ := exists_p_of_phi hU φ hφ hD
  have hpI : p ∈ I := (Subgroup.mem_inf.mp hp).1
  have hpx : p ∈ stabilizer G x := (Subgroup.mem_inf.mp hp).2
  have hpx' : p • x = x := mem_stabilizer_iff.mp hpx
  have hxy : x ≠ y := hU.adj.ne
  let α : ↥(stabilizer G x) ≃* ↥(stabilizer Gb xb) := ψ.symm.trans a
  let ζ₁ : ↥I ≃* ↥Ib := φ.trans z
  have hEq : ∀ (i : ↥I) (h : (i : G) ∈ stabilizer G x),
      ((α ⟨i, h⟩ : ↥(stabilizer Gb xb)) : Gb) = ((ζ₁ i : ↥Ib) : Gb) := by
    intro i h
    have hiIx : (i : G) ∈ I ⊓ stabilizer G x := Subgroup.mem_inf.mpr ⟨i.2, h⟩
    have hg₀ : ((ψ.symm ⟨i, h⟩ : ↥(stabilizer G x)) : G) ∈ I ⊓ stabilizer G x := by
      have h1 := hψ (ψ.symm ⟨i, h⟩)
      rw [MulEquiv.apply_symm_apply] at h1
      exact h1.mpr hiIx
    have h2 := hθφψ ⟨_, hg₀⟩
    have h3 := hθ ⟨_, hg₀⟩
    have e1 : totFun ψ ((ψ.symm ⟨i, h⟩ : ↥(stabilizer G x)) : G) = i := by
      rw [totFun_coe ψ, MulEquiv.apply_symm_apply]
    have e2 : totFun φ (i : G) = ((φ i : ↥I) : G) := totFun_coe φ i
    dsimp only at h2 h3
    rw [e1, e2] at h2
    rw [h2, totFun_coe z, totFun_coe a] at h3
    exact h3.symm
  have hMS' : ∀ g : ↥I, (g : G) ∈ stabilizer G x ↔
      ((ζ₁ g : ↥Ib) : Gb) ∈ stabilizer Gb xb := by
    intro g
    have h1 := hφ g
    rw [Subgroup.mem_inf, Subgroup.mem_inf] at h1
    have h2 := hZ1' (φ g)
    have h1' : (g : G) ∈ stabilizer G x ↔ ((φ g : ↥I) : G) ∈ stabilizer G x := by
      constructor
      · intro hx; exact (h1.mp ⟨g.2, hx⟩).2
      · intro hx; exact (h1.mpr ⟨(φ g).2, hx⟩).2
    exact h1'.trans h2
  obtain ⟨j, hj, hjG⟩ := hGψ 1 (one_mem _)
  have hjI : j ∈ I := (Subgroup.mem_inf.mp hj).1
  have hjx : j ∈ stabilizer G x := (Subgroup.mem_inf.mp hj).2
  have hjaIb : ((a ⟨j, hjx⟩ : ↥(stabilizer Gb xb)) : Gb) ∈ Ib := (hA2' ⟨j, hjx⟩).mp hjI
  have hjaxb : ((a ⟨j, hjx⟩ : ↥(stabilizer Gb xb)) : Gb) ∈ stabilizer Gb xb :=
    (a ⟨j, hjx⟩).2
  have hjzIb : ((z ⟨p, hpI⟩ : ↥Ib) : Gb) ∈ Ib := (z ⟨p, hpI⟩).2
  have hjzxb : ((z ⟨p, hpI⟩ : ↥Ib) : Gb) ∈ stabilizer Gb xb := (hZ1' ⟨p, hpI⟩).mp hpx
  have hAy : ∀ g : ↥(stabilizer G x), (g : G) ∈ stabilizer G y ↔
      ((α g : ↥(stabilizer Gb xb)) : Gb) ∈
        stabilizer Gb (((a ⟨j, hjx⟩ : ↥(stabilizer Gb xb)) : Gb) • yb) := by
    intro g
    set h : ↥(stabilizer G x) := ψ.symm g with hh
    have hψh : ψ h = g := by rw [hh]; exact MulEquiv.apply_symm_apply _ _
    have h1 := mem_autImage_iff ψ.symm (conjSub 1 (stabilizer G x ⊓ stabilizer G y)) h
    rw [hjG, MulEquiv.symm_symm, hψh, mem_conjSub_iff, mem_conjSub_iff] at h1
    have hjg : (g : G) ∈ stabilizer G y ↔ j⁻¹ * (h : G) * j ∈ stabilizer G y := by
      rw [Subgroup.mem_inf, Subgroup.mem_inf] at h1
      simp only [inv_one, one_mul, mul_one] at h1
      have hgx : (g : G) ∈ stabilizer G x := g.2
      have hhx : j⁻¹ * (h : G) * j ∈ stabilizer G x :=
        mul_mem (mul_mem (inv_mem hjx) h.2) hjx
      constructor
      · intro hy'; exact (h1.mpr ⟨hgx, hy'⟩).2
      · intro hy'; exact (h1.mp ⟨hhx, hy'⟩).2
    set e : ↥(stabilizer G x) := ⟨j, hjx⟩⁻¹ * h * ⟨j, hjx⟩ with he
    have hecoe : (e : G) = j⁻¹ * (h : G) * j := by simp [he]
    have hA := hA1' e
    rw [hecoe] at hA
    have hae : ((a e : ↥(stabilizer Gb xb)) : Gb) =
        (((a ⟨j, hjx⟩ : ↥(stabilizer Gb xb)) : Gb))⁻¹ * ((a h : ↥(stabilizer Gb xb)) : Gb) *
          ((a ⟨j, hjx⟩ : ↥(stabilizer Gb xb)) : Gb) := by
      rw [he, map_mul, map_mul, map_inv]
      simp
    rw [hjg, hA, hae]
    show _ ↔ ((a h : ↥(stabilizer Gb xb)) : Gb) ∈ _
    rw [mem_stabilizer_iff, mem_stabilizer_iff, mul_smul, mul_smul, inv_smul_eq_iff]
  have hZe : ∀ g : ↥I, (g : G) ∈ stabilizer G ({x, y} : Set X) ↔
      ((ζ₁ g : ↥Ib) : Gb) ∈ stabilizer Gb
        ({xb, ((z ⟨p, hpI⟩ : ↥Ib) : Gb) • yb} : Set Xb) := by
    intro g
    rw [hpair g, mem_stab_pair_conj hpx']
    have h1 := hZ2' (⟨p, hpI⟩⁻¹ * φ g * ⟨p, hpI⟩)
    have hcoe : (((⟨p, hpI⟩⁻¹ * φ g * ⟨p, hpI⟩ : ↥I)) : G) = p⁻¹ * ((φ g : ↥I) : G) * p := by
      simp
    rw [hcoe] at h1
    rw [h1, map_mul, map_mul, map_inv]
    rw [mem_stab_pair_conj (q := ((z ⟨p, hpI⟩ : ↥Ib) : Gb)) (y := yb)
      (mem_stabilizer_iff.mp hjzxb)]
    exact Iff.rfl
  have hfix : ∀ g ∈ Ib ⊓ stabilizer Gb xb,
      g • (((z ⟨p, hpI⟩ : ↥Ib) : Gb) • yb) = ((z ⟨p, hpI⟩ : ↥Ib) : Gb) • yb →
      g • (((a ⟨j, hjx⟩ : ↥(stabilizer Gb xb)) : Gb) • yb) =
        ((a ⟨j, hjx⟩ : ↥(stabilizer Gb xb)) : Gb) • yb := by
    intro g hg hgz
    obtain ⟨hgI, hgx⟩ := Subgroup.mem_inf.mp hg
    set g₀ : ↥I := ζ₁.symm ⟨g, hgI⟩ with hg₀
    have hζg₀ : ζ₁ g₀ = ⟨g, hgI⟩ := MulEquiv.apply_symm_apply _ _
    have hg₀x : (g₀ : G) ∈ stabilizer G x := by
      have := hMS' g₀
      rw [hζg₀] at this
      exact this.mpr hgx
    have hg₀pair : (g₀ : G) ∈ stabilizer G ({x, y} : Set X) := by
      rw [hZe g₀, hζg₀]
      have hgz' : g ∈ stabilizer Gb ({xb, ((z ⟨p, hpI⟩ : ↥Ib) : Gb) • yb} : Set Xb) := by
        rw [mem_stabilizer_iff, Set.smul_set_insert, Set.smul_set_singleton,
          mem_stabilizer_iff.mp hgx, hgz]
      exact hgz'
    have hg₀y : (g₀ : G) ∈ stabilizer G y := by
      rcases (mem_stabilizer_pair_iff hxy _).mp hg₀pair with ⟨-, h2⟩ | ⟨h1, -⟩
      · exact mem_stabilizer_iff.mpr h2
      · exfalso
        rw [mem_stabilizer_iff.mp hg₀x] at h1
        exact hxy h1
    have h3 := (hAy ⟨g₀, hg₀x⟩).mp hg₀y
    rw [hEq g₀ hg₀x, hζg₀] at h3
    exact mem_stabilizer_iff.mp h3
  have hEqS := stab_inf_eq_of_fix hVb (Subgroup.mem_inf.mpr ⟨hjaIb, hjaxb⟩)
    (Subgroup.mem_inf.mpr ⟨hjzIb, hjzxb⟩) hfix
  have hs : IsSimilarity I x y Ib xb (((z ⟨p, hpI⟩ : ↥Ib) : Gb) • yb) α ζ₁ := by
    refine ⟨(map_subgroupOf_eq_iff ζ₁ _ _).mpr hMS', fun i h => hEq i h, ?_, ?_⟩
    · rw [map_subgroupOf_eq_iff]
      intro g
      rw [hAy g]
      have h1 := SetLike.ext_iff.mp hEqS ((α g : ↥(stabilizer Gb xb)) : Gb)
      rw [Subgroup.mem_inf, Subgroup.mem_inf] at h1
      have hαx : ((α g : ↥(stabilizer Gb xb)) : Gb) ∈ stabilizer Gb xb := (α g).2
      constructor
      · intro hh; exact (h1.mp ⟨hαx, hh⟩).2
      · intro hh; exact (h1.mpr ⟨hαx, hh⟩).2
    · rw [map_subgroupOf_eq_iff]
      exact hZe
  obtain ⟨β, ζ, hsim⟩ := IsSimilarity.conj_target hs hjzIb hjzxb
  refine ⟨β, ζ, ?_⟩
  rwa [inv_smul_smul] at hsim

end CFSG.Quasithin.H13.AS91
