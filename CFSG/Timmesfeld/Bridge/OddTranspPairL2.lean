module

public import CFSG.Timmesfeld.Bridge.OddTranspQ
public import CFSG.Timmesfeld.Bridge.OddTranspGenL2
public import CFSG.Timmesfeld.Bridge.OddTranspNPC

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity CFSG.Timmesfeld.Bridge.Asc72
  CFSG.Timmesfeld.Bridge.OddTransp
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] {D : Set G}

namespace OddTransp

theorem eq_top_of_sup_center_eq_top {H : Type*} [Group H] (hperf : commutator H = ⊤)
    {M : Subgroup H} (hM : M ⊔ Subgroup.center H = ⊤) : M = ⊤ := by
  have hcl : ∀ x y z : H, z ∈ Subgroup.center H → ⁅x * z, y⁆ = ⁅x, y⁆ := by
    intro x y z hz
    rw [commutatorElement_def, commutatorElement_def, mul_assoc x z y,
      ← Subgroup.mem_center_iff.mp hz y, ← mul_assoc]
    group
  have hcr : ∀ x y z : H, z ∈ Subgroup.center H → ⁅x, y * z⁆ = ⁅x, y⁆ := by
    intro x y z hz
    rw [← commutatorElement_inv, hcl _ _ _ hz, commutatorElement_inv]
  have hprod : ∀ g : H, ∃ m ∈ M, ∃ z ∈ Subgroup.center H, g = m * z := by
    intro g
    have hg : g ∈ (↑(M ⊔ Subgroup.center H) : Set H) := by
      rw [hM]
      exact Subgroup.mem_top g
    rw [Subgroup.mul_normal] at hg
    obtain ⟨m, hm, z, hz, rfl⟩ := Set.mem_mul.mp hg
    exact ⟨m, hm, z, hz, rfl⟩
  rw [eq_top_iff, ← hperf, commutator_def, Subgroup.commutator_le]
  intro x _ y _
  obtain ⟨m, hm, z, hz, rfl⟩ := hprod x
  obtain ⟨m', hm', z', hz', rfl⟩ := hprod y
  rw [hcl _ _ _ hz, hcr _ _ _ hz', commutatorElement_def]
  exact M.mul_mem (M.mul_mem (M.mul_mem hm hm') (M.inv_mem hm)) (M.inv_mem hm')

end OddTransp

namespace ThirdKindHyp

variable {S : Sylow 2 G} {a b c : G} {n : ℕ} (h : ThirdKindHyp G D S a b c n)
include h

theorem exists_closure_eq_top [Finite G] (hperf : commutator G = ⊤)
    (hB : CFSG.BenderSuzuki.IsBenderGroup (G ⧸ zStar G))
    (hgen : InvolutionThreeGen (G ⧸ zStar G)) {α β : G} (hα : α ∈ D ∩ (S : Set G))
    (hβ : β ∈ D ∩ (S : Set G)) (hαβ : α⁻¹ * β ∉ CFSG.pCore 2 G) :
    ∃ x ∈ D, Subgroup.closure {α, β, x} ⊔ CFSG.pCore 2 G = ⊤ := by
  set π := QuotientGroup.mk' (zStar G) with hπdef
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hDZ : ∀ d ∈ D, d ∉ zStar G := by
    rcases h.setup.subset_or_disjoint (zStar G) with h' | h'
    · exfalso
      have htop := h.setup.eq_top_of_subset _ h'
      have := (IsBenderGroup.isSimpleGroup hB).toNontrivial
      obtain ⟨x, y, hxy⟩ := exists_pair_ne (G ⧸ zStar G)
      apply hxy
      obtain ⟨x, rfl⟩ := hπs x
      obtain ⟨y, rfl⟩ := hπs y
      rw [hπdef, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
      exact htop ▸ Subgroup.mem_top _
    · exact h'
  have hord : ∀ d ∈ D, orderOf (π d) = 2 := by
    intro d hd
    refine orderOf_eq_prime ?_ ?_
    · rw [← map_pow, pow_two, h.oddT.mul_self_eq_one hd, map_one]
    · intro h1
      exact hDZ d hd ((QuotientGroup.eq_one_iff d).mp h1)
  have hcomm : Commute α β := h.commute_of_mem hα hβ
  have hne : π α ≠ π β := by
    intro heq
    apply hαβ
    have h1 : α⁻¹ * β ∈ zStar G := by
      rw [← QuotientGroup.eq_one_iff (N := zStar G), ← QuotientGroup.mk'_apply, ← hπdef,
        map_mul, map_inv, heq, inv_mul_cancel]
    refine mem_pCore_of_mem_center h1 ?_
    have hα2 := h.oddT.mul_self_eq_one hα.1
    have hβ2 := h.oddT.mul_self_eq_one hβ.1
    have e : α⁻¹ * β * (α⁻¹ * β) = 1 := by
      rw [inv_eq_of_mul_eq_one_right hα2, mul_assoc, ← mul_assoc β α, ← hcomm.eq, mul_assoc,
        hβ2, mul_one, hα2]
    rw [e]
    exact Subgroup.one_mem _
  obtain ⟨t, ht, hcl⟩ := hgen (π α) (π β) (hord α hα.1) (hord β hβ.1) hne (hcomm.map π)
  obtain ⟨d₀, hd₀⟩ := h.setup.nonempty
  obtain ⟨cq, hcq⟩ := isConj_iff.mp (IsBenderGroup.isConj_of_orderOf_eq_two hB (hord d₀ hd₀) ht)
  obtain ⟨g, rfl⟩ := hπs cq
  refine ⟨g * d₀ * g⁻¹, h.setup.conj_mem g hd₀, ?_⟩
  set K := Subgroup.closure ({α, β, g * d₀ * g⁻¹} : Set G) with hKdef
  have hKmap : K.map π = ⊤ := by
    rw [hKdef, MonoidHom.map_closure, Set.image_insert_eq, Set.image_insert_eq,
      Set.image_singleton, map_mul, map_mul, map_inv, hcq]
    exact hcl
  have hKZ : K ⊔ zStar G = ⊤ := by
    have h1 := Subgroup.comap_map_eq π K
    rw [hKmap, Subgroup.comap_top, hπdef, QuotientGroup.ker_mk'] at h1
    exact h1.symm
  set ρ := QuotientGroup.mk' (CFSG.pCore 2 G) with hρdef
  have hρs : Function.Surjective ρ := QuotientGroup.mk'_surjective _
  have hzmap : (zStar G).map ρ = Subgroup.center (G ⧸ CFSG.pCore 2 G) := by
    rw [zStar]
    exact Subgroup.map_comap_eq_self_of_surjective hρs _
  have hKρ : K.map ρ ⊔ Subgroup.center (G ⧸ CFSG.pCore 2 G) = ⊤ := by
    rw [← hzmap, ← Subgroup.map_sup, hKZ, Subgroup.map_top_of_surjective _ hρs]
  have hKρ' := eq_top_of_sup_center_eq_top (commutator_eq_top_of_surjective hρs hperf) hKρ
  have h1 := Subgroup.comap_map_eq ρ K
  rw [hKρ', Subgroup.comap_top, hρdef, QuotientGroup.ker_mk'] at h1
  exact h1.symm

theorem center_le_sup_of_gen [Finite G] (hB : CFSG.BenderSuzuki.IsBenderGroup (G ⧸ zStar G))
    (hgen : InvolutionThreeGen (G ⧸ zStar G))
    (hDD : ∃ u ∈ D ∩ (S : Set G), ∃ v ∈ D ∩ (S : Set G), u ≠ v ∧ u * v ∈ D)
    (hQab : ∀ p ∈ ⁅CFSG.pCore 2 G, (⊤ : Subgroup G)⁆, ∀ q ∈ ⁅CFSG.pCore 2 G, (⊤ : Subgroup G)⁆,
      Commute p q) {α β : G} (hα : α ∈ D ∩ (S : Set G)) (hβ : β ∈ D ∩ (S : Set G))
    (hαβ : α⁻¹ * β ∉ CFSG.pCore 2 G) :
    CFSG.pCore 2 G ⊓ Subgroup.center G ≤
      ⁅CFSG.pCore 2 G, Subgroup.zpowers α⁆ ⊔ ⁅CFSG.pCore 2 G, Subgroup.zpowers β⁆ := by
  obtain ⟨u, hu, v, hv, huv, huvD⟩ := hDD
  have hperf : commutator G = ⊤ := OddTransp.commutator_eq_top h.setup
    ⟨u, hu.1, v, hv.1, huv, h.commute_of_mem hu hv, huvD⟩
  obtain ⟨x, hx, hcl⟩ := h.exists_closure_eq_top hperf hB hgen hα hβ hαβ
  exact h.center_le_sup_of_closure hperf hQab hα hβ hx hcl

theorem center_le_sup_of_psl2 [Finite G] {m : ℕ} (hm : 2 ≤ m)
    (e : G ⧸ zStar G ≃* CFSG.Theory.Comparator.PSL2Model m)
    (hDD : ∃ u ∈ D ∩ (S : Set G), ∃ v ∈ D ∩ (S : Set G), u ≠ v ∧ u * v ∈ D)
    (hQab : ∀ p ∈ ⁅CFSG.pCore 2 G, (⊤ : Subgroup G)⁆, ∀ q ∈ ⁅CFSG.pCore 2 G, (⊤ : Subgroup G)⁆,
      Commute p q) {α β : G} (hα : α ∈ D ∩ (S : Set G)) (hβ : β ∈ D ∩ (S : Set G))
    (hαβ : α⁻¹ * β ∉ CFSG.pCore 2 G) :
    CFSG.pCore 2 G ⊓ Subgroup.center G ≤
      ⁅CFSG.pCore 2 G, Subgroup.zpowers α⁆ ⊔ ⁅CFSG.pCore 2 G, Subgroup.zpowers β⁆ :=
  h.center_le_sup_of_gen (.isPSL2 m hm e) ((involutionThreeGen_psl2 hm).of_mulEquiv e) hDD hQab
    hα hβ hαβ

end ThirdKindHyp

namespace OddTransp

theorem oddTranspCenterPairPSL2 :
    ∀ (G : Type) [Group G] [Finite G] (D : Set G) (S : Sylow 2 G) (a b c : G) (n : ℕ),
      ThirdKindHyp G D S a b c n →
      (∃ m : ℕ, 2 ≤ m ∧ Nonempty (G ⧸ zStar G ≃* CFSG.Theory.Comparator.PSL2Model m)) →
      (∃ u ∈ D ∩ (S : Set G), ∃ v ∈ D ∩ (S : Set G), u ≠ v ∧ u * v ∈ D) →
      (∀ p ∈ ⁅CFSG.pCore 2 G, (⊤ : Subgroup G)⁆, ∀ q ∈ ⁅CFSG.pCore 2 G, (⊤ : Subgroup G)⁆,
        Commute p q) →
      ∀ α ∈ D ∩ (S : Set G), ∀ β ∈ D ∩ (S : Set G), α⁻¹ * β ∉ CFSG.pCore 2 G →
        CFSG.pCore 2 G ⊓ Subgroup.center G ≤
          ⁅CFSG.pCore 2 G, Subgroup.zpowers α⁆ ⊔ ⁅CFSG.pCore 2 G, Subgroup.zpowers β⁆ := by
  intro G _ _ D S a b c n h ⟨m, hm, ⟨e⟩⟩ hDD hQab α hα β hβ hαβ
  exact h.center_le_sup_of_psl2 hm e hDD hQab hα hβ hαβ

end OddTransp

end CFSG.Timmesfeld.Bridge
