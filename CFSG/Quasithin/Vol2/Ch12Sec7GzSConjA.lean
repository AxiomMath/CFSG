module

public import CFSG.Quasithin.Vol2.Ch12Sec7IdentA
public import CFSG.Quasithin.Vol2.Ch12Sec7GzConj

public section

namespace CFSG.Quasithin.H13.I1277

open CFSG.Open

theorem Gz_conj_eq {G : Type} [Group G] (g z : G) : Gz (g * z * g⁻¹) = cjS g (Gz z) := by
  ext x
  rw [mem_cjS_iff, Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    calc g⁻¹ * x * g * z = g⁻¹ * (x * (g * z * g⁻¹)) * g := by group
      _ = g⁻¹ * (g * z * g⁻¹ * x) * g := by rw [h]
      _ = z * (g⁻¹ * x * g) := by group
  · intro h
    calc x * (g * z * g⁻¹) = g * (g⁻¹ * x * g * z) * g⁻¹ := by group
      _ = g * (z * (g⁻¹ * x * g)) * g⁻¹ := by rw [h]
      _ = g * z * g⁻¹ * x := by group

theorem injective_conj_toMonoidHom {G : Type} [Group G] (g : G) :
    Function.Injective (MulAut.conj g).toMonoidHom := by
  rw [MulEquiv.coe_toMonoidHom]
  exact (MulAut.conj g).injective

theorem pCoreOf_cjS {G : Type} [Group G] (g : G) (H : Subgroup G) :
    pCoreOf 2 (cjS g H) = cjS g (pCoreOf 2 H) := by
  have hp := CFSG.pCore_map_iso 2
    (Subgroup.equivMapOfInjective H (MulAut.conj g).toMonoidHom (injective_conj_toMonoidHom g))
  unfold pCoreOf cjS
  rw [← hp, Subgroup.map_map, Subgroup.map_map]
  congr 1 <;> ext x <;> simp [MulAut.conj_apply]

theorem cjS_zpowers {G : Type} [Group G] (g z : G) :
    cjS g (Subgroup.zpowers z) = Subgroup.zpowers (g * z * g⁻¹) := by
  unfold cjS
  rw [MonoidHom.map_zpowers, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]

theorem coe_equivMap_cjS {G : Type} [Group G] (g : G) (K : Subgroup G) (w : ↥K) :
    ((Subgroup.equivMapOfInjective K (MulAut.conj g).toMonoidHom
      (injective_conj_toMonoidHom g) w : ↥(cjS g K)) : G) = g * (w : G) * g⁻¹ := by
  simp only [Subgroup.coe_equivMapOfInjective_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]

theorem exists_mulEquiv_cjS {G : Type} [Group G] (g : G) (K : Subgroup G) :
    ∃ E : ↥(cjS g K) ≃* ↥K, ∀ y : ↥(cjS g K), ((E y : ↥K) : G) = g⁻¹ * (y : G) * g := by
  refine ⟨(Subgroup.equivMapOfInjective K (MulAut.conj g).toMonoidHom
    (injective_conj_toMonoidHom g)).symm, fun y => ?_⟩
  have h2 := coe_equivMap_cjS g K ((Subgroup.equivMapOfInjective K (MulAut.conj g).toMonoidHom
    (injective_conj_toMonoidHom g)).symm y)
  rw [MulEquiv.apply_symm_apply] at h2
  rw [h2]
  group

theorem exists_surj_ker_cjS {G : Type} [Group G] {N : Type*} [Group N] (g : G) (K : Subgroup G)
    (f : ↥K →* N) (hfsurj : Function.Surjective f) (hfker : f.ker = (pCoreOf 2 K).subgroupOf K) :
    ∃ f' : ↥(cjS g K) →* N, Function.Surjective f' ∧
      f'.ker = (cjS g (pCoreOf 2 K)).subgroupOf (cjS g K) := by
  obtain ⟨E, hE⟩ := exists_mulEquiv_cjS g K
  refine ⟨f.comp E.toMonoidHom, ?_, ?_⟩
  · intro b
    obtain ⟨a, ha⟩ := hfsurj b
    refine ⟨E.symm a, ?_⟩
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply, ha]
  · ext y
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      ← MonoidHom.mem_ker, hfker, Subgroup.mem_subgroupOf, hE, mem_cjS_iff]

theorem mem_centralizer_cjS_iff {G : Type} [Group G] (g x : G) (P : Subgroup G) :
    x ∈ Subgroup.centralizer ((cjS g P : Subgroup G) : Set G) ↔
      g⁻¹ * x * g ∈ Subgroup.centralizer ((P : Subgroup G) : Set G) := by
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro hx y hy
    have hgy : g * y * g⁻¹ ∈ cjS g P := by
      rw [mem_cjS_iff, show g⁻¹ * (g * y * g⁻¹) * g = y by group]
      exact hy
    have h1 := hx (g * y * g⁻¹) hgy
    calc y * (g⁻¹ * x * g) = g⁻¹ * (g * y * g⁻¹ * x) * g := by group
      _ = g⁻¹ * (x * (g * y * g⁻¹)) * g := by rw [h1]
      _ = g⁻¹ * x * g * y := by group
  · intro hx y hy
    have hy' : y ∈ cjS g P := hy
    have hy'' : g⁻¹ * y * g ∈ P := mem_cjS_iff.mp hy'
    have h1 := hx (g⁻¹ * y * g) hy''
    calc y * x = g * (g⁻¹ * y * g * (g⁻¹ * x * g)) * g⁻¹ := by group
      _ = g * (g⁻¹ * x * g * (g⁻¹ * y * g)) * g⁻¹ := by rw [h1]
      _ = x * y := by group

theorem inf_centralizer_cjS_le {G : Type} [Group G] (g : G) (K P : Subgroup G)
    (h : K ⊓ Subgroup.centralizer (P : Set G) ≤ P) :
    cjS g K ⊓ Subgroup.centralizer ((cjS g P : Subgroup G) : Set G) ≤ cjS g P := by
  intro x hx
  obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.mp hx
  rw [mem_cjS_iff] at hx1 ⊢
  exact h (Subgroup.mem_inf.mpr ⟨hx1, (mem_centralizer_cjS_iff g x P).mp hx2⟩)

theorem cjS_Gz_le_normalizer {G : Type} [Group G] (g z : G) (A : Subgroup G)
    (hCA : Gz z ≤ Subgroup.normalizer (A : Set G)) :
    cjS g (Gz z) ≤ Subgroup.normalizer ((cjS g A : Subgroup G) : Set G) := by
  intro w hw
  have hN := Subgroup.mem_normalizer_iff.mp (hCA (mem_cjS_iff.mp hw))
  rw [Subgroup.mem_normalizer_iff]
  intro y
  have e : g⁻¹ * (w * y * w⁻¹) * g = (g⁻¹ * w * g) * (g⁻¹ * y * g) * (g⁻¹ * w * g)⁻¹ := by
    group
  simp only [SetLike.mem_coe, mem_cjS_iff, e]
  exact hN (g⁻¹ * y * g)

theorem structAt_conj {G : Type} [Group G] [Finite G] (g z : G) (h : StructAt G z) :
    StructAt G (g * z * g⁻¹) := by
  obtain ⟨hext, hP, hcent, ⟨f, hfsurj, hfker⟩, A, B, hA, hB, hA16, hB16, hAB, hAB', hCA, hCB⟩ := h
  obtain ⟨f', hf'surj, hf'ker⟩ := exists_surj_ker_cjS g (Gz z) f hfsurj hfker
  have hP' : Nat.card ↥(cjS g (pCoreOf 2 (Gz z))) = 128 := by
    rw [card_cjS]
    exact hP
  have hA' : Nat.card ↥(cjS g A) = 16 := by
    rw [card_cjS]
    exact hA16
  have hB' : Nat.card ↥(cjS g B) = 16 := by
    rw [card_cjS]
    exact hB16
  have hsup : cjS g A ⊔ cjS g B = cjS g (pCoreOf 2 (Gz z)) := by
    rw [← hAB]
    exact (Subgroup.map_sup A B (MulAut.conj g).toMonoidHom).symm
  have hinf : cjS g A ⊓ cjS g B = Subgroup.zpowers (g * z * g⁻¹) := by
    rw [← cjS_inf, hAB', cjS_zpowers]
  unfold StructAt
  rw [Gz_conj_eq, pCoreOf_cjS]
  exact ⟨CFSG.LargeExtraspecial.isExtraspecialPGroup_of_mulEquiv
      (Subgroup.equivMapOfInjective (pCoreOf 2 (Gz z)) (MulAut.conj g).toMonoidHom
        (injective_conj_toMonoidHom g)) hext,
    hP', inf_centralizer_cjS_le g (Gz z) (pCoreOf 2 (Gz z)) hcent, ⟨f', hf'surj, hf'ker⟩,
    cjS g A, cjS g B, isElemAbelian_cjS hA, isElemAbelian_cjS hB, hA', hB', hsup, hinf,
    cjS_Gz_le_normalizer g z A hCA, cjS_Gz_le_normalizer g z B hCB⟩

end CFSG.Quasithin.H13.I1277

end
