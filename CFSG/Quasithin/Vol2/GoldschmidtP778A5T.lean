module

public import CFSG.Quasithin.Vol2.GoldschmidtP778A5E1Mem
public import CFSG.Quasithin.Vol2.GoldschmidtP778A5E2Amb
public import CFSG.Quasithin.Vol2.GoldschmidtP778A5S5Cls
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.Quasithin.E1.ThinA5

open Equiv CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.Quasithin.E1.LiftS5
open scoped commutatorElement

variable {G : Type*} [Group G] [Finite G] {H T A : Subgroup G} (ψ : ↥H →* Perm (Fin 5))

omit [Finite G] in
theorem map_conjSub (h : ↥H) :
    ((A1b.conjSub (h : G) A).subgroupOf H).map ψ =
      ((A.subgroupOf H).map ψ).map (MulAut.conj (ψ h)).toMonoidHom := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hy' : (h : G)⁻¹ * (y : G) * h ∈ A := A1b.mem_conjSub_iff.1 hy
    refine ⟨ψ (h⁻¹ * y * h), ⟨h⁻¹ * y * h, ?_, rfl⟩, ?_⟩
    · show (((h⁻¹ * y * h : ↥H)) : G) ∈ A
      simpa using hy'
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv]
      group
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    have hz' : (z : G) ∈ A := hz
    refine ⟨h * z * h⁻¹, ?_, ?_⟩
    · show (((h * z * h⁻¹ : ↥H)) : G) ∈ A1b.conjSub (h : G) A
      rw [A1b.mem_conjSub_iff]
      simpa [mul_assoc] using hz'
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv]

theorem exists_conj_le_T (hT : IsSylowIn 2 T H) (hAH : A ≤ H) (hA : IsPGroup 2 A) :
    ∃ h ∈ H, A1b.conjSub h A ≤ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS, hAS⟩ := exists_isSylowIn_ge 2 hAH hA
  obtain ⟨g, hg, hTS⟩ := B6.isSylowTwoOf_exists_conj hS hT
  refine ⟨g, hg, ?_⟩
  rw [hTS]
  exact Subgroup.map_mono hAS

omit [Finite G] in
theorem isPGroup_of_isElemAbelian (hA : IsElemAbelian 2 A) : IsPGroup 2 A :=
  CFSG.Open.IsElemAbelian.isPGroup hA

omit [Finite G] in
theorem le_T_of_image_bot (hker : IsPGroup 2 ψ.ker) (hT : IsSylowIn 2 T H) (hAH : A ≤ H)
    (h : (A.subgroupOf H).map ψ = ⊥) : A ≤ T := by
  have h1 : A.subgroupOf H ≤ ψ.ker := (Subgroup.map_eq_bot_iff _).1 h
  intro a ha
  exact ker_le_T ψ hker hT ⟨⟨a, hAH ha⟩, h1 ha, rfl⟩

omit [Finite G] in
theorem conj_props (g : Perm (Fin 5)) (hA5 : alternatingGroup (Fin 5) ≤ ψ.range)
    (hker : IsPGroup 2 ψ.ker) :
    alternatingGroup (Fin 5) ≤ ((MulAut.conj g).toMonoidHom.comp ψ).range ∧
      IsPGroup 2 ((MulAut.conj g).toMonoidHom.comp ψ).ker := by
  constructor
  · intro σ hσ
    have h1 : g⁻¹ * σ * g ∈ alternatingGroup (Fin 5) := by
      have := (alternatingGroup.normal (α := Fin 5)).conj_mem σ hσ g⁻¹
      simpa using this
    obtain ⟨x, hx⟩ := hA5 h1
    refine ⟨x, ?_⟩
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hx]
    group
  · have : ((MulAut.conj g).toMonoidHom.comp ψ).ker = ψ.ker := by
      ext x
      simp [MonoidHom.mem_ker]
    rw [this]
    exact hker

theorem map_conj_g0_Vo : Vo.map (MulAut.conj g0).toMonoidHom = Vo := by
  refine Subgroup.eq_of_le_of_card_ge ?_
    (by rw [Subgroup.card_map_of_injective (MulAut.conj g0).injective])
  rintro _ ⟨v, hv, rfl⟩
  exact g0_conj_vo v hv

theorem nParam_le_one_of_a5Quot (hA5 : alternatingGroup (Fin 5) ≤ ψ.range)
    (hker : IsPGroup 2 ψ.ker)
    (hno : ∀ A : Subgroup G, A ≤ H → IsElemAbelian 2 A →
      ¬ ((A.subgroupOf H).map ψ ≤ alternatingGroup (Fin 5) ∧
        Nat.card ↥((A.subgroupOf H).map ψ) = 4)) :
    nParam H ≤ 1 := by
  obtain ⟨T, hT⟩ := exists_isSylowIn_two H
  have hTH := hT.le
  refine (nParam_le_iff Nat.one_pos).mpr ((inE_iff_inEFor hT).mpr fun Ω hΩ => ?_)
  refine le_antisymm (sup_le (eGen_le 1 H T Ω) inf_le_left) ?_
  by_cases hex : ∃ A ∈ Ω, A ≤ T ∧ (A.subgroupOf H).map ψ ≠ ⊥
  · obtain ⟨A, hAΩ, hAT, hne⟩ := hex
    have hAH := hΩ.le A hAΩ
    have hAab := hΩ.isElemAbelian A hAΩ
    have hAmem : ∀ K, IsE 1 H T A K → K ≤ eGen 1 H T Ω := fun K hK =>
      le_iSup₂_of_le A hAΩ (le_iSup_of_le hAT (le_iSup₂_of_le K hK le_rfl))
    by_cases hV2 : Nat.card ↥((A.subgroupOf H).map ψ) ≤ 2
    · exact le_sup_of_le_left
        (hAmem H (isE_one_top_of_card_le_two ψ hA5 hker hT hAT hne hV2))
    · have hVe2 : ∀ x ∈ (A.subgroupOf H).map ψ, x ^ 2 = 1 := by
        rintro _ ⟨a, ha, rfl⟩
        rw [← map_pow]
        have h1 : a ^ 2 = 1 := Subtype.ext (hAab.2 a ha)
        rw [h1, map_one]
      have hVc : ∀ x ∈ (A.subgroupOf H).map ψ, ∀ y ∈ (A.subgroupOf H).map ψ, x * y = y * x := by
        rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
        rw [← map_mul, ← map_mul]
        congr 1
        exact Subtype.ext (commute_of_isElemAbelian hAab ha hb)
      rcases cls hVe2 hVc (by omega) with ⟨hVA, hV4⟩ | ⟨g, hg⟩
      · exact absurd ⟨hVA, hV4⟩ (hno A hAH hAab)
      · set ψ1 := (MulAut.conj g).toMonoidHom.comp ψ with hψ1
        obtain ⟨hA51, hker1⟩ := conj_props ψ g hA5 hker
        have hV1 : (A.subgroupOf H).map ψ1 = Vo := by
          rw [hψ1, ← Subgroup.map_map]
          exact hg
        have hrange1 : ψ1.range = ⊤ := by
          have : sA ∈ (A.subgroupOf H).map ψ1 := hV1 ▸ sA_mem_Vo
          obtain ⟨a, -, ha⟩ := this
          exact eq_top_of_alt_le_of_odd hA51 ⟨a, ha⟩ sign_sA
        set ψ2 := (MulAut.conj g0).toMonoidHom.comp ψ1 with hψ2
        obtain ⟨hA52, hker2⟩ := conj_props ψ1 g0 hA51 hker1
        have hV2' : (A.subgroupOf H).map ψ2 = Vo := by
          rw [hψ2, ← Subgroup.map_map, hV1]
          exact map_conj_g0_Vo
        have hrange2 : ψ2.range = ⊤ := by
          have : sA ∈ (A.subgroupOf H).map ψ2 := hV2' ▸ sA_mem_Vo
          obtain ⟨a, -, ha⟩ := this
          exact eq_top_of_alt_le_of_odd hA52 ⟨a, ha⟩ sign_sA
        have hK1 := isE_one_kA ψ1 hA51 hrange1 hker1 hT hAT hV1
        have hK2 := isE_one_kA ψ2 hA52 hrange2 hker2 hT hAT hV2'
        have hgen : H ≤ kA ψ1 ⊔ kA ψ2 := by
          have h1 : C1.comap ψ1 ⊔ C1.comap ψ2 = ⊤ := by
            have hc2 : C1.comap ψ2 = (C1.comap (MulAut.conj g0).toMonoidHom).comap ψ1 := by
              rw [Subgroup.comap_comap]
            rw [hc2, Subgroup.comap_sup_eq_of_le_range ψ1 (hrange1 ▸ le_top) (hrange1 ▸ le_top),
              c1_sup_conj, Subgroup.comap_top]
          have h2 : kA ψ1 ⊔ kA ψ2 = ((C1.comap ψ1) ⊔ (C1.comap ψ2)).map H.subtype :=
            (Subgroup.map_sup _ _ _).symm
          rw [h2, h1, Subgroup.map_top, Subgroup.range_subtype]
        exact le_sup_of_le_left (hgen.trans (sup_le (hAmem _ hK1) (hAmem _ hK2)))
  · push Not at hex
    have hall : ∀ A ∈ Ω, A ≤ T := by
      intro A hA
      have hAH := hΩ.le A hA
      have hbot : (A.subgroupOf H).map ψ = ⊥ := by
        obtain ⟨h, hh, hconj⟩ := exists_conj_le_T hT hAH
          (isPGroup_of_isElemAbelian (hΩ.isElemAbelian A hA))
        have h1 := hex _ (hΩ.conj A hA h hh) hconj
        rw [map_conjSub ψ ⟨h, hh⟩] at h1
        have h2 := (Subgroup.map_eq_bot_iff _).1 h1
        have h3 : (A.subgroupOf H).map ψ ≤ ⊥ := by
          intro x hx
          have : (MulAut.conj (ψ ⟨h, hh⟩)).toMonoidHom x = 1 := MonoidHom.mem_ker.mp (h2 hx)
          have h4 : ψ ⟨h, hh⟩ * x * (ψ ⟨h, hh⟩)⁻¹ = 1 := this
          rw [Subgroup.mem_bot, conj_eq_one_iff.mp h4]
        exact le_bot_iff.mp h3
      exact le_T_of_image_bot ψ hker hT hAH hbot
    have key : ∀ z ∈ H, A1b.conjSub z (weakClosure T Ω) ≤ weakClosure T Ω := by
      intro z hz
      rw [A1b.conjSub, Subgroup.map_le_iff_le_comap]
      refine iSup₂_le fun B hB => iSup_le fun _ => ?_
      rw [← Subgroup.map_le_iff_le_comap]
      have hzB : A1b.conjSub z B ∈ Ω := hΩ.conj B hB z hz
      exact le_iSup₂_of_le (A1b.conjSub z B) hzB (le_iSup_of_le (hall _ hzB) le_rfl)
    have hNorm : H ≤ Subgroup.normalizer (weakClosure T Ω : Set G) := by
      intro y hy
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · intro hx
        exact key y hy (A1b.mem_conjSub_of_mem hx)
      · intro hx
        have := key y⁻¹ (H.inv_mem hy) (A1b.mem_conjSub_of_mem hx)
        simpa [mul_assoc] using this
    exact le_sup_of_le_right (le_inf le_rfl hNorm)

end CFSG.Quasithin.E1.ThinA5
