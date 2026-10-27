module

public import CFSG.Quasithin.Vol2.Ch11SecU1U3A
public import CFSG.Quasithin.Vol2.Ch11SecU1L3IG

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecU1.U3

open CFSG.Quasithin.E2P.Asc80 CFSG.Quasithin

variable {G : Type} [Group G] {L : Subgroup G} {C : Type} [Group C]

abbrev embU (ψ : C ≃* ↥L) : C →* G := L.subtype.comp ψ.toMonoidHom

theorem embU_injective (ψ : C ≃* ↥L) : Function.Injective (embU ψ) :=
  L.subtype_injective.comp ψ.injective

theorem range_embU (ψ : C ≃* ↥L) : (embU ψ).range = L := by
  rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr ψ.surjective, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype]

theorem exists_embU_eq (ψ : C ≃* ↥L) {x : G} (hx : x ∈ L) : ∃ c, embU ψ c = x := by
  rw [← MonoidHom.mem_range, range_embU]
  exact hx

theorem orderOf_embU (ψ : C ≃* ↥L) (c : C) : orderOf (embU ψ c) = orderOf c :=
  orderOf_injective _ (embU_injective ψ) c

theorem eq_or_eq_of_isCoatom (ψ : C ≃* ↥L) {B : Subgroup C} (hB : IsCoatom B) {N : Subgroup G}
    (hBN : B.map (embU ψ) ≤ N) (hNL : N ≤ L) : N = B.map (embU ψ) ∨ N = L := by
  have hN : (N.comap (embU ψ)).map (embU ψ) = N :=
    Subgroup.map_comap_eq_self (by rw [range_embU]; exact hNL)
  rcases hB.le_iff.mp (Subgroup.map_le_iff_le_comap.mp hBN) with h | h
  · right
    rw [← hN, h, ← MonoidHom.range_eq_map, range_embU]
  · left
    rw [← hN, h]

theorem inf_centralizer_embU (ψ : C ≃* ↥L) (c : C) :
    L ⊓ Subgroup.centralizer ({embU ψ c} : Set G) =
      (Subgroup.centralizer ({c} : Set C)).map (embU ψ) := by
  ext y
  constructor
  · rintro ⟨hyL, hyC⟩
    obtain ⟨d, rfl⟩ := exists_embU_eq ψ hyL
    refine ⟨d, ?_, rfl⟩
    have h1 : embU ψ d * embU ψ c = embU ψ c * embU ψ d :=
      Subgroup.mem_centralizer_singleton_iff.mp hyC
    show d ∈ Subgroup.centralizer ({c} : Set C)
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply embU_injective ψ
    rw [map_mul, map_mul, h1]
  · rintro ⟨d, hd, rfl⟩
    have h1 : d * c = c * d := Subgroup.mem_centralizer_singleton_iff.mp hd
    refine ⟨(ψ d).2, ?_⟩
    show embU ψ d ∈ Subgroup.centralizer ({embU ψ c} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, h1]

variable {p : ℕ} [Fact p.Prime] {F : Type} [Field F]

theorem inner_conj (hp2 : p ≠ 2) (hF : Nat.card F = p ^ 2) (ψ : PSU3F p F ≃* ↥L) :
    ∀ x ∈ L, ∀ y ∈ L, orderOf x = 2 → orderOf y = 2 → ∃ g ∈ L, g * x * g⁻¹ = y := by
  intro x hx y hy hx2 hy2
  obtain ⟨x', rfl⟩ := exists_embU_eq ψ hx
  obtain ⟨y', rfl⟩ := exists_embU_eq ψ hy
  rw [orderOf_embU] at hx2 hy2
  obtain ⟨c, hc⟩ := isConj_iff.mp ((isConj_zcU hp2 hF hx2).trans (isConj_zcU hp2 hF hy2).symm)
  exact ⟨embU ψ c, (ψ c).2, by rw [← map_inv, ← map_mul, ← map_mul, hc]⟩

omit [Fact p.Prime] in
theorem centralizer_conj {X : Type*} [Group X] (c z : X) :
    Subgroup.centralizer ({c * z * c⁻¹} : Set X) =
      (Subgroup.centralizer ({z} : Set X)).map (MulAut.conj c).toMonoidHom := by
  ext y
  rw [Subgroup.mem_map_equiv, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff, MulAut.conj_symm_apply]
  constructor
  · intro h
    calc c⁻¹ * y * c * z = c⁻¹ * (y * (c * z * c⁻¹)) * c := by group
      _ = c⁻¹ * ((c * z * c⁻¹) * y) * c := by rw [h]
      _ = z * (c⁻¹ * y * c) := by group
  · intro h
    calc y * (c * z * c⁻¹) = c * ((c⁻¹ * y * c) * z) * c⁻¹ := by group
      _ = c * (z * (c⁻¹ * y * c)) * c⁻¹ := by rw [h]
      _ = c * z * c⁻¹ * y := by group


variable [Finite F]

theorem isCoatom_centralizer [Finite G] (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hF : Nat.card F = p ^ 2)
    (hAS : SecE3.AlmostSimple L) {T : Subgroup G} (hT : IsSylowIn 2 T ⊤)
    (ψ : PSU3F p F ≃* ↥L) {x : G} (hxL : x ∈ L) (hx : orderOf x = 2) :
    IsCoatom (Subgroup.centralizer ({x} : Set G)) := by
  have hLn := hAS.normal
  have h2 : 2 ∣ Nat.card L := by
    rw [← hx, ← Subgroup.orderOf_mk x hxL]
    exact orderOf_dvd_natCard _
  obtain ⟨z₀, hz₀L, hz₀2, hz₀T, hz₀c⟩ := L3I.exists_central_involution_of_normal hLn h2 hT
  obtain ⟨g, hgL, hg⟩ := inner_conj hp2 hF ψ z₀ hz₀L x hxL hz₀2 hx
  have hTx : A1b.conjSub g T ≤ Subgroup.centralizer ({x} : Set G) := by
    rintro _ ⟨t, ht, rfl⟩
    rw [← hg, centralizer_conj, Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
    rw [Subgroup.mem_centralizer_singleton_iff]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [show g⁻¹ * (g * t * g⁻¹) * g = t by group]
    exact hz₀c t ht
  have hLC : L ⊔ Subgroup.centralizer ({x} : Set G) = ⊤ := by
    refine eq_top_iff.mpr ?_
    have hgL : A1b.conjSub g L = L := A1b.conjSub_eq_iff_mem_normalizer.mpr (by
      rw [Subgroup.normalizer_eq_top_iff.mpr hLn]
      exact Subgroup.mem_top g)
    have h1 : A1b.conjSub g (L ⊔ T) = L ⊔ A1b.conjSub g T := by
      rw [A1b.conjSub, Subgroup.map_sup, ← A1b.conjSub, ← A1b.conjSub, hgL]
    rw [← Subgroup.map_top_of_surjective (MulAut.conj g).toMonoidHom (MulAut.conj g).surjective,
      ← L3I.sup_eq_top_of_almostSimple hAS hT]
    exact h1.le.trans (sup_le_sup_left hTx _)
  obtain ⟨x', rfl⟩ := exists_embU_eq ψ hxL
  rw [orderOf_embU] at hx
  obtain ⟨c, hc⟩ := isConj_iff.mp (isConj_zcU hp2 hF hx).symm
  have hcoat : IsCoatom (Subgroup.centralizer ({x'} : Set (PSU3F p F))) := by
    rw [← hc, centralizer_conj, centralizer_zcU hp2 hF]
    exact ((MulEquiv.mapSubgroup (MulAut.conj c)).isCoatom_iff _).mpr
      (isCoatom_leviCU hp2 hp3 hF)
  refine ⟨fun htop => ?_, fun M hM => ?_⟩
  · have hz : embU ψ x' ∈ Subgroup.centralizer (L : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y _
      have hy : y ∈ Subgroup.centralizer ({embU ψ x'} : Set G) := htop ▸ Subgroup.mem_top y
      exact Subgroup.mem_centralizer_singleton_iff.mp hy
    rw [hAS.centralizer_eq, Subgroup.mem_bot] at hz
    rw [← orderOf_embU ψ, hz, orderOf_one] at hx
    omega
  · rcases eq_or_eq_of_isCoatom ψ hcoat (N := M ⊓ L)
      (by rw [← inf_centralizer_embU]; exact le_inf (inf_le_right.trans hM.le) inf_le_left)
      inf_le_right with h | h
    · exfalso
      apply not_le_of_gt hM
      intro m hm
      have hmLC : m ∈ L ⊔ Subgroup.centralizer ({embU ψ x'} : Set G) := hLC ▸ Subgroup.mem_top m
      obtain ⟨l, hl, d, hd, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hmLC
      have hlM : l ∈ M ⊓ L := ⟨by simpa using M.mul_mem hm (M.inv_mem (hM.le hd)), hl⟩
      rw [h, ← inf_centralizer_embU] at hlM
      exact Subgroup.mul_mem _ hlM.2 hd
    · have hLM : L ≤ M := fun y hy => by
        have hy' : y ∈ M ⊓ L := by rw [h]; exact hy
        exact hy'.1
      exact eq_top_iff.mpr (hLC ▸ sup_le hLM hM.le)

end CFSG.Quasithin.Vol2.Ch11.SecU1.U3
