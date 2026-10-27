module

public import CFSG.GroupTheory.SteinbergBSQuotientLifting

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup

theorem uc22s218_exists_section_of_coprime_ker {R H : Type*} [Group R] [Group H] [Finite R]
    (ρ : R →* H) (hρ : Function.Surjective ρ)
    (hcop : Nat.Coprime (Nat.card ρ.ker) (Nat.card H)) :
    ∃ s : H →* R, ∀ x, ρ (s x) = x := by
  have hidx : ρ.ker.index = Nat.card H := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hρ, Subgroup.card_top]
  obtain ⟨C, hC⟩ :=
    Subgroup.exists_right_complement'_of_coprime (N := ρ.ker) (by rw [hidx]; exact hcop)
  let φ : C →* H := ρ.comp C.subtype
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro c hc
    exact Subtype.ext (Subgroup.disjoint_def.mp hC.disjoint hc c.2)
  have hsurj : Function.Surjective φ := by
    intro h
    obtain ⟨r, rfl⟩ := hρ h
    obtain ⟨⟨⟨n, hn⟩, c⟩, hnc⟩ := hC.2 r
    refine ⟨c, ?_⟩
    have hn1 : ρ n = 1 := hn
    have : r = n * (c : R) := hnc.symm
    change ρ (c : R) = ρ r
    rw [this, map_mul, hn1, one_mul]
  let e : C ≃* H := MulEquiv.ofBijective φ ⟨hinj, hsurj⟩
  refine ⟨C.subtype.comp e.symm.toMonoidHom, fun x => ?_⟩
  change φ (e.symm x) = x
  exact e.apply_symm_apply x

theorem uc22s218_exists_lift_hom_of_coprime {X : Type*} [Group X] [Finite X] (K : Subgroup X)
    [K.Normal] (C : Subgroup X) (hC : ∀ l : X, ∃ c ∈ C, c⁻¹ * l ∈ K) (P : Subgroup (X ⧸ K))
    (hcop : Nat.Coprime (Nat.card P) (Nat.card K)) :
    ∃ β : P →* X, (∀ a, β a ∈ C) ∧ ∀ a, QuotientGroup.mk' K (β a) = a := by
  let Pre : Subgroup X := C ⊓ P.comap (QuotientGroup.mk' K)
  let ρ : Pre →* P :=
    ((QuotientGroup.mk' K).comp Pre.subtype).codRestrict P (fun c => c.2.2)
  have hρ : Function.Surjective ρ := by
    intro a
    obtain ⟨l, hl⟩ := QuotientGroup.mk'_surjective K (a : X ⧸ K)
    obtain ⟨c, hcC, hcl⟩ := hC l
    have hπc : QuotientGroup.mk' K c = (a : X ⧸ K) := by
      rw [← hl]
      exact QuotientGroup.eq.2 hcl
    refine ⟨⟨c, hcC, ?_⟩, Subtype.ext hπc⟩
    show QuotientGroup.mk' K c ∈ P
    rw [hπc]
    exact a.2
  have hker : Nat.card ρ.ker ∣ Nat.card K := by
    have h1 : ρ.ker.map Pre.subtype ≤ K := by
      rintro _ ⟨c, hc, rfl⟩
      have h2 : QuotientGroup.mk' K (c : X) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 hc)
      exact (QuotientGroup.eq_one_iff (c : X)).1 h2
    rw [← Subgroup.card_map_of_injective Pre.subtype_injective]
    exact Subgroup.card_dvd_of_le h1
  obtain ⟨s, hs⟩ := uc22s218_exists_section_of_coprime_ker ρ hρ
    (Nat.Coprime.coprime_dvd_left hker hcop.symm)
  refine ⟨Pre.subtype.comp s, fun a => (s a).2.1, fun a => ?_⟩
  have h := congrArg Subtype.val (hs a)
  exact h

theorem uc22s218_exists_mem_centralizer_of_comm_mod {G : Type*} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {N X L : Subgroup G} (hN : ¬ p ∣ Nat.card N) (hX : IsPGroup p X)
    (hXN : X ≤ normalizer (N : Set G)) (hLN : L ≤ normalizer (N : Set G)) (hNL : N ≤ L)
    (hXL : ∀ x ∈ X, ∀ l ∈ L, x * l * x⁻¹ * l⁻¹ ∈ N) {l : G} (hl : l ∈ L) :
    ∃ c ∈ L ⊓ centralizer (X : Set G), c⁻¹ * l ∈ N := by
  set W : Subgroup G := normalizer (N : Set G) with hW
  have hNW : N ≤ W := le_normalizer
  have : (N.subgroupOf W).Normal := Subgroup.normal_in_normalizer
  have hN' : ¬ p ∣ Nat.card (N.subgroupOf W) := by
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNW).toEquiv]
  have hX' : IsPGroup p (X.subgroupOf W) := hX.comap_subtype
  let l' : W := ⟨l, hLN hl⟩
  have hmem : QuotientGroup.mk' (N.subgroupOf W) l' ∈
      centralizer (((X.subgroupOf W).map (QuotientGroup.mk' (N.subgroupOf W)) :
        Subgroup (↥W ⧸ N.subgroupOf W)) : Set (↥W ⧸ N.subgroupOf W)) := by
    rw [mem_centralizer_iff]
    rintro _ ⟨x', hx', rfl⟩
    rw [← map_mul, ← map_mul]
    symm
    apply QuotientGroup.eq.2
    rw [Subgroup.mem_subgroupOf]
    have hx'' : (x' : G) ∈ X := hx'
    have h := hXL ((x' : G)⁻¹) (X.inv_mem hx'') (l⁻¹) (L.inv_mem hl)
    simpa [l', mul_assoc] using h
  rw [CFSG.GroupTheory.SteinbergBS.centralizer_map_mk'_eq hN' hX'] at hmem
  obtain ⟨c', hc', hπ⟩ := hmem
  have hcl : (c' : G)⁻¹ * l ∈ N := by
    have h := QuotientGroup.eq.1 hπ
    rw [Subgroup.mem_subgroupOf] at h
    simpa [l'] using h
  have hcL : (c' : G) ∈ L := by
    have h1 : (c' : G) = l * (l⁻¹ * (c' : G)) := by group
    have h2 : l⁻¹ * (c' : G) ∈ N := by
      have := N.inv_mem hcl
      simpa using this
    rw [h1]
    exact L.mul_mem hl (hNL h2)
  refine ⟨(c' : G), mem_inf.2 ⟨hcL, ?_⟩, hcl⟩
  rw [mem_centralizer_iff]
  intro x hx
  have h := hc' (⟨x, hXN hx⟩ : W) (show (⟨x, hXN hx⟩ : W) ∈ X.subgroupOf W from hx)
  exact congrArg Subtype.val h

end CFSG.LocalAnalysis.UniquenessCase.UC22
