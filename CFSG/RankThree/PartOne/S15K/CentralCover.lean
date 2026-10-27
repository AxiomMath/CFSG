module

public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeGroup

public section

namespace CFSG.RankThree.PartOne.S15K

open scoped commutatorElement
open CFSG.RankThree.PartOne.KCUnitary

section Cover

variable {H C : Type*} [Group H] [Group C]

theorem eq_of_perfect_of_map_eq {Q : Type*} [Group Q] (Φ : H →* C) (hker : Φ.ker ≤ Subgroup.center H)
    (hQ : Group.IsPerfect Q) (τ₁ τ₂ : Q →* H) (h : ∀ u, Φ (τ₁ u) = Φ (τ₂ u)) :
    ∀ u, τ₁ u = τ₂ u := by
  have hmem : ∀ u, (τ₁ u)⁻¹ * τ₂ u ∈ Φ.ker := fun u => by
    rw [MonoidHom.mem_ker, map_mul, map_inv, h u, inv_mul_cancel]
  have hc : ∀ u (g : H), g * ((τ₁ u)⁻¹ * τ₂ u) = ((τ₁ u)⁻¹ * τ₂ u) * g := fun u g =>
    Subgroup.mem_center_iff.mp (hker (hmem u)) g
  let δ : Q →* Φ.ker :=
    { toFun := fun u => ⟨(τ₁ u)⁻¹ * τ₂ u, hmem u⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun u v => Subtype.ext (by
        change (τ₁ (u * v))⁻¹ * τ₂ (u * v) = ((τ₁ u)⁻¹ * τ₂ u) * ((τ₁ v)⁻¹ * τ₂ v)
        rw [map_mul, map_mul, mul_inv_rev]
        calc (τ₁ v)⁻¹ * (τ₁ u)⁻¹ * (τ₂ u * τ₂ v)
            = (τ₁ v)⁻¹ * ((τ₁ u)⁻¹ * τ₂ u) * τ₂ v := by group
          _ = ((τ₁ u)⁻¹ * τ₂ u) * (τ₁ v)⁻¹ * τ₂ v := by rw [hc u ((τ₁ v)⁻¹)]
          _ = ((τ₁ u)⁻¹ * τ₂ u) * ((τ₁ v)⁻¹ * τ₂ v) := by group) }
  have hδ := eq_one_of_perfect_of_comm hQ
    (fun a b : Φ.ker => Subtype.ext (Subgroup.mem_center_iff.mp (hker b.2) a)) δ
  intro u
  have h1 := congrArg Subtype.val (hδ u)
  change (τ₁ u)⁻¹ * τ₂ u = 1 at h1
  exact inv_mul_eq_one.mp h1


theorem commutator_mul_central_left {z : H} (hz : z ∈ Subgroup.center H) (g h : H) :
    ⁅g * z, h⁆ = ⁅g, h⁆ := by
  have hzh : z * h = h * z := (Subgroup.mem_center_iff.mp hz h).symm
  have h1 : z * h * z⁻¹ = h := by rw [hzh, mul_inv_cancel_right]
  calc ⁅g * z, h⁆ = g * (z * h * z⁻¹) * g⁻¹ * h⁻¹ := by simp only [commutatorElement_def]; group
    _ = ⁅g, h⁆ := by rw [h1]; rfl

theorem commutator_mul_central_right {z : H} (hz : z ∈ Subgroup.center H) (g h : H) :
    ⁅g, h * z⁆ = ⁅g, h⁆ := by
  have hzg : z * g⁻¹ = g⁻¹ * z := (Subgroup.mem_center_iff.mp hz g⁻¹).symm
  have h1 : z * g⁻¹ * z⁻¹ = g⁻¹ := by rw [hzg, mul_inv_cancel_right]
  calc ⁅g, h * z⁆ = g * h * (z * g⁻¹ * z⁻¹) * h⁻¹ := by simp only [commutatorElement_def]; group
    _ = ⁅g, h⁆ := by rw [h1]; rfl

variable {Φ : H →* C}

theorem map_commutator_comap (hΦ : Function.Surjective Φ) {F : Subgroup C} (hF : ⁅F, F⁆ = F) :
    (⁅F.comap Φ, F.comap Φ⁆).map Φ = F := by
  rw [Subgroup.map_commutator, Subgroup.map_comap_eq_self_of_surjective hΦ, hF]

theorem commutator_comap_perfect (hΦ : Function.Surjective Φ) (hker : Φ.ker ≤ Subgroup.center H)
    {F : Subgroup C} (hF : ⁅F, F⁆ = F) :
    ⁅⁅F.comap Φ, F.comap Φ⁆, ⁅F.comap Φ, F.comap Φ⁆⁆ = ⁅F.comap Φ, F.comap Φ⁆ := by
  set R : Subgroup H := F.comap Φ with hR
  set Q : Subgroup H := ⁅R, R⁆ with hQ
  have hmap : Q.map Φ = F := map_commutator_comap hΦ hF
  refine le_antisymm (KCUnitary.commutator_self_le Q) ?_
  refine Subgroup.commutator_le.mpr fun r₁ hr₁ r₂ hr₂ => ?_
  have hlift : ∀ r ∈ R, ∃ q ∈ Q, ∃ z ∈ Subgroup.center H, r = q * z := by
    intro r hr
    have hΦr : Φ r ∈ Q.map Φ := by rw [hmap]; exact hr
    obtain ⟨q, hq, hqr⟩ := Subgroup.mem_map.mp hΦr
    refine ⟨q, hq, q⁻¹ * r, hker ?_, by group⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, hqr, inv_mul_cancel]
  obtain ⟨q₁, hq₁, z₁, hz₁, rfl⟩ := hlift r₁ hr₁
  obtain ⟨q₂, hq₂, z₂, hz₂, rfl⟩ := hlift r₂ hr₂
  rw [commutator_mul_central_left hz₁, commutator_mul_central_right hz₂]
  exact Subgroup.commutator_mem_commutator hq₁ hq₂

theorem isQuasisimple_commutator_comap (hΦ : Function.Surjective Φ)
    (hker : Φ.ker ≤ Subgroup.center H) {F : Subgroup C} (hF : CFSG.IsQuasisimple ↥F) :
    CFSG.IsQuasisimple ↥⁅F.comap Φ, F.comap Φ⁆ := by
  have hFp : ⁅F, F⁆ = F := Subgroup.isPerfect_iff.1 hF.1
  set R : Subgroup H := F.comap Φ with hR
  set Q : Subgroup H := ⁅R, R⁆ with hQ
  have hmap : Q.map Φ = F := map_commutator_comap hΦ hFp
  have hQp : ⁅Q, Q⁆ = Q := commutator_comap_perfect hΦ hker hFp
  have hQperf : Group.IsPerfect ↥Q := Subgroup.isPerfect_iff.2 hQp
  have hQR : Q ≤ R := KCUnitary.commutator_self_le R
  let Ψ : ↥Q →* ↥F :=
    ((Φ.comp Q.subtype).codRestrict F fun q => hQR q.2)
  have hΨ : Function.Surjective Ψ := by
    intro f
    have : (f : C) ∈ Q.map Φ := by rw [hmap]; exact f.2
    obtain ⟨q, hq, hqf⟩ := Subgroup.mem_map.mp this
    exact ⟨⟨q, hq⟩, Subtype.ext hqf⟩
  let f' : ↥Q →* ↥F ⧸ Subgroup.center ↥F := (QuotientGroup.mk' _).comp Ψ
  have hf' : Function.Surjective f' :=
    (QuotientGroup.mk'_surjective _).comp hΨ
  have hcen : f'.ker = Subgroup.center ↥Q := by
    apply le_antisymm
    · intro q hq
      have hqF : Ψ q ∈ Subgroup.center ↥F := (QuotientGroup.eq_one_iff _).mp hq
      rw [Subgroup.mem_center_iff]
      intro g
      have hcomm := KCUnitary.commutator_eq_one_of_central (F := Q) (Z := Φ.ker) (q : H) hQperf
        (fun z hz g' => (Subgroup.mem_center_iff.mp (hker hz) g').symm)
        (fun g' hg' => by
          rw [MonoidHom.mem_ker, map_commutatorElement]
          have hg'F : Φ g' ∈ F := by rw [← hmap]; exact Subgroup.mem_map_of_mem Φ hg'
          have h1 := Subgroup.mem_center_iff.mp hqF ⟨Φ g', hg'F⟩
          have h2 : Φ g' * Φ (q : H) = Φ (q : H) * Φ g' := congrArg Subtype.val h1
          exact commutatorElement_eq_one_iff_commute.mpr h2.symm)
        (g : H) g.2
      exact Subtype.ext ((commutatorElement_eq_one_iff_commute.mp hcomm).symm.eq)
    · intro z hz
      rw [MonoidHom.mem_ker]
      refine (QuotientGroup.eq_one_iff _).mpr ?_
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨g', rfl⟩ := hΨ g
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz g']
  let e : ↥Q ⧸ Subgroup.center ↥Q ≃* ↥F ⧸ Subgroup.center ↥F :=
    (QuotientGroup.quotientMulEquivOfEq hcen.symm).trans (QuotientGroup.quotientKerEquivOfSurjective f' hf')
  have hsimple : IsSimpleGroup (↥Q ⧸ Subgroup.center ↥Q) :=
    (MulEquiv.isSimpleGroup_congr e).mpr hF.2.1
  exact KCUnitary.isQuasisimple_of_perfect_of_simple hQperf hsimple


theorem isSubnormal_commutator_comap {F : Subgroup C} (hF : F.IsSubnormal) :
    (⁅F.comap Φ, F.comap Φ⁆).IsSubnormal := by
  set R : Subgroup H := F.comap Φ with hR
  have hRs : R.IsSubnormal := hF.comap Φ
  have hn : (⁅R, R⁆.subgroupOf R).Normal :=
    ⟨fun n hn g => KCUnitary.conj_mem_commutator_self g.2 hn⟩
  exact Subgroup.IsSubnormal.trans (KCUnitary.commutator_self_le R) hn.isSubnormal hRs

theorem le_iSup_of_isPerfect_of_map_le {ι : Type*} (hker : Φ.ker ≤ Subgroup.center H)
    {Q : ι → Subgroup H} {F : ι → Subgroup C} (hQF : ∀ i, (Q i).map Φ = F i) {Y : Subgroup H}
    (hY : ⁅Y, Y⁆ = Y) (hle : Y.map Φ ≤ ⨆ i, F i) : Y ≤ ⨆ i, Q i := by
  set N : Subgroup H := ⨆ i, Q i with hN
  have hmapN : N.map Φ = ⨆ i, F i := by
    rw [hN, Subgroup.map_iSup]
    exact iSup_congr hQF
  have hy : ∀ y ∈ Y, ∃ n ∈ N, ∃ z ∈ Subgroup.center H, y = n * z := by
    intro y hy
    have : Φ y ∈ N.map Φ := by rw [hmapN]; exact hle (Subgroup.mem_map_of_mem Φ hy)
    obtain ⟨n, hn, hny⟩ := Subgroup.mem_map.mp this
    refine ⟨n, hn, n⁻¹ * y, hker ?_, by group⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, hny, inv_mul_cancel]
  calc Y = ⁅Y, Y⁆ := hY.symm
    _ ≤ N := by
      refine Subgroup.commutator_le.mpr fun y₁ h₁ y₂ h₂ => ?_
      obtain ⟨n₁, hn₁, z₁, hz₁, rfl⟩ := hy y₁ h₁
      obtain ⟨n₂, hn₂, z₂, hz₂, rfl⟩ := hy y₂ h₂
      rw [commutator_mul_central_left hz₁, commutator_mul_central_right hz₂]
      exact KCUnitary.commutator_self_le N (Subgroup.commutator_mem_commutator hn₁ hn₂)

theorem exists_inner_of_map_eq_conj (hker : Φ.ker ≤ Subgroup.center H) {Q : Subgroup H}
    {F : Subgroup C} (hQ : ⁅Q, Q⁆ = Q) (hQF : Q.map Φ = F) (τ : H →* H) {x : C} (hx : x ∈ F)
    (h : ∀ y ∈ Q, Φ (τ y) = x * Φ y * x⁻¹) : ∃ x' ∈ Q, ∀ y ∈ Q, τ y = x' * y * x'⁻¹ := by
  have hxQ : x ∈ Q.map Φ := hQF ▸ hx
  obtain ⟨x', hx'Q, hx'⟩ := Subgroup.mem_map.mp hxQ
  refine ⟨x', hx'Q, fun y hy => ?_⟩
  have hperf : Group.IsPerfect ↥Q := Subgroup.isPerfect_iff.2 hQ
  have key := eq_of_perfect_of_map_eq Φ hker hperf (τ.comp Q.subtype)
    ((MulAut.conj x').toMonoidHom.comp Q.subtype) (fun u => by
      have h1 : Φ (τ (u : H)) = x * Φ (u : H) * x⁻¹ := h u u.2
      have h2 : Φ (x' * (u : H) * x'⁻¹) = x * Φ (u : H) * x⁻¹ := by
        rw [map_mul, map_mul, map_inv, hx']
      show Φ (τ (u : H)) = Φ (x' * (u : H) * x'⁻¹)
      rw [h1, h2])
  exact key ⟨y, hy⟩

end Cover

end CFSG.RankThree.PartOne.S15K
