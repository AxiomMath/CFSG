module

public import CFSG.SignalizerFunctorTheorem.McBride.Functor.Transfer
public import CFSG.SignalizerFunctorTheorem.McBride.Functor.Sections
public import CFSG.SignalizerFunctorTheorem.McBride.Functor.Class

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride

variable {G : Type*} [Group G] {p : ℕ} {A : Subgroup G} {θ : G → Subgroup G}
  {P : Subgroup G → Prop}

theorem isCompleteIn_of_image [Finite G] (hp : p.Prime) (hA : IsElemAbelian p A)
    (hθ : IsFunctor p A θ) {N : Subgroup G} [N.Normal] (hN : N ∈ signalizers p A θ P)
    {P' : Subgroup (G ⧸ N) → Prop}
    (hmap : ∀ X ∈ signalizers p A θ P, P' (X.map (QuotientGroup.mk' N)))
    (hext : ∀ X : Subgroup G, N ≤ X → A ≤ Subgroup.normalizer (X : Set G) →
      Nat.Coprime p (Nat.card X) → P' (X.map (QuotientGroup.mk' N)) → P X)
    (hbar : IsCompleteIn (signalizers p (A.map (QuotientGroup.mk' N))
      (imageFunctor (QuotientGroup.mk' N) A θ) P')) :
    IsCompleteIn (signalizers p A θ P) := by
  set π : G →* G ⧸ N := QuotientGroup.mk' N
  have hπker : π.ker = N := QuotientGroup.ker_mk' N
  have hf : Set.InjOn π A := injOn_of_coprime_ker hp hA (by rw [hπker]; exact hN.2.1)
  obtain ⟨Wb, hWb, hmax⟩ := hbar
  obtain ⟨hWbN, hWbp, hWbθ, hWbP⟩ := hWb
  have hsurj : Function.Surjective π := QuotientGroup.mk'_surjective N
  have hmapW : (Wb.comap π).map π = Wb := Subgroup.map_comap_eq_self_of_surjective hsurj Wb
  have hNW : N ≤ Wb.comap π := hπker.ge.trans (MonoidHom.ker_le_comap π Wb)
  have hAW : A ≤ Subgroup.normalizer ((Wb.comap π : Subgroup G) : Set G) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have h := Subgroup.mem_normalizer_iff.mp (hWbN (Subgroup.mem_map_of_mem π ha)) (π x)
    change π x ∈ Wb ↔ π (a * x * a⁻¹) ∈ Wb
    simpa only [map_mul, map_inv] using h
  have hcard : Nat.card (Wb.comap π) = Nat.card N * Nat.card Wb := by
    have h := Subgroup.card_ker_mul_card_range (π.domRestrict (Wb.comap π))
    rw [MonoidHom.ker_domRestrict, MonoidHom.domRestrict_range, hmapW] at h
    have hNcard : Nat.card π.ker = Nat.card N := by rw [hπker]
    rw [← h, ← hNcard]
    exact congrArg (· * Nat.card Wb)
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe (MonoidHom.ker_le_comap π Wb)).toEquiv)
  have hWp : Nat.Coprime p (Nat.card (Wb.comap π)) := by
    rw [hcard]
    exact hN.2.1.mul_right hWbp
  have hW : Wb.comap π ∈ signalizers p A θ P := by
    refine ⟨hAW, hWp, ?_, hext _ hNW hAW hWp (by rw [hmapW]; exact hWbP)⟩
    intro a ha ha1 x hx
    have hx1 : π x ∈ Wb := hx.1
    have hx2 : x ∈ Subgroup.centralizer {a} := hx.2
    have hπa1 : π a ≠ 1 := fun h => ha1 (hf ha A.one_mem (h.trans (map_one π).symm))
    have hπx : π x ∈ Subgroup.centralizer {π a} := by
      rw [Subgroup.mem_centralizer_singleton_iff] at hx2 ⊢
      simpa only [map_mul] using congrArg π hx2
    have h1 := hWbθ (π a) (Subgroup.mem_map_of_mem π ha) hπa1 ⟨hx1, hπx⟩
    rw [imageFunctor_apply hf ha] at h1
    obtain ⟨t, ht, hπt⟩ := h1
    have hn : t⁻¹ * x ∈ N := by
      rw [← hπker, MonoidHom.mem_ker, map_mul, map_inv, hπt, inv_mul_cancel]
    have hnc : t⁻¹ * x ∈ Subgroup.centralizer {a} :=
      mul_mem (inv_mem (hθ.le_centralizer a ha ha1 ht)) hx2
    have hnθ : t⁻¹ * x ∈ θ a := hN.2.2.1 a ha ha1 ⟨hn, hnc⟩
    simpa using mul_mem ht hnθ
  refine ⟨Wb.comap π, hW, fun X hX => ?_⟩
  have hX' := map_mem_signalizers_imageFunctor hp hA hf hX (hmap X hX)
  exact Subgroup.map_le_iff_le_comap.mp (hmax _ hX')

theorem coprime_and_fixed_le_of_map_le [Finite G] (hp : p.Prime) (hA : IsElemAbelian p A)
    {N : Subgroup G} [N.Normal] (hN : Nat.Coprime p (Nat.card N))
    {P' : Subgroup (G ⧸ N) → Prop} {Wb : Subgroup (G ⧸ N)}
    (hWb : Wb ∈ signalizers p (A.map (QuotientGroup.mk' N))
      (imageFunctor (QuotientGroup.mk' N) A θ) P')
    {Y : Subgroup G} (hAY : A ≤ Subgroup.normalizer (Y : Set G))
    (hY : Y.map (QuotientGroup.mk' N) ≤ Wb) :
    Nat.Coprime p (Nat.card Y) ∧
      ∀ a ∈ A, a ≠ 1 → Y ⊓ Subgroup.centralizer {a} ≤ θ a ⊔ N := by
  set π : G →* G ⧸ N := QuotientGroup.mk' N with hπ
  have hker : π.ker = N := QuotientGroup.ker_mk' N
  have hf : Set.InjOn π A := injOn_of_coprime_ker hp hA (by rw [hker]; exact hN)
  have hcop : Nat.Coprime p (Nat.card Y) := by
    have h := Subgroup.card_ker_mul_card_of_surjective (π.subgroupMap_surjective Y)
    rw [ker_subgroupMap_mk'] at h
    rw [← h]
    refine Nat.Coprime.mul_right ?_ ?_
    · have hcard : Nat.card (N.subgroupOf Y) = Nat.card (N ⊓ Y : Subgroup G) := by
        rw [← Subgroup.subgroupOf_map_subtype N Y,
          Subgroup.card_map_of_injective Y.subtype_injective]
      rw [hcard]
      exact hN.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left)
    · exact hWb.2.1.coprime_dvd_right (Subgroup.card_dvd_of_le hY)
  refine ⟨hcop, fun a ha ha1 => ?_⟩
  have hπa : π a ≠ 1 := fun h => ha1 (hf ha A.one_mem (by rw [h, map_one]))
  have himg := map_inf_centralizer_singleton hp hA π hAY hcop ha
  have hle : (Y ⊓ Subgroup.centralizer {a}).map π ≤ (θ a).map π := by
    rw [himg, ← imageFunctor_apply hf ha]
    exact (inf_le_inf_right _ hY).trans (hWb.2.2.1 (π a) (Subgroup.mem_map_of_mem π ha) hπa)
  calc Y ⊓ Subgroup.centralizer {a}
      ≤ ((Y ⊓ Subgroup.centralizer {a}).map π).comap π := Subgroup.le_comap_map _ _
    _ ≤ ((θ a).map π).comap π := Subgroup.comap_mono hle
    _ = θ a ⊔ N := by rw [Subgroup.comap_map_eq, hker]

theorem cl_imageFunctor_apply {Cl : SigClass.{u}} (hCl : IsSigClass p Cl) {G : Type u} [Group G]
    [Finite G] {A : Subgroup G} {θ : G → Subgroup G} (hp : p.Prime) (hA : IsElemAbelian p A)
    (hθ : IsFunctor p A θ) {N : Subgroup G} [N.Normal] (hN : Nat.Coprime p (Nat.card N))
    (hC : ∀ a ∈ A, a ≠ 1 → Cl G A (θ a)) {x : G ⧸ N} (hx : x ∈ A.map (QuotientGroup.mk' N))
    (hx1 : x ≠ 1) :
    Cl (G ⧸ N) (A.map (QuotientGroup.mk' N)) (imageFunctor (QuotientGroup.mk' N) A θ x) := by
  have hf : Set.InjOn (QuotientGroup.mk' N) A :=
    injOn_of_coprime_ker hp hA (by rw [QuotientGroup.ker_mk']; exact hN)
  obtain ⟨a, ha, rfl⟩ := hx
  have ha1 : a ≠ 1 := fun h => hx1 (by rw [h, map_one])
  rw [imageFunctor_apply hf ha]
  exact hCl.quotient G hA (hθ.normalized a ha ha1) (hθ.coprime a ha ha1) (hC a ha ha1)

theorem isCompleteIn_of_quotient {Cl : SigClass.{u}} (hCl : IsSigClass p Cl) {G : Type u}
    [Group G] [Finite G] {A : Subgroup G} {θ : G → Subgroup G} (hp : p.Prime)
    (hA : IsElemAbelian p A) (hθ : IsFunctor p A θ) {N : Subgroup G} [N.Normal]
    (hN : N ∈ signalizers p A θ (Cl G A))
    (hbar : IsCompleteIn (signalizers p (A.map (QuotientGroup.mk' N))
      (imageFunctor (QuotientGroup.mk' N) A θ) (Cl (G ⧸ N) (A.map (QuotientGroup.mk' N))))) :
    IsCompleteIn (signalizers p A θ (Cl G A)) := by
  refine isCompleteIn_of_image hp hA hθ hN (fun X hX => ?_) (fun X hNX hAX _ hXbar => ?_) hbar
  · exact hCl.quotient G hA hX.1 hX.2.1 hX.2.2.2
  · exact hCl.extension G hA hAX hNX hN.2.1 hN.2.2.2 hXbar

end CFSG.SignalizerFunctorTheorem.McBride
