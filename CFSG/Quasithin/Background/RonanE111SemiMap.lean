module

public import CFSG.Quasithin.Background.RonanE111Semi

public section

namespace CFSG.Quasithin.RonanE111

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b
open scoped commutatorElement

theorem SemisimpleMod.map_of_injective {Q G : Type} [Group Q] [Group G] (f : Q →* G)
    (hf : Function.Injective f) {T D Y : Subgroup Q} {𝒟 : Set (Subgroup Q)}
    (h : SemisimpleMod T D Y 𝒟) :
    SemisimpleMod (T.map f) (D.map f) (Y.map f) ((fun L : Subgroup Q => L.map f) '' 𝒟) := by
  have hle : ∀ {A B : Subgroup Q}, A.map f ≤ B.map f ↔ A ≤ B := fun {A B} =>
    Subgroup.map_le_map_iff_of_injective hf
  have hconj : ∀ (t : Q) (S : Subgroup Q), A1b.conjSub (f t) (S.map f) =
      (A1b.conjSub t S).map f := by
    intro t S
    unfold A1b.conjSub
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext x
    simp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨S, hS, rfl⟩
    exact Subgroup.map_mono (h.Y_le S hS)
  · rintro _ ⟨S, hS, rfl⟩
    exact Subgroup.map_mono (h.le_D S hS)
  · rintro _ ⟨S, hS, rfl⟩ N' hYN' hN'S hN'n
    have hN'S' : N' ≤ S.map f := hN'S
    set N : Subgroup Q := N'.comap f with hN
    have hNS : N ≤ S := by
      intro x hx
      obtain ⟨s, hs, hsx⟩ := hN'S' hx
      have : s = x := hf hsx
      rwa [this] at hs
    have hmapN : N.map f = N' := by
      refine le_antisymm (Subgroup.map_comap_le f N') (fun y hy => ?_)
      obtain ⟨s, hs, rfl⟩ := hN'S' hy
      exact ⟨s, hy, rfl⟩
    have hYN : Y ≤ N := by
      intro y hy
      exact hYN' ⟨y, hy, rfl⟩
    have hnorm : S.map f ≤ Subgroup.normalizer (N' : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hN'S').mp hN'n
    have hNn : (N.subgroupOf S).Normal := by
      refine normal_subgroupOf_of_conj hNS fun s hs n hn => ?_
      have h1 := (Subgroup.mem_normalizer_iff.mp (hnorm ⟨s, hs, rfl⟩) (f n)).mp hn
      show f (s * n * s⁻¹) ∈ N'
      simpa using h1
    rcases h.simple S hS N hYN hNS hNn with e | e
    · left
      rw [← hmapN, e]
    · right
      rw [← hmapN, e]
  · rintro _ ⟨S, hS, rfl⟩ hc
    apply h.nonab S hS
    rw [← Subgroup.map_commutator] at hc
    exact hle.mp hc
  · rintro _ ⟨S, hS, rfl⟩ _ ⟨S', hS', rfl⟩ hne
    have hSS : S ≠ S' := fun e => hne (by rw [e])
    rw [← Subgroup.map_commutator]
    exact hle.mpr (h.comm S hS S' hS' hSS)
  · rw [← sSup_eq_iSup, sSup_image, ← h.gen, Subgroup.map_iSup]
    simp [sSup_eq_iSup, Subgroup.map_iSup]
  · rintro _ ⟨S, hS, rfl⟩ t' ht'
    obtain ⟨t, ht, rfl⟩ := ht'
    exact ⟨A1b.conjSub t S, h.conj S hS t ht, (hconj t S).symm⟩
  · rintro _ ⟨S, hS, rfl⟩ _ ⟨S', hS', rfl⟩
    obtain ⟨t, ht, hts⟩ := h.trans S hS S' hS'
    exact ⟨f t, ⟨t, ht, rfl⟩, by rw [hconj, hts]⟩

theorem SemisimpleMod.map_subtype {G : Type} [Group G] (U : Subgroup G) {T D Y : Subgroup ↥U}
    {𝒟 : Set (Subgroup ↥U)} (h : SemisimpleMod T D Y 𝒟) :
    SemisimpleMod (T.map U.subtype) (D.map U.subtype) (Y.map U.subtype)
      ((fun L : Subgroup ↥U => L.map U.subtype) '' 𝒟) :=
  SemisimpleMod.map_of_injective U.subtype U.subtype_injective h

end CFSG.Quasithin.RonanE111
