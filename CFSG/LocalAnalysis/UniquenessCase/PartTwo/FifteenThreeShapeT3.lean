module

public import CFSG.Quasithin.Background.D2Basic
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin

section DirectSum

variable {V : Type*} [CommGroup V]

theorem fix_of_mem_sSup_diff {𝒲 : Set (Subgroup V)} (h𝒲 : sSupIndep 𝒲) {W : Subgroup V}
    (hW : W ∈ 𝒲) {k : MulAut V} (hkW : k ∈ stabSub W)
    (hperm : ∀ Z ∈ 𝒲, Z.map k.toMonoidHom ∈ 𝒲) (hfix : ∀ v : V, k v * v⁻¹ ∈ W)
    {u : V} (hu : u ∈ sSup (𝒲 \ {W})) : k u = u := by
  have hkU : (sSup (𝒲 \ {W})).map k.toMonoidHom ≤ sSup (𝒲 \ {W}) := by
    rw [(Subgroup.gc_map_comap _).l_sSup]
    refine iSup₂_le fun Z hZ => le_sSup ⟨hperm Z hZ.1, ?_⟩
    intro hZW
    apply hZ.2
    ext z
    constructor
    · intro hz
      exact (hkW z).1 (by rw [Set.mem_singleton_iff] at hZW; rw [← hZW]; exact ⟨z, hz, rfl⟩)
    · intro hz
      obtain ⟨z', hz', hkz⟩ : k z ∈ Z.map k.toMonoidHom := by
        rw [Set.mem_singleton_iff] at hZW
        rw [hZW]
        exact (hkW z).2 hz
      have : z' = z := k.injective hkz
      rw [← this]
      exact hz'
  have h1 : k u * u⁻¹ ∈ sSup (𝒲 \ {W}) :=
    Subgroup.mul_mem _ (hkU ⟨u, hu, rfl⟩) (Subgroup.inv_mem _ hu)
  have h2 : k u * u⁻¹ ∈ W ⊓ sSup (𝒲 \ {W}) := ⟨hfix u, h1⟩
  rw [(h𝒲 hW).eq_bot, Subgroup.mem_bot, mul_inv_eq_one] at h2
  exact h2

theorem commSub_top_eq_map_autSub {𝒲 : Set (Subgroup V)} (h𝒲 : sSupIndep 𝒲)
    (htop : sSup 𝒲 = ⊤) {W : Subgroup V} (hW : W ∈ 𝒲) {K : Subgroup (MulAut V)}
    (hKW : K ≤ stabSub W) (hperm : ∀ k ∈ K, ∀ Z ∈ 𝒲, Z.map k.toMonoidHom ∈ 𝒲)
    (hfix : ∀ k ∈ K, ∀ v : V, k v * v⁻¹ ∈ W) :
    commSub ⊤ K = (commSub ⊤ (autSub K W)).map W.subtype := by
  have hsup : W ⊔ sSup (𝒲 \ {W}) = ⊤ := by
    rw [← sSup_insert, Set.insert_diff_singleton, Set.insert_eq_of_mem hW, htop]
  apply le_antisymm
  · rw [commSub, Subgroup.closure_le]
    rintro _ ⟨k, hk, v, -, rfl⟩
    obtain ⟨w, hw, u, hu, hwu⟩ := Subgroup.mem_sup.1 (hsup ▸ Subgroup.mem_top v)
    have hku : k u = u := fix_of_mem_sSup_diff h𝒲 hW (hKW hk) (hperm k hk) (hfix k hk) hu
    have hkv : k v * v⁻¹ = k w * w⁻¹ := by
      rw [← hwu, map_mul, hku]
      group
    rw [hkv]
    refine Subgroup.mem_map.2 ⟨resHom W ⟨k, hKW hk⟩ ⟨w, hw⟩ * ⟨w, hw⟩⁻¹,
      Subgroup.subset_closure ⟨resHom W ⟨k, hKW hk⟩, mem_autSub.2 ⟨⟨k, hKW hk⟩, hk, rfl⟩,
        ⟨w, hw⟩, Subgroup.mem_top _, rfl⟩, rfl⟩
  · rw [Subgroup.map_le_iff_le_comap, commSub, Subgroup.closure_le]
    rintro _ ⟨φ, hφ, w, -, rfl⟩
    obtain ⟨g, hg, rfl⟩ := mem_autSub.1 hφ
    exact Subgroup.subset_closure ⟨g, hg, w, Subgroup.mem_top _, rfl⟩

end DirectSum

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
