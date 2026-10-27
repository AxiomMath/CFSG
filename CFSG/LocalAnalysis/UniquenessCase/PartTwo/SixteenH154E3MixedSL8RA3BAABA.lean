module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL8RA3BAABAA

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Subgroup

theorem s16h_frattini_lift_noncyclic_pgroup
    {Γ Q : Type} [Group Γ] [Finite Γ] [Group Q] [Finite Q] (φ : Γ →* Q)
    {M T : Subgroup Γ} (hTM : T ≤ M) (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M)
    {B E : Subgroup Q} (hB : B ≤ T.map φ) (hE : E ≤ M.map φ)
    (hEB : E ≤ Subgroup.normalizer (B : Set Q)) {p : ℕ} [hp : Fact p.Prime]
    (hEp : IsPGroup p E) (hEc : ¬ IsCyclic ↥E) :
    ∃ P : Subgroup Γ, P ≤ M ⊓ Subgroup.normalizer ((T ⊓ B.comap φ : Subgroup Γ) : Set Γ) ∧
      IsPGroup p P ∧ ¬ IsCyclic ↥P := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let R : Subgroup Γ := T ⊓ B.comap φ
  let H : Subgroup Γ := M ⊓ B.comap φ
  let X : Subgroup Γ := M ⊓ (Subgroup.normalizer (B : Set Q)).comap φ
  have hR_sylow : CFSG.ABGLocalTools.IsSylowOf 2 R H :=
    s16h_isSylowOf_inf_comap_of_map_eq φ hT hB
  have hHX : H ≤ X := by
    rintro y ⟨hyM, hyB⟩
    exact ⟨hyM, Subgroup.le_normalizer hyB⟩
  have hHnorm : X ≤ Subgroup.normalizer (H : Set Γ) := by
    intro x hx
    obtain ⟨hxM, hxN⟩ := hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨hyM, hyB⟩
      refine ⟨M.mul_mem (M.mul_mem hxM hyM) (M.inv_mem hxM), ?_⟩
      have h := (Subgroup.mem_normalizer_iff.mp hxN (φ y)).mp hyB
      simpa [map_mul] using h
    · rintro hxy
      obtain ⟨hxyM, hxyB⟩ := hxy
      have hyM : y ∈ M := by
        have h1 : x⁻¹ * (x * y * x⁻¹) * x ∈ M :=
          M.mul_mem (M.mul_mem (M.inv_mem hxM) hxyM) hxM
        convert h1 using 1
        group
      refine ⟨hyM, ?_⟩
      have hmem : φ x * φ y * (φ x)⁻¹ ∈ B := by simpa [map_mul] using hxyB
      exact (Subgroup.mem_normalizer_iff.mp hxN (φ y)).mpr hmem
  have hmapR : R.map φ = B := by
    apply le_antisymm
    · rintro _ ⟨r, hr, rfl⟩
      exact hr.2
    · intro b hb
      obtain ⟨t, htT, htφ⟩ := Subgroup.mem_map.mp (hB hb)
      exact Subgroup.mem_map.mpr
        ⟨t, ⟨htT, Subgroup.mem_comap.mpr (by rw [htφ]; exact hb)⟩, htφ⟩
  let N : Subgroup Γ := X ⊓ Subgroup.normalizer (R : Set Γ)
  have hlifting : ∀ e ∈ E, ∃ n ∈ N, φ n = e := by
    intro e he
    have heX : e ∈ X.map φ := by
      obtain ⟨m, hmM, hmφ⟩ := Subgroup.mem_map.mp (hE he)
      exact Subgroup.mem_map.mpr
        ⟨m, ⟨hmM, Subgroup.mem_comap.mpr (by rw [hmφ]; exact hEB he)⟩, hmφ⟩
    obtain ⟨x, hxX, hxφ⟩ := Subgroup.mem_map.mp heX
    obtain ⟨h, hhH, n, hnN, hhn⟩ :=
      s16h_exists_mul_mem_of_isSylowOf hHX hHnorm hR_sylow x hxX
    obtain ⟨r, hrR, hrφ⟩ := Subgroup.mem_map.mp (by
      show φ h ∈ R.map φ
      rw [hmapR]
      exact hhH.2)
    have hrX : r ∈ X :=
      ⟨hTM hrR.1, Subgroup.mem_comap.mpr (by rw [hrφ]; exact Subgroup.le_normalizer hhH.2)⟩
    have hnX : n ∈ X := by
      have : n = h⁻¹ * x := by rw [← hhn]; group
      rw [this]
      exact X.mul_mem (X.inv_mem (hHX hhH)) hxX
    exact ⟨r * n,
      ⟨X.mul_mem hrX hnX, (Subgroup.normalizer (R : Set Γ)).mul_mem
        (Subgroup.le_normalizer hrR) hnN⟩, by rw [map_mul, hrφ, ← map_mul, hhn, hxφ]⟩
  let P₀ : Subgroup Γ := N ⊓ E.comap φ
  have hφP₀ : P₀.map φ = E := by
    apply le_antisymm
    · rintro _ ⟨p, hp, rfl⟩
      exact hp.2
    · intro e he
      obtain ⟨n, hnN, hnφ⟩ := hlifting e he
      exact Subgroup.mem_map.mpr
        ⟨n, ⟨hnN, Subgroup.mem_comap.mpr (by rw [hnφ]; exact he)⟩, hnφ⟩
  obtain ⟨P, hP⟩ := CFSG.ABGLocalTools.exists_isSylowOf p P₀
  have hPmap : P.map φ = E := by
    obtain ⟨Q₀, hQ⟩ := hP.exists_sylow_eq_subgroupOf
    let f' : ↥P₀ →* ↥E :=
      (φ.comp P₀.subtype).codRestrict E (fun x => x.2.2)
    have hf' : Function.Surjective f' := by
      intro e
      obtain ⟨p, hp, hpe⟩ := Subgroup.mem_map.mp (by
        show (e : Q) ∈ P₀.map φ
        rw [hφP₀]
        exact e.2)
      exact ⟨⟨p, hp⟩, Subtype.ext hpe⟩
    have hEq : (Q₀.mapSurjective hf' : Subgroup ↥E) = ⊤ :=
      eq_top_iff.mpr (IsPGroup.le_sylow_of_normal (hEp.to_subgroup ⊤)
        (Q₀.mapSurjective hf'))
    have hcoe : (Q₀.mapSurjective hf' : Subgroup ↥E) = (P.map φ).subgroupOf E := by
      rw [Sylow.coe_mapSurjective, hQ]
      ext e
      rw [Subgroup.mem_subgroupOf]
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact Subgroup.mem_map.mpr
          ⟨x.val, Subgroup.mem_subgroupOf.mp hx, rfl⟩
      · intro he
        obtain ⟨p, hpP, hpe⟩ := Subgroup.mem_map.mp he
        refine ⟨⟨p, hP.le hpP⟩, Subgroup.mem_subgroupOf.mpr hpP, ?_⟩
        apply Subtype.ext
        exact hpe
    have htop : (P.map φ).subgroupOf E = ⊤ := by rw [← hcoe, hEq]
    refine le_antisymm (Subgroup.map_le_iff_le_comap.mpr (hP.le.trans inf_le_right)) ?_
    intro e he
    have : (⟨e, he⟩ : ↥E) ∈ (P.map φ).subgroupOf E := by
      rw [htop]
      exact Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp this
  refine ⟨P, ?_, hP.isPGroup, ?_⟩
  · intro p hp
    have hpN : p ∈ N := (hP.le hp).1
    exact ⟨hpN.1.1, hpN.2⟩
  · intro hPcyc
    apply hEc
    let fE : ↥P →* ↥E :=
      (φ.comp P.subtype).codRestrict E (fun p => hPmap.le (Subgroup.mem_map_of_mem φ p.2))
    have hfE : Function.Surjective fE := by
      intro e
      have he : (e : Q) ∈ P.map φ := hPmap.ge e.2
      obtain ⟨p, hp, hpe⟩ := Subgroup.mem_map.mp he
      exact ⟨⟨p, hp⟩, Subtype.ext hpe⟩
    exact isCyclic_of_surjective fE hfE

theorem s16h_frattini_lift_noncyclic_seven
    {Γ Q : Type} [Group Γ] [Finite Γ] [Group Q] [Finite Q] (φ : Γ →* Q)
    {M T : Subgroup Γ} (hTM : T ≤ M) (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M)
    {B E : Subgroup Q} (hB : B ≤ T.map φ) (hE : E ≤ M.map φ)
    (hEB : E ≤ Subgroup.normalizer (B : Set Q)) (hE7 : IsPGroup 7 E) (hEc : ¬ IsCyclic ↥E) :
    ∃ P : Subgroup Γ, P ≤ M ⊓ Subgroup.normalizer ((T ⊓ B.comap φ : Subgroup Γ) : Set Γ) ∧
      IsPGroup 7 P ∧ ¬ IsCyclic ↥P := by
  haveI : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  exact s16h_frattini_lift_noncyclic_pgroup φ hTM hT hB hE hEB hE7 hEc

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

end
