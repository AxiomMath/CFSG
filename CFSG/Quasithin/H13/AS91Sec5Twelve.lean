module

public import CFSG.Quasithin.H13.AS91Sec7Inc
public import CFSG.Quasithin.H13.AS91Sec3TwelveDefs
public import CFSG.Quasithin.H13.AS91Sec3Delta

public section

namespace CFSG.Quasithin.H13.AS91

open Subgroup CFSG.Open MulAction CFSG.Quasithin.Asc94
open scoped Pointwise
open CFSG.ASVolI.ChH (IsTrio IsSextet M24g S24)

theorem ResM24.card_range_R {G : Type} [Group G] [Finite G] {z : G} {c : Loc49 G z}
    (ρ : ResM24 c) : Nat.card (ρ.φ.comp (c.R.subgroupOf c.G1).subtype).range = 64 := by
  have hRG1 : c.R ≤ c.G1 := c.R_le_K.trans c.K_le_G1
  have hEker : ∀ x : ↥c.G1, ρ.φ x = 1 ↔ (x : G) ∈ c.E := by
    intro x
    rw [← MonoidHom.mem_ker, ρ.ker_eq, Subgroup.mem_subgroupOf]
  have hinj : Function.Injective
      (c.G1.subtype.comp (c.R.subgroupOf c.G1).subtype : ↥(c.R.subgroupOf c.G1) →* G) :=
    Subtype.val_injective.comp Subtype.val_injective
  have hmapeq : (ρ.φ.comp (c.R.subgroupOf c.G1).subtype).ker.map
      (c.G1.subtype.comp (c.R.subgroupOf c.G1).subtype) = c.R ⊓ c.E := by
    ext y
    rw [Subgroup.mem_map, Subgroup.mem_inf]
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [MonoidHom.mem_ker] at hx
      exact ⟨Subgroup.mem_subgroupOf.mp x.2, (hEker x.1).mp hx⟩
    · rintro ⟨hyR, hyE⟩
      have hyG1 : y ∈ c.G1 := c.E_le_G1 hyE
      refine ⟨⟨⟨y, hyG1⟩, Subgroup.mem_subgroupOf.mpr hyR⟩, ?_, rfl⟩
      rw [MonoidHom.mem_ker]
      exact (hEker ⟨y, hyG1⟩).mpr hyE
  have hker : Nat.card (ρ.φ.comp (c.R.subgroupOf c.G1).subtype).ker = 2 ^ 9 :=
    calc Nat.card (ρ.φ.comp (c.R.subgroupOf c.G1).subtype).ker
        = Nat.card ((ρ.φ.comp (c.R.subgroupOf c.G1).subtype).ker.map
            (c.G1.subtype.comp (c.R.subgroupOf c.G1).subtype)) :=
          (Subgroup.card_map_of_injective hinj).symm
      _ = Nat.card ↥(c.R ⊓ c.E) := by rw [hmapeq]
      _ = 2 ^ 9 := c.card_R_inf_E
  have hR : Nat.card ↥(c.R.subgroupOf c.G1) = 2 ^ 15 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRG1).toEquiv, c.card_R]
  have key := Subgroup.card_ker_mul_card_range (ρ.φ.comp (c.R.subgroupOf c.G1).subtype)
  rw [hker, hR] at key
  exact Nat.eq_of_mul_eq_mul_left (by norm_num) (key.trans (by norm_num))

theorem ResM24.stmt3_12_at
    {G : Type} [Group G] [Finite G] {z : G} {c : Loc49 G z}
    (ρ : ResM24 c) (h : M24G.Stmt3_12M24) (k : G ⧸ c.G2) (hk : CInc c.G1 c.G2 c.x0 k)
    (hkl : ¬ ∃ p : G ⧸ c.G3, CInc c.G2 c.G3 c.l0 p ∧ CInc c.G2 c.G3 k p) :
    4 < Set.ncard ((fun r : G => r • k) '' (c.R : Set G)) := by
  have hRG2 : c.R ≤ c.G2 := c.R_le_K.trans c.K_le_G2
  obtain ⟨N, hN⟩ : ∃ N : Subgroup (Equiv.Perm (Fin 24)),
      N = (ρ.φ.comp (c.R.subgroupOf c.G1).subtype).range := ⟨_, rfl⟩
  have hmem : ∀ σ, σ ∈ N ↔ ∃ x : ↥c.G1, (x : G) ∈ c.R ∧ ρ.φ x = σ := by
    intro σ
    rw [hN, MonoidHom.mem_range]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x.1, Subgroup.mem_subgroupOf.mp x.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, Subgroup.mem_subgroupOf.mpr hx⟩, rfl⟩
  have hNle : N ≤ M24g := by
    intro σ hσ
    obtain ⟨x, -, rfl⟩ := (hmem σ).mp hσ
    exact ρ.φ_mem x
  have hNfix : ∀ σ ∈ N, σ • ρ.l₀ = ρ.l₀ := by
    intro σ hσ
    obtain ⟨x, hx, rfl⟩ := (hmem σ).mp hσ
    exact (ρ.stab₂ x).mp (hRG2 hx)
  have hNnorm : ∀ σ ∈ M24g, σ • ρ.l₀ = ρ.l₀ → ∀ n ∈ N, σ * n * σ⁻¹ ∈ N := by
    intro σ hσ hσl n hn
    obtain ⟨u, rfl⟩ := ρ.exists_φ_eq hσ
    obtain ⟨x, hx, rfl⟩ := (hmem n).mp hn
    rw [hmem]
    refine ⟨u * x * u⁻¹, ?_, ?_⟩
    · have hu2 : (u : G) ∈ c.G2 := (ρ.stab₂ u).mpr hσl
      simpa using c.R_conj_G2 hu2 hx
    · simp
  have hcardN : Nat.card N = 64 := by
    rw [hN]
    exact ResM24.card_range_R ρ
  have hpgroup : IsPGroup 2 N := IsPGroup.of_card (n := 6) (by norm_num [hcardN])
  have hl0 : CInc c.G1 c.G2 c.x0 c.l0 := cInc_mk c.G1 c.G2 1
  have hnc : ¬ M24G.Coplanar ρ.l₀ (ρ.trio k) := by
    rw [← ρ.trio_l0]
    exact fun hc => hkl ((ρ.coplanar_iff hl0 hk).mpr hc)
  have hnc' : ¬ (M24G.Delta ρ.l₀ (ρ.trio k) 0 ∨ M24G.Delta ρ.l₀ (ρ.trio k) 1 ∨
      M24G.Delta ρ.l₀ (ρ.trio k) 2) := fun hd =>
    hnc ((M24G.coplanar_iff_delta ρ.isTrio_l₀ (ρ.isTrio_trio hk)).mpr hd)
  have hD : M24G.Delta ρ.l₀ (ρ.trio k) 3 ∨ M24G.Delta ρ.l₀ (ρ.trio k) 4 := by
    have hcop : ∀ j : Fin 5, M24G.Delta ρ.l₀ (ρ.trio k) j → j = 3 ∨ j = 4 := by
      intro j
      fin_cases j
      · intro hj
        exact absurd (Or.inl hj) hnc'
      · intro hj
        exact absurd (Or.inr (Or.inl hj)) hnc'
      · intro hj
        exact absurd (Or.inr (Or.inr hj)) hnc'
      · intro _
        exact Or.inl rfl
      · intro _
        exact Or.inr rfl
    obtain ⟨i, hi, -⟩ := M24G.delta_existsUnique ρ.isTrio_l₀ (ρ.isTrio_trio hk)
    rcases hcop i hi with rfl | rfl
    · exact Or.inl hi
    · exact Or.inr hi
  have hm : ∀ s ∈ c.R, CInc c.G1 c.G2 c.x0 (s • k) := by
    intro s hs
    have hs1 : s ∈ stabilizer G c.x0 := by
      rw [c.stab_x0]
      exact c.R_le_K.trans c.K_le_G1 hs
    have h1 := (cInc_smul c.G1 c.G2 s c.x0 k).mpr hk
    rwa [mem_stabilizer_iff.mp hs1] at h1
  have hinj : Set.InjOn ρ.trio ((fun r : G => r • k) '' (c.R : Set G)) := by
    rintro _ ⟨r, hr, rfl⟩ _ ⟨r', hr', rfl⟩ htr
    exact ρ.trio_injOn (hm r hr) (hm r' hr') htr
  have himg : (fun σ : S24 => σ • ρ.trio k) '' (N : Set S24) =
      ρ.trio '' ((fun r : G => r • k) '' (c.R : Set G)) := by
    ext t
    constructor
    · rintro ⟨σ, hσ, rfl⟩
      obtain ⟨x, hx, rfl⟩ := (hmem σ).mp hσ
      exact ⟨(x : G) • k, ⟨(x : G), hx, rfl⟩, ρ.trio_smul_line x hk⟩
    · rintro ⟨y, ⟨r, hr, rfl⟩, rfl⟩
      have hr1 : r ∈ c.G1 := c.K_le_G1 (c.R_le_K hr)
      exact ⟨ρ.φ ⟨r, hr1⟩, (hmem (ρ.φ ⟨r, hr1⟩)).mpr ⟨⟨r, hr1⟩, hr, rfl⟩,
        (ρ.trio_smul_line ⟨r, hr1⟩ hk).symm⟩
  have key := h ρ.l₀ (ρ.trio k) N ρ.isTrio_l₀ (ρ.isTrio_trio hk) hD hNle hNfix hNnorm hpgroup
    hcardN
  rw [himg, hinj.ncard_image] at key
  exact key

theorem stmt3_12_of
    (hres : ∀ (G : Type) [Group G] [Finite G] (z : G) (_ : HypJ4 G z) (c : Loc49 G z),
      Nonempty (ResM24 c)) (h : M24G.Stmt3_12M24) : Stmt3_12 := by
  intro G _ _ z hJ c k hk hkl
  obtain ⟨ρ⟩ := hres G z hJ c
  exact ResM24.stmt3_12_at ρ h k hk hkl

end CFSG.Quasithin.H13.AS91
