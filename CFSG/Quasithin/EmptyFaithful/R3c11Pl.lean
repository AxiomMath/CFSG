module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.A4Defs

public section

namespace CFSG.Quasithin.R3c11

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

section Planes

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem exists_mul_of_mem_sup_of_comm {A B : Subgroup G} (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    {x : G} (hx : x ∈ A ⊔ B) : ∃ a ∈ A, ∃ b ∈ B, a * b = x := by
  let P : Subgroup G :=
    { carrier := {x | ∃ a ∈ A, ∃ b ∈ B, a * b = x}
      one_mem' := ⟨1, A.one_mem, 1, B.one_mem, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨a₁, ha₁, b₁, hb₁, rfl⟩ ⟨a₂, ha₂, b₂, hb₂, rfl⟩
        refine ⟨a₁ * a₂, A.mul_mem ha₁ ha₂, b₁ * b₂, B.mul_mem hb₁ hb₂, ?_⟩
        calc a₁ * a₂ * (b₁ * b₂) = a₁ * (a₂ * b₁) * b₂ := by group
          _ = a₁ * (b₁ * a₂) * b₂ := by rw [hc a₂ ha₂ b₁ hb₁]
          _ = a₁ * b₁ * (a₂ * b₂) := by group
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨a⁻¹, A.inv_mem ha, b⁻¹, B.inv_mem hb, ?_⟩
        calc a⁻¹ * b⁻¹ = (b * a)⁻¹ := by group
          _ = (a * b)⁻¹ := by rw [hc a ha b hb] }
  have hAP : A ≤ P := fun a ha => ⟨a, ha, 1, B.one_mem, by simp⟩
  have hBP : B ≤ P := fun b hb => ⟨1, A.one_mem, b, hb, by simp⟩
  exact (sup_le hAP hBP) hx

theorem plane_eq {V₁ V₂ E : Subgroup G} {y : G}
    (hc : ∀ a ∈ V₁, ∀ b ∈ V₂, a * b = b * a)
    (hV₁ : Nat.card V₁ = 4) (hV₂ : Nat.card V₂ = 4) (hE : Nat.card E = 4)
    (hEle : E ≤ V₁ ⊔ V₂) (hyE : ∀ e ∈ E, y * e * y⁻¹ ∈ E)
    (hyV₂ : ∀ u ∈ V₂, y * u * y⁻¹ ∈ V₂) (hy1 : ∀ a ∈ V₁, y * a = a * y)
    (hfpf : ∀ u ∈ V₂, u ≠ 1 → y * u * y⁻¹ ≠ u) :
    E = V₁ ∨ E = V₂ := by
  classical
  by_cases hA : ∃ u ∈ E, u ∈ V₂ ∧ u ≠ 1
  · right
    obtain ⟨u, huE, huV, hu1⟩ := hA
    set K : Subgroup G := E ⊓ V₂ with hK
    have hKV : K ≤ V₂ := inf_le_right
    have huK : u ∈ K := ⟨huE, huV⟩
    have hyuK : y * u * y⁻¹ ∈ K := ⟨hyE u huE, hyV₂ u huV⟩
    have hne : y * u * y⁻¹ ≠ u := hfpf u huV hu1
    have h3 : 3 ≤ Nat.card K := by
      have hs : ({1, u, y * u * y⁻¹} : Set G).ncard = 3 :=
        Set.ncard_eq_three.mpr ⟨1, u, y * u * y⁻¹, hu1.symm, fun h => hu1 (by simpa using h.symm),
          fun h => hne h.symm, rfl⟩
      have hsub : ({1, u, y * u * y⁻¹} : Set G) ⊆ (K : Set G) := by
        intro x hx
        rcases hx with rfl | rfl | rfl
        · exact K.one_mem
        · exact huK
        · exact hyuK
      calc 3 = ({1, u, y * u * y⁻¹} : Set G).ncard := hs.symm
        _ ≤ (K : Set G).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
        _ = Nat.card K := Nat.card_coe_set_eq _
    have hKdvd : Nat.card K ∣ 4 := by
      have := Subgroup.card_dvd_of_le hKV
      rwa [hV₂] at this
    have hK4 : Nat.card K = 4 := by
      have hle := Nat.le_of_dvd (by norm_num) hKdvd
      have : Nat.card K = 3 ∨ Nat.card K = 4 := by omega
      rcases this with h | h
      · rw [h] at hKdvd
        omega
      · exact h
    have hKeq : K = V₂ := Subgroup.eq_of_le_of_card_ge hKV (by rw [hK4, hV₂])
    have hV₂E : V₂ ≤ E := by
      rw [← hKeq]
      exact inf_le_left
    exact (Subgroup.eq_of_le_of_card_ge hV₂E (by rw [hE, hV₂])).symm
  · left
    push Not at hA
    have hEV1 : E ≤ V₁ := by
      intro e he
      obtain ⟨a, ha, b, hb, hab⟩ := exists_mul_of_mem_sup_of_comm hc (hEle he)
      have h1 : y * e * y⁻¹ * e⁻¹ = (y * b * y⁻¹) * b⁻¹ := by
        rw [← hab]
        have hya : y * a * y⁻¹ = a := by
          have := hy1 a ha
          rw [this]
          group
        calc y * (a * b) * y⁻¹ * (a * b)⁻¹ = (y * a * y⁻¹) * (y * b * y⁻¹) * (b⁻¹ * a⁻¹) := by group
          _ = a * (y * b * y⁻¹) * (b⁻¹ * a⁻¹) := by rw [hya]
          _ = (y * b * y⁻¹) * b⁻¹ := by
            have hcomm : ∀ x ∈ V₂, a * x = x * a := fun x hx => hc a ha x hx
            have hyb : y * b * y⁻¹ ∈ V₂ := hyV₂ b hb
            have e1 : a * (y * b * y⁻¹) = (y * b * y⁻¹) * a := hcomm _ hyb
            calc a * (y * b * y⁻¹) * (b⁻¹ * a⁻¹) = ((y * b * y⁻¹) * a) * (b⁻¹ * a⁻¹) := by rw [e1]
              _ = (y * b * y⁻¹) * (a * b⁻¹ * a⁻¹) := by group
              _ = (y * b * y⁻¹) * b⁻¹ := by rw [hcomm b⁻¹ (V₂.inv_mem hb)]; group
      have hmemE : y * e * y⁻¹ * e⁻¹ ∈ E := E.mul_mem (hyE e he) (E.inv_mem he)
      have hmemV : (y * b * y⁻¹) * b⁻¹ ∈ V₂ := V₂.mul_mem (hyV₂ b hb) (V₂.inv_mem hb)
      rw [h1] at hmemE
      have h2 : (y * b * y⁻¹) * b⁻¹ = 1 := hA _ hmemE hmemV
      have hb1 : b = 1 := by
        by_contra hb1
        apply hfpf b hb hb1
        have := mul_inv_eq_one.mp h2
        exact this
      rw [← hab, hb1, mul_one]
      exact ha
    exact Subgroup.eq_of_le_of_card_ge hEV1 (by rw [hE, hV₁])

theorem le_normalizer_of_swap {V₁ V₂ H S : Subgroup G} (hS : IsSylowTwoOf S H)
    (hSV : S ≤ Subgroup.normalizer (V₂ : Set G))
    (hH : ∀ h ∈ H, (∀ v ∈ V₂, h * v * h⁻¹ ∈ V₂) ∨
      ((∀ v ∈ V₂, h * v * h⁻¹ ∈ V₁) ∧ (∀ v ∈ V₁, h * v * h⁻¹ ∈ V₂))) :
    H ≤ Subgroup.normalizer (V₂ : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hcon
  obtain ⟨m, hmH, hmN⟩ := Set.not_subset.mp fun h => hcon h
  have hmV : ¬ ∀ v ∈ V₂, m * v * m⁻¹ ∈ V₂ := fun h => hmN (A4.mem_normalizer_of_conj_mem h)
  have hm : (∀ v ∈ V₂, m * v * m⁻¹ ∈ V₁) ∧ (∀ v ∈ V₁, m * v * m⁻¹ ∈ V₂) :=
    (hH m hmH).resolve_left hmV
  set N : Subgroup G := H ⊓ Subgroup.normalizer (V₂ : Set G) with hN
  set N' : Subgroup ↥H := N.subgroupOf H with hN'
  have hmemN' : ∀ x : ↥H, x ∈ N' ↔ (x : G) ∈ Subgroup.normalizer (V₂ : Set G) := fun x => by
    rw [hN', Subgroup.mem_subgroupOf]
    exact ⟨fun h => h.2, fun h => ⟨x.2, h⟩⟩
  have hidx : N'.index = 2 := by
    rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨m, hmH⟩, fun x => ?_⟩
    by_cases hx : (x : G) ∈ Subgroup.normalizer (V₂ : Set G)
    · have hxN : x ∈ N' := (hmemN' x).mpr hx
      have hxm : x * ⟨m, hmH⟩ ∉ N' := by
        intro h
        apply hmN
        have h1 := (hmemN' _).mp h
        have : m = (x : G)⁻¹ * ((x : G) * m) := by group
        rw [this]
        exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hx) h1
      exact Or.inr ⟨hxN, hxm⟩
    · have hxV : ¬ ∀ v ∈ V₂, (x : G) * v * (x : G)⁻¹ ∈ V₂ := fun h => hx (A4.mem_normalizer_of_conj_mem h)
      have hxs := (hH x x.2).resolve_left hxV
      have hxm : x * ⟨m, hmH⟩ ∈ N' := by
        rw [hmemN']
        refine A4.mem_normalizer_of_conj_mem fun v hv => ?_
        have h1 := hm.1 v hv
        have h2 := hxs.2 _ h1
        simpa [mul_assoc] using h2
      exact Or.inl ⟨hxm, hx ∘ ((hmemN' x).mp)⟩
  let Sy : Sylow 2 ↥H := A4.toSylow hS
  have hSy : (Sy : Subgroup ↥H) = S.subgroupOf H := A4.toSylow_coe hS
  have hSN' : (Sy : Subgroup ↥H) ≤ N' := by
    rw [hSy]
    intro x hx
    rw [hmemN']
    exact hSV (Subgroup.mem_subgroupOf.mp hx)
  have h1 := Subgroup.relIndex_mul_index hSN'
  have h2 : 2 ∣ (Sy : Subgroup ↥H).index := by
    rw [← h1, hidx]
    exact Dvd.intro_left _ rfl
  exact Sy.not_dvd_index h2

end Planes

end CFSG.Quasithin.R3c11
