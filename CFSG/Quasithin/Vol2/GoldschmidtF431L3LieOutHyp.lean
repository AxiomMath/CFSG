module

public import CFSG.Quasithin.Vol2.GoldschmidtF431L3LieOutAut
public import CFSG.Quasithin.Vol2.GoldschmidtF431L3LieOutAbs
public import CFSG.Quasithin.Vol2.GoldschmidtF431L3LieFrame

public section

namespace CFSG.Quasithin.H13.F431.L3.P3

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open CFSG.QuasithinUnique.Fin257
  CFSG.QuasithinUnique.Fin257.L3 CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour

variable {F : Type} [Field F] [CharP F 2]

theorem stab_of_stab_U [Finite F] {θ : MulAut (projectiveSL 3 F)}
    (hθ : θ ∈ semilinearAutGroup 3 F)
    (hU : ∀ p, p ∈ projUnitriangular 3 F ↔ θ p ∈ projUnitriangular 3 F) :
    (∀ p, p ∈ (V1 : Subgroup (projectiveSL 3 F)) ↔ θ p ∈ (V1 : Subgroup (projectiveSL 3 F))) ∧
      (∀ p, p ∈ (V2 : Subgroup (projectiveSL 3 F)) ↔
        θ p ∈ (V2 : Subgroup (projectiveSL 3 F))) := by
  set θm : projectiveSL 3 F →* projectiveSL 3 F := θ.toMonoidHom with hθm
  have hinj : Function.Injective θm := θ.injective
  have hUmap : (projUnitriangular 3 F).map θm = projUnitriangular 3 F := by
    ext x
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact (hU p).mp hp
    · intro hx
      refine ⟨θ⁻¹ x, ?_, by simp [hθm]⟩
      exact (hU (θ⁻¹ x)).mpr (by simpa using hx)
  have hF' := Frame.map θm hinj (frame_U (F := F))
  rw [hUmap] at hF'
  have hcard : Nat.card (V1 : Subgroup (projectiveSL 3 F)) =
      Nat.card (V2 : Subgroup (projectiveSL 3 F)) := (frame_U (F := F)).card_eq
  have hA : (V1 : Subgroup (projectiveSL 3 F)).map θm = V1 ∨
      (V1 : Subgroup (projectiveSL 3 F)).map θm = V2 :=
    (frame_U (F := F)).maxea _ hF'.Q₁_le hF'.Q₁_ea
      (le_of_eq (Subgroup.card_map_of_injective hinj).symm)
  have hB : (V2 : Subgroup (projectiveSL 3 F)).map θm = V1 ∨
      (V2 : Subgroup (projectiveSL 3 F)).map θm = V2 :=
    (frame_U (F := F)).maxea _ hF'.Q₂_le hF'.Q₂_ea
      (by rw [Subgroup.card_map_of_injective hinj, hcard])
  have hne : (V1 : Subgroup (projectiveSL 3 F)).map θm ≠
      (V2 : Subgroup (projectiveSL 3 F)).map θm :=
    fun h => (frame_U (F := F)).Q_ne (Subgroup.map_injective hinj h)
  have hA1 : (V1 : Subgroup (projectiveSL 3 F)).map θm = V1 := by
    rcases hA with h | h
    · exact h
    · exfalso
      rcases hB with h' | h'
      · refine not_forall_V2_mem_V1 hθ fun g hg => ?_
        have : θm g ∈ (V2 : Subgroup (projectiveSL 3 F)).map θm := ⟨g, hg, rfl⟩
        rw [h'] at this
        exact this
      · exact hne (h.trans h'.symm)
  have hB1 : (V2 : Subgroup (projectiveSL 3 F)).map θm = V2 := by
    rcases hB with h | h
    · exact absurd (hA1.trans h.symm) hne
    · exact h
  refine ⟨fun p => ⟨fun hp => ?_, fun hp => ?_⟩, fun p => ⟨fun hp => ?_, fun hp => ?_⟩⟩
  · have : θm p ∈ (V1 : Subgroup (projectiveSL 3 F)).map θm := ⟨p, hp, rfl⟩
    rwa [hA1] at this
  · rw [← hA1] at hp
    obtain ⟨p', hp', hpp⟩ := hp
    have : p' = p := hinj hpp
    rwa [this] at hp'
  · have : θm p ∈ (V2 : Subgroup (projectiveSL 3 F)).map θm := ⟨p, hp, rfl⟩
    rwa [hB1] at this
  · rw [← hB1] at hp
    obtain ⟨p', hp', hpp⟩ := hp
    have : p' = p := hinj hpp
    rwa [this] at hp'

section Action

variable [Finite F] {H : Type} [Group H]

theorem l3OutHyp_of_action {f : ℕ} (hf : 2 ≤ f) (hF : Nat.card F = 2 ^ f)
    (ρ : H →* MulAut (projectiveSL 3 F)) (hρ : Function.Injective ρ)
    (Φ : projectiveSL 3 F →* H) (hΦ : Function.Injective Φ)
    (hΦρ : ∀ (h : H) (p : projectiveSL 3 F), Φ (ρ h p) = h * Φ p * h⁻¹)
    (hE : ∀ h : H, ρ h ∈ semilinearAutGroup 3 F)
    {R₁ R₂ : Subgroup (projectiveSL 3 F)}
    (hR : (R₁ = V1 ∧ R₂ = V2) ∨ (R₁ = V2 ∧ R₂ = V1)) :
    L3OutHyp Φ (projUnitriangular 3 F) R₁ R₂ (Nat.card F) := by
  have hq : 4 ≤ Nat.card F := by
    rw [hF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hconj : ∀ (h : H) (X : Subgroup (projectiveSL 3 F)),
      h ∈ Subgroup.normalizer ((X.map Φ : Subgroup H) : Set H) ↔ ∀ p, p ∈ X ↔ ρ h p ∈ X := by
    intro h X
    rw [Subgroup.mem_normalizer_iff]
    constructor
    · intro hh p
      have := hh (Φ p)
      rw [Subgroup.mem_map_iff_mem hΦ, ← hΦρ, Subgroup.mem_map_iff_mem hΦ] at this
      exact this
    · intro hh y
      by_cases hy : y ∈ Φ.range
      · obtain ⟨p, rfl⟩ := hy
        rw [Subgroup.mem_map_iff_mem hΦ, ← hΦρ, Subgroup.mem_map_iff_mem hΦ]
        exact hh p
      · have h1 : y ∉ X.map Φ := fun hyX => hy (Subgroup.map_le_range Φ X hyX)
        have h2 : h * y * h⁻¹ ∉ X.map Φ := by
          intro hmem
          obtain ⟨q', -, hq'⟩ := hmem
          apply hy
          refine ⟨ρ h⁻¹ q', ?_⟩
          rw [hΦρ, hq']
          group
        exact ⟨fun hh' => absurd hh' h1, fun hh' => absurd hh' h2⟩
  have hρΦ : ∀ p, ρ (Φ p) = MulAut.conj p := by
    intro p
    ext g
    apply hΦ
    rw [hΦρ]
    simp [MulAut.conj_apply]
  have hinner : ∀ h : H, ρ h ∈ (MulAut.conj : projectiveSL 3 F →* MulAut (projectiveSL 3 F)).range →
      h ∈ Φ.range := by
    rintro h ⟨p, hp⟩
    refine ⟨p, hρ ?_⟩
    rw [hρΦ]
    exact hp
  have hfix : ∀ (h : H) (B : Subgroup H), B ≤ Φ.range → (∀ g ∈ B, h * g = g * h) →
      ∀ p ∈ B.comap Φ, ρ h p = p := by
    intro h B hB hc p hp
    apply hΦ
    rw [hΦρ]
    have := hc (Φ p) hp
    rw [this]
    group
  have hcardB : ∀ B : Subgroup H, B ≤ Φ.range → Nat.card (B.comap Φ) = Nat.card B := by
    intro B hB
    have h1 : (B.comap Φ).map Φ = B := by
      rw [Subgroup.map_comap_eq, inf_of_le_right hB]
    calc Nat.card (B.comap Φ) = Nat.card ((B.comap Φ).map Φ) :=
          (Subgroup.card_map_of_injective hΦ).symm
      _ = Nat.card B := by rw [h1]
  refine ⟨by omega, ?_, ?_, ?_, ?_, ?_⟩
  · rw [centerOf_U, card_Wg]
  · rcases hR with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact card_V1
    · exact card_V2
  · intro h hh
    have hU := (hconj h _).mp hh
    obtain ⟨h1, h2⟩ := stab_of_stab_U (hE h) hU
    rcases hR with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨(hconj h _).mpr h1, (hconj h _).mpr h2⟩
    · exact ⟨(hconj h _).mpr h2, (hconj h _).mpr h1⟩
  · intro X _ hX2 hXI
    set X' : Subgroup (MulAut (projectiveSL 3 F)) := X.map ρ with hX'
    have hX'2 : IsPGroup 2 X' := hX2.map ρ
    have hX'E : X' ≤ semilinearAutGroup 3 F := by
      rintro _ ⟨x, -, rfl⟩
      exact hE x
    have hX'I : ∀ x ∈ X', x ∈
        (MulAut.conj : projectiveSL 3 F →* MulAut (projectiveSL 3 F)).range → x = 1 := by
      rintro _ ⟨x, hx, rfl⟩ hI
      have : x ∈ X ⊓ Φ.range := ⟨hx, hinner x hI⟩
      rw [hXI] at this
      rw [Subgroup.mem_bot.mp this, map_one]
    obtain ⟨hcyc, hcard⟩ := isCyclic_card_le (by omega) hF hX'2 hX'E hX'I
    have hcardX : Nat.card X = Nat.card X' := (Subgroup.card_map_of_injective hρ).symm
    refine ⟨?_, ?_⟩
    · have := hcyc
      exact isCyclic_of_injective (Subgroup.equivMapOfInjective X ρ hρ).toMonoidHom
        (Subgroup.equivMapOfInjective X ρ hρ).injective
    · rw [hcardX]
      calc Nat.card X' ≤ f := hcard
        _ < 2 ^ f := Nat.lt_two_pow_self
        _ = Nat.card F := hF.symm
  · intro h _ hk hIh
    obtain ⟨k, hk⟩ := hk
    have hθE := hE h
    have hθord : orderOf (ρ h) = 2 ^ k := by rw [orderOf_injective ρ hρ h]; exact hk
    have hθI : ρ h ∉ (MulAut.conj : projectiveSL 3 F →* MulAut (projectiveSL 3 F)).range :=
      fun hI => hIh (hinner h hI)
    have hθD := not_mem_linearAut_of_two_power hθord hθI
    have hRle : ∀ R : Subgroup (projectiveSL 3 F), (R = V1 ∨ R = V2) → ∀ B : Subgroup H,
        B ≤ R.map Φ → (∀ g ∈ B, h * g = g * h) → Nat.card B ≤ Nat.card F := by
      intro R hRV B hB hc
      have hBr : B ≤ Φ.range := hB.trans (Subgroup.map_le_range Φ _)
      have hBR : B.comap Φ ≤ R := fun p hp => (Subgroup.mem_map_iff_mem hΦ).mp (hB hp)
      have hB' : B.comap Φ ≤ V1 ∨ B.comap Φ ≤ V2 := by
        rcases hRV with rfl | rfl
        · exact Or.inl hBR
        · exact Or.inr hBR
      have := card_le_of_not_linear hB' hθD (hfix h B hBr hc)
      rwa [hcardB B hBr] at this
    refine ⟨?_, ?_, ?_⟩
    · rcases hR with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hRle _ (Or.inl rfl)
      · exact hRle _ (Or.inr rfl)
    · rcases hR with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hRle _ (Or.inr rfl)
      · exact hRle _ (Or.inl rfl)
    · intro B hB hc
      have hBr : B ≤ Φ.range := hB.trans (Subgroup.map_le_range Φ _)
      have hBW : B.comap Φ ≤ (Wg : Subgroup (projectiveSL 3 F)) := by
        rw [← centerOf_U]
        exact fun p hp => (Subgroup.mem_map_iff_mem hΦ).mp (hB hp)
      have := card_sq_le_center hBW hθE hθD (hfix h B hBr hc)
      rwa [hcardB B hBr] at this

end Action

end CFSG.Quasithin.H13.F431.L3.P3
