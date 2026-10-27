module

public import CFSG.Timmesfeld.ARS.CaseOALevi
public import CFSG.Timmesfeld.ARS.CaseELevel
public import CFSG.Timmesfeld.ARS.CaseESpecial
public import CFSG.Timmesfeld.ARS.CaseOAInputs

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement
open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg CFSG.LieType.TitsSimplicity

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

namespace CaseOA

variable {K : Type*} [Group K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K} {Ψ : K →* G}

section Frame

variable (h : Hyp G R) {A A₀ : Subgroup G} (hA : A ∈ R) (hAne : sigmaSet R A ≠ lambdaSet R A)
  (hA₀ : A₀ ∈ omegaSet R A) (h2 : Nat.card (leviComps R A A₀) = 2) {Δ₁ Δ₂ : Set (Subgroup G)}
  (hΔ₁ : Δ₁ ∈ leviComps R A A₀) (hΔ₂ : Δ₂ ∈ leviComps R A A₀) (hne : Δ₁ ≠ Δ₂)
include h hA hAne hA₀ h2 hΔ₁ hΔ₂ hne

theorem compFrame_of_frame (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) (hdiv : D.divisible = ∅)
    (hmem : ∀ γ ∈ D.roots, (D.rootGroup γ).map Ψ ∈ Δ₁) (hrange : ∀ g, Ψ g ∈ gen Δ₁)
    (hsurj : ∀ v ∈ gen Δ₁, ∃ g, Ψ g = v)
    (hopp : ∀ k, Opposite ((D.rootGroup (Pi.single k 1)).map Ψ)
      ((D.rootGroup (-Pi.single k 1)).map Ψ)) :
    CompFrame R A A₀ D n H Ψ := by
  have hl₁ := fun {X : Subgroup G} (hX : X ∈ Δ₁) =>
    Sec9.mem_leviSet_of_mem_leviComps h hA hAne hA₀ hΔ₁ hX
  have hV₁ : gen Δ₁ ≤ levi R A A₀ := Sec9.gen_le_levi fun _ hX => hl₁ hX
  have hc := Sec9.commuting_gen_of_ne h hA hAne hA₀ hΔ₁ hΔ₂ hne
  refine ⟨hct, hext, hdiv, fun γ hγ => hl₁ (hmem γ hγ), fun g => hV₁ (hrange g),
    fun v hv => ?_, hopp⟩
  obtain ⟨v₁, hv₁, v₂, hv₂, rfl⟩ := exists_eq_mul_of_mem_levi h hA hAne hA₀ h2 hΔ₁ hΔ₂ hne hv
  obtain ⟨g, rfl⟩ := hsurj v₁ hv₁
  exact ⟨g, v₂, fun y => (hc _ (hrange y) v₂ hv₂).symm, rfl⟩

omit h2 in
theorem exists_lowest (hext : SteinbergExtras D n H) (hdiv : D.divisible = ∅)
    (hmem : ∀ γ ∈ D.roots, (D.rootGroup γ).map Ψ ∈ leviSet R A A₀) (hrange : ∀ g, Ψ g ∈ gen Δ₁)
    {P₂ Q₂ : Subgroup G} (hP₂ : P₂ ∈ Δ₂) (hQ₂ : Q₂ ∈ Δ₂) :
    ∃ E ∈ lambdaStar R A A₀, Commuting E ((negUnipotent D).map Ψ) ∧ Commuting Q₂ E := by
  have := h.finite
  have hR := h.root
  obtain ⟨E₀, hE₀, hE₀U⟩ :=
    exists_mem_lambdaStar_commuting_negUnipotent h hA hAne hA₀ hext hdiv Ψ hmem
  have hl₂ := fun {X : Subgroup G} (hX : X ∈ Δ₂) =>
    Sec9.mem_leviSet_of_mem_leviComps h hA hAne hA₀ hΔ₂ hX
  obtain ⟨B, hB, hBE⟩ : ∃ B ∈ Δ₂, Commuting B E₀ := by
    by_cases hc : Commuting E₀ P₂
    · exact ⟨P₂, hP₂, hc.symm⟩
    · have hs := special_of_not_commuting_of_mem_leviSet h hA hE₀ (hl₂ hP₂) hc
      obtain ⟨-, D', hD', hPD', hE₀D'⟩ :=
        exists_opposite_of_mem_lambdaStar h hA hAne hA₀ (hl₂ hP₂) hE₀ hs
      exact ⟨D', Sec9.mem_of_opposite h hA hAne hA₀ hΔ₂ hP₂ hD' hPD', hE₀D'.1.2.2⟩
  obtain ⟨g, hg, hgQ⟩ := Sec9.exists_conjSub_eq h hΔ₂ hB hQ₂
  have hgV : g ∈ levi R A A₀ := Sec9.gen_le_levi (fun _ hX => hl₂ hX) hg
  have hc := Sec9.commuting_gen_of_ne h hA hAne hA₀ hΔ₁ hΔ₂ hne
  refine ⟨conjSub E₀ g, conjSub_mem_lambdaStar_of_mem_levi hR hE₀ hgV, ?_, ?_⟩
  ·
    have hU : conjSub ((negUnipotent D).map Ψ) g = (negUnipotent D).map Ψ :=
      conjSub_of_forall_commute fun u hu => by
        obtain ⟨y, -, rfl⟩ := hu
        exact (hc _ (hrange y) g hg).symm
    have h1 := hE₀U.conjSub g
    rwa [hU] at h1
  · rw [← hgQ]
    exact hBE.conjSub g

end Frame

section Highest

variable (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
    (weylAction D.isFiniteType) D.roots D.rootGroup n H)
include hct

theorem commuting_posUnipotent_conjSub {w₀ : (coxeterMatrix D.isFiniteType).Group}
    (hw₀ : ∀ i, (coxeterMatrix D.isFiniteType).toCoxeterSystem.IsRightDescent w₀ i)
    {X : Subgroup G} (hXU : Commuting X ((negUnipotent D).map Ψ)) :
    Commuting (conjSub X (Ψ (nrep hct w₀))⁻¹) ((posUnipotent D).map Ψ) := by
  refine (hXU.conjSub (Ψ (nrep hct w₀))⁻¹).mono le_rfl ?_
  rintro _ ⟨u, hu, rfl⟩
  rw [mem_conjSub, inv_inv, ← map_mul, ← map_inv, ← map_mul]
  exact Subgroup.mem_map_of_mem Ψ
    (nrep_conj_mem_negUnipotent_of_forall_isRightDescent hct hw₀ hu)

theorem map_iSup_le_normalizer_conjSub (w₀ : (coxeterMatrix D.isFiniteType).Group)
    {X : Subgroup G} (hXT : (⨆ i, H i).map Ψ ≤ Subgroup.normalizer (X : Set G)) :
    (⨆ i, H i).map Ψ ≤
      Subgroup.normalizer ((conjSub X (Ψ (nrep hct w₀))⁻¹ : Subgroup G) : Set G) := by
  rintro _ ⟨s, hs, rfl⟩
  rw [← conjSub_eq_self_iff, ← conjSub_mul]
  have e : Ψ s * (Ψ (nrep hct w₀))⁻¹ =
      (Ψ (nrep hct w₀))⁻¹ * Ψ (nrep hct w₀ * s * (nrep hct w₀)⁻¹) := by
    rw [map_mul, map_mul, map_inv]
    group
  rw [e, conjSub_mul, conjSub_eq_self_iff.2 (hXT (Subgroup.mem_map_of_mem Ψ
    (conj_mem_iSup_of_mem_weylN hct (nrep_mem_weylN hct w₀) hs)))]

end Highest

theorem commutator_eq_of_frames (h : Hyp G R) {A A₀ : Subgroup G} (hA : A ∈ R)
    (hAne : sigmaSet R A ≠ lambdaSet R A) (hmax : IsSigmaMaximal R (centralGroup R A))
    (hA₀ : A₀ ∈ omegaSet R A) (h2 : Nat.card (leviComps R A A₀) = 2) {Δ₁ Δ₂ : Set (Subgroup G)}
    (hΔ₁ : Δ₁ ∈ leviComps R A A₀) (hΔ₂ : Δ₂ ∈ leviComps R A A₀) (hne : Δ₁ ≠ Δ₂)
    {P₂ Q₂ : Subgroup G} (hP₂ : P₂ ∈ Δ₂) (hQ₂ : Q₂ ∈ Δ₂) (hPQ₂ : Opposite P₂ Q₂)
    (hgen₂ : gen Δ₂ = P₂ ⊔ Q₂)
    {K₁ : Type*} [Group K₁] {D₁ : UniversalRootDatum K₁} {n₁ : Fin D₁.rank → K₁}
    {H₁ : Fin D₁.rank → Subgroup K₁} {Ψ₁ : K₁ →* G} (hF₁ : CompFrame R A A₀ D₁ n₁ H₁ Ψ₁)
    (hrange₁ : ∀ g, Ψ₁ g ∈ gen Δ₁) (hsurj₁ : ∀ v ∈ gen Δ₁, ∃ g, Ψ₁ g = v)
    (hpd₁ : (D₁.cartan.map (Int.cast : ℤ → ℚ)).PosDef) {adj : Fin D₁.rank → Fin D₁.rank → Prop}
    (hX₁ : IsConfig R adj (fun k => (D₁.rootGroup (Pi.single k 1)).map Ψ₁)
      (fun k => (D₁.rootGroup (-Pi.single k 1)).map Ψ₁))
    (hadj₁ : ∀ a b, D₁.cartan a b = -1 → adj a b ∨ adj b a)
    {K₂ : Type*} [Group K₂] {D₂ : UniversalRootDatum K₂} {n₂ : Fin D₂.rank → K₂}
    {H₂ : Fin D₂.rank → Subgroup K₂} {Ψ₂ : K₂ →* G} (hF₂ : CompFrame R A A₀ D₂ n₂ H₂ Ψ₂)
    (hrange₂ : ∀ g, Ψ₂ g ∈ gen Δ₂) (hsurj₂ : ∀ v ∈ gen Δ₂, ∃ g, Ψ₂ g = v)
    (hQ₂Ψ : ∀ k, (D₂.rootGroup (-Pi.single k 1)).map Ψ₂ = Q₂) {E C : Subgroup G}
    (hE : E ∈ lambdaStar R A A₀) (hEU₁ : Commuting E ((negUnipotent D₁).map Ψ₁))
    (hEU₂ : Commuting E ((negUnipotent D₂).map Ψ₂))
    (hET₁ : (⨆ i, H₁ i).map Ψ₁ ≤ Subgroup.normalizer (E : Set G))
    (hET₂ : (⨆ i, H₂ i).map Ψ₂ ≤ Subgroup.normalizer (E : Set G))
    (hC : C ∈ lambdaStar R A A₀) (hCU₁ : Commuting C ((posUnipotent D₁).map Ψ₁))
    (hCU₂ : Commuting C ((posUnipotent D₂).map Ψ₂))
    (hCT₁ : (⨆ i, H₁ i).map Ψ₁ ≤ Subgroup.normalizer (C : Set G))
    (hCT₂ : (⨆ i, H₂ i).map Ψ₂ ≤ Subgroup.normalizer (C : Set G)) :
    Special R E C ∧ ⁅E, C⁆ = A := by
  have := h.finite
  have hR := h.root
  have hc := Sec9.commuting_gen_of_ne h hA hAne hA₀ hΔ₁ hΔ₂ hne
  have hcomm : ∀ a b, Commute (Ψ₁ a) (Ψ₂ b) := fun a b => hc _ (hrange₁ a) _ (hrange₂ b)
  have hsing₁ : ∀ k, (Pi.single k 1 : Fin D₁.rank → ℤ) ∈ D₁.roots := fun k =>
    (RootSystem.ofCartan D₁.isFiniteType D₁.divisible).single_mem k
  have hsing₂ : ∀ k, (Pi.single k 1 : Fin D₂.rank → ℤ) ∈ D₂.roots := fun k =>
    (RootSystem.ofCartan D₂.isFiniteType D₂.divisible).single_mem k
  have hnsing₁ : ∀ k, (-Pi.single k 1 : Fin D₁.rank → ℤ) ∈ D₁.roots := fun k =>
    (RootSystem.ofCartan D₁.isFiniteType D₁.divisible).neg_mem _ (hsing₁ k)
  have hnsing₂ : ∀ k, (-Pi.single k 1 : Fin D₂.rank → ℤ) ∈ D₂.roots := fun k =>
    (RootSystem.ofCartan D₂.isFiniteType D₂.divisible).neg_mem _ (hsing₂ k)
  have hmapsup₁ : ∀ {y : K₁} {X Y : Subgroup K₁}, y ∈ X ⊔ Y → Ψ₁ y ∈ X.map Ψ₁ ⊔ Y.map Ψ₁ :=
    fun hy => by
      rw [← Subgroup.map_sup]
      exact Subgroup.mem_map_of_mem Ψ₁ hy
  have hmapsup₂ : ∀ {y : K₂} {X Y : Subgroup K₂}, y ∈ X ⊔ Y → Ψ₂ y ∈ X.map Ψ₂ ⊔ Y.map Ψ₂ :=
    fun hy => by
      rw [← Subgroup.map_sup]
      exact Subgroup.mem_map_of_mem Ψ₂ hy
  have hfixA : ∀ (Y : Subgroup K₁) (b : K₂), conjSub (Y.map Ψ₁) (Ψ₂ b)⁻¹ = Y.map Ψ₁ :=
    fun Y b => conjSub_of_forall_commute fun z hz => by
      obtain ⟨w, -, rfl⟩ := hz
      exact ((hcomm w b).symm).inv_left
  have hfixA' : ∀ (Y : Subgroup K₁) (b : K₂), conjSub (Y.map Ψ₁) (Ψ₂ b) = Y.map Ψ₁ :=
    fun Y b => conjSub_of_forall_commute fun z hz => by
      obtain ⟨w, -, rfl⟩ := hz
      exact (hcomm w b).symm
  have hfixB : ∀ (Y : Subgroup K₂) (a : K₁), conjSub (Y.map Ψ₂) (Ψ₁ a)⁻¹ = Y.map Ψ₂ :=
    fun Y a => conjSub_of_forall_commute fun z hz => by
      obtain ⟨w, -, rfl⟩ := hz
      exact (hcomm a w).inv_left
  refine commutator_eq_of_bruhat h hA hAne hmax hA₀
    (ι := Fin D₁.rank ⊕ Fin D₂.rank) (κ := weylN n₁ H₁ × weylN n₂ H₂)
    (U := (negUnipotent D₁).map Ψ₁ ⊔ (negUnipotent D₂).map Ψ₂)
    (U' := (posUnipotent D₁).map Ψ₁ ⊔ (posUnipotent D₂).map Ψ₂)
    (T := (⨆ i, H₁ i).map Ψ₁ ⊔ (⨆ i, H₂ i).map Ψ₂)
    (P := Sum.elim (fun k => (D₁.rootGroup (Pi.single k 1)).map Ψ₁)
      (fun k => (D₂.rootGroup (Pi.single k 1)).map Ψ₂))
    (Q := Sum.elim (fun k => (D₁.rootGroup (-Pi.single k 1)).map Ψ₁)
      (fun k => (D₂.rootGroup (-Pi.single k 1)).map Ψ₂))
    (x := fun y => Ψ₁ y.1 * Ψ₂ y.2)
    (ℓ := fun y => (coxeterMatrix D₁.isFiniteType).toCoxeterSystem.length
        (weylNHom hF₁.hct hF₁.hext y.1) +
      (coxeterMatrix D₂.isFiniteType).toCoxeterSystem.length (weylNHom hF₂.hct hF₂.hext y.2))
    (fun y => mul_mem (hF₁.range _) (hF₂.range _)) ?_ ?_ ?_ ?_ hE hC (hEU₁.sup_right hEU₂)
    (sup_le hET₁ hET₂) (hCU₁.sup_right hCU₂) (sup_le hCT₁ hCT₂) ?_
  ·
    intro v hv
    obtain ⟨v₁, hv₁, v₂, hv₂, rfl⟩ := exists_eq_mul_of_mem_levi h hA hAne hA₀ h2 hΔ₁ hΔ₂ hne hv
    obtain ⟨g₁, rfl⟩ := hsurj₁ v₁ hv₁
    obtain ⟨g₂, rfl⟩ := hsurj₂ v₂ hv₂
    obtain ⟨b₁, hb₁, y₁, hy₁, b₁', hb₁', rfl⟩ :=
      exists_eq_mul_mul_borel_negBorel hF₁.hct hF₁.hext g₁
    obtain ⟨b₂, hb₂, y₂, hy₂, b₂', hb₂', rfl⟩ :=
      exists_eq_mul_mul_borel_negBorel hF₂.hct hF₂.hext g₂
    have hle : ∀ {A₁ A₂ B₁ B₂ : Subgroup G} {g : G}, g ∈ A₁ ⊔ B₁ → A₁ ≤ A₂ → B₁ ≤ B₂ →
        g ∈ A₂ ⊔ B₂ := fun hg hA hB => sup_le_sup hA hB hg
    have h1 := hmapsup₁ hb₁
    have h2' := hmapsup₂ hb₂
    have h3 := hmapsup₁ hb₁'
    have h4 := hmapsup₂ hb₂'
    refine ⟨Ψ₁ b₁ * Ψ₂ b₂, mul_mem ?_ ?_, (⟨y₁, hy₁⟩, ⟨y₂, hy₂⟩), Ψ₁ b₁' * Ψ₂ b₂',
      mul_mem ?_ ?_, ?_⟩
    · exact hle h1 le_sup_left le_sup_left
    · exact hle h2' le_sup_right le_sup_right
    · exact hle h3 le_sup_left le_sup_left
    · exact hle h4 le_sup_right le_sup_right
    · simp only [map_mul]
      calc Ψ₁ b₁ * Ψ₁ y₁ * Ψ₁ b₁' * (Ψ₂ b₂ * Ψ₂ y₂ * Ψ₂ b₂')
          = Ψ₁ b₁ * Ψ₁ y₁ * (Ψ₁ b₁' * Ψ₂ b₂) * Ψ₂ y₂ * Ψ₂ b₂' := by group
        _ = Ψ₁ b₁ * Ψ₁ y₁ * (Ψ₂ b₂ * Ψ₁ b₁') * Ψ₂ y₂ * Ψ₂ b₂' := by rw [(hcomm b₁' b₂).eq]
        _ = Ψ₁ b₁ * (Ψ₁ y₁ * Ψ₂ b₂) * (Ψ₁ b₁' * Ψ₂ y₂) * Ψ₂ b₂' := by group
        _ = Ψ₁ b₁ * (Ψ₂ b₂ * Ψ₁ y₁) * (Ψ₂ y₂ * Ψ₁ b₁') * Ψ₂ b₂' := by
          rw [(hcomm y₁ b₂).eq, (hcomm b₁' y₂).eq]
        _ = Ψ₁ b₁ * Ψ₂ b₂ * (Ψ₁ y₁ * Ψ₂ y₂) * (Ψ₁ b₁' * Ψ₂ b₂') := by group
  ·
    rintro (k | k)
    · exact ⟨hF₁.mem _ (hsing₁ k), hF₁.mem _ (hnsing₁ k), hF₁.opp k⟩
    · exact ⟨hF₂.mem _ (hsing₂ k), hF₂.mem _ (hnsing₂ k), hF₂.opp k⟩
  · rintro (k | k)
    · exact (Subgroup.map_mono (rootGroup_le_posUnipotent (hsing₁ k)
        (ht_single_pos k))).trans le_sup_left
    · exact (Subgroup.map_mono (rootGroup_le_posUnipotent (hsing₂ k)
        (ht_single_pos k))).trans le_sup_right
  ·
    rintro ⟨y₁, y₂⟩
    rcases exists_left_descent_of_mem_weylN hF₁.hct hF₁.hext y₁ with
      hy₁ | ⟨j, y₁', m, hm, hy, hlt, hle⟩
    · rcases exists_left_descent_of_mem_weylN hF₂.hct hF₂.hext y₂ with
        hy₂ | ⟨j, y₂', m, hm, hy, hlt, hle⟩
      · exact Or.inl (mul_mem (Subgroup.mem_sup_left (Subgroup.mem_map_of_mem Ψ₁ hy₁))
          (Subgroup.mem_sup_right (Subgroup.mem_map_of_mem Ψ₂ hy₂)))
      · refine Or.inr ⟨Sum.inr j, (y₁, y₂'), Ψ₂ m, hmapsup₂ hm, ?_, ?_, ?_⟩
        · change Ψ₁ y₁ * Ψ₂ y₂ = Ψ₂ m * (Ψ₁ y₁ * Ψ₂ y₂')
          rw [hy, map_mul, ← mul_assoc, (hcomm y₁ m).eq, mul_assoc]
        · dsimp only
          omega
        · change conjSub ((D₂.rootGroup (-Pi.single j 1)).map Ψ₂) (Ψ₁ y₁ * Ψ₂ y₂')⁻¹ ≤ _
          rw [mul_inv_rev, conjSub_mul, hfixB, ← map_inv Ψ₂, map_conjSub_eq]
          exact (Subgroup.map_mono hle).trans le_sup_right
    · refine Or.inr ⟨Sum.inl j, (y₁', y₂), Ψ₁ m, hmapsup₁ hm, ?_, ?_, ?_⟩
      · change Ψ₁ y₁ * Ψ₂ y₂ = Ψ₁ m * (Ψ₁ y₁' * Ψ₂ y₂)
        rw [hy, map_mul, mul_assoc]
      · dsimp only
        omega
      · change conjSub ((D₁.rootGroup (-Pi.single j 1)).map Ψ₁) (Ψ₁ y₁' * Ψ₂ y₂)⁻¹ ≤ _
        rw [mul_inv_rev, conjSub_mul, ← map_inv Ψ₁, map_conjSub_eq, hfixA]
        exact (Subgroup.map_mono hle).trans le_sup_left
  ·
    rintro ⟨y₁, y₂⟩ (j | j) hQ hP
    · change ¬ Commuting (conjSub E (Ψ₁ y₁ * Ψ₂ y₂)) ((D₁.rootGroup (Pi.single j 1)).map Ψ₁)
        at hP
      change conjSub E (Ψ₁ y₁ * Ψ₂ y₂) ∈ lambdaSet R ((D₁.rootGroup (-Pi.single j 1)).map Ψ₁)
      rw [conjSub_mul] at hP ⊢
      have hE' : conjSub E (Ψ₂ y₂) ∈ lambdaStar R A A₀ :=
        conjSub_mem_lambdaStar_of_mem_levi hR hE (hF₂.range _)
      have hE'U : Commuting (conjSub E (Ψ₂ y₂)) ((negUnipotent D₁).map Ψ₁) := by
        have h1 := hEU₁.conjSub (Ψ₂ y₂)
        rwa [hfixA'] at h1
      exact mem_lambdaSet_of_mem_weylN h hA hAne hmax hA₀ hF₁ hpd₁ hE' hE'U hX₁ hadj₁ y₁.2 j hP
    · change Commuting (conjSub E (Ψ₁ y₁ * Ψ₂ y₂)) ((D₂.rootGroup (-Pi.single j 1)).map Ψ₂)
        at hQ
      change conjSub E (Ψ₁ y₁ * Ψ₂ y₂) ∈ lambdaSet R ((D₂.rootGroup (-Pi.single j 1)).map Ψ₂)
      rw [hQ₂Ψ j] at hQ ⊢
      exact (natural_of_sl2 h hA hAne hmax hA₀ hΔ₂ hP₂ hQ₂ hPQ₂ hgen₂
        (conjSub_mem_lambdaStar_of_mem_levi hR hE (mul_mem (hF₁.range _) (hF₂.range _)))
        hQ.symm).1

theorem commuting_conjSub_iff {X Y : Subgroup G} (g : G) :
    Commuting (conjSub X g) (conjSub Y g) ↔ Commuting X Y := by
  refine ⟨fun hc => ?_, fun hc => hc.conjSub g⟩
  have h1 := hc.conjSub g⁻¹
  rwa [← conjSub_mul, ← conjSub_mul, inv_mul_cancel, conjSub_one, conjSub_one] at h1

theorem exists_node (h : Hyp G R) {A A₀ : Subgroup G} (hA : A ∈ R)
    (hAne : sigmaSet R A ≠ lambdaSet R A) (hmax : IsSigmaMaximal R (centralGroup R A))
    (hA₀ : A₀ ∈ omegaSet R A) (h2 : Nat.card (leviComps R A A₀) = 2) {Δ₁ Δ₂ : Set (Subgroup G)}
    (hΔ₁ : Δ₁ ∈ leviComps R A A₀) (hΔ₂ : Δ₂ ∈ leviComps R A A₀) (hne : Δ₁ ≠ Δ₂)
    (hS₁ : ¬ IsSL2Comp Δ₁) (hnd : ∃ X ∈ Δ₁, ∃ Y ∈ Δ₁, Special R X Y) {P₂ Q₂ : Subgroup G}
    (hP₂ : P₂ ∈ Δ₂) (hQ₂ : Q₂ ∈ Δ₂) (hPQ₂ : Opposite P₂ Q₂) (hgen₂ : gen Δ₂ = P₂ ⊔ Q₂)
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) (hdiv : D.divisible = ∅)
    (hpd : (D.cartan.map (Int.cast : ℤ → ℚ)).PosDef)
    (hmem : ∀ γ ∈ D.roots, (D.rootGroup γ).map Ψ ∈ Δ₁) (hrange : ∀ g, Ψ g ∈ gen Δ₁)
    (hsurj : ∀ v ∈ gen Δ₁, ∃ g, Ψ g = v) {P Q : Fin D.rank → Subgroup G}
    (hP : ∀ k, (D.rootGroup (Pi.single k 1)).map Ψ = P k)
    (hQ : ∀ k, (D.rootGroup (-Pi.single k 1)).map Ψ = Q k)
    {adj : Fin D.rank → Fin D.rank → Prop} (hX : IsConfig R adj P Q)
    (hadj : ∀ a b, D.cartan a b = -1 → adj a b ∨ adj b a)
    (hgen₁ : ⨆ k, (P k ⊔ Q k) = gen Δ₁)
    {θ : Fin D.rank → ℤ} (hθ : θ ∈ D.roots) (hθ1 : ∀ i, 1 ≤ θ i) :
    ∃ E C, Lowest R A A₀ P Q P₂ Q₂ E C ∧ ⁅E, C⁆ = A ∧ Commuting E ((negUnipotent D).map Ψ) ∧
      ∃ j, θ j = 1 ∧ (∀ k, ¬ Commuting E (P k) ↔ k = j) ∧
        ∃ w₀ : (coxeterMatrix D.isFiniteType).Group,
          (∀ w, (coxeterMatrix D.isFiniteType).toCoxeterSystem.length w ≤
            (coxeterMatrix D.isFiniteType).toCoxeterSystem.length w₀) ∧
          weylAction D.isFiniteType w₀ (Pi.single j 1) = -Pi.single j 1 := by
  obtain rfl : (fun k => (D.rootGroup (Pi.single k 1)).map Ψ) = P := funext hP
  obtain rfl : (fun k => (D.rootGroup (-Pi.single k 1)).map Ψ) = Q := funext hQ
  have := h.finite
  have hR := h.root
  have hc := Sec9.commuting_gen_of_ne h hA hAne hA₀ hΔ₁ hΔ₂ hne
  set Φ := RootSystem.ofCartan D.isFiniteType D.divisible
  have hsing : ∀ k, (Pi.single k 1 : Fin D.rank → ℤ) ∈ D.roots := fun k => Φ.single_mem k
  have hnsing : ∀ k, (-Pi.single k 1 : Fin D.rank → ℤ) ∈ D.roots := fun k =>
    Φ.neg_mem _ (hsing k)
  have hneg : ∀ k, ht (-Pi.single k 1 : Fin D.rank → ℤ) < 0 := fun k => by
    rw [ht_neg, ht_single]
    omega
  have hF₁ : CompFrame R A A₀ D n H Ψ :=
    compFrame_of_frame h hA hAne hA₀ h2 hΔ₁ hΔ₂ hne hct hext hdiv hmem hrange hsurj hX.opp
  obtain ⟨n₂, Ψ₂, hF₂, hrange₂, hsurj₂, hP₂Ψ, hQ₂Ψ⟩ :=
    exists_compFrame_sl2 h hA hAne hA₀ h2 hΔ₁ hΔ₂ hne hP₂ hPQ₂ hgen₂
  have hcomm : ∀ a b, Commute (Ψ a) (Ψ₂ b) := fun a b => hc _ (hrange a) _ (hrange₂ b)
  have hQ₂Ψ' : ∀ k, ((SpecialLinear.rootDatum 1 (GaloisField 2 n₂)).rootGroup
      (-Pi.single k 1)).map Ψ₂ = Q₂ := fun k => by
    obtain rfl : k = ⟨0, Nat.one_pos⟩ := Fin.ext (Nat.lt_one_iff.1 k.2)
    exact hQ₂Ψ
  obtain ⟨E, hE, hEU₁, hQ₂E⟩ :=
    exists_lowest h hA hAne hA₀ hΔ₁ hΔ₂ hne hext hdiv hF₁.mem hrange hP₂ hQ₂
  have hEU₂ : Commuting E
      ((negUnipotent (SpecialLinear.rootDatum 1 (GaloisField 2 n₂))).map Ψ₂) := by
    refine commuting_map_negUnipotent fun γ hγ hγn => ?_
    rcases eq_or_eq_neg_of_mem_roots_SL2 _ hγ with rfl | rfl
    · exfalso
      change ∑ j : Fin 1, (Pi.single (0 : Fin 1) (1 : ℤ) : Fin 1 → ℤ) j < 0 at hγn
      simp at hγn
    · rw [hQ₂Ψ]
      exact hQ₂E.symm
  have hET₁ := map_iSup_le_normalizer_of_commuting_negUnipotent h hA hAne hmax hA₀ hF₁ hE hEU₁
  have hET₂ := map_iSup_le_normalizer_of_commuting_negUnipotent h hA hAne hmax hA₀ hF₂ hE hEU₂
  have := finite_group D.isFiniteType
  obtain ⟨w₁, hw₁⟩ := Finite.exists_max fun w : (coxeterMatrix D.isFiniteType).Group =>
    (coxeterMatrix D.isFiniteType).toCoxeterSystem.length w
  have hw₁d : ∀ i, (coxeterMatrix D.isFiniteType).toCoxeterSystem.IsRightDescent w₁ i :=
    fun i => by_contra fun hi => by
      have h' := (coxeterMatrix D.isFiniteType).toCoxeterSystem.not_isRightDescent_iff.mp hi
      have := hw₁ (w₁ * (coxeterMatrix D.isFiniteType).toCoxeterSystem.simple i)
      omega
  obtain ⟨w₂, hw₂d⟩ := exists_forall_isRightDescent
    (D := SpecialLinear.rootDatum 1 (GaloisField 2 n₂))
  set C₁ := conjSub E (Ψ (nrep hct w₁))⁻¹ with hC₁def
  set C := conjSub C₁ (Ψ₂ (nrep hF₂.hct w₂))⁻¹ with hCdef
  have hC₁ : C₁ ∈ lambdaStar R A A₀ :=
    conjSub_mem_lambdaStar_of_mem_levi hR hE (inv_mem (hF₁.range _))
  have hC : C ∈ lambdaStar R A A₀ :=
    conjSub_mem_lambdaStar_of_mem_levi hR hC₁ (inv_mem (hF₂.range _))
  have hfix₂ : ∀ (Y : Subgroup _) (a : K), conjSub (Y.map Ψ₂) (Ψ a)⁻¹ = Y.map Ψ₂ :=
    fun Y a => conjSub_of_forall_commute fun z hz => by
      obtain ⟨w, -, rfl⟩ := hz
      exact (hcomm a w).inv_left
  have hfix₁ : ∀ (Y : Subgroup K)
      (b : Matrix.SpecialLinearGroup (Fin (1 + 1)) (GaloisField 2 n₂)),
      conjSub (Y.map Ψ) (Ψ₂ b)⁻¹ = Y.map Ψ :=
    fun Y b => conjSub_of_forall_commute fun z hz => by
      obtain ⟨w, -, rfl⟩ := hz
      exact ((hcomm w b).symm).inv_left
  have hC₁U₁ : Commuting C₁ ((posUnipotent D).map Ψ) :=
    commuting_posUnipotent_conjSub hct hw₁d hEU₁
  have hC₁T₁ := map_iSup_le_normalizer_conjSub hct w₁ hET₁
  have hC₁U₂ : Commuting C₁
      ((negUnipotent (SpecialLinear.rootDatum 1 (GaloisField 2 n₂))).map Ψ₂) := by
    have h1 := hEU₂.conjSub (Ψ (nrep hct w₁))⁻¹
    rwa [hfix₂] at h1
  have hC₁T₂ : (⨆ i, SpecialLinear.torus 1 (GaloisField 2 n₂) i).map Ψ₂ ≤
      Subgroup.normalizer (C₁ : Set G) := by
    rintro _ ⟨s, hs, rfl⟩
    rw [← conjSub_eq_self_iff, hC₁def, ← conjSub_mul, ← (hcomm (nrep hct w₁) s).inv_left.eq,
      conjSub_mul, conjSub_eq_self_iff.2 (hET₂ ⟨s, hs, rfl⟩)]
  have hCU₂ : Commuting C ((posUnipotent (SpecialLinear.rootDatum 1 (GaloisField 2 n₂))).map Ψ₂) :=
    commuting_posUnipotent_conjSub hF₂.hct hw₂d hC₁U₂
  have hCT₂ := map_iSup_le_normalizer_conjSub hF₂.hct w₂ hC₁T₂
  have hCU₁ : Commuting C ((posUnipotent D).map Ψ) := by
    have h1 := hC₁U₁.conjSub (Ψ₂ (nrep hF₂.hct w₂))⁻¹
    rwa [hfix₁] at h1
  have hCT₁ : (⨆ i, H i).map Ψ ≤ Subgroup.normalizer (C : Set G) := by
    rintro _ ⟨s, hs, rfl⟩
    rw [← conjSub_eq_self_iff, hCdef, ← conjSub_mul, (hcomm s (nrep hF₂.hct w₂)).inv_right.eq,
      conjSub_mul, conjSub_eq_self_iff.2 (hC₁T₁ ⟨s, hs, rfl⟩)]
  obtain ⟨-, hEC⟩ := commutator_eq_of_frames h hA hAne hmax hA₀ h2 hΔ₁ hΔ₂ hne hP₂ hQ₂ hPQ₂
    hgen₂ hF₁ hrange hsurj hpd hX hadj hF₂ hrange₂ hsurj₂ hQ₂Ψ' hE hEU₁ hEU₂ hET₁ hET₂ hC hCU₁
    hCU₂ hCT₁ hCT₂
  have hQE : ∀ k, Commuting ((D.rootGroup (-Pi.single k 1)).map Ψ) E := fun k =>
    (hEU₁.mono le_rfl (map_rootGroup_le_map_negUnipotent (hnsing k) (hneg k))).symm
  obtain ⟨j, hj, hjE⟩ := exists_eq_of_highest_of_exists h hA hAne hmax hA₀ hF₁ hpd hE hEU₁ hX
    hadj hθ hθ1 (exists_not_commuting h hA hAne hmax hA₀ hΔ₁ hS₁ hnd hgen₁ hE hQE)
  have hlow := natural_of_commuting_negUnipotent h hA hAne hmax hA₀ hF₁ hE hEU₁
  have hact := actsAs_nrep hct w₁
  have hacti := hact.inv
  have hkey : ∀ k i, weylAction D.isFiniteType w₁ (Pi.single k 1) = -Pi.single i 1 →
      ¬ Commuting C ((D.rootGroup (-Pi.single k 1)).map Ψ) →
      ¬ Commuting E ((D.rootGroup (Pi.single i 1)).map Ψ) := by
    intro k i hi hck hEi
    apply hck
    have e1 : conjSub ((D.rootGroup (-Pi.single k 1)).map Ψ) (Ψ (nrep hct w₁)) =
        (D.rootGroup (Pi.single i 1)).map Ψ := by
      rw [map_conjSub_eq, hact _ (hnsing k), map_neg, hi, neg_neg]
    have h1 : Commuting C₁ ((D.rootGroup (-Pi.single k 1)).map Ψ) := by
      rw [← commuting_conjSub_iff (Ψ (nrep hct w₁)), hC₁def, ← conjSub_mul, mul_inv_cancel,
        conjSub_one, e1]
      exact hEi
    have h2 := h1.conjSub (Ψ₂ (nrep hF₂.hct w₂))⁻¹
    rwa [hfix₁] at h2
  have hhigh : ∀ k, Commuting C ((D.rootGroup (-Pi.single k 1)).map Ψ) ∨
      (C ∈ lambdaSet R ((D.rootGroup (Pi.single k 1)).map Ψ) ∧
        Special R C ((D.rootGroup (-Pi.single k 1)).map Ψ)) := by
    intro k
    by_cases hck : Commuting C ((D.rootGroup (-Pi.single k 1)).map Ψ)
    · exact Or.inl hck
    right
    obtain ⟨i, hi⟩ := exists_weylAction_eq_neg_single D.isFiniteType hpd hw₁ k
    have hwi : weylAction D.isFiniteType w₁⁻¹ (Pi.single i 1) = -Pi.single k 1 := by
      rw [← neg_neg (Pi.single i 1 : Fin D.rank → ℤ), ← hi, map_neg,
        weylAction_inv_apply_apply]
    have e2 : conjSub ((D.rootGroup (-Pi.single i 1)).map Ψ) (Ψ (nrep hct w₁))⁻¹ =
        (D.rootGroup (Pi.single k 1)).map Ψ := by
      rw [← map_inv, map_conjSub_eq, hacti _ (hnsing i), map_neg, hwi, neg_neg]
    have e3 : conjSub ((D.rootGroup (Pi.single i 1)).map Ψ) (Ψ (nrep hct w₁))⁻¹ =
        (D.rootGroup (-Pi.single k 1)).map Ψ := by
      rw [← map_inv, map_conjSub_eq, hacti _ (hsing i), hwi]
    obtain ⟨hEl, hEs⟩ := (hlow i).resolve_left (hkey k i hi hck)
    have hC₁l := conjSub_mem_lambdaSet hR hEl (Ψ (nrep hct w₁))⁻¹
    have hC₁s := Sec3.special_conjSub hR hEs (Ψ (nrep hct w₁))⁻¹
    rw [e2] at hC₁l
    rw [e3] at hC₁s
    have hCl := conjSub_mem_lambdaSet hR hC₁l (Ψ₂ (nrep hF₂.hct w₂))⁻¹
    have hCs := Sec3.special_conjSub hR hC₁s (Ψ₂ (nrep hF₂.hct w₂))⁻¹
    rw [hfix₁] at hCl hCs
    exact ⟨hCl, hCs⟩
  have hLow : Lowest R A A₀ (fun k => (D.rootGroup (Pi.single k 1)).map Ψ)
      (fun k => (D.rootGroup (-Pi.single k 1)).map Ψ) P₂ Q₂ E C := by
    refine ⟨hE, hC, hQ₂E, ?_, hQE, fun k => ?_, hlow, hhigh⟩
    · rw [← hP₂Ψ]
      exact (hCU₂.mono le_rfl (Subgroup.map_mono (rootGroup_le_posUnipotent
        ((RootSystem.ofCartan _ _).single_mem _) (ht_single_pos _)))).symm
    · exact (hCU₁.mono le_rfl (Subgroup.map_mono (rootGroup_le_posUnipotent (hsing k)
        (ht_single_pos k)))).symm
  have hjw : weylAction D.isFiniteType w₁ (Pi.single j 1) = -Pi.single j 1 := by
    obtain ⟨i, hi⟩ := exists_weylAction_eq_neg_single D.isFiniteType hpd hw₁ j
    have hCj : ¬ Commuting C ((D.rootGroup (-Pi.single j 1)).map Ψ) := by
      rw [← Lowest.not_commuting_iff h hA hX
        (fun k => ⟨hF₁.mem _ (hsing k), hF₁.mem _ (hnsing k)⟩) hLow hEC j]
      exact (hjE j).2 rfl
    rw [hi, (hjE i).1 (hkey j i hi hCj)]
  exact ⟨E, C, hLow, hEC, hEU₁, j, hj, hjE, w₁, hw₁, hjw⟩

end CaseOA

end CFSG.Timmesfeld.ARS
