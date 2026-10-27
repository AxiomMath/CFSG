module

public import CFSG.LocalAnalysis.StandardType.GGHLDefs
public import CFSG.LocalAnalysis.StandardType.GGTableBUnit63Desc
public import CFSG.LocalAnalysis.StandardType.GGNbrFrameOneCoord

public section

namespace CFSG.StandardType

open CFSG

@[expose] def GGWNormConclAt (p : ℕ) {L' : Type} [Group L'] (A : Subgroup (MulAut L')) : Prop :=
  ∀ [Fact p.Prime] (Λ : Type) [Fintype Λ] [DecidableEq Λ] (M : CoxeterMatrix Λ)
    (C : Matrix Λ Λ ℤ) (V : Type) [AddCommGroup V] [Module (ZMod p) V] (ι : Additive ↥A ≃+ V)
    (φ : Λ → MulAut ↥A) (h : Λ → V) (α : Λ → Module.Dual (ZMod p) V),
    GGIsWeylMatrix M → GGIntCartan M C → (∀ i j, α i (h j) = (C i j : ZMod p)) →
    (∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i) →
    ggAutomizer (MulAut.conj : L' →* MulAut L').range A = Subgroup.closure (Set.range φ) →
    ∀ φ' ∈ ggInduced (⊤ : Subgroup (MulAut L')) A, GGWNormConcl ι φ h α φ'

section Congr

variable {p : ℕ} [Fact p.Prime] {E E₁ : Type} [Group E] [Group E₁] (e : E ≃* E₁) {V : Type}
  [AddCommGroup V] [Module (ZMod p) V]

theorem ggHL_mulEquiv_congr (ι : Additive E ≃+ V) {Λ : Type} (φ : Λ → MulAut E) (h : Λ → V)
    (α : Λ → Module.Dual (ZMod p) V) :
    ggHL ((MulEquiv.toAdditive e.symm).trans ι) (fun i => MulAut.congr e (φ i)) h α =
      ggHL ι φ h α := by
  simp only [ggHL, ggLin_mulEquiv_congr]

end Congr

section ConclCongr

variable {p : ℕ} [Fact p.Prime] {Y Y₁ : Type} [Group Y] [Group Y₁] {A : Subgroup Y}
  {A₁ : Subgroup Y₁} (e : ↥A ≃* ↥A₁) {V : Type} [AddCommGroup V] [Module (ZMod p) V]

theorem ggWNormConcl_of_mulEquiv_congr {Λ : Type} (ι : Additive ↥A ≃+ V) (φ : Λ → MulAut ↥A)
    (h : Λ → V) (α : Λ → Module.Dual (ZMod p) V) {φ' : MulAut ↥A}
    (H : GGWNormConcl ((MulEquiv.toAdditive e.symm).trans ι) (fun i => MulAut.congr e (φ i)) h α
      (MulAut.congr e φ')) :
    GGWNormConcl ι φ h α φ' := by
  obtain ⟨⟨c, w, hw, hcw⟩, hrefl⟩ := H
  rw [ggHL_mulEquiv_congr] at hw hrefl
  refine ⟨⟨c, w, hw, fun v => ?_⟩, fun hr => ?_⟩
  · rw [← hcw v, ggLin_mulEquiv_congr]
  · have := hrefl (ggIsReflection_congr e hr.1 hr.2)
    rwa [ggLin_mulEquiv_congr] at this

end ConclCongr

section Descent

open U63TB

variable {L' R : Type} [Group L'] [Finite L'] [Group R] {ψ : L' →* R}
  (hker : ψ.ker ≤ Subgroup.center L')

theorem redHom_mem_range_redSub_iff (hperf : commutator L' = ⊤) {A : Subgroup (MulAut L')}
    (hAle : A ≤ presZ (twoSub ψ.ker hker)) (τ : presZ (twoSub ψ.ker hker)) :
    redHom (twoSub ψ.ker hker) τ ∈ (redSub hker hAle).range ↔ (τ : MulAut L') ∈ A := by
  constructor
  · rintro ⟨b, hb⟩
    have hbτ : Subgroup.inclusion hAle b = τ :=
      redHom_injective _ (twoSub_le_center hker) hperf hb
    rw [← hbτ]
    exact b.2
  · intro hτ
    exact ⟨⟨τ, hτ⟩, rfl⟩

theorem mem_normalizer_iff_redHom (hperf : commutator L' = ⊤) {A : Subgroup (MulAut L')}
    (hAle : A ≤ presZ (twoSub ψ.ker hker)) (σ : presZ (twoSub ψ.ker hker)) :
    (σ : MulAut L') ∈ Subgroup.normalizer (A : Set (MulAut L')) ↔
      redHom (twoSub ψ.ker hker) σ ∈ Subgroup.normalizer
        ((redSub hker hAle).range : Set (MulAut (L' ⧸ twoSub ψ.ker hker))) := by
  have hmem := redHom_mem_range_redSub_iff hker hperf hAle
  simp only [Subgroup.mem_normalizer_iff, SetLike.mem_coe]
  constructor
  · intro hσ x
    by_cases hx : x ∈ (redHom (twoSub ψ.ker hker)).range
    · obtain ⟨τ, rfl⟩ := hx
      rw [← map_inv, ← map_mul, ← map_mul, hmem, hmem]
      exact hσ τ
    · have h1 : x ∉ (redSub hker hAle).range := by
        rintro ⟨b, rfl⟩
        exact hx ⟨_, rfl⟩
      have h2 : redHom (twoSub ψ.ker hker) σ * x * (redHom (twoSub ψ.ker hker) σ)⁻¹ ∉
          (redSub hker hAle).range := by
        rintro ⟨b, hb⟩
        refine hx ⟨σ⁻¹ * Subgroup.inclusion hAle b * σ, ?_⟩
        rw [map_mul, map_mul, map_inv]
        change (redHom (twoSub ψ.ker hker) σ)⁻¹ * redSub hker hAle b *
          redHom (twoSub ψ.ker hker) σ = x
        rw [hb]
        group
      exact iff_of_false h1 h2
  · intro hσ b
    by_cases hb : b ∈ presZ (twoSub ψ.ker hker)
    · have := hσ (redHom (twoSub ψ.ker hker) ⟨b, hb⟩)
      rw [← map_inv, ← map_mul, ← map_mul, hmem, hmem] at this
      exact this
    · have h1 : b ∉ A := fun h => hb (hAle h)
      have h2 : (σ : MulAut L') * b * (σ : MulAut L')⁻¹ ∉ A := fun h => hb (by
        have := (presZ (twoSub ψ.ker hker)).mul_mem
          ((presZ (twoSub ψ.ker hker)).mul_mem ((presZ (twoSub ψ.ker hker)).inv_mem σ.2)
            (hAle h)) σ.2
        rwa [show (σ : MulAut L')⁻¹ * ((σ : MulAut L') * b * (σ : MulAut L')⁻¹) * σ = b by
          group] at this)
      exact iff_of_false h1 h2

include hker in
theorem ggWNormConclAt_descent (hR : Subgroup.center R = ⊥) (hψ : Function.Surjective ψ)
    (hperf : commutator L' = ⊤) {A : Subgroup (MulAut L')} (hA : CFSG.Open.IsElemAbelian 3 A)
    {I : Set (MulAut R)} (hAI : ∀ a ∈ A, ∃ x ∈ I, ∀ l : L', x (ψ l) = ψ (a l))
    (h3 : 3 ^ 3 ≤ Nat.card A) (hsc : GGTorusSelfCent 3 A)
    (H : ∀ (L₁ : Type) [Group L₁] [Finite L₁] (ψ₁ : L₁ →* R), Function.Surjective ψ₁ →
      ψ₁.ker ≤ Subgroup.center L₁ → commutator L₁ = ⊤ → Odd (Nat.card ψ₁.ker) →
      ∀ A₁ : Subgroup (MulAut L₁), CFSG.Open.IsElemAbelian 3 A₁ →
        (∀ a ∈ A₁, ∃ x ∈ I, ∀ l : L₁, x (ψ₁ l) = ψ₁ (a l)) → 3 ^ 3 ≤ Nat.card A₁ →
        GGTorusSelfCent 3 A₁ → GGWNormConclAt 3 A₁) :
    GGWNormConclAt 3 A := by
  classical
  have hAle : A ≤ presZ (twoSub ψ.ker hker) := fun a ha =>
    mem_presZ_of_ker hker fun z hz => preserves_ker (hAI a ha) hz
  have H₁ := H (L' ⧸ twoSub ψ.ker hker) (psi1 hker) (psi1_surjective hker hψ)
    (psi1_ker_central hker) (commutator_quot hker hperf) (odd_card_ker_psi1 hker)
    (redSub hker hAle).range (isElemAbelian_range_redSub hker hAle hA)
    (redSub_hAI hker hAle hAI) (by rw [card_range_redSub hker hAle hperf]; exact h3)
    (selfCent_quot hker hA hAle hsc)
  obtain ⟨e, hecoe⟩ : ∃ e : ↥A ≃* ↥(redSub hker hAle).range, ∀ b : ↥A,
      ((e b : ↥(redSub hker hAle).range) : MulAut (L' ⧸ twoSub ψ.ker hker)) = redSub hker hAle b :=
    ⟨MonoidHom.ofInjective (redSub_injective hker hAle hperf), fun _ => rfl⟩
  have hkerc : ψ.ker = Subgroup.center L' := by
    refine le_antisymm hker fun z hz => ?_
    rw [MonoidHom.mem_ker]
    have hzc : ψ z ∈ Subgroup.center R := Subgroup.mem_center_iff.mpr fun r => by
      obtain ⟨l, rfl⟩ := hψ r
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz l]
    rw [hR] at hzc
    exact Subgroup.mem_bot.mp hzc
  have hpres : ∀ σ : MulAut L', σ ∈ presZ (twoSub ψ.ker hker) := fun σ =>
    mem_presZ_of_ker hker fun z hz => by
      rw [hkerc] at hz ⊢
      exact Subgroup.mem_center_iff.mpr fun l => by
        obtain ⟨l', rfl⟩ := σ.surjective l
        rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz l']
  have hind : ∀ (σ : presZ (twoSub ψ.ker hker)) (φ' : MulAut ↥A),
      (∀ b : ↥A, ((φ' b : ↥A) : MulAut L') = σ * b * (σ : MulAut L')⁻¹) →
      ∀ b₁ : ↥(redSub hker hAle).range,
        ((MulAut.congr e φ' b₁ : ↥(redSub hker hAle).range) : MulAut (L' ⧸ twoSub ψ.ker hker)) =
          redHom (twoSub ψ.ker hker) σ * b₁ * (redHom (twoSub ψ.ker hker) σ)⁻¹ := by
    intro σ φ' hφ' b₁
    obtain ⟨b, rfl⟩ := e.surjective b₁
    have e1 : MulAut.congr e φ' (e b) = e (φ' b) := by
      show e (φ' (e.symm (e b))) = e (φ' b)
      rw [MulEquiv.symm_apply_apply]
    rw [e1, hecoe, hecoe]
    have e2 : Subgroup.inclusion hAle (φ' b) = σ * Subgroup.inclusion hAle b * σ⁻¹ :=
      Subtype.ext (hφ' b)
    show redHom (twoSub ψ.ker hker) (Subgroup.inclusion hAle (φ' b)) = _
    rw [e2, map_mul, map_mul, map_inv]
    rfl
  have hset : ggInduced (MulAut.conj : (L' ⧸ twoSub ψ.ker hker) →*
        MulAut (L' ⧸ twoSub ψ.ker hker)).range (redSub hker hAle).range =
      MulAut.congr e '' ggInduced (MulAut.conj : L' →* MulAut L').range A := by
    ext ψ₁
    constructor
    · rintro ⟨g₁, ⟨m₁, rfl⟩, hg₁N, hg₁⟩
      obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective m₁
      have hconj := redHom_conjP (twoSub ψ.ker hker) m
      have hmN : (conjP (twoSub ψ.ker hker) m : MulAut L') ∈
          Subgroup.normalizer (A : Set (MulAut L')) :=
        (mem_normalizer_iff_redHom hker hperf hAle _).mpr (by rw [hconj]; exact hg₁N)
      refine ⟨ggConjAut A hmN, ⟨MulAut.conj m, ⟨m, rfl⟩, hmN, fun b => ggConjAut_apply A hmN b⟩,
        MulEquiv.ext fun b₁ => Subtype.ext ?_⟩
      rw [hind _ (ggConjAut A hmN) (fun b => ggConjAut_apply A hmN b) b₁, hconj, hg₁ b₁]
    · rintro ⟨ψ', ⟨g, ⟨m, rfl⟩, hgN, hg⟩, rfl⟩
      refine ⟨MulAut.conj (m : L' ⧸ twoSub ψ.ker hker), ⟨_, rfl⟩, ?_, fun b₁ => ?_⟩
      · rw [← redHom_conjP (twoSub ψ.ker hker) m]
        exact (mem_normalizer_iff_redHom hker hperf hAle (conjP (twoSub ψ.ker hker) m)).mp hgN
      · rw [hind (conjP (twoSub ψ.ker hker) m) ψ' hg b₁, redHom_conjP]
  intro _ Λ _ _ M C V _ _ ι φ h α hM hC hpair hlin hgen φ' hφ'
  refine ggWNormConcl_of_mulEquiv_congr e ι φ h α (H₁ Λ M C V
    ((MulEquiv.toAdditive e.symm).trans ι) (fun i => MulAut.congr e (φ i)) h α hM hC hpair
    (fun i w => by rw [ggLin_mulEquiv_congr]; exact hlin i w) ?_ (MulAut.congr e φ') ?_)
  ·
    obtain ⟨Φ, hΦ⟩ : ∃ Φ : MulAut ↥A →* MulAut ↥(redSub hker hAle).range,
        ∀ f, Φ f = MulAut.congr e f := ⟨(MulAut.congr e).toMonoidHom, fun _ => rfl⟩
    have hrange : (Set.range fun i => MulAut.congr e (φ i)) = Φ '' Set.range φ := by
      ext x
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨φ i, ⟨i, rfl⟩, hΦ (φ i)⟩
      · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
        exact ⟨i, (hΦ (φ i)).symm⟩
    have hgen' : Subgroup.closure (ggInduced (MulAut.conj : L' →* MulAut L').range A) =
        Subgroup.closure (Set.range φ) := hgen
    show Subgroup.closure (ggInduced _ _) = _
    rw [hset, Set.image_congr fun f _ => (hΦ f).symm, hrange, ← MonoidHom.map_closure,
      ← MonoidHom.map_closure, hgen']
  ·
    obtain ⟨σ, -, hσN, hσφ⟩ := hφ'
    exact ⟨redHom (twoSub ψ.ker hker) ⟨σ, hpres σ⟩, Subgroup.mem_top _,
      (mem_normalizer_iff_redHom hker hperf hAle ⟨σ, hpres σ⟩).mp hσN,
      hind ⟨σ, hpres σ⟩ φ' hσφ⟩

end Descent

end CFSG.StandardType
