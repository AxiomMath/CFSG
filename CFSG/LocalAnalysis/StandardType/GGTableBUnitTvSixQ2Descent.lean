module

public import CFSG.LocalAnalysis.StandardType.GGTableBUnit63Desc
public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs

public section

namespace CFSG.StandardType.UnitTvQ2

open CFSG.StandardType.U63TB

theorem ggIsTransvection_transport {p : ℕ} {G G' : Type} [Group G] [Group G']
    {Bs : Subgroup G} {Bs' : Subgroup G'} (e : ↥Bs ≃* ↥Bs') {φ : MulAut ↥Bs}
    {ψ : MulAut ↥Bs'} (h : ∀ b : ↥Bs, e (φ b) = ψ (e b)) (hφ : GGIsTransvection p φ) :
    GGIsTransvection p ψ := by
  obtain ⟨h1, h2⟩ := hφ
  have hiff : ∀ b : ↥Bs, φ b = b ↔ ψ (e b) = e b := fun b =>
    ⟨fun hb => by rw [← h, hb], fun hb => e.injective (by rw [h, hb])⟩
  have hc : Nat.card {b : ↥Bs // φ b = b} = Nat.card {b' : ↥Bs' // ψ b' = b'} :=
    Nat.card_congr (Equiv.subtypeEquiv e.toEquiv hiff)
  refine ⟨?_, ?_⟩
  · rw [← hc, ← Nat.card_congr e.toEquiv]
    exact h1
  · intro b'
    obtain ⟨b, rfl⟩ := e.surjective b'
    rw [← h b, ← map_inv e, ← map_mul e, ← h (b⁻¹ * φ b), h2 b]

theorem tv_descent {L' R : Type} [Group L'] [Finite L'] [Group R] {ψ : L' →* R}
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    (hperf : commutator L' = ⊤) {A : Subgroup (MulAut L')} (hA : CFSG.Open.IsElemAbelian 3 A)
    {I : Set (MulAut R)} (hAI : ∀ a ∈ A, ∃ x ∈ I, ∀ l : L', x (ψ l) = ψ (a l))
    (hsc : GGTorusSelfCent 3 A)
    (H : ∀ (L₁ : Type) [Group L₁] [Finite L₁] (ψ₁ : L₁ →* R), Function.Surjective ψ₁ →
      ψ₁.ker ≤ Subgroup.center L₁ → commutator L₁ = ⊤ → Odd (Nat.card ψ₁.ker) →
      ∀ A₁ : Subgroup (MulAut L₁), CFSG.Open.IsElemAbelian 3 A₁ →
        (∀ a ∈ A₁, ∃ x ∈ I, ∀ l : L₁, x (ψ₁ l) = ψ₁ (a l)) → Nat.card A₁ = Nat.card A →
        GGTorusSelfCent 3 A₁ → ∀ α₁ : Subgroup.normalizer (A₁ : Set (MulAut L₁)),
          (∃ φ : MulAut R, ∀ l : L₁, φ (ψ₁ l) = ψ₁ ((α₁ : MulAut L₁) l)) →
          ¬ GGIsTransvection 3 (A₁.normalizerMonoidHom α₁))
    (α : Subgroup.normalizer (A : Set (MulAut L')))
    (hα : ∃ φ : MulAut R, ∀ l : L', φ (ψ l) = ψ ((α : MulAut L') l)) :
    ¬ GGIsTransvection 3 (A.normalizerMonoidHom α) := by
  classical
  have hAle : A ≤ presZ (twoSub ψ.ker hker) := fun a ha =>
    mem_presZ_of_ker hker fun z hz => preserves_ker (hAI a ha) hz
  obtain ⟨φ, hφ⟩ := hα
  have hαZ : (α : MulAut L') ∈ presZ (twoSub ψ.ker hker) := by
    apply mem_presZ_of_ker hker
    intro z hz
    rw [MonoidHom.mem_ker, ← hφ z, MonoidHom.mem_ker.mp hz, map_one]
  set αP : presZ (twoSub ψ.ker hker) := ⟨(α : MulAut L'), hαZ⟩ with hαP
  set α₁ : MulAut (L' ⧸ twoSub ψ.ker hker) := redHom (twoSub ψ.ker hker) αP with hα₁
  set A₁ : Subgroup (MulAut (L' ⧸ twoSub ψ.ker hker)) := (redSub hker hAle).range with hA₁
  have hconj : ∀ b : A, (α : MulAut L') * (b : MulAut L') * (α : MulAut L')⁻¹ ∈ A :=
    fun b => (Subgroup.mem_normalizer_iff.mp α.2 (b : MulAut L')).mp b.2
  have key : ∀ b : A, α₁ * redSub hker hAle b * α₁⁻¹ =
      redSub hker hAle ⟨(α : MulAut L') * (b : MulAut L') * (α : MulAut L')⁻¹, hconj b⟩ := by
    intro b
    have e1 : redSub hker hAle ⟨(α : MulAut L') * (b : MulAut L') * (α : MulAut L')⁻¹,
        hconj b⟩ = redHom (twoSub ψ.ker hker) (αP * ⟨(b : MulAut L'), hAle b.2⟩ * αP⁻¹) :=
      rfl
    rw [e1, map_mul, map_mul, map_inv]
    rfl
  haveI : Finite (MulAut (L' ⧸ twoSub ψ.ker hker)) :=
    Finite.of_injective (fun φ : MulAut (L' ⧸ twoSub ψ.ker hker) =>
      (φ : L' ⧸ twoSub ψ.ker hker → L' ⧸ twoSub ψ.ker hker)) DFunLike.coe_injective
  have hα₁N : α₁ ∈ Subgroup.normalizer (A₁ : Set (MulAut (L' ⧸ twoSub ψ.ker hker))) := by
    refine Subgroup.mem_normalizer_fintype fun a₁ ha₁ => ?_
    obtain ⟨b, rfl⟩ := ha₁
    rw [key b]
    exact ⟨⟨_, hconj b⟩, rfl⟩
  set α₁' : Subgroup.normalizer (A₁ : Set (MulAut (L' ⧸ twoSub ψ.ker hker))) :=
    ⟨α₁, hα₁N⟩ with hα₁'
  have hinj := redSub_injective hker hAle hperf
  let e : ↥A ≃* ↥A₁ := MonoidHom.ofInjective hinj
  have hTrel : ∀ b : ↥A, e (A.normalizerMonoidHom α b) = A₁.normalizerMonoidHom α₁' (e b) := by
    intro b
    apply Subtype.ext
    have hTb : A.normalizerMonoidHom α b =
        ⟨(α : MulAut L') * (b : MulAut L') * (α : MulAut L')⁻¹, hconj b⟩ :=
      Subtype.ext (Subgroup.normalizerMonoidHom_apply_apply_coe A α b)
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe A₁ α₁' (e b)]
    show redSub hker hAle (A.normalizerMonoidHom α b) = α₁ * redSub hker hAle b * α₁⁻¹
    rw [hTb, key b]
  have hφ₁ : ∀ l : L' ⧸ twoSub ψ.ker hker,
      φ (psi1 hker l) = psi1 hker ((α₁' : MulAut (L' ⧸ twoSub ψ.ker hker)) l) := by
    intro l
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective l
    rw [psi1_mk]
    show φ (ψ l) = psi1 hker (α₁ (l : L' ⧸ twoSub ψ.ker hker))
    rw [hα₁, redHom_mk (twoSub ψ.ker hker) αP l, psi1_mk]
    exact hφ l
  intro hTr
  exact H (L' ⧸ twoSub ψ.ker hker) (psi1 hker) (psi1_surjective hker hψ)
    (psi1_ker_central hker) (commutator_quot hker hperf) (odd_card_ker_psi1 hker) A₁
    (isElemAbelian_range_redSub hker hAle hA) (redSub_hAI hker hAle hAI)
    (card_range_redSub hker hAle hperf) (selfCent_quot hker hA hAle hsc) α₁' ⟨φ, hφ₁⟩
    (ggIsTransvection_transport e hTrel hTr)

end CFSG.StandardType.UnitTvQ2

end
