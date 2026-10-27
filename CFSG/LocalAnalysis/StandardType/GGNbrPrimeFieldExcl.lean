module

public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL45
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL4546Defs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggNbr_not_primeField (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {G : Type} [Group G] {Bs K : Subgroup G} {x : G}
    (hx : x ∈ Bs) (hInn : GGInnerDiagOn Bs K) :
    ¬ LargeEvenMarking ↥K (fun lab _ _ I F θ =>
      LargeEvenPrimeField p lab I F (LargeEvenInduces θ fun j j' => (j' : G) = x⁻¹ * j * x)) := by
  intro hPF
  have hInn₁ := largeEvenMarking_and_labelAll (S := fun _ => True) (P' := GGRawInnField p)
    (fun lab hl _ => hraw p hp hp2 lab hl) (fun _ _ _ _ _ _ _ => trivial) hInn
  have hInn₂ := largeEvenMarking_and_labelAll_simple (S := fun _ => True)
    (P' := GGRawInndiagIso) (fun lab hl _ => hiso lab hl)
    (fun _ _ _ _ _ _ _ => trivial) hInn₁
  obtain ⟨-, lab₁, -, hraw₁⟩ := hInn₂
  obtain ⟨R₁, _, I₁, F₁, hs₁, hna₁, θ₁, ⟨hInnOn₁, hRIF₁⟩, hiso₁⟩ :=
    largeEvenRawDatum_exists hraw₁
  have hPF₁ := largeEvenMarking_and_labelAll (S := fun _ => True) (P' := GGRawInnField p)
    (fun lab hl _ => hraw p hp hp2 lab hl) (fun _ _ _ _ _ _ _ => trivial) hPF
  have hPF₂ := largeEvenMarking_and_labelAll_simple (S := fun _ => True)
    (P' := fun R _ I _ => ∀ (σ : R₁ ≃* R) (φ : MulAut R₁),
      φ ∈ ggInndiag R₁ I₁ ↔ MulAut.congr σ φ ∈ ggInndiag R I)
    (fun lab hl _ => hiso₁ lab hl) (fun _ _ _ _ _ _ _ => trivial) hPF₁
  obtain ⟨-, lab₅, -, hraw₅⟩ := hPF₂
  obtain ⟨R₅, _, I₅, F₅, hs₅, hna₅, θ₅, ⟨⟨hPF₅, hRIF₅⟩, hiso₅⟩⟩ :=
    largeEvenRawDatum_exists hraw₅
  obtain ⟨φ₁, hφ₁, hind₁⟩ := hInnOn₁.2 x hx
  obtain ⟨-, f, hf, u, hu, hord, hind₅⟩ := hPF₅
  let σ : R₁ ≃* R₅ := θ₁.symm.trans θ₅
  have hcongr : MulAut.congr σ φ₁ = u * f * u⁻¹ := by
    ext r
    obtain ⟨q, rfl⟩ := θ₅.surjective r
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
    have hmem : x⁻¹ * (k : G) * x ∈ K :=
      (Subgroup.mem_normalizer_iff''.mp (hInnOn₁.1 hx) (k : G)).mp k.2
    let k' : ↥K := ⟨x⁻¹ * (k : G) * x, hmem⟩
    have h1 : φ₁ (θ₁ (QuotientGroup.mk k)) = θ₁ (QuotientGroup.mk k') := hind₁ k k' rfl
    have h2 : (u * f * u⁻¹) (θ₅ (QuotientGroup.mk k)) = θ₅ (QuotientGroup.mk k') :=
      hind₅ k k' rfl
    have hσ : σ.symm (θ₅ (QuotientGroup.mk k)) = θ₁ (QuotientGroup.mk k) := by simp [σ]
    rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply, hσ, h1, h2]
    simp [σ]
  obtain ⟨hmul₅, hinv₅, hinn₅, hF₅⟩ := hRIF₅ hs₅ hna₅
  have hmem₅ : u * f * u⁻¹ ∈ I₅ := by
    have hgg : MulAut.congr σ φ₁ ∈ ggInndiag R₅ I₅ :=
      (hiso₅ σ φ₁).mp (subset_ggInndiag hφ₁)
    rw [hcongr] at hgg
    exact (ggL45_mem_ggInndiag_iff hmul₅ hinv₅ hinn₅).mp hgg
  have hfI : f ∈ I₅ := by
    have h2 : u⁻¹ * (u * f * u⁻¹) ∈ I₅ := hmul₅ u⁻¹ (hinv₅ u hu) (u * f * u⁻¹) hmem₅
    have h3 : u⁻¹ * (u * f * u⁻¹) * u ∈ I₅ := hmul₅ (u⁻¹ * (u * f * u⁻¹)) h2 u hu
    rwa [show u⁻¹ * (u * f * u⁻¹) * u = f by group] at h3
  exact (hF₅ f hf hord) hfI

end CFSG.StandardType

end
