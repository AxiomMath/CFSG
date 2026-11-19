module

public import CFSG.LocalAnalysis.StandardType.GGTBJSympMinusModel
public import CFSG.LocalAnalysis.StandardType.GGTBJSympMinusBlock
public import CFSG.LocalAnalysis.StandardType.GGTBJSympMinusA6

public section

namespace CFSG.StandardType.SympMinus

open CFSG.Open CFSG.Assembly CFSG.HardMathSupport.Solomon.Coordinator

abbrev BlockCases {p m : ℕ} {L' : Type} [Group L']
    (σ : (Fin m → Multiplicative (ZMod p)) →* L') (J : Subgroup L') : Prop :=
  (∃ S : Finset (Fin m), 1 ≤ S.card ∧
    FrameBs.sectionFrameAut σ J = TypeBDatum.signedSupportedAut m p S ∧
    (∀ f : Fin m → Multiplicative (ZMod p),
      (∀ τ ∈ FrameBs.sectionFrameAut σ J, τ f = f) → ∀ j ∈ J, σ f * j = j * σ f) ∧
    (S.card = m → J = ⊤)) ∨
  (∃ (S : Finset (Fin m)) (s : Fin m → ZMod p) (hs : ∀ i, s i * s i = 1), 2 ≤ S.card ∧
    FrameBs.sectionFrameAut σ J = TypeBDatum.twistedPermAut m p S s hs ∧
    ∀ f : Fin m → Multiplicative (ZMod p),
      (∀ τ ∈ FrameBs.sectionFrameAut σ J, τ f = f) → ∀ j ∈ J, σ f * j = j * σ f)

theorem ggTBJ_sympMinus_frame
    {p m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) [NeZero m] {K : Type}
    [Field K] [Finite K] [CharP K 2] (hq : 4 ≤ Nat.card K ∨ Nat.card K = 2) (hm3 : 3 ≤ m)
    (hpq : p ∣ Nat.card K + 1) {L' : Type} [Group L'] [Finite L']
    (ψ₀ : L' →* LargeEvenProj (LargeEvenSpGroup K m)) (hψ : Function.Surjective ψ₀)
    (hker : ψ₀.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    (A : Subgroup (MulAut L')) (hAe : IsElemAbelian p A)
    (hAI : ∀ a ∈ A, ∃ φ ∈ Set.range (MulAut.conj : LargeEvenProj (LargeEvenSpGroup K m) →*
        MulAut (LargeEvenProj (LargeEvenSpGroup K m))), ∀ l : L', φ (ψ₀ l) = ψ₀ (a l))
    (hsc : GGTorusSelfCent p A) :
    ∃ (σ : (Fin m → Multiplicative (ZMod p)) →* L')
      (Θ : (Fin m → Multiplicative (ZMod p)) ≃* ↥A),
      (∀ f, ((Θ f : ↥A) : MulAut L') = MulAut.conj (σ f)) ∧
      FrameBs.sectionFrameAut σ ⊤ = TypeBDatum.signedAut m p ∧
      ∀ (y : MulAut L') (_ : y ∈ A) (J : Subgroup L'),
        CFSG.Open.IsComponentOf J (fixSubgroup y) → BlockCases σ J ∨
          (Nat.card K = 2 ∧ ∃ f₀ : Fin m → Multiplicative (ZMod p),
            y = MulAut.conj (σ f₀) ∧ SympA6Frame ψ₀ σ J f₀) := by
  obtain ⟨ζ, σ, Θ, hζ, hζW, hΘσ, -, x, hψσ, hmod⟩ :=
    ggTBJ_spPlane_model hp hp2 hpq ψ₀ hψ hker hperf A hAe hAI hsc
  refine ⟨σ, Θ, hΘσ, ?_, fun y hy J hJ => ?_⟩
  · obtain ⟨J₀, -, hsec, -, htop, -⟩ := hmod 1 A.one_mem ⊤
    rw [hsec, (htop.mpr rfl : J₀ = ⊤)]
    exact sympMinus_frameAut_top hp hp2 hζ hζW
  · obtain ⟨J₀, hJ₀, hsec, hcen, htop, hrel⟩ := hmod y hy J
    rcases sympMinus_block hq (fun _ => hm3) hp hp2 hpq hζ hζW _ (hJ₀ hJ) with
      ⟨S, hS, hA1, hA2, hA3⟩ | ⟨S, s, hs, hS, hA1, hA2⟩ | ⟨hK2, f, hblocks, hd, hJ₀eq⟩
    · refine Or.inl (Or.inl ⟨S, hS, hsec.trans hA1, fun f hf j hj => ?_,
        fun hSm => htop.mp (hA3 hSm)⟩)
      exact (hcen f).mp (hA2 f (fun τ hτ => hf τ (hsec ▸ hτ))) j hj
    · refine Or.inl (Or.inr ⟨S, s, hs, hS, hsec.trans hA1, fun f hf j hj => ?_⟩)
      exact (hcen f).mp (hA2 f (fun τ hτ => hf τ (hsec ▸ hτ))) j hj
    · refine Or.inr ⟨hK2, Θ.symm ⟨y, hy⟩, ?_, ζ, x, J₀, f, hψσ, hrel, hblocks, hd, hJ₀eq⟩
      have h := hΘσ (Θ.symm ⟨y, hy⟩)
      rw [show Θ (Θ.symm ⟨y, hy⟩) = ⟨y, hy⟩ from MulEquiv.apply_symm_apply Θ _] at h
      exact h

end CFSG.StandardType.SympMinus

end
