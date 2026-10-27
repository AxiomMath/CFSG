module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.Statement
public import CFSG.Quasithin.Background.B4Models
import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.Base8Nat

public section

namespace CFSG.LocalAnalysis.WeakClosure81.GF2Reps86

open CFSG.Quasithin CFSG.RankThree.PartTwo CFSG.HardMathSupport.Cooperstein.Coordinator
  CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive Equiv

variable {V : Type} [CommGroup V] {H : Subgroup (MulAut V)} {n : ℕ} {ψ : ↥H →* Perm (Fin n)}

theorem alternatingNatural_of_natVia [Finite V] (hn5 : 5 ≤ n) (hψ : Function.Injective ψ)
    (hA : alternatingGroup (Fin n) ≤ ψ.range) (hfix : fixV (altPre ψ) = ⊥) (h : NatVia ψ ⊤) :
    AlternatingNatural (altPre ψ) ⊤ ⊥ n := by
  obtain ⟨π, hπs, hπk, hπe⟩ := h
  set K : Subgroup ↥(G6.coreMod n) :=
    (Subgroup.zpowers (G6.allOnes n) ⊓ G6.coreMod n).subgroupOf (G6.coreMod n)
  have hKle : ∀ m ∈ K, coreHeart n m = 1 := fun m hm =>
    (coreHeart_eq_one_iff (by omega) m).2 hm
  let Φ₀ : (↥(G6.coreMod n) ⧸ K) →* Multiplicative (altHeart n) :=
    QuotientGroup.lift K (coreHeart n) hKle
  have hΦ₀mk : ∀ m, Φ₀ (QuotientGroup.mk m) = coreHeart n m := fun m => rfl
  have hΦ₀inj : Function.Injective Φ₀ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective x
    rw [hΦ₀mk] at hx
    exact (QuotientGroup.eq_one_iff m).2 ((coreHeart_eq_one_iff (by omega) m).1 hx)
  have hΦ₀surj : Function.Surjective Φ₀ := by
    intro y
    obtain ⟨m, hm⟩ := coreHeart_surjective n y
    exact ⟨QuotientGroup.mk m, by rw [hΦ₀mk, hm]⟩
  let e : (↥(G6.coreMod n) ⧸ K) ≃* Multiplicative (altHeart n) :=
    MulEquiv.ofBijective Φ₀ ⟨hΦ₀inj, hΦ₀surj⟩
  have he : ∀ m, e (QuotientGroup.mk m) = coreHeart n m := fun m => rfl
  have hker : ∀ u : ↥(⊤ : Subgroup V), π u = 1 ↔ (u : V) ∈ (⊥ : Subgroup V) := fun u => by
    rw [← MonoidHom.mem_ker, hπk, Subgroup.mem_subgroupOf, hfix, inf_bot_eq]
  have hone : ∀ γ : Perm (Fin n), G6.permAct n γ (G6.allOnes n) = G6.allOnes n := fun γ => by
    apply Multiplicative.toAdd.injective
    funext i
    simp [G6.permAct_apply, G6.allOnes]
  have hsec : ∀ γ : alternatingGroup (Fin n), ∀ m ∈ G6.coreMod n,
      G6.permAct n (γ : Perm (Fin n)) m ∈ G6.coreMod n := fun γ _ hm =>
    G6.permAct_mem_coreMod (γ : Perm (Fin n)) hm
  have hkerinv : ∀ γ : alternatingGroup (Fin n), ∀ m ∈ Subgroup.zpowers (G6.allOnes n) ⊓
      G6.coreMod n, G6.permAct n (γ : Perm (Fin n)) m ∈
        Subgroup.zpowers (G6.allOnes n) ⊓ G6.coreMod n := by
    rintro γ m ⟨hz, hcore⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    refine ⟨Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩, G6.permAct_mem_coreMod (γ : Perm (Fin n)) hcore⟩
    rw [map_zpow, hone]
    rfl
  refine ⟨(altPreEquiv hψ hA).symm.toMonoidHom, (altPreEquiv hψ hA).symm.surjective, bot_le,
    inf_le_right, fun _ _ _ => Subgroup.mem_top _, fun g z hz => ?_, hsec, hkerinv,
    e.symm.toMonoidHom.comp π, e.symm.surjective.comp hπs, fun u => ?_, ?_⟩
  · rw [Subgroup.mem_bot] at hz ⊢
    rw [hz]
    exact map_one _
  · change e.symm (π u) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff, hker]
  · intro (γ : alternatingGroup (Fin n)) u (m : ↥(G6.coreMod n)) hu hm hβ
    change e.symm (π u) = QuotientGroup.mk m at hβ
    change e.symm (π ⟨_, hu⟩) =
      QuotientGroup.mk (⟨G6.permAct n (γ : Perm (Fin n)) m, hm⟩ : ↥(G6.coreMod n))
    rw [MulEquiv.symm_apply_eq, he]
    have h1 : π u = coreHeart n m := by
      rw [← he, ← hβ, MulEquiv.apply_symm_apply]
    have hψγ : ψ (Subgroup.inclusion altPre_le ((altPreEquiv hψ hA).symm γ)) =
        (γ : Perm (Fin n)) := by
      rw [← coe_altPreEquiv hψ hA, MulEquiv.apply_symm_apply]
    have h2 := hπe (Subgroup.inclusion altPre_le ((altPreEquiv hψ hA).symm γ)) u ⟨_, hu⟩ rfl
    rw [hψγ] at h2
    apply Multiplicative.toAdd.injective
    rw [h2, h1]
    exact (toAdd_coreHeart_permAct (γ : Perm (Fin n)) m).symm

end CFSG.LocalAnalysis.WeakClosure81.GF2Reps86

end
