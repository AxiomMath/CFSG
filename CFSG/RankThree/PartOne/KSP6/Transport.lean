module

public import CFSG.RankThree.PartOne.AUTSL.KF1514S0
public import CFSG.RankThree.PartOne.S9.Sylow.GlobalBridge

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory

namespace KSP6

open AUTSL

theorem kf1514PAutGen_of_mulEquiv {L L' : Type} [Group L] [Group L'] [Finite L] [Finite L']
    (e : L ≃* L') {p : ℕ} (hp : p.Prime) (h : KF1514PAutGen L' p) : KF1514PAutGen L p := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (MulAut L) :=
    Finite.of_injective (fun α : MulAut L => (α : L → L)) fun _ _ h => MulEquiv.ext (congrFun h)
  have : Finite (MulAut L') :=
    Finite.of_injective (fun α : MulAut L' => (α : L' → L')) fun _ _ h => MulEquiv.ext (congrFun h)
  intro H A₀ hInnH hA₀Inn hel hcard
  let Φ : MulAut L ≃* MulAut L' := MulAut.congr e
  let Ψ : MulAut L' →* MulAut L := Φ.symm.toMonoidHom
  have hΨinj : Function.Injective Ψ := Φ.symm.injective
  have hΦconj : ∀ x : L, Φ (MulAut.conj x) = MulAut.conj (e x) := by
    intro x
    ext z
    simp [Φ, MulAut.congr_apply, MulAut.conj_apply]
  have hconjrange : ∀ x' : L', (MulAut.conj x' : MulAut L') = Φ (MulAut.conj (e.symm x')) := by
    intro x'
    rw [hΦconj]
    simp
  have hH : (MulAut.conj : L' →* MulAut L').range ≤ H.map Φ.toMonoidHom := by
    rintro _ ⟨x', rfl⟩
    exact ⟨MulAut.conj (e.symm x'), hInnH ⟨e.symm x', rfl⟩, (hconjrange x').symm⟩
  have hA : A₀.map Φ.toMonoidHom ≤ (MulAut.conj : L' →* MulAut L').range := by
    rintro _ ⟨a, ha, rfl⟩
    obtain ⟨x, rfl⟩ := hA₀Inn ha
    exact ⟨e x, (hΦconj x).symm⟩
  have : IsElementaryAbelian p ↥A₀ := hel
  have hel' : IsElementaryAbelian p ↥(A₀.map Φ.toMonoidHom) := IsElementaryAbelian.map _
  have hcard' : Nat.card ↥(A₀.map Φ.toMonoidHom) = p ^ 3 := by
    rw [Subgroup.card_map_of_injective Φ.injective, hcard]
  obtain ⟨T', hT', ⟨B₁, hB₁A, hB₁c, hB₁n⟩, ⟨x', hx', hx'1, B₂, hB₂A, hB₂c, hB₂n⟩⟩ :=
    h _ _ hH hA hel' hcard'
  have hmm : ∀ K : Subgroup (MulAut L), (K.map Φ.toMonoidHom).map Ψ = K := by
    intro K
    ext z
    simp only [Subgroup.mem_map]
    constructor
    · rintro ⟨_, ⟨k, hk, rfl⟩, rfl⟩
      simpa [Ψ] using hk
    · intro hz
      exact ⟨Φ z, ⟨z, hz, rfl⟩, by simp [Ψ]⟩
  have hinjT : Function.Injective (Ψ.comp T'.subtype) := hΨinj.comp T'.subtype_injective
  have hS : (pushingUpS T').map Ψ = pushingUpS (T'.map Ψ) := U5K.map_pushingUpS Ψ hinjT
  have hΩ : (omegaOneCenterIn T').map Ψ = omegaOneCenterIn (T'.map Ψ) :=
    Sec1514Five.map_omegaOneCenterIn Ψ hinjT
  have hAB : ∀ B : Subgroup (MulAut L'), B ≤ A₀.map Φ.toMonoidHom → B.map Ψ ≤ A₀ := by
    intro B hB
    calc B.map Ψ ≤ (A₀.map Φ.toMonoidHom).map Ψ := Subgroup.map_mono hB
      _ = A₀ := hmm A₀
  refine ⟨T'.map Ψ, ?_, ⟨B₁.map Ψ, hAB B₁ hB₁A, ?_, ?_⟩,
    ⟨Ψ x', ?_, ?_, B₂.map Ψ, hAB B₂ hB₂A, ?_, ?_⟩⟩
  · have := Sec9B.isSylowOf_map hΨinj hT'
    rwa [hmm H] at this
  · rw [Subgroup.card_map_of_injective hΨinj]
    exact (Subgroup.card_map_of_injective Φ.injective).symm.le.trans hB₁c
  · rw [← hS]
    intro b hb
    have h1 : Subgroup.normalizer ((pushingUpS T').map Ψ : Set (MulAut L)) =
        (Subgroup.normalizer (pushingUpS T' : Set (MulAut L'))).map Ψ :=
      (Subgroup.map_equiv_normalizer_eq (pushingUpS T') Φ.symm).symm
    rw [h1]
    exact Subgroup.map_mono hB₁n hb
  · rw [← hΩ]
    exact Subgroup.mem_map_of_mem Ψ hx'
  · intro h1
    exact hx'1 (hΨinj (h1.trans (map_one Ψ).symm))
  · rw [Subgroup.card_map_of_injective hΨinj]
    exact (Subgroup.card_map_of_injective Φ.injective).symm.le.trans hB₂c
  · rintro _ ⟨b, hb, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    subst hw
    have := Subgroup.mem_centralizer_iff.1 (hB₂n hb) x' rfl
    have h2 : Ψ (x' * b) = Ψ (b * x') := by rw [this]
    rw [map_mul, map_mul] at h2
    exact h2

end KSP6

end CFSG.RankThree.PartOne
