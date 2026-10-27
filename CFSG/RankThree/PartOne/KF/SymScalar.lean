module

public import CFSG.RankThree.PartOne.KF.SymCtx

public section

namespace CFSG.RankThree.PartOne.KFU

open Equiv

section Main

variable {n p : ℕ} {K : Type} [Field K]

theorem exists_symAut_mul_pow_of_symNormalizer [Finite K] (hp : p.Prime) (hp2 : p ≠ 2)
    (hn : 3 ≤ n) (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p)
    (hinner : ∀ α : Perm (Fin n) →* Perm (Fin n), Function.Injective α →
      (∀ a b : Fin n, a ≠ b → ∃ c d : Fin n, c ≠ d ∧ α (Equiv.swap a b) = Equiv.swap c d) →
      ∃ π : Perm (Fin n), ∀ σ, α σ = π * σ * π⁻¹)
    (φ : MulAut (torusVec p n K))
    (hnorm : ∀ σ : Perm (Fin n), ∃ τ : Perm (Fin n), φ * symAut p K σ * φ⁻¹ = symAut p K τ) :
    ∃ (π : Perm (Fin n)) (e : ℕ), ∀ d, φ d = (symAct p K π d) ^ e := by
  classical
  have hinj := symAut_injective (n := n) (K := K) hp hp2 hζ
  choose α hα using hnorm
  let αh : Perm (Fin n) →* Perm (Fin n) :=
    { toFun := α
      map_one' := hinj (by rw [← hα 1, map_one, mul_one, mul_inv_cancel])
      map_mul' := fun σ τ => hinj (by
        rw [map_mul (symAut p K) (α σ) (α τ), ← hα σ, ← hα τ, ← hα (σ * τ), map_mul]
        group) }
  have hαinj : Function.Injective αh := by
    rw [injective_iff_map_eq_one]
    intro σ hσ
    apply hinj
    have h1 := hα σ
    have h2 : α σ = 1 := hσ
    rw [h2, map_one] at h1
    rw [map_one]
    calc symAut p K σ = φ⁻¹ * (φ * symAut p K σ * φ⁻¹) * φ := by group
      _ = 1 := by rw [h1]; group
  have hαtrans : ∀ a b : Fin n, a ≠ b → ∃ c d : Fin n, c ≠ d ∧
      α (Equiv.swap a b) = Equiv.swap c d := by
    intro a b hab
    have hsw1 : Equiv.swap a b * Equiv.swap a b = 1 := Equiv.swap_mul_self a b
    have hτ1 : α (Equiv.swap a b) * α (Equiv.swap a b) = 1 := by
      have : αh (Equiv.swap a b * Equiv.swap a b) = 1 := by rw [hsw1, map_one]
      rw [map_mul] at this
      exact this
    have hτne : α (Equiv.swap a b) ≠ 1 := by
      intro h
      have : αh (Equiv.swap a b) = αh 1 := by rw [map_one]; exact h
      have := hαinj this
      have h2 := congrArg (fun τ : Perm (Fin n) => τ a) this
      simp [Equiv.swap_apply_left] at h2
      exact hab h2.symm
    have hmoved : movedSub p K (α (Equiv.swap a b)) = (movedSub p K (Equiv.swap a b)).map
        φ.toMonoidHom := by
      unfold movedSub
      rw [MonoidHom.map_closure]
      congr 1
      ext x
      constructor
      · rintro ⟨d, rfl⟩
        refine ⟨symAct p K (Equiv.swap a b) (φ.symm d) * (φ.symm d)⁻¹, ⟨φ.symm d, rfl⟩, ?_⟩
        have h1 := congrArg (fun m : MulAut (torusVec p n K) => m d) (hα (Equiv.swap a b))
        simp only [MulAut.mul_apply, MulAut.inv_apply, symAut_apply] at h1
        show φ (symAct p K (Equiv.swap a b) (φ.symm d) * (φ.symm d)⁻¹) = _
        rw [map_mul, map_inv, MulEquiv.apply_symm_apply]
        have h2 : φ (symAct p K (Equiv.swap a b) (φ.symm d)) =
            symAct p K (α (Equiv.swap a b)) d := by
          rw [← h1]
        rw [h2]
      · rintro ⟨_, ⟨d, rfl⟩, rfl⟩
        refine ⟨φ d, ?_⟩
        have h1 := congrArg (fun m : MulAut (torusVec p n K) => m (φ d)) (hα (Equiv.swap a b))
        simp only [MulAut.mul_apply, MulAut.inv_apply, symAut_apply, MulEquiv.symm_apply_apply]
          at h1
        show symAct p K (α (Equiv.swap a b)) (φ d) * (φ d)⁻¹ =
          φ (symAct p K (Equiv.swap a b) d * d⁻¹)
        rw [map_mul, map_inv, ← h1]
    have hcardτ : Nat.card (movedSub p K (α (Equiv.swap a b))) = p := by
      rw [hmoved, Subgroup.card_map_of_injective φ.injective]
      exact card_movedSub_swap hp hp2 hζ hab
    rcases involution_cases _ hτ1 hτne with ⟨c, d, hcd, h⟩ | ⟨a', b', c', d', hab', hac', hada,
        hbc', hbd', hcd', h1, h2, h3, h4⟩
    · exact ⟨c, d, hcd, h⟩
    · exact absurd hcardτ (card_movedSub_ne_prime_of_double_swap hp hp2 hζ _ hab' hac' hbc' hcd'
        h1 h2 h3 h4)
  obtain ⟨π, hπ⟩ := hinner αh hαinj hαtrans
  set φ' : MulAut (torusVec p n K) := (symAut p K π)⁻¹ * φ with hφ'def
  have hφdef : φ = symAut p K π * φ' := by rw [hφ'def, mul_inv_cancel_left]
  have hcomm : ∀ σ, φ' * symAut p K σ = symAut p K σ * φ' := by
    intro σ
    have h1 := hα σ
    have h2 : α σ = π * σ * π⁻¹ := hπ σ
    rw [h2, map_mul, map_mul, map_inv] at h1
    calc (symAut p K π)⁻¹ * φ * symAut p K σ
        = (symAut p K π)⁻¹ * (φ * symAut p K σ * φ⁻¹) * φ := by group
      _ = (symAut p K π)⁻¹ * (symAut p K π * symAut p K σ * (symAut p K π)⁻¹) * φ := by rw [h1]
      _ = symAut p K σ * ((symAut p K π)⁻¹ * φ) := by group
  obtain ⟨e, he⟩ := exists_pow_of_commutes hp hp2 (by omega) hζ φ' hcomm
  refine ⟨π, e, fun d => ?_⟩
  rw [hφdef, MulAut.mul_apply, he, symAut_apply, map_pow]

end Main

namespace SymCtx

variable {G : Type} [Group G] {p n : ℕ} {K : Type} [Field K] {L F : Subgroup G}
  (S : SymCtx p n K L F)

include S in
theorem exists_scalar_of_normalizes [Finite K] (hp : p.Prime) (hp2 : p ≠ 2) (hn : 3 ≤ n)
    (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p)
    (hinner : ∀ α : Equiv.Perm (Fin n) →* Equiv.Perm (Fin n), Function.Injective α →
      (∀ a b : Fin n, a ≠ b → ∃ c d : Fin n, c ≠ d ∧ α (Equiv.swap a b) = Equiv.swap c d) →
      ∃ π : Equiv.Perm (Fin n), ∀ σ, α σ = π * σ * π⁻¹)
    {y : G} (hyL : y ∈ Subgroup.normalizer (L : Set G)) (hyF : y ∈ Subgroup.normalizer (F : Set G)) :
    ∃ (l : G) (hlF : l ∈ Subgroup.normalizer (F : Set G)), l ∈ L ∧ ∃ e : ℕ, ∀ f : F,
      ((F.normalizerMonoidHom ⟨l, hlF⟩ * F.normalizerMonoidHom ⟨y, hyF⟩) f : F) = f ^ e := by
  set φ : MulAut F := F.normalizerMonoidHom ⟨y, hyF⟩ with hφdef
  let φV : MulAut (torusVec p n K) := (MulAut.congr S.tor).symm φ
  have hnorm : ∀ σ : Equiv.Perm (Fin n), ∃ τ : Equiv.Perm (Fin n),
      φV * symAut p K σ * φV⁻¹ = symAut p K τ := by
    intro σ
    obtain ⟨g, hg, hgL, hgσ⟩ := S.exists_elt σ
    have hywL : y * g * y⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hyL _).mp hgL
    have hywF : y * g * y⁻¹ ∈ Subgroup.normalizer (F : Set G) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hyF hg) (Subgroup.inv_mem _ hyF)
    obtain ⟨τ, hτ⟩ := S.induced _ hywF hywL
    refine ⟨τ, ?_⟩
    have h1 : φ * MulAut.congr S.tor (symAut p K σ) * φ⁻¹ = MulAut.congr S.tor (symAut p K τ) := by
      rw [← hτ, ← hgσ]
      have : (⟨y * g * y⁻¹, hywF⟩ : Subgroup.normalizer (F : Set G)) =
          ⟨y, hyF⟩ * ⟨g, hg⟩ * ⟨y, hyF⟩⁻¹ := rfl
      rw [this, map_mul, map_mul, map_inv]
    have h2 := congrArg (MulAut.congr S.tor).symm h1
    rw [map_mul, map_mul, map_inv, MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply] at h2
    exact h2
  obtain ⟨π, e, hπe⟩ := exists_symAut_mul_pow_of_symNormalizer hp hp2 hn hζ hinner φV hnorm
  obtain ⟨l, hlF, hlL, hlπ⟩ := S.exists_elt π⁻¹
  refine ⟨l, hlF, hlL, e, fun f => ?_⟩
  obtain ⟨d, rfl⟩ := S.tor.surjective f
  rw [MulAut.mul_apply, hlπ]
  have h3 : φ (S.tor d) = S.tor (φV d) := by
    rw [← SymCtx.congr_apply_tor, MulEquiv.apply_symm_apply]
  have h4 : (MulAut.congr S.tor (symAut p K π⁻¹)) (S.tor ((symAct p K π d) ^ e)) =
      (S.tor d) ^ e := by
    rw [SymCtx.congr_apply_tor, symAut_apply, map_pow, ← symAct_mul, inv_mul_cancel, symAct_one,
      map_pow]
  rw [h3, hπe d]
  exact h4

end SymCtx

end CFSG.RankThree.PartOne.KFU
