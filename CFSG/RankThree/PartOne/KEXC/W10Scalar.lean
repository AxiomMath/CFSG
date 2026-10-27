module

public import CFSG.RankThree.PartOne.KF.SymScalar
public import CFSG.RankThree.PartOne.KF.W10Ctx
public import CFSG.RankThree.PartOne.KF.D8Normalizer

public section

namespace CFSG.RankThree.PartOne.KEXC

open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KFU

variable {p : ℕ} {K : Type} [Field K]

theorem eq_one_of_sq_of_pow_of_odd {x : Kˣ} (hp : Odd p) (hx : x ^ 2 = 1) (hxp : x ^ p = 1) :
    x = 1 := by
  obtain ⟨k, rfl⟩ := hp
  have : x ^ (2 * k + 1) = (x ^ 2) ^ k * x := by rw [pow_succ, pow_mul]
  rw [this, hx, one_pow, one_mul] at hxp
  exact hxp

theorem card_ker_movedHom_inv_swap_le [Finite K] (hp : p.Prime) (hp2 : p ≠ 2) {a b : Fin 4} :
    Nat.card (movedHom (act10 (p := p) (K := K)
      (Multiplicative.ofAdd 1, Equiv.swap a b))).ker ≤ Nat.card (rootsOfUnity p K) := by
  classical
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hfix : ∀ v : torusVec p 4 K, v ∈ (movedHom (act10 (p := p) (K := K)
      (Multiplicative.ofAdd 1, Equiv.swap a b))).ker →
        ∀ i : Fin 4, ((v : Fin 4 → Kˣ) (Equiv.swap a b i))⁻¹ = (v : Fin 4 → Kˣ) i := by
    intro v hv i
    rw [mem_ker_movedHom, act10_inv] at hv
    have := congrFun (congrArg Subtype.val hv) i
    simpa [coe_symAct] using this
  have hone : ∀ v : torusVec p 4 K, v ∈ (movedHom (act10 (p := p) (K := K)
      (Multiplicative.ofAdd 1, Equiv.swap a b))).ker → ∀ i : Fin 4, i ≠ a → i ≠ b →
        (v : Fin 4 → Kˣ) i = 1 := by
    intro v hv i hia hib
    have h1 := hfix v hv i
    rw [Equiv.swap_apply_of_ne_of_ne hia hib] at h1
    apply eq_one_of_sq_of_pow_of_odd hpodd _ (v.2.1 i)
    rw [sq]
    nth_rewrite 1 [← h1]
    exact inv_mul_cancel _
  have hb : ∀ v : torusVec p 4 K, v ∈ (movedHom (act10 (p := p) (K := K)
      (Multiplicative.ofAdd 1, Equiv.swap a b))).ker →
        (v : Fin 4 → Kˣ) b = ((v : Fin 4 → Kˣ) a)⁻¹ := by
    intro v hv
    have h1 := hfix v hv a
    rw [Equiv.swap_apply_left] at h1
    rw [← h1, inv_inv]
  let f : ↥(movedHom (act10 (p := p) (K := K)
      (Multiplicative.ofAdd 1, Equiv.swap a b))).ker → rootsOfUnity p K := fun v =>
    ⟨(v.1 : Fin 4 → Kˣ) a, (mem_rootsOfUnity p _).mpr (v.1.2.1 a)⟩
  have hf : Function.Injective f := by
    intro v w hvw
    have ha : (v.1 : Fin 4 → Kˣ) a = (w.1 : Fin 4 → Kˣ) a := congrArg Subtype.val hvw
    apply Subtype.ext
    apply Subtype.ext
    funext i
    by_cases hia : i = a
    · rw [hia]
      exact ha
    · by_cases hib : i = b
      · rw [hib, hb v.1 v.2, hb w.1 w.2, ha]
      · rw [hone v.1 v.2 i hia hib, hone w.1 w.2 i hia hib]
  exact Nat.card_le_card_of_injective f hf

theorem card_movedV_act10_neg_swap_ne [Finite K] (hp : p.Prime) (hp2 : p ≠ 2)
    (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p) {a b : Fin 4} :
    Nat.card (movedV (act10 (p := p) (K := K) (Multiplicative.ofAdd 1, Equiv.swap a b))) ≠ p := by
  intro h
  have h1 := card_movedV_mul_card_fixed
    (act10 (p := p) (K := K) (Multiplicative.ofAdd 1, Equiv.swap a b))
  have h2 := card_ker_movedHom_inv_swap_le (K := K) (a := a) (b := b) hp hp2
  rw [card_rootsOfUnity_eq' hp.pos hζ] at h2
  have hV : Nat.card (torusVec p 4 K) = p ^ 3 := card_torusVec_eq hp.pos hζ 3
  rw [h, hV] at h1
  have h3 : Nat.card (movedHom (act10 (p := p) (K := K)
      (Multiplicative.ofAdd 1, Equiv.swap a b))).ker = p ^ 2 := by
    have : p * Nat.card (movedHom (act10 (p := p) (K := K)
        (Multiplicative.ofAdd 1, Equiv.swap a b))).ker = p * p ^ 2 := by
      rw [h1]
      ring
    exact Nat.eq_of_mul_eq_mul_left hp.pos this
  rw [h3] at h2
  have hp2' := hp.two_le
  nlinarith

theorem exists_symAct_mul_pow_of_w10Normalizer [Finite K] (hp : p.Prime) (hp5 : 5 ≤ p)
    (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p)
    (hinner : ∀ α : Equiv.Perm (Fin 4) →* Equiv.Perm (Fin 4), Function.Injective α →
      ∃ π : Equiv.Perm (Fin 4), ∀ σ, α σ = π * σ * π⁻¹)
    (φ : MulAut (torusVec p 4 K))
    (hnorm : ∀ γ : W10, ∃ γ' : W10, φ * act10 γ * φ⁻¹ = act10 γ') :
    ∃ (π : Equiv.Perm (Fin 4)) (e : ℕ), ∀ d, φ d = (symAct p K π d) ^ e := by
  classical
  have hp2 : p ≠ 2 := by omega
  have hinj := act10_injective hp hp2 hζ
  choose α hα using hnorm
  have hαmul : ∀ γ δ, α (γ * δ) = α γ * α δ := fun γ δ => hinj (by
    rw [map_mul, ← hα γ, ← hα δ, ← hα (γ * δ), map_mul]
    group)
  have hα1 : α 1 = 1 := hinj (by
    rw [← hα 1, map_one]
    group)
  have hαinj : Function.Injective α := fun γ δ h => hinj (by
    have h1 := hα γ
    have h2 := hα δ
    rw [h] at h1
    rw [← h2] at h1
    exact mul_right_cancel (mul_left_cancel h1))
  let αh : W10 →* W10 := { toFun := α, map_one' := hα1, map_mul' := hαmul }
  let ι : Equiv.Perm (Fin 4) →* W10 := MonoidHom.inr _ _
  let ᾱ : Equiv.Perm (Fin 4) →* Equiv.Perm (Fin 4) := (MonoidHom.snd _ _).comp (αh.comp ι)
  let η : Equiv.Perm (Fin 4) →* Multiplicative (ZMod 2) := (MonoidHom.fst _ _).comp (αh.comp ι)
  have hαι : ∀ σ, α (1, σ) = (η σ, ᾱ σ) := fun σ => rfl
  have hcentral : ∀ (e : Multiplicative (ZMod 2)) (w : W10), (e, (1 : Equiv.Perm (Fin 4))) * w =
      w * (e, 1) := fun e w => by
    obtain ⟨e', σ'⟩ := w
    simp [Prod.mk_mul_mk, mul_comm]
  have hᾱinj : Function.Injective ᾱ := by
    rw [injective_iff_map_eq_one]
    intro σ hσ
    have hc : α (1, σ) = (η σ, 1) := by rw [hαι]; exact Prod.ext rfl hσ
    apply perm_four_center
    intro τ
    have h1 : α ((1, σ) * (1, τ)) = α ((1, τ) * (1, σ)) := by
      rw [hαmul, hαmul, hc]
      exact hcentral _ _
    have := hαinj h1
    simpa [Prod.mk_mul_mk] using (congrArg Prod.snd this).symm
  obtain ⟨π, hπ⟩ := hinner ᾱ hᾱinj
  have hηswap : ∀ a b : Fin 4, a ≠ b → η (Equiv.swap a b) = 1 := by
    intro a b hab
    rcases cases_zmod_two (η (Equiv.swap a b)) with h | h
    · exact h
    · exfalso
      have hsw : ᾱ (Equiv.swap a b) = Equiv.swap (π a) (π b) := by
        rw [hπ, Equiv.swap_apply_apply]
      have hconj : act10 (p := p) (K := K) (Multiplicative.ofAdd 1, Equiv.swap (π a) (π b)) =
          φ * act10 (p := p) (K := K) (1, Equiv.swap a b) * φ⁻¹ := by
        rw [← h, ← hsw, ← hαι, hα]
      have hcard : Nat.card (movedV (act10 (p := p) (K := K)
          (Multiplicative.ofAdd 1, Equiv.swap (π a) (π b)))) = p := by
        rw [hconj, movedV_conj, Subgroup.card_map_of_injective φ.injective, movedV_one_swap]
        exact card_movedSub_swap hp hp2 hζ hab
      exact card_movedV_act10_neg_swap_ne hp hp2 hζ hcard
  have hη1 : ∀ σ, η σ = 1 := by
    intro σ
    have hσ : σ ∈ Subgroup.closure {σ : Equiv.Perm (Fin 4) | σ.IsSwap} := by
      rw [Equiv.Perm.closure_isSwap]
      trivial
    induction hσ using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨a, b, hab, rfl⟩ := hx
      exact hηswap a b hab
    | one => exact map_one η
    | mul x y _ _ hx hy => rw [map_mul, hx, hy, mul_one]
    | inv x _ hx =>
      rw [map_inv, hx]
      decide
  have hnormS : ∀ σ : Equiv.Perm (Fin 4), ∃ τ : Equiv.Perm (Fin 4),
      φ * symAut p K σ * φ⁻¹ = symAut p K τ := fun σ => by
    refine ⟨π * σ * π⁻¹, ?_⟩
    rw [← act10_one_eq, hα (1, σ), hαι, hη1, act10_one_eq, hπ]
  exact exists_symAut_mul_pow_of_symNormalizer hp hp2 (by norm_num) hζ
    (fun α hα _ => hinner α hα) φ hnormS

end CFSG.RankThree.PartOne.KEXC
