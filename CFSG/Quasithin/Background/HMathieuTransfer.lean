module

public import CFSG.Quasithin.Background.HMathieuChain
public import CFSG.Quasithin.Background.HMathieuArr

public section

namespace CFSG.Quasithin.H.Mathieu

open CFSG.QuasithinUnique.Setup.X1

variable {V : Type*} [CommGroup V] {n : ℕ} {K P : Type*} [Group K] [Finite K] [Group P]

@[expose] def twistEquiv (e : V ≃* Wn n) (ψ : K →* MulAut (Wn n)) (g : K) : V ≃* Wn n :=
  e.trans (ψ g)

@[expose] def chainAut (e : V ≃* Wn n) (ψ : K →* MulAut (Wn n)) (φ : P →* K)
    (g : K) : P →* MulAut V :=
  (MulAut.congr (twistEquiv e ψ g)).symm.toMonoidHom.comp (ψ.comp φ)

omit [Finite K] in
theorem congrHom_twist_apply (e : V ≃* Wn n) (ψ : K →* MulAut (Wn n)) (g : K) (a : MulAut V)
    (w : Wn n) : congrHom (twistEquiv e ψ g) a w = ψ g (congrHom e a ((ψ g).symm w)) := rfl

omit [Finite K] in
theorem congrHom_chainAut (e : V ≃* Wn n) (ψ : K →* MulAut (Wn n)) (φ : P →* K) (g : K)
    (s : P) : congrHom (twistEquiv e ψ g) (chainAut e ψ φ g s) = ψ (φ s) :=
  (MulAut.congr (twistEquiv e ψ g)).apply_symm_apply _

omit [Finite K] in
theorem chainAut_injective {e : V ≃* Wn n} {ψ : K →* MulAut (Wn n)} {φ : P →* K}
    (hψ : Function.Injective ψ) (hφ : Function.Injective φ) (g : K) :
    Function.Injective (chainAut e ψ φ g) :=
  fun _ _ h => hφ (hψ ((MulAut.congr (twistEquiv e ψ g)).symm.injective h))

omit [Finite K] in

theorem chainAct_twist (e : V ≃* Wn n) (ψ : K →* MulAut (Wn n)) (φ : P →* K) (g : K)
    {act : P → ℕ → ℕ} (hact : ∀ s, ∀ m < 2 ^ n, ψ (φ s) (toW n m) = toW n (act s m))
    (hlt : ∀ s, ∀ m < 2 ^ n, act s m < 2 ^ n) :
    ChainAct (MaskCoords.ofEquiv (twistEquiv e ψ g)) (chainAut e ψ φ g) act where
  spec s m hm := by
    show (twistEquiv e ψ g).symm (ψ (φ s) ((twistEquiv e ψ g)
      ((twistEquiv e ψ g).symm (toW n m)))) = _
    rw [MulEquiv.apply_symm_apply, hact s m hm]
    rfl
  lt := hlt

variable [Finite P] [DecidableEq P]

theorem exists_chainModel (ψ : K →* MulAut (Wn n)) (hψ : Function.Injective ψ) (φ : P →* K)
    (hφ : Function.Injective φ) (hsyl : Nat.card P = 2 ^ (Nat.card K).factorization 2)
    {Rinv : List P} (hR : ∀ x : P, x ≠ 1 → x * x = 1 → x ∈ Rinv)
    {pred : List P → Bool} {k : ℕ} (hg : forallGreedy Rinv pred k [] = true)
    (e : V ≃* Wn n) {A : Subgroup (MulAut V)} (hAR : A.map (congrHom e) ≤ ψ.range)
    (hA : IsElemAbelian2 A) (hcard : Nat.card A = 2 ^ k) :
    ∃ g : K, ∃ l : List P, IndepList l ∧ pred l = true ∧ IsChainSub (chainAut e ψ φ g) l A := by
  have hE := (isElemAbelian2_map_congrHom e).2 hA
  obtain ⟨g, l, hind, hpred, hiff⟩ := exists_conj_chain φ hφ ψ hψ hsyl hR hg
    (A.map (congrHom e)) hAR hE.1 (fun a ha => by rw [← sq]; exact hE.2 a ha)
    ((card_map_congrHom e A).trans hcard)
  refine ⟨g, l, hind, hpred, fun a => ?_⟩
  have h1 : a ∈ A ↔ congrHom e a ∈ A.map (congrHom e) :=
    (Subgroup.mem_map_iff_mem (congrHom_injective e)).symm
  refine h1.trans ((hiff _).trans (exists_congr fun s => and_congr_right fun _ => ?_))
  constructor
  · intro h
    apply congrHom_injective (twistEquiv e ψ g)
    rw [congrHom_chainAut, ← h]
    ext w
    rfl
  · intro h
    rw [h, ← congrHom_chainAut e ψ φ g s]
    ext w
    rfl

omit [Finite P] [DecidableEq P] in
theorem exists_conj_elemModel {p : ℕ} [Fact p.Prime] (ψ : K →* MulAut (Wn n))
    (hψ : Function.Injective ψ) (φ : P →* K) (hφ : Function.Injective φ)
    (hsyl : Nat.card P = p ^ (Nat.card K).factorization p) (e : V ≃* Wn n) {y : MulAut V}
    (hyR : congrHom e y ∈ ψ.range) (hy : orderOf y = p) :
    ∃ g : K, ∃ s : P, s ≠ 1 ∧ congrHom (twistEquiv e ψ g) y = ψ (φ s) := by
  obtain ⟨k, hk⟩ := hyR
  have hko : orderOf k = p :=
    (orderOf_injective ψ hψ k).symm.trans ((congrArg orderOf hk).trans
      ((orderOf_injective _ (congrHom_injective e) y).trans hy))
  obtain ⟨g, s, hs1, hgs⟩ := exists_conj_of_prime φ hφ hsyl hko
  refine ⟨g, s, hs1, ?_⟩
  ext w
  rw [congrHom_twist_apply, ← hgs, map_mul, map_mul, map_inv, hk]
  rfl

end CFSG.Quasithin.H.Mathieu
