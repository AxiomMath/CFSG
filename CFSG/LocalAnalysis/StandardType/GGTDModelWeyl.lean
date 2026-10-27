module

public import CFSG.LocalAnalysis.StandardType.GGTDModelBasic

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

section Weyl

variable {K : Type} [Field K] {N m : ℕ} {L' : Type} [Group L']

private lemma l48g2_act_root (M : GGTDModel K N m L') (k : Fin N) {r : Kˣ} (hr : r ∈ M.μ) :
    ggTDcor M k (M.ι ⟨r, hr⟩) = M.φ (M.dgm (ggTDpv M.μ N k ⟨r, hr⟩)) := by
  rw [ggTDcor_apply]
  simp

private lemma l48g2_castSucc_ne_succ (k : Fin N) : k.castSucc ≠ k.succ := by
  intro h
  have h2 : (k.castSucc : ℕ) = (k.succ : ℕ) := by simpa using congrArg Fin.val h
  simp only [Fin.val_castSucc, Fin.val_succ] at h2
  exact Nat.succ_ne_self k.val h2.symm

private lemma l48g2_succ_ne_castSucc (k : Fin N) : k.succ ≠ k.castSucc :=
  (l48g2_castSucc_ne_succ k).symm

private lemma l48g2_tuple_act (N : ℕ) (k : Fin N) (t : Fin (N + 1) → Kˣ) :
    (fun i => t (Equiv.swap k.castSucc k.succ i)) =
      t * (ggTDpvFun N k (t k.castSucc / t k.succ))⁻¹ := by
  funext i
  rw [Pi.mul_apply, Pi.inv_apply]
  by_cases h1 : i = k.castSucc
  · subst h1
    rw [Equiv.swap_apply_left]
    simp [ggTDpvFun, Pi.mul_apply, Pi.mulSingle_apply, l48g2_castSucc_ne_succ,
      l48g2_succ_ne_castSucc]
  · by_cases h2 : i = k.succ
    · subst h2
      rw [Equiv.swap_apply_right]
      simp [ggTDpvFun, Pi.mul_apply, Pi.mulSingle_apply, l48g2_castSucc_ne_succ,
        l48g2_succ_ne_castSucc]
    · rw [Equiv.swap_apply_of_ne_of_ne h1 h2]
      simp only [ggTDpvFun, Pi.mul_apply, Pi.mulSingle_apply]
      rw [if_neg h1, if_neg h2]
      simp

private lemma l48g2_tuple_div (N : ℕ) (k : Fin N) (t : Fin (N + 1) → Kˣ) (i : Fin (N + 1)) :
    ggTDpvFun N k (t k.castSucc / t k.succ) i =
      t i / t (Equiv.swap k.castSucc k.succ i) := by
  by_cases h1 : i = k.castSucc
  · subst h1
    rw [Equiv.swap_apply_left]
    simp [ggTDpvFun, Pi.mul_apply, Pi.mulSingle_apply, l48g2_castSucc_ne_succ,
      l48g2_succ_ne_castSucc]
  · by_cases h2 : i = k.succ
    · subst h2
      rw [Equiv.swap_apply_right]
      simp [ggTDpvFun, Pi.mul_apply, Pi.mulSingle_apply, l48g2_castSucc_ne_succ,
        l48g2_succ_ne_castSucc]
    · rw [Equiv.swap_apply_of_ne_of_ne h1 h2]
      simp only [ggTDpvFun, Pi.mul_apply, Pi.mulSingle_apply]
      rw [if_neg h1, if_neg h2]
      simp [div_self]

private lemma l48g2_c9 (M : GGTDModel K N m L') (k : Fin N) {τ : MulAut L'}
    (hτ : τ ∈ ggTDT M) :
    MulAut.conj (ggTDn M k) * τ * (MulAut.conj (ggTDn M k))⁻¹ =
      τ * (MulAut.conj (ggTDcor M k (ggTDroot M k τ)))⁻¹ := by
  obtain ⟨t, ht⟩ := hτ
  let s : ggTDTg M.μ N :=
    ggTDpv M.μ N k ⟨t k.castSucc / t k.succ, M.act_ratio_mem ht _ _⟩
  have hroot : ggTDroot M k τ =
      M.ι ⟨t k.castSucc / t k.succ, M.act_ratio_mem ht _ _⟩ :=
    ggTDroot_of_act M ht k
  have hcor : ggTDcor M k (ggTDroot M k τ) = M.φ (M.dgm s) := by
    rw [hroot]
    exact l48g2_act_root M k (M.act_ratio_mem ht _ _)
  have hL : M.Act (MulAut.conj (ggTDn M k) * τ * (MulAut.conj (ggTDn M k))⁻¹)
      (fun i => t (Equiv.swap k.castSucc k.succ i)) := by
    simpa only [ggTDn] using M.act_perm (Equiv.swap k.castSucc k.succ) ht
  have hR : M.Act (τ * (MulAut.conj (ggTDcor M k (ggTDroot M k τ)))⁻¹)
      (t * (s : Fin (N + 1) → Kˣ)⁻¹) := by
    have h1 : M.Act (MulAut.conj (M.φ (M.dgm s))) (s : Fin (N + 1) → Kˣ) := M.act_dgm s
    have h2 : M.Act (MulAut.conj (M.φ (M.dgm s)))⁻¹ ((s : Fin (N + 1) → Kˣ))⁻¹ :=
      M.act_inv h1
    have h3 : M.Act (τ * (MulAut.conj (M.φ (M.dgm s)))⁻¹)
        (t * (s : Fin (N + 1) → Kˣ)⁻¹) := M.act_mul ht h2
    rwa [← hcor] at h3
  have htuple : (fun i => t (Equiv.swap k.castSucc k.succ i)) =
      t * (s : Fin (N + 1) → Kˣ)⁻¹ := by
    show (fun i => t (Equiv.swap k.castSucc k.succ i)) =
      t * (ggTDpvFun N k (t k.castSucc / t k.succ))⁻¹
    exact l48g2_tuple_act N k t
  exact M.act_unique hL (by rwa [← htuple] at hR)

private lemma l48g2_c10 (M : GGTDModel K N m L') (k : Fin N) {τ : MulAut L'}
    (hτ : τ ∈ ggTDT M) :
    ggTDn M k * (τ (ggTDn M k))⁻¹ = (ggTDcor M k (ggTDroot M k τ))⁻¹ := by
  obtain ⟨t, ht⟩ := hτ
  let s : ggTDTg M.μ N :=
    ggTDpv M.μ N k ⟨t k.castSucc / t k.succ, M.act_ratio_mem ht _ _⟩
  have hroot : ggTDroot M k τ =
      M.ι ⟨t k.castSucc / t k.succ, M.act_ratio_mem ht _ _⟩ :=
    ggTDroot_of_act M ht k
  have hcor : ggTDcor M k (ggTDroot M k τ) = M.φ (M.dgm s) := by
    rw [hroot]
    exact l48g2_act_root M k (M.act_ratio_mem ht _ _)
  have hs : ∀ i, (s : Fin (N + 1) → Kˣ) i =
      t i / t (Equiv.swap k.castSucc k.succ i) := by
    intro i
    show ggTDpvFun N k (t k.castSucc / t k.succ) i =
      t i / t (Equiv.swap k.castSucc k.succ i)
    exact l48g2_tuple_div N k t i
  have hperm : τ (ggTDn M k) =
      M.φ (M.dgm s * M.Pm (Equiv.swap k.castSucc k.succ)) := by
    simpa only [ggTDn] using
      M.act_apply_perm (Equiv.swap k.castSucc k.succ) s ht hs
  rw [hcor, hperm, map_mul]
  simp only [ggTDn]
  group

private lemma l48g2_c11 (M : GGTDModel K N m L') {τ : MulAut L'} (hτ : τ ∈ ggTDT M)
    (h : ∀ k, ggTDroot M k τ = 1) : τ = 1 := by
  obtain ⟨t, ht⟩ := hτ
  have hstep : ∀ k : Fin N, t k.castSucc = t k.succ := by
    intro k
    have hk := ggTDroot_of_act M ht k
    have hι : M.ι ⟨t k.castSucc / t k.succ, M.act_ratio_mem ht _ _⟩ = 1 := by
      rw [← hk]; exact h k
    have hsub : (⟨t k.castSucc / t k.succ, M.act_ratio_mem ht _ _⟩ : M.μ) = 1 :=
      M.ι.injective (by rw [hι, map_one])
    have hval : t k.castSucc / t k.succ = 1 := by
      have := congrArg (fun x : M.μ => (x : Kˣ)) hsub
      simpa using this
    exact div_eq_one.mp hval
  have hconst : t = fun _ => t 0 := by
    funext i
    exact Fin.induction (motive := fun i => t i = t 0) rfl
      (fun i ih => by rw [← hstep i]; exact ih) i
  exact M.act_const (t 0) (hconst ▸ ht)

private lemma l48g2_c12 (M : GGTDModel K N m L') {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpm : p ∣ m) (hm : 0 < m) {A : Subgroup (MulAut L')} (hsc : GGTorusSelfCent p A)
    (hAT : ∀ a ∈ A, ∃ t, M.Act a t) (k : Fin N) :
    ∃ a ∈ A, ggTDroot M k a ≠ 1 := by
  obtain ⟨ζ, hζμ, hζp, hζne, hζneinv⟩ := ggTDzeta M hp hp2 hpm hm
  let s : ggTDTg M.μ N := ggTDpv M.μ N k ⟨ζ, hζμ⟩
  have hsp : ∀ i, (s : Fin (N + 1) → Kˣ) i ^ p = 1 := by
    intro i
    by_cases h1 : i = k.castSucc
    · subst h1
      show ggTDpvFun N k ζ k.castSucc ^ p = 1
      simp [ggTDpvFun, l48g2_castSucc_ne_succ, l48g2_succ_ne_castSucc, hζp]
    · by_cases h2 : i = k.succ
      · subst h2
        show ggTDpvFun N k ζ k.succ ^ p = 1
        rw [show ggTDpvFun N k ζ k.succ = ζ⁻¹ by
          simp [ggTDpvFun, l48g2_castSucc_ne_succ, l48g2_succ_ne_castSucc]]
        rw [inv_pow, hζp, inv_one]
      · show ggTDpvFun N k ζ i ^ p = 1
        have h1' : ggTDpvFun N k ζ i = 1 := by
          simp [ggTDpvFun, h1, h2, l48g2_castSucc_ne_succ, l48g2_succ_ne_castSucc]
        rw [h1', one_pow]
  have hmemA : MulAut.conj (M.φ (M.dgm s)) ∈ A := M.heart_mem hsc hAT s hsp
  refine ⟨MulAut.conj (M.φ (M.dgm s)), hmemA, ?_⟩
  intro hroot_one
  have hroot := ggTDroot_of_act M (M.act_dgm s) k
  have hι : M.ι ⟨(s : Fin (N + 1) → Kˣ) k.castSucc / (s : Fin (N + 1) → Kˣ) k.succ,
      M.act_ratio_mem (M.act_dgm s) _ _⟩ = 1 := by
    rw [← hroot]; exact hroot_one
  have hsub : (⟨(s : Fin (N + 1) → Kˣ) k.castSucc / (s : Fin (N + 1) → Kˣ) k.succ,
      M.act_ratio_mem (M.act_dgm s) _ _⟩ : M.μ) = 1 :=
    M.ι.injective (by rw [hι, map_one])
  have hval : (s : Fin (N + 1) → Kˣ) k.castSucc / (s : Fin (N + 1) → Kˣ) k.succ = 1 := by
    have := congrArg (fun x : M.μ => (x : Kˣ)) hsub
    simpa using this
  have hsval1 : (s : Fin (N + 1) → Kˣ) k.castSucc = ζ := by
    show ggTDpvFun N k ζ k.castSucc = ζ
    simp [ggTDpvFun, l48g2_castSucc_ne_succ, l48g2_succ_ne_castSucc]
  have hsval2 : (s : Fin (N + 1) → Kˣ) k.succ = ζ⁻¹ := by
    show ggTDpvFun N k ζ k.succ = ζ⁻¹
    simp [ggTDpvFun, l48g2_castSucc_ne_succ, l48g2_succ_ne_castSucc]
  rw [hsval1, hsval2] at hval
  exact hζneinv (div_eq_one.mp hval)

theorem ggTDholdsTwo (M : GGTDModel K N m L') {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpm : p ∣ m)
    (hm : 0 < m) {A : Subgroup (MulAut L')}
    (hN : ∀ σ, MulAut.conj (M.φ (M.Pm σ)) ∈ Subgroup.normalizer (A : Set (MulAut L')))
    (hAT : ∀ a ∈ A, ∃ t, M.Act a t) (hsc : GGTorusSelfCent p A) :
    GGTDHoldsTwo (ggTDwit M A hN) := by
  unfold GGTDHoldsTwo
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k τ hτ
    exact l48g2_c9 M k hτ
  · intro k τ hτ
    exact l48g2_c10 M k hτ
  · intro τ hτ h
    exact l48g2_c11 M hτ h
  · intro k
    exact l48g2_c12 M hp hp2 hpm hm hsc hAT k

end Weyl

end CFSG.StandardType
