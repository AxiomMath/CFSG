module

public import CFSG.LocalAnalysis.StandardType.GGLangDictChar
public import CFSG.LocalAnalysis.StandardType.GGLangCoroot

public section

namespace CFSG.StandardType

section Reidx

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal CFSG.LieType.RootSystem
open CFSG.Open CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.LangTorus

@[expose] def ggLangPerm {R N : ℕ} (h : R = N) (π : Equiv.Perm (Fin R)) : Equiv.Perm (Fin N) :=
  (finCongr h).symm.trans (π.trans (finCongr h))

@[expose] def ggLangReidxEquiv {R N : ℕ} (h : R = N) : (Fin R → ℤ) ≃ (Fin N → ℤ) where
  toFun := ggLangReidx h
  invFun := ggLangReidx h.symm
  left_inv v := by subst h; rfl
  right_inv v := by subst h; rfl

theorem ggLangPerm_apply {R N : ℕ} (h : R = N) (π : Equiv.Perm (Fin R)) (j : Fin N) :
    ggLangPerm h π j = Fin.cast h (π (Fin.cast h.symm j)) := by
  subst h
  rfl

theorem ggLang_reidx_latPerm {R N : ℕ} (h : R = N) (π : Equiv.Perm (Fin R)) (v : Fin R → ℤ) :
    ggLangReidx h (latPerm π v) = latPerm (ggLangPerm h π) (ggLangReidx h v) := by
  subst h
  rfl

theorem ggLang_latSolv_preimage {R N : ℕ} (h : R = N) (q2 : Prop) (π : Equiv.Perm (Fin R))
    (O' : Set (Fin N → ℤ)) :
    LatSolv q2 π (ggLangReidx h ⁻¹' O') ↔ LatSolv q2 (ggLangPerm h π) O' := by
  subst h
  exact Iff.rfl

theorem ggLang_cartan_perm
    {L : Type} [Field L] [IsAlgClosed L] {t : StatedLieTag} {n f p : ℕ}
    {Bs : Subgroup (GGAutU t n f)}
    {S : Matrix (Fin (ggU (absTag t) 6 f).D.rank) (Fin (ggU (absTag t) 6 f).D.rank) ℤ}
    {π : Equiv.Perm (Fin (ggU (absTag t) 6 f).D.rank)}
    {coord : Bs →* Multiplicative (Fin (ggU (absTag t) 6 f).D.rank → ZMod p)}
    (B : GGLangData L t n f p Bs S π coord) (j k : Fin B.τ.rank) :
    B.τ.cartan (ggLangPerm B.rank_eq π j) (ggLangPerm B.rank_eq π k) = B.τ.cartan j k := by
  have h := B.pi_diag (Fin.cast B.rank_eq.symm j) (Fin.cast B.rank_eq.symm k)
  rw [ggLangPerm_apply, ggLangPerm_apply]
  simpa using h

theorem ggLang_rho_eq_perm
    {L : Type} [Field L] [IsAlgClosed L] {t : StatedLieTag} {n f p : ℕ}
    {Bs : Subgroup (GGAutU t n f)}
    {S : Matrix (Fin (ggU (absTag t) 6 f).D.rank) (Fin (ggU (absTag t) 6 f).D.rank) ℤ}
    {π : Equiv.Perm (Fin (ggU (absTag t) 6 f).D.rank)}
    {coord : Bs →* Multiplicative (Fin (ggU (absTag t) 6 f).D.rank → ZMod p)}
    (B : GGLangData L t n f p Bs S π coord) {γ : Fin B.τ.rank → ℤ} (hγ : IsRoot B.τ γ) :
    B.setup.ρ γ = B.ε • latPerm (ggLangPerm B.rank_eq π) γ := by
  set v : Fin (ggU (absTag t) 6 f).D.rank → ℤ := fun i => γ (Fin.cast B.rank_eq i) with hv
  have hvγ : ggLangReidx B.rank_eq v = γ := by
    funext j
    simp [ggLangReidx, hv]
  have hvroot : v ∈ (ggU (absTag t) 6 f).D.roots := by
    rw [B.roots_iff, hvγ]
    exact hγ
  have h := B.rho_eq v hvroot
  rw [hvγ] at h
  rw [h, ggLang_reidx_latPerm, hvγ]

theorem ggLang_gram_perm
    {L : Type} [Field L] [IsAlgClosed L] {t : StatedLieTag} {n f p : ℕ}
    {Bs : Subgroup (GGAutU t n f)}
    {S : Matrix (Fin (ggU (absTag t) 6 f).D.rank) (Fin (ggU (absTag t) 6 f).D.rank) ℤ}
    {π : Equiv.Perm (Fin (ggU (absTag t) 6 f).D.rank)}
    {coord : Bs →* Multiplicative (Fin (ggU (absTag t) 6 f).D.rank → ZMod p)}
    (B : GGLangData L t n f p Bs S π coord) (i j : Fin (ggU (absTag t) 6 f).D.rank) :
    S (π i) (π j) = S i j := by
  obtain ⟨k, hk, hg⟩ := B.gram_eq
  have hsingle : ∀ a b : Fin (ggU (absTag t) 6 f).D.rank,
      S a b = k * iform (Pi.single (Fin.cast B.rank_eq a) (1 : ℤ) : Fin B.τ.rank → ℤ)
        (Pi.single (Fin.cast B.rank_eq b) (1 : ℤ) : Fin B.τ.rank → ℤ) := by
    intro a b
    have h1 : latGram S (Pi.single a 1) (Pi.single b 1) = S a b := by
      simp [latGram, Pi.single_apply]
    have hre : ∀ c : Fin (ggU (absTag t) 6 f).D.rank,
        ggLangReidx B.rank_eq (Pi.single c (1 : ℤ)) =
          (Pi.single (Fin.cast B.rank_eq c) (1 : ℤ) : Fin B.τ.rank → ℤ) := by
      intro c
      funext m
      simp only [ggLangReidx, Pi.single_apply]
      congr 1
      apply propext
      constructor
      · intro hm
        rw [← hm]
        simp
      · intro hm
        rw [hm]
        simp
    rw [← h1, hg, hre, hre]
  rw [hsingle (π i) (π j), hsingle i j]
  congr 1
  have hπ : ∀ a : Fin (ggU (absTag t) 6 f).D.rank,
      Fin.cast B.rank_eq (π a) = ggLangPerm B.rank_eq π (Fin.cast B.rank_eq a) := by
    intro a
    rw [ggLangPerm_apply]
    simp
  rw [hπ i, hπ j]
  set i' := Fin.cast B.rank_eq i
  set j' := Fin.cast B.rank_eq j
  set π' := ggLangPerm B.rank_eq π
  have hei : B.setup.ρ (Pi.single i' 1) = B.ε • (Pi.single (π' i') 1 : Fin B.τ.rank → ℤ) := by
    rw [ggLang_rho_eq_perm B (isRoot_single B.τ i')]
    congr 1
    funext m
    simp [latPerm, Pi.single_apply, Equiv.symm_apply_eq]
    rfl
  have hej : B.setup.ρ (Pi.single j' 1) = B.ε • (Pi.single (π' j') 1 : Fin B.τ.rank → ℤ) := by
    rw [ggLang_rho_eq_perm B (isRoot_single B.τ j')]
    congr 1
    funext m
    simp [latPerm, Pi.single_apply, Equiv.symm_apply_eq]
    rfl
  have hform := B.setup.frob.iform_eq (Pi.single i' 1) (Pi.single j' 1)
  rw [hei, hej, iform_smul_left, iform_smul_right] at hform
  have hε : B.ε * (B.ε * iform (Pi.single (π' i') 1 : Fin B.τ.rank → ℤ)
      (Pi.single (π' j') 1 : Fin B.τ.rank → ℤ)) =
        iform (Pi.single (π' i') 1 : Fin B.τ.rank → ℤ) (Pi.single (π' j') 1 : Fin B.τ.rank → ℤ) := by
    rcases B.ε_cases with h | h <;> rw [h] <;> ring
  rw [hε] at hform
  exact hform

theorem ggLang_gram_ne_zero_iff
    {L : Type} [Field L] [IsAlgClosed L] {t : StatedLieTag} {n f p : ℕ}
    {Bs : Subgroup (GGAutU t n f)}
    {S : Matrix (Fin (ggU (absTag t) 6 f).D.rank) (Fin (ggU (absTag t) 6 f).D.rank) ℤ}
    {π : Equiv.Perm (Fin (ggU (absTag t) 6 f).D.rank)}
    {coord : Bs →* Multiplicative (Fin (ggU (absTag t) 6 f).D.rank → ZMod p)}
    (B : GGLangData L t n f p Bs S π coord) (α β : Fin (ggU (absTag t) 6 f).D.rank → ℤ) :
    latGram S α β ≠ 0 ↔
      iform (ggLangReidx B.rank_eq α) (ggLangReidx B.rank_eq β) ≠ 0 := by
  obtain ⟨k, hk, hg⟩ := B.gram_eq
  rw [hg]
  exact mul_ne_zero_iff.trans ⟨fun h => h.2, fun h => ⟨hk.ne', h⟩⟩

theorem ggLang_a_pow_eq_one
    {L : Type} [Field L] [IsAlgClosed L] {t : StatedLieTag} {n f p : ℕ}
    {Bs : Subgroup (GGAutU t n f)}
    {S : Matrix (Fin (ggU (absTag t) 6 f).D.rank) (Fin (ggU (absTag t) 6 f).D.rank) ℤ}
    {π : Equiv.Perm (Fin (ggU (absTag t) 6 f).D.rank)}
    {coord : Bs →* Multiplicative (Fin (ggU (absTag t) 6 f).D.rank → ZMod p)}
    (B : GGLangData L t n f p Bs S π coord) (b : Bs) (j : Fin B.τ.rank) :
    B.a b j ^ p = 1 := by
  have hζ : B.ζ ^ p = 1 := by
    have h := pow_orderOf_eq_one B.ζ
    rwa [B.ζ_order] at h
  rw [B.a_coord, ← pow_mul, mul_comm, pow_mul, hζ, one_pow]

theorem ggLang_natCast_ne_zero
    {L : Type} [Field L] [IsAlgClosed L] {t : StatedLieTag} {n f p : ℕ}
    {Bs : Subgroup (GGAutU t n f)}
    {S : Matrix (Fin (ggU (absTag t) 6 f).D.rank) (Fin (ggU (absTag t) 6 f).D.rank) ℤ}
    {π : Equiv.Perm (Fin (ggU (absTag t) 6 f).D.rank)}
    {coord : Bs →* Multiplicative (Fin (ggU (absTag t) 6 f).D.rank → ZMod p)}
    (B : GGLangData L t n f p Bs S π coord) (hp : p.Prime) (hp2 : p ≠ 2) : (p : L) ≠ 0 := by
  haveI : CharP L 2 :=
    LangRat.charP_two_of_langSetup_q_eq_two_pow B.setup (f := f) B.q_eq
  intro h
  have h2 : 2 ∣ p := (CharP.cast_eq_zero_iff L 2 p).1 h
  exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 h2).symm

end Reidx

end CFSG.StandardType
