module

public import CFSG.LocalAnalysis.StandardType.GGLangData
public import CFSG.LieType.Chevalley.E8A8RootLattice

public section

namespace CFSG.StandardType

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal CFSG.LieType.RootSystem
open CFSG.Open CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.LangTorus

private lemma lang8_eq_one_of_comp_cast_eq_one {n m : ℕ} {M : Type} [Monoid M] (h : n = m)
    (f : Fin m → M) (hf : (fun i : Fin n => f (Fin.cast h i)) = 1) : f = 1 := by
  funext x
  have hx : f (Fin.cast h (Fin.cast h.symm x)) = 1 := congrFun hf (Fin.cast h.symm x)
  rwa [Fin.rightInverse_cast h x] at hx

theorem ggLang_e8_prime_sign
    {L : Type} [Field L] [IsAlgClosed L] {t : StatedLieTag} {n f p : ℕ}
    {Bs : Subgroup (GGAutU t n f)}
    {S : Matrix (Fin (ggU (absTag t) 6 f).D.rank) (Fin (ggU (absTag t) 6 f).D.rank) ℤ}
    {π : Equiv.Perm (Fin (ggU (absTag t) 6 f).D.rank)}
    {coord : Bs →* Multiplicative (Fin (ggU (absTag t) 6 f).D.rank → ZMod p)}
    (B : GGLangData L t n f p Bs S π coord) (hτ : B.τ = .E8) (hp : p.Prime)
    (b : Bs) (hb : b ≠ 1)
    (Bm : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ)
    (hGram : Bm.transpose * Tag.E8.cartan * Bm = CartanMatrix.A 8)
    (hCols : ∀ j, rootChar (fun i : Fin Tag.E8.rank => B.a b (Fin.cast (by rw [hτ]) i))
        (fun i => Bm i j) = 1) :
    p = 3 ∧ (3 : ℤ) ∣ (2 : ℤ) ^ f - B.ε := by
  have hζp : B.ζ ^ p = 1 := by
    have h := pow_orderOf_eq_one B.ζ
    rwa [B.ζ_order] at h
  have hPow : ∀ i : Fin Tag.E8.rank,
      (B.a b (Fin.cast (by rw [hτ]) i)) ^ p = 1 := by
    intro i
    rw [B.a_coord b (Fin.cast (by rw [hτ]) i), ← pow_mul, Nat.mul_comm, pow_mul, hζp, one_pow]
  have hne : (fun i : Fin Tag.E8.rank => B.a b (Fin.cast (by rw [hτ]) i)) ≠ 1 := by
    intro h
    have ha_eq : B.a b = 1 :=
      lang8_eq_one_of_comp_cast_eq_one (by rw [hτ]) (B.a b) h
    have hroot : rootDiagUnit B.τ (B.a b) = 1 := by rw [ha_eq, rootDiagUnit_one]
    have hb_eq : b = 1 := by
      have hc : ∀ c : (ggU t n f).K ⧸ Subgroup.center (ggU t n f).K,
          (b : GGAutU t n f) c = c := by
        intro c
        apply B.ι_inj
        have h' := B.a_act b c
        rw [hroot] at h'
        simpa using h'
      apply Subtype.ext
      ext c
      simpa using hc c
    exact hb hb_eq
  have hp3 : p = 3 :=
    e8_a8_rootChar_prime hp (fun i : Fin Tag.E8.rank => B.a b (Fin.cast (by rw [hτ]) i))
      Bm hGram hCols hPow hne
  exact ⟨hp3, by simpa [hp3] using B.p_dvd⟩

end CFSG.StandardType
