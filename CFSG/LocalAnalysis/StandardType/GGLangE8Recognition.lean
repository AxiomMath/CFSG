module

public import CFSG.LocalAnalysis.StandardType.GGLangE8RecogBase
public import CFSG.LocalAnalysis.StandardType.GGLangE8RecogClass
public import CFSG.LocalAnalysis.StandardType.GGLangE8RecogDispatch
public import CFSG.LocalAnalysis.StandardType.GGLangE8RecogFrame

public section

namespace CFSG.StandardType

section Recognition

open CFSG.Assembly
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal CFSG.LieType.RootSystem
open CFSG.Open CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.LangTorus

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def GGE8Recognition
    : Prop :=
  ∀ (L : Type) [Field L] [IsAlgClosed L] (n' f p : ℕ) (Bs : Subgroup (GGAutU .E8 n' f))
    (S : Matrix (Fin (ggU (absTag .E8) 6 f).D.rank) (Fin (ggU (absTag .E8) 6 f).D.rank) ℤ)
    (π : Equiv.Perm (Fin (ggU (absTag .E8) 6 f).D.rank))
    (coord : Bs →* Multiplicative (Fin (ggU (absTag .E8) 6 f).D.rank → ZMod p))
    (B : GGLangData L .E8 n' f p Bs S π coord) (hτ : B.τ = .E8), p.Prime → p ≠ 2 →
      ∀ b : Bs, b ≠ 1 → ∀ Jm : Subgroup (GGAutU .E8 n' f),
        CFSG.Assembly.IsComponentOf Jm ((ggPsiU .E8 n' f).range ⊓
          Subgroup.centralizer ({(b : GGAutU .E8 n' f)} : Set (GGAutU .E8 n' f))) →
        ∀ labJ : LargeEvenLabel, LargeEvenInLambda2 labJ →
          GGHasLabel labJ (↥Jm ⧸ Subgroup.center ↥Jm) →
          (labJ.tag = .A ∨ labJ.tag = .twA) → labJ.rank = 8 → labJ.n = f →
          ∃ Bm : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ,
            Bm.transpose * Tag.E8.cartan * Bm = CartanMatrix.A 8 ∧
            (∀ j, rootChar (fun i : Fin Tag.E8.rank => B.a b (Fin.cast (by rw [hτ]) i))
              (fun i => Bm i j) = 1) ∧
            (labJ.tag = .A → B.ε = 1) ∧ (labJ.tag = .twA → B.ε = -1)

theorem recoga_GGE8Recognition_of_packets
    : GGE8Recognition := by
  intro L _ _ n' f p Bs S π coord B hτ hp hp2 b hb Jm hJm labJ hΛJ hJ htag hrank hn
  obtain ⟨i, hqs, hJm', hlab⟩ := recoga_class_exists B hτ hp hp2 hb hJm hΛJ hJ
  obtain ⟨hr8, hn72, hcases⟩ :=
    recoga_kind_dispatch B hτ hp hp2 hb i hqs hΛJ hlab htag hrank hn
  obtain ⟨Bm, hGram, hCols, hinner, hsuN⟩ := recoga_A8_frame B hτ hp hp2 hb i hr8 hn72
  refine ⟨Bm, hGram, hCols, ?_, ?_⟩
  · intro ht
    rcases hcases with ⟨-, hk⟩ | ⟨ht', -⟩
    · exact hinner hk
    · rw [ht] at ht'; exact absurd ht' (by decide)
  · intro ht
    rcases hcases with ⟨ht', -⟩ | ⟨-, hk⟩
    · rw [ht] at ht'; exact absurd ht' (by decide)
    · exact hsuN hk

theorem ggTCJE8A8Sign_of_recognition
    (h : GGE8Recognition) : GGTCJE8A8Sign := by
  intro L _ _ n' f p Bs S π coord B hp hp2 b hb Jm hJm labJ hΛJ hJ htag hrank hn
  have hτ : B.τ = .E8 := recoga_tau_eq_E8 B
  obtain ⟨Bm, hGram, hCols, hA, htwA⟩ :=
    h L n' f p Bs S π coord B hτ hp hp2 b hb Jm hJm labJ hΛJ hJ htag hrank hn
  obtain ⟨hp3, hsign⟩ := ggLang_e8_prime_sign B hτ hp b hb Bm hGram hCols
  refine ⟨hp3, ?_, ?_⟩
  · intro ht
    have heps : B.ε = 1 := hA ht
    have h2f : 1 ≤ 2 ^ f := Nat.one_le_pow f 2 (by norm_num)
    have hcast : ((2 ^ f - 1 : ℕ) : ℤ) = (2 : ℤ) ^ f - 1 := by
      rw [Nat.cast_sub h2f]; push_cast; ring
    rw [heps, ← hcast] at hsign
    exact_mod_cast hsign
  · intro ht
    have heps : B.ε = -1 := htwA ht
    have hcast : ((2 ^ f + 1 : ℕ) : ℤ) = (2 : ℤ) ^ f + 1 := by push_cast; ring
    rw [heps] at hsign
    rw [sub_neg_eq_add] at hsign
    rw [← hcast] at hsign
    exact_mod_cast hsign

theorem ggTCJE8A8Sign_holds :
    GGTCJE8A8Sign :=
  ggTCJE8A8Sign_of_recognition recoga_GGE8Recognition_of_packets

end Recognition

end CFSG.StandardType

end
