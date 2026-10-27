module

public import CFSG.Sporadic.Recognition.LyonsLocalMain
public import CFSG.Sporadic.Recognition.LyonsLocalMcLPairCert

public section

namespace CFSG.Sporadic.Recognition.LyonsSims

section Cert

variable {G : Type} [Group G] [Finite G] {t : G}
  {ρ : ↥(Subgroup.centralizer ({t} : Set G)) →* Equiv.Perm (Fin 11)}
  {x₁ x₂ x₃ : ↥(Subgroup.centralizer ({t} : Set G))}

namespace LyData

theorem exists_sylowQ3_of_certificate (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃) :
    ∃ A : Subgroup G, SylowQ3 (x₁ : G) (x₂ : G) (x₃ : G) t A :=
  D.exists_sylowQ3_of_checks S McLAS.threeFacts_cert McLAS.pairCheck_eq_true

theorem card_normalizer_A3_of_certificate (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃) :
    Nat.card ↥(Subgroup.normalizer (A3 (x₁ : G) (x₂ : G) (x₃ : G) : Set G)) = 23328 :=
  D.card_normalizer_A3_of_checks S McLAS.threeFacts_cert McLAS.pairCheck_eq_true

end LyData

end Cert

end CFSG.Sporadic.Recognition.LyonsSims
