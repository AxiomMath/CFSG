module

public import CFSG.Sporadic.Recognition.LyonsAS44Main
public import Certificates.Certificate6109

public section

namespace CFSG.Sporadic.Recognition.LyonsSims

section Cert

variable {G : Type} [Group G] [Finite G] {t : G}
  {ρ : ↥(Subgroup.centralizer ({t} : Set G)) →* Equiv.Perm (Fin 11)}
  {x₁ x₂ x₃ : ↥(Subgroup.centralizer ({t} : Set G))}

theorem lemma45_of_certificate (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃) (T : Sylow 3 G) :
    Lemma45 (x₁ : G) (T : Subgroup G) :=
  D.lemma45 Certificates.certificate6109 S T

theorem lemma45_classes_of_certificate (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃) :
    (∀ g : G, orderOf g = 3 → IsConj g (x₁ : G) ∨ IsConj g ((x₁ : G) * (x₂ : G))) ∧
      ¬ IsConj (x₁ : G) ((x₁ : G) * (x₂ : G)) :=
  D.lemma45_classes Certificates.certificate6109 S

end Cert

end CFSG.Sporadic.Recognition.LyonsSims
