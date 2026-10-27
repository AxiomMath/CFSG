module

public import CFSG.Quasithin.Vol2.Ch12Sec8Six
public import CFSG.Quasithin.EmptyFaithful.S1421Defs
public import CFSG.Quasithin.Background.F9Basic

public section

namespace CFSG.Quasithin

open CFSG.Open

structure Setting146 (G : Type) [Group G] [Finite G] (T M : Subgroup G) : Prop where
  hyp : Hyp1421 G T M
  facts : Facts1422 T M
  notSix : ¬ SixModels G
  abelian : IsMulCommutative ↥(uOfL22 T M)

@[expose] def IsHTM {G : Type*} [Group G] (T M H : Subgroup G) : Prop := InH T H ∧ ¬ H ≤ M

namespace Setting146

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

theorem hyp1281 (S : Setting146 G T M) : Hyp1281Two G T M (yOfL22 T M) :=
  S.hyp.hyp1281Two S.facts.unique S.facts.centralizer_yT S.facts.sThree

theorem card_Z (S : Setting146 G T M) : Nat.card (quasithinOmegaOneCenter T) = 2 :=
  S.hyp.card_omegaOneCenter

theorem normalizer_Z (S : Setting146 G T M) :
    Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) = mcOf T :=
  S.hyp1281.normalizer_omegaOneCenter

theorem lOne_eq_bot (S : Setting146 G T M) :
    lOne (yOfL22 T M) (quasithinOmegaOneCenter T) = ⊥ :=
  S.hyp1281.lOne_eq_bot

theorem le_mcOf (S : Setting146 G T M) {H : Subgroup G} (hH : IsHTM T M H) : H ≤ mcOf T :=
  (S.hyp.isUniqueM_centralizer hH.1 hH.2).1.2

theorem isUniqueM_mcOf (S : Setting146 G T M) {H : Subgroup G} (hH : IsHTM T M H) :
    IsUniqueM H (mcOf T) :=
  S.hyp.isUniqueM_centralizer hH.1 hH.2

theorem isHz_iff (S : Setting146 G T M) {H : Subgroup G} :
    IsHz T M (yOfL22 T M) H ↔ IsHTM T M H := by
  rw [S.hyp1281.isHz_iff, S.normalizer_Z]
  exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, S.le_mcOf h, h.2⟩⟩

theorem isHTM_mcOf (S : Setting146 G T M) : IsHTM T M (mcOf T) := by
  rw [← S.isHz_iff, ← S.normalizer_Z]
  exact S.hyp1281.isHz_normalizer

theorem lemma_14_5_14 (S : Setting146 G T M) {H : Subgroup G} (hH : IsHz T M (yOfL22 T M) H) :
    HypF81 T (VZ T M) (yOfL22 T M) (quasithinOmegaOneCenter T) H ∧
      HypF98 T (VZ T M) (yOfL22 T M) (quasithinOmegaOneCenter T) (VZ T M) H := by
  have h81 : HypF81 T (VZ T M) (yOfL22 T M) (quasithinOmegaOneCenter T) H :=
    S.hyp1281.hypF81_of_commutator
      (fun _ hg => S.hyp1281.commutator_eq_bot_of_abelian S.abelian hg) hH
  exact ⟨h81, h81.toHypF98 S.card_Z⟩

end Setting146

end CFSG.Quasithin
