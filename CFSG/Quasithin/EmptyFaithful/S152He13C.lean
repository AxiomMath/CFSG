module

public import CFSG.Quasithin.EmptyFaithful.SBc12Top
public import CFSG.Quasithin.EmptyFaithful.S151cStmt2
public import CFSG.Quasithin.EmptyFaithful.S152He13B

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace He13

@[expose] def Input15111YRigid : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M : Subgroup G), quasithinQTFE14Cat G T Mc →
    IsMf T Mc M → IsCE1513 T M → ∀ H : Subgroup G, IsHStar T M H →
      ¬ V154 T Mc M ≤ pCoreOf 2 H →
      ¬ Case1512Six T Mc M →
      Nat.card (quasithinOmegaOneCenter T) = 2 →
      Mc ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) →
      (∃ D : Subgroup G, D ≤ conjClosure (V154 T Mc M) H ∧
        conjClosure (V154 T Mc M) H ≤ Subgroup.normalizer (D : Set G) ∧ E2.IsExtraspecialPlus 2 D ∧
        ∃ φ : ↥(conjClosure (V154 T Mc M) H) →* Equiv.Perm (Fin 3), Function.Surjective φ ∧
          φ.ker = D.subgroupOf (conjClosure (V154 T Mc M) H)) → False

theorem input15111YRigid_of_input15111Y (hY : SBc12.Input15111Y) : Input15111YRigid :=
  fun G _ _ T Mc M hq hM hCE H hH hV _ _ _ hD => hY G T Mc M hq hM hCE H hH hV hD

theorem input15111Y_of_rigid (h15 : StageLemma1515CE) (h159 : StageLemma1519)
    (hR : Input15111YRigid) : SBc12.Input15111Y := by
  intro G _ _ T Mc M hq hM hCE H hH hV hY
  obtain ⟨D, hDY, hDN, hD, φ, hφs, hφk⟩ := hY
  obtain ⟨hB, hZ2, hMc⟩ := rigid_facts hq hM (h159 G T Mc M hq hM hCE) (h15 G T Mc M hq hM hCE) hH
    hDY hD φ hφs hφk
  exact hR G T Mc M hq hM hCE H hH hV hB hZ2 hMc ⟨D, hDY, hDN, hD, φ, hφs, hφk⟩

end He13

end CFSG.Quasithin
