module

public import CFSG.Quasithin.Vol2.Ch4Sec4W443
public import CFSG.Quasithin.Vol2.Ch4Sec4HypPrime

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.H13

structure Setting443' (G : Type) [Group G] [Finite G] (T M L B Tp VB : Subgroup G) : Prop where
  hyp : Hyp4_4_1Orbit G T M L B Tp VB
  not_concl : ¬ Concl4_4_3' G T M L B VB

theorem setting443_of_prime {G : Type} [Group G] [Finite G] {T M L B Tp VB : Subgroup G}
    (s : Setting443' G T M L B Tp VB) : Setting443 G T M L B Tp VB :=
  ⟨s.hyp, fun h => s.not_concl (Concl4_4_3.toPrime h)⟩

@[expose] def Lemma443End' : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L B Tp VB : Subgroup G),
    Setting443' G T M L B Tp VB →
    IsUniqueM (perfectCore (conjClosure L T ⊓ Subgroup.centralizer (B : Set G)) ⊔
      (Tp ⊓ Subgroup.normalizer (B : Set G))) M →
    oddCoreIn (Subgroup.normalizer (B : Set G)) ≤ M ⊓ Subgroup.normalizer (B : Set G) → False

end CFSG.Quasithin.H13.Ch4

end
