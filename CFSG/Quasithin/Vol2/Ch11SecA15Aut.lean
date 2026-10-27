module

public import CFSG.Quasithin.Vol2.Ch11SecANat2

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13

variable {G : Type} [Group G]

@[expose] noncomputable def autOnHom' (V X : Subgroup G)
    (hX : X ≤ Subgroup.normalizer (V : Set G)) : ↥X →* ↥(autOn X V) :=
  (MulEquiv.subgroupCongr (range_conjHomL V X hX)).toMonoidHom.comp
    (conjHomL V X hX).rangeRestrict

theorem autOnHom'_coe (V X : Subgroup G) (hX : X ≤ Subgroup.normalizer (V : Set G)) (x : ↥X) :
    ((autOnHom' V X hX x : ↥(autOn X V)) : MulAut ↥V) = conjV V x (hX x.2) :=
  rfl

theorem autOnHom'_surjective (V X : Subgroup G) (hX : X ≤ Subgroup.normalizer (V : Set G)) :
    Function.Surjective (autOnHom' V X hX) :=
  (MulEquiv.subgroupCongr (range_conjHomL V X hX)).surjective.comp
    (conjHomL V X hX).rangeRestrict_surjective

theorem conjV_mem_pCore_of_mem_pCoreOf {V X : Subgroup G}
    (hX : X ≤ Subgroup.normalizer (V : Set G)) {k : ↥X} (hk : (k : G) ∈ pCoreOf 2 X) :
    autOnHom' V X hX k ∈ CFSG.pCore 2 ↥(autOn X V) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hk' : k ∈ CFSG.pCore 2 ↥X := by
    obtain ⟨k', hk', hkk⟩ := hk
    rwa [Subtype.ext hkk] at hk'
  have hn : ((CFSG.pCore 2 ↥X).map (autOnHom' V X hX)).Normal :=
    Subgroup.Normal.map CFSG.pCore_normal _ (autOnHom'_surjective V X hX)
  have hp : IsPGroup 2 ↥((CFSG.pCore 2 ↥X).map (autOnHom' V X hX)) :=
    (CFSG.pCore_isPGroup (p := 2) (G := ↥X)).map _
  have hle := (CFSG.LieType.BorelTits.le_pCore 2 hn hp).trans_eq (open_pCore_eq 2 _)
  exact hle ⟨k, hk', rfl⟩

theorem exists_mem_pCoreOf_of_mem_pCore {V X : Subgroup G}
    (hX : X ≤ Subgroup.normalizer (V : Set G))
    (hC : IsPGroup 2 ↥(X ⊓ Subgroup.centralizer (V : Set G))) {x : ↥(autOn X V)}
    (hx : x ∈ CFSG.pCore 2 ↥(autOn X V)) :
    ∃ k : ↥X, (k : G) ∈ pCoreOf 2 X ∧ autOnHom' V X hX k = x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set ρ := autOnHom' V X hX
  have hker : IsPGroup 2 ↥ρ.ker := by
    intro a
    have ha : ((a : ↥X) : G) ∈ X ⊓ Subgroup.centralizer (V : Set G) := by
      have h1 : conjHomL V X hX (a : ↥X) = 1 := by
        have := congrArg Subtype.val (MonoidHom.mem_ker.mp a.2)
        exact this
      have h2 : (a : ↥X) ∈ (conjHomL V X hX).ker := h1
      rw [ker_conjHomL, Subgroup.mem_subgroupOf] at h2
      exact h2
    obtain ⟨j, hj⟩ := hC ⟨_, ha⟩
    refine ⟨j, Subtype.ext (Subtype.ext ?_)⟩
    simpa using congrArg Subtype.val hj
  have hn : ((CFSG.pCore 2 ↥(autOn X V)).comap ρ).Normal :=
    (CFSG.pCore_normal (p := 2) (G := ↥(autOn X V))).comap ρ
  have hp : IsPGroup 2 ↥((CFSG.pCore 2 ↥(autOn X V)).comap ρ) :=
    (CFSG.pCore_isPGroup (p := 2) (G := ↥(autOn X V))).comap_of_ker_isPGroup ρ hker
  have hle := (CFSG.LieType.BorelTits.le_pCore 2 hn hp)
  obtain ⟨a, rfl⟩ := autOnHom'_surjective V X hX x
  exact ⟨a, ⟨a, hle hx, rfl⟩, rfl⟩

end CFSG.Quasithin.Vol2.Ch11.SecA
