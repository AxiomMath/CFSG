module

public import CFSG.Quasithin.Vol2.Ch11SecAViLevi

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13
open scoped IsMulCommutative

theorem pCore_map_eq_of_surjective {A B : Type*} [Group A] [Group B] [Finite A] [Finite B]
    (f : A →* B) (hf : Function.Surjective f) (hker : IsPGroup 2 f.ker) :
    (CFSG.pCore 2 A).map f = CFSG.pCore 2 B := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_antisymm ?_ ?_
  · have hn : ((CFSG.pCore 2 A).map f).Normal :=
      (CFSG.pCore_normal (p := 2) (G := A)).map f hf
    have hp : IsPGroup 2 ((CFSG.pCore 2 A).map f) :=
      (CFSG.pCore_isPGroup (p := 2) (G := A)).map f
    exact (CFSG.LieType.BorelTits.le_pCore 2 hn hp).trans_eq (open_pCore_eq 2 B)
  · have hp : IsPGroup 2 ((CFSG.pCore 2 B).comap f) :=
      (CFSG.pCore_isPGroup (p := 2) (G := B)).comap_of_ker_isPGroup f hker
    have hn : ((CFSG.pCore 2 B).comap f).Normal :=
      (CFSG.pCore_normal (p := 2) (G := B)).comap f
    have hle : (CFSG.pCore 2 B).comap f ≤ CFSG.pCore 2 A :=
      (CFSG.LieType.BorelTits.le_pCore 2 hn hp).trans_eq (open_pCore_eq 2 A)
    calc CFSG.pCore 2 B = ((CFSG.pCore 2 B).comap f).map f :=
          (Subgroup.map_comap_eq_self_of_surjective hf _).symm
      _ ≤ (CFSG.pCore 2 A).map f := Subgroup.map_mono hle

variable {G : Type} [Group G] [Finite G]

theorem autOn_pCoreOf {X V : Subgroup G} (hX : X ≤ Subgroup.normalizer (V : Set G))
    (hC : IsPGroup 2 ↥(X ⊓ Subgroup.centralizer (V : Set G))) :
    autOn (pCoreOf 2 X) V = pCoreOf 2 (autOn X V) := by
  set f := (MulEquiv.subgroupCongr (range_conjHomL V X hX)).toMonoidHom.comp
    (conjHomL V X hX).rangeRestrict
  have hf : Function.Surjective f :=
    (MulEquiv.subgroupCongr (range_conjHomL V X hX)).surjective.comp
      (MonoidHom.rangeRestrict_surjective _)
  have hfx : ∀ x : ↥X, ((f x : ↥(autOn X V)) : MulAut ↥V) = conjV V x (hX x.2) := fun _ => rfl
  have hker : IsPGroup 2 ↥f.ker := by
    intro k
    have hk : ((k : ↥X) : G) ∈ X ⊓ Subgroup.centralizer (V : Set G) := by
      have h1 : (k : ↥X) ∈ (conjHomL V X hX).ker := by
        rw [MonoidHom.mem_ker]
        have := congrArg Subtype.val ((MonoidHom.mem_ker).mp k.2)
        simpa [f] using this
      rw [ker_conjHomL, Subgroup.mem_subgroupOf] at h1
      exact h1
    obtain ⟨j, hj⟩ := hC ⟨_, hk⟩
    refine ⟨j, Subtype.ext (Subtype.ext ?_)⟩
    have := congrArg Subtype.val hj
    simpa using this
  have hmap := pCore_map_eq_of_surjective f hf hker
  ext s
  constructor
  · intro hs
    obtain ⟨y, hy, hyV, rfl⟩ := mem_autOn_iff.mp hs
    obtain ⟨y', hy', rfl⟩ := hy
    have : f y' ∈ CFSG.pCore 2 ↥(autOn X V) := hmap ▸ Subgroup.mem_map_of_mem f hy'
    refine ⟨f y', ?_, ?_⟩
    · try with_reducible rfl
      exact this
    · exact hfx y'
  · rintro ⟨s', hs', rfl⟩
    rw [← hmap] at hs'
    obtain ⟨y', hy', hys⟩ := hs'
    rw [← hys]
    have e : (autOn X V).subtype (f y') = conjV V y' (hX y'.2) := hfx y'
    rw [e]
    refine conjV_mem_autOn ?_ _
    exact ⟨y', by exact hy', rfl⟩

theorem autOn_lOf {L V U : Subgroup G} (hL : L ≤ Subgroup.normalizer (V : Set G)) (hU : U ≤ V) :
    autOn (LOf L U) V = perfectCore (autOn L V ⊓ stabW (U.subgroupOf V)) := by
  rw [LOf, autOn_perfectCore (inf_le_left.trans hL), autOn_inf_normalizer hU]

end CFSG.Quasithin.Vol2.Ch11.SecA
