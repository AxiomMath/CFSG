module

public import CFSG.Quasithin.Vol2.Ch11SecAVi

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13
open scoped IsMulCommutative

theorem quotPCoreEquivOfSurjective {A B : Type*} [Group A] [Group B] [Finite A] [Finite B]
    (f : A →* B) (hf : Function.Surjective f) (hker : IsPGroup 2 f.ker) :
    Nonempty (A ⧸ CFSG.pCore 2 A ≃* B ⧸ CFSG.pCore 2 B) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set g := (QuotientGroup.mk' (CFSG.pCore 2 B)).comp f
  have hg : Function.Surjective g := (QuotientGroup.mk'_surjective _).comp hf
  have hK : g.ker = CFSG.pCore 2 A := by
    have hk : g.ker = (CFSG.pCore 2 B).comap f := by
      ext a
      simp [g, QuotientGroup.eq_one_iff]
    rw [hk]
    refine le_antisymm ?_ ?_
    · have hp : IsPGroup 2 ((CFSG.pCore 2 B).comap f) :=
        (CFSG.pCore_isPGroup (p := 2) (G := B)).comap_of_ker_isPGroup f hker
      have hn : ((CFSG.pCore 2 B).comap f).Normal :=
        (CFSG.pCore_normal (p := 2) (G := B)).comap f
      exact (CFSG.LieType.BorelTits.le_pCore 2 hn hp).trans_eq (open_pCore_eq 2 A)
    · intro a ha
      have hn : ((CFSG.pCore 2 A).map f).Normal :=
        (CFSG.pCore_normal (p := 2) (G := A)).map f hf
      have hp : IsPGroup 2 ((CFSG.pCore 2 A).map f) :=
        (CFSG.pCore_isPGroup (p := 2) (G := A)).map f
      have hle := (CFSG.LieType.BorelTits.le_pCore 2 hn hp).trans_eq (open_pCore_eq 2 B)
      exact hle (Subgroup.mem_map_of_mem f ha)
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hK.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective g hg)⟩

variable {G : Type} [Group G] [Finite G]

theorem perfectCore_subgroupOf {X N : Subgroup G} (hX : X ≤ N) :
    (perfectCore X).subgroupOf N = perfectCore (X.subgroupOf N) := by
  have h1 : perfectCore X = (perfectCore (X.subgroupOf N)).map N.subtype := by
    rw [map_perfectCore, Subgroup.map_subgroupOf_eq_of_le hX]
  rw [h1]
  exact Subgroup.comap_map_eq_self_of_injective N.subtype_injective _

theorem autOn_perfectCore {X V : Subgroup G} (hX : X ≤ Subgroup.normalizer (V : Set G)) :
    autOn (perfectCore X) V = perfectCore (autOn X V) := by
  unfold autOn
  rw [perfectCore_subgroupOf hX, map_perfectCore]

omit [Finite G] in
theorem autOn_inf_normalizer {L V U : Subgroup G} (hU : U ≤ V) :
    autOn (L ⊓ Subgroup.normalizer (U : Set G)) V = autOn L V ⊓ stabW (U.subgroupOf V) := by
  ext g
  constructor
  · intro hg
    obtain ⟨x, hx, hxV, rfl⟩ := mem_autOn_iff.mp hg
    exact ⟨conjV_mem_autOn (Subgroup.mem_inf.mp hx).1 hxV,
      (conjV_mem_stabW_iff hU hxV).mpr (Subgroup.mem_inf.mp hx).2⟩
  · rintro ⟨hg, hs⟩
    obtain ⟨x, hx, hxV, rfl⟩ := mem_autOn_iff.mp hg
    exact conjV_mem_autOn (Subgroup.mem_inf.mpr ⟨hx, (conjV_mem_stabW_iff hU hxV).mp hs⟩) hxV

theorem lOf_quotEquiv {L V U : Subgroup G} (hL : L ≤ Subgroup.normalizer (V : Set G))
    (hU : U ≤ V) (hC : IsPGroup 2 ↥(L ⊓ Subgroup.centralizer (V : Set G))) :
    Nonempty (↥(LOf L U) ⧸ CFSG.pCore 2 ↥(LOf L U) ≃*
      ↥(perfectCore (autOn L V ⊓ stabW (U.subgroupOf V))) ⧸
        CFSG.pCore 2 ↥(perfectCore (autOn L V ⊓ stabW (U.subgroupOf V)))) := by
  set X := L ⊓ Subgroup.normalizer (U : Set G)
  have hX : X ≤ Subgroup.normalizer (V : Set G) := inf_le_left.trans hL
  have hPX : perfectCore X ≤ Subgroup.normalizer (V : Set G) :=
    (iInf_le (derivedSeriesOf X) 0).trans hX
  have hrange : (conjHomL V (perfectCore X) hPX).range =
      perfectCore (autOn L V ⊓ stabW (U.subgroupOf V)) := by
    rw [range_conjHomL, autOn_perfectCore hX, autOn_inf_normalizer hU]
  set f := (MulEquiv.subgroupCongr hrange).toMonoidHom.comp
    (conjHomL V (perfectCore X) hPX).rangeRestrict
  have hf : Function.Surjective f :=
    (MulEquiv.subgroupCongr hrange).surjective.comp (MonoidHom.rangeRestrict_surjective _)
  have hker : IsPGroup 2 ↥f.ker := by
    intro k
    have hk : (k : ↥(perfectCore X)) ∈ (conjHomL V (perfectCore X) hPX).ker := by
      have := k.2
      simp only [MonoidHom.mem_ker, f, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        MulEquiv.map_eq_one_iff] at this
      rw [MonoidHom.mem_ker]
      have := congrArg Subtype.val this
      simpa using this
    rw [ker_conjHomL, Subgroup.mem_subgroupOf] at hk
    have hxL : ((k : ↥(perfectCore X)) : G) ∈ L ⊓ Subgroup.centralizer (V : Set G) :=
      Subgroup.mem_inf.mpr
        ⟨((iInf_le (derivedSeriesOf X) 0).trans inf_le_left) (k : ↥(perfectCore X)).2,
          (Subgroup.mem_inf.mp hk).2⟩
    obtain ⟨j, hj⟩ := hC ⟨_, hxL⟩
    refine ⟨j, Subtype.ext (Subtype.ext ?_)⟩
    have := congrArg Subtype.val hj
    simpa using this
  exact quotPCoreEquivOfSurjective f hf hker

variable {T L I : Subgroup G} {n : ℕ}

theorem centralizer_eq_pCoreOf (h1102 : Stmt11_0_2) (h : Hyp11 G T L I n) :
    L ⊓ Subgroup.centralizer (fsuV T I : Set G) = pCoreOf 2 L := by
  obtain ⟨_, -, -, ⟨e⟩, -⟩ := h1102 G T L I n h
  exact inf_centralizer_eq_pCoreOf (L_le_normalizer_fsuV h) e

theorem lOf_quot_SL2 (hF : NatFacts) (h1102 : Stmt11_0_2) (h : Hyp11 G T L I n) {i : ℕ}
    (hi : i = 1 ∨ i = 2) {U : Subgroup G} (hU : IsVi T L I n i U) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
      Nonempty (↥(LOf L U) ⧸ CFSG.pCore 2 ↥(LOf L U) ≃* Matrix.SpecialLinearGroup (Fin 2) K) := by
  have hC : IsPGroup 2 ↥(L ⊓ Subgroup.centralizer (fsuV T I : Set G)) := by
    rw [centralizer_eq_pCoreOf h1102 h]
    exact CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L
  obtain ⟨e₁⟩ := lOf_quotEquiv (L_le_normalizer_fsuV h) (IsVi.le_fsuV hU) hC
  have hflag := isFlagW_of_isVi h hU
  obtain ⟨_, -, -, -, hk⟩ := h1102 G T L I n h
  have hsq : ∀ w : ↥(fsuV T I), w ^ 2 = 1 := fun w =>
    Subtype.ext (by simpa using (isElemAbelian_fsuV h).2 w w.2)
  have hn : 2 ≤ n := h.one_lt
  rcases hk with ⟨K, _, _, hK, -, π, hπ, -⟩ | ⟨K, _, _, hK, -, π, hπ, -⟩ | ⟨-, -, -, -, -, hG2⟩
  · obtain ⟨e₂⟩ := hF.leviSL3 K n hn hK _ hsq _ _ π hπ _ (isSylowTwoOf_P h) i _ hi hflag
    exact ⟨K, inferInstance, inferInstance, hK, ⟨e₁.trans e₂⟩⟩
  · obtain ⟨e₂⟩ := hF.leviSp4 K n hn hK _ hsq _ _ π hπ _ (isSylowTwoOf_P h) i _ hi hflag
    exact ⟨K, inferInstance, inferInstance, hK, ⟨e₁.trans e₂⟩⟩
  · obtain ⟨K, _, _, hK, π, hπ⟩ := hG2
    obtain ⟨e₂⟩ := hF.leviG2 K n hn hK _ hsq _ _ π hπ _ (isSylowTwoOf_P h) i _ hi hflag
    exact ⟨K, inferInstance, inferInstance, hK, ⟨e₁.trans e₂⟩⟩

end CFSG.Quasithin.Vol2.Ch11.SecA
