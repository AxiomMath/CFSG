module

public import CFSG.Quasithin.Background.GoldschmidtS146RLat
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListRank2
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix
public import CFSG.Timmesfeld.Orders.Classical

public section

namespace CFSG.Quasithin.GoldS146R

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

section Cover

variable {G S : Type} [Group G] [Group S]

theorem isSolvable_comap_of_ker {f : G →* S} {N : Subgroup S} [Group.IsSolvable N]
    (hk : Group.IsSolvable f.ker) : Group.IsSolvable (N.comap f) := by
  have hle : f.ker ≤ N.comap f := fun x hx => by
    rw [Subgroup.mem_comap, MonoidHom.mem_ker.mp hx]
    exact one_mem _
  refine Group.isSolvable_of_ker_le_range (Subgroup.inclusion hle) (f.subgroupComap N)
    fun x hx => ?_
  have hx1 : f (x : G) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
  exact ⟨⟨x, MonoidHom.mem_ker.mpr hx1⟩, rfl⟩

theorem solvable_overgroup_of_cover (π : G →* S) (hπ : Function.Surjective π)
    (hk : Group.IsSolvable π.ker) {V : Subgroup G}
    (h : ∀ Y : Subgroup G, V ≤ Y → Group.IsSolvable ↥Y → Y ≤ Subgroup.normalizer (V : Set G))
    {Y : Subgroup S} (hVY : V.map π ≤ Y) (hY : Group.IsSolvable ↥Y) :
    Y ≤ Subgroup.normalizer ((V.map π : Subgroup S) : Set S) := by
  have hY' : Group.IsSolvable ↥(Y.comap π) := isSolvable_comap_of_ker hk
  have h1 : V ≤ Y.comap π := Subgroup.map_le_iff_le_comap.mp hVY
  have h2 := h _ h1 hY'
  have h3 : (Y.comap π).map π = Y := Subgroup.map_comap_eq_self_of_surjective hπ Y
  rw [← h3]
  exact (Subgroup.map_mono h2).trans (Subgroup.le_normalizer_map π)

end Cover

section Sylow

variable {X Y : Type} [Group X] [Group Y]

theorem isSylowTwoOf_top_map_equiv (e : X ≃* Y) {U : Subgroup X} (h : IsSylowTwoOf U ⊤) :
    IsSylowTwoOf (U.map e.toMonoidHom) ⊤ := by
  refine ⟨le_top, h.2.1.map e.toMonoidHom, ?_⟩
  have h1 := h.2.2
  rw [show (U.subgroupOf ⊤).index = U.index from Subgroup.relIndex_top_right U] at h1
  rw [show ((U.map e.toMonoidHom).subgroupOf ⊤).index = (U.map e.toMonoidHom).index from
    Subgroup.relIndex_top_right _, Subgroup.index_map_of_bijective (f := e.toMonoidHom) e.bijective]
  exact h1

theorem LatShape.of_equiv_sylow [Finite X] [Finite Y] (e : X ≃* Y) {U₀ : Subgroup X}
    (hU₀ : IsSylowTwoOf U₀ ⊤) (h : LatShape X U₀) {U : Subgroup Y} (hU : IsSylowTwoOf U ⊤) :
    LatShape Y U :=
  LatShape.of_sylow (isSylowTwoOf_top_map_equiv e hU₀) hU (h.map e)

end Sylow

section RankTwo

variable {S : Type} [Group S] [Finite S]

theorem latShape_of_rank_two {U : Subgroup S} {P : Fin 2 → Subgroup S}
    (hP : CFSG.QuasithinUnique.Setup.X6.ResidualOvergroupsAt S U P)
    (hsolv : ∀ Y : Subgroup S, U ≤ Y → Group.IsSolvable ↥Y →
      Y ≤ Subgroup.normalizer (U : Set S))
    {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n)
    (g : ∀ j, ↥(perfectCore (P j)) →* Matrix.SpecialLinearGroup (Fin 2) K)
    (hg : ∀ j, Function.Surjective (g j)) (hker : ∀ j, IsPGroup 2 (g j).ker) :
    LatShape S U := by
  intro Y hUY hYtop
  by_cases hs : Group.IsSolvable ↥Y
  · exact Or.inl (hsolv Y hUY hs)
  · right
    right
    obtain ⟨j, -, hd⟩ := hP.2.2.2.2.1 Y hUY hYtop hs
    have hpc : perfectCore Y = perfectCore (P j) := by
      rw [← CFSG.QuasithinUnique.Vol2Native.A312L.dInf_eq_perfectCore,
        ← CFSG.QuasithinUnique.Vol2Native.A312L.dInf_eq_perfectCore, hd]
    have : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hK
    have hK4 : ∃ s : Finset K, s.card = 4 := by
      refine CFSG.QuasithinUnique.Vol2Native.A312L.exists_finset_card_four ?_
      rw [hK]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    let φ : ↥(perfectCore Y) ≃* ↥(perfectCore (P j)) := MulEquiv.subgroupCongr hpc
    refine ⟨n, hn, hs, Matrix.SpecialLinearGroup (Fin 2) K, inferInstance,
      (g j).comp φ.toMonoidHom, (hg j).comp φ.surjective, ?_,
      CFSG.QuasithinUnique.Vol2Native.A312L.sl2_isSimple hK4, ?_⟩
    · rw [← MonoidHom.comap_ker]
      exact (hker j).comap_of_injective _ φ.injective
    · rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hK]
      rfl

end RankTwo

end CFSG.Quasithin.GoldS146R
