module

public import CFSG.LocalAnalysis.AGLEmbedding.BlockThreeAux
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.H13.Ch4.NSB

open CFSG.QuasithinUnique

theorem exists_mem_ne_one_of_isSylowTwoOf {X Y : Type*} [Group X] [Finite X] [Group Y]
    {T : Subgroup X} (hT : IsSylowTwoOf T ⊤) (f : X →* Y) {x₀ : X} (h2 : f x₀ ^ 2 = 1)
    (h1 : f x₀ ≠ 1) : ∃ t ∈ T, f t ≠ 1 := by
  by_contra hcon
  push_neg at hcon
  have hbot : T.map f.rangeRestrict = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    rintro _ ⟨t, ht, rfl⟩
    apply Subtype.ext
    simpa using hcon t ht
  have hS := CFSG.AGLEmbedding.isSylowTwoOf_map_top_of_surjective hT
    (MonoidHom.rangeRestrict_surjective f)
  rw [hbot] at hS
  haveI : Finite ↥f.range := Finite.of_surjective _ (MonoidHom.rangeRestrict_surjective f)
  have hidx : ((⊥ : Subgroup ↥f.range).subgroupOf ⊤).index = Nat.card ↥f.range :=
    (Subgroup.relIndex_top_right _).trans Subgroup.index_bot
  obtain ⟨z, hzval⟩ : ∃ z : ↥f.range, (z : Y) = f x₀ :=
    ⟨⟨f x₀, MonoidHom.mem_range.mpr ⟨x₀, rfl⟩⟩, rfl⟩
  have hz2 : z ^ 2 = 1 := Subtype.ext (by simpa [hzval] using h2)
  have hz1 : z ≠ 1 := by
    rintro rfl
    exact h1 (by simpa using hzval.symm)
  have hdvd : orderOf z ∣ Nat.card ↥f.range := orderOf_dvd_natCard z
  rw [orderOf_eq_prime hz2 hz1] at hdvd
  apply hS.2.2
  rw [hidx]
  exact hdvd

end CFSG.Quasithin.H13.Ch4.NSB
