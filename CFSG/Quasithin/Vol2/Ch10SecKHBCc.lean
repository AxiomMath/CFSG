module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListSp4

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.C10KH

open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl

variable {K : Type} [Field K]

@[expose] noncomputable def cartanSp : Kˣ →* StatedProj (StatedSp 2 K) :=
  (proj 2 K).comp (torusHom.comp (MonoidHom.mulSingle (fun _ : Fin 2 => Kˣ) 0))

theorem cartanSp_injective [CharP K 2] : Function.Injective (cartanSp (K := K)) :=
  CFSG.QuasithinUnique.Vol2Native.A312L.proj_injective_charTwo.comp
    (torusHom_injective.comp fun a b h => by simpa using congrFun h 0)

theorem cartanSp_mem_normalizer (l : Kˣ) :
    cartanSp l ∈ Subgroup.normalizer (projUnipotent 2 K : Set (StatedProj (StatedSp 2 K))) := by
  rw [projUnipotent]
  apply Subgroup.le_normalizer_map (proj 2 K)
  refine ⟨torusHom (Pi.mulSingle 0 l), ?_, rfl⟩
  rw [normalizer_unipotent]
  exact torus_le_borelSubgroup (torusHom_mem_torus _)

theorem exists_cartan_projSp [Finite K] [CharP K 2] :
    ∃ d₀ ∈ Subgroup.normalizer (projUnipotent 2 K : Set (StatedProj (StatedSp 2 K))),
      orderOf d₀ = Nat.card K - 1 := by
  obtain ⟨l, hl⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Kˣ)
  exact ⟨cartanSp l, cartanSp_mem_normalizer l, by
    rw [orderOf_injective _ cartanSp_injective l, hl, Nat.card_units]⟩

end CFSG.Quasithin.Vol2.Ch10.SecB.C10KH
