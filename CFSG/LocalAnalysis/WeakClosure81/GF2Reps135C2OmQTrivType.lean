module

public import CFSG.Quasithin.Background.SmithCurtisMain

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin.SmithCurtis

theorem omq_rep_eq_one_of_isCurtisType_zero {G : Type*} [Group G] [Finite G] {B : Type*}
    {M : CoxeterMatrix B} {Weyl : Type*} [Group Weyl] {cs : CoxeterSystem M Weyl}
    (D : CurtisDatum G cs 2) {k V : Type*} [Field k] [CharP k 2] [AddCommGroup V] [Module k V]
    {σ : Representation k G V} (hσ : IsSimpleRep σ) {y : V} {χ : G → k}
    (ht : D.IsCurtisType σ y χ 0) (hχ : ∀ h ∈ D.H, χ h = 1) (g : G) : σ g = 1 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hτ : IsSimpleRep (Representation.trivial k G k) :=
    ⟨inferInstance, fun W _ => Ideal.eq_bot_or_top W⟩
  have htτ : D.IsCurtisType (Representation.trivial k G k) 1 χ 0 := by
    refine ⟨fun u _ => rfl, one_ne_zero, fun h hh => by rw [hχ h hh, one_smul]; rfl, fun s => ?_⟩
    haveI : Fintype (D.X s) := Fintype.ofFinite _
    rw [CurtisDatum.heckeT_apply D (Representation.trivial k G k) s 1]
    have hterm : ∀ x : D.X s, Representation.trivial k G k ((x : G) * D.n s) 1 = 1 :=
      fun x => by rw [Representation.trivial_apply]
    rw [Finset.sum_congr rfl (fun x _ => hterm x), Finset.sum_const, Finset.card_univ,
      ← Nat.card_eq_fintype_card, ← Nat.cast_smul_eq_nsmul k,
      (CharP.cast_eq_zero_iff k 2 (Nat.card (D.X s))).mpr (D.dvd_card_X s)]
    simp only [Pi.zero_apply, zero_smul]
  obtain ⟨β, hβ⟩ := D.iso_of_isCurtisType hσ hτ ht htτ
  exact LinearMap.ext fun v => β.injective (by rw [hβ, Module.End.one_apply]; rfl)

end CFSG.LocalAnalysis.WeakClosure81
