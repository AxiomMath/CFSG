module

public import CFSG.Quasithin.Vol2.Ch10SecB3FactsC
public import CFSG.Quasithin.Vol2.Ch10SecKGCFc
public import CFSG.Quasithin.Vol2.Ch10SecKGCFg
public import CFSG.Quasithin.Vol2.Ch10SecAModels
public import CFSG.Quasithin.Background.HSL

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

open CFSG.Quasithin CFSG.Quasithin.H CFSG.Assembly.LowTwoRank
open scoped Matrix

theorem factCommField_holds : FactCommField := by
  intro V _ _ H R x a r hmod hR hRH _ hr hr2 hrH hxr hxH hfix
  have hodd : Odd r := hr.odd_of_ne_two hr2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases hmod with ⟨ha, K, _, _, hK, π, hRV⟩ | ⟨a', ha', rfl, K, _, _, hK, π, hRV⟩ |
    ⟨ha, K, _, _, _, hK, π, hRV⟩
  ·
    obtain ⟨e, he⟩ := exists_mulEquiv_of_realizesVia (StatedSL 2 K) hRV
    have := Fintype.ofFinite K
    have : CharP K 2 := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hK])
    have : Nontrivial V := e.toEquiv.nontrivial
    have hx := C10KG.isSemi_one_of_fix (by omega : 1 ≤ a) hK (C10KG.isScalarAct_smOf e)
      (C10KG.smOf_comm hRV.1 he) (C10KG.smOf_commutant (hasScalarCommutant_statedSL le_rfl) he)
      hR hRH hodd hxr hxH hfix
    exact C10KG.eq_one_natSL hRV.1 he hr hrH hx hxr
  ·
    obtain ⟨e, he⟩ := exists_mulEquiv_of_realizesVia (CFSG.Blueprint.suzukiGroup a' K) hRV
    have := Fintype.ofFinite K
    have : CharP K 2 := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hK])
    have : Nontrivial V := e.toEquiv.nontrivial
    have hx := C10KG.isSemi_one_of_fix (by omega : 1 ≤ 2 * a' + 1) hK
      (C10KG.isScalarAct_smOf e) (C10KG.smOf_comm hRV.1 he)
      (C10KG.smOf_commutant C10KG.hasScalarCommutant_sz he) hR hRH hodd hxr hxH hfix
    exact C10KG.eq_one_natSz ha' hK hRV.1 he hr hrH hx hxH hxr
  ·
    obtain ⟨B, hBs, hBk, hBe⟩ := C10P34.exists_herm_hom a hRV
    have hBi : Function.Injective B := (injective_iff_map_eq_one B).mpr fun w hw =>
      Subgroup.mem_bot.mp ((hBk w).mp hw)
    let BE : V ≃* ↥(hermSub a (Fin 2) K) := MulEquiv.ofBijective B ⟨hBi, hBs⟩
    have hBE : ∀ (γ : ↥(StatedSL 2 K)) v, C10KG.hmat a (BE (((π γ : ↥H) : MulAut V) v)) =
        C10KG.smat γ * C10KG.hmat a (BE v) * (frobPow a (C10KG.smat γ))ᵀ := fun γ v =>
      (congrArg Multiplicative.toAdd (hBe γ v)).trans rfl
    obtain ⟨S, hS, hSfix, hScard⟩ := C10KG.exists_fq a (by omega) hK
    have hπinj := FFModel.RealizesVia.injective_of_faithful
      (SecA.twistTensor_faithful a) hRV
    have : Nontrivial ↥(hermSub a (Fin 2) K) :=
      ⟨⟨⟨Multiplicative.ofAdd (C10P34.e11 1), C10P34.isHerm_e11_one a⟩, 1, fun h => by
        have h1 := congrFun (congrFun (congrArg (C10KG.hmat a) h) 0) 0
        simp [C10KG.hmat, C10P34.e11] at h1⟩⟩
    have : Nontrivial V := BE.toEquiv.nontrivial
    have hx := C10KG.isSemi_one_of_fix (by omega : 1 ≤ a) hScard
      (C10KG.isScalarAct_smH a BE S hS) (C10KG.smH_comm a hRV.1 hBE S hS)
      (C10KG.smH_commutant a (by omega) hK hBE S hS) hR hRH hodd hxr hxH hfix
    exact C10KG.eq_one_orth a (by omega) hK ⟨hπinj, hRV.1⟩ hBE S hS hSfix hScard hr hr2 hrH hx
      hxH hxr

end CFSG.Quasithin.Vol2.Ch10.SecB
