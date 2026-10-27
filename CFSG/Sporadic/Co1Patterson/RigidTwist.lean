module

public import CFSG.Sporadic.Co1Patterson.TwistNativeCount

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Sporadic.Co1Patterson.TwistNative

open Subgroup CFSG.LargeExtraspecial.S14

variable {X : Type} [Group X] [Finite X] {t : X}

theorem card_sq_pCore_centralizer_eq_of_eq (h : PattersonCo1Hyp X t) (hw : NotWeaklyClosed h)
    {T : Type*} [Group T] (σ : centralizer ({t} : Set X) ≃* T) {w z : T}
    (hz : σ ⟨t, mem_centralizer_singleton_self t⟩ = z)
    (hwQ : ((σ.symm w : centralizer ({t} : Set X)) : X) ∈ (setting h).QG)
    (hw2 : orderOf w = 2) (hwz : w ≠ z) :
    Nat.card {x : CFSG.pCore 2 ↥(centralizer ({w} : Set T)) //
        ((x : ↥(centralizer ({w} : Set T))) : T) ^ 2 = z} =
      Nat.card {x : CFSG.pCore 2 ↥(centralizer ({w} : Set T)) //
        ((x : ↥(centralizer ({w} : Set T))) : T) ^ 2 = w} := by
  subst hz
  exact card_sq_pCore_centralizer_eq h hw σ hwQ hw2 hwz


theorem not_isGenuine (h : PattersonCo1Hyp X t) (hw : NotWeaklyClosed h) {k : Fin 3}
    (σ : centralizer ({t} : Set X) ≃* TM k) : ¬ IsGenuine k := by
  intro hk
  have hzt := σ_t_eq h σ (zT_mem_center k) (zT_ne_one k)
  have hQ := symm_mem_QG h σ (twPhi typeSystemC (wPlusMap_zPlus iotaC k)).normal_ker
    (isPGroup_ker_twPhiT k) (wT_mem_ker k)
  have heq := card_sq_pCore_centralizer_eq_of_eq h hw σ hzt hQ (orderOf_wT k) (wT_ne_zT k)
  have h1 : (3136 : ℕ) = 4032 := (card_sq_zT k hk).symm.trans (heq.trans (card_sq_wT k hk))
  norm_num at h1

theorem eq_zero_of_mulEquiv (h : PattersonCo1Hyp X t) (hw : NotWeaklyClosed h) {k : Fin 3}
    (σ : centralizer ({t} : Set X) ≃* TM k) : k = 0 := by
  have hk := not_isGenuine h hw σ
  unfold IsGenuine at hk
  have hk3 := k.isLt
  exact Fin.ext (by simp only [Fin.val_zero]; omega)

end CFSG.Sporadic.Co1Patterson.TwistNative
