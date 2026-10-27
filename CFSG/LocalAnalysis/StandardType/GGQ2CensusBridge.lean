module

public import CFSG.LocalAnalysis.StandardType.GGNbrBalancePumpup
public import CFSG.LocalAnalysis.StandardType.GGPumpupBalance
public import CFSG.LocalAnalysis.StandardType.GGNbrBalanceBasic
public import CFSG.LocalAnalysis.StandardType.GGOneFiveNbr

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

variable {G : Type} [Group G] [Finite G]

private theorem ggNbr_of_component_pumpup {p : ℕ} {B : Subgroup G} {x : G} {L D J : Subgroup G}
    {d : G} {X Kd : Subgroup G}
    (hX : IsComponentOf X (ggG0 p B x L D J ⊓ Subgroup.centralizer ({d} : Set G)))
    (hXKd : X ≤ Kd)
    (hKdC : IsComponentOf Kd (Subgroup.centralizer ({d} : Set G)))
    (hKdG0 : Kd ≤ ggG0 p B x L D J)
    (hnb : GGNbr p B x D J d Kd) :
    GGNbr p B x D J d X := by
  have hKdH : IsComponentOf Kd (ggG0 p B x L D J ⊓ Subgroup.centralizer ({d} : Set G)) :=
    hKdC.of_le_of_le (le_inf hKdG0 hKdC.1) inf_le_right
  rcases isComponentOf_le_or_commutator_eq_bot hKdH hX.2.1 with hKdX | hcomm
  · have hXKd' : X = Kd := le_antisymm hXKd hKdX
    rwa [hXKd']
  · exfalso
    have hXX : ⁅X, X⁆ ≤ ⁅Kd, X⁆ := Subgroup.commutator_mono hXKd le_rfl
    have hbot : ⁅X, X⁆ = ⊥ := le_bot_iff.mp (hcomm ▸ hXX)
    exact commutator_ne_bot_of_isQuasisimple hX.2.2 hbot

private theorem centralizes_of_commutator_le_primeCore {p : ℕ}
    {x : G} {X Kd : Subgroup G} (hp : p.Prime)
    (hXq : CFSG.Assembly.IsQuasisimple X) (hpX : p ∣ Nat.card X)
    (hXKd : X ≤ Kd) (hxN : x ∈ Subgroup.normalizer (X : Set G))
    (hcore : (⁅Kd, Subgroup.zpowers x⁆ : Subgroup G) ≤ LargeEvenPPrimeCoreOf p Kd) :
    x ∈ Subgroup.centralizer (X : Set G) := by
  have : Fact p.Prime := ⟨hp⟩
  have hOcop : Nat.Coprime p (Nat.card (LargeEvenPPrimeCoreOf p Kd)) := by
    rw [LargeEvenPPrimeCoreOf, Subgroup.card_map_of_injective Kd.subtype_injective]
    exact CFSG.pPrimeCore_coprime_card
  have hXN : X ≤ Subgroup.normalizer (LargeEvenPPrimeCoreOf p Kd : Set G) :=
    fun j hj => mem_normalizer_largeEvenPPrimeCoreOf (Subgroup.le_normalizer (hXKd hj))
  have hcomm_le : (⁅X, Subgroup.zpowers x⁆ : Subgroup G) ≤ LargeEvenPPrimeCoreOf p Kd :=
    (Subgroup.commutator_mono hXKd le_rfl).trans hcore
  exact mem_centralizer_of_commutator_le_coprime hp hXq hpX hOcop hXN hxN hcomm_le

private theorem contradict_of_commutator_eq_bot {p : ℕ} {B : Subgroup G} {x : G}
    {L D J : Subgroup G} (hDJ : LargeEvenStdSub p B x L D J)
    {Kd X : Subgroup G} (hJKd : J ≤ Kd)
    (hcomm : ⁅X, Kd ⊓ ggG0 p B x L D J⁆ = ⊥)
    (hJX : ⁅J, X⁆ ≠ ⊥) : False := by
  have hJgg : J ≤ ggG0 p B x L D J :=
    (hDJ.1.2.2.2.2.2.1.1.trans inf_le_left).trans le_sup_left
  have hJle : J ≤ Kd ⊓ ggG0 p B x L D J := le_inf hJKd hJgg
  have hle : ⁅J, X⁆ ≤ ⁅Kd ⊓ ggG0 p B x L D J, X⁆ := Subgroup.commutator_mono hJle le_rfl
  have hbot : ⁅Kd ⊓ ggG0 p B x L D J, X⁆ = ⊥ := by
    rw [Subgroup.commutator_comm]
    exact hcomm
  exact hJX (le_bot_iff.mp (hbot ▸ hle))

theorem ggNbr_of_isComponentOf_ggG0_inf_centralizer (hLB : GGLBalanceInput) {p : ℕ}
    {B : Subgroup G} {x : G} {L D J : Subgroup G} (hI : GGThmIHyp p B x L)
    (hDJ : LargeEvenStdSub p B x L D J) (hpJ : p ∣ Nat.card J) {d : G} (hdD : d ∈ D)
    (hdx : d ∉ Subgroup.zpowers x) {X : Subgroup G}
    (hX : IsComponentOf X (ggG0 p B x L D J ⊓ Subgroup.centralizer ({d} : Set G)))
    (hxN : x ∈ Subgroup.normalizer (X : Set G)) (hxC : x ∉ Subgroup.centralizer (X : Set G))
    (hpX : p ∣ Nat.card X) (hJX : ⁅J, X⁆ ≠ ⊥) :
    GGNbr p B x D J d X := by
  have hp : p.Prime := hI.2.2.2.2.2.1.1
  have hst : LargeEvenStandardType p B x L := hI.2.2.2.2.2.2.2
  let Kd := ggLayerClosure p (Subgroup.centralizer ({d} : Set G)) J
  have hD : D = Subgroup.closure {x, d} := eq_closure_pair_of_mem hI hDJ hdD hdx
  obtain ⟨hKd_pc, hJKd, hxKd, hnb⟩ :=
    pumpup_of_stdSub (ggPumpupInput_of_lBalance hLB) hI hDJ hpJ hD
  have hKd_sub : IsSubnormal Kd (Subgroup.centralizer ({d} : Set G)) := hKd_pc.2.1
  have hKdG0_sub : IsSubnormal (Kd ⊓ ggG0 p B x L D J)
      (ggG0 p B x L D J ⊓ Subgroup.centralizer ({d} : Set G)) := by
    have h := hKd_sub.inf (ggG0 p B x L D J)
    rwa [inf_comm (Subgroup.centralizer ({d} : Set G)) (ggG0 p B x L D J)] at h
  rcases isComponentOf_le_or_commutator_eq_bot hX hKdG0_sub with hX_le | hcomm
  · have hXKd : X ≤ Kd := hX_le.trans inf_le_left
    rcases hnb with hnb' | hcore'
    · exact ggNbr_of_component_pumpup hX hXKd
        (isComponentOf_of_isNeighborOf hst (isNeighborOf_of_ggNbr hDJ hnb')).1
        (le_ggG0_of_ggNbr hnb') hnb'
    · exact absurd (centralizes_of_commutator_le_primeCore hp hX.2.2 hpX hXKd hxN hcore') hxC
  · exact (contradict_of_commutator_eq_bot hDJ hJKd hcomm hJX).elim

end CFSG.StandardType

end
