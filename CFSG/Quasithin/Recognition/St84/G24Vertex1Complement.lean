module

public import CFSG.Quasithin.Recognition.St84.G24Vertex1Frame
public import CFSG.GroupTheory.FixedPointFreeModCentral
import CFSG.Quasithin.Background.SpecialPGroupCenter
import CFSG.Quasithin.Recognition.St84.G24Tools
import CFSG.Quasithin.Recognition.St84.Gen.CoprimeComplement
import CFSG.GroupTheory.Commutator.JoinNormalizer
import CFSG.GroupTheory.CentralizerSup
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F112R CFSG.GroupTheory
  CFSG.GH74.QTGen4.DSGen4
open scoped commutatorElement

variable {G : Type} [Group G]

private theorem relIndex_L1_P1 [Finite G]
    {L1 L2 S : Subgroup G} (hF : F112HypW L1 L2 S) (h1 : VA5 L1)
    (hD : G24LocalData L1 L2 S) :
    L1.relIndex (L1 ⊔ bigB L1 L2 S) = 3 := by
  have h := Subgroup.relIndex_mul_card (H := L1) (K := L1 ⊔ bigB L1 L2 S)
  rw [inf_eq_left.mpr le_sup_left, G24LocalData.card_vertex_left hF h1 hD,
    G24LocalData.card_L_left hF h1 hD, hD.card_dsQ_left] at h
  norm_num at h ⊢
  omega

theorem G24Vertex1.sup_zpowers_eq_sup_bigB [Finite G]
    {L1 L2 S : Subgroup G} (hF : F112HypW L1 L2 S) (h1 : VA5 L1)
    (hD : G24LocalData L1 L2 S) {k : G} (hkB : k ∈ bigB L1 L2 S)
    (hkL : k ∉ L1) :
    L1 ⊔ Subgroup.zpowers k = L1 ⊔ bigB L1 L2 S := by
  have hkP : k ∈ L1 ⊔ bigB L1 L2 S :=
    (le_sup_right : bigB L1 L2 S ≤ L1 ⊔ bigB L1 L2 S) hkB
  have hKle : Subgroup.zpowers k ≤ L1 ⊔ bigB L1 L2 S := Subgroup.zpowers_le.mpr hkP
  have hsup_le : L1 ⊔ Subgroup.zpowers k ≤ L1 ⊔ bigB L1 L2 S := sup_le le_sup_left hKle
  have hrel := Subgroup.relIndex_mul_relIndex (H := L1) (K := L1 ⊔ Subgroup.zpowers k)
    (L := L1 ⊔ bigB L1 L2 S) le_sup_left hsup_le
  rw [relIndex_L1_P1 hF h1 hD] at hrel
  have hdvd : L1.relIndex (L1 ⊔ Subgroup.zpowers k) ∣ 3 := ⟨_, hrel.symm⟩
  have hne : L1.relIndex (L1 ⊔ Subgroup.zpowers k) ≠ 1 := by
    intro h1'
    have hle : L1 ⊔ Subgroup.zpowers k ≤ L1 := Subgroup.relIndex_eq_one.mp h1'
    exact hkL (hle (Subgroup.mem_sup_right (Subgroup.mem_zpowers k)))
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1' | h3
  · exact absurd h1' hne
  · have hPrel : (L1 ⊔ Subgroup.zpowers k).relIndex (L1 ⊔ bigB L1 L2 S) = 1 := by
      rw [h3] at hrel
      omega
    exact le_antisymm hsup_le (Subgroup.relIndex_eq_one.mp hPrel)

private theorem inf_centerOf_centralizer [Finite G]
    {L1 L2 S : Subgroup G} (hF : F112HypW L1 L2 S) (h1 : VA5 L1) (h2 : VA5 L2)
    (hD : G24LocalData L1 L2 S) {k : G} (hkB : k ∈ bigB L1 L2 S)
    (hkL : k ∉ L1) :
    centerOf (dsQ L1 L2 S) ⊓ Subgroup.centralizer ({k} : Set G) = ⊥ := by
  refine le_antisymm ?_ bot_le
  intro z hz
  rw [Subgroup.mem_bot]
  have hzZ : z ∈ centerOf (dsQ L1 L2 S) := hz.1
  have hzC : z ∈ Subgroup.centralizer ({k} : Set G) := hz.2
  have hzL : z ∈ L1 := (Subgroup.mem_inf.mp (hD.center_left ▸ hzZ)).1
  have hcentP : z ∈ Subgroup.centralizer
      ((L1 ⊔ bigB L1 L2 S : Subgroup G) : Set G) := by
    rw [← G24Vertex1.sup_zpowers_eq_sup_bigB hF h1 hD hkB hkL, CFSG.centralizer_sup_zpowers_eq]
    exact ⟨(hD.center_left ▸ hzZ).2, hzC⟩
  have hzcP : z ∈ centerOf (L1 ⊔ bigB L1 L2 S) := by
    refine Subgroup.mem_inf.mpr ⟨?_, hcentP⟩
    exact (le_sup_left : L1 ≤ L1 ⊔ bigB L1 L2 S) hzL
  rw [G24LocalData.center_vertex_left hF h2 hD] at hzcP
  exact Subgroup.mem_bot.mp hzcP

private theorem conj_mem_fixedModSubgroup {L1 L2 S : Subgroup G}
    (hD : G24LocalData L1 L2 S) {k : G}
    (hkc : ∀ x ∈ L1 ⊔ bigB L1 L2 S, ⁅k, x⁆ ∈ dsQ L1 L2 S)
    {p x : G} (hp : p ∈ L1 ⊔ bigB L1 L2 S)
    (hx : x ∈ fixedModSubgroup (dsQ L1 L2 S) (centerOf (dsQ L1 L2 S)) k
      ((dsQ_le_P_left L1 L2 S).trans (P_le_normalizer_centerOf_dsQ_left L1 L2 S))) :
    p * x * p⁻¹ ∈ fixedModSubgroup (dsQ L1 L2 S) (centerOf (dsQ L1 L2 S)) k
      ((dsQ_le_P_left L1 L2 S).trans (P_le_normalizer_centerOf_dsQ_left L1 L2 S)) := by
  rw [CFSG.GroupTheory.mem_fixedModSubgroup] at hx
  rcases hx with ⟨hxQ, hxZ⟩
  have hpQ : p ∈ Subgroup.normalizer (dsQ L1 L2 S : Set G) :=
    P_le_normalizer_dsQ_left L1 L2 S hp
  have hpZ : p ∈ Subgroup.normalizer (centerOf (dsQ L1 L2 S) : Set G) :=
    P_le_normalizer_centerOf_dsQ_left L1 L2 S hp
  have hyQ : p * x * p⁻¹ ∈ dsQ L1 L2 S :=
    (Subgroup.mem_normalizer_iff.mp hpQ x).mp hxQ
  rw [CFSG.GroupTheory.mem_fixedModSubgroup]
  refine ⟨hyQ, ?_⟩
  set c := k * p * k⁻¹ * p⁻¹ with hcdef
  set y := p * x * p⁻¹ with hydef
  have hcQ : c ∈ dsQ L1 L2 S := hkc p hp
  have hkp : k * p = c * (p * k) := by
    rw [hcdef]
    group
  have hz : p * (k * x * k⁻¹ * x⁻¹) * p⁻¹ ∈ centerOf (dsQ L1 L2 S) :=
    (Subgroup.mem_normalizer_iff.mp hpZ _).mp hxZ
  have hkp_inv : p⁻¹ * k⁻¹ = k⁻¹ * p⁻¹ * c⁻¹ := by
    have h := congrArg Inv.inv hkp
    simpa [mul_inv_rev, mul_assoc] using h
  have hky : k * y * k⁻¹ = c * (p * (k * x * k⁻¹ * x⁻¹) * p⁻¹) * y * c⁻¹ := by
    rw [hydef]
    calc k * (p * x * p⁻¹) * k⁻¹ = (k * p) * x * p⁻¹ * k⁻¹ := by group
      _ = (c * (p * k)) * x * p⁻¹ * k⁻¹ := by rw [hkp]
      _ = c * p * k * x * (p⁻¹ * k⁻¹) := by group
      _ = c * p * k * x * (k⁻¹ * p⁻¹ * c⁻¹) := by rw [hkp_inv]
      _ = c * (p * (k * x * k⁻¹) * p⁻¹) * c⁻¹ := by group
      _ = c * (p * ((k * x * k⁻¹ * x⁻¹) * x) * p⁻¹) * c⁻¹ := by group
      _ = c * (p * (k * x * k⁻¹ * x⁻¹) * p⁻¹) * y * c⁻¹ := by
        rw [hydef]
        group
  have hφ : k * y * k⁻¹ * y⁻¹ =
      (p * (k * x * k⁻¹ * x⁻¹) * p⁻¹) * (c * y * c⁻¹ * y⁻¹) := by
    rw [hky]
    have h1 : (p * (k * x * k⁻¹ * x⁻¹) * p⁻¹) * c =
        c * (p * (k * x * k⁻¹ * x⁻¹) * p⁻¹) :=
      G24Vertex1.centerOf_dsQ_comm _ hz c hcQ
    calc c * (p * (k * x * k⁻¹ * x⁻¹) * p⁻¹) * y * c⁻¹ * y⁻¹
        = ((p * (k * x * k⁻¹ * x⁻¹) * p⁻¹) * c) * y * c⁻¹ * y⁻¹ := by
          rw [h1]
      _ = (p * (k * x * k⁻¹ * x⁻¹) * p⁻¹) * (c * y * c⁻¹ * y⁻¹) := by group
  rw [hφ]
  exact (centerOf (dsQ L1 L2 S)).mul_mem hz
    (G24Vertex1.commutator_mem_centerOf_dsQ hD c hcQ y hyQ)

theorem G24Vertex1.fixedModSubgroup_eq_centerOf [Finite G]
    {L1 L2 S : Subgroup G} (hF : F112HypW L1 L2 S) (h1 : VA5 L1) (h2 : VA5 L2)
    (hD : G24LocalData L1 L2 S) {k : G} (hkB : k ∈ bigB L1 L2 S)
    (hk3 : orderOf k = 3) (hkL : k ∉ L1)
    (hkc : ∀ x ∈ L1 ⊔ bigB L1 L2 S, ⁅k, x⁆ ∈ dsQ L1 L2 S) :
    fixedModSubgroup (dsQ L1 L2 S) (centerOf (dsQ L1 L2 S)) k
        ((dsQ_le_P_left L1 L2 S).trans (P_le_normalizer_centerOf_dsQ_left L1 L2 S)) =
      centerOf (dsQ L1 L2 S) := by
  let hQZ := (dsQ_le_P_left L1 L2 S).trans
    (P_le_normalizer_centerOf_dsQ_left L1 L2 S)
  let X := fixedModSubgroup (dsQ L1 L2 S) (centerOf (dsQ L1 L2 S)) k hQZ
  have hZX : centerOf (dsQ L1 L2 S) ≤ X :=
    CFSG.GroupTheory.le_fixedModSubgroup hQZ inf_le_left
      (P_le_normalizer_centerOf_dsQ_left L1 L2 S (Subgroup.mem_sup_right hkB))
  have hXQ : X ≤ dsQ L1 L2 S := fun x hx =>
    (CFSG.GroupTheory.mem_fixedModSubgroup.mp hx).1
  have hPX : L1 ⊔ bigB L1 L2 S ≤ Subgroup.normalizer (X : Set G) := by
    intro p hp
    exact Subgroup.mem_normalizer_fintype fun x hx =>
      conj_mem_fixedModSubgroup hD hkc hp hx
  rcases hD.irr_left X hZX hXQ hPX with hX | hX
  · exact hX
  · exfalso
    have htriv : ∀ x ∈ dsQ L1 L2 S, k * x * k⁻¹ * x⁻¹ ∈ centerOf (dsQ L1 L2 S) := by
      intro x hx
      have hxX : x ∈ X := by rw [hX]; exact hx
      exact (CFSG.GroupTheory.mem_fixedModSubgroup.mp
        (show x ∈ fixedModSubgroup (dsQ L1 L2 S) (centerOf (dsQ L1 L2 S)) k hQZ
          from hxX)).2
    obtain ⟨hQ2, -⟩ := hD.special_left.1
    have hkP : k ∈ L1 ⊔ bigB L1 L2 S :=
      (le_sup_right : bigB L1 L2 S ≤ L1 ⊔ bigB L1 L2 S) hkB
    have hkQ : k ∈ Subgroup.normalizer (dsQ L1 L2 S : Set G) :=
      P_le_normalizer_dsQ_left L1 L2 S hkP
    have hkZ : k ∈ Subgroup.normalizer (centerOf (dsQ L1 L2 S) : Set G) :=
      P_le_normalizer_centerOf_dsQ_left L1 L2 S hkP
    have hZn : ∀ q ∈ dsQ L1 L2 S, ∀ z ∈ centerOf (dsQ L1 L2 S),
        q * z * q⁻¹ ∈ centerOf (dsQ L1 L2 S) := by
      intro q hq z hz
      exact (Subgroup.mem_normalizer_iff.mp
        ((dsQ_le_P_left L1 L2 S).trans
          (P_le_normalizer_centerOf_dsQ_left L1 L2 S) hq) z).mp hz
    have hdec := CFSG.Quasithin.St84.exists_mul_mem_centralizer_of_acts_trivially
      (Q := dsQ L1 L2 S) (Z := centerOf (dsQ L1 L2 S)) (k := k)
      inf_le_left hQ2 hk3 hkQ hkZ hZn htriv
    let C : Subgroup G := dsQ L1 L2 S ⊓ Subgroup.centralizer ({k} : Set G)
    have hCZ : C ⊓ centerOf (dsQ L1 L2 S) = ⊥ := by
      refine le_antisymm ?_ bot_le
      intro x hx
      rw [Subgroup.mem_bot]
      have hx' : x ∈ centerOf (dsQ L1 L2 S) ⊓ Subgroup.centralizer ({k} : Set G) :=
        ⟨hx.2, hx.1.2⟩
      rw [inf_centerOf_centralizer hF h1 h2 hD hkB hkL] at hx'
      exact Subgroup.mem_bot.mp hx'
    have hCcommZ : ⁅C, C⁆ ≤ centerOf (dsQ L1 L2 S) :=
      (Subgroup.commutator_mono inf_le_left inf_le_left).trans
        hD.special_left.1.commutator_le_centerOf
    have hCcommBot : ⁅C, C⁆ = ⊥ := by
      refine le_antisymm ?_ bot_le
      have hle : ⁅C, C⁆ ≤ C ⊓ centerOf (dsQ L1 L2 S) :=
        le_inf (Subgroup.commutator_le_self C) hCcommZ
      rwa [hCZ] at hle
    haveI : IsMulCommutative C := by
      refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
      have h : ⁅(a : G), (b : G)⁆ ∈ (⊥ : Subgroup G) := by
        rw [← hCcommBot]
        exact Subgroup.commutator_mem_commutator a.2 b.2
      rw [Subgroup.mem_bot] at h
      exact commutatorElement_eq_one_iff_mul_comm.mp h
    refine G24Vertex1.not_forall_exists_mul_centerOf_left hD (H := (C : Set G))
      (fun a ha => ha.1) ?_ ?_
    · intro a ha b hb
      exact congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : C) ⟨b, hb⟩)
    · intro x hx
      obtain ⟨z, hz, a, ha, rfl⟩ := hdec x hx
      exact ⟨a, ha, z, hz, G24Vertex1.centerOf_dsQ_comm z hz a ha.1⟩

theorem G24Vertex1.inf_centralizer_eq_bot [Finite G]
    {L1 L2 S : Subgroup G} (hF : F112HypW L1 L2 S) (h1 : VA5 L1) (h2 : VA5 L2)
    (hD : G24LocalData L1 L2 S) {k : G} (hkB : k ∈ bigB L1 L2 S)
    (hk3 : orderOf k = 3) (hkL : k ∉ L1)
    (hfix : ∀ x ∈ dsQ L1 L2 S,
      k * x * k⁻¹ * x⁻¹ ∈ centerOf (dsQ L1 L2 S) → x ∈ centerOf (dsQ L1 L2 S)) :
    dsQ L1 L2 S ⊓ Subgroup.centralizer ({k} : Set G) = ⊥ := by
  have hZfix : ∀ z ∈ centerOf (dsQ L1 L2 S), k * z * k⁻¹ = z → z = 1 := by
    intro z hz hfixz
    have hzC : z ∈ Subgroup.centralizer ({k} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc z * k = (k * z * k⁻¹) * k := by rw [hfixz]
        _ = k * z := by group
    have hmem : z ∈ centerOf (dsQ L1 L2 S) ⊓ Subgroup.centralizer ({k} : Set G) :=
      ⟨hz, hzC⟩
    rw [inf_centerOf_centralizer hF h1 h2 hD hkB hkL] at hmem
    exact Subgroup.mem_bot.mp hmem
  have hkP : k ∈ L1 ⊔ bigB L1 L2 S :=
    (le_sup_right : bigB L1 L2 S ≤ L1 ⊔ bigB L1 L2 S) hkB
  exact CFSG.Quasithin.St84.centralizer_eq_bot_of_fpf
    (P_le_normalizer_dsQ_left L1 L2 S hkP) hZfix hfix

theorem G24Vertex1.exists_mul_centralizer [Finite G]
    {L1 L2 S : Subgroup G} (hD : G24LocalData L1 L2 S) {k : G}
    (hkB : k ∈ bigB L1 L2 S) (hk3 : orderOf k = 3)
    (hkc : ∀ x ∈ L1 ⊔ bigB L1 L2 S, ⁅k, x⁆ ∈ dsQ L1 L2 S) :
    ∀ x ∈ L1 ⊔ bigB L1 L2 S, ∃ q ∈ dsQ L1 L2 S,
      ∃ c ∈ (L1 ⊔ bigB L1 L2 S) ⊓ Subgroup.centralizer ({k} : Set G), x = q * c := by
  have hkP : k ∈ L1 ⊔ bigB L1 L2 S :=
    (le_sup_right : bigB L1 L2 S ≤ L1 ⊔ bigB L1 L2 S) hkB
  have hQL : dsQ L1 L2 S ≤ L1 ⊔ bigB L1 L2 S := dsQ_le_P_left L1 L2 S
  have hLQ : L1 ⊔ bigB L1 L2 S ≤ Subgroup.normalizer (dsQ L1 L2 S : Set G) :=
    P_le_normalizer_dsQ_left L1 L2 S
  have hHQ : Subgroup.zpowers k ≤ Subgroup.normalizer (dsQ L1 L2 S : Set G) :=
    (Subgroup.zpowers_le.mpr hkP).trans hLQ
  have hcop : Nat.Coprime (Nat.card ↥(Subgroup.zpowers k))
      (Nat.card ↥(dsQ L1 L2 S)) := by
    rw [Nat.card_zpowers, hk3, hD.card_dsQ_left]
    norm_num
  have hcommSub : ⁅L1 ⊔ bigB L1 L2 S, Subgroup.zpowers k⁆ ≤ dsQ L1 L2 S :=
    CFSG.GroupTheory.commutator_zpowers_le_of_forall_mem (A := L1 ⊔ bigB L1 L2 S)
      (N := dsQ L1 L2 S) (c := k) (P_le_normalizer_dsQ_left L1 L2 S hkP) (fun a ha => by
        have h := hkc a ha
        rw [← commutatorElement_inv]
        exact (dsQ L1 L2 S).inv_mem h)
  have hcomm : ∀ h ∈ Subgroup.zpowers k, ∀ l ∈ L1 ⊔ bigB L1 L2 S,
      h * l * h⁻¹ * l⁻¹ ∈ dsQ L1 L2 S := by
    intro h hh l hl
    have hc := Subgroup.commutator_le.mp hcommSub l hl h hh
    have he : ⁅l, h⁆⁻¹ = h * l * h⁻¹ * l⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [← he]
    exact (dsQ L1 L2 S).inv_mem hc
  intro x hx
  obtain ⟨q, hq, c, hc, rfl⟩ :=
    CFSG.Quasithin.F112R.St84.exists_mul_mem_inf_centralizer_of_coprime
      hQL hLQ hHQ hcop hcomm hx
  refine ⟨q, hq, c, ?_, rfl⟩
  rw [CFSG.centralizer_zpowers_eq_centralizer_singleton k] at hc
  exact hc

theorem G24Vertex1.card_centralizer [Finite G]
    {L1 L2 S : Subgroup G} (hF : F112HypW L1 L2 S) (h1 : VA5 L1)
    (hD : G24LocalData L1 L2 S) {k : G}
    (hdec : ∀ x ∈ L1 ⊔ bigB L1 L2 S, ∃ q ∈ dsQ L1 L2 S,
      ∃ c ∈ (L1 ⊔ bigB L1 L2 S) ⊓ Subgroup.centralizer ({k} : Set G), x = q * c)
    (hinf : dsQ L1 L2 S ⊓ Subgroup.centralizer ({k} : Set G) = ⊥) :
    Nat.card ↥((L1 ⊔ bigB L1 L2 S) ⊓ Subgroup.centralizer ({k} : Set G)) = 180 := by
  have hsup : dsQ L1 L2 S ⊔
      ((L1 ⊔ bigB L1 L2 S) ⊓ Subgroup.centralizer ({k} : Set G)) =
      L1 ⊔ bigB L1 L2 S := by
    refine le_antisymm (sup_le ?_ inf_le_left) ?_
    · exact dsQ_le_P_left L1 L2 S
    intro x hx
    obtain ⟨q, hq, c, hc, rfl⟩ := hdec x hx
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hq) (Subgroup.mem_sup_right hc)
  have hdisj : Disjoint (dsQ L1 L2 S)
      ((L1 ⊔ bigB L1 L2 S) ⊓ Subgroup.centralizer ({k} : Set G)) := by
    rw [disjoint_iff]
    refine le_antisymm ?_ bot_le
    calc dsQ L1 L2 S ⊓ ((L1 ⊔ bigB L1 L2 S) ⊓ Subgroup.centralizer ({k} : Set G))
        ≤ dsQ L1 L2 S ⊓ Subgroup.centralizer ({k} : Set G) := inf_le_inf_left _ inf_le_right
      _ = ⊥ := hinf
  have hnorm : ((L1 ⊔ bigB L1 L2 S) ⊓ Subgroup.centralizer ({k} : Set G)) ≤
      Subgroup.normalizer (dsQ L1 L2 S : Set G) :=
    inf_le_left.trans (P_le_normalizer_dsQ_left L1 L2 S)
  have hcard := CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
    (dsQ L1 L2 S) ((L1 ⊔ bigB L1 L2 S) ⊓ Subgroup.centralizer ({k} : Set G)) hnorm hdisj
  rw [hsup, G24LocalData.card_vertex_left hF h1 hD, hD.card_dsQ_left] at hcard
  have h1' : 2 ^ 10 * Nat.card ↥((L1 ⊔ bigB L1 L2 S) ⊓
      Subgroup.centralizer ({k} : Set G)) = 2 ^ 10 * 180 := by
    rw [← hcard]
    norm_num
  exact Nat.eq_of_mul_eq_mul_left (by norm_num) h1'

end CFSG.Quasithin.F112R.St84
