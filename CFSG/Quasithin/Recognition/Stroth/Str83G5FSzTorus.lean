module

public import CFSG.Quasithin.Recognition.Stroth.Str83G5FVertex
public import CFSG.Quasithin.Background.RonanF13Hall
import CFSG.LieType.Ree.SuzukiBorelHall
import CFSG.Quasithin.Recognition.Stroth.Str83CartanTools
public import CFSG.GroupTheory.CommutingConjugatePair
public import CFSG.Quasithin.Vol2.Ch8Sec2L828E34Suz

public section

namespace CFSG.Quasithin.Stroth.G5F

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F112R
open CFSG.GH74.Uniqueness.Bender CFSG.Blueprint CFSG.LieType.Ree

variable {G : Type} [Group G] [Finite G] {L1 L2 S : Subgroup G} {a : ℕ}

theorem borelOf_le_normalizer_of_sz (hF : Hyp111 L1 L2 S)
    (hB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G)) (ha : 1 ≤ a)
    (hSz : Nonempty (oTwoQuot ↥L1 ≃* Sz a)) :
    borelOf L1 S ≤ Subgroup.normalizer (S : Set G) := by
  have hS1 : S = (S ⊓ L1) ⊔ Q1 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_left hF hB (Or.inl ⟨a, ha, hSz⟩)
  conv_rhs => rw [hS1]
  refine F1.le_normalizer_sup (F1.borelOf_le_normalizer L1 S) ?_
  exact (F1.borelOf_le L1 S).trans
    (le_sup_left.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (P1 L1 L2 S)))

theorem exists_vertexEquiv_torus {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (hF : Hyp111 L1 L2 S)
    (hB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G)) (ha : 1 ≤ a)
    (hSz : Nonempty (oTwoQuot ↥L1 ≃* Sz a))
    {D : Subgroup G} (hD : RonanF13.HallTwoPrime D (borelOf L1 S))
    (hBD : borelOf L1 S = (S ⊓ L1) ⊔ D) {l : Kˣ} (hl : orderOf l = 2 ^ (2 * a + 1) - 1) :
    ∃ (e : oTwoQuot ↥(L1 ⊔ S) ≃* suzukiGroup a K) (d₁ : ↥(L1 ⊔ S)),
      (szSbar L1 L2 S).map e.toMonoidHom = suzukiU a K ∧
      Subgroup.zpowers (d₁ : G) = D ∧ orderOf (d₁ : G) = 2 ^ (2 * a + 1) - 1 ∧
      e (QuotientGroup.mk' (CFSG.pCore 2 ↥(L1 ⊔ S)) d₁) = suzukiDElt a K l := by
  classical
  obtain ⟨-, -, -, e0, he0⟩ := sz_vertex hK hF hB ha hSz
  have hBt : BenderType (oTwoQuot ↥L1) (2 * a + 1) 2 1 :=
    BenderType.suzuki a ha (Classical.choice hSz |>.trans
      (MulEquiv.subgroupCongr (szModel_eq_open_sz a).symm))
  obtain ⟨hDcard, hDcyc⟩ := card_isCyclic_of_hallTwoPrime hF.h1.sylow hD hBD hBt
  haveI : IsCyclic ↥D := hDcyc
  obtain ⟨gD, hgDord⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := ↥D)
  let g : G := (gD : D)
  have hgD : g ∈ D := gD.2
  have hgord : orderOf g = Nat.card D := (Subgroup.orderOf_coe gD).trans hgDord
  have hoddg : Odd (orderOf g) := by
    rw [hgord]
    exact hD.2.1
  have hgB1 : g ∈ borelOf L1 S := hD.1 hgD
  have hgNS : g ∈ Subgroup.normalizer (S : Set G) :=
    borelOf_le_normalizer_of_sz hF hB ha hSz hgB1
  have hgH : g ∈ L1 ⊔ S := Subgroup.mem_sup_left (F1.borelOf_le L1 S hgB1)
  let H : Subgroup G := L1 ⊔ S
  let gH : ↥H := ⟨g, hgH⟩
  let π : ↥H →* oTwoQuot ↥H := QuotientGroup.mk' (pCore 2 ↥H)
  let ψ0 : ↥H →* suzukiGroup a K := e0.toMonoidHom.comp π
  have hgNH : gH ∈ Subgroup.normalizer ((S.subgroupOf H : Subgroup ↥H) : Set ↥H) := by
    have h1 : gH ∈ (Subgroup.normalizer (S : Set G)).subgroupOf H :=
      Subgroup.mem_subgroupOf.mpr hgNS
    rwa [Subgroup.subgroupOf_normalizer_eq (le_sup_right : S ≤ H)] at h1
  have hqN : π gH ∈ Subgroup.normalizer
      ((S.subgroupOf H).map π : Set (oTwoQuot ↥H)) :=
    Subgroup.le_normalizer_map π (Subgroup.mem_map_of_mem _ hgNH)
  have hψ0NU : ψ0 gH ∈ Subgroup.normalizer (suzukiU a K : Set (suzukiGroup a K)) := by
    have h := Subgroup.le_normalizer_map e0.toMonoidHom (Subgroup.mem_map_of_mem _ hqN)
    have hmap : ((S.subgroupOf H).map π).map e0.toMonoidHom = suzukiU a K := by
      simpa [π, szSbar] using he0
    rwa [hmap] at h
  have hψ0B : ψ0 gH ∈ suzukiB a K := by
    rw [← CFSG.Quasithin.H13.normalizer_suzukiU_e34 hK]
    exact hψ0NU
  have hψ0odd : Odd (orderOf (ψ0 gH)) := by
    have hdvd : orderOf (ψ0 gH) ∣ orderOf gH := orderOf_map_dvd ψ0 gH
    refine Odd.of_dvd_nat ?_ hdvd
    rwa [Subgroup.orderOf_mk g hgH]
  obtain ⟨v, hvB, hvT⟩ :=
    exists_conj_mem_suzukiT_of_mem_suzukiB_of_odd hK hψ0B hψ0odd
  have hvNU : v ∈ Subgroup.normalizer (suzukiU a K : Set (suzukiGroup a K)) := by
    rw [CFSG.Quasithin.H13.normalizer_suzukiU_e34 hK]
    exact hvB
  let e : oTwoQuot ↥H ≃* suzukiGroup a K := e0.trans (MulAut.conj v)
  let ψ : ↥H →* suzukiGroup a K := e.toMonoidHom.comp π
  have he_map : (szSbar L1 L2 S).map e.toMonoidHom = suzukiU a K := by
    have hmap : (szSbar L1 L2 S).map e.toMonoidHom =
        ((szSbar L1 L2 S).map e0.toMonoidHom).map (MulAut.conj v).toMonoidHom := by
      rw [show e.toMonoidHom = (MulAut.conj v).toMonoidHom.comp e0.toMonoidHom from rfl,
        ← Subgroup.map_map]
    rw [hmap, he0]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp hvNU
  have hψgT : ψ gH ∈ suzukiT a K := by
    have h1 : ψ gH = v * ψ0 gH * v⁻¹ := by
      simp [ψ, ψ0, e, MulAut.conj_apply]
    rw [h1]
    exact hvT
  have hDL : D ≤ H := hD.1.trans ((F1.borelOf_le L1 S).trans le_sup_left)
  let Dbar : Subgroup ↥H := D.subgroupOf H
  let gbar : ↥Dbar := ⟨gH, Subgroup.mem_subgroupOf.mpr hgD⟩
  let fD : ↥Dbar →* suzukiGroup a K := ψ.comp Dbar.subtype
  have hfDg : fD gbar = ψ gH := rfl
  have hfDgT : fD gbar ∈ suzukiT a K := by
    rw [hfDg]
    exact hψgT
  have hfD_inj : Function.Injective fD := by
    intro x y hxy
    have hπeq : π (x : ↥H) = π (y : ↥H) := e.injective hxy
    have hdiv : π (((x * y⁻¹ : ↥Dbar) : ↥H)) = 1 := by
      rw [show ((x * y⁻¹ : ↥Dbar) : ↥H) = (x : ↥H) * (y : ↥H)⁻¹ from rfl,
        map_mul, map_inv, hπeq, mul_inv_cancel]
    have hmem : ((x * y⁻¹ : ↥Dbar) : ↥H) ∈ pCore 2 ↥H :=
      (QuotientGroup.eq_one_iff _).mp hdiv
    have hmemG : (((x * y⁻¹ : ↥Dbar) : ↥H) : G) ∈ pCoreOf 2 (L1 ⊔ S) :=
      (F1.mem_pCore_iff_coe _).mp hmem
    have hmemD : (((x * y⁻¹ : ↥Dbar) : ↥H) : G) ∈ D := (x * y⁻¹).2
    have hbot : pCoreOf 2 (L1 ⊔ S) ⊓ D = ⊥ :=
      CFSG.GroupTheory.inf_eq_bot_of_isPGroup_two_of_odd
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (L1 ⊔ S)) hD.2.1
    have hmemInter : (((x * y⁻¹ : ↥Dbar) : ↥H) : G) ∈ pCoreOf 2 (L1 ⊔ S) ⊓ D :=
      ⟨hmemG, hmemD⟩
    rw [hbot] at hmemInter
    have hval : (((x * y⁻¹ : ↥Dbar) : ↥H) : G) = 1 := Subgroup.mem_bot.mp hmemInter
    have h1 : (x * y⁻¹ : ↥Dbar) = 1 := Subtype.ext (Subtype.ext hval)
    exact mul_inv_eq_one.mp (by simpa using h1)
  have hcardDbar : Nat.card ↥Dbar = Nat.card D :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDL).toEquiv
  have hcardRange : Nat.card (fD.range) = Nat.card D := by
    rw [show Nat.card (fD.range) = Nat.card (Set.range fD) from rfl,
      Nat.card_range_of_injective hfD_inj, hcardDbar]
  have hcardT : Nat.card (suzukiT a K) = 2 ^ (2 * a + 1) - 1 :=
    (suzuki_borel_structure hK).2.2.1
  have hgbarord : orderOf gbar = Nat.card ↥Dbar := by
    rw [← Subgroup.orderOf_coe gbar, Subgroup.orderOf_mk g hgH, hgord, ← hcardDbar]
  have hzgbar : Subgroup.zpowers gbar = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [Nat.card_zpowers, hgbarord]
  have hrangeT : fD.range ≤ suzukiT a K := by
    rintro y ⟨x, rfl⟩
    have hx : x ∈ Subgroup.zpowers gbar := by
      rw [hzgbar]
      exact Subgroup.mem_top x
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [← hn, map_zpow]
    exact (suzukiT a K).zpow_mem hfDgT n
  have hrange_eq : fD.range = suzukiT a K := by
    refine Subgroup.eq_of_le_of_card_ge hrangeT ?_
    rw [hcardT, hcardRange, hDcard]
  obtain ⟨dbar, hdbar⟩ : ∃ dbar : ↥Dbar, fD dbar = suzukiDElt a K l := by
    have hmem : suzukiDElt a K l ∈ fD.range := by
      rw [hrange_eq]
      exact suzukiDElt_mem_suzukiT a K l
    exact MonoidHom.mem_range.mp hmem
  let toT : Kˣ →* suzukiGroup a K :=
    { toFun := suzukiDElt a K
      map_one' := suzukiDElt_one
      map_mul' := fun x y => (suzukiDElt_mul x y).symm }
  have hordT : orderOf (suzukiDElt a K l) = orderOf l :=
    orderOf_injective toT (fun x y h => (suzukiDElt_inj hK).1 h) l
  have horddbar : orderOf dbar = 2 ^ (2 * a + 1) - 1 := by
    have h1 := (orderOf_injective fD hfD_inj dbar).symm
    rw [h1, hdbar, hordT, hl]
  have hord_out : orderOf (((dbar : ↥Dbar) : ↥H) : G) = 2 ^ (2 * a + 1) - 1 := by
    rw [Subgroup.orderOf_coe ((dbar : ↥Dbar) : ↥H), Subgroup.orderOf_coe dbar]
    exact horddbar
  have hzpowers : Subgroup.zpowers (((dbar : ↥Dbar) : ↥H) : G) = D := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr dbar.2) ?_
    rw [Nat.card_zpowers, hord_out]
    exact le_of_eq hDcard
  have hfinal : e (QuotientGroup.mk' (CFSG.pCore 2 ↥(L1 ⊔ S))
      ((dbar : ↥Dbar) : ↥H)) = suzukiDElt a K l := by
    change fD dbar = suzukiDElt a K l
    exact hdbar
  exact ⟨e, ((dbar : ↥Dbar) : ↥H), he_map, hzpowers, hord_out, hfinal⟩

end CFSG.Quasithin.Stroth.G5F

end
