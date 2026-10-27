module

public import CFSG.RankThree.GF2n.Tim81.Sec7.S73Bar
import CFSG.RankThree.GF2n.Tim81.Sec4.CentralQuot
import CFSG.GroupTheory.CommutingConjugatePair

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Tim78
open CFSG.RankThree.GF2n.Tim81.Sec7 (yOf rOf oOf)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M V : Subgroup G}

namespace EpsIn

variable {h : G} (hE : EpsIn M V h)

private theorem conjSubgroup_normalizer_conj_oOf {y : G} :
    conjSubgroup y (rOf M h) ≤ Subgroup.normalizer (conjSubgroup y (oOf M h) : Set G) := by
  have hRN : rOf M h ≤ Subgroup.normalizer (oOf M h : Set G) :=
    le_normalizer_map_subtype (rOf M h) (pPrimeCore 2 ↥(rOf M h))
  have hmap := Subgroup.map_mono (f := (MulAut.conj y).toMonoidHom) hRN
  rwa [Subgroup.map_equiv_normalizer_eq] at hmap

private theorem conjSubgroup_le_rOf (hE : EpsIn M V h) {y : G} (hy : y ∈ yOf h)
    (hc : ⁅V, conjSubgroup y V⁆ = ⊥) : conjSubgroup y V ≤ rOf M h := by
  have hVleC : V ≤ Subgroup.centralizer (conjSubgroup y V : Set G) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer
      (H₁ := V) (H₂ := conjSubgroup y V)).mp hc
  have hcomm : ∀ a ∈ V, ∀ b ∈ conjSubgroup y V, a * b = b * a := by
    intro a ha b hb
    exact (Subgroup.mem_centralizer_iff.mp (hVleC ha) b hb).symm
  have hVyM : conjSubgroup y V ≤ M := by
    have hC : conjSubgroup y V ≤ Subgroup.centralizer (V : Set G) := by
      intro b hb
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      exact hcomm a ha b hb
    calc conjSubgroup y V ≤ Subgroup.normalizer (V : Set G) :=
          hC.trans (Subgroup.centralizer_le_normalizer _)
      _ = M := hE.root.normalizer_eq
  exact le_inf hVyM (hE.conjSubgroup_le_yOf hy)

private theorem conj_oOf_le_rOf (hE : EpsIn M V h) {y : G} (hy : y ∈ yOf h)
    (hc : ⁅V, conjSubgroup y V⁆ = ⊥) : conjSubgroup y (oOf M h) ≤ rOf M h := by
  have hVleC : V ≤ Subgroup.centralizer (conjSubgroup y V : Set G) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer
      (H₁ := V) (H₂ := conjSubgroup y V)).mp hc
  have hVRy : V ≤ conjSubgroup y (rOf M h) := by
    have hVN : V ≤ Subgroup.normalizer (conjSubgroup y V : Set G) :=
      hVleC.trans (Subgroup.centralizer_le_normalizer _)
    have hVM : V ≤ conjSubgroup y M := by
      calc V ≤ Subgroup.normalizer (conjSubgroup y V : Set G) := hVN
        _ = conjSubgroup y (Subgroup.normalizer (V : Set G)) := normalizer_conjSubgroup y V
        _ = conjSubgroup y M := by rw [hE.root.normalizer_eq]
    rw [show conjSubgroup y (rOf M h) =
        conjSubgroup y M ⊓ yOf h by
      rw [rOf, conjSubgroup_inf,
        conjSubgroup_eq_self_iff.mpr (Subgroup.le_normalizer hy)]]
    exact le_inf hVM hE.le_yOf
  have hRyY : conjSubgroup y (rOf M h) ≤ yOf h := by
    rintro z ⟨r, hr, rfl⟩
    exact (yOf h).mul_mem ((yOf h).mul_mem hy (rOf_le_yOf (M := M) (h := h) hr))
      ((yOf h).inv_mem hy)
  have hOyY : conjSubgroup y (oOf M h) ≤ yOf h :=
    (Subgroup.map_mono (oOf_le_rOf (M := M) (h := h))).trans hRyY
  have hRyN : conjSubgroup y (rOf M h) ≤
      Subgroup.normalizer (conjSubgroup y (oOf M h) : Set G) :=
    conjSubgroup_normalizer_conj_oOf
  have hnormOy : V ≤ Subgroup.normalizer (conjSubgroup y (oOf M h) : Set G) :=
    hVRy.trans hRyN
  have hOyodd : Odd (Nat.card (conjSubgroup y (oOf M h))) := by
    rw [card_conjSubgroup]
    exact hE.odd_oOf
  have hCV : conjSubgroup y (oOf M h) ≤ Subgroup.centralizer (V : Set G) :=
    CentralTI.le_centralizer_of_odd_card (T := V) (O := conjSubgroup y (oOf M h))
      hE.root.elem hE.root.four_le_card hE.root.ti hnormOy hOyodd
  exact le_inf (hCV.trans ((Subgroup.centralizer_le_normalizer _).trans_eq hE.root.normalizer_eq))
    hOyY

private theorem conj_oOf_commute_p0_inf_centralizer (hE : EpsIn M V h) {y : G}
    (hy : y ∈ yOf h) (hOyR : conjSubgroup y (oOf M h) ≤ rOf M h)
    {P0 : Subgroup G} (hP0_2 : IsPGroup 2 P0) (hP0_R : P0 ≤ rOf M h)
    (hR_NP0 : rOf M h ≤ Subgroup.normalizer (P0 : Set G))
    {o c : G} (ho : o ∈ conjSubgroup y (oOf M h)) (hcP0 : c ∈ P0)
    (hcC : c ∈ Subgroup.centralizer (conjSubgroup y V : Set G)) :
    o * c = c * o := by
  have hOyodd : Odd (Nat.card (conjSubgroup y (oOf M h))) := by
    rw [card_conjSubgroup]
    exact hE.odd_oOf
  have hoR : o ∈ rOf M h := hOyR ho
  have hcY : c ∈ yOf h := rOf_le_yOf (M := M) (h := h) (hP0_R hcP0)
  have hcN : c ∈ Subgroup.normalizer (conjSubgroup y V : Set G) :=
    Subgroup.centralizer_le_normalizer (conjSubgroup y V : Set G) hcC
  have hcMy : c ∈ conjSubgroup y M := by
    rw [normalizer_conjSubgroup y V, hE.root.normalizer_eq] at hcN
    exact hcN
  have hC_le_Ry : c ∈ conjSubgroup y (rOf M h) := by
    rw [show conjSubgroup y (rOf M h) = conjSubgroup y M ⊓ yOf h by
      rw [rOf, conjSubgroup_inf,
        conjSubgroup_eq_self_iff.mpr (Subgroup.le_normalizer hy)]]
    exact ⟨hcMy, hcY⟩
  have hC_N_Oy : c ∈ Subgroup.normalizer (conjSubgroup y (oOf M h) : Set G) :=
    conjSubgroup_normalizer_conj_oOf hC_le_Ry
  have hOy_N_P0 : o ∈ Subgroup.normalizer (P0 : Set G) := hR_NP0 hoR
  have h1 : ⁅Subgroup.zpowers c, Subgroup.zpowers o⁆ ≤ conjSubgroup y (oOf M h) := by
    have hCN : Subgroup.zpowers c ≤
        Subgroup.normalizer (conjSubgroup y (oOf M h) : Set G) :=
      Subgroup.zpowers_le.mpr hC_N_Oy
    have h : ⁅Subgroup.zpowers c, conjSubgroup y (oOf M h)⁆ ≤
        conjSubgroup y (oOf M h) :=
      Subgroup.le_normalizer_iff_commutator_le_right.mp hCN
    exact (Subgroup.commutator_mono le_rfl (Subgroup.zpowers_le.mpr ho)).trans h
  have h2 : ⁅Subgroup.zpowers c, Subgroup.zpowers o⁆ ≤ P0 := by
    have hON : Subgroup.zpowers o ≤ Subgroup.normalizer (P0 : Set G) :=
      Subgroup.zpowers_le.mpr hOy_N_P0
    have h : ⁅Subgroup.zpowers o, P0⁆ ≤ P0 :=
      Subgroup.le_normalizer_iff_commutator_le_right.mp hON
    calc ⁅Subgroup.zpowers c, Subgroup.zpowers o⁆ =
        ⁅Subgroup.zpowers o, Subgroup.zpowers c⁆ := Subgroup.commutator_comm _ _
      _ ≤ ⁅Subgroup.zpowers o, P0⁆ :=
        Subgroup.commutator_mono le_rfl (Subgroup.zpowers_le.mpr hcP0)
      _ ≤ P0 := h
  have hdisj : conjSubgroup y (oOf M h) ⊓ P0 = ⊥ := by
    rw [inf_comm]
    exact CFSG.GroupTheory.inf_eq_bot_of_isPGroup_two_of_odd hP0_2 hOyodd
  have hbot : ⁅Subgroup.zpowers c, Subgroup.zpowers o⁆ = ⊥ := by
    apply le_bot_iff.mp
    exact (le_inf h1 h2).trans (le_of_eq hdisj)
  have hcent : c ∈ Subgroup.centralizer (Subgroup.zpowers o : Set G) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot) (Subgroup.mem_zpowers c)
  exact Subgroup.mem_centralizer_iff.mp hcent o (Subgroup.mem_zpowers o)

private theorem conj_oOf_commute_conj_V (hE : EpsIn M V h) {y a b : G}
    (ha : a ∈ conjSubgroup y (oOf M h)) (hb : b ∈ conjSubgroup y V) :
    a * b = b * a := by
  have ho : y⁻¹ * a * y ∈ oOf M h := mem_conjSubgroup.mp ha
  have hv : y⁻¹ * b * y ∈ V := mem_conjSubgroup.mp hb
  have h := hE.oOf_commute_V ho hv
  calc a * b = y * ((y⁻¹ * a * y) * (y⁻¹ * b * y)) * y⁻¹ := by group
    _ = y * ((y⁻¹ * b * y) * (y⁻¹ * a * y)) * y⁻¹ := by rw [h]
    _ = b * a := by group

private theorem conj_oOf_le_oOf (hE : EpsIn M V h) {y : G}
    (hOyOV : conjSubgroup y (oOf M h) ≤ oOf M h ⊔ V) :
    conjSubgroup y (oOf M h) ≤ oOf M h := by
  have hOyodd : Odd (Nat.card (conjSubgroup y (oOf M h))) := by
    rw [card_conjSubgroup]
    exact hE.odd_oOf
  have hdisj : V ⊓ oOf M h = ⊥ :=
    CFSG.GroupTheory.inf_eq_bot_of_isPGroup_two_of_odd hE.root.isPGroup_V hE.odd_oOf
  intro z hz
  have hzOV : z ∈ oOf M h ⊔ V := by
    have := hOyOV hz
    simpa [sup_comm] using this
  have hzodd : Odd (orderOf z) :=
    hOyodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard _ hz)
  have hOVnorm : V ≤ Subgroup.normalizer (oOf M h : Set G) :=
    hE.le_rOf.trans (le_normalizer_map_subtype (rOf M h) (pPrimeCore 2 ↥(rOf M h)))
  obtain ⟨o, ho, v, hv, hzv⟩ := exists_mul_of_mem_sup hOVnorm hzOV
  have hcomm : Commute o v := hE.oOf_commute_V ho hv
  have hv2 : v * v = 1 := by
    have := hE.root.elem.2 v hv
    rwa [pow_two] at this
  have hvn : v ^ orderOf z = 1 := by
    have hord : orderOf z = orderOf (o * v) := congrArg orderOf hzv
    rw [hord]
    have hzn : o ^ orderOf (o * v) * v ^ orderOf (o * v) = 1 := by
      have h := pow_orderOf_eq_one (o * v)
      rw [hcomm.mul_pow] at h
      exact h
    have ho_pow : o ^ orderOf (o * v) ∈ oOf M h := (oOf M h).pow_mem ho _
    have hv_pow : v ^ orderOf (o * v) ∈ V := V.pow_mem hv _
    have heq : o ^ orderOf (o * v) = (v ^ orderOf (o * v))⁻¹ := by
      rw [eq_inv_iff_mul_eq_one]
      simpa [mul_comm] using hzn
    have hmem : o ^ orderOf (o * v) ∈ V := by
      rw [heq]
      exact V.inv_mem hv_pow
    have hbot : o ^ orderOf (o * v) ∈ (⊥ : Subgroup G) := by
      rw [← hdisj]
      exact Subgroup.mem_inf.mpr ⟨hmem, ho_pow⟩
    have ho1 : o ^ orderOf (o * v) = 1 := Subgroup.mem_bot.mp hbot
    rw [ho1, one_mul] at hzn
    exact hzn
  have hv1 : v = 1 := by
    have hdvd : orderOf v ∣ orderOf z := orderOf_dvd_of_pow_eq_one hvn
    have hdvd2 : orderOf v ∣ 2 :=
      orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hv2)
    have hcop : Nat.Coprime (orderOf z) 2 := hzodd.coprime_two_right
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop hdvd hdvd2)
  rw [hzv, hv1, mul_one]
  exact ho

theorem conj_oOf_eq (hE : EpsIn M V h) {y : G} (hy : y ∈ yOf h)
    (hc : ⁅V, conjSubgroup y V⁆ = ⊥) : conjSubgroup y (oOf M h) = oOf M h := by
  have hVyR := conjSubgroup_le_rOf hE hy hc
  have hOyR := conj_oOf_le_rOf hE hy hc
  have hOyodd : Odd (Nat.card (conjSubgroup y (oOf M h))) := by
    rw [card_conjSubgroup]
    exact hE.odd_oOf
  set P0 : Subgroup G := p0Of M V (Subgroup.zpowers h) with hP0
  have hP0_2 : IsPGroup 2 P0 := by
    rw [hP0, p0Of]
    exact (inSubgroup_pCore_two M).1.to_le (inf_le_left.trans inf_le_left)
  have hP0_R : P0 ≤ rOf M h := by
    rw [hP0]
    exact le_inf (inf_le_left.trans hE.root.Pc_le_M) inf_le_right
  have hR_NP0 : rOf M h ≤ Subgroup.normalizer (P0 : Set G) := by
    intro r hr
    obtain ⟨hrM, hrY⟩ := Subgroup.mem_inf.mp hr
    exact mem_normalizer_inf (hE.root.le_normalizer_Pc hrM) (Subgroup.le_normalizer hrY)
  have hOy_le_C : conjSubgroup y (oOf M h) ≤ cenOf P0 := by
    intro a ha
    have hoddA : Odd (orderOf a) :=
      hOyodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard _ ha)
    have hB2 : IsPGroup 2 (conjSubgroup y V) :=
      hE.root.isPGroup_V.map (MulAut.conj y).toMonoidHom
    have hcomm : ∀ q ∈ P0, a * q = q * a :=
      CFSG.RankThree.GF2n.Tim78.commute_of_thompson_A_times_B hP0_2 hB2
        (hR_NP0 (hOyR ha)) (hVyR.trans hR_NP0) hoddA
        (fun b hb => conj_oOf_commute_conj_V hE ha hb)
        (fun q hq hqcomm => conj_oOf_commute_p0_inf_centralizer hE hy hOyR hP0_2
          hP0_R hR_NP0 ha hq (Subgroup.mem_centralizer_iff.mpr fun b hb => (hqcomm b hb).symm))
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    exact (hcomm q hq).symm
  have hOy_OV : conjSubgroup y (oOf M h) ≤ oOf M h ⊔ V := by
    rw [← hE.cen]
    exact le_inf hOyR hOy_le_C
  have hOyO := conj_oOf_le_oOf hE hOy_OV
  have heq : conjSubgroup y (oOf M h) = oOf M h :=
    Subgroup.eq_of_le_of_card_ge hOyO (by rw [card_conjSubgroup])
  exact heq

private theorem inv_mem_normalizer_of_conj_mem_rOf (hE : EpsIn M V h) {u k : G}
    (hu : u ∈ V) (hkY : k ∈ yOf h) (hkR : k⁻¹ * u * k ∈ rOf M h)
    (hk1 : k⁻¹ * u * k ≠ 1) :
    k⁻¹ ∈ Subgroup.normalizer (oOf M h : Set G) := by
  have hkV : k⁻¹ * u * k ∈ conjSubgroup k⁻¹ V := by
    rw [mem_conjSubgroup]
    rw [show (k⁻¹)⁻¹ * (k⁻¹ * u * k) * k⁻¹ = u by group]
    exact hu
  have hne : conjSubgroup k⁻¹ V ⊓ M ≠ ⊥ := by
    intro hbot
    have hmem' : k⁻¹ * u * k ∈ (⊥ : Subgroup G) := by
      rw [← hbot]
      exact Subgroup.mem_inf.mpr ⟨hkV, (Subgroup.mem_inf.mp hkR).1⟩
    exact hk1 (Subgroup.mem_bot.mp hmem')
  have hcomm := hE.root.commute_of_conj_inf_ne_bot hE.root.rootType hne
  have hcbot : ⁅V, conjSubgroup k⁻¹ V⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact (hcomm a ha b hb).symm
  have hkO : conjSubgroup k⁻¹ (oOf M h) = oOf M h :=
    hE.conj_oOf_eq (by simpa using hkY) hcbot
  exact conjSubgroup_eq_self_iff.mp hkO

private theorem exists_conj_mem_rOf_of_mem_normalizer (hE : EpsIn M V h) {u g : G}
    (hu : u ∈ V) (hu1 : u ≠ 1) (hg : g ∈ yOf h)
    (hmem : g⁻¹ * u * g ∈ Subgroup.normalizer (oOf M h : Set G)) :
    ∃ c ∈ Subgroup.normalizer (oOf M h : Set G), c ∈ yOf h ∧
      c * (g⁻¹ * u * g) * c⁻¹ ∈ rOf M h := by
  obtain ⟨S, -, hSR, -, -, -, -⟩ := hE.exists_sylow
  let Y := ↥(yOf h)
  let N : Subgroup G := Subgroup.normalizer (oOf M h : Set G)
  let K : Subgroup Y := N.subgroupOf (yOf h)
  let x : G := g⁻¹ * u * g
  have hxY : x ∈ yOf h :=
    (yOf h).mul_mem ((yOf h).mul_mem ((yOf h).inv_mem hg) (hE.le_yOf hu)) hg
  let xY : Y := ⟨x, hxY⟩
  have hu2 : u * u = 1 := by
    simpa [pow_two] using hE.root.elem.2 u hu
  have hx2 : x * x = 1 := by
    calc x * x = g⁻¹ * (u * u) * g := by
          rw [show x = g⁻¹ * u * g from rfl]; group
      _ = 1 := by rw [hu2]; group
  have hxne : x ≠ 1 := by
    intro hx1
    apply hu1
    have := congrArg (fun z => g * z * g⁻¹) hx1
    simpa [x, mul_assoc] using this
  have hord : orderOf xY = 2 := by
    rw [← Subgroup.orderOf_coe]
    simpa [xY] using orderOf_eq_prime (p := 2) (by rwa [pow_two]) hxne
  have hW : IsPGroup 2 (Subgroup.zpowers xY) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hord, pow_one]
  have hSK : (S : Subgroup Y) ≤ K := by
    intro s hs
    exact Subgroup.mem_subgroupOf.mpr
      (le_normalizer_map_subtype (rOf M h) (pPrimeCore 2 ↥(rOf M h))
        (hSR (Subgroup.mem_map_of_mem (yOf h).subtype hs)))
  have hWK : Subgroup.zpowers xY ≤ K := by
    intro w hw
    exact Subgroup.mem_subgroupOf.mpr (by
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
      exact N.zpow_mem hmem n)
  obtain ⟨c, hcK, hcW⟩ := CFSG.QuasiDihedralFusion.exists_conj_le_sylow K S hSK
    (Subgroup.zpowers xY) hWK hW
  have hcxS : c * xY * c⁻¹ ∈ (S : Subgroup Y) := by
    have hmemW : xY ∈ Subgroup.zpowers xY := Subgroup.mem_zpowers xY
    have := hcW (Subgroup.mem_map_of_mem (MulAut.conj c).toMonoidHom hmemW)
    simpa [MulAut.conj_apply] using this
  have hcR : c * (g⁻¹ * u * g) * c⁻¹ ∈ rOf M h := by
    have hh := hSR (Subgroup.mem_map_of_mem (yOf h).subtype hcxS)
    change ((c * xY * c⁻¹ : Y) : G) ∈ rOf M h
    exact hh
  exact ⟨c, Subgroup.mem_subgroupOf.mp hcK, c.2, hcR⟩

theorem conj_mem_normalizer_oOf_iff (hE : EpsIn M V h) {u g : G} (hu : u ∈ V)
    (hu1 : u ≠ 1) (hg : g ∈ yOf h) :
    g⁻¹ * u * g ∈ Subgroup.normalizer (oOf M h : Set G) ↔
      g ∈ Subgroup.normalizer (oOf M h : Set G) := by
  constructor
  · intro hmem
    obtain ⟨c, hcN, hcY, hcR⟩ := exists_conj_mem_rOf_of_mem_normalizer hE hu hu1 hg hmem
    let k : G := g * c⁻¹
    have hkY : k ∈ yOf h := (yOf h).mul_mem hg ((yOf h).inv_mem hcY)
    have hkux : k⁻¹ * u * k = c * (g⁻¹ * u * g) * c⁻¹ := by
      change (g * c⁻¹)⁻¹ * u * (g * c⁻¹) = c * (g⁻¹ * u * g) * c⁻¹
      group
    have hkR : k⁻¹ * u * k ∈ rOf M h := by rw [hkux]; exact hcR
    have hk1 : k⁻¹ * u * k ≠ 1 := by
      intro h
      apply hu1
      rw [show u = k * (k⁻¹ * u * k) * k⁻¹ by group, h, mul_one, mul_inv_cancel]
    have hkNin : k⁻¹ ∈ Subgroup.normalizer (oOf M h : Set G) :=
      inv_mem_normalizer_of_conj_mem_rOf hE hu hkY hkR hk1
    have hkN : k ∈ Subgroup.normalizer (oOf M h : Set G) := by
      simpa using (Subgroup.normalizer (oOf M h : Set G)).inv_mem hkNin
    have hgN : g ∈ Subgroup.normalizer (oOf M h : Set G) := by
      have : g = k * c := by
        rw [show k = g * c⁻¹ from rfl]
        group
      rw [this]
      exact (Subgroup.normalizer (oOf M h : Set G)).mul_mem hkN hcN
    exact hgN
  · intro hgN
    have huN : u ∈ Subgroup.normalizer (oOf M h : Set G) := by
      have huR : u ∈ rOf M h := hE.le_rOf hu
      exact le_normalizer_map_subtype (rOf M h) (pPrimeCore 2 ↥(rOf M h)) huR
    have hg'inv : g⁻¹ ∈ Subgroup.normalizer (oOf M h : Set G) :=
      (Subgroup.normalizer (oOf M h : Set G)).inv_mem hgN
    exact (Subgroup.normalizer (oOf M h : Set G)).mul_mem
      ((Subgroup.normalizer (oOf M h : Set G)).mul_mem hg'inv huN) hgN


end EpsIn

end CFSG.RankThree.GF2n.Tim81
