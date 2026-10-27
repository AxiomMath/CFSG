module

public import CFSG.RankThree.GF2n.Tim81.Sec6.M0Basic

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M V : Subgroup G}

private theorem Sec5Hyp.exists_mul_of_mem_xOf (hS : Sec5Hyp M V) {g : G}
    (hg : conjSubgroup g V ∈ sigmaSet M V) {x : G}
    (hx : x ∈ Tim79a.xOf V (hOf M V g)) :
    ∃ a ∈ conjSubgroup g V, ∃ p ∈ Pc M V, x = a * p := by
  obtain ⟨y, hyH, -, hVy, -, -⟩ := hS.exists_conj_data hg
  have hR := hS.toRootHyp
  have hSg := hS.shape hg
  obtain ⟨F, hField, hFintype, hCharP, l, hl, ψ, hw⟩ := hSg.shape
  have hAW : conjSubgroup g V ≤ Tim79a.xOf V (hOf M V g) := by
    rw [hVy]
    exact conjSubgroup_le_xOf_of_mem hyH
  have hQN : Pc M V ⊓ Tim79a.xOf V (hOf M V g) ≤
      Subgroup.normalizer (conjSubgroup g V : Set G) := by
    refine le_normalizer_of_comm (X := Pc M V ⊓ Tim79a.xOf V (hOf M V g))
      (N := conjSubgroup g V) fun a ha b hb => ?_
    haveI : IsMulCommutative ↥(Tim79a.xOf V (hOf M V g)) := (hSg.isElemAbelian hR).1
    exact setLike_mul_comm (s := Tim79a.xOf V (hOf M V g)) ha.2 (hAW hb)
  have hbot : Pc M V ⊓ Tim79a.xOf V (hOf M V g) ⊓ conjSubgroup g V = ⊥ := by
    rw [inf_comm (Pc M V ⊓ Tim79a.xOf V (hOf M V g)) (conjSubgroup g V), ← inf_assoc,
      hS.inf_Pc_eq_bot hg, bot_inf_eq]
  have hcardW : Nat.card ↥(Tim79a.xOf V (hOf M V g)) = Nat.card V ^ 4 := by
    rw [hw.card_W, hw.card_V, ← pow_mul]
    congr 1
    omega
  have hprod := CFSG.QuasithinUnique.C5.card_sup_mul_card_inf_of_le_normalizer
    (A := Pc M V ⊓ Tim79a.xOf V (hOf M V g)) (B := conjSubgroup g V) hQN
  rw [hSg.card_inf_Pc_xOf hR, card_conjSubgroup g V, hbot, Subgroup.card_bot, mul_one]
    at hprod
  have hprod' : Nat.card ↥(conjSubgroup g V ⊔ (Pc M V ⊓ Tim79a.xOf V (hOf M V g))) =
      Nat.card V * Nat.card V ^ 3 := by
    rw [sup_comm, mul_comm]
    exact hprod
  have hsup : conjSubgroup g V ⊔ (Pc M V ⊓ Tim79a.xOf V (hOf M V g)) =
      Tim79a.xOf V (hOf M V g) := by
    refine Subgroup.eq_of_le_of_card_ge (sup_le hAW inf_le_right) ?_
    have hcardEq : Nat.card ↥(conjSubgroup g V ⊔
        (Pc M V ⊓ Tim79a.xOf V (hOf M V g))) =
        Nat.card ↥(Tim79a.xOf V (hOf M V g)) := by
      rw [hprod', hcardW]
      ring
    exact le_of_eq hcardEq.symm
  have hxsup : x ∈ conjSubgroup g V ⊔ (Pc M V ⊓ Tim79a.xOf V (hOf M V g)) := by
    rw [hsup]
    exact hx
  obtain ⟨a, haA, p, hpQ, hxap⟩ :=
    exists_mul_of_mem_sup (V := conjSubgroup g V) (U := Pc M V ⊓ Tim79a.xOf V (hOf M V g))
      hQN hxsup
  exact ⟨a, haA, p, hpQ.1, hxap⟩

private theorem Sec5Hyp.mem_xOf_of_mem_center_conj (hS : Sec5Hyp M V) {g : G}
    (hg : conjSubgroup g V ∈ sigmaSet M V) {x : G}
    (hx : x ∈ conjSubgroup g (Pc M V) ⊓ kOf V (hOf M V g))
    (hxc : ∀ z ∈ conjSubgroup g (Pc M V) ⊓ kOf V (hOf M V g), z * x = x * z) :
    x ∈ Tim79a.xOf V (hOf M V g) := by
  obtain ⟨y, hyH, hPy, -, -, -⟩ := hS.exists_conj_data hg
  have hx'P : y⁻¹ * x * y ∈ Pc M V := by
    have hxy : x ∈ conjSubgroup y (Pc M V) := hPy ▸ hx.1
    exact mem_conjSubgroup.mp hxy
  have hx'K : y⁻¹ * x * y ∈ kOf V (hOf M V g) :=
    (Subgroup.mem_normalizer_iff''.1 (le_normalizer_kOf V (hOf M V g) hyH) x).1 hx.2
  have hx'C : y⁻¹ * x * y ∈ Subgroup.centralizer
      ((Pc M V ⊓ kOf V (hOf M V g) : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    obtain ⟨hwP, hwK⟩ := Subgroup.mem_inf.mp hw
    have hw'P : y * w * y⁻¹ ∈ conjSubgroup g (Pc M V) := by
      rw [hPy]
      exact Subgroup.mem_map_of_mem (MulAut.conj y).toMonoidHom hwP
    have hw'K : y * w * y⁻¹ ∈ kOf V (hOf M V g) :=
      (Subgroup.mem_normalizer_iff.1 (le_normalizer_kOf V (hOf M V g) hyH) w).1 hwK
    have hcomm := hxc (y * w * y⁻¹) (Subgroup.mem_inf.mpr ⟨hw'P, hw'K⟩)
    calc w * (y⁻¹ * x * y) = y⁻¹ * ((y * w * y⁻¹) * x) * y := by group
      _ = y⁻¹ * (x * (y * w * y⁻¹)) * y := by rw [hcomm]
      _ = (y⁻¹ * x * y) * w := by group
  have hx'W : y⁻¹ * x * y ∈ Tim79a.xOf V (hOf M V g) := by
    obtain ⟨F, hField, hFintype, hCharP, l, hl, ψ, hw⟩ := (hS.shape hg).shape
    have hmem : y⁻¹ * x * y ∈ Pc M V ⊓ kOf V (hOf M V g) ⊓
        Subgroup.centralizer ((Pc M V ⊓ kOf V (hOf M V g) : Subgroup G) : Set G) :=
      Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hx'P, hx'K⟩, hx'C⟩
    rw [hw.center_PK] at hmem
    exact (Subgroup.mem_inf.mp hmem).2
  have hxW : y * (y⁻¹ * x * y) * y⁻¹ ∈ Tim79a.xOf V (hOf M V g) :=
    (Subgroup.mem_normalizer_iff.1
      (Tim79a.H_le_normalizer_xOf V (hOf M V g) hyH) (y⁻¹ * x * y)).1 hx'W
  rwa [show y * (y⁻¹ * x * y) * y⁻¹ = x by group] at hxW

private theorem Sec6Hyp.commute_of_mk_mem_center_lOf (hS : Sec6Hyp M V) {g : G}
    (hg : conjSubgroup g V ∈ sigmaSet M V) {x : ↥M}
    (hxL : (x : G) ∈ lOf M V g)
    (hxc : QuotientGroup.mk' (pCore 2 ↥M) x ∈
      Subgroup.centralizer (imgQ M (lOf M V g) : Set (MBar M)))
    {l : G} (hl : l ∈ lOf M V g) : l * (x : G) = (x : G) * l := by
  have hlM : l ∈ M := hl.2
  have hcomm : QuotientGroup.mk' (pCore 2 ↥M) (⟨l, hlM⟩ : ↥M) *
      QuotientGroup.mk' (pCore 2 ↥M) x =
      QuotientGroup.mk' (pCore 2 ↥M) x *
        QuotientGroup.mk' (pCore 2 ↥M) (⟨l, hlM⟩ : ↥M) :=
    Subgroup.mem_centralizer_iff.mp hxc _ (mk_mem_imgQ hl)
  have hmemM : ⁅l, (x : G)⁆ ∈ M :=
    M.mul_mem (M.mul_mem (M.mul_mem hlM x.2) (M.inv_mem hlM)) (M.inv_mem x.2)
  have hq : QuotientGroup.mk' (pCore 2 ↥M) (⟨⁅l, (x : G)⁆, hmemM⟩ : ↥M) = 1 := by
    rw [show (⟨⁅l, (x : G)⁆, hmemM⟩ : ↥M) = ⁅(⟨l, hlM⟩ : ↥M), x⁆ from Subtype.ext rfl,
      map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hcomm
  have hP : ⁅l, (x : G)⁆ ∈ Pc M V :=
    (hS.mk_eq_one_iff ⟨⁅l, (x : G)⁆, hmemM⟩).mp hq
  have hV : ⁅l, (x : G)⁆ ∈ conjSubgroup g V := by
    have hmem : ⁅l, (x : G)⁆ ∈ ⁅conjSubgroup g (Pc M V), conjSubgroup g (Pc M V)⁆ :=
      Subgroup.commutator_mem_commutator hl.1 hxL.1
    rwa [hS.sec5.commutator_conj_Pc hg] at hmem
  have hbot : ⁅l, (x : G)⁆ = 1 := by
    have hmem : ⁅l, (x : G)⁆ ∈ conjSubgroup g V ⊓ Pc M V := ⟨hV, hP⟩
    rw [hS.sec5.inf_Pc_eq_bot hg] at hmem
    exact Subgroup.mem_bot.mp hmem
  exact commutatorElement_eq_one_iff_mul_comm.mp hbot

theorem Sec6Hyp.imgQ_lOf_inf_centralizer_le (hS : Sec6Hyp M V) {g : G}
    (hg : conjSubgroup g V ∈ sigmaSet M V) :
    imgQ M (lOf M V g) ⊓ Subgroup.centralizer (imgQ M (lOf M V g) : Set (MBar M)) ≤
      imgQ M (conjSubgroup g V) := by
  intro z hz
  obtain ⟨hzL, hzC⟩ := Subgroup.mem_inf.mp hz
  obtain ⟨x, hxL, rfl⟩ := mem_imgQ_iff.mp hzL
  have hPK : lOf M V g = conjSubgroup g (Pc M V) ⊓ kOf V (hOf M V g) :=
    (hS.sec5.shape hg).conj_Pc_inf_M hS.sec5.toRootHyp
  have hxPK : (x : G) ∈ conjSubgroup g (Pc M V) ⊓ kOf V (hOf M V g) := hPK ▸ hxL
  have hcomm : ∀ w ∈ conjSubgroup g (Pc M V) ⊓ kOf V (hOf M V g),
      w * (x : G) = (x : G) * w := fun w hw =>
    hS.commute_of_mk_mem_center_lOf hg hxL hzC (hPK.symm ▸ hw)
  have hxW : (x : G) ∈ Tim79a.xOf V (hOf M V g) :=
    hS.sec5.mem_xOf_of_mem_center_conj hg hxPK hcomm
  obtain ⟨a, haA, p, hpP, hap⟩ := hS.sec5.exists_mul_of_mem_xOf hg hxW
  have haM : a ∈ M := (hS.sec5.le_M_of_mem_sigmaSet hg).1 haA
  have hpM : p ∈ M := hS.sec5.toRootHyp.toHyp.Pc_le_M hpP
  have hpmk : QuotientGroup.mk' (pCore 2 ↥M) (⟨p, hpM⟩ : ↥M) = 1 :=
    (hS.mk_eq_one_iff ⟨p, hpM⟩).mpr hpP
  have hxeq : x = (⟨a, haM⟩ : ↥M) * ⟨p, hpM⟩ := by
    ext
    simpa using hap
  have hz : QuotientGroup.mk' (pCore 2 ↥M) x =
      QuotientGroup.mk' (pCore 2 ↥M) (⟨a, haM⟩ : ↥M) := by
    rw [hxeq, map_mul, hpmk, mul_one]
  rw [hz]
  exact mk_mem_imgQ haA

theorem Sec5Hyp.imgQ_le_imgQ_lOf_inf_centralizer (hS : Sec5Hyp M V) {g : G}
    (hg : conjSubgroup g V ∈ sigmaSet M V) :
    imgQ M (conjSubgroup g V) ≤
      imgQ M (lOf M V g) ⊓ Subgroup.centralizer (imgQ M (lOf M V g) : Set (MBar M)) := by
  refine le_inf (imgQ_mono (hS.conjSubgroup_le_lOf hg)) ?_
  intro z hz
  obtain ⟨x, hxA, rfl⟩ := mem_imgQ_iff.mp hz
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  obtain ⟨l, hlL, rfl⟩ := mem_imgQ_iff.mp hy
  have hcent : (l : G) ∈ Subgroup.centralizer (conjSubgroup g V : Set G) :=
    conjSubgroup_Pc_le_centralizer M V g hlL.1
  have hcomm : (x : G) * (l : G) = (l : G) * (x : G) :=
    Subgroup.mem_centralizer_iff.mp hcent (x : G) hxA
  have h1 : (l : ↥M) * x = x * l := Subtype.ext hcomm.symm
  calc QuotientGroup.mk' (pCore 2 ↥M) l * QuotientGroup.mk' (pCore 2 ↥M) x
      = QuotientGroup.mk' (pCore 2 ↥M) ((l : ↥M) * x) := (map_mul _ _ _).symm
    _ = QuotientGroup.mk' (pCore 2 ↥M) (x * l) := by rw [h1]
    _ = QuotientGroup.mk' (pCore 2 ↥M) x * QuotientGroup.mk' (pCore 2 ↥M) l :=
        map_mul _ _ _

end CFSG.RankThree.GF2n.Tim81
