module

public import CFSG.RankThree.GF2n.Stroth80.Sec103Root
public import CFSG.RankThree.GF2n.Stroth80.Sec10Second

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n.Smith81
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem Good101.exists_root_of_mem_Vt {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n) {t : G}
    (ht : Good101 M Q Z B t) {a : G} (haV : a ∈ Vt M (LB M Q B) B Z t) (haZ : a ∉ Z) :
    ∃ D : Subgroup G, Ctx M Q Z D ∧ a ∈ D := by
  obtain ⟨g, z, hz, -, hgz⟩ := ht.isRoot_of_mem_Vt H haV haZ
  obtain ⟨g', hg'Q, hag'⟩ := stroth_2_6 hc.hyp (hc.Vt_le_Q t haV) haZ ⟨g, z, hz, hgz.symm⟩
  exact ⟨conjSubgroup g' Z, ⟨hc.hyp, ⟨g', rfl⟩, hg'Q, fun e => haZ (e ▸ hag')⟩, hag'⟩

theorem StrothHyp.le_QB_of_mem_of_mem_QB (H : StrothHyp M Q Z) {D X : Subgroup G}
    (hD : ∃ h : G, D = conjSubgroup h Z) (hX : ∃ h : G, X = conjSubgroup h Z) (hne : D ≠ X)
    {γ : G} (hγD : γ ∈ D) (hγ1 : γ ≠ 1) (hγX : γ ∈ QB X) : D ≤ QB X :=
  H.le_QB_of_le_QB hX hD hne.symm (H.le_QB_of_mem_QB hX hD hγD hγ1 hγX)

theorem Good101.Vt_le_QB_of_root (h34 : Stroth34Statement) (hspread : StrothNoA2SpreadStatement)
    {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n) {t : G} (ht : Good101 M Q Z B t)
    {Y : Subgroup G} (hs : Sit M Q Z Y t) {D : Subgroup G} (hD : Ctx M Q Z D)
    (hDY : D ≤ QB Y) : Vt M (LB M Q B) B Z t ≤ QB D := by
  obtain ⟨r, hr, hrD⟩ := H.rootTrans h34 hspread D hD
  subst D
  have hne : conjSubgroup r B ≠ Y := by
    intro heq
    have htD : t ∈ conjSubgroup r B := by
      rw [heq]
      exact hs.mem
    exact ht.2.2.1 (hD.le htD)
  have htD : t ∈ QB (conjSubgroup r B) :=
    hc.hyp.le_QB_of_le_QB hD.conj hs.conj hne hDY hs.mem
  obtain ⟨m, hm2, hsl⟩ := SLlike.exists_SLMNat (H.slLike ht)
  have h5 : Sec5Hyp (hc.conj_of_mem hr) n t :=
    (H.conj_of_mem hr).toSec5 (Subgroup.mem_sup_right ⟨htD, ht.2.1⟩) ht.2.2.1
  have hsl' : SLNat (hc.conj_of_mem hr) t :=
    SLMNat.toSLNat ((SLMNat.conj_of_mem_iff hr).mpr hsl) hm2
  have h := stroth310SL_of_34 h34 G M Q Z (conjSubgroup r B) (hc.conj_of_mem hr) n t h5 hsl'
  rwa [(rt_vt_conj hc hr t).2] at h

theorem Sec10Hyp.Rt_ne_LB_of_mem_QB (h34 : Stroth34Statement) {hc : Ctx M Q Z B} {n : ℕ}
    (H : Sec10Hyp hc n) {r : G} (hr : r ∈ M)
    (hBr : (B ⊔ Z) ⊓ (conjSubgroup r B ⊔ Z) = Z) {s : G} (hsM : s ∈ M)
    (hsD : s ∈ QB (conjSubgroup r B)) : Rt M (LB M Q B) s ≠ LB M Q B := by
  intro hR
  have hsD' : s ∈ conjSubgroup r (LB M Q B) := by
    have h1 : s ∈ LB M Q (conjSubgroup r B) := Subgroup.mem_sup_right ⟨hsD, hsM⟩
    rwa [hc.LB_conj hr] at h1
  have hle : conjSubgroup r (LB M Q B) ≤ LB M Q B := by
    have h := hc.LB_conj_le_Rt hr hsD'
    rwa [hR, hc.LB_conj hr] at h
  have heq : conjSubgroup r (LB M Q B) = LB M Q B :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [CFSG.RankThree.GF2n.card_conjSubgroup])
  have hBZ : conjSubgroup r B ≤ Z := by
    intro x hx
    have hx' : x ∈ (B ⊔ Z) ⊓ (conjSubgroup r B ⊔ Z) :=
      Subgroup.mem_inf.mpr ⟨H.conj_le_sup_of_conj_LB_eq h34 hr heq hx,
        Subgroup.mem_sup_left hx⟩
    rwa [hBr] at hx'
  obtain ⟨b, hb, hb1⟩ := (hc.conj_of_mem hr).exists_ne_one
  apply hb1
  have : b ∈ Z := hBZ hb
  have hzb : b ∈ Z ⊓ conjSubgroup r B := ⟨this, hb⟩
  rwa [(hc.conj_of_mem hr).inf_eq_bot, Subgroup.mem_bot] at hzb

theorem Good101.le_of_min_conj {hc : Ctx M Q Z B} {m : ℕ}
    (hmin : ∀ (s : G) (k : ℕ), Good101 M Q Z B s → SLMNat hc s k → m ≤ k) {r : G}
    (hr : r ∈ M) {y : G} (hy : Good101 M Q Z (conjSubgroup r B) y) {k : ℕ}
    (hk : SLMNat (hc.conj_of_mem hr) y k) : m ≤ k := by
  have hy' : Good101 (conjSubgroup r M) (conjSubgroup r Q) (conjSubgroup r Z)
      (conjSubgroup r B) y := by
    rwa [hc.conj_M_eq hr, hc.conj_Q_eq hr, hc.conj_Z_eq hr]
  have hyc : Good101 M Q Z B (r⁻¹ * y * r) := by
    have h := Good101.conjG (hc := hc.conjBy r) hy' r⁻¹
    simpa only [conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one, inv_inv] using h
  have hk' : SLMNat (hc.conjBy r) y k :=
    SLMNat.of_eq hk (hc.conjBy r) (hc.conj_M_eq hr).symm (hc.conj_Q_eq hr).symm
      (hc.conj_Z_eq hr).symm rfl
  have hk'' : SLMNat ((hc.conjBy r).conjBy r⁻¹) (r⁻¹ * y * r) k := by
    simpa only [inv_inv] using SLMNat.conjG hk' r⁻¹
  have hk''' : SLMNat hc (r⁻¹ * y * r) k := by
    refine SLMNat.of_eq hk'' hc ?_ ?_ ?_ ?_ <;>
      rw [conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one]
  exact hmin (r⁻¹ * y * r) k hyc hk'''

theorem Sit.mem_QB_of_le_QB {X : Subgroup G} {y : G} (hsy : Sit M Q Z X y) {D : Subgroup G}
    (hD : Ctx M Q Z D) (hDX : D ≤ QB X) : y ∈ QB D := by
  have hne : D ≠ X := by
    intro h
    apply hsy.notQ
    have hyD : y ∈ D := by
      rw [h]
      exact hsy.mem
    exact hD.le hyD
  exact hD.hyp.le_QB_of_le_QB hD.conj hsy.conj hne hDX hsy.mem

end CFSG.RankThree.GF2n.Stroth80
