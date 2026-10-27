module

public import CFSG.LocalAnalysis.StandardType.FF81.Defs
public import CFSG.LocalAnalysis.StandardType.GGSixE6TwoModel
public import Certificates.Certificate1953
public import Certificates.Certificate1954
import CFSG.LocalAnalysis.StandardType.FF81.CentE6.ConjModel
import CFSG.LocalAnalysis.StandardType.FF81.E6Position

public section

namespace CFSG.StandardType.FF81.CentE6

open CFSG CFSG.Assembly CFSG.Open CFSG.StandardType.GGSixE6Two
open CFSG.RankThree.PartTwo.Sec4.Item434Kit (vecElt)

private theorem not_mem_of_model {G : Type} [Group G] {b : G} {L : Subgroup G}
    {z : Fin 3 → ↥L} (hM : GGFF.Model ↥L z) (hb : orderOf b = 3)
    (hLb : L ≤ Subgroup.centralizer ({b} : Set G)) : b ∉ L := by
  intro hbL
  have hcent : (⟨b, hbL⟩ : ↥L) = 1 := hM.eq_one_of_forall_comm (x := ⟨b, hbL⟩) fun y =>
    Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (hLb y.2)).symm
  have hb1 : b = 1 := by simpa using congrArg (fun t : ↥L => (t : G)) hcent
  simp [hb1] at hb

private theorem exists_conj_eq_inv_mul_vecElt
    {G : Type} [Group G] {b : G} {L : Subgroup G} {z : Fin 3 → ↥L} (hM : GGFF.Model ↥L z)
    (hLb : L ≤ Subgroup.centralizer ({b} : Set G)) {φ : EC →* G}
    (hφ : Function.Injective φ) (hφb : φ zE = b) (hφL : lE.map φ = L) :
    ∃ x : G, ∃ v : Fin 3 → ZMod 3, vecElt z v ≠ 1 ∧
      x * b * x⁻¹ = b⁻¹ * ((vecElt z v : ↥L) : G) := by
  obtain ⟨g, u, hu, hu1, hu3, hgu⟩ := exists_conj_zE_eq_inv_mul
  have hu'L : φ u ∈ L := by
    rw [← hφL]
    exact Subgroup.mem_map_of_mem φ hu
  have hu'1 : φ u ≠ 1 := fun h => hu1 (hφ (by simpa using h))
  have hu'3 : φ u ^ 3 = 1 := by
    have := map_pow φ u 3
    rw [hu3, map_one] at this
    exact this.symm
  have hgu' : φ g * b * (φ g)⁻¹ = b⁻¹ * φ u := by
    have := congrArg φ hgu
    simpa [map_mul, map_inv, hφb] using this
  have hu'cube : (⟨φ u, hu'L⟩ : ↥L) ^ 3 = 1 := Subtype.ext (by simpa using hu'3)
  obtain ⟨h, v, hv⟩ := hM.fus ⟨φ u, hu'L⟩ hu'cube
  have hvG : φ u = (h : G) * ((vecElt z v : ↥L) : G) * (h : G)⁻¹ := by
    have := congrArg (fun t : ↥L => (t : G)) hv
    simpa using this
  have hcinv : (h : G)⁻¹ * b⁻¹ * (h : G) = b⁻¹ := by
    have hhcomm : Commute (h : G) b := Subgroup.mem_centralizer_singleton_iff.mp (hLb h.2)
    calc (h : G)⁻¹ * b⁻¹ * (h : G) = (b⁻¹ * (h : G)⁻¹) * (h : G) := by
          rw [Commute.inv_right (Commute.inv_left hhcomm)]
      _ = b⁻¹ := by rw [mul_assoc, inv_mul_cancel, mul_one]
  refine ⟨(h : G)⁻¹ * φ g, v, fun hz1 => hu'1 ?_, ?_⟩
  · have hv1 : (⟨φ u, hu'L⟩ : ↥L) = 1 := by
      rw [hv, hz1]
      simp
    simpa using congrArg (fun t : ↥L => (t : G)) hv1
  · calc ((h : G)⁻¹ * φ g) * b * ((h : G)⁻¹ * φ g)⁻¹
        = (h : G)⁻¹ * (φ g * b * (φ g)⁻¹) * (h : G) := by group
      _ = (h : G)⁻¹ * (b⁻¹ * φ u) * (h : G) := by rw [hgu']
      _ = (h : G)⁻¹ * (b⁻¹ * ((h : G) * ((vecElt z v : ↥L) : G) * (h : G)⁻¹)) * (h : G) := by
          rw [hvG]
      _ = ((h : G)⁻¹ * b⁻¹ * (h : G)) * ((vecElt z v : ↥L) : G) := by group
      _ = b⁻¹ * ((vecElt z v : ↥L) : G) := by rw [hcinv]

private theorem inv_mul_not_mem_zpowers_xs {G : Type} [Group G] {b w : G} {L : Subgroup G}
    {z : Fin 3 → ↥L} (hb : orderOf b = 3) (hbL : b ∉ L) (hwL : w ∈ L) (hw1 : w ≠ 1)
    (hw3 : w ^ 3 = 1) (i : Fin 4) : b⁻¹ * w ∉ Subgroup.zpowers (xs b z i) := by
  intro hmem
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  by_cases hi0 : i = 0
  ·
    subst hi0
    have hmem0 : b⁻¹ * w ∈ Subgroup.zpowers b := by simpa [xs] using hmem
    have hwz : w ∈ Subgroup.zpowers b := by
      have := (Subgroup.zpowers b).mul_mem (Subgroup.mem_zpowers b) hmem0
      simpa using this
    have hwcard : Nat.card (Subgroup.zpowers w) = 3 := by
      rw [Nat.card_zpowers]
      exact orderOf_eq_prime hw3 hw1
    have hbcard : Nat.card (Subgroup.zpowers b) = 3 := by
      rw [Nat.card_zpowers]
      exact hb
    have hfinw : Finite ↥(Subgroup.zpowers w) :=
      Nat.finite_of_card_ne_zero (by rw [hwcard]; norm_num)
    have hfinb : Finite ↥(Subgroup.zpowers b) :=
      Nat.finite_of_card_ne_zero (by rw [hbcard]; norm_num)
    have heq : Subgroup.zpowers w = Subgroup.zpowers b :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hwz) (by simp [hbcard, hwcard])
    have hbzw : b ∈ Subgroup.zpowers w := by
      rw [heq]
      exact Subgroup.mem_zpowers b
    exact hbL ((Subgroup.zpowers_le.mpr hwL) hbzw)
  ·
    have hxsL : xs b z i ∈ L := by
      fin_cases i
      · exact absurd rfl hi0
      · simp [xs]
      · simp [xs]
      · simp [xs]
    have hbwL : b⁻¹ * w ∈ L := (Subgroup.zpowers_le.mpr hxsL) hmem
    apply hbL
    have hbeq : b = w * (b⁻¹ * w)⁻¹ := by group
    rw [hbeq]
    exact L.mul_mem hwL (L.inv_mem hbwL)

private theorem not_conjLinesOfB_of_conj_eq_inv_mul {G : Type} [Group G] {b w x : G}
    {L : Subgroup G} {z : Fin 3 → ↥L} (hb : orderOf b = 3)
    (hLb : L ≤ Subgroup.centralizer ({b} : Set G)) (hbL : b ∉ L) (hwL : w ∈ L)
    (hwB : w ∈ GGFF.Bt b z) (hw1 : w ≠ 1) (hw3 : w ^ 3 = 1) (hx : x * b * x⁻¹ = b⁻¹ * w) :
    ¬ ConjLinesOfB b z (coordLines b z) := by
  intro hConj
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hcomm : Commute b w := (Subgroup.mem_centralizer_singleton_iff.mp (hLb hwL)).symm
  have hbw1 : b⁻¹ * w ≠ 1 := by
    intro hbw
    apply hbL
    have hwb : w = b := by
      have := congrArg (fun t => b * t) hbw
      simpa using this
    rwa [hwb] at hwL
  have hb3 : b ^ 3 = 1 := by rw [← hb]; exact pow_orderOf_eq_one b
  have hbw3 : (b⁻¹ * w) ^ 3 = 1 := by
    rw [Commute.mul_pow hcomm.inv_left, inv_pow, hb3, hw3, inv_one, one_mul]
  have hZle : Subgroup.zpowers (b⁻¹ * w) ≤ GGFF.Bt b z :=
    Subgroup.zpowers_le.mpr ((GGFF.Bt b z).mul_mem
      ((GGFF.Bt b z).inv_mem (GGFF.SettingCore.b_mem_Bt b z)) hwB)
  have hZcard : Nat.card (Subgroup.zpowers (b⁻¹ * w)) = 3 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime hbw3 hbw1
  obtain ⟨i, hi⟩ := (hConj _ hZle hZcard).mp ⟨x, congrArg Subgroup.zpowers hx⟩
  exact inv_mul_not_mem_zpowers_xs hb hbL hwL hw1 hw3 i
    (hi ▸ Subgroup.mem_zpowers (b⁻¹ * w))

theorem not_conjLinesOfB_coordLines_of_embedding
    {G : Type} [Group G] {b : G} {L : Subgroup G} {z : Fin 3 → ↥L} (hM : GGFF.Model ↥L z)
    (hb : orderOf b = 3) (hLb : L ≤ Subgroup.centralizer ({b} : Set G)) {φ : EC →* G}
    (hφ : Function.Injective φ) (hφb : φ zE = b) (hφL : lE.map φ = L) :
    ¬ ConjLinesOfB b z (coordLines b z) := by
  obtain ⟨x, v, hv1, hx⟩ := exists_conj_eq_inv_mul_vecElt hM hLb hφ hφb hφL
  have hw3 : ((vecElt z v : ↥L) : G) ^ 3 = 1 := by
    have h1 : (vecElt z v) ^ 3 = 1 := (hM.isElemAbelian_tor').2 _ (GGFF.vecElt_mem_tor z v)
    simpa using congrArg (fun t : ↥L => (t : G)) h1
  have hwB : ((vecElt z v : ↥L) : G) ∈ GGFF.Bt b z := by
    rw [show ((vecElt z v : ↥L) : G) = vecElt (GGFF.zs z) v from
      (GGFF.vecElt_map (Subgroup.subtype L) z v).symm]
    exact GGFF.SettingCore.tor_le_Bt b z (GGFF.vecElt_mem_tor _ v)
  exact not_conjLinesOfB_of_conj_eq_inv_mul hb hLb (not_mem_of_model hM hb hLb)
    (vecElt z v).2 hwB (fun hw => hv1 (Subtype.ext hw)) hw3 hx

section Frame

theorem not_conjLinesOfB_coordLines {G : Type} [Group G] [Finite G] {n : ℕ} {b t : G}
    {L : Subgroup G} {K : ℕ → Subgroup G} (hA : HypA G n b L) (hU : Upstream n b L K t)
    (hYD : YData n b L (⨆ i : Fin (n + 2), K (i : ℕ)) t) (hn : n = 5)
    (hlab : GGHasLabel ⟨.E6, 0, 1⟩ ↥(⨆ i : Fin (n + 2), K (i : ℕ))) {z : Fin 3 → ↥L}
    (hM : GGFF.Model ↥L z) : ¬ ConjLinesOfB b z (coordLines b z) := by
  obtain ⟨φ, hφ, -, -, hφb, hφL, -⟩ := exists_e6Position_of_yData hA hU hYD hn hlab
  exact not_conjLinesOfB_coordLines_of_embedding hM hA.ord hA.le hφ hφb hφL

end Frame

end CFSG.StandardType.FF81.CentE6

end
