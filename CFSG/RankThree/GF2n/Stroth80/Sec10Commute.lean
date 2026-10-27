module

public import CFSG.RankThree.GF2n.Stroth80.Sec10Partner
public import CFSG.RankThree.GF2n.Stroth80.Sec10Center
public import CFSG.RankThree.GF2n.Stroth80.Sec10CQt
public import CFSG.RankThree.GF2n.Stroth80.Sec10CardU

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n.Smith81
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

private theorem centralizer_le_conjSubgroup {t : G} {Y : Subgroup G} {g : G}
    (hs : Sit M Q Z Y t) (hgZ : conjSubgroup g Z = Y) :
    Subgroup.centralizer ({t} : Set G) ≤ conjSubgroup g M := by
  intro c hc
  rw [← normalizer_conj_eq hs.hyp g, hgZ]
  exact mem_normalizer_of_comm_Y hs (Subgroup.mem_centralizer_singleton_iff.mp hc)

theorem Good103.commute_centralizer (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (hspread : StrothNoA2SpreadStatement) {hc : Ctx M Q Z B}
    {n : ℕ} (H : Sec10Hyp hc n)
    {t z₀ : G} (ht : Good103 M Q Z B t) (hz₀ : z₀ ∈ Z) (hz₀1 : z₀ ≠ 1)
    (hfuse : ∃ g : G, g * t * g⁻¹ = t * z₀) :
    ∀ x ∈ Q ⊓ QB B ⊓ Subgroup.centralizer ({t} : Set G),
      ∀ a ∈ Q ⊓ Subgroup.centralizer ({t} : Set G), x * a = a * x := by
  obtain ⟨Y, hs⟩ := Good101.exists_sit hc ht.1
  obtain ⟨Y', hs', h103, ha, hb⟩ :=
    Good103.partner h34 h311a hspread H ht hz₀ hz₀1 hfuse hs
  obtain ⟨m, -, hm⟩ := SLlike.exists_SLMNat (H.slLike ht.1)
  obtain ⟨g, hgZ, -, hcY, H', hswap⟩ := Good103.exists_swap h34 hspread H ht hs hm
  obtain ⟨hsz, hz103, -, -⟩ := hswap z₀ hz₀ hz₀1
  have h103swap : Good103 (conjSubgroup g M) (conjSubgroup g Q) Y B (z₀ * t) :=
    Good103.swap_partner h34 h311a hspread hc hcY H' ht.1 hs hz₀ hfuse hgZ hz103
  have hsit : Sit (conjSubgroup g M) (conjSubgroup g Q) Y Y' (z₀ * t) :=
    Sit.swap_partner (hc := hc) hs hs' hgZ hcY hz₀ hz₀1
  have hQY : conjSubgroup g Q = QB Y := by
    rw [← Smith81.QB_conj_eq hs.hyp g, hgZ]
  have hbswap : QB Z ⊓ QB Y' ≤ conjSubgroup g Q := by
    rw [hc.hyp.QB_Z, hQY, ha]
    exact inf_le_right
  have hcomm := Good103.commute_of_mem_QB_inf_QB h34 h311a hspread (hc := hcY) (H := H')
    (hw := hs.mem) (ht := hz103) (htw := h103swap) (Y := Z) (Y' := Y')
    (hs := hsz) (hs' := hsit) hbswap
  intro x hx a ha'
  obtain ⟨⟨hxQ, hxB⟩, hxC⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨haQ, haC⟩ := Subgroup.mem_inf.mp ha'
  have hxQ' : x ∈ QB Z := by rw [hc.hyp.QB_Z]; exact hxQ
  have haQ' : a ∈ QB Z := by rw [hc.hyp.QB_Z]; exact haQ
  exact hcomm x ⟨⟨hxB, hxQ'⟩, centralizer_le_conjSubgroup hs hgZ hxC⟩ a
    ⟨haQ', centralizer_le_conjSubgroup hs hgZ haC⟩

theorem Good103.card_centralizer_le_of_fuse (h34 : Stroth34Statement)
    (h311a : Stroth311aStatement) (hspread : StrothNoA2SpreadStatement)
    {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n)
    {t z₀ : G}
    (ht : Good103 M Q Z B t) (hz₀ : z₀ ∈ Z) (hz₀1 : z₀ ≠ 1)
    (hfuse : ∃ g : G, g * t * g⁻¹ = t * z₀) {m : ℕ} (hm : SLMNat hc t m) :
    Nat.card ↥(Q ⊓ Subgroup.centralizer ({t} : Set G)) ≤ Nat.card Z ^ (n + 1) ∧
      Nat.card ↥(Q ⊓ Subgroup.centralizer ({t} : Set G)) ≤
        Nat.card Z * Nat.card ↥(Q ⊓ QB B ⊓ Subgroup.centralizer ({t} : Set G)) ∧
      2 * m ≤ n ∧ n ≤ 2 * m + 1 := by
  have hcomm := Good103.commute_centralizer h34 h311a hspread H ht hz₀ hz₀1 hfuse
  obtain ⟨h1, h2, h3⟩ := Ctx.card_centralizer_le_of_commute hc H.width H.n_gt H.noA2
    ht.1.2.1 ht.1.2.2.2.1 hcomm
  have hUt := Good103.card_Ut_eq h34 h311a hspread H ht hm
  have hn : n ≤ 2 * m + 1 := h3 (2 * m) hUt
  have hUtle := Ctx.card_Ut_le hc H.width ht.1.mem_LB
  have hq : 1 < Nat.card Z := by have := hc.hyp.q4; omega
  have h2m : 2 * m ≤ n := by
    have hle : Nat.card Z ^ (2 * m + 1) ≤ Nat.card Z ^ (n + 1) := by
      rw [← hUt]
      exact hUtle
    have := (Nat.pow_le_pow_iff_right hq).mp hle
    omega
  exact ⟨h1, h2, h2m, hn⟩

theorem Good103.card_QB_inf_le_of_fuse (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (hspread : StrothNoA2SpreadStatement) {hc : Ctx M Q Z B}
    {n : ℕ} (H : Sec10Hyp hc n)
    {t z₀ : G} (ht : Good103 M Q Z B t) (hz₀ : z₀ ∈ Z) (hz₀1 : z₀ ≠ 1)
    (hfuse : ∃ g : G, g * t * g⁻¹ = t * z₀) {Y : Subgroup G} (hs : Sit M Q Z Y t) :
    Nat.card ↥(QB Y ⊓ M) ≤ Nat.card Z * Nat.card ↥(QB B ⊓ QB Y ⊓ M) := by
  obtain ⟨Y', hs', h103, -, hb⟩ :=
    Good103.partner h34 h311a hspread H ht hz₀ hz₀1 hfuse hs
  have hfcomm := Good103.commute_of_mem_QB_inf_QB h34 h311a hspread H hz₀ ht h103 hs hs'
    (by rw [hb]; exact inf_le_right)
  have hCB : QB Y ⊓ Subgroup.centralizer ({z₀} : Set G) ≤ QB Y ⊓ M := by
    intro c hc_mem
    obtain ⟨hcY, hcC⟩ := Subgroup.mem_inf.mp hc_mem
    have hcN : c ∈ Subgroup.normalizer (Z : Set G) :=
      Tim77.mem_normalizer_of_commute_of_isTI hc.hyp.ti hz₀ hz₀1
        (Subgroup.mem_centralizer_singleton_iff.mp hcC)
    exact ⟨hcY, by rwa [hc.hyp.normalizer_Z.1] at hcN⟩
  have hCM : QB Y ⊓ M ≤ QB Y ⊓ Subgroup.centralizer ({z₀} : Set G) :=
    le_inf inf_le_left ((Lx_le_H0 hs (smith_1_12 hs)).trans
      (inf_le_right.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hz₀))))
  have hinfC : QB Y ⊓ M = QB Y ⊓ Subgroup.centralizer ({z₀} : Set G) :=
    le_antisymm hCM hCB
  have hinfC' : QB Y ⊓ QB B ⊓ Subgroup.centralizer ({z₀} : Set G) = QB Y ⊓ QB B ⊓ M := by
    rw [show QB Y ⊓ QB B ⊓ Subgroup.centralizer ({z₀} : Set G) =
        QB B ⊓ (QB Y ⊓ Subgroup.centralizer ({z₀} : Set G)) by ac_rfl,
      ← hinfC,
      show QB B ⊓ (QB Y ⊓ M) = QB Y ⊓ QB B ⊓ M by ac_rfl]
  obtain ⟨m, -, hm⟩ := SLlike.exists_SLMNat (H.slLike ht.1)
  obtain ⟨g, hgZ, -, hcY, H', hswap⟩ := Good103.exists_swap h34 hspread H ht hs hm
  obtain ⟨hsz, hz103, -, -⟩ := hswap z₀ hz₀ hz₀1
  have hQY : conjSubgroup g Q = QB Y := by
    rw [← Smith81.QB_conj_eq hs.hyp g, hgZ]
  have hcomm : ∀ x ∈ conjSubgroup g Q ⊓ QB B ⊓ Subgroup.centralizer ({z₀} : Set G),
      ∀ a ∈ conjSubgroup g Q ⊓ Subgroup.centralizer ({z₀} : Set G), x * a = a * x := by
    rw [hQY, hinfC', ← hinfC]
    simpa only [inf_comm, inf_assoc] using hfcomm
  have hC := (Ctx.card_centralizer_le_of_commute (hc := hcY) (n := n) (hw := H'.width)
    H'.n_gt H'.noA2 hsz.memM ((Ctx.Z_le_QB hc).1 hz₀) hcomm).2.1
  have hYcard : Nat.card Y = Nat.card Z := by
    obtain ⟨k, hk⟩ := hs.conj
    rw [hk, CFSG.RankThree.GF2n.card_conjSubgroup]
  rw [hQY, ← hinfC, hinfC', hYcard, inf_comm (QB Y) (QB B)] at hC
  exact hC

theorem Good103.card_CN_le_of_fuse (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (hspread : StrothNoA2SpreadStatement) {hc : Ctx M Q Z B}
    {n : ℕ} (H : Sec10Hyp hc n)
    {t z₀ : G} (ht : Good103 M Q Z B t) (hz₀ : z₀ ∈ Z) (hz₀1 : z₀ ≠ 1)
    (hfuse : ∃ g : G, g * t * g⁻¹ = t * z₀) :
    Nat.card ↥(hc.CN t) ≤ Nat.card Z * Nat.card ↥(LB M Q B ⊓ hc.CN t) := by
  obtain ⟨Y, hs⟩ := Good101.exists_sit hc ht.1
  let P : Subgroup G := QB Y ⊓ M
  let P₀ : Subgroup G := QB B ⊓ QB Y ⊓ M
  have hCNle : hc.CN t ≤ Q ⊔ P := Sec10Hyp.CN_le_sup h34 h311a hspread H ht hs
  have hPle : Q ⊔ P₀ ≤ LB M Q B ⊓ hc.CN t := by
    refine le_inf (sup_le sec39_Q_le_LB ?_) (sup_le (Ctx.Q_le_CN hc ht.1.mem_LB) ?_)
    · exact (le_inf (inf_le_left.trans inf_le_left) inf_le_right).trans le_sup_right
    · exact Good103.inf_QB_inf_QB_le_CN h34 h311a hspread H ht hs
  obtain ⟨m, hm2, hm⟩ := SLlike.exists_SLMNat (H.slLike ht.1)
  have h5 : Sec5Hyp hc n t := H.toSec5 ht.1.mem_LB ht.1.2.2.1
  have hSL : SLNat hc t := SLMNat.toSLNat hm hm2
  have hVQB : Vt M (LB M Q B) B Z t ≤ QB B := (stroth310SL_of_34 h34) G M Q Z B hc n t h5 hSL
  have hQYQB : Q ⊓ QB Y ≤ QB B :=
    calc Q ⊓ QB Y ≤ (Q ⊓ QB Y) ⊔ Z := le_sup_left
      _ = Vt M (LB M Q B) B Z t := (Good103.Vt_eq ht hs).symm
      _ ≤ QB B := hVQB
  have hQP : Q ⊓ P = Q ⊓ QB Y := by
    rw [show P = QB Y ⊓ M from rfl, ← inf_assoc,
      inf_eq_left.mpr (inf_le_left.trans hc.hyp.Q_normal.1)]
  have hQP0 : Q ⊓ P₀ = Q ⊓ QB Y := by
    rw [show Q ⊓ P₀ = (Q ⊓ QB Y) ⊓ QB B ⊓ M by unfold P₀; ac_rfl,
      inf_eq_left.mpr hQYQB,
      inf_eq_left.mpr (inf_le_left.trans hc.hyp.Q_normal.1)]
  have hPN : P ≤ Subgroup.normalizer (Q : Set G) := inf_le_right.trans hc.hyp.Q_normal.2
  have hP0N : P₀ ≤ Subgroup.normalizer (Q : Set G) := inf_le_right.trans hc.hyp.Q_normal.2
  have hcardP : Nat.card ↥(Q ⊔ P) * Nat.card ↥(Q ⊓ QB Y) = Nat.card Q * Nat.card ↥P := by
    simpa only [hQP] using card_sup_mul_card_inf_of_normalizer (A := Q) (C := P) hPN
  have hcardP0 : Nat.card ↥(Q ⊔ P₀) * Nat.card ↥(Q ⊓ QB Y) = Nat.card Q * Nat.card ↥P₀ := by
    simpa only [hQP0] using card_sup_mul_card_inf_of_normalizer (A := Q) (C := P₀) hP0N
  have hPleP0 : Nat.card ↥P ≤ Nat.card Z * Nat.card ↥P₀ :=
    Good103.card_QB_inf_le_of_fuse h34 h311a hspread H ht hz₀ hz₀1 hfuse hs
  have hQPle : Nat.card ↥(Q ⊔ P) ≤ Nat.card Z * Nat.card ↥(Q ⊔ P₀) := by
    have hstep : Nat.card ↥(Q ⊔ P) * Nat.card ↥(Q ⊓ QB Y) ≤
        (Nat.card Z * Nat.card ↥(Q ⊔ P₀)) * Nat.card ↥(Q ⊓ QB Y) := by
      calc Nat.card ↥(Q ⊔ P) * Nat.card ↥(Q ⊓ QB Y)
          = Nat.card Q * Nat.card ↥P := hcardP
        _ ≤ Nat.card Q * (Nat.card Z * Nat.card ↥P₀) := Nat.mul_le_mul_left _ hPleP0
        _ = Nat.card Z * (Nat.card Q * Nat.card ↥P₀) := by ring
        _ = Nat.card Z * (Nat.card ↥(Q ⊔ P₀) * Nat.card ↥(Q ⊓ QB Y)) := by rw [← hcardP0]
        _ = (Nat.card Z * Nat.card ↥(Q ⊔ P₀)) * Nat.card ↥(Q ⊓ QB Y) := by ring
    exact Nat.le_of_mul_le_mul_right hstep Nat.card_pos
  exact (Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le hCNle)).trans
    (hQPle.trans (Nat.mul_le_mul_left _
      (Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le hPle))))

end CFSG.RankThree.GF2n.Stroth80
