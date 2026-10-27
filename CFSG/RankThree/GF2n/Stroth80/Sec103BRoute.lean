module

public import CFSG.RankThree.GF2n.Stroth80.Sec103BCent
public import CFSG.RankThree.GF2n.Stroth80.Sec103AG1b
public import CFSG.RankThree.GF2n.Stroth80.Sec10CQtRoot
public import CFSG.RankThree.GF2n.Stroth80.Hom24Omega

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n.Smith81
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem Good101.exists_conj_eq_mul_of_caseA_conj (h34 : Stroth34Statement)
    (hspread : StrothNoA2SpreadStatement) {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n)
    {t : G} (ht : Good101 M Q Z B t) {Y : Subgroup G} (hs : Sit M Q Z Y t) {c : G}
    (hcQ : c ∈ Q) (hcB : c ∈ Subgroup.centralizer (B : Set G))
    (hcW : c ∉ Wt Q (Vt M (LB M Q B) B Z t)) (hA' : CaseA (QB Y) Y (c * t * c⁻¹)) {a : G}
    (ha : a ∈ Q ⊓ QB Y ⊓ Subgroup.centralizer ({c} : Set G)) :
    ∃ u ∈ QB Y, ∃ y ∈ Y, u * (c * t * c⁻¹) * u⁻¹ = c * t * c⁻¹ * a * y := by
  obtain ⟨hcY, -⟩ := Good101.exists_yFrame h34 hspread H ht hs
  have hw : c * t * c⁻¹ ∈ LB (Subgroup.normalizer (Y : Set G)) (QB Y) B :=
    Good101.conj_mem_LB h34 H ht hs hcQ hcB
  have hsw : Sit (Subgroup.normalizer (Y : Set G)) (QB Y) Y (conjSubgroup c Y)
      (c * t * c⁻¹) := Good101.sit_conj h34 hspread H ht hs hcQ hcW
  have haY' : a ∈ QB (conjSubgroup c Y) := mem_QB_conj_of_mem_centralizer ha.1.2 ha.2
  have haU : a ∈ Ut (QB Y) Y (c * t * c⁻¹) :=
    Good101.inf_QB_le_Ut_of_caseA hcY hsw hA' ⟨ha.1.2, haY'⟩
  obtain ⟨x, hxQB, hx⟩ := hcY.exists_comm_mul_inv_mem_Z hw haU
  have haQ : a ∈ QB Y := ha.1.2
  have hac : a * c = c * a := Subgroup.mem_centralizer_singleton_iff.mp ha.2
  have hat : a * t = t * a := (Sit.QB_comm_X hs hs.mem haQ).symm
  have hacc : Commute a c := hac
  have hatt : Commute a t := hat
  have haw : a * (c * t * c⁻¹) = (c * t * c⁻¹) * a :=
    (hacc.mul_right hatt).mul_right hacc.inv_right
  let y₀ : G := ⁅x, c * t * c⁻¹⁆ * a⁻¹
  have hy₀ : y₀ ∈ Y := hx
  have hwy : (c * t * c⁻¹) * y₀ = y₀ * (c * t * c⁻¹) := by
    have h := hcY.LB_centralizes_Z hw y₀ hy₀
    calc (c * t * c⁻¹) * y₀ = ((c * t * c⁻¹) * y₀ * (c * t * c⁻¹)⁻¹) * (c * t * c⁻¹) := by
          group
      _ = y₀ * (c * t * c⁻¹) := by rw [h]
  have hay : y₀ * a = a * y₀ := Sit.QB_comm_X hs hy₀ haQ
  have hx_eq : ⁅x, c * t * c⁻¹⁆ = y₀ * a := by
    show ⁅x, c * t * c⁻¹⁆ = (⁅x, c * t * c⁻¹⁆ * a⁻¹) * a
    group
  refine ⟨x, hxQB, y₀, hy₀, ?_⟩
  calc x * (c * t * c⁻¹) * x⁻¹ = ⁅x, c * t * c⁻¹⁆ * (c * t * c⁻¹) := by
        rw [commutatorElement_def]; group
    _ = (y₀ * a) * (c * t * c⁻¹) := by rw [hx_eq]
    _ = y₀ * (a * (c * t * c⁻¹)) := by group
    _ = y₀ * ((c * t * c⁻¹) * a) := by rw [haw]
    _ = (y₀ * (c * t * c⁻¹)) * a := by group
    _ = ((c * t * c⁻¹) * y₀) * a := by rw [hwy]
    _ = (c * t * c⁻¹) * (y₀ * a) := by group
    _ = (c * t * c⁻¹) * (a * y₀) := by rw [hay]
    _ = (c * t * c⁻¹) * a * y₀ := by group

private theorem Good101.mem_B_of_mem_Vt_of_centralizes {hc : Ctx M Q Z B}
    {t : G} (ht : Good101 M Q Z B t) {Y : Subgroup G} (hs : Sit M Q Z Y t)
    (h2 : SLMNat hc t 2) {c a : G} (hcQ : c ∈ Q) (hcB : c ∈ Subgroup.centralizer (B : Set G))
    (hcW : c ∉ Wt Q (Vt M (LB M Q B) B Z t)) (ha : a ∈ Q ⊓ QB Y)
    (haV : a ∈ Vt M (LB M Q B) B Z t) (hac : a ∈ Subgroup.centralizer ({c} : Set G)) :
    a ∈ B := by
  have hmem : a ∈ Q ⊓ QB Y ⊓ Vt M (LB M Q B) B Z t ⊓ Subgroup.centralizer ({c} : Set G) :=
    ⟨⟨ha, haV⟩, hac⟩
  rwa [Good101.inf_Vt_inf_centralizer_eq ht hs h2 hcQ hcB hcW] at hmem

private theorem conj_eq_of_conj_eq_mul {w u a y : G} (hconj : u * w * u⁻¹ = w * a * y)
    (hww : w * w = 1) (hay2 : (a * y) * (a * y) = 1) (huy : u * y = y * u)
    (hu2w : (u * u) * w = w * (u * u)) : u * a * u⁻¹ = a := by
  have hw_inv : w⁻¹ = w := inv_eq_of_mul_eq_one_right hww
  have hay_inv : (a * y)⁻¹ = a * y := inv_eq_of_mul_eq_one_right hay2
  have h1 : u * (w * a * y) * u⁻¹ = w := by
    rw [← hconj]
    calc u * (u * w * u⁻¹) * u⁻¹ = (u * u) * w * (u * u)⁻¹ := by group
      _ = w := by rw [hu2w]; group
  have h2 : u * (w * a * y) * u⁻¹ = (w * a * y) * (u * (a * y) * u⁻¹) := by
    calc u * (w * a * y) * u⁻¹ = (u * w * u⁻¹) * (u * (a * y) * u⁻¹) := by group
      _ = (w * a * y) * (u * (a * y) * u⁻¹) := by rw [hconj]
  have h4 : (w * a * y) * (u * (a * y) * u⁻¹) = w := by rw [← h2, h1]
  have h3 : u * (a * y) * u⁻¹ = a * y := by
    calc u * (a * y) * u⁻¹
        = (w * a * y)⁻¹ * ((w * a * y) * (u * (a * y) * u⁻¹)) := by group
      _ = (w * a * y)⁻¹ * w := by rw [h4]
      _ = a * y := by
          rw [show (w * a * y)⁻¹ = (a * y) * w by
            rw [show (w * a * y)⁻¹ = (a * y)⁻¹ * w⁻¹ by group, hay_inv, hw_inv]]
          rw [mul_assoc, hww, mul_one]
  calc u * a * u⁻¹ = (u * (a * y) * u⁻¹) * (u * y * u⁻¹)⁻¹ := by group
    _ = (a * y) * y⁻¹ := by rw [h3, huy]; group
    _ = a := by group

private theorem conj_mul_conj_eq_of_conj {c t u k a b w y : G} (hw : w = c * t * c⁻¹)
    (hca : c⁻¹ * a * c = a) (hcb : c⁻¹ * b * c = b) (hkt : k * t * k⁻¹ = t * b)
    (hconj : u * w * u⁻¹ = w * a * y) (hbu : u * b * u⁻¹ = y⁻¹ * b) :
    (c⁻¹ * u * c * k) * t * (c⁻¹ * u * c * k)⁻¹ = t * (a * b) := by
  subst hw
  have h1 : u * (c * t * c⁻¹ * b) * u⁻¹ = c * t * c⁻¹ * a * b := by
    calc u * (c * t * c⁻¹ * b) * u⁻¹
        = (u * (c * t * c⁻¹) * u⁻¹) * (u * b * u⁻¹) := by group
      _ = (c * t * c⁻¹ * a * y) * (y⁻¹ * b) := by rw [hconj, hbu]
      _ = c * t * c⁻¹ * a * b := by group
  have hbc : c⁻¹ * b = b * c⁻¹ := by
    have h1 : b * c = c * b := by
      calc b * c = c * (c⁻¹ * b * c) := by group
        _ = c * b := by rw [hcb]
    calc c⁻¹ * b = c⁻¹ * (b * c) * c⁻¹ := by group
      _ = c⁻¹ * (c * b) * c⁻¹ := by rw [h1]
      _ = b * c⁻¹ := by group
  have h2 : c * (t * b) * c⁻¹ = c * t * c⁻¹ * b := by
    calc c * (t * b) * c⁻¹ = c * t * (b * c⁻¹) := by group
      _ = c * t * (c⁻¹ * b) := by rw [hbc]
      _ = c * t * c⁻¹ * b := by group
  calc (c⁻¹ * u * c * k) * t * (c⁻¹ * u * c * k)⁻¹
      = c⁻¹ * (u * (c * (k * t * k⁻¹) * c⁻¹) * u⁻¹) * c := by group
    _ = c⁻¹ * (u * (c * (t * b) * c⁻¹) * u⁻¹) * c := by rw [hkt]
    _ = c⁻¹ * (u * (c * t * c⁻¹ * b) * u⁻¹) * c := by rw [h2]
    _ = c⁻¹ * (c * t * c⁻¹ * a * b) * c := by rw [h1]
    _ = t * (a * b) := by
        rw [show c⁻¹ * (c * t * c⁻¹ * a * b) * c
          = t * (c⁻¹ * a * c) * (c⁻¹ * b * c) by group, hca, hcb]
        group

private theorem Good101.mem_Vt_of_exists_conj_mul (h34 : Stroth34Statement)
    (hspread : StrothNoA2SpreadStatement) {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n)
    {t : G} (ht : Good101 M Q Z B t) {Y : Subgroup G} (hs : Sit M Q Z Y t) {a b : G}
    (ha : a ∈ Q ⊓ QB Y) (hb : b ∈ B) (hbV : b ∈ Vt M (LB M Q B) B Z t)
    (hconj : ∃ g : G, g * t * g⁻¹ = t * (a * b)) : a ∈ Vt M (LB M Q B) B Z t := by
  have hbY : B ≤ QB Y :=
    hc.hyp.le_QB_of_mem_QB hc.conj hs.conj hs.mem hs.ne_one ht.2.2.2.1
  have hab : a * b ∈ Vt M (LB M Q B) B Z t :=
    ht.mem_Vt_of_conj h34 hspread H hs
      ⟨Q.mul_mem ha.1 (hc.le hb), (QB Y).mul_mem ha.2 (hbY hb)⟩ hconj
  have e : a = (a * b) * b⁻¹ := by group
  rw [e]
  exact (Vt M (LB M Q B) B Z t).mul_mem hab ((Vt M (LB M Q B) B Z t).inv_mem hbV)

private theorem Good101.mem_Vt_of_not_mem_centralizer_B (h34 : Stroth34Statement)
    (hspread : StrothNoA2SpreadStatement) {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n)
    {t : G} (ht : Good101 M Q Z B t) {Y : Subgroup G} (hs : Sit M Q Z Y t) {c u a y : G}
    (ha : a ∈ Q ⊓ QB Y) (hac : a ∈ Subgroup.centralizer ({c} : Set G))
    (hcB : c ∈ Subgroup.centralizer (B : Set G)) (hu : u ∈ QB Y) (hy : y ∈ Y)
    (hconj : u * (c * t * c⁻¹) * u⁻¹ = c * t * c⁻¹ * a * y)
    (huB : ∃ b ∈ B, u * b ≠ b * u) : a ∈ Vt M (LB M Q B) B Z t := by
  obtain ⟨hcY, -⟩ := Good101.exists_yFrame h34 hspread H ht hs
  have hbY : B ≤ QB Y :=
    hc.hyp.le_QB_of_mem_QB hc.conj hs.conj hs.mem hs.ne_one ht.2.2.2.1
  obtain ⟨b, hbB, hub⟩ := huB
  obtain ⟨b', hb'B, hcomm⟩ := hcY.exists_mem_comm_eq hbB hu (fun h => hub h.symm) hy
  have hbu : u * b' * u⁻¹ = y⁻¹ * b' := by
    have h1 : ⁅u, b'⁆ = y⁻¹ := by rw [← commutatorElement_inv, hcomm]
    calc u * b' * u⁻¹ = ⁅u, b'⁆ * b' := by rw [commutatorElement_def]; group
      _ = y⁻¹ * b' := by rw [h1]
  have hcb : c⁻¹ * b' * c = b' := by
    have h := Subgroup.mem_centralizer_iff.mp hcB b' hb'B
    calc c⁻¹ * b' * c = c⁻¹ * (b' * c) := by group
      _ = c⁻¹ * (c * b') := by rw [h]
      _ = b' := by group
  obtain ⟨k, -, hkt⟩ := ht.exists_conj_of_mem_Vt h34 hspread H hs ⟨hc.le hb'B, hbY hb'B⟩
    (hc.B_le_Vt ht.mem_LB hb'B)
  refine Good101.mem_Vt_of_exists_conj_mul h34 hspread H ht hs ha hb'B
    (hc.B_le_Vt ht.mem_LB hb'B) ⟨c⁻¹ * u * c * k, ?_⟩
  exact conj_mul_conj_eq_of_conj rfl (by
    rw [show c⁻¹ * a * c = a by
      rw [show c⁻¹ * a * c = c⁻¹ * (a * c) by group,
        show a * c = c * a from Subgroup.mem_centralizer_singleton_iff.mp hac]
      group]) hcb hkt hconj hbu

private theorem Good101.conj_eq_mul_ne_one (h34 : Stroth34Statement)
    (hspread : StrothNoA2SpreadStatement) {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n)
    {t : G} (ht : Good101 M Q Z B t) {Y : Subgroup G} (hs : Sit M Q Z Y t)
    (h2 : SLMNat hc t 2) {c : G} (hcQ : c ∈ Q) (hcB : c ∈ Subgroup.centralizer (B : Set G))
    (hcW : c ∉ Wt Q (Vt M (LB M Q B) B Z t)) {a : G}
    (ha : a ∈ Q ⊓ QB Y ⊓ Subgroup.centralizer ({c} : Set G)) (haB : a ∉ B) {u y : G}
    (hconj : u * (c * t * c⁻¹) * u⁻¹ = c * t * c⁻¹ * a * y) : y ≠ 1 := by
  intro hy1
  have hconj' : ∃ g : G, g * t * g⁻¹ = t * a := by
    refine ⟨c⁻¹ * u * c, ?_⟩
    calc (c⁻¹ * u * c) * t * (c⁻¹ * u * c)⁻¹
        = c⁻¹ * (u * (c * t * c⁻¹) * u⁻¹) * c := by group
      _ = c⁻¹ * (c * t * c⁻¹ * a) * c := by rw [hconj, hy1, mul_one]
      _ = t * a := by
          rw [show c⁻¹ * (c * t * c⁻¹ * a) * c = t * (c⁻¹ * a * c) by group,
            show c⁻¹ * a * c = a by
              rw [show c⁻¹ * a * c = c⁻¹ * (a * c) by group,
                show a * c = c * a from Subgroup.mem_centralizer_singleton_iff.mp ha.2]
              group]
  exact haB (Good101.mem_B_of_mem_Vt_of_centralizes ht hs h2 hcQ hcB hcW ha.1
    (ht.mem_Vt_of_conj h34 hspread H hs ha.1 hconj') ha.2)

private theorem Good101.mem_centralizer_B_of_conj_eq_mul (h34 : Stroth34Statement)
    (hspread : StrothNoA2SpreadStatement) {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n)
    {t : G} (ht : Good101 M Q Z B t) {Y : Subgroup G} (hs : Sit M Q Z Y t)
    (h2 : SLMNat hc t 2) {c : G} (hcQ : c ∈ Q) (hcB : c ∈ Subgroup.centralizer (B : Set G))
    (hcW : c ∉ Wt Q (Vt M (LB M Q B) B Z t)) {a : G}
    (ha : a ∈ Q ⊓ QB Y ⊓ Subgroup.centralizer ({c} : Set G)) (haB : a ∉ B) {u y : G}
    (hu : u ∈ QB Y) (hy : y ∈ Y)
    (hconj : u * (c * t * c⁻¹) * u⁻¹ = c * t * c⁻¹ * a * y) :
    u ∈ Subgroup.centralizer (B : Set G) := by
  by_contra hnot
  have hex : ∃ b ∈ B, u * b ≠ b * u := by
    by_contra hcon
    push Not at hcon
    exact hnot (Subgroup.mem_centralizer_iff.mpr fun b hb => (hcon b hb).symm)
  exact haB (Good101.mem_B_of_mem_Vt_of_centralizes ht hs h2 hcQ hcB hcW ha.1
    (Good101.mem_Vt_of_not_mem_centralizer_B h34 hspread H ht hs ha.1 ha.2 hcB hu hy hconj
      hex) ha.2)

private theorem conj_sq_eq_one_of_conj_eq_mul {w u a y : G}
    (hconj : u * w * u⁻¹ = w * a * y) (hww : w * w = 1)
    (hway : (a * y) * w = w * (a * y)) : (a * y) * (a * y) = 1 := by
  have h1 : ((w * a * y) * (w * a * y)) = 1 := by
    rw [← hconj]
    calc (u * w * u⁻¹) * (u * w * u⁻¹) = u * (w * w) * u⁻¹ := by group
      _ = 1 := by rw [hww]; group
  have h2 : ((w * a * y) * (w * a * y)) = (a * y) * (a * y) := by
    calc ((w * a * y) * (w * a * y))
        = w * ((a * y) * w) * (a * y) := by group
      _ = w * (w * (a * y)) * (a * y) := by rw [hway]
      _ = (w * w) * ((a * y) * (a * y)) := by group
      _ = (a * y) * (a * y) := by rw [hww]; group
  rw [← h2]; exact h1

private theorem Good101.commute_of_conj_eq_mul (h34 : Stroth34Statement)
    (hspread : StrothNoA2SpreadStatement) {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n)
    {t : G} (ht : Good101 M Q Z B t) {Y : Subgroup G} (hs : Sit M Q Z Y t)
    {c : G} (hcQ : c ∈ Q) (hcB : c ∈ Subgroup.centralizer (B : Set G)) {a : G}
    (ha : a ∈ Q ⊓ QB Y ⊓ Subgroup.centralizer ({c} : Set G)) {u y : G}
    (hu : u ∈ QB Y) (hy : y ∈ Y)
    (hconj : u * (c * t * c⁻¹) * u⁻¹ = c * t * c⁻¹ * a * y) : u * a = a * u := by
  obtain ⟨hcY, -⟩ := Good101.exists_yFrame h34 hspread H ht hs
  have hw : c * t * c⁻¹ ∈ LB (Subgroup.normalizer (Y : Set G)) (QB Y) B :=
    Good101.conj_mem_LB h34 H ht hs hcQ hcB
  have hww : (c * t * c⁻¹) * (c * t * c⁻¹) = 1 := by
    have ht2 : t * t = 1 := hs.x_sq
    calc (c * t * c⁻¹) * (c * t * c⁻¹) = c * (t * t) * c⁻¹ := by group
      _ = 1 := by rw [ht2]; group
  have hu2Y : u * u ∈ Y := by
    have h := CFSG.RankThree.GF2n.Stroth80.IsZConjugate.sq_mem_QB hc.hyp hs.conj
      (a := u) hu
    rwa [pow_two] at h
  have hu2w : (u * u) * (c * t * c⁻¹) = (c * t * c⁻¹) * (u * u) := by
    have h := hcY.LB_centralizes_Z hw (u * u) hu2Y
    calc (u * u) * (c * t * c⁻¹) = ((c * t * c⁻¹) * (u * u) * (c * t * c⁻¹)⁻¹) *
          (c * t * c⁻¹) := by rw [h]
      _ = (c * t * c⁻¹) * (u * u) := by group
  have hac : Commute a c := Subgroup.mem_centralizer_singleton_iff.mp ha.2
  have hat : Commute a t := (Sit.QB_comm_X hs hs.mem ha.1.2).symm
  have haw : Commute a (c * t * c⁻¹) := (hac.mul_right hat).mul_right hac.inv_right
  have hwy : Commute y (c * t * c⁻¹) := by
    have h := hcY.LB_centralizes_Z hw y hy
    refine (show Commute (c * t * c⁻¹) y from ?_).symm
    calc (c * t * c⁻¹) * y = ((c * t * c⁻¹) * y * (c * t * c⁻¹)⁻¹) * (c * t * c⁻¹) := by
          group
      _ = y * (c * t * c⁻¹) := by rw [h]
  have hway : (a * y) * (c * t * c⁻¹) = (c * t * c⁻¹) * (a * y) := haw.mul_left hwy
  have hay2 : (a * y) * (a * y) = 1 := conj_sq_eq_one_of_conj_eq_mul hconj hww hway
  have huy : u * y = y * u := (Sit.QB_comm_X hs hy hu).symm
  have huau : u * a * u⁻¹ = a := conj_eq_of_conj_eq_mul hconj hww hay2 huy hu2w
  calc u * a = (u * a * u⁻¹) * u := by group
    _ = a * u := by rw [huau]

theorem Good101.conj_eq_mul_facts (h34 : Stroth34Statement)
    (hspread : StrothNoA2SpreadStatement) {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n)
    {t : G} (ht : Good101 M Q Z B t) {Y : Subgroup G} (hs : Sit M Q Z Y t)
    (h2 : SLMNat hc t 2) {c : G} (hcQ : c ∈ Q) (hcB : c ∈ Subgroup.centralizer (B : Set G))
    (hcW : c ∉ Wt Q (Vt M (LB M Q B) B Z t)) {a : G}
    (ha : a ∈ Q ⊓ QB Y ⊓ Subgroup.centralizer ({c} : Set G)) (haB : a ∉ B) {u y : G}
    (hu : u ∈ QB Y) (hy : y ∈ Y) (hconj : u * (c * t * c⁻¹) * u⁻¹ = c * t * c⁻¹ * a * y) :
    y ≠ 1 ∧ u ∈ Subgroup.centralizer (B : Set G) ∧ u * a = a * u :=
  ⟨Good101.conj_eq_mul_ne_one h34 hspread H ht hs h2 hcQ hcB hcW ha haB hconj,
    Good101.mem_centralizer_B_of_conj_eq_mul h34 hspread H ht hs h2 hcQ hcB hcW ha haB hu hy
      hconj,
    Good101.commute_of_conj_eq_mul h34 hspread H ht hs hcQ hcB ha hu hy hconj⟩

private theorem mem_B_of_pi_mem_img_B_of_mem_Q {Y : Subgroup G} {K : Type} [Field K]
    {γ : G → K} {M₀ : Tim79.QuadModel (QB Y) Y K γ} {hc : Ctx M Q Z B} {x : G}
    (hZY : Y ⊓ Q = ⊥) (hxQ : x ∈ Q) (hxY : x ∈ QB Y) (hπ : M₀.π x ∈ M₀.img B) : x ∈ B := by
  obtain ⟨b, hbB, hbY, hπb⟩ := M₀.mem_img.mp hπ
  have hzb : x⁻¹ * b ∈ Y := (M₀.pi_eq_iff hxY hbY).mp hπb.symm
  have hzQ : x⁻¹ * b ∈ Q := Q.mul_mem (Q.inv_mem hxQ) (hc.le hbB)
  have h1 : x⁻¹ * b ∈ Y ⊓ Q := ⟨hzb, hzQ⟩
  rw [hZY, Subgroup.mem_bot] at h1
  have hxb : b = x := by
    calc b = x * (x⁻¹ * b) := by group
      _ = x := by rw [h1, mul_one]
  rwa [← hxb]

private theorem mem_B_of_pi_eq_smul_of_mem_B {Y : Subgroup G} {K : Type} [Field K]
    {γ : G → K} {M₀ : Tim79.QuadModel (QB Y) Y K γ} {hc : Ctx M Q Z B} {b₀ : M₀.E}
    (hBline : ∀ v : M₀.E, v ∈ M₀.img B ↔ ∃ s : K, v = s • b₀)
    (hZY : Y ⊓ Q = ⊥) {a x : G} (ha : a ∈ Q ⊓ QB Y) (hx : x ∈ Q ⊓ QB Y) {lam : K}
    (hlam : lam ≠ 0) (hπ : M₀.π x = lam • M₀.π a) (hxB : x ∈ B) : a ∈ B := by
  obtain ⟨s, hs⟩ := (hBline _).mp (M₀.pi_mem_img hxB hx.2)
  have h1 : lam • M₀.π a = s • b₀ := by rw [← hπ, hs]
  have h2 : M₀.π a = lam⁻¹ • (s • b₀) := by
    rw [← h1, smul_smul, inv_mul_cancel₀ hlam, one_smul]
  exact mem_B_of_pi_mem_img_B_of_mem_Q (Y := Y) (K := K) (γ := γ) (M₀ := M₀) (hc := hc)
    (x := a) hZY ha.1 ha.2 ((hBline _).mpr ⟨lam⁻¹ * s, by rw [h2, smul_smul]⟩)

private theorem centralizes_of_pi_eq_smul {Y : Subgroup G} {K : Type} [Field K] {γ : G → K}
    {M₀ : Tim79.QuadModel (QB Y) Y K γ}
    (hDY : GlobalModelData (Subgroup.normalizer (Y : Set G)) (QB Y) Y γ M₀)
    {a a' u : G} {lam : K} (hu : u ∈ QB Y) (ha : a ∈ QB Y) (ha' : a' ∈ QB Y)
    (hua : u * a = a * u) (hπ : M₀.π a' = lam • M₀.π a) : u * a' = a' * u := by
  have hcomm : ⁅u, a'⁆ = 1 := by
    refine hDY.reg.inj ⁅u, a'⁆ (M₀.comm_mem u hu a' ha') ?_
    have hB0 : M₀.B (M₀.π u) (M₀.π a) = 0 := (M₀.comm_iff_B hDY.reg hu ha).mp hua
    calc γ ⁅u, a'⁆ = M₀.B (M₀.π u) (M₀.π a') := M₀.comm_eq u hu a' ha'
      _ = M₀.B (M₀.π u) (lam • M₀.π a) := by rw [hπ]
      _ = lam • M₀.B (M₀.π u) (M₀.π a) := by rw [map_smul]
      _ = lam • (0 : K) := by rw [hB0]
      _ = 0 := smul_zero lam
  exact commutatorElement_eq_one_iff_mul_comm.mp hcomm

theorem Good101.exists_mem_centralizer_scalar (h34 : Stroth34Statement)
    (hspread : StrothNoA2SpreadStatement) {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n)
    {t : G} (ht : Good101 M Q Z B t) {Y : Subgroup G} (hs : Sit M Q Z Y t)
    (hAB : Q ⊓ QB Y ≤ QB B) {c : G} (hcQ : c ∈ Q) (hcB : c ∈ Subgroup.centralizer (B : Set G))
    (hcW : c ∉ Wt Q (Vt M (LB M Q B) B Z t)) {a : G}
    (ha : a ∈ Q ⊓ QB Y ⊓ Subgroup.centralizer ({c} : Set G)) (haB : a ∉ B) :
    ∃ a' ∈ Q ⊓ QB Y ⊓ Subgroup.centralizer ({c} : Set G), a' ∉ B ∧ a * a' ∉ B ∧
      ∀ u ∈ QB Y, u * a = a * u → u * a' = a' * u := by
  obtain ⟨hcY, HY⟩ := Good101.exists_yFrame h34 hspread H ht hs
  obtain ⟨K, _, _, _, γ, M₀, hDY⟩ := stroth_globalModelData hcY.hyp
  have hK : 4 ≤ Nat.card K := by
    rw [hDY.card]
    obtain ⟨g, hg⟩ := hs.conj
    rw [hg, card_conjSubgroup]
    have := hc.hyp.q4
    omega
  obtain ⟨lam, hlam0, hlam1⟩ := exists_ne_zero_ne_one K hK
  have hSm : lam • M₀.π a ∈ M₀.img (Q ⊓ QB Y ⊓ Subgroup.centralizer ({c} : Set G)) :=
    Good101.smul_mem_img_centralizer h34 hspread H ht hs hAB hcY HY hDY hcQ hcB hcW lam
      (M₀.pi_mem_img ⟨ha.1, ha.2⟩ ha.1.2)
  obtain ⟨a', ha', -, ha'π⟩ := M₀.mem_img.mp hSm
  obtain ⟨b₀, -, -, hBline, -, -⟩ := hcY.dictB hDY
  have hZY : Y ⊓ Q = ⊥ := hs.X_inf_Q
  have ha'B : a' ∉ B := fun hB =>
    haB (mem_B_of_pi_eq_smul_of_mem_B (Y := Y) (K := K) (γ := γ) (M₀ := M₀) (hc := hc)
      (x := a') hBline hZY ha.1 ⟨ha'.1.1, ha'.1.2⟩ hlam0 ha'π hB)
  have h1lam : (1 + lam : K) ≠ 0 := by
    intro h0
    exact hlam1 (CharTwo.add_eq_zero.mp h0).symm
  have hπaa' : M₀.π (a * a') = (1 + lam) • M₀.π a := by
    rw [M₀.π_mul a ha.1.2 a' ha'.1.2, ha'π, add_smul, one_smul]
  have haa'B : a * a' ∉ B := fun hB =>
    haB (mem_B_of_pi_eq_smul_of_mem_B (Y := Y) (K := K) (γ := γ) (M₀ := M₀) (hc := hc)
      (x := a * a') hBline hZY ha.1 ⟨Q.mul_mem ha.1.1 ha'.1.1,
        (QB Y).mul_mem ha.1.2 ha'.1.2⟩ h1lam hπaa' hB)
  refine ⟨a', ha', ha'B, haa'B, ?_⟩
  intro u hu hua
  exact centralizes_of_pi_eq_smul hDY hu ha.1.2 ha'.1.2 hua ha'π

private theorem mul_conj_eq_mul {w u₁ u₂ α a y₁ y₂ : G}
    (hconj₁ : u₁ * w * u₁⁻¹ = w * α * y₁) (hconj₂ : u₂ * w * u₂⁻¹ = w * a * y₂)
    (hcent : u₁ * a * u₁⁻¹ = a) (huy : u₁ * y₂ = y₂ * u₁) :
    (u₁ * u₂) * w * (u₁ * u₂)⁻¹ = w * α * y₁ * a * y₂ := by
  have huy' : u₁ * y₂ * u₁⁻¹ = y₂ := by
    calc u₁ * y₂ * u₁⁻¹ = (y₂ * u₁) * u₁⁻¹ := by rw [huy]
      _ = y₂ := by group
  calc (u₁ * u₂) * w * (u₁ * u₂)⁻¹ = u₁ * (u₂ * w * u₂⁻¹) * u₁⁻¹ := by group
    _ = u₁ * (w * a * y₂) * u₁⁻¹ := by rw [hconj₂]
    _ = (u₁ * w * u₁⁻¹) * (u₁ * a * u₁⁻¹) * (u₁ * y₂ * u₁⁻¹) := by group
    _ = (w * α * y₁) * a * y₂ := by rw [hconj₁, hcent, huy']

private theorem Good101.false_of_both_conj_eq_mul (h34 : Stroth34Statement)
    (hspread : StrothNoA2SpreadStatement) {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n)
    {t : G} (ht : Good101 M Q Z B t) {Y : Subgroup G} (hs : Sit M Q Z Y t)
    (h2 : SLMNat hc t 2) {c : G} (hcQ : c ∈ Q) (hcB : c ∈ Subgroup.centralizer (B : Set G))
    (hcW : c ∉ Wt Q (Vt M (LB M Q B) B Z t)) {α a' : G}
    (hα : α ∈ Q ⊓ QB Y ⊓ Subgroup.centralizer ({c} : Set G))
    (ha' : a' ∈ Q ⊓ QB Y ⊓ Subgroup.centralizer ({c} : Set G)) (haa'B : α * a' ∉ B)
    (hcent : ∀ u ∈ QB Y, u * α = α * u → u * a' = a' * u) {u₁ u₂ y₁ y₂ : G}
    (hu₁ : u₁ ∈ QB Y) (hu₂ : u₂ ∈ QB Y) (hy₂ : y₂ ∈ Y) (hu₁α : u₁ * α = α * u₁)
    (hconj₁ : u₁ * (c * t * c⁻¹) * u₁⁻¹ = c * t * c⁻¹ * α * y₁)
    (hconj₂ : u₂ * (c * t * c⁻¹) * u₂⁻¹ = c * t * c⁻¹ * a' * y₂)
    (h1 : y₁ = t) (h2' : y₂ = t) : False := by
  have hmem : α * a' ∈ Q ⊓ QB Y ⊓ Subgroup.centralizer ({c} : Set G) :=
    ⟨⟨Q.mul_mem hα.1.1 ha'.1.1, (QB Y).mul_mem hα.1.2 ha'.1.2⟩,
      (Subgroup.centralizer ({c} : Set G)).mul_mem hα.2 ha'.2⟩
  have hta' : t * a' = a' * t := Sit.QB_comm_X hs hs.mem ha'.1.2
  have hcent' : u₁ * a' * u₁⁻¹ = a' := by
    calc u₁ * a' * u₁⁻¹ = (a' * u₁) * u₁⁻¹ := by rw [hcent u₁ hu₁ hu₁α]
      _ = a' := by group
  have hconj12 : (u₁ * u₂) * (c * t * c⁻¹) * (u₁ * u₂)⁻¹ =
      (c * t * c⁻¹) * (α * a') * 1 := by
    rw [mul_conj_eq_mul hconj₁ hconj₂ hcent' (Sit.QB_comm_X hs hy₂ hu₁).symm]
    calc (c * t * c⁻¹) * α * y₁ * a' * y₂ = (c * t * c⁻¹) * α * t * a' * t := by
          rw [h1, h2']
      _ = (c * t * c⁻¹) * α * (t * a') * t := by group
      _ = (c * t * c⁻¹) * α * (a' * t) * t := by rw [hta']
      _ = (c * t * c⁻¹) * α * a' * (t * t) := by group
      _ = (c * t * c⁻¹) * (α * a') * 1 := by rw [hs.x_sq]; group
  have hne := (Good101.conj_eq_mul_facts h34 hspread H ht hs h2 hcQ hcB hcW hmem haa'B
    ((QB Y).mul_mem hu₁ hu₂) (Y.one_mem) hconj12).1
  exact hne rfl

theorem Good101.exists_conj_eq_mul_ne (h34 : Stroth34Statement)
    (hspread : StrothNoA2SpreadStatement) {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n)
    {t : G} (ht : Good101 M Q Z B t) {Y : Subgroup G} (hs : Sit M Q Z Y t)
    (h2 : SLMNat hc t 2) (hAB : Q ⊓ QB Y ≤ QB B) {c : G} (hcQ : c ∈ Q)
    (hcB : c ∈ Subgroup.centralizer (B : Set G)) (hcW : c ∉ Wt Q (Vt M (LB M Q B) B Z t))
    (hA' : CaseA (QB Y) Y (c * t * c⁻¹)) {α : G}
    (hα : α ∈ Q ⊓ QB Y ⊓ Subgroup.centralizer ({c} : Set G))
    (hαV : α ∉ Vt M (LB M Q B) B Z t) :
    ∃ a ∈ Q ⊓ QB Y ⊓ Subgroup.centralizer ({c} : Set G), a ∉ B ∧
      ∃ u ∈ QB Y, u ∈ Subgroup.centralizer (B : Set G) ∧
        ∃ y ∈ Y, y ≠ t ∧ u * (c * t * c⁻¹) * u⁻¹ = c * t * c⁻¹ * a * y := by
  have hαB : α ∉ B := fun h => hαV (hc.B_le_Vt ht.mem_LB h)
  obtain ⟨a', ha', ha'B, haa'B, hcent⟩ :=
    Good101.exists_mem_centralizer_scalar h34 hspread H ht hs hAB hcQ hcB hcW hα hαB
  obtain ⟨u₁, hu₁, y₁, hy₁, hconj₁⟩ :=
    Good101.exists_conj_eq_mul_of_caseA_conj h34 hspread H ht hs hcQ hcB hcW hA' hα
  obtain ⟨u₂, hu₂, y₂, hy₂, hconj₂⟩ :=
    Good101.exists_conj_eq_mul_of_caseA_conj h34 hspread H ht hs hcQ hcB hcW hA' ha'
  obtain ⟨-, hu₁B, hu₁α⟩ :=
    Good101.conj_eq_mul_facts h34 hspread H ht hs h2 hcQ hcB hcW hα hαB hu₁ hy₁ hconj₁
  obtain ⟨-, hu₂B, -⟩ :=
    Good101.conj_eq_mul_facts h34 hspread H ht hs h2 hcQ hcB hcW ha' ha'B hu₂ hy₂ hconj₂
  by_cases h1 : y₁ = t
  · by_cases h2' : y₂ = t
    · exact (Good101.false_of_both_conj_eq_mul h34 hspread H ht hs h2 hcQ hcB hcW hα ha' haa'B
        hcent hu₁ hu₂ hy₂ hu₁α hconj₁ hconj₂ h1 h2').elim
    · exact ⟨a', ha', ha'B, u₂, hu₂, hu₂B, y₂, hy₂, h2', hconj₂⟩
  · exact ⟨α, hα, hαB, u₁, hu₁, hu₁B, y₁, hy₁, h1, hconj₁⟩

end CFSG.RankThree.GF2n.Stroth80
