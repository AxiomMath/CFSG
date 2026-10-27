module

public import CFSG.RankThree.GF2n.Stroth80.Sec10Fuse
public import CFSG.RankThree.GF2n.Stroth80.Sec10Perp
public import CFSG.RankThree.GF2n.Stroth80.Sec10Four

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n.Smith81
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem Ctx.Tt_le_inf_QB (hc : Ctx M Q Z B) {t : G} (ht : Good101 M Q Z B t) :
    Tt Q Z (Vt M (LB M Q B) B Z t) t ≤ Q ⊓ QB B := by
  have h1 := hc.Tt_comm_le_inf_QB (t := t) ht.mem_LB (m := (1 : G)) M.one_mem (by
    rw [conjSubgroup_one]; exact ht.mem_LB)
  rw [conjSubgroup_one] at h1
  have h1' : ⁅Wt Q (Vt M (LB M Q B) B Z t), Subgroup.zpowers t⁆ ≤ Q ⊓ QB B := h1
  exact sup_le h1' fun z hz => Subgroup.mem_inf.mpr ⟨hc.Z_le_Q hz, (Ctx.Z_le_QB hc).1 hz⟩

theorem Ctx.inf_QB_le_CN (hc : Ctx M Q Z B) {t : G} (ht : Good103 M Q Z B t)
    {Y : Subgroup G} (hs : Sit M Q Z Y t) :
    QB B ⊓ QB Y ⊓ M ≤ hc.CN t := by
  intro p hp
  obtain ⟨⟨hpB, hpY⟩, hpM⟩ := Subgroup.mem_inf.mp hp
  have hpR : p ∈ Rt M (LB M Q B) t :=
    le_Rt (LB M Q B) ht.1.mem_LB (Subgroup.mem_sup_right ⟨hpB, hpM⟩)
  exact Ctx.Rt_inf_le_CN hc hs (Good103.Vt_eq ht hs)
    (Subgroup.mem_inf.mpr ⟨hpR, ⟨hpY, hpM⟩⟩)

theorem Ctx.inf_QB_le_centralizer_Vt (hc : Ctx M Q Z B) {t : G}
    (ht : Good103 M Q Z B t) {Y : Subgroup G} (hs : Sit M Q Z Y t) :
    QB B ⊓ QB Y ⊓ M ≤ Subgroup.centralizer (Vt M (LB M Q B) B Z t : Set G) := by
  intro p hp
  obtain ⟨⟨hpB, hpY⟩, hpM⟩ := Subgroup.mem_inf.mp hp
  have hpLB : p ∈ LB M Q B := Subgroup.mem_sup_right ⟨hpB, hpM⟩
  refine Subgroup.mem_centralizer_iff.mpr fun v hv => ?_
  rw [Good103.Vt_eq ht hs] at hv
  have hnorm : Q ⊓ QB Y ≤ Subgroup.normalizer (Z : Set G) :=
    fun x hx => hs.hyp.Z_normal.2 (hs.hyp.Q_normal.1 hx.1)
  obtain ⟨a, ha, z, hz, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer hnorm hv
  obtain ⟨haQ, haY⟩ := Subgroup.mem_inf.mp ha
  have hpa : p * a = a * p := by
    have hmem : ⁅p, a⁆ ∈ Y ⊓ Q :=
      ⟨hs.comm_QB_mem_X hpY haY, by
        rw [commutatorElement_def]
        exact Q.mul_mem
          ((Subgroup.mem_normalizer_iff.mp (hs.hyp.Q_normal.2 hpM) a).mp haQ) (Q.inv_mem haQ)⟩
    rw [hs.X_inf_Q, Subgroup.mem_bot] at hmem
    exact commutatorElement_eq_one_iff_mul_comm.mp hmem
  have hzp : z * p = p * z := by
    have h1 := hc.LB_centralizes_Z hpLB z hz
    calc z * p = (p * z * p⁻¹) * p := by rw [h1]
      _ = p * z := by group
  calc (a * z) * p = a * (z * p) := by rw [mul_assoc]
    _ = a * (p * z) := by rw [hzp]
    _ = (a * p) * z := by rw [mul_assoc]
    _ = (p * a) * z := by rw [hpa]
    _ = p * (a * z) := by rw [mul_assoc]

private theorem card_Wt_QB_mul_le (hc : Ctx M Q Z B) {X : Subgroup G} (hBX : B ≤ X)
    (hXQB : X ≤ QB B) :
    Nat.card ↥(Wt (QB B) X) * Nat.card X ≤ Nat.card (QB B) * Nat.card B := by
  obtain ⟨g, hg⟩ := hc.conj
  have hH : StrothHyp (conjSubgroup g M) (QB B) B := by
    have h := StrothHyp.conj hc.hyp g
    rwa [← (Ctx.QB_eq hc hg).2, ← hg] at h
  exact StrothHyp.card_Wt_mul_card_le hH hXQB hBX

private theorem card_sup_mul_card_inf_AP (hc : Ctx M Q Z B) (Y : Subgroup G) :
    Nat.card ↥(Q ⊓ QB B ⊔ (QB B ⊓ QB Y ⊓ M)) *
        Nat.card ↥(Q ⊓ QB B ⊓ (QB B ⊓ QB Y ⊓ M)) =
      Nat.card ↥(Q ⊓ QB B) * Nat.card ↥(QB B ⊓ QB Y ⊓ M) := by
  refine card_sup_mul_card_inf_of_normalizer (A := Q ⊓ QB B) (C := QB B ⊓ QB Y ⊓ M) ?_
  intro p hp
  obtain ⟨⟨hpB, hpY⟩, hpM⟩ := Subgroup.mem_inf.mp hp
  refine conjSubgroup_eq_self_iff.mp ?_
  show conjSubgroup p (Q ⊓ QB B) = Q ⊓ QB B
  rw [conjSubgroup_inf, hc.conj_Q_eq hpM,
    conjSubgroup_eq_self_iff.mpr (Subgroup.le_normalizer hpB)]

private theorem inf_centralizer_le_Wt (hc : Ctx M Q Z B) (Y : Subgroup G) :
    Q ⊓ QB B ⊓ Subgroup.centralizer ((QB B ⊓ QB Y ⊓ M : Subgroup G) : Set G) ≤
      Wt (QB B) (Q ⊓ QB B ⊔ (QB B ⊓ QB Y ⊓ M)) := by
  intro c hcC
  obtain ⟨hcA, hcP⟩ := Subgroup.mem_inf.mp hcC
  refine Subgroup.mem_inf.mpr ⟨hcA.2, ?_⟩
  have hAcent : Q ⊓ QB B ≤ Subgroup.centralizer (Subgroup.zpowers c : Set G) := by
    intro a ha
    haveI : IsMulCommutative ↥(Q ⊓ QB B) := hc.inf_QB_elemAbelian.1
    have hcomm : Commute a c :=
      Subgroup.mul_comm_of_mem_isMulCommutative (H := Q ⊓ QB B) ha hcA
    refine Subgroup.mem_centralizer_iff.mpr fun x hx => ?_
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact (hcomm.zpow_right k).eq.symm
  have hPcent : QB B ⊓ QB Y ⊓ M ≤ Subgroup.centralizer (Subgroup.zpowers c : Set G) :=
    (Subgroup.le_centralizer_iff).mpr (Subgroup.zpowers_le.mpr hcP)
  have h2 : Subgroup.zpowers c ≤
      Subgroup.centralizer (((Q ⊓ QB B) ⊔ (QB B ⊓ QB Y ⊓ M) : Subgroup G) : Set G) :=
    (Subgroup.le_centralizer_iff).mp (sup_le hAcent hPcent)
  exact h2 (Subgroup.mem_zpowers c)

private theorem card_le_pow_of_bounds {c s i a p q n m : ℕ} (hq : 0 < q)
    (hcs : c * s ≤ q ^ (2 * n + 1) * q) (hsi : s * i = a * p) (ha : a = q ^ (n + 1))
    (hp : q ^ n ≤ p) (hi : i ≤ q ^ m) : c ≤ q ^ (m + 1) := by
  have hqi : q ^ (n + 1) * q ^ n = q ^ (2 * n + 1) := by rw [← pow_add]; congr 1; omega
  have hsi' : q ^ (2 * n + 1) ≤ s * i := by
    rw [← hqi, hsi, ← ha]
    exact Nat.mul_le_mul_left _ hp
  have hkey : c * q ^ (2 * n + 1) ≤ q ^ (2 * n + 1) * q ^ (m + 1) := by
    calc c * q ^ (2 * n + 1)
        ≤ c * (s * i) := Nat.mul_le_mul_left _ hsi'
      _ = c * s * i := by ring
      _ ≤ q ^ (2 * n + 1) * q * i := Nat.mul_le_mul_right _ hcs
      _ ≤ q ^ (2 * n + 1) * q * q ^ m := Nat.mul_le_mul_left _ hi
      _ = q ^ (2 * n + 1) * q ^ (m + 1) := by rw [mul_assoc, ← pow_succ']
  rw [mul_comm c (q ^ (2 * n + 1))] at hkey
  exact Nat.le_of_mul_le_mul_left hkey (pow_pos hq _)

private theorem pow_le_card_inf_QB (hspread : StrothNoA2SpreadStatement)
    {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n) {t : G} (ht : Good103 M Q Z B t)
    {Y : Subgroup G} (hs : Sit M Q Z Y t) : Nat.card Z ^ n ≤ Nat.card ↥(QB B ⊓ QB Y ⊓ M) := by
  have hBY : B ≠ Y := by
    intro hEq
    exact ht.1.2.2.1 (hc.le (by rw [hEq]; exact hs.mem))
  have hBQY : B ≤ QB Y :=
    hc.hyp.le_QB_of_mem_QB hc.conj hs.conj hs.mem hs.ne_one ht.1.2.2.2.1
  exact H.pow_le_card_QB_inf_QB_inf hspread hc hs.conj hBY hBQY

private theorem card_inf_AP_le (hc : Ctx M Q Z B) {t : G} (ht : Good103 M Q Z B t)
    {Y : Subgroup G} (hs : Sit M Q Z Y t) {m : ℕ}
    (hVcard : Nat.card ↥(Vt M (LB M Q B) B Z t) = Nat.card Z ^ (m + 1)) :
    Nat.card ↥(Q ⊓ QB B ⊓ (QB B ⊓ QB Y ⊓ M)) ≤ Nat.card Z ^ m := by
  have hle : Q ⊓ QB B ⊓ (QB B ⊓ QB Y ⊓ M) ≤ Q ⊓ QB Y :=
    le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans (inf_le_left.trans inf_le_right))
  calc Nat.card ↥(Q ⊓ QB B ⊓ (QB B ⊓ QB Y ⊓ M)) ≤ Nat.card ↥(Q ⊓ QB Y) :=
        Nat.card_le_card_of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective _)
    _ = Nat.card Z ^ m := Good103.card_inf_QB_eq_pow hc ht hs hVcard

private theorem Vt_le_inf_centralizer (h34 : Stroth34Statement) {hc : Ctx M Q Z B} {n : ℕ}
    (H : Sec10Hyp hc n) {t : G} (ht : Good103 M Q Z B t) {Y : Subgroup G} (hs : Sit M Q Z Y t) :
    Vt M (LB M Q B) B Z t ≤
      Q ⊓ QB B ⊓ Subgroup.centralizer ((QB B ⊓ QB Y ⊓ M : Subgroup G) : Set G) := by
  have h5 : Sec5Hyp hc n t := H.toSec5 ht.1.mem_LB ht.1.2.2.1
  obtain ⟨m', hm', hsl'⟩ := SLlike.exists_SLMNat (H.slLike ht.1)
  have hVQB : Vt M (LB M Q B) B Z t ≤ QB B :=
    stroth310SL_of_34 h34 G M Q Z B hc n t h5 (SLMNat.toSLNat hsl' hm')
  exact le_inf (le_inf (hc.Vt_le_Q t) hVQB)
    ((Subgroup.le_centralizer_iff).mpr (Ctx.inf_QB_le_centralizer_Vt hc ht hs))

theorem Sec10Hyp.inf_centralizer_le_Vt (h34 : Stroth34Statement)
    (hspread : StrothNoA2SpreadStatement) {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n)
    {t : G} (ht : Good103 M Q Z B t) {Y : Subgroup G} (hs : Sit M Q Z Y t) :
    Q ⊓ QB B ⊓ Subgroup.centralizer ((QB B ⊓ QB Y ⊓ M : Subgroup G) : Set G) ≤
      Vt M (LB M Q B) B Z t := by
  set A : Subgroup G := Q ⊓ QB B
  set P : Subgroup G := QB B ⊓ QB Y ⊓ M
  set V := Vt M (LB M Q B) B Z t
  set Cc : Subgroup G := A ⊓ Subgroup.centralizer (P : Set G)
  obtain ⟨m, hm2, hVcard, -⟩ := H.exists_card_Vt_card_LB_inf_CN h34 ht.1
  have hn1 : 1 ≤ n := by have := H.n_gt; omega
  obtain ⟨g, hg⟩ := hc.conj
  have hQBcard : Nat.card (QB B) = Nat.card Z ^ (2 * n + 1) := by
    rw [(Ctx.QB_eq hc hg).2, card_conjSubgroup, H.width]
  have hBcard : Nat.card B = Nat.card Z := by rw [hg, card_conjSubgroup]
  have hBleA : B ≤ A := by
    refine le_inf hc.le ?_
    rw [(Ctx.QB_eq hc hg).2, hg]
    exact Subgroup.map_mono hc.hyp.Z_normal.1
  have hCcard : Nat.card Cc ≤ Nat.card Z ^ (m + 1) := by
    have hAPleQB : A ⊔ P ≤ QB B := sup_le inf_le_right (inf_le_left.trans inf_le_left)
    have hCleCard : Nat.card Cc ≤ Nat.card ↥(Wt (QB B) (A ⊔ P)) :=
      Nat.card_le_card_of_injective (Subgroup.inclusion (inf_centralizer_le_Wt hc Y))
        (Subgroup.inclusion_injective _)
    have hcs : Nat.card Cc * Nat.card ↥(A ⊔ P) ≤ Nat.card Z ^ (2 * n + 1) * Nat.card Z :=
      (Nat.mul_le_mul_right _ hCleCard).trans
        (by rw [← hQBcard, ← hBcard]
            exact card_Wt_QB_mul_le hc (hBleA.trans le_sup_left) hAPleQB)
    have hAcard : Nat.card A = Nat.card Z ^ (n + 1) :=
      (hc.card_of_3_3 H.width hn1 H.noA2 (stroth_3_3 hc H.width hn1)).2
    exact card_le_pow_of_bounds Nat.card_pos hcs (card_sup_mul_card_inf_AP hc Y) hAcard
      (pow_le_card_inf_QB hspread H ht hs) (card_inf_AP_le hc ht hs hVcard)
  refine (Subgroup.eq_of_le_of_card_ge (Vt_le_inf_centralizer h34 H ht hs) ?_).ge
  calc Nat.card Cc ≤ Nat.card Z ^ (m + 1) := hCcard
    _ = Nat.card V := hVcard.symm

theorem Sec10Hyp.comm_mem_Vt_of_mem_centralizer (h34 : Stroth34Statement)
    (h311a : Stroth311aStatement) (hspread : StrothNoA2SpreadStatement) {hc : Ctx M Q Z B}
    {n : ℕ} (H : Sec10Hyp hc n) {t : G} (ht : Good103 M Q Z B t) {Y : Subgroup G}
    (hs : Sit M Q Z Y t) {c x : G} (hcC : c ∈ Q ⊓ Subgroup.centralizer ({t} : Set G))
    (hx : x ∈ hc.CN t) : ⁅c, x⁆ ∈ Vt M (LB M Q B) B Z t := by
  set V := Vt M (LB M Q B) B Z t
  obtain ⟨hcQ, hct⟩ := Subgroup.mem_inf.mp hcC
  have hct' : c * t = t * c :=
    (Subgroup.mem_centralizer_iff.mp hct t (Set.mem_singleton t)).symm
  have hQBYc : c ∈ Subgroup.normalizer (QB Y : Set G) := by
    refine conjSubgroup_eq_self_iff.mp ?_
    rw [← QB_conj c Y, conjSubgroup_eq_self_iff.mpr (mem_normalizer_of_comm_Y hs hct')]
  have hsup : x ∈ Q ⊔ QB Y ⊓ M := (H.CN_le_sup h34 h311a hspread ht hs) hx
  have hsup' : x ∈ (QB Y ⊓ M) ⊔ Q := by rw [sup_comm]; exact hsup
  obtain ⟨y, hy, a, ha, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer
    (H := QB Y ⊓ M) (K := Q) (fun z hz => hs.hyp.Q_normal.2 (Subgroup.mem_inf.mp hz).2) hsup'
  have hcy : ⁅c, y⁆ ∈ V := by
    have hQ : ⁅c, y⁆ ∈ Q := by
      have h1 : ⁅y, c⁆ ∈ Q := by
        rw [commutatorElement_def]
        exact Q.mul_mem
          ((Subgroup.mem_normalizer_iff.mp (hs.hyp.Q_normal.2 hy.2) c).mp hcQ) (Q.inv_mem hcQ)
      have e : ⁅c, y⁆ = (⁅y, c⁆)⁻¹ := by
        rw [← commutatorElement_inv c y, inv_inv]
      rw [e]
      exact Q.inv_mem h1
    have hY : ⁅c, y⁆ ∈ QB Y := by
      rw [commutatorElement_def]
      exact (QB Y).mul_mem
        ((Subgroup.mem_normalizer_iff.mp hQBYc y).mp hy.1) ((QB Y).inv_mem hy.1)
    have hVeq : V = (Q ⊓ QB Y) ⊔ Z := Good103.Vt_eq ht hs
    rw [hVeq]
    exact Subgroup.mem_sup_left ⟨hQ, hY⟩
  have hya : y * ⁅c, a⁆ * y⁻¹ ∈ V := by
    have h1 : y * ⁅c, a⁆ * y⁻¹ ∈ Z :=
      (Subgroup.mem_normalizer_iff.mp (hs.hyp.Z_normal.2 hy.2) _).mp
        (comm_mem_Z hs.hyp hcQ ha)
    exact sec39_Z_le_Vt h1
  rw [show ⁅c, y * a⁆ = ⁅c, y⁆ * (y * ⁅c, a⁆ * y⁻¹) by
    simp only [commutatorElement_def]; group]
  exact V.mul_mem hcy hya

private theorem commutator_Wt_CN_eq_bot (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (hspread : StrothNoA2SpreadStatement) {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n)
    {t : G} (ht : Good103 M Q Z B t) {Y : Subgroup G} (hs : Sit M Q Z Y t) :
    ⁅⁅Wt Q (Vt M (LB M Q B) B Z t), hc.CN t⁆, Q ⊓ Subgroup.centralizer ({t} : Set G)⁆ = ⊥ := by
  set V := Vt M (LB M Q B) B Z t
  set Cc : Subgroup G := Q ⊓ Subgroup.centralizer ({t} : Set G)
  set W : Subgroup G := Wt Q V
  set N : Subgroup G := hc.CN t
  have hNC : ⁅N, Cc⁆ ≤ V := by
    refine Subgroup.commutator_le.mpr fun n hn c hc' => ?_
    have h1 := H.comm_mem_Vt_of_mem_centralizer h34 h311a hspread ht hs hc' hn
    have e : ⁅n, c⁆ = (⁅c, n⁆)⁻¹ := by
      rw [← commutatorElement_inv n c, inv_inv]
    rw [e]
    exact V.inv_mem h1
  have hVW : ⁅V, W⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact (Subgroup.le_centralizer_iff).mpr inf_le_right
  have hCcQ : Cc ≤ Q := inf_le_left
  have hWQ : W ≤ Q := inf_le_left
  have hCW : ⁅Cc, W⁆ ≤ Z :=
    Subgroup.commutator_le.mpr fun c hc' w hw' => comm_mem_Z hs.hyp (hCcQ hc') (hWQ hw')
  have hZN : ⁅Z, N⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro z hz
    refine Subgroup.mem_centralizer_iff.mpr fun n hn => ?_
    have hnZ : n ∈ Subgroup.centralizer (Z : Set G) :=
      (Subgroup.mem_inf.mp (hc.Rt_le_H0 t (Ctx.mem_CN.mp hn).1)).2
    exact (Subgroup.mem_centralizer_iff.mp hnZ z hz).symm
  have h1 : ⁅⁅N, Cc⁆, W⁆ = ⊥ := by
    rw [eq_bot_iff]
    exact (Subgroup.commutator_mono hNC le_rfl).trans (le_of_eq hVW)
  have h2 : ⁅⁅Cc, W⁆, N⁆ = ⊥ := by
    rw [eq_bot_iff]
    exact (Subgroup.commutator_mono hCW le_rfl).trans (le_of_eq hZN)
  exact Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2

theorem Sec10Hyp.comm_Wt_CN_le_Wt (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (hspread : StrothNoA2SpreadStatement) {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n)
    {t : G} (ht : Good103 M Q Z B t) {Y : Subgroup G} (hs : Sit M Q Z Y t)
    {w x : G} (hw : w ∈ Wt Q (Vt M (LB M Q B) B Z t)) (hx : x ∈ hc.CN t) :
    ⁅w, x⁆ ∈ Wt Q (Q ⊓ Subgroup.centralizer ({t} : Set G)) := by
  set Cc : Subgroup G := Q ⊓ Subgroup.centralizer ({t} : Set G)
  set W : Subgroup G := Wt Q (Vt M (LB M Q B) B Z t)
  set N : Subgroup G := hc.CN t
  have hcomm : ⁅⁅W, N⁆, Cc⁆ = ⊥ := commutator_Wt_CN_eq_bot h34 h311a hspread H ht hs
  have hxM : x ∈ M := hc.Rt_le_M t (Ctx.mem_CN.mp hx).1
  have hwQ : w ∈ Q := hw.1
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · have hxw : ⁅x, w⁆ ∈ Q := by
      rw [commutatorElement_def]
      exact Q.mul_mem ((Subgroup.mem_normalizer_iff.mp (hs.hyp.Q_normal.2 hxM) w).mp hwQ)
        (Q.inv_mem hwQ)
    have e : ⁅w, x⁆ = (⁅x, w⁆)⁻¹ := by rw [← commutatorElement_inv w x, inv_inv]
    rw [e]
    exact Q.inv_mem hxw
  · refine Subgroup.mem_centralizer_iff.mpr fun c hc' => ?_
    have hwx : ⁅w, x⁆ ∈ ⁅W, N⁆ := Subgroup.commutator_mem_commutator hw hx
    have h3 := Subgroup.commutator_le.mp (le_of_eq hcomm) _ hwx _ hc'
    rw [Subgroup.mem_bot] at h3
    exact (commutatorElement_eq_one_iff_mul_comm.mp h3).symm

section Step8

variable {K : Type} [Field K] [Finite K] [CharP K 2] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}

private def tauSubOneHom (M₀ : Tim79.QuadModel Q Z K γ) (T : M₀.E ≃ₗ[K] M₀.E) :
    ↥Q →* Multiplicative M₀.E where
  toFun x := Multiplicative.ofAdd (((T : M₀.E →ₗ[K] M₀.E) - 1) (M₀.π x))
  map_one' := by simp [Tim79.QuadModel.pi_one]
  map_mul' x y := by
    rw [Subgroup.coe_mul, M₀.π_mul x x.2 y y.2, map_add]
    rfl

private theorem ker_tauSubOneHom (hc : Ctx M Q Z B) {t : G} (htM : t ∈ M)
    (R : Tim79.GammaReg Q Z γ) {T : M₀.E ≃ₗ[K] M₀.E}
    (htQ : ∀ x ∈ Q, t * x * t⁻¹ ∈ Q)
    (hTπ : ∀ x ∈ Q, M₀.π (t * x * t⁻¹) = T (M₀.π x)) :
    (tauSubOneHom M₀ T).ker = (Q1 hc t).subgroupOf Q := by
  ext x
  simp only [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, tauSubOneHom, MonoidHom.coe_mk,
    MonoidHom.coe_coe]
  rw [hc.mem_Q1_iff htM]
  constructor
  · intro h1
    have h2 : ((T : M₀.E →ₗ[K] M₀.E) - 1) (M₀.π (x : G)) = 0 := by
      simpa using congrArg Multiplicative.toAdd h1
    have hD : ((T : M₀.E →ₗ[K] M₀.E) - 1) (M₀.π (x : G)) =
        (T : M₀.E →ₗ[K] M₀.E) (M₀.π (x : G)) - M₀.π (x : G) := rfl
    exact ⟨x.2, (comm_mem_iff_fix htQ hTπ x.2).mpr (sub_eq_zero.mp (hD ▸ h2))⟩
  · rintro ⟨-, hz⟩
    have h3 : (T : M₀.E →ₗ[K] M₀.E) (M₀.π (x : G)) = M₀.π (x : G) :=
      (comm_mem_iff_fix htQ hTπ x.2).mp hz
    have h2 : ((T : M₀.E →ₗ[K] M₀.E) - 1) (M₀.π (x : G)) = 0 := by
      simpa only [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] using h3
    show Multiplicative.ofAdd (((T : M₀.E →ₗ[K] M₀.E) - 1) (M₀.π (x : G))) = 1
    rw [h2]
    rfl

private theorem card_range_tauSubOneHom (R : Tim79.GammaReg Q Z γ) {T : M₀.E ≃ₗ[K] M₀.E}
    {t : G} (htQ : ∀ x ∈ Q, t * x * t⁻¹ ∈ Q) (htQ' : ∀ x ∈ Q, t⁻¹ * x * t ∈ Q)
    (hTπ : ∀ x ∈ Q, M₀.π (t * x * t⁻¹) = T (M₀.π x)) :
    Nat.card (tauSubOneHom M₀ T).range = Nat.card (M₀.img (Ut Q Z t)) := by
  refine Nat.card_congr
    { toFun := fun y => ⟨Multiplicative.toAdd y.1, ?_⟩
      invFun := fun v => ⟨Multiplicative.ofAdd v.1, ?_⟩
      left_inv := fun y => Subtype.ext rfl
      right_inv := fun v => Subtype.ext rfl }
  · obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp y.2
    have h1 : Multiplicative.toAdd y.1 =
        ((T : M₀.E →ₗ[K] M₀.E) - 1) (M₀.π (x : G)) := by
      rw [← hx]
      rfl
    rw [h1]
    exact (mem_img_comm_zpowers_sup_iff M₀ R T htQ htQ' hTπ _).mpr
      (LinearMap.mem_range.mpr ⟨M₀.π x, rfl⟩)
  · obtain ⟨e, he⟩ := LinearMap.mem_range.mp
      ((mem_img_comm_zpowers_sup_iff M₀ R T htQ htQ' hTπ v.1).mp v.2)
    obtain ⟨x, hxQ, hxe⟩ := M₀.π_surj e
    refine MonoidHom.mem_range.mpr ⟨⟨x, hxQ⟩, ?_⟩
    show Multiplicative.ofAdd (((T : M₀.E →ₗ[K] M₀.E) - 1) (M₀.π x)) = Multiplicative.ofAdd v.1
    rw [hxe, he]

theorem Ctx.card_Q_eq_card_Q1_mul_img_Ut (hc : Ctx M Q Z B) {t : G} (htM : t ∈ M)
    (R : Tim79.GammaReg Q Z γ) (T : M₀.E ≃ₗ[K] M₀.E)
    (htQ : ∀ x ∈ Q, t * x * t⁻¹ ∈ Q) (htQ' : ∀ x ∈ Q, t⁻¹ * x * t ∈ Q)
    (hTπ : ∀ x ∈ Q, M₀.π (t * x * t⁻¹) = T (M₀.π x)) :
    Nat.card ↥Q = Nat.card ↥(Q1 hc t) * Nat.card (M₀.img (Ut Q Z t)) := by
  have hQ1Q : Q1 hc t ≤ Q := fun x hx => hx.1
  have hkerCard : Nat.card (tauSubOneHom M₀ T).ker = Nat.card ↥(Q1 hc t) := by
    rw [ker_tauSubOneHom hc htM R htQ hTπ]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQ1Q).toEquiv
  rw [← hkerCard, ← card_range_tauSubOneHom R htQ htQ' hTπ, ← Subgroup.index_ker,
    Subgroup.card_mul_index]

theorem Ctx.card_Q1_le (hc : Ctx M Q Z B) {t : G} (htM : t ∈ M) :
    Nat.card ↥(Q1 hc t) ≤
      Nat.card ↥(Q ⊓ Subgroup.centralizer ({t} : Set G)) * Nat.card ↥Z := by
  have hCcQ1 : Q ⊓ Subgroup.centralizer ({t} : Set G) ≤ Q1 hc t := by
    intro x hx
    refine (hc.mem_Q1_iff htM).mpr ⟨(Subgroup.mem_inf.mp hx).1, ?_⟩
    have hxt : t * x = x * t :=
      (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hx).2).symm
    have h1 : ⁅t, x⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr hxt
    rw [h1]
    exact Z.one_mem
  have hcard := Subgroup.card_mul_index (Ctx.commQ1Hom hc htM).ker
  rw [Subgroup.index_ker] at hcard
  have hkerCard : Nat.card (Ctx.commQ1Hom hc htM).ker =
      Nat.card ↥(Q ⊓ Subgroup.centralizer ({t} : Set G)) := by
    rw [Ctx.ker_commQ1Hom hc htM]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCcQ1).toEquiv
  have hrange : Nat.card (Ctx.commQ1Hom hc htM).range ≤ Nat.card ↥Z :=
    Nat.card_le_card_of_injective (fun x : ↥(Ctx.commQ1Hom hc htM).range => (x.1 : ↥Z))
      (fun a b h => Subtype.ext h)
  calc Nat.card ↥(Q1 hc t) = Nat.card (Ctx.commQ1Hom hc htM).ker *
        Nat.card (Ctx.commQ1Hom hc htM).range := hcard.symm
    _ ≤ Nat.card ↥(Q ⊓ Subgroup.centralizer ({t} : Set G)) * Nat.card ↥Z :=
        Nat.mul_le_mul (le_of_eq hkerCard) hrange

private theorem card_le_mul_of_bounds {s c q q1 w z : ℕ} (hc : 0 < c)
    (h1 : s * c ≤ q * z) (h2 : q = q1 * w) (h3 : q1 ≤ c * z) : s ≤ z * (z * w) := by
  have hkey : s * c ≤ c * (z * (z * w)) := by
    calc s * c ≤ q * z := h1
      _ = q1 * w * z := by rw [h2]
      _ ≤ (c * z) * w * z := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ h3)
      _ = c * (z * (z * w)) := by ring
  rw [mul_comm s c] at hkey
  exact Nat.le_of_mul_le_mul_left hkey hc

private theorem card_img_le_of_bounds {a w s sz q u : ℕ} (hq : 0 < q) (hw : 0 < w)
    (hD : a * w ≤ s) (hcardS : sz = q * s) (hSU : sz ≤ q * u) (hcardU : u = q * w) :
    a ≤ q := by
  have h1 : s ≤ q * w := by
    refine Nat.le_of_mul_le_mul_left ?_ hq
    calc q * s = sz := hcardS.symm
      _ ≤ q * u := hSU
      _ = q * (q * w) := by rw [hcardU]
  exact Nat.le_of_mul_le_mul_right (hD.trans h1) hw

theorem card_Wt_centralizer_le (hc : Ctx M Q Z B) {t : G} (ht : t ∈ LB M Q B) :
    Nat.card ↥(Wt Q (Q ⊓ Subgroup.centralizer ({t} : Set G))) ≤
      Nat.card Z * Nat.card ↥(Ut Q Z t) := by
  set Cc : Subgroup G := Q ⊓ Subgroup.centralizer ({t} : Set G)
  obtain ⟨K, hK, hfin, hch, γ, M₀, hD⟩ := stroth_globalModelData hc.hyp
  haveI := hfin
  obtain ⟨φ, hφπ, -, -⟩ := exists_actionHom_H0 hc.hyp hD
  let τ := φ ⟨t, hc.LB_le_H0 ht⟩
  have htM : t ∈ M := hc.LB_le_M ht
  obtain ⟨htQ, htQ'⟩ := hc.conj_mem_Q_of_mem_M htM
  have hTπ : ∀ x ∈ Q, M₀.π (t * x * t⁻¹) = τ (M₀.π x) :=
    fun x hx => hφπ ⟨t, hc.LB_le_H0 ht⟩ x hx
  have hcardQ := hc.card_Q_eq_card_Q1_mul_img_Ut htM hD.reg τ htQ htQ' hTπ
  have hcardQ1 := hc.card_Q1_le htM
  have hcardU : Nat.card ↥(Ut Q Z t) = Nat.card Z * Nat.card (M₀.img (Ut Q Z t)) :=
    M₀.card_eq (hc.Ut_le_Q htM) le_sup_right
  have hZC : Z ≤ Cc := by
    intro z hz
    refine Subgroup.mem_inf.mpr ⟨hc.Z_le_Q hz, ?_⟩
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    have h1 := hc.LB_centralizes_Z ht z hz
    calc z * t = (t * z * t⁻¹) * t := by rw [h1]
      _ = t * z := by group
  have hSU' : Nat.card ↥(Wt Q Cc) ≤
      Nat.card Z * (Nat.card Z * Nat.card (M₀.img (Ut Q Z t))) :=
    card_le_mul_of_bounds Nat.card_pos
      (StrothHyp.card_Wt_mul_card_le hc.hyp (X := Cc) inf_le_left hZC) hcardQ hcardQ1
  rwa [← hcardU] at hSU'

theorem Ut_le_Wt_centralizer (hc : Ctx M Q Z B) {t : G} (ht : t ∈ LB M Q B) :
    Ut Q Z t ≤ Wt Q (Q ⊓ Subgroup.centralizer ({t} : Set G)) := by
  set Cc : Subgroup G := Q ⊓ Subgroup.centralizer ({t} : Set G)
  have hCQ : Cc ≤ Q := inf_le_left
  have htc : ⁅Subgroup.zpowers t, Cc⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro u hu
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    refine Subgroup.mem_centralizer_iff.mpr fun c hcv => ?_
    have hct : c * t = t * c :=
      Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hcv).2
    exact (Commute.zpow_right (show Commute c t from hct) k).eq
  have hCQZ : ⁅Cc, Q⁆ ≤ Z :=
    Subgroup.commutator_le.mpr fun c hcv q hq => comm_mem_Z hc.hyp (hCQ hcv) hq
  have hZt : ⁅Z, Subgroup.zpowers t⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro z hz
    refine Subgroup.mem_centralizer_iff.mpr fun u hu => ?_
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    have hzt : t * z * t⁻¹ = z := hc.LB_centralizes_Z ht z hz
    have hcomm : Commute t z := by
      show t * z = z * t
      calc t * z = (t * z * t⁻¹) * t := by group
        _ = z * t := by rw [hzt]
    exact (hcomm.zpow_left k).eq
  have h1 : ⁅⁅Subgroup.zpowers t, Cc⁆, Q⁆ = ⊥ := by rw [htc]; simp
  have h2 : ⁅⁅Cc, Q⁆, Subgroup.zpowers t⁆ = ⊥ := by
    rw [eq_bot_iff]
    exact (Subgroup.commutator_mono hCQZ le_rfl).trans (le_of_eq hZt)
  have hQtC : ⁅⁅Q, Subgroup.zpowers t⁆, Cc⁆ = ⊥ :=
    Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2
  show Ut Q Z t ≤ Wt Q Cc
  refine le_inf (hc.Ut_le_Q (hc.LB_le_M ht)) (sup_le ?_ ?_)
  · exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hQtC
  · intro z hz
    exact Subgroup.mem_centralizer_iff.mpr fun c hcv =>
      (Z_central hc.hyp hz (hCQ hcv)).symm

private theorem comp_self_eq_id {T : M₀.E ≃ₗ[K] M₀.E} (hT2 : T ^ 2 = 1) :
    (T : M₀.E →ₗ[K] M₀.E) ∘ₗ (T : M₀.E →ₗ[K] M₀.E) = LinearMap.id := by
  ext x
  have h := congrArg (fun g : M₀.E ≃ₗ[K] M₀.E => g x) hT2
  simpa [pow_two, LinearMap.comp_apply] using h

private theorem card_range_tauSubOne (hc : Ctx M Q Z B) {t : G} (ht : t ∈ LB M Q B)
    (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (m : H0 M Z) (x : G), x ∈ Q → M₀.π ((m : G) * x * (m : G)⁻¹) = φ m (M₀.π x))
    (hT2 : φ ⟨t, hc.LB_le_H0 ht⟩ ^ 2 = 1)
    (f : ↥(M₀.img (Wt Q (Q ⊓ Subgroup.centralizer ({t} : Set G)))) →+ M₀.E)
    (hf : ∀ v, f v =
      ((φ ⟨t, hc.LB_le_H0 ht⟩ : M₀.E →ₗ[K] M₀.E) - 1) v.1) :
    Nat.card f.range = Nat.card (M₀.img (Tt Q Z (Q ⊓ Subgroup.centralizer ({t} : Set G)) t)) := by
  let Cc : Subgroup G := Q ⊓ Subgroup.centralizer ({t} : Set G)
  let D : Subgroup G := Tt Q Z Cc t
  have hset : ∀ e : M₀.E, e ∈ f.range ↔ e ∈ M₀.img D := by
    intro e
    rw [AddMonoidHom.mem_range]
    constructor
    · rintro ⟨v, rfl⟩
      rw [hf]
      exact (StrothHyp.mem_img_Tt_iff hc.hyp φ hφπ Cc ⟨t, hc.LB_le_H0 ht⟩ hT2).mpr
        ⟨v.1, v.2, rfl⟩
    · intro he
      obtain ⟨w, hw, hwe⟩ :=
        (StrothHyp.mem_img_Tt_iff hc.hyp φ hφπ Cc ⟨t, hc.LB_le_H0 ht⟩ hT2).mp he
      exact ⟨⟨w, hw⟩, by rw [hf]; exact hwe⟩
  exact Nat.card_congr
    { toFun := fun y => ⟨y.1, (hset y.1).mp y.2⟩
      invFun := fun v => ⟨v.1, (hset v.1).mpr v.2⟩
      left_inv := fun y => Subtype.ext rfl
      right_inv := fun v => Subtype.ext rfl }

private theorem card_img_Tt_mul_card_img_Ut_le (hc : Ctx M Q Z B) {t : G}
    (ht : t ∈ LB M Q B) (R : Tim79.GammaReg Q Z γ)
    (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (m : H0 M Z) (x : G), x ∈ Q → M₀.π ((m : G) * x * (m : G)⁻¹) = φ m (M₀.π x))
    (hT2 : φ ⟨t, hc.LB_le_H0 ht⟩ ^ 2 = 1)
    (hUS : Ut Q Z t ≤ Wt Q (Q ⊓ Subgroup.centralizer ({t} : Set G))) :
    Nat.card (M₀.img (Tt Q Z (Q ⊓ Subgroup.centralizer ({t} : Set G)) t)) *
        Nat.card (M₀.img (Ut Q Z t)) ≤
      Nat.card (M₀.img (Wt Q (Q ⊓ Subgroup.centralizer ({t} : Set G)))) := by
  let Cc : Subgroup G := Q ⊓ Subgroup.centralizer ({t} : Set G)
  let S : Subgroup G := Wt Q Cc
  let D : Subgroup G := Tt Q Z Cc t
  let τ : M₀.E ≃ₗ[K] M₀.E := φ ⟨t, hc.LB_le_H0 ht⟩
  haveI : Finite M₀.E := Module.finite_of_finite K
  haveI : Finite ↥(M₀.img S) := Finite.of_injective (Subtype.val) Subtype.val_injective
  haveI : Finite ↥(M₀.img (Ut Q Z t)) :=
    Finite.of_injective (Subtype.val) Subtype.val_injective
  let f : ↥(M₀.img S) →+ M₀.E :=
    { toFun := fun v => ((τ : M₀.E →ₗ[K] M₀.E) - 1) v.1
      map_zero' := map_zero _
      map_add' := fun a b => map_add _ a.1 b.1 }
  have hf : ∀ v : ↥(M₀.img S), f v = ((τ : M₀.E →ₗ[K] M₀.E) - 1) v.1 := fun v => rfl
  have hfrange := card_range_tauSubOne hc ht φ hφπ hT2 f hf
  have htM : t ∈ M := hc.LB_le_M ht
  obtain ⟨htQ, htQ'⟩ := hc.conj_mem_Q_of_mem_M htM
  have hTπ : ∀ x ∈ Q, M₀.π (t * x * t⁻¹) = τ (M₀.π x) :=
    fun x hx => hφπ ⟨t, hc.LB_le_H0 ht⟩ x hx
  have hcardKer : Nat.card (M₀.img (Ut Q Z t)) ≤ Nat.card ↥f.ker := by
    refine Nat.card_le_card_of_injective
      (fun v : ↥(M₀.img (Ut Q Z t)) =>
        (⟨⟨v.1, M₀.img_mono hUS v.2⟩, ?_⟩ : ↥f.ker)) ?_
    · obtain ⟨e, he⟩ := LinearMap.mem_range.mp
        ((mem_img_comm_zpowers_sup_iff M₀ R τ htQ htQ' hTπ v.1).mp v.2)
      rw [AddMonoidHom.mem_ker, hf]
      show ((τ : M₀.E →ₗ[K] M₀.E) - 1) v.1 = 0
      rw [← he]
      exact LinearMap.mem_ker.mp
        (Tim79.QuadModel.range_le_ker_of_sq_eq_one M₀ (comp_self_eq_id hT2) ⟨e, rfl⟩)
    · intro a b h
      exact Subtype.ext (congrArg (fun z : ↥f.ker => (z.1.1 : M₀.E)) h)
  calc Nat.card (M₀.img D) * Nat.card (M₀.img (Ut Q Z t))
      = Nat.card f.range * Nat.card (M₀.img (Ut Q Z t)) := by rw [hfrange]
    _ = Nat.card (M₀.img (Ut Q Z t)) * Nat.card f.range := by ring
    _ ≤ Nat.card ↥f.ker * Nat.card f.range := Nat.mul_le_mul_right _ hcardKer
    _ = Nat.card ↥(M₀.img S) := by
        rw [← AddSubgroup.card_mul_index f.ker, AddSubgroup.index_ker]

theorem Ctx.card_Tt_centralizer_le (hc : Ctx M Q Z B) {t : G} (ht : t ∈ LB M Q B) :
    Nat.card ↥(Tt Q Z (Q ⊓ Subgroup.centralizer ({t} : Set G)) t) ≤ Nat.card Z ^ 2 := by
  set Cc : Subgroup G := Q ⊓ Subgroup.centralizer ({t} : Set G)
  set S : Subgroup G := Wt Q Cc
  set D : Subgroup G := Tt Q Z Cc t
  obtain ⟨K, hK, hfin, hch, γ, M₀, hD⟩ := stroth_globalModelData hc.hyp
  haveI := hfin
  haveI : Finite M₀.E := Module.finite_of_finite K
  obtain ⟨φ, hφπ, hφQ, -⟩ := exists_actionHom_H0 hc.hyp hD
  have htM : t ∈ M := hc.LB_le_M ht
  have hSU : Nat.card ↥S ≤ Nat.card Z * Nat.card ↥(Ut Q Z t) := card_Wt_centralizer_le hc ht
  have hUS : Ut Q Z t ≤ S := Ut_le_Wt_centralizer hc ht
  have hcardU : Nat.card ↥(Ut Q Z t) = Nat.card Z * Nat.card (M₀.img (Ut Q Z t)) :=
    M₀.card_eq (hc.Ut_le_Q htM) le_sup_right
  have hZS : Z ≤ S := by
    intro z hz
    refine Subgroup.mem_inf.mpr ⟨hc.Z_le_Q hz, ?_⟩
    exact Subgroup.mem_centralizer_iff.mpr fun x hx =>
      (Z_central hc.hyp hz (Subgroup.mem_inf.mp hx).1).symm
  have hcardS : Nat.card ↥S = Nat.card Z * Nat.card (M₀.img S) := M₀.card_eq inf_le_left hZS
  have hDstep := card_img_Tt_mul_card_img_Ut_le hc ht hD.reg φ hφπ
    (hc.actionHom_sq_eq_one φ hφQ ht) hUS
  have hDimg : Nat.card (M₀.img D) ≤ Nat.card Z :=
    card_img_le_of_bounds Nat.card_pos Nat.card_pos hDstep hcardS hSU hcardU
  calc Nat.card ↥D = Nat.card Z * Nat.card (M₀.img D) :=
        M₀.card_eq (Tt_le_Q hc.Z_le_Q (hc.hyp.Q_normal.2 htM)) le_sup_right
    _ ≤ Nat.card Z * Nat.card Z := Nat.mul_le_mul_left _ hDimg
    _ = Nat.card Z ^ 2 := by ring

private theorem sub_one_sub_comm {T S : M₀.E →ₗ[K] M₀.E} (hcomm : ∀ e, T (S e) = S (T e))
    (u : M₀.E) : (T - 1) u - S ((T - 1) u) = (T - 1) (u - S u) := by
  have h1 : (T - 1) u = T u - u := rfl
  have h2 : (T - 1) (u - S u) = (T u - T (S u)) - (u - S u) := by
    rw [map_sub, h1, show (T - 1) (S u) = T (S u) - S u from rfl]
    simp only [sub_eq_add_neg, neg_add_rev, neg_neg]
    abel
  rw [h1, h2, map_sub, show S (T u) = T (S u) from (hcomm u).symm]
  simp only [sub_eq_add_neg, neg_add_rev, neg_neg]
  abel

private theorem pi_commutator_eq {t y : G} {φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)}
    (hφπ : ∀ (m : H0 M Z) (x : G), x ∈ Q → M₀.π ((m : G) * x * (m : G)⁻¹) = φ m (M₀.π x))
    {x w : G} {u : M₀.E} (htH : t ∈ H0 M Z) (hyH : y ∈ H0 M Z)
    (hyQ : ∀ z ∈ Q, y * z * y⁻¹ ∈ Q) (hxQ : x ∈ Q) (hwQ : w ∈ Q)
    (hux : ((φ ⟨t, htH⟩ : M₀.E →ₗ[K] M₀.E) - 1) u = M₀.π x) (hwu : M₀.π w = u)
    (hcomm : ∀ e, φ ⟨t, htH⟩ (φ ⟨y, hyH⟩ e) = φ ⟨y, hyH⟩ (φ ⟨t, htH⟩ e)) :
    M₀.π ⁅x, y⁆ = ((φ ⟨t, htH⟩ : M₀.E →ₗ[K] M₀.E) - 1) (M₀.π ⁅w, y⁆) := by
  have hTπy : ∀ z ∈ Q, M₀.π (y * z * y⁻¹) = φ ⟨y, hyH⟩ (M₀.π z) :=
    fun z hz => hφπ ⟨y, hyH⟩ z hz
  have e1 : M₀.π ⁅x, y⁆ = M₀.π x - φ ⟨y, hyH⟩ (M₀.π x) :=
    pi_comm_eq_sub (t := y) (T := φ ⟨y, hyH⟩) hyQ hTπy hxQ
  have e2 : M₀.π ⁅w, y⁆ = M₀.π w - φ ⟨y, hyH⟩ (M₀.π w) :=
    pi_comm_eq_sub (t := y) (T := φ ⟨y, hyH⟩) hyQ hTπy hwQ
  rw [e1, e2, ← hux, hwu]
  exact sub_one_sub_comm hcomm u

private theorem comm_Tt_CN_le_Tt (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (hspread : StrothNoA2SpreadStatement) {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n)
    {t : G} (ht : Good103 M Q Z B t) {Y : Subgroup G} (hs : Sit M Q Z Y t) :
    ⁅Tt Q Z (Vt M (LB M Q B) B Z t) t, hc.CN t⁆ ≤
      Tt Q Z (Q ⊓ Subgroup.centralizer ({t} : Set G)) t := by
  let Cc : Subgroup G := Q ⊓ Subgroup.centralizer ({t} : Set G)
  let D : Subgroup G := Tt Q Z Cc t
  obtain ⟨K, hK, hfin, hch, γ, M₀, hD⟩ := stroth_globalModelData hc.hyp
  haveI := hfin
  obtain ⟨φ, hφπ, hφQ, -⟩ := exists_actionHom_H0 hc.hyp hD
  let tH : ↥(H0 M Z) := ⟨t, hc.LB_le_H0 ht.1.mem_LB⟩
  have hT2 : φ tH ^ 2 = 1 := hc.actionHom_sq_eq_one φ hφQ ht.1.mem_LB
  refine Subgroup.commutator_le.mpr fun x hxT y hyN => ?_
  have hyR : y ∈ Rt M (LB M Q B) t := (Ctx.mem_CN.mp hyN).1
  have hyH0 : y ∈ H0 M Z := hc.Rt_le_H0 t hyR
  have hyM : y ∈ M := (Subgroup.mem_inf.mp hyH0).1
  let yH : ↥(H0 M Z) := ⟨y, hyH0⟩
  have hyQ : ∀ z ∈ Q, y * z * y⁻¹ ∈ Q := (hc.conj_mem_Q_of_mem_M hyM).1
  have hxQ : x ∈ Q := Tt_le_Q hc.Z_le_Q (hc.hyp.Q_normal.2 (hc.LB_le_M ht.1.mem_LB)) hxT
  have hxyQ : ⁅x, y⁆ ∈ Q := hc.comm_mem_Q (t := y) hyM hxQ
  obtain ⟨u, huS, hux⟩ := (StrothHyp.mem_img_Tt_iff hc.hyp φ hφπ
    (Vt M (LB M Q B) B Z t) tH hT2).mp (M₀.pi_mem_img hxT hxQ)
  obtain ⟨w, hwW, hwQ, hwu⟩ := M₀.mem_img.mp huS
  have hwy : ⁅w, y⁆ ∈ Wt Q Cc :=
    Sec10Hyp.comm_Wt_CN_le_Wt h34 h311a hspread H ht hs hwW hyN
  have hwyQ : ⁅w, y⁆ ∈ Q := (Subgroup.mem_inf.mp hwy).1
  have hcomm : ∀ e, φ tH (φ yH e) = φ yH (φ tH e) := fun e =>
    StrothHyp.comm_action hc.hyp (hc.LB_le_M ht.1.mem_LB) hyM (by
      rw [show ⁅t, y⁆ = (⁅y, t⁆)⁻¹ by rw [← commutatorElement_inv t y, inv_inv]]
      exact Q.inv_mem (hc.Rt_comm_mem_Q hyR))
      (fun z hz => hφπ tH z hz) (fun z hz => hφπ yH z hz) e
  have hmem : M₀.π ⁅x, y⁆ ∈ M₀.img D := by
    rw [pi_commutator_eq hφπ (hc.LB_le_H0 ht.1.mem_LB) hyH0 hyQ hxQ hwQ hux hwu hcomm]
    exact (StrothHyp.mem_img_Tt_iff hc.hyp φ hφπ Cc tH hT2).mpr
      ⟨M₀.π ⁅w, y⁆, M₀.pi_mem_img hwy hwyQ, rfl⟩
  exact (M₀.mem_img_iff (le_sup_right : Z ≤ D) hxyQ).mp hmem

private theorem Rt_normalizes_Tt (hc : Ctx M Q Z B) {t : G} (ht : Good103 M Q Z B t) :
    Rt M (LB M Q B) t ≤
      Subgroup.normalizer (Tt Q Z (Vt M (LB M Q B) B Z t) t : Set G) := by
  let V : Subgroup G := Vt M (LB M Q B) B Z t
  let T : Subgroup G := Tt Q Z V t
  obtain ⟨K, hK, hfin, hch, γ, M₀, hD⟩ := stroth_globalModelData hc.hyp
  haveI := hfin
  obtain ⟨φ, hφπ, hφQ, hφiso⟩ := exists_actionHom_H0 hc.hyp hD
  let tH : ↥(H0 M Z) := ⟨t, hc.LB_le_H0 ht.1.mem_LB⟩
  have hT2 : φ tH ^ 2 = 1 := hc.actionHom_sq_eq_one φ hφQ ht.1.mem_LB
  have hTQ : T ≤ Q := Tt_le_Q hc.Z_le_Q (hc.hyp.Q_normal.2 (hc.LB_le_M ht.1.mem_LB))
  have hZT : Z ≤ T := le_sup_right
  have hle : ∀ s ∈ Rt M (LB M Q B) t, conjSubgroup s T ≤ T := by
    intro s hs
    have hsM : s ∈ M := hc.Rt_le_M t hs
    have hsH0 : s ∈ H0 M Z := hc.Rt_le_H0 t hs
    rintro - ⟨x, hxT, rfl⟩
    have hxQ : x ∈ Q := hTQ hxT
    have hsxQ : s * x * s⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hsM) x).mp hxQ
    refine (M₀.mem_img_iff hZT hsxQ).mp ?_
    rw [hφπ ⟨s, hsH0⟩ x hxQ]
    exact StrothHyp.mem_img_Tt_of_comm hc.hyp φ hφπ tH hT2 hsM
      (hc.Rt_normalizes_Vt ht.1.mem_LB hs) (hc.Rt_comm_mem_Q hs)
      (φ ⟨s, hsH0⟩) (fun z hz => hφπ ⟨s, hsH0⟩ z hz)
      ((M₀.mem_img_iff hZT hxQ).mpr hxT)
  intro r hr
  refine conjSubgroup_eq_self_iff.mp ?_
  show conjSubgroup r T = T
  refine le_antisymm (hle r hr) ?_
  calc T = conjSubgroup r (conjSubgroup r⁻¹ T) := by
        rw [← conjSubgroup_mul, mul_inv_cancel, conjSubgroup_one]
    _ ≤ conjSubgroup r T := Subgroup.map_mono (hle r⁻¹ ((Rt M (LB M Q B) t).inv_mem hr))

private theorem Rt_le_normalizer_commutator (hc : Ctx M Q Z B) {t : G}
    (ht : Good103 M Q Z B t) :
    Rt M (LB M Q B) t ≤ Subgroup.normalizer
      ((⁅Tt Q Z (Vt M (LB M Q B) B Z t) t, hc.CN t⁆ ⊔ Z : Subgroup G) : Set G) := by
  let V : Subgroup G := Vt M (LB M Q B) B Z t
  let T : Subgroup G := Tt Q Z V t
  let N : Subgroup G := hc.CN t
  intro r hr
  have h1 : r ∈ Subgroup.normalizer (T : Set G) := Rt_normalizes_Tt hc ht hr
  have h2 : r ∈ Subgroup.normalizer (N : Set G) :=
    Subgroup.mem_normalizer_fintype fun x hx => Ctx.CN_conj_mem hc ht.1.mem_LB hr hx
  refine conjSubgroup_eq_self_iff.mp ?_
  show conjSubgroup r (⁅T, N⁆ ⊔ Z) = ⁅T, N⁆ ⊔ Z
  rw [conjSubgroup_sup', hc.conj_Z_eq (hc.Rt_le_M t hr)]
  have e : conjSubgroup r ⁅T, N⁆ = ⁅T, N⁆ := by
    have hmap : conjSubgroup r ⁅T, N⁆ = ⁅conjSubgroup r T, conjSubgroup r N⁆ :=
      Subgroup.map_commutator (H₁ := T) (H₂ := N) (f := (MulAut.conj r).toMonoidHom)
    rw [hmap, conjSubgroup_eq_self_iff.mpr h1, conjSubgroup_eq_self_iff.mpr h2]
  rw [e]

theorem Sec10Hyp.comm_Tt_CN_le_Z (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (hspread : StrothNoA2SpreadStatement) {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n)
    {t : G} (ht : Good103 M Q Z B t) {Y : Subgroup G} (hs : Sit M Q Z Y t) :
    ⁅Tt Q Z (Vt M (LB M Q B) B Z t) t, hc.CN t⁆ ≤ Z := by
  let V : Subgroup G := Vt M (LB M Q B) B Z t
  let T : Subgroup G := Tt Q Z V t
  let N : Subgroup G := hc.CN t
  let D : Subgroup G := Tt Q Z (Q ⊓ Subgroup.centralizer ({t} : Set G)) t
  let X : Subgroup G := ⁅T, N⁆ ⊔ Z
  have hTD : ⁅T, N⁆ ≤ D := comm_Tt_CN_le_Tt h34 h311a hspread H ht hs
  have hDcard : Nat.card ↥D ≤ Nat.card Z ^ 2 := Ctx.card_Tt_centralizer_le hc ht.1.mem_LB
  have hXD : X ≤ D := sup_le hTD le_sup_right
  have hTV : ⁅T, N⁆ ≤ V := by
    refine Subgroup.commutator_le.mpr fun x hxT y hyN => ?_
    have hyR : y ∈ Rt M (LB M Q B) t := (Ctx.mem_CN.mp hyN).1
    have h1 := hc.comm_Rt_Tt_le_Vt ht.1.mem_LB y hyR x hxT
    rw [show ⁅x, y⁆ = (⁅y, x⁆)⁻¹ by rw [← commutatorElement_inv x y, inv_inv]]
    exact V.inv_mem h1
  have hXV : X ≤ V := sup_le hTV sec39_Z_le_Vt
  have hZX : Z ≤ X := le_sup_right
  obtain ⟨m, hm2, hsl⟩ := SLlike.exists_SLMNat (H.slLike ht.1)
  have hVcard : Nat.card V = Nat.card Z ^ (m + 1) := SLMNat.card_Vt hsl
  rcases SLMNat.eq_or_eq_of_le_normalizer hsl hm2 hZX hXV
    (Rt_le_normalizer_commutator hc ht) with hXZ | hXVe
  · have h : ⁅T, N⁆ ≤ Z := by
      rw [← hXZ]
      exact le_sup_left
    exact h
  · exfalso
    have h1 : Nat.card ↥X ≤ Nat.card ↥D :=
      Nat.card_le_card_of_injective (Subgroup.inclusion hXD) (Subgroup.inclusion_injective _)
    have h1' : Nat.card ↥V ≤ Nat.card ↥D := by
      rw [show V = X from hXVe.symm]
      exact h1
    have h2 : Nat.card Z ^ 2 < Nat.card Z ^ (m + 1) := by
      have hq : 1 < Nat.card Z := by have := hc.hyp.q4; omega
      calc Nat.card Z ^ 2 < Nat.card Z ^ 3 := Nat.pow_lt_pow_right hq (by norm_num)
        _ ≤ Nat.card Z ^ (m + 1) := Nat.pow_le_pow_right (by omega) (by omega)
    omega

end Step8

theorem Sec10Hyp.Tt_le_Vt (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (hspread : StrothNoA2SpreadStatement) {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n)
    {t : G} (ht : Good103 M Q Z B t) :
    Tt Q Z (Vt M (LB M Q B) B Z t) t ≤ Vt M (LB M Q B) B Z t := by
  obtain ⟨Y, hs⟩ := ht.1.exists_sit hc
  let A : Subgroup G := Q ⊓ QB B
  let P : Subgroup G := QB B ⊓ QB Y ⊓ M
  have hA : Tt Q Z (Vt M (LB M Q B) B Z t) t ≤ A := Ctx.Tt_le_inf_QB hc ht.1
  intro x hxT
  have hxA : x ∈ A := hA hxT
  have hxP : x ∈ Subgroup.centralizer (P : Set G) := by
    refine Subgroup.mem_centralizer_iff.mpr fun p hp => ?_
    have hpN : p ∈ hc.CN t := Ctx.inf_QB_le_CN hc ht hs hp
    have hxQ : x ∈ Q := hxA.1
    have hxN : x ∈ Tt Q Z (Vt M (LB M Q B) B Z t) t := hxT
    have hcZ : ⁅x, p⁆ ∈ Z :=
      Subgroup.commutator_le.mp (Sec10Hyp.comm_Tt_CN_le_Z h34 h311a hspread H ht hs) x hxN p hpN
    have hcB : ⁅x, p⁆ ∈ B :=
      hc.comm_QB_le_B hxA.2 (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hp).1).1
    have hzero : ⁅x, p⁆ = 1 := by
      have hmem : ⁅x, p⁆ ∈ Z ⊓ B := ⟨hcZ, hcB⟩
      rwa [hc.inf_eq_bot, Subgroup.mem_bot] at hmem
    exact (commutatorElement_eq_one_iff_mul_comm.mp hzero).symm
  exact Sec10Hyp.inf_centralizer_le_Vt h34 hspread H ht hs ⟨hxA, hxP⟩

theorem stroth_10_5 (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (hspread : StrothNoA2SpreadStatement) :
    ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
      Sec10Hyp hc n → Good103 M Q Z B t →
        Vt M (LB M Q B) B Z t = Tt Q Z (Vt M (LB M Q B) B Z t) t := by
  intro G _ _ M Q Z B hc n t H ht
  have h35 : CQt Q Z (LB M Q B) = ((B ⊔ Z : Subgroup G) : Set G) :=
    (stroth_3_5 h34 hc H.width H.n_gt H.noA2 H.gen).2.1
  obtain ⟨m, hm, hsl⟩ := SLlike.exists_SLMNat (H.slLike ht.1)
  exact le_antisymm
    (hc.Vt_le_Tt_of_SLNat (H.toSec5 ht.1.mem_LB ht.1.2.2.1) h35 (SLMNat.toSLNat hsl hm))
    (Sec10Hyp.Tt_le_Vt h34 h311a hspread H ht)

end CFSG.RankThree.GF2n.Stroth80
