module

public import CFSG.RankThree.GF2n.Stroth80.Sec10Two
public import CFSG.RankThree.GF2n.Stroth80.Sec311Stmt
public import CFSG.RankThree.GF2n.Stroth80.Sec310SLTransv
public import CFSG.RankThree.GF2n.Stroth80.Sec57
public import CFSG.RankThree.GF2n.Stroth80.Sec83Count
public import CFSG.RankThree.GF2n.Stroth80.Sec12Cases

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n.Smith81
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem inf_QB_zpowers_eq {Y : Subgroup G} {t : G} (hs : Sit M Q Z Y t) :
    Q ⊓ QB (Subgroup.zpowers t) = Q ⊓ QB Y := by
  refine le_antisymm ?_ (inf_le_inf_left _ (QB_le_QB_zpowers hs))
  intro x hx
  obtain ⟨hxQ, hxt⟩ := Subgroup.mem_inf.mp hx
  have hxN : x ∈ Subgroup.normalizer (Y : Set G) :=
    normalizer_zpowers_le_Y hs (QB_zpowers_le_normalizer hxt)
  have hxM : x ∈ M := hs.hyp.Q_normal.1 hxQ
  refine Subgroup.mem_inf.mpr ⟨hxQ, key_Y hs hxt hxN (fun y hy => ?_)⟩
  have hcommY : ⁅y, x⁆ ∈ Y := by
    have h1 : x * y⁻¹ * x⁻¹ ∈ Y :=
      (Subgroup.mem_normalizer_iff.mp hxN y⁻¹).mp (Y.inv_mem hy)
    have h2 : ⁅x, y⁻¹⁆ ∈ Y := by
      rw [commutatorElement_def]
      exact Y.mul_mem h1 (by simpa using hy)
    have e : ⁅y, x⁆ = y * ⁅x, y⁻¹⁆ * y⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact Y.mul_mem (Y.mul_mem hy h2) (Y.inv_mem hy)
  have hcommQ : ⁅y, x⁆ ∈ Q := by
    have hyM : y ∈ M := (Subgroup.mem_inf.mp ((smith_1_12 hs).1 hy)).1
    have h2 : y * x * y⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp (hs.hyp.Q_normal.2 hyM) x).mp hxQ
    rw [commutatorElement_def]
    exact Q.mul_mem h2 (Q.inv_mem hxQ)
  have h1 : ⁅y, x⁆ ∈ Y ⊓ Q := ⟨hcommY, hcommQ⟩
  rw [hs.X_inf_Q, Subgroup.mem_bot] at h1
  exact (commutatorElement_eq_one_iff_mul_comm.mp h1).symm

theorem Good103.Vt_eq {t : G} (ht : Good103 M Q Z B t) {Y : Subgroup G}
    (hs : Sit M Q Z Y t) :
    Vt M (LB M Q B) B Z t = (Q ⊓ QB Y) ⊔ Z := by
  rw [ht.2, inf_QB_zpowers_eq hs]

theorem Ctx.Rt_inf_le_CN (hc : Ctx M Q Z B) {t : G} {Y : Subgroup G} (hs : Sit M Q Z Y t)
    (hV : Vt M (LB M Q B) B Z t = (Q ⊓ QB Y) ⊔ Z) :
    Rt M (LB M Q B) t ⊓ (QB Y ⊓ M) ≤ hc.CN t := by
  rintro y ⟨hyR, hyQB, hyM⟩
  refine Ctx.mem_CN.mpr ⟨hyR, fun v hv => ?_⟩
  rw [hV] at hv
  have hnorm : Q ⊓ QB Y ≤ Subgroup.normalizer (Z : Set G) :=
    fun x hx => hc.hyp.Z_normal.2 (hc.hyp.Q_normal.1 hx.1)
  obtain ⟨a, ha, z, hz, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer hnorm hv
  obtain ⟨haQ, haQB⟩ := Subgroup.mem_inf.mp ha
  have hya : y * a = a * y := by
    have h1 : ⁅y, a⁆ = 1 := by
      have hY : ⁅y, a⁆ ∈ Y := hs.comm_QB_mem_X hyQB haQB
      have hQ : ⁅y, a⁆ ∈ Q := by
        rw [commutatorElement_def]
        exact Q.mul_mem
          ((Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hyM) a).mp haQ) (Q.inv_mem haQ)
      have hmem : ⁅y, a⁆ ∈ Y ⊓ Q := ⟨hY, hQ⟩
      rwa [hs.X_inf_Q, Subgroup.mem_bot] at hmem
    exact commutatorElement_eq_one_iff_mul_comm.mp h1
  have hwZ : ⁅y, z⁆ ∈ Z := by
    have h1 : y * z * y⁻¹ ∈ Z :=
      (Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 hyM) z).mp hz
    rw [commutatorElement_def]
    exact Z.mul_mem h1 (Z.inv_mem hz)
  have hstep : ⁅y, a * z⁆ = a * ⁅y, z⁆ * a⁻¹ := by
    rw [commutatorElement_def, commutatorElement_def]
    calc y * (a * z) * y⁻¹ * (a * z)⁻¹
        = (y * a) * z * y⁻¹ * (z⁻¹ * a⁻¹) := by group
      _ = (a * y) * z * y⁻¹ * (z⁻¹ * a⁻¹) := by rw [hya]
      _ = a * (y * z * y⁻¹ * z⁻¹) * a⁻¹ := by group
  rw [hstep, ← Z_central hc.hyp hwZ haQ, mul_assoc, mul_inv_cancel, mul_one]
  exact hwZ

theorem Ctx.card_le_card_inf_centralizer_mul {C : Subgroup G} (hC : Ctx M Q Z C)
    {A : Subgroup G} (hAQ : A ≤ Q) :
    Nat.card A ≤ Nat.card ↥(A ⊓ Subgroup.centralizer (C : Set G)) * Nat.card Z := by
  obtain ⟨K, fK, finK, hcp, γ, M₀, hgm⟩ := stroth_globalModelData hC.hyp
  obtain ⟨b, hb0, hbq, hbline, hbcent, hQcard⟩ := hC.dictB hgm
  set D : Subgroup G := Q ⊓ Subgroup.centralizer (C : Set G) with hD
  have hZD : Z ≤ D := by
    intro z hz
    refine Subgroup.mem_inf.mpr ⟨hC.Z_le_Q hz, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    exact (Z_central hC.hyp hz (hC.le hc)).symm
  have hQD : Q ≤ Subgroup.normalizer (D : Set G) := by
    intro x hx
    refine Subgroup.mem_normalizer_fintype fun d hd => ?_
    obtain ⟨hdQ, hdC⟩ := Subgroup.mem_inf.mp hd
    have hcommZ : ⁅x, d⁆ ∈ Z := hC.hyp.toHyp79.comm_mem_V hx hdQ
    have hcommD : ⁅x, d⁆ ∈ D :=
      Subgroup.mem_inf.mpr ⟨hC.Z_le_Q hcommZ, (Subgroup.mem_inf.mp (hZD hcommZ)).2⟩
    rw [show x * d * x⁻¹ = ⁅x, d⁆ * d by rw [commutatorElement_def]; group]
    exact D.mul_mem hcommD hd
  have hcard := card_sup_mul_card_inf_of_normalizer (A := D) (C := A) (hAQ.trans hQD)
  have hmain : Nat.card A * Nat.card ↥D =
      Nat.card ↥(A ⊔ D) * Nat.card ↥(A ⊓ D) := by
    rw [sup_comm, inf_comm, mul_comm (Nat.card A)]
    exact hcard.symm
  have hle : Nat.card ↥(A ⊔ D) ≤ Nat.card Q :=
    Nat.card_le_card_of_injective (Subgroup.inclusion (sup_le hAQ inf_le_left))
      (Subgroup.inclusion_injective _)
  have hfin : Nat.card A * Nat.card ↥D ≤
      (Nat.card ↥(A ⊓ D) * Nat.card Z) * Nat.card ↥D := by
    calc Nat.card A * Nat.card ↥D = Nat.card ↥(A ⊔ D) * Nat.card ↥(A ⊓ D) := hmain
      _ ≤ Nat.card Q * Nat.card ↥(A ⊓ D) := Nat.mul_le_mul hle le_rfl
      _ = Nat.card ↥D * Nat.card Z * Nat.card ↥(A ⊓ D) := by rw [hQcard]
      _ = (Nat.card ↥(A ⊓ D) * Nat.card Z) * Nat.card ↥D := by ring
  have hcancel := Nat.le_of_mul_le_mul_right hfin Nat.card_pos
  rwa [show A ⊓ D = A ⊓ Subgroup.centralizer (C : Set G) by
    rw [hD, ← inf_assoc, inf_eq_left.mpr hAQ]] at hcancel

private theorem card_QB_inf_QB_eq_pow (hspread : StrothNoA2SpreadStatement)
    {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n) {X Y : Subgroup G} (hX : Ctx M Q Z X)
    (hXY : X ≠ Y) (hXQY : X ≤ QB Y) {k g : G} (hXk : X = conjSubgroup k Z)
    (hg : Y = conjSubgroup g Z) :
    Nat.card ↥(QB X ⊓ QB Y) = Nat.card Z ^ (n + 1) := by
  have hQBX : QB X = conjSubgroup k Q := by rw [hXk, QB_conj, hc.hyp.QB_Z]
  have hYQBX : Y ≤ QB X := hc.hyp.le_QB_of_le_QB hX.conj ⟨g, hg⟩ hXY hXQY
  have hYkQ : Y ≤ conjSubgroup k Q := hYQBX.trans hQBX.le
  have hY'Q : conjSubgroup k⁻¹ Y ≤ Q := by
    have h1 : conjSubgroup k⁻¹ Y ≤ conjSubgroup k⁻¹ (conjSubgroup k Q) :=
      Subgroup.map_mono hYkQ
    rwa [← conjSubgroup_mul, inv_mul_cancel, conjSubgroup_one] at h1
  have hY'Z : conjSubgroup k⁻¹ Y ≠ Z := by
    intro h
    apply hXY
    have hYeq : Y = X := by
      calc Y = conjSubgroup k (conjSubgroup k⁻¹ Y) := by
            rw [conjSubgroup_conjSubgroup, mul_inv_cancel, conjSubgroup_one]
        _ = conjSubgroup k Z := by rw [h]
        _ = X := hXk.symm
    exact hYeq.symm
  have hcY' : Ctx M Q Z (conjSubgroup k⁻¹ Y) :=
    { hyp := hc.hyp
      conj := ⟨k⁻¹ * g, by rw [hg, ← conjSubgroup_mul]⟩
      le := hY'Q
      ne := hY'Z }
  have hn : 1 ≤ n := by have := H.n_gt; omega
  have hnoY' : NoA2 Q Z (LB M Q (conjSubgroup k⁻¹ Y)) :=
    hspread G M Q Z B hc n H.width H.n_gt H.noA2 H.gen _ hcY'
  have hQBkY' : conjSubgroup k (QB (conjSubgroup k⁻¹ Y)) = QB Y := by
    rw [QB_conj, ← conjSubgroup_mul, mul_inv_cancel, conjSubgroup_one]
  have h1 : QB X ⊓ QB Y = conjSubgroup k (Q ⊓ QB (conjSubgroup k⁻¹ Y)) := by
    rw [hQBX, ← hQBkY', conjSubgroup_inf]
  rw [h1, card_conjSubgroup]
  exact (hcY'.card_of_3_3 H.width hn hnoY' (stroth_3_3 hcY' H.width hn)).2

theorem Sec10Hyp.pow_le_card_QB_inf_QB_inf (hspread : StrothNoA2SpreadStatement)
    {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n) {X Y : Subgroup G} (hX : Ctx M Q Z X)
    (hY : ∃ g : G, Y = conjSubgroup g Z) (hXY : X ≠ Y) (hXQY : X ≤ QB Y) :
    Nat.card Z ^ n ≤ Nat.card ↥(QB X ⊓ QB Y ⊓ M) := by
  obtain ⟨k, hXk⟩ := hX.conj
  obtain ⟨g, hg⟩ := hY
  have hQBX : QB X = conjSubgroup k Q := by rw [hXk, QB_conj, hc.hyp.QB_Z]
  have hZkQ : Z ≤ conjSubgroup k Q := hX.Z_le_QB.1.trans hQBX.le
  have hZ'Q : conjSubgroup k⁻¹ Z ≤ Q := by
    have h1 : conjSubgroup k⁻¹ Z ≤ conjSubgroup k⁻¹ (conjSubgroup k Q) :=
      Subgroup.map_mono hZkQ
    rwa [← conjSubgroup_mul, inv_mul_cancel, conjSubgroup_one] at h1
  have hZ'Z : conjSubgroup k⁻¹ Z ≠ Z := by
    intro h
    apply hX.ne
    calc X = conjSubgroup k Z := hXk
      _ = conjSubgroup k (conjSubgroup k⁻¹ Z) := by rw [h]
      _ = Z := by rw [conjSubgroup_conjSubgroup, mul_inv_cancel, conjSubgroup_one]
  have hcZ' : Ctx M Q Z (conjSubgroup k⁻¹ Z) :=
    { hyp := hc.hyp
      conj := ⟨k⁻¹, rfl⟩
      le := hZ'Q
      ne := hZ'Z }
  have hcard := card_QB_inf_QB_eq_pow hspread H hX hXY hXQY hXk hg
  have hZ'k : conjSubgroup k (conjSubgroup k⁻¹ Z) = Z := by
    rw [conjSubgroup_conjSubgroup, mul_inv_cancel, conjSubgroup_one]
  have hA : QB X ⊓ QB Y ≤ conjSubgroup k Q := by
    rw [hQBX]
    exact inf_le_left
  have hstep4 := Ctx.card_le_card_inf_centralizer_mul
    (C := conjSubgroup k (conjSubgroup k⁻¹ Z)) (A := QB X ⊓ QB Y) (hcZ'.conjBy k) hA
  rw [hZ'k, card_conjSubgroup] at hstep4
  have hCG : Subgroup.centralizer (Z : Set G) ≤ M := by
    intro x hx
    rw [← hc.hyp.normalizer_Z.1]
    exact Subgroup.centralizer_le_normalizer (Z : Set G) hx
  have hsub : (QB X ⊓ QB Y) ⊓ Subgroup.centralizer (Z : Set G) ≤ QB X ⊓ QB Y ⊓ M :=
    le_inf inf_le_left (inf_le_right.trans hCG)
  have hleP : Nat.card ↥((QB X ⊓ QB Y) ⊓ Subgroup.centralizer (Z : Set G)) ≤
      Nat.card ↥(QB X ⊓ QB Y ⊓ M) :=
    Nat.card_le_card_of_injective (Subgroup.inclusion hsub) (Subgroup.inclusion_injective _)
  have hfin : Nat.card Z ^ (n + 1) ≤ Nat.card ↥(QB X ⊓ QB Y ⊓ M) * Nat.card Z := by
    rw [← hcard]
    exact hstep4.trans (Nat.mul_le_mul hleP le_rfl)
  rw [pow_succ] at hfin
  exact Nat.le_of_mul_le_mul_right hfin Nat.card_pos

theorem card_Vt_of_sectionAct {m : ℕ} {K : Type} [Field K] [Finite K] {t : G}
    {φ : ↥(Rt M (LB M Q B) t) →* GL (Fin m) K} (hK : Nat.card K = Nat.card Z)
    (h : SectionAct K (Rt M (LB M Q B) t) (Vt M (LB M Q B) B Z t) Z φ
      (fun g => (g : Matrix (Fin m) (Fin m) K))) :
    Nat.card ↥(Vt M (LB M Q B) B Z t) = Nat.card Z ^ (m + 1) := by
  obtain ⟨-, hN, ψ, -⟩ := h
  haveI := hN
  have hcardQ : Nat.card (↥(Vt M (LB M Q B) B Z t) ⧸
      Z.subgroupOf (Vt M (LB M Q B) B Z t)) = Nat.card K ^ m := by
    rw [Nat.card_congr ψ.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_fun,
      Nat.card_eq_fintype_card (α := Fin m), Fintype.card_fin]
  have hcardZ : Nat.card (Z.subgroupOf (Vt M (LB M Q B) B Z t)) = Nat.card Z :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe sec39_Z_le_Vt).toEquiv
  have h3 := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (Z.subgroupOf (Vt M (LB M Q B) B Z t))
  rw [hcardQ, hcardZ, hK] at h3
  rw [h3, pow_succ]

theorem Sec10Hyp.exists_card_Vt_card_LB_inf_CN (h34 : Stroth34Statement) {hc : Ctx M Q Z B}
    {n : ℕ} (H : Sec10Hyp hc n) {t : G} (ht : Good101 M Q Z B t) :
    ∃ m : ℕ, 2 ≤ m ∧ Nat.card ↥(Vt M (LB M Q B) B Z t) = Nat.card Z ^ (m + 1) ∧
      Nat.card ↥(LB M Q B ⊓ hc.CN t) * Nat.card Z ^ (m - 1) ≤ Nat.card ↥(LB M Q B) := by
  have h5 : Sec5Hyp hc n t := H.toSec5 ht.mem_LB ht.2.2.1
  obtain ⟨m₀, hm₀, hsl⟩ := SLlike.exists_SLMNat (H.slLike ht)
  have hSL : SLNat hc t := SLMNat.toSLNat hsl hm₀
  have hVQB : Vt M (LB M Q B) B Z t ≤ QB B :=
    stroth310SL_of_34 h34 G M Q Z B hc n t h5 hSL
  obtain ⟨K, fK, finK, hchar, hKcard, m, hm2, φ, hker, hSA, -, -, -, hcount⟩ :=
    stroth310SLTransv_of_34 h34 G M Q Z B hc n t h5 ht.2.2.2.2 hVQB
  refine ⟨m, hm2, card_Vt_of_sectionAct (t := t) (φ := φ) hKcard hSA, ?_⟩
  have hmap := card_inf_mul_card_map (le_Rt (LB M Q B) ht.mem_LB) φ hker
  rw [hKcard] at hcount
  rw [← hmap]
  exact Nat.mul_le_mul_left _ hcount

theorem Good103.card_inf_QB_eq_pow (hc : Ctx M Q Z B) {m : ℕ} {t : G}
    (ht : Good103 M Q Z B t) {Y : Subgroup G} (hs : Sit M Q Z Y t)
    (hVcard : Nat.card ↥(Vt M (LB M Q B) B Z t) = Nat.card Z ^ (m + 1)) :
    Nat.card ↥(Q ⊓ QB Y) = Nat.card Z ^ m := by
  have hZY : Z ⊓ QB Y = ⊥ := Z_inf_QB_eq_bot hs (smith_1_12 hs)
  have hnorm : Q ⊓ QB Y ≤ Subgroup.normalizer (Z : Set G) :=
    fun x hx => hs.hyp.Z_normal.2 (hs.hyp.Q_normal.1 hx.1)
  have hcard := card_sup_mul_card_inf_of_normalizer (A := Z) (C := Q ⊓ QB Y) hnorm
  have hinf : Z ⊓ (Q ⊓ QB Y) = ⊥ := by
    rw [← inf_assoc, inf_eq_left.mpr hs.hyp.Z_normal.1, hZY]
  rw [hinf, Subgroup.card_bot, mul_one] at hcard
  have hcard' : Nat.card ↥(Q ⊓ QB Y) * Nat.card Z = Nat.card ↥((Q ⊓ QB Y) ⊔ Z) := by
    rw [mul_comm, ← hcard, sup_comm]
  have h1 : Nat.card ↥(Q ⊓ QB Y) * Nat.card Z = Nat.card Z ^ (m + 1) := by
    rw [hcard', ← Good103.Vt_eq ht hs]
    exact hVcard
  rw [pow_succ] at h1
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h1

private theorem card_conj_LB_inf_CN {t r : G} {hc : Ctx M Q Z B} (ht : t ∈ LB M Q B)
    (hr : r ∈ Rt M (LB M Q B) t) :
    Nat.card ↥(conjSubgroup r (LB M Q B) ⊓ hc.CN t) =
      Nat.card ↥(LB M Q B ⊓ hc.CN t) := by
  have hrN : r ∈ Subgroup.normalizer (hc.CN t : Set G) :=
    Subgroup.mem_normalizer_fintype fun x hx => hc.CN_conj_mem ht hr hx
  have h1 : conjSubgroup r (LB M Q B) ⊓ hc.CN t =
      conjSubgroup r (LB M Q B ⊓ hc.CN t) := by
    rw [conjSubgroup_inf, conjSubgroup_eq_self_iff.mpr hrN]
  rw [h1, card_conjSubgroup]

private theorem card_inf_le_card_sup {L N Q QY P : Subgroup G} {n m : ℕ} (hn : 1 ≤ n)
    (hm : 1 ≤ m) (hLcard : Nat.card ↥L = Nat.card Q * Nat.card Z ^ (n - 1))
    (hbound : Nat.card ↥(L ⊓ N) * Nat.card Z ^ (m - 1) ≤ Nat.card ↥L)
    (hQYcard : Nat.card ↥QY = Nat.card Z ^ m) (hPcard : Nat.card Z ^ n ≤ Nat.card ↥P)
    (hPN : P ≤ Subgroup.normalizer (Q : Set G)) (hQP : Q ⊓ P ≤ QY) :
    Nat.card ↥(L ⊓ N) ≤ Nat.card ↥(Q ⊔ P) := by
  have hsupCard : Nat.card ↥(Q ⊔ P) * Nat.card ↥(Q ⊓ P) = Nat.card Q * Nat.card ↥P :=
    card_sup_mul_card_inf_of_normalizer (A := Q) (C := P) hPN
  have hQPle : Nat.card ↥(Q ⊓ P) ≤ Nat.card ↥QY :=
    Nat.card_le_card_of_injective (Subgroup.inclusion hQP) (Subgroup.inclusion_injective _)
  have hstep : Nat.card ↥(L ⊓ N) * Nat.card Z ^ m ≤
      Nat.card ↥(Q ⊔ P) * Nat.card Z ^ m := by
    calc Nat.card ↥(L ⊓ N) * Nat.card Z ^ m
        = Nat.card ↥(L ⊓ N) * Nat.card Z ^ (m - 1) * Nat.card Z := by
          rw [mul_assoc, ← pow_sub_one_mul (by omega : m ≠ 0) (Nat.card Z)]
      _ ≤ Nat.card ↥L * Nat.card Z := Nat.mul_le_mul hbound le_rfl
      _ = Nat.card Q * Nat.card Z ^ n := by
          rw [hLcard, mul_assoc, ← pow_sub_one_mul (by omega : n ≠ 0) (Nat.card Z)]
      _ ≤ Nat.card Q * Nat.card ↥P := Nat.mul_le_mul_left _ hPcard
      _ = Nat.card ↥(Q ⊔ P) * Nat.card ↥(Q ⊓ P) := hsupCard.symm
      _ ≤ Nat.card ↥(Q ⊔ P) * Nat.card Z ^ m :=
          Nat.mul_le_mul_left _ (hQPle.trans (le_of_eq hQYcard))
  exact Nat.le_of_mul_le_mul_right hstep (pow_pos Nat.card_pos m)

theorem Sec10Hyp.conj_LB_inf_CN_eq (h34 : Stroth34Statement)
    (hspread : StrothNoA2SpreadStatement) {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n)
    {t : G} (ht : Good103 M Q Z B t) {Y : Subgroup G} (hs : Sit M Q Z Y t) {r : G}
    (hr : r ∈ Rt M (LB M Q B) t) (hrY : conjSubgroup r B ≤ QB Y) :
    conjSubgroup r (LB M Q B) ⊓ hc.CN t = Q ⊔ (QB (conjSubgroup r B) ⊓ QB Y ⊓ M) := by
  obtain ⟨m, hm2, hVcard, hbound⟩ := H.exists_card_Vt_card_LB_inf_CN h34 ht.1
  have hn1 : 1 ≤ n := by have := H.n_gt; omega
  have hm1 : 1 ≤ m := by omega
  set X : Subgroup G := conjSubgroup r B with hXdef
  set P : Subgroup G := QB X ⊓ QB Y ⊓ M with hPdef
  have hrM : r ∈ M := hc.Rt_le_M t hr
  have hX : Ctx M Q Z X := hc.conj_of_mem hrM
  have hLrR : conjSubgroup r (LB M Q B) ≤ Rt M (LB M Q B) t := by
    rw [← hc.LB_conj hrM]
    exact Ctx.LB_conj_le_Rt_of_mem hc ht.1.mem_LB hr
  have htX : t ∈ conjSubgroup r (LB M Q B) := hc.mem_conjSubgroup_LB_of_mem_Rt ht.1.mem_LB hr
  have hXQ : X ≤ Q := (sec39_conjB_le_Vt hrM htX).trans (hc.Vt_le_Q t)
  have hXY : X ≠ Y := by
    intro h
    exact ht.1.2.2.1 (hXQ (h.symm ▸ hs.mem))
  have hPcard : Nat.card Z ^ n ≤ Nat.card ↥P :=
    H.pow_le_card_QB_inf_QB_inf hspread hX hs.conj hXY hrY
  have hQle : Q ≤ conjSubgroup r (LB M Q B) := by
    rw [← hc.LB_conj hrM]
    exact sec39_Q_le_LB
  have hQCN : Q ≤ hc.CN t := Ctx.Q_le_CN hc ht.1.mem_LB
  have hPleLB : P ≤ conjSubgroup r (LB M Q B) := by
    rw [← hc.LB_conj hrM]
    intro x hx
    obtain ⟨hxQBY, hxM⟩ := Subgroup.mem_inf.mp hx
    exact Subgroup.mem_sup_right ⟨(Subgroup.mem_inf.mp hxQBY).1, hxM⟩
  have hPleCN : P ≤ hc.CN t :=
    (le_inf (hPleLB.trans hLrR) (le_inf (inf_le_left.trans inf_le_right) inf_le_right)).trans
      (Ctx.Rt_inf_le_CN hc hs (Good103.Vt_eq ht hs))
  refine (Subgroup.eq_of_le_of_card_ge (sup_le (le_inf hQle hQCN) (le_inf hPleLB hPleCN)) ?_).symm
  rw [card_conj_LB_inf_CN ht.1.mem_LB hr]
  have hQYcard : Nat.card ↥(Q ⊓ QB Y) = Nat.card Z ^ m :=
    Good103.card_inf_QB_eq_pow hc ht hs hVcard
  have hLcard : Nat.card ↥(LB M Q B) = Nat.card Q * Nat.card Z ^ (n - 1) :=
    (hc.card_of_3_3 H.width hn1 H.noA2 (stroth_3_3 hc H.width hn1)).1
  have hPN : P ≤ Subgroup.normalizer (Q : Set G) :=
    fun x hx => hs.hyp.Q_normal.2 (Subgroup.mem_inf.mp hx).2
  have hQP : Q ⊓ P ≤ Q ⊓ QB Y := inf_le_inf_left Q (inf_le_left.trans inf_le_right)
  exact card_inf_le_card_sup hn1 hm1 hLcard hbound hQYcard hPcard hPN hQP

theorem Sec10Hyp.CN_le_sup (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (hspread : StrothNoA2SpreadStatement) {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n)
    {t : G} (ht : Good103 M Q Z B t) {Y : Subgroup G} (hs : Sit M Q Z Y t) :
    hc.CN t ≤ Q ⊔ (QB Y ⊓ M) := by
  rw [h311a G M Q Z B hc n H.width H.n_gt H.noA2 H.gen t ht.1.mem_LB ht.1.2.2.1
    ht.1.2.2.2.2]
  refine iSup₂_le fun h hh => ?_
  intro x hx
  obtain ⟨hxL, hxN⟩ := Subgroup.mem_inf.mp hx
  have hhM : h ∈ M := hc.Rt_le_M t hh
  have htLh : t ∈ conjSubgroup h (LB M Q B) := hc.mem_conjSubgroup_LB_of_mem_Rt ht.1.mem_LB hh
  have hle : conjSubgroup h B ≤ (Q ⊓ QB Y) ⊔ Z :=
    (sec39_conjB_le_Vt hhM htLh).trans (le_of_eq (Good103.Vt_eq ht hs))
  obtain ⟨w, hwQ, a, haX, ha1, haP⟩ :=
    Ctx.exists_conj_mem_of_le_sup (hc := hc) (m := h) (P := Q ⊓ QB Y) hhM inf_le_left hle
  have hr : w * h ∈ Rt M (LB M Q B) t :=
    (Rt M (LB M Q B) t).mul_mem (hc.Q_le_Rt ht.1.mem_LB hwQ) hh
  have hrM : w * h ∈ M := M.mul_mem (hc.hyp.Q_normal.1 hwQ) hhM
  have hX : Ctx M Q Z (conjSubgroup (w * h) B) := hc.conj_of_mem hrM
  have htQBX : t ∈ QB (conjSubgroup (w * h) B) :=
    hX.mem_QB_of_inf_QB_zpowers hs haX ha1 (QB_le_QB_zpowers hs haP.2)
  have hXQ : conjSubgroup (w * h) B ≤ Q :=
    (sec39_conjB_le_Vt hrM (hc.mem_conjSubgroup_LB_of_mem_Rt ht.1.mem_LB hr)).trans
      (hc.Vt_le_Q t)
  have hXY : conjSubgroup (w * h) B ≠ Y := by
    intro heq
    exact ht.1.2.2.1 (hXQ (heq.symm ▸ hs.mem))
  have hXQY : conjSubgroup (w * h) B ≤ QB Y :=
    hc.hyp.le_QB_of_mem_QB hX.conj hs.conj hs.mem hs.ne_one htQBX
  have h7 := H.conj_LB_inf_CN_eq h34 hspread ht hs hr hXQY
  have hwL : w ∈ conjSubgroup h (LB M Q B) := by
    have h1 : w ∈ conjSubgroup h Q := by rw [hc.conj_Q_eq hhM]; exact hwQ
    exact Subgroup.map_mono sec39_Q_le_LB h1
  have hLhL : conjSubgroup (w * h) (LB M Q B) = conjSubgroup h (LB M Q B) := by
    rw [conjSubgroup_mul, conjSubgroup_eq_self_iff.mpr (Subgroup.le_normalizer hwL)]
  have hx' : x ∈ conjSubgroup (w * h) (LB M Q B) ⊓ hc.CN t := by
    rw [hLhL]
    exact ⟨hxL, hxN⟩
  rw [h7] at hx'
  have hsub : Q ⊔ (QB (conjSubgroup (w * h) B) ⊓ QB Y ⊓ M) ≤ Q ⊔ (QB Y ⊓ M) :=
    sup_le le_sup_left ((le_inf (inf_le_left.trans inf_le_right) inf_le_right).trans le_sup_right)
  exact hsub hx'

theorem stroth_10_4 (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (hspread : StrothNoA2SpreadStatement) :
    ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G)
      (Y : Subgroup G), Sec10Hyp hc n → Good103 M Q Z B t → (∃ g : G, Y = conjSubgroup g Z) →
        t ∈ Y →
        hc.CN t ≤ Q ⊔ (QB Y ⊓ M) ∧
        ∀ r ∈ Rt M (LB M Q B) t, conjSubgroup r B ≤ QB Y →
          conjSubgroup r (LB M Q B) ⊓ hc.CN t = Q ⊔ (QB (conjSubgroup r B) ⊓ QB Y ⊓ M) := by
  intro G _ _ M Q Z B hc n t Y H ht hY htY
  have htQ : t ∉ Q := ht.1.2.2.1
  have ht1 : t ≠ 1 := fun h => htQ (by rw [h]; exact Q.one_mem)
  have hs : Sit M Q Z Y t := ⟨hc.hyp, hY, htY, ht1, ht.1.2.1, htQ⟩
  exact ⟨H.CN_le_sup h34 h311a hspread ht hs,
    fun r hr hrY => H.conj_LB_inf_CN_eq h34 hspread ht hs hr hrY⟩

end CFSG.RankThree.GF2n.Stroth80
