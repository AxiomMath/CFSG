module

public import CFSG.RankThree.GF2n.Stroth80.Sec103ATools
public import CFSG.RankThree.GF2n.Stroth80.Sec103AModel
public import CFSG.RankThree.GF2n.Stroth80.Sec101Tt
public import CFSG.RankThree.GF2n.Stroth80.Sec103Three
public import CFSG.RankThree.GF2n.Stroth80.Sec10Five
public import CFSG.RankThree.GF2n.Stroth80.Sec10Swap

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n.Smith81
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

structure BadA (hc : Ctx M Q Z B) (n : ℕ) (t : G) (Y : Subgroup G) : Prop where
  h34 : Stroth34Statement
  hspread : StrothNoA2SpreadStatement
  H : Sec10Hyp hc n
  ht : Good101 M Q Z B t
  hs : Sit M Q Z Y t
  hA : CaseA Q Z t
  hbad : ¬ Q ⊓ QB Y ≤ Vt M (LB M Q B) B Z t

variable {hc : Ctx M Q Z B} {n : ℕ} {t : G} {Y : Subgroup G}

theorem BadA.inf_QB_le_Tt (D : BadA hc n t Y) :
    Q ⊓ QB Y ≤ Tt Q Z (Vt M (LB M Q B) B Z t) t := fun _ ha =>
  D.ht.inf_QB_inf_Ut_le_Tt D.h34 D.hspread D.H D.hs
    ⟨ha, Good101.inf_QB_le_Ut_of_caseA hc D.hs D.hA ha⟩

theorem BadA.inf_QB_le_QB (D : BadA hc n t Y) : Q ⊓ QB Y ≤ QB B := fun _ ha =>
  ((hc.Tt_le_inf_QB D.ht) (D.inf_QB_le_Tt ha)).2

theorem BadA.inf_QB_le_QB_of_root (D : BadA hc n t Y) {X : Subgroup G} (hX : Ctx M Q Z X)
    (htX : t ∈ QB X) : Q ⊓ QB Y ≤ QB X := by
  obtain ⟨m, hm, hmX⟩ := (D.H.rootTrans D.h34 D.hspread) X hX
  have htL : t ∈ conjSubgroup m (LB M Q B) := by
    rw [← hc.LB_conj hm, hmX]
    exact Subgroup.mem_sup_right ⟨htX, D.ht.2.1⟩
  have hcomm := hc.Tt_comm_le_inf_QB D.ht.mem_LB hm htL
  have hT : Tt Q Z (Vt M (LB M Q B) B Z t) t ≤ QB X :=
    sup_le ((hcomm.trans inf_le_right).trans (le_of_eq (congrArg QB hmX))) hX.Z_le_QB.1
  exact D.inf_QB_le_Tt.trans hT

theorem BadA.Vt_le (D : BadA hc n t Y) : Vt M (LB M Q B) B Z t ≤ Q ⊓ QB Y ⊔ Z := by
  have h := D.H.Vt_le (stroth_5_7 D.h34 D.hspread) D.ht
  rwa [inf_QB_zpowers_eq D.hs] at h

theorem BadA.mul_self_eq_one (D : BadA hc n t Y) {a : G} (ha : a ∈ Q ⊓ QB Y) : a * a = 1 := by
  have h1 : a ^ 2 ∈ Z ⊓ QB Y := ⟨sq_mem_Z hc.hyp ha.1, (QB Y).pow_mem ha.2 2⟩
  rw [Z_inf_QB_eq_bot D.hs (smith_1_12 D.hs), Subgroup.mem_bot] at h1
  rwa [pow_two] at h1

theorem BadA.comm_of_mem (D : BadA hc n t Y) {a a' : G} (ha : a ∈ Q ⊓ QB Y)
    (ha' : a' ∈ Q ⊓ QB Y) : a * a' = a' * a := by
  have h1 : ⁅a, a'⁆ ∈ Z ⊓ QB Y := by
    refine ⟨comm_mem_Z hc.hyp ha.1 ha'.1, ?_⟩
    rw [commutatorElement_def]
    exact (QB Y).mul_mem ((QB Y).mul_mem ((QB Y).mul_mem ha.2 ha'.2) ((QB Y).inv_mem ha.2))
      ((QB Y).inv_mem ha'.2)
  rw [Z_inf_QB_eq_bot D.hs (smith_1_12 D.hs), Subgroup.mem_bot] at h1
  exact commutatorElement_eq_one_iff_mul_comm.mp h1

theorem BadA.comm_mem_Q (D : BadA hc n t Y) {c : G} (hcQ : c ∈ Q) : ⁅t, c⁆ ∈ Q := by
  rw [← commutatorElement_inv]
  exact Q.inv_mem (hc.comm_mem_Q D.ht.2.1 hcQ)

theorem BadA.comm_comm_self (D : BadA hc n t Y) {c : G} (hcQ : c ∈ Q) :
    ⁅t, c⁆ * t = t * ⁅t, c⁆ := by
  obtain ⟨m, hm, hsl⟩ := SLlike.exists_SLMNat (D.H.slLike D.ht)
  have ht2 : t ^ 2 = 1 := by rw [pow_two]; exact D.hs.x_sq
  have hU := hc.Ut_le_centralizer D.h34 (D.H.toSec5 D.ht.mem_LB D.ht.2.2.1)
    (SLMNat.toSLNat hsl hm) ht2
  have hx : ⁅t, c⁆ ∈ Ut Q Z t := by
    rw [← commutatorElement_inv]
    exact (Ut Q Z t).inv_mem (comm_mem_Ut hcQ)
  exact Subgroup.mem_centralizer_singleton_iff.mp (hU hx)

theorem BadA.conj_eq_mul_comm (D : BadA hc n t Y) (c : G) : c * t * c⁻¹ = t * ⁅t, c⁆ := by
  have ht2 : t * t = 1 := D.hs.x_sq
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  calc c * t * c⁻¹ = (t * t) * c * t⁻¹ * c⁻¹ := by rw [ht2, htinv]; group
    _ = t * ⁅t, c⁆ := by simp only [commutatorElement_def]; group

theorem BadA.conj_mul_mul_self (D : BadA hc n t Y) {c a : G} (hcQ : c ∈ Q)
    (ha : a ∈ Q ⊓ QB Y) : c * t * c⁻¹ * a * t = a * ⁅t, c⁆ := by
  have hxt := D.comm_comm_self hcQ
  have hat : a * t = t * a :=
    Subgroup.mem_centralizer_singleton_iff.mp ((smith_1_13 D.hs).2.2.2.1 ha).2
  have hxa := Sit.comm_comm_of_mem_inf_QB D.hs hcQ ha
  have ht2 : t * t = 1 := D.hs.x_sq
  rw [D.conj_eq_mul_comm c]
  calc t * ⁅t, c⁆ * a * t = t * ⁅t, c⁆ * (a * t) := by group
    _ = t * ⁅t, c⁆ * (t * a) := by rw [hat]
    _ = t * (⁅t, c⁆ * t) * a := by group
    _ = t * (t * ⁅t, c⁆) * a := by rw [hxt]
    _ = (t * t) * (⁅t, c⁆ * a) := by group
    _ = a * ⁅t, c⁆ := by rw [ht2, one_mul, hxa]

private theorem BadA.img_Vt_eq_img_inf (D : BadA hc n t Y) {K : Type} [Field K] {γ : G → K}
    {M₀ : Tim79.QuadModel Q Z K γ} :
    M₀.img (Vt M (LB M Q B) B Z t) =
      M₀.img (Q ⊓ QB Y ⊓ Vt M (LB M Q B) B Z t) := by
  refine le_antisymm ?_ (M₀.img_mono inf_le_right)
  rintro e ⟨v, hvV, -, rfl⟩
  have hAnorm : Q ⊓ QB Y ≤ Subgroup.normalizer (Z : Set G) :=
    (show Q ⊓ QB Y ≤ Subgroup.centralizer (Z : Set G) from
      fun a ha => Subgroup.mem_centralizer_iff.mpr fun z hz =>
        Smith81.Z_central hc.hyp hz ha.1).trans
      (Subgroup.centralizer_le_normalizer (Z : Set G))
  obtain ⟨a, haA, z, hz, hav⟩ :=
    exists_mul_of_mem_sup_of_le_normalizer hAnorm (D.Vt_le hvV)
  have hzV : z ∈ Vt M (LB M Q B) B Z t := sec39_Z_le_Vt hz
  have haV : a ∈ Vt M (LB M Q B) B Z t := by
    have e' : a = v * z⁻¹ := by rw [← hav]; group
    rw [e']
    exact (Vt _ _ _ _ _).mul_mem hvV ((Vt _ _ _ _ _).inv_mem hzV)
  have hpi : M₀.π a = M₀.π v := by
    have hz0 : M₀.π z = 0 := (M₀.π_ker z (hc.Z_le_Q hz)).mpr hz
    rw [← hav, M₀.π_mul a haA.1 z (hc.Z_le_Q hz), hz0, add_zero]
  exact ⟨a, ⟨haA, haV⟩, haA.1, hpi⟩

private theorem BadA.card_inf_eq (D : BadA hc n t Y) {K : Type} [Field K] {γ : G → K}
    {M₀ : Tim79.QuadModel Q Z K γ} {m : ℕ} (hsl : SLMNat hc t m) :
    Nat.card ↥(Q ⊓ QB Y ⊓ Vt M (LB M Q B) B Z t) = Nat.card Z ^ m := by
  have hcardV : Nat.card ↥(Vt M (LB M Q B) B Z t) = Nat.card Z ^ (m + 1) :=
    SLMNat.card_Vt hsl
  have hVQ : Vt M (LB M Q B) B Z t ≤ Q :=
    (D.ht.Vt_le_Ut D.h34 D.H).trans (hc.Ut_le_Q (hc.LB_le_M D.ht.mem_LB))
  have hZV : Z ≤ Vt M (LB M Q B) B Z t := sec39_Z_le_Vt
  have hcardImgV : Nat.card (M₀.img (Vt M (LB M Q B) B Z t)) = Nat.card Z ^ m := by
    refine Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := Z)) ?_
    calc Nat.card Z * Nat.card (M₀.img (Vt M (LB M Q B) B Z t))
        = Nat.card ↥(Vt M (LB M Q B) B Z t) := (M₀.card_eq hVQ hZV).symm
      _ = Nat.card Z ^ (m + 1) := hcardV
      _ = Nat.card Z * Nat.card Z ^ m := by rw [pow_succ']
  have hZY : Z ⊓ QB Y = ⊥ := Z_inf_QB_eq_bot D.hs (smith_1_12 D.hs)
  have hAZ : Q ⊓ QB Y ⊓ Z = ⊥ := by
    rw [eq_bot_iff]
    intro a ha
    have ha' := Subgroup.mem_inf.mp ha
    have h : a ∈ Z ⊓ QB Y := ⟨ha'.2, (Subgroup.mem_inf.mp ha'.1).2⟩
    rwa [hZY] at h
  have hA₀Z : (Q ⊓ QB Y ⊓ Vt M (LB M Q B) B Z t) ⊓ Z = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hx' := Subgroup.mem_inf.mp hx
    have h : x ∈ (Q ⊓ QB Y) ⊓ Z := ⟨(Subgroup.mem_inf.mp hx'.1).1, hx'.2⟩
    rwa [hAZ] at h
  have hA₀Q : Q ⊓ QB Y ⊓ Vt M (LB M Q B) B Z t ≤ Q :=
    fun x hx => (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hx).1).1
  have hcardA₀ : Nat.card ↥(Q ⊓ QB Y ⊓ Vt M (LB M Q B) B Z t) =
      Nat.card (M₀.img (Q ⊓ QB Y ⊓ Vt M (LB M Q B) B Z t)) :=
    (card_img_eq_of_inf_eq_bot M₀ hA₀Q hA₀Z).symm
  rw [hcardA₀, ← BadA.img_Vt_eq_img_inf D, hcardImgV]

private theorem BadA.exists_finrank_gt (D : BadA hc n t Y) {K : Type} [Field K] [Finite K]
    [CharP K 2] {γ : G → K}
    {M₀ : Tim79.QuadModel Q Z K γ} (hD : GlobalModelData M Q Z γ M₀) {m : ℕ}
    (hA₀card : Nat.card ↥(Q ⊓ QB Y ⊓ Vt M (LB M Q B) B Z t) = Nat.card Z ^ m) :
    ∃ d : ℕ, Nat.card ↥(Q ⊓ QB Y) = Nat.card Z ^ d ∧ m < d := by
  have hZY : Z ⊓ QB Y = ⊥ := Z_inf_QB_eq_bot D.hs (smith_1_12 D.hs)
  have hAZ : Q ⊓ QB Y ⊓ Z = ⊥ := by
    rw [eq_bot_iff]
    intro a ha
    have ha' := Subgroup.mem_inf.mp ha
    have h : a ∈ Z ⊓ QB Y := ⟨ha'.2, (Subgroup.mem_inf.mp ha'.1).2⟩
    rwa [hZY] at h
  have hYB : Y ≠ B := fun hYB => D.ht.2.2.1 (hc.le (hYB ▸ D.hs.mem))
  have hBY : B ≤ QB Y :=
    hc.hyp.le_QB_of_mem_QB hc.conj D.hs.conj D.hs.mem D.hs.ne_one D.ht.2.2.2.1
  have hAeq : Q ⊓ QB Y ⊓ QB B = Q ⊓ QB Y := inf_eq_left.mpr D.inf_QB_le_QB
  have hK : ∀ (s : K) (e : M₀.E), e ∈ M₀.img (Q ⊓ QB Y) →
      s • e ∈ M₀.img (Q ⊓ QB Y) := by
    intro s e he
    rw [← hAeq] at he ⊢
    exact D.H.smul_mem_img_inf_QB_inf_QB D.h34 D.hspread hD D.hs.conj hYB hBY hZY s he
  let S : Submodule K M₀.E :=
    { carrier := (M₀.img (Q ⊓ QB Y) : Set M₀.E)
      add_mem' := fun ha hb => (M₀.img (Q ⊓ QB Y)).add_mem ha hb
      zero_mem' := (M₀.img (Q ⊓ QB Y)).zero_mem
      smul_mem' := fun s e he => hK s e he }
  have hSc : Nat.card ↥(Q ⊓ QB Y) = Nat.card S :=
    (card_img_eq_of_inf_eq_bot M₀ inf_le_left hAZ).symm
  have hcardA : Nat.card ↥(Q ⊓ QB Y) = Nat.card Z ^ Module.finrank K S := by
    rw [hSc, Module.natCard_eq_pow_finrank (K := K) (V := S), hD.card]
  have hlt : (Q ⊓ QB Y ⊓ Vt M (LB M Q B) B Z t) < (Q ⊓ QB Y) := by
    refine lt_of_le_of_ne inf_le_left ?_
    intro heq
    exact D.hbad (heq ▸ inf_le_right)
  have hltCard : Nat.card Z ^ m < Nat.card Z ^ Module.finrank K S := by
    calc Nat.card Z ^ m = Nat.card ↥(Q ⊓ QB Y ⊓ Vt M (LB M Q B) B Z t) := hA₀card.symm
      _ < Nat.card ↥(Q ⊓ QB Y) := Subgroup.card_lt_of_lt hlt
      _ = Nat.card Z ^ Module.finrank K S := hcardA
  have hq1 : 1 < Nat.card Z := by have := hc.hyp.q4; omega
  exact ⟨Module.finrank K S, hcardA, (Nat.pow_lt_pow_iff_right hq1).mp hltCard⟩

theorem BadA.card (D : BadA hc n t Y) :
    ∃ m : ℕ, 2 ≤ m ∧ Nat.card ↥(Q ⊓ QB Y ⊓ Vt M (LB M Q B) B Z t) = Nat.card Z ^ m ∧
      Nat.card Z ^ (m + 1) ≤ Nat.card ↥(Q ⊓ QB Y) := by
  obtain ⟨m, hm, hsl⟩ := SLlike.exists_SLMNat (D.H.slLike D.ht)
  obtain ⟨K, fK, finK, chK, γ, M₀, hD⟩ := stroth_globalModelData hc.hyp
  letI := fK
  letI := finK
  letI := chK
  have hA₀card := BadA.card_inf_eq D (M₀ := M₀) hsl
  obtain ⟨d, hcardA, hmd⟩ := BadA.exists_finrank_gt D hD hA₀card
  refine ⟨m, hm, hA₀card, ?_⟩
  calc Nat.card Z ^ (m + 1) ≤ Nat.card Z ^ d :=
        Nat.pow_le_pow_right (Nat.card_pos (α := Z)) (by omega)
    _ = Nat.card ↥(Q ⊓ QB Y) := hcardA.symm

theorem Good101.exists_yFrame (h34 : Stroth34Statement) (hspread : StrothNoA2SpreadStatement)
    {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n) {t : G} (ht : Good101 M Q Z B t)
    {Y : Subgroup G} (hs : Sit M Q Z Y t) :
    ∃ hcY : Ctx (Subgroup.normalizer (Y : Set G)) (QB Y) Y B, Sec10Hyp hcY n := by
  obtain ⟨g, hgZ, hgB⟩ := Sec10Hyp.exists_conj_swap h34 hspread H ht hs
  have hBQBY : B ≤ QB Y :=
    hc.hyp.le_QB_of_mem_QB hc.conj hs.conj hs.mem hs.ne_one ht.2.2.2.1
  have hQc : conjSubgroup g Q = QB Y := by rw [← Smith81.QB_conj_eq hs.hyp g, hgZ]
  have hMc : conjSubgroup g M = Subgroup.normalizer (Y : Set G) := by
    rw [← Smith81.normalizer_conj_eq hs.hyp g, hgZ]
  have hBY : B ≠ Y := fun hBY => ht.2.2.1 (hc.le (hBY.symm ▸ hs.mem))
  obtain ⟨b, hb⟩ := hc.conj
  let hcY : Ctx (Subgroup.normalizer (Y : Set G)) (QB Y) Y B :=
    { hyp := by rw [← hMc, ← hQc, ← hgZ]; exact hs.hyp.conj g
      conj := ⟨b * g⁻¹, by
        rw [← hgZ, conjSubgroup_conjSubgroup, show b * g⁻¹ * g = b by group, hb]⟩
      le := hBQBY
      ne := hBY }
  exact ⟨hcY, (H.conjG g).of_eq hcY hMc hQc hgZ hgB⟩

end CFSG.RankThree.GF2n.Stroth80
