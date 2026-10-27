module

public import CFSG.Quasithin.Vol2.KGFactC31HSRef
public import CFSG.Quasithin.Vol2.KGFactC31Rad
public import CFSG.RankThree.Native.HSMcLFiveCentralizers

public section

namespace CFSG.Quasithin.KGC31.HS

open CFSG.Open CFSG.Blueprint CFSG.Certificates CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native CFSG.Quasithin.KGC31.Native
  CFSG.Quasithin.KGC31 CFSG.RankThree.Native

theorem conj_mem_hs100P {s x : Equiv.Perm (Fin 100)}
    (hs : s ∈ hs100R) (hx : x ∈ hs100P) : s * x * s⁻¹ ∈ hs100P := by
  have := hs100P_normal_R.conj_mem ⟨x, hs100P_le_R hx⟩ (Subgroup.mem_subgroupOf.2 hx) ⟨s, hs⟩
  exact Subgroup.mem_subgroupOf.1 this

@[expose] noncomputable def conjR (s : Equiv.Perm (Fin 100))
    (hs : s ∈ hs100R) : G₀ ≃* G₀ where
  toFun x := ⟨s * x * s⁻¹, conj_mem_hs100P hs x.2⟩
  invFun x := ⟨s⁻¹ * x * s⁻¹⁻¹, conj_mem_hs100P (hs100R.inv_mem hs) x.2⟩
  left_inv x := Subtype.ext (by simp [mul_assoc])
  right_inv x := Subtype.ext (by simp [mul_assoc])
  map_mul' x y := Subtype.ext (by simp [mul_assoc])

theorem map_conjR {s : Equiv.Perm (Fin 100)} (hs : s ∈ hs100R)
    (H : Subgroup G₀) :
    (H.map (conjR s hs).toMonoidHom).map hs100P.subtype =
      (H.map hs100P.subtype).map (MulAut.conj s).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  rfl

@[expose] noncomputable def cand (k : ℕ) : G₀ :=
  elt (candW.getD k [])

theorem forall₂_cand {k : ℕ}
    (hk : k < 7) {l : ℕ} {v : Fin l → G₀} {bs : List Table}
    (hbs : List.Forall₂ (Rep 100) bs (List.ofFn fun i => ((v i : G₀) : Equiv.Perm (Fin 100)))) :
    List.Forall₂ (Rep 100) (conjAll (candT k) bs) (List.ofFn fun i =>
      ((cand k : G₀) : Equiv.Perm (Fin 100)) * ((v i : G₀) : Equiv.Perm (Fin 100)) *
        ((cand k : G₀) : Equiv.Perm (Fin 100))⁻¹) := by
  have hc : Rep 100 (candT k) ((cand k : G₀) : Equiv.Perm (Fin 100)) := rep_elt _
  have h := c_candInv
  rw [List.all_eq_true] at h
  have hci := Rep.inv_of_invOK hc (h k (List.mem_range.mpr hk))
  exact forall₂_conjTab hbs hc hci

theorem closure_ofFn_conj {k : ℕ} {v : Fin k → G₀} (hv : EBasis v) (c : G₀) :
    Subgroup.closure {x | x ∈ List.ofFn fun i => ((c : G₀) : Equiv.Perm (Fin 100)) *
      ((v i : G₀) : Equiv.Perm (Fin 100)) * ((c : G₀) : Equiv.Perm (Fin 100))⁻¹} =
      ((eSub hv).map hs100P.subtype).map (MulAut.conj (c : Equiv.Perm (Fin 100))).toMonoidHom := by
  rw [eSub_eq_closure, MonoidHom.map_closure, MonoidHom.map_closure]
  congr 1
  ext x
  simp [List.mem_ofFn, MulAut.conj_apply]

theorem perm_facts {y t : G₀} (hmove : y * t * y⁻¹ ≠ t)
    (hcomm : ∀ j : ℕ, t * (y ^ j * t * y⁻¹ ^ j) = y ^ j * t * y⁻¹ ^ j * t) :
    (y : Equiv.Perm (Fin 100)) * t * (y : Equiv.Perm (Fin 100))⁻¹ ≠ t ∧
      ∀ j : ℕ, (t : Equiv.Perm (Fin 100)) * ((y : Equiv.Perm (Fin 100)) ^ j * t *
        (y : Equiv.Perm (Fin 100))⁻¹ ^ j) =
        (y : Equiv.Perm (Fin 100)) ^ j * t * (y : Equiv.Perm (Fin 100))⁻¹ ^ j * t := by
  refine ⟨fun h => hmove (Subtype.ext (by simpa using h)), fun j => ?_⟩
  have := congrArg Subtype.val (hcomm j)
  simpa using this

theorem bad_conj {X : Type*} [Group X] {y t : X} (g : X) (hmove : y * t * y⁻¹ ≠ t)
    (hcomm : ∀ j : ℕ, t * (y ^ j * t * y⁻¹ ^ j) = y ^ j * t * y⁻¹ ^ j * t) :
    (g * y * g⁻¹) * (g * t * g⁻¹) * (g * y * g⁻¹)⁻¹ ≠ g * t * g⁻¹ ∧
      ∀ j : ℕ, (g * t * g⁻¹) * ((g * y * g⁻¹) ^ j * (g * t * g⁻¹) * (g * y * g⁻¹)⁻¹ ^ j) =
        (g * y * g⁻¹) ^ j * (g * t * g⁻¹) * (g * y * g⁻¹)⁻¹ ^ j * (g * t * g⁻¹) := by
  have hpow : ∀ j : ℕ, (g * y * g⁻¹) ^ j = g * y ^ j * g⁻¹ := fun j => by
    rw [← MulAut.conj_apply, ← map_pow, MulAut.conj_apply]
  have hpowi : ∀ j : ℕ, (g * y * g⁻¹)⁻¹ ^ j = g * y⁻¹ ^ j * g⁻¹ := fun j => by
    rw [show (g * y * g⁻¹)⁻¹ = g * y⁻¹ * g⁻¹ by group, ← MulAut.conj_apply, ← map_pow,
      MulAut.conj_apply]
  refine ⟨fun h => hmove ?_, fun j => ?_⟩
  · have h' : g * (y * t * y⁻¹) * g⁻¹ = g * t * g⁻¹ := by
      rw [← h]; group
    have := congrArg (fun z => g⁻¹ * z * g) h'
    simpa [mul_assoc] using this
  · rw [hpow, hpowi]
    have h1 := hcomm j
    calc g * t * g⁻¹ * (g * y ^ j * g⁻¹ * (g * t * g⁻¹) * (g * y⁻¹ ^ j * g⁻¹))
        = g * (t * (y ^ j * t * y⁻¹ ^ j)) * g⁻¹ := by group
      _ = g * (y ^ j * t * y⁻¹ ^ j * t) * g⁻¹ := by rw [h1]
      _ = g * y ^ j * g⁻¹ * (g * t * g⁻¹) * (g * y⁻¹ ^ j * g⁻¹) * (g * t * g⁻¹) := by group

theorem orbSub_conj {X : Type} [Group X] (g y t : X) :
    orbSub (g * y * g⁻¹) (g * t * g⁻¹) = (orbSub y t).map (MulAut.conj g).toMonoidHom := by
  rw [orbSub_map]
  simp [MulAut.conj_apply]

theorem lineRec
    (j : Fin 31) :
    (hs100FiveRecordOf j : ℕ) = 0 ∨ (hs100FiveRecordOf j : ℕ) = 2 ∨
      (hs100FiveRecordOf j : ℕ) = 23 := by
  obtain ⟨⟨-, -, -, hrec, -⟩, -⟩ := R3E_HS_McL_full_five_centralizer_structures
  have := hrec j
  simpa using this

theorem exists_line
    {y : Equiv.Perm (Fin 100)}
    (hy : y ∈ hs100FiveQ) (hy1 : y ≠ 1) :
    ∃ j : Fin 31, Subgroup.zpowers y = Subgroup.zpowers (hs100FiveLine j) := by
  obtain ⟨⟨⟨-, -, -, hexp⟩, ⟨hlines, -⟩, -⟩, -⟩ := R3E_HS_McL_full_five_centralizer_structures
  have hy5 : y ^ 5 = 1 := by
    have := Monoid.pow_exponent_eq_one (⟨y, hy⟩ : hs100FiveQ)
    rw [hexp] at this
    exact congrArg Subtype.val this
  have hord : orderOf y = 5 := orderOf_eq_prime hy5 hy1
  have hmem : Subgroup.zpowers y ∈
      {H : Subgroup (Equiv.Perm (Fin 100)) | H ≤ hs100FiveQ ∧ Nat.card H = 5} :=
    ⟨(Subgroup.zpowers_le).mpr hy, by rw [Nat.card_zpowers, hord]⟩
  rw [hlines] at hmem
  obtain ⟨j, hj⟩ := hmem
  exact ⟨j, hj.symm⟩

theorem map_conj_map_conj {X : Type*} [Group X] (H : Subgroup X) (a b : X) :
    (H.map (MulAut.conj a).toMonoidHom).map (MulAut.conj b).toMonoidHom =
      H.map (MulAut.conj (b * a)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

theorem line_pow_five
    (j : Fin 31) :
    hs100FiveLine j ∈ hs100FiveQ ∧ hs100FiveLine j ^ 5 = 1 := by
  obtain ⟨⟨⟨-, -, -, hexp⟩, ⟨hlines, -⟩, -⟩, -⟩ := R3E_HS_McL_full_five_centralizer_structures
  have hmem : Subgroup.zpowers (hs100FiveLine j) ∈
      {H : Subgroup (Equiv.Perm (Fin 100)) | H ≤ hs100FiveQ ∧ Nat.card H = 5} := by
    rw [hlines]; exact ⟨j, rfl⟩
  have hQ : hs100FiveLine j ∈ hs100FiveQ := hmem.1 (Subgroup.mem_zpowers _)
  refine ⟨hQ, ?_⟩
  have := Monoid.pow_exponent_eq_one (⟨_, hQ⟩ : hs100FiveQ)
  rw [hexp] at this
  exact congrArg Subtype.val this

theorem orbSub_cases5
    {y t : G₀} (hy : ∃ k : ℕ, y ^ 5 ^ k = 1) (ht : orderOf t = 2)
    (hmove : y * t * y⁻¹ ≠ t)
    (hcomm : ∀ j : ℕ, t * (y ^ j * t * y⁻¹ ^ j) = y ^ j * t * y⁻¹ ^ j * t) :
    ∃ s : Equiv.Perm (Fin 100), ∃ hs : s ∈ hs100R,
      orbSub y t = (eSub basis_u16).map (conjR s hs).toMonoidHom := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨⟨⟨hQP, -, hcard, -⟩, -, htrans, -⟩, -⟩ := R3E_HS_McL_full_five_centralizer_structures
  set P5 : Subgroup G₀ := hs100FiveQ.subgroupOf hs100P with hP5
  have hP5card : Nat.card P5 = 125 := by
    rw [hP5, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQP).toEquiv, hcard]
  have hP5p : IsPGroup 5 P5 := IsPGroup.of_card (n := 3) (by rw [hP5card]; norm_num)
  have hP5i : ¬ 5 ∣ P5.index := by
    have h := P5.card_mul_index
    rw [hP5card, card_G₀] at h
    have : P5.index = 354816 := by omega
    rw [this]; norm_num
  obtain ⟨g, hg⟩ := exists_conj_mem_of_sylow hP5p hP5i hy
  obtain ⟨hmove₁, hcomm₁⟩ := bad_conj g⁻¹ hmove hcomm
  simp only [inv_inv] at hmove₁ hcomm₁
  set y₁ := g⁻¹ * y * g with hy₁
  set t₁ := g⁻¹ * t * g with ht₁
  have hy₁1 : y₁ ≠ 1 := by
    intro h
    apply hmove₁
    rw [h]; group
  obtain ⟨j, hj⟩ := exists_line (y := (y₁ : Equiv.Perm (Fin 100))) hg
    (fun h => hy₁1 (Subtype.ext h))
  have hlj : hs100FiveLine j ∈ Subgroup.zpowers (y₁ : Equiv.Perm (Fin 100)) := by
    rw [hj]; exact Subgroup.mem_zpowers _
  have hyl : (y₁ : Equiv.Perm (Fin 100)) ∈ Subgroup.zpowers (hs100FiveLine j) := by
    rw [← hj]; exact Subgroup.mem_zpowers _
  obtain ⟨hmove', hcomm'⟩ := perm_facts hmove₁ hcomm₁
  have horb₁ : orbSub (y₁ : Equiv.Perm (Fin 100)) (t₁ : Equiv.Perm (Fin 100)) =
      orbSub (hs100FiveLine j) (t₁ : Equiv.Perm (Fin 100)) :=
    orbSub_eq_of_zpowers hyl hlj
  obtain ⟨hmoveL, hcommL⟩ := bad_of_zpowers hyl hlj hmove' hcomm'
  obtain ⟨hTR, hTconj⟩ := htrans j
  set T := hs100FiveTransporter j with hT
  set r := hs100FiveRecordOf j with hr
  have hline : hs100FiveLine r = T⁻¹ * hs100FiveLine j * T⁻¹⁻¹ := by
    rw [← hTconj]; group
  set t₂ : G₀ := conjR T⁻¹ (hs100R.inv_mem hTR) t₁ with ht₂
  have ht₂e : (t₂ : Equiv.Perm (Fin 100)) = T⁻¹ * t₁ * T⁻¹⁻¹ := rfl
  obtain ⟨hmove₂, hcomm₂⟩ := bad_conj T⁻¹ hmoveL hcommL
  rw [← hline, ← ht₂e] at hmove₂ hcomm₂
  have horb₂ : orbSub (hs100FiveLine r) (t₂ : Equiv.Perm (Fin 100)) =
      (orbSub (hs100FiveLine j) (t₁ : Equiv.Perm (Fin 100))).map
        (MulAut.conj T⁻¹).toMonoidHom := by
    rw [hline, ht₂e, orbSub_conj]
  have ht₂o : orderOf t₂ = 2 := by
    rw [ht₂, MulEquiv.orderOf_eq, ht₁, show g⁻¹ * t * g = MulAut.conj g⁻¹ t by simp,
      MulEquiv.orderOf_eq, ht]
  obtain ⟨Tt, hTt, hrepT⟩ := exists_invTab ht₂o
  have hcomm₂' : ∀ i < 5, (t₂ : Equiv.Perm (Fin 100)) * (hs100FiveLine r ^ i * t₂ *
      (hs100FiveLine r)⁻¹ ^ i) = hs100FiveLine r ^ i * t₂ * (hs100FiveLine r)⁻¹ ^ i * t₂ :=
    fun i _ => hcomm₂ i
  rcases lineRec j with h0 | h2 | h23
  ·
    have hr0 : r = 0 := Fin.ext h0
    rw [hr0] at hmove₂ hcomm₂' horb₂
    have hrep0 : Rep 100 (lineT 0) (hs100FiveLine 0) := by
      have := rep_lineT 0
      rwa [linePerm_eq (Or.inl rfl)] at this
    set candG : List (List (Equiv.Perm (Fin 100))) := (List.range 5).map fun k =>
      List.ofFn fun i => ((cand k : G₀) : Equiv.Perm (Fin 100)) *
        ((vU16 i : G₀) : Equiv.Perm (Fin 100)) * ((cand k : G₀) : Equiv.Perm (Fin 100))⁻¹
      with hcandG
    have hcands : List.Forall₂ (List.Forall₂ (Rep 100)) cands5 candG := by
      rw [cands5, hcandG, List.forall₂_map_left_iff, List.forall₂_map_right_iff]
      refine List.forall₂_same.2 fun k hk => ?_
      exact forall₂_cand (by have := List.mem_range.mp hk; omega) forall₂_u16
    obtain ⟨cg, hcg, hcl⟩ := orbSub_eq_of_orbCheck hn100 c_orb5 hcands (List.mem_singleton_self _)
      hTt hrep0 hrepT (by norm_num) (line_pow_five 0).2 hmove₂ hcomm₂'
    rw [hcandG, List.mem_map] at hcg
    obtain ⟨k, -, rfl⟩ := hcg
    rw [closure_ofFn_conj basis_u16] at hcl
    have hgR : (g : Equiv.Perm (Fin 100)) ∈ hs100R := hs100P_le_R g.2
    have hcR : ((cand k : G₀) : Equiv.Perm (Fin 100)) ∈ hs100R := hs100P_le_R (cand k).2
    set s := (g : Equiv.Perm (Fin 100)) * T * (cand k : Equiv.Perm (Fin 100)) with hs
    have hsR : s ∈ hs100R := hs100R.mul_mem (hs100R.mul_mem hgR hTR) hcR
    refine ⟨s, hsR, Subgroup.map_injective (f := hs100P.subtype) Subtype.val_injective ?_⟩
    rw [map_conjR, orbSub_map]
    have hyt : y = g * y₁ * g⁻¹ ∧ t = g * t₁ * g⁻¹ := ⟨by rw [hy₁]; group, by rw [ht₁]; group⟩
    rw [hyt.1, hyt.2]
    simp only [map_mul, map_inv, Subgroup.coe_subtype]
    rw [orbSub_conj, horb₁]
    have h3 : orbSub (hs100FiveLine j) (t₁ : Equiv.Perm (Fin 100)) =
        (orbSub (hs100FiveLine 0) (t₂ : Equiv.Perm (Fin 100))).map
          (MulAut.conj T).toMonoidHom := by
      rw [horb₂, map_conj_map_conj, mul_inv_cancel]
      ext x; simp
    rw [h3, hcl, map_conj_map_conj, map_conj_map_conj, hs, mul_assoc]
  ·
    exfalso
    have hr2 : r = 2 := Fin.ext h2
    rw [hr2] at hmove₂ hcomm₂'
    have hrep2 : Rep 100 (lineT 2) (hs100FiveLine 2) := by
      have := rep_lineT 2
      rwa [linePerm_eq (Or.inr (Or.inl rfl))] at this
    exact false_of_actCheck hn100 c_act5b hTt (List.mem_singleton_self _) hrep2 hrepT hmove₂ hcomm₂'
  ·
    exfalso
    have hr23 : r = 23 := Fin.ext h23
    rw [hr23] at hmove₂ hcomm₂'
    have hrep23 : Rep 100 (lineT 23) (hs100FiveLine 23) := by
      have := rep_lineT 23
      rwa [linePerm_eq (Or.inr (Or.inr rfl))] at this
    exact false_of_actCheck hn100 c_act5a hTt (List.mem_singleton_self _) hrep23 hrepT hmove₂
      hcomm₂'

@[expose] noncomputable def x7 : G₀ := elt w7

@[expose] noncomputable def x11 : G₀ := elt w11

theorem orderOf_elt {w : List ℤ} {q : ℕ} (hq : 0 < q)
    (h : ordTest 100 q (wordT 100 gensT w) = true) : orderOf (elt w) = q := by
  rw [← Subgroup.orderOf_coe]
  exact (ordTest_iff perm_faithful (rep_elt w) hq).1 h

theorem orderOf_x7 : orderOf x7 = 7 :=
  orderOf_elt (by norm_num) c_ord7

theorem orderOf_x11 : orderOf x11 = 11 :=
  orderOf_elt (by norm_num) c_ord11

theorem sylow_of_order {x : G₀} {p : ℕ} [Fact p.Prime]
    (hx : orderOf x = p) (hpi : ¬ p ∣ 44352000 / p) :
    IsPGroup p (Subgroup.zpowers x) ∧ ¬ p ∣ (Subgroup.zpowers x).index := by
  have hcardx : Nat.card (Subgroup.zpowers x) = p := by rw [Nat.card_zpowers, hx]
  refine ⟨IsPGroup.of_card (n := 1) (by rw [hcardx, pow_one]), ?_⟩
  have h := (Subgroup.zpowers x).card_mul_index
  rw [hcardx, card_G₀] at h
  rw [← h, Nat.mul_div_cancel_left _ (Fact.out : p.Prime).pos] at hpi
  exact hpi

theorem exists_conj_bad {x : G₀}
    {p : ℕ} [hp : Fact p.Prime] (hx : orderOf x = p) (hpi : ¬ p ∣ 44352000 / p) {y t : G₀}
    (hy : ∃ k : ℕ, y ^ p ^ k = 1) (ht : orderOf t = 2) (hmove : y * t * y⁻¹ ≠ t)
    (hcomm : ∀ j : ℕ, t * (y ^ j * t * y⁻¹ ^ j) = y ^ j * t * y⁻¹ ^ j * t) :
    ∃ g t₁ : G₀, orderOf t₁ = 2 ∧ x * t₁ * x⁻¹ ≠ t₁ ∧
      (∀ j : ℕ, t₁ * (x ^ j * t₁ * x⁻¹ ^ j) = x ^ j * t₁ * x⁻¹ ^ j * t₁) ∧
      orbSub y t = (orbSub x t₁).map (MulAut.conj g).toMonoidHom := by
  obtain ⟨hP, hPi⟩ := sylow_of_order hx hpi
  obtain ⟨g, hg⟩ := exists_conj_mem_of_sylow hP hPi hy
  obtain ⟨hmove₁, hcomm₁⟩ := bad_conj g⁻¹ hmove hcomm
  simp only [inv_inv] at hmove₁ hcomm₁
  have hy1 : g⁻¹ * y * g ≠ 1 := by
    intro h
    apply hmove₁
    rw [h]; group
  have hxy := mem_zpowers_of_prime hp.out hx hg hy1
  obtain ⟨hmoveX, hcommX⟩ := bad_of_zpowers hg hxy hmove₁ hcomm₁
  refine ⟨g, g⁻¹ * t * g, ?_, hmoveX, hcommX, ?_⟩
  · rw [show g⁻¹ * t * g = MulAut.conj g⁻¹ t by simp, MulEquiv.orderOf_eq, ht]
  · rw [← orbSub_eq_of_zpowers hg hxy, ← orbSub_conj]
    congr 1 <;> group

theorem orbSub_cases7
    {y t : G₀} (hy : ∃ k : ℕ, y ^ 7 ^ k = 1)
    (ht : orderOf t = 2) (hmove : y * t * y⁻¹ ≠ t)
    (hcomm : ∀ j : ℕ, t * (y ^ j * t * y⁻¹ ^ j) = y ^ j * t * y⁻¹ ^ j * t) :
    ∃ s : Equiv.Perm (Fin 100), ∃ hs : s ∈ hs100R,
      orbSub y t = (eSub basis_u8).map (conjR s hs).toMonoidHom := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨g, t₁, ht₁, hmove₁, hcomm₁, horb⟩ :=
    exists_conj_bad orderOf_x7 (by norm_num) hy ht hmove hcomm
  obtain ⟨Tt, hTt, hrepT⟩ := exists_invTab ht₁
  obtain ⟨hmove', hcomm'⟩ := perm_facts hmove₁ hcomm₁
  set candG : List (List (Equiv.Perm (Fin 100))) := [5, 6].map fun k =>
    List.ofFn fun i => ((cand k : G₀) : Equiv.Perm (Fin 100)) *
      ((vU8 i : G₀) : Equiv.Perm (Fin 100)) * ((cand k : G₀) : Equiv.Perm (Fin 100))⁻¹
    with hcandG
  have hcands : List.Forall₂ (List.Forall₂ (Rep 100)) cands7 candG :=
    .cons (forall₂_cand (by norm_num) forall₂_u8) (.cons (forall₂_cand (by norm_num) forall₂_u8)
      .nil)
  have hx7 : ((x7 : G₀) : Equiv.Perm (Fin 100)) ^ 7 = 1 := by
    rw [← Subgroup.coe_pow, ← orderOf_x7, pow_orderOf_eq_one, Subgroup.coe_one]
  obtain ⟨cg, hcg, hcl⟩ := orbSub_eq_of_orbCheck hn100 c_orb7 hcands (List.mem_singleton_self _)
    hTt (rep_elt w7) hrepT (by norm_num) hx7 hmove' fun j _ => hcomm' j
  rw [hcandG, List.mem_map] at hcg
  obtain ⟨k, -, rfl⟩ := hcg
  rw [closure_ofFn_conj basis_u8] at hcl
  have hgR : (g : Equiv.Perm (Fin 100)) ∈ hs100R := hs100P_le_R g.2
  have hcR : ((cand k : G₀) : Equiv.Perm (Fin 100)) ∈ hs100R := hs100P_le_R (cand k).2
  refine ⟨(g : Equiv.Perm (Fin 100)) * (cand k : Equiv.Perm (Fin 100)), hs100R.mul_mem hgR hcR,
    Subgroup.map_injective (f := hs100P.subtype) Subtype.val_injective ?_⟩
  rw [map_conjR, horb, Subgroup.map_map]
  have e : hs100P.subtype.comp (MulAut.conj g).toMonoidHom =
      (MulAut.conj (g : Equiv.Perm (Fin 100))).toMonoidHom.comp hs100P.subtype := by
    ext x; simp [MulAut.conj_apply]
  rw [e, ← Subgroup.map_map, orbSub_map]
  change (orbSub ((elt w7 : G₀) : Equiv.Perm (Fin 100)) (t₁ : Equiv.Perm (Fin 100))).map _ = _
  rw [hcl, map_conj_map_conj]

theorem not_bad11
    {y t : G₀} (hy : ∃ k : ℕ, y ^ 11 ^ k = 1)
    (ht : orderOf t = 2) (hmove : y * t * y⁻¹ ≠ t)
    (hcomm : ∀ j : ℕ, t * (y ^ j * t * y⁻¹ ^ j) = y ^ j * t * y⁻¹ ^ j * t) : False := by
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  obtain ⟨g, t₁, ht₁, hmove₁, hcomm₁, -⟩ :=
    exists_conj_bad orderOf_x11 (by norm_num) hy ht hmove hcomm
  obtain ⟨Tt, hTt, hrepT⟩ := exists_invTab ht₁
  obtain ⟨hmove', hcomm'⟩ := perm_facts hmove₁ hcomm₁
  exact false_of_actCheck hn100 c_act11 hTt (List.mem_singleton_self _) (rep_elt w11) hrepT hmove'
    fun j _ => hcomm' j

end CFSG.Quasithin.KGC31.HS

end
