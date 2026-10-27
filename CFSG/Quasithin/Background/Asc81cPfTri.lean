module

public import CFSG.Quasithin.Background.Asc81cPfOrd3
public import Certificates.Certificate7226

public section

namespace CFSG.Quasithin

namespace Asc81c

namespace Pf

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.KGroups.Native Check

theorem c7226_check4 : checkT 4 = true :=
  Certificates.certificate7226.1

theorem c7226_check3 : checkT 3 = true :=
  Certificates.certificate7226.2

theorem mem_allLists {N : ℕ} : ∀ {k : ℕ} {l : List ℕ}, l.length = k → (∀ a ∈ l, a < N) →
    l ∈ allLists N k
  | 0, [], _, _ => by simp [allLists]
  | k + 1, a :: l, hl, ha => by
    simp only [allLists, List.mem_flatMap, List.mem_range, List.mem_map]
    exact ⟨a, ha a (List.mem_cons_self ..), l,
      mem_allLists (by simpa using hl) (fun b hb => ha b (List.mem_cons_of_mem _ hb)), rfl⟩

theorem evalG_mem {Γ : Type*} [Group Γ] {K : Subgroup Γ} {a b : Γ} (ha : a ∈ K) (hb : b ∈ K)
    (w : List Bool) : evalG a b w ∈ K := by
  induction w with
  | nil => exact K.one_mem
  | cons c w ih =>
    cases c
    · exact K.mul_mem ha ih
    · exact K.mul_mem hb ih

variable {W : Type*} [CommGroup W] [Finite W] {G : Subgroup (MulAut W)}

section Index

theorem index_fixV_frob21 (hW : ∀ w : W, w ^ 2 = 1) {F A : Subgroup (MulAut W)}
    (hF : Nat.card F = 21) (hna : ∃ a ∈ F, ∃ b ∈ F, a * b ≠ b * a) (hAF : A ≤ F)
    (hA : Hyp101 G A) (hA3 : Nat.card A = 3) : (fixV F).index = 8 := by
  have h8 := card_commSub_frob21 hW hF hna hAF hA3 (by rw [card_commSub hA, hA3])
  have hodd : Odd (Nat.card F) := by rw [hF]; decide
  have h1 := card_fixV_mul_card_commSub hW hodd
  have h2 := (fixV F).card_mul_index
  rw [h8] at h1
  have hpos : 0 < Nat.card (fixV F) := Nat.card_pos
  rw [← h2] at h1
  exact (Nat.eq_of_mul_eq_mul_left hpos h1).symm

omit [Finite W] in
theorem exists_ne_of_not_commutes {A M : Subgroup (MulAut W)} (h : ¬ Commutes A M) :
    ∃ a ∈ A ⊔ M, ∃ b ∈ A ⊔ M, a * b ≠ b * a := by
  by_contra hall
  push Not at hall
  exact h fun a ha b hb => hall a (Subgroup.mem_sup_left ha) b (Subgroup.mem_sup_right hb)

theorem index_fixV_triple (hW : ∀ w : W, w ^ 2 = 1) {A M B : Subgroup (MulAut W)}
    (hM : Hyp101 G M) (hM3 : Nat.card M = 3) (hF₁ : Nat.card ↥(A ⊔ M) = 21)
    (hF₂ : Nat.card ↥(M ⊔ B) = 21) (hAM : ¬ Commutes A M) (hMB : ¬ Commutes M B) :
    8 ≤ (fixV ((A ⊔ M) ⊔ (M ⊔ B))).index ∧ (fixV ((A ⊔ M) ⊔ (M ⊔ B))).index ≤ 16 := by
  have i₁ := index_fixV_frob21 hW hF₁ (exists_ne_of_not_commutes hAM) le_sup_right hM hM3
  have i₂ := index_fixV_frob21 hW hF₂ (exists_ne_of_not_commutes hMB) le_sup_left hM hM3
  have iM := (index_fixV_eq_four hW hM hM3).1
  have hsup := fixV_sup (A ⊔ M) (M ⊔ B)
  constructor
  · have h1 := Subgroup.index_dvd_of_le (show fixV ((A ⊔ M) ⊔ (M ⊔ B)) ≤ fixV (A ⊔ M) by
      rw [hsup]; exact inf_le_left)
    rw [i₁] at h1
    exact Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite) h1
  · rw [hsup]
    have hle : fixV (A ⊔ M) ⊔ fixV (M ⊔ B) ≤ fixV M :=
      sup_le (fun v hv z hz => hv z (Subgroup.mem_sup_right hz))
        (fun v hv z hz => hv z (Subgroup.mem_sup_left hz))
    have hc := card_sup_mul_card_inf (fixV (A ⊔ M)) (fixV (M ⊔ B))
    have hs := Subgroup.card_le_of_le hle
    have e1 := (fixV (A ⊔ M)).card_mul_index
    have e2 := (fixV (M ⊔ B)).card_mul_index
    have e3 := (fixV M).card_mul_index
    have e4 := (fixV (A ⊔ M) ⊓ fixV (M ⊔ B)).card_mul_index
    rw [i₁] at e1
    rw [i₂] at e2
    rw [iM] at e3
    set w := Nat.card W
    set s := Nat.card ↥(fixV (A ⊔ M) ⊔ fixV (M ⊔ B))
    set i := Nat.card ↥(fixV (A ⊔ M) ⊓ fixV (M ⊔ B))
    set k := (fixV (A ⊔ M) ⊓ fixV (M ⊔ B)).index
    have hw : 0 < w := Nat.card_pos
    have hi : 0 < i := Nat.card_pos
    have h1 : w * w ≤ 16 * (w * i) := by nlinarith
    have h2 : w ≤ 16 * i := by
      have := Nat.le_of_mul_le_mul_left (by linarith : w * w ≤ w * (16 * i)) hw
      exact this
    nlinarith

end Index

section Triple

variable {A M B : Subgroup (MulAut W)}

theorem mem_partners {n : ℕ} {t : Array ℕ} {c : List ℕ} (hc : c.length = n)
    (hcb : ∀ a ∈ c, a < 2 ^ n) (hord : ord3V n c = true) (hpre : pre1 n (x0 n) (linA n c) = true)
    (ht : t = linA n c) : t ∈ partners n (x0 n) := by
  unfold partners
  rw [List.mem_filterMap]
  exact ⟨c, mem_allLists hc hcb, by rw [hord, hpre, ht]; rfl⟩

omit [Finite W] in
theorem pre1_eq_true {H : Subgroup (MulAut W)} {n : ℕ}
    (hcard : Nat.card (W ⧸ fixV H) = 2 ^ n) (hn : n = 3 ∨ n = 4)
    {φ : Fin (2 ^ n) → W ⧸ fixV H} (hφ : Function.Bijective φ)
    (hinj : Function.Injective (quoAct H))
    {m a : MulAut W} (hmH : m ∈ H) (haH : a ∈ H) (ha3 : a ^ 3 = 1)
    (hrepm : Rep (2 ^ n) (x0 n) (permOf hφ (quoAct H ⟨m, hmH⟩))) {t : Array ℕ}
    (hrepa : Rep (2 ^ n) t (permOf hφ (quoAct H ⟨a, haH⟩)))
    (hfix : Nat.card (fixV (Subgroup.zpowers (quoAct H ⟨a, haH⟩))) * 4 = Nat.card (W ⧸ fixV H))
    (hma : m * a ≠ a * m) {F : Subgroup (MulAut W)} (hmF : m ∈ F) (haF : a ∈ F)
    (hF : Nat.card F = 21) : pre1 n (x0 n) t = true := by
  have hM : Function.Injective ((permOfHom hφ).comp (quoAct H)) :=
    (permOfHom_injective hφ).comp hinj
  unfold pre1
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_eq_eq_not, Bool.not_true]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  ·
    rw [ord3A_iff hrepa]
    have h1 : (⟨a, haH⟩ : H) ^ 3 = 1 := Subtype.ext (by simp [ha3])
    rw [← permOfHom_apply, ← map_pow, ← map_pow, h1, map_one, map_one]
  ·
    rw [fixCount_eq hrepa, ← Nat.card_eq_fintype_card]
    have e1 : Nat.card {i : Fin (2 ^ n) // permOf hφ (quoAct H ⟨a, haH⟩) i = i} =
        Nat.card (fixV (Subgroup.zpowers (quoAct H ⟨a, haH⟩))) := by
      refine Nat.card_congr ((Equiv.subtypeEquiv (Equiv.ofBijective φ hφ)
        (fun i => (permOf_eq_iff hφ _ i i).trans Iff.rfl)).trans
        (Equiv.subtypeEquivRight fun q => ⟨fun h => mem_fixV_zpowers h,
          fun h => h _ (Subgroup.mem_zpowers _)⟩))
    rw [e1]
    rw [hcard] at hfix
    rcases hn with rfl | rfl
    · have h8 : (2 : ℕ) ^ 3 = 8 := by norm_num
      rw [h8] at hfix
      show _ = 2
      omega
    · have h16 : (2 : ℕ) ^ 4 = 16 := by norm_num
      rw [h16] at hfix
      show _ = 4
      omega
  ·
    cases hc : eqA (2 ^ n) (compA (2 ^ n) (x0 n) t) (compA (2 ^ n) t (x0 n))
    · rfl
    · exfalso
      have h1 := (eqA_iff (rep_compA hrepm hrepa) (rep_compA hrepa hrepm)).1 hc
      have h1' : ((permOfHom hφ).comp (quoAct H)) (⟨m, hmH⟩ * ⟨a, haH⟩) =
          ((permOfHom hφ).comp (quoAct H)) (⟨a, haH⟩ * ⟨m, hmH⟩) := by
        simp only [map_mul, MonoidHom.comp_apply, permOfHom_apply]
        exact h1
      exact hma (congrArg Subtype.val (hM h1'))
  ·
    unfold lawsOK
    rw [List.all_eq_true]
    intro w _
    have hrep := rep_evalG_quoAct hφ hrepm hrepa w
    unfold ord21A
    rw [eqA_iff (rep_powA hrep 21) rep_idA]
    have h1 : ((evalG (⟨m, hmH⟩ : H) ⟨a, haH⟩ w : H) : MulAut W) = evalG m a w :=
      map_evalG H.subtype _ _ w
    have h2 : evalG m a w ∈ F := evalG_mem hmF haF w
    have h3 : (evalG (⟨m, hmH⟩ : H) ⟨a, haH⟩ w) ^ 21 = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, h1, Subgroup.coe_one]
      have := pow_card_eq_one' (G := F) (x := ⟨evalG m a w, h2⟩)
      rw [hF] at this
      exact congrArg Subtype.val this
    rw [← permOfHom_apply, ← map_pow, ← map_pow, h3, map_one, map_one]

theorem triple333
    (hW : ∀ w : W, w ^ 2 = 1) (hA : Hyp102 G A) (hM : Hyp102 G M) (hB : Hyp102 G B)
    (hA3 : Nat.card A = 3) (hM3 : Nat.card M = 3) (hB3 : Nat.card B = 3) (hAM : ¬ Commutes A M)
    (hMB : ¬ Commutes M B) : A ⊔ M = M ⊔ B := by
  have hF₁ : Nat.card ↥(A ⊔ M) = 21 := (ord3_pair hW hA hM hA3 hM3).resolve_left hAM
  have hF₂ : Nat.card ↥(M ⊔ B) = 21 := (ord3_pair hW hM hB hM3 hB3).resolve_left hMB
  obtain ⟨a, haA, hao, hAa⟩ := exists_gen_three hA3
  obtain ⟨m, hmM, hmo, hMm⟩ := exists_gen_three hM3
  obtain ⟨b, hbB, hbo, hBb⟩ := exists_gen_three hB3
  set H := (A ⊔ M) ⊔ (M ⊔ B) with hH
  have hAH : A ≤ H := le_sup_left.trans le_sup_left
  have hMH : M ≤ H := le_sup_right.trans le_sup_left
  have hBH : B ≤ H := le_sup_right.trans le_sup_right
  have haH : a ∈ H := hAH haA
  have hmH : m ∈ H := hMH hmM
  have hbH : b ∈ H := hBH hbB
  have hHG : H ≤ G := sup_le (sup_le hA.1.1 hM.1.1) (sup_le hM.1.1 hB.1.1)
  obtain ⟨h8, h16⟩ := index_fixV_triple hW hM.1 hM3 hF₁ hF₂ hAM hMB
  have hinj := quoAct_injective_of_le hW hM hM3 hHG hMH h16
  have hQ : ∀ q : W ⧸ fixV H, q ^ 2 = 1 := fun q => by
    obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective q
    rw [← QuotientGroup.mk_pow, hW, QuotientGroup.mk_one]
  have ha3 : a ^ 3 = 1 := by rw [← hao]; exact pow_orderOf_eq_one a
  have hm3 : m ^ 3 = 1 := by rw [← hmo]; exact pow_orderOf_eq_one m
  have hb3 : b ^ 3 = 1 := by rw [← hbo]; exact pow_orderOf_eq_one b
  have hξ3 : quoAct H ⟨m, hmH⟩ ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨m, hmH⟩ : H) ^ 3 = 1 := Subtype.ext (by simp [hm3])
    rw [this, map_one]
  have hfixm := card_fixV_quoAct hW hM.1 hM3 hMm hmH hMH hmo
  have hfixa := card_fixV_quoAct hW hA.1 hA3 hAa haH hAH hao
  have hfixb := card_fixV_quoAct hW hB.1 hB3 hBb hbH hBH hbo
  have hgen : ∀ {Z : Subgroup (MulAut W)} {z : MulAut W}, Z = Subgroup.zpowers z →
      ¬ Commutes Z M → m * z ≠ z * m := by
    intro Z z hZz hZM h
    apply hZM
    intro u hu v hv
    rw [hZz] at hu
    rw [hMm] at hv
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hv
    exact (Commute.zpow_zpow h.symm i j).eq
  have hma : m * a ≠ a * m := hgen hAa hAM
  have hmb : m * b ≠ b * m := hgen hBb (fun h => hMB h.symm)
  have hmeet : ∀ q : W ⧸ fixV H, quoAct H ⟨m, hmH⟩ q = q → quoAct H ⟨a, haH⟩ q = q →
      quoAct H ⟨b, hbH⟩ q = q → q = 1 := by
    intro q h1 h2 h3
    obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective q
    have hodd : ∀ (z : MulAut W) (hz : z ∈ H), orderOf z = 3 →
        Odd (orderOf ((⟨z, hz⟩ : H) : MulAut W)) := fun z hz h => by
      show Odd (orderOf z)
      rw [h]
      decide
    rw [quoAct_mk_eq_iff hW (hodd m hmH hmo)] at h1
    rw [quoAct_mk_eq_iff hW (hodd a haH hao)] at h2
    rw [quoAct_mk_eq_iff hW (hodd b hbH hbo)] at h3
    have hw : w ∈ fixV H := by
      rw [hH, fixV_sup, fixV_sup, fixV_sup]
      refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
      · rw [hAa]; exact mem_fixV_zpowers h2
      · rw [hMm]; exact mem_fixV_zpowers h1
      · rw [hMm]; exact mem_fixV_zpowers h1
      · rw [hBb]; exact mem_fixV_zpowers h3
    exact (QuotientGroup.eq_one_iff w).2 hw
  have hcardQ : Nat.card (W ⧸ fixV H) = (fixV H).index := (Subgroup.index_eq_card _).symm
  have hpow : Nat.card (W ⧸ fixV H) = 2 ^ rk (⊤ : Subgroup (W ⧸ fixV H)) := by
    rw [← card_eq_two_pow hQ ⊤, Subgroup.card_top]
  have hr : rk (⊤ : Subgroup (W ⧸ fixV H)) = 3 ∨ rk (⊤ : Subgroup (W ⧸ fixV H)) = 4 := by
    rw [← hcardQ, hpow] at h8 h16
    have h1 : 3 ≤ rk (⊤ : Subgroup (W ⧸ fixV H)) := by
      by_contra h
      push Not at h
      have := Nat.pow_le_pow_right (by norm_num : 0 < 2) (Nat.le_of_lt_succ h)
      omega
    have h2 : rk (⊤ : Subgroup (W ⧸ fixV H)) ≤ 4 := by
      by_contra h
      push Not at h
      have := Nat.pow_le_pow_right (by norm_num : 0 < 2) h
      omega
    omega
  have core : ∀ n, (n = 3 ∨ n = 4) → Nat.card (W ⧸ fixV H) = 2 ^ n →
      ∀ (φ : Fin (2 ^ n) → W ⧸ fixV H) (hφ : Function.Bijective φ),
      (∀ i j, φ (i ^^^ j) = φ i * φ j) → Rep (2 ^ n) (x0 n) (permOf hφ (quoAct H ⟨m, hmH⟩)) →
      checkT n = true → A ⊔ M = M ⊔ B := by
    intro n hn hcard φ hφ hxor hrepm hck
    have hM' : Function.Injective ((permOfHom hφ).comp (quoAct H)) :=
      (permOfHom_injective hφ).comp hinj
    have htab : ∀ (z : MulAut W) (hz : z ∈ H), z ^ 3 = 1 → ∃ c : List ℕ, c.length = n ∧
        (∀ x ∈ c, x < 2 ^ n) ∧ Rep (2 ^ n) (linA n c) (permOf hφ (quoAct H ⟨z, hz⟩)) ∧
        ord3V n c = true := by
      intro z hz hz3
      · refine ⟨List.ofFn fun k : Fin n =>
          (permOf hφ (quoAct H ⟨z, hz⟩) ⟨2 ^ (k : ℕ), Nat.pow_lt_pow_right (by norm_num) k.2⟩ :
            ℕ), List.length_ofFn, ?_, ?_, ?_⟩
        · intro x hx
          obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hx
          exact Fin.isLt _
        · refine rep_linA _ (permOf_xor hφ hxor _) _ fun k hk => ?_
          rw [List.getD_eq_getElem _ _ (by simpa using hk), List.getElem_ofFn]
        · refine ord3V_eq_true (permOf_xor hφ hxor (quoAct H ⟨z, hz⟩)) (fun k hk => ?_) ?_
          · rw [List.getD_eq_getElem _ _ (by simpa using hk), List.getElem_ofFn]
          · have h1 : (⟨z, hz⟩ : H) ^ 3 = 1 := Subtype.ext (by simp [hz3])
            rw [← permOfHom_apply, ← map_pow, ← map_pow, h1, map_one, map_one]
    obtain ⟨ca, hcal, hcab, hrepa, hcao⟩ := htab a haH ha3
    obtain ⟨cb, hcbl, hcbb, hrepb, hcbo⟩ := htab b hbH hb3
    have hpa := mem_partners hcal hcab hcao (pre1_eq_true hcard hn hφ hinj hmH haH ha3 hrepm
      hrepa hfixa hma (Subgroup.mem_sup_right hmM) (Subgroup.mem_sup_left haA) hF₁) rfl
    have hpb := mem_partners hcbl hcbb hcbo (pre1_eq_true hcard hn hφ hinj hmH hbH hb3 hrepm
      hrepb hfixb hmb (Subgroup.mem_sup_left hmM) (Subgroup.mem_sup_right hbB) hF₂) rfl
    have hφ0 : φ ⟨0, Nat.two_pow_pos n⟩ = 1 := by
      have h := hxor ⟨0, Nat.two_pow_pos n⟩ ⟨0, Nat.two_pow_pos n⟩
      have h0 : (⟨0, Nat.two_pow_pos n⟩ : Fin (2 ^ n)) ^^^ ⟨0, Nat.two_pow_pos n⟩ =
          ⟨0, Nat.two_pow_pos n⟩ := Fin.ext (by simp)
      rw [h0] at h
      exact (mul_eq_left.1 h.symm)
    have hm3t : meet3 (2 ^ n) (x0 n) (linA n ca) (linA n cb) = true := by
      unfold meet3
      rw [allLt_iff]
      intro i hi
      by_cases h1 : (x0 n)[i]! = i
      · by_cases h2 : (linA n ca)[i]! = i
        · by_cases h3 : (linA n cb)[i]! = i
          · have e1 := (permOf_eq_iff hφ _ _ _).1 ((rep_eq_iff hrepm hi).1 h1)
            have e2 := (permOf_eq_iff hφ _ _ _).1 ((rep_eq_iff hrepa hi).1 h2)
            have e3 := (permOf_eq_iff hφ _ _ _).1 ((rep_eq_iff hrepb hi).1 h3)
            have h4 := hmeet _ e1 e2 e3
            rw [← hφ0] at h4
            have h5 : i = 0 := congrArg Fin.val (hφ.1 h4)
            simp [h5]
          · simp [h3]
        · simp [h2]
      · simp [h1]
    unfold checkT at hck
    simp only [List.all_eq_true] at hck
    have hc := hck _ hpa _ hpb
    simp only [hm3t, Bool.not_true, Bool.false_or, Bool.or_eq_true] at hc
    rcases hc with hpt | hsame
    ·
      exfalso
      unfold ptOK at hpt
      simp only [List.any_eq_true, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hpt
      obtain ⟨w₁, -, hc₁, w₂, -, ⟨hc₂, hnc⟩, v, -, hv⟩ := hpt
      have hrep₁ := rep_evalG_quoAct hφ hrepm hrepa w₁
      have hrep₂ := rep_evalG_quoAct hφ hrepm hrepb w₂
      set c₁ := evalG (⟨m, hmH⟩ : H) ⟨a, haH⟩ w₁ with hc₁def
      set c₂ := evalG (⟨m, hmH⟩ : H) ⟨b, hbH⟩ w₂ with hc₂def
      have h21 : ∀ (c : H) {t : Array ℕ}, Rep (2 ^ n) t (permOf hφ (quoAct H c)) →
          ord21A (2 ^ n) t = true → c ^ 21 = 1 := by
        intro c t ht h
        unfold ord21A at h
        rw [eqA_iff (rep_powA ht 21) rep_idA, ← permOfHom_apply, ← map_pow, ← map_pow] at h
        exact hM' (h.trans (map_one _).symm)
      have hc₁21 := h21 c₁ hrep₁ hc₁
      have hc₂21 := h21 c₂ hrep₂ hc₂
      have hconjrep : ∀ (c : H) {t : Array ℕ}, Rep (2 ^ n) t (permOf hφ (quoAct H c)) →
          Rep (2 ^ n) (conjA (2 ^ n) t (x0 n))
            (permOf hφ (quoAct H (c * ⟨m, hmH⟩ * c ^ 20))) := by
        intro c t ht
        have e : permOf hφ (quoAct H (c * ⟨m, hmH⟩ * c ^ 20)) = permOf hφ (quoAct H c) *
            (permOf hφ (quoAct H ⟨m, hmH⟩) * permOf hφ (quoAct H c) ^ 20) := by
          rw [← permOfHom_apply, ← permOfHom_apply, ← permOfHom_apply, ← map_pow, ← map_mul,
            ← map_mul, ← map_pow, ← map_mul, ← map_mul, mul_assoc]
        rw [e]
        exact rep_compA ht (rep_compA hrepm (rep_powA ht 20))
      have hr₁ := hconjrep c₁ hrep₁
      have hr₂ := hconjrep c₂ hrep₂
      have hinv : ∀ c : H, c ^ 21 = 1 → c ^ 20 = c⁻¹ := fun c h =>
        eq_inv_of_mul_eq_one_right (by rw [← pow_succ', h])
      have hmem : ∀ c : H, c ^ 21 = 1 →
          ((c * ⟨m, hmH⟩ * c ^ 20 : H) : MulAut W) ∈ M.map (MulAut.conj (c : MulAut W)).toMonoidHom
          := by
        intro c hc
        refine ⟨m, hmM, ?_⟩
        rw [hinv c hc]
        rfl
      have hM₁ := hyp102_map_conj hM (hHG c₁.2)
      have hM₂ := hyp102_map_conj hM (hHG c₂.2)
      have hcardc : ∀ c : MulAut W,
          Nat.card ↥(M.map (MulAut.conj c).toMonoidHom) = 3 := fun c => by
        rw [← hM3]
        exact (Nat.card_congr (Subgroup.equivMapOfInjective M _
          (MulEquiv.injective (MulAut.conj c))).toEquiv).symm
      rcases ord3_pair hW hM₁ hM₂ (hcardc _) (hcardc _) with hcomm | h21'
      ·
        have e1 := hcomm _ (hmem c₁ hc₁21) _ (hmem c₂ hc₂21)
        have e2 : (c₁ * ⟨m, hmH⟩ * c₁ ^ 20) * (c₂ * ⟨m, hmH⟩ * c₂ ^ 20) =
            (c₂ * ⟨m, hmH⟩ * c₂ ^ 20) * (c₁ * ⟨m, hmH⟩ * c₁ ^ 20) := Subtype.ext e1
        set g₁ : H := c₁ * ⟨m, hmH⟩ * c₁ ^ 20 with hg₁
        set g₂ : H := c₂ * ⟨m, hmH⟩ * c₂ ^ 20 with hg₂
        have e3 : ((permOfHom hφ).comp (quoAct H)) g₁ * ((permOfHom hφ).comp (quoAct H)) g₂ =
            ((permOfHom hφ).comp (quoAct H)) g₂ * ((permOfHom hφ).comp (quoAct H)) g₁ := by
          rw [← map_mul, ← map_mul, e2]
        have e4 := (eqA_iff (rep_compA hr₁ hr₂) (rep_compA hr₂ hr₁)).2 e3
        rw [e4] at hnc
        exact Bool.noConfusion hnc
      ·
        have hvrep := rep_evalG_quoAct hφ hr₁ hr₂ v
        have hvmem : ((evalG (c₁ * ⟨m, hmH⟩ * c₁ ^ 20) (c₂ * ⟨m, hmH⟩ * c₂ ^ 20) v : H) :
            MulAut W) ∈ M.map (MulAut.conj (c₁ : MulAut W)).toMonoidHom ⊔
              M.map (MulAut.conj (c₂ : MulAut W)).toMonoidHom := by
          rw [show ((evalG (c₁ * ⟨m, hmH⟩ * c₁ ^ 20) (c₂ * ⟨m, hmH⟩ * c₂ ^ 20) v : H) :
            MulAut W) = evalG ((c₁ * ⟨m, hmH⟩ * c₁ ^ 20 : H) : MulAut W)
              ((c₂ * ⟨m, hmH⟩ * c₂ ^ 20 : H) : MulAut W) v from map_evalG H.subtype _ _ v]
          exact evalG_mem (Subgroup.mem_sup_left (hmem c₁ hc₁21))
            (Subgroup.mem_sup_right (hmem c₂ hc₂21)) v
        have hv21 : (evalG (c₁ * ⟨m, hmH⟩ * c₁ ^ 20) (c₂ * ⟨m, hmH⟩ * c₂ ^ 20) v) ^ 21 = 1 := by
          apply Subtype.ext
          rw [Subgroup.coe_pow, Subgroup.coe_one]
          have := pow_card_eq_one' (G := ↥(M.map (MulAut.conj (c₁ : MulAut W)).toMonoidHom ⊔
            M.map (MulAut.conj (c₂ : MulAut W)).toMonoidHom)) (x := ⟨_, hvmem⟩)
          rw [h21'] at this
          exact congrArg Subtype.val this
        have hv' : ord21A (2 ^ n) (evalWA (2 ^ n)
            (conjA (2 ^ n) (evalWA (2 ^ n) (x0 n) (linA n ca) w₁) (x0 n))
            (conjA (2 ^ n) (evalWA (2 ^ n) (x0 n) (linA n cb) w₂) (x0 n)) v) = true := by
          unfold ord21A
          rw [eqA_iff (rep_powA hvrep 21) rep_idA, ← permOfHom_apply, ← map_pow, ← map_pow, hv21,
            map_one, map_one]
        rw [hv'] at hv
        exact Bool.noConfusion hv
    ·
      unfold sameOK at hsame
      obtain ⟨w, -, hw⟩ := List.any_eq_true.1 hsame
      have hrep := rep_evalG_quoAct hφ hrepm hrepa w
      have e1 := (eqA_iff hrep hrepb).1 hw
      have e2 : ((permOfHom hφ).comp (quoAct H)) (evalG ⟨m, hmH⟩ ⟨a, haH⟩ w) =
          ((permOfHom hφ).comp (quoAct H)) ⟨b, hbH⟩ := e1
      have e3 := congrArg Subtype.val (hM' e2)
      rw [show ((evalG (⟨m, hmH⟩ : H) ⟨a, haH⟩ w : H) : MulAut W) = evalG m a w from
        map_evalG H.subtype _ _ w] at e3
      have e4 : evalG m a w = b := e3
      have hbF : b ∈ A ⊔ M := by
        rw [← e4]
        exact evalG_mem (Subgroup.mem_sup_right hmM) (Subgroup.mem_sup_left haA) w
      have hle : M ⊔ B ≤ A ⊔ M := sup_le le_sup_right (by
        rw [hBb]
        exact (Subgroup.zpowers_le).2 hbF)
      exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hF₁, hF₂])).symm
  rcases hr with hr | hr
  · have hcard : Nat.card (W ⧸ fixV H) = 2 ^ 3 := by rw [hpow, hr]
    obtain ⟨φ, hφ, hxor, hrepm⟩ := exists_frame3 hQ hξ3 (by rw [hcard]; norm_num)
      (by rw [hcard] at hfixm; omega)
    exact core 3 (Or.inl rfl) hcard φ hφ hxor hrepm c7226_check3
  · have hcard : Nat.card (W ⧸ fixV H) = 2 ^ 4 := by rw [hpow, hr]
    obtain ⟨φ, hφ, hxor, hrepm⟩ := exists_frame4 hQ hξ3 (by rw [hcard]; norm_num)
      (by rw [hcard] at hfixm; omega)
    exact core 4 (Or.inr rfl) hcard φ hφ hxor hrepm c7226_check4

end Triple

end Pf

end Asc81c

end CFSG.Quasithin
