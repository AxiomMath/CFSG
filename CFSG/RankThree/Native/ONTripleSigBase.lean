module

public import CFSG.RankThree.Native.ONTripleK0
public import CFSG.RankThree.Native.ONTripleSigCheck
public import Certificates.Certificate8145

public noncomputable section

namespace CFSG.RankThree.Native.ONTriple

open CFSG.ONSchreier CFSG.ONSchreier.Native Subgroup Equiv
open CFSG.RankThree.PartTwo.Sec4.Sporadic.SetAction

attribute [local irreducible] dotProduct

theorem wordN_nil : wordN [] = 1 := rfl

theorem wordN_cons
    (k : ℕ) (w : List ℕ) : wordN (k :: w) = nG k * wordN w := by
  simp [wordN]

theorem wordN_val :
    ∀ w : List ℕ, (wordN w).1 = (w.map fun k => eM (if k = 0 then rN1 else rN2)).prod
  | [] => by rw [wordN_nil, OneMemClass.coe_one, List.map_nil, List.prod_nil]
  | k :: w => by
    rw [wordN_cons, Subgroup.coe_mul, wordN_val w, List.map_cons, List.prod_cons]
    rfl

abbrev lw (j l : ℕ) : List ℕ := (lineWords.getD j []).getD l []

abbrev nL (j l : ℕ) : GM := wordN (lw j l)

theorem lw_lt {j : ℕ} (hj : j < 2) {l : ℕ} (hl : l < 4) : ∀ k ∈ lw j l, k < 2 := by
  interval_cases j <;> interval_cases l <;> decide

theorem eM_rL
    {j : ℕ} (hj : j < 2) {l : ℕ} (hl : l < 4) :
    eM ((rL.getD j []).getD l 0) = (nL j l).1 := by
  rw [wordN_val]
  exact sig_check.1 j hj l hl

theorem K0_comm
    {k : GM} (hk : k ∈ K0G) : k * xG 0 = xG 0 * k :=
  mem_centralizer_singleton_iff.1 (K0G_le_centralizer hk)

theorem xG0_cube :
    xG 0 ^ 3 = 1 := relG.vcube 0

theorem mem_sup_x0
    {g : GM} (hg : g ∈ zpowers (xG 0) ⊔ K0G) :
    ∃ a : ℕ, ∃ k ∈ K0G, g = xG 0 ^ a * k := by
  rw [sup_eq_closure] at hg
  induction hg using closure_induction with
  | mem y hy =>
    rcases hy with hy | hy
    · obtain ⟨n, rfl⟩ := (mem_powers_iff_mem_zpowers).2 hy
      exact ⟨n, 1, one_mem _, (mul_one _).symm⟩
    · exact ⟨0, y, hy, (one_mul _).symm⟩
  | one => exact ⟨0, 1, one_mem _, by simp⟩
  | mul a b _ _ ha hb =>
    obtain ⟨p, k, hk, rfl⟩ := ha
    obtain ⟨q, k', hk', rfl⟩ := hb
    refine ⟨p + q, k * k', mul_mem hk hk', ?_⟩
    have hk0 : Commute k (xG 0) := K0_comm hk
    have hc : k * xG 0 ^ q = xG 0 ^ q * k := (hk0.pow_right q).eq
    calc xG 0 ^ p * k * (xG 0 ^ q * k') = xG 0 ^ p * (k * xG 0 ^ q) * k' := by group
      _ = xG 0 ^ p * (xG 0 ^ q * k) * k' := by rw [hc]
      _ = xG 0 ^ (p + q) * (k * k') := by rw [pow_add]; group
  | inv a _ ha =>
    obtain ⟨p, k, hk, rfl⟩ := ha
    refine ⟨2 * p, k⁻¹, inv_mem hk, ?_⟩
    have hk0 : Commute k⁻¹ (xG 0) := K0_comm (inv_mem hk)
    have hc : k⁻¹ * xG 0 ^ (2 * p) = xG 0 ^ (2 * p) * k⁻¹ := (hk0.pow_right (2 * p)).eq
    have hinv : (xG 0 ^ p)⁻¹ = xG 0 ^ (2 * p) := by
      rw [inv_eq_iff_mul_eq_one, ← pow_add, show p + 2 * p = 3 * p by ring, pow_mul, xG0_cube,
        one_pow]
    rw [mul_inv_rev, hinv, hc]

theorem mem_centralizer_x0_iff
    {g : GM} :
    g ∈ centralizer {xG 0} ↔ ∃ a : ℕ, ∃ k ∈ K0G, g = xG 0 ^ a * k := by
  constructor
  · intro hg
    rw [centralizer_x0_eq.1] at hg
    exact mem_sup_x0 hg
  · rintro ⟨a, k, hk, rfl⟩
    rw [centralizer_x0_eq.1]
    exact mul_mem (mem_sup_left (pow_mem (mem_zpowers _) a)) (mem_sup_right hk)

theorem pow_x0_mem_K0
    {a : ℕ} (ha : xG 0 ^ a ∈ K0G) : xG 0 ^ a = 1 := by
  have : xG 0 ^ a ∈ zpowers (xG 0) ⊓ K0G := mem_inf.2 ⟨pow_mem (mem_zpowers _) a, ha⟩
  rw [zpowers_inf_K0] at this
  exact this

theorem three_dvd_of_pow_x0
    {a : ℕ} (ha : xG 0 ^ a = 1) : 3 ∣ a := by
  rw [← orderOf_xG0]
  exact orderOf_dvd_of_pow_eq_one ha

theorem mem_K0_of_two
    {g : GM} (hg : g ∈ centralizer {xG 0}) {n : ℕ} (hn : g ^ (2 ^ n) = 1) :
    g ∈ K0G := by
  obtain ⟨a, k, hk, rfl⟩ := mem_centralizer_x0_iff.1 hg
  have hk0 : Commute k (xG 0) := K0_comm hk
  have hc : Commute (xG 0 ^ a) k := hk0.symm.pow_left a
  rw [hc.mul_pow, ← pow_mul] at hn
  have h1 : xG 0 ^ (a * 2 ^ n) ∈ K0G := by
    rw [eq_inv_of_mul_eq_one_left hn]
    exact inv_mem (pow_mem hk _)
  have h3 := three_dvd_of_pow_x0 (pow_x0_mem_K0 h1)
  have hcop : Nat.Coprime 3 (2 ^ n) := Nat.Coprime.pow_right n (by norm_num)
  obtain ⟨b, rfl⟩ := hcop.dvd_of_dvd_mul_right h3
  rw [pow_mul, xG0_cube, one_pow, one_mul]
  exact hk

@[expose] def blockStab :
    Subgroup GM where
  carrier := {h | ∀ i, ∃ j, (blockF i).image (rhoM h) = blockF j}
  one_mem' := fun i => ⟨i, by simp⟩
  mul_mem' {a b} ha hb := fun i => by
    obtain ⟨j, hj⟩ := hb i
    obtain ⟨k, hk⟩ := ha j
    exact ⟨k, by rw [map_mul, Equiv.Perm.coe_mul, ← Finset.image_image, hj, hk]⟩
  inv_mem' {a} ha := fun i => by
    choose f hf using ha
    have hinj : Function.Injective f := by
      intro i₁ i₂ h12
      apply blockF_injective
      have e1 := hf i₁
      have e2 := hf i₂
      rw [h12, ← e2] at e1
      exact Finset.image_injective (rhoM a).injective e1
    obtain ⟨i', hi'⟩ := (Finite.injective_iff_surjective.1 hinj) i
    refine ⟨i', ?_⟩
    rw [← hi', ← hf i', Finset.image_image, map_inv]
    simp

theorem K0G_le_blockStab :
    K0G ≤ blockStab := fun h hh => himg_K0 h hh

theorem xG0_not_mem_blockStab :
    xG 0 ∉ blockStab := by
  intro hx
  obtain ⟨j, hj⟩ := (hx : ∀ i, ∃ j, (blockF i).image (rhoM (xG 0)) = blockF j) 0
  exact x0_off_blocks hj

theorem mem_K0_of_blocks
    {g : GM} (hg : g ∈ centralizer {xG 0}) (hb : g ∈ blockStab) :
    g ∈ K0G := by
  obtain ⟨a, k, hk, rfl⟩ := mem_centralizer_x0_iff.1 hg
  have hxa : xG 0 ^ a ∈ blockStab := by
    have := mul_mem hb (inv_mem (K0G_le_blockStab hk))
    rwa [mul_inv_cancel_right] at this
  have h3 : 3 ∣ a := by
    by_contra hne
    apply xG0_not_mem_blockStab
    have hmod : a % 3 = 1 ∨ a % 3 = 2 := by omega
    rcases hmod with h | h
    · have e : xG 0 = xG 0 ^ a := by rw [← pow_mod_three xG0_cube a, h, pow_one]
      rw [e]
      exact hxa
    · have e : xG 0 = (xG 0 ^ a) ^ 2 := by
        rw [← pow_mul, ← pow_mod_three xG0_cube (a * 2), Nat.mul_mod, h]
        norm_num
      rw [e]
      exact pow_mem hxa 2
  obtain ⟨b, rfl⟩ := h3
  rw [pow_mul, xG0_cube, one_pow, one_mul]
  exact hk

abbrev vReg (j m i : ℕ) : ℕ := ((rV.getD j []).getD m []).getD i 0

abbrev yReg (j : ℕ) : ℕ := if j == 0 then rX.getD 1 0 else rX12

@[expose] def vG (j m i : ℕ) : GM := ⟨eM (vReg j m i), eM_mem _⟩

@[expose] def yG (j : ℕ) : GM := ⟨eM (yReg j), eM_mem _⟩

theorem chkV_facts
    {j : ℕ} (hj : j < 2) {m : ℕ} (hm : m < 3) :
    vG j m 0 * vG j m 1 = vG j m 2 ∧ vG j m 1 * vG j m 0 = vG j m 2 ∧
      (∀ i < 3, vG j m i * vG j m i = 1 ∧ vG j m i ≠ 1) ∧
      (∀ i < 3, ∃ i' < 3, (yG j)⁻¹ * vG j m i * yG j = vG j m i') ∧
      ∀ i < 3, MapsB (vG j m i).1 (((sigV.getD j []).getD m []).getD i []) := by
  obtain ⟨h01, h10, hsq, hcj, hmb⟩ :=
    v_facts hj hm
  have hy : yReg j = if j = 0 then rX.getD 1 0 else rX12 := by
    interval_cases j <;> rfl
  refine ⟨Subtype.ext h01, Subtype.ext h10, fun i hi => ⟨Subtype.ext (hsq i hi).1,
    fun e => (hsq i hi).2 (congrArg Subtype.val e)⟩, fun i hi => ?_, hmb⟩
  obtain ⟨i', hi', e⟩ := hcj i hi
  refine ⟨i', hi', Subtype.ext ?_⟩
  change (eM (yReg j))⁻¹ * eM (vReg j m i) * eM (yReg j) = eM (vReg j m i')
  rw [hy, mul_assoc]
  exact e

theorem vG_sq
    {j : ℕ} (hj : j < 2) {m : ℕ} (hm : m < 3) {i : ℕ} (hi : i < 3) :
    vG j m i * vG j m i = 1 :=
  ((chkV_facts hj hm).2.2.1 i hi).1

theorem vG_comm_x0
    {j : ℕ} (hj : j < 2) {m : ℕ} (hm : m < 3) {i : ℕ} (hi : i < 3) :
    vG j m i * xG 0 = xG 0 * vG j m i :=
  Subtype.ext (sig_check.2.1 j hj m hm i hi)

theorem vG_mem_K0
    {j : ℕ} (hj : j < 2) {m : ℕ} (hm : m < 3) {i : ℕ} (hi : i < 3) :
    vG j m i ∈ K0G := by
  apply mem_K0_of_two (n := 1)
  · rw [mem_centralizer_singleton_iff]
    exact vG_comm_x0 hj hm hi
  · rw [pow_one, sq]
    exact vG_sq hj hm hi

theorem sV_vals : ∀ j < 2, ∀ m < 3, ∀ i < 3, ∀ b : Fin 6,
    (sV j m i b).val = (((sigV.getD j []).getD m []).getD i []).getD b.val 6 := by
  decide

theorem actK_vG
    {j : ℕ} (hj : j < 2) {m : ℕ} (hm : m < 3) {i : ℕ} (hi : i < 3) :
    actK ⟨vG j m i, vG_mem_K0 hj hm hi⟩ = sV j m i :=
  setAct_eq_of_image blockF_injective himg_K0
    (image_blockF_of_maps (sV_vals j hj m hm i hi) ((chkV_facts hj hm).2.2.2.2 i hi))

theorem yG_zero : yG 0 = xG 1 := rfl

theorem yG_one :
    yG 1 = xG 1 * xG 2 := by
  apply Subtype.ext
  change eM rX12 = eM (rX.getD 1 0) * eM (rX.getD 2 0)
  exact sig_check.2.2.2

theorem yG_comm_x0
    {j : ℕ} (hj : j < 2) : yG j * xG 0 = xG 0 * yG j := by
  have hc : ∀ i : Fin 4, omegaZ 0 i = 0 → xG i * xG 0 = xG 0 * xG i := fun i hi => by
    have := relG.comm 0 i
    rw [hi, ZMod.val_zero, pow_zero, commutatorElement_eq_one_iff_mul_comm] at this
    exact this.symm
  interval_cases j
  · rw [yG_zero]
    exact hc 1 (by decide)
  · rw [yG_one, mul_assoc, hc 2 (by decide), ← mul_assoc, hc 1 (by decide), mul_assoc]

theorem yG_maps
    {j : ℕ} (hj : j < 2) :
    MapsB (eM (if j = 0 then rY1 else rY3)) (sYList.getD j []) := by
  have h := sig_check.2.2.1
  interval_cases j
  · exact h.1
  · exact h.2

theorem yG_val {j : ℕ} (hj : j < 2) :
    (yG j).1 = eM (if j = 0 then rY1 else rY3) := by
  have hk := chkK0_parts.2
  interval_cases j
  · exact hk.1.symm
  · exact hk.2.symm

theorem sY_vals : ∀ j < 2, ∀ b : Fin 6, (sY j b).val = (sYList.getD j []).getD b.val 6 := by
  decide

theorem yG_mem_blockStab
    {j : ℕ} (hj : j < 2) : yG j ∈ blockStab :=
  fun i => ⟨_, image_blockF_of_maps (σ := sY j) (sY_vals j hj)
    (by rw [yG_val hj]; exact yG_maps hj) i⟩

theorem yG_mem_K0
    {j : ℕ} (hj : j < 2) : yG j ∈ K0G :=
  mem_K0_of_blocks (mem_centralizer_singleton_iff.2 (yG_comm_x0 hj)) (yG_mem_blockStab hj)

theorem actK_yG
    {j : ℕ} (hj : j < 2) : actK ⟨yG j, yG_mem_K0 hj⟩ = sY j :=
  setAct_eq_of_image blockF_injective himg_K0
    (image_blockF_of_maps (sY_vals j hj) (by rw [yG_val hj]; exact yG_maps hj))

theorem zG_mem_ker :
    ∀ k : K0G, actK k = 1 → ∃ c : ℕ, (k : GM) = zG ^ c := by
  intro k hk
  rw [← MonoidHom.mem_ker, ker_actK] at hk
  obtain ⟨c, hc⟩ := (mem_powers_iff_mem_zpowers).2 hk
  exact ⟨c, by rw [← hc, SubgroupClass.coe_pow]⟩

theorem eq_of_actK_eq
    {a b : K0G} (h : actK a = actK b) {p q : ℕ} (ha : (a : GM) ^ (2 ^ p) = 1)
    (hb : (b : GM) ^ (2 ^ q) = 1) : a = b := by
  obtain ⟨c, hc⟩ := zG_mem_ker (a * b⁻¹) (by rw [map_mul, map_inv, h, mul_inv_cancel])
  have hab : (a : GM) = zG ^ c * b := by
    rw [← hc, Subgroup.coe_mul, Subgroup.coe_inv, inv_mul_cancel_right]
  have hcom : Commute (zG ^ c) (b : GM) := Commute.pow_left (zG_central b) c
  have haN : (a : GM) ^ (2 ^ p * 2 ^ q) = 1 := by rw [pow_mul, ha, one_pow]
  have hbN : (b : GM) ^ (2 ^ p * 2 ^ q) = 1 := by rw [mul_comm, pow_mul, hb, one_pow]
  rw [hab, hcom.mul_pow, hbN, mul_one, ← pow_mul] at haN
  have h3 : 3 ∣ c * (2 ^ p * 2 ^ q) := by
    rw [← relG.orderOf_x]
    exact orderOf_dvd_of_pow_eq_one haN
  have hcop : Nat.Coprime 3 (2 ^ p * 2 ^ q) := by
    rw [← pow_add]
    exact Nat.Coprime.pow_right _ (by norm_num)
  obtain ⟨d, rfl⟩ := hcop.dvd_of_dvd_mul_right h3
  apply Subtype.ext
  rw [hab, pow_mul, relG.xcube, one_pow, one_mul]

theorem two_subgroups
    {j : ℕ} (hj : j < 2) (T : Subgroup (Perm (Fin 6)))
    (hA : ∀ t ∈ T, Perm.sign t = 1) (h4 : ∀ t ∈ T, t ^ 4 = 1)
    (hinv : ∀ t ∈ T, cj (sY j) t ∈ T) :
    T = ⊥ ∨ ∃ m < 3, ∀ t, t ∈ T ↔ t = 1 ∨ ∃ i < 3, t = sV j m i := by
  by_cases hT : T = ⊥
  · exact Or.inl hT
  right
  obtain ⟨⟨t, ht⟩, ht1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hT
  have ht1' : t ≠ 1 := fun h => ht1 (Subtype.ext h)
  rcases d1_check j hj t (hA t ht) (h4 t ht) ht1' with ⟨m, hm, i, hi, hti⟩ | hbad
  · have hV : ∀ i' < 3, sV j m i' ∈ T := by
      intro i' hi'
      rcases dV_check j hj m hm i hi i' hi' with h | h | h <;> rw [h, ← hti]
      exacts [ht, hinv _ ht, hinv _ (hinv _ ht)]
    refine ⟨m, hm, fun s => ⟨fun hs => ?_, ?_⟩⟩
    · by_contra hns
      push Not at hns
      have hbad := d2_check j hj m hm s (hA s hs) (h4 s hs) hns.1 hns.2
      rw [List.any_eq_true] at hbad
      obtain ⟨u, hu, hu4⟩ := hbad
      have huT : u ∈ T := by
        have h1 : (1 : Perm (Fin 6)) ∈ T := one_mem _
        have hcs := hinv s hs
        have hccs := hinv _ hcs
        simp only [cand2, List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil,
          or_false] at hu
        rcases hu with ((⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩) | rfl | rfl | rfl)
        · have hvT : v ∈ T := by
            rcases hv with rfl | rfl | rfl | rfl
            exacts [h1, hV 0 (by norm_num), hV 1 (by norm_num), hV 2 (by norm_num)]
          exact mul_mem hs hvT
        · have hvT : v ∈ T := by
            rcases hv with rfl | rfl | rfl | rfl
            exacts [h1, hV 0 (by norm_num), hV 1 (by norm_num), hV 2 (by norm_num)]
          exact mul_mem hcs (mul_mem hs hvT)
        · exact mul_mem hs hcs
        · exact mul_mem hs hccs
        · exact mul_mem (mul_mem hs hcs) hccs
      rw [bne_iff_ne] at hu4
      exact hu4 (h4 u huT)
    · rintro (rfl | ⟨i', hi', rfl⟩)
      · exact one_mem _
      · exact hV i' hi'
  · exfalso
    rw [List.any_eq_true] at hbad
    obtain ⟨u, hu, hu4⟩ := hbad
    have hct := hinv _ ht
    have huT : u ∈ T := by
      simp only [cand1, List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl | rfl
      · exact mul_mem ht hct
      · exact mul_mem (mul_mem ht ht) hct
      · exact mul_mem (mul_mem (mul_mem ht ht) ht) hct
    rw [bne_iff_ne] at hu4
    exact hu4 (h4 u huT)

theorem perm_six_pow_four :
    ∀ t : Perm (Fin 6), t ^ 16 = 1 → t ^ 4 = 1 :=
  Certificates.certificate8145

theorem perm_six_pow_four_of
    {t : Perm (Fin 6)} {n : ℕ} (ht : t ^ (2 ^ n) = 1) : t ^ 4 = 1 := by
  apply perm_six_pow_four
  have h1 : orderOf t ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one ht
  have h2 : orderOf t ∣ 720 := by
    have := orderOf_dvd_card (x := t)
    simpa [Fintype.card_perm, Nat.factorial] using this
  have h3 : Nat.Coprime (orderOf t) 45 :=
    Nat.Coprime.coprime_dvd_left h1 (Nat.Coprime.pow_left n (by norm_num))
  have h4 : orderOf t ∣ 16 := h3.dvd_of_dvd_mul_right (by simpa using h2)
  exact orderOf_dvd_iff_pow_eq_one.1 h4

end CFSG.RankThree.Native.ONTriple
