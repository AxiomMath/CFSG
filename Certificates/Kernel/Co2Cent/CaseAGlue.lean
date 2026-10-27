module

public import Certificates.Kernel.Co2Cent.ChainAGlue
public import CFSG.Certificates.Kernel.OrbRow.PRepFacts
public import CFSG.Certificates.Kernel.OrbRow.CentPerm
public import CFSG.Certificates.Kernel.OrbRow.KeyOrbit

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelCo2Cent

open CFSG.KC.Enum CFSG.KC.OrbRow CFSG.KC.OrbRow.CentGrp CFSG.KC.PGrp CFSG.KS CFSG.KS.Raw
  CFSG.KS.Raw.Orb CFSG.KS.PF CFSG.KD.Co2Cent Subgroup CFSG.Sporadic.Co2Cert

@[expose] noncomputable def wv (wd : List ℕ) : Equiv.Perm (Fin 2300) := (wd.map sA).prod

theorem word_rep {lv x : ℕ} {wd : List ℕ} (h : wordEqK 2300 12 SA 16 lv x wd = true) :
    PRep 2300 12 x (wv wd) ∧ ∀ j ∈ wd, lvOk 16 lv j := by
  obtain ⟨hl, hx⟩ := wordEqK_sound h
  refine ⟨?_, fun j hj => lvOk_of_letter (hl j hj)⟩
  rw [hx]
  exact posWordK_rep (by norm_num) (by norm_num) fun l hl' => prepA (hl l hl').1

theorem wv_mem {wd : List ℕ} {H : Subgroup (Equiv.Perm (Fin 2300))} (h : ∀ j ∈ wd, sA j ∈ H) :
    wv wd ∈ H := by
  apply list_prod_mem
  intro g hg
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hg
  exact h j hj

theorem sA_mem_GA {i j : ℕ} (hj : lvOk 16 (getS MA i) j) : sA j ∈ GA i :=
  subset_closure ⟨j, hj, rfl⟩

theorem wv_mem_P {lv : ℕ} {wd : List ℕ} (h : ∀ j ∈ wd, lvOk 16 lv j) : wv wd ∈ co2P :=
  wv_mem fun j hj => sA_mem (lvOk_iff.1 (h j hj)).1

@[expose] noncomputable def rA (j : ℕ) : Equiv.Perm (Fin 2300) := wv (getLs RW j)

@[expose] noncomputable def tA (j : ℕ) : Equiv.Perm (Fin 2300) := wv (getLs TW j)

@[expose] noncomputable def RA : Subgroup (Equiv.Perm (Fin 2300)) :=
  closure (Set.range fun j : Fin 4 => rA j)

@[expose] noncomputable def TA : Subgroup (Equiv.Perm (Fin 2300)) :=
  closure (Set.range fun j : Fin 4 => tA j)

theorem wFacts : (∀ j < 4, wordEqK 2300 12 SA 16 (getS MA 5) (getS TG j) (getLs TW j) = true) ∧
    ∀ j < 4, wordEqK 2300 12 SA 16 (getS MA 5) (RGp j) (getLs RW j) = true := by
  have h := ch17351_w
  simp only [bAnd_iff] at h
  exact ⟨allN_spec h.1, allN_spec h.2.2⟩

theorem prepRG {j : ℕ} (hj : j < 4) : PRep 2300 12 (RGp j) (rA j) :=
  (word_rep (wFacts.2 j hj)).1

theorem prepTG {j : ℕ} (hj : j < 4) : PRep 2300 12 (getS TG j) (tA j) :=
  (word_rep (wFacts.1 j hj)).1

theorem rA_mem {j : ℕ} (hj : j < 4) : rA j ∈ GA 5 :=
  wv_mem fun l hl => sA_mem_GA ((word_rep (wFacts.2 j hj)).2 l hl)

theorem tA_mem {j : ℕ} (hj : j < 4) : tA j ∈ GA 5 :=
  wv_mem fun l hl => sA_mem_GA ((word_rep (wFacts.1 j hj)).2 l hl)

theorem RA_le : RA ≤ GA 5 := by
  rw [RA, closure_le]
  rintro _ ⟨j, rfl⟩
  exact rA_mem j.2

theorem TA_le : TA ≤ GA 5 := by
  rw [TA, closure_le]
  rintro _ ⟨j, rfl⟩
  exact tA_mem j.2

theorem rA_mem_RA {j : ℕ} (hj : j < 4) : rA j ∈ RA := subset_closure ⟨⟨j, hj⟩, rfl⟩

@[expose] noncomputable def FA (t : Fin 5) : Fin 2300 := bA t

theorem take5 : BA.take 5 = List.ofFn (fun t : Fin 5 => getS BA t) := by decide +kernel

theorem nodup5 : (List.ofFn (fun t : Fin 5 => getS BA t)).Nodup := by decide +kernel

theorem FA_inj : Function.Injective FA := by
  intro s t h
  exact List.nodup_ofFn.1 nodup5 (congrArg Fin.val h)

theorem xFacts : fixSetK 2300 12 4095 xA (BA.take 5) = true ∧ powIdK 2300 12 4095 xA 3 = true ∧
    movesK 2300 12 4095 xA = true ∧ lvCommK 2300 12 4095 SA 16 (getS MA 5) xA = true := by
  have h := ch17351_x
  simp only [bAnd_iff] at h
  exact h

theorem fixA {x : Equiv.Perm (Fin 2300)} (hx : PRep 2300 12 xA x) :
    ∀ i, x i = i ↔ i ∈ Set.range FA := by
  intro i
  have h1 := fixSetK_sound xFacts.1 i.2
  have e : pg 12 4095 xA i = x i := hx i
  rw [e, take5, List.mem_ofFn] at h1
  rw [Fin.ext_iff, h1]
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨t, Fin.ext ht⟩
  · rintro ⟨t, rfl⟩
    exact ⟨t, rfl⟩

theorem memK_iff
    (g : Equiv.Perm (Fin 2300)) : g ∈ GA 5 ↔ g ∈ co2P ∧ ∀ t, g (FA t) = FA t := by
  rw [GA5_eq, mem_stabB]
  constructor
  · rintro ⟨hP, hf⟩
    exact ⟨hP, fun t => hf t t.2⟩
  · rintro ⟨hP, hf⟩
    exact ⟨hP, fun t ht => hf ⟨t, ht⟩⟩

theorem K_comm {x : Equiv.Perm (Fin 2300)} (hx : PRep 2300 12 xA x) :
    ∀ g ∈ GA 5, g * x = x * g := by
  have hle : GA 5 ≤ centralizer {x} := by
    rw [GA, closure_le]
    rintro _ ⟨j, hj, rfl⟩
    rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
    obtain ⟨hj1, hj2⟩ := lvOk_iff.1 hj
    have h := allN_spec xFacts.2.2.2 j hj1
    beta_reduce at h
    rw [testBit_iff_fld.2 hj2] at h
    exact (commOK_iff (prepA hj1) hx).1 h
  exact fun g hg => mem_centralizer_singleton_iff.1 (hle hg)

theorem conj_K
    {x : Equiv.Perm (Fin 2300)} (hx : PRep 2300 12 xA x) {y r : Equiv.Perm (Fin 2300)}
    (hy : y ∈ centP co2P x) (hr : r ∈ GA 5) : y * r * y⁻¹ ∈ GA 5 := by
  obtain ⟨hrP, hrF⟩ := (memK_iff r).1 hr
  have hyP : y ∈ co2P := hy.2
  rw [memK_iff]
  refine ⟨co2P.mul_mem (co2P.mul_mem hyP hrP) (co2P.inv_mem hyP), fun t => ?_⟩
  have hc : y * x = x * y := comm_of_mem_centP hy
  have hci : y⁻¹ * x = x * y⁻¹ := by
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hc, mul_assoc, mul_inv_cancel, mul_one]
  have hfx : x (y⁻¹ (FA t)) = y⁻¹ (FA t) := by
    have h1 := congrArg (fun σ : Equiv.Perm (Fin 2300) => σ (FA t)) hci
    simp only [Equiv.Perm.mul_apply] at h1
    rw [← h1, (fixA hx (FA t)).2 ⟨t, rfl⟩]
  obtain ⟨s, hs⟩ := (fixA hx _).1 hfx
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, ← hs, hrF s, hs]
  exact y.apply_symm_apply (FA t)

@[expose] noncomputable def vR (i : Fin 5) : Fin 2300 := bA (5 + i)

theorem hvR : ∀ i : Fin 5, getS BA (5 + i) = vR i := fun _ => rfl

theorem recR : RK.length = 243 ∧ (RK.map (revKey 12 4095 5)).Nodup ∧
    (0 < 243 → subKey 12 BA 5 5 ∈ RK) ∧ (∀ e ∈ RK, ∀ j < 4, rAct j e ∈ RK) ∧
    ∀ e ∈ RK, ActReach rAct 4 (subKey 12 BA 5 5) e :=
  orbRecK_sound ch17351_r

theorem rAct_tkey {j : ℕ} (hj : j < 4) (u : Fin 5 → Fin 2300) :
    rAct j (tkey 12 u) = tkey 12 (fun i => rA j (u i)) :=
  mapKey_tkey (by norm_num) (prepRG hj) u

theorem reachR : ∀ e, ActReach rAct 4 (subKey 12 BA 5 5) e →
    ∃ r ∈ RA, e = tkey 12 (fun i => r (vR i)) := by
  intro e he
  induction he with
  | root =>
    refine ⟨1, one_mem _, ?_⟩
    rw [subKey_tkey hvR]
    rfl
  | @step e j _ hj ih =>
    obtain ⟨r, hr, rfl⟩ := ih
    refine ⟨rA j * r, mul_mem (rA_mem_RA hj) hr, ?_⟩
    rw [rAct_tkey hj]
    rfl

@[expose] noncomputable def ER : Finset (Fin 5 → Fin 2300) :=
  Finset.univ.filter fun u => tkey 12 u ∈ RK

theorem mem_ER {u : Fin 5 → Fin 2300} : u ∈ ER ↔ tkey 12 u ∈ RK := by
  simp [ER]

theorem card_ER : ER.card = 243 := by
  have himg : ER.image (tkey 12) = RK.toFinset := by
    ext k
    rw [Finset.mem_image, List.mem_toFinset]
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact mem_ER.1 hu
    · intro hk
      obtain ⟨r, -, rfl⟩ := reachR k (recR.2.2.2.2 k hk)
      exact ⟨_, mem_ER.2 hk, rfl⟩
  rw [← Finset.card_image_of_injective _ (fun u u' h => tkey_inj (w := 12) (by norm_num) h), himg,
    List.toFinset_card_of_nodup (List.Nodup.of_map _ recR.2.1), recR.1]

theorem fixR_eq_one :
    ∀ g ∈ GA 5, (∀ i, g (vR i) = vR i) → g = 1 := by
  intro g hg hv
  rw [GA5_eq, mem_stabB] at hg
  refine eq_one_of_fixA hg.1 fun t ht => ?_
  rcases Nat.lt_or_ge t 5 with h5 | h5
  · exact hg.2 t h5
  · have h := hv ⟨t - 5, by omega⟩
    have e : 5 + (t - 5) = t := by omega
    simp only [vR, Fin.val_mk, e] at h
    exact h

theorem keyR_facts :
    Nat.card RA = ER.card ∧ ∀ y ∈ GA 5, (fun i => y (vR i)) ∈ ER → y ∈ RA :=
  key_orbit rfl RA_le vR fixR_eq_one ER
    (mem_ER.2 (by rw [← subKey_tkey hvR]; exact recR.2.2.1 (by norm_num)))
    (by
      rintro e he _ ⟨j, rfl⟩
      have h := recR.2.2.2.1 _ (mem_ER.1 he) j j.2
      rw [rAct_tkey j.2] at h
      exact mem_ER.2 h)
    (by
      intro e he
      obtain ⟨r, hr, he'⟩ := reachR _ (recR.2.2.2.2 _ (mem_ER.1 he))
      exact ⟨r, hr, (tkey_inj (w := 12) (by norm_num) he').symm⟩)

theorem card_RA :
    Nat.card RA = 243 := by
  rw [keyR_facts.1, card_ER]

theorem conj_mem_RA
    {yp : ℕ} {y : Equiv.Perm (Fin 2300)} (hy : PRep 2300 12 yp y)
    (hn : normK 2300 12 4095 RGp 4 yp BA 5 5 RK = true) {j : ℕ} (hj : j < 4)
    (hK : y * rA j * y⁻¹ ∈ GA 5) : y * rA j * y⁻¹ ∈ RA := by
  obtain ⟨hp, hk⟩ := normK_sound hn
  have hyi := prep_inv hp hy
  have e := conjKey_tkey hy hyi (prepRG hj) hvR
  refine keyR_facts.2 _ hK (mem_ER.2 ?_)
  rw [← e]
  exact hk j hj

theorem tFacts : orbRecK tAct (fun e => e) 4 8 255 (pidn 2300 12) 32 TE TR = true ∧
    ncAllK 2300 12 4095 (pidn 2300 12) RGp 4 TE = true := by
  have h := ch17351_t
  simp only [bAnd_iff] at h
  exact h

theorem recT : TE.length = 32 ∧ (TE.map (fun e => e)).Nodup ∧ (0 < 32 → pidn 2300 12 ∈ TE) ∧
    (∀ e ∈ TE, ∀ j < 4, tAct j e ∈ TE) ∧ ∀ e ∈ TE, ActReach tAct 4 (pidn 2300 12) e :=
  orbRecK_sound tFacts.1

theorem prep_one : PRep 2300 12 (pidn 2300 12) 1 := prep_pidn (by norm_num) (by norm_num)

theorem reachT : ∀ e, ActReach tAct 4 (pidn 2300 12) e →
    ∃ t ∈ TA, PRep 2300 12 e t ∧ e >>> (2300 * 12) = 0 := by
  intro e he
  induction he with
  | root => exact ⟨1, one_mem _, prep_one, pidn_shr (by norm_num) (by norm_num)⟩
  | @step e j _ hj ih =>
    obtain ⟨t, ht, hp, -⟩ := ih
    exact ⟨tA j * t, mul_mem (subset_closure ⟨⟨j, hj⟩, rfl⟩) ht,
      prep_pcomp (by norm_num) (prepTG hj) hp, pcomp_shr _ _ (by norm_num) (by norm_num)⟩

@[expose] noncomputable def ET : Finset (Fin 2300 → Fin 2300) := (TE.map (decP 2300 12)).toFinset

theorem mem_ET {u : Fin 2300 → Fin 2300} : u ∈ ET ↔ ∃ p ∈ TE, decP 2300 12 p = u := by
  rw [ET, List.mem_toFinset, List.mem_map]

theorem ET_root : (fun i => i) ∈ ET :=
  mem_ET.2 ⟨_, recT.2.2.1 (by norm_num), by rw [decP_of_prep prep_one]; rfl⟩

theorem ET_clos : ∀ e ∈ ET, ∀ r ∈ Set.range (fun j : Fin 4 => tA j), (fun i => r (e i)) ∈ ET := by
  rintro e he _ ⟨j, rfl⟩
  obtain ⟨p, hp, rfl⟩ := mem_ET.1 he
  obtain ⟨t, -, hpr, -⟩ := reachT p (recT.2.2.2.2 p hp)
  refine mem_ET.2 ⟨tAct j p, recT.2.2.2.1 p hp j j.2, ?_⟩
  have hq : PRep 2300 12 (tAct j p) (tA j * t) := prep_pcomp (by norm_num) (prepTG j.2) hpr
  rw [decP_of_prep hq, decP_of_prep hpr]
  rfl

theorem card_ET : ET.card = 32 := by
  rw [ET, List.toFinset_card_of_nodup, List.length_map, recT.1]
  have hnd : TE.Nodup := by simpa using recT.2.1
  refine hnd.map_on fun p hp q hq he => ?_
  obtain ⟨t, -, hpt, hps⟩ := reachT p (recT.2.2.2.2 p hp)
  obtain ⟨s, -, hqs, hqs'⟩ := reachT q (recT.2.2.2.2 q hq)
  rw [decP_of_prep hpt, decP_of_prep hqs] at he
  have hts : t = s := Equiv.ext (congrFun he)
  rw [hts] at hpt
  exact eq_of_prep (by norm_num) hpt hqs hps hqs'

theorem keyT_facts : Nat.card TA = ET.card ∧ ∀ y ∈ GA 5, (fun i => y i) ∈ ET → y ∈ TA :=
  key_orbit rfl TA_le (fun i => i) (fun g _ h => Equiv.ext h) ET ET_root ET_clos (by
    intro e he
    obtain ⟨p, hp, rfl⟩ := mem_ET.1 he
    obtain ⟨t, ht, hpr, -⟩ := reachT p (recT.2.2.2.2 p hp)
    exact ⟨t, ht, by rw [decP_of_prep hpr]⟩)

theorem card_TA : Nat.card TA = 32 := by
  rw [keyT_facts.1, card_ET]

theorem TA_cent : ∀ t ∈ TA, t ∈ centralizer (RA : Set (Equiv.Perm (Fin 2300))) → t = 1 := by
  intro t ht htc
  have hTS : TA ≤ tupStab ET := by
    rw [TA, closure_le]
    rintro _ ⟨j, rfl⟩ e he
    exact ET_clos e he _ ⟨j, rfl⟩
  obtain ⟨p, hp, hpe⟩ := mem_ET.1 (hTS ht _ ET_root)
  obtain ⟨t', -, hpr, -⟩ := reachT p (recT.2.2.2.2 p hp)
  rw [decP_of_prep hpr] at hpe
  have htt : t' = t := Equiv.ext (congrFun hpe)
  rw [htt] at hpr
  by_cases hpid : p = pidn 2300 12
  · rw [hpid] at hpr
    exact prep_unique hpr prep_one
  · exfalso
    have hf := ncAllK_sound tFacts.2 p hp hpid
    have hall : allN 4 (fun j => commOK 2300 12 4095 p (RGp j)) = true :=
      allN_iff.2 fun j hj => (commOK_iff hpr (prepRG hj)).2
        ((mem_centralizer_iff.1 htc (rA j) (rA_mem_RA hj)).symm)
    rw [hall] at hf
    exact absurd hf (by decide)

theorem cFacts : wordEqK 2300 12 SA 16 65535 c1 (getLs W 0) = true ∧
    wordEqK 2300 12 SA 16 65535 c2 (getLs W 1) = true ∧
    wordEqK 2300 12 SA 16 65535 c5 (getLs W 2) = true ∧
    wordEqK 2300 12 SA 16 65535 g0 (getLs W 3) = true ∧
    commOK 2300 12 4095 c1 xA = true ∧ commOK 2300 12 4095 c2 xA = true ∧
    commOK 2300 12 4095 c5 xA = true ∧ (!(commOK 2300 12 4095 g0 xA)) = true ∧
    actFK 12 4095 c1 BA [1, 2, 0, 3, 4] = true ∧ actFK 12 4095 c2 BA [1, 2, 3, 4, 0] = true ∧
    actFK 12 4095 g0 BA [1, 0, 2, 3, 4] = true ∧ powIdK 2300 12 4095 c5 5 = true ∧
    movesK 2300 12 4095 c5 = true ∧
    (!(allN 4 (fun j => commOK 2300 12 4095 c5 (RGp j)))) = true := by
  have h := ch17351_c
  simp only [bAnd_iff] at h
  exact h

theorem nFacts : normK 2300 12 4095 RGp 4 c1 BA 5 5 RK = true ∧
    normK 2300 12 4095 RGp 4 c2 BA 5 5 RK = true ∧
    allN 16 (fun j => bIf(Nat.beq fld(getS MA 5, j, 1) 1,
      normK 2300 12 4095 RGp 4 (getS SA j) BA 5 5 RK, true)) = true := by
  have h := ch17351_n
  simp only [bAnd_iff] at h
  exact h

theorem act_F {cp : ℕ} {c : Equiv.Perm (Fin 2300)} (hc : PRep 2300 12 cp c) {img : List ℕ}
    (h : actFK 12 4095 cp BA img = true) (hl : img.length = 5) {σ : Equiv.Perm (Fin 5)}
    (hσ : ∀ t : Fin 5, getS img t = (σ t : ℕ)) : ∀ t, c (FA t) = FA (σ t) := by
  intro t
  apply Fin.ext
  have h1 := actFK_sound h (t := t) (by rw [hl]; exact t.2)
  have e : pg 12 4095 cp (getS BA t) = c (FA t) := hc (FA t)
  rw [e, hσ t] at h1
  exact h1

theorem img_c3 : ∀ t : Fin 5, getS [1, 2, 0, 3, 4] t = (c3 t : ℕ) := by decide

theorem img_rot : ∀ t : Fin 5, getS [1, 2, 3, 4, 0] t = (finRotate 5 t : ℕ) := by decide

theorem img_swap : ∀ t : Fin 5, getS [1, 0, 2, 3, 4] t = (Equiv.swap (0 : Fin 5) 1 t : ℕ) := by
  decide

theorem false_of_not {b : Bool} (h : (!b) = true) : b = false := by
  cases b
  · rfl
  · exact absurd h (by decide)

theorem caseA
    {x : Equiv.Perm (Fin 2300)} (hx : PRep 2300 12 xA x) :
    x ^ 3 = 1 ∧ x ≠ 1 ∧ Nat.card RA = 243 ∧ RA ≤ centP co2P x ∧
      (∀ g ∈ centP co2P x, ∀ r ∈ RA, g * r * g⁻¹ ∈ RA) ∧
      centralizer (RA : Set (Equiv.Perm (Fin 2300))) ⊓ centP co2P x ≤ RA := by
  obtain ⟨w1, w2, w5, w0, k1, k2, k5, k0, a1, a2, a0, p5, m5, n5⟩ := cFacts
  have r1 := word_rep w1
  have r2 := word_rep w2
  have r5 := word_rep w5
  have r0 := word_rep w0
  have hP1 := wv_mem_P r1.2
  have hP2 := wv_mem_P r2.2
  have hP5 := wv_mem_P r5.2
  have hP0 := wv_mem_P r0.2
  have hc1 : wv (getLs W 0) ∈ centP co2P x := mem_centP hP1 ((commOK_iff r1.1 hx).1 k1)
  have hc2 : wv (getLs W 1) ∈ centP co2P x := mem_centP hP2 ((commOK_iff r2.1 hx).1 k2)
  have hc5 : wv (getLs W 2) ∈ centP co2P x := mem_centP hP5 ((commOK_iff r5.1 hx).1 k5)
  have hg0x : wv (getLs W 3) * x ≠ x * wv (getLs W 3) := by
    intro h
    have := (commOK_iff r0.1 hx).2 h
    have hk : commOK 2300 12 (mask 12) g0 xA = false := false_of_not k0
    rw [hk] at this
    exact absurd this (by decide)
  have hKC : GA 5 ≤ centP co2P x := fun g hg => mem_centP (GA_le 5 hg) (K_comm hx g hg)
  have h5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hc5o : orderOf (wv (getLs W 2)) = 5 :=
    orderOf_eq_prime (pow_eq_one_of_powIdK p5 r5.1) (ne_one_of_movesK m5 r5.1)
  have hc5R : wv (getLs W 2) ∉ centralizer (RA : Set (Equiv.Perm (Fin 2300))) := by
    intro hcent
    have hall : allN 4 (fun j => commOK 2300 12 4095 c5 (RGp j)) = true :=
      allN_iff.2 fun j hj => (commOK_iff r5.1 (prepRG hj)).2
        ((mem_centralizer_iff.1 hcent (rA j) (rA_mem_RA hj)).symm)
    rw [hall] at n5
    exact absurd n5 (by decide)
  obtain ⟨nc1, nc2, nK⟩ := nFacts
  have hnorm : ∀ y ∈ ({wv (getLs W 0), wv (getLs W 1)} ∪
      sA '' {j | lvOk 16 (getS MA 5) j} : Set (Equiv.Perm (Fin 2300))),
      ∀ r ∈ Set.range (fun j : Fin 4 => rA j), y * r * y⁻¹ ∈ RA := by
    rintro y hy _ ⟨⟨j, hj⟩, rfl⟩
    rcases hy with (rfl | rfl) | ⟨l, hl, rfl⟩
    · exact conj_mem_RA r1.1 nc1 hj (conj_K hx hc1 (rA_mem hj))
    · exact conj_mem_RA r2.1 nc2 hj (conj_K hx hc2 (rA_mem hj))
    · obtain ⟨hl1, hl2⟩ := lvOk_iff.1 hl
      have h := allN_spec nK l hl1
      beta_reduce at h
      have e : Nat.beq fld(getS MA 5, l, 1) 1 = true := testBit_iff_fld.2 hl2
      rw [e] at h
      exact conj_mem_RA (prepA hl1) h hj
        ((GA 5).mul_mem ((GA 5).mul_mem (sA_mem_GA hl) (rA_mem hj)) ((GA 5).inv_mem (sA_mem_GA hl)))
  have hres := caseA_perm FA_inj (fixA hx) memK_iff (K_comm hx) rfl hc1 hc2
    (act_F r1.1 a1 rfl img_c3) (act_F r2.1 a2 rfl img_rot) hP0 (act_F r0.1 a0 rfl img_swap) hg0x
    rfl RA_le hnorm (card_GA5.trans (by norm_num)) (card_RA.trans (by norm_num)) TA_le
    (card_TA.trans (by norm_num)) TA_cent hc5 hc5o hc5R
  exact ⟨pow_eq_one_of_powIdK xFacts.2.1 hx, ne_one_of_movesK xFacts.2.2.1 hx, card_RA,
    RA_le.trans hKC, hres.1, hres.2⟩

end CertificateChecks.KernelCo2Cent

end
