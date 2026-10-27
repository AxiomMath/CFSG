module

public import Certificates.Kernel.Co3Cent.CaseBGlue

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo3Cent

open CFSG.KC.Enum CFSG.KC.OrbRow CFSG.KC.OrbRow.CentGrp CFSG.KC.PGrp CFSG.KS CFSG.KS.Raw
  CFSG.KS.Raw.Orb CFSG.KS.PF CFSG.KD.Co3Cent Subgroup
open CFSG.KC.Misc.ArrEnum (permB)
open CFSG.Sporadic.Schreier.Co3 CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co3T

@[expose] noncomputable def CB : Subgroup (Equiv.Perm (Fin 276)) := centralizer {xB} ⊓ co3P

theorem mem_CB {g : Equiv.Perm (Fin 276)} : g ∈ CB ↔ g * xB = xB * g ∧ g ∈ co3P := by
  rw [CB, Subgroup.mem_inf, mem_centralizer_singleton_iff]

theorem inCB_mem {g : ℕ}
    (h : inCB g = true) : permB 276 9 g = true ∧ pv g ∈ CB := by
  obtain ⟨hp, hP, hc⟩ := inC_spec permXB h
  exact ⟨hp, mem_CB.2 ⟨hc, hP⟩⟩

@[expose] noncomputable def HBg : Subgroup (Equiv.Perm (Fin 276)) := Gv SHB MHB 12 0

theorem cHB : allN 12 (fun j => commOK 276 9 511 (getS SHB j) xBp) = true := by
  have h := ch17370_c
  simp only [bAnd_iff] at h
  exact h.2

theorem shb_facts {j : ℕ}
    (hj : j < 12) : permB 276 9 (getS SHB j) = true ∧ sv SHB j ∈ CB := by
  have hp := permS sFacts.2.2.2 j hj
  have hc : commOK 276 9 (mask 9) (getS SHB j) xBp = true := allN_spec cHB j hj
  exact ⟨hp, mem_CB.2 ⟨(commOK_iff (prep_pv hp) prepXB).1 hc, pv_mem (allN_spec sFacts.2.2.2 j hj)⟩⟩

theorem HBg_le : HBg ≤ CB := by
  rw [HBg, Gv, closure_le]
  rintro _ ⟨j, hj, rfl⟩
  exact (shb_facts (lvOk_iff.1 hj).1).2

theorem C_eq
    (hC : Nat.card CB ≤ 29160) : HBg = CB :=
  Subgroup.eq_of_le_of_card_ge HBg_le (hC.trans card_HB)

theorem dnFacts : allN 12 (fun j => normK 276 9 511 DGp 5 (getS SHB j) KPB 0 7 DK) = true ∧
    normK 276 9 511 DGp 5 C3 KPB 0 7 DK = true := by
  have h := ch17370_dn
  simp only [bAnd_iff] at h
  exact h

theorem DB_norm
    (hC : Nat.card CB ≤ 29160) : ∀ g ∈ CB, ∀ r ∈ DB, g * r * g⁻¹ ∈ DB := by
  rw [← C_eq hC]
  refine conj_mem_of_closure DB_eq ?_
  rintro _ ⟨j, hj, rfl⟩ _ ⟨l, rfl⟩
  have hj12 := (lvOk_iff.1 hj).1
  obtain ⟨hp, hCj⟩ := shb_facts hj12
  have hPj := (mem_CB.1 hCj).2
  exact conj_mem_DB (prep_pv hp) (allN_spec dnFacts.1 j hj12) l.2
    (co3P.mul_mem (co3P.mul_mem hPj (dv_facts l.2).1) (co3P.inv_mem hPj))

@[expose] noncomputable def tB (j : ℕ) : Equiv.Perm (Fin 276) := pv (getS TGB j)

@[expose] noncomputable def TB : Subgroup (Equiv.Perm (Fin 276)) :=
  closure (Set.range fun j : Fin 2 => tB j)

theorem tbFacts : orbRecK tActB (fun e => e) 2 8 255 (pidn 276 9) 8 TEB TRB = true ∧
    allN 2 (fun j => inCB (getS TGB j)) = true ∧ ncAllK 276 9 511 (pidn 276 9) DGp 5 TEB = true := by
  have h := ch17370_tb
  simp only [bAnd_iff] at h
  exact h

theorem tB_facts {j : ℕ}
    (hj : j < 2) : permB 276 9 (getS TGB j) = true ∧ tB j ∈ CB :=
  inCB_mem (allN_spec tbFacts.2.1 j hj)

theorem TB_le : TB ≤ CB := by
  rw [TB, closure_le]
  rintro _ ⟨j, rfl⟩
  exact (tB_facts j.2).2

theorem permC {g : ℕ} (h : inCB g = true) : permB 276 9 g = true :=
  (inP3K_spec ((bAnd_iff _ _).1 h).1).1

theorem prepTB {j : ℕ} (hj : j < 2) : PRep 276 9 (getS TGB j) (tB j) :=
  prep_pv (permC (allN_spec tbFacts.2.1 j hj))

theorem recT : TEB.length = 8 ∧ (TEB.map (fun e => e)).Nodup ∧ (0 < 8 → pidn 276 9 ∈ TEB) ∧
    (∀ e ∈ TEB, ∀ j < 2, tActB j e ∈ TEB) ∧ ∀ e ∈ TEB, ActReach tActB 2 (pidn 276 9) e :=
  orbRecK_sound tbFacts.1

theorem prep_one : PRep 276 9 (pidn 276 9) 1 := prep_pidn (by norm_num) (by norm_num)

theorem reachT : ∀ e, ActReach tActB 2 (pidn 276 9) e →
    ∃ t ∈ TB, PRep 276 9 e t ∧ e >>> (276 * 9) = 0 := by
  intro e he
  induction he with
  | root => exact ⟨1, one_mem _, prep_one, pidn_shr (by norm_num) (by norm_num)⟩
  | @step e j _ hj ih =>
    obtain ⟨t, ht, hp, -⟩ := ih
    exact ⟨tB j * t, mul_mem (subset_closure ⟨⟨j, hj⟩, rfl⟩) ht,
      prep_pcomp (by norm_num) (prepTB hj) hp, pcomp_shr _ _ (by norm_num) (by norm_num)⟩

@[expose] noncomputable def ET : Finset (Fin 276 → Fin 276) := (TEB.map (decP 276 9)).toFinset

theorem mem_ET {u : Fin 276 → Fin 276} : u ∈ ET ↔ ∃ p ∈ TEB, decP 276 9 p = u := by
  rw [ET, List.mem_toFinset, List.mem_map]

theorem ET_root : (fun i => i) ∈ ET :=
  mem_ET.2 ⟨_, recT.2.2.1 (by norm_num), by rw [decP_of_prep prep_one]; rfl⟩

theorem ET_clos : ∀ e ∈ ET, ∀ r ∈ Set.range (fun j : Fin 2 => tB j), (fun i => r (e i)) ∈ ET := by
  rintro e he _ ⟨j, rfl⟩
  obtain ⟨p, hp, rfl⟩ := mem_ET.1 he
  obtain ⟨t, -, hpr, -⟩ := reachT p (recT.2.2.2.2 p hp)
  refine mem_ET.2 ⟨tActB j p, recT.2.2.2.1 p hp j j.2, ?_⟩
  have hq : PRep 276 9 (tActB j p) (tB j * t) := prep_pcomp (by norm_num) (prepTB j.2) hpr
  rw [decP_of_prep hq, decP_of_prep hpr]
  rfl

theorem card_ET : ET.card = 8 := by
  rw [ET, List.toFinset_card_of_nodup, List.length_map, recT.1]
  have hnd : TEB.Nodup := by simpa using recT.2.1
  refine hnd.map_on fun p hp q hq he => ?_
  obtain ⟨t, -, hpt, hps⟩ := reachT p (recT.2.2.2.2 p hp)
  obtain ⟨s, -, hqs, hqs'⟩ := reachT q (recT.2.2.2.2 q hq)
  rw [decP_of_prep hpt, decP_of_prep hqs] at he
  have hts : t = s := Equiv.ext (congrFun he)
  rw [hts] at hpt
  exact eq_of_prep (by norm_num) hpt hqs hps hqs'

theorem keyT_facts : Nat.card TB = ET.card ∧ ∀ y ∈ (⊤ : Subgroup (Equiv.Perm (Fin 276))),
    (fun i => y i) ∈ ET → y ∈ TB :=
  key_orbit rfl le_top (fun i => i) (fun g _ h => Equiv.ext h) ET ET_root ET_clos (by
    intro e he
    obtain ⟨p, hp, rfl⟩ := mem_ET.1 he
    obtain ⟨t, ht, hpr, -⟩ := reachT p (recT.2.2.2.2 p hp)
    exact ⟨t, ht, by rw [decP_of_prep hpr]⟩)

theorem card_TB : Nat.card TB = 8 := by
  rw [keyT_facts.1, card_ET]

theorem TB_cent : ∀ t ∈ TB, (∀ d ∈ DB, d * t = t * d) → t = 1 := by
  intro t ht htc
  have hTS : TB ≤ tupStab ET := by
    rw [TB, closure_le]
    rintro _ ⟨j, rfl⟩ e he
    exact ET_clos e he _ ⟨j, rfl⟩
  obtain ⟨p, hp, hpe⟩ := mem_ET.1 (hTS ht _ ET_root)
  obtain ⟨t', -, hpr, -⟩ := reachT p (recT.2.2.2.2 p hp)
  rw [decP_of_prep hpr] at hpe
  have htt : t' = t := Equiv.ext (congrFun hpe)
  rw [htt] at hpr
  by_cases hpid : p = pidn 276 9
  · rw [hpid] at hpr
    exact CFSG.KC.OrbRow.prep_unique hpr prep_one
  · exfalso
    have hf := ncAllK_sound tbFacts.2.2 p hp hpid
    have hall : allN 5 (fun j => commOK 276 9 (mask 9) p (DGp j)) = true :=
      allN_iff.2 fun j hj => (commOK_iff hpr (prepD hj)).2 (htc _ (dv_mem_DB hj)).symm
    have hall' : allN 5 (fun j => commOK 276 9 511 p (DGp j)) = true := hall
    rw [hall'] at hf
    exact absurd hf (by decide)

theorem c5Facts : inCB C5B = true ∧ powIdK 276 9 511 C5B 5 = true ∧ movesK 276 9 511 C5B = true ∧
    (!(allN 5 (fun j => commOK 276 9 511 C5B (DGp j)))) = true := by
  have h := ch17370_c5b
  simp only [bAnd_iff] at h
  exact h

theorem c3Facts : inCB C3 = true ∧ powIdK 276 9 511 C3 3 = true ∧
    (!(allN 5 (fun j => commOK 276 9 511 C3 (DGp j)))) = true := by
  have h := ch17370_c3
  simp only [bAnd_iff] at h
  exact h

theorem false_of_not {b : Bool} (h : (!b) = true) : b = false := by
  cases b
  · rfl
  · exact absurd h (by decide)

theorem not_cent {cp : ℕ} (hp : permB 276 9 cp = true)
    (h : (!(allN 5 (fun j => commOK 276 9 511 cp (DGp j)))) = true) :
    ∃ j < 5, pv cp * dv j ≠ dv j * pv cp := by
  by_contra hcon
  push Not at hcon
  have hall : allN 5 (fun j => commOK 276 9 (mask 9) cp (DGp j)) = true :=
    allN_iff.2 fun j hj => (commOK_iff (prep_pv hp) (prepD hj)).2 (hcon j hj)
  have hall' : allN 5 (fun j => commOK 276 9 511 cp (DGp j)) = true := hall
  rw [false_of_not h] at hall'
  exact absurd hall' (by decide)

theorem DB_cent
    (hC : Nat.card CB ≤ 29160) : centralizer (DB : Set (Equiv.Perm (Fin 276))) ⊓ CB ≤ DB := by
  have hCc : Nat.card CB = 29160 := le_antisymm hC (card_HB.trans (Subgroup.card_le_of_le HBg_le))
  have hDC : DB ≤ CB := DB_le
  set D' : Subgroup CB := DB.subgroupOf CB
  have hD'n : D'.Normal := ⟨fun n hn g => by
    rw [mem_subgroupOf] at hn ⊢
    exact DB_norm hC g g.2 n hn⟩
  set N : Subgroup CB := centralizer (D' : Set CB)
  have hNn : N.Normal := centralizer_normal D'
  have hD' : Nat.card D' = 3 ^ 5 := by
    rw [← (by norm_num : (243 : ℕ) = 3 ^ 5), ← card_DB]
    exact Nat.card_congr (subgroupOfEquivOfLe hDC).toEquiv
  set T' : Subgroup CB := TB.subgroupOf CB
  have hT' : Nat.card T' = 2 ^ 3 := by
    rw [← (by norm_num : (8 : ℕ) = 2 ^ 3), ← card_TB]
    exact Nat.card_congr (subgroupOfEquivOfLe TB_le).toEquiv
  have hTN : ∀ t ∈ T', t ∈ N → t = 1 := by
    intro t ht htN
    refine Subtype.ext (TB_cent _ (mem_subgroupOf.1 ht) fun d hd => ?_)
    exact congrArg Subtype.val (mem_centralizer_iff.1 htN ⟨d, hDC hd⟩ (mem_subgroupOf.2 hd))
  obtain ⟨c5C, p5, m5, n5⟩ := c5Facts
  obtain ⟨hp5, hc5C⟩ := inCB_mem c5C
  have hc5o : orderOf (⟨pv C5B, hc5C⟩ : CB) = 5 := by
    rw [← orderOf_injective CB.subtype CB.subtype_injective]
    exact orderOf_eq_prime (pow_eq_one_of_powIdK p5 (prep_pv hp5)) (ne_one_of_movesK m5 (prep_pv hp5))
  have hc5N : (⟨pv C5B, hc5C⟩ : CB) ∉ N := by
    intro hc
    obtain ⟨j, hj, hne⟩ := not_cent hp5 n5
    exact hne (congrArg Subtype.val
      (mem_centralizer_iff.1 hc ⟨dv j, hDC (dv_mem_DB hj)⟩ (mem_subgroupOf.2 (dv_mem_DB hj)))).symm
  have hN3 : Nat.card N ∣ 3 ^ 6 :=
    CFSG.KC.Co3Cent.card_dvd_of_two_five N (a := 3) (by rw [hCc]; norm_num) T' hT' hTN hc5o hc5N
  obtain ⟨c3C, p3, n3⟩ := c3Facts
  obtain ⟨hp3, hc3C⟩ := inCB_mem c3C
  have hc3 : (⟨pv C3, hc3C⟩ : CB) ^ 3 = 1 := Subtype.ext (by
    rw [SubgroupClass.coe_pow]
    exact pow_eq_one_of_powIdK p3 (prep_pv hp3))
  have hcD : ∃ d ∈ D', (⟨pv C3, hc3C⟩ : CB) * d ≠ d * ⟨pv C3, hc3C⟩ := by
    obtain ⟨j, hj, hne⟩ := not_cent hp3 n3
    exact ⟨⟨dv j, hDC (dv_mem_DB hj)⟩, mem_subgroupOf.2 (dv_mem_DB hj),
      fun he => hne (congrArg Subtype.val he)⟩
  have hDab : ∀ a ∈ D', ∀ d ∈ D', a * d = d * a := fun a ha d hd =>
    Subtype.ext (DB_ab _ (mem_subgroupOf.1 ha) _ (mem_subgroupOf.1 hd))
  have hNc : ∀ n ∈ N, ∀ d ∈ D', n * d = d * n := fun n hn d hd =>
    (mem_centralizer_iff.1 hn d hd).symm
  have hle := CFSG.KC.Co3Cent.cent_le_of_index3 D' N (b := 5) (m := 40) (by rw [hCc]; norm_num)
    (by norm_num) hD' hDab hc3 hcD hN3 hNc
  intro g hg
  obtain ⟨hgc, hgC⟩ := Subgroup.mem_inf.1 hg
  have hgN : (⟨g, hgC⟩ : CB) ∈ N := mem_centralizer_iff.2 fun d hd =>
    Subtype.ext (mem_centralizer_iff.1 hgc _ (mem_subgroupOf.1 hd))
  exact mem_subgroupOf.1 (hle hgN)

end CertificateChecks.KernelCo3Cent

end
