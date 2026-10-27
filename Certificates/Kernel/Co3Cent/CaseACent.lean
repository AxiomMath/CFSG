module

public import Certificates.Kernel.Co3Cent.CaseABound
public import Certificates.Kernel.Co3Cent.CaseBCent

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo3Cent

open CFSG.KC.Enum CFSG.KC.OrbRow CFSG.KC.OrbRow.CentGrp CFSG.KC.PGrp CFSG.KS CFSG.KS.Raw
  CFSG.KS.Raw.Orb CFSG.KS.PF CFSG.KD.Co3Cent Subgroup
open CFSG.KC.Misc.ArrEnum (permB)
open CFSG.Sporadic.Schreier.Co3 CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co3T

theorem inCA_mem {g : ℕ}
    (h : inCA g = true) : permB 276 9 g = true ∧ pv g ∈ CA := by
  obtain ⟨hp, hP, hc⟩ := inC_spec permXA h
  exact ⟨hp, mem_CA.2 ⟨hc, hP⟩⟩

theorem permCA {g : ℕ} (h : inCA g = true) : permB 276 9 g = true :=
  (inP3K_spec ((bAnd_iff _ _).1 h).1).1

@[expose] noncomputable def tA (j : ℕ) : Equiv.Perm (Fin 276) := pv (getS TG j)

@[expose] noncomputable def TA : Subgroup (Equiv.Perm (Fin 276)) :=
  closure (Set.range fun j : Fin 3 => tA j)

theorem taFacts : orbRecK tActA (fun e => e) 3 8 255 (pidn 276 9) 32 TE TR = true ∧
    allN 3 (fun j => inCA (getS TG j)) = true ∧ ncAllK 276 9 511 (pidn 276 9) RGp 5 TE = true := by
  have h := ch17370_ta
  simp only [bAnd_iff] at h
  exact h

theorem TA_le : TA ≤ CA := by
  rw [TA, closure_le]
  rintro _ ⟨j, rfl⟩
  exact (inCA_mem (allN_spec taFacts.2.1 j j.2)).2

theorem prepTA {j : ℕ} (hj : j < 3) : PRep 276 9 (getS TG j) (tA j) :=
  prep_pv (permCA (allN_spec taFacts.2.1 j hj))

theorem recTA : TE.length = 32 ∧ (TE.map (fun e => e)).Nodup ∧ (0 < 32 → pidn 276 9 ∈ TE) ∧
    (∀ e ∈ TE, ∀ j < 3, tActA j e ∈ TE) ∧ ∀ e ∈ TE, ActReach tActA 3 (pidn 276 9) e :=
  orbRecK_sound taFacts.1

theorem reachTA : ∀ e, ActReach tActA 3 (pidn 276 9) e →
    ∃ t ∈ TA, PRep 276 9 e t ∧ e >>> (276 * 9) = 0 := by
  intro e he
  induction he with
  | root => exact ⟨1, one_mem _, prep_one, pidn_shr (by norm_num) (by norm_num)⟩
  | @step e j _ hj ih =>
    obtain ⟨t, ht, hp, -⟩ := ih
    exact ⟨tA j * t, mul_mem (subset_closure ⟨⟨j, hj⟩, rfl⟩) ht,
      prep_pcomp (by norm_num) (prepTA hj) hp, pcomp_shr _ _ (by norm_num) (by norm_num)⟩

@[expose] noncomputable def ETA : Finset (Fin 276 → Fin 276) := (TE.map (decP 276 9)).toFinset

theorem mem_ETA {u : Fin 276 → Fin 276} : u ∈ ETA ↔ ∃ p ∈ TE, decP 276 9 p = u := by
  rw [ETA, List.mem_toFinset, List.mem_map]

theorem ETA_root : (fun i => i) ∈ ETA :=
  mem_ETA.2 ⟨_, recTA.2.2.1 (by norm_num), by rw [decP_of_prep prep_one]; rfl⟩

theorem ETA_clos : ∀ e ∈ ETA, ∀ r ∈ Set.range (fun j : Fin 3 => tA j), (fun i => r (e i)) ∈ ETA := by
  rintro e he _ ⟨j, rfl⟩
  obtain ⟨p, hp, rfl⟩ := mem_ETA.1 he
  obtain ⟨t, -, hpr, -⟩ := reachTA p (recTA.2.2.2.2 p hp)
  refine mem_ETA.2 ⟨tActA j p, recTA.2.2.2.1 p hp j j.2, ?_⟩
  have hq : PRep 276 9 (tActA j p) (tA j * t) := prep_pcomp (by norm_num) (prepTA j.2) hpr
  rw [decP_of_prep hq, decP_of_prep hpr]
  rfl

theorem card_ETA : ETA.card = 32 := by
  rw [ETA, List.toFinset_card_of_nodup, List.length_map, recTA.1]
  have hnd : TE.Nodup := by simpa using recTA.2.1
  refine hnd.map_on fun p hp q hq he => ?_
  obtain ⟨t, -, hpt, hps⟩ := reachTA p (recTA.2.2.2.2 p hp)
  obtain ⟨s, -, hqs, hqs'⟩ := reachTA q (recTA.2.2.2.2 q hq)
  rw [decP_of_prep hpt, decP_of_prep hqs] at he
  have hts : t = s := Equiv.ext (congrFun he)
  rw [hts] at hpt
  exact eq_of_prep (by norm_num) hpt hqs hps hqs'

theorem card_TA : Nat.card TA = 32 := by
  have h := key_orbit (K := ⊤) rfl le_top (fun i => i) (fun g _ h => Equiv.ext h) ETA ETA_root
    ETA_clos (by
      intro e he
      obtain ⟨p, hp, rfl⟩ := mem_ETA.1 he
      obtain ⟨t, ht, hpr, -⟩ := reachTA p (recTA.2.2.2.2 p hp)
      exact ⟨t, ht, by rw [decP_of_prep hpr]⟩)
  have h1 : Nat.card TA = ETA.card := h.1
  rw [h1, card_ETA]

theorem TA_cent : ∀ t ∈ TA, (∀ r ∈ RA, r * t = t * r) → t = 1 := by
  intro t ht htc
  have hTS : TA ≤ tupStab ETA := by
    rw [TA, closure_le]
    rintro _ ⟨j, rfl⟩ e he
    exact ETA_clos e he _ ⟨j, rfl⟩
  obtain ⟨p, hp, hpe⟩ := mem_ETA.1 (hTS ht _ ETA_root)
  obtain ⟨t', -, hpr, -⟩ := reachTA p (recTA.2.2.2.2 p hp)
  rw [decP_of_prep hpr] at hpe
  have htt : t' = t := Equiv.ext (congrFun hpe)
  rw [htt] at hpr
  by_cases hpid : p = pidn 276 9
  · rw [hpid] at hpr
    exact CFSG.KC.OrbRow.prep_unique hpr prep_one
  · exfalso
    have hf := ncAllK_sound taFacts.2.2 p hp hpid
    have hall : allN 5 (fun j => commOK 276 9 (mask 9) p (RGp j)) = true :=
      allN_iff.2 fun j hj => (commOK_iff hpr (prepRG hj)).2 (htc _ (rv_mem_RA hj)).symm
    have hall' : allN 5 (fun j => commOK 276 9 511 p (RGp j)) = true := hall
    rw [hall'] at hf
    exact absurd hf (by decide)

theorem c5aFacts : inCA C5 = true ∧ powIdK 276 9 511 C5 5 = true ∧ movesK 276 9 511 C5 = true ∧
    (!(allN 5 (fun j => commOK 276 9 511 C5 (RGp j)))) = true := by
  have h := ch17370_c5
  simp only [bAnd_iff] at h
  exact h

theorem not_centR {cp : ℕ} (hp : permB 276 9 cp = true)
    (h : (!(allN 5 (fun j => commOK 276 9 511 cp (RGp j)))) = true) :
    ∃ j < 5, pv cp * rv j ≠ rv j * pv cp := by
  by_contra hcon
  push Not at hcon
  have hall : allN 5 (fun j => commOK 276 9 (mask 9) cp (RGp j)) = true :=
    allN_iff.2 fun j hj => (commOK_iff (prep_pv hp) (prepRG hj)).2 (hcon j hj)
  have hall' : allN 5 (fun j => commOK 276 9 511 cp (RGp j)) = true := hall
  rw [false_of_not h] at hall'
  exact absurd hall' (by decide)

theorem cent_dvd :
    Nat.card (centralizer ((RA.subgroupOf CA : Subgroup CA) : Set CA)) ∣ 3 ^ 7 := by
  have hRC : RA ≤ CA := RA_C
  set R' : Subgroup CA := RA.subgroupOf CA
  have hR'n : R'.Normal := ⟨fun n hn g => by
    rw [mem_subgroupOf] at hn ⊢
    exact RA_norm g g.2 n hn⟩
  set N : Subgroup CA := centralizer (R' : Set CA)
  have hNn : N.Normal := centralizer_normal R'
  set T' : Subgroup CA := TA.subgroupOf CA
  have hT' : Nat.card T' = 2 ^ 5 := by
    rw [← (by norm_num : (32 : ℕ) = 2 ^ 5), ← card_TA]
    exact Nat.card_congr (subgroupOfEquivOfLe TA_le).toEquiv
  have hTN : ∀ t ∈ T', t ∈ N → t = 1 := by
    intro t ht htN
    refine Subtype.ext (TA_cent _ (mem_subgroupOf.1 ht) fun r hr => ?_)
    exact congrArg Subtype.val (mem_centralizer_iff.1 htN ⟨r, hRC hr⟩ (mem_subgroupOf.2 hr))
  obtain ⟨c5C, p5, m5, n5⟩ := c5aFacts
  obtain ⟨hp5, hc5C⟩ := inCA_mem c5C
  have hc5o : orderOf (⟨pv C5, hc5C⟩ : CA) = 5 := by
    rw [← orderOf_injective CA.subtype CA.subtype_injective]
    exact orderOf_eq_prime (pow_eq_one_of_powIdK p5 (prep_pv hp5)) (ne_one_of_movesK m5 (prep_pv hp5))
  have hc5N : (⟨pv C5, hc5C⟩ : CA) ∉ N := by
    intro hc
    obtain ⟨j, hj, hne⟩ := not_centR hp5 n5
    exact hne (congrArg Subtype.val
      (mem_centralizer_iff.1 hc ⟨rv j, hRC (rv_mem_RA hj)⟩ (mem_subgroupOf.2 (rv_mem_RA hj)))).symm
  exact CFSG.KC.Co3Cent.card_dvd_of_two_five N (a := 5) (by rw [card_CA_eq]; norm_num) T' hT' hTN
    hc5o hc5N

theorem zMul_cases {a b : ℕ} {g h : Equiv.Perm (Fin 276)} (ha : PRep 276 9 a g)
    (hb : PRep 276 9 b h) (hz : zMulAK a b = true) :
    g = h ∨ g = xA * h ∨ g = xA * (xA * h) := by
  unfold zMulAK at hz
  simp only [bIf_eq] at hz
  split_ifs at hz with h1 h2
  · left
    have hb' : PRep 276 9 a h := by rw [Nat.eq_of_beq_eq_true h1]; exact hb
    exact CFSG.KC.OrbRow.prep_unique ha hb'
  · right
    left
    have hb' : PRep 276 9 a (xA * h) := by
      rw [Nat.eq_of_beq_eq_true h2]
      exact prep_pcomp (by norm_num) prepXA hb
    exact CFSG.KC.OrbRow.prep_unique ha hb'
  · right
    right
    have hb' : PRep 276 9 a (xA * (xA * h)) := by
      rw [Nat.eq_of_beq_eq_true hz]
      exact prep_pcomp (by norm_num) prepXA (prep_pcomp (by norm_num) prepXA hb)
    exact CFSG.KC.OrbRow.prep_unique ha hb'

theorem comm_R :
    ∀ a ∈ RA, ∀ b ∈ RA, a * b * a⁻¹ * b⁻¹ ∈ zpowers xA := by
  have hZ : ∀ z ∈ zpowers xA, ∀ g ∈ closure (Set.range fun j : Fin 5 => rv j), z * g = g * z := by
    intro z hz g hg
    rw [← RA_eq] at hg
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hz
    have hc : Commute xA g := ((mem_CA.1 (RA_C hg)).1).symm
    exact (hc.zpow_left k).eq
  have hY : ∀ a ∈ Set.range (fun j : Fin 5 => rv j), ∀ b ∈ Set.range (fun j : Fin 5 => rv j),
      a * b * a⁻¹ * b⁻¹ ∈ zpowers xA := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    have hz := allN_spec (allN_spec raFacts.2 i i.2) j j.2
    have h1 := prep_pcomp (n := 276) (by norm_num) (prepRG i.2) (prepRG j.2)
    have h2 := prep_pcomp (n := 276) (by norm_num) (prepRG j.2) (prepRG i.2)
    have e : rv i * rv j * (rv i)⁻¹ * (rv j)⁻¹ = (rv i * rv j) * (rv j * rv i)⁻¹ := by group
    rw [e]
    rcases zMul_cases h1 h2 hz with h | h | h <;> rw [h]
    · rw [mul_inv_cancel]
      exact one_mem _
    · rw [mul_inv_cancel_right]
      exact mem_zpowers xA
    · rw [← mul_assoc, mul_inv_cancel_right, ← pow_two]
      exact pow_mem (mem_zpowers xA) 2
  intro a ha b hb
  rw [RA_eq] at ha hb
  exact CFSG.KC.Co3Cent.comm_mem_of_gens hZ hY a ha b hb

end CertificateChecks.KernelCo3Cent

end
