module

public import Certificates.Kernel.Co3Cent.CaseACent

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo3Cent

open CFSG.KC.Enum CFSG.KC.OrbRow CFSG.KC.OrbRow.CentGrp CFSG.KC.PGrp CFSG.KS CFSG.KS.Raw
  CFSG.KS.Raw.Orb CFSG.KS.PF CFSG.KD.Co3Cent Subgroup
open CFSG.KC.Misc.ArrEnum (permB)
open CFSG.RankThree.Native (permsA)
open CFSG.Sporadic.Schreier.Co3 CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co3T
open CFSG.HardMathSupport.Dickson.I271.Co3Cent (rGens)

theorem prep_upw {p : ℕ} {g : Equiv.Perm (Fin 276)} (h : PRep 276 9 p g) :
    ∀ e, PRep 276 9 (upw p e) (g ^ e)
  | 0 => by
    rw [pow_zero]
    exact prep_one
  | e + 1 => by
    rw [pow_succ']
    exact prep_pcomp (by norm_num) h (prep_upw h e)

theorem prep_of_pcomp {P Q R : ℕ} {g h : Equiv.Perm (Fin 276)} (hR : PRep 276 9 R g)
    (hQ : PRep 276 9 Q h) (he : R = pcomp 276 9 511 P Q) : PRep 276 9 P (g * h⁻¹) := by
  intro x
  subst he
  have h1 := hR (h⁻¹ x)
  have h2 := CFSG.KS.PF.pg_pcomp (n := 276) (w := 9) (p := P) (q := Q) (by norm_num) (h⁻¹ x).2
  have h3 : pg 9 (mask 9) P (pg 9 (mask 9) Q (h⁻¹ x)) = g (h⁻¹ x) := h2.symm.trans h1
  have e : h (h⁻¹ x) = x := h.apply_symm_apply x
  rw [hQ (h⁻¹ x), e] at h3
  rw [Equiv.Perm.mul_apply]
  exact h3

theorem memR_of {yp : ℕ}
    {y : Equiv.Perm (Fin 276)} (hp : PRep 276 9 yp y) (hP : y ∈ co3P) (hf : fixFA yp = true)
    (hk : memK (mapKey 9 511 yp 5 (subKey 9 BA 6 5)) RK = true) : y ∈ RA := by
  refine keyR_facts.2 _ ((memK_iff _).2 ⟨hP, fun t => ?_⟩) (mem_ER.2 ?_)
  · unfold fixFA at hf
    have h1 := allN_spec hf t t.2
    rw [strictB_apply] at h1
    apply Fin.ext
    rw [← (hp (FA t))]
    exact Nat.eq_of_beq_eq_true h1
  · have h := memK_sound hk
    rw [subKey_tkey hvR] at h
    have e := mapKey_tkey (n := 276) (w := 9) (by norm_num) hp vR
    change mapKey 9 511 yp 5 (tkey 9 vR) = _ at e
    rw [← e]
    exact h

theorem zcases
    {g h : Equiv.Perm (Fin 276)} (hz : g * h⁻¹ ∈ zpowers xA) :
    g = h ∨ g = xA * h ∨ g = xA * (xA * h) := by
  obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).1 (mem_powers_iff_mem_zpowers.2 hz)
  rw [CFSG.KC.Co3Cent.pow_mod3 xA_pow] at hn
  have hg : g = xA ^ (n % 3) * h := by rw [hn, inv_mul_cancel_right]
  have h3 : n % 3 < 3 := Nat.mod_lt _ (by norm_num)
  generalize n % 3 = m at hg h3
  interval_cases m
  · left
    rw [hg, pow_zero, one_mul]
  · right
    left
    rw [hg, pow_one]
  · right
    right
    rw [hg, pow_two, mul_assoc]

theorem zMulAK_of {a b : ℕ} {g h : Equiv.Perm (Fin 276)} (ha : PRep 276 9 a g)
    (hb : PRep 276 9 b h) (hsa : a >>> (276 * 9) = 0) (hsb : b >>> (276 * 9) = 0)
    (hz : g = h ∨ g = xA * h ∨ g = xA * (xA * h)) : zMulAK a b = true := by
  unfold zMulAK
  simp only [bIf_eq]
  rcases hz with rfl | rfl | rfl
  · have ea := eq_of_prep (by norm_num) ha hb hsa hsb
    subst ea
    split_ifs with h1 h2
    · rfl
    · exact absurd (Nat.beq_refl a) h1
    · exact absurd (Nat.beq_refl a) h1
  · have hq : PRep 276 9 (pcomp 276 9 511 xAp b) (xA * h) := prep_pcomp (by norm_num) prepXA hb
    have ea := eq_of_prep (by norm_num) ha hq hsa (pcomp_shr _ _ (by norm_num) (by norm_num))
    subst ea
    split_ifs with h1 h2
    · rfl
    · rfl
    · exact absurd (Nat.beq_refl _) h2
  · have hq : PRep 276 9 (pcomp 276 9 511 xAp (pcomp 276 9 511 xAp b)) (xA * (xA * h)) :=
      prep_pcomp (by norm_num) prepXA (prep_pcomp (by norm_num) prepXA hb)
    have ea := eq_of_prep (by norm_num) ha hq hsa (pcomp_shr _ _ (by norm_num) (by norm_num))
    subst ea
    split_ifs with h1 h2
    · rfl
    · rfl
    · exact Nat.beq_refl _

theorem bad_ne {sp : ℕ}
    {s : Equiv.Perm (Fin 276)} (hs : PRep 276 9 sp s) (hb : badA sp = true) :
    ∃ j < 5, s * rv j * s⁻¹ * (rv j)⁻¹ ∉ zpowers xA := by
  by_contra hcon
  push Not at hcon
  have hall : allN 5 (fun j => zMulAK (pcomp 276 9 511 sp (RGp j))
      (pcomp 276 9 511 (RGp j) sp)) = true := by
    refine allN_iff.2 fun j hj => ?_
    have e : s * rv j * s⁻¹ * (rv j)⁻¹ = (s * rv j) * (rv j * s)⁻¹ := by group
    have h1 : PRep 276 9 (pcomp 276 9 511 sp (RGp j)) (s * rv j) :=
      prep_pcomp (by norm_num) hs (prepRG hj)
    have h2 : PRep 276 9 (pcomp 276 9 511 (RGp j) sp) (rv j * s) :=
      prep_pcomp (by norm_num) (prepRG hj) hs
    exact zMulAK_of h1 h2 (pcomp_shr _ _ (by norm_num) (by norm_num))
      (pcomp_shr _ _ (by norm_num) (by norm_num))
      (zcases (g := s * rv j) (h := rv j * s) (by rw [← e]; exact hcon j hj))
  unfold badA at hb
  rw [hall] at hb
  exact absurd hb (by decide)

@[expose] noncomputable def u1A : Equiv.Perm (Fin 276) := pv (getS U 0)

@[expose] noncomputable def u2A : Equiv.Perm (Fin 276) := pv (getS U 1)

theorem uFacts : inCA (getS U 0) = true ∧ inCA (getS U 1) = true ∧
    Nat.beq (getS U3 0) (upw (getS U 0) 3) = true ∧ Nat.beq (getS U3 1) (upw (getS U 1) 3) = true ∧
    Nat.beq (pcomp 276 9 511 (getS U 0) (getS U 1))
      (pcomp 276 9 511 (getS U3 2) (pcomp 276 9 511 (getS U 1) (getS U 0))) = true ∧
    allN 3 (fun t => bAnd(fixFA (getS U3 t),
      memK (mapKey 9 511 (getS U3 t) 5 (subKey 9 BA 6 5)) RK)) = true ∧
    allN 8 (fun t => Nat.beq (getS SAB t)
      (pcomp 276 9 511 (upw (getS U 0) (Nat.mod (Nat.succ t) 3))
        (upw (getS U 1) (Nat.div (Nat.succ t) 3)))) = true ∧
    allN 8 (fun t => badA (getS SAB t)) = true := by
  have h := ch17370_u
  simp only [strictB_apply, bAnd_iff] at h
  exact h

theorem u_facts :
    PRep 276 9 (getS U 0) u1A ∧ u1A ∈ CA ∧ PRep 276 9 (getS U 1) u2A ∧ u2A ∈ CA := by
  obtain ⟨hp1, hc1⟩ := inCA_mem uFacts.1
  obtain ⟨hp2, hc2⟩ := inCA_mem uFacts.2.1
  exact ⟨prep_pv hp1, hc1, prep_pv hp2, hc2⟩

theorem U3_mem {t : ℕ} (ht : t < 3)
    {y : Equiv.Perm (Fin 276)} (hp : PRep 276 9 (getS U3 t) y) (hP : y ∈ co3P) : y ∈ RA := by
  obtain ⟨hf, hk⟩ := (bAnd_iff _ _).1 (allN_spec uFacts.2.2.2.2.2.1 t ht)
  exact memR_of hp hP hf hk

theorem u1_pow : u1A ^ 3 ∈ RA := by
  have hp : PRep 276 9 (getS U3 0) (u1A ^ 3) := by
    rw [Nat.eq_of_beq_eq_true uFacts.2.2.1]
    exact prep_upw u_facts.1 3
  exact U3_mem (by norm_num) hp (pow_mem (mem_CA.1 u_facts.2.1).2 3)

theorem u2_pow : u2A ^ 3 ∈ RA := by
  have hp : PRep 276 9 (getS U3 1) (u2A ^ 3) := by
    rw [Nat.eq_of_beq_eq_true uFacts.2.2.2.1]
    exact prep_upw u_facts.2.2.1 3
  exact U3_mem (by norm_num) hp (pow_mem (mem_CA.1 u_facts.2.2.2).2 3)

theorem u_comm :
    u1A * u2A * u1A⁻¹ * u2A⁻¹ ∈ RA := by
  obtain ⟨hp1, hc1, hp2, hc2⟩ := u_facts
  have h12 : PRep 276 9 (pcomp 276 9 511 (getS U 0) (getS U 1)) (u1A * u2A) :=
    prep_pcomp (by norm_num) hp1 hp2
  have h21 : PRep 276 9 (pcomp 276 9 511 (getS U 1) (getS U 0)) (u2A * u1A) :=
    prep_pcomp (by norm_num) hp2 hp1
  have hc := prep_of_pcomp h12 h21 (Nat.eq_of_beq_eq_true uFacts.2.2.2.2.1)
  have e : u1A * u2A * u1A⁻¹ * u2A⁻¹ = u1A * u2A * (u2A * u1A)⁻¹ := by group
  have h1P := (mem_CA.1 hc1).2
  have h2P := (mem_CA.1 hc2).2
  rw [e]
  exact U3_mem (by norm_num) hc
    (co3P.mul_mem (co3P.mul_mem h1P h2P) (co3P.inv_mem (co3P.mul_mem h2P h1P)))

theorem prep_SAB {t : ℕ}
    (ht : t < 8) : PRep 276 9 (getS SAB t) (u1A ^ ((t + 1) % 3) * u2A ^ ((t + 1) / 3)) := by
  rw [Nat.eq_of_beq_eq_true (allN_spec uFacts.2.2.2.2.2.2.1 t ht)]
  exact prep_pcomp (by norm_num) (prep_upw u_facts.1 _) (prep_upw u_facts.2.2.1 _)

theorem badAB {a b : ℕ} (ha : a < 3)
    (hb : b < 3) (hab : ¬ (a = 0 ∧ b = 0)) :
    ∃ j < 5, u1A ^ a * u2A ^ b * rv j * (u1A ^ a * u2A ^ b)⁻¹ * (rv j)⁻¹ ∉ zpowers xA := by
  have ht : a + 3 * b - 1 < 8 := by omega
  have e1 : (a + 3 * b - 1 + 1) % 3 = a := by omega
  have e2 : (a + 3 * b - 1 + 1) / 3 = b := by omega
  have h := bad_ne (prep_SAB ht) (allN_spec uFacts.2.2.2.2.2.2.2 _ ht)
  rw [e1, e2] at h
  exact h

theorem RA_cent :
    centralizer (RA : Set (Equiv.Perm (Fin 276))) ⊓ CA ≤ RA := by
  have hRC : RA ≤ CA := RA_C
  set R' : Subgroup CA := RA.subgroupOf CA
  have hR'n : R'.Normal := ⟨fun n hn g => by
    rw [mem_subgroupOf] at hn ⊢
    exact RA_norm g g.2 n hn⟩
  set N : Subgroup CA := centralizer (R' : Set CA)
  have hNn : N.Normal := centralizer_normal R'
  have hN : Nat.card N ∣ 3 ^ 7 := cent_dvd
  obtain ⟨-, hc1, -, hc2⟩ := u_facts
  set u : CA := ⟨u1A, hc1⟩
  set v : CA := ⟨u2A, hc2⟩
  have huv : ((u ^ 0 * v ^ 0 : CA) : Equiv.Perm (Fin 276)) = 1 := by simp
  have hcoe : ∀ a b : ℕ, ((u ^ a * v ^ b : CA) : Equiv.Perm (Fin 276)) = u1A ^ a * u2A ^ b := by
    intro a b
    rw [Subgroup.coe_mul, SubgroupClass.coe_pow, SubgroupClass.coe_pow]
  have hxC : xA ∈ CA := mem_CA.2 ⟨rfl, xA_mem⟩
  set x' : CA := ⟨xA, hxC⟩
  have hZ : ∀ g : CA, g ∈ zpowers x' ↔ (g : Equiv.Perm (Fin 276)) ∈ zpowers xA := by
    intro g
    rw [← Subgroup.mem_map_iff_mem CA.subtype_injective, MonoidHom.map_zpowers]
    exact Iff.rfl
  have hS : ∀ a < 3, ∀ b < 3, u ^ a * v ^ b ∈ R' → a = 0 ∧ b = 0 := by
    intro a ha b hb hs
    by_contra hab
    obtain ⟨j, hj, hne⟩ := badAB ha hb hab
    rw [mem_subgroupOf, hcoe] at hs
    exact hne (comm_R _ hs _ (rv_mem_RA hj))
  have hu3 : u ^ 3 ∈ R' := by
    rw [mem_subgroupOf, SubgroupClass.coe_pow]
    exact u1_pow
  have hv3 : v ^ 3 ∈ R' := by
    rw [mem_subgroupOf, SubgroupClass.coe_pow]
    exact u2_pow
  have hc : u * v * u⁻¹ * v⁻¹ ∈ R' := by
    rw [mem_subgroupOf]
    exact u_comm
  obtain ⟨M, -, hMc, hMd⟩ := CFSG.KC.Co3Cent.card_two_gen R' hc hu3 hv3 hS
  have hR'c : Nat.card R' = 243 := by
    rw [← card_RA]
    exact Nat.card_congr (subgroupOfEquivOfLe hRC).toEquiv
  have hM : Nat.card M = 3 ^ 7 := by
    rw [hMc, hR'c]
    norm_num
  have h3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hN
  have hNM : N ≤ M := CFSG.KC.Co3Cent.le_of_normal_of_card (p := 3) N M hk hM
    (m := 160) (by rw [card_CA_eq]; norm_num) (by norm_num)
  have hcos := CFSG.KC.Co3Cent.eq_one_of_cosets (R := R') (Z := zpowers x') (T := M)
    (S := {s | ∃ a < 3, ∃ b < 3, s = u ^ a * v ^ b})
    (fun t ht => by
      obtain ⟨r, hr, a, ha, b, hb, rfl⟩ := hMd t ht
      exact ⟨r, hr, _, ⟨a, ha, b, hb, rfl⟩, rfl⟩)
    (fun a ha b hb => by
      rw [hZ]
      exact comm_R _ (mem_subgroupOf.1 ha) _ (mem_subgroupOf.1 hb))
    (fun s hs hs1 => by
      obtain ⟨a, ha, b, hb, rfl⟩ := hs
      have hab : ¬ (a = 0 ∧ b = 0) := by
        rintro ⟨rfl, rfl⟩
        exact hs1 (Subtype.ext huv)
      obtain ⟨j, hj, hne⟩ := badAB ha hb hab
      refine ⟨⟨rv j, hRC (rv_mem_RA hj)⟩, mem_subgroupOf.2 (rv_mem_RA hj), fun hz => hne ?_⟩
      rw [hZ] at hz
      rw [← hcoe]
      exact hz)
  intro g hg
  obtain ⟨hgc, hgC⟩ := Subgroup.mem_inf.1 hg
  have hgN : (⟨g, hgC⟩ : CA) ∈ N := mem_centralizer_iff.2 fun d hd =>
    Subtype.ext (mem_centralizer_iff.1 hgc _ (mem_subgroupOf.1 hd))
  exact mem_subgroupOf.1 (hcos _ (hNM hgN) fun r hr => (mem_centralizer_iff.1 hgN r hr).symm)

theorem caseA :
    xA ^ 3 = 1 ∧ xA ≠ 1 ∧ xA ∈ co3P ∧ Nat.card (closure (permsA 276 (rGens ()))) = 243 ∧
      closure (permsA 276 (rGens ())) ≤ centralizer {xA} ⊓ co3P ∧
      (∀ g ∈ centralizer {xA} ⊓ co3P, ∀ r ∈ closure (permsA 276 (rGens ())),
        g * r * g⁻¹ ∈ closure (permsA 276 (rGens ()))) ∧
      centralizer (closure (permsA 276 (rGens ())) : Set (Equiv.Perm (Fin 276))) ⊓
        (centralizer {xA} ⊓ co3P) ≤ closure (permsA 276 (rGens ())) :=
  ⟨xA_pow, xA_ne, xA_mem, card_RA, RA_C, RA_norm, RA_cent⟩

end CertificateChecks.KernelCo3Cent

end
