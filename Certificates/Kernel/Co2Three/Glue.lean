
module

public import Certificates.Kernel.Co2Three.QFacts
public import Certificates.Kernel.Co2Three.HypB
public import Certificates.Kernel.Co2Three.GChecks
public import CFSG.Certificates.Kernel.Co2Three.DSearchMSound
public import CFSG.Certificates.Kernel.Co2Three.CentConj
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co2ThreeBase
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co2ThreeDefs

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo2Three

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.RankThree.Native.F2 CertificateChecks.KernelMisc.Co2K
open CFSG.RankThree.PartTwo.Sec4.Item434SporE81
open CFSG.RankThree.Native CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.Monster.B.Mathieu
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co2T CFSG.Certificates.Native
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance CFSG.Sporadic.Co2Cert CFSG.Monster.B.Co2
open CFSG.KC.Co2Three

theorem kQ_spec :
    (∀ x, x ∈ Qg ↔ ∃ i < qLit.pts.size, permOfArr 2300 qLit.pts[i]! = x) ∧
      Nat.card Qg = qLit.pts.size ∧ ∀ i < qLit.pts.size, validA 2300 qLit.pts[i]! = true :=
  enumOK_spec qKeys_lt enumQ

theorem kcard_Qg : Nat.card Qg = 729 := kQ_spec.2.1.trans qLit_size

theorem kqPts_valid : ∀ k < 729, validA 2300 (qCert2 ()).pts[k]! = true := by
  intro k hk
  rw [qCert2_pts]
  exact kQ_spec.2.2 k (by rw [qLit_size]; exact hk)

theorem kmem_Qg_iff : ∀ x, x ∈ Qg ↔ ∃ k < 729, permOfArr 2300 (qCert2 ()).pts[k]! = x := by
  intro x
  rw [qCert2_pts, kQ_spec.1 x, qLit_size]

theorem kQg_le : Qg ≤ co2P := by
  rw [Qg, Subgroup.closure_le]
  rintro _ ⟨k, hk, rfl⟩
  exact mem_co2P_of_inP (rep_of_validA (enumOK_gens_valid enumQ hk))
    (qGens_inP (by rwa [qGens2_size] at hk))

theorem mm_I22 {A : ℕ} (hA : Good A) : mmK I22 A = A := by
  rw [hmm, I22_eq]
  exact mat_ext (mmul_lt _ _) hA.2 fun _ hk => row_idM_mmul hd22 _ hk

theorem kD_parts : (∀ i < 4, pwK (CertificateChecks.KernelCo2Pump.DD i) 3 = I22) ∧
    (∀ i < 4, ∀ j < 4,
      comm (CertificateChecks.KernelCo2Pump.DD i) (CertificateChecks.KernelCo2Pump.DD j) = true) ∧
    ∀ k < 81, ∀ k' < 81, k = k' ∨ ED k ≠ ED k' := by
  have h := ch13636D_all 0 (by norm_num)
  unfold ch13636D dK at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨fun i hi => Nat.eq_of_beq_eq_true (allN_spec h1 i hi),
    fun i hi j hj => allN_spec (allN_spec h2 i hi) j hj, fun k hk k' hk' => ?_⟩
  have := allN_spec (allN_spec h3 k hk) k' hk'
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at this
  rcases this with e | e
  · exact Or.inl (Nat.eq_of_beq_eq_true e)
  · exact Or.inr fun e' => by rw [e', Nat.beq_refl] at e; exact absurd e (by decide)

theorem kD_inv {i : ℕ} (hi : i < 4) : Inv 22 co2FiveV (CertificateChecks.KernelCo2Pump.DD i)
    (mmK (CertificateChecks.KernelCo2Pump.DD i) (CertificateChecks.KernelCo2Pump.DD i)) := by
  set A := CertificateChecks.KernelCo2Pump.DD i
  have hg : Good A := (CertificateChecks.KernelCo2Pump.dG hi).2
  have e3 : pwK A 3 = mmK (mmK (mmK I22 A) A) A := rfl
  have h2 : mmK (mmK A A) A = I22 := by
    have h := kD_parts.1 i hi
    rw [e3, mm_I22 hg] at h
    exact h
  refine inv_of_good hg ?_ h2
  rw [← h2]
  simp only [hmm]
  exact (mmul_assoc _ _ _).symm

theorem kdGen_valid {i : ℕ} (hi : i < 4) : validA 2300 (dGens ())[i]! = true := by
  rw [(CertificateChecks.KernelCo2Pump.dG hi).1]
  exact validA_inv (kD_inv hi)

theorem krep_dGen {i : ℕ} (hi : i < 4) : Rep 2300 (dGens ())[i]! (dGenP i) :=
  rep_of_validA (kdGen_valid hi)

theorem kdGen_pow {i : ℕ} (hi : i < 4) : dGenP i ^ 3 = 1 := by
  obtain ⟨e, g⟩ := CertificateChecks.KernelCo2Pump.dG hi
  refine (eqA_iff (rep_powArr (krep_dGen hi) 3) rep_idA).1 ?_
  rw [e, pow_good g, idA_eq, eqA_good (good_pw g 3) good_I22, kD_parts.1 i hi]
  exact Nat.beq_refl _

theorem kdGen_comm : ∀ i < 4, ∀ j < 4, Commute (dGenP i) (dGenP j) := by
  intro i hi j hj
  obtain ⟨ei, gi⟩ := CertificateChecks.KernelCo2Pump.dG hi
  obtain ⟨ej, gj⟩ := CertificateChecks.KernelCo2Pump.dG hj
  refine (commA_iff (krep_dGen hi) (krep_dGen hj)).1 ?_
  rw [ei, ej, commA_good gi gj]
  exact kD_parts.2.1 i hi j hj

theorem kdGen_facts :
    ∀ i < 4, validA 2300 (dGens ())[i]! = true ∧ dGenP i ∈ co2P ∧ dGenP i ^ 3 = 1 :=
  fun i hi => ⟨kdGen_valid hi, mem_co2P_of_inP (krep_dGen hi) (dGens_inP hi), kdGen_pow hi⟩

theorem krep_dElt {k : ℕ} (hk : k < 81) : Rep 2300 (dElts ())[k]! (dGenP 0 ^ digit3 k 0 *
    (dGenP 1 ^ digit3 k 1 * (dGenP 2 ^ digit3 k 2 * dGenP 3 ^ digit3 k 3))) := by
  have he : (dElts ())[k]! = dProd (dGens ()) k := by
    rw [dElts, getElem!_pos _ k (by simpa using hk), Array.getElem_ofFn]
  rw [he, dProd]
  exact rep_compA (rep_powArr (krep_dGen (by norm_num)) _) (rep_compA (rep_powArr
    (krep_dGen (by norm_num)) _) (rep_compA (rep_powArr (krep_dGen (by norm_num)) _)
      (rep_powArr (krep_dGen (by norm_num)) _)))

theorem kdElt_eq {k : ℕ} (hk : k < 81) : dEltP k = dGenP 0 ^ digit3 k 0 *
    (dGenP 1 ^ digit3 k 1 * (dGenP 2 ^ digit3 k 2 * dGenP 3 ^ digit3 k 3)) :=
  CFSG.RankThree.Native.permOfArr_eq_of_rep (krep_dElt hk)

theorem krep_e {k : ℕ} (hk : k < 81) : Rep 2300 (dElts ())[k]! (dEltP k) := by
  rw [kdElt_eq hk]
  exact krep_dElt hk

theorem kdElt_inj : ∀ k < 81, ∀ k' < 81, dEltP k = dEltP k' → k = k' := by
  intro k hk k' hk' e
  have h := (eqA_iff (krep_e hk) (krep_e hk')).2 e
  obtain ⟨ek, gk⟩ := CertificateChecks.KernelCo2Pump.eG hk
  obtain ⟨ek', gk'⟩ := CertificateChecks.KernelCo2Pump.eG hk'
  rw [ek, ek', eqA_good gk gk'] at h
  exact (kD_parts.2.2 k hk k' hk').resolve_right fun hne => hne (Nat.eq_of_beq_eq_true h)

@[expose] noncomputable def kφ : Multiplicative (Fin 4 → ZMod 3) →* Equiv.Perm (Fin 2300) :=
  Co3T.vecProdHom (fun i : Fin 4 => dGenP i) (fun i j => kdGen_comm i i.2 j j.2)
    (fun i => kdGen_pow i.2)

theorem kvecProd_eq (a : Fin 4 → ZMod 3) : Co3T.vecProd (fun i : Fin 4 => dGenP i) a =
    dGenP 0 ^ (a 0).val * (dGenP 1 ^ (a 1).val * (dGenP 2 ^ (a 2).val * dGenP 3 ^ (a 3).val)) := by
  simp [Co3T.vecProd, List.finRange_succ]

theorem kφ_vec (k : ℕ) (hk : k < 81) : kφ (Multiplicative.ofAdd (vec k)) = dEltP k := by
  rw [kdElt_eq hk]
  change Co3T.vecProd (fun i : Fin 4 => dGenP i) (vec k) = _
  rw [kvecProd_eq]
  simp only [vec_val]
  rfl

theorem kφ_idx (a : Fin 4 → ZMod 3) : kφ (Multiplicative.ofAdd a) = dEltP (idx a) := by
  rw [← kφ_vec _ (idx_lt a), vec_idx]

theorem kφ_apply (a : Multiplicative (Fin 4 → ZMod 3)) : kφ a = dEltP (idx a.toAdd) := by
  have h := kφ_idx a.toAdd
  rwa [ofAdd_toAdd] at h

theorem kφ_injective : Function.Injective kφ := by
  intro a b hab
  rw [kφ_apply, kφ_apply] at hab
  have := congrArg vec (kdElt_inj _ (idx_lt _) _ (idx_lt _) hab)
  rw [vec_idx, vec_idx] at this
  exact Multiplicative.toAdd.injective this

theorem kφ_range_le :
    kφ.range ≤ co2P := by
  rintro _ ⟨a, rfl⟩
  rw [kφ_apply, kdElt_eq (idx_lt _)]
  have h := fun i hi => (kdGen_facts i hi).2.1
  exact co2P.mul_mem (co2P.pow_mem (h 0 (by norm_num)) _) (co2P.mul_mem
    (co2P.pow_mem (h 1 (by norm_num)) _) (co2P.mul_mem (co2P.pow_mem (h 2 (by norm_num)) _)
      (co2P.pow_mem (h 3 (by norm_num)) _)))

@[expose] def hypSet (r : ℕ) : Set (Equiv.Perm (Fin 2300)) :=
  {x | ∃ k < 81, dotK r k = 0 ∧ x = dEltP k}

theorem dotK_eq (m k : ℕ) : dotK m k = dot3 m k := by
  have h : ∀ a b c d : ℕ, (a + b + (c + d)) % 3 = (a + b + c + d) % 3 := fun a b c d => by
    rw [Nat.add_assoc (a + b)]
  exact h _ _ _ _

theorem beqB_eq {a b : Bool} (h : beqB a b = true) : a = b := by
  cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

theorem linK_lt (C : ℕ → ℕ) (k : ℕ) : linK C k < 81 := by
  unfold linK
  have h : ∀ r, linD C k r < 3 := fun r => Nat.mod_lt _ (by norm_num)
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  simp only [Nat.add_eq, Nat.mul_eq]
  omega

theorem hypBd_le (ρ : ℕ) : hypBd ρ ≤ 162 := by
  unfold hypBd
  cases Nat.beq ρ 1 <;> decide

theorem hypS_le {ρ : ℕ} (hρ : ρ < 8) : hypS ρ ≤ hypBd ρ :=
  Nat.le_of_ble_eq_true (ch13636HypB_all ρ hρ)

theorem kconj_e {j k : ℕ} (hj : j < 3) (hk : k < 81) :
    permOfArr 2300 (qGens2 ())[j]! * dEltP k * (permOfArr 2300 (qGens2 ())[j]!)⁻¹ =
      dEltP (linK (CC j) k) := by
  have h := ch13636Q_all j hj
  unfold ch13636Q qK at h
  simp only [Bool.and_eq_true] at h
  have he := Nat.eq_of_beq_eq_true (allN_spec h.2 k hk)
  have hk' := linK_lt (CC j) k
  obtain ⟨eq, gq⟩ := qD_get hj
  have hv : validA 2300 (qGens2 ())[j]! = true := by rw [eq]; exact validA_inv (qD_inv hj)
  have hr := rep_conjA hv (krep_e hk)
  have hc : conjA 2300 (qGens2 ())[j]! (dElts ())[k]! = (dElts ())[linK (CC j) k]! := by
    obtain ⟨ek, gk⟩ := CertificateChecks.KernelCo2Pump.eG hk
    rw [eq, ek, conj_good (qD_inv hj) gk, (CertificateChecks.KernelCo2Pump.eG hk').1]
    exact congrArg _ he.symm
  rw [hc] at hr
  exact (CFSG.RankThree.Native.permOfArr_eq_of_rep hr).symm

theorem forest_at {h : ℕ} (hh : h < 40) : forestK HH HP HJ HD CC h = true := by
  have e : Nat.add (Nat.mul 10 (h / 10)) (h % 10) = h := by
    simp only [Nat.add_eq, Nat.mul_eq]
    omega
  have h4 : h / 10 < 4 := by omega
  have hc := ch13636F_all (h / 10) h4
  unfold ch13636F at hc
  have : forestK HH HP HJ HD CC (Nat.add (Nat.mul 10 (h / 10)) (h % 10)) = true :=
    allN_spec hc (h % 10) (Nat.mod_lt _ (by norm_num))
  rw [e] at this
  exact this

theorem cover_at {m : ℕ} (hm0 : m ≠ 0) (hm : m < 81) : coverK CV m = true := by
  have e : Nat.add (Nat.add (Nat.mul 20 ((m - 1) / 20)) ((m - 1) % 20)) 1 = m := by
    simp only [Nat.add_eq, Nat.mul_eq]
    omega
  have h4 : (m - 1) / 20 < 4 := by omega
  have hc := ch13636C_all ((m - 1) / 20) h4
  unfold ch13636C at hc
  have : coverK CV (Nat.add (Nat.add (Nat.mul 20 ((m - 1) / 20)) ((m - 1) % 20)) 1) = true :=
    allN_spec hc ((m - 1) % 20) (Nat.mod_lt _ (by norm_num))
  rw [e] at this
  exact this

section Hyp

theorem pt_of_vec {M : ℕ} {σ : Equiv.Perm (Fin 2300)} (hM : ∀ v ∈ co2FiveV, vmul 22 v M ∈ co2FiveV)
    (hσ : Rep 2300 (permOfMat 22 co2FiveV M) σ) (p q : Fin 2300) (h : vmK (VG p) M = VG q) :
    σ p = q := by
  have e := vg_apply sys V_size hM hσ p
  rw [← hvm, h] at e
  apply Fin.ext
  have := congrArg LK e
  rwa [sys.lk _ (by rw [V_size]; exact (σ p).2), sys.lk _ (by rw [V_size]; exact q.2)] at this

theorem base_get (l : ℕ) (hl : l < co2Q.baseCount) :
    ((co2Q.base.get ⟨l, hl⟩ : Fin 2300) : ℕ) = BS l := by
  rw [co2Q_chainArrays.base_val ⟨l, hl⟩, hBS l (by rw [base_size, ← co2Q_baseCount]; exact hl)]

theorem root_parts {ρ : ℕ} (hρ : ρ < 8) : Good (GM ρ) ∧ Inv 22 co2FiveV (GM ρ) (GIM ρ) ∧
    ∀ l < 6, (relOK (RT ρ) (GM ρ) (GIM ρ) (RFn ρ) (RSn ρ) (RKn ρ) (YM ρ) l &&
        fixOK (RT ρ) (GM ρ) (GIM ρ) (FTn ρ) (FKn ρ) (ZM ρ) l) = true := by
  have hR := ch13636R_all ρ hρ
  unfold ch13636R rootK at hR
  simp only [Bool.and_eq_true, Nat.beq_eq] at hR
  obtain ⟨⟨⟨⟨⟨-, hT⟩, hG⟩, h1⟩, h2⟩, hls⟩ := hR
  have hgood : Good (GM ρ) := by
    rw [hG]
    exact good_gProd fun l hl => Nat.blt_eq.mp (allN_spec hT l hl)
  exact ⟨hgood, inv_of_good hgood h1 h2, fun l hl => allN_spec hls l hl⟩

theorem root_rel {ρ : ℕ} (hρ : ρ < 8) : ∀ l < 6, Nat.beq (RFn ρ l) 1 = true → RSn ρ l < l ∧
    RKn ρ l < 81 ∧ dotK (RT ρ) (RKn ρ l) = 0 ∧ YM ρ l = conjG (GM ρ) (GIM ρ) (RKn ρ l) ∧
      vmK (VG (BS (RSn ρ l))) (YM ρ l) = VG (BS l) := by
  intro l hl hf
  have h0 := (root_parts hρ).2.2 l hl
  rw [Bool.and_eq_true] at h0
  have h := h0.1
  simp only [relOK, inB, hf, Bool.not_true, Bool.false_or, Bool.and_eq_true, Nat.blt_eq,
    Nat.beq_eq] at h
  obtain ⟨⟨⟨hs, hk, hd⟩, hY⟩, hv⟩ := h
  exact ⟨hs, hk, hd, hY, hv⟩

theorem root_fix {ρ : ℕ} (hρ : ρ < 8) : ∀ l < 6, Nat.beq (FTn ρ l) 1 = true → FKn ρ l < 81 ∧
    dotK (RT ρ) (FKn ρ l) = 0 ∧ ZM ρ l = conjG (GM ρ) (GIM ρ) (FKn ρ l) ∧
      vmK (VG (BS l)) (ZM ρ l) = VG (BS l) := by
  intro l hl hf
  have h0 := (root_parts hρ).2.2 l hl
  rw [Bool.and_eq_true] at h0
  have h := h0.2
  simp only [fixOK, inB, hf, Bool.not_true, Bool.false_or, Bool.and_eq_true, Nat.blt_eq,
    Nat.beq_eq] at h
  obtain ⟨⟨⟨hk, hd⟩, hZ⟩, hv⟩ := h
  exact ⟨hk, hd, hZ, hv⟩

theorem root_g {ρ : ℕ} (hρ : ρ < 8) :
    permOfArr 2300 (permOfMat 22 co2FiveV (GM ρ)) ∈ co2P ∧ ∀ k < 81,
      (∀ v ∈ co2FiveV, vmul 22 v (conjG (GM ρ) (GIM ρ) k) ∈ co2FiveV) ∧
      Rep 2300 (permOfMat 22 co2FiveV (conjG (GM ρ) (GIM ρ) k))
        ((permOfArr 2300 (permOfMat 22 co2FiveV (GM ρ)))⁻¹ *
          (dEltP k * permOfArr 2300 (permOfMat 22 co2FiveV (GM ρ)))) := by
  obtain ⟨hgood, hinv, -⟩ := root_parts hρ
  have hgv := validA_inv hinv
  have RG := rep_of_validA hgv
  have RGI : Rep 2300 (permOfMat 22 co2FiveV (GIM ρ))
      (permOfArr 2300 (permOfMat 22 co2FiveV (GM ρ)))⁻¹ := by
    rw [← invCand_good hinv]
    exact rep_inv_of_validA hgv
  have hsift : inP (Co2T.levels ()) (permOfMat 22 co2FiveV (GM ρ)) = true := by
    unfold inP Co2T.levels
    exact sift_of hgood.1 (ch13636G_all ρ hρ)
  refine ⟨mem_co2P_of_inP RG hsift, fun k hk => ⟨?_, ?_⟩⟩
  · have gk' : Good (ED k) := (CertificateChecks.KernelCo2Pump.eG hk).2
    unfold conjG
    rw [hmm, hmm]
    exact maps_mmul (maps_mmul hgood.1 gk'.1) hinv.2.1
  · obtain ⟨ek, gk⟩ := CertificateChecks.KernelCo2Pump.eG hk
    have gk' : Good (ED k) := gk
    have hre : Rep 2300 (permOfMat 22 co2FiveV (ED k)) (dEltP k) := by
      have := krep_e hk
      rw [ek] at this
      exact this
    unfold conjG
    rw [← compA_good (good_mm hgood gk'), ← compA_good hgood]
    exact rep_compA RGI (rep_compA hre RG)

theorem hypS_eq (ρ : ℕ) : hypS ρ = dsearchM vmK mmK VG BS LK (fun i => Nat.beq (RFn ρ i) 1)
    (fun i => Nat.beq (FTn ρ i) 1) (RSn ρ) (YM ρ)
    (fun i u => bIf(Nat.beq (FTn ρ i) 1, Nat.beq (vmK u (ZM ρ i)) u, true)) (fun _ => true)
    mL PT PO TM TIM 6 0 I22 I22 := by
  unfold hypS hypG
  rfl

@[expose] noncomputable def gRoot (ρ : ℕ) : Equiv.Perm (Fin 2300) :=
  permOfArr 2300 (permOfMat 22 co2FiveV (GM ρ))

theorem conj_comm (g c e : Equiv.Perm (Fin 2300)) (h : c * e = e * c) :
    (g⁻¹ * c * g) * (g⁻¹ * (e * g)) = (g⁻¹ * (e * g)) * (g⁻¹ * c * g) := by
  calc (g⁻¹ * c * g) * (g⁻¹ * (e * g)) = g⁻¹ * (c * e) * g := by group
    _ = g⁻¹ * (e * c) * g := by rw [h]
    _ = (g⁻¹ * (e * g)) * (g⁻¹ * c * g) := by group

theorem rel_of_comm {c Y : Equiv.Perm (Fin 2300)} {p q : Fin 2300} (hY : Y p = q)
    (h : c * Y = Y * c) : c q = Y (c p) :=
  calc c q = c (Y p) := by rw [hY]
    _ = (c * Y) p := rfl
    _ = (Y * c) p := by rw [h]
    _ = Y (c p) := rfl

theorem fix_of_comm {c Z : Equiv.Perm (Fin 2300)} {p : Fin 2300} (hZ : Z p = p)
    (h : c * Z = Z * c) : Z (c p) = c p :=
  calc Z (c p) = (Z * c) p := rfl
    _ = (c * Z) p := by rw [h]
    _ = c (Z p) := rfl
    _ = c p := by rw [hZ]

theorem root_relRep {ρ : ℕ} (hρ : ρ < 8) (l : ℕ) (hl : l < co2Q.baseCount)
    (hf : Nat.beq (RFn ρ l) 1 = true) : Rep 2300 (permOfMat 22 co2FiveV (YM ρ l))
      ((gRoot ρ)⁻¹ * (dEltP (RKn ρ l) * gRoot ρ)) := by
  have hl6 : l < 6 := by rw [co2Q_baseCount] at hl; exact hl
  obtain ⟨hs, hk, hd, hY, hv⟩ := root_rel hρ l hl6 hf
  have hg := (root_g hρ).2 _ hk
  rw [hY]
  exact hg.2

theorem root_relVec {ρ : ℕ} (hρ : ρ < 8) (l : ℕ) (hl : l < co2Q.baseCount)
    (hf : Nat.beq (RFn ρ l) 1 = true) (hs : RSn ρ l < l) :
    vmK (VG (co2Q.base.get ⟨RSn ρ l, by omega⟩)) (YM ρ l) = VG (co2Q.base.get ⟨l, hl⟩) := by
  have hl6 : l < 6 := by rw [co2Q_baseCount] at hl; exact hl
  obtain ⟨-, -, -, -, hv⟩ := root_rel hρ l hl6 hf
  rw [base_get, base_get]
  exact hv

theorem root_conj_comm {ρ : ℕ} {c : Equiv.Perm (Fin 2300)} (hc : ∀ x ∈ hypSet (RT ρ), Commute c x)
    {k : ℕ} (hk : k < 81) (hd : dotK (RT ρ) k = 0) :
    ((gRoot ρ)⁻¹ * c * gRoot ρ) * ((gRoot ρ)⁻¹ * (dEltP k * gRoot ρ)) =
      ((gRoot ρ)⁻¹ * (dEltP k * gRoot ρ)) * ((gRoot ρ)⁻¹ * c * gRoot ρ) :=
  conj_comm (gRoot ρ) c _ (hc _ ⟨_, hk, hd, rfl⟩)

theorem root_relPt {ρ : ℕ} (hρ : ρ < 8) (l : ℕ) (hl : l < co2Q.baseCount)
    (hf : Nat.beq (RFn ρ l) 1 = true) (hs : RSn ρ l < l) :
    ((gRoot ρ)⁻¹ * (dEltP (RKn ρ l) * gRoot ρ)) (co2Q.base.get ⟨RSn ρ l, by omega⟩) =
      co2Q.base.get ⟨l, hl⟩ := by
  have hl6 : l < 6 := by rw [co2Q_baseCount] at hl; exact hl
  obtain ⟨-, hk, -, hY, -⟩ := root_rel hρ l hl6 hf
  have hg := (root_g hρ).2 _ hk
  exact pt_of_vec (by rw [hY]; exact hg.1) (root_relRep hρ l hl hf) _ _
    (root_relVec hρ l hl hf hs)

theorem root_relEq {ρ : ℕ} (hρ : ρ < 8) {c : Equiv.Perm (Fin 2300)}
    (hc : ∀ x ∈ hypSet (RT ρ), Commute c x) (l : ℕ) (hl : l < co2Q.baseCount)
    (hf : Nat.beq (RFn ρ l) 1 = true) (hs : RSn ρ l < l) :
    ((gRoot ρ)⁻¹ * c * gRoot ρ) (co2Q.base.get ⟨l, hl⟩) =
      ((gRoot ρ)⁻¹ * (dEltP (RKn ρ l) * gRoot ρ))
        (((gRoot ρ)⁻¹ * c * gRoot ρ) (co2Q.base.get ⟨RSn ρ l, by omega⟩)) := by
  have hl6 : l < 6 := by rw [co2Q_baseCount] at hl; exact hl
  obtain ⟨-, hk, hd, -, -⟩ := root_rel hρ l hl6 hf
  exact rel_of_comm (root_relPt hρ l hl hf hs) (root_conj_comm hc hk hd)

theorem root_hrel {ρ : ℕ} (hρ : ρ < 8) {c : Equiv.Perm (Fin 2300)}
    (hc : ∀ x ∈ hypSet (RT ρ), Commute c x) (l : ℕ) (hl : l < co2Q.baseCount)
    (hf : Nat.beq (RFn ρ l) 1 = true) : ∃ hs : RSn ρ l < l, ∃ Y : Equiv.Perm (Fin 2300),
      Rep 2300 (permOfMat 22 co2FiveV (YM ρ l)) Y ∧
        ((gRoot ρ)⁻¹ * c * gRoot ρ) (co2Q.base.get ⟨l, hl⟩) =
          Y (((gRoot ρ)⁻¹ * c * gRoot ρ) (co2Q.base.get ⟨RSn ρ l, by omega⟩)) := by
  have hl6 : l < 6 := by rw [co2Q_baseCount] at hl; exact hl
  obtain ⟨hs, -, -, -, -⟩ := root_rel hρ l hl6 hf
  exact ⟨hs, _, root_relRep hρ l hl hf, root_relEq hρ hc l hl hf hs⟩

theorem root_hfix {ρ : ℕ} (hρ : ρ < 8) {c : Equiv.Perm (Fin 2300)}
    (hc : ∀ x ∈ hypSet (RT ρ), Commute c x) (l : ℕ) (hl : l < co2Q.baseCount) :
    Nat.beq (FTn ρ l) 1 = true → Nat.beq (vmK (VG (((gRoot ρ)⁻¹ * c * gRoot ρ)
      (co2Q.base.get ⟨l, hl⟩))) (ZM ρ l)) (VG (((gRoot ρ)⁻¹ * c * gRoot ρ)
        (co2Q.base.get ⟨l, hl⟩))) = true := by
  intro hft
  have hl6 : l < 6 := by rw [co2Q_baseCount] at hl; exact hl
  obtain ⟨hk, hd, hZ, hv⟩ := root_fix hρ l hl6 hft
  have hg := (root_g hρ).2 _ hk
  have hmZ : ∀ v ∈ co2FiveV, vmul 22 v (ZM ρ l) ∈ co2FiveV := by
    rw [hZ]
    exact hg.1
  have hRZ : Rep 2300 (permOfMat 22 co2FiveV (ZM ρ l))
      ((gRoot ρ)⁻¹ * (dEltP (FKn ρ l) * gRoot ρ)) := by
    rw [hZ]
    exact hg.2
  have hZb := pt_of_vec hmZ hRZ (co2Q.base.get ⟨l, hl⟩) (co2Q.base.get ⟨l, hl⟩)
    (by rw [base_get]; exact hv)
  have e := vg_apply sys V_size hmZ hRZ (((gRoot ρ)⁻¹ * c * gRoot ρ) (co2Q.base.get ⟨l, hl⟩))
  rw [fix_of_comm hZb (root_conj_comm hc hk hd)] at e
  rw [hvm, ← e]
  exact Nat.beq_refl _

theorem root_search {ρ : ℕ} (hρ : ρ < 8) {X : Set (Equiv.Perm (Fin 2300))}
    (hX : ∀ c ∈ X, c ∈ co2P)
    (hrel : ∀ c ∈ X, ∀ l (hl : l < co2Q.baseCount), Nat.beq (RFn ρ l) 1 = true →
      ∃ hs : RSn ρ l < l, ∃ Y : Equiv.Perm (Fin 2300),
        Rep 2300 (permOfMat 22 co2FiveV (YM ρ l)) Y ∧
          c (co2Q.base.get ⟨l, hl⟩) = Y (c (co2Q.base.get ⟨RSn ρ l, by omega⟩)))
    (hfix : ∀ c ∈ X, ∀ l (hl : l < co2Q.baseCount), Nat.beq (FTn ρ l) 1 = true →
      Nat.beq (vmK (VG (c (co2Q.base.get ⟨l, hl⟩))) (ZM ρ l)) (VG (c (co2Q.base.get ⟨l, hl⟩)))
        = true) :
    Nat.card X ≤ hypS ρ := by
  have hS := card_le_dsearchM co2Q_chainArrays
    (CFSG.Certificates.chainCheckFacts co2Chain_check.1) co2Q_valid.1 sys V_size hvm hmm
    (nb := co2BaseArr.size) (by rw [co2Q_baseCount, base_size]) LF hBS
    (RF := fun i => Nat.beq (RFn ρ i) 1) (FF := fun i => Nat.beq (FTn ρ i) 1) (RS := RSn ρ)
    (RY := YM ρ) (FX := fun i u => bIf(Nat.beq (FTn ρ i) 1, Nat.beq (vmK u (ZM ρ i)) u, true))
    (PR := fun _ => true)
    (fun l hl hf => by
      obtain ⟨-, hk, -, hY, -⟩ := root_rel hρ l (by rwa [base_size] at hl) hf
      rw [hY]
      exact ((root_g hρ).2 _ hk).1) I22_eq (X := X)
    (fun c hc => by rw [co2Q_originalSubgroup]; exact hX c hc) hrel
    (fun c hc l hl => by
      change bIf(Nat.beq (FTn ρ l) 1, _, true) = true
      cases hft : Nat.beq (FTn ρ l) 1
      · rfl
      · exact hfix c hc l hl hft)
    (fun _ _ _ _ _ => rfl)
  rw [base_size, ← hypS_eq] at hS
  exact hS

theorem kcard_le_root : ∀ ρ < 8, ∀ K : Subgroup (Equiv.Perm (Fin 2300)), K ≤ co2P →
    (∀ c ∈ K, ∀ x ∈ hypSet (RT ρ), Commute c x) → Nat.card K ≤ hypS ρ := by
  intro ρ hρ K hKP hK
  have hgP : gRoot ρ ∈ co2P := (root_g hρ).1
  have hinj : Function.Injective fun c : Equiv.Perm (Fin 2300) => (gRoot ρ)⁻¹ * c * gRoot ρ :=
    fun a b h => by simpa using h
  have h := root_search hρ (X := (fun c => (gRoot ρ)⁻¹ * c * gRoot ρ) '' (K : Set _))
    (by
      rintro _ ⟨c, hc, rfl⟩
      exact co2P.mul_mem (co2P.mul_mem (co2P.inv_mem hgP) (hKP hc)) hgP)
    (by
      rintro _ ⟨c, hc, rfl⟩
      exact root_hrel hρ (hK c hc))
    (by
      rintro _ ⟨c, hc, rfl⟩
      exact root_hfix hρ (hK c hc))
  rw [Nat.card_image_of_injective hinj] at h
  exact h

theorem card_cent_forest :
    ∀ h < 40, Nat.card ↥(Subgroup.centralizer (hypSet (HH h)) ⊓ co2P) ≤ 162 := by
  suffices H : ∀ n, ∀ h < 40, HD h = n →
      Nat.card ↥(Subgroup.centralizer (hypSet (HH h)) ⊓ co2P) ≤ 162 from
    fun h hh => H _ h hh rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro h hh hn
  have hf := forest_at hh
  unfold forestK at hf
  cases hj : Nat.beq (HJ h) 3
  · simp only [hj, Bool.and_eq_true, Nat.blt_eq] at hf
    obtain ⟨⟨-, hJ⟩, ⟨hP, hD⟩, hall⟩ := hf
    have hJ3 : HJ h < 3 := by
      have : HJ h ≠ 3 := fun e => by rw [e] at hj; exact absurd hj (by decide)
      omega
    have hIH := ih (HD (HP h)) (hn ▸ hD) (HP h) hP rfl
    set q := permOfArr 2300 (qGens2 ())[HJ h]!
    have hq : q ∈ co2P := kQg_le (Subgroup.subset_closure ⟨HJ h, by rw [qGens2_size]; exact hJ3,
      rfl⟩)
    have hsub : (fun x => q * x * q⁻¹) '' hypSet (HH (HP h)) ⊆ hypSet (HH h) := by
      rintro _ ⟨_, ⟨k, hk, hdk, rfl⟩, rfl⟩
      refine ⟨linK (CC (HJ h)) k, linK_lt _ _, ?_, kconj_e hJ3 hk⟩
      have := beqB_eq (allN_spec hall k hk)
      rw [hdk, Nat.beq_refl] at this
      exact Nat.eq_of_beq_eq_true this.symm
    calc Nat.card ↥(Subgroup.centralizer (hypSet (HH h)) ⊓ co2P)
        ≤ Nat.card ↥(Subgroup.centralizer ((fun x => q * x * q⁻¹) '' hypSet (HH (HP h))) ⊓
            co2P) :=
          Subgroup.card_le_of_le (inf_le_inf_right _ (Subgroup.centralizer_le hsub))
      _ = _ := card_centralizer_conj_inf hq _
      _ ≤ 162 := hIH
  · simp only [hj, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at hf
    obtain ⟨-, hP, hR⟩ := hf
    rw [← hR]
    refine (kcard_le_root (HP h) hP _ inf_le_right fun c hc x hx => ?_).trans
      ((hypS_le hP).trans (hypBd_le _))
    exact ((Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hc).1) x hx).symm

theorem kcard_cent_le (B : Subgroup (Equiv.Perm (Fin 2300))) (hBD : ∀ b ∈ B, ∃ k < 81, b = dEltP k)
    (hB : Nat.card B * 3 = 81) :
    Nat.card ↥(Subgroup.centralizer (B : Set (Equiv.Perm (Fin 2300))) ⊓ co2P) ≤ 162 := by
  have hBr : B ≤ kφ.range := fun b hb => by
    obtain ⟨k, hk, rfl⟩ := hBD b hb
    exact ⟨_, kφ_vec k hk⟩
  obtain ⟨f, hf0, hf⟩ := Co3T.exists_dot_eq_zero_imp_mem kφ kφ_injective hBr
    (by rw [hB]; norm_num)
  have hm0 : idx f ≠ 0 := fun h => hf0 ((idx_eq_zero_iff f).1 h)
  have hc := cover_at hm0 (idx_lt f)
  unfold coverK at hc
  simp only [Bool.and_eq_true, Nat.blt_eq] at hc
  have hsub : hypSet (HH (CV (idx f))) ⊆ B := by
    rintro _ ⟨k, hk, hdk, rfl⟩
    have := beqB_eq (allN_spec hc.2 k hk)
    rw [hdk, Nat.beq_refl] at this
    have h0 : dot3 (idx f) k = 0 := by rw [← dotK_eq]; exact Nat.eq_of_beq_eq_true this
    rw [← kφ_vec k hk]
    exact hf _ ((dot3_eq_zero_iff f k).1 h0)
  exact (Subgroup.card_le_of_le (inf_le_inf_right _ (Subgroup.centralizer_le hsub))).trans
    (card_cent_forest _ hc.1)

theorem kcent_D : ∀ c ∈ co2P, (∀ k < 81, Commute c (dEltP k)) → ∃ k < 81, c = dEltP k := by
  intro c hcP hc
  set K := Subgroup.centralizer (hypSet (RT 1)) ⊓ co2P
  have hK : Nat.card K ≤ 81 := (kcard_le_root 1 (by norm_num) K inf_le_right fun c hc x hx =>
    ((Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hc).1) x hx).symm).trans
      (hypS_le (by norm_num))
  have hDK : kφ.range ≤ K := by
    rintro _ ⟨a, rfl⟩
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_iff.2 ?_, kφ_range_le ⟨a, rfl⟩⟩
    rintro _ ⟨k, hk, -, rfl⟩
    rw [← kφ_vec k hk, ← map_mul, ← map_mul, mul_comm]
  have hcard : Nat.card kφ.range = 81 := by
    rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective kφ_injective, Subgroup.card_top,
      Co3T.card_vec]
    norm_num
  have heq := Subgroup.eq_of_le_of_card_ge hDK (by rw [hcard]; exact hK)
  have hcK : c ∈ K := Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_iff.2 fun x hx => by
    obtain ⟨k, hk, -, rfl⟩ := hx
    exact (hc k hk).symm, hcP⟩
  rw [← heq] at hcK
  obtain ⟨a, rfl⟩ := hcK
  exact ⟨idx a.toAdd, idx_lt _, kφ_apply a⟩

end Hyp

theorem kmem_e {a : Array ℕ} {A : Equiv.Perm (Fin 2300)} (ha : Rep 2300 a A)
    (h : inD (dElts ()) a = true) : ∃ k < 81, A = dEltP k := by
  unfold inD at h
  obtain ⟨i, hi, hai⟩ := anyLt_true h
  exact ⟨i, hi, (eqA_iff ha (krep_e hi)).1 hai⟩

theorem kfus :
    ∀ x ∈ co2P, orderOf x = 3 → ∃ h ∈ co2P, ∃ k < 81, h * x * h⁻¹ = dEltP k := by
  intro x hx hxo
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨g, hgP, hgQ⟩ := Co3T.exists_conj_mem_of_full kQg_le
    (by rw [kcard_Qg, factorization_card_co2P_three]; norm_num) hx hxo
  set t := g⁻¹ * x * g with htdef
  have hto : orderOf t = 3 := by
    have := (MulAut.conj g⁻¹ : Equiv.Perm (Fin 2300) ≃* Equiv.Perm (Fin 2300)).orderOf_eq x
    simpa [MulAut.conj_apply, htdef, hxo] using this
  have ht3 : t ^ 3 = 1 := hto ▸ pow_orderOf_eq_one t
  have ht1 : t ≠ 1 := fun h => by rw [h, orderOf_one] at hto; omega
  obtain ⟨k, hk, hkt⟩ := (kmem_Qg_iff t).1 hgQ
  have hrep : Rep 2300 (qCert2 ()).pts[k]! t := by
    rw [← hkt]
    exact rep_of_validA (kqPts_valid k hk)
  rcases fus_parts hk with h | h | h | ⟨i, hi, h⟩
  · rw [(eqA_iff (rep_powArr hrep 3) rep_idA).2 ht3] at h
    exact absurd h (by decide)
  · exact absurd ((eqA_iff hrep rep_idA).1 h) ht1
  · obtain ⟨e, he, hte⟩ := kmem_e hrep h
    exact ⟨g⁻¹, co2P.inv_mem hgP, e, he, by rw [inv_inv]; exact hte⟩
  · obtain ⟨hgood, hinv, hs⟩ := hM_facts hi
    have hv := validA_inv hinv
    set H := permOfArr 2300 (permOfMat 22 co2FiveV (HM i))
    have hHmem : H ∈ co2P := mem_co2P_of_inP (rep_of_validA hv) hs
    obtain ⟨e, he, hte⟩ := kmem_e (rep_conjA hv hrep) h
    refine ⟨H * g⁻¹, co2P.mul_mem hHmem (co2P.inv_mem hgP), e, he, ?_⟩
    have hkey : H * g⁻¹ * x * (H * g⁻¹)⁻¹ = H * t * H⁻¹ := by
      rw [htdef]
      group
    rw [hkey]
    exact hte

end CertificateChecks.KernelCo2Three

end
