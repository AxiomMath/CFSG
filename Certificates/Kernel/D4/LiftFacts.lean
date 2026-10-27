module

public import Certificates.Kernel.D4.LiftChecks
public import Certificates.Kernel.D4.PhiFacts
public import CFSG.Certificates.Kernel.D4LiftSound
public import CFSG.Certificates.Kernel.Spor.PackFld
public import CFSG.LocalAnalysis.StandardType.GGTriD4TwoRow.Model

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelD4

open CFSG.RankThree.PartTwo.Sec4.Item434D42 CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.B3S3K
open CFSG.KC.Misc.ArrEnum CFSG.KC.D4Lift CFSG.KC.BfsPin CFSG.KC.D4K CFSG.Monster.B.Co2
open CFSG.StandardType.TriD4TwoRow CFSG.Monster.B.Fischer CFSG.RankThree.Native
open CFSG.RankThree.PartOne CFSG.RankThree.PartTwo.KFacts.K426 CFSG.Certificates.Native
open CFSG.Monster.B.Co2.Native Subgroup

theorem row_eq : ∀ k < 53, rowArr k = unpack 2457 12 (RX.F k) := by
  intro k hk
  rw [rowArr, RX.eq]
  exact CFSG.KC.Misc.HexFlat.hexTable_sound RX.all k hk

theorem f0_eq : f0Arr () = unpack 2457 12 (RX.F 0) := row_eq 0 (by norm_num)

theorem d4QGens_size' : d4QGens.size = 4 := by simp [d4QGens]

theorem s0Gens_size' : (s0Gens ()).size = 5 := by simp [s0Gens, d4QGens_size']

theorem s0Gens_get {k : ℕ} (hk : k < 4) : (s0Gens ())[k]! = d4QGens[k]! := by
  rw [getElem!_pos (s0Gens ()) k (by rw [s0Gens_size']; omega),
    getElem!_pos d4QGens k (by rw [d4QGens_size']; exact hk)]
  simp [s0Gens, Array.getElem_push, d4QGens_size', hk]

theorem s0Gens_get_four' : (s0Gens ())[4]! = f0Arr () := by
  rw [getElem!_pos (s0Gens ()) 4 (by rw [s0Gens_size']; omega)]
  simp [s0Gens, Array.getElem_push, d4QGens_size']

theorem bindS : BindA 2457 12 (s0Gens ()) ES.ng ES.G := by
  have hng : ES.ng = 5 := Nat.eq_of_beq_eq_true bS.2.2.1
  refine ⟨by rw [hng, s0Gens_size'], fun j hj => ?_⟩
  rw [hng] at hj
  rcases Nat.lt_or_ge j 4 with h4 | h4
  · have e : ES.G j = HX.F j := Nat.eq_of_beq_eq_true (Orb.allN_iff.1 bS.1 j h4)
    rw [s0Gens_get h4, e]
    unfold d4QGens
    rw [fget (by norm_num) h4, Nat.zero_add]
  · obtain rfl : j = 4 := by omega
    rw [s0Gens_get_four', Nat.eq_of_beq_eq_true bS.2.1, f0_eq]

theorem permB_of_ok {p q : ℕ} (h : permOK 2457 12 (mask 12) (2457 * 12) p q = true) :
    permB 2457 12 p = true :=
  permB_of_pp (pp_of_permOK szOK' h)

theorem pSG : ∀ k < ES.ng, permB 2457 12 (ES.G k) = true := fun k hk => by
  rw [Nat.eq_of_beq_eq_true bS.2.2.1] at hk
  rcases Nat.lt_or_ge k 4 with h4 | h4
  · rw [Nat.eq_of_beq_eq_true (Orb.allN_iff.1 bS.1 k h4),
      ← Nat.eq_of_beq_eq_true (Orb.allN_iff.1 bQ.1 k h4)]
    exact Orb.allN_iff.1 pQ k h4
  · obtain rfl : k = 4 := by omega
    rw [Nat.eq_of_beq_eq_true bS.2.1]
    exact permB_of_ok (liftK_sound liftOK).1

theorem okS : bfsK 2457 12 ES.ng ES.G ES.N ES.T ES.E ES.S = true :=
  bfsK_of_slices (L := 27) (K := 9) (C := ES.C) (by decide) (by norm_num) szOK' ES.g ES.csAll ES.t0
    ES.dist (Nat.eq_of_beq_eq_true ES.c0) (Nat.eq_of_beq_eq_true ES.cK) ES.rsAll

theorem hN243 : ES.N = 243 := Nat.eq_of_beq_eq_true bS.2.2.2

theorem enumS : enumOK 2457 (s0Gens ()) d4Keys (s0Cert ()) = true ∧ (s0Cert ()).pts.size = 243 ∧
    ∀ i < 243, (s0Cert ()).pts[i]! = unpack 2457 12 (ES.T i) := by
  have h := enum_of (fuel := 300) bindS pSG okS (mem_base_lt bindsA CA.hl) ES.keys
    (by rw [hN243]; norm_num)
  rw [keys_eq, hN243] at h
  exact h

theorem s0_facts : (s0Cert ()).pts.size = 243 ∧
    (∀ i < 243, Rep 2457 (s0Cert ()).pts[i]! (permOfArr 2457 (s0Cert ()).pts[i]!) ∧
      permOfArr 2457 (s0Cert ()).pts[i]! ∈ closure (permsA 2457 (s0Gens ()))) ∧
    (∀ x ∈ closure (permsA 2457 (s0Gens ())), ∃ i < 243, Rep 2457 (s0Cert ()).pts[i]! x) ∧
    Nat.card (closure (permsA 2457 (s0Gens ()))) = 243 := by
  obtain ⟨h1, h2, -⟩ := enumS
  have hsp := enumOK_spec d4Keys_lt h1
  refine ⟨h2, fun i hi => ?_, fun x hx => ?_, by rw [hsp.2.1, h2]⟩
  · have hv := rep_of_validA (hsp.2.2 i (h2 ▸ hi))
    exact ⟨hv, enumOK_mem d4Keys_lt h1 (h2 ▸ hi) hv⟩
  · obtain ⟨i, hi, hr⟩ := enumOK_exists_rep d4Keys_lt h1 hx
    exact ⟨i, h2 ▸ hi, hr⟩

theorem rep_unpack {p : ℕ} (hp : permB 2457 12 p = true) :
    Rep 2457 (unpack 2457 12 p) (permOfArr 2457 (unpack 2457 12 p)) :=
  rep_of_validA (validA_of hp)

theorem rep_val {p : ℕ} {X : Equiv.Perm (Fin 2457)} (h : Rep 2457 (unpack 2457 12 p) X)
    (x : Fin 2457) : (X x : ℕ) = pg 12 (mask 12) p x :=
  (h x).symm.trans (Orb.unpack_get x.2)

theorem rep_cm {p q : ℕ} {X Y : Equiv.Perm (Fin 2457)} (hX : Rep 2457 (unpack 2457 12 p) X)
    (hY : Rep 2457 (unpack 2457 12 q) Y) : Rep 2457 (unpack 2457 12 (cm 2457 12 p q)) (X * Y) :=
  fun x => by
    rw [Orb.unpack_get x.2]
    unfold cm
    rw [CFSG.KS.PackFld.pg_pcomp (by norm_num) x.2, Equiv.Perm.mul_apply, rep_val hX, rep_val hY]

theorem f0_mem : permOfArr 2457 (f0Arr ()) * d4Phi⁻¹ ∈ d4P := by
  obtain ⟨hF, hsift, -, -⟩ := liftK_sound liftOK
  have hf : Rep 2457 (unpack 2457 12 (RX.F 0)) (permOfArr 2457 (f0Arr ())) := by
    rw [f0_eq]
    exact rep_unpack (permB_of_ok hF)
  have hinv : d4Phi⁻¹ = d4Phi * d4Phi := by
    rw [inv_eq_iff_mul_eq_one, ← mul_assoc, ← pow_three', phi_facts.2.2.1]
  rw [hinv]
  exact mem_d4P_of_sift (rep_cm hf (rep_cm rep_phi rep_phi)) (siftA_ofOK hsift)

theorem base_lt : ∀ t < 7, pg 12 (mask 12) CA.BP t < 2457 := by decide +kernel

theorem mem_base {b : Fin 2457} (hb : b ∈ d4ChainABase) :
    ∃ t < 7, (b : ℕ) = pg 12 (mask 12) CA.BP t := by
  obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hb
  have ht7 : t < 7 := by simpa [d4ChainABase] using ht
  refine ⟨t, ht7, ?_⟩
  rw [← baseA t ht7, d4ChainABaseArr, getElem!_pos _ t (by simpa using ht)]
  simp

theorem d4_eq_one {g : Equiv.Perm (Fin 2457)} (hg : g ∈ d4P)
    (hfix : ∀ t < 7, ∀ x : Fin 2457, (x : ℕ) = pg 12 (mask 12) CA.BP t → g x = x) : g = 1 :=
  eq_one_of_fix_two (by norm_num) (by simp [d4ChainAArrs]) d4ChainABase_nodup rep_d4A rep_d4B
    d4_chain_check.1 hg fun b hb => by
      obtain ⟨t, ht, e⟩ := mem_base hb
      exact hfix t ht b e

theorem s0_le :
    closure (permsA 2457 (s0Gens ())) ≤ d4G := by
  rw [closure_le]
  rintro _ ⟨k, hk, rfl⟩
  have hk5 : k < 5 := by rw [← s0Gens_size']; exact hk
  dsimp only
  rcases Nat.lt_or_ge k 4 with h4 | h4
  · rw [s0Gens_get h4]
    exact d4P_le_d4G (d4Q_le (subset_closure ⟨k, by rw [Set.mem_setOf_eq, d4QGens_size']; exact h4,
      rfl⟩))
  · obtain rfl : k = 4 := by omega
    rw [s0Gens_get_four']
    have h := d4G.mul_mem (d4P_le_d4G f0_mem) d4Phi_mem_d4G
    rwa [inv_mul_cancel_right] at h

theorem card_s0 :
    Nat.card (closure (permsA 2457 (s0Gens ()))) = 3 ^ (Nat.card d4G).factorization 3 := by
  rw [s0_facts.2.2.2, card_d4G, show (634023936 : ℕ) = 3 ^ 5 * 2609152 by norm_num,
    factorization_pow_mulG Nat.prime_three (by norm_num)]
  norm_num

theorem outer_commute
    {z : Equiv.Perm (Fin 2457)} (hzG : z ∈ d4G)
    (hzS : z ∈ closure (permsA 2457 (s0Gens ()))) (hzP : z ∉ d4P) (hz3 : z ^ 3 = 1) :
    ∃ t ∈ d4P, t ≠ 1 ∧ t ^ 2 = 1 ∧ z * t = t * z := by
  obtain ⟨-, -, hI, hpt⟩ := liftK_sound liftOK
  obtain ⟨h1, h2, h3⟩ := enumS
  obtain ⟨i, hi, hzr⟩ := enumOK_exists_rep d4Keys_lt h1 hzS
  rw [h2] at hi
  have hR : Rep 2457 (unpack 2457 12 (ES.T i)) z := by
    rw [← h3 i hi]
    exact hzr
  rw [← hN243] at hi
  rcases hpt i hi with ⟨j, hj, e⟩ | ⟨t, ht, e⟩ | ⟨j, hj, e⟩
  · exfalso
    apply hzP
    obtain ⟨q1, q2, q3⟩ := enumQ
    have hq : Rep 2457 d4QCert.pts[j]! z := by
      rw [q3 j hj, ← e]
      exact hR
    exact d4Q_le (enumOK_mem d4Keys_lt q1 (q2 ▸ hj) hq)
  · exfalso
    apply e
    let x : Fin 2457 := ⟨_, base_lt t ht⟩
    have hx : pg 12 (mask 12) CA.BP t = (x : ℕ) := rfl
    rw [hx, ← rep_val hR x, ← rep_val hR, ← rep_val hR, ← Equiv.Perm.mul_apply,
      ← Equiv.Perm.mul_apply, ← pow_three', hz3, Equiv.Perm.one_apply]
  · obtain ⟨p1, p2, p3, p4⟩ := hI j hj
    set τ := permOfArr 2457 (unpack 2457 12 (RX.F (Nat.add 1 j))) with hτdef
    have hτ : Rep 2457 (unpack 2457 12 (RX.F (Nat.add 1 j))) τ := rep_unpack (permB_of_ok p1)
    have hτP : τ ∈ d4P := mem_d4P_of_sift hτ (siftA_ofOK p2)
    refine ⟨τ, hτP, fun h1 => ?_, ?_, ?_⟩
    · obtain ⟨t, ht, e⟩ := p4
      apply e
      let x : Fin 2457 := ⟨_, base_lt t ht⟩
      have hx : pg 12 (mask 12) CA.BP t = (x : ℕ) := rfl
      rw [hx, ← rep_val hτ x, h1, Equiv.Perm.one_apply]
    · rw [pow_two]
      refine d4_eq_one (d4P.mul_mem hτP hτP) fun t ht x hx => Fin.ext ?_
      rw [Equiv.Perm.mul_apply, rep_val hτ, rep_val hτ, hx]
      exact p3 t ht
    · have hc : (τ * z)⁻¹ * (z * τ) ∈ d4P := by
        have h := conj_mem_d4P (d4G.inv_mem hzG) (d4P.inv_mem hτP)
        rw [inv_inv] at h
        have e : (τ * z)⁻¹ * (z * τ) = z⁻¹ * τ⁻¹ * z * τ := by group
        rw [e]
        exact d4P.mul_mem h hτP
      have h1 := d4_eq_one hc fun t ht x hx => by
        rw [Equiv.Perm.mul_apply, Equiv.Perm.inv_eq_iff_eq]
        apply Fin.ext
        rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, rep_val hR, rep_val hτ, rep_val hτ,
          rep_val hR, hx]
        exact e t ht
      exact (inv_mul_eq_one.1 h1).symm

theorem lift_fact :
    ∀ y ∈ zpowers d4Phi ⊔ d4P, y ∉ d4P → y ^ 3 = 1 →
      ∃ t ∈ d4P, t ≠ 1 ∧ t ^ 2 = 1 ∧ y * t = t * y := by
  intro y hyG hyP hy3
  change y ∈ d4G at hyG
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hy1 : y ≠ 1 := fun h => hyP (h ▸ d4P.one_mem)
  have hyo : orderOf y = 3 := orderOf_eq_prime hy3 hy1
  obtain ⟨g, hg, hgy⟩ := exists_conj_mem_of_card s0_le card_s0 hyG hyo
  have hzP : g⁻¹ * y * g ∉ d4P := by
    have := conj_not_mem_d4P (d4G.inv_mem hg) hyP
    rwa [inv_inv] at this
  have hz3 : (g⁻¹ * y * g) ^ 3 = 1 := by
    rw [show g⁻¹ * y * g = MulAut.conj g⁻¹ y by simp, ← map_pow, hy3, map_one]
  obtain ⟨t, htP, ht1, ht2, htc⟩ := outer_commute (s0_le hgy) hgy hzP hz3
  refine ⟨g * t * g⁻¹, conj_mem_d4P hg htP, fun h => ht1 ?_, ?_, ?_⟩
  · have : t = g⁻¹ * (g * t * g⁻¹) * g := by group
    rw [this, h]
    group
  · rw [show g * t * g⁻¹ = MulAut.conj g t by simp, ← map_pow, ht2, map_one]
  · calc y * (g * t * g⁻¹) = g * ((g⁻¹ * y * g) * t) * g⁻¹ := by group
      _ = g * (t * (g⁻¹ * y * g)) * g⁻¹ := by rw [htc]
      _ = g * t * g⁻¹ * y := by group

theorem lift_facts : (s0Cert ()).pts.size = 243 ∧
    (∀ i < 243, Rep 2457 (s0Cert ()).pts[i]! (permOfArr 2457 (s0Cert ()).pts[i]!) ∧
      permOfArr 2457 (s0Cert ()).pts[i]! ∈ closure (permsA 2457 (s0Gens ()))) ∧
    (∀ x ∈ closure (permsA 2457 (s0Gens ())), ∃ i < 243, Rep 2457 (s0Cert ()).pts[i]! x) ∧
    Nat.card (closure (permsA 2457 (s0Gens ()))) = 243 ∧
    (permOfArr 2457 (f0Arr ()) * d4Phi⁻¹ ∈ d4P) ∧
    
      ∀ y ∈ zpowers d4Phi ⊔ d4P, y ∉ d4P → y ^ 3 = 1 →
        ∃ t ∈ d4P, t ≠ 1 ∧ t ^ 2 = 1 ∧ y * t = t * y :=
  ⟨s0_facts.1, s0_facts.2.1, s0_facts.2.2.1, s0_facts.2.2.2, f0_mem, lift_fact⟩

end CertificateChecks.KernelD4

end
