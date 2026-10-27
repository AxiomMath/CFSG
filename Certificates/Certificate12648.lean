module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Coordinator.KF148Sig.J2Data
public import CFSG.RankThree.PartTwo.Sec4.Sporadic.J2Base
import Certificates.Certificate8168
import Certificates.Certificate8169
import Certificates.Certificate10019
import Certificates.Kernel.J2Sig12648.Checks
import Certificates.Kernel.J2Sig12648.Small
import Certificates.Kernel.J2Sig12648.TwoChecks
import Certificates.Kernel.Misc.Perm.J2Enum
import CFSG.Certificates.Kernel.J2Sig12648Sound
import CFSG.Certificates.Kernel.Misc.PermClosSound
import CFSG.RankThree.PartTwo.Sec4.Sporadic.J2Local45
import CFSG.Certificates.Kernel.Common.ForallChunks
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.Group
import Mathlib.Tactic.IntervalCases

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ2Sig

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Misc.ArrEnum CFSG.KC.J2Sig
open CFSG.RankThree.PartTwo.Sec4.Sporadic.J2 CFSG.RankThree.Native CFSG.Monster.B.Co2.Native
open CFSG.AGLEmbeddingD2.Wilson.Coordinator.KF148Sig.J2 (vA pairA genSets wordA wordB twoSets)
open CertificateChecks.KernelMisc.J2C3 (X Y Z I AB keyF keys_of_all all_of_chunks)
open CFSG.KC.Misc.Clos (allN_iff anyN_iff allR_iff forall_of_chunks)
open CertificateChecks.KernelMisc.J2M5 (okA_of)

#kc_forall_chunks ch12648zS (fun c => zC c = true) 12 CertificateChecks.KernelJ2Sig.zC 1
#kc_forall_chunks ch12648wS (fun c => wC c = true) 3 CertificateChecks.KernelJ2Sig.wC 1

theorem vfacts {i : ℕ} (hi : i < 18) :
    vA[i]! = unpack 315 9 (VV i) ∧ permB 315 9 (VV i) = true ∧ okA vA[i]! = true := by
  have h1 : vA[i]! = unpack 315 9 (VV i) := by
    interval_cases i <;> exact arrBind_sound (by quickRfl)
  have h2 : permB 315 9 (VV i) = true := by
    interval_cases i <;> quickRfl
  refine ⟨h1, h2, okA_of h1 ?_ ?_ ?_⟩ <;> interval_cases i <;> quickRfl

noncomputable def tV (i : ℕ) : GJ := if h : i < 18 then eltOf vA[i]! (vfacts h).2.2 else 1

theorem rep_tV {i : ℕ} (hi : i < 18) : CFSG.Monster.B.Co2.Rep 315 vA[i]! (tV i).1 := by
  simp only [tV, hi, ↓reduceDIte]
  exact rep_eltOf _

theorem prT {i : ℕ} (hi : i < 18) : PR (VV i) (tV i) :=
  ⟨(vfacts hi).2.1, by rw [← (vfacts hi).1]; exact rep_tV hi⟩

theorem prI : PR I 1 := ⟨KernelMisc.J2C3.pI, by rw [KernelMisc.J2C3.hI]; exact rep_one⟩

theorem prX : PR X xJ := ⟨KernelMisc.J2C3.pX, by rw [← KernelMisc.J2C3.hx]; exact rep_x⟩

theorem prY : PR Y yJ := ⟨KernelMisc.J2C3.pY, by rw [← KernelMisc.J2C3.hy]; exact rep_y⟩

theorem prZ : PR Z zJ := ⟨KernelMisc.J2C3.pZ, by rw [← KernelMisc.J2C3.hz]; exact rep_z⟩

theorem inv3 {a : GJ} (h : a ^ 3 = 1) : a⁻¹ = a * a :=
  inv_eq_of_mul_eq_one_right (by rw [← pow_three]; exact h)

theorem inv3' {a : GJ} (h : a ^ 3 = 1) : (a * a)⁻¹ = a :=
  inv_eq_of_mul_eq_one_right (by rw [← pow_three']; exact h)

theorem prX2 : PR X2 (xJ * xJ) := PR_mul prX prX

theorem prXI : PR X2 xJ⁻¹ := by
  rw [inv3 x_cube]
  exact prX2

theorem prX2I : PR X (xJ * xJ)⁻¹ := by
  rw [inv3' x_cube]
  exact prX

theorem dvd_of_not_three {d m n : ℕ} (hd : d ∣ m * 3 ^ n) (h3 : ¬ 3 ∣ d) : d ∣ m :=
  (Nat.Coprime.pow_right n ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3).symm).dvd_of_dvd_mul_right hd

theorem permB_of_pointK {n w ngen N : ℕ} {G PT : ℕ → ℕ} {E : ℕ → ℕ → ℕ} {PAR LAB : ℕ → ℕ}
    {i : ℕ} (h : pointK n w ngen N G PT E PAR LAB i = true) : permB n w (PT i) = true := by
  unfold pointK at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1

theorem conjE_spec {A t e : ℕ} {a g : GJ} (hA : PR A a) (ha : a ^ 3 = 1) (ht : PR t g)
    (he : e < 3) : PR (conjE A t e) (a ^ e * g * (a ^ e)⁻¹) := by
  interval_cases e
  · rw [pow_zero, one_mul, inv_one, mul_one]
    exact ht
  · rw [pow_one, inv3 ha, mul_assoc]
    exact PR_mul hA (PR_mul ht (PR_mul hA hA))
  · rw [pow_two, inv3' ha, mul_assoc (a * a)]
    exact PR_mul (PR_mul hA hA) (PR_mul ht hA)

theorem orbF : ∀ j < 6, ∀ p < 3, ∀ q < 3, ∃ e < 3, (if j < 3 then zJ else xJ) ^ e *
    tV (3 * j + p) * ((if j < 3 then zJ else xJ) ^ e)⁻¹ = tV (3 * j + q) := by
  intro j hj p hp q hq
  have hA : PR (actP j) (if j < 3 then zJ else xJ) ∧ (if j < 3 then zJ else xJ) ^ 3 = 1 := by
    by_cases h : j < 3
    · have hb : Nat.blt j 3 = true := by rw [Nat.blt_eq]; exact h
      rw [if_pos h]
      unfold actP
      rw [hb]
      exact ⟨prZ, z_cube⟩
    · have hb : Nat.blt j 3 = false := by
        rw [Bool.eq_false_iff, ne_eq, Nat.blt_eq]
        exact h
      rw [if_neg h]
      unfold actP
      rw [hb]
      exact ⟨prX, x_cube⟩
  obtain ⟨e, he, h2⟩ := (anyN_iff _ _).1 ((allN_iff _ _).1 ((allN_iff _ _).1
    ((allN_iff _ _).1 ch12648orb j hj) p hp) q hq)
  exact ⟨e, he, (PR_beq (conjE_spec hA.1 hA.2 (prT (i := 3 * j + p) (by omega)) he)
    (prT (i := 3 * j + q) (by omega))).1 h2⟩

theorem pairB_spec {a b : ℕ} {g h : GJ} (hp : PR (VV a) g) (hq : PR (VV b) h)
    (hb : pairB (a, b) = true) : (g * h) ^ 3 = 1 ∧ g * h ≠ 1 := by
  have hu := PR_mul hp hq
  unfold pairB at hb
  rw [strictB_eq'] at hb
  change Bool.rec (motive := fun _ => Bool) false _ _ = true at hb
  cases e1 : Nat.beq (m9 (m9 (VV a) (VV b)) (m9 (m9 (VV a) (VV b)) (m9 (VV a) (VV b)))) I
  · rw [e1] at hb
    exact absurd hb (by simp)
  · rw [e1] at hb
    refine ⟨?_, fun h1 => ?_⟩
    · rw [pow_three]
      exact (PR_beq (PR_mul hu (PR_mul hu hu)) prI).1 e1
    · have := (PR_beq hu prI).2 h1
      rw [this] at hb
      exact absurd hb (by simp)

theorem pairF : ∀ pq ∈ pairA, (tV pq.1 * tV pq.2) ^ 3 = 1 ∧ tV pq.1 * tV pq.2 ≠ 1 := by
  have hl : pairA.map pairB = [true, true, true] := eq_of_beq ch12648pair
  intro pq hpq
  have hb : pairB pq = true := by
    have h : pairB pq ∈ pairA.map pairB := List.mem_map.2 ⟨pq, hpq, rfl⟩
    rw [hl] at h
    simpa using h
  have hlt : pq.1 < 18 ∧ pq.2 < 18 := by
    simp only [pairA, List.mem_cons, List.not_mem_nil, or_false] at hpq
    rcases hpq with rfl | rfl | rfl <;> exact ⟨by norm_num, by norm_num⟩
  obtain ⟨a, b⟩ := pq
  exact pairB_spec (prT hlt.1) (prT hlt.2) hb

theorem evW_spec : ∀ w : List ℕ, (∀ l ∈ w, l < 18) → PR (evW w) (w.map tV).prod
  | [], _ => by
    rw [List.map_nil, List.prod_nil]
    exact prI
  | l :: w, h => by
    rw [List.map_cons, List.prod_cons]
    exact PR_mul (prT (h l (by simp))) (evW_spec w fun l' hl' => h l' (by simp [hl']))

theorem all_of_map_eq {f : ℕ → Bool} {n : ℕ} (h : (List.range n).map f = List.replicate n true) :
    ∀ s < n, f s = true := by
  intro s hs
  have hm : f s ∈ (List.range n).map f := List.mem_map.2 ⟨s, List.mem_range.2 hs, rfl⟩
  rw [h] at hm
  exact List.eq_of_mem_replicate hm

theorem words_lt : ∀ s < 4, (∀ i ∈ wordA.getD s [], i / 3 ∈ genSets.getD s [] ∧ i < 18) ∧
    (∀ i ∈ wordB.getD s [], i / 3 ∈ genSets.getD s [] ∧ i < 18) := by
  decide

theorem prA : PR (AB 0) CFSG.ComponentClassification.J2Cover.pa :=
  ⟨by quickRfl, by
    rw [← KernelMisc.J2C3.hab 0 (by norm_num)]
    exact CFSG.ComponentClassification.J2Cover.rep_permA⟩

theorem prB : PR (AB 1) CFSG.ComponentClassification.J2Cover.pb :=
  ⟨by quickRfl, by
    rw [← KernelMisc.J2C3.hab 1 (by norm_num)]
    exact CFSG.ComponentClassification.J2Cover.rep_permB⟩

theorem genF {s : ℕ} (hs : s < 4) (K : Subgroup GJ)
    (hK : ∀ j ∈ genSets.getD s [], ∀ q < 3, tV (3 * j + q) ∈ K) : K = ⊤ := by
  have hw := all_of_map_eq (eq_of_beq ch12648words) s hs
  obtain ⟨ha, hb⟩ : Nat.beq (evW (wordA.getD s [])) (AB 0) = true ∧
      Nat.beq (evW (wordB.getD s [])) (AB 1) = true := by
    rcases bIf_true hw with h | ⟨-, h⟩
    · exact h
    · exact absurd h (by decide)
  obtain ⟨hla, hlb⟩ := words_lt s hs
  have hmem : ∀ w : List ℕ, (∀ i ∈ w, i / 3 ∈ genSets.getD s [] ∧ i < 18) →
      (w.map tV).prod ∈ K := by
    intro w hw'
    apply Subgroup.list_prod_mem
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
    have h := hK _ (hw' i hi).1 (i % 3) (Nat.mod_lt _ (by norm_num))
    rwa [Nat.div_add_mod] at h
  have hpa : ((wordA.getD s []).map tV).prod = CFSG.ComponentClassification.J2Cover.pa :=
    (PR_beq (evW_spec _ fun i hi => (hla i hi).2) prA).1 ha
  have hpb : ((wordB.getD s []).map tV).prod = CFSG.ComponentClassification.J2Cover.pb :=
    (PR_beq (evW_spec _ fun i hi => (hlb i hi).2) prB).1 hb
  have haK : CFSG.ComponentClassification.J2Cover.pa ∈ K := by
    rw [← hpa]
    exact hmem _ hla
  have hbK : CFSG.ComponentClassification.J2Cover.pb ∈ K := by
    rw [← hpb]
    exact hmem _ hlb
  have hle : Subgroup.closure ({CFSG.ComponentClassification.J2Cover.permA,
      CFSG.ComponentClassification.J2Cover.permB} : Set (Equiv.Perm (Fin 315))) ≤
      K.map (CFSG.ComponentClassification.J2Cover.P).subtype := by
    rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact ⟨_, haK, rfl⟩
    · exact ⟨_, hbK, rfl⟩
  rw [eq_top_iff]
  intro g _
  obtain ⟨k, hk, hkg⟩ := hle g.2
  rwa [← Subtype.ext hkg]

theorem twoSets_lt : ∀ s < 6, ∀ j ∈ twoSets.getD s [], j < 6 := by decide

theorem two_mem : ∀ s < 6, ∀ k < 3 * (twoSets.getD s []).length,
    (twoSets.getD s []).getD (k / 3) 0 ∈ twoSets.getD s [] := by decide

theorem two_idx : ∀ s < 6, ∀ j ∈ twoSets.getD s [], ∀ q < 3, ∃ k < 3 * (twoSets.getD s []).length,
    (twoSets.getD s []).getD (k / 3) 0 = j ∧ k % 3 = q := by decide

noncomputable def gsT (s ngen : ℕ) : Array (Array ℕ) :=
  Array.ofFn fun k : Fin ngen => unpack 315 9 (GT s k)

theorem gsT_size (s ngen : ℕ) : (gsT s ngen).size = ngen := by simp [gsT]

theorem gsT_get (s : ℕ) {ngen k : ℕ} (hk : k < ngen) :
    (gsT s ngen)[k]! = unpack 315 9 (GT s k) := by
  unfold gsT
  rw [getElem!_pos _ k (by simpa using hk), Array.getElem_ofFn]

theorem GT_facts {s k : ℕ} (hs : s < 6) (hk : k < 3 * (twoSets.getD s []).length) :
    (twoSets.getD s []).getD (k / 3) 0 ∈ twoSets.getD s [] ∧
      unpack 315 9 (GT s k) = vA[3 * (twoSets.getD s []).getD (k / 3) 0 + k % 3]! ∧
      okA vA[3 * (twoSets.getD s []).getD (k / 3) 0 + k % 3]! = true ∧
      CFSG.Monster.B.Co2.Rep 315 vA[3 * (twoSets.getD s []).getD (k / 3) 0 + k % 3]!
        (tV (3 * (twoSets.getD s []).getD (k / 3) 0 + k % 3)).1 := by
  have hm := two_mem s hs k hk
  have hlt : 3 * (twoSets.getD s []).getD (k / 3) 0 + k % 3 < 18 := by
    have := twoSets_lt s hs _ hm
    omega
  exact ⟨hm, (vfacts hlt).1.symm, (vfacts hlt).2.2, rep_tV hlt⟩

theorem two_card {s ngen : ℕ} (hs : s < 6) (hn : 3 * (twoSets.getD s []).length = ngen)
    {P E R L : List ℕ} (hh : headK 315 9 ngen 64 (GT s) (lget P) = true)
    (hp : CFSG.KC.LQT.P.allN 64 (pointK 315 9 ngen 64 (GT s) (lget P)
      (KernelMisc.J2En.EL ngen E) (lget R) (lget L)) = true)
    (hk : CFSG.KC.LQT.P.allN 64 (keyF (lget P)) = true) :
    Nat.card (Subgroup.closure {g : GJ | ∃ j ∈ twoSets.getD s [], ∃ q < 3,
      g = tV (3 * j + q)}) = 64 := by
  have b := KernelMisc.J2En.certL_bound 64 ngen P E R L
  have hen := enumK_sound (G := GT s) (gs := gsT s ngen) hw9 (by decide) (gsT_size s ngen)
    (fun k hk => gsT_get s hk) b.1 b.2.1 b.2.2.1 b.2.2.2 hh ((allN_iff _ _).1 hp)
    (keys_of_all ((allN_iff _ _).1 hk))
  have hspec : ∀ k < (gsT s ngen).size,
      validA 315 (gsT s ngen)[k]! = true ∧
        CFSG.ComponentClassification.J2Cover.inP (gsT s ngen)[k]! = true := by
    intro k hk
    have hkn : k < ngen := lt_of_lt_of_eq hk (gsT_size s ngen)
    have hf := GT_facts hs (k := k) (by omega)
    rw [gsT_get s hkn, hf.2.1]
    exact okA_spec hf.2.2.1
  have heq : Subgroup.closure {g : GJ | ∃ j ∈ twoSets.getD s [], ∃ q < 3, g = tV (3 * j + q)} =
      subOf (gsT s ngen) := by
    apply le_antisymm
    · rw [Subgroup.closure_le]
      rintro _ ⟨j, hj, q, hq, rfl⟩
      obtain ⟨k, hk, hkj, hkq⟩ := two_idx s hs j hj q hq
      have hkn : k < ngen := by omega
      have hf := GT_facts hs hk
      rw [hkj, hkq] at hf
      rw [SetLike.mem_coe, mem_subOf]
      apply Subgroup.subset_closure
      refine ⟨k, lt_of_lt_of_eq hkn (gsT_size s ngen).symm, ?_⟩
      change CFSG.Monster.B.Co2.permOfArr 315 (gsT s ngen)[k]! = (tV (3 * j + q)).1
      rw [gsT_get s hkn, hf.2.1]
      exact (rep_of_validA (okA_spec hf.2.2.1).1).unique hf.2.2.2
    · rw [subOf_eq_closure_gElt _ hspec, Subgroup.closure_le]
      rintro _ ⟨k, hk, rfl⟩
      apply Subgroup.subset_closure
      have hkn : k < ngen := lt_of_lt_of_eq hk (gsT_size s ngen)
      have hf := GT_facts hs (k := k) (by omega)
      refine ⟨_, hf.1, k % 3, Nat.mod_lt _ (by norm_num), ?_⟩
      apply elA_eq_iff
      rw [gsT_get s hkn, hf.2.1]
      exact hf.2.2.2
  rw [heq, card_subOf (by decide) hen hspec, b.1]

theorem twoF : ∀ s < 6, Nat.card (Subgroup.closure
    {g : GJ | ∃ j ∈ twoSets.getD s [], ∃ q < 3, g = tV (3 * j + q)}) = 64 := by
  intro s hs
  interval_cases s
  · exact two_card (ngen := 6) (by norm_num) (by decide) ch12648hd0 ch12648pt0 ch12648ky0
  · exact two_card (ngen := 6) (by norm_num) (by decide) ch12648hd1 ch12648pt1 ch12648ky1
  · exact two_card (ngen := 6) (by norm_num) (by decide) ch12648hd2 ch12648pt2 ch12648ky2
  · exact two_card (ngen := 9) (by norm_num) (by decide) ch12648hd3 ch12648pt3 ch12648ky3
  · exact two_card (ngen := 9) (by norm_num) (by decide) ch12648hd4 ch12648pt4 ch12648ky4
  · exact two_card (ngen := 9) (by norm_num) (by decide) ch12648hd5 ch12648pt5 ch12648ky5

theorem card_cx : Nat.card (Subgroup.centralizer ({xJ} : Set GJ)) = 36 := by
  rw [centralizer_x, card_subOf (by decide) KernelMisc.J2En.enumCa gensCa_spec,
    KernelMisc.J2En.sizeCa]

theorem conj_data {k : ℕ} (hk : k < 3) :
    ∃ a : GJ, PR (cjG k) a ∧ PR (cjGI k) a⁻¹ ∧ a * (xJ * a⁻¹) = zJ ^ k * xJ := by
  have hc := (ch12648cj k hk).1
  interval_cases k
  · refine ⟨1, prI, by rw [inv_one]; exact prI, ?_⟩
    rw [inv_one, pow_zero]
    exact (PR_beq (PR_mul prI (PR_mul prX prI)) (PR_mul prI prX)).1 hc
  · refine ⟨yJ * yJ, PR_mul prY prY, by rw [inv3' y_cube]; exact prY, ?_⟩
    rw [inv3' y_cube, pow_one]
    exact (PR_beq (PR_mul (PR_mul prY prY) (PR_mul prX prY)) (PR_mul prZ prX)).1 hc
  · refine ⟨yJ, prY, by rw [inv3 y_cube]; exact PR_mul prY prY, ?_⟩
    rw [inv3 y_cube, pow_two]
    exact (PR_beq (PR_mul prY (PR_mul prX (PR_mul prY prY))) (PR_mul (PR_mul prZ prZ) prX)).1 hc

theorem cwF {k : ℕ} (hk : k < 3) {g : GJ} (hg : Commute g (zJ ^ k * xJ))
    (h3 : ¬ 3 ∣ orderOf g) : g = 1 ∨ ∃ p < 3, g = tV (3 * k + p) := by
  obtain ⟨a, hG, hGI, hw⟩ := conj_data hk
  have hC : a⁻¹ * g * a ∈ Subgroup.centralizer ({xJ} : Set GJ) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hg' : g * (a * (xJ * a⁻¹)) = a * (xJ * a⁻¹) * g := by
      rw [hw]
      exact hg
    calc a⁻¹ * g * a * xJ = a⁻¹ * (g * (a * (xJ * a⁻¹))) * a := by group
      _ = a⁻¹ * (a * (xJ * a⁻¹) * g) * a := by rw [hg']
      _ = xJ * (a⁻¹ * g * a) := by group
  have ho : orderOf (a⁻¹ * g * a) = orderOf g := by
    have := MulEquiv.orderOf_eq (MulAut.conj a⁻¹) g
    rwa [MulAut.conj_apply, inv_inv] at this
  have h36 : orderOf (a⁻¹ * g * a) ∣ 4 * 3 ^ 2 := by
    have := Subgroup.orderOf_dvd_natCard _ hC
    rw [card_cx] at this
    norm_num
    exact this
  have h4 : (a⁻¹ * g * a) ^ 4 = 1 :=
    orderOf_dvd_iff_pow_eq_one.1 (dvd_of_not_three h36 (by rw [ho]; exact h3))
  rw [centralizer_x] at hC
  obtain ⟨i, hi, hr⟩ := exists_rep_subOf (by decide) KernelMisc.J2En.enumCa hC
  rw [KernelMisc.J2En.sizeCa] at hi
  have e1 : KernelMisc.J2En.cCaL.pts[i]! = unpack 315 9 (lget KernelMisc.J2En.CaP i) :=
    (KernelMisc.J2En.certL_bound 36 2 KernelMisc.J2En.CaP KernelMisc.J2En.CaE
      KernelMisc.J2En.CaR KernelMisc.J2En.CaL).2.1 i hi
  rw [e1] at hr
  have hpt : permB 315 9 (lget KernelMisc.J2En.CaP i) = true :=
    permB_of_pointK (all_of_chunks 36 1 KernelMisc.J2En.ptCaS i (by omega))
  have hwk : wK I (cjG k) (cjGI k) VV (3 * k) (lget KernelMisc.J2En.CaP i) = true :=
    (allR_iff _ _ _).1 (ch12648wS k hk) i (Nat.zero_le _) (by omega)
  have e2 : a * (a⁻¹ * g * a) * a⁻¹ = g := by group
  rcases wK_sound (V := VV) (T := tV) (lo := 3 * k) prI hG hGI
      (fun j hj => prT (i := 3 * k + j) (by omega)) ⟨hpt, hr⟩ hwk h4 with h | ⟨j, hj, h⟩
  · rw [e2] at h
    exact Or.inl h
  · rw [e2] at h
    exact Or.inr ⟨j, hj, h⟩

theorem czF {g : GJ} (hg : Commute g zJ) (h3 : ¬ 3 ∣ orderOf g) :
    g = 1 ∨ (∃ j, 3 ≤ j ∧ j < 6 ∧ ∃ p < 3, g = tV (3 * j + p)) ∨
      ∃ v ∈ Subgroup.closure ({g, xJ * g * xJ⁻¹, (xJ * xJ) * g * (xJ * xJ)⁻¹} : Set GJ),
        orderOf v = 3 := by
  have hgC : g ∈ Subgroup.centralizer ({zJ} : Set GJ) :=
    Subgroup.mem_centralizer_singleton_iff.2 hg
  have h1 : orderOf g ∣ 40 * 3 ^ 3 := by
    have := Subgroup.orderOf_dvd_natCard _ hgC
    rw [card_centralizer_z] at this
    norm_num
    exact this
  have h40 : g ^ 40 = 1 := orderOf_dvd_iff_pow_eq_one.1 (dvd_of_not_three h1 h3)
  rw [centralizer_z] at hgC
  obtain ⟨i, hi, hr⟩ := exists_rep_subOf (by decide) enum_spec.2.2.1 hgC
  rw [enum_spec.2.2.2.1] at hi
  rw [KernelMisc.J2C3.cz.2.1 i hi] at hr
  have hk : zK X X2 X2 X I VV W i (KernelMisc.J2C3.CzP.F i) = true :=
    forall_of_chunks 90 12 _ ch12648zS i hi
  rcases zK_sound (V := VV) (T := tV) prI prX prXI prX2 prX2I
      (fun j hj => prT (i := 9 + j) (by omega)) ⟨KernelMisc.J2C3.czp i hi, hr⟩ hk h40 with
    h | ⟨j, hj, e⟩ | h
  · exact Or.inl h
  · refine Or.inr (Or.inl ⟨3 + j / 3, by omega, by omega, j % 3, Nat.mod_lt _ (by norm_num), ?_⟩)
    rw [e]
    congr 1
    omega
  · exact Or.inr (Or.inr h)

end CertificateChecks.KernelJ2Sig

public section

namespace Certificates

open CertificateChecks

open CFSG.RankThree.PartTwo.Sec4.Sporadic.J2 CertificateChecks.KernelJ2Sig

open CFSG.AGLEmbeddingD2.Wilson.Coordinator.KF148Sig.J2 CFSG.RankThree.PartTwo.Sec4.Sporadic.J2 in
theorem certificate12648 : ∃ T : ℕ → GJ, (∀ i < 18, CFSG.Monster.B.Co2.Rep 315 vA[i]! (T i).1) ∧
    ∀ X Z : GJ, CFSG.Monster.B.Co2.Rep 315 xArr X.1 → CFSG.Monster.B.Co2.Rep 315 zArr Z.1 →
      (∀ j < 6, ∀ p < 3, ∀ q < 3, ∃ e < 3, (if j < 3 then Z else X) ^ e * T (3 * j + p) *
        ((if j < 3 then Z else X) ^ e)⁻¹ = T (3 * j + q)) ∧
      (∀ pq ∈ pairA, (T pq.1 * T pq.2) ^ 3 = 1 ∧ T pq.1 * T pq.2 ≠ 1) ∧
      (∀ s < 4, ∀ K : Subgroup GJ, (∀ j ∈ genSets.getD s [], ∀ q < 3, T (3 * j + q) ∈ K) →
        K = ⊤) ∧
      (∀ s < 6, Nat.card (Subgroup.closure
        {g : GJ | ∃ j ∈ twoSets.getD s [], ∃ q < 3, g = T (3 * j + q)}) = 64) ∧
      (∀ k < 3, ∀ g : GJ, Commute g (Z ^ k * X) → ¬ 3 ∣ orderOf g →
        g = 1 ∨ ∃ p < 3, g = T (3 * k + p)) ∧
      (∀ g : GJ, Commute g Z → ¬ 3 ∣ orderOf g →
        g = 1 ∨ (∃ j, 3 ≤ j ∧ j < 6 ∧ ∃ p < 3, g = T (3 * j + p)) ∨
          ∃ v ∈ Subgroup.closure ({g, X * g * X⁻¹, (X * X) * g * (X * X)⁻¹} : Set GJ),
            orderOf v = 3) := by
  refine ⟨tV, fun i hi => rep_tV hi, fun X' Z' hX hZ => ?_⟩
  obtain rfl : X' = xJ := Subtype.ext (hX.unique rep_x)
  obtain rfl : Z' = zJ := Subtype.ext (hZ.unique rep_z)
  exact ⟨orbF, pairF, fun s hs K hK => genF hs K hK, twoF, fun k hk g hg h3 => cwF hk hg h3,
    fun g hg h3 => czF hg h3⟩

end Certificates

end
