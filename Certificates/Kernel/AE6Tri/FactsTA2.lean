module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7.CertQ8
public import CFSG.Certificates.Kernel.AE6TriSoundB
public import Certificates.Kernel.AE6Tri.ChecksTAQ
public import Certificates.Kernel.AE6Tri.FactsG

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelAE6Tri

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.AE6Tri CFSG.KD.AE6Tri CFSG.KD.AE6TA
open CertificateChecks.KernelAE6TriTA
open CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
open CFSG.EvenSmallLie.OmegaEight (omegaT)
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6S

@[expose] def taQ : Set AE6Om :=
  {x | ∃ J ∈ ae6ConjIn (ae6LetterSub ↑(ae6EdgeLetters 0 1)) ae6ModelK, x ∈ J ∧ orderOf x = 4}

theorem taEL_iff : ∀ i : Fin 8, i ∈ ae6EdgeLetters 0 1 ↔ i.val ∈ taEL := by decide

theorem taEL_lt : ∀ c ∈ taEL, c < 8 := by decide

theorem wv_letterSub {A : Set (Fin 8)} : ∀ w : List Nat,
    (∀ c ∈ w, ∃ h : c < 8, (⟨c, h⟩ : Fin 8) ∈ A) →
      ∃ m ∈ ae6LetterSub A, (m : Equiv.Perm (Fin 360)) = wv gP w
  | [], _ => ⟨1, Subgroup.one_mem _, rfl⟩
  | c :: w, h => by
    obtain ⟨hc, hcA⟩ := h c (by simp)
    obtain ⟨m, hm, hmw⟩ := wv_letterSub w fun d hd => h d (by simp [hd])
    refine ⟨A6.curtisGen ⟨c, hc⟩ * m, Subgroup.mul_mem _ (gen_mem_letterSub hcA) hm, ?_⟩
    rw [Subgroup.coe_mul, hmw, coe_curtisGen, wv_cons]

theorem conj_inv_of {S : Finset (Equiv.Perm (Fin 360))} {h : Equiv.Perm (Fin 360)}
    (hS : ∀ p ∈ S, h * p * h⁻¹ ∈ S) : ∀ p ∈ S, h⁻¹ * p * h⁻¹⁻¹ ∈ S := by
  have hsub : S.image (fun p => h * p * h⁻¹) ⊆ S := by
    intro q hq
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hq
    exact hS p hp
  have hinj : Function.Injective fun p : Equiv.Perm (Fin 360) => h * p * h⁻¹ := by
    intro a b hab
    simpa using hab
  have he := Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_image_of_injective _ hinj])
  intro p hp
  rw [← he] at hp
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hp
  simpa [mul_assoc] using hq

section Quat

variable {ℓ : Nat → Equiv.Perm (Fin 360)}

@[expose] noncomputable def lset (ℓ : Nat → Equiv.Perm (Fin 360)) : Finset (Equiv.Perm (Fin 360)) :=
  (Finset.range 168).image ℓ

theorem mem_lset {p : Equiv.Perm (Fin 360)} : p ∈ lset ℓ ↔ ∃ a < 168, ℓ a = p := by
  simp [lset]

theorem edge_conj
    (hτ : ∀ c ∈ taEL, ∀ a < 168, tq taTau c a < 168 ∧ ℓ (tq taTau c a) = gP c * ℓ a * (gP c)⁻¹) :
    ∀ h ∈ ae6LetterSub ↑(ae6EdgeLetters 0 1), ∀ p ∈ lset ℓ,
      (h : Equiv.Perm (Fin 360)) * p * (h : Equiv.Perm (Fin 360))⁻¹ ∈ lset ℓ := by
  intro h hh
  induction hh using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨i, hi, rfl⟩ := hx
    intro p hp
    obtain ⟨a, ha, rfl⟩ := mem_lset.1 hp
    have hi' := (taEL_iff i).1 hi
    obtain ⟨h1, h2⟩ := hτ i.val hi' a ha
    rw [coe_curtisGen, ← h2]
    exact mem_lset.2 ⟨_, h1, rfl⟩
  | one => intro p hp; simpa using hp
  | mul x y _ _ hx hy =>
    intro p hp
    have := hx _ (hy p hp)
    simpa [mul_assoc] using this
  | inv x _ hx =>
    intro p hp
    have := conj_inv_of hx p hp
    simpa using this

theorem wv_append (g : Nat → Equiv.Perm (Fin 360)) (u v : List Nat) :
    wv g (u ++ v) = wv g u * wv g v := by
  simp [wv, List.prod_append]

theorem taKW_eq : taKW = [taKw1, taKw1 ++ taKw1 ++ taKw1, nthD taKW [] 2,
    nthD taKW [] 2 ++ nthD taKW [] 2 ++ nthD taKW [] 2, taKw1 ++ nthD taKW [] 2,
    nthD taKW [] 2 ++ taKw1] := by decide

theorem taKw1_eq : taKw1 = tg0.getD 0 [] := by decide

theorem taPW0 : taPW.getD 0 [] = [0] ∧ nthN taPO 0 = 4 ∧ 0 < taPW.length := by decide

theorem k0_facts (hℓ : LRep taLL ℓ) (h0 : ℓ 0 = wv gP taKw1)
    (hK : ∀ i < taKW.length, nthN taKI i < 168 ∧ ℓ (nthN taKI i) = wv gP (taKW.getD i []))
    (hT : ∀ i < tg0.length, nthN taTI i < 168 ∧ ℓ (nthN taTI i) = wv gP (tg0.getD i []))
    (hP : prof ℓ taB taPW taPO taPS taPM (nthN taTI)) {i j : Equiv.Perm (Fin 360)}
    (hi : wv gP taKw1 = i) (hj : wv gP (nthD taKW [] 2) = j) :
    CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S5.Q8Rel i j ∧
    ∀ x ∈ Subgroup.closure ({i, j} : Set (Equiv.Perm (Fin 360))), orderOf x = 4 → x ∈ lset ℓ := by
  have hKl : taKW.length = 6 := by decide
  have hk : ∀ t < 6, ℓ (nthN taKI t) = wv gP (taKW.getD t []) ∧ nthN taKI t < 168 :=
    fun t ht => ⟨(hK t (by omega)).2, (hK t (by omega)).1⟩
  have e0 : ℓ (nthN taKI 0) = i := by
    rw [(hk 0 (by norm_num)).1, taKW_eq, ← hi]
    rfl
  have e1 : ℓ (nthN taKI 1) = i * i * i := by
    rw [(hk 1 (by norm_num)).1, taKW_eq]
    change wv gP (taKw1 ++ taKw1 ++ taKw1) = _
    rw [wv_append, wv_append, hi]
  have e2 : ℓ (nthN taKI 2) = j := by
    rw [(hk 2 (by norm_num)).1, taKW_eq, ← hj]
    rfl
  have e3 : ℓ (nthN taKI 3) = j * j * j := by
    rw [(hk 3 (by norm_num)).1, taKW_eq]
    change wv gP (nthD taKW [] 2 ++ nthD taKW [] 2 ++ nthD taKW [] 2) = _
    rw [wv_append, wv_append, hj]
  have e4 : ℓ (nthN taKI 4) = i * j := by
    rw [(hk 4 (by norm_num)).1, taKW_eq]
    change wv gP (taKw1 ++ nthD taKW [] 2) = _
    rw [wv_append, hi, hj]
  have e5 : ℓ (nthN taKI 5) = j * i := by
    rw [(hk 5 (by norm_num)).1, taKW_eq]
    change wv gP (nthD taKW [] 2 ++ taKw1) = _
    rw [wv_append, hi, hj]
  have ho : orderOf i = 4 := by
    obtain ⟨hw, hpo, hlen⟩ := taPW0
    have h := (hP 0 hlen).1
    rw [hw, hpo] at h
    have ht := (hT 0 (by decide)).2
    rw [← taKw1_eq, hi] at ht
    simpa [ht] using h
  have hi4 : i ^ 4 = 1 := by rw [← ho]; exact pow_orderOf_eq_one i
  have hi2 : i ^ 2 ≠ 1 := by
    intro h
    have := orderOf_dvd_of_pow_eq_one h
    rw [ho] at this
    norm_num at this
  have hq := kTaQ8
  rw [Orb.strictB_eq, Orb.strictB_eq, Orb.strictB_eq] at hq
  have hpt := allN_spec hq
  have hr : ∀ x : Fin 360, (i * i) x = (j * j) x ∧ (i * j) x = (j * (i * i * i)) x := by
    intro x
    have hb := hpt x.val x.isLt
    rw [Orb.bAnd_eq, Bool.and_eq_true] at hb
    obtain ⟨h1, h2⟩ := hb
    rw [Nat.beq_eq] at h1 h2
    have r0 := hℓ _ (hk 0 (by norm_num)).2
    have r1 := hℓ _ (hk 1 (by norm_num)).2
    have r2 := hℓ _ (hk 2 (by norm_num)).2
    rw [e0] at r0
    rw [e1] at r1
    rw [e2] at r2
    simp only [ap] at h1 h2
    rw [r0, r0, r2, r2] at h1
    rw [r2, r0, r1, r2] at h2
    exact ⟨Fin.ext h1, Fin.ext h2⟩
  have hij : i * i = j * j := Equiv.ext fun x => (hr x).1
  have hij' : i * j = j * (i * i * i) := Equiv.ext fun x => (hr x).2
  have hinv : i * i * i = i⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← hi4]
    simp only [pow_succ, pow_zero, one_mul]
  have hQ : CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S5.Q8Rel i j := by
    refine ⟨hi4, hi2, by rw [pow_two, pow_two, hij], ?_⟩
    rw [mul_assoc, hij', ← mul_assoc, inv_mul_cancel, one_mul, hinv]
  refine ⟨hQ, fun x hx hox => ?_⟩
  rw [CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7Cert.mem_closure_pair_iff hQ] at hx
  have hj4 : j * j * j = j⁻¹ := by
    rw [eq_inv_iff_mul_eq_one]
    calc j * j * j * j = (j * j) * (j * j) := by group
      _ = (i * i) * (i * i) := by rw [hij]
      _ = i ^ 4 := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      _ = 1 := hi4
  simp only [Certificates.S5Rows.q8Span, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [orderOf_one] at hox
    norm_num at hox
  · exfalso
    have : (i ^ 2) ^ 2 = 1 := by rw [← pow_mul]; exact hi4
    have := orderOf_dvd_of_pow_eq_one this
    rw [hox] at this
    norm_num at this
  · exact mem_lset.2 ⟨_, (hk 0 (by norm_num)).2, e0⟩
  · exact mem_lset.2 ⟨_, (hk 1 (by norm_num)).2, by rw [e1, hinv]⟩
  · exact mem_lset.2 ⟨_, (hk 2 (by norm_num)).2, e2⟩
  · exact mem_lset.2 ⟨_, (hk 3 (by norm_num)).2, by rw [e3, hj4]⟩
  · exact mem_lset.2 ⟨_, (hk 4 (by norm_num)).2, e4⟩
  · exact mem_lset.2 ⟨_, (hk 5 (by norm_num)).2, e5⟩

theorem kw1_map : ([2, 4, 2, 0, 2, 6, 2, 4, 2, 0, 2, 6] : List (Fin 8)).map Fin.val = taKw1 := by
  decide

theorem kw2_map : ([0, 2, 4, 0, 2, 0, 6, 2, 0, 2, 4, 2, 6] : List (Fin 8)).map Fin.val =
    nthD taKW [] 2 := by decide

theorem orderOf_conj' {G : Type*} [Group G] (g x : G) : orderOf (g * x * g⁻¹) = orderOf x := by
  have := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective x
  simpa [MulAut.conj_apply] using this

theorem quat_iff (hℓ : LRep taLL ℓ) (h0 : ℓ 0 = wv gP taKw1)
    (hτ : ∀ c ∈ taEL, ∀ a < 168, tq taTau c a < 168 ∧ ℓ (tq taTau c a) = gP c * ℓ a * (gP c)⁻¹)
    (hw : ∀ a < 168, ∃ w : List Nat, (∀ c ∈ w, c ∈ taEL) ∧ ℓ a = wv gP w * ℓ 0 * (wv gP w)⁻¹)
    (hK : ∀ i < taKW.length, nthN taKI i < 168 ∧ ℓ (nthN taKI i) = wv gP (taKW.getD i []))
    (hT : ∀ i < tg0.length, nthN taTI i < 168 ∧ ℓ (nthN taTI i) = wv gP (tg0.getD i []))
    (hP : prof ℓ taB taPW taPO taPS taPM (nthN taTI)) (x : AE6Om) :
    x ∈ taQ ↔ (x : Equiv.Perm (Fin 360)) ∈ lset ℓ := by
  have e1 : ((ae6Word [2, 4, 2, 0, 2, 6, 2, 4, 2, 0, 2, 6] : AE6Om) : Equiv.Perm (Fin 360)) =
      wv gP taKw1 := by rw [coe_ae6Word, kw1_map]
  have e2 : ((ae6Word [0, 2, 4, 0, 2, 0, 6, 2, 0, 2, 4, 2, 6] : AE6Om) : Equiv.Perm (Fin 360)) =
      wv gP (nthD taKW [] 2) := by rw [coe_ae6Word, kw2_map]
  obtain ⟨hQ, hK0⟩ := k0_facts hℓ h0 hK hT hP rfl rfl
  have ho0 : orderOf (wv gP taKw1) = 4 :=
    CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7Cert.orderOf_eq_four_of_q8Rel hQ
  constructor
  · rintro ⟨J, ⟨g, hg, rfl⟩, hxJ, hox⟩
    have hy := mem_conjSub_iff.1 hxJ
    have hyc : ((g⁻¹ * x * g : AE6Om) : Equiv.Perm (Fin 360)) ∈
        Subgroup.closure ({wv gP taKw1, wv gP (nthD taKW [] 2)} : Set (Equiv.Perm (Fin 360))) := by
      have hm : ((g⁻¹ * x * g : AE6Om) : Equiv.Perm (Fin 360)) ∈ ae6ModelK.map omegaT.subtype :=
        ⟨_, hy, rfl⟩
      rw [ae6ModelK, MonoidHom.map_closure, Set.image_pair] at hm
      have ee1 : omegaT.subtype (ae6Word [2, 4, 2, 0, 2, 6, 2, 4, 2, 0, 2, 6]) = wv gP taKw1 := e1
      have ee2 : omegaT.subtype (ae6Word [0, 2, 4, 0, 2, 0, 6, 2, 0, 2, 4, 2, 6]) =
          wv gP (nthD taKW [] 2) := e2
      rw [ee1, ee2] at hm
      exact hm
    have hoy : orderOf ((g⁻¹ * x * g : AE6Om) : Equiv.Perm (Fin 360)) = 4 := by
      rw [Subgroup.orderOf_coe]
      have := orderOf_conj' g⁻¹ x
      rw [inv_inv] at this
      rw [this, hox]
    have hyL := hK0 _ hyc hoy
    have := edge_conj hτ g hg _ hyL
    simpa [mul_assoc] using this
  · intro hx
    obtain ⟨a, ha, hax⟩ := mem_lset.1 hx
    obtain ⟨w, hwE, hwa⟩ := hw a ha
    obtain ⟨m, hm, hmw⟩ := wv_letterSub (A := ↑(ae6EdgeLetters 0 1)) w fun c hc =>
      ⟨taEL_lt c (hwE c hc), Finset.mem_coe.2 ((taEL_iff ⟨c, taEL_lt c (hwE c hc)⟩).2 (hwE c hc))⟩
    have hxe : x = m * ae6Word [2, 4, 2, 0, 2, 6, 2, 4, 2, 0, 2, 6] * m⁻¹ := by
      apply Subtype.ext
      rw [← hax, hwa, h0, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hmw, e1]
    refine ⟨conjSub m ae6ModelK, ⟨m, hm, rfl⟩, ?_, ?_⟩
    · rw [hxe]
      exact conj_mem_conjSub (Subgroup.subset_closure (Set.mem_insert _ _))
    · rw [← Subgroup.orderOf_coe, ← hax, hwa, h0, orderOf_conj', ho0]

end Quat

end CertificateChecks.KernelAE6Tri

end
