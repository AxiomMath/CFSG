module

public import CFSG.RankThree.PartTwo.Sec4.Sporadic.J2Local45
public import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeAmbientCentralizerGeneration
public import Certificates.Certificate10019
public import Certificates.Certificate8168
public import Certificates.Certificate8169
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourInvolutions

public section

namespace CFSG.RankThree.PartTwo.Sec4.Sporadic.J2

open CFSG.ComponentClassification.J2Cover CFSG.Certificates CFSG.Certificates.Native
  CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.RankThree.Native CFSG.Monster.B.Mathieu
  CFSG.RankThree.Asc83Table Subgroup
open scoped commutatorElement

theorem chkW_spec : chkW = true :=
  Certificates.certificate8169.1.2.2.2.1

theorem chkS_spec : chkS = true :=
  Certificates.certificate8169.1.2.2.2.2.1

theorem chkVk_spec : chkVk = true :=
  Certificates.certificate8169.1.2.2.2.2.2.2

theorem chkS_parts : chkSConj = true ∧ chkSPieces = true ∧ chkSNorm = true ∧
    chkSVWits = true ∧ chkSTrip = true ∧ chkSDistinct = true ∧ chkSCz = true ∧
    chkSProd = true ∧ chkSP3 = true ∧ chkSP3Onto = true ∧ chkSU = true ∧ chkSLaw = true := by
  have h := chkS_spec
  simp only [chkS, Bool.and_eq_true, and_assoc] at h
  exact h

theorem chkW_0 (i : ℕ) (hi : i < 3) :
    (isInvolA (wg i 0) && isInvolA (wg i 1) && commA (wg i 0) (wg i 1) &&
        !(eqA 315 (wg i 0) (wg i 1)) && commA (wg i 0) zArr && commA (wg i 1) zArr &&
        (aElts.all fun f => (wElts i).all fun w => inW i (conjA 315 f w)) &&
        ((wElts i).all fun u => eqA 315 u (idA 315) ||
          ((aElts.any fun f => eqA 315 (conjA 315 f u) (wg i 0)) &&
            (aElts.any fun f => eqA 315 (conjA 315 f u) (wg i 1)))) &&
        ([0, 1, 2].all fun j => j == i || !(inW j (wg i 0)))) = true := by
  have h := chkW_spec
  simp only [chkW, Bool.and_eq_true] at h
  exact List.all_eq_true.1 h.1 i (by simp; omega)

theorem chkW_1 : allLt cCz.pts.size (fun k =>
    (!(isInvolA cCz.pts[k]! && aElts.all fun f => commA cCz.pts[k]! (conjA 315 f cCz.pts[k]!)) ||
        inW 0 cCz.pts[k]! || inW 1 cCz.pts[k]! || inW 2 cCz.pts[k]!) &&
      [0, 1, 2].all fun i => !(commA cCz.pts[k]! (wg i 0) && commA cCz.pts[k]! (wg i 1)) ||
        inWZ i cCz.pts[k]!) = true := by
  have h := chkW_spec
  simp only [chkW, Bool.and_eq_true] at h
  exact h.2

theorem chkVk_0 : (aElts.all fun f => validA 315 f) = true := by
  have h := chkVk_spec
  simp only [chkVk, Bool.and_eq_true, and_assoc] at h
  exact h.1

theorem chkVk_1 : allLt vWits.size (fun k => okA vWits[k]!) = true := by
  have h := chkVk_spec
  simp only [chkVk, Bool.and_eq_true, and_assoc] at h
  exact h.2.1

theorem chkVk_2 : allLt tripWit.size (fun k => okA tripWit[k]!) = true := by
  have h := chkVk_spec
  simp only [chkVk, Bool.and_eq_true, and_assoc] at h
  exact h.2.2.1

theorem chkVk_3 : ([0, 1, 2].all fun k =>
      [vkArr k 1, vkArr k 2, compA 315 (vkArr k 1) (vkArr k 2)].all fun e =>
        (aElts.any fun f => eqA 315 (conjA 315 f e) (vkArr k 1)) &&
          (aElts.any fun f => eqA 315 (conjA 315 f e) (vkArr k 2))) = true := by
  have h := chkVk_spec
  simp only [chkVk, Bool.and_eq_true, and_assoc] at h
  exact h.2.2.2.1

theorem chkVk_4 : ((List.range 4).all fun a => (List.range 4).all fun b =>
    (List.range 4).all fun c => (List.range 4).all fun a' => (List.range 4).all fun b' =>
      (List.range 4).all fun c' =>
        (a == a' && b == b' && c == c') || !(eqA 315 (phiA a b c) (phiA a' b' c'))) = true := by
  have h := chkVk_spec
  simp only [chkVk, Bool.and_eq_true, and_assoc] at h
  exact h.2.2.2.2

theorem chkS_0 : ([0, 1, 2].all fun i => inCert cP3 cConj[i]! &&
    eqA 315 (conjA 315 cConj[i]! xArr) (compA 315 (powArr 315 zArr i) xArr)) = true := by
  have h := chkS_parts.1
  unfold chkSConj at h
  exact h

theorem chkS_1 : ([(0, 0), (1, 2), (2, 1)].all fun p => inCert (cS p.1) (wg p.2 0) &&
    inCert (cS p.1) (wg p.2 1)) = true := by
  have h := chkS_parts.2.1
  unfold chkSPieces at h
  exact h

theorem chkS_2 : ([0, 1, 2].all fun k => (gensS k).all fun s =>
    inCert (cS k) (conjA 315 zArr s) && inCert (cS k) (conjA 315 xArr s)) = true := by
  have h := chkS_parts.2.2.1
  unfold chkSNorm at h
  exact h

theorem chkS_4 : ((List.range vWitPairs.length).all fun m =>
    inW (vWitPairs.getD m (0, 0)).1 vWits[4 * m]! &&
      inVk (vWitPairs.getD m (0, 0)).2 vWits[4 * m + 1]! &&
      inW (vWitPairs.getD m (0, 0)).1 vWits[4 * m + 2]! &&
      inVk (vWitPairs.getD m (0, 0)).2 vWits[4 * m + 3]! &&
      !(isTwoA (compA 315 vWits[4 * m]! (compA 315 vWits[4 * m + 1]!
        (compA 315 vWits[4 * m + 2]! vWits[4 * m + 3]!))))) = true := by
  have h := chkS_parts.2.2.2.1
  unfold chkSVWits at h
  exact h

theorem chkS_trip : inVk 0 tripWit[0]! = true ∧ inVk 1 tripWit[1]! = true ∧
    inVk 2 tripWit[2]! = true ∧
    (!(isTwoA (compA 315 tripWit[0]! (compA 315 tripWit[1]! tripWit[2]!)))) = true := by
  have h := chkS_parts.2.2.2.2.1
  simp only [chkSTrip, Bool.and_eq_true, and_assoc] at h
  exact h

theorem chkS_distinct : (!(inCert (cS 1) (vkArr 1 1))) = true ∧
    (!(inCert (cS 2) (vkArr 0 1))) = true ∧ (!(inCert (cS 0) (vkArr 2 1))) = true := by
  have h := chkS_parts.2.2.2.2.2.1
  simp only [chkSDistinct, Bool.and_eq_true, and_assoc] at h
  exact h

theorem chkS_12 : allLt (cS 0).pts.size (fun k =>
    !(commA (cS 0).pts[k]! zArr) || inW 0 (cS 0).pts[k]!) = true := by
  have h := chkS_parts.2.2.2.2.2.2.1
  unfold chkSCz at h
  exact h

theorem chkS_13 : allLt (cS 0).pts.size (fun k => (wElts 0).any fun w =>
      (List.range 4).any fun e => (List.range 4).any fun f =>
        eqA 315 (cS 0).pts[k]! (compA 315 w (compA 315
          (conjA 315 cConj[0]! (if e = 0 then idA 315 else if e = 1 then v1Arr else
            if e = 2 then v2Arr else compA 315 v1Arr v2Arr))
          (conjA 315 cConj[1]! (if f = 0 then idA 315 else if f = 1 then v1Arr else
            if f = 2 then v2Arr else compA 315 v1Arr v2Arr))))) = true := by
  have h := chkS_parts.2.2.2.2.2.2.2.1
  unfold chkSProd at h
  exact h

theorem chkS_14 : allLt cP3.pts.size (fun m => [0, 1, 2].any fun k => (gensS 0).all fun s =>
    inCert (cS k) (conjInvA 315 cP3.pts[m]! s)) = true := by
  have h := chkS_parts.2.2.2.2.2.2.2.2.1
  unfold chkSP3 at h
  exact h

theorem chkS_15 : ([0, 1, 2].all fun k => (List.range cP3.pts.size).any fun m =>
    (gensS 0).all fun s => inCert (cS k) (conjInvA 315 cP3.pts[m]! s)) = true := by
  have h := chkS_parts.2.2.2.2.2.2.2.2.2.1
  unfold chkSP3Onto at h
  exact h

theorem chkS_16 : ((List.range 4).all fun j => inCert (cS 0) u34Gens[j]!) = true := by
  have h := chkS_parts.2.2.2.2.2.2.2.2.2.2.1
  unfold chkSU at h
  exact h

theorem chkS_17 : ((List.range 4).all fun a => (List.range 4).all fun b =>
    (List.range 4).all fun c => (List.range 4).all fun a' => (List.range 4).all fun b' =>
      (List.range 4).all fun c' =>
        eqA 315 (compA 315 (phiA a b c) (phiA a' b' c'))
          (phiA (a ^^^ a') (b ^^^ b') (c ^^^ c' ^^^ mulCode4 a' b))) = true := by
  have h := chkS_parts.2.2.2.2.2.2.2.2.2.2.2
  unfold chkSLaw at h
  exact h

theorem enumS (k : ℕ) (hk : k < 3) :
    enumOK 315 (gensS k) keyPts (cS k) = true ∧ (cS k).pts.size = 64 := by
  have h := List.all_eq_true.1 enum45.2.2.2.2.2.2.2.2.2.2 k (by simp; omega)
  rw [Bool.and_eq_true, beq_iff_eq] at h
  exact h

theorem card_E0 : Nat.card E0 = 3 ^ 2 :=
  (ex27Basis x_cube y_cube z_comm_x z_comm_y z_ne_one 0).card.trans (by norm_num)

theorem E0_comm {a : GJ} (ha : a ∈ E0) {b : GJ} (hb : b ∈ E0) : a * b = b * a := by
  have hb' : b ∈ centralizer ((E0 : Subgroup GJ) : Set GJ) := by rw [centralizer_E0]; exact hb
  exact mem_centralizer_iff.mp hb' a ha

theorem aElt_spec {f : Array ℕ} (hf : f ∈ aElts) :
    ∃ e ∈ E0, Rep 315 f e.1 ∧ validA 315 f = true := by
  have hv := List.all_eq_true.1 chkVk_0 f hf
  simp only [aElts, List.mem_flatMap, List.mem_map, List.mem_range] at hf
  obtain ⟨a, -, c, -, rfl⟩ := hf
  exact ⟨⁅xJ, yJ⁆ ^ a * xJ ^ c, E0.mul_mem (E0.pow_mem z_mem_E0 a) (E0.pow_mem x_mem_E0 c),
    rep_mul (rep_pow rep_z' a) (rep_pow rep_x c), hv⟩

theorem cConj_size : cConj.size = 3 := rfl

theorem ok_c (k : Fin 3) : okA cConj[k.1]! = true := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ := elts45
  exact allLt_spec h (by rw [cConj_size]; exact k.2)

@[expose] noncomputable def cJ (k : Fin 3) : GJ := eltOf cConj[k.1]! (ok_c k)

theorem rep_c (k : Fin 3) : Rep 315 cConj[k.1]! (cJ k).1 := rep_eltOf _

theorem valid_c (k : Fin 3) : validA 315 cConj[k.1]! = true := (okA_spec (ok_c k)).1

@[expose] noncomputable def aJ (k : Fin 3) : GJ := zJ ^ k.1 * xJ

theorem c_spec (k : Fin 3) : cJ k ∈ P3 ∧ cJ k * xJ * (cJ k)⁻¹ = aJ k := by
  have h := List.all_eq_true.1 chkS_0 k.1 (by fin_cases k <;> simp)
  rw [Bool.and_eq_true] at h
  exact ⟨mem_P3_of_inCert (rep_c k) h.1,
    eq_of_rep (rep_conj (rep_c k) (valid_c k) rep_x) (rep_mul (rep_pow rep_z k.1) rep_x) h.2⟩

theorem conj_c_a (k : Fin 3) : (cJ k)⁻¹ * aJ k * cJ k = xJ := by
  rw [← (c_spec k).2]
  group

theorem aJ_mem_E0 (k : Fin 3) : aJ k ∈ E0 :=
  E0.mul_mem (E0.pow_mem zJ_mem_E0 _) x_mem_E0

@[expose] noncomputable def VkJ (k : Fin 3) : Subgroup GJ :=
  VJ.map (MulAut.conj (cJ k)).toMonoidHom

theorem mem_Vk {k : Fin 3} {g : GJ} : g ∈ VkJ k ↔ (cJ k)⁻¹ * g * cJ k ∈ VJ := by
  constructor
  · rintro ⟨v, hv, rfl⟩
    rw [show (cJ k)⁻¹ * (MulAut.conj (cJ k)).toMonoidHom v * cJ k = v by
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group]
    exact hv
  · intro h
    refine ⟨_, h, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

theorem isPGroup_Vk (k : Fin 3) : IsPGroup 2 (VkJ k) := isPGroup_V.map _

theorem Vk_le_C (k : Fin 3) : VkJ k ≤ centralizer ({aJ k} : Set GJ) := by
  intro g hg
  have hv := V_le_C (mem_Vk.1 hg)
  rw [mem_centralizer_singleton_iff] at hv ⊢
  have e1 : g = cJ k * ((cJ k)⁻¹ * g * cJ k) * (cJ k)⁻¹ := by group
  have e2 : aJ k = cJ k * xJ * (cJ k)⁻¹ := (c_spec k).2.symm
  rw [e1, e2]
  calc cJ k * ((cJ k)⁻¹ * g * cJ k) * (cJ k)⁻¹ * (cJ k * xJ * (cJ k)⁻¹) =
      cJ k * ((cJ k)⁻¹ * g * cJ k * xJ) * (cJ k)⁻¹ := by group
    _ = cJ k * (xJ * ((cJ k)⁻¹ * g * cJ k)) * (cJ k)⁻¹ := by rw [hv]
    _ = cJ k * xJ * (cJ k)⁻¹ * (cJ k * ((cJ k)⁻¹ * g * cJ k) * (cJ k)⁻¹) := by group

theorem mem_Vk_of_two {k : Fin 3} {g : GJ} (hg : g ∈ centralizer ({aJ k} : Set GJ))
    (h2 : g ^ 2 ^ 7 = 1) : g ∈ VkJ k := by
  rw [mem_Vk]
  refine mem_V_of_two ?_ ?_
  · rw [mem_centralizer_singleton_iff] at hg ⊢
    calc (cJ k)⁻¹ * g * cJ k * xJ = (cJ k)⁻¹ * g * cJ k * ((cJ k)⁻¹ * aJ k * cJ k) := by
          rw [conj_c_a]
      _ = (cJ k)⁻¹ * (g * aJ k) * cJ k := by group
      _ = (cJ k)⁻¹ * (aJ k * g) * cJ k := by rw [hg]
      _ = (cJ k)⁻¹ * aJ k * cJ k * ((cJ k)⁻¹ * g * cJ k) := by group
      _ = xJ * ((cJ k)⁻¹ * g * cJ k) := by rw [conj_c_a]
  · have h := conj_pow (i := 2 ^ 7) (a := (cJ k)⁻¹) (b := g)
    rw [inv_inv] at h
    rw [h, h2, mul_one, inv_mul_cancel]

theorem pCore_centralizer_a (k : Fin 3) :
    inSubgroup (CFSG.pCore 2) (centralizer ({aJ k} : Set GJ)) = VkJ k := by
  have hn : ((VkJ k).subgroupOf (centralizer ({aJ k} : Set GJ))).Normal := by
    constructor
    intro v hv c
    rw [mem_subgroupOf] at hv ⊢
    have hc : (c : GJ) * v * (c : GJ)⁻¹ ∈ centralizer ({aJ k} : Set GJ) :=
      mul_mem (mul_mem c.2 (Vk_le_C k hv)) (inv_mem c.2)
    refine mem_Vk_of_two hc (pow128 ⟨1, ?_⟩)
    have hvv : (v : GJ) * v = 1 := by
      have := mul_self_of_mem_kleinSub (mem_Vk.1 hv)
      calc (v : GJ) * v = cJ k * (((cJ k)⁻¹ * v * cJ k) * ((cJ k)⁻¹ * v * cJ k)) * (cJ k)⁻¹ := by
            group
        _ = 1 := by rw [this, mul_one, mul_inv_cancel]
    rw [pow_one, sq]
    show (c : GJ) * v * (c : GJ)⁻¹ * ((c : GJ) * v * (c : GJ)⁻¹) = 1
    rw [show (c : GJ) * v * (c : GJ)⁻¹ * ((c : GJ) * v * (c : GJ)⁻¹) =
      (c : GJ) * (v * v) * (c : GJ)⁻¹ by group, hvv, mul_one, mul_inv_cancel]
  exact inSubgroup_pCore_eq (Vk_le_C k) hn (isPGroup_Vk k) fun w hw => by
    obtain ⟨hwH, h2⟩ := two_of_mem_inSubgroup_pCore hw
    exact mem_Vk_of_two hwH (pow128 h2)

@[expose] noncomputable def vkE (k : Fin 3) (i : ℕ) : GJ :=
  cJ k * (if i = 1 then v1J else v2J) * (cJ k)⁻¹

theorem rep_vkE (k : Fin 3) (i : ℕ) : Rep 315 (vkArr k.1 i) (vkE k i).1 := by
  unfold vkArr vkE
  split_ifs
  · exact rep_conj (rep_c k) (valid_c k) rep_v1
  · exact rep_conj (rep_c k) (valid_c k) rep_v2

theorem vkE_mem (k : Fin 3) (i : ℕ) : vkE k i ∈ VkJ k := by
  rw [mem_Vk, vkE]
  rw [show (cJ k)⁻¹ * (cJ k * (if i = 1 then v1J else v2J) * (cJ k)⁻¹) * cJ k =
    (if i = 1 then v1J else v2J) by group]
  split_ifs
  · exact v1_mem_V
  · exact v2_mem_V

theorem mem_Vk_iff {k : Fin 3} {g : GJ} :
    g ∈ VkJ k ↔ g = 1 ∨ g = vkE k 1 ∨ g = vkE k 2 ∨ g = vkE k 1 * vkE k 2 := by
  rw [mem_Vk]
  have e1 : vkE k 1 = cJ k * v1J * (cJ k)⁻¹ := by simp [vkE]
  have e2 : vkE k 2 = cJ k * v2J * (cJ k)⁻¹ := by simp [vkE]
  have hg : g = cJ k * ((cJ k)⁻¹ * g * cJ k) * (cJ k)⁻¹ := by group
  rw [e1, e2]
  constructor
  · intro hm
    rcases mem_kleinSub.1 hm with h | h | h | h
    · left
      rw [hg, h, mul_one, mul_inv_cancel]
    · right; left
      rw [hg, h]
    · right; right; left
      rw [hg, h]
    · right; right; right
      rw [hg, h]
      group
  · rintro (rfl | rfl | rfl | rfl)
    · exact mem_kleinSub.2 (Or.inl (by group))
    · exact mem_kleinSub.2 (Or.inr (Or.inl (by group)))
    · exact mem_kleinSub.2 (Or.inr (Or.inr (Or.inl (by group))))
    · exact mem_kleinSub.2 (Or.inr (Or.inr (Or.inr (by group))))

theorem Vk_le_of_mem {X : Subgroup GJ} (hXE : E0 ≤ normalizer (X : Set GJ)) {k : Fin 3}
    {v : GJ} (hv : v ∈ VkJ k) (hvX : v ∈ X) (hv1 : v ≠ 1) : VkJ k ≤ X := by
  have hall := List.all_eq_true.1 chkVk_3 k.1 (by fin_cases k <;> simp)
  rw [List.all_eq_true] at hall
  have key : ∀ e ∈ [vkArr k.1 1, vkArr k.1 2, compA 315 (vkArr k.1 1) (vkArr k.1 2)],
      Rep 315 e v.1 → vkE k 1 ∈ X ∧ vkE k 2 ∈ X := by
    intro e he hre
    have h := hall e he
    rw [Bool.and_eq_true, List.any_eq_true, List.any_eq_true] at h
    obtain ⟨⟨f0, hf0, h0⟩, ⟨f1, hf1, h1⟩⟩ := h
    obtain ⟨e0, he0, hr0, hv0⟩ := aElt_spec hf0
    obtain ⟨e1, he1, hr1, hv1'⟩ := aElt_spec hf1
    have q0 : e0 * v * e0⁻¹ = vkE k 1 := eq_of_rep (rep_conj hr0 hv0 hre) (rep_vkE k 1) h0
    have q1 : e1 * v * e1⁻¹ = vkE k 2 := eq_of_rep (rep_conj hr1 hv1' hre) (rep_vkE k 2) h1
    refine ⟨?_, ?_⟩
    · rw [← q0]; exact (mem_normalizer_iff.mp (hXE he0) v).mp hvX
    · rw [← q1]; exact (mem_normalizer_iff.mp (hXE he1) v).mp hvX
  have h12 : vkE k 1 ∈ X ∧ vkE k 2 ∈ X := by
    rcases mem_Vk_iff.1 hv with h | h | h | h
    · exact absurd h hv1
    · exact key (vkArr k.1 1) (by simp) (by rw [h]; exact rep_vkE k 1)
    · exact key (vkArr k.1 2) (by simp) (by rw [h]; exact rep_vkE k 2)
    · exact key (compA 315 (vkArr k.1 1) (vkArr k.1 2)) (by simp)
        (by rw [h]; exact rep_mul (rep_vkE k 1) (rep_vkE k 2))
  intro g hg
  rcases mem_Vk_iff.1 hg with h | h | h | h <;> rw [h]
  · exact one_mem _
  · exact h12.1
  · exact h12.2
  · exact mul_mem h12.1 h12.2

theorem piece_a {X : Subgroup GJ} (hX2 : IsPGroup 2 X) (k : Fin 3) :
    X ⊓ centralizer ({aJ k} : Set GJ) ≤ VkJ k :=
  fun _ hy => mem_Vk_of_two hy.2 (pow128 (two_of_mem hX2 hy.1))

theorem Vk_le_of_ne_bot {X : Subgroup GJ} (hX2 : IsPGroup 2 X)
    (hXE : E0 ≤ normalizer (X : Set GJ)) (k : Fin 3)
    (h : X ⊓ centralizer ({aJ k} : Set GJ) ≠ ⊥) : VkJ k ≤ X := by
  obtain ⟨⟨v, hv⟩, hv1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 h
  have hv1' : v ≠ 1 := fun e => hv1 (Subtype.ext e)
  exact Vk_le_of_mem hXE (piece_a hX2 k hv) hv.1 hv1'

theorem chkW_parts (i : Fin 3) : isInvolA (wg i 0) = true ∧ isInvolA (wg i 1) = true ∧
    commA (wg i 0) (wg i 1) = true ∧ (!(eqA 315 (wg i 0) (wg i 1))) = true ∧
    commA (wg i 0) zArr = true ∧ commA (wg i 1) zArr = true ∧
    (aElts.all fun f => (wElts i).all fun w => inW i (conjA 315 f w)) = true ∧
    ((wElts i).all fun u => eqA 315 u (idA 315) ||
      ((aElts.any fun f => eqA 315 (conjA 315 f u) (wg i 0)) &&
        (aElts.any fun f => eqA 315 (conjA 315 f u) (wg i 1)))) = true ∧
    ([0, 1, 2].all fun j => j == i || !(inW j (wg i 0))) = true := by
  have h := chkW_0 i i.2
  simp only [Bool.and_eq_true, and_assoc] at h
  exact h

theorem wGens_size : wGens.size = 6 := rfl

theorem ok_w (i : Fin 3) (j : Fin 2) : okA (wg i j) = true := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ := elts45
  have hi := i.2
  have hj := j.2
  exact allLt_spec h (by rw [wGens_size]; omega)

@[expose] noncomputable def wJ (i : Fin 3) (j : Fin 2) : GJ := eltOf (wg i j) (ok_w i j)

theorem rep_w (i : Fin 3) (j : Fin 2) : Rep 315 (wg i j) (wJ i j).1 := rep_eltOf _

theorem w_sq (i : Fin 3) (j : Fin 2) : wJ i j * wJ i j = 1 := by
  have h : isInvolA (wg i j) = true := by
    fin_cases j
    · exact (chkW_parts i).1
    · exact (chkW_parts i).2.1
  rw [isInvolA, Bool.and_eq_true] at h
  exact eq_of_rep (rep_mul (rep_w i j) (rep_w i j)) rep_one h.1

theorem w_ne_one (i : Fin 3) (j : Fin 2) : wJ i j ≠ 1 := by
  have h : isInvolA (wg i j) = true := by
    fin_cases j
    · exact (chkW_parts i).1
    · exact (chkW_parts i).2.1
  rw [isInvolA, Bool.and_eq_true, Bool.not_eq_true'] at h
  intro he
  have h1 : eqA 315 (wg i j) (idA 315) = true := (eqA_iff (rep_w i j) rep_one).2 (by rw [he])
  rw [h1] at h
  exact Bool.noConfusion h.2

theorem w_comm (i : Fin 3) : wJ i 0 * wJ i 1 = wJ i 1 * wJ i 0 :=
  (commute_of_commA (rep_w i 0) (rep_w i 1) (chkW_parts i).2.2.1).eq

@[expose] noncomputable def WJ (i : Fin 3) : Subgroup GJ :=
  kleinSub (w_sq i 0) (w_sq i 1) (w_comm i)

theorem W_le_Cz (i : Fin 3) : WJ i ≤ centralizer ({zJ} : Set GJ) := by
  have h0 : wJ i 0 ∈ centralizer ({zJ} : Set GJ) := mem_centralizer_singleton_iff.2
    (commute_of_commA (rep_w i 0) rep_z (chkW_parts i).2.2.2.2.1).eq
  have h1 : wJ i 1 ∈ centralizer ({zJ} : Set GJ) := mem_centralizer_singleton_iff.2
    (commute_of_commA (rep_w i 1) rep_z (chkW_parts i).2.2.2.2.2.1).eq
  intro g hg
  rcases mem_kleinSub.1 hg with h | h | h | h <;> rw [h]
  · exact one_mem _
  · exact h0
  · exact h1
  · exact mul_mem h0 h1

theorem wElts_rep {i : Fin 3} {u : Array ℕ} (hu : u ∈ wElts i) : ∃ w ∈ WJ i, Rep 315 u w.1 := by
  simp only [wElts, List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl
  · exact ⟨1, mem_kleinSub.2 (Or.inl rfl), rep_one⟩
  · exact ⟨wJ i 0, mem_kleinSub.2 (Or.inr (Or.inl rfl)), rep_w i 0⟩
  · exact ⟨wJ i 1, mem_kleinSub.2 (Or.inr (Or.inr (Or.inl rfl))), rep_w i 1⟩
  · exact ⟨wJ i 0 * wJ i 1, mem_kleinSub.2 (Or.inr (Or.inr (Or.inr rfl))),
      rep_mul (rep_w i 0) (rep_w i 1)⟩

theorem mem_W_of_inW {i : Fin 3} {t : Array ℕ} {g : GJ} (ht : Rep 315 t g.1)
    (h : inW i t = true) : g ∈ WJ i := by
  rw [inW, List.any_eq_true] at h
  obtain ⟨u, hu, h⟩ := h
  obtain ⟨w, hw, hrw⟩ := wElts_rep hu
  rw [eq_of_rep ht hrw h]
  exact hw

theorem wElts_of_mem {i : Fin 3} {w : GJ} (hw : w ∈ WJ i) : ∃ u ∈ wElts i, Rep 315 u w.1 := by
  rcases mem_kleinSub.1 hw with h | h | h | h <;> rw [h]
  · exact ⟨_, by simp [wElts], rep_one⟩
  · exact ⟨_, by simp [wElts], rep_w i 0⟩
  · exact ⟨_, by simp [wElts], rep_w i 1⟩
  · exact ⟨_, by simp [wElts], rep_mul (rep_w i 0) (rep_w i 1)⟩

theorem W_conj_gens {i : Fin 3} {w : GJ} (hw : w ∈ WJ i) (hw1 : w ≠ 1) :
    (∃ e ∈ E0, e * w * e⁻¹ = wJ i 0) ∧ ∃ e ∈ E0, e * w * e⁻¹ = wJ i 1 := by
  obtain ⟨u, hu, hru⟩ := wElts_of_mem hw
  have h := List.all_eq_true.1 (chkW_parts i).2.2.2.2.2.2.2.1 u hu
  rw [Bool.or_eq_true, Bool.and_eq_true, List.any_eq_true, List.any_eq_true] at h
  rcases h with h | ⟨⟨f0, hf0, h0⟩, ⟨f1, hf1, h1⟩⟩
  · exact absurd (eq_of_rep hru rep_one h) hw1
  obtain ⟨e0, he0, hre0, hve0⟩ := aElt_spec hf0
  obtain ⟨e1, he1, hre1, hve1⟩ := aElt_spec hf1
  exact ⟨⟨e0, he0, eq_of_rep (rep_conj hre0 hve0 hru) (rep_w i 0) h0⟩,
    ⟨e1, he1, eq_of_rep (rep_conj hre1 hve1 hru) (rep_w i 1) h1⟩⟩

theorem pow128_W {i : Fin 3} {w : GJ} (hw : w ∈ WJ i) : w ^ 2 ^ 7 = 1 := by
  rw [show 2 ^ 7 = 2 * 64 by norm_num, pow_mul, sq, mul_self_of_mem_kleinSub hw, one_pow]

theorem mem_W_of_inWZ {i : Fin 3} {t : Array ℕ} {y : GJ} (ht : Rep 315 t y.1)
    (h : inWZ i t = true) (h2 : y ^ 2 ^ 7 = 1) : y ∈ WJ i := by
  rw [inWZ, List.any_eq_true] at h
  obtain ⟨u, hu, h⟩ := h
  rw [List.any_eq_true] at h
  obtain ⟨e, he, h⟩ := h
  rw [List.mem_range] at he
  obtain ⟨w, hw, hrw⟩ := wElts_rep hu
  have hy : y = w * zJ ^ e := eq_of_rep ht (rep_mul hrw (rep_pow rep_z e)) h
  have hwz : Commute w zJ := mem_centralizer_singleton_iff.1 (W_le_Cz i hw)
  have hz : zJ ^ (e * 2 ^ 7) = 1 := by
    rw [hy, (hwz.pow_right e).mul_pow, pow128_W hw, one_mul, ← pow_mul] at h2
    exact h2
  have hdvd := orderOf_dvd_of_pow_eq_one hz
  rw [orderOf_eq_prime z_cube zJ_ne_one] at hdvd
  interval_cases e
  · rw [hy, pow_zero, mul_one]
    exact hw
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)

theorem piece_z {X : Subgroup GJ} (hX2 : IsPGroup 2 X) (hXE : E0 ≤ normalizer (X : Set GJ)) :
    X ⊓ centralizer ({zJ} : Set GJ) = ⊥ ∨ ∃ i : Fin 3, X ⊓ centralizer ({zJ} : Set GJ) = WJ i := by
  set Y := X ⊓ centralizer ({zJ} : Set GJ) with hYdef
  by_cases hY : Y = ⊥
  · exact Or.inl hY
  right
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hY2 : IsPGroup 2 Y := hX2.to_le inf_le_left
  have : Nontrivial Y := (Subgroup.nontrivial_iff_ne_bot Y).2 hY
  have hZ2 : IsPGroup 2 (center Y) := hY2.to_subgroup (center Y)
  have hZn : Nontrivial (center Y) := hY2.center_nontrivial
  obtain ⟨n, hn0, hn⟩ := hZ2.nontrivial_iff_card.1 hZn
  obtain ⟨w0, hw0⟩ := exists_prime_orderOf_dvd_card' (G := center Y) 2
    (by rw [hn]; exact dvd_pow_self 2 (by omega))
  set w : GJ := ((w0 : Y) : GJ) with hwdef
  have hwY : w ∈ Y := (w0 : Y).2
  have hwc : ∀ y ∈ Y, y * w = w * y := fun y hy =>
    congrArg Subtype.val (Subgroup.mem_center_iff.1 w0.2 ⟨y, hy⟩)
  have hw2 : w * w = 1 := by
    have h := pow_orderOf_eq_one w0
    rw [hw0, sq] at h
    exact congrArg (fun q : center Y => ((q : Y) : GJ)) h
  have hw1 : w ≠ 1 := by
    intro h
    have : w0 = 1 := Subtype.ext (Subtype.ext h)
    rw [this, orderOf_one] at hw0
    exact absurd hw0 (by norm_num)
  have hEY : ∀ f ∈ E0, ∀ y ∈ Y, f * y * f⁻¹ ∈ Y := by
    intro f hf y hy
    refine Subgroup.mem_inf.2 ⟨(mem_normalizer_iff.mp (hXE hf) y).mp hy.1,
      mem_centralizer_singleton_iff.2 ?_⟩
    have hfz : f * zJ = zJ * f := E0_comm hf zJ_mem_E0
    have hfz' : f⁻¹ * zJ = zJ * f⁻¹ := (Commute.inv_left (show Commute f zJ from hfz)).eq
    have hyz : y * zJ = zJ * y := mem_centralizer_singleton_iff.1 hy.2
    calc f * y * f⁻¹ * zJ = f * y * (f⁻¹ * zJ) := by group
      _ = f * (y * zJ) * f⁻¹ := by rw [hfz']; group
      _ = f * (zJ * y) * f⁻¹ := by rw [hyz]
      _ = f * zJ * y * f⁻¹ := by group
      _ = zJ * (f * y * f⁻¹) := by rw [hfz]; group
  have hconjc : ∀ f ∈ E0, ∀ y ∈ Y, y * (f * w * f⁻¹) = f * w * f⁻¹ * y := by
    intro f hf y hy
    have hy' : f⁻¹ * y * f ∈ Y := by
      have := hEY f⁻¹ (inv_mem hf) y hy
      simpa using this
    have h := hwc _ hy'
    calc y * (f * w * f⁻¹) = f * (f⁻¹ * y * f * w) * f⁻¹ := by group
      _ = f * (w * (f⁻¹ * y * f)) * f⁻¹ := by rw [h]
      _ = f * w * f⁻¹ * y := by group
  have hwC : w ∈ centralizer ({zJ} : Set GJ) := hwY.2
  rw [centralizer_z] at hwC
  obtain ⟨kw, hkw, hrw⟩ := exists_rep_subOf (by decide) enum_spec.2.2.1 hwC
  have hck := allLt_spec chkW_1 hkw
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hck
  have hinv : isInvolA cCz.pts[kw]! = true := by
    rw [isInvolA, Bool.and_eq_true, Bool.not_eq_true']
    refine ⟨(eqA_iff (rep_mul hrw hrw) rep_one).2 (by rw [hw2]), ?_⟩
    rw [Bool.eq_false_iff]
    intro h
    exact hw1 (eq_of_rep hrw rep_one h)
  have hall : (aElts.all fun f => commA cCz.pts[kw]! (conjA 315 f cCz.pts[kw]!)) = true := by
    rw [List.all_eq_true]
    intro f hf
    obtain ⟨e, he, hre, hve⟩ := aElt_spec hf
    exact commA_of_commute hrw (rep_conj hre hve hrw) (hconjc e he w hwY)
  obtain ⟨i, hwi⟩ : ∃ i : Fin 3, w ∈ WJ i := by
    rcases hck.1 with ((h | h) | h) | h
    · rw [hinv, hall] at h
      exact absurd h Bool.noConfusion
    · exact ⟨0, mem_W_of_inW hrw h⟩
    · exact ⟨1, mem_W_of_inW hrw h⟩
    · exact ⟨2, mem_W_of_inW hrw h⟩
  obtain ⟨⟨e0, he0, he0w⟩, ⟨e1, he1, he1w⟩⟩ := W_conj_gens hwi hw1
  have hw0Y : wJ i 0 ∈ Y := by rw [← he0w]; exact hEY e0 he0 w hwY
  have hw1Y : wJ i 1 ∈ Y := by rw [← he1w]; exact hEY e1 he1 w hwY
  refine ⟨i, le_antisymm ?_ ?_⟩
  · intro y hy
    have c0 : y * wJ i 0 = wJ i 0 * y := by
      have := hconjc e0 he0 y hy
      rwa [he0w] at this
    have c1 : y * wJ i 1 = wJ i 1 * y := by
      have := hconjc e1 he1 y hy
      rwa [he1w] at this
    have hyC := hy.2
    rw [centralizer_z] at hyC
    obtain ⟨ky, hky, hry⟩ := exists_rep_subOf (by decide) enum_spec.2.2.1 hyC
    have hck' := allLt_spec chkW_1 hky
    simp only [Bool.and_eq_true] at hck'
    have hiW := List.all_eq_true.1 hck'.2 i.1 (by fin_cases i <;> simp)
    rw [Bool.or_eq_true, Bool.not_eq_true'] at hiW
    have hcomm : (commA cCz.pts[ky]! (wg i 0) && commA cCz.pts[ky]! (wg i 1)) = true := by
      rw [Bool.and_eq_true]
      exact ⟨commA_of_commute hry (rep_w i 0) c0, commA_of_commute hry (rep_w i 1) c1⟩
    rcases hiW with h | h
    · rw [hcomm] at h
      exact absurd h Bool.noConfusion
    · exact mem_W_of_inWZ hry h (pow128 (two_of_mem hY2 hy))
  · intro u hu
    rcases mem_kleinSub.1 hu with h | h | h | h <;> rw [h]
    · exact one_mem _
    · exact hw0Y
    · exact hw1Y
    · exact mul_mem hw0Y hw1Y

theorem zx_pow_eq (a c n a' c' : ℕ) (h1 : a * n % 3 = a') (h2 : c * n % 3 = c') :
    (zJ ^ a * xJ ^ c) ^ n = zJ ^ a' * xJ ^ c' := by
  have hzx : Commute zJ xJ := by rw [z_eq]; exact z_comm_x
  have hz3 : ∀ m, zJ ^ m = zJ ^ (m % 3) := fun m => by
    conv_lhs => rw [← Nat.mod_add_div m 3, pow_add, pow_mul, z_cube, one_pow, mul_one]
  have hx3 : ∀ m, xJ ^ m = xJ ^ (m % 3) := fun m => by
    conv_lhs => rw [← Nat.mod_add_div m 3, pow_add, pow_mul, x_cube, one_pow, mul_one]
  rw [(hzx.pow_pow a c).mul_pow, ← pow_mul, ← pow_mul, hz3 (a * n), hx3 (c * n), h1, h2]

theorem E0_elt_pow {e : GJ} (he : e ∈ E0) (he1 : e ≠ 1) :
    (∃ n : ℕ, e ^ n = zJ) ∨ ∃ k : Fin 3, ∃ n : ℕ, e ^ n = aJ k := by
  obtain ⟨a, c, ha, hc, rfl⟩ :=
    (ex27Basis x_cube y_cube z_comm_x z_comm_y z_ne_one 0).exists_pow_mul_pow he
  have hEa : (ex27Basis x_cube y_cube z_comm_x z_comm_y z_ne_one 0).a = zJ := z_eq.symm
  have hEb : (ex27Basis x_cube y_cube z_comm_x z_comm_y z_ne_one 0).b = xJ := rfl
  rw [hEa, hEb] at he1 ⊢
  interval_cases a <;> interval_cases c
  · simp at he1
  · exact Or.inr ⟨0, 1, by rw [zx_pow_eq 0 1 1 0 1 rfl rfl]; simp [aJ]⟩
  · exact Or.inr ⟨0, 2, by rw [zx_pow_eq 0 2 2 0 1 rfl rfl]; simp [aJ]⟩
  · exact Or.inl ⟨1, by rw [zx_pow_eq 1 0 1 1 0 rfl rfl]; simp⟩
  · exact Or.inr ⟨1, 1, by rw [zx_pow_eq 1 1 1 1 1 rfl rfl]; simp [aJ]⟩
  · exact Or.inr ⟨2, 2, by rw [zx_pow_eq 1 2 2 2 1 rfl rfl]; simp [aJ]⟩
  · exact Or.inl ⟨2, by rw [zx_pow_eq 2 0 2 1 0 rfl rfl]; simp⟩
  · exact Or.inr ⟨2, 1, by rw [zx_pow_eq 2 1 1 2 1 rfl rfl]; simp [aJ]⟩
  · exact Or.inr ⟨1, 2, by rw [zx_pow_eq 2 2 2 1 1 rfl rfl]; simp [aJ]⟩

theorem inf_centralizer_le_of_pow {X : Subgroup GJ} {m g : GJ} {n : ℕ} (h : m ^ n = g) :
    X ⊓ centralizer ({m} : Set GJ) ≤ X ⊓ centralizer ({g} : Set GJ) := by
  intro y hy
  refine ⟨hy.1, mem_centralizer_singleton_iff.2 ?_⟩
  rw [← h]
  exact (Commute.pow_right (show Commute y m from mem_centralizer_singleton_iff.1 hy.2) n).eq

theorem not_three_dvd {X : Subgroup GJ} (hX2 : IsPGroup 2 X) : ¬ 3 ∣ Nat.card X := by
  obtain ⟨n, hn⟩ := hX2.exists_card_eq
  rw [hn]
  intro h
  have := (Nat.prime_three.dvd_of_dvd_pow h)
  omega

theorem le_sup_pieces {X : Subgroup GJ} (hX2 : IsPGroup 2 X)
    (hXE : E0 ≤ normalizer (X : Set GJ)) :
    X ≤ X ⊓ centralizer ({zJ} : Set GJ) ⊔ X ⊓ centralizer ({aJ 0} : Set GJ) ⊔
      X ⊓ centralizer ({aJ 1} : Set GJ) ⊔ X ⊓ centralizer ({aJ 2} : Set GJ) := by
  have hgen := CFSG.RankThreeEvenClassification.Helpers.coprime_centralizer_generation_of_plane
    3 Nat.prime_three E0 X
    (fun m => Subtype.ext (by
      rw [Subgroup.coe_pow, OneMemClass.coe_one]; exact cube_of_mem_P3 (E0_le_P3 m.2)))
    card_E0 (not_three_dvd hX2) hXE
  refine hgen.le.trans (iSup₂_le fun m hm => ?_)
  have hm1 : (m : GJ) ≠ 1 := fun h => hm (Subtype.ext h)
  rcases E0_elt_pow m.2 hm1 with ⟨n, hn⟩ | ⟨k, n, hn⟩
  · exact (inf_centralizer_le_of_pow hn).trans (le_sup_left.trans (le_sup_left.trans le_sup_left))
  · refine (inf_centralizer_le_of_pow hn).trans ?_
    fin_cases k
    · exact le_sup_right.trans (le_sup_left.trans le_sup_left)
    · exact le_sup_right.trans le_sup_left
    · exact le_sup_right

@[expose] noncomputable def SJ (k : Fin 3) : Subgroup GJ := subOf (gensS k.1)

theorem getElem!_four {α : Type} [Inhabited α] (a b c d : α) :
    #[a, b, c, d][0]! = a ∧ #[a, b, c, d][1]! = b ∧ #[a, b, c, d][2]! = c ∧
      #[a, b, c, d][3]! = d := ⟨rfl, rfl, rfl, rfl⟩

theorem gensS_zero : gensS 0 = #[vkArr 0 1, vkArr 0 2, vkArr 1 1, vkArr 1 2] := rfl

theorem gensS_one : gensS 1 = #[vkArr 0 1, vkArr 0 2, vkArr 2 1, vkArr 2 2] := rfl

theorem gensS_two : gensS 2 = #[vkArr 1 1, vkArr 1 2, vkArr 2 1, vkArr 2 2] := rfl

theorem gensS0 : (gensS 0)[0]! = vkArr 0 1 ∧ (gensS 0)[1]! = vkArr 0 2 ∧
    (gensS 0)[2]! = vkArr 1 1 ∧ (gensS 0)[3]! = vkArr 1 2 := by
  rw [gensS_zero]
  exact getElem!_four _ _ _ _

theorem gensS1 : (gensS 1)[0]! = vkArr 0 1 ∧ (gensS 1)[1]! = vkArr 0 2 ∧
    (gensS 1)[2]! = vkArr 2 1 ∧ (gensS 1)[3]! = vkArr 2 2 := by
  rw [gensS_one]
  exact getElem!_four _ _ _ _

theorem gensS2 : (gensS 2)[0]! = vkArr 1 1 ∧ (gensS 2)[1]! = vkArr 1 2 ∧
    (gensS 2)[2]! = vkArr 2 1 ∧ (gensS 2)[3]! = vkArr 2 2 := by
  rw [gensS_two]
  exact getElem!_four _ _ _ _

theorem gensS_eq (k : Fin 3) (idx : ℕ) (hidx : idx < 4) :
    ∃ j : Fin 3, ∃ i : ℕ, (gensS k.1)[idx]! = vkArr j.1 i := by
  obtain ⟨k, hk⟩ := k
  change ∃ j : Fin 3, ∃ i : ℕ, (gensS k)[idx]! = vkArr j.1 i
  interval_cases k <;> interval_cases idx
  · exact ⟨0, 1, gensS0.1⟩
  · exact ⟨0, 2, gensS0.2.1⟩
  · exact ⟨1, 1, gensS0.2.2.1⟩
  · exact ⟨1, 2, gensS0.2.2.2⟩
  · exact ⟨0, 1, gensS1.1⟩
  · exact ⟨0, 2, gensS1.2.1⟩
  · exact ⟨2, 1, gensS1.2.2.1⟩
  · exact ⟨2, 2, gensS1.2.2.2⟩
  · exact ⟨1, 1, gensS2.1⟩
  · exact ⟨1, 2, gensS2.2.1⟩
  · exact ⟨2, 1, gensS2.2.2.1⟩
  · exact ⟨2, 2, gensS2.2.2.2⟩

theorem gensS_size (k : Fin 3) : (gensS k.1).size = 4 := by
  fin_cases k <;> rfl

theorem gensS_spec (k : Fin 3) :
    ∀ idx < (gensS k.1).size, validA 315 (gensS k.1)[idx]! = true ∧
      inP (gensS k.1)[idx]! = true := by
  intro idx hidx
  refine ⟨enumOK_gens_valid (enumS k.1 k.2).1 hidx, ?_⟩
  obtain ⟨j, i, he⟩ := gensS_eq k idx (lt_of_lt_of_eq hidx (gensS_size k))
  rw [he]
  exact (mem_P_iff (rep_vkE j i)).2 (vkE j i).2

theorem card_S (k : Fin 3) : Nat.card (SJ k) = 64 := by
  rw [SJ, card_subOf (by decide) (enumS k.1 k.2).1 (gensS_spec k), (enumS k.1 k.2).2]

theorem isPGroup_S (k : Fin 3) : IsPGroup 2 (SJ k) := IsPGroup.of_card (n := 6) (by
  rw [card_S]; norm_num)

theorem mem_S_of_rep (k : Fin 3) (idx : ℕ) (hidx : idx < (gensS k.1).size) {g : GJ}
    (hg : Rep 315 (gensS k.1)[idx]! g.1) : g ∈ SJ k := by
  have e : g = gElt (gensS k.1) (gensS_spec k) idx hidx :=
    Subtype.ext (hg.unique (rep_gElt _ _ idx hidx))
  rw [e]
  exact gElt_mem _ _ idx hidx

theorem mem_S_of_inCert {k : Fin 3} {t : Array ℕ} {g : GJ} (ht : Rep 315 t g.1)
    (h : inCert (cS k.1) t = true) : g ∈ SJ k :=
  mem_of_inCert (enumS k.1 k.2).1 ht h

theorem inCert_S {k : Fin 3} {t : Array ℕ} {g : GJ} (ht : Rep 315 t g.1) (hg : g ∈ SJ k) :
    inCert (cS k.1) t = true :=
  inCert_of_mem (enumS k.1 k.2).1 ht hg

theorem Vk_le_S {j k : Fin 3} (i1 i2 : ℕ) (h1 : i1 < (gensS k.1).size)
    (h2 : i2 < (gensS k.1).size) (e1 : (gensS k.1)[i1]! = vkArr j.1 1)
    (e2 : (gensS k.1)[i2]! = vkArr j.1 2) : VkJ j ≤ SJ k := by
  have m1 : vkE j 1 ∈ SJ k := mem_S_of_rep k i1 h1 (by rw [e1]; exact rep_vkE j 1)
  have m2 : vkE j 2 ∈ SJ k := mem_S_of_rep k i2 h2 (by rw [e2]; exact rep_vkE j 2)
  intro g hg
  rcases mem_Vk_iff.1 hg with h | h | h | h <;> rw [h]
  · exact one_mem _
  · exact m1
  · exact m2
  · exact mul_mem m1 m2

theorem gensS_lt (k : Fin 3) {i : ℕ} (hi : i < 4) : i < (gensS k.1).size := by
  rw [gensS_size]
  exact hi

theorem V0_le_S0 : VkJ 0 ≤ SJ 0 :=
  Vk_le_S 0 1 (gensS_lt 0 (by norm_num)) (gensS_lt 0 (by norm_num)) gensS0.1 gensS0.2.1

theorem V1_le_S0 : VkJ 1 ≤ SJ 0 :=
  Vk_le_S 2 3 (gensS_lt 0 (by norm_num)) (gensS_lt 0 (by norm_num)) gensS0.2.2.1 gensS0.2.2.2

theorem V0_le_S1 : VkJ 0 ≤ SJ 1 :=
  Vk_le_S 0 1 (gensS_lt 1 (by norm_num)) (gensS_lt 1 (by norm_num)) gensS1.1 gensS1.2.1

theorem V2_le_S1 : VkJ 2 ≤ SJ 1 :=
  Vk_le_S 2 3 (gensS_lt 1 (by norm_num)) (gensS_lt 1 (by norm_num)) gensS1.2.2.1 gensS1.2.2.2

theorem V1_le_S2 : VkJ 1 ≤ SJ 2 :=
  Vk_le_S 0 1 (gensS_lt 2 (by norm_num)) (gensS_lt 2 (by norm_num)) gensS2.1 gensS2.2.1

theorem V2_le_S2 : VkJ 2 ≤ SJ 2 :=
  Vk_le_S 2 3 (gensS_lt 2 (by norm_num)) (gensS_lt 2 (by norm_num)) gensS2.2.2.1 gensS2.2.2.2

theorem W_le_S {k i : Fin 3} (hp : (k.1, i.1) ∈ ([(0, 0), (1, 2), (2, 1)] : List (ℕ × ℕ))) :
    WJ i ≤ SJ k := by
  have h := List.all_eq_true.1 chkS_1 _ hp
  rw [Bool.and_eq_true] at h
  have m0 : wJ i 0 ∈ SJ k := mem_S_of_inCert (rep_w i 0) h.1
  have m1 : wJ i 1 ∈ SJ k := mem_S_of_inCert (rep_w i 1) h.2
  intro g hg
  rcases mem_kleinSub.1 hg with h | h | h | h <;> rw [h]
  · exact one_mem _
  · exact m0
  · exact m1
  · exact mul_mem m0 m1

theorem W0_le_S0 : WJ 0 ≤ SJ 0 := W_le_S (by decide)

theorem W2_le_S1 : WJ 2 ≤ SJ 1 := W_le_S (by decide)

theorem W1_le_S2 : WJ 1 ≤ SJ 2 := W_le_S (by decide)

theorem E0_le_normalizer_S (k : Fin 3) : E0 ≤ normalizer ((SJ k : Subgroup GJ) : Set GJ) := by
  have hall := List.all_eq_true.1 chkS_2 k.1 (by fin_cases k <;> simp)
  rw [Array.all_eq_true] at hall
  have hS : SJ k = closure {g | ∃ idx, ∃ h : idx < (gensS k.1).size,
      gElt (gensS k.1) (gensS_spec k) idx h = g} := subOf_eq_closure_gElt _ _
  have key : ∀ {f : GJ} {fArr : Array ℕ}, Rep 315 fArr f.1 → validA 315 fArr = true →
      (∀ idx (h : idx < (gensS k.1).size),
        inCert (cS k.1) (conjA 315 fArr (gensS k.1)[idx]) = true) →
      f ∈ normalizer ((SJ k : Subgroup GJ) : Set GJ) := by
    intro f fArr hf hfv hc
    rw [hS]
    refine mem_normalizer_of_conj_gens ?_
    rintro _ ⟨idx, h, rfl⟩
    rw [← hS]
    have hr : Rep 315 (gensS k.1)[idx] (gElt (gensS k.1) (gensS_spec k) idx h).1 := by
      have := rep_gElt (gensS k.1) (gensS_spec k) idx h
      rwa [getElem!_pos _ idx h] at this
    exact mem_S_of_inCert (rep_conj hf hfv hr) (hc idx h)
  have hz : zJ ∈ normalizer ((SJ k : Subgroup GJ) : Set GJ) :=
    key rep_z (okA_spec elts_spec.2.2.1).1 fun idx h => by
      have := hall idx h
      rw [Bool.and_eq_true] at this
      exact this.1
  have hx : xJ ∈ normalizer ((SJ k : Subgroup GJ) : Set GJ) :=
    key rep_x (okA_spec elts_spec.1).1 fun idx h => by
      have := hall idx h
      rw [Bool.and_eq_true] at this
      exact this.2
  rw [show E0 = closure {⁅xJ, yJ⁆, xJ} from rfl, closure_le]
  rintro s (rfl | rfl)
  · rw [← z_eq]; exact hz
  · exact hx

theorem S_mem_invariant (k : Fin 3) : SJ k ∈ invariantPiSubgroups ⊤ E0 (piOf 2) := by
  rw [mem_invariantPiSubgroups_piOf_iff Nat.prime_two]
  exact ⟨le_top, isPGroup_S k, E0_le_normalizer_S k⟩

theorem vWits_size : vWits.size = 12 := rfl

theorem tripWit_size : tripWit.size = 3 := rfl

theorem inVk_spec {k : Fin 3} {t : Array ℕ} {g : GJ} (ht : Rep 315 t g.1)
    (h : inVk k.1 t = true) : g ∈ VkJ k := by
  rw [inVk] at h
  have hr := rep_conjInv (rep_c k) (valid_c k) ht
  rw [mem_Vk]
  exact inV_spec hr h

@[expose] noncomputable def vWitJ (idx : ℕ) (h : idx < 12) : GJ :=
  eltOf vWits[idx]! (allLt_spec chkVk_1 (by rw [vWits_size]; exact h))

theorem rep_vWit (idx : ℕ) (h : idx < 12) : Rep 315 vWits[idx]! (vWitJ idx h).1 := rep_eltOf _

theorem not_pair_of {X : Subgroup GJ} (hX2 : IsPGroup 2 X) (m : ℕ) (hm : m < 3) (i k : Fin 3)
    (hp : vWitPairs.getD m (0, 0) = (i.1, k.1)) (hW : WJ i ≤ X) (hV : VkJ k ≤ X) : False := by
  have h := List.all_eq_true.1 chkS_4 m (List.mem_range.2 (by simpa [vWitPairs] using hm))
  rw [hp] at h
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  have g0 := hW (mem_W_of_inW (rep_vWit (4 * m) (by omega)) h1)
  have g1 := hV (inVk_spec (rep_vWit (4 * m + 1) (by omega)) h2)
  have g2 := hW (mem_W_of_inW (rep_vWit (4 * m + 2) (by omega)) h3)
  have g3 := hV (inVk_spec (rep_vWit (4 * m + 3) (by omega)) h4)
  have hprod := X.mul_mem g0 (X.mul_mem g1 (X.mul_mem g2 g3))
  have h2' := (isTwoA_iff (rep_mul (rep_vWit (4 * m) (by omega)) (rep_mul
    (rep_vWit (4 * m + 1) (by omega)) (rep_mul (rep_vWit (4 * m + 2) (by omega))
      (rep_vWit (4 * m + 3) (by omega)))))).2 (pow128 (two_of_mem hX2 hprod))
  rw [h2'] at h5
  exact Bool.noConfusion h5

theorem not_triple {X : Subgroup GJ} (hX2 : IsPGroup 2 X) (h0 : VkJ 0 ≤ X) (h1 : VkJ 1 ≤ X)
    (h2 : VkJ 2 ≤ X) : False := by
  obtain ⟨t0, t1, t2, t3⟩ := chkS_trip
  have ok : ∀ j (hj : j < 3), okA tripWit[j]! = true := fun j hj =>
    allLt_spec chkVk_2 (by rw [tripWit_size]; exact hj)
  have g0 : eltOf _ (ok 0 (by norm_num)) ∈ X := h0 (inVk_spec (rep_eltOf _) t0)
  have g1 : eltOf _ (ok 1 (by norm_num)) ∈ X := h1 (inVk_spec (rep_eltOf _) t1)
  have g2 : eltOf _ (ok 2 (by norm_num)) ∈ X := h2 (inVk_spec (rep_eltOf _) t2)
  have hprod := X.mul_mem g0 (X.mul_mem g1 g2)
  have h2' := (isTwoA_iff (rep_mul (rep_eltOf (ok 0 (by norm_num)))
    (rep_mul (rep_eltOf (ok 1 (by norm_num))) (rep_eltOf (ok 2 (by norm_num)))))).2
    (pow128 (two_of_mem hX2 hprod))
  rw [Bool.not_eq_true', h2'] at t3
  exact Bool.noConfusion t3

theorem le_S {X : Subgroup GJ} (hX2 : IsPGroup 2 X) (hXE : E0 ≤ normalizer (X : Set GJ)) :
    ∃ k : Fin 3, X ≤ SJ k := by
  have hgen := le_sup_pieces hX2 hXE
  have hA := piece_a hX2
  have hV := Vk_le_of_ne_bot hX2 hXE
  have bot : ∀ {S : Subgroup GJ} {T : Subgroup GJ}, T = ⊥ → T ≤ S := fun h => h ▸ bot_le
  rcases piece_z hX2 hXE with hz | ⟨i, hz⟩
  · by_cases h2 : X ⊓ centralizer ({aJ 2} : Set GJ) = ⊥
    · exact ⟨0, hgen.trans (sup_le (sup_le (sup_le (bot hz) ((hA 0).trans V0_le_S0))
        ((hA 1).trans V1_le_S0)) (bot h2))⟩
    by_cases h1 : X ⊓ centralizer ({aJ 1} : Set GJ) = ⊥
    · exact ⟨1, hgen.trans (sup_le (sup_le (sup_le (bot hz) ((hA 0).trans V0_le_S1))
        (bot h1)) ((hA 2).trans V2_le_S1))⟩
    by_cases h0 : X ⊓ centralizer ({aJ 0} : Set GJ) = ⊥
    · exact ⟨2, hgen.trans (sup_le (sup_le (sup_le (bot hz) (bot h0))
        ((hA 1).trans V1_le_S2)) ((hA 2).trans V2_le_S2))⟩
    exact (not_triple hX2 (hV 0 h0) (hV 1 h1) (hV 2 h2)).elim
  · have hW : WJ i ≤ X := by rw [← hz]; exact inf_le_left
    fin_cases i
    · have h2 : X ⊓ centralizer ({aJ 2} : Set GJ) = ⊥ := by
        by_contra h
        exact not_pair_of hX2 0 (by norm_num) 0 2 rfl hW (hV 2 h)
      have hW0 : X ⊓ centralizer ({zJ} : Set GJ) ≤ SJ 0 := by rw [hz]; exact W0_le_S0
      exact ⟨0, hgen.trans (sup_le (sup_le (sup_le hW0 ((hA 0).trans V0_le_S0))
        ((hA 1).trans V1_le_S0)) (bot h2))⟩
    · have h0 : X ⊓ centralizer ({aJ 0} : Set GJ) = ⊥ := by
        by_contra h
        exact not_pair_of hX2 1 (by norm_num) 1 0 rfl hW (hV 0 h)
      have hW1 : X ⊓ centralizer ({zJ} : Set GJ) ≤ SJ 2 := by rw [hz]; exact W1_le_S2
      exact ⟨2, hgen.trans (sup_le (sup_le (sup_le hW1 (bot h0))
        ((hA 1).trans V1_le_S2)) ((hA 2).trans V2_le_S2))⟩
    · have h1 : X ⊓ centralizer ({aJ 1} : Set GJ) = ⊥ := by
        by_contra h
        exact not_pair_of hX2 2 (by norm_num) 2 1 rfl hW (hV 1 h)
      have hW2 : X ⊓ centralizer ({zJ} : Set GJ) ≤ SJ 1 := by rw [hz]; exact W2_le_S1
      exact ⟨1, hgen.trans (sup_le (sup_le (sup_le hW2 ((hA 0).trans V0_le_S1))
        (bot h1)) ((hA 2).trans V2_le_S1))⟩

theorem vkE_mem_S0 : vkE 1 1 ∈ SJ 0 := V1_le_S0 (vkE_mem 1 1)

theorem S_ne_01 : SJ 0 ≠ SJ 1 := by
  intro h
  have h1 : vkE 1 1 ∈ SJ 1 := h ▸ vkE_mem_S0
  have : inCert (cS 1) (vkArr 1 1) = true := inCert_S (k := 1) (rep_vkE 1 1) h1
  have hd := chkS_distinct.1
  rw [Bool.not_eq_true'] at hd
  rw [this] at hd
  exact Bool.noConfusion hd

theorem S_ne_02 : SJ 0 ≠ SJ 2 := by
  intro h
  have h1 : vkE 0 1 ∈ SJ 2 := h ▸ V0_le_S0 (vkE_mem 0 1)
  have : inCert (cS 2) (vkArr 0 1) = true := inCert_S (k := 2) (rep_vkE 0 1) h1
  have hd := chkS_distinct.2.1
  rw [Bool.not_eq_true'] at hd
  rw [this] at hd
  exact Bool.noConfusion hd

theorem S_ne_12 : SJ 1 ≠ SJ 2 := by
  intro h
  have h1 : vkE 0 1 ∈ SJ 2 := h ▸ V0_le_S1 (vkE_mem 0 1)
  have : inCert (cS 2) (vkArr 0 1) = true := inCert_S (k := 2) (rep_vkE 0 1) h1
  have hd := chkS_distinct.2.1
  rw [Bool.not_eq_true'] at hd
  rw [this] at hd
  exact Bool.noConfusion hd

theorem S_ne_of_lt {a b : Fin 3} (hab : a.1 < b.1) : SJ a ≠ SJ b := by
  obtain ⟨a, ha⟩ := a
  obtain ⟨b, hb⟩ := b
  change a < b at hab
  have : (a = 0 ∧ b = 1) ∨ (a = 0 ∧ b = 2) ∨ (a = 1 ∧ b = 2) := by omega
  rcases this with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact S_ne_01
  · exact S_ne_02
  · exact S_ne_12

theorem S_injective : Function.Injective SJ := by
  intro j k h
  rcases lt_trichotomy j.1 k.1 with hl | he | hl
  · exact absurd h (S_ne_of_lt hl)
  · exact Fin.ext he
  · exact absurd h.symm (S_ne_of_lt hl)

theorem S_le_S {j k : Fin 3} (h : SJ j ≤ SJ k) : j = k :=
  S_injective (Subgroup.eq_of_le_of_card_ge h (by rw [card_S, card_S]))

theorem maxInvariant_E0 :
    maxInvariantPiSubgroups ⊤ E0 (piOf 2) = Set.range SJ := by
  ext X
  rw [mem_maxInvariantPiSubgroups_iff]
  constructor
  · rintro ⟨hX, hmax⟩
    have hX' := hX
    rw [mem_invariantPiSubgroups_piOf_iff Nat.prime_two] at hX'
    obtain ⟨k, hk⟩ := le_S hX'.2.1 hX'.2.2
    exact ⟨k, (hmax _ (S_mem_invariant k) hk)⟩
  · rintro ⟨k, rfl⟩
    refine ⟨S_mem_invariant k, fun Y hY hle => ?_⟩
    rw [mem_invariantPiSubgroups_piOf_iff Nat.prime_two] at hY
    obtain ⟨j, hj⟩ := le_S hY.2.1 hY.2.2
    obtain rfl := S_le_S (hle.trans hj)
    exact le_antisymm hj hle

theorem ncard_maxInvariant_E0 : (maxInvariantPiSubgroups ⊤ E0 (piOf 2)).ncard = 3 := by
  rw [maxInvariant_E0, Set.ncard_eq_three]
  refine ⟨SJ 0, SJ 1, SJ 2, S_ne_01, S_ne_02, S_ne_12, ?_⟩
  ext X
  simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨k, rfl⟩
    fin_cases k
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  · rintro (rfl | rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩

theorem conjugate_S0_le {g : GJ} {t : Array ℕ} (ht : Rep 315 t g.1) (hv : validA 315 t = true)
    {k : Fin 3} (h : (gensS 0).all (fun s => inCert (cS k.1) (conjInvA 315 t s)) = true) :
    conjugate (SJ 0) g = SJ k := by
  apply Subgroup.eq_of_le_of_card_ge
  · rw [conjugate, show SJ 0 = closure {g' | ∃ idx, ∃ h : idx < (gensS (0 : Fin 3).1).size,
        gElt (gensS (0 : Fin 3).1) (gensS_spec 0) idx h = g'} from subOf_eq_closure_gElt _ _,
      MonoidHom.map_closure, closure_le]
    rintro _ ⟨_, ⟨idx, hidx, rfl⟩, rfl⟩
    rw [Array.all_eq_true] at h
    have hr : Rep 315 (gensS 0)[idx] (gElt (gensS (0 : Fin 3).1) (gensS_spec 0) idx hidx).1 := by
      have := rep_gElt (gensS (0 : Fin 3).1) (gensS_spec 0) idx hidx
      rwa [getElem!_pos _ idx hidx] at this
    have hm := mem_S_of_inCert (rep_conjInv ht hv hr) (h idx hidx)
    simpa using hm
  · rw [conjugate, Subgroup.card_map_of_injective (MulAut.conj _).injective, card_S, card_S]

theorem range_S_eq : Set.range SJ = (conjugate (SJ 0)) '' (P3 : Set GJ) := by
  ext X
  constructor
  · rintro ⟨k, rfl⟩
    have h := List.all_eq_true.1 chkS_15 k.1 (by fin_cases k <;> simp)
    rw [List.any_eq_true] at h
    obtain ⟨m, hm, hk⟩ := h
    rw [List.mem_range] at hm
    have hv : validA 315 cP3.pts[m]! = true := (enumOK_spec (by decide) enum_spec.1).2.2 m hm
    have hcl : permOfArr 315 cP3.pts[m]! ∈ Subgroup.closure (permsA 315 gensP3) :=
      ((enumOK_spec (by decide) enum_spec.1).1 _).2 ⟨m, hm, rfl⟩
    have hgs : ∀ j < gensP3.size, validA 315 gensP3[j]! = true ∧ inP gensP3[j]! = true := by
      intro j hj
      have hj2 : j < 2 := hj
      interval_cases j
      · exact okA_spec elts_spec.1
      · exact okA_spec elts_spec.2.1
    set g : GJ := ⟨_, closure_le_P hgs hcl⟩
    have hr : Rep 315 cP3.pts[m]! g.1 := rep_of_validA hv
    have hg : g ∈ P3 := by rw [P3_eq_subOf, mem_subOf]; exact hcl
    exact ⟨g, hg, conjugate_S0_le hr hv hk⟩
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨m, hm, hr⟩ := rep_mem_P3 hg
    have hm' : m < cP3.pts.size := by rw [enum_spec.2.1]; exact hm
    have hv : validA 315 cP3.pts[m]! = true := (enumOK_spec (by decide) enum_spec.1).2.2 m hm'
    have h := allLt_spec chkS_14 hm'
    rw [List.any_eq_true] at h
    obtain ⟨k, hk, hk'⟩ := h
    have hk3 : k < 3 := by simp at hk; omega
    exact ⟨⟨k, hk3⟩, (conjugate_S0_le (k := ⟨k, hk3⟩) hr hv hk').symm⟩

end CFSG.RankThree.PartTwo.Sec4.Sporadic.J2
