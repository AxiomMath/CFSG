module

public import Certificates.Kernel.Co1Seven.Vals
public import Certificates.Kernel.Co1Seven.Seeds
public import Certificates.Kernel.Co1Seven.Slp
public import CFSG.Certificates.Kernel.SporSch.Co1RankGrpSound
public import CFSG.Certificates.Kernel.Co1Seven.PackEnc

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1Seven

open CFSG.KC.Co1Cl CFSG.KC.Co1B CFSG.Sporadic.Co1Schreier

theorem CH_length : CH.length = 7 := by decide +kernel

theorem GL_eq : KernelCo1Seven.GL = [[617, 1437]] := by decide +kernel

theorem chunks : ∀ j < CH.length, chunkK TS CH WL j = true := by
  rw [CH_length]
  intro j hj
  interval_cases j
  exacts [ch1023013slp0, ch1023013slp1, ch1023013slp2, ch1023013slp3, ch1023013slp4,
    ch1023013slp5, ch1023013slp6]

theorem recK_parts {TS : Nat → Nat} {S : List Nat} {lo k c : Nat} (h : recK TS S lo k c = true) :
    canK (TS k) = true ∧
    (Nat.beq (Nat.land c 1) 1 = true →
      mulWK (TS k) (TS (refK S S.length lo (Nat.land (Nat.shiftRight c 1) 1048575))) = oneK) ∧
    (Nat.beq (Nat.land c 1) 1 = false →
      TS k = mulWK (TS (refK S S.length lo (Nat.land (Nat.shiftRight c 1) 1048575)))
        (TS (refK S S.length lo (Nat.shiftRight c 21)))) := by
  unfold recK at h
  simp only [strictB_eq, CFSG.KC.Co1Cl.lenL_eq, brec_eq_true, Bool.false_eq_true, and_false, or_false] at h
  obtain ⟨h0, -, h3⟩ := h
  refine ⟨h0, fun hc => ?_, fun hc => ?_⟩
  · rcases h3 with ⟨-, h3⟩ | ⟨h3c, -⟩
    · exact Nat.eq_of_beq_eq_true h3
    · exact absurd (hc.symm.trans h3c) (by decide)
  · rcases h3 with ⟨h3c, -⟩ | ⟨-, -, h4⟩
    · exact absurd (hc.symm.trans h3c) (by decide)
    · exact Nat.eq_of_beq_eq_true h4

theorem rec_at {j i : Nat} (hj : j < CH.length) (hi : i < (WL j).length) :
    recK TS (CH.getD j (0, 0, [])).2.2 (CH.getD j (0, 0, [])).2.1 ((CH.getD j (0, 0, [])).1 + i)
      ((WL j).getD i 0) = true :=
  chunkK_sound (chunks j hj) i hi

theorem node_mul {j i k a b : Nat} (hj : j < CH.length) (hi : i < (WL j).length)
    (hk : (CH.getD j (0, 0, [])).1 + i = k)
    (hc : Nat.beq (Nat.land ((WL j).getD i 0) 1) 1 = false)
    (ha : refK (CH.getD j (0, 0, [])).2.2 (CH.getD j (0, 0, [])).2.2.length
      (CH.getD j (0, 0, [])).2.1 (Nat.land (Nat.shiftRight ((WL j).getD i 0) 1) 1048575) = a)
    (hb : refK (CH.getD j (0, 0, [])).2.2 (CH.getD j (0, 0, [])).2.2.length
      (CH.getD j (0, 0, [])).2.1 (Nat.shiftRight ((WL j).getD i 0) 21) = b) :
    TS k = mulWK (TS a) (TS b) := by
  have h := (recK_parts (rec_at hj hi)).2.2 hc
  rwa [hk, ha, hb] at h

theorem node_inv {j i k a : Nat} (hj : j < CH.length) (hi : i < (WL j).length)
    (hk : (CH.getD j (0, 0, [])).1 + i = k)
    (hc : Nat.beq (Nat.land ((WL j).getD i 0) 1) 1 = true)
    (ha : refK (CH.getD j (0, 0, [])).2.2 (CH.getD j (0, 0, [])).2.2.length
      (CH.getD j (0, 0, [])).2.1 (Nat.land (Nat.shiftRight ((WL j).getD i 0) 1) 1048575) = a) :
    mulWK (TS k) (TS a) = oneK := by
  have h := (recK_parts (rec_at hj hi)).2.1 hc
  rwa [hk, ha] at h

theorem node_lt {j i k : Nat} (hj : j < CH.length) (hi : i < (WL j).length)
    (hk : (CH.getD j (0, 0, [])).1 + i = k) : TS k < 2 ^ (24 * 24) := by
  have h := (recK_parts (rec_at hj hi)).1
  rw [hk] at h
  unfold canK at h
  have e : Nat.shiftLeft 1 576 = 2 ^ (24 * 24) := by decide +kernel
  rw [Nat.blt_eq] at h
  exact lt_of_lt_of_eq h e

theorem nodeIn : ∀ k < 4189, NodeIn GA TS k :=
  nodeIn_all GA ch1023013layout chunks ch1023013seedsBelow nodeIn_seeds

@[expose] noncomputable def nodeG (k : Nat) : ↥GA :=
  if h : k < 4189 then ⟨(nodeIn k h).choose, (nodeIn k h).choose_spec.1⟩ else 1

theorem matK_nodeG {k : Nat} (h : k < 4189) : matK (TS k) = matHom GA (nodeG k) := by
  unfold nodeG
  rw [dif_pos h]
  exact (nodeIn k h).choose_spec.2

theorem nodeG_eq {k : Nat} (hk : k < 4189) (g : ↥GA)
    (h : matK (TS k) = ((g : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2))) : nodeG k = g :=
  matHom_injective GA ((matK_nodeG hk).symm.trans h)

theorem nodeG_one : nodeG 2 = 1 :=
  nodeG_eq (by norm_num) 1 (by rw [matK_TS_one]; rfl)

theorem nodeG_A₁ : nodeG 0 = ⟨A₁, A₁_mem⟩ := nodeG_eq (by norm_num) ⟨A₁, A₁_mem⟩ matK_TS_A₁

theorem nodeG_A₂ : nodeG 1 = ⟨A₂, A₂_mem⟩ := nodeG_eq (by norm_num) ⟨A₂, A₂_mem⟩ matK_TS_A₂

theorem nodeG_mul {k a b : Nat} (hk : k < 4189) (ha : a < 4189) (hb : b < 4189)
    (h : TS k = mulWK (TS a) (TS b)) : nodeG k = nodeG a * nodeG b := by
  apply matHom_injective GA
  rw [map_mul, ← matK_nodeG hk, ← matK_nodeG ha, ← matK_nodeG hb, h, matK_mulWK]

theorem nodeG_inv {k a : Nat} (hk : k < 4189) (ha : a < 4189) (h : mulWK (TS k) (TS a) = oneK) :
    nodeG k = (nodeG a)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left (matHom_injective GA ?_)
  rw [map_mul, map_one, ← matK_nodeG hk, ← matK_nodeG ha, ← matK_mulWK, h, matK_oneK]

theorem nodeG_ne_one {k : Nat} (hk : k < 4189) (hlt : TS k < 2 ^ (24 * 24))
    (hne : (!Nat.beq (TS k) oneK) = true) : nodeG k ≠ 1 := by
  intro h1
  have hm : matK (TS k) = matK oneK := by rw [matK_nodeG hk, h1, map_one, matK_oneK]
  have he := CFSG.KS.SporSch.Co1Rank.matK_inj_rk hlt CFSG.KS.SporSch.Co1Rank.oneK_lt_rk hm
  rw [he, Nat.beq_refl] at hne
  exact absurd hne (by decide)

@[expose] noncomputable def termG (t : Nat) : ↥GA := termM nodeG 7 KernelCo1Seven.GL t

theorem termG_eval (t : Nat) : termG t =
    if t % 2 = 0 then nodeG (t / 2) else epM nodeG 7 ([[617, 1437]].getD (t / 2 % 4) []) (t / 8) 1 := by
  rw [termG, termM, GL_eq]

theorem termK_eq {t : Nat} (ht : t % 2 = 0 → t / 2 < 4189) :
    termM (fun k => matK (TS k)) 7 KernelCo1Seven.GL t = matHom GA (termG t) := by
  rw [termG, ← termM_map (matHom GA)]
  unfold termM
  split_ifs with h
  · exact matK_nodeG (ht h)
  · refine epM_congr 7 _ (fun g hg => matK_nodeG ?_) _ 1
    rw [GL_eq] at hg
    have hi : t / 2 % 4 < 4 := Nat.mod_lt _ (by norm_num)
    interval_cases (t / 2 % 4) <;> simp at hg <;> omega

theorem eqG {s t u w : Nat} (hq : [s, t, u, w] ∈ getLLL Q 0)
    (hb : ∀ x ∈ [s, t, u, w], x % 2 = 0 → x / 2 < 4189) :
    termG s * termG t = termG u * termG w := by
  obtain ⟨-, h⟩ := eqsK_sound (TS := TS) (p := 7) (GLs := KernelCo1Seven.GL) ch1023013eq0 _ hq
  simp only [List.getD_cons_zero, List.getD_cons_succ] at h
  rw [termK_eq (hb s (by simp)), termK_eq (hb t (by simp)), termK_eq (hb u (by simp)),
    termK_eq (hb w (by simp)), ← map_mul, ← map_mul] at h
  exact matHom_injective GA h

end CertificateChecks.KernelCo1Seven

end
