module

public import Certificates.Kernel.Co1Three.Vals
public import Certificates.Kernel.Co1ThreeK.GlueQ
public import Certificates.Kernel.Co1Three.Seeds
public import Certificates.Kernel.Co1Three.Slp0
public import Certificates.Kernel.Co1Three.Slp1

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1Three

open CFSG.KC.Co1Cl CFSG.KC.Co1B CFSG.Sporadic.Co1Schreier CFSG.Sporadic.Co1Schreier.ElemThree
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance

theorem CH_length : CH.length = 31 := by decide +kernel

theorem Q_length : Q.length = 4 := by decide +kernel

theorem GL0 : KernelCo1Three.GL.getD 0 [] = [2, 3, 4, 5, 6, 7] := by decide +kernel

theorem GL1 : KernelCo1Three.GL.getD 1 [] = [10, 13096] := by decide +kernel

theorem GL_lt : ∀ l ∈ KernelCo1Three.GL, ∀ g ∈ l, g < 28098 := by decide +kernel

theorem Q_lt : ∀ c ∈ Q, ∀ q ∈ c, ∀ t ∈ q, t % 2 = 0 → t / 2 < 28098 := by decide +kernel

theorem NZ_lt : ∀ x ∈ NZ, x.1 < 28098 := by decide +kernel

theorem RT_eq : RT = [721, 12, 42] := by decide +kernel

theorem chunks : ∀ j < CH.length, chunkK TS CH WL j = true := by
  rw [CH_length]
  intro j hj
  interval_cases j
  exacts [slpChunk0, slpChunk1, slpChunk2, slpChunk3, slpChunk4, slpChunk5, slpChunk6, slpChunk7,
    slpChunk8, slpChunk9, slpChunk10, slpChunk11, slpChunk12, slpChunk13, slpChunk14, slpChunk15,
    slpChunk16, slpChunk17, slpChunk18, slpChunk19, slpChunk20, slpChunk21, slpChunk22, slpChunk23,
    slpChunk24, slpChunk25, slpChunk26, slpChunk27, slpChunk28, slpChunk29, slpChunk30]

theorem getLLL_eq (L : List (List (List Nat))) (i : Nat) : getLLL L i = L.getD i [] := by
  induction L generalizing i with
  | nil => rfl
  | cons a L ih => cases i with
    | zero => rfl
    | succ i => exact ih i

theorem eqChunks : ∀ k < 4, eqsK TS 3 KernelCo1Three.GL (Q.getD k []) = true := by
  intro k hk
  rw [← getLLL_eq]
  interval_cases k
  exacts [eqChunk0, eqChunk1, eqChunk2, eqChunk3]

theorem getD_lt {L : List Nat} {N : Nat} (hN : 0 < N) (hL : ∀ g ∈ L, g < N) (j : Nat) :
    L.getD j 0 < N := by
  by_cases hj : j < L.length
  · rw [List.getD_eq_getElem _ _ hj]
    exact hL _ (List.getElem_mem hj)
  · rw [List.getD_eq_default _ _ (by omega)]
    exact hN

theorem GL_getD_lt (i : Nat) : ∀ g ∈ KernelCo1Three.GL.getD i [], g < 28098 := by
  intro g hg
  by_cases hi : i < KernelCo1Three.GL.length
  · rw [List.getD_eq_getElem _ _ hi] at hg
    exact GL_lt _ (List.getElem_mem hi) g hg
  · rw [List.getD_eq_default _ _ (by omega)] at hg
    exact absurd hg List.not_mem_nil

@[expose] noncomputable def ι : ↥GA →* Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  (Units.coeHom (Matrix (Fin 24) (Fin 24) (ZMod 2))).comp GA.subtype

theorem ι_injective : Function.Injective ι := fun _ _ h => Subtype.ext (Units.ext h)

theorem nodeIn : ∀ k < 28098, NodeIn GA TS k :=
  nodeIn_all GA layout chunks seedsBelow nodeIn_seeds

@[expose] noncomputable def nodeG (k : Nat) : ↥GA :=
  if h : k < 28098 then ⟨(nodeIn k h).choose, (nodeIn k h).choose_spec.1⟩ else 1

theorem matK_nodeG {k : Nat} (h : k < 28098) : matK (TS k) = ι (nodeG k) := by
  unfold nodeG
  rw [dif_pos h]
  exact (nodeIn k h).choose_spec.2

theorem nodeG_eq {k : Nat} (hk : k < 28098) (g : ↥GA)
    (h : matK (TS k) = ((g : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2))) : nodeG k = g :=
  ι_injective ((matK_nodeG hk).symm.trans h)

theorem nodeG_one : nodeG 11 = 1 :=
  nodeG_eq (by norm_num) 1 (by rw [matK_TS_one]; rfl)

theorem nodeG_A₁ : nodeG 0 = ⟨A₁, A₁_mem⟩ := nodeG_eq (by norm_num) ⟨A₁, A₁_mem⟩ matK_TS_A₁

theorem nodeG_A₂ : nodeG 1 = ⟨A₂, A₂_mem⟩ := nodeG_eq (by norm_num) ⟨A₂, A₂_mem⟩ matK_TS_A₂

theorem nodeG_a {i : Nat} (hi : i < 6) :
    nodeG (i + 2) = ⟨a ⟨i, hi⟩, A_le_GA (Subgroup.subset_closure (Set.mem_union_left _ (a_mem_E _)))⟩ :=
  nodeG_eq (by omega) _ (matK_TS_a ⟨i, hi⟩)

theorem nodeG_root {j : Nat} (hj : j < 3) : nodeG (j + 8) = Co1T.root j :=
  nodeG_eq (by omega) _ (matK_TS_root hj)

@[expose] noncomputable def termG (t : Nat) : ↥GA := termM nodeG 3 KernelCo1Three.GL t

theorem epM_nodeG (G : List Nat) (hG : ∀ g ∈ G, g < 28098) (v : Nat) :
    epM (fun k => matK (TS k)) 3 G v 1 = ι (epM nodeG 3 G v 1) := by
  rw [← epM_map ι nodeG 3 G v 1, map_one]
  exact epM_congr 3 G (fun g hg => matK_nodeG (hG g hg)) v 1

theorem termK_eq {t : Nat} (ht : t % 2 = 0 → t / 2 < 28098) :
    termM (fun k => matK (TS k)) 3 KernelCo1Three.GL t = ι (termG t) := by
  rw [termG, ← termM_map ι]
  unfold termM
  split_ifs with h
  · exact matK_nodeG (ht h)
  · exact epM_congr 3 _ (fun g hg => matK_nodeG (GL_getD_lt _ g hg)) _ 1

theorem eqG {k : Nat} (hk : k < 4) {s t u w : Nat} (hq : [s, t, u, w] ∈ Q.getD k []) :
    termG s * termG t = termG u * termG w := by
  have hkQ : k < Q.length := by rw [Q_length]; exact hk
  have hc : Q.getD k [] ∈ Q := by
    rw [List.getD_eq_getElem _ _ hkQ]
    exact List.getElem_mem hkQ
  have hb := Q_lt _ hc _ hq
  obtain ⟨-, h⟩ := eqsK_sound (eqChunks k hk) _ hq
  simp only [List.getD_cons_zero, List.getD_cons_succ] at h
  rw [termK_eq (hb s (by simp)), termK_eq (hb t (by simp)), termK_eq (hb u (by simp)),
    termK_eq (hb w (by simp)), ← map_mul, ← map_mul] at h
  exact ι_injective h

theorem termG_nd (n : Nat) : termG (2 * n) = nodeG n := by
  unfold termG termM
  rw [if_pos (Nat.mul_mod_right 2 n), Nat.mul_div_cancel_left n (by norm_num)]

theorem termG_pt {g : Nat} (hg : g < 4) (v : Nat) :
    termG (2 * (g + 4 * v) + 1) = epM nodeG 3 (KernelCo1Three.GL.getD g []) v 1 := by
  unfold termG termM
  have h1 : (2 * (g + 4 * v) + 1) / 2 % 4 = g := by omega
  have h2 : (2 * (g + 4 * v) + 1) / 8 = v := by omega
  rw [if_neg (by omega), h1, h2]

@[expose] noncomputable def eG (v : Nat) : ↥GA := epM nodeG 3 [2, 3, 4, 5, 6, 7] v 1

theorem termG_E (v : Nat) : termG (2 * (0 + 4 * v) + 1) = eG v := by
  rw [termG_pt (by norm_num), GL0, eG]

theorem nodeG_mem_aGA : ∀ x ∈ [2, 3, 4, 5, 6, 7], nodeG x ∈ Co1T.aGA := by
  intro x hx
  have hx' : 2 ≤ x ∧ x < 8 := by simp at hx; omega
  obtain ⟨i, rfl⟩ : ∃ i, x = i + 2 := ⟨x - 2, by omega⟩
  rw [nodeG_a (by omega), Co1T.aGA]
  exact List.mem_map.2 ⟨⟨i, by omega⟩, List.mem_finRange _, rfl⟩

theorem aGA_eq : Co1T.aGA = [2, 3, 4, 5, 6, 7].map nodeG := by
  rw [Co1T.aGA]
  simp only [List.map_cons, List.map_nil]
  rw [nodeG_a (i := 0) (by norm_num), nodeG_a (i := 1) (by norm_num), nodeG_a (i := 2) (by norm_num),
    nodeG_a (i := 3) (by norm_num), nodeG_a (i := 4) (by norm_num), nodeG_a (i := 5) (by norm_num)]
  rfl

theorem E_comm : ∀ x ∈ [2, 3, 4, 5, 6, 7], ∀ y ∈ [2, 3, 4, 5, 6, 7], Commute (nodeG x) (nodeG y) :=
  fun x hx y hy => KernelCo1ThreeK.eSplitK.comm _ (nodeG_mem_aGA x hx) _ (nodeG_mem_aGA y hy)

theorem E_cube : ∀ x ∈ [2, 3, 4, 5, 6, 7], nodeG x ^ 3 = 1 :=
  fun x hx => KernelCo1ThreeK.eSplitK.cube _ (nodeG_mem_aGA x hx)

theorem normG : ∀ x ∈ NZ, x.2.length = [2, 3, 4, 5, 6, 7].length ∧ ∀ j < x.2.length,
    nodeG ([2, 3, 4, 5, 6, 7].getD j 0) * nodeG x.1 =
      nodeG x.1 * epM nodeG 3 [2, 3, 4, 5, 6, 7] (x.2.getD j 0) 1 := by
  intro x hx
  obtain ⟨hl, h⟩ := normK_sound norm x hx
  rw [GL0] at hl h
  refine ⟨hl, fun j hj => ι_injective ?_⟩
  have hG : ∀ g ∈ [2, 3, 4, 5, 6, 7], g < 28098 := by decide
  have := h j hj
  rw [matK_nodeG (getD_lt (by norm_num) hG j), matK_nodeG (NZ_lt x hx), epM_nodeG _ hG] at this
  rw [map_mul, map_mul]
  exact this

theorem forest_len : forestK 3 ([2, 3, 4, 5, 6, 7] : List Nat).length NZ RT DP FT = true := forest

theorem orbit_epM {c : Nat} (h1 : 1 ≤ c) (h2 : c < 3 ^ ([2, 3, 4, 5, 6, 7] : List Nat).length) :
    ∃ r ∈ RT, IsConj (epM nodeG 3 [2, 3, 4, 5, 6, 7] r 1) (epM nodeG 3 [2, 3, 4, 5, 6, 7] c 1) :=
  @forest_isConj ↥GA (Subgroup.toGroup GA) nodeG 3 (by norm_num) [2, 3, 4, 5, 6, 7] E_comm E_cube
    NZ RT DP FT forest_len normG c h1 h2

theorem orbit_E {c : Nat} (h1 : 1 ≤ c) (h2 : c < 729) : ∃ r ∈ RT, IsConj (eG r) (eG c) :=
  orbit_epM h1 h2

theorem epM_ofDigits {M : Type*} [Monoid M] (f : Nat → M) {p : Nat} (hp : 0 < p) :
    ∀ (G b : List Nat) (acc : M), b.length = G.length → (∀ x ∈ b, x < p) →
      epM f p G (Nat.ofDigits p b) acc = ((G.map f).zip b).foldl (fun acc fb => acc * fb.1 ^ fb.2) acc
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, h, _ => absurd h (by simp)
  | _ :: _, [], _, h, _ => absurd h (by simp)
  | g :: G, d :: b, acc, hl, hb => by
    have hd : d < p := hb d List.mem_cons_self
    rw [epM, Nat.ofDigits_cons, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hd,
      Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt hd, Nat.zero_add, List.map_cons, List.zip_cons_cons,
      List.foldl_cons]
    exact epM_ofDigits f hp G b _ (Nat.succ.inj hl) fun x hx => hb x (List.mem_cons_of_mem d hx)

theorem mem_T_eG {t : ↥GA} (ht : t ∈ KernelCo1ThreeK.eSplitK.T) : ∃ c < 729, t = eG c := by
  obtain ⟨x, rfl⟩ := ht
  have hx := KernelCo1ThreeK.eSplitK.φ_apply (Multiplicative.toAdd x)
  rw [ofAdd_toAdd] at hx
  have hlen := Co1T.vecList_length (Multiplicative.toAdd x)
  have hlt := Co1T.vecList_lt (Multiplicative.toAdd x)
  refine ⟨Nat.ofDigits 3 (Co1T.vecList (Multiplicative.toAdd x)), ?_, ?_⟩
  · have := Nat.ofDigits_lt_base_pow_length (b := 3) (by norm_num) hlt
    rw [hlen] at this
    calc _ < 3 ^ Co1T.aGA.length := this
      _ = 729 := by rw [Co1T.aGA_length]; rfl
  · rw [hx, eG, epM_ofDigits nodeG (by norm_num) _ _ 1 (by rw [hlen, Co1T.aGA_length]; rfl) hlt,
      Co1T.eltG]
    generalize Co1T.vecList (Multiplicative.toAdd x) = L
    rw [aGA_eq]

theorem eG_mem (v : Nat) : eG v ∈ KernelCo1ThreeK.eSplitK.T := by
  have key : ∀ (G : List Nat), (∀ x ∈ G, nodeG x ∈ KernelCo1ThreeK.eSplitK.T) → ∀ (v : Nat) (acc : ↥GA),
      acc ∈ KernelCo1ThreeK.eSplitK.T → epM nodeG 3 G v acc ∈ KernelCo1ThreeK.eSplitK.T := by
    intro G
    induction G with
    | nil => intro _ v acc h; exact h
    | cons g G ih =>
      intro hG v acc h
      exact ih (fun x hx => hG x (List.mem_cons_of_mem g hx)) _ _
        (Subgroup.mul_mem _ h (Subgroup.pow_mem _ (hG g List.mem_cons_self) _))
  refine key _ (fun x hx => ?_) v 1 (Subgroup.one_mem _)
  rw [Co1T.SplitData.T_eq_closure]
  exact Subgroup.subset_closure (nodeG_mem_aGA x hx)

end CertificateChecks.KernelCo1Three

end
