module

public import Certificates.Kernel.D43.Hat
public import CFSG.Certificates.Kernel.D43.BaseSound
public import CFSG.Milestones.ASVolI.F48.D43.EInputs
import Certificates.Kernel.D43.BaseChk
import Certificates.Kernel.D43.GenCube
import Certificates.Kernel.D43.Cube
public import Certificates.Kernel.D43.Bind

set_option maxRecDepth 400000

public section

open CFSG.ASVolI CFSG.KC.D43 CFSG.Blueprint.Chevalley

namespace CertificateChecks.KernelD43

@[expose] noncomputable def σhat (j : ℕ) : Equiv.Perm (Fin 26572) :=
  if j = 2 then burnsideF48d_frob else burnsideF48d_σ (if j < 2 then j else j - 1)

theorem σhat_two : σhat 2 = burnsideF48d_frob := by
  unfold σhat
  rw [if_pos rfl]

theorem σhat_lt {j : ℕ} (hj : j < 2) : σhat j = burnsideF48d_σ j := by
  unfold σhat
  rw [if_neg (by omega), if_pos hj]

theorem σhat_gt {j : ℕ} (hj : 2 < j) : σhat j = burnsideF48d_σ (j - 1) := by
  unfold σhat
  rw [if_neg (by omega), if_neg (by omega)]

theorem γ_spec {k : ℕ} (hk : k < 8) :
    (∀ p : Fin 26572, (burnsideF48d_γ k p : ℕ) = tabAt GX.F k p) ∧ burnsideF48d_γ k ^ 3 = 1 := by
  have hc : ∀ c < 13, cubeChunk GX.F k c = true := fun c hc => by
    have h := genCube (13 * k + c) (by change 13 * k + c < 104; omega)
    change cubeChunk GX.F ((13 * k + c) / 13) ((13 * k + c) % 13) = true at h
    have e1 : (13 * k + c) / 13 = k := by omega
    have e2 : (13 * k + c) % 13 = c := by omega
    rwa [e1, e2] at h
  obtain ⟨e, he⟩ := exists_perm_of_cube hc
  have hγ : burnsideF48d_γ k = e := burnsideF48d_perm_eq (burnsideF48d_rep_of_apply (by
      simp only [burnsideF48d_gen, CFSG.Monster.B.Co2.Native.hexTable, Array.size_ofFn])
      fun q => (he q).trans (gen_tab hk q.2).symm)
  rw [hγ]
  refine ⟨he, Equiv.ext fun p => Fin.ext ?_⟩
  have hp := p.2
  obtain ⟨-, -, h3⟩ := cubeChk_spec (cubeChunk_spec (hc (p.val / 2048) (by omega)) (by omega)
    (by omega) hp)
  rw [pow_three', Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, he, he, he, Equiv.Perm.one_apply]
  exact h3

theorem φ_spec :
    (∀ p : Fin 26572, (burnsideF48d_frob p : ℕ) = tabAt PX.F 0 p) ∧ burnsideF48d_frob ^ 3 = 1 := by
  obtain ⟨e, he⟩ := exists_perm_of_cube (F := PX.F) (k := 0) phiCube
  have hφ : burnsideF48d_frob = e := burnsideF48d_perm_eq (burnsideF48d_rep_of_apply (by
      simp only [burnsideF48d_phi, CFSG.Monster.B.Co2.Native.hexTable, Array.size_ofFn])
      fun q => (he q).trans (phi_tab q.2).symm)
  rw [hφ]
  refine ⟨he, Equiv.ext fun p => Fin.ext ?_⟩
  have hp := p.2
  obtain ⟨-, -, h3⟩ := cubeChk_spec (cubeChunk_spec (phiCube (p.val / 2048)
    (by change p.val / 2048 < 13; omega))
    (by omega) (by omega) hp)
  rw [pow_three', Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, he, he, he, Equiv.Perm.one_apply]
  exact h3

theorem allBlk_at {b : ℕ} {f : ℕ → Bool} :
    ∀ {len : ℕ}, CFSG.KC.Enum.allBlk b f len = true → ∀ l < len, f (b + l) = true
  | 0, _, l, hl => absurd hl (Nat.not_lt_zero l)
  | len + 1, h, l, hl => by
    change Bool.rec (motive := fun _ => Bool) false (CFSG.KC.Enum.allBlk b f len)
      (f (Nat.add b len)) = true at h
    cases hf : f (Nat.add b len)
    · rw [hf] at h
      exact absurd h Bool.false_ne_true
    · rw [hf] at h
      rcases Nat.lt_succ_iff_lt_or_eq.1 hl with hl | rfl
      · exact allBlk_at h l hl
      · exact hf

theorem wV_flatL (l : Fin 18 × Bool) :
    wV burnsideF48d_γ burnsideF48d_frob (flatL burnsideF48d_LW l) =
      cond l.2 (σhat l.1) (σhat l.1)⁻¹ := by
  obtain ⟨j, b⟩ := l
  unfold flatL
  by_cases h2 : (j : ℕ) = 2
  · rw [if_pos h2]
    have e : σhat j = burnsideF48d_frob := by rw [h2]; exact σhat_two
    rw [e]
    cases b <;> simp [wV, dV]
  · rw [if_neg h2]
    have e : σhat j = burnsideF48d_σ (if (j : ℕ) < 2 then j else j - 1) := by
      unfold σhat
      rw [if_neg h2]
    rw [e]
    cases b
    · simp only [cond_false]
      rw [wV_flatG, ev_invW, burnsideF48d_σ]
    · simp only [cond_true]
      rw [wV_flatG, burnsideF48d_σ]

theorem ev_flatX (r : List (Fin 18 × Bool)) :
    burnsideF48s_ev (fun j : Fin 18 => σhat j) r =
      wV burnsideF48d_γ burnsideF48d_frob (flatX burnsideF48d_LW r) := by
  induction r with
  | nil => rfl
  | cons l r ih =>
    rw [flatX, List.map_cons, List.flatten_cons, ← flatX, wV_append, ← ih, wV_flatL,
      burnsideF48s_ev_cons]

theorem relWs_length : relWs.length = 195 := by
  decide +kernel

theorem conj_mem : ∀ k < 15, [((2 : Fin 18), false), (⟨(k + 3) % 18, Nat.mod_lt _ (by decide)⟩, true),
    ((2 : Fin 18), true)] ++ invW (burnsideF48dE_PhiW.getD k []) ∈ burnsideF48d_R13 := by
  decide +kernel

theorem comm_mem : [((0 : Fin 18), false), (2, true), (0, true), (2, false)] ∈ burnsideF48d_R13 ∧
    [((1 : Fin 18), false), (2, true), (1, true), (2, false)] ∈ burnsideF48d_R23 := by
  decide +kernel

theorem e_facts {K : Type} [Field K] (ω : K) (hK : Nat.card K = 27) (hω : ω ^ 3 = ω + 1)
    (g : Fin 8 → ModGL Tag.D4 K)
    (hg : ∀ k, (g k : Module.End K (RootModule Tag.D4 K)) = burnsideF48d_genEnd ω k)
    (hbase : ∀ z : ↥burnsideF48d_X,
      (∀ p ∈ burnsideF48d_baseF, (z : Equiv.Perm (Fin 26572)) p = p) → z = 1) :
    burnsideF48d_frob ^ 3 = 1 ∧ burnsideF48d_frob ≠ 1 ∧
      (∀ p ∈ burnsideF48d_aptF, burnsideF48d_frob p = p) ∧
      (∀ p ∈ burnsideF48d_line, burnsideF48d_frob p ∈ burnsideF48d_line) ∧
      burnsideF48d_frob * burnsideF48d_σ 0 = burnsideF48d_σ 0 * burnsideF48d_frob ∧
      burnsideF48d_frob * burnsideF48d_σ 1 = burnsideF48d_σ 1 * burnsideF48d_frob ∧
      (burnsideF48d_σ 0 * burnsideF48d_σ 1) ^ 6 = 1 ∧
      (∀ k < 15, burnsideF48d_frob⁻¹ * (burnsideF48d_σ (k + 2) * burnsideF48d_frob) =
        burnsideF48s_ev (fun j : Fin 18 => σhat j) (burnsideF48dE_PhiW.getD k [])) ∧
      ∀ r ∈ burnsideF48d_R13 ++ burnsideF48d_R23,
        burnsideF48s_ev (fun j : Fin 18 => σhat j) r = 1 := by
  obtain ⟨hφ, hφ3⟩ := φ_spec
  have hγ : ∀ k < 8, ∀ p : Fin 26572, (burnsideF48d_γ k p : ℕ) = tabAt GX.F k p :=
    fun k hk => (γ_spec hk).1
  have h3 : ∀ k < 8, burnsideF48d_γ k ^ 3 = 1 := fun k hk => (γ_spec hk).2
  have hX : ∀ k < 8, burnsideF48d_γ k ∈ burnsideF48d_X := fun k hk => burnsideF48d_γ_mem ⟨k, hk⟩
  have hconj := (frob_facts ω hK hω g hg).2
  have hn : ∀ h ∈ burnsideF48d_X, burnsideF48d_frob * h * burnsideF48d_frob⁻¹ ∈ burnsideF48d_X := by
    intro h hh
    rw [burnsideF48d_X] at hh
    induction hh using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨k, rfl⟩ := hy
      rw [hconj k k.2, mul_inv_cancel_right]
      refine burnsideF48d_X.list_prod_mem fun x hx => ?_
      obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
      exact burnsideF48d_γ_mem ⟨i, conjW_lt k k.2 i hi⟩
    | one =>
      rw [mul_one, mul_inv_cancel]
      exact burnsideF48d_X.one_mem
    | mul a b _ _ ha hb =>
      have e : burnsideF48d_frob * (a * b) * burnsideF48d_frob⁻¹ =
          (burnsideF48d_frob * a * burnsideF48d_frob⁻¹) *
            (burnsideF48d_frob * b * burnsideF48d_frob⁻¹) := by group
      rw [e]
      exact burnsideF48d_X.mul_mem ha hb
    | inv a _ ha =>
      have e : burnsideF48d_frob * a⁻¹ * burnsideF48d_frob⁻¹ =
          (burnsideF48d_frob * a * burnsideF48d_frob⁻¹)⁻¹ := by group
      rw [e]
      exact burnsideF48d_X.inv_mem ha
  have hb : ∀ h ∈ burnsideF48d_X, (∀ b ∈ baseL, ∀ hb : b < 26572, h ⟨b, hb⟩ = ⟨b, hb⟩) →
      h = 1 := by
    intro h hh hfix
    have e := hbase ⟨h, hh⟩ fun p hp => by
      have hp' : p.val ∈ baseL := by
        simp only [burnsideF48d_baseF, Finset.mem_insert, Finset.mem_singleton] at hp
        rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      exact hfix p.val hp' p.2
    exact congrArg Subtype.val e
  have hW : ∀ r ∈ relWs, burnsideF48s_ev (fun j : Fin 18 => σhat j) r = 1 := by
    intro r hr
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hr
    rw [relWs_length] at hi
    have hc0 : CFSG.KC.Enum.allBlk (Nat.mul 5 (i / 5))
        (fun j => wOK GX.F PX.F (flatX burnsideF48d_LW (relWs.getD j []))) 5 = true :=
      relAll (i / 5) (by change i / 5 < 39; omega)
    have hc := allBlk_at hc0 (i % 5) (Nat.mod_lt _ (by norm_num))
    have e : Nat.mul 5 (i / 5) + i % 5 = i := Nat.div_add_mod i 5
    rw [e, List.getD_eq_getElem _ _ (by rw [relWs_length]; exact hi)] at hc
    rw [ev_flatX]
    exact wV_one_of_wOK hγ h3 hφ hφ3 hX hn hb hc
  have hR : ∀ r ∈ burnsideF48d_R13 ++ burnsideF48d_R23,
      burnsideF48s_ev (fun j : Fin 18 => σhat j) r = 1 := fun r hr =>
    hW r (List.mem_append_left _ hr)
  have hfix : ∀ p : Fin 26572, p.val ∈ [0, 6, 479, 26571, 15916, 186, 1, 2] →
      burnsideF48d_frob p = p := by
    intro p hp
    have h1 := List.all_eq_true.1 phiPts.2 p.val hp
    rw [beq_iff_eq, ← hφ p] at h1
    exact Fin.ext h1
  have hσ0 : σhat 0 = burnsideF48d_σ 0 := σhat_lt (by norm_num)
  have hσ1 : σhat 1 = burnsideF48d_σ 1 := σhat_lt (by norm_num)
  refine ⟨hφ3, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hR⟩
  · intro h1
    have h4 := hφ ⟨4, by norm_num⟩
    rw [h1, phiPts.1] at h4
    exact absurd h4 (by decide)
  · intro p hp
    refine hfix p ?_
    simp only [burnsideF48d_aptF, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · intro p hp
    rw [hfix p ?_]
    · exact hp
    simp only [burnsideF48d_line, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> decide
  · have h := hR _ (List.mem_append_left _ comm_mem.1)
    change (σhat 0)⁻¹ * (σhat 2 * (σhat 0 * ((σhat 2)⁻¹ * 1))) = 1 at h
    rw [hσ0, σhat_two, mul_one, inv_mul_eq_one, ← mul_assoc, eq_mul_inv_iff_mul_eq] at h
    exact h.symm
  · have h := hR _ (List.mem_append_right _ comm_mem.2)
    change (σhat 1)⁻¹ * (σhat 2 * (σhat 1 * ((σhat 2)⁻¹ * 1))) = 1 at h
    rw [hσ1, σhat_two, mul_one, inv_mul_eq_one, ← mul_assoc, eq_mul_inv_iff_mul_eq] at h
    exact h.symm
  · have h := hW xy6W (by simp [relWs])
    rw [xy6W, burnsideF48s_ev_replicate] at h
    change (σhat 0 * (σhat 1 * 1)) ^ 6 = 1 at h
    rw [hσ0, hσ1, mul_one] at h
    exact h
  · intro k hk
    have h := hR _ (List.mem_append_left _ (conj_mem k hk))
    rw [burnsideF48s_ev_append, ev_invW] at h
    change (σhat 2)⁻¹ * (σhat ((k + 3) % 18) * (σhat 2 * 1)) *
      (burnsideF48s_ev (fun j : Fin 18 => σhat j) (burnsideF48dE_PhiW.getD k []))⁻¹ = 1 at h
    have e : k + 3 - 1 = k + 2 := by omega
    rw [σhat_two, Nat.mod_eq_of_lt (by omega), σhat_gt (by omega), mul_one, mul_inv_eq_one, e] at h
    exact h

end CertificateChecks.KernelD43

end
