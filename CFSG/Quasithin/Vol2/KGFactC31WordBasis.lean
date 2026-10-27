
module

public import CFSG.Quasithin.Vol2.KGFactC31BadScan
public import CFSG.Quasithin.Vol2.KGFactC31Gen

public section

namespace CFSG.Quasithin.KGC31.Native

open CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier.PairNative

@[expose] def maskW : List (Array Nat) → Nat → List (Array Nat)
  | [], _ => []
  | b :: B, mask => maskW B (mask / 2) ++ (if mask % 2 = 1 then [b] else [])

@[expose] def ebasisW (bs : List Nat) (B : List (Array Nat)) : Bool :=
  (B.all fun b => fixB bs [b] 2) &&
    (B.all fun b => B.all fun c => baseImgs bs [b, c] == baseImgs bs [c, b]) &&
    (List.range (2 ^ B.length)).all fun m => m == 0 || !(fixB bs (maskW B m) 1)

@[expose] def normsW (bs : List Nat) (B : List (Array Nat)) (g gi : Array Nat) : Bool :=
  inSpanW bs (spanW bs (B.map fun b => [b])) (B.map fun b => [gi, b, g])

end CFSG.Quasithin.KGC31.Native

namespace CFSG.Quasithin.KGC31

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.PairNative CFSG.Quasithin.KGC31.Native

variable {n : ℕ}

@[expose] def bitVec (k mask : ℕ) : Fin k → ZMod 2 := fun i => ((mask / 2 ^ i.val) % 2 : ℕ)

theorem bitVec_zero (k mask : ℕ) : bitVec (k + 1) mask 0 = ((mask % 2 : ℕ) : ZMod 2) := by
  simp [bitVec]

theorem bitVec_succ (k mask : ℕ) :
    (fun i : Fin k => bitVec (k + 1) mask i.succ) = bitVec k (mask / 2) := by
  funext i
  simp only [bitVec, Fin.val_succ, pow_succ, Nat.div_div_eq_div_mul]
  rw [mul_comm (2 ^ i.val) 2, ← Nat.div_div_eq_div_mul]

theorem exists_bitVec : ∀ {k : ℕ} (c : Fin k → ZMod 2), ∃ mask < 2 ^ k, bitVec k mask = c
  | 0, c => ⟨0, by norm_num, funext fun i => i.elim0⟩
  | k + 1, c => by
    obtain ⟨m', hm', hc⟩ := exists_bitVec (fun i : Fin k => c i.succ)
    have hc0 : (c 0).val < 2 := ZMod.val_lt _
    refine ⟨(c 0).val + 2 * m', by rw [pow_succ]; omega, funext fun i => ?_⟩
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [bitVec_zero]
      have : ((c 0).val + 2 * m') % 2 = (c 0).val := by omega
      rw [this, ZMod.natCast_zmod_val]
    · have h1 := congrFun (bitVec_succ k ((c 0).val + 2 * m')) j
      rw [h1]
      have : ((c 0).val + 2 * m') / 2 = m' := by omega
      rw [this, hc]

theorem repW_maskW : ∀ {k : ℕ} (v : Fin k → Equiv.Perm (Fin n)) (B : List (Array ℕ)),
    List.Forall₂ (Rep n) B (List.ofFn v) → ∀ mask,
      RepW n (maskW B mask) (eElt v (bitVec k mask))
  | 0, v, B, h, mask => by
    rw [List.ofFn_zero, List.forall₂_nil_right_iff] at h
    subst h
    rw [show eElt v (bitVec 0 mask) = 1 by simp [eElt]]
    exact repW_nil
  | k + 1, v, B, h, mask => by
    rw [List.ofFn_succ] at h
    cases h with
    | cons hb hB =>
      rw [maskW, eElt_succ, bitVec_succ, bitVec_zero]
      have hval : ((mask % 2 : ℕ) : ZMod 2).val = mask % 2 :=
        ZMod.val_cast_of_lt (Nat.mod_lt _ (by norm_num))
      rw [hval]
      refine (repW_maskW (fun i => v i.succ) _ hB (mask / 2)).append ?_
      split_ifs with h1
      · rw [h1, pow_one]
        exact RepW.single hb
      · have h0 : mask % 2 = 0 := by omega
        rw [h0, pow_zero]
        exact repW_nil

variable {H : Subgroup (Equiv.Perm (Fin n))} {bs : List ℕ}

theorem ebasis_of_ebasisW (hH : BaseFaithful H bs) (hbs : ∀ b ∈ bs, b < n) {k : ℕ}
    {v : Fin k → Equiv.Perm (Fin n)} {B : List (Array ℕ)}
    (hB : List.Forall₂ (Rep n) B (List.ofFn v)) (hvH : ∀ i, v i ∈ H)
    (h : ebasisW bs B = true) : EBasis v := by
  have hlen : B.length = k := by rw [hB.length_eq, List.length_ofFn]
  simp only [ebasisW, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨hsq, hcomm⟩, hne⟩ := h
  have hrep : ∀ i : Fin k, ∃ b ∈ B, Rep n b (v i) := fun i =>
    exists_left_of_forall₂ hB (List.mem_ofFn.mpr ⟨i, rfl⟩)
  refine ⟨fun i => ?_, fun i j => ?_, fun c hc => ?_⟩
  · obtain ⟨b, hb, hbi⟩ := hrep i
    have := (fixB_iff_eq_one hH hbs (RepW.single hbi) (hvH i) 2).1 (hsq b hb)
    rwa [sq] at this
  · obtain ⟨b, hb, hbi⟩ := hrep i
    obtain ⟨b', hb', hbj⟩ := hrep j
    have he := hcomm b hb b' hb'
    rw [beq_iff_eq] at he
    have h1 : RepW n [b, b'] (v j * v i) := (RepW.single hbi).append (RepW.single hbj)
    have h2 : RepW n [b', b] (v i * v j) := (RepW.single hbj).append (RepW.single hbi)
    exact (eq_of_baseImgs_eq hH hbs h2 h1 (H.mul_mem (hvH i) (hvH j))
      (H.mul_mem (hvH j) (hvH i)) he.symm)
  · obtain ⟨mask, hmask, rfl⟩ := exists_bitVec c
    have h1 := hne mask (by rw [List.mem_range, hlen]; exact hmask)
    rw [Bool.or_eq_true, beq_iff_eq] at h1
    rcases h1 with h0 | h1
    · subst h0
      funext i
      simp [bitVec]
    · exfalso
      rw [Bool.not_eq_true'] at h1
      have hmem : eElt v (bitVec k mask) ∈ H :=
        H.list_prod_mem fun x hx => by
          obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
          exact H.pow_mem (hvH i) _
      have h2 := (fixB_iff_eq_one hH hbs (repW_maskW v B hB mask) hmem 1).2 (by rw [pow_one, hc])
      rw [h1] at h2
      exact absurd h2 (by decide)

theorem mem_eNorm_of_normsW (hH : BaseFaithful H bs) (hbs : ∀ b ∈ bs, b < n) {k : ℕ}
    {v : Fin k → Equiv.Perm (Fin n)} (hv : EBasis v) {B : List (Array ℕ)}
    (hB : List.Forall₂ (Rep n) B (List.ofFn v)) (hvH : ∀ i, v i ∈ H) {g : Equiv.Perm (Fin n)}
    {gA giA : Array ℕ} (hg : Rep n gA g) (hgi : Rep n giA g⁻¹) (hgH : g ∈ H)
    (h : normsW bs B gA giA = true) : g ∈ eNorm hv := by
  have hBw : List.Forall₂ (RepW n) (B.map fun b => [b]) (List.ofFn v) := by
    rw [List.forall₂_map_left_iff]
    exact hB.imp fun _ _ hb => RepW.single hb
  have hsp := spanW_mem (bs := bs) hBw
  have hcl : Subgroup.closure {x | x ∈ List.ofFn v} ≤ eSub hv := by
    rw [Subgroup.closure_le]
    intro x hx
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
    exact mem_eSub hv i
  have hclH : Subgroup.closure {x | x ∈ List.ofFn v} ≤ H := by
    rw [Subgroup.closure_le]
    intro x hx
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
    exact hvH i
  have hconj : List.Forall₂ (RepW n) (B.map fun b => [giA, b, gA])
      ((List.ofFn v).map fun x => g * x * g⁻¹) := by
    rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    refine hB.imp fun b x hb => ?_
    have := ((RepW.single hgi).append (RepW.single hb)).append (RepW.single hg)
    rwa [← mul_assoc] at this
  have hconjH : ∀ z ∈ (List.ofFn v).map (fun x => g * x * g⁻¹), z ∈ H := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hz
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
    exact H.mul_mem (H.mul_mem hgH (hvH i)) (H.inv_mem hgH)
  have hmem := mem_of_inSpanW hH hbs hclH hsp hconj hconjH h
  rw [mem_eNorm_iff hv]
  intro i
  have := hcl (hmem _ (List.mem_map.mpr ⟨v i, List.mem_ofFn.mpr ⟨i, rfl⟩, rfl⟩))
  obtain ⟨c, hc⟩ := (mem_eSub_iff hv _).mp this
  exact ⟨c, hc.symm⟩

end CFSG.Quasithin.KGC31

end
