module

public import CFSG.LocalAnalysis.UniquenessCase.UC1K49CoreMod

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC49

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem range_e2_eq_ker_one_sub (Z : Module.End (ZMod 2) V) (hZ : Z ^ 3 = 1) :
    LinearMap.range (e2 Z) = LinearMap.ker (1 - Z) := by
  ext w
  rw [mem_range_e2_iff Z hZ w, LinearMap.mem_ker]
  constructor
  · intro h
    rw [LinearMap.sub_apply, Module.End.one_apply, h, sub_self]
  · intro h
    rw [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at h
    exact h.symm

theorem mul_e2_comm_self (Z : Module.End (ZMod 2) V) :
    Z * e2 Z = e2 Z * Z := by
  let S : Subring (Module.End (ZMod 2) V) := Subring.closure ({Z} : Set _)
  letI : CommRing S := Subring.closureCommRingOfComm (Set.pairwise_singleton Z Commute)
  let Z' : S := ⟨Z, Subring.subset_closure (by simp)⟩
  have key : Z' * e2 Z' = e2 Z' * Z' := mul_comm _ _
  have h := congrArg Subtype.val key
  change Z * ((e2 Z' : ↥S) : Module.End (ZMod 2) V) =
    ((e2 Z' : ↥S) : Module.End (ZMod 2) V) * Z at h
  rw [e2_subring_coe S Z'] at h
  simpa using h

private theorem card_ker_e2_eq_four_pow (T : Module.End (ZMod 2) V) (hT : T ^ 3 = 1) :
    ∃ k, Nat.card ↥(LinearMap.ker (e2 T)) = 4 ^ k := by
  have he : IsIdempotentElem (e2 T) := e2_end_mul_self T hT
  have hcompl : IsCompl (LinearMap.range (e2 T)) (LinearMap.ker (e2 T)) :=
    LinearMap.IsIdempotentElem.isCompl he
  have hdisj : Disjoint (LinearMap.range (e2 T)) (LinearMap.ker (e2 T)) := hcompl.1
  have hW : ∀ w : V, w ∈ LinearMap.ker (e2 T) → T w ∈ LinearMap.ker (e2 T) := by
    intro w hw
    rw [LinearMap.mem_ker] at hw ⊢
    rw [← Module.End.mul_apply, ← mul_e2_comm_self T, Module.End.mul_apply, hw, map_zero]
  have hfpf : ∀ w : V, w ∈ LinearMap.ker (e2 T) → T w = w → w = 0 := by
    intro w hw hTw
    have hw2 : w ∈ LinearMap.range (e2 T) := by
      rw [range_e2_eq_ker_one_sub T hT]
      rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, hTw, sub_self]
    exact Submodule.disjoint_def.mp hdisj w hw2 hw
  exact card_eq_four_pow_of_fpf (LinearMap.ker (e2 T)) T hT hW hfpf

private theorem card_ker_e2_eq_four_pow_and_le_one_of_finrank_le_two
    (T : Module.End (ZMod 2) V) (hT : T ^ 3 = 1)
    (hrank : Module.finrank (ZMod 2) V ≤ 2) :
    ∃ k, Nat.card ↥(LinearMap.ker (e2 T)) = 4 ^ k ∧ k ≤ 1 := by
  obtain ⟨k, hk⟩ := card_ker_e2_eq_four_pow T hT
  refine ⟨k, hk, ?_⟩
  by_contra hk'
  have h2 : 2 ≤ k := by omega
  have hcardV : Nat.card V ≤ 4 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := V), Nat.card_zmod]
    calc 2 ^ Module.finrank (ZMod 2) V ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hrank
      _ = 4 := by norm_num
  have he : IsIdempotentElem (e2 T) := e2_end_mul_self T hT
  have hcompl : IsCompl (LinearMap.range (e2 T)) (LinearMap.ker (e2 T)) :=
    LinearMap.IsIdempotentElem.isCompl he
  have hcard : Nat.card V = Nat.card ↥(LinearMap.range (e2 T)) *
      Nat.card ↥(LinearMap.ker (e2 T)) := by
    have h := Nat.card_congr (Submodule.prodEquivOfIsCompl _ _ hcompl).toEquiv
    rw [Nat.card_prod] at h
    exact h.symm
  have h16 : 16 ≤ 4 ^ k := by
    have := Nat.pow_le_pow_right (by norm_num : 1 ≤ 4) h2
    norm_num at this ⊢
    exact this
  have hle : 4 ^ k ≤ Nat.card V := by
    rw [← hk]
    calc Nat.card ↥(LinearMap.ker (e2 T))
        = 1 * Nat.card ↥(LinearMap.ker (e2 T)) := (one_mul _).symm
      _ ≤ Nat.card ↥(LinearMap.range (e2 T)) * Nat.card ↥(LinearMap.ker (e2 T)) :=
          Nat.mul_le_mul_right _ (Nat.succ_le_of_lt Nat.card_pos)
      _ = Nat.card V := hcard.symm
  omega

private theorem eq_one_of_card_ker_e2_eq_one (T : Module.End (ZMod 2) V) (hT : T ^ 3 = 1)
    (hk : Nat.card ↥(LinearMap.ker (e2 T)) = 1) : T = 1 := by
  have hbot : LinearMap.ker (e2 T) = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro w hw
    haveI : Subsingleton ↥(LinearMap.ker (e2 T)) :=
      (Finite.card_le_one_iff_subsingleton).mp (le_of_eq hk)
    exact congrArg Subtype.val
      (Subsingleton.elim (⟨w, hw⟩ : ↥(LinearMap.ker (e2 T))) 0)
  have he : IsIdempotentElem (e2 T) := e2_end_mul_self T hT
  have hcompl : IsCompl (LinearMap.range (e2 T)) (LinearMap.ker (e2 T)) :=
    LinearMap.IsIdempotentElem.isCompl he
  have htop : LinearMap.range (e2 T) = ⊤ := by
    rw [← hcompl.sup_eq_top, hbot, sup_bot_eq]
  have hz : (1 - T : V →ₗ[ZMod 2] V) = 0 := by
    rw [← LinearMap.ker_eq_top, ← range_e2_eq_ker_one_sub T hT, htop]
  exact (sub_eq_zero.mp hz).symm

private theorem fpf_of_card_ker_e2_eq_four (T : Module.End (ZMod 2) V) (hT : T ^ 3 = 1)
    (hrank : Module.finrank (ZMod 2) V ≤ 2)
    (hk : Nat.card ↥(LinearMap.ker (e2 T)) = 4) : ∀ v : V, T v = v → v = 0 := by
  have hcardV : Nat.card V ≤ 4 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := V), Nat.card_zmod]
    calc 2 ^ Module.finrank (ZMod 2) V ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hrank
      _ = 4 := by norm_num
  have he : IsIdempotentElem (e2 T) := e2_end_mul_self T hT
  have hcompl : IsCompl (LinearMap.range (e2 T)) (LinearMap.ker (e2 T)) :=
    LinearMap.IsIdempotentElem.isCompl he
  have hcard : Nat.card V = Nat.card ↥(LinearMap.range (e2 T)) *
      Nat.card ↥(LinearMap.ker (e2 T)) := by
    have h := Nat.card_congr (Submodule.prodEquivOfIsCompl _ _ hcompl).toEquiv
    rw [Nat.card_prod] at h
    exact h.symm
  have hcard1 : Nat.card ↥(LinearMap.range (e2 T)) = 1 := by
    rw [hk] at hcard
    have hpos := Nat.card_pos (α := ↥(LinearMap.range (e2 T)))
    omega
  have hbot : LinearMap.range (e2 T) = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro w hw
    haveI : Subsingleton ↥(LinearMap.range (e2 T)) :=
      (Finite.card_le_one_iff_subsingleton).mp (le_of_eq hcard1)
    exact congrArg Subtype.val
      (Subsingleton.elim (⟨w, hw⟩ : ↥(LinearMap.range (e2 T))) 0)
  intro v hv
  rw [range_e2_eq_ker_one_sub T hT] at hbot
  have hmem : v ∈ LinearMap.ker (1 - T) := by
    rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, hv, sub_self]
  rw [hbot] at hmem
  simpa using hmem

theorem eq_one_or_fpf_of_finrank_le_two (T : Module.End (ZMod 2) V) (hT : T ^ 3 = 1)
    (hrank : Module.finrank (ZMod 2) V ≤ 2) :
    T = 1 ∨ ∀ v : V, T v = v → v = 0 := by
  obtain ⟨k, hk, hk1⟩ := card_ker_e2_eq_four_pow_and_le_one_of_finrank_le_two T hT hrank
  interval_cases k
  · exact Or.inl (eq_one_of_card_ker_e2_eq_one T hT (by simpa using hk))
  · exact Or.inr (fpf_of_card_ker_e2_eq_four T hT hrank (by simpa using hk))

private theorem apply_eq_zero_of_mul_eq_mul_e2 (p q s : Module.End (ZMod 2) V)
    {Z : Module.End (ZMod 2) V} (y : V)
    (h : p * q = s * e2 Z) (hq : q y = y) (hy : e2 Z y = 0) : p y = 0 := by
  calc p y = p (q y) := by rw [hq]
    _ = (p * q) y := by rw [Module.End.mul_apply]
    _ = (s * e2 Z) y := by rw [h]
    _ = s (e2 Z y) := by rw [Module.End.mul_apply]
    _ = 0 := by rw [hy, map_zero]

private theorem card_le_of_map_mem (X : Module.End (ZMod 2) V) (hXinj : Function.Injective X)
    {W W' : Submodule (ZMod 2) V} (h : ∀ w : V, w ∈ W → X w ∈ W') :
    Nat.card ↥W ≤ Nat.card ↥W' := by
  refine Nat.card_le_card_of_injective (fun w : ↥W => (⟨X w.1, h w.1 w.2⟩ : ↥W')) ?_
  intro a b hab
  exact Subtype.ext (hXinj (Subtype.ext_iff.mp hab))

private theorem e2_decomp_sum (B Z : Module.End (ZMod 2) V) (hB : B ^ 3 = 1)
    (hZ : Z ^ 3 = 1) (hBZ : B * Z = Z * B) :
    (∀ u : V, u ∈ LinearMap.ker (e2 Z) → e2 B u ∈ LinearMap.ker (e2 Z)) ∧
      (∀ u : V, u ∈ LinearMap.ker (e2 Z) → e2 (B * Z) u ∈ LinearMap.ker (e2 Z)) ∧
      (∀ u : V, u ∈ LinearMap.ker (e2 Z) → e2 (B * Z ^ 2) u ∈ LinearMap.ker (e2 Z)) ∧
      (∀ u : V, u ∈ LinearMap.ker (e2 Z) →
        e2 B u + e2 (B * Z) u + e2 (B * Z ^ 2) u = u) := by
  have hBmem : B ∈ Subring.closure ({B, Z} : Set (Module.End (ZMod 2) V)) :=
    Subring.subset_closure (by simp)
  have hZmem : Z ∈ Subring.closure ({B, Z} : Set (Module.End (ZMod 2) V)) :=
    Subring.subset_closure (by simp)
  have hBZmem : B * Z ∈ Subring.closure ({B, Z} : Set (Module.End (ZMod 2) V)) :=
    Subring.mul_mem _ hBmem hZmem
  have hBZ2mem : B * Z ^ 2 ∈ Subring.closure ({B, Z} : Set (Module.End (ZMod 2) V)) :=
    Subring.mul_mem _ hBmem (Subring.pow_mem _ hZmem 2)
  have heZeB := e2_end_comm_of_mem B Z Z B hBZ hZmem hBmem
  have heZeBZ := e2_end_comm_of_mem B Z Z (B * Z) hBZ hZmem hBZmem
  have heZeBZ2 := e2_end_comm_of_mem B Z Z (B * Z ^ 2) hBZ hZmem hBZ2mem
  have hid4 := e2_end_sum B Z hB hZ hBZ
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro u hu
    change e2 Z u = 0 at hu
    change e2 Z (e2 B u) = 0
    rw [← Module.End.mul_apply, heZeB, Module.End.mul_apply, hu, map_zero]
  · intro u hu
    change e2 Z u = 0 at hu
    change e2 Z (e2 (B * Z) u) = 0
    rw [← Module.End.mul_apply, heZeBZ, Module.End.mul_apply, hu, map_zero]
  · intro u hu
    change e2 Z u = 0 at hu
    change e2 Z (e2 (B * Z ^ 2) u) = 0
    rw [← Module.End.mul_apply, heZeBZ2, Module.End.mul_apply, hu, map_zero]
  · intro u hu
    change e2 Z u = 0 at hu
    have h4 := congrArg (fun f : Module.End (ZMod 2) V => f u) hid4
    simp only [LinearMap.add_apply, Module.End.one_apply, Module.End.mul_apply] at h4
    rw [hu, map_zero] at h4
    simpa using h4

private theorem e2_decomp_span (B Z : Module.End (ZMod 2) V) (hB : B ^ 3 = 1)
    (hZ : Z ^ 3 = 1) (hBZ : B * Z = Z * B) :
    let U : Submodule (ZMod 2) V := LinearMap.ker (e2 Z)
    let Wb : Submodule (ZMod 2) V := LinearMap.range (e2 B) ⊓ U
    let Wbz : Submodule (ZMod 2) V := LinearMap.range (e2 (B * Z)) ⊓ U
    let Wbz2 : Submodule (ZMod 2) V := LinearMap.range (e2 (B * Z ^ 2)) ⊓ U
    U = Wb ⊔ Wbz ⊔ Wbz2 := by
  let U : Submodule (ZMod 2) V := LinearMap.ker (e2 Z)
  let Wb : Submodule (ZMod 2) V := LinearMap.range (e2 B) ⊓ U
  let Wbz : Submodule (ZMod 2) V := LinearMap.range (e2 (B * Z)) ⊓ U
  let Wbz2 : Submodule (ZMod 2) V := LinearMap.range (e2 (B * Z ^ 2)) ⊓ U
  obtain ⟨hU_B, hU_BZ, hU_BZ2, hsum⟩ := e2_decomp_sum B Z hB hZ hBZ
  have hU_ge : Wb ⊔ Wbz ⊔ Wbz2 ≤ U :=
    sup_le (sup_le inf_le_right inf_le_right) inf_le_right
  have hU_le : U ≤ Wb ⊔ Wbz ⊔ Wbz2 := by
    intro u hu
    have hx : e2 B u ∈ Wb := ⟨⟨u, rfl⟩, hU_B u hu⟩
    have hy : e2 (B * Z) u ∈ Wbz := ⟨⟨u, rfl⟩, hU_BZ u hu⟩
    have hz : e2 (B * Z ^ 2) u ∈ Wbz2 := ⟨⟨u, rfl⟩, hU_BZ2 u hu⟩
    rw [← hsum u hu]
    exact Submodule.add_mem_sup (Submodule.add_mem_sup hx hy) hz
  exact le_antisymm hU_le hU_ge

private theorem e2_decomp_idem (B Z : Module.End (ZMod 2) V) (hB : B ^ 3 = 1)
    (hZ : Z ^ 3 = 1) (hBZ : B * Z = Z * B) :
    let U : Submodule (ZMod 2) V := LinearMap.ker (e2 Z)
    let Wb : Submodule (ZMod 2) V := LinearMap.range (e2 B) ⊓ U
    let Wbz : Submodule (ZMod 2) V := LinearMap.range (e2 (B * Z)) ⊓ U
    let Wbz2 : Submodule (ZMod 2) V := LinearMap.range (e2 (B * Z ^ 2)) ⊓ U
    (∀ x : V, x ∈ Wb → e2 B x = x) ∧ (∀ y : V, y ∈ Wbz → e2 (B * Z) y = y) ∧
      (∀ z : V, z ∈ Wbz2 → e2 (B * Z ^ 2) z = z) := by
  let U : Submodule (ZMod 2) V := LinearMap.ker (e2 Z)
  let Wb : Submodule (ZMod 2) V := LinearMap.range (e2 B) ⊓ U
  let Wbz : Submodule (ZMod 2) V := LinearMap.range (e2 (B * Z)) ⊓ U
  let Wbz2 : Submodule (ZMod 2) V := LinearMap.range (e2 (B * Z ^ 2)) ⊓ U
  have hBZ3 : (B * Z) ^ 3 = 1 := by rw [Commute.mul_pow hBZ 3, hB, hZ, mul_one]
  have hZ23 : (Z ^ 2) ^ 3 = 1 := by
    rw [← pow_mul, show 2 * 3 = 3 * 2 by norm_num, pow_mul, hZ, one_pow]
  have hBZ23 : (B * Z ^ 2) ^ 3 = 1 := by
    rw [Commute.mul_pow (Commute.pow_right hBZ 2) 3, hB, hZ23, mul_one]
  have heBi : IsIdempotentElem (e2 B) := e2_end_mul_self B hB
  have heBZi : IsIdempotentElem (e2 (B * Z)) := e2_end_mul_self (B * Z) hBZ3
  have heBZ2i : IsIdempotentElem (e2 (B * Z ^ 2)) := e2_end_mul_self (B * Z ^ 2) hBZ23
  exact ⟨fun x hx => (LinearMap.IsIdempotentElem.mem_range_iff heBi).mp
      (Submodule.mem_inf.mp hx).1,
    fun y hy => (LinearMap.IsIdempotentElem.mem_range_iff heBZi).mp
      (Submodule.mem_inf.mp hy).1,
    fun z hz => (LinearMap.IsIdempotentElem.mem_range_iff heBZ2i).mp
      (Submodule.mem_inf.mp hz).1⟩

private theorem e2_decomp_ann_B (B Z : Module.End (ZMod 2) V) (hB : B ^ 3 = 1)
    (hZ : Z ^ 3 = 1) (hBZ : B * Z = Z * B) :
    let U : Submodule (ZMod 2) V := LinearMap.ker (e2 Z)
    let Wbz : Submodule (ZMod 2) V := LinearMap.range (e2 (B * Z)) ⊓ U
    let Wbz2 : Submodule (ZMod 2) V := LinearMap.range (e2 (B * Z ^ 2)) ⊓ U
    (∀ y : V, y ∈ Wbz → e2 B y = 0) ∧ (∀ z : V, z ∈ Wbz2 → e2 B z = 0) := by
  let U : Submodule (ZMod 2) V := LinearMap.ker (e2 Z)
  let Wbz : Submodule (ZMod 2) V := LinearMap.range (e2 (B * Z)) ⊓ U
  let Wbz2 : Submodule (ZMod 2) V := LinearMap.range (e2 (B * Z ^ 2)) ⊓ U
  obtain ⟨_, hBZ_idem, hBZ2_idem⟩ := e2_decomp_idem B Z hB hZ hBZ
  have hid1 := e2_end_mul_bz B Z hB hZ hBZ
  have hid2 := e2_end_mul_bz2 B Z hB hZ hBZ
  refine ⟨?_, ?_⟩
  · intro y hy
    exact apply_eq_zero_of_mul_eq_mul_e2 (e2 B) (e2 (B * Z)) (e2 B) y hid1 (hBZ_idem y hy)
      (Submodule.mem_inf.mp hy).2
  · intro z hz
    exact apply_eq_zero_of_mul_eq_mul_e2 (e2 B) (e2 (B * Z ^ 2)) (e2 B) z hid2
      (hBZ2_idem z hz) (Submodule.mem_inf.mp hz).2

private theorem e2_decomp_ann_BZ (B Z : Module.End (ZMod 2) V) (hB : B ^ 3 = 1)
    (hZ : Z ^ 3 = 1) (hBZ : B * Z = Z * B) :
    let U : Submodule (ZMod 2) V := LinearMap.ker (e2 Z)
    let Wb : Submodule (ZMod 2) V := LinearMap.range (e2 B) ⊓ U
    let Wbz : Submodule (ZMod 2) V := LinearMap.range (e2 (B * Z)) ⊓ U
    let Wbz2 : Submodule (ZMod 2) V := LinearMap.range (e2 (B * Z ^ 2)) ⊓ U
    (∀ x : V, x ∈ Wb → e2 (B * Z) x = 0) ∧
      (∀ z : V, z ∈ Wbz2 → e2 (B * Z) z = 0) ∧
      (∀ x : V, x ∈ Wb → e2 (B * Z ^ 2) x = 0) ∧
      (∀ y : V, y ∈ Wbz → e2 (B * Z ^ 2) y = 0) := by
  let U : Submodule (ZMod 2) V := LinearMap.ker (e2 Z)
  let Wb : Submodule (ZMod 2) V := LinearMap.range (e2 B) ⊓ U
  let Wbz : Submodule (ZMod 2) V := LinearMap.range (e2 (B * Z)) ⊓ U
  let Wbz2 : Submodule (ZMod 2) V := LinearMap.range (e2 (B * Z ^ 2)) ⊓ U
  obtain ⟨hB_idem, hBZ_idem, hBZ2_idem⟩ := e2_decomp_idem B Z hB hZ hBZ
  have hid3 := e2_end_bz_mul_bz2 B Z hB hZ hBZ
  have hBmem : B ∈ Subring.closure ({B, Z} : Set (Module.End (ZMod 2) V)) :=
    Subring.subset_closure (by simp)
  have hBZmem : B * Z ∈ Subring.closure ({B, Z} : Set (Module.End (ZMod 2) V)) :=
    Subring.mul_mem _ hBmem (Subring.subset_closure (by simp))
  have hBZ2mem : B * Z ^ 2 ∈ Subring.closure ({B, Z} : Set (Module.End (ZMod 2) V)) :=
    Subring.mul_mem _ hBmem (Subring.pow_mem _ (Subring.subset_closure (by simp)) 2)
  have hcBZB : e2 (B * Z) * e2 B = e2 B * e2 Z := by
    rw [e2_end_comm_of_mem B Z (B * Z) B hBZ hBZmem hBmem, e2_end_mul_bz B Z hB hZ hBZ]
  have hcBZ2B : e2 (B * Z ^ 2) * e2 B = e2 B * e2 Z := by
    rw [e2_end_comm_of_mem B Z (B * Z ^ 2) B hBZ hBZ2mem hBmem, e2_end_mul_bz2 B Z hB hZ hBZ]
  have hcBZ2BZ : e2 (B * Z ^ 2) * e2 (B * Z) = e2 B * e2 Z := by
    rw [e2_end_comm_of_mem B Z (B * Z ^ 2) (B * Z) hBZ hBZ2mem hBZmem, hid3]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx
    exact apply_eq_zero_of_mul_eq_mul_e2 (e2 (B * Z)) (e2 B) (e2 B) x hcBZB (hB_idem x hx)
      (Submodule.mem_inf.mp hx).2
  · intro z hz
    exact apply_eq_zero_of_mul_eq_mul_e2 (e2 (B * Z)) (e2 (B * Z ^ 2)) (e2 B) z hid3
      (hBZ2_idem z hz) (Submodule.mem_inf.mp hz).2
  · intro x hx
    exact apply_eq_zero_of_mul_eq_mul_e2 (e2 (B * Z ^ 2)) (e2 B) (e2 B) x hcBZ2B (hB_idem x hx)
      (Submodule.mem_inf.mp hx).2
  · intro y hy
    exact apply_eq_zero_of_mul_eq_mul_e2 (e2 (B * Z ^ 2)) (e2 (B * Z)) (e2 B) y hcBZ2BZ
      (hBZ_idem y hy) (Submodule.mem_inf.mp hy).2

private def e2DecompMap (B Z : Module.End (ZMod 2) V) (hB : B ^ 3 = 1) (hZ : Z ^ 3 = 1)
    (hBZ : B * Z = Z * B) :
    ↥(LinearMap.ker (e2 Z)) →
      (↥(LinearMap.range (e2 B) ⊓ LinearMap.ker (e2 Z)) ×
        ↥(LinearMap.range (e2 (B * Z)) ⊓ LinearMap.ker (e2 Z))) ×
        ↥(LinearMap.range (e2 (B * Z ^ 2)) ⊓ LinearMap.ker (e2 Z)) :=
  fun u =>
    ((⟨e2 B u.1, ⟨⟨u.1, rfl⟩, (e2_decomp_sum B Z hB hZ hBZ).1 u.1 u.2⟩⟩,
      ⟨e2 (B * Z) u.1, ⟨⟨u.1, rfl⟩, (e2_decomp_sum B Z hB hZ hBZ).2.1 u.1 u.2⟩⟩),
      ⟨e2 (B * Z ^ 2) u.1, ⟨⟨u.1, rfl⟩,
        (e2_decomp_sum B Z hB hZ hBZ).2.2.1 u.1 u.2⟩⟩)

private theorem e2_decomp_bijective (B Z : Module.End (ZMod 2) V) (hB : B ^ 3 = 1)
    (hZ : Z ^ 3 = 1) (hBZ : B * Z = Z * B) :
    Function.Bijective (e2DecompMap B Z hB hZ hBZ) := by
  obtain ⟨_, _, _, hsum⟩ := e2_decomp_sum B Z hB hZ hBZ
  obtain ⟨hB_idem, hBZ_idem, hBZ2_idem⟩ := e2_decomp_idem B Z hB hZ hBZ
  obtain ⟨hB_ann, hB_ann2⟩ := e2_decomp_ann_B B Z hB hZ hBZ
  obtain ⟨hBZ_ann, hBZ_ann2, hBZ2_ann, hBZ2_ann2⟩ := e2_decomp_ann_BZ B Z hB hZ hBZ
  constructor
  · intro u v huv
    apply Subtype.ext
    have h1 : e2 B u.1 = e2 B v.1 := by
      have := congrArg (fun p => p.1.1.1) huv
      simpa [e2DecompMap] using this
    have h2 : e2 (B * Z) u.1 = e2 (B * Z) v.1 := by
      have := congrArg (fun p => p.1.2.1) huv
      simpa [e2DecompMap] using this
    have h3 : e2 (B * Z ^ 2) u.1 = e2 (B * Z ^ 2) v.1 := by
      have := congrArg (fun p => p.2.1) huv
      simpa [e2DecompMap] using this
    calc u.1 = e2 B u.1 + e2 (B * Z) u.1 + e2 (B * Z ^ 2) u.1 := (hsum u.1 u.2).symm
      _ = e2 B v.1 + e2 (B * Z) v.1 + e2 (B * Z ^ 2) v.1 := by rw [h1, h2, h3]
      _ = v.1 := hsum v.1 v.2
  · intro p
    refine ⟨⟨p.1.1.1 + p.1.2.1 + p.2.1, ?_⟩, ?_⟩
    · exact (LinearMap.ker (e2 Z)).add_mem
        ((LinearMap.ker (e2 Z)).add_mem p.1.1.2.2 p.1.2.2.2) p.2.2.2
    · apply Prod.ext
      · apply Prod.ext
        · apply Subtype.ext
          change e2 B (p.1.1.1 + p.1.2.1 + p.2.1) = p.1.1.1
          rw [map_add, map_add, hB_idem p.1.1 p.1.1.2, hB_ann p.1.2 p.1.2.2,
            hB_ann2 p.2 p.2.2]
          abel
        · apply Subtype.ext
          change e2 (B * Z) (p.1.1.1 + p.1.2.1 + p.2.1) = p.1.2.1
          rw [map_add, map_add, hBZ_ann p.1.1 p.1.1.2, hBZ_idem p.1.2 p.1.2.2,
            hBZ_ann2 p.2 p.2.2]
          abel
      · apply Subtype.ext
        change e2 (B * Z ^ 2) (p.1.1.1 + p.1.2.1 + p.2.1) = p.2.1
        rw [map_add, map_add, hBZ2_ann p.1.1 p.1.1.2, hBZ2_ann2 p.1.2 p.1.2.2,
          hBZ2_idem p.2 p.2.2]
        abel

private theorem e2_decomp_card (B Z : Module.End (ZMod 2) V) (hB : B ^ 3 = 1)
    (hZ : Z ^ 3 = 1) (hBZ : B * Z = Z * B) :
    let U : Submodule (ZMod 2) V := LinearMap.ker (e2 Z)
    let Wb : Submodule (ZMod 2) V := LinearMap.range (e2 B) ⊓ U
    let Wbz : Submodule (ZMod 2) V := LinearMap.range (e2 (B * Z)) ⊓ U
    let Wbz2 : Submodule (ZMod 2) V := LinearMap.range (e2 (B * Z ^ 2)) ⊓ U
    Nat.card ↥U = Nat.card ↥Wb * Nat.card ↥Wbz * Nat.card ↥Wbz2 := by
  have h := Nat.card_congr
    (Equiv.ofBijective (e2DecompMap B Z hB hZ hBZ) (e2_decomp_bijective B Z hB hZ hBZ))
  rw [Nat.card_prod, Nat.card_prod] at h
  exact h

private theorem e2_decomp_card_Wb_eq (B Z X Xi : Module.End (ZMod 2) V)
    (hXiX : Xi * X = 1) (hXXi : X * Xi = 1) (hB : B ^ 3 = 1) (hZ : Z ^ 3 = 1)
    (hBZ : B * Z = Z * B) (hXZ : X * Z = Z * X) (hXB : Xi * B * X = B * Z ^ 2) :
    let U : Submodule (ZMod 2) V := LinearMap.ker (e2 Z)
    let Wb : Submodule (ZMod 2) V := LinearMap.range (e2 B) ⊓ U
    let Wbz : Submodule (ZMod 2) V := LinearMap.range (e2 (B * Z)) ⊓ U
    let Wbz2 : Submodule (ZMod 2) V := LinearMap.range (e2 (B * Z ^ 2)) ⊓ U
    Nat.card ↥Wb = Nat.card ↥Wbz ∧ Nat.card ↥Wb = Nat.card ↥Wbz2 := by
  let U : Submodule (ZMod 2) V := LinearMap.ker (e2 Z)
  let Wb : Submodule (ZMod 2) V := LinearMap.range (e2 B) ⊓ U
  let Wbz : Submodule (ZMod 2) V := LinearMap.range (e2 (B * Z)) ⊓ U
  let Wbz2 : Submodule (ZMod 2) V := LinearMap.range (e2 (B * Z ^ 2)) ⊓ U
  obtain ⟨hB_idem, hBZ_idem, hBZ2_idem⟩ := e2_decomp_idem B Z hB hZ hBZ
  obtain ⟨_, _, _, hXeZ, hBZ_X, hBZ2_X, hB_X⟩ :=
    e2_conj_relations B Z X Xi hXiX hXXi hB hZ hBZ hXZ hXB
  have hXinj : Function.Injective X := by
    intro a b hab
    simpa [← Module.End.mul_apply, hXiX] using congrArg Xi hab
  have hφ : Nat.card ↥Wb ≤ Nat.card ↥Wbz :=
    card_le_of_map_mem X hXinj (fun w hw =>
      ⟨⟨X w, by
          change e2 (B * Z) (X w) = X w
          rw [← Module.End.mul_apply, hBZ_X, Module.End.mul_apply, hB_idem w hw]⟩, by
          change e2 Z (X w) = 0
          rw [← Module.End.mul_apply, hXeZ.symm, Module.End.mul_apply,
            (Submodule.mem_inf.mp hw).2, map_zero]⟩)
  have hψ : Nat.card ↥Wbz ≤ Nat.card ↥Wbz2 :=
    card_le_of_map_mem X hXinj (fun w hw =>
      ⟨⟨X w, by
          change e2 (B * Z ^ 2) (X w) = X w
          rw [← Module.End.mul_apply, hBZ2_X, Module.End.mul_apply, hBZ_idem w hw]⟩, by
          change e2 Z (X w) = 0
          rw [← Module.End.mul_apply, hXeZ.symm, Module.End.mul_apply,
            (Submodule.mem_inf.mp hw).2, map_zero]⟩)
  have hχ : Nat.card ↥Wbz2 ≤ Nat.card ↥Wb :=
    card_le_of_map_mem X hXinj (fun w hw =>
      ⟨⟨X w, by
          change e2 B (X w) = X w
          rw [← Module.End.mul_apply, hB_X, Module.End.mul_apply, hBZ2_idem w hw]⟩, by
          change e2 Z (X w) = 0
          rw [← Module.End.mul_apply, hXeZ.symm, Module.End.mul_apply,
            (Submodule.mem_inf.mp hw).2, map_zero]⟩)
  exact ⟨le_antisymm hφ (hψ.trans hχ), le_antisymm (hφ.trans hψ) hχ⟩

private theorem e2_decomp_Z_mem_Wb (B Z : Module.End (ZMod 2) V) (hB : B ^ 3 = 1)
    (hZ : Z ^ 3 = 1) (hBZ : B * Z = Z * B) :
    ∀ w : V, w ∈ LinearMap.range (e2 B) ⊓ LinearMap.ker (e2 Z) →
      Z w ∈ LinearMap.range (e2 B) ⊓ LinearMap.ker (e2 Z) := by
  obtain ⟨hB_idem, _, _⟩ := e2_decomp_idem B Z hB hZ hBZ
  have hZeB := e2_mul_comm_of_mem B Z B hBZ (Subring.subset_closure (by simp))
  have hZeZ := e2_mul_comm_of_mem B Z Z hBZ (Subring.subset_closure (by simp))
  intro w hw
  refine ⟨⟨Z w, by
      change e2 B (Z w) = Z w
      rw [← Module.End.mul_apply, hZeB.symm, Module.End.mul_apply, hB_idem w hw]⟩, by
      change e2 Z (Z w) = 0
      rw [← Module.End.mul_apply, hZeZ.symm, Module.End.mul_apply,
        (Submodule.mem_inf.mp hw).2, map_zero]⟩

private theorem e2_decomp_Z_fpf_Wb (B Z : Module.End (ZMod 2) V) (hZ : Z ^ 3 = 1) :
    ∀ w : V, w ∈ LinearMap.range (e2 B) ⊓ LinearMap.ker (e2 Z) → Z w = w → w = 0 := by
  intro w hw hZw
  have hwU : e2 Z w = 0 := (Submodule.mem_inf.mp hw).2
  have hwE : e2 Z w = w := (e2_eq_self_iff Z hZ w).mpr hZw
  rw [hwE] at hwU
  exact hwU

theorem U_decomp (B Z X Xi : Module.End (ZMod 2) V)
    (hXiX : Xi * X = 1) (hXXi : X * Xi = 1)
    (hB : B ^ 3 = 1) (hZ : Z ^ 3 = 1) (hBZ : B * Z = Z * B)
    (hXZ : X * Z = Z * X) (hXB : Xi * B * X = B * Z ^ 2) :
    let U : Submodule (ZMod 2) V := LinearMap.ker (e2 Z)
    let Wb : Submodule (ZMod 2) V := LinearMap.range (e2 B) ⊓ U
    let Wbz : Submodule (ZMod 2) V := LinearMap.range (e2 (B * Z)) ⊓ U
    let Wbz2 : Submodule (ZMod 2) V := LinearMap.range (e2 (B * Z ^ 2)) ⊓ U
    U = Wb ⊔ Wbz ⊔ Wbz2 ∧ Nat.card ↥Wb = Nat.card ↥Wbz ∧
      Nat.card ↥Wb = Nat.card ↥Wbz2 ∧
      Nat.card ↥U = Nat.card ↥Wb * Nat.card ↥Wbz * Nat.card ↥Wbz2 ∧
      (∀ w : V, w ∈ Wb → Z w ∈ Wb) ∧ (∀ w : V, w ∈ Wb → Z w = w → w = 0) := by
  obtain ⟨hcard1, hcard2⟩ := e2_decomp_card_Wb_eq B Z X Xi hXiX hXXi hB hZ hBZ hXZ hXB
  exact ⟨e2_decomp_span B Z hB hZ hBZ, hcard1, hcard2, e2_decomp_card B Z hB hZ hBZ,
    e2_decomp_Z_mem_Wb B Z hB hZ hBZ, e2_decomp_Z_fpf_Wb B Z hZ⟩

theorem U_card_eq_64 (B Z X Xi : Module.End (ZMod 2) V)
    (hXiX : Xi * X = 1) (hXXi : X * Xi = 1)
    (hB : B ^ 3 = 1) (hZ : Z ^ 3 = 1) (hBZ : B * Z = Z * B)
    (hXZ : X * Z = Z * X) (hXB : Xi * B * X = B * Z ^ 2) (hZ1 : Z ≠ 1)
    (hV : Nat.card V ≤ 64 * Nat.card {v : V // Z v = v}) :
    Nat.card ↥(LinearMap.ker (e2 Z)) = 64 := by
  classical
  have he : IsIdempotentElem (e2 Z) := e2_end_mul_self Z hZ
  have hcompl : IsCompl (LinearMap.range (e2 Z)) (LinearMap.ker (e2 Z)) :=
    LinearMap.IsIdempotentElem.isCompl he
  have hcard : Nat.card V =
      Nat.card ↥(LinearMap.range (e2 Z)) * Nat.card ↥(LinearMap.ker (e2 Z)) := by
    have h := Nat.card_congr (Submodule.prodEquivOfIsCompl _ _ hcompl).toEquiv
    rw [Nat.card_prod] at h
    exact h.symm
  have hfix : Nat.card ↥(LinearMap.range (e2 Z)) = Nat.card {v : V // Z v = v} :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun v => mem_range_e2_iff Z hZ v))
  have hlow : 64 * Nat.card {v : V // Z v = v} ≤ Nat.card V :=
    sixtyFour_le_index_fixed_end B Z X Xi hXiX hXXi hB hZ hBZ hXZ hXB hZ1
  haveI : Nonempty {v : V // Z v = v} := ⟨⟨0, map_zero Z⟩⟩
  have hCpos : 0 < Nat.card {v : V // Z v = v} := Nat.card_pos
  have hge : 64 ≤ Nat.card ↥(LinearMap.ker (e2 Z)) := by
    rw [hcard, hfix, mul_comm 64] at hlow
    exact Nat.le_of_mul_le_mul_left hlow hCpos
  have hle : Nat.card ↥(LinearMap.ker (e2 Z)) ≤ 64 := by
    rw [hcard, hfix, mul_comm 64] at hV
    exact Nat.le_of_mul_le_mul_left hV hCpos
  omega

theorem mul_e2_comm_of_comm (A B : Module.End (ZMod 2) V) (hAB : A * B = B * A) :
    A * e2 B = e2 B * A := by
  let S : Subring (Module.End (ZMod 2) V) := Subring.closure ({A, B} : Set _)
  letI : CommRing S := Subring.closureCommRingOfComm (pairwise_commute_pair hAB)
  let A' : S := ⟨A, Subring.subset_closure (by simp)⟩
  let B' : S := ⟨B, Subring.subset_closure (by simp)⟩
  have key : A' * e2 B' = e2 B' * A' := mul_comm _ _
  have h := congrArg Subtype.val key
  change A * ((e2 B' : S) : Module.End (ZMod 2) V) =
    ((e2 B' : S) : Module.End (ZMod 2) V) * A at h
  rw [e2_subring_coe S B'] at h
  simpa using h

theorem mul_e2_eq_self (Z : Module.End (ZMod 2) V) (hZ : Z ^ 3 = 1) : Z * e2 Z = e2 Z := by
  ext w
  exact g_apply_e2 Z hZ w

theorem e2_mul_self_eq_self (Z : Module.End (ZMod 2) V) (hZ : Z ^ 3 = 1) :
    e2 Z * Z = e2 Z := by
  rw [← mul_e2_comm_of_comm Z Z rfl, mul_e2_eq_self Z hZ]

theorem e2_mul_one_sub (Z : Module.End (ZMod 2) V) (hZ : Z ^ 3 = 1) :
    e2 Z * (1 - Z) = 0 := by
  rw [mul_sub, mul_one, e2_mul_self_eq_self Z hZ, sub_self]

theorem ker_e2_eq_range_one_sub (Z : Module.End (ZMod 2) V) (hZ : Z ^ 3 = 1) :
    LinearMap.ker (e2 Z) = LinearMap.range (1 - Z) := by
  have hle : LinearMap.range (1 - Z) ≤ LinearMap.ker (e2 Z) := by
    rintro v ⟨w, rfl⟩
    rw [LinearMap.mem_ker, ← Module.End.mul_apply, e2_mul_one_sub Z hZ, LinearMap.zero_apply]
  have hfin : Module.finrank (ZMod 2) ↥(LinearMap.range (1 - Z)) =
      Module.finrank (ZMod 2) ↥(LinearMap.ker (e2 Z)) := by
    have h1 : Module.finrank (ZMod 2) ↥(LinearMap.ker (1 - Z)) =
        Module.finrank (ZMod 2) ↥(LinearMap.range (e2 Z)) := by
      rw [range_e2_eq_ker_one_sub Z hZ]
    have h2 := LinearMap.finrank_range_add_finrank_ker (1 - Z : V →ₗ[ZMod 2] V)
    have h3 := LinearMap.finrank_range_add_finrank_ker (e2 Z : V →ₗ[ZMod 2] V)
    rw [h1] at h2
    omega
  exact (Submodule.eq_of_le_of_finrank_eq hle hfin).symm

theorem e2_eq (Z : Module.End (ZMod 2) V) (hZ : Z ^ 3 = 1) :
    e2 Z = 1 + Z + Z ^ 2 := by
  have hlin : ∀ a : V, Z a = a → (1 + Z + Z ^ 2 : Module.End (ZMod 2) V) a = a := by
    intro a ha
    simp only [LinearMap.add_apply, Module.End.one_apply, pow_two, Module.End.mul_apply, ha,
      add_assoc, add_self_eq_zero_zmod2, zero_add, add_zero]
  have hmul : (1 + Z + Z ^ 2 : Module.End (ZMod 2) V) * (1 - Z) = 0 := by
    rw [show (1 + Z + Z ^ 2 : Module.End (ZMod 2) V) * (1 - Z) = 1 - Z ^ 3 by
      noncomm_ring, hZ, sub_self]
  ext v
  have hva : e2 Z (e2 Z v) = e2 Z v := by
    rw [← Module.End.mul_apply, e2_end_mul_self Z hZ]
  have hZva : Z (e2 Z v) = e2 Z v :=
    (mem_range_e2_iff Z hZ (e2 Z v)).mp ⟨v, rfl⟩
  have hb : v - e2 Z v ∈ LinearMap.range (1 - Z) := by
    rw [← ker_e2_eq_range_one_sub Z hZ]
    rw [LinearMap.mem_ker, map_sub, hva, sub_self]
  obtain ⟨w, hw⟩ := hb
  have hker : (1 + Z + Z ^ 2 : Module.End (ZMod 2) V) (v - e2 Z v) = 0 := by
    rw [← hw, ← Module.End.mul_apply, hmul, LinearMap.zero_apply]
  have hv : v = e2 Z v + (v - e2 Z v) := by abel
  have h1 : (1 + Z + Z ^ 2 : Module.End (ZMod 2) V) v = e2 Z v := by
    conv_lhs => rw [hv]
    rw [map_add, hlin (e2 Z v) hZva, hker, add_zero]
  exact h1.symm

theorem range_e2_invariant_of_comm (T A : Module.End (ZMod 2) V) (h : T * A = A * T) :
    ∀ w : V, w ∈ LinearMap.range (e2 A) → T w ∈ LinearMap.range (e2 A) := by
  rintro w ⟨u, rfl⟩
  exact ⟨T u, by
    conv_rhs => rw [← Module.End.mul_apply, mul_e2_comm_of_comm T A h, Module.End.mul_apply]⟩

theorem eq_one_or_fpf_on_of_card_four (W : Submodule (ZMod 2) V) (T : Module.End (ZMod 2) V)
    (hWcard : Nat.card ↥W = 4) (hWinv : ∀ x : V, x ∈ W → T x ∈ W) (hT : T ^ 3 = 1) :
    (∀ x : V, x ∈ W → T x = x) ∨ (∀ x : V, x ∈ W → T x = x → x = 0) := by
  have h2 : 2 ^ Module.finrank (ZMod 2) ↥W = 4 := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := ↥W)
    rw [Nat.card_zmod] at h
    rw [← h, hWcard]
  have hfinle : Module.finrank (ZMod 2) ↥W ≤ 2 := by
    by_contra h
    push Not at h
    have h3 : 3 ≤ Module.finrank (ZMod 2) ↥W := by omega
    have hpow := Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) h3
    rw [h2] at hpow
    norm_num at hpow
  have hTrestrict : (T.restrict hWinv) ^ 3 = 1 := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change (T ^ 3) (x : V) = (x : V)
    rw [hT, Module.End.one_apply]
  rcases eq_one_or_fpf_of_finrank_le_two (T.restrict hWinv) hTrestrict hfinle with h1 | hfpf
  · left
    intro x hx
    have hx' := congrArg (fun f : ↥W →ₗ[ZMod 2] ↥W => f ⟨x, hx⟩) h1
    have hx'' := congrArg Subtype.val hx'
    simpa using hx''
  · right
    intro x hx hTx
    have hfix : (T.restrict hWinv) ⟨x, hx⟩ = ⟨x, hx⟩ := by
      apply Subtype.ext
      simpa using hTx
    exact Subtype.ext_iff.mp (hfpf ⟨x, hx⟩ hfix)

theorem Y_eq_bot_of_fpf (A0 A1 A2 B Z : Module.End (ZMod 2) V)
    (hA03 : A0 ^ 3 = 1) (hA13 : A1 ^ 3 = 1) (hA23 : A2 ^ 3 = 1) (hB3 : B ^ 3 = 1)
    (hZ3 : Z ^ 3 = 1) (hA02 : A0 * A2 = A2 * A0) (hA12 : A1 * A2 = A2 * A1)
    (hA2Z : A2 * Z = Z * A2) (hprod : A0 * A1 * A2 = Z) (hBA1 : B * A1 = A0)
    (hfpf : ∀ x : V, x ∈ LinearMap.range (e2 B) ⊓ LinearMap.ker (e2 Z) → A0 x = x → x = 0) :
    LinearMap.range (e2 A0) ⊓ LinearMap.range (e2 A1) ⊓ LinearMap.ker (e2 A2) = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro y hy
  obtain ⟨⟨hy0, hy1⟩, hy2⟩ := hy
  have h0 : A0 y = y := (mem_range_e2_iff A0 hA03 y).mp hy0
  have h1 : A1 y = y := (mem_range_e2_iff A1 hA13 y).mp hy1
  have hstep1 : A1 (A2 y) = A2 y := by
    rw [← Module.End.mul_apply, hA12, Module.End.mul_apply, h1]
  have hstep2 : A0 (A2 y) = A2 y := by
    rw [← Module.End.mul_apply, hA02, Module.End.mul_apply, h0]
  have hZy : Z y = A2 y := by
    have h := congrArg (fun f : Module.End (ZMod 2) V => f y) hprod
    simp only [Module.End.mul_apply] at h
    rw [← h, hstep1, hstep2]
  have hZZ : Z (Z y) = A2 (A2 y) := by
    calc Z (Z y) = Z (A2 y) := by rw [hZy]
      _ = A2 (Z y) := by rw [← Module.End.mul_apply, ← hA2Z, Module.End.mul_apply]
      _ = A2 (A2 y) := by rw [hZy]
  have heq : e2 Z y = e2 A2 y := by
    rw [e2_eq Z hZ3, e2_eq A2 hA23]
    simp only [LinearMap.add_apply, Module.End.one_apply, pow_two, Module.End.mul_apply]
    rw [hZZ, hZy]
  have hkerZ : e2 Z y = 0 := by rw [heq, hy2]
  have hpow : A1 ^ 3 = A1 * A1 ^ 2 := by
    rw [show (3 : ℕ) = 1 + 2 by norm_num, pow_add, pow_one]
  have hB : B = A0 * A1 ^ 2 := by
    calc B = B * A1 ^ 3 := by rw [hA13, mul_one]
      _ = B * (A1 * A1 ^ 2) := by rw [hpow]
      _ = (B * A1) * A1 ^ 2 := by rw [mul_assoc]
      _ = A0 * A1 ^ 2 := by rw [hBA1]
  have hA1sq : (A1 ^ 2) y = y := by rw [pow_two, Module.End.mul_apply, h1, h1]
  have hBy : B y = y := by rw [hB, Module.End.mul_apply, hA1sq, h0]
  have hyB : y ∈ LinearMap.range (e2 B) := (mem_range_e2_iff B hB3 y).mpr hBy
  exact hfpf y ⟨hyB, hkerZ⟩ h0

theorem pair_eq_of_Y_eq_bot (A0 A1 A2 : Module.End (ZMod 2) V)
    (hA02 : A0 * A2 = A2 * A0) (hA12 : A1 * A2 = A2 * A1) (hA23 : A2 ^ 3 = 1)
    (hY : LinearMap.range (e2 A0) ⊓ LinearMap.range (e2 A1) ⊓ LinearMap.ker (e2 A2) = ⊥) :
    LinearMap.range (e2 A0) ⊓ LinearMap.range (e2 A1) =
      LinearMap.range (e2 A0) ⊓ LinearMap.range (e2 A1) ⊓ LinearMap.range (e2 A2) := by
  apply le_antisymm
  · intro w hw
    refine ⟨hw, ?_⟩
    have hc0 : e2 A2 * e2 A0 = e2 A0 * e2 A2 :=
      e2_end_comm_of_mem A2 A0 A2 A0 hA02.symm (Subring.subset_closure (by simp))
        (Subring.subset_closure (by simp))
    have hc1 : e2 A2 * e2 A1 = e2 A1 * e2 A2 :=
      e2_end_comm_of_mem A2 A1 A2 A1 hA12.symm (Subring.subset_closure (by simp))
        (Subring.subset_closure (by simp))
    have hpres0 : ∀ x ∈ LinearMap.range (e2 A0), e2 A2 x ∈ LinearMap.range (e2 A0) := by
      rintro _ ⟨u, rfl⟩
      exact ⟨e2 A2 u, by
        rw [← Module.End.mul_apply, ← Module.End.mul_apply, hc0, Module.End.mul_apply]⟩
    have hpres1 : ∀ x ∈ LinearMap.range (e2 A1), e2 A2 x ∈ LinearMap.range (e2 A1) := by
      rintro _ ⟨u, rfl⟩
      exact ⟨e2 A2 u, by
        rw [← Module.End.mul_apply, ← Module.End.mul_apply, hc1, Module.End.mul_apply]⟩
    have hwA2 : e2 A2 w ∈ LinearMap.range (e2 A0) ⊓ LinearMap.range (e2 A1) :=
      ⟨hpres0 w hw.1, hpres1 w hw.2⟩
    have hker : w - e2 A2 w ∈ LinearMap.ker (e2 A2) := by
      rw [LinearMap.mem_ker, map_sub, ← Module.End.mul_apply, e2_end_mul_self A2 hA23, sub_self]
    have hmem : w - e2 A2 w ∈
        LinearMap.range (e2 A0) ⊓ LinearMap.range (e2 A1) ⊓ LinearMap.ker (e2 A2) :=
      ⟨⟨Submodule.sub_mem _ hw.1 hwA2.1, Submodule.sub_mem _ hw.2 hwA2.2⟩, hker⟩
    rw [hY, Submodule.mem_bot] at hmem
    exact ⟨w, (sub_eq_zero.mp hmem).symm⟩
  · exact inf_le_left

end CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC49
