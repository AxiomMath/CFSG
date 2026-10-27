module

public import CFSG.Quasithin.H13.GoldschmidtC137U33S2Gen

public section

namespace CFSG.Quasithin.H13.U3.GC137.S2

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Quasithin.H13.Orbit

@[expose] def act (g : Gam) (c : ℕ) : ℕ := mact (matCode g.1) c

theorem act_lt (g : Gam) (c : ℕ) : act g c < 256 := mact_lt' g.1 c

theorem decodeZ_act (g : Gam) {c : ℕ} (hc : c < 256) : decodeZ (act g c) = g.1 (decodeZ c) :=
  decodeZ_mact' g.1 hc

theorem act_mul (g h : Gam) {c : ℕ} (hc : c < 256) : act (g * h) c = act g (act h c) := by
  refine decodeZ_injective (act_lt _ _) (act_lt _ _) ?_
  rw [decodeZ_act _ hc, decodeZ_act _ (act_lt _ _), decodeZ_act _ hc]
  rfl

theorem act_one {c : ℕ} (hc : c < 256) : act (1 : Gam) c = c := by
  refine decodeZ_injective (act_lt _ _) hc ?_
  rw [decodeZ_act _ hc]
  rfl

theorem act_inj (g : Gam) {x y : ℕ} (hx : x < 256) (hy : y < 256) (h : act g x = act g y) :
    x = y := by
  refine decodeZ_injective hx hy ?_
  have h1 : g.1 (decodeZ x) = g.1 (decodeZ y) := by
    rw [← decodeZ_act _ hx, ← decodeZ_act _ hy, h]
  exact g.1.injective h1

theorem act_inv_act (g : Gam) {c : ℕ} (hc : c < 256) : act g⁻¹ (act g c) = c := by
  rw [← act_mul _ _ hc, inv_mul_cancel, act_one hc]

theorem act_zero (g : Gam) : act g 0 = 0 := by
  refine decodeZ_injective (act_lt _ _) (by norm_num) ?_
  rw [decodeZ_act _ (by norm_num), decodeZ_zero, map_zero]

theorem act_xor (g : Gam) {a b : ℕ} (ha : a < 256) (hb : b < 256) :
    act g (a ^^^ b) = act g a ^^^ act g b := by
  refine decodeZ_injective (act_lt _ _) (xor_lt_256 (act_lt _ _) (act_lt _ _)) ?_
  rw [decodeZ_act _ (xor_lt_256 ha hb), decodeZ_xor, decodeZ_xor, decodeZ_act _ ha,
    decodeZ_act _ hb, map_add]

instance : MulAction Gam O0C where
  smul g c := o0Act g c
  one_smul c := Subtype.ext (act_one (mem_o0Codes.1 c.2).1)
  mul_smul g h c := Subtype.ext (act_mul g h (mem_o0Codes.1 c.2).1)

@[expose] def bitN (c k : ℕ) : ℕ := if c.testBit k then 1 else 0

@[expose] def normC (c : ℕ) : ℕ :=
  (bitN c 0 * bitN c 7 + (bitN c 1 * bitN c 4 + bitN c 2 * bitN c 5 + bitN c 3 * bitN c 6)) % 2

@[expose] def isPt (c : ℕ) : Bool := c != 0 && normC c == 0

theorem norm_decodeZ : ∀ c < 256, (zornNorm (decodeZ c) = 0 ↔ normC c = 0) := by
  decide +kernel

theorem normC_act (g : Gam) {c : ℕ} (hc : c < 256) : normC (act g c) = 0 ↔ normC c = 0 := by
  rw [← norm_decodeZ _ (act_lt _ _), ← norm_decodeZ _ hc, decodeZ_act _ hc,
    quasithinG2_norm g.2]

theorem isPt_act (g : Gam) {c : ℕ} (hc : c < 256) (h : isPt c = true) : isPt (act g c) = true := by
  simp only [isPt, Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at h ⊢
  refine ⟨fun h0 => h.1 ?_, (normC_act g hc).2 h.2⟩
  have : act g c = act g 0 := by rw [h0, act_zero]
  exact act_inj g hc (by norm_num) this

@[expose] def pt0 : O0C := ⟨8, by decide⟩

@[expose] def Ppt : Subgroup Gam := MulAction.stabilizer Gam pt0

theorem mem_Ppt {g : Gam} : g ∈ Ppt ↔ act g 8 = 8 := by
  rw [Ppt, MulAction.mem_stabilizer_iff]
  exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

theorem act_sEltG {i : ℕ} (hi : i < 64) (c : ℕ) : act (sEltG i) c = mact (sM i) c := by
  unfold act
  rw [matCode_sEltG hi]

theorem sM_fix8 : ∀ i < 64, mact (sM i) 8 = 8 := by
  decide +kernel

theorem sSubG_fix (s : Gam) (hs : s ∈ sSubG) : act s 8 = 8 := by
  obtain ⟨i, hi, rfl⟩ := mem_sSubG.1 hs
  rw [act_sEltG hi]
  exact sM_fix8 i hi

theorem sSubG_le_Ppt : sSubG ≤ Ppt := fun s hs => mem_Ppt.2 (sSubG_fix s hs)

@[expose] def ell0 : List ℕ := [8, 32, 40]

theorem ell0_perm : ∀ a ∈ ell0, ∀ b ∈ ell0, ∀ c ∈ ell0, a ≠ b → a ≠ c → b ≠ c →
    ∀ x ∈ ell0, x = a ∨ x = b ∨ x = c := by
  decide

theorem ell0_lt : ∀ x ∈ ell0, x < 256 := by
  decide

@[expose] def Pline : Subgroup Gam where
  carrier := {g | ∀ c ∈ ell0, act g c ∈ ell0}
  mul_mem' := fun {g h} hg hh c hc => by
    rw [act_mul g h (ell0_lt c hc)]
    exact hg _ (hh c hc)
  one_mem' := fun c hc => by
    rw [act_one (ell0_lt c hc)]
    exact hc
  inv_mem' := fun {g} hg c hc => by
    have h8 : (8 : ℕ) ∈ ell0 := by decide
    have h32 : (32 : ℕ) ∈ ell0 := by decide
    have h40 : (40 : ℕ) ∈ ell0 := by decide
    have hab : act g 8 ≠ act g 32 := fun h => by
      have := act_inj g (by norm_num) (by norm_num) h
      omega
    have hac : act g 8 ≠ act g 40 := fun h => by
      have := act_inj g (by norm_num) (by norm_num) h
      omega
    have hbc : act g 32 ≠ act g 40 := fun h => by
      have := act_inj g (by norm_num) (by norm_num) h
      omega
    rcases ell0_perm _ (hg 8 h8) _ (hg 32 h32) _ (hg 40 h40) hab hac hbc c hc with h | h | h
    · rw [h, act_inv_act g (by norm_num)]
      exact h8
    · rw [h, act_inv_act g (by norm_num)]
      exact h32
    · rw [h, act_inv_act g (by norm_num)]
      exact h40

theorem sM_ell0 : ∀ c ∈ ell0, ∀ i < 64, mact (sM i) c ∈ ell0 := by
  decide +kernel

theorem sSubG_le_Pline : sSubG ≤ Pline := by
  intro s hs c hc
  obtain ⟨i, hi, rfl⟩ := mem_sSubG.1 hs
  rw [act_sEltG hi]
  exact sM_ell0 c hc i hi

end CFSG.Quasithin.H13.U3.GC137.S2
