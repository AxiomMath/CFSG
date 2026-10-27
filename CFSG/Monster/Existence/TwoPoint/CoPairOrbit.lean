module

public import CFSG.Monster.Existence.Co2Bridge
public import Certificates.Data.CFSGNative.MonsterAxis.CoPair

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Existence.CoPair

open CFSG.Monster CFSG.Monster.SpinLattice CFSG.Monster.VisCert CFSG.Monster.VisQuot
  CFSG.Monster.B.Short CFSG.Monster.B.Co2 CFSG.Monster.Existence.Co2Bridge
  CFSG.Monster.Existence.CoPair.Native

theorem native_actGo_eq (rows : Array ℕ) (v : ℕ) :
    ∀ n acc, VisCert.Native.actGo rows v n acc = VisCert.actGo rows v n acc
  | 0, _ => rfl
  | n + 1, acc => by rw [VisCert.Native.actGo, VisCert.actGo, native_actGo_eq rows v n]

theorem native_actRows_eq (rows : Array ℕ) (v : ℕ) :
    VisCert.Native.actRows rows v = VisCert.actRows rows v :=
  native_actGo_eq rows v 24 0

theorem kOp_alphaK_dec
    {l : ℕ} (hl : l < 24) (v : ℕ) :
    kOp (alphaK l).1 (dec v) = dec (VisCert.Native.actRows (letterRows l) v) := by
  have h : alphaK l = ⟨alpha ⟨l, hl⟩, alpha_mem_Kv _⟩ := by simp [alphaK, hl]
  rw [h]
  show kOp (alpha ⟨l, hl⟩) (dec v) = _
  rw [kOp_alpha_dec, native_actRows_eq]
  rfl

theorem kOp_wordK_dec
    (w : List ℕ) (hw : ∀ l ∈ w, l < 24) (v : ℕ) :
    kOp (wordK w).1 (dec v) = dec (actLetters w v) := by
  induction w generalizing v with
  | nil =>
    rw [wordK, List.map_nil, List.prod_nil]
    exact LinearMap.congr_fun kOp_one (dec v)
  | cons l w ih =>
    have hl : l < 24 := hw l List.mem_cons_self
    rw [wordK, List.map_cons, List.prod_cons, Subgroup.coe_mul, kOp_mul]
    change kOp (wordK w).1 (kOp (alphaK l).1 (dec v)) = _
    rw [kOp_alphaK_dec hl, ih (fun l' hl' => hw l' (List.mem_cons_of_mem _ hl'))]
    rfl

theorem xWordN_eq : xWordN = xWord := rfl

theorem yWordN_eq : yWordN = yWord := rfl

theorem kOp_xK_dec
    (v : ℕ) : kOp xK.1 (dec v) = dec (actLetters xWordN v) := by
  rw [xK, kOp_wordK_dec xWord xWord_lt, xWordN_eq]

theorem kOp_yK_dec
    (v : ℕ) : kOp yK.1 (dec v) = dec (actLetters yWordN v) := by
  rw [yK, kOp_wordK_dec yWord yWord_lt, yWordN_eq]

@[expose] def xyK : List ℕ → Kstab v0
  | [] => 1
  | g :: w => (if g = 0 then xK else yK) * xyK w

theorem kOp_xyK_dec
    (w : List ℕ) (v : ℕ) : kOp (xyK w).1 (dec v) = dec (actXY w v) := by
  induction w generalizing v with
  | nil =>
    rw [xyK]
    exact LinearMap.congr_fun kOp_one (dec v)
  | cons g w ih =>
    rw [xyK, Subgroup.coe_mul, kOp_mul]
    change kOp (xyK w).1 (kOp (if g = 0 then xK else yK).1 (dec v)) = _
    by_cases hg : g = 0
    · rw [ite_eq_left hg, kOp_xK_dec, ih]
      simp [actXY, hg]
    · rw [ite_eq_right hg, kOp_yK_dec, ih]
      simp [actXY, hg]

@[expose, instance_reducible] def kvLeft : MulAction (Kstab v0) L2 where
  smul k x := kOp ((k⁻¹ : Kstab v0) : OLq) x
  one_smul x := by
    change kOp (((1 : Kstab v0)⁻¹ : Kstab v0) : OLq) x = x
    rw [inv_one]
    exact LinearMap.congr_fun kOp_one x
  mul_smul k k' x := by
    change kOp (((k * k')⁻¹ : Kstab v0) : OLq) x =
      kOp ((k⁻¹ : Kstab v0) : OLq) (kOp ((k'⁻¹ : Kstab v0) : OLq) x)
    rw [mul_inv_rev, Subgroup.coe_mul, kOp_mul]
    rfl

attribute [local instance] kvLeft

theorem kvLeft_smul (k : Kstab v0) (x : L2) : k • x = kOp ((k⁻¹ : Kstab v0) : OLq) x := rfl

theorem kvLeft_inv_smul (k : Kstab v0) (x : L2) : k⁻¹ • x = kOp (k : OLq) x := by
  rw [kvLeft_smul, inv_inv]

theorem kOp_inv_kOp (k : OLq) (x : L2) : kOp k⁻¹ (kOp k x) = x := by
  have h := LinearMap.congr_fun (kOp_mul k k⁻¹) x
  rw [mul_inv_cancel, kOp_one] at h
  exact h.symm

theorem kOp_kOp_inv (k : OLq) (x : L2) : kOp k (kOp k⁻¹ x) = x := by
  simpa using kOp_inv_kOp k⁻¹ x

@[expose] def kvStab (x : L2) : Subgroup (Kstab v0) where
  carrier := {k | kOp (k : OLq) x = x}
  one_mem' := LinearMap.congr_fun kOp_one x
  mul_mem' {k k'} hk hk' := by
    change kOp ((k * k' : Kstab v0) : OLq) x = x
    rw [Subgroup.coe_mul, kOp_mul]
    change kOp (k' : OLq) (kOp (k : OLq) x) = x
    rw [show kOp (k : OLq) x = x from hk]
    exact hk'
  inv_mem' {k} hk := by
    change kOp (((k⁻¹ : Kstab v0)) : OLq) x = x
    have h : kOp (k : OLq) x = x := hk
    conv_lhs => rw [← h]
    exact kOp_inv_kOp (k : OLq) x

theorem mem_kvStab {x : L2} {k : Kstab v0} : k ∈ kvStab x ↔ kOp (k : OLq) x = x := Iff.rfl

theorem stabilizer_kvLeft (x : L2) : MulAction.stabilizer (Kstab v0) x = kvStab x := by
  ext k
  rw [MulAction.mem_stabilizer_iff, kvLeft_smul]
  show k⁻¹ ∈ kvStab x ↔ k ∈ kvStab x
  exact inv_mem_iff (H := kvStab x) (x := k)

theorem index_kvStab
    (x : L2) : (kvStab x).index = (MulAction.orbit (Kstab v0) x).ncard := by
  rw [← stabilizer_kvLeft]
  exact MulAction.index_stabilizer (Kstab v0) x

theorem ncard_orbit_mul
    (x : L2) :
    (MulAction.orbit (Kstab v0) x).ncard * Nat.card (kvStab x) = 42305421312000 := by
  rw [← index_kvStab, Subgroup.index_mul_card, natCard_Kv]

@[expose] def kvStabEquivInf (x : L2) : kvStab x ≃* ↥(Kstab v0 ⊓ Kstab x) where
  toFun k := ⟨(k.1 : OLq), k.1.2, k.2⟩
  invFun k := ⟨⟨k.1, k.2.1⟩, k.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

theorem natCard_inf_of_orbit
    {x : L2} {N : ℕ} (h : (MulAction.orbit (Kstab v0) x).ncard = N) :
    N * Nat.card ↥(Kstab v0 ⊓ Kstab x) = 42305421312000 := by
  rw [← h, ← Nat.card_congr (kvStabEquivInf x).toEquiv, ncard_orbit_mul]

theorem genXY_zero (v : ℕ) : genXY 0 v = actLetters xWordN v := by
  simp [genXY, actXY]

theorem genXY_one (v : ℕ) : genXY 1 v = actLetters yWordN v := by
  simp [genXY, actXY]

theorem dec_genXY_zero
    (v : ℕ) : dec (genXY 0 v) = xK⁻¹ • dec v := by
  rw [genXY_zero, kvLeft_inv_smul, kOp_xK_dec]

theorem dec_genXY_one
    (v : ℕ) : dec (genXY 1 v) = yK⁻¹ • dec v := by
  rw [genXY_one, kvLeft_inv_smul, kOp_yK_dec]

theorem orbPoint_spec {seed : ℕ} {lev par lab : ℕ → ℕ} {v : ℕ}
    (h : orbPoint seed lev par lab v = true) (hv : lev v ≠ 0) :
    (lev v = 1 → v = seed) ∧
    (lev v ≠ 1 → par v < 2 ^ 24 ∧ lab v < 2 ∧ lev (par v) + 1 = lev v ∧
      genXY (lab v) (par v) = v) ∧
    genXY 0 v < 2 ^ 24 ∧ lev (genXY 0 v) ≠ 0 ∧ genXY 1 v < 2 ^ 24 ∧ lev (genXY 1 v) ≠ 0 := by
  unfold orbPoint at h
  have h0 : (lev v == 0) = false := by simpa using hv
  simp only [h0, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq,
    bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  refine ⟨fun hl => ?_, fun hl => ?_, h2, h3, h4, h5⟩
  · simpa [hl] using h1
  · have hl' : (lev v == 1) = false := by simpa using hl
    simp only [hl', Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq,
      beq_iff_eq] at h1
    obtain ⟨⟨⟨hp, hg⟩, hlp⟩, hgp⟩ := h1
    exact ⟨hp, hg, hlp, hgp⟩

theorem dec_genXY
    {g : ℕ} (hg : g < 2) (v : ℕ) :
    dec (genXY g v) = (if g = 0 then xK⁻¹ else yK⁻¹) • dec v := by
  rcases (by omega : g = 0 ∨ g = 1) with rfl | rfl
  · simpa using dec_genXY_zero v
  · simpa using dec_genXY_one v

theorem ncard_orbit_of_orbCheck
    {seed N chunks : ℕ} {T : OrbTables} (hc : 0 < chunks)
    (h : orbCheck seed N T chunks = true) :
    (MulAction.orbit (Kstab v0) (dec seed)).ncard = N := by
  simp only [orbCheck, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨hs, hlev⟩, hpar⟩, hcount⟩ := h
  have hpt := VisCert.parAll_spec hc hpar
  let F : Set ℕ := {v | v < 2 ^ 24 ∧ VisCert.Native.rd8 T.lev v ≠ 0}
  have hFfin : (dec '' F).Finite :=
    ((Set.finite_lt_nat (2 ^ 24)).subset fun v hv => hv.1).image dec
  have hseed : seed ∈ F := ⟨hs, by rw [hlev]; omega⟩
  have hX : ∀ v ∈ F, genXY 0 v ∈ F := fun v hv => by
    obtain ⟨-, -, h2, h3, -, -⟩ := orbPoint_spec (hpt v hv.1) hv.2
    exact ⟨h2, h3⟩
  have hY : ∀ v ∈ F, genXY 1 v ∈ F := fun v hv => by
    obtain ⟨-, -, -, -, h4, h5⟩ := orbPoint_spec (hpt v hv.1) hv.2
    exact ⟨h4, h5⟩
  have hreach : ∀ m v, v < 2 ^ 24 → VisCert.Native.rd8 T.lev v = m → m ≠ 0 →
      dec v ∈ MulAction.orbit (Kstab v0) (dec seed) := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro v hv hm hm0
      obtain ⟨h1, hpar', -⟩ := orbPoint_spec (hpt v hv) (by rw [hm]; exact hm0)
      by_cases hl1 : VisCert.Native.rd8 T.lev v = 1
      · rw [h1 hl1]
        exact MulAction.mem_orbit_self _
      · obtain ⟨hp, hg, hlp, himg⟩ := hpar' hl1
        have hpl : VisCert.Native.rd8 T.lev (VisCert.Native.rd32 T.par v) ≠ 0 := by omega
        have ih' := ih (VisCert.Native.rd8 T.lev (VisCert.Native.rd32 T.par v)) (by omega)
          (VisCert.Native.rd32 T.par v) hp rfl hpl
        rw [← himg, dec_genXY hg]
        exact MulAction.mem_orbit_of_mem_orbit _ ih'
  have horb : MulAction.orbit (Kstab v0) (dec seed) = dec '' F := by
    apply Set.Subset.antisymm
    · rintro _ ⟨g, rfl⟩
      have hg : g ∈ Subgroup.closure ({xK⁻¹, yK⁻¹} : Set (Kstab v0)) := by
        rw [closure_inv_eq_top]
        trivial
      refine VisCert.orbit_closure_subset (S := ({xK⁻¹, yK⁻¹} : Set (Kstab v0))) hFfin ?_
        (x := dec seed) ⟨seed, hseed, rfl⟩ ⟨⟨g, hg⟩, rfl⟩
      rintro s (rfl | rfl) _ ⟨v, hv, rfl⟩
      · exact ⟨genXY 0 v, hX v hv, dec_genXY_zero v⟩
      · exact ⟨genXY 1 v, hY v hv, dec_genXY_one v⟩
    · rintro _ ⟨v, hv, rfl⟩
      exact hreach _ v hv.1 rfl hv.2
  have hcardF : F.ncard = N := by
    have hF : F = ↑((Finset.range (2 ^ 24)).filter fun v => VisCert.Native.rd8 T.lev v ≠ 0) := by
      ext v
      simp [F]
    rw [hF, Set.ncard_coe_finset, ← hcount, VisCert.countBelow_eq]
    congr 1
  have hinj : Set.InjOn dec F := fun a ha b hb hab => dec_injective ha.1 hb.1 hab
  rw [horb, hinj.ncard_image, hcardF]

end CFSG.Monster.Existence.CoPair
