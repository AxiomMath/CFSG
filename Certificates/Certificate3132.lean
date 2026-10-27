module

public import Certificates.Data.CFSGNative.CTIB.Arith
public import CFSG.Monster.B.GSide.MuFourOmega
public import Certificates.Kernel.MonsterB.Orb3132Tree
public import Certificates.Kernel.MonsterB.Orb3132Inv
public import CFSG.Certificates.Kernel.MonsterB.QFormSound
public import CFSG.Certificates.Kernel.MonsterB.CTIBBfsSound
public import CFSG.Monster.B.TwoA.Unitary.OrbitInputs
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.Monster.B.Classical.PlaneAut
public import CFSG.Monster.B.TwoA.Amalgam.CoFiberGraphAdj
public import CFSG.Monster.B.TwoA.Base.GeomNative
public import CFSG.Monster.B.TwoA.Par3.MainBase
public import CFSG.Monster.B.TwoA.Sp8.GenActionBase
public import CFSG.Monster.B.TwoA.Sp8.NormalizerBase
public import CFSG.Monster.B.TwoA.Sp8.Orth8Base
public import CFSG.Monster.B.TwoA.Sp8.SubgeomBuildingBase
public import CFSG.Monster.B.TwoA.Sp8.SubgeomFive
public import CFSG.Monster.B.TwoA.Sp8.SubgeomFiveBase
public import CFSG.Monster.B.TwoA.Sp8.SubgeomIsoBase
public import CFSG.Monster.B.TwoA.Sp8.SubgeomStdBase
public import CFSG.Monster.B.TwoA.Unitary.Twenty

public section

open CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.GSide CFSG.KLie.CT CFSG.KC.QForm
  CFSG.KC.U6Orb CFSG.KC.SortTree CFSG.KC.Bfs CertificateChecks.Orb3132 CertificateChecks.KernelMonB

namespace CertificateChecks.Batch3132

open CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.GSide CFSG.KLie.CT CFSG.KC.QForm
  CFSG.KC.U6Orb CFSG.KC.SortTree CFSG.KC.Bfs CertificateChecks.Orb3132 CertificateChecks.KernelMonB

set_option maxRecDepth 100000

theorem nrows : Unitary.n6RowArr.size = 17 := Nat.eq_of_beq_eq_true kSize

theorem mat_eq {k : ℕ} (hk : k < 17) : mat k = packL 22 Unitary.n6RowArr[k]!.toList := by
  have hM := Nat.eq_of_beq_eq_true kMat
  change fget MM k 484 = _
  rw [hM]
  exact packR_get kRow (by rw [nrows]; exact hk)

theorem genAct_eq {k : ℕ} (hk : k < 17) (v : ℕ) : Unitary.genAct k v = actK (mat k) v := by
  have hmem : Unitary.n6RowArr[k]! ∈ Unitary.n6RowArr.toList := by
    rw [getElem!_toList _ (by rw [nrows]; exact hk)]
    exact List.getElem_mem _
  have hrow := (shapeL_iff _ _ _).1 kRow _ hmem
  rw [mat_eq hk]
  exact actD_eq_actK hrow.1 (fun x hx => by have := hrow.2 x hx; rwa [pw2_eq] at this) v

theorem gen_lt {k : ℕ} (hk : k < 17) (v : ℕ) : Unitary.genAct k v < 2 ^ 22 := by
  rw [genAct_eq hk]
  exact actK_lt _ _

theorem act_eq {k : ℕ} (hk : k < 17) {v : ℕ} (hv : v < 2 ^ 22) :
    Orb3132.act k v = Unitary.genAct k v := by
  rw [genAct_eq hk]
  exact actB_eq kTab hk hv

theorem inv_k {k : ℕ} (hk : k < 17) :
    (∀ x < 2 ^ 22, ∀ y < 2 ^ 22, bK U (actK (mat k) x) (actK (mat k) y) = bK U x y) ∧
      ∀ x < 2 ^ 22, qK U (actK (mat k) x) = qK U x :=
  invK_sound ((CFSG.KC.U6Orb.allN_iff _ _).1 kInv k hk)

theorem bK_gen {k : ℕ} (hk : k < 17) {x y : ℕ} (hx : x < 2 ^ 22) (hy : y < 2 ^ 22) :
    bK U (Unitary.genAct k x) (Unitary.genAct k y) = bK U x y := by
  rw [genAct_eq hk, genAct_eq hk]
  exact (inv_k hk).1 x hx y hy

theorem qK_gen {k : ℕ} (hk : k < 17) {x : ℕ} (hx : x < 2 ^ 22) :
    qK U (Unitary.genAct k x) = qK U x := by
  rw [genAct_eq hk]
  exact (inv_k hk).2 x hx

theorem sig_fix {k : ℕ} (hk : k < 17) : Unitary.genAct k 6144 = 6144 := by
  rw [genAct_eq hk]
  exact Nat.eq_of_beq_eq_true ((CFSG.KC.U6Orb.allN_iff _ _).1 kSig k hk)

theorem bK_sig_gen {k : ℕ} (hk : k < 17) {x : ℕ} (hx : x < 2 ^ 22) :
    bK U 6144 (Unitary.genAct k x) = bK U 6144 x := by
  have := bK_gen hk (by decide : 6144 < 2 ^ 22) hx
  rwa [sig_fix hk] at this

theorem form : qK U 6144 = 0 ∧ bK U 6144 32 = 1 ∧
    (repOK 60 = true ∧ repOK 39 = true ∧ repOK 35 = true ∧ repOK 32 = true) := by
  have h := kForm
  simp only [andB_eq_true] at h
  exact ⟨Nat.eq_of_beq_eq_true h.1, Nat.eq_of_beq_eq_true h.2.1, h.2.2⟩

noncomputable def V : Finset ℕ :=
  (Finset.range (2 ^ 22)).filter fun v => bK U 6144 v = 1 ∧ qK U v = 0

theorem card_V : V.card = 2 ^ 20 := card_singular (by decide) (by decide) form.1 form.2.1

theorem mem_V {v : ℕ} : v ∈ V ↔ v < 2 ^ 22 ∧ bK U 6144 v = 1 ∧ qK U v = 0 := by
  simp [V]

theorem rep_V {r : ℕ} (hr : r < 2 ^ 22) (h : repOK r = true) : r ∈ V := by
  rw [repOK, andB_eq_true] at h
  exact mem_V.2 ⟨hr, Nat.eq_of_beq_eq_true h.1, Nat.eq_of_beq_eq_true h.2⟩

theorem gen_V {k : ℕ} (hk : k < 17) {v : ℕ} (hv : v ∈ V) : Unitary.genAct k v ∈ V := by
  obtain ⟨h1, h2, h3⟩ := mem_V.1 hv
  exact mem_V.2 ⟨gen_lt hk v, (bK_sig_gen hk h1).trans h2, (qK_gen hk h1).trans h3⟩

theorem sumN_card (n : ℕ) (p : ℕ → Bool) :
    sumN n (fun j => Bool.rec (motive := fun _ => ℕ) 0 1 (p j)) =
      ((Finset.range n).filter fun j => p j = true).card := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change Bool.rec (motive := fun _ => ℕ) 0 1 (p n) + sumN n _ = _
    rw [ih, Finset.range_add_one, Finset.filter_insert]
    cases h : p n
    · simp
    · rw [ite_eq_left_of_eq_true _ _ (eq_true rfl), Finset.card_insert_of_notMem (by simp)]
      change 1 + _ = _
      omega

theorem card_reindex {n : ℕ} {π ρ : ℕ → ℕ} (hπ : ∀ j < n, π j < n)
    (hρ : ∀ j < n, ρ (π j) = j) (Q : ℕ → Prop) [DecidablePred Q] :
    ((Finset.range n).filter fun j => Q (π j)).card = ((Finset.range n).filter Q).card := by
  have hinj : ∀ a < n, ∀ b < n, π a = π b → a = b := fun a ha b hb e => by
    rw [← hρ a ha, ← hρ b hb, e]
  have hsurj : ∀ b < n, ∃ a < n, π a = b := by
    intro b hb
    have := Finset.surj_on_of_inj_on_of_card_le (s := Finset.range n) (t := Finset.range n)
      (fun a _ => π a) (fun a ha => Finset.mem_range.2 (hπ a (Finset.mem_range.1 ha)))
      (fun a₁ a₂ h₁ h₂ e => hinj a₁ (Finset.mem_range.1 h₁) a₂ (Finset.mem_range.1 h₂) e)
      le_rfl b (Finset.mem_range.2 hb)
    obtain ⟨a, ha, e⟩ := this
    exact ⟨a, Finset.mem_range.1 ha, e.symm⟩
  refine Finset.card_bij (fun j _ => π j) (fun j hj => ?_) (fun a ha b hb e => ?_)
    (fun b hb => ?_)
  · rw [Finset.mem_filter, Finset.mem_range] at hj ⊢
    exact ⟨hπ j hj.1, hj.2⟩
  · rw [Finset.mem_filter, Finset.mem_range] at ha hb
    exact hinj a ha.1 b hb.1 e
  · rw [Finset.mem_filter, Finset.mem_range] at hb
    obtain ⟨a, ha, rfl⟩ := hsurj b hb.1
    exact ⟨a, Finset.mem_filter.2 ⟨Finset.mem_range.2 ha, hb.2⟩, rfl⟩

theorem fK_eq (v : ℕ) : fK v = ((Finset.range 2300).filter fun j => fP v j = true).card :=
  sumN_card 2300 (fP v)

theorem om_spec : (∀ j < 2300, om j < 2 ^ 22) ∧ ∀ k < 17, ∀ j < 2300, pi k j < 2300 ∧
    rho k (pi k j) = j ∧ Orb3132.act k (om j) = om (pi k j) := by
  have h := kOm
  rw [andB_eq_true, CFSG.KC.U6Orb.allN_iff, CFSG.KC.U6Orb.allN_iff] at h
  refine ⟨fun j hj => ?_, fun k hk j hj => ?_⟩
  · have := blt_iff.1 (h.1 j hj)
    rwa [pw2_eq] at this
  · have := h.2 k hk
    rw [CFSG.KC.U6Orb.allN_iff] at this
    have h' := this j hj
    rw [andB_eq_true, andB_eq_true] at h'
    exact ⟨blt_iff.1 h'.1, Nat.eq_of_beq_eq_true h'.2.1, Nat.eq_of_beq_eq_true h'.2.2⟩

theorem fK_gen {k : ℕ} (hk : k < 17) {v : ℕ} (hv : v < 2 ^ 22) :
    fK (Unitary.genAct k v) = fK v := by
  obtain ⟨hlt, hp⟩ := om_spec
  rw [fK_eq, fK_eq, ← card_reindex (π := pi k) (ρ := rho k) (fun j hj => (hp k hk j hj).1)
    (fun j hj => (hp k hk j hj).2.1)]
  refine congrArg Finset.card (Finset.filter_congr fun j hj => ?_)
  have hj := Finset.mem_range.1 hj
  unfold fP
  rw [← (hp k hk j hj).2.2, act_eq hk (hlt j hj), bK_gen hk hv (hlt j hj),
    bK_sig_gen hk (hlt j hj)]

theorem fvals : fK 60 = 324 ∧ fK 39 = 420 ∧ fK 35 = 452 ∧ fK 32 = 484 := by
  have h := kF
  simp only [andB_eq_true] at h
  exact ⟨Nat.eq_of_beq_eq_true h.1, Nat.eq_of_beq_eq_true h.2.1, Nat.eq_of_beq_eq_true h.2.2.1,
    Nat.eq_of_beq_eq_true h.2.2.2⟩

theorem reach_props {r : ℕ} (hr : r ∈ V) {x : ℕ} (h : Reach Unitary.genAct 17 r x) :
    x ∈ V ∧ fK x = fK r :=
  reach_inv (P := fun x => x ∈ V ∧ fK x = fK r) ⟨hr, rfl⟩
    (fun _ hk _ hx => ⟨gen_V hk hx.1, (fK_gen hk (mem_V.1 hx.1).1).trans hx.2⟩) h

noncomputable def O (r : ℕ) : Finset ℕ := by
  classical exact V.filter fun x => Reach Unitary.genAct 17 r x

theorem mem_O {r x : ℕ} : x ∈ O r ↔ x ∈ V ∧ Reach Unitary.genAct 17 r x := by
  classical
  unfold O
  rw [Finset.mem_filter]

noncomputable def T (rec : ℕ → ℕ) (n : ℕ) : Finset ℕ :=
  (Finset.range n).image fun i => valF 22 (rec i)

theorem tree_O {r n wl wp C : ℕ} {rec : ℕ → ℕ} (hr : r ∈ V)
    (hT : treeOK Orb3132.act 17 (fun _ => true) r rec n 22 wl wp 2048 C = true) :
    T rec n ⊆ O r ∧ (T rec n).card = n ∧ ∀ x ∈ T rec n, valF 22 (rec 0) ≤ x := by
  obtain ⟨h1, -, h2, -⟩ := tree_sound hT
  have hr22 := (mem_V.1 hr).1
  have hreach : ∀ i < n, Reach Unitary.genAct 17 r (valF 22 (rec i)) := fun i hi =>
    (reach_congr (P := fun x => x < 2 ^ 22) hr22 (fun k hk x _ => gen_lt hk x)
      (fun k hk x hx => act_eq hk hx)).1 (h1 i hi)
  refine ⟨fun x hx => ?_, ?_, fun x hx => ?_⟩
  · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hx
    have hi' := Finset.mem_range.1 hi
    exact mem_O.2 ⟨(reach_props hr (hreach i hi')).1, hreach i hi'⟩
  · rw [T, Finset.card_image_of_injOn, Finset.card_range]
    intro a ha b hb e
    simp only [Finset.coe_range, Set.mem_Iio] at ha hb
    rcases lt_trichotomy a b with hab | rfl | hab
    · exact absurd e (ne_of_lt (h2 a b hab hb))
    · rfl
    · exact absurd e (ne_of_gt (h2 b a hab ha))
  · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hx
    rcases Nat.eq_zero_or_pos i with rfl | h
    · exact le_rfl
    · exact le_of_lt (h2 0 i h (Finset.mem_range.1 hi))

theorem O_disj {r r' : ℕ} (hr : r ∈ V) (hr' : r' ∈ V) (hf : fK r ≠ fK r') : Disjoint (O r) (O r') :=
  Finset.disjoint_left.2 fun _ h h' => hf <| (reach_props hr (mem_O.1 h).2).2.symm.trans
    (reach_props hr' (mem_O.1 h').2).2

theorem O_sub (r : ℕ) : O r ⊆ V := fun _ hx => (mem_O.1 hx).1

theorem cover {A B C D TA TB TC TD : Finset ℕ} (hA : A ⊆ V) (hB : B ⊆ V) (hC : C ⊆ V) (hD : D ⊆ V)
    (dAB : Disjoint A B) (dAC : Disjoint A C) (dAD : Disjoint A D) (dBC : Disjoint B C)
    (dBD : Disjoint B D) (dCD : Disjoint C D) (tA : TA ⊆ A) (tB : TB ⊆ B) (tC : TC ⊆ C)
    (tD : TD ⊆ D) (hsum : TA.card + TB.card + TC.card + TD.card = V.card) :
    A = TA ∧ B = TB ∧ C = TC ∧ D = TD := by
  have h1 := Finset.card_union_of_disjoint dAB
  have h2 := Finset.card_union_of_disjoint (Finset.disjoint_union_left.2 ⟨dAC, dBC⟩)
  have h3 := Finset.card_union_of_disjoint
    (Finset.disjoint_union_left.2 ⟨Finset.disjoint_union_left.2 ⟨dAD, dBD⟩, dCD⟩)
  have hle := Finset.card_le_card (Finset.union_subset (Finset.union_subset
    (Finset.union_subset hA hB) hC) hD)
  have cA := Finset.card_le_card tA
  have cB := Finset.card_le_card tB
  have cC := Finset.card_le_card tC
  have cD := Finset.card_le_card tD
  refine ⟨(Finset.eq_of_subset_of_card_le tA ?_).symm, (Finset.eq_of_subset_of_card_le tB ?_).symm,
    (Finset.eq_of_subset_of_card_le tC ?_).symm, (Finset.eq_of_subset_of_card_le tD ?_).symm⟩ <;>
    omega

theorem orbits : O 39 = T rec39 228096 ∧ O 35 = T rec35 798336 ∧ O 32 = T rec32 20736 ∧
    (∀ x ∈ T rec39 228096, 39 ≤ x) ∧ (∀ x ∈ T rec35 798336, 35 ≤ x) ∧
    (∀ x ∈ T rec32 20736, 32 ≤ x) := by
  obtain ⟨-, -, r60, r39, r35, r32⟩ := form
  have v60 := rep_V (by decide) r60
  have v39 := rep_V (by decide) r39
  have v35 := rep_V (by decide) r35
  have v32 := rep_V (by decide) r32
  obtain ⟨f60, f39, f35, f32⟩ := fvals
  obtain ⟨t60, c60, -⟩ := tree_O v60 tree60
  obtain ⟨t39, c39, m39⟩ := tree_O v39 tree39
  obtain ⟨t35, c35, m35⟩ := tree_O v35 tree35
  obtain ⟨t32, c32, m32⟩ := tree_O v32 tree32
  have h := kRoots
  simp only [andB_eq_true] at h
  have e39 := Nat.eq_of_beq_eq_true h.2.1
  have e35 := Nat.eq_of_beq_eq_true h.2.2.1
  have e32 := Nat.eq_of_beq_eq_true h.2.2.2
  obtain ⟨-, a39, a35, a32⟩ := cover (O_sub 60) (O_sub 39) (O_sub 35) (O_sub 32)
    (O_disj v60 v39 (by omega)) (O_disj v60 v35 (by omega)) (O_disj v60 v32 (by omega))
    (O_disj v39 v35 (by omega)) (O_disj v39 v32 (by omega)) (O_disj v35 v32 (by omega))
    t60 t39 t35 t32 (by rw [c60, c39, c35, c32, card_V]; rfl)
  exact ⟨a39, a35, a32, e39 ▸ m39, e35 ▸ m35, e32 ▸ m32⟩

theorem orbitOK_of_O {r n : ℕ} {rec : ℕ → ℕ} (hr : r ∈ V) (hO : O r = T rec n)
    (hc : (T rec n).card = n) (hm : ∀ x ∈ T rec n, r ≤ x) :
    CTIB.Native.orbitOK Unitary.genAct 17 (fun a => decide (a < 2 ^ 22)) r n = true := by
  refine orbitOK_of_reach (O r) (fun x => ⟨fun h => mem_O.2 ⟨(reach_props hr h).1, h⟩,
    fun h => (mem_O.1 h).2⟩) (fun x hx => decide_eq_true (mem_V.1 (O_sub r hx)).1)
    (hO ▸ hc) (fun x hx => hm x (hO ▸ hx))

theorem orbitOK_all :
    CTIB.Native.orbitOK Unitary.genAct 17 (fun a => decide (a < 2 ^ 22)) 39 228096 = true ∧
    CTIB.Native.orbitOK Unitary.genAct 17 (fun a => decide (a < 2 ^ 22)) 35 798336 = true ∧
    CTIB.Native.orbitOK Unitary.genAct 17 (fun a => decide (a < 2 ^ 22)) 32 20736 = true := by
  obtain ⟨-, -, -, r39, r35, r32⟩ := form
  obtain ⟨a39, a35, a32, m39, m35, m32⟩ := orbits
  exact ⟨orbitOK_of_O (rep_V (by decide) r39) a39 (tree_O (rep_V (by decide) r39) tree39).2.1 m39,
    orbitOK_of_O (rep_V (by decide) r35) a35 (tree_O (rep_V (by decide) r35) tree35).2.1 m35,
    orbitOK_of_O (rep_V (by decide) r32) a32 (tree_O (rep_V (by decide) r32) tree32).2.1 m32⟩

theorem pg_eq (X t : ℕ) : CFSG.KC.Enum.pg 24 (CFSG.KS.mask 24) X t = fget X t 24 := by
  change (X >>> (24 * t)) &&& CFSG.KS.mask 24 = (X >>> (t * 24)) &&& maskN 24
  rw [Nat.mul_comm]
  rfl

theorem contains_of {y t : ℕ} (ht : t < 2300) (h : Nat.beq (fget (Co2V.F 0) t 24) y = true) :
    (Co2.Native.vectors ()).contains y = true := by
  rw [← Nat.eq_of_beq_eq_true h, ← pg_eq]
  exact vectors_contains ht

theorem kV0 : Nat.beq (fget (Co2V.F 0) 79 24) 2311997 = true := by quickRfl
theorem kV1 : Nat.beq (fget (Co2V.F 0) 136 24) 3378621 = true := by quickRfl
theorem kV2 : Nat.beq (fget (Co2V.F 0) 803 24) 1100455 = true := by quickRfl
theorem kV3 : Nat.beq (fget (Co2V.F 0) 1 24) 1050624 = true := by quickRfl
theorem kV4 : Nat.beq (fget (Co2V.F 0) 13 24) 2099200 = true := by quickRfl
theorem kV5 : Nat.beq (fget (Co2V.F 0) 88 24) 3145763 = true := by quickRfl
theorem kV6 : Nat.beq (fget (Co2V.F 0) 18 24) 12315 = true := by quickRfl
theorem kV7 : Nat.beq (fget (Co2V.F 0) 331 24) 12347 = true := by quickRfl

theorem vec_checks : Co2.Native.vectors.contains 2311997 = true ∧
    Co2.Native.vectors.contains 3378621 = true ∧ Co2.Native.vectors.contains 1100455 = true ∧
    Co2.Native.vectors.contains 1050624 = true ∧ Co2.Native.vectors.contains 2099200 = true ∧
    Co2.Native.vectors.contains 3145763 = true ∧ Co2.Native.vectors.contains 12315 = true ∧
    Co2.Native.vectors.contains 12347 = true :=
  ⟨contains_of (by decide) kV0, contains_of (by decide) kV1, contains_of (by decide) kV2,
    contains_of (by decide) kV3, contains_of (by decide) kV4, contains_of (by decide) kV5,
    contains_of (by decide) kV6, contains_of (by decide) kV7⟩

theorem bW_sigma_checks : bWcode 6144 39 = 1 ∧ bWcode 6144 35 = 1 ∧ bWcode 6144 32 = 1 := by
  decide +kernel

theorem bW_orth_checks : bWcode 2311997 3378621 = 0 ∧ bWcode 2311997 1100455 = 0 ∧
    bWcode 3378621 1100455 = 0 ∧ bWcode 1050624 2099200 = 0 ∧ bWcode 1050624 3145763 = 0 ∧
    bWcode 2099200 3145763 = 0 ∧ bWcode 12315 12347 = 0 := by
  decide +kernel

end CertificateChecks.Batch3132

namespace Certificates

open CertificateChecks

open CertificateChecks.Batch3132 in
open CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.GSide in
theorem certificate3132 : (CTIB.Native.orbitOK Unitary.genAct 17 (fun a => decide (a < 2 ^ 22)) 39 228096 = true)
    ∧ (CTIB.Native.orbitOK Unitary.genAct 17 (fun a => decide (a < 2 ^ 22)) 35 798336 = true)
    ∧ (CTIB.Native.orbitOK Unitary.genAct 17 (fun a => decide (a < 2 ^ 22)) 32 20736 = true)
    ∧ (Co2.Native.vectors.contains 2311997 = true ∧
       Co2.Native.vectors.contains 3378621 = true ∧ Co2.Native.vectors.contains 1100455 = true ∧
       Co2.Native.vectors.contains 1050624 = true ∧ Co2.Native.vectors.contains 2099200 = true ∧
       Co2.Native.vectors.contains 3145763 = true ∧ Co2.Native.vectors.contains 12315 = true ∧
       Co2.Native.vectors.contains 12347 = true)
    ∧ (bWcode 6144 39 = 1 ∧ bWcode 6144 35 = 1 ∧ bWcode 6144 32 = 1)
    ∧ (bWcode 2311997 3378621 = 0 ∧ bWcode 2311997 1100455 = 0 ∧
       bWcode 3378621 1100455 = 0 ∧ bWcode 1050624 2099200 = 0 ∧ bWcode 1050624 3145763 = 0 ∧
       bWcode 2099200 3145763 = 0 ∧ bWcode 12315 12347 = 0) :=
  ⟨orbitOK_all.1, orbitOK_all.2.1, orbitOK_all.2.2, vec_checks, bW_sigma_checks,
    bW_orth_checks⟩

end Certificates
