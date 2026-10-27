
module

public import CFSG.Monster.B.TwoA.Unitary.OrbitBase
public import CFSG.Monster.B.TwoA.Base.FrameBase
public import CFSG.Monster.B.Classical.ThreePlaneData
public meta import CFSG.Monster.B.TwoA.Census.PermCert
public meta import CFSG.Monster.B.TwoA.Census.PermBFS
public meta import CFSG.Monster.B.TwoA.Unitary.NData
public import CFSG.Monster.B.TwoA.Unitary.WStabInputs
public import Certificates.Data.CFSGNative.MonsterB.Short
public import Certificates.Data.CFSGNative.Mathieu.M24
public import CFSG.Certificates.Kernel.AxisPlane.Orbit
public import Certificates.Data.Kernel.VisFrame.Gens
public import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public import Certificates.Data.CFSGNative.MonsterB.Co2Matrix
public import CFSG.Monster.B.TwoA.Unitary.Bridge
public import CFSG.Monster.B.TwoA.Unitary.ActionInputs

@[expose] public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Unitary

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Lifts CFSG.Monster.Visible
  CFSG.Monster.VisQuot CFSG.Monster.VisCert CFSG.Monster.ScalarKernel CFSG.Monster.SpinLattice
  CFSG.Monster.B.Short CFSG.Monster.B.Co2 CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Census

@[expose] def C012 : Submodule (ZMod 2) (Fin 24 → ZMod 2) := Ceq ⊓ coordEq 0 2

theorem mem_C012 {x : Fin 24 → ZMod 2} : x ∈ C012 ↔ x ∈ C ∧ x 0 = x 1 ∧ x 0 = x 2 := by
  rw [C012, Submodule.mem_inf, mem_Ceq, mem_coordEq, and_assoc]

@[expose] def P2 : Subgroup AutPerm := Ppair ⊓ MulAction.stabilizer AutPerm (2 : Fin 24)

theorem mem_P2 {p : AutPerm} : p ∈ P2 ↔ p ∈ Ppair ∧ (p : Equiv.Perm (Fin 24)) 2 = 2 := by
  rw [P2, Subgroup.mem_inf, MulAction.mem_stabilizer_iff]
  rfl

theorem P2_le_Ppair : P2 ≤ Ppair := inf_le_left

theorem c012Hyp : MonoHyp C012 P2 where
  le_C := fun x hx => (mem_C012.1 hx).1
  Ω_mem := mem_C012.2 ⟨Ω_mem_C, rfl, rfl⟩
  preserves p hp a ha := by
    rw [mem_C012] at ha ⊢
    refine ⟨permWord_mem_of_mem_AutPerm p.2 ha.1, ?_, ?_⟩
    · have h := ceqHyp.preserves p (P2_le_Ppair hp) a (mem_Ceq.2 ⟨ha.1, ha.2.1⟩)
      exact (mem_Ceq.1 h).2
    · rw [permWord_apply', permWord_apply']
      have hp' := P2.inv_mem hp
      have h2 : ((p⁻¹ : AutPerm) : Equiv.Perm (Fin 24)) 2 = 2 := (mem_P2.1 hp').2
      rw [← coe_inv_autPerm, h2]
      rcases (mem_Ppair_iff p⁻¹).1 (mem_P2.1 hp').1 with ⟨h0, -⟩ | ⟨h0, -⟩
      · rw [h0]; exact ha.2.2
      · rw [h0, ← ha.2.1]; exact ha.2.2

theorem sigmaCls_add_v0 : sigmaCls + v0 = pairCls 1 2 0 := by
  rw [sigmaCls_eq_dec, ← vShort_eq_v0, vShort, ← dec_xor,
    cls_pairN_eq (by decide) (pairN_eq 1 2 (by decide)) (r := 20480 ^^^ 12288) (by decide +kernel)]

theorem mk_eq_sigmaW_iff
    (x : vPerpL v0) :
    (Submodule.Quotient.mk x : Wv v0) = sigmaW ↔
      (x : L2) = sigmaCls ∨ (x : L2) = pairCls 1 2 0 := by
  rw [sigmaW, Submodule.Quotient.eq]
  change (x : L2) - sigmaCls ∈ vLineL v0 ↔ _
  rw [mem_vLineL, sub_eq_zero, sub_eq_iff_eq_add, add_comm, sigmaCls_add_v0]

theorem zmod_add_eq_zero_iff : ∀ s t : ZMod 2, s + t = 0 ↔ s = t := by decide

theorem monomial_fix_sigma_iff
    {a : C} {p : AutPerm}
    (hk : (QuotientGroup.mk (gO a * PO p) : OLq) ∈ Kstab v0) :
    wAct v0 ⟨_, hk⟩ sigmaW = sigmaW ↔
      (p : Equiv.Perm (Fin 24)) 2 = 2 ∧ (a : Fin 24 → ZMod 2) 0 = (a : Fin 24 → ZMod 2) 2 := by
  have hp := ((mk_mem_Kstab_iff_monomial a p).1 hk).1
  have e : wAct v0 ⟨_, hk⟩ sigmaW = Submodule.Quotient.mk
      ⟨kOp (QuotientGroup.mk (gO a * PO p)) sigmaCls, kOp_mem_vPerpL hk sigmaCls_mem⟩ := rfl
  rw [e, mk_eq_sigmaW_iff]
  change kOp _ sigmaCls = sigmaCls ∨ kOp _ sigmaCls = pairCls 1 2 0 ↔ _
  rw [kOp_mk, modTwoEnd_gO_mul_PO_pairCls a p (by decide),
    pairCls_eq_iff ((p : Equiv.Perm (Fin 24)).injective.ne (by decide)) (by decide),
    pairCls_eq_iff ((p : Equiv.Perm (Fin 24)).injective.ne (by decide)) (by decide), zero_add,
    zmod_add_eq_zero_iff]
  rcases (mem_Ppair_iff p).1 hp with ⟨h0, -⟩ | ⟨h0, -⟩ <;> rw [h0] <;>
    constructor <;> intro h
  · rcases h with ⟨⟨-, h2⟩ | ⟨h2, -⟩, ha⟩ | ⟨⟨h2, -⟩ | ⟨h2, -⟩, -⟩
    · exact ⟨h2, ha⟩
    · exact absurd h2 (by decide)
    · exact absurd h2 (by decide)
    · exact absurd h2 (by decide)
  · exact .inl ⟨.inl ⟨rfl, h.1⟩, h.2⟩
  · rcases h with ⟨⟨h2, -⟩ | ⟨h2, -⟩, -⟩ | ⟨⟨-, h2⟩ | ⟨h2, -⟩, ha⟩
    · exact absurd h2 (by decide)
    · exact absurd h2 (by decide)
    · exact ⟨h2, ha⟩
    · exact absurd h2 (by decide)
  · exact .inr ⟨.inl ⟨rfl, h.1⟩, h.2⟩

@[expose] def UsigW :
    Subgroup (Kstab v0) := Usig ⊓ Mfr

theorem monoSub_c012_le_ceq : monoSub c012Hyp ≤ monoSub ceqHyp :=
  monoSub_mono c012Hyp ceqHyp (fun _ hx => mem_Ceq.2 ⟨(mem_C012.1 hx).1, (mem_C012.1 hx).2.1⟩)
    P2_le_Ppair

theorem monoSub_c012_le_Kstab :
    monoSub c012Hyp ≤ Kstab v0 :=
  monoSub_c012_le_ceq.trans monoSub_ceq_le_Kstab

theorem mem_UsigW_iff
    (k : Kstab v0) : k ∈ UsigW ↔ (k : OLq) ∈ monoSub c012Hyp := by
  rw [UsigW, Subgroup.mem_inf, mem_Mfr_iff]
  constructor
  · rintro ⟨hs, hm⟩
    obtain ⟨a, ha, p, hp, hk⟩ := (mem_monoSub_iff ceqHyp).1 hm
    have hk' : (QuotientGroup.mk (gO a * PO p) : OLq) ∈ Kstab v0 := hk ▸ k.2
    have e : k = ⟨_, hk'⟩ := Subtype.ext hk
    rw [e, mem_Usig, monomial_fix_sigma_iff] at hs
    rw [hk]
    exact mk_mem_monoSub c012Hyp (mem_C012.2 ⟨a.2, (mem_Ceq.1 ha).2, hs.2⟩)
      (mem_P2.2 ⟨hp, hs.1⟩)
  · intro hm
    refine ⟨?_, monoSub_c012_le_ceq hm⟩
    obtain ⟨a, ha, p, hp, hk⟩ := (mem_monoSub_iff c012Hyp).1 hm
    have hk' : (QuotientGroup.mk (gO a * PO p) : OLq) ∈ Kstab v0 := hk ▸ k.2
    have e : k = ⟨_, hk'⟩ := Subtype.ext hk
    rw [e, mem_Usig, monomial_fix_sigma_iff]
    exact ⟨(mem_P2.1 hp).2, (mem_C012.1 ha).2.2⟩

theorem map_UsigW :
    UsigW.map (Kstab v0).subtype = monoSub c012Hyp := by
  ext x
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact (mem_UsigW_iff k).1 hk
  · intro hx
    exact ⟨⟨x, monoSub_c012_le_Kstab hx⟩, (mem_UsigW_iff _).2 hx, rfl⟩

@[expose] def usigWEquivMono :
    UsigW ≃* monoSub c012Hyp :=
  (UsigW.equivMapOfInjective (Kstab v0).subtype Subtype.val_injective).trans
    (MulEquiv.subgroupCongr map_UsigW)

@[expose] def UsigWEquiv :
    SDD c012Hyp ≃* UsigW :=
  (monoSubEquiv c012Hyp).trans usigWEquivMono.symm

theorem coe_UsigWEquiv
    (x : SDD c012Hyp) :
    ((UsigWEquiv x : Kstab v0) : OLq) = monoD c012Hyp x := by
  have h : (usigWEquivMono (UsigWEquiv x) : OLq) = ((UsigWEquiv x : Kstab v0) : OLq) := rfl
  rw [UsigWEquiv, MulEquiv.trans_apply, MulEquiv.apply_symm_apply] at h
  exact h.symm

@[expose] def c012Form : Ceq →ₗ[ZMod 2] ZMod 2 :=
  ((LinearMap.proj 0 : (Fin 24 → ZMod 2) →ₗ[ZMod 2] ZMod 2) - LinearMap.proj 2).comp Ceq.subtype

theorem B6_mem_Ceq : B 6 ∈ Ceq := mem_Ceq.2 ⟨B_mem_C 6, by decide⟩

theorem c012Form_surjective : Function.Surjective c012Form := by
  intro t
  refine ⟨t • ⟨B 6, B6_mem_Ceq⟩, ?_⟩
  rw [map_smul]
  have h : c012Form ⟨B 6, B6_mem_Ceq⟩ = B 6 0 - B 6 2 := rfl
  rw [h, show B 6 0 - B 6 2 = 1 by decide, smul_eq_mul, mul_one]

theorem comap_C012 : C012.comap Ceq.subtype = LinearMap.ker c012Form := by
  ext c
  simp only [Submodule.mem_comap, Submodule.subtype_apply, LinearMap.mem_ker, c012Form,
    LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.proj_apply, sub_eq_zero, C012,
    Submodule.mem_inf, mem_coordEq]
  exact ⟨fun h => h.2, fun h => ⟨c.2, h⟩⟩

theorem finrank_C012 : Module.finrank (ZMod 2) C012 = 10 := by
  have h := LinearMap.finrank_range_add_finrank_ker c012Form
  rw [LinearMap.range_eq_top.2 c012Form_surjective, finrank_top, Module.finrank_self,
    finrank_Ceq, ← comap_C012] at h
  have e := (Submodule.comapSubtypeEquivOfLe (p := C012) (q := Ceq) inf_le_left).finrank_eq
  omega

theorem natCard_C012_quot : Nat.card (C012 ⧸ ΩIn C012) = 2 ^ 9 := by
  rw [natCard_quot_ΩIn c012Hyp, finrank_C012]

attribute [local instance] restAction

@[expose] def rest2 : Rest := ⟨2, by decide, by decide⟩

instance isPretransitive_rest :
    MulAction.IsPretransitive Ppair Rest :=
  @MulAction.isPretransitive_of_is_two_pretransitive _ _ _ _ isMultiplyPretransitive_rest

theorem natCard_stabilizer_rest2 :
    Nat.card (MulAction.stabilizer Ppair rest2) = 40320 := by
  have h1 := Subgroup.index_mul_card (MulAction.stabilizer Ppair rest2)
  rw [MulAction.index_stabilizer_of_transitive, natCard_rest, natCard_Ppair] at h1
  omega

theorem map_stabilizer_rest2 : (MulAction.stabilizer Ppair rest2).map Ppair.subtype = P2 := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact mem_P2.2 ⟨q.2, congrArg Subtype.val hq⟩
  · intro hp
    exact ⟨⟨p, (mem_P2.1 hp).1⟩, Subtype.ext (mem_P2.1 hp).2, rfl⟩

theorem natCard_P2 : Nat.card P2 = 40320 := by
  rw [← map_stabilizer_rest2, ← Nat.card_congr ((MulAction.stabilizer Ppair
    rest2).equivMapOfInjective Ppair.subtype Subtype.val_injective).toEquiv,
    natCard_stabilizer_rest2]

theorem natCard_UsigW :
    Nat.card UsigW = 20643840 := by
  rw [← Nat.card_congr UsigWEquiv.toEquiv, SemidirectProduct.card]
  change Nat.card (C012 ⧸ ΩIn C012) * Nat.card P2 = 20643840
  rw [natCard_C012_quot, natCard_P2]
  norm_num

theorem permGens_perm : ∀ k < permGens.size, PermArr permGens[k]! = true := by decide +kernel

theorem permGens_size : permGens.size = 6 := rfl

theorem n6Aut_fix : ∀ k : Fin 6, (n6PermArr[(k : ℕ)]!)[2]! = 2 ∧ (n6PermArr[(k : ℕ)]!)[0]! < 2 ∧
    (n6PermArr[(k : ℕ)]!)[1]! < 2 := by decide +kernel

theorem n6Aut_mem_P2 (k : Fin 6) : n6Aut k ∈ P2 := by
  obtain ⟨h2, h0, h1⟩ := n6Aut_fix k
  have e2 := n6Aut_apply k 2
  have e0 := n6Aut_apply k 0
  have e1 := n6Aut_apply k 1
  refine mem_P2.2 ⟨(mem_Ppair_iff _).2 ?_, Fin.ext (by rw [e2]; exact h2)⟩
  have hne : ((n6Aut k : Equiv.Perm (Fin 24)) 0) ≠ ((n6Aut k : Equiv.Perm (Fin 24)) 1) :=
    (n6Aut k : Equiv.Perm (Fin 24)).injective.ne (by decide)
  have h0' : ((n6Aut k : Equiv.Perm (Fin 24)) 0 : ℕ) < 2 := by rw [e0]; exact h0
  have h1' : ((n6Aut k : Equiv.Perm (Fin 24)) 1 : ℕ) < 2 := by rw [e1]; exact h1
  rcases Nat.lt_succ_iff_lt_or_eq.1 h0' with h0'' | h0'' <;>
    rcases Nat.lt_succ_iff_lt_or_eq.1 h1' with h1'' | h1''
  · exact absurd (Fin.ext (by omega)) hne
  · exact .inl ⟨Fin.ext (by omega), Fin.ext h1''⟩
  · exact .inr ⟨Fin.ext h0'', Fin.ext (by omega)⟩
  · exact absurd (Fin.ext (h0''.trans h1''.symm)) hne

@[expose] def bCN (j : ℕ) : C := if h : j < 12 then bC ⟨j, h⟩ else 0

@[expose] def frameCode : List ℤ → C
  | [] => 0
  | l :: w => bCN (l.toNat - 3) + frameCode w

theorem frameQ_sign {j : ℕ} (h3 : 3 ≤ j) (h15 : j < 15) :
    frameQ j = QuotientGroup.mk (gO (bCN (j - 3))) := by
  rw [frameQ, dite_eq_left h15, frameGen, ite_eq_right (by simp; omega),
    ite_eq_right (by simp; omega), ite_eq_right (by simp; omega), bCN, dite_eq_left (by omega)]

theorem frameWordQ_sign : ∀ w : List ℤ, (∀ l ∈ w, 3 ≤ l.toNat ∧ l.toNat < 15) →
    frameWordQ w = QuotientGroup.mk (gO (frameCode w))
  | [], _ => by rw [frameWordQ, frameCode, gO_zero, QuotientGroup.mk_one]
  | l :: w, hw => by
    have hl := hw l List.mem_cons_self
    rw [frameWordQ, frameWordQ_sign w (fun l' h => hw l' (List.mem_cons_of_mem _ h)),
      frameQ_sign hl.1 hl.2, frameCode, gO_add, QuotientGroup.mk_mul]

@[expose] def wordSignCode : List ℕ → C
  | [] => 0
  | a :: w => frameCode (Native.genRecords[a]!).word + wordSignCode w

@[expose] def signRecOK (a : ℕ) : Bool :=
  decide (a < 24) && (Native.genRecords[a]!).kind == .codeSign &&
    (Native.genRecords[a]!).word.all fun l => decide (3 ≤ l.toNat ∧ l.toNat < 15)

theorem alphaN_sign {a : ℕ} (h : signRecOK a = true) :
    alphaN a = QuotientGroup.mk (gO (frameCode (Native.genRecords[a]!).word)) := by
  simp only [signRecOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨ha, hk⟩, hw⟩ := h
  rw [alphaN, dite_eq_left ha, ← frameWordQ_sign _ hw]
  have hk' : (genRecord ⟨a, ha⟩).kind = .codeSign := hk
  unfold alpha
  rw [hk']
  rfl

theorem alphaWordL_sign : ∀ w : List ℕ, (∀ a ∈ w, signRecOK a = true) →
    alphaWordL w = QuotientGroup.mk (gO (wordSignCode w))
  | [], _ => by rw [alphaWordL, wordSignCode, gO_zero, QuotientGroup.mk_one]
  | a :: w, hw => by
    rw [alphaWordL, alphaN_sign (hw a List.mem_cons_self),
      alphaWordL_sign w (fun b h => hw b (List.mem_cons_of_mem _ h)), wordSignCode, gO_add,
      QuotientGroup.mk_mul]

theorem signWords_ok : ∀ i < 10, ∀ a ∈ n6WordArr[i]!, signRecOK a = true := by decide +kernel

@[expose] def signVec (i : Fin 10) : Fin 24 → ZMod 2 := (wordSignCode n6WordArr[(i : ℕ)]! : _)

theorem n6Elt_sign (i : Fin 10) :
    n6Elt ⟨6 + i, by omega⟩ = QuotientGroup.mk (gO (wordSignCode n6WordArr[(i : ℕ)]!)) := by
  rw [n6Elt_of_ge (show ¬(6 + (i : ℕ)) < 6 by omega), show 6 + (i : ℕ) - 6 = i by omega]
  exact alphaWordL_sign _ (signWords_ok i i.2)

@[expose] def signMask : Fin 10 → ℕ :=
  ![255, 3855, 61455, 983055, 15728655, 14381336, 6996160, 13017248, 13421568, 11184640]

theorem signVec_eq : ∀ i : Fin 10, signVec i = bvec 24 (signMask i) := by decide +kernel

@[expose] def signDual : Fin 10 → ℕ := ![25, 265, 4105, 65545, 69905, 9, 89, 57, 1289, 777]

theorem signDual_check : ∀ i j : Fin 10,
    bvec 24 (signDual j) ⬝ᵥ bvec 24 (signMask i) = if i = j then 1 else 0 := by decide +kernel

theorem signVec_mem : ∀ i : Fin 10, signVec i ∈ C012 := by
  intro i
  refine mem_C012.2 ⟨(wordSignCode n6WordArr[(i : ℕ)]!).2, ?_⟩
  rw [signVec_eq]
  revert i
  decide +kernel

theorem linearIndependent_signVec : LinearIndependent (ZMod 2) signVec := by
  rw [Fintype.linearIndependent_iff]
  intro g hg j
  have h := congrArg (fun x => bvec 24 (signDual j) ⬝ᵥ x) hg
  simp only [dotProduct_sum, dotProduct_smul, signVec_eq, signDual_check, smul_eq_mul, mul_ite,
    mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true, dotProduct_zero] at h
  exact h

theorem span_signVec : Submodule.span (ZMod 2) (Set.range signVec) = C012 := by
  refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact signVec_mem i
  · rw [finrank_span_eq_card linearIndependent_signVec, Fintype.card_fin, finrank_C012]

theorem mk_gO_mem_H6 {a : C} (ha : (a : Fin 24 → ZMod 2) ∈ C012) :
    (QuotientGroup.mk (gO a) : OLq) ∈ H6 := by
  have key : ∀ x ∈ Submodule.span (ZMod 2) (Set.range signVec),
      ∃ h : x ∈ C, (QuotientGroup.mk (gO ⟨x, h⟩) : OLq) ∈ H6 := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      refine ⟨(wordSignCode n6WordArr[(i : ℕ)]!).2, ?_⟩
      have e := n6Elt_sign i
      have e' : (⟨signVec i, (wordSignCode n6WordArr[(i : ℕ)]!).2⟩ : C) =
          wordSignCode n6WordArr[(i : ℕ)]! := rfl
      rw [e', ← e]
      exact Subgroup.subset_closure ⟨_, rfl⟩
    | zero =>
      refine ⟨zero_mem _, ?_⟩
      have e : (⟨0, zero_mem C⟩ : C) = 0 := rfl
      rw [e, gO_zero, QuotientGroup.mk_one]
      exact one_mem _
    | add x y _ _ hx hy =>
      obtain ⟨hx', hx''⟩ := hx
      obtain ⟨hy', hy''⟩ := hy
      refine ⟨add_mem hx' hy', ?_⟩
      have e : (⟨x + y, add_mem hx' hy'⟩ : C) = ⟨x, hx'⟩ + ⟨y, hy'⟩ := rfl
      rw [e, gO_add, QuotientGroup.mk_mul]
      exact mul_mem hx'' hy''
    | smul c x _ hx =>
      obtain ⟨hx', hx''⟩ := hx
      refine ⟨C.smul_mem c hx', ?_⟩
      rcases zmod2_cases' c with rfl | rfl
      · have e : (⟨(0 : ZMod 2) • x, C.smul_mem 0 hx'⟩ : C) = 0 := Subtype.ext (zero_smul _ x)
        rw [e, gO_zero, QuotientGroup.mk_one]
        exact one_mem _
      · have e : (⟨(1 : ZMod 2) • x, C.smul_mem 1 hx'⟩ : C) = ⟨x, hx'⟩ :=
          Subtype.ext (one_smul _ x)
        rw [e]
        exact hx''
  rw [← span_signVec] at ha
  obtain ⟨h, hm⟩ := key _ ha
  exact hm

@[expose] def permQ : AutPerm →* OLq := (QuotientGroup.mk' _).comp permOHom

end CFSG.Monster.B.TwoA.Unitary
