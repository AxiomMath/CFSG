module

public import CFSG.LocalAnalysis.WeakClosure81.W183FinSp44G45Rad
public import CFSG.LocalAnalysis.WeakClosure81.W183B2Fin

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Sp44

open CFSG.GH74.KGroups CFSG.Quasithin CFSG.Open Subgroup
open CFSG.QuasithinUnique.Setup.X7b
open CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain
  (antiUnipotent antiUnipotentCenter uElt minorAut glMat_uElt antiSp_ext mem_antiUnipotent
   mem_antiSp)

@[expose] def Z0list : List Nat :=
  (List.range 4).flatMap fun b => (List.range 4).map fun c => uMat 0 b c 0

@[expose] def weylCode : Nat := 272630020

@[expose] def weylConj (z : Nat) : Nat := mmul weylCode (mmul z weylCode)

@[expose] def inZ0 (m : Nat) : Bool := m == uMat 0 (e2 m 0 2) (e2 m 0 3) 0

theorem weyl_check : symp weylCode = true ∧ mmul weylCode weylCode = idM ∧
    (Z0list.all fun z => inU (weylConj z)) = true ∧
    (Z0list.filter fun z => inZ0 (weylConj z)).length ≤ 4 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

private theorem w183finSp44gi_e2_lt (m i j : Nat) : e2 m i j < 4 := by
  unfold e2
  exact Nat.and_lt_two_pow _ (y := 3) (n := 2) (by norm_num)

private theorem w183finSp44gi_inU_eq (m : Nat) :
    inU m = true ↔ m = uMat (e2 m 0 1) (e2 m 0 2) (e2 m 0 3) (e2 m 1 2) := by
  simp [inU, beq_iff_eq]

private theorem w183finSp44gi_ofNat'_surj (x : GF4) : ∃ n < 4, GF4.ofNat' n = x := by
  obtain ⟨⟨n, hn⟩⟩ := x
  exact ⟨n, hn, by simp [GF4.ofNat', Nat.mod_eq_of_lt hn]⟩

private theorem w183finSp44gi_symp_uMat {a b c d : Nat} (ha : a < 4) (hb : b < 4)
    (hc : c < 4) (hd : d < 4) : symp (uMat a b c d) = true := by
  rw [symp_iff, decodeM_uMat ha hb hc hd]
  have h := (uElt (GF4.ofNat' a) (GF4.ofNat' b) (GF4.ofNat' c) (GF4.ofNat' d)).2
  rw [mem_antiSp] at h
  rwa [glMat_uElt] at h

private theorem w183finSp44gi_uMat_lt {a b c d : Nat} (ha : a < 4) (hb : b < 4)
    (hc : c < 4) (hd : d < 4) : uMat a b c d < 4294967296 := by
  have h : ∀ a' : Fin 4, ∀ b' : Fin 4, ∀ c' : Fin 4, ∀ d' : Fin 4,
      uMat a'.val b'.val c'.val d'.val < 4294967296 := by decide +kernel
  exact h ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩ ⟨d, hd⟩

private theorem w183finSp44gi_uMat_valid {a b c d : Nat} (ha : a < 4) (hb : b < 4)
    (hc : c < 4) (hd : d < 4) : validB (uMat a b c d, 0) = true := by
  rw [validB_iff]
  exact ⟨w183finSp44gi_uMat_lt ha hb hc hd, w183finSp44gi_symp_uMat ha hb hc hd, by norm_num⟩

private theorem w183finSp44gi_toS4_glMat (z : Nat) (hz : symp z = true) :
    SpChain.glMat (↑(toS4 z hz)) = decodeM z :=
  toS4_val z hz

private theorem w183finSp44gi_uElt_glMat (a b c d : GF4) :
    SpChain.glMat (↑(uElt a b c d)) = SpChain.uMat a b c d :=
  glMat_uElt a b c d

private theorem w183finSp44gi_autOf_uMat {a b c d : Nat} (ha : a < 4) (hb : b < 4)
    (hc : c < 4) (hd : d < 4) :
    autOf (uMat a b c d, 0) =
      MulAut.conj (uElt (GF4.ofNat' a) (GF4.ofNat' b) (GF4.ofNat' c) (GF4.ofNat' d)) := by
  have hvalid : validB (uMat a b c d, 0) = true := w183finSp44gi_uMat_valid ha hb hc hd
  have hauto : autOf (uMat a b c d, 0) =
      MulAut.conj (toS4 (uMat a b c d, 0).1 (validB_symp hvalid)) *
        minorAut GF4 ^ (uMat a b c d, 0).2 := by
    rw [autOf, dif_pos hvalid]
  have hto : toS4 (uMat a b c d, 0).1 (validB_symp hvalid) =
      uElt (GF4.ofNat' a) (GF4.ofNat' b) (GF4.ofNat' c) (GF4.ofNat' d) := by
    apply antiSp_ext
    show ((toS4 (uMat a b c d, 0).1 (validB_symp hvalid) : GL (Fin 4) GF4) :
        Matrix (Fin 4) (Fin 4) GF4) =
      ((uElt (GF4.ofNat' a) (GF4.ofNat' b) (GF4.ofNat' c) (GF4.ofNat' d) : GL (Fin 4) GF4) :
        Matrix (Fin 4) (Fin 4) GF4)
    rw [toS4_val]
    rw [show (uMat a b c d, 0).1 = uMat a b c d from rfl]
    rw [decodeM_uMat ha hb hc hd]
    exact (glMat_uElt (GF4.ofNat' a) (GF4.ofNat' b) (GF4.ofNat' c) (GF4.ofNat' d)).symm
  rw [hauto, show (uMat a b c d, 0).2 = 0 from rfl, pow_zero, mul_one]
  exact congrArg MulAut.conj hto

private theorem w183finSp44gi_mem_Pel_uMat {a b c d j : Nat} (ha : a < 4) (hb : b < 4)
    (hc : c < 4) (hd : d < 4) (hj : j < 4) : (uMat a b c d, j) ∈ Pel := by
  rw [Pel]
  refine List.mem_flatMap.mpr ⟨a, List.mem_range.mpr ha, ?_⟩
  refine List.mem_flatMap.mpr ⟨b, List.mem_range.mpr hb, ?_⟩
  refine List.mem_flatMap.mpr ⟨c, List.mem_range.mpr hc, ?_⟩
  refine List.mem_flatMap.mpr ⟨d, List.mem_range.mpr hd, ?_⟩
  exact List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩

private theorem w183finSp44gi_U_le_Psub_inner :
    (antiUnipotent GF4).map (MulAut.conj : S4 →* MulAut S4) ≤ Psub ⊓ innAutOf S4 := by
  intro α hα
  obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hα
  obtain ⟨a, b, c, d, rfl⟩ := hu
  obtain ⟨a', ha', ha⟩ := w183finSp44gi_ofNat'_surj a
  obtain ⟨b', hb', hb⟩ := w183finSp44gi_ofNat'_surj b
  obtain ⟨c', hc', hc⟩ := w183finSp44gi_ofNat'_surj c
  obtain ⟨d', hd', hd⟩ := w183finSp44gi_ofNat'_surj d
  rw [← ha, ← hb, ← hc, ← hd]
  refine Subgroup.mem_inf.mpr ⟨?_, ⟨uElt (GF4.ofNat' a') (GF4.ofNat' b') (GF4.ofNat' c')
    (GF4.ofNat' d'), rfl⟩⟩
  exact (mem_Psub_iff _).mpr ⟨(uMat a' b' c' d', 0),
    w183finSp44gi_mem_Pel_uMat ha' hb' hc' hd' (by norm_num),
    w183finSp44gi_autOf_uMat ha' hb' hc' hd'⟩

theorem w183finSp44gi_Q1_inf_Q2 :
    Q1sub ⊓ Q2sub = (antiUnipotentCenter GF4).map (MulAut.conj : S4 →* MulAut S4) := by
  have hinj : Function.Injective (MulAut.conj : S4 →* MulAut S4) := conj_injective (K := GF4)
  rw [Q1sub, Q2sub,
    ← Subgroup.map_inf (radA1 GF4) (radA2 GF4) (MulAut.conj : S4 →* MulAut S4) hinj,
    radA1_inf_radA2]

private theorem w183finSp44gi_Z0list_symp : Z0list.all symp = true := by decide +kernel

private theorem w183finSp44gi_symp_of_Z0 {z : Nat} (hz : z ∈ Z0list) : symp z = true :=
  List.all_eq_true.mp w183finSp44gi_Z0list_symp z hz

private theorem w183finSp44gi_inU_weylConj_of_Z0 {z : Nat} (hz : z ∈ Z0list) :
    inU (weylConj z) = true :=
  List.all_eq_true.mp weyl_check.2.2.1 z hz

private theorem w183finSp44gi_Z0list_weylConj_lt :
    Z0list.all (fun z => decide (weylConj z < 4294967296)) = true := by decide +kernel

private theorem w183finSp44gi_weylConj_lt_of_Z0 {z : Nat} (hz : z ∈ Z0list) :
    weylConj z < 4294967296 :=
  of_decide_eq_true (List.all_eq_true.mp w183finSp44gi_Z0list_weylConj_lt z hz)

private theorem w183finSp44gi_uMat_lt0 {n m : Nat} (hn : n < 4) (hm : m < 4) :
    uMat 0 n m 0 < 4294967296 :=
  (validB_iff.mp (w183finSp44gi_uMat_valid (by norm_num) hn hm (by norm_num))).1

private theorem w183finSp44gi_inZ0_uMat {n m : Nat} (hn : n < 4) (hm : m < 4) :
    inZ0 (uMat 0 n m 0) = true := by
  have hn' : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 := by omega
  have hm' : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 := by omega
  rcases hn' with rfl | rfl | rfl | rfl <;>
    rcases hm' with rfl | rfl | rfl | rfl <;> decide

private theorem w183finSp44gi_uMat_mem_Z0 {n m : Nat} (hn : n < 4) (hm : m < 4) :
    uMat 0 n m 0 ∈ Z0list := by
  rw [Z0list]
  exact List.mem_flatMap.mpr ⟨n, List.mem_range.mpr hn,
    List.mem_map.mpr ⟨m, List.mem_range.mpr hm, rfl⟩⟩

private noncomputable def w183finSp44gi_W : S4 := toS4 weylCode weyl_check.1

private theorem w183finSp44gi_W_mul_self : w183finSp44gi_W * w183finSp44gi_W = 1 := by
  have hMM : decodeM weylCode * decodeM weylCode = 1 := by
    rw [← decodeM_mmul, weyl_check.2.1, decodeM_idM]
  apply antiSp_ext
  simp [w183finSp44gi_W, toS4_val, hMM]

private theorem w183finSp44gi_weylConj_glMat (z : Nat) (hz : symp z = true) :
    SpChain.glMat (↑(w183finSp44gi_W * toS4 z hz * w183finSp44gi_W⁻¹ : S4)) =
      decodeM (weylConj z) := by
  have hMM : decodeM weylCode * decodeM weylCode = 1 := by
    rw [← decodeM_mmul, weyl_check.2.1, decodeM_idM]
  have hW : ((w183finSp44gi_W : GL (Fin 4) GF4) : Matrix (Fin 4) (Fin 4) GF4) =
      decodeM weylCode := toS4_val weylCode weyl_check.1
  have hWinv : (((w183finSp44gi_W⁻¹ : S4) : GL (Fin 4) GF4) :
      Matrix (Fin 4) (Fin 4) GF4) = decodeM weylCode := by
    rw [inv_eq_of_mul_eq_one_right w183finSp44gi_W_mul_self, hW]
  change (((w183finSp44gi_W * toS4 z hz * w183finSp44gi_W⁻¹ : S4) : GL (Fin 4) GF4) :
    Matrix (Fin 4) (Fin 4) GF4) = decodeM (weylConj z)
  simp only [Subgroup.coe_mul, Units.val_mul, hW, toS4_val, hWinv, weylConj, decodeM_mmul,
    Matrix.mul_assoc]

private theorem w183finSp44gi_inZ0_of_decodeM {m : Nat} (hm : m < 4294967296) {b c : GF4}
    (h : decodeM m = SpChain.uMat 0 b c 0) : inZ0 m = true := by
  obtain ⟨n, hn, hy⟩ := w183finSp44gi_ofNat'_surj b
  obtain ⟨k, hk, hz⟩ := w183finSp44gi_ofNat'_surj c
  rw [← hy, ← hz] at h
  have h2 := decodeM_uMat (a := 0) (b := n) (c := k) (d := 0) (by norm_num) hn hk
    (by norm_num)
  have hm' : m = uMat 0 n k 0 :=
    decodeM_inj hm (w183finSp44gi_uMat_lt0 hn hk) (h.trans h2.symm)
  rw [hm']
  exact w183finSp44gi_inZ0_uMat hn hk

private noncomputable def w183finSp44gi_toS4' (z : Nat) : S4 :=
  if h : symp z = true then toS4 z h else 1

private theorem w183finSp44gi_toS4'_eq {z : Nat} (h : symp z = true) :
    w183finSp44gi_toS4' z = toS4 z h := dif_pos h

private theorem w183finSp44gi_conj_conj {G : Type*} [Group G] (g : MulAut G) (a : G) :
    MulAut.conj g (MulAut.conj a) = MulAut.conj (g a) := by
  ext x
  simp only [MulAut.conj_apply, MulAut.mul_apply, map_mul, map_inv]
  simp

private theorem w183finSp44gi_autConj_le_innAutOf {A : Subgroup (MulAut S4)}
    (hA : A ≤ innAutOf S4) (g : MulAut S4) : autConj g A ≤ innAutOf S4 := by
  intro α hα
  rw [autConj, Subgroup.mem_map] at hα
  obtain ⟨β, hβ, hβα⟩ := hα
  rw [← hβα]
  obtain ⟨a, ha⟩ := hA hβ
  rw [← ha,
    show (MulAut.conj g).toMonoidHom (MulAut.conj a) = MulAut.conj (g a) from
      w183finSp44gi_conj_conj g a]
  exact ⟨g a, rfl⟩

private theorem w183finSp44gi_conj_W_mem_U_of_mem_Z {b : S4}
    (hb : b ∈ antiUnipotentCenter GF4) : MulAut.conj w183finSp44gi_W b ∈ antiUnipotent GF4 := by
  obtain ⟨y, z, hb_eq⟩ := hb
  obtain ⟨n, hn, hy⟩ := w183finSp44gi_ofNat'_surj y
  obtain ⟨k, hk, hz⟩ := w183finSp44gi_ofNat'_surj z
  rw [← hy, ← hz] at hb_eq
  have hzmem : uMat 0 n k 0 ∈ Z0list := w183finSp44gi_uMat_mem_Z0 hn hk
  have hsymp := w183finSp44gi_symp_of_Z0 hzmem
  have hto : toS4 (uMat 0 n k 0) hsymp = uElt 0 (GF4.ofNat' n) (GF4.ofNat' k) 0 := by
    apply antiSp_ext
    rw [w183finSp44gi_toS4_glMat, decodeM_uMat (by norm_num) hn hk (by norm_num),
      w183finSp44gi_uElt_glMat]
    rfl
  rw [MulAut.conj_apply, hb_eq, ← hto, mem_antiUnipotent]
  refine ⟨GF4.ofNat' (e2 (weylConj (uMat 0 n k 0)) 0 1),
    GF4.ofNat' (e2 (weylConj (uMat 0 n k 0)) 0 2),
    GF4.ofNat' (e2 (weylConj (uMat 0 n k 0)) 0 3),
    GF4.ofNat' (e2 (weylConj (uMat 0 n k 0)) 1 2), ?_⟩
  have hiu := (w183finSp44gi_inU_eq (weylConj (uMat 0 n k 0))).mp
    (w183finSp44gi_inU_weylConj_of_Z0 hzmem)
  rw [w183finSp44gi_weylConj_glMat (uMat 0 n k 0) hsymp]
  conv_lhs => rw [hiu, decodeM_uMat (w183finSp44gi_e2_lt _ 0 1) (w183finSp44gi_e2_lt _ 0 2)
    (w183finSp44gi_e2_lt _ 0 3) (w183finSp44gi_e2_lt _ 1 2)]

private theorem w183finSp44gi_exists_Z0 {b : S4} (hb : b ∈ antiUnipotentCenter GF4)
    (hbw : MulAut.conj w183finSp44gi_W b ∈ antiUnipotentCenter GF4) :
    ∃ (z : Nat) (hz : z ∈ Z0list), inZ0 (weylConj z) = true ∧
      w183finSp44gi_toS4' z = b := by
  obtain ⟨y, z, hb_eq⟩ := hb
  obtain ⟨n, hn, hy⟩ := w183finSp44gi_ofNat'_surj y
  obtain ⟨k, hk, hz⟩ := w183finSp44gi_ofNat'_surj z
  rw [← hy, ← hz] at hb_eq
  have hzmem : uMat 0 n k 0 ∈ Z0list := w183finSp44gi_uMat_mem_Z0 hn hk
  have hsymp := w183finSp44gi_symp_of_Z0 hzmem
  have hto : toS4 (uMat 0 n k 0) hsymp = uElt 0 (GF4.ofNat' n) (GF4.ofNat' k) 0 := by
    apply antiSp_ext
    rw [w183finSp44gi_toS4_glMat, decodeM_uMat (by norm_num) hn hk (by norm_num),
      w183finSp44gi_uElt_glMat]
    rfl
  rw [hb_eq, ← hto, MulAut.conj_apply] at hbw
  obtain ⟨b1, b2, hbw_eq⟩ := hbw
  exact ⟨uMat 0 n k 0, hzmem,
    w183finSp44gi_inZ0_of_decodeM (w183finSp44gi_weylConj_lt_of_Z0 hzmem) (by
      rw [← w183finSp44gi_weylConj_glMat (uMat 0 n k 0) hsymp, hbw_eq, glMat_uElt]),
    (w183finSp44gi_toS4'_eq hsymp).trans (hto.trans hb_eq.symm)⟩

private theorem w183finSp44gi_card_le_four {B : Subgroup S4}
    (hBZ : B ≤ antiUnipotentCenter GF4)
    (hBw : B.map (MulAut.conj w183finSp44gi_W).toMonoidHom ≤ antiUnipotentCenter GF4) :
    Nat.card B ≤ 4 := by
  classical
  let Pp : Nat → Bool := fun z => inZ0 (weylConj z)
  have hex : ∀ b : B, ∃ (z : Nat) (hz : z ∈ Z0list), Pp z = true ∧
      w183finSp44gi_toS4' z = (b : S4) := fun b =>
    w183finSp44gi_exists_Z0 (hBZ b.2)
      (hBw (Subgroup.mem_map.mpr ⟨b.1, b.2, rfl⟩))
  choose z hzm hP hb using hex
  let f : B → ↥((Z0list.filter Pp).toFinset) := fun b =>
    ⟨z b, List.mem_toFinset.mpr (List.mem_filter.mpr ⟨hzm b, hP b⟩)⟩
  have hf : Function.Injective f := by
    intro b1 b2 h
    have h1 : z b1 = z b2 := congrArg Subtype.val h
    apply Subtype.ext
    rw [← hb b1, ← hb b2, h1]
  haveI : Fintype ↥((Z0list.filter Pp).toFinset) := Finset.fintypeCoeSort _
  calc Nat.card B ≤ Nat.card ↥((Z0list.filter Pp).toFinset) :=
        Nat.card_le_card_of_injective f hf
    _ = ((Z0list.filter Pp).toFinset).card := by
        rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    _ ≤ (Z0list.filter Pp).length := List.toFinset_card_le (Z0list.filter Pp)
    _ ≤ 4 := weyl_check.2.2.2

private theorem w183finSp44gi_exists_conj_le_Psub (A : Subgroup (MulAut S4))
    (hA : IsPGroup 2 A) : ∃ k : MulAut S4, A.map (MulAut.conj k).toMonoidHom ≤ Psub := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite (MulAut S4) :=
    Finite.of_injective (fun f : MulAut S4 => (f : S4 → S4))
      (fun f g h => MulEquiv.ext (congrFun h))
  let P' : Subgroup ↥(⊤ : Subgroup (MulAut S4)) := Psub.subgroupOf ⊤
  have hP'grp : IsPGroup 2 P' := Psub_sylow.2.1.comap_subtype (K := ⊤)
  have hP'idx : ¬ 2 ∣ P'.index := by
    have h := Subgroup.relIndex_subgroupOf (H := Psub) (K := ⊤) (L := ⊤) le_rfl
    rw [Subgroup.subgroupOf_self, Subgroup.relIndex_top_right] at h
    rw [show P'.index = Psub.relIndex ⊤ from h]
    exact Psub_sylow.2.2
  let P'' : Sylow 2 ↥(⊤ : Subgroup (MulAut S4)) := hP'grp.toSylow hP'idx
  have hP''coe : (P'' : Subgroup ↥(⊤ : Subgroup (MulAut S4))) = Psub.subgroupOf ⊤ :=
    IsPGroup.toSylow_coe _ _
  haveI : P''.FiniteIndex := inferInstance
  haveI : Finite (Sylow 2 ↥(⊤ : Subgroup (MulAut S4))) := Sylow.finite_of_finiteIndex P''
  obtain ⟨P₁, hP₁⟩ := (hA.comap_subtype (K := (⊤ : Subgroup (MulAut S4)))).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (↥(⊤ : Subgroup (MulAut S4))) P₁ P''
  refine ⟨(g : MulAut S4), ?_⟩
  intro x hx
  rw [Subgroup.mem_map] at hx
  obtain ⟨a, ha, rfl⟩ := hx
  have ha' : (⟨a, Subgroup.mem_top a⟩ : ↥(⊤ : Subgroup (MulAut S4))) ∈ P₁ :=
    hP₁ (Subgroup.mem_subgroupOf.mpr ha)
  have hmem : (MulAut.conj g) • (⟨a, Subgroup.mem_top a⟩ : ↥(⊤ : Subgroup (MulAut S4))) ∈
      (P'' : Subgroup ↥(⊤ : Subgroup (MulAut S4))) := by
    rw [← hg, Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul _ (MulAut.conj g)
      (P₁ : Subgroup ↥(⊤ : Subgroup (MulAut S4))) ha'
  have hmemP : ((MulAut.conj g) •
      (⟨a, Subgroup.mem_top a⟩ : ↥(⊤ : Subgroup (MulAut S4)))).1 ∈ Psub := by
    rw [hP''coe] at hmem
    exact Subgroup.mem_subgroupOf.mp hmem
  have hqeq : (MulAut.conj (g : MulAut S4)).toMonoidHom a =
      ((MulAut.conj g) • (⟨a, Subgroup.mem_top a⟩ : ↥(⊤ : Subgroup (MulAut S4)))).1 := by
    change MulAut.conj (g : MulAut S4) a =
      ((MulAut.conj g) • (⟨a, _⟩ : ↥(⊤ : Subgroup (MulAut S4)))).1
    simp [MulAut.conj_apply]
  rw [hqeq]
  exact hmemP

private theorem w183finSp44gi_conj_W_le {C : Subgroup (MulAut S4)}
    (hC : C ≤ Q1sub ⊓ Q2sub) :
    autConj (MulAut.conj w183finSp44gi_W) C ≤ Psub ⊓ innAutOf S4 := by
  intro α hα
  rw [autConj, Subgroup.mem_map] at hα
  obtain ⟨β, hβ, hβα⟩ := hα
  rw [← hβα]
  have hβZ : β ∈ (antiUnipotentCenter GF4).map (MulAut.conj : S4 →* MulAut S4) := by
    rw [← w183finSp44gi_Q1_inf_Q2]
    exact hC hβ
  obtain ⟨b, hb, hbβ⟩ := Subgroup.mem_map.mp hβZ
  rw [← hbβ,
    show (MulAut.conj (MulAut.conj w183finSp44gi_W)).toMonoidHom (MulAut.conj b) =
      MulAut.conj (MulAut.conj w183finSp44gi_W b) from
        w183finSp44gi_conj_conj (MulAut.conj w183finSp44gi_W) b]
  exact w183finSp44gi_U_le_Psub_inner (Subgroup.mem_map.mpr
    ⟨MulAut.conj w183finSp44gi_W b, w183finSp44gi_conj_W_mem_U_of_mem_Z hb, rfl⟩)

private theorem w183finSp44gi_autConj_mul (A : Subgroup (MulAut S4)) (k : MulAut S4) :
    autConj (MulAut.conj w183finSp44gi_W * k) A =
      autConj (MulAut.conj w183finSp44gi_W) (autConj k A) := by
  ext α
  simp only [autConj, Subgroup.mem_map]
  constructor
  · rintro ⟨β, hβ, hβα⟩
    refine ⟨MulAut.conj k β, ⟨β, hβ, rfl⟩, ?_⟩
    rw [← hβα]
    change MulAut.conj (MulAut.conj w183finSp44gi_W) (MulAut.conj k β) =
      MulAut.conj (MulAut.conj w183finSp44gi_W * k) β
    simp only [MulAut.conj_apply]
    group
  · rintro ⟨γ, ⟨β, hβ, hβγ⟩, hγα⟩
    refine ⟨β, hβ, ?_⟩
    rw [← hγα, ← hβγ]
    change MulAut.conj (MulAut.conj w183finSp44gi_W * k) β =
      MulAut.conj (MulAut.conj w183finSp44gi_W) (MulAut.conj k β)
    simp only [MulAut.conj_apply]
    group

theorem inner_case (A : Subgroup (MulAut S4)) (hel : IsElemAbelian 2 A) (h8 : 8 ≤ Nat.card A)
    (hin : A ≤ innAutOf S4) :
    ∃ g : MulAut S4, autConj g A ≤ Psub ⊓ innAutOf S4 ∧ ¬ autConj g A ≤ Q1sub ⊓ Q2sub := by
  obtain ⟨k, hkP⟩ := w183finSp44gi_exists_conj_le_Psub A hel.isPGroup
  have hkIn : autConj k A ≤ innAutOf S4 := w183finSp44gi_autConj_le_innAutOf hin k
  have hkS : autConj k A ≤ Psub ⊓ innAutOf S4 := le_inf hkP hkIn
  by_cases hout : autConj k A ≤ Q1sub ⊓ Q2sub
  · refine ⟨MulAut.conj w183finSp44gi_W * k, ?_, ?_⟩
    · rw [w183finSp44gi_autConj_mul]
      exact w183finSp44gi_conj_W_le hout
    · rw [w183finSp44gi_autConj_mul]
      intro hconj
      let B : Subgroup S4 := (autConj k A).comap (MulAut.conj : S4 →* MulAut S4)
      have hA'le : autConj k A ≤ (MulAut.conj : S4 →* MulAut S4).range := hkIn
      have hBmap : B.map (MulAut.conj : S4 →* MulAut S4) = autConj k A :=
        Subgroup.map_comap_eq_self hA'le
      have hBZ : B ≤ antiUnipotentCenter GF4 := by
        intro b hb
        have hbc : MulAut.conj b ∈ autConj k A := Subgroup.mem_comap.mp hb
        have hmem : MulAut.conj b ∈ (antiUnipotentCenter GF4).map
            (MulAut.conj : S4 →* MulAut S4) := by
          rw [← w183finSp44gi_Q1_inf_Q2]
          exact hout hbc
        obtain ⟨b', hb', hb'b⟩ := Subgroup.mem_map.mp hmem
        rwa [← conj_injective hb'b]
      have hBw : B.map (MulAut.conj w183finSp44gi_W).toMonoidHom ≤
          antiUnipotentCenter GF4 := by
        intro x hx
        rw [Subgroup.mem_map] at hx
        obtain ⟨b, hb, hbx⟩ := hx
        rw [← hbx]
        have hbc : MulAut.conj b ∈ autConj k A := Subgroup.mem_comap.mp hb
        have hmem : MulAut.conj (MulAut.conj w183finSp44gi_W b) ∈
            autConj (MulAut.conj w183finSp44gi_W) (autConj k A) :=
          Subgroup.mem_map.mpr ⟨MulAut.conj b, hbc,
            w183finSp44gi_conj_conj (MulAut.conj w183finSp44gi_W) b⟩
        have hZ : MulAut.conj (MulAut.conj w183finSp44gi_W b) ∈ Q1sub ⊓ Q2sub := hconj hmem
        rw [w183finSp44gi_Q1_inf_Q2] at hZ
        obtain ⟨b', hb', hb'b⟩ := Subgroup.mem_map.mp hZ
        change (MulAut.conj w183finSp44gi_W) b ∈ antiUnipotentCenter GF4
        rwa [← conj_injective hb'b]
      have hcard := w183finSp44gi_card_le_four hBZ hBw
      have hcardB : Nat.card B = Nat.card A := by
        have h1 : Nat.card B = Nat.card (B.map (MulAut.conj : S4 →* MulAut S4)) :=
          (Subgroup.card_map_of_injective (K := B) conj_injective).symm
        have h2 : Nat.card (B.map (MulAut.conj : S4 →* MulAut S4)) = Nat.card A := by
          rw [hBmap, autConj,
            Subgroup.card_map_of_injective (K := A) (MulAut.conj k).injective]
        exact h1.trans h2
      omega
  · exact ⟨k, hkS, hout⟩

end CFSG.LocalAnalysis.WeakClosure81.Sp44

end
