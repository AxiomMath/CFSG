
module

public import CFSG.LocalAnalysis.StandardType.GGQ2ExcRaw
public import CFSG.LocalAnalysis.StandardType.GGQ2TableBNbrFrameDefs
public import Certificates.Data.CFSGNative.ExcCensus.Nbr
public import CFSG.LocalAnalysis.StandardType.GGQ2ExcCensusLin
public import CFSG.LocalAnalysis.StandardType.GGQ2TableBNbrFrameAut
import CFSG.LocalAnalysis.StandardType.GGQ2ExcRawInternal

@[expose] public section

namespace CFSG.StandardType.GGQ2Frame.ExcRaw

open Module

noncomputable section

variable {m : Fin 6} {T : Chk.Tabs} {w : Chk.LinW}

theorem root_eq_zero_of_reflection_apply (t : Root m) {v : V m} (h : reflection m t v = v) :
    root m t v = 0 := by
  rw [reflection_apply, sub_eq_self] at h
  rcases smul_eq_zero.mp h with h | h
  · exact h
  · have h2 := root_coroot m t
    rw [h, map_zero] at h2
    exact absurd h2 (by decide)

private theorem sgnN_cast_ne_zero (w : Chk.LinW) (i : ℕ) : (Chk.sgnN w i : ZMod 3) ≠ 0 := by
  have h : Chk.sgnN w i = 1 ∨ Chk.sgnN w i = -1 := by
    unfold Chk.sgnN
    split <;> simp
  rcases h with h | h <;> rw [h] <;> norm_num

theorem linOf_root_eq_zero_iff (hT : Chk.tabsOK m T = true) (hw : Chk.linOK T (nroots m) w = true)
    {k : ℕ} {L : List (ℕ × ℕ)}
    (hgen : Chk.genOK T (nroots m) (Chk.nodeMask w fun _ => true) k L = true)
    (hb : Chk.notB2 m k = true) (v : V m) :
    (∀ i, (linOf m T hT w hw).root i v = 0) ↔ v ∈ cent m (ofMask m k) := by
  have hnode := typeOK_node_lt (linOK_typeOK hw)
  have hcent : v ∈ cent m (ofMask m k) ↔ ∀ t ∈ ofMask m k, root m t v = 0 := by
    simp only [cent, Submodule.mem_iInf, LinearMap.mem_ker]
  have hroot : ∀ i : Fin (Chk.rkN w.tc w.n),
      (linOf m T hT w hw).root i v = (Chk.sgnN w i : ZMod 3) * root m (nodeRoot m w hnode i) v := by
    intro i
    rw (config := { transparency := .all }) [linOf_root, LinearMap.smul_apply, smul_eq_mul]
  rw [hcent]
  constructor
  · intro hv t ht
    have hfix : ∀ i, reflection m (nodeRoot m w hnode i) ∈
        MulAction.stabilizer (V m ≃ₗ[ZMod 3] V m) v := by
      intro i
      rw [MulAction.mem_stabilizer_iff, LinearEquiv.smul_def, reflection_apply]
      have h := hv i
      rw (config := { transparency := .all }) [hroot i] at h
      rw [(mul_eq_zero.mp h).resolve_left (sgnN_cast_ne_zero w i), zero_smul]
      exact sub_zero v
    have hpar := linOf_parab_eq (m := m) hT hw (p := fun _ => true) hgen hb
    rw [normalizerGroup_ofMask hb, linOf_parab] at hpar
    have hle : weyl m (ofMask m k) ≤ MulAction.stabilizer (V m ≃ₗ[ZMod 3] V m) v := by
      rw [← hpar, Subgroup.closure_le]
      rintro _ ⟨_, ⟨i, -, rfl⟩, rfl⟩
      exact hfix i
    have hmem := hle (Subgroup.subset_closure ⟨t, ht, rfl⟩ : reflection m t ∈ weyl m (ofMask m k))
    rw [MulAction.mem_stabilizer_iff, LinearEquiv.smul_def] at hmem
    exact root_eq_zero_of_reflection_apply t hmem
  · intro hv i
    rw (config := { transparency := .all }) [hroot i,
      hv _ (genOK_subset hgen ((mem_ofMask_nodeMask hnode _ _).mpr ⟨i, rfl, rfl⟩)), mul_zero]

theorem codeWeylDatum_of_genOK (hT : Chk.tabsOK m T = true) (hw : Chk.linOK T (nroots m) w = true)
    {k : ℕ} {L : List (ℕ × ℕ)}
    (hgen : Chk.genOK T (nroots m) (Chk.nodeMask w fun _ => true) k L = true)
    (hb : Chk.notB2 m k = true) : Nonempty (CodeWeylDatum (excRaw m) (ofMask m k)) := by
  have hpar := linOf_parab_eq (m := m) hT hw (p := fun _ => true) hgen hb
  have huniv : ({i | (fun _ : ℕ => true) i = true} : Set (Fin (Chk.rkN w.tc w.n))) = Set.univ :=
    Set.eq_univ_of_forall fun _ => rfl
  rw [huniv] at hpar
  have hcl : Subgroup.closure (Set.range (linOf m T hT w hw).toLin.simpleRefl) =
      normalizerGroup m (ofMask m k) := by
    rw [← Set.image_univ]
    exact hpar
  exact ⟨{
    ι := Fin (Chk.rkN w.tc w.n)
    coxeter := (linOf m T hT w hw).coxeter
    cartan := (linOf m T hT w hw).cartan
    coroot := (linOf m T hT w hw).coroot
    root := (linOf m T hT w hw).root
    isWeyl := (linOf m T hT w hw).isWeyl
    isCartan := (linOf m T hT w hw).isCartan
    pairing := (linOf m T hT w hw).pairing
    refl := (linOf m T hT w hw).toLin.simpleRefl
    refl_apply := fun i v => Module.reflection_apply v _
    closure_refl := hcl
    ker_iff := linOf_root_eq_zero_iff hT hw hgen hb }⟩

private theorem tbnx_nat_all_iff {n : ℕ} {f : (i : ℕ) → i < n → Bool} :
    Nat.all n f = true ↔ ∀ i (h : i < n), f i h = true := by
  induction n with
  | zero => rw [Nat.all_zero]; simp
  | succ n ih =>
    rw [Nat.all_succ, Bool.and_eq_true]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases Nat.lt_or_ge i n with h | h
      · exact ih.mp h1 i h
      · have : i = n := by omega
        subst this
        simpa using h2
    · intro h
      exact ⟨ih.mpr fun i hi => h i (by omega), h n (by omega)⟩

private theorem tbnx_testBit_of_subN {a b t : ℕ} (h : Chk.subN a b = true)
    (ht : a.testBit t = true) : b.testBit t = true := by
  have h' : a &&& b = a := by simpa [Chk.subN] using h
  have h'' := congrArg (fun n => n.testBit t) h'
  simp only [Nat.testBit_land, ht, Bool.true_and] at h''
  exact h''

private theorem tbnx_testBit_trunc {r c t : ℕ} (ht : t < r) :
    (Chk.trunc r c).testBit t = c.testBit t := by
  simp [Chk.trunc, ht]

private theorem tbnx_eq_ofMask (hT : Chk.tabsOK m T = true) {v : V m} {z k' : ℕ}
    (hz : ∀ t : Root m, t ∈ ofMask m z ↔ root m t v = 0)
    (hconn : Chk.connN T (nroots m) k' = true) (hsub : Chk.subN (Chk.trunc (nroots m) k') z = true)
    (hcl : ∀ i < nroots m, k'.testBit i = true → Chk.subN (T.adj[i]! &&& z) k' = true)
    {k : Finset (Root m)} (hk : occurs m (Submodule.span (ZMod 3) {v}) k) {t : Root m}
    (htk : t ∈ k) (htk' : t ∈ ofMask m k') : k = ofMask m k' := by
  obtain ⟨-, hkS, hkcl, hkmin⟩ := hk
  have hS : ∀ i, Vanish m (Submodule.span (ZMod 3) {v}) i ↔ i ∈ ofMask m z := fun i => by
    rw [vanish_span_singleton_iff, hz]
  have hK'S : ∀ i ∈ ofMask m k', Vanish m (Submodule.span (ZMod 3) {v}) i := fun i hi => by
    rw [hS, mem_ofMask]
    exact tbnx_testBit_of_subN hsub (by rw [tbnx_testBit_trunc i.isLt]; exact mem_ofMask.mp hi)
  have hK'cl : ∀ i ∈ ofMask m k', ∀ j, Vanish m (Submodule.span (ZMod 3) {v}) j → Adj m i j →
      j ∈ ofMask m k' := fun i hi j hj hij => by
    have hadj : (T.adj[i.val]!).testBit j = true := (tabsOK_adj hT i j).mpr ⟨j.isLt, hij⟩
    have hzj : z.testBit j = true := mem_ofMask.mp ((hS j).mp hj)
    rw [mem_ofMask]
    exact tbnx_testBit_of_subN (hcl i i.isLt (mem_ofMask.mp hi))
      (by rw [Nat.testBit_land, hadj, hzj]; rfl)
  have hconn' := connN_sound hT hconn
  refine le_antisymm ?_ ?_
  · have h := hkmin (k ∩ ofMask m k') Finset.inter_subset_left ⟨t, Finset.mem_inter.mpr ⟨htk, htk'⟩⟩
      fun i hi j hj hij => Finset.mem_inter.mpr
        ⟨hj, hK'cl i (Finset.mem_inter.mp hi).2 j (hkS j hj) hij⟩
    rw [← h]
    exact Finset.inter_subset_right
  · have h := hconn'.2 (k ∩ ofMask m k') Finset.inter_subset_right
      ⟨t, Finset.mem_inter.mpr ⟨htk, htk'⟩⟩
      fun i hi j hj hij => Finset.mem_inter.mpr
        ⟨hkcl i (Finset.mem_inter.mp hi).1 j (hK'S j hj) hij, hj⟩
    rw [← h]
    exact Finset.inter_subset_left

theorem nbrWeylDataVx_of_nbrLineOK (hT : Chk.tabsOK m T = true) {X : Chk.NSearch} {v : V m}
    (h : Chk.nbrLineOK T m X (code m v) = true) : NbrWeylDataVx (excRaw m) v := by
  intro k _ _ hocc hcod
  change occurs m (Submodule.span (ZMod 3) {v}) k at hocc
  change 3 + finrank (ZMod 3) (cent m k) ≤ finrank (ZMod 3) (V m) at hcod
  have hcv : code m v < 3 ^ dim m := code_lt m v
  have hline' := h
  simp only [Chk.nbrLineOK, Chk.compsOK, Bool.and_eq_true] at hline'
  obtain ⟨⟨hks, hcover⟩, hdata⟩ := hline'
  have hz : ∀ t : Root m, t ∈ ofMask m (T.zm[code m v]!) ↔ root m t v = 0 := fun t => by
    rw [mem_ofMask_zm hT hcv t, vec_code m v]
  obtain ⟨t, htk⟩ := hocc.1
  have htz : (T.zm[code m v]!).testBit t = true :=
    mem_ofMask.mp ((hz t).mpr (vanish_span_singleton_iff.mp (hocc.2.1 t htk)))
  have hcov := (tbnx_nat_all_iff.mp hcover) t t.isLt
  simp only [htz, Bool.not_true, Bool.false_or, List.any_eq_true, List.mem_map] at hcov
  obtain ⟨_, ⟨⟨k', W⟩, he, rfl⟩, hk't⟩ := hcov
  have hkk := List.all_eq_true.mp hks k' (List.mem_map.mpr ⟨(k', W), he, rfl⟩)
  simp only [Bool.and_eq_true] at hkk
  obtain ⟨⟨hconn, hsub⟩, hcl⟩ := hkk
  have hcl' : ∀ i < nroots m, k'.testBit i = true →
      Chk.subN (T.adj[i]! &&& T.zm[code m v]!) k' = true := fun i hi hb => by
    have h := (tbnx_nat_all_iff.mp hcl) i hi
    simp only [hb, Bool.not_true, Bool.false_or] at h
    exact h
  have hkeq : k = ofMask m k' := tbnx_eq_ofMask hT hz hconn hsub hcl' hocc htk (mem_ofMask.mpr hk't)
  subst hkeq
  have hW : Chk.nbrWOK T m k' W = true := List.all_eq_true.mp hdata (k', W) he
  cases W with
  | small g L =>
    simp only [Chk.nbrWOK, Bool.and_eq_true, decide_eq_true_eq] at hW
    have hle := finrank_le_card_add_finrank_cent hT hW.2
    rw [card_ofMask] at hle
    omega
  | weyl w L =>
    simp only [Chk.nbrWOK, Bool.and_eq_true] at hW
    exact codeWeylDatum_of_genOK hT hW.1.1 hW.1.2 hW.2

end

end CFSG.StandardType.GGQ2Frame.ExcRaw

end
