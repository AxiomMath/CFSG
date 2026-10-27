module

public import CFSG.RankThree.PartTwo.Sec21.FF81Sec52M
public import CFSG.RankThree.PartTwo.Sec21.FF81Sec526
import CFSG.RankThree.PartTwo.Sec21.FF81Sec53

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG.RankThree.PartTwo.Sec21.FF79
open P51 (V e)

namespace S52

def gf : Fin 3 → V → V := ![ft, fs, fr]

def act (w : List (Fin 3)) (v : V) : V := w.foldr (fun i u => gf i u) v

def lw : List (List (Fin 3)) :=
  [[], [0], [1], [2], [1, 0], [2, 0], [0, 1], [2, 1], [0, 2], [0, 1, 0], [2, 1, 0], [0, 2, 0],
    [1, 0, 1], [2, 0, 1], [0, 2, 1], [1, 0, 2], [1, 0, 1, 0], [2, 0, 1, 0], [0, 2, 1, 0],
    [1, 0, 2, 0], [2, 1, 0, 1], [0, 2, 0, 1], [1, 0, 2, 1], [0, 1, 0, 2], [2, 1, 0, 1, 0],
    [0, 2, 0, 1, 0], [1, 0, 2, 1, 0], [0, 1, 0, 2, 0], [0, 2, 1, 0, 1], [1, 0, 2, 0, 1],
    [0, 1, 0, 2, 1], [2, 0, 1, 0, 2], [0, 2, 1, 0, 1, 0], [1, 0, 2, 0, 1, 0], [0, 1, 0, 2, 1, 0],
    [2, 0, 1, 0, 2, 0], [1, 0, 2, 1, 0, 1], [0, 1, 0, 2, 0, 1], [2, 0, 1, 0, 2, 1],
    [1, 0, 2, 1, 0, 1, 0], [0, 1, 0, 2, 0, 1, 0], [2, 0, 1, 0, 2, 1, 0], [0, 1, 0, 2, 1, 0, 1],
    [2, 0, 1, 0, 2, 0, 1], [0, 1, 0, 2, 1, 0, 1, 0], [2, 0, 1, 0, 2, 0, 1, 0],
    [2, 0, 1, 0, 2, 1, 0, 1], [2, 0, 1, 0, 2, 1, 0, 1, 0]]

def t12 : Fin 12 → V :=
  ![![2, 0, 0, 0], ![0, 2, 0, 0], ![0, 1, 0, 0], ![1, 0, 0, 0], ![1, 1, 1, 1], ![1, 1, 2, 2],
    ![2, 2, 1, 1], ![2, 2, 2, 2], ![1, 2, 1, 1], ![1, 2, 2, 2], ![2, 1, 1, 1], ![2, 1, 2, 2]]

def tw : Fin 12 → List (Fin 3) :=
  ![[0], [1, 0], [1], [], [0, 2], [0, 2, 1, 0], [0, 2, 1], [0, 2, 0], [2, 1], [2, 0], [2],
    [2, 1, 0]]

def emb (x : Fin 3 → ZMod 3) : V := ![x 0, x 1, x 2, x 2]

def Tup (G : Type) : Type := Fin 3 → G

theorem emb_smul (s : ZMod 3) (x : Fin 3 → ZMod 3) : emb (s • x) = s • emb x := by
  ext j; fin_cases j <;> simp [emb]

set_option maxRecDepth 100000 in
theorem lw_nodup : (lw.map fun w => fun i : Fin 3 => act w (uv i)).Nodup := by decide +kernel

theorem lw_length : lw.length = 48 := rfl

set_option maxRecDepth 100000 in
theorem tw_act : ∀ k : Fin 12, act (tw k) (e 0) = t12 k := by decide +kernel

set_option maxRecDepth 100000 in
theorem span_key : ∀ x y : Fin 3 → ZMod 3, x ≠ 0 → (∀ s : ZMod 3, y ≠ s • x) →
    ∃ s t : ZMod 3, ∃ k : Fin 12, s • emb x + t • emb y = t12 k := by decide +kernel

set_option maxRecDepth 100000 in
theorem span3 : ∀ v : V, v 2 = v 3 → ∃ c : Fin 3 → ZMod 3,
    v = c 0 • uv 0 + c 1 • uv 1 + c 2 • uv 2 := by decide +kernel

theorem uv_ne : ∀ a b : Fin 3, a ≠ b → uv a ≠ uv b ∧ uv a ≠ -uv b := by decide

set_option maxRecDepth 100000 in
theorem card_mono : (Finset.univ.filter fun idx : Fin 3 → Fin 6 => ∀ a b : Fin 3, a ≠ b →
    ffv (idx a) ≠ ffv (idx b) ∧ ffv (idx a) ≠ -ffv (idx b)).card = 48 := by decide +kernel

end S52

variable {G : Type} [Group G] [Finite G] {b : G} {L B : Subgroup G} {b₁ b₂ b₃ t₀ s₀ : G}

section Gens

variable (hKF : KF_Sp6Levi) (h5 : FF81Sec5 b L B b₁ b₂ b₃ t₀ s₀)
include hKF h5

theorem FF81Sec5.gens : ∃ g : Fin 3 → G, (∀ i, g i ∈ H₅₂ b b₁ b₂ b₃ s₀) ∧
    ∀ i v, g i * h5.ε v * (g i)⁻¹ = h5.ε (S52.gf i v) := by
  obtain ⟨-, -, -, ⟨n₁, hn₁⟩, ⟨n₂, hn₂⟩⟩ := h5.setup
  obtain ⟨g0, hg0, hg0'⟩ := h5.lift hKF h5.t₀_ε (fun v hv => by simp [S52.ft, hv]) (by decide)
  obtain ⟨g1, hg1, hg1'⟩ := h5.lift hKF hn₁ (fun v hv => by simp [S52.fs, hv]) (by decide)
  obtain ⟨g2, hg2, hg2'⟩ := h5.lift hKF hn₂ (fun v hv => by simp [S52.fr, hv]) (by decide)
  refine ⟨![g0, g1, g2], ?_, ?_⟩ <;> intro i <;> fin_cases i
  exacts [hg0, hg1, hg2, hg0', hg1', hg2']

omit hKF in
theorem FF81Sec5.word_conj {g : Fin 3 → G}
    (hg : ∀ i v, g i * h5.ε v * (g i)⁻¹ = h5.ε (S52.gf i v)) (w : List (Fin 3)) (v : V) :
    (w.map g).prod * h5.ε v * ((w.map g).prod)⁻¹ = h5.ε (S52.act w v) := by
  induction w with
  | nil => simp [S52.act]
  | cons i w ih =>
    rw [List.map_cons, List.prod_cons]
    calc g i * (w.map g).prod * h5.ε v * (g i * (w.map g).prod)⁻¹
        = g i * ((w.map g).prod * h5.ε v * ((w.map g).prod)⁻¹) * (g i)⁻¹ := by group
      _ = h5.ε (S52.act (i :: w) v) := by rw [ih, hg]; rfl

theorem FF81Sec5.relIndex_H : (CenS (A₁sub b b₁ b₂ b₃)).relIndex (H₅₂ b b₁ b₂ b₃ s₀) = 48 := by
  obtain ⟨g, hgH, hg⟩ := h5.gens hKF
  set H := H₅₂ b b₁ b₂ b₃ s₀ with hHdef
  classical
  letI : MulAction H (S52.Tup G) :=
    { smul := fun h x i => (h : G) * x i * (h : G)⁻¹
      one_smul := fun x => funext fun i => by
        show ((1 : H) : G) * x i * ((1 : H) : G)⁻¹ = x i
        rw [Subgroup.coe_one]; group
      mul_smul := fun h k x => funext fun i => by
        show ((h * k : H) : G) * x i * ((h * k : H) : G)⁻¹ =
          (h : G) * ((k : G) * x i * (k : G)⁻¹) * (h : G)⁻¹
        rw [Subgroup.coe_mul]; group }
  haveI : Finite (S52.Tup G) := inferInstanceAs (Finite (Fin 3 → G))
  have hsmul : ∀ (h : H) (x : S52.Tup G) i,
      (h • x : Fin 3 → G) i = (h : G) * (x : Fin 3 → G) i * (h : G)⁻¹ :=
    fun _ _ _ => rfl
  have hext : ∀ x y : S52.Tup G, (∀ i, (x : Fin 3 → G) i = (y : Fin 3 → G) i) → x = y :=
    fun _ _ h => funext h
  set x₀ : S52.Tup G := fun i => h5.ε (S52.uv i) with hx₀
  have hu : ∀ i, S52.uv i 2 = S52.uv i 3 := by decide
  have hstab : (CenS (A₁sub b b₁ b₂ b₃)).subgroupOf H = MulAction.stabilizer H x₀ := by
    ext h
    rw [Subgroup.mem_subgroupOf, MulAction.mem_stabilizer_iff]
    constructor
    · intro hc
      refine hext _ _ fun i => ?_
      rw [hsmul, ← Subgroup.mem_centralizer_iff.mp hc _ (h5.mem_A₁_of (hu i)),
        mul_inv_cancel_right]
    · intro hs
      refine Subgroup.mem_centralizer_iff.mpr fun a ha => ?_
      obtain ⟨v, hv, rfl⟩ := h5.coord_of_mem_A₁ ha
      obtain ⟨c, rfl⟩ := S52.span3 v hv
      have hc : ∀ i, Commute (h5.ε (S52.uv i)) (h : G) := fun i => by
        have hfix : (h : G) * h5.ε (S52.uv i) * (h : G)⁻¹ = h5.ε (S52.uv i) := congrFun hs i
        show h5.ε (S52.uv i) * h = h * h5.ε (S52.uv i)
        calc h5.ε (S52.uv i) * h = ((h : G) * h5.ε (S52.uv i) * (h : G)⁻¹) * h := by rw [hfix]
          _ = h * h5.ε (S52.uv i) := by group
      rw [h5.ε_add, h5.ε_add, h5.ε_smul, h5.ε_smul, h5.ε_smul]
      exact ((((hc 0).pow_left _).mul_left ((hc 1).pow_left _)).mul_left ((hc 2).pow_left _)).eq
  rw [Subgroup.relIndex, hstab, MulAction.index_stabilizer]
  apply le_antisymm
  ·
    let S := Finset.univ.filter fun idx : Fin 3 → Fin 6 => ∀ a b : Fin 3, a ≠ b →
      S52.ffv (idx a) ≠ S52.ffv (idx b) ∧ S52.ffv (idx a) ≠ -S52.ffv (idx b)
    let F : (Fin 3 → Fin 6) → S52.Tup G := fun idx i => h5.ε (S52.ffv (idx i))
    have hsub : MulAction.orbit H x₀ ⊆ ↑(S.image F) := by
      rintro _ ⟨h, rfl⟩
      choose idx hidx using fun i => h5.monomial hKF h.2 i
      have hconj : ∀ {y z : G}, (h : G) * y * (h : G)⁻¹ = (h : G) * z * (h : G)⁻¹ → y = z :=
        fun hyz => mul_left_cancel (mul_right_cancel hyz)
      refine Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨idx, ?_, hext _ _ fun i => (hidx i).symm⟩)
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun a c hac => ⟨fun heq => ?_, fun heq => ?_⟩⟩
      · have := hconj ((hidx a).trans ((congrArg h5.ε heq).trans (hidx c).symm))
        exact (S52.uv_ne a c hac).1 (h5.ε_inj this)
      · have h1 : (h : G) * h5.ε (S52.uv a) * (h : G)⁻¹ =
            (h : G) * h5.ε (-S52.uv c) * (h : G)⁻¹ := by
          rw [hidx a, heq, h5.ε_neg, h5.ε_neg, ← hidx c]; group
        exact (S52.uv_ne a c hac).2 (h5.ε_inj (hconj h1))
    calc (MulAction.orbit H x₀).ncard ≤ (↑(S.image F) : Set (S52.Tup G)).ncard :=
          Set.ncard_le_ncard hsub (Finset.finite_toSet _)
      _ = (S.image F).card := Set.ncard_coe_finset _
      _ ≤ S.card := Finset.card_image_le
      _ = 48 := S52.card_mono
  ·
    let Fw : List (Fin 3) → S52.Tup G := fun w i => h5.ε (S52.act w (S52.uv i))
    have hinj : Function.Injective fun (f : Fin 3 → V) => (fun i => h5.ε (f i) : S52.Tup G) :=
      fun f f' hff => funext fun i => h5.ε_inj (congrFun hff i)
    have hnd : (S52.lw.map Fw).Nodup := by
      have := S52.lw_nodup.map hinj
      rwa [List.map_map] at this
    have hsub : ↑(S52.lw.map Fw).toFinset ⊆ MulAction.orbit H x₀ := by
      intro y hy
      obtain ⟨w, -, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp (Finset.mem_coe.mp hy))
      refine ⟨⟨(w.map g).prod, Subgroup.list_prod_mem _ (l := w.map g) fun x hx => by
        obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx; exact hgH i⟩, hext _ _ fun i => ?_⟩
      exact (hsmul _ _ i).trans (h5.word_conj hg w _)
    calc 48 = (S52.lw.map Fw).toFinset.card := by
          rw [List.toFinset_card_of_nodup hnd, List.length_map, S52.lw_length]
      _ = (↑(S52.lw.map Fw).toFinset : Set (S52.Tup G)).ncard := (Set.ncard_coe_finset _).symm
      _ ≤ (MulAction.orbit H x₀).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)

theorem FF81Sec5.hyperplane {W : Subgroup G} (hW : W ≤ A₁sub b b₁ b₂ b₃) (hE : IsElemAb 3 2 W) :
    ∃ h ∈ H₅₂ b b₁ b₂ b₃ s₀, h * b * h⁻¹ ∈ W := by
  obtain ⟨g, hgH, hg⟩ := h5.gens hKF
  have hcard : Nat.card W = 9 := by rw [hE.2]; norm_num
  obtain ⟨a, haW, ha1⟩ : ∃ a ∈ W, a ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have : W = ⊥ := (Subgroup.eq_bot_iff_forall W).mpr hcon
    rw [this, Subgroup.card_bot] at hcard
    norm_num at hcard
  obtain ⟨c, hcW, hca⟩ : ∃ c ∈ W, c ∉ Subgroup.zpowers a := by
    by_contra hcon
    push Not at hcon
    have h1 := Subgroup.card_le_of_le (show W ≤ Subgroup.zpowers a from fun c hc => hcon c hc)
    rw [hcard, Nat.card_zpowers] at h1
    have h3 : a ^ 3 = 1 := h5.basis.B_cube (h5.A₁_le_B (hW haW))
    have := orderOf_le_of_pow_eq_one (by norm_num) h3
    omega
  obtain ⟨av, hav, rfl⟩ := h5.coord_of_mem_A₁ (hW haW)
  obtain ⟨cv, hcv, rfl⟩ := h5.coord_of_mem_A₁ (hW hcW)
  have hav0 : av ≠ 0 := fun h => ha1 (by rw [h, h5.ε_zero])
  have hcs : ∀ s : ZMod 3, cv ≠ s • av := fun s h => hca (by
    rw [h, h5.ε_smul]; exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _)
  have hax : av = S52.emb ![av 0, av 1, av 2] := by
    ext j; fin_cases j <;> simp [S52.emb, hav]
  have hcy : cv = S52.emb ![cv 0, cv 1, cv 2] := by
    ext j; fin_cases j <;> simp [S52.emb, hcv]
  have hx0 : (![av 0, av 1, av 2] : Fin 3 → ZMod 3) ≠ 0 := fun h => hav0 (by
    rw [hax, h]; decide)
  have hys : ∀ s : ZMod 3, (![cv 0, cv 1, cv 2] : Fin 3 → ZMod 3) ≠ s • ![av 0, av 1, av 2] :=
    fun s h => hcs s (by rw [hax, hcy, h, S52.emb_smul])
  obtain ⟨s, t, k, hk⟩ := S52.span_key _ _ hx0 hys
  refine ⟨((S52.tw k).map g).prod, Subgroup.list_prod_mem _ (l := (S52.tw k).map g) fun x hx => by
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx; exact hgH i, ?_⟩
  rw [← h5.ε_e0, h5.word_conj hg, S52.tw_act k, ← hk, h5.ε_add, h5.ε_smul, h5.ε_smul, ← hax,
    ← hcy]
  exact W.mul_mem (W.pow_mem haW _) (W.pow_mem hcW _)

end Gens

theorem ff81_5_2 (hKF : KF_Sp6Levi) : FF81_5_2 := by
  intro G _ _ b L B b₁ b₂ b₃ t₀ s₀ h5 _ _
  refine ⟨h5.nor_A₁_eq hKF, h5.A₁_le_H hKF, h5.relIndex_H hKF, fun h hh x hx => ?_,
    fun W hW hE => h5.hyperplane hKF hW hE⟩
  obtain ⟨e0', e1', e2'⟩ := h5.ε_uv
  obtain ⟨i, rfl⟩ : ∃ i, x = h5.ε (S52.uv i) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    exacts [⟨0, e0'.symm⟩, ⟨1, e1'.symm⟩, ⟨2, e2'.symm⟩]
  obtain ⟨j, hj⟩ := h5.monomial hKF hh i
  rw [hj]
  exact h5.ε_ffv_mem j

end CFSG.RankThree.PartTwo.Sec21.FF81
