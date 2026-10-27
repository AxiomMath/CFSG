module

public import CFSG.RankThree.PartTwo.Sec11.Item1119SymLines
public import CFSG.RankThree.PartTwo.Sec11.Item1119CMAux
public import CFSG.RankThree.PartTwo.Sec11.Item1119SymAY

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open scoped commutatorElement

section Facts


variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
  {R Y : Subgroup G} {d x s r g : G}

theorem sym1119_zpowers_d_eq (h : Sec11Data G A c L a R Y d x s r g) (hord : orderOf x = 27) :
    Subgroup.zpowers d = Subgroup.zpowers (x ^ 9) :=
  Item1119Sym.zpowers_eq_of_orderOf x d hord (Item1115Proof.d_mem_zpowers_x h)
    (Item1117Proof.orderOf_d h)

theorem sym1119_c1_mem_A (h45 : Sec4.Item4_5) (h113 : Item113) (h117 : Item117)
    (h : Sec11Data G A c L a R Y d x s r g) (hs : Subgroup.zpowers s = Subgroup.zpowers c)
    (hgV : g ∈ Subgroup.normalizer
      ((Subgroup.closure ({s, x, a} : Set G) : Subgroup G) : Set G))
    (hord : orderOf x = 27) : (x ^ 3)⁻¹ * g⁻¹ * x ^ 3 * g ∈ A := by
  have hgA : g ∈ Subgroup.normalizer (A : Set G) := (h.g_mem).2
  have hgW : g ∈ Subgroup.normalizer ((sym1119W0 A x : Subgroup G) : Set G) :=
    sym1119_g_norm_W0 h45 h hs hgA hgV
  have hyW : x ^ 3 ∈ sym1119W0 A x := sym1119_y_mem_W0 A x
  have hz : g⁻¹ * x ^ 3 * g ∈ sym1119W0 A x := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgW) (x ^ 3)).mp hyW
    simpa using this
  have hW : (x ^ 3)⁻¹ * (g⁻¹ * x ^ 3 * g) ∈ sym1119W0 A x :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ hyW) hz
  obtain ⟨i, u, hu, he⟩ := (sym1119_mem_W0_iff h45 h).mp hW
  have hd9 : x ^ 9 ∈ Subgroup.zpowers d := by
    rw [sym1119_zpowers_d_eq h hord]
    exact Subgroup.mem_zpowers _
  refine sym1119_comm_cube_mem hord (fun u hu => Item1117Proof.pow_three_of_mem_A h hu)
    (sym1119_A_comm_y h45 h) (Subgroup.zpowers_le.mpr (Item1117Proof.d_mem_A h) hd9)
    (Item1119Proof.commute_of_mem_zpowers_d h113 h117 h hd9 (Item1119Proof.g_mem_P R g))
    ⟨i, u, hu, he⟩

theorem sym1119_c1_not_mem_zpowers_x9 (hStep : Step1119Comm)
    (hbig : Sec11Big G A c L a R Y d x s r g) :
    (x ^ 3)⁻¹ * g⁻¹ * x ^ 3 * g ∉ Subgroup.zpowers (x ^ 9) := by
  obtain ⟨v, hv, -, -, w, hw, hvw⟩ := hStep G A c L a R Y d x s r g hbig
  intro hmem
  apply hv
  have h9 : x ^ 9 ∈ Subgroup.closure ({x ^ 9, v ^ 3} : Set G) :=
    Subgroup.subset_closure (by simp)
  have hle : Subgroup.zpowers (x ^ 9) ≤ Subgroup.closure ({x ^ 9, v ^ 3} : Set G) :=
    Subgroup.zpowers_le.mpr h9
  have hv' : v = ((x ^ 3)⁻¹ * g⁻¹ * x ^ 3 * g) * w⁻¹ := by
    rw [hvw]; group
  have hmem' : ((x ^ 3)⁻¹ * g⁻¹ * x ^ 3 * g) * w⁻¹ ∈
      Subgroup.closure ({x ^ 9, v ^ 3} : Set G) :=
    Subgroup.mul_mem _ (hle hmem) (Subgroup.inv_mem _ hw)
  rwa [← hv'] at hmem'

theorem sym1119YAlphaComm_of (h45 : Sec4.Item4_5) (h113 : Item113) (h117 : Item117)
    (h1120 : Item1120) (hStep : Step1119Comm) (hSplit : Sym1119YAlphaSplit)
    (hNum : Sym1119Numbers) (hL3 : Sym1119NotLThree) : Sym1119YAlphaComm := by
  intro G _ _ A c L a R Y d x s r g hctx
  have h := hctx.big.toSec11Data
  obtain ⟨hord, -⟩ := sym1119_numbers_all h45 hNum hL3 hctx
  obtain ⟨hcard, -⟩ := hSplit G A c L a R Y d x s r g hctx
  have hgV : g ∈ Subgroup.normalizer
      ((Subgroup.closure ({s, x, a} : Set G) : Subgroup G) : Set G) :=
    h1120 G A c L a R Y d x s r g hctx.big (Item1119Proof.g_mem_P R g)
  have hdA : d ∈ A := Item1117Proof.d_mem_A h
  have hdY : d ∈ Y := h.sec11K_le (h.toSec11Std.d_mem_sec11K h.inf_eq)
  have hyY : x ^ 3 ∈ Y := Item1119Proof.x_cube_mem_Y h45 h
  have hgY : g ∈ Y := (h.g_mem).1
  have hc1A := sym1119_c1_mem_A h45 h113 h117 h hctx.s_eq_c hgV hord
  have hc1Y : (x ^ 3)⁻¹ * g⁻¹ * x ^ 3 * g ∈ Y :=
    Y.mul_mem (Y.mul_mem (Y.mul_mem (Y.inv_mem hyY) (Y.inv_mem hgY)) hyY) hgY
  have hdB : d ∈ A ⊓ (Y ⊔ sym1119Theta a) := Subgroup.mem_inf.mpr ⟨hdA, Subgroup.mem_sup_left hdY⟩
  have hc1B : (x ^ 3)⁻¹ * g⁻¹ * x ^ 3 * g ∈ A ⊓ (Y ⊔ sym1119Theta a) :=
    Subgroup.mem_inf.mpr ⟨hc1A, Subgroup.mem_sup_left hc1Y⟩
  have hc1d : (x ^ 3)⁻¹ * g⁻¹ * x ^ 3 * g ∉ Subgroup.zpowers d := by
    rw [sym1119_zpowers_d_eq h hord]
    exact sym1119_c1_not_mem_zpowers_x9 hStep hctx.big
  have hxa3 : x ^ 3 * a = a * x ^ 3 := (sym1119_A_comm_y h45 h a h.a_mem).symm
  have hyQ : x ^ 3 ∈ sym1119Q R g a :=
    ⟨Item1119Proof.R_le_P R g (Subgroup.pow_mem _ (sym1119_x_mem_R h) 3),
      Subgroup.mem_centralizer_singleton_iff.mpr hxa3⟩
  have hgQ : g ∈ sym1119Q R g a :=
    ⟨Item1119Proof.g_mem_P R g,
      Subgroup.mem_centralizer_singleton_iff.mpr (sym1119_g_comm_a h)⟩
  have hcQ : c ∈ sym1119Q R g a :=
    ⟨sym1119_A_le_P h h.mem_A,
      Subgroup.mem_centralizer_singleton_iff.mpr
        (Item1117Proof.commute_of_mem_A h h.mem_A h.a_mem)⟩
  obtain ⟨κ, hκ, hgc⟩ := sym1119_g_c_action h113 h117 h
  have hd3 : d ^ 3 = 1 := Item1117Proof.pow_three_of_mem_A h hdA
  have hgcd : ⁅g, c⁆ = d ^ κ := by
    rw [commutatorElement_def, hgc]; group
  have hdQ : d ∈ ⁅sym1119Q R g a, sym1119Q R g a⁆ := by
    have hmem : d ^ κ ∈ ⁅sym1119Q R g a, sym1119Q R g a⁆ := by
      rw [← hgcd]; exact Subgroup.commutator_mem_commutator hgQ hcQ
    exact Subgroup.zpowers_le.mpr hmem (sym1119_mem_zpowers_zpow hd3 hκ)
  have hc1Q : (x ^ 3)⁻¹ * g⁻¹ * x ^ 3 * g ∈ ⁅sym1119Q R g a, sym1119Q R g a⁆ := by
    have := Subgroup.commutator_mem_commutator (Subgroup.inv_mem _ hyQ) (Subgroup.inv_mem _ hgQ)
    simpa [commutatorElement_def] using this
  exact sym1119_le_of_two_gens hcard hdB hc1B (Item1117Proof.orderOf_d h) hc1d hdQ hc1Q

end Facts

end CFSG.RankThree.PartTwo.Sec11

end
