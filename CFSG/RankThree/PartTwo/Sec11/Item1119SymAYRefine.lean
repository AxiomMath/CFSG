module

public import CFSG.RankThree.PartTwo.Sec11.Item1119SymAY
public import CFSG.RankThree.PartTwo.Sec11.Item1119SymLines

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.GH74.GLS (oResidual)

section Facts


variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
  {R Y : Subgroup G} {d x s r g : G}

theorem sym1119_normalizer_sup {Y Θ : Subgroup G} {t : G}
    (hY : t ∈ Subgroup.normalizer (Y : Set G)) (hΘ : t ∈ Subgroup.normalizer (Θ : Set G)) :
    t ∈ Subgroup.normalizer ((Y ⊔ Θ : Subgroup G) : Set G) := by
  refine Subgroup.mem_normalizer_fintype fun w hw => ?_
  rw [Subgroup.sup_eq_closure] at hw ⊢
  refine Item1119Sym.conj_mem_closure_of_gens ((Y : Set G) ∪ (Θ : Set G))
    (Subgroup.closure ((Y : Set G) ∪ (Θ : Set G))) t ?_ hw
  rintro u (hu | hu)
  · exact Subgroup.subset_closure (Or.inl ((Subgroup.mem_normalizer_iff.mp hY u).mp hu))
  · exact Subgroup.subset_closure (Or.inr ((Subgroup.mem_normalizer_iff.mp hΘ u).mp hu))

theorem sym1119_Q_le_closure (h45 : Sec4.Item4_5) (h113 : Item113) (h117 : Item117)
    (h : Sec11Data G A c L a R Y d x s r g) (hra : r * a = a * r)
    (hs : Subgroup.zpowers s = Subgroup.zpowers c) :
    sym1119Q R g a ≤ Subgroup.closure ({r, x ^ 3, c, g} : Set G) := by
  intro z hz
  obtain ⟨hzP, hzC⟩ := hz
  obtain ⟨m, hm, hxa⟩ := sym1119_x_a_action h45 h
  obtain ⟨hxc, hxd⟩ := sym1119_x_comm h45 h
  have hdA : d ∈ A := Item1117Proof.d_mem_A h
  have hd3 : d ^ 3 = 1 := Item1117Proof.pow_three_of_mem_A h hdA
  have hd1 : d ≠ 1 := sym1119_d_ne_one h
  have had : a * d = d * a := Item1117Proof.commute_of_mem_A h h.a_mem hdA
  have hca : c * a = a * c := Item1117Proof.commute_of_mem_A h h.mem_A h.a_mem
  obtain ⟨u, huR, j, rfl⟩ := Item1119Sym.mem_sup_zpowers_form R g h.g_mem_normalizer hzP
  have hza : (u * g ^ j) * a = a * (u * g ^ j) := Subgroup.mem_centralizer_singleton_iff.mp hzC
  have hga : g * a = a * g := sym1119_g_comm_a h
  have hgja : g ^ j * a = a * g ^ j := ((show Commute g a from hga).zpow_left j).eq
  have hua : u * a = a * u := by
    have h1 : (u * a) * g ^ j = (a * u) * g ^ j := by
      calc (u * a) * g ^ j = u * (a * g ^ j) := by rw [mul_assoc]
        _ = u * (g ^ j * a) := by rw [hgja]
        _ = (u * g ^ j) * a := by rw [mul_assoc]
        _ = a * (u * g ^ j) := hza
        _ = (a * u) * g ^ j := by rw [mul_assoc]
    exact mul_right_cancel h1
  have hrR := sym1119_r_mem_R h
  have hscl : s ∈ Subgroup.zpowers c := hs ▸ Subgroup.mem_zpowers s
  have hRle : R ≤ Subgroup.closure ({r, x, c} : Set G) := by
    rw [h.R_eq]
    refine (Subgroup.closure_le _).mpr ?_
    rintro y (rfl | rfl | rfl)
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp)) hscl
  have hux : r * x * r⁻¹ ∈ Subgroup.zpowers x :=
    (Subgroup.mem_normalizer_iff.mp (Item1115Proof.mem_normalizer_zpowers_x h45 h hrR) x).mp
      (Subgroup.mem_zpowers x)
  have hux' : r⁻¹ * x * r ∈ Subgroup.zpowers x := by
    have := (Subgroup.mem_normalizer_iff.mp
      (Item1115Proof.mem_normalizer_zpowers_x h45 h (R.inv_mem hrR)) x).mp (Subgroup.mem_zpowers x)
    simpa using this
  obtain ⟨j', i, l, hu⟩ := Item1119Sym.commute_a_triple_form r x c a d m
    (sym1119_R_comm_c h r hrR).symm hxc.symm hca hux hux' hra hxa hxd had hd3 hd1 hm
    (hRle huR) hua
  rw [hu]
  refine Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ?_ ?_) ?_) ?_
  · exact Subgroup.zpow_mem _ (Subgroup.subset_closure (by simp)) _
  · exact Subgroup.zpow_mem _ (Subgroup.subset_closure (by simp)) _
  · exact Subgroup.zpow_mem _ (Subgroup.subset_closure (by simp)) _
  · exact Subgroup.zpow_mem _ (Subgroup.subset_closure (by simp)) _

theorem sym1119_comm_Q_le (h45 : Sec4.Item4_5) (h113 : Item113) (h117 : Item117)
    (h : Sec11Data G A c L a R Y d x s r g) (hra : r * a = a * r)
    (hs : Subgroup.zpowers s = Subgroup.zpowers c) (hord : orderOf x = 27)
    {f : G} (hf : f ∈ Subgroup.closure ({a, c} : Set G)) (hfc : f ∉ Subgroup.zpowers c)
    (hr3 : r ^ 3 = f) :
    ⁅sym1119Q R g a, sym1119Q R g a⁆ ≤ Y ⊔ sym1119Theta a := by
  have hQ := sym1119_Q_le_closure h45 h113 h117 h hra hs
  refine le_trans (Subgroup.commutator_mono hQ hQ) ?_
  obtain ⟨κ, hκ, hgc⟩ := sym1119_g_c_action h113 h117 h
  obtain ⟨hrx, hyr, hyr1⟩ := sym1119_yr_facts h45 h113 h117 h hord hf hfc hr3
  obtain ⟨hxc, hxd⟩ := sym1119_x_comm h45 h
  have hdA : d ∈ A := Item1117Proof.d_mem_A h
  have hdY : d ∈ Y := h.sec11K_le (h.toSec11Std.d_mem_sec11K h.inf_eq)
  have hyY : x ^ 3 ∈ Y := Item1119Proof.x_cube_mem_Y h45 h
  have hgY : g ∈ Y := (h.g_mem).1
  have hzdY : Subgroup.zpowers d ≤ Y := Subgroup.zpowers_le.mpr hdY
  have hga : g * a = a * g := sym1119_g_comm_a h
  have hAY : A ≤ Subgroup.normalizer (Y : Set G) :=
    Sec6.le_normalizer_of_mem_thetaComponentsAt h45 h.toTheoremFourHyp h.mem_partTwoF.1 h.a_mem
      h.a_ne_one Y h.mem_thetaComponentsAt_Y
  have hK1 : sec11K L a ≠ ⊥ := fun hbot => sym1119_d_ne_one h (by
    have := h.toSec11Std.d_mem_sec11K h.inf_eq
    rw [hbot] at this
    simpa using this)
  have hrL : r ∈ Subgroup.normalizer (L : Set G) :=
    (Item1116Proof.le_centralizer_and_normalizer h45 h).2 (sym1119_r_mem_R h)
  have hrNY : r ∈ Subgroup.normalizer (Y : Set G) := h.toSec11Std.mem_normalizer_Y hK1 hrL hra
  have hΘ : ∀ t : G, t * a = a * t →
      t ∈ Subgroup.normalizer ((sym1119Theta a : Subgroup G) : Set G) := fun t ht =>
    centralizer_le_normalizer_sym1119Theta a (Subgroup.mem_centralizer_singleton_iff.mpr ht)
  have hca : c * a = a * c := Item1117Proof.commute_of_mem_A h h.mem_A h.a_mem
  have hxa3 : x ^ 3 * a = a * x ^ 3 := (sym1119_A_comm_y h45 h a h.a_mem).symm
  have hYW : Y ≤ Y ⊔ sym1119Theta a := le_sup_left
  have hnorm : ∀ t ∈ ({r, x ^ 3, c, g} : Set G),
      t ∈ Subgroup.normalizer ((Y ⊔ sym1119Theta a : Subgroup G) : Set G) := by
    intro t ht
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
    rcases ht with ht | ht | ht | ht <;> rw [ht]
    · exact sym1119_normalizer_sup hrNY (hΘ r hra)
    · exact Subgroup.le_normalizer (hYW hyY)
    · exact sym1119_normalizer_sup (hAY h.mem_A) (hΘ c hca)
    · exact Subgroup.le_normalizer (hYW hgY)
  have hrc := sym1119_R_comm_c h r (sym1119_r_mem_R h)
  have hry : r * x ^ 3 * r⁻¹ * (x ^ 3)⁻¹ ∈ Y ⊔ sym1119Theta a := by
    refine sym1119_comm_symm ?_
    exact hYW (hzdY hyr)
  have hrc1 : r * c * r⁻¹ * c⁻¹ ∈ Y ⊔ sym1119Theta a := by
    have : r * c * r⁻¹ * c⁻¹ = 1 := by rw [hrc]; group
    rw [this]; exact Subgroup.one_mem _
  have hrg : r * g * r⁻¹ * g⁻¹ ∈ Y ⊔ sym1119Theta a := by
    refine hYW (Y.mul_mem ?_ (Y.inv_mem hgY))
    exact (Subgroup.mem_normalizer_iff.mp hrNY g).mp hgY
  have hyc : x ^ 3 * c * (x ^ 3)⁻¹ * c⁻¹ ∈ Y ⊔ sym1119Theta a := by
    have h3 : x ^ 3 * c = c * x ^ 3 := (((show Commute x c from hxc).pow_left 3).eq)
    have : x ^ 3 * c * (x ^ 3)⁻¹ * c⁻¹ = 1 := by rw [h3]; group
    rw [this]; exact Subgroup.one_mem _
  have hyg : x ^ 3 * g * (x ^ 3)⁻¹ * g⁻¹ ∈ Y ⊔ sym1119Theta a :=
    hYW (Y.mul_mem (Y.mul_mem (Y.mul_mem hyY hgY) (Y.inv_mem hyY)) (Y.inv_mem hgY))
  have hcg : c * g * c⁻¹ * g⁻¹ ∈ Y ⊔ sym1119Theta a := by
    have e1 : g * c * g⁻¹ * c⁻¹ = d ^ κ := by rw [hgc]; group
    have e : c * g * c⁻¹ * g⁻¹ = (g * c * g⁻¹ * c⁻¹)⁻¹ := by group
    rw [e, e1]
    exact hYW (Y.inv_mem (Y.zpow_mem hdY κ))
  refine commutator_closure_le (T := ({r, x ^ 3, c, g} : Set G)) (V := Y ⊔ sym1119Theta a)
    ((Subgroup.closure_le _).mpr hnorm) ?_
  intro u hu v hv
  rw [commutatorElement_def]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu hv
  rcases hu with hu | hu | hu | hu <;> rcases hv with hv | hv | hv | hv <;> rw [hu, hv]
  · exact sym1119_comm_self _ _
  · exact hry
  · exact hrc1
  · exact hrg
  · exact sym1119_comm_symm hry
  · exact sym1119_comm_self _ _
  · exact hyc
  · exact hyg
  · exact sym1119_comm_symm hrc1
  · exact sym1119_comm_symm hyc
  · exact sym1119_comm_self _ _
  · exact hcg
  · exact sym1119_comm_symm hrg
  · exact sym1119_comm_symm hyg
  · exact sym1119_comm_symm hcg
  · exact sym1119_comm_self _ _
theorem sym1119CommLe_holds (h45 : Sec4.Item4_5) (h113 : Item113) (h117 : Item117)
    (hNum : Sym1119Numbers) (hL3 : Sym1119NotLThree) : Sym1119CommLe := by
  intro G _ _ A c L a R Y d x s r g hctx
  have h := hctx.big.toSec11Data
  obtain ⟨hord, f, hf, hfc, hr3⟩ := sym1119_numbers_all h45 hNum hL3 hctx
  exact sym1119_comm_Q_le h45 h113 h117 h hctx.r_comm hctx.s_eq_c hord hf hfc hr3

theorem step1119AY_holds (h45 : Sec4.Item4_5) (h113 : Item113) (h117 : Item117)
    (hNum : Sym1119Numbers) (hL3 : Sym1119NotLThree) (hSplit : Sym1119YAlphaSplit)
    (hComm : Sym1119YAlphaComm) : Step1119AY :=
  step1119AY_of_yalpha h45 hSplit hComm (sym1119CommLe_holds h45 h113 h117 hNum hL3)


end Facts

end CFSG.RankThree.PartTwo.Sec11

end
