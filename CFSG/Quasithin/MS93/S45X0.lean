module

public import CFSG.Quasithin.MS93.S45K

public section

namespace CFSG.Quasithin.MS93.S45

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix

section Comm

variable {𝔾 : Type} [Group 𝔾]

@[expose] def commIn (H W N : Subgroup 𝔾) (hHN : H ≤ Subgroup.normalizer (N : Set 𝔾)) :
    Subgroup 𝔾 where
  carrier := {g | g ∈ H ∧ ∀ w ∈ W, ⁅g, w⁆ ∈ N}
  one_mem' := ⟨H.one_mem, fun w _ => by rw [commutatorElement_one_left]; exact N.one_mem⟩
  mul_mem' := fun {g g'} hg hg' => ⟨H.mul_mem hg.1 hg'.1, fun w hw => by
    rw [S46.commutatorElement_mul_left_conj]
    exact N.mul_mem ((Subgroup.mem_normalizer_iff.mp (hHN hg.1) _).mp (hg'.2 w hw)) (hg.2 w hw)⟩
  inv_mem' := fun {g} hg => ⟨H.inv_mem hg.1, fun w hw => by
    have h := (Subgroup.mem_normalizer_iff.mp (hHN (H.inv_mem hg.1)) _).mp
      (N.inv_mem (hg.2 w hw))
    have e : ⁅g⁻¹, w⁆ = g⁻¹ * ⁅g, w⁆⁻¹ * g⁻¹⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact h⟩

theorem mem_commIn {H W N : Subgroup 𝔾} {hHN : H ≤ Subgroup.normalizer (N : Set 𝔾)} {g : 𝔾} :
    g ∈ commIn H W N hHN ↔ g ∈ H ∧ ∀ w ∈ W, ⁅g, w⁆ ∈ N := Iff.rfl

theorem commutator_conjCl_le {H A W N : Subgroup 𝔾} (hHN : H ≤ Subgroup.normalizer (N : Set 𝔾))
    (hAH : A ≤ H) (hA : ∀ g ∈ H, ⁅A.map (MulAut.conj g).toMonoidHom, W⁆ ≤ N) :
    ⁅conjCl H A, W⁆ ≤ N := by
  have hle : conjCl H A ≤ commIn H W N hHN := iSup₂_le fun g hg x hx =>
    mem_commIn.mpr ⟨S4A.conjCl_le_of_le hAH (le_iSup₂_of_le (f := fun g (_ : g ∈ H) =>
      A.map (MulAut.conj g).toMonoidHom) g hg le_rfl hx),
      fun w hw => hA g hg (Subgroup.commutator_mem_commutator hx hw)⟩
  rw [Subgroup.commutator_le]
  intro x hx w hw
  exact (mem_commIn.mp (hle hx)).2 w hw

theorem commutator_conjCl_conjCl_le {H A N : Subgroup 𝔾}
    (hHN : H ≤ Subgroup.normalizer (N : Set 𝔾)) (hAH : A ≤ H)
    (hA : ∀ k ∈ H, ⁅A, A.map (MulAut.conj k).toMonoidHom⁆ ≤ N) :
    ⁅conjCl H A, conjCl H A⁆ ≤ N := by
  refine commutator_conjCl_le hHN hAH fun g hg => ?_
  rw [Subgroup.commutator_comm]
  refine commutator_conjCl_le hHN hAH fun g' hg' => ?_
  have e : ⁅A.map (MulAut.conj g').toMonoidHom, A.map (MulAut.conj g).toMonoidHom⁆ =
      (⁅A, A.map (MulAut.conj (g'⁻¹ * g)).toMonoidHom⁆).map (MulAut.conj g').toMonoidHom := by
    rw [Subgroup.map_commutator, Subgroup.map_map]
    congr 2
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  rw [e]
  refine (Subgroup.map_mono (hA _ (H.mul_mem (H.inv_mem hg') hg))).trans ?_
  exact (map_conj_eq_of_mem_normalizer (hHN hg')).le

end Comm

section Sq

variable {𝔾 : Type} [Group 𝔾]

@[expose] def sqSub' (W Z : Subgroup 𝔾) (hWW : ⁅W, W⁆ ≤ Z)
    (hZ : W ≤ Subgroup.normalizer (Z : Set 𝔾)) : Subgroup 𝔾 where
  carrier := {x | x ∈ W ∧ x ^ 2 ∈ Z}
  one_mem' := ⟨W.one_mem, by rw [one_pow]; exact Z.one_mem⟩
  mul_mem' := fun {x y} hx hy => by
    refine ⟨W.mul_mem hx.1 hy.1, ?_⟩
    have hc : ⁅y, x⁆ ∈ Z := hWW (Subgroup.commutator_mem_commutator hy.1 hx.1)
    have hc' : x * ⁅y, x⁆ * x⁻¹ ∈ Z := (Subgroup.mem_normalizer_iff.mp (hZ hx.1) _).mp hc
    have e : (x * y) ^ 2 = (x * ⁅y, x⁆ * x⁻¹) * x ^ 2 * y ^ 2 := by
      rw [sq, sq, sq, commutatorElement_def]; group
    rw [e]
    exact Z.mul_mem (Z.mul_mem hc' hx.2) hy.2
  inv_mem' := fun {x} hx => ⟨W.inv_mem hx.1, by rw [inv_pow]; exact Z.inv_mem hx.2⟩

theorem le_sqSub' {W Z A : Subgroup 𝔾} {hWW : ⁅W, W⁆ ≤ Z}
    {hZ : W ≤ Subgroup.normalizer (Z : Set 𝔾)} (hAW : A ≤ W) (hA : ∀ a ∈ A, a ^ 2 ∈ Z) :
    A ≤ sqSub' W Z hWW hZ := fun a ha => ⟨hAW ha, hA a ha⟩

end Sq

section Count

variable {F : Type} [Field F]

theorem card_le_of_mulVec_sub_mem [Finite F] {H P : Submodule F (Fin 3 → F)}
    (hH : Module.finrank F H = 2) (S : Set (SL3 F))
    (hfix : ∀ g ∈ S, ∀ h ∈ H, ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ h = h)
    (hP : ∀ g ∈ S, ∀ v, ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v - v ∈ P) :
    Nat.card S ≤ Nat.card P := by
  have hHtop : H ≠ ⊤ := by
    intro htop
    rw [htop, finrank_top, Module.finrank_fin_fun] at hH
    omega
  obtain ⟨e, -, heH⟩ := IsConcreteLE.exists_of_lt (lt_top_iff_ne_top.mpr hHtop)
  have hsup := sup_span_eq_top hH heH
  let f : S → P := fun g =>
    ⟨((g.1 : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ e - e, hP g.1 g.2 e⟩
  have hf : Function.Injective f := by
    intro g g' hgg
    have h1 : ((g.1 : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ e =
        ((g'.1 : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ e := by
      have := congrArg Subtype.val hgg
      simpa [f] using this
    have h2 : ∀ v, ((g.1 : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v =
        ((g'.1 : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v := by
      intro v
      have hv : v ∈ H ⊔ Submodule.span F {e} := by rw [hsup]; trivial
      obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hv
      obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hy
      rw [Matrix.mulVec_add, Matrix.mulVec_add, hfix g.1 g.2 x hx, hfix g'.1 g'.2 x hx,
        Matrix.mulVec_smul, Matrix.mulVec_smul, h1]
    apply Subtype.ext
    apply Subtype.ext
    exact Matrix.ext_of_mulVec_single fun i => h2 _
  have : Finite P := inferInstance
  exact Nat.card_le_card_of_injective f hf

end Count

variable {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Fintype F]

namespace Ctx

variable {M T L : Subgroup G} {φ : ↥M →* ↥(StatedSL 3 F)} (c : Ctx M T L φ)
include c

theorem whv_le_qv_of_dist {δ μ v : Vtx (puAmalgam c.hyp.le)} (hμ : IsMVtx _ μ)
    (hd : (puAmalgam c.hyp.le).treeGraph.dist δ μ = 2)
    (hv : (puAmalgam c.hyp.le).treeGraph.dist δ v ≤ 3) :
    whv c.hyp δ μ ≤ Qv (puAmalgam c.hyp.le) v :=
  (c.whv_le_vi hμ hd).trans (vi_le_qv _ (by rw [c.b8]; omega))

section GoodPath

variable {p : ℕ → Vtx (puAmalgam c.hyp.le)} {N : ℕ}

theorem commutator_vsix_le (hZV : c.HZV) (hQ4 : c.HQ4) (hp : IsGoodPath _ p N) {a : ℕ}
    (ha : Even a) (h34 : 34 ≤ a) (haN : a + 27 ≤ N) :
    ⁅conjCl (stab (puAmalgam c.hyp.le) (p a)) (whv c.hyp (p (a + 2)) (p a)),
        conjCl (stab (puAmalgam c.hyp.le) (p a)) (whv c.hyp (p (a + 2)) (p a))⁆ ≤
      whv c.hyp (p a) (p (a + 2)) := by
  have h := c.hyp
  have hα := c.isMVtx_of_isGoodPath hp (k := a) (by omega) ha
  have hγ := c.isMVtx_of_isGoodPath hp (k := a + 2) (by omega) (ha.add even_two)
  have hd2 : (puAmalgam h.le).treeGraph.dist (p a) (p (a + 2)) = 2 := by
    rw [hp.dist_eq' (by omega) (by omega)]; omega
  have hd2' : (puAmalgam h.le).treeGraph.dist (p (a + 2)) (p a) = 2 := by
    rw [tdist_comm]; exact hd2
  have hαβ : (puAmalgam h.le).treeGraph.Adj (p a) (p (a + 1)) := hp.adj a (by omega)
  have hβγ : (puAmalgam h.le).treeGraph.Adj (p (a + 1)) (p (a + 2)) := hp.adj (a + 1) (by omega)
  set Wh := whv h (p a) (p (a + 2)) with hWh
  set Wγ := whv h (p (a + 2)) (p a) with hWγ
  have hKWh : stab (puAmalgam h.le) (p a) ≤ Subgroup.normalizer (Wh : Set _) :=
    S4A.le_normalizer_conjCl _ _
  have hWγK : Wγ ≤ stab (puAmalgam h.le) (p a) :=
    (c.whv_le_qv_of_dist hα hd2' (by omega)).trans (qv_le_stab _ _)
  have hKey : ⁅Wγ, Qv (puAmalgam h.le) (p (a + 1))⁆ ≤ Wh := by
    refine (c.commutator_whv_qv_le_vhat_left hZV hQ4 hp ha h34 haN).trans (sup_le ?_ ?_)
    · exact c.vhat_le_whv' hZV hp ha (by omega) (by omega)
    · exact c.vhat_le_whv_self
  refine commutator_conjCl_conjCl_le hKWh hWγK fun k hk => ?_
  have hkα : k • p a = p a := (mem_stab _).mp hk
  have hdk : (puAmalgam h.le).treeGraph.dist (p (a + 2)) (k • p (a + 1)) ≤ 3 := by
    have h1 := dist_triangle (puAmalgam h.le) (p (a + 2)) (p a) (k • p (a + 1))
    have h2 : (puAmalgam h.le).treeGraph.dist (p a) (k • p (a + 1)) = 1 := by
      conv_lhs => rw [← hkα]
      rw [dist_smul, dist_eq_one_of_adj _ hαβ]
    omega
  have hWT : Wγ ≤ (Qv (puAmalgam h.le) (p (a + 1))).map (MulAut.conj k).toMonoidHom := by
    rw [← qv_smul]
    exact c.whv_le_qv_of_dist hα hd2' hdk
  refine (Subgroup.commutator_mono hWT le_rfl).trans ?_
  rw [← Subgroup.map_commutator, Subgroup.commutator_comm]
  exact (Subgroup.map_mono hKey).trans (map_conj_eq_of_mem_normalizer (hKWh hk)).le

end GoodPath

end Ctx

end CFSG.Quasithin.MS93.S45
