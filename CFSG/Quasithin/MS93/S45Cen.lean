module

public import CFSG.Quasithin.MS93.S45B4

public section

namespace CFSG.Quasithin.MS93.S45

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix

section Abelian

variable {𝔾 : Type} [Group 𝔾]

theorem commutator_conjCl_sup_eq_bot {H A B : Subgroup 𝔾} (hAH : A ≤ H)
    (hA : ∀ k ∈ H, ⁅A, A.map (MulAut.conj k).toMonoidHom⁆ = ⊥)
    (hB : ⁅B, B⁆ = ⊥) (hAB : ⁅conjCl H A, B⁆ = ⊥) :
    ⁅conjCl H A ⊔ B, conjCl H A ⊔ B⁆ = ⊥ := by
  have hn : ∀ K : Subgroup 𝔾, K ≤ Subgroup.normalizer ((⊥ : Subgroup 𝔾) : Set 𝔾) :=
    fun K g _ => Subgroup.mem_normalizer_iff.mpr fun x => by simp
  have hCC : ⁅conjCl H A, conjCl H A⁆ = ⊥ := le_bot_iff.mp
    (commutator_conjCl_conjCl_le (hn H) hAH fun k hk => (hA k hk).le)
  rw [eq_bot_iff]
  refine commutator_sup_left_le (hn _) (hn _) ?_ ?_
  · rw [Subgroup.commutator_comm]
    refine commutator_sup_left_le (hn _) (hn _) ?_ ?_
    · rw [hCC]
    · rw [Subgroup.commutator_comm, hAB]
  · rw [Subgroup.commutator_comm]
    refine commutator_sup_left_le (hn _) (hn _) ?_ ?_
    · rw [hAB]
    · rw [hB]

end Abelian

variable {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Fintype F]

namespace Ctx

variable {M T L : Subgroup G} {φ : ↥M →* ↥(StatedSL 3 F)} (c : Ctx M T L φ)
include c

section GoodPath

variable {p p' : ℕ → Vtx (puAmalgam c.hyp.le)} {N : ℕ}

theorem sup_whv_eq (hZV : c.HZV) (hQ4 : c.HQ4) (hp : IsGoodPath _ p N)
    (hp' : IsGoodPath _ p' N) {a : ℕ} (ha : Even a) (h34 : 34 ≤ a) (haN : a + 30 ≤ N)
    (hpp' : ∀ i, i ≤ a + 2 → p' i = p i)
    (hU3 : Usup (puAmalgam c.hyp.le) (p (a + 2)) (p' (a + 3)) ⊓ Usup _ (p (a + 2)) (p (a + 1)) ≠
      Usup _ (p (a + 2)) (p (a + 3)) ⊓ Usup _ (p (a + 2)) (p (a + 1))) :
    ⁅Qv (puAmalgam c.hyp.le) (p a), Ltil c.hyp.le L (p a)⁆ ⊔ whv c.hyp (p a) (p (a + 2)) =
      (⁅conjCl (stab (puAmalgam c.hyp.le) (p a))
          (Vcirc c.hyp.le L (p (a + 4)) ⊔ ZM _ (p (a + 4))) ⊔ whv c.hyp (p a) (p (a + 2)),
          stab (puAmalgam c.hyp.le) (p a)⁆ ⊔ whv c.hyp (p a) (p (a + 2))) ⊔
        (⁅conjCl (stab (puAmalgam c.hyp.le) (p a))
          (Vcirc c.hyp.le L (p' (a + 4)) ⊔ ZM _ (p' (a + 4))) ⊔ whv c.hyp (p a) (p (a + 2)),
          stab (puAmalgam c.hyp.le) (p a)⁆ ⊔ whv c.hyp (p a) (p (a + 2))) := by
  have h := c.hyp
  have hα := c.isMVtx_of_isGoodPath hp (k := a) (by omega) ha
  have hpa : p' a = p a := hpp' a (by omega)
  have hpa2 : p' (a + 2) = p (a + 2) := hpp' (a + 2) le_rfl
  have hF7 := c.commutator_qv_ltil_le_top' hZV hQ4 hp hp' ha h34 haN hpp' hU3
  have hXQ := c.top_le_qv hp hp' ha (by omega) hpp'
  set Qα := Qv (puAmalgam h.le) (p a) with hQα
  set Lt := Ltil h.le L (p a) with hLt
  set V := ⁅Qα, Lt⁆ with hV
  set Wh := whv h (p a) (p (a + 2)) with hWh
  have hQs : Qα ≤ stab (puAmalgam h.le) (p a) := qv_le_stab _ _
  have hLs : Lt ≤ stab (puAmalgam h.le) (p a) := ltil_le_stab h _
  have hKQ : stab (puAmalgam h.le) (p a) ≤ Subgroup.normalizer (Qα : Set _) :=
    stab_le_normalizer_qv _ _
  have hKL : stab (puAmalgam h.le) (p a) ≤ Subgroup.normalizer (Lt : Set _) :=
    stab_le_normalizer_ltil h _
  have hKV : stab (puAmalgam h.le) (p a) ≤ Subgroup.normalizer (V : Set _) :=
    le_normalizer_commutator hKQ hKL
  have hKWh : stab (puAmalgam h.le) (p a) ≤ Subgroup.normalizer (Wh : Set _) :=
    S4A.le_normalizer_conjCl _ _
  have hKVW : stab (puAmalgam h.le) (p a) ≤
      Subgroup.normalizer ((V ⊔ Wh : Subgroup _) : Set _) := le_normalizer_sup hKV hKWh
  have hstab : stab (puAmalgam h.le) (p a) = Lt ⊔ Qα := stab_eq_ltil_sup_qv h c.full hα
  have hC1₁ := c.commutator_top_qv_le hZV hQ4 hp ha h34 (by omega)
  have hC1₂ := c.commutator_top_qv_le hZV hQ4 hp' ha h34 (by omega)
  rw [hpa, hpa2] at hC1₂
  have hXi : ∀ X : Subgroup (puAmalgam h.le).Universal, X ≤ Qα → ⁅X, Qα⁆ ≤ Wh →
      ⁅X, stab (puAmalgam h.le) (p a)⁆ ⊔ Wh ≤ V ⊔ Wh := by
    intro X hXQ hXW
    refine sup_le ?_ le_sup_right
    refine (Subgroup.commutator_mono le_rfl hstab.le).trans ?_
    rw [Subgroup.commutator_comm]
    refine S46.commutator_sup_le_of_le_normalizer hKVW hLs hQs ?_ ?_
    · rw [Subgroup.commutator_comm]
      exact (Subgroup.commutator_mono hXQ le_rfl).trans le_sup_left
    · rw [Subgroup.commutator_comm]
      exact hXW.trans le_sup_right
  exact le_antisymm (sup_le hF7 (le_sup_right.trans le_sup_left))
    (sup_le (hXi _ (le_sup_left.trans hXQ) hC1₁) (hXi _ (le_sup_right.trans hXQ) hC1₂))

theorem inf_whv_sup_vhat (h14 : MS14AS) (hSQ : SQTKQuot) (hZV : c.HZV) (hQ4 : c.HQ4)
    (hp : IsGoodPath _ p N) (hp' : IsGoodPath _ p' N) {a : ℕ} (ha : Even a) (h34 : 34 ≤ a)
    (haN : a + 30 ≤ N) (hpp' : ∀ i, i ≤ a + 2 → p' i = p i)
    (hU1 : Usup (puAmalgam c.hyp.le) (p (a + 2)) (p' (a + 3)) ≠ Usup _ (p (a + 2)) (p (a + 1)))
    (hU3 : Usup (puAmalgam c.hyp.le) (p (a + 2)) (p' (a + 3)) ⊓ Usup _ (p (a + 2)) (p (a + 1)) ≠
      Usup _ (p (a + 2)) (p (a + 3)) ⊓ Usup _ (p (a + 2)) (p (a + 1))) :
    (⁅Qv (puAmalgam c.hyp.le) (p a), Ltil c.hyp.le L (p a)⁆ ⊓ whv c.hyp (p a) (p (a + 2))) ⊔
      (Vcirc c.hyp.le L (p a) ⊔ ZM _ (p a)) = whv c.hyp (p a) (p (a + 2)) := by
  have h := c.hyp
  have hα := c.isMVtx_of_isGoodPath hp (k := a) (by omega) ha
  obtain ⟨ψ, hψs, hψ, hT⟩ := c.exists_coord_qv hα (hp.adj a (by omega))
  obtain ⟨hsup2, -, h₁m, h₂m⟩ :=
    c.mid_layer h14 hSQ hZV hQ4 hp ha (by omega) (by omega) hp' hpp' hU1 hU3 hψs hψ hT
  have hKQ : stab (puAmalgam h.le) (p a) ≤
      Subgroup.normalizer (Qv (puAmalgam h.le) (p a) : Set _) := stab_le_normalizer_qv _ _
  have hKV : stab (puAmalgam h.le) (p a) ≤ Subgroup.normalizer
      ((⁅Qv (puAmalgam h.le) (p a), Ltil h.le L (p a)⁆ : Subgroup _) : Set _) :=
    le_normalizer_commutator hKQ (stab_le_normalizer_ltil h _)
  have hWhQ : whv h (p a) (p (a + 2)) ≤ Qv (puAmalgam h.le) (p a) :=
    c.whv_le_qv_of_dist (c.isMVtx_of_isGoodPath hp (k := a + 2) (by omega) (ha.add even_two))
      (by rw [hp.dist_eq' (i := a) (j := a + 2) (by omega) (by omega)]; omega) (by simp)
  have hVhWh := c.vhat_le_whv' hZV hp ha (by omega) (by omega)
  refine le_antisymm (sup_le inf_le_right hVhWh) ?_
  refine (show whv h (p a) (p (a + 2)) ≤ _ from hsup2.symm.le).trans (sup_le ?_ ?_)
  · rw [← c.sup_inf_eq_of_dual hα hψs hψ h₁m hKV (Subgroup.commutator_mono
      ((le_sup_left.trans hsup2.le).trans hWhQ) le_rfl)]
    exact sup_le_sup_right (inf_le_inf_left _ (le_sup_left.trans hsup2.le)) _
  · rw [← c.sup_inf_eq_of_dual hα hψs hψ h₂m hKV (Subgroup.commutator_mono
      ((le_sup_right.trans hsup2.le).trans hWhQ) le_rfl)]
    exact sup_le_sup_right (inf_le_inf_left _ (le_sup_right.trans hsup2.le)) _

theorem center_whv_le_vhat (h14 : MS14AS) (hSQ : SQTKQuot) (hZV : c.HZV) (hQ4 : c.HQ4)
    (hp : IsGoodPath _ p N) (hp' : IsGoodPath _ p' N) {a : ℕ} (ha : Even a) (h34 : 34 ≤ a)
    (haN : a + 30 ≤ N) (hpp' : ∀ i, i ≤ a + 2 → p' i = p i)
    (hU1 : Usup (puAmalgam c.hyp.le) (p (a + 2)) (p' (a + 3)) ≠ Usup _ (p (a + 2)) (p (a + 1)))
    (hU3 : Usup (puAmalgam c.hyp.le) (p (a + 2)) (p' (a + 3)) ⊓ Usup _ (p (a + 2)) (p (a + 1)) ≠
      Usup _ (p (a + 2)) (p (a + 3)) ⊓ Usup _ (p (a + 2)) (p (a + 1))) :
    whv c.hyp (p a) (p (a + 2)) ⊓
        Subgroup.centralizer (whv c.hyp (p a) (p (a + 2)) : Set (puAmalgam c.hyp.le).Universal) ≤
      Vcirc c.hyp.le L (p a) ⊔ ZM _ (p a) := by
  have h := c.hyp
  have h20 := h.hyp20
  have hα := c.isMVtx_of_isGoodPath hp (k := a) (by omega) ha
  have hγ := c.isMVtx_of_isGoodPath hp (k := a + 2) (by omega) (ha.add even_two)
  have hμ := c.isMVtx_of_isGoodPath hp (k := a + 4) (by omega) (ha.add (by decide))
  have hμ' := c.isMVtx_of_isGoodPath hp' (k := a + 4) (by omega) (ha.add (by decide))
  have hpa : p' a = p a := hpp' a (by omega)
  have hd2 : (puAmalgam h.le).treeGraph.dist (p a) (p (a + 2)) = 2 := by
    rw [hp.dist_eq' (i := a) (j := a + 2) (by omega) (by omega)]; omega
  obtain ⟨ψ, hψs, hψ, hT⟩ := c.exists_coord_qv hα (hp.adj a (by omega))
  obtain ⟨hsup2, hinf2, h₁m, h₂m⟩ :=
    c.mid_layer h14 hSQ hZV hQ4 hp ha (by omega) (by omega) hp' hpp' hU1 hU3 hψs hψ hT
  set Vh := Vcirc h.le L (p a) ⊔ ZM (puAmalgam h.le) (p a) with hVh
  set Wh := whv h (p a) (p (a + 2)) with hWh
  set W₁ := conjCl (stab (puAmalgam h.le) (p a)) (ZM _ (p (a + 4))) ⊔ Vh with hW₁
  set W₂ := conjCl (stab (puAmalgam h.le) (p a)) (ZM _ (p' (a + 4))) ⊔ Vh with hW₂
  have hWhC : Wh ≤ Subgroup.centralizer (Vh : Set _) :=
    (c.whv_le_centralizer_vv hγ hd2).trans (Subgroup.centralizer_le (c.vhat_le_vv hα))
  have hVhWh : Vh ≤ Wh := c.vhat_le_whv' hZV hp ha (by omega) (by omega)
  have hVhab : ⁅Vh, Vh⁆ = ⊥ :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer).mpr (hVhWh.trans hWhC)
  have hW₁Wh : W₁ ≤ Wh := le_sup_left.trans hsup2.le
  have hW₂Wh : W₂ ≤ Wh := le_sup_right.trans hsup2.le
  have hWhs : Wh ≤ stab (puAmalgam h.le) (p a) :=
    (c.whv_le_qv_of_dist hγ hd2 (by simp)).trans (qv_le_stab _ _)
  have hKW₁ : stab (puAmalgam h.le) (p a) ≤ Subgroup.normalizer (W₁ : Set _) := h₁m.1
  have hKW₂ : stab (puAmalgam h.le) (p a) ≤ Subgroup.normalizer (W₂ : Set _) := h₂m.1
  have hZQ4 : ∀ k ∈ stab (puAmalgam h.le) (p a),
      ⁅ZM (puAmalgam h.le) (p (a + 4)),
        (ZM (puAmalgam h.le) (p (a + 4))).map (MulAut.conj k).toMonoidHom⁆ = ⊥ := by
    intro k hk
    rw [← zm_smul, Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact (zm_le_centralizer_qv _ h20 hμ).trans
      (Subgroup.centralizer_le (hQ4 p N hp a ha (by omega) (by omega) k hk))
  have hZQ4' : ∀ k ∈ stab (puAmalgam h.le) (p a),
      ⁅ZM (puAmalgam h.le) (p' (a + 4)),
        (ZM (puAmalgam h.le) (p' (a + 4))).map (MulAut.conj k).toMonoidHom⁆ = ⊥ := by
    intro k hk
    rw [← zm_smul, Subgroup.commutator_eq_bot_iff_le_centralizer]
    have hk' : k ∈ stab (puAmalgam h.le) (p' a) := by rw [hpa]; exact hk
    exact (zm_le_centralizer_qv _ h20 hμ').trans
      (Subgroup.centralizer_le (hQ4 p' N hp' a ha (by omega) (by omega) k hk'))
  have hpa2 : p' (a + 2) = p (a + 2) := hpp' (a + 2) le_rfl
  have hZ₁W : ZM (puAmalgam h.le) (p (a + 4)) ≤ Wh :=
    c.zm_le_whv_right hZV hp ha (by omega) (by omega)
  have hZ₂W : ZM (puAmalgam h.le) (p' (a + 4)) ≤ Wh := by
    have := c.zm_le_whv_right hZV hp' ha (by omega) (by omega)
    rwa [hpa, hpa2] at this
  have hab₁ : ⁅W₁, W₁⁆ = ⊥ := commutator_conjCl_sup_eq_bot (hZ₁W.trans hWhs) hZQ4 hVhab
    ((Subgroup.commutator_eq_bot_iff_le_centralizer).mpr ((le_sup_left.trans hW₁Wh).trans hWhC))
  have hab₂ : ⁅W₂, W₂⁆ = ⊥ := commutator_conjCl_sup_eq_bot (hZ₂W.trans hWhs) hZQ4' hVhab
    ((Subgroup.commutator_eq_bot_iff_le_centralizer).mpr ((le_sup_left.trans hW₂Wh).trans hWhC))
  have hZ₄W : ZM (puAmalgam h.le) (p (a - 4)) ≤ Wh := by
    have ha2 : Even (a - 2) := (Nat.even_sub (by omega)).mpr (iff_of_true ha (by decide))
    have hz := c.zm_le_vhat_left' hZV hp (a := a - 2) ha2 (by omega) (by omega)
    rw [show a - 2 - 2 = a - 4 by omega] at hz
    have e := c.whv_eq_of_isGoodPath hp (a := a) ha (by omega) (by omega)
    rw [hWh, e]
    exact hz.trans c.vhat_le_whv_self
  have hR : ⁅ZM (puAmalgam h.le) (p (a - 4)), ZM _ (p (a + 4))⁆ ≠ ⊥ := by
    have := c.critR_ne_bot_of_isGoodPath hp (a := a - 2)
      ((Nat.even_sub (by omega)).mpr (iff_of_true ha (by decide))) (by omega) (by omega)
    rwa [show a - 2 - 2 = a - 4 by omega, show a - 2 + 6 = a + 4 by omega] at this
  have hne : ⁅W₂, W₁⁆ ≠ ⊥ := by
    intro h0
    apply hR
    have hWab : ⁅Wh, Wh⁆ = ⊥ := by
      rw [← hsup2, eq_bot_iff]
      have hn : ∀ K : Subgroup (puAmalgam h.le).Universal,
          K ≤ Subgroup.normalizer ((⊥ : Subgroup (puAmalgam h.le).Universal) : Set _) :=
        fun K g _ => Subgroup.mem_normalizer_iff.mpr fun x => by simp
      refine commutator_sup_left_le (hn _) (hn _) ?_ ?_
      · rw [Subgroup.commutator_comm]
        refine commutator_sup_left_le (hn _) (hn _) ?_ ?_
        · rw [hab₁]
        · rw [h0]
      · rw [Subgroup.commutator_comm]
        refine commutator_sup_left_le (hn _) (hn _) ?_ ?_
        · rw [Subgroup.commutator_comm, h0]
        · rw [hab₂]
    exact le_bot_iff.mp ((Subgroup.commutator_mono hZ₄W hZ₁W).trans hWab.le)
  have hne' : ⁅W₁, W₂⁆ ≠ ⊥ := by rw [Subgroup.commutator_comm]; exact hne
  have hVhC₁ : Vh ≤ Subgroup.centralizer (W₁ : Set _) := Subgroup.le_centralizer_iff.mp
    (hW₁Wh.trans hWhC)
  have hVhC₂ : Vh ≤ Subgroup.centralizer (W₂ : Set _) := Subgroup.le_centralizer_iff.mp
    (hW₂Wh.trans hWhC)
  intro x hx
  obtain ⟨hxW, hxC⟩ := Subgroup.mem_inf.mp hx
  have hxW' : x ∈ W₁ ⊔ W₂ := hsup2 ▸ hxW
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right W₁ W₂
    ((hW₁Wh.trans hWhs).trans hKW₂)] at hxW'
  obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := hxW'
  have hc₁ : ∀ y ∈ W₁, x₁ * y = y * x₁ := fun y hy =>
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hab₁ hx₁ |>
      Subgroup.mem_centralizer_iff.mp) y hy |>.symm
  have hc₂ : ∀ y ∈ W₂, x₂ * y = y * x₂ := fun y hy =>
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hab₂ hx₂ |>
      Subgroup.mem_centralizer_iff.mp) y hy |>.symm
  have hxc : ∀ y ∈ Wh, x₁ * x₂ * y = y * (x₁ * x₂) := fun y hy =>
    (Subgroup.mem_centralizer_iff.mp hxC y hy).symm
  have hx₂V : x₂ ∈ Vh := by
    refine le_of_commutator_eq_one hψs h₂m hKW₁ hVhC₁ hne hx₂ fun y hy => ?_
    rw [commutatorElement_eq_one_iff_commute]
    have e1 := hxc y (hW₁Wh hy)
    have e2 := hc₁ y hy
    show x₂ * y = y * x₂
    have : x₁ * (x₂ * y) = x₁ * (y * x₂) := by
      rw [← mul_assoc, e1, ← mul_assoc, ← e2, mul_assoc]
    exact mul_left_cancel this
  have hx₁V : x₁ ∈ Vh := by
    refine le_of_commutator_eq_one hψs h₁m hKW₂ hVhC₂ hne' hx₁ fun y hy => ?_
    rw [commutatorElement_eq_one_iff_commute]
    have e1 := hxc y (hW₂Wh hy)
    have e2 := hc₂ y hy
    show x₁ * y = y * x₁
    have : x₁ * y * x₂ = y * x₁ * x₂ := by
      rw [mul_assoc, ← e2, ← mul_assoc, e1, mul_assoc]
    exact mul_right_cancel this
  exact Vh.mul_mem hx₁V hx₂V

theorem center_le_zm (h14 : MS14AS) (hSQ : SQTKQuot) (hZV : c.HZV) (hQ4 : c.HQ4)
    (hp : IsGoodPath _ p N) (hp' : IsGoodPath _ p' N) {a : ℕ} (ha : Even a) (h34 : 34 ≤ a)
    (haN : a + 30 ≤ N) (hpp' : ∀ i, i ≤ a + 2 → p' i = p i)
    (hU1 : Usup (puAmalgam c.hyp.le) (p (a + 2)) (p' (a + 3)) ≠ Usup _ (p (a + 2)) (p (a + 1)))
    (hU3 : Usup (puAmalgam c.hyp.le) (p (a + 2)) (p' (a + 3)) ⊓ Usup _ (p (a + 2)) (p (a + 1)) ≠
      Usup _ (p (a + 2)) (p (a + 3)) ⊓ Usup _ (p (a + 2)) (p (a + 1))) :
    centerOf ⁅Qv (puAmalgam c.hyp.le) (p a), Ltil c.hyp.le L (p a)⁆ ≤ ZM _ (p a) := by
  have h := c.hyp
  have h20 := h.hyp20
  obtain ⟨k, rfl⟩ : ∃ k, a = k + 34 := ⟨a - 34, by omega⟩
  have hk : Even k := (Nat.even_add.mp ha).mpr (by decide)
  have hα := c.isMVtx_of_isGoodPath hp (k := k + 34) (by omega) ha
  have hγ := c.isMVtx_of_isGoodPath hp (k := k + 34 + 2) (by omega) (ha.add even_two)
  have hd2 : (puAmalgam h.le).treeGraph.dist (p (k + 34)) (p (k + 34 + 2)) = 2 := by
    rw [hp.dist_eq' (i := k + 34) (j := k + 34 + 2) (by omega) (by omega)]; omega
  obtain ⟨ψ, hψs, hψ⟩ := exists_natural_Uloc h c.via hα
  obtain ⟨d, hd⟩ := c.exists_isSum_vhat hα hψs hψ
  have hdB := c.isSum_bloc hα hd
  have hdt := c.dual_eq_true hp (x := k + 28) (hk.add (by decide)) (by omega) (by omega) hψs hψ hdB
  subst hdt
  have hB4 := c.inf_centralizer_vcirc_le_whv h14 hSQ hZV hQ4 hp hp' ha h34 haN hpp' hU1 hU3
  have hF8 := c.sup_whv_eq hZV hQ4 hp hp' ha h34 haN hpp' hU3
  have hF9 := c.inf_whv_sup_vhat h14 hSQ hZV hQ4 hp hp' ha h34 haN hpp' hU1 hU3
  have hZW := c.center_whv_le_vhat h14 hSQ hZV hQ4 hp hp' ha h34 haN hpp' hU1 hU3
  have hne₁ := c.commutator_top'_ne_bot h14 hSQ hZV hQ4 hp ha h34 haN
  obtain ⟨-, h₁t, -⟩ := c.top_layer h14 hSQ hZV hQ4 hp ha h34 haN hp' hpp' hU1 hU3 hψs hψ
  have hXQ := c.top_le_qv hp hp' ha (by omega) hpp'
  set Qα := Qv (puAmalgam h.le) (p (k + 34)) with hQα
  set Lt := Ltil h.le L (p (k + 34)) with hLt
  set V := ⁅Qα, Lt⁆ with hV
  set Vh := Vcirc h.le L (p (k + 34)) ⊔ ZM (puAmalgam h.le) (p (k + 34)) with hVh
  set Wh := whv h (p (k + 34)) (p (k + 34 + 2)) with hWh
  have hQs : Qα ≤ stab (puAmalgam h.le) (p (k + 34)) := qv_le_stab _ _
  have hKQ : stab (puAmalgam h.le) (p (k + 34)) ≤ Subgroup.normalizer (Qα : Set _) :=
    stab_le_normalizer_qv _ _
  have hLs : Lt ≤ stab (puAmalgam h.le) (p (k + 34)) := ltil_le_stab h _
  have hVQ : V ≤ Qα := Subgroup.le_normalizer_iff_commutator_le_left.mp (hLs.trans hKQ)
  have hKWh : stab (puAmalgam h.le) (p (k + 34)) ≤ Subgroup.normalizer (Wh : Set _) :=
    S4A.le_normalizer_conjCl _ _
  have hWhC : Wh ≤ Subgroup.centralizer (Vh : Set _) :=
    (c.whv_le_centralizer_vv hγ hd2).trans (Subgroup.centralizer_le (c.vhat_le_vv hα))
  have hVcV : Vcirc h.le L (p (k + 34)) ≤ V :=
    Subgroup.commutator_mono (c.vv_le_qv' hα) le_rfl
  intro z hz
  obtain ⟨hzV, hzC⟩ := Subgroup.mem_inf.mp hz
  have hzW : z ∈ Wh := hB4 (Subgroup.mem_inf.mpr ⟨hzV, Subgroup.centralizer_le hVcV hzC⟩)
  have hWz : Wh ≤ Subgroup.centralizer ({z} : Set (puAmalgam h.le).Universal) := by
    rw [← hF9]
    refine sup_le (fun v hv => ?_) (fun u hu => ?_)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.mp hzC v (Subgroup.mem_inf.mp hv).1
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.mp (hWhC hzW) u hu
  have hzVh : z ∈ Vh := hZW (Subgroup.mem_inf.mpr ⟨hzW, Subgroup.mem_centralizer_iff.mpr
    fun w hw => (Subgroup.mem_centralizer_singleton_iff.mp (hWz hw))⟩)
  have hZX : ZM (puAmalgam h.le) (p (k + 34)) ≤ Subgroup.centralizer
      ((⁅conjCl (stab (puAmalgam h.le) (p (k + 34)))
          (Vcirc h.le L (p (k + 34 + 4)) ⊔ ZM _ (p (k + 34 + 4))) ⊔ Wh,
          stab (puAmalgam h.le) (p (k + 34))⁆ ⊔ Wh : Subgroup _) : Set _) := by
    refine (zm_le_centralizer_qv _ h20 hα).trans (Subgroup.centralizer_le ?_)
    refine sup_le ?_ ((le_sup_right.trans le_sup_left).trans hXQ)
    exact (Subgroup.le_normalizer_iff_commutator_le_left.mp
      (le_normalizer_sup (S4A.le_normalizer_conjCl _ _) hKWh)).trans (le_sup_left.trans hXQ)
  refine le_of_commutator_eq_one hψs hd h₁t.1 hZX (by rw [Subgroup.commutator_comm]; exact hne₁)
    hzVh fun x hx => ?_
  have hxVW : x ∈ V ⊔ Wh := hF8 ▸ Subgroup.mem_sup_left hx
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right V Wh
    ((hVQ.trans hQs).trans hKWh)] at hxVW
  obtain ⟨v, hv, w, hw, rfl⟩ := hxVW
  rw [S46.commutatorElement_mul_right_conj, commutatorElement_eq_one_iff_commute.mpr
    (Subgroup.mem_centralizer_iff.mp hzC v hv).symm, one_mul,
    commutatorElement_eq_one_iff_commute.mpr (Subgroup.mem_centralizer_iff.mp (hWhC hw) z hzVh),
    mul_one, mul_inv_cancel]

end GoodPath

end Ctx

end CFSG.Quasithin.MS93.S45
