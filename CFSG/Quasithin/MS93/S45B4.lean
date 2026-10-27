module

public import CFSG.Quasithin.MS93.S45B5

public section

namespace CFSG.Quasithin.MS93.S45

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix

section Irr

variable {𝔾 : Type} [Group 𝔾] {F : Type} [Field F]

theorem le_of_commutator_eq_one {K X W A : Subgroup 𝔾} {ψ : ↥K →* ↥(StatedSL 3 F)}
    {dual : Bool} (hψs : Function.Surjective ψ) (hX : IsSumOfNaturalModulesVia K X W ψ dual 1)
    (hKA : K ≤ Subgroup.normalizer (A : Set 𝔾)) (hWA : W ≤ Subgroup.centralizer (A : Set 𝔾))
    (hne : ⁅X, A⁆ ≠ ⊥) {x : 𝔾} (hx : x ∈ X) (hxA : ∀ v ∈ A, ⁅x, v⁆ = 1) : x ∈ W := by
  by_contra hxW
  apply hne
  set C := X ⊓ Subgroup.centralizer (A : Set 𝔾) with hC
  have hxC : x ∈ C := by
    refine Subgroup.mem_inf.mpr ⟨hx, Subgroup.mem_centralizer_iff.mpr fun v hv => ?_⟩
    have := hxA v hv
    rw [commutatorElement_eq_one_iff_commute] at this
    exact this.eq.symm
  have hCK : ∀ k : ↥K, ∀ y ∈ C, (k : 𝔾) * y * (k : 𝔾)⁻¹ ∈ C := by
    intro k y hy
    obtain ⟨hyX, hyA⟩ := Subgroup.mem_inf.mp hy
    refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp (hX.1 k.2) y).mp hyX,
      Subgroup.mem_centralizer_iff.mpr fun v hv => ?_⟩
    have hv' : (k : 𝔾)⁻¹ * v * (k : 𝔾)⁻¹⁻¹ ∈ A :=
      (Subgroup.mem_normalizer_iff.mp (hKA (inv_mem k.2)) v).mp hv
    have h1 := Subgroup.mem_centralizer_iff.mp hyA _ hv'
    simp only [inv_inv] at h1
    calc v * ((k : 𝔾) * y * (k : 𝔾)⁻¹)
        = (k : 𝔾) * (((k : 𝔾)⁻¹ * v * (k : 𝔾)) * y) * (k : 𝔾)⁻¹ := by group
      _ = (k : 𝔾) * (y * ((k : 𝔾)⁻¹ * v * (k : 𝔾))) * (k : 𝔾)⁻¹ := by rw [h1]
      _ = (k : 𝔾) * y * (k : 𝔾)⁻¹ * v := by group
  have hXC : X ≤ C := by
    intro v hv
    obtain ⟨w, hwC, -, hwv⟩ := (NatSec.ofIsSum hX).exists_inv_mul_mem_of_invariant hψs hCK hxC hx
      hxW hv
    have hWC : W ≤ C := le_inf hX.2.1 hWA
    have e : v = w * (w⁻¹ * v) := by group
    rw [e]
    exact C.mul_mem hwC (hWC hwv)
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  exact hXC.trans inf_le_right

end Irr

variable {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Fintype F]

namespace Ctx

variable {M T L : Subgroup G} {φ : ↥M →* ↥(StatedSL 3 F)} (c : Ctx M T L φ)
include c

theorem commute_of_mem_stabCenter {δ : Vtx (puAmalgam c.hyp.le)}
    {r g : (puAmalgam c.hyp.le).Universal} (hr : r ∈ stabCenter (puAmalgam c.hyp.le) δ)
    (hg : g ∈ stab (puAmalgam c.hyp.le) δ) : g * r = r * g := by
  obtain ⟨r', hr', rfl⟩ := hr
  exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hr' ⟨g, hg⟩)

theorem stab_le_normalizer_of_le_stabCenter {δ : Vtx (puAmalgam c.hyp.le)}
    {R : Subgroup (puAmalgam c.hyp.le).Universal} (hR : R ≤ stabCenter (puAmalgam c.hyp.le) δ) :
    stab (puAmalgam c.hyp.le) δ ≤ Subgroup.normalizer (R : Set _) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro r
  constructor
  · intro hr
    rw [c.commute_of_mem_stabCenter (hR hr) hg, mul_inv_cancel_right]
    exact hr
  · intro hr
    have e := c.commute_of_mem_stabCenter (hR hr) (inv_mem hg)
    simp only [← mul_assoc, inv_mul_cancel, one_mul] at e
    rw [mul_right_cancel e]
    exact hr

theorem commutator_conjCl_sup_vhat_le {α γ μ : Vtx (puAmalgam c.hyp.le)} (hα : IsMVtx _ α)
    (hγ : IsMVtx _ γ) (hd : (puAmalgam c.hyp.le).treeGraph.dist α γ = 2)
    (hμs : Vcirc c.hyp.le L μ ⊔ ZM _ μ ≤ stab (puAmalgam c.hyp.le) α)
    {R : Subgroup (puAmalgam c.hyp.le).Universal}
    (hKR : stab (puAmalgam c.hyp.le) α ≤ Subgroup.normalizer (R : Set _))
    (hμ : ⁅Vcirc c.hyp.le L μ ⊔ ZM _ μ, Vcirc c.hyp.le L α ⊔ ZM _ α⁆ ≤ R) :
    ⁅conjCl (stab (puAmalgam c.hyp.le) α) (Vcirc c.hyp.le L μ ⊔ ZM _ μ) ⊔ whv c.hyp α γ,
      Vcirc c.hyp.le L α ⊔ ZM _ α⁆ ≤ R := by
  have h := c.hyp
  have hVn : stab (puAmalgam h.le) α ≤
      Subgroup.normalizer ((Vcirc h.le L α ⊔ ZM _ α : Subgroup _) : Set _) :=
    le_normalizer_sup (c.stab_le_normalizer_vcirc _) (stab_le_normalizer_zm _ _)
  have hWs : whv h α γ ≤ stab (puAmalgam h.le) α :=
    (c.whv_le_qv_of_dist hγ hd (by simp)).trans (qv_le_stab _ _)
  refine commutator_sup_left_le ((S4A.conjCl_le_of_le hμs).trans hKR) (hWs.trans hKR) ?_ ?_
  · refine commutator_conjCl_le hKR hμs fun g hg => ?_
    rw [← map_conj_eq_of_mem_normalizer (hVn hg), ← Subgroup.map_commutator]
    exact (Subgroup.map_mono hμ).trans (map_conj_eq_of_mem_normalizer (hKR hg)).le
  · rw [(Subgroup.commutator_eq_bot_iff_le_centralizer).mpr]
    · exact bot_le
    · exact (c.whv_le_centralizer_vv hγ hd).trans (Subgroup.centralizer_le (c.vhat_le_vv hα))

section GoodPath

variable {p p' : ℕ → Vtx (puAmalgam c.hyp.le)} {N : ℕ}

theorem inf_centralizer_vcirc_le_whv (h14 : MS14AS) (hSQ : SQTKQuot) (hZV : c.HZV)
    (hQ4 : c.HQ4) (hp : IsGoodPath _ p N) (hp' : IsGoodPath _ p' N) {a : ℕ} (ha : Even a)
    (h34 : 34 ≤ a) (haN : a + 30 ≤ N) (hpp' : ∀ i, i ≤ a + 2 → p' i = p i)
    (hU1 : Usup (puAmalgam c.hyp.le) (p (a + 2)) (p' (a + 3)) ≠ Usup _ (p (a + 2)) (p (a + 1)))
    (hU3 : Usup (puAmalgam c.hyp.le) (p (a + 2)) (p' (a + 3)) ⊓ Usup _ (p (a + 2)) (p (a + 1)) ≠
      Usup _ (p (a + 2)) (p (a + 3)) ⊓ Usup _ (p (a + 2)) (p (a + 1))) :
    ⁅Qv (puAmalgam c.hyp.le) (p a), Ltil c.hyp.le L (p a)⁆ ⊓
        Subgroup.centralizer (Vcirc c.hyp.le L (p a) : Set (puAmalgam c.hyp.le).Universal) ≤
      whv c.hyp (p a) (p (a + 2)) := by
  have h := c.hyp
  have h20 := h.hyp20
  have hα := c.isMVtx_of_isGoodPath hp (k := a) (by omega) ha
  have hγ := c.isMVtx_of_isGoodPath hp (k := a + 2) (by omega) (ha.add even_two)
  have hμ := c.isMVtx_of_isGoodPath hp (k := a + 4) (by omega) (ha.add (by decide))
  have hμ' := c.isMVtx_of_isGoodPath hp' (k := a + 4) (by omega) (ha.add (by decide))
  have ha2 : Even (a - 2) := (Nat.even_sub (by omega)).mpr (iff_of_true ha (by decide))
  have hpa : p' a = p a := hpp' a (by omega)
  have hpa1 : p' (a + 1) = p (a + 1) := hpp' (a + 1) (by omega)
  have hpa2 : p' (a + 2) = p (a + 2) := hpp' (a + 2) le_rfl
  have hpam : p' (a - 2) = p (a - 2) := hpp' (a - 2) (by omega)
  have hd2 : (puAmalgam h.le).treeGraph.dist (p a) (p (a + 2)) = 2 := by
    rw [hp.dist_eq' (i := a) (j := a + 2) (by omega) (by omega)]; omega
  obtain ⟨ψ, hψs, hψ⟩ := exists_natural_Uloc h c.via hα
  obtain ⟨-, h₁t, h₂t⟩ := c.top_layer h14 hSQ hZV hQ4 hp ha h34 haN hp' hpp' hU1 hU3 hψs hψ
  have hF7 := c.commutator_qv_ltil_le_top' hZV hQ4 hp hp' ha h34 haN hpp' hU3
  have hXQ := c.top_le_qv hp hp' ha (by omega) hpp'
  set Wh := whv h (p a) (p (a + 2)) with hWh
  set Vh := Vcirc h.le L (p a) ⊔ ZM _ (p a) with hVh
  set X₁ := conjCl (stab (puAmalgam h.le) (p a))
    (Vcirc h.le L (p (a + 4)) ⊔ ZM _ (p (a + 4))) ⊔ Wh with hX₁
  set X₂ := conjCl (stab (puAmalgam h.le) (p a))
    (Vcirc h.le L (p' (a + 4)) ⊔ ZM _ (p' (a + 4))) ⊔ Wh with hX₂
  set X₁' := ⁅X₁, stab (puAmalgam h.le) (p a)⁆ ⊔ Wh with hX₁'
  set X₂' := ⁅X₂, stab (puAmalgam h.le) (p a)⁆ ⊔ Wh with hX₂'
  have hKWh : stab (puAmalgam h.le) (p a) ≤ Subgroup.normalizer (Wh : Set _) :=
    S4A.le_normalizer_conjCl _ _
  have hKX₁ : stab (puAmalgam h.le) (p a) ≤ Subgroup.normalizer (X₁ : Set _) :=
    le_normalizer_sup (S4A.le_normalizer_conjCl _ _) hKWh
  have hKX₂ : stab (puAmalgam h.le) (p a) ≤ Subgroup.normalizer (X₂ : Set _) :=
    le_normalizer_sup (S4A.le_normalizer_conjCl _ _) hKWh
  have hX₁'X₁ : X₁' ≤ X₁ :=
    sup_le (Subgroup.le_normalizer_iff_commutator_le_left.mp hKX₁) le_sup_right
  have hX₂'X₂ : X₂' ≤ X₂ :=
    sup_le (Subgroup.le_normalizer_iff_commutator_le_left.mp hKX₂) le_sup_right
  have hX₁s : X₁ ≤ stab (puAmalgam h.le) (p a) := (le_sup_left.trans hXQ).trans (qv_le_stab _ _)
  have hX₂s : X₂ ≤ stab (puAmalgam h.le) (p a) := (le_sup_right.trans hXQ).trans (qv_le_stab _ _)
  have hKVh : stab (puAmalgam h.le) (p a) ≤ Subgroup.normalizer (Vh : Set _) :=
    le_normalizer_sup (c.stab_le_normalizer_vcirc _) (stab_le_normalizer_zm _ _)
  have hWhC : Wh ≤ Subgroup.centralizer (Vh : Set _) :=
    (c.whv_le_centralizer_vv hγ hd2).trans (Subgroup.centralizer_le (c.vhat_le_vv hα))
  have hvv₁ := c.commutator_vv_vv hp (x := a) ha (by omega) (by omega)
  have hvv₂ := c.commutator_vv_vv hp' (x := a) ha (by omega) (by omega)
  rw [hpa, hpam] at hvv₂
  set R₁ := critR (puAmalgam h.le) (p (a - 2)) (p (a + 6)) with hR₁
  set R₂ := critR (puAmalgam h.le) (p (a - 2)) (p' (a + 6)) with hR₂
  have hHc : Hloc h.le L (p a) ≤ stabCenter (puAmalgam h.le) (p a) :=
    (Subgroup.commutator_mono (c.vcirc_le_vv _) le_rfl).trans
      (c.commutator_vv_qv_le_stabCenter hα)
  have hR₁c : R₁ ≤ stabCenter (puAmalgam h.le) (p a) := hvv₁.2 ▸ inf_le_left.trans hHc
  have hR₂c : R₂ ≤ stabCenter (puAmalgam h.le) (p a) := by
    rw [← hvv₂.2]; exact inf_le_left.trans hHc
  have hP₁ : ⁅X₁', Vh⁆ ≤ R₁ := (Subgroup.commutator_mono hX₁'X₁ le_rfl).trans
    (c.commutator_conjCl_sup_vhat_le hα hγ hd2 ((S4A.le_conjCl _ _).trans
      (le_sup_left.trans hX₁s)) (c.stab_le_normalizer_of_le_stabCenter hR₁c)
      ((Subgroup.commutator_mono (c.vhat_le_vv hμ) (c.vhat_le_vv hα)).trans
        (by rw [Subgroup.commutator_comm, hvv₁.1])))
  have hP₂ : ⁅X₂', Vh⁆ ≤ R₂ := (Subgroup.commutator_mono hX₂'X₂ le_rfl).trans
    (c.commutator_conjCl_sup_vhat_le hα hγ hd2 ((S4A.le_conjCl _ _).trans
      (le_sup_left.trans hX₂s)) (c.stab_le_normalizer_of_le_stabCenter hR₂c)
      ((Subgroup.commutator_mono (c.vhat_le_vv hμ') (c.vhat_le_vv hα)).trans
        (by rw [Subgroup.commutator_comm, hvv₂.1])))
  have hRR : R₁ ⊓ R₂ = ⊥ := by
    have e₁ := c.critR_eq_usup_inf hp (x := a - 2) ha2 (by omega) (by omega)
    have e₂ := c.critR_eq_usup_inf hp' (x := a - 2) ha2 (by omega) (by omega)
    rw [show a - 2 + 8 = a + 6 by omega, show a - 2 + 4 = a + 2 by omega,
      show a - 2 + 3 = a + 1 by omega, show a - 2 + 5 = a + 3 by omega] at e₁ e₂
    rw [hpam, hpa2, hpa1] at e₂
    have hadj1 : (puAmalgam h.le).treeGraph.Adj (p (a + 2)) (p (a + 1)) :=
      (hp.adj (a + 1) (by omega)).symm
    have hadj3 : (puAmalgam h.le).treeGraph.Adj (p (a + 2)) (p (a + 3)) := hp.adj (a + 2) (by omega)
    have hadj3' : (puAmalgam h.le).treeGraph.Adj (p (a + 2)) (p' (a + 3)) := by
      have := hp'.adj (a + 2) (by omega)
      rwa [hpa2] at this
    obtain ⟨ψγ, -, hψγ⟩ := exists_natural_Uloc h c.via hγ
    have h13 : Usup (puAmalgam h.le) (p (a + 2)) (p (a + 1)) ≠ Usup _ (p (a + 2)) (p (a + 3)) := by
      rw [Ne, c.usup_eq_iff_zh_eq hψγ hγ hadj1 hadj3]
      have := c.zh_ne_of_isGoodPath hp (y := a + 2) (ha.add even_two) (by omega) (by omega)
      rwa [show a + 2 - 1 = a + 1 by omega, show a + 2 + 1 = a + 3 by omega] at this
    have hb := c.usup_inf_inf_eq_bot hγ hadj1 hadj3 hadj3' h13 (Ne.symm hU1) hU3
    rw [eq_bot_iff, ← hb, hR₁, hR₂, e₁, e₂]
    exact le_inf (le_inf (inf_le_left.trans inf_le_left) (inf_le_left.trans inf_le_right))
      (inf_le_right.trans inf_le_right)
  have hne₁ : ⁅X₁', Vh⁆ ≠ ⊥ := c.commutator_top'_ne_bot h14 hSQ hZV hQ4 hp ha h34 haN
  have hne₂ : ⁅X₂', Vh⁆ ≠ ⊥ := by
    have := c.commutator_top'_ne_bot h14 hSQ hZV hQ4 hp' ha h34 haN
    rwa [hpa, hpa2] at this
  have hC₁ : ∀ x ∈ X₁', (∀ v ∈ Vh, ⁅x, v⁆ = 1) → x ∈ Wh := fun x hx hxv =>
    le_of_commutator_eq_one hψs h₁t hKVh hWhC hne₁ hx hxv
  have hC₂ : ∀ x ∈ X₂', (∀ v ∈ Vh, ⁅x, v⁆ = 1) → x ∈ Wh := fun x hx hxv =>
    le_of_commutator_eq_one hψs h₂t hKVh hWhC hne₂ hx hxv
  intro x hx
  obtain ⟨hxV, hxC⟩ := Subgroup.mem_inf.mp hx
  have hxQ : x ∈ Qv (puAmalgam h.le) (p a) :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp
      ((ltil_le_stab h _).trans (stab_le_normalizer_qv _ _)) hxV
  have hxVh : ∀ v ∈ Vh, ⁅x, v⁆ = 1 := by
    have hle : Vh ≤ Subgroup.centralizer ({x} : Set _) := by
      refine sup_le (fun v hv => ?_) (fun z hz => ?_)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact Subgroup.mem_centralizer_iff.mp hxC v hv
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact Subgroup.mem_centralizer_iff.mp (zm_le_centralizer_qv _ h20 hα hz) x hxQ |>.symm
    intro v hv
    rw [commutatorElement_eq_one_iff_commute]
    exact ((Subgroup.mem_centralizer_singleton_iff.mp (hle hv))).symm
  have hxX : x ∈ X₁' ⊔ X₂' := hF7 hxV
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right X₁' X₂'
    ((hX₁'X₁.trans hX₁s).trans (le_normalizer_sup (S45.le_normalizer_commutator hKX₂
      Subgroup.le_normalizer) hKWh))] at hxX
  obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := hxX
  have hx₁s : x₁ ∈ stab (puAmalgam h.le) (p a) := hX₁s (hX₁'X₁ hx₁)
  have key : ∀ v ∈ Vh, ⁅x₁, v⁆ = 1 ∧ ⁅x₂, v⁆ = 1 := by
    intro v hv
    have h1 := hxVh v hv
    have hr₂ : ⁅x₂, v⁆ ∈ R₂ := hP₂ (Subgroup.commutator_mem_commutator hx₂ hv)
    have hr₁ : ⁅x₁, v⁆ ∈ R₁ := hP₁ (Subgroup.commutator_mem_commutator hx₁ hv)
    rw [S46.commutatorElement_mul_left_conj, c.commute_of_mem_stabCenter (hR₂c hr₂) hx₁s,
      mul_inv_cancel_right] at h1
    have e₁ : ⁅x₁, v⁆ = ⁅x₂, v⁆⁻¹ := eq_inv_of_mul_eq_one_right h1
    have hm : ⁅x₁, v⁆ ∈ R₁ ⊓ R₂ := Subgroup.mem_inf.mpr ⟨hr₁, by rw [e₁]; exact inv_mem hr₂⟩
    rw [hRR, Subgroup.mem_bot] at hm
    refine ⟨hm, ?_⟩
    rw [hm, eq_comm, inv_eq_one] at e₁
    exact e₁
  exact mul_mem (hC₁ x₁ hx₁ fun v hv => (key v hv).1) (hC₂ x₂ hx₂ fun v hv => (key v hv).2)

end GoodPath

end Ctx

end CFSG.Quasithin.MS93.S45
