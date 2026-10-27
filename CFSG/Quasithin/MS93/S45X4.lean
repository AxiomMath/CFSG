module

public import CFSG.Quasithin.MS93.S45X3

public section

namespace CFSG.Quasithin.MS93.S45

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Fintype F]

namespace Ctx

variable {M T L : Subgroup G} {φ : ↥M →* ↥(StatedSL 3 F)} (c : Ctx M T L φ)
include c

section GoodPath

variable {p : ℕ → Vtx (puAmalgam c.hyp.le)} {N : ℕ}

theorem commutator_top'_ne_bot (h14 : MS14AS) (hSQ : SQTKQuot) (hZV : c.HZV) (hQ4 : c.HQ4)
    (hp : IsGoodPath _ p N) {a : ℕ} (ha : Even a) (h34 : 34 ≤ a) (haN : a + 30 ≤ N) :
    ⁅⁅conjCl (stab (puAmalgam c.hyp.le) (p a)) (Vcirc c.hyp.le L (p (a + 4)) ⊔ ZM _ (p (a + 4))) ⊔
          whv c.hyp (p a) (p (a + 2)), stab (puAmalgam c.hyp.le) (p a)⁆ ⊔
        whv c.hyp (p a) (p (a + 2)), Vcirc c.hyp.le L (p a) ⊔ ZM _ (p a)⁆ ≠ ⊥ := by
  have h := c.hyp
  have h20 := h.hyp20
  have hα := c.isMVtx_of_isGoodPath hp (k := a) (by omega) ha
  have hγ := c.isMVtx_of_isGoodPath hp (k := a + 2) (by omega) (ha.add even_two)
  have hμ := c.isMVtx_of_isGoodPath hp (k := a + 4) (by omega) (ha.add (by decide))
  set Wh := whv h (p a) (p (a + 2)) with hWh
  set X := conjCl (stab (puAmalgam h.le) (p a)) (Vcirc h.le L (p (a + 4)) ⊔ ZM _ (p (a + 4))) ⊔
    Wh with hX
  have hC1 := c.commutator_top_qv_le hZV hQ4 hp ha h34 (by omega)
  rw [← hX] at hC1
  have hXV := c.commutator_top_vv_le hp ha (by omega) (by omega)
  rw [← hX] at hXV
  obtain ⟨-, C, hCle, hCX, hCG, hsupC, -, -⟩ := c.isC1_top h14 hSQ hZV hQ4 hp ha h34 haN
  rw [← hWh, ← hX] at hCle hCX hCG hsupC
  rw [sup_eq_right.mpr hC1] at hCG
  have hQs : Qv (puAmalgam h.le) (p a) ≤ stab (puAmalgam h.le) (p a) := qv_le_stab _ _
  have hQn : stab (puAmalgam h.le) (p a) ≤
      Subgroup.normalizer (Qv (puAmalgam h.le) (p a) : Set _) := stab_le_normalizer_qv _ _
  have hWhn : stab (puAmalgam h.le) (p a) ≤ Subgroup.normalizer (Wh : Set _) :=
    S4A.le_normalizer_conjCl _ _
  have hXQ : X ≤ Qv (puAmalgam h.le) (p a) := by
    refine sup_le (conjCl_le_of_le_normalizer ((c.vhat_le_vv hμ).trans (vi_le_qv _ ?_)) hQn)
      (conjCl_le_of_le_normalizer ((c.vhat_le_vv hγ).trans (vi_le_qv _ ?_)) hQn)
    · rw [tdist_comm, hp.dist_eq' (i := a) (j := a + 4) (by omega) (by omega), c.b8]; omega
    · rw [tdist_comm, hp.dist_eq' (i := a) (j := a + 2) (by omega) (by omega), c.b8]; omega
  have hXn : stab (puAmalgam h.le) (p a) ≤ Subgroup.normalizer (X : Set _) :=
    le_normalizer_sup (S4A.le_normalizer_conjCl _ _) hWhn
  have hX'X : ⁅X, stab (puAmalgam h.le) (p a)⁆ ⊔ Wh ≤ X :=
    sup_le (Subgroup.le_normalizer_iff_commutator_le_left.mp hXn) le_sup_right
  have ha2 : Even (a - 2) := (Nat.even_sub (by omega)).mpr (iff_of_true ha (by decide))
  have hc2 := c.isCritical_of_isGoodPath hp ha2 (show a - 2 + 8 ≤ N by omega)
  rw [show a - 2 + 8 = a + 6 by omega] at hc2
  have hg2 : geo (puAmalgam h.le) (p (a - 2)) (p (a + 6)) 2 = p a := by
    rw [hp.eq_geo (i := a - 2) (j := a + 6) (k := a) (by omega) (by omega) (by omega),
      show a - (a - 2) = 2 by omega]
  have hRZ : critR (puAmalgam h.le) (p (a - 2)) (p (a + 6)) ≤ Zloc h.le L (p a) := by
    have := c.critR_le_zloc hc2
    rwa [hg2] at this
  have hCV : ∀ x ∈ C, ∀ u ∈ Vcirc h.le L (p a) ⊔ ZM _ (p a), x * u = u * x :=
    fun x hx => c.commute_vhat_of_comm hp ha (by omega) (hXQ (hCX hx))
      (fun v hv => hRZ (hXV (Subgroup.commutator_mem_commutator (hCX hx) hv)))
      (fun l hl => hCG (Subgroup.commutator_mem_commutator hx (ltil_le_stab h _ hl)))
  intro hbot
  apply c.critR_ne_bot_of_isGoodPath hp ha (by omega) (by omega)
  rw [eq_bot_iff, critR, Subgroup.commutator_le]
  intro z hz x hx
  have hμ6 : ZM (puAmalgam h.le) (p (a + 6)) ≤ X := by
    have := c.zm_le_vhat_right hZV hp (a := a + 4) (ha.add (by decide)) (by omega) (by omega)
    rw [show a + 4 + 2 = a + 6 by omega] at this
    exact (this.trans (S4A.le_conjCl _ _)).trans le_sup_left
  have hzV : z ∈ Vcirc h.le L (p a) ⊔ ZM _ (p a) :=
    c.zm_le_vhat_left' hZV hp ha (by omega) (by omega) hz
  have hxX := hμ6 hx
  rw [← hsupC] at hxX
  have hCn : ⁅X, stab (puAmalgam h.le) (p a)⁆ ⊔ Wh ≤ Subgroup.normalizer (C : Set _) :=
    (hX'X.trans (hXQ.trans hQs)).trans (Subgroup.le_normalizer_iff_commutator_le_left.mpr
      (hCG.trans (le_sup_right.trans hCle)))
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hCn] at hxX
  obtain ⟨x', hx', c', hc', rfl⟩ := hxX
  rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_commute]
  have h1 : x' * z = z * x' := by
    have := (Subgroup.commutator_le.mp hbot.le) x' hx' z hzV
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_commute] at this
    exact this
  have h2 : c' * z = z * c' := hCV c' hc' z hzV
  show z * (x' * c') = x' * c' * z
  calc z * (x' * c') = (z * x') * c' := by group
    _ = (x' * z) * c' := by rw [h1]
    _ = x' * (z * c') := by group
    _ = x' * (c' * z) := by rw [h2]
    _ = x' * c' * z := by group

theorem usup_inf_inf_eq_bot {δ ρ₁ ρ₂ ρ₃ : Vtx (puAmalgam c.hyp.le)} (hδ : IsMVtx _ δ)
    (h₁ : (puAmalgam c.hyp.le).treeGraph.Adj δ ρ₁) (h₂ : (puAmalgam c.hyp.le).treeGraph.Adj δ ρ₂)
    (h₃ : (puAmalgam c.hyp.le).treeGraph.Adj δ ρ₃)
    (h12 : Usup (puAmalgam c.hyp.le) δ ρ₁ ≠ Usup _ δ ρ₂)
    (h13 : Usup (puAmalgam c.hyp.le) δ ρ₁ ≠ Usup _ δ ρ₃)
    (hne : Usup (puAmalgam c.hyp.le) δ ρ₃ ⊓ Usup _ δ ρ₁ ≠ Usup _ δ ρ₂ ⊓ Usup _ δ ρ₁) :
    Usup (puAmalgam c.hyp.le) δ ρ₁ ⊓ Usup _ δ ρ₂ ⊓ Usup _ δ ρ₃ = ⊥ := by
  have h := c.hyp
  obtain ⟨ψ, -, hψ⟩ := exists_natural_Uloc h c.via hδ
  have hcoord : ∀ ρ, (puAmalgam h.le).treeGraph.Adj δ ρ →
      ∀ v : ↥(Uloc h.le L δ), (v : (puAmalgam h.le).Universal) ∈ Usup _ δ ρ ↔
        natVec hψ v ∈ fixN (natImage ψ (Qv (puAmalgam h.le) ρ)) := fun ρ hρ v =>
    c.mem_usup_iff hψ hδ hρ v
  have hUs : ∀ ρ, (puAmalgam h.le).treeGraph.Adj δ ρ →
      Usup (puAmalgam h.le) δ ρ ≤ Uloc h.le L δ := fun ρ hρ => by
    rw [c.usup_eq_uloc_inf_centralizer hψ hδ hρ]; exact inf_le_left
  have hrank : ∀ ρ, (puAmalgam h.le).treeGraph.Adj δ ρ →
      Module.finrank F ↥(fixN (natImage ψ (Qv (puAmalgam h.le) ρ))) = 2 := fun ρ hρ =>
    (c.fixN_eq_commN_qv hψ hδ hρ).2
  have e12 : fixN (natImage ψ (Qv (puAmalgam h.le) ρ₁)) ≠
      fixN (natImage ψ (Qv (puAmalgam h.le) ρ₂)) := fun heq =>
    h12 ((eq_iff_of_natVec_iff hψ (hUs _ h₁) (hUs _ h₂) (hcoord _ h₁) (hcoord _ h₂)).mpr heq)
  have e13 : fixN (natImage ψ (Qv (puAmalgam h.le) ρ₁)) ≠
      fixN (natImage ψ (Qv (puAmalgam h.le) ρ₃)) := fun heq =>
    h13 ((eq_iff_of_natVec_iff hψ (hUs _ h₁) (hUs _ h₃) (hcoord _ h₁) (hcoord _ h₃)).mpr heq)
  have ene : fixN (natImage ψ (Qv (puAmalgam h.le) ρ₃)) ⊓
      fixN (natImage ψ (Qv (puAmalgam h.le) ρ₁)) ≠
      fixN (natImage ψ (Qv (puAmalgam h.le) ρ₂)) ⊓ fixN (natImage ψ (Qv (puAmalgam h.le) ρ₁)) := by
    intro heq
    refine hne ((eq_iff_of_natVec_iff hψ (inf_le_left.trans (hUs _ h₃))
      (inf_le_left.trans (hUs _ h₂)) (fun v => ?_) (fun v => ?_)).mpr heq)
    · rw [Subgroup.mem_inf, Submodule.mem_inf, hcoord _ h₃, hcoord _ h₁]
    · rw [Subgroup.mem_inf, Submodule.mem_inf, hcoord _ h₂, hcoord _ h₁]
  have hbot := inf_inf_eq_bot_of_ne (hrank _ h₁) (hrank _ h₂) (hrank _ h₃) e12 e13 ene
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨⟨hx1, hx2⟩, hx3⟩ := hx
  have hxU := hUs _ h₁ hx1
  have h0 : natVec hψ ⟨x, hxU⟩ ∈ fixN (natImage ψ (Qv (puAmalgam h.le) ρ₁)) ⊓
      fixN (natImage ψ (Qv (puAmalgam h.le) ρ₂)) ⊓ fixN (natImage ψ (Qv (puAmalgam h.le) ρ₃)) :=
    ⟨⟨(hcoord _ h₁ ⟨x, hxU⟩).mp hx1, (hcoord _ h₂ ⟨x, hxU⟩).mp hx2⟩,
      (hcoord _ h₃ ⟨x, hxU⟩).mp hx3⟩
  rw [hbot, Submodule.mem_bot] at h0
  have h1 : (⟨x, hxU⟩ : ↥(Uloc h.le L δ)) = 1 :=
    natVec_injective hψ (by rw [h0, natVec_one])
  rw [Subgroup.mem_bot]
  exact congrArg Subtype.val h1

theorem top_layer (h14 : MS14AS) (hSQ : SQTKQuot) (hZV : c.HZV) (hQ4 : c.HQ4)
    (hp : IsGoodPath _ p N) {a : ℕ} (ha : Even a) (h34 : 34 ≤ a) (haN : a + 30 ≤ N)
    {p' : ℕ → Vtx (puAmalgam c.hyp.le)} (hp' : IsGoodPath _ p' N)
    (hpp' : ∀ i, i ≤ a + 2 → p' i = p i)
    (hU1 : Usup (puAmalgam c.hyp.le) (p (a + 2)) (p' (a + 3)) ≠ Usup _ (p (a + 2)) (p (a + 1)))
    (hU3 : Usup (puAmalgam c.hyp.le) (p (a + 2)) (p' (a + 3)) ⊓ Usup _ (p (a + 2)) (p (a + 1)) ≠
      Usup _ (p (a + 2)) (p (a + 3)) ⊓ Usup _ (p (a + 2)) (p (a + 1)))
    {ψ : ↥(stab (puAmalgam c.hyp.le) (p a)) →* ↥(StatedSL 3 F)} (hψs : Function.Surjective ψ)
    (hψ : IsSumOfNaturalModulesVia (stab _ (p a)) (Uloc c.hyp.le L (p a)) ⊥ ψ false 1) :
    (⁅conjCl (stab (puAmalgam c.hyp.le) (p a)) (Vcirc c.hyp.le L (p (a + 4)) ⊔ ZM _ (p (a + 4))) ⊔
          whv c.hyp (p a) (p (a + 2)), stab (puAmalgam c.hyp.le) (p a)⁆ ⊔
        whv c.hyp (p a) (p (a + 2))) ⊓
      (⁅conjCl (stab (puAmalgam c.hyp.le) (p a))
            (Vcirc c.hyp.le L (p' (a + 4)) ⊔ ZM _ (p' (a + 4))) ⊔
          whv c.hyp (p a) (p (a + 2)), stab (puAmalgam c.hyp.le) (p a)⁆ ⊔
        whv c.hyp (p a) (p (a + 2))) = whv c.hyp (p a) (p (a + 2)) ∧
    IsSumOfNaturalModulesVia (stab _ (p a))
      (⁅conjCl (stab (puAmalgam c.hyp.le) (p a)) (Vcirc c.hyp.le L (p (a + 4)) ⊔ ZM _ (p (a + 4))) ⊔
          whv c.hyp (p a) (p (a + 2)), stab (puAmalgam c.hyp.le) (p a)⁆ ⊔
        whv c.hyp (p a) (p (a + 2))) (whv c.hyp (p a) (p (a + 2))) ψ false 1 ∧
    IsSumOfNaturalModulesVia (stab _ (p a))
      (⁅conjCl (stab (puAmalgam c.hyp.le) (p a))
            (Vcirc c.hyp.le L (p' (a + 4)) ⊔ ZM _ (p' (a + 4))) ⊔
          whv c.hyp (p a) (p (a + 2)), stab (puAmalgam c.hyp.le) (p a)⁆ ⊔
        whv c.hyp (p a) (p (a + 2))) (whv c.hyp (p a) (p (a + 2))) ψ false 1 := by
  have h := c.hyp
  have hpa : p' a = p a := hpp' a (by omega)
  have hpa2 : p' (a + 2) = p (a + 2) := hpp' (a + 2) (by omega)
  have hpa1 : p' (a + 1) = p (a + 1) := hpp' (a + 1) (by omega)
  have hpam : p' (a - 2) = p (a - 2) := hpp' (a - 2) (by omega)
  have h₁ := c.top_isSum h14 hSQ hZV hQ4 hp ha h34 haN hψs hψ
  have key : ∀ (ψ' : ↥(stab (puAmalgam h.le) (p' a)) →* ↥(StatedSL 3 F)),
      Function.Surjective ψ' →
      IsSumOfNaturalModulesVia (stab _ (p' a)) (Uloc h.le L (p' a)) ⊥ ψ' false 1 →
      IsSumOfNaturalModulesVia (stab _ (p' a))
        (⁅conjCl (stab (puAmalgam h.le) (p' a)) (Vcirc h.le L (p' (a + 4)) ⊔ ZM _ (p' (a + 4))) ⊔
            whv h (p' a) (p' (a + 2)), stab (puAmalgam h.le) (p' a)⁆ ⊔
          whv h (p' a) (p' (a + 2))) (whv h (p' a) (p' (a + 2))) ψ' false 1 :=
    fun ψ' h1 h2 => c.top_isSum h14 hSQ hZV hQ4 hp' ha h34 haN h1 h2
  rw [hpa, hpa2] at key
  have h₂ := key ψ hψs hψ
  refine ⟨?_, h₁, h₂⟩
  set Wh := whv h (p a) (p (a + 2)) with hWh
  set X₁ := conjCl (stab (puAmalgam h.le) (p a)) (Vcirc h.le L (p (a + 4)) ⊔ ZM _ (p (a + 4))) ⊔
    Wh with hX₁
  set X₂ := conjCl (stab (puAmalgam h.le) (p a)) (Vcirc h.le L (p' (a + 4)) ⊔ ZM _ (p' (a + 4))) ⊔
    Wh with hX₂
  have hα := c.isMVtx_of_isGoodPath hp (k := a) (by omega) ha
  have hγ := c.isMVtx_of_isGoodPath hp (k := a + 2) (by omega) (ha.add even_two)
  have hne := c.commutator_top'_ne_bot h14 hSQ hZV hQ4 hp ha h34 haN
  rw [← hWh, ← hX₁] at hne
  have hV₁ := c.commutator_top_vv_le hp ha (by omega) (by omega)
  rw [← hWh, ← hX₁] at hV₁
  have hV₂ := c.commutator_top_vv_le hp' ha (by omega) (by omega)
  rw [hpa, hpa2, hpam, ← hWh, ← hX₂] at hV₂
  have hXn : ∀ X : Subgroup (puAmalgam h.le).Universal,
      stab (puAmalgam h.le) (p a) ≤ Subgroup.normalizer (X : Set _) →
      ⁅X, stab (puAmalgam h.le) (p a)⁆ ⊔ Wh ≤ X ⊔ Wh := fun X hX =>
    sup_le_sup_right (Subgroup.le_normalizer_iff_commutator_le_left.mp hX) _
  have hWhn : stab (puAmalgam h.le) (p a) ≤ Subgroup.normalizer (Wh : Set _) :=
    S4A.le_normalizer_conjCl _ _
  have hX₁n : stab (puAmalgam h.le) (p a) ≤ Subgroup.normalizer (X₁ : Set _) :=
    le_normalizer_sup (S4A.le_normalizer_conjCl _ _) hWhn
  have hX₂n : stab (puAmalgam h.le) (p a) ≤ Subgroup.normalizer (X₂ : Set _) :=
    le_normalizer_sup (S4A.le_normalizer_conjCl _ _) hWhn
  have hX₁' : ⁅X₁, stab (puAmalgam h.le) (p a)⁆ ⊔ Wh ≤ X₁ :=
    sup_le (Subgroup.le_normalizer_iff_commutator_le_left.mp hX₁n) le_sup_right
  have hX₂' : ⁅X₂, stab (puAmalgam h.le) (p a)⁆ ⊔ Wh ≤ X₂ :=
    sup_le (Subgroup.le_normalizer_iff_commutator_le_left.mp hX₂n) le_sup_right
  have hR₁ := c.critR_eq_usup_inf hp (x := a - 2) ((Nat.even_sub (by omega)).mpr
    (iff_of_true ha (by decide))) (by omega) (by omega)
  have hR₂ := c.critR_eq_usup_inf hp' (x := a - 2) ((Nat.even_sub (by omega)).mpr
    (iff_of_true ha (by decide))) (by omega) (by omega)
  rw [show a - 2 + 8 = a + 6 by omega, show a - 2 + 4 = a + 2 by omega,
    show a - 2 + 3 = a + 1 by omega, show a - 2 + 5 = a + 3 by omega] at hR₁ hR₂
  rw [hpam, hpa2, hpa1] at hR₂
  have hγ1 : (puAmalgam h.le).treeGraph.Adj (p (a + 2)) (p (a + 1)) :=
    (hp.adj (a + 1) (by omega)).symm
  have hγ3 : (puAmalgam h.le).treeGraph.Adj (p (a + 2)) (p (a + 3)) := hp.adj (a + 2) (by omega)
  have hγ3' : (puAmalgam h.le).treeGraph.Adj (p (a + 2)) (p' (a + 3)) := by
    have := hp'.adj (a + 2) (by omega)
    rwa [hpa2] at this
  have h13 : Usup (puAmalgam h.le) (p (a + 2)) (p (a + 1)) ≠ Usup _ (p (a + 2)) (p (a + 3)) := by
    intro heq
    obtain ⟨ψ₂, -, hψ₂⟩ := exists_natural_Uloc h c.via hγ
    have hzh := c.zh_ne_of_isGoodPath hp (y := a + 2) (ha.add even_two) (by omega) (by omega)
    rw [show a + 2 - 1 = a + 1 by omega, show a + 2 + 1 = a + 3 by omega] at hzh
    exact hzh ((c.usup_eq_iff_zh_eq hψ₂ hγ hγ1 hγ3).mp heq)
  have hbotR : critR (puAmalgam h.le) (p (a - 2)) (p (a + 6)) ⊓
      critR _ (p (a - 2)) (p' (a + 6)) = ⊥ := by
    rw [hR₁, hR₂]
    have := c.usup_inf_inf_eq_bot hγ hγ1 hγ3 hγ3' h13 (Ne.symm hU1) hU3
    rw [eq_bot_iff] at this ⊢
    intro x hx
    exact this ⟨⟨hx.1.1, hx.1.2⟩, hx.2.2⟩
  refine le_antisymm ?_ (le_inf le_sup_right le_sup_right)
  by_contra hcon
  obtain ⟨x, hx, hxW⟩ := Set.not_subset.mp hcon
  have hX12 : ⁅X₁, stab (puAmalgam h.le) (p a)⁆ ⊔ Wh ≤ ⁅X₂, stab (puAmalgam h.le) (p a)⁆ ⊔ Wh := by
    intro v hv
    obtain ⟨w, hw, -, hwv⟩ := (NatSec.ofIsSum h₁).exists_inv_mul_mem_of_invariant hψs
      (fun l y hy => Subgroup.mem_inf.mpr
        ⟨(Subgroup.mem_normalizer_iff.mp (h₁.1 l.2) y).mp (Subgroup.mem_inf.mp hy).1,
          (Subgroup.mem_normalizer_iff.mp (h₂.1 l.2) y).mp (Subgroup.mem_inf.mp hy).2⟩)
      hx (Subgroup.mem_inf.mp hx).1 hxW hv
    have e : v = w * (w⁻¹ * v) := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_inf.mp hw).2 (Subgroup.mem_sup_right hwv)
  apply hne
  rw [eq_bot_iff, ← hbotR]
  refine le_inf ?_ ?_
  · exact (Subgroup.commutator_mono hX₁' (c.vhat_le_vv hα)).trans hV₁
  · exact (Subgroup.commutator_mono (hX12.trans hX₂') (c.vhat_le_vv hα)).trans hV₂

end GoodPath

end Ctx

end CFSG.Quasithin.MS93.S45
