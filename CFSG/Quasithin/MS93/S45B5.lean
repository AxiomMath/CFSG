module

public import CFSG.Quasithin.MS93.S45Y2

public section

namespace CFSG.Quasithin.MS93.S45

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix

theorem sup_inf_eq_of_le' {K : Type*} [Group K] {A B C : Subgroup K} (hAC : A ≤ C)
    (hn : B ≤ Subgroup.normalizer (A : Set K)) : (A ⊔ B) ⊓ C = A ⊔ (B ⊓ C) := by
  refine le_antisymm ?_ (sup_le (le_inf le_sup_left hAC) (inf_le_inf_right _ le_sup_right))
  intro x hx'
  obtain ⟨hx, hxC⟩ := Subgroup.mem_inf.mp hx'
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left A B hn] at hx
  obtain ⟨a, ha, b, hb, rfl⟩ := hx
  have hbC : b ∈ C := by
    have := C.mul_mem (C.inv_mem (hAC ha)) hxC
    rwa [inv_mul_cancel_left] at this
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right ⟨hb, hbC⟩)

variable {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Fintype F]

namespace Ctx

variable {M T L : Subgroup G} {φ : ↥M →* ↥(StatedSL 3 F)} (c : Ctx M T L φ)
include c

section GoodPath

variable {p p' : ℕ → Vtx (puAmalgam c.hyp.le)} {N : ℕ}

theorem qv_le_zm_sup_qv_of_branch (hp : IsGoodPath _ p N) (hp' : IsGoodPath _ p' N) {y : ℕ}
    (hy : Even y) (h12 : 12 ≤ y) (hyN : y + 10 ≤ N) (hpp' : ∀ i, i ≤ y → p' i = p i)
    (hne : Usup (puAmalgam c.hyp.le) (p y) (p' (y + 1)) ⊓ Usup _ (p y) (p (y - 1)) ≠
      Usup _ (p y) (p (y + 1)) ⊓ Usup _ (p y) (p (y - 1))) :
    Qv (puAmalgam c.hyp.le) (p (y - 3)) ≤
      (ZM _ (p (y + 4)) ⊔ ZM _ (p' (y + 4))) ⊔ Qv _ (p (y - 4)) := by
  have h := c.hyp
  have : CharP F 2 := c.charP
  have hy4 : Even (y - 4) := by obtain ⟨k, hk⟩ := hy; exact ⟨k - 2, by omega⟩
  have hc₁ : IsCritical (puAmalgam h.le) (p (y - 4)) (p (y + 4)) := by
    have := c.isCritical_of_isGoodPath hp hy4 (by omega)
    rwa [show y - 4 + 8 = y + 4 by omega] at this
  have hc₂ : IsCritical (puAmalgam h.le) (p (y - 4)) (p' (y + 4)) := by
    have := c.isCritical_of_isGoodPath hp' hy4 (by omega)
    rwa [show y - 4 + 8 = y + 4 by omega, hpp' (y - 4) (by omega)] at this
  have hR₁ := c.critR_eq_usup_inf hp (x := y - 4) hy4 (by omega) (by omega)
  have hR₂ := c.critR_eq_usup_inf hp' (x := y - 4) hy4 (by omega) (by omega)
  rw [show y - 4 + 8 = y + 4 by omega, show y - 4 + 4 = y by omega,
    show y - 4 + 3 = y - 1 by omega, show y - 4 + 5 = y + 1 by omega] at hR₁ hR₂
  rw [hpp' (y - 4) (by omega), hpp' y le_rfl, hpp' (y - 1) (by omega)] at hR₂
  have hRne :
      critR (puAmalgam h.le) (p (y - 4)) (p (y + 4)) ≠ critR _ (p (y - 4)) (p' (y + 4)) := by
    rw [hR₁, hR₂]
    intro heq
    apply hne
    rw [inf_comm (Usup _ _ (p' (y + 1))), inf_comm (Usup _ _ (p (y + 1)))]
    exact heq.symm
  have hM4 : IsMVtx (puAmalgam h.le) (p (y - 4)) := hc₁.1
  obtain ⟨ψ, hψs, hψ⟩ := exists_natural_Uloc h c.via hM4
  have hg1 : ∀ μ : Vtx (puAmalgam h.le), IsCritical _ (p (y - 4)) μ →
      geo (puAmalgam h.le) (p (y - 4)) μ 1 = p (y - 3) → ZM (puAmalgam h.le) μ ≤ Qv _ (p (y - 3)) :=
    fun μ hc hg => hg ▸ c.zm_le_qv_geo_one hc
  have hgeo₁ : geo (puAmalgam h.le) (p (y - 4)) (p (y + 4)) 1 = p (y - 3) := by
    rw [hp.eq_geo (i := y - 4) (j := y + 4) (k := y - 3) (by omega) (by omega) (by omega),
      show y - 3 - (y - 4) = 1 by omega]
  have hgeo₂ : geo (puAmalgam h.le) (p (y - 4)) (p' (y + 4)) 1 = p (y - 3) := by
    rw [← hpp' (y - 4) (by omega), ← hpp' (y - 3) (by omega),
      hp'.eq_geo (i := y - 4) (j := y + 4) (k := y - 3) (by omega) (by omega) (by omega),
      show y - 3 - (y - 4) = 1 by omega]
  set RT := natImage ψ (Qv (puAmalgam h.le) (p (y - 3))) with hRT
  have hadj : (puAmalgam h.le).treeGraph.Adj (p (y - 4)) (p (y - 3)) := by
    have := hp.adj (y - 4) (by omega)
    rwa [show y - 4 + 1 = y - 3 by omega] at this
  obtain ⟨hRT2, hRTc, hRTfc, hRTr⟩ := c.natImage_qv_props hM4 hadj hψ
  set A₁ := natImage ψ (ZM (puAmalgam h.le) (p (y + 4))) with hA₁
  set A₂ := natImage ψ (ZM (puAmalgam h.le) (p' (y + 4))) with hA₂
  have hA₁R : A₁ ≤ RT := natImage_mono (hg1 _ hc₁ hgeo₁)
  have hA₂R : A₂ ≤ RT := natImage_mono (hg1 _ hc₂ hgeo₂)
  have hcA₁ : Nat.card ↥A₁ = Fintype.card F := c.card_natImage_zm hc₁ hψ
  have hcA₂ : Nat.card ↥A₂ = Fintype.card F := c.card_natImage_zm hc₂ hψ
  have hRU : ∀ μ : Vtx (puAmalgam h.le), IsCritical _ (p (y - 4)) μ →
      critR (puAmalgam h.le) (p (y - 4)) μ ≤ Uloc h.le L (p (y - 4)) :=
    fun μ hc => c.critR_le_uloc hc
  have hne' : commN A₁ ≠ commN A₂ := fun heq => hRne ((eq_iff_of_natVec_iff hψ (hRU _ hc₁)
    (hRU _ hc₂) (c.mem_critR_iff hc₁ hψ) (c.mem_critR_iff hc₂ hψ)).mpr heq)
  have hrank : ∀ μ : Vtx (puAmalgam h.le), IsCritical _ (p (y - 4)) μ →
      Nat.card ↥(critR (puAmalgam h.le) (p (y - 4)) μ) = Fintype.card F →
      Module.finrank F ↥(commN (natImage ψ (ZM (puAmalgam h.le) μ))) = 1 := by
    intro μ hc hcard
    have h1 := card_eq_of_natVec_iff hψ (hRU _ hc) (c.mem_critR_iff hc hψ)
    rw [hcard, Module.natCard_eq_pow_finrank (K := F), Nat.card_eq_fintype_card] at h1
    have h1' : Fintype.card F ^ 1 = Fintype.card F ^
        Module.finrank F ↥(commN (natImage ψ (ZM (puAmalgam h.le) μ))) := by
      rw [pow_one]; exact h1
    exact (Nat.pow_right_injective Fintype.one_lt_card h1').symm
  have hcardR₁ : Nat.card ↥(critR (puAmalgam h.le) (p (y - 4)) (p (y + 4))) =
      Fintype.card F := by
    have := c.card_critR hp.toIsNBPath (x := y - 4) (by omega)
      (c.isCritical_of_isGoodPath hp hy4 (by omega)) (c.straight_of_isGoodPath hp hy4 (by omega))
      (by
        have := c.zh_ne_of_isGoodPath hp hy (by omega) (by omega)
        rwa [show y - 4 + 3 = y - 1 by omega, show y - 4 + 5 = y + 1 by omega])
    rwa [show y - 4 + 8 = y + 4 by omega] at this
  have hcardR₂ : Nat.card ↥(critR (puAmalgam h.le) (p (y - 4)) (p' (y + 4))) =
      Fintype.card F := by
    have := c.card_critR hp'.toIsNBPath (x := y - 4) (by omega)
      (c.isCritical_of_isGoodPath hp' hy4 (by omega))
      (c.straight_of_isGoodPath hp' hy4 (by omega))
      (by
        have := c.zh_ne_of_isGoodPath hp' hy (by omega) (by omega)
        rwa [show y - 4 + 3 = y - 1 by omega, show y - 4 + 5 = y + 1 by omega])
    rwa [show y - 4 + 8 = y + 4 by omega, hpp' (y - 4) (by omega)] at this
  have hr₁ := hrank _ hc₁ hcardR₁
  have hr₂ := hrank _ hc₂ hcardR₂
  rw [← hA₁] at hr₁
  rw [← hA₂] at hr₂
  have hinf : A₁ ⊓ A₂ = ⊥ := by
    rw [eq_bot_iff]
    intro a ha
    rw [Subgroup.mem_bot]
    apply eq_one_of_mulVec_eq_self
    intro v
    have h1 : ((a : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v - v ∈ commN A₁ ⊓ commN A₂ :=
      ⟨sub_mem_commN ha.1 v, sub_mem_commN ha.2 v⟩
    have h0 : commN A₁ ⊓ commN A₂ = ⊥ := by
      have hle : Module.finrank F ↥(commN A₁ ⊓ commN A₂) ≤ 1 :=
        hr₁ ▸ Submodule.finrank_mono inf_le_left
      by_contra h0
      have hpos : 0 < Module.finrank F ↥(commN A₁ ⊓ commN A₂) :=
        Nat.pos_of_ne_zero fun h => h0 (Submodule.finrank_eq_zero.mp h)
      have e1 : commN A₁ ⊓ commN A₂ = commN A₁ :=
        Submodule.eq_of_le_of_finrank_le inf_le_left (by omega)
      have e2 : commN A₁ ⊓ commN A₂ = commN A₂ :=
        Submodule.eq_of_le_of_finrank_le inf_le_right (by omega)
      exact hne' (e1.symm.trans e2)
    rw [h0, Submodule.mem_bot, sub_eq_zero] at h1
    exact h1
  have hab : A₂ ≤ Subgroup.centralizer (A₁ : Set (SL3 F)) := by
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact comm_of_commN_le_fixN (hRTfc ▸ le_rfl) (hA₁R ha) (hA₂R hb)
  have hcard12 : Nat.card ↥(A₁ ⊔ A₂) = Nat.card F ^ 2 := by
    rw [card_sup_of_commute hab hinf, hcA₁, hcA₂, sq, Nat.card_eq_fintype_card]
  have hfinRT : Finite ↥RT := Nat.finite_of_card_ne_zero (by
    rw [hRTc]; exact pow_ne_zero _ Nat.card_pos.ne')
  have hRTeq : A₁ ⊔ A₂ = RT := Subgroup.eq_of_le_of_card_ge (sup_le hA₁R hA₂R)
    (by rw [hRTc, hcard12])
  have hRTW : RT ≤ natImage ψ (ZM (puAmalgam h.le) (p (y + 4)) ⊔ ZM _ (p' (y + 4))) := by
    rw [← hRTeq]
    exact sup_le (natImage_mono le_sup_left) (natImage_mono le_sup_right)
  intro t ht
  have hts : t ∈ stab (puAmalgam h.le) (p (y - 4)) := qv_le_stab_of_adj _ hadj.symm ht
  set t' : ↥(stab (puAmalgam h.le) (p (y - 4))) := ⟨t, hts⟩ with ht'
  obtain ⟨w, hw, hwt⟩ := mem_natImage.mp (hRTW (mem_natImage.mpr ⟨t', ht, rfl⟩))
  have hk : w⁻¹ * t' ∈ (toSL3 ψ).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hwt, inv_mul_cancel]
  rw [c.ker_toSL3_eq hM4 hψ, Subgroup.mem_subgroupOf] at hk
  have e : t = (w : (puAmalgam h.le).Universal) * ((w⁻¹ * t' : ↥(stab _ _)) :
      (puAmalgam h.le).Universal) := by
    simp [ht']
  rw [e]
  exact mul_mem (Subgroup.mem_sup_left hw) (Subgroup.mem_sup_right hk)

theorem top_le_qv (hp : IsGoodPath _ p N) (hp' : IsGoodPath _ p' N) {a : ℕ} (ha : Even a)
    (haN : a + 4 ≤ N) (hpp' : ∀ i, i ≤ a + 2 → p' i = p i) :
    (conjCl (stab (puAmalgam c.hyp.le) (p a)) (Vcirc c.hyp.le L (p (a + 4)) ⊔ ZM _ (p (a + 4))) ⊔
          whv c.hyp (p a) (p (a + 2))) ⊔
        (conjCl (stab (puAmalgam c.hyp.le) (p a))
            (Vcirc c.hyp.le L (p' (a + 4)) ⊔ ZM _ (p' (a + 4))) ⊔
          whv c.hyp (p a) (p (a + 2))) ≤ Qv (puAmalgam c.hyp.le) (p a) := by
  have h := c.hyp
  have hγ := c.isMVtx_of_isGoodPath hp (k := a + 2) (by omega) (ha.add even_two)
  have hμ := c.isMVtx_of_isGoodPath hp (k := a + 4) (by omega) (ha.add (by decide))
  have hμ' := c.isMVtx_of_isGoodPath hp' (k := a + 4) (by omega) (ha.add (by decide))
  have hKQ : stab (puAmalgam h.le) (p a) ≤
      Subgroup.normalizer (Qv (puAmalgam h.le) (p a) : Set _) := stab_le_normalizer_qv _ _
  have hWhQ : whv h (p a) (p (a + 2)) ≤ Qv (puAmalgam h.le) (p a) :=
    c.whv_le_qv_of_dist hγ (by rw [hp.dist_eq' (i := a) (j := a + 2) (by omega) (by omega)]; omega)
      (by simp)
  refine sup_le (sup_le (conjCl_le_of_le_normalizer ((c.vhat_le_vv hμ).trans
    (vi_le_qv _ ?_)) hKQ) hWhQ)
    (sup_le (conjCl_le_of_le_normalizer ((c.vhat_le_vv hμ').trans (vi_le_qv _ ?_)) hKQ) hWhQ)
  · rw [tdist_comm, hp.dist_eq' (i := a) (j := a + 4) (by omega) (by omega), c.b8]
    omega
  · rw [← hpp' a (by omega), tdist_comm, hp'.dist_eq' (i := a) (j := a + 4) (by omega)
      (by omega), c.b8]
    omega

theorem commutator_qv_ltil_le_top (hZV : c.HZV) (hp : IsGoodPath _ p N)
    (hp' : IsGoodPath _ p' N) {a : ℕ} (ha : Even a) (h34 : 34 ≤ a) (haN : a + 30 ≤ N)
    (hpp' : ∀ i, i ≤ a + 2 → p' i = p i)
    (hU3 : Usup (puAmalgam c.hyp.le) (p (a + 2)) (p' (a + 3)) ⊓ Usup _ (p (a + 2)) (p (a + 1)) ≠
      Usup _ (p (a + 2)) (p (a + 3)) ⊓ Usup _ (p (a + 2)) (p (a + 1))) :
    ⁅Qv (puAmalgam c.hyp.le) (p a), Ltil c.hyp.le L (p a)⁆ ≤
      (conjCl (stab (puAmalgam c.hyp.le) (p a)) (Vcirc c.hyp.le L (p (a + 4)) ⊔ ZM _ (p (a + 4))) ⊔
          whv c.hyp (p a) (p (a + 2))) ⊔
        (conjCl (stab (puAmalgam c.hyp.le) (p a))
            (Vcirc c.hyp.le L (p' (a + 4)) ⊔ ZM _ (p' (a + 4))) ⊔
          whv c.hyp (p a) (p (a + 2))) := by
  have h := c.hyp
  have h20 := h.hyp20
  have hα := c.isMVtx_of_isGoodPath hp (k := a) (by omega) ha
  have ha2 : Even (a - 2) := (Nat.even_sub (by omega)).mpr (iff_of_true ha (by decide))
  have ha4 : Even (a - 4) := (Nat.even_sub (by omega)).mpr (iff_of_true ha (by decide))
  have hM2 := c.isMVtx_of_isGoodPath hp (k := a - 2) (by omega) ha2
  have hM4 := c.isMVtx_of_isGoodPath hp (k := a - 4) (by omega) ha4
  have hγ := c.isMVtx_of_isGoodPath hp (k := a + 2) (by omega) (ha.add even_two)
  have hμ := c.isMVtx_of_isGoodPath hp (k := a + 4) (by omega) (ha.add (by decide))
  have hμ' := c.isMVtx_of_isGoodPath hp' (k := a + 4) (by omega) (ha.add (by decide))
  have hd : ∀ i j, i ≤ j → j ≤ N → (puAmalgam h.le).treeGraph.dist (p i) (p j) = j - i :=
    fun i j hij hj => hp.dist_eq' hij hj
  have hadj : ∀ i, i < N → (puAmalgam h.le).treeGraph.Adj (p i) (p (i + 1)) := hp.adj
  have hm1 : (puAmalgam h.le).treeGraph.Adj (p a) (p (a - 1)) := by
    have := hadj (a - 1) (by omega)
    rw [show a - 1 + 1 = a by omega] at this
    exact this.symm
  have hm12 : (puAmalgam h.le).treeGraph.Adj (p (a - 1)) (p (a - 2)) := by
    have := hadj (a - 2) (by omega)
    rw [show a - 2 + 1 = a - 1 by omega] at this
    exact this.symm
  have hm23 : (puAmalgam h.le).treeGraph.Adj (p (a - 2)) (p (a - 3)) := by
    have := hadj (a - 3) (by omega)
    rw [show a - 3 + 1 = a - 2 by omega] at this
    exact this.symm
  have hm34 : (puAmalgam h.le).treeGraph.Adj (p (a - 3)) (p (a - 4)) := by
    have := hadj (a - 4) (by omega)
    rw [show a - 4 + 1 = a - 3 by omega] at this
    exact this.symm
  set Wh := whv h (p a) (p (a + 2)) with hWh
  set X := (conjCl (stab (puAmalgam h.le) (p a)) (Vcirc h.le L (p (a + 4)) ⊔ ZM _ (p (a + 4))) ⊔
      Wh) ⊔ (conjCl (stab (puAmalgam h.le) (p a))
        (Vcirc h.le L (p' (a + 4)) ⊔ ZM _ (p' (a + 4))) ⊔ Wh) with hX
  have hKQ : stab (puAmalgam h.le) (p a) ≤
      Subgroup.normalizer (Qv (puAmalgam h.le) (p a) : Set _) := stab_le_normalizer_qv _ _
  have hKX : stab (puAmalgam h.le) (p a) ≤ Subgroup.normalizer (X : Set _) :=
    le_normalizer_sup (le_normalizer_sup (S4A.le_normalizer_conjCl _ _)
      (S4A.le_normalizer_conjCl _ _)) (le_normalizer_sup (S4A.le_normalizer_conjCl _ _)
      (S4A.le_normalizer_conjCl _ _))
  have hd2 : (puAmalgam h.le).treeGraph.dist (p a) (p (a + 2)) = 2 := by
    rw [hd a (a + 2) (by omega) (by omega)]; omega
  have hWhQ : ∀ j, a - 3 ≤ j → j ≤ a → Wh ≤ Qv (puAmalgam h.le) (p j) := fun j hj hja =>
    c.whv_le_qv_of_dist hγ hd2 (by rw [tdist_comm, hd j a hja (by omega)]; omega)
  have hWhX : Wh ≤ X := le_sup_right.trans le_sup_left
  have hXQ : X ≤ Qv (puAmalgam h.le) (p a) := c.top_le_qv hp hp' ha (by omega) hpp'
  have h1 : Qv (puAmalgam h.le) (p (a - 1)) ≤ X ⊔ Qv _ (p (a - 2)) := by
    have hb := c.qv_le_zm_sup_qv_of_branch hp hp' (y := a + 2) (ha.add even_two) (by omega)
      (by omega) hpp' (by rwa [show a + 2 + 1 = a + 3 by omega, show a + 2 - 1 = a + 1 by omega])
    rw [show a + 2 - 3 = a - 1 by omega, show a + 2 + 4 = a + 6 by omega,
      show a + 2 - 4 = a - 2 by omega] at hb
    refine hb.trans (sup_le_sup_right (sup_le ?_ ?_) _)
    · have hz := c.zm_le_vhat_right hZV hp (a := a + 4) (ha.add (by decide)) (by omega)
        (by omega)
      rw [show a + 4 + 2 = a + 6 by omega] at hz
      exact hz.trans ((S4A.le_conjCl _ _).trans (le_sup_left.trans le_sup_left))
    · have hz := c.zm_le_vhat_right hZV hp' (a := a + 4) (ha.add (by decide)) (by omega)
        (by omega)
      rw [show a + 4 + 2 = a + 6 by omega] at hz
      exact hz.trans ((S4A.le_conjCl _ _).trans (le_sup_left.trans le_sup_right))
  have hQ2s : Qv (puAmalgam h.le) (p (a - 2)) ≤ stab _ (p a) :=
    (qv_le_qv _ h20 hM2 hm12.symm).trans (qv_le_stab_of_adj _ hm1.symm)
  have h2 : Qv (puAmalgam h.le) (p a) ≤ X ⊔ (Qv _ (p (a - 2)) ⊓ Qv _ (p a)) := by
    rw [← sup_inf_eq_of_le' hXQ (hQ2s.trans hKX)]
    exact le_inf ((qv_le_qv _ h20 hα hm1).trans h1) le_rfl
  have hW' : whv h (p a) (p (a - 2)) = Wh :=
    (c.whv_eq_of_isGoodPath hp (a := a) ha (by omega) (by omega)).symm
  have h3 : Qv (puAmalgam h.le) (p (a - 2)) ≤ Wh ⊔ Qv _ (p (a - 4)) := by
    have hq := c.qv_le_whv_sup_qv hZV hp (y := a) ha (by omega) (by omega)
    rw [hW'] at hq
    exact (qv_le_qv _ h20 hM2 hm23).trans hq
  have hWh4 : Wh ≤ Subgroup.normalizer (Qv (puAmalgam h.le) (p (a - 4)) : Set _) :=
    (hWhQ (a - 3) le_rfl (by omega)).trans
      ((qv_le_stab_of_adj _ hm34).trans (stab_le_normalizer_qv _ _))
  have h4 : Qv (puAmalgam h.le) (p (a - 2)) ⊓ Qv _ (p a) ≤
      Wh ⊔ (Qv _ (p (a - 4)) ⊓ (Qv _ (p (a - 2)) ⊓ Qv _ (p a))) := by
    rw [← sup_inf_eq_of_le (le_inf (hWhQ (a - 2) (by omega) (by omega))
      (hWhQ a (by omega) le_rfl)) hWh4]
    exact le_inf (inf_le_left.trans h3) le_rfl
  set D := Qv (puAmalgam h.le) (p (a - 4)) ⊓ (Qv _ (p (a - 2)) ⊓ Qv _ (p a)) with hD
  have h5 : Qv (puAmalgam h.le) (p a) ≤ X ⊔ D :=
    h2.trans (sup_le le_sup_left (h4.trans (sup_le (hWhX.trans le_sup_left) le_sup_right)))
  set K := whv h (p (a - 4)) (p (a - 2)) with hK
  have hK4 : ⁅K, Qv (puAmalgam h.le) (p (a - 4))⁆ ≤ ZM _ (p (a - 4)) := by
    have hc := c.commutator_whv_qv_le hZV hp (a := a - 4) ha4 (by omega) (by omega)
    have e := c.whv_eq_of_isGoodPath hp (a := a - 4) ha4 (by omega) (by omega)
    rw [← e, show a - 4 + 2 = a - 2 by omega] at hc
    exact hc
  have hZ4X : ZM (puAmalgam h.le) (p (a - 4)) ≤ X := by
    have hz := c.zm_le_vhat_left' hZV hp (a := a - 2) ha2 (by omega) (by omega)
    rw [show a - 2 - 2 = a - 4 by omega] at hz
    exact hz.trans ((c.vhat_le_whv_self (δ := p a)).trans (hW'.le.trans hWhX))
  have hT1 : Qv (puAmalgam h.le) (p (a - 1)) ≤ K ⊔ Qv _ (p a) := by
    have hq := c.qv_le_whv_sup_qv_right hZV hp (a := a - 4) ha4 (by omega) (by omega)
    rwa [show a - 4 + 3 = a - 1 by omega, show a - 4 + 2 = a - 2 by omega,
      show a - 4 + 4 = a by omega] at hq
  have hd42 : (puAmalgam h.le).treeGraph.dist (p (a - 4)) (p (a - 2)) = 2 := by
    rw [hd (a - 4) (a - 2) (by omega) (by omega)]; omega
  have hKT : K ≤ Qv (puAmalgam h.le) (p (a - 1)) :=
    c.whv_le_qv_of_dist hM2 hd42 (by rw [hd (a - 4) (a - 1) (by omega) (by omega)]; omega)
  have hKs : K ≤ stab (puAmalgam h.le) (p a) := hKT.trans (qv_le_stab_of_adj _ hm1.symm)
  have hKQα : ¬ K ≤ Qv (puAmalgam h.le) (p a) := fun hle =>
    S46.not_qv_le_qv_of_adj h hα hm1 (hT1.trans (sup_le hle le_rfl))
  have hDs : D ≤ stab (puAmalgam h.le) (p a) := inf_le_right.trans (inf_le_right.trans
    (qv_le_stab _ _))
  have hXs : X ≤ stab (puAmalgam h.le) (p a) := hXQ.trans (qv_le_stab _ _)
  have hQK : ⁅Qv (puAmalgam h.le) (p a), K⁆ ≤ X := by
    refine (Subgroup.commutator_mono h5 le_rfl).trans ?_
    refine S46.commutator_sup_le_of_le_normalizer hKX hXs hDs
      (Subgroup.le_normalizer_iff_commutator_le_left.mp (hKs.trans hKX)) ?_
    rw [Subgroup.commutator_comm]
    exact ((Subgroup.commutator_mono le_rfl inf_le_left).trans hK4).trans hZ4X
  set C := commIn (stab (puAmalgam h.le) (p a)) (Qv _ (p a)) X hKX with hC
  have hCs : C ≤ stab (puAmalgam h.le) (p a) := fun g hg => (mem_commIn.mp hg).1
  have hCconj : ∀ k ∈ stab (puAmalgam h.le) (p a), ∀ g ∈ C, k * g * k⁻¹ ∈ C := by
    intro k hk g hg
    obtain ⟨hgs, hgw⟩ := mem_commIn.mp hg
    refine mem_commIn.mpr ⟨mul_mem (mul_mem hk hgs) (inv_mem hk), fun w hw => ?_⟩
    have hw' : k⁻¹ * w * k⁻¹⁻¹ ∈ Qv (puAmalgam h.le) (p a) :=
      (Subgroup.mem_normalizer_iff.mp (hKQ (inv_mem hk)) w).mp hw
    have h1 := (Subgroup.mem_normalizer_iff.mp (hKX hk) _).mp (hgw _ hw')
    have e : ⁅k * g * k⁻¹, w⁆ = k * ⁅g, k⁻¹ * w * k⁻¹⁻¹⁆ * k⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact h1
  have hCn : stab (puAmalgam h.le) (p a) ≤ Subgroup.normalizer (C : Set _) := by
    intro k hk
    rw [Subgroup.mem_normalizer_iff]
    intro g
    refine ⟨hCconj k hk g, fun hg => ?_⟩
    have := hCconj k⁻¹ (inv_mem hk) _ hg
    simpa [mul_assoc] using this
  have hKC : K ≤ C := fun x hx => mem_commIn.mpr ⟨hKs hx, fun w hw => by
    have := hQK (Subgroup.commutator_mem_commutator hw hx)
    rw [← inv_mem_iff, commutatorElement_inv] at this
    exact this⟩
  have hLC := S46.ltil_le_of_normal h c.full hα hm1 hCs hCn hKC hKT hKQα
  rw [Subgroup.commutator_comm, Subgroup.commutator_le]
  intro l hl q hq
  exact (mem_commIn.mp (hLC hl)).2 q hq

theorem commutator_qv_ltil_le_top' (hZV : c.HZV) (hQ4 : c.HQ4) (hp : IsGoodPath _ p N)
    (hp' : IsGoodPath _ p' N) {a : ℕ} (ha : Even a) (h34 : 34 ≤ a) (haN : a + 30 ≤ N)
    (hpp' : ∀ i, i ≤ a + 2 → p' i = p i)
    (hU3 : Usup (puAmalgam c.hyp.le) (p (a + 2)) (p' (a + 3)) ⊓ Usup _ (p (a + 2)) (p (a + 1)) ≠
      Usup _ (p (a + 2)) (p (a + 3)) ⊓ Usup _ (p (a + 2)) (p (a + 1))) :
    ⁅Qv (puAmalgam c.hyp.le) (p a), Ltil c.hyp.le L (p a)⁆ ≤
      (⁅conjCl (stab (puAmalgam c.hyp.le) (p a))
          (Vcirc c.hyp.le L (p (a + 4)) ⊔ ZM _ (p (a + 4))) ⊔ whv c.hyp (p a) (p (a + 2)),
          stab (puAmalgam c.hyp.le) (p a)⁆ ⊔ whv c.hyp (p a) (p (a + 2))) ⊔
        (⁅conjCl (stab (puAmalgam c.hyp.le) (p a))
          (Vcirc c.hyp.le L (p' (a + 4)) ⊔ ZM _ (p' (a + 4))) ⊔ whv c.hyp (p a) (p (a + 2)),
          stab (puAmalgam c.hyp.le) (p a)⁆ ⊔ whv c.hyp (p a) (p (a + 2))) := by
  have h := c.hyp
  have hα := c.isMVtx_of_isGoodPath hp (k := a) (by omega) ha
  have hB5 := c.commutator_qv_ltil_le_top hZV hp hp' ha h34 haN hpp' hU3
  have hpa : p' a = p a := hpp' a (by omega)
  have hpa2 : p' (a + 2) = p (a + 2) := hpp' (a + 2) le_rfl
  set Wh := whv h (p a) (p (a + 2)) with hWh
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
  have hKX₁' : stab (puAmalgam h.le) (p a) ≤ Subgroup.normalizer (X₁' : Set _) :=
    le_normalizer_sup (S45.le_normalizer_commutator hKX₁ Subgroup.le_normalizer) hKWh
  have hKX₂' : stab (puAmalgam h.le) (p a) ≤ Subgroup.normalizer (X₂' : Set _) :=
    le_normalizer_sup (S45.le_normalizer_commutator hKX₂ Subgroup.le_normalizer) hKWh
  have hKXt : stab (puAmalgam h.le) (p a) ≤
      Subgroup.normalizer ((X₁' ⊔ X₂' : Subgroup _) : Set _) := le_normalizer_sup hKX₁' hKX₂'
  have hX₁'X₁ : X₁' ≤ X₁ :=
    sup_le (Subgroup.le_normalizer_iff_commutator_le_left.mp hKX₁) le_sup_right
  have hX₂'X₂ : X₂' ≤ X₂ :=
    sup_le (Subgroup.le_normalizer_iff_commutator_le_left.mp hKX₂) le_sup_right
  have hV6 : X₁ ⊔ X₂ ≤ conjCl (stab (puAmalgam h.le) (p a)) (whv h (p (a + 2)) (p a)) := by
    have e : whv h (p (a + 2)) (p (a + 2 + 2)) = whv h (p (a + 2)) (p (a + 2 - 2)) :=
      c.whv_eq_of_isGoodPath hp (a := a + 2) (ha.add even_two) (by omega) (by omega)
    rw [show a + 2 + 2 = a + 4 by omega, show a + 2 - 2 = a by omega] at e
    have hγγ : Vcirc h.le L (p (a + 2)) ⊔ ZM _ (p (a + 2)) ≤ whv h (p (a + 2)) (p a) := by
      have := c.vhat_le_whv' hZV hp (a := a + 2) (ha.add even_two) (by omega) (by omega)
      rw [show a + 2 + 2 = a + 4 by omega] at this
      rwa [← e]
    have hμγ : Vcirc h.le L (p (a + 4)) ⊔ ZM _ (p (a + 4)) ≤ whv h (p (a + 2)) (p a) := by
      rw [← e]; exact c.vhat_le_whv_self
    have hμ'γ : Vcirc h.le L (p' (a + 4)) ⊔ ZM _ (p' (a + 4)) ≤ whv h (p (a + 2)) (p a) := by
      have e' : whv h (p' (a + 2)) (p' (a + 2 + 2)) = whv h (p' (a + 2)) (p' (a + 2 - 2)) :=
        c.whv_eq_of_isGoodPath hp' (a := a + 2) (ha.add even_two) (by omega) (by omega)
      rw [show a + 2 + 2 = a + 4 by omega, show a + 2 - 2 = a by omega, hpa, hpa2] at e'
      rw [← e']; exact c.vhat_le_whv_self
    have hWhγ : Wh ≤ conjCl (stab (puAmalgam h.le) (p a)) (whv h (p (a + 2)) (p a)) :=
      conjCl_mono hγγ
    exact sup_le (sup_le (conjCl_mono hμγ) hWhγ) (sup_le (conjCl_mono hμ'γ) hWhγ)
  have hDD : ⁅X₁ ⊔ X₂, X₁ ⊔ X₂⁆ ≤ X₁' ⊔ X₂' :=
    ((Subgroup.commutator_mono hV6 hV6).trans
      (c.commutator_vsix_le hZV hQ4 hp ha h34 (by omega))).trans (le_sup_right.trans le_sup_left)
  have hLs : Ltil h.le L (p a) ≤ stab (puAmalgam h.le) (p a) := ltil_le_stab h _
  have hXQ := c.top_le_qv hp hp' ha (by omega) hpp'
  have hX₁s : X₁ ≤ stab (puAmalgam h.le) (p a) := (le_sup_left.trans hXQ).trans (qv_le_stab _ _)
  have hX₂s : X₂ ≤ stab (puAmalgam h.le) (p a) := (le_sup_right.trans hXQ).trans (qv_le_stab _ _)
  have hDL : ⁅X₁ ⊔ X₂, Ltil h.le L (p a)⁆ ≤ X₁' ⊔ X₂' := by
    refine S46.commutator_sup_le_of_le_normalizer hKXt hX₁s hX₂s ?_ ?_
    · exact ((Subgroup.commutator_mono le_rfl hLs).trans le_sup_left).trans le_sup_left
    · exact ((Subgroup.commutator_mono le_rfl hLs).trans le_sup_left).trans le_sup_right
  rw [Subgroup.commutator_le]
  intro q hq l hl
  exact commutator_mem_of_perfect (S4A.ltil_perfect h hα)
    (sup_le (hX₁'X₁.trans le_sup_left) (hX₂'X₂.trans le_sup_right)) hDD hDL
    (fun l hl => hB5 (Subgroup.commutator_mem_commutator hq hl)) hl

end GoodPath

end Ctx

end CFSG.Quasithin.MS93.S45
