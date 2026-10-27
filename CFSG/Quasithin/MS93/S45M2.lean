module

public import CFSG.Quasithin.MS93.S45M0

public section

namespace CFSG.Quasithin.MS93.S45

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix

section Lin

variable {F : Type} [Field F]

theorem dualMat_fixed_iff (A : Subgroup (SL3 F)) (y : Fin 3 → F) :
    (∀ a ∈ A, dualMat a *ᵥ y = y) ↔ ∀ x ∈ commN A, y ⬝ᵥ x = 0 := by
  constructor
  · intro hy x hx
    induction hx using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨g, hg, x, rfl⟩ := hv
      have := dualMat_mulVec_dotProduct g y x
      rw [hy g hg] at this
      rw [dotProduct_sub, this, sub_self]
    | zero => simp
    | add u v _ _ hu hv => rw [dotProduct_add, hu, hv, add_zero]
    | smul t u _ hu => rw [dotProduct_smul, hu, smul_zero]
  · intro hy a ha
    have h1 : ∀ z, (dualMat a *ᵥ y) ⬝ᵥ z = y ⬝ᵥ z := by
      intro z
      set x := ((a⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ z with hx
      have hz : ((a : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x = z := by
        rw [hx, Matrix.mulVec_mulVec, ← coe_mul_SL3, mul_inv_cancel, coe_one_SL3,
          Matrix.one_mulVec]
      have h2 := hy _ (sub_mem_commN ha x)
      rw [dotProduct_sub, sub_eq_zero] at h2
      rw [← hz, dualMat_mulVec_dotProduct, h2]
    funext i
    have := h1 (Pi.single i 1)
    simpa [dotProduct_single] using this

theorem exists_add_add_of_inf_eq_bot {H₁ H₂ H₃ : Submodule F (Fin 3 → F)}
    (h : H₁ ⊓ H₂ ⊓ H₃ = ⊥) (y : Fin 3 → F) :
    ∃ y₁ y₂ y₃ : Fin 3 → F, (∀ x ∈ H₁, y₁ ⬝ᵥ x = 0) ∧ (∀ x ∈ H₂, y₂ ⬝ᵥ x = 0) ∧
      (∀ x ∈ H₃, y₃ ⬝ᵥ x = 0) ∧ y = y₁ + y₂ + y₃ := by
  have h1 : (H₁ ⊓ H₂ ⊓ H₃).dualAnnihilator = ⊤ := by rw [h, Submodule.dualAnnihilator_bot]
  rw [Subspace.dualAnnihilator_inf_eq, Subspace.dualAnnihilator_inf_eq] at h1
  set e := dotProductEquiv F (Fin 3) with he
  have hφ : e y ∈ H₁.dualAnnihilator ⊔ H₂.dualAnnihilator ⊔ H₃.dualAnnihilator := by
    rw [h1]; trivial
  obtain ⟨φ₁₂, hφ₁₂, φ₃, hφ₃, hsum⟩ := Submodule.mem_sup.mp hφ
  obtain ⟨φ₁, hφ₁, φ₂, hφ₂, rfl⟩ := Submodule.mem_sup.mp hφ₁₂
  have key : ∀ (φ : Module.Dual F (Fin 3 → F)) (H : Submodule F (Fin 3 → F)),
      φ ∈ H.dualAnnihilator → ∀ x ∈ H, e.symm φ ⬝ᵥ x = 0 := by
    intro φ H hφ x hx
    have h2 := (Submodule.mem_dualAnnihilator φ).mp hφ x hx
    have h3 : e (e.symm φ) x = e.symm φ ⬝ᵥ x := rfl
    rw [← h3, LinearEquiv.apply_symm_apply]
    exact h2
  refine ⟨e.symm φ₁, e.symm φ₂, e.symm φ₃, key _ _ hφ₁, key _ _ hφ₂, key _ _ hφ₃, ?_⟩
  apply e.injective
  rw [map_add, map_add, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply,
    LinearEquiv.apply_symm_apply, hsum]

theorem inf_inf_eq_bot_of_ne {H₁ H₂ H₃ : Submodule F (Fin 3 → F)}
    (h₁ : Module.finrank F H₁ = 2) (h₂ : Module.finrank F H₂ = 2) (h₃ : Module.finrank F H₃ = 2)
    (h12 : H₁ ≠ H₂) (h13 : H₁ ≠ H₃) (hne : H₃ ⊓ H₁ ≠ H₂ ⊓ H₁) : H₁ ⊓ H₂ ⊓ H₃ = ⊥ := by
  have hP : Module.finrank F ↥(H₂ ⊓ H₁) = 1 := finrank_inf_eq_one h₂ h₁ (Ne.symm h12)
  have hP' : Module.finrank F ↥(H₃ ⊓ H₁) = 1 := finrank_inf_eq_one h₃ h₁ (Ne.symm h13)
  have e : H₁ ⊓ H₂ ⊓ H₃ = (H₃ ⊓ H₁) ⊓ (H₂ ⊓ H₁) := by
    ext x
    simp only [Submodule.mem_inf]
    tauto
  rw [e]
  by_contra hne0
  have hpos : Module.finrank F ↥((H₃ ⊓ H₁) ⊓ (H₂ ⊓ H₁)) ≠ 0 :=
    fun h0 => hne0 (Submodule.finrank_eq_zero.mp h0)
  have hle1 := Submodule.finrank_mono (inf_le_left : (H₃ ⊓ H₁) ⊓ (H₂ ⊓ H₁) ≤ H₃ ⊓ H₁)
  have hle2 := Submodule.finrank_mono (inf_le_right : (H₃ ⊓ H₁) ⊓ (H₂ ⊓ H₁) ≤ H₂ ⊓ H₁)
  have e1 := Submodule.eq_of_le_of_finrank_eq (inf_le_left : (H₃ ⊓ H₁) ⊓ (H₂ ⊓ H₁) ≤ H₃ ⊓ H₁)
    (by omega)
  have e2 := Submodule.eq_of_le_of_finrank_eq (inf_le_right : (H₃ ⊓ H₁) ⊓ (H₂ ⊓ H₁) ≤ H₂ ⊓ H₁)
    (by omega)
  exact hne (e1.symm.trans e2)

end Lin

variable {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Fintype F]

namespace Ctx

variable {M T L : Subgroup G} {φ : ↥M →* ↥(StatedSL 3 F)} (c : Ctx M T L φ)
include c

theorem usup_le_zm {δ ρ μ : Vtx (puAmalgam c.hyp.le)} (hδ : IsMVtx _ δ)
    (hρ : (puAmalgam c.hyp.le).treeGraph.Adj δ ρ)
    (hμ : (puAmalgam c.hyp.le).treeGraph.Adj μ ρ) :
    Usup (puAmalgam c.hyp.le) δ ρ ≤ ZM _ μ := by
  obtain ⟨ψ, -, hψ⟩ := exists_natural_Uloc c.hyp c.via hδ
  exact (le_sup_left.trans (c.zh_eq_usup_sup_zloc hψ hδ hρ).ge).trans (zh_le_zm _ hμ)

theorem qv_le_normalizer_usup {δ ρ : Vtx (puAmalgam c.hyp.le)} (hδ : IsMVtx _ δ)
    (hρ : (puAmalgam c.hyp.le).treeGraph.Adj δ ρ) :
    Qv (puAmalgam c.hyp.le) ρ ≤
      Subgroup.normalizer (Usup _ δ ρ : Set (puAmalgam c.hyp.le).Universal) := by
  intro t ht
  rw [Usup, Subgroup.mem_normalizer_iff]
  have key : ∀ s ∈ Qv (puAmalgam c.hyp.le) ρ,
      ⁅Zv (puAmalgam c.hyp.le) δ, Qv _ ρ⁆.map (MulAut.conj s).toMonoidHom ≤
        ⁅Zv (puAmalgam c.hyp.le) δ, Qv _ ρ⁆ := by
    intro s hs
    have hss : s ∈ stab (puAmalgam c.hyp.le) δ := qv_le_stab_of_adj _ hρ.symm hs
    rw [Subgroup.map_commutator]
    refine Subgroup.commutator_mono ?_ ?_
    · rw [zv_of_isMVtx _ hδ]
      exact (map_conj_eq_of_mem_normalizer (stab_le_normalizer_zm _ δ hss)).le
    · exact (map_conj_eq_of_mem_normalizer (Subgroup.le_normalizer hs)).le
  intro w
  constructor
  · intro hw
    exact key t ht ⟨w, hw, rfl⟩
  · intro hw
    have := key t⁻¹ (inv_mem ht) ⟨_, hw, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using this

section GoodPath

variable {p : ℕ → Vtx (puAmalgam c.hyp.le)} {N : ℕ}

theorem not_zm_le_zm_right (hp : IsGoodPath _ p N) {a : ℕ} (ha : Even a) (h8 : 8 ≤ a)
    (haN : a + 8 ≤ N) : ¬ ZM (puAmalgam c.hyp.le) (p (a + 2)) ≤ ZM _ (p a) := by
  intro hle
  have ha6 : Even (a - 6) := (Nat.even_sub (by omega)).mpr (iff_of_true ha (by decide))
  have hc := hp.crit (a - 6) ha6 (by omega)
  rw [show a - 6 + 8 = a + 2 by omega] at hc
  have hα := c.isMVtx_of_isGoodPath hp (k := a) (by omega) ha
  refine hc.2.2 (hle.trans (zm_le_qv_of_dist_lt _ hα ?_))
  rw [tdist_comm, hp.dist_eq' (by omega) (by omega), c.b8]; omega

theorem not_zm_le_zm_left (hp : IsGoodPath _ p N) {a : ℕ} (ha : Even a) (h2 : 2 ≤ a)
    (haN : a + 6 ≤ N) : ¬ ZM (puAmalgam c.hyp.le) (p (a - 2)) ≤ ZM _ (p a) := by
  intro hle
  have ha2 : Even (a - 2) := (Nat.even_sub (by omega)).mpr (iff_of_true ha (by decide))
  have hc := c.isCritical_of_isGoodPath hp ha2 (show a - 2 + 8 ≤ N by omega)
  have hα := c.isMVtx_of_isGoodPath hp (k := a) (by omega) ha
  refine hc.2.2 (hle.trans (zm_le_qv_of_dist_lt _ hα ?_))
  rw [hp.dist_eq' (by omega) (by omega), c.b8]; omega

theorem whv_le_sup_of_branch (hZV : c.HZV) (hp : IsGoodPath _ p N) {a : ℕ} (ha : Even a)
    (h24 : 24 ≤ a) (haN : a + 24 ≤ N) {p' : ℕ → Vtx (puAmalgam c.hyp.le)}
    (hp' : IsGoodPath _ p' N) (hpp' : ∀ i, i ≤ a + 2 → p' i = p i)
    (hU1 : Usup (puAmalgam c.hyp.le) (p (a + 2)) (p' (a + 3)) ≠ Usup _ (p (a + 2)) (p (a + 1)))
    (hU3 : Usup (puAmalgam c.hyp.le) (p (a + 2)) (p' (a + 3)) ⊓ Usup _ (p (a + 2)) (p (a + 1)) ≠
      Usup _ (p (a + 2)) (p (a + 3)) ⊓ Usup _ (p (a + 2)) (p (a + 1))) :
    whv c.hyp (p a) (p (a + 2)) ≤
      (conjCl (stab (puAmalgam c.hyp.le) (p a)) (ZM _ (p (a + 4))) ⊔
          (Vcirc c.hyp.le L (p a) ⊔ ZM _ (p a))) ⊔
        (conjCl (stab (puAmalgam c.hyp.le) (p a)) (ZM _ (p' (a + 4))) ⊔
          (Vcirc c.hyp.le L (p a) ⊔ ZM _ (p a))) := by
  have h := c.hyp
  have : CharP F 2 := c.charP
  obtain ⟨k, rfl⟩ : ∃ k, a = k + 24 := ⟨a - 24, by omega⟩
  have hk : Even k := (Nat.even_add.mp ha).mpr (by decide)
  have hx : Even (k + 20) := hk.add (by decide)
  set Vh := Vcirc h.le L (p (k + 24)) ⊔ ZM (puAmalgam h.le) (p (k + 24)) with hVh
  set S := (conjCl (stab (puAmalgam h.le) (p (k + 24))) (ZM _ (p (k + 24 + 4))) ⊔ Vh) ⊔
    (conjCl (stab (puAmalgam h.le) (p (k + 24))) (ZM _ (p' (k + 24 + 4))) ⊔ Vh) with hS
  have hKVh : stab (puAmalgam h.le) (p (k + 24)) ≤ Subgroup.normalizer (Vh : Set _) :=
    le_normalizer_sup (c.stab_le_normalizer_vcirc _) (stab_le_normalizer_zm _ _)
  have hKS : stab (puAmalgam h.le) (p (k + 24)) ≤ Subgroup.normalizer (S : Set _) :=
    le_normalizer_sup (le_normalizer_sup (S4A.le_normalizer_conjCl _ _) hKVh)
      (le_normalizer_sup (S4A.le_normalizer_conjCl _ _) hKVh)
  refine conjCl_le_of_le_normalizer ?_ hKS
  have hγ := c.isMVtx_of_isGoodPath hp (k := k + 26) (by omega) (hk.add (by decide))
  have hα := c.isMVtx_of_isGoodPath hp (k := k + 24) (by omega) (hk.add (by decide))
  have hμ := c.isMVtx_of_isGoodPath hp (k := k + 28) (by omega) (hk.add (by decide))
  have hμ' := c.isMVtx_of_isGoodPath hp' (k := k + 28) (by omega) (hk.add (by decide))
  have ha25 : (puAmalgam h.le).treeGraph.Adj (p (k + 26)) (p (k + 25)) :=
    (hp.adj (k + 25) (by omega)).symm
  have ha27 : (puAmalgam h.le).treeGraph.Adj (p (k + 26)) (p (k + 27)) := hp.adj (k + 26) (by omega)
  have ha27' : (puAmalgam h.le).treeGraph.Adj (p (k + 26)) (p' (k + 27)) := by
    have := hp'.adj (k + 26) (by omega)
    rwa [hpp' (k + 26) (by omega)] at this
  obtain ⟨ψ, hψs, hψ⟩ := exists_natural_Uloc h c.via hγ
  obtain ⟨d, hd⟩ := c.exists_isSum_vhat hγ hψs hψ
  have hdB := c.isSum_bloc hγ hd
  have hdt := c.dual_eq_true hp hx (by omega) (by omega) hψs hψ hdB
  subst hdt
  set Nn := NatSec.ofIsSum hd with hNn
  have himg2 := c.img_zm_eq' hp hx (by omega) (by omega) hψs hψ hd
    (c.zm_le_vhat_right hZV hp (a := k + 26) (hk.add (by decide)) (by omega) (by omega))
    (c.usup_le_zm hμ (hp.adj (k + 27) (by omega)).symm ha27)
    (c.not_zm_le_zm_right hp (a := k + 26) (hk.add (by decide)) (by omega) (by omega))
  have hZ3V := c.zm_le_vhat_right hZV hp' (a := k + 26) (hk.add (by decide)) (by omega) (by omega)
  have hHB3 := c.usup_le_zm hμ' (hp'.adj (k + 27) (by omega)).symm (hp'.adj (k + 26) (by omega))
  have hZ3ne := c.not_zm_le_zm_right hp' (a := k + 26) (hk.add (by decide)) (by omega) (by omega)
  have key3 : ∀ (ψ' : ↥(stab (puAmalgam h.le) (p' (k + 26))) →* ↥(StatedSL 3 F)),
      Function.Surjective ψ' →
      ∀ (hψ' : IsSumOfNaturalModulesVia (stab _ (p' (k + 26))) (Uloc h.le L (p' (k + 26))) ⊥ ψ'
        false 1)
      (hd' : IsSumOfNaturalModulesVia (stab _ (p' (k + 26)))
        (Vcirc h.le L (p' (k + 26)) ⊔ ZM _ (p' (k + 26))) (ZM _ (p' (k + 26))) ψ' true 1),
      ∀ y : Fin 3 → F,
        (∀ a ∈ natImage ψ' (Qv (puAmalgam h.le) (p' (k + 27))), dualMat a *ᵥ y = y) ↔
          y ∈ (NatSec.ofIsSum hd').img (ZM (puAmalgam h.le) (p' (k + 28))) :=
    fun ψ' hψ's hψ' hd' => c.img_zm_eq' hp' hx (by omega) (by omega) hψ's hψ' hd' hZ3V hHB3 hZ3ne
  rw [hpp' (k + 26) (by omega)] at key3
  have himg3 := key3 ψ hψs hψ hd
  have hr := c.isGoodPath_rev hp (m := k + 36) (hk.add (by decide)) (by omega) (by omega)
  have himg1 := c.img_zm_eq' hr (x := 4) (by decide) le_rfl (by omega) (ψ := ψ) hψs hψ hd
    (c.zm_le_vhat_left' hZV hp (a := k + 26) (hk.add (by decide)) (by omega) (by omega))
    (c.usup_le_zm hα (hp.adj (k + 24) (by omega)) ha25)
    (c.not_zm_le_zm_left hp (a := k + 26) (hk.add (by decide)) (by omega) (by omega))
  have hcoord : ∀ ρ, (puAmalgam h.le).treeGraph.Adj (p (k + 26)) ρ →
      ∀ v : ↥(Uloc h.le L (p (k + 26))), (v : (puAmalgam h.le).Universal) ∈ Usup _ (p (k + 26)) ρ ↔
        natVec hψ v ∈ commN (natImage ψ (Qv (puAmalgam h.le) ρ)) := fun ρ hρ v => by
    rw [c.mem_usup_iff hψ hγ hρ v, (c.fixN_eq_commN_qv hψ hγ hρ).1]
  have hUs : ∀ ρ, (puAmalgam h.le).treeGraph.Adj (p (k + 26)) ρ →
      Usup (puAmalgam h.le) (p (k + 26)) ρ ≤ Uloc h.le L (p (k + 26)) := fun ρ hρ => by
    rw [c.usup_eq_uloc_inf_centralizer hψ hγ hρ]; exact inf_le_left
  have hrank : ∀ ρ, (puAmalgam h.le).treeGraph.Adj (p (k + 26)) ρ →
      Module.finrank F ↥(commN (natImage ψ (Qv (puAmalgam h.le) ρ))) = 2 := fun ρ hρ =>
    (c.natImage_qv_props hγ hρ hψ).2.2.2
  have h12 : commN (natImage ψ (Qv (puAmalgam h.le) (p (k + 25)))) ≠
      commN (natImage ψ (Qv (puAmalgam h.le) (p (k + 27)))) := by
    intro heq
    have hzh := c.zh_ne_of_isGoodPath hp (y := k + 26) (hk.add (by decide)) (by omega) (by omega)
    rw [show k + 26 - 1 = k + 25 by omega, show k + 26 + 1 = k + 27 by omega] at hzh
    apply hzh
    rw [← c.usup_eq_iff_zh_eq hψ hγ ha25 ha27]
    exact (eq_iff_of_natVec_iff hψ (hUs _ ha25) (hUs _ ha27) (hcoord _ ha25)
      (hcoord _ ha27)).mpr heq
  have h13 : commN (natImage ψ (Qv (puAmalgam h.le) (p (k + 25)))) ≠
      commN (natImage ψ (Qv (puAmalgam h.le) (p' (k + 27)))) := by
    intro heq
    exact hU1 ((eq_iff_of_natVec_iff hψ (hUs _ ha27') (hUs _ ha25) (hcoord _ ha27')
      (hcoord _ ha25)).mpr heq.symm)
  have hne : commN (natImage ψ (Qv (puAmalgam h.le) (p' (k + 27)))) ⊓
      commN (natImage ψ (Qv (puAmalgam h.le) (p (k + 25)))) ≠
      commN (natImage ψ (Qv (puAmalgam h.le) (p (k + 27)))) ⊓
      commN (natImage ψ (Qv (puAmalgam h.le) (p (k + 25)))) := by
    intro heq
    refine hU3 ((eq_iff_of_natVec_iff hψ (inf_le_left.trans (hUs _ ha27'))
      (inf_le_left.trans (hUs _ ha27)) (fun v => ?_) (fun v => ?_)).mpr heq)
    · rw [Subgroup.mem_inf, Submodule.mem_inf, hcoord _ ha27', hcoord _ ha25]
    · rw [Subgroup.mem_inf, Submodule.mem_inf, hcoord _ ha27, hcoord _ ha25]
  have hbot := inf_inf_eq_bot_of_ne (hrank _ ha25) (hrank _ ha27) (hrank _ ha27') h12 h13 hne
  have hZαS : ZM (puAmalgam h.le) (p (k + 24)) ≤ S :=
    (le_sup_right.trans le_sup_right).trans le_sup_left
  have hZμS : ZM (puAmalgam h.le) (p (k + 28)) ≤ S :=
    ((S4A.le_conjCl _ _).trans le_sup_left).trans le_sup_left
  have hZμ'S : ZM (puAmalgam h.le) (p' (k + 28)) ≤ S :=
    ((S4A.le_conjCl _ _).trans le_sup_left).trans le_sup_right
  have hZγS : ZM (puAmalgam h.le) (p (k + 26)) ≤ S :=
    ((c.zm_le_vhat_right hZV hp (a := k + 24) (hk.add (by decide)) (by omega) (by omega)).trans
      le_sup_right).trans le_sup_left
  intro v hv
  obtain ⟨y₁, y₂, y₃, hy₁, hy₂, hy₃, hy⟩ := exists_add_add_of_inf_eq_bot hbot (Nn.coord v)
  obtain ⟨z₁, hz₁Z, hz₁V, hz₁c⟩ := Nn.mem_img.mp ((himg1 y₁).mp ((dualMat_fixed_iff _ y₁).mpr hy₁))
  obtain ⟨z₂, hz₂Z, hz₂V, hz₂c⟩ := Nn.mem_img.mp ((himg2 y₂).mp ((dualMat_fixed_iff _ y₂).mpr hy₂))
  obtain ⟨z₃, hz₃Z, hz₃V, hz₃c⟩ := Nn.mem_img.mp ((himg3 y₃).mp ((dualMat_fixed_iff _ y₃).mpr hy₃))
  have hzV : z₁ * z₂ * z₃ ∈ Vcirc h.le L (p (k + 26)) ⊔ ZM (puAmalgam h.le) (p (k + 26)) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hz₁V hz₂V) hz₃V
  have hc : Nn.coord (z₁ * z₂ * z₃) = Nn.coord v := by
    rw [Nn.coord_mul (Subgroup.mul_mem _ hz₁V hz₂V) hz₃V, Nn.coord_mul hz₁V hz₂V, hz₁c, hz₂c,
      hz₃c, hy]
  have hw := Nn.inv_mul_mem_of_coord_eq hzV hv hc
  have e : v = z₁ * z₂ * z₃ * ((z₁ * z₂ * z₃)⁻¹ * v) := by group
  rw [e]
  exact S.mul_mem (S.mul_mem (S.mul_mem (hZαS hz₁Z) (hZμS hz₂Z)) (hZμ'S hz₃Z)) (hZγS hw)

end GoodPath

end Ctx

end CFSG.Quasithin.MS93.S45
