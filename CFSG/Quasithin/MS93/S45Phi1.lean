module

public import CFSG.Quasithin.MS93.S45Y2

public section

namespace CFSG.Quasithin.MS93.S45

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix

section Lin

variable {𝔾 : Type} [Group 𝔾] {F : Type} [Field F]

theorem coord_dot_eq_zero_of_commutator_mem {K X Z A : Subgroup 𝔾}
    {ψ : ↥K →* ↥(StatedSL 3 F)} (hd : IsSumOfNaturalModulesVia K X Z ψ true 1) {x : 𝔾}
    (hx : x ∈ X) (hxa : ∀ a : ↥K, (a : 𝔾) ∈ A → ⁅x, (a : 𝔾)⁆ ∈ Z) :
    ∀ y ∈ commN (natImage ψ A), (NatSec.ofIsSum hd).coord x ⬝ᵥ y = 0 := by
  set N := NatSec.ofIsSum hd
  rw [← dualMat_fixed_iff]
  intro g hg
  obtain ⟨a, haA, rfl⟩ := mem_natImage.mp hg
  have hax : (a : 𝔾) * x⁻¹ * (a : 𝔾)⁻¹ ∈ X := N.conj_mem a (X.inv_mem hx)
  have e : ⁅x, (a : 𝔾)⁆ = x * ((a : 𝔾) * x⁻¹ * (a : 𝔾)⁻¹) := by
    simp only [commutatorElement_def]
    group
  have h0 := (N.coord_eq_zero_iff (X.mul_mem hx hax)).mpr (e ▸ hxa a haA)
  rw [N.coord_mul hx hax, N.coord_conj a (X.inv_mem hx), N.coord_inv hx, natAct_true,
    Matrix.mulVec_neg] at h0
  exact (add_neg_eq_zero.mp h0).symm

theorem eq_zero_of_dot_eq_zero_of_ne [Finite F] {H₁ H₂ : Submodule F (Fin 3 → F)}
    (h₁ : Module.finrank F H₁ = 2) (h₂ : Module.finrank F H₂ = 2) (hne : H₁ ≠ H₂)
    {y : Fin 3 → F} (hy₁ : ∀ x ∈ H₁, y ⬝ᵥ x = 0) (hy₂ : ∀ x ∈ H₂, y ⬝ᵥ x = 0) : y = 0 := by
  have htop : H₁ ⊔ H₂ = ⊤ := by
    have hlt : H₁ < H₁ ⊔ H₂ := by
      refine lt_of_le_of_ne le_sup_left fun heq => hne ?_
      have hle : H₂ ≤ H₁ := heq ▸ le_sup_right
      exact (Submodule.eq_of_le_of_finrank_le hle (by omega)).symm
    have h3 : Module.finrank F ↥(H₁ ⊔ H₂) = 3 := by
      have := Submodule.finrank_lt_finrank_of_lt hlt
      have hle := Submodule.finrank_le (H₁ ⊔ H₂)
      simp only [Module.finrank_fin_fun] at hle
      omega
    exact Submodule.eq_top_of_finrank_eq (by rw [h3]; simp)
  have hall : ∀ x : Fin 3 → F, y ⬝ᵥ x = 0 := by
    intro x
    have hx : x ∈ H₁ ⊔ H₂ := htop ▸ Submodule.mem_top
    obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp hx
    rw [dotProduct_add, hy₁ u hu, hy₂ v hv, add_zero]
  funext i
  have := hall (Pi.single i 1)
  simpa [dotProduct_single] using this

theorem mem_of_commutator_mem_two [Finite F] {K W₁ W₂ Z A B : Subgroup 𝔾}
    {ψ : ↥K →* ↥(StatedSL 3 F)} (h₁ : IsSumOfNaturalModulesVia K W₁ Z ψ true 1)
    (h₂ : IsSumOfNaturalModulesVia K W₂ Z ψ true 1) (hinf : W₁ ⊓ W₂ = Z) (hW₁K : W₁ ≤ K)
    (hA2 : Module.finrank F ↥(commN (natImage ψ A)) = 2)
    (hB2 : Module.finrank F ↥(commN (natImage ψ B)) = 2)
    (hAB : commN (natImage ψ A) ≠ commN (natImage ψ B)) {x : 𝔾} (hx : x ∈ W₁ ⊔ W₂)
    (hxA : ∀ a ∈ A, ⁅x, a⁆ ∈ Z) (hxB : ∀ b ∈ B, ⁅x, b⁆ ∈ Z) : x ∈ Z := by
  have hKZ : K ≤ Subgroup.normalizer (Z : Set 𝔾) := by
    rw [← hinf]
    exact le_normalizer_inf h₁.1 h₂.1
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right W₁ W₂
    (hW₁K.trans h₂.1)] at hx
  obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := hx
  have key : ∀ a ∈ K, ⁅x₁ * x₂, a⁆ ∈ Z → ⁅x₁⁻¹, a⁆ ∈ Z ∧ ⁅x₂, a⁆ ∈ Z := by
    intro a ha hz
    have hy₁ : a * x₁ * a⁻¹ ∈ W₁ := (Subgroup.mem_normalizer_iff.mp (h₁.1 ha) _).mp hx₁
    have hy₂ : a * x₂ * a⁻¹ ∈ W₂ := (Subgroup.mem_normalizer_iff.mp (h₂.1 ha) _).mp hx₂
    have hZW₁ : Z ≤ W₁ := h₁.2.1
    have e : x₁⁻¹ * ⁅x₁ * x₂, a⁆ * (a * x₁ * a⁻¹) = x₂ * (a * x₂ * a⁻¹)⁻¹ := by
      simp only [commutatorElement_def]
      group
    have hm : x₂ * (a * x₂ * a⁻¹)⁻¹ ∈ W₁ ⊓ W₂ := Subgroup.mem_inf.mpr
      ⟨e ▸ W₁.mul_mem (W₁.mul_mem (W₁.inv_mem hx₁) (hZW₁ hz)) hy₁,
        W₂.mul_mem hx₂ (W₂.inv_mem hy₂)⟩
    rw [hinf] at hm
    have h2 : ⁅x₂, a⁆ ∈ Z := by
      rwa [show x₂ * (a * x₂ * a⁻¹)⁻¹ = ⁅x₂, a⁆ by simp only [commutatorElement_def]; group]
        at hm
    refine ⟨?_, h2⟩
    have hz' : x₁⁻¹ * ⁅x₁ * x₂, a⁆ * x₁ ∈ Z := by
      have := (Subgroup.mem_normalizer_iff.mp (hKZ (hW₁K (W₁.inv_mem hx₁))) _).mp hz
      rwa [inv_inv] at this
    have e2 : ⁅x₁⁻¹, a⁆ = (x₁⁻¹ * ⁅x₁ * x₂, a⁆ * x₁)⁻¹ * (x₂ * (a * x₂ * a⁻¹)⁻¹) := by
      rw [← e]
      simp only [commutatorElement_def]
      group
    rw [e2]
    exact Z.mul_mem (Z.inv_mem hz') (hinf ▸ hm)
  set N₁ := NatSec.ofIsSum h₁
  set N₂ := NatSec.ofIsSum h₂
  have hx₁' : x₁⁻¹ ∈ Z := by
    rw [← N₁.coord_eq_zero_iff (W₁.inv_mem hx₁)]
    refine eq_zero_of_dot_eq_zero_of_ne hA2 hB2 hAB ?_ ?_
    · exact coord_dot_eq_zero_of_commutator_mem h₁ (W₁.inv_mem hx₁) fun a ha =>
        (key a a.2 (hxA a ha)).1
    · exact coord_dot_eq_zero_of_commutator_mem h₁ (W₁.inv_mem hx₁) fun a ha =>
        (key a a.2 (hxB a ha)).1
  have hx₂' : x₂ ∈ Z := by
    rw [← N₂.coord_eq_zero_iff hx₂]
    refine eq_zero_of_dot_eq_zero_of_ne hA2 hB2 hAB ?_ ?_
    · exact coord_dot_eq_zero_of_commutator_mem h₂ hx₂ fun a ha => (key a a.2 (hxA a ha)).2
    · exact coord_dot_eq_zero_of_commutator_mem h₂ hx₂ fun a ha => (key a a.2 (hxB a ha)).2
  exact Z.mul_mem (by simpa using Z.inv_mem hx₁') hx₂'

end Lin

variable {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Fintype F]

namespace Ctx

variable {M T L : Subgroup G} {φ : ↥M →* ↥(StatedSL 3 F)} (c : Ctx M T L φ)
include c

section GoodPath

variable {p p' : ℕ → Vtx (puAmalgam c.hyp.le)} {N : ℕ}

theorem sq_mem_commutator_vv (δ : Vtx (puAmalgam c.hyp.le)) {v : (puAmalgam c.hyp.le).Universal}
    (hv : v ∈ Vv (puAmalgam c.hyp.le) δ) :
    v ^ 2 ∈ ⁅Vv (puAmalgam c.hyp.le) δ, Vv (puAmalgam c.hyp.le) δ⁆ := by
  have h := c.hyp
  have hle : Vv (puAmalgam h.le) δ ≤ sqSub' (Vv _ δ) ⁅Vv _ δ, Vv _ δ⁆ le_rfl
      (le_normalizer_commutator Subgroup.le_normalizer Subgroup.le_normalizer) := by
    refine iSup₂_le fun ρ hρ => le_sqSub' (zv_le_vi _ hρ) fun z hz => ?_
    have h2 : z ^ 2 = 1 := by
      by_cases hM : IsMVtx (puAmalgam h.le) ρ
      · rw [zv_of_isMVtx _ hM] at hz
        exact (isElemAbelian_zm _ h.hyp20 c.bpos hM).2 z hz
      · rw [zv_of_not_isMVtx _ hM] at hz
        exact (isElemAbelian_xm _ ρ).2 z hz
    rw [h2]
    exact one_mem _
  exact (hle hv).2

theorem sq_eq_one_of_mem_vhat (hZV : c.HZV) (hp : IsGoodPath _ p N) {a : ℕ} (ha : Even a)
    (h34 : 34 ≤ a) (haN : a + 14 ≤ N) {v : (puAmalgam c.hyp.le).Universal}
    (hv : v ∈ Vcirc c.hyp.le L (p a) ⊔ ZM _ (p a)) : v ^ 2 = 1 := by
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
  set Vh := Vcirc h.le L (p (k + 34)) ⊔ ZM (puAmalgam h.le) (p (k + 34)) with hVh
  have hVhV : Vh ≤ Vv (puAmalgam h.le) (p (k + 34)) := c.vhat_le_vv hα
  have hab : ∀ x ∈ Vh, ∀ y ∈ Vh, x * y = y * x := by
    have hC := ((c.vhat_le_whv' hZV hp ha (by omega) (by omega)).trans
      (c.whv_le_centralizer_vv hγ hd2)).trans (Subgroup.centralizer_le hVhV)
    intro x hx y hy
    exact (Subgroup.mem_centralizer_iff.mp (hC hy) x hx)
  have hsq : ∀ x ∈ Vh, x ^ 2 ∈ Zloc h.le L (p (k + 34)) := fun x hx =>
    (Subgroup.commutator_mono le_rfl (c.vv_le_qv' hα)).trans (c.commutator_vv_qv_le_zloc hα)
      (c.sq_mem_commutator_vv _ (hVhV hx))
  have hZc := zloc_le_centralizer_stab h c.full hα
  set K : Subgroup (puAmalgam h.le).Universal :=
    { carrier := {x | x ∈ Vh ∧ x ^ 2 = 1}
      one_mem' := ⟨Vh.one_mem, one_pow 2⟩
      mul_mem' := fun {x y} hx hy => ⟨Vh.mul_mem hx.1 hy.1, by
        rw [(show Commute x y from hab x hx.1 y hy.1).mul_pow 2, hx.2, hy.2, one_mul]⟩
      inv_mem' := fun {x} hx => ⟨Vh.inv_mem hx.1, by rw [inv_pow, hx.2, inv_one]⟩ } with hK
  have hKL : ⁅Vh, Ltil h.le L (p (k + 34))⁆ ≤ K := by
    rw [Subgroup.commutator_le]
    intro x hx l hl
    have hls : l ∈ stab (puAmalgam h.le) (p (k + 34)) := ltil_le_stab h _ hl
    have hlx : l * x⁻¹ * l⁻¹ ∈ Vh := (Subgroup.mem_normalizer_iff.mp
      (le_normalizer_sup (c.stab_le_normalizer_vcirc _) (stab_le_normalizer_zm _ _) hls) _).mp
      (Vh.inv_mem hx)
    have e : ⁅x, l⁆ = x * (l * x⁻¹ * l⁻¹) := by
      simp only [commutatorElement_def]; group
    refine ⟨e ▸ Vh.mul_mem hx hlx, ?_⟩
    rw [e, (show Commute x (l * x⁻¹ * l⁻¹) from hab x hx _ hlx).mul_pow 2]
    have h1 : (l * x⁻¹ * l⁻¹) ^ 2 = l * (x ^ 2)⁻¹ * l⁻¹ := by
      rw [sq, sq]; group
    have hc : Commute l (x ^ 2) := Subgroup.mem_centralizer_iff.mp (hZc (hsq x hx)) l hls
    rw [h1, hc.inv_right.eq, mul_inv_cancel_right, mul_inv_cancel]
  have hZK : ZM (puAmalgam h.le) (p (k + 34)) ≤ K := fun z hz =>
    ⟨Subgroup.mem_sup_right hz, (isElemAbelian_zm _ h20 c.bpos hα).2 z hz⟩
  have hVL : stab (puAmalgam h.le) (p (k + 34)) ≤
      Subgroup.normalizer ((⁅Vh, Ltil h.le L (p (k + 34))⁆ : Subgroup _) : Set _) :=
    le_normalizer_commutator (le_normalizer_sup (c.stab_le_normalizer_vcirc _)
      (stab_le_normalizer_zm _ _)) (stab_le_normalizer_ltil h _)
  have hcov := c.sup_inf_eq_of_dual hα hψs hψ hd hVL le_rfl
  have : v ∈ (⁅Vh, Ltil h.le L (p (k + 34))⁆ ⊓ Vh) ⊔ ZM _ (p (k + 34)) := hcov.symm ▸ hv
  exact (sup_le (inf_le_left.trans hKL) hZK this).2

theorem sq_mem_commutator_vsix (hZV : c.HZV) (hp : IsGoodPath _ p N) {a : ℕ} (ha : Even a)
    (h34 : 34 ≤ a) (haN : a + 14 ≤ N) {x : (puAmalgam c.hyp.le).Universal}
    (hx : x ∈ conjCl (stab (puAmalgam c.hyp.le) (p a)) (whv c.hyp (p (a + 2)) (p a))) :
    x ^ 2 ∈ ⁅conjCl (stab (puAmalgam c.hyp.le) (p a)) (whv c.hyp (p (a + 2)) (p a)),
      conjCl (stab (puAmalgam c.hyp.le) (p a)) (whv c.hyp (p (a + 2)) (p a))⁆ := by
  have h := c.hyp
  set V6 := conjCl (stab (puAmalgam h.le) (p a)) (whv h (p (a + 2)) (p a)) with hV6
  have hle : V6 ≤ sqSub' V6 ⁅V6, V6⁆ le_rfl
      (le_normalizer_commutator Subgroup.le_normalizer Subgroup.le_normalizer) := by
    refine iSup₂_le fun t ht => ?_
    rw [Subgroup.map_le_iff_le_comap]
    refine iSup₂_le fun u hu => ?_
    rw [Subgroup.map_le_iff_le_comap]
    intro v hv
    have hv2 : v ^ 2 = 1 := c.sq_eq_one_of_mem_vhat hZV hp ha h34 haN hv
    have hmemW : u * v * u⁻¹ ∈ whv h (p (a + 2)) (p a) :=
      le_iSup₂_of_le (f := fun s (_ : s ∈ stab (puAmalgam h.le) (p (a + 2))) =>
        (Vcirc h.le L (p a) ⊔ ZM _ (p a)).map (MulAut.conj s).toMonoidHom) u hu le_rfl
        ⟨v, hv, rfl⟩
    have hmem : t * (u * v * u⁻¹) * t⁻¹ ∈ V6 :=
      le_iSup₂_of_le (f := fun s (_ : s ∈ stab (puAmalgam h.le) (p a)) =>
        (whv h (p (a + 2)) (p a)).map (MulAut.conj s).toMonoidHom) t ht le_rfl
        ⟨_, hmemW, rfl⟩
    refine ⟨hmem, ?_⟩
    have e : (t * (u * v * u⁻¹) * t⁻¹) ^ 2 = t * u * v ^ 2 * u⁻¹ * t⁻¹ := by
      rw [sq, sq]; group
    show (MulAut.conj t).toMonoidHom ((MulAut.conj u).toMonoidHom v) ^ 2 ∈ _
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [e, hv2, mul_one, mul_inv_cancel_right, mul_inv_cancel]
    exact one_mem _
  exact (hle hx).2

end GoodPath

end Ctx

end CFSG.Quasithin.MS93.S45
