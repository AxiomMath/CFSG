module

public import CFSG.Quasithin.MS93.S45Rev
public import CFSG.Quasithin.MS93.S46T
public import CFSG.Quasithin.MS93.S45W

public section

namespace CFSG.Quasithin.MS93.S45

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix

section Aux

variable {𝔾 : Type} [Group 𝔾]

theorem conjCl_mono {H K K' : Subgroup 𝔾} (hK : K ≤ K') : conjCl H K ≤ conjCl H K' :=
  iSup₂_le fun g hg => le_iSup₂_of_le (f := fun g (_ : g ∈ H) =>
    K'.map (MulAut.conj g).toMonoidHom) g hg (Subgroup.map_mono hK)

theorem conjCl_le_of_le_normalizer {H K N : Subgroup 𝔾} (hK : K ≤ N)
    (hH : H ≤ Subgroup.normalizer (N : Set 𝔾)) : conjCl H K ≤ N :=
  iSup₂_le fun _ hg => (Subgroup.map_mono hK).trans (map_conj_eq_of_mem_normalizer (hH hg)).le

theorem relIndex_sup_eq {H N : Subgroup 𝔾} (h : H ≤ Subgroup.normalizer (N : Set 𝔾)) :
    N.relIndex (H ⊔ N) = N.relIndex H := by
  have := Subgroup.normal_subgroupOf_of_le_normalizer h
  have := Subgroup.normal_subgroupOf_sup_of_le_normalizer h
  exact Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalizerQuotient H N h).toEquiv.symm

@[expose] def sqSub (W Z : Subgroup 𝔾) (hWW : ⁅W, W⁆ ≤ Z)
    (hZ : Z ≤ Subgroup.centralizer (W : Set 𝔾)) : Subgroup 𝔾 where
  carrier := {x | x ∈ W ∧ x ^ 2 ∈ Z}
  one_mem' := ⟨W.one_mem, by rw [one_pow]; exact Z.one_mem⟩
  mul_mem' := fun {x y} hx hy => by
    refine ⟨W.mul_mem hx.1 hy.1, ?_⟩
    have hc : ⁅y, x⁆ ∈ Z := hWW (Subgroup.commutator_mem_commutator hy.1 hx.1)
    have h1 : ⁅y, x⁆ * x = x * ⁅y, x⁆ := (Subgroup.mem_centralizer_iff.mp (hZ hc) x hx.1).symm
    have e : (x * y) ^ 2 = ⁅y, x⁆ * x ^ 2 * y ^ 2 := by
      calc (x * y) ^ 2 = x * (y * x) * y := by rw [sq]; group
        _ = x * (⁅y, x⁆ * x * y) * y := by rw [commutatorElement_def]; group
        _ = (x * ⁅y, x⁆) * x * y * y := by group
        _ = (⁅y, x⁆ * x) * x * y * y := by rw [h1]
        _ = ⁅y, x⁆ * x ^ 2 * y ^ 2 := by rw [sq, sq]; group
    rw [e]
    exact Z.mul_mem (Z.mul_mem hc hx.2) hy.2
  inv_mem' := fun {x} hx => ⟨W.inv_mem hx.1, by rw [inv_pow]; exact Z.inv_mem hx.2⟩

theorem le_sqSub {W Z A : Subgroup 𝔾} {hWW : ⁅W, W⁆ ≤ Z}
    {hZ : Z ≤ Subgroup.centralizer (W : Set 𝔾)} (hAW : A ≤ W) (hA : ∀ a ∈ A, a ^ 2 = 1) :
    A ≤ sqSub W Z hWW hZ := fun a ha => ⟨hAW ha, by rw [hA a ha]; exact Z.one_mem⟩

end Aux

section Gen

variable {𝔾 : Type} [Group 𝔾] {F : Type} [Field F]

private def centMod (K W Z : Subgroup 𝔾) (hKZ : K ≤ Subgroup.normalizer (Z : Set 𝔾)) :
    Subgroup 𝔾 where
  carrier := {g | g ∈ K ∧ ∀ w ∈ W, ⁅w, g⁆ ∈ Z}
  one_mem' := ⟨K.one_mem, fun w _ => by rw [commutatorElement_one_right]; exact Z.one_mem⟩
  mul_mem' := fun {g g'} hg hg' => ⟨K.mul_mem hg.1 hg'.1, fun w hw => by
    rw [S46.commutatorElement_mul_right_conj]
    exact Z.mul_mem (hg.2 w hw) ((Subgroup.mem_normalizer_iff.mp (hKZ hg.1) _).mp (hg'.2 w hw))⟩
  inv_mem' := fun {g} hg => ⟨K.inv_mem hg.1, fun w hw => by
    have e : ⁅w, g⁻¹⁆ = g⁻¹ * ⁅w, g⁆⁻¹ * g⁻¹⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (hKZ (K.inv_mem hg.1)) _).mp (Z.inv_mem (hg.2 w hw))⟩

theorem commutator_mem_of_natImage {K Q N Z T : Subgroup 𝔾} {ψ : ↥K →* ↥(StatedSL 3 F)}
    (hψ : Function.Surjective ψ) (hker : ∀ k : ↥K, toSL3 ψ k = 1 ↔ (k : 𝔾) ∈ Q)
    (hQK : Q ≤ K) (hKZ : K ≤ Subgroup.normalizer (Z : Set 𝔾))
    (hKN : K ≤ Subgroup.normalizer (N : Set 𝔾)) (hTK : T ≤ K)
    (hT : natImage ψ T = rootGroup 1 0 ⊔ rootGroup 2 0) (hNQ : ⁅N, Q⁆ ≤ Z) (hNT : ⁅N, T⁆ ≤ Z)
    {x : 𝔾} (hx : x ∈ N) {l : 𝔾} (hl : l ∈ K) : ⁅x, l⁆ ∈ Z := by
  have hTC : T ≤ centMod K N Z hKZ := fun g hg =>
    ⟨hTK hg, fun w hw => hNT (Subgroup.commutator_mem_commutator hw hg)⟩
  have hQC : Q ≤ centMod K N Z hKZ := fun g hg =>
    ⟨hQK hg, fun w hw => hNQ (Subgroup.commutator_mem_commutator hw hg)⟩
  have hCn : ∀ k ∈ K, ∀ g ∈ centMod K N Z hKZ, k * g * k⁻¹ ∈ centMod K N Z hKZ := by
    intro k hk g hg
    refine ⟨K.mul_mem (K.mul_mem hk hg.1) (K.inv_mem hk), fun w hw => ?_⟩
    have hw' : k⁻¹ * w * k⁻¹⁻¹ ∈ N :=
      (Subgroup.mem_normalizer_iff.mp (hKN (K.inv_mem hk)) w).mp hw
    have e : ⁅w, k * g * k⁻¹⁆ = k * ⁅k⁻¹ * w * k⁻¹⁻¹, g⁆ * k⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (hKZ hk) _).mp (hg.2 _ hw')
  have hD : natImage ψ (centMod K N Z hKZ) = ⊤ := by
    refine S46.eq_top_of_normal_of_le (fun s d hd => ?_) ?_
    · obtain ⟨k, rfl⟩ := toSL3_surjective hψ s
      obtain ⟨g, hgC, rfl⟩ := mem_natImage.mp hd
      exact mem_natImage.mpr ⟨k * g * k⁻¹, hCn k k.2 g hgC, by simp⟩
    · rw [← hT]
      intro g hg
      obtain ⟨t, htT, rfl⟩ := mem_natImage.mp hg
      exact mem_natImage.mpr ⟨t, hTC htT, rfl⟩
  obtain ⟨g, hgC, hg⟩ := mem_natImage.mp (hD ▸ Subgroup.mem_top (toSL3 ψ ⟨l, hl⟩))
  have hq : ((g⁻¹ * ⟨l, hl⟩ : ↥K) : 𝔾) ∈ Q := by
    rw [← hker]
    rw [map_mul, map_inv, hg, inv_mul_cancel]
  have hlC : l ∈ centMod K N Z hKZ := by
    have e : l = (g : 𝔾) * ((g⁻¹ * ⟨l, hl⟩ : ↥K) : 𝔾) := by simp
    rw [e]
    exact Subgroup.mul_mem _ hgC (hQC hq)
  exact hlC.2 x hx

end Gen

variable {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Fintype F]

namespace Ctx

variable {M T L : Subgroup G} {φ : ↥M →* ↥(StatedSL 3 F)} (c : Ctx M T L φ)
include c

theorem vhat_le_vv {δ : Vtx (puAmalgam c.hyp.le)} (hδ : IsMVtx _ δ) :
    Vcirc c.hyp.le L δ ⊔ ZM _ δ ≤ Vv (puAmalgam c.hyp.le) δ := by
  refine sup_le (c.vcirc_le_vv δ) ?_
  have := zv_le_vi (puAmalgam c.hyp.le) (δ := δ) (ρ := δ) (i := 2) (by simp)
  rwa [zv_of_isMVtx _ hδ] at this

theorem whv_le_vi {δ μ : Vtx (puAmalgam c.hyp.le)} (hμ : IsMVtx _ μ)
    (hd : (puAmalgam c.hyp.le).treeGraph.dist δ μ = 2) :
    whv c.hyp δ μ ≤ Vi (puAmalgam c.hyp.le) δ 4 := by
  refine conjCl_le_of_le_normalizer ((c.vhat_le_vv hμ).trans (vi_le_vi _ ?_))
    (stab_le_normalizer_of_smul _ (F := fun ρ => Vi _ ρ 4) (fun g ρ => vi_smul _ g ρ 4) δ)
  rw [tdist_comm, hd]

theorem whv_le_centralizer_vv {δ μ : Vtx (puAmalgam c.hyp.le)} (hμ : IsMVtx _ μ)
    (hd : (puAmalgam c.hyp.le).treeGraph.dist δ μ = 2) :
    whv c.hyp δ μ ≤ Subgroup.centralizer (Vv (puAmalgam c.hyp.le) δ : Set _) :=
  (c.whv_le_vi hμ hd).trans (vi_le_centralizer_vi _ c.hyp.hyp20 c.bpos (by rw [c.b8]; simp))

theorem exists_coord_qv {δ β : Vtx (puAmalgam c.hyp.le)} (hδ : IsMVtx _ δ)
    (hβ : (puAmalgam c.hyp.le).treeGraph.Adj δ β) :
    ∃ ψ : ↥(stab (puAmalgam c.hyp.le) δ) →* ↥(StatedSL 3 F), Function.Surjective ψ ∧
      IsSumOfNaturalModulesVia (stab _ δ) (Uloc c.hyp.le L δ) ⊥ ψ false 1 ∧
      natImage ψ (Qv (puAmalgam c.hyp.le) β) = rootGroup 1 0 ⊔ rootGroup 2 0 := by
  have h := c.hyp
  have : CharP F 2 := c.charP
  obtain ⟨ψ₀, hψ₀s, hψ₀⟩ := exists_natural_Uloc h c.via hδ
  obtain ⟨hA2, -, -, -⟩ := c.natImage_qv_props hδ hβ hψ₀
  obtain ⟨x, hx⟩ := exists_conj_le_sStar hA2
  have hψ₁ := S4A.isSumOfNaturalModulesVia_conjSL hψ₀ x
  set E := natImage (S4A.conjSL x ψ₀) (Qv (puAmalgam h.le) β) with hE
  have hEs : E ≤ sStar := by rw [hE, S46.natImage_conjSL]; exact hx
  obtain ⟨-, hcard, hfc, h2⟩ := c.natImage_qv_props hδ hβ hψ₁
  rw [← hE] at hcard hfc h2
  have hfc' : Nat.card (fixN E) = Nat.card F ^ 2 := by rw [card_fixN, hfc, h2]
  have hEq : E = qLn := S46.QjAux.eq_qLn_of_card hEs hcard hfc'
  refine ⟨S4A.conjSL cyc (S4A.conjSL x ψ₀), S4A.conjSL_surjective (S4A.conjSL_surjective hψ₀s),
    S4A.isSumOfNaturalModulesVia_conjSL hψ₁ cyc, ?_⟩
  rw [S46.natImage_conjSL, ← hE, hEq, ← ML3.map_transposeInv_qPt,
    S46.map_transposeInv_qPt_eq]

section GoodPath

variable {p : ℕ → Vtx (puAmalgam c.hyp.le)} {N : ℕ}

theorem isMVtx_of_isGoodPath (hp : IsGoodPath _ p N) {k : ℕ} (hk : k ≤ N) (hev : Even k) :
    IsMVtx (puAmalgam c.hyp.le) (p k) := by
  have := c.isMVtx_add hp.toIsNBPath (x := 0) (k := k) (by omega) hp.mvtx hev
  rwa [zero_add] at this

theorem zm_le_vhat_right (hZV : c.HZV) (hp : IsGoodPath _ p N) {a : ℕ} (ha : Even a)
    (h10 : 10 ≤ a) (haN : a + 8 ≤ N) :
    ZM (puAmalgam c.hyp.le) (p (a + 2)) ≤ Vcirc c.hyp.le L (p a) ⊔ ZM _ (p a) := by
  have hx : Even (a - 6) := (Nat.even_sub (by omega)).mpr (iff_of_true ha (by decide))
  have := hZV p N hp (a - 6) hx (by omega) (by omega)
  rwa [show a - 6 + 8 = a + 2 by omega, show a - 6 + 6 = a by omega] at this

theorem zm_le_vhat_left' (hZV : c.HZV) (hp : IsGoodPath _ p N) {a : ℕ} (ha : Even a)
    (h10 : 10 ≤ a) (haN : a + 8 ≤ N) :
    ZM (puAmalgam c.hyp.le) (p (a - 2)) ≤ Vcirc c.hyp.le L (p a) ⊔ ZM _ (p a) := by
  have hx : Even (a - 6) := (Nat.even_sub (by omega)).mpr (iff_of_true ha (by decide))
  have := c.zm_le_vhat_left hZV hp hx (by omega) (by omega)
  rwa [show a - 6 + 4 = a - 2 by omega, show a - 6 + 6 = a by omega] at this

theorem vhat_le_whv_self {δ μ : Vtx (puAmalgam c.hyp.le)} :
    Vcirc c.hyp.le L μ ⊔ ZM _ μ ≤ whv c.hyp δ μ :=
  S4A.le_conjCl _ _

theorem vhat_le_whv' (hZV : c.HZV) (hp : IsGoodPath _ p N) {a : ℕ} (ha : Even a)
    (h10 : 10 ≤ a) (haN : a + 10 ≤ N) :
    Vcirc c.hyp.le L (p a) ⊔ ZM _ (p a) ≤ whv c.hyp (p a) (p (a + 2)) := by
  have h := c.hyp
  have hα := c.isMVtx_of_isGoodPath hp (k := a) (by omega) ha
  have hγ := c.isMVtx_of_isGoodPath hp (k := a + 2) (by omega) (ha.add even_two)
  have hd : (puAmalgam h.le).treeGraph.dist (p a) (p (a + 2)) = 2 := by
    rw [hp.dist_eq' (by omega) (by omega)]; omega
  have hc := c.isCritical_of_isGoodPath hp ha (show a + 8 ≤ N by omega)
  have hB := c.not_zm_le_bloc hc
  have hg : geo (puAmalgam h.le) (p a) (p (a + 8)) 2 = p (a + 2) := by
    rw [hp.eq_geo (i := a) (j := a + 8) (k := a + 2) (by omega) (by omega) (by omega),
      show a + 2 - a = 2 by omega]
  rw [hg] at hB
  refine (c.vcirc_sup_zm_le hα hγ hd hB).trans (sup_le (conjCl_mono le_sup_right) ?_)
  have := c.zm_le_vhat_left' hZV hp (a := a + 2) (ha.add even_two) (by omega) (by omega)
  rw [show a + 2 - 2 = a by omega] at this
  exact this.trans c.vhat_le_whv_self

theorem zm_le_whv_right (hZV : c.HZV) (hp : IsGoodPath _ p N) {a : ℕ} (ha : Even a)
    (h8 : 8 ≤ a) (haN : a + 10 ≤ N) :
    ZM (puAmalgam c.hyp.le) (p (a + 4)) ≤ whv c.hyp (p a) (p (a + 2)) := by
  have := c.zm_le_vhat_right hZV hp (a := a + 2) (ha.add even_two) (by omega) (by omega)
  rw [show a + 2 + 2 = a + 4 by omega] at this
  exact this.trans c.vhat_le_whv_self

theorem zm_le_whv_left (hZV : c.HZV) (hp : IsGoodPath _ p N) {a : ℕ} (ha : Even a)
    (h12 : 12 ≤ a) (haN : a + 6 ≤ N) :
    ZM (puAmalgam c.hyp.le) (p (a - 4)) ≤ whv c.hyp (p a) (p (a + 2)) := by
  rw [c.whv_eq_of_isGoodPath hp ha (by omega) (by omega)]
  have ha2 : Even (a - 2) := (Nat.even_sub (by omega)).mpr (iff_of_true ha (by decide))
  have := c.zm_le_vhat_left' hZV hp (a := a - 2) ha2 (by omega) (by omega)
  rw [show a - 2 - 2 = a - 4 by omega] at this
  exact this.trans c.vhat_le_whv_self

theorem whv_le_qv_right (hp : IsGoodPath _ p N) {a : ℕ} (ha : Even a) (h12 : 12 ≤ a)
    (haN : a + 13 ≤ N) :
    whv c.hyp (p a) (p (a + 2)) ≤ Qv (puAmalgam c.hyp.le) (p (a + 3)) := by
  have hr := c.isGoodPath_rev hp (m := a + 12) (ha.add (by decide)) (by omega) (by omega)
  have := c.whv_le_qv hr (y := 12) (by decide) (by decide) (by omega)
  rwa [show a + 12 - 12 = a by omega, show a + 12 - (12 - 2) = a + 2 by omega,
    show a + 12 - (12 - 3) = a + 3 by omega] at this

theorem commutator_vhat_qv_le_left (hZV : c.HZV) (hp : IsGoodPath _ p N) {a : ℕ} (ha : Even a)
    (h18 : 18 ≤ a) (haN : a + 13 ≤ N) :
    ⁅Vcirc c.hyp.le L (p (a + 2)) ⊔ ZM _ (p (a + 2)), Qv (puAmalgam c.hyp.le) (p (a + 1))⁆ ≤
      ZM _ (p a) ⊔ ZM _ (p (a + 2)) := by
  have hr := c.isGoodPath_rev hp (m := a + 12) (ha.add (by decide)) (by omega) (by omega)
  have := c.commutator_vhat_qv_le hZV hr (x := 4) (by decide) le_rfl (by omega)
  rwa [show a + 12 - (4 + 6) = a + 2 by omega, show a + 12 - (4 + 7) = a + 1 by omega,
    show a + 12 - (4 + 8) = a by omega] at this

theorem commutator_whv_qv_le' (hZV : c.HZV) (hp : IsGoodPath _ p N) {a : ℕ} (ha : Even a)
    (h12 : 12 ≤ a) (haN : a + 12 ≤ N) :
    ⁅whv c.hyp (p a) (p (a + 2)), Qv (puAmalgam c.hyp.le) (p a)⁆ ≤ ZM _ (p a) := by
  rw [c.whv_eq_of_isGoodPath hp ha (by omega) (by omega)]
  exact c.commutator_whv_qv_le hZV hp ha h12 haN

end GoodPath

end Ctx

end CFSG.Quasithin.MS93.S45
