module

public import CFSG.Quasithin.MS93.S45Br
import CFSG.Quasithin.MS93.S4A39
public import CFSG.Quasithin.MS93.S45Ext
public import CFSG.Quasithin.MS93.S45T

public section

namespace CFSG.Quasithin.MS93.S45

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Fintype F]

theorem IsGoodPath.mono {A B : Type} {C : Type} [Group A] [Group C] [Group B]
    {X : GoldAmalgam A C B} {p : ℕ → Vtx X} {N : ℕ} (hp : IsGoodPath X p N) {M : ℕ}
    (hM : M ≤ N) : IsGoodPath X p M :=
  ⟨hp.toIsNBPath.mono hM, hp.mvtx, fun i hi hi8 => hp.crit i hi (by omega),
    fun i hi h2 hi2 => hp.straight i hi h2 (by omega), fun i hi h8 hiN => hp.pe i hi h8 (by omega)⟩

theorem comm_of_commN_le_fixN {F : Type} [Field F] {A : Subgroup (SL3 F)}
    (hA : commN A ≤ fixN A) {a b : SL3 F} (ha : a ∈ A) (hb : b ∈ A) : a * b = b * a := by
  apply Subtype.ext
  rw [coe_mul_SL3, coe_mul_SL3]
  apply Matrix.ext_of_mulVec_single
  intro i
  set v : Fin 3 → F := Pi.single i 1
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  have hav := hA (sub_mem_commN ha v) b hb
  have hbv := hA (sub_mem_commN hb v) a ha
  rw [Matrix.mulVec_sub] at hav hbv
  linear_combination hbv - hav

@[expose] noncomputable def whv {M T L : Subgroup G} (h : PUHyp M T L)
    (δ μ : Vtx (puAmalgam h.le)) : Subgroup (puAmalgam h.le).Universal :=
  conjCl (stab (puAmalgam h.le) δ) (Vcirc h.le L μ ⊔ ZM _ μ)

namespace Ctx

variable {M T L : Subgroup G} {φ : ↥M →* ↥(StatedSL 3 F)} (c : Ctx M T L φ)
include c

@[expose] def HZV : Prop :=
  ∀ (p : ℕ → Vtx (puAmalgam c.hyp.le)) (N : ℕ), IsGoodPath _ p N → ∀ x : ℕ, Even x → 4 ≤ x →
    x + 14 ≤ N →
      ZM (puAmalgam c.hyp.le) (p (x + 8)) ≤ Vcirc c.hyp.le L (p (x + 6)) ⊔ ZM _ (p (x + 6))

theorem hZV_of_ne_two (hq : Fintype.card F ≠ 2) : c.HZV := fun _ _ hp _ hx h4 hxN =>
  c.zm_le_vhat_of_ne_two hp hx h4 hxN hq

theorem le_normalizer_usup_iff {δ γ : Vtx (puAmalgam c.hyp.le)}
    {ψ : ↥(stab (puAmalgam c.hyp.le) δ) →* ↥(StatedSL 3 F)}
    (hψ : IsSumOfNaturalModulesVia (stab _ δ) (Uloc c.hyp.le L δ) ⊥ ψ false 1)
    (hδ : IsMVtx _ δ) (hγ : (puAmalgam c.hyp.le).treeGraph.Adj δ γ)
    {A : Subgroup (puAmalgam c.hyp.le).Universal} (hA : A ≤ stab _ δ)
    {H : Submodule F (Fin 3 → F)}
    (hH : ∀ v : ↥(Uloc c.hyp.le L δ), (v : (puAmalgam c.hyp.le).Universal) ∈ Usup _ δ γ ↔
      natVec hψ v ∈ H) :
    A ≤ Subgroup.normalizer (Usup (puAmalgam c.hyp.le) δ γ : Set _) ↔
      ∀ e ∈ natImage ψ A, ∀ z ∈ H, ((e : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ z ∈ H := by
  have hUs : Usup (puAmalgam c.hyp.le) δ γ ≤ Uloc c.hyp.le L δ := by
    rw [c.usup_eq_uloc_inf_centralizer hψ hδ hγ]; exact inf_le_left
  have hconj : ∀ (a : ↥(stab (puAmalgam c.hyp.le) δ)) (w : (puAmalgam c.hyp.le).Universal)
      (hw : w ∈ Usup (puAmalgam c.hyp.le) δ γ),
      ((a : (puAmalgam c.hyp.le).Universal) * w * (a : (puAmalgam c.hyp.le).Universal)⁻¹ ∈
        Usup (puAmalgam c.hyp.le) δ γ ↔
        ((toSL3 ψ a : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ natVec hψ ⟨w, hUs hw⟩ ∈ H) := by
    intro a w hw
    have hmem : (a : (puAmalgam c.hyp.le).Universal) * w * (a : (puAmalgam c.hyp.le).Universal)⁻¹
        ∈ Uloc c.hyp.le L δ := (Subgroup.mem_normalizer_iff.mp (hψ.1 a.2) _).mp (hUs hw)
    rw [← natVec_conj hψ a ⟨w, hUs hw⟩ ⟨_, hmem⟩ rfl]
    exact hH ⟨_, hmem⟩
  constructor
  · intro hN e he z hz
    obtain ⟨a, ha, rfl⟩ := mem_natImage.mp he
    obtain ⟨w, rfl⟩ := natVec_surjective hψ z
    have hw : (w : (puAmalgam c.hyp.le).Universal) ∈ Usup _ δ γ := (hH w).mpr hz
    exact (hconj a w hw).mp ((Subgroup.mem_normalizer_iff.mp (hN ha) _).mp hw)
  · intro hE a ha
    rw [Subgroup.mem_normalizer_iff]
    intro w
    have key : ∀ b ∈ A, ∀ w ∈ Usup (puAmalgam c.hyp.le) δ γ, b * w * b⁻¹ ∈ Usup _ δ γ := by
      intro b hb w hw
      have h1 := (hconj ⟨b, hA hb⟩ w hw).mpr
        (hE _ (mem_natImage.mpr ⟨⟨b, hA hb⟩, hb, rfl⟩) _ ((hH ⟨w, hUs hw⟩).mp hw))
      exact h1
    refine ⟨key a ha w, fun hw => ?_⟩
    have := key a⁻¹ (inv_mem ha) _ hw
    simpa [mul_assoc] using this

section GoodPath

variable {p : ℕ → Vtx (puAmalgam c.hyp.le)} {N : ℕ}

theorem exists_adj_branch (hp : IsGoodPath _ p N) {y : ℕ} (hy : Even y) (h12 : 12 ≤ y)
    (hyN : y < N) :
    ∃ γ, (puAmalgam c.hyp.le).treeGraph.Adj (p y) γ ∧
      ¬ ZM _ (p (y - 8)) ≤ Subgroup.normalizer (Usup _ (p y) γ : Set _) ∧
      Usup (puAmalgam c.hyp.le) (p y) γ ⊓ Usup _ (p y) (p (y - 1)) ≠
        Usup _ (p y) (p (y + 1)) ⊓ Usup _ (p y) (p (y - 1)) := by
  have h := c.hyp
  have h20 := h.hyp20
  have : CharP F 2 := c.charP
  have hM : ∀ k, k ≤ N → Even k → IsMVtx (puAmalgam h.le) (p k) := fun k hk hev => by
    have := c.isMVtx_add hp.toIsNBPath (x := 0) (k := k) (by omega) hp.mvtx hev
    rwa [zero_add] at this
  have hδ := hM y (by omega) hy
  have hy8 : Even (y - 8) := by obtain ⟨k, hk⟩ := hy; exact ⟨k - 4, by omega⟩
  have hc : IsCritical (puAmalgam h.le) (p y) (p (y - 8)) := by
    have := hp.crit (y - 8) hy8 (by omega)
    rwa [show y - 8 + 8 = y by omega] at this
  obtain ⟨ψ, hψs, hψ⟩ := exists_natural_Uloc h c.via hδ
  have hm1 : (puAmalgam h.le).treeGraph.Adj (p y) (p (y - 1)) := by
    have := hp.adj (y - 1) (by omega)
    rw [show y - 1 + 1 = y by omega] at this
    exact this.symm
  have hp1 : (puAmalgam h.le).treeGraph.Adj (p y) (p (y + 1)) := hp.adj y hyN
  have hg1 : geo (puAmalgam h.le) (p y) (p (y - 8)) 1 = p (y - 1) := by
    rw [hp.eq_geo_rev (i := y - 8) (j := y) (k := y - 1) (by omega) (by omega) (by omega),
      show y - (y - 1) = 1 by omega]
  have hZs : ZM (puAmalgam h.le) (p (y - 8)) ≤ stab _ (p y) :=
    zm_le_stab_of_isCritical _ h20 c.bpos hc
  set E := natImage ψ (ZM (puAmalgam h.le) (p (y - 8))) with hEdef
  have hZab := isElemAbelian_zm _ h20 c.bpos (c.isCritical_symm hc).1
  have hE2 : ∀ g ∈ E, g * g = 1 := by
    intro g hg
    obtain ⟨a, ha, rfl⟩ := mem_natImage.mp hg
    rw [← map_mul, ← sq]
    have : a ^ 2 = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hZab.2 _ ha)
    rw [this, map_one]
  have hEc : ∀ g ∈ E, ∀ g' ∈ E, g * g' = g' * g := by
    intro g hg g' hg'
    obtain ⟨a, ha, rfl⟩ := mem_natImage.mp hg
    obtain ⟨b, hb, rfl⟩ := mem_natImage.mp hg'
    have hcomm := hZab.1
    rw [isMulCommutative_subgroup_iff] at hcomm
    have : a * b = b * a := Subtype.ext (by
      simp only [Subgroup.coe_mul]; exact hcomm _ ha _ hb)
    rw [← map_mul, ← map_mul, this]
  set Wm := fixN (natImage ψ (Qv (puAmalgam h.le) (p (y - 1)))) with hWm
  set Wp := fixN (natImage ψ (Qv (puAmalgam h.le) (p (y + 1)))) with hWp
  have hWm2 := (c.fixN_eq_commN_qv hψ hδ hm1).2
  have hWp2 := (c.fixN_eq_commN_qv hψ hδ hp1).2
  have hfix := c.fixN_natImage_zm hc hψ
  rw [hg1] at hfix
  have hpe := hp.pe y hy (by omega) hyN
  obtain ⟨u, hu, huWp⟩ : ∃ u ∈ commN E, u ∉ Wp := by
    by_contra hcon
    push Not at hcon
    apply hpe
    refine (c.le_normalizer_usup_iff hψ hδ hp1 hZs (c.mem_usup_iff hψ hδ hp1)).mpr ?_
    intro e he z hz
    have := Wp.add_mem hz (hcon _ (sub_mem_commN he z))
    rwa [add_sub_cancel] at this
  have huWm : u ∈ Wm := by
    have := commN_le_fixN_of_elemAb hE2 hEc hu
    rw [hfix] at this
    exact this
  have hu0 : u ≠ 0 := fun h0 => huWp (h0 ▸ Wp.zero_mem)
  have hWne : Wm ≠ Wp := by
    intro heq
    have hgpd := c.zh_ne_of_isGoodPath hp hy (by omega) hyN
    apply hgpd
    rw [← c.usup_eq_iff_zh_eq hψ hδ hm1 hp1]
    exact (eq_iff_of_natVec_iff hψ
      (by rw [c.usup_eq_uloc_inf_centralizer hψ hδ hm1]; exact inf_le_left)
      (by rw [c.usup_eq_uloc_inf_centralizer hψ hδ hp1]; exact inf_le_left)
      (c.mem_usup_iff hψ hδ hm1) (c.mem_usup_iff hψ hδ hp1)).mpr heq
  have h1 := finrank_inf_eq_one hWm2 hWp2 hWne
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (by
    intro hb; rw [hb, finrank_bot] at h1; omega : Wm ⊓ Wp ≠ ⊥)
  have hwu : ∀ t : F, w ≠ t • u := by
    intro t ht
    have ht0 : t ≠ 0 := fun h0 => hw0 (by rw [ht, h0, zero_smul])
    apply huWp
    have := Wp.smul_mem t⁻¹ hw.2
    rwa [ht, smul_smul, inv_mul_cancel₀ ht0, one_smul] at this
  obtain ⟨x, hx0, hx1⟩ := exists_mulVec_e0_e1 hu0 hwu
  set g' := x * rootElt 0 1 (1 : F) * x⁻¹ with hg'
  have hxi : ∀ v : Fin 3 → F, ((x⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
      (((x : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v) = v := fun v => by
    rw [Matrix.mulVec_mulVec, ← coe_mul_SL3, inv_mul_cancel, coe_one_SL3, Matrix.one_mulVec]
  have hg'u : ((g' : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ u = u := by
    rw [hg', coe_mul_SL3, coe_mul_SL3, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← hx0,
      hxi, rootElt_mulVec (by decide)]
    simp
  have hg'w : ((g' : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ w = w + u := by
    rw [hg', coe_mul_SL3, coe_mul_SL3, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← hx1,
      hxi, rootElt_mulVec (by decide), Matrix.mulVec_add, hx1, ← hx0]
    congr 2
    funext k; fin_cases k <;> simp
  have hginv : ∀ v z : Fin 3 → F, ((g' : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v = z →
      ((g'⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ z = v := fun v z hvz => by
    rw [← hvz, Matrix.mulVec_mulVec, ← coe_mul_SL3, inv_mul_cancel, coe_one_SL3,
      Matrix.one_mulVec]
  obtain ⟨g, hg⟩ := toSL3_surjective hψs g'
  set γ := (g : (puAmalgam h.le).Universal) • p (y + 1) with hγdef
  have hgδ : (g : (puAmalgam h.le).Universal) • p y = p y := (mem_stab _).mp g.2
  have hγ : (puAmalgam h.le).treeGraph.Adj (p y) γ := by
    rw [← hgδ]; exact (adj_smul _ _ _ _).mpr hp1
  set H := Wp.comap (Matrix.SpecialLinearGroup.toLin' (toSL3 ψ g⁻¹) : (Fin 3 → F) →ₗ[F] _)
    with hH
  have hmemH : ∀ z, z ∈ H ↔ ((toSL3 ψ g⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ z ∈ Wp := by
    intro z
    rw [hH, Submodule.mem_comap]
    simp only [LinearEquiv.coe_coe, Matrix.SpecialLinearGroup.toLin'_apply, Matrix.toLin'_apply]
  have hgi : toSL3 ψ g⁻¹ = g'⁻¹ := by rw [map_inv, hg]
  have hHγ : ∀ v : ↥(Uloc h.le L (p y)), (v : (puAmalgam h.le).Universal) ∈ Usup _ (p y) γ ↔
      natVec hψ v ∈ H := fun v => by
    rw [hmemH]; exact c.mem_usup_smul_iff hψ hδ hp1 g v
  refine ⟨γ, hγ, fun hN => ?_, fun heq => ?_⟩
  ·
    have huH : u ∉ H := by
      rw [hmemH, hgi, hginv u u hg'u]; exact huWp
    have hHrank : Module.finrank F H = 2 := by
      rw [hH, Submodule.comap_equiv_eq_map_symm, LinearEquiv.finrank_map_eq, hWp2]
    obtain ⟨e, he, z, hz, hez⟩ :=
      exists_not_mem_of_commN hE2 hEc hu huH (sup_span_eq_top hHrank huH)
    exact hez ((c.le_normalizer_usup_iff hψ hδ hγ hZs hHγ).mp hN e he z hz)
  ·
    obtain ⟨v₀, hv₀⟩ := natVec_surjective hψ (w + u)
    have hv₀γ : (v₀ : (puAmalgam h.le).Universal) ∈ Usup _ (p y) γ := by
      rw [hHγ, hv₀, hmemH, hgi, hginv w (w + u) hg'w]; exact hw.2
    have hv₀m : (v₀ : (puAmalgam h.le).Universal) ∈ Usup _ (p y) (p (y - 1)) := by
      rw [c.mem_usup_iff hψ hδ hm1, hv₀]; exact Wm.add_mem hw.1 huWm
    have hv₀p : (v₀ : (puAmalgam h.le).Universal) ∉ Usup _ (p y) (p (y + 1)) := by
      rw [c.mem_usup_iff hψ hδ hp1, hv₀]
      intro hwu'
      apply huWp
      have := Wp.sub_mem hwu' hw.2
      rwa [add_sub_cancel_left] at this
    have h2 : (v₀ : (puAmalgam h.le).Universal) ∈
        Usup (puAmalgam h.le) (p y) γ ⊓ Usup _ (p y) (p (y - 1)) := ⟨hv₀γ, hv₀m⟩
    rw [heq] at h2
    exact hv₀p h2.1

theorem vhat_le_whv (hp : IsGoodPath _ p N) {y : ℕ} (hy : Even y) (h2 : 2 ≤ y)
    (hyN : y + 2 ≤ N) :
    Vcirc c.hyp.le L (p (y + 2)) ⊔ ZM _ (p (y + 2)) ≤ whv c.hyp (p y) (p (y - 2)) := by
  obtain ⟨g, hg, hgx⟩ := hp.straight y hy h2 hyN
  have e : p (y + 2) = g⁻¹ • p (y - 2) := by rw [← hgx, inv_smul_smul]
  rw [e, vcirc_smul c.hyp, zm_smul, ← Subgroup.map_sup]
  exact le_iSup₂_of_le (f := fun t (_ : t ∈ stab (puAmalgam c.hyp.le) (p y)) =>
    (Vcirc c.hyp.le L (p (y - 2)) ⊔ ZM _ (p (y - 2))).map (MulAut.conj t).toMonoidHom) g⁻¹
    (inv_mem hg) le_rfl

theorem whv_le_qv (hp : IsGoodPath _ p N) {y : ℕ} (hy : Even y) (h4 : 4 ≤ y) (hyN : y ≤ N) :
    whv c.hyp (p y) (p (y - 2)) ≤ Qv (puAmalgam c.hyp.le) (p (y - 3)) := by
  have hd : ∀ i j, i ≤ j → j ≤ N → (puAmalgam c.hyp.le).treeGraph.dist (p i) (p j) = j - i :=
    fun i j hij hj => hp.dist_eq' hij hj
  have hM : ∀ k, k ≤ N → Even k → IsMVtx (puAmalgam c.hyp.le) (p k) := fun k hk hev => by
    have := c.isMVtx_add hp.toIsNBPath (x := 0) (k := k) (by omega) hp.mvtx hev
    rwa [zero_add] at this
  refine iSup₂_le fun t ht => ?_
  have htp : t • p y = p y := (mem_stab _).mp ht
  have h2 : (puAmalgam c.hyp.le).treeGraph.dist (t • p (y - 2)) (p y) = 2 := by
    conv_lhs => rw [← htp]
    rw [dist_smul, hd (y - 2) y (by omega) hyN]; omega
  have h3 : (puAmalgam c.hyp.le).treeGraph.dist (p y) (p (y - 3)) = 3 := by
    rw [tdist_comm, hd (y - 3) y (by omega) hyN]; omega
  have h1 := dist_triangle (puAmalgam c.hyp.le) (t • p (y - 2)) (p y) (p (y - 3))
  have hle : Vcirc c.hyp.le L (t • p (y - 2)) ⊔ ZM _ (t • p (y - 2)) ≤ Qv _ (p (y - 3)) := by
    refine sup_le ((c.vcirc_le_vv _).trans (vi_le_qv _ ?_)) ?_
    · rw [c.b8]; omega
    · refine zm_le_qv_of_dist_lt _ ((isMVtx_smul _ _ _).mpr (hM (y - 2) (by omega)
        (by obtain ⟨k, hk⟩ := hy; exact ⟨k - 1, by omega⟩))) ?_
      rw [c.b8]; omega
  rw [vcirc_smul c.hyp, zm_smul, ← Subgroup.map_sup] at hle
  exact hle

theorem qv_le_whv_sup_qv (hZV : c.HZV) (hp : IsGoodPath _ p N) {y : ℕ} (hy : Even y)
    (h12 : 12 ≤ y) (hyN : y + 10 ≤ N) :
    Qv (puAmalgam c.hyp.le) (p (y - 3)) ≤ whv c.hyp (p y) (p (y - 2)) ⊔ Qv _ (p (y - 4)) := by
  have h := c.hyp
  have : CharP F 2 := c.charP
  obtain ⟨γ, hγa, hγZ, hγne⟩ := c.exists_adj_branch hp hy h12 (by omega)
  obtain ⟨p₁, hp₁e, hp₁, hU1⟩ := (hp.mono (show y ≤ N by omega)).extend_of h c.b8 c.c444
    (by omega) hy hγa hγZ
  obtain ⟨p', hp'e, hp'⟩ := c.exists_extend hp₁ (by omega) (hy.add even_two) 4
  have hpp' : ∀ i, i ≤ y → p' i = p i := fun i hi => (hp'e i (by omega)).trans (hp₁e i hi)
  have hU' : Usup (puAmalgam h.le) (p y) (p' (y + 1)) = Usup _ (p y) γ := by
    rw [hp'e (y + 1) (by omega)]; exact hU1
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
  rw [hpp' (y - 4) (by omega), hpp' y le_rfl, hpp' (y - 1) (by omega), hU'] at hR₂
  have hRne :
      critR (puAmalgam h.le) (p (y - 4)) (p (y + 4)) ≠ critR _ (p (y - 4)) (p' (y + 4)) := by
    rw [hR₁, hR₂]
    intro heq
    apply hγne
    rw [inf_comm (Usup _ _ γ), inf_comm (Usup _ _ (p (y + 1)))]
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
  have hcardR₁ : Nat.card ↥(critR (puAmalgam h.le) (p (y - 4)) (p (y + 4))) = Fintype.card F := by
    have := c.card_critR hp.toIsNBPath (x := y - 4) (by omega)
      (c.isCritical_of_isGoodPath hp hy4 (by omega)) (c.straight_of_isGoodPath hp hy4 (by omega))
      (by
        have := c.zh_ne_of_isGoodPath hp hy (by omega) (by omega)
        rwa [show y - 4 + 3 = y - 1 by omega, show y - 4 + 5 = y + 1 by omega])
    rwa [show y - 4 + 8 = y + 4 by omega] at this
  have hcardR₂ : Nat.card ↥(critR (puAmalgam h.le) (p (y - 4)) (p' (y + 4))) =
      Fintype.card F := by
    have := c.card_critR hp'.toIsNBPath (x := y - 4) (by omega)
      (c.isCritical_of_isGoodPath hp' hy4 (by omega)) (c.straight_of_isGoodPath hp' hy4 (by omega))
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
  have hZ₁ : ZM (puAmalgam h.le) (p (y + 4)) ≤ whv h (p y) (p (y - 2)) := by
    have := hZV p N hp (y - 4) hy4 (by omega) (by omega)
    rw [show y - 4 + 8 = y + 4 by omega, show y - 4 + 6 = y + 2 by omega] at this
    exact this.trans (c.vhat_le_whv hp hy (by omega) (by omega))
  have hZ₂ : ZM (puAmalgam h.le) (p' (y + 4)) ≤ whv h (p y) (p (y - 2)) := by
    have := hZV p' (y + 2 + 2 * 4) hp' (y - 4) hy4 (by omega) (by omega)
    rw [show y - 4 + 8 = y + 4 by omega, show y - 4 + 6 = y + 2 by omega] at this
    have hw := c.vhat_le_whv hp' hy (by omega) (by omega)
    rw [hpp' y le_rfl, hpp' (y - 2) (by omega)] at hw
    exact this.trans hw
  have hWs : whv h (p y) (p (y - 2)) ≤ stab (puAmalgam h.le) (p (y - 4)) :=
    (c.whv_le_qv hp hy (by omega) (by omega)).trans (qv_le_stab_of_adj _ hadj.symm)
  have hRTW : RT ≤ natImage ψ (whv h (p y) (p (y - 2))) := by
    rw [← hRTeq]
    exact sup_le (natImage_mono hZ₁) (natImage_mono hZ₂)
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

end GoodPath

end Ctx

end CFSG.Quasithin.MS93.S45
