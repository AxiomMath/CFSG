module

public import CFSG.Quasithin.MS93.S45A

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

theorem natImage_qv_props {δ β : Vtx (puAmalgam c.hyp.le)} (hδ : IsMVtx _ δ)
    (hβ : (puAmalgam c.hyp.le).treeGraph.Adj δ β)
    {ψ : ↥(stab (puAmalgam c.hyp.le) δ) →* ↥(StatedSL 3 F)}
    (hψ : IsSumOfNaturalModulesVia (stab _ δ) (Uloc c.hyp.le L δ) ⊥ ψ false 1) :
    IsPGroup 2 (natImage ψ (Qv (puAmalgam c.hyp.le) β)) ∧
      Nat.card (natImage ψ (Qv (puAmalgam c.hyp.le) β)) = Nat.card F ^ 2 ∧
      fixN (natImage ψ (Qv (puAmalgam c.hyp.le) β)) =
        commN (natImage ψ (Qv (puAmalgam c.hyp.le) β)) ∧
      Module.finrank F ↥(commN (natImage ψ (Qv (puAmalgam c.hyp.le) β))) = 2 := by
  have hβH : ¬ IsMVtx (puAmalgam c.hyp.le) β := by
    rw [← isMVtx_iff_of_adj _ hβ]; exact hδ
  have hTs : Qv (puAmalgam c.hyp.le) β ≤ stab _ δ := qv_le_stab_of_adj _ hβ.symm
  have hfc := c.fixN_eq_commN_qv hψ hδ hβ
  refine ⟨?_, ?_, hfc.1, hfc.1 ▸ hfc.2⟩
  · have h1 : IsPGroup 2 (Qv (puAmalgam c.hyp.le) β) := isPGroup_qv _ c.hyp.hyp20 hβH
    exact (h1.of_equiv (Subgroup.subgroupOfEquivOfLe hTs).symm).map _
  · rw [Nat.card_eq_fintype_card (α := F)]; exact c.card_natImage_qv hψ hδ hβ

theorem mem_normalizer_qv_of {δ β : Vtx (puAmalgam c.hyp.le)} (hδ : IsMVtx _ δ)
    (hβ : (puAmalgam c.hyp.le).treeGraph.Adj δ β)
    {ψ : ↥(stab (puAmalgam c.hyp.le) δ) →* ↥(StatedSL 3 F)}
    (hψ : IsSumOfNaturalModulesVia (stab _ δ) (Uloc c.hyp.le L δ) ⊥ ψ false 1)
    {g : ↥(stab (puAmalgam c.hyp.le) δ)}
    (hg : toSL3 ψ g ∈ Subgroup.normalizer
      ((natImage ψ (Qv (puAmalgam c.hyp.le) β) : Subgroup (SL3 F)) : Set (SL3 F))) :
    (g : (puAmalgam c.hyp.le).Universal) ∈
      Subgroup.normalizer (Qv (puAmalgam c.hyp.le) β : Set (puAmalgam c.hyp.le).Universal) := by
  have hTs : Qv (puAmalgam c.hyp.le) β ≤ stab _ δ := qv_le_stab_of_adj _ hβ.symm
  rw [Subgroup.mem_normalizer_iff]
  intro t
  constructor
  · intro ht
    have hts : t ∈ stab (puAmalgam c.hyp.le) δ := hTs ht
    set t' : ↥(stab (puAmalgam c.hyp.le) δ) := ⟨t, hts⟩ with ht'
    have h1 := (c.mem_qv_iff_natImage hδ hβ hψ t').mp ht
    have h2 : toSL3 ψ (g * t' * g⁻¹) ∈ natImage ψ (Qv (puAmalgam c.hyp.le) β) := by
      rw [map_mul, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.mp hg _).mp h1
    exact (c.mem_qv_iff_natImage hδ hβ hψ (g * t' * g⁻¹)).mpr h2
  · intro ht
    have hts : t ∈ stab (puAmalgam c.hyp.le) δ := by
      have h1 : (g : (puAmalgam c.hyp.le).Universal) * t *
          (g : (puAmalgam c.hyp.le).Universal)⁻¹ ∈ stab _ δ := hTs ht
      have h2 := mul_mem (mul_mem (inv_mem g.2) h1) g.2
      have e : (g : (puAmalgam c.hyp.le).Universal)⁻¹ *
          ((g : (puAmalgam c.hyp.le).Universal) * t * (g : (puAmalgam c.hyp.le).Universal)⁻¹) *
            (g : (puAmalgam c.hyp.le).Universal) = t := by group
      rwa [e] at h2
    set t' : ↥(stab (puAmalgam c.hyp.le) δ) := ⟨t, hts⟩ with ht'
    have h1 := (c.mem_qv_iff_natImage hδ hβ hψ (g * t' * g⁻¹)).mp ht
    rw [map_mul, map_mul, map_inv] at h1
    have h2 := (Subgroup.mem_normalizer_iff.mp hg _).mpr h1
    exact (c.mem_qv_iff_natImage hδ hβ hψ t').mpr h2

section GoodPath

variable {p : ℕ → Vtx (puAmalgam c.hyp.le)} {N : ℕ}

theorem img_zm_eq (hp : IsGoodPath _ p N) {x : ℕ} (hx : Even x) (h4 : 4 ≤ x) (hxN : x + 14 ≤ N)
    {ψ : ↥(stab (puAmalgam c.hyp.le) (p (x + 6))) →* ↥(StatedSL 3 F)}
    (hψs : Function.Surjective ψ)
    (hψ : IsSumOfNaturalModulesVia (stab _ (p (x + 6))) (Uloc c.hyp.le L (p (x + 6))) ⊥ ψ
      false 1)
    (hd : IsSumOfNaturalModulesVia (stab _ (p (x + 6))) (Vv (puAmalgam c.hyp.le) (p (x + 6)))
      (Bloc c.hyp.le L (p (x + 6))) ψ true 1) :
    ∀ y : Fin 3 → F, (∀ a ∈ natImage ψ (Qv (puAmalgam c.hyp.le) (p (x + 7))), dualMat a *ᵥ y = y) ↔
      y ∈ (NatSec.ofIsSum hd).img (ZM (puAmalgam c.hyp.le) (p (x + 8))) := by
  have h := c.hyp
  have : CharP F 2 := c.charP
  have hM : ∀ k, k ≤ N → Even k → IsMVtx (puAmalgam h.le) (p k) := fun k hk hev => by
    have := c.isMVtx_add hp.toIsNBPath (x := 0) (k := k) (by omega) hp.mvtx hev
    rwa [zero_add] at this
  have hd' : ∀ i j, i ≤ j → j ≤ N → (puAmalgam h.le).treeGraph.dist (p i) (p j) = j - i :=
    fun i j hij hj => hp.dist_eq' hij hj
  have hMδ := hM (x + 6) (by omega) (hx.add (by decide))
  have hMμ := hM (x + 8) (by omega) (hx.add (by decide))
  have hδβ : (puAmalgam h.le).treeGraph.Adj (p (x + 6)) (p (x + 7)) := hp.adj (x + 6) (by omega)
  set Nn := NatSec.ofIsSum hd with hNn
  set A := natImage ψ (Qv (puAmalgam h.le) (p (x + 7))) with hAdef
  obtain ⟨hA2, hAc, hfc, h2⟩ := c.natImage_qv_props hMδ hδβ hψ
  have hZμV : ZM (puAmalgam h.le) (p (x + 8)) ≤ Vv _ (p (x + 6)) :=
    c.zm_le_vv_of_dist hMμ (by rw [hd' (x + 6) (x + 8) (by omega) (by omega)]; omega)
  have hHB : Usup (puAmalgam h.le) (p (x + 8)) (p (x + 7)) ≤ Bloc h.le L (p (x + 6)) := by
    rw [← c.hloc_eq_usup' hp hx h4 (by omega)]
    exact c.hloc_le_bloc hMδ
  set S := Nn.img (ZM (puAmalgam h.le) (p (x + 8))) with hSdef
  have hSfix : ∀ y ∈ S, ∀ a ∈ A, dualMat a *ᵥ y = y := by
    intro y hy a ha
    obtain ⟨z, hzμ, hzV, rfl⟩ := Nn.mem_img.mp hy
    obtain ⟨t, ht, rfl⟩ := mem_natImage.mp ha
    have h1 := Nn.coord_conj t hzV
    rw [natAct_true] at h1
    rw [← h1]
    have hw : z⁻¹ * ((t : (puAmalgam h.le).Universal) * z * (t : (puAmalgam h.le).Universal)⁻¹) ∈
        Bloc h.le L (p (x + 6)) := by
      have e : z⁻¹ * ((t : (puAmalgam h.le).Universal) * z * (t : (puAmalgam h.le).Universal)⁻¹) =
          ⁅z⁻¹, (t : (puAmalgam h.le).Universal)⁆ := by
        rw [commutatorElement_def]; group
      rw [e]
      refine hHB ?_
      rw [Usup, zv_of_isMVtx _ hMμ]
      exact Subgroup.commutator_mem_commutator (inv_mem hzμ) ht
    have h2 := (Nn.coord_eq_zero_iff (Subgroup.mul_mem _ (inv_mem hzV) (Nn.conj_mem t hzV))).mpr hw
    rw [Nn.coord_mul (inv_mem hzV) (Nn.conj_mem t hzV), Nn.coord_inv hzV, neg_add_eq_zero] at h2
    exact h2.symm
  have hcrit : IsCritical (puAmalgam h.le) (p (x + 6)) (p (x + 14)) := by
    have := c.isCritical_of_isGoodPath hp (y := x + 6) (hx.add (by decide)) (by omega)
    rwa [show x + 6 + 8 = x + 14 by omega] at this
  have hgeo : geo (puAmalgam h.le) (p (x + 6)) (p (x + 14)) 2 = p (x + 8) := by
    rw [hp.eq_geo (i := x + 6) (j := x + 14) (k := x + 8) (by omega) (by omega) (by omega),
      show x + 8 - (x + 6) = 2 by omega]
  have hB := c.not_zm_le_bloc hcrit
  rw [hgeo] at hB
  obtain ⟨z₀, hz₀μ, hz₀B⟩ := Set.not_subset.mp hB
  have hne : ∃ y ∈ S, y ≠ 0 := ⟨Nn.coord z₀, Nn.mem_img.mpr ⟨z₀, hz₀μ, hZμV hz₀μ, rfl⟩,
    fun h0 => hz₀B ((Nn.coord_eq_zero_iff (hZμV hz₀μ)).mp h0)⟩
  have hinv : ∀ g ∈ Subgroup.normalizer (A : Set (SL3 F)), ∀ y ∈ S, dualMat g *ᵥ y ∈ S := by
    intro g' hg' y hy
    obtain ⟨z, hzμ, hzV, rfl⟩ := Nn.mem_img.mp hy
    obtain ⟨g, rfl⟩ := toSL3_surjective hψs g'
    have hgT := c.mem_normalizer_qv_of hMδ hδβ hψ hg'
    have hgZ := c.normalizer_zm_right hp hx h4 (by omega) ⟨g.2, hgT⟩
    refine Nn.mem_img.mpr ⟨g * z * (g : (puAmalgam h.le).Universal)⁻¹,
      (Subgroup.mem_normalizer_iff.mp hgZ z).mp hzμ, Nn.conj_mem g hzV, ?_⟩
    rw [Nn.coord_conj g hzV, natAct_true]
  have hall := (dual_fix_of_normalizer hA2 hAc hfc h2).1 S hSfix hne hinv
  intro y
  exact ⟨fun hy => hall y hy, fun hy => hSfix y hy⟩

theorem zm_inf_bloc_le (hp : IsGoodPath _ p N) {x : ℕ} (hx : Even x) (h4 : 4 ≤ x)
    (hxN : x + 14 ≤ N) :
    ZM (puAmalgam c.hyp.le) (p (x + 8)) ⊓ Bloc c.hyp.le L (p (x + 6)) ≤ ZM _ (p (x + 6)) := by
  have h := c.hyp
  have : CharP F 2 := c.charP
  have hM : ∀ k, k ≤ N → Even k → IsMVtx (puAmalgam h.le) (p k) := fun k hk hev => by
    have := c.isMVtx_add hp.toIsNBPath (x := 0) (k := k) (by omega) hp.mvtx hev
    rwa [zero_add] at this
  have hd' : ∀ i j, i ≤ j → j ≤ N → (puAmalgam h.le).treeGraph.dist (p i) (p j) = j - i :=
    fun i j hij hj => hp.dist_eq' hij hj
  have hMδ := hM (x + 6) (by omega) (hx.add (by decide))
  have hMμ := hM (x + 8) (by omega) (hx.add (by decide))
  have hδβ : (puAmalgam h.le).treeGraph.Adj (p (x + 6)) (p (x + 7)) := hp.adj (x + 6) (by omega)
  have hμβ : (puAmalgam h.le).treeGraph.Adj (p (x + 8)) (p (x + 7)) :=
    (hp.adj (x + 7) (by omega)).symm
  obtain ⟨ψ, hψs, hψ⟩ := exists_natural_Uloc h c.via hMδ
  obtain ⟨d, hd⟩ := c.exists_isSum_vhat hMδ hψs hψ
  have hdB := c.isSum_bloc hMδ hd
  have hdt := c.dual_eq_true hp hx h4 hxN hψs hψ hdB
  subst hdt
  set Nn := NatSec.ofIsSum hdB with hNn
  obtain ⟨hA2, hAc, hfc, h2⟩ := c.natImage_qv_props hMδ hδβ hψ
  have himg := c.img_zm_eq hp hx h4 hxN hψs hψ hdB
  obtain ⟨e, he, heA⟩ := (dual_fix_of_normalizer hA2 hAc hfc h2).2.1
  have hZμV : ZM (puAmalgam h.le) (p (x + 8)) ≤ Vv _ (p (x + 6)) :=
    c.zm_le_vv_of_dist hMμ (by rw [hd' (x + 6) (x + 8) (by omega) (by omega)]; omega)
  let f : ↥(ZM (puAmalgam h.le) (p (x + 8))) →* Multiplicative (Fin 3 → F) :=
    { toFun := fun z => Multiplicative.ofAdd (Nn.coord z)
      map_one' := by simp [Nn.coord_one]
      map_mul' := fun z w => by
        simp only [Subgroup.coe_mul]
        rw [Nn.coord_mul (hZμV z.2) (hZμV w.2), ofAdd_add] }
  have hfker : f.ker = (Bloc h.le L (p (x + 6))).subgroupOf (ZM _ (p (x + 8))) := by
    ext z
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    show Multiplicative.ofAdd (Nn.coord z) = 1 ↔ _
    rw [← Nn.coord_eq_zero_iff (hZμV z.2)]
    exact ⟨fun h1 => by simpa using h1, fun h1 => by rw [h1, ofAdd_zero]⟩
  have hrange : Fintype.card F ≤ Nat.card f.range := by
    have hmem : ∀ t : F, Multiplicative.ofAdd (e t) ∈ f.range := by
      intro t
      obtain ⟨z, hzμ, -, hze⟩ := Nn.mem_img.mp ((himg (e t)).mp (fun a ha => heA t a ha))
      exact ⟨⟨z, hzμ⟩, by show Multiplicative.ofAdd (Nn.coord z) = _; rw [hze]⟩
    let ι : F → ↥f.range := fun t => ⟨Multiplicative.ofAdd (e t), hmem t⟩
    have hι : Function.Injective ι := fun t t' htt => by
      have h1 : ((ι t : ↥f.range) : Multiplicative (Fin 3 → F)) = ι t' := congrArg Subtype.val htt
      exact he (Multiplicative.ofAdd.injective h1)
    rw [← Nat.card_eq_fintype_card]
    exact Nat.card_le_card_of_injective ι hι
  have hidx : (ZH (puAmalgam h.le) (p (x + 7))).relIndex (ZM _ (p (x + 8))) = Fintype.card F :=
    c.relIndex_zh hMμ hμβ
  have hZβB : (ZH (puAmalgam h.le) (p (x + 7))).subgroupOf (ZM _ (p (x + 8))) ≤ f.ker := by
    rw [hfker]
    intro z hz
    rw [Subgroup.mem_subgroupOf] at hz ⊢
    exact zm_le_bloc h (by rw [c.b8]; norm_num) hMδ (zh_le_zm _ hδβ hz)
  have hkidx : f.ker.index = Fintype.card F := by
    have h1 : f.ker.index ∣
        ((ZH (puAmalgam h.le) (p (x + 7))).subgroupOf (ZM _ (p (x + 8)))).index :=
      Subgroup.index_dvd_of_le hZβB
    rw [← Subgroup.relIndex, hidx] at h1
    have h2 := Nat.le_of_dvd Fintype.card_pos h1
    rw [Subgroup.index_ker] at h2 ⊢
    omega
  have hkeq : (ZH (puAmalgam h.le) (p (x + 7))).subgroupOf (ZM _ (p (x + 8))) = f.ker := by
    have h1 := Subgroup.relIndex_mul_index hZβB
    rw [hkidx, ← Subgroup.relIndex, hidx] at h1
    have h3 : (((ZH (puAmalgam h.le) (p (x + 7))).subgroupOf (ZM _ (p (x + 8))))).relIndex f.ker =
        1 := by
      have := Fintype.card_pos (α := F)
      exact (Nat.mul_eq_right (by omega)).mp h1
    exact le_antisymm hZβB (Subgroup.relIndex_eq_one.mp h3)
  intro z hz
  have h1 : (⟨z, hz.1⟩ : ↥(ZM (puAmalgam h.le) (p (x + 8)))) ∈ f.ker := by
    rw [hfker, Subgroup.mem_subgroupOf]; exact hz.2
  rw [← hkeq, Subgroup.mem_subgroupOf] at h1
  exact zh_le_zm _ hδβ h1

theorem zm_le_vhat_of_ne_two (hp : IsGoodPath _ p N) {x : ℕ} (hx : Even x) (h4 : 4 ≤ x)
    (hxN : x + 14 ≤ N) (hq : Fintype.card F ≠ 2) :
    ZM (puAmalgam c.hyp.le) (p (x + 8)) ≤ Vcirc c.hyp.le L (p (x + 6)) ⊔ ZM _ (p (x + 6)) := by
  have h := c.hyp
  have : CharP F 2 := c.charP
  have hM : ∀ k, k ≤ N → Even k → IsMVtx (puAmalgam h.le) (p k) := fun k hk hev => by
    have := c.isMVtx_add hp.toIsNBPath (x := 0) (k := k) (by omega) hp.mvtx hev
    rwa [zero_add] at this
  have hd' : ∀ i j, i ≤ j → j ≤ N → (puAmalgam h.le).treeGraph.dist (p i) (p j) = j - i :=
    fun i j hij hj => hp.dist_eq' hij hj
  have hMδ := hM (x + 6) (by omega) (hx.add (by decide))
  have hMμ := hM (x + 8) (by omega) (hx.add (by decide))
  have hδβ : (puAmalgam h.le).treeGraph.Adj (p (x + 6)) (p (x + 7)) := hp.adj (x + 6) (by omega)
  obtain ⟨ψ, hψs, hψ⟩ := exists_natural_Uloc h c.via hMδ
  obtain ⟨d, hd⟩ := c.exists_isSum_vhat hMδ hψs hψ
  have hdB := c.isSum_bloc hMδ hd
  have hdt := c.dual_eq_true hp hx h4 hxN hψs hψ hdB
  subst hdt
  set Nn := NatSec.ofIsSum hdB with hNn
  set A := natImage ψ (Qv (puAmalgam h.le) (p (x + 7))) with hAdef
  obtain ⟨hA2, hAc, hfc, h2⟩ := c.natImage_qv_props hMδ hδβ hψ
  have himg := c.img_zm_eq hp hx h4 hxN hψs hψ hdB
  have hZμV : ZM (puAmalgam h.le) (p (x + 8)) ≤ Vv _ (p (x + 6)) :=
    c.zm_le_vv_of_dist hMμ (by rw [hd' (x + 6) (x + 8) (by omega) (by omega)]; omega)
  obtain ⟨l, hl0, hl1⟩ : ∃ l : F, l ≠ 0 ∧ l ≠ 1 := by
    classical
    by_contra hcon
    push Not at hcon
    apply hq
    have hle : Fintype.card F ≤ 2 := by
      have : (Finset.univ : Finset F) ⊆ {0, 1} := fun y _ => by
        by_cases hy : y = 0
        · simp [hy]
        · simp [hcon y hy]
      calc Fintype.card F = (Finset.univ : Finset F).card := Finset.card_univ.symm
        _ ≤ ({0, 1} : Finset F).card := Finset.card_le_card this
        _ ≤ 2 := Finset.card_le_two
    have := Fintype.one_lt_card (α := F)
    omega
  obtain ⟨g', hg'N, hg'fix⟩ := (dual_fix_of_normalizer hA2 hAc hfc h2).2.2 l hl0 hl1
  obtain ⟨g, rfl⟩ := toSL3_surjective hψs g'
  have hgT := c.mem_normalizer_qv_of hMδ hδβ hψ hg'N
  have hgZ := c.normalizer_zm_right hp hx h4 (by omega) ⟨g.2, hgT⟩
  set g₀ := toSL3 ψ g with hg₀
  set D := {y : Fin 3 → F | ∀ a ∈ A, dualMat a *ᵥ y = y} with hD
  have hgDD : ∀ y ∈ D, dualMat g₀ *ᵥ y ∈ D := by
    intro y hy a ha
    have ha' : g₀⁻¹ * a * g₀⁻¹⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp (inv_mem hg'N) a).mp ha
    rw [inv_inv] at ha'
    calc dualMat a *ᵥ (dualMat g₀ *ᵥ y) = dualMat (a * g₀) *ᵥ y := by
          rw [dualMat_mul, Matrix.mulVec_mulVec]
      _ = dualMat (g₀ * (g₀⁻¹ * a * g₀)) *ᵥ y := by congr 2; group
      _ = dualMat g₀ *ᵥ (dualMat (g₀⁻¹ * a * g₀) *ᵥ y) := by
          rw [dualMat_mul, Matrix.mulVec_mulVec]
      _ = dualMat g₀ *ᵥ y := by rw [hy _ ha']
  have hgD : ∀ y ∈ D, dualMat g₀ *ᵥ y - y ∈ D := fun y hy a ha => by
    rw [Matrix.mulVec_sub, hgDD y hy a ha, hy a ha]
  have hinj : Function.Injective (fun y : ↥D =>
      (⟨dualMat g₀ *ᵥ (y : Fin 3 → F) - y, hgD y y.2⟩ : ↥D)) := by
    intro y y' hyy
    have h1 : dualMat g₀ *ᵥ (y : Fin 3 → F) - y = dualMat g₀ *ᵥ y' - y' :=
      congrArg Subtype.val hyy
    have h2 : dualMat g₀ *ᵥ ((y : Fin 3 → F) - y') = (y : Fin 3 → F) - y' := by
      rw [Matrix.mulVec_sub]
      linear_combination h1
    have hyD : (y : Fin 3 → F) - y' ∈ D := fun a ha => by
      rw [Matrix.mulVec_sub, y.2 a ha, y'.2 a ha]
    exact Subtype.ext (sub_eq_zero.mp (hg'fix _ hyD h2))
  have hsurj := Finite.injective_iff_surjective.mp hinj
  intro z hz
  have hzV := hZμV hz
  have hzD : Nn.coord z ∈ D := (himg _).mpr (Nn.mem_img.mpr ⟨z, hz, hzV, rfl⟩)
  obtain ⟨⟨y', hy'D⟩, hy'⟩ := hsurj ⟨_, hzD⟩
  have hy'eq : dualMat g₀ *ᵥ y' - y' = Nn.coord z := congrArg Subtype.val hy'
  obtain ⟨z', hz'μ, hz'V, hz'c⟩ := Nn.mem_img.mp ((himg y').mp hy'D)
  set u := (g : (puAmalgam h.le).Universal) * z' * (g : (puAmalgam h.le).Universal)⁻¹ * z'⁻¹
    with hu
  have huV : u ∈ Vv (puAmalgam h.le) (p (x + 6)) :=
    mul_mem (Nn.conj_mem g hz'V) (inv_mem hz'V)
  have huhat : u ∈ Vcirc h.le L (p (x + 6)) ⊔ ZM _ (p (x + 6)) := by
    have e : u = ⁅(g : (puAmalgam h.le).Universal), z'⁆ := by rw [commutatorElement_def]
    have h1 := Subgroup.commutator_mem_commutator g.2 hz'V
    rw [Subgroup.commutator_comm] at h1
    rw [e]
    exact c.commutator_vv_stab_le hMδ h1
  have huμ : u ∈ ZM (puAmalgam h.le) (p (x + 8)) :=
    mul_mem ((Subgroup.mem_normalizer_iff.mp hgZ z').mp hz'μ) (inv_mem hz'μ)
  have hucoord : Nn.coord u = Nn.coord z := by
    rw [hu, Nn.coord_mul (Nn.conj_mem g hz'V) (inv_mem hz'V), Nn.coord_inv hz'V,
      Nn.coord_conj g hz'V, natAct_true, hz'c, ← hy'eq, sub_eq_add_neg]
  have hw : u⁻¹ * z ∈ Bloc h.le L (p (x + 6)) := by
    refine (Nn.coord_eq_zero_iff (mul_mem (inv_mem huV) hzV)).mp ?_
    rw [Nn.coord_mul (inv_mem huV) hzV, Nn.coord_inv huV, hucoord, neg_add_cancel]
  have hwZ : u⁻¹ * z ∈ ZM (puAmalgam h.le) (p (x + 6)) :=
    c.zm_inf_bloc_le hp hx h4 hxN
      (Subgroup.mem_inf.mpr ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ huμ) hz, hw⟩)
  have e : z = u * (u⁻¹ * z) := by group
  rw [e]
  exact mul_mem huhat (Subgroup.mem_sup_right hwZ)

end GoodPath

end Ctx

end CFSG.Quasithin.MS93.S45
