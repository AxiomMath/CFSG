module

public import CFSG.Quasithin.MS93.S45I
public import CFSG.Quasithin.MS93.S45SL3
import CFSG.Quasithin.MS93.ML3AutBridge
import CFSG.Quasithin.MS93.S4A431C
import CFSG.Quasithin.MS93.S4AFMain

public section

namespace CFSG.Quasithin.MS93.S45

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Fintype F]

omit [Finite G] [Fintype F] in
theorem toSL3_eq_one_iff' {K : Subgroup G} (ψ : ↥K →* ↥(StatedSL 3 F)) (a : ↥K) :
    toSL3 ψ a = 1 ↔ ψ a = 1 := by
  rw [toSL3, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff]

namespace Ctx

variable {M T L : Subgroup G} {φ : ↥M →* ↥(StatedSL 3 F)} (c : Ctx M T L φ)
include c

theorem ker_toSL3_eq {δ : Vtx (puAmalgam c.hyp.le)} (hδ : IsMVtx _ δ)
    {ψ : ↥(stab (puAmalgam c.hyp.le) δ) →* ↥(StatedSL 3 F)}
    (hψ : IsSumOfNaturalModulesVia (stab _ δ) (Uloc c.hyp.le L δ) ⊥ ψ false 1) :
    (toSL3 ψ).ker = (Qv (puAmalgam c.hyp.le) δ).subgroupOf (stab _ δ) := by
  ext g
  rw [MonoidHom.mem_ker, toSL3_eq_one_iff hψ, Subgroup.mem_subgroupOf,
    ← S4A.stab_inf_centralizer_uloc c.hyp c.via hδ]
  constructor
  · intro hg
    refine ⟨g.2, Subgroup.mem_centralizer_iff.mpr fun v hv => ?_⟩
    have h1 := hg v hv
    have h2 : (g : (puAmalgam c.hyp.le).Universal) * v = v * g := by
      calc (g : (puAmalgam c.hyp.le).Universal) * v =
          ((g : (puAmalgam c.hyp.le).Universal) * v * (g : (puAmalgam c.hyp.le).Universal)⁻¹) *
            g := by group
        _ = v * g := by rw [h1]
    exact h2.symm
  · rintro ⟨-, hgc⟩ v hv
    rw [← Subgroup.mem_centralizer_iff.mp hgc v hv, mul_inv_cancel_right]

theorem mem_qv_iff_natImage {δ β : Vtx (puAmalgam c.hyp.le)} (hδ : IsMVtx _ δ)
    (hβ : (puAmalgam c.hyp.le).treeGraph.Adj δ β)
    {ψ : ↥(stab (puAmalgam c.hyp.le) δ) →* ↥(StatedSL 3 F)}
    (hψ : IsSumOfNaturalModulesVia (stab _ δ) (Uloc c.hyp.le L δ) ⊥ ψ false 1)
    (t : ↥(stab (puAmalgam c.hyp.le) δ)) :
    (t : (puAmalgam c.hyp.le).Universal) ∈ Qv _ β ↔ toSL3 ψ t ∈ natImage ψ (Qv _ β) := by
  constructor
  · intro ht
    exact mem_natImage.mpr ⟨t, ht, rfl⟩
  · intro ht
    obtain ⟨t', ht', he⟩ := mem_natImage.mp ht
    have hk : t'⁻¹ * t ∈ (toSL3 ψ).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, he, inv_mul_cancel]
    rw [c.ker_toSL3_eq hδ hψ, Subgroup.mem_subgroupOf] at hk
    have e : (t : (puAmalgam c.hyp.le).Universal) = t' * ((t'⁻¹ * t : ↥(stab _ δ)) : _) := by
      simp
    rw [e]
    exact mul_mem ht' (qv_le_qv _ c.hyp.hyp20 hδ hβ hk)

theorem stab_le_normalizer_bloc (δ : Vtx (puAmalgam c.hyp.le)) :
    stab (puAmalgam c.hyp.le) δ ≤
      Subgroup.normalizer (Bloc c.hyp.le L δ : Set (puAmalgam c.hyp.le).Universal) :=
  stab_le_normalizer_of_smul (F := fun δ => Bloc c.hyp.le L δ) _ (fun g δ => bloc_smul c.hyp g δ) δ

theorem commutator_stab_sup_zm {δ : Vtx (puAmalgam c.hyp.le)} (hδ : IsMVtx _ δ) :
    ⁅Vv (puAmalgam c.hyp.le) δ, stab _ δ⁆ ⊔ ZM _ δ = Vcirc c.hyp.le L δ ⊔ ZM _ δ :=
  le_antisymm (sup_le (c.commutator_vv_stab_le hδ) le_sup_right)
    (sup_le_sup_right (Subgroup.commutator_mono le_rfl (ltil_le_stab c.hyp δ)) _)

theorem commutator_qv_sup_zm {δ : Vtx (puAmalgam c.hyp.le)} (hδ : IsMVtx _ δ) :
    ⁅Vv (puAmalgam c.hyp.le) δ, Qv _ δ⁆ ⊔ ZM _ δ = ZM _ δ :=
  sup_eq_right.mpr ((c.commutator_vv_qv_le_zloc hδ).trans (zloc_le_zm c.hyp c.full hδ))

theorem vhat_inf_bloc {δ : Vtx (puAmalgam c.hyp.le)} (hδ : IsMVtx _ δ) :
    (Vcirc c.hyp.le L δ ⊔ ZM _ δ) ⊓ Bloc c.hyp.le L δ = ZM (puAmalgam c.hyp.le) δ := by
  obtain ⟨β, hβ⟩ := exists_adj _ δ
  obtain ⟨-, -, -, -, -, -, -, hPiB, -, -, -⟩ :=
    S4A.isC1_normal c.hyp c.full (by rw [c.b8]; norm_num) hδ (c.c1 δ β hδ hβ).1
  rwa [c.commutator_stab_sup_zm hδ, c.commutator_qv_sup_zm hδ] at hPiB

theorem vhat_sup_bloc {δ : Vtx (puAmalgam c.hyp.le)} (hδ : IsMVtx _ δ) :
    (Vcirc c.hyp.le L δ ⊔ ZM _ δ) ⊔ Bloc c.hyp.le L δ = Vv (puAmalgam c.hyp.le) δ := by
  obtain ⟨β, hβ⟩ := exists_adj _ δ
  obtain ⟨-, -, -, -, -, -, -, -, hPB, -, -⟩ :=
    S4A.isC1_normal c.hyp c.full (by rw [c.b8]; norm_num) hδ (c.c1 δ β hδ hβ).1
  rwa [c.commutator_stab_sup_zm hδ] at hPB

theorem exists_isSum_vhat {δ : Vtx (puAmalgam c.hyp.le)} (hδ : IsMVtx _ δ)
    {ψ : ↥(stab (puAmalgam c.hyp.le) δ) →* ↥(StatedSL 3 F)} (hψs : Function.Surjective ψ)
    (hψ : IsSumOfNaturalModulesVia (stab _ δ) (Uloc c.hyp.le L δ) ⊥ ψ false 1) :
    ∃ dual : Bool, IsSumOfNaturalModulesVia (stab _ δ) (Vcirc c.hyp.le L δ ⊔ ZM _ δ) (ZM _ δ) ψ
      dual 1 := by
  have h := c.hyp
  obtain ⟨F', iF', fF', ψ', hq', hs', hnat'⟩ := c.exists_natural_vcirc hδ
  have : CharP F 2 := c.charP
  have : CharP F' 2 := by
    obtain ⟨n, hn⟩ := c.via.1
    exact charP_two_of_card_eq_two_pow (hq'.trans hn)
  refine isSumOfNaturalModulesVia_of_surj hψs hs' ?_ hnat'
  intro a ha
  have ha' : a ∈ (toSL3 ψ).ker := by
    rw [MonoidHom.mem_ker, toSL3_eq_one_iff']
    exact ha
  rw [c.ker_toSL3_eq hδ hψ, Subgroup.mem_subgroupOf] at ha'
  have h1 := toSL3_eq_one_of_conj hnat' a (fun v hv => by
    have hvV : v ∈ Vv (puAmalgam h.le) δ := (sup_le (c.vcirc_le_vv δ) (zm_le_vv h hδ)) hv
    have hcomm : ⁅v⁻¹, (a : (puAmalgam h.le).Universal)⁆ ∈ ⁅Vv (puAmalgam h.le) δ, Qv _ δ⁆ :=
      Subgroup.commutator_mem_commutator (inv_mem hvV) ha'
    have := (c.commutator_vv_qv_le_zloc hδ).trans (zloc_le_zm h c.full hδ) hcomm
    rw [commutatorElement_def, inv_inv] at this
    simpa [mul_assoc] using this)
  rw [MonoidHom.mem_ker, ← toSL3_eq_one_iff']
  exact h1

theorem isSum_bloc {δ : Vtx (puAmalgam c.hyp.le)} (hδ : IsMVtx _ δ)
    {ψ : ↥(stab (puAmalgam c.hyp.le) δ) →* ↥(StatedSL 3 F)} {dual : Bool}
    (hd : IsSumOfNaturalModulesVia (stab _ δ) (Vcirc c.hyp.le L δ ⊔ ZM _ δ) (ZM _ δ) ψ dual 1) :
    IsSumOfNaturalModulesVia (stab _ δ) (Vv (puAmalgam c.hyp.le) δ) (Bloc c.hyp.le L δ) ψ
      dual 1 :=
  isSumOfNaturalModulesVia_sup hd (stab_le_normalizer_vv c.hyp δ) (c.stab_le_normalizer_bloc δ)
    ((sup_le (c.vcirc_le_vv δ) (zm_le_vv c.hyp hδ)).trans ((c.vv_le_qv' hδ).trans
      ((qv_le_stab _ δ).trans (c.stab_le_normalizer_bloc δ))))
    (c.vhat_sup_bloc hδ) (c.vhat_inf_bloc hδ)

theorem hloc_le_bloc {δ : Vtx (puAmalgam c.hyp.le)} (hδ : IsMVtx _ δ) :
    Hloc c.hyp.le L δ ≤ Bloc c.hyp.le L δ :=
  (Subgroup.commutator_mono (c.vcirc_le_vv δ) le_rfl).trans ((c.commutator_vv_qv_le_zloc hδ).trans
    ((zloc_le_zm c.hyp c.full hδ).trans (zm_le_bloc c.hyp (by rw [c.b8]; norm_num) hδ)))

section GoodPath

variable {p : ℕ → Vtx (puAmalgam c.hyp.le)} {N : ℕ}

theorem dual_eq_true (hp : IsGoodPath _ p N) {x : ℕ} (hx : Even x) (h4 : 4 ≤ x)
    (hxN : x + 14 ≤ N) {ψ : ↥(stab (puAmalgam c.hyp.le) (p (x + 6))) →* ↥(StatedSL 3 F)}
    (hψs : Function.Surjective ψ)
    (hψ : IsSumOfNaturalModulesVia (stab _ (p (x + 6))) (Uloc c.hyp.le L (p (x + 6))) ⊥ ψ
      false 1) {dual : Bool}
    (hd : IsSumOfNaturalModulesVia (stab _ (p (x + 6))) (Vv (puAmalgam c.hyp.le) (p (x + 6)))
      (Bloc c.hyp.le L (p (x + 6))) ψ dual 1) : dual = true := by
  cases dual with
  | true => rfl
  | false =>
  exfalso
  have h := c.hyp
  have h20 := h.hyp20
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
  have hβH : ¬ IsMVtx (puAmalgam h.le) (p (x + 7)) := by
    rw [← isMVtx_iff_of_adj _ hδβ]; exact hMδ
  set Nn := NatSec.ofIsSum hd with hNn
  set A := natImage ψ (Qv (puAmalgam h.le) (p (x + 7))) with hAdef
  have hTs : Qv (puAmalgam h.le) (p (x + 7)) ≤ stab _ (p (x + 6)) :=
    qv_le_stab_of_adj _ hδβ.symm
  have hA2 : IsPGroup 2 A := by
    have h1 : IsPGroup 2 (Qv (puAmalgam h.le) (p (x + 7))) := isPGroup_qv _ h20 hβH
    exact (h1.of_equiv (Subgroup.subgroupOfEquivOfLe hTs).symm).map _
  have hAc : Nat.card A = Nat.card F ^ 2 := by
    rw [Nat.card_eq_fintype_card (α := F)]; exact c.card_natImage_qv hψ hMδ hδβ
  have hfc := c.fixN_eq_commN_qv hψ hMδ hδβ
  have hZμV : ZM (puAmalgam h.le) (p (x + 8)) ≤ Vv _ (p (x + 6)) :=
    c.zm_le_vv_of_dist hMμ (by rw [hd' (x + 6) (x + 8) (by omega) (by omega)]; omega)
  have hHB : Usup (puAmalgam h.le) (p (x + 8)) (p (x + 7)) ≤ Bloc h.le L (p (x + 6)) := by
    rw [← c.hloc_eq_usup' hp hx h4 (by omega)]
    exact c.hloc_le_bloc hMδ
  set S := Nn.img (ZM (puAmalgam h.le) (p (x + 8))) with hSdef
  have hSfix : ∀ y ∈ S, y ∈ fixN A := by
    intro y hy
    obtain ⟨z, hzμ, hzV, rfl⟩ := Nn.mem_img.mp hy
    rw [mem_fixN]
    intro g hg
    obtain ⟨t, ht, rfl⟩ := mem_natImage.mp hg
    have h1 := Nn.coord_conj t hzV
    rw [natAct_false] at h1
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
  have hinv : ∀ g ∈ Subgroup.normalizer (A : Set (SL3 F)), ∀ y ∈ S,
      ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ y ∈ S := by
    intro g' hg' y hy
    obtain ⟨z, hzμ, hzV, rfl⟩ := Nn.mem_img.mp hy
    obtain ⟨g, rfl⟩ := toSL3_surjective hψs g'
    have hgT : (g : (puAmalgam h.le).Universal) ∈
        Subgroup.normalizer (Qv (puAmalgam h.le) (p (x + 7)) : Set _) := by
      rw [Subgroup.mem_normalizer_iff]
      intro t
      constructor
      · intro ht
        have hts : t ∈ stab (puAmalgam h.le) (p (x + 6)) := hTs ht
        set t' : ↥(stab (puAmalgam h.le) (p (x + 6))) := ⟨t, hts⟩ with ht'
        have h1 := (c.mem_qv_iff_natImage hMδ hδβ hψ t').mp ht
        have h2 : toSL3 ψ (g * t' * g⁻¹) ∈ A := by
          rw [map_mul, map_mul, map_inv]
          exact (Subgroup.mem_normalizer_iff.mp hg' _).mp h1
        exact (c.mem_qv_iff_natImage hMδ hδβ hψ (g * t' * g⁻¹)).mpr h2
      · intro ht
        have hts : t ∈ stab (puAmalgam h.le) (p (x + 6)) := by
          have h1 : (g : (puAmalgam h.le).Universal) * t * (g : (puAmalgam h.le).Universal)⁻¹ ∈
              stab _ (p (x + 6)) := hTs ht
          have h2 := mul_mem (mul_mem (inv_mem g.2) h1) g.2
          have e : (g : (puAmalgam h.le).Universal)⁻¹ *
              ((g : (puAmalgam h.le).Universal) * t * (g : (puAmalgam h.le).Universal)⁻¹) *
                (g : (puAmalgam h.le).Universal) = t := by group
          rwa [e] at h2
        set t' : ↥(stab (puAmalgam h.le) (p (x + 6))) := ⟨t, hts⟩ with ht'
        have h1 := (c.mem_qv_iff_natImage hMδ hδβ hψ (g * t' * g⁻¹)).mp ht
        rw [map_mul, map_mul, map_inv] at h1
        have h2 := (Subgroup.mem_normalizer_iff.mp hg' _).mpr h1
        exact (c.mem_qv_iff_natImage hMδ hδβ hψ t').mpr h2
    have hgZ := c.normalizer_zm_right hp hx h4 (by omega) ⟨g.2, hgT⟩
    refine Nn.mem_img.mpr ⟨g * z * (g : (puAmalgam h.le).Universal)⁻¹,
      (Subgroup.mem_normalizer_iff.mp hgZ z).mp hzμ, Nn.conj_mem g hzV, ?_⟩
    rw [Nn.coord_conj g hzV, natAct_false]
  have hall := mem_of_normalizer_invariant hA2 hAc hfc.1 (hfc.1 ▸ hfc.2) S hSfix hne hinv
  let f : ↥(ZM (puAmalgam h.le) (p (x + 8))) →* Multiplicative (Fin 3 → F) :=
    { toFun := fun z => Multiplicative.ofAdd (Nn.coord z)
      map_one' := by simp [Nn.coord_one]
      map_mul' := fun z w => by
        simp only [Subgroup.coe_mul]
        rw [Nn.coord_mul (hZμV z.2) (hZμV w.2), ofAdd_add] }
  have hker : (ZH (puAmalgam h.le) (p (x + 7))).subgroupOf (ZM _ (p (x + 8))) ≤ f.ker := by
    intro z hz
    rw [Subgroup.mem_subgroupOf] at hz
    rw [MonoidHom.mem_ker]
    show Multiplicative.ofAdd (Nn.coord z) = 1
    rw [(Nn.coord_eq_zero_iff (hZμV z.2)).mpr ((zh_le_zm _ hδβ).trans
      (zm_le_bloc h (by rw [c.b8]; norm_num) hMδ) hz), ofAdd_zero]
  have hidx : (ZH (puAmalgam h.le) (p (x + 7))).relIndex (ZM _ (p (x + 8))) = Fintype.card F :=
    c.relIndex_zh hMμ hμβ
  have hrange : Nat.card f.range ≤ Fintype.card F := by
    rw [← Subgroup.index_ker, ← hidx]
    exact Nat.le_of_dvd (by rw [hidx]; exact Fintype.card_pos) (Subgroup.index_dvd_of_le hker)
  have hfix : Nat.card ↥(fixN A) ≤ Nat.card f.range := by
    have hmem : ∀ y : ↥(fixN A), Multiplicative.ofAdd (y : Fin 3 → F) ∈ f.range := by
      intro y
      obtain ⟨z, hzμ, hzV, hze⟩ := Nn.mem_img.mp (hall y y.2)
      exact ⟨⟨z, hzμ⟩, by show Multiplicative.ofAdd (Nn.coord z) = _; rw [hze]⟩
    let ι : ↥(fixN A) → ↥f.range := fun y => ⟨Multiplicative.ofAdd (y : Fin 3 → F), hmem y⟩
    have hι : Function.Injective ι := fun y y' hyy => by
      have h1 : ((ι y : ↥f.range) : Multiplicative (Fin 3 → F)) = ι y' := congrArg Subtype.val hyy
      exact Subtype.ext (Multiplicative.ofAdd.injective h1)
    exact Nat.card_le_card_of_injective ι hι
  have hcard : Nat.card ↥(fixN A) = Fintype.card F ^ 2 := by
    rw [Module.natCard_eq_pow_finrank (K := F), hfc.2, Nat.card_eq_fintype_card]
  have hq := Fintype.one_lt_card (α := F)
  have : Fintype.card F < Fintype.card F ^ 2 := by
    calc Fintype.card F = Fintype.card F * 1 := (mul_one _).symm
      _ < Fintype.card F * Fintype.card F := Nat.mul_lt_mul_of_pos_left hq (by omega)
      _ = Fintype.card F ^ 2 := (sq _).symm
  omega

theorem bloc_le_qv (hp : IsGoodPath _ p N) {x : ℕ} (hx : Even x) (h10 : 10 ≤ x)
    (hxN : x + 12 ≤ N) : Bloc c.hyp.le L (p x) ≤ Qv (puAmalgam c.hyp.le) (p (x + 6)) := by
  have h := c.hyp
  have h20 := h.hyp20
  have : CharP F 2 := c.charP
  have hM : ∀ k, k ≤ N → Even k → IsMVtx (puAmalgam h.le) (p k) := fun k hk hev => by
    have := c.isMVtx_add hp.toIsNBPath (x := 0) (k := k) (by omega) hp.mvtx hev
    rwa [zero_add] at this
  have hd' : ∀ i j, i ≤ j → j ≤ N → (puAmalgam h.le).treeGraph.dist (p i) (p j) = j - i :=
    fun i j hij hj => hp.dist_eq' hij hj
  have hM0 := hM x (by omega) hx
  have hM6 := hM (x + 6) (by omega) (hx.add (by decide))
  have hM8 := hM (x + 8) (by omega) (hx.add (by decide))
  have hc := c.isCritical_of_isGoodPath hp hx (by omega)
  have hVs : Vv (puAmalgam h.le) (p x) ≤ stab _ (p x) := (c.vv_le_qv' hM0).trans (qv_le_stab _ _)
  set Y := Vv (puAmalgam h.le) (p x) ⊓ Qv _ (p (x + 6)) with hYdef
  have hY : Y.relIndex (Vv (puAmalgam h.le) (p x)) ≤ Fintype.card F := by
    obtain ⟨ψ₆, -, hψ₆⟩ := exists_natural_Uloc h c.via hM6
    have ha65 : (puAmalgam h.le).treeGraph.Adj (p (x + 6)) (p (x + 5)) :=
      (hp.adj (x + 5) (by omega)).symm
    have hVT : Vv (puAmalgam h.le) (p x) ≤ Qv _ (p (x + 5)) :=
      vi_le_qv _ (by rw [hd' x (x + 5) (by omega) (by omega), c.b8]; omega)
    have hVs6 : Vv (puAmalgam h.le) (p x) ≤ stab _ (p (x + 6)) :=
      hVT.trans (qv_le_stab_of_adj _ ha65.symm)
    have hYC : Y = Vv (puAmalgam h.le) (p x) ⊓
        Subgroup.centralizer (Uloc h.le L (p (x + 6)) : Set _) := by
      rw [hYdef, ← c.qv_inf_centralizer_uloc hM6 ha65, ← inf_assoc, inf_eq_left.mpr hVT]
    set E := natImage ψ₆ (Vv (puAmalgam h.le) (p x)) with hEdef
    have hET : E ≤ natImage ψ₆ (Qv (puAmalgam h.le) (p (x + 5))) := natImage_mono hVT
    have hT := c.fixN_eq_commN_qv hψ₆ hM6 ha65
    have hcommE : Module.finrank F ↥(commN E) ≤ 1 := by
      have h1 := card_commutator_eq hψ₆ hVs6
      have h2 : ⁅Uloc h.le L (p (x + 6)), Vv (puAmalgam h.le) (p x)⁆ ≤
          critR (puAmalgam h.le) (p (x - 2)) (p (x + 6)) := by
        rw [← c.commutator_vv_zm hp hx h10 (by omega), Subgroup.commutator_comm]
        exact Subgroup.commutator_mono le_rfl (uloc_le_zm h c.full hM6)
      have hR : Nat.card ↥(critR (puAmalgam h.le) (p (x - 2)) (p (x + 6))) = Fintype.card F := by
        obtain ⟨y, rfl⟩ : ∃ y, x = y + 2 := ⟨x - 2, by omega⟩
        have hy : Even y := (Nat.even_add.mp hx).mpr (by decide)
        have hgpd := c.zh_ne_of_isGoodPath hp (y := y + 4) (hy.add (by decide)) (by omega)
          (by omega)
        rw [show y + 4 - 1 = y + 3 by omega, show y + 4 + 1 = y + 5 by omega] at hgpd
        have := c.card_critR hp.toIsNBPath (x := y) (by omega)
          (c.isCritical_of_isGoodPath hp hy (by omega)) (c.straight_of_isGoodPath hp hy (by omega))
          hgpd
        rwa [show y + 2 - 2 = y by omega, show y + 2 + 6 = y + 8 by omega]
      have hfinR : Finite ↥(critR (puAmalgam h.le) (p (x - 2)) (p (x + 6))) :=
        Nat.finite_of_card_ne_zero (by rw [hR]; exact Fintype.card_ne_zero)
      have h3 := Subgroup.card_le_of_le h2
      rw [← hEdef] at h1
      rw [hR, h1, Module.natCard_eq_pow_finrank (K := F), Nat.card_eq_fintype_card] at h3
      by_contra hlt
      push Not at hlt
      have : Fintype.card F ^ 2 ≤ Fintype.card F ^ Module.finrank F ↥(commN E) :=
        Nat.pow_le_pow_right Fintype.card_pos (by omega)
      have hq := Fintype.one_lt_card (α := F)
      have : Fintype.card F < Fintype.card F ^ 2 := by
        calc Fintype.card F = Fintype.card F * 1 := (mul_one _).symm
          _ < Fintype.card F * Fintype.card F := Nat.mul_lt_mul_of_pos_left hq (by omega)
          _ = Fintype.card F ^ 2 := (sq _).symm
      omega
    have hEq : Nat.card ↥E ≤ Fintype.card F := by
      have hb := card_le_pow_finrank E
      have hfixE : 2 ≤ Module.finrank F ↥(fixN E) := hT.2 ▸ Submodule.finrank_mono (fixN_anti hET)
      have hexp : (3 - Module.finrank F ↥(fixN E)) * Module.finrank F ↥(commN E) ≤ 1 := by
        calc (3 - Module.finrank F ↥(fixN E)) * Module.finrank F ↥(commN E)
            ≤ 1 * 1 := Nat.mul_le_mul (by omega) hcommE
          _ = 1 := rfl
      rw [Nat.card_eq_fintype_card (α := F)] at hb
      calc Nat.card ↥E ≤ _ := hb
        _ ≤ Fintype.card F ^ 1 := Nat.pow_le_pow_right Fintype.card_pos hexp
        _ = Fintype.card F := pow_one _
    have h1 := card_natImage_mul hψ₆ hVs6
    have h2 := Subgroup.relIndex_mul_card Y (Vv (puAmalgam h.le) (p x))
    have hYV : Y ⊓ Vv (puAmalgam h.le) (p x) = Y := inf_eq_left.mpr inf_le_left
    rw [hYV] at h2
    rw [← hYC] at h1
    have : Finite ↥(stab (puAmalgam h.le) (p x)) := S4A.finite_stab h hM0
    have : Finite ↥Y := Finite.of_injective _ (Subgroup.inclusion_injective (inf_le_left.trans hVs))
    have hpos : 0 < Nat.card ↥Y := Nat.card_pos
    have : Y.relIndex (Vv (puAmalgam h.le) (p x)) = Nat.card ↥E := by
      have := h2.trans h1.symm
      exact Nat.eq_of_mul_eq_mul_right hpos this
    rw [this]
    exact hEq
  obtain ⟨ψ₀, hψ₀s, hψ₀⟩ := exists_natural_Uloc h c.via hM0
  obtain ⟨d, hd⟩ := c.exists_isSum_vhat hM0 hψ₀s hψ₀
  have hdB := c.isSum_bloc hM0 hd
  set Nn := NatSec.ofIsSum hdB with hNn
  have hc' := c.isCritical_symm hc
  obtain ⟨z, hzZ, hzQ⟩ := Set.not_subset.mp hc'.2.2
  have hzs : z ∈ stab (puAmalgam h.le) (p x) := zm_le_stab_of_isCritical _ h20 c.bpos hc hzZ
  set g := toSL3 ψ₀ ⟨z, hzs⟩ with hg
  have hg1 : g ≠ 1 := by
    intro h1
    have : (⟨z, hzs⟩ : ↥(stab (puAmalgam h.le) (p x))) ∈ (toSL3 ψ₀).ker := h1
    rw [c.ker_toSL3_eq hM0 hψ₀, Subgroup.mem_subgroupOf] at this
    exact hzQ this
  obtain ⟨y₀, hy₀⟩ : ∃ y₀ : Fin 3 → F, natAct d g *ᵥ y₀ ≠ y₀ := by
    by_contra hcon
    push Not at hcon
    exact hg1 (eq_one_of_natAct_mulVec_eq_self d hcon)
  let Sfix : AddSubgroup (Fin 3 → F) :=
    { carrier := {y | natAct d g *ᵥ y = y}
      zero_mem' := Matrix.mulVec_zero _
      add_mem' := fun {y y'} hy hy' => by
        show natAct d g *ᵥ (y + y') = y + y'
        rw [Matrix.mulVec_add, show natAct d g *ᵥ y = y from hy,
          show natAct d g *ᵥ y' = y' from hy']
      neg_mem' := fun {y} hy => by
        show natAct d g *ᵥ (-y) = -y
        rw [Matrix.mulVec_neg, show natAct d g *ᵥ y = y from hy] }
  set C := Nn.pre Sfix with hCdef
  have hCV : C ≤ Vv (puAmalgam h.le) (p x) := fun v hv => (Nn.mem_pre.mp hv).1
  have hBC : Bloc h.le L (p x) ≤ C := by
    intro b hb
    have hbV := bloc_le_vv h (p x) hb
    refine Nn.mem_pre.mpr ⟨hbV, ?_⟩
    rw [(Nn.coord_eq_zero_iff hbV).mpr hb]
    exact Sfix.zero_mem
  have hYC' : Y ≤ C := by
    intro v hv
    have hvV : v ∈ Vv (puAmalgam h.le) (p x) := hv.1
    refine Nn.mem_pre.mpr ⟨hvV, ?_⟩
    have hv2 := c.vv_inf_qv_le hp hx (by omega) hxN hv
    have hZn : ZM (puAmalgam h.le) (p x) ≤
        Subgroup.normalizer (Qv (puAmalgam h.le) (p (x + 8)) : Set _) := by
      have hd7 : (puAmalgam h.le).treeGraph.dist (p x) (p (x + 7)) <
          critDist (puAmalgam h.le) := by
        rw [hd' x (x + 7) (by omega) (by omega), c.b8]; omega
      exact (zm_le_qv_of_dist_lt _ hM0 hd7).trans
        ((qv_le_stab_of_adj _ (hp.adj (x + 7) (by omega))).trans (stab_le_normalizer_qv _ _))
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hZn] at hv2
    obtain ⟨w, hw, q, hq, rfl⟩ := Set.mem_mul.mp hv2
    have hzq : z * q = q * z :=
      (Subgroup.mem_centralizer_iff.mp (zm_le_centralizer_qv _ h20 hM8 hzZ) q hq).symm
    have hr : w⁻¹ * (z * w * z⁻¹) ∈ critR (puAmalgam h.le) (p x) (p (x + 8)) := by
      have : w⁻¹ * (z * w * z⁻¹) = ⁅w⁻¹, z⁆ := by rw [commutatorElement_def]; group
      rw [this]
      exact Subgroup.commutator_mem_commutator (inv_mem hw) hzZ
    have hrq : q⁻¹ * (w⁻¹ * (z * w * z⁻¹)) * q = w⁻¹ * (z * w * z⁻¹) := by
      have hmem := (uloc_le_zm h c.full hM8) (c.critR_le_uloc' hc hr)
      have := (Subgroup.mem_centralizer_iff.mp (zm_le_centralizer_qv _ h20 hM8 hmem) q hq)
      calc q⁻¹ * (w⁻¹ * (z * w * z⁻¹)) * q = q⁻¹ * (q * (w⁻¹ * (z * w * z⁻¹))) := by
            rw [mul_assoc, this]
        _ = _ := by group
    have hzq' : z⁻¹ * q = q * z⁻¹ := by
      calc z⁻¹ * q = z⁻¹ * (q * z) * z⁻¹ := by group
        _ = z⁻¹ * (z * q) * z⁻¹ := by rw [hzq]
        _ = q * z⁻¹ := by group
    have he : (w * q)⁻¹ * (z * (w * q) * z⁻¹) = w⁻¹ * (z * w * z⁻¹) := by
      rw [← hrq]
      calc (w * q)⁻¹ * (z * (w * q) * z⁻¹) = q⁻¹ * w⁻¹ * z * w * (q * z⁻¹) := by group
        _ = q⁻¹ * w⁻¹ * z * w * (z⁻¹ * q) := by rw [hzq']
        _ = _ := by group
    have hB : (w * q)⁻¹ * (z * (w * q) * z⁻¹) ∈ Bloc h.le L (p x) := by
      rw [he]
      exact zm_le_bloc h (by rw [c.b8]; norm_num) hM0
        (uloc_le_zm h c.full hM0 (c.critR_le_uloc hc hr))
    have hcz := Nn.coord_conj ⟨z, hzs⟩ hvV
    have h0 := (Nn.coord_eq_zero_iff (Subgroup.mul_mem _ (inv_mem hvV)
      (Nn.conj_mem ⟨z, hzs⟩ hvV))).mpr hB
    rw [Nn.coord_mul (inv_mem hvV) (Nn.conj_mem ⟨z, hzs⟩ hvV), Nn.coord_inv hvV,
      neg_add_eq_zero] at h0
    show natAct d g *ᵥ Nn.coord (w * q) = Nn.coord (w * q)
    rw [← hcz]
    exact h0.symm
  have hCidx : Fintype.card F ≤ C.relIndex (Vv (puAmalgam h.le) (p x)) := by
    have hv : ∀ t : F, ∃ v ∈ Vv (puAmalgam h.le) (p x), Nn.coord v = t • y₀ :=
      fun t => Nn.exists_coord_eq (t • y₀)
    choose v hvV hvc using hv
    rw [Subgroup.relIndex, Subgroup.index, ← Nat.card_eq_fintype_card]
    have : Finite ↥(stab (puAmalgam h.le) (p x)) := S4A.finite_stab h hM0
    have : Finite ↥(Vv (puAmalgam h.le) (p x)) :=
      Finite.of_injective _ (Subgroup.inclusion_injective hVs)
    have : Finite (↥(Vv (puAmalgam h.le) (p x)) ⧸ C.subgroupOf (Vv (puAmalgam h.le) (p x))) :=
      Finite.of_surjective _ QuotientGroup.mk_surjective
    refine Nat.card_le_card_of_injective (fun t => (⟨v t, hvV t⟩ : ↥(Vv _ (p x)))) ?_
    intro t t' htt
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at htt
    have h1 := (Nn.mem_pre.mp htt).2
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h1
    rw [Nn.coord_mul (inv_mem (hvV t)) (hvV t'), Nn.coord_inv (hvV t), hvc, hvc] at h1
    have h2 : natAct d g *ᵥ ((t' - t) • y₀) = (t' - t) • y₀ := by
      rw [sub_smul]
      have := h1
      rw [neg_add_eq_sub] at this
      exact this
    rw [Matrix.mulVec_smul] at h2
    by_contra hne
    apply hy₀
    have hts : t' - t ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
    exact smul_right_injective _ hts h2
  have hmul := Subgroup.relIndex_mul_relIndex Y C (Vv (puAmalgam h.le) (p x)) hYC' hCV
  have hq0 := Fintype.card_pos (α := F)
  have hCpos : 0 < C.relIndex (Vv (puAmalgam h.le) (p x)) := by omega
  have : Finite ↥(stab (puAmalgam h.le) (p x)) := S4A.finite_stab h hM0
  have : Finite ↥C := Finite.of_injective _ (Subgroup.inclusion_injective (hCV.trans hVs))
  have hYC1 : Y.relIndex C = 1 := by
    have hYCpos : Y.relIndex C ≠ 0 := Subgroup.index_ne_zero_of_finite
    have : Y.relIndex C * C.relIndex (Vv (puAmalgam h.le) (p x)) ≤
        1 * C.relIndex (Vv (puAmalgam h.le) (p x)) := by
      rw [hmul, one_mul]; omega
    have := Nat.le_of_mul_le_mul_right this hCpos
    omega
  have hCY : C ≤ Y := Subgroup.relIndex_eq_one.mp hYC1
  exact hBC.trans (hCY.trans inf_le_right)

end GoodPath

end Ctx

end CFSG.Quasithin.MS93.S45
