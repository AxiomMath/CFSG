module

public import CFSG.RankThree.GF2n.Tim81.Sec7.S73BarIso
import CFSG.RankThree.GF2n.Tim81.Sec6.RootImages
import CFSG.RankThree.GF2n.Tim81.Sec7.S73Split
import CFSG.RankThree.GF2n.Tim81.Sec7.Transport

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Tim78
open CFSG.RankThree.GF2n.Tim81.Sec7 (yOf rOf oOf)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M V A B : Subgroup G} {h : G} {n f : ℕ}

theorem IsSUImage.exists_conj_eq {K : Type} [Group K] {X : Subgroup K} {Δ : Set (Subgroup K)}
    {f m : ℕ} {hf : 1 ≤ f} {hm : 2 ≤ m} (hX : IsSUImage X Δ f m hf hm) {T₁ T₂ : Subgroup K}
    (h₁ : T₁ ∈ Δ) (h₂ : T₂ ∈ Δ) : ∃ x ∈ X, T₂ = conjSubgroup x T₁ := by
  obtain ⟨Φ, -, hrange, hclass⟩ := hX
  obtain ⟨x₁, rfl⟩ := (hclass T₁).mp h₁
  obtain ⟨x₂, rfl⟩ := (hclass T₂).mp h₂
  refine ⟨Φ (x₂ * x₁⁻¹), hrange.le (MonoidHom.mem_range.mpr ⟨_, rfl⟩), ?_⟩
  rw [← CFSG.CGT.Timmesfeld75.map_conjSubgroup]
  congr 1
  change conjSubgroup x₂ _ = conjSubgroup (x₂ * x₁⁻¹) (conjSubgroup x₁ _)
  rw [conjSubgroup_conjSubgroup, inv_mul_cancel_right]

namespace EpsIn

theorem inSubgroup_pCore_inf_cenOf_barY (hE : EpsIn M V h) {P : Subgroup G}
    (hP : inSubgroup (pCore 2) (barY h (rOf M h)) = barY h P) (hPc : P ≤ cenOf V)
    (hP2 : IsPGroup 2 P) {m : ℕ} (hf : 1 ≤ f) (hm : 4 ≤ m)
    {X₀ : Subgroup (YBar h)} [X₀.Normal] (hC : Subgroup.centralizer (X₀ : Set (YBar h)) = ⊥)
    (hSU : IsSUImage X₀ (barRoots h V) f m hf (Nat.le_trans (Nat.le_add_left 2 2) hm)) :
    inSubgroup (pCore 2) (X₀ ⊓ cenOf (barY h V)) = barY h P := by
  obtain ⟨hQ2, hQS, -⟩ := inSubgroup_pCore_two (X₀ ⊓ cenOf (barY h V))
  obtain ⟨-, -, hRP'⟩ := inSubgroup_pCore_two (barY h (rOf M h))
  rw [hP] at hRP'
  have hSR : X₀ ⊓ cenOf (barY h V) ≤ barY h (rOf M h) :=
    inf_le_right.trans ((Subgroup.centralizer_le_normalizer _).trans hE.normalizer_barY.le)
  have hRS : barY h (rOf M h) ≤
      Subgroup.normalizer ((X₀ ⊓ cenOf (barY h V) : Subgroup (YBar h)) : Set (YBar h)) :=
    fun r hr => mem_normalizer_inf ((Subgroup.normalizer_eq_top X₀).ge (Subgroup.mem_top r))
      (mem_normalizer_centralizer (hE.normalizer_barY.ge hr))
  have hT : barY h V ∈ barRoots h V := ⟨1, (conjSubgroup_one _).symm⟩
  apply le_antisymm
  · rw [← hP]
    exact le_inSubgroup_pCore (hQS.trans hSR)
      (fun r hr => mem_normalizer_map_subtype_of_characteristic (hRS hr)
        (pCore 2 ↥(X₀ ⊓ cenOf (barY h V)))) hQ2
  · have hA := hSU.le_pCore_sup_cenOf hm hT (isPGroup_barY h hP2) (barY_le_centralizer h hPc)
      fun x hx => hRP' (hE.normalizer_barY.le (Subgroup.mem_inf.1 hx).2)
    rwa [show cenOf X₀ = ⊥ from hC, sup_bot_eq] at hA

theorem eq_of_isSUImage_barY (hE : EpsIn M V h) (hS : Sec7Hyp M V n f)
    (hD : L2Datum M V A B h) (h72 : Sec7.Stmt72 M V n f)
    (hP : inSubgroup (pCore 2) (barY h (rOf M h)) = barY h (p0Of M V (A ⊔ B)))
    {m : ℕ} (hm : 4 ≤ m)
    {X₀ : Subgroup (YBar h)} [X₀.Normal] (hC : Subgroup.centralizer (X₀ : Set (YBar h)) = ⊥)
    (hSU : IsSUImage X₀ (barRoots h V) f m hS.one_le
      (Nat.le_trans (Nat.le_add_left 2 2) hm)) : m = n := by
  have hT : barY h V ∈ barRoots h V := ⟨1, (conjSubgroup_one _).symm⟩
  have hcard := hSU.natCard_pCore_cenOf hm hT
  have hP2 : IsPGroup 2 (p0Of M V (A ⊔ B)) :=
    (inSubgroup_pCore_two M).1.to_le (inf_le_left.trans inf_le_left)
  rw [hE.inSubgroup_pCore_inf_cenOf_barY hP (inf_le_left.trans inf_le_right) hP2
      hS.one_le hm hC hSU,
    hE.card_barY_of_disjoint ((hD.p0_le_rOf hS.toSec6Hyp).trans inf_le_right)
      (hE.disjoint_oddCore_of_isPGroup hP2),
    (h72 A B h hD).2.1, hS.card_V] at hcard
  have h2 : 2 ≤ 2 ^ f :=
    (pow_one (2 : ℕ)).symm.trans_le (Nat.pow_le_pow_right (by norm_num) hS.one_le)
  have := Nat.pow_right_injective h2 hcard
  have := hS.four_le
  omega

theorem barY_y0Of (hE : EpsIn M V h) :
    barY h (y0Of V (Subgroup.zpowers h)) = Subgroup.normalClosure (barY h V : Set (YBar h)) := by
  apply le_antisymm
  · rw [barY_le_iff_le_preimY h hE.y0Of_le_yOf]
    unfold y0Of
    refine iSup₂_le fun x hx => ?_
    rw [← barY_le_iff_le_preimY h (hE.conjSubgroup_le_yOf hx), ← barY_conj h hx hE.le_yOf]
    have hle : barY h V ≤ Subgroup.normalClosure (barY h V : Set (YBar h)) :=
      fun _ hu => Subgroup.subset_normalClosure hu
    exact (conjSubgroup_mono hle).trans
      (conjSubgroup_eq_self_iff.mpr ((Subgroup.normalizer_eq_top
        (Subgroup.normalClosure (barY h V : Set (YBar h)))).ge (Subgroup.mem_top _))).le
  · haveI := normal_barY h (cenOf_le_normalizer_y0Of V (Subgroup.zpowers h))
    exact Subgroup.normalClosure_le_normal (barY_mono h (le_y0Of V _))

theorem conj_eq_of_barY_conj_eq (hE : EpsIn M V h) {x y : G} (hx : x ∈ yOf h) (hy : y ∈ yOf h)
    (hxy : barY h (conjSubgroup x V) = barY h (conjSubgroup y V)) :
    conjSubgroup x V = conjSubgroup y V := by
  rw [← barY_conj h hx hE.le_yOf, ← barY_conj h hy hE.le_yOf] at hxy
  have hyx : y⁻¹ * x ∈ yOf h := (yOf h).mul_mem ((yOf h).inv_mem hy) hx
  have hN : (QuotientGroup.mk' (pPrimeCore 2 ↥(yOf h)) ⟨y, hy⟩)⁻¹ *
      QuotientGroup.mk' (pPrimeCore 2 ↥(yOf h)) ⟨x, hx⟩ ∈
      Subgroup.normalizer (barY h V : Set (YBar h)) := by
    rw [← conjSubgroup_eq_self_iff, conjSubgroup_mul, hxy, ← conjSubgroup_mul, inv_mul_cancel,
      conjSubgroup_one]
  rw [← map_inv, ← map_mul, hE.normalizer_barY] at hN
  have hV : conjSubgroup (y⁻¹ * x) V = V :=
    conjSubgroup_eq_self_iff.mpr (hE.root.le_normalizer (hE.mem_rOf_of_bar_mem hyx hN).1)
  calc conjSubgroup x V = conjSubgroup y (conjSubgroup (y⁻¹ * x) V) := by
        rw [← conjSubgroup_mul, mul_inv_cancel_left]
    _ = conjSubgroup y V := by rw [hV]

theorem exists_conj_eq_y0Of (hE : EpsIn M V h) {m : ℕ} {hf : 1 ≤ f} {hm : 2 ≤ m}
    (hSU : IsSUImage (barY h (y0Of V (Subgroup.zpowers h))) (barRoots h V) f m hf hm)
    {y : G} (hy : y ∈ yOf h) :
    ∃ x ∈ y0Of V (Subgroup.zpowers h), conjSubgroup y V = conjSubgroup x V := by
  have hV : barY h V ∈ barRoots h V := ⟨1, (conjSubgroup_one _).symm⟩
  have hVy : barY h (conjSubgroup y V) ∈ barRoots h V := ⟨_, (barY_conj h hy hE.le_yOf).symm⟩
  obtain ⟨xbar, hxbar, hxeq⟩ := hSU.exists_conj_eq hV hVy
  obtain ⟨⟨x, hxY⟩, hx0, rfl⟩ := hxbar
  refine ⟨x, Subgroup.mem_subgroupOf.mp hx0, hE.conj_eq_of_barY_conj_eq hy hxY ?_⟩
  rw [hxeq, barY_conj h hxY hE.le_yOf]

theorem pCore_y0Of_eq_bot (hE : EpsIn M V h) (ho2 : pCore 2 (YBar h) = ⊥) :
    pCore 2 ↥(y0Of V (Subgroup.zpowers h)) = ⊥ := by
  have hQ2 : IsPGroup 2 (inSubgroup (pCore 2) (y0Of V (Subgroup.zpowers h))) :=
    (inSubgroup_pCore_two _).1
  have hQY : inSubgroup (pCore 2) (y0Of V (Subgroup.zpowers h)) ≤ yOf h :=
    (inSubgroup_pCore_two _).2.1.trans hE.y0Of_le_yOf
  have hYQ : yOf h ≤ Subgroup.normalizer
      (inSubgroup (pCore 2) (y0Of V (Subgroup.zpowers h)) : Set G) := fun y hy =>
    mem_normalizer_map_subtype_of_characteristic (cenOf_le_normalizer_y0Of V _ hy)
      (pCore 2 ↥(y0Of V (Subgroup.zpowers h)))
  haveI := normal_barY h hYQ
  have hle : barY h (inSubgroup (pCore 2) (y0Of V (Subgroup.zpowers h))) ≤ pCore 2 (YBar h) :=
    le_sSup ⟨inferInstance, isPGroup_barY h hQ2⟩
  have hbot := le_bot_iff.mp (hle.trans ho2.le)
  have hQ1 : Nat.card (inSubgroup (pCore 2) (y0Of V (Subgroup.zpowers h))) = 1 := by
    rw [← hE.card_barY_of_disjoint hQY (hE.disjoint_oddCore_of_isPGroup hQ2), hbot,
      Subgroup.card_bot]
  exact (Subgroup.map_eq_bot_iff_of_injective (pCore 2 ↥(y0Of V (Subgroup.zpowers h)))
    (y0Of V (Subgroup.zpowers h)).subtype_injective).mp (Subgroup.eq_bot_of_card_eq _ hQ1)

theorem pPrimeCore_y0Of_le_center (hE : EpsIn M V h) :
    pPrimeCore 2 ↥(y0Of V (Subgroup.zpowers h)) ≤ Subgroup.center _ := by
  intro z hz
  rw [← hE.subgroupOf_y0Of, Subgroup.mem_subgroupOf] at hz
  have hY₀ : y0Of V (Subgroup.zpowers h) ≤ cenOf (inSubgroup (pPrimeCore 2) (yOf h)) := by
    unfold y0Of
    exact iSup₂_le fun y hy => Subgroup.le_centralizer_iff.mp ((hE.oddCore_yOf_le).2 y hy)
  rw [Subgroup.mem_center_iff]
  intro w
  exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hY₀ w.2) z hz).symm

theorem exists_surjective_y0Of (hE : EpsIn M V h) {K : Type*} [Group K] (Φ : K →* YBar h)
    (hrange : Φ.range = barY h (y0Of V (Subgroup.zpowers h))) :
    ∃ Ψ : K →* (↥(y0Of V (Subgroup.zpowers h)) ⧸ pPrimeCore 2 ↥(y0Of V (Subgroup.zpowers h))),
      Function.Surjective Ψ ∧ Ψ.ker = Φ.ker := by
  obtain ⟨e, -⟩ := exists_barQuotEquiv h hE.y0Of_le_yOf hE.subgroupOf_y0Of
  let Φ' : K →* ↥(barY h (y0Of V (Subgroup.zpowers h))) :=
    Φ.codRestrict _ fun k => hrange.le (MonoidHom.mem_range.mpr ⟨k, rfl⟩)
  refine ⟨e.symm.toMonoidHom.comp Φ', fun q => ?_, ?_⟩
  · have hq : ((e q : ↥(barY h _)) : YBar h) ∈ Φ.range := by
      rw [hrange]
      exact (e q).2
    obtain ⟨k, hk⟩ := MonoidHom.mem_range.mp hq
    refine ⟨k, ?_⟩
    have hk' : Φ' k = e q := Subtype.ext hk
    change e.symm (Φ' k) = q
    rw [hk', MulEquiv.symm_apply_apply]
  · rw [MonoidHom.ker_comp_of_injective Φ' e.symm.toMonoidHom e.symm.injective]
    exact MonoidHom.ker_codRestrict _ _ _

end EpsIn

end CFSG.RankThree.GF2n.Tim81
