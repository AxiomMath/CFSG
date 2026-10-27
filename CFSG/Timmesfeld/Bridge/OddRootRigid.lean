module

public import CFSG.Timmesfeld.Bridge.OddRootLocalQ
import CFSG.Timmesfeld.Bridge.OddRootNormalizer
import CFSG.Timmesfeld.Bridge.OddLocalRoot

public section

namespace CFSG.Timmesfeld.Bridge.OddRoot

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
  CFSG.Timmesfeld.Bridge.OddTransp CFSG.Timmesfeld.Bridge.OddLocal
  CFSG.CGT.Timmesfeld75 CFSG.BenderSuzuki
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {D : Set G}

private theorem rootGen_le_of_mem {d y c : G} (hcY : c ∈ rootGen D d y) :
    rootGen D d c ≤ rootGen D d y := by
  change Subgroup.closure (insert c (rootSet D d)) ≤ rootGen D d y
  rw [Subgroup.closure_le]
  intro w hw
  rcases Set.mem_insert_iff.mp hw with rfl | hw
  · exact hcY
  · exact mem_rootGen_of_mem hw

private theorem inf_rootGen_le_Qof {d y c : G} (hXcY : rootGen D d c ≤ rootGen D d y) :
    rootGen D d c ⊓ Qof D d y ≤ Qof D d c := by
  let X := rootGen D d c
  let N := Qof D d y
  have hNp : IsPGroup 2 N := isPGroup_Qof d y
  have hNnorm : ∀ g ∈ rootGen D d y, ∀ n ∈ N, g * n * g⁻¹ ∈ N :=
    fun g hg n hn => conj_mem_Qof d y hg hn
  have hHnorm : ((X ⊓ N).subgroupOf X).Normal := by
    refine ⟨fun k hk g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hk ⊢
    exact ⟨X.mul_mem (X.mul_mem g.2 hk.1) (X.inv_mem g.2),
      hNnorm (g : G) (hXcY g.2) (k : G) hk.2⟩
  have hHp : IsPGroup 2 ((X ⊓ N).subgroupOf X) := by
    have h1 : IsPGroup 2 ↥(X ⊓ N) := hNp.to_le inf_le_right
    exact h1.of_equiv (Subgroup.subgroupOfEquivOfLe inf_le_left).symm
  have hle : (X ⊓ N).subgroupOf X ≤ CFSG.pCore 2 X :=
    CFSG.BaerSuzuki.Helpers.le_pCore_of_normal_isPGroup hHnorm hHp
  intro q hq
  have hqX : q ∈ X := hq.1
  refine ⟨⟨q, hqX⟩, hle ?_, rfl⟩
  rw [Subgroup.mem_subgroupOf]
  exact hq

private theorem exists_sylow_eq_subgroupOf (h : Hyp G D) {d y z : G} {Y S : Subgroup G}
    (hC : GoodCompl D d y Y S) (hz : z ∈ Qof D d y) (hzd : Commute z d) :
    ∃ Sd : Sylow 2 ↥(conjSubgroup z Y),
      (Sd : Subgroup ↥(conjSubgroup z Y)) =
        (conjSubgroup z S).subgroupOf (conjSubgroup z Y) := by
  let Y₂ := conjSubgroup z Y
  let S₂ := conjSubgroup z S
  have hC₂ : IsRootCompl D d y Y₂ S₂ := IsRootCompl.conj h hC.toIsRootCompl hz hzd
  have hS₂p : IsPGroup 2 S₂ := IsRootCompl.isPGroup h hC₂
  have hS₂Yp : IsPGroup 2 ↥(S₂.subgroupOf Y₂) :=
    hS₂p.of_equiv (Subgroup.subgroupOfEquivOfLe hC₂.S_le).symm
  obtain ⟨Sd, hS₂d⟩ := hS₂Yp.exists_le_sylow
  have hmapSd : (Sd : Subgroup ↥Y₂).map Y₂.subtype = S₂ := by
    apply hC₂.S_sylow
    · rw [← Subgroup.map_subgroupOf_eq_of_le hC₂.S_le]
      exact Subgroup.map_mono hS₂d
    · exact Subgroup.map_subtype_le _
    · exact Sd.isPGroup'.map Y₂.subtype
  have hSd_eq : (Sd : Subgroup ↥Y₂) = S₂.subgroupOf Y₂ := by
    apply Subgroup.map_injective (f := Y₂.subtype) (Subgroup.subtype_injective Y₂)
    rw [hmapSd, Subgroup.map_subgroupOf_eq_of_le hC₂.S_le]
  exact ⟨Sd, hSd_eq⟩

private theorem sylow_map_conj_ne_of_not_mem {L : Type} [Group L] [Finite L] {n : ℕ}
    (e : L ≃* PSL2Model n) (hn : 2 ≤ n) {Sd : Sylow 2 L} {c : L}
    (hc1 : c ≠ 1) (hc2 : c * c = 1) (hcS : c ∉ (Sd : Subgroup L)) :
    Sd ≠ Sylow.mapSurjective (f := (MulAut.conj c).toMonoidHom)
      (MulAut.conj c).surjective Sd := by
  intro heq
  have hcoe : (Sylow.mapSurjective (f := (MulAut.conj c).toMonoidHom)
      (MulAut.conj c).surjective Sd : Subgroup L) =
      (Sd : Subgroup L).map (MulAut.conj c).toMonoidHom :=
    Sylow.coe_mapSurjective _ _
  have hmap : (Sd : Subgroup L).map (MulAut.conj c).toMonoidHom = (Sd : Subgroup L) := by
    rw [← hcoe]
    exact (congrArg (fun P : Sylow 2 L => (P : Subgroup L)) heq).symm
  have hcnorm : c ∈ Subgroup.normalizer ((Sd : Subgroup L) : Set L) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr hmap
  obtain ⟨Sc, hcSc⟩ := (isPGroup_two_zpowers_of_mul_self_eq_one hc2).exists_le_sylow
  have hSc_ne : Sc ≠ Sd := fun hsc => hcS (hsc ▸ hcSc (Subgroup.mem_zpowers c))
  have hmem : c ∈ Subgroup.normalizer ((Sd : Subgroup L) : Set L) ⊓ (Sc : Subgroup L) :=
    ⟨hcnorm, hcSc (Subgroup.mem_zpowers c)⟩
  rw [psl2_normalizer_inf_eq_bot e hn (fun h => hSc_ne h.symm)] at hmem
  exact hc1 (Subgroup.mem_bot.mp hmem)

private theorem conj_goodCompl_closure
    (h : Hyp G D) {d y c z : G} (hd : d ∈ D)
    (hpx : PSL2Pair D d y) {Y S : Subgroup G}
    (hC : GoodCompl D d y Y S) (hz : z ∈ Qof D d y) (hzd : Commute z d) (hc : c ∈ D)
    (hcY : c ∈ conjSubgroup z Y) (hdc : ¬ Commute d c) :
    conjSubgroup z Y ≤ Subgroup.closure ((conjSubgroup z S : Set G) ∪ {c}) := by
  let Y₂ := conjSubgroup z Y
  let S₂ := conjSubgroup z S
  obtain ⟨Sd, hSd_eq⟩ := exists_sylow_eq_subgroupOf h hC hz hzd
  have hC₂ : IsRootCompl D d y Y₂ S₂ := IsRootCompl.conj h hC.toIsRootCompl hz hzd
  obtain ⟨n, hn, ⟨eC⟩⟩ := exists_mulEquiv_PSL2Model_of_compl hpx hC₂.le hC₂.inf hC₂.sup
  have hnotc : (⟨c, hcY⟩ : ↥Y₂) ∉ (Sd : Subgroup ↥Y₂) := by
    intro hmem
    have hcS₂ : c ∈ S₂ := Subgroup.mem_subgroupOf.mp (hSd_eq ▸ hmem)
    have hc1 : c ≠ 1 := h.setup.oddT.ne_one hc
    have hcroot : c ∈ rootSet D d := hC₂.S_root c hcS₂ hc1
    exact hdc ((hcroot.2 d hd).mpr (Commute.refl d)).symm
  let cY : ↥Y₂ := ⟨c, hcY⟩
  have hcY2 : cY * cY = 1 := Subtype.ext (h.setup.oddT.mul_self_eq_one hc)
  have hcY1 : cY ≠ 1 := fun h1 => h.setup.oddT.ne_one hc (Subtype.ext_iff.mp h1)
  let Sd' : Sylow 2 ↥Y₂ := Sylow.mapSurjective (f := (MulAut.conj cY).toMonoidHom)
    (MulAut.conj cY).surjective Sd
  have hne : Sd ≠ Sd' := sylow_map_conj_ne_of_not_mem eC hn hcY1 hcY2 hnotc
  have hcoeSd' : (Sd' : Subgroup ↥Y₂) = (Sd : Subgroup ↥Y₂).map
      (MulAut.conj cY).toMonoidHom := Sylow.coe_mapSurjective _ _
  have hsup : (Sd : Subgroup ↥Y₂) ⊔ (Sd' : Subgroup ↥Y₂) = ⊤ :=
    psl2_sup_sylow_eq_top eC hn hne
  have hgen : (⊤ : Subgroup ↥Y₂) ≤ Subgroup.closure
      ((S₂.subgroupOf Y₂ : Set ↥Y₂) ∪ {cY}) := by
    rw [← hsup]
    apply sup_le
    · intro x hx
      exact Subgroup.subset_closure (Set.mem_union_left _ (hSd_eq ▸ hx))
    · intro x hx
      rw [hcoeSd'] at hx
      obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hx
      have hcYmem : cY ∈ Subgroup.closure ((S₂.subgroupOf Y₂ : Set ↥Y₂) ∪ {cY}) :=
        Subgroup.subset_closure (Set.mem_union_right _ (Set.mem_singleton cY))
      have hs2 : s ∈ Subgroup.closure ((S₂.subgroupOf Y₂ : Set ↥Y₂) ∪ {cY}) :=
        Subgroup.subset_closure (Set.mem_union_left _ (hSd_eq ▸ hs))
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hcYmem hs2)
        (Subgroup.inv_mem _ hcYmem)
  intro x hx
  have hsub : Subgroup.closure ((S₂.subgroupOf Y₂ : Set ↥Y₂) ∪ {cY}) ≤
      Subgroup.comap Y₂.subtype (Subgroup.closure ((S₂ : Set G) ∪ {c})) := by
    rw [Subgroup.closure_le]
    intro u hu
    rcases hu with hu | hu
    · have huS₂ : (u : G) ∈ S₂ := by
        rw [← Subgroup.map_subgroupOf_eq_of_le hC₂.S_le]
        exact Subgroup.mem_map_of_mem Y₂.subtype hu
      exact Subgroup.subset_closure (Set.mem_union_left _ huS₂)
    · rw [Set.mem_singleton_iff] at hu
      subst hu
      exact Subgroup.subset_closure (Set.mem_union_right _ rfl)
  exact Subgroup.mem_subgroupOf.mp (hsub (hgen (Subgroup.mem_top (⟨x, hx⟩ : ↥Y₂))))

private theorem conj_goodCompl_le_rootGen
    (h : Hyp G D) {d y c z : G} (hd : d ∈ D)
    (hpx : PSL2Pair D d y) {Y S : Subgroup G}
    (hC : GoodCompl D d y Y S) (hz : z ∈ Qof D d y) (hzd : Commute z d) (hc : c ∈ D)
    (hcY : c ∈ conjSubgroup z Y) (hdc : ¬ Commute d c) :
    conjSubgroup z Y ≤ rootGen D d c := by
  have hC₂ : IsRootCompl D d y (conjSubgroup z Y) (conjSubgroup z S) :=
    IsRootCompl.conj h hC.toIsRootCompl hz hzd
  refine (conj_goodCompl_closure h hd hpx hC hz hzd hc hcY hdc).trans ?_
  rw [rootGen, Subgroup.closure_le]
  intro u hu
  rcases hu with hu | hu
  · by_cases hu1 : u = 1
    · rw [hu1]
      exact Subgroup.one_mem _
    · exact Subgroup.subset_closure (Set.mem_insert_of_mem c (hC₂.S_root u hu hu1))
  · rw [Set.mem_singleton_iff] at hu
    subst hu
    exact Subgroup.subset_closure (Set.mem_insert _ _)

private theorem Wof_le_rootGen_of_inf
    (h : Hyp G D) {d y c : G} (hd : d ∈ D) (hy : y ∈ D)
    (hdy : ¬ Commute d y) (hpx : PSL2Pair D d y)
    (hinf : rootGen D d c ⊓ Qof D d y ≤ Qof D d c) :
    Wof D d y ≤ rootGen D d c := by
  rw [Wof_eq_closure h hd hy hdy hpx, Subgroup.closure_le]
  rintro g ⟨a, ha, b, hb, -, habN, rfl⟩
  exact Qof_le_rootGen d c
    (hinf ⟨(rootGen D d c).mul_mem (mem_rootGen_of_mem ha) (mem_rootGen_of_mem hb), habN⟩)

private theorem Qof_eq_closure_conj
    (h : Hyp G D) {d y z : G} (hd : d ∈ D) (hy : y ∈ D) (hdy : ¬ Commute d y)
    (hpx : PSL2Pair D d y) {Y S : Subgroup G} (hC : GoodCompl D d y Y S)
    (hz : z ∈ Qof D d y) (hzd : Commute z d) :
    Qof D d y = Subgroup.closure
      {g | ∃ c ∈ conjSubgroup z Y, ∃ w ∈ Wof D d y, g = c * w * c⁻¹} := by
  let N := Qof D d y
  let W := Wof D d y
  have hN1 : N = Subgroup.closure {g | ∃ c ∈ Y, ∃ w ∈ W, g = c * w * c⁻¹} :=
    Qof_eq_closure h hd hy hdy hpx hC
  have hE : (rootGroup D d).map (MulAut.conj z).toMonoidHom = rootGroup D d := by
    have hconj : z * d * z⁻¹ = d := by rw [hzd.eq]; group
    have := rootGroup_conj h.setup.isClass z d
    rw [hconj] at this
    exact this.symm
  have hNmap : N.map (MulAut.conj z).toMonoidHom = N := by
    ext q
    constructor
    · rintro ⟨n, hn, rfl⟩
      have hmem := N.mul_mem (N.mul_mem hz hn) (N.inv_mem hz)
      simpa [MulAut.conj_apply] using hmem
    · intro hq
      refine ⟨z⁻¹ * q * z, N.mul_mem (N.mul_mem (N.inv_mem hz) hq) hz, ?_⟩
      change z * (z⁻¹ * q * z) * z⁻¹ = q
      group
  have hWmap : W.map (MulAut.conj z).toMonoidHom = W := by
    dsimp only [W, Wof]
    rw [Subgroup.map_inf _ _ _ (MulAut.conj z).injective, hE, hNmap]
  have hset : Subgroup.map (MulAut.conj z).toMonoidHom
      (Subgroup.closure {g | ∃ c ∈ Y, ∃ w ∈ W, g = c * w * c⁻¹}) =
      Subgroup.closure {g | ∃ c ∈ conjSubgroup z Y, ∃ w ∈ W, g = c * w * c⁻¹} := by
    rw [MonoidHom.map_closure]
    congr 1
    ext g
    constructor
    · rintro ⟨h', ⟨c, hc, w, hw, rfl⟩, rfl⟩
      refine ⟨z * c * z⁻¹, Subgroup.mem_map_of_mem _ hc, z * w * z⁻¹, ?_, ?_⟩
      · rw [← hWmap]
        exact Subgroup.mem_map_of_mem _ hw
      · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
    · rintro ⟨c', hc', w, hw, rfl⟩
      obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.mp hc'
      have hw' : z⁻¹ * w * z ∈ W := by
        have hmem : w ∈ W.map (MulAut.conj z).toMonoidHom := by rw [hWmap]; exact hw
        obtain ⟨w₀, hw₀, hw₀eq⟩ := Subgroup.mem_map.mp hmem
        rw [← hw₀eq]
        change z⁻¹ * (z * w₀ * z⁻¹) * z ∈ W
        rwa [show z⁻¹ * (z * w₀ * z⁻¹) * z = w₀ from by group]
      refine ⟨c * (z⁻¹ * w * z) * c⁻¹, ⟨c, hc, z⁻¹ * w * z, hw', rfl⟩, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
  calc N = N.map (MulAut.conj z).toMonoidHom := hNmap.symm
    _ = Subgroup.map (MulAut.conj z).toMonoidHom
          (Subgroup.closure {g | ∃ c ∈ Y, ∃ w ∈ W, g = c * w * c⁻¹}) := by rw [hN1]
    _ = Subgroup.closure {g | ∃ c ∈ conjSubgroup z Y, ∃ w ∈ W, g = c * w * c⁻¹} := hset

theorem rootGen_eq_of_mem
    {G : Type} [Group G] [Finite G] {D : Set G}
    (h : Hyp G D) (hall : ∀ d ∈ D, ∀ x ∈ D, ¬ Commute d x → PSL2Pair D d x) {d y c : G}
    (hd : d ∈ D) (hy : y ∈ D) (hdy : ¬ Commute d y) (hc : c ∈ D)
    (hcY : c ∈ rootGen D d y) (hdc : ¬ Commute d c) :
    rootGen D d c = rootGen D d y ∧ Qof D d c = Qof D d y := by
  let N := Qof D d y
  have hpx : PSL2Pair D d y := hall d hd y hy hdy
  have hXcY : rootGen D d c ≤ rootGen D d y := rootGen_le_of_mem hcY
  obtain ⟨Y₁, S₁, hC₁⟩ := exists_goodCompl h hd hy hdy hpx
  obtain ⟨z, hzN, hzd, hcz⟩ := exists_conj_mem_of_compl h hd hy hdy hpx hC₁.le hC₁.inf
    hC₁.sup ⟨y, hC₁.x_mem, hy⟩ hc hcY hdc
  have hY₂X : conjSubgroup z Y₁ ≤ rootGen D d c :=
    conj_goodCompl_le_rootGen h hd hpx hC₁ hzN hzd hc hcz hdc
  have hC₂ : IsRootCompl D d y (conjSubgroup z Y₁) (conjSubgroup z S₁) :=
    IsRootCompl.conj h hC₁.toIsRootCompl hzN hzd
  have hWX : Wof D d y ≤ rootGen D d c :=
    Wof_le_rootGen_of_inf h hd hy hdy hpx (inf_rootGen_le_Qof hXcY)
  have hNX : N ≤ rootGen D d c := by
    have hclosure : N = Subgroup.closure {g | ∃ c' ∈ conjSubgroup z Y₁,
        ∃ w ∈ Wof D d y, g = c' * w * c'⁻¹} :=
      Qof_eq_closure_conj h hd hy hdy hpx hC₁ hzN hzd
    rw [hclosure, Subgroup.closure_le]
    rintro g ⟨c', hc', w, hw, rfl⟩
    exact (rootGen D d c).mul_mem ((rootGen D d c).mul_mem (hY₂X hc') (hWX hw))
      ((rootGen D d c).inv_mem (hY₂X hc'))
  have hXY : rootGen D d c = rootGen D d y := by
    apply le_antisymm hXcY
    rw [← hC₂.sup]
    exact sup_le hY₂X hNX
  refine ⟨hXY, ?_⟩
  simp only [Qof]
  rw [hXY]

private theorem commute_of_commute_of_mem_rootGroup
    (h : Hyp G D) {d x y z : G} (hd : d ∈ D)
    (hy : y ∈ D) (hdy : ¬ Commute d y) (hpx : PSL2Pair D d y)
    (hzEd : z ∈ rootGroup D d) (hzEx : z ∈ rootGroup D x) (hzN : z ∉ Qof D d y)
    (hyx : Commute y x) : Commute y d := by
  let Y := rootGen D d y
  have hzY : z ∈ Y := rootGroup_le_rootGen d y hzEd
  have hdY : d ∈ Y := mem_rootGen_of_mem (mem_rootSet_self hd)
  have hyY : y ∈ Y := mem_rootGen_left d y
  obtain ⟨n, hn, ⟨e⟩⟩ := hpx
  let L := ↥Y ⧸ CFSG.pCore 2 ↥Y
  let dz : L := QuotientGroup.mk' (CFSG.pCore 2 ↥Y) ⟨d, hdY⟩
  let yz : L := QuotientGroup.mk' (CFSG.pCore 2 ↥Y) ⟨y, hyY⟩
  let zz : L := QuotientGroup.mk' (CFSG.pCore 2 ↥Y) ⟨z, hzY⟩
  have hdz1 : dz ≠ 1 := fun h1 => not_mem_Qof_self h.setup.oddT hd hy hdy
    ((mk_eq_one_iff_mem_Qof hdY).mp h1)
  have hzz1 : zz ≠ 1 := fun h1 => hzN ((mk_eq_one_iff_mem_Qof hzY).mp h1)
  have hdz2 : dz * dz = 1 := by
    change QuotientGroup.mk' (CFSG.pCore 2 ↥Y) ⟨d, hdY⟩ *
      QuotientGroup.mk' (CFSG.pCore 2 ↥Y) ⟨d, hdY⟩ = 1
    rw [← map_mul,
      show (⟨d, hdY⟩ : ↥Y) * ⟨d, hdY⟩ = 1 from
        Subtype.ext (h.setup.oddT.mul_self_eq_one hd), map_one]
  have hzd : Commute z d :=
    commute_of_mem_rootGroup hd hzEd (rootSet_subset_rootGroup D d (mem_rootSet_self hd))
  have hcomm_zd : Commute zz dz := by
    have h1 : Commute (⟨z, hzY⟩ : ↥Y) ⟨d, hdY⟩ := Subtype.ext (by simpa using hzd.eq)
    change Commute (QuotientGroup.mk' (CFSG.pCore 2 ↥Y) ⟨z, hzY⟩)
      (QuotientGroup.mk' (CFSG.pCore 2 ↥Y) ⟨d, hdY⟩)
    exact h1.map _
  have hzy : Commute z y := commute_of_mem_rootGroup_of_commute hzEx hy hyx.symm
  have hcomm_yz_zz : Commute yz zz := by
    have h1 : Commute (⟨y, hyY⟩ : ↥Y) ⟨z, hzY⟩ := Subtype.ext (by simpa using hzy.symm.eq)
    change Commute (QuotientGroup.mk' (CFSG.pCore 2 ↥Y) ⟨y, hyY⟩)
      (QuotientGroup.mk' (CFSG.pCore 2 ↥Y) ⟨z, hzY⟩)
    exact h1.map _
  obtain ⟨Sd, hdzSd⟩ := (isPGroup_two_zpowers_of_mul_self_eq_one hdz2).exists_le_sylow
  have hzzSd : zz ∈ (Sd : Subgroup L) :=
    psl2_mem_sylow_of_commute e hn hdz1 (hdzSd (Subgroup.mem_zpowers dz)) hcomm_zd
  have hyzSd : yz ∈ (Sd : Subgroup L) :=
    psl2_mem_sylow_of_commute e hn hzz1 hzzSd hcomm_yz_zz
  have hcent : yz ∈ Subgroup.centralizer ({dz} : Set L) := by
    rw [psl2_centralizer_eq_sylow e hn (hdzSd (Subgroup.mem_zpowers dz)) hdz1]
    exact hyzSd
  have hcommq : Commute yz dz := Subgroup.mem_centralizer_singleton_iff.mp hcent
  have hcommY : Commute (⟨y, hyY⟩ : ↥Y) ⟨d, hdY⟩ := by
    have hC : IsOddTransp (((↑) : ↥Y → G) ⁻¹' D) := IsOddTransp.preimage h.setup.oddT Y
    exact (commute_iff_of_mem_pCore (C := ((↑) : ↥Y → G) ⁻¹' D) hC
      (CFSG.pCore_isPGroup (p := 2) (G := ↥Y)) (a := ⟨y, hyY⟩) hy
      (b := ⟨d, hdY⟩) hd).mp hcommq
  exact hcommY.map Y.subtype


private theorem mem_normalizer_of_commute_conj {L : Type} [Group L] [Finite L] {n : ℕ}
    (e : L ≃* PSL2Model n) (hn : 2 ≤ n) {S : Sylow 2 L} {t c : L}
    (ht1 : t ≠ 1) (htS : t ∈ (S : Subgroup L))
    (hcomm : Commute t (c * t * c⁻¹)) :
    c ∈ Subgroup.normalizer ((S : Subgroup L) : Set L) := by
  have hconj1 : c * t * c⁻¹ ≠ 1 := by
    intro h1
    apply ht1
    calc t = c⁻¹ * (c * t * c⁻¹) * c := by group
      _ = 1 := by rw [h1]; group
  have hmemS : c * t * c⁻¹ ∈ (S : Subgroup L) :=
    psl2_mem_sylow_of_commute e hn ht1 htS hcomm.symm
  let S' : Sylow 2 L := Sylow.mapSurjective (f := (MulAut.conj c).toMonoidHom)
    (MulAut.conj c).surjective S
  have hcoeS' : (S' : Subgroup L) = (S : Subgroup L).map
      (MulAut.conj c).toMonoidHom := Sylow.coe_mapSurjective _ _
  have hmemS' : c * t * c⁻¹ ∈ (S' : Subgroup L) := by
    rw [hcoeS']
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using
      Subgroup.mem_map_of_mem (MulAut.conj c).toMonoidHom htS
  have hS'_eq : S' = S := psl2_sylow_eq_of_mem e hn hconj1 hmemS' hmemS
  have hmap : (S : Subgroup L).map (MulAut.conj c).toMonoidHom = (S : Subgroup L) := by
    rw [← hcoeS', hS'_eq]
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr hmap

private theorem not_commute_conj_of_mem_rootGroup
    (h : Hyp G D) {d y z : G} (hd : d ∈ D) (hy : y ∈ D)
    (hdy : ¬ Commute d y) (hpx : PSL2Pair D d y) (hzEd : z ∈ rootGroup D d)
    (hzN : z ∉ Qof D d y) : ¬ Commute y (z * y * z⁻¹) := by
  let Y := rootGen D d y
  have hzY : z ∈ Y := rootGroup_le_rootGen d y hzEd
  have hdY : d ∈ Y := mem_rootGen_of_mem (mem_rootSet_self hd)
  have hyY : y ∈ Y := mem_rootGen_left d y
  obtain ⟨n, hn, ⟨e⟩⟩ := hpx
  let L := ↥Y ⧸ CFSG.pCore 2 ↥Y
  let dz : L := QuotientGroup.mk' (CFSG.pCore 2 ↥Y) ⟨d, hdY⟩
  let yz : L := QuotientGroup.mk' (CFSG.pCore 2 ↥Y) ⟨y, hyY⟩
  let zz : L := QuotientGroup.mk' (CFSG.pCore 2 ↥Y) ⟨z, hzY⟩
  have hdz1 : dz ≠ 1 := fun h1 => not_mem_Qof_self h.setup.oddT hd hy hdy
    ((mk_eq_one_iff_mem_Qof hdY).mp h1)
  have hzz1 : zz ≠ 1 := fun h1 => hzN ((mk_eq_one_iff_mem_Qof hzY).mp h1)
  have hyN : y ∉ Qof D d y := by
    intro hQ
    exact hdy ((commute_of_mem_D_of_mem_Qof h.setup.oddT (x := y) hy hy hQ d
      (mem_rootGen_of_mem (mem_rootSet_self hd)))).symm
  have hyz1 : yz ≠ 1 := fun h1 => hyN ((mk_eq_one_iff_mem_Qof hyY).mp h1)
  have hdz2 : dz * dz = 1 := by
    change QuotientGroup.mk' (CFSG.pCore 2 ↥Y) ⟨d, hdY⟩ *
      QuotientGroup.mk' (CFSG.pCore 2 ↥Y) ⟨d, hdY⟩ = 1
    rw [← map_mul,
      show (⟨d, hdY⟩ : ↥Y) * ⟨d, hdY⟩ = 1 from
        Subtype.ext (h.setup.oddT.mul_self_eq_one hd), map_one]
  have hyz2 : yz * yz = 1 := by
    change QuotientGroup.mk' (CFSG.pCore 2 ↥Y) ⟨y, hyY⟩ *
      QuotientGroup.mk' (CFSG.pCore 2 ↥Y) ⟨y, hyY⟩ = 1
    rw [← map_mul,
      show (⟨y, hyY⟩ : ↥Y) * ⟨y, hyY⟩ = 1 from
        Subtype.ext (h.setup.oddT.mul_self_eq_one hy), map_one]
  have hzd : Commute z d :=
    commute_of_mem_rootGroup hd hzEd (rootSet_subset_rootGroup D d (mem_rootSet_self hd))
  have hcomm_zd : Commute zz dz := by
    have h1 : Commute (⟨z, hzY⟩ : ↥Y) ⟨d, hdY⟩ := Subtype.ext (by simpa using hzd.eq)
    change Commute (QuotientGroup.mk' (CFSG.pCore 2 ↥Y) ⟨z, hzY⟩)
      (QuotientGroup.mk' (CFSG.pCore 2 ↥Y) ⟨d, hdY⟩)
    exact h1.map _
  obtain ⟨Sd, hdzSd⟩ := (isPGroup_two_zpowers_of_mul_self_eq_one hdz2).exists_le_sylow
  have hzzSd : zz ∈ (Sd : Subgroup L) :=
    psl2_mem_sylow_of_commute e hn hdz1 (hdzSd (Subgroup.mem_zpowers dz)) hcomm_zd
  obtain ⟨S, hyzS⟩ := (isPGroup_two_zpowers_of_mul_self_eq_one hyz2).exists_le_sylow
  have hyzS' : yz ∈ (S : Subgroup L) := hyzS (Subgroup.mem_zpowers yz)
  have hS_ne : S ≠ Sd := by
    intro heq
    have hcomm : Commute yz dz := by
      have hcent : yz ∈ Subgroup.centralizer ({dz} : Set L) := by
        rw [psl2_centralizer_eq_sylow e hn (hdzSd (Subgroup.mem_zpowers dz)) hdz1, ← heq]
        exact hyzS'
      exact Subgroup.mem_centralizer_singleton_iff.mp hcent
    have hC : IsOddTransp (((↑) : ↥Y → G) ⁻¹' D) := IsOddTransp.preimage h.setup.oddT Y
    have hcommY : Commute (⟨y, hyY⟩ : ↥Y) ⟨d, hdY⟩ :=
      (commute_iff_of_mem_pCore (C := ((↑) : ↥Y → G) ⁻¹' D) hC
        (CFSG.pCore_isPGroup (p := 2) (G := ↥Y)) (a := ⟨y, hyY⟩) hy
        (b := ⟨d, hdY⟩) hd).mp hcomm
    exact hdy (hcommY.map Y.subtype).symm
  intro hcomm
  have hcommL : Commute yz (zz * yz * zz⁻¹) := by
    have h1 : Commute (⟨y, hyY⟩ : ↥Y)
        ((⟨z, hzY⟩ : ↥Y) * ⟨y, hyY⟩ * (⟨z, hzY⟩ : ↥Y)⁻¹) :=
      Subtype.ext (by simpa using hcomm.eq)
    change Commute (QuotientGroup.mk' (CFSG.pCore 2 ↥Y) ⟨y, hyY⟩)
      (QuotientGroup.mk' (CFSG.pCore 2 ↥Y) ⟨z, hzY⟩ *
       QuotientGroup.mk' (CFSG.pCore 2 ↥Y) ⟨y, hyY⟩ *
       (QuotientGroup.mk' (CFSG.pCore 2 ↥Y) ⟨z, hzY⟩)⁻¹)
    simpa only [map_mul, map_inv] using h1.map (QuotientGroup.mk' (CFSG.pCore 2 ↥Y))
  have hznorm : zz ∈ Subgroup.normalizer ((S : Subgroup L) : Set L) :=
    mem_normalizer_of_commute_conj e hn hyz1 hyzS' hcommL
  have hmem_bot : zz ∈ Subgroup.normalizer ((S : Subgroup L) : Set L) ⊓ (Sd : Subgroup L) :=
    ⟨hznorm, hzzSd⟩
  rw [psl2_normalizer_inf_eq_bot e hn hS_ne] at hmem_bot
  exact hzz1 (Subgroup.mem_bot.mp hmem_bot)

theorem rootGroup_inf_le_Qof_of_not_commute
    {G : Type} [Group G] [Finite G] {D : Set G}
    (h : Hyp G D) (hall : ∀ d ∈ D, ∀ x ∈ D, ¬ Commute d x → PSL2Pair D d x)
    {d x y : G} (hd : d ∈ D) (hx : x ∈ D) (hy : y ∈ D) (hdx : ¬ Commute d x)
    (hdy : ¬ Commute d y) : rootGroup D d ⊓ rootGroup D x ≤ Qof D d y := by
  rintro z hz
  by_contra hzN
  have hzEd : z ∈ rootGroup D d := hz.1
  have hzEx : z ∈ rootGroup D x := hz.2
  have hpx : PSL2Pair D d y := hall d hd y hy hdy
  have hxy : ¬ Commute y x := fun hyx =>
    hdy (commute_of_commute_of_mem_rootGroup h (d := d) (x := x) (y := y) (z := z)
      hd hy hdy hpx hzEd hzEx hzN hyx).symm
  have hy'D : z * y * z⁻¹ ∈ D := h.setup.conj_mem z hy
  have hzY : z ∈ rootGen D d y := rootGroup_le_rootGen d y hzEd
  have hyY : y ∈ rootGen D d y := mem_rootGen_left d y
  have hy'Y : z * y * z⁻¹ ∈ rootGen D d y :=
    (rootGen D d y).mul_mem ((rootGen D d y).mul_mem hzY hyY) ((rootGen D d y).inv_mem hzY)
  have hnoty' : ¬ Commute y (z * y * z⁻¹) :=
    not_commute_conj_of_mem_rootGroup h hd hy hdy hpx hzEd hzN
  have hYdy : rootGen D y d = rootGen D d y :=
    rootGen_comm h hy hd (fun hc => hdy hc.symm) (hall y hy d hd (fun hc => hdy hc.symm))
      (hall d hd y hy hdy)
  have hy'Xyd : z * y * z⁻¹ ∈ rootGen D y d := by rw [hYdy]; exact hy'Y
  have hT1 := rootGen_eq_of_mem h hall hy hd (fun hc => hdy hc.symm) hy'D hy'Xyd hnoty'
  have hY_eq : rootGen D d y = rootGen D y (z * y * z⁻¹) := by
    rw [← hYdy, ← hT1.1]
  have hpx_yx : PSL2Pair D y x := hall y hy x hx hxy
  have hExXyx : rootGroup D x ≤ rootGen D y x := by
    rw [rootGroup, Subgroup.closure_le]
    exact rootSet_subset_rootGen h hy hx hxy hpx_yx
  have hzXyx : z ∈ rootGen D y x := hExXyx hzEx
  have hyXyx : y ∈ rootGen D y x := mem_rootGen_of_mem (mem_rootSet_self hy)
  have hy'Xyx : z * y * z⁻¹ ∈ rootGen D y x :=
    (rootGen D y x).mul_mem ((rootGen D y x).mul_mem hzXyx hyXyx)
      ((rootGen D y x).inv_mem hzXyx)
  have hsub : rootGen D y (z * y * z⁻¹) ≤ rootGen D y x := rootGen_le_of_mem hy'Xyx
  have hdXyx : d ∈ rootGen D y x := (hY_eq ▸ hsub) (mem_rootGen_of_mem (mem_rootSet_self hd))
  have hT2 := rootGen_eq_of_mem h hall hy hx hxy hd hdXyx (fun hc => hdy hc.symm)
  have hxY : x ∈ rootGen D d y := by
    rw [← hYdy, hT2.1]
    exact mem_rootGen_left y x
  have hpx_x : PSL2Pair D d x := hall d hd x hx hdx
  have hzQdx : z ∈ Qof D d x :=
    rootGroup_inf_le_Qof h hd hx hdx hpx_x ⟨hzEd, hzEx⟩
  have hT3 := rootGen_eq_of_mem h hall hd hy hdy hx hxY hdx
  exact hzN (hT3.2 ▸ hzQdx)

end CFSG.Timmesfeld.Bridge.OddRoot
