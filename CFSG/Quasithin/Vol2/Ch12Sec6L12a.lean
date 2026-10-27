module

public import CFSG.Quasithin.Vol2.Ch12Sec6L13c

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.G6 S126 S126L1a S126P S126E S126F
  S126L1b S126N S126T2 CFSG.LieType.BorelTits
open scoped IsMulCommutative Pointwise commutatorElement

namespace S126T2

@[expose] def c01 : Finset (Fin 8 → ZMod 2) :=
  Finset.univ.filter fun x => x 0 = 0 ∧ x 1 = 0 ∧ ∑ i, x i = 0

theorem card_c01 : c01.card = 32 := by
  decide +kernel

theorem fixed_c01 : ∀ x ∈ c01, (fun i => x ((cy 2 3 4)⁻¹ i)) = x →
    (fun i => x ((cy 4 5 6)⁻¹ i)) = x → (fun i => x ((cy 5 6 7)⁻¹ i)) = x →
    x = 0 ∨ x = vSix := by
  decide +kernel

theorem coord01_of_fixed : ∀ x : Fin 8 → ZMod 2, ∑ i, x i = 0 →
    ((fun i => x ((cy 2 3 4)⁻¹ i)) = x ∨ (fun i => x ((cy 2 3 4)⁻¹ i)) = x + fun _ => 1) →
    ((fun i => x ((cy 4 5 6)⁻¹ i)) = x ∨ (fun i => x ((cy 4 5 6)⁻¹ i)) = x + fun _ => 1) →
    ((fun i => x ((cy 5 6 7)⁻¹ i)) = x ∨ (fun i => x ((cy 5 6 7)⁻¹ i)) = x + fun _ => 1) →
    x 0 = x 1 := by
  decide +kernel

theorem cy234_mem : cy 2 3 4 ∈ A6s :=
  cy_mem (by decide) (by decide) (by decide) (by decide) (by decide)

theorem cy456_mem : cy 4 5 6 ∈ A6s :=
  cy_mem (by decide) (by decide) (by decide) (by decide) (by decide)

theorem cy567_mem : cy 5 6 7 ∈ A6s :=
  cy_mem (by decide) (by decide) (by decide) (by decide) (by decide)

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} [IsMulCommutative ↥V]

theorem coordV_mem_c01 (h1222 : Stmt12_2_2) {F : Frame126 T L V} (hH : Hyp126 G T L V) {v : G}
    (hv : v ∈ V) (hβ : F.β ⟨v, hv⟩ = QuotientGroup.mk (pe 0 1)) {y : G} (hy : y ∈ Vv L V v) :
    coordV F y ∈ c01 := by
  obtain ⟨c, hc, hcy, -⟩ := coordV_spec h1222 hH hv hβ (Vv_le_V hH v hy) hy
  obtain ⟨h0, h1⟩ := mem_core01.1 hc
  rw [← hcy]
  exact Finset.mem_filter.2 ⟨Finset.mem_univ _, h0, h1, mem_coreMod.1 c.2⟩

theorem exists_coordV_eq (h1222 : Stmt12_2_2) {F : Frame126 T L V} (hH : Hyp126 G T L V) {v : G}
    (hv : v ∈ V) (hβ : F.β ⟨v, hv⟩ = QuotientGroup.mk (pe 0 1)) {x : Fin 8 → ZMod 2}
    (hx : x ∈ c01) : ∃ y ∈ Vv L V v, coordV F y = x := by
  obtain ⟨-, h0, h1, hs⟩ := Finset.mem_filter.1 hx
  have hD : ∀ d ∈ duads, ∃ u ∈ Vv L V v, coordV F u = d := fun d hd => by
    obtain ⟨u, hu, hc⟩ := exists_mem_Delta_coordV h1222 hH hv hβ hd
    exact ⟨u, ((mem_Delta_iff h1222 hH hv hβ).1 hu).1, hc⟩
  rcases classify_core x h0 h1 hs with rfl | hd | hq | rfl
  · exact ⟨1, (Vv L V v).one_mem, coordV_one h1222 hH hv hβ⟩
  · exact hD x hd
  · obtain ⟨d₁, hd₁, d₂, hd₂, rfl⟩ := quad_eq_add x hq
    obtain ⟨u₁, hv₁, hc₁⟩ := hD d₁ hd₁
    obtain ⟨u₂, hv₂, hc₂⟩ := hD d₂ hd₂
    exact ⟨u₁ * u₂, (Vv L V v).mul_mem hv₁ hv₂, by rw [coordV_mul h1222 hH hv hβ hv₁ hv₂, hc₁, hc₂]⟩
  · obtain ⟨u₁, hv₁, hc₁⟩ := hD _ (pv_mem_duads (i := 2) (j := 3) (by decide) (by decide)
      (by decide))
    obtain ⟨u₂, hv₂, hc₂⟩ := hD _ (pv_mem_duads (i := 4) (j := 5) (by decide) (by decide)
      (by decide))
    obtain ⟨u₃, hv₃, hc₃⟩ := hD _ (pv_mem_duads (i := 6) (j := 7) (by decide) (by decide)
      (by decide))
    have h12 := (Vv L V v).mul_mem hv₁ hv₂
    refine ⟨u₁ * u₂ * u₃, (Vv L V v).mul_mem h12 hv₃, ?_⟩
    rw [coordV_mul h1222 hH hv hβ h12 hv₃, coordV_mul h1222 hH hv hβ hv₁ hv₂, hc₁, hc₂, hc₃]
    rfl

theorem card_Vv (h1222 : Stmt12_2_2) {F : Frame126 T L V} (hH : Hyp126 G T L V) {v : G}
    (hv : v ∈ V) (hβ : F.β ⟨v, hv⟩ = QuotientGroup.mk (pe 0 1)) : Nat.card ↥(Vv L V v) = 32 := by
  have hinj : Set.InjOn (coordV F) (Vv L V v : Set G) := fun y hy y' hy' h =>
    coordV_injOn h1222 hH hv hβ hy hy' h
  have himg : coordV F '' (Vv L V v : Set G) = ↑c01 := by
    ext x
    refine ⟨?_, fun hx => ?_⟩
    · rintro ⟨y, hy, rfl⟩
      exact coordV_mem_c01 h1222 hH hv hβ hy
    · obtain ⟨y, hy, hyx⟩ := exists_coordV_eq h1222 hH hv hβ hx
      exact ⟨y, hy, hyx⟩
  rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq, ← hinj.ncard_image, himg,
    Set.ncard_coe_finset, card_c01]

theorem coordV_of_mem_centralizer (h1222 : Stmt12_2_2) {F : Frame126 T L V}
    (hH : Hyp126 G T L V) {v : G} (hv : v ∈ V) (hβ : F.β ⟨v, hv⟩ = QuotientGroup.mk (pe 0 1))
    {y : G} (hy : y ∈ Vv L V v) (hyc : y ∈ Subgroup.centralizer (Lv L v : Set G)) :
    coordV F y = 0 ∨ coordV F y = vSix := by
  have hfix : ∀ σ ∈ A6s, (fun i => coordV F y (σ⁻¹ i)) = coordV F y := by
    intro σ hσ
    obtain ⟨l, hl, hlσ⟩ := exists_Lv_of_A6s h1222 F hH hv hβ σ hσ
    have h := coordV_conj h1222 hH hv hβ hl hy
    have hly : (l : G) * y * (l : G)⁻¹ = y := by
      rw [Subgroup.mem_centralizer_iff.1 hyc l hl, mul_inv_cancel_right]
    rw [hly, hlσ] at h
    exact h.symm
  exact fixed_c01 _ (coordV_mem_c01 h1222 hH hv hβ hy) (hfix _ cy234_mem) (hfix _ cy456_mem)
    (hfix _ cy567_mem)

theorem mem_centralizer_of_coordV (h1222 : Stmt12_2_2) {F : Frame126 T L V}
    (hH : Hyp126 G T L V) {v : G} (hv : v ∈ V) (hβ : F.β ⟨v, hv⟩ = QuotientGroup.mk (pe 0 1))
    {y : G} (hy : y ∈ Vv L V v) (h : coordV F y = 0 ∨ coordV F y = vSix) :
    y ∈ Subgroup.centralizer (Lv L v : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  have hlL : l ∈ L := Lv_le_L L v hl
  have hly : l * y * l⁻¹ ∈ Vv L V v :=
    (Subgroup.mem_normalizer_iff.1 (Lv_le_normalizer_Vv hH v hl) y).1 hy
  have hσ : psiP F hH ⟨l, hlL⟩ ∈ A6s := psiP_mem_A6s h1222 F hH hv hβ
    (show (⟨l, hlL⟩ : ↥L) ∈ (Lv L v).subgroupOf L from hl)
  have he : l * y * l⁻¹ = y := by
    refine coordV_injOn h1222 hH hv hβ hly hy ?_
    rw [show l = ((⟨l, hlL⟩ : ↥L) : G) from rfl,
      coordV_conj h1222 hH hv hβ (l := ⟨l, hlL⟩) hl hy]
    rcases h with h | h
    · rw [h]
      rfl
    · rw [h]
      exact vSix_comp_inv hσ
  calc l * y = l * y * l⁻¹ * l := by group
    _ = y * l := by rw [he]

theorem card_Vv_inf (h1222 : Stmt12_2_2) {F : Frame126 T L V} (hH : Hyp126 G T L V) {v : G}
    (hv : v ∈ V) (hβ : F.β ⟨v, hv⟩ = QuotientGroup.mk (pe 0 1)) :
    Nat.card ↥(Vv L V v ⊓ Subgroup.centralizer (Lv L v : Set G)) = 2 := by
  have hinj : Set.InjOn (coordV F)
      ((Vv L V v ⊓ Subgroup.centralizer (Lv L v : Set G) : Subgroup G) : Set G) :=
    fun y hy y' hy' h => coordV_injOn h1222 hH hv hβ hy.1 hy'.1 h
  have himg : coordV F ''
      ((Vv L V v ⊓ Subgroup.centralizer (Lv L v : Set G) : Subgroup G) : Set G) =
        ({0, vSix} : Set (Fin 8 → ZMod 2)) := by
    ext x
    refine ⟨?_, fun hx => ?_⟩
    · rintro ⟨y, ⟨hy, hyc⟩, rfl⟩
      exact coordV_of_mem_centralizer h1222 hH hv hβ hy hyc
    · have hx' : x ∈ c01 := by
        rcases hx with rfl | rfl <;> decide
      obtain ⟨y, hy, hyx⟩ := exists_coordV_eq h1222 hH hv hβ hx'
      exact ⟨y, ⟨hy, mem_centralizer_of_coordV h1222 hH hv hβ hy (hyx ▸ hx)⟩, hyx⟩
  rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq, ← hinj.ncard_image, himg,
    Set.ncard_pair (by decide)]

theorem coord01_of_mem_centralizer (h1222 : Stmt12_2_2) (F : Frame126 T L V)
    (hH : Hyp126 G T L V) {v : G} (hv : v ∈ V) (hβ : F.β ⟨v, hv⟩ = QuotientGroup.mk (pe 0 1))
    {y : G} (hyV : y ∈ V) (hyc : y ∈ Subgroup.centralizer (Lv L v : Set G)) {c : ↥(coreMod 8)}
    (hc : F.β ⟨y, hyV⟩ = QuotientGroup.mk c) :
    Multiplicative.toAdd (c : PermMod 8) 0 = Multiplicative.toAdd (c : PermMod 8) 1 := by
  have hfix : ∀ σ ∈ A6s, (fun i => Multiplicative.toAdd (c : PermMod 8) (σ⁻¹ i)) =
      Multiplicative.toAdd (c : PermMod 8) ∨
      (fun i => Multiplicative.toAdd (c : PermMod 8) (σ⁻¹ i)) =
        Multiplicative.toAdd (c : PermMod 8) + fun _ => 1 := by
    intro σ hσ
    obtain ⟨l, hl, hlσ⟩ := exists_Lv_of_A6s h1222 F hH hv hβ σ hσ
    have hly : (l : G) * y * (l : G)⁻¹ = y := by
      rw [Subgroup.mem_centralizer_iff.1 hyc l hl, mul_inv_cancel_right]
    have h := actsAs_psiP F hH l ⟨y, hyV⟩ ⟨y, hyV⟩ hly.symm
    rw [hlσ, hc, dAct_mk] at h
    have h1 : (QuotientGroup.mk (coreAct 8 σ c * c⁻¹) : D8) = 1 := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, ← h, mul_inv_cancel]
    rcases (S126FE.mk_eq_one_iff _).1 h1 with h2 | h2
    · left
      have h3 : coreAct 8 σ c = c := by rw [← mul_inv_eq_one, h2]
      funext i
      have := congrFun (congrArg (fun m : ↥(coreMod 8) => Multiplicative.toAdd (m : PermMod 8))
        h3) i
      simpa [coreAct_coe, permAct_apply] using this
    · right
      have h3 : coreAct 8 σ c = S126FE.eOm * c := by rw [← h2, inv_mul_cancel_right]
      funext i
      have := congrFun (congrArg (fun m : ↥(coreMod 8) => Multiplicative.toAdd (m : PermMod 8))
        h3) i
      simp only [coreAct_coe, permAct_apply, Subgroup.coe_mul, toAdd_mul, Pi.add_apply] at this
      rw [this, add_comm]
      rfl
  exact coord01_of_fixed _ (mem_coreMod.1 c.2) (hfix _ cy234_mem) (hfix _ cy456_mem)
    (hfix _ cy567_mem)

omit [IsMulCommutative ↥V] in
theorem comm_Vv_Lv (h1222 : Stmt12_2_2) (hH : Hyp126 G T L V) {v : G} (hv : v ∈ V) :
    ⁅Vv L V v, Lv L v⁆ = Vv L V v := by
  refine le_antisymm ?_ (Vv_le_comm h1222 hH hv)
  rw [Subgroup.commutator_le]
  intro u hu l hl
  have e : ⁅u, l⁆ = u * (l * u⁻¹ * l⁻¹) := by rw [commutatorElement_def]; group
  rw [e]
  exact (Vv L V v).mul_mem hu
    ((Subgroup.mem_normalizer_iff.1 (Lv_le_normalizer_Vv hH v hl) u⁻¹).1 ((Vv L V v).inv_mem hu))

noncomputable def a6sEquiv : ↥A6s ≃* ↥(alternatingGroup (Fin 6)) := by
  classical
  have hinj : Function.Injective (Equiv.Perm.ofSubtype : Equiv.Perm ↥six →* Equiv.Perm (Fin 8)) :=
    Equiv.Perm.ofSubtype_injective
  have hcard : Fintype.card ↥six = Fintype.card (Fin 6) := by
    rw [← Nat.card_eq_fintype_card, card_six, Fintype.card_fin]
  exact (Subgroup.equivMapOfInjective _ _ hinj).symm.trans
    (Equiv.altCongrHom (Fintype.equivOfCardEq hcard))

noncomputable def psiLv (h1222 : Stmt12_2_2) (F : Frame126 T L V) (hH : Hyp126 G T L V) {v : G}
    (hv : v ∈ V) (hβ : F.β ⟨v, hv⟩ = QuotientGroup.mk (pe 0 1)) :
    ↥(Lv L v) →* ↥(alternatingGroup (Fin 6)) :=
  a6sEquiv.toMonoidHom.comp (((psiP F hH).comp (Subgroup.inclusion (Lv_le_L L v))).codRestrict
    A6s fun l => psiP_mem_A6s h1222 F hH hv hβ
      (show Subgroup.inclusion (Lv_le_L L v) l ∈ (Lv L v).subgroupOf L from l.2))

theorem o2Iso_Lv (h1222 : Stmt12_2_2) (F : Frame126 T L V) (hH : Hyp126 G T L V) {v : G}
    (hv : v ∈ V) (hβ : F.β ⟨v, hv⟩ = QuotientGroup.mk (pe 0 1)) :
    Function.Surjective (psiLv h1222 F hH hv hβ) ∧
      (psiLv h1222 F hH hv hβ).ker = CFSG.Open.pCore 2 ↥(Lv L v) := by
  refine ⟨fun a => ?_, ?_⟩
  · obtain ⟨l, hl, hla⟩ := exists_Lv_of_A6s h1222 F hH hv hβ (a6sEquiv.symm a) (a6sEquiv.symm a).2
    refine ⟨⟨l, hl⟩, ?_⟩
    have h1 : ((psiP F hH).comp (Subgroup.inclusion (Lv_le_L L v))).codRestrict A6s
        (fun l => psiP_mem_A6s h1222 F hH hv hβ
          (show Subgroup.inclusion (Lv_le_L L v) l ∈ (Lv L v).subgroupOf L from l.2)) ⟨l, hl⟩ =
        a6sEquiv.symm a := Subtype.ext hla
    show a6sEquiv _ = a
    rw [h1, MulEquiv.apply_symm_apply]
  · ext x
    rw [MonoidHom.mem_ker]
    have hx : (x : G) ∈ pCoreOf 2 (Lv L v) ↔ x ∈ CFSG.Open.pCore 2 ↥(Lv L v) := by
      constructor
      · rintro ⟨y, hy, hyx⟩
        rwa [show y = x from Subtype.ext hyx] at hy
      · intro hx
        exact ⟨x, hx, rfl⟩
    rw [← hx]
    constructor
    · intro h
      have h1 : psiP F hH (Subgroup.inclusion (Lv_le_L L v) x) = 1 := by
        have := congrArg (fun z => (a6sEquiv.symm z : Equiv.Perm (Fin 8))) h
        simpa [psiLv] using this
      have h2 : S126L19a.psi F hH (Subgroup.inclusion (Lv_le_L L v) x) = 1 := Subtype.ext h1
      exact Lv_inf_le h1222 hH v ⟨x.2, (S126L19a.psi_eq_one_iff F hH _).1 h2⟩
    · intro h
      have h1 := psi_pCore_eq_one h1222 F hH hv hβ (y := Subgroup.inclusion (Lv_le_L L v) x) h
      simp only [psiLv, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
      have h2 : ((psiP F hH).comp (Subgroup.inclusion (Lv_le_L L v))).codRestrict A6s
          (fun l => psiP_mem_A6s h1222 F hH hv hβ
            (show Subgroup.inclusion (Lv_le_L L v) l ∈ (Lv L v).subgroupOf L from l.2)) x = 1 :=
        Subtype.ext h1
      rw [h2, map_one]

theorem card_Lv (h1222 : Stmt12_2_2) (F : Frame126 T L V) (hH : Hyp126 G T L V) {v : G}
    (hv : v ∈ V) (hβ : F.β ⟨v, hv⟩ = QuotientGroup.mk (pe 0 1)) :
    Nat.card ↥(Lv L v) = 360 * Nat.card ↥(pCoreOf 2 (Lv L v)) := by
  obtain ⟨hs, hk⟩ := o2Iso_Lv h1222 F hH hv hβ
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (psiLv h1222 F hH hv hβ).ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _ hs).toEquiv, hk] at h1
  have h360 : Nat.card ↥(alternatingGroup (Fin 6)) = 360 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
    decide
  rw [h1, h360]
  congr 1
  exact (Subgroup.card_map_of_injective (Lv L v).subtype_injective).symm

end S126T2

end CFSG.Quasithin.H13
