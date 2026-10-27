module

public import CFSG.Milestones.ASVolI.B610.BlkA
public import CFSG.Quasithin.Background.B610TwoOff

public section

namespace CFSG.Quasithin.B610T.TwoBlk

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

section NatOf

variable {G : Type} [Group G] [Finite G] {V H : Subgroup G} (hV : IsElemAbelian 2 V)
  (hHN : H ≤ Subgroup.normalizer (V : Set G)) {B : Subgroup (MulAut (IntMod V hV))}
  (hBH : B ≤ autI hV H)

omit [Finite G] in
include hHN in
theorem burnsideB610_preI_le_normalizer :
    preI hV H hHN B ≤ Subgroup.normalizer (V : Set G) :=
  (preI_le hV).trans hHN

omit [Finite G] in
include hBH in
theorem burnsideB610_convI_mem (y : ↥(preI hV H hHN B)) :
    convI hV ⟨y, burnsideB610_preI_le_normalizer hV hHN y.2⟩ ∈ B := by
  have h := convI_mem_autI hV y.2 (burnsideB610_preI_le_normalizer hV hHN y.2)
  rw [autI_preI hV hBH] at h
  exact h

@[expose] noncomputable def burnsideB610_preProj : ↥(preI hV H hHN B) →* ↥B :=
  ((convI hV).comp (Subgroup.inclusion (burnsideB610_preI_le_normalizer hV hHN))).codRestrict B
    (fun y => burnsideB610_convI_mem hV hHN hBH y)

omit [Finite G] in
theorem burnsideB610_preProj_apply (y : ↥(preI hV H hHN B)) :
    ((burnsideB610_preProj hV hHN hBH y : ↥B) : MulAut (IntMod V hV)) =
      convI hV ⟨y, burnsideB610_preI_le_normalizer hV hHN y.2⟩ := rfl

omit [Finite G] in
theorem burnsideB610_preProj_surjective :
    Function.Surjective (burnsideB610_preProj hV hHN hBH) := by
  rintro ⟨b, hb⟩
  rw [← autI_preI hV hBH (hA := hHN)] at hb
  obtain ⟨g, hg, rfl⟩ := (mem_autI hV).1 hb
  exact ⟨⟨g, hg⟩, Subtype.ext rfl⟩

omit [Finite G] in
theorem burnsideB610_preProj_eq_one_iff (y : ↥(preI hV H hHN B)) :
    burnsideB610_preProj hV hHN hBH y = 1 ↔ (y : G) ∈ Subgroup.centralizer (V : Set G) := by
  rw [← (convI_eq_one_iff hV ⟨y, burnsideB610_preI_le_normalizer hV hHN y.2⟩),
    ← burnsideB610_preProj_apply hV hHN hBH y]
  exact ⟨fun h => by rw [h]; rfl, fun h => Subtype.ext h⟩

omit [Finite G] in
include hBH in
theorem burnsideB610_mk_mem (w : ↥⁅V, preI hV H hHN B⁆) :
    IntMod.mk hV ⟨w, Subgroup.le_normalizer_iff_commutator_le_left.mp
      (burnsideB610_preI_le_normalizer hV hHN) w.2⟩ ∈ commV B := by
  have h := burnsideB610_mk_mem_commV hV (burnsideB610_preI_le_normalizer hV hHN) w.2
    (Subgroup.le_normalizer_iff_commutator_le_left.mp (burnsideB610_preI_le_normalizer hV hHN) w.2)
  rwa [autI_preI hV hBH] at h

@[expose] noncomputable def burnsideB610_commIncl :
    ↥⁅V, preI hV H hHN B⁆ →* ↥(commV B) where
  toFun w := ⟨IntMod.mk hV ⟨w, Subgroup.le_normalizer_iff_commutator_le_left.mp
      (burnsideB610_preI_le_normalizer hV hHN) w.2⟩, burnsideB610_mk_mem hV hHN hBH w⟩
  map_one' := Subtype.ext (IntMod.val_injective rfl)
  map_mul' _ _ := Subtype.ext (IntMod.val_injective rfl)

omit [Finite G] in
theorem burnsideB610_commIncl_val (w : ↥⁅V, preI hV H hHN B⁆) :
    ((burnsideB610_commIncl hV hHN hBH w : ↥(commV B)) : IntMod V hV).val = w := rfl

omit [Finite G] in
theorem burnsideB610_commIncl_injective :
    Function.Injective (burnsideB610_commIncl hV hHN hBH) := by
  intro a b hab
  have h := congrArg (fun m : ↥(commV B) => (m : IntMod V hV).val) hab
  exact Subtype.ext h

omit [Finite G] in
theorem burnsideB610_commIncl_surjective :
    Function.Surjective (burnsideB610_commIncl hV hHN hBH) := by
  rintro ⟨m, hm⟩
  have hm' : m ∈ commV (autI hV (preI hV H hHN B)) := by rw [autI_preI hV hBH]; exact hm
  refine ⟨⟨m.val, burnsideB610_val_mem_commutator hV
    (burnsideB610_preI_le_normalizer hV hHN) hm'⟩, Subtype.ext (IntMod.val_injective rfl)⟩

@[expose] noncomputable def burnsideB610_natAlpha
    (e : ↥B ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) :
    ↥(preI hV H hHN B) →* ↥(StatedSL 2 (ZMod 2)) :=
  (specialLinearGroupEquivStatedSL 2 (ZMod 2)).toMonoidHom.comp
    (e.toMonoidHom.comp (burnsideB610_preProj hV hHN hBH))

omit [Finite G] in
theorem burnsideB610_natAlpha_surjective (e : ↥B ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) :
    Function.Surjective (burnsideB610_natAlpha hV hHN hBH e) := by
  intro γ
  obtain ⟨s, rfl⟩ := (specialLinearGroupEquivStatedSL 2 (ZMod 2)).surjective γ
  obtain ⟨b, rfl⟩ := e.surjective s
  obtain ⟨y, rfl⟩ := burnsideB610_preProj_surjective hV hHN hBH b
  exact ⟨y, rfl⟩

omit [Finite G] in
theorem burnsideB610_natAlpha_ker (e : ↥B ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) :
    (burnsideB610_natAlpha hV hHN hBH e).ker =
      (preI hV H hHN B ⊓ Subgroup.centralizer (V : Set G)).subgroupOf (preI hV H hHN B) := by
  ext y
  have h1 : burnsideB610_natAlpha hV hHN hBH e y = 1 ↔
      (y : G) ∈ Subgroup.centralizer (V : Set G) := by
    rw [← burnsideB610_preProj_eq_one_iff hV hHN hBH y]
    constructor
    · intro h
      apply e.injective
      apply (specialLinearGroupEquivStatedSL 2 (ZMod 2)).injective
      rw [map_one, map_one]
      exact h
    · intro h
      show (specialLinearGroupEquivStatedSL 2 (ZMod 2)) (e (burnsideB610_preProj hV hHN hBH y)) = 1
      rw [h, map_one, map_one]
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf, h1]
  exact ⟨fun h => ⟨y.2, h⟩, fun h => h.2⟩

include hBH in
theorem burnsideB610_preI_inf_centralizer (hcf : commV B ⊓ fixV B = ⊥) :
    ⁅V, preI hV H hHN B⁆ ⊓ Subgroup.centralizer (preI hV H hHN B : Set G) = ⊥ :=
  burnsideB610_inf_centralizer_eq_bot hV (burnsideB610_preI_le_normalizer hV hHN)
    (by rw [autI_preI hV hBH]; exact hcf)

@[expose] noncomputable def burnsideB610_natOf
    (e : ↥B ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2))
    (φ : ↥(commV B) ≃* Multiplicative (Fin 2 → ZMod 2))
    (hφ : ∀ (h : ↥B) (u : ↥(commV B)) (hu : (h : MulAut (IntMod V hV)) (u : IntMod V hV) ∈ commV B),
      φ ⟨(h : MulAut (IntMod V hV)) u, hu⟩ =
        Multiplicative.ofAdd ((e h : Matrix (Fin 2) (Fin 2) (ZMod 2)) *ᵥ
          Multiplicative.toAdd (φ u)))
    (hcf : commV B ⊓ fixV B = ⊥) : NatData (preI hV H hHN B) V (ZMod 2) where
  α := burnsideB610_natAlpha hV hHN hBH e
  surj := burnsideB610_natAlpha_surjective hV hHN hBH e
  ker := burnsideB610_natAlpha_ker hV hHN hBH e
  β := φ.toMonoidHom.comp (burnsideB610_commIncl hV hHN hBH)
  βsurj := by
    intro z
    obtain ⟨m, rfl⟩ := φ.surjective z
    obtain ⟨w, rfl⟩ := burnsideB610_commIncl_surjective hV hHN hBH m
    exact ⟨w, rfl⟩
  βker := by
    rw [burnsideB610_preI_inf_centralizer hV hHN hBH hcf, Subgroup.bot_subgroupOf]
    exact (MonoidHom.ker_eq_bot_iff _).2
      (φ.injective.comp (burnsideB610_commIncl_injective hV hHN hBH))
  βeq := by
    intro a u v huv
    have heq : ((burnsideB610_preProj hV hHN hBH a : ↥B) : MulAut (IntMod V hV))
        (burnsideB610_commIncl hV hHN hBH u : IntMod V hV) =
          (burnsideB610_commIncl hV hHN hBH v : IntMod V hV) := by
      apply IntMod.val_injective
      rw [burnsideB610_preProj_apply, convI_apply_val, burnsideB610_commIncl_val,
        burnsideB610_commIncl_val]
      exact huv.symm
    have hmem : ((burnsideB610_preProj hV hHN hBH a : ↥B) : MulAut (IntMod V hV))
        (burnsideB610_commIncl hV hHN hBH u : IntMod V hV) ∈ commV B := by
      rw [heq]
      exact (burnsideB610_commIncl hV hHN hBH v).2
    have hv : burnsideB610_commIncl hV hHN hBH v = ⟨_, hmem⟩ := Subtype.ext heq.symm
    show Multiplicative.toAdd (φ (burnsideB610_commIncl hV hHN hBH v)) =
      ((burnsideB610_natAlpha hV hHN hBH e a : GL (Fin 2) (ZMod 2)) :
        Matrix (Fin 2) (Fin 2) (ZMod 2)) *ᵥ
          Multiplicative.toAdd (φ (burnsideB610_commIncl hV hHN hBH u))
    rw [hv, hφ]
    rfl

@[expose] noncomputable def burnsideB610_natOfActs (hnat : ActsAsNaturalL2 B (commV B))
    (hcf : commV B ⊓ fixV B = ⊥) : NatData (preI hV H hHN B) V (ZMod 2) :=
  burnsideB610_natOf hV hHN hBH hnat.choose hnat.choose_spec.choose
    hnat.choose_spec.choose_spec hcf

end NatOf

section NatFacts

variable {G : Type} [Group G] {Y V : Subgroup G} {F : Type} [Field F]

theorem burnsideB610_beta_injective (D : NatData Y V F)
    (h : ⁅V, Y⁆ ⊓ Subgroup.centralizer (Y : Set G) = ⊥) : Function.Injective D.β := by
  rw [← MonoidHom.ker_eq_bot_iff, D.βker, h]
  exact Subgroup.bot_subgroupOf _

theorem burnsideB610_mem_centralizer_of_act_eq_one (D : NatData Y V F)
    (hinj : Function.Injective D.β) (a : ↥(nLV Y V)) (ha : D.act a = 1) :
    (a : G) ∈ Subgroup.centralizer ((⁅V, Y⁆ : Subgroup G) : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  have h1 := rho_apply D.β D.βsurj D.βker a ⟨w, hw⟩
  have h2 : rho D.β D.βsurj D.βker a = 1 := ha
  rw [h2, MulAut.one_apply] at h1
  have h3 := congrArg Subtype.val (hinj h1)
  rw [coe_cW] at h3
  calc w * (a : G) = ((a : G) * w * (a : G)⁻¹) * a := by rw [← h3]
    _ = a * w := by group

theorem burnsideB610_fixV_img_eq_bot (D : NatData Y V F) (hinj : Function.Injective D.β)
    {K : Subgroup G} {k : G} (hk : k ∈ K) (hkN : k ∈ nLV Y V)
    (hfpf : ∀ u ∈ ⁅V, Y⁆, k * u * k⁻¹ = u → u = 1) : fixV (D.img K) = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).2 fun z hz => ?_
  obtain ⟨w, rfl⟩ := D.βsurj z
  have hmem : D.act ⟨k, hkN⟩ ∈ D.img K := ⟨⟨k, hkN⟩, Subgroup.mem_subgroupOf.2 hk, rfl⟩
  have h1 := hz _ hmem
  have h2 : rho D.β D.βsurj D.βker ⟨k, hkN⟩ (D.β w) = D.β w := h1
  rw [rho_apply] at h2
  have h3 := congrArg Subtype.val (hinj h2)
  rw [coe_cW] at h3
  have hw1 : (w : G) = 1 := hfpf w w.2 h3
  have : w = 1 := Subtype.ext hw1
  rw [this, map_one]

theorem burnsideB610_autI_ne_bot (hV : IsElemAbelian 2 V) (D : NatData Y V F)
    (hYN : Y ≤ Subgroup.normalizer (V : Set G)) {P : Subgroup G}
    (hPN : P ≤ Subgroup.normalizer (V : Set G)) (hP : D.img P ≠ ⊥) : autI hV P ≠ ⊥ := by
  intro hbot
  apply hP
  have hPC : P ≤ Subgroup.centralizer (V : Set G) := (autI_eq_bot_iff hV hPN).1 hbot
  refine (Subgroup.map_eq_bot_iff _).2 fun a ha => ?_
  exact D.act_eq_one hYN a (hPC (Subgroup.mem_subgroupOf.1 ha))

end NatFacts

end CFSG.Quasithin.B610T.TwoBlk
