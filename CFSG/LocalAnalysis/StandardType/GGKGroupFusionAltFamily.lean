module

public import CFSG.LocalAnalysis.StandardType.GGKGroupFusionAltCore
public import CFSG.LocalAnalysis.StandardType.GGKGroupFusionBridge
public import CFSG.Quasithin.SteinbergCBAlternatingAut
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierAlternatingSix
public import CFSG.LocalAnalysis.ComponentClassification.BlockTwoProductAction
public import CFSG.LocalAnalysis.ComponentClassification.NormalizedProductSylow
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionFixedInvolution
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionInvariantSylow
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
public import CFSG.Permutation.AlternatingAutomorphism

public section

namespace CFSG.StandardType

open CFSG.Assembly Equiv Equiv.Perm
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

theorem ggNot_three_dvd_outer_six : ¬ 3 ∣ Nat.card (Outer (alternatingGroup (Fin 6))) := by
  have hle := CFSG.ComponentClassification.CatalogueSchreierAlternating.DegreeSix.outer_card_le_four
  have hfin : Finite (MulAut (alternatingGroup (Fin 6))) := MulEquiv.finite_left
  have hpos : 0 < Nat.card (Outer (alternatingGroup (Fin 6))) := Nat.card_pos
  have hf1 : QuotientGroup.mk' (inner (alternatingGroup (Fin 6)))
      (CFSG.Quasithin.SteinbergCB.conjPerm 6 (swap 0 1)) ≠ 1 := by
    intro h
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      ← CFSG.Quasithin.SteinbergCB.map_conjPerm_alternatingGroup] at h
    obtain ⟨a, ha, hae⟩ := h
    have := CFSG.Quasithin.SteinbergCB.conjPerm_injective (by norm_num) hae
    rw [this, SetLike.mem_coe, mem_alternatingGroup, sign_swap (by decide)] at ha
    exact absurd ha (by decide)
  have hf2 : QuotientGroup.mk' (inner (alternatingGroup (Fin 6)))
      (CFSG.Quasithin.SteinbergCB.conjPerm 6 (swap 0 1)) ^ 2 = 1 := by
    rw [← map_pow, ← map_pow, sq, swap_mul_self, map_one, map_one]
  have hord := orderOf_eq_prime hf2 hf1
  have hdvd : 2 ∣ Nat.card (Outer (alternatingGroup (Fin 6))) := hord ▸ orderOf_dvd_natCard _
  omega

theorem ggNot_dvd_outer_alternating {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hn5 : 5 ≤ n) :
    ¬ p ∣ Nat.card (Outer (alternatingGroup (Fin n))) := by
  have hfin : Finite (MulAut (alternatingGroup (Fin n))) := MulEquiv.finite_left
  have hpos : 0 < Nat.card (Outer (alternatingGroup (Fin n))) := Nat.card_pos
  by_cases h6 : n = 6
  · subst h6
    intro hd
    by_cases h3 : p = 3
    · subst h3
      exact ggNot_three_dvd_outer_six hd
    · have hle :=
        CFSG.ComponentClassification.CatalogueSchreierAlternating.DegreeSix.outer_card_le_four
      have h1 := Nat.le_of_dvd hpos hd
      have h5 := hp.five_le_of_ne_two_of_ne_three hp2 h3
      omega
  · have h2 :=
      (CFSG.Quasithin.SteinbergCB.isSolvable_outer_alternatingGroup (by omega : n = 5 ∨ 7 ≤ n)).2
    intro hd
    have h1 := Nat.le_of_dvd (by norm_num) (hd.trans h2)
    have := hp.two_le
    omega

theorem ggCard_outer_congr {K K' : Type} [Group K] [Group K'] (e : K ≃* K') :
    Nat.card (Outer K) = Nat.card (Outer K') :=
  Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).toEquiv

theorem ggMem_generalizedFitting_of_pow {W : Type} [Group W] [Finite W] {p : ℕ} (hp : p.Prime)
    (hsimple : IsSimpleGroup ↥(CFSG.generalizedFitting W))
    (hnab : ∃ a b : ↥(CFSG.generalizedFitting W), a * b ≠ b * a)
    (hout : ¬ p ∣ Nat.card (Outer ↥(CFSG.generalizedFitting W))) {x : W} (hx : x ^ p = 1) :
    x ∈ CFSG.generalizedFitting W := by
  have hKn : (CFSG.generalizedFitting W).Normal :=
    CFSG.LocalCores.generalized_fitting_characteristic.2
  have hfin : Finite (MulAut ↥(CFSG.generalizedFitting W)) := MulEquiv.finite_left
  set β : MulAut ↥(CFSG.generalizedFitting W) := MulAut.conjNormal x with hβdef
  have hβ : β ^ p = 1 := by rw [hβdef, ← map_pow, hx, map_one]
  have h1 : (QuotientGroup.mk β : Outer ↥(CFSG.generalizedFitting W)) ^ p = 1 := by
    rw [← QuotientGroup.mk_pow, hβ, QuotientGroup.mk_one]
  rcases (Nat.dvd_prime hp).mp (orderOf_dvd_of_pow_eq_one h1) with h | h
  · have hβi : β ∈ inner ↥(CFSG.generalizedFitting W) :=
      (QuotientGroup.eq_one_iff β).mp (orderOf_eq_one_iff.mp h)
    obtain ⟨k, hk⟩ := hβi
    have hw : x⁻¹ * (k : W) = 1 := by
      apply ggEq_one_of_commute_generalizedFitting hsimple hnab
      intro y hy
      have h3 := congrArg (fun f : MulAut ↥(CFSG.generalizedFitting W) =>
        ((f ⟨y, hy⟩ : ↥(CFSG.generalizedFitting W)) : W)) hk
      simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv,
        hβdef, MulAut.conjNormal_apply] at h3
      calc x⁻¹ * (k : W) * y = x⁻¹ * ((k : W) * y * (k : W)⁻¹) * (k : W) := by group
        _ = x⁻¹ * (x * y * x⁻¹) * (k : W) := by rw [h3]
        _ = y * (x⁻¹ * (k : W)) := by group
    have hxk : x = k := by
      calc x = x * (x⁻¹ * (k : W)) := by rw [hw, mul_one]
        _ = k := by group
    rw [hxk]
    exact k.2
  · exact absurd (h ▸ orderOf_dvd_natCard _) hout

section Transport

theorem ggNotLe_ker_of_injective {G G' : Type*} [Group G] [Group G'] {f : G →* G'}
    (hf : Function.Injective f) {L : Subgroup G} (hL : L ≠ ⊥) : ¬ L ≤ f.ker := by
  rw [(MonoidHom.ker_eq_bot_iff f).mpr hf]
  exact fun h => hL (le_bot_iff.mp h)

variable {W : Type} [Group W] {n : ℕ} {K : Subgroup W} (e : ↥K ≃* ↥(alternatingGroup (Fin n)))

@[expose] noncomputable def ggAltImage (H : Subgroup W) : Subgroup (Perm (Fin n)) :=
  ((H.subgroupOf K).map e.toMonoidHom).map (alternatingGroup (Fin n)).subtype

theorem ggAltImage_le (H : Subgroup W) : ggAltImage e H ≤ alternatingGroup (Fin n) :=
  Subgroup.map_subtype_le _

theorem ggMem_altImage_iff {H : Subgroup W} {x : Perm (Fin n)} :
    x ∈ ggAltImage e H ↔ ∃ k : ↥K, (k : W) ∈ H ∧ ((e k : ↥(alternatingGroup (Fin n))) : Perm (Fin n)) = x := by
  constructor
  · rintro ⟨a, ⟨k, hk, rfl⟩, rfl⟩
    exact ⟨k, hk, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨e k, ⟨k, hk, rfl⟩, rfl⟩

theorem ggMem_altImage {H : Subgroup W} {k : ↥K} :
    ((e k : ↥(alternatingGroup (Fin n))) : Perm (Fin n)) ∈ ggAltImage e H ↔ (k : W) ∈ H := by
  rw [ggMem_altImage_iff]
  constructor
  · rintro ⟨k', hk', hkk⟩
    have : k' = k := e.injective (Subtype.ext hkk)
    rwa [← this]
  · intro hk
    exact ⟨k, hk, rfl⟩

noncomputable def ggAltImageEquiv {C : Subgroup W} (hCK : C ≤ K) : ↥C ≃* ↥(ggAltImage e C) :=
  (Subgroup.subgroupOfEquivOfLe hCK).symm.trans
    ((Subgroup.equivMapOfInjective _ e.toMonoidHom e.injective).trans
      (Subgroup.equivMapOfInjective _ _ (alternatingGroup (Fin n)).subtype_injective))

theorem ggIsComponentOf_altImage {H C : Subgroup W} (hC : IsComponentOf C (H ⊓ K)) :
    IsComponentOf (ggAltImage e C) (ggAltImage e H) := by
  have h1 := ggIsComponentOf_subgroupOf hC (inf_le_right : H ⊓ K ≤ K)
  rw [Subgroup.inf_subgroupOf_right] at h1
  have h2 := ggIsComponentOf_map e.toMonoidHom h1
    (ggNotLe_ker_of_injective e.injective (ggComponent_ne_bot h1))
  exact ggIsComponentOf_map (alternatingGroup (Fin n)).subtype h2
    (ggNotLe_ker_of_injective (alternatingGroup (Fin n)).subtype_injective (ggComponent_ne_bot h2))

theorem ggExists_isComponentOf_of_altImage {H : Subgroup W} {C' : Subgroup (Perm (Fin n))}
    (hC' : IsComponentOf C' (ggAltImage e H)) :
    ∃ C : Subgroup W, IsComponentOf C (H ⊓ K) ∧ Nonempty (↥C ≃* ↥C') := by
  have hC'A : C' ≤ alternatingGroup (Fin n) := hC'.1.trans (ggAltImage_le e H)
  have h1 := ggIsComponentOf_subgroupOf hC' (ggAltImage_le e H)
  have heq1 : (ggAltImage e H).subgroupOf (alternatingGroup (Fin n)) =
      (H.subgroupOf K).map e.toMonoidHom :=
    Subgroup.comap_map_eq_self_of_injective (alternatingGroup (Fin n)).subtype_injective _
  rw [heq1] at h1
  have h2 := ggIsComponentOf_map e.symm.toMonoidHom h1
    (ggNotLe_ker_of_injective e.symm.injective (ggComponent_ne_bot h1))
  have hid : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id _ := by
    ext x
    simp
  rw [Subgroup.map_map, hid, Subgroup.map_id] at h2
  have h3 := ggIsComponentOf_map K.subtype h2
    (ggNotLe_ker_of_injective K.subtype_injective (ggComponent_ne_bot h2))
  rw [Subgroup.subgroupOf_map_subtype] at h3
  exact ⟨_, h3, ⟨(Subgroup.equivMapOfInjective _ K.subtype K.subtype_injective).symm.trans
    ((Subgroup.equivMapOfInjective _ e.symm.toMonoidHom e.symm.injective).symm.trans
      (Subgroup.subgroupOfEquivOfLe hC'A))⟩⟩

end Transport

@[expose] def GGAltNotMarkedInput : Prop :=
  ∀ (m : ℕ), 7 ≤ m → m ≠ 8 → ∀ (L : Type) [Group L],
    Nonempty (L ≃* ↥(alternatingGroup (Fin m))) → ∀ P : LargeEvenMarkProp L, ¬ LargeEvenMarking L P

open CFSG.ComponentClassification.OuterAutomorphisms in
theorem ggKGroupFusionAt_alternating_of (hNM : GGAltNotMarkedInput) :
    GGKGroupFusionAt GGKFAlternating := by
  rintro W _ _ p H E i ⟨n, hn, rfl⟩ hyp - hKH ⟨e⟩
  obtain ⟨⟨hp, hp2, hE, hEcard, hfus⟩, ⟨hsimple, hnab, -⟩, hIIIa, -⟩ := hyp
  have : Fact p.Prime := ⟨hp⟩
  have hKn : (CFSG.generalizedFitting W).Normal :=
    CFSG.LocalCores.generalized_fitting_characteristic.2
  have hout : ¬ p ∣ Nat.card (Outer ↥(CFSG.generalizedFitting W)) := by
    rw [ggCard_outer_congr e]
    exact ggNot_dvd_outer_alternating hp hp2 hn
  have hEK : E ≤ CFSG.generalizedFitting W := fun x hx =>
    ggMem_generalizedFitting_of_pow hp hsimple hnab hout (hE.2 x hx)
  have hEH : E ≤ H := hfus.1
  have hMtop : ¬ alternatingGroup (Fin n) ≤ ggAltImage e H := by
    intro hle
    apply hKH
    intro k hk
    have h1 := hle (e ⟨k, hk⟩).2
    exact (ggMem_altImage e).mp h1
  have hEM : ggAltImage e E ≤ ggAltImage e H :=
    Subgroup.map_mono (Subgroup.map_mono (Subgroup.comap_mono hEH))
  have hEab' : ∀ x ∈ ggAltImage e E, ∀ y ∈ ggAltImage e E, x * y = y * x := by
    intro x hx y hy
    obtain ⟨k, hk, rfl⟩ := (ggMem_altImage_iff e).mp hx
    obtain ⟨k', hk', rfl⟩ := (ggMem_altImage_iff e).mp hy
    have hc0 := hE.1.is_comm.comm (⟨k, hk⟩ : ↥E) ⟨k', hk'⟩
    have hc : k * k' = k' * k := Subtype.ext (by simpa using congrArg Subtype.val hc0)
    rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul, hc]
  have hEp' : ∀ x ∈ ggAltImage e E, x ^ p = 1 := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := (ggMem_altImage_iff e).mp hx
    have hkp : k ^ p = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      exact hE.2 _ hk)
    rw [← Subgroup.coe_pow, ← map_pow, hkp, map_one, Subgroup.coe_one]
  have hEcard' : Nat.card (ggAltImage e E) = p ^ 2 := by
    rw [← hEcard]
    exact (Nat.card_congr (ggAltImageEquiv e hEK).toEquiv).symm
  have hctl : ∀ g ∈ alternatingGroup (Fin n), ∀ x ∈ ggAltImage e E, x ≠ 1 →
      g⁻¹ * x * g ∈ ggAltImage e H → g ∈ ggAltImage e H := by
    intro g hg x hx hx1 hgx
    obtain ⟨y, hyE, rfl⟩ := (ggMem_altImage_iff e).mp hx
    set k := e.symm ⟨g, hg⟩ with hkdef
    have hgk : ((e k : ↥(alternatingGroup (Fin n))) : Perm (Fin n)) = g := by simp [hkdef]
    have hy1 : (y : W) ≠ 1 := by
      intro h
      apply hx1
      have : y = 1 := Subtype.ext h
      rw [this, map_one, Subgroup.coe_one]
    rw [← hgk] at hgx ⊢
    have h1 : ((e (k⁻¹ * y * k) : ↥(alternatingGroup (Fin n))) : Perm (Fin n)) ∈ ggAltImage e H := by
      simpa [map_mul, map_inv] using hgx
    have h2 := (ggMem_altImage e).mp h1
    have h3 : (k : W)⁻¹ * (y : W) * (k : W) ∈ H := by simpa using h2
    exact (ggMem_altImage e).mpr ((ggControlsStrongFusion_iff.mp hfus).2 _ hyE hy1 _ h3)
  rcases ggAltCore hp2 hMtop hEM hEab' hEp' hEcard' hctl with
    ⟨rfl, h6, hnc⟩ | ⟨rfl, ⟨k, hk2, hk4, hk⟩, hcomp⟩ | ⟨C', hC', m, hm7, hm8, ⟨eC⟩⟩
  ·
    left
    have hn6 : n = 6 := by simpa using h6
    subst hn6
    exact ⟨rfl, ⟨e⟩, fun C hC => hnc _ (ggIsComponentOf_altImage e hC)⟩
  ·
    right
    left
    have hn5 : n = 5 * k := by simpa using hk
    subst hn5
    refine ⟨rfl, ⟨k, hk2, hk4, ⟨e⟩⟩, fun C hC => ?_⟩
    obtain ⟨eA⟩ := hcomp _ (ggIsComponentOf_altImage e hC)
    have e5 : ↥C ≃* ↥(alternatingGroup (Fin 5)) :=
      (ggAltImageEquiv e (hC.1.trans inf_le_right)).trans eA
    have hsimp : IsSimpleGroup ↥C :=
      (MulEquiv.isSimpleGroup_congr e5).mpr (alternatingGroup.isSimpleGroup (by simp))
    have hnabC : ∃ a b : ↥C, a * b ≠ b * a := by
      have h5 : ¬ IsMulCommutative ↥(alternatingGroup (Fin 5)) := by
        rw [alternatingGroup.isMulCommutative_iff_card_le_three]
        simp
      by_contra h
      push Not at h
      exact h5 ⟨⟨fun a b => e5.symm.injective (by rw [map_mul, map_mul]; exact h _ _)⟩⟩
    have hZ := ggCenter_eq_bot_of_simple hnabC
    exact ⟨((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans e5⟩
  ·
    exfalso
    obtain ⟨L, hLc, ⟨eL⟩⟩ := ggExists_isComponentOf_of_altImage e hC'
    have eLm : ↥L ≃* ↥(alternatingGroup (Fin m)) := eL.trans eC
    have hLsimp : IsSimpleGroup ↥L :=
      (MulEquiv.isSimpleGroup_congr eLm).mpr (alternatingGroup.isSimpleGroup (by simp; omega))
    have hLH : L ≤ H := hLc.1.trans inf_le_left
    have hnorm : ((H ⊓ CFSG.generalizedFitting W).subgroupOf H).Normal := by
      rw [Subgroup.inf_subgroupOf_left]
      exact hKn.subgroupOf H
    have hLcH : IsComponentOf L H :=
      ⟨hLH, ggIsSubnormal_trans hLc.2.1 (ggIsSubnormal_of_normal inf_le_left hnorm), hLc.2.2⟩
    have hL1 := ggIsComponentOf_subgroupOf hLcH (le_refl H)
    rw [Subgroup.subgroupOf_self] at hL1
    set π := QuotientGroup.mk' (CFSG.pCore 2 ↥H) with hπ
    have hO2 : Group.IsSolvable ↥(CFSG.pCore 2 ↥H) := by
      have : Fact (2 : ℕ).Prime := ⟨Nat.prime_two⟩
      have : Group.IsNilpotent ↥(CFSG.pCore 2 ↥H) :=
        (CFSG.pCore_isPGroup (p := 2) (G := ↥H)).isNilpotent
      infer_instance
    have hnotker : ¬ L.subgroupOf H ≤ π.ker := by
      rw [hπ, QuotientGroup.ker_mk']
      exact ggComponent_not_le_of_isSolvable hL1 hO2
    have hCbar := ggIsComponentOf_map π hL1 hnotker
    rw [Subgroup.map_top_of_surjective π (QuotientGroup.mk'_surjective _)] at hCbar
    obtain ⟨-, hmark⟩ := hIIIa _ hCbar
    set f : ↥(L.subgroupOf H) →* GGHypQuot H := π.comp (L.subgroupOf H).subtype with hf
    have hLsub : IsSimpleGroup ↥(L.subgroupOf H) :=
      (MulEquiv.isSimpleGroup_congr (Subgroup.subgroupOfEquivOfLe hLH).symm).mp hLsimp
    have hfinj : Function.Injective f := by
      rw [← MonoidHom.ker_eq_bot_iff]
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal f.ker with h | h
      · exact h
      · exfalso
        apply hnotker
        intro x hx
        have : (⟨x, hx⟩ : ↥(L.subgroupOf H)) ∈ f.ker := h ▸ Subgroup.mem_top _
        rw [MonoidHom.mem_ker] at this
        rw [MonoidHom.mem_ker]
        exact this
    have hrange : f.range = (L.subgroupOf H).map π := by
      rw [hf, MonoidHom.range_comp, Subgroup.range_subtype]
    have eCbar : ↥((L.subgroupOf H).map π) ≃* ↥(alternatingGroup (Fin m)) :=
      (MulEquiv.subgroupCongr hrange).symm.trans ((MonoidHom.ofInjective hfinj).symm.trans
        ((Subgroup.subgroupOfEquivOfLe hLH).trans eLm))
    exact hNM m hm7 hm8 _ ⟨eCbar⟩ _ hmark

end CFSG.StandardType
