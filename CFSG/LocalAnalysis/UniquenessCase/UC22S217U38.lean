module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
import CFSG.LocalAnalysis.UniquenessCase.UC6S846g
import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
public import CFSG.CGT.Timmesfeld75.Statements
public import CFSG.Foundations
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.RankThreeUC.Asc1930
public import CFSG.Quasithin.Background.A1bGroups
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase
import CFSG.LocalAnalysis.UniquenessCase.UC6S846d
import CFSG.LocalAnalysis.UniquenessCase.UCFront07
import CFSG.LocalAnalysis.UniquenessCase.UCFront08
import CFSG.LocalAnalysis.UniquenessCase.UCR638
import CFSG.Milestones.ASVolI.I2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup

local notation "Z₉" => Multiplicative (ZMod 9)

section Omega

variable {A P : Type*} [CommGroup A] [Finite A] [Group P]

theorem uc22s217u38_exists_elemAbelian (Φ : A →* P) {p : ℕ}
    (hker : Φ.ker ≤ (powMonoidHom p : A →* A).range) :
    ∃ E : Subgroup P, IsElemAbelian p E ∧ Nat.card E = Nat.card (powMonoidHom p : A →* A).ker := by
  set pw : A →* A := powMonoidHom p with hpw
  set K₃ : Subgroup A := (Φ.comp pw).ker with hK₃
  have hΦK : Φ.ker ≤ K₃ := fun a ha => by
    rw [hK₃, MonoidHom.mem_ker, MonoidHom.comp_apply, hpw, powMonoidHom_apply, map_pow,
      MonoidHom.mem_ker.1 ha, one_pow]
  have hpwK : pw.ker ≤ K₃ := fun a ha => by
    rw [hK₃, MonoidHom.mem_ker, MonoidHom.comp_apply, MonoidHom.mem_ker.1 ha, map_one]
  refine ⟨K₃.map Φ, ⟨⟨⟨?_⟩⟩, ?_⟩, ?_⟩
  · rintro ⟨_, a, -, rfl⟩ ⟨_, b, -, rfl⟩
    exact Subtype.ext ((map_mul Φ a b).symm.trans ((congrArg Φ (mul_comm a b)).trans (map_mul Φ b a)))
  · rintro _ ⟨a, ha, rfl⟩
    have h1 : Φ (a ^ p) = 1 := MonoidHom.mem_ker.1 ha
    rwa [map_pow] at h1
  · have h1 := Subgroup.card_ker_mul_card_range (Φ.domRestrict K₃)
    rw [MonoidHom.ker_domRestrict, MonoidHom.domRestrict_range,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hΦK).toEquiv] at h1
    have e3 : K₃.map pw = Φ.ker := by
      ext b
      constructor
      · rintro ⟨a, ha, rfl⟩
        exact ha
      · intro hb
        obtain ⟨a, rfl⟩ := hker hb
        exact ⟨a, hb, rfl⟩
    have h2 := Subgroup.card_ker_mul_card_range (pw.domRestrict K₃)
    rw [MonoidHom.ker_domRestrict, MonoidHom.domRestrict_range, e3,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hpwK).toEquiv] at h2
    have hpos : 0 < Nat.card Φ.ker := Nat.card_pos
    refine Nat.eq_of_mul_eq_mul_left hpos ?_
    rw [h1, ← h2, Nat.mul_comm]

end Omega

section ZNine

private noncomputable def uc22s217u38_zhom {S : Type*} [Group S] (x : S) (hx : x ^ 9 = 1) :
    Z₉ →* S :=
  MonoidHom.mk' (fun k => x ^ (Multiplicative.toAdd k).val) (fun a b => by
    have key : ∀ n : ℕ, x ^ (n % 9) = x ^ n := fun n => by
      conv_rhs => rw [← Nat.div_add_mod n 9, pow_add, pow_mul, hx, one_pow, one_mul]
    simp only [toAdd_mul]
    rw [ZMod.val_add, key, pow_add])

private theorem uc22s217u38_zhom_apply {S : Type*} [Group S] (x : S) (hx : x ^ 9 = 1) (k : Z₉) :
    uc22s217u38_zhom x hx k = x ^ (Multiplicative.toAdd k).val :=
  rfl

theorem uc22s217u38_mem_range_pow (k : Z₉) (hk : 3 ∣ (Multiplicative.toAdd k).val) :
    k ∈ (powMonoidHom 3 : Z₉ →* Z₉).range := by
  obtain ⟨c, hc⟩ := hk
  refine ⟨Multiplicative.ofAdd (c : ZMod 9), ?_⟩
  rw [powMonoidHom_apply, ← ofAdd_nsmul]
  apply Multiplicative.toAdd.injective
  rw [toAdd_ofAdd, nsmul_eq_mul, ← Nat.cast_mul, ← hc, ZMod.natCast_zmod_val]

theorem uc22s217u38_card_ker_pow_z9 : Nat.card (powMonoidHom 3 : Z₉ →* Z₉).ker = 3 := by
  rw [Nat.card_eq_fintype_card]
  decide

theorem uc22s217u38_card_ker_pow_prod {X Y : Type*} [CommGroup X] [CommGroup Y] (p : ℕ) :
    Nat.card (powMonoidHom p : X × Y →* X × Y).ker =
      Nat.card (powMonoidHom p : X →* X).ker * Nat.card (powMonoidHom p : Y →* Y).ker := by
  have hA : (powMonoidHom p : X × Y →* X × Y) = (powMonoidHom p).prodMap (powMonoidHom p) :=
    MonoidHom.ext fun _ => rfl
  rw [hA, MonoidHom.ker_prodMap, Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod]

theorem uc22s217u38_card_ker_pow :
    Nat.card (powMonoidHom 3 : (Z₉ × Z₉) × (Z₉ × Z₉) →* (Z₉ × Z₉) × (Z₉ × Z₉)).ker = 3 ^ 4 := by
  rw [uc22s217u38_card_ker_pow_prod, uc22s217u38_card_ker_pow_prod, uc22s217u38_card_ker_pow_z9]
  norm_num

end ZNine

section Cover

variable {G : Type} [Group G] [Finite G]

theorem uc22s217u38_pRank_of_cover {M L : Subgroup G} (hL : L ∈ calC M)
    (hnN : ¬ M ≤ normalizer (L : Set G)) {S : Type} [Group S] [Finite S]
    (hS : commutator S = ⊤) {α : S →* Bar2 L} (hα : Function.Surjective α)
    (hαc : α.ker ≤ center S) {h y : S} (hhy : h * y = y * h) (hh9 : h ^ 9 = 1)
    (hy9 : y ^ 9 = 1) (hZ : ∀ i j : ℕ, h ^ i * y ^ j ∈ center S → 3 ∣ i ∧ 3 ∣ j) :
    4 ≤ Open.pRank 3 M := by
  classical
  have hSp : Group.IsPerfect S := Group.isPerfect_def.2 hS
  obtain ⟨m, hmM, hmN⟩ := SetLike.not_le_iff_exists.1 hnN
  let f : MulAut G := MulAut.conj m
  have hM : M.map f.toMonoidHom = M :=
    UC6S846.mem_normalizer_iff_map_conj.1 (Subgroup.le_normalizer hmM)
  have hL' : L.map f.toMonoidHom ∈ calC M := UC6S846.calC_map M f hM hL
  have hne : L ≠ L.map f.toMonoidHom := fun he =>
    hmN (UC6S846.mem_normalizer_iff_map_conj.2 he.symm)
  have hLM : L ≤ M := hL.1.le
  have hL'M : L.map f.toMonoidHom ≤ M := hL'.1.le
  obtain ⟨hsn, hp, hqs, -⟩ := UC6S846.calC_subgroupOf hL
  obtain ⟨hsn', hp', hqs', -⟩ := UC6S846.calC_subgroupOf hL'
  have hne' : L.subgroupOf M ≠ (L.map f.toMonoidHom).subgroupOf M := by
    intro he
    apply hne
    have := congrArg (Subgroup.map M.subtype) he
    rwa [Subgroup.map_subgroupOf_eq_of_le hLM, Subgroup.map_subgroupOf_eq_of_le hL'M] at this
  let π : ↥M →* ↥M ⧸ CFSG.pCore 2 ↥M := QuotientGroup.mk' (CFSG.pCore 2 ↥M)
  let C₁ : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M) := (L.subgroupOf M).map π
  let C₂ : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M) := ((L.map f.toMonoidHom).subgroupOf M).map π
  have hcomm : ⁅C₁, C₂⁆ = ⊥ :=
    (CFSG.LocalCores.distinct_components_commute (UC6S846.isComponent_image hsn hqs)
      (UC6S846.isComponent_image hsn' hqs')).resolve_left
      (fun he => hne' (UC6S846.image_injective hsn hp hsn' hp' he))
  have hc12 : ∀ x ∈ C₁, ∀ z ∈ C₂, x * z = z * x := by
    intro x hx z hz
    have h1 : C₁ ≤ Subgroup.centralizer (C₂ : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm
    exact (Subgroup.mem_centralizer_iff.1 (h1 hx) z hz).symm
  let e₁ : ↥L ≃* ↥(L.subgroupOf M) := (Subgroup.subgroupOfEquivOfLe hLM).symm
  let e₂ : ↥L ≃* ↥((L.map f.toMonoidHom).subgroupOf M) :=
    (Subgroup.equivMapOfInjective L f.toMonoidHom f.injective).trans
      (Subgroup.subgroupOfEquivOfLe hL'M).symm
  let β₁ : S →* ↥C₁ :=
    ((UC6S846.barIso hsn).toMonoidHom.comp (UC6S846.bar2Equiv e₁).toMonoidHom).comp α
  let β₂ : S →* ↥C₂ :=
    ((UC6S846.barIso hsn').toMonoidHom.comp (UC6S846.bar2Equiv e₂).toMonoidHom).comp α
  have hβ₁ : Function.Surjective β₁ :=
    (UC6S846.barIso hsn).surjective.comp ((UC6S846.bar2Equiv e₁).surjective.comp hα)
  have hβ₂ : Function.Surjective β₂ :=
    (UC6S846.barIso hsn').surjective.comp ((UC6S846.bar2Equiv e₂).surjective.comp hα)
  have hβ₁c : β₁.ker ≤ center S := fun s hs => by
    have h1 : (UC6S846.barIso hsn) ((UC6S846.bar2Equiv e₁) (α s)) = 1 := MonoidHom.mem_ker.1 hs
    exact hαc (MonoidHom.mem_ker.2 ((map_eq_one_iff _ (UC6S846.bar2Equiv e₁).injective).1
      ((map_eq_one_iff _ (UC6S846.barIso hsn).injective).1 h1)))
  have hβ₂c : β₂.ker ≤ center S := fun s hs => by
    have h1 : (UC6S846.barIso hsn') ((UC6S846.bar2Equiv e₂) (α s)) = 1 := MonoidHom.mem_ker.1 hs
    exact hαc (MonoidHom.mem_ker.2 ((map_eq_one_iff _ (UC6S846.bar2Equiv e₂).injective).1
      ((map_eq_one_iff _ (UC6S846.barIso hsn').injective).1 h1)))
  have hZ₁ : ∀ s : S, β₁ s ∈ center ↥C₁ → s ∈ center S := fun s hs => by
    rw [← CFSG.LocalCores.comap_center_eq_of_perfect hSp β₁ hβ₁ hβ₁c]
    exact hs
  have hZ₂ : ∀ s : S, β₂ s ∈ center ↥C₂ → s ∈ center S := fun s hs => by
    rw [← CFSG.LocalCores.comap_center_eq_of_perfect hSp β₂ hβ₂ hβ₂c]
    exact hs
  let Ψ : Z₉ × Z₉ →* S :=
    (uc22s217u38_zhom h hh9).noncommCoprod (uc22s217u38_zhom y hy9) (fun a b => by
      rw [uc22s217u38_zhom_apply, uc22s217u38_zhom_apply]
      exact Commute.pow_pow (a := h) (b := y) hhy _ _)
  have hΨ : ∀ u, Ψ u ∈ center S → u ∈ (powMonoidHom 3 : Z₉ × Z₉ →* Z₉ × Z₉).range := by
    rintro ⟨a, b⟩ hu
    have hu' : h ^ (Multiplicative.toAdd a).val * y ^ (Multiplicative.toAdd b).val ∈ center S := hu
    obtain ⟨ha, hb⟩ := hZ _ _ hu'
    obtain ⟨a', ha'⟩ := uc22s217u38_mem_range_pow a ha
    obtain ⟨b', hb'⟩ := uc22s217u38_mem_range_pow b hb
    refine ⟨(a', b'), ?_⟩
    rw [powMonoidHom_apply] at ha' hb' ⊢
    rw [Prod.pow_mk, ha', hb']
  let Φ : (Z₉ × Z₉) × (Z₉ × Z₉) →* ↥M ⧸ CFSG.pCore 2 ↥M :=
    (C₁.subtype.comp (β₁.comp Ψ)).noncommCoprod (C₂.subtype.comp (β₂.comp Ψ))
      (fun u v => hc12 _ (β₁ (Ψ u)).2 _ (β₂ (Ψ v)).2)
  have hker : Φ.ker ≤
      (powMonoidHom 3 : (Z₉ × Z₉) × (Z₉ × Z₉) →* (Z₉ × Z₉) × (Z₉ × Z₉)).range := by
    rintro ⟨u, v⟩ huv
    have huv' : ((β₁ (Ψ u) : ↥C₁) : ↥M ⧸ CFSG.pCore 2 ↥M) * ((β₂ (Ψ v) : ↥C₂) : _) = 1 := huv
    have hx₁ : ((β₁ (Ψ u) : ↥C₁) : ↥M ⧸ CFSG.pCore 2 ↥M) = ((β₂ (Ψ v) : ↥C₂) : _)⁻¹ :=
      eq_inv_of_mul_eq_one_left huv'
    have hx₂ : ((β₂ (Ψ v) : ↥C₂) : ↥M ⧸ CFSG.pCore 2 ↥M) = ((β₁ (Ψ u) : ↥C₁) : _)⁻¹ :=
      eq_inv_of_mul_eq_one_right huv'
    have hu : Ψ u ∈ center S := hZ₁ _ (by
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      rw [hx₁]
      exact hc12 _ g.2 _ (C₂.inv_mem (β₂ (Ψ v)).2))
    have hv : Ψ v ∈ center S := hZ₂ _ (by
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      rw [hx₂]
      exact (hc12 _ (C₁.inv_mem (β₁ (Ψ u)).2) _ g.2).symm)
    obtain ⟨u', hu'⟩ := hΨ u hu
    obtain ⟨v', hv'⟩ := hΨ v hv
    refine ⟨(u', v'), ?_⟩
    rw [powMonoidHom_apply] at hu' hv' ⊢
    rw [Prod.pow_mk, hu', hv']
  obtain ⟨E, hEel, hEcard⟩ := uc22s217u38_exists_elemAbelian Φ hker
  have hE81 : Nat.card E = 3 ^ 4 := hEcard.trans uc22s217u38_card_ker_pow
  have hker2 : IsPGroup 2 π.ker := by
    show IsPGroup 2 (QuotientGroup.mk' (CFSG.pCore 2 ↥M)).ker
    rw [QuotientGroup.ker_mk']
    exact CFSG.pCore_isPGroup
  obtain ⟨Q, -, hQmap, hQdisj⟩ := UC6S846.exists_lift_pGroup π (QuotientGroup.mk'_surjective _)
    hker2 Nat.prime_three (by norm_num) E hEel.isPGroup
  have hQel : IsElemAbelian 3 Q :=
    UC6S846.isElemAbelian_of_disjoint_ker π Q hQdisj (by rw [hQmap]; exact hEel)
  have hQc : Nat.card Q = 3 ^ 4 := by
    rw [← UC6S846.card_map_of_disjoint_ker π Q hQdisj, hQmap, hE81]
  exact UC6S846.le_pRank' Nat.prime_three (E := Q.map M.subtype) (H := M)
    (Subgroup.map_subtype_le Q) (hQel.map _)
    (by rw [Subgroup.card_map_of_injective M.subtype_injective, hQc])

end Cover

end CFSG.LocalAnalysis.UniquenessCase.UC22
