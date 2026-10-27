module

public import CFSG.Foundations.Basic
import CFSG.OddTranspositions.PartFour.ThirteenList

public section

namespace CFSG.OddTranspositions.PartFour

open scoped commutatorElement

private theorem commutator_sup_le_of_le_center {G : Type*} [Group G] {H K Z : Subgroup G}
    (hZ : Z ≤ Subgroup.center G) : ⁅H ⊔ Z, K ⊔ Z⁆ ≤ ⁅H, K⁆ := by
  have : Z.Normal := Subgroup.normal_of_le_center hZ
  rw [Subgroup.commutator_le]
  intro x hx y hy
  rw [← SetLike.mem_coe, Subgroup.mul_normal] at hx hy
  obtain ⟨a, ha, z, hz, rfl⟩ := hx
  obtain ⟨b, hb, w, hw, rfl⟩ := hy
  have hz' := Subgroup.mem_center_iff.mp (hZ hz)
  have hw' := Subgroup.mem_center_iff.mp (hZ hw)
  have hc : ⁅a * z, b * w⁆ = ⁅a, b⁆ := by
    rw [commutatorElement_def, commutatorElement_def]
    calc a * z * (b * w) * (a * z)⁻¹ * (b * w)⁻¹
        = a * (z * b) * (w * z⁻¹) * a⁻¹ * w⁻¹ * b⁻¹ := by group
      _ = a * (b * z) * (z⁻¹ * w) * a⁻¹ * w⁻¹ * b⁻¹ := by
          rw [hz' b, ← Subgroup.mem_center_iff.mp (Subgroup.inv_mem _ (hZ hz)) w]
      _ = a * b * (w * a⁻¹) * w⁻¹ * b⁻¹ := by group
      _ = a * b * (a⁻¹ * w) * w⁻¹ * b⁻¹ := by rw [hw' a⁻¹]
      _ = a * b * a⁻¹ * b⁻¹ := by group
  rw [hc]
  exact Subgroup.commutator_mem_commutator ha hb

variable {X : Type} [Group X]

theorem derivedSeries_one_le_sup_center
    (hder : derivedSeries (X ⧸ Subgroup.center X) 1 = derivedSeries (X ⧸ Subgroup.center X) 2) :
    derivedSeries X 1 ≤ derivedSeries X 2 ⊔ Subgroup.center X := by
  have hs := QuotientGroup.mk'_surjective (Subgroup.center X)
  have h := congrArg (Subgroup.comap (QuotientGroup.mk' (Subgroup.center X))) hder
  rw [← map_derivedSeries_eq hs 1, ← map_derivedSeries_eq hs 2, Subgroup.comap_map_eq,
    Subgroup.comap_map_eq, QuotientGroup.ker_mk'] at h
  exact le_sup_left.trans h.le

theorem isPerfect_derivedSeries_two
    (hder : derivedSeries (X ⧸ Subgroup.center X) 1 = derivedSeries (X ⧸ Subgroup.center X) 2) :
    Group.IsPerfect ↥(derivedSeries X 2) := by
  rw [Subgroup.isPerfect_iff]
  refine le_antisymm (Subgroup.commutator_le_left _ _) ?_
  calc derivedSeries X 2 = ⁅derivedSeries X 1, derivedSeries X 1⁆ := derivedSeries_succ X 1
    _ ≤ ⁅derivedSeries X 2 ⊔ Subgroup.center X, derivedSeries X 2 ⊔ Subgroup.center X⁆ :=
        Subgroup.commutator_mono (derivedSeries_one_le_sup_center hder)
          (derivedSeries_one_le_sup_center hder)
    _ ≤ ⁅derivedSeries X 2, derivedSeries X 2⁆ := commutator_sup_le_of_le_center le_rfl

theorem center_eq_bot_of_inf_derivedSeries_two [Finite X] {s : X} (hs : s * s = 1)
    (hncl : Subgroup.normalClosure ({s} : Set X) = ⊤) (hZ : Odd (Nat.card (Subgroup.center X)))
    (hder : derivedSeries (X ⧸ Subgroup.center X) 1 = derivedSeries (X ⧸ Subgroup.center X) 2)
    (hY : derivedSeries X 2 ⊓ Subgroup.center X = ⊥) : Subgroup.center X = ⊥ := by
  have hgen : Subgroup.closure {x : X | IsConj s x} = ⊤ := by
    rw [closure_setOf_isConj_eq_normalClosure]
    exact hncl
  have hsq : ∀ x ∈ {x : X | IsConj s x}, x ^ 2 = 1 := fun x hx => by
    obtain ⟨c, rfl⟩ := isConj_iff.mp hx
    calc (c * s * c⁻¹) ^ 2 = c * (s * s) * c⁻¹ := by rw [pow_two]; group
      _ = 1 := by rw [hs]; group
  have hZX' : Subgroup.center X ≤ commutator X := fun z hz =>
    CFSG.ComponentClassification.AschbacherStrongEmbedding.mem_commutator_of_odd_order hgen hsq
      (Odd.of_dvd_nat hZ (by rw [← Subgroup.orderOf_mk z hz]; exact orderOf_dvd_natCard _))
  have hX's : commutator X ⊔ Subgroup.zpowers s = ⊤ := by
    have : (commutator X ⊔ Subgroup.zpowers s).Normal :=
      Subgroup.Normal.of_commutator_le _ le_sup_left
    refine eq_top_iff.mpr ?_
    rw [← hncl]
    exact Subgroup.normalClosure_le_normal
      (Set.singleton_subset_iff.mpr (Subgroup.mem_sup_right (Subgroup.mem_zpowers s)))
  have hH : IsMulCommutative ↥(Subgroup.center X ⊔ Subgroup.zpowers s) := by
    rw [← Subgroup.le_centralizer_iff_isMulCommutative]
    refine sup_le (Subgroup.center_le_centralizer _) ?_
    rw [Subgroup.le_centralizer_iff]
    exact sup_le (Subgroup.center_le_centralizer _) (Subgroup.le_centralizer _)
  have hsup : derivedSeries X 2 ⊔ (Subgroup.center X ⊔ Subgroup.zpowers s) = ⊤ := by
    rw [eq_top_iff, ← hX's, ← sup_assoc, ← derivedSeries_one]
    exact sup_le_sup_right (derivedSeries_one_le_sup_center hder) _
  have hcomm : commutator X ≤ derivedSeries X 2 :=
    Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top hsup hH
  rw [eq_bot_iff, ← hY]
  exact le_inf (hZX'.trans hcomm) le_rfl

theorem isQuasisimple_of_map_eq_commutator {G : Type*} [Group G] {N : Subgroup G} [N.Normal]
    (hN : N ≤ Subgroup.center G) {C : Subgroup G} (hC : Group.IsPerfect ↥C)
    (hmap : C.map (QuotientGroup.mk' N) = commutator (G ⧸ N))
    (hS : IsSimpleGroup ↥(commutator (G ⧸ N)))
    (hnc : ∃ a b : ↥(commutator (G ⧸ N)), a * b ≠ b * a) :
    CFSG.IsQuasisimple ↥C ∧ Nonempty (↥C ⧸ Subgroup.center ↥C ≃* ↥(commutator (G ⧸ N))) := by
  let ψ : ↥C →* G ⧸ N := (QuotientGroup.mk' N).comp C.subtype
  have hrange : ψ.range = commutator (G ⧸ N) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype, hmap]
  have hZK : Subgroup.center ↥(commutator (G ⧸ N)) = ⊥ := by
    have := hS
    rcases Subgroup.Normal.eq_bot_or_eq_top (Subgroup.center ↥(commutator (G ⧸ N))) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnc
      exact hab (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a)
  have hker : Subgroup.center ↥C = ψ.ker := by
    refine le_antisymm (fun x hx => ?_) (fun x hx => ?_)
    · rw [MonoidHom.mem_ker]
      have hxr : ψ x ∈ commutator (G ⧸ N) := hrange ▸ ⟨x, rfl⟩
      have hxK : (⟨ψ x, hxr⟩ : ↥(commutator (G ⧸ N))) ∈ Subgroup.center _ := by
        rw [Subgroup.mem_center_iff]
        intro b
        have hb : (b : G ⧸ N) ∈ ψ.range := hrange.symm ▸ b.2
        obtain ⟨y, hy⟩ := hb
        apply Subtype.ext
        show (b : G ⧸ N) * ψ x = ψ x * b
        rw [← hy, ← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hx y]
      rw [hZK, Subgroup.mem_bot] at hxK
      exact congrArg Subtype.val hxK
    · rw [MonoidHom.mem_ker] at hx
      have hxN : (x : G) ∈ N := (QuotientGroup.eq_one_iff _).mp hx
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (Subgroup.mem_center_iff.mp (hN hxN) y)
  let e : ↥C ⧸ Subgroup.center ↥C ≃* ↥(commutator (G ⧸ N)) :=
    (QuotientGroup.quotientMulEquivOfEq hker).trans
      ((QuotientGroup.quotientKerEquivRange ψ).trans (MulEquiv.subgroupCongr hrange))
  have := hS
  refine ⟨⟨hC, MulEquiv.isSimpleGroup e, ?_⟩, ⟨e⟩⟩
  obtain ⟨a, b, hab⟩ := hnc
  exact ⟨e.symm a, e.symm b, fun h => hab (by simpa using congrArg e h)⟩

theorem inf_center_eq_bot_of_isPGroup_two [Finite X] (hZ : Odd (Nat.card (Subgroup.center X)))
    {Y : Subgroup X} (hY : IsPGroup 2 ↥(Subgroup.center ↥Y)) : Y ⊓ Subgroup.center X = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  obtain ⟨hzY, hzZ⟩ := Subgroup.mem_inf.mp hz
  rw [Subgroup.mem_bot]
  have hzc : (⟨z, hzY⟩ : ↥Y) ∈ Subgroup.center ↥Y :=
    Subgroup.mem_center_iff.mpr fun y => Subtype.ext (Subgroup.mem_center_iff.mp hzZ y)
  obtain ⟨k, hk⟩ := hY ⟨⟨z, hzY⟩, hzc⟩
  have h1 : orderOf z ∣ 2 ^ k := by
    apply orderOf_dvd_of_pow_eq_one
    have := congrArg (fun g : ↥(Subgroup.center ↥Y) => ((g : ↥Y) : X)) hk
    simpa using this
  have h2 : orderOf z ∣ Nat.card (Subgroup.center X) := by
    rw [← Subgroup.orderOf_mk z hzZ]
    exact orderOf_dvd_natCard _
  have hcop : Nat.Coprime (2 ^ k) (Nat.card (Subgroup.center X)) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hZ)
  exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 hcop) h2)

end CFSG.OddTranspositions.PartFour
