module

public import CFSG.Timmesfeld.Bridge.Asc72Triangle

public section

namespace CFSG.Timmesfeld.Bridge.Asc72

open CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity CFSG.Timmesfeld.Bridge

variable {G : Type*} [Group G] {D : Set G}

@[expose] def centSet (D : Set G) (z : G) : Set G := {d | d ∈ D ∧ Commute d z}

@[expose] def localGroup (D : Set G) (z : G) : Subgroup G := Subgroup.closure (centSet D z)

@[expose] def localSet (D : Set G) (z : G) : Set (localGroup D z) :=
  ((↑) : localGroup D z → G) ⁻¹' centSet D z

theorem reach_mono {E : Set G} (hED : E ⊆ D) {x y : G} (h : Reach E x y) : Reach D x y := by
  induction h with
  | refl => exact reach_refl _
  | tail _ hbc ih => exact reach_trans ih (reach_of_commute (hED hbc.1) (hED hbc.2.1) hbc.2.2)

theorem reach_of_reach_subgroup (L : Subgroup G) {a b : L}
    (h : Reach (((↑) : L → G) ⁻¹' D) a b) : Reach D (a : G) (b : G) := by
  induction h with
  | refl => exact reach_refl _
  | tail _ hbc ih => exact reach_trans ih (reach_of_commute hbc.1 hbc.2.1 (hbc.2.2.map L.subtype))

theorem Setup.mul_mem_commutator (hS : Setup G D) {x y : G} (hx : x ∈ D) (hy : y ∈ D) :
    x * y ∈ commutator G := by
  rw [← Abelianization.ker_of, MonoidHom.mem_ker, map_mul, hS.abelianization_eq hy hx,
    ← map_mul, hS.oddT.mul_self_eq_one hx, map_one]

theorem commute_of_mem_localGroup {z g : G} (hg : g ∈ localGroup D z) : Commute g z := by
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact hx.2
  | one => exact Commute.one_left z
  | mul x y _ _ hx hy => exact hx.mul_left hy
  | inv x _ hx => exact hx.inv_left

theorem mem_localGroup_of_mem {z x : G} (hx : x ∈ centSet D z) : x ∈ localGroup D z :=
  Subgroup.subset_closure hx

section Triangle

variable {u w v : G} (hS : Setup G D) (htri : IsTriangle D u w v) {n : ℕ} (hn : Odd n)
  (hord : orderOf (u * v * w) = 2 * n) (huw : ¬ Reach D u w)
include hS htri hn hord huw

theorem thirdKind_z_not_mem : (u * v * w) ^ n ∉ D := by
  obtain ⟨-, -, hzu, -, hzw, -⟩ := htri.third_kind hS.oddT hS.normal hn hord
  intro hz
  exact huw (reach_trans (reach_of_commute htri.1 hz hzu.symm)
    (reach_of_commute hz htri.2.2.1 hzw))

omit huw in
theorem thirdKind_mem_centSet :
    u ∈ centSet D ((u * v * w) ^ n) ∧ v ∈ centSet D ((u * v * w) ^ n) ∧
      w ∈ centSet D ((u * v * w) ^ n) ∧
      u * v * (u * v * w) ^ n ∈ centSet D ((u * v * w) ^ n) := by
  obtain ⟨hzz, -, hzu, hzv, hzw, huvz⟩ := htri.third_kind hS.oddT hS.normal hn hord
  refine ⟨⟨htri.1, hzu.symm⟩, ⟨htri.2.1, hzv.symm⟩, ⟨htri.2.2.1, hzw.symm⟩, ⟨huvz, ?_⟩⟩
  exact ((hzu.symm.mul_left hzv.symm).mul_left (Commute.refl _))

theorem localSetup : Setup (localGroup D ((u * v * w) ^ n)) (localSet D ((u * v * w) ^ n)) := by
  set z := (u * v * w) ^ n with hz
  obtain ⟨hu, hv, hw, -⟩ := thirdKind_mem_centSet hS htri hn hord
  have huH : u ∈ localGroup D z := mem_localGroup_of_mem hu
  have hwH : w ∈ localGroup D z := mem_localGroup_of_mem hw
  have hconjH : ∀ {a b : G}, a ∈ centSet D z → b ∈ centSet D z → ¬ Commute a b →
      ∃ c ∈ localGroup D z, c * a * c⁻¹ = b := by
    intro a b ha hb hab
    obtain ⟨c, hc, hcab⟩ := hS.oddT.exists_conj ha.1 hb.1 hab
    refine ⟨c, ?_, hcab⟩
    have hle : Subgroup.closure ({a, b} : Set G) ≤ localGroup D z := by
      rw [Subgroup.closure_le]
      rintro x (rfl | rfl)
      · exact mem_localGroup_of_mem ha
      · exact mem_localGroup_of_mem hb
    exact hle hc
  have hwu : ¬ Commute u w := htri.2.2.2.2.2.1
  refine ⟨⟨⟨u, huH⟩, ?_⟩, ?_, ?_⟩
  · ext g
    constructor
    · intro hg
      by_cases hgu : Commute u (g : G)
      · have hgw : ¬ Commute w (g : G) := fun hgw =>
          huw (reach_trans (reach_of_commute htri.1 hg.1 hgu)
            (reach_of_commute hg.1 htri.2.2.1 hgw.symm))
        obtain ⟨c₁, hc₁, h₁⟩ := hconjH hu hw hwu
        obtain ⟨c₂, hc₂, h₂⟩ := hconjH hw hg hgw
        refine isConj_iff.mpr ⟨⟨c₂, hc₂⟩ * ⟨c₁, hc₁⟩, Subtype.ext ?_⟩
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev]
        rw [← h₂, ← h₁]
        group
      · obtain ⟨c, hc, h⟩ := hconjH hu hg hgu
        exact isConj_iff.mpr ⟨⟨c, hc⟩, Subtype.ext (by simpa using h)⟩
    · intro hg
      obtain ⟨c, rfl⟩ := isConj_iff.mp hg
      have hcz := commute_of_mem_localGroup c.2
      show ((c : G) * u * (c : G)⁻¹) ∈ centSet D z
      exact ⟨hS.normal c u htri.1, (hcz.mul_left hu.2).mul_left hcz.inv_left⟩
  · exact (hS.oddT.mono fun x hx => hx.1).preimage _
  · exact Subgroup.closure_closure_coe_preimage

theorem localSet_disconnected : Disconnected (localSet D ((u * v * w) ^ n)) := by
  obtain ⟨hu, -, hw, -⟩ := thirdKind_mem_centSet hS htri hn hord
  refine ⟨⟨u, mem_localGroup_of_mem hu⟩, hu, ⟨w, mem_localGroup_of_mem hw⟩, hw, fun h => huw ?_⟩
  exact reach_mono (fun x hx => hx.1) (reach_of_reach_subgroup _ h)

end Triangle

theorem isSolvable_sup_of_normal {K : Type*} [Group K] {A B : Subgroup K} [A.Normal] [B.Normal]
    (hA : Group.IsSolvable A) (hB : Group.IsSolvable B) :
    Group.IsSolvable (A ⊔ B : Subgroup K) := by
  set L := A ⊔ B
  set M := A.subgroupOf L
  have hM : M.Normal := inferInstance
  have hMsol : Group.IsSolvable M := by
    refine Group.isSolvable_of_isSolvable_injective (f := (Subgroup.subgroupOfEquivOfLe
      (le_sup_left : A ≤ L)).toMonoidHom) ?_
    exact (Subgroup.subgroupOfEquivOfLe (le_sup_left : A ≤ L)).injective
  let f : B →* L ⧸ M := (QuotientGroup.mk' M).comp (Subgroup.inclusion (le_sup_right : B ≤ L))
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨⟨x, hx⟩, rfl⟩ := QuotientGroup.mk'_surjective M y
    obtain ⟨a, ha, b, hb, rfl⟩ := (Subgroup.mem_sup_of_normal_left (s := A) (t := B)).mp hx
    refine ⟨⟨b, hb⟩, ?_⟩
    simp only [f, MonoidHom.comp_apply]
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
      Subgroup.mem_subgroupOf]
    simpa [mul_assoc] using ‹A.Normal›.conj_mem' a ha b
  have : Group.IsSolvable (L ⧸ M) := Group.isSolvable_of_surjective hf
  exact Group.isSolvable_of_ker_le_range M.subtype (QuotientGroup.mk' M) (by
    rw [QuotientGroup.ker_mk', Subgroup.range_subtype])

theorem exists_solvableRadical (K : Type*) [Group K] [Finite K] :
    ∃ R : Subgroup K, R.Normal ∧ Group.IsSolvable R ∧
      ∀ N : Subgroup K, N.Normal → Group.IsSolvable N → N ≤ R := by
  classical
  obtain ⟨R, -, hR⟩ := Finite.exists_le_maximal
    (p := fun N : Subgroup K => N.Normal ∧ Group.IsSolvable N) (a := ⊥)
    ⟨inferInstance, inferInstance⟩
  refine ⟨R, hR.1.1, hR.1.2, fun N hN hNs => ?_⟩
  have : R.Normal := hR.1.1
  have : N.Normal := hN
  have h := hR.eq_of_le ⟨inferInstance, isSolvable_sup_of_normal hR.1.2 hNs⟩ le_sup_left
  rw [h]
  exact le_sup_right

theorem eq_bot_of_solvableRadical {K : Type*} [Group K] {R : Subgroup K} [R.Normal]
    (hR : Group.IsSolvable R) (hall : ∀ N : Subgroup K, N.Normal → Group.IsSolvable N → N ≤ R)
    (N : Subgroup (K ⧸ R)) (hN : N.Normal) (hNs : Group.IsSolvable N) : N = ⊥ := by
  set P := N.comap (QuotientGroup.mk' R)
  have hPn : P.Normal := Subgroup.Normal.comap hN _
  have hRP : R ≤ P := fun x hx => by
    show QuotientGroup.mk' R x ∈ N
    have h1 : QuotientGroup.mk' R x = 1 := (QuotientGroup.eq_one_iff x).mpr hx
    rw [h1]
    exact N.one_mem
  have hPs : Group.IsSolvable P := by
    let g : P →* N := ((QuotientGroup.mk' R).comp P.subtype).codRestrict N (fun x => x.2)
    let f : R →* P := Subgroup.inclusion hRP
    refine Group.isSolvable_of_ker_le_range f g ?_
    intro x hx
    have : ((x : K)) ∈ R := by
      have h1 := congrArg Subtype.val hx
      simp only [g, OneMemClass.coe_one] at h1
      exact (QuotientGroup.eq_one_iff _).mp h1
    exact ⟨⟨x, this⟩, rfl⟩
  have hPR := hall P hPn hPs
  rw [eq_bot_iff]
  intro y hy
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective R y
  have hx : x ∈ R := hPR hy
  rw [Subgroup.mem_bot]
  exact (QuotientGroup.eq_one_iff x).mpr hx

section Quotient

variable {G : Type} [Group G] {D : Set G} {u w v : G} (hS : Setup G D)
  (htri : IsTriangle D u w v) {n : ℕ} (hn : Odd n) (hord : orderOf (u * v * w) = 2 * n)
  (huw : ¬ Reach D u w)
include hS htri hn hord huw

omit huw in
theorem thirdKind_z_mem_localGroup : (u * v * w) ^ n ∈ localGroup D ((u * v * w) ^ n) := by
  obtain ⟨hu, hv, -, huvz⟩ := thirdKind_mem_centSet hS htri hn hord
  have h := (localGroup D _).mul_mem ((localGroup D _).inv_mem
    ((localGroup D _).mul_mem (mem_localGroup_of_mem hu) (mem_localGroup_of_mem hv)))
    (mem_localGroup_of_mem huvz)
  rwa [inv_mul_cancel_left] at h

end Quotient

end CFSG.Timmesfeld.Bridge.Asc72
