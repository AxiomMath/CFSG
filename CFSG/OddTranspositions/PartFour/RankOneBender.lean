module

public import CFSG.OddTranspositions.PartFour.RootGroupBender
import CFSG.Timmesfeld.Bridge.Asc72Bender
import CFSG.ThirdParty.BrauerInduction.Background.Group.Conjugacy
public import CFSG.Adapters.QiuzhenLegacy.BenderSuzuki.BenderLinearBorel

public section

namespace CFSG.OddTranspositions.PartFour

open CFSG.BenderSuzuki CFSG.Open

section Finite

variable {X : Type} [Group X]

private theorem rankOneBender_orderOf_eq_two_of_mem {s : X} (hs : orderOf s = 2) {E : Set X}
    (hE : E = {y | IsConj s y}) {y : X} (hy : y ∈ E) : orderOf y = 2 := by
  rw [hE] at hy
  change IsConj s y at hy
  exact (IsConj.orderOf_eq hy).symm.trans hs

private theorem rankOneBender_mul_self_eq_one_of_orderOf_eq_two {y : X}
    (hy : orderOf y = 2) : y * y = 1 := by
  rw [← pow_two, ← hy, pow_orderOf_eq_one]

variable [Finite X]

theorem Vmem_eq_setOf_commute_of_isBenderGroup (hX : IsBenderGroup X) {s : X}
    (hs : orderOf s = 2) {E : Set X} (hE : E = {y | IsConj s y}) {x : X} (hx : x ∈ E) :
    Vmem E x = {z | z ∈ E ∧ Commute z x} := by
  subst hE
  refine Set.Subset.antisymm (fun v hv => ?_) (fun z hz => ?_)
  · have hvE : v ∈ {y | IsConj s y} := (mem_Vmem.mp hv).1
    have hvperp : v ∈ perpMem {y | IsConj s y} v := mem_perpMem_self hvE
    rw [(mem_Vmem.mp hv).2] at hvperp
    exact ⟨hvE, (mem_perpMem.mp hvperp).2⟩
  · exact mem_Vmem_of_commute_of_isBenderGroup hX hs hx hz.1 hz.2.symm

private theorem rankOneBender_sq_eq_one_of_mem_insert_Vmem {s : X} (hs : orderOf s = 2)
    {E : Set X} (hE : E = {y | IsConj s y}) {x y : X} (hy : y ∈ insert 1 (Vmem E x)) :
    y * y = 1 := by
  rcases hy with rfl | hy
  · simp
  · exact rankOneBender_mul_self_eq_one_of_orderOf_eq_two
      (rankOneBender_orderOf_eq_two_of_mem hs hE (mem_Vmem.mp hy).1)

private theorem rankOneBender_coe_eq_center_map (hX : IsBenderGroup X) {s : X}
    (hs : orderOf s = 2) {x : X} (hx : x ∈ {y | IsConj s y}) {R : Subgroup X}
    (hR : (R : Set X) = insert 1 (Vmem {y | IsConj s y} x)) (Q : Sylow 2 X)
    (hRQ : R ≤ (Q : Subgroup X)) :
    (R : Set X) = ((Subgroup.center (Q : Subgroup X)).map (Q : Subgroup X).subtype : Set X) := by
  refine Set.Subset.antisymm (fun y hy => ?_) (fun y hy => ?_)
  · have hyQ : y ∈ (Q : Subgroup X) := hRQ hy
    have hy2 : y * y = 1 :=
      rankOneBender_sq_eq_one_of_mem_insert_Vmem hs rfl (hR ▸ hy)
    have hcomm : ∀ z ∈ (Q : Subgroup X), Commute y z :=
      CFSG.Timmesfeld.Bridge.Asc72.IsBenderGroup.commute_of_mul_self_eq_one hX Q hyQ hy2
    refine Subgroup.mem_map.mpr ⟨⟨y, hyQ⟩, Subgroup.mem_center_iff.mpr (fun z => ?_), rfl⟩
    exact Subtype.ext (hcomm z z.2).symm.eq
  · obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hy
    have hz2 : (z : X) * (z : X) = 1 :=
      CFSG.Timmesfeld.Bridge.Asc72.IsBenderGroup.mul_self_eq_one_of_commute hX Q z.2
        fun u hu => (congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨u, hu⟩)).symm
    rw [hR]
    by_cases hz1 : (z : X) = 1
    · show (z : X) ∈ insert (1 : X) (Vmem {y | IsConj s y} x)
      rw [hz1]
      exact Set.mem_insert _ _
    · refine Set.mem_insert_of_mem _ ?_
      have hzord : orderOf (z : X) = 2 :=
        orderOf_eq_prime (by rw [pow_two]; exact hz2) hz1
      have hzE : (z : X) ∈ {y | IsConj s y} :=
        CFSG.Timmesfeld.Bridge.Asc72.IsBenderGroup.isConj_of_orderOf_eq_two hX hs hzord
      have hxR : x ∈ (R : Set X) := by
        rw [hR]
        exact Set.mem_insert_of_mem _ (mem_Vmem_self hx)
      have hcomm : Commute (z : X) x :=
        CFSG.Timmesfeld.Bridge.Asc72.IsBenderGroup.commute_of_mul_self_eq_one hX Q z.2 hz2 x
          (hRQ hxR)
      exact mem_Vmem_of_commute_of_isBenderGroup hX hs hx hzE hcomm.symm

theorem ncard_Vmem_eq_of_fusionBenderBorel (hX : IsBenderGroup X) {s : X} (hs : orderOf s = 2)
    {E : Set X} (hE : E = {y | IsConj s y}) {q k : ℕ} (hB : fusionBenderBorel X q k) {x : X}
    (hx : x ∈ E) : (Vmem E x).ncard = q - 1 := by
  subst hE
  obtain ⟨R, hR⟩ := exists_subgroup_eq_insert_Vmem_of_isBenderGroup hX hs hx
  have hsq : ∀ y ∈ (R : Set X), y * y = 1 := fun y hy =>
    rankOneBender_sq_eq_one_of_mem_insert_Vmem hs rfl (hR ▸ hy)
  have h2 : IsPGroup 2 R := by
    rw [isPGroup_iff_exists_pow_pow_eq_one]
    refine ⟨1, fun y => ?_⟩
    rw [pow_one, pow_two]
    exact Subtype.ext (hsq (y : X) y.2)
  obtain ⟨Q, hRQ⟩ := h2.exists_le_sylow
  have hRcard : (R : Set X).ncard = q := by
    rw [rankOneBender_coe_eq_center_map hX hs hx hR Q hRQ, ← Nat.card_coe_set_eq]
    change Nat.card ↥((Subgroup.center (Q : Subgroup X)).map (Q : Subgroup X).subtype) = q
    rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _), (hB Q).2.2.2.1]
  have h1 : (1 : X) ∉ Vmem {y | IsConj s y} x := by
    intro h
    have hord := IsConj.orderOf_eq (mem_Vmem.mp h).1
    rw [hs, orderOf_one] at hord
    omega
  have hins : (insert (1 : X) (Vmem {y | IsConj s y} x)).ncard =
      (Vmem {y | IsConj s y} x).ncard + 1 :=
    Set.ncard_insert_of_notMem h1 (Set.toFinite _)
  have hcount : (Vmem {y | IsConj s y} x).ncard + 1 = q := by
    rw [← hins, ← hR]
    exact hRcard
  omega

theorem ncard_image_Vmem_eq_of_fusionBenderBorel
    (hX : IsBenderGroup X) {s : X} (hs : orderOf s = 2) {E : Set X} (hE : E = {y | IsConj s y})
    {q k : ℕ} (hB : fusionBenderBorel X q k) : (Vmem E '' E).ncard = q ^ k + 1 := by
  subst hE
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S⟩ : Nonempty (Sylow 2 X) := inferInstance
  rw [ncard_image_Vmem_of_isBenderGroup hX hs S, (hB S).2.2.2.2]

theorem fusionBenderBorel_of_mulEquiv_psl2Model {f : ℕ} (hf : 2 ≤ f) (e : X ≃* PSL2Model f) :
    fusionBenderBorel X (2 ^ f) 1 := by
  have : Finite (PSL2Model f) := Finite.of_surjective e e.surjective
  exact (bender_psl2_borel_full f hf).map_mulEquiv e.symm

end Finite

variable {X : Type} [Group X]

private theorem rankOneBender_image_Vmem_conj (E : Set X) (g u : X) :
    MulAut.conj g '' Vmem E u = Vmem (MulAut.conj g '' E) (MulAut.conj g u) := by
  have hperp : ∀ v : X, perpMem (MulAut.conj g '' E) (MulAut.conj g v) =
      MulAut.conj g '' perpMem E v := by
    intro v
    ext w
    constructor
    · rintro ⟨hwE, hwc⟩
      obtain ⟨z, hzE, rfl⟩ := hwE
      have h := Commute.map hwc (MulAut.conj g).symm
      rw [MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply] at h
      exact ⟨z, mem_perpMem.mpr ⟨hzE, h⟩, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨⟨z, hz.1, rfl⟩, Commute.map hz.2 (MulAut.conj g)⟩
  ext w
  constructor
  · rintro ⟨v, hv, rfl⟩
    have hv' := mem_Vmem.mp hv
    refine mem_Vmem.mpr ⟨⟨v, hv'.1, rfl⟩, ?_⟩
    rw [hperp v, hperp u, hv'.2]
  · intro hw
    obtain ⟨hwE, hwp⟩ := mem_Vmem.mp hw
    obtain ⟨v, hvE, rfl⟩ := hwE
    have hv : v ∈ Vmem E u := by
      refine mem_Vmem.mpr ⟨hvE, ?_⟩
      rw [hperp v, hperp u] at hwp
      exact (Set.image_injective (f := MulAut.conj g)).mpr (MulAut.conj g).injective hwp
    exact ⟨v, hv, rfl⟩

theorem rootLiftClass_of_closure_insert_eq_top {s : X} {E : Set X} (hE : E = {y | IsConj s y})
    (hgen : ∀ x ∈ E, ∀ y ∈ E, ¬ Commute x y →
      Subgroup.closure (insert y {z | z ∈ E ∧ Commute z x}) = ⊤)
    (hnc : ∃ x ∈ E, ∃ y ∈ E, ¬ Commute x y) :
    Subgroup.closure E = ⊤ ∧ (∀ x ∈ E, ∀ y ∈ E, y * x * y⁻¹ ∈ E) ∧
      (∀ x ∈ E, ∀ y ∈ E, ¬ Commute x y →
        Subgroup.closure (insert y {z | z ∈ E ∧ Commute z x}) = Subgroup.closure E) ∧
      ∀ x ∈ E, ∀ y ∈ E, ∃ g ∈ Subgroup.closure E, g * x * g⁻¹ = y := by
  obtain ⟨x, hx, y, hy, hnc⟩ := hnc
  have hsub : insert y {z | z ∈ E ∧ Commute z x} ⊆ E := by
    rintro w (rfl | hw)
    · exact hy
    · exact hw.1
  have htop : Subgroup.closure E = ⊤ := by
    have h := Subgroup.closure_mono hsub
    rw [hgen x hx y hy hnc] at h
    exact top_le_iff.mp h
  refine ⟨htop, ?_, ?_, ?_⟩
  · intro x hx y hy
    rw [hE] at hx ⊢
    exact hx.trans (isConj_iff.mpr ⟨y, rfl⟩)
  · intro x hx y hy h
    rw [hgen x hx y hy h, htop]
  · intro x hx y hy
    rw [hE] at hx hy
    obtain ⟨g, hg⟩ := isConj_iff.mp (hx.symm.trans hy)
    refine ⟨g, ?_, hg⟩
    rw [htop]
    exact Subgroup.mem_top g

private theorem rankOneBender_not_commute_of_mem_class {s : X} (hs : orderOf s = 2)
    {E : Set X} (hE : E = {y | IsConj s y}) {n : ℕ} (hn : 0 < n) {x₀ y₀ : X}
    (hx₀E : x₀ ∈ E) (hy₀E : y₀ ∈ E) (hord : orderOf (x₀ * y₀) = 2 ^ n + 1) :
    ¬ Commute x₀ y₀ := by
  have hx : x₀ * x₀ = 1 :=
    rankOneBender_mul_self_eq_one_of_orderOf_eq_two
      (rankOneBender_orderOf_eq_two_of_mem hs hE hx₀E)
  have hy : y₀ * y₀ = 1 :=
    rankOneBender_mul_self_eq_one_of_orderOf_eq_two
      (rankOneBender_orderOf_eq_two_of_mem hs hE hy₀E)
  intro hc
  have hsq : (x₀ * y₀) ^ 2 = 1 := by
    rw [Commute.mul_pow hc 2, pow_two, pow_two, hx, hy, mul_one]
  have hle : orderOf (x₀ * y₀) ≤ 2 :=
    Nat.le_of_dvd (by norm_num) (orderOf_dvd_iff_pow_eq_one.mpr hsq)
  rw [hord] at hle
  have h2n : 2 ≤ 2 ^ n := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

private theorem rankOneBender_conj_class_data {s : X} {E : Set X}
    (hE : E = {y | IsConj s y}) (g : X) :
    (∀ y, y ∈ E ↔ MulAut.conj g y ∈ E) ∧ MulAut.conj g '' E = E ∧
      ∀ u, MulAut.conj g '' Vmem E u = Vmem E (MulAut.conj g u) := by
  have hφE : ∀ y, y ∈ E ↔ MulAut.conj g y ∈ E := by
    intro y
    have h1 : y ∈ E ↔ IsConj s y := by simp [hE]
    have h2 : MulAut.conj g y ∈ E ↔ IsConj s (MulAut.conj g y) := by simp [hE]
    rw [h1, h2]
    constructor
    · intro hy
      have hc : IsConj s (MulAut.conj g s) :=
        isConj_iff.mpr ⟨g, by rw [MulAut.conj_apply]⟩
      exact hc.trans ((MulAut.conj g).toMonoidHom.map_isConj hy)
    · intro hy
      have hc : IsConj s ((MulAut.conj g).symm s) :=
        isConj_iff.mpr ⟨g⁻¹, by rw [MulAut.conj_symm_apply, inv_inv]⟩
      have h2 : IsConj ((MulAut.conj g).symm s) ((MulAut.conj g).symm (MulAut.conj g y)) :=
        (MulAut.conj g).symm.toMonoidHom.map_isConj hy
      rw [MulEquiv.symm_apply_apply] at h2
      exact hc.trans h2
  have hφE' : MulAut.conj g '' E = E := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact (hφE z).mp hz
    · intro hy
      refine ⟨(MulAut.conj g).symm y, (hφE _).mpr ?_, ?_⟩
      · rw [MulEquiv.apply_symm_apply]
        exact hy
      · rw [MulEquiv.apply_symm_apply]
  exact ⟨hφE, hφE', fun u => by rw [rankOneBender_image_Vmem_conj E g u, hφE']⟩

private theorem rankOneBender_Vmem_subset_of_generate {E : Set X} {K0 : Subgroup X}
    (hgen : ∀ x ∈ E, x ∈ K0 → ∀ y ∈ E, y ∈ K0 → ¬ Commute x y →
      Subgroup.closure (insert y (Vmem E x)) = K0)
    {x y : X} (hxE : x ∈ E) (hxK : x ∈ K0) (hyE : y ∈ E) (hyK : y ∈ K0)
    (hxy : ¬ Commute x y) : Vmem E x ⊆ K0 := by
  intro v hv
  have hmem : v ∈ Subgroup.closure (insert y (Vmem E x)) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ hv)
  rwa [hgen x hxE hxK y hyE hyK hxy] at hmem

private theorem rankOneBender_conj_Vmem_subset {E : Set X} {K0 : Subgroup X} {g x₀ x : X}
    (hφx₀ : MulAut.conj g x₀ = x)
    (hφE : ∀ y, y ∈ E ↔ MulAut.conj g y ∈ E)
    (hV : ∀ u, MulAut.conj g '' Vmem E u = Vmem E (MulAut.conj g u))
    (hVx₀ : Vmem E x₀ ⊆ K0) :
    Vmem E x ⊆ {y | y ∈ E ∧ y ∈ K0.map (MulAut.conj g).toMonoidHom} := by
  intro v hv
  have hv' : v ∈ MulAut.conj g '' Vmem E x₀ := by
    rw [hV x₀, hφx₀]
    exact hv
  obtain ⟨z, hzV, hzv⟩ := hv'
  rw [← hzv]
  exact ⟨(hφE z).mp hzV.1, Subgroup.mem_map.mpr ⟨z, hVx₀ hzV, rfl⟩⟩

private theorem rankOneBender_conj_mem_not_commute {E : Set X} {K0 : Subgroup X}
    {g x₀ y₀ x : X} (hφx₀ : MulAut.conj g x₀ = x)
    (hφE : ∀ y, y ∈ E ↔ MulAut.conj g y ∈ E) (hx₀E : x₀ ∈ E) (hy₀E : y₀ ∈ E)
    (hy₀K : y₀ ∈ K0) (hnc₀ : ¬ Commute x₀ y₀) :
    MulAut.conj g y₀ ∈ {y | y ∈ E ∧ y ∈ K0.map (MulAut.conj g).toMonoidHom} ∧
      ¬ Commute (MulAut.conj g y₀) x := by
  have hwS : MulAut.conj g y₀ ∈ {y | y ∈ E ∧ y ∈ K0.map (MulAut.conj g).toMonoidHom} :=
    ⟨(hφE y₀).mp hy₀E, Subgroup.mem_map.mpr ⟨y₀, hy₀K, rfl⟩⟩
  refine ⟨hwS, ?_⟩
  rw [← hφx₀]
  intro h
  have h' : Commute y₀ x₀ := by
    have hc := Commute.map h (MulAut.conj g).symm
    rw [MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply] at hc
    exact hc
  exact hnc₀ h'.symm

private theorem rankOneBender_conj_mem_inter {s : X} {E : Set X} (hE : E = {y | IsConj s y})
    {K : Subgroup X} {y z : X} (hyE : y ∈ E) (hyK : y ∈ K) (hzK : z ∈ K) :
    z * y * z⁻¹ ∈ E ∧ z * y * z⁻¹ ∈ K := by
  refine ⟨?_, K.mul_mem (K.mul_mem hzK hyK) (K.inv_mem hzK)⟩
  have hyconj : IsConj y (z * y * z⁻¹) := isConj_iff.mpr ⟨z, rfl⟩
  rw [hE] at hyE ⊢
  exact hyE.trans hyconj

private theorem rankOneBender_map_closure_generate {E : Set X} {K0 : Subgroup X}
    (hgen : ∀ x ∈ E, x ∈ K0 → ∀ y ∈ E, y ∈ K0 → ¬ Commute x y →
      Subgroup.closure (insert y (Vmem E x)) = K0)
    {g x₀ y₀ : X} (hx₀E : x₀ ∈ E) (hx₀K : x₀ ∈ K0) (hy₀E : y₀ ∈ E) (hy₀K : y₀ ∈ K0)
    (hnc₀ : ¬ Commute x₀ y₀)
    (hV : ∀ u, MulAut.conj g '' Vmem E u = Vmem E (MulAut.conj g u)) :
    Subgroup.closure (insert (MulAut.conj g y₀) (Vmem E (MulAut.conj g x₀))) =
      K0.map (MulAut.conj g).toMonoidHom := by
  have h := MonoidHom.map_closure (MulAut.conj g).toMonoidHom (insert y₀ (Vmem E x₀))
  rw [hgen x₀ hx₀E hx₀K y₀ hy₀E hy₀K hnc₀, Set.image_insert_eq] at h
  change Subgroup.map (MulAut.conj g).toMonoidHom K0 =
    Subgroup.closure (insert (MulAut.conj g y₀) (MulAut.conj g '' Vmem E x₀)) at h
  rw [hV x₀] at h
  exact h.symm

private theorem rankOneBender_closure_inter_eq {E : Set X} {K : Subgroup X} {S : Set X}
    (hS : S = {y | y ∈ E ∧ y ∈ K}) {A : Set X} (hA : Subgroup.closure A = K) (hle : A ⊆ S) :
    Subgroup.closure S = K := by
  refine le_antisymm (Subgroup.closure_le K |>.mpr (fun y hy => ?_)) ?_
  · rw [hS] at hy
    exact hy.2
  · rw [← hA]
    exact Subgroup.closure_mono hle

private theorem rankOneBender_closure_inter_conj {E : Set X} {K0 : Subgroup X}
    (hgen : ∀ x ∈ E, x ∈ K0 → ∀ y ∈ E, y ∈ K0 → ¬ Commute x y →
      Subgroup.closure (insert y (Vmem E x)) = K0)
    {g x₀ y₀ x : X} (hx₀E : x₀ ∈ E) (hx₀K : x₀ ∈ K0) (hy₀E : y₀ ∈ E) (hy₀K : y₀ ∈ K0)
    (hnc₀ : ¬ Commute x₀ y₀) (hφx₀ : MulAut.conj g x₀ = x)
    (hV : ∀ u, MulAut.conj g '' Vmem E u = Vmem E (MulAut.conj g u))
    (hVx : Vmem E x ⊆ {y | y ∈ E ∧ y ∈ K0.map (MulAut.conj g).toMonoidHom})
    (hwS : MulAut.conj g y₀ ∈ {y | y ∈ E ∧ y ∈ K0.map (MulAut.conj g).toMonoidHom}) :
    Subgroup.closure {y | y ∈ E ∧ y ∈ K0.map (MulAut.conj g).toMonoidHom} =
      K0.map (MulAut.conj g).toMonoidHom := by
  have hgenK := rankOneBender_map_closure_generate hgen hx₀E hx₀K hy₀E hy₀K hnc₀ hV
  have hle : insert (MulAut.conj g y₀) (Vmem E (MulAut.conj g x₀)) ⊆
      {y | y ∈ E ∧ y ∈ K0.map (MulAut.conj g).toMonoidHom} := by
    intro w hw
    rcases hw with rfl | hw
    · exact hwS
    · exact hVx (by rwa [hφx₀] at hw)
  exact rankOneBender_closure_inter_eq rfl hgenK hle

private theorem rankOneBender_exists_preimage {E : Set X} {K0 : Subgroup X} {g : X}
    (hφE : ∀ y, y ∈ E ↔ MulAut.conj g y ∈ E)
    {S : Set X} (hS : S = {w | w ∈ E ∧ w ∈ K0.map (MulAut.conj g).toMonoidHom})
    {y : X} (hyS : y ∈ S) :
    ∃ y' ∈ K0, y' ∈ E ∧ MulAut.conj g y' = y := by
  rw [hS] at hyS
  obtain ⟨y', hy'K0, hy'eq⟩ := Subgroup.mem_map.mp hyS.2
  refine ⟨y', hy'K0, ?_, hy'eq⟩
  exact (hφE y').mpr (by
    change (MulAut.conj g).toMonoidHom y' ∈ E
    rw [hy'eq]
    exact hyS.1)

private theorem rankOneBender_closure_insert_Vmem {E : Set X} {K0 : Subgroup X}
    (hgen : ∀ x ∈ E, x ∈ K0 → ∀ y ∈ E, y ∈ K0 → ¬ Commute x y →
      Subgroup.closure (insert y (Vmem E x)) = K0)
    {g y y' z z' : X} (hV : ∀ u, MulAut.conj g '' Vmem E u = Vmem E (MulAut.conj g u))
    (hy'E : y' ∈ E) (hy'K0 : y' ∈ K0) (hz'E : z' ∈ E) (hz'K0 : z' ∈ K0)
    (hy'eq : MulAut.conj g y' = y) (hz'eq : MulAut.conj g z' = z)
    (hync' : ¬ Commute y' z') :
    Subgroup.closure (insert z (Vmem E y)) = K0.map (MulAut.conj g).toMonoidHom := by
  have hK' : Subgroup.closure (insert z' (Vmem E y')) = K0 :=
    hgen y' hy'E hy'K0 z' hz'E hz'K0 hync'
  have hmap : Subgroup.map (MulAut.conj g).toMonoidHom
      (Subgroup.closure (insert z' (Vmem E y'))) =
      Subgroup.closure (insert z (Vmem E y)) := by
    rw [MonoidHom.map_closure, Set.image_insert_eq]
    rw [show (MulAut.conj g).toMonoidHom '' Vmem E y' =
        Vmem E ((MulAut.conj g).toMonoidHom y') from by
      change MulAut.conj g '' Vmem E y' = Vmem E (MulAut.conj g y')
      rw [hV y']]
    change Subgroup.closure
      (insert ((MulAut.conj g) z') (Vmem E ((MulAut.conj g) y'))) =
      Subgroup.closure (insert z (Vmem E y))
    rw [hy'eq, hz'eq]
  rw [← hmap, hK']

private theorem rankOneBender_closure_insert_inter {E : Set X} {K0 : Subgroup X} {g y z : X}
    {S : Set X} (hS : S = {w | w ∈ E ∧ w ∈ K0.map (MulAut.conj g).toMonoidHom})
    (hzS : z ∈ S) (hSclosure : Subgroup.closure S = K0.map (MulAut.conj g).toMonoidHom)
    (hgenKpair : Subgroup.closure (insert z (Vmem E y)) =
      K0.map (MulAut.conj g).toMonoidHom) :
    Subgroup.closure (insert z {w | w ∈ S ∧ Commute w y}) = Subgroup.closure S := by
  have hVsub : Vmem E y ⊆ {w | w ∈ S ∧ Commute w y} := by
    intro w hw
    have hwK : w ∈ K0.map (MulAut.conj g).toMonoidHom := by
      rw [← hgenKpair]
      exact Subgroup.subset_closure (Set.mem_insert_of_mem _ hw)
    have hself : w ∈ perpMem E w := mem_perpMem_self hw.1
    rw [(mem_Vmem.mp hw).2] at hself
    exact ⟨by rw [hS]; exact ⟨hw.1, hwK⟩, (mem_perpMem.mp hself).2⟩
  have hins : insert z (Vmem E y) ⊆ insert z {w | w ∈ S ∧ Commute w y} := by
    intro w hw
    rcases hw with rfl | hw
    · exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ (hVsub hw)
  have hinsS : insert z {w | w ∈ S ∧ Commute w y} ⊆ S := by
    intro w hw
    rcases hw with rfl | hw
    · exact hzS
    · exact hw.1
  have hAle : Subgroup.closure (insert z {w | w ∈ S ∧ Commute w y}) ≤
      K0.map (MulAut.conj g).toMonoidHom := by
    rw [← hSclosure]
    exact Subgroup.closure_mono hinsS
  have hKle : K0.map (MulAut.conj g).toMonoidHom ≤
      Subgroup.closure (insert z {w | w ∈ S ∧ Commute w y}) := by
    rw [← hgenKpair]
    exact Subgroup.closure_mono hins
  rw [hSclosure]
  exact le_antisymm hAle hKle

private theorem rankOneBender_pair_generation {E : Set X} {K0 : Subgroup X}
    (hgen : ∀ x ∈ E, x ∈ K0 → ∀ y ∈ E, y ∈ K0 → ¬ Commute x y →
      Subgroup.closure (insert y (Vmem E x)) = K0)
    {g : X} (hφE : ∀ y, y ∈ E ↔ MulAut.conj g y ∈ E)
    (hV : ∀ u, MulAut.conj g '' Vmem E u = Vmem E (MulAut.conj g u))
    {S : Set X} (hS : S = {w | w ∈ E ∧ w ∈ K0.map (MulAut.conj g).toMonoidHom})
    (hSclosure : Subgroup.closure S = K0.map (MulAut.conj g).toMonoidHom)
    {y z : X} (hyS : y ∈ S) (hzS : z ∈ S) (hync : ¬ Commute y z) :
    Subgroup.closure (insert z {w | w ∈ S ∧ Commute w y}) = Subgroup.closure S := by
  obtain ⟨y', hy'K0, hy'E, hy'eq⟩ := rankOneBender_exists_preimage hφE hS hyS
  obtain ⟨z', hz'K0, hz'E, hz'eq⟩ := rankOneBender_exists_preimage hφE hS hzS
  have hync' : ¬ Commute y' z' := by
    intro h
    have h' : Commute (MulAut.conj g y') (MulAut.conj g z') := Commute.map h (MulAut.conj g)
    rw [hy'eq, hz'eq] at h'
    exact hync h'
  exact rankOneBender_closure_insert_inter hS hzS hSclosure
    (rankOneBender_closure_insert_Vmem hgen hV hy'E hy'K0 hz'E hz'K0 hy'eq hz'eq hync')

private theorem rankOneBender_class_under_closure {E : Set X} {K0 : Subgroup X}
    (hconj : ∀ x ∈ E, x ∈ K0 → ∀ y ∈ E, y ∈ K0 → ∃ g ∈ K0, g * x * g⁻¹ = y)
    {g : X} (hφE : ∀ y, y ∈ E ↔ MulAut.conj g y ∈ E)
    {S : Set X} (hS : S = {w | w ∈ E ∧ w ∈ K0.map (MulAut.conj g).toMonoidHom})
    (hSclosure : Subgroup.closure S = K0.map (MulAut.conj g).toMonoidHom)
    {y z : X} (hyS : y ∈ S) (hzS : z ∈ S) :
    ∃ h ∈ Subgroup.closure S, h * y * h⁻¹ = z := by
  obtain ⟨y', hy'K0, hy'E, hy'eq⟩ := rankOneBender_exists_preimage hφE hS hyS
  obtain ⟨z', hz'K0, hz'E, hz'eq⟩ := rankOneBender_exists_preimage hφE hS hzS
  obtain ⟨c, hcK0, hcc⟩ := hconj y' hy'E hy'K0 z' hz'E hz'K0
  refine ⟨MulAut.conj g c, ?_, ?_⟩
  · rw [hSclosure]
    exact Subgroup.mem_map.mpr ⟨c, hcK0, rfl⟩
  · have hhc := congrArg (MulAut.conj g) hcc
    rw [show (MulAut.conj g) (c * y' * c⁻¹) =
      MulAut.conj g c * MulAut.conj g y' * (MulAut.conj g c)⁻¹ from by
        rw [← MulEquiv.map_inv, ← MulEquiv.map_mul, ← MulEquiv.map_mul]] at hhc
    rw [← hy'eq, ← hz'eq]
    exact hhc

private theorem rankOneBender_setup {s : X} (hs : orderOf s = 2) {E : Set X}
    (hE : E = {y | IsConj s y}) {K0 : Subgroup X} {n : ℕ} (hn : 0 < n)
    (hgen : ∀ x ∈ E, x ∈ K0 → ∀ y ∈ E, y ∈ K0 → ¬ Commute x y →
      Subgroup.closure (insert y (Vmem E x)) = K0)
    (hord : ∃ x ∈ E, x ∈ K0 ∧ ∃ y ∈ E, y ∈ K0 ∧ orderOf (x * y) = 2 ^ n + 1)
    {x : X} (hx : x ∈ E) :
    ∃ (g x₀ y₀ : X), x₀ ∈ E ∧ x₀ ∈ K0 ∧ y₀ ∈ E ∧ y₀ ∈ K0 ∧ ¬ Commute x₀ y₀ ∧
      MulAut.conj g x₀ = x ∧ (∀ y, y ∈ E ↔ MulAut.conj g y ∈ E) ∧
      (∀ u, MulAut.conj g '' Vmem E u = Vmem E (MulAut.conj g u)) ∧
      Vmem E x₀ ⊆ K0 ∧ orderOf (x₀ * y₀) = 2 ^ n + 1 := by
  obtain ⟨x₀, hx₀E, hx₀K, y₀, hy₀E, hy₀K, hordxy⟩ := hord
  have hnc₀ : ¬ Commute x₀ y₀ :=
    rankOneBender_not_commute_of_mem_class hs hE hn hx₀E hy₀E hordxy
  have hconjxx : IsConj x₀ x := by
    rw [hE] at hx₀E hx
    exact hx₀E.symm.trans hx
  obtain ⟨g, hg⟩ := isConj_iff.mp hconjxx
  have hφx₀ : MulAut.conj g x₀ = x := by
    rw [MulAut.conj_apply, hg]
  obtain ⟨hφE, _, hV⟩ := rankOneBender_conj_class_data hE g
  have hVx₀ : Vmem E x₀ ⊆ K0 :=
    rankOneBender_Vmem_subset_of_generate hgen hx₀E hx₀K hy₀E hy₀K hnc₀
  exact ⟨g, x₀, y₀, hx₀E, hx₀K, hy₀E, hy₀K, hnc₀, hφx₀, hφE, hV, hVx₀, hordxy⟩

theorem exists_rootLiftClass_of_subgroup {s : X} (hs : orderOf s = 2) {E : Set X}
    (hE : E = {y | IsConj s y}) (K0 : Subgroup X) {n : ℕ} (hn : 0 < n)
    (hgen : ∀ x ∈ E, x ∈ K0 → ∀ y ∈ E, y ∈ K0 → ¬ Commute x y →
      Subgroup.closure (insert y (Vmem E x)) = K0)
    (hconj : ∀ x ∈ E, x ∈ K0 → ∀ y ∈ E, y ∈ K0 → ∃ g ∈ K0, g * x * g⁻¹ = y)
    (hord : ∃ x ∈ E, x ∈ K0 ∧ ∃ y ∈ E, y ∈ K0 ∧ orderOf (x * y) = 2 ^ n + 1)
    {x : X} (hx : x ∈ E) :
    ∃ S₀ : Set X, S₀ ⊆ E ∧ Vmem E x ⊆ S₀ ∧ (∃ w ∈ S₀, ¬ Commute w x) ∧
      (∀ y ∈ S₀, ∀ z ∈ S₀, z * y * z⁻¹ ∈ S₀) ∧
      (∀ y ∈ S₀, ∀ z ∈ S₀, ¬ Commute y z →
        Subgroup.closure (insert z {w | w ∈ S₀ ∧ Commute w y}) = Subgroup.closure S₀) ∧
      (∀ y ∈ S₀, ∀ z ∈ S₀, ∃ g ∈ Subgroup.closure S₀, g * y * g⁻¹ = z) ∧
      ∃ y ∈ S₀, ∃ z ∈ S₀, orderOf (y * z) = 2 ^ n + 1 := by
  obtain ⟨g, x₀, y₀, hx₀E, hx₀K, hy₀E, hy₀K, hnc₀, hφx₀, hφE, hV, hVx₀, hordxy⟩ :=
    rankOneBender_setup hs hE hn hgen hord hx
  let S : Set X := {y | y ∈ E ∧ y ∈ K0.map (MulAut.conj g).toMonoidHom}
  have hVx : Vmem E x ⊆ S := by
    simpa [S] using rankOneBender_conj_Vmem_subset hφx₀ hφE hV hVx₀
  obtain ⟨hwS, hwnc⟩ := rankOneBender_conj_mem_not_commute hφx₀ hφE hx₀E hy₀E hy₀K hnc₀
  have hwS' : MulAut.conj g y₀ ∈ S := hwS
  have hSclosure : Subgroup.closure S = K0.map (MulAut.conj g).toMonoidHom := by
    have h := rankOneBender_closure_inter_conj hgen hx₀E hx₀K hy₀E hy₀K hnc₀ hφx₀ hV
      (by simpa [S] using hVx) hwS
    simpa [S] using h
  have hpair : ∀ y ∈ S, ∀ z ∈ S, ¬ Commute y z →
      Subgroup.closure (insert z {w | w ∈ S ∧ Commute w y}) = Subgroup.closure S :=
    fun y hy z hz hync => rankOneBender_pair_generation hgen hφE hV rfl hSclosure hy hz hync
  have hSconjS : ∀ y ∈ S, ∀ z ∈ S, ∃ h ∈ Subgroup.closure S, h * y * h⁻¹ = z :=
    fun y hy z hz => rankOneBender_class_under_closure hconj hφE rfl hSclosure hy hz
  have hSconj : ∀ y ∈ S, ∀ z ∈ S, z * y * z⁻¹ ∈ S := by
    intro y hy z hz
    simpa [S] using rankOneBender_conj_mem_inter hE hy.1 hy.2 hz.2
  have hxS : MulAut.conj g x₀ ∈ S :=
    ⟨(hφE x₀).mp hx₀E, Subgroup.mem_map.mpr ⟨x₀, hx₀K, rfl⟩⟩
  have hordS : ∃ y ∈ S, ∃ z ∈ S, orderOf (y * z) = 2 ^ n + 1 := by
    refine ⟨MulAut.conj g x₀, hxS, MulAut.conj g y₀, hwS', ?_⟩
    rw [← MulEquiv.map_mul, MulEquiv.orderOf_eq, hordxy]
  exact ⟨S, fun y hy => hy.1, hVx, ⟨MulAut.conj g y₀, hwS', hwnc⟩, hSconj, hpair,
    hSconjS, hordS⟩

end CFSG.OddTranspositions.PartFour
