module

public import CFSG.RankThree.PartTwo.Sec14.Item14Res9ProofFix
import CFSG.RankThree.PartTwo.Sec14.Item148PtResProofTools

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS

namespace Res9Fix

variable {G : Type} [Group G] [Finite G] {A X : Subgroup G} {a : G}

omit [Finite G] in
theorem Base.exists_decomp (hC : Base A a X)
    (n : ↥(pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔ X)) :
    ∃ y : ↥X, (n : G) * (y : G)⁻¹ ∈ pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) := by
  obtain ⟨o, ho, y, hy, hn⟩ := Item148PtRes.exists_mul_of_mem_sup hC.X_le_normalizer_O n.2
  refine ⟨⟨y, hy⟩, ?_⟩
  rw [hn, mul_inv_cancel_right]
  exact ho

omit [Finite G] in
theorem Base.mk_eq_of_decomp (hC : Base A a X) {n : G} {y y' : ↥X}
    (hy : n * (y : G)⁻¹ ∈ pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)))
    (hy' : n * (y' : G)⁻¹ ∈ pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G))) :
    QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X) y =
      QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X) y' := by
  have e : (y : G) * (y' : G)⁻¹ = (n * (y : G)⁻¹)⁻¹ * (n * (y' : G)⁻¹) := by group
  have h1 : (y : G) * (y' : G)⁻¹ ∈ inSubgroup (aschbacherSolvableCore 3) X :=
    hC.inf_le_theta (Subgroup.mem_inf.mpr ⟨e ▸ mul_mem (inv_mem hy) hy',
      mul_mem y.2 (inv_mem y'.2)⟩)
  exact (mk_eq_mk_iff y.2 y'.2).mpr h1

noncomputable def Base.phi (hC : Base A a X) :
    ↥(pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔ X) →*
      (↥X ⧸ aschbacherSolvableCore 3 ↥X) where
  toFun n := QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X) (hC.exists_decomp n).choose
  map_one' := by
    rw [← map_one (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X))]
    refine hC.mk_eq_of_decomp (hC.exists_decomp 1).choose_spec ?_
    simp
  map_mul' n₁ n₂ := by
    set y₁ := (hC.exists_decomp n₁).choose with hy₁
    set y₂ := (hC.exists_decomp n₂).choose with hy₂
    have h₁ := (hC.exists_decomp n₁).choose_spec
    have h₂ := (hC.exists_decomp n₂).choose_spec
    rw [← hy₁] at h₁
    rw [← hy₂] at h₂
    rw [← map_mul]
    refine hC.mk_eq_of_decomp (hC.exists_decomp (n₁ * n₂)).choose_spec ?_
    have e : ((n₁ * n₂ : ↥(pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔ X)) : G) *
        ((y₁ * y₂ : ↥X) : G)⁻¹ =
        ((n₁ : G) * (y₁ : G)⁻¹) * ((y₁ : G) * ((n₂ : G) * (y₂ : G)⁻¹) * (y₁ : G)⁻¹) := by
      simp only [Subgroup.coe_mul]
      group
    rw [e]
    exact mul_mem h₁ ((Subgroup.mem_normalizer_iff.mp (hC.X_le_normalizer_O y₁.2) _).mp h₂)

omit [Finite G] in
theorem Base.phi_eq (hC : Base A a X)
    (n : ↥(pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔ X)) {y : ↥X}
    (hy : (n : G) * (y : G)⁻¹ ∈ pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G))) :
    hC.phi n = QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X) y :=
  hC.mk_eq_of_decomp (hC.exists_decomp n).choose_spec hy

omit [Finite G] in
theorem Base.phi_mul (hC : Base A a X) {o y : G}
    (ho : o ∈ pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G))) (hy : y ∈ X)
    (h : o * y ∈ pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔ X) :
    hC.phi ⟨o * y, h⟩ = QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X) ⟨y, hy⟩ :=
  hC.phi_eq _ (by simpa using ho)

omit [Finite G] in
theorem Base.mem_ker_phi (hC : Base A a X)
    (n : ↥(pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔ X)) :
    hC.phi n = 1 ↔ (n : G) ∈ pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) := by
  obtain ⟨y, hy⟩ := hC.exists_decomp n
  rw [hC.phi_eq n hy, mk_eq_one_iff y.2]
  constructor
  · intro h
    have e : (n : G) = (n : G) * (y : G)⁻¹ * y := by group
    rw [e]
    exact mul_mem hy (hC.theta_le h)
  · intro h
    have e : (y : G) = ((n : G) * (y : G)⁻¹)⁻¹ * n := by group
    exact hC.inf_le_theta (Subgroup.mem_inf.mpr ⟨e ▸ mul_mem (inv_mem hy) h, y.2⟩)

omit [Finite G] in
theorem Base.img_eq_map (hC : Base A a X) {H : Subgroup G}
    (hH : H ≤ pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔ X) :
    img a X H = (H.subgroupOf (pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔ X)).map
      hC.phi := by
  have hHO : H ≤ Subgroup.normalizer
      (pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) : Set G) :=
    hH.trans (sup_le Subgroup.le_normalizer hC.X_le_normalizer_O)
  ext γ
  constructor
  · rintro ⟨w, hw, rfl⟩
    have hw' := Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hw)
    obtain ⟨o, ho, h, hh, hoh⟩ := Item148PtRes.exists_mul_of_mem_sup hHO hw'.1
    have hhN : h ∈ pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔ X := hH hh
    refine ⟨⟨h, hhN⟩, Subgroup.mem_subgroupOf.mpr hh, ?_⟩
    have e : h = o⁻¹ * (w : G) := by rw [hoh]; group
    have h1 : (⟨h, hhN⟩ : ↥(pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔ X)) =
        ⟨o⁻¹ * w, e ▸ hhN⟩ := Subtype.ext e
    rw [h1, hC.phi_mul (inv_mem ho) w.2]
  · rintro ⟨n, hn, rfl⟩
    obtain ⟨o, ho, y, hy, hoy⟩ := Item148PtRes.exists_mul_of_mem_sup hC.X_le_normalizer_O n.2
    have h1 : n = ⟨o * y, hoy ▸ n.2⟩ := Subtype.ext hoy
    rw [h1, hC.phi_mul ho hy]
    refine mk_mem_img hy ?_
    have e : y = o⁻¹ * (n : G) := by rw [hoy]; group
    rw [e]
    exact mul_mem (Subgroup.mem_sup_left (inv_mem ho))
      (Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.mp hn))

omit [Finite G] in
theorem Base.isPerfect_img (hC : Base A a X) {H : Subgroup G} (hHp : Group.IsPerfect H)
    (hH : H ≤ pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔ X) :
    Group.IsPerfect (img a X H) := by
  rw [hC.img_eq_map hH]
  have : Group.IsPerfect
      ↥(H.subgroupOf (pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔ X)) :=
    Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hH).symm.toMonoidHom)
      (MulEquiv.surjective _)
  exact Group.IsPerfect.ofSurjective (hC.phi.subgroupMap_surjective _)

omit [Finite G] in
theorem Base.card_img_mul (hC : Base A a X) {H : Subgroup G}
    (hH : H ≤ pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔ X) :
    Nat.card (img a X H) *
        Nat.card (H ⊓ pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) : Subgroup G) =
      Nat.card H := by
  rw [hC.img_eq_map hH]
  set N := pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔ X with hN
  set f : ↥(H.subgroupOf N) →* (↥X ⧸ aschbacherSolvableCore 3 ↥X) :=
    hC.phi.comp (H.subgroupOf N).subtype with hf
  have hrange : f.range = (H.subgroupOf N).map hC.phi := by
    rw [hf, MonoidHom.range_comp, Subgroup.range_subtype]
  have hker : Nat.card f.ker =
      Nat.card (H ⊓ pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) : Subgroup G) := by
    refine Nat.card_congr ⟨fun k => ⟨((k : ↥(H.subgroupOf N)) : G), ?_⟩,
      fun x => ⟨⟨⟨x, hH (Subgroup.mem_inf.mp x.2).1⟩, Subgroup.mem_subgroupOf.mpr
        (Subgroup.mem_inf.mp x.2).1⟩, ?_⟩, ?_, ?_⟩
    · refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_subgroupOf.mp (k : ↥(H.subgroupOf N)).2, ?_⟩
      have h1 : hC.phi ((k : ↥(H.subgroupOf N)) : ↥N) = 1 := MonoidHom.mem_ker.mp k.2
      exact (hC.mem_ker_phi _).mp h1
    · show hC.phi _ = 1
      exact (hC.mem_ker_phi _).mpr (Subgroup.mem_inf.mp x.2).2
    · intro k
      rfl
    · intro x
      rfl
  have h1 := Subgroup.card_ker_mul_card_range f
  rw [hrange, hker] at h1
  have h2 : Nat.card ↥(H.subgroupOf N) = Nat.card H :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hH).toEquiv
  rw [mul_comm, h1, h2]

end Res9Fix

end CFSG.RankThree.PartTwo.Sec14
