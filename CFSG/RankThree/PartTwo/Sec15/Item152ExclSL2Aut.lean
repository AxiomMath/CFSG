module

public import CFSG.RankThree.PartTwo.Sec15.Item152ExclSL2Tools
import CFSG.RankThree.PartTwo.Sec13.Item136Lift
import CFSG.RankThree.PartTwo.KFacts.AutPSL2
import CFSG.RankThree.PartTwo.Sec4.Census.Item44Groups
import CFSG.Dihedral.GorensteinWalter.PGL2SquareRange

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG Matrix
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo (pglAction pglAction_toPGL)
open scoped MatrixGroups commutatorElement

theorem sq_mem_range_toPGL {K : Type*} [Field K] (g : PGL(2, K)) :
    g ^ 2 ∈ (ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range :=
  CFSG.GorensteinWalter.pgl2_sq_mem_psl2Range g

section Aut

variable {p : ℕ} [hp : Fact p.Prime]

theorem exists_sq_eq_conj_PSL2 (α : MulAut PSL(2, ZMod p)) :
    ∃ x : PSL(2, ZMod p), α ^ 2 = MulAut.conj x := by
  obtain ⟨g, σ, hα⟩ := KFacts.exists_pglAction_mul_psl2FieldAut α
  have hσ : σ = 1 := RingEquiv.toRingHom_injective (RingHom.ext_zmod _ _)
  rw [hσ, map_one, mul_one] at hα
  obtain ⟨x, hx⟩ := sq_mem_range_toPGL g
  refine ⟨x, ?_⟩
  rw [hα, ← map_pow, ← hx, pglAction_toPGL]

theorem exists_eq_conj_of_pow_three_PSL2 {α : MulAut PSL(2, ZMod p)} (hα : α ^ 3 = 1) :
    ∃ x : PSL(2, ZMod p), α = MulAut.conj x := by
  obtain ⟨x, hx⟩ := exists_sq_eq_conj_PSL2 α
  refine ⟨x⁻¹, ?_⟩
  calc α = α ^ 3 * (α ^ 2)⁻¹ := by group
    _ = MulAut.conj x⁻¹ := by rw [hα, hx, one_mul, map_inv]

theorem quotMulAut_conj {S : Type*} [Group S] (s : S) :
    quotMulAut (Subgroup.center S) (MulAut.conj s) = MulAut.conj (s : S ⧸ Subgroup.center S) := by
  ext x
  induction x using QuotientGroup.induction_on with
  | H x => rfl

theorem exists_eq_conj_of_pow_three_SL2 (hp5 : 5 ≤ p) {φ : MulAut SL(2, ZMod p)}
    (hφ : φ ^ 3 = 1) : ∃ s : SL(2, ZMod p), φ = MulAut.conj s := by
  set Z := Subgroup.center SL(2, ZMod p) with hZ
  have h3 : quotMulAut Z φ ^ 3 = 1 := by rw [← map_pow, hφ, map_one]
  obtain ⟨x, hx⟩ := exists_eq_conj_of_pow_three_PSL2 (p := p) h3
  obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective x
  set ψ := (MulAut.conj s)⁻¹ * φ with hψ
  have hψZ : ∀ t : SL(2, ZMod p), t⁻¹ * ψ t ∈ Z := by
    intro t
    have h1 : quotMulAut Z ψ = 1 := by
      rw [hψ, map_mul, map_inv, quotMulAut_conj, hx, inv_mul_cancel]
    have h2 := congrArg (fun τ : MulAut (SL(2, ZMod p) ⧸ Z) => τ (t : SL(2, ZMod p) ⧸ Z)) h1
    simp only [MulAut.one_apply, quotMulAut_mk] at h2
    exact (QuotientGroup.eq.mp h2.symm)
  have hcomm : ∀ a b : SL(2, ZMod p), ψ ⁅a, b⁆ = ⁅a, b⁆ := by
    intro a b
    have ha := Subgroup.mem_center_iff.mp (hψZ a)
    have hb := Subgroup.mem_center_iff.mp (hψZ b)
    have ea : ψ a = a * (a⁻¹ * ψ a) := by group
    have eb : ψ b = b * (b⁻¹ * ψ b) := by group
    rw [map_commutatorElement, ea, eb, commutatorElement_def, commutatorElement_def]
    set u := a⁻¹ * ψ a
    set v := b⁻¹ * ψ b
    have hu : ∀ y, y * u = u * y := ha
    have hv : ∀ y, y * v = v * y := hb
    calc a * u * (b * v) * (a * u)⁻¹ * (b * v)⁻¹
        = a * (u * b) * v * u⁻¹ * a⁻¹ * v⁻¹ * b⁻¹ := by group
      _ = a * (b * u) * v * u⁻¹ * a⁻¹ * v⁻¹ * b⁻¹ := by rw [hu b]
      _ = a * b * (u * v * u⁻¹) * a⁻¹ * v⁻¹ * b⁻¹ := by group
      _ = a * b * v * a⁻¹ * v⁻¹ * b⁻¹ := by rw [← hu v]; group
      _ = a * b * (a⁻¹ * v) * v⁻¹ * b⁻¹ := by rw [mul_assoc (a * b) v a⁻¹, ← hv a⁻¹]
      _ = a * b * a⁻¹ * b⁻¹ := by group
  have hperf : commutator SL(2, ZMod p) = ⊤ :=
    (Sec4.Census.isQuasisimple_SL2 hp5).1.commutator_eq_top
  have hle : commutator SL(2, ZMod p) ≤ MonoidHom.eqLocus (ψ : SL(2, ZMod p) →* SL(2, ZMod p))
      (MonoidHom.id _) := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    exact hcomm a b
  have hψ1 : ψ = 1 := by
    refine MulEquiv.ext fun t => ?_
    have ht : t ∈ MonoidHom.eqLocus (ψ : SL(2, ZMod p) →* SL(2, ZMod p)) (MonoidHom.id _) :=
      hle (hperf ▸ Subgroup.mem_top t)
    exact ht
  refine ⟨s, ?_⟩
  rw [hψ, inv_mul_eq_one] at hψ1
  exact hψ1.symm

end Aut

theorem kSL2pAutThree : KSL2pAutThree := by
  intro p _ hp5 E hE
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set S := SL(2, ZMod p)
  have hEinn : E ≤ (MulAut.conj : S →* MulAut S).range := by
    intro φ hφ
    obtain ⟨s, hs⟩ := exists_eq_conj_of_pow_three_SL2 (by omega) (hE.2 φ hφ)
    exact ⟨s, hs.symm⟩
  set Ehat := E.comap (MulAut.conj : S →* MulAut S) with hEhat
  set f : Ehat →* E := ((MulAut.conj : S →* MulAut S).comp Ehat.subtype).codRestrict E
    (fun x => x.2) with hf
  have hfs : Function.Surjective f := by
    rintro ⟨φ, hφ⟩
    obtain ⟨s, rfl⟩ := hEinn hφ
    exact ⟨⟨s, hφ⟩, rfl⟩
  have hE3 : IsPGroup 3 E := fun x => ⟨1, Subtype.ext (by simpa using hE.2 x x.2)⟩
  obtain ⟨T⟩ : Nonempty (Sylow 3 Ehat) := inferInstance
  have hTE : (T : Subgroup Ehat).map f = ⊤ := by
    have hEtop : IsPGroup 3 (⊤ : Subgroup E) := hE3.of_equiv Subgroup.topEquiv.symm
    have h := ((T.mapSurjective hfs).is_maximal' hEtop le_top).symm
    rwa [Sylow.coe_mapSurjective] at h
  have hTinj : Set.InjOn f ((T : Subgroup Ehat) : Set Ehat) := by
    intro x hx y hy hxy
    have hTxy : x⁻¹ * y ∈ (T : Subgroup Ehat) := mul_mem (inv_mem hx) hy
    have hf1 : f (x⁻¹ * y) = 1 := by rw [map_mul, map_inv, hxy, inv_mul_cancel]
    have hcen : ((x⁻¹ * y : Ehat) : S) ∈ Subgroup.center S := by
      have h2 : MulAut.conj ((x⁻¹ * y : Ehat) : S) = 1 := congrArg Subtype.val hf1
      rw [Subgroup.mem_center_iff]
      intro g
      have h3 := congrArg (fun τ : MulAut S => τ g) h2
      simp only [MulAut.conj_apply, MulAut.one_apply] at h3
      rw [mul_inv_eq_iff_eq_mul] at h3
      exact h3.symm
    obtain ⟨k, hk⟩ := T.isPGroup' ⟨x⁻¹ * y, hTxy⟩
    have hord3 : orderOf (x⁻¹ * y : Ehat) ∣ 3 ^ k := by
      apply orderOf_dvd_of_pow_eq_one
      exact congrArg Subtype.val hk
    have hord2 : orderOf ((x⁻¹ * y : Ehat) : S) ∣ 2 := by
      have := Subgroup.orderOf_dvd_natCard (Subgroup.center S) hcen
      rwa [Sec4.Census.card_center_SL2 (by omega)] at this
    rw [Subgroup.orderOf_coe] at hord2
    have hcop : Nat.Coprime (3 ^ k) 2 := Nat.Coprime.pow_left k (by norm_num)
    have hord1 : orderOf (x⁻¹ * y : Ehat) ∣ 1 := by
      rw [← hcop.gcd_eq_one]
      exact Nat.dvd_gcd hord3 hord2
    rw [Nat.dvd_one, orderOf_eq_one_iff, inv_mul_eq_one] at hord1
    exact hord1
  have hcardT : Nat.card (T : Subgroup Ehat) = Nat.card E := by
    rw [← Sec13.card_map_eq_of_injOn f hTinj, hTE, Subgroup.card_top]
  set T' : Subgroup S := (T : Subgroup Ehat).map Ehat.subtype with hT'
  have hT'3 : IsPGroup 3 T' := T.isPGroup'.map _
  obtain ⟨Q, hQ⟩ := hT'3.exists_le_sylow
  have hQc : IsCyclic (Q : Subgroup S) :=
    Sec4.Census.isCyclic_sylow_SL2 (p := p) (r := 3) (by norm_num) (by omega) Q
  have hT'c : IsCyclic T' := by
    have : IsCyclic (T'.subgroupOf (Q : Subgroup S)) := Subgroup.isCyclic _
    exact isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hQ).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hQ).surjective
  have hTc : IsCyclic (T : Subgroup Ehat) := by
    have e := (T : Subgroup Ehat).equivMapOfInjective Ehat.subtype Ehat.subtype_injective
    exact isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (T : Subgroup Ehat))
  have hog : orderOf g = Nat.card (T : Subgroup Ehat) :=
    orderOf_eq_card_of_forall_mem_zpowers hg
  have hg3 : g ^ 3 = 1 := by
    apply Subtype.ext
    refine hTinj (pow_mem g.2 3) (one_mem _) ?_
    rw [map_pow, OneMemClass.coe_one, map_one]
    exact Subtype.ext (by rw [Subgroup.coe_pow]; exact hE.2 _ (f (g : Ehat)).2)
  rw [← hcardT, ← hog]
  exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hg3)

end CFSG.RankThree.PartTwo.Sec15
