module

public import CFSG.LocalAnalysis.UniquenessCase.UC6K323Basic
public import CFSG.LocalAnalysis.UniquenessCase.UC6K322
public import CFSG.LieType.SteinbergBRAutGL32
public import CFSG.LargeExtraspecial.S12TriG2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6.K323A

open Matrix Subgroup CFSG.RepresentationTheory
open CFSG.LocalAnalysis.UniquenessCase.UCK (gl32_not_comm)

variable {p : ℕ} [Fact p.Prime]

theorem eq_one_of_commute_irred {H : Subgroup (GL (Fin 3) (ZMod p))}
    (hirr : IsIrreducibleMatrixRep H.subtype) (hnc : ∃ a ∈ H, ∃ b ∈ H, a * b ≠ b * a)
    {x : GL (Fin 3) (ZMod p)} (hx : ∀ h ∈ H, x * h = h * x) {z : Fin 3 → ZMod p} (hz0 : z ≠ 0)
    (hxz : (x : Matrix (Fin 3) (Fin 3) (ZMod p)) *ᵥ z = z) : x = 1 := by
  rcases CFSG.RankThree.SubgroupLists.scalar_commutant_or_cyclic Nat.prime_three hirr with
    hs | ⟨hcyc, -⟩
  · obtain ⟨c, hc⟩ := hs (x : Matrix (Fin 3) (Fin 3) (ZMod p)) fun g hg => by
      have := congrArg (fun w : GL (Fin 3) (ZMod p) => (w : Matrix (Fin 3) (Fin 3) (ZMod p)))
        (hx g hg).symm
      simpa only [Units.val_mul] using this
    have hcz : (c - 1) • z = 0 := by
      have h1 : (x : Matrix (Fin 3) (Fin 3) (ZMod p)) *ᵥ z = c • z := by
        rw [hc]
        ext i
        simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]
      rw [sub_smul, one_smul, ← h1, hxz, sub_self]
    have hc1 : c = 1 := sub_eq_zero.1 ((smul_eq_zero.1 hcz).resolve_right hz0)
    refine Units.ext ?_
    rw [hc, hc1, Units.val_one]
    simp
  · exfalso
    obtain ⟨a, ha, b, hb, hab⟩ := hnc
    exact hab (congrArg Subtype.val (hcyc.isMulCommutative.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩))

section Conj

variable {Γ : Type*} [Group Γ]

@[expose] def conjAut (H : Subgroup Γ) (x : Γ) (hx : ∀ h ∈ H, x * h * x⁻¹ ∈ H)
    (hx' : ∀ h ∈ H, x⁻¹ * h * x ∈ H) : MulAut H where
  toFun h := ⟨x * h * x⁻¹, hx h h.2⟩
  invFun h := ⟨x⁻¹ * h * x, hx' h h.2⟩
  left_inv h := Subtype.ext (by simp [mul_assoc])
  right_inv h := Subtype.ext (by simp [mul_assoc])
  map_mul' a b := Subtype.ext (by simp [mul_assoc])

@[expose] def conjHom (H G X : Subgroup Γ) (hXG : X ≤ G)
    (hnorm : ∀ g ∈ G, ∀ h ∈ H, g * h * g⁻¹ ∈ H) : X →* MulAut H where
  toFun x := conjAut H x (hnorm x (hXG x.2)) (fun h hh => by
    simpa using hnorm x⁻¹ (G.inv_mem (hXG x.2)) h hh)
  map_one' := MulEquiv.ext fun h => Subtype.ext (by simp [conjAut])
  map_mul' a b := MulEquiv.ext fun h => Subtype.ext (by simp [conjAut, mul_assoc])

theorem conjHom_apply (H G X : Subgroup Γ) (hXG : X ≤ G)
    (hnorm : ∀ g ∈ G, ∀ h ∈ H, g * h * g⁻¹ ∈ H) (x : X) (h : H) :
    ((conjHom H G X hXG hnorm x h : H) : Γ) = x * h * (x : Γ)⁻¹ := rfl

end Conj

theorem conjHom_injective {G H X : Subgroup (GL (Fin 3) (ZMod p))} (hXG : X ≤ G)
    (hnorm : ∀ g ∈ G, ∀ h ∈ H, g * h * g⁻¹ ∈ H) (hirr : IsIrreducibleMatrixRep H.subtype)
    (hnc : ∃ a ∈ H, ∃ b ∈ H, a * b ≠ b * a) {z : Fin 3 → ZMod p} (hz0 : z ≠ 0)
    (hXz : ∀ y ∈ X, (y : Matrix (Fin 3) (Fin 3) (ZMod p)) *ᵥ z = z) :
    Function.Injective (conjHom H G X hXG hnorm) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have hc : ∀ h ∈ H, (x : GL (Fin 3) (ZMod p)) * h = h * x := by
    intro h hh
    have := congrArg (fun φ : MulAut H => ((φ ⟨h, hh⟩ : H) : GL (Fin 3) (ZMod p))) hx
    simp only [conjHom_apply, MulAut.one_apply] at this
    calc (x : GL (Fin 3) (ZMod p)) * h = (x * h * (x : GL (Fin 3) (ZMod p))⁻¹) * x := by group
      _ = h * x := by rw [this]
  exact Subtype.ext (eq_one_of_commute_irred hirr hnc hc hz0 (hXz x x.2))

theorem card_dvd_mulAut {G H X : Subgroup (GL (Fin 3) (ZMod p))} (hXG : X ≤ G)
    (hnorm : ∀ g ∈ G, ∀ h ∈ H, g * h * g⁻¹ ∈ H) (hirr : IsIrreducibleMatrixRep H.subtype)
    (hnc : ∃ a ∈ H, ∃ b ∈ H, a * b ≠ b * a) {z : Fin 3 → ZMod p} (hz0 : z ≠ 0)
    (hXz : ∀ y ∈ X, (y : Matrix (Fin 3) (Fin 3) (ZMod p)) *ᵥ z = z) :
    Nat.card X ∣ Nat.card (MulAut H) :=
  Subgroup.card_dvd_of_injective _ (conjHom_injective hXG hnorm hirr hnc hz0 hXz)

theorem false_of_gl32 (hp2 : p ≠ 2) {G H X : Subgroup (GL (Fin 3) (ZMod p))} (hXG : X ≤ G)
    (hnorm : ∀ g ∈ G, ∀ h ∈ H, g * h * g⁻¹ ∈ H) (hirr : IsIrreducibleMatrixRep H.subtype)
    (e : H ≃* GL (Fin 3) (ZMod 2)) (h7 : p % 7 = 1 ∨ p % 7 = 2 ∨ p % 7 = 4)
    {z : Fin 3 → ZMod p} (hz0 : z ≠ 0)
    (hXz : ∀ y ∈ X, (y : Matrix (Fin 3) (Fin 3) (ZMod p)) *ᵥ z = z)
    (hXcard : Nat.card X = (p ^ 2 - 1) / 2) : False := by
  have hnc : ∃ a ∈ H, ∃ b ∈ H, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := gl32_not_comm
    exact ⟨(e.symm a : GL (Fin 3) (ZMod p)), (e.symm a).2, (e.symm b : GL (Fin 3) (ZMod p)),
      (e.symm b).2, fun h => hab (by
        have h2 : e.symm (a * b) = e.symm (b * a) :=
          Subtype.ext (by rw [map_mul, map_mul, Subgroup.coe_mul, Subgroup.coe_mul]; exact h)
        exact e.symm.injective h2)⟩
  have hdvd := card_dvd_mulAut hXG hnorm hirr hnc hz0 hXz
  rw [Nat.card_congr (MulAut.congr e).toEquiv,
    CFSG.LieType.SteinbergBR.AutGL32.card_mulAut_GL32, hXcard] at hdvd
  have hp : p.Prime := Fact.out
  have hle := Nat.le_of_dvd (by norm_num) hdvd
  have hp25 : p ≤ 25 := by
    by_contra h
    push Not at h
    have : 26 ^ 2 ≤ p ^ 2 := Nat.pow_le_pow_left h 2
    omega
  interval_cases p <;> first | omega | exact absurd hp (by norm_num) | skip
  all_goals omega

section InnerTwelve

theorem exists_pow_twelve_mem_inner {S : Type*} [Group S] [Finite S]
    (hinj : Function.Injective (MulAut.conj : S →* MulAut S))
    (hle : Nat.card (MulAut S) ≤ 4 * Nat.card S) (a : MulAut S) :
    ∃ s : S, MulAut.conj s = a ^ 12 := by
  classical
  set Inn : Subgroup (MulAut S) := (MulAut.conj : S →* MulAut S).range with hInn
  haveI : Inn.Normal := ⟨by
    rintro _ ⟨s, rfl⟩ φ
    refine ⟨φ s, MulEquiv.ext fun x => ?_⟩
    simp [MulAut.conj_apply]⟩
  have hcard : Nat.card Inn = Nat.card S :=
    (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hmul := Subgroup.card_mul_index Inn
  have hS0 : 0 < Nat.card S := Nat.card_pos
  have hidx : Inn.index ≤ 4 := by
    rw [hcard] at hmul
    nlinarith
  have h0 : 0 < Inn.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have hmem := Subgroup.pow_index_mem Inn a
  have hdvd : Inn.index ∣ 12 := by
    interval_cases h : Inn.index <;> norm_num
  obtain ⟨k, hk⟩ := hdvd
  have : a ^ 12 ∈ Inn := by
    rw [hk, pow_mul]
    exact Inn.pow_mem hmem k
  obtain ⟨s, hs⟩ := this
  exact ⟨s, hs⟩

end InnerTwelve

section ThreeCover

open CFSG.LocalAnalysis.UniquenessCase.UC6.K322Rows (map_center_k322)

@[expose] def autQuot {H : Type*} [Group H] (φ : MulAut H) : MulAut (H ⧸ Subgroup.center H) :=
  QuotientGroup.congr _ _ φ (map_center_k322 φ)

theorem autQuot_mk {H : Type*} [Group H] (φ : MulAut H) (h : H) :
    autQuot φ (h : H ⧸ Subgroup.center H) = ((φ h : H) : H ⧸ Subgroup.center H) := rfl

@[expose] def quotHom (H G X : Subgroup (GL (Fin 3) (ZMod p))) (hXG : X ≤ G)
    (hnorm : ∀ g ∈ G, ∀ h ∈ H, g * h * g⁻¹ ∈ H) : X →* MulAut (H ⧸ Subgroup.center H) where
  toFun x := autQuot (conjHom H G X hXG hnorm x)
  map_one' := MulEquiv.ext fun q => by
    induction q using QuotientGroup.induction_on
    simp [autQuot_mk]
  map_mul' a b := MulEquiv.ext fun q => by
    induction q using QuotientGroup.induction_on
    simp [autQuot_mk]

theorem quotHom_injective {G H X : Subgroup (GL (Fin 3) (ZMod p))} (hXG : X ≤ G)
    (hnorm : ∀ g ∈ G, ∀ h ∈ H, g * h * g⁻¹ ∈ H) (hirr : IsIrreducibleMatrixRep H.subtype)
    (hnc : ∃ a ∈ H, ∃ b ∈ H, a * b ≠ b * a) (hperf : Group.IsPerfect H)
    {z : Fin 3 → ZMod p} (hz0 : z ≠ 0)
    (hXz : ∀ y ∈ X, (y : Matrix (Fin 3) (Fin 3) (ZMod p)) *ᵥ z = z) :
    Function.Injective (quotHom H G X hXG hnorm) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  set c : H → H := fun h => conjHom H G X hXG hnorm x h with hc
  have hcen : ∀ h : H, h⁻¹ * c h ∈ Subgroup.center H := by
    intro h
    have := congrArg (fun φ : MulAut (H ⧸ Subgroup.center H) => φ (h : H ⧸ Subgroup.center H)) hx
    simp only [quotHom, MonoidHom.coe_mk, OneHom.coe_mk, autQuot_mk, MulAut.one_apply] at this
    exact QuotientGroup.eq.1 this.symm
  let lam : H →* Subgroup.center H :=
    { toFun := fun h => ⟨h⁻¹ * c h, hcen h⟩
      map_one' := Subtype.ext (by simp [hc, conjHom, conjAut])
      map_mul' := fun a b => Subtype.ext (by
        have hmul : c (a * b) = c a * c b := map_mul _ a b
        have hb := Subgroup.mem_center_iff.1 (hcen a) (b⁻¹)
        simp only [Subgroup.coe_mul, hmul]
        calc (a * b)⁻¹ * (c a * c b) = b⁻¹ * (a⁻¹ * c a) * c b := by group
          _ = (a⁻¹ * c a) * b⁻¹ * c b := by rw [← hb]
          _ = (a⁻¹ * c a) * (b⁻¹ * c b) := by group) }
  have hker : commutator H ≤ lam.ker := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.2
      (Subtype.ext (Subgroup.mem_center_iff.1 (lam b).2 (lam a)))
  have htriv : ∀ h : H, c h = h := by
    intro h
    have h1 : lam h = 1 := by
      have : h ∈ lam.ker := by
        apply hker
        rw [hperf.commutator_eq_top]
        exact Subgroup.mem_top h
      exact this
    have h2 := congrArg Subtype.val h1
    simp only [lam, MonoidHom.coe_mk, OneHom.coe_mk, OneMemClass.coe_one] at h2
    exact (inv_mul_eq_one.1 h2).symm
  have hcomm : ∀ h ∈ H, (x : GL (Fin 3) (ZMod p)) * h = h * x := by
    intro h hh
    have := congrArg Subtype.val (htriv ⟨h, hh⟩)
    simp only [hc, conjHom_apply] at this
    calc (x : GL (Fin 3) (ZMod p)) * h = ((x : GL (Fin 3) (ZMod p)) * h * (x : GL (Fin 3) (ZMod p))⁻¹) * x := by
          group
      _ = h * x := by rw [this]
  exact Subtype.ext (eq_one_of_commute_irred hirr hnc hcomm hz0 (hXz x x.2))

theorem orderOf_le_five_alt6 (σ : alternatingGroup (Fin 6)) : orderOf σ ≤ 5 := by
  have h : ∀ σ : alternatingGroup (Fin 6), σ ^ 5 = 1 ∨ σ ^ 4 = 1 ∨ σ ^ 3 = 1 := by
    decide +kernel
  rcases h σ with h | h | h
  · exact orderOf_le_of_pow_eq_one (by norm_num) h
  · exact (orderOf_le_of_pow_eq_one (by norm_num) h).trans (by norm_num)
  · exact (orderOf_le_of_pow_eq_one (by norm_num) h).trans (by norm_num)

theorem conj_injective_alt6 :
    Function.Injective (MulAut.conj : alternatingGroup (Fin 6) →* MulAut (alternatingGroup (Fin 6))) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hc : g ∈ Subgroup.center (alternatingGroup (Fin 6)) := by
    rw [Subgroup.mem_center_iff]
    intro h
    have := congrArg (fun e : MulAut (alternatingGroup (Fin 6)) => e h) hg
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    calc h * g = g * h * g⁻¹ * g := by rw [this]
      _ = g * h := by group
  rw [alternatingGroup.center_eq_bot (by simp)] at hc
  exact hc

theorem card_alt6 : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  rfl

theorem false_of_threeCoverA6 (hp2 : p ≠ 2)
    {G H X : Subgroup (GL (Fin 3) (ZMod p))} (hXG : X ≤ G)
    (hnorm : ∀ g ∈ G, ∀ h ∈ H, g * h * g⁻¹ ∈ H) (hirr : IsIrreducibleMatrixRep H.subtype)
    (hperf : Group.IsPerfect H) (e6 : (H ⧸ Subgroup.center H) ≃* alternatingGroup (Fin 6))
    (h30 : p % 30 = 1 ∨ p % 30 = 19) {z : Fin 3 → ZMod p} (hz0 : z ≠ 0)
    (hXz : ∀ y ∈ X, (y : Matrix (Fin 3) (Fin 3) (ZMod p)) *ᵥ z = z) (hXcyc : IsCyclic X)
    (hXcard : Nat.card X = (p ^ 2 - 1) / 2) : False := by
  haveI : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  have hq : CFSG.Open.IsQuasisimple ↥H := ⟨hperf.commutator_eq_top, e6.isSimpleGroup⟩
  have hnc : ∃ a ∈ H, ∃ b ∈ H, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := K322Rows.not_comm_of_isQuasisimple_k322 hq
    exact ⟨a, a.2, b, b.2, fun h => hab (Subtype.ext h)⟩
  have hinj := quotHom_injective hXG hnorm hirr hnc hperf hz0 hXz
  let ρ : X →* MulAut (alternatingGroup (Fin 6)) :=
    (MulAut.congr e6).toMonoidHom.comp (quotHom H G X hXG hnorm)
  have hρ : Function.Injective ρ := (MulAut.congr e6).injective.comp hinj
  obtain ⟨g, hgX, hgord, -⟩ := K323B.cyclic_data hXcyc
  set a : MulAut (alternatingGroup (Fin 6)) := ρ ⟨g, hgX⟩ with ha
  have hao : orderOf a = (p ^ 2 - 1) / 2 := by
    rw [ha, orderOf_injective ρ hρ, ← Subgroup.orderOf_coe]
    simpa [hXcard] using hgord
  obtain ⟨σ, hσ⟩ := exists_pow_twelve_mem_inner conj_injective_alt6
    (by rw [card_alt6]; exact CFSG.LargeExtraspecial.S12Tri.card_mulAut_alternatingGroup_six_le) a
  have hσo : orderOf σ = ((p ^ 2 - 1) / 2) / Nat.gcd ((p ^ 2 - 1) / 2) 12 := by
    rw [← orderOf_injective _ conj_injective_alt6 σ, hσ, orderOf_pow' a (by norm_num), hao]
  have h5 := orderOf_le_five_alt6 σ
  rw [hσo] at h5
  have hp : p.Prime := Fact.out
  have h2 := hp.two_le
  have hd : Nat.gcd ((p ^ 2 - 1) / 2) 12 ≤ 12 := Nat.gcd_le_right _ (by norm_num)
  have hd0 : 0 < Nat.gcd ((p ^ 2 - 1) / 2) 12 := Nat.gcd_pos_of_pos_right _ (by norm_num)
  have h12 : ((p ^ 2 - 1) / 2) / 12 ≤ ((p ^ 2 - 1) / 2) / Nat.gcd ((p ^ 2 - 1) / 2) 12 :=
    Nat.div_le_div_left hd hd0
  have hp12 : p ≤ 12 := by
    by_contra h
    push Not at h
    have : 13 ^ 2 ≤ p ^ 2 := Nat.pow_le_pow_left h 2
    omega
  omega

end ThreeCover

end CFSG.LocalAnalysis.UniquenessCase.UC6.K323A
