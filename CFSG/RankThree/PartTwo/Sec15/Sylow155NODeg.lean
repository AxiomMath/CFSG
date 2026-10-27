module

public import CFSG.RankThree.PartTwo.Sec4.Vocabulary
import CFSG.RankThree.PartTwo.Sec14.Item148PtResProofA6A6Cent
import CFSG.RankThree.PartTwo.Sec14.Item148PtResProofA6Aut
import CFSG.RankThree.PartTwo.Sec15.Sylow155TwinGrp
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierAlternatingSix
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.A6Aut

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155NO

open CFSG.RankThree.PartTwo
open scoped commutatorElement

private theorem eq_or_mul_eq_one_of_card_three {G : Type*} [Group G] {Z : Subgroup G}
    (hZ : Nat.card Z = 3) {u v : G} (hu : u ∈ Z) (hv : v ∈ Z) (hu1 : u ≠ 1) (hv1 : v ≠ 1) :
    u = v ∨ u * v = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite Z := Nat.finite_of_card_ne_zero (by rw [hZ]; norm_num)
  have hu3 : u ^ 3 = 1 := by
    have h := Subgroup.orderOf_dvd_natCard Z hu
    rw [hZ] at h
    exact orderOf_dvd_iff_pow_eq_one.mp h
  have hord : orderOf u = 3 := orderOf_eq_prime hu3 hu1
  have hzp : Subgroup.zpowers u = Z :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hu) (by
      rw [Nat.card_zpowers, hord, hZ])
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hzp ▸ hv)
  rw [← zpow_mod_orderOf, hord] at hk
  have hk3 : k % ((3 : ℕ) : ℤ) = 0 ∨ k % ((3 : ℕ) : ℤ) = 1 ∨ k % ((3 : ℕ) : ℤ) = 2 := by omega
  rcases hk3 with h | h | h
  · rw [h] at hk
    exact absurd hk.symm (by simpa using hv1)
  · rw [h] at hk
    exact Or.inl (by simpa using hk)
  · rw [h] at hk
    refine Or.inr ?_
    rw [← hk]
    have : (u : G) * u ^ (2 : ℤ) = u ^ 3 := by
      rw [← zpow_one_add]
      norm_num
    rw [this, hu3]

private theorem mul_pow_three_of_mem_center {X : Type*} [Group X]
    (hZ : Nat.card (Subgroup.center X) = 3) {g h : X} (hc : ⁅h, g⁆ ∈ Subgroup.center X) :
    (g * h) ^ 3 = g ^ 3 * h ^ 3 := by
  have h1 := Subgroup.mem_center_iff.mp hc
  have h3 : ⁅h, g⁆ ^ 3 = 1 := by
    have := Subgroup.orderOf_dvd_natCard (Subgroup.center X) hc
    rw [hZ] at this
    exact orderOf_dvd_iff_pow_eq_one.mp this
  rw [Commute.mul_pow_eq_pow_mul_pow_mul_commutatorElement_pow_choose_two (a := g) (b := h)
    (h1 g) (h1 h) 3]
  have : Nat.choose 3 2 = 3 := by decide
  rw [this, h3, mul_one]

private theorem exists_threeCycles : ∃ a b : alternatingGroup (Fin 6), a * b = b * a ∧
    a ^ 3 = 1 ∧ b ^ 3 = 1 ∧ a ≠ 1 ∧ b ≠ 1 ∧ a * b ≠ 1 ∧ a * b⁻¹ ≠ 1 :=
  ⟨⟨Equiv.swap 0 1 * Equiv.swap 1 2, Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩,
    ⟨Equiv.swap 3 4 * Equiv.swap 4 5, Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩, by decide⟩

theorem exists_pow_three_not_mem_center {X : Type*} [Group X] [Finite X]
    (hX : Sec4.IsTripleCover X (alternatingGroup (Fin 6))) :
    ∃ x : X, x ^ 3 = 1 ∧ x ∉ Subgroup.center X := by
  obtain ⟨hZ, ⟨e⟩⟩ := hX
  obtain ⟨a, b, hab, ha3, hb3, ha1, hb1, hab1, hab2⟩ := exists_threeCycles
  obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (e.symm a)
  obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective (e.symm b)
  set π := QuotientGroup.mk' (Subgroup.center X)
  have hπx : π x = e.symm a := hx
  have hπy : π y = e.symm b := hy
  have hmem : ∀ z : X, z ∈ Subgroup.center X ↔ π z = 1 := fun z =>
    (QuotientGroup.eq_one_iff z).symm
  have hnot : ∀ (z : X) (c : alternatingGroup (Fin 6)), π z = e.symm c → c ≠ 1 →
      z ∉ Subgroup.center X := by
    intro z c hz hc hzc
    rw [hmem, hz] at hzc
    exact hc (e.symm.injective (hzc.trans (map_one _).symm))
  have hcom : ∀ (z w : X) (c d : alternatingGroup (Fin 6)), π z = e.symm c → π w = e.symm d →
      c * d = d * c → ⁅z, w⁆ ∈ Subgroup.center X := by
    intro z w c d hz hw hcd
    rw [hmem, map_commutatorElement, hz, hw, ← map_commutatorElement,
      commutatorElement_eq_one_iff_mul_comm.mpr hcd, map_one]
  have hpow : ∀ (z : X) (c : alternatingGroup (Fin 6)), π z = e.symm c → c ^ 3 = 1 →
      z ^ 3 ∈ Subgroup.center X := by
    intro z c hz hc
    rw [hmem, map_pow, hz, ← map_pow, hc, map_one]
  have hxZ : x ∉ Subgroup.center X := hnot x a hπx ha1
  have hyZ : y ∉ Subgroup.center X := hnot y b hπy hb1
  have hxy : x * y ∉ Subgroup.center X :=
    hnot (x * y) (a * b) (by rw [map_mul, hπx, hπy, map_mul]) hab1
  have hxyi : x * y⁻¹ ∉ Subgroup.center X :=
    hnot (x * y⁻¹) (a * b⁻¹) (by rw [map_mul, map_inv, hπx, hπy, map_mul, map_inv]) hab2
  have hu : x ^ 3 ∈ Subgroup.center X := hpow x a hπx ha3
  have hv : y ^ 3 ∈ Subgroup.center X := hpow y b hπy hb3
  have hcomm : Commute a b := hab
  have hc1 : ⁅y, x⁆ ∈ Subgroup.center X := hcom y x b a hπy hπx hab.symm
  have hc2 : ⁅y⁻¹, x⁆ ∈ Subgroup.center X :=
    hcom y⁻¹ x b⁻¹ a (by rw [map_inv, hπy, map_inv]) hπx hcomm.inv_right.eq.symm
  have e1 : (x * y) ^ 3 = x ^ 3 * y ^ 3 := mul_pow_three_of_mem_center hZ hc1
  have e2 : (x * y⁻¹) ^ 3 = x ^ 3 * (y ^ 3)⁻¹ := by
    rw [mul_pow_three_of_mem_center hZ hc2, inv_pow]
  by_cases hu1 : x ^ 3 = 1
  · exact ⟨x, hu1, hxZ⟩
  by_cases hv1 : y ^ 3 = 1
  · exact ⟨y, hv1, hyZ⟩
  rcases eq_or_mul_eq_one_of_card_three hZ hu hv hu1 hv1 with h | h
  · refine ⟨x * y⁻¹, ?_, hxyi⟩
    rw [e2, h]
    exact mul_inv_cancel _
  · exact ⟨x * y, by rw [e1]; exact h, hxy⟩


section Commutator

variable {Q : Type*} [Group Q]

private theorem mem_normalizer_commutator {J : Subgroup Q} {a : Q}
    (ha : a ∈ Subgroup.normalizer (J : Set Q)) :
    a ∈ Subgroup.normalizer ((⁅J, J⁆ : Subgroup Q) : Set Q) := by
  have key : ∀ b ∈ Subgroup.normalizer (J : Set Q), ∀ d ∈ ⁅J, J⁆, b * d * b⁻¹ ∈ ⁅J, J⁆ := by
    intro b hb d hd
    have hle : ⁅J, J⁆ ≤ (⁅J, J⁆ : Subgroup Q).comap (MulAut.conj b).toMonoidHom := by
      rw [Subgroup.commutator_le]
      intro g₁ hg₁ g₂ hg₂
      have h1 : b * g₁ * b⁻¹ ∈ J := (Subgroup.mem_normalizer_iff.mp hb g₁).mp hg₁
      have h2 : b * g₂ * b⁻¹ ∈ J := (Subgroup.mem_normalizer_iff.mp hb g₂).mp hg₂
      rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, map_commutatorElement, MulAut.conj_apply,
        MulAut.conj_apply]
      exact Subgroup.commutator_mem_commutator h1 h2
    exact hle hd
  refine Subgroup.mem_normalizer_iff.mpr fun d => ⟨key a ha d, fun h => ?_⟩
  have := key a⁻¹ (inv_mem ha) _ h
  simpa [mul_assoc] using this

private theorem exists_equiv_commutator {J : Subgroup Q}
    (hZ : Nat.card (Subgroup.center ↥J) = 3)
    (e : ↥J ⧸ Subgroup.center ↥J ≃* alternatingGroup (Fin 6)) (hne : commutator ↥J ≠ ⊤) :
    ⁅J, J⁆ ⊓ Sec14.Item148PtRes.centerIn J = ⊥ ∧
      Nonempty (↥(⁅J, J⁆ : Subgroup Q) ≃* alternatingGroup (Fin 6)) := by
  have hDeq := Subgroup.map_subtype_commutator J
  haveI : Group.IsPerfect (alternatingGroup (Fin 6)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  haveI : Group.IsPerfect (↥J ⧸ Subgroup.center ↥J) :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  set π := QuotientGroup.mk' (Subgroup.center ↥J) with hπ
  have hsurj : ∀ y : ↥J ⧸ Subgroup.center ↥J, ∃ d ∈ commutator ↥J, π d = y := by
    intro y
    have h : (commutator ↥J).map π = ⊤ := by
      rw [commutator_def, Subgroup.map_commutator,
        Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _), ← commutator_def,
        Group.IsPerfect.commutator_eq_top]
    have hy : y ∈ (commutator ↥J).map π := h ▸ Subgroup.mem_top y
    obtain ⟨d, hd, rfl⟩ := hy
    exact ⟨d, hd, rfl⟩
  set Z := Sec14.Item148PtRes.centerIn J with hZdef
  have hZcard : Nat.card Z = 3 := by
    rw [hZdef, Sec14.Item148PtRes.centerIn, Subgroup.card_map_of_injective J.subtype_injective, hZ]
  haveI : Finite Z := Nat.finite_of_card_ne_zero (by rw [hZcard]; norm_num)
  have hDJ : (⁅J, J⁆ : Subgroup Q) ≤ J := Subgroup.commutator_le_self J
  have hmemD : ∀ d : ↥J, d ∈ commutator ↥J → (d : Q) ∈ (⁅J, J⁆ : Subgroup Q) := fun d hd =>
    hDeq ▸ Subgroup.mem_map_of_mem _ hd
  have hbot : ⁅J, J⁆ ⊓ Z = ⊥ := by
    by_contra hbot
    have hZD : Z ≤ ⁅J, J⁆ := by
      have hdvd := Subgroup.card_dvd_of_le (inf_le_right : (⁅J, J⁆ : Subgroup Q) ⊓ Z ≤ Z)
      rw [hZcard] at hdvd
      have hne1 : Nat.card (⁅J, J⁆ ⊓ Z : Subgroup Q) ≠ 1 := fun h =>
        hbot (Subgroup.eq_bot_of_card_eq _ h)
      have h3 : Nat.card (⁅J, J⁆ ⊓ Z : Subgroup Q) = 3 := by
        rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
        · exact absurd h hne1
        · exact h
      have : (⁅J, J⁆ ⊓ Z : Subgroup Q) = Z :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h3, hZcard])
      rw [← this]
      exact inf_le_left
    apply hne
    have hJD : J ≤ ⁅J, J⁆ := by
      intro j hj
      obtain ⟨d, hd, hdj⟩ := hsurj (π ⟨j, hj⟩)
      have hz : d⁻¹ * ⟨j, hj⟩ ∈ Subgroup.center ↥J := QuotientGroup.eq.mp hdj
      have hzZ : ((d⁻¹ * ⟨j, hj⟩ : ↥J) : Q) ∈ Z :=
        Sec14.Item148PtRes.mem_centerIn_iff.mpr ⟨(d⁻¹ * ⟨j, hj⟩ : ↥J).2, hz⟩
      have hj' : j = (d : Q) * ((d⁻¹ * ⟨j, hj⟩ : ↥J) : Q) := by
        simp
      rw [hj']
      exact mul_mem (hmemD d hd) (hZD hzZ)
    exact Group.isPerfect_def.mp (Subgroup.isPerfect_iff.mpr (le_antisymm hDJ hJD))
  let f : ↥(⁅J, J⁆ : Subgroup Q) →* alternatingGroup (Fin 6) :=
    e.toMonoidHom.comp (π.comp (Subgroup.inclusion hDJ))
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro d hd
    have h1 : π (Subgroup.inclusion hDJ d) = 1 := e.injective (hd.trans (map_one e).symm)
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    have h2 : (d : Q) ∈ Z := Sec14.Item148PtRes.mem_centerIn_iff.mpr ⟨hDJ d.2, h1⟩
    have h3 : (d : Q) ∈ (⁅J, J⁆ ⊓ Z : Subgroup Q) := ⟨d.2, h2⟩
    rw [hbot, Subgroup.mem_bot] at h3
    exact Subtype.ext h3
  have hsurj' : Function.Surjective f := by
    intro x
    obtain ⟨d₀, hd₀, hd₀x⟩ := hsurj (e.symm x)
    refine ⟨⟨(d₀ : Q), hmemD d₀ hd₀⟩, ?_⟩
    show e (π (Subgroup.inclusion hDJ ⟨(d₀ : Q), hmemD d₀ hd₀⟩)) = x
    have : Subgroup.inclusion hDJ ⟨(d₀ : Q), hmemD d₀ hd₀⟩ = d₀ := rfl
    rw [this, hd₀x]
    exact e.apply_symm_apply x
  exact ⟨hbot, ⟨MulEquiv.ofBijective f ⟨hinj, hsurj'⟩⟩⟩

private theorem exists_hom_conj {D Ā : Subgroup Q}
    (ψ : ↥D ≃* alternatingGroup (Fin 6)) (hN : Ā ≤ Subgroup.normalizer (D : Set Q))
    (h3 : ∀ a ∈ Ā, a ^ 3 = 1) :
    ∃ θ : ↥Ā →* ↥D, ∀ (a : ↥Ā) (d : ↥D),
      ((θ a : ↥D) : Q) * d * ((θ a : ↥D) : Q)⁻¹ = a * d * a⁻¹ := by
  let σ : ↥Ā →* MulAut ↥D := (Subgroup.normalizerMonoidHom D).comp (Subgroup.inclusion hN)
  let τ : ↥Ā →* MulAut (alternatingGroup (Fin 6)) := (MulAut.congr ψ).toMonoidHom.comp σ
  have hτ3 : ∀ a : ↥Ā, τ a ^ 3 = 1 := by
    intro a
    rw [← map_pow]
    have : a ^ 3 = 1 := Subtype.ext (by simpa using h3 a a.2)
    rw [this, map_one]
  have hτ : ∀ a : ↥Ā, τ a ∈ (MulAut.conj : alternatingGroup (Fin 6) →*
      MulAut (alternatingGroup (Fin 6))).range := fun a =>
    Sec14.Item148PtRes.mem_inner_of_pow_three (hτ3 a)
  have hinj : Function.Injective (MulAut.conj : alternatingGroup (Fin 6) →*
      MulAut (alternatingGroup (Fin 6))) :=
    ComponentClassification.CatalogueSchreierAlternating.DegreeSix.inner_conjugation_injective
  let θ₀ : ↥Ā →* alternatingGroup (Fin 6) :=
    ((MonoidHom.ofInjective hinj).symm : _ ≃* alternatingGroup (Fin 6)).toMonoidHom.comp
      (τ.codRestrict _ hτ)
  refine ⟨ψ.symm.toMonoidHom.comp θ₀, fun a d => ?_⟩
  have h1 : MulAut.conj (θ₀ a) = τ a := MonoidHom.apply_ofInjective_symm hinj ⟨τ a, hτ a⟩
  have h2 : θ₀ a * ψ d * (θ₀ a)⁻¹ =
      ψ ⟨a * d * a⁻¹, (Subgroup.mem_normalizer_iff.mp (hN a.2) d).mp d.2⟩ := by
    rw [← MulAut.conj_apply, h1]
    simp only [τ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.congr_apply,
      MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    rfl
  have h3' : ψ.symm (θ₀ a) * d * (ψ.symm (θ₀ a))⁻¹ =
      ⟨a * d * a⁻¹, (Subgroup.mem_normalizer_iff.mp (hN a.2) d).mp d.2⟩ := by
    have := congrArg ψ.symm h2
    simpa only [map_mul, map_inv, MulEquiv.symm_apply_apply] using this
  exact congrArg Subtype.val h3'

private theorem pow_three_of_pow_nine :
    ∀ g : alternatingGroup (Fin 6), g ^ 9 = 1 → g ^ 3 = 1 := by
  decide +kernel

private theorem exists_sylow_centralizing [Finite Q] {D Ā : Subgroup Q}
    (ψ : ↥D ≃* alternatingGroup (Fin 6)) (θ : ↥Ā →* ↥D)
    (hθ : ∀ (a : ↥Ā) (d : ↥D), ((θ a : ↥D) : Q) * d * ((θ a : ↥D) : Q)⁻¹ = a * d * a⁻¹)
    (h3 : ∀ a ∈ Ā, a ^ 3 = 1) :
    ∃ E : Subgroup Q, E ≤ D ∧ Nat.card E = 9 ∧ (∀ e ∈ E, e ^ 3 = 1) ∧
      ∀ e ∈ E, ∀ a ∈ Ā, a * e = e * a := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hF : IsPGroup 3 θ.range := by
    intro f
    obtain ⟨a, ha⟩ := f.2
    refine ⟨1, ?_⟩
    apply Subtype.ext
    show (f : ↥D) ^ 3 ^ 1 = 1
    rw [pow_one, ← ha, ← map_pow]
    have : a ^ 3 = 1 := Subtype.ext (by simpa using h3 a a.2)
    rw [this, map_one]
  obtain ⟨S, hFS⟩ := hF.exists_le_sylow
  have hD360 : Nat.card ↥D = 360 := by
    rw [Nat.card_congr ψ.toEquiv]
    exact CFSG.QuasithinUnique.DoubleA3.card_alt6'
  have hS9 : Nat.card (S : Subgroup ↥D) = 3 ^ 2 := by
    rw [Sylow.card_eq_multiplicity, hD360]
    have : Nat.factorization 360 3 = 2 := by decide +kernel
    rw [this]
  have hcomm : IsMulCommutative (S : Subgroup ↥D) :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq hS9
  have hS3 : ∀ s ∈ (S : Subgroup ↥D), s ^ 3 = 1 := by
    intro s hs
    have h9 : s ^ 9 = 1 := by
      have := pow_card_eq_one' (G := (S : Subgroup ↥D)) (x := ⟨s, hs⟩)
      rw [hS9] at this
      exact congrArg Subtype.val this
    apply ψ.injective
    rw [map_pow, pow_three_of_pow_nine _ (by rw [← map_pow, h9, map_one]), map_one]
  refine ⟨(S : Subgroup ↥D).map D.subtype, Subgroup.map_subtype_le _, ?_, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective D.subtype_injective, hS9]
    norm_num
  · rintro _ ⟨s, hs, rfl⟩
    exact congrArg Subtype.val (hS3 s hs)
  · rintro _ ⟨s, hs, rfl⟩ a ha
    have h1 := hθ ⟨a, ha⟩ s
    have h2 : θ ⟨a, ha⟩ ∈ (S : Subgroup ↥D) := hFS ⟨⟨a, ha⟩, rfl⟩
    have h4 : θ ⟨a, ha⟩ * s = s * θ ⟨a, ha⟩ :=
      congrArg Subtype.val (hcomm.is_comm.comm (⟨θ ⟨a, ha⟩, h2⟩ : (S : Subgroup ↥D)) ⟨s, hs⟩)
    have h5 : ((θ ⟨a, ha⟩ : ↥D) : Q) * (s : Q) = (s : Q) * ((θ ⟨a, ha⟩ : ↥D) : Q) :=
      congrArg Subtype.val h4
    have h6 : ((θ ⟨a, ha⟩ : ↥D) : Q) * s * ((θ ⟨a, ha⟩ : ↥D) : Q)⁻¹ = s := by
      rw [h5]
      group
    have h7 : a * (s : Q) * a⁻¹ = s := by
      rw [h6] at h1
      exact h1.symm
    calc a * (s : Q) = a * s * a⁻¹ * a := by group
      _ = s * a := by rw [h7]

end Commutator

variable {Q : Type} [Group Q] [Finite Q]

theorem commutator_eq_top_of_elemAbelian {Ā J₁ J₂ : Subgroup Q}
    (hĀc : ∀ a ∈ Ā, ∀ b ∈ Ā, a * b = b * a) (hĀ3 : ∀ a ∈ Ā, a ^ 3 = 1)
    (hĀ27 : Nat.card Ā = 27)
    (hĀC : ∀ q ∈ Subgroup.centralizer (Ā : Set Q), q ^ 3 = 1 → q ∈ Ā)
    (hĀJ₁ : Ā ≤ Subgroup.normalizer (J₁ : Set Q)) (hĀJ₂ : Ā ≤ Subgroup.normalizer (J₂ : Set Q))
    (hJ : ⁅J₁, J₂⁆ = ⊥) (h3 : Nat.card ↥(J₁ ⊓ J₂) = 3)
    (hT₁ : Sec4.IsTripleCover ↥J₁ (alternatingGroup (Fin 6)))
    (hT₂ : Sec4.IsTripleCover ↥J₂ (alternatingGroup (Fin 6))) :
    commutator ↥J₁ = ⊤ := by
  by_contra hne
  have hZ₁ : J₁ ⊓ J₂ = Sec14.Item148PtRes.centerIn J₁ :=
    Sec14.Item148PtRes.inf_eq_centerIn_left hJ h3 hT₁.1
  have hZ₂ : J₁ ⊓ J₂ = Sec14.Item148PtRes.centerIn J₂ :=
    Sec14.Item148PtRes.inf_eq_centerIn_right hJ h3 hT₂.1
  obtain ⟨hDZ, ⟨ψ⟩⟩ := exists_equiv_commutator hT₁.1 hT₁.2.some hne
  rw [← hZ₁] at hDZ
  have hDJ : (⁅J₁, J₁⁆ : Subgroup Q) ≤ J₁ := Subgroup.commutator_le_self J₁
  have hĀD : Ā ≤ Subgroup.normalizer ((⁅J₁, J₁⁆ : Subgroup Q) : Set Q) := fun a ha =>
    mem_normalizer_commutator (hĀJ₁ ha)
  obtain ⟨θ, hθ⟩ := exists_hom_conj ψ hĀD hĀ3
  obtain ⟨E, hED, hE9, hE3, hEc⟩ := exists_sylow_centralizing ψ θ hθ hĀ3
  have hEĀ : E ≤ Ā := fun e he =>
    hĀC e (Subgroup.mem_centralizer_iff.mpr fun a ha => hEc e he a ha) (hE3 e he)
  have hZĀ : J₁ ⊓ J₂ ≤ Ā := by
    intro z hz
    have hz3 : z ^ 3 = 1 := by
      have h := Subgroup.orderOf_dvd_natCard (J₁ ⊓ J₂) hz
      rw [h3] at h
      exact orderOf_dvd_iff_pow_eq_one.mp h
    refine hĀC z (Subgroup.mem_centralizer_iff.mpr fun a ha => ?_) hz3
    have haZ : a ∈ Subgroup.normalizer ((J₁ ⊓ J₂ : Subgroup Q) : Set Q) := by
      refine Subgroup.mem_normalizer_iff.mpr fun x => ⟨fun hx => ⟨?_, ?_⟩, fun hx => ⟨?_, ?_⟩⟩
      · exact (Subgroup.mem_normalizer_iff.mp (hĀJ₁ ha) x).mp hx.1
      · exact (Subgroup.mem_normalizer_iff.mp (hĀJ₂ ha) x).mp hx.2
      · exact (Subgroup.mem_normalizer_iff.mp (hĀJ₁ ha) x).mpr hx.1
      · exact (Subgroup.mem_normalizer_iff.mp (hĀJ₂ ha) x).mpr hx.2
    have h1 := Sylow155T.conj_eq_of_card_le_three (Z := J₁ ⊓ J₂) (by rw [h3]) haZ (k := 1)
      (by simpa using hĀ3 a ha) hz
    calc a * z = a * z * a⁻¹ * a := by group
      _ = z * a := by rw [h1]
  have hB : Nat.card (Ā ⊓ J₁ : Subgroup Q) = 27 := by
    have hEB : E ≤ Ā ⊓ J₁ := le_inf hEĀ (hED.trans hDJ)
    have hZB : J₁ ⊓ J₂ ≤ Ā ⊓ J₁ := le_inf hZĀ inf_le_left
    have h9 : 9 ∣ Nat.card (Ā ⊓ J₁ : Subgroup Q) := by
      have := Subgroup.card_dvd_of_le hEB
      rwa [hE9] at this
    have h27 : Nat.card (Ā ⊓ J₁ : Subgroup Q) ∣ 27 := by
      have := Subgroup.card_dvd_of_le (inf_le_left : Ā ⊓ J₁ ≤ Ā)
      rwa [hĀ27] at this
    have hne9 : Nat.card (Ā ⊓ J₁ : Subgroup Q) ≠ 9 := by
      intro h
      have hEq : E = Ā ⊓ J₁ := Subgroup.eq_of_le_of_card_ge hEB (by rw [h, hE9])
      have hZE : J₁ ⊓ J₂ ≤ E := hEq ▸ hZB
      have hZD : J₁ ⊓ J₂ ≤ ⁅J₁, J₁⁆ ⊓ (J₁ ⊓ J₂) := le_inf (hZE.trans hED) le_rfl
      rw [hDZ, le_bot_iff] at hZD
      rw [hZD, Subgroup.card_bot] at h3
      omega
    have hpos : 0 < Nat.card (Ā ⊓ J₁ : Subgroup Q) := Nat.card_pos
    have hle : Nat.card (Ā ⊓ J₁ : Subgroup Q) ≤ 27 := Nat.le_of_dvd (by norm_num) h27
    rcases (by omega : Nat.card (Ā ⊓ J₁ : Subgroup Q) = 18 ∨
        Nat.card (Ā ⊓ J₁ : Subgroup Q) = 27) with h | h
    · rw [h] at h27
      omega
    · exact h
  have hĀJ : Ā ≤ J₁ := by
    have : (Ā ⊓ J₁ : Subgroup Q) = Ā :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by omega)
    rw [← this]
    exact inf_le_right
  obtain ⟨q, hq3, hqZ⟩ := exists_pow_three_not_mem_center hT₂
  have hqc : (q : Q) ∈ Subgroup.centralizer (Ā : Set Q) :=
    Subgroup.mem_centralizer_iff.mpr fun a ha =>
      Sec14.Item148PtRes.commute_of_commutator_eq_bot hJ (hĀJ ha) q.2
  have hqĀ : (q : Q) ∈ Ā := hĀC q hqc (congrArg Subtype.val hq3)
  have hqZ' : (q : Q) ∈ J₁ ⊓ J₂ := ⟨hĀJ hqĀ, q.2⟩
  rw [hZ₂] at hqZ'
  exact hqZ (Sec14.Item148PtRes.mem_centerIn_iff.mp hqZ').2

end CFSG.RankThree.PartTwo.Sec15.Sylow155NO
