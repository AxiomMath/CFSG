module

public import CFSG.OddTranspositions.PartThree.Twelve.Five
import CFSG.ClassicalGroups.Unitary.Transitivity
import CFSG.LocalAnalysis.WeakClosure81.W16Gt2KFactsI
import CFSG.LieType.Steinberg.CentralExt.UnitaryField
import CFSG.LinearAlgebra.LinearGroups.UnitaryVectorCount
import CFSG.OddTranspositions.WidthSylow
import CFSG.GH74.Generic.BProg.B3.S1IdentSl2
import CFSG.OddTranspositions.O4PairTenWidth
import CFSG.OddTranspositions.Width

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Open CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.LocalAnalysis.WeakClosure81 CFSG.LocalAnalysis.WeakClosure81.SevenK
  CFSG.OddTranspositions.PartFour

section VectorCount

variable {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}

theorem natCard_isotropic_ne_zero (hF : Nat.card F = (2 ^ f) ^ 2) (hf : 1 ≤ f) {m : ℕ}
    (hm : 1 ≤ m) :
    (Nat.card {v : Fin m → F // v ≠ 0 ∧ herm (unitaryInvolution F 2 f) v v = 0} : ℤ) =
      (((2 ^ f : ℕ) : ℤ) ^ m - (-1) ^ m) * (((2 ^ f : ℕ) : ℤ) ^ (m - 1) - (-1) ^ (m - 1)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set σ := unitaryInvolution F 2 f with hσdef
  have hσ : IsUnitaryInvolution σ := isUnitaryInvolution_unitaryInvolution hF
  have h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 f F :=
    ⟨Nat.prime_two, hf, by rw [hF, ← pow_mul, mul_comm]⟩
  have hbar : ∀ c, h.bar c = σ c := fun c => by
    rw [h.bar_apply, hσdef, unitaryInvolution_apply]
  let B : (Fin m → F) →ₛₗ[h.bar] (Fin m → F) →ₗ[F] F :=
    LinearMap.mk₂'ₛₗ h.bar (RingHom.id F) (fun x y => herm σ x y)
      (fun x x' y => herm_add_left σ x x' y)
      (fun c x y => by rw [herm_smul_left, hbar, smul_eq_mul])
      (fun x y y' => herm_add_right σ x y y')
      (fun c x y => by rw [herm_smul_right, smul_eq_mul, RingHom.id_apply])
  have hB : B.IsSymm := ⟨fun x y => by
    change h.bar (herm σ x y) = herm σ y x
    rw [hbar]
    exact (herm_conj σ hσ.invol x y).symm⟩
  have hBl : B.SeparatingLeft := fun x hx => eq_zero_of_herm σ hx
  have hdim : Module.finrank F (Fin m → F) = m := by simp
  exact (CFSG.LinearGroups.unitary_hermitian_vector_count h hB hBl hdim hm).2.2

theorem natCard_norm_eq_one (hF : Nat.card F = (2 ^ f) ^ 2) :
    Nat.card {l : F // unitaryInvolution F 2 f l * l = 1} = 2 ^ f + 1 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨l₀, -, hord⟩ := CFSG.LieType.Steinberg.exists_norm_one_orderOf_eq hF
  have hprim : IsPrimitiveRoot (l₀ : F) (2 ^ f + 1) := by
    rw [← hord, ← orderOf_units]
    exact IsPrimitiveRoot.orderOf _
  have hkey : ∀ l : F, unitaryInvolution F 2 f l * l = 1 ↔
      l ∈ Polynomial.nthRootsFinset (2 ^ f + 1) (1 : F) := by
    intro l
    rw [Polynomial.mem_nthRootsFinset (n := 2 ^ f + 1) (Nat.succ_pos _), unitaryInvolution_apply,
      pow_succ]
  rw [← hprim.card_nthRootsFinset, ← Nat.card_eq_finsetCard]
  exact Nat.card_congr (Equiv.subtypeEquivRight hkey)

theorem kFactsSuProj_suTv_eq_iff (hF : Nat.card F = (2 ^ f) ^ 2) {m : ℕ} (hm : 3 ≤ m)
    {v v' : Fin m → F} (hv0 : v ≠ 0) (hv : herm (unitaryInvolution F 2 f) v v = 0)
    (hv0' : v' ≠ 0) (hv' : herm (unitaryInvolution F 2 f) v' v' = 0) :
    kFactsSuProj hF m (suTv (isUnitaryInvolution_unitaryInvolution hF) v 1) =
        kFactsSuProj hF m (suTv (isUnitaryInvolution_unitaryInvolution hF) v' 1) ↔
      ∃ l : F, unitaryInvolution F 2 f l * l = 1 ∧ v' = l • v := by
  set σ := unitaryInvolution F 2 f with hσdef
  have hσ : IsUnitaryInvolution σ := isUnitaryInvolution_unitaryInvolution hF
  have h1 : (1 : F) + σ 1 = 0 := by rw [map_one]; exact CharTwo.add_self_eq_zero 1
  constructor
  · intro h12
    obtain ⟨μ, hμ⟩ := (kFacts_suProj_eq_iff hF _ _).mp h12
    have hact : ∀ y : Fin m → F, suTv hσ v' 1 • y = (μ : F) • (suTv hσ v 1 • y) := by
      intro y
      rw [smul_def, smul_def, hμ, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mulVec]
    obtain ⟨y₀, hy₀0, hy₀, hy₀'⟩ :
        ∃ y : Fin m → F, y ≠ 0 ∧ herm σ v y = 0 ∧ herm σ v' y = 0 := by
      let g : (Fin m → F) →ₗ[F] F × F := (hermL σ v).prod (hermL σ v')
      have hlt : Module.finrank F (F × F) < Module.finrank F (Fin m → F) := by
        rw [Module.finrank_prod, Module.finrank_self, Module.finrank_fin_fun]
        omega
      obtain ⟨y, hy, hy0⟩ :=
        Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt (f := g) hlt)
      have hy' := LinearMap.mem_ker.mp hy
      refine ⟨y, hy0, ?_, ?_⟩
      · have := congrArg Prod.fst hy'
        simpa [g] using this
      · have := congrArg Prod.snd hy'
        simpa [g] using this
    have hμ1 : (μ : F) = 1 := by
      have h2 := hact y₀
      simp only [suTv_smul hσ hv' h1, suTv_smul hσ hv h1, hy₀, hy₀', mul_zero, zero_smul,
        add_zero] at h2
      have h3 : ((μ : F) - 1) • y₀ = 0 := by rw [sub_smul, one_smul, ← h2, sub_self]
      exact sub_eq_zero.mp ((smul_eq_zero.mp h3).resolve_right hy₀0)
    have hall : ∀ y, herm σ v' y • v' = herm σ v y • v := by
      intro y
      have h2 := hact y
      rw [hμ1, one_smul, suTv_smul hσ hv' h1, suTv_smul hσ hv h1, one_mul, one_mul] at h2
      exact add_left_cancel h2
    obtain ⟨y, hy⟩ := exists_herm_ne_zero σ hv0'
    have hvl : v' = ((herm σ v' y)⁻¹ * herm σ v y) • v := by
      rw [mul_smul, ← hall y, smul_smul, inv_mul_cancel₀ hy, one_smul]
    refine ⟨(herm σ v' y)⁻¹ * herm σ v y, ?_, hvl⟩
    set l := (herm σ v' y)⁻¹ * herm σ v y with hl
    obtain ⟨z, hz⟩ := exists_herm_ne_zero σ hv0
    have h2 := hall z
    rw [hvl, herm_smul_left, smul_smul] at h2
    have h3 : (σ l * herm σ v z * l - herm σ v z) • v = 0 := by rw [sub_smul, h2, sub_self]
    have h4 := (smul_eq_zero.mp h3).resolve_right hv0
    have h5 : (σ l * l - 1) * herm σ v z = 0 := by linear_combination h4
    exact sub_eq_zero.mp ((mul_eq_zero.mp h5).resolve_right hz)
  · rintro ⟨l, hl, rfl⟩
    rw [suTv_smul_eq hσ hv l h1, mul_one, hl]

theorem natCard_trace_eq (hF : Nat.card F = (2 ^ f) ^ 2) {t : F}
    (ht : unitaryInvolution F 2 f t = t) :
    Nat.card {x : F // x + unitaryInvolution F 2 f x = t} = 2 ^ f := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set σ := unitaryInvolution F 2 f with hσdef
  have hσ : IsUnitaryInvolution σ := isUnitaryInvolution_unitaryInvolution hF
  obtain ⟨x₀, hx₀⟩ := hσ.trace_surj t ht
  rw [← CFSG.LieType.Steinberg.card_traceZero hF]
  refine Nat.card_congr
    { toFun := fun x => ⟨x.1 - x₀, ?_⟩
      invFun := fun y => ⟨y.1 + x₀, ?_⟩
      left_inv := fun x => Subtype.ext (sub_add_cancel _ _)
      right_inv := fun y => Subtype.ext (add_sub_cancel_right _ _) }
  · change x.1 - x₀ + σ (x.1 - x₀) = 0
    rw [map_sub]
    linear_combination x.2 - hx₀
  · have hy : y.1 + σ y.1 = 0 := y.2
    rw [map_add]
    linear_combination hy + hx₀

theorem natCard_isotropic_herm_eq (hF : Nat.card F = (2 ^ f) ^ 2) {m : ℕ} (hm : 2 ≤ m)
    {u : Fin m → F} (hu0 : u ≠ 0) (hu : herm (unitaryInvolution F 2 f) u u = 0) {c : F}
    (hc : c ≠ 0) :
    Nat.card {v : Fin m → F // herm (unitaryInvolution F 2 f) v v = 0 ∧
      herm (unitaryInvolution F 2 f) u v = c} = (2 ^ f) ^ (2 * m - 3) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set σ := unitaryInvolution F 2 f with hσdef
  have hσ : IsUnitaryInvolution σ := isUnitaryInvolution_unitaryInvolution hF
  have hinv := hσ.invol
  obtain ⟨u', hu', huu'⟩ := exists_partner hσ hu0 hu
  have hu'u : herm σ u' u = 1 := by rw [herm_conj σ hinv, huu', map_one]
  let g : (Fin m → F) →ₗ[F] F × F := (hermL σ u).prod (hermL σ u')
  have hmemW : ∀ w, w ∈ LinearMap.ker g ↔ herm σ u w = 0 ∧ herm σ u' w = 0 := by
    intro w
    simp [g, LinearMap.mem_ker]
  have hgsurj : Function.Surjective g := by
    rintro ⟨a, b⟩
    refine ⟨a • u' + b • u, ?_⟩
    change (herm σ u (a • u' + b • u), herm σ u' (a • u' + b • u)) = (a, b)
    simp only [herm_add_right, herm_smul_right, huu', hu, hu', hu'u, mul_one, mul_zero, add_zero,
      zero_add]
  have hW : Nat.card (LinearMap.ker g) = (2 ^ f) ^ (2 * (m - 2)) := by
    have hrank := LinearMap.finrank_range_add_finrank_ker g
    rw [LinearMap.range_eq_top.mpr hgsurj, finrank_top, Module.finrank_prod, Module.finrank_self,
      Module.finrank_fin_fun] at hrank
    rw [Module.natCard_eq_pow_finrank (K := F), hF, ← pow_mul]
    congr 1
    omega
  have hexp : ∀ (a : F) (w : Fin m → F), herm σ u w = 0 → herm σ u' w = 0 →
      herm σ (a • u + c • u' + w) (a • u + c • u' + w) = σ a * c + σ c * a + herm σ w w := by
    intro a w hw hw'
    have hwu : herm σ w u = 0 := herm_eq_zero_comm σ hinv hw
    have hwu' : herm σ w u' = 0 := herm_eq_zero_comm σ hinv hw'
    simp only [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right, hu, hu', huu',
      hu'u, hw, hw', hwu, hwu']
    ring
  let P := {p : F × LinearMap.ker g // σ p.1 * c + σ c * p.1 = herm σ p.2.1 p.2.1}
  have hP : Nat.card {v : Fin m → F // herm σ v v = 0 ∧ herm σ u v = c} = Nat.card P := by
    refine Nat.card_congr
      { toFun := fun v => ⟨(herm σ u' v.1, ⟨v.1 - herm σ u' v.1 • u - c • u', ?_⟩), ?_⟩
        invFun := fun p => ⟨p.1.1 • u + c • u' + p.1.2.1, ?_, ?_⟩
        left_inv := fun v => Subtype.ext (by simp)
        right_inv := fun p => ?_ }
    · rw [hmemW]
      constructor
      · simp only [herm_sub_right, herm_smul_right, hu, huu', v.2.2, mul_zero, mul_one, sub_zero,
          sub_self]
      · simp only [herm_sub_right, herm_smul_right, hu', hu'u, mul_zero, mul_one,
          sub_self]
    · have hw := (hmemW _).mp (show v.1 - herm σ u' v.1 • u - c • u' ∈ LinearMap.ker g from by
        rw [hmemW]
        constructor
        · simp only [herm_sub_right, herm_smul_right, hu, huu', v.2.2, mul_zero, mul_one,
            sub_zero, sub_self]
        · simp only [herm_sub_right, herm_smul_right, hu', hu'u, mul_zero, mul_one,
            sub_self])
      have h2 := hexp (herm σ u' v.1) _ hw.1 hw.2
      have hv : herm σ u' v.1 • u + c • u' + (v.1 - herm σ u' v.1 • u - c • u') = v.1 := by abel
      rw [hv, v.2.1] at h2
      change σ (herm σ u' v.1) * c + σ c * herm σ u' v.1 =
        herm σ (v.1 - herm σ u' v.1 • u - c • u') (v.1 - herm σ u' v.1 • u - c • u')
      rw [← sub_eq_zero, CharTwo.sub_eq_add]
      exact h2.symm
    · have hw := (hmemW _).mp p.1.2.2
      rw [hexp _ _ hw.1 hw.2, p.2]
      exact CharTwo.add_self_eq_zero _
    · have hw := (hmemW _).mp p.1.2.2
      simp only [herm_add_right, herm_smul_right, hu, huu', hw.1, mul_zero, mul_one, zero_add,
        add_zero]
    · obtain ⟨⟨a, w, hwmem⟩, hp⟩ := p
      have hw := (hmemW _).mp hwmem
      refine Subtype.ext (Prod.ext ?_ (Subtype.ext ?_))
      · simp only [herm_add_right, herm_smul_right, hu', hu'u, hw.2, mul_zero, mul_one,
          add_zero]
      · simp only [herm_add_right, herm_smul_right, hu', hu'u, hw.2, mul_zero, mul_one,
          add_zero]
        abel
  have hfib : ∀ w : LinearMap.ker g,
      Nat.card {a : F // σ a * c + σ c * a = herm σ w.1 w.1} = 2 ^ f := by
    intro w
    rw [← natCard_trace_eq hF (herm_self_fixed σ hinv w.1)]
    refine Nat.card_congr
      { toFun := fun a => ⟨σ a.1 * c, ?_⟩
        invFun := fun x => ⟨σ (x.1 * c⁻¹), ?_⟩
        left_inv := fun a => Subtype.ext (by simp [hinv, mul_inv_cancel_right₀ hc])
        right_inv := fun x => Subtype.ext (by simp [hinv, inv_mul_cancel_right₀ hc]) }
    · change σ a.1 * c + σ (σ a.1 * c) = herm σ w.1 w.1
      rw [map_mul, hinv]
      linear_combination a.2
    · have hc' : σ c ≠ 0 := (map_ne_zero σ).mpr hc
      rw [hinv, map_mul, map_inv₀, mul_assoc, inv_mul_cancel₀ hc, mul_one, mul_left_comm,
        mul_inv_cancel₀ hc', mul_one]
      exact x.2
  have hPcard : Nat.card P = Nat.card (LinearMap.ker g) * 2 ^ f := by
    have e : P ≃ Σ w : LinearMap.ker g, {a : F // σ a * c + σ c * a = herm σ w.1 w.1} :=
      { toFun := fun p => ⟨p.1.2, p.1.1, p.2⟩
        invFun := fun q => ⟨(q.2.1, q.1), q.2.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    have : Fintype (LinearMap.ker g) := Fintype.ofFinite _
    rw [Nat.card_congr e, Nat.card_sigma]
    simp only [hfib, Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.card_eq_fintype_card]
  rw [hP, hPcard, hW, ← pow_succ]
  congr 1
  omega

theorem natCard_isotropic_herm_ne_zero (hF : Nat.card F = (2 ^ f) ^ 2) {m : ℕ} (hm : 2 ≤ m)
    {u : Fin m → F} (hu0 : u ≠ 0) (hu : herm (unitaryInvolution F 2 f) u u = 0) :
    Nat.card {v : Fin m → F // herm (unitaryInvolution F 2 f) v v = 0 ∧
      herm (unitaryInvolution F 2 f) u v ≠ 0} = ((2 ^ f) ^ 2 - 1) * (2 ^ f) ^ (2 * m - 3) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set σ := unitaryInvolution F 2 f with hσdef
  let φ : {v : Fin m → F // herm σ v v = 0 ∧ herm σ u v ≠ 0} → {c : F // c ≠ 0} :=
    fun v => ⟨herm σ u v.1, v.2.2⟩
  have hfib : ∀ c : {c : F // c ≠ 0}, Nat.card {v // φ v = c} = (2 ^ f) ^ (2 * m - 3) := by
    intro c
    rw [← natCard_isotropic_herm_eq hF hm hu0 hu c.2]
    exact Nat.card_congr
      { toFun := fun v => ⟨v.1.1, v.1.2.1, congrArg Subtype.val v.2⟩
        invFun := fun v => ⟨⟨v.1, v.2.1, by rw [v.2.2]; exact c.2⟩, Subtype.ext v.2.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have : Fintype {c : F // c ≠ 0} := Fintype.ofFinite _
  rw [Nat.card_congr (Equiv.sigmaFiberEquiv φ).symm, Nat.card_sigma,
    Finset.sum_congr rfl fun c _ => hfib c, Finset.sum_const, Finset.card_univ, smul_eq_mul,
    ← Nat.card_eq_fintype_card, Nat.card_congr unitsEquivNeZero.symm,
    CFSG.ClassicalGroups.Unitary.card_units_of_card hF]

end VectorCount

theorem ncard_of_isUnitaryTransvection {X : Type} [Group X] {E : Set X}
    (hcls : ∃ d₀ : X, E = {g | IsConj d₀ g}) (hZ : Subgroup.center X = ⊥) {s : X} (hs : s ∈ E)
    {m f : ℕ} (hm : 3 ≤ m) (h : IsUnitaryTransvection X m f s) :
    ((E.ncard * (2 ^ f + 1) : ℕ) : ℤ) =
        (((2 ^ f : ℕ) : ℤ) ^ m - (-1) ^ m) * (((2 ^ f : ℕ) : ℤ) ^ (m - 1) - (-1) ^ (m - 1)) ∧
      {x ∈ E | ¬ Commute x s}.ncard * (2 ^ f + 1) = ((2 ^ f) ^ 2 - 1) * (2 ^ f) ^ (2 * m - 3) := by
  classical
  obtain ⟨F, _, _, hF, e, hrank⟩ := h
  have : Fintype F := Fintype.ofFinite F
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2 * f)
    (by rw [← Nat.card_eq_fintype_card, hF, ← pow_mul, mul_comm])
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h0 | h0
    · have h2 := Finite.one_lt_card (α := F)
      rw [hF, h0] at h2
      norm_num at h2
    · exact h0
  set σ := unitaryInvolution F 2 f with hσdef
  have hσ : IsUnitaryInvolution σ := isUnitaryInvolution_unitaryInvolution hF
  have h1 : (1 : F) + σ 1 = 0 := by rw [map_one]; exact CharTwo.add_self_eq_zero 1
  set π := kFactsSuProj hF m with hπdef
  have hπsurj : Function.Surjective π := kFacts_suProj_surjective hF m
  set ψ : X →* StatedProj (StatedSU m (2 ^ f) F) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center X)) with hψdef
  have hψinj : Function.Injective ψ := by
    intro a b hab
    have h2 : QuotientGroup.mk' (Subgroup.center X) a = QuotientGroup.mk' (Subgroup.center X) b :=
      e.injective hab
    rw [QuotientGroup.mk'_eq_mk'] at h2
    obtain ⟨z, hz, hzb⟩ := h2
    rw [hZ, Subgroup.mem_bot] at hz
    rw [hz, mul_one] at hzb
    exact hzb
  have hψsurj : Function.Surjective ψ :=
    e.surjective.comp (QuotientGroup.mk'_surjective _)
  obtain ⟨u, hu0, hu, hψs⟩ := kFacts_su_exists_centre hF hrank
  change ψ s = π (suTv hσ u 1) at hψs
  replace hu : herm σ u u = 0 := hu
  have hEs : ∀ x, x ∈ E ↔ IsConj s x := by
    obtain ⟨d₀, rfl⟩ := hcls
    intro x
    exact ⟨fun hx => (isConj_comm.mp hs).trans hx, fun hx => (show IsConj d₀ s from hs).trans hx⟩
  have hEmem : ∀ v, v ≠ 0 → herm σ v v = 0 → ∃ y ∈ E, ψ y = π (suTv hσ v 1) := by
    intro v hv0 hv
    obtain ⟨t, -, ht⟩ := exists_mem_T_smul_eq_of_iso hσ hm hu0 hu hv0 hv
    obtain ⟨g, hg⟩ := hψsurj (π t)
    refine ⟨g * s * g⁻¹, (hEs _).mpr (isConj_iff.mpr ⟨g, rfl⟩), ?_⟩
    rw [map_mul, map_mul, map_inv, hg, hψs, ← map_inv, ← map_mul, ← map_mul,
      suTv_conj hσ t hu h1, ht]
  have hEtr : ∀ x ∈ E, ∃ v, v ≠ 0 ∧ herm σ v v = 0 ∧ ψ x = π (suTv hσ v 1) := by
    intro x hx
    obtain ⟨g, rfl⟩ := isConj_iff.mp ((hEs x).mp hx)
    obtain ⟨g', hg'⟩ := hπsurj (ψ g)
    refine ⟨g' • u, fun h0 => hu0 (by rw [← inv_smul_smul g' u, h0, smul_zero]),
      by rw [herm_smul_smul, hu], ?_⟩
    rw [map_mul, map_mul, map_inv, hψs, ← hg', ← map_inv, ← map_mul, ← map_mul,
      suTv_conj hσ g' hu h1]
  let S := {v : Fin m → F // v ≠ 0 ∧ herm σ v v = 0}
  have hΦ : ∀ v : S, ∃ y ∈ E, ψ y = π (suTv hσ v.1 1) := fun v => hEmem v.1 v.2.1 v.2.2
  let Φ : S → E := fun v => ⟨(hΦ v).choose, (hΦ v).choose_spec.1⟩
  have hΦψ : ∀ v : S, ψ (Φ v) = π (suTv hσ v.1 1) := fun v => (hΦ v).choose_spec.2
  have hfib : ∀ v w : S, Φ v = Φ w ↔ ∃ l : F, σ l * l = 1 ∧ w.1 = l • v.1 := by
    intro v w
    rw [← kFactsSuProj_suTv_eq_iff hF hm v.2.1 v.2.2 w.2.1 w.2.2]
    change Φ v = Φ w ↔ π (suTv hσ v.1 1) = π (suTv hσ w.1 1)
    rw [← hΦψ, ← hΦψ]
    exact ⟨fun h => congrArg _ (congrArg Subtype.val h), fun h => Subtype.ext (hψinj h)⟩
  have hΦsurj : Function.Surjective Φ := by
    rintro ⟨x, hx⟩
    obtain ⟨v, hv0, hv, hψx⟩ := hEtr x hx
    exact ⟨⟨v, hv0, hv⟩, Subtype.ext (hψinj (by rw [hΦψ, hψx]))⟩
  have hcardfib : ∀ y : E, Nat.card {v : S // Φ v = y} = 2 ^ f + 1 := by
    intro y
    obtain ⟨v₀, rfl⟩ := hΦsurj y
    rw [← natCard_norm_eq_one hF]
    let g : {l : F // σ l * l = 1} → {v : S // Φ v = Φ v₀} := fun l =>
      ⟨⟨l.1 • v₀.1, smul_ne_zero (right_ne_zero_of_mul_eq_one l.2) v₀.2.1, by
        rw [herm_smul_left, herm_smul_right, v₀.2.2, mul_zero, mul_zero]⟩,
        ((hfib v₀ _).mpr ⟨l.1, l.2, rfl⟩).symm⟩
    have hg : Function.Bijective g := by
      refine ⟨fun l l' hll' => Subtype.ext ?_, fun w => ?_⟩
      · have h2 := congrArg (fun w => w.1.1) hll'
        exact smul_left_injective F v₀.2.1 h2
      · obtain ⟨l, hl, hw⟩ := (hfib v₀ w.1).mp w.2.symm
        exact ⟨⟨l, hl⟩, Subtype.ext (Subtype.ext hw.symm)⟩
    exact (Nat.card_congr (Equiv.ofBijective g hg)).symm
  have hcommE : ∀ v : S, Commute (Φ v : X) s ↔ herm σ u v.1 = 0 := by
    intro v
    have hc : Commute (Φ v : X) s ↔ Commute (ψ (Φ v)) (ψ s) :=
      ⟨fun h => h.map ψ, fun h => hψinj (by rw [map_mul, map_mul]; exact h.eq)⟩
    rw [hc, hΦψ, hψs]
    constructor
    · intro h
      exact herm_eq_zero_comm σ hσ.invol (herm_eq_zero_of_commute_kFactsSuProjTv hF hm v.2.1
        v.2.2 hu h)
    · intro h
      exact kFacts_suProjTv_comm_of_herm_eq_zero hF v.2.2 hu (herm_eq_zero_comm σ hσ.invol h)
        h1 h1
  have hsum : ∀ A : Set E, Nat.card {v : S // Φ v ∈ A} = Nat.card A * (2 ^ f + 1) := by
    intro A
    have : Finite A := Finite.of_surjective (fun v : {v : S // Φ v ∈ A} => (⟨Φ v.1, v.2⟩ : A))
      (fun y => by
        obtain ⟨v, hv⟩ := hΦsurj y.1
        exact ⟨⟨v, by rw [hv]; exact y.2⟩, Subtype.ext hv⟩)
    have : Fintype A := Fintype.ofFinite A
    have hfib' : ∀ y : A, Nat.card {v : {v : S // Φ v ∈ A} // (⟨Φ v.1, v.2⟩ : A) = y} =
        2 ^ f + 1 := by
      intro y
      rw [← hcardfib y.1]
      exact Nat.card_congr
        { toFun := fun v => ⟨v.1.1, congrArg Subtype.val v.2⟩
          invFun := fun v => ⟨⟨v.1, by rw [v.2]; exact y.2⟩, Subtype.ext v.2⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
    rw [Nat.card_congr (Equiv.sigmaFiberEquiv
        (fun v : {v : S // Φ v ∈ A} => (⟨Φ v.1, v.2⟩ : A))).symm, Nat.card_sigma,
      Finset.sum_congr rfl fun y _ => hfib' y, Finset.sum_const, Finset.card_univ, smul_eq_mul,
      ← Nat.card_eq_fintype_card]
  refine ⟨?_, ?_⟩
  · have hS : Nat.card S = E.ncard * (2 ^ f + 1) := by
      rw [← Nat.card_coe_set_eq, ← Nat.card_univ (α := E), ← hsum Set.univ]
      exact Nat.card_congr (Equiv.subtypeUnivEquiv fun v => Set.mem_univ _).symm
    rw [← hS]
    exact natCard_isotropic_ne_zero hF hf (by omega)
  · have h2 := hsum {x : E | ¬ Commute (x : X) s}
    have hA : Nat.card {x : E | ¬ Commute (x : X) s} = {x ∈ E | ¬ Commute x s}.ncard := by
      rw [← Nat.card_coe_set_eq]
      exact Nat.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter (· ∈ E) (¬ Commute · s))
    have hB : Nat.card {v : S // Φ v ∈ {x : E | ¬ Commute (x : X) s}} =
        Nat.card {v : Fin m → F // herm σ v v = 0 ∧ herm σ u v ≠ 0} := by
      refine Nat.card_congr
        { toFun := fun v => ⟨v.1.1, v.1.2.2, fun h0 => v.2 ((hcommE v.1).mpr h0)⟩
          invFun := fun v => ⟨⟨v.1, fun h0 => v.2.2 (by rw [h0, herm_zero_right]), v.2.1⟩,
            fun hc => v.2.2 ((hcommE _).mp hc)⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
    rw [← hA, ← h2, hB, natCard_isotropic_herm_ne_zero hF (by omega) hu0 hu]

theorem ncard_of_isUnitaryTransvection_four {X : Type} [Group X] {E : Set X}
    (hcls : ∃ d₀ : X, E = {g | IsConj d₀ g}) (hZ : Subgroup.center X = ⊥) {s : X} (hs : s ∈ E)
    {f : ℕ} (h : IsUnitaryTransvection X 4 f s) :
    E.ncard = (2 ^ f - 1) * ((2 ^ f) ^ 2 + 1) * ((2 ^ f) ^ 3 + 1) ∧
      {x ∈ E | ¬ Commute x s}.ncard = (2 ^ f - 1) * (2 ^ f) ^ 5 := by
  obtain ⟨h1, h2⟩ := ncard_of_isUnitaryTransvection hcls hZ hs (by norm_num) h
  obtain ⟨r, hr⟩ : ∃ r, 2 ^ f = r + 1 :=
    ⟨2 ^ f - 1, (Nat.succ_pred_eq_of_pos (Nat.two_pow_pos f)).symm⟩
  rw [hr] at h1 h2 ⊢
  simp only [Nat.add_sub_cancel]
  refine ⟨?_, ?_⟩
  · have h3 : (E.ncard : ℤ) * ((r : ℤ) + 1 + 1) =
        ((r : ℤ) * (((r : ℤ) + 1) ^ 2 + 1) * (((r : ℤ) + 1) ^ 3 + 1)) * ((r : ℤ) + 1 + 1) := by
      push_cast at h1
      rw [h1]
      norm_num
      ring
    have h4 := mul_right_cancel₀ (by positivity) h3
    exact_mod_cast h4
  · have h3 : {x ∈ E | ¬ Commute x s}.ncard * (r + 1 + 1) = r * (r + 1) ^ 5 * (r + 1 + 1) := by
      rw [h2, show (r + 1) ^ 2 - 1 = r * (r + 2) from Nat.sub_eq_of_eq_add (by ring)]
      ring
    exact Nat.eq_of_mul_eq_mul_right (Nat.succ_pos _) h3

section OrthogonalSubgroup

open Matrix

variable {F : Type} [Field F] {σ : F ≃+* F} {m : ℕ}

structure IsFixedQuadForm (σ : F ≃+* F) (U : AddSubgroup (Fin m → F))
    (Q : (Fin m → F) → F) : Prop where
  smul_mem : ∀ c : F, σ c = c → ∀ x ∈ U, c • x ∈ U
  exists_basis : ∃ b : Fin m → Fin m → F, (∀ i, b i ∈ U) ∧ (Matrix.of b).det ≠ 0 ∧
    ∀ x ∈ U, ∃ c : Fin m → F, (∀ i, σ (c i) = c i) ∧ x = ∑ i, c i • b i
  fix : ∀ x ∈ U, σ (Q x) = Q x
  smul : ∀ c : F, σ c = c → ∀ x ∈ U, Q (c • x) = c ^ 2 * Q x
  add : ∀ x ∈ U, ∀ y ∈ U, Q (x + y) = Q x + Q y + herm σ x y

theorem exists_fix_sq_eq [Finite F] [CharP F 2] {c : F} (hc : σ c = c) :
    ∃ s : F, σ s = s ∧ s ^ 2 = c := by
  obtain ⟨s, hs⟩ := surjective_frobenius F 2 c
  rw [frobenius_def] at hs
  refine ⟨s, frobenius_inj F 2 ?_, hs⟩
  rw [frobenius_def, frobenius_def, ← map_pow, hs, hc]

theorem eq_one_of_fix_of_norm [CharP F 2] {μ : F} (hμ : σ μ = μ) (hN : σ μ * μ = 1) : μ = 1 := by
  rw [hμ] at hN
  have h : (μ + 1) ^ 2 = 0 := by
    have e : (μ + 1) ^ 2 = μ * μ + 1 + (2 : F) * μ := by ring
    rw [e, hN, CharTwo.two_eq_zero, zero_mul, add_zero, CharTwo.add_self_eq_zero]
  have h1 : μ + 1 = 0 := (pow_eq_zero_iff two_ne_zero).mp h
  rw [← CharTwo.neg_eq μ]
  linear_combination -h1

theorem exists_mem_three_ne_zero [CharP F 2] {lam : F} (hlam0 : lam ≠ 0) (hlam1 : lam ≠ 1)
    (c a : F) : ∃ t : F, (t = 0 ∨ t = 1 ∨ t = lam) ∧ c + t ^ 2 + t * a ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have h0 := hcon 0 (Or.inl rfl)
  have h1 := hcon 1 (Or.inr (Or.inl rfl))
  have hl := hcon lam (Or.inr (Or.inr rfl))
  simp only [zero_pow two_ne_zero, add_zero, zero_mul] at h0
  have ha : a = 1 := by
    rw [h0, zero_add, one_pow, one_mul] at h1
    rw [← CharTwo.neg_eq a]
    linear_combination -h1
  rw [h0, ha, zero_add, mul_one] at hl
  have : lam * (lam + 1) = 0 := by linear_combination hl
  rcases mul_eq_zero.mp this with h | h
  · exact hlam0 h
  · apply hlam1
    rw [← CharTwo.neg_eq lam]
    linear_combination -h

namespace IsFixedQuadForm

variable {U : AddSubgroup (Fin m → F)} {Q : (Fin m → F) → F}

section Basic

variable (hU : IsFixedQuadForm σ U Q)
include hU

theorem Q_zero : Q 0 = 0 := by
  have h := hU.smul 0 (map_zero σ) 0 U.zero_mem
  rwa [zero_smul, zero_pow two_ne_zero, zero_mul] at h

theorem herm_self [CharP F 2] {x : Fin m → F} (hx : x ∈ U) : herm σ x x = 0 := by
  have h := hU.add x hx x hx
  rw [← two_smul F x, CharTwo.two_eq_zero, zero_smul, hU.Q_zero, CharTwo.add_self_eq_zero,
    zero_add] at h
  exact h.symm

theorem herm_fix {x y : Fin m → F} (hx : x ∈ U) (hy : y ∈ U) :
    σ (herm σ x y) = herm σ x y := by
  have h := hU.add x hx y hy
  have hxy : herm σ x y = Q (x + y) - Q x - Q y := by rw [h]; ring
  rw [hxy, map_sub, map_sub, hU.fix _ (U.add_mem hx hy), hU.fix x hx, hU.fix y hy]

theorem herm_comm {x y : Fin m → F} (hx : x ∈ U) (hy : y ∈ U) : herm σ y x = herm σ x y := by
  have h1 := hU.add x hx y hy
  have h2 := hU.add y hy x hx
  rw [add_comm y x, h1] at h2
  linear_combination -h2

theorem eq_zero_of_forall_herm {a : Fin m → F} (h : ∀ x ∈ U, herm σ a x = 0) : a = 0 := by
  obtain ⟨b, hbU, hdet, -⟩ := hU.exists_basis
  refine eq_zero_of_herm σ fun y => ?_
  have hy : y = ∑ i, (y ᵥ* (Matrix.of b)⁻¹) i • b i := by
    have h1 : (y ᵥ* (Matrix.of b)⁻¹) ᵥ* Matrix.of b = y := by
      rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet),
        Matrix.vecMul_one]
    conv_lhs => rw [← h1]
    rw [Matrix.vecMul_eq_sum]
    rfl
  rw [hy, ← hermL_apply, map_sum]
  exact Finset.sum_eq_zero fun i _ => by
    rw [map_smul, hermL_apply, h _ (hbU i), smul_zero]

theorem exists_herm_eq_one_of_mem {x : Fin m → F} (hx : x ∈ U) (hx0 : x ≠ 0) :
    ∃ y ∈ U, herm σ x y = 1 := by
  by_contra hcon
  push Not at hcon
  refine hx0 (hU.eq_zero_of_forall_herm fun y hy => ?_)
  by_contra hxy
  have hfix : σ (herm σ x y)⁻¹ = (herm σ x y)⁻¹ := by rw [map_inv₀, hU.herm_fix hx hy]
  exact hcon _ (hU.smul_mem _ hfix y hy) (by rw [herm_smul_right, inv_mul_cancel₀ hxy])

theorem exists_smul_of_Q_ne_zero [Finite F] [CharP F 2] {x : Fin m → F} (hx : x ∈ U)
    (hQ : Q x ≠ 0) : ∃ s : F, σ s = s ∧ s ≠ 0 ∧ s ^ 2 = Q x ∧ s⁻¹ • x ∈ U ∧
      Q (s⁻¹ • x) = 1 := by
  obtain ⟨s, hs, hs2⟩ := exists_fix_sq_eq (hU.fix x hx)
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [zero_pow two_ne_zero] at hs2
    exact hQ hs2.symm
  have hsi : σ s⁻¹ = s⁻¹ := by rw [map_inv₀, hs]
  refine ⟨s, hs, hs0, hs2, hU.smul_mem _ hsi x hx, ?_⟩
  rw [hU.smul _ hsi x hx, ← hs2, inv_pow, inv_mul_cancel₀ (pow_ne_zero 2 hs0)]

theorem exists_add_of_Q_eq_zero [CharP F 2] {lam : F} (hlam : σ lam = lam) (hlam0 : lam ≠ 0)
    (hlam1 : lam ≠ 1) {x : Fin m → F} (hx : x ∈ U) (hx0 : x ≠ 0) (hQ : Q x = 0) :
    ∃ x₁ ∈ U, ∃ x₂ ∈ U, Q x₁ ≠ 0 ∧ Q x₂ ≠ 0 ∧ x = x₁ + x₂ := by
  obtain ⟨y, hy, hxy⟩ := hU.exists_herm_eq_one_of_mem hx hx0
  have hyx : herm σ y x = 1 := by rw [hU.herm_comm hx hy, hxy]
  have hQt : ∀ t : F, σ t = t → Q (y + t • x) = Q y + t := by
    intro t ht
    rw [hU.add y hy _ (hU.smul_mem t ht x hx), hU.smul t ht x hx, hQ, mul_zero, add_zero,
      herm_smul_right, hyx, mul_one]
  have hfix : σ (Q y + lam) = Q y + lam := by rw [map_add, hU.fix y hy, hlam]
  have hfix1 : σ (Q y + lam + 1) = Q y + lam + 1 := by rw [map_add, hfix, map_one]
  refine ⟨y + (Q y + lam) • x, U.add_mem hy (hU.smul_mem _ hfix x hx),
    y + (Q y + lam + 1) • x, U.add_mem hy (hU.smul_mem _ hfix1 x hx), ?_, ?_, ?_⟩
  · rw [hQt _ hfix, ← add_assoc, CharTwo.add_self_eq_zero, zero_add]
    exact hlam0
  · rw [hQt _ hfix1, ← add_assoc, ← add_assoc, CharTwo.add_self_eq_zero, zero_add]
    intro h
    apply hlam1
    rw [← CharTwo.neg_eq lam]
    linear_combination -h
  · have h2 : y + (Q y + lam) • x + (y + (Q y + lam + 1) • x) =
        x + (2 : F) • (y + (Q y + lam) • x) := by module
    rw [h2, CharTwo.two_eq_zero, zero_smul, add_zero]

theorem exists_Q_eq_one [Finite F] [CharP F 2] {x : Fin m → F} (hx : x ∈ U) (hx0 : x ≠ 0) :
    ∃ v ∈ U, Q v = 1 := by
  by_cases hQ : Q x = 0
  · obtain ⟨y, hy, hxy⟩ := hU.exists_herm_eq_one_of_mem hx hx0
    have hfix : σ (Q y + 1) = Q y + 1 := by rw [map_add, hU.fix y hy, map_one]
    refine ⟨y + (Q y + 1) • x, U.add_mem hy (hU.smul_mem _ hfix x hx), ?_⟩
    rw [hU.add y hy _ (hU.smul_mem _ hfix x hx), hU.smul _ hfix x hx, hQ, mul_zero, add_zero,
      herm_smul_right, hU.herm_comm hx hy, hxy, mul_one, ← add_assoc, CharTwo.add_self_eq_zero,
      zero_add]
  · obtain ⟨s, -, -, -, hu, hQu⟩ := hU.exists_smul_of_Q_ne_zero hx hQ
    exact ⟨_, hu, hQu⟩

theorem exists_Q_eq_one_herm_ne_zero [Finite F] [CharP F 2] {lam : F} (hlam : σ lam = lam)
    (hlam0 : lam ≠ 0) (hlam1 : lam ≠ 1) {v w : Fin m → F} (hv : v ∈ U) (hw : w ∈ U)
    (hQv : Q v = 1) (hvw : herm σ v w = 0) (hv0 : v ≠ 0) (hw0 : w ≠ 0) :
    ∃ z ∈ U, Q z = 1 ∧ herm σ v z ≠ 0 ∧ herm σ w z ≠ 0 := by
  obtain ⟨zv, hzv, hvzv⟩ := hU.exists_herm_eq_one_of_mem hv hv0
  obtain ⟨zw, hzw, hwzw⟩ := hU.exists_herm_eq_one_of_mem hw hw0
  obtain ⟨z₁, hz₁, hvz₁, hwz₁⟩ : ∃ z₁ ∈ U, herm σ v z₁ ≠ 0 ∧ herm σ w z₁ ≠ 0 := by
    by_cases h1 : herm σ w zv = 0
    · by_cases h2 : herm σ v zw = 0
      · refine ⟨zv + zw, U.add_mem hzv hzw, ?_, ?_⟩
        · rw [herm_add_right, hvzv, h2, add_zero]
          exact one_ne_zero
        · rw [herm_add_right, h1, hwzw, zero_add]
          exact one_ne_zero
      · exact ⟨zw, hzw, h2, by rw [hwzw]; exact one_ne_zero⟩
    · exact ⟨zv, hzv, by rw [hvzv]; exact one_ne_zero, h1⟩
  obtain ⟨t, ht, hQt⟩ := exists_mem_three_ne_zero hlam0 hlam1 (Q z₁) (herm σ z₁ v)
  have htf : σ t = t := by
    rcases ht with rfl | rfl | rfl
    · exact map_zero σ
    · exact map_one σ
    · exact hlam
  have hwv : herm σ w v = 0 := by rw [hU.herm_comm hv hw, hvw]
  set z₂ := z₁ + t • v with hz₂
  have hz₂U : z₂ ∈ U := U.add_mem hz₁ (hU.smul_mem t htf v hv)
  have hQz₂ : Q z₂ ≠ 0 := by
    rw [hz₂, hU.add z₁ hz₁ _ (hU.smul_mem t htf v hv), hU.smul t htf v hv, hQv, mul_one,
      herm_smul_right]
    exact hQt
  have hvz₂ : herm σ v z₂ = herm σ v z₁ := by
    rw [hz₂, herm_add_right, herm_smul_right, hU.herm_self hv, mul_zero, add_zero]
  have hwz₂ : herm σ w z₂ = herm σ w z₁ := by
    rw [hz₂, herm_add_right, herm_smul_right, hwv, mul_zero, add_zero]
  obtain ⟨s, -, hs0, -, hu, hQu⟩ := hU.exists_smul_of_Q_ne_zero hz₂U hQz₂
  refine ⟨_, hu, hQu, ?_, ?_⟩
  · rw [herm_smul_right, hvz₂]
    exact mul_ne_zero (inv_ne_zero hs0) hvz₁
  · rw [herm_smul_right, hwz₂]
    exact mul_ne_zero (inv_ne_zero hs0) hwz₁

theorem exists_smul_mapsTo [Finite F] [CharP F 2] (hinv : ∀ c, σ (σ c) = c) {lam : F}
    (hlam : σ lam = lam) (hlam0 : lam ≠ 0) (hlam1 : lam ≠ 1)
    (g : (Fin m → F) →ₗ[F] (Fin m → F)) (hg : ∀ x y, herm σ (g x) (g y) = herm σ x y)
    (hgU : ∀ v ∈ U, Q v = 1 → ∃ l : F, σ l * l = 1 ∧ l • g v ∈ U ∧ Q (l • g v) = 1) :
    ∃ l : F, σ l * l = 1 ∧ ∀ x ∈ U, l • g x ∈ U ∧ Q (l • g x) = Q x := by
  classical
  have hagree : ∀ v ∈ U, ∀ w ∈ U, herm σ v w ≠ 0 → ∀ l l' : F, σ l * l = 1 → l • g v ∈ U →
      σ l' * l' = 1 → l' • g w ∈ U → l = l' := by
    intro v hv w hw hvw l l' hl hlv hl' hlw
    have h1 : herm σ (l • g v) (l' • g w) = σ l * l' * herm σ v w := by
      rw [herm_smul_left, herm_smul_right, hg]
      ring
    have h2 := hU.herm_fix hlv hlw
    rw [h1, map_mul, map_mul, hinv, hU.herm_fix hv hw] at h2
    have e1 : l * σ l' = σ l * l' := mul_right_cancel₀ hvw h2
    have hsq : l ^ 2 = l' ^ 2 := by
      linear_combination (-l ^ 2) * hl' + (l * l') * e1 + l' ^ 2 * hl
    exact frobenius_inj F 2 (by simpa [frobenius_def] using hsq)
  have hne0 : ∀ v ∈ U, Q v = 1 → v ≠ 0 := fun v _ hQv h => by
    rw [h, hU.Q_zero] at hQv
    exact zero_ne_one hQv
  have hconst : ∀ v ∈ U, Q v = 1 → ∀ w ∈ U, Q w = 1 → ∀ l l' : F, σ l * l = 1 → l • g v ∈ U →
      σ l' * l' = 1 → l' • g w ∈ U → l = l' := by
    intro v hv hQv w hw hQw l l' hl hlv hl' hlw
    by_cases hvw : herm σ v w = 0
    · obtain ⟨z, hz, hQz, hvz, hwz⟩ := hU.exists_Q_eq_one_herm_ne_zero hlam hlam0 hlam1 hv hw
        hQv hvw (hne0 v hv hQv) (hne0 w hw hQw)
      obtain ⟨lz, hlz, hlzU, -⟩ := hgU z hz hQz
      exact (hagree v hv z hz hvz l lz hl hlv hlz hlzU).trans
        (hagree w hw z hz hwz l' lz hl' hlw hlz hlzU).symm
    · exact hagree v hv w hw hvw l l' hl hlv hl' hlw
  by_cases hne : ∃ v ∈ U, Q v = 1
  · obtain ⟨v₀, hv₀, hQv₀⟩ := hne
    obtain ⟨l, hl, hlv₀, -⟩ := hgU v₀ hv₀ hQv₀
    have h1 : ∀ v ∈ U, Q v = 1 → l • g v ∈ U ∧ Q (l • g v) = 1 := by
      intro v hv hQv
      obtain ⟨l', hl', hl'v, hQl'v⟩ := hgU v hv hQv
      obtain rfl := hconst v₀ hv₀ hQv₀ v hv hQv l l' hl hlv₀ hl' hl'v
      exact ⟨hl'v, hQl'v⟩
    have h2 : ∀ x ∈ U, Q x ≠ 0 → l • g x ∈ U ∧ Q (l • g x) = Q x := by
      intro x hx hQx
      obtain ⟨s, hs, hs0, hs2, hu, hQu⟩ := hU.exists_smul_of_Q_ne_zero hx hQx
      obtain ⟨h1a, h1b⟩ := h1 _ hu hQu
      have e : l • g x = s • (l • g (s⁻¹ • x)) := by
        rw [map_smul, smul_comm l s⁻¹, smul_smul, mul_inv_cancel₀ hs0, one_smul]
      rw [e]
      refine ⟨hU.smul_mem s hs _ h1a, ?_⟩
      rw [hU.smul s hs _ h1a, h1b, mul_one, hs2]
    refine ⟨l, hl, fun x hx => ?_⟩
    by_cases hQx : Q x = 0
    · by_cases hx0 : x = 0
      · subst hx0
        rw [map_zero, smul_zero]
        exact ⟨U.zero_mem, rfl⟩
      · obtain ⟨x₁, hx₁, x₂, hx₂, hQ₁, hQ₂, rfl⟩ :=
          hU.exists_add_of_Q_eq_zero hlam hlam0 hlam1 hx hx0 hQx
        obtain ⟨a1, b1⟩ := h2 x₁ hx₁ hQ₁
        obtain ⟨a2, b2⟩ := h2 x₂ hx₂ hQ₂
        rw [map_add, smul_add]
        refine ⟨U.add_mem a1 a2, ?_⟩
        rw [hU.add _ a1 _ a2, b1, b2, hU.add _ hx₁ _ hx₂, herm_smul_left, herm_smul_right, hg,
          ← mul_assoc, hl, one_mul]
    · exact h2 x hx hQx
  · push Not at hne
    refine ⟨1, by rw [map_one, one_mul], fun x hx => ?_⟩
    have hx0 : x = 0 := by
      by_contra hx0
      obtain ⟨v, hv, hQv⟩ := hU.exists_Q_eq_one hx hx0
      exact hne v hv hQv
    subst hx0
    rw [map_zero, smul_zero]
    exact ⟨U.zero_mem, rfl⟩

theorem det_fix_of_mapsTo (M : Matrix (Fin m) (Fin m) F) (hM : ∀ x ∈ U, M *ᵥ x ∈ U) :
    σ M.det = M.det := by
  classical
  obtain ⟨b, hbU, hdet, hspan⟩ := hU.exists_basis
  choose c hcfix hc using fun j => hspan _ (hM _ (hbU j))
  have hBM : Matrix.of b * Mᵀ = Matrix.of c * Matrix.of b := by
    ext j k
    have h := congrFun (hc j) k
    rw [Finset.sum_apply] at h
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at h
    simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.transpose_apply]
    rw [← h]
    exact Finset.sum_congr rfl fun l _ => mul_comm _ _
  have hdetM : M.det = (Matrix.of c).det := by
    have h := congrArg Matrix.det hBM
    rw [det_mul, det_mul, det_transpose, mul_comm (Matrix.of c).det] at h
    exact mul_left_cancel₀ hdet h
  rw [hdetM]
  have hmap : (Matrix.of c).map σ = Matrix.of c := by
    ext j i
    exact hcfix j i
  have h := RingHom.map_det (σ : F →+* F) (Matrix.of c)
  rw [RingHom.mapMatrix_apply] at h
  simpa [hmap] using h

theorem suTv_mapsTo [CharP F 2] (hσ : IsUnitaryInvolution σ) {v : Fin m → F} (hv : v ∈ U)
    (hQv : Q v = 1) {x : Fin m → F} (hx : x ∈ U) :
    suTv hσ v 1 • x ∈ U ∧ Q (suTv hσ v 1 • x) = Q x := by
  have h1 : (1 : F) + σ 1 = 0 := by rw [map_one]; exact CharTwo.add_self_eq_zero 1
  rw [suTv_smul hσ (hU.herm_self hv) h1, one_mul]
  have hfix := hU.herm_fix hv hx
  refine ⟨U.add_mem hx (hU.smul_mem _ hfix v hv), ?_⟩
  rw [hU.add x hx _ (hU.smul_mem _ hfix v hv), hU.smul _ hfix v hv, hQv, mul_one,
    herm_smul_right, hU.herm_comm hv hx, add_assoc, ← sq, CharTwo.add_self_eq_zero, add_zero]

theorem exists_eq_suTv_one [Finite F] [CharP F 2] (hσ : IsUnitaryInvolution σ)
    {a : Fin m → F} (ha0 : a ≠ 0) (ha : herm σ a a = 0) {c : F} (hc0 : c ≠ 0)
    (hc : c + σ c = 0) (hpres : ∀ x ∈ U, suTv hσ a c • x ∈ U ∧ Q (suTv hσ a c • x) = Q x) :
    ∃ v ∈ U, Q v = 1 ∧ suTv hσ a c = suTv hσ v 1 := by
  have hcfix : σ c = c := by
    have e : σ c = -c := by linear_combination hc
    rw [e, CharTwo.neg_eq]
  obtain ⟨x, hx, hax⟩ : ∃ x ∈ U, herm σ a x ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact ha0 (hU.eq_zero_of_forall_herm hcon)
  set μ := c * herm σ a x with hμ
  have hμ0 : μ ≠ 0 := mul_ne_zero hc0 hax
  have ha₀U : μ • a ∈ U := by
    have h1 := (hpres x hx).1
    rw [suTv_smul hσ ha hc] at h1
    have h2 := U.sub_mem h1 hx
    rwa [add_sub_cancel_left] at h2
  set a₀ := μ • a with ha₀def
  have ha₀ : herm σ a₀ a₀ = 0 := by rw [herm_smul_left, herm_smul_right, ha, mul_zero, mul_zero]
  have ha₀0 : a₀ ≠ 0 := smul_ne_zero hμ0 ha0
  set c' := σ μ⁻¹ * μ⁻¹ * c with hc'
  have hT : suTv hσ a c = suTv hσ a₀ c' := by
    have e : a = μ⁻¹ • a₀ := by rw [ha₀def, smul_smul, inv_mul_cancel₀ hμ0, one_smul]
    conv_lhs => rw [e]
    exact suTv_smul_vec hσ ha₀ hc μ⁻¹
  have hc'fix : σ c' = c' := by rw [hc', map_mul, map_mul, hσ.invol, hcfix]; ring
  have hc'0 : c' ≠ 0 :=
    mul_ne_zero (mul_ne_zero ((map_ne_zero σ).mpr (inv_ne_zero hμ0)) (inv_ne_zero hμ0)) hc0
  have hc'' : c' + σ c' = 0 := by rw [hc'fix]; exact CharTwo.add_self_eq_zero c'
  obtain ⟨y, hy, ha₀y⟩ := hU.exists_herm_eq_one_of_mem ha₀U ha₀0
  have hQa₀ : c' * Q a₀ = 1 := by
    have h1 := (hpres y hy).2
    rw [hT, suTv_smul hσ ha₀ hc'', ha₀y, mul_one, hU.add y hy _ (hU.smul_mem _ hc'fix _ ha₀U),
      hU.smul _ hc'fix _ ha₀U, herm_smul_right, hU.herm_comm ha₀U hy, ha₀y, mul_one] at h1
    have h2 : c' * (c' * Q a₀ + 1) = 0 := by linear_combination h1
    have h3 := (mul_eq_zero.mp h2).resolve_left hc'0
    rw [← CharTwo.neg_eq (1 : F)]
    linear_combination h3
  obtain ⟨s, hs, hs2⟩ := exists_fix_sq_eq hc'fix
  refine ⟨s • a₀, hU.smul_mem s hs _ ha₀U, ?_, ?_⟩
  · rw [hU.smul s hs _ ha₀U, hs2, hQa₀]
  · rw [hT, suTv_smul_vec hσ ha₀ (by rw [map_one]; exact CharTwo.add_self_eq_zero 1) s, hs,
      mul_one, ← sq, hs2]

end Basic

end IsFixedQuadForm

theorem suTv_one_mul_self [CharP F 2] (hσ : IsUnitaryInvolution σ) {v : Fin m → F}
    (hv : herm σ v v = 0) : suTv hσ v 1 * suTv hσ v 1 = 1 := by
  have h1 : (1 : F) + σ 1 = 0 := by rw [map_one]; exact CharTwo.add_self_eq_zero 1
  apply ext_smul
  intro x
  rw [mul_smul, suTv_smul hσ hv h1, suTv_smul hσ hv h1, one_smul, herm_add_right,
    herm_smul_right, hv, mul_zero, add_zero, one_mul, add_assoc, ← add_smul,
    CharTwo.add_self_eq_zero, zero_smul, add_zero]

theorem exists_norm_eq_one_of_suTv_eq [CharP F 2] (hσ : IsUnitaryInvolution σ)
    {a b : Fin m → F} (ha0 : a ≠ 0) (ha : herm σ a a = 0) (hb : herm σ b b = 0)
    (h : suTv hσ a 1 = suTv hσ b 1) : ∃ μ : F, σ μ * μ = 1 ∧ b = μ • a := by
  have h1 : (1 : F) + σ 1 = 0 := by rw [map_one]; exact CharTwo.add_self_eq_zero 1
  have hx : ∀ x, herm σ a x • a = herm σ b x • b := by
    intro x
    have h2 := congrArg (· • x) h
    rw [suTv_smul hσ ha h1, suTv_smul hσ hb h1, one_mul, one_mul] at h2
    exact add_left_cancel h2
  obtain ⟨y, hy⟩ := exists_herm_eq_one σ ha0
  have hb0 : b ≠ 0 := by
    rintro rfl
    have h2 := hx y
    rw [hy, one_smul, smul_zero] at h2
    exact ha0 h2
  obtain ⟨x, hxb⟩ := exists_herm_eq_one σ hb0
  have hbx : b = herm σ a x • a := by rw [hx x, hxb, one_smul]
  refine ⟨herm σ a x, ?_, hbx⟩
  have h2 := hx y
  rw [hy, one_smul, hbx, herm_smul_left, hy, mul_one, smul_smul] at h2
  by_contra hne
  have h3 : (σ (herm σ a x) * herm σ a x - 1) • a = 0 := by
    rw [sub_smul, ← h2, one_smul, sub_self]
  exact ha0 ((smul_eq_zero.mp h3).resolve_left (sub_ne_zero.mpr hne))

def fixedQuadSubgroup (σ : F ≃+* F) (U : AddSubgroup (Fin m → F)) (Q : (Fin m → F) → F) :
    Subgroup (SUid σ m) where
  carrier := {g | (∀ x, g • x ∈ U ↔ x ∈ U) ∧ ∀ x ∈ U, Q (g • x) = Q x}
  mul_mem' {g g'} hg hg' := ⟨fun x => by rw [mul_smul, hg.1, hg'.1],
    fun x hx => by rw [mul_smul, hg.2 _ ((hg'.1 x).mpr hx), hg'.2 x hx]⟩
  one_mem' := ⟨fun x => by rw [one_smul], fun x _ => by rw [one_smul]⟩
  inv_mem' {g} hg := ⟨fun x => by rw [← hg.1 (g⁻¹ • x), smul_inv_smul], fun x hx => by
    have h := hg.2 (g⁻¹ • x) ((hg.1 _).mp (by rwa [smul_inv_smul]))
    rw [smul_inv_smul] at h
    exact h.symm⟩

theorem mem_fixedQuadSubgroup {U : AddSubgroup (Fin m → F)} {Q : (Fin m → F) → F}
    {g : SUid σ m} :
    g ∈ fixedQuadSubgroup σ U Q ↔ (∀ x, g • x ∈ U ↔ x ∈ U) ∧ ∀ x ∈ U, Q (g • x) = Q x :=
  Iff.rfl

theorem IsFixedQuadForm.mapsTo_of_conj [Finite F] [CharP F 2] (hσ : IsUnitaryInvolution σ)
    {lam : F} (hlam : σ lam = lam) (hlam0 : lam ≠ 0) (hlam1 : lam ≠ 1)
    {U : AddSubgroup (Fin m → F)} {Q : (Fin m → F) → F} (hU : IsFixedQuadForm σ U Q)
    (hscal : ∀ l : F, σ l * l = 1 → l ^ m = 1 → l = 1) (g : SUid σ m)
    (hg : ∀ v ∈ U, Q v = 1 → ∃ v' ∈ U, Q v' = 1 ∧ g * suTv hσ v 1 * g⁻¹ = suTv hσ v' 1) :
    ∀ x ∈ U, g • x ∈ U ∧ Q (g • x) = Q x := by
  have h1 : (1 : F) + σ 1 = 0 := by rw [map_one]; exact CharTwo.add_self_eq_zero 1
  let G : (Fin m → F) →ₗ[F] (Fin m → F) :=
    Matrix.mulVecLin ((g : GL (Fin m) F) : Matrix (Fin m) (Fin m) F)
  have hG : ∀ x, G x = g • x := fun x => rfl
  have hGh : ∀ x y, herm σ (G x) (G y) = herm σ x y := fun x y => by
    rw [hG, hG, herm_smul_smul]
  have hgU : ∀ v ∈ U, Q v = 1 → ∃ l : F, σ l * l = 1 ∧ l • G v ∈ U ∧ Q (l • G v) = 1 := by
    intro v hv hQv
    have hv0 : v ≠ 0 := fun h => by
      rw [h, hU.Q_zero] at hQv
      exact zero_ne_one hQv
    obtain ⟨v', hv', hQv', hconj⟩ := hg v hv hQv
    rw [suTv_conj hσ g (hU.herm_self hv) h1] at hconj
    have hgv0 : g • v ≠ 0 := fun h => hv0 (by simpa using congrArg (g⁻¹ • ·) h)
    have hgv : herm σ (g • v) (g • v) = 0 := by rw [herm_smul_smul, hU.herm_self hv]
    obtain ⟨μ, hμ, hμv⟩ := exists_norm_eq_one_of_suTv_eq hσ hgv0 hgv (hU.herm_self hv') hconj
    refine ⟨μ, hμ, ?_, ?_⟩
    · rw [hG, ← hμv]
      exact hv'
    · rw [hG, ← hμv]
      exact hQv'
  obtain ⟨l, hl, hlU⟩ := hU.exists_smul_mapsTo hσ.invol hlam hlam0 hlam1 G hGh hgU
  have hdet := hU.det_fix_of_mapsTo (l • ((g : GL (Fin m) F) : Matrix (Fin m) (Fin m) F))
    (fun x hx => by rw [Matrix.smul_mulVec]; exact (hlU x hx).1)
  rw [Matrix.det_smul, Fintype.card_fin, ((mem_SUid_iff σ).mp g.2).1, mul_one] at hdet
  have hlm : l ^ m = 1 :=
    eq_one_of_fix_of_norm hdet (by rw [map_pow, ← mul_pow, hl, one_pow])
  obtain rfl := hscal l hl hlm
  intro x hx
  simpa [hG] using hlU x hx

theorem normalizer_fixedQuadSubgroup [Finite F] [CharP F 2] (hσ : IsUnitaryInvolution σ)
    {lam : F} (hlam : σ lam = lam) (hlam0 : lam ≠ 0) (hlam1 : lam ≠ 1)
    {U : AddSubgroup (Fin m → F)} {Q : (Fin m → F) → F} (hU : IsFixedQuadForm σ U Q)
    (hscal : ∀ l : F, σ l * l = 1 → l ^ m = 1 → l = 1) :
    Subgroup.normalizer (fixedQuadSubgroup σ U Q : Set (SUid σ m)) =
      fixedQuadSubgroup σ U Q := by
  have h1 : (1 : F) + σ 1 = 0 := by rw [map_one]; exact CharTwo.add_self_eq_zero 1
  have key : ∀ g ∈ Subgroup.normalizer (fixedQuadSubgroup σ U Q : Set (SUid σ m)),
      ∀ x ∈ U, g • x ∈ U ∧ Q (g • x) = Q x := by
    intro g hg
    refine hU.mapsTo_of_conj hσ hlam hlam0 hlam1 hscal g fun v hv hQv => ?_
    have hv0 : v ≠ 0 := fun h => by
      rw [h, hU.Q_zero] at hQv
      exact zero_ne_one hQv
    have hmem : suTv hσ v 1 ∈ fixedQuadSubgroup σ U Q := by
      refine ⟨fun x => ⟨fun h => ?_, fun h => (hU.suTv_mapsTo hσ hv hQv h).1⟩,
        fun x hx => (hU.suTv_mapsTo hσ hv hQv hx).2⟩
      have h2 := (hU.suTv_mapsTo hσ hv hQv h).1
      rwa [← mul_smul, suTv_one_mul_self hσ (hU.herm_self hv), one_smul] at h2
    have hconj := (Subgroup.mem_normalizer_iff.mp hg (suTv hσ v 1)).mp hmem
    have hconj' := hconj
    rw [suTv_conj hσ g (hU.herm_self hv) h1] at hconj'
    have hgv0 : g • v ≠ 0 := fun h => hv0 (by simpa using congrArg (g⁻¹ • ·) h)
    have hgv : herm σ (g • v) (g • v) = 0 := by rw [herm_smul_smul, hU.herm_self hv]
    obtain ⟨v', hv', hQv', heq⟩ := hU.exists_eq_suTv_one hσ hgv0 hgv one_ne_zero h1
      (fun x hx => ⟨(hconj'.1 x).mpr hx, hconj'.2 x hx⟩)
    exact ⟨v', hv', hQv', by rw [suTv_conj hσ g (hU.herm_self hv) h1, heq]⟩
  refine le_antisymm (fun g hg => ?_) (Subgroup.le_normalizer)
  refine ⟨fun x => ⟨fun h => ?_, fun h => (key g hg x h).1⟩, fun x hx => (key g hg x hx).2⟩
  have h2 := (key g⁻¹ (inv_mem hg) _ h).1
  rwa [inv_smul_smul] at h2

theorem IsFixedQuadForm.suTv_injOn [CharP F 2] (hσ : IsUnitaryInvolution σ)
    {U : AddSubgroup (Fin m → F)} {Q : (Fin m → F) → F} (hU : IsFixedQuadForm σ U Q) :
    Set.InjOn (fun v => suTv hσ v 1) {v | v ∈ U ∧ Q v = 1} := by
  rintro v ⟨hv, hQv⟩ v' ⟨hv', hQv'⟩ h
  have hv0 : v ≠ 0 := fun h0 => by
    rw [h0, hU.Q_zero] at hQv
    exact zero_ne_one hQv
  obtain ⟨μ, hμ, rfl⟩ := exists_norm_eq_one_of_suTv_eq hσ hv0 (hU.herm_self hv)
    (hU.herm_self hv') h
  obtain ⟨y, hy, hvy⟩ := hU.exists_herm_eq_one_of_mem hv hv0
  have hfix : σ (σ μ) = σ μ := by
    have h2 := hU.herm_fix hv' hy
    rwa [herm_smul_left, hvy, mul_one] at h2
  rw [hσ.invol] at hfix
  have hμ1 : μ = 1 := eq_one_of_fix_of_norm hfix.symm hμ
  rw [hμ1, one_smul]

private theorem eq_one_of_pow_four_eq_one [CharP F 2] {l : F} (h : l ^ 4 = 1) : l = 1 := by
  have h2 : l ^ 2 = 1 := frobenius_inj F 2 (by
    rw [frobenius_def, frobenius_def, ← pow_mul, one_pow]; exact h)
  exact frobenius_inj F 2 (by rw [frobenius_def, frobenius_def, h2, one_pow])

theorem normalizer_fixedQuadSubgroup_four [Finite F] [CharP F 2] (hσ : IsUnitaryInvolution σ)
    {lam : F} (hlam : σ lam = lam) (hlam0 : lam ≠ 0) (hlam1 : lam ≠ 1)
    {U : AddSubgroup (Fin 4 → F)} {Q : (Fin 4 → F) → F} (hU : IsFixedQuadForm σ U Q) :
    Subgroup.normalizer (fixedQuadSubgroup σ U Q : Set (SUid σ 4)) =
      fixedQuadSubgroup σ U Q :=
  normalizer_fixedQuadSubgroup hσ hlam hlam0 hlam1 hU fun _ _ h => eq_one_of_pow_four_eq_one h

section Frame

theorem eq_frame_expansion (hinv : ∀ c, σ (σ c) = c) {v w e f : Fin 4 → F}
    (hvv : herm σ v v = 0) (hww : herm σ w w = 0) (hee : herm σ e e = 0) (hff : herm σ f f = 0)
    (hvw : herm σ v w = 1) (hve : herm σ v e = 0) (hvf : herm σ v f = 0) (hwe : herm σ w e = 0)
    (hwf : herm σ w f = 0) (hef : herm σ e f = 1) (x : Fin 4 → F) :
    x = herm σ w x • v + herm σ v x • w + herm σ f x • e + herm σ e x • f := by
  have hwv : herm σ w v = 1 := by rw [herm_conj σ hinv, hvw, map_one]
  have hev : herm σ e v = 0 := herm_eq_zero_comm σ hinv hve
  have hfv : herm σ f v = 0 := herm_eq_zero_comm σ hinv hvf
  have hew : herm σ e w = 0 := herm_eq_zero_comm σ hinv hwe
  have hfw : herm σ f w = 0 := herm_eq_zero_comm σ hinv hwf
  have hfe : herm σ f e = 1 := by rw [herm_conj σ hinv, hef, map_one]
  set r : Fin 4 → Fin 4 → F := ![v, w, e, f] with hr
  have hli : LinearIndependent F r := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have hc' : c 0 • v + c 1 • w + c 2 • e + c 3 • f = 0 := by
      rw [← hc, Fin.sum_univ_four]
      rfl
    have h0 := congrArg (herm σ w) hc'
    have h1 := congrArg (herm σ v) hc'
    have h2 := congrArg (herm σ f) hc'
    have h3 := congrArg (herm σ e) hc'
    simp only [herm_add_right, herm_smul_right, herm_zero_right, hvv, hww, hee, hff, hvw, hve, hvf,
      hwe, hwf, hef, hwv, hev, hfv, hew, hfw, hfe, mul_zero, mul_one, add_zero, zero_add]
      at h0 h1 h2 h3
    intro i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
    · exact h3
  have hspan : Submodule.span F (Set.range r) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank (by rw [Fintype.card_fin, Module.finrank_fin_fun])
  set x' := x - (herm σ w x • v + herm σ v x • w + herm σ f x • e + herm σ e x • f) with hx'
  have hperp : ∀ i, herm σ (r i) x' = 0 := by
    intro i
    fin_cases i <;>
    simp [r, hx', herm_sub_right, herm_add_right, herm_smul_right, hvv, hww, hee, hff, hvw, hve,
      hvf, hwe, hwf, hef, hwv, hev, hfv, hew, hfw, hfe]
  have hall : ∀ y, herm σ y x' = 0 := by
    intro y
    have hy : y ∈ Submodule.span F (Set.range r) := by rw [hspan]; exact Submodule.mem_top
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      exact hperp i
    | zero => exact herm_zero_left σ x'
    | add a b _ _ ha hb => rw [herm_add_left, ha, hb, add_zero]
    | smul c a _ ha => rw [herm_smul_left, ha, mul_zero]
  have hx0 : x' = 0 := eq_zero_of_herm σ fun y => by rw [herm_conj σ hinv, hall y, map_zero]
  rw [hx', sub_eq_zero] at hx0
  exact hx0

theorem eq_of_frame (hinv : ∀ c, σ (σ c) = c) {v w e f : Fin 4 → F}
    (hvv : herm σ v v = 0) (hww : herm σ w w = 0) (hee : herm σ e e = 0) (hff : herm σ f f = 0)
    (hvw : herm σ v w = 1) (hve : herm σ v e = 0) (hvf : herm σ v f = 0) (hwe : herm σ w e = 0)
    (hwf : herm σ w f = 0) (hef : herm σ e f = 1) {g g' : SUid σ 4} (h1 : g • v = g' • v)
    (h2 : g • w = g' • w) (h3 : g • e = g' • e) (h4 : g • f = g' • f) : g = g' := by
  refine ext_smul σ fun x => ?_
  rw [eq_frame_expansion hinv hvv hww hee hff hvw hve hvf hwe hwf hef x]
  simp only [smul_add, smul_comm g, smul_comm g', h1, h2, h3, h4]

variable [CharP F 2]

theorem IsFixedQuadForm.exists_frame (hσ : IsUnitaryInvolution σ) {U : AddSubgroup (Fin 4 → F)}
    {Q : (Fin 4 → F) → F} (hU : IsFixedQuadForm σ U Q) {v : Fin 4 → F} (hv : v ∈ U)
    (hv0 : v ≠ 0) :
    ∃ w ∈ U, ∃ e ∈ U, ∃ f ∈ U, herm σ v w = 1 ∧ herm σ v e = 0 ∧ herm σ v f = 0 ∧
      herm σ w e = 0 ∧ herm σ w f = 0 ∧ herm σ e f = 1 := by
  obtain ⟨w, hw, hvw⟩ := hU.exists_herm_eq_one_of_mem hv hv0
  have hwv : herm σ w v = 1 := by rw [hU.herm_comm hv hw, hvw]
  have hvv := hU.herm_self hv
  have hww := hU.herm_self hw
  let π : (Fin 4 → F) →ₗ[F] (Fin 4 → F) :=
    LinearMap.id + (hermL σ w).smulRight v + (hermL σ v).smulRight w
  have hπ : ∀ x, π x = x + herm σ w x • v + herm σ v x • w := fun x => rfl
  have hπU : ∀ x ∈ U, π x ∈ U := fun x hx => by
    rw [hπ]
    exact U.add_mem (U.add_mem hx (hU.smul_mem _ (hU.herm_fix hw hx) v hv))
      (hU.smul_mem _ (hU.herm_fix hv hx) w hw)
  have hπv : ∀ x, herm σ v (π x) = 0 := fun x => by
    rw [hπ, herm_add_right, herm_add_right, herm_smul_right, herm_smul_right, hvv, hvw, mul_zero,
      mul_one, add_zero, CharTwo.add_self_eq_zero]
  have hπw : ∀ x, herm σ w (π x) = 0 := fun x => by
    rw [hπ, herm_add_right, herm_add_right, herm_smul_right, herm_smul_right, hwv, hww, mul_zero,
      mul_one, add_zero, CharTwo.add_self_eq_zero]
  obtain ⟨z, hzz, hvz, hwz⟩ := exists_norm_one_perp_pair hσ (by norm_num) hvv hww hvw
  obtain ⟨b, hbU, hdet, -⟩ := hU.exists_basis
  obtain ⟨i, hi⟩ : ∃ i, π (b i) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hz : z = ∑ i, (z ᵥ* (Matrix.of b)⁻¹) i • b i := by
      have h1 : (z ᵥ* (Matrix.of b)⁻¹) ᵥ* Matrix.of b = z := by
        rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet),
          Matrix.vecMul_one]
      conv_lhs => rw [← h1]
      rw [Matrix.vecMul_eq_sum]
      rfl
    have hπz : π z = z := by rw [hπ, hwz, hvz, zero_smul, zero_smul, add_zero, add_zero]
    have h0 : π z = 0 := by
      rw [hz, map_sum]
      exact Finset.sum_eq_zero fun i _ => by rw [map_smul, hcon i, smul_zero]
    rw [hπz] at h0
    rw [h0, herm_zero_left] at hzz
    exact zero_ne_one hzz
  obtain ⟨y, hy, hey⟩ := hU.exists_herm_eq_one_of_mem (hπU _ (hbU i)) hi
  refine ⟨w, hw, π (b i), hπU _ (hbU i), π y, hπU y hy, hvw, hπv _, hπv _, hπw _, hπw _, ?_⟩
  rw [hπ y, herm_add_right, herm_add_right, herm_smul_right, herm_smul_right,
    hU.herm_comm hv (hπU _ (hbU i)), hπv, hU.herm_comm hw (hπU _ (hbU i)), hπw, mul_zero, mul_zero,
    add_zero, add_zero, hey]

theorem IsFixedQuadForm.frame_coords (hσ : IsUnitaryInvolution σ) {U : AddSubgroup (Fin 4 → F)}
    {Q : (Fin 4 → F) → F} (hU : IsFixedQuadForm σ U Q) {v w e f : Fin 4 → F} (hv : v ∈ U)
    (hw : w ∈ U) (he : e ∈ U) (hf : f ∈ U) (hQv : Q v = 1) (hvw : herm σ v w = 1)
    (hve : herm σ v e = 0) (hvf : herm σ v f = 0) (hwe : herm σ w e = 0) (hwf : herm σ w f = 0)
    (hef : herm σ e f = 1) (g : SUid σ 4) (hgU : ∀ x ∈ U, g • x ∈ U)
    (hgQ : ∀ x ∈ U, Q (g • x) = Q x) (hgv : g • v = v) :
    g • e = herm σ w (g • e) • v + herm σ f (g • e) • e + herm σ e (g • e) • f ∧
    g • f = herm σ w (g • f) • v + herm σ f (g • f) • e + herm σ e (g • f) • f ∧
    g • w = herm σ w (g • w) • v + w + herm σ f (g • w) • e + herm σ e (g • w) • f ∧
    herm σ f (g • e) * herm σ e (g • f) + herm σ f (g • f) * herm σ e (g • e) = 1 ∧
    herm σ w (g • e) ^ 2 = Q e + Q (herm σ f (g • e) • e + herm σ e (g • e) • f) ∧
    herm σ w (g • f) ^ 2 = Q f + Q (herm σ f (g • f) • e + herm σ e (g • f) • f) ∧
    herm σ w (g • e) + herm σ f (g • e) * herm σ e (g • w) +
      herm σ e (g • e) * herm σ f (g • w) = 0 ∧
    herm σ w (g • f) + herm σ f (g • f) * herm σ e (g • w) +
      herm σ e (g • f) * herm σ f (g • w) = 0 ∧
    herm σ w (g • w) ^ 2 + herm σ w (g • w) =
      Q w + Q (w + (herm σ f (g • w) • e + herm σ e (g • w) • f)) := by
  have hinv := hσ.invol
  have hvv := hU.herm_self hv
  have hww := hU.herm_self hw
  have hee := hU.herm_self he
  have hff := hU.herm_self hf
  have hexp := eq_frame_expansion hinv hvv hww hee hff hvw hve hvf hwe hwf hef
  have hfe : herm σ f e = 1 := by rw [herm_conj σ hinv, hef, map_one]
  have hev : herm σ e v = 0 := herm_eq_zero_comm σ hinv hve
  have hfv : herm σ f v = 0 := herm_eq_zero_comm σ hinv hvf
  have hgvx : ∀ x, herm σ v (g • x) = herm σ v x := fun x => by
    conv_lhs => rw [← hgv]
    exact herm_smul_smul σ g v x
  have hge := hgU e he
  have hgf := hgU f hf
  have hgw := hgU w hw
  have exE : g • e = herm σ w (g • e) • v + herm σ f (g • e) • e + herm σ e (g • e) • f := by
    conv_lhs => rw [hexp (g • e)]
    rw [hgvx, hve, zero_smul, add_zero]
  have exF : g • f = herm σ w (g • f) • v + herm σ f (g • f) • e + herm σ e (g • f) • f := by
    conv_lhs => rw [hexp (g • f)]
    rw [hgvx, hvf, zero_smul, add_zero]
  have exW : g • w = herm σ w (g • w) • v + w + herm σ f (g • w) • e + herm σ e (g • w) • f := by
    conv_lhs => rw [hexp (g • w)]
    rw [hgvx, hvw, one_smul]
  have fx : ∀ x ∈ U, ∀ y ∈ U, σ (herm σ x y) = herm σ x y := fun x hx y hy => hU.herm_fix hx hy
  have hQv' : ∀ A : F, σ A = A → ∀ y ∈ U, herm σ v y = 0 → Q (A • v + y) = A ^ 2 + Q y := by
    intro A hA y hy hvy
    rw [hU.add _ (hU.smul_mem A hA v hv) y hy, hU.smul A hA v hv, hQv, mul_one, herm_smul_left,
      hvy, mul_zero, add_zero]
  refine ⟨exE, exF, exW, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    have h1 : herm σ (g • e) (g • f) = 1 := by rw [herm_smul_smul, hef]
    conv_lhs at h1 => rw [exE]
    simp only [herm_add_left, herm_smul_left, hgvx, hvf, mul_zero, zero_add] at h1
    rw [fx f hf _ hge, fx e he _ hge] at h1
    linear_combination h1
  · have h1 := hgQ e he
    rw [exE, add_assoc] at h1
    have hy : herm σ f (g • e) • e + herm σ e (g • e) • f ∈ U :=
      U.add_mem (hU.smul_mem _ (fx f hf _ hge) e he) (hU.smul_mem _ (fx e he _ hge) f hf)
    have hvy : herm σ v (herm σ f (g • e) • e + herm σ e (g • e) • f) = 0 := by
      rw [herm_add_right, herm_smul_right, herm_smul_right, hve, hvf, mul_zero, mul_zero, add_zero]
    rw [hQv' _ (fx w hw _ hge) _ hy hvy] at h1
    rw [← h1, add_assoc, CharTwo.add_self_eq_zero, add_zero]
  · have h1 := hgQ f hf
    rw [exF, add_assoc] at h1
    have hy : herm σ f (g • f) • e + herm σ e (g • f) • f ∈ U :=
      U.add_mem (hU.smul_mem _ (fx f hf _ hgf) e he) (hU.smul_mem _ (fx e he _ hgf) f hf)
    have hvy : herm σ v (herm σ f (g • f) • e + herm σ e (g • f) • f) = 0 := by
      rw [herm_add_right, herm_smul_right, herm_smul_right, hve, hvf, mul_zero, mul_zero, add_zero]
    rw [hQv' _ (fx w hw _ hgf) _ hy hvy] at h1
    rw [← h1, add_assoc, CharTwo.add_self_eq_zero, add_zero]
  · have h1 : herm σ (g • e) (g • w) = 0 := by
      rw [herm_smul_smul]
      exact herm_eq_zero_comm σ hinv hwe
    conv_lhs at h1 => rw [exE]
    simp only [herm_add_left, herm_smul_left, hgvx, hvw, mul_one] at h1
    rw [fx w hw _ hge, fx f hf _ hge, fx e he _ hge] at h1
    exact h1
  · have h1 : herm σ (g • f) (g • w) = 0 := by
      rw [herm_smul_smul]
      exact herm_eq_zero_comm σ hinv hwf
    conv_lhs at h1 => rw [exF]
    simp only [herm_add_left, herm_smul_left, hgvx, hvw, mul_one] at h1
    rw [fx w hw _ hgf, fx f hf _ hgf, fx e he _ hgf] at h1
    exact h1
  · have h1 := hgQ w hw
    have hAw := fx w hw _ hgw
    have hy : w + (herm σ f (g • w) • e + herm σ e (g • w) • f) ∈ U :=
      U.add_mem hw (U.add_mem (hU.smul_mem _ (fx f hf _ hgw) e he)
        (hU.smul_mem _ (fx e he _ hgw) f hf))
    have hexW : g • w = herm σ w (g • w) • v + (w + (herm σ f (g • w) • e +
        herm σ e (g • w) • f)) := by
      conv_lhs => rw [exW]
      abel
    rw [hexW, hU.add _ (hU.smul_mem _ hAw v hv) _ hy, hU.smul _ hAw v hv, hQv, mul_one,
      herm_smul_left, herm_add_right, herm_add_right, herm_smul_right, herm_smul_right, hvw, hve,
      hvf, mul_zero, mul_zero, add_zero, add_zero, mul_one, hAw] at h1
    rw [← h1]
    have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
    linear_combination (-Q (w + (herm σ f (g • w) • e + herm σ e (g • w) • f))) * h2

theorem exists_sl2_fixed {a b c d : F} (ha : σ a = a) (hb : σ b = b) (hc : σ c = c)
    (hd : σ d = d) (h : a * d + b * c = 1) :
    ∃ M : Matrix.SpecialLinearGroup (Fin 2) (RingHom.eqLocusField (σ : F →+* F) (RingHom.id F)),
      (M.1 0 0 : F) = a ∧ (M.1 0 1 : F) = b ∧ (M.1 1 0 : F) = c ∧ (M.1 1 1 : F) = d := by
  refine ⟨⟨!![⟨a, ha⟩, ⟨b, hb⟩; ⟨c, hc⟩, ⟨d, hd⟩], ?_⟩, rfl, rfl, rfl, rfl⟩
  rw [Matrix.det_fin_two_of]
  apply Subtype.ext
  change a * d - b * c = 1
  rw [sub_eq_add_neg, CharTwo.neg_eq]
  exact h

theorem IsFixedQuadForm.natCard_stabilizer_le [Finite F] (hσ : IsUnitaryInvolution σ) {q : ℕ}
    (hq : Nat.card {c : F // σ c = c} = q) {U : AddSubgroup (Fin 4 → F)} {Q : (Fin 4 → F) → F}
    (hU : IsFixedQuadForm σ U Q) {v : Fin 4 → F} (hv : v ∈ U) (hQv : Q v = 1) :
    Nat.card {g : fixedQuadSubgroup σ U Q // (g : SUid σ 4) • v = v} ≤ 2 * (q * (q ^ 2 - 1)) := by
  classical
  have hinv := hσ.invol
  have hv0 : v ≠ 0 := fun h => by
    rw [h, hU.Q_zero] at hQv
    exact zero_ne_one hQv
  obtain ⟨w, hw, e, he, f, hf, hvw, hve, hvf, hwe, hwf, hef⟩ := hU.exists_frame hσ hv hv0
  have hvv := hU.herm_self hv
  have hww := hU.herm_self hw
  have hee := hU.herm_self he
  have hff := hU.herm_self hf
  set K₀ : Subfield F := RingHom.eqLocusField (σ : F →+* F) (RingHom.id F) with hK₀def
  have hK₀ : Nat.card K₀ = q := by
    rw [← hq]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun c => Iff.rfl)
  set S := {g : fixedQuadSubgroup σ U Q // (g : SUid σ 4) • v = v} with hSdef
  have hgU : ∀ g : S, ∀ x ∈ U, (g.1 : SUid σ 4) • x ∈ U := fun g x hx =>
    ((mem_fixedQuadSubgroup.mp g.1.2).1 x).mpr hx
  have hgQ : ∀ g : S, ∀ x ∈ U, Q ((g.1 : SUid σ 4) • x) = Q x := fun g x hx =>
    (mem_fixedQuadSubgroup.mp g.1.2).2 x hx
  have hc : ∀ g : S, _ := fun g => hU.frame_coords hσ hv hw he hf hQv hvw hve hvf hwe hwf hef
    (g.1 : SUid σ 4) (hgU g) (hgQ g) g.2
  have fx : ∀ g : S, ∀ x ∈ U, ∀ y ∈ U, σ (herm σ x ((g.1 : SUid σ 4) • y)) =
      herm σ x ((g.1 : SUid σ 4) • y) := fun g x hx y hy => hU.herm_fix hx (hgU g y hy)
  have hM : ∀ g : S, ∃ M : Matrix.SpecialLinearGroup (Fin 2) K₀,
      (M.1 0 0 : F) = herm σ f ((g.1 : SUid σ 4) • e) ∧
      (M.1 0 1 : F) = herm σ f ((g.1 : SUid σ 4) • f) ∧
      (M.1 1 0 : F) = herm σ e ((g.1 : SUid σ 4) • e) ∧
      (M.1 1 1 : F) = herm σ e ((g.1 : SUid σ 4) • f) := fun g =>
    exists_sl2_fixed (fx g f hf e he) (fx g f hf f hf) (fx g e he e he) (fx g e he f hf)
      (hc g).2.2.2.1
  choose M hM using hM
  have hsame : ∀ g g' : S, M g = M g' →
      (g.1 : SUid σ 4) • e = (g'.1 : SUid σ 4) • e ∧ (g.1 : SUid σ 4) • f = (g'.1 : SUid σ 4) • f ∧
      herm σ f ((g.1 : SUid σ 4) • w) = herm σ f ((g'.1 : SUid σ 4) • w) ∧
      herm σ e ((g.1 : SUid σ 4) • w) = herm σ e ((g'.1 : SUid σ 4) • w) := by
    intro g g' hgg'
    obtain ⟨a1, b1, c1, d1⟩ := hM g
    obtain ⟨a2, b2, c2, d2⟩ := hM g'
    rw [hgg'] at a1 b1 c1 d1
    have ha : herm σ f ((g.1 : SUid σ 4) • e) = herm σ f ((g'.1 : SUid σ 4) • e) := a1.symm.trans a2
    have hb : herm σ f ((g.1 : SUid σ 4) • f) = herm σ f ((g'.1 : SUid σ 4) • f) := b1.symm.trans b2
    have hc' : herm σ e ((g.1 : SUid σ 4) • e) = herm σ e ((g'.1 : SUid σ 4) • e) :=
      c1.symm.trans c2
    have hd : herm σ e ((g.1 : SUid σ 4) • f) = herm σ e ((g'.1 : SUid σ 4) • f) :=
      d1.symm.trans d2
    obtain ⟨exE, exF, -, hdet, hAe, hAf, hl1, hl2, -⟩ := hc g
    obtain ⟨exE', exF', -, -, hAe', hAf', hl1', hl2', -⟩ := hc g'
    have hAeq : herm σ w ((g.1 : SUid σ 4) • e) = herm σ w ((g'.1 : SUid σ 4) • e) :=
      frobenius_inj F 2 (by rw [frobenius_def, frobenius_def, hAe, hAe', ha, hc'])
    have hAfq : herm σ w ((g.1 : SUid σ 4) • f) = herm σ w ((g'.1 : SUid σ 4) • f) :=
      frobenius_inj F 2 (by rw [frobenius_def, frobenius_def, hAf, hAf', hb, hd])
    have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
    rw [hAeq, ha, hc'] at hl1
    rw [hAfq, hb, hd] at hl2
    rw [ha, hb, hc', hd] at hdet
    refine ⟨by rw [exE, exE', hAeq, ha, hc'], by rw [exF, exF', hAfq, hb, hd], ?_, ?_⟩
    · linear_combination (herm σ f ((g'.1 : SUid σ 4) • e)) * (hl2 - hl2') -
        (herm σ f ((g'.1 : SUid σ 4) • f)) * (hl1 - hl1') -
        (herm σ f ((g.1 : SUid σ 4) • w) - herm σ f ((g'.1 : SUid σ 4) • w)) * hdet +
        (herm σ f ((g'.1 : SUid σ 4) • f) * herm σ e ((g'.1 : SUid σ 4) • e) *
          (herm σ f ((g.1 : SUid σ 4) • w) - herm σ f ((g'.1 : SUid σ 4) • w))) * h2
    · linear_combination (herm σ e ((g'.1 : SUid σ 4) • f)) * (hl1 - hl1') -
        (herm σ e ((g'.1 : SUid σ 4) • e)) * (hl2 - hl2') -
        (herm σ e ((g.1 : SUid σ 4) • w) - herm σ e ((g'.1 : SUid σ 4) • w)) * hdet +
        (herm σ f ((g'.1 : SUid σ 4) • f) * herm σ e ((g'.1 : SUid σ 4) • e) *
          (herm σ e ((g.1 : SUid σ 4) • w) - herm σ e ((g'.1 : SUid σ 4) • w))) * h2
  have hroot : ∀ g g' : S, M g = M g' →
      herm σ w ((g.1 : SUid σ 4) • w) = herm σ w ((g'.1 : SUid σ 4) • w) ∨
      herm σ w ((g.1 : SUid σ 4) • w) = herm σ w ((g'.1 : SUid σ 4) • w) + 1 := by
    intro g g' hgg'
    obtain ⟨-, -, hγ, hδ⟩ := hsame g g' hgg'
    have hq1 := (hc g).2.2.2.2.2.2.2.2
    have hq2 := (hc g').2.2.2.2.2.2.2.2
    rw [hγ, hδ] at hq1
    have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
    have hxy : (herm σ w ((g.1 : SUid σ 4) • w) + herm σ w ((g'.1 : SUid σ 4) • w)) *
        (herm σ w ((g.1 : SUid σ 4) • w) + herm σ w ((g'.1 : SUid σ 4) • w) + 1) = 0 := by
      linear_combination hq1 - hq2 + (herm σ w ((g.1 : SUid σ 4) • w) *
        herm σ w ((g'.1 : SUid σ 4) • w) + herm σ w ((g'.1 : SUid σ 4) • w) ^ 2 +
        herm σ w ((g'.1 : SUid σ 4) • w)) * h2
    rcases mul_eq_zero.mp hxy with h | h
    · left
      linear_combination h - (herm σ w ((g'.1 : SUid σ 4) • w)) * h2
    · right
      linear_combination h - (herm σ w ((g'.1 : SUid σ 4) • w) + 1) * h2
  have hinj : ∀ g g' : S, M g = M g' →
      herm σ w ((g.1 : SUid σ 4) • w) = herm σ w ((g'.1 : SUid σ 4) • w) → g = g' := by
    intro g g' hgg' hA
    obtain ⟨hE, hF', hγ, hδ⟩ := hsame g g' hgg'
    have hW : (g.1 : SUid σ 4) • w = (g'.1 : SUid σ 4) • w := by
      rw [(hc g).2.2.1, (hc g').2.2.1, hA, hγ, hδ]
    exact Subtype.ext (Subtype.ext (eq_of_frame hinv hvv hww hee hff hvw hve hvf hwe hwf hef
      (g.2.trans g'.2.symm) hW hE hF'))
  have : Finite S := inferInstance
  have : Fintype S := Fintype.ofFinite S
  have : Finite K₀ := inferInstance
  have : Fintype (Matrix.SpecialLinearGroup (Fin 2) K₀) := Fintype.ofFinite _
  have hfib : ∀ M₀ ∈ (Finset.univ : Finset (Matrix.SpecialLinearGroup (Fin 2) K₀)),
      (Finset.univ.filter fun g : S => M g = M₀).card ≤ 2 := by
    intro M₀ _
    by_cases hne : (Finset.univ.filter fun g : S => M g = M₀).Nonempty
    · obtain ⟨g₀, hg₀⟩ := hne
      rw [Finset.mem_filter] at hg₀
      calc (Finset.univ.filter fun g : S => M g = M₀).card
          ≤ ({herm σ w ((g₀.1 : SUid σ 4) • w), herm σ w ((g₀.1 : SUid σ 4) • w) + 1} :
              Finset F).card := by
            refine Finset.card_le_card_of_injOn (fun g : S => herm σ w ((g.1 : SUid σ 4) • w))
              (fun g hg => ?_) (fun g hg g' hg' h => ?_)
            · have hg' := (Finset.mem_filter.mp (Finset.mem_coe.mp hg)).2
              rcases hroot g g₀ (hg'.trans hg₀.2.symm) with h | h
              · simp [h]
              · simp [h]
            · exact hinj g g' (((Finset.mem_filter.mp (Finset.mem_coe.mp hg)).2).trans
                ((Finset.mem_filter.mp (Finset.mem_coe.mp hg')).2).symm) h
        _ ≤ 2 := Finset.card_le_two
    · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.card_empty]
      exact Nat.zero_le _
  have hcard := Finset.card_le_mul_card_image_of_maps_to (s := Finset.univ)
    (t := Finset.univ) (f := M) (fun _ _ => Finset.mem_univ _) 2 hfib
  rw [Finset.card_univ, Finset.card_univ] at hcard
  rw [Nat.card_eq_fintype_card, ← hK₀, ← CFSG.GH74.Generic.BProg.B3.S1IdentSl2.card_sl2,
    Nat.card_eq_fintype_card]
  exact hcard

end Frame

end OrthogonalSubgroup

end CFSG.OddTranspositions.PartThree
