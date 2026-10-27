module

public import CFSG.RankThree.Transfer.FixedPoints
public import CFSG.RankThree.Transfer.Wreath
public import CFSG.RankThree.Transfer.PGroup

public section

namespace CFSG.RankThree.Transfer

open MulAction

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime] (P : Sylow p G)

local notation "N" => Subgroup.normalizer (((P : Sylow p G) : Subgroup G) : Set G)

theorem map_eq_one_of_orderOf_lt
    (μ : Subgroup.normalizer ((P : Subgroup G) : Set G) →* Multiplicative (ZMod p))
    (u : (P : Subgroup G))
    (hmin : ∀ v : (P : Subgroup G), μ (Subgroup.inclusion Subgroup.le_normalizer v) ≠ 1 →
      orderOf (u : G) ≤ orderOf (v : G))
    (h : Subgroup.normalizer ((P : Subgroup G) : Set G))
    (hlt : orderOf (h : G) < orderOf (u : G)) : μ h = 1 := by
  by_contra hne
  obtain ⟨a, m, hm, hord⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos (h : G)).ne' p hp.out.one_lt.ne'
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hm (dvd_zero p)
  have hμm : μ (h ^ m) ≠ 1 := by
    rw [map_pow]
    intro h1
    have hordμ : orderOf (μ h) = p := by
      refine orderOf_eq_prime ?_ hne
      have := pow_card_eq_one' (G := Multiplicative (ZMod p)) (x := μ h)
      rwa [card_multiplicative_zmod] at this
    exact hm (hordμ ▸ orderOf_dvd_of_pow_eq_one h1)
  have hpow : ((h : G) ^ m) ^ p ^ a = 1 := by
    rw [← pow_mul, mul_comm, ← hord, pow_orderOf_eq_one]
  have hmemP : (h : G) ^ m ∈ (P : Subgroup G) :=
    mem_of_pow_eq_one_of_mem_normalizer P (Subgroup.pow_mem _ h.2 m) hpow
  have hordm : orderOf ((h : G) ^ m) = p ^ a := by
    rw [orderOf_pow_of_dvd hm0 (Dvd.intro_left _ hord.symm), hord,
      Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hm0)]
  have hle := hmin ⟨_, hmemP⟩ (by
    convert hμm using 2
    exact Subtype.ext (by simp))
  have : orderOf ((h : G) ^ m) ≤ orderOf (h : G) := by
    rw [hordm, hord]
    exact Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hm0)
  simp only at hle
  omega

theorem exists_surjective_regularWreathProduct_of_transfer_eq_one
    (μ : Subgroup.normalizer ((P : Subgroup G) : Set G) →* Multiplicative (ZMod p))
    (hμ : ∃ u : (P : Subgroup G), μ (Subgroup.inclusion Subgroup.le_normalizer u) ≠ 1)
    (hV : ∀ g : G, μ.transfer g = 1) :
    ∃ Ψ : (P : Subgroup G) →* Multiplicative (ZMod p) ≀ᵣ Multiplicative (ZMod p),
      Function.Surjective Ψ := by
  classical
  have hPN : (P : Subgroup G) ≤ N := Subgroup.le_normalizer
  have hex : ∃ n, ∃ v : (P : Subgroup G), μ (Subgroup.inclusion hPN v) ≠ 1 ∧
      orderOf (v : G) = n := ⟨_, hμ.choose, hμ.choose_spec, rfl⟩
  obtain ⟨u, hu1, hun⟩ := Nat.find_spec hex
  have hmin : ∀ v : (P : Subgroup G), μ (Subgroup.inclusion hPN v) ≠ 1 →
      orderOf (u : G) ≤ orderOf (v : G) := by
    intro v hv
    rw [hun]
    exact Nat.find_min' hex ⟨v, hv, rfl⟩
  have hMinOrd := map_eq_one_of_orderOf_lt P μ u hmin
  have : Fintype (G ⧸ N) := Fintype.ofFinite _
  set F : G ⧸ N → Multiplicative (ZMod p) :=
    fun X => if (u : G) • X = X then cosetValue μ (u : G) X else 1 with hF
  have htot : ∏ X, F X = 1 := by
    rw [hF, ← transfer_eq_prod_fixed_of_orderOf_lt μ (u : G) hMinOrd]
    exact hV _
  set X₁ : G ⧸ N := ((1 : G) : G ⧸ N) with hX₁
  let π : G ⧸ N → MulAction.orbitRel.Quotient (P : Subgroup G) (G ⧸ N) := Quotient.mk''
  have : Fintype (MulAction.orbitRel.Quotient (P : Subgroup G) (G ⧸ N)) := Fintype.ofFinite _
  have hπ : ∀ X Y : G ⧸ N, π X = π Y ↔ X ∈ MulAction.orbit (P : Subgroup G) Y := by
    intro X Y
    exact Quotient.eq''.trans MulAction.orbitRel_apply
  have hfib₁ : (Finset.univ.filter fun X => π X = π X₁) = {X₁} := by
    ext X
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, hπ]
    constructor
    · rintro ⟨c, rfl⟩
      change c • X₁ = X₁
      rw [Subgroup.smul_def, hX₁, MulAction.Quotient.smul_mk, smul_eq_mul, mul_one,
        QuotientGroup.eq, mul_one]
      exact Subgroup.inv_mem _ (hPN c.2)
    · rintro rfl
      exact MulAction.mem_orbit_self _
  have hFX₁ : F X₁ ≠ 1 := by
    have hfix : (u : G) • X₁ = X₁ := by
      rw [hX₁, smul_coe_eq_iff]
      simpa using hPN u.2
    rw [hF]
    simp only [hfix, ite_true]
    rw [hX₁, cosetValue_coe μ (by simpa using hPN u.2)]
    convert hu1 using 2
    exact Subtype.ext (by simp)
  obtain ⟨o, ho, hoprod⟩ : ∃ o, o ≠ π X₁ ∧
      ∏ X ∈ Finset.univ.filter (fun X => π X = o), F X ≠ 1 := by
    by_contra hcon
    push Not at hcon
    apply hFX₁
    rw [← htot, ← Finset.prod_fiberwise Finset.univ π F,
      Finset.prod_eq_single (π X₁) (fun o _ hne => hcon o hne)
        (fun h => absurd (Finset.mem_univ _) h), hfib₁, Finset.prod_singleton]
  obtain ⟨X₀, hX₀mem, hX₀ne⟩ := Finset.exists_ne_one_of_prod_ne_one hoprod
  have hπX₀ : π X₀ = o := (Finset.mem_filter.mp hX₀mem).2
  have hfixX₀ : (u : G) • X₀ = X₀ := by
    by_contra h
    exact hX₀ne (by rw [hF]; simp only [h, ite_false])
  set g : G := Quotient.out X₀ with hg
  have hgX₀ : (g : G ⧸ N) = X₀ := QuotientGroup.out_eq' X₀
  set R : Subgroup (P : Subgroup G) := MulAction.stabilizer (P : Subgroup G) X₀ with hR
  have hRmem : ∀ c : (P : Subgroup G), c ∈ R ↔ g⁻¹ * (c : G) * g ∈ N := by
    intro c
    rw [hR, MulAction.mem_stabilizer_iff, Subgroup.smul_def, ← hgX₀, smul_coe_eq_iff]
  have huR : u ∈ R := by
    rw [hR, MulAction.mem_stabilizer_iff, Subgroup.smul_def]
    exact hfixX₀
  have hRne : R ≠ ⊤ := by
    intro htop
    have hgN : g ∈ N := mem_normalizer_of_forall_conj_mem_normalizer P fun c hc =>
      (hRmem ⟨c, hc⟩).mp (htop ▸ Subgroup.mem_top _)
    apply ho
    have hX₀X₁ : X₀ = X₁ := by
      rw [← hgX₀, hX₁, QuotientGroup.eq, mul_one]
      exact Subgroup.inv_mem _ hgN
    rw [← hπX₀, hX₀X₁]
  let θg : R →* Multiplicative (ZMod p) :=
    MonoidHom.mk' (fun c => μ ⟨g⁻¹ * ((c : (P : Subgroup G)) : G) * g, (hRmem c).mp c.2⟩)
      (fun a b => by
        rw [← map_mul]
        congr 1
        apply Subtype.ext
        simp only [Subgroup.coe_mul]
        group)
  obtain ⟨φ, hφs, hRφ⟩ := exists_surjective_zmod_of_ne_top P.isPGroup' hRne
  set t := Function.surjInv hφs with ht_def
  have ht : ∀ x, φ (t x) = x := Function.surjInv_eq hφs
  set R' : Subgroup φ.ker := R.subgroupOf φ.ker with hR'
  let θ' : R' →* Multiplicative (ZMod p) :=
    θg.comp (Subgroup.subgroupOfEquivOfLe hRφ).toMonoidHom
  have hθ'mem : ∀ r : R', g⁻¹ * (((r : φ.ker) : (P : Subgroup G)) : G) * g ∈ N :=
    fun r => (hRmem _).mp (Subgroup.mem_subgroupOf.mp r.2)
  have hθ' : ∀ r : R', θ' r = μ ⟨_, hθ'mem r⟩ := by
    intro r
    change μ _ = μ _
    congr 2
  let θ₁ : φ.ker →* Multiplicative (ZMod p) := θ'.transfer
  set u₁ : φ.ker := ⟨u, hRφ huR⟩ with hu₁
  refine exists_surjective_regularWreathProduct hp.out φ t ht θ₁ u₁ ?_
  have hux : ∀ x, (((MulAut.conjNormal (t x)⁻¹ u₁ : φ.ker) : (P : Subgroup G)) : G) =
      ((t x : (P : Subgroup G)) : G)⁻¹ * u * (t x : (P : Subgroup G)) := by
    intro x
    simp [hu₁]
  have hordux : ∀ x, orderOf (MulAut.conjNormal (t x)⁻¹ u₁) = orderOf (u : G) := by
    intro x
    rw [← Subgroup.orderOf_coe, ← Subgroup.orderOf_coe, hux, orderOf_conj]
  have hyp : ∀ x, ∀ h : R', orderOf (h : φ.ker) < orderOf (MulAut.conjNormal (t x)⁻¹ u₁) →
      θ' h = 1 := by
    intro x h hlt
    rw [hθ']
    apply hMinOrd
    simp only
    rw [orderOf_conj, Subgroup.orderOf_coe, Subgroup.orderOf_coe, ← hordux x]
    exact hlt
  have : Fintype (φ.ker ⧸ R') := Fintype.ofFinite _
  set F' : Multiplicative (ZMod p) → φ.ker ⧸ R' → Multiplicative (ZMod p) :=
    fun x Z => if MulAut.conjNormal (t x)⁻¹ u₁ • Z = Z then
      cosetValue θ' (MulAut.conjNormal (t x)⁻¹ u₁ : φ.ker) Z else 1 with hF'
  have hθ₁ : ∀ x, θ₁ (MulAut.conjNormal (t x)⁻¹ u₁) = ∏ Z, F' x Z := fun x =>
    transfer_eq_prod_fixed_of_orderOf_lt θ' _ (hyp x)
  let Θ : Multiplicative (ZMod p) × (φ.ker ⧸ R') → G ⧸ N := fun xZ =>
    (((t xZ.1 * ((Quotient.out xZ.2 : φ.ker) : (P : Subgroup G)) : (P : Subgroup G)) : G) * g :
      G ⧸ N)
  have hΘsmul : ∀ (c : (P : Subgroup G)), (((c : G) * g : G) : G ⧸ N) = c • X₀ := by
    intro c
    rw [Subgroup.smul_def, ← hgX₀, MulAction.Quotient.smul_mk, smul_eq_mul]
  have hΘ : ∏ x, ∏ Z, F' x Z = ∏ X ∈ Finset.univ.filter (fun X => π X = o), F X := by
    rw [← Fintype.prod_prod_type']
    refine Finset.prod_bij (fun xZ _ => Θ xZ) ?_ ?_ ?_ ?_
    · intro xZ _
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [← hπX₀]
      refine (hπ _ _).mpr ?_
      change ((((t xZ.1 * ((Quotient.out xZ.2 : φ.ker) : (P : Subgroup G)) :
        (P : Subgroup G)) : G) * g : G) : G ⧸ N) ∈ _
      rw [hΘsmul]
      exact MulAction.mem_orbit X₀ _
    · rintro ⟨x, Z⟩ _ ⟨x', Z'⟩ _ h
      change ((((t x * ((Quotient.out Z : φ.ker) : (P : Subgroup G)) :
        (P : Subgroup G)) : G) * g : G) : G ⧸ N) =
          ((((t x' * ((Quotient.out Z' : φ.ker) : (P : Subgroup G)) :
            (P : Subgroup G)) : G) * g : G) : G ⧸ N) at h
      rw [QuotientGroup.eq] at h
      set c : (P : Subgroup G) := t x * ((Quotient.out Z : φ.ker) : (P : Subgroup G)) with hc
      set c' : (P : Subgroup G) := t x' * ((Quotient.out Z' : φ.ker) : (P : Subgroup G))
        with hc'
      have hcR : c⁻¹ * c' ∈ R := by
        rw [hRmem]
        convert h using 1
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group
      have hφc : φ (c⁻¹ * c') = 1 := hRφ hcR
      have hφZ : φ ((Quotient.out Z : φ.ker) : (P : Subgroup G)) = 1 := (Quotient.out Z).2
      have hφZ' : φ ((Quotient.out Z' : φ.ker) : (P : Subgroup G)) = 1 := (Quotient.out Z').2
      have hxx' : x = x' := by
        rw [map_mul, map_inv, hc, hc', map_mul, map_mul, ht, ht, hφZ, hφZ', mul_one,
          mul_one] at hφc
        exact inv_mul_eq_one.mp hφc
      subst hxx'
      have hZZ : Z = Z' := by
        rw [← QuotientGroup.out_eq' Z, ← QuotientGroup.out_eq' Z', QuotientGroup.eq]
        refine Subgroup.mem_subgroupOf.mpr ?_
        convert hcR using 1
        rw [hc, hc']
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group
      rw [hZZ]
    · intro X hX
      rw [Finset.mem_filter] at hX
      obtain ⟨c, hc⟩ := MulAction.mem_orbit_iff.mp ((hπ X X₀).mp (hX.2.trans hπX₀.symm))
      have hr : (t (φ c))⁻¹ * c ∈ φ.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, ht, inv_mul_cancel]
      obtain ⟨s, hs⟩ := QuotientGroup.mk_out_eq_mul R' (⟨_, hr⟩ : φ.ker)
      refine ⟨(φ c, ((⟨_, hr⟩ : φ.ker) : φ.ker ⧸ R')), Finset.mem_univ _, ?_⟩
      change ((((t (φ c) * ((Quotient.out ((⟨_, hr⟩ : φ.ker) : φ.ker ⧸ R') : φ.ker) :
        (P : Subgroup G)) : (P : Subgroup G)) : G) * g : G) : G ⧸ N) = X
      rw [hΘsmul, hs]
      have hsR : (((s : φ.ker) : (P : Subgroup G))) ∈ R := Subgroup.mem_subgroupOf.mp s.2
      have hcs : t (φ c) * (((⟨_, hr⟩ : φ.ker) * (s : φ.ker) : φ.ker) : (P : Subgroup G)) =
          c * ((s : φ.ker) : (P : Subgroup G)) := by
        simp only [Subgroup.coe_mul]
        group
      rw [hcs, mul_smul, MulAction.mem_stabilizer_iff.mp hsR, hc]
    · rintro ⟨x, Z⟩ _
      set c : (P : Subgroup G) := t x * ((Quotient.out Z : φ.ker) : (P : Subgroup G)) with hc
      set ux : φ.ker := MulAut.conjNormal (t x)⁻¹ u₁ with hux'
      have hw : ((((Quotient.out Z)⁻¹ * ux * Quotient.out Z : φ.ker) : (P : Subgroup G)) : G) =
          (c : G)⁻¹ * u * c := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        rw [hux', hux x, hc]
        simp only [Subgroup.coe_mul]
        group
      have hΘc : Θ (x, Z) = (((c : G) * g : G) : G ⧸ N) := rfl
      have hfixiff : ux • Z = Z ↔ (u : G) • Θ (x, Z) = Θ (x, Z) := by
        rw [smul_eq_self_iff_out]
        change _ ∈ R.subgroupOf φ.ker ↔ _
        rw [Subgroup.mem_subgroupOf, hRmem, hΘc, smul_coe_eq_iff, hw]
        constructor <;> intro h <;> convert h using 1 <;> group
      change (if ux • Z = Z then cosetValue θ' (ux : φ.ker) Z else 1) =
        (if (u : G) • Θ (x, Z) = Θ (x, Z) then cosetValue μ (u : G) (Θ (x, Z)) else 1)
      by_cases hfix : ux • Z = Z
      · rw [ite_eq_left hfix, ite_eq_left (hfixiff.mp hfix),
          cosetValue_of_mem θ' (smul_eq_self_iff_out.mp hfix), hθ', hΘc,
          cosetValue_coe μ (smul_coe_eq_iff.mp (hΘc ▸ hfixiff.mp hfix))]
        congr 1
        apply Subtype.ext
        change g⁻¹ * ((((Quotient.out Z)⁻¹ * ux * Quotient.out Z : φ.ker) :
          (P : Subgroup G)) : G) * g = _
        rw [hw]
        group
      · rw [ite_eq_right hfix, ite_eq_right fun h => hfix (hfixiff.mpr h)]
  simp_rw [hθ₁]
  rw [hΘ]
  exact hoprod

end CFSG.RankThree.Transfer

end
