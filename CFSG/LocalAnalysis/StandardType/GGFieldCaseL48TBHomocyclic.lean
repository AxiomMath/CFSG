module

public import CFSG.LocalAnalysis.StandardType.GGFieldCaseXL48Homocyclic

public section

namespace CFSG.StandardType

theorem one_add_pow_of_mul_self_eq_zero {R : Type*} [CommRing R] {a : R} (ha : a * a = 0)
    (r : ℕ) : (1 + a) ^ r = 1 + r * a := by
  induction r with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih]
    calc (1 + n * a) * (1 + a) = 1 + (n + 1) * a + n * (a * a) := by ring
      _ = 1 + ((n + 1 : ℕ) : R) * a := by rw [ha]; push_cast; ring

theorem one_add_pow_ne_one {p s r : ℕ} (hp : p.Prime) (hs : 2 ≤ s) (hr : ¬ p ∣ r) :
    (1 + (p : ZMod (p ^ s)) ^ (s - 1)) ^ r ≠ 1 := by
  have ha : (p : ZMod (p ^ s)) ^ (s - 1) * (p : ZMod (p ^ s)) ^ (s - 1) = 0 := by
    rw [← pow_add, ← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
    exact pow_dvd_pow p (by omega)
  rw [one_add_pow_of_mul_self_eq_zero ha]
  intro h
  have h0 : ((r * p ^ (s - 1) : ℕ) : ZMod (p ^ s)) = 0 := by
    push_cast
    linear_combination h
  rw [ZMod.natCast_eq_zero_iff] at h0
  apply hr
  have hps : p ^ s = p * p ^ (s - 1) := by
    rw [← pow_succ']; congr 1; omega
  rw [hps] at h0
  exact (Nat.mul_dvd_mul_iff_right (pow_pos hp.pos _)).mp h0

variable {G : Type} [Group G]

@[expose] noncomputable def homocyclicLinear {p s r : ℕ} {U : Subgroup G}
    (e : Additive U ≃+ (Fin r → ZMod (p ^ s))) (n : Subgroup.normalizer (U : Set G)) :
    (Fin r → ZMod (p ^ s)) ≃ₗ[ZMod (p ^ s)] (Fin r → ZMod (p ^ s)) :=
  let f : (Fin r → ZMod (p ^ s)) ≃+ (Fin r → ZMod (p ^ s)) :=
    (e.symm.trans (MulEquiv.toAdditive (U.normalizerMonoidHom n))).trans e
  { f with map_smul' := fun c v => (f.toAddMonoidHom.toZModLinearMap (p ^ s)).map_smul c v }

theorem homocyclicLinear_apply {p s r : ℕ} {U : Subgroup G}
    (e : Additive U ≃+ (Fin r → ZMod (p ^ s))) (n : Subgroup.normalizer (U : Set G))
    (v : Fin r → ZMod (p ^ s)) :
    homocyclicLinear e n v = e (Additive.ofMul (U.normalizerMonoidHom n (e.symm v).toMul)) :=
  rfl

@[expose] noncomputable def homocyclicDet {p s r : ℕ} {U : Subgroup G}
    (e : Additive U ≃+ (Fin r → ZMod (p ^ s))) :
    Subgroup.normalizer (U : Set G) →* (ZMod (p ^ s))ˣ :=
  LinearEquiv.det.comp
    { toFun := homocyclicLinear e
      map_one' := by
        ext v i
        simp [homocyclicLinear_apply]
      map_mul' := fun a b => by
        ext v i
        simp [homocyclicLinear_apply] }

theorem exists_monoidHom_zmod_ne_one_of_homocyclic [Finite G] {p : ℕ} [hp : Fact p.Prime]
    {x : G} {U : Subgroup G} {s r : ℕ} (hs : 2 ≤ s) (hr : ¬ p ∣ r)
    (e : Additive U ≃+ (Fin r → ZMod (p ^ s))) (hxp : x ^ p = 1)
    (hx : ∀ u ∈ U, x⁻¹ * u * x = u ^ (1 + p ^ (s - 1))) :
    ∃ ψ : Subgroup.normalizer (U : Set G) →* Multiplicative (ZMod p), ψ ≠ 1 := by
  set N₀ := Subgroup.normalizer (U : Set G) with hN₀
  have hxN : x⁻¹ ∈ N₀ := by
    have hle : U.map (MulAut.conj x⁻¹).toMonoidHom ≤ U := by
      rintro _ ⟨u, hu, rfl⟩
      change x⁻¹ * u * x⁻¹⁻¹ ∈ U
      rw [inv_inv, hx u hu]
      exact U.pow_mem hu _
    have heq : U.map (MulAut.conj x⁻¹).toMonoidHom = U :=
      Subgroup.eq_of_le_of_card_ge hle
        (by rw [Subgroup.card_map_of_injective (MulAut.conj x⁻¹).injective])
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr heq
  have h1 : Fact (1 < p ^ s) := ⟨Nat.one_lt_pow (by omega) hp.out.one_lt⟩
  set n : N₀ := ⟨x⁻¹, hxN⟩ with hn
  set c : ZMod (p ^ s) := 1 + (p : ZMod (p ^ s)) ^ (s - 1) with hc
  have hlin : (homocyclicLinear e n : (Fin r → ZMod (p ^ s)) →ₗ[ZMod (p ^ s)] _) =
      c • LinearMap.id := by
    apply LinearMap.ext
    intro v
    rw [LinearEquiv.coe_coe, homocyclicLinear_apply, LinearMap.smul_apply, LinearMap.id_apply]
    have hu := hx _ (e.symm v).toMul.2
    have hconj :
        U.normalizerMonoidHom n (e.symm v).toMul = (e.symm v).toMul ^ (1 + p ^ (s - 1)) := by
      apply Subtype.ext
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe, SubgroupClass.coe_pow, hn]
      simpa using hu
    rw [hconj, ofMul_pow, map_nsmul, ofMul_toMul, AddEquiv.apply_symm_apply]
    rw [hc, ← Nat.cast_smul_eq_nsmul (ZMod (p ^ s))]
    push_cast
    rfl
  have hdet : (homocyclicDet e n : ZMod (p ^ s)) = c ^ r := by
    change ((LinearEquiv.det (homocyclicLinear e n) : (ZMod (p ^ s))ˣ) : ZMod (p ^ s)) = _
    rw [LinearEquiv.coe_det, hlin, LinearMap.det_smul, LinearMap.det_id, mul_one,
      Module.finrank_fin_fun]
  have hne : homocyclicDet e n ≠ 1 := by
    intro h
    apply one_add_pow_ne_one hp.out hs hr
    rw [← hc, ← hdet, h, Units.val_one]
  have hxc : x ∉ ⁅N₀, N₀⁆ := by
    intro hxc
    have hxc' : x⁻¹ ∈ ⁅N₀, N₀⁆ := Subgroup.inv_mem _ hxc
    rw [← N₀.map_subtype_commutator] at hxc'
    obtain ⟨y, hy, hyx⟩ := hxc'
    have hyn : y = n := Subtype.ext hyx
    apply hne
    rw [← hyn]
    exact Abelianization.commutator_subset_ker (homocyclicDet e) hy
  have hxN' : x ∈ N₀ := by simpa using N₀.inv_mem hxN
  exact exists_monoidHom_zmod_ne_one_of_not_mem_commutator' hxN' hxp hxc

theorem exists_pow_eq_of_mem_closure_pow {U : Subgroup G} (hab : IsMulCommutative U) (k : ℕ)
    {g : G} (hg : g ∈ Subgroup.closure {w | ∃ v ∈ U, v ^ k = w}) : ∃ v ∈ U, v ^ k = g := by
  have hc : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hab.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  induction hg using Subgroup.closure_induction with
  | mem w hw => exact hw
  | one => exact ⟨1, U.one_mem, one_pow k⟩
  | mul a b _ _ ha hb =>
    obtain ⟨v, hv, rfl⟩ := ha
    obtain ⟨w, hw, rfl⟩ := hb
    exact ⟨v * w, U.mul_mem hv hw, (Commute.mul_pow (hc v hv w hw) k)⟩
  | inv a _ ha =>
    obtain ⟨v, hv, rfl⟩ := ha
    exact ⟨v⁻¹, U.inv_mem hv, inv_pow v k⟩

theorem ggL48Homocyclic_of_irreducible {p : ℕ} (hp1 : 1 < p) {U₁ B₁ A : Subgroup G}
    (hab : IsMulCommutative U₁)
    (hAN : A ≤ Subgroup.normalizer (U₁ : Set G)) (hB₁ : ∀ u, u ∈ B₁ ↔ u ∈ U₁ ∧ u ^ p = 1)
    (hirr : ∀ M : Subgroup G, M ≤ B₁ → M ≠ ⊥ → (∀ a ∈ A, ∀ m ∈ M, a * m * a⁻¹ ∈ M) → M = B₁) :
    GGL48Homocyclic p U₁ := by
  intro s hs hexp ⟨u₀, hu₀, hord⟩ b hb hbp
  set M := Subgroup.closure {w | ∃ v ∈ U₁, v ^ p ^ (s - 1) = w} with hM
  have hps : p ^ s = p ^ (s - 1) * p := by rw [← pow_succ]; congr 1; omega
  have hMB : M ≤ B₁ := by
    rw [hM, Subgroup.closure_le]
    rintro _ ⟨v, hv, rfl⟩
    refine (hB₁ _).mpr ⟨U₁.pow_mem hv _, ?_⟩
    rw [← pow_mul, ← hps]
    exact hexp v hv
  have hM1 : M ≠ ⊥ := by
    intro h
    have hmem : u₀ ^ p ^ (s - 1) ∈ M := Subgroup.subset_closure ⟨u₀, hu₀, rfl⟩
    rw [h, Subgroup.mem_bot] at hmem
    have hdvd := orderOf_dvd_of_pow_eq_one hmem
    rw [hord] at hdvd
    have := Nat.pow_dvd_pow_iff_le_right hp1 |>.mp hdvd
    omega
  have hMA : ∀ a ∈ A, ∀ m ∈ M, a * m * a⁻¹ ∈ M := by
    intro a ha m hm
    obtain ⟨v, hv, rfl⟩ := exists_pow_eq_of_mem_closure_pow hab _ hm
    refine Subgroup.subset_closure ⟨a * v * a⁻¹, ?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp (hAN ha) v).mp hv
    · rw [conj_pow]
  have heq := hirr M hMB hM1 hMA
  have hbM : b ∈ M := heq ▸ (hB₁ b).mpr ⟨hb, hbp⟩
  exact exists_pow_eq_of_mem_closure_pow hab _ hbM

theorem card_nsmul_eq_zero_zmod {p s : ℕ} (hp : p.Prime) (hs : 1 ≤ s) :
    Nat.card {z : ZMod (p ^ s) // p • z = 0} = p := by
  haveI : NeZero (p ^ s) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hps : p ^ s = p * p ^ (s - 1) := by rw [← pow_succ']; congr 1; omega
  set a : ZMod (p ^ s) := ((p ^ (s - 1) : ℕ) : ZMod (p ^ s)) with ha
  have h0 : p • a = 0 := by
    rw [ha, nsmul_eq_mul, ← Nat.cast_mul, ← hps, ZMod.natCast_self]
  have hiff : ∀ z : ZMod (p ^ s), p • z = 0 ↔ z ∈ AddSubgroup.zmultiples a := by
    intro z
    rw [AddSubgroup.mem_zmultiples_iff]
    constructor
    · intro hz
      have hz' : ((p * z.val : ℕ) : ZMod (p ^ s)) = 0 := by
        rw [Nat.cast_mul, ZMod.natCast_zmod_val, ← nsmul_eq_mul]; exact hz
      rw [ZMod.natCast_eq_zero_iff] at hz'
      have hz'' : p * p ^ (s - 1) ∣ p * z.val := by rw [← hps]; exact hz'
      obtain ⟨t, ht⟩ := (Nat.mul_dvd_mul_iff_left hp.pos).mp hz''
      refine ⟨t, ?_⟩
      rw [zsmul_eq_mul, Int.cast_natCast, ha, ← Nat.cast_mul, mul_comm, ← ht,
        ZMod.natCast_zmod_val]
    · rintro ⟨t, rfl⟩
      rw [smul_comm, h0, smul_zero]
  rw [Nat.card_congr (Equiv.subtypeEquivRight hiff), Nat.card_zmultiples, ha,
    ZMod.addOrderOf_coe _ (pow_ne_zero _ hp.ne_zero),
    Nat.gcd_eq_right (pow_dvd_pow p (Nat.sub_le s 1)), hps,
    Nat.mul_div_cancel _ (pow_pos hp.pos _)]

theorem exists_homocyclic_model [Finite G] {p : ℕ} (hp : p.Prime) {U : Subgroup G}
    (hab : IsMulCommutative U) {s m : ℕ} (hs : 1 ≤ s) (hexp : ∀ u ∈ U, u ^ p ^ s = 1)
    (hhom : ∀ b ∈ U, b ^ p = 1 → ∃ v ∈ U, v ^ p ^ (s - 1) = b)
    {B : Subgroup G} (hB : ∀ u, u ∈ B ↔ u ∈ U ∧ u ^ p = 1) (hcard : Nat.card B = p ^ m) :
    Nonempty (Additive U ≃+ (Fin m → ZMod (p ^ s))) := by
  classical
  letI : CommGroup U := { (inferInstance : Group U) with mul_comm := hab.is_comm.comm }
  haveI : Finite (Additive U) := inferInstanceAs (Finite U)
  obtain ⟨ι, _, n, hn, ⟨f⟩⟩ := AddCommGroup.equiv_directSum_zmod_of_finite' (Additive U)
  set F : Additive U ≃+ ((i : ι) → ZMod (n i)) :=
    f.trans (DirectSum.linearEquivFunOnFintype ℤ ι (fun i => ZMod (n i))).toAddEquiv with hF
  have hpow : ∀ (a : Additive U) (k : ℕ), k • a = 0 ↔ ((Additive.toMul a : U) : G) ^ k = 1 := by
    intro a k
    rw [← Additive.toMul.injective.eq_iff, toMul_nsmul, toMul_zero, Subtype.ext_iff,
      SubgroupClass.coe_pow, OneMemClass.coe_one]
  have hexpA : ∀ a : Additive U, (p ^ s) • a = 0 := fun a =>
    (hpow a _).mpr (hexp _ (Additive.toMul a).2)
  have hhomA : ∀ b : Additive U, p • b = 0 → ∃ v : Additive U, (p ^ (s - 1)) • v = b := by
    intro b hb
    obtain ⟨v, hv, hvb⟩ := hhom _ (Additive.toMul b).2 ((hpow b p).mp hb)
    refine ⟨Additive.ofMul ⟨v, hv⟩, ?_⟩
    apply Additive.toMul.injective
    rw [toMul_nsmul, toMul_ofMul]
    exact Subtype.ext (by rw [SubgroupClass.coe_pow]; exact hvb)
  have hni : ∀ i, n i = p ^ s := by
    intro i
    have h1 : n i ∣ p ^ s := by
      have h := congrFun (congrArg F (hexpA (F.symm (Pi.single i 1)))) i
      rw [map_nsmul, AddEquiv.apply_symm_apply, map_zero, Pi.smul_apply, Pi.single_eq_same,
        Pi.zero_apply, nsmul_eq_mul, mul_one] at h
      exact (ZMod.natCast_eq_zero_iff _ _).mp h
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow hp).mp h1
    have hk1 : 1 ≤ k := by
      rcases Nat.eq_zero_or_pos k with h | h
      · have := hn i; rw [hk', h, pow_zero] at this; omega
      · exact h
    by_contra hne
    have hks : k ≤ s - 1 := by
      have : k ≠ s := fun h => hne (by rw [hk', h])
      omega
    set c : ZMod (n i) := ((p ^ (k - 1) : ℕ) : ZMod (n i)) with hc
    have hpc : p • c = 0 := by
      rw [hc, nsmul_eq_mul, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff, hk']
      exact ⟨1, by rw [mul_one, ← pow_succ', Nat.sub_add_cancel hk1]⟩
    obtain ⟨v, hv⟩ := hhomA (F.symm (Pi.single i c)) (by
      apply F.injective
      rw [map_nsmul, AddEquiv.apply_symm_apply, map_zero]
      funext j
      rw [Pi.smul_apply, Pi.zero_apply]
      by_cases hj : j = i
      · subst hj; rw [Pi.single_eq_same]; exact hpc
      · rw [Pi.single_eq_of_ne hj, smul_zero])
    have h2 := congrFun (congrArg F hv) i
    rw [map_nsmul, AddEquiv.apply_symm_apply, Pi.smul_apply, Pi.single_eq_same,
      nsmul_eq_mul] at h2
    have h3 : ((p ^ (s - 1) : ℕ) : ZMod (n i)) = 0 := by
      rw [ZMod.natCast_eq_zero_iff, hk']; exact pow_dvd_pow p hks
    rw [h3, zero_mul, hc] at h2
    have h4 := (ZMod.natCast_eq_zero_iff _ _).mp h2.symm
    rw [hk'] at h4
    have := (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp h4
    omega
  set E : Additive U ≃+ (ι → ZMod (p ^ s)) :=
    F.trans (AddEquiv.piCongrRight (fun i => (ZMod.ringEquivCongr (hni i)).toAddEquiv)) with hE
  have hc1 : Nat.card B = Nat.card {a : Additive U // p • a = 0} := by
    refine Nat.card_congr
      { toFun := fun b => ⟨Additive.ofMul ⟨b.1, ((hB b.1).mp b.2).1⟩,
          (hpow _ p).mpr ((hB b.1).mp b.2).2⟩
        invFun := fun a => ⟨((Additive.toMul a.1 : U) : G),
          (hB _).mpr ⟨(Additive.toMul a.1).2, (hpow a.1 p).mp a.2⟩⟩
        left_inv := fun b => rfl
        right_inv := fun a => rfl }
  have hc2 : Nat.card {a : Additive U // p • a = 0} =
      Nat.card {w : ι → ZMod (p ^ s) // p • w = 0} :=
    Nat.card_congr (Equiv.subtypeEquiv E.toEquiv (fun a => by
      change p • a = 0 ↔ p • E a = 0
      rw [← map_nsmul, E.map_eq_zero_iff]))
  have hc3 : Nat.card {w : ι → ZMod (p ^ s) // p • w = 0} = p ^ Fintype.card ι := by
    rw [Nat.card_congr ((Equiv.subtypeEquivRight (fun w : ι → ZMod (p ^ s) =>
        (show p • w = 0 ↔ ∀ i, p • w i = 0 from
          ⟨fun h i => by simpa using congrFun h i,
            fun h => funext fun i => by simpa using h i⟩))).trans
        (@Equiv.subtypePiEquivPi ι (fun _ => ZMod (p ^ s)) (fun _ b => p • b = 0))), Nat.card_pi]
    simp only [card_nsmul_eq_zero_zmod hp hs, Finset.prod_const, Finset.card_univ]
  have hm : m = Fintype.card ι :=
    Nat.pow_right_injective hp.two_le (hcard.symm.trans (hc1.trans (hc2.trans hc3)))
  exact ⟨E.trans (LinearEquiv.funCongrLeft ℤ (ZMod (p ^ s))
    ((finCongr hm).trans (Fintype.equivFin ι).symm)).toAddEquiv⟩

theorem exists_monoidHom_of_irreducible [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J X B₂ : Subgroup G} {d y : G} {K U U₁ : Subgroup G}
    (hS : GGFieldCaseSetup p B Bs x L D J X B₂ d y K U U₁) (h46 : GGL46 p Bs x X U U₁)
    {A : Subgroup G} (hAN : A ≤ Subgroup.normalizer (U₁ : Set G))
    (hirr : ∀ M : Subgroup G, M ≤ Bs ⊓ Subgroup.centralizer (X : Set G) → M ≠ ⊥ →
      (∀ a ∈ A, ∀ m ∈ M, a * m * a⁻¹ ∈ M) → M = Bs ⊓ Subgroup.centralizer (X : Set G))
    {m : ℕ} (hm : Nat.card (Bs ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) = p ^ m)
    (hpm : ¬ p ∣ m) :
    ∃ ψ : Subgroup.normalizer (U₁ : Set G) →* Multiplicative (ZMod p), ψ ≠ 1 := by
  have hp : p.Prime := hS.1.1.1.2.2.2.2.2.1.1
  haveI : Fact p.Prime := ⟨hp⟩
  have hBp : ∀ b ∈ Bs, b ^ p = 1 := hS.1.1.2.1.2.1.2
  have hxBs : x ∈ Bs := by
    rw [hS.2.2.1.2]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
  have hB₁ := h46.2.2.2.1
  obtain ⟨hab, ⟨s, hs2, hexp, ⟨u₀, hu₀, hord⟩, ⟨x', hx'x, hx'⟩, -⟩, -⟩ := h46
  have hhom := ggL48Homocyclic_of_irreducible hp.one_lt hab hAN hB₁ hirr s hs2 hexp ⟨u₀, hu₀, hord⟩
  obtain ⟨e⟩ := exists_homocyclic_model hp hab (by omega) hexp hhom hB₁ hm
  have hx'Bs : x' ∈ Bs := by
    have : x' ∈ Subgroup.zpowers x := hx'x ▸ Subgroup.mem_zpowers x'
    obtain ⟨k, rfl⟩ := this
    exact Bs.zpow_mem hxBs k
  exact exists_monoidHom_zmod_ne_one_of_homocyclic hs2 hpm e (hBp x' hx'Bs) hx'

end CFSG.StandardType
