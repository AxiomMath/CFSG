module

public import CFSG.Quasithin.SteinbergBQPlaneEigen
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismGeneration

public section

namespace CFSG.Quasithin.SteinbergBQ

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {F : Type*} [Field F] {p : ℕ}

theorem pow_three_eq_one_of_mem_scalars {z : SpecialLinearGroup (Fin 3) F}
    (hz : z ∈ scalars 3 F) : z ^ 3 = 1 := by
  obtain ⟨c, hc, hz⟩ := hz
  apply Subtype.ext
  change (z : Matrix (Fin 3) (Fin 3) F) ^ 3 = 1
  rw [hz, ← map_pow, ← Units.val_pow_eq_pow_val, hc, Units.val_one, map_one]

theorem eq_one_of_mem_scalars_of_pow_prime [hp : Fact p.Prime] (hp3 : p ≠ 3)
    {z : SpecialLinearGroup (Fin 3) F} (hz : z ∈ scalars 3 F) (hzp : z ^ p = 1) : z = 1 := by
  have hcop : Nat.gcd p 3 = 1 := (Nat.coprime_primes hp.out Nat.prime_three).2 hp3
  have h := pow_gcd_eq_one.2 ⟨hzp, pow_three_eq_one_of_mem_scalars hz⟩
  rwa [hcop, pow_one] at h

theorem mem_diagPlane_of_proj_mem [NeZero p] [Fact p.Prime] (hp3 : p ≠ 3) {ζ : F}
    (hζ : ζ ^ p = 1) {X : SpecialLinearGroup (Fin 3) F} (hXp : X ^ p = 1)
    (hX : proj 3 F X ∈ (diagPlane p ζ hζ).map (proj 3 F)) : X ∈ diagPlane p ζ hζ := by
  obtain ⟨d, hd, hdX⟩ := hX
  have hz : d⁻¹ * X ∈ scalars 3 F := by
    rw [← proj_eq_one_iff, map_mul, map_inv, hdX, inv_mul_cancel]
  have hcomm : Commute d (d⁻¹ * X) :=
    (Subgroup.mem_center_iff.1 (scalars_le_center 3 F hz) d)
  have hzp : (d⁻¹ * X) ^ p = 1 := by
    have h := hcomm.mul_pow p
    rw [mul_inv_cancel_left, hXp, pow_eq_one_of_mem_diagPlane hd, one_mul] at h
    exact h.symm
  have h1 := eq_one_of_mem_scalars_of_pow_prime hp3 hz hzp
  rw [inv_mul_eq_one] at h1
  rw [← h1]
  exact hd

theorem exists_lift_of_isPGroup [Finite F] [hp : Fact p.Prime] (hp3 : p ≠ 3)
    (P : Subgroup (projectiveSL 3 F)) (hP : IsPGroup p P) :
    ∃ P₀ : Subgroup (SpecialLinearGroup (Fin 3) F), P₀.map (proj 3 F) = P ∧
      ∀ a ∈ P₀, ∀ b ∈ P₀, proj 3 F a = proj 3 F b → a = b := by
  classical
  have : Fintype F := Fintype.ofFinite F
  set G := P.comap (proj 3 F) with hG
  set N := (scalars 3 F).subgroupOf G with hN
  have : N.Normal := Subgroup.Normal.subgroupOf inferInstance G
  let f : G →* P := ((proj 3 F).comp G.subtype).codRestrict P fun g => g.2
  have hf : Function.Surjective f := by
    rintro ⟨x, hx⟩
    obtain ⟨g, rfl⟩ := proj_surjective 3 F x
    exact ⟨⟨g, hx⟩, rfl⟩
  have hker : f.ker = N := by
    ext g
    rw [MonoidHom.mem_ker, hN, Subgroup.mem_subgroupOf, ← proj_eq_one_iff]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  have hidx : N.index = Nat.card P := by
    rw [Subgroup.index_eq_card, ← hker]
    exact Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv
  have hcop : Nat.Coprime (Nat.card N) N.index := by
    rw [hidx]
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hP
    rw [hn]
    refine Nat.Coprime.pow_right n (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hp.out).2
      fun hdvd => ?_))
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := N) p hdvd
    have hz1 : z = 1 := by
      have h1 : ((z : G) : SpecialLinearGroup (Fin 3) F) ∈ scalars 3 F := z.2
      have h2 : ((z : G) : SpecialLinearGroup (Fin 3) F) ^ p = 1 := by
        have h3 := pow_orderOf_eq_one z
        rw [hz] at h3
        exact congrArg (fun w : N => ((w : G) : SpecialLinearGroup (Fin 3) F)) h3
      exact Subtype.ext (Subtype.ext (eq_one_of_mem_scalars_of_pow_prime hp3 h1 h2))
    rw [hz1, orderOf_one] at hz
    exact hp.out.one_lt.ne hz
  obtain ⟨H, hH⟩ := Subgroup.exists_right_complement'_of_coprime hcop
  refine ⟨H.map G.subtype, le_antisymm ?_ fun x hx => ?_, ?_⟩
  · rintro _ ⟨_, ⟨h, -, rfl⟩, rfl⟩
    exact h.2
  · obtain ⟨g, rfl⟩ := proj_surjective 3 F x
    obtain ⟨⟨n, h⟩, hnh⟩ := (Subgroup.isComplement'_def.1 hH).2 ⟨g, hx⟩
    refine ⟨G.subtype h.1, ⟨h.1, h.2, rfl⟩, ?_⟩
    have h1 : ((n.1 : G) : SpecialLinearGroup (Fin 3) F) *
        ((h.1 : G) : SpecialLinearGroup (Fin 3) F) = g := congrArg Subtype.val hnh
    have hn : ((n.1 : G) : SpecialLinearGroup (Fin 3) F) ∈ scalars 3 F := n.2
    rw [← h1, map_mul, proj_eq_one_iff.2 hn, one_mul]
    rfl
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hab
    have h1 : a⁻¹ * b ∈ N := by
      rw [hN, Subgroup.mem_subgroupOf, ← proj_eq_one_iff, Subgroup.coe_mul, Subgroup.coe_inv,
        map_mul, map_inv]
      change (proj 3 F (G.subtype a))⁻¹ * proj 3 F (G.subtype b) = 1
      rw [hab, inv_mul_cancel]
    have h2 : a⁻¹ * b ∈ H := H.mul_mem (H.inv_mem ha) hb
    have h3 := Subgroup.disjoint_def.1 hH.disjoint h1 h2
    exact congrArg Subtype.val (inv_mul_eq_one.1 h3)

theorem exists_central_pair {S : Type*} [Group S] [Finite S] [hp : Fact p.Prime]
    (P : Subgroup S) (hP : IsPGroup p P) (hPc : ¬ IsCyclic P) :
    ∃ z ∈ P, ∃ x ∈ P, z ≠ 1 ∧ (∀ y ∈ P, y * z = z * y) ∧ x ∉ Subgroup.zpowers z ∧
      ∀ y ∈ P, y * x * y⁻¹ * x⁻¹ ∈ Subgroup.zpowers z := by
  classical
  have : Nontrivial P := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact hPc isCyclic_of_subsingleton
  have := hP.center_nontrivial
  obtain ⟨z', hz'1⟩ := exists_ne (1 : Subgroup.center P)
  set Z1 := Subgroup.zpowers (z' : P) with hZ1
  have hZ1n : Z1.Normal := ⟨fun a ha g => by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    have hc : g * (z' : P) ^ k * g⁻¹ = (z' : P) ^ k := by
      rw [Subgroup.mem_center_iff.1 (Subgroup.zpow_mem _ z'.2 k) g, mul_inv_cancel_right]
    rw [hc]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) k⟩
  have hQnt : Nontrivial (P ⧸ Z1) := by
    rw [QuotientGroup.nontrivial_iff]
    intro htop
    apply hPc
    refine ⟨⟨(z' : P), fun y => ?_⟩⟩
    have hy : y ∈ Z1 := htop ▸ Subgroup.mem_top y
    exact Subgroup.mem_zpowers_iff.1 hy
  have hQp : IsPGroup p (P ⧸ Z1) := hP.to_quotient Z1
  have := hQp.center_nontrivial
  obtain ⟨xq, hxq1⟩ := exists_ne (1 : Subgroup.center (P ⧸ Z1))
  obtain ⟨x', hx'⟩ := QuotientGroup.mk_surjective (xq : P ⧸ Z1)
  refine ⟨((z' : P) : S), (z' : P).2, (x' : S), x'.2, fun h => hz'1 (Subtype.ext (Subtype.ext h)),
    fun y hy => ?_, fun h => ?_, fun y hy => ?_⟩
  · exact congrArg Subtype.val (Subgroup.mem_center_iff.1 z'.2 ⟨y, hy⟩)
  · obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 h
    have h1 : (z' : P) ^ k = x' := Subtype.ext (by rw [Subgroup.coe_zpow, hk])
    have h2 : (x' : P ⧸ Z1) = 1 := (QuotientGroup.eq_one_iff x').2 (h1 ▸ Subgroup.zpow_mem _
      (Subgroup.mem_zpowers _) k)
    exact hxq1 (Subtype.ext (hx'.symm.trans h2))
  · have h1 : ((⟨y, hy⟩ * x' * (⟨y, hy⟩ : P)⁻¹ * x'⁻¹ : P) : P ⧸ Z1) = 1 := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
        QuotientGroup.mk_inv, hx', Subgroup.mem_center_iff.1 xq.2]
      group
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 ((QuotientGroup.eq_one_iff _).1 h1)
    exact Subgroup.mem_zpowers_iff.2 ⟨k, by
      have := congrArg Subtype.val hk
      rw [Subgroup.coe_zpow] at this
      exact this⟩

theorem dualAut_planeElem [NeZero p] (ζ : F) (hζ : ζ ^ p = 1) :
    ∃ m : (ZMod p)ˣ, ∀ v : sumZeroPlane p,
      dualAut 3 F (proj 3 F (planeElem ζ hζ v)) = proj 3 F (planeElem ζ hζ ((m : ZMod p) • v)) := by
  refine ⟨-1, fun v => ?_⟩
  have hv : ((((-1 : (ZMod p)ˣ) : ZMod p) • v : sumZeroPlane p)) = -v :=
    Subtype.ext (funext fun i => by simp)
  rw [dualAut_proj, hv, ← planeElem_neg]
  congr 1
  apply Subtype.ext
  rw [SpecialLinearGroup.coe_transpose, coe_planeElem, diagPow, diagonal_transpose]

theorem fieldAut_planeElem [NeZero p] [hp : Fact p.Prime] {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    (σ : F ≃+* F) : ∃ s : (ZMod p)ˣ, ∀ v : sumZeroPlane p,
      fieldAut 3 F σ (proj 3 F (planeElem ζ hζ.pow_eq_one v)) =
        proj 3 F (planeElem ζ hζ.pow_eq_one ((s : ZMod p) • v)) := by
  have hσp : (σ ζ) ^ p = 1 := by rw [← map_pow, hζ.pow_eq_one, map_one]
  obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one hσp
  have hi0 : (i : ZMod p) ≠ 0 := by
    intro h
    have h1 : σ ζ = 1 := by
      rw [← hi, ← pow_val_natCast hζ.pow_eq_one, h, ZMod.val_zero, pow_zero]
    have h2 : ζ = 1 := σ.injective (h1.trans (map_one σ).symm)
    exact hζ.ne_one hp.out.one_lt h2
  refine ⟨Units.mk0 _ hi0, fun v => ?_⟩
  rw [fieldAut_proj]
  congr 1
  apply Subtype.ext
  rw [SpecialLinearGroup.map_apply_coe, coe_planeElem, coe_planeElem, RingHom.mapMatrix_apply,
    diagPow, diagPow, diagonal_map (map_zero _)]
  congr 1
  funext m
  rw [Units.val_mk0, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, map_pow, ← hi,
    Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, pow_val_mul hζ.pow_eq_one,
    pow_val_natCast hζ.pow_eq_one]

theorem conjAut_planeElem_of_mem [NeZero p] [hp : Fact p.Prime] (hp5 : 5 ≤ p) {ζ : F}
    (hζ : IsPrimitiveRoot ζ p) (h : GL (Fin 3) F)
    (hh : ∀ v : sumZeroPlane p, conjAut 3 F h⁻¹ (proj 3 F (planeElem ζ hζ.pow_eq_one v)) ∈
      (diagPlane p ζ hζ.pow_eq_one).map (proj 3 F)) :
    ∃ w : Equiv.Perm (Fin 3), ∀ v : sumZeroPlane p,
      conjAut 3 F h (proj 3 F (planeElem ζ hζ.pow_eq_one v)) =
        proj 3 F (planeElem ζ hζ.pow_eq_one (permPlane w v)) := by
  classical
  have hp3 : p ≠ 3 := by omega
  have hX : CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 F h⁻¹
      (planeElem ζ hζ.pow_eq_one (regVec p)) ∈ diagPlane p ζ hζ.pow_eq_one := by
    refine mem_diagPlane_of_proj_mem hp3 hζ.pow_eq_one ?_ ?_
    · rw [← map_pow, pow_eq_one_of_mem_diagPlane (planeElem_mem _ _ _), map_one]
    · rw [← conjAut_proj]
      exact hh _
  obtain ⟨u, hu⟩ := mem_diagPlane.1 hX
  have hmat : ((h⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
      diagPow ζ (regVec p : Fin 3 → ZMod p) * (h : Matrix (Fin 3) (Fin 3) F) =
        diagonal fun i => ζ ^ ((u : Fin 3 → ZMod p) i).val := by
    have h1 := congrArg (fun A : SpecialLinearGroup (Fin 3) F => (A : Matrix (Fin 3) (Fin 3) F)) hu
    simp only [coe_planeElem, coe_slConjugation, inv_inv] at h1
    rw [← h1]
    rfl
  have hinv1 : ((h⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * (h : Matrix (Fin 3) (Fin 3) F) =
      1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hinv2 : (h : Matrix (Fin 3) (Fin 3) F) * ((h⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  obtain ⟨w, t, ht, hN⟩ := exists_perm_of_conj_diagonal (by omega) hζ hinv1 hinv2 _ hmat
  refine ⟨w.symm, fun v => ?_⟩
  rw [conjAut_proj]
  congr 1
  apply Subtype.ext
  rw [coe_slConjugation, coe_planeElem, coe_planeElem, diagPow, diagPow,
    conj_diagonal_of_monomial hinv1 w t ht hN]
  rfl

theorem standard_plane_automorphism [Finite F] [NeZero p] [hp : Fact p.Prime] (hp5 : 5 ≤ p)
    {ζ : F} (hζ : IsPrimitiveRoot ζ p) (α : MulAut (projectiveSL 3 F))
    (hα : ((diagPlane p ζ hζ.pow_eq_one).map (proj 3 F)).map α.toMonoidHom =
      (diagPlane p ζ hζ.pow_eq_one).map (proj 3 F)) :
    ∃ (c : (ZMod p)ˣ) (w : Equiv.Perm (Fin 3)), ∀ v : sumZeroPlane p,
      α (proj 3 F (planeElem ζ hζ.pow_eq_one v)) =
        proj 3 F (planeElem ζ hζ.pow_eq_one ((c : ZMod p) • permPlane w v)) := by
  classical
  obtain ⟨h, σ, ε, hε, hαeq⟩ := (automorphism_generation (K := F) (n := 3) le_rfl).2 α
  obtain ⟨s, hs⟩ := fieldAut_planeElem hζ σ
  obtain ⟨m, hm⟩ := dualAut_planeElem ζ hζ.pow_eq_one
  set β := fieldAut 3 F σ * dualAut 3 F ^ ε with hβ
  set c₀ : (ZMod p)ˣ := s * m ^ ε with hc₀
  have hβv : ∀ v : sumZeroPlane p, β (proj 3 F (planeElem ζ hζ.pow_eq_one v)) =
      proj 3 F (planeElem ζ hζ.pow_eq_one ((c₀ : ZMod p) • v)) := by
    intro v
    rw [hβ, MulAut.mul_apply]
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hε with rfl | rfl
    · rw [pow_zero, MulAut.one_apply, hs, hc₀, pow_zero, mul_one]
    · rw [pow_one, hm, hs, smul_smul, hc₀, pow_one, Units.val_mul]
  have hαh : conjAut 3 F h = α * β⁻¹ := by
    rw [hαeq, hβ, mul_assoc (conjAut 3 F h), mul_inv_cancel_right]
  have hmemD : ∀ y ∈ (diagPlane p ζ hζ.pow_eq_one).map (proj 3 F),
      α⁻¹ y ∈ (diagPlane p ζ hζ.pow_eq_one).map (proj 3 F) := by
    intro y hy
    rw [← hα] at hy
    obtain ⟨y', hy', rfl⟩ := hy
    change α⁻¹ (α y') ∈ _
    rwa [MulAut.inv_apply_self]
  have hh : ∀ v : sumZeroPlane p, conjAut 3 F h⁻¹ (proj 3 F (planeElem ζ hζ.pow_eq_one v)) ∈
      (diagPlane p ζ hζ.pow_eq_one).map (proj 3 F) := by
    intro v
    rw [map_inv, hαh, _root_.mul_inv_rev, inv_inv, MulAut.mul_apply]
    obtain ⟨d, hd, hdv⟩ := hmemD _ (Subgroup.mem_map_of_mem _ (planeElem_mem _ _ v))
    obtain ⟨u, rfl⟩ := mem_diagPlane.1 hd
    rw [← hdv]
    change β (proj 3 F (planeElem ζ hζ.pow_eq_one u)) ∈ _
    rw [hβv]
    exact Subgroup.mem_map_of_mem _ (planeElem_mem _ _ _)
  obtain ⟨w, hw⟩ := conjAut_planeElem_of_mem hp5 hζ h hh
  refine ⟨c₀, w, fun v => ?_⟩
  rw [hαeq, mul_assoc, ← hβ, MulAut.mul_apply, hβv, hw, LinearMap.map_smul]

theorem perm_eq_of_smul_permPlane_eq [NeZero p] [Fact (1 < p)] {c c' : (ZMod p)ˣ}
    {w w' : Equiv.Perm (Fin 3)}
    (h : ∀ v : sumZeroPlane p, (c : ZMod p) • permPlane w v = (c' : ZMod p) • permPlane w' v) :
    w = w' := by
  refine Equiv.ext fun k => ?_
  by_contra hne
  obtain ⟨j, hj1, hj2⟩ : ∃ j : Fin 3, j ≠ w k ∧ j ≠ w' k := by
    revert hne
    generalize w k = a
    generalize w' k = b
    revert a b
    decide
  set u : Fin 3 → ZMod p := Pi.single (w k) 1 - Pi.single j 1 with hu
  have huV : u ∈ sumZeroPlane p := by
    rw [mem_sumZeroPlane, ← Fin.sum_univ_three, hu]
    simp [Finset.sum_sub_distrib]
  have h1 := congrFun (congrArg Subtype.val (h ⟨u, huV⟩)) k
  have hz1 : (Pi.single j 1 : Fin 3 → ZMod p) (w k) = 0 := Pi.single_eq_of_ne' hj1 _
  have hz2 : (Pi.single (w k) 1 : Fin 3 → ZMod p) (w' k) = 0 := Pi.single_eq_of_ne' hne _
  have hz3 : (Pi.single j 1 : Fin 3 → ZMod p) (w' k) = 0 := Pi.single_eq_of_ne' hj2 _
  change (c : ZMod p) * ((Pi.single (w k) 1 : Fin 3 → ZMod p) (w k) -
      (Pi.single j 1 : Fin 3 → ZMod p) (w k)) =
    (c' : ZMod p) * ((Pi.single (w k) 1 : Fin 3 → ZMod p) (w' k) -
      (Pi.single j 1 : Fin 3 → ZMod p) (w' k)) at h1
  rw [Pi.single_eq_same, hz1, hz2, hz3, sub_zero, mul_one, sub_zero, mul_zero] at h1
  exact c.ne_zero h1

theorem regVec_ne_zero [Fact (1 < p)] : regVec p ≠ 0 := by
  intro h
  have h1 := congrFun (congrArg Subtype.val h) 0
  exact one_ne_zero h1

theorem exists_permPlane_neg [NeZero p] [Fact (1 < p)] (τ : Equiv.Perm (Fin 3))
    (hτ2 : τ ^ 2 = 1) (hτ1 : τ ≠ 1) :
    ∃ u : sumZeroPlane p, u ≠ 0 ∧ ∃ m : ZMod p, permPlane τ u = m • u := by
  obtain ⟨i, hi⟩ : ∃ i, τ i ≠ i := by
    by_contra h
    push Not at h
    exact hτ1 (Equiv.ext h)
  have hinv : ∀ k, τ (τ k) = k := fun k => by
    have h := congrArg (fun σ : Equiv.Perm (Fin 3) => σ k) hτ2
    simpa [sq] using h
  set u : Fin 3 → ZMod p := Pi.single i 1 - Pi.single (τ i) 1 with hu
  have huV : u ∈ sumZeroPlane p := by
    rw [mem_sumZeroPlane, ← Fin.sum_univ_three, hu]
    simp [Finset.sum_sub_distrib]
  refine ⟨⟨u, huV⟩, fun h => ?_, -1, Subtype.ext (funext fun k => ?_)⟩
  · have h1 := congrFun (congrArg Subtype.val h) i
    simp only [hu, Pi.sub_apply, Pi.single_eq_same, Pi.single_eq_of_ne hi.symm, sub_zero] at h1
    exact one_ne_zero h1
  · change u (τ k) = (-1 : ZMod p) * u k
    have e1 : (τ k = i) ↔ (k = τ i) := ⟨fun h => by rw [← h, hinv], fun h => by rw [h, hinv]⟩
    have e2 : (τ k = τ i) ↔ (k = i) := τ.injective.eq_iff
    simp only [hu, Pi.sub_apply, Pi.single_apply, e1, e2]
    split_ifs <;> ring

theorem perm_three_sq {σ τ : Equiv.Perm (Fin 3)} (hσ : σ ^ 2 = 1) (hτ : τ ^ 2 = 1) (hσ1 : σ ≠ 1)
    (hτ1 : τ ≠ 1) (hστ : σ ≠ τ) : (σ * τ) ^ 2 ≠ 1 := by
  revert σ τ
  decide

theorem noncyclic_exponent_prime_projective_linear_three_subgroups_have_reducible_two_normalizers
    [Finite F] [NeZero p] [hp : Fact p.Prime] (hp5 : 5 ≤ p) (hpF : ringChar F ≠ p)
    (P : Subgroup (projectiveSL 3 F)) (hPc : ¬ IsCyclic P) (hPexp : ∀ x ∈ P, x ^ p = 1) :
    p ∣ Nat.card F - 1 ∧ IsElementaryAbelian p P ∧ Nat.card P = p ^ 2 ∧
    ∃ (ζ : F) (hζ : IsPrimitiveRoot ζ p) (g : GL (Fin 3) F),
      P.map (conjAut 3 F g).toMonoidHom = (diagPlane p ζ hζ.pow_eq_one).map (proj 3 F) ∧
      Function.Injective ((proj 3 F).comp (diagPlane p ζ hζ.pow_eq_one).subtype) ∧
      (∀ α : MulAut (projectiveSL 3 F), P.map α.toMonoidHom = P →
        ∃ (c : (ZMod p)ˣ) (w : Equiv.Perm (Fin 3)), ∀ v : sumZeroPlane p,
          α (conjAut 3 F g⁻¹ (proj 3 F (planeElem ζ hζ.pow_eq_one v))) =
            conjAut 3 F g⁻¹ (proj 3 F (planeElem ζ hζ.pow_eq_one ((c : ZMod p) • permPlane w v)))) ∧
      ∀ B : Subgroup (MulAut (projectiveSL 3 F)), IsPGroup 2 B →
        (∀ b ∈ B, P.map (b : MulAut (projectiveSL 3 F)).toMonoidHom = P) →
        ∃ P₁ : Subgroup (projectiveSL 3 F), P₁ < P ∧ Nat.card P₁ = p ∧
          ∀ b ∈ B, P₁.map (b : MulAut (projectiveSL 3 F)).toMonoidHom = P₁ := by
  classical
  have : Fintype F := Fintype.ofFinite F
  have hp3 : p ≠ 3 := by omega
  have hpF' : (p : F) ≠ 0 := by
    intro h
    have hd := (ringChar.spec F p).1 h
    rcases (Nat.Prime.eq_one_or_self_of_dvd hp.out _ hd) with h1 | h1
    · have h2 := (ringChar.spec F 1).2 (by rw [h1])
      rw [Nat.cast_one] at h2
      exact one_ne_zero h2
    · exact hpF h1
  have hPp : IsPGroup p P := fun x => ⟨1, by rw [pow_one]; exact Subtype.ext (hPexp x x.2)⟩
  obtain ⟨P₀, hP₀P, hP₀inj⟩ := exists_lift_of_isPGroup hp3 P hPp
  have hmemP : ∀ N ∈ P₀, proj 3 F N ∈ P := fun N hN => hP₀P ▸ Subgroup.mem_map_of_mem _ hN
  obtain ⟨z, hzP, x, hxP, hz1, hzc, hxz, hxc⟩ := exists_central_pair P hPp hPc
  obtain ⟨a, haP₀, rfl⟩ : ∃ a ∈ P₀, proj 3 F a = z := by
    rw [← hP₀P] at hzP
    obtain ⟨a, ha, rfl⟩ := hzP
    exact ⟨a, ha, rfl⟩
  obtain ⟨b, hbP₀, rfl⟩ : ∃ b ∈ P₀, proj 3 F b = x := by
    rw [← hP₀P] at hxP
    obtain ⟨b, hb, rfl⟩ := hxP
    exact ⟨b, hb, rfl⟩
  have hP₀p : ∀ N ∈ P₀, N ^ p = 1 := fun N hN => hP₀inj _ (P₀.pow_mem hN p) _ P₀.one_mem (by
    rw [map_pow, map_one]
    exact hPexp _ (hmemP N hN))
  have hap : a ^ p = 1 := hP₀p a haP₀
  have hbp : b ^ p = 1 := hP₀p b hbP₀
  have hab : a * b = b * a := hP₀inj _ (P₀.mul_mem haP₀ hbP₀) _ (P₀.mul_mem hbP₀ haP₀) (by
    rw [map_mul, map_mul]
    exact (hzc _ hxP).symm)
  have hNa : ∀ N ∈ P₀, N * a = a * N := fun N hN =>
    hP₀inj _ (P₀.mul_mem hN haP₀) _ (P₀.mul_mem haP₀ hN) (by
      rw [map_mul, map_mul]
      exact hzc _ (hmemP N hN))
  have hNb : ∀ N ∈ P₀, ∃ k : ℤ, N * b * N⁻¹ * b⁻¹ = a ^ k := fun N hN => by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hxc _ (hmemP N hN))
    refine ⟨k, hP₀inj _ ?_ _ (P₀.zpow_mem haP₀ k) ?_⟩
    · exact P₀.mul_mem (P₀.mul_mem (P₀.mul_mem hN hbP₀) (P₀.inv_mem hN)) (P₀.inv_mem hbP₀)
    · rw [map_zpow, hk]
      simp only [map_mul, map_inv]
  let φ : Multiplicative (ZMod p × ZMod p) →* SpecialLinearGroup (Fin 3) F :=
    { toFun := fun y => a ^ (Multiplicative.toAdd y).1.val * b ^ (Multiplicative.toAdd y).2.val
      map_one' := by
        change a ^ (0 : ZMod p).val * b ^ (0 : ZMod p).val = 1
        rw [ZMod.val_zero, pow_zero, pow_zero, mul_one]
      map_mul' := fun y y' => by
        change a ^ ((Multiplicative.toAdd y).1 + (Multiplicative.toAdd y').1).val *
          b ^ ((Multiplicative.toAdd y).2 + (Multiplicative.toAdd y').2).val = _
        rw [pow_val_add hap, pow_val_add hbp]
        have hc : Commute (b ^ (Multiplicative.toAdd y).2.val)
            (a ^ (Multiplicative.toAdd y').1.val) := Commute.pow_pow hab.symm _ _
        calc a ^ (Multiplicative.toAdd y).1.val * a ^ (Multiplicative.toAdd y').1.val *
              (b ^ (Multiplicative.toAdd y).2.val * b ^ (Multiplicative.toAdd y').2.val)
            = a ^ (Multiplicative.toAdd y).1.val * (a ^ (Multiplicative.toAdd y').1.val *
              b ^ (Multiplicative.toAdd y).2.val) * b ^ (Multiplicative.toAdd y').2.val := by
              simp only [mul_assoc]
          _ = a ^ (Multiplicative.toAdd y).1.val * (b ^ (Multiplicative.toAdd y).2.val *
              a ^ (Multiplicative.toAdd y').1.val) * b ^ (Multiplicative.toAdd y').2.val := by
              rw [← hc.eq]
          _ = _ := by simp only [mul_assoc] }
  have hφy : ∀ y, φ y = a ^ (Multiplicative.toAdd y).1.val * b ^ (Multiplicative.toAdd y).2.val :=
    fun _ => rfl
  have hφa : φ (Multiplicative.ofAdd (1, 0)) = a := by
    change a ^ (1 : ZMod p).val * b ^ (0 : ZMod p).val = a
    rw [ZMod.val_one, ZMod.val_zero, pow_one, pow_zero, mul_one]
  have hφb : φ (Multiplicative.ofAdd (0, 1)) = b := by
    change a ^ (0 : ZMod p).val * b ^ (1 : ZMod p).val = b
    rw [ZMod.val_one, ZMod.val_zero, pow_one, pow_zero, one_mul]
  have hzord : orderOf (proj 3 F a) = p := orderOf_eq_prime (hPexp _ hzP) hz1
  have hφinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro y hy
    have h1 : proj 3 F a ^ (Multiplicative.toAdd y).1.val *
        proj 3 F b ^ (Multiplicative.toAdd y).2.val = 1 := by
      rw [← map_pow, ← map_pow, ← map_mul, ← hφy, hy, map_one]
    have hl : (Multiplicative.toAdd y).2 = 0 := by
      by_contra hl0
      apply hxz
      have h2 : proj 3 F b ^ (Multiplicative.toAdd y).2.val ∈ Subgroup.zpowers (proj 3 F a) := by
        rw [eq_inv_of_mul_eq_one_right h1]
        exact Subgroup.inv_mem _ (Subgroup.npow_mem_zpowers _ _)
      have h3 : proj 3 F b = (proj 3 F b ^ (Multiplicative.toAdd y).2.val) ^
          ((Multiplicative.toAdd y).2⁻¹).val := by
        rw [← pow_val_mul (hPexp _ hxP), mul_inv_cancel₀ hl0, ZMod.val_one, pow_one]
      rw [h3]
      exact Subgroup.pow_mem _ h2 _
    have hj : (Multiplicative.toAdd y).1 = 0 := by
      rw [hl, ZMod.val_zero, pow_zero, mul_one] at h1
      have h2 := orderOf_dvd_of_pow_eq_one h1
      rw [hzord] at h2
      rw [← ZMod.val_eq_zero]
      exact Nat.eq_zero_of_dvd_of_lt h2 (ZMod.val_lt _)
    apply Multiplicative.toAdd.injective
    rw [toAdd_one]
    exact Prod.ext hj hl
  have hdvd := dvd_card_sub_one_of_injective hpF' φ hφinj
  obtain ⟨ζu, hζu⟩ := exists_prime_orderOf_dvd_card (G := Fˣ) p (by
    rw [Fintype.card_units, ← Nat.card_eq_fintype_card]
    exact hdvd)
  have hζ : IsPrimitiveRoot (ζu : F) p :=
    IsPrimitiveRoot.coe_units_iff.2 (hζu ▸ IsPrimitiveRoot.orderOf ζu)
  set ζ : F := (ζu : F) with hζdef
  obtain ⟨M, M', hM'M, hMM', hD1, hD2⟩ := exists_conj_eq_diagPlane hζ hpF' φ hφinj
  set g : GL (Fin 3) F := ⟨M', M, hM'M, hMM'⟩ with hg
  have hgM : (g : Matrix (Fin 3) (Fin 3) F) = M' := rfl
  have hgM' : ((g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = M := rfl
  have hcancel : ∀ X : Matrix (Fin 3) (Fin 3) F, X = M * (M' * X * M) * M' := fun X => by
    simp only [← Matrix.mul_assoc, hMM', Matrix.one_mul]
    rw [Matrix.mul_assoc, hMM', Matrix.mul_one]
  have hrange_le : φ.range ≤ P₀ := by
    rintro _ ⟨y, rfl⟩
    exact P₀.mul_mem (P₀.pow_mem haP₀ _) (P₀.pow_mem hbP₀ _)
  have hnorm : ∀ N ∈ P₀, ∀ y, N⁻¹ * φ y * N ∈ φ.range := fun N hN y => by
    have hc : ∀ X, N⁻¹ * X * N = MulAut.conj N⁻¹ X := fun X => by
      rw [MulAut.conj_apply, inv_inv]
    have hNa' : N⁻¹ * a * N = a := by
      rw [mul_assoc, ← hNa N hN, ← mul_assoc, inv_mul_cancel, one_mul]
    obtain ⟨k, hk⟩ := hNb N⁻¹ (P₀.inv_mem hN)
    have hNb' : N⁻¹ * b * N = a ^ k * b := by
      calc N⁻¹ * b * N = N⁻¹ * b * N⁻¹⁻¹ * b⁻¹ * b := by group
        _ = a ^ k * b := by rw [hk]
    rw [hc, hφy, map_mul, map_pow, map_pow, ← hc, ← hc, hNa', hNb']
    refine φ.range.mul_mem (φ.range.pow_mem ⟨_, hφa⟩ _) (φ.range.pow_mem
      (φ.range.mul_mem (φ.range.zpow_mem ⟨_, hφa⟩ k) ⟨_, hφb⟩) _)
  have hP₀le : P₀ ≤ φ.range := by
    intro N hN
    set N₁ := M' * (N : Matrix (Fin 3) (Fin 3) F) * M with hN₁
    set N₂ := M' * ((N⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * M
      with hN₂
    have hNN : ((N⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
        (N : Matrix (Fin 3) (Fin 3) F) = 1 := congrArg Subtype.val (inv_mul_cancel N)
    have hNN' : (N : Matrix (Fin 3) (Fin 3) F) *
        ((N⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = 1 :=
      congrArg Subtype.val (mul_inv_cancel N)
    have h21 : N₂ * N₁ = 1 := by
      rw [hN₁, hN₂, conj_mul_conj hMM', hNN, Matrix.mul_one, hM'M]
    have h12 : N₁ * N₂ = 1 := by
      rw [hN₁, hN₂, conj_mul_conj hMM', hNN', Matrix.mul_one, hM'M]
    obtain ⟨y₀, hy₀⟩ := hD2 (regVec p)
    obtain ⟨y₁, hy₁⟩ := hnorm N hN (Multiplicative.ofAdd y₀)
    obtain ⟨v₁, hv₁⟩ := hD1 (Multiplicative.toAdd y₁)
    have hreg : N₂ * diagPow ζ (regVec p : Fin 3 → ZMod p) * N₁ =
        diagPow ζ (v₁ : Fin 3 → ZMod p) := by
      rw [← hy₀, ← hv₁, hN₁, hN₂, conj_mul_conj hMM', conj_mul_conj hMM']
      congr 2
      exact (congrArg (fun A : SpecialLinearGroup (Fin 3) F => (A : Matrix (Fin 3) (Fin 3) F))
        hy₁).symm
    obtain ⟨w, t, ht, hNe⟩ := exists_perm_of_conj_diagonal (by omega) hζ h21 h12
      (fun i => ζ ^ ((v₁ : Fin 3 → ZMod p) i).val) hreg
    have hNp : (N : Matrix (Fin 3) (Fin 3) F) ^ p = 1 :=
      (Matrix.SpecialLinearGroup.coe_pow N p).symm.trans (congrArg Subtype.val (hP₀p N hN))
    have hN₁p : N₁ ^ p = 1 := by
      rw [hN₁, conj_pow_eq hM'M hMM', hNp, Matrix.mul_one, hM'M]
    have hdiag := diagonal_of_monomial_of_pow_eq_one hp5 w t ht hNe hN₁p
    have htp : ∀ i, t i ^ p = 1 := fun i => by
      have h1 := congrFun (congrFun (hdiag ▸ hN₁p : diagonal t ^ p = 1) i) i
      rwa [diagonal_pow, diagonal_apply_eq, Pi.pow_apply, one_apply_eq] at h1
    have hdet : N₁.det = 1 := by rw [hN₁, det_conj hM'M]; exact N.2
    obtain ⟨v, hv⟩ := mem_diagPlane.1 (mem_diagPlane_of_diagonal hζ ⟨N₁, hdet⟩ t hdiag htp)
    obtain ⟨y, hy⟩ := hD2 v
    refine ⟨Multiplicative.ofAdd y, Subtype.ext ?_⟩
    have h1 : M' * pairMat φ y * M = N₁ := by
      rw [hy, ← coe_planeElem ζ hζ.pow_eq_one, hv]
    rw [hcancel (N : Matrix (Fin 3) (Fin 3) F), ← hN₁, ← h1, ← hcancel]
  have hP₀eq : P₀ = φ.range := le_antisymm hP₀le hrange_le
  have hcardP₀ : Nat.card P₀ = p ^ 2 := by
    rw [hP₀eq, ← Nat.card_congr (MonoidHom.ofInjective hφinj).toEquiv,
      Nat.card_congr Multiplicative.toAdd, Nat.card_prod, Nat.card_zmod, sq]
  have hcardP : Nat.card P = p ^ 2 := by
    rw [← hcardP₀, ← hP₀P]
    refine (Nat.card_congr (Equiv.ofBijective (fun N : P₀ =>
      (⟨proj 3 F N, Subgroup.mem_map_of_mem _ N.2⟩ : P₀.map (proj 3 F))) ⟨fun N N' h => ?_,
        fun ⟨_, N, hN, rfl⟩ => ⟨⟨N, hN⟩, rfl⟩⟩)).symm
    exact Subtype.ext (hP₀inj _ N.2 _ N'.2 (congrArg Subtype.val h))
  have hcomm : ∀ X ∈ P, ∀ Y ∈ P, X * Y = Y * X := by
    intro X hX Y hY
    rw [← hP₀P] at hX hY
    obtain ⟨N, hN, rfl⟩ := hX
    obtain ⟨N', hN', rfl⟩ := hY
    rw [hP₀eq] at hN hN'
    obtain ⟨y, rfl⟩ := hN
    obtain ⟨y', rfl⟩ := hN'
    rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, mul_comm y y']
  have hEA : IsElementaryAbelian p P :=
    { is_comm := ⟨fun X Y => Subtype.ext (hcomm X X.2 Y Y.2)⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun X =>
        Subtype.ext (by simpa using hPexp X X.2) }
  have hconjP : ∀ N ∈ P₀, ∃ v : sumZeroPlane p,
      conjAut 3 F g (proj 3 F N) = proj 3 F (planeElem ζ hζ.pow_eq_one v) := by
    intro N hN
    rw [hP₀eq] at hN
    obtain ⟨y, rfl⟩ := hN
    obtain ⟨v, hv⟩ := hD1 (Multiplicative.toAdd y)
    refine ⟨v, ?_⟩
    rw [conjAut_proj]
    congr 1
    apply Subtype.ext
    rw [coe_slConjugation, hgM, hgM', coe_planeElem, ← hv]
    rfl
  have hPD : P.map (conjAut 3 F g).toMonoidHom = (diagPlane p ζ hζ.pow_eq_one).map (proj 3 F) := by
    refine le_antisymm ?_ fun X hX => ?_
    · rintro _ ⟨X, hX, rfl⟩
      rw [← hP₀P] at hX
      obtain ⟨N, hN, rfl⟩ := hX
      obtain ⟨v, hv⟩ := hconjP N hN
      exact ⟨_, planeElem_mem _ _ v, hv.symm⟩
    · obtain ⟨d, hd, rfl⟩ := hX
      obtain ⟨v, rfl⟩ := mem_diagPlane.1 hd
      obtain ⟨y, hy⟩ := hD2 v
      refine ⟨proj 3 F (φ (Multiplicative.ofAdd y)), hmemP _ (hrange_le ⟨_, rfl⟩), ?_⟩
      change conjAut 3 F g (proj 3 F (φ (Multiplicative.ofAdd y))) = _
      rw [conjAut_proj]
      congr 1
      apply Subtype.ext
      rw [coe_slConjugation, hgM, hgM', coe_planeElem, ← hy]
  have hDinj : Function.Injective ((proj 3 F).comp (diagPlane p ζ hζ.pow_eq_one).subtype) := by
    intro d d' h
    have h1 : (d : SpecialLinearGroup (Fin 3) F)⁻¹ * d' ∈ scalars 3 F := by
      rw [← proj_eq_one_iff, map_mul, map_inv]
      change (proj 3 F d)⁻¹ * proj 3 F d' = 1
      rw [show proj 3 F d = proj 3 F d' from h, inv_mul_cancel]
    have h2 := eq_one_of_mem_scalars_of_pow_prime hp3 h1
      (pow_eq_one_of_mem_diagPlane ((diagPlane p ζ hζ.pow_eq_one).mul_mem
        ((diagPlane p ζ hζ.pow_eq_one).inv_mem d.2) d'.2))
    exact Subtype.ext (inv_mul_eq_one.1 h2)
  have hαpart : ∀ α : MulAut (projectiveSL 3 F), P.map α.toMonoidHom = P →
      ∃ (c : (ZMod p)ˣ) (w : Equiv.Perm (Fin 3)), ∀ v : sumZeroPlane p,
        α (conjAut 3 F g⁻¹ (proj 3 F (planeElem ζ hζ.pow_eq_one v))) =
          conjAut 3 F g⁻¹
            (proj 3 F (planeElem ζ hζ.pow_eq_one ((c : ZMod p) • permPlane w v))) := by
    intro α hα
    set α' := conjAut 3 F g * α * (conjAut 3 F g)⁻¹ with hα'
    have hα'D : ((diagPlane p ζ hζ.pow_eq_one).map (proj 3 F)).map α'.toMonoidHom =
        (diagPlane p ζ hζ.pow_eq_one).map (proj 3 F) := by
      rw [← hPD, Subgroup.map_map]
      have h1 : α'.toMonoidHom.comp (conjAut 3 F g).toMonoidHom =
          (conjAut 3 F g).toMonoidHom.comp α.toMonoidHom := by
        ext X
        change (conjAut 3 F g * α * (conjAut 3 F g)⁻¹) (conjAut 3 F g X) = conjAut 3 F g (α X)
        rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self]
      rw [h1, ← Subgroup.map_map, hα]
    obtain ⟨c, w, hcw⟩ := standard_plane_automorphism hp5 hζ α' hα'D
    refine ⟨c, w, fun v => ?_⟩
    rw [← hcw, map_inv, hα']
    change α ((conjAut 3 F g)⁻¹ _) = (conjAut 3 F g)⁻¹ ((conjAut 3 F g * α * (conjAut 3 F g)⁻¹) _)
    rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self]
  refine ⟨hdvd, hEA, hcardP, ζ, hζ, g, hPD, hDinj, hαpart, ?_⟩
  intro B hB2 hBP
  set ι : Multiplicative (sumZeroPlane p) →* projectiveSL 3 F :=
    ((conjAut 3 F g⁻¹).toMonoidHom.comp (proj 3 F)).comp (planeHom ζ hζ.pow_eq_one) with hι
  have hιv : ∀ v : sumZeroPlane p, ι (Multiplicative.ofAdd v) =
      conjAut 3 F g⁻¹ (proj 3 F (planeElem ζ hζ.pow_eq_one v)) := fun _ => rfl
  have hιinj : Function.Injective ι := by
    intro v v' h
    have h1 := (conjAut 3 F g⁻¹).injective h
    have h2 := hDinj (a₁ := ⟨_, planeElem_mem _ _ (Multiplicative.toAdd v)⟩)
      (a₂ := ⟨_, planeElem_mem _ _ (Multiplicative.toAdd v')⟩) h1
    exact congrArg Multiplicative.ofAdd
      (planeElem_injective hζ (congrArg Subtype.val h2))
  have hιP : ∀ v : sumZeroPlane p, ι (Multiplicative.ofAdd v) ∈ P := by
    intro v
    have h1 : proj 3 F (planeElem ζ hζ.pow_eq_one v) ∈ P.map (conjAut 3 F g).toMonoidHom := by
      rw [hPD]
      exact Subgroup.mem_map_of_mem _ (planeElem_mem _ _ v)
    obtain ⟨X, hX, hXv⟩ := h1
    rw [hιv, ← hXv, map_inv]
    change (conjAut 3 F g)⁻¹ (conjAut 3 F g X) ∈ P
    rwa [MulAut.inv_apply_self]
  have hact : ∀ b : B, ∃ (c : (ZMod p)ˣ) (w : Equiv.Perm (Fin 3)), ∀ v : sumZeroPlane p,
      (b : MulAut (projectiveSL 3 F)) (ι (Multiplicative.ofAdd v)) =
        ι (Multiplicative.ofAdd ((c : ZMod p) • permPlane w v)) := fun b =>
    hαpart b (hBP b b.2)
  choose cB wB hcw using hact
  have huniq : ∀ (c c' : (ZMod p)ˣ) (w w' : Equiv.Perm (Fin 3)), (∀ v : sumZeroPlane p,
      ι (Multiplicative.ofAdd ((c : ZMod p) • permPlane w v)) =
        ι (Multiplicative.ofAdd ((c' : ZMod p) • permPlane w' v))) → w = w' :=
    fun c c' w w' h => perm_eq_of_smul_permPlane_eq fun v =>
      congrArg Multiplicative.toAdd (hιinj (h v))
  have hcomp : ∀ (w₁ w₂ : Equiv.Perm (Fin 3)) (v : sumZeroPlane p),
      permPlane w₁ (permPlane w₂ v) = permPlane (w₂ * w₁) v := fun _ _ _ => rfl
  have hmulw : ∀ b₁ b₂ : B, wB (b₁ * b₂) = wB b₂ * wB b₁ := fun b₁ b₂ =>
    huniq (cB (b₁ * b₂)) (cB b₁ * cB b₂) _ _ fun v => by
      rw [← hcw]
      change (b₁ : MulAut (projectiveSL 3 F)) ((b₂ : MulAut (projectiveSL 3 F))
        (ι (Multiplicative.ofAdd v))) = _
      rw [hcw, hcw, LinearMap.map_smul, hcomp, smul_smul, Units.val_mul]
  have hpoww : ∀ (b : B) (n : ℕ), wB (b ^ n) = wB b ^ n := by
    intro b n
    induction n with
    | zero =>
      rw [pow_zero, pow_zero]
      exact huniq _ 1 _ _ fun v => by
        rw [← hcw, Units.val_one, one_smul]
        rfl
    | succ n ih => rw [pow_succ b n, hmulw, ih, pow_succ' (wB b) n]
  have hsq : ∀ b : B, wB b ^ 2 = 1 := by
    intro b
    obtain ⟨k, hk⟩ := hB2 b
    have h1 : wB b ^ (2 ^ k) = 1 := by
      rw [← hpoww, hk]
      exact huniq _ 1 _ _ fun v => by
        rw [← hcw, Units.val_one, one_smul]
        rfl
    have h2 : orderOf (wB b) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h1
    have h3 : orderOf (wB b) ∣ 6 := by
      have := orderOf_dvd_card (x := wB b)
      rwa [Fintype.card_perm, Fintype.card_fin] at this
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h2
    have hj1 : j ≤ 1 := by
      by_contra hj1
      have h4 : 4 ∣ 6 := by
        rw [hj] at h3
        exact (pow_dvd_pow 2 (by omega : 2 ≤ j)).trans h3
      norm_num at h4
    have h4 : orderOf (wB b) ∣ 2 := by
      rw [hj]
      exact pow_dvd_pow 2 hj1
    exact orderOf_dvd_iff_pow_eq_one.1 h4
  obtain ⟨u, hu0, hu⟩ : ∃ u : sumZeroPlane p, u ≠ 0 ∧ ∀ b : B, ∃ t : ZMod p,
      (cB b : ZMod p) • permPlane (wB b) u = t • u := by
    by_cases hall : ∀ b : B, wB b = 1
    · exact ⟨regVec p, regVec_ne_zero, fun b => ⟨cB b, by rw [hall b]; rfl⟩⟩
    · push Not at hall
      obtain ⟨b₀, hb₀⟩ := hall
      have h1τ : ∀ b : B, wB b = 1 ∨ wB b = wB b₀ := by
        intro b
        by_contra hc
        push Not at hc
        have h1 := hsq (b₀ * b)
        rw [hmulw] at h1
        exact perm_three_sq (hsq b) (hsq b₀) hc.1 hb₀ hc.2 h1
      obtain ⟨u, hu0, m, hτu⟩ := exists_permPlane_neg (p := p) (wB b₀) (hsq b₀) hb₀
      refine ⟨u, hu0, fun b => ?_⟩
      rcases h1τ b with h | h
      · exact ⟨cB b, by rw [h]; rfl⟩
      · exact ⟨(cB b : ZMod p) * m, by rw [h, hτu, smul_smul]⟩
  have hιu1 : ι (Multiplicative.ofAdd u) ≠ 1 := by
    intro h
    apply hu0
    have := hιinj (h.trans (map_one ι).symm)
    exact congrArg Multiplicative.toAdd this
  have hιup : ι (Multiplicative.ofAdd u) ^ p = 1 := by
    rw [← map_pow, ← ofAdd_nsmul, ← Nat.cast_smul_eq_nsmul (ZMod p), ZMod.natCast_self, zero_smul,
      ofAdd_zero, map_one]
  have hcardP₁ : Nat.card (Subgroup.zpowers (ι (Multiplicative.ofAdd u))) = p := by
    rw [Nat.card_zpowers, orderOf_eq_prime hιup hιu1]
  have hP₁P : Subgroup.zpowers (ι (Multiplicative.ofAdd u)) ≤ P :=
    Subgroup.zpowers_le.2 (hιP u)
  refine ⟨Subgroup.zpowers (ι (Multiplicative.ofAdd u)), lt_of_le_of_ne hP₁P fun h => ?_,
    hcardP₁, fun b hb => ?_⟩
  · have h1 : p = p ^ 2 := by
      have h2 := hcardP₁
      rw [h, hcardP] at h2
      exact h2.symm
    have h2 : p ^ 1 < p ^ 2 := Nat.pow_lt_pow_right hp.out.one_lt (by norm_num)
    rw [pow_one] at h2
    omega
  · refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rw [MonoidHom.map_zpowers]
      refine Subgroup.zpowers_le.2 ?_
      obtain ⟨t, ht⟩ := hu ⟨b, hb⟩
      change (b : MulAut (projectiveSL 3 F)) (ι (Multiplicative.ofAdd u)) ∈ _
      have h1 := hcw ⟨b, hb⟩ u
      change (b : MulAut (projectiveSL 3 F)) (ι (Multiplicative.ofAdd u)) = _ at h1
      rw [h1, ht, ← ZMod.natCast_zmod_val t, Nat.cast_smul_eq_nsmul, ofAdd_nsmul, map_pow]
      exact Subgroup.npow_mem_zpowers _ _
    · rw [Subgroup.card_map_of_injective (b : MulAut (projectiveSL 3 F)).injective]

end CFSG.Quasithin.SteinbergBQ
