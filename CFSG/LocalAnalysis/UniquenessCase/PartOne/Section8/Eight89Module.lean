module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight89Defs
import CFSG.HardMathSupport.Solomon.Coordinator.T112MCover

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.UC22.F08

private theorem k89mod_kerMul {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (f g : Module.End F V) :
    Module.finrank F (LinearMap.ker (f * g)) ≤
      Module.finrank F (LinearMap.ker f) + Module.finrank F (LinearMap.ker g) := by
  have h := LinearMap.lift_rank_comap_le (f := g) (LinearMap.ker f)
  simp only [Cardinal.lift_id] at h
  rw [← LinearMap.ker_comp, ← Module.End.mul_eq_comp] at h
  simp only [← Module.finrank_eq_rank] at h
  exact_mod_cast h

private theorem k89mod_step_weyl {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (x y z : Module.End F V) (hy : Function.Injective y)
    (hx : x ^ 3 = 1) (hz : z ^ 3 = 1) (hxz : x * z = z * x) (hyz : y * z = z * y)
    (hxy : x * y = z * y * x) (hfix : ∀ v : V, z v = v → v = 0) :
    3 ∣ Module.finrank F V := by
  have hmem : ∀ (c : Module.End F V) (v : V), v ∈ LinearMap.ker (x - c) ↔ x v = c v := by
    intro c v
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
  have hxzv : ∀ v : V, x (z v) = z (x v) := fun v => by
    rw [← Module.End.mul_apply, hxz, Module.End.mul_apply]
  have h3 : z * z * z = 1 := by
    rw [← pow_three']
    exact hz
  have hz3v : ∀ v : V, z (z (z v)) = v := fun v => by
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, h3, Module.End.one_apply]
  have hz2v : ∀ v : V, (z ^ 2) v = z (z v) := fun v => by
    rw [pow_two, Module.End.mul_apply]
  have hz2 : z ^ 2 + z + 1 = 0 := by
    have hz0 : (z - 1) * (z ^ 2 + z + 1) = 0 := by
      have e : (z - 1) * (z ^ 2 + z + 1) = z ^ 3 - 1 := by noncomm_ring
      rw [e, hz, sub_self]
    ext v
    have h := congrArg (fun φ : Module.End F V => φ v) hz0
    simp only [Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply,
      LinearMap.zero_apply] at h
    exact hfix _ (sub_eq_zero.mp h)
  have hxz2 : x * z ^ 2 = z ^ 2 * x := (Commute.pow_right (show Commute x z from hxz) 2).eq
  have hz3 : z * z ^ 2 = 1 := by
    rw [← pow_succ']
    exact hz
  have hzsum : z ^ 2 + z = -1 := by
    rw [← add_eq_zero_iff_eq_neg]
    exact hz2
  have hprod : (x - 1) * ((x - z) * (x - z ^ 2)) = 0 := by
    have e1 : (x - z) * (x - z ^ 2) = x * x - x * z ^ 2 - z * x + z * z ^ 2 := by noncomm_ring
    have e2 : (x - z) * (x - z ^ 2) = x * x + x + 1 := by
      rw [e1, hxz2, hz3]
      have e3 : x * x - z ^ 2 * x - z * x + 1 = x * x - (z ^ 2 + z) * x + 1 := by noncomm_ring
      rw [e3, hzsum]
      noncomm_ring
    rw [e2]
    have e4 : (x - 1) * (x * x + x + 1) = x ^ 3 - 1 := by noncomm_ring
    rw [e4, hx, sub_self]
  have hup1 := k89mod_kerMul (x - 1) ((x - z) * (x - z ^ 2))
  have hup2 := k89mod_kerMul (x - z) (x - z ^ 2)
  rw [hprod, LinearMap.ker_zero, finrank_top] at hup1
  have hd01 : LinearMap.ker (x - 1) ⊓ LinearMap.ker (x - z) = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    rw [Submodule.mem_inf, hmem 1, hmem z, Module.End.one_apply] at hv
    rw [Submodule.mem_bot]
    exact hfix v (hv.2.symm.trans hv.1)
  have hd012 : (LinearMap.ker (x - 1) ⊔ LinearMap.ker (x - z)) ⊓ LinearMap.ker (x - z ^ 2) = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    rw [Submodule.mem_inf, Submodule.mem_sup] at hv
    obtain ⟨⟨v0, hv0, v1, hv1, rfl⟩, hv2⟩ := hv
    rw [hmem 1, Module.End.one_apply] at hv0
    rw [hmem z] at hv1
    rw [hmem (z ^ 2), map_add, hz2v, map_add, map_add, hv0, hv1] at hv2
    have hu : v0 - z (z v0) = z (z v1) - z v1 := by
      rw [sub_eq_sub_iff_add_eq_add]
      exact hv2.trans (add_comm _ _)
    have hu0 : x (v0 - z (z v0)) = v0 - z (z v0) := by
      rw [map_sub, hxzv, hxzv, hv0]
    have hu1 : x (z (z v1) - z v1) = z (z (z v1) - z v1) := by
      rw [map_sub, map_sub, hxzv, hxzv, hv1]
    have h0 : v0 - z (z v0) ∈ LinearMap.ker (x - 1) ⊓ LinearMap.ker (x - z) := by
      refine ⟨(hmem 1 _).mpr (by rw [Module.End.one_apply]; exact hu0), ?_⟩
      rw [hu]
      exact (hmem z _).mpr hu1
    rw [hd01, Submodule.mem_bot] at h0
    have hv0z : z v0 = v0 := by
      have e := congrArg z (sub_eq_zero.mp h0)
      rw [e, hz3v]
    have h1' : z (z v1) - z v1 = 0 := by
      rw [← hu]
      exact h0
    have hv1z : z v1 = v1 := by
      have e := sub_eq_zero.mp h1'
      have e2 := congrArg z e
      rw [hz3v, e] at e2
      exact e2.symm
    rw [Submodule.mem_bot, hfix v0 hv0z, hfix v1 hv1z, add_zero]
  have hsum01 := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.ker (x - 1))
    (LinearMap.ker (x - z))
  rw [hd01, finrank_bot, add_zero] at hsum01
  have hsum012 := Submodule.finrank_sup_add_finrank_inf_eq
    (LinearMap.ker (x - 1) ⊔ LinearMap.ker (x - z)) (LinearMap.ker (x - z ^ 2))
  rw [hd012, finrank_bot, add_zero, hsum01] at hsum012
  have hlow := Submodule.finrank_le
    (LinearMap.ker (x - 1) ⊔ LinearMap.ker (x - z) ⊔ LinearMap.ker (x - z ^ 2))
  have hdim : ∀ c : Module.End F V, y * c = c * y →
      Module.finrank F (LinearMap.ker (x - c)) ≤
        Module.finrank F (LinearMap.ker (x - z * c)) := by
    intro c hc
    have hmaps : ∀ v ∈ LinearMap.ker (x - c), y v ∈ LinearMap.ker (x - z * c) := by
      intro v hv
      rw [hmem] at hv ⊢
      calc x (y v) = (x * y) v := rfl
        _ = (z * y * x) v := by rw [hxy]
        _ = z (y (x v)) := rfl
        _ = z (y (c v)) := by rw [hv]
        _ = z ((y * c) v) := rfl
        _ = z ((c * y) v) := by rw [hc]
        _ = (z * c) (y v) := rfl
    let r : LinearMap.ker (x - c) →ₗ[F] LinearMap.ker (x - z * c) := y.restrict hmaps
    apply LinearMap.finrank_le_finrank_of_injective (f := r)
    intro u w huw
    apply Subtype.ext
    apply hy
    have e := congrArg Subtype.val huw
    simpa [r] using e
  have hd1 := hdim 1 (by rw [mul_one, one_mul])
  have hd2 := hdim z hyz
  have hd3 := hdim (z ^ 2) (Commute.pow_right (show Commute y z from hyz) 2).eq
  rw [mul_one] at hd1
  rw [← pow_two] at hd2
  rw [hz3] at hd3
  omega

private theorem k89mod_step_sylowThree {K : Type} [Group K] [Finite K] (T : Subgroup K)
    [T.Normal] (hT : IsPGroup 2 T) (hbar : IsA6Z3 (K ⧸ T)) (z : K) (hz : orderOf z = 3)
    (hzc : QuotientGroup.mk' T z ∈ Subgroup.center (K ⧸ T)) :
    ∃ Q : Subgroup K, z ∈ Q ∧ Nat.card Q = 27 ∧ (∃ a ∈ Q, ∃ b ∈ Q, a * b ≠ b * a) ∧
      (∀ a ∈ Q, a ^ 3 = 1) ∧ ∀ a ∈ Q, a * z = z * a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hzp : IsPGroup 3 (Subgroup.zpowers z) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz, pow_one])
  obtain ⟨R, hR⟩ := hzp.exists_le_sylow
  have hzR : z ∈ (R : Subgroup K) := hR (Subgroup.mem_zpowers z)
  have hdisj : Disjoint (R : Subgroup K) T :=
    IsPGroup.disjoint_of_ne 3 2 (by norm_num) _ _ R.isPGroup' hT
  have hRT : ∀ a ∈ (R : Subgroup K), a ∈ T → a = 1 := fun a ha haT =>
    Subgroup.disjoint_def.mp hdisj ha haT
  have hf : Function.Surjective (QuotientGroup.mk' T) := QuotientGroup.mk'_surjective T
  have hφ : Function.Injective ((QuotientGroup.mk' T).comp (R : Subgroup K).subtype) := by
    refine (injective_iff_map_eq_one _).mpr fun a ha => ?_
    rw [MonoidHom.comp_apply, Subgroup.coe_subtype, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at ha
    exact Subtype.ext (hRT a a.2 ha)
  obtain ⟨h27, ⟨r, hr, s, hs, hrs⟩, hexp⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.t112m_sylow_hatSix
      ⟨hbar.1.1.commutator_eq_top, hbar.2.1, hbar.2.2⟩ (R.mapSurjective hf)
  have hrange : ((QuotientGroup.mk' T).comp (R : Subgroup K).subtype).range =
      (R : Subgroup K).map (QuotientGroup.mk' T) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hcardR : Nat.card (R : Subgroup K) = 27 := by
    rw [← h27, Sylow.coe_mapSurjective, ← hrange]
    exact Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv
  rw [Sylow.coe_mapSurjective, Subgroup.mem_map] at hr hs
  obtain ⟨a, ha, rfl⟩ := hr
  obtain ⟨b, hb, rfl⟩ := hs
  refine ⟨R, hzR, hcardR, ⟨a, ha, b, hb, fun h => hrs (by rw [← map_mul, h, map_mul])⟩, ?_, ?_⟩
  · intro x hx
    have h1 : QuotientGroup.mk' T (x ^ 3) = 1 := by
      rw [map_pow]
      exact hexp _ (Subgroup.mem_map_of_mem _ hx)
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact hRT _ (Subgroup.pow_mem _ hx 3) h1
  · intro x hx
    have h1 : QuotientGroup.mk' T (x * z * x⁻¹ * z⁻¹) = 1 := by
      have hc := Subgroup.mem_center_iff.mp hzc (QuotientGroup.mk' T x)
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hc]
      group
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    have hmem : x * z * x⁻¹ * z⁻¹ ∈ (R : Subgroup K) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hx hzR)
        (Subgroup.inv_mem _ hx)) (Subgroup.inv_mem _ hzR)
    have h2 := hRT _ hmem h1
    calc x * z = x * z * x⁻¹ * z⁻¹ * (z * x) := by group
      _ = z * x := by rw [h2, one_mul]

private theorem k89mod_step_cubeCommutator {Q : Type*} [Group Q] [Finite Q]
    (hcard : Nat.card Q = 27) (hnab : ∃ a b : Q, a * b ≠ b * a) (z : Q)
    (hzc : ∀ a : Q, a * z = z * a) : ∃ x y : Q, x * y * x⁻¹ * y⁻¹ = z := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hcomm, hZ3, -⟩ :=
    CFSG.SectionRank.Ccomm.nonabelian_prime_cube_central_structure (p := 3)
      (by rw [hcard]; norm_num) hnab
  obtain ⟨a, b, hab⟩ := hnab
  obtain ⟨c, hcdef⟩ : ∃ c : Q, c = a * b * a⁻¹ * b⁻¹ := ⟨_, rfl⟩
  have hcZ : c ∈ Subgroup.center Q := by
    rw [← hcomm, hcdef, ← commutatorElement_def, commutator_def]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
  have hc1 : (⟨c, hcZ⟩ : Subgroup.center Q) ≠ 1 := by
    intro h
    have h' : c = 1 := congrArg Subtype.val h
    rw [hcdef] at h'
    apply hab
    calc a * b = a * b * a⁻¹ * b⁻¹ * (b * a) := by group
      _ = b * a := by rw [h', one_mul]
  have hzZ : z ∈ Subgroup.center Q := Subgroup.mem_center_iff.mpr hzc
  obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).mp
    (mem_powers_of_prime_card hZ3 hc1 (g' := ⟨z, hzZ⟩))
  have hn' : c ^ n = z := by
    have := congrArg Subtype.val hn
    simpa using this
  have hcen : ∀ g : Q, g * c = c * g := Subgroup.mem_center_iff.mp hcZ
  have hpow : ∀ m : ℕ, a * b ^ m * a⁻¹ * (b ^ m)⁻¹ = c ^ m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      calc a * b ^ (m + 1) * a⁻¹ * (b ^ (m + 1))⁻¹
          = (a * b ^ m * a⁻¹ * (b ^ m)⁻¹) * (b ^ m * (a * b * a⁻¹ * b⁻¹) * (b ^ m)⁻¹) := by
            group
        _ = c ^ m * (b ^ m * c * (b ^ m)⁻¹) := by rw [ih, ← hcdef]
        _ = c ^ m * c := by rw [hcen (b ^ m), mul_inv_cancel_right]
        _ = c ^ (m + 1) := by rw [pow_succ]
  exact ⟨a, b ^ n, by rw [hpow n, hn']⟩

private theorem k89mod_step_normalFive {K : Type} [Group K] [Finite K]
    (hperf : ⁅(⊤ : Subgroup K), (⊤ : Subgroup K)⁆ = ⊤) (T : Subgroup K) [T.Normal]
    (hT : IsPGroup 2 T) (hbar : IsA6Z3 (K ⧸ T)) (e : K) (he : orderOf e = 5) (N : Subgroup K)
    (hN : N.Normal)
    (heN : e ∈ N) : N = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have heT : e ∉ T := by
    intro heT
    obtain ⟨k, hk⟩ := hT ⟨e, heT⟩
    have hk' : e ^ 2 ^ k = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    have hdvd : 5 ∣ 2 ^ k := by
      rw [← he]
      exact orderOf_dvd_of_pow_eq_one hk'
    have h52 := Nat.prime_five.dvd_of_dvd_pow hdvd
    omega
  have hNbar : N.map (QuotientGroup.mk' T) = ⊤ := by
    have hn : (N.map (QuotientGroup.mk' T)).Normal := hN.map _ (QuotientGroup.mk'_surjective T)
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hbar.1 hn with h | h
    · exact h
    · exfalso
      have hmem : QuotientGroup.mk' T e ∈ Subgroup.center (K ⧸ T) :=
        h (Subgroup.mem_map_of_mem _ heN)
      have h3 : (⟨_, hmem⟩ : Subgroup.center (K ⧸ T)) ^ 3 = 1 := by
        rw [← hbar.2.1]
        exact pow_card_eq_one'
      have h3' : (QuotientGroup.mk' T e) ^ 3 = 1 := by
        have := congrArg Subtype.val h3
        simpa using this
      have h5' : (QuotientGroup.mk' T e) ^ 5 = 1 := by
        rw [← map_pow, ← he, pow_orderOf_eq_one, map_one]
      have h1 : QuotientGroup.mk' T e = 1 := by
        have := pow_gcd_eq_one.mpr ⟨h3', h5'⟩
        simpa using this
      apply heT
      rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  have hsurj : Function.Surjective ((QuotientGroup.mk' N).comp T.subtype) := by
    intro x
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective N x
    have hk : QuotientGroup.mk' T k ∈ N.map (QuotientGroup.mk' T) := by
      rw [hNbar]
      exact Subgroup.mem_top _
    obtain ⟨n, hn, hnk⟩ := hk
    have ht : n⁻¹ * k ∈ T := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hnk
      exact hnk
    refine ⟨⟨n⁻¹ * k, ht⟩, ?_⟩
    rw [MonoidHom.comp_apply, Subgroup.coe_subtype, QuotientGroup.mk'_apply,
      QuotientGroup.mk'_apply, QuotientGroup.eq]
    have hid : (n⁻¹ * k)⁻¹ * k = k⁻¹ * n * k⁻¹⁻¹ := by group
    rw [hid]
    exact hN.conj_mem n hn k⁻¹
  have hpg : IsPGroup 2 (K ⧸ N) := hT.of_surjective _ hsurj
  have : Group.IsPerfect K := ⟨hperf⟩
  have hsub : Subsingleton (K ⧸ N) := by
    by_contra hns
    rw [not_subsingleton_iff_nontrivial] at hns
    exact Group.IsPerfect.not_isNilpotent (K ⧸ N) hpg.isNilpotent
  rw [eq_top_iff]
  intro k _
  have hk1 : (k : K ⧸ N) = 1 := Subsingleton.elim _ _
  rwa [QuotientGroup.eq_one_iff] at hk1

private theorem k89mod_step_eOrbit {F V G : Type*} [Field F] [AddCommGroup V] [Module F V]
    [Group G] (ρ : G →* Module.End F V)
    (hirr : ∀ W : Submodule F V, (∀ g : G, ∀ w ∈ W, ρ g w ∈ W) → W = ⊥ ∨ W = ⊤)
    (e : G) (he : orderOf e = 5) (hfix : ∀ v : V, ρ e v = v → v = 0)
    (hnorm : ∀ N : Subgroup G, N.Normal → e ∈ N → N = ⊤)
    (𝒲 : Set (Submodule F V)) (hne : ∀ W ∈ 𝒲, W ≠ ⊥) (hind : sSupIndep 𝒲)
    (hperm : ∀ g : G, ∀ W ∈ 𝒲, W.map (ρ g) ∈ 𝒲) : ∀ W ∈ 𝒲, W = ⊤ := by
  have hmap_mul : ∀ (g h : G) (W : Submodule F V),
      W.map (ρ (g * h)) = (W.map (ρ h)).map (ρ g) := by
    intro g h W
    rw [map_mul, Module.End.mul_eq_comp, Submodule.map_comp]
  have hmap_one : ∀ W : Submodule F V, W.map (ρ 1) = W := by
    intro W
    rw [map_one, Module.End.one_eq_id, Submodule.map_id]
  have he5 : e ^ 5 = 1 := by
    rw [← he]
    exact pow_orderOf_eq_one e
  have hfixW : ∀ W ∈ 𝒲, W.map (ρ e) = W := by
    intro W hW
    by_contra hneq
    have hpowne : ∀ i : ℕ, 1 ≤ i → i ≤ 4 → W.map (ρ (e ^ i)) ≠ W := by
      intro i hi1 hi4 heq
      apply hneq
      have hiter : ∀ m : ℕ, W.map (ρ (e ^ (i * m))) = W := by
        intro m
        induction m with
        | zero =>
          rw [mul_zero, pow_zero]
          exact hmap_one W
        | succ m ih =>
          rw [mul_add, mul_one, pow_add, hmap_mul, heq, ih]
      obtain ⟨m, hm⟩ : ∃ m : ℕ, e ^ (i * m) = e := by
        interval_cases i
        · exact ⟨1, by simp⟩
        · exact ⟨3, by rw [show 2 * 3 = 5 + 1 by norm_num, pow_add, he5, one_mul, pow_one]⟩
        · exact ⟨2, by rw [show 3 * 2 = 5 + 1 by norm_num, pow_add, he5, one_mul, pow_one]⟩
        · exact ⟨4, by
            rw [show 4 * 4 = 5 * 3 + 1 by norm_num, pow_add, pow_mul, he5, one_pow, one_mul,
              pow_one]⟩
      rw [← hm]
      exact hiter m
    obtain ⟨w, hwW, hw0⟩ := (Submodule.ne_bot_iff W).mp (hne W hW)
    let f : ℕ → V := fun i => ρ (e ^ i) w
    have hρf : ∀ i : ℕ, ρ e (f i) = f (i + 1) := by
      intro i
      simp only [f]
      rw [← Module.End.mul_apply, ← map_mul, ← pow_succ']
    have hf5 : f 5 = f 0 := by
      simp only [f]
      rw [he5, pow_zero]
    have hshift : ∑ i ∈ Finset.range 5, f (i + 1) = ∑ i ∈ Finset.range 5, f i := by
      have h1 := Finset.sum_range_succ' f 5
      have h2 := Finset.sum_range_succ f 5
      rw [h1, hf5] at h2
      exact add_right_cancel h2
    have hev : ρ e (∑ i ∈ Finset.range 5, f i) = ∑ i ∈ Finset.range 5, f i := by
      rw [map_sum, ← hshift]
      exact Finset.sum_congr rfl fun i _ => hρf i
    have hv0 := hfix _ hev
    rw [Finset.sum_range_succ'] at hv0
    have hf0 : f 0 = w := by
      simp only [f]
      rw [pow_zero, map_one, Module.End.one_apply]
    rw [hf0] at hv0
    have hrest : ∑ i ∈ Finset.range 4, f (i + 1) ∈ sSup (𝒲 \ {W}) := by
      refine Submodule.sum_mem _ fun i hi => ?_
      have hi4 : i < 4 := Finset.mem_range.mp hi
      have hmem : W.map (ρ (e ^ (i + 1))) ∈ 𝒲 \ {W} :=
        ⟨hperm _ W hW, hpowne (i + 1) (by omega) (by omega)⟩
      exact (le_sSup hmem) (Submodule.mem_map_of_mem hwW)
    have hwmem : w ∈ sSup (𝒲 \ {W}) := by
      have hw : w = -(∑ i ∈ Finset.range 4, f (i + 1)) := by
        rw [eq_neg_iff_add_eq_zero, add_comm w]
        exact hv0
      rw [hw]
      exact Submodule.neg_mem _ hrest
    exact hw0 ((Submodule.disjoint_def.mp (hind hW)) w hwW hwmem)
  let N : Subgroup G :=
    { carrier := {g | ∀ W ∈ 𝒲, W.map (ρ g) = W}
      mul_mem' := by
        intro a b ha hb W hW
        rw [hmap_mul, hb W hW, ha W hW]
      one_mem' := fun W _ => hmap_one W
      inv_mem' := by
        intro a ha W hW
        have h := hmap_mul a⁻¹ a W
        rw [inv_mul_cancel, hmap_one, ha W hW] at h
        exact h.symm }
  have hNn : N.Normal := by
    constructor
    intro n hn g W hW
    have hW' : W.map (ρ g⁻¹) ∈ 𝒲 := hperm g⁻¹ W hW
    have hn' : ∀ W ∈ 𝒲, W.map (ρ n) = W := hn
    show W.map (ρ (g * n * g⁻¹)) = W
    rw [hmap_mul, hmap_mul, hn' _ hW', ← hmap_mul, mul_inv_cancel, hmap_one]
  have hNtop : N = ⊤ := hnorm N hNn hfixW
  intro W hW
  have hinvW : ∀ g : G, ∀ w ∈ W, ρ g w ∈ W := by
    intro g w hw
    have hg : g ∈ N := by
      rw [hNtop]
      exact Subgroup.mem_top g
    have hg' : W.map (ρ g) = W := hg W hW
    rw [← hg']
    exact Submodule.mem_map_of_mem hw
  exact (hirr W hinvW).resolve_left (hne W hW)

private theorem k89mod_step_invEigenFamily {F V G : Type*} [Field F] [AddCommGroup V]
    [Module F V] [FiniteDimensional F V] [Nontrivial V] [Group G] (h2 : (2 : F) ≠ 0)
    (ρ : G →* Module.End F V) (T : Subgroup G) [T.Normal] (c : G) (hcT : c ∈ T)
    (hcZ : ∀ t ∈ T, c * t = t * c) (hc2 : c * c = 1) :
    ∃ 𝒲 : Set (Submodule F V), 𝒲.Nonempty ∧ (∀ W ∈ 𝒲, W ≠ ⊥) ∧ sSupIndep 𝒲 ∧
      (∀ g : G, ∀ W ∈ 𝒲, W.map (ρ g) ∈ 𝒲) ∧
      ∀ W ∈ 𝒲, (∀ w ∈ W, ρ c w = w) ∨ (∀ w ∈ W, ρ c w = -w) := by
  classical
  obtain ⟨J, hJ⟩ : ∃ J : Set G, ∀ a, a ∈ J ↔ a ∈ T ∧ (∀ t ∈ T, a * t = t * a) ∧ a * a = 1 :=
    ⟨{a | a ∈ T ∧ (∀ t ∈ T, a * t = t * a) ∧ a * a = 1}, fun a => Iff.rfl⟩
  have hcomm : ∀ a b : J, Commute (ρ a.1) (ρ b.1) := by
    intro a b
    show ρ a.1 * ρ b.1 = ρ b.1 * ρ a.1
    rw [← map_mul, ← map_mul, ((hJ a.1).mp a.2).2.1 b.1 ((hJ b.1).mp b.2).1]
  have hinvol : ∀ a : J, ρ a.1 * ρ a.1 = 1 := fun a => by
    rw [← map_mul, ((hJ a.1).mp a.2).2.2, map_one]
  have hρρ : ∀ (a : J) (v : V), ρ a.1 (ρ a.1 v) = v := fun a v => by
    rw [← Module.End.mul_apply, hinvol a, Module.End.one_apply]
  have hss : ∀ (a : J) (μ : F), (ρ a.1).maxGenEigenspace μ = (ρ a.1).eigenspace μ := by
    intro a μ
    have hsq : Squarefree (Polynomial.X ^ 2 - Polynomial.C (1 : F)) :=
      (Polynomial.separable_X_pow_sub_C (1 : F) (by exact_mod_cast h2) one_ne_zero).squarefree
    have haeval : Polynomial.aeval (ρ a.1) (Polynomial.X ^ 2 - Polynomial.C (1 : F)) = 0 := by
      rw [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, map_one, pow_two, hinvol a,
        sub_self]
    exact (Module.End.isSemisimple_of_squarefree_aeval_eq_zero hsq
      haeval).isFinitelySemisimple.maxGenEigenspace_eq_eigenspace μ
  have hspan1 : ∀ a : J, ⨆ μ, (ρ a.1).maxGenEigenspace μ = ⊤ := by
    intro a
    rw [eq_top_iff]
    intro v _
    have hv : v = (2 : F)⁻¹ • (v + ρ a.1 v) + (2 : F)⁻¹ • (v - ρ a.1 v) := by
      rw [← smul_add, add_add_sub_cancel, ← two_smul F v, smul_smul, inv_mul_cancel₀ h2,
        one_smul]
    rw [hv]
    refine Submodule.add_mem _ (Submodule.mem_iSup_of_mem 1 ?_)
      (Submodule.mem_iSup_of_mem (-1) ?_)
    · rw [hss, Module.End.mem_eigenspace_iff, map_smul, map_add, hρρ, one_smul, add_comm v]
    · rw [hss, Module.End.mem_eigenspace_iff, map_smul, map_sub, hρρ, neg_one_smul, ← smul_neg,
        neg_sub]
  have hspanM :=
    Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute
      (fun a : J => ρ a.1) (fun ⦃a b⦄ _ => hcomm a b) hspan1
  have hindM := Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo
    (fun a : J => ρ a.1) (fun a b μ => Module.End.mapsTo_maxGenEigenspace_of_comm (hcomm b a) μ)
  obtain ⟨t, ht⟩ : ∃ t : (J → F) → Submodule F V,
      ∀ χ, t χ = ⨅ a : J, (ρ a.1).eigenspace (χ a) :=
    ⟨fun χ => ⨅ a : J, (ρ a.1).eigenspace (χ a), fun χ => rfl⟩
  have hmemt : ∀ (χ : J → F) (v : V), v ∈ t χ ↔ ∀ a : J, ρ a.1 v = χ a • v := by
    intro χ v
    rw [ht, Submodule.mem_iInf]
    simp only [Module.End.mem_eigenspace_iff]
  have hspanE : ⨆ χ, t χ = ⊤ := by
    simp only [ht, ← hss]
    exact hspanM
  have hindE : iSupIndep t := by
    refine hindM.mono ?_
    intro χ
    rw [ht]
    exact iInf_mono fun a => Module.End.eigenspace_le_maxGenEigenspace
  have hJconj : ∀ (h : G) (a : J), h * a.1 * h⁻¹ ∈ J := by
    intro h a
    obtain ⟨haT, haZ, ha2⟩ := (hJ a.1).mp a.2
    rw [hJ]
    refine ⟨Subgroup.Normal.conj_mem inferInstance a.1 haT h, fun t ht => ?_, ?_⟩
    · have ht' : h⁻¹ * t * h⁻¹⁻¹ ∈ T := Subgroup.Normal.conj_mem inferInstance t ht h⁻¹
      have hc := haZ _ ht'
      calc h * a.1 * h⁻¹ * t = h * (a.1 * (h⁻¹ * t * h⁻¹⁻¹)) * h⁻¹ := by group
        _ = h * ((h⁻¹ * t * h⁻¹⁻¹) * a.1) * h⁻¹ := by rw [hc]
        _ = t * (h * a.1 * h⁻¹) := by group
    · calc h * a.1 * h⁻¹ * (h * a.1 * h⁻¹) = h * (a.1 * a.1) * h⁻¹ := by group
        _ = 1 := by rw [ha2, mul_one, mul_inv_cancel]
  have hρinv : ∀ (g : G) (v : V), ρ g (ρ g⁻¹ v) = v := fun g v => by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have hρinv' : ∀ (g : G) (v : V), ρ g⁻¹ (ρ g v) = v := fun g v => by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have hmap : ∀ (g : G) (χ : J → F),
      (t χ).map (ρ g) = t (fun a => χ ⟨g⁻¹ * a.1 * g⁻¹⁻¹, hJconj g⁻¹ a⟩) := by
    intro g χ
    ext v
    rw [hmemt]
    constructor
    · intro hv'
      obtain ⟨w, hw, rfl⟩ := (Submodule.mem_map).mp hv'
      intro b
      have hb : ρ (g⁻¹ * b.1 * g⁻¹⁻¹) w = χ ⟨g⁻¹ * b.1 * g⁻¹⁻¹, hJconj g⁻¹ b⟩ • w :=
        (hmemt χ w).mp hw ⟨g⁻¹ * b.1 * g⁻¹⁻¹, hJconj g⁻¹ b⟩
      have e : b.1 * g = g * (g⁻¹ * b.1 * g⁻¹⁻¹) := by group
      calc ρ b.1 (ρ g w) = ρ (b.1 * g) w := by rw [map_mul, Module.End.mul_apply]
        _ = ρ (g * (g⁻¹ * b.1 * g⁻¹⁻¹)) w := by rw [e]
        _ = ρ g (ρ (g⁻¹ * b.1 * g⁻¹⁻¹) w) := by rw [map_mul, Module.End.mul_apply]
        _ = ρ g (χ ⟨g⁻¹ * b.1 * g⁻¹⁻¹, hJconj g⁻¹ b⟩ • w) := by rw [hb]
        _ = χ ⟨g⁻¹ * b.1 * g⁻¹⁻¹, hJconj g⁻¹ b⟩ • ρ g w := map_smul _ _ _
    · intro hv
      refine (Submodule.mem_map).mpr ⟨ρ g⁻¹ v, ?_, hρinv g v⟩
      rw [hmemt]
      intro a
      have hχ : χ ⟨g⁻¹ * (g * a.1 * g⁻¹) * g⁻¹⁻¹, hJconj g⁻¹ ⟨g * a.1 * g⁻¹, hJconj g a⟩⟩ =
          χ a :=
        congrArg χ (Subtype.ext (show g⁻¹ * (g * a.1 * g⁻¹) * g⁻¹⁻¹ = a.1 by group))
      have hb : ρ (g * a.1 * g⁻¹) v = χ a • v := by
        rw [← hχ]
        exact hv ⟨g * a.1 * g⁻¹, hJconj g a⟩
      have e : a.1 * g⁻¹ = g⁻¹ * (g * a.1 * g⁻¹) := by group
      calc ρ a.1 (ρ g⁻¹ v) = ρ (a.1 * g⁻¹) v := by rw [map_mul, Module.End.mul_apply]
        _ = ρ (g⁻¹ * (g * a.1 * g⁻¹)) v := by rw [e]
        _ = ρ g⁻¹ (ρ (g * a.1 * g⁻¹) v) := by rw [map_mul, Module.End.mul_apply]
        _ = ρ g⁻¹ (χ a • v) := by rw [hb]
        _ = χ a • ρ g⁻¹ v := map_smul _ _ _
  refine ⟨Set.range t \ {⊥}, ?_, fun W hW => hW.2, hindE.sSupIndep_range.mono Set.diff_subset,
    ?_, ?_⟩
  · by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    have hall : ∀ χ, t χ = ⊥ := by
      intro χ
      by_contra hne
      have hmem : t χ ∈ Set.range t \ {⊥} := ⟨⟨χ, rfl⟩, hne⟩
      rw [hemp] at hmem
      exact hmem
    have htb : (⊤ : Submodule F V) = ⊥ := by
      rw [← hspanE]
      exact iSup_eq_bot.mpr hall
    exact top_ne_bot htb
  · rintro g _ ⟨⟨χ, rfl⟩, hW⟩
    refine ⟨⟨fun a => χ ⟨g⁻¹ * a.1 * g⁻¹⁻¹, hJconj g⁻¹ a⟩, (hmap g χ).symm⟩, ?_⟩
    intro hbot
    rw [Set.mem_singleton_iff] at hbot
    apply hW
    rw [Set.mem_singleton_iff, eq_bot_iff]
    intro w hw
    have hm : ρ g w ∈ (t χ).map (ρ g) := Submodule.mem_map_of_mem hw
    rw [hbot, Submodule.mem_bot] at hm
    rw [Submodule.mem_bot, ← hρinv' g w, hm, map_zero]
  · rintro _ ⟨⟨χ, rfl⟩, hW⟩
    let c' : J := ⟨c, (hJ c).mpr ⟨hcT, hcZ, hc2⟩⟩
    have hc' : ∀ w ∈ t χ, ρ c w = χ c' • w := fun w hw => (hmemt χ w).mp hw c'
    have hW' : t χ ≠ ⊥ := fun h => hW h
    obtain ⟨w0, hw0, hw00⟩ := (Submodule.ne_bot_iff _).mp hW'
    have hcc : ρ c (ρ c w0) = w0 := by
      rw [← Module.End.mul_apply, ← map_mul, hc2, map_one, Module.End.one_apply]
    have hsq : χ c' * χ c' = 1 := by
      have e : ρ c (ρ c w0) = (χ c' * χ c') • w0 := by
        rw [hc' w0 hw0, map_smul, hc' w0 hw0, smul_smul]
      rw [hcc] at e
      have e2 : (χ c' * χ c' - 1) • w0 = 0 := by
        rw [sub_smul, ← e, one_smul, sub_self]
      exact sub_eq_zero.mp ((smul_eq_zero.mp e2).resolve_right hw00)
    rcases mul_self_eq_one_iff.mp hsq with h1 | h1
    · left
      intro w hw
      rw [hc' w hw, h1, one_smul]
    · right
      intro w hw
      rw [hc' w hw, h1, neg_one_smul]

private theorem k89mod_weylTriple {K : Type} [Group K] [Finite K] (T : Subgroup K) [T.Normal]
    (hT : IsPGroup 2 T) (hbar : IsA6Z3 (K ⧸ T)) (z : K) (hz : orderOf z = 3)
    (hzc : QuotientGroup.mk' T z ∈ Subgroup.center (K ⧸ T)) :
    ∃ x y : K, x ^ 3 = 1 ∧ x * y * x⁻¹ * y⁻¹ = z ∧ x * z = z * x ∧ y * z = z * y := by
  obtain ⟨Q, hzQ, hQ27, ⟨a, ha, b, hb, hab⟩, hexp, hcomm⟩ :=
    k89mod_step_sylowThree T hT hbar z hz hzc
  obtain ⟨x, y, hxy⟩ := k89mod_step_cubeCommutator (Q := Q) hQ27
    ⟨⟨a, ha⟩, ⟨b, hb⟩, fun h => hab (congrArg Subtype.val h)⟩ ⟨z, hzQ⟩
    (fun c => Subtype.ext (hcomm c c.2))
  refine ⟨x, y, hexp x x.2, ?_, hcomm x x.2, hcomm y y.2⟩
  have h := congrArg Subtype.val hxy
  simpa using h

private theorem k89mod_three_dvd {K : Type} [Group K] [Finite K] (T : Subgroup K) [T.Normal]
    (hT : IsPGroup 2 T) (hbar : IsA6Z3 (K ⧸ T)) {F V : Type*} [Field F] [AddCommGroup V]
    [Module F V] [FiniteDimensional F V] (ρ : K →* Module.End F V) (z : K) (hz : orderOf z = 3)
    (hzc : QuotientGroup.mk' T z ∈ Subgroup.center (K ⧸ T))
    (hfix : ∀ v : V, ρ z v = v → v = 0) :
    3 ∣ Module.finrank F V := by
  obtain ⟨x, y, hx3, hxy, hxz, hyz⟩ := k89mod_weylTriple T hT hbar z hz hzc
  have key : ∀ u : V, ρ y⁻¹ (ρ y u) = u := fun u => by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have hxy' : x * y = z * y * x := by
    rw [← hxy]
    group
  refine k89mod_step_weyl (ρ x) (ρ y) (ρ z) ?_ ?_ ?_ ?_ ?_ ?_ hfix
  · intro u w huw
    rw [← key u, ← key w, huw]
  · rw [← map_pow, hx3, map_one]
  · rw [← map_pow, ← hz, pow_orderOf_eq_one, map_one]
  · rw [← map_mul, ← map_mul, hxz]
  · rw [← map_mul, ← map_mul, hyz]
  · rw [← map_mul, ← map_mul, ← map_mul, hxy']

private theorem k89mod_centralInvolution {F V G : Type*} [Field F] [AddCommGroup V]
    [Module F V] [FiniteDimensional F V] [Nontrivial V] [Group G] (h2 : (2 : F) ≠ 0)
    (ρ : G →* Module.End F V)
    (hirr : ∀ W : Submodule F V, (∀ g : G, ∀ w ∈ W, ρ g w ∈ W) → W = ⊥ ∨ W = ⊤)
    (T : Subgroup G) [T.Normal] (e : G) (he : orderOf e = 5)
    (hfix : ∀ v : V, ρ e v = v → v = 0) (hnorm : ∀ N : Subgroup G, N.Normal → e ∈ N → N = ⊤)
    (c : G) (hcT : c ∈ T) (hcZ : ∀ t ∈ T, c * t = t * c) (hc2 : c * c = 1) :
    ρ c = 1 ∨ ρ c = -1 := by
  obtain ⟨𝒲, ⟨W, hW⟩, hne, hind, hperm, hlink⟩ :=
    k89mod_step_invEigenFamily h2 ρ T c hcT hcZ hc2
  have htop : W = ⊤ := k89mod_step_eOrbit ρ hirr e he hfix hnorm 𝒲 hne hind hperm W hW
  have hmem : ∀ v : V, v ∈ W := fun v => by
    rw [htop]
    exact Submodule.mem_top
  rcases hlink W hW with h | h
  · left
    ext v
    simpa using h v (hmem v)
  · right
    ext v
    simpa using h v (hmem v)

private theorem k89mod_hom_eq_one_of_perfect {L M : Type*} [Group L] [Group M]
    [hM : Group.IsSolvable M] (hperf : ⁅(⊤ : Subgroup L), (⊤ : Subgroup L)⁆ = ⊤) (f : L →* M) :
    f = 1 := by
  obtain ⟨n, hn⟩ := hM.solvable
  have hd : ∀ k, derivedSeries L k = ⊤ := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [derivedSeries_succ, ih]
      exact hperf
  have h1 : (derivedSeries L n).map f ≤ derivedSeries M n :=
    map_derivedSeries_le_derivedSeries f n
  rw [hd n, hn] at h1
  ext x
  have hx : f x ∈ (⊥ : Subgroup M) := h1 ⟨x, Subgroup.mem_top x, rfl⟩
  simpa using hx

private theorem k89mod_uniqueInvCentral {K : Type*} [Group K] [Finite K]
    (hperf : ⁅(⊤ : Subgroup K), (⊤ : Subgroup K)⁆ = ⊤) (T : Subgroup K) [T.Normal]
    (hT : IsPGroup 2 T) (huniq : ∀ a ∈ T, ∀ b ∈ T, orderOf a = 2 → orderOf b = 2 → a = b) :
    T ≤ Subgroup.center K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro t ht
  by_cases hw : ∃ w : T, orderOf w = 2
  · obtain ⟨w, hw⟩ := hw
    have hrank : CFSG.Open.twoRank T ≤ 1 :=
      CFSG.Semidihedral.CharacteristicSL2Layer.twoRank_le_one_of_unique_involution w hw
        fun x hx => Subtype.ext (huniq x x.2 w w.2 (by rwa [Subgroup.orderOf_coe])
          (by rwa [Subgroup.orderOf_coe]))
    have : Group.IsSolvable (MulAut T) :=
      CFSG.ProperTwoGeneratedCore.rank_one_two_group_automorphism_solvable (↥T) hT hrank
    have h1 := k89mod_hom_eq_one_of_perfect hperf (MulAut.conjNormal : K →* MulAut T)
    rw [Subgroup.mem_center_iff]
    intro g
    have h2 : g * t * g⁻¹ = t := by
      have h3 : ((MulAut.conjNormal g ⟨t, ht⟩ : T) : K) = t := by
        rw [h1, MonoidHom.one_apply, MulAut.one_apply]
      rwa [MulAut.conjNormal_apply] at h3
    calc g * t = g * t * g⁻¹ * g := by group
      _ = t * g := by rw [h2]
  · have ht1 : t = 1 := by
      by_contra ht1
      apply hw
      have hnt : Nontrivial T := ⟨⟨⟨t, ht⟩, 1, fun h => ht1 (congrArg Subtype.val h)⟩⟩
      obtain ⟨k, hk, hcard⟩ := hT.nontrivial_iff_card.mp hnt
      have hdvd : 2 ∣ Nat.card T := by
        rw [hcard]
        exact dvd_pow_self 2 (Nat.pos_iff_ne_zero.mp hk)
      exact exists_prime_orderOf_dvd_card' 2 hdvd
    rw [ht1]
    exact Subgroup.one_mem _

private theorem k89mod_invSplit {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (h2 : (2 : F) ≠ 0) (f : Module.End F V) (hf : f * f = 1) :
    Module.finrank F (LinearMap.ker (f - 1)) + Module.finrank F (LinearMap.ker (f + 1)) =
      Module.finrank F V := by
  have hff : ∀ v : V, f (f v) = v := fun v => by
    rw [← Module.End.mul_apply, hf, Module.End.one_apply]
  have hc : IsCompl (LinearMap.ker (f - 1)) (LinearMap.ker (f + 1)) := by
    constructor
    · rw [Submodule.disjoint_def]
      intro v h1 h1'
      rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at h1
      rw [LinearMap.mem_ker, LinearMap.add_apply, Module.End.one_apply, h1] at h1'
      have h2v : (2 : F) • v = 0 := by
        rw [two_smul]
        exact h1'
      exact (smul_eq_zero.mp h2v).resolve_left h2
    · rw [codisjoint_iff, eq_top_iff]
      intro v _
      have hv : v = (2 : F)⁻¹ • (v + f v) + (2 : F)⁻¹ • (v - f v) := by
        rw [← smul_add, add_add_sub_cancel, ← two_smul F v, smul_smul, inv_mul_cancel₀ h2,
          one_smul]
      rw [hv]
      refine Submodule.add_mem_sup ?_ ?_
      · rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, map_smul, map_add,
          hff, add_comm (f v) v, sub_self]
      · rw [LinearMap.mem_ker, LinearMap.add_apply, Module.End.one_apply, map_smul, map_sub,
          hff, ← smul_add, sub_add_sub_cancel', sub_self, smul_zero]
  exact Submodule.finrank_add_eq_of_isCompl hc

private theorem k89mod_detEven {F V G : Type*} [Field F] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] [Group G] (h2 : (2 : F) ≠ 0)
    (hperf : ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ = ⊤)
    (ρ : G →* Module.End F V) (c : G) (hc : ρ c = -1) : Even (Module.finrank F V) := by
  let δ : G →* Fˣ := (LinearMap.det.comp ρ).toHomUnits
  have hker : commutator G ≤ δ.ker := Abelianization.commutator_subset_ker δ
  have hc1 : δ c = 1 := by
    have : c ∈ commutator G := by
      rw [commutator_def, hperf]
      exact Subgroup.mem_top c
    exact hker this
  have hdet : LinearMap.det (ρ c) = 1 := by
    have := congrArg Units.val hc1
    simpa [δ] using this
  have hneg : LinearMap.det (ρ c) = (-1) ^ Module.finrank F V := by
    rw [hc, show (-1 : Module.End F V) = (-1 : F) • (1 : Module.End F V) by rw [neg_one_smul],
      LinearMap.det_smul, map_one, mul_one]
  have hne : (-1 : F) ≠ 1 := by
    intro h
    apply h2
    linear_combination -h
  exact (neg_one_pow_eq_one_iff_even hne).mp (hneg ▸ hdet)

private theorem k89mod_centerInvolution {K : Type*} [Group K] [Finite K] (T : Subgroup K)
    (hT : IsPGroup 2 T) (a : K) (ha : a ∈ T) (ha2 : orderOf a = 2) :
    ∃ c ∈ T, (∀ t ∈ T, c * t = t * c) ∧ orderOf c = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnt : Nontrivial T := by
    refine ⟨⟨⟨a, ha⟩, 1, fun h => ?_⟩⟩
    have h' : a = 1 := congrArg Subtype.val h
    rw [h', orderOf_one] at ha2
    omega
  have hZ : Nontrivial (Subgroup.center T) := hT.center_nontrivial
  obtain ⟨k, hk, hcard⟩ := (hT.to_subgroup (Subgroup.center T)).nontrivial_iff_card.mp hZ
  have hdvd : 2 ∣ Nat.card (Subgroup.center T) := by
    rw [hcard]
    exact dvd_pow_self 2 (Nat.pos_iff_ne_zero.mp hk)
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
  refine ⟨((c : T) : K), (c : T).2, fun t ht => ?_, ?_⟩
  · have := Subgroup.mem_center_iff.mp c.2 ⟨t, ht⟩
    exact (congrArg Subtype.val this).symm
  · rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hc]

private theorem k89mod_two_ne_zero {q : ℕ} (hq7 : 7 ≤ q) : (2 : ZMod q) ≠ 0 := by
  intro h
  have h' : ((2 : ℕ) : ZMod q) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at h'
  have := Nat.le_of_dvd (by norm_num) h'
  omega

private theorem k89mod_pCore_le_center {q : ℕ} [Fact q.Prime] (hq7 : 7 ≤ q) {K : Type}
    [Group K] [Finite K] (hperf : ⁅(⊤ : Subgroup K), (⊤ : Subgroup K)⁆ = ⊤)
    (hbar : IsA6Z3 (K ⧸ CFSG.pCore 2 K)) {V : Type} [AddCommGroup V] [Module (ZMod q) V]
    [Finite V] [Nontrivial V] (ρ : K →* Module.End (ZMod q) V) (hinj : Function.Injective ρ)
    (hirr : ∀ W : Submodule (ZMod q) V, (∀ k : K, ∀ w ∈ W, ρ k w ∈ W) → W = ⊥ ∨ W = ⊤)
    (z : K) (hz3 : orderOf z = 3)
    (hzc : QuotientGroup.mk' (CFSG.pCore 2 K) z ∈ Subgroup.center (K ⧸ CFSG.pCore 2 K))
    (hzfix : ∀ v : V, ρ z v = v → v = 0) (e : K) (he5 : orderOf e = 5)
    (hefix : ∀ v : V, ρ e v = v → v = 0)
    (hinv : ∀ t : K, orderOf t = 2 → Module.finrank (ZMod q) (LinearMap.ker (ρ t - 1)) ≤ 2) :
    CFSG.pCore 2 K ≤ Subgroup.center K := by
  have h2 : (2 : ZMod q) ≠ 0 := k89mod_two_ne_zero hq7
  have hT : IsPGroup 2 (CFSG.pCore 2 K) := CFSG.pCore_isPGroup
  have hnorm : ∀ N : Subgroup K, N.Normal → e ∈ N → N = ⊤ := fun N hN heN =>
    k89mod_step_normalFive hperf (CFSG.pCore 2 K) hT hbar e he5 N hN heN
  have h3 : 3 ∣ Module.finrank (ZMod q) V :=
    k89mod_three_dvd (CFSG.pCore 2 K) hT hbar ρ z hz3 hzc hzfix
  have hpos : 0 < Module.finrank (ZMod q) V := Module.finrank_pos
  have key : ∀ a ∈ CFSG.pCore 2 K, orderOf a = 2 → ∀ c ∈ CFSG.pCore 2 K,
      (∀ t ∈ CFSG.pCore 2 K, c * t = t * c) → orderOf c = 2 → a = c := by
    intro a ha ha2 c hcT hcZ hc2
    have hcc : c * c = 1 := by rw [← pow_two, ← hc2, pow_orderOf_eq_one]
    have haa : a * a = 1 := by rw [← pow_two, ← ha2, pow_orderOf_eq_one]
    have hρc : ρ c = -1 := by
      rcases k89mod_centralInvolution h2 ρ hirr (CFSG.pCore 2 K) e he5 hefix hnorm c hcT hcZ
          hcc with h | h
      · exfalso
        have hc1 : c = 1 := hinj (by rw [h, map_one])
        rw [hc1, orderOf_one] at hc2
        omega
      · exact h
    have heven : Even (Module.finrank (ZMod q) V) := k89mod_detEven h2 hperf ρ c hρc
    by_contra hac
    have hac2 : orderOf (a * c) = 2 := by
      apply orderOf_eq_prime
      · rw [pow_two, mul_assoc, ← mul_assoc c a c, hcZ a ha, mul_assoc a c c, hcc, mul_one,
          haa]
      · intro h
        apply hac
        calc a = a * (c * c) := by rw [hcc, mul_one]
          _ = (a * c) * c := by rw [mul_assoc]
          _ = c := by rw [h, one_mul]
    have hρaa : ρ a * ρ a = 1 := by rw [← map_mul, haa, map_one]
    have hsplit := k89mod_invSplit h2 (ρ a) hρaa
    have hle1 := hinv a ha2
    have hle2 := hinv (a * c) hac2
    have hker : LinearMap.ker (ρ (a * c) - 1) = LinearMap.ker (ρ a + 1) := by
      rw [map_mul, hρc, mul_neg, mul_one, ← neg_add', LinearMap.ker_neg]
    rw [hker] at hle2
    have hle : Module.finrank (ZMod q) V ≤ 4 := by
      rw [← hsplit]
      exact add_le_add hle1 hle2
    obtain ⟨m, hm⟩ := h3
    obtain ⟨r, hr⟩ := heven
    omega
  refine k89mod_uniqueInvCentral hperf (CFSG.pCore 2 K) hT ?_
  intro a ha b hb ha2 hb2
  obtain ⟨c, hcT, hcZ, hc2⟩ := k89mod_centerInvolution (CFSG.pCore 2 K) hT a ha ha2
  rw [key a ha ha2 c hcT hcZ hc2, key b hb hb2 c hcT hcZ hc2]

private theorem k89mod_schurSix {K : Type} [Group K]
    [Group.IsPerfect K] (e : K ⧸ Subgroup.center K ≃* alternatingGroup (Fin 6)) :
    Nat.card (Subgroup.center K) ∣ 6 := by
  let q : K →* alternatingGroup (Fin 6) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : q.ker = Subgroup.center K := by
    ext x
    simp [q]
  have hd : Nat.card q.ker ∣
      Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier (alternatingGroup (Fin 6))) := by
    rw [← CFSG.RankThree.PerfectCover.map_hopfMultiplier_hopfLift q hq hker.le]
    exact Subgroup.card_map_dvd _ _
  rwa [hker, CFSG.Alternating.Multipliers.hopfMultiplier_alternatingGroup_six.2] at hd

private theorem k89mod_charInput {K : Type} [Group K] [Finite K]
    (hperf : ⁅(⊤ : Subgroup K), (⊤ : Subgroup K)⁆ = ⊤) (T : Subgroup K) [T.Normal]
    (hbar : IsA6Z3 (K ⧸ T)) (hTZ : T ≤ Subgroup.center K) (z : K)
    (hzc : QuotientGroup.mk' T z ∈ Subgroup.center (K ⧸ T)) :
    IsQuasisimple K ∧ (Nat.card (Subgroup.center K) = 3 ∨ Nat.card (Subgroup.center K) = 6) ∧
      IsAlt (K ⧸ Subgroup.center K) 6 ∧ z ∈ Subgroup.center K := by
  obtain ⟨⟨-, hsimpleBar, a, b, hab⟩, hcardBar, ⟨eBar⟩⟩ := hbar
  have hperfK : Group.IsPerfect K := ⟨hperf⟩
  have hZ : (Subgroup.center (K ⧸ T)).comap (QuotientGroup.mk' T) = Subgroup.center K :=
    CFSG.LocalCores.comap_center_eq_of_perfect hperfK (QuotientGroup.mk' T)
      (QuotientGroup.mk'_surjective T) (by rw [QuotientGroup.ker_mk']; exact hTZ)
  have hmap : (Subgroup.center K).map (QuotientGroup.mk' T) = Subgroup.center (K ⧸ T) := by
    rw [← hZ]
    exact Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective T) _
  let e1 : (K ⧸ T) ⧸ Subgroup.center (K ⧸ T) ≃* K ⧸ Subgroup.center K :=
    (QuotientGroup.quotientMulEquivOfEq hmap.symm).trans
      (QuotientGroup.quotientQuotientEquivQuotient T (Subgroup.center K) hTZ)
  let e2 : K ⧸ Subgroup.center K ≃* alternatingGroup (Fin 6) := e1.symm.trans eBar
  have hnt : Nontrivial (K ⧸ Subgroup.center K) := ⟨⟨e1 a, e1 b, fun h => hab (by
    rw [e1.injective h])⟩⟩
  have hsimple : IsSimpleGroup (K ⧸ Subgroup.center K) :=
    IsSimpleGroup.isSimpleGroup_of_surjective e1.toMonoidHom e1.surjective
  have hnab : ∃ a b : K ⧸ Subgroup.center K, a * b ≠ b * a :=
    ⟨e1 a, e1 b, fun h => hab (e1.injective (by rw [map_mul, map_mul, h]))⟩
  have hdvd : Nat.card (Subgroup.center K) ∣ 6 := k89mod_schurSix e2
  have h360 : Nat.card (alternatingGroup (Fin 6)) = 360 := by
    rw [nat_card_alternatingGroup, Nat.card_fin]
    decide
  have c1 := Subgroup.card_eq_card_quotient_mul_card_subgroup T
  have c2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center K)
  have c3 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center (K ⧸ T))
  rw [Nat.card_congr e2.toEquiv, h360] at c2
  rw [Nat.card_congr eBar.toEquiv, h360, hcardBar] at c3
  rw [c3] at c1
  have hTpos : 0 < Nat.card T := Nat.card_pos
  have hle := Nat.le_of_dvd (by norm_num) hdvd
  refine ⟨⟨hperfK, hsimple, hnab⟩, by omega, ⟨e2⟩, ?_⟩
  rw [← hZ]
  exact hzc

theorem s889_module (hchar : Alt6CharCore) : S889Module := by
  intro q hq hq7 K _ _ hperf hbar V _ _ _ _ ρ hinj hirr z hz3 hzc hzfix e he5 hefix hinv
  have : Fact q.Prime := ⟨hq⟩
  have hTZ := k89mod_pCore_le_center hq7 hperf hbar ρ hinj hirr z hz3 hzc hzfix e he5 hefix hinv
  obtain ⟨hquasi, hcard, halt, hzcen⟩ :=
    k89mod_charInput hperf (CFSG.pCore 2 K) hbar hTZ z hzc
  obtain ⟨v, hv0, hv⟩ := hchar q hq hq7 K hquasi hcard halt V ρ z hzcen hz3 hzfix e he5
  exact hv0 (hefix v hv)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
