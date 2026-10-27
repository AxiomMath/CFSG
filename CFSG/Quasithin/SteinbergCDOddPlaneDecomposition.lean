module

public import CFSG.Quasithin.SteinbergBQCyclicFiveSupport

public noncomputable section

namespace CFSG.Quasithin.SteinbergCD

open Module CFSG.Quasithin.SteinbergBQ Subgroup

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {p : ℕ}

theorem apply_sum_pow_eq {g : LinearMap.GeneralLinearGroup (ZMod 2) V} (hg : g ^ p = 1)
    (v : V) :
    (g : V →ₗ[ZMod 2] V) (∑ k ∈ Finset.range p,
        ((g ^ k : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) v) =
      ∑ k ∈ Finset.range p,
        ((g ^ k : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) v := by
  set f : ℕ → V := fun k =>
    ((g ^ k : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) v with hf
  have h1 : ∀ k, (g : V →ₗ[ZMod 2] V) (f k) = f (k + 1) := fun k => by
    simp only [hf]
    rw [pow_succ', Units.val_mul, Module.End.mul_apply]
  rw [map_sum, Finset.sum_congr rfl fun k _ => h1 k]
  have h2 := Finset.sum_range_succ' f p
  have h3 := Finset.sum_range_succ f p
  have hp0 : f p = f 0 := by
    rw [hf]
    simp only [hg, pow_zero]
  rw [h3, hp0] at h2
  exact (add_right_cancel h2).symm

theorem sum_pow_apply_of_fixed (hp : Odd p) {g : LinearMap.GeneralLinearGroup (ZMod 2) V}
    {v : V} (hv : (g : V →ₗ[ZMod 2] V) v = v) :
    ∑ k ∈ Finset.range p,
      ((g ^ k : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) v = v := by
  have hk : ∀ k : ℕ,
      ((g ^ k : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) v = v := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [pow_succ', Units.val_mul, Module.End.mul_apply, ih, hv]
  rw [Finset.sum_congr rfl fun k _ => hk k, Finset.sum_const, Finset.card_range]
  obtain ⟨m, rfl⟩ := hp
  rw [add_smul, mul_smul, one_smul]
  have h2 : (2 : ℕ) • v = 0 := by
    rw [two_nsmul]
    exact CFSG.LinearAlgebra.zmod2_vec_add_self v
  rw [smul_comm, h2, smul_zero, zero_add]

theorem pow_apply_of_fixed {g : LinearMap.GeneralLinearGroup (ZMod 2) V} {w : V}
    (hw : (g : V →ₗ[ZMod 2] V) w = w) (k : ℕ) :
    ((g ^ k : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) w = w := by
  induction k with
  | zero => rfl
  | succ k ih => rw [pow_succ', Units.val_mul, Module.End.mul_apply, ih, hw]

theorem sum_pow_apply_eq_zero [FiniteDimensional (ZMod 2) V]
    {d : LinearMap.GeneralLinearGroup (ZMod 2) V} (hd : d ^ p = 1) {u : V}
    (hu : u ∈ commSpan (zpowers d)) :
    ∑ k ∈ Finset.range p,
      ((d ^ k : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) u = 0 := by
  have := finite_generalLinearGroup (V := V)
  set S : V →ₗ[ZMod 2] V := ∑ k ∈ Finset.range p,
    ((d ^ k : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) with hS
  have hSapp : ∀ v, S v = ∑ k ∈ Finset.range p,
      ((d ^ k : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) v := fun v => by
    rw [hS, LinearMap.sum_apply]
  rw [← hSapp]
  induction hu using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨x, hx, v, rfl⟩ := hw
    obtain ⟨m, rfl⟩ := (Submonoid.mem_powers_iff _ _).1 (mem_powers_iff_mem_zpowers.2 hx)
    have hcomm : ∀ k, ((d ^ k : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V)
        (((d ^ m : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) v) =
        ((d ^ m : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V)
          (((d ^ k : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) v) := fun k => by
      rw [← Module.End.mul_apply, ← Units.val_mul, ← pow_add, add_comm, pow_add, Units.val_mul,
        Module.End.mul_apply]
    rw [map_sub, hSapp, hSapp, Finset.sum_congr rfl fun k _ => hcomm k, ← map_sum,
      pow_apply_of_fixed (apply_sum_pow_eq hd v) m, sub_self]
  | zero => exact map_zero S
  | add a b _ _ ha hb => rw [map_add, ha, hb, add_zero]
  | smul c a _ ha => rw [map_smul, ha, smul_zero]

theorem map_mem_commSpan_of_mem_normalizer {Q : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) V)}
    {g : LinearMap.GeneralLinearGroup (ZMod 2) V}
    (hg : g ∈ normalizer (Q : Set (LinearMap.GeneralLinearGroup (ZMod 2) V))) {w : V}
    (hw : w ∈ commSpan Q) : (g : V →ₗ[ZMod 2] V) w ∈ commSpan Q := by
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨x, hx, v, rfl⟩ := hw
    have e : (g : V →ₗ[ZMod 2] V) ((x : V →ₗ[ZMod 2] V) v - v) =
        ((g * x * g⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V)
          ((g : V →ₗ[ZMod 2] V) v) - (g : V →ₗ[ZMod 2] V) v := by
      rw [map_sub, Units.val_mul, Units.val_mul, Module.End.mul_apply, Module.End.mul_apply,
        ← Module.End.mul_apply (((g⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) V)) :
          V →ₗ[ZMod 2] V), ← Units.val_mul, inv_mul_cancel, Units.val_one, Module.End.one_apply]
    rw [e]
    exact sub_mem_commSpan Q ((mem_normalizer_iff.1 hg x).1 hx) _
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
  | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ c ha

theorem mem_normalizer_of_commute {G : Type*} [Group G] {Q : Subgroup G} {g : G}
    (hg : ∀ x ∈ Q, g * x = x * g) : g ∈ normalizer (Q : Set G) := by
  rw [mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [hg x hx, mul_inv_cancel_right]
    exact hx
  · intro hx
    have h1 := hg _ hx
    have h2 : g * x * g⁻¹ = x := by
      have h3 : g * (g * x * g⁻¹) = g * x := by
        rw [h1]
        group
      exact mul_left_cancel h3
    rw [← h2]
    exact hx

theorem finrank_eq_mul_of_conj [FiniteDimensional (ZMod 2) V] (hp : p.Prime) (hp2 : p ≠ 2)
    {z y : LinearMap.GeneralLinearGroup (ZMod 2) V} (hz : z ^ p = 1) (hz1 : z ≠ 1)
    (hyz : y * z = z * y) (hyc : ∀ c ∈ zpowers z, (y * c) ^ p = 1)
    (hconj : ∀ c ∈ zpowers z, ∃ g ∈ normalizer
      ((zpowers z : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) V)) :
        Set (LinearMap.GeneralLinearGroup (ZMod 2) V)), g * y * g⁻¹ = y * c) :
    finrank (ZMod 2) (commSpan (zpowers z)) = p * finrank (ZMod 2)
      (commSpan (zpowers z) ⊓ LinearMap.ker ((y : V →ₗ[ZMod 2] V) - 1) :
        Submodule (ZMod 2) V) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have := finite_generalLinearGroup (V := V)
  have hodd : Odd p := hp.odd_of_ne_two hp2
  set Z := zpowers z with hZ
  set U := commSpan Z with hU
  have : Fintype Z := Fintype.ofFinite Z
  have hZcard : Nat.card Z = p := by rw [hZ, Nat.card_zpowers, orderOf_eq_prime hz hz1]
  have hyZ : ∀ c ∈ Z, y * c = c * y := fun c hc => by
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hc
    exact ((Commute.zpow_right hyz n)).eq
  have hZZ : ∀ c ∈ Z, ∀ c' ∈ Z, c * c' = c' * c := fun c hc c' hc' => by
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hc
    obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 hc'
    exact (Commute.zpow_zpow_self z n m).eq
  have hZp : ∀ c ∈ Z, c ^ p = 1 := fun c hc => by
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hc
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hz, one_zpow]
  have hval : ∀ (g h : LinearMap.GeneralLinearGroup (ZMod 2) V) (v : V),
      ((g * h : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) v =
        (g : V →ₗ[ZMod 2] V) ((h : V →ₗ[ZMod 2] V) v) := fun g h v => by
    rw [Units.val_mul, Module.End.mul_apply]
  have hUN : ∀ g ∈ normalizer (Z : Set (LinearMap.GeneralLinearGroup (ZMod 2) V)), ∀ u ∈ U,
      (g : V →ₗ[ZMod 2] V) u ∈ U := fun g hg u hu => map_mem_commSpan_of_mem_normalizer hg hu
  have hycN : ∀ c ∈ Z, y * c ∈ normalizer (Z : Set (LinearMap.GeneralLinearGroup (ZMod 2) V)) :=
    fun c hc => mem_normalizer_of_commute fun x hx => by
      rw [mul_assoc, hZZ c hc x hx, ← mul_assoc, hyZ x hx, mul_assoc]
  set F : Z → Submodule (ZMod 2) V := fun c =>
    U ⊓ LinearMap.ker (((y * c : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) - 1)
    with hF
  set e : Z → V → V := fun c v => ∑ k ∈ Finset.range p,
    (((y * c) ^ k : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) v with he
  have he_ker : ∀ c : Z, ∀ v, (((y * c : LinearMap.GeneralLinearGroup (ZMod 2) V) :
      V →ₗ[ZMod 2] V)) (e c v) = e c v := fun c v => apply_sum_pow_eq (hyc c c.2) v
  have he_U : ∀ c : Z, ∀ u ∈ U, e c u ∈ U := fun c u hu =>
    Submodule.sum_mem _ fun k _ => hUN _ (pow_mem (hycN c c.2) k) u hu
  have he_F : ∀ c : Z, ∀ u ∈ U, e c u ∈ F c := fun c u hu => by
    refine Submodule.mem_inf.2 ⟨he_U c u hu, ?_⟩
    rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, he_ker, sub_self]
  have he_fix : ∀ c : Z, ∀ u ∈ F c, e c u = u := fun c u hu => by
    have h := (Submodule.mem_inf.1 hu).2
    rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at h
    exact sum_pow_apply_of_fixed hodd h
  have he_zero : ∀ c c' : Z, c ≠ c' → ∀ u ∈ F c', e c u = 0 := by
    intro c c' hcc' u hu
    obtain ⟨huU, huk⟩ := Submodule.mem_inf.1 hu
    rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero, hval] at huk
    set d := (c : LinearMap.GeneralLinearGroup (ZMod 2) V) * (c' : _)⁻¹ with hd
    have hdZ : d ∈ Z := mul_mem c.2 (inv_mem c'.2)
    have hd1 : d ≠ 1 := fun h => hcc' (Subtype.ext (mul_inv_eq_one.1 h))
    have hyu : (y : V →ₗ[ZMod 2] V) u =
        ((((c' : LinearMap.GeneralLinearGroup (ZMod 2) V))⁻¹ :
          LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) u := by
      have h1 : ((c' : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V)
          ((y : V →ₗ[ZMod 2] V) u) = u := by
        rw [← hval, ← hyZ _ c'.2, hval]
        exact huk
      calc (y : V →ₗ[ZMod 2] V) u
          = (((((c' : LinearMap.GeneralLinearGroup (ZMod 2) V))⁻¹ * c' :
              LinearMap.GeneralLinearGroup (ZMod 2) V)) : V →ₗ[ZMod 2] V)
              ((y : V →ₗ[ZMod 2] V) u) := by
            rw [inv_mul_cancel, Units.val_one, Module.End.one_apply]
        _ = _ := by rw [hval, h1]
    have hycu : (((y * c : LinearMap.GeneralLinearGroup (ZMod 2) V)) : V →ₗ[ZMod 2] V) u =
        (d : V →ₗ[ZMod 2] V) u := by
      rw [hyZ _ c.2, hval, hyu, hd, hval]
      rfl
    have hpow : ∀ k : ℕ, ((((y * c) ^ k : LinearMap.GeneralLinearGroup (ZMod 2) V)) :
        V →ₗ[ZMod 2] V) u = ((d ^ k : LinearMap.GeneralLinearGroup (ZMod 2) V) :
          V →ₗ[ZMod 2] V) u := by
      intro k
      induction k with
      | zero => rfl
      | succ k ih =>
        have hcomm : (y * c) * d ^ k = d ^ k * (y * c) := by
          refine (Commute.pow_right ?_ k).eq
          show (y * c) * d = d * (y * c)
          rw [mul_assoc, hZZ c c.2 d hdZ, ← mul_assoc, hyZ d hdZ, mul_assoc]
        rw [pow_succ', hval, ih, ← hval, hcomm, hval, hycu, ← hval, ← pow_succ]
    have hdZ' : zpowers d = Z := by
      have hle : zpowers d ≤ Z := zpowers_le.2 hdZ
      refine eq_of_le_of_card_ge hle ?_
      rw [hZcard, Nat.card_zpowers, orderOf_eq_prime (hZp d hdZ) hd1]
    rw [he]
    simp only
    rw [Finset.sum_congr rfl fun k _ => hpow k]
    exact sum_pow_apply_eq_zero (hZp d hdZ) (hdZ' ▸ huU)
  have hsum : ∀ u ∈ U, ∑ c : Z, e c u = u := by
    intro u hu
    have hck : ∀ (c : Z) (k : ℕ), ((((y * c) ^ k : LinearMap.GeneralLinearGroup (ZMod 2) V)) :
        V →ₗ[ZMod 2] V) u = ((y ^ k : LinearMap.GeneralLinearGroup (ZMod 2) V) :
          V →ₗ[ZMod 2] V) (((((c : LinearMap.GeneralLinearGroup (ZMod 2) V) ^ k) :
            LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) u) := fun c k => by
      rw [(Commute.mul_pow (hyZ c c.2) k), hval]
    have hinner : ∀ k ∈ Finset.range p, ∑ c : Z,
        ((((c : LinearMap.GeneralLinearGroup (ZMod 2) V) ^ k) :
          LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) u =
        if k = 0 then u else 0 := by
      intro k hk
      split_ifs with hk0
      · subst hk0
        simp only [pow_zero, Units.val_one, Module.End.one_apply, Finset.sum_const,
          Finset.card_univ]
        rw [← Nat.card_eq_fintype_card, hZcard]
        obtain ⟨m, rfl⟩ := hodd
        rw [add_smul, mul_smul, one_smul]
        have h2 : (2 : ℕ) • u = 0 := by
          rw [two_nsmul]
          exact CFSG.LinearAlgebra.zmod2_vec_add_self u
        rw [smul_comm, h2, smul_zero, zero_add]
      · have hcop : (Nat.card Z).Coprime k := by
          rw [hZcard]
          exact Nat.coprime_of_lt_prime hk0 (Finset.mem_range.1 hk) hp
        have h := Fintype.sum_equiv (powCoprime hcop)
          (fun c : Z => ((((c : LinearMap.GeneralLinearGroup (ZMod 2) V) ^ k) :
            LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) u)
          (fun c : Z => ((c : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) u)
          fun c => rfl
        rw [h]
        exact sum_apply_eq_zero Z hu
    rw [he]
    simp only
    rw [Finset.sum_comm]
    have hk : ∀ k ∈ Finset.range p, ∑ c : Z, ((((y * c) ^ k :
        LinearMap.GeneralLinearGroup (ZMod 2) V)) : V →ₗ[ZMod 2] V) u =
        if k = 0 then u else 0 := by
      intro k hk
      rw [Finset.sum_congr rfl fun c _ => hck c k, ← map_sum, hinner k hk]
      split_ifs with hk0
      · subst hk0
        rfl
      · exact map_zero _
    rw [Finset.sum_congr rfl hk, Finset.sum_ite_eq' (Finset.range p) 0 fun _ => u]
    simp only [Finset.mem_range, hp.pos, ↓reduceIte]
  set Φ : (∀ c : Z, F c) →ₗ[ZMod 2] V :=
    { toFun := fun x => ∑ c, (x c : V)
      map_add' := fun x x' => by
        simp only [Pi.add_apply, Submodule.coe_add, Finset.sum_add_distrib]
      map_smul' := fun a x => by
        simp only [Pi.smul_apply, Submodule.coe_smul, RingHom.id_apply, Finset.smul_sum] }
    with hΦ
  have hΦapp : ∀ x, Φ x = ∑ c, (x c : V) := fun x => rfl
  have he_lin : ∀ c : Z, ∀ (s : Finset Z) (f : Z → V), e c (∑ c' ∈ s, f c') =
      ∑ c' ∈ s, e c (f c') := fun c s f => by
    rw [he]
    simp only
    simp only [map_sum]
    rw [Finset.sum_comm]
  have hΦinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro x hx
    rw [LinearMap.mem_ker, hΦapp] at hx
    refine (Submodule.mem_bot _).2 (funext fun c₀ => Subtype.ext ?_)
    have h := congrArg (e c₀) hx
    rw [he_lin, Finset.sum_eq_single c₀ (fun c _ hc => he_zero c₀ c (Ne.symm hc) _ (x c).2)
      (fun h => absurd (Finset.mem_univ c₀) h), he_fix c₀ _ (x c₀).2] at h
    rw [h]
    change e c₀ 0 = 0
    rw [he]
    simp only [map_zero, Finset.sum_const_zero]
  have hrange : LinearMap.range Φ = U := by
    refine le_antisymm ?_ fun u hu => ?_
    · rintro _ ⟨x, rfl⟩
      rw [hΦapp]
      exact Submodule.sum_mem _ fun c _ => (Submodule.mem_inf.1 (x c).2).1
    · exact ⟨fun c => ⟨e c u, he_F c u hu⟩, by rw [hΦapp]; exact hsum u hu⟩
  have hdim : finrank (ZMod 2) U = ∑ c : Z, finrank (ZMod 2) (F c) := by
    rw [← hrange, LinearMap.finrank_range_of_inj hΦinj, Module.finrank_pi_fintype]
  have hF1 : F 1 = U ⊓ LinearMap.ker ((y : V →ₗ[ZMod 2] V) - 1) := by
    rw [hF]
    simp only [OneMemClass.coe_one, mul_one]
  have hequal : ∀ c : Z, finrank (ZMod 2) (F c) = finrank (ZMod 2) (F 1) := by
    intro c
    obtain ⟨g, hgN, hgy⟩ := hconj c c.2
    have hmap1 : ∀ v ∈ F 1, (g : V →ₗ[ZMod 2] V) v ∈ F c := by
      intro v hv
      rw [hF1] at hv
      obtain ⟨hvU, hvk⟩ := Submodule.mem_inf.1 hv
      rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hvk
      refine Submodule.mem_inf.2 ⟨hUN g hgN v hvU, ?_⟩
      rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero, ← hgy,
        hval, hval, ← hval (g⁻¹), inv_mul_cancel, Units.val_one, Module.End.one_apply, hvk]
    have hmap2 : ∀ v ∈ F c, ((g⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) V) :
        V →ₗ[ZMod 2] V) v ∈ F 1 := by
      intro v hv
      obtain ⟨hvU, hvk⟩ := Submodule.mem_inf.1 hv
      rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero, ← hgy,
        hval, hval] at hvk
      rw [hF1]
      refine Submodule.mem_inf.2 ⟨hUN _ (inv_mem hgN) v hvU, ?_⟩
      rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
      have h := congrArg ((g⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) hvk
      rwa [← hval (g⁻¹) g, inv_mul_cancel, Units.val_one, Module.End.one_apply] at h
    have hinj : ∀ (h : LinearMap.GeneralLinearGroup (ZMod 2) V), Function.Injective
        ((h : V →ₗ[ZMod 2] V)) := fun h v w hvw => by
      have := congrArg ((h⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) hvw
      rwa [← hval, ← hval, inv_mul_cancel, Units.val_one, Module.End.one_apply,
        Module.End.one_apply] at this
    refine le_antisymm ?_ ?_
    · exact LinearMap.finrank_le_finrank_of_injective (f := ((g⁻¹ :
        LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V).restrict hmap2)
        fun v w hvw => Subtype.ext (hinj _ (congrArg Subtype.val hvw))
    · exact LinearMap.finrank_le_finrank_of_injective (f := ((g :
        LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V).restrict hmap1)
        fun v w hvw => Subtype.ext (hinj _ (congrArg Subtype.val hvw))
  rw [hdim, Finset.sum_congr rfl fun c _ => hequal c, Finset.sum_const, Finset.card_univ,
    ← Nat.card_eq_fintype_card, hZcard, smul_eq_mul, hF1]

end CFSG.Quasithin.SteinbergCD
