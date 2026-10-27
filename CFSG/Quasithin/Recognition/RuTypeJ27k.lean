module

public import CFSG.Quasithin.Recognition.RuTypeJ27j
public import CFSG.Quasithin.Recognition.RuTypeAutA6
public import CFSG.Quasithin.Recognition.RuTypeJ27f

public section

namespace CFSG.Quasithin.RuType

open CFSG.Open CFSG.Quasithin CFSG.LieType.BorelTits CFSG.QuasithinUnique

variable {G : Type} [Group G]

namespace RuDataM

variable (M : RuDataM G) [Finite G]

theorem ρ_injective
    (e : M.NP ≃* A6Models.psl29) : Function.Injective (M.ρ e) :=
  (M.ρ_dichotomy e).resolve_right fun ⟨c, h1, h2, _, h4⟩ => M.not_exists_central ⟨c, h1, h2, h4⟩

theorem ρ_bijective
    (e : M.NP ≃* A6Models.psl29) : Function.Bijective (M.ρ e) :=
  (M.ρ_injective e).bijective_of_nat_card_le (by rw [M.card_XP, A6Facts.card_autA6])

theorem ρ_NP
    (e : M.NP ≃* A6Models.psl29) (n : M.NP) :
    ((M.ρ e n : A6Models.autA6) : Equiv.Perm (Fin 10)) = (e n : Equiv.Perm (Fin 10)) := by
  have h := Unc25K1.A6Model.thetaEquiv_eq e (MulAut.conjNormal (n : M.XP))
    ⟨(e n : Equiv.Perm (Fin 10)), A6Facts.psl29_le_autA6 (e n).2⟩ (fun k => by
      have hk : MulAut.conjNormal (n : M.XP) k = n * k * n⁻¹ := Subtype.ext (by
        rw [MulAut.conjNormal_apply]
        simp)
      rw [hk, map_mul, map_mul, map_inv]
      rfl)
  show ((Unc25K1.A6Model.thetaEquiv e (MulAut.conjNormal (n : M.XP)) : A6Models.autA6) :
    Equiv.Perm (Fin 10)) = _
  rw [h]

theorem ρι_injective
    (e : M.NP ≃* A6Models.psl29) : Function.Injective ((M.ρ e).comp M.ι) :=
  (M.ρ_injective e).comp M.ι_injective

noncomputable abbrev ρI
    (e : M.NP ≃* A6Models.psl29) : Subgroup (Equiv.Perm (Fin 10)) :=
  ((M.ρ e).comp M.ι).range.map A6Models.autA6.subtype

theorem card_ρI
    (e : M.NP ≃* A6Models.psl29) : Nat.card (M.ρI e) = 720 := by
  rw [Subgroup.card_map_of_injective A6Models.autA6.subtype_injective, ← M.card_XQ]
  exact Nat.card_congr (MonoidHom.ofInjective (M.ρι_injective e)).toEquiv.symm

theorem psl29_le_ρI
    (e : M.NP ≃* A6Models.psl29) : A6Models.psl29 ≤ M.ρI e := by
  intro x hx
  set n := e.symm ⟨x, hx⟩
  obtain ⟨w, -, hw⟩ := n.2
  refine ⟨M.ρ e (M.ι w), ⟨w, rfl⟩, ?_⟩
  rw [Subgroup.coe_subtype, hw, M.ρ_NP e n]
  simp [n]

theorem mem_psl29_of_ρI
    (e : M.NP ≃* A6Models.psl29) {σ : Equiv.Perm (Fin 10)}
    (hσ : σ ∈ M.ρI e) (h2 : σ * σ = 1) : σ ∈ A6Models.psl29 := by
  obtain ⟨_, ⟨w, rfl⟩, rfl⟩ := hσ
  have hw2 : w * w = 1 := by
    apply M.ρι_injective e
    rw [map_mul, map_one]
    exact Subtype.ext h2
  have hwN : w ∈ M.NQ := M.mem_NQ_of_sq (by rw [pow_two]; exact hw2)
  have h := M.ρ_NP e ⟨M.ι w, w, hwN, rfl⟩
  simp only [MonoidHom.comp_apply, Subgroup.coe_subtype]
  rw [h]
  exact (e _).2

theorem ρI_eq
    (e : M.NP ≃* A6Models.psl29) : M.ρI e = A6Models.m10 := by
  have hle : M.ρI e ≤ A6Models.autA6 := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hs6 : ∃ σ ∈ M.ρI e, σ ∉ A6Facts.s6 := by
    by_contra hno
    push Not at hno
    have hcard : Nat.card A6Facts.s6 ≤ 720 :=
      Out21.A6.card_le_of_cosets fun x hx => (A6Facts.mem_s6_iff_exists x).mp hx
    have heq : M.ρI e = A6Facts.s6 :=
      Subgroup.eq_of_le_of_card_ge hno (by rw [M.card_ρI e]; exact hcard)
    have ht : A6Models.tFrob ∈ M.ρI e := heq ▸ AutA6.tFrob_mem_s6
    exact AutA6.tFrob_not_mem_psl29 (M.mem_psl29_of_ρI e ht AutA6.tFrob_mul_self)
  rcases Unc25K1.A6Model.classify _ hle (M.psl29_le_ρI e) hs6 with h | h | h
  · exfalso
    have hd : AutA6.dInv ∈ M.ρI e := h ▸ AutA6.dInv_mem_pgl29
    exact AutA6.dInv_not_mem_psl29 (M.mem_psl29_of_ρI e hd AutA6.dInv_mul_self)
  · exact h
  · exfalso
    have := M.card_ρI e
    rw [h, A6Facts.card_autA6] at this
    norm_num at this

theorem ρ_mk_mem_m10_iff
    (e : M.NP ≃* A6Models.psl29) (g : M.GP) :
    ((M.ρ e (QuotientGroup.mk g) : A6Models.autA6) : Equiv.Perm (Fin 10)) ∈ A6Models.m10 ↔
      (g : G) ∈ M.GB := by
  rw [← M.ρI_eq e, ← M.mk_mem_range_ι_iff]
  constructor
  · rintro ⟨_, ⟨w, rfl⟩, hw⟩
    exact ⟨w, M.ρ_injective e (Subtype.ext hw)⟩
  · rintro ⟨w, hw⟩
    exact ⟨_, ⟨w, rfl⟩, by rw [MonoidHom.comp_apply, hw]; rfl⟩

theorem exists_lift_inv
    (e : M.NP ≃* A6Models.psl29) {σ : Equiv.Perm (Fin 10)}
    (hσ : σ ∈ A6Models.autA6) (h2 : σ * σ = 1) (hm : σ ∉ A6Models.m10) :
    ∃ y : M.GP, ((M.ρ e (QuotientGroup.mk y) : A6Models.autA6) : Equiv.Perm (Fin 10)) = σ ∧
      (y : G) ∉ M.GB ∧ (y : G) * y = 1 ∧ (y : G) * M.bel * (y : G)⁻¹ = (M.bel : G)⁻¹ := by
  obtain ⟨x, hx⟩ := (M.ρ_bijective e).2 ⟨σ, hσ⟩
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
  have hyB : (y : G) ∉ M.GB := fun h => hm (by
    have := (M.ρ_mk_mem_m10_iff e y).mpr h
    rw [hx] at this
    exact this)
  have hinv := M.conj_bel_of_not_mem_GB y.2 hyB
  refine ⟨y, by rw [hx], hyB, M.sq_eq_one_of_inv hinv ?_, hinv⟩
  have h1 : (QuotientGroup.mk (y * y) : M.XP) = 1 := by
    apply M.ρ_injective e
    rw [QuotientGroup.mk_mul, map_mul, hx, map_one]
    exact Subtype.ext h2
  rw [QuotientGroup.eq_one_iff] at h1
  exact Subgroup.mem_subgroupOf.mp h1

theorem conj_inv_of_mem_GP {x y : G} (hx : x ∈ M.GP) (hy : y ∈ M.GP) (hyB : y ∉ M.GB) :
    (x * y * x⁻¹) * M.bel * (x * y * x⁻¹)⁻¹ = (M.bel : G)⁻¹ := by
  refine M.conj_bel_of_not_mem_GB (mul_mem (mul_mem hx hy) (inv_mem hx)) fun h => hyB ?_
  have := M.conj_mem_GB (inv_mem hx) h
  simpa [mul_assoc] using this

theorem isConj_of_ρ_conj
    (e : M.NP ≃* A6Models.psl29) {y y' : M.GP} (hyB : (y : G) ∉ M.GB)
    {m : Equiv.Perm (Fin 10)} (hm : m ∈ A6Models.m10)
    (h : m * ((M.ρ e (QuotientGroup.mk y) : A6Models.autA6) : Equiv.Perm (Fin 10)) * m⁻¹ =
      ((M.ρ e (QuotientGroup.mk y') : A6Models.autA6) : Equiv.Perm (Fin 10))) :
    ∃ g ∈ M.GB, g * y * g⁻¹ = y' := by
  rw [← M.ρI_eq e] at hm
  obtain ⟨_, ⟨w, rfl⟩, rfl⟩ := hm
  obtain ⟨g0, rfl⟩ := QuotientGroup.mk_surjective w
  set g := Subgroup.inclusion M.GB_le_GP g0
  have hq : (QuotientGroup.mk (g * y * g⁻¹) : M.XP) = QuotientGroup.mk y' := by
    apply M.ρ_injective e
    apply Subtype.ext
    rw [← h, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, map_mul, map_mul,
      map_inv]
    rfl
  have hb := M.mk_eq_mk_iff_XP.mp hq
  set b := ((g * y * g⁻¹ : M.GP) : G)⁻¹ * y' with hbdef
  have hinv : ((g : G) * y * (g : G)⁻¹) * M.bel * ((g : G) * y * (g : G)⁻¹)⁻¹ =
      (M.bel : G)⁻¹ := M.conj_inv_of_mem_GP g.2 y.2 hyB
  have e1 := M.mul_eq_conj_of_inv hinv hb
  have hy' : (y' : G) = ((g : G) * y * (g : G)⁻¹) * b := by
    rw [hbdef]; simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group
  refine ⟨b * g, mul_mem (M.B_le_GB hb) g0.2, ?_⟩
  rw [hy', e1]
  group

theorem isConj_H_of_ρ_conj
    (e : M.NP ≃* A6Models.psl29) {y y' : M.GP} (hyB : (y : G) ∉ M.GB)
    {p : Equiv.Perm (Fin 10)} (hp : p ∈ A6Models.autA6)
    (hpz : p * ((M.ρ e (QuotientGroup.mk (⟨M.z, M.GB_le_GP (M.TB_le_GB M.z_mem_TB)⟩ : M.GP)) :
      A6Models.autA6) : Equiv.Perm (Fin 10)) =
      ((M.ρ e (QuotientGroup.mk (⟨M.z, M.GB_le_GP (M.TB_le_GB M.z_mem_TB)⟩ : M.GP)) :
        A6Models.autA6) : Equiv.Perm (Fin 10)) * p)
    (h : p * ((M.ρ e (QuotientGroup.mk y) : A6Models.autA6) : Equiv.Perm (Fin 10)) * p⁻¹ =
      ((M.ρ e (QuotientGroup.mk y') : A6Models.autA6) : Equiv.Perm (Fin 10))) :
    ∃ h ∈ ruH M.T, h * y * h⁻¹ = y' := by
  set z' : M.GP := ⟨M.z, M.GB_le_GP (M.TB_le_GB M.z_mem_TB)⟩
  obtain ⟨x, hx⟩ := (M.ρ_bijective e).2 ⟨p, hp⟩
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  have hgz : (QuotientGroup.mk (g * z') : M.XP) = QuotientGroup.mk (z' * g) := by
    apply M.ρ_injective e
    apply Subtype.ext
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, map_mul, map_mul, hx]
    exact hpz
  have hb := M.mk_eq_mk_iff_XP.mp hgz
  set b := ((g * z' : M.GP) : G)⁻¹ * (z' * g : M.GP) with hbdef
  have hbz : M.z * b = b * M.z :=
    (Subgroup.mem_centralizer_iff.mp (M.TB_le_GB M.z_mem_TB) b hb).symm
  have hgzg : (g : G)⁻¹ * M.z * g = M.z * b := by
    rw [hbdef]
    show _ = M.z * (((g : G) * M.z)⁻¹ * (M.z * (g : G)))
    group
  have hb2 : b * b = 1 := by
    have h1 : ((g : G)⁻¹ * M.z * g) * ((g : G)⁻¹ * M.z * g) = 1 := by
      calc ((g : G)⁻¹ * M.z * g) * ((g : G)⁻¹ * M.z * g) = (g : G)⁻¹ * (M.z * M.z) * g := by
            group
        _ = 1 := by rw [M.z_mul_self]; group
    rw [hgzg] at h1
    calc b * b = (M.z * b) * (M.z * b) := by
          rw [show (M.z * b) * (M.z * b) = (M.z * M.z) * (b * b) by
            rw [mul_assoc, ← mul_assoc b, ← hbz]; group, M.z_mul_self, one_mul]
      _ = 1 := h1
  have hb1 : b = 1 := by
    have h3 := M.pow_three_of_mem_B hb
    calc b = b ^ 3 * (b * b)⁻¹ := by group
      _ = 1 := by rw [h3, hb2]; group
  have hgH : (g : G) ∈ ruH M.T := by
    rw [M.mem_H_iff_comm]
    rw [hb1, mul_one] at hgzg
    calc M.z * g = g * ((g : G)⁻¹ * M.z * g) := by group
      _ = g * M.z := by rw [hgzg]
  have hq : (QuotientGroup.mk (g * y * g⁻¹) : M.XP) = QuotientGroup.mk y' := by
    apply M.ρ_injective e
    apply Subtype.ext
    rw [← h, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, map_mul, map_mul,
      map_inv, hx]
    rfl
  have hb' := M.mk_eq_mk_iff_XP.mp hq
  set b' := ((g * y * g⁻¹ : M.GP) : G)⁻¹ * y' with hb'def
  have hinv : ((g : G) * y * (g : G)⁻¹) * M.bel * ((g : G) * y * (g : G)⁻¹)⁻¹ =
      (M.bel : G)⁻¹ := M.conj_inv_of_mem_GP g.2 y.2 hyB
  have e1 := M.mul_eq_conj_of_inv hinv hb'
  have hy' : (y' : G) = ((g : G) * y * (g : G)⁻¹) * b' := by
    rw [hb'def]; simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group
  refine ⟨b' * g, mul_mem (M.B_le_H hb') hgH, ?_⟩
  rw [hy', e1]
  group

theorem exists_five_H : ∃ b ∈ ruH M.T, orderOf b = 5 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ruH M.T) 5
    (by rw [M.toRuData.card_H]; norm_num)
  exact ⟨x, x.2, by rw [← hx, Subgroup.orderOf_coe]⟩

theorem not_isConj_z_of_comm_five
    {d y : G} (hy : y ∈ M.GB) (hy5 : orderOf y = 5)
    (hc : d * y = y * d) : ¬ IsConj M.z d := by
  intro hz
  obtain ⟨g, rfl⟩ := isConj_iff.mp hz
  have hyH : g⁻¹ * y * g ∈ ruH M.T := by
    rw [M.mem_H_iff_comm]
    calc M.z * (g⁻¹ * y * g) = g⁻¹ * ((g * M.z * g⁻¹) * y) * g := by group
      _ = g⁻¹ * (y * (g * M.z * g⁻¹)) * g := by rw [hc]
      _ = g⁻¹ * y * g * M.z := by group
  have hy5' : orderOf (g⁻¹ * y * g) = 5 := by
    rw [show g⁻¹ * y * g = g⁻¹ * y * g⁻¹⁻¹ by rw [inv_inv], orderOf_conj_eq]
    exact hy5
  obtain ⟨b, hbH, hb5⟩ := M.exists_five_H
  obtain ⟨c, -, hc⟩ := M.exists_conj_five hbH hyH hb5 hy5'
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hc
  apply lemma_J27_6 (M := M) hbH hb5 (g * c)
  have e : g * c * b * (g * c)⁻¹ = y ^ k := by
    calc g * c * b * (g * c)⁻¹ = g * (c * b * c⁻¹) * g⁻¹ := by group
      _ = g * (g⁻¹ * y * g) ^ k * g⁻¹ := by rw [← hk]
      _ = y ^ k := by
        rw [show g⁻¹ * y * g = g⁻¹ * y * g⁻¹⁻¹ by rw [inv_inv], conj_zpow]
        group
  rw [e]
  exact zpow_mem hy k

theorem exists_comm_five_of_ρ
    (e : M.NP ≃* A6Models.psl29) (d : M.GP)
    {x5 : Equiv.Perm (Fin 10)} (hx5 : x5 ∈ A6Models.psl29) (hx55 : x5 ^ 5 = 1) (hx51 : x5 ≠ 1)
    (hc : ((M.ρ e (QuotientGroup.mk d) : A6Models.autA6) : Equiv.Perm (Fin 10)) * x5 =
      x5 * ((M.ρ e (QuotientGroup.mk d) : A6Models.autA6) : Equiv.Perm (Fin 10))) :
    ∃ y ∈ M.GB, orderOf y = 5 ∧ (d : G) * y = y * d ∧
      ∀ hy : y ∈ M.GP, ((M.ρ e (QuotientGroup.mk (⟨y, hy⟩ : M.GP)) : A6Models.autA6) :
        Equiv.Perm (Fin 10)) = x5 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  set n := e.symm ⟨x5, hx5⟩
  have hn := M.ρ_NP e n
  have hen : (e n : Equiv.Perm (Fin 10)) = x5 := by simp [n]
  obtain ⟨w, hw, hwn⟩ := n.2
  obtain ⟨x0, hx0, rfl⟩ := hw
  set x : M.GP := Subgroup.inclusion M.GB_le_GP x0
  have hxn : (QuotientGroup.mk x : M.XP) = n := by rw [← hwn]; rfl
  have hdx : (QuotientGroup.mk (d * x) : M.XP) = QuotientGroup.mk (x * d) := by
    apply M.ρ_injective e
    apply Subtype.ext
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, map_mul, map_mul, hxn]
    simp only [Subgroup.coe_mul]
    rw [hn, hen]
    exact hc
  have hx5q : (QuotientGroup.mk (x ^ 5) : M.XP) = 1 := by
    apply M.ρ_injective e
    apply Subtype.ext
    rw [QuotientGroup.mk_pow, map_pow, hxn, map_one]
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [hn, hen, hx55]
  have hx5B : (x : G) ^ 5 ∈ M.B := by
    rw [QuotientGroup.eq_one_iff] at hx5q
    simpa using Subgroup.mem_subgroupOf.mp hx5q
  have hx1 : (x : G) ∉ M.B := by
    intro hB
    apply hx51
    rw [← hen, ← hn, ← hxn]
    have : (QuotientGroup.mk x : M.XP) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hB)
    rw [this, map_one]
    rfl
  set y : G := (x : G) ^ 6 with hydef
  have hx15 : (x : G) ^ 15 = 1 := by
    rw [show 15 = 5 * 3 by rfl, pow_mul, M.pow_three_of_mem_B hx5B]
  have hy5 : y ^ 5 = 1 := by
    rw [hydef, ← pow_mul, show 6 * 5 = 15 * 2 by rfl, pow_mul, hx15, one_pow]
  have hyx : (x : G)⁻¹ * y ∈ M.B := by
    rw [hydef, show (x : G) ^ 6 = x * x ^ 5 by rw [← pow_succ']]
    simpa using hx5B
  have hy1 : y ≠ 1 := by
    intro h1
    apply hx1
    have := hyx
    rw [h1, mul_one] at this
    simpa using inv_mem this
  have hyGB : y ∈ M.GB := pow_mem x0.2 _
  refine ⟨y, hyGB, orderOf_eq_prime hy5 hy1, ?_, fun hy => ?_⟩
  swap
  · have hyx6 : (⟨y, hy⟩ : M.GP) = x ^ 6 := Subtype.ext (by
      show y = ((x ^ 6 : M.GP) : G)
      rw [SubgroupClass.coe_pow])
    rw [hyx6, QuotientGroup.mk_pow, show 6 = 5 + 1 by rfl, pow_succ, ← QuotientGroup.mk_pow,
      hx5q, one_mul, hxn, hn, hen]
  have hdq : (QuotientGroup.mk (d * x ^ 6) : M.XP) = QuotientGroup.mk (x ^ 6 * d) := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_pow]
    have hc' : (QuotientGroup.mk d : M.XP) * QuotientGroup.mk x =
        QuotientGroup.mk x * QuotientGroup.mk d := by
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hdx]
    exact (Commute.pow_right hc' 6).eq
  have hb := M.mk_eq_mk_iff_XP.mp hdq
  set b := ((d * x ^ 6 : M.GP) : G)⁻¹ * (x ^ 6 * d : M.GP) with hbdef
  have hbx : y * d = d * y * b := by
    rw [hbdef, hydef]
    simp only [Subgroup.coe_mul, SubgroupClass.coe_pow]
    group
  have hyb : Commute y b := (Subgroup.mem_centralizer_iff.mp hyGB b hb).symm
  have h1 : (d : G)⁻¹ * y * d = y * b := by
    calc (d : G)⁻¹ * y * d = (d : G)⁻¹ * (y * d) := by group
      _ = (d : G)⁻¹ * (d * y * b) := by rw [hbx]
      _ = y * b := by group
  have h2 : ((d : G)⁻¹ * y * d) ^ 5 = 1 := by
    rw [show (d : G)⁻¹ * y * d = (d : G)⁻¹ * y * (d : G)⁻¹⁻¹ by rw [inv_inv], conj_pow, hy5]
    group
  rw [h1, hyb.mul_pow, hy5, one_mul] at h2
  have h3 := M.pow_three_of_mem_B hb
  have hb1 : b = 1 := by
    calc b = (b ^ 3) ^ 2 * (b ^ 5)⁻¹ := by group
      _ = 1 := by rw [h2, h3]; group
  rw [hb1, mul_one] at hbx
  exact hbx.symm

end RuDataM

end CFSG.Quasithin.RuType
