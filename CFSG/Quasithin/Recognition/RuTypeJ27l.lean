module

public import CFSG.Quasithin.Recognition.RuTypeJ27k

public section

namespace CFSG.Quasithin.RuType

open CFSG.Open CFSG.Quasithin CFSG.LieType.BorelTits CFSG.QuasithinUnique

variable {G : Type} [Group G]

namespace RuDataM

variable (M : RuDataM G) [Finite G]

noncomputable abbrev zP : M.GP := ⟨M.z, M.GB_le_GP (M.TB_le_GB M.z_mem_TB)⟩

theorem exists_conj_le_T {P : Subgroup G} (hP : IsPGroup 2 P) :
    ∃ g : G, ∀ x ∈ P, g * x * g⁻¹ ∈ (M.T : Subgroup G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨PS, hPS⟩ := hP.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq G PS M.T
  refine ⟨c, fun x hx => ?_⟩
  rw [← hc, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
  exact ⟨x, hPS hx, by simp [MulAut.conj_apply]⟩

theorem exists_conj_mem_H {x : G} (hx2 : x ^ 2 = 1) : ∃ g : G, g * x * g⁻¹ ∈ ruH M.T := by
  have hP : IsPGroup 2 (Subgroup.zpowers x) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rw [IsPGroup.iff_card, Nat.card_zpowers]
    have h := orderOf_dvd_of_pow_eq_one hx2
    rcases (Nat.dvd_prime Nat.prime_two).mp h with h | h
    · exact ⟨0, by rw [h, pow_zero]⟩
    · exact ⟨1, by rw [h, pow_one]⟩
  obtain ⟨g, hg⟩ := M.exists_conj_le_T hP
  exact ⟨g, M.toRuData.T_le_H (hg x (Subgroup.mem_zpowers x))⟩

theorem outer_inv_classes
    (e : M.NP ≃* A6Models.psl29) (y : M.GP) (hyB : (y : G) ∉ M.GB)
    (hy2 : (y : G) * y = 1) :
    (((M.ρ e (QuotientGroup.mk y) : A6Models.autA6) : Equiv.Perm (Fin 10)) ∈ A6Facts.s6 →
        IsConj M.z y) ∧
      (((M.ρ e (QuotientGroup.mk y) : A6Models.autA6) : Equiv.Perm (Fin 10)) ∉ A6Facts.s6 →
        ∀ s ∈ M.S0, s ≠ 1 → IsConj s y) := by
  have hclass : ∀ y : M.GP, (y : G) ∉ M.GB → (y : G) * y = 1 →
      ∀ σ ∈ A6Models.autA6, σ * σ = 1 → σ ∉ A6Models.m10 →
      ∀ y' : M.GP, ((M.ρ e (QuotientGroup.mk y') : A6Models.autA6) : Equiv.Perm (Fin 10)) = σ →
        (∃ m ∈ A6Models.m10, m * ((M.ρ e (QuotientGroup.mk y) : A6Models.autA6) :
          Equiv.Perm (Fin 10)) * m⁻¹ = σ) → IsConj (y : G) y' := by
    intro y hyB _ σ _ _ _ y' hy' ⟨m, hm, hmσ⟩
    obtain ⟨g, -, hg⟩ := M.isConj_of_ρ_conj e hyB hm (hmσ.trans hy'.symm)
    exact isConj_iff.mpr ⟨g, hg⟩
  have hρinv : ∀ y : M.GP, (y : G) ∉ M.GB → (y : G) * y = 1 →
      ((M.ρ e (QuotientGroup.mk y) : A6Models.autA6) : Equiv.Perm (Fin 10)) ∈ A6Models.autA6 ∧
      ((M.ρ e (QuotientGroup.mk y) : A6Models.autA6) : Equiv.Perm (Fin 10)) *
        ((M.ρ e (QuotientGroup.mk y) : A6Models.autA6) : Equiv.Perm (Fin 10)) = 1 ∧
      ((M.ρ e (QuotientGroup.mk y) : A6Models.autA6) : Equiv.Perm (Fin 10)) ∉ A6Models.m10 := by
    intro y hyB hy2
    refine ⟨(M.ρ e _).2, ?_, fun h => hyB ((M.ρ_mk_mem_m10_iff e y).mp h)⟩
    have : y * y = 1 := Subtype.ext hy2
    rw [← Subgroup.coe_mul, ← map_mul, ← QuotientGroup.mk_mul, this, QuotientGroup.mk_one,
      map_one]
    rfl
  obtain ⟨f, hf, hfB, hf2, -⟩ := M.exists_lift_inv e Out21.A6.tFrob_mem_autA6
    AutA6.tFrob_mul_self AutA6.tFrob_not_mem_m10
  obtain ⟨d, hd, hdB, hd2, -⟩ := M.exists_lift_inv e AutA6.dInv_mem_autA6
    AutA6.dInv_mul_self AutA6.dInv_not_mem_m10
  have hfd : ∀ y : M.GP, (y : G) ∉ M.GB → (y : G) * y = 1 →
      (((M.ρ e (QuotientGroup.mk y) : A6Models.autA6) : Equiv.Perm (Fin 10)) ∈ A6Facts.s6 →
        IsConj (y : G) f) ∧
      (((M.ρ e (QuotientGroup.mk y) : A6Models.autA6) : Equiv.Perm (Fin 10)) ∉ A6Facts.s6 →
        IsConj (y : G) d) := by
    intro y hyB hy2
    obtain ⟨hA, h2, hm⟩ := hρinv y hyB hy2
    refine ⟨fun hs => ?_, fun hs => ?_⟩
    · exact hclass y hyB hy2 _ Out21.A6.tFrob_mem_autA6 AutA6.tFrob_mul_self
        AutA6.tFrob_not_mem_m10 f hf (AutA6.out_classes_s6 hA h2 hm hs)
    · exact hclass y hyB hy2 _ AutA6.dInv_mem_autA6 AutA6.dInv_mul_self
        AutA6.dInv_not_mem_m10 d hd (AutA6.out_classes_d hA h2 hm hs)
  have hx5 : A6Models.tAdd * A6Models.tSq * A6Models.tInv ∈ A6Models.psl29 :=
    mul_mem (mul_mem Out21.A6.tAdd_mem_psl29 Out21.A6.tSq_mem_psl29) Out21.A6.tInv_mem_psl29
  obtain ⟨y5, hy5GB, hy5o, hy5c, -⟩ := M.exists_comm_five_of_ρ e d hx5 x5_pow_five x5_ne_one
    (by rw [hd]; exact AutA6.dInv_comm)
  have hdz : ¬ IsConj M.z d := M.not_isConj_z_of_comm_five hy5GB hy5o hy5c
  obtain ⟨hjH, hjK, hj2, -, hjz⟩ := M.jel_spec
  have hjQ : M.jel ∉ ruQ M.T := fun h => hjK (M.Q_le_K h)
  obtain ⟨h0, hh0, hj0⟩ := M.exists_conj_inv_bel hjH hj2 hjQ
  set j0 := h0 * M.jel * h0⁻¹ with hj0def
  have hj0GP : j0 ∈ M.GP := M.mem_GP_of_inv hj0
  have hj0B : j0 ∉ M.GB := fun hm => M.bel_ne_inv (by rw [← hj0, M.mem_GB_iff_conj.mp hm])
  have hj02 : j0 * j0 = 1 := by
    rw [hj0def]
    calc h0 * M.jel * h0⁻¹ * (h0 * M.jel * h0⁻¹) = h0 * (M.jel * M.jel) * h0⁻¹ := by group
      _ = 1 := by rw [M.jel_mul_self]; group
  have hj0z : IsConj M.z j0 := hjz.trans (isConj_iff.mpr ⟨h0, rfl⟩)
  have hfz : IsConj M.z f := by
    obtain ⟨h1, h2⟩ := hfd ⟨j0, hj0GP⟩ hj0B hj02
    by_cases hs : ((M.ρ e (QuotientGroup.mk (⟨j0, hj0GP⟩ : M.GP)) : A6Models.autA6) :
        Equiv.Perm (Fin 10)) ∈ A6Facts.s6
    · exact hj0z.trans (h1 hs)
    · exact absurd (hj0z.trans (h2 hs)) hdz
  have hds : ∀ s ∈ M.S0, s ≠ 1 → IsConj s d := by
    intro s hs hs1
    have hsH := M.S0_le_H hs
    have hs2 : s ^ 2 = 1 := M.S0_elem.2 _ hs
    have hsQ : s ∉ ruQ M.T := fun h => hs1 (M.eq_one_of_mem_S0_Q hs h)
    obtain ⟨h, -, hs0⟩ := M.exists_conj_inv_bel hsH hs2 hsQ
    set s0 := h * s * h⁻¹ with hs0def
    have hs0GP : s0 ∈ M.GP := M.mem_GP_of_inv hs0
    have hs0B : s0 ∉ M.GB := fun hm => M.bel_ne_inv (by rw [← hs0, M.mem_GB_iff_conj.mp hm])
    have hs02 : s0 * s0 = 1 := by
      rw [hs0def]
      calc h * s * h⁻¹ * (h * s * h⁻¹) = h * (s * s) * h⁻¹ := by group
        _ = 1 := by rw [← pow_two, hs2]; group
    have hss0 : IsConj s s0 := isConj_iff.mpr ⟨h, rfl⟩
    have hsz : ¬ IsConj M.z s := fun hz => by
      obtain ⟨g, hg⟩ := isConj_iff.mp hz
      exact M.lemma_J23_2 g (hg ▸ hs)
    obtain ⟨h1, h2⟩ := hfd ⟨s0, hs0GP⟩ hs0B hs02
    by_cases hS : ((M.ρ e (QuotientGroup.mk (⟨s0, hs0GP⟩ : M.GP)) : A6Models.autA6) :
        Equiv.Perm (Fin 10)) ∈ A6Facts.s6
    · exact absurd (hfz.trans ((hss0.trans (h1 hS)).symm)) hsz
    · exact hss0.trans (h2 hS)
  obtain ⟨h1, h2⟩ := hfd y hyB hy2
  refine ⟨fun hs => hfz.trans (h1 hs).symm, fun hs s hs0 hs1 => (hds s hs0 hs1).trans (h2 hs).symm⟩

theorem lemma_J27_4
    {s : G} (hs : s ∈ M.S0) (hs1 : s ≠ 1) :
    ¬ IsConj M.z s ∧ ∀ x : G, x ^ 2 = 1 → x ≠ 1 → IsConj M.z x ∨ IsConj s x := by
  refine ⟨fun hz => ?_, fun x hx2 hx1 => ?_⟩
  · obtain ⟨g, hg⟩ := isConj_iff.mp hz
    exact M.lemma_J23_2 g (hg ▸ hs)
  obtain ⟨e⟩ := M.nonempty_NP_psl29
  obtain ⟨g, hgH⟩ := M.exists_conj_mem_H hx2
  set x' := g * x * g⁻¹ with hx'def
  have hxx' : IsConj x x' := isConj_iff.mpr ⟨g, rfl⟩
  have hx'2 : x' ^ 2 = 1 := by rw [hx'def, conj_pow, hx2]; group
  have hx'1 : x' ≠ 1 := fun h => hx1 (by
    have : x = g⁻¹ * x' * g := by rw [hx'def]; group
    rw [this, h]; group)
  by_cases hQ : x' ∈ ruQ M.T
  · exact Or.inl ((M.lemma_J26.2.2.2.2.1 x' hQ hx'2 hx'1).trans hxx'.symm)
  obtain ⟨h, -, hinv⟩ := M.exists_conj_inv_bel hgH hx'2 hQ
  set y := h * x' * h⁻¹ with hydef
  have hyGP : y ∈ M.GP := M.mem_GP_of_inv hinv
  have hyB : y ∉ M.GB := fun hm => M.bel_ne_inv (by rw [← hinv, M.mem_GB_iff_conj.mp hm])
  have hy2 : y * y = 1 := by
    rw [hydef]
    calc h * x' * h⁻¹ * (h * x' * h⁻¹) = h * (x' * x') * h⁻¹ := by group
      _ = 1 := by rw [← pow_two, hx'2]; group
  have hxy : IsConj x y := hxx'.trans (isConj_iff.mpr ⟨h, rfl⟩)
  obtain ⟨h1, h2⟩ := M.outer_inv_classes e ⟨y, hyGP⟩ hyB hy2
  by_cases hS : ((M.ρ e (QuotientGroup.mk (⟨y, hyGP⟩ : M.GP)) : A6Models.autA6) :
      Equiv.Perm (Fin 10)) ∈ A6Facts.s6
  · exact Or.inl ((h1 hS).trans hxy.symm)
  · exact Or.inr ((h2 hS s hs hs1).trans hxy.symm)

theorem ρ_mem_psl29_of_GB
    (e : M.NP ≃* A6Models.psl29) (y : M.GP) (hyB : (y : G) ∈ M.GB)
    (hy2 : (y : G) * y = 1) :
    ((M.ρ e (QuotientGroup.mk y) : A6Models.autA6) : Equiv.Perm (Fin 10)) ∈ A6Models.psl29 := by
  have hmem : ((M.ρ e (QuotientGroup.mk y) : A6Models.autA6) : Equiv.Perm (Fin 10)) ∈
      M.ρI e := by
    rw [M.ρI_eq e]
    exact (M.ρ_mk_mem_m10_iff e y).mpr hyB
  refine M.mem_psl29_of_ρI e hmem ?_
  have : y * y = 1 := Subtype.ext hy2
  rw [← Subgroup.coe_mul, ← map_mul, ← QuotientGroup.mk_mul, this, QuotientGroup.mk_one, map_one]
  rfl

theorem ρ_zP_props
    (e : M.NP ≃* A6Models.psl29) :
    ((M.ρ e (QuotientGroup.mk M.zP) : A6Models.autA6) : Equiv.Perm (Fin 10)) ∈
        A6Models.psl29 ∧
      ((M.ρ e (QuotientGroup.mk M.zP) : A6Models.autA6) : Equiv.Perm (Fin 10)) *
        ((M.ρ e (QuotientGroup.mk M.zP) : A6Models.autA6) : Equiv.Perm (Fin 10)) = 1 ∧
      ((M.ρ e (QuotientGroup.mk M.zP) : A6Models.autA6) : Equiv.Perm (Fin 10)) ≠ 1 := by
  refine ⟨M.ρ_mem_psl29_of_GB e M.zP (M.TB_le_GB M.z_mem_TB) M.z_mul_self, ?_, ?_⟩
  · have : M.zP * M.zP = 1 := Subtype.ext M.z_mul_self
    rw [← Subgroup.coe_mul, ← map_mul, ← QuotientGroup.mk_mul, this, QuotientGroup.mk_one,
      map_one]
    rfl
  · intro h
    apply M.z_not_mem_B
    have h1 : (QuotientGroup.mk M.zP : M.XP) = 1 := by
      apply M.ρ_injective e
      rw [map_one]
      exact Subtype.ext h
    rw [QuotientGroup.eq_one_iff] at h1
    exact Subgroup.mem_subgroupOf.mp h1

theorem ρ_comm_zP
    (e : M.NP ≃* A6Models.psl29) (y : M.GP) (hyH : (y : G) ∈ ruH M.T) :
    ((M.ρ e (QuotientGroup.mk y) : A6Models.autA6) : Equiv.Perm (Fin 10)) *
        ((M.ρ e (QuotientGroup.mk M.zP) : A6Models.autA6) : Equiv.Perm (Fin 10)) =
      ((M.ρ e (QuotientGroup.mk M.zP) : A6Models.autA6) : Equiv.Perm (Fin 10)) *
        ((M.ρ e (QuotientGroup.mk y) : A6Models.autA6) : Equiv.Perm (Fin 10)) := by
  have hc : y * M.zP = M.zP * y := Subtype.ext (M.mem_H_iff_comm.mp hyH).symm
  rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul, ← QuotientGroup.mk_mul,
    ← QuotientGroup.mk_mul, hc]

theorem exists_conj_diag
    (e : M.NP ≃* A6Models.psl29) {x : G} (hxH : x ∈ ruH M.T)
    (hx2 : x ^ 2 = 1) (hxQ : x ∉ ruQ M.T) (hxz : ¬ IsConj M.z x) :
    ∃ h ∈ ruH M.T, ∃ hy : h * x * h⁻¹ ∈ M.GP, h * x * h⁻¹ ∉ M.GB ∧
      (h * x * h⁻¹) * (h * x * h⁻¹) = 1 ∧
      ((M.ρ e (QuotientGroup.mk (⟨h * x * h⁻¹, hy⟩ : M.GP)) : A6Models.autA6) :
        Equiv.Perm (Fin 10)) ∉ A6Facts.s6 := by
  obtain ⟨h, hh, hinv⟩ := M.exists_conj_inv_bel hxH hx2 hxQ
  have hyGP : h * x * h⁻¹ ∈ M.GP := M.mem_GP_of_inv hinv
  have hyB : h * x * h⁻¹ ∉ M.GB := fun hm => M.bel_ne_inv (by
    rw [← hinv, M.mem_GB_iff_conj.mp hm])
  have hy2 : (h * x * h⁻¹) * (h * x * h⁻¹) = 1 := by
    calc (h * x * h⁻¹) * (h * x * h⁻¹) = h * (x * x) * h⁻¹ := by group
      _ = 1 := by rw [← pow_two, hx2]; group
  refine ⟨h, hh, hyGP, hyB, hy2, fun hs => hxz ?_⟩
  have := (M.outer_inv_classes e ⟨_, hyGP⟩ hyB hy2).1 hs
  exact this.trans (isConj_iff.mpr ⟨h⁻¹, by group⟩)

theorem lemma_J27_8
    {s : G} (hs : s ∈ M.S0) (hs1 : s ≠ 1) {x : G} (hxH : x ∈ ruH M.T)
    (hsx : IsConj s x) : (∃ h ∈ ruH M.T, h * s * h⁻¹ = x) ∧ x ∈ M.K ∧ x ∉ ruQ M.T := by
  obtain ⟨e⟩ := M.nonempty_NP_psl29
  have hsz : ¬ IsConj M.z s := (M.lemma_J27_4 hs hs1).1
  have hxz : ¬ IsConj M.z x := fun h => hsz (h.trans hsx.symm)
  have hs2 : s ^ 2 = 1 := M.S0_elem.2 _ hs
  obtain ⟨g, hg⟩ := isConj_iff.mp hsx
  have hx2 : x ^ 2 = 1 := by rw [← hg, conj_pow, hs2]; group
  have hx1 : x ≠ 1 := fun h => hs1 (by
    have : s = g⁻¹ * x * g := by rw [← hg]; group
    rw [this, h]; group)
  have hxQ : x ∉ ruQ M.T := fun h => hxz (M.lemma_J26.2.2.2.2.1 x h hx2 hx1)
  have hxK : x ∈ M.K := by
    by_contra hK
    exact hxz (M.lemma_J26.2.2.1 x hxH hK hx2)
  refine ⟨?_, hxK, hxQ⟩
  have hsH := M.S0_le_H hs
  have hsQ : s ∉ ruQ M.T := fun h => hs1 (M.eq_one_of_mem_S0_Q hs h)
  obtain ⟨h1, hh1, hy1, hy1B, hy12, hy1s⟩ := M.exists_conj_diag e hxH hx2 hxQ hxz
  obtain ⟨h2, hh2, hy2, hy2B, hy22, hy2s⟩ := M.exists_conj_diag e hsH hs2 hsQ hsz
  obtain ⟨hτ, hτ2, hτ1⟩ := M.ρ_zP_props e
  have hA : ∀ y : M.GP, (y : G) ∉ M.GB → (y : G) * y = 1 →
      ((M.ρ e (QuotientGroup.mk y) : A6Models.autA6) : Equiv.Perm (Fin 10)) *
        ((M.ρ e (QuotientGroup.mk y) : A6Models.autA6) : Equiv.Perm (Fin 10)) = 1 ∧
      ((M.ρ e (QuotientGroup.mk y) : A6Models.autA6) : Equiv.Perm (Fin 10)) ∉ A6Models.m10 := by
    intro y hyB hy2
    refine ⟨?_, fun h => hyB ((M.ρ_mk_mem_m10_iff e y).mp h)⟩
    have : y * y = 1 := Subtype.ext hy2
    rw [← Subgroup.coe_mul, ← map_mul, ← QuotientGroup.mk_mul, this, QuotientGroup.mk_one,
      map_one]
    rfl
  obtain ⟨a1, a2⟩ := hA ⟨_, hy2⟩ hy2B hy22
  obtain ⟨b1, b2⟩ := hA ⟨_, hy1⟩ hy1B hy12
  have hyH : ∀ {h y : G}, h ∈ ruH M.T → y ∈ ruH M.T → h * y * h⁻¹ ∈ ruH M.T :=
    fun hh hy => mul_mem (mul_mem hh hy) (inv_mem hh)
  obtain ⟨p, hp, hpτ, hpσ⟩ := AutA6.cent_trans hτ hτ2 hτ1 (M.ρ e _).2 (M.ρ e _).2
    (M.ρ_comm_zP e ⟨_, hy2⟩ (hyH hh2 hsH)) (M.ρ_comm_zP e ⟨_, hy1⟩ (hyH hh1 hxH)) a1 b1 a2 b2
    hy2s hy1s
  obtain ⟨k, hk, hkk⟩ := M.isConj_H_of_ρ_conj e hy2B hp hpτ hpσ
  refine ⟨h1⁻¹ * k * h2, mul_mem (mul_mem (inv_mem hh1) hk) hh2, ?_⟩
  have e1 : k * (h2 * s * h2⁻¹) * k⁻¹ = h1 * x * h1⁻¹ := hkk
  calc h1⁻¹ * k * h2 * s * (h1⁻¹ * k * h2)⁻¹ = h1⁻¹ * (k * (h2 * s * h2⁻¹) * k⁻¹) * h1 := by
        group
    _ = x := by rw [e1]; group

theorem exists_centralizer_conj_z
    {s : G} (hs : s ∈ M.S0) (hs1 : s ≠ 1) {w : G}
    (hw : IsConj M.z w) (hws : w * s = s * w) : ∃ k : G, k * s = s * k ∧ k * M.z * k⁻¹ = w := by
  obtain ⟨g, rfl⟩ := isConj_iff.mp hw
  have hH : g⁻¹ * s * g ∈ ruH M.T := by
    rw [M.mem_H_iff_comm]
    calc M.z * (g⁻¹ * s * g) = g⁻¹ * ((g * M.z * g⁻¹) * s) * g := by group
      _ = g⁻¹ * (s * (g * M.z * g⁻¹)) * g := by rw [hws]
      _ = g⁻¹ * s * g * M.z := by group
  obtain ⟨⟨h, hh, hhs⟩, -, -⟩ := M.lemma_J27_8 hs hs1 hH (isConj_iff.mpr ⟨g⁻¹, by group⟩)
  have hzh : M.z * h = h * M.z := M.mem_H_iff_comm.mp hh
  refine ⟨g * h, ?_, ?_⟩
  · calc g * h * s = g * (h * s * h⁻¹) * h := by group
      _ = g * (g⁻¹ * s * g) * h := by rw [hhs]
      _ = s * (g * h) := by group
  · calc g * h * M.z * (g * h)⁻¹ = g * (h * M.z * h⁻¹) * g⁻¹ := by group
      _ = g * M.z * g⁻¹ := by rw [← hzh, mul_inv_cancel_right]

theorem centralizer_H_eq
    {s : G} (hs : s ∈ M.S0) (hs1 : s ≠ 1) :
    ruH M.T ⊓ Subgroup.centralizer ({s} : Set G) =
      ruS M.L ⊓ Subgroup.centralizer ({s} : Set G) := by
  have hconj : IsConj M.s1el s := by
    obtain ⟨e⟩ := M.nonempty_NP_psl29
    have hsH := M.S0_le_H hs
    have hs2 : s ^ 2 = 1 := M.S0_elem.2 _ hs
    have hsQ : s ∉ ruQ M.T := fun h => hs1 (M.eq_one_of_mem_S0_Q hs h)
    have hsz : ¬ IsConj M.z s := (M.lemma_J27_4 hs hs1).1
    obtain ⟨h, -, hy, hyB, hy2, hys⟩ := M.exists_conj_diag e hsH hs2 hsQ hsz
    have h1 := (M.outer_inv_classes e ⟨_, hy⟩ hyB hy2).2 hys M.s1el M.s1el_mem_S0 M.s1el_ne_one
    exact h1.trans (isConj_iff.mpr ⟨h⁻¹, by group⟩)
  obtain ⟨⟨h, hh, hhs⟩, -, -⟩ := M.lemma_J27_8 M.s1el_mem_S0 M.s1el_ne_one (M.S0_le_H hs) hconj
  have hle : ruS M.L ⊓ Subgroup.centralizer ({s} : Set G) ≤
      ruH M.T ⊓ Subgroup.centralizer ({s} : Set G) :=
    inf_le_inf_right _ fun x hx => M.toRuData.T_le_H (M.toRuData.S_le_T hx)
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [M.card_centralizer_S (M.mem_S0.mp hs).1 (M.not_mem_V_of_S0 hs hs1)]
  have hmap : ruH M.T ⊓ Subgroup.centralizer ({s} : Set G) ≤
      (ruS M.L ⊓ Subgroup.centralizer ({M.s1el} : Set G)).map (MulAut.conj h).toMonoidHom := by
    intro x hx
    obtain ⟨hxH, hxc⟩ := Subgroup.mem_inf.mp hx
    replace hxc := Subgroup.mem_centralizer_singleton_iff.mp hxc
    have hyH : h⁻¹ * x * h ∈ ruH M.T := by
      have := mul_mem (mul_mem (inv_mem hh) hxH) hh
      exact this
    have hyc : h⁻¹ * x * h * M.s1el = M.s1el * (h⁻¹ * x * h) := by
      have e1 : M.s1el = h⁻¹ * s * h := by rw [← hhs]; group
      rw [e1]
      calc h⁻¹ * x * h * (h⁻¹ * s * h) = h⁻¹ * (x * s) * h := by group
        _ = h⁻¹ * (s * x) * h := by rw [hxc]
        _ = h⁻¹ * s * h * (h⁻¹ * x * h) := by group
    refine ⟨h⁻¹ * x * h, Subgroup.mem_inf.mpr ⟨M.mem_S_of_comm_s1el hyH hyc,
      Subgroup.mem_centralizer_singleton_iff.mpr hyc⟩, ?_⟩
    simp [MulAut.conj_apply]
    group
  have hc := Subgroup.card_le_of_le hmap
  rw [Subgroup.card_map_of_injective (MulAut.conj h).injective,
    M.card_centralizer_S (M.mem_S0.mp M.s1el_mem_S0).1
      (M.not_mem_V_of_S0 M.s1el_mem_S0 M.s1el_ne_one)] at hc
  exact hc

theorem not_dvd_card_centralizer
    {s : G} (hs : s ∈ M.S0) (hs1 : s ≠ 1) :
    ¬ 2 ^ 9 ∣ Nat.card (Subgroup.centralizer ({s} : Set G)) := by
  intro hdvd
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Cs := Subgroup.centralizer ({s} : Set G)
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime 2 hdvd
  set P := K.map Cs.subtype
  have hPcard : Nat.card P = 2 ^ 9 := by
    rw [Subgroup.card_map_of_injective Cs.subtype_injective, hK]
  have hPp : IsPGroup 2 P := IsPGroup.of_card hPcard
  have hPC : P ≤ Cs := Subgroup.map_subtype_le K
  have hsp : IsPGroup 2 (Subgroup.zpowers s) := by
    rw [IsPGroup.iff_card, Nat.card_zpowers]
    have h := orderOf_dvd_of_pow_eq_one (M.S0_elem.2 _ hs)
    rcases (Nat.dvd_prime Nat.prime_two).mp h with h | h
    · exact ⟨0, by rw [h, pow_zero]⟩
    · exact ⟨1, by rw [h, pow_one]⟩
  have hnorm : P ≤ Subgroup.normalizer (Subgroup.zpowers s : Set G) := by
    intro x hx
    have hxs : x * s = s * x := Subgroup.mem_centralizer_singleton_iff.mp (hPC hx)
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      have : x * s ^ k * x⁻¹ = s ^ k := by
        rw [← conj_zpow, show x * s * x⁻¹ = s by rw [hxs, mul_inv_cancel_right]]
      rw [this]
      exact Subgroup.zpow_mem_zpowers _ _
    · intro hy
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hy
      have : y = s ^ k := by
        have h1 : x * s ^ k * x⁻¹ = s ^ k := by
          rw [← conj_zpow, show x * s * x⁻¹ = s by rw [hxs, mul_inv_cancel_right]]
        calc y = x⁻¹ * (x * y * x⁻¹) * x := by group
          _ = x⁻¹ * s ^ k * x := by rw [hk]
          _ = x⁻¹ * (x * s ^ k * x⁻¹) * x := by rw [h1]
          _ = s ^ k := by group
      rw [this]
      exact Subgroup.zpow_mem_zpowers _ _
  have hQp : IsPGroup 2 ↥(P ⊔ Subgroup.zpowers s : Subgroup G) :=
    hPp.to_sup_of_normal_right' hsp hnorm
  obtain ⟨g, hg⟩ := M.exists_conj_le_T hQp
  set w := g⁻¹ * M.z * g with hwdef
  have hwc : ∀ x ∈ P ⊔ Subgroup.zpowers s, x * w = w * x := by
    intro x hx
    have hT := hg x hx
    have hzc := ((M.toRuData.mem_Z_iff).mp M.z_mem_Z).2 _ hT
    rw [hwdef]
    calc x * (g⁻¹ * M.z * g) = g⁻¹ * ((g * x * g⁻¹) * M.z) * g := by group
      _ = g⁻¹ * (M.z * (g * x * g⁻¹)) * g := by rw [hzc]
      _ = g⁻¹ * M.z * g * x := by group
  have hws : w * s = s * w := (hwc s (Subgroup.mem_sup_right (Subgroup.mem_zpowers s))).symm
  obtain ⟨k, hks, hkz⟩ := M.exists_centralizer_conj_z hs hs1
    (isConj_iff.mpr ⟨g⁻¹, by rw [hwdef, inv_inv]⟩) hws
  have hle : P.map (MulAut.conj k⁻¹).toMonoidHom ≤ ruH M.T ⊓ Cs := by
    rintro _ ⟨x, hx, rfl⟩
    have hxs : x * s = s * x := Subgroup.mem_centralizer_singleton_iff.mp (hPC hx)
    have hxw := hwc x (Subgroup.mem_sup_left hx)
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    refine Subgroup.mem_inf.mpr ⟨?_, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    · rw [M.mem_H_iff_comm]
      have e1 : M.z = k⁻¹ * w * k := by rw [← hkz]; group
      rw [e1]
      calc k⁻¹ * w * k * (k⁻¹ * x * k) = k⁻¹ * (w * x) * k := by group
        _ = k⁻¹ * (x * w) * k := by rw [hxw]
        _ = k⁻¹ * x * k * (k⁻¹ * w * k) := by group
    · have hks' : k⁻¹ * s = s * k⁻¹ := by
        calc k⁻¹ * s = k⁻¹ * (s * k) * k⁻¹ := by group
          _ = k⁻¹ * (k * s) * k⁻¹ := by rw [hks]
          _ = s * k⁻¹ := by group
      calc k⁻¹ * x * k * s = k⁻¹ * x * (k * s) := by group
        _ = k⁻¹ * x * (s * k) := by rw [hks]
        _ = k⁻¹ * (x * s) * k := by group
        _ = k⁻¹ * (s * x) * k := by rw [hxs]
        _ = (k⁻¹ * s) * x * k := by group
        _ = (s * k⁻¹) * x * k := by rw [hks']
        _ = s * (k⁻¹ * x * k) := by group
  have hc := Subgroup.card_le_of_le hle
  rw [Subgroup.card_map_of_injective (MulAut.conj k⁻¹).injective, hPcard,
    M.centralizer_H_eq hs hs1, M.card_centralizer_S (M.mem_S0.mp hs).1
      (M.not_mem_V_of_S0 hs hs1)] at hc
  norm_num at hc

theorem lemma_J27_10
    {s : G} (hs : s ∈ M.S0) (hs1 : s ≠ 1) :
    M.S0 ⊔ ⁅ruS M.L ⊓ Subgroup.centralizer ({s} : Set G), M.B7⁆ =
        ruH M.T ⊓ Subgroup.centralizer ({s} : Set G) ∧
      ∃ P : Sylow 2 ↥(Subgroup.centralizer ({s} : Set G)),
        (P : Subgroup _) = (ruH M.T ⊓ Subgroup.centralizer ({s} : Set G)).subgroupOf
          (Subgroup.centralizer ({s} : Set G)) := by
  have heq : M.S0 ⊔ ⁅ruS M.L ⊓ Subgroup.centralizer ({s} : Set G), M.B7⁆ =
      ruH M.T ⊓ Subgroup.centralizer ({s} : Set G) := by
    rw [M.centralizer_H_eq hs hs1]
    exact (M.lemma_J23_3 hs hs1).2.1.symm
  refine ⟨heq, ?_⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Cs := Subgroup.centralizer ({s} : Set G)
  have hle : ruH M.T ⊓ Cs ≤ Cs := inf_le_right
  have hcard : Nat.card ((ruH M.T ⊓ Cs).subgroupOf Cs) = 2 ^ 8 := by
    rw [card_subgroupOf_of_le hle, M.centralizer_H_eq hs hs1,
      M.card_centralizer_S (M.mem_S0.mp hs).1 (M.not_mem_V_of_S0 hs hs1)]
  have h8 : 2 ^ 8 ∣ Nat.card Cs := by
    rw [← hcard, card_subgroupOf_of_le hle]
    exact Subgroup.card_dvd_of_le hle
  have h9 := M.not_dvd_card_centralizer hs hs1
  have hfac : (Nat.card Cs).factorization 2 = 8 := by
    have hpos : Nat.card Cs ≠ 0 := Nat.card_pos.ne'
    have hge : 8 ≤ (Nat.card Cs).factorization 2 :=
      (Nat.prime_two.pow_dvd_iff_le_factorization hpos).mp h8
    have hlt : ¬ 9 ≤ (Nat.card Cs).factorization 2 := fun h =>
      h9 ((Nat.prime_two.pow_dvd_iff_le_factorization hpos).mpr h)
    omega
  exact ⟨Sylow.ofCard ((ruH M.T ⊓ Cs).subgroupOf Cs) (by rw [hcard, hfac]), rfl⟩

end RuDataM

end CFSG.Quasithin.RuType
