module

public import CFSG.Quasithin.Recognition.J2RecTwoBR

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique Equiv CFSG.LieType.BorelTits J2Cz J2Cz.QM
open scoped Pointwise

@[expose] def J2Cz.pf : Perm (Fin 5) := swap 0 3 * swap 0 4 * swap 0 2 * swap 0 1

theorem J2Cz.pf_mem : pf ∈ alternatingGroup (Fin 5) := by
  rw [Perm.mem_alternatingGroup]
  decide

theorem J2Cz.pf_pow_five : pf ^ 5 = 1 := by decide

theorem J2Cz.pf_ne_one : pf ≠ 1 := by decide

theorem J2Cz.pa_pf_pa : pa * pf * pa = pf⁻¹ := by decide

theorem J2Cz.eq_pow_of_comm_pf : ∀ γ : Perm (Fin 5), γ * pf = pf * γ →
    γ = 1 ∨ γ = pf ∨ γ = pf ^ 2 ∨ γ = pf ^ 3 ∨ γ = pf ^ 4 := by
  decide +kernel

namespace J2Frame

variable {G : Type} [Group G] {z : G} (F : J2Frame G z)

@[expose] noncomputable def g5 : G := F.ι ⟨pa * pb, mul_mem pa_mem pb_mem⟩

theorem g5_eq : F.g5 = F.ι ⟨pa * pb, mul_mem pa_mem pb_mem⟩ := rfl

theorem g5_mem_centralizer : F.g5 ∈ Subgroup.centralizer ({z} : Set G) := F.ι_mem_centralizer _

theorem g5_pow_five : F.g5 ^ 5 = 1 := by
  rw [g5_eq, ← map_pow, show (⟨pa * pb, mul_mem pa_mem pb_mem⟩ : alternatingGroup (Fin 5)) ^ 5 = 1
    from Subtype.ext (by simpa using papb_pow_five), map_one]

theorem g5_ne_one : F.g5 ≠ 1 := fun h1 =>
  papb_ne_one (congrArg Subtype.val (F.ι_injective (h1.trans (map_one F.ι).symm)))

end J2Frame

structure J2A5Five {G : Type} [Group G] (A : Subgroup G) (z f : G) : Prop where
  mem : f ∈ A
  pow_five : f ^ 5 = 1
  ne_one : f ≠ 1
  inv : z * f * z = f⁻¹
  centralizer : ∀ a ∈ A, a * f = f * a → ∃ i : ℕ, a = f ^ i

namespace J2A5Five

variable {G : Type} [Group G] {A : Subgroup G} {z f : G} (hf : J2A5Five A z f)
include hf

theorem orderOf_eq : orderOf f = 5 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact orderOf_eq_prime hf.pow_five hf.ne_one

omit hf in
theorem exists_pow_eq [Finite G] {u : G} (hu : u ∈ Subgroup.zpowers f) : ∃ i : ℕ, f ^ i = u := by
  rw [← mem_powers_iff_mem_zpowers] at hu
  exact (Submonoid.mem_powers_iff _ _).mp hu

omit hf in
theorem pow_eq_one_of_two_pow_of_five {x : G} (hx5 : x ^ 5 = 1) {k : ℕ} (hxk : x ^ (2 ^ k) = 1) :
    x = 1 := by
  have h2 : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hxk
  have h3 : orderOf x ∣ 5 := orderOf_dvd_of_pow_eq_one hx5
  have h4 : Nat.gcd (2 ^ k) 5 = 1 := Nat.Coprime.pow_left _ (by norm_num)
  have h5 : orderOf x = 1 := Nat.dvd_one.mp (h4 ▸ Nat.dvd_gcd h2 h3)
  exact orderOf_eq_one_iff.mp h5

theorem pow_pow_five (i : ℕ) : (f ^ i) ^ 5 = 1 := by
  rw [← pow_mul, mul_comm, pow_mul, hf.pow_five, one_pow]

end J2A5Five

namespace J2A5Config

variable {G : Type} [Group G] {z : G} {A R : Subgroup G} {y : G} (c : J2A5Config z A R y)
include c

theorem exists_five (h : IsTypeH2 G z) : ∃ f, J2A5Five A z f := by
  obtain ⟨e⟩ := c.equiv
  set zA : ↥A := ⟨z, c.z_mem⟩ with hzA
  have hzz : zA * zA = 1 := Subtype.ext (by
    show z * z = 1
    rw [← pow_two]
    exact h.sq)
  have hz1 : zA ≠ 1 := fun h1 => h.ne_one (congrArg Subtype.val h1)
  set α : Perm (Fin 5) := (e zA : Perm (Fin 5)) with hα
  have hα2 : α * α = 1 := by
    rw [hα, ← Subgroup.coe_mul, ← map_mul, hzz, map_one]
    rfl
  have hα1 : α ≠ 1 := fun h1 => hz1 (e.injective (by rw [map_one]; exact Subtype.ext h1))
  obtain ⟨π, hπ, hπα⟩ := exists_conj_pa α (Perm.mem_alternatingGroup.mp (e zA).2) hα2 hα1
  have hαπ : α = π⁻¹ * pa * π := by rw [← hπα]; group
  set πA : alternatingGroup (Fin 5) := ⟨π, Perm.mem_alternatingGroup.mpr hπ⟩ with hπA
  set fA : alternatingGroup (Fin 5) := πA⁻¹ * ⟨pf, pf_mem⟩ * πA with hfA
  have hfAv : (fA : Perm (Fin 5)) = π⁻¹ * pf * π := rfl
  have hfApow : ∀ i : ℕ, ((fA ^ i : alternatingGroup (Fin 5)) : Perm (Fin 5)) = π⁻¹ * pf ^ i * π :=
    fun i => by
      rw [Subgroup.coe_pow, hfAv]
      have h1 := conj_pow (a := π⁻¹) (b := pf) (i := i)
      rwa [inv_inv] at h1
  refine ⟨((e.symm fA : ↥A) : G), (e.symm fA).2, ?_, ?_, ?_, ?_⟩
  · have h1 : fA ^ 5 = 1 := Subtype.ext (by
      rw [hfApow, pf_pow_five, mul_one, inv_mul_cancel]
      rfl)
    rw [← Subgroup.coe_pow, ← map_pow, h1, map_one]
    rfl
  · intro h1
    apply pf_ne_one
    have h2 : fA = 1 := by
      have h3 : e.symm fA = 1 := Subtype.ext h1
      rw [← map_one e.symm] at h3
      exact e.symm.injective h3
    have h4 : π⁻¹ * pf * π = 1 := by rw [← hfAv, h2]; rfl
    calc pf = π * (π⁻¹ * pf * π) * π⁻¹ := by group
      _ = 1 := by rw [h4]; group
  ·
    have h1 : zA * e.symm fA * zA = (e.symm fA)⁻¹ := by
      apply e.injective
      apply Subtype.ext
      rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, Subgroup.coe_mul,
        Subgroup.coe_mul, Subgroup.coe_inv, ← hα, hfAv, hαπ]
      calc π⁻¹ * pa * π * (π⁻¹ * pf * π) * (π⁻¹ * pa * π) = π⁻¹ * (pa * pf * pa) * π := by group
        _ = (π⁻¹ * pf * π)⁻¹ := by rw [pa_pf_pa]; group
    have h2 := congrArg Subtype.val h1
    simpa using h2
  ·
    intro a ha haf
    set β : Perm (Fin 5) := (e ⟨a, ha⟩ : Perm (Fin 5)) with hβ
    have h1 : β * (π⁻¹ * pf * π) = π⁻¹ * pf * π * β := by
      have h2 : (⟨a, ha⟩ : ↥A) * e.symm fA = e.symm fA * ⟨a, ha⟩ := Subtype.ext haf
      have h3 := congrArg (fun u => ((e u : alternatingGroup (Fin 5)) : Perm (Fin 5))) h2
      simp only [map_mul, MulEquiv.apply_symm_apply, Subgroup.coe_mul] at h3
      rw [hβ, ← hfAv]
      exact h3
    have h4 : π * β * π⁻¹ * pf = pf * (π * β * π⁻¹) := by
      calc π * β * π⁻¹ * pf = π * (β * (π⁻¹ * pf * π)) * π⁻¹ := by group
        _ = π * (π⁻¹ * pf * π * β) * π⁻¹ := by rw [h1]
        _ = pf * (π * β * π⁻¹) := by group
    obtain ⟨i, hi⟩ : ∃ i : ℕ, π * β * π⁻¹ = pf ^ i := by
      rcases eq_pow_of_comm_pf _ h4 with h5 | h5 | h5 | h5 | h5
      · exact ⟨0, by rw [h5, pow_zero]⟩
      · exact ⟨1, by rw [h5, pow_one]⟩
      · exact ⟨2, h5⟩
      · exact ⟨3, h5⟩
      · exact ⟨4, h5⟩
    refine ⟨i, ?_⟩
    have h6 : e ⟨a, ha⟩ = fA ^ i := Subtype.ext (by
      rw [hfApow, ← hβ, ← hi]
      group)
    have h7 : (⟨a, ha⟩ : ↥A) = (e.symm fA) ^ i := by
      rw [← map_pow, ← h6, MulEquiv.symm_apply_apply]
    have h8 := congrArg Subtype.val h7
    simpa using h8

theorem comm_f {f : G} (hf : J2A5Five A z f) {r : G} (hr : r ∈ R) : r * f = f * r :=
  c.comm_A hr hf.mem

theorem R_le_centralizer_f {f : G} (hf : J2A5Five A z f) :
    R ≤ Subgroup.centralizer ({f} : Set G) := fun _ hr =>
  Subgroup.mem_centralizer_singleton_iff.mpr (c.comm_f hf hr)

theorem y_mem_centralizer_f {f : G} (hf : J2A5Five A z f) :
    y ∈ Subgroup.centralizer ({f} : Set G) :=
  Subgroup.mem_centralizer_singleton_iff.mpr
    ((Subgroup.mem_centralizer_iff.mp c.y_mem) f hf.mem).symm

variable [Finite G]

theorem mem_four {t s : G} (ht : t ∈ R) (hs : s ∈ R) (ht1 : t ≠ 1) (hs1 : s ≠ 1) (hst : s ≠ t)
    {r : G} (hr : r ∈ R) : r = 1 ∨ r = t ∨ r = s ∨ r = t * s := by
  classical
  by_contra hne
  push Not at hne
  obtain ⟨hr1, hrt, hrs, hrts⟩ := hne
  have hts1 : t * s ≠ 1 := fun h1 => hst (by
    calc s = t * (t * s) := by rw [← mul_assoc, c.mul_self t ht, one_mul]
      _ = t := by rw [h1, mul_one])
  have htst : t * s ≠ t := fun h1 => hs1 (by
    calc s = t⁻¹ * (t * s) := by group
      _ = 1 := by rw [h1, inv_mul_cancel])
  have htss : t * s ≠ s := fun h1 => ht1 (by
    calc t = t * s * s⁻¹ := by group
      _ = 1 := by rw [h1, mul_inv_cancel])
  have hsub : (({1, t, s, t * s, r} : Finset G) : Set G) ⊆ R := by
    intro u hu
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl
    · exact R.one_mem
    · exact ht
    · exact hs
    · exact R.mul_mem ht hs
    · exact hr
  have hcard : ({1, t, s, t * s, r} : Finset G).card = 5 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_pair hrts.symm]
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨htss.symm, hrs.symm⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hst.symm, htst.symm, hrt.symm⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨ht1.symm, hs1.symm, hts1.symm, hr1.symm⟩
  have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_coe_finset, hcard] at h1
  have h2 : (R : Set G).ncard = 4 := by
    rw [← Nat.card_coe_set_eq]
    exact c.card
  omega

theorem exists_two : ∃ t s : G, t ∈ R ∧ s ∈ R ∧ t ≠ 1 ∧ s ≠ 1 ∧ s ≠ t := by
  classical
  have hR : (R : Set G).ncard = 4 := by
    rw [← Nat.card_coe_set_eq]
    exact c.card
  obtain ⟨t, ht, ht1⟩ : ∃ t ∈ R, t ≠ 1 := by
    by_contra hne
    push Not at hne
    have h1 : (R : Set G) ⊆ {1} := fun u hu => hne u hu
    have h2 := Set.ncard_le_ncard h1 (Set.toFinite _)
    rw [Set.ncard_singleton] at h2
    omega
  obtain ⟨s, hs, hs1, hst⟩ : ∃ s ∈ R, s ≠ 1 ∧ s ≠ t := by
    by_contra hne
    push Not at hne
    have h1 : (R : Set G) ⊆ {1, t} := fun u hu => by
      by_cases hu1 : u = 1
      · exact Or.inl hu1
      · exact Or.inr (hne u hu hu1)
    have h2 := Set.ncard_le_ncard h1 (Set.toFinite _)
    have h3 : ({1, t} : Set G).ncard ≤ 2 := by
      have h4 := Set.ncard_insert_le (1 : G) {t}
      rw [Set.ncard_singleton] at h4
      exact h4
    omega
  exact ⟨t, s, ht, hs, ht1, hs1, hst⟩

theorem mem_R_mul_pow (h : IsTypeH2 G z) (hcount : involutionClassCount G = 2) {f : G}
    (hf : J2A5Five A z f) {t : G} (htR : t ∈ R) (ht1 : t ≠ 1) {g : G}
    (hgt : g ∈ Subgroup.centralizer ({t} : Set G)) (hgf : g ∈ Subgroup.centralizer ({f} : Set G)) :
    ∃ r ∈ R, ∃ i : ℕ, g = r * f ^ i := by
  obtain ⟨r, hr, a, ha, rfl⟩ := c.exists_mul_eq_of_mem_centralizer h hcount htR ht1 hgt
  have haf : a * f = f * a := by
    have h1 : r * a * f = f * (r * a) := Subgroup.mem_centralizer_singleton_iff.mp hgf
    have h2 := c.comm_f hf hr
    calc a * f = r⁻¹ * (r * a * f) := by group
      _ = r⁻¹ * (f * (r * a)) := by rw [h1]
      _ = r⁻¹ * (f * r) * a := by group
      _ = r⁻¹ * (r * f) * a := by rw [h2]
      _ = f * a := by group
  obtain ⟨i, rfl⟩ := hf.centralizer a ha haf
  exact ⟨r, hr, i, rfl⟩

omit [Finite G] in
theorem pow_eq_one_of_two_pow {f : G} (hf : J2A5Five A z f) {r : G} (hr : r ∈ R) {i k : ℕ}
    (h1 : (r * f ^ i) ^ (2 ^ k) = 1) : f ^ i = 1 := by
  have hcomm : Commute r (f ^ i) := Commute.pow_right (c.comm_f hf hr) i
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [pow_zero, pow_one] at h1
    have h2 : f ^ i = r⁻¹ := eq_inv_of_mul_eq_one_right h1
    refine J2A5Five.pow_eq_one_of_two_pow_of_five (hf.pow_pow_five i) (k := 1) ?_
    rw [pow_one, pow_two, h2, ← mul_inv_rev, c.mul_self r hr, inv_one]
  · rw [hcomm.mul_pow] at h1
    have hr2k : r ^ (2 ^ k) = 1 := by
      obtain ⟨k', rfl⟩ := Nat.exists_eq_add_of_lt hk
      rw [show 0 + k' + 1 = k' + 1 by omega, pow_succ', pow_mul, pow_two, c.mul_self r hr, one_pow]
    rw [hr2k, one_mul] at h1
    exact J2A5Five.pow_eq_one_of_two_pow_of_five (hf.pow_pow_five i) h1

theorem le_R_of_isPGroup (h : IsTypeH2 G z) (hcount : involutionClassCount G = 2) {f : G}
    (hf : J2A5Five A z f) {P : Subgroup G} (hP : IsPGroup 2 P)
    (hPf : P ≤ Subgroup.centralizer ({f} : Set G)) (hRP : R ≤ P) : P ≤ R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t, -, ht, -, ht1, -, -⟩ := c.exists_two
  have : Nontrivial ↥P := ⟨⟨⟨t, hRP ht⟩, 1, fun h1 => ht1 (congrArg Subtype.val h1)⟩⟩
  have := hP.center_nontrivial
  obtain ⟨c₀, hc₀⟩ := exists_ne (1 : ↥(Subgroup.center ↥P))
  have hu1 : ((c₀ : ↥P) : G) ≠ 1 := fun h1 => hc₀ (Subtype.ext (Subtype.ext h1))
  have hucomm : ∀ p ∈ P, p * ((c₀ : ↥P) : G) = ((c₀ : ↥P) : G) * p := fun p hp =>
    congrArg Subtype.val (Subgroup.mem_center_iff.mp c₀.2 ⟨p, hp⟩)
  have h2elt : ∀ u ∈ P, ∀ {r : G}, r ∈ R → ∀ {i : ℕ}, u = r * f ^ i → u ∈ R := by
    intro u hu r hr i hri
    obtain ⟨k, hk⟩ := hP ⟨u, hu⟩
    have hk' : u ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
    rw [hri] at hk'
    rw [hri, c.pow_eq_one_of_two_pow hf hr hk', mul_one]
    exact hr
  obtain ⟨r, hr, i, hri⟩ := c.mem_R_mul_pow h hcount hf ht ht1
    (Subgroup.mem_centralizer_singleton_iff.mpr (hucomm t (hRP ht)).symm)
    (hPf (c₀ : ↥P).2)
  have hcR := h2elt _ (c₀ : ↥P).2 hr hri
  intro p hp
  obtain ⟨r', hr', j, hrj⟩ := c.mem_R_mul_pow h hcount hf hcR hu1
    (Subgroup.mem_centralizer_singleton_iff.mpr (hucomm p hp)) (hPf hp)
  exact h2elt p hp hr' hrj

theorem exists_conj_mem_R (h : IsTypeH2 G z) (hcount : involutionClassCount G = 2) {f : G}
    (hf : J2A5Five A z f) {u : G} (huf : u ∈ Subgroup.centralizer ({f} : Set G))
    (hu2 : u * u = 1) (hu1 : u ≠ 1) :
    ∃ g ∈ Subgroup.centralizer ({f} : Set G), g * u * g⁻¹ ∈ R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Cf := Subgroup.centralizer ({f} : Set G) with hCf
  have hRCf := c.R_le_centralizer_f hf
  have hRp : IsPGroup 2 (R.subgroupOf Cf) := by
    have h1 : IsPGroup 2 R := IsPGroup.of_card (n := 2) (by rw [c.card]; rfl)
    exact h1.of_equiv (Subgroup.subgroupOfEquivOfLe hRCf).symm
  obtain ⟨PR, hPR⟩ := hRp.exists_le_sylow
  have hPReq : ∀ v : ↥Cf, v ∈ (PR : Subgroup ↥Cf) → (v : G) ∈ R := by
    have h1 : (PR : Subgroup ↥Cf).map Cf.subtype ≤ R :=
      c.le_R_of_isPGroup h hcount hf (PR.isPGroup'.map _) (Subgroup.map_subtype_le _)
        fun r hr => ⟨⟨r, hRCf hr⟩, hPR (Subgroup.mem_subgroupOf.mpr hr), rfl⟩
    exact fun v hv => h1 ⟨v, hv, rfl⟩
  have huC1 : (⟨u, huf⟩ : ↥Cf) ≠ 1 := fun h1 => hu1 (congrArg Subtype.val h1)
  have hsp : IsPGroup 2 (Subgroup.zpowers (⟨u, huf⟩ : ↥Cf)) :=
    IsPGroup.of_card (n := 1) (by
      rw [Nat.card_zpowers, orderOf_eq_prime (Subtype.ext (by rw [pow_two]; exact hu2)) huC1,
        pow_one])
  obtain ⟨P', hP'⟩ := hsp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥Cf P' PR
  have h1 : MulAut.conj g ⟨u, huf⟩ ∈ MulAut.conj g • (P' : Subgroup ↥Cf) :=
    Subgroup.smul_mem_pointwise_smul _ _ _ (hP' (Subgroup.mem_zpowers _))
  rw [← Sylow.coe_subgroup_smul, hg] at h1
  refine ⟨g, g.2, ?_⟩
  have h2 := hPReq _ h1
  simpa [MulAut.conj_apply] using h2

theorem exists_odd_mover (h : IsTypeH2 G z) (hcount : involutionClassCount G = 2) {f : G}
    (hf : J2A5Five A z f) :
    ∃ w ∈ Subgroup.centralizer (A : Set G), w ∈ Subgroup.normalizer (R : Set G) ∧
      Odd (orderOf w) ∧ ∀ r ∈ R, r ≠ 1 → w * r * w⁻¹ ≠ r := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, m, hm, ham⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos y).ne'
  have hy2R : y ^ m ∈ R := by
    have h1 : IsPGroup 2 (Subgroup.zpowers (y ^ m)) := by
      refine IsPGroup.of_card (n := a) ?_
      rw [Nat.card_zpowers, orderOf_pow_of_dvd hm.pos.ne' (ham ▸ Dvd.intro_left _ rfl), ham,
        Nat.mul_div_cancel _ hm.pos]
    have hRp : IsPGroup 2 R := IsPGroup.of_card (n := 2) (by rw [c.card]; rfl)
    have hle : Subgroup.zpowers (y ^ m) ≤ Subgroup.normalizer (R : Set G) :=
      Subgroup.zpowers_le.mpr (Subgroup.pow_mem _ c.y_normalizes m)
    have hsup := IsPGroup.to_sup_of_normal_right' h1 hRp hle
    have hyf := c.y_mem_centralizer_f hf
    have h2 := c.le_R_of_isPGroup h hcount hf hsup
      (sup_le (Subgroup.zpowers_le.mpr (Subgroup.pow_mem _ hyf m)) (c.R_le_centralizer_f hf))
      le_sup_right
    exact h2 (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))
  set w := y ^ (2 ^ a) with hw
  refine ⟨w, Subgroup.pow_mem _ c.y_mem _, Subgroup.pow_mem _ c.y_normalizes _, ?_, ?_⟩
  · rw [hw, orderOf_pow_of_dvd (by positivity) (ham ▸ Dvd.intro _ rfl), ham,
      Nat.mul_div_cancel_left _ (by positivity)]
    exact hm
  ·
    have hwR : w ∉ Subgroup.centralizer (R : Set G) := by
      intro hwC
      apply c.y_not_mem
      have hy2C : y ^ m ∈ Subgroup.centralizer (R : Set G) :=
        Subgroup.mem_centralizer_iff.mpr fun r hr => c.comm_R hr hy2R
      have hcop : Nat.Coprime (2 ^ a) m := Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hm)
      have hgcd := Nat.gcd_eq_gcd_ab (2 ^ a) m
      rw [hcop.gcd_eq_one, Nat.cast_one] at hgcd
      have hy : y = w ^ (Nat.gcdA (2 ^ a) m) * (y ^ m) ^ (Nat.gcdB (2 ^ a) m) := by
        rw [hw, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add, ← hgcd,
          zpow_one]
      rw [hy]
      exact Subgroup.mul_mem _ (Subgroup.zpow_mem _ hwC _) (Subgroup.zpow_mem _ hy2C _)
    intro r hr hr1 hwr
    apply hwR
    obtain ⟨-, s, -, hs, -, hs1, hsr⟩ : ∃ t s : G, t = r ∧ s ∈ R ∧ r ≠ 1 ∧ s ≠ 1 ∧ s ≠ r := by
      obtain ⟨t₀, s₀, ht₀, hs₀, ht₀1, hs₀1, hst₀⟩ := c.exists_two
      by_cases h1 : t₀ = r
      · exact ⟨r, s₀, rfl, hs₀, hr1, hs₀1, h1 ▸ hst₀⟩
      · exact ⟨r, t₀, rfl, ht₀, hr1, ht₀1, h1⟩
    have hwN : ∀ u ∈ R, w * u * w⁻¹ ∈ R := fun u hu =>
      (Subgroup.mem_normalizer_iff.mp (Subgroup.pow_mem _ c.y_normalizes _) u).mp hu
    have hws : w * s * w⁻¹ = s := by
      by_contra hws
      have hws' : w * s * w⁻¹ = r * s := by
        rcases c.mem_four hr hs hr1 hs1 hsr (hwN s hs) with h1 | h1 | h1 | h1
        · exfalso
          apply hs1
          calc s = w⁻¹ * (w * s * w⁻¹) * w := by group
            _ = 1 := by rw [h1]; group
        · exfalso
          apply hsr
          calc s = w⁻¹ * (w * s * w⁻¹) * w := by group
            _ = w⁻¹ * (w * r * w⁻¹) * w := by rw [h1, hwr]
            _ = r := by group
        · exact absurd h1 hws
        · exact h1
      have hpow : ∀ j : ℕ, w ^ j * s * (w ^ j)⁻¹ = r ^ j * s := by
        intro j
        induction j with
        | zero => simp
        | succ j ih =>
          calc w ^ (j + 1) * s * (w ^ (j + 1))⁻¹ = w * (w ^ j * s * (w ^ j)⁻¹) * w⁻¹ := by
                rw [pow_succ']
                group
            _ = w * (r ^ j * s) * w⁻¹ := by rw [ih]
            _ = (w * r * w⁻¹) ^ j * (w * s * w⁻¹) := by rw [conj_pow]; group
            _ = r ^ (j + 1) * s := by rw [hwr, hws', pow_succ]; group
      have hodd : Odd (orderOf w) := by
        rw [hw, orderOf_pow_of_dvd (by positivity) (ham ▸ Dvd.intro _ rfl), ham,
          Nat.mul_div_cancel_left _ (by positivity)]
        exact hm
      have h1 := hpow (orderOf w)
      rw [pow_orderOf_eq_one, one_mul, inv_one, mul_one] at h1
      obtain ⟨q, hq⟩ := hodd
      rw [hq, pow_succ, pow_mul, pow_two, c.mul_self r hr, one_pow, one_mul] at h1
      apply hr1
      calc r = r * s * s⁻¹ := by group
        _ = 1 := by rw [← h1, mul_inv_cancel]
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    rcases c.mem_four hr hs hr1 hs1 hsr hu with rfl | rfl | rfl | rfl
    · group
    · calc u * w = w * u * w⁻¹ * w := by rw [hwr]
        _ = w * u := by group
    · calc u * w = w * u * w⁻¹ * w := by rw [hws]
        _ = w * u := by group
    · calc r * s * w = (w * r * w⁻¹) * (w * s * w⁻¹) * w := by rw [hwr, hws]
        _ = w * (r * s) := by group

theorem exists_conj_eq_of_mul_self (h : IsTypeH2 G z) (hcount : involutionClassCount G = 2)
    {f : G} (hf : J2A5Five A z f) {t : G} (htR : t ∈ R) (ht1 : t ≠ 1) {u : G}
    (huf : u ∈ Subgroup.centralizer ({f} : Set G)) (hu2 : u * u = 1) (hu1 : u ≠ 1) :
    ∃ g ∈ Subgroup.centralizer ({f} : Set G), g * u * g⁻¹ = t := by
  obtain ⟨g, hgf, hgR⟩ := c.exists_conj_mem_R h hcount hf huf hu2 hu1
  obtain ⟨w, hwA, hwN, hwodd, hwmove⟩ := c.exists_odd_mover h hcount hf
  have hwf : w ∈ Subgroup.centralizer ({f} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr ((Subgroup.mem_centralizer_iff.mp hwA) f hf.mem).symm
  obtain ⟨r, hr⟩ : ∃ r, r = g * u * g⁻¹ := ⟨_, rfl⟩
  rw [← hr] at hgR
  have hr1 : r ≠ 1 := fun h1 => hu1 (by
    calc u = g⁻¹ * r * g := by rw [hr]; group
      _ = 1 := by rw [h1]; group)
  have hwN' : ∀ v ∈ R, w * v * w⁻¹ ∈ R := fun v hv =>
    (Subgroup.mem_normalizer_iff.mp hwN v).mp hv
  obtain ⟨r₁, hr₁⟩ : ∃ r₁, r₁ = w * r * w⁻¹ := ⟨_, rfl⟩
  obtain ⟨r₂, hr₂⟩ : ∃ r₂, r₂ = w * r₁ * w⁻¹ := ⟨_, rfl⟩
  have hr₁R : r₁ ∈ R := hr₁ ▸ hwN' r hgR
  have hr₂R : r₂ ∈ R := hr₂ ▸ hwN' r₁ hr₁R
  have hr₁1 : r₁ ≠ 1 := fun h1 => hr1 (by
    calc r = w⁻¹ * r₁ * w := by rw [hr₁]; group
      _ = 1 := by rw [h1]; group)
  have hr₁r : r₁ ≠ r := hr₁ ▸ hwmove r hgR hr1
  have hr₂r₁ : r₂ ≠ r₁ := hr₂ ▸ hwmove r₁ hr₁R hr₁1
  have hr₂r : r₂ ≠ r := by
    intro h1
    obtain ⟨q, hq⟩ := hwodd
    have hw2 : ∀ j : ℕ, w ^ (2 * j) * r * (w ^ (2 * j))⁻¹ = r := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
        calc w ^ (2 * (j + 1)) * r * (w ^ (2 * (j + 1)))⁻¹ =
              w * (w * (w ^ (2 * j) * r * (w ^ (2 * j))⁻¹) * w⁻¹) * w⁻¹ := by
              rw [show 2 * (j + 1) = 2 * j + 1 + 1 by ring, pow_succ', pow_succ']
              group
          _ = r := by rw [ih, ← hr₁, ← hr₂, h1]
    have h2 := hw2 (q + 1)
    rw [show 2 * (q + 1) = orderOf w + 1 by rw [hq]; ring, pow_succ, pow_orderOf_eq_one,
      one_mul] at h2
    exact hr₁r (hr₁.trans h2)
  have hr₂1 : r₂ ≠ 1 := fun h1 => hr₁1 (by
    calc r₁ = w⁻¹ * r₂ * w := by rw [hr₂]; group
      _ = 1 := by rw [h1]; group)
  rcases c.mem_four hgR hr₁R hr1 hr₁1 hr₁r htR with h1 | h1 | h1 | h1
  · exact absurd h1 ht1
  · exact ⟨g, hgf, by rw [h1, hr]⟩
  · refine ⟨w * g, Subgroup.mul_mem _ hwf hgf, ?_⟩
    rw [h1, hr₁, hr]
    group
  ·
    have hr₂eq : r₂ = r * r₁ := by
      rcases c.mem_four hgR hr₁R hr1 hr₁1 hr₁r hr₂R with h2 | h2 | h2 | h2
      · exact absurd h2 hr₂1
      · exact absurd h2 hr₂r
      · exact absurd h2 hr₂r₁
      · exact h2
    refine ⟨w * (w * g), Subgroup.mul_mem _ hwf (Subgroup.mul_mem _ hwf hgf), ?_⟩
    rw [h1, ← hr₂eq, hr₂, hr₁, hr]
    group

omit c [Finite G] in
theorem centralizer_eq_of_zpowers_eq {a b : G} (hab : Subgroup.zpowers a = Subgroup.zpowers b) :
    Subgroup.centralizer ({a} : Set G) = Subgroup.centralizer ({b} : Set G) := by
  have key : ∀ {a b : G}, Subgroup.zpowers a = Subgroup.zpowers b →
      Subgroup.centralizer ({a} : Set G) ≤ Subgroup.centralizer ({b} : Set G) := by
    intro a b hab u hu
    have hb : b ∈ Subgroup.zpowers a := hab ▸ Subgroup.mem_zpowers b
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    rw [Subgroup.mem_centralizer_singleton_iff] at hu ⊢
    exact ((Commute.zpow_right (Commute.symm hu).symm k).eq)
  exact le_antisymm (key hab) (key hab.symm)

theorem dvd_card_centralizer_five (h : IsTypeH2 G z) (hcount : involutionClassCount G = 2)
    {f : G} (hf : J2A5Five A z f) : 25 ∣ Nat.card (Subgroup.centralizer ({f} : Set G)) := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  by_contra h25
  have hfo := hf.orderOf_eq
  have hzf : IsPGroup 5 (Subgroup.zpowers f) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hfo, pow_one])
  obtain ⟨P, hfP⟩ := hzf.exists_le_sylow
  have hPeq : (P : Subgroup G) = Subgroup.zpowers f := by
    by_contra hne
    apply h25
    have hlt : Subgroup.zpowers f < P := lt_of_le_of_ne hfP (Ne.symm hne)
    obtain ⟨d, hdP, hdf, hdcomm⟩ : ∃ d ∈ (P : Subgroup G), d ∉ Subgroup.zpowers f ∧
        d * f = f * d := by
      have : Nontrivial ↥(P : Subgroup G) :=
        ⟨⟨⟨f, hfP (Subgroup.mem_zpowers f)⟩, 1, fun h1 => hf.ne_one (congrArg Subtype.val h1)⟩⟩
      have := P.isPGroup'.center_nontrivial
      obtain ⟨c₀, hc₀⟩ := exists_ne (1 : ↥(Subgroup.center ↥(P : Subgroup G)))
      have hc₀1 : ((c₀ : ↥(P : Subgroup G)) : G) ≠ 1 := fun h1 =>
        hc₀ (Subtype.ext (Subtype.ext h1))
      have hc₀comm : ∀ p ∈ (P : Subgroup G), p * ((c₀ : ↥(P : Subgroup G)) : G) =
          ((c₀ : ↥(P : Subgroup G)) : G) * p := fun p hp =>
        congrArg Subtype.val (Subgroup.mem_center_iff.mp c₀.2 ⟨p, hp⟩)
      by_cases hc₀f : ((c₀ : ↥(P : Subgroup G)) : G) ∈ Subgroup.zpowers f
      ·
        obtain ⟨d, hdP, hdf⟩ := IsConcreteLE.exists_of_lt hlt
        refine ⟨d, hdP, hdf, ?_⟩
        have hzeq : Subgroup.zpowers ((c₀ : ↥(P : Subgroup G)) : G) = Subgroup.zpowers f := by
          refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hc₀f) ?_
          rw [Nat.card_zpowers, Nat.card_zpowers, hfo]
          have h1 : orderOf ((c₀ : ↥(P : Subgroup G)) : G) ∣ 5 := by
            exact orderOf_dvd_of_pow_eq_one (by
              obtain ⟨i, hi⟩ := J2A5Five.exists_pow_eq hc₀f
              rw [← hi, hf.pow_pow_five])
          rcases (Nat.dvd_prime (by norm_num)).mp h1 with h2 | h2
          · exact absurd (orderOf_eq_one_iff.mp h2) hc₀1
          · rw [h2]
        have hfc : f ∈ Subgroup.zpowers ((c₀ : ↥(P : Subgroup G)) : G) :=
          hzeq ▸ Subgroup.mem_zpowers f
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hfc
        rw [← hk]
        exact (Commute.zpow_right (Commute.symm (hc₀comm d hdP)).symm k).eq
      · exact ⟨_, (c₀ : ↥(P : Subgroup G)).2, hc₀f,
          (hc₀comm f (hfP (Subgroup.mem_zpowers f))).symm⟩
    set K := Subgroup.zpowers d ⊔ Subgroup.zpowers f with hK
    have hKP : K ≤ (P : Subgroup G) :=
      sup_le (Subgroup.zpowers_le.mpr hdP) hfP
    have hKf : K ≤ Subgroup.centralizer ({f} : Set G) :=
      sup_le (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hdcomm))
        (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr rfl))
    have hK5 : IsPGroup 5 K := P.isPGroup'.to_le hKP
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card.mp hK5)
    have hfK : Subgroup.zpowers f < K := by
      refine lt_of_le_of_ne le_sup_right fun h1 => hdf ?_
      rw [h1]
      exact Subgroup.mem_sup_left (Subgroup.mem_zpowers d)
    have h1 : Nat.card (Subgroup.zpowers f) < Nat.card K :=
      Subgroup.card_lt_of_lt hfK
    rw [Nat.card_zpowers, hfo, hn] at h1
    have hn2 : 2 ≤ n := by
      by_contra hn2
      push Not at hn2
      interval_cases n <;> simp at h1
    have h2 : 25 ∣ Nat.card K := by
      rw [hn]
      exact (pow_dvd_pow 5 hn2)
    exact h2.trans (Subgroup.card_dvd_of_le hKf)
  obtain ⟨t, -, htR, -, ht1, -, -⟩ := c.exists_two
  obtain ⟨L, hLC, hLQ, hL⟩ := h.exists_complement_of_involution (c.mem_centralizer_z htR)
    (c.mul_self t htR) (c.not_mem_pCoreOf h htR ht1)
  obtain ⟨F, -⟩ := J2Frame.exists_frame h hLC hLQ hL
  have hgo : orderOf F.g5 = 5 := orderOf_eq_prime F.g5_pow_five F.g5_ne_one
  have hzg : IsPGroup 5 (Subgroup.zpowers F.g5) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hgo, pow_one])
  obtain ⟨P', hgP'⟩ := hzg.exists_le_sylow
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq G P' P
  have h1 : MulAut.conj x F.g5 ∈ MulAut.conj x • (P' : Subgroup G) :=
    Subgroup.smul_mem_pointwise_smul _ _ _ (hgP' (Subgroup.mem_zpowers _))
  rw [← Sylow.coe_subgroup_smul, hx, hPeq] at h1
  have hxg : x * F.g5 * x⁻¹ ∈ Subgroup.zpowers f := by simpa [MulAut.conj_apply] using h1
  have hxgo : orderOf (x * F.g5 * x⁻¹) = 5 := by
    rw [show x * F.g5 * x⁻¹ = (MulAut.conj x).toMonoidHom F.g5 from rfl,
      orderOf_injective _ (MulAut.conj x).injective, hgo]
  have hzeq : Subgroup.zpowers (x * F.g5 * x⁻¹) = Subgroup.zpowers f :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hxg)
      (by rw [Nat.card_zpowers, Nat.card_zpowers, hfo, hxgo])
  have hCeq := centralizer_eq_of_zpowers_eq hzeq
  set z' := x * z * x⁻¹ with hz'
  have hz'f : z' ∈ Subgroup.centralizer ({f} : Set G) := by
    rw [← hCeq, Subgroup.mem_centralizer_singleton_iff]
    have hzg : z * F.g5 = F.g5 * z :=
      (Subgroup.mem_centralizer_singleton_iff.mp F.g5_mem_centralizer).symm
    calc x * z * x⁻¹ * (x * F.g5 * x⁻¹) = x * (z * F.g5) * x⁻¹ := by group
      _ = x * (F.g5 * z) * x⁻¹ := by rw [hzg]
      _ = x * F.g5 * x⁻¹ * (x * z * x⁻¹) := by group
  have hzz : z * z = 1 := by rw [← pow_two]; exact h.sq
  have hz'2 : z' * z' = 1 := by
    rw [hz']
    calc x * z * x⁻¹ * (x * z * x⁻¹) = x * (z * z) * x⁻¹ := by group
      _ = 1 := by rw [hzz]; group
  have hz'1 : z' ≠ 1 := fun h2 => h.ne_one (by
    calc z = x⁻¹ * z' * x := by rw [hz']; group
      _ = 1 := by rw [h2]; group)
  obtain ⟨k, -, hk⟩ := c.exists_conj_eq_of_mul_self h hcount hf htR ht1 hz'f hz'2 hz'1
  exact c.not_isConj t htR ht1 (isConj_iff.mpr ⟨k * x, by rw [← hk, hz']; group⟩)

end J2A5Config

end CFSG.Quasithin
