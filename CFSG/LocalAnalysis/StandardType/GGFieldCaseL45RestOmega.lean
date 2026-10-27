module

public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL4546Moving

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

section General

variable {G : Type} [Group G]

theorem inv_mul_conj_pow_mem_of_normalizer {V : Subgroup G} {g z : G}
    (hg : g ∈ Subgroup.normalizer (V : Set G)) (h : z⁻¹ * (g⁻¹ * z * g) ∈ V) :
    ∀ k : ℕ, z⁻¹ * ((g ^ k)⁻¹ * z * g ^ k) ∈ V := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    have h2 : g⁻¹ * (z⁻¹ * ((g ^ k)⁻¹ * z * g ^ k)) * g ∈ V := by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem hg) _).mp ih
      simpa using this
    have e : z⁻¹ * ((g ^ (k + 1))⁻¹ * z * g ^ (k + 1)) =
        (z⁻¹ * (g⁻¹ * z * g)) * (g⁻¹ * (z⁻¹ * ((g ^ k)⁻¹ * z * g ^ k)) * g) := by
      rw [pow_succ]
      group
    rw [e]
    exact V.mul_mem h h2

theorem not_independent_of_mem_zpowers [Finite G] {p : ℕ} [Fact p.Prime] {e c₁ c₂ : G}
    (hep : e ^ p = 1)
    (hc₁ : c₁ ∈ Subgroup.zpowers e) (hc₂ : c₂ ∈ Subgroup.zpowers e) (V : Subgroup G)
    (hind : ∀ i j : ℕ, c₁ ^ i * c₂ ^ j ∈ V → p ∣ i ∧ p ∣ j) : False := by
  have hp := (Fact.out : p.Prime)
  have hV1 : (1 : G) ∈ V := one_mem _
  have hc₁p : c₁ ^ p = 1 := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hc₁
    rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hep, one_zpow]
  by_cases h1 : c₁ = 1
  · have := hind 1 0 (by rw [h1, one_pow, pow_zero, one_mul]; exact hV1)
    exact hp.one_lt.ne' (Nat.dvd_one.mp this.1)
  · have heq := zpowers_eq_of_mem_of_ne_one hep hc₁ h1
    have hc₂' : c₂ ∈ Subgroup.zpowers c₁ := heq ▸ hc₂
    obtain ⟨m, hm⟩ := (mem_powers_iff_mem_zpowers.mpr hc₂' : c₂ ∈ Submonoid.powers c₁)
    have := hind (m * (p - 1)) 1 (by
      rw [pow_one, ← hm, ← pow_add, ← mul_add_one, Nat.sub_add_cancel hp.one_lt.le, mul_comm,
        pow_mul, hc₁p, one_pow]
      exact hV1)
    exact hp.one_lt.ne' (Nat.dvd_one.mp this.2)

end General

section Moving

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
  {L D J X B₂ : Subgroup G} {d y : G} {K U U₁ : Subgroup G}

theorem GGL45Config.comm_mem_V_of_torus (hcfg : GGL45Config p B Bs x L D J X B₂ d y K U U₁)
    {s : ℕ} (hs : 2 ≤ s) {x' : G} (hx'x : Subgroup.zpowers x' = Subgroup.zpowers x)
    (hx'V : ∀ u ∈ U₁, (u ^ (1 + p ^ (s - 1)))⁻¹ * (x'⁻¹ * u * x') ∈
      U ⊓ Subgroup.centralizer (K : Set G))
    {z : G} (hz : z ∈ U₁) (hzp : z ^ p ∈ U ⊓ Subgroup.centralizer (K : Set G)) :
    x * z * x⁻¹ * z⁻¹ ∈ U ⊓ Subgroup.centralizer (K : Set G) := by
  set V : Subgroup G := U ⊓ Subgroup.centralizer (K : Set G) with hV
  have hzU : z ∈ U := hcfg.part_le hz
  have hxU : x ∈ U := hcfg.bs_le hcfg.x_mem
  have hNV : ∀ u ∈ U, u ∈ Subgroup.normalizer (V : Set G) := fun u hu =>
    mem_normalizer_of_forall_conj_mem fun v hv => by
      have := hcfg.conj_mem_V (U.inv_mem hu) hv
      rwa [inv_inv] at this
  have hx'U : x' ∈ U :=
    (Subgroup.zpowers_le.mpr hxU) (hx'x ▸ Subgroup.mem_zpowers x')
  have hzN : z ^ p ^ (s - 1) ∈ V := by
    have e : p ^ (s - 1) = p * p ^ (s - 2) := by
      rw [← pow_succ']
      congr 1
      omega
    rw [e, pow_mul]
    exact V.pow_mem hzp _
  have h1 : z⁻¹ * (x'⁻¹ * z * x') ∈ V := by
    have h := hx'V z hz
    have e : z⁻¹ * (x'⁻¹ * z * x') =
        z ^ p ^ (s - 1) * ((z ^ (1 + p ^ (s - 1)))⁻¹ * (x'⁻¹ * z * x')) := by
      rw [pow_add, pow_one]
      group
    rw [e]
    exact V.mul_mem hzN h
  obtain ⟨k, hk⟩ : ∃ k : ℕ, x' ^ k = x⁻¹ := (Submonoid.mem_powers_iff _ _).mp
    (mem_powers_iff_mem_zpowers.mpr (hx'x ▸ inv_mem (Subgroup.mem_zpowers x) :
      x⁻¹ ∈ Subgroup.zpowers x'))
  have h2 := inv_mul_conj_pow_mem_of_normalizer (hNV x' hx'U) h1 k
  rw [hk, inv_inv] at h2
  have h3 := (Subgroup.mem_normalizer_iff.mp (hNV z hzU) _).mp h2
  have e : x * z * x⁻¹ * z⁻¹ = z * (z⁻¹ * (x * z * x⁻¹)) * z⁻¹ := by group
  rw [e]
  exact h3

theorem ggL45_omega_conj_V_of_comm (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput)
    (hcent : GGL45CentInput) (hcfg : GGL45Config p B Bs x L D J X B₂ d y K U U₁)
    (hcomm : ∀ z ∈ U₁, z ^ p ∈ U ⊓ Subgroup.centralizer (K : Set G) →
      x * z * x⁻¹ * z⁻¹ ∈ U ⊓ Subgroup.centralizer (K : Set G)) {r : G}
    (hr : r ∈ Subgroup.normalizer (U : Set G) ⊓
      Subgroup.normalizer ((Bs ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) : Set G))
    (hrd : r ∉ Subgroup.normalizer (Subgroup.zpowers d : Set G)) {z : G}
    (hzV : r⁻¹ * z * r ∈ U ⊓ Subgroup.centralizer (K : Set G)) (hzU₁ : z ∈ U₁)
    (hzp : z ^ p = 1) : z ∈ Subgroup.zpowers (r * d * r⁻¹) := by
  obtain ⟨hB₁U₁, hxU₁, -⟩ := ggL4546_basic hraw hiso hcfg
  have hC := hcent G p B Bs x L D J X B₂ d y K U U₁ hcfg
  have hii := ggL45_inf_conj_eq_one hraw hiso hcent hcfg hr hrd
  have hzU : z ∈ U := hcfg.part_le hzU₁
  have hxU : x ∈ U := hcfg.bs_le hcfg.x_mem
  have hV1 : (1 : G) ∈ U ⊓ Subgroup.centralizer (K : Set G) := one_mem _
  have ht := hcomm z hzU₁ (hzp ▸ hV1)
  have hrx : r⁻¹ * x * r ∈ U := by
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem hr.1) x).mp hxU
    rwa [inv_inv] at this
  have ht' : r⁻¹ * (x * z * x⁻¹ * z⁻¹) * r ∈ U ⊓ Subgroup.centralizer (K : Set G) := by
    have h1 := hcfg.conj_mem_V hrx hzV
    have e : r⁻¹ * (x * z * x⁻¹ * z⁻¹) * r =
        (r⁻¹ * x * r) * (r⁻¹ * z * r) * (r⁻¹ * x * r)⁻¹ * (r⁻¹ * z * r)⁻¹ := by group
    rw [e]
    exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ hzV)
  have h1 := hii _ ht' (by simpa [mul_assoc] using ht)
  have hxz : z * x = x * z := by
    have : x * z * x⁻¹ * z⁻¹ = 1 := by
      have := congrArg (fun g => r * g * r⁻¹) h1
      simpa [mul_assoc] using this
    have h2 := congrArg (· * (z * x)) this
    simp only [one_mul] at h2
    rw [← h2]
    group
  have hzBs := hcfg.mem_of_commute hzU hxz hzp
  have hzB₁ := hcfg.inf_part_le hB₁U₁ hxU₁ ⟨hzBs, hzU₁⟩
  have hrz : r⁻¹ * z * r ∈ Bs ⊓ Subgroup.centralizer (X : Set G) := by
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem hr.2) z).mp hzB₁
    rwa [inv_inv] at this
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hC ⟨hrz, hzV.2⟩)
  refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
  rw [conj_zpow, hk]
  group

theorem ggL45_comm_mem_zpowers_of_comm (hraw : GGRawInnFieldInput)
    (hiso : GGRawInndiagIsoInput) (hcent : GGL45CentInput)
    (hcfg : GGL45Config p B Bs x L D J X B₂ d y K U U₁)
    (hcomm : ∀ z ∈ U₁, z ^ p ∈ U ⊓ Subgroup.centralizer (K : Set G) →
      x * z * x⁻¹ * z⁻¹ ∈ U ⊓ Subgroup.centralizer (K : Set G)) {n : G}
    (hn : n ∈ Subgroup.normalizer (U : Set G) ⊓
      Subgroup.normalizer ((Bs ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) : Set G))
    (hnd : n ∉ Subgroup.normalizer (Subgroup.zpowers d : Set G))
    {v : G} (hv : v ∈ U ⊓ Subgroup.centralizer (K : Set G)) {a : G} (ha : a ∈ U₁)
    (hap : (a * (n * v * n⁻¹) * a⁻¹ * (n * v * n⁻¹)⁻¹) ^ p ∈
      U ⊓ Subgroup.centralizer (K : Set G)) :
    a * (n * v * n⁻¹) * a⁻¹ * (n * v * n⁻¹)⁻¹ ∈ Subgroup.zpowers (n * d * n⁻¹) := by
  have hwU : n * v * n⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp hn.1 v).mp hv.1
  have hii := ggL45_inf_conj_eq_one hraw hiso hcent hcfg hn hnd
  set w := n * v * n⁻¹ with hwdef
  have hcU₁ : a * w * a⁻¹ * w⁻¹ ∈ U₁ := by
    have := U₁.mul_mem ha (hcfg.conj_mem_part hwU (U₁.inv_mem ha))
    simpa [mul_assoc] using this
  have hnaU : n⁻¹ * a * n ∈ U := by
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem hn.1) a).mp (hcfg.part_le ha)
    rwa [inv_inv] at this
  have hcV : n⁻¹ * (a * w * a⁻¹ * w⁻¹) * n ∈ U ⊓ Subgroup.centralizer (K : Set G) := by
    have e : n⁻¹ * (a * w * a⁻¹ * w⁻¹) * n =
        (n⁻¹ * a * n) * v * (n⁻¹ * a * n)⁻¹ * v⁻¹ := by
      rw [hwdef]
      group
    rw [e]
    exact Subgroup.mul_mem _ (hcfg.conj_mem_V hnaU hv) (Subgroup.inv_mem _ hv)
  have hc1 : (a * w * a⁻¹ * w⁻¹) ^ p = 1 := by
    have hpV : n⁻¹ * (a * w * a⁻¹ * w⁻¹) ^ p * n ∈ U ⊓ Subgroup.centralizer (K : Set G) := by
      have e := (conj_pow (a := n⁻¹) (b := a * w * a⁻¹ * w⁻¹) (i := p)).symm
      rw [inv_inv] at e
      rw [e]
      exact Subgroup.pow_mem _ hcV p
    have h1 := hii _ hpV (by
      rw [show n * (n⁻¹ * (a * w * a⁻¹ * w⁻¹) ^ p * n) * n⁻¹ = (a * w * a⁻¹ * w⁻¹) ^ p by
        group]
      exact hap)
    have := congrArg (fun g => n * g * n⁻¹) h1
    simpa [mul_assoc] using this
  exact ggL45_omega_conj_V_of_comm hraw hiso hcent hcfg hcomm hn hnd hcV hcU₁ hc1

theorem ggL45_conj_V_mem_of_moving (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput)
    (hcfg : GGL45Config p B Bs x L D J X B₂ d y K U U₁)
    (hmov : ∀ n ∈ Subgroup.normalizer (U : Set G) ⊓
        Subgroup.normalizer ((Bs ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) : Set G),
      n ∉ Subgroup.normalizer (Subgroup.zpowers d : Set G) →
      ∀ v ∈ U ⊓ Subgroup.centralizer (K : Set G), n * v * n⁻¹ ∈ U₁) {n : G}
    (hn : n ∈ Subgroup.normalizer (U : Set G) ⊓
      Subgroup.normalizer ((Bs ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) : Set G))
    {v : G} (hv : v ∈ U ⊓ Subgroup.centralizer (K : Set G)) : n * v * n⁻¹ ∈ U₁ := by
  obtain ⟨-, -, hVU₁⟩ := ggL4546_basic hraw hiso hcfg
  by_cases hnd : n ∈ Subgroup.normalizer (Subgroup.zpowers d : Set G)
  · have hnK := ggL45_normalizer_le_of_canonical hcfg.1 hcfg.2.2.2.2.2.1 ⟨hn.2, hnd⟩
    refine hVU₁ ⟨(Subgroup.mem_normalizer_iff.mp hn.1 v).mp hv.1, ?_⟩
    exact (Subgroup.mem_normalizer_iff.mp (ggNormalizer_le_normalizer_centralizer K hnK) v).mp
      hv.2
  · exact hmov n hn hnd v hv

theorem ggL45_conj_V_mem_of_comm (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput)
    (hcent : GGL45CentInput) (hrank : GGL45RankInput)
    (hcfg : GGL45Config p B Bs x L D J X B₂ d y K U U₁)
    (hcomm : ∀ z ∈ U₁, z ^ p ∈ U ⊓ Subgroup.centralizer (K : Set G) →
      x * z * x⁻¹ * z⁻¹ ∈ U ⊓ Subgroup.centralizer (K : Set G)) {n : G}
    (hn : n ∈ Subgroup.normalizer (U : Set G) ⊓
      Subgroup.normalizer ((Bs ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) : Set G))
    {v : G} (hv : v ∈ U ⊓ Subgroup.centralizer (K : Set G)) : n * v * n⁻¹ ∈ U₁ := by
  have : Fact p.Prime := ⟨hcfg.prime⟩
  refine ggL45_conj_V_mem_of_moving hraw hiso hcfg (fun n hn hnd v hv => ?_) hn hv
  have hwU : n * v * n⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp hn.1 v).mp hv.1
  by_contra hw
  obtain ⟨a₁, ha₁, a₂, ha₂, hp₁, hp₂, hind⟩ :=
    hrank G p B Bs x L D J X B₂ d y K U U₁ hcfg _ hwU hw
  have hd'p : (n * d * n⁻¹) ^ p = 1 := by rw [conj_pow, hcfg.d_pow]; group
  exact not_independent_of_mem_zpowers hd'p
    (ggL45_comm_mem_zpowers_of_comm hraw hiso hcent hcfg hcomm hn hnd hv ha₁ hp₁)
    (ggL45_comm_mem_zpowers_of_comm hraw hiso hcent hcfg hcomm hn hnd hv ha₂ hp₂) _ hind

theorem ggL45_omega_V_of_conj (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput)
    (hcent : GGL45CentInput) (hcfg : GGL45Config p B Bs x L D J X B₂ d y K U U₁)
    (hcomm : ∀ z ∈ U₁, z ^ p ∈ U ⊓ Subgroup.centralizer (K : Set G) →
      x * z * x⁻¹ * z⁻¹ ∈ U ⊓ Subgroup.centralizer (K : Set G))
    (hconj : ∀ n ∈ Subgroup.normalizer (U : Set G) ⊓
        Subgroup.normalizer ((Bs ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) : Set G),
      ∀ v ∈ U ⊓ Subgroup.centralizer (K : Set G), n * v * n⁻¹ ∈ U₁) {v : G}
    (hv : v ∈ U ⊓ Subgroup.centralizer (K : Set G)) (hvp : v ^ p = 1) :
    v ∈ Subgroup.zpowers d := by
  obtain ⟨r, hr, hrd⟩ := ggL45_exists_moving hcfg.1 hcfg.2.1 hcfg.2.2.1 hcfg.2.2.2.2.2.1
    hcfg.2.2.2.2.2.2.1
  have hr' : r⁻¹ ∈ Subgroup.normalizer (U : Set G) ⊓
      Subgroup.normalizer ((Bs ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) : Set G) :=
    inv_mem hr
  have hrd' : r⁻¹ ∉ Subgroup.normalizer (Subgroup.zpowers d : Set G) := fun h =>
    hrd (by simpa using inv_mem h)
  have hzU₁ : r⁻¹ * v * r ∈ U₁ := by
    have := hconj _ hr' v hv
    rwa [inv_inv] at this
  have hzV : (r⁻¹)⁻¹ * (r⁻¹ * v * r) * r⁻¹ ∈ U ⊓ Subgroup.centralizer (K : Set G) := by
    simpa [mul_assoc] using hv
  have hzp : (r⁻¹ * v * r) ^ p = 1 := by
    have e := conj_pow (a := r⁻¹) (b := v) (i := p)
    rw [inv_inv] at e
    rw [e, hvp]
    group
  have h := ggL45_omega_conj_V_of_comm hraw hiso hcent hcfg hcomm hr' hrd' hzV hzU₁ hzp
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
  refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
  rw [conj_zpow, inv_inv] at hk
  have := congrArg (fun g => r * g * r⁻¹) hk
  simpa [mul_assoc] using this

end Moving

theorem ggL45MovingInput_of_torus (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput)
    (hcent : GGL45CentInput) (htorus : GGL45TorusInput) (hrank : GGL45RankInput)
    (hfive : GGL45FiveInput) : GGL45MovingInput := by
  intro G _ _ p B Bs x L D J X B₂ d y K U U₁ hFC hTBM hL43 hL44 hL44ii hK hsetup hpart hon r hr
    hrd
  have hcfg : GGL45Config p B Bs x L D J X B₂ d y K U U₁ :=
    ⟨hFC, hTBM, hL43, hL44, hL44ii, hK, hsetup, hpart,
      fun u hu => hon ⟨Subgroup.le_normalizer hu, hpart.1 hu⟩⟩
  obtain ⟨s, hs, -, -, -, x', hx'x, hx'V⟩ := htorus G p B Bs x L D J X B₂ d y K U U₁ hcfg
  have hcomm := fun z (hz : z ∈ U₁) hzp => hcfg.comm_mem_V_of_torus hs hx'x hx'V hz hzp
  have hconj := fun n hn v (hv : v ∈ U ⊓ Subgroup.centralizer (K : Set G)) =>
    ggL45_conj_V_mem_of_comm hraw hiso hcent hrank hcfg hcomm (n := n) hn hv
  exact hfive G p B Bs x L D J X B₂ d y K U U₁ hcfg hon
    (fun r hr hrd => ggL45_inf_conj_eq_one hraw hiso hcent hcfg hr hrd)
    (fun v hv hvp => ggL45_omega_V_of_conj hraw hiso hcent hcfg hcomm hconj hv hvp)
    hconj r hr hrd

theorem ggL45Input_of_torus (hN : GGInndiagNormalInput) (hraw : GGRawInnFieldInput)
    (hiso : GGRawInndiagIsoInput) (hcent : GGL45CentInput) (htorus : GGL45TorusInput)
    (hrank : GGL45RankInput) (hfive : GGL45FiveInput) : GGL45Input :=
  ggL45Input_of_moving_rawInnField hN hraw
    (ggL45MovingInput_of_torus hraw hiso hcent htorus hrank hfive)

end CFSG.StandardType

end
