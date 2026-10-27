module

public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL4546Defs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

section General

variable {G : Type} [Group G]

theorem exists_pow_pow_ne_one {p : ℕ} {w : G} (hw : ∃ n : ℕ, w ^ p ^ n = 1) (hw1 : w ≠ 1) :
    ∃ m : ℕ, w ^ p ^ m ≠ 1 ∧ (w ^ p ^ m) ^ p = 1 := by
  classical
  have hn0 : Nat.find hw ≠ 0 := by
    intro h0
    have := Nat.find_spec hw
    rw [h0, pow_zero, pow_one] at this
    exact hw1 this
  refine ⟨Nat.find hw - 1, Nat.find_min hw (by omega), ?_⟩
  rw [← pow_mul, ← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn0)]
  exact Nat.find_spec hw

theorem mem_normalizer_zpowers_of_conj_mem [Finite G] {p : ℕ} [Fact p.Prime] {d e r : G}
    (hdp : d ^ p = 1) (he : e ∈ Subgroup.zpowers d) (he1 : e ≠ 1)
    (hre : r * e * r⁻¹ ∈ Subgroup.zpowers d) :
    r ∈ Subgroup.normalizer (Subgroup.zpowers d : Set G) := by
  have hre1 : r * e * r⁻¹ ≠ 1 := fun h => he1 (by
    have := congrArg (fun g => r⁻¹ * g * r) h
    simpa [mul_assoc] using this)
  have h1 := zpowers_eq_of_mem_of_ne_one hdp he he1
  have h2 := zpowers_eq_of_mem_of_ne_one hdp hre hre1
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · intro hg
    rw [← h1] at hg
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    rw [← h2, ← conj_zpow]
    exact Subgroup.zpow_mem_zpowers _ k
  · intro hg
    rw [← h2] at hg
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hg
    rw [conj_zpow] at hk
    have hg' : g = e ^ k := by
      have := congrArg (fun z => r⁻¹ * z * r) hk
      simpa [mul_assoc] using this.symm
    rw [hg', ← h1]
    exact Subgroup.zpow_mem_zpowers _ k

end General

section Moving

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
  {L D J X B₂ : Subgroup G} {d y : G} {K U U₁ : Subgroup G}

theorem ggL45_inf_conj_eq_one (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput)
    (hcent : GGL45CentInput) (hcfg : GGL45Config p B Bs x L D J X B₂ d y K U U₁) {r : G}
    (hr : r ∈ Subgroup.normalizer (U : Set G) ⊓
      Subgroup.normalizer ((Bs ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) : Set G))
    (hrd : r ∉ Subgroup.normalizer (Subgroup.zpowers d : Set G)) :
    ∀ v ∈ U ⊓ Subgroup.centralizer (K : Set G),
      r * v * r⁻¹ ∈ U ⊓ Subgroup.centralizer (K : Set G) → v = 1 := by
  have : Fact p.Prime := ⟨hcfg.prime⟩
  obtain ⟨hB₁U₁, hxU₁, hVU₁⟩ := ggL4546_basic hraw hiso hcfg
  have hC := hcent G p B Bs x L D J X B₂ d y K U U₁ hcfg
  set V : Subgroup G := U ⊓ Subgroup.centralizer (K : Set G) with hV
  set W : Subgroup G := V ⊓ V.comap (MulAut.conj r).toMonoidHom with hW
  have hmemW : ∀ g : G, g ∈ W ↔ g ∈ V ∧ r * g * r⁻¹ ∈ V := fun g => by
    simp [hW, MulAut.conj_apply]
  have hxU : x ∈ U := hcfg.bs_le hcfg.x_mem
  intro v hv hrv
  by_contra hv1
  have hWp : IsPGroup p W := hcfg.isPGroup.to_le (inf_le_left.trans inf_le_left)
  have hpW : p ∣ Nat.card W := by
    rcases hWp.card_eq_or_dvd with h | h
    · exfalso
      rw [Subgroup.card_eq_one] at h
      have hvW : v ∈ W := (hmemW v).mpr ⟨hv, hrv⟩
      rw [h] at hvW
      exact hv1 hvW
    · exact h
  have hxW : Subgroup.zpowers x ≤ Subgroup.normalizer (W : Set G) := by
    rw [Subgroup.zpowers_le]
    apply mem_normalizer_of_forall_conj_mem
    intro w hw
    obtain ⟨hwV, hrwV⟩ := (hmemW w).mp hw
    refine (hmemW _).mpr ⟨?_, ?_⟩
    · have h1 := hcfg.conj_mem_V (U.inv_mem hxU) hwV
      rw [inv_inv] at h1
      exact h1
    · have hrx : r * x⁻¹ * r⁻¹ ∈ U :=
        (Subgroup.mem_normalizer_iff.mp hr.1 _).mp (U.inv_mem hxU)
      have := hcfg.conj_mem_V hrx hrwV
      have e : r * (x⁻¹ * w * x) * r⁻¹ =
          r * x⁻¹ * r⁻¹ * (r * w * r⁻¹) * (r * x⁻¹ * r⁻¹)⁻¹ := by group
      rw [e]
      exact this
  have hxp : ∀ g ∈ Subgroup.zpowers x, ∃ k : ℕ, g ^ p ^ k ∈ Subgroup.centralizer (W : Set G) := by
    intro g hg
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    refine ⟨1, ?_⟩
    rw [pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hcfg.x_pow,
      one_zpow]
    exact one_mem _
  obtain ⟨w, hwW, hw1, hwx⟩ := exists_ne_one_mem_centralizer hpW hxW hxp
  have hwU : w ∈ U := ((hmemW w).mp hwW).1.1
  obtain ⟨n, hn⟩ := hcfg.isPGroup ⟨w, hwU⟩
  have hwn : w ^ p ^ n = 1 := by simpa using congrArg Subtype.val hn
  obtain ⟨m, he1, hep⟩ := exists_pow_pow_ne_one ⟨n, hwn⟩ hw1
  set e := w ^ p ^ m with he
  have heW : e ∈ W := W.pow_mem hwW _
  obtain ⟨heV, hreV⟩ := (hmemW e).mp heW
  have hwx' : w * x = x * w :=
    ((Subgroup.mem_centralizer_iff.mp hwx) x (Subgroup.mem_zpowers x)).symm
  have hex : e * x = x * e := (Commute.pow_left hwx' _).eq
  have heBs : e ∈ Bs := hcfg.mem_of_commute heV.1 hex hep
  have heB₁ := hcfg.inf_part_le hB₁U₁ hxU₁ ⟨heBs, hVU₁ heV⟩
  have hed : e ∈ Subgroup.zpowers d := hC ⟨heB₁, heV.2⟩
  have hreB₁ : r * e * r⁻¹ ∈ Bs ⊓ Subgroup.centralizer (X : Set G) :=
    (Subgroup.mem_normalizer_iff.mp hr.2 e).mp heB₁
  have hred : r * e * r⁻¹ ∈ Subgroup.zpowers d := hC ⟨hreB₁, hreV.2⟩
  exact hrd (mem_normalizer_zpowers_of_conj_mem hcfg.d_pow hed he1 hred)

theorem GGL45Config.comm_mem_V (hcfg : GGL45Config p B Bs x L D J X B₂ d y K U U₁)
    (homega : GGL45OmegaInput) {z : G} (hz : z ∈ U)
    (hzp : z ^ p ∈ U ⊓ Subgroup.centralizer (K : Set G)) :
    x * z * x⁻¹ * z⁻¹ ∈ U ⊓ Subgroup.centralizer (K : Set G) := by
  have hz' := homega G p B Bs x L D J X B₂ d y K U U₁ hcfg z hz hzp
  have hN : Bs ≤ Subgroup.normalizer ((U ⊓ Subgroup.centralizer (K : Set G) : Subgroup G) :
      Set G) := fun b hb => by
    apply mem_normalizer_of_forall_conj_mem
    intro v hv
    have := hcfg.conj_mem_V (U.inv_mem (hcfg.bs_le hb)) hv
    rwa [inv_inv] at this
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hN] at hz'
  obtain ⟨b, hb, v, hv, rfl⟩ := hz'
  have hxb : x * b = b * x := mul_comm_of_isElemAbelian hcfg.isElemAbelian hcfg.x_mem hb
  have hxU : x ∈ U := hcfg.bs_le hcfg.x_mem
  have h1 : x * v * x⁻¹ * v⁻¹ ∈ U ⊓ Subgroup.centralizer (K : Set G) :=
    Subgroup.mul_mem _ (hcfg.conj_mem_V hxU hv) (Subgroup.inv_mem _ hv)
  have h2 := hcfg.conj_mem_V (hcfg.bs_le hb) h1
  have e : x * (b * v) * x⁻¹ * (b * v)⁻¹ = b * (x * v * x⁻¹ * v⁻¹) * b⁻¹ := by
    calc x * (b * v) * x⁻¹ * (b * v)⁻¹ = (x * b) * v * x⁻¹ * v⁻¹ * b⁻¹ := by group
      _ = (b * x) * v * x⁻¹ * v⁻¹ * b⁻¹ := by rw [hxb]
      _ = b * (x * v * x⁻¹ * v⁻¹) * b⁻¹ := by group
  rw [e]
  exact h2

theorem ggL45_omega_conj_V (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput)
    (hcent : GGL45CentInput) (homega : GGL45OmegaInput)
    (hcfg : GGL45Config p B Bs x L D J X B₂ d y K U U₁) {r : G}
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
  have ht := hcfg.comm_mem_V homega hzU (hzp ▸ hV1)
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

theorem ggL45_conj_V_mem (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput)
    (hcent : GGL45CentInput) (homega : GGL45OmegaInput) (hrank : GGL45RankInput)
    (hcfg : GGL45Config p B Bs x L D J X B₂ d y K U U₁) {n : G}
    (hn : n ∈ Subgroup.normalizer (U : Set G) ⊓
      Subgroup.normalizer ((Bs ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) : Set G))
    {v : G} (hv : v ∈ U ⊓ Subgroup.centralizer (K : Set G)) : n * v * n⁻¹ ∈ U₁ := by
  have : Fact p.Prime := ⟨hcfg.prime⟩
  have hp := hcfg.prime
  obtain ⟨-, -, hVU₁⟩ := ggL4546_basic hraw hiso hcfg
  have hwU : n * v * n⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp hn.1 v).mp hv.1
  by_cases hnd : n ∈ Subgroup.normalizer (Subgroup.zpowers d : Set G)
  · have hnK := ggL45_normalizer_le_of_canonical hcfg.1 hcfg.2.2.2.2.2.1 ⟨hn.2, hnd⟩
    refine hVU₁ ⟨hwU, ?_⟩
    exact (Subgroup.mem_normalizer_iff.mp (ggNormalizer_le_normalizer_centralizer K hnK) v).mp
      hv.2
  by_contra hw
  obtain ⟨a₁, ha₁, a₂, ha₂, hp₁, hp₂, hind⟩ :=
    hrank G p B Bs x L D J X B₂ d y K U U₁ hcfg _ hwU hw
  have hii := ggL45_inf_conj_eq_one hraw hiso hcent hcfg hn hnd
  set w := n * v * n⁻¹ with hwdef
  have key : ∀ a ∈ U₁, (a * w * a⁻¹ * w⁻¹) ^ p ∈ U ⊓ Subgroup.centralizer (K : Set G) →
      a * w * a⁻¹ * w⁻¹ ∈ Subgroup.zpowers (n * d * n⁻¹) := by
    intro a ha hap
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
    exact ggL45_omega_conj_V hraw hiso hcent homega hcfg hn hnd hcV hcU₁ hc1
  have hd'p : (n * d * n⁻¹) ^ p = 1 := by rw [conj_pow, hcfg.d_pow]; group
  have hc₁ := key a₁ ha₁ hp₁
  have hc₂ := key a₂ ha₂ hp₂
  have hc₁p : (a₁ * w * a₁⁻¹ * w⁻¹) ^ p = 1 := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hc₁
    rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hd'p, one_zpow]
  generalize a₁ * w * a₁⁻¹ * w⁻¹ = c₁ at hc₁ hc₁p hind
  generalize a₂ * w * a₂⁻¹ * w⁻¹ = c₂ at hc₂ hind
  have hV1 : (1 : G) ∈ U ⊓ Subgroup.centralizer (K : Set G) := one_mem _
  by_cases h1 : c₁ = 1
  · have := hind 1 0 (by rw [h1, one_pow, pow_zero, one_mul]; exact hV1)
    exact hp.one_lt.ne' (Nat.dvd_one.mp this.1)
  · have heq := zpowers_eq_of_mem_of_ne_one hd'p hc₁ h1
    have hc₂' : c₂ ∈ Subgroup.zpowers c₁ := heq ▸ hc₂
    obtain ⟨m, hm⟩ := (mem_powers_iff_mem_zpowers.mpr hc₂' : c₂ ∈ Submonoid.powers c₁)
    have := hind (m * (p - 1)) 1 (by
      rw [pow_one, ← hm, ← pow_add, ← mul_add_one, Nat.sub_add_cancel hp.one_lt.le, mul_comm,
        pow_mul, hc₁p, one_pow]
      exact hV1)
    exact hp.one_lt.ne' (Nat.dvd_one.mp this.2)

theorem ggL45_omega_V (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput)
    (hcent : GGL45CentInput) (homega : GGL45OmegaInput) (hrank : GGL45RankInput)
    (hcfg : GGL45Config p B Bs x L D J X B₂ d y K U U₁) {v : G}
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
    have := ggL45_conj_V_mem hraw hiso hcent homega hrank hcfg hr' hv
    rwa [inv_inv] at this
  have hzV : (r⁻¹)⁻¹ * (r⁻¹ * v * r) * r⁻¹ ∈ U ⊓ Subgroup.centralizer (K : Set G) := by
    simpa [mul_assoc] using hv
  have hzp : (r⁻¹ * v * r) ^ p = 1 := by
    have e := conj_pow (a := r⁻¹) (b := v) (i := p)
    rw [inv_inv] at e
    rw [e, hvp]
    group
  have h := ggL45_omega_conj_V hraw hiso hcent homega hcfg hr' hrd' hzV hzU₁ hzp
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
  refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
  rw [conj_zpow, inv_inv] at hk
  have := congrArg (fun g => r * g * r⁻¹) hk
  simpa [mul_assoc] using this

end Moving

theorem ggL45MovingInput_of_inputs (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput)
    (hcent : GGL45CentInput) (homega : GGL45OmegaInput) (hrank : GGL45RankInput)
    (hfive : GGL45FiveInput) : GGL45MovingInput := by
  intro G _ _ p B Bs x L D J X B₂ d y K U U₁ hFC hTBM hL43 hL44 hL44ii hK hsetup hpart hon r hr
    hrd
  have hcfg : GGL45Config p B Bs x L D J X B₂ d y K U U₁ :=
    ⟨hFC, hTBM, hL43, hL44, hL44ii, hK, hsetup, hpart,
      fun u hu => hon ⟨Subgroup.le_normalizer hu, hpart.1 hu⟩⟩
  exact hfive G p B Bs x L D J X B₂ d y K U U₁ hcfg hon
    (fun r hr hrd => ggL45_inf_conj_eq_one hraw hiso hcent hcfg hr hrd)
    (fun v hv hvp => ggL45_omega_V hraw hiso hcent homega hrank hcfg hv hvp)
    (fun n hn v hv => ggL45_conj_V_mem hraw hiso hcent homega hrank hcfg hn hv) r hr hrd

theorem ggL45Input_of_inputs (hN : GGInndiagNormalInput) (hraw : GGRawInnFieldInput)
    (hiso : GGRawInndiagIsoInput) (hcent : GGL45CentInput) (homega : GGL45OmegaInput)
    (hrank : GGL45RankInput) (hfive : GGL45FiveInput) : GGL45Input :=
  ggL45Input_of_moving_rawInnField hN hraw
    (ggL45MovingInput_of_inputs hraw hiso hcent homega hrank hfive)

end CFSG.StandardType

end
