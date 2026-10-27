module

public import CFSG.Quasithin.Background.C118Main
public import CFSG.Quasithin.Background.C118BridgeAlg

public section

namespace CFSG.Quasithin

open Subgroup CFSG CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.Campbell
open scoped commutatorElement

section Setup

variable {Ω : Type} [Group Ω]

@[expose, reducible] def clV (B H : Subgroup Ω) : Subgroup Ω := VZ B H

@[expose, reducible] noncomputable def clK (B H : Subgroup Ω) : Subgroup Ω := fstarPre H (VZ B H)

@[expose, reducible] noncomputable def clW1 (B H : Subgroup Ω) : Subgroup Ω := ⁅clV B H, clK B H⁆

@[expose, reducible] noncomputable def clW0 (B H : Subgroup Ω) : Subgroup Ω :=
  clW1 B H ⊓ Subgroup.centralizer (clK B H : Set Ω)

theorem clK_le (B H : Subgroup Ω) : clK B H ≤ H := inf_le_left

theorem H_le_normalizer_clV (B H : Subgroup Ω) : H ≤ Subgroup.normalizer (clV B H : Set Ω) :=
  le_normalizer_conjClosure _ _

theorem H_le_normalizer_fstarPre (H V : Subgroup Ω) (hV : H ≤ Subgroup.normalizer (V : Set Ω)) :
    H ≤ Subgroup.normalizer (fstarPre H V : Set Ω) := by
  have hnorm : ∀ h ∈ H, ∀ k ∈ fstarPre H V, h * k * h⁻¹ ∈ fstarPre H V := by
    intro h hh k hk
    obtain ⟨hkH, n, hn, rfl⟩ := hk
    obtain ⟨φ, hφ, hφn⟩ := hn
    set g : ↥(Subgroup.normalizer (V : Set Ω)) := ⟨h, hV hh⟩ with hg
    have hgH : g ∈ H.subgroupOf (Subgroup.normalizer (V : Set Ω)) := Subgroup.mem_subgroupOf.mpr hh
    let a : ↥(autOn H V) := ⟨conjAct V g, ⟨g, hgH, rfl⟩⟩
    have : (generalizedFitting ↥(autOn H V)).Normal :=
      (CFSG.LocalCores.generalized_fitting_characteristic).2
    have hconj := this.conj_mem φ hφ a
    refine ⟨H.mul_mem (H.mul_mem hh hkH) (H.inv_mem hh), g * n * g⁻¹, ?_, rfl⟩
    refine ⟨a * φ * a⁻¹, hconj, ?_⟩
    simp only [map_mul, map_inv]
    rw [hφn]
    rfl
  intro h hh
  rw [Subgroup.mem_normalizer_iff]
  intro x
  exact ⟨fun hx => hnorm h hh x hx, fun hx => by
    simpa [mul_assoc] using hnorm h⁻¹ (H.inv_mem hh) _ hx⟩

theorem H_le_normalizer_clK (B H : Subgroup Ω) : H ≤ Subgroup.normalizer (clK B H : Set Ω) :=
  H_le_normalizer_fstarPre H _ (H_le_normalizer_clV B H)

theorem le_normalizer_commutator' {V K H : Subgroup Ω} (hV : H ≤ Subgroup.normalizer (V : Set Ω))
    (hK : H ≤ Subgroup.normalizer (K : Set Ω)) :
    H ≤ Subgroup.normalizer ((⁅V, K⁆ : Subgroup Ω) : Set Ω) := by
  have key : ∀ x ∈ H, ∀ y ∈ (⁅V, K⁆ : Subgroup Ω), x * y * x⁻¹ ∈ (⁅V, K⁆ : Subgroup Ω) := by
    intro x hx y hy
    induction hy using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨q, hq, k, hk', rfl⟩ := hy
      have h1 : x * q * x⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp (hV hx) q).mp hq
      have h2 : x * k * x⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp (hK hx) k).mp hk'
      have := Subgroup.commutator_mem_commutator h1 h2
      convert this using 1
      simp only [commutatorElement_def]
      group
    | one => simp
    | mul y z _ _ ihy ihz =>
      have := mul_mem ihy ihz
      simpa [mul_assoc] using this
    | inv y _ ih =>
      have := inv_mem ih
      simpa [mul_assoc] using this
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  exact ⟨key x hx y, fun hy => by simpa [mul_assoc] using key x⁻¹ (H.inv_mem hx) _ hy⟩

theorem le_normalizer_inf_centralizer_c118 {W K H : Subgroup Ω}
    (hW : H ≤ Subgroup.normalizer (W : Set Ω)) (hK : H ≤ Subgroup.normalizer (K : Set Ω)) :
    H ≤ Subgroup.normalizer ((W ⊓ Subgroup.centralizer (K : Set Ω) : Subgroup Ω) : Set Ω) := by
  have key : ∀ x ∈ H, ∀ y ∈ W ⊓ Subgroup.centralizer (K : Set Ω),
      x * y * x⁻¹ ∈ W ⊓ Subgroup.centralizer (K : Set Ω) := by
    intro x hx y hy
    refine ⟨(Subgroup.mem_normalizer_iff.mp (hW hx) y).mp hy.1, ?_⟩
    show x * y * x⁻¹ ∈ Subgroup.centralizer (K : Set Ω)
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have hk' : x⁻¹ * k * x ∈ K := by
      simpa using (Subgroup.mem_normalizer_iff.mp (hK (H.inv_mem hx)) k).mp hk
    have hc := Subgroup.mem_centralizer_iff.mp hy.2 _ hk'
    calc k * (x * y * x⁻¹) = x * ((x⁻¹ * k * x) * y) * x⁻¹ := by group
      _ = x * (y * (x⁻¹ * k * x)) * x⁻¹ := by rw [hc]
      _ = x * y * x⁻¹ * k := by group
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  exact ⟨key x hx y, fun hy => by simpa [mul_assoc] using key x⁻¹ (H.inv_mem hx) _ hy⟩

theorem H_le_normalizer_clW1 (B H : Subgroup Ω) : H ≤ Subgroup.normalizer (clW1 B H : Set Ω) :=
  le_normalizer_commutator' (H_le_normalizer_clV B H) (H_le_normalizer_clK B H)

theorem H_le_normalizer_clW0 (B H : Subgroup Ω) : H ≤ Subgroup.normalizer (clW0 B H : Set Ω) :=
  le_normalizer_inf_centralizer_c118 (H_le_normalizer_clW1 B H) (H_le_normalizer_clK B H)

theorem clW1_le_clV (B H : Subgroup Ω) : clW1 B H ≤ clV B H := by
  show ⁅clV B H, clK B H⁆ ≤ clV B H
  refine Subgroup.commutator_le.mpr fun v hv k hk => ?_
  have h1 : k * v⁻¹ * k⁻¹ ∈ clV B H :=
    (Subgroup.mem_normalizer_iff.mp (H_le_normalizer_clV B H (clK_le B H hk)) v⁻¹).mp
      ((clV B H).inv_mem hv)
  have h2 : ⁅v, k⁆ = v * (k * v⁻¹ * k⁻¹) := by simp only [commutatorElement_def]; group
  rw [h2]
  exact (clV B H).mul_mem hv h1

structure C118NatData (B H : Subgroup Ω) (n : ℕ) where
  F : Type
  [fld : Field F]
  [fin : Fintype F]
  hcard : Fintype.card F = 2 ^ n
  α : ↥(clK B H) →* Matrix.SpecialLinearGroup (Fin 2) F
  hα_ker : α.ker = (Subgroup.centralizer (clV B H : Set Ω)).subgroupOf (clK B H)
  hα_range : α.range = commutator (Matrix.SpecialLinearGroup (Fin 2) F)
  β : ↥(clW1 B H) →* Multiplicative (Fin 2 → F)
  hβ_surj : Function.Surjective β
  hβ_ker : β.ker = (clW0 B H).subgroupOf (clW1 B H)
  hβ_equiv : ∀ (k : ↥(clK B H)) (u v : ↥(clW1 B H)), (v : Ω) = k * u * (k : Ω)⁻¹ →
    Multiplicative.toAdd (β v) =
      (α k : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (β u))

attribute [instance] C118NatData.fld C118NatData.fin

abbrev NatOneData (B H : Subgroup Ω) := C118NatData B H 1

theorem C118NatData.hcard_one {B H : Subgroup Ω} (d : NatOneData B H) : Fintype.card d.F = 2 := by
  simpa using d.hcard

theorem exists_natData {B H : Subgroup Ω} {n : ℕ}
    (h : IsNatL2Section (clK B H) (Subgroup.centralizer (clV B H : Set Ω)) (clW1 B H)
      (clW0 B H) n) : Nonempty (C118NatData B H n) := by
  obtain ⟨F, hfld, hfin, hcard, α, hαker, hαrange, β, hβs, hβker, hβeq⟩ := h
  exact ⟨⟨F, hcard, α, hαker, hαrange, β, hβs, hβker, hβeq⟩⟩

variable {B H : Subgroup Ω} (d : NatOneData B H)

include d in
theorem NatOneData.exists_rho :
    ∃ ρ : ↥H →* Matrix.SpecialLinearGroup (Fin 2) d.F,
      ∀ (g : ↥H) (u v : ↥(clW1 B H)), (v : Ω) = g * u * (g : Ω)⁻¹ →
        Multiplicative.toAdd (d.β v) =
          (ρ g : Matrix (Fin 2) (Fin 2) d.F).mulVec (Multiplicative.toAdd (d.β u)) := by
  have hHW := H_le_normalizer_clW1 B H
  let act : ↥H →* MulAut ↥(clW1 B H) :=
    (clW1 B H).normalizerMonoidHom.comp (Subgroup.inclusion hHW)
  have hact : ∀ (g : ↥H) (u : ↥(clW1 B H)), ((act g u : ↥(clW1 B H)) : Ω) = g * u * (g : Ω)⁻¹ :=
    fun g u => Subgroup.normalizerMonoidHom_apply_apply_coe _ _ _
  have hker : ∀ g u v, d.β u = d.β v → d.β (act g u) = d.β (act g v) := by
    intro g u v huv
    have h1 : u⁻¹ * v ∈ d.β.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, huv, inv_mul_cancel]
    rw [d.hβ_ker, Subgroup.mem_subgroupOf] at h1
    have h2 : (act g u)⁻¹ * (act g v) ∈ d.β.ker := by
      rw [d.hβ_ker, Subgroup.mem_subgroupOf]
      have := Subgroup.mem_normalizer_iff.mp (H_le_normalizer_clW0 B H g.2)
        ((u⁻¹ * v : ↥(clW1 B H)) : Ω)
      have h3 := this.mp h1
      have e : (act g u)⁻¹ * (act g v) = act g (u⁻¹ * v) := by simp [map_mul, map_inv]
      rw [e, hact g (u⁻¹ * v)]
      exact h3
    rw [MonoidHom.mem_ker, map_mul, map_inv] at h2
    exact (inv_mul_eq_one.mp h2)
  obtain ⟨ρ, hρ⟩ := exists_sl2_action act d.β d.hβ_surj d.hcard_one hker
  refine ⟨ρ, fun g u v hv => ?_⟩
  have : v = act g u := Subtype.ext (by rw [hact]; exact hv)
  rw [this]
  exact hρ g u

@[expose] def IsRhoFor {n : ℕ} (d : C118NatData B H n)
    (ρ : ↥H →* Matrix.SpecialLinearGroup (Fin 2) d.F) :
    Prop :=
  ∀ (g : ↥H) (u v : ↥(clW1 B H)), (v : Ω) = g * u * (g : Ω)⁻¹ →
    Multiplicative.toAdd (d.β v) =
      (ρ g : Matrix (Fin 2) (Fin 2) d.F).mulVec (Multiplicative.toAdd (d.β u))

theorem clW1_conj_mem (g : ↥H) (u : ↥(clW1 B H)) : (g : Ω) * u * (g : Ω)⁻¹ ∈ clW1 B H :=
  (Subgroup.mem_normalizer_iff.mp (H_le_normalizer_clW1 B H g.2) u).mp u.2

theorem IsRhoFor.eq_of {n : ℕ} {d : C118NatData B H n} {ρ : ↥H →* Matrix.SpecialLinearGroup (Fin 2) d.F}
    (hρ : IsRhoFor d ρ) (g : ↥H) (M : Matrix.SpecialLinearGroup (Fin 2) d.F)
    (h : ∀ (u v : ↥(clW1 B H)), (v : Ω) = g * u * (g : Ω)⁻¹ →
      Multiplicative.toAdd (d.β v) =
        (M : Matrix (Fin 2) (Fin 2) d.F).mulVec (Multiplicative.toAdd (d.β u))) :
    ρ g = M := by
  apply Subtype.ext
  have hall : ∀ x : Fin 2 → d.F, (ρ g : Matrix (Fin 2) (Fin 2) d.F).mulVec x =
      (M : Matrix (Fin 2) (Fin 2) d.F).mulVec x := by
    intro x
    obtain ⟨u, hu⟩ := d.hβ_surj (Multiplicative.ofAdd x)
    have hux : Multiplicative.toAdd (d.β u) = x := by rw [hu]; rfl
    let v : ↥(clW1 B H) := ⟨(g : Ω) * u * (g : Ω)⁻¹, clW1_conj_mem g u⟩
    have h1 := hρ g u v rfl
    have h2 := h u v rfl
    rw [hux] at h1 h2
    rw [← h1, ← h2]
  ext i j
  have := congrFun (hall (Pi.single j 1)) i
  simpa [Matrix.mulVec_single_one] using this

theorem IsRhoFor.rho_incl {n : ℕ} {d : C118NatData B H n}
    {ρ : ↥H →* Matrix.SpecialLinearGroup (Fin 2) d.F}
    (hρ : IsRhoFor d ρ) (k : ↥(clK B H)) :
    ρ (Subgroup.inclusion (clK_le B H) k) = d.α k := by
  refine hρ.eq_of _ _ fun u v hv => ?_
  exact d.hβ_equiv k u v hv

theorem IsRhoFor.eq_one_of_centralizes {n : ℕ} {d : C118NatData B H n}
    {ρ : ↥H →* Matrix.SpecialLinearGroup (Fin 2) d.F} (hρ : IsRhoFor d ρ) (g : ↥H)
    (hg : ∀ u ∈ clW1 B H, (g : Ω) * u = u * (g : Ω)) : ρ g = 1 := by
  refine hρ.eq_of _ _ fun u v hv => ?_
  have : v = u := Subtype.ext (by
    rw [hv, hg u u.2]
    group)
  rw [this]
  simp

end Setup

section MinPar

open B6

variable {Ω : Type} [Group Ω] [Finite Ω] {B H M : Subgroup Ω}

theorem exists_minParabolic {T : Subgroup Ω} (hT : IsSylowTwoOf T H) (h : IsMinParabolicOf H H) :
    ∃ M, MinParabolic H T M := by
  obtain ⟨T₀, hT₀, ⟨-, hlt, hncard⟩, hnorm⟩ := h
  obtain ⟨g, hg, hgT⟩ := isSylowTwoOf_exists_conj hT₀ hT
  have hH : conjSub g H = H := conjSub_eq_self (Subgroup.le_normalizer hg)
  have h1 : (maxOver (conjSub g H) (conjSub g T₀)).ncard = 1 := by
    rw [ncard_maxOver_conjSub]
    exact hncard
  rw [hH, ← hgT] at h1
  obtain ⟨M, hM⟩ := maxOver_ncard_eq_one_iff.mp h1
  exact ⟨M, minParabolic_iff.mpr ⟨⟨T₀, hT₀, ⟨le_rfl, hlt, hncard⟩, hnorm⟩, hT, hM⟩⟩

theorem normal_sylow_eq (hMP : MinParabolic H B M) {Y : Subgroup Ω} (hBY : B ≤ Y) (hYH : Y ≤ H)
    (hYn : H ≤ Subgroup.normalizer (Y : Set Ω)) : Y = H := by
  by_contra hne
  have hlt : Y < H := lt_of_le_of_ne hYH hne
  have hYM : Y ≤ M := hMP.le_of_lt hBY hlt
  have hS : IsSylowTwoOf B Y := isSylowTwoOf_mono hMP.isSylow hBY hYH
  have hfr := frattini_two hYH hYn hS
  have : H ≤ M := hfr.trans (sup_le hYM hMP.inf_normalizer_le)
  exact absurd (lt_of_le_of_lt this hMP.maximal.1) (lt_irrefl _)

end MinPar

section RhoMin

open B6

variable {Ω : Type} [Group Ω] [Finite Ω] {B H M : Subgroup Ω} {d : NatOneData B H}
  {ρ : ↥H →* Matrix.SpecialLinearGroup (Fin 2) d.F}

omit [Finite Ω] in
theorem NatOneData.exists_t (d : NatOneData B H) :
    ∃ t : Matrix.SpecialLinearGroup (Fin 2) d.F, orderOf t = 3 ∧
      d.α.range = Subgroup.zpowers t ∧ ∃ a : ↥(clK B H), d.α a = t := by
  obtain ⟨t, ht3, hc⟩ := exists_commutator_eq_zpowers d.hcard_one
  have hr : d.α.range = Subgroup.zpowers t := d.hα_range.trans hc
  refine ⟨t, ht3, hr, ?_⟩
  have : t ∈ d.α.range := hr ▸ Subgroup.mem_zpowers t
  exact this

omit [Finite Ω] in
theorem ker_map_le (f : ↥H →* Matrix.SpecialLinearGroup (Fin 2) d.F) : f.ker.map H.subtype ≤ H :=
  fun _ ⟨y, _, hy⟩ => hy ▸ y.2

theorem exists_B_ne_one (hMP : MinParabolic H B M) (hρ : IsRhoFor d ρ) :
    ∃ b : ↥H, (b : Ω) ∈ B ∧ ρ b ≠ 1 := by
  by_contra hall
  push Not at hall
  have hNn := le_normalizer_map_subtype H ρ.ker
  have hBN : B ≤ ρ.ker.map H.subtype := fun b hb =>
    ⟨⟨b, hMP.isSylow.1 hb⟩, hall _ hb, rfl⟩
  have hNH' : ρ.ker.map H.subtype = H := normal_sylow_eq hMP hBN (ker_map_le ρ) hNn
  obtain ⟨t, ht3, -, a, ha⟩ := d.exists_t
  have h1 := hρ.rho_incl a
  have hmem : (Subgroup.inclusion (clK_le B H) a : ↥H) ∈ ρ.ker := by
    have : ((Subgroup.inclusion (clK_le B H) a : ↥H) : Ω) ∈ ρ.ker.map H.subtype := by
      rw [hNH']
      exact clK_le B H a.2
    obtain ⟨y, hy, hyx⟩ := this
    have : y = Subgroup.inclusion (clK_le B H) a := Subtype.ext hyx
    rwa [← this]
  rw [MonoidHom.mem_ker, h1, ha] at hmem
  rw [hmem] at ht3
  simp at ht3

theorem rho_surjective (hMP : MinParabolic H B M) (hρ : IsRhoFor d ρ) : Function.Surjective ρ := by
  obtain ⟨b, hbB, hb1⟩ := exists_B_ne_one hMP hρ
  obtain ⟨t, ht3, -, a, ha⟩ := d.exists_t
  have htR : t ∈ ρ.range := ⟨Subgroup.inclusion (clK_le B H) a, by rw [hρ.rho_incl, ha]⟩
  have hbR : ρ b ∈ ρ.range := ⟨b, rfl⟩
  have hSL : Nat.card (Matrix.SpecialLinearGroup (Fin 2) d.F) = 6 := by
    have : Finite d.F := Finite.of_fintype d.F
    rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, Nat.card_eq_fintype_card,
      d.hcard_one]
    norm_num
  have h3 : 3 ∣ Nat.card ρ.range := by
    have := Subgroup.orderOf_dvd_natCard ρ.range htR
    rwa [ht3] at this
  have h2 : 2 ∣ Nat.card ρ.range := by
    obtain ⟨m, hm⟩ := hMP.isSylow.2.1 ⟨(b : Ω), hbB⟩
    have hm' : (ρ b) ^ (2 ^ m) = 1 := by
      have : (b : Ω) ^ (2 ^ m) = 1 := by simpa using congrArg Subtype.val hm
      have h4 : b ^ (2 ^ m) = 1 := Subtype.ext (by simpa using this)
      rw [← map_pow, h4, map_one]
    have hdvd : orderOf (ρ b) ∣ 2 ^ m := orderOf_dvd_iff_pow_eq_one.mpr hm'
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    have hj0 : j ≠ 0 := by
      rintro rfl
      exact hb1 (orderOf_eq_one_iff.mp (by simpa using hj))
    have := Subgroup.orderOf_dvd_natCard ρ.range hbR
    rw [hj] at this
    exact (dvd_pow_self 2 hj0).trans this
  have h6 : 6 ∣ Nat.card ρ.range := by
    have := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 2 3) h2 h3
    simpa using this
  have hle : Nat.card ρ.range ∣ 6 := hSL ▸ Subgroup.card_subgroup_dvd_card ρ.range
  have h6' : Nat.card ρ.range = 6 := Nat.dvd_antisymm hle h6
  have htop : ρ.range = ⊤ := Subgroup.eq_top_of_card_eq _ (by rw [h6', hSL])
  exact MonoidHom.range_eq_top.mp htop

theorem ker_map_le_kerIn (hMP : MinParabolic H B M) (hρ : IsRhoFor d ρ) :
    ρ.ker.map H.subtype ≤ kerIn M H := by
  have hNn := le_normalizer_map_subtype H ρ.ker
  rcases hMP.le_kerIn_or_twoResidual_le (ker_map_le ρ) hNn with h | h
  · exact h
  · exfalso
    obtain ⟨t, ht3, -, a, ha⟩ := d.exists_t
    obtain ⟨k, hk⟩ := twoResidual_isTwoQuotient H (a : Ω) (clK_le B H a.2)
    obtain ⟨y, hy, hyx⟩ := h hk
    have hy' : y = (Subgroup.inclusion (clK_le B H) a) ^ (2 ^ k) :=
      Subtype.ext (by simpa using hyx)
    have hy2 : ρ ((Subgroup.inclusion (clK_le B H) a) ^ (2 ^ k)) = 1 := by rw [← hy']; exact hy
    rw [map_pow, hρ.rho_incl, ha] at hy2
    have h1 : orderOf t ∣ 2 ^ k := orderOf_dvd_iff_pow_eq_one.mpr hy2
    rw [ht3] at h1
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h1
    omega

end RhoMin

section Coprime

variable {Ω : Type} [Group Ω] {B H : Subgroup Ω}

theorem NatOneData.clW0_eq_bot (d : NatOneData B H) (hVe : CFSG.Open.IsElemAbelian 2 (clV B H)) :
    clW0 B H = ⊥ := by
  classical
  obtain ⟨t, ht3, hrange, a, ha⟩ := d.exists_t
  have hVn := H_le_normalizer_clV B H
  have hKH := clK_le B H
  obtain ⟨hcomm, hsq⟩ := isElemAbelian_iff.mp hVe
  have hinv : ∀ x ∈ clV B H, x⁻¹ = x := fun x hx =>
    inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hsq x hx)
  set T : Ω → Ω := fun v => (a : Ω) * v * (a : Ω)⁻¹ with hT
  have hTV : ∀ v ∈ clV B H, T v ∈ clV B H := fun v hv =>
    (Subgroup.mem_normalizer_iff.mp (hVn (hKH a.2)) v).mp hv
  have hker : ∀ k : ↥(clK B H), d.α k = 1 → ∀ v ∈ clV B H, (k : Ω) * v * (k : Ω)⁻¹ = v := by
    intro k hk v hv
    have h1 : k ∈ d.α.ker := hk
    rw [d.hα_ker, Subgroup.mem_subgroupOf] at h1
    have h2 := Subgroup.mem_centralizer_iff.mp h1 v hv
    calc (k : Ω) * v * (k : Ω)⁻¹ = ((k : Ω) * v) * (k : Ω)⁻¹ := rfl
      _ = (v * (k : Ω)) * (k : Ω)⁻¹ := by rw [← h2]
      _ = v := by group
  have hpow3 : t ^ 3 = 1 := by rw [← ht3]; exact pow_orderOf_eq_one t
  have hT3 : ∀ v ∈ clV B H, T (T (T v)) = v := by
    intro v hv
    have := hker (a ^ 3) (by rw [map_pow, ha, hpow3]) v hv
    simp only [hT]
    rw [show (a : Ω) * ((a : Ω) * ((a : Ω) * v * (a : Ω)⁻¹) * (a : Ω)⁻¹) * (a : Ω)⁻¹ =
      ((a ^ 3 : ↥(clK B H)) : Ω) * v * ((a ^ 3 : ↥(clK B H)) : Ω)⁻¹ by simp [pow_succ]; group]
    exact this
  have hact : ∀ k : ↥(clK B H), ∃ n : ℕ, ∀ v ∈ clV B H,
      (k : Ω) * v * (k : Ω)⁻¹ = ((a : Ω) ^ n) * v * ((a : Ω) ^ n)⁻¹ := by
    intro k
    have hk : d.α k ∈ Subgroup.zpowers t := hrange ▸ ⟨k, rfl⟩
    obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr hk)
    refine ⟨n, fun v hv => ?_⟩
    have h1 := hker ((a ^ n)⁻¹ * k) (by rw [map_mul, map_inv, map_pow, ha, hn, inv_mul_cancel]) v hv
    have e : (((a ^ n)⁻¹ * k : ↥(clK B H)) : Ω) = ((a : Ω) ^ n)⁻¹ * (k : Ω) := by simp
    rw [e] at h1
    calc (k : Ω) * v * (k : Ω)⁻¹ = ((a : Ω) ^ n) * (((a : Ω) ^ n)⁻¹ * (k : Ω) * v *
        (((a : Ω) ^ n)⁻¹ * (k : Ω))⁻¹) * ((a : Ω) ^ n)⁻¹ := by group
      _ = ((a : Ω) ^ n) * v * ((a : Ω) ^ n)⁻¹ := by rw [h1]
  have hTmul : ∀ x y : Ω, T (x * y) = T x * T y := fun x y => by simp only [hT]; group
  have hTinv : ∀ x : Ω, T x⁻¹ = (T x)⁻¹ := fun x => by simp only [hT]; group
  have hT1 : T 1 = 1 := by simp only [hT]; group
  have hTn : ∀ (n : ℕ) (v : Ω), ((a : Ω) ^ (n + 1)) * v * ((a : Ω) ^ (n + 1))⁻¹ =
      T (((a : Ω) ^ n) * v * ((a : Ω) ^ n)⁻¹) := fun n v => by
    simp only [hT]; rw [pow_succ']; group
  let I : Subgroup Ω :=
    { carrier := {x | ∃ u ∈ clV B H, x = u * T u}
      one_mem' := ⟨1, one_mem _, by rw [hT1]; simp⟩
      mul_mem' := by
        rintro _ _ ⟨u, hu, rfl⟩ ⟨u', hu', rfl⟩
        refine ⟨u * u', (clV B H).mul_mem hu hu', ?_⟩
        have h1 : T u * u' = u' * T u := hcomm _ (hTV u hu) _ hu'
        rw [hTmul]
        calc u * T u * (u' * T u') = u * (T u * u') * T u' := by group
          _ = u * (u' * T u) * T u' := by rw [h1]
          _ = u * u' * (T u * T u') := by group
      inv_mem' := by
        rintro _ ⟨u, hu, rfl⟩
        refine ⟨u⁻¹, (clV B H).inv_mem hu, ?_⟩
        have h1 : T u * u⁻¹ = u⁻¹ * T u :=
          hcomm _ (hTV u hu) _ ((clV B H).inv_mem hu)
        rw [hTinv]
        calc (u * T u)⁻¹ = (T u)⁻¹ * u⁻¹ := by group
          _ = u⁻¹ * (T u)⁻¹ := by
            have := congrArg (fun z => (T u)⁻¹ * z * (T u)⁻¹) h1
            simpa [mul_assoc] using this.symm }
  have hIT : ∀ x ∈ I, T x ∈ I := by
    rintro _ ⟨u, hu, rfl⟩
    exact ⟨T u, hTV u hu, hTmul u (T u)⟩
  have hcommI : ∀ n : ℕ, ∀ v ∈ clV B H,
      v * (((a : Ω) ^ n) * v * ((a : Ω) ^ n)⁻¹)⁻¹ ∈ I := by
    intro n
    induction n with
    | zero => intro v hv; simp
    | succ n ih =>
      intro v hv
      have h1 : v * (T v)⁻¹ ∈ I := by
        refine ⟨v, hv, ?_⟩
        rw [hinv _ (hTV v hv)]
      have h2 := hIT _ (ih v hv)
      have h3 := I.mul_mem h1 h2
      have e : v * (T v)⁻¹ * T (v * (((a : Ω) ^ n) * v * ((a : Ω) ^ n)⁻¹)⁻¹) =
          v * (((a : Ω) ^ (n + 1)) * v * ((a : Ω) ^ (n + 1))⁻¹)⁻¹ := by
        rw [hTmul, hTinv, ← hTn n v]
        group
      rwa [e] at h3
  have hW1 : clW1 B H ≤ I := by
    show ⁅clV B H, clK B H⁆ ≤ I
    refine Subgroup.commutator_le.mpr fun v hv k hk => ?_
    obtain ⟨n, hn⟩ := hact ⟨k, hk⟩
    have h1 : ⁅v, k⁆ = v * ((k : Ω) * v * (k : Ω)⁻¹)⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [h1, hn v hv]
    exact hcommI n v hv
  rw [eq_bot_iff]
  intro w hw
  obtain ⟨hwW, hwc⟩ := hw
  obtain ⟨u, hu, rfl⟩ := hW1 hwW
  have hTw : T (u * T u) = u * T u := by
    have := Subgroup.mem_centralizer_iff.mp hwc (a : Ω) a.2
    simp only [hT]
    calc (a : Ω) * (u * T u) * (a : Ω)⁻¹ = ((a : Ω) * (u * T u)) * (a : Ω)⁻¹ := rfl
      _ = ((u * T u) * (a : Ω)) * (a : Ω)⁻¹ := by rw [← this]
      _ = u * T u := by group
  have hTu : T u ∈ clV B H := hTV u hu
  have h2 : T (T u) = u := by
    rw [hTmul] at hTw
    have e2 : u * T u = T u * u := hcomm _ hu _ hTu
    rw [e2] at hTw
    exact mul_left_cancel hTw
  have h3 : T u = u := by
    have := hT3 u hu
    rw [h2] at this
    exact this
  rw [Subgroup.mem_bot, h3]
  simpa [pow_two] using hsq u hu

end Coprime

section SeedOne

open B6

theorem map_mk_le_frattini_congr {X : Type*} [Group X] {N N' : Subgroup X} [N.Normal]
    [N'.Normal] (h : N = N') {A : Subgroup X}
    (hA : A.map (QuotientGroup.mk' N) ≤ frattini (X ⧸ N)) :
    A.map (QuotientGroup.mk' N') ≤ frattini (X ⧸ N') := by
  subst h
  exact hA

variable {Ω : Type} [Group Ω] [Finite Ω] {B H : Subgroup Ω}

theorem clV_facts (hB : IsSylowTwoOf B H) (hchar : CharTwo H) :
    clV B H ≤ centerOf (pCoreOf 2 H) ∧ CFSG.Open.IsElemAbelian 2 (clV B H) :=
  conjClosure_le_centerOf_pCoreOf_of_sylowIn hB.1 hB.2.1 hB.2.2 hchar le_rfl

theorem clV_le_core (hB : IsSylowTwoOf B H) (hchar : CharTwo H) : clV B H ≤ pCoreOf 2 H :=
  (clV_facts hB hchar).1.trans inf_le_left

theorem clW1_le_H (hB : IsSylowTwoOf B H) (hchar : CharTwo H) : clW1 B H ≤ H :=
  (clW1_le_clV B H).trans ((clV_le_core hB hchar).trans (CFSG.LieType.BorelTits.pCoreOf_le 2 H))

theorem isSeed_of_rho {n : ℕ} (hn : 1 ≤ n) (hB : IsSylowTwoOf B H) (hchar : CharTwo H)
    {M : Subgroup Ω} (hMP : MinParabolic H B M) (hbaum : baum B = B) (d : C118NatData B H n)
    (ρ : ↥H →* Matrix.SpecialLinearGroup (Fin 2) d.F) (hρ' : IsRhoFor d ρ)
    (hsurj : Function.Surjective ρ) (hker : ρ.ker.map H.subtype ≤ kerIn M H)
    (hW0 : ∀ x : ↥H, (x : Ω) ∈ clW0 B H → x ∈ Subgroup.center ↥H) :
    ∃ (S : Sylow 2 ↥H) (ψ : ↥((clW1 B H).subgroupOf H) →* Multiplicative (Fin 2 → d.F)),
      (S : Subgroup ↥H) = B.subgroupOf H ∧ IsSeed S ρ ((clW1 B H).subgroupOf H) ψ := by
  classical
  have hW1H := clW1_le_H hB hchar
  have hVQ := (clV_facts hB hchar).1
  have hVel := (clV_facts hB hchar).2
  have : Finite d.F := Finite.of_fintype d.F
  refine ⟨toSylow2 hB, d.β.comp (Subgroup.subgroupOfEquivOfLe hW1H).toMonoidHom,
    toSylow2_coe hB, ?_⟩
  have hQ : ∀ x : ↥H, (x : Ω) ∈ pCoreOf 2 H ↔ x ∈ CFSG.pCore 2 ↥H := by
    intro x
    rw [pCoreOf_eq]
    constructor
    · rintro ⟨y, hy, hyx⟩
      have : y = x := Subtype.ext hyx
      exact this ▸ hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  refine
    { card_k := ⟨n, hn, by rw [Nat.card_eq_fintype_card, d.hcard]⟩
      surj := hsurj
      core_le := ?_
      frattini_le := ?_
      normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hW1H).mpr
        (H_le_normalizer_clW1 B H)
      le_E := ?_
      ψ_surj := d.hβ_surj.comp (Subgroup.subgroupOfEquivOfLe hW1H).surjective
      ψ_equiv := ?_
      ψ_ker := ?_
      not_le := ?_ }
  · intro g hg
    have hgQ : (g : Ω) ∈ pCoreOf 2 H := (hQ g).mpr hg
    refine hρ'.eq_one_of_centralizes g fun u hu => ?_
    have hu' : u ∈ centerOf (pCoreOf 2 H) := hVQ (clW1_le_clV B H hu)
    exact Subgroup.mem_centralizer_iff.mp hu'.2 (g : Ω) hgQ
  · have h1 : ρ.ker ≤ (kerIn M H).subgroupOf H := fun x hx =>
      Subgroup.mem_subgroupOf.mpr (hker ⟨x, hx, rfl⟩)
    exact map_mk_le_frattini_congr (CFSG.pCore_eq_open ↥H 2).symm
      ((Subgroup.map_mono h1).trans (MinParabolic.map_kerIn_subgroupOf_eq_frattini hMP).le)
  · intro x hx
    have hxV : (x : Ω) ∈ clV B H := clW1_le_clV B H (Subgroup.mem_subgroupOf.mp hx)
    have hxc : (x : Ω) ∈ centerOf (pCoreOf 2 H) := hVQ hxV
    rw [Ecore, BlueprintB2.mem_centerTorsion_iff]
    refine ⟨(hQ x).mp hxc.1, fun q hq => ?_, ?_⟩
    · exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hxc.2 (q : Ω) ((hQ q).mpr hq))
    · exact Subtype.ext (by simpa using (B6.isElemAbelian_iff.mp hVel).2 _ hxV)
  · intro g x x' hx
    let u : ↥(clW1 B H) := ⟨(x : ↥H), Subgroup.mem_subgroupOf.mp x.2⟩
    let v : ↥(clW1 B H) := ⟨(x' : ↥H), Subgroup.mem_subgroupOf.mp x'.2⟩
    have := hρ' g u v (by simpa using congrArg Subtype.val hx)
    exact this
  · ext x
    constructor
    · intro hx
      have h2 : Subgroup.subgroupOfEquivOfLe hW1H x ∈ d.β.ker := hx
      rw [d.hβ_ker, Subgroup.mem_subgroupOf] at h2
      exact Subgroup.mem_subgroupOf.mpr ⟨x.2, hW0 _ h2⟩
    · intro hx
      have hx' : (x : ↥H) ∈ (clW1 B H).subgroupOf H ⊓ Subgroup.center ↥H :=
        Subgroup.mem_subgroupOf.mp hx
      have hxW : ((x : ↥H) : Ω) ∈ clW0 B H := by
        refine ⟨Subgroup.mem_subgroupOf.mp hx'.1, Subgroup.mem_centralizer_iff.mpr fun k hk => ?_⟩
        have := Subgroup.mem_center_iff.mp hx'.2 ⟨k, clK_le B H hk⟩
        exact congrArg Subtype.val this
      have h2 : Subgroup.subgroupOfEquivOfLe hW1H x ∈ d.β.ker := by
        rw [d.hβ_ker, Subgroup.mem_subgroupOf]
        exact hxW
      exact h2
  · intro hJ
    have hcoe := toSylow2_coe hB
    have hJ' : thompsonJ B ≤ pCoreOf 2 H := by
      have h1 : thompsonJ (B.subgroupOf H) ≤ CFSG.pCore 2 ↥H := by rw [← hcoe]; exact hJ
      have h2 := Subgroup.map_mono (f := H.subtype) h1
      rw [← thompsonJ_map_of_injective' H.subtype_injective,
        Subgroup.map_subgroupOf_eq_of_le hB.1, ← pCoreOf_eq] at h2
      exact h2
    have hred : IsTwoReducedIn H (clV B H) :=
      isTwoReducedIn_conjClosure_of_sylowIn hB.1 hB.2.1 hB.2.2 hchar le_rfl
    have hHV : ¬ H ≤ Subgroup.centralizer (clV B H : Set Ω) := by
      intro hle
      obtain ⟨g, hg⟩ : ∃ g : ↥H, ρ g ≠ 1 := by
        by_contra hall
        push Not at hall
        apply not_commutative_sl2 (F := d.F)
        intro a b
        obtain ⟨ga, rfl⟩ := hsurj a
        obtain ⟨gb, rfl⟩ := hsurj b
        rw [hall ga, hall gb]
      refine hg (hρ'.eq_one_of_centralizes g fun u hu => ?_)
      have := Subgroup.mem_centralizer_iff.mp (hle g.2) u (clW1_le_clV B H hu)
      exact this.symm
    have h1 : ⁅clV B H, thompsonJ B⁆ = ⊥ := by
      rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
      exact hJ'.trans (MinParabolic.pCoreOf_le_centralizer hred)
    have h3 := ((MinParabolic.tfae_thompsonJ hMP hred hHV).out 1 3).mp h1
    have hBQ : B ≤ pCoreOf 2 H := by
      calc B = baum B := hbaum.symm
        _ = baum (pCoreOf 2 H) := h3
        _ ≤ pCoreOf 2 H := C1GN.baum_le _
    have hQB := pCoreOf_two_le_of_isSylowTwoOf hB
    have hBeq : B = pCoreOf 2 H := le_antisymm hBQ hQB
    exact hMP.not_normal (hBeq ▸ CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H)

theorem isSeed_one (hB : IsSylowTwoOf B H) (hchar : CharTwo H) (hmin : IsMinParabolicOf H H)
    (hbaum : baum B = B) (d : NatOneData B H) :
    ∃ (S : Sylow 2 ↥H) (ρ : ↥H →* Matrix.SpecialLinearGroup (Fin 2) d.F)
      (ψ : ↥((clW1 B H).subgroupOf H) →* Multiplicative (Fin 2 → d.F)),
      (S : Subgroup ↥H) = B.subgroupOf H ∧ IsSeed S ρ ((clW1 B H).subgroupOf H) ψ := by
  obtain ⟨M, hMP⟩ := exists_minParabolic hB hmin
  obtain ⟨ρ, hρ⟩ := d.exists_rho
  have hρ' : IsRhoFor d ρ := hρ
  have hW0 := d.clW0_eq_bot (clV_facts hB hchar).2
  obtain ⟨S, ψ, hS, hseed⟩ := isSeed_of_rho le_rfl hB hchar hMP hbaum d ρ hρ'
    (rho_surjective hMP hρ') (ker_map_le_kerIn hMP hρ') (fun x hx => by
      rw [hW0] at hx
      have : x = 1 := Subtype.ext (Subgroup.mem_bot.mp hx)
      rw [this]
      exact one_mem _)
  exact ⟨S, ρ, ψ, hS, hseed⟩

theorem exists_seed_of_natOneData (hB : IsSylowTwoOf B H) (hchar : CharTwo H)
    (hmin : IsMinParabolicOf H H) (hbaum : baum B = B) (d : NatOneData B H) :
    ∃ (k : Type) (_ : Field k) (_ : Finite k) (S : Sylow 2 ↥H)
      (ρ : ↥H →* Matrix.SpecialLinearGroup (Fin 2) k)
      (ψ : Ecore ↥H →* Multiplicative (Fin 2 → k)),
      (S : Subgroup ↥H) = B.subgroupOf H ∧ IsSeed S ρ (Ecore ↥H) ψ := by
  obtain ⟨S, ρ, ψ, hS, hseed⟩ := isSeed_one hB hchar hmin hbaum d
  have : Finite d.F := Finite.of_fintype d.F
  obtain ⟨ψE, hE, -⟩ := hseed.toEcore
  exact ⟨d.F, inferInstance, this, S, ρ, ψE, hS, hE⟩

end SeedOne

end CFSG.Quasithin
