module

public import CFSG.LocalAnalysis.StandardType.GGL45NtCoreGeo
public import CFSG.LocalAnalysis.StandardType.GGL45NtExcEndPow

public section

namespace CFSG.HardMathSupport.C14Exc

open CFSG CFSG.Assembly CFSG.StandardType

@[expose] def pCent (p : ℕ) {Γ : Type*} [Group Γ] (G E : Subgroup Γ) : Set Γ :=
  {x | x ∈ G ∧ (∀ e ∈ E, x * e = e * x) ∧ ∃ k : ℕ, x ^ p ^ k = 1}

@[expose] def AbsSat0 (p : ℕ) {Γ : Type*} [Group Γ] (G : Subgroup Γ) (F₀ : Γ →* Γ)
    (E : Subgroup Γ) : Prop :=
  ∀ y ∈ G, y ^ p = 1 → (∀ x ∈ E, y * x = x * y) → F₀ y = y → y ∈ E

@[expose] def AbsGeo (p : ℕ) {Γ : Type*} [Group Γ] (G : Subgroup Γ) (F₀ : Γ →* Γ)
    (E : Subgroup Γ) : Prop :=
  (∀ u ∈ pCent p G E, ∀ v ∈ pCent p G E, u * v = v * u) ∧
  (∀ u ∈ pCent p G E, ∀ w ∈ G, (∀ e ∈ E, w * e = e * w) → w * u = u * w) ∧
  ∃ N : ℕ, 2 ≤ N ∧ (∀ u ∈ pCent p G E, F₀ u = u ^ N) ∧
    ∀ a ∈ pCent p G E, F₀ a = a →
      ∃ b ∈ pCent p G E, a = b ^ ∑ i ∈ Finset.range p, N ^ i

@[expose] def AbsGeoAt (p : ℕ) {Γ : Type*} [Group Γ] (G : Subgroup Γ) (F₀ : Γ →* Γ) : Prop :=
  ∀ E : Subgroup Γ, E ≤ G → IsElemAbelian p E → p ^ 2 ≤ Nat.card E → (∀ x ∈ E, F₀ x = x) →
    AbsSat0 p G F₀ E → AbsGeo p G F₀ E

@[expose] def AbsBridge (p : ℕ) {R : Type} [Group R] (I F : Set (MulAut R)) {Γ : Type*} [Group Γ]
    (G : Subgroup Γ) (F₀ : Γ →* Γ) : Prop :=
  ∃ (ρ : R →* Γ) (Θ : G →* MulAut R), Function.Injective ρ ∧ (∀ r, ρ r ∈ G) ∧
    Function.Injective Θ ∧ (∀ φ, φ ∈ I ↔ ∃ g, Θ g = φ) ∧
    (∀ (g : G) (r : R), ρ (Θ g r) = (g : Γ) * ρ r * (g : Γ)⁻¹) ∧
    ∀ f ∈ F, orderOf f = p → ∃ j : ℕ, ¬ p ∣ j ∧ ∀ r, ρ (f r) = (endPow F₀ j) (ρ r)

theorem endPow_mem {Γ : Type*} [Group Γ] {G : Subgroup Γ} {F₀ : Γ →* Γ}
    (hstab : ∀ g ∈ G, F₀ g ∈ G) (j : ℕ) {g : Γ} (hg : g ∈ G) : endPow F₀ j g ∈ G := by
  induction j with
  | zero => simpa [endPow_apply] using hg
  | succ j ih =>
    rw [endPow_apply, Function.iterate_succ_apply', ← endPow_apply]
    exact hstab _ ih

theorem endPow_fixed_iff {Γ : Type*} [Group Γ] {F₀ : Γ →* Γ} {p : ℕ} (hp : p.Prime) {g : Γ}
    (hg : endPow F₀ p g = g) {j : ℕ} (hj : ¬ p ∣ j) : endPow F₀ j g = g ↔ F₀ g = g := by
  have hgp : F₀^[p] g = g := by rw [← endPow_apply F₀ p g]; exact hg
  constructor
  · intro h
    have hgj : F₀^[j] g = g := by rw [← endPow_apply F₀ j g]; exact h
    have hcop : Nat.Coprime j p := ((hp.coprime_iff_not_dvd).2 hj).symm
    obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hp.one_lt
    have hdiv : p * (j * m / p) + 1 = j * m := by
      have h := Nat.div_add_mod (j * m) p
      rw [hm] at h
      exact h
    have hjm : F₀^[j * m] g = g := by
      rw [Function.iterate_mul]
      exact Function.iterate_fixed hgj m
    have hpk : F₀^[p * (j * m / p)] g = g := by
      rw [Function.iterate_mul]
      exact Function.iterate_fixed hgp (j * m / p)
    have hkey : F₀^[j * m] g = F₀ g := by
      conv_lhs => rw [← hdiv]
      rw [Nat.add_comm (p * (j * m / p)) 1, Function.iterate_add_apply, hpk, Function.iterate_one]
    rw [hkey] at hjm
    exact hjm
  · intro h
    rw [endPow_apply]
    exact Function.iterate_fixed h j

theorem endPow_pow {Γ : Type*} [Group Γ] {F₀ : Γ →* Γ} {N : ℕ} {u : Γ} (hu : F₀ u = u ^ N)
    (m : ℕ) : endPow F₀ m u = u ^ N ^ m := by
  induction m with
  | zero => simp [endPow_apply]
  | succ m ih =>
    have hstep : endPow F₀ (m + 1) u = F₀ (endPow F₀ m u) := by
      rw [endPow_apply, Function.iterate_succ_apply']
      rfl
    rw [hstep, ih, map_pow, hu, ← pow_mul, ← pow_succ']

theorem absBridge_theta_rho {R : Type} [Group R] {Γ : Type*} [Group Γ] {G : Subgroup Γ}
    {ρ : R →* Γ} {Θ : G →* MulAut R} (hρ : Function.Injective ρ) (hρG : ∀ r, ρ r ∈ G)
    (hconj : ∀ (g : G) (r : R), ρ (Θ g r) = (g : Γ) * ρ r * (g : Γ)⁻¹) (r : R) :
    Θ ⟨ρ r, hρG r⟩ = MulAut.conj r := by
  apply MulEquiv.ext
  intro r'
  apply hρ
  rw [hconj, MulAut.conj_apply]
  simp only [map_mul, map_inv]

theorem absBridge_conj {R : Type} [Group R] {Γ : Type*} [Group Γ] {G : Subgroup Γ} {F₀ : Γ →* Γ}
    (hstab : ∀ g ∈ G, F₀ g ∈ G) {ρ : R →* Γ} {Θ : G →* MulAut R} (hρ : Function.Injective ρ)
    (hconj : ∀ (g : G) (r : R), ρ (Θ g r) = (g : Γ) * ρ r * (g : Γ)⁻¹) {f : MulAut R} {j : ℕ}
    (hfj : ∀ r, ρ (f r) = (endPow F₀ j) (ρ r)) (g : G) :
    f * Θ g * f⁻¹ = Θ ⟨endPow F₀ j g, endPow_mem hstab j g.2⟩ := by
  apply MulEquiv.ext
  intro r
  apply hρ
  have hff : f (f⁻¹ r) = r := by
    rw [← MulAut.mul_apply R f f⁻¹ r, mul_inv_cancel f]
    rfl
  have hfinv : (endPow F₀ j) (ρ (f⁻¹ r)) = ρ r := by
    rw [← hfj (f⁻¹ r), hff]
  rw [MulAut.mul_apply, MulAut.mul_apply, hfj, hconj g (f⁻¹ r), map_mul, map_mul, map_inv,
    hfinv, hconj ⟨endPow F₀ j g, endPow_mem hstab j g.2⟩ r]

@[expose] def bridgeSub {R : Type} [Group R] {Γ : Type*} [Group Γ] {G : Subgroup Γ}
    (Θ : G →* MulAut R) (Ebar : Subgroup (MulAut R)) : Subgroup Γ :=
  (Ebar.comap Θ).map G.subtype

theorem mem_bridgeSub {R : Type} [Group R] {Γ : Type*} [Group Γ] {G : Subgroup Γ}
    (Θ : G →* MulAut R) (Ebar : Subgroup (MulAut R)) (g : G) :
    (g : Γ) ∈ bridgeSub Θ Ebar ↔ Θ g ∈ Ebar := by
  rw [bridgeSub, Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, hxg⟩
    rw [Subgroup.mem_comap] at hx
    have hx' : x = g := Subtype.ext hxg
    rwa [hx'] at hx
  · intro hg
    exact ⟨g, by rwa [Subgroup.mem_comap], rfl⟩

theorem bridgeSub_le {R : Type} [Group R] {Γ : Type*} [Group Γ] {G : Subgroup Γ}
    (Θ : G →* MulAut R) (Ebar : Subgroup (MulAut R)) : bridgeSub Θ Ebar ≤ G := by
  exact Subgroup.map_subtype_le _

theorem bridgeSub_isElemAbelian {p : ℕ} {R : Type} [Group R] {Γ : Type*} [Group Γ]
    {G : Subgroup Γ} {Θ : G →* MulAut R} (hΘ : Function.Injective Θ) {Ebar : Subgroup (MulAut R)}
    (hE : IsElemAbelian p Ebar) : IsElemAbelian p (bridgeSub Θ Ebar) := by
  refine ⟨IsMulCommutative.of_comm ?_, ?_⟩
  · intro a b
    apply Subtype.ext
    have haG : (a : Γ) ∈ G := bridgeSub_le Θ Ebar a.2
    have hbG : (b : Γ) ∈ G := bridgeSub_le Θ Ebar b.2
    have haE : Θ ⟨(a : Γ), haG⟩ ∈ Ebar := (mem_bridgeSub Θ Ebar ⟨(a : Γ), haG⟩).1 a.2
    have hbE : Θ ⟨(b : Γ), hbG⟩ ∈ Ebar := (mem_bridgeSub Θ Ebar ⟨(b : Γ), hbG⟩).1 b.2
    haveI : IsMulCommutative Ebar := hE.1
    have hcommE : (⟨Θ ⟨(a : Γ), haG⟩, haE⟩ : Ebar) * ⟨Θ ⟨(b : Γ), hbG⟩, hbE⟩ =
        ⟨Θ ⟨(b : Γ), hbG⟩, hbE⟩ * ⟨Θ ⟨(a : Γ), haG⟩, haE⟩ := mul_comm' _ _
    have hcomm : Θ ⟨(a : Γ), haG⟩ * Θ ⟨(b : Γ), hbG⟩ =
        Θ ⟨(b : Γ), hbG⟩ * Θ ⟨(a : Γ), haG⟩ := congrArg Subtype.val hcommE
    have hmap : Θ (⟨(a : Γ), haG⟩ * ⟨(b : Γ), hbG⟩) =
        Θ (⟨(b : Γ), hbG⟩ * ⟨(a : Γ), haG⟩) := by
      rw [map_mul, map_mul, hcomm]
    exact congrArg (fun x : G => (x : Γ)) (hΘ hmap)
  · intro x hx
    have hxG : x ∈ G := bridgeSub_le Θ Ebar hx
    have hxE : Θ ⟨x, hxG⟩ ∈ Ebar := (mem_bridgeSub Θ Ebar ⟨x, hxG⟩).1 hx
    have hp : (Θ ⟨x, hxG⟩) ^ p = 1 := hE.2 _ hxE
    have hmap : Θ (⟨x, hxG⟩ ^ p) = Θ 1 := by rw [map_pow, hp, map_one]
    exact congrArg (fun y : G => (y : Γ)) (hΘ hmap)

theorem bridgeSub_card {R : Type} [Group R] {Γ : Type*} [Group Γ] {G : Subgroup Γ}
    {Θ : G →* MulAut R} (hΘ : Function.Injective Θ) {Ebar : Subgroup (MulAut R)}
    (hEI : ∀ e ∈ Ebar, ∃ g : G, Θ g = e) : Nat.card (bridgeSub Θ Ebar) = Nat.card Ebar := by
  have h1 : Nat.card (bridgeSub Θ Ebar) = Nat.card (Ebar.comap Θ) := by
    rw [bridgeSub]
    exact Subgroup.card_map_of_injective G.subtype_injective
  have hmap : (Ebar.comap Θ).map Θ = Ebar := by
    apply le_antisymm
    · intro e he
      rw [Subgroup.mem_map] at he
      obtain ⟨g, hg, rfl⟩ := he
      exact hg
    · intro e he
      obtain ⟨g, hg⟩ := hEI e he
      exact Subgroup.mem_map.mpr ⟨g, by rw [Subgroup.mem_comap, hg]; exact he, hg⟩
  calc Nat.card (bridgeSub Θ Ebar)
      = Nat.card (Ebar.comap Θ) := h1
    _ = Nat.card ((Ebar.comap Θ).map Θ) := (Subgroup.card_map_of_injective hΘ).symm
    _ = Nat.card Ebar := congrArg (fun H : Subgroup (MulAut R) => Nat.card H) hmap

theorem bridgeSub_fixed {p : ℕ} (hp : p.Prime) {R : Type} [Group R] {Γ : Type*} [Group Γ]
    {G : Subgroup Γ} {F₀ : Γ →* Γ} (hstab : ∀ g ∈ G, F₀ g ∈ G)
    (hfix : ∀ g ∈ G, endPow F₀ p g = g) {ρ : R →* Γ} {Θ : G →* MulAut R}
    (hρ : Function.Injective ρ) (hΘ : Function.Injective Θ)
    (hconj : ∀ (g : G) (r : R), ρ (Θ g r) = (g : Γ) * ρ r * (g : Γ)⁻¹) {f : MulAut R} {j : ℕ}
    (hj : ¬ p ∣ j) (hfj : ∀ r, ρ (f r) = (endPow F₀ j) (ρ r)) {Ebar : Subgroup (MulAut R)}
    (hcomm : ∀ e ∈ Ebar, e * f = f * e) : ∀ x ∈ bridgeSub Θ Ebar, F₀ x = x := by
  intro x hx
  have hxG : x ∈ G := bridgeSub_le Θ Ebar hx
  let g : G := ⟨x, hxG⟩
  have hgx : (g : Γ) = x := rfl
  have hgEbar : Θ g ∈ Ebar := (mem_bridgeSub Θ Ebar g).mp (by rw [hgx]; exact hx)
  have hcomm' : Θ g * f = f * Θ g := hcomm (Θ g) hgEbar
  have hconj_eq : f * Θ g * f⁻¹ = Θ g := by
    rw [← hcomm']
    group
  have hconj2 := absBridge_conj hstab hρ hconj hfj g
  have hTheta_eq : Θ ⟨endPow F₀ j g, endPow_mem hstab j g.2⟩ = Θ g := by
    rw [← hconj2, hconj_eq]
  have hsub : (⟨endPow F₀ j g, endPow_mem hstab j g.2⟩ : G) = g := hΘ hTheta_eq
  have hfixj : endPow F₀ j g = g := congrArg Subtype.val hsub
  have hF0g : F₀ g = g := (endPow_fixed_iff hp (hfix g g.2) hj).mp hfixj
  rw [← hgx]
  exact hF0g

theorem bridgeSub_sat0 {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)} {Γ : Type*} [Group Γ]
    {G : Subgroup Γ} {F₀ : Γ →* Γ} {ρ : R →* Γ} {Θ : G →* MulAut R}
    (hρ : Function.Injective ρ) (hρG : ∀ r, ρ r ∈ G) (hΘ : Function.Injective Θ)
    (hI : ∀ φ, φ ∈ I ↔ ∃ g, Θ g = φ)
    (hconj : ∀ (g : G) (r : R), ρ (Θ g r) = (g : Γ) * ρ r * (g : Γ)⁻¹)
    (hrec : ∀ u ∈ I, GGL45IsPElt p u → ∃ r : R, u = MulAut.conj r) {f : MulAut R} {j : ℕ}
    (hfj : ∀ r, ρ (f r) = (endPow F₀ j) (ρ r)) {Ebar : Subgroup (MulAut R)}
    (hEI : ∀ e ∈ Ebar, e ∈ I)
    (hsat : ∀ r : R, r ^ p = 1 → (∀ e ∈ Ebar, e r = r) → f r = r → MulAut.conj r ∈ Ebar) :
    AbsSat0 p G F₀ (bridgeSub Θ Ebar) := by
  intro y hyG hyp hcent hF0y
  have hI_mem : Θ ⟨y, hyG⟩ ∈ I := (hI (Θ ⟨y, hyG⟩)).2 ⟨⟨y, hyG⟩, rfl⟩
  have hIsP : GGL45IsPElt p (Θ ⟨y, hyG⟩) := by
    refine ⟨1, ?_⟩
    have hg : (⟨y, hyG⟩ : G) ^ p = 1 := by
      apply Subtype.ext
      simpa [Subgroup.coe_pow] using hyp
    rw [pow_one, ← map_pow, hg, map_one]
  obtain ⟨r, hr⟩ := hrec (Θ ⟨y, hyG⟩) hI_mem hIsP
  have htheta : Θ ⟨ρ r, hρG r⟩ = MulAut.conj r := absBridge_theta_rho hρ hρG hconj r
  have hEq : (⟨ρ r, hρG r⟩ : G) = ⟨y, hyG⟩ := hΘ (by rw [htheta, hr])
  have hrho : ρ r = y := congrArg Subtype.val hEq
  have hrp : r ^ p = 1 := by
    apply hρ
    rw [map_pow, hrho, hyp, map_one]
  have her : ∀ e ∈ Ebar, e r = r := by
    intro e he
    obtain ⟨h, hh⟩ := (hI e).1 (hEI e he)
    have hmem : (h : Γ) ∈ bridgeSub Θ Ebar :=
      (mem_bridgeSub Θ Ebar h).mpr (by rw [hh]; exact he)
    have hhy : (h : Γ) * y = y * (h : Γ) := (hcent (h : Γ) hmem).symm
    have hval : ρ (Θ h r) = ρ r := by
      rw [hconj h r, hrho, hhy]
      group
    have hth : Θ h r = r := hρ hval
    rw [← hh]
    exact hth
  have hfr : f r = r := by
    apply hρ
    rw [hfj r, hrho, endPow_apply]
    exact Function.iterate_fixed hF0y j
  exact (mem_bridgeSub Θ Ebar ⟨y, hyG⟩).mpr (by rw [hr]; exact hsat r hrp her hfr)

private theorem eA5_mem_bridgeSub_iff {R : Type} [Group R] {Γ : Type*} [Group Γ] {G : Subgroup Γ}
    (Θ : G →* MulAut R) (Ebar : Subgroup (MulAut R)) (x : Γ) :
    x ∈ bridgeSub Θ Ebar ↔ ∃ g : G, Θ g ∈ Ebar ∧ (g : Γ) = x := by
  rw [bridgeSub, Subgroup.mem_map]
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g, (Subgroup.mem_comap).1 hg, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g, (Subgroup.mem_comap).2 hg, rfl⟩

theorem cip_iff_pCent {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)} {Γ : Type*} [Group Γ]
    {G : Subgroup Γ} {Θ : G →* MulAut R} (hΘ : Function.Injective Θ)
    (hI : ∀ φ, φ ∈ I ↔ ∃ g, Θ g = φ) {Ebar : Subgroup (MulAut R)}
    (hEI : ∀ e ∈ Ebar, e ∈ I) (g : G) :
    GGL45NtCIp p I Ebar (Θ g) ↔ (g : Γ) ∈ pCent p G (bridgeSub Θ Ebar) := by
  constructor
  · intro h
    unfold GGL45NtCIp GGL45IsPElt at h
    simp only [pCent, Set.mem_setOf_eq]
    refine ⟨g.2, ?_, ?_⟩
    · intro x hx
      obtain ⟨gx, hgxE, rfl⟩ := (eA5_mem_bridgeSub_iff Θ Ebar x).1 hx
      have hc : Θ g * Θ gx = Θ gx * Θ g := h.2.1 _ hgxE
      have hgx : g * gx = gx * g := hΘ (by rw [map_mul, map_mul, hc])
      simpa using congrArg Subtype.val hgx
    · obtain ⟨k, hk⟩ := h.2.2
      refine ⟨k, ?_⟩
      have hg1 : g ^ p ^ k = 1 := hΘ (by rw [map_pow, hk, map_one])
      rw [← Subgroup.coe_pow, hg1, Subgroup.coe_one]
  · intro h
    simp only [pCent, Set.mem_setOf_eq] at h
    unfold GGL45NtCIp GGL45IsPElt
    refine ⟨(hI (Θ g)).2 ⟨g, rfl⟩, ?_, ?_⟩
    · intro e he
      obtain ⟨k, hk⟩ := (hI e).1 (hEI e he)
      have hmem : ((k : G) : Γ) ∈ bridgeSub Θ Ebar :=
        (eA5_mem_bridgeSub_iff Θ Ebar (k : Γ)).2 ⟨k, by rwa [hk], rfl⟩
      have hc : (g : Γ) * (k : Γ) = (k : Γ) * (g : Γ) := h.2.1 _ hmem
      have hgk : g * k = k * g := Subtype.ext (by simpa using hc)
      rw [← hk, ← map_mul, ← map_mul, hgk]
    · obtain ⟨k, hk⟩ := h.2.2
      refine ⟨k, ?_⟩
      have h1 : g ^ p ^ k = 1 := by
        apply Subtype.ext
        rw [Subgroup.coe_pow, hk, Subgroup.coe_one]
      rw [← map_pow, h1, map_one]

private lemma eA6_sum_reindex {p : ℕ} (hp : p.Prime) {j : ℕ} (hj : ¬ p ∣ j) (N : ℕ) :
    ∑ i ∈ Finset.range p, N ^ ((j * i) % p) = ∑ i ∈ Finset.range p, N ^ i := by
  have hcop : Nat.gcd p j = 1 := hp.coprime_iff_not_dvd.mpr hj
  have hmod_inj : ∀ a₁ a₂, a₁ < p → a₂ < p → (j * a₁) % p = (j * a₂) % p → a₁ = a₂ := by
    intro a₁ a₂ h₁ h₂ heq
    have hmod' : j * a₁ ≡ j * a₂ [MOD p] := heq
    exact Nat.ModEq.eq_of_lt_of_lt (Nat.ModEq.cancel_left_of_coprime hcop hmod') h₁ h₂
  have hinj : Function.Injective
      (fun i : Fin p => (⟨(j * i.val) % p, Nat.mod_lt _ hp.pos⟩ : Fin p)) := by
    intro i₁ i₂ h
    exact Fin.ext (hmod_inj i₁.val i₂.val i₁.isLt i₂.isLt (congrArg Fin.val h))
  have hsurj : Function.Surjective
      (fun i : Fin p => (⟨(j * i.val) % p, Nat.mod_lt _ hp.pos⟩ : Fin p)) :=
    Finite.injective_iff_surjective.mp hinj
  apply Finset.sum_bij (fun a _ => (j * a) % p)
  · intro a _
    exact Finset.mem_range.mpr (Nat.mod_lt _ hp.pos)
  · intro a₁ ha₁ a₂ ha₂ heq
    exact hmod_inj a₁ a₂ (Finset.mem_range.mp ha₁) (Finset.mem_range.mp ha₂) heq
  · intro c hc
    obtain ⟨a, ha⟩ := hsurj ⟨c, Finset.mem_range.mp hc⟩
    exact ⟨a.val, Finset.mem_range.mpr a.isLt, congrArg Fin.val ha⟩
  · intro a _
    rfl

private lemma eA6_modeq_pow_mod {N p j i m : ℕ} (hNp : N ^ p ≡ 1 [MOD m]) :
    N ^ (j * i) ≡ N ^ ((j * i) % p) [MOD m] := by
  have hleft : N ^ (j * i) = (N ^ p) ^ ((j * i) / p) * N ^ ((j * i) % p) := by
    rw [← pow_mul, ← pow_add]
    congr 1
    exact (Nat.div_add_mod (j * i) p).symm
  have hq : (N ^ p) ^ ((j * i) / p) ≡ 1 ^ ((j * i) / p) [MOD m] :=
    Nat.ModEq.pow ((j * i) / p) hNp
  have hmul : (N ^ p) ^ ((j * i) / p) * N ^ ((j * i) % p) ≡
      1 ^ ((j * i) / p) * N ^ ((j * i) % p) [MOD m] :=
    Nat.ModEq.mul_right (N ^ ((j * i) % p)) hq
  rw [hleft]
  simpa using hmul

private lemma eA6_modeq_sum {p N j : ℕ} (hp : p.Prime) (hj : ¬ p ∣ j) {m : ℕ}
    (hNp : N ^ p ≡ 1 [MOD m]) :
    ∑ i ∈ Finset.range p, (N ^ j) ^ i ≡ ∑ i ∈ Finset.range p, N ^ i [MOD m] := by
  have h1 : ∑ i ∈ Finset.range p, (N ^ j) ^ i ≡
      ∑ i ∈ Finset.range p, N ^ ((j * i) % p) [MOD m] := by
    apply Nat.ModEq.sum
    intro i _
    rw [← pow_mul]
    exact eA6_modeq_pow_mod (N := N) (p := p) (j := j) (i := i) hNp
  rw [eA6_sum_reindex hp hj N] at h1
  exact h1

theorem norm_reindex {Γ : Type*} [Group Γ] {F₀ : Γ →* Γ} {p : ℕ} (hp : p.Prime) {N j : ℕ}
    (hj : ¬ p ∣ j) {b : Γ} (hb : F₀ b = b ^ N) (hbp : endPow F₀ p b = b) :
    b ^ ∑ i ∈ Finset.range p, (N ^ j) ^ i = b ^ ∑ i ∈ Finset.range p, N ^ i := by
  have hbp' : b ^ N ^ p = b := by
    rw [← endPow_pow hb p]
    exact hbp
  have hNp : N ^ p ≡ 1 [MOD orderOf b] :=
    (pow_eq_pow_iff_modEq (x := b) (n := N ^ p) (m := 1)).1 (by rw [pow_one]; exact hbp')
  exact (pow_eq_pow_iff_modEq (x := b)
    (n := ∑ i ∈ Finset.range p, (N ^ j) ^ i) (m := ∑ i ∈ Finset.range p, N ^ i)).2
    (eA6_modeq_sum hp hj hNp)

theorem geo_comm_of_absGeo {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)} {Γ : Type*} [Group Γ]
    {G : Subgroup Γ} {F₀ : Γ →* Γ} {Θ : G →* MulAut R} (hΘ : Function.Injective Θ)
    (hI : ∀ φ, φ ∈ I ↔ ∃ g, Θ g = φ) {Ebar : Subgroup (MulAut R)} (hEI : ∀ e ∈ Ebar, e ∈ I)
    (hAbs : AbsGeo p G F₀ (bridgeSub Θ Ebar)) :
    ∀ u v : MulAut R, GGL45NtCIp p I Ebar u → GGL45NtCIp p I Ebar v → u * v = v * u := by
  intro u v hu hv
  obtain ⟨g, rfl⟩ := (hI u).1 hu.1
  obtain ⟨h, rfl⟩ := (hI v).1 hv.1
  have hgp : (g : Γ) ∈ pCent p G (bridgeSub Θ Ebar) := (cip_iff_pCent hΘ hI hEI g).1 hu
  have hhp : (h : Γ) ∈ pCent p G (bridgeSub Θ Ebar) := (cip_iff_pCent hΘ hI hEI h).1 hv
  have hc : (g : Γ) * (h : Γ) = (h : Γ) * (g : Γ) := hAbs.1 (g : Γ) hgp (h : Γ) hhp
  have hgh : g * h = h * g := Subtype.ext (by simpa using hc)
  rw [← map_mul, ← map_mul, hgh]

theorem geo_central_of_absGeo {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)} {Γ : Type*}
    [Group Γ] {G : Subgroup Γ} {F₀ : Γ →* Γ} {Θ : G →* MulAut R} (hΘ : Function.Injective Θ)
    (hI : ∀ φ, φ ∈ I ↔ ∃ g, Θ g = φ) {Ebar : Subgroup (MulAut R)} (hEI : ∀ e ∈ Ebar, e ∈ I)
    (hAbs : AbsGeo p G F₀ (bridgeSub Θ Ebar)) :
    ∀ u : MulAut R, GGL45NtCIp p I Ebar u → ∀ w ∈ I, (∀ e ∈ Ebar, w * e = e * w) →
      w * u = u * w := by
  intro u hu w hwI hwcomm
  obtain ⟨g, rfl⟩ := (hI u).1 hu.1
  obtain ⟨h, rfl⟩ := (hI w).1 hwI
  have hgp : (g : Γ) ∈ pCent p G (bridgeSub Θ Ebar) := (cip_iff_pCent hΘ hI hEI g).1 hu
  have hwcent : ∀ e ∈ bridgeSub Θ Ebar, (h : Γ) * e = e * (h : Γ) := by
    intro e he
    obtain ⟨k, hkE, rfl⟩ := (eA5_mem_bridgeSub_iff Θ Ebar e).1 he
    have hc : Θ h * Θ k = Θ k * Θ h := hwcomm _ hkE
    have hhk : h * k = k * h := hΘ (by rw [map_mul, map_mul, hc])
    simpa using congrArg Subtype.val hhk
  have hc : (h : Γ) * (g : Γ) = (g : Γ) * (h : Γ) :=
    hAbs.2.1 (g : Γ) hgp (h : Γ) h.2 hwcent
  have hgh : h * g = g * h := Subtype.ext (by simpa using hc)
  rw [← map_mul, ← map_mul, hgh]

theorem geo_power_of_absGeo {p : ℕ} (hp : p.Prime) {R : Type} [Group R] {I : Set (MulAut R)}
    {Γ : Type*} [Group Γ] {G : Subgroup Γ} {F₀ : Γ →* Γ} (hstab : ∀ g ∈ G, F₀ g ∈ G)
    (hfix : ∀ g ∈ G, endPow F₀ p g = g) {ρ : R →* Γ} {Θ : G →* MulAut R}
    (hρ : Function.Injective ρ) (hΘ : Function.Injective Θ)
    (hI : ∀ φ, φ ∈ I ↔ ∃ g, Θ g = φ)
    (hconj : ∀ (g : G) (r : R), ρ (Θ g r) = (g : Γ) * ρ r * (g : Γ)⁻¹) {f : MulAut R} {j : ℕ}
    (hj : ¬ p ∣ j) (hfj : ∀ r, ρ (f r) = (endPow F₀ j) (ρ r)) {Ebar : Subgroup (MulAut R)}
    (hEI : ∀ e ∈ Ebar, e ∈ I) (hAbs : AbsGeo p G F₀ (bridgeSub Θ Ebar)) :
    ∃ N : ℕ, 2 ≤ N ∧ (∀ u : MulAut R, GGL45NtCIp p I Ebar u → f * u * f⁻¹ = u ^ N) ∧
      ∀ a : MulAut R, GGL45NtCIp p I Ebar a → f * a * f⁻¹ = a →
        ∃ b : MulAut R, GGL45NtCIp p I Ebar b ∧ a = b ^ ∑ i ∈ Finset.range p, N ^ i := by
  obtain ⟨-, -, N, hN2, hNpow, hNnorm⟩ := hAbs
  have hj0 : j ≠ 0 := by rintro rfl; exact hj (dvd_zero p)
  have hN2j : 2 ≤ N ^ j := by
    have h1 : 1 < N := by omega
    exact Nat.one_lt_pow hj0 h1
  refine ⟨N ^ j, hN2j, ?_, ?_⟩
  · intro u hu
    obtain ⟨g, hg⟩ := (hI u).1 hu.1
    have hu' : GGL45NtCIp p I Ebar (Θ g) := by rwa [hg]
    have hgpc : (g : Γ) ∈ pCent p G (bridgeSub Θ Ebar) :=
      (cip_iff_pCent hΘ hI hEI g).1 hu'
    have hFg : F₀ (g : Γ) = (g : Γ) ^ N := hNpow (g : Γ) hgpc
    have hstep := absBridge_conj hstab hρ hconj hfj g
    have harg : (⟨endPow F₀ j (g : Γ), endPow_mem hstab j g.2⟩ : G) = g ^ N ^ j := by
      apply Subtype.ext
      show endPow F₀ j (g : Γ) = ((g ^ N ^ j : G) : Γ)
      rw [Subgroup.coe_pow]
      exact endPow_pow hFg j
    rw [← hg, hstep, harg]
    exact map_pow Θ g (N ^ j)
  · intro a ha hfixa
    obtain ⟨g, hg⟩ := (hI a).1 ha.1
    have ha' : GGL45NtCIp p I Ebar (Θ g) := by rwa [hg]
    have hgpc : (g : Γ) ∈ pCent p G (bridgeSub Θ Ebar) :=
      (cip_iff_pCent hΘ hI hEI g).1 ha'
    have hstep := absBridge_conj hstab hρ hconj hfj g
    have hfixg : endPow F₀ j (g : Γ) = (g : Γ) := by
      have h1 : Θ ⟨endPow F₀ j (g : Γ), endPow_mem hstab j g.2⟩ = Θ g := by
        rw [← hstep]
        rw [← hg] at hfixa
        exact hfixa
      exact congrArg Subtype.val (hΘ h1)
    have hF₀g : F₀ (g : Γ) = (g : Γ) :=
      (endPow_fixed_iff hp (hfix (g : Γ) g.2) hj).1 hfixg
    obtain ⟨b₀, hb₀pc, hb₀eq⟩ := hNnorm (g : Γ) hgpc hF₀g
    have hb₀G : b₀ ∈ G := hb₀pc.1
    refine ⟨Θ ⟨b₀, hb₀G⟩, (cip_iff_pCent hΘ hI hEI ⟨b₀, hb₀G⟩).2 hb₀pc, ?_⟩
    have hb : F₀ b₀ = b₀ ^ N := hNpow b₀ hb₀pc
    have hbp : endPow F₀ p b₀ = b₀ := hfix b₀ hb₀G
    have hnr : b₀ ^ ∑ i ∈ Finset.range p, (N ^ j) ^ i = b₀ ^ ∑ i ∈ Finset.range p, N ^ i :=
      norm_reindex hp hj hb hbp
    have hG_eq : (⟨b₀, hb₀G⟩ : G) ^ (∑ i ∈ Finset.range p, N ^ i) =
        (⟨b₀, hb₀G⟩ : G) ^ (∑ i ∈ Finset.range p, (N ^ j) ^ i) := by
      apply Subtype.ext
      simp only [Subgroup.coe_pow]
      exact hnr.symm
    rw [← hg]
    calc Θ g = Θ (⟨b₀, hb₀G⟩ ^ (∑ i ∈ Finset.range p, N ^ i)) := by
            congr 1
            apply Subtype.ext
            simp only [Subgroup.coe_pow]
            exact hb₀eq
      _ = (Θ ⟨b₀, hb₀G⟩) ^ (∑ i ∈ Finset.range p, N ^ i) := map_pow Θ _ _
      _ = (Θ ⟨b₀, hb₀G⟩) ^ (∑ i ∈ Finset.range p, (N ^ j) ^ i) := by
            have hh := congrArg (fun x : G => Θ x) hG_eq
            simpa only [map_pow] using hh

theorem geo_of_absBridge {p : ℕ} (hp : p.Prime) {R : Type} [Group R] {I F : Set (MulAut R)}
    {Γ : Type*} [Group Γ] {G : Subgroup Γ} {F₀ : Γ →* Γ} (hstab : ∀ g ∈ G, F₀ g ∈ G)
    (hfix : ∀ g ∈ G, endPow F₀ p g = g) (hbr : AbsBridge p I F G F₀)
    (hrec : ∀ u ∈ I, GGL45IsPElt p u → ∃ r : R, u = MulAut.conj r) (halg : AbsGeoAt p G F₀)
    (Ebar : Subgroup (MulAut R)) (f : MulAut R) (hfF : f ∈ F) (hfp : orderOf f = p)
    (hEab : IsElemAbelian p Ebar) (hEcard : p ^ 2 ≤ Nat.card Ebar) (hEI : ∀ e ∈ Ebar, e ∈ I)
    (hcomm : ∀ e ∈ Ebar, e * f = f * e)
    (hsat : ∀ r : R, r ^ p = 1 → (∀ e ∈ Ebar, e r = r) → f r = r → MulAut.conj r ∈ Ebar) :
    GGL45NtGeo p I Ebar f := by
  obtain ⟨ρ, Θ, hρ, hρG, hΘ, hI, hconj, hF⟩ := hbr
  obtain ⟨j, hj, hfj⟩ := hF f hfF hfp
  have hEΘ : ∀ e ∈ Ebar, ∃ g : G, Θ g = e := fun e he => (hI e).1 (hEI e he)
  have hAbs : AbsGeo p G F₀ (bridgeSub Θ Ebar) :=
    halg (bridgeSub Θ Ebar) (bridgeSub_le Θ Ebar) (bridgeSub_isElemAbelian hΘ hEab)
      (by rw [bridgeSub_card hΘ hEΘ]; exact hEcard)
      (bridgeSub_fixed hp hstab hfix hρ hΘ hconj hj hfj hcomm)
      (bridgeSub_sat0 hρ hρG hΘ hI hconj hrec hfj hEI hsat)
  exact ⟨geo_comm_of_absGeo hΘ hI hEI hAbs, geo_central_of_absGeo hΘ hI hEI hAbs,
    geo_power_of_absGeo hp hstab hfix hρ hΘ hI hconj hj hfj hEI hAbs⟩

end CFSG.HardMathSupport.C14Exc
