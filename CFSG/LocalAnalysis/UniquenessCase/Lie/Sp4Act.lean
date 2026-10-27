module

public import CFSG.LocalAnalysis.UniquenessCase.Lie.Sp4
public import CFSG.LocalAnalysis.UniquenessCase.Lie.Shared
public import CFSG.Quasithin.EmptyFaithful.T1521SSp4Std

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl (torusHom torus coe_torusHom statedSp_ext
  mem_statedSp_iff torusHom_injective)
open Subgroup Matrix

variable {K : Type} [Field K]

variable (K) in
abbrev uc22pwI2RhoE : Monoid.End (Fin 2 → Kˣ) := uc22pwI2Rho K

theorem uc22pwI2Rho_apply (t : Fin 2 → Kˣ) :
    uc22pwI2RhoE K t = ![t 0 * t 1, t 0 * (t 1)⁻¹] := rfl

theorem uc22pwI2Rho_sq (t : Fin 2 → Kˣ) : uc22pwI2RhoE K (uc22pwI2RhoE K t) = t ^ 2 := by
  have h0 : ((t 0 : Kˣ) : K) ≠ 0 := (t 0).ne_zero
  have h1 : ((t 1 : Kˣ) : K) ≠ 0 := (t 1).ne_zero
  ext i
  fin_cases i <;> simp [uc22pwI2Rho_apply, pow_two] <;> field_simp

theorem uc22pwI2Rho_pow_two (t : Fin 2 → Kˣ) : ((uc22pwI2RhoE K) ^ 2) t = t ^ 2 := by
  rw [pow_two]
  exact uc22pwI2Rho_sq t

theorem uc22pwI2Rho_pow_even (l : ℕ) (t : Fin 2 → Kˣ) :
    ((uc22pwI2RhoE K) ^ (2 * l)) t = t ^ 2 ^ l := by
  induction l generalizing t with
  | zero => simp
  | succ l ih =>
    rw [Nat.mul_succ, pow_add, pow_succ' 2 l]
    change ((uc22pwI2RhoE K) ^ (2 * l)) (((uc22pwI2RhoE K) ^ 2) t) = _
    rw [uc22pwI2Rho_pow_two, ih, ← pow_mul]

theorem uc22pwI2Rho_pow_odd (l : ℕ) (t : Fin 2 → Kˣ) :
    ((uc22pwI2RhoE K) ^ (2 * l + 1)) t = uc22pwI2RhoE K (t ^ 2 ^ l) := by
  rw [pow_succ]
  change ((uc22pwI2RhoE K) ^ (2 * l)) (uc22pwI2RhoE K t) = _
  rw [uc22pwI2Rho_pow_even, map_pow]

theorem uc22pwI2_dvd_of_forall_pow [Finite K] {n l : ℕ} (hn : Nat.card K = 2 ^ n)
    (h : ∀ x : K, x ^ 2 ^ l = x) : n ∣ l := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hord : orderOf g = 2 ^ n - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units, hn]
  have hpos : 1 ≤ 2 ^ l := Nat.one_le_two_pow
  have h3 : g ^ 2 ^ l = g := Units.ext (by simpa using h (g : K))
  have hg1 : g ^ (2 ^ l - 1) = 1 := by
    refine (mul_left_inj g).1 ?_
    rw [one_mul, ← pow_succ, Nat.sub_add_cancel hpos]
    exact h3
  have hd : 2 ^ n - 1 ∣ 2 ^ l - 1 := hord ▸ orderOf_dvd_of_pow_eq_one hg1
  have hgcd := Nat.pow_sub_one_gcd_pow_sub_one 2 n l
  rw [Nat.gcd_eq_left hd] at hgcd
  have h4 : 2 ^ Nat.gcd n l = 2 ^ n := by
    have := Nat.one_le_two_pow (n := Nat.gcd n l)
    have := Nat.one_le_two_pow (n := n)
    omega
  have h5 : Nat.gcd n l = n := Nat.pow_right_injective (le_refl 2) h4
  exact h5 ▸ Nat.gcd_dvd_right n l

variable (K) in
@[expose] def uc22pwI2Fixed (k : ℕ) (a : Kˣ) : Fin 2 → Kˣ := ![a ^ (1 + 2 ^ k), a ^ 2 ^ k]

theorem uc22pwI2_rho_pow_fixed {k m : ℕ} (hdvd : 2 * k + 1 ∣ m) {a : Kˣ}
    (ha : a ^ 2 ^ (2 * k + 1) = a) :
    ((uc22pwI2RhoE K) ^ m) (uc22pwI2Fixed K k a) = uc22pwI2Fixed K k a := by
  set s := uc22pwI2Fixed K k a with hs
  have hsfix : ∀ i, s i ^ 2 ^ (2 * k + 1) = s i := by
    intro i
    fin_cases i
    · show (a ^ (1 + 2 ^ k)) ^ 2 ^ (2 * k + 1) = a ^ (1 + 2 ^ k)
      rw [← pow_mul, mul_comm, pow_mul, ha]
    · show (a ^ 2 ^ k) ^ 2 ^ (2 * k + 1) = a ^ 2 ^ k
      rw [← pow_mul, mul_comm, pow_mul, ha]
  have hit : ∀ (r : ℕ) (u : Kˣ), u ^ 2 ^ (2 * k + 1) = u → u ^ 2 ^ ((2 * k + 1) * r) = u := by
    intro r u hu
    induction r with
    | zero => simp
    | succ r ih =>
      rw [Nat.mul_succ, pow_add, pow_mul, ih, hu]
  rcases Nat.even_or_odd' m with ⟨l, hl | hl⟩
  ·
    subst hl
    have hl' : 2 * k + 1 ∣ l := by
      have h2 : 2 * k + 1 ∣ 2 * l := hdvd
      exact (odd_two_mul_add_one k).coprime_two_right.dvd_of_dvd_mul_left h2
    obtain ⟨r, rfl⟩ := hl'
    rw [uc22pwI2Rho_pow_even]
    funext i
    exact hit r (s i) (hsfix i)
  ·
    subst hl
    obtain ⟨r, hr⟩ := hdvd
    have hodd : Odd ((2 * k + 1) * r) := hr ▸ odd_two_mul_add_one l
    obtain ⟨r', rfl⟩ := (Nat.odd_mul.mp hodd).2
    have hl : l = (2 * k + 1) * r' + k := by nlinarith [hr]
    have hsl : s ^ 2 ^ l = fun i => s i ^ 2 ^ k := by
      funext i
      rw [Pi.pow_apply, hl, pow_add, pow_mul, hit r' (s i) (hsfix i)]
    rw [uc22pwI2Rho_pow_odd, hsl]
    have hc : (1 + 2 ^ k) * 2 ^ k + 2 ^ k * 2 ^ k = 2 ^ k + 2 ^ (2 * k + 1) := by ring
    funext i
    fin_cases i
    · show (a ^ (1 + 2 ^ k)) ^ 2 ^ k * (a ^ 2 ^ k) ^ 2 ^ k = a ^ (1 + 2 ^ k)
      rw [← pow_mul, ← pow_mul, ← pow_add, hc, pow_add, ha, add_comm, pow_add, pow_one, mul_comm]
    · show (a ^ (1 + 2 ^ k)) ^ 2 ^ k * ((a ^ 2 ^ k) ^ 2 ^ k)⁻¹ = a ^ 2 ^ k
      rw [mul_inv_eq_iff_eq_mul, ← pow_mul, ← pow_mul, ← pow_add]
      congr 1
      ring

theorem uc22pwI2_dvd_of_rho_pow [Finite K] {n e m' m k : ℕ} (hm' : Odd m') (hn : Nat.card K = 2 ^ n)
    (hn2 : 2 ≤ n) (hnem : n = 2 ^ e * m')
    (h : ∀ t : Fin 2 → Kˣ, (((uc22pwI2RhoE K) ^ m) ^ 2 ^ k) t = t) : m' ∣ m := by
  rw [← pow_mul] at h
  rcases Nat.even_or_odd' (m * 2 ^ k) with ⟨l, hl | hl⟩
  · rw [hl] at h
    have hfix : ∀ x : K, x ^ 2 ^ l = x := by
      intro x
      by_cases hx : x = 0
      · subst hx
        simp
      · have h1 := congrFun (h (fun _ => Units.mk0 x hx)) 0
        rw [uc22pwI2Rho_pow_even] at h1
        have h2 := congrArg (fun u : Kˣ => (u : K)) h1
        simpa using h2
    have hnl : n ∣ l := uc22pwI2_dvd_of_forall_pow hn hfix
    have hm'l : m' ∣ l := (Dvd.intro_left _ hnem.symm).trans hnl
    have h2 : m' ∣ m * 2 ^ k := by
      rw [hl]
      exact Dvd.dvd.mul_left hm'l 2
    exact (Nat.Coprime.pow_right k hm'.coprime_two_right).dvd_of_dvd_mul_right h2
  · exfalso
    rw [hl] at h
    have hcard : 1 < Nat.card Kˣ := by
      rw [Nat.card_units, hn]
      have : 4 ≤ 2 ^ n := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
      omega
    haveI : Nontrivial Kˣ := Finite.one_lt_card_iff_nontrivial.mp hcard
    obtain ⟨a, ha⟩ := exists_ne (1 : Kˣ)
    have h1 := h ![a, 1]
    rw [uc22pwI2Rho_pow_odd] at h1
    have h2 : (![a, 1] : Fin 2 → Kˣ) ^ 2 ^ l = ![a ^ 2 ^ l, 1] := by
      funext i
      fin_cases i <;> simp
    rw [h2] at h1
    have h3 := congrFun h1 0
    have h4 := congrFun h1 1
    simp [uc22pwI2Rho_apply] at h3 h4
    exact ha (h3.symm.trans h4)

variable (K) in
@[expose] def uc22pwI2Stab : Subgroup (MulAut (StatedSp 2 K)) where
  carrier := {β | ∀ y, y ∈ unipotent 2 K ↔ β y ∈ unipotent 2 K}
  mul_mem' := fun {β₁ β₂} h₁ h₂ y => (h₂ y).trans (h₁ (β₂ y))
  one_mem' := fun y => Iff.rfl
  inv_mem' := fun {β} h y => by
    rw [h (β⁻¹ y)]
    simp

theorem mem_uc22pwI2Stab {β : MulAut (StatedSp 2 K)} :
    β ∈ uc22pwI2Stab K ↔ ∀ y, y ∈ unipotent 2 K ↔ β y ∈ unipotent 2 K := Iff.rfl

theorem uc22pwI2Stab_borel {β : MulAut (StatedSp 2 K)} (hβ : β ∈ uc22pwI2Stab K) {b : StatedSp 2 K}
    (hb : b ∈ borelSubgroup 2 K) : β b ∈ borelSubgroup 2 K := by
  rw [← normalizer_unipotent (r := 2) (K := K)] at hb ⊢
  rw [Subgroup.mem_normalizer_iff] at hb ⊢
  intro h
  have h1 : β (β⁻¹ h) = h := by simp
  have h2 := hβ (β⁻¹ h)
  have h3 := hb (β⁻¹ h)
  have h4 := hβ (b * β⁻¹ h * b⁻¹)
  rw [map_mul, map_mul, map_inv, h1] at h4
  rw [h1] at h2
  exact h2.symm.trans (h3.trans h4)

variable (K) in
@[expose] noncomputable def uc22pwI2ActOf (β : MulAut (StatedSp 2 K)) (hβ : β ∈ uc22pwI2Stab K) :
    (Fin 2 → Kˣ) →* (Fin 2 → Kˣ) :=
  (diagHom 2 K).comp
    ((MonoidHom.codRestrict (β.toMonoidHom.comp (borelSubgroup 2 K).subtype) (borelSubgroup 2 K)
      fun b => uc22pwI2Stab_borel hβ b.2).comp
      (MonoidHom.codRestrict torusHom (borelSubgroup 2 K) fun t => torus_le_borelSubgroup ⟨t, rfl⟩))

theorem uc22pwI2Act_spec {β : MulAut (StatedSp 2 K)} (hβ : β ∈ uc22pwI2Stab K) (t : Fin 2 → Kˣ) :
    β (torusHom t) * (torusHom (uc22pwI2ActOf K β hβ t))⁻¹ ∈ unipotent 2 K :=
  uc22pwI2_sp4_decomp (uc22pwI2Stab_borel hβ (torus_le_borelSubgroup ⟨t, rfl⟩))

theorem uc22pwI2Act_eq {β : MulAut (StatedSp 2 K)} (hβ : β ∈ uc22pwI2Stab K) {t s : Fin 2 → Kˣ}
    (h : β (torusHom t) * (torusHom s)⁻¹ ∈ unipotent 2 K) : uc22pwI2ActOf K β hβ t = s := by
  have h1 := uc22pwI2Act_spec hβ t
  have h2 : torusHom (uc22pwI2ActOf K β hβ t * s⁻¹) ∈ unipotent 2 K := by
    have := Subgroup.mul_mem _ (Subgroup.inv_mem _ h1) h
    rw [map_mul, map_inv]
    convert this using 1
    group
  have h3 : torusHom (uc22pwI2ActOf K β hβ t * s⁻¹) = 1 :=
    Subgroup.disjoint_def.mp uc22pwI2_sp4_borel.2 h2 ⟨_, rfl⟩
  have h4 : uc22pwI2ActOf K β hβ t * s⁻¹ = 1 := torusHom_injective (h3.trans (map_one _).symm)
  exact mul_inv_eq_one.mp h4

theorem uc22pwI2Act_mul {β₁ β₂ : MulAut (StatedSp 2 K)} (h₁ : β₁ ∈ uc22pwI2Stab K)
    (h₂ : β₂ ∈ uc22pwI2Stab K) (t : Fin 2 → Kˣ) :
    uc22pwI2ActOf K (β₁ * β₂) (Subgroup.mul_mem _ h₁ h₂) t =
      uc22pwI2ActOf K β₁ h₁ (uc22pwI2ActOf K β₂ h₂ t) := by
  apply uc22pwI2Act_eq
  set s₂ := uc22pwI2ActOf K β₂ h₂ t with hs₂
  set s₁ := uc22pwI2ActOf K β₁ h₁ s₂ with hs₁
  have hu₂ := uc22pwI2Act_spec h₂ t
  have hu₁ := uc22pwI2Act_spec h₁ s₂
  have hu₂' : β₁ (β₂ (torusHom t) * (torusHom s₂)⁻¹) ∈ unipotent 2 K := (h₁ _).mp hu₂
  have : (β₁ * β₂) (torusHom t) * (torusHom s₁)⁻¹ =
      β₁ (β₂ (torusHom t) * (torusHom s₂)⁻¹) * (β₁ (torusHom s₂) * (torusHom s₁)⁻¹) := by
    simp only [MulAut.mul_apply, map_mul, map_inv]
    group
  rw [this]
  exact Subgroup.mul_mem _ hu₂' hu₁

theorem uc22pwI2Act_one (t : Fin 2 → Kˣ) :
    uc22pwI2ActOf K 1 (Subgroup.one_mem _) t = t := by
  apply uc22pwI2Act_eq
  simp

variable (K) in
@[expose] noncomputable def uc22pwI2ActHom : uc22pwI2Stab K →* Monoid.End (Fin 2 → Kˣ) where
  toFun β := uc22pwI2ActOf K β.1 β.2
  map_one' := MonoidHom.ext fun t => uc22pwI2Act_one t
  map_mul' β₁ β₂ := MonoidHom.ext fun t => uc22pwI2Act_mul β₁.2 β₂.2 t

theorem uc22pwI2_std_form [Finite K] [CharP K 2] {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n)
    {β : MulAut (StatedSp 2 K)} (hβ : β ∈ uc22pwI2Stab K) :
    ∃ (σ : K ≃+* K) (u : StatedSp 2 K) (s : Fin 2 → Kˣ) (ε : Bool), u ∈ unipotent 2 K ∧
      ∀ h : StatedSp 2 K, β h = u * torusHom s *
        fieldSp 2 K σ (if ε then CFSG.QuasithinUnique.Lin2.Five.tauSp h else h) * (u * torusHom s)⁻¹ := by
  have hproj_inj : Function.Injective (proj 2 K) :=
    (CFSG.QuasithinUnique.Lin2.Five.projEquiv K).injective
  set α : MulAut (StatedProj (StatedSp 2 K)) :=
    MulAut.congr (CFSG.QuasithinUnique.Lin2.Five.projEquiv K) β with hα_def
  have hαproj : ∀ g : StatedSp 2 K, α (proj 2 K g) = proj 2 K (β g) := by
    intro g
    rw [hα_def, MulAut.congr_apply]
    show (CFSG.QuasithinUnique.Lin2.Five.projEquiv K)
      (β ((CFSG.QuasithinUnique.Lin2.Five.projEquiv K).symm
        ((CFSG.QuasithinUnique.Lin2.Five.projEquiv K) g))) = _
    rw [MulEquiv.symm_apply_apply]
    rfl
  have hα : ∀ x, α x ∈ projUnipotent 2 K ↔ x ∈ projUnipotent 2 K := by
    intro x
    obtain ⟨g, rfl⟩ := proj_surjective x
    rw [hαproj, projUnipotent, Subgroup.mem_map_iff_mem hproj_inj,
      Subgroup.mem_map_iff_mem hproj_inj]
    exact (hβ g).symm
  obtain ⟨σ, u, s, ε, hu, hαeq⟩ := CFSG.Quasithin.Sp4.exists_standard_form hn hK hα
  refine ⟨σ, u, s, ε, hu, fun h => ?_⟩
  have h1 := congrArg (fun γ : MulAut (StatedProj (StatedSp 2 K)) => γ (proj 2 K h)) hαeq
  rw [hαproj] at h1
  apply hproj_inj
  rw [h1]
  cases ε
  · simp [MulAut.mul_apply, MulAut.conj_apply, fieldAut_proj, mul_assoc]
  · simp [MulAut.mul_apply, MulAut.conj_apply, fieldAut_proj,
      CFSG.QuasithinUnique.Lin2.Five.tauAut_proj, mul_assoc]

theorem uc22pwI2_act_eq_rho_pow [Finite K] [CharP K 2] {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n)
    {β : MulAut (StatedSp 2 K)} (hβ : β ∈ uc22pwI2Stab K) :
    ∃ m : ℕ, ∀ t, uc22pwI2ActOf K β hβ t = ((uc22pwI2RhoE K) ^ m) t := by
  obtain ⟨σ, u, s, ε, hu, hform⟩ := uc22pwI2_std_form hn hK hβ
  obtain ⟨i, hi⟩ := uc22pwlie_ringEquiv_pow σ
  refine ⟨2 * i + (if ε then 1 else 0), fun t => ?_⟩
  apply uc22pwI2Act_eq
  have hx : u * torusHom s ∈ borelSubgroup 2 K :=
    Subgroup.mul_mem _ (unipotent_le_borelSubgroup hu) (torus_le_borelSubgroup ⟨s, rfl⟩)
  have hin : (if ε then CFSG.QuasithinUnique.Lin2.Five.tauSp (torusHom t) else torusHom t) =
      torusHom (((uc22pwI2RhoE K) ^ (if ε then 1 else 0)) t) := by
    cases ε
    · simp
    · simp [uc22pwI2_sp4_tau_torus]
      rfl
  have hfield : ∀ t' : Fin 2 → Kˣ,
      fieldSp 2 K σ (torusHom t') = torusHom (((uc22pwI2RhoE K) ^ (2 * i)) t') := by
    intro t'
    rw [uc22pwI2_sp4_field_torus, uc22pwI2Rho_pow_even]
    congr 1
    funext j
    apply Units.ext
    simp [hi]
  have hβt : β (torusHom t) = u * torusHom s *
      torusHom (((uc22pwI2RhoE K) ^ (2 * i + (if ε then 1 else 0))) t) * (u * torusHom s)⁻¹ := by
    rw [hform, hin, hfield, pow_add]
    rfl
  rw [hβt]
  exact uc22pwI2_sp4_conj_torus_mem hx _

end CFSG.LocalAnalysis.UniquenessCase.UC22
