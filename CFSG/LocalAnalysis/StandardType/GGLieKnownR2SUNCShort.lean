module

public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2FixedPointOdd
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2ShortSU
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2GeoSUShort
public import CFSG.LieType.Universal.Unitary

public section

namespace CFSG.StandardType.LieKnownR2.PSU

open CFSG.Open CFSG.StandardType CFSG.StandardType.LieKnownR2.Short CFSG.LieType.Universal
open CFSG.LieType.RootSystem CFSG.LieType.BorelTits CFSG.StandardType.GGOppRadSpU
open CFSG.QuasithinUnique.B113Lie.Sp CFSG.LieType.Universal.Unitary

private lemma l10su5_exists_fixed_ne_zero_ne_one {F : Type} [Field F] [Finite F] [CharP F 2]
    {f : ℕ} (hc : Nat.card F = (2 ^ f) ^ 2) (hf : 2 ≤ f) :
    ∃ t : F, unitaryInvolution F 2 f t = t ∧ t ≠ 0 ∧ t ≠ 1 ∧ t ^ (2 ^ f - 1) = 1 := by
  classical
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
  have hord : orderOf g = Nat.card Fˣ := orderOf_eq_card_of_forall_mem_zpowers hg
  have hcard : Nat.card Fˣ = (2 ^ f) ^ 2 - 1 := by
    haveI : Fintype F := Fintype.ofFinite F
    rw [Nat.card_eq_fintype_card, Fintype.card_units, ← Nat.card_eq_fintype_card, hc]
  set q := 2 ^ f with hq
  have hq4 : 4 ≤ q := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hqord : q ^ 2 - 1 = orderOf g := by
    rw [hord, hcard, hq]
  have hpow : g ^ (q ^ 2 - 1) = 1 := by
    rw [hqord]
    exact pow_orderOf_eq_one g
  have hexp : (q + 1) * q = (q ^ 2 - 1) + (q + 1) := by
    have h1 : (q + 1) * q = q ^ 2 + q := by ring
    have h2 : (q ^ 2 - 1) + (q + 1) = q ^ 2 + q := by
      have : 1 ≤ q ^ 2 := one_le_pow₀ (show 1 ≤ q by omega)
      omega
    rw [h1, h2]
  have hu : (g ^ (q + 1) : Fˣ) ^ q = g ^ (q + 1) := by
    rw [← pow_mul, hexp, pow_add, hpow, one_mul]
  have hpowr : ((g ^ (q + 1) : Fˣ) : F) ^ (q - 1) = 1 := by
    have hlamq : ((g ^ (q + 1) : Fˣ) : F) ^ q = ((g ^ (q + 1) : Fˣ) : F) := by
      simpa using congrArg (fun u : Fˣ => (u : F)) hu
    have hsplit : (q - 1) + 1 = q := by omega
    have hq' : ((g ^ (q + 1) : Fˣ) : F) ^ ((q - 1) + 1) =
        ((g ^ (q + 1) : Fˣ) : F) := by
      simpa [hsplit] using hlamq
    rw [pow_succ] at hq'
    exact mul_right_cancel₀ (Units.ne_zero (g ^ (q + 1) : Fˣ)) (by simpa using hq')
  refine ⟨((g ^ (q + 1) : Fˣ) : F), ?_, ?_, ?_, ?_⟩
  · rw [unitaryInvolution_apply, ← hq, ← Units.val_pow_eq_pow_val]
    exact congrArg (fun u : Fˣ => (u : F)) hu
  · exact Units.ne_zero _
  · intro h1
    have hlt : q + 1 < orderOf g := by
      rw [← hqord, Nat.lt_sub_iff_add_lt]
      nlinarith [hq4]
    exact (pow_ne_one_of_lt_orderOf (by omega : q + 1 ≠ 0) hlt) (Units.ext h1)
  · exact hpowr

private lemma l10su5_suH_symm {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    {hc : Nat.card F = (2 ^ f) ^ 2} {n : ℕ} (u v : Fin n → F) :
    (suH hc n).β v u = unitaryInvolution F 2 f ((suH hc n).β u v) := by
  change (suForm (unitaryInvolution F 2 f) (unitaryInvolution_involutive hc) n).β v u =
    unitaryInvolution F 2 f
      ((suForm (unitaryInvolution F 2 f) (unitaryInvolution_involutive hc) n).β u v)
  rw [suForm_symm]

private lemma l10su5_mem_perp_frame_iff {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hc : Nat.card F = (2 ^ f) ^ 2) {n : ℕ} (v w v' w' : Fin n → F) (z : Fin n → F) :
    z ∈ (suH hc n).perp (Submodule.span F {v, w, v', w'}) ↔
      (suH hc n).β v z = 0 ∧ (suH hc n).β w z = 0 ∧
        (suH hc n).β v' z = 0 ∧ (suH hc n).β w' z = 0 := by
  rw [ReflForm.mem_perp]
  constructor
  · intro h
    exact ⟨h v (Submodule.subset_span (by simp)), h w (Submodule.subset_span (by simp)),
      h v' (Submodule.subset_span (by simp)), h w' (Submodule.subset_span (by simp))⟩
  · rintro ⟨h1, h2, h3, h4⟩ x hx
    refine Submodule.span_induction (p := fun x _ => (suH hc n).β x z = 0)
      (fun y hy => ?_) ?_ ?_ ?_ hx
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl | rfl | rfl
      · exact h1
      · exact h2
      · exact h3
      · exact h4
    · exact (suH hc n).β_zero_left z
    · intro a b ha hb hpa hpb; rw [(suH hc n).add_left, hpa, hpb, add_zero]
    · intro c a ha hpa; rw [(suH hc n).smul_left, hpa, mul_zero]

private lemma l10su5_frame_proj_mem_K {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    {hc : Nat.card F = (2 ^ f) ^ 2} {n : ℕ} {v w v' w' : Fin n → F}
    (hfr : SUFrame hc n v w v' w') (y : Fin n → F) :
    y - ((suH hc n).β w' y • v + (suH hc n).β v' y • w +
        (suH hc n).β w y • v' + (suH hc n).β v y • w') ∈
      (suH hc n).perp (Submodule.span F {v, w, v', w'}) := by
  have hvv : (suH hc n).β v v = 0 := hfr.2.2.1.1
  have hvw : (suH hc n).β v w = 0 := hfr.2.2.2.1
  have hvv' : (suH hc n).β v v' = 0 := hfr.2.2.2.2.1
  have hvw' : (suH hc n).β v w' = 1 := hfr.1
  have hwv : (suH hc n).β w v = 0 := (suH hc n).refl v w hvw
  have hww : (suH hc n).β w w = 0 := hfr.2.2.1.2.1
  have hwv' : (suH hc n).β w v' = 1 := hfr.2.1
  have hww' : (suH hc n).β w w' = 0 := hfr.2.2.2.2.2.1
  have hv'v : (suH hc n).β v' v = 0 := (suH hc n).refl v v' hvv'
  have hv'w : (suH hc n).β v' w = 1 := by
    rw [l10su5_suH_symm w v', hwv', map_one]
  have hv'v' : (suH hc n).β v' v' = 0 := hfr.2.2.1.2.2.1
  have hv'w' : (suH hc n).β v' w' = 0 := hfr.2.2.2.2.2.2
  have hw'v : (suH hc n).β w' v = 1 := by
    rw [l10su5_suH_symm v w', hvw', map_one]
  have hw'w : (suH hc n).β w' w = 0 := (suH hc n).refl w w' hww'
  have hw'v' : (suH hc n).β w' v' = 0 := (suH hc n).refl v' w' hv'w'
  have hw'w' : (suH hc n).β w' w' = 0 := hfr.2.2.1.2.2.2
  rw [l10su5_mem_perp_frame_iff hc]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [(suH hc n).β_sub_right, (suH hc n).add_right, (suH hc n).smul_right,
      hvv, hvw, hvv', hvw', hwv, hww, hwv', hww', hv'v, hv'w, hv'v', hv'w',
      hw'v, hw'w, hw'v', hw'w', mul_zero, mul_one, sub_zero, zero_add, add_zero] <;>
    ring_nf

private lemma l10su5_span_pair_inf_perp_frame {F : Type} [Field F] [Finite F] [CharP F 2]
    {f : ℕ} {hc : Nat.card F = (2 ^ f) ^ 2} {n : ℕ} {v w v' w' : Fin n → F}
    (hfr : SUFrame hc n v w v' w') :
    Submodule.span F {v, w} ⊓ (suH hc n).perp (Submodule.span F {v, w, v', w'}) = ⊥ := by
  refine le_antisymm ?_ bot_le
  intro x hx
  obtain ⟨hxA, hxK⟩ := hx
  rw [Submodule.mem_bot]
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hxA
  change (a • v + b • w) ∈ (suH hc n).perp (Submodule.span F {v, w, v', w'}) at hxK
  rw [l10su5_mem_perp_frame_iff hc] at hxK
  obtain ⟨-, -, hv', hw'⟩ := hxK
  have hw'v : (suH hc n).β w' v = 1 := by
    rw [l10su5_suH_symm v w', hfr.1, map_one]
  have hv'w : (suH hc n).β v' w = 1 := by
    rw [l10su5_suH_symm w v', hfr.2.1, map_one]
  have hw'w : (suH hc n).β w' w = 0 := (suH hc n).refl w w' hfr.2.2.2.2.2.1
  have hv'v : (suH hc n).β v' v = 0 := (suH hc n).refl v v' hfr.2.2.2.2.1
  have h1 : a = 0 := by
    have h := hw'
    simp only [(suH hc n).add_right, (suH hc n).smul_right, hw'v, hw'w, mul_one, mul_zero,
      add_zero] at h
    exact h
  have h2 : b = 0 := by
    have h := hv'
    simp only [(suH hc n).add_right, (suH hc n).smul_right, hv'v, hv'w, mul_zero, mul_one,
      zero_add] at h
    exact h
  rw [h1, h2, zero_smul, zero_smul, add_zero]

private lemma l10su5_span_pair_le_frame {F : Type} [Field F] {n : ℕ} {v w v' w' : Fin n → F} :
    Submodule.span F {v, w} ≤ Submodule.span F {v, w, v', w'} := by
  refine Submodule.span_mono ?_
  intro z hz
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢
  tauto

private lemma l10su5_lin_fix_span_pair {F : Type} [Field F] {n : ℕ} {v w : Fin n → F}
    (ρ : (Fin n → F) →ₗ[F] (Fin n → F)) (hv : ρ v = v) (hw : ρ w = w)
    {a : Fin n → F} (ha : a ∈ Submodule.span F {v, w}) : ρ a = a := by
  obtain ⟨α, γ, rfl⟩ := Submodule.mem_span_pair.mp ha
  rw [map_add, map_smul, map_smul, hv, hw]

private lemma l10su5_lin_smul_span_pair {F : Type} [Field F] {n : ℕ} {v w : Fin n → F}
    (ρ : (Fin n → F) →ₗ[F] (Fin n → F)) {lam : F} (hv : ρ v = lam • v) (hw : ρ w = lam • w)
    {a : Fin n → F} (ha : a ∈ Submodule.span F {v, w}) : ρ a = lam • a := by
  obtain ⟨α, γ, rfl⟩ := Submodule.mem_span_pair.mp ha
  rw [map_add, map_smul, map_smul, hv, hw]
  module

private lemma l10su5_lam_inv_mem_span {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    {hc : Nat.card F = (2 ^ f) ^ 2} {n : ℕ} {v w v' w' : Fin n → F}
    (hfr : SUFrame hc n v w v' w') {lam : F} (hlam0 : lam ≠ 0) (hlam1 : lam ≠ 1)
    (hlam2 : lam * lam ≠ 1)
    {t : ↥(SU (unitaryInvolution F 2 f) n)}
    (htv : natRep (SU (unitaryInvolution F 2 f) n) t v = lam • v)
    (htw : natRep (SU (unitaryInvolution F 2 f) n) t w = lam • w)
    (htv' : natRep (SU (unitaryInvolution F 2 f) n) t v' = lam⁻¹ • v')
    (htw' : natRep (SU (unitaryInvolution F 2 f) n) t w' = lam⁻¹ • w')
    (htK : ∀ z ∈ (suH hc n).perp (Submodule.span F {v, w, v', w'}),
      natRep (SU (unitaryInvolution F 2 f) n) t z = z)
    {z : Fin n → F} (hz : natRep (SU (unitaryInvolution F 2 f) n) t z = lam⁻¹ • z) :
    z ∈ Submodule.span F {v', w'} := by
  set a : Fin n → F := (suH hc n).β w' z • v + (suH hc n).β v' z • w with ha
  set b : Fin n → F := (suH hc n).β w z • v' + (suH hc n).β v z • w' with hb
  set k : Fin n → F := z - a - b with hk
  have haA : a ∈ Submodule.span F {v, w} := by
    rw [ha]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  have hbB : b ∈ Submodule.span F {v', w'} := by
    rw [hb]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  have hkK : k ∈ (suH hc n).perp (Submodule.span F {v, w, v', w'}) := by
    rw [hk, ha, hb]
    convert l10su5_frame_proj_mem_K hfr z using 1
    abel
  have hza : z = a + b + k := by rw [hk]; abel
  have hta : natRep (SU (unitaryInvolution F 2 f) n) t a = lam • a :=
    l10su5_lin_smul_span_pair _ htv htw haA
  have htb : natRep (SU (unitaryInvolution F 2 f) n) t b = lam⁻¹ • b :=
    l10su5_lin_smul_span_pair _ htv' htw' hbB
  have htk : natRep (SU (unitaryInvolution F 2 f) n) t k = k := htK k hkK
  have heq : lam • a + k = lam⁻¹ • a + lam⁻¹ • k := by
    have h := hz
    rw [hza, map_add, map_add, hta, htb, htk] at h
    have hR : lam⁻¹ • (a + b + k) = lam⁻¹ • a + lam⁻¹ • b + lam⁻¹ • k := by
      rw [smul_add, smul_add]
    rw [hR] at h
    rw [show lam • a + lam⁻¹ • b + k = lam⁻¹ • b + (lam • a + k) by abel,
        show lam⁻¹ • a + lam⁻¹ • b + lam⁻¹ • k =
          lam⁻¹ • b + (lam⁻¹ • a + lam⁻¹ • k) by abel] at h
    exact add_left_cancel h
  have hne : lam - lam⁻¹ ≠ 0 := by
    rw [sub_ne_zero]
    intro h
    have h1 : lam * lam = 1 := by
      calc lam * lam = lam * lam⁻¹ := by rw [← h]
        _ = 1 := mul_inv_cancel₀ hlam0
    exact hlam2 h1
  have hmem : (lam - lam⁻¹) • a ∈ Submodule.span F {v, w} ⊓
      (suH hc n).perp (Submodule.span F {v, w, v', w'}) := by
    refine ⟨Submodule.smul_mem _ _ haA, ?_⟩
    have hconv : (lam - lam⁻¹) • a = (lam⁻¹ - 1) • k := by
      rw [sub_smul, sub_smul, one_smul]
      linear_combination heq
    rw [hconv]
    exact Submodule.smul_mem _ _ hkK
  rw [l10su5_span_pair_inf_perp_frame hfr, Submodule.mem_bot] at hmem
  have ha0 : a = 0 := (smul_eq_zero.mp hmem).resolve_left hne
  have hk0 : k = 0 := by
    rw [ha0, smul_zero, zero_add, smul_zero, zero_add] at heq
    have h1 : (1 - lam⁻¹) • k = 0 := by
      rw [sub_smul, one_smul, ← heq, sub_self]
    have hne' : 1 - lam⁻¹ ≠ 0 := by
      rw [sub_ne_zero]
      intro h
      exact hlam1 (inv_eq_one.mp h.symm)
    exact (smul_eq_zero.mp h1).resolve_left hne'
  rw [hza, ha0, hk0, zero_add, add_zero]
  exact hbB

private lemma l10su5_pow_eq_one {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    {hc : Nat.card F = (2 ^ f) ^ 2} {n : ℕ} {v w v' w' : Fin n → F}
    (hfr : SUFrame hc n v w v' w') {lam : F}
    {t : ↥(SU (unitaryInvolution F 2 f) n)}
    (htv : natRep (SU (unitaryInvolution F 2 f) n) t v = lam • v)
    (htw : natRep (SU (unitaryInvolution F 2 f) n) t w = lam • w)
    (htv' : natRep (SU (unitaryInvolution F 2 f) n) t v' = lam⁻¹ • v')
    (htw' : natRep (SU (unitaryInvolution F 2 f) n) t w' = lam⁻¹ • w')
    (htK : ∀ z ∈ (suH hc n).perp (Submodule.span F {v, w, v', w'}),
      natRep (SU (unitaryInvolution F 2 f) n) t z = z)
    (hlampow : lam ^ (2 ^ f - 1) = 1) : t ^ (2 ^ f - 1) = 1 := by
  have hpowA : ∀ (m : ℕ) (a : Fin n → F), a ∈ Submodule.span F {v, w} →
      (natRep (SU (unitaryInvolution F 2 f) n) t ^ m) a = lam ^ m • a := by
    intro m
    induction m with
    | zero => intro a ha; simp
    | succ m ih =>
      intro a ha
      calc (natRep (SU (unitaryInvolution F 2 f) n) t ^ (m + 1)) a
          = (natRep (SU (unitaryInvolution F 2 f) n) t ^ m *
              natRep (SU (unitaryInvolution F 2 f) n) t) a := by rw [pow_succ]
        _ = (natRep (SU (unitaryInvolution F 2 f) n) t ^ m)
              ((natRep (SU (unitaryInvolution F 2 f) n) t) a) := by
              rw [Module.End.mul_apply]
        _ = (natRep (SU (unitaryInvolution F 2 f) n) t ^ m) (lam • a) := by
              rw [l10su5_lin_smul_span_pair _ htv htw ha]
        _ = lam ^ m • (lam • a) := ih (lam • a) (Submodule.smul_mem _ _ ha)
        _ = lam ^ (m + 1) • a := by rw [smul_smul, pow_succ]
  have hpowB : ∀ (m : ℕ) (b : Fin n → F), b ∈ Submodule.span F {v', w'} →
      (natRep (SU (unitaryInvolution F 2 f) n) t ^ m) b = (lam⁻¹) ^ m • b := by
    intro m
    induction m with
    | zero => intro b hb; simp
    | succ m ih =>
      intro b hb
      calc (natRep (SU (unitaryInvolution F 2 f) n) t ^ (m + 1)) b
          = (natRep (SU (unitaryInvolution F 2 f) n) t ^ m *
              natRep (SU (unitaryInvolution F 2 f) n) t) b := by rw [pow_succ]
        _ = (natRep (SU (unitaryInvolution F 2 f) n) t ^ m)
              ((natRep (SU (unitaryInvolution F 2 f) n) t) b) := by
              rw [Module.End.mul_apply]
        _ = (natRep (SU (unitaryInvolution F 2 f) n) t ^ m) (lam⁻¹ • b) := by
              rw [l10su5_lin_smul_span_pair _ htv' htw' hb]
        _ = (lam⁻¹) ^ m • (lam⁻¹ • b) := ih (lam⁻¹ • b) (Submodule.smul_mem _ _ hb)
        _ = (lam⁻¹) ^ (m + 1) • b := by rw [smul_smul, pow_succ]
  have hpowK : ∀ (m : ℕ) (k : Fin n → F),
      k ∈ (suH hc n).perp (Submodule.span F {v, w, v', w'}) →
      (natRep (SU (unitaryInvolution F 2 f) n) t ^ m) k = k := by
    intro m
    induction m with
    | zero => intro k hk; simp
    | succ m ih =>
      intro k hk
      calc (natRep (SU (unitaryInvolution F 2 f) n) t ^ (m + 1)) k
          = (natRep (SU (unitaryInvolution F 2 f) n) t ^ m *
              natRep (SU (unitaryInvolution F 2 f) n) t) k := by rw [pow_succ]
        _ = (natRep (SU (unitaryInvolution F 2 f) n) t ^ m)
              ((natRep (SU (unitaryInvolution F 2 f) n) t) k) := by
              rw [Module.End.mul_apply]
        _ = (natRep (SU (unitaryInvolution F 2 f) n) t ^ m) k := by rw [htK k hk]
        _ = k := ih k hk
  have hpow : natRep (SU (unitaryInvolution F 2 f) n) t ^ (2 ^ f - 1) = 1 := by
    refine LinearMap.ext fun x => ?_
    set a : Fin n → F := (suH hc n).β w' x • v + (suH hc n).β v' x • w with ha
    set b : Fin n → F := (suH hc n).β w x • v' + (suH hc n).β v x • w' with hb
    set k : Fin n → F := x - a - b with hk
    have haA : a ∈ Submodule.span F {v, w} := by
      rw [ha]
      exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
        (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    have hbB : b ∈ Submodule.span F {v', w'} := by
      rw [hb]
      exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
        (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    have hkK : k ∈ (suH hc n).perp (Submodule.span F {v, w, v', w'}) := by
      rw [hk, ha, hb]
      convert l10su5_frame_proj_mem_K hfr x using 1
      abel
    have hx : x = a + b + k := by rw [hk]; abel
    calc (natRep (SU (unitaryInvolution F 2 f) n) t ^ (2 ^ f - 1)) x
        = (natRep (SU (unitaryInvolution F 2 f) n) t ^ (2 ^ f - 1)) (a + b + k) := by
            rw [hx]
      _ = (natRep (SU (unitaryInvolution F 2 f) n) t ^ (2 ^ f - 1)) a +
            (natRep (SU (unitaryInvolution F 2 f) n) t ^ (2 ^ f - 1)) b +
            (natRep (SU (unitaryInvolution F 2 f) n) t ^ (2 ^ f - 1)) k := by
            rw [map_add, map_add]
      _ = lam ^ (2 ^ f - 1) • a + (lam⁻¹) ^ (2 ^ f - 1) • b + k := by
            rw [hpowA _ a haA, hpowB _ b hbB, hpowK _ k hkK]
      _ = a + b + k := by rw [hlampow, inv_pow, hlampow, inv_one, one_smul, one_smul]
      _ = x := hx.symm
  apply natRep_injective (SU (unitaryInvolution F 2 f) n)
  rw [map_pow, hpow, map_one]

private lemma l10su5_rad_eq_one {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    {hc : Nat.card F = (2 ^ f) ^ 2} {n : ℕ} {v w v' w' : Fin n → F}
    (hfr : SUFrame hc n v w v' w') {lam : F} (hlam0 : lam ≠ 0) (hlam1 : lam ≠ 1)
    (hlam2 : lam * lam ≠ 1)
    {t : ↥(SU (unitaryInvolution F 2 f) n)}
    (htv : natRep (SU (unitaryInvolution F 2 f) n) t v = lam • v)
    (htw : natRep (SU (unitaryInvolution F 2 f) n) t w = lam • w)
    (htv' : natRep (SU (unitaryInvolution F 2 f) n) t v' = lam⁻¹ • v')
    (htw' : natRep (SU (unitaryInvolution F 2 f) n) t w' = lam⁻¹ • w')
    (htK : ∀ z ∈ (suH hc n).perp (Submodule.span F {v, w, v', w'}),
      natRep (SU (unitaryInvolution F 2 f) n) t z = z)
    {y : ↥(SU (unitaryInvolution F 2 f) n)}
    (hyA : ∀ a ∈ Submodule.span F {v, w},
      natRep (SU (unitaryInvolution F 2 f) n) y a = a)
    (hyPerp : ∀ z ∈ (suH hc n).perp (Submodule.span F {v, w}),
      natRep (SU (unitaryInvolution F 2 f) n) y z - z ∈ Submodule.span F {v, w})
    (hcomm : ∀ x : Fin n → F,
      natRep (SU (unitaryInvolution F 2 f) n) t
          (natRep (SU (unitaryInvolution F 2 f) n) y x) =
        natRep (SU (unitaryInvolution F 2 f) n) y
          (natRep (SU (unitaryInvolution F 2 f) n) t x)) :
    y = 1 := by
  have hρ := isIsometric_natRep_SU (unitaryInvolution F 2 f)
    (unitaryInvolution_involutive hc) n
  have hvA : v ∈ Submodule.span F {v, w} := Submodule.subset_span (by simp)
  have hwA : w ∈ Submodule.span F {v, w} := Submodule.subset_span (by simp)
  have hyv : natRep (SU (unitaryInvolution F 2 f) n) y v = v := hyA v hvA
  have hyw : natRep (SU (unitaryInvolution F 2 f) n) y w = w := hyA w hwA
  have hz1 : natRep (SU (unitaryInvolution F 2 f) n) t
      (natRep (SU (unitaryInvolution F 2 f) n) y v') =
        lam⁻¹ • natRep (SU (unitaryInvolution F 2 f) n) y v' := by
    have h := hcomm v'
    rw [htv', map_smul] at h
    exact h
  have hz1B : natRep (SU (unitaryInvolution F 2 f) n) y v' ∈
      Submodule.span F {v', w'} :=
    l10su5_lam_inv_mem_span hfr hlam0 hlam1 hlam2 htv htw htv' htw' htK hz1
  obtain ⟨p1, q1, hpq1⟩ := Submodule.mem_span_pair.mp hz1B
  have hwz1 : (suH hc n).β w (natRep (SU (unitaryInvolution F 2 f) n) y v') = 1 := by
    have h := hρ y w v'
    rw [hyw] at h
    change (suH hc n).β w (natRep (SU (unitaryInvolution F 2 f) n) y v') =
      (suH hc n).β w v' at h
    rw [hfr.2.1] at h
    exact h
  have hvz1 : (suH hc n).β v (natRep (SU (unitaryInvolution F 2 f) n) y v') = 0 := by
    have h := hρ y v v'
    rw [hyv] at h
    change (suH hc n).β v (natRep (SU (unitaryInvolution F 2 f) n) y v') =
      (suH hc n).β v v' at h
    rw [hfr.2.2.2.2.1] at h
    exact h
  have hp1 : p1 = 1 := by
    have h := hwz1
    rw [← hpq1, (suH hc n).add_right, (suH hc n).smul_right, (suH hc n).smul_right,
      hfr.2.1, hfr.2.2.2.2.2.1, mul_one, mul_zero, add_zero] at h
    exact h
  have hq1 : q1 = 0 := by
    have h := hvz1
    rw [← hpq1, (suH hc n).add_right, (suH hc n).smul_right, (suH hc n).smul_right,
      hfr.2.2.2.2.1, hfr.1, mul_zero, mul_one, zero_add] at h
    exact h
  have hyv' : natRep (SU (unitaryInvolution F 2 f) n) y v' = v' := by
    rw [← hpq1, hp1, hq1, one_smul, zero_smul, add_zero]
  have hz2 : natRep (SU (unitaryInvolution F 2 f) n) t
      (natRep (SU (unitaryInvolution F 2 f) n) y w') =
        lam⁻¹ • natRep (SU (unitaryInvolution F 2 f) n) y w' := by
    have h := hcomm w'
    rw [htw', map_smul] at h
    exact h
  have hz2B : natRep (SU (unitaryInvolution F 2 f) n) y w' ∈
      Submodule.span F {v', w'} :=
    l10su5_lam_inv_mem_span hfr hlam0 hlam1 hlam2 htv htw htv' htw' htK hz2
  obtain ⟨p2, q2, hpq2⟩ := Submodule.mem_span_pair.mp hz2B
  have hwz2 : (suH hc n).β w (natRep (SU (unitaryInvolution F 2 f) n) y w') = 0 := by
    have h := hρ y w w'
    rw [hyw] at h
    change (suH hc n).β w (natRep (SU (unitaryInvolution F 2 f) n) y w') =
      (suH hc n).β w w' at h
    rw [hfr.2.2.2.2.2.1] at h
    exact h
  have hvz2 : (suH hc n).β v (natRep (SU (unitaryInvolution F 2 f) n) y w') = 1 := by
    have h := hρ y v w'
    rw [hyv] at h
    change (suH hc n).β v (natRep (SU (unitaryInvolution F 2 f) n) y w') =
      (suH hc n).β v w' at h
    rw [hfr.1] at h
    exact h
  have hp2 : p2 = 0 := by
    have h := hwz2
    rw [← hpq2, (suH hc n).add_right, (suH hc n).smul_right, (suH hc n).smul_right,
      hfr.2.1, hfr.2.2.2.2.2.1, mul_one, mul_zero, add_zero] at h
    exact h
  have hq2 : q2 = 1 := by
    have h := hvz2
    rw [← hpq2, (suH hc n).add_right, (suH hc n).smul_right, (suH hc n).smul_right,
      hfr.2.2.2.2.1, hfr.1, mul_zero, mul_one, zero_add] at h
    exact h
  have hyw' : natRep (SU (unitaryInvolution F 2 f) n) y w' = w' := by
    rw [← hpq2, hp2, hq2, zero_smul, one_smul, zero_add]
  have hyK : ∀ k ∈ (suH hc n).perp (Submodule.span F {v, w, v', w'}),
      natRep (SU (unitaryInvolution F 2 f) n) y k = k := by
    intro k hk
    have hkAperp : k ∈ (suH hc n).perp (Submodule.span F {v, w}) :=
      ReflForm.perp_antitone (suH hc n) l10su5_span_pair_le_frame hk
    set d : Fin n → F := natRep (SU (unitaryInvolution F 2 f) n) y k - k with hd
    have hdA : d ∈ Submodule.span F {v, w} := hyPerp k hkAperp
    have hcommk : natRep (SU (unitaryInvolution F 2 f) n) t
        (natRep (SU (unitaryInvolution F 2 f) n) y k) =
          natRep (SU (unitaryInvolution F 2 f) n) y k := by
      have h := hcomm k
      rw [htK k hk] at h
      exact h
    have htd : natRep (SU (unitaryInvolution F 2 f) n) t d = lam • d :=
      l10su5_lin_smul_span_pair _ htv htw hdA
    have h1 : natRep (SU (unitaryInvolution F 2 f) n) t
        (natRep (SU (unitaryInvolution F 2 f) n) y k) = lam • d + k := by
      rw [show natRep (SU (unitaryInvolution F 2 f) n) y k = d + k by rw [hd]; abel,
        map_add, htd, htK k hk]
    have h2 : lam • d = d := by
      have h := hcommk
      rw [h1] at h
      rw [show natRep (SU (unitaryInvolution F 2 f) n) y k = d + k by rw [hd]; abel] at h
      exact add_right_cancel h
    have h3 : d = 0 := by
      have h4 : (lam - 1) • d = 0 := by rw [sub_smul, one_smul, h2, sub_self]
      exact (smul_eq_zero.mp h4).resolve_left (sub_ne_zero.mpr hlam1)
    rw [show natRep (SU (unitaryInvolution F 2 f) n) y k = d + k by rw [hd]; abel, h3,
      zero_add]
  apply natRep_injective (SU (unitaryInvolution F 2 f) n)
  rw [map_one]
  refine LinearMap.ext fun x => ?_
  set a : Fin n → F := (suH hc n).β w' x • v + (suH hc n).β v' x • w with ha
  set b : Fin n → F := (suH hc n).β w x • v' + (suH hc n).β v x • w' with hb
  set k : Fin n → F := x - a - b with hk
  have haA : a ∈ Submodule.span F {v, w} := by
    rw [ha]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  have hbB : b ∈ Submodule.span F {v', w'} := by
    rw [hb]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  have hkK : k ∈ (suH hc n).perp (Submodule.span F {v, w, v', w'}) := by
    rw [hk, ha, hb]
    convert l10su5_frame_proj_mem_K hfr x using 1
    abel
  have hx : x = a + b + k := by rw [hk]; abel
  have hyB : natRep (SU (unitaryInvolution F 2 f) n) y b = b :=
    l10su5_lin_fix_span_pair _ hyv' hyw' hbB
  calc natRep (SU (unitaryInvolution F 2 f) n) y x
      = natRep (SU (unitaryInvolution F 2 f) n) y (a + b + k) := by rw [hx]
    _ = natRep (SU (unitaryInvolution F 2 f) n) y a +
          natRep (SU (unitaryInvolution F 2 f) n) y b +
          natRep (SU (unitaryInvolution F 2 f) n) y k := by rw [map_add, map_add]
    _ = a + b + k := by rw [hyA a haA, hyB, hyK k hkK]
    _ = x := hx.symm

private theorem l10su5_fpf {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hF : Nat.card F = (2 ^ f) ^ 2) {n : ℕ} (hf : 2 ≤ f)
    {β : Fin (Unitary.rootDatum hF n).rank → ℤ} (hβ : β ∈ (Unitary.rootDatum hF n).roots)
    (hs : ¬ GGLongRoot (Unitary.rootDatum hF n) β)
    (h2β : 2 • β ∉ (Unitary.rootDatum hF n).roots) :
    ∃ h ∈ Subgroup.normalizer
        (((Unitary.rootDatum hF n).rootGroup β :
          Subgroup ↥(Unitary.SU (unitaryInvolution F 2 f) n)) :
          Set ↥(Unitary.SU (unitaryInvolution F 2 f) n)),
      Odd (orderOf h) ∧ ∀ y ∈ pCoreOf 2 (Subgroup.normalizer
        (((Unitary.rootDatum hF n).rootGroup β :
          Subgroup ↥(Unitary.SU (unitaryInvolution F 2 f) n)) :
          Set ↥(Unitary.SU (unitaryInvolution F 2 f) n))),
        h * y = y * h → y ∈ (Unitary.rootDatum hF n).rootGroup β := by
  obtain ⟨v, w, v', w', hfr, hA, -⟩ :=
    Geo.exists_unitPairGroup_eq_conj_rootGroup_SU hF n hβ hs h2β
      (1 : ↥(SU (unitaryInvolution F 2 f) n))
  have hA' : (Unitary.rootDatum hF n).rootGroup β =
      suPair (unitaryInvolution F 2 f) n v w := by
    rw [← hA]
    ext x
    simp [MulAut.conj_apply]
  obtain ⟨lam, hsiglam, hlam0, hlam1, hlampow⟩ :=
    l10su5_exists_fixed_ne_zero_ne_one hF hf
  have hlam2 : lam * lam ≠ 1 := by
    intro h
    rw [← sq] at h
    rcases sq_eq_one_iff.mp h with h1 | h1
    · exact hlam1 h1
    · rw [CharTwo.neg_eq] at h1
      exact hlam1 h1
  have hsiglam2 : unitaryInvolution F 2 f (lam * lam) = lam * lam := by
    rw [map_mul, hsiglam]
  obtain ⟨t, htv, htw, htv', htw', htK⟩ :=
    exists_mem_SU_torus hfr (μ := lam) (ν := lam) hlam0 hlam0 hsiglam2
  rw [hsiglam] at htv' htw'
  have htN : t ∈ Subgroup.normalizer
      (suPair (unitaryInvolution F 2 f) n v w :
        Set ↥(SU (unitaryInvolution F 2 f) n)) := by
    rw [mem_normalizer_suPair_iff hfr]
    exact Or.inl ⟨lam, lam, htv, htw⟩
  have hpow : t ^ (2 ^ f - 1) = 1 :=
    l10su5_pow_eq_one hfr htv htw htv' htw' htK hlampow
  have hodd : Odd (orderOf t) := by
    have hodd2 : Odd (2 ^ f - 1) :=
      Nat.Even.sub_odd (one_le_pow₀ (show 1 ≤ 2 by norm_num))
        (Even.pow_of_ne_zero even_two (by omega : f ≠ 0)) odd_one
    exact Odd.of_dvd_nat hodd2 (orderOf_dvd_of_pow_eq_one hpow)
  refine ⟨t, ?_, hodd, ?_⟩
  · rw [hA']
    exact htN
  · intro y hy hty
    rw [hA'] at hy
    have hyR : y ∈ suStabRad hF n (Submodule.span F {v, w})
        (suFrame_isTotallyIsotropic hfr) :=
      pCoreOf_normalizer_suPair_le_suStabRad hfr hy
    rw [suStabRad] at hyR
    obtain ⟨hyA, hyPerp⟩ := mem_rad.mp hyR
    have hcomm : ∀ x : Fin n → F,
        natRep (SU (unitaryInvolution F 2 f) n) t
            (natRep (SU (unitaryInvolution F 2 f) n) y x) =
          natRep (SU (unitaryInvolution F 2 f) n) y
            (natRep (SU (unitaryInvolution F 2 f) n) t x) := by
      intro x
      have h := congrArg (fun z : ↥(SU (unitaryInvolution F 2 f) n) =>
        natRep (SU (unitaryInvolution F 2 f) n) z x) hty
      simpa only [map_mul, Module.End.mul_apply] using h
    have hy1 : y = 1 :=
      l10su5_rad_eq_one hfr hlam0 hlam1 hlam2 htv htw htv' htw' htK hyA hyPerp hcomm
    rw [hy1, hA']
    exact one_mem _

private theorem l10su5_fpf_map {K : Type*} [Group K] (e : K ≃* K) {X : Subgroup K} {h : K}
    (hhN : h ∈ Subgroup.normalizer (X : Set K))
    (hfix : ∀ y ∈ pCoreOf 2 (Subgroup.normalizer (X : Set K)), h * y = y * h → y ∈ X) :
    e h ∈ Subgroup.normalizer ((X.map e.toMonoidHom : Subgroup K) : Set K) ∧
      ∀ y ∈ pCoreOf 2 (Subgroup.normalizer ((X.map e.toMonoidHom : Subgroup K) : Set K)),
        e h * y = y * e h → y ∈ X.map e.toMonoidHom := by
  constructor
  · rw [GGRootNorm.normalizer_map_mulEquiv e X, Subgroup.mem_map_equiv]
    simpa using hhN
  · intro y hy hcomm
    rw [GGRootNorm.normalizer_map_mulEquiv e X,
      GGRootNorm.pCoreOf_map_mulEquiv e (Subgroup.normalizer (X : Set K))] at hy
    rw [Subgroup.mem_map_equiv] at hy
    have hcomm' : h * e.symm y = e.symm y * h := by
      have h1 := congrArg (fun z => e.symm z) hcomm
      simpa using h1
    rw [Subgroup.mem_map_equiv]
    exact hfix (e.symm y) hy hcomm'

theorem ggRootNoCentral_su_short {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hF : Nat.card F = (2 ^ f) ^ 2) {n : ℕ} (hf : 2 ≤ f)
    {β : Fin (Unitary.rootDatum hF n).rank → ℤ} (hβ : β ∈ (Unitary.rootDatum hF n).roots)
    (hs : ¬ GGLongRoot (Unitary.rootDatum hF n) β)
    (h2β : 2 • β ∉ (Unitary.rootDatum hF n).roots)
    (u : ↥(Unitary.SU (unitaryInvolution F 2 f) n)) :
    GGRootNoCentralAt (⊤ : Subgroup ↥(Unitary.SU (unitaryInvolution F 2 f) n))
      (((Unitary.rootDatum hF n).rootGroup β).map (MulAut.conj u).toMonoidHom) := by
  obtain ⟨h, hhN, hodd, hfix⟩ := l10su5_fpf hF hf hβ hs h2β
  obtain ⟨hhN', hfix'⟩ := l10su5_fpf_map (MulAut.conj u) hhN hfix
  refine noCentral_of_fixedPoint_odd (h := (MulAut.conj u) h) ?_ ?_ ?_
  · rwa [MulEquiv.orderOf_eq]
  · rw [top_inf_eq]
    exact hhN'
  · intro y hy hcomm
    rw [top_inf_eq] at hy
    exact hfix' y hy hcomm

end CFSG.StandardType.LieKnownR2.PSU
