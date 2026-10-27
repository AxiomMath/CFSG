module

public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2ShortSUDefs

public section

namespace CFSG.StandardType.LieKnownR2.Short

open CFSG.StandardType CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary
  CFSG.QuasithinUnique.B113Lie.Sp

theorem mem_normalizer_suPair_iff {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    {hc : Nat.card F = (2 ^ f) ^ 2} {n : ℕ} {v w v' w' : Fin n → F}
    (hfr : SUFrame hc n v w v' w') {g : ↥(SU (unitaryInvolution F 2 f) n)} :
    g ∈ Subgroup.normalizer
        (suPair (unitaryInvolution F 2 f) n v w : Set ↥(SU (unitaryInvolution F 2 f) n)) ↔
      (∃ a d : F, natRep (SU (unitaryInvolution F 2 f) n) g v = a • v ∧
        natRep (SU (unitaryInvolution F 2 f) n) g w = d • w) ∨
      (∃ a d : F, natRep (SU (unitaryInvolution F 2 f) n) g v = a • w ∧
        natRep (SU (unitaryInvolution F 2 f) n) g w = d • v) := by
  let σ := unitaryInvolution F 2 f
  let hσ := unitaryInvolution_involutive hc
  have hσ' : ∀ c : F, σ (σ c) = c := fun c => hσ c
  let B : ReflForm F (Fin n → F) := suH hc n
  let ρ : ↥(SU σ n) →* Module.End F (Fin n → F) := natRep (SU σ n)
  have hρ : IsIsometric B ρ := GGOppRadSpU.isIsometric_natRep_SU σ hσ n
  have hvw' : B.β v w' = 1 := hfr.1
  have hwv' : B.β w v' = 1 := hfr.2.1
  have hvv : B.β v v = 0 := hfr.2.2.1.1
  have hww : B.β w w = 0 := hfr.2.2.1.2.1
  have hvw : B.β v w = 0 := hfr.2.2.2.1
  have hvv' : B.β v v' = 0 := hfr.2.2.2.2.1
  have hww' : B.β w w' = 0 := hfr.2.2.2.2.2.1
  have hsm : ∀ (c : F) (u y : Fin n → F), B.β (c • u) y = σ c * B.β u y :=
    fun c u y => B.smul_left c u y
  have hv0 : v ≠ 0 := by
    intro h0
    rw [h0, B.β_zero_left] at hvw'
    exact zero_ne_one hvw'
  have hw0 : w ≠ 0 := by
    intro h0
    rw [h0, B.β_zero_left] at hwv'
    exact zero_ne_one hwv'
  have hker : ∀ (u : ↥(SU σ n)) (x : Fin n → F), ρ u x = 0 → x = 0 := by
    intro u x hx
    have := congrArg (ρ u⁻¹) hx
    rwa [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply,
      map_zero] at this
  have hinj : ∀ (u : ↥(SU σ n)) {x y : Fin n → F}, ρ u x = ρ u y → x = y := by
    intro u x y hxy
    have hsub : ρ u (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    exact sub_eq_zero.mp (hker u (x - y) hsub)
  let Mono : ↥(SU σ n) → Prop := fun u =>
    (∃ a d : F, ρ u v = a • v ∧ ρ u w = d • w) ∨
      (∃ a d : F, ρ u v = a • w ∧ ρ u w = d • v)
  have mono_inv : ∀ u, Mono u → Mono u⁻¹ := by
    intro u hu
    rcases hu with ⟨a, d, hav, haw⟩ | ⟨a, d, ha, hd⟩
    · left
      have ha0 : a ≠ 0 := by
        intro h0
        exact hv0 (hker u v (by rw [hav, h0, zero_smul]))
      have hd0 : d ≠ 0 := by
        intro h0
        exact hw0 (hker u w (by rw [haw, h0, zero_smul]))
      refine ⟨a⁻¹, d⁻¹, ?_, ?_⟩
      · have h : ρ u (ρ u⁻¹ v) = ρ u (a⁻¹ • v) := by
          rw [rep_apply_inv_apply, map_smul, hav, smul_smul, inv_mul_cancel₀ ha0, one_smul]
        exact hinj u h
      · have h : ρ u (ρ u⁻¹ w) = ρ u (d⁻¹ • w) := by
          rw [rep_apply_inv_apply, map_smul, haw, smul_smul, inv_mul_cancel₀ hd0, one_smul]
        exact hinj u h
    · right
      have ha0 : a ≠ 0 := by
        intro h0
        exact hv0 (hker u v (by rw [ha, h0, zero_smul]))
      have hd0 : d ≠ 0 := by
        intro h0
        exact hw0 (hker u w (by rw [hd, h0, zero_smul]))
      refine ⟨d⁻¹, a⁻¹, ?_, ?_⟩
      · have h : ρ u (ρ u⁻¹ v) = ρ u (d⁻¹ • w) := by
          rw [rep_apply_inv_apply, map_smul, hd, smul_smul, inv_mul_cancel₀ hd0, one_smul]
        exact hinj u h
      · have h : ρ u (ρ u⁻¹ w) = ρ u (a⁻¹ • v) := by
          rw [rep_apply_inv_apply, map_smul, ha, smul_smul, inv_mul_cancel₀ ha0, one_smul]
        exact hinj u h
  have mono_conj : ∀ u, Mono u → ∀ s ∈ suPair σ n v w, u * s * u⁻¹ ∈ suPair σ n v w := by
    intro u hu s hs
    obtain ⟨c, hpar⟩ := exists_mulVec_of_mem_suPair hc hvv hww hvw hs
    have hcρ : ∀ y, ρ s y = y + (c * B.β w y) • v + (σ c * B.β v y) • w := hpar
    have hc' : ∀ y, ρ s y = y + B.β w y • (c • v) + B.β v y • (σ c • w) := by
      intro y
      rw [hcρ y, smul_smul, smul_smul, mul_comm c (B.β w y), mul_comm (σ c) (B.β v y)]
    rcases hu with ⟨a, d, hav, haw⟩ | ⟨a, d, ha, hd⟩
    · refine mem_suPair_of_mulVec hc (c * σ d * a) (fun y => ?_)
      have hconj := rep_conj_apply hρ hc' u y
      rw [map_smul, map_smul, hav, haw, hsm, hsm] at hconj
      have h1 : (σ d * B.β w y) • (c • (a • v)) = ((c * σ d * a) * B.β w y) • v := by
        rw [smul_smul, smul_smul]
        congr 1
        ring
      have h2 : (σ a * B.β v y) • (σ c • (d • w)) =
          (σ (c * σ d * a) * B.β v y) • w := by
        rw [smul_smul, smul_smul]
        congr 1
        simp only [map_mul, hσ']
        ring
      rw [hconj, h1, h2]
    · refine mem_suPair_of_mulVec hc (σ c * σ a * d) (fun y => ?_)
      have hconj := rep_conj_apply hρ hc' u y
      rw [map_smul, map_smul, ha, hd, hsm, hsm] at hconj
      have h1 : (σ a * B.β w y) • (σ c • (d • v)) = ((σ c * σ a * d) * B.β w y) • v := by
        rw [smul_smul, smul_smul]
        congr 1
        ring
      have h2 : (σ d * B.β v y) • (c • (a • w)) =
          (σ (σ c * σ a * d) * B.β v y) • w := by
        rw [smul_smul, smul_smul]
        congr 1
        simp only [map_mul, hσ']
        ring
      rw [hconj, h1, h2]
      abel
  constructor
  · intro hg
    change Mono g
    have hvA : v ∈ Submodule.span F ({v, w} : Set (Fin n → F)) :=
      Submodule.subset_span (by simp)
    have hwA : w ∈ Submodule.span F ({v, w} : Set (Fin n → F)) :=
      Submodule.subset_span (by simp)
    obtain ⟨t1, ht1_mem, ht1⟩ := exists_mem_suPair_mulVec hc hvv hww hvw (1 : F)
    have ht1ρ : ∀ y, ρ t1 y = y + (1 * B.β w y) • v + (σ 1 * B.β v y) • w := ht1
    have hgt1 : g * t1 * g⁻¹ ∈ suPair σ n v w := (Subgroup.mem_normalizer_iff.mp hg t1).1 ht1_mem
    obtain ⟨c1, hc1⟩ := exists_mulVec_of_mem_suPair hc hvv hww hvw hgt1
    have hc1ρ : ∀ y, ρ (g * t1 * g⁻¹) y = y + (c1 * B.β w y) • v + (σ c1 * B.β v y) • w := hc1
    have hAinv : ∀ x ∈ Submodule.span F ({v, w} : Set (Fin n → F)),
        ρ g x ∈ Submodule.span F ({v, w} : Set (Fin n → F)) := by
      intro x hx
      obtain ⟨α, β, hαβ⟩ := Submodule.mem_span_pair.mp hx
      let y : Fin n → F := α • v' + β • w'
      have hwy : B.β w y = α := by
        change B.β w (α • v' + β • w') = α
        rw [B.add_right, B.smul_right, B.smul_right, hwv', hww', mul_one, mul_zero, add_zero]
      have hvy : B.β v y = β := by
        change B.β v (α • v' + β • w') = β
        rw [B.add_right, B.smul_right, B.smul_right, hvv', hvw', mul_zero, mul_one, zero_add]
      have hty : ρ t1 y = y + x := by
        rw [ht1ρ y, one_mul, map_one, one_mul, hwy, hvy, add_assoc, hαβ]
      have hginv : ρ g⁻¹ (ρ g y) = y := by
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
      have hcomp : ρ g (ρ t1 y) = ρ (g * t1 * g⁻¹) (ρ g y) := by
        rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hginv]
      have heq : ρ g x = (c1 * B.β w (ρ g y)) • v + (σ c1 * B.β v (ρ g y)) • w := by
        have hx' : x = ρ t1 y - y := by rw [hty]; abel
        rw [hx', map_sub, hcomp, hc1ρ (ρ g y)]
        abel
      rw [heq]
      exact Submodule.add_mem _ (Submodule.smul_mem _ _ hvA) (Submodule.smul_mem _ _ hwA)
    obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp (hAinv v hvA)
    obtain ⟨d, e, hde⟩ := Submodule.mem_span_pair.mp (hAinv w hwA)
    have hpw' : B.β (ρ g v) w' = σ a := by
      rw [← hab, B.add_left, hsm, hsm, hvw', hww', mul_one, mul_zero, add_zero]
    have hpv' : B.β (ρ g v) v' = σ b := by
      rw [← hab, B.add_left, hsm, hsm, hvv', hwv', mul_zero, mul_one, zero_add]
    have hrw' : B.β (ρ g w) w' = σ d := by
      rw [← hde, B.add_left, hsm, hsm, hvw', hww', mul_one, mul_zero, add_zero]
    have hrv' : B.β (ρ g w) v' = σ e := by
      rw [← hde, B.add_left, hsm, hsm, hvv', hwv', mul_zero, mul_one, zero_add]
    have hindep : ∀ x y : F, x • v + y • w = 0 → x = 0 ∧ y = 0 := by
      intro x y hxy
      have h1 := congrArg (fun z => B.β z w') hxy
      have h2 := congrArg (fun z => B.β z v') hxy
      simp only [B.add_left, hsm, B.β_zero_left, hvw', hww', hvv', hwv', mul_one, mul_zero,
        add_zero, zero_add] at h1 h2
      exact ⟨(map_eq_zero_iff _ σ.injective).mp h1, (map_eq_zero_iff _ σ.injective).mp h2⟩
    have coeff : ∀ {x y z t : F}, x • v + y • w = z • v + t • w → x = z ∧ y = t := by
      intro x y z t heq
      have h0 : (x - z) • v + (y - t) • w = 0 := by
        have habel : (x - z) • v + (y - t) • w =
            (x • v + y • w) - (z • v + t • w) := by
          rw [sub_smul, sub_smul]
          abel
        rw [habel, heq, sub_self]
      obtain ⟨hx, hy⟩ := hindep (x - z) (y - t) h0
      exact ⟨sub_eq_zero.mp hx, sub_eq_zero.mp hy⟩
    have hkey : ∀ c : F, ∃ c' : F, ∀ y : Fin n → F,
        B.β (ρ g w) y • (c • ρ g v) + B.β (ρ g v) y • (σ c • ρ g w) =
          (c' * B.β w y) • v + (σ c' * B.β v y) • w := by
      intro c
      obtain ⟨t, ht_mem, ht⟩ := exists_mem_suPair_mulVec hc hvv hww hvw c
      have htρ : ∀ y, ρ t y = y + (c * B.β w y) • v + (σ c * B.β v y) • w := ht
      have hgt : g * t * g⁻¹ ∈ suPair σ n v w := (Subgroup.mem_normalizer_iff.mp hg t).1 ht_mem
      obtain ⟨c', hc'⟩ := exists_mulVec_of_mem_suPair hc hvv hww hvw hgt
      have hc'ρ : ∀ y, ρ (g * t * g⁻¹) y =
          y + (c' * B.β w y) • v + (σ c' * B.β v y) • w := hc'
      refine ⟨c', fun y => ?_⟩
      have ht' : ∀ y, ρ t y = y + B.β w y • (c • v) + B.β v y • (σ c • w) := by
        intro y
        rw [htρ y, smul_smul, smul_smul, mul_comm c (B.β w y), mul_comm (σ c) (B.β v y)]
      have hconj := rep_conj_apply hρ ht' g y
      rw [map_smul, map_smul] at hconj
      have h := hconj.symm.trans (hc'ρ y)
      rw [add_assoc, add_assoc] at h
      exact add_left_cancel h
    have hI : ∀ c : F, σ d * c * a + σ a * σ c * d = 0 := by
      intro c
      obtain ⟨c', hc'⟩ := hkey c
      have he := hc' w'
      rw [hrw', hpw', hww', hvw', mul_zero, zero_smul, zero_add, mul_one] at he
      have hsub : σ d • (c • ρ g v) + σ a • (σ c • ρ g w) =
          (σ d * c * a + σ a * σ c * d) • v +
            (σ d * c * b + σ a * σ c * e) • w := by
        rw [← hab, ← hde]
        simp only [smul_add, smul_smul, add_smul, mul_assoc]
        abel
      have heq : (σ d * c * a + σ a * σ c * d) • v +
            (σ d * c * b + σ a * σ c * e) • w = (0 : F) • v + (σ c') • w := by
        rw [zero_smul, zero_add]
        exact hsub.symm.trans he
      exact (coeff heq).1
    have hIII : ∀ c : F, σ e * c * b + σ b * σ c * e = 0 := by
      intro c
      obtain ⟨c', hc'⟩ := hkey c
      have he := hc' v'
      rw [hrv', hpv', hwv', hvv', mul_one, mul_zero, zero_smul, add_zero] at he
      have hsub : σ e • (c • ρ g v) + σ b • (σ c • ρ g w) =
          (σ e * c * a + σ b * σ c * d) • v +
            (σ e * c * b + σ b * σ c * e) • w := by
        rw [← hab, ← hde]
        simp only [smul_add, smul_smul, add_smul, mul_assoc]
        abel
      have heq : (σ e * c * a + σ b * σ c * d) • v +
            (σ e * c * b + σ b * σ c * e) • w = (c') • v + (0 : F) • w := by
        rw [zero_smul, add_zero]
        exact hsub.symm.trans he
      exact (coeff heq).2
    have hA : d = 0 ∨ a = 0 := by
      have hu : σ d * a = 0 := by
        by_contra hu
        have hIu : ∀ c : F, (σ d * a) * c + σ ((σ d * a) * c) = 0 := by
          intro c
          have h := hI c
          have hgoal : (σ d * a) * c + σ ((σ d * a) * c) =
              σ d * c * a + σ a * σ c * d := by
            rw [map_mul, map_mul, hσ]
            ring
          rw [hgoal, h]
        have hfix : ∀ c₀ : F, σ c₀ = c₀ := by
          intro c₀
          have h := hIu (c₀ * (σ d * a)⁻¹)
          have harg : (σ d * a) * (c₀ * (σ d * a)⁻¹) = c₀ := by
            rw [mul_comm c₀ ((σ d * a)⁻¹), ← mul_assoc, mul_inv_cancel₀ hu, one_mul]
          rw [harg] at h
          have hneg : σ c₀ = -c₀ := by
            rw [eq_neg_iff_add_eq_zero, add_comm]
            exact h
          rwa [CharTwo.neg_eq] at hneg
        obtain ⟨c₀, hc₀⟩ := exists_unitaryInvolution_ne hc
        exact hc₀ (hfix c₀)
      rcases mul_eq_zero.mp hu with h | h
      · left
        exact (map_eq_zero_iff _ σ.injective).mp h
      · right
        exact h
    have hB : e = 0 ∨ b = 0 := by
      have hu : σ e * b = 0 := by
        by_contra hu
        have hIIIu : ∀ c : F, (σ e * b) * c + σ ((σ e * b) * c) = 0 := by
          intro c
          have h := hIII c
          have hgoal : (σ e * b) * c + σ ((σ e * b) * c) =
              σ e * c * b + σ b * σ c * e := by
            rw [map_mul, map_mul, hσ]
            ring
          rw [hgoal, h]
        have hfix : ∀ c₀ : F, σ c₀ = c₀ := by
          intro c₀
          have h := hIIIu (c₀ * (σ e * b)⁻¹)
          have harg : (σ e * b) * (c₀ * (σ e * b)⁻¹) = c₀ := by
            rw [mul_comm c₀ ((σ e * b)⁻¹), ← mul_assoc, mul_inv_cancel₀ hu, one_mul]
          rw [harg] at h
          have hneg : σ c₀ = -c₀ := by
            rw [eq_neg_iff_add_eq_zero, add_comm]
            exact h
          rwa [CharTwo.neg_eq] at hneg
        obtain ⟨c₀, hc₀⟩ := exists_unitaryInvolution_ne hc
        exact hc₀ (hfix c₀)
      rcases mul_eq_zero.mp hu with h | h
      · left
        exact (map_eq_zero_iff _ σ.injective).mp h
      · right
        exact h
    have hpne : ρ g v ≠ 0 := fun h => hv0 (hker g v h)
    have hrne : ρ g w ≠ 0 := fun h => hw0 (hker g w h)
    rcases hA with hd0 | ha0
    · rcases hB with he0 | hb0
      · exfalso
        apply hrne
        rw [← hde, hd0, he0, zero_smul, zero_smul, add_zero]
      · left
        refine ⟨a, e, ?_, ?_⟩
        · rw [← hab, hb0, zero_smul, add_zero]
        · rw [← hde, hd0, zero_smul, zero_add]
    · rcases hB with he0 | hb0
      · right
        refine ⟨b, d, ?_, ?_⟩
        · rw [← hab, ha0, zero_smul, zero_add]
        · rw [← hde, he0, zero_smul, add_zero]
      · exfalso
        apply hpne
        rw [← hab, ha0, hb0, zero_smul, zero_smul, add_zero]
  · intro hmono
    rw [Subgroup.mem_normalizer_iff]
    intro s
    constructor
    · exact mono_conj g hmono s
    · intro hs
      have h2 := mono_conj g⁻¹ (mono_inv g hmono) (g * s * g⁻¹) hs
      rwa [show g⁻¹ * (g * s * g⁻¹) * (g⁻¹)⁻¹ = s by group] at h2

theorem suStabRad_le_normalizer_suPair {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    {hc : Nat.card F = (2 ^ f) ^ 2} {n : ℕ} {v w v' w' : Fin n → F}
    (hfr : SUFrame hc n v w v' w') :
    suStabRad hc n (Submodule.span F {v, w}) (suFrame_isTotallyIsotropic hfr) ≤
      Subgroup.normalizer
        (suPair (unitaryInvolution F 2 f) n v w : Set ↥(SU (unitaryInvolution F 2 f) n)) := by
  intro g hg
  rw [mem_normalizer_suPair_iff hfr]
  left
  have hv : v ∈ Submodule.span F ({v, w} : Set (Fin n → F)) := Submodule.subset_span (by simp)
  have hw : w ∈ Submodule.span F ({v, w} : Set (Fin n → F)) := Submodule.subset_span (by simp)
  have hgv : natRep (SU (unitaryInvolution F 2 f) n) g v = v := (mem_rad.mp hg).1 v hv
  have hgw : natRep (SU (unitaryInvolution F 2 f) n) g w = w := (mem_rad.mp hg).1 w hw
  exact ⟨1, 1, by simpa using hgv, by simpa using hgw⟩

end CFSG.StandardType.LieKnownR2.Short
