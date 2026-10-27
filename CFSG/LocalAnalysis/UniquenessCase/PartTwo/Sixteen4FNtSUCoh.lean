module

public import CFSG.Quasithin.Background.JonesParshallBasic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin.JonesParshall

private lemma w183_nsmul_eq_self_of_odd {M : Type*} [AddCommMonoid M]
    (h2 : ∀ x : M, x + x = 0) {n : ℕ} (hn : Odd n) (x : M) : n • x = x := by
  obtain ⟨k, hk⟩ := hn
  rw [hk, add_nsmul, mul_nsmul, two_nsmul, h2 x, nsmul_zero, one_nsmul, zero_add]

theorem s16nt_normalize_cocycle {Γ : Type} [Group Γ] [Finite Γ] {N : Type} [AddCommGroup N]
    [Module (ZMod 2) N] (ρ : Representation (ZMod 2) Γ N) (T : Subgroup Γ)
    (hodd : Odd (Nat.card T)) (hfix : ∀ v : N, (∀ t ∈ T, ρ t v = v) → v = 0) {c : Γ → N}
    (hc : c ∈ Z1 ρ) : ∃ v : N, ∀ m ∈ Subgroup.normalizer (T : Set Γ), c m = ρ m v - v := by
  classical
  haveI : Fintype ↥T := Fintype.ofFinite ↥T
  have h2 : ∀ x : N, x + x = 0 := fun x => by
    have h := two_smul (ZMod 2) x
    rw [show (2 : ZMod 2) = 0 from by decide, zero_smul] at h
    exact h.symm
  have hneg : ∀ x : N, -x = x := fun x => by
    rw [neg_eq_iff_add_eq_zero]
    exact h2 x
  let b : N := ∑ t : ↥T, c (t : Γ)
  refine ⟨b, ?_⟩
  have hct : ∀ t' : ↥T, c (t' : Γ) = ρ (t' : Γ) b - b := by
    intro t'
    have hreindex : ∑ t : ↥T, c ((t' : Γ) * (t : Γ)) = b := by
      have h := Equiv.sum_comp (Equiv.mulLeft t') (fun t : ↥T => c (t : Γ))
      simpa [b] using h
    have hsplit : ∑ t : ↥T, c ((t' : Γ) * (t : Γ)) =
        (Nat.card ↥T) • c (t' : Γ) + ρ (t' : Γ) b := by
      calc ∑ t : ↥T, c ((t' : Γ) * (t : Γ))
          = ∑ t : ↥T, (c (t' : Γ) + ρ (t' : Γ) (c (t : Γ))) :=
              Finset.sum_congr rfl fun t _ => hc (t' : Γ) (t : Γ)
        _ = ∑ t : ↥T, c (t' : Γ) + ∑ t : ↥T, ρ (t' : Γ) (c (t : Γ)) :=
              Finset.sum_add_distrib
        _ = (Nat.card ↥T) • c (t' : Γ) + ρ (t' : Γ) b := by
              rw [Finset.sum_const, Finset.card_univ, Nat.card_eq_fintype_card, ← map_sum]
    have hcb : c (t' : Γ) + ρ (t' : Γ) b = b := by
      rw [← w183_nsmul_eq_self_of_odd (n := Nat.card ↥T) h2 hodd (c (t' : Γ)),
        ← hsplit, hreindex]
    rw [sub_eq_add_neg, hneg b]
    calc c (t' : Γ) = (c (t' : Γ) + ρ (t' : Γ) b) + ρ (t' : Γ) b := by
            rw [add_assoc, h2 (ρ (t' : Γ) b), add_zero]
      _ = b + ρ (t' : Γ) b := by rw [hcb]
      _ = ρ (t' : Γ) b + b := add_comm _ _
  have hc1 : c - coboundary ρ b ∈ Z1 ρ := sub_mem hc (B1_le_Z1 ρ ⟨b, rfl⟩)
  have hc1T : ∀ t ∈ T, (c - coboundary ρ b) t = 0 := by
    intro t ht
    change c t - (ρ t b - b) = 0
    rw [hct ⟨t, ht⟩, sub_self]
  intro m hm
  have key : ∀ t ∈ T, ρ (m * t * m⁻¹) ((c - coboundary ρ b) m) =
      (c - coboundary ρ b) m := by
    intro t ht
    have hu : m * t * m⁻¹ ∈ T := ((Subgroup.mem_normalizer_iff (H := T)).1 hm t).1 ht
    have h1 : (c - coboundary ρ b) (m * t) = (c - coboundary ρ b) m := by
      have h := hc1 m t
      change (c - coboundary ρ b) (m * t) =
        (c - coboundary ρ b) m + ρ m ((c - coboundary ρ b) t) at h
      rw [hc1T t ht, map_zero, add_zero] at h
      exact h
    have h2' : (c - coboundary ρ b) (m * t) =
        ρ (m * t * m⁻¹) ((c - coboundary ρ b) m) := by
      have h := hc1 (m * t * m⁻¹) m
      have hprod : (m * t * m⁻¹) * m = m * t := by group
      rw [hprod] at h
      change (c - coboundary ρ b) (m * t) = (c - coboundary ρ b) (m * t * m⁻¹) +
        ρ (m * t * m⁻¹) ((c - coboundary ρ b) m) at h
      rw [hc1T (m * t * m⁻¹) hu, zero_add] at h
      exact h
    rw [← h2', h1]
  have hfixm : ∀ t'' ∈ T, ρ t'' ((c - coboundary ρ b) m) = (c - coboundary ρ b) m := by
    intro t'' ht''
    have ht : m⁻¹ * t'' * m ∈ T := by
      have h := ((Subgroup.mem_normalizer_iff (H := T)).1 (inv_mem hm) t'').1 ht''
      simpa using h
    have hconj : m * (m⁻¹ * t'' * m) * m⁻¹ = t'' := by group
    have hk := key (m⁻¹ * t'' * m) ht
    rwa [hconj] at hk
  have hm0 : (c - coboundary ρ b) m = 0 := hfix _ hfixm
  change c m - (ρ m b - b) = 0 at hm0
  exact sub_eq_zero.mp hm0

theorem s16nt_h1_le_of_eval {Γ : Type} [Group Γ] [Finite Γ] {N : Type} [AddCommGroup N]
    [Module (ZMod 2) N] [Finite N] (ρ : Representation (ZMod 2) Γ N) (M : Subgroup Γ) (s : Γ)
    (hgen : Subgroup.closure ((M : Set Γ) ∪ {s}) = ⊤)
    (hnorm : ∀ c ∈ Z1 ρ, ∃ v : N, ∀ m ∈ M, c m = ρ m v - v) (S : Set Γ)
    (hS : ∀ d ∈ S, d ∈ M ∧ d * s = s * d) (F : Submodule (ZMod 2) N)
    (hF : ∀ v : N, (∀ d ∈ S, ρ d v = v) → v ∈ F) :
    Module.finrank (ZMod 2) (H1 ρ) ≤ Module.finrank (ZMod 2) F := by
  classical
  haveI : Finite (Γ → N) := Pi.finite
  let P : Submodule (ZMod 2) (Γ → N) :=
    { carrier := {c | ∀ m ∈ M, c m = 0}
      add_mem' := by
        intro a b ha hb m hm
        simp only [Pi.add_apply, ha m hm, hb m hm, add_zero]
      zero_mem' := fun m hm => rfl
      smul_mem' := by
        intro a c hc m hm
        simp only [Pi.smul_apply, hc m hm, smul_zero] }
  let Z₀ : Submodule (ZMod 2) (Γ → N) := Z1 ρ ⊓ P
  let q : ↥Z₀ →ₗ[ZMod 2] H1 ρ :=
    ((B1 ρ).comap (Z1 ρ).subtype).mkQ.comp (Submodule.inclusion inf_le_left)
  have hq : Function.Surjective q := by
    intro x
    obtain ⟨c, hc⟩ := ((B1 ρ).comap (Z1 ρ).subtype).mkQ_surjective x
    obtain ⟨v, hv⟩ := hnorm c.1 c.2
    have hc'Z1 : c.1 - coboundary ρ v ∈ Z1 ρ :=
      sub_mem c.2 (B1_le_Z1 ρ ⟨v, rfl⟩)
    have hc'P : c.1 - coboundary ρ v ∈ P := by
      intro m hm
      change c.1 m - (ρ m v - v) = 0
      rw [hv m hm, sub_self]
    refine ⟨⟨c.1 - coboundary ρ v, ⟨hc'Z1, hc'P⟩⟩, ?_⟩
    have hmk : ((B1 ρ).comap (Z1 ρ).subtype).mkQ
        (⟨c.1 - coboundary ρ v, hc'Z1⟩ : ↥(Z1 ρ)) =
        ((B1 ρ).comap (Z1 ρ).subtype).mkQ c := by
      rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
      change (⟨c.1 - coboundary ρ v, hc'Z1⟩ : ↥(Z1 ρ)).1 - c.1 ∈ B1 ρ
      have h : (⟨c.1 - coboundary ρ v, hc'Z1⟩ : ↥(Z1 ρ)).1 - c.1 =
          -coboundary ρ v := by
        change (c.1 - coboundary ρ v) - c.1 = -coboundary ρ v
        abel
      rw [h]
      exact neg_mem ⟨v, rfl⟩
    change ((B1 ρ).comap (Z1 ρ).subtype).mkQ
      ((Submodule.inclusion inf_le_left) ⟨c.1 - coboundary ρ v, ⟨hc'Z1, hc'P⟩⟩) = x
    rw [Submodule.inclusion_apply, hmk, hc]
  have hle1 : Module.finrank (ZMod 2) (H1 ρ) ≤ Module.finrank (ZMod 2) ↥Z₀ :=
    LinearMap.finrank_le_finrank_of_surjective hq
  let ev : ↥Z₀ →ₗ[ZMod 2] N := (LinearMap.proj s).comp Z₀.subtype
  have hev : ∀ c : ↥Z₀, ev c = 0 → c = 0 := by
    intro c hc0
    have hc0' : c.1 s = 0 := hc0
    let H₀ : Subgroup Γ :=
      { carrier := {g | c.1 g = 0}
        one_mem' := by
          have h := c.2.1 1 1
          rw [one_mul, map_one, Module.End.one_apply] at h
          exact left_eq_add.mp h
        mul_mem' := by
          intro a b ha hb
          have h := c.2.1 a b
          rw [ha, hb, map_zero, add_zero] at h
          exact h
        inv_mem' := by
          intro a ha
          have h1 : c.1 1 = 0 := by
            have h := c.2.1 1 1
            rw [one_mul, map_one, Module.End.one_apply] at h
            exact left_eq_add.mp h
          have h := c.2.1 a a⁻¹
          rw [mul_inv_cancel, h1, ha, zero_add] at h
          calc c.1 a⁻¹ = (ρ a⁻¹) (ρ a (c.1 a⁻¹)) := by
                rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
                  Module.End.one_apply]
            _ = (ρ a⁻¹) 0 := by rw [h.symm]
            _ = 0 := map_zero _ }
    have hM : M ≤ H₀ := fun m hm => c.2.2 m hm
    have hs : s ∈ H₀ := hc0'
    have htop : (⊤ : Subgroup Γ) ≤ H₀ := by
      rw [← hgen]
      exact (Subgroup.closure_le H₀).mpr (fun x hx => by
        rcases hx with hxM | hxs
        · exact hM hxM
        · rw [Set.mem_singleton_iff] at hxs
          rw [hxs]
          exact hs)
    exact Subtype.ext (funext fun g => htop (Subgroup.mem_top g))
  have hev_inj : Function.Injective ev := by
    intro a b hab
    have h : ev (a - b) = 0 := by rw [map_sub, hab, sub_self]
    exact sub_eq_zero.mp (hev (a - b) h)
  have hrange : LinearMap.range ev ≤ F := by
    rintro x ⟨c, rfl⟩
    refine hF (ev c) (fun d hd => ?_)
    obtain ⟨hdM, hds⟩ := hS d hd
    have h1 : c.1 (d * s) = ρ d (c.1 s) := by
      have h := c.2.1 d s
      rw [c.2.2 d hdM, zero_add] at h
      exact h
    have h2 : c.1 (s * d) = c.1 s := by
      have h := c.2.1 s d
      rw [c.2.2 d hdM, map_zero, add_zero] at h
      exact h
    have h3 : ρ d (c.1 s) = c.1 s := by
      rw [← h1, hds, h2]
    change ρ d (c.1 s) = c.1 s
    exact h3
  have hle2 : Module.finrank (ZMod 2) ↥Z₀ ≤ Module.finrank (ZMod 2) F := by
    rw [← LinearMap.finrank_range_of_inj hev_inj]
    exact Submodule.finrank_mono hrange
  exact hle1.trans hle2

theorem s16nt_h1_le_of_normalizer {Γ : Type} [Group Γ] [Finite Γ] {N : Type} [AddCommGroup N]
    [Module (ZMod 2) N] [Finite N] (ρ : Representation (ZMod 2) Γ N) (T : Subgroup Γ)
    (hodd : Odd (Nat.card T)) (hfix : ∀ v : N, (∀ t ∈ T, ρ t v = v) → v = 0) (s : Γ)
    (hgen : Subgroup.closure ((Subgroup.normalizer (T : Set Γ) : Set Γ) ∪ {s}) = ⊤)
    (S : Set Γ) (hS : ∀ d ∈ S, d ∈ Subgroup.normalizer (T : Set Γ) ∧ d * s = s * d)
    (F : Submodule (ZMod 2) N) (hF : ∀ v : N, (∀ d ∈ S, ρ d v = v) → v ∈ F) :
    Module.finrank (ZMod 2) (H1 ρ) ≤ Module.finrank (ZMod 2) F :=
  s16nt_h1_le_of_eval ρ _ s hgen (fun _ hc => s16nt_normalize_cocycle ρ T hodd hfix hc) S hS F hF

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

end
