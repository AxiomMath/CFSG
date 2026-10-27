module

public import CFSG.LocalAnalysis.StandardType.FS81.NoTransvOrth
public import CFSG.HardMathSupport.Timmesfeld.LinearRank.PermOrbitCount

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly MulAction
open scoped Matrix

variable {G : Type} [Group G] [Finite G]

@[expose] def MonoA {n : ℕ} (B : Basis3 G (n + 1)) (f : G) (σ : Equiv.Perm (Fin (n + 1)))
    (s : Fin (n + 1) → ZMod 3) : Prop :=
  σ 0 = 0 ∧ IsSign s ∧ ∀ e : Coords (n + 1), e 0 = 0 → f * B.vec e * f⁻¹ = B.vec (spMat σ s *ᵥ e)

namespace MonoA

variable {n : ℕ} {B : Basis3 G (n + 1)}

theorem mulVec_zero {σ : Equiv.Perm (Fin (n + 1))} {s : Fin (n + 1) → ZMod 3} (hσ : σ 0 = 0)
    {e : Coords (n + 1)} (he : e 0 = 0) : (spMat σ s *ᵥ e) 0 = 0 := by
  have : σ.symm 0 = 0 := by rw [Equiv.symm_apply_eq, hσ]
  simp [spMat_mulVec, this, he]

omit [Finite G] in
theorem one : MonoA B 1 1 (fun _ => 1) :=
  ⟨rfl, fun _ => Or.inl rfl, fun e _ => by rw [spMat_one, Matrix.one_mulVec, one_mul, inv_one,
    mul_one]⟩

omit [Finite G] in
theorem unique {f : G} {σ σ' : Equiv.Perm (Fin (n + 1))} {s s' : Fin (n + 1) → ZMod 3}
    (h : MonoA B f σ s) (h' : MonoA B f σ' s') : σ = σ' := by
  refine Equiv.ext fun j => ?_
  by_cases hj : j = 0
  · rw [hj, h.1, h'.1]
  · have he : (Pi.single j 1 : Coords (n + 1)) 0 = 0 := Pi.single_eq_of_ne (Ne.symm hj) _
    have h1 := B.vec_injective ((h.2.2 _ he).symm.trans (h'.2.2 _ he))
    rw [spMat_mulVec_single, spMat_mulVec_single] at h1
    have h2 := congrFun h1 (σ j)
    rw [Pi.single_eq_same] at h2
    by_contra hne
    rw [Pi.single_eq_of_ne hne, mul_one] at h2
    rcases h.2.1 j with hs | hs <;> rw [hs] at h2 <;> exact absurd h2 (by decide)

omit [Finite G] in
theorem mul {f g : G} {σ τ : Equiv.Perm (Fin (n + 1))} {s t : Fin (n + 1) → ZMod 3}
    (hg : MonoA B g σ s) (hf : MonoA B f τ t) :
    MonoA B (f * g) (τ * σ) (fun j => t (σ j) * s j) := by
  refine ⟨by rw [Equiv.Perm.mul_apply, hg.1, hf.1], fun j => ?_, fun e he => ?_⟩
  · show t (σ j) * s j = 1 ∨ t (σ j) * s j = -1
    rcases hf.2.1 (σ j) with h1 | h1 <;> rcases hg.2.1 j with h2 | h2 <;> rw [h1, h2] <;> decide
  · rw [show f * g * B.vec e * (f * g)⁻¹ = f * (g * B.vec e * g⁻¹) * f⁻¹ by group, hg.2.2 e he,
      hf.2.2 _ (mulVec_zero hg.1 he), Matrix.mulVec_mulVec, spMat_mul]

omit [Finite G] in
theorem centralizes {f : G} {s : Fin (n + 1) → ZMod 3} (h : MonoA B f 1 s) (hf3 : f ^ 3 = 1)
    {e : Coords (n + 1)} (he : e 0 = 0) : f * B.vec e * f⁻¹ = B.vec e := by
  have h1 : ∀ v : Coords (n + 1), v 0 = 0 → f * B.vec v * f⁻¹ = B.vec (fun i => s i * v i) :=
    fun v hv => by rw [h.2.2 v hv, spMat_mulVec]; rfl
  have h3 : B.vec e = B.vec (fun i => s i * (s i * (s i * e i))) := by
    calc B.vec e = f ^ 3 * B.vec e * (f ^ 3)⁻¹ := by rw [hf3, one_mul, inv_one, mul_one]
      _ = f * (f * (f * B.vec e * f⁻¹) * f⁻¹) * f⁻¹ := by rw [pow_three]; group
      _ = B.vec (fun i => s i * (s i * (s i * e i))) := by
        rw [h1 e he, h1 (fun i => s i * e i) (by simp [he]),
          h1 (fun i => s i * (s i * e i)) (by simp [he])]
  have h4 := B.vec_injective h3
  rw [h1 e he]
  congr 1
  funext i
  have key : ∀ x y : ZMod 3, (y = 1 ∨ y = -1) → x = y * (y * (y * x)) → y * x = x := by decide
  exact key _ _ (h.2.1 i) (congrFun h4 i)

end MonoA

omit [Finite G] in
theorem monoA_of_mem {n : ℕ} {B : Basis3 G (n + 1)} {b₀ : G} {K E : Subgroup G}
    (hB : Adapted B b₀ K E)
    (hCm : B.realized (Subgroup.centralizer ({b₀} : Set G)) = monoFix0 n ∨
      B.realized (Subgroup.centralizer ({b₀} : Set G)) = evenFix0 n)
    (htr : TransvAll b₀ K E) {f : G} (hfN : f ∈ Subgroup.normalizer (E : Set G))
    (hfb : b₀⁻¹ * (f * b₀ * f⁻¹) ∈ E ⊓ K) : ∃ σ s, MonoA B f σ s := by
  obtain ⟨t, htN, htA, htb⟩ := htr.2 _ hfb
  set c := t⁻¹ * f with hc
  have hcN : c ∈ Subgroup.normalizer (E : Set G) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ htN) hfN
  have hcb : c * b₀ * c⁻¹ = b₀ := by
    have h1 : f * b₀ * f⁻¹ = t * b₀ * t⁻¹ := by rw [htb, mul_inv_cancel_left]
    rw [hc, show t⁻¹ * f * b₀ * (t⁻¹ * f)⁻¹ = t⁻¹ * (f * b₀ * f⁻¹) * t by group, h1]
    group
  have hcC : c ∈ Subgroup.centralizer ({b₀} : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun x hx => by
      rw [Set.mem_singleton_iff.mp hx]
      exact (mul_inv_eq_iff_eq_mul.mp hcb).symm
  have hcS : c ∈ Subgroup.normalizer (B.span : Set G) := by
    rw [hB.1]
    exact hcN
  have hφ : ∀ y : ↥B.span,
      ((B.span.normalizerMonoidHom ⟨c, hcS⟩ y : ↥B.span) : G) = c * y * c⁻¹ := fun y =>
    Subgroup.normalizerMonoidHom_apply_apply_coe _ _ _
  have hM := B.acts_matOf hφ
  have hMr : B.matOf (B.span.normalizerMonoidHom ⟨c, hcS⟩) ∈
      B.realized (Subgroup.centralizer ({b₀} : Set G)) := ⟨c, hcC, hM⟩
  obtain ⟨σ, s, hs, hσ, hMeq⟩ : ∃ σ s, IsSign s ∧ σ 0 = 0 ∧
      B.matOf (B.span.normalizerMonoidHom ⟨c, hcS⟩) = spMat σ s := by
    rcases hCm with h | h <;> rw [h] at hMr
    · obtain ⟨σ, s, hs, ⟨hσ, -⟩, hMeq⟩ := hMr
      exact ⟨σ, s, hs, hσ, hMeq⟩
    · obtain ⟨σ, s, hs, ⟨hσ, -, -⟩, hMeq⟩ := hMr
      exact ⟨σ, s, hs, hσ, hMeq⟩
  rw [hMeq] at hM
  refine ⟨σ, s, hσ, hs, fun e he => ?_⟩
  have h2 : c * B.vec e * c⁻¹ = B.vec (spMat σ s *ᵥ e) := B.acts_vec' hcS hM e
  have h3 : B.vec (spMat σ s *ᵥ e) ∈ E ⊓ K := by
    refine ⟨?_, B.vec_mem_of_zero hB.2.2 (MonoA.mulVec_zero hσ he)⟩
    rw [← hB.1]
    exact B.vec_mem_span _
  calc f * B.vec e * f⁻¹ = t * (c * B.vec e * c⁻¹) * t⁻¹ := by rw [hc]; group
    _ = B.vec (spMat σ s *ᵥ e) := by rw [h2, htA _ h3]

theorem orth_noOffenderA {n : ℕ} {B : Basis3 G (n + 1)} {b₀ : G} {K E : Subgroup G}
    (hB : Adapted B b₀ K E) (hord : orderOf b₀ = 3)
    (hdisj : Disjoint (Subgroup.zpowers b₀) (E ⊓ K)) (hAcard : Nat.card ↥(E ⊓ K) = 3 ^ n)
    (hCm : B.realized (Subgroup.centralizer ({b₀} : Set G)) = monoFix0 n ∨
      B.realized (Subgroup.centralizer ({b₀} : Set G)) = evenFix0 n)
    (htr : TransvAll b₀ K E) : NoOffenderA b₀ K E := by
  classical
  intro F hFN hF hFb hFA
  set CA := Subgroup.centralizer ((E ⊓ K : Subgroup G) : Set G) with hCA
  have hFc : ∀ x y : ↥F, x * y = y * x := fun x y => hF.1.is_comm.comm x y
  have hF3 : ∀ x : ↥F, x ^ 3 = 1 := fun x => Subtype.ext (by simpa using hF.2 x x.2)
  have hdisj' : Disjoint (Subgroup.zpowers b₀) (B.span ⊓ K) := by
    rw [hB.1]
    exact hdisj
  have hco : ∀ {a : G}, a ∈ E ⊓ K → ∃ e : Coords (n + 1), e 0 = 0 ∧ B.vec e = a := by
    intro a ha
    have haS : a ∈ B.span := by
      rw [hB.1]
      exact ha.1
    exact ⟨B.coords ⟨a, haS⟩, B.coords_zero_of_mem hB.2.1 hord hB.2.2 hdisj' ⟨a, haS⟩ ha.2,
      B.vec_coords _⟩
  choose σf sf hσf using fun f : ↥F => monoA_of_mem hB hCm htr (hFN f.2) (hFb f f.2)
  let ρ : ↥F →* Equiv.Perm (Fin (n + 1)) :=
    { toFun := σf
      map_one' := MonoA.unique (hσf 1) MonoA.one
      map_mul' := fun f g => MonoA.unique (hσf (f * g)) (MonoA.mul (hσf g) (hσf f)) }
  have hρ : ∀ f, ρ f = σf f := fun _ => rfl
  set U := ρ.range with hU
  have hUc : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a := by
    rintro _ ⟨f, rfl⟩ _ ⟨g, rfl⟩
    rw [← map_mul, ← map_mul, hFc]
  have hU3 : ∀ x ∈ U, x ^ 3 = 1 := by
    rintro _ ⟨f, rfl⟩
    rw [← map_pow, hF3, map_one]
  have hcount := CFSG.HardMathSupport.Timmesfeld.LinearRank.card_sq_mul_pow_orbits_le
    Nat.prime_three (by norm_num) U hUc hU3
  have hker : ∀ f : ↥F, ρ f = 1 → (f : G) ∈ CA := by
    intro f hf
    have hf' : σf f = 1 := hf
    have h1 : MonoA B (f : G) 1 (sf f) := hf' ▸ hσf f
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    obtain ⟨e, he, rfl⟩ := hco ha
    exact (mul_inv_eq_iff_eq_mul.mp (MonoA.centralizes h1 (hF.2 f f.2) he)).symm
  have hUne : U ≠ ⊥ := by
    intro hbot
    apply hFA
    intro f hf
    refine hker ⟨f, hf⟩ ?_
    have : ρ ⟨f, hf⟩ ∈ U := ⟨_, rfl⟩
    rw [hbot] at this
    exact this
  have hkerle : ρ.ker ≤ (F ⊓ CA).subgroupOf F := fun f hf =>
    Subgroup.mem_subgroupOf.mpr ⟨f.2, hker f hf⟩
  have hidx : (F ⊓ CA).relIndex F ≤ Nat.card U := by
    have h1 : (F ⊓ CA).relIndex F ∣ ρ.ker.index := Subgroup.index_dvd_of_le hkerle
    rw [Subgroup.index_ker] at h1
    exact Nat.le_of_dvd Nat.card_pos h1
  have hU3le : 3 ≤ Nat.card U := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hUp : IsPGroup 3 U := fun x => ⟨1, Subtype.ext (by simpa using hU3 x x.2)⟩
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hUp
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact hUne (Subgroup.eq_bot_of_card_eq _ (by rw [hk, pow_zero]))
    rw [hk]
    calc 3 = 3 ^ 1 := by norm_num
      _ ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) (Nat.one_le_iff_ne_zero.mpr hk0)
  have h0 : ∀ u : ↥U, u • (0 : Fin (n + 1)) = 0 := by
    rintro ⟨_, f, rfl⟩
    exact (hσf f).1
  have hout0 : Quotient.out (Quotient.mk (orbitRel U (Fin (n + 1))) 0) = 0 := by
    obtain ⟨u, hu⟩ := mem_orbit_iff.mp
      (orbitRel_apply.mp (Quotient.mk_out (s := orbitRel U (Fin (n + 1))) 0))
    rw [← hu, h0]
  set C₀ := E ⊓ K ⊓ Subgroup.centralizer (F : Set G) with hC₀
  have hC₀S : ∀ a : ↥C₀, (a : G) ∈ B.span := fun a => by
    rw [hB.1]
    exact a.2.1.1
  let ev : ↥C₀ → Coords (n + 1) := fun a => B.coords ⟨a, hC₀S a⟩
  have hev : ∀ a : ↥C₀, B.vec (ev a) = a := fun a => B.vec_coords _
  have hev0 : ∀ a : ↥C₀, ev a 0 = 0 := fun a =>
    B.coords_zero_of_mem hB.2.1 hord hB.2.2 hdisj' _ a.2.1.2
  have hevfix : ∀ (a : ↥C₀) (f : ↥F) (j : Fin (n + 1)), ev a (σf f j) = sf f j * ev a j := by
    intro a f j
    have hfix : (f : G) * B.vec (ev a) * (f : G)⁻¹ = B.vec (ev a) := by
      rw [hev, Subgroup.mem_centralizer_iff.mp a.2.2 f f.2, mul_inv_cancel_right]
    rw [(hσf f).2.2 _ (hev0 a)] at hfix
    have h2 := congrFun (B.vec_injective hfix) (σf f j)
    simp only [spMat_mulVec, Equiv.symm_apply_apply] at h2
    exact h2.symm
  let ω₀ : orbitRel.Quotient U (Fin (n + 1)) := Quotient.mk (orbitRel U (Fin (n + 1))) 0
  let Φ : ↥C₀ × ZMod 3 → (orbitRel.Quotient U (Fin (n + 1)) → ZMod 3) :=
    fun p ω => if ω = ω₀ then p.2 else ev p.1 (Quotient.out ω)
  have hΦ : Function.Injective Φ := by
    rintro ⟨a, z⟩ ⟨a', z'⟩ h
    have hz : z = z' := by
      have := congrFun h ω₀
      simpa [Φ] using this
    have hev' : ev a = ev a' := by
      funext i
      obtain ⟨u, hu⟩ := mem_orbit_iff.mp
        (orbitRel_apply.mp (Quotient.mk_out (s := orbitRel U (Fin (n + 1))) i))
      obtain ⟨f, hf⟩ := u.2
      have hui : σf f i = Quotient.out (Quotient.mk (orbitRel U (Fin (n + 1))) i) := by
        rw [← hu, ← hρ, hf]
        rfl
      by_cases hω : Quotient.mk (orbitRel U (Fin (n + 1))) i = ω₀
      · have hi0 : i = 0 := by
          have h1 : σf f i = σf f 0 := by
            rw [hui, hω, (hσf f).1]
            exact hout0
          exact (σf f).injective h1
        rw [hi0, hev0, hev0]
      · have h1 := congrFun h (Quotient.mk (orbitRel U (Fin (n + 1))) i)
        simp only [Φ, if_neg hω] at h1
        rw [← hui, hevfix a f i, hevfix a' f i] at h1
        rcases (hσf f).2.1 i with hs | hs <;> rw [hs] at h1
        · simpa using h1
        · exact mul_left_cancel₀ (by decide : (-1 : ZMod 3) ≠ 0) h1
    have ha : a = a' := Subtype.ext (by rw [← hev a, ← hev a', hev'])
    rw [ha, hz]
  have hfix : Nat.card ↥C₀ * 3 ≤ 3 ^ Nat.card (orbitRel.Quotient U (Fin (n + 1))) := by
    have := Nat.card_le_card_of_injective Φ hΦ
    rwa [Nat.card_prod, Nat.card_fun, Nat.card_zmod] at this
  rw [hAcard]
  have hX : 0 < Nat.card ↥C₀ := Nat.card_pos
  have h1 : Nat.card ↥C₀ * Nat.card U * Nat.card U ≤ 3 ^ n := by
    have h2 : 3 * (Nat.card ↥C₀ * Nat.card U * Nat.card U) ≤ 3 * 3 ^ n := by
      calc 3 * (Nat.card ↥C₀ * Nat.card U * Nat.card U) =
          (Nat.card ↥C₀ * 3) * (Nat.card U * Nat.card U) := by ring
        _ ≤ 3 ^ Nat.card (orbitRel.Quotient U (Fin (n + 1))) * (Nat.card U * Nat.card U) :=
          Nat.mul_le_mul_right _ hfix
        _ = Nat.card U ^ 2 * 3 ^ Nat.card (orbitRel.Quotient U (Fin (n + 1))) := by ring
        _ ≤ 3 ^ (n + 1) := hcount
        _ = 3 * 3 ^ n := by ring
    exact Nat.le_of_mul_le_mul_left h2 (by norm_num)
  calc Nat.card ↥C₀ * (F ⊓ CA).relIndex F ≤ Nat.card ↥C₀ * Nat.card U :=
        Nat.mul_le_mul_left _ hidx
    _ < Nat.card ↥C₀ * Nat.card U * Nat.card U :=
        lt_mul_of_one_lt_right (Nat.mul_pos hX (by omega)) (by omega)
    _ ≤ 3 ^ n := h1

theorem orth_kleinSigns {n : ℕ} {B : Basis3 G (n + 1)} {b₀ : G} {K E : Subgroup G}
    (hB : Adapted B b₀ K E)
    (hCm : B.realized (Subgroup.centralizer ({b₀} : Set G)) = monoFix0 n ∨
      B.realized (Subgroup.centralizer ({b₀} : Set G)) = evenFix0 n)
    {s s' : Fin (n + 1) → ZMod 3} (hs : IsSign s ∧ s 0 = 1 ∧ ∏ i : Fin n, s i.succ = 1)
    (hs' : IsSign s' ∧ s' 0 = 1 ∧ ∏ i : Fin n, s' i.succ = 1)
    (hss : IsSign (s * s') ∧ (s * s') 0 = 1 ∧ ∏ i : Fin n, (s * s') i.succ = 1)
    (hcov : ∀ k : Fin (n + 1), k ≠ 0 → s k = -1 ∨ s' k = -1) : KleinSigns B E :=
  ⟨s, s', orth_signRealized hB hCm hs.1 hs.2.1 hs.2.2,
    orth_signRealized hB hCm hs'.1 hs'.2.1 hs'.2.2,
    orth_signRealized hB hCm hss.1 hss.2.1 hss.2.2, hcov⟩

theorem noTransvDataAt_D6 : NoTransvDataAt Row.D6 := by
  intro G _ _ b₀ K E hstd B hB hloc hfus htr
  obtain ⟨-, ⟨⟨hord, -⟩, -⟩, ⟨-, hdisj, -, -, hEKcard, -⟩⟩ := hstd
  have hCm : B.realized (Subgroup.centralizer ({b₀} : Set G)) = monoFix0 6 ∨
      B.realized (Subgroup.centralizer ({b₀} : Set G)) = evenFix0 6 := by
    rcases hloc with ⟨h, -⟩ | ⟨h, -⟩
    · exact Or.inl h
    · exact Or.inr h
  obtain ⟨hsc, hdiag, hct, hd3, hds⟩ := orthSignData (n := 6) (by norm_num) hB hCm
  have hKl : KleinSigns B E := orth_kleinSigns (n := 6) hB hCm
    (s := ![1, -1, -1, -1, -1, 1, 1]) (s' := ![1, 1, 1, -1, -1, -1, -1])
    ⟨by unfold IsSign; decide, by decide, by decide⟩
    ⟨by unfold IsSign; decide, by decide, by decide⟩
    ⟨by unfold IsSign; decide, by decide, by decide⟩ (by decide)
  exact ⟨hsc, hdiag, hct, hKl, hd3, hds, orth_noOffenderA hB hord hdisj hEKcard hCm htr⟩

theorem noTransvDataAt_twD7 : NoTransvDataAt Row.twD7 := by
  intro G _ _ b₀ K E hstd B hB hloc hfus htr
  obtain ⟨-, ⟨⟨hord, -⟩, -⟩, ⟨-, hdisj, -, -, hEKcard, -⟩⟩ := hstd
  have hCm : B.realized (Subgroup.centralizer ({b₀} : Set G)) = monoFix0 7 ∨
      B.realized (Subgroup.centralizer ({b₀} : Set G)) = evenFix0 7 := by
    rcases hloc with ⟨h, -⟩ | ⟨h, -⟩
    · exact Or.inl h
    · exact Or.inr h
  obtain ⟨hsc, hdiag, hct, hd3, hds⟩ := orthSignData (n := 7) (by norm_num) hB hCm
  have hKl : KleinSigns B E := orth_kleinSigns (n := 7) hB hCm
    (s := ![1, -1, -1, -1, -1, 1, 1, 1]) (s' := ![1, 1, 1, 1, -1, -1, -1, -1])
    ⟨by unfold IsSign; decide, by decide, by decide⟩
    ⟨by unfold IsSign; decide, by decide, by decide⟩
    ⟨by unfold IsSign; decide, by decide, by decide⟩ (by decide)
  exact ⟨hsc, hdiag, hct, hKl, hd3, hds, orth_noOffenderA hB hord hdisj hEKcard hCm htr⟩

end CFSG.StandardType.FrameRoute.FS81

end
