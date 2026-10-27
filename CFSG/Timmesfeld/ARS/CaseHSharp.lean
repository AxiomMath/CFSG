module

public import CFSG.Timmesfeld.ARS.CaseHNorm
public import CFSG.Timmesfeld.ARS.CaseHTorus

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement
open CFSG.LieType.Universal CFSG.Timmesfeld.RankOne Matrix NaturalModule FrameSL3 Sec8Field

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

namespace CaseH

variable {A A₀ P P' : Subgroup G}

namespace Setup

variable (S : Setup R A A₀ P P')

theorem proj_conj_U3 {x : G} (hx : x ∈ shortRoot R A A₀ P') (g : ↥(M R A))
    (hg : x * g * x⁻¹ ∈ M R A) :
    ((S.proj ⟨x * g * x⁻¹, hg⟩).2.2.1 : G) =
      (S.proj ⟨⁅x, ((S.proj g).1 : G)⁆, (commutator_mem_H S hx (S.proj g).1.2).1⟩).2.2.1 *
        (S.proj ⟨⁅x, ((S.proj g).2.1 : G)⁆,
          (S.facts.2.1 (Subgroup.commutator_mem_commutator hx (S.proj g).2.1.2)).1⟩).2.2.1 *
        (S.proj g).2.2.1 := by
  have hxN : x ∈ Subgroup.normalizer (A : Set G) :=
    conjSub_eq_self_iff.1 (conjSub_left_of_mem_shortRoot hx)
  obtain ⟨-, hUU, -, -, -, -⟩ := S.facts
  obtain ⟨hU13, hU1P', -⟩ :=
    positive_relations S.hyp S.hH S.hT S.hA S.h3 S.hA₀ S.hP S.hP' S.hPP'
  rw [S.proj_conj hxN g]
  simp only [Prod.snd_mul, Prod.fst_mul, Subgroup.coe_mul]
  set p := (S.proj g).1
  set u := (S.proj g).2.1
  set u' := (S.proj g).2.2.1
  set p' := (S.proj g).2.2.2
  have h1 : ((S.proj ⟨x * p * x⁻¹, conj_mem_M_of_mem_normalizer S.hyp.root hxN
      (S.P_le_M p.2)⟩).2.2.1 : G) =
      (S.proj ⟨⁅x, (p : G)⁆, (commutator_mem_H S hx p.2).1⟩).2.2.1 := by
    have e : (⟨x * p * x⁻¹, conj_mem_M_of_mem_normalizer S.hyp.root hxN (S.P_le_M p.2)⟩ :
        ↥(M R A)) = ⟨⁅x, (p : G)⁆, (commutator_mem_H S hx p.2).1⟩ * ⟨p, S.P_le_M p.2⟩ :=
      Subtype.ext (by simp only [Subgroup.coe_mul, commutatorElement_def]; group)
    rw [e, map_mul, S.proj_P p.2]
    simp
  have h2 : ((S.proj ⟨x * u * x⁻¹, conj_mem_M_of_mem_normalizer S.hyp.root hxN
      (U5_le_M u.2)⟩).2.2.1 : G) =
      (S.proj ⟨⁅x, (u : G)⁆, (hUU (Subgroup.commutator_mem_commutator hx u.2)).1⟩).2.2.1 := by
    have e : (⟨x * u * x⁻¹, conj_mem_M_of_mem_normalizer S.hyp.root hxN (U5_le_M u.2)⟩ :
        ↥(M R A)) = ⟨⁅x, (u : G)⁆, (hUU (Subgroup.commutator_mem_commutator hx u.2)).1⟩ *
          ⟨u, U5_le_M u.2⟩ :=
      Subtype.ext (by simp only [Subgroup.coe_mul, commutatorElement_def]; group)
    rw [e, map_mul, S.proj_U5 u.2]
    simp
  have h3 : ((S.proj ⟨x * u' * x⁻¹, conj_mem_M_of_mem_normalizer S.hyp.root hxN
      (U3_le_M u'.2)⟩).2.2.1 : G) = u' := by
    have hc : ⁅x, (u' : G)⁆ ∈ P' := hU13 (Subgroup.commutator_mem_commutator hx u'.2)
    have e : (⟨x * u' * x⁻¹, conj_mem_M_of_mem_normalizer S.hyp.root hxN (U3_le_M u'.2)⟩ :
        ↥(M R A)) = ⟨⁅x, (u' : G)⁆, S.P'_le_M hc⟩ * ⟨u', U3_le_M u'.2⟩ :=
      Subtype.ext (by simp only [Subgroup.coe_mul, commutatorElement_def]; group)
    rw [e, map_mul, S.proj_U3 u'.2, S.proj_P' hc]
    simp
  have h4 : ((S.proj ⟨x * p' * x⁻¹, conj_mem_M_of_mem_normalizer S.hyp.root hxN
      (S.P'_le_M p'.2)⟩).2.2.1 : G) = 1 := by
    have e : (⟨x * p' * x⁻¹, conj_mem_M_of_mem_normalizer S.hyp.root hxN (S.P'_le_M p'.2)⟩ :
        ↥(M R A)) = ⟨p', S.P'_le_M p'.2⟩ :=
      Subtype.ext (by simp only; rw [(hU1P' x hx _ p'.2).eq, mul_inv_cancel_right])
    rw [e, S.proj_P' p'.2]
    rfl
  rw [h1, h2, h3, h4, mul_one]

end Setup

namespace Coords

variable {S : Setup R A A₀ P P'} {F E : Type} [Field F] [Field E] (c : Coords S F E)

section Weyl

variable [CharP E 2]

theorem x3_injective : Function.Injective c.x3 := fun s s' h => c.x5_injective (by
  rw [← c.m_conj_x3, h, c.m_conj_x3])

theorem x3_add (s s' : E) : c.x3 (s + s') = c.x3 s * c.x3 s' := by
  simp only [x3, c.x5_add]
  group

theorem x3_zero : c.x3 0 = 1 := by
  rw [x3, c.x5_zero, mul_one, mul_inv_cancel]

theorem sharp_zero : c.sharp 0 = 0 := by
  apply c.x3_injective
  rw [c.x3_sharp, c.x3_zero]
  change ((S.proj ⟨_, c.comm1_mem 0⟩).2.2.1 : G) = 1
  have : (⟨_, c.comm1_mem 0⟩ : ↥(M R A)) = 1 :=
    Subtype.ext (by simp only [c.x1_zero, commutatorElement_one_left]; rfl)
  rw [this, map_one]
  rfl

variable [Finite F] [CharP F 2] (e : F →+* E) (he : ∀ s u, c.c5 s u = c.c5 (e u * s) 1)
  {τ : F} (hτ0 : τ ≠ 0) (hτ : ∀ u, c.m * c.x6 u * c.m⁻¹ = c.x2 (τ * u))
include he hτ0 hτ

theorem sharp_eq' {s : E} (hs : s ≠ 0) : c.sharp s = e (c.nu (Units.mk0 s hs)⁻¹) * s⁻¹ := by
  rw [c.sharp_eq e he hτ0 hτ hs, c.N_eq hτ hs, ← mul_assoc, inv_mul_cancel₀ hτ0, one_mul]

theorem sharp_ne_zero {s : E} (hs : s ≠ 0) : c.sharp s ≠ 0 := by
  rw [c.sharp_eq' e he hτ0 hτ hs]
  exact mul_ne_zero ((map_ne_zero e).2 (c.nu_ne_zero _)) (inv_ne_zero hs)

theorem sharp_mul (s s' : E) : c.sharp (s * s') = c.sharp s * c.sharp s' := by
  by_cases hs : s = 0
  · rw [hs, zero_mul, c.sharp_zero, zero_mul]
  by_cases hs' : s' = 0
  · rw [hs', mul_zero, c.sharp_zero, mul_zero]
  rw [c.sharp_eq' e he hτ0 hτ hs, c.sharp_eq' e he hτ0 hτ hs',
    c.sharp_eq' e he hτ0 hτ (mul_ne_zero hs hs'),
    show Units.mk0 (s * s') (mul_ne_zero hs hs') = Units.mk0 s hs * Units.mk0 s' hs' by
      ext; simp, mul_inv, c.nu_mul, map_mul, mul_inv]
  ring

theorem exists_sharp_pow [Finite E] :
    ∃ d : ℕ, d < Nat.card Eˣ ∧ ∀ s : E, s ≠ 0 → c.sharp s = s ^ d := by
  have h11 : c.sharp 1 = 1 := by
    have h := c.sharp_mul e he hτ0 hτ 1 1
    rw [mul_one] at h
    have hne := c.sharp_ne_zero e he hτ0 hτ (one_ne_zero (α := E))
    exact mul_left_cancel₀ hne (h.symm.trans (mul_one _).symm)
  let σ : Eˣ →* Eˣ :=
    { toFun := fun μ => Units.mk0 (c.sharp μ) (c.sharp_ne_zero e he hτ0 hτ μ.ne_zero)
      map_one' := by
        ext
        simp only [Units.val_mk0, Units.val_one]
        exact h11
      map_mul' := fun μ μ' => by
        ext
        simp only [Units.val_mk0, Units.val_mul]
        exact c.sharp_mul e he hτ0 hτ μ μ' }
  obtain ⟨z, hz⟩ := σ.map_cyclic
  have hpos : 0 < Nat.card Eˣ := Nat.card_pos
  have hn0 : (Nat.card Eˣ : ℤ) ≠ 0 := by exact_mod_cast hpos.ne'
  set d := (z % (Nat.card Eˣ : ℤ)).toNat with hd
  have hdz : (d : ℤ) = z % (Nat.card Eˣ : ℤ) := Int.toNat_of_nonneg (Int.emod_nonneg z hn0)
  have key : ∀ μ : Eˣ, μ ^ z = μ ^ d := by
    intro μ
    have hn : μ ^ (Nat.card Eˣ) = 1 := pow_card_eq_one'
    rw [← zpow_natCast μ d, hdz]
    conv_lhs => rw [← Int.emod_add_mul_ediv z (Nat.card Eˣ : ℤ)]
    rw [_root_.zpow_add, _root_.zpow_mul, zpow_natCast, hn, _root_.one_zpow, mul_one]
  refine ⟨d, ?_, fun s hs => ?_⟩
  · have h1 := Int.emod_lt_of_pos z (by exact_mod_cast hpos : (0 : ℤ) < Nat.card Eˣ)
    omega
  · have h := congrArg Units.val (hz (Units.mk0 s hs))
    simp only [σ, MonoidHom.coe_mk, OneHom.coe_mk, Units.val_mk0] at h
    rw [h, key, Units.val_pow_eq_pow_val, Units.val_mk0]

theorem sharp_mul_self_eq {s : E} (hs : s ≠ 0) :
    c.sharp s * s = e (c.nu (Units.mk0 s hs)⁻¹) := by
  rw [c.sharp_eq' e he hτ0 hτ hs, mul_assoc, inv_mul_cancel₀ hs, mul_one]

theorem sharp_e (l : Fˣ) : c.sharp (e l) = e l * e l := by
  have hl : e l ≠ 0 := (map_ne_zero e).2 l.ne_zero
  have h1 := c.N_eq hτ hl
  have h2 := c.N_smul e he l 1
  rw [mul_one, c.N_one hτ] at h2
  rw [h2] at h1
  have hν : c.nu (Units.mk0 (e l) hl)⁻¹ = (l : F) ^ 3 :=
    (mul_left_cancel₀ hτ0 ((mul_comm τ _).trans h1)).symm
  rw [c.sharp_eq' e he hτ0 hτ hl, hν, map_pow]
  field_simp

omit [Finite F] [CharP F 2] he hτ0 hτ in
theorem exists_polar (s₀ : E) :
    ∃ f : E → E, (∀ s s', f (s + s') = f s + f s') ∧
      ∀ s, c.sharp (s₀ + s) = c.sharp s₀ + c.sharp s + f s := by
  have hR := S.hyp.root
  have hx := c.x1_mem s₀
  obtain ⟨-, hUU, -, -, -, -⟩ := S.facts
  have hPR : P ∈ R := S.hP.2.1
  obtain ⟨-, -, -, -, -, -, ⟨hsAQ', -⟩, -, hQ'Ω, -⟩ :=
    apartment S.hyp S.hH S.hA S.hA₀ S.hP S.hP' S.hPP'
  have hAs : A ∈ lambdaStar R P ⁅A₀, P'⁆ := ⟨mem_lambdaSet_comm S.hA S.hP.1, S.hA, hsAQ'.symm⟩
  have hU3c := (shortRoot_moufang_of S.hyp S.hH S.hT hPR hQ'Ω hAs).1
  have hmemK : ∀ y ∈ shortRoot R P' ⁅A₀, P⁆ A, ⁅c.x1 s₀, y⁆ ∈ M R A := fun y hy =>
    (hUU (Subgroup.commutator_mem_commutator hx hy)).1
  let g : E → G := fun s => (S.proj ⟨_, hmemK _ (c.x5_mem s)⟩).2.2.1
  have hg_mem : ∀ s, g s ∈ shortRoot R P ⁅A₀, P'⁆ A := fun s => Subtype.prop _
  choose f hf using fun s => c.x3_surjective (hg_mem s)
  have hgadd : ∀ s s', g (s + s') = g s * g s' := by
    intro s s'
    have e1 : (⟨_, hmemK _ (c.x5_mem (s + s'))⟩ : ↥(M R A)) =
        ⟨_, hmemK _ (c.x5_mem s)⟩ * (⟨c.x5 s, Setup.U5_le_M (c.x5_mem s)⟩ *
          ⟨_, hmemK _ (c.x5_mem s')⟩ * ⟨c.x5 s, Setup.U5_le_M (c.x5_mem s)⟩⁻¹) := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, c.x5_add, commutatorElement_def]
      group
    simp only [g]
    rw [e1, map_mul, map_mul, map_mul, map_inv, S.proj_U5 (c.x5_mem s)]
    simp [Prod.fst_mul, Prod.snd_mul]
  refine ⟨f, fun s s' => c.x3_injective (by rw [c.x3_add, hf, hf, hf, hgadd]), fun s => ?_⟩
  apply c.x3_injective
  rw [c.x3_add, c.x3_add, hf, c.x3_sharp, c.x3_sharp, c.x3_sharp]
  have hgH := commutator_mem_H S (c.x1_mem s) (c.x6_mem 1)
  have hcM : c.x1 s₀ * ⁅c.x1 s, c.x6 1⁆ * (c.x1 s₀)⁻¹ ∈ M R A :=
    conj_mem_M_of_mem_normalizer hR (conjSub_eq_self_iff.1 (conjSub_left_of_mem_shortRoot hx))
      hgH.1
  have e2 : (⟨_, c.comm1_mem (s₀ + s)⟩ : ↥(M R A)) =
      ⟨_, hcM⟩ * ⟨_, c.comm1_mem s₀⟩ := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, c.x1_add, commutatorElement_def]
    group
  change ((S.proj ⟨_, c.comm1_mem (s₀ + s)⟩).2.2.1 : G) = _
  rw [e2, map_mul, Prod.snd_mul, Prod.snd_mul, Prod.fst_mul, Subgroup.coe_mul]
  have h3 := S.proj_conj_U3 hx ⟨_, hgH.1⟩ hcM
  rw [h3]
  obtain ⟨hp1, hp5⟩ := S.proj_H hgH
  have key : ∀ (y y' : G) (hy : ⁅c.x1 s₀, y⁆ ∈ M R A) (hy' : ⁅c.x1 s₀, y'⁆ ∈ M R A), y = y' →
      ((S.proj ⟨_, hy⟩).2.2.1 : G) = (S.proj ⟨_, hy'⟩).2.2.1 := by
    rintro y y' hy hy' rfl
    rfl
  have h1M : ⁅c.x1 s₀, (1 : G)⁆ ∈ M R A := by
    rw [commutatorElement_one_right]
    exact Subgroup.one_mem _
  rw [key (S.proj ⟨_, hgH.1⟩).1 1 _ h1M (congrArg Subtype.val hp1),
    key (S.proj ⟨_, hgH.1⟩).2.1 (c.x5 s) _ (hmemK _ (c.x5_mem s)) hp5]
  have h1 : (⟨⁅c.x1 s₀, (1 : G)⁆, h1M⟩ : ↥(M R A)) = 1 :=
    Subtype.ext (by simp only [commutatorElement_one_right]; rfl)
  rw [h1, map_one]
  change 1 * g s * c.n3 s * c.n3 s₀ = c.n3 s₀ * c.n3 s * g s
  have m1 := hg_mem s
  have m2 : c.n3 s ∈ shortRoot R P ⁅A₀, P'⁆ A := Subtype.prop _
  have m3 : c.n3 s₀ ∈ shortRoot R P ⁅A₀, P'⁆ A := Subtype.prop _
  rw [one_mul, (hU3c _ (Subgroup.mul_mem _ m1 m2) _ m3).eq, (hU3c _ m1 _ m2).eq, mul_assoc]

end Weyl

end Coords

end CaseH

end CFSG.Timmesfeld.ARS
