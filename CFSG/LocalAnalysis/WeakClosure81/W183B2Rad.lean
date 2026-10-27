module

public import CFSG.LocalAnalysis.WeakClosure81.W183B2One
import CFSG.LocalAnalysis.WeakClosure81.W183Abs1
import CFSG.SignalizerFunctorTheorem.Quadratic.Invariance

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Quasithin CFSG.Open Subgroup

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  {Y T L Q₁ Q₂ : Subgroup (LGL 2 V)} {Γ : Set (Subgroup (LGL 2 V))}
  {VA : Subgroup (LGL 2 V) → Submodule (ZMod 2) V} {𝒢 : Set (Subgroup (LGL 2 V))}
  {Zs : Submodule (ZMod 2) V} {m i₀ : ℕ} {δ : Subgroup (LGL 2 V) → ℕ}

structure Br2RadY (T L Q₁ Q₂ : Subgroup (LGL 2 V)) : Prop where
  le₁ : Q₁ ≤ T ⊓ L
  le₂ : Q₂ ≤ T ⊓ L
  gen_S : T ⊓ L ≤ Q₁ ⊔ Q₂
  norm₁ : T ⊓ L ≤ Subgroup.normalizer (Q₁ : Set (LGL 2 V))
  norm₂ : T ⊓ L ≤ Subgroup.normalizer (Q₂ : Set (LGL 2 V))
  elem₁ : IsElemAbelian 2 Q₁
  elem₂ : IsElemAbelian 2 Q₂
  central : ∀ x ∈ Q₁ ⊓ Q₂, ∀ s ∈ T ⊓ L, x * s = s * x
  cover : ∀ E : Subgroup (LGL 2 V), E ≤ T ⊓ L → IsElemAbelian 2 E → E ≤ Q₁ ∨ E ≤ Q₂
  rank₁ : ∀ E : Subgroup (LGL 2 V), E ≤ Q₁ → mOf E (E ⊓ Q₂) ≤ 2
  rank₂ : ∀ E : Subgroup (LGL 2 V), E ≤ Q₂ → mOf E (E ⊓ Q₁) ≤ 2
  gen_L : (⨆ p ∈ L ⊓ Subgroup.normalizer (Q₁ : Set (LGL 2 V)), cj p (T ⊓ L)) ⊔
    (⨆ p ∈ L ⊓ Subgroup.normalizer (Q₂ : Set (LGL 2 V)), cj p (T ⊓ L)) = L
  gen₁ : ∀ E : Subgroup (LGL 2 V), E ≤ Q₁ → 8 ≤ Nat.card E → ¬ E ≤ Q₁ ⊓ Q₂ →
    (⨆ p ∈ L ⊓ Subgroup.normalizer (Q₁ : Set (LGL 2 V)), cj p E) = Q₁
  gen₂ : ∀ E : Subgroup (LGL 2 V), E ≤ Q₂ → 8 ≤ Nat.card E → ¬ E ≤ Q₁ ⊓ Q₂ →
    (⨆ p ∈ L ⊓ Subgroup.normalizer (Q₂ : Set (LGL 2 V)), cj p E) = Q₂
  swap : ∃ τ ∈ T, cj τ Q₁ = Q₂ ∧ cj τ Q₂ = Q₁

theorem Br2RadY.symm {T L Q₁ Q₂ : Subgroup (LGL 2 V)} (h : Br2RadY T L Q₁ Q₂) :
    Br2RadY T L Q₂ Q₁ := by
  refine
    { le₁ := h.le₂
      le₂ := h.le₁
      gen_S := by rw [sup_comm]; exact h.gen_S
      norm₁ := h.norm₂
      norm₂ := h.norm₁
      elem₁ := h.elem₂
      elem₂ := h.elem₁
      central := ?_
      cover := ?_
      rank₁ := h.rank₂
      rank₂ := h.rank₁
      gen_L := by rw [sup_comm]; exact h.gen_L
      gen₁ := fun E hE hcard hnot =>
        h.gen₂ E hE hcard (fun hh => hnot (by rwa [inf_comm] at hh))
      gen₂ := fun E hE hcard hnot =>
        h.gen₁ E hE hcard (fun hh => hnot (by rwa [inf_comm] at hh))
      swap := ?_ }
  · intro x hx s hs
    rw [inf_comm] at hx
    exact h.central x hx s hs
  · intro E hE hEel
    exact (h.cover E hE hEel).elim Or.inr Or.inl
  · obtain ⟨τ, hτ, hτ₁, hτ₂⟩ := h.swap
    exact ⟨τ, hτ, hτ₂, hτ₁⟩

private def w183b2_stabPt (U : Submodule (ZMod 2) V) : Subgroup (LGL 2 V) where
  carrier := {g | ∀ u ∈ U, g u = u}
  one_mem' := fun _ _ => rfl
  mul_mem' := fun {a b} ha hb u hu => by
    show a (b u) = u
    rw [hb u hu, ha u hu]
  inv_mem' := fun {a} ha u hu => a.symm_apply_eq.mpr (ha u hu).symm

private theorem w183b2_mem_stabPt {U : Submodule (ZMod 2) V} {g : LGL 2 V} :
    g ∈ w183b2_stabPt U ↔ ∀ u ∈ U, g u = u := Iff.rfl

private theorem w183b2_le_stabPt_iff {G' : Subgroup (LGL 2 V)}
    {U : Submodule (ZMod 2) V} :
    G' ≤ w183b2_stabPt U ↔ U ≤ fixSub G' := by
  constructor
  · intro h u hu
    rw [mem_fixSub]
    intro g hg
    exact (w183b2_mem_stabPt.mp (h hg)) u hu
  · intro h g hg
    rw [w183b2_mem_stabPt]
    intro u hu
    exact (h hu) g hg

private theorem w183b2_index_eq_two_pow {A B : Subgroup (LGL 2 V)}
    (hA : IsElemAbelian 2 A) (hB : B ≤ A) :
    ∃ k : ℕ, (B.subgroupOf A).index = 2 ^ k := by
  haveI : IsMulCommutative ↥A := hA.1
  have hpg : IsPGroup 2 ↥A := hA.isPGroup
  have hq : IsPGroup 2 (↥A ⧸ B.subgroupOf A) := hpg.to_quotient (B.subgroupOf A)
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hq
  exact ⟨k, by rw [Subgroup.index_eq_card]; exact hk⟩

private theorem w183b2_mOf_add_of_elemAbelian {A B C : Subgroup (LGL 2 V)}
    (hA : IsElemAbelian 2 A) (hBA : B ≤ A) (hCB : C ≤ B) :
    mOf A C = mOf A B + mOf B C := by
  obtain ⟨j, hj⟩ := w183b2_index_eq_two_pow hA hBA
  have hBel : IsElemAbelian 2 B := hA.mono hBA
  obtain ⟨l, hl⟩ := w183b2_index_eq_two_pow hBel hCB
  have hmul : (C.subgroupOf A).index =
      (C.subgroupOf B).index * (B.subgroupOf A).index := by
    show C.relIndex A = C.relIndex B * B.relIndex A
    exact (Subgroup.relIndex_mul_relIndex (H := C) (K := B) (L := A) hCB hBA).symm
  have hAB : mOf A B = j := by
    rw [mOf, hj, Nat.log_pow (by norm_num)]
  have hBC : mOf B C = l := by
    rw [mOf, hl, Nat.log_pow (by norm_num)]
  have hAC : mOf A C = l + j := by
    rw [mOf, hmul, hl, hj, ← pow_add, Nat.log_pow (by norm_num)]
  omega

private theorem w183b2_mem_VA_of_mem_commSpace
    (hc : Br1Base Y Γ VA T 𝒢 Zs m i₀ δ) (hR : Br2RadY T L Q₁ Q₂)
    {A : Subgroup (LGL 2 V)} (hA : A ∈ Γ) (hAQ : A ≤ Q₁)
    {v : V} (hv : v ∈ commSpace A (fixSub Q₂)) : v ∈ VA A := by
  have hB0 : A ⊓ Q₂ ≤ A := inf_le_left
  have hrank : mOf A (A ⊓ Q₂) ≤ 2 := hR.rank₁ A hAQ
  have hdelta : δ A ≤ i₀ := hc.delta_le A hA
  have hmi : i₀ + 3 ≤ m := hc.hmi
  have hlt : mOf A (A ⊓ Q₂) + δ A < m := by omega
  have hcomm : commSpace A (fixSub (A ⊓ Q₂)) ≤ VA A :=
    hc.comm_le A hA (A ⊓ Q₂) hB0 hlt
  have hle : fixSub Q₂ ≤ fixSub (A ⊓ Q₂) :=
    fixSub_anti (A ⊓ Q₂) Q₂ inf_le_right
  exact hcomm (commSpace_mono le_rfl hle hv)

private theorem w183b2_mem_fixSub_of_mem_commSpace
    (hc : Br1Base Y Γ VA T 𝒢 Zs m i₀ δ) (hR : Br2RadY T L Q₁ Q₂)
    {A : Subgroup (LGL 2 V)} (hAQ : A ≤ Q₁)
    {v : V} (hv : v ∈ commSpace A (fixSub Q₂)) : v ∈ fixSub Q₂ := by
  have hA_le : A ≤ T ⊓ L := hAQ.trans hR.le₁
  have hnorm : A ≤ Subgroup.normalizer (Q₂ : Set (LGL 2 V)) :=
    hA_le.trans hR.norm₂
  have hinv : Invariant A (fixSub Q₂) := by
    intro a ha w hw
    exact map_mem_fixSub_of_mem_normalizer Q₂ (hnorm ha) hw
  exact commSpace_le_of_invariant hinv hv

theorem w183b2_rad_step1 (hc : Br1Base Y Γ VA T 𝒢 Zs m i₀ δ) (hL : SimpleCore Y L)
    (hR : Br2RadY T L Q₁ Q₂) (hrk : ∀ D ∈ Γ, 3 ≤ mRank D) {D₀ : Subgroup (LGL 2 V)}
    (hD₀ : D₀ ∈ Γ) (hD₀Q : D₀ ≤ Q₁) (hD₀n : ¬ D₀ ≤ Q₂) :
    ∃ A ∈ Γ, A ≤ Q₁ ∧ commSpace A (fixSub Q₂) ≠ ⊥ := by
  by_contra hno
  have hstep : ∀ A ∈ Γ, A ≤ Q₁ → commSpace A (fixSub Q₂) = ⊥ := by
    intro A hA hAQ
    by_contra hne
    exact hno ⟨A, hA, hAQ, hne⟩
  have hP₁D₀ : (⨆ p ∈ L ⊓ Subgroup.normalizer (Q₁ : Set (LGL 2 V)), cj p D₀) ≤
      w183b2_stabPt (fixSub Q₂) := by
    refine iSup_le fun p => iSup_le fun hp => ?_
    have hpY : p ∈ Y := hL.le hp.1
    have hpN : p ∈ Subgroup.normalizer (Q₁ : Set (LGL 2 V)) := hp.2
    have hcjΓ : cj p D₀ ∈ Γ := hc.h131.invariant D₀ hD₀ p hpY
    have hcjQ : cj p D₀ ≤ Q₁ := by
      have hpQ : cj p Q₁ = Q₁ :=
        (Subgroup.mem_normalizer_iff_map_conj_eq (H := Q₁) (g := p)).mp hpN
      calc cj p D₀ ≤ cj p Q₁ := cj_mono p hD₀Q
        _ = Q₁ := hpQ
    have hbot : commSpace (cj p D₀) (fixSub Q₂) = ⊥ := hstep (cj p D₀) hcjΓ hcjQ
    intro x hx
    rw [w183b2_mem_stabPt]
    intro u hu
    exact (commSpace_eq_bot_iff.mp hbot) x hx u hu
  have hnotSub : ¬ D₀ ≤ Q₁ ⊓ Q₂ := fun h => hD₀n (fun x hx => (h hx).2)
  have hcard8 : 8 ≤ Nat.card D₀ := by
    have hlog : 3 ≤ Nat.log 2 (Nat.card D₀) := hrk D₀ hD₀
    have hcardpos : Nat.card D₀ ≠ 0 := Nat.card_pos.ne'
    have hpow := Nat.pow_le_of_le_log hcardpos hlog
    simpa using hpow
  have hQ₁stab : Q₁ ≤ w183b2_stabPt (fixSub Q₂) := by
    rw [← hR.gen₁ D₀ hD₀Q hcard8 hnotSub]
    exact hP₁D₀
  have hQ₂stab : Q₂ ≤ w183b2_stabPt (fixSub Q₂) :=
    (w183b2_le_stabPt_iff).mpr le_rfl
  have hSstab : T ⊓ L ≤ w183b2_stabPt (fixSub Q₂) :=
    hR.gen_S.trans (sup_le hQ₁stab hQ₂stab)
  have hfixS : fixSub (T ⊓ L) = fixSub Q₂ := by
    apply le_antisymm
    · exact fixSub_anti Q₂ (T ⊓ L) hR.le₂
    · exact (w183b2_le_stabPt_iff).mp hSstab
  have hP₂S : (⨆ p ∈ L ⊓ Subgroup.normalizer (Q₂ : Set (LGL 2 V)),
      cj p (T ⊓ L)) ≤ w183b2_stabPt (fixSub Q₂) := by
    refine iSup_le fun p => iSup_le fun hp => ?_
    intro x hx
    rw [w183b2_mem_stabPt]
    intro w hw
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hx
    have hpN : p ∈ Subgroup.normalizer (Q₂ : Set (LGL 2 V)) := hp.2
    have hpinv : p⁻¹ w ∈ fixSub Q₂ :=
      map_mem_fixSub_of_mem_normalizer Q₂
        ((Subgroup.normalizer (Q₂ : Set (LGL 2 V))).inv_mem hpN) hw
    have hsfix : s (p⁻¹ w) = p⁻¹ w :=
      (w183b2_mem_stabPt.mp (hSstab hs)) (p⁻¹ w) hpinv
    show (p * s * p⁻¹) w = w
    calc (p * s * p⁻¹) w = p (s (p⁻¹ w)) := rfl
      _ = p (p⁻¹ w) := by rw [hsfix]
      _ = w := p.apply_symm_apply w
  obtain ⟨τ, hτT, hτQ₁, hτQ₂⟩ := hR.swap
  have hτY : τ ∈ Y := hc.sylow.le hτT
  have hcjS : cj τ (T ⊓ L) = T ⊓ L := by
    apply le_antisymm
    · intro x hx
      obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hx
      exact ⟨T.mul_mem (T.mul_mem hτT hs.1) (T.inv_mem hτT),
        hL.normal τ hτY s hs.2⟩
    · intro x hx
      refine Subgroup.mem_map.mpr ⟨τ⁻¹ * x * τ, ⟨?_, ?_⟩, ?_⟩
      · exact T.mul_mem (T.mul_mem (T.inv_mem hτT) hx.1) hτT
      · exact hL.normal τ⁻¹ (Y.inv_mem hτY) x hx.2
      · show τ * (τ⁻¹ * x * τ) * τ⁻¹ = x
        group
  have hfixQ1 : fixSub Q₁ = fixSub Q₂ := by
    calc fixSub Q₁ = fixSub (cj τ Q₂) := by rw [hτQ₂]
      _ = (fixSub Q₂).map (τ : V →ₗ[ZMod 2] V) := fixSub_cj Q₂ τ
      _ = (fixSub (T ⊓ L)).map (τ : V →ₗ[ZMod 2] V) := by rw [hfixS]
      _ = fixSub (cj τ (T ⊓ L)) := (fixSub_cj (T ⊓ L) τ).symm
      _ = fixSub (T ⊓ L) := by rw [hcjS]
      _ = fixSub Q₂ := hfixS
  have hP₁S : (⨆ p ∈ L ⊓ Subgroup.normalizer (Q₁ : Set (LGL 2 V)),
      cj p (T ⊓ L)) ≤ w183b2_stabPt (fixSub Q₂) := by
    refine iSup_le fun p => iSup_le fun hp => ?_
    intro x hx
    rw [w183b2_mem_stabPt]
    intro w hw
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hx
    have hpN : p ∈ Subgroup.normalizer (Q₁ : Set (LGL 2 V)) := hp.2
    have hw1 : w ∈ fixSub Q₁ := by rw [hfixQ1]; exact hw
    have hpinv : p⁻¹ w ∈ fixSub Q₁ :=
      map_mem_fixSub_of_mem_normalizer Q₁
        ((Subgroup.normalizer (Q₁ : Set (LGL 2 V))).inv_mem hpN) hw1
    have hpinv₂ : p⁻¹ w ∈ fixSub Q₂ := by rw [← hfixQ1]; exact hpinv
    have hsfix : s (p⁻¹ w) = p⁻¹ w :=
      (w183b2_mem_stabPt.mp (hSstab hs)) (p⁻¹ w) hpinv₂
    show (p * s * p⁻¹) w = w
    calc (p * s * p⁻¹) w = p (s (p⁻¹ w)) := rfl
      _ = p (p⁻¹ w) := by rw [hsfix]
      _ = w := p.apply_symm_apply w
  have hLstab : L ≤ w183b2_stabPt (fixSub Q₂) := by
    rw [← hR.gen_L]
    exact sup_le hP₁S hP₂S
  have hfixL : fixSub Q₂ ≤ fixSub L := (w183b2_le_stabPt_iff).mp hLstab
  have hZsS : Zs ≤ fixSub (T ⊓ L) := by
    rw [hc.zs_eq]
    exact fixSub_anti (T ⊓ L) T inf_le_left
  have hZsF : Zs ≤ fixSub Q₂ := by
    rw [← hfixS]
    exact hZsS
  have hLfix : ∀ y ∈ Y, conjSub y Zs ≤ fixSub L := by
    intro y hy z hz
    rw [G11.conjSub, Submodule.mem_map] at hz
    obtain ⟨z0, hz0, rfl⟩ := hz
    rw [mem_fixSub]
    intro l hl
    have hly : y⁻¹ * l * y ∈ L := hL.normal y⁻¹ (Y.inv_mem hy) l hl
    have hzfix : (y⁻¹ * l * y) z0 = z0 :=
      (hfixL (hZsF hz0)) (y⁻¹ * l * y) hly
    calc l (y z0) = (l * y) z0 := rfl
      _ = (y * (y⁻¹ * l * y)) z0 := by
        rw [show l * y = y * (y⁻¹ * l * y) by group]
      _ = y ((y⁻¹ * l * y) z0) := rfl
      _ = y z0 := by rw [hzfix]
  have htop : (⊤ : Submodule (ZMod 2) V) ≤ fixSub L := by
    rw [← hc.zs_gen]
    exact iSup_le fun y => iSup_le fun hy => hLfix y hy
  have hLbot : L = ⊥ := by
    have hfixLtop : fixSub L = ⊤ := top_le_iff.mp htop
    exact (fixSub_eq_top_iff L).mp hfixLtop
  obtain ⟨a, ha, b, hb, hab⟩ := hL.nonab
  rw [hLbot] at ha hb
  have ha1 : a = 1 := Subgroup.mem_bot.mp ha
  have hb1 : b = 1 := Subgroup.mem_bot.mp hb
  exact hab (by rw [ha1, hb1])

theorem w183b2_rad_step2 (hc : Br1Base Y Γ VA T 𝒢 Zs m i₀ δ) (hR : Br2RadY T L Q₁ Q₂)
    (hgen : ∀ B ∈ 𝒢, B ≤ Q₁ ∨ B ≤ Q₂) {A : Subgroup (LGL 2 V)} (hA : A ∈ Γ) (hAQ : A ≤ Q₁)
    {v : V} (hv : v ∈ commSpace A (fixSub Q₂)) (hv0 : v ≠ 0) :
    ∀ B ∈ 𝒢, ∀ b ∈ B, b v = v := by
  have hvA : v ∈ VA A := w183b2_mem_VA_of_mem_commSpace hc hR hA hAQ hv
  have hvF : v ∈ fixSub Q₂ := w183b2_mem_fixSub_of_mem_commSpace hc hR hAQ hv
  intro B hB b hb
  have hBT : B ≤ T := (hc.gens B hB).1
  rcases hgen B hB with hBQ₁ | hBQ₂
  · have hB_el : IsElemAbelian 2 B := hR.elem₁.mono hBQ₁
    have hcommute : ∀ a ∈ A, ∀ x ∈ B, a * x = x * a := by
      intro a ha x hx
      exact hR.elem₁.comm (hAQ ha) (hBQ₁ hx)
    have hconjA : cj b A = A := by
      apply le_antisymm
      · intro y hy
        obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hy
        have hc1 := hcommute a ha b hb
        have e : b * a * b⁻¹ = a := by rw [← hc1]; group
        show b * a * b⁻¹ ∈ A
        rwa [e]
      · intro a ha
        refine Subgroup.mem_map.mpr ⟨a, ha, ?_⟩
        have hc1 := hcommute a ha b hb
        show b * a * b⁻¹ = a
        rw [← hc1]; group
    have hbnorm : b ∈ Subgroup.normalizer (A : Set (LGL 2 V)) :=
      (Subgroup.mem_normalizer_iff_map_conj_eq (H := A) (g := b)).mpr hconjA
    have hbY : b ∈ Y := hc.sylow.le (hBT hb)
    have hbstab : b ∈ stabilizerOf Y (VA A) := by
      rw [← hc.h131.normalizer_eq A hA]
      exact ⟨hbY, hbnorm⟩
    have hbvA : b v ∈ VA A := by
      have := apply_mem_conjSub (g := b) hvA
      rwa [hbstab.2] at this
    have hdiffA : b v - v ∈ VA A := (VA A).sub_mem hbvA hvA
    obtain ⟨D', hD', hBD', hleD'⟩ := (hc.gens B hB).2
    have hD'el : IsElemAbelian 2 D' := hc.h131.isElemAb D' hD'
    have hB1D' : B ⊓ Q₂ ≤ D' := inf_le_left.trans hBD'
    have hmOf : mOf D' (B ⊓ Q₂) = mOf D' B + mOf B (B ⊓ Q₂) :=
      w183b2_mOf_add_of_elemAbelian hD'el hBD' inf_le_left
    have hrankB : mOf B (B ⊓ Q₂) ≤ 2 := hR.rank₁ B hBQ₁
    have hmi : i₀ + 3 ≤ m := hc.hmi
    have hlt : mOf D' (B ⊓ Q₂) + δ D' < m := by omega
    have hcommD' : commSpace D' (fixSub (B ⊓ Q₂)) ≤ VA D' :=
      hc.comm_le D' hD' (B ⊓ Q₂) hB1D' hlt
    have hvB1 : v ∈ fixSub (B ⊓ Q₂) :=
      fixSub_anti (B ⊓ Q₂) Q₂ inf_le_right hvF
    have hdiffD' : b v - v ∈ VA D' :=
      hcommD' (sub_mem_commSpace (hBD' hb) hvB1)
    by_cases hDA : D' = A
    · have hvD' : v ∈ VA D' := by rw [hDA]; exact hvA
      exact (hc.vfix D' hD' hvD') b (hBD' hb)
    · have hdisj : VA A ⊓ VA D' = ⊥ :=
        hc.h131.disjoint A hA D' hD' (fun h => hDA h.symm)
      have hboth : b v - v ∈ VA A ⊓ VA D' := ⟨hdiffA, hdiffD'⟩
      rw [hdisj, Submodule.mem_bot] at hboth
      exact sub_eq_zero.mp hboth
  · exact hvF b (hBQ₂ hb)

private theorem w183b2_false_of_le (hc : Br1Base Y Γ VA T 𝒢 Zs m i₀ δ) (hL : SimpleCore Y L)
    (hR : Br2RadY T L Q₁ Q₂) (hgen : ∀ B ∈ 𝒢, B ≤ Q₁ ∨ B ≤ Q₂)
    (hrk : ∀ D ∈ Γ, 3 ≤ mRank D) {D₀ : Subgroup (LGL 2 V)} (hD₀ : D₀ ∈ Γ)
    (hD₀S : D₀ ≤ T ⊓ L) (hD₀Q : D₀ ≤ Q₁) (hD₀n : ¬ D₀ ≤ Q₂) : False := by
  obtain ⟨A, hA, hAQ, hAv⟩ :=
    w183b2_rad_step1 hc hL hR hrk hD₀ hD₀Q hD₀n
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hAv
  have hvA : v ∈ VA A := w183b2_mem_VA_of_mem_commSpace hc hR hA hAQ hv
  have hfix : ∀ B ∈ 𝒢, ∀ b ∈ B, b v = v :=
    w183b2_rad_step2 hc hR hgen hA hAQ hv hv0
  have hgenNorm : ∀ B ∈ 𝒢, B ≤ Subgroup.normalizer (A : Set (LGL 2 V)) := by
    intro B hB b hb
    have hBT : b ∈ T := (hc.gens B hB).1 hb
    have hbY : b ∈ Y := hc.sylow.le hBT
    exact hc.h131.stabilizer_le_normalizer hA hvA hv0 hbY (hfix B hB b hb)
  have hAT : A ≤ T := hAQ.trans (hR.le₁.trans inf_le_left)
  have hTne : T ≠ Y := hL.ne_of_isSylowIn hc.sylow
  have hTnorm : T ≤ Subgroup.normalizer (A : Set (LGL 2 V)) :=
    hc.weakClosure A hA hAT hgenNorm T hc.sylow.le le_rfl hTne
  obtain ⟨τ, hτT, hτQ₁, hτQ₂⟩ := hR.swap
  have hτnorm : τ ∈ Subgroup.normalizer (A : Set (LGL 2 V)) := hTnorm hτT
  have hcjA : cj τ A = A :=
    (Subgroup.mem_normalizer_iff_map_conj_eq (H := A) (g := τ)).mp hτnorm
  have hAleQ₂ : A ≤ Q₂ := by
    have h1 : cj τ A ≤ cj τ Q₁ := cj_mono τ hAQ
    rw [hτQ₁, hcjA] at h1
    exact h1
  have hzero : commSpace A (fixSub Q₂) = ⊥ := by
    rw [commSpace_eq_bot_iff]
    intro a ha w hw
    exact hw a (hAleQ₂ ha)
  exact hAv hzero

theorem br2_false_of_two_radicals (hc : Br1Base Y Γ VA T 𝒢 Zs m i₀ δ) (hL : SimpleCore Y L)
    (hR : Br2RadY T L Q₁ Q₂) (hgen : ∀ B ∈ 𝒢, B ≤ Q₁ ∨ B ≤ Q₂)
    (hrk : ∀ D ∈ Γ, 3 ≤ mRank D) {D₀ : Subgroup (LGL 2 V)} (hD₀ : D₀ ∈ Γ)
    (hD₀S : D₀ ≤ T ⊓ L) (hD₀Z : ¬ D₀ ≤ Q₁ ⊓ Q₂) : False := by
  have hD₀el : IsElemAbelian 2 D₀ := hc.h131.isElemAb D₀ hD₀
  rcases hR.cover D₀ hD₀S hD₀el with hD₀Q₁ | hD₀Q₂
  · exact w183b2_false_of_le hc hL hR hgen hrk hD₀ hD₀S hD₀Q₁
      (fun h => hD₀Z (le_inf hD₀Q₁ h))
  · exact w183b2_false_of_le hc hL hR.symm
      (fun B hB => (hgen B hB).elim Or.inr Or.inl) hrk hD₀ hD₀S hD₀Q₂
      (fun h => hD₀Z (le_inf h hD₀Q₂))

end CFSG.LocalAnalysis.WeakClosure81

end
