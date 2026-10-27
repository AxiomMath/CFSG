module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13ThrEightXA
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13ThrXB
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13ThrW6

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.Quasithin CFSG.Open Subgroup
open scoped commutatorElement

variable {W : Type} [CommGroup W] [Finite W] {A : Subgroup (MulAut W)} {t : MulAut W}

private theorem w16g_odd_card_of_isElemAbelian {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {X : Subgroup (MulAut W)} (hX : IsElemAbelian p X) : Odd (Nat.card X) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hX.isPGroup
  rw [hn]
  exact (hp.odd_of_ne_two hp2).pow

private theorem w16g_stableUnder_bot {X : Subgroup (MulAut W)} :
    StableUnder X (⊥ : Subgroup W) := by
  intro x hx u hu
  rw [Subgroup.mem_bot] at hu ⊢
  rw [hu, map_one]

private theorem w16g_stableUnder_map_of_commute {X : Subgroup (MulAut W)} {V : Subgroup W}
    {g : MulAut W} (hg : ∀ x ∈ X, g * x = x * g) (hV : StableUnder X V) :
    StableUnder X (V.map g.toMonoidHom) := by
  intro x hx w hw
  obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hw
  refine Subgroup.mem_map.mpr ⟨x v, hV x hx v hv, ?_⟩
  have h := congrArg (fun φ : MulAut W => φ v) (hg x hx)
  simpa only [MulAut.mul_apply, MulEquiv.coe_toMonoidHom] using h

private theorem w16g_le_s13IsoSum {X : Subgroup (MulAut W)} {U₀ V₁ : Subgroup W}
    (h : IsIrrOn X V₁ ⊥ ∧ SecIsoOn X V₁ ⊥ U₀ ⊥) : V₁ ≤ s13IsoSum X U₀ := by
  unfold s13IsoSum
  exact le_iSup₂ (f := fun W₁ (_ : IsIrrOn X W₁ ⊥ ∧ SecIsoOn X W₁ ⊥ U₀ ⊥) => W₁) V₁ h

private theorem w16g_secIsoOn_map_self {X : Subgroup (MulAut W)} {V : Subgroup W}
    {g : MulAut W} (hV : StableUnder X V) (hg : ∀ x ∈ X, g * x = x * g) :
    SecIsoOn X (V.map g.toMonoidHom) ⊥ V ⊥ := by
  have hg' : ∀ x ∈ X, g⁻¹ * x = x * g⁻¹ := by
    intro x hx
    have h := hg x hx
    calc g⁻¹ * x = g⁻¹ * (x * g) * g⁻¹ := by group
      _ = g⁻¹ * (g * x) * g⁻¹ := by rw [← h]
      _ = x * g⁻¹ := by group
  have hVg : StableUnder X (V.map g.toMonoidHom) := w16g_stableUnder_map_of_commute hg hV
  let β : ↥(V.map g.toMonoidHom) →* W :=
    (g⁻¹).toMonoidHom.comp (V.map g.toMonoidHom).subtype
  have hβ : ∀ a : ↥(V.map g.toMonoidHom), β a = g⁻¹ (a : W) := fun a => rfl
  refine ⟨bot_le, bot_le, hVg, w16g_stableUnder_bot, hV, w16g_stableUnder_bot, β, ?_, ?_, ?_, ?_⟩
  · intro a
    obtain ⟨v, hv, hva⟩ := Subgroup.mem_map.mp a.2
    have hva' : g v = (a : W) := hva
    rw [hβ, ← hva']
    change g⁻¹ (g v) ∈ V
    rw [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]
    exact hv
  · intro a
    rw [Subgroup.mem_bot, Subgroup.mem_bot, hβ]
    constructor
    · intro h
      exact (g⁻¹).injective (by rw [h, map_one])
    · intro h
      rw [h, map_one]
  · intro b hb
    refine ⟨⟨g b, Subgroup.mem_map.mpr ⟨b, hb, rfl⟩⟩, ?_⟩
    rw [Subgroup.mem_bot, hβ]
    change g⁻¹ (g b) * b⁻¹ = 1
    rw [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply, mul_inv_cancel]
  · intro x hx a a' ha'
    rw [Subgroup.mem_bot, hβ, hβ]
    have hxβ : g⁻¹ (x (a : W)) = x (g⁻¹ (a : W)) := by
      have h := congrArg (fun φ : MulAut W => φ (a : W)) (hg' x hx)
      simpa only [MulAut.mul_apply, MulEquiv.coe_toMonoidHom] using h
    rw [ha', hxβ, mul_inv_cancel]

theorem s13_eight_W6_comp (h : Cfg133 A t 3) {z : MulAut W} {N : Subgroup (MulAut W)}
    (hD : Data8 A t z N) :
    commSub ⊤ (Subgroup.zpowers z) ∈ s13IsoComps (conjClosure A (Subgroup.zpowers z)) := by
  classical
  obtain ⟨hXe, hXA, hXO, hcent⟩ := w16g_s13_eight_X_facts h hD
  have hW2 : ∀ w : W, w ^ 2 = 1 := fun w => by rw [pow_two]; exact h.hW w
  obtain ⟨hPO, -, -, -, -, -⟩ := s13_P_facts (p := 3) h
  let P : Subgroup (MulAut W) := ⁅pCoreOf 3 A, Subgroup.zpowers t⁆
  have hzP : z ∈ P := hD.hNP hD.hzN
  have hzO : z ∈ pCoreOf 3 A := hPO hzP
  have hzX : z ∈ conjClosure A (Subgroup.zpowers z) :=
    Subgroup.subset_closure ⟨1, A.one_mem, z, Subgroup.mem_zpowers z, by group⟩
  have hIrrP : IsIrrOn P (commSub ⊤ (Subgroup.zpowers z)) ⊥ :=
    s13_W6_irreducible h.hW hD.hP hzP hD.hz3 hD.hzc hD.hZP hD.hrkz
  have hW6ne : commSub ⊤ (Subgroup.zpowers z) ≠ ⊥ := by
    intro hbot
    have h6 := hD.hrkz
    rw [hbot, rk_bot] at h6
    omega
  have hXnormz : ∀ y ∈ conjClosure A (Subgroup.zpowers z), ∀ x ∈ Subgroup.zpowers z,
      y * x * y⁻¹ ∈ Subgroup.zpowers z := by
    intro y hy x hx
    rw [Subgroup.mem_zpowers_iff] at hx ⊢
    obtain ⟨n, rfl⟩ := hx
    refine ⟨n, ?_⟩
    symm
    have hyz : y * z * y⁻¹ = z := by
      have hc := hcent y (hXO hy) z hzX
      rw [hc, mul_assoc, mul_inv_cancel, mul_one]
    rw [show y * z ^ n * y⁻¹ = (y * z * y⁻¹) ^ n from (conj_zpow).symm, hyz]
  have hW6stabX : StableUnder (conjClosure A (Subgroup.zpowers z))
      (commSub ⊤ (Subgroup.zpowers z)) :=
    stableUnder_commSub hXnormz (fun _ _ _ _ => Subgroup.mem_top _)
  have hPnormz : ∀ y ∈ P, ∀ x ∈ Subgroup.zpowers z, y * x * y⁻¹ ∈ Subgroup.zpowers z := by
    intro y hy x hx
    rw [Subgroup.mem_zpowers_iff] at hx ⊢
    obtain ⟨n, rfl⟩ := hx
    refine ⟨n, ?_⟩
    symm
    have hyz : y * z * y⁻¹ = z := by
      have hc := hD.hzc y hy
      rw [hc, mul_assoc, mul_inv_cancel, mul_one]
    rw [show y * z ^ n * y⁻¹ = (y * z * y⁻¹) ^ n from (conj_zpow).symm, hyz]
  have hW6stabP : StableUnder P (commSub ⊤ (Subgroup.zpowers z)) :=
    stableUnder_commSub hPnormz (fun _ _ _ _ => Subgroup.mem_top _)
  obtain ⟨V, hVW, hVirr⟩ := exists_isIrrOn_le (X := conjClosure A (Subgroup.zpowers z))
    (N := ⊥) (A := commSub ⊤ (Subgroup.zpowers z)) (bot_lt_iff_ne_bot.mpr hW6ne)
    hW6stabX w16g_stableUnder_bot
  have hoddz : Odd (Nat.card ↥(Subgroup.zpowers z)) := by
    rw [Nat.card_zpowers, hD.hz3]; norm_num
  have hfixz_bot : fixV (Subgroup.zpowers z) ⊓ commSub ⊤ (Subgroup.zpowers z) = ⊥ :=
    CFSG.Quasithin.Asc81c.fixV_inf_commSub_eq_bot' hW2 hoddz
  have hV_nfix : ¬ ∀ v ∈ V, z v = v := by
    intro hfix
    have hVle : V ≤ fixV (Subgroup.zpowers z) := fun v hv =>
      mem_fixV_zpowers_iff_apply.mpr (hfix v hv)
    have hle : V ≤ fixV (Subgroup.zpowers z) ⊓ commSub ⊤ (Subgroup.zpowers z) :=
      le_inf hVle hVW
    rw [hfixz_bot] at hle
    exact (bot_lt_iff_ne_bot.mp hVirr.1) (le_bot_iff.mp hle)
  have hne : commSub V (conjClosure A (Subgroup.zpowers z)) ≠ ⊥ := by
    intro hbot
    apply hV_nfix
    intro v hv
    exact (commSub_eq_bot_iff.mp hbot hv) z hzX
  let S : Subgroup W := ⨆ g : ↥P, V.map ((g : MulAut W)).toMonoidHom
  have hVleS : V ≤ S := by
    change V ≤ ⨆ g : ↥P, V.map ((g : MulAut W)).toMonoidHom
    have h1 : V ≤ V.map ((1 : ↥P) : MulAut W).toMonoidHom := by
      intro v hv
      exact Subgroup.mem_map.mpr ⟨v, hv, by simp⟩
    exact h1.trans (le_iSup (fun g : ↥P => V.map ((g : MulAut W)).toMonoidHom) 1)
  have hSne : S ≠ ⊥ := by
    intro hbot
    have hVbot : V ≤ (⊥ : Subgroup W) := hVleS.trans (le_of_eq hbot)
    exact (bot_lt_iff_ne_bot.mp hVirr.1) (le_bot_iff.mp hVbot)
  have hSle : S ≤ commSub ⊤ (Subgroup.zpowers z) := by
    change (⨆ g : ↥P, V.map ((g : MulAut W)).toMonoidHom) ≤
      commSub ⊤ (Subgroup.zpowers z)
    refine iSup_le fun g => ?_
    intro w hw
    obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hw
    exact hW6stabP (g : MulAut W) g.2 v (hVW hv)
  have hSstab : StableUnder P S := by
    intro g' hg' w hw
    change w ∈ ⨆ g : ↥P, V.map ((g : MulAut W)).toMonoidHom at hw
    refine Subgroup.iSup_induction
      (fun g : ↥P => V.map ((g : MulAut W)).toMonoidHom)
      (C := fun w => g' w ∈ ⨆ g : ↥P, V.map ((g : MulAut W)).toMonoidHom) hw ?_ ?_ ?_
    · intro g v hv
      obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hv
      refine Subgroup.mem_iSup_of_mem (⟨g' * g, P.mul_mem hg' g.2⟩ : ↥P) ?_
      exact Subgroup.mem_map.mpr ⟨u, hu, by
        show ((⟨g' * g, P.mul_mem hg' g.2⟩ : ↥P) : MulAut W) u = g' ((g : MulAut W) u)
        rw [Subgroup.coe_mk, MulAut.mul_apply]⟩
    · rw [map_one]
      exact Subgroup.one_mem _
    · intro y z hy hz
      rw [map_mul]
      exact Subgroup.mul_mem _ hy hz
  have hSeq : S = commSub ⊤ (Subgroup.zpowers z) := by
    rcases hIrrP.2.2.2 S hSstab bot_le hSle with h | h
    · exact absurd h hSne
    · exact h
  have hW6le_sum : commSub ⊤ (Subgroup.zpowers z) ≤
      s13IsoSum (conjClosure A (Subgroup.zpowers z)) V := by
    rw [← hSeq]
    change (⨆ g : ↥P, V.map ((g : MulAut W)).toMonoidHom) ≤
      s13IsoSum (conjClosure A (Subgroup.zpowers z)) V
    refine iSup_le fun g => w16g_le_s13IsoSum ⟨?_, ?_⟩
    · exact (map_isIrrOn (X := conjClosure A (Subgroup.zpowers z)) (C := ⊥) (A := ⊤)
        (J := V) (g := (g : MulAut W))
        (fun x hx => hcent (g : MulAut W) (hPO g.2) x hx)
        (fun c hc => by rw [Subgroup.mem_bot] at hc; rw [hc, map_one])
        (fun a _ => Subgroup.mem_top a) ⟨le_top, hVirr⟩).2
    · exact w16g_secIsoOn_map_self hVirr.2.1
        (fun x hx => hcent (g : MulAut W) (hPO g.2) x hx)
  let U : Subgroup W := s13IsoSum (conjClosure A (Subgroup.zpowers z)) V
  have hU : U ∈ s13IsoComps (conjClosure A (Subgroup.zpowers z)) :=
    ⟨V, hVirr, hne, rfl⟩
  have hznot : ¬ Subgroup.zpowers z ≤ s13KerOn (conjClosure A (Subgroup.zpowers z)) U := by
    intro hle
    apply hV_nfix
    intro v hv
    have hzmem : z ∈ s13KerOn (conjClosure A (Subgroup.zpowers z)) U :=
      hle (Subgroup.mem_zpowers z)
    have hzcent : z ∈ centSub U := (Subgroup.mem_inf.mp hzmem).2
    have hvU : v ∈ U := (w16g_le_s13IsoSum_self hVirr) hv
    exact (mem_centSub.mp hzcent) v hvU
  have hcommEq : commSub U (Subgroup.zpowers z) = U :=
    (s13IsoComps_commSub_eq h.hW (p := 3) Nat.prime_three (by norm_num) hXe
      (Subgroup.zpowers_le.mpr hzX) hU).2 hznot
  have hUle : U ≤ commSub ⊤ (Subgroup.zpowers z) := by
    rw [← hcommEq]
    exact commSub_mono le_top le_rfl
  exact ⟨V, hVirr, hne, le_antisymm hW6le_sum hUle⟩

end CFSG.LocalAnalysis.WeakClosure81
