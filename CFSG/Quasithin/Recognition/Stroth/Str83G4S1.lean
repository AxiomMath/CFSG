module

public import CFSG.Quasithin.Recognition.Stroth.Str83G4S1Torus
public import CFSG.Quasithin.Recognition.Stroth.Str83G4S1Chief

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F112R
open CFSG.LieType.BorelTits CFSG.Blueprint CFSG.LieType.Ree
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

section Step5

variable {L1 L2 S : Subgroup G} {a : ℕ}

theorem str83G4_s1_false
    (hfr : Str83G4Frame L1 L2 S a) {g : G} (hg : g ∈ L1 ⊔ S)
    (hc : ¬ Z2 L1 L2 S ≤ Subgroup.centralizer (CFSG.conjugate (Z2 L1 L2 S) g : Set G)) :
    False := by
  classical
  obtain ⟨d⟩ := str83G4Data_nonempty hfr
  have hsupq := str83G4_s1_sup_q2 hfr hg hc
  have hA0 := str83G4_s1_centralizer_sup_z2 hfr hg hc
  have hQ1S : Q1 L1 L2 S ≤ S := str83G4_q1_le_s hfr
  have hQ2S : Q2 L1 L2 S ≤ S := str83G4_q2_le_s hfr
  have hXQ1 : str83X L1 L2 S ≤ Q1 L1 L2 S := str83X_le_q1 hfr
  have hZ2Q1 : Z2 L1 L2 S ≤ Q1 L1 L2 S := (z2_le_str83X L1 L2 S).trans hXQ1
  have hZ2Q2 : Z2 L1 L2 S ≤ Q2 L1 L2 S := Setup.omegaOneCenterOf_le _
  have hQ2C : Q2 L1 L2 S ≤ Subgroup.centralizer (Z2 L1 L2 S : Set G) :=
    SmithC27.pCoreOf_le_centralizer_omegaOneCenterOf (P2 L1 L2 S)
  have hHZ2 : L2 ⊔ S ≤ Subgroup.normalizer (Z2 L1 L2 S : Set G) :=
    (sup_le le_sup_left ((le_sup_right : S ≤ bigB L1 L2 S).trans le_sup_right)).trans
      (SmithC27.le_normalizer_omegaOneCenterOf_pCoreOf (P2 L1 L2 S))
  have hZgS : CFSG.conjugate (Z2 L1 L2 S) g ≤ S :=
    (le_sup_left : CFSG.conjugate (Z2 L1 L2 S) g ≤ CFSG.conjugate (Z2 L1 L2 S) g ⊔ Q2 L1 L2 S).trans
      hsupq.le
  have hgX : g⁻¹ ∈ Subgroup.normalizer (str83X L1 L2 S : Set G) :=
    le_normalizer_str83X L1 L2 S (sup_left_le_p1 L1 L2 S ((L1 ⊔ S).inv_mem hg))
  have hZgX : CFSG.conjugate (Z2 L1 L2 S) g ≤ str83X L1 L2 S := by
    intro y hy
    have h := (Subgroup.mem_normalizer_iff.mp hgX (g * y * g⁻¹)).mp
      (z2_le_str83X L1 L2 S ((CFSG.mem_conjugate_iff _ _ _).mp hy))
    have e : g⁻¹ * (g * y * g⁻¹) * g⁻¹⁻¹ = y := by group
    rwa [e] at h
  have hXQ : str83X L1 L2 S ⊔ Q2 L1 L2 S = S :=
    le_antisymm (sup_le (hXQ1.trans hQ1S) hQ2S) (hsupq.symm.le.trans (sup_le_sup_right hZgX _))
  have hQ : Q1 L1 L2 S ⊔ Q2 L1 L2 S = S :=
    le_antisymm (sup_le hQ1S hQ2S) (hXQ.symm.le.trans (sup_le_sup_right hXQ1 _))
  obtain ⟨R₀, hR₀⟩ : ∃ R₀ : Subgroup G, R₀ = Q1 L1 L2 S ⊓ Q2 L1 L2 S ⊓
      CFSG.conjugate (Q1 L1 L2 S ⊓ Q2 L1 L2 S) d.w := ⟨_, rfl⟩
  have hR0 : R₀ ≤ Q1 L1 L2 S ⊓ Q2 L1 L2 S := hR₀ ▸ inf_le_left
  have hR0N : L2 ⊔ S ≤ Subgroup.normalizer (R₀ : Set G) :=
    hR₀ ▸ str83G4_s1_le_normalizer_r0 hfr d hXQ
  have hZ2R0 : Z2 L1 L2 S ≤ R₀ := by
    rw [hR₀]
    refine le_inf (le_inf hZ2Q1 hZ2Q2) fun z hz => ?_
    rw [CFSG.mem_conjugate_iff]
    have h := (Subgroup.mem_normalizer_iff.mp (hHZ2 d.hwH2) z).mp hz
    exact ⟨hZ2Q1 h, hZ2Q2 h⟩
  obtain ⟨x0, hx0, hx01⟩ :=
    (Subgroup.bot_or_exists_ne_one d.D2).resolve_left (str83G4Data_D2_ne_bot hfr d)
  have hfix : ∀ y ∈ Q2 L1 L2 S, (∀ x ∈ d.D2, x * y * x⁻¹ * y⁻¹ ∈ R₀) → y ∈ R₀ := by
    intro y hy h
    rw [hR₀] at h ⊢
    exact str83G4_s1_fpf_r0 hfr d hg hc hx0 hx01 hy (h x0 hx0)
  obtain ⟨t, htZg, htQ2⟩ := SetLike.not_le_iff_exists.mp
    fun h : CFSG.conjugate (Z2 L1 L2 S) g ≤ Q2 L1 L2 S =>
      hc (Subgroup.le_centralizer_iff.mpr (h.trans hQ2C))
  have ht2 : t * t = 1 := by
    have h1 := (SmithC27.isElemAbelian_omegaOneCenterOf (Q2 L1 L2 S)).2 _
      ((CFSG.mem_conjugate_iff _ _ _).mp htZg)
    rw [sq] at h1
    have e : t * t = g⁻¹ * ((g * t * g⁻¹) * (g * t * g⁻¹)) * g := by group
    rw [e, h1, mul_one, inv_mul_cancel]
  have hdisp : Q1 L1 L2 S ⊓ Q2 L1 L2 S ≤
      centralizerMod R₀ (Q2 L1 L2 S) (Subgroup.zpowers t) := by
    rw [← hA0]
    refine sup_le (fun c hc' => ?_) (fun z hz => ?_)
    · obtain ⟨hcQ2, hcC⟩ := Subgroup.mem_inf.mp hc'
      refine ⟨hcQ2, hR0N ((le_sup_right : S ≤ L2 ⊔ S) (hQ2S hcQ2)), fun u hu => ?_⟩
      have hct : Commute c t := (Subgroup.mem_centralizer_iff.mp hcC t htZg).symm
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
      rw [(hct.zpow_right k).eq, mul_inv_cancel_right, mul_inv_cancel]
      exact R₀.one_mem
    · refine ⟨hZ2Q2 hz, hR0N ((le_sup_right : S ≤ L2 ⊔ S) (hQ2S (hZ2Q2 hz))), fun u hu => ?_⟩
      have huS : u ∈ S := (Subgroup.zpowers_le.mpr (hZgS htZg)) hu
      have h1 : u * z⁻¹ * u⁻¹ ∈ Z2 L1 L2 S :=
        (Subgroup.mem_normalizer_iff.mp (hHZ2 ((le_sup_right : S ≤ L2 ⊔ S) huS)) z⁻¹).mp
          ((Z2 L1 L2 S).inv_mem hz)
      have e : z * u * z⁻¹ * u⁻¹ = z * (u * z⁻¹ * u⁻¹) := by group
      rw [e]
      exact hZ2R0 ((Z2 L1 L2 S).mul_mem hz h1)
  exact str83G4_s1_false_of_r0 hfr d hR0 hR0N hfix hQ (hZgS htZg) htQ2 ht2 hdisp

end Step5

theorem str83G4Z2Comm_holds :
    Str83G4Z2Comm := by
  intro G _ _ L1 L2 S a hfr k hk
  classical
  have hF := hfr.1
  have hBL1 : bigB L1 L2 S ≤ Subgroup.normalizer (L1 : Set G) :=
    sup_le (sup_le ((F1.borelOf_le L1 S).trans Subgroup.le_normalizer) hF.1.h1.borel_le)
      hF.1.h1.normalizes
  have hk' : k ∈ ((L1 ⊔ bigB L1 L2 S : Subgroup G) : Set G) := hk
  rw [Subgroup.coe_mul_of_right_le_normalizer_left L1 (bigB L1 L2 S) hBL1] at hk'
  obtain ⟨l, hl, b, hb, rfl⟩ := Set.mem_mul.mp hk'
  have hbZ := bigB_le_normalizer_z2 L1 L2 S hb
  have heq : CFSG.Quasithin.conjSub (l * b) (Z2 L1 L2 S) = CFSG.conjugate (Z2 L1 L2 S) l⁻¹ := by
    ext y
    rw [CFSG.Quasithin.mem_conjSub, CFSG.mem_conjugate_iff]
    have e : (l * b)⁻¹ * y * (l * b) = b⁻¹ * (l⁻¹ * y * l⁻¹⁻¹) * b⁻¹⁻¹ := by group
    rw [e, ← Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (Z2 L1 L2 S : Set G)).inv_mem hbZ)]
  rw [heq]
  by_contra hc
  exact str83G4_s1_false hfr ((L1 ⊔ S).inv_mem ((le_sup_left : L1 ≤ L1 ⊔ S) hl)) hc

end CFSG.Quasithin.Stroth

end
