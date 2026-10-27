module

public import CFSG.Quasithin.Recognition.Stroth.Str83G4S1B7
public import CFSG.Quasithin.Recognition.Stroth.Str83CartanTools

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F112R
open CFSG.GH74.Uniqueness.Bender
open CFSG.LieType.BorelTits CFSG.Blueprint CFSG.LieType.Ree
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L1 L2 S : Subgroup G} {a : ℕ}

private theorem g4_eq_sup_left (hfr : Str83G4Frame L1 L2 S a) :
    S = (S ⊓ L1) ⊔ Q1 L1 L2 S := by
  obtain ⟨hF, hB, ha, ⟨eSz⟩, -, -⟩ := hfr
  exact eq_sup_pCoreOf_of_bender_left hF.1 hB (Or.inl ⟨a, ha, ⟨eSz⟩⟩)

private theorem g4_sup_left (hfr : Str83G4Frame L1 L2 S a) :
    L1 ⊔ S = L1 ⊔ Q1 L1 L2 S :=
  sup_eq_of_S_eq (g4_eq_sup_left hfr)

private theorem g4_q1_le_normalizer_left (hF : Hyp111 L1 L2 S) :
    Q1 L1 L2 S ≤ Subgroup.normalizer (L1 : Set G) :=
  (pCoreOf_le 2 (P1 L1 L2 S)).trans
    (sup_le Subgroup.le_normalizer (bigB_le_normalizer_of_hyp111 hF))

private theorem g4_inf_normalizer_eq_borelOf_sup_q1
    (hfr : Str83G4Frame L1 L2 S a) :
    (L1 ⊔ Q1 L1 L2 S) ⊓ Subgroup.normalizer (S : Set G) = borelOf L1 S ⊔ Q1 L1 L2 S := by
  have hF := hfr.1
  have hB := hfr.2.1
  have hQ1S : Q1 L1 L2 S ≤ S := str83G4_q1_le_s hfr
  have hQ1NL : Q1 L1 L2 S ≤ Subgroup.normalizer (L1 : Set G) := g4_q1_le_normalizer_left hF.1
  refine le_antisymm ?_ ?_
  · intro g hg
    obtain ⟨hgH, hgN⟩ := Subgroup.mem_inf.mp hg
    obtain ⟨l, hl, q, hq, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hQ1NL).mp hgH
    have hqN : q ∈ Subgroup.normalizer (S : Set G) := Subgroup.le_normalizer (hQ1S hq)
    have hlN : l ∈ Subgroup.normalizer (S : Set G) := by
      have h1 : l = (l * q) * q⁻¹ := by group
      rw [h1]
      exact (Subgroup.normalizer (S : Set G)).mul_mem hgN (Subgroup.inv_mem _ hqN)
    have hlN' : l ∈ Subgroup.normalizer ((S ⊓ L1 : Subgroup G) : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · intro hx
        exact ⟨(Subgroup.mem_normalizer_iff.mp hlN x).mp hx.1,
          L1.mul_mem (L1.mul_mem hl hx.2) (L1.inv_mem hl)⟩
      · intro hx
        refine ⟨(Subgroup.mem_normalizer_iff.mp hlN x).mpr hx.1, ?_⟩
        have hx' : x = l⁻¹ * (l * x * l⁻¹) * l := by group
        rw [hx']
        exact L1.mul_mem (L1.mul_mem (L1.inv_mem hl) hx.2) hl
    have hlB : l ∈ borelOf L1 S := Subgroup.mem_inf.mpr ⟨hl, hlN'⟩
    exact (borelOf L1 S ⊔ Q1 L1 L2 S).mul_mem (Subgroup.mem_sup_left hlB)
      (Subgroup.mem_sup_right hq)
  · refine sup_le ?_ ?_
    · have hB1bigB : borelOf L1 S ≤ bigB L1 L2 S := by
        show borelOf L1 S ≤ (borelOf L1 S ⊔ borelOf L2 S) ⊔ S
        exact le_sup_of_le_left le_sup_left
      exact le_inf ((F1.borelOf_le L1 S).trans le_sup_left) (hB1bigB.trans hB)
    · exact le_inf le_sup_right (hQ1S.trans Subgroup.le_normalizer)

theorem str83G4Data_D2_ne_bot (hfr : Str83G4Frame L1 L2 S a)
    (d : Str83G4Data L1 L2 S) : d.D2 ≠ ⊥ := by
  obtain ⟨hF, -, ha, -, hL2, -⟩ := hfr
  have hBT : BenderType (oTwoQuot ↥L2) (2 * a + 1) 1 1 :=
    BenderType.linear (2 * a + 1) (by omega) (Classical.choice hL2)
  have hcard : Nat.card d.D2 = 2 ^ (2 * a + 1) - 1 :=
    (card_isCyclic_of_hallTwoPrime hF.1.h2.sylow d.hD2hall d.hD2sup hBT).1
  intro hbot
  rw [hbot, Subgroup.card_bot] at hcard
  have h8 : 8 ≤ 2 ^ (2 * a + 1) :=
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

theorem str83G4_fpf_D1 (hfr : Str83G4Frame L1 L2 S a)
    (d : Str83G4Data L1 L2 S) {δ x : G} (hδ : δ ∈ d.D1) (hδ1 : δ ≠ 1) (hxS : x ∈ S)
    (hcomm : δ * x * δ⁻¹ * x⁻¹ ∈ Q1 L1 L2 S) : x ∈ Q1 L1 L2 S := by
  have hF := hfr.1
  have ha : 1 ≤ a := hfr.2.2.1
  obtain ⟨eSz⟩ := hfr.2.2.2.1
  have hS1 := g4_eq_sup_left hfr
  have hQ1S : Q1 L1 L2 S ≤ S := str83G4_q1_le_s hfr
  let H : Subgroup G := L1 ⊔ Q1 L1 L2 S
  have hH : H = L1 ⊔ S := (g4_sup_left hfr).symm
  have hSH : IsSylowTwoOf S H := by
    rw [hH]
    exact str83G4_isSylowTwoOf_sup_left hfr
  have hQ : Q1 L1 L2 S = pCoreOf 2 H := (pCoreOf_sup_pCoreOf hF.1).symm
  have hBLH : borelOf L1 S ≤ H := (F1.borelOf_le L1 S).trans le_sup_left
  have hDleH : d.D1 ≤ H := d.hD1hall.1.trans hBLH
  have hDinfQ : d.D1 ⊓ Q1 L1 L2 S = ⊥ := by
    rw [inf_comm]
    exact RonanF13.inf_eq_bot_of_odd (pCoreOf_isPGroup 2 (P1 L1 L2 S)) d.hD1hall.2.1
  have hBT : BenderType (oTwoQuot ↥H) (2 * a + 1) 2 1 := by
    have e : oTwoQuot ↥H ≃* CFSG.Open.Sz a := (oTwoQuotSupEquiv hF.1).trans eSz
    exact BenderType.suzuki a ha
      (e.trans (MulEquiv.subgroupCongr (szModel_eq_open_sz a).symm))
  exact fixed_point_free_of_bender_quotient (L := L1) hQ hSH hQ1S hS1 hDleH
    d.hD1hall d.hD1sup hBLH (g4_inf_normalizer_eq_borelOf_sup_q1 hfr) hDinfQ hBT
    (hDleH hδ) hxS hδ hδ1 hcomm

theorem str83G4_trivial_on_sup (hfr : Str83G4Frame L1 L2 S a)
    {k : G} (hkB : k ∈ bigB L1 L2 S)
    (hk : ∀ l ∈ L1, k * l * k⁻¹ * l⁻¹ ∈ pCoreOf 2 L1) :
    ∀ x ∈ L1 ⊔ S, k * x * k⁻¹ * x⁻¹ ∈ Q1 L1 L2 S := by
  have hF := hfr.1
  have hQ1NL1 : Q1 L1 L2 S ≤ Subgroup.normalizer (L1 : Set G) := g4_q1_le_normalizer_left hF.1
  have hBigBNQ1 : bigB L1 L2 S ≤ Subgroup.normalizer (Q1 L1 L2 S : Set G) :=
    (le_sup_right : bigB L1 L2 S ≤ P1 L1 L2 S).trans (le_normalizer_pCoreOf 2 (P1 L1 L2 S))
  have hL1NQ1 : L1 ≤ Subgroup.normalizer (Q1 L1 L2 S : Set G) :=
    (le_sup_left : L1 ≤ P1 L1 L2 S).trans (le_normalizer_pCoreOf 2 (P1 L1 L2 S))
  intro x hx
  have hx' : x ∈ L1 ⊔ Q1 L1 L2 S := by rwa [g4_sup_left hfr] at hx
  obtain ⟨l, hl, q, hq, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hQ1NL1).mp hx'
  have hkl : k * l * k⁻¹ * l⁻¹ ∈ Q1 L1 L2 S := (Hyp111.pCoreOf_le_pCoreOf_vertex hF.1) (hk l hl)
  have hkq : k * q * k⁻¹ * q⁻¹ ∈ Q1 L1 L2 S := by
    have h1 : k * q * k⁻¹ ∈ Q1 L1 L2 S :=
      (Subgroup.mem_normalizer_iff.mp (hBigBNQ1 hkB) q).mp hq
    exact (Q1 L1 L2 S).mul_mem h1 ((Q1 L1 L2 S).inv_mem hq)
  have hconj : l * (k * q * k⁻¹ * q⁻¹) * l⁻¹ ∈ Q1 L1 L2 S :=
    (Subgroup.mem_normalizer_iff.mp (hL1NQ1 hl) _).mp hkq
  have e : k * (l * q) * k⁻¹ * (l * q)⁻¹ =
      (k * l * k⁻¹ * l⁻¹) * (l * (k * q * k⁻¹ * q⁻¹) * l⁻¹) := by
    group
  rw [e]
  exact (Q1 L1 L2 S).mul_mem hkl hconj

theorem str83G4_mem_q1_inf_q2_of_fix
    (hfr : Str83G4Frame L1 L2 S a) (d : Str83G4Data L1 L2 S)
    (htriv : ∀ x ∈ d.D2, (∀ l ∈ L1, x * l * x⁻¹ * l⁻¹ ∈ pCoreOf 2 L1) → x = 1)
    {x y : G} (hx : x ∈ d.D2) (hx1 : x ≠ 1) (hy : y ∈ Q2 L1 L2 S)
    (hxy : x * y * x⁻¹ * y⁻¹ ∈ Q1 L1 L2 S ⊓ Q2 L1 L2 S) : y ∈ Q1 L1 L2 S ⊓ Q2 L1 L2 S := by
  by_cases hyQ1 : y ∈ Q1 L1 L2 S
  · exact ⟨hyQ1, hy⟩
  exfalso
  obtain ⟨δ, hδD1, hδ⟩ := d.hdelta x hx
  have hD1B : d.D1 ≤ bigB L1 L2 S := by
    rw [d.hBsplit]
    exact le_sup_of_le_left le_sup_right
  have hxB : x ∈ bigB L1 L2 S := by
    rw [d.hBsplit]
    exact Subgroup.mem_sup_right hx
  have hδ1 : δ ≠ 1 := by
    intro hδ1
    refine hx1 (htriv x hx fun l hl => ?_)
    simpa [hδ1] using hδ l hl
  have hyS : y ∈ S := str83G4_q2_le_s hfr hy
  set k : G := x * δ⁻¹ with hkdef
  have hkB : k ∈ bigB L1 L2 S := (bigB L1 L2 S).mul_mem hxB ((bigB L1 L2 S).inv_mem (hD1B hδD1))
  have hky : k * y * k⁻¹ * y⁻¹ ∈ Q1 L1 L2 S :=
    str83G4_trivial_on_sup hfr hkB hδ y ((le_sup_right : S ≤ L1 ⊔ S) hyS)
  set r : G := x * y * x⁻¹ * y⁻¹ with hrdef
  have hr : r ∈ Q1 L1 L2 S := hxy.1
  set c : G := y * k * y⁻¹ * k⁻¹ with hcdef
  have hc : c ∈ Q1 L1 L2 S := by
    have e : c = (k * y * k⁻¹ * y⁻¹)⁻¹ := by rw [hcdef]; group
    rw [e]
    exact (Q1 L1 L2 S).inv_mem hky
  have hBigBNQ1 : bigB L1 L2 S ≤ Subgroup.normalizer (Q1 L1 L2 S : Set G) :=
    (le_sup_right : bigB L1 L2 S ≤ P1 L1 L2 S).trans (le_normalizer_pCoreOf 2 (P1 L1 L2 S))
  have hconj : k⁻¹ * (r * c) * k ∈ Q1 L1 L2 S := by
    have h := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hBigBNQ1 hkB)) (r * c)).mp
      ((Q1 L1 L2 S).mul_mem hr hc)
    simpa using h
  have e : δ * y * δ⁻¹ * y⁻¹ = k⁻¹ * (r * c) * k := by
    rw [hrdef, hcdef, hkdef]
    group
  exact hyQ1 (str83G4_fpf_D1 hfr d hδD1 hδ1 hyS (by rwa [e]))

private theorem g4_conjugate_centralizerMod {V X U : Subgroup G} {w : G}
    (hV : w ∈ Subgroup.normalizer (V : Set G)) (hX : w ∈ Subgroup.normalizer (X : Set G)) :
    CFSG.conjugate (centralizerMod V X U) w = centralizerMod V X (CFSG.conjugate U w) := by
  have h := conjSub_centralizerMod w⁻¹ V X U
  rw [F7.conjSub_eq_of_mem_normalizer (inv_mem hV), F7.conjSub_eq_of_mem_normalizer (inv_mem hX)]
    at h
  exact h

theorem str83G4_s1_le_normalizer_r0
    (hfr : Str83G4Frame L1 L2 S a) (d : Str83G4Data L1 L2 S)
    (hXQ : str83X L1 L2 S ⊔ Q2 L1 L2 S = S) :
    L2 ⊔ S ≤ Subgroup.normalizer
      ((Q1 L1 L2 S ⊓ Q2 L1 L2 S ⊓ CFSG.conjugate (Q1 L1 L2 S ⊓ Q2 L1 L2 S) d.w :
        Subgroup G) : Set G) := by
  have hL2S : L2 ⊔ S ≤ Subgroup.normalizer (Q2 L1 L2 S : Set G) :=
    str86_l2sup_le_normalizer_q2
  have hwQ : d.w ∈ Subgroup.normalizer (Q2 L1 L2 S : Set G) := hL2S d.hwH2
  have hwZ : d.w ∈ Subgroup.normalizer (Z2 L1 L2 S : Set G) :=
    normalizer_le_normalizer_omegaOneCenterOf (Q2 L1 L2 S) hwQ
  have hSB : S ≤ bigB L1 L2 S := le_sup_right
  have hXN : str83X L1 L2 S ≤ Subgroup.normalizer (Z2 L1 L2 S : Set G) :=
    (str83X_le_q1 hfr).trans ((str83G4_q1_le_s hfr).trans
      (hSB.trans (bigB_le_normalizer_z2 L1 L2 S)))
  have hXwN : CFSG.conjugate (str83X L1 L2 S) d.w ≤
      Subgroup.normalizer (Z2 L1 L2 S : Set G) := by
    have h := conjSub_le_normalizer (g := d.w⁻¹) hXN
    rwa [F7.conjSub_eq_of_mem_normalizer (inv_mem hwZ)] at h
  have hR0 : Q1 L1 L2 S ⊓ Q2 L1 L2 S ⊓ CFSG.conjugate (Q1 L1 L2 S ⊓ Q2 L1 L2 S) d.w =
      centralizerMod (Z2 L1 L2 S) (Q2 L1 L2 S)
        (str83X L1 L2 S ⊔ CFSG.conjugate (str83X L1 L2 S) d.w) := by
    rw [str83G4_q1_inf_q2_eq_centralizerMod hfr, g4_conjugate_centralizerMod hwZ hwQ,
      centralizerMod_sup_right hXN hXwN]
  rw [hR0]
  have hQX : Q2 L1 L2 S ≤ Subgroup.normalizer (str83X L1 L2 S : Set G) :=
    ((str83G4_q2_le_s hfr).trans ((le_sup_right : S ≤ bigB L1 L2 S).trans le_sup_right)).trans
      (le_normalizer_str83X L1 L2 S)
  have hQXw : Q2 L1 L2 S ≤ Subgroup.normalizer
      (CFSG.conjugate (str83X L1 L2 S) d.w : Set G) := by
    have h := conjSub_le_normalizer (g := d.w⁻¹) hQX
    rwa [F7.conjSub_eq_of_mem_normalizer (inv_mem hwQ)] at h
  have hQY : Q2 L1 L2 S ≤ Subgroup.normalizer
      ((str83X L1 L2 S ⊔ CFSG.conjugate (str83X L1 L2 S) d.w : Subgroup G) : Set G) :=
    (le_inf hQX hQXw).trans (Subgroup.inf_normalizer_le_normalizer_sup _ _)
  refine le_normalizer_centralizerMod (fun g hg => ?_) hL2S ?_
  · exact normalizer_le_normalizer_omegaOneCenterOf (Q2 L1 L2 S) (hL2S hg)
  ·
    rw [← d.hwTop]
    refine sup_le ?_ ?_
    · exact hXQ.symm.le.trans (sup_le (le_sup_left.trans Subgroup.le_normalizer) hQY)
    · have hQw : CFSG.conjugate (Q2 L1 L2 S) d.w = Q2 L1 L2 S :=
        CFSG.conjugate_eq_self_of_mem_normalizer hwQ
      have hSw : CFSG.conjugate S d.w =
          CFSG.conjugate (str83X L1 L2 S) d.w ⊔ Q2 L1 L2 S :=
        calc CFSG.conjugate S d.w
            = CFSG.conjugate (str83X L1 L2 S ⊔ Q2 L1 L2 S) d.w := by rw [hXQ]
          _ = CFSG.conjugate (str83X L1 L2 S) d.w ⊔ CFSG.conjugate (Q2 L1 L2 S) d.w := by
              simp only [CFSG.conjugate]
              rw [Subgroup.map_sup]
          _ = CFSG.conjugate (str83X L1 L2 S) d.w ⊔ Q2 L1 L2 S := by rw [hQw]
      exact hSw.le.trans (sup_le (le_sup_right.trans Subgroup.le_normalizer) hQY)

theorem str83G4_mem_r0_of_fpf (d : Str83G4Data L1 L2 S)
    (hfpf : ∀ x ∈ d.D2, x ≠ 1 → ∀ y ∈ Q2 L1 L2 S,
      x * y * x⁻¹ * y⁻¹ ∈ Q1 L1 L2 S ⊓ Q2 L1 L2 S → y ∈ Q1 L1 L2 S ⊓ Q2 L1 L2 S)
    {x y : G} (hx : x ∈ d.D2) (hx1 : x ≠ 1) (hy : y ∈ Q2 L1 L2 S)
    (hxy : x * y * x⁻¹ * y⁻¹ ∈
      Q1 L1 L2 S ⊓ Q2 L1 L2 S ⊓ CFSG.conjugate (Q1 L1 L2 S ⊓ Q2 L1 L2 S) d.w) :
    y ∈ Q1 L1 L2 S ⊓ Q2 L1 L2 S ⊓ CFSG.conjugate (Q1 L1 L2 S ⊓ Q2 L1 L2 S) d.w := by
  refine ⟨hfpf x hx hx1 y hy hxy.1, ?_⟩
  have hwQ : d.w ∈ Subgroup.normalizer (Q2 L1 L2 S : Set G) :=
    str86_l2sup_le_normalizer_q2 d.hwH2
  have hy' : d.w * y * d.w⁻¹ ∈ Q2 L1 L2 S := (Subgroup.mem_normalizer_iff.mp hwQ y).mp hy
  have hw : d.w * x * d.w⁻¹ = x⁻¹ := d.hwInv x hx
  have hxyw : d.w * (x * y * x⁻¹ * y⁻¹) * d.w⁻¹ ∈ Q1 L1 L2 S ⊓ Q2 L1 L2 S :=
    (CFSG.mem_conjugate_iff _ _ _).mp hxy.2
  have e : d.w * (x * y * x⁻¹ * y⁻¹) * d.w⁻¹ =
      (d.w * x * d.w⁻¹) * (d.w * y * d.w⁻¹) * (d.w * x * d.w⁻¹)⁻¹ * (d.w * y * d.w⁻¹)⁻¹ := by
    group
  rw [e, hw] at hxyw
  exact (CFSG.mem_conjugate_iff _ _ _).mpr
    (hfpf x⁻¹ (d.D2.inv_mem hx) (inv_ne_one.mpr hx1) _ hy' hxyw)

end CFSG.Quasithin.Stroth

end
