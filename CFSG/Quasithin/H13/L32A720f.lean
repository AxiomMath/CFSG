module

public import CFSG.Quasithin.H13.L32A720e

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

section General

variable {G : Type} [Group G]

theorem exists_mul_pow_eq {N : Subgroup G} {b p : G} (hbN : b ∈ Subgroup.normalizer (N : Set G))
    (hpN : p ∈ Subgroup.normalizer (N : Set G))
    (hcomm : ∀ n : ℕ, (p ^ n)⁻¹ * (b⁻¹ * p ^ n * b) ∈ N) (n : ℕ) :
    ∃ ν ∈ N, (b * p) ^ n = b ^ n * p ^ n * ν := by
  induction n with
  | zero => exact ⟨1, N.one_mem, by simp⟩
  | succ n ih =>
    obtain ⟨ν, hν, e⟩ := ih
    have h1 : b⁻¹ * ν * b ∈ N := by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem hbN) ν).mp hν
      simpa using this
    have h2 : (p ^ n)⁻¹ * (b⁻¹ * p ^ n * b) * (b⁻¹ * ν * b) ∈ N := N.mul_mem (hcomm n) h1
    have h3 : p⁻¹ * ((p ^ n)⁻¹ * (b⁻¹ * p ^ n * b) * (b⁻¹ * ν * b)) * p ∈ N := by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem hpN) _).mp h2
      simpa using this
    refine ⟨_, h3, ?_⟩
    rw [pow_succ, e, pow_succ, pow_succ]
    group

theorem commutator_sup_le_of {A B K N H₀ : Subgroup G} (hAH : A ≤ H₀) (hBH : B ≤ H₀)
    (hN : H₀ ≤ Subgroup.normalizer (N : Set G)) (hA : ⁅A, K⁆ ≤ N) (hB : ⁅B, K⁆ ≤ N) :
    ⁅A ⊔ B, K⁆ ≤ N := by
  let S : Subgroup G :=
    { carrier := {x | x ∈ H₀ ∧ ∀ k ∈ K, ⁅x, k⁆ ∈ N}
      mul_mem' := fun {x y} hx hy => ⟨mul_mem hx.1 hy.1, fun k hk => by
        rw [commutatorElement_mul_left']
        have h1 : x * ⁅y, k⁆ * x⁻¹ ∈ N :=
          (Subgroup.mem_normalizer_iff.mp (hN hx.1) _).mp (hy.2 k hk)
        exact mul_mem h1 (hx.2 k hk)⟩
      one_mem' := ⟨one_mem _, fun k _ => by simp⟩
      inv_mem' := fun {x} hx => ⟨inv_mem hx.1, fun k hk => by
        have e : ⁅x⁻¹, k⁆ = x⁻¹ * ⁅x, k⁆⁻¹ * x⁻¹⁻¹ := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact (Subgroup.mem_normalizer_iff.mp (hN (inv_mem hx.1)) _).mp (inv_mem (hx.2 k hk))⟩ }
  have hAS : A ≤ S := fun a ha =>
    ⟨hAH ha, fun k hk => hA (Subgroup.commutator_mem_commutator ha hk)⟩
  have hBS : B ≤ S := fun b hb =>
    ⟨hBH hb, fun k hk => hB (Subgroup.commutator_mem_commutator hb hk)⟩
  rw [Subgroup.commutator_le]
  intro x hx k hk
  exact ((sup_le hAS hBS) hx).2 k hk

end General

namespace Ctx7153

variable {G : Type} [Group G] [Finite G] {T L V H : Subgroup G} (E : Ctx7153 G T L V H)
  (hF : HypF98 T V L (fsuV1 T V) V (hz T V))
include E hF

theorem u_le_l1 : fsuU T V ≤ l1 T L V := by
  have hMod := stmtL32NModule_of_inputs E.h1332 E.h1334
  have hueq := E.u_eq hF
  rw [← hueq, Subgroup.commutator_le]
  intro u hu l hl
  have huU : u ∈ conjClosure V (hz T V) := E.fsuU_eq ▸ hu
  have huH : u ∈ hz T V := pCoreOf_le 2 _ (hF.toHypF91.conjClosure_Vp_le_pCoreOf huU)
  have h1 : u * l * u⁻¹ ∈ l1 T L V :=
    (Subgroup.mem_normalizer_iff.mp (E.hz_le_normalizer_l1 huH) l).mp hl
  rw [commutatorElement_def]
  exact mul_mem h1 (inv_mem hl)

omit hF in
theorem n1_eq : pCoreOf 2 (l1 T L V) = l1 T L V ⊓ pCoreOf 2 (hz T V) := by
  obtain ⟨hL1K, -⟩ := lemma14_7_15_one E.h331 E.hThm E.h1222 E.h1332 E.h1334 E.S E.three
  exact pCoreOf_eq_inf_pCoreOf ((hL1K.trans (oTwoUpper_le H)).trans E.le_hz)
    E.hz_le_normalizer_l1

theorem inf_centralizer_n1 (h13314 : A6.Stmt13_3_14) :
    fsuU T V ⊓ Subgroup.centralizer (pCoreOf 2 (l1 T L V) : Set G) = fsuV1 T V := by
  have hQC := E.inf_centralizer_qh hF h13314
  have hn1 := E.n1_eq
  obtain ⟨hL1K, -⟩ := lemma14_7_15_one E.h331 E.hThm E.h1222 E.h1332 E.h1334 E.S E.three
  have hL1H : l1 T L V ≤ hz T V := (hL1K.trans (oTwoUpper_le H)).trans E.le_hz
  have hUe : fsuU T V = conjClosure V (hz T V) := E.fsuU_eq
  have hN1H : pCoreOf 2 (l1 T L V) ≤ hz T V := (pCoreOf_le 2 _).trans hL1H
  apply le_antisymm
  · rintro u ⟨huU, huN⟩
    refine E.fpf_u hF u huU fun l hl => ?_
    have hlH : l ∈ hz T V := hL1H hl
    have huU' : u ∈ conjClosure V (hz T V) := hUe ▸ huU
    have hw : u * l * u⁻¹ * l⁻¹ ∈
        fsuU T V ⊓ Subgroup.centralizer (pCoreOf 2 (hz T V) : Set G) := by
      refine Subgroup.mem_inf.mpr ⟨?_, Subgroup.mem_centralizer_iff.mpr fun x hx => ?_⟩
      · rw [hUe]
        have h1 : l * u⁻¹ * l⁻¹ ∈ conjClosure V (hz T V) := conj_mem_UH hlH (inv_mem huU')
        have e : u * l * u⁻¹ * l⁻¹ = u * (l * u⁻¹ * l⁻¹) := by group
        rw [e]
        exact mul_mem huU' h1
      · have hc : x * l⁻¹ * x⁻¹ * l⁻¹⁻¹ ∈ pCoreOf 2 (l1 T L V) := by
          rw [hn1]
          refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
          · have h1 : x * l⁻¹ * x⁻¹ ∈ l1 T L V :=
              (Subgroup.mem_normalizer_iff.mp (E.hz_le_normalizer_l1 (pCoreOf_le 2 _ hx)) _).mp
                (inv_mem hl)
            exact mul_mem h1 (by simpa using hl)
          · have h1 : l⁻¹ * x⁻¹ * l⁻¹⁻¹ ∈ pCoreOf 2 (hz T V) :=
              (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 _ (inv_mem hlH)) _).mp
                (inv_mem hx)
            have e : x * l⁻¹ * x⁻¹ * l⁻¹⁻¹ = x * (l⁻¹ * x⁻¹ * l⁻¹⁻¹) := by group
            rw [e]
            exact mul_mem hx h1
        have h2 := Subgroup.mem_centralizer_iff.mp huN _ hc
        have h3 : (x * l⁻¹ * x⁻¹ * l⁻¹⁻¹) * u * (x * l⁻¹ * x⁻¹ * l⁻¹⁻¹)⁻¹ * u⁻¹ = 1 := by
          rw [h2]
          group
        rw [comm_comm_eq hF.toHypF91 hx (inv_mem hlH) huU', inv_inv] at h3
        calc x * (u * l * u⁻¹ * l⁻¹) =
            (x * (u * l * u⁻¹ * l⁻¹) * x⁻¹ * (u * l * u⁻¹ * l⁻¹)⁻¹) * (u * l * u⁻¹ * l⁻¹) * x := by
              group
          _ = (u * l * u⁻¹ * l⁻¹) * x := by rw [h3]; group
    rw [hQC] at hw
    have e : l * u * l⁻¹ * u⁻¹ = (u * l * u⁻¹ * l⁻¹)⁻¹ := by group
    rw [e]
    exact inv_mem hw
  · refine le_inf ?_ fun v hv => Subgroup.mem_centralizer_iff.mpr fun p hp => ?_
    · rw [hUe]
      exact inf_le_left.trans (le_conjClosure V _)
    · exact (Subgroup.mem_centralizer_iff.mp (hN1H hp) v hv).symm

theorem n1_le_p : pCoreOf 2 (l1 T L V) ≤ pCoreOf 2 (oTwoUpper (hz T V)) ∧
    hz T V ≤ Subgroup.normalizer (pCoreOf 2 (l1 T L V) : Set G) := by
  obtain ⟨hH, -⟩ := E.lemma14_7_15_three_of hF
  have hn1 := E.n1_eq
  subst hH
  obtain ⟨hL1K, -⟩ := lemma14_7_15_one E.h331 E.hThm E.h1222 E.h1332 E.h1334 E.S E.three
  refine ⟨?_, fun x hx => ?_⟩
  · rw [hn1, pCoreOf_eq_inf_pCoreOf (oTwoUpper_le _) (le_normalizer_oTwoUpper _)]
    exact inf_le_inf_right _ hL1K
  · rw [hn1]
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have h1 := Subgroup.mem_normalizer_iff.mp (E.hz_le_normalizer_l1 hx) y
    have h2 := Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 _ hx) y
    simp only [Subgroup.mem_inf]
    rw [h1, h2]

theorem u_le_n1 : fsuU T V ≤ pCoreOf 2 (l1 T L V) := by
  rw [E.n1_eq]
  refine le_inf (E.u_le_l1 hF) ?_
  rw [E.fsuU_eq]
  exact hF.toHypF91.conjClosure_Vp_le_pCoreOf

theorem p_le_sup_n1 (h13314 : A6.Stmt13_3_14) :
    pCoreOf 2 (oTwoUpper (hz T V)) ≤ pCoreOf 2 (l1 T L V) ⊔
      (pCoreOf 2 (oTwoUpper (hz T V)) ⊓ Subgroup.centralizer (fsuU T V : Set G)) := by
  have hCN := E.inf_centralizer_n1 hF h13314
  have hN1P := (E.n1_le_p hF).1
  have hUe : fsuU T V = conjClosure V (hz T V) := E.fsuU_eq
  have hN1Q : pCoreOf 2 (l1 T L V) ≤ pCoreOf 2 (hz T V) := by
    rw [E.n1_eq]
    exact inf_le_right
  intro x hx
  have hxQ : x ∈ pCoreOf 2 (hz T V) := pCoreOf_oTwoUpper_le (hz T V) hx
  let f : ↥(conjClosure V (hz T V)) →* ↥(fsuV1 T V) :=
    { toFun := fun u => ⟨x * (u : G) * x⁻¹ * (u : G)⁻¹, hF.toHypF91.commutator_mem_V₁ hxQ u.2⟩
      map_one' := by ext; simp
      map_mul' := fun u₁ u₂ => Subtype.ext (hF.toHypF91.commutator_mul_right hxQ u₁.2 u₂.2) }
  obtain ⟨n, hn, hnf⟩ := exists_mem_of_forall_comm hF.toHypF91 hF.F911_3 hN1Q f (fun u hu => by
    have huV1 : (u : G) ∈ fsuV1 T V := by
      rw [← hCN]
      have hu' : (u : G) ∈ fsuU T V := by
        rw [hUe]
        exact u.2
      exact Subgroup.mem_inf.mpr ⟨hu', Subgroup.mem_centralizer_iff.mpr fun p hp => hu p hp⟩
    apply Subtype.ext
    show x * (u : G) * x⁻¹ * (u : G)⁻¹ = 1
    have hxc : x * u = u * x :=
      (Subgroup.mem_centralizer_iff.mp (pCoreOf_le 2 _ hxQ) _ huV1).symm
    rw [hxc]
    group)
  have hnx : n⁻¹ * x ∈
      pCoreOf 2 (oTwoUpper (hz T V)) ⊓ Subgroup.centralizer (fsuU T V : Set G) := by
    refine Subgroup.mem_inf.mpr
      ⟨mul_mem (inv_mem (hN1P hn)) hx, Subgroup.mem_centralizer_iff.mpr fun u hu => ?_⟩
    have huU : u ∈ conjClosure V (hz T V) := hUe ▸ hu
    have h1 := hnf ⟨u, huU⟩
    change x * u * x⁻¹ * u⁻¹ = n * u * n⁻¹ * u⁻¹ at h1
    have h2 : x * u * x⁻¹ = n * u * n⁻¹ := by
      calc x * u * x⁻¹ = (x * u * x⁻¹ * u⁻¹) * u := by group
        _ = (n * u * n⁻¹ * u⁻¹) * u := by rw [h1]
        _ = n * u * n⁻¹ := by group
    calc u * (n⁻¹ * x) = n⁻¹ * (n * u * n⁻¹) * x := by group
      _ = n⁻¹ * (x * u * x⁻¹) * x := by rw [h2]
      _ = n⁻¹ * x * u := by group
  have e : x = n * (n⁻¹ * x) := by group
  rw [e]
  exact Subgroup.mul_mem_sup hn hnx

variable {γ γ' : F8.Geom T L (hz T V)} {g k : ↥((L ⊔ T) ⊔ hz T V)}
  (N : Not1471 T L V (hz T V) γ γ' g k)
include N

theorem commutator_p_k_le (h13314 : A6.Stmt13_3_14) :
    ⁅pCoreOf 2 (oTwoUpper (hz T V)), oTwoUpper (hz T V)⁆ ≤ pCoreOf 2 (l1 T L V) := by
  have hMod := stmtL32NModule_of_inputs E.h1332 E.h1334
  have hsup := E.p_le_sup_n1 hF h13314
  obtain ⟨hN1P, hN1n⟩ := E.n1_le_p hF
  have hUN1 := E.u_le_n1 hF
  have hn1 := E.n1_eq
  have hcases := E.cases_720 hF N
  have hcard := E.card_l1dot
  obtain ⟨hH, -⟩ := E.lemma14_7_15_three_of hF
  subst hH
  obtain ⟨hL1K, -⟩ := lemma14_7_15_one E.h331 E.hThm E.h1222 E.h1332 E.h1334 E.S E.three
  have hPH : pCoreOf 2 (oTwoUpper (hz T V)) ≤ hz T V :=
    (pCoreOf_le 2 _).trans (oTwoUpper_le _)
  have hPQ : pCoreOf 2 (oTwoUpper (hz T V)) ≤ pCoreOf 2 (hz T V) := pCoreOf_oTwoUpper_le _
  have hPn : hz T V ≤ Subgroup.normalizer (pCoreOf 2 (oTwoUpper (hz T V)) : Set G) :=
    (le_normalizer_oTwoUpper _).trans (normalizer_le_normalizer_pCoreOf 2 _)
  have hPeq : pCoreOf 2 (oTwoUpper (hz T V)) = pCoreOf 2 (l1 T L V) ⊔
      (pCoreOf 2 (oTwoUpper (hz T V)) ⊓ Subgroup.centralizer (fsuU T V : Set G)) :=
    le_antisymm hsup (sup_le hN1P inf_le_left)
  have hN1K : ⁅pCoreOf 2 (l1 T L V), oTwoUpper (hz T V)⁆ ≤ pCoreOf 2 (l1 T L V) :=
    commutator_le_self hN1n
  have hCPC : pCoreOf 2 (oTwoUpper (hz T V)) ⊓ Subgroup.centralizer (fsuU T V : Set G) ≤
      hz T V ⊓ Subgroup.centralizer (fsuU T V : Set G) := inf_le_inf_right _ hPH
  have hN1H : pCoreOf 2 (l1 T L V) ≤ hz T V := hN1P.trans hPH
  rcases hcases with h | ⟨W₁, W₂, hUW₂, hW₂W₁, hW₁P, hW₁n, hW₂n, -, -, hirr, hfaith, hW₂K, hCK⟩
  · rw [hPeq]
    exact commutator_sup_le_of hN1H (inf_le_left.trans hPH) hN1n hN1K
      ((Subgroup.commutator_mono hCPC le_rfl).trans (h.trans hUN1))
  ·
    have hW₁H : W₁ ≤ hz T V := hW₁P.trans (inf_le_left.trans hPH)
    have hW₁sub : W₁ ≤ W₂ ⊔ pCoreOf 2 (l1 T L V) := by
      have hXn : oTwoUpper (hz T V) ≤ Subgroup.normalizer
          ((W₁ ⊓ (W₂ ⊔ pCoreOf 2 (l1 T L V)) : Subgroup G) : Set G) := by
        intro x hx
        have hxH : x ∈ hz T V := oTwoUpper_le _ hx
        rw [Subgroup.mem_normalizer_iff]
        intro y
        have h1 := Subgroup.mem_normalizer_iff.mp (hW₁n hxH) y
        have h2 := Subgroup.mem_normalizer_iff.mp
          (mem_normalizer_sup_of (hW₂n hxH) (hN1n hxH)) y
        simp only [Subgroup.mem_inf]
        rw [h1, h2]
      rcases hirr _ (le_inf hW₂W₁ le_sup_left) inf_le_left hXn with hX | hX
      · exfalso
        have hl : ∀ l ∈ l1 T L V, ∀ w ∈ W₁, l * w * l⁻¹ * w⁻¹ ∈ W₂ := by
          intro l hl w hw
          have hlH : l ∈ hz T V := (hL1K.trans (oTwoUpper_le _)) hl
          have hwQ : w ∈ pCoreOf 2 (hz T V) := hPQ (hW₁P hw).1
          have h1 : l * w * l⁻¹ * w⁻¹ ∈ pCoreOf 2 (l1 T L V) := by
            rw [hn1]
            refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
            · have h3 : w * l⁻¹ * w⁻¹ ∈ l1 T L V :=
                (Subgroup.mem_normalizer_iff.mp (E.hz_le_normalizer_l1 (pCoreOf_le 2 _ hwQ))
                  _).mp (inv_mem hl)
              have e : l * w * l⁻¹ * w⁻¹ = l * (w * l⁻¹ * w⁻¹) := by group
              rw [e]
              exact mul_mem hl h3
            · have h3 : l * w * l⁻¹ ∈ pCoreOf 2 (hz T V) :=
                (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 _ hlH) w).mp hwQ
              exact mul_mem h3 (inv_mem hwQ)
          have h2 : l * w * l⁻¹ * w⁻¹ ∈ W₁ :=
            mul_mem ((Subgroup.mem_normalizer_iff.mp (hW₁n hlH) w).mp hw) (inv_mem hw)
          have h4 : l * w * l⁻¹ * w⁻¹ ∈ W₁ ⊓ (W₂ ⊔ pCoreOf 2 (l1 T L V)) :=
            Subgroup.mem_inf.mpr ⟨h2, Subgroup.mem_sup_right h1⟩
          rw [hX] at h4
          exact h4
        obtain ⟨x, hx, hx1⟩ : ∃ x ∈ modO2Image (hz T V) (l1 T L V), x ≠ 1 := by
          by_contra hno
          push Not at hno
          have : modO2Image (hz T V) (l1 T L V) = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr hno
          rw [this, Subgroup.card_bot] at hcard
          omega
        obtain ⟨l, hlL, rfl⟩ := mem_modO2Image_iff.mp hx
        apply hx1
        rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
        have := hfaith l l.2 (hl l hlL)
        rw [pCoreOf] at this
        obtain ⟨l', hl', e⟩ := this
        rwa [show l' = l from Subtype.ext e] at hl'
      · rw [← hX]
        exact inf_le_right
    have hA₀H : W₂ ⊔ pCoreOf 2 (l1 T L V) ≤ hz T V := sup_le (hW₂W₁.trans hW₁H) hN1H
    have hA₀n : hz T V ≤ Subgroup.normalizer ((W₂ ⊔ pCoreOf 2 (l1 T L V) : Subgroup G) : Set G) :=
      fun x hx => mem_normalizer_sup_of (hW₂n hx) (hN1n hx)
    have h1 : ⁅pCoreOf 2 (oTwoUpper (hz T V)), oTwoUpper (hz T V)⁆ ≤
        W₂ ⊔ pCoreOf 2 (l1 T L V) := by
      rw [hPeq]
      exact commutator_sup_le_of hN1H (inf_le_left.trans hPH) hA₀n (hN1K.trans le_sup_right)
        ((Subgroup.commutator_mono hCPC le_rfl).trans (hCK.trans hW₁sub))
    have h2 : ⁅W₂ ⊔ pCoreOf 2 (l1 T L V), oTwoUpper (hz T V)⁆ ≤ pCoreOf 2 (l1 T L V) :=
      commutator_sup_le_of (hW₂W₁.trans hW₁H) hN1H hN1n (hW₂K.trans hUN1) hN1K
    exact commutator_le_of_series (sup_le ((hW₂W₁.trans hW₁P).trans inf_le_left) hN1P) hPQ
      hN1n hPn h1 h2

theorem o2_l1 (h13314 : A6.Stmt13_3_14) :
    pCoreOf 2 (l1 T L V) = pCoreOf 2 (oTwoUpper (hz T V)) := by
  have hPK := E.commutator_p_k_le hF N h13314
  obtain ⟨hN1P, hN1n⟩ := E.n1_le_p hF
  have hcardK := E.card_kdot
  obtain ⟨hH, -⟩ := E.lemma14_7_15_three_of hF
  subst hH
  refine le_antisymm hN1P ?_
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKH : oTwoUpper (hz T V) ≤ hz T V := oTwoUpper_le _
  have hP2 : IsPGroup 2 ↥(pCoreOf 2 (oTwoUpper (hz T V))) := pCoreOf_isPGroup 2 _
  have hidx : Nat.card (↥(oTwoUpper (hz T V)) ⧸
      (pCoreOf 2 (oTwoUpper (hz T V))).subgroupOf (oTwoUpper (hz T V))) = 27 := by
    rw [Nat.card_congr (quotEquivStar hKH (le_normalizer_oTwoUpper _)).toEquiv]
    exact hcardK
  have h27 : 3 ^ 3 ∣ Nat.card ↥(oTwoUpper (hz T V)) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup
      ((pCoreOf 2 (oTwoUpper (hz T V))).subgroupOf (oTwoUpper (hz T V))), hidx]
    exact Dvd.intro _ rfl
  obtain ⟨B, hB⟩ := Sylow.exists_subgroup_card_pow_prime 3 h27
  set B' := B.map (oTwoUpper (hz T V)).subtype with hB'
  have hB'K : B' ≤ oTwoUpper (hz T V) := Subgroup.map_subtype_le _
  have hB'card : Nat.card B' = 27 := by
    rw [hB', Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hB]
    norm_num
  have hBP : ∀ x ∈ B', x ∈ pCoreOf 2 (oTwoUpper (hz T V)) → x = 1 := by
    intro x hxB hxP
    have h1 : x ^ 27 ∈ (⊥ : Subgroup G) := by
      have := pow_card_eq_one' (G := ↥B') (x := ⟨x, hxB⟩)
      rw [hB'card] at this
      exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)
    obtain ⟨e, he⟩ := hP2 ⟨x, hxP⟩
    have h2 : x ^ 2 ^ e ∈ (⊥ : Subgroup G) :=
      Subgroup.mem_bot.mpr (by simpa using congrArg Subtype.val he)
    exact Subgroup.mem_bot.mp (mem_of_pow_odd_mem (by decide) h1 h2)
  have hKBP : ∀ k ∈ oTwoUpper (hz T V), ∃ b ∈ B', b⁻¹ * k ∈ pCoreOf 2 (oTwoUpper (hz T V)) := by
    intro k hk
    let f : ↥B →* ↥(oTwoUpper (hz T V)) ⧸
        (pCoreOf 2 (oTwoUpper (hz T V))).subgroupOf (oTwoUpper (hz T V)) :=
      (QuotientGroup.mk' _).comp B.subtype
    have hinj : Function.Injective f := by
      rw [injective_iff_map_eq_one]
      intro b hb
      have h1 : ((b : ↥(oTwoUpper (hz T V))) : G) ∈ pCoreOf 2 (oTwoUpper (hz T V)) := by
        have := (QuotientGroup.eq_one_iff _).mp hb
        exact Subgroup.mem_subgroupOf.mp this
      have h2 := hBP _ ⟨b, b.2, rfl⟩ h1
      exact Subtype.ext (Subtype.ext h2)
    have hbij := hinj.bijective_of_nat_card_le (by rw [hidx, hB]; norm_num)
    obtain ⟨b, hb⟩ := hbij.2 (QuotientGroup.mk' _ ⟨k, hk⟩)
    refine ⟨b, ⟨b, b.2, rfl⟩, ?_⟩
    have := QuotientGroup.eq.mp hb
    exact Subgroup.mem_subgroupOf.mp this
  have hP_N : ∀ x ∈ hz T V, Odd (orderOf x) →
      ∃ b ∈ B', ∃ n ∈ pCoreOf 2 (l1 T L V), x = b * n := by
    intro x hx hxo
    have hxK : x ∈ oTwoUpper (hz T V) := mem_oTwoUpper_of_odd hx hxo
    obtain ⟨b, hb, hbp⟩ := hKBP x hxK
    set p := b⁻¹ * x with hpdef
    have hbH : b ∈ hz T V := hKH (hB'K hb)
    have hpH : p ∈ hz T V := mul_mem (inv_mem hbH) hx
    have hcomm : ∀ n : ℕ, (p ^ n)⁻¹ * (b⁻¹ * p ^ n * b) ∈ pCoreOf 2 (l1 T L V) := by
      intro n
      have h1 := Subgroup.commutator_mem_commutator (inv_mem (Subgroup.pow_mem _ hbp n))
        (inv_mem (hB'K hb))
      rw [commutatorElement_def, inv_inv, inv_inv] at h1
      have e : (p ^ n)⁻¹ * (b⁻¹ * p ^ n * b) = (p ^ n)⁻¹ * b⁻¹ * p ^ n * b := by group
      rw [e]
      exact hPK h1
    obtain ⟨ν, hν, e⟩ := exists_mul_pow_eq (hN1n hbH) (hN1n hpH) hcomm (orderOf x)
    have hx' : b * p = x := by rw [hpdef]; group
    rw [hx', pow_orderOf_eq_one] at e
    have hbm : b ^ orderOf x = 1 := by
      apply hBP _ (Subgroup.pow_mem _ hb _)
      have : b ^ orderOf x = (p ^ orderOf x * ν)⁻¹ := by
        rw [eq_inv_iff_mul_eq_one, ← mul_assoc]
        exact e.symm
      rw [this]
      exact inv_mem (mul_mem (Subgroup.pow_mem _ hbp _) (hN1P hν))
    have hpm : p ^ orderOf x ∈ pCoreOf 2 (l1 T L V) := by
      rw [hbm, one_mul] at e
      have : p ^ orderOf x = ν⁻¹ := eq_inv_of_mul_eq_one_left e.symm
      rw [this]
      exact inv_mem hν
    obtain ⟨k₂, hk₂⟩ := hP2 ⟨p, hbp⟩
    have hpe : p ^ 2 ^ k₂ ∈ pCoreOf 2 (l1 T L V) := by
      rw [show p ^ 2 ^ k₂ = 1 from by simpa using congrArg Subtype.val hk₂]
      exact one_mem _
    exact ⟨b, hb, p, mem_of_pow_odd_mem hxo hpm hpe, hx'.symm⟩
  have hK : ∀ k ∈ oTwoUpper (hz T V), ∃ b ∈ B', ∃ n ∈ pCoreOf 2 (l1 T L V), k = b * n := by
    intro k hk
    induction hk using Subgroup.closure_induction with
    | mem x hx => exact hP_N x hx.1 hx.2
    | one => exact ⟨1, one_mem _, 1, one_mem _, by group⟩
    | mul x y _ _ ihx ihy =>
      obtain ⟨b₁, hb₁, n₁, hn₁, rfl⟩ := ihx
      obtain ⟨b₂, hb₂, n₂, hn₂, rfl⟩ := ihy
      have h1 : b₂⁻¹ * n₁ * b₂ ∈ pCoreOf 2 (l1 T L V) := by
        have := (Subgroup.mem_normalizer_iff.mp (hN1n (inv_mem (hKH (hB'K hb₂)))) n₁).mp hn₁
        simpa using this
      exact ⟨b₁ * b₂, mul_mem hb₁ hb₂, b₂⁻¹ * n₁ * b₂ * n₂, mul_mem h1 hn₂, by group⟩
    | inv x _ ihx =>
      obtain ⟨b, hb, n, hn, rfl⟩ := ihx
      have h1 : b * n⁻¹ * b⁻¹ ∈ pCoreOf 2 (l1 T L V) :=
        (Subgroup.mem_normalizer_iff.mp (hN1n (hKH (hB'K hb))) _).mp (inv_mem hn)
      exact ⟨b⁻¹, inv_mem hb, b * n⁻¹ * b⁻¹, h1, by group⟩
  intro p hp
  obtain ⟨b, hb, n, hn, rfl⟩ := hK p (pCoreOf_le 2 _ hp)
  have hbP : b ∈ pCoreOf 2 (oTwoUpper (hz T V)) := by
    have : b = (b * n) * n⁻¹ := by group
    rw [this]
    exact mul_mem hp (inv_mem (hN1P hn))
  rw [hBP b hb hbP, one_mul]
  exact hn

end Ctx7153

end CFSG.Quasithin.H13.L32A
