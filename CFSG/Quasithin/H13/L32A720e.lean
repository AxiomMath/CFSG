module

public import CFSG.Quasithin.H13.L32A720d
public import CFSG.Quasithin.H13.L32A720a

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

namespace Ctx7153

variable {G : Type} [Group G] [Finite G] {T L V H : Subgroup G} (E : Ctx7153 G T L V H)
  (hF : HypF98 T V L (fsuV1 T V) V (hz T V))
include E hF

omit hF in
theorem le_normalizer_centralizer : hz T V ≤ Subgroup.normalizer
    ((hz T V ⊓ Subgroup.centralizer (fsuU T V : Set G) : Subgroup G) : Set G) := by
  have hMod := stmtL32NModule_of_inputs E.h1332 E.h1334
  have hUN : hz T V ≤ Subgroup.normalizer (fsuU T V : Set G) := hz_le_normalizer_U E.S.hyp hMod
  intro g hg
  refine mem_normalizer_of_forall_conj
    (R := hz T V ⊓ Subgroup.centralizer (fsuU T V : Set G)) (fun x hx c hc => ?_) hg
  refine Subgroup.mem_inf.mpr ⟨mul_mem (mul_mem hx hc.1) (inv_mem hx),
    Subgroup.mem_centralizer_iff.mpr fun u hu => ?_⟩
  have hu' : x⁻¹ * u * x ∈ fsuU T V := by
    have := (Subgroup.mem_normalizer_iff.mp (hUN (inv_mem hx)) u).mp hu
    simpa using this
  have h1 := Subgroup.mem_centralizer_iff.mp hc.2 _ hu'
  calc u * (x * c * x⁻¹) = x * ((x⁻¹ * u * x) * c) * x⁻¹ := by group
    _ = x * (c * (x⁻¹ * u * x)) * x⁻¹ := by rw [h1]
    _ = x * c * x⁻¹ * u := by group

omit [Finite G] E hF in
theorem commutator_le_of_odd {Y N : Subgroup G} (hY : hz T V ≤ Subgroup.normalizer (Y : Set G))
    (hN : hz T V ≤ Subgroup.normalizer (N : Set G))
    (h : ∀ x ∈ hz T V, Odd (orderOf x) → ∀ y ∈ Y, y⁻¹ * (x * y * x⁻¹) ∈ N) :
    ⁅Y, oTwoUpper (hz T V)⁆ ≤ N := by
  have hK : oTwoUpper (hz T V) =
      Subgroup.closure {x | x ∈ hz T V ∧ Odd (orderOf x)} := rfl
  have key := forall_conj_mem_of_closure (S := {x | x ∈ hz T V ∧ Odd (orderOf x)})
    ((hK ▸ oTwoUpper_le _).trans hY) ((hK ▸ oTwoUpper_le _).trans hN)
    (fun x hx y hy => h x hx.1 hx.2 y hy)
  rw [Subgroup.commutator_le]
  intro y hy k hk
  have h1 := key k (hK ▸ hk) y⁻¹ (inv_mem hy)
  rw [commutatorElement_def]
  have e : y * k * y⁻¹ * k⁻¹ = y⁻¹⁻¹ * (k * y⁻¹ * k⁻¹) := by group
  rw [e]
  exact h1

omit [Finite G] E hF in
theorem commutator_le_self {Y : Subgroup G} (hY : hz T V ≤ Subgroup.normalizer (Y : Set G)) :
    ⁅Y, oTwoUpper (hz T V)⁆ ≤ Y := by
  rw [Subgroup.commutator_le]
  intro y hy k hk
  have h1 : k * y⁻¹ * k⁻¹ ∈ Y :=
    (Subgroup.mem_normalizer_iff.mp (hY (oTwoUpper_le _ hk)) _).mp (inv_mem hy)
  rw [commutatorElement_def, mul_assoc, mul_assoc, ← mul_assoc k]
  exact mul_mem hy h1

omit E hF in
theorem commutator_le_of_series {N Y₀ Y : Subgroup G} (hY₀Y : Y₀ ≤ Y)
    (hYQ : Y ≤ pCoreOf 2 (hz T V)) (hN : hz T V ≤ Subgroup.normalizer (N : Set G))
    (hY : hz T V ≤ Subgroup.normalizer (Y : Set G))
    (h1 : ⁅Y, oTwoUpper (hz T V)⁆ ≤ Y₀) (h2 : ⁅Y₀, oTwoUpper (hz T V)⁆ ≤ N) :
    ⁅Y, oTwoUpper (hz T V)⁆ ≤ N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine commutator_le_of_odd hY hN fun x hx hxo y hy => ?_
  have hxK : x ∈ oTwoUpper (hz T V) := mem_oTwoUpper_of_odd hx hxo
  have hYhz : Y ≤ hz T V := hYQ.trans (pCoreOf_le 2 _)
  refine conj_mem_of_odd hxo (pow_orderOf_eq_one x) (hYhz.trans hN) (hN hx) hY₀Y
    (fun a ha => ?_) (fun y hy => ?_) (fun a ha => ?_) y hy
  · obtain ⟨e, he⟩ := (pCoreOf_isPGroup 2 (hz T V)) ⟨a, hYQ (hY₀Y ha)⟩
    have he' : a ^ 2 ^ e = 1 := by simpa using congrArg Subtype.val he
    exact ⟨e, by rw [he']; exact one_mem _⟩
  · have := h1 (Subgroup.commutator_mem_commutator (inv_mem hy) hxK)
    rw [commutatorElement_def, inv_inv] at this
    simpa [mul_assoc] using this
  · have := h2 (Subgroup.commutator_mem_commutator (inv_mem ha) hxK)
    rw [commutatorElement_def, inv_inv] at this
    simpa [mul_assoc] using this

variable {γ γ' : F8.Geom T L (hz T V)} {g k : ↥((L ⊔ T) ⊔ hz T V)}
  (N : Not1471 T L V (hz T V) γ γ' g k)
include N

theorem cases_720 :
    ⁅hz T V ⊓ Subgroup.centralizer (fsuU T V : Set G), oTwoUpper (hz T V)⁆ ≤ fsuU T V ∨
      ∃ W₁ W₂ : Subgroup G, fsuU T V ≤ W₂ ∧ W₂ ≤ W₁ ∧
        W₁ ≤ pCoreOf 2 (oTwoUpper (hz T V)) ⊓ Subgroup.centralizer (fsuU T V : Set G) ∧
        hz T V ≤ Subgroup.normalizer (W₁ : Set G) ∧ hz T V ≤ Subgroup.normalizer (W₂ : Set G) ∧
        W₂.relIndex W₁ = 64 ∧
        (∀ x ∈ W₁, ∀ y ∈ W₁, x * y * x⁻¹ * y⁻¹ ∈ W₂ ∧ x ^ 2 ∈ W₂) ∧
        (∀ X : Subgroup G, W₂ ≤ X → X ≤ W₁ →
          oTwoUpper (hz T V) ≤ Subgroup.normalizer (X : Set G) → X = W₂ ∨ X = W₁) ∧
        (∀ x ∈ hz T V, (∀ w ∈ W₁, x * w * x⁻¹ * w⁻¹ ∈ W₂) → x ∈ pCoreOf 2 (hz T V)) ∧
        ⁅W₂, oTwoUpper (hz T V)⁆ ≤ fsuU T V ∧
        ⁅hz T V ⊓ Subgroup.centralizer (fsuU T V : Set G), oTwoUpper (hz T V)⁆ ≤ W₁ := by
  have hMod := stmtL32NModule_of_inputs E.h1332 E.h1334
  have hUN : hz T V ≤ Subgroup.normalizer (fsuU T V : Set G) := hz_le_normalizer_U E.S.hyp hMod
  have hCn := E.le_normalizer_centralizer
  have hCQ := E.centralizer_le_qh hF
  have hUP := E.u_le_p hF
  set C := hz T V ⊓ Subgroup.centralizer (fsuU T V : Set G) with hCdef
  set K := oTwoUpper (hz T V) with hKdef
  have hUC : fsuU T V ≤ C := by
    refine le_inf ?_ fun u hu => Subgroup.mem_centralizer_iff.mpr fun u' hu' =>
      fsuU_comm E.S.hyp hu' hu
    rw [E.fsuU_eq]
    exact (hF.toHypF91.conjClosure_Vp_le_pCoreOf).trans (pCoreOf_le 2 _)
  have hUK : ⁅fsuU T V, K⁆ ≤ fsuU T V := commutator_le_self hUN
  by_cases hcase : ⁅C, K⁆ ≤ fsuU T V
  · exact Or.inl hcase
  right
  obtain ⟨Y, ⟨hUY, hYC, hYn, hYK⟩, hmin⟩ := exists_minimal_subgroup (P := fun Y =>
    fsuU T V ≤ Y ∧ Y ≤ C ∧ hz T V ≤ Subgroup.normalizer (Y : Set G) ∧ ¬ ⁅Y, K⁆ ≤ fsuU T V)
    ⟨C, hUC, le_rfl, hCn, hcase⟩
  have hYQ : Y ≤ pCoreOf 2 (hz T V) := hYC.trans hCQ
  have hY2 : IsPGroup 2 ↥Y := (pCoreOf_isPGroup 2 (hz T V)).to_le hYQ
  have hUY' : fsuU T V < Y := lt_of_le_of_ne hUY fun e => hYK (e ▸ hUK)
  obtain ⟨Y₀, hUY₀, hY₀Y, hY₀n, hsec, hchief⟩ := exists_chief hUY' hY2 hYn hUN
  have hY₀K : ⁅Y₀, K⁆ ≤ fsuU T V := by
    by_contra hno
    exact hY₀Y.ne (hmin Y₀ ⟨hUY₀, hY₀Y.le.trans hYC, hY₀n, hno⟩ hY₀Y.le)
  have hnc : ¬ ⁅Y, K⁆ ≤ Y₀ := fun h =>
    hYK (commutator_le_of_series hY₀Y.le hYQ hUN hYn h hY₀K)
  have hYP : Y ≤ pCoreOf 2 (oTwoUpper (hz T V)) := by
    have hY'n : hz T V ≤ Subgroup.normalizer ((⁅Y, K⁆ ⊔ fsuU T V : Subgroup G) : Set G) :=
      fun x hx => mem_normalizer_sup_of (mem_normalizer_commutator (hYn hx)
        ((le_normalizer_oTwoUpper _) hx)) (hUN hx)
    have hY'Y : ⁅Y, K⁆ ⊔ fsuU T V ≤ Y := sup_le (commutator_le_self hYn) hUY
    have hY'P : ⁅Y, K⁆ ⊔ fsuU T V ≤ pCoreOf 2 (oTwoUpper (hz T V)) := by
      refine sup_le ?_ hUP
      rw [Subgroup.commutator_le]
      intro y hy x hx
      rw [commutatorElement_def]
      exact comm_mem_pCoreOf_oTwoUpper (hYQ hy) hx
    by_cases h1 : ⁅⁅Y, K⁆ ⊔ fsuU T V, K⁆ ≤ fsuU T V
    · exfalso
      exact hYK (commutator_le_of_series hY'Y hYQ hUN hYn le_sup_left h1)
    · have he := hmin _ ⟨le_sup_right, hY'Y.trans hYC, hY'n, h1⟩ hY'Y
      rw [← he]
      exact hY'P
  obtain ⟨h64, hirr, hfaith, h4⟩ := E.chief_faithful hF N hUY₀ hY₀Y hYC hY₀n hYn hsec hchief hnc
  obtain ⟨hVEα, hVEα4⟩ := E.relIndex_v_ealpha hF N
  have hVU : V ≤ fsuU T V := by
    rw [E.fsuU_eq]
    exact le_conjClosure V _
  set Eα := Quasithin.conjSub (k : G) (F8.Uγ V (hz T V) (g : G)) ⊓
    Subgroup.centralizer (fsuU T V : Set G) with hEαdef
  have hEαY : Eα ≤ Y := by
    have h2 : Y₀.relIndex (Eα ⊓ Y) ≤ V.relIndex (Eα ⊓ Y) :=
      Subgroup.relIndex_le_of_le_left (hVU.trans hUY₀) (by
        rw [Subgroup.relIndex]
        exact Subgroup.index_ne_zero_of_finite)
    have h3 : V.relIndex (Eα ⊓ Y) ≤ V.relIndex Eα :=
      Subgroup.relIndex_le_of_le_right inf_le_left (by
        rw [Subgroup.relIndex]
        exact Subgroup.index_ne_zero_of_finite)
    have hVEY : V ≤ Eα ⊓ Y := le_inf hVEα (hVU.trans hUY)
    have e1 := Subgroup.relIndex_mul_card V (Eα ⊓ Y)
    have e2 := Subgroup.relIndex_mul_card V Eα
    rw [inf_eq_left.mpr hVEY] at e1
    rw [inf_eq_left.mpr hVEα] at e2
    have hcard : Nat.card ↥Eα ≤ Nat.card ↥(Eα ⊓ Y) := by
      rw [← e1, ← e2]
      have : V.relIndex (Eα ⊓ Y) = V.relIndex Eα := by omega
      rw [this]
    have he := Subgroup.eq_of_le_of_card_ge inf_le_left hcard
    rw [← he]
    exact inf_le_right
  have hCK : ⁅C, K⁆ ≤ Y := by
    by_contra hno
    obtain ⟨Y', ⟨hYY', hY'C, hY'n, hY'K⟩, hmin'⟩ := exists_minimal_subgroup (P := fun Y' =>
      Y ≤ Y' ∧ Y' ≤ C ∧ hz T V ≤ Subgroup.normalizer (Y' : Set G) ∧ ¬ ⁅Y', K⁆ ≤ Y)
      ⟨C, hYC, le_rfl, hCn, hno⟩
    have hY'Q : Y' ≤ pCoreOf 2 (hz T V) := hY'C.trans hCQ
    have hY'2 : IsPGroup 2 ↥Y' := (pCoreOf_isPGroup 2 (hz T V)).to_le hY'Q
    have hYY'' : Y < Y' := lt_of_le_of_ne hYY' fun e => hY'K (e ▸ commutator_le_self hYn)
    obtain ⟨Y₀', hYY₀', hY₀'Y', hY₀'n, hsec', hchief'⟩ := exists_chief hYY'' hY'2 hY'n hYn
    have hY₀'K : ⁅Y₀', K⁆ ≤ Y := by
      by_contra hno'
      exact hY₀'Y'.ne (hmin' Y₀' ⟨hYY₀', hY₀'Y'.le.trans hY'C, hY₀'n, hno'⟩ hY₀'Y'.le)
    have hnc' : ¬ ⁅Y', K⁆ ≤ Y₀' := fun h =>
      hY'K (commutator_le_of_series hY₀'Y'.le hY'Q hYn hY'n h hY₀'K)
    obtain ⟨-, -, hfaith', -⟩ := E.chief_faithful hF N (hUY.trans hYY₀') hY₀'Y' hY'C hY₀'n
      hY'n hsec' hchief' hnc'
    have h2 := E.relIndex_uα hF N
    obtain ⟨s, hsA, hsQ, -⟩ := N.exists_mem_not_mem E.S.hyp hMod hF h2
    have hsA' : s ∈ Quasithin.conjSub (k : G) (F8.Uγ V (hz T V) (g : G)) :=
      (Not1471.uα_eq (g := g) (k := k) E.S.hyp hMod) ▸ hsA
    have hsH : s ∈ hz T V := E.ualpha_le_hz hF N hsA'
    apply hsQ
    refine hfaith' s hsH fun w hw => ?_
    have h3 := E.comm_mem_ealpha hF N w (hY'C hw) s hsA'
    have h4' : w⁻¹ * (s * w * s⁻¹) ∈ Y₀' := hYY₀' (hEαY h3)
    have h5 : w * (w⁻¹ * (s * w * s⁻¹)) * w⁻¹ ∈ Y₀' :=
      (Subgroup.mem_normalizer_iff.mp (hY₀'n (hY'C hw).1) _).mp h4'
    have e : s * w * s⁻¹ * w⁻¹ = w * (w⁻¹ * (s * w * s⁻¹)) * w⁻¹ := by group
    rw [e]
    exact h5
  exact ⟨Y, Y₀, hUY₀, hY₀Y.le, le_inf hYP (hYC.trans inf_le_right), hYn, hY₀n, h64, hsec.2,
    hirr, hfaith, hY₀K, hCK⟩

end Ctx7153

end CFSG.Quasithin.H13.L32A
