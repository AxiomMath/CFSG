module

public import CFSG.Quasithin.H13.L32NLem1444i
public import CFSG.Quasithin.H13.L32NLem1444j

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.LieType.BorelTits

namespace L1444CTL

open L1444

variable {G : Type} [Group G] [Finite G]

theorem normalizer_le_of_unique {X M P : Subgroup G}
    (huniq : ∀ M' : Subgroup G, quasithinIsMaxTwoLocal M' → X ≤ M' → M' = M) (hP1 : P ≠ ⊥)
    (hP2 : IsPGroup 2 P) (hXP : X ≤ Subgroup.normalizer (P : Set G)) :
    Subgroup.normalizer (P : Set G) ≤ M := by
  obtain ⟨M', hM', hle⟩ := CFSG.Quasithin.exists_maxTwoLocal_ge ⟨P, hP1, hP2, rfl⟩
  rw [← huniq M' hM' (hXP.trans hle)]
  exact hle

section Setup

variable {T L V V₂ : Subgroup G} {g : G} {D : HatModelU (fsuU T V)} {Q₁ Q₂ : Subgroup G}
  (S : Setup4 G T L V V₂ g D Q₁ Q₂)
include S

theorem centralizer_L_le_T : Subgroup.centralizer (L : Set G) ≤ T :=
  (Subgroup.centralizer_le S.U_le_L).trans S.cent_le_T

theorem centralizer_L_le_cent :
    Subgroup.centralizer (L : Set G) ≤ Subgroup.centralizer (fsuU T V : Set G) :=
  Subgroup.centralizer_le S.U_le_L

omit [Finite G] S in
theorem mem_normalizer_of_mem {n : G} (hnL : n ∈ Subgroup.normalizer (L : Set G))
    (hnT : n ∈ Subgroup.normalizer (T : Set G)) :
    n ∈ Subgroup.normalizer ((T ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro d
  have hc : ∀ e : G, e ∈ Subgroup.centralizer (L : Set G) →
      n * e * n⁻¹ ∈ Subgroup.centralizer (L : Set G) := fun e he => by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have hl' : n⁻¹ * l * n ∈ L := by
      have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer _).inv_mem hnL) l).mp hl
      simpa using this
    have h1 := Subgroup.mem_centralizer_iff.mp he _ hl'
    calc l * (n * e * n⁻¹) = n * ((n⁻¹ * l * n) * e) * n⁻¹ := by group
      _ = n * (e * (n⁻¹ * l * n)) * n⁻¹ := by rw [h1]
      _ = n * e * n⁻¹ * l := by group
  have hc' : ∀ e : G, n * e * n⁻¹ ∈ Subgroup.centralizer (L : Set G) →
      e ∈ Subgroup.centralizer (L : Set G) := fun e he => by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have hl' : n * l * n⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hnL l).mp hl
    have h1 := Subgroup.mem_centralizer_iff.mp he _ hl'
    calc l * e = n⁻¹ * ((n * l * n⁻¹) * (n * e * n⁻¹)) * n := by group
      _ = n⁻¹ * ((n * e * n⁻¹) * (n * l * n⁻¹)) * n := by rw [h1]
      _ = e * l := by group
  constructor
  · rintro ⟨hdT, hdC⟩
    exact ⟨(Subgroup.mem_normalizer_iff.mp hnT d).mp hdT, hc d hdC⟩
  · rintro ⟨hdT, hdC⟩
    exact ⟨(Subgroup.mem_normalizer_iff.mp hnT d).mpr hdT, hc' d hdC⟩

theorem T_le_normalizer :
    T ≤ Subgroup.normalizer ((T ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) : Set G) :=
  fun _ ht => mem_normalizer_of_mem (S.TL ht) (Subgroup.le_normalizer ht)

theorem M_le_normalizer : Subgroup.normalizer (L : Set G) ≤
    Subgroup.normalizer ((T ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) : Set G) := by
  rw [inf_eq_right.mpr (centralizer_L_le_T S)]
  exact normalizer_le_normalizer_centralizer'' (L : Subgroup G)

theorem Q_le_normalizer : pCoreOf 2 (l32nH T V) ≤
    Subgroup.normalizer ((T ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) : Set G) :=
  S.QT.trans (T_le_normalizer S)

theorem LT_le_normalizer : L ⊔ T ≤
    Subgroup.normalizer ((T ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) : Set G) :=
  sup_le (le_sup_left.trans ((sup_le Subgroup.le_normalizer S.TL).trans (M_le_normalizer S)))
    (T_le_normalizer S)

theorem normalizer_le_M (h13322 : Stmt13_3_2_two) {P : Subgroup G} (hP1 : P ≠ ⊥)
    (hP2 : IsPGroup 2 P) (hLT : L ⊔ T ≤ Subgroup.normalizer (P : Set G)) :
    Subgroup.normalizer (P : Set G) ≤ Subgroup.normalizer (L : Set G) := by
  obtain ⟨-, -, -, huniq⟩ := h13322 G T L S.hyp.hyp.h13 L S.hyp.hyp.h13.faithful
  exact normalizer_le_of_unique huniq hP1 hP2 hLT

theorem isPGroup_D : IsPGroup 2 ↥(T ⊓ Subgroup.centralizer (L : Set G)) :=
  S.hyp.fsu.sylow.1.to_le inf_le_left

theorem false_of_H_le (h12213 : Stmt12_2_13) (h13322 : Stmt13_3_2_two) (hV : StmtL32NModule)
    (hD : T ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥)
    (hH : l32nH T V ≤
      Subgroup.normalizer ((T ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) : Set G)) :
    False :=
  lemma12_8_3_four h12213 (S.hyp.hyp1281One h13322 hV) (S.hyp.isTSub_fsuV1 hV)
    (hH.trans (normalizer_le_M S h13322 hD (isPGroup_D S) (LT_le_normalizer S)))

theorem mem_normalizer_of_inv {x b : G} (hx : x ∈ CFSG.conjugate (l32nW T V V₂) g)
    (hb : b ∈ oTwoUpper (l32nH T V)) (hxb : x * b * x⁻¹ * b ∈ pCoreOf 2 (l32nH T V)) :
    b ∈ Subgroup.normalizer ((T ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) : Set G) := by
  have hbH : b ∈ l32nH T V := oTwoUpper_le _ hb
  have hbN : b ∈ Subgroup.normalizer (fsuU T V : Set G) :=
    L14332.l32nH_le_normalizer_fsuU T V hbH
  have hxC : ∀ d ∈ Subgroup.centralizer (fsuU T V : Set G), x * d = d * x := fun d hd =>
    S.comm_TL hd (Subgroup.mem_sup_right hx)
  have haC : x * b * x⁻¹ * b⁻¹ ∈ Subgroup.centralizer
      ((T ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    have hdC := centralizer_L_le_cent S hd.2
    have hd' : b⁻¹ * d * b ∈ Subgroup.centralizer (fsuU T V : Set G) := by
      have := (Subgroup.mem_normalizer_iff.mp
        (normalizer_le_normalizer_centralizer'' _ ((Subgroup.normalizer _).inv_mem hbN)) d).mp hdC
      simpa using this
    have h1 := hxC _ hd'
    have h2 := hxC _ hdC
    have h1' : x⁻¹ * (b⁻¹ * d * b) = (b⁻¹ * d * b) * x⁻¹ := by
      calc x⁻¹ * (b⁻¹ * d * b) = x⁻¹ * ((b⁻¹ * d * b) * x) * x⁻¹ := by group
        _ = x⁻¹ * (x * (b⁻¹ * d * b)) * x⁻¹ := by rw [h1]
        _ = (b⁻¹ * d * b) * x⁻¹ := by group
    symm
    calc (x * b * x⁻¹ * b⁻¹) * d = x * b * (x⁻¹ * (b⁻¹ * d * b)) * b⁻¹ := by group
      _ = x * b * ((b⁻¹ * d * b) * x⁻¹) * b⁻¹ := by rw [h1']
      _ = (x * d) * b * x⁻¹ * b⁻¹ := by group
      _ = (d * x) * b * x⁻¹ * b⁻¹ := by rw [h2]
      _ = d * (x * b * x⁻¹ * b⁻¹) := by group
  have hcube := S.cube_mem_Q_of_mem_K hb
  have heq : b = (b ^ 3 * (x * b * x⁻¹ * b)⁻¹) * (x * b * x⁻¹ * b⁻¹) := by group
  rw [heq]
  refine Subgroup.mul_mem _ ?_ (Subgroup.centralizer_le_normalizer _ haC)
  exact Q_le_normalizer S (Subgroup.mul_mem _ hcube (Subgroup.inv_mem _ hxb))

theorem H_le_of_K_le (hV : StmtL32NModule)
    (hK : oTwoUpper (l32nH T V) ≤
      Subgroup.normalizer ((T ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) : Set G)) :
    l32nH T V ≤
      Subgroup.normalizer ((T ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) : Set G) := by
  rw [← C1Pack12.oTwoUpper_sup_eq_of_sylow (S.hyp.isSylowTwoOf_l32nH hV)]
  exact sup_le hK (T_le_normalizer S)

theorem false_of_normalizes (h12213 : Stmt12_2_13) (h13322 : Stmt13_3_2_two)
    (hV : StmtL32NModule) (hD : T ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥) {x : G}
    (hxW : x ∈ CFSG.conjugate (l32nW T V V₂) g) (hxQ : x ∉ pCoreOf 2 (l32nH T V))
    (hx₁ : x ∈ Subgroup.normalizer (Q₁ : Set G)) (hx₂ : x ∈ Subgroup.normalizer (Q₂ : Set G)) :
    False :=
  false_of_H_le S h12213 h13322 hV hD (H_le_of_K_le S hV fun _ hk =>
    mem_normalizer_of_inv S hxW hk (S.inv_of_normalizes hxW hxQ hx₁ hx₂ hk))

end Setup

end L1444CTL

end CFSG.Quasithin.H13
