module

public import CFSG.Milestones.ASVolI.C121.Ctx
public import CFSG.CGT.PushingUpLit.SubnormalTwoGroup
public import CFSG.Milestones.ASVolI.C121.Nat

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC CFSG.LieType.BorelTits
open scoped MatrixGroups

structure burnsideC121_NatD {Ω : Type} [Group Ω] (Y W : Subgroup Ω) (n : ℕ) (F : Type) [Field F]
    [Fintype F] where
  card : Fintype.card F = 2 ^ n
  one_le : 1 ≤ n
  α : ↥Y →* SL(2, F)
  αk : α.ker = (pCoreOf 2 Y).subgroupOf Y
  αr : α.range = commutator SL(2, F)
  β : ↥W →* Multiplicative (Fin 2 → F)
  βs : Function.Surjective β
  βk : β.ker = (W ⊓ Subgroup.centralizer (Y : Set Ω)).subgroupOf W
  βe : ∀ (k : ↥Y) (u v : ↥W), (v : Ω) = k * u * k⁻¹ →
    Multiplicative.toAdd (β v) =
      (α k : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (β u))

theorem burnsideC121_exists_natD {Ω : Type} [Group Ω] {X R S Y W : Subgroup Ω}
    (hY : InYSet X R S Y) (hW : IsR2Max ((S ⊔ pCoreOf 2 X) ⊔ Y) W) :
    ∃ (n : ℕ) (F : Type) (_ : Field F) (_ : Fintype F), Nonempty (burnsideC121_NatD Y W n F) := by
  obtain ⟨W', hW', n, hn, F, iF, iFin, hF, α, hαk, hαr, β, hβs, hβk, hβe⟩ := hY.natural
  have hWW : W' = W := le_antisymm (hW.2 W' hW'.1) (hW'.2 W hW.1)
  subst hWW
  exact ⟨n, F, iF, iFin, ⟨⟨hF, hn, α, hαk, hαr, β, hβs, hβk, hβe⟩⟩⟩

namespace burnsideC121_YCtx

variable {Ω : Type} [Group Ω] [Finite Ω] {X R T Y W : Subgroup Ω}
  (c : burnsideC121_YCtx X R T Y W) {n : ℕ} {F : Type} [Field F] [Fintype F]
  (D : burnsideC121_NatD Y W n F)

include c

theorem noTwoQuotient : CFSG.CGT.PushingUpLit.SubTwo.NoTwoQuotient Y := by
  intro N hNY _ h2
  apply le_antisymm hNY
  rw [c.hY.perf]
  exact oTwoUpper_le_of_pow_mem h2

theorem eq_of_mul_pCore {N : Subgroup Ω} (hNY : N ≤ Y)
    (hYN : Y ≤ Subgroup.normalizer (N : Set Ω))
    (h : ∀ y ∈ Y, ∃ m ∈ N, ∃ o ∈ pCoreOf 2 Y, y = m * o) : N = Y := by
  refine c.noTwoQuotient N hNY hYN fun y hy => ?_
  exact C124.exists_pow_mem_of_prod hNY hYN ((pCoreOf_le 2 Y)) (pCoreOf_isPGroup 2 Y) hy (h y hy)

include D

theorem normal_le_or_eq {N : Subgroup Ω} (hNY : N ≤ Y)
    (hYN : Y ≤ Subgroup.normalizer (N : Set Ω)) : N ≤ pCoreOf 2 Y ∨ N = Y := by
  rcases burnsideC121_normal_dichotomy D.one_le D.card D.α D.αk D.αr hNY hYN with h | h
  · exact Or.inl h
  · exact Or.inr (c.eq_of_mul_pCore hNY hYN h)

theorem inf_centralizer_W : Y ⊓ Subgroup.centralizer (W : Set Ω) = pCoreOf 2 Y :=
  le_antisymm (burnsideC121_inf_centralizer_le D.α D.β D.αk D.βs D.βe)
    (le_inf (pCoreOf_le 2 Y) c.pCore_Y_le_centralizer)

theorem not_le_pCore : ¬ Y ≤ pCoreOf 2 Y := by
  intro h
  have hbot : D.α.range = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨y, rfl⟩
    have hy : y ∈ D.α.ker := by
      rw [D.αk, Subgroup.mem_subgroupOf]
      exact h y.2
    exact hy
  have hcomm : commutator SL(2, F) ≠ ⊥ := by
    by_cases hn2 : 2 ≤ n
    · have h4 : 4 ≤ Nat.card F := by
        rw [Nat.card_eq_fintype_card, D.card]
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have : CharP F 2 := charP_of_card_eq_prime_pow D.card
      have : IsSimpleGroup SL(2, F) := CFSG.Quasithin.C126.Nat.isSimpleGroup_sl2 h4
      rw [CFSG.Quasithin.C126.Nat.commutator_sl2_eq_top h4]
      exact top_ne_bot
    · have hn1 : n = 1 := by have := D.one_le; omega
      have h3 := burnsideC121_card_commutator_sl2_two (F := F) (by rw [D.card, hn1]; rfl)
      intro hb
      rw [hb, Subgroup.card_bot] at h3
      omega
  exact hcomm (D.αr ▸ hbot)

theorem not_le_centralizer_W : ¬ Y ≤ Subgroup.centralizer (W : Set Ω) := by
  intro h
  apply c.not_le_pCore D
  rw [← c.inf_centralizer_W D]
  exact le_inf le_rfl h

theorem inf_centralizer_H :
    burnsideC121_H X T Y ⊓ Subgroup.centralizer (W : Set Ω) =
      pCoreOf 2 (burnsideC121_H X T Y) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := burnsideC121_H X T Y with hH
  set C := H ⊓ Subgroup.centralizer (W : Set Ω) with hC
  have hCp : IsPGroup 2 C := by
    rintro ⟨x, hx⟩
    obtain ⟨k, hk⟩ := C124.exists_pow_mem_of_prod c.Y_le_H c.H_le_normalizer c.P_le_H c.P_pGroup
      hx.1 (c.H_prod x hx.1)
    have hkC : x ^ 2 ^ k ∈ Y ⊓ Subgroup.centralizer (W : Set Ω) :=
      ⟨hk, Subgroup.pow_mem _ hx.2 _⟩
    rw [c.inf_centralizer_W D] at hkC
    obtain ⟨m, hm⟩ := (pCoreOf_isPGroup 2 Y) ⟨_, hkC⟩
    refine ⟨k + m, Subtype.ext ?_⟩
    have hm' : (x ^ 2 ^ k) ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
    simp only [Subgroup.coe_pow, OneMemClass.coe_one]
    rw [pow_add, pow_mul, hm']
  have hCn : H ≤ Subgroup.normalizer (C : Set Ω) := by
    intro h hh
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer hh,
        B2F.normalizer_le_normalizer_centralizer W (c.H_le_normalizer_W hh)⟩
  apply le_antisymm (le_pCoreOf_of_le_normalizer 2 inf_le_left hCn hCp)
  exact le_inf (pCoreOf_le 2 H) c.pCore_H_le_centralizer

theorem inf_centralizer_P :
    burnsideC121_P X R T Y ⊓ Subgroup.centralizer (W : Set Ω) =
      pCoreOf 2 (burnsideC121_H X T Y) := by
  apply le_antisymm
  · rw [← c.inf_centralizer_H D]
    exact inf_le_inf_right _ c.P_le_H
  · exact le_inf c.pCore_H_le_P c.pCore_H_le_centralizer

theorem le_normalizer_S_of_thompsonJ_le
    (hJ : thompsonJ (burnsideC121_P X R T Y) ≤ Subgroup.centralizer (W : Set Ω)) :
    Y ≤ Subgroup.normalizer (baum T : Set Ω) := by
  have hWP : W ≤ burnsideC121_P X R T Y := c.W_le_pCore_H.trans c.pCore_H_le_P
  have hJP : thompsonJ (burnsideC121_P X R T Y) ≤
      burnsideC121_P X R T Y ⊓ Subgroup.centralizer (W : Set Ω) :=
    le_inf (B6.thompsonJ_le _) hJ
  have hb := baum_eq_baum_centralizer c.W_elem hWP hJP
  rw [c.inf_centralizer_P D, c.baum_P] at hb
  rw [hb]
  exact c.Y_le_H.trans ((le_normalizer_pCoreOf 2 _).trans
    (normalizer_le_normalizer_baum (pCoreOf 2 (burnsideC121_H X T Y))))

omit D in
theorem thompsonJ_le_pCore_H
    (hJ : ⁅Y, thompsonJ (burnsideC121_P X R T Y)⁆ ≤ pCoreOf 2 Y) :
    thompsonJ (burnsideC121_P X R T Y) ≤ pCoreOf 2 (burnsideC121_H X T Y) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P := burnsideC121_P X R T Y with hP
  set D₀ := pCoreOf 2 Y ⊔ thompsonJ P with hD₀
  have hD₀P : D₀ ≤ P := sup_le c.pCore_Y_le_P (B6.thompsonJ_le P)
  have hD₀H : D₀ ≤ burnsideC121_H X T Y := hD₀P.trans c.P_le_H
  have hD₀p : IsPGroup 2 D₀ := c.P_pGroup.to_le hD₀P
  have hY1 : ∀ y ∈ Y, ∀ x ∈ D₀, y * x * y⁻¹ ∈ D₀ := by
    intro y hy
    refine C124.conj_mem_sup (fun x hx => ?_) (fun j hj => ?_)
    · exact Subgroup.mem_sup_left
        ((Subgroup.mem_normalizer_iff.1 (le_normalizer_pCoreOf 2 Y hy) x).1 hx)
    · have hc : y * j * y⁻¹ * j⁻¹ ∈ pCoreOf 2 Y :=
        hJ (Subgroup.commutator_mem_commutator hy hj)
      have e : y * j * y⁻¹ = (y * j * y⁻¹ * j⁻¹) * j := by group
      rw [e]
      exact D₀.mul_mem (Subgroup.mem_sup_left hc) (Subgroup.mem_sup_right hj)
  have hP1 : ∀ p ∈ P, ∀ x ∈ D₀, p * x * p⁻¹ ∈ D₀ := by
    intro p hp
    refine C124.conj_mem_sup (fun x hx => ?_) (fun j hj => ?_)
    · exact Subgroup.mem_sup_left
        ((Subgroup.mem_normalizer_iff.1 (normalizer_le_normalizer_pCoreOf 2 Y
          (c.P_le_normalizer hp)) x).1 hx)
    · exact Subgroup.mem_sup_right
        ((Subgroup.mem_normalizer_iff.1 (B6.le_normalizer_thompsonJ P hp) j).1 hj)
  have hHN : burnsideC121_H X T Y ≤ Subgroup.normalizer (D₀ : Set Ω) := by
    intro x hx
    obtain ⟨y, hy, p, hp, rfl⟩ := c.H_prod x hx
    refine Subgroup.mul_mem _ ?_ ?_
    · exact C124.mem_normalizer_of_conj (hY1 y hy) (by simpa using hY1 y⁻¹ (Y.inv_mem hy))
    · exact C124.mem_normalizer_of_conj (hP1 p hp) (by simpa using hP1 p⁻¹ (P.inv_mem hp))
  exact le_sup_right.trans (le_pCoreOf_of_le_normalizer 2 hD₀H hHN hD₀p)

theorem commutator_thompsonJ_eq (hYS : ¬ Y ≤ Subgroup.normalizer (baum T : Set Ω)) :
    ⁅Y, thompsonJ R⁆ = Y := by
  have hJY : thompsonJ R ≤ Subgroup.normalizer (Y : Set Ω) :=
    (c.thompsonJ_R_le_S.trans c.S_le_P).trans c.P_le_normalizer
  have hNY : ⁅Y, thompsonJ R⁆ ≤ Y := Subgroup.le_normalizer_iff_commutator_le_left.mp hJY
  have hYN : Y ≤ Subgroup.normalizer ((⁅Y, thompsonJ R⁆ : Subgroup Ω) : Set Ω) :=
    Subgroup.normalizer_commutator_ge_left Y (thompsonJ R)
  rcases c.normal_le_or_eq D hNY hYN with h | h
  · exfalso
    apply hYS
    apply c.le_normalizer_S_of_thompsonJ_le D
    rw [c.thompsonJ_P]
    have h1 := c.thompsonJ_le_pCore_H (by rw [c.thompsonJ_P]; exact h)
    rw [c.thompsonJ_P] at h1
    exact h1.trans c.pCore_H_le_centralizer
  · exact h

theorem commutator_W_thompsonJ_ne_bot (hYS : ¬ Y ≤ Subgroup.normalizer (baum T : Set Ω)) :
    ⁅W, thompsonJ (burnsideC121_P X R T Y)⁆ ≠ ⊥ := by
  intro h
  apply hYS
  apply c.le_normalizer_S_of_thompsonJ_le D
  rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer] at h
  exact h

end burnsideC121_YCtx

end CFSG.ASVolI
