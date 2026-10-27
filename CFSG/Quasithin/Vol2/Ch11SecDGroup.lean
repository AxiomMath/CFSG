module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.E1Util
public import CFSG.Quasithin.H13.Statements
public import CFSG.Quasithin.Vol2.Ch1Xi
public import CFSG.Quasithin.Vol2.Ch3Basic

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecD

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13
open scoped IsMulCommutative

variable {G : Type} [Group G]

theorem commutator_le_self' (H : Subgroup G) : ⁅H, H⁆ ≤ H :=
  Subgroup.commutator_le.mpr fun x hx y hy => by
    rw [commutatorElement_def]
    exact H.mul_mem (H.mul_mem (H.mul_mem hx hy) (H.inv_mem hx)) (H.inv_mem hy)

theorem conjClosure_perfect {A N : Subgroup G} (hA : ⁅A, A⁆ = A) :
    ⁅conjClosure A N, conjClosure A N⁆ = conjClosure A N := by
  refine le_antisymm (commutator_le_self' _) (conjClosure_le fun h hh a ha => ?_)
  set φ : G →* G := (MulAut.conj h).toMonoidHom with hφ
  have hmap : A.map φ ≤ conjClosure A N := by
    rintro _ ⟨b, hb, rfl⟩
    exact mem_conjClosure hh hb
  have hmem : h * a * h⁻¹ ∈ A.map φ := ⟨a, ha, by simp [hφ, MulAut.conj_apply]⟩
  rw [← hA, Subgroup.map_commutator] at hmem
  exact Subgroup.commutator_mono hmap hmap hmem

theorem mem_normalizer_of_conj {S : Subgroup G} {t : G} (h₁ : ∀ g ∈ S, t * g * t⁻¹ ∈ S)
    (h₂ : ∀ g ∈ S, t⁻¹ * g * t ∈ S) : t ∈ Subgroup.normalizer (S : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro g
  refine ⟨h₁ g, fun hg => ?_⟩
  have := h₂ _ hg
  simpa [mul_assoc] using this

theorem conj_mem_sectionCentralizer {X K : Subgroup G} {t g : G}
    (hX : t ∈ Subgroup.normalizer (X : Set G)) (hK : t ∈ Subgroup.normalizer (K : Set G))
    (hg : g ∈ sectionCentralizer X K) : t * g * t⁻¹ ∈ sectionCentralizer X K := by
  obtain ⟨hgX, hgK, hgc⟩ := hg
  refine ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hX hgX) (Subgroup.inv_mem _ hX),
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hK hgK) (Subgroup.inv_mem _ hK), fun x hx => ?_⟩
  have hx' : t⁻¹ * x * t ∈ X := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hX) x).mp hx
    simpa using this
  have h1 := (Subgroup.mem_normalizer_iff.mp hK _).mp (hgc _ hx')
  convert h1 using 1
  group

theorem mem_normalizer_sectionCentralizer {X K : Subgroup G} {t : G}
    (hX : t ∈ Subgroup.normalizer (X : Set G)) (hK : t ∈ Subgroup.normalizer (K : Set G)) :
    t ∈ Subgroup.normalizer (sectionCentralizer X K : Set G) := by
  refine mem_normalizer_of_conj (fun g hg => conj_mem_sectionCentralizer hX hK hg)
    (fun g hg => ?_)
  have := conj_mem_sectionCentralizer (Subgroup.inv_mem _ hX) (Subgroup.inv_mem _ hK) hg
  simpa using this

theorem commute_of_le_of_isMulCommutative {A B : Subgroup G} (hAB : A ≤ B)
    (hc : IsMulCommutative ↥(A.subgroupOf B)) {a b : G} (ha : a ∈ A) (hb : b ∈ A) :
    a * b = b * a := by
  have h := mul_comm (⟨⟨a, hAB ha⟩, Subgroup.mem_subgroupOf.mpr ha⟩ : ↥(A.subgroupOf B))
    ⟨⟨b, hAB hb⟩, Subgroup.mem_subgroupOf.mpr hb⟩
  exact congrArg (fun x : ↥(A.subgroupOf B) => ((x : ↥B) : G)) h

theorem oTwoUpper_le_of_le_sup' {X Y T : Subgroup G} (hXYT : X ≤ Y ⊔ T) (hT : IsPGroup 2 T)
    (hTY : T ≤ Subgroup.normalizer (Y : Set G)) : oTwoUpper X ≤ Y :=
  oTwoUpper_le_of_pow_mem fun _ hx => E1.exists_pow_mem_of_mem_sup hT hTY (hXYT hx)

theorem inH_of_le {T P W : Subgroup G} (hTP : T ≤ P) (hWP : W ≤ P) (hW : IsPGroup 2 W)
    (hW1 : W ≠ ⊥) (hPW : P ≤ Subgroup.normalizer (W : Set G)) : InH T P := by
  refine ⟨hTP, fun h => hW1 (le_bot_iff.mp ?_)⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [← h]
  exact CFSG.LieType.BorelTits.le_pCoreOf 2 hWP
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hWP).2 hPW) hW

variable [Finite G]

theorem exists_mem_centralizer_ne_one {T U : Subgroup G} (hT : IsPGroup 2 T) (hUT : U ≤ T)
    (hUn : T ≤ Subgroup.normalizer (U : Set G)) (hU : U ≠ ⊥) :
    ∃ z ∈ U, z ≠ 1 ∧ z ∈ Subgroup.centralizer (T : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent T := hT.isNilpotent
  have hnormal : (U.subgroupOf T).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hUn
  have hne : U.subgroupOf T ≠ ⊥ := by
    intro h
    apply hU
    rw [← Subgroup.map_subgroupOf_eq_of_le hUT, h, Subgroup.map_bot]
  obtain ⟨⟨y, hy⟩, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
  refine ⟨y, hy.1, fun h => hy1 (Subtype.ext (Subtype.ext h)), ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro t ht
  exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hy.2 ⟨t, ht⟩)

theorem exists_isHStar_le {T M : Subgroup G} (k : ℕ) :
    ∀ P : Subgroup G, Nat.card P = k → InH T P → ¬ P ≤ M → ∃ H, IsHStar T M H ∧ H ≤ P := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro P hk hP hPM
    by_cases hstar : IsHStar T M P
    · exact ⟨P, hstar, le_rfl⟩
    · have hex : ∃ Y : Subgroup G, InH T Y ∧ Y ≤ P ∧ ¬ Y ≤ M ∧ Y ≠ P := by
        by_contra hcon
        push Not at hcon
        exact hstar ⟨hP, hPM, fun Y hY hYP hYM => hcon Y hY hYP hYM⟩
      obtain ⟨Y, hY, hYP, hYM, hYne⟩ := hex
      have hlt : Nat.card Y < k := hk ▸ Subgroup.card_lt_of_lt (lt_of_le_of_ne hYP hYne)
      obtain ⟨H, hH, hHY⟩ := ih _ hlt Y rfl hY hYM
      exact ⟨H, hH, hHY.trans hYP⟩

end CFSG.Quasithin.Vol2.Ch11.SecD
