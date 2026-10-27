module

public import CFSG.Quasithin.Vol2.Ch4Sec3L4311C135
public import CFSG.Quasithin.Vol2.Ch4Sec3L4310Mod
public import CFSG.Quasithin.Vol2.Ch4Sec3L4311Set

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Open hiding StatedSL StatedSp
open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.A4
open CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] [Finite G]

theorem eq_bot_of_inf_eq_bot_of_charTwo {X S N : Subgroup G} (hchar : CharTwo X)
    (hS : IsSylowTwoOf S X) (hNX : N ≤ X) (hN : X ≤ Subgroup.normalizer (N : Set G))
    (hNS : N ⊓ S = ⊥) : N = ⊥ := by
  have hOS : pCoreOf 2 X ≤ S := pCoreOf_two_le_of_isSylowTwoOf hS
  have hNC : N ≤ X ⊓ Subgroup.centralizer (pCoreOf 2 X : Set G) := by
    intro x hx
    refine ⟨hNX hx, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
    have hyX : y ∈ X := pCoreOf_le 2 _ hy
    have h1 : x * y * x⁻¹ * y⁻¹ ∈ N := by
      have := (Subgroup.mem_normalizer_iff.mp (hN hyX) x⁻¹).mp (N.inv_mem hx)
      have e : x * y * x⁻¹ * y⁻¹ = x * (y * x⁻¹ * y⁻¹) := by group
      rw [e]
      exact N.mul_mem hx this
    have h2 : x * y * x⁻¹ * y⁻¹ ∈ S := by
      apply hOS
      have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 _ (hNX hx)) y).mp hy
      exact (pCoreOf 2 X).mul_mem this ((pCoreOf 2 X).inv_mem hy)
    have h3 : x * y * x⁻¹ * y⁻¹ = 1 := by
      rw [← Subgroup.mem_bot, ← hNS]
      exact ⟨h1, h2⟩
    calc y * x = (x * y * x⁻¹ * y⁻¹)⁻¹ * (x * y) := by group
      _ = x * y := by rw [h3, inv_one, one_mul]
  have hNS' : N ≤ S := hNC.trans (hchar.trans hOS)
  rw [eq_bot_iff]
  intro x hx
  rw [← hNS]
  exact ⟨hx, hNS' hx⟩

theorem c134Q_sup_eq {K X : Subgroup G} (hperf : ⁅K, K⁆ = K)
    (hX : X ≤ Subgroup.normalizer (K : Set G)) : c134Q (K ⊔ X) K = ⁅pCoreOf 2 K, K⁆ := by
  have hKXN : K ⊔ X ≤ Subgroup.normalizer (K : Set G) :=
    _root_.sup_le (fun x hx => Subgroup.le_normalizer hx) hX
  have hUO : pCoreOf 2 K ≤ pCoreOf 2 (K ⊔ X) :=
    le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 K).trans le_sup_left)
      (hKXN.trans (normalizer_le_normalizer_pCoreOf 2 K)) (pCoreOf_isPGroup 2 K)
  refine le_antisymm ?_ (Subgroup.commutator_mono hUO le_rfl)
  have h1 := (commutator_le_pCoreOf_of_le hperf hX le_rfl).1
  have hON : pCoreOf 2 (K ⊔ X) ≤ Subgroup.normalizer (K : Set G) :=
    (pCoreOf_le 2 _).trans hKXN
  show ⁅pCoreOf 2 (K ⊔ X), K⁆ ≤ ⁅pCoreOf 2 K, K⁆
  rw [commutator_eq_commutator_commutator_of_perfect' hperf hON]
  exact Subgroup.commutator_mono h1 le_rfl

namespace Setting4311

variable {T M L : Subgroup G} {n : ℕ} {I H K : Subgroup G} {t : G} {m : ℕ} {F : Type} [Field F]
  [Fintype F] {α : ↥K →* ↥(StatedSL 3 F)} {β : ↥(u4311 I K) →* Multiplicative (Fin 3 → F)}
  {W' : Submodule F (Fin 3 → F)} {ZS K₂ R₂ : Subgroup G} {μ : Fˣ} {y : G}
variable (s : Setting4311 G T M L n I H K t m F α β W' ZS K₂ R₂ μ y)
include s

theorem c134Q_sup_S_eq : c134Q (K ⊔ T ⊓ H) K = q4311 I K := by
  have hperf : ⁅K, K⁆ = K := perfect_of_mem_cComp s.sk.cComp
  have hSK : T ⊓ H ≤ Subgroup.normalizer (K : Set G) := s.sk.S_le_normalizer
  have hRK : pCoreOf 2 I ≤ Subgroup.normalizer (K : Set G) := s.sk.base.pCoreOf_le_S.trans hSK
  rw [q4311, c134Q_sup_eq hperf hSK, c134Q_sup_eq hperf hRK]

theorem isSylowTwoOf_S_sup (hR : L2RankOneSylowFact) (hC : LemmaC53C56Six) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (h39 : A39ForSQTK) : IsSylowTwoOf (T ⊓ H) (K ⊔ T ⊓ H) := by
  have hSsylH := s.sk.base.isSylowTwoOf_S_H hR hC h37 h38 h39
  have hKSH : K ⊔ T ⊓ H ≤ H := _root_.sup_le (le_of_mem_cComp s.sk.cComp) inf_le_right
  refine ⟨le_sup_right, hSsylH.2.1, fun h2 => hSsylH.2.2 ?_⟩
  have h1 := Subgroup.relIndex_mul_relIndex (T ⊓ H) (K ⊔ T ⊓ H) H le_sup_right hKSH
  exact h2.trans (Dvd.intro _ h1)

theorem sup_inf_centralizer_eq_bot (hR : L2RankOneSylowFact) (hC : LemmaC53C56Six)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) :
    (K ⊔ T ⊓ H) ⊓ Subgroup.centralizer (K : Set G) = ⊥ := by
  have hSK : T ⊓ H ≤ Subgroup.normalizer (K : Set G) := s.sk.S_le_normalizer
  have hsyl := s.isSylowTwoOf_S_sup hR hC h37 h38 h39
  have hchKS : CharTwo (K ⊔ T ⊓ H) := charTwo_sup_of_isPGroup s.charTwo hsyl.2.1 hSK
  have hKSN : K ⊔ T ⊓ H ≤ Subgroup.normalizer (K : Set G) :=
    _root_.sup_le (fun x hx => Subgroup.le_normalizer hx) hSK
  refine eq_bot_of_inf_eq_bot_of_charTwo hchKS hsyl inf_le_left (fun x hx =>
    mem_normalizer_inf (Subgroup.le_normalizer hx)
      (mem_normalizer_centralizer_of_mem (hKSN hx))) ?_
  rw [eq_bot_iff, ← s.cent]
  exact fun x hx => ⟨hx.2, hx.1.2⟩

theorem isSumOfNaturalModulesVia_u : IsSumOfNaturalModulesVia K (u4311 I K) ⊥ α false 1 := by
  let β₁ : ↥(u4311 I K) →* Multiplicative (Fin 1 → Fin 3 → F) :=
    { toFun := fun u => Multiplicative.ofAdd fun _ => Multiplicative.toAdd (β u)
      map_one' := by
        apply Multiplicative.toAdd.injective
        funext i
        simp
      map_mul' := fun u v => by
        apply Multiplicative.toAdd.injective
        funext i
        simp }
  have hβ₁ : ∀ (u : ↥(u4311 I K)) (i : Fin 1),
      Multiplicative.toAdd (β₁ u) i = Multiplicative.toAdd (β u) := fun _ _ => rfl
  refine ⟨s.K_U, bot_le, β₁, fun w => ?_, ?_, fun a u v huv i => ?_⟩
  · obtain ⟨u, hu⟩ := s.β_bij.2 (Multiplicative.ofAdd (Multiplicative.toAdd w 0))
    refine ⟨u, ?_⟩
    apply Multiplicative.toAdd.injective
    funext i
    rw [Fin.fin_one_eq_zero i, hβ₁, hu, toAdd_ofAdd]
  · rw [Subgroup.bot_subgroupOf]
    ext u
    rw [MonoidHom.mem_ker, Subgroup.mem_bot]
    constructor
    · intro h
      apply s.β_bij.1
      rw [map_one]
      apply Multiplicative.toAdd.injective
      have h1 := congrFun (congrArg Multiplicative.toAdd h) 0
      rw [hβ₁] at h1
      rw [h1]
      rfl
    · rintro rfl
      exact map_one β₁
  · rw [hβ₁, hβ₁, s.β_act a u v huv]
    simp [moduleAct]

theorem pCoreOf_sup_eq (h135 : AsC135Three) (hR : L2RankOneSylowFact) (hC : LemmaC53C56Six)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) :
    pCoreOf 2 (K ⊔ T ⊓ H) = q4311 I K := by
  have hSK : T ⊓ H ≤ Subgroup.normalizer (K : Set G) := s.sk.S_le_normalizer
  have hMS := s.sk.isMSPair_sup hR hC h37 h38 h39 s.charTwo s.c3
  have hKSN : K ⊔ T ⊓ H ≤ Subgroup.normalizer (K : Set G) :=
    _root_.sup_le (fun x hx => Subgroup.le_normalizer hx) hSK
  have hQ := s.c134Q_sup_S_eq
  have hU : IsSumOfNaturalModulesVia K (centerOf (c134Q (K ⊔ T ⊓ H) K)) ⊥ α false 1 := by
    rw [hQ]
    exact s.isSumOfNaturalModulesVia_u
  have hD : IsSumOfNaturalModulesVia K (c134Q (K ⊔ T ⊓ H) K)
      (centerOf (c134Q (K ⊔ T ⊓ H) K)) α true 2 := by
    rw [hQ]
    exact s.dualQ
  rw [← hQ]
  exact h135 G (K ⊔ T ⊓ H) (T ⊓ H) K m F α hMS (mem_cComp_sup s.sk.cComp hSK)
    (Subgroup.coe_mul_of_right_le_normalizer_left K (T ⊓ H) hSK) hKSN s.two_le s.card_F s.modO2
    (s.sup_inf_centralizer_eq_bot hR hC h37 h38 h39) hU hD

theorem pCoreOf_K_eq (h135 : AsC135Three) (hR : L2RankOneSylowFact) (hC : LemmaC53C56Six)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) : pCoreOf 2 K = q4311 I K := by
  have hSK : T ⊓ H ≤ Subgroup.normalizer (K : Set G) := s.sk.S_le_normalizer
  have hKSN : K ⊔ T ⊓ H ≤ Subgroup.normalizer (K : Set G) :=
    _root_.sup_le (fun x hx => Subgroup.le_normalizer hx) hSK
  refine le_antisymm ?_ ?_
  · rw [← s.pCoreOf_sup_eq h135 hR hC h37 h38 h39]
    exact le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 K).trans le_sup_left)
      (hKSN.trans (normalizer_le_normalizer_pCoreOf 2 K)) (pCoreOf_isPGroup 2 K)
  · have hperf : ⁅K, K⁆ = K := perfect_of_mem_cComp s.sk.cComp
    have hRK : pCoreOf 2 I ≤ Subgroup.normalizer (K : Set G) :=
      s.sk.base.pCoreOf_le_S.trans hSK
    rw [q4311, c134Q]
    exact (commutator_le_pCoreOf_of_le hperf hRK le_rfl).1

end Setting4311

end CFSG.Quasithin.H13.Ch4
