module

public import CFSG.Quasithin.Vol2.Ch4Sec2CentKU2
public import CFSG.Quasithin.Vol2.Ch4Sec2CentKU4
public import CFSG.Quasithin.Vol2.Ch4Sec2CentKU3

public section

namespace CFSG.Quasithin.H13.Ch4.CentK

open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.A4
open CFSG.Open hiding StatedSL
open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {T M L Mm I H K : Subgroup G} {n : ℕ}

omit [Finite G] in
private theorem le_normalizer_sup_centKU5 {S A B : Subgroup G}
    (hA : S ≤ Subgroup.normalizer (A : Set G)) (hB : S ≤ Subgroup.normalizer (B : Set G)) :
    S ≤ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  intro g hg
  refine Subgroup.mem_normalizer_iff_map_conj_eq.mpr ?_
  rw [Subgroup.map_sup, Subgroup.mem_normalizer_iff_map_conj_eq.mp (hA hg),
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hB hg)]

omit [Finite G] in
private theorem le_normalizer_centralizer_centKU5 (N : Subgroup G) :
    Subgroup.normalizer (N : Set G) ≤
      Subgroup.normalizer (Subgroup.centralizer (N : Set G) : Set G) := by
  have key : ∀ g ∈ Subgroup.normalizer (N : Set G), ∀ c ∈ Subgroup.centralizer (N : Set G),
      g * c * g⁻¹ ∈ Subgroup.centralizer (N : Set G) := by
    intro g hg c hc
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have hk' : g⁻¹ * k * g ∈ N := (Subgroup.mem_normalizer_iff''.mp hg k).mp hk
    have h1 := (Subgroup.mem_centralizer_iff.mp hc) _ hk'
    calc k * (g * c * g⁻¹) = g * ((g⁻¹ * k * g) * c) * g⁻¹ := by group
      _ = g * (c * (g⁻¹ * k * g)) * g⁻¹ := by rw [h1]
      _ = g * c * g⁻¹ * k := by group
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro c
  refine ⟨fun hc => key g hg c hc, fun hc => ?_⟩
  have h2 := key g⁻¹ (inv_mem hg) _ hc
  have e : g⁻¹ * (g * c * g⁻¹) * g⁻¹⁻¹ = c := by group
  rwa [e] at h2

private theorem c134Q_ne_bot_centKU5 (s : Setting28 T M L Mm I H K n) :
    c134Q (K ⊔ pCoreOf 2 I) K ≠ ⊥ := by
  intro hQ
  obtain ⟨⟨_, F₂, _, _, _, _, _, hN⟩, _⟩ := (s.h2 : IsC134Case2 _ _ _)
  obtain ⟨-, -, β, hβ, -, -⟩ := hN
  obtain ⟨u, hu⟩ := hβ (Multiplicative.ofAdd fun _ _ => (1 : F₂))
  have key : ∀ x : G, x ∈ c134Q (K ⊔ pCoreOf 2 I) K → x = 1 := by
    rw [hQ]
    exact fun x hx => Subgroup.mem_bot.mp hx
  have hu1 : u = 1 := Subtype.ext (key u u.2)
  rw [hu1, map_one] at hu
  have h1 := congrFun (congrFun (congrArg Multiplicative.toAdd hu) 0) 0
  exact one_ne_zero h1.symm

theorem lemma28 (s : Setting28 T M L Mm I H K n)
    (h36 : A36ForSQTK) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (h48 : ASC48Statement G) (h425 : Thm4_2_5) {X : Subgroup G} (hIX : I ≤ X) (hKX : K ≤ X)
    (hX : pCoreOf 2 X ≠ ⊥) : X ≤ H := by
  obtain ⟨H₁, hH₁⟩ := exists_inM_of_pCoreOf_ne_bot hX
  have hIH₁ : InM I H₁ := ⟨hH₁.1, hIX.trans hH₁.2⟩
  have hKH₁ : K ≤ H₁ := hKX.trans hH₁.2
  have hH₁M : ¬ H₁ ≤ M := fun h => s.c.K_not_le (hKH₁.trans h)
  have hne : H₁ ≠ M := fun h => hH₁M (h ▸ le_rfl)
  have h425' := h425 G T M L Mm I H₁ s.hy hIH₁ hne
  obtain ⟨K₁, c₁⟩ := s.hy.lemma_4_2_12_two h36 h37 h38 h39 h48 (inH_of_inM hIH₁) hH₁M h425'
  have hL₁ : perfectCore (L ⊓ H₁) = perfectCore (L ⊓ H) := by
    rw [LH_inf_eq s h37 h38 h39 hIH₁.2 hKH₁ c₁]
  have h2₁ : IsC134Case 2 (K₁ ⊔ pCoreOf 2 I) (pCoreOf 2 I) K₁ := isC134Case2_of_conf s c₁ hL₁
  obtain ⟨h41₁, -⟩ := c₁.c41Case3_of_isC134Case2 h2₁
  have hH₁K₁ : H₁ ≤ Subgroup.normalizer (K₁ : Set G) := by
    intro h hh
    apply mem_normalizer_of_map_conj_le
    rintro _ ⟨k, hk, rfl⟩
    have h1 := mem_conjClosure hh hk
    rw [h41₁.2.2.1] at h1
    exact h1
  have hLK₁ : perfectCore (L ⊓ H) ≤ K₁ := by
    rw [← hL₁]
    exact c₁.LH_le
  have hKK₁ : K ≤ K₁ := K_le_K₁ s hKH₁ hH₁K₁ hLK₁
  have hcard : Nat.card (ModO2 K₁) = Nat.card (ModO2 K) := card_modO2_eq s c₁ hL₁ h2₁
  have hK₁K : K₁ ≤ K := K₁_le_K s h37 h38 h39 c₁ hKK₁ hH₁K₁ hcard
  have hK₁eq : K₁ = K := le_antisymm hK₁K hKK₁
  rw [hK₁eq] at hH₁K₁
  have hperf : ⁅K, K⁆ = K := perfect_of_mem_cComp s.c.K_mem
  have hRK : pCoreOf 2 I ≤ Subgroup.normalizer (K : Set G) :=
    ((pCoreOf_le 2 I).trans s.c.inH.1).trans s.hKH
  have hQU : c134Q (K ⊔ pCoreOf 2 I) K ≤ pCoreOf 2 K :=
    (commutator_le_pCoreOf_of_le hperf hRK le_rfl).1
  have hK2 : pCoreOf 2 K ≠ ⊥ := by
    intro h
    rw [h] at hQU
    exact c134Q_ne_bot_centKU5 s (le_bot_iff.mp hQU)
  have hH₁H : H₁ ≤ H := by
    have h1 : H₁ ≤ Subgroup.normalizer (pCoreOf 2 K : Set G) :=
      hH₁K₁.trans (normalizer_le_normalizer_pCoreOf 2 K)
    rwa [Conf4212.normalizer_pCoreOf_K_eq s.hIH s.hKH hK2] at h1
  exact hH₁.2.trans hH₁H

theorem normalizer_Q_le_H (s : Setting28 T M L Mm I H K n)
    (h36 : A36ForSQTK) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (h48 : ASC48Statement G) (h425 : Thm4_2_5) :
    Subgroup.normalizer (c134Q (K ⊔ pCoreOf 2 I) K : Set G) ≤ H := by
  have hQne : c134Q (K ⊔ pCoreOf 2 I) K ≠ ⊥ := c134Q_ne_bot_centKU5 s
  have hRK : pCoreOf 2 I ≤ Subgroup.normalizer (K : Set G) :=
    ((pCoreOf_le 2 I).trans s.c.inH.1).trans s.hKH
  have hperf : ⁅K, K⁆ = K := perfect_of_mem_cComp s.c.K_mem
  have hQU : c134Q (K ⊔ pCoreOf 2 I) K ≤ pCoreOf 2 K :=
    (commutator_le_pCoreOf_of_le hperf hRK le_rfl).1
  have hQ2 : IsPGroup 2 ↥(c134Q (K ⊔ pCoreOf 2 I) K) := (pCoreOf_isPGroup 2 K).to_le hQU
  have hKP : K ≤ Subgroup.normalizer (pCoreOf 2 (K ⊔ pCoreOf 2 I) : Set G) :=
    le_sup_left.trans (le_normalizer_pCoreOf 2 (K ⊔ pCoreOf 2 I))
  have hKN : K ≤ Subgroup.normalizer (c134Q (K ⊔ pCoreOf 2 I) K : Set G) :=
    fun k hk => CFSG.Quasithin.A4.mem_normalizer_commutator (A := pCoreOf 2 (K ⊔ pCoreOf 2 I))
      (B := K) (hKP hk) (Subgroup.le_normalizer hk)
  have hIK : I ≤ Subgroup.normalizer (K : Set G) := s.c.inH.1.trans s.hKH
  have hIR : I ≤ Subgroup.normalizer (pCoreOf 2 I : Set G) := le_normalizer_pCoreOf 2 I
  have hIKR : I ≤ Subgroup.normalizer ((K ⊔ pCoreOf 2 I : Subgroup G) : Set G) :=
    le_normalizer_sup_centKU5 hIK hIR
  have hIP : I ≤ Subgroup.normalizer (pCoreOf 2 (K ⊔ pCoreOf 2 I) : Set G) :=
    hIKR.trans (normalizer_le_normalizer_pCoreOf 2 (K ⊔ pCoreOf 2 I))
  have hIN : I ≤ Subgroup.normalizer (c134Q (K ⊔ pCoreOf 2 I) K : Set G) :=
    fun i hi => CFSG.Quasithin.A4.mem_normalizer_commutator (A := pCoreOf 2 (K ⊔ pCoreOf 2 I))
      (B := K) (hIP hi) (hIK hi)
  have hQX : c134Q (K ⊔ pCoreOf 2 I) K ≤
      pCoreOf 2 (Subgroup.normalizer (c134Q (K ⊔ pCoreOf 2 I) K : Set G)) :=
    CFSG.LieType.BorelTits.le_pCoreOf_normalizer 2 _ hQ2
  have hX : pCoreOf 2 (Subgroup.normalizer (c134Q (K ⊔ pCoreOf 2 I) K : Set G)) ≠ ⊥ := by
    intro h
    rw [h] at hQX
    exact hQne (le_bot_iff.mp hQX)
  exact lemma28 s h36 h37 h38 h39 h48 h425 hIN hKN hX

theorem normalizer_ZC_le_H (s : Setting28 T M L Mm I H K n)
    (h36 : A36ForSQTK) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (h48 : ASC48Statement G) (h425 : Thm4_2_5)
    (hZ : omegaOneCenterOf (pCoreOf 2 I) ⊓ Subgroup.centralizer (K : Set G) ≠ ⊥) :
    Subgroup.normalizer ((omegaOneCenterOf (pCoreOf 2 I) ⊓ Subgroup.centralizer (K : Set G) :
      Subgroup G) : Set G) ≤ H := by
  have hKZ : K ≤ Subgroup.normalizer ((omegaOneCenterOf (pCoreOf 2 I) ⊓
      Subgroup.centralizer (K : Set G) : Subgroup G) : Set G) := by
    intro k hk
    refine Subgroup.centralizer_le_normalizer _ ?_
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hzC : z ∈ Subgroup.centralizer (K : Set G) := (Subgroup.mem_inf.mp hz).2
    exact ((Subgroup.mem_centralizer_iff.mp hzC) k hk).symm
  have hIO : I ≤ Subgroup.normalizer (omegaOneCenterOf (pCoreOf 2 I) : Set G) :=
    (le_normalizer_pCoreOf 2 I).trans
      (CFSG.Quasithin.A4.normalizer_le_normalizer_omegaOneCenterOf (pCoreOf 2 I))
  have hIC : I ≤ Subgroup.normalizer (Subgroup.centralizer (K : Set G) : Set G) :=
    (s.c.inH.1.trans s.hKH).trans (le_normalizer_centralizer_centKU5 K)
  have hIZ : I ≤ Subgroup.normalizer ((omegaOneCenterOf (pCoreOf 2 I) ⊓
      Subgroup.centralizer (K : Set G) : Subgroup G) : Set G) :=
    fun i hi => CFSG.Quasithin.A4.mem_normalizer_inf (hIO hi) (hIC hi)
  have hZR : omegaOneCenterOf (pCoreOf 2 I) ⊓ Subgroup.centralizer (K : Set G) ≤ pCoreOf 2 I :=
    inf_le_left.trans (CFSG.Quasithin.A4.omegaOneCenterOf_le (pCoreOf 2 I))
  have hZ2 : IsPGroup 2 ↥(omegaOneCenterOf (pCoreOf 2 I) ⊓
      Subgroup.centralizer (K : Set G) : Subgroup G) :=
    (pCoreOf_isPGroup 2 I).to_le hZR
  have hX : pCoreOf 2 (Subgroup.normalizer ((omegaOneCenterOf (pCoreOf 2 I) ⊓
      Subgroup.centralizer (K : Set G) : Subgroup G) : Set G)) ≠ ⊥ := by
    intro h
    have h1 := CFSG.LieType.BorelTits.le_pCoreOf_normalizer 2 _ hZ2
    rw [h] at h1
    exact hZ (le_bot_iff.mp h1)
  exact lemma28 s h36 h37 h38 h39 h48 h425 hIZ hKZ hX

end CFSG.Quasithin.H13.Ch4.CentK
