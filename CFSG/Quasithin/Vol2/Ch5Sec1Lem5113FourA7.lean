module

public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5113BlockSteps
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5113Cmp

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin

@[expose] def FactFFJ2M23 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K Q W : Subgroup G), ⁅K, K⁆ = K →
    (Nonempty (O2Q K ≃* NativeSporadic.J2) ∨ Nonempty (O2Q K ≃* NativeSporadic.M23)) →
    IsSylowTwoOf Q (K ⊔ Q) → Q ≤ Subgroup.normalizer (K : Set G) → SQTKGroup ↥(K ⊔ Q) →
    IsTwoReducedIn (K ⊔ Q) W → ¬ K ≤ Subgroup.centralizer (W : Set G) →
      thompsonJ Q ≤ Subgroup.centralizer (W : Set G)

section General

variable {G : Type} [Group G] [Finite G]

theorem le_pCoreOf_of_normal_of_ne {K N : Subgroup G} (hK : ⁅K, K⁆ = K)
    (hs : IsSimpleGroup (O2Q K)) (hNK : N ≤ K) (hKN : K ≤ Subgroup.normalizer (N : Set G))
    (hne : N ≠ K) : N ≤ pCoreOf 2 K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn : (modO2Image K N).Normal := by
    have : (N.subgroupOf K).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hNK).mpr hKN
    exact Subgroup.Normal.map this _ (QuotientGroup.mk'_surjective _)
  have := hs
  rcases hn.eq_bot_or_eq_top with hbot | htop
  · have h1 := le_sup_of_modO2Image_le hNK (bot_le : (⊥ : Subgroup G) ≤ K)
      (by rw [hbot]; exact bot_le)
    simpa using h1
  · exfalso
    apply hne
    have h1 := Vol2.Ch11.SecS.le_sup_of_modO2Image_eq_top hNK htop
    have hON : pCoreOf 2 K ≤ Subgroup.normalizer (N : Set G) :=
      (CFSG.LieType.BorelTits.pCoreOf_le 2 K).trans hKN
    exact le_antisymm hNK (le_of_perfect_of_le_sup hK h1
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K) hON)

theorem isPGroup_sup_inf_centralizer {K Q W : Subgroup G} (hK : ⁅K, K⁆ = K)
    (hs : IsSimpleGroup (O2Q K)) (hQ2 : IsPGroup 2 ↥Q)
    (hQK : Q ≤ Subgroup.normalizer (K : Set G))
    (hYW : K ⊔ Q ≤ Subgroup.normalizer (W : Set G))
    (hKW : ¬ K ≤ Subgroup.centralizer (W : Set G)) :
    IsPGroup 2 ↥((K ⊔ Q) ⊓ Subgroup.centralizer (W : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := (K ⊔ Q) ⊓ Subgroup.centralizer (W : Set G) with hC
  have hCN : K ⊔ Q ≤ Subgroup.normalizer (C : Set G) := fun y hy =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer hy, B6.le_normalizer_centralizer hYW hy⟩
  have hCK : C ⊓ K ≤ pCoreOf 2 K := by
    refine le_pCoreOf_of_normal_of_ne hK hs inf_le_right (fun y hy =>
      Subgroup.inf_normalizer_le_normalizer_inf
        ⟨hCN (Subgroup.mem_sup_left hy), Subgroup.le_normalizer hy⟩) fun he => hKW ?_
    rw [← he]
    exact inf_le_left.trans inf_le_right
  intro c
  have hcY : (c : G) ∈ ((Q ⊔ K : Subgroup G) : Set G) := by
    rw [sup_comm]
    exact c.2.1
  rw [Subgroup.coe_mul_of_left_le_normalizer_right Q K hQK] at hcY
  obtain ⟨t, ht, k, hk, htk⟩ := hcY
  obtain ⟨e, he⟩ := hQ2 ⟨t, ht⟩
  have he' : t ^ 2 ^ e = 1 := congrArg Subtype.val he
  obtain ⟨k', hk', hpow⟩ := exists_pow_mul_eq_pow_mul (hQK ht) hk (2 ^ e)
  have h1 : (c : G) ^ 2 ^ e ∈ C ⊓ K := by
    refine ⟨C.pow_mem c.2 _, ?_⟩
    rw [← htk, hpow, he', one_mul]
    exact hk'
  obtain ⟨f, hf⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K ⟨_, hCK h1⟩
  have hf' : ((c : G) ^ 2 ^ e) ^ 2 ^ f = 1 := congrArg Subtype.val hf
  refine ⟨e + f, Subtype.ext ?_⟩
  rw [Subgroup.coe_pow, Subgroup.coe_one, pow_add, pow_mul]
  exact hf'

omit [Finite G] in
theorem le_omegaOneCenterOf_thompsonJ [Finite G] {T W : Subgroup G} (hW : IsElemAbelian 2 W)
    (hWT : W ≤ T) (hJ : thompsonJ T ≤ Subgroup.centralizer (W : Set G)) :
    W ≤ omegaOneCenterOf (thompsonJ T) := by
  obtain ⟨A, hA⟩ := exists_isMaxElemAbelian T
  have hAW : A ≤ Subgroup.centralizer (W : Set G) := (B6.le_thompsonJ hA).trans hJ
  have hWA : W ≤ A := by
    have hel : IsElemAbelian 2 (W ⊔ A) := B2F.isElemAbelian_sup_of_commute hW hA.2.1
      fun w hw a ha => Subgroup.mem_centralizer_iff.mp (hAW ha) w hw
    have hcard := hA.2.2 (W ⊔ A) (sup_le hWT hA.1) hel
    have heq : A = W ⊔ A := Subgroup.eq_of_le_of_card_ge le_sup_right hcard
    rw [heq]
    exact le_sup_left
  intro w hw
  refine Subgroup.subset_closure ⟨⟨B6.le_thompsonJ hA (hWA hw),
    Subgroup.mem_centralizer_iff.mpr fun j hj => ?_⟩, hW.2 w hw⟩
  exact (Subgroup.mem_centralizer_iff.mp (hJ hj) w hw).symm

theorem baum_eq_of_baum_le {T R : Subgroup G} (hBR : baum T ≤ R) (hRT : R ≤ T) :
    baum R = baum T := by
  have hJ : thompsonJ R = thompsonJ T :=
    B6.thompsonJ_eq_of_le ((B6.thompsonJ_le_baum T).trans hBR) hRT
  unfold baum
  rw [hJ]
  refine le_antisymm (inf_le_inf_right _ hRT) (le_inf hBR inf_le_right)

end General

namespace Main513

variable {G : Type} [Group G] [Finite G] {T M L V H B D K₁ X Kh₁ : Subgroup G} {n : ℕ}

theorem commutator_thompsonJ_ne_bot (h5171 : A5.Stmt5_1_7_one)
    (m : Main513 G T M L V H B D K₁ X Kh₁ n)
    (hmax : quasithinIsMaximalLocal T (conjClosure Kh₁ T))
    (hs : IsSimpleGroup (O2Q (conjClosure Kh₁ T)))
    (hZ : ¬ conjClosure Kh₁ T ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) :
    IsTwoReducedIn (conjClosure Kh₁ T ⊔ T)
        (conjClosure (quasithinOmegaOneCenter T) (conjClosure Kh₁ T ⊔ T)) ∧
      ¬ conjClosure Kh₁ T ≤ Subgroup.centralizer
        ((conjClosure (quasithinOmegaOneCenter T) (conjClosure Kh₁ T ⊔ T) : Subgroup G) :
          Set G) ∧
      ⁅conjClosure (quasithinOmegaOneCenter T) (conjClosure Kh₁ T ⊔ T), thompsonJ T⁆ ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := m.hyp.toHyp5_0_1
  have hKhperf : ⁅conjClosure Kh₁ T, conjClosure Kh₁ T⁆ = conjClosure Kh₁ T :=
    A3.conjClosure_perfect (perfect_of_mem_cComp m.hat.1)
  have hTKh : T ≤ Subgroup.normalizer (conjClosure Kh₁ T : Set G) :=
    le_normalizer_conjClosure Kh₁ T
  have hTY : IsSylowTwoOf T (conjClosure Kh₁ T ⊔ T) := h.isSylowTwoOf le_sup_right
  have hchar : CharTwo (conjClosure Kh₁ T ⊔ T) :=
    charTwo_of_inH' h.qtke h.sylow ⟨le_sup_right, hmax.1.2.2.2⟩
  obtain ⟨hWO, hWel, hWred⟩ := conjClosure_isTwoReducedIn_of_charTwo hTY hchar le_rfl
  have hOT : pCoreOf 2 (conjClosure Kh₁ T ⊔ T) ≤ T := F7.isSylowTwoOf_pCoreOf_le hTY
  have hWT : conjClosure (quasithinOmegaOneCenter T) (conjClosure Kh₁ T ⊔ T) ≤ T :=
    (hWO.trans inf_le_left).trans hOT
  have hYW := hWred.2.1
  have hKhW : ¬ conjClosure Kh₁ T ≤ Subgroup.centralizer
      ((conjClosure (quasithinOmegaOneCenter T) (conjClosure Kh₁ T ⊔ T) : Subgroup G) :
        Set G) := fun hle =>
    hZ (hle.trans (Subgroup.centralizer_le fun x hx => le_conjClosure _ _ hx))
  refine ⟨hWred, hKhW, fun hJ => ?_⟩
  rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer] at hJ
  have hWZ := le_omegaOneCenterOf_thompsonJ hWel hWT hJ
  have hBC : baum T ≤ (conjClosure Kh₁ T ⊔ T) ⊓ Subgroup.centralizer
      ((conjClosure (quasithinOmegaOneCenter T) (conjClosure Kh₁ T ⊔ T) : Subgroup G) :
        Set G) :=
    le_inf (inf_le_left.trans le_sup_right)
      (inf_le_right.trans (Subgroup.centralizer_le fun x hx => hWZ hx))
  have hC2 := isPGroup_sup_inf_centralizer hKhperf hs h.sylow.1 hTKh hYW hKhW
  have hCY : conjClosure Kh₁ T ⊔ T ≤ Subgroup.normalizer
      (((conjClosure Kh₁ T ⊔ T) ⊓ Subgroup.centralizer
        ((conjClosure (quasithinOmegaOneCenter T) (conjClosure Kh₁ T ⊔ T) : Subgroup G) :
          Set G) : Subgroup G) : Set G) := fun y hy =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer hy, B6.le_normalizer_centralizer hYW hy⟩
  have hCO := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left hCY hC2
  have hbeq := baum_eq_of_baum_le (hBC.trans hCO) hOT
  have hYB : conjClosure Kh₁ T ⊔ T ≤ Subgroup.normalizer (baum T : Set G) := by
    rw [← hbeq]
    exact (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _).trans
      (normalizer_le_normalizer_baum _)
  have hNM := h5171 G T L M h.simple h.nonabelian h.qtke h.sylow h.maximal h.faithful
    ⟨n, h.two_le, h.lie⟩ h.maxTwoLocal h.T_le h.L_le h.normal
  have hKM : oTwoUpper H ≤ M := (m.lt.le.trans (le_sup_left.trans hYB)).trans hNM
  apply m.hyp.hStar.2.1
  rw [eq_oTwoUpper_sup_of_isSylowTwoOf' (h.isSylowTwoOf m.hyp.hStar.1.1)]
  exact sup_le hKM h.T_le

end Main513

theorem stmt5_1_13_four_A7_of
    (h5171 : A5.Stmt5_1_7_one) (hFF : FactFFJ2M23) : Stmt5_1_13_four_A7 := by
  intro G _ _ T M L V H B D K₁ X Kh₁ n m hc5 ty hmax hZ
  have h := m.hyp.toHyp5_0_1
  have : IsSimpleGroup G := h.simple
  have hloc : LocalSQTK G := (qtkeCore_of_cat h.nonabelian h.qtke).1
  have hs : IsSimpleGroup (O2Q (conjClosure Kh₁ T)) := IsA7J2M23.isSimpleGroup ty.1
  rcases ty.1 with hA7 | hJM | hJM
  · exact hA7
  all_goals
    exfalso
    obtain ⟨hW, hKhW, hJ⟩ := m.commutator_thompsonJ_ne_bot h5171 hmax hs hZ
    apply hJ
    rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact hFF G (conjClosure Kh₁ T) T _ (A3.conjClosure_perfect (perfect_of_mem_cComp m.hat.1))
      (by first | exact Or.inl hJM | exact Or.inr hJM) (h.isSylowTwoOf le_sup_right)
      (le_normalizer_conjClosure Kh₁ T) (InternalSec.sqtkGroup_of_localSQTK hloc hmax.1.2.2.2) hW
      hKhW

end CFSG.Quasithin.H13
