module

public import CFSG.Quasithin.Vol2.Ch4Sec2Lem4212B
public import CFSG.Quasithin.Vol2.Ch4Sec4L446Mod
public import CFSG.Quasithin.Background.C4Statement

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.H13
open CFSG.Blueprint CFSG.Quasithin.A4
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

structure Conf4212 (G : Type) [Group G] [Finite G] (T M L I H K : Subgroup G) : Prop where
  hyp421 : Hyp4_2_1 G T M L
  I_le : I ≤ M
  inH : InH I H
  not_le : ¬ H ≤ M
  normal : M ≤ Subgroup.normalizer (L : Set G)
  conjClosure_eq : conjClosure L T = L
  omega_eq : omegaOneCenterOf (pCoreOf 2 (L ⊔ T)) = reducedAggregate (L ⊔ T)
  R_le : pCoreOf 2 I ≤ pCoreOf 2 (L ⊔ T)
  L_le : L ≤ perfectCore (L ⊓ H) ⊔ pCoreOf 2 L
  LH_mem : perfectCore (L ⊓ H) ∈ cComp (H ⊓ M)
  LH_normal : H ⊓ M ≤ Subgroup.normalizer (perfectCore (L ⊓ H) : Set G)
  hypC28 : HypC28 H (pCoreOf 2 I) (H ⊓ M) (perfectCore (L ⊓ H)) ⁅reducedAggregate (L ⊔ T), L⁆
  K_mem : K ∈ cComp H
  K_quasisimple : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K)
  LH_le : perfectCore (L ⊓ H) ≤ K
  K_not_le : ¬ K ≤ M
  K_normal : H ⊓ M ≤ Subgroup.normalizer (K : Set G)
  described : C48KDescribed H (pCoreOf 2 I) (H ⊓ M) (perfectCore (L ⊓ H))
    ⁅reducedAggregate (L ⊔ T), L⁆ K
  cases :
    C48Case1 H (pCoreOf 2 I) (H ⊓ M) (perfectCore (L ⊓ H)) ⁅reducedAggregate (L ⊔ T), L⁆ K ∨
    C48Case2 H (pCoreOf 2 I) (H ⊓ M) (perfectCore (L ⊓ H)) ⁅reducedAggregate (L ⊔ T), L⁆ K ∨
    C48Case3 H (pCoreOf 2 I) (H ⊓ M) (perfectCore (L ⊓ H)) ⁅reducedAggregate (L ⊔ T), L⁆ K ∨
    C48Case4 H (pCoreOf 2 I) (H ⊓ M) (perfectCore (L ⊓ H)) ⁅reducedAggregate (L ⊔ T), L⁆ K ∨
    C48Case5 H (pCoreOf 2 I) (H ⊓ M) (perfectCore (L ⊓ H)) ⁅reducedAggregate (L ⊔ T), L⁆ K ∨
    C48Case6 H (pCoreOf 2 I) (H ⊓ M) (perfectCore (L ⊓ H)) ⁅reducedAggregate (L ⊔ T), L⁆ K ∨
    C48Case7 H (pCoreOf 2 I) (H ⊓ M) (perfectCore (L ⊓ H)) ⁅reducedAggregate (L ⊔ T), L⁆ K ∨
    C48Case8 H (pCoreOf 2 I) (H ⊓ M) (perfectCore (L ⊓ H)) ⁅reducedAggregate (L ⊔ T), L⁆ K ∨
    C48Case9 H (pCoreOf 2 I) (H ⊓ M) (perfectCore (L ⊓ H)) ⁅reducedAggregate (L ⊔ T), L⁆ K

theorem reducedAggregate_le_omegaOneCenterOf_pCoreOf (H : Subgroup G) :
    reducedAggregate H ≤ omegaOneCenterOf (pCoreOf 2 H) := by
  show (primeReducedAggregate ↥H 2).map H.subtype ≤ _
  rw [primeReducedAggregate_map_subtype_eq_twoReducedJoin]
  exact Hyp4_2_1.twoReducedJoin_le_omegaOneCenterOf H

namespace Hyp4_2_3

variable {T M L Mm I : Subgroup G} (h : Hyp4_2_3 G T M L Mm I)
include h

theorem I_le_normalizer (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    {H : Subgroup G} (hIH : I ≤ H)
    (hLH : H ⊓ M ≤ Subgroup.normalizer (perfectCore (L ⊓ H) : Set G)) :
    I ≤ Subgroup.normalizer (L : Set G) := by
  intro i hi
  set LH := perfectCore (L ⊓ H) with hLHdef
  have hLc : L ∈ cComp M := h.mem_cComp h37 h39
  have hiM : i ∈ M := h.I_le hi
  have hLi := map_conj_mem_cComp hLc hiM
  by_contra hiN
  have he : L.map (MulAut.conj i).toMonoidHom ≠ L := fun h' =>
    hiN (Subgroup.mem_normalizer_iff_map_conj_eq.mpr h')
  have hO2M : pCoreOf 2 M ≠ ⊥ := pCoreOf_ne_bot_of_isTwoLocal h.maxTwoLocal.1
  have hc := (lemma_1_2_1_two h.qtke h.simple h.nonabelian h37 hO2M hLc hLi (Ne.symm he)).1
  have hLHL : LH ≤ L := (perfectCore_le _).trans inf_le_left
  have hLHi : LH ≤ L.map (MulAut.conj i).toMonoidHom := by
    have h1 : LH.map (MulAut.conj i).toMonoidHom = LH :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hLH ⟨hIH hi, hiM⟩)
    rw [← h1]
    exact Subgroup.map_mono hLHL
  have hLHO : LH ≤ pCoreOf 2 L := calc
    LH = ⁅LH, LH⁆ := (perfectCore_perfect _).symm
    _ ≤ ⁅L, L.map (MulAut.conj i).toMonoidHom⁆ := Subgroup.commutator_mono hLHL hLHi
    _ ≤ pCoreOf 2 L := hc.trans inf_le_left
  exact ne_bot_of_mem_cComp (h.mem_cComp_LH h37 h38 h39 hIH)
    (eq_bot_of_commutator_eq_self_of_isPGroup_two (perfectCore_perfect _)
      ((pCoreOf_isPGroup 2 L).to_le hLHO))

theorem T_le_normalizer (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (hIN : I ≤ Subgroup.normalizer (L : Set G)) : T ≤ Subgroup.normalizer (L : Set G) := by
  intro t ht
  obtain ⟨i, hi, he⟩ := h.exists_conj_I h37 h38 h39 ht
  have hLi : CFSG.conjugate L i = L :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.inv_mem _ (hIN hi))
  rw [hLi] at he
  have ht' : t⁻¹ ∈ Subgroup.normalizer (L : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr he
  simpa using Subgroup.inv_mem _ ht'

theorem omega_eq_reducedAggregate (h36 : A36ForSQTK) (h37 : A37ForSQTK) (h39 : A39ForSQTK)
    (hn : M ≤ Subgroup.normalizer (L : Set G)) (hc : conjClosure L T = L) :
    omegaOneCenterOf (pCoreOf 2 (L ⊔ T)) = reducedAggregate (L ⊔ T) := by
  set Z₀ := omegaOneCenterOf (pCoreOf 2 (L ⊔ T)) with hZ₀
  have hVL : ⁅Z₀, L⁆ ≠ ⊥ := by
    have h1 := h.V_ne_bot h36 h37 h39
    rwa [← h.pCoreOf_sup_eq_inf, hc] at h1
  have hVN : L ⊔ T ≤ Subgroup.normalizer (Z₀ : Set G) :=
    (le_normalizer_pCoreOf 2 _).trans (normalizer_le_normalizer_omegaOneCenterOf _)
  have hred := h.toHyp4_2_1.isTwoReducedIn_of_le_omegaOneCenter hn
    (CFSG.Quasithin.omegaOneCenterOf_eq (pCoreOf 2 (L ⊔ T))).le hVN hVL
  exact le_antisymm (A7.le_reducedAggregate_of_isTwoReducedIn hred)
    (reducedAggregate_le_omegaOneCenterOf_pCoreOf _)

theorem lemma_4_2_12_two (h36 : A36ForSQTK) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h39 : A39ForSQTK) (h48 : ASC48Statement G) {H : Subgroup G} (hH : InH I H)
    (hHM : ¬ H ≤ M) (h425 : ¬ oTwoFstarIn H ≤ M) :
    ∃ K : Subgroup G, Conf4212 G T M L I H K := by
  have hC28 := h.lemma_4_2_4 h36 h37 h38 h39 hH hHM
  have hlt : H ⊓ M < H := lt_of_le_of_ne inf_le_left fun he => hHM (he ▸ inf_le_right)
  obtain ⟨hM0, -⟩ := h48 _ _ _ _ _ hC28 hlt
  have hLHN : H ⊓ M ≤ Subgroup.normalizer (perfectCore (L ⊓ H) : Set G) := by
    have h1 := le_normalizer_conjClosure (perfectCore (L ⊓ H)) (H ⊓ M)
    rwa [← hM0] at h1
  have hIN := h.I_le_normalizer h37 h38 h39 hH.1 hLHN
  have hTN := h.T_le_normalizer h37 h38 h39 hIN
  have hc : conjClosure L T = L := conjClosure_eq_self hTN
  have hn : M ≤ Subgroup.normalizer (L : Set G) := by
    have h1 := h.le_normalizer_conjClosure h37 h38 h39
    rwa [hc] at h1
  have hΩ := h.omega_eq_reducedAggregate h36 h37 h39 hn hc
  have hV : ⁅omegaOneCenterOf (T ⊓ centralizerSection M (conjClosure L T)
      (pCoreOf 2 (conjClosure L T))), conjClosure L T⁆ = ⁅reducedAggregate (L ⊔ T), L⁆ := by
    rw [← h.pCoreOf_sup_eq_inf, hc, hΩ]
  rw [hV] at hC28
  obtain ⟨-, K, hK, hKq, hLK, hcase⟩ := h48 _ _ _ _ _ hC28 hlt
  rcases hcase with h10 | ⟨hcases, hKM, hKN, hdesc⟩
  · exact absurd (h10.1.trans inf_le_right) h425
  refine ⟨K, ⟨h.toHyp4_2_1, h.I_le, hH, hHM, hn, hc, hΩ, ?_,
    h.le_perfectCore_sup h37 h38 h39 hH.1, h.mem_cComp_LH h37 h38 h39 hH.1, hLHN, hC28, hK,
    hKq, hLK, fun hle => hKM (le_inf (le_of_mem_cComp hK) hle), hKN, hdesc, hcases⟩⟩
  rw [h.pCoreOf_sup_eq_inf]
  exact h.R_le

end Hyp4_2_3

end CFSG.Quasithin.H13.Ch4
