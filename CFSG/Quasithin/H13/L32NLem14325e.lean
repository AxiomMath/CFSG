module

public import CFSG.Quasithin.Vol2.Ch1Chief
public import CFSG.Quasithin.H13.L32NLem14325c

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint
open scoped commutatorElement

namespace L14325

variable {G : Type} [Group G] [Finite G] {T L V V₂ : Subgroup G} {g : G} {D : HatModelU (fsuU T V)}

namespace Ctx14325

variable (C : Ctx14325 G T L V V₂ g D)
include C

theorem pCoreOf_le_cHat : pCoreOf 2 (l32nH T V) ≤ l32nCHat T V := by
  rw [← C.q_tilde]
  rintro x ⟨hxH, -, hxc⟩
  exact ⟨hxH, L14332.l32nH_le_normalizer_zU hxH, fun u hu => C.lt.le (hxc u hu)⟩

theorem pCoreOf_ne_bot : pCoreOf 2 (l32nH T V) ≠ ⊥ := by
  intro hb
  have hle := C.hyp.fsuV1_le_pCoreOf
  rw [hb, le_bot_iff] at hle
  have := C.card_V1
  rw [hle, Subgroup.card_bot] at this
  omega

theorem exists_comp (h39 : A39ForSQTK) {P : Subgroup (D.V ≃ₗ[ZMod 2] D.V)}
    (hPH : P ≤ D.img (l32nH T V)) (hP1 : P ≠ ⊥) (hPp : ⁅P, P⁆ = P) :
    ∃ K ∈ cComp (l32nH T V), D.img K ≠ ⊥ := by
  have := L14332.finite_linearEquiv D
  by_contra hcon
  push Not at hcon
  apply hP1
  set H := l32nH T V with hH
  set N := Subgroup.normalizer (fsuU T V : Set G) with hN
  have hHN : H ≤ N := L14332.l32nH_le_normalizer_fsuU T V
  have hspan : cCompSpan H ≤ l32nCHat T V := by
    refine sSup_le fun K hK => ?_
    intro k hk
    have hkH : k ∈ H := le_of_mem_cComp hK hk
    have h1 : D.ρ ⟨k, hHN hkH⟩ ∈ D.img K := L128A.HatU.rho_mem_img D hk (hHN hkH)
    rw [hcon K hK, Subgroup.mem_bot] at h1
    exact (L14332.rho_eq_one_iff_mem hkH _).mp h1
  rw [lemma_1_2_1_one C.hyp.fsu.qtke C.hyp.fsu.simple C.hyp.fsu.nonabelian h39
    C.pCoreOf_ne_bot] at hspan
  set X := H.subgroupOf N with hX
  have hXmap : X.map N.subtype = H := Subgroup.map_subgroupOf_eq_of_le hHN
  have hcore : (perfectCore X).map D.ρ = ⊥ := by
    rw [Subgroup.map_eq_bot_iff]
    intro z hz
    have hz' : (z : G) ∈ perfectCore H := by
      rw [← hXmap, ← map_perfectCore]
      exact Subgroup.mem_map_of_mem _ hz
    exact (L128A.HatU.rho_eq_one_iff D z).mpr (hspan hz').2.2
  have hcore' : perfectCore (D.img H) = ⊥ := by
    have := map_perfectCore D.ρ X
    unfold HatModelU.img
    rw [← this, hcore]
  rw [eq_bot_iff, ← hcore']
  exact le_perfectCore_of_perfect hPH hPp

omit [Finite G] C in
theorem img_subnormal {K : Subgroup G} (hK : K ∈ cComp (l32nH T V)) :
    IsSubnormal (D.img K) (D.img (l32nH T V)) :=
  A3.subnormal_map D.ρ (A3.subnormal_comap (Subgroup.normalizer (fsuU T V : Set G)).subtype
    (subnormal_of_mem_cComp hK))

omit [Finite G] C in
theorem img_perfect {K : Subgroup G} (hK : K ∈ cComp (l32nH T V)) :
    ⁅D.img K, D.img K⁆ = D.img K := by
  set N := Subgroup.normalizer (fsuU T V : Set G) with hN
  have hKN : K ≤ N := (le_of_mem_cComp hK).trans (L14332.l32nH_le_normalizer_fsuU T V)
  have hK' : ⁅K.subgroupOf N, K.subgroupOf N⁆ = K.subgroupOf N := by
    apply Subgroup.map_injective N.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hKN]
    exact perfect_of_mem_cComp hK
  unfold HatModelU.img
  rw [← Subgroup.map_commutator, hK']

theorem card_img_dvd {K : Subgroup G} (hK : K ∈ cComp (l32nH T V)) :
    Nat.card ↥(D.img K) ∣ Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKH : K ≤ l32nH T V := le_of_mem_cComp hK
  have hKN : K ≤ Subgroup.normalizer (fsuU T V : Set G) :=
    hKH.trans (L14332.l32nH_le_normalizer_fsuU T V)
  have hker : ∀ x ∈ K, (∃ hxN : x ∈ Subgroup.normalizer (fsuU T V : Set G),
      D.ρ ⟨x, hxN⟩ = 1) ↔ x ∈ l32nCHat T V := by
    intro x hx
    constructor
    · rintro ⟨hxN, h1⟩
      exact (L14332.rho_eq_one_iff_mem (hKH hx) hxN).mp h1
    · intro h1
      exact ⟨hKN hx, (L14332.rho_eq_one_iff_mem (hKH hx) (hKN hx)).mpr h1⟩
  rw [L128A.HatU.card_img_eq_relIndex D hKN hker]
  have hO : pCoreOf 2 K ≤ l32nCHat T V :=
    (A4.pCoreOf_le_of_subnormal 2 (subnormal_of_mem_cComp hK)).trans C.pCoreOf_le_cHat
  have hdvd := Subgroup.relIndex_dvd_of_le_left (L := K) hO
  have hq : (pCoreOf 2 K).relIndex K = Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) := by
    have h1 : (pCoreOf 2 K).subgroupOf K = CFSG.pCore 2 ↥K := by
      exact Subgroup.comap_map_eq_self_of_injective K.subtype_injective _
    rw [Subgroup.relIndex, h1]
    rfl
  rw [hq] at hdvd
  exact hdvd

theorem exists_comp_img (h1332 : Stmt13_3_2) (h1352 : A6.Stmt13_5_2) (h1381 : Stmt13_8_1)
    (h36 : A36ForSQTK) (h39 : A39ForSQTK) {P : Subgroup (D.V ≃ₗ[ZMod 2] D.V)}
    (hPH : P ≤ D.img (l32nH T V)) (hP1 : P ≠ ⊥) (hPp : ⁅P, P⁆ = P)
    (hnorm : ∀ X : Subgroup (D.V ≃ₗ[ZMod 2] D.V), IsSubnormal X (D.img (l32nH T V)) →
      X ≠ ⊥ → ⁅X, X⁆ = X → ¬ ∀ γ ∈ X, ∀ w ∈ D.hat V, γ w ∈ D.hat V) :
    ∃ X : Subgroup (D.V ≃ₗ[ZMod 2] D.V), IsSubnormal X (D.img (l32nH T V)) ∧ X ≠ ⊥ ∧
      ⁅X, X⁆ = X ∧ (Nat.card X ∣ 60 ∨ Nat.card X ∣ 168) := by
  obtain ⟨K, hK, hK1⟩ := C.exists_comp h39 hPH hP1 hPp
  refine ⟨D.img K, img_subnormal hK, hK1, img_perfect hK, ?_⟩
  have hKH : K ≤ l32nH T V := le_of_mem_cComp hK
  have hKM : ¬ K ≤ Subgroup.normalizer (L : Set G) := by
    intro hle
    apply hnorm _ (img_subnormal hK) hK1 (img_perfect hK)
    intro γ hγ w hw
    obtain ⟨k, hk, hkN, rfl⟩ := (L128A.HatU.mem_img D).mp hγ
    have hkM : k ∈ l32nH T V ⊓ Subgroup.normalizer (L : Set G) := ⟨hKH hk, hle hk⟩
    rw [C.HM] at hkM
    exact C.rho_mem_hatV_of_normalizer (hKH hk) hkM.2 hw
  have hVK : ⁅vH T L V, K⁆ ≠ ⊥ := by
    intro hb
    apply hKM
    refine le_trans ?_ C.cent_le
    intro k hk
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have h1 : ⁅w, k⁆ = 1 := by
      have := Subgroup.commutator_mem_commutator hw hk
      rwa [hb, Subgroup.mem_bot] at this
    rw [commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1
  obtain ⟨S, hS⟩ := exists_sylow_of_quasithinIsSylowTwo C.hyp.fsu.sylow
  have hInH : InH (S : Subgroup G) (l32nH T V) := ⟨hS ▸ C.T_le, C.pCoreOf_ne_bot⟩
  have hTFAE := lemma_1_2_10_of_a36 C.hyp.fsu.qtke C.hyp.fsu.simple C.hyp.fsu.nonabelian h36 S
    hInH hK
  have h2 : ∃ W, IsTwoReducedIn (l32nH T V) W ∧ ⁅W, K⁆ ≠ ⊥ := ⟨vH T L V, C.red, hVK⟩
  have hLf : quasithinIsFaithfulLocal (S : Subgroup G) K := (hTFAE.out 1 2).mpr h2
  rw [hS] at hLf
  have hdvd := C.card_img_dvd hK
  rcases lemma1434One_of_inputs h1332 h1352 h1381 G T L C.hyp.hyp K hLf with he | h3
  · left
    obtain ⟨e⟩ := he
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin] at hdvd
    exact hdvd
  · right
    obtain ⟨e⟩ := nonempty_equiv_SL32_of_lieModel h3
    rw [Nat.card_congr e.toEquiv, HSType.card_SL_three_two] at hdvd
    exact hdvd

end Ctx14325

end L14325

end CFSG.Quasithin.H13
