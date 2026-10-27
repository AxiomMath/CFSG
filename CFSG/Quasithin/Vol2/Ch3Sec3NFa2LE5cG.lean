module

public import CFSG.Quasithin.Vol2.Ch3Sec3NFa2LModel
public import CFSG.Quasithin.Vol2.Ch3Sec3NFa2Fx
public import CFSG.Quasithin.Vol2.Ch3Sec3NFa2Core
public import CFSG.Quasithin.Vol2.Ch3Sec3NFa2LC1

public section

namespace CFSG.Quasithin.H13.NFa2

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Quasithin
open CFSG.Quasithin.H13.Ch3Sec3
open CFSG.QuasithinUnique.Vol2Native (A37ForSQTKCat A38ForSQTKCat A39ForSQTKCat)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T M L D H K : Subgroup G} {q : ℕ}

theorem VMod.card_V_le {V L Z : Subgroup G} (m : VMod V L Z) : Nat.card V ≤ 64 := by
  have h := Nat.card_le_card_of_injective m.Φ m.inj
  have e : Nat.card (Multiplicative (Fin 6 → ZMod 2)) = 64 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, Fintype.card_fun, ZMod.card]
    simp
  rwa [e] at h

theorem A2Cfg.not_K_le_normalizer_Vp (hG1 : Leaf_G1)
    (h36 : A36ForSQTK) (h5 : Stmt3_3_5) (h7 : Stmt3_3_7) (h9 : Stmt3_3_9)
    (hGA : GriessAllModelsStatement) (h128 : Lemma128Two) (h37 : A37ForSQTKCat)
    (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat)
    (c : A2Cfg G T M L D H K q) :
    ¬ K ≤ Subgroup.normalizer (a2Vp L T H : Set G) := by
  classical
  intro hKN
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hxY, hxK, hx3⟩ := c.exists_x h37 h38
  obtain ⟨m, -⟩ := c.exists_vmod h36 h5 h7 h9 hGA h128 h37 h38 h39
  have hVe := c.V_elemAbelian
  obtain ⟨-, hLV, hTV, -, -, -, -⟩ := L3321.setting_facts c.nf.hyp c.TL
  have hVp : a2Vp L T H ≤ a2V L T :=
    commutator_le_left_of_le_normalizer'
      ((CFSG.Quasithin.oTwoUpper_le H).trans (c.nf.HLT.trans (sup_le hLV hTV)))
  have hAab : IsElemAbelian 2 (a2Vp L T H) := F7.isElemAbelian_mono hVe hVp
  have hA2 : IsPGroup 2 ↥(a2Vp L T H) := F7.isPGroup_of_isElemAbelian hAab
  have hnc := c.not_comm_le_Z (leaf_LSCV_of h7 h9 hGA) hxY hx3
  have hx : ∃ a ∈ a2Vp L T H, x * a * x⁻¹ * a⁻¹ ∉ (⊥ : Subgroup G) := by
    by_contra hcon
    push Not at hcon
    apply hnc
    rw [Subgroup.commutator_le]
    intro a ha b hb
    have hxa : x * a = a * x := by
      have h1 := Subgroup.mem_bot.mp (hcon a ha)
      calc x * a = (x * a * x⁻¹ * a⁻¹) * (a * x) := by group
        _ = a * x := by rw [h1, one_mul]
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    have hc : Commute a x := hxa.symm
    have h2 : a * x ^ n = x ^ n * a := (hc.zpow_right n).eq
    have e : ⁅a, x ^ n⁆ = 1 := by
      rw [commutatorElement_def]
      calc a * x ^ n * a⁻¹ * (x ^ n)⁻¹ = (x ^ n * a) * a⁻¹ * (x ^ n)⁻¹ := by rw [h2]
        _ = 1 := by group
    rw [e]
    exact (a2Z T).one_mem
  have hAX : ∀ N : Subgroup G, N ≤ a2Vp L T H → K ≤ Subgroup.normalizer (N : Set G) →
      a2Vp L T H ≤ Subgroup.normalizer (N : Set G) := by
    intro N hN _
    intro a ha
    refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun n hn => ?_)
    exact (F7.isElemAbelian_comm hAab (hN hn) ha)
  obtain ⟨N₀, N₁, hc, hZN₀, hN₁A, n, hn, hnn⟩ :=
    exists_chiefPair (X := K) (A := a2Vp L T H) (Z₀ := ⊥) hA2 hKN
      (fun _ _ => mem_normalizer_bot' _) (fun _ _ => mem_normalizer_bot' _) bot_le hAX hxK
      (by rw [hx3]; decide) hx
  have hN₁2 : IsPGroup 2 ↥N₁ := hA2.to_le hN₁A
  have hh : SecHyp K N₀ N₁ := hc.secHyp hN₁2
  obtain ⟨W, _, _, _, ⟨s⟩⟩ := exists_secRep hh
  have hρ : ∀ k : ↥K, (k : G) ∈ pCoreOf 2 K → s.ρ k = 1 :=
    SecRep.ρ_eq_one_of_normal_pgroup hc hh s (CFSG.LieType.BorelTits.pCoreOf_le 2 K)
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K)
      (fun y hy p hp => conj_mem_pCoreOf_of_mem_normalizer (Subgroup.le_normalizer hy) hp)
  have hker : CFSG.pCore 2 ↥K ≤ s.ρ.ker := by
    intro k hk
    rw [MonoidHom.mem_ker]
    exact hρ k (Subgroup.mem_map_of_mem K.subtype hk)
  let rb : (↥K ⧸ CFSG.pCore 2 ↥K) →* (W ≃ₗ[ZMod 2] W) := QuotientGroup.lift _ s.ρ hker
  have hrb : ∀ k : ↥K, rb (k : ↥K ⧸ CFSG.pCore 2 ↥K) = s.ρ k := fun k => rfl
  have hxne : s.ρ ⟨x, hxK⟩ ≠ 1 := by
    intro h1
    have h2 : s.ρ ⟨x, hxK⟩ (s.cl ⟨n, hn⟩) = s.cl ⟨n, hn⟩ := by
      rw [h1]; rfl
    exact hnn ((SecRep.fix_iff hh s _ ⟨n, hn⟩).mp h2)
  have h10 : 10 ≤ Module.finrank (ZMod 2) W :=
    hG1 q c.q_prime c.q_mod _ c.model W rb ⟨(⟨x, hxK⟩ : ↥K), by rw [hrb]; exact hxne⟩
  haveI : Module.Finite (ZMod 2) W := Module.finite_iff_finite.mpr inferInstance
  have hVcard := m.card_V_le
  have hA64 : Nat.card ↥(a2Vp L T H) ≤ 64 := (Subgroup.card_le_of_le hVp).trans hVcard
  have hN64 : Nat.card ↥N₁ ≤ 64 := (Subgroup.card_le_of_le hN₁A).trans hA64
  have hW64 : Nat.card (Multiplicative W) ≤ 64 :=
    (Nat.card_le_card_of_surjective _ s.surj).trans hN64
  have hWcard : Nat.card W = 2 ^ Module.finrank (ZMod 2) W := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := W), Nat.card_zmod]
  have hMW : Nat.card (Multiplicative W) = Nat.card W := Nat.card_congr Multiplicative.toAdd
  have h1024 : 2 ^ 10 ≤ 2 ^ Module.finrank (ZMod 2) W := Nat.pow_le_pow_right (by norm_num) h10
  rw [hMW, hWcard] at hW64
  omega

end CFSG.Quasithin.H13.NFa2
