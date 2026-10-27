module

public import CFSG.Quasithin.Vol2.Ch3Sec3NFa2LKey
public import CFSG.Quasithin.Vol2.Ch3Sec3NFa2G23
public import CFSG.Quasithin.Vol2.Ch3Sec3NFa2E6

public section

namespace CFSG.Quasithin.H13.NFa2

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Quasithin
open CFSG.QuasithinUnique.Vol2Native (A37ForSQTKCat A38ForSQTKCat A39ForSQTKCat)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T M L D H K : Subgroup G} {q : ℕ}

theorem mem_normalizer_bot' (g : G) : g ∈ Subgroup.normalizer ((⊥ : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  simp only [SetLike.mem_coe, Subgroup.mem_bot]
  constructor
  · rintro rfl
    simp
  · intro h1
    have : g * h = g := mul_inv_eq_one.mp h1
    exact mul_eq_left.mp this

theorem A2Cfg.charTwo_G2 (h36 : A36ForSQTK) (c : A2Cfg G T M L D H K q) :
    CharTwo (a2G2 K T) := by
  have hZ0 : a2Z T ≠ ⊥ :=
    quasithinOmegaOneCenter_ne_bot c.nf.hyp.sylow.1 c.nf.hyp.toSetup331.T_ne_bot
  have hZT : a2Z T ≤ T := (Subgroup.closure_le _).2 fun _ hz => hz.1.1
  have hP2 : IsPGroup 2 (a2Z T) := c.nf.hyp.sylow.1.to_le hZT
  have hG2 : a2G2 K T ≤ Subgroup.centralizer (a2Z T : Set G) := c.G2_le_centralizer_Z h36
  have hZP : a2Z T ≤ pCoreOf 2 (a2G2 K T) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hZT.trans le_sup_right)
      (hG2.trans (Subgroup.centralizer_le_normalizer _)) hP2
  have hO : pCoreOf 2 (a2G2 K T) ≠ ⊥ := fun h => hZ0 (le_bot_iff.mp (h ▸ hZP))
  exact charTwo_of_inH' c.nf.hyp.qtke c.nf.hyp.sylow ⟨le_sup_right, hO⟩

theorem A2Cfg.exists_nontriv_N0 (h36 : A36ForSQTK) (h37 : A37ForSQTKCat) (h38 : A38ForSQTKCat)
    (c : A2Cfg G T M L D H K q) {x : G} (hxK : x ∈ K)
    (hx3 : orderOf x = 3) : ∃ a ∈ a2N0 K T, x * a * x⁻¹ * a⁻¹ ∉ (⊥ : Subgroup G) := by
  by_contra hcon
  push Not at hcon
  have hKX : K ≤ a2G2 K T := (le_conjClosure K T).trans le_sup_left
  have hxX : x ∈ a2G2 K T := hKX hxK
  have hG2N : a2G2 K T ≤ Subgroup.normalizer (a2K0 K T : Set G) :=
    sup_le Subgroup.le_normalizer (le_normalizer_conjClosure K T)
  have hXA : a2G2 K T ≤ Subgroup.normalizer (a2N0 K T : Set G) :=
    hG2N.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 (a2K0 K T))
  have hTCX : a2TC K T ≤ a2G2 K T := CFSG.LieType.BorelTits.pCoreOf_le 2 _
  have hTCn : a2G2 K T ≤ Subgroup.normalizer (a2TC K T : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _
  have hN₀2 : IsPGroup 2 ↥(a2N0 K T) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have h1 : ∀ n ∈ a2TC K T, x * n * x⁻¹ * n⁻¹ ∈ a2N0 K T := by
    intro n hn
    have hnR : n ∈ Subgroup.normalizer (K : Set G) := c.R_le_normalizer_K h37 h38 (c.TC_le_R hn)
    have hK₁ : x * n * x⁻¹ * n⁻¹ ∈ K := by
      have e : x * n * x⁻¹ * n⁻¹ = x * (n * x⁻¹ * n⁻¹) := by group
      rw [e]
      exact K.mul_mem hxK ((Subgroup.mem_normalizer_iff.mp hnR x⁻¹).mp (K.inv_mem hxK))
    have hT₁ : x * n * x⁻¹ * n⁻¹ ∈ a2TC K T := by
      have hxn : x * n * x⁻¹ ∈ a2TC K T := (Subgroup.mem_normalizer_iff.mp (hTCn hxX) n).mp hn
      exact (a2TC K T).mul_mem hxn ((a2TC K T).inv_mem hn)
    have hXN : a2K0 K T ≤ Subgroup.normalizer ((a2K0 K T ⊓ a2TC K T : Subgroup G) : Set G) :=
      F7.le_normalizer_inf Subgroup.le_normalizer
        (fun y hy => CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _ (Subgroup.mem_sup_left hy))
    have hXle : a2K0 K T ⊓ a2TC K T ≤ a2N0 K T :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left hXN
        ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _).to_le inf_le_right)
    exact hXle (Subgroup.mem_inf.mpr ⟨le_conjClosure K T hK₁, hT₁⟩)
  have h2 := odd_centralizes_of_stable (k := x) (by rw [hx3]; decide) (Z₀ := ⊥)
    (N₀ := a2N0 K T) (N₁ := a2TC K T) bot_le c.N0_le_TC hN₀2
    (fun _ _ => mem_normalizer_bot' _) (fun y hy => hXA (hTCX hy))
    (mem_normalizer_bot' _) (hXA hxX) (hTCn hxX) hcon h1
  have hxC : x ∈ Subgroup.centralizer (pCoreOf 2 (a2G2 K T) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro n hn
    have := h2 n hn
    rw [Subgroup.mem_bot, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at this
    exact this.symm
  have hxP : x ∈ pCoreOf 2 (a2G2 K T) := c.charTwo_G2 h36 (Subgroup.mem_inf.mpr ⟨hxX, hxC⟩)
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _))
    ⟨x, hxP⟩
  rw [Subgroup.orderOf_mk, hx3] at hk
  have h3 : (3 : ℕ) ∣ 2 ^ k := ⟨1, by omega⟩
  have h32 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
  norm_num at h32

theorem centralizerMod_bot_zpowers (A : Subgroup G) (c : G) :
    centralizerMod ⊥ A (Subgroup.zpowers c) = A ⊓ Subgroup.centralizer ({c} : Set G) := by
  ext x
  rw [mem_centralizerMod, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  constructor
  · rintro ⟨hxA, -, hx⟩
    refine ⟨hxA, fun y hy => ?_⟩
    rw [Set.mem_singleton_iff] at hy
    subst hy
    have := hx y (Subgroup.mem_zpowers y)
    rw [Subgroup.mem_bot, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at this
    exact this.symm
  · rintro ⟨hxA, hx⟩
    refine ⟨hxA, mem_normalizer_bot' _, fun u hu => ?_⟩
    have hc : x * c = c * x := (hx c rfl).symm
    have hcomm : Commute x c := hc
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    have : x * c ^ n = c ^ n * x := (hcomm.zpow_right n).eq
    rw [Subgroup.mem_bot, mul_inv_eq_one, mul_inv_eq_iff_eq_mul]
    exact this

theorem leaf_C1_of
    (h36 : A36ForSQTK) (h5 : Stmt3_3_5) (h7 : Stmt3_3_7) (h9 : Stmt3_3_9) (h128 : Lemma128Two)
    (h37 : A37ForSQTKCat) (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat) : Leaf_C1 := by
  intro hG1 hG3 G _ _ T M L D H K q c t ht htK r hr h1 h2
  obtain ⟨x, hxY, hxK, hx3⟩ := c.exists_x h37 h38
  obtain ⟨a, haA, ha⟩ := c.exists_nontriv_N0 h36 h37 h38 hxK hx3
  have hKX : K ≤ a2G2 K T := (le_conjClosure K T).trans le_sup_left
  have hG2N : a2G2 K T ≤ Subgroup.normalizer (a2K0 K T : Set G) :=
    sup_le Subgroup.le_normalizer (le_normalizer_conjClosure K T)
  have hAX : a2N0 K T ≤ a2G2 K T :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 (conjClosure K T)).trans le_sup_left
  have hkey := (a2_keyBounds hG1 nfa2_G2 hG3 h5 h7 h9 h128 h37 h38 h39 c ht htK
    (A := a2N0 K T) (Z₀ := ⊥) (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _) hAX
    (hG2N.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 (a2K0 K T)))
    (fun _ _ => mem_normalizer_bot' _) bot_le hxK
    (by rw [hx3]; decide) ⟨a, haA, ha⟩).2 r hr h1 h2
  rw [centralizerMod_bot_zpowers] at hkey
  exact hkey

end CFSG.Quasithin.H13.NFa2
