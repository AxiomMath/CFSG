module

public import CFSG.Quasithin.Recognition.St84.Sec4Comm
public import CFSG.Quasithin.Recognition.St84.Sec4QuotA
public import CFSG.RankThree.GF2n.QuadraticSection
public import CFSG.Timmesfeld.LocalTwoSubgroups.CoprimeActionBounds
public import CFSG.GroupTheory.Commutator.JoinNormalizer
public import CFSG.Quasithin.Background.RonanF713Sylow
public import CFSG.Quasithin.Background.RonanF13Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CentralizerSup
public import CFSG.GroupTheory.GroupAction.CoprimeFiniteSubgroups

public section

namespace CFSG.Quasithin.St84

open SimpleGraph CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.Fan86
  CFSG.Quasithin.F6.GoldAmL3T

open scoped Pointwise commutatorElement

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V} {s : ℕ}

namespace Setup

variable (X : Setup Γ G)
variable {r : ℕ}

private abbrev Qg' (a : ℤ) : Subgroup G := pCoreOf 2 (X.arcStab a (a + (r : ℤ)))

private theorem s45_step10 (H : X.Sec4Hyp s r) {d₀ d₁ : ℕ} (hd₀ : X.HasB 0 d₀)
    (hd₁ : X.HasB 1 d₁)
    (hna : ¬ ⁅X.Z 1, X.Z ((d₁ : ℤ) + 1)⁆ ≤ X.Z 1 ⊓ X.Z ((d₁ : ℤ) + 1))
    (hodd₀ : Odd d₀) :
    2 * d₀ + 4 = r ∧ 2 * d₁ = r := by
  obtain ⟨hlt, hodd₁, -, -⟩ := X.s45_lt_odd_of_not_comm_le H hd₀ hd₁ hna
  obtain ⟨b0, hb0⟩ := hodd₀
  obtain ⟨b1, hb1⟩ := hodd₁
  have hd : d₀ + 2 ≤ d₁ := by omega
  obtain ⟨h0l, h0r⟩ := X.hasB_zero_bounds H hd₀
  obtain ⟨h1l, h1r⟩ := X.hasB_one_bounds H hd₁
  constructor <;> omega

private theorem Z_one_le_edgeSylow (H : X.Sec4Hyp s r) {d₁ : ℕ} (hd₁ : X.HasB 1 d₁) :
    X.Z 1 ≤ X.edgeSylow (d₁ : ℤ) := by
  have hd1 : 1 ≤ d₁ := X.one_le_of_hasB hd₁
  have hfix := X.fixSet_Z 1 hd₁
  have hZle1 : X.Z 1 ≤ X.Gi (d₁ : ℤ) := by
    intro z hz
    refine MulAction.mem_stabilizer_iff.mpr ?_
    have hmem : (d₁ : ℤ) ∈ X.fixSet (X.Z 1) := by
      rw [hfix]
      simp only [Set.mem_Icc]
      omega
    exact hmem z hz
  have hZle2 : X.Z 1 ≤ X.Gi ((d₁ : ℤ) + 1) := by
    intro z hz
    refine MulAction.mem_stabilizer_iff.mpr ?_
    have hmem : ((d₁ : ℤ) + 1) ∈ X.fixSet (X.Z 1) := by
      rw [hfix]
      simp only [Set.mem_Icc]
      omega
    exact hmem z hz
  have hQle1 : X.Q ((d₁ : ℤ) + 1) ≤ X.Gi (d₁ : ℤ) := by
    have h := X.Q_le_edgeSylow_right ((d₁ : ℤ) + 1)
    rw [show (d₁ : ℤ) + 1 - 1 = (d₁ : ℤ) by ring] at h
    exact h.trans ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans inf_le_left)
  have hQle2 : X.Q ((d₁ : ℤ) + 1) ≤ X.Gi ((d₁ : ℤ) + 1) := X.Q_le_Gi _
  haveI : Finite ↥(X.Gi (d₁ : ℤ) ⊓ X.Gi ((d₁ : ℤ) + 1)) :=
    finite_of_le_stabilizer X.hyp (H := X.Gi (d₁ : ℤ) ⊓ X.Gi ((d₁ : ℤ) + 1)) inf_le_left
  have hPle : (X.Z 1 ⊔ X.Q ((d₁ : ℤ) + 1) : Subgroup G) ≤
      (X.Gi (d₁ : ℤ) ⊓ X.Gi ((d₁ : ℤ) + 1) : Subgroup G) :=
    sup_le (le_inf hZle1 hZle2) (le_inf hQle1 hQle2)
  have hnorm : X.Z 1 ≤ Subgroup.normalizer (X.Q ((d₁ : ℤ) + 1) : Set G) :=
    hZle2.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi ((d₁ : ℤ) + 1)))
  have hP2 : IsPGroup 2 (X.Z 1 ⊔ X.Q ((d₁ : ℤ) + 1) : Subgroup G) :=
    IsPGroup.to_sup_of_normal_right'
      ((pCoreOf_isPGroup' (X.Gi 1)).to_le (X.Z_le_Q 1))
      (pCoreOf_isPGroup' (X.Gi ((d₁ : ℤ) + 1))) hnorm
  have hPS : (X.Z 1 ⊔ X.Q ((d₁ : ℤ) + 1) : Subgroup G) ≤ X.edgeSylow (d₁ : ℤ) :=
    le_of_normal_isSylowTwoOf (X.isSylowTwoOf_edgeSylow (d₁ : ℤ))
      (X.edgeSylow_subgroupOf_normal (d₁ : ℤ)) hPle hP2
  exact le_trans le_sup_left hPS

private theorem Z_one_eq_Qg' (H : X.Sec4Hyp s r) {d₀ d₁ : ℕ} (hd₀ : X.HasB 0 d₀)
    (hd₁ : X.HasB 1 d₁)
    (hna : ¬ ⁅X.Z 1, X.Z ((d₁ : ℤ) + 1)⁆ ≤ X.Z 1 ⊓ X.Z ((d₁ : ℤ) + 1))
    (hodd₀ : Odd d₀) :
    X.Z 1 = X.Qg' (r := r) (1 - (d₁ : ℤ)) ∧ Nat.card (X.Z 1) = 2 ^ X.n 0 ∧
      X.Z 1 ⊓ X.Q ((d₁ : ℤ) + 1) = ⊥ := by
  have hr1 : 2 * d₁ = r := (X.s45_step10 H hd₀ hd₁ hna hodd₀).2
  have hrcast : (r : ℤ) = 2 * (d₁ : ℤ) := by omega
  have hZne : X.Z 1 ≠ ⊥ := X.Z_ne_bot_of 1 (X.Q_ne_bot H.char 1)
  have hZ2 : IsPGroup 2 (X.Z 1) := (pCoreOf_isPGroup' (X.Gi 1)).to_le (X.Z_le_Q 1)
  have hKZ : X.K ≤ Subgroup.normalizer (X.Z 1 : Set G) := by
    intro k hk
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    change conjSub k (X.Z 1) = X.Z 1
    exact X.Z_normal 1 k (X.K_le_Gi 1 hk)
  have hfix := X.fixSet_Z 1 hd₁
  have hle_arc : X.Z 1 ≤ X.arcStab (1 - (d₁ : ℤ)) ((1 - (d₁ : ℤ)) + (r : ℤ)) := by
    apply X.le_arcStab_of_fixSet
    intro j hj
    rw [hfix]
    simp only [Set.mem_Icc] at hj ⊢
    rw [hrcast] at hj
    omega
  have hleQg : X.Z 1 ≤ X.Qg' (r := r) (1 - (d₁ : ℤ)) :=
    X.le_pCoreOf_arcStab_r H hZ2 hle_arc
  have hEqQg : X.Z 1 = X.Qg' (r := r) (1 - (d₁ : ℤ)) :=
    X.eq_of_le_pCoreOf_arcStab_r H hKZ hZne hleQg
  have hQgne : X.Qg' (r := r) (1 - (d₁ : ℤ)) ≠ ⊥ := by rw [← hEqQg]; exact hZne
  have hcard : Nat.card (X.Z 1) = 2 ^ X.n 0 := by
    have hn : X.n (1 - (d₁ : ℤ)) = X.n 0 := by
      obtain ⟨k, hk⟩ := (X.s45_lt_odd_of_not_comm_le H hd₀ hd₁ hna).2.1
      rw [show (1 : ℤ) - (d₁ : ℤ) = 0 + 2 * (-(k : ℤ)) by omega, X.n_add]
    rw [hEqQg, ← hn]
    exact (X.pCoreOf_arcStab_r H (1 - (d₁ : ℤ)) hQgne).1
  have hsum : (1 : ℤ) - (d₁ : ℤ) + (r : ℤ) = (d₁ : ℤ) + 1 := by
    rw [hrcast]; ring
  have hinf : X.Z 1 ⊓ X.Q ((d₁ : ℤ) + 1) = ⊥ := by
    rw [hEqQg]
    have h := (X.pCoreOf_arcStab_r H (1 - (d₁ : ℤ)) hQgne).2.2.1
    simpa [Setup.Qg', hsum] using h
  exact ⟨hEqQg, hcard, hinf⟩

private theorem K_transitive_on_Z_one (H : X.Sec4Hyp s r) {d₀ d₁ : ℕ}
    (hd₀ : X.HasB 0 d₀) (hd₁ : X.HasB 1 d₁)
    (hna : ¬ ⁅X.Z 1, X.Z ((d₁ : ℤ) + 1)⁆ ≤ X.Z 1 ⊓ X.Z ((d₁ : ℤ) + 1))
    (hodd₀ : Odd d₀) :
    ∀ x ∈ X.Z 1, x ≠ 1 → ∀ y ∈ X.Z 1, y ≠ 1 →
      ∃ k ∈ X.K, k * x * k⁻¹ = y := by
  obtain ⟨-, -, hinf⟩ := X.Z_one_eq_Qg' H hd₀ hd₁ hna hodd₀
  have hZle : X.Z 1 ≤ X.edgeSylow (d₁ : ℤ) := X.Z_one_le_edgeSylow H hd₁
  intro x hx hx1 y hy hy1
  have hxS : x ∈ X.edgeSylow (d₁ : ℤ) := hZle hx
  have hyS : y ∈ X.edgeSylow (d₁ : ℤ) := hZle hy
  have hxQ : x ∉ X.Q ((d₁ : ℤ) + 1) := by
    intro h
    have : x ∈ X.Z 1 ⊓ X.Q ((d₁ : ℤ) + 1) := ⟨hx, h⟩
    rw [hinf] at this
    exact hx1 (Subgroup.mem_bot.mp this)
  have hyQ : y ∉ X.Q ((d₁ : ℤ) + 1) := by
    intro h
    have : y ∈ X.Z 1 ⊓ X.Q ((d₁ : ℤ) + 1) := ⟨hy, h⟩
    rw [hinf] at this
    exact hy1 (Subgroup.mem_bot.mp this)
  obtain ⟨k, hkK, hk⟩ := X.exists_conj_mem_pCoreOf (i := (d₁ : ℤ)) hxS hyS hxQ hyQ
  have hkx : k * x * k⁻¹ ∈ X.Z 1 := by
    have hZk : conjSub k (X.Z 1) = X.Z 1 := X.Z_normal 1 k (X.K_le_Gi 1 hkK.1)
    rw [← hZk, mem_conjSub]
    rw [show k⁻¹ * (k * x * k⁻¹) * k = x by group]
    exact hx
  have hmem : k * x * k⁻¹ * y⁻¹ ∈ X.Z 1 ⊓ X.Q ((d₁ : ℤ) + 1) :=
    ⟨(X.Z 1).mul_mem hkx ((X.Z 1).inv_mem hy), hk⟩
  rw [hinf] at hmem
  have hone : k * x * k⁻¹ * y⁻¹ = 1 := Subgroup.mem_bot.mp hmem
  refine ⟨k, hkK.1, ?_⟩
  calc k * x * k⁻¹ = k * x * k⁻¹ * y⁻¹ * y := by group
    _ = y := by rw [hone, one_mul]

private theorem sylow_centralizes_Z_one (H : X.Sec4Hyp s r) {d₀ d₁ : ℕ}
    (hd₀ : X.HasB 0 d₀) (hd₁ : X.HasB 1 d₁)
    (hna : ¬ ⁅X.Z 1, X.Z ((d₁ : ℤ) + 1)⁆ ≤ X.Z 1 ⊓ X.Z ((d₁ : ℤ) + 1))
    (hodd₀ : Odd d₀) {P : Subgroup G} (hP : IsSylowTwoOf P (X.Gi 1)) (hPne : P ≠ ⊥)
    (hKP : X.K ≤ Subgroup.normalizer (P : Set G)) :
    P ≤ Subgroup.centralizer (X.Z 1 : Set G) := by
  have htrans := X.K_transitive_on_Z_one H hd₀ hd₁ hna hodd₀
  have hzfacts := X.centerOf_sylow_le_Z H.char 1 hP
  set C : Subgroup G := X.Z 1 ⊓ Subgroup.centralizer (P : Set G) with hC
  have hCeq : C = centerOf P := hzfacts.2
  haveI : Finite ↥P := finite_of_le_stabilizer X.hyp (H := P) hP.1
  have hcenterne : centerOf P ≠ ⊥ := by
    intro hbot
    have hnt : Nontrivial ↥P :=
      Finite.one_lt_card_iff_nontrivial.mp ((Subgroup.one_lt_card_iff_ne_bot P).mpr hPne)
    haveI := hnt
    have hlt : ⊥ < Subgroup.center ↥P := IsPGroup.bot_lt_center hP.2.1
    obtain ⟨z, hz, hz1⟩ :=
      (Subgroup.bot_or_exists_ne_one (Subgroup.center ↥P)).resolve_left (ne_of_gt hlt)
    have hzG : (z : G) ∈ centerOf P := by
      refine Subgroup.mem_inf.mpr ⟨z.2, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      exact congrArg (fun t : ↥P => (t : G))
        (Subgroup.mem_center_iff.mp hz (⟨w, hw⟩ : ↥P))
    have hz1' : (z : G) ≠ 1 := fun h1 => hz1 (Subtype.ext (by simpa using h1))
    rw [hbot] at hzG
    exact hz1' (Subgroup.mem_bot.mp hzG)
  have hCne : C ≠ ⊥ := by rw [hCeq]; exact hcenterne
  have hCZ : C = X.Z 1 := by
    refine le_antisymm inf_le_left ?_
    intro z hz
    by_cases hz1 : z = 1
    · rw [hz1]; exact C.one_mem
    · obtain ⟨c, hcC, hc1⟩ := (Subgroup.bot_or_exists_ne_one C).resolve_left hCne
      have hcZ : c ∈ X.Z 1 := (Subgroup.mem_inf.mp hcC).1
      obtain ⟨k, hkK, hk⟩ := htrans c hcZ hc1 z hz hz1
      rw [← hk]
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · have hZk : conjSub k (X.Z 1) = X.Z 1 := X.Z_normal 1 k (X.K_le_Gi 1 hkK)
        rw [← hZk, mem_conjSub]
        rw [show k⁻¹ * (k * c * k⁻¹) * k = c by group]
        exact hcZ
      · rw [Subgroup.mem_centralizer_iff]
        intro s hs
        have hPk : conjSub k⁻¹ P = P := by
          have hk' : k⁻¹ ∈ Subgroup.normalizer (P : Set G) :=
            Subgroup.inv_mem (Subgroup.normalizer (P : Set G)) (hKP hkK)
          exact Subgroup.mem_normalizer_iff_map_conj_eq.mp hk'
        have hs' : k⁻¹ * s * k ∈ P := by
          rw [← hPk, mem_conjSub]
          rw [show k⁻¹⁻¹ * (k⁻¹ * s * k) * k⁻¹ = s by group]
          exact hs
        have hcomm := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hcC).2
          (k⁻¹ * s * k) hs'
        have e1 : (k * c * k⁻¹) * s = k * (c * (k⁻¹ * s * k)) * k⁻¹ := by group
        have e2 : s * (k * c * k⁻¹) = k * ((k⁻¹ * s * k) * c) * k⁻¹ := by group
        rw [e1, e2, hcomm]
  intro s hs
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  have hzC : z ∈ C := by rw [hCZ]; exact hz
  exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hzC).2 s hs).symm

private theorem L_one_le_centralizer_Z_one (H : X.Sec4Hyp s r) {d₀ d₁ : ℕ}
    (hd₀ : X.HasB 0 d₀) (hd₁ : X.HasB 1 d₁)
    (hna : ¬ ⁅X.Z 1, X.Z ((d₁ : ℤ) + 1)⁆ ≤ X.Z 1 ⊓ X.Z ((d₁ : ℤ) + 1))
    (hodd₀ : Odd d₀) :
    X.L 1 ≤ Subgroup.centralizer (X.Z 1 : Set G) := by
  have h0 : X.edgeSylow 0 ≤ Subgroup.centralizer (X.Z 1 : Set G) := by
    refine X.sylow_centralizes_Z_one H hd₀ hd₁ hna hodd₀ ?_ ?_ ?_
    · simpa using X.isSylowTwoOf_edgeSylow_Gi_succ 0
    · intro h
      have hQ : X.Q 0 ≤ X.edgeSylow 0 := X.Q_le_edgeSylow_left 0
      rw [h] at hQ
      exact X.Q_ne_bot H.char 0 (le_bot_iff.mp hQ)
    · exact (le_inf (X.K_le_Gi 0) (X.K_le_Gi 1)).trans
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 0 ⊓ X.Gi 1))
  have h1 : X.edgeSylow 1 ≤ Subgroup.centralizer (X.Z 1 : Set G) := by
    refine X.sylow_centralizes_Z_one H hd₀ hd₁ hna hodd₀ ?_ ?_ ?_
    · exact X.isSylowTwoOf_edgeSylow_Gi 1
    · intro h
      have hQ : X.Q 1 ≤ X.edgeSylow 1 := X.Q_le_edgeSylow_left 1
      rw [h] at hQ
      exact X.Q_ne_bot H.char 1 (le_bot_iff.mp hQ)
    · exact (le_inf (X.K_le_Gi 1) (X.K_le_Gi 2)).trans
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 1 ⊓ X.Gi 2))
  rw [← X.edgeSylow_sup_edgeSylow 1]
  exact sup_le h0 h1

private theorem s45_step11 (H : X.Sec4Hyp s r) {d₀ d₁ : ℕ} (hd₀ : X.HasB 0 d₀)
    (hd₁ : X.HasB 1 d₁)
    (hna : ¬ ⁅X.Z 1, X.Z ((d₁ : ℤ) + 1)⁆ ≤ X.Z 1 ⊓ X.Z ((d₁ : ℤ) + 1))
    (hodd₀ : Odd d₀) :
    X.Z 1 = centerOf (X.L 1) ∧ Nat.card (X.Z 1) = 2 ^ X.n 0 ∧
      X.Z 1 = X.Qg' (r := r) (1 - (d₁ : ℤ)) ∧ ⁅X.Z 0, X.Z d₀⁆ = ⊥ := by
  obtain ⟨hEqQg, hcard, hinf⟩ := X.Z_one_eq_Qg' H hd₀ hd₁ hna hodd₀
  have hL1cent := X.L_one_le_centralizer_Z_one H hd₀ hd₁ hna hodd₀
  have hZ1L : X.Z 1 ≤ X.L 1 := (X.Z_le_Q 1).trans (X.Q_le_L 1)
  have hZ1cent : X.Z 1 ≤ Subgroup.centralizer (X.L 1 : Set G) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact (Subgroup.mem_centralizer_iff.mp (hL1cent hl) z hz).symm
  have hZ1center : X.Z 1 = centerOf (X.L 1) :=
    le_antisymm (by intro z hz; exact Subgroup.mem_inf.mpr ⟨hZ1L hz, hZ1cent hz⟩)
      (X.centerOf_L_le_Z H.char 1)
  have hodd0Z : Odd (d₀ : ℤ) := by
    obtain ⟨m, hm⟩ := hodd₀
    exact ⟨m, by push_cast [hm]; ring⟩
  have hd0center : X.Z (d₀ : ℤ) = centerOf (X.L (d₀ : ℤ)) :=
    X.Z_eq_centerOf_of_even_sub (hodd0Z.sub_odd odd_one) hZ1center
  have hZ0L : X.Z 0 ≤ X.L (d₀ : ℤ) := by
    have hZG : X.Z 0 ≤ X.Gi (d₀ : ℤ) := by
      have h := hd₀.1 (d₀ : ℤ) (by simp)
      simpa using h
    exact le_oTwoPrime_of_isPGroup ((pCoreOf_isPGroup' (X.Gi 0)).to_le (X.Z_le_Q 0)) hZG
  have hcomm : ⁅X.Z 0, X.Z (d₀ : ℤ)⁆ = ⊥ := by
    rw [hd0center, eq_bot_iff, Subgroup.commutator_le]
    intro a ha b hb
    have hbcent : b ∈ Subgroup.centralizer (X.L (d₀ : ℤ) : Set G) := (Subgroup.mem_inf.mp hb).2
    have hcomm' : a * b = b * a :=
      Subgroup.mem_centralizer_iff.mp hbcent a (hZ0L ha)
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact hcomm'
  exact ⟨hZ1center, hcard, hEqQg, hcomm⟩

private theorem s45_step12 (H : X.Sec4Hyp s r) {d₀ d₁ : ℕ} (hd₀ : X.HasB 0 d₀)
    (hd₁ : X.HasB 1 d₁)
    (hna : ¬ ⁅X.Z 1, X.Z ((d₁ : ℤ) + 1)⁆ ≤ X.Z 1 ⊓ X.Z ((d₁ : ℤ) + 1))
    (hodd₀ : Odd d₀) :
    s < r := by
  by_contra hsr
  push Not at hsr
  have hpar : r + 1 = s := by
    have hle : s ≤ r + 1 := by
      have := H.le_r
      omega
    have hrs : r ≠ s := by
      intro hrs
      apply (Nat.not_even_iff_odd.mpr H.odd_s)
      have heven := H.even_r
      rwa [hrs] at heven
    omega
  have hswap := Sec4Hyp.swap X H hpar
  have hb : X.swap.HasB 1 d₀ := (X.hasB_swap (i := 1) (d := d₀)).mpr hd₀
  have hle := (X.swap.hasB_one_bounds hswap hb).2
  have h10 := (X.s45_step10 H hd₀ hd₁ hna hodd₀).1
  omega

private theorem d1_numeric (H : X.Sec4Hyp s r) {d₀ d₁ : ℕ} (hd₀ : X.HasB 0 d₀)
    (hd₁ : X.HasB 1 d₁)
    (hna : ¬ ⁅X.Z 1, X.Z ((d₁ : ℤ) + 1)⁆ ≤ X.Z 1 ⊓ X.Z ((d₁ : ℤ) + 1))
    (hodd₀ : Odd d₀) (h3 : d₁ = 3) :
    d₀ = 1 ∧ r = 6 ∧ s = 5 := by
  have hb := X.s45_step10 H hd₀ hd₁ hna hodd₀
  have hlt := X.s45_step12 H hd₀ hd₁ hna hodd₀
  have hr : r = 6 := by omega
  have hd0 : d₀ = 1 := by omega
  have hs : s = 5 := by
    obtain ⟨k, hk⟩ := H.odd_s
    have h5 := H.five_le
    omega
  exact ⟨hd0, hr, hs⟩

private theorem d1_card_Q1 (H : X.Sec4Hyp s r) {d₀ d₁ : ℕ} (hd₀ : X.HasB 0 d₀)
    (hd₁ : X.HasB 1 d₁)
    (hna : ¬ ⁅X.Z 1, X.Z ((d₁ : ℤ) + 1)⁆ ≤ X.Z 1 ⊓ X.Z ((d₁ : ℤ) + 1))
    (hodd₀ : Odd d₀) (h3 : d₁ = 3) :
    Nat.card (X.Q 1) = 2 ^ (3 * X.n 0 + X.n 1) := by
  obtain ⟨-, hr, hs⟩ := d1_numeric X H hd₀ hd₁ hna hodd₀ h3
  exact X.card_Q_one_of_s_five_of_r_six H hs hr

private theorem d1_Z1_le_Q0 (H : X.Sec4Hyp s r) {d₀ d₁ : ℕ} (hd₀ : X.HasB 0 d₀)
    (hd₁ : X.HasB 1 d₁)
    (hna : ¬ ⁅X.Z 1, X.Z ((d₁ : ℤ) + 1)⁆ ≤ X.Z 1 ⊓ X.Z ((d₁ : ℤ) + 1))
    (hodd₀ : Odd d₀) (h3 : d₁ = 3) :
    X.Z 1 ≤ X.Q 0 := by
  obtain ⟨hd0, hr, hs⟩ := d1_numeric X H hd₀ hd₁ hna hodd₀ h3
  subst h3; subst hd0; subst hr; subst hs
  have hZ1Qg : X.Z 1 = pCoreOf 2 (X.arcStab (-2) 4) := by
    have h := (X.s45_step11 H hd₀ hd₁ hna hodd₀).2.2.1
    rw [h]; norm_num [Setup.Qg']
  rw [hZ1Qg]
  exact X.pCoreOf_arcStab_le_Q_of_lt_of_lt (by norm_num) (by norm_num)

private theorem d1_Z1_le_Q2 (H : X.Sec4Hyp s r) {d₀ d₁ : ℕ} (hd₀ : X.HasB 0 d₀)
    (hd₁ : X.HasB 1 d₁)
    (hna : ¬ ⁅X.Z 1, X.Z ((d₁ : ℤ) + 1)⁆ ≤ X.Z 1 ⊓ X.Z ((d₁ : ℤ) + 1))
    (hodd₀ : Odd d₀) (h3 : d₁ = 3) :
    X.Z 1 ≤ X.Q 2 := by
  obtain ⟨hd0, hr, hs⟩ := d1_numeric X H hd₀ hd₁ hna hodd₀ h3
  subst h3; subst hd0; subst hr; subst hs
  have hZ1Qg : X.Z 1 = pCoreOf 2 (X.arcStab (-2) 4) := by
    have h := (X.s45_step11 H hd₀ hd₁ hna hodd₀).2.2.1
    rw [h]; norm_num [Setup.Qg']
  rw [hZ1Qg]
  exact X.pCoreOf_arcStab_le_Q_of_lt_of_lt (by norm_num) (by norm_num)

private theorem d1_Z0_sup_Q1 (H : X.Sec4Hyp s r) {d₀ d₁ : ℕ} (hd₀ : X.HasB 0 d₀)
    (hd₁ : X.HasB 1 d₁)
    (hna : ¬ ⁅X.Z 1, X.Z ((d₁ : ℤ) + 1)⁆ ≤ X.Z 1 ⊓ X.Z ((d₁ : ℤ) + 1))
    (hodd₀ : Odd d₀) (h3 : d₁ = 3) :
    X.Z 0 ⊔ X.Q 1 = X.S := by
  obtain ⟨hd0, hr, hs⟩ := d1_numeric X H hd₀ hd₁ hna hodd₀ h3
  subst h3; subst hd0; subst hr; subst hs
  have hKZ : X.K ≤ Subgroup.normalizer (X.Z 0 : Set G) := by
    intro k hk
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact X.Z_normal 0 k (X.K_le_Gi 0 hk)
  have hZle : X.Z 0 ≤ X.edgeSylow 0 := (X.Z_le_Q 0).trans (X.Q_le_edgeSylow_left 0)
  have hnot : ¬ X.Z 0 ≤ X.Q 1 := by
    intro h
    exact hd₀.2.1 (h.trans ((X.Q_le_Gi_adj 1).trans inf_le_right))
  have h := X.sup_Q_eq_edgeSylow_of_gen (0 : ℤ) (inf_le_left.trans hKZ) hZle hnot
  rwa [show X.edgeSylow 0 = X.S from rfl] at h

private theorem d1_Z2_sup_Q1 (H : X.Sec4Hyp s r) {d₀ d₁ : ℕ} (hd₀ : X.HasB 0 d₀)
    (hd₁ : X.HasB 1 d₁)
    (hna : ¬ ⁅X.Z 1, X.Z ((d₁ : ℤ) + 1)⁆ ≤ X.Z 1 ⊓ X.Z ((d₁ : ℤ) + 1))
    (hodd₀ : Odd d₀) (h3 : d₁ = 3) :
    X.Z 2 ⊔ X.Q 1 = X.edgeSylow 1 := by
  obtain ⟨hd0, hr, hs⟩ := d1_numeric X H hd₀ hd₁ hna hodd₀ h3
  subst h3; subst hd0; subst hr; subst hs
  have hd2 : X.HasB 2 1 :=
    (X.hasB_iff_of_even (i := 2) (j := 0) (by norm_num) 1).mpr hd₀
  have hKZ : X.K ≤ Subgroup.normalizer (X.Z 2 : Set G) := by
    intro k hk
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact X.Z_normal 2 k (X.K_le_Gi 2 hk)
  have hZle : X.Z 2 ≤ X.edgeSylow 1 := (X.Z_le_Q 2).trans (X.Q_le_edgeSylow (1:ℤ))
  have hnot : ¬ X.Z 2 ≤ X.Q 1 := by
    intro h
    exact hd2.2.2 (by simpa using (h.trans ((X.Q_le_Gi_adj 1).trans inf_le_left)))
  exact X.sup_Q_eq_edgeSylow_of_left_gen (1 : ℤ) (inf_le_left.trans hKZ) hZle hnot

private theorem d1_L1_eq (H : X.Sec4Hyp s r) {d₀ d₁ : ℕ} (hd₀ : X.HasB 0 d₀)
    (hd₁ : X.HasB 1 d₁)
    (hna : ¬ ⁅X.Z 1, X.Z ((d₁ : ℤ) + 1)⁆ ≤ X.Z 1 ⊓ X.Z ((d₁ : ℤ) + 1))
    (hodd₀ : Odd d₀) (h3 : d₁ = 3) :
    X.L 1 = (X.Z 0 ⊔ X.Z 2) ⊔ X.Q 1 := by
  have hZ0 := d1_Z0_sup_Q1 X H hd₀ hd₁ hna hodd₀ h3
  have hZ2 := d1_Z2_sup_Q1 X H hd₀ hd₁ hna hodd₀ h3
  obtain ⟨hd0, hr, hs⟩ := d1_numeric X H hd₀ hd₁ hna hodd₀ h3
  subst h3; subst hd0; subst hr; subst hs
  have hL := (X.edgeSylow_sup_edgeSylow 1).symm
  rw [show (1:ℤ) - 1 = 0 by norm_num] at hL
  have hZ0' : X.Z 0 ⊔ X.Q 1 = X.edgeSylow 0 := hZ0.trans rfl
  rw [hL, ← hZ0', ← hZ2]
  ac_rfl

private theorem d1_Z0_le_centralizer_of_le_Q0 {U : Subgroup G} (hU : U ≤ X.Q 0) :
    X.Z 0 ≤ Subgroup.centralizer (U : Set G) :=
  ((X.Z_le_center 0).trans inf_le_right).trans (Subgroup.centralizer_le hU)

private theorem d1_Q1_le_normalizers (H : X.Sec4Hyp s r) {d₀ d₁ : ℕ} (hd₀ : X.HasB 0 d₀)
    (hd₁ : X.HasB 1 d₁)
    (hna : ¬ ⁅X.Z 1, X.Z ((d₁ : ℤ) + 1)⁆ ≤ X.Z 1 ⊓ X.Z ((d₁ : ℤ) + 1))
    (hodd₀ : Odd d₀) (h3 : d₁ = 3) :
    X.Q 1 ≤ Subgroup.normalizer (X.Q 0 : Set G) ∧
      X.Q 1 ≤ Subgroup.normalizer (X.Q 2 : Set G) ∧
      X.Q 1 ≤ Subgroup.normalizer (X.Z 0 : Set G) ∧
      X.Q 1 ≤ Subgroup.normalizer (X.Z 2 : Set G) := by
  obtain ⟨hd0, hr, hs⟩ := d1_numeric X H hd₀ hd₁ hna hodd₀ h3
  subst h3; subst hd0; subst hr; subst hs
  have hQ0norm : X.Gi 0 ≤ Subgroup.normalizer (X.Q 0 : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 0)
  have hQ2norm : X.Gi 2 ≤ Subgroup.normalizer (X.Q 2 : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 2)
  have hZ0norm : X.Gi 0 ≤ Subgroup.normalizer (X.Z 0 : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact X.Z_normal 0 g hg
  have hZ2norm : X.Gi 2 ≤ Subgroup.normalizer (X.Z 2 : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact X.Z_normal 2 g hg
  have hQ1le0 : X.Q 1 ≤ X.Gi 0 := (X.Q_le_Gi_adj 1).trans inf_le_left
  have hQ1le2 : X.Q 1 ≤ X.Gi 2 := (X.Q_le_Gi_adj 1).trans inf_le_right
  exact ⟨hQ1le0.trans hQ0norm, hQ1le2.trans hQ2norm, hQ1le0.trans hZ0norm,
    hQ1le2.trans hZ2norm⟩

private theorem d1_Q1_inf_Q0_eq (H : X.Sec4Hyp s r) {d₀ d₁ : ℕ} (hd₀ : X.HasB 0 d₀)
    (hd₁ : X.HasB 1 d₁)
    (hna : ¬ ⁅X.Z 1, X.Z ((d₁ : ℤ) + 1)⁆ ≤ X.Z 1 ⊓ X.Z ((d₁ : ℤ) + 1))
    (hodd₀ : Odd d₀) (h3 : d₁ = 3) :
    X.Q 1 ⊓ X.Q 0 = (X.Z 0 ⊓ X.Q 1) ⊔ (X.Q 0 ⊓ X.Q 2) := by
  obtain ⟨hd0, hr, hs⟩ := d1_numeric X H hd₀ hd₁ hna hodd₀ h3
  subst h3; subst hd0; subst hr; subst hs
  obtain ⟨hQ1N0, hQ1N2, hQ1NZ0, hQ1NZ2⟩ := d1_Q1_le_normalizers X H hd₀ hd₁ hna hodd₀ rfl
  have hrev := (X.reverse).Q_quot_comm H.char H.sing (by norm_num : 4 ≤ 5) (-1)
  have hcomm_eq : X.Q 1 ⊓ X.Q 0 = ⁅X.Q 1 ⊓ X.Q 2, X.Q 0⁆ ⊔ (X.Q 0 ⊓ X.Q 2) := by
    simpa [inf_comm] using hrev.2
  have hquot := X.Q_quot H.char H.sing (by norm_num : 4 ≤ 5) 1
  have hW0leQ0 : X.Z 0 ⊓ X.Q 1 ≤ X.Q 0 := fun x hx => X.Z_le_Q 0 hx.1
  have hA'leQ0 : X.Q 0 ⊓ X.Q 2 ≤ X.Q 0 := inf_le_left
  have hZ0NW0 : X.Z 0 ≤ Subgroup.normalizer ((X.Z 0 ⊓ X.Q 1 : Subgroup G) : Set G) :=
    (d1_Z0_le_centralizer_of_le_Q0 X hW0leQ0).trans
      (Subgroup.centralizer_le_normalizer ((X.Z 0 ⊓ X.Q 1 : Subgroup G) : Set G))
  have hZ0NA' : X.Z 0 ≤ Subgroup.normalizer ((X.Q 0 ⊓ X.Q 2 : Subgroup G) : Set G) :=
    (d1_Z0_le_centralizer_of_le_Q0 X hA'leQ0).trans
      (Subgroup.centralizer_le_normalizer ((X.Q 0 ⊓ X.Q 2 : Subgroup G) : Set G))
  have hQ1NW0 : X.Q 1 ≤ Subgroup.normalizer ((X.Z 0 ⊓ X.Q 1 : Subgroup G) : Set G) :=
    (le_inf hQ1NZ0 Subgroup.le_normalizer).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hQ1NA' : X.Q 1 ≤ Subgroup.normalizer ((X.Q 0 ⊓ X.Q 2 : Subgroup G) : Set G) :=
    (le_inf hQ1N0 hQ1N2).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hAC : ⁅X.Z 0, X.Q 1 ⊓ X.Q 2⁆ ≤ (X.Z 0 ⊓ X.Q 1) ⊔ (X.Q 0 ⊓ X.Q 2) := by
    have h1 : X.Q 1 ⊓ X.Q 2 ≤ Subgroup.normalizer (X.Z 0 : Set G) :=
      (inf_le_left : X.Q 1 ⊓ X.Q 2 ≤ X.Q 1).trans hQ1NZ0
    have hle : ⁅X.Q 1 ⊓ X.Q 2, X.Z 0⁆ ≤ X.Z 0 :=
      Subgroup.le_normalizer_iff_commutator_le_right.mp h1
    have h2 : ⁅X.Q 1 ⊓ X.Q 2, X.Z 0⁆ ≤ X.Q 1 := by
      have hZ0norm : X.Z 0 ≤ Subgroup.normalizer (X.Q 1 : Set G) := by
        have h : X.Gi 1 ≤ Subgroup.normalizer (X.Q 1 : Set G) :=
          CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 1)
        have hZ0le : X.Z 0 ≤ X.Gi 1 := fun z hz =>
          (X.Q_le_Gi_adj 0).trans inf_le_right (X.Z_le_Q 0 hz)
        exact hZ0le.trans h
      have hle' : ⁅X.Z 0, X.Q 1 ⊓ X.Q 2⁆ ≤ X.Q 1 :=
        (Subgroup.commutator_mono_right inf_le_left).trans
          (Subgroup.le_normalizer_iff_commutator_le_right.mp hZ0norm)
      rwa [Subgroup.commutator_comm] at hle'
    calc ⁅X.Z 0, X.Q 1 ⊓ X.Q 2⁆ = ⁅X.Q 1 ⊓ X.Q 2, X.Z 0⁆ := Subgroup.commutator_comm _ _
      _ ≤ X.Z 0 ⊓ X.Q 1 := le_inf hle h2
      _ ≤ _ := le_sup_left
  have hBC : ⁅X.Q 1, X.Q 1 ⊓ X.Q 2⁆ ≤ (X.Z 0 ⊓ X.Q 1) ⊔ (X.Q 0 ⊓ X.Q 2) :=
    (Subgroup.commutator_mono_right inf_le_left).trans
      (hquot.2.2.1.trans le_sup_right)
  have hAD : X.Z 0 ≤
      Subgroup.normalizer (((X.Z 0 ⊓ X.Q 1) ⊔ (X.Q 0 ⊓ X.Q 2) : Subgroup G) : Set G) :=
    (le_inf hZ0NW0 hZ0NA').trans (Subgroup.inf_normalizer_le_normalizer_sup _ _)
  have hBD : X.Q 1 ≤
      Subgroup.normalizer (((X.Z 0 ⊓ X.Q 1) ⊔ (X.Q 0 ⊓ X.Q 2) : Subgroup G) : Set G) :=
    (le_inf hQ1NW0 hQ1NA').trans (Subgroup.inf_normalizer_le_normalizer_sup _ _)
  have hQ0C : ⁅X.Q 0, X.Q 1 ⊓ X.Q 2⁆ ≤ (X.Z 0 ⊓ X.Q 1) ⊔ (X.Q 0 ⊓ X.Q 2) := by
    have hQ0le : X.Q 0 ≤ X.Z 0 ⊔ X.Q 1 := by
      rw [d1_Z0_sup_Q1 X H hd₀ hd₁ hna hodd₀ rfl]
      exact X.Q_le_edgeSylow_left 0
    exact (Subgroup.commutator_mono_left hQ0le).trans
      (CFSG.GorensteinWalter.commutator_sup_le_of_commutator_le_and_normalize
        (X.Z 0) (X.Q 1) (X.Q 1 ⊓ X.Q 2) ((X.Z 0 ⊓ X.Q 1) ⊔ (X.Q 0 ⊓ X.Q 2))
        hAC hBC hAD hBD)
  have hAle : X.Q 0 ⊓ X.Q 2 ≤ X.Q 1 := by
    have h := hquot.1
    rwa [show (1:ℤ) - 1 = 0 by norm_num, show (1:ℤ) + 1 = 2 by norm_num] at h
  have hle1 : X.Q 1 ⊓ X.Q 0 ≤ (X.Z 0 ⊓ X.Q 1) ⊔ (X.Q 0 ⊓ X.Q 2) := by
    rw [hcomm_eq]
    refine sup_le ?_ le_sup_right
    calc ⁅X.Q 1 ⊓ X.Q 2, X.Q 0⁆ = ⁅X.Q 0, X.Q 1 ⊓ X.Q 2⁆ := Subgroup.commutator_comm _ _
      _ ≤ _ := hQ0C
  have hle2 : (X.Z 0 ⊓ X.Q 1) ⊔ (X.Q 0 ⊓ X.Q 2) ≤ X.Q 1 ⊓ X.Q 0 := by
    refine sup_le ?_ ?_
    · exact le_inf inf_le_right (inf_le_left.trans (X.Z_le_Q 0))
    · exact le_inf hAle inf_le_left
  exact le_antisymm hle1 hle2

private theorem d1_Q1_inf_Q2_eq (H : X.Sec4Hyp s r) {d₀ d₁ : ℕ} (hd₀ : X.HasB 0 d₀)
    (hd₁ : X.HasB 1 d₁)
    (hna : ¬ ⁅X.Z 1, X.Z ((d₁ : ℤ) + 1)⁆ ≤ X.Z 1 ⊓ X.Z ((d₁ : ℤ) + 1))
    (hodd₀ : Odd d₀) (h3 : d₁ = 3) :
    X.Q 1 ⊓ X.Q 2 = (X.Z 2 ⊓ X.Q 1) ⊔ (X.Q 0 ⊓ X.Q 2) := by
  obtain ⟨hd0, hr, hs⟩ := d1_numeric X H hd₀ hd₁ hna hodd₀ h3
  subst h3; subst hd0; subst hr; subst hs
  have hW0 := d1_Q1_inf_Q0_eq X H hd₀ hd₁ hna hodd₀ rfl
  obtain ⟨t, ht, htref⟩ := X.exists_reflection H 1
  have hQ1 : conjSub t (X.Q 1) = X.Q 1 :=
    (X.Q_smul X (by simpa using htref 0)).symm
  have hQ0 : conjSub t (X.Q 0) = X.Q 2 :=
    (X.Q_smul X (i := 0) (j := 2) (by simpa using htref (-1))).symm
  have hQ2 : conjSub t (X.Q 2) = X.Q 0 :=
    (X.Q_smul X (i := 2) (j := 0) (by simpa using htref 1)).symm
  have hZ0 : conjSub t (X.Z 0) = X.Z 2 :=
    (X.Z_smul X (i := 0) (j := 2) (by simpa using htref (-1))).symm
  calc X.Q 1 ⊓ X.Q 2 = conjSub t (X.Q 1 ⊓ X.Q 0) := by
        rw [conjSub_inf, hQ1, hQ0]
    _ = conjSub t ((X.Z 0 ⊓ X.Q 1) ⊔ (X.Q 0 ⊓ X.Q 2)) := by rw [hW0]
    _ = (X.Z 2 ⊓ X.Q 1) ⊔ (X.Q 0 ⊓ X.Q 2) := by
        rw [conjSub_sup, conjSub_inf, conjSub_inf, hZ0, hQ1, hQ0, hQ2, inf_comm (X.Q 2) (X.Q 0)]

private theorem d1_Q1_decomp (H : X.Sec4Hyp s r) {d₀ d₁ : ℕ} (hd₀ : X.HasB 0 d₀)
    (hd₁ : X.HasB 1 d₁)
    (hna : ¬ ⁅X.Z 1, X.Z ((d₁ : ℤ) + 1)⁆ ≤ X.Z 1 ⊓ X.Z ((d₁ : ℤ) + 1))
    (hodd₀ : Odd d₀) (h3 : d₁ = 3) :
    X.Q 1 = ((X.Z 0 ⊓ X.Q 1) ⊔ (X.Z 2 ⊓ X.Q 1)) ⊔ (X.Q 0 ⊓ X.Q 2) := by
  obtain ⟨hd0, hr, hs⟩ := d1_numeric X H hd₀ hd₁ hna hodd₀ h3
  subst h3; subst hd0; subst hr; subst hs
  have hW0 := d1_Q1_inf_Q0_eq X H hd₀ hd₁ hna hodd₀ rfl
  have hW2 := d1_Q1_inf_Q2_eq X H hd₀ hd₁ hna hodd₀ rfl
  have hquot := X.Q_quot H.char H.sing (by norm_num : 4 ≤ 5) 1
  have hdeg : X.Q 1 = (X.Q 1 ⊓ X.Q 2) ⊔ (X.Q 1 ⊓ X.Q 0) := by
    have h := hquot.2.2.2.2.2
    rwa [show (1:ℤ) - 1 = 0 by norm_num, show (1:ℤ) + 1 = 2 by norm_num] at h
  calc X.Q 1 = (X.Q 1 ⊓ X.Q 2) ⊔ (X.Q 1 ⊓ X.Q 0) := hdeg
    _ = ((X.Z 0 ⊓ X.Q 1) ⊔ (X.Z 2 ⊓ X.Q 1)) ⊔ (X.Q 0 ⊓ X.Q 2) := by
        rw [hW2, hW0,
          sup_sup_sup_comm (X.Z 2 ⊓ X.Q 1) (X.Q 0 ⊓ X.Q 2) (X.Z 0 ⊓ X.Q 1) (X.Q 0 ⊓ X.Q 2),
          sup_idem, sup_comm (X.Z 2 ⊓ X.Q 1) (X.Z 0 ⊓ X.Q 1)]

private theorem d1_card_Aprime (H : X.Sec4Hyp s r) {d₀ d₁ : ℕ} (hd₀ : X.HasB 0 d₀)
    (hd₁ : X.HasB 1 d₁)
    (hna : ¬ ⁅X.Z 1, X.Z ((d₁ : ℤ) + 1)⁆ ≤ X.Z 1 ⊓ X.Z ((d₁ : ℤ) + 1))
    (hodd₀ : Odd d₀) (h3 : d₁ = 3) :
    Nat.card ↥(X.Q 0 ⊓ X.Q 2) = 2 ^ (X.n 0 + X.n 1) := by
  obtain ⟨hd0, hr, hs⟩ := d1_numeric X H hd₀ hd₁ hna hodd₀ h3
  subst h3; subst hd0; subst hr; subst hs
  have hQ1 := d1_card_Q1 X H hd₀ hd₁ hna hodd₀ rfl
  have hquot := X.Q_quot H.char H.sing (by norm_num : 4 ≤ 5) 1
  have hAle : X.Q 0 ⊓ X.Q 2 ≤ X.Q 1 := by
    have h := hquot.1
    rwa [show (1:ℤ) - 1 = 0 by norm_num, show (1:ℤ) + 1 = 2 by norm_num] at h
  have hrel : (X.Q 0 ⊓ X.Q 2).relIndex (X.Q 1) = 2 ^ (2 * X.n 0) := by
    have h := hquot.2.2.2.1
    rw [show (1:ℤ) - 1 = 0 by norm_num, show (1:ℤ) + 1 = 2 by norm_num] at h
    rwa [X.n_two] at h
  have hcard := Subgroup.relIndex_mul_card (H := X.Q 0 ⊓ X.Q 2) (K := X.Q 1)
  rw [hrel, hQ1, inf_eq_left.mpr hAle] at hcard
  have hpos : 0 < 2 ^ (2 * X.n 0) := by positivity
  exact Nat.eq_of_mul_eq_mul_left hpos
    (hcard.trans (by rw [← pow_add]; congr 1; ring))

private theorem d1_Q0_eq (H : X.Sec4Hyp s r) {d₀ d₁ : ℕ} (hd₀ : X.HasB 0 d₀)
    (hd₁ : X.HasB 1 d₁)
    (hna : ¬ ⁅X.Z 1, X.Z ((d₁ : ℤ) + 1)⁆ ≤ X.Z 1 ⊓ X.Z ((d₁ : ℤ) + 1))
    (hodd₀ : Odd d₀) (h3 : d₁ = 3) :
    X.Q 0 = X.Z 0 ⊔ (X.Q 0 ⊓ X.Q 2) := by
  obtain ⟨hd0, hr, hs⟩ := d1_numeric X H hd₀ hd₁ hna hodd₀ h3
  subst h3; subst hd0; subst hr; subst hs
  have hW0 := d1_Q1_inf_Q0_eq X H hd₀ hd₁ hna hodd₀ rfl
  have hQ0leS : X.Q 0 ≤ X.Z 0 ⊔ X.Q 1 := by
    rw [d1_Z0_sup_Q1 X H hd₀ hd₁ hna hodd₀ rfl]
    exact X.Q_le_edgeSylow_left 0
  have hZ0norm : X.Z 0 ≤ Subgroup.normalizer (X.Q 1 : Set G) := by
    have h : X.Gi 1 ≤ Subgroup.normalizer (X.Q 1 : Set G) :=
      CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 1)
    have hZ0le : X.Z 0 ≤ X.Gi 1 := fun z hz =>
      (X.Q_le_Gi_adj 0).trans inf_le_right (X.Z_le_Q 0 hz)
    exact hZ0le.trans h
  have hcoe : ((X.Z 0 ⊔ X.Q 1 : Subgroup G) : Set G) =
      (X.Z 0 : Set G) * (X.Q 1 : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right (X.Z 0) (X.Q 1) hZ0norm
  have h1 : X.Q 0 ≤ X.Z 0 ⊔ (X.Q 0 ⊓ X.Q 2) := by
    intro x hx
    have hxS : x ∈ X.Z 0 ⊔ X.Q 1 := hQ0leS hx
    have hxmul : x ∈ (X.Z 0 : Set G) * (X.Q 1 : Set G) := by rw [← hcoe]; exact hxS
    obtain ⟨z, hz, q, hq, hxq⟩ := hxmul
    have hxq' : x = z * q := hxq.symm
    have hqQ0 : q ∈ X.Q 0 := by
      have : q = z⁻¹ * x := by rw [hxq']; group
      rw [this]
      exact (X.Q 0).mul_mem ((X.Q 0).inv_mem (X.Z_le_Q 0 hz)) hx
    have hqW0 : q ∈ (X.Z 0 ⊓ X.Q 1) ⊔ (X.Q 0 ⊓ X.Q 2) := by
      rw [← hW0]
      exact Subgroup.mem_inf.mpr ⟨hq, hqQ0⟩
    have hxmem : x ∈ X.Z 0 ⊔ ((X.Z 0 ⊓ X.Q 1) ⊔ (X.Q 0 ⊓ X.Q 2)) := by
      rw [hxq']
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hz) (Subgroup.mem_sup_right hqW0)
    have hsimpl : X.Z 0 ⊔ ((X.Z 0 ⊓ X.Q 1) ⊔ (X.Q 0 ⊓ X.Q 2)) =
        X.Z 0 ⊔ (X.Q 0 ⊓ X.Q 2) := by
      rw [← sup_assoc, sup_eq_left.mpr (inf_le_left : X.Z 0 ⊓ X.Q 1 ≤ X.Z 0)]
    rw [hsimpl] at hxmem
    exact hxmem
  exact le_antisymm h1 (sup_le (X.Z_le_Q 0) inf_le_left)

private theorem d1_Z1_le_Z0 (H : X.Sec4Hyp s r) {d₀ d₁ : ℕ} (hd₀ : X.HasB 0 d₀)
    (hd₁ : X.HasB 1 d₁)
    (hna : ¬ ⁅X.Z 1, X.Z ((d₁ : ℤ) + 1)⁆ ≤ X.Z 1 ⊓ X.Z ((d₁ : ℤ) + 1))
    (hodd₀ : Odd d₀) (h3 : d₁ = 3) :
    X.Z 1 ≤ X.Z 0 := by
  obtain ⟨hd0, hr, hs⟩ := d1_numeric X H hd₀ hd₁ hna hodd₀ h3
  subst h3; subst hd0; subst hr; subst hs
  have hZ1c : X.Z 1 = centerOf (X.L 1) := (X.s45_step11 H hd₀ hd₁ hna hodd₀).1
  have hSleL1 : X.edgeSylow 0 ≤ X.L 1 := by
    have h := (X.edgeSylow_sup_edgeSylow 1).symm
    rw [show (1:ℤ) - 1 = 0 by norm_num] at h
    rw [h]; exact le_sup_left
  have hZ1centS : X.Z 1 ≤ Subgroup.centralizer (X.edgeSylow 0 : Set G) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have hzc : z ∈ centerOf (X.L 1) := by rw [← hZ1c]; exact hz
    have hzc' : z ∈ Subgroup.centralizer (X.L 1 : Set G) := (Subgroup.mem_inf.mp hzc).2
    exact Subgroup.mem_centralizer_iff.mp hzc' s (hSleL1 hs)
  have hP : IsSylowTwoOf (X.edgeSylow 0) (X.Gi 0) := X.isSylowTwoOf_edgeSylow_Gi 0
  have hcenter := X.centerOf_sylow_le_Z H.char 0 hP
  have hmem : X.Z 1 ≤ centerOf (X.edgeSylow 0) :=
    le_inf ((d1_Z1_le_Q0 X H hd₀ hd₁ hna hodd₀ rfl).trans (X.Q_le_edgeSylow_left 0)) hZ1centS
  exact hmem.trans hcenter.1

private theorem d1_Z0_inf_Q2_le_Z1 (H : X.Sec4Hyp s r) {d₀ d₁ : ℕ} (hd₀ : X.HasB 0 d₀)
    (hd₁ : X.HasB 1 d₁)
    (hna : ¬ ⁅X.Z 1, X.Z ((d₁ : ℤ) + 1)⁆ ≤ X.Z 1 ⊓ X.Z ((d₁ : ℤ) + 1))
    (hodd₀ : Odd d₀) (h3 : d₁ = 3) :
    X.Z 0 ⊓ X.Q 2 ≤ X.Z 1 := by
  obtain ⟨hd0, hr, hs⟩ := d1_numeric X H hd₀ hd₁ hna hodd₀ h3
  subst h3; subst hd0; subst hr; subst hs
  have hZ1c : X.Z 1 = centerOf (X.L 1) := (X.s45_step11 H hd₀ hd₁ hna hodd₀).1
  have hZ0C : X.Z 0 ≤ Subgroup.centralizer ((X.Z 0 ⊓ X.Q 2 : Subgroup G) : Set G) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact Subgroup.mem_centralizer_iff.mp
      (Subgroup.mem_inf.mp (X.Z_le_center 0 hz)).2 y (X.Z_le_Q 0 hy.1)
  have hZ2C : X.Z 2 ≤ Subgroup.centralizer ((X.Z 0 ⊓ X.Q 2 : Subgroup G) : Set G) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact Subgroup.mem_centralizer_iff.mp
      (Subgroup.mem_inf.mp (X.Z_le_center 2 hz)).2 y hy.2
  have hA'C : X.Q 0 ⊓ X.Q 2 ≤
      Subgroup.centralizer ((X.Z 0 ⊓ X.Q 2 : Subgroup G) : Set G) := by
    have hYcent : (X.Z 0 ⊓ X.Q 2 : Subgroup G) ≤ Subgroup.centralizer (X.Q 0 : Set G) := by
      intro y hy
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      exact Subgroup.mem_centralizer_iff.mp
        (Subgroup.mem_inf.mp (X.Z_le_center 0 hy.1)).2 a ha
    have hYcent' : (X.Z 0 ⊓ X.Q 2 : Subgroup G) ≤
        Subgroup.centralizer ((X.Q 0 ⊓ X.Q 2 : Subgroup G) : Set G) :=
      hYcent.trans (Subgroup.centralizer_le (inf_le_left : X.Q 0 ⊓ X.Q 2 ≤ X.Q 0))
    exact Subgroup.le_centralizer_iff.mp hYcent'
  have hW0C : X.Z 0 ⊓ X.Q 1 ≤
      Subgroup.centralizer ((X.Z 0 ⊓ X.Q 2 : Subgroup G) : Set G) :=
    (inf_le_left : X.Z 0 ⊓ X.Q 1 ≤ X.Z 0).trans hZ0C
  have hW2C : X.Z 2 ⊓ X.Q 1 ≤
      Subgroup.centralizer ((X.Z 0 ⊓ X.Q 2 : Subgroup G) : Set G) :=
    (inf_le_left : X.Z 2 ⊓ X.Q 1 ≤ X.Z 2).trans hZ2C
  have hdeg : X.Q 1 = (X.Q 1 ⊓ X.Q 2) ⊔ (X.Q 1 ⊓ X.Q 0) := by
    have hquot := X.Q_quot H.char H.sing (by norm_num : 4 ≤ 5) 1
    have h := hquot.2.2.2.2.2
    rwa [show (1:ℤ) - 1 = 0 by norm_num, show (1:ℤ) + 1 = 2 by norm_num] at h
  have hQ1C : X.Q 1 ≤ Subgroup.centralizer ((X.Z 0 ⊓ X.Q 2 : Subgroup G) : Set G) := by
    rw [hdeg]
    refine sup_le ?_ ?_
    · rw [d1_Q1_inf_Q2_eq X H hd₀ hd₁ hna hodd₀ rfl]
      exact sup_le hW2C hA'C
    · rw [d1_Q1_inf_Q0_eq X H hd₀ hd₁ hna hodd₀ rfl]
      exact sup_le hW0C hA'C
  have hL1C : X.L 1 ≤ Subgroup.centralizer ((X.Z 0 ⊓ X.Q 2 : Subgroup G) : Set G) := by
    rw [d1_L1_eq X H hd₀ hd₁ hna hodd₀ rfl]
    exact sup_le (sup_le hZ0C hZ2C) hQ1C
  have hYleC : (X.Z 0 ⊓ X.Q 2 : Subgroup G) ≤ Subgroup.centralizer (X.L 1 : Set G) :=
    Subgroup.le_centralizer_iff.mp hL1C
  have hYleL1 : (X.Z 0 ⊓ X.Q 2 : Subgroup G) ≤ X.L 1 := by
    have hY2 : IsPGroup 2 ↥(X.Z 0 ⊓ X.Q 2) :=
      (pCoreOf_isPGroup' (X.Gi 2)).to_le inf_le_right
    have hYG1 : (X.Z 0 ⊓ X.Q 2 : Subgroup G) ≤ X.Gi 1 :=
      (inf_le_right : X.Z 0 ⊓ X.Q 2 ≤ X.Q 2).trans
        ((X.Q_le_Gi_adj 2).trans inf_le_left)
    exact le_oTwoPrime_of_isPGroup hY2 hYG1
  rw [hZ1c]
  exact le_inf hYleL1 hYleC

private theorem d1_Z0_inf_Q2_eq (H : X.Sec4Hyp s r) {d₀ d₁ : ℕ} (hd₀ : X.HasB 0 d₀)
    (hd₁ : X.HasB 1 d₁)
    (hna : ¬ ⁅X.Z 1, X.Z ((d₁ : ℤ) + 1)⁆ ≤ X.Z 1 ⊓ X.Z ((d₁ : ℤ) + 1))
    (hodd₀ : Odd d₀) (h3 : d₁ = 3) :
    X.Z 0 ⊓ X.Q 2 = X.Z 1 :=
  le_antisymm (d1_Z0_inf_Q2_le_Z1 X H hd₀ hd₁ hna hodd₀ h3)
    (le_inf (d1_Z1_le_Z0 X H hd₀ hd₁ hna hodd₀ h3)
      (d1_Z1_le_Q2 X H hd₀ hd₁ hna hodd₀ h3))

private theorem d1_Q0_ne_Z0 (H : X.Sec4Hyp s r) {d₀ d₁ : ℕ} (hd₀ : X.HasB 0 d₀)
    (hd₁ : X.HasB 1 d₁)
    (hna : ¬ ⁅X.Z 1, X.Z ((d₁ : ℤ) + 1)⁆ ≤ X.Z 1 ⊓ X.Z ((d₁ : ℤ) + 1))
    (hodd₀ : Odd d₀) (h3 : d₁ = 3) :
    X.Q 0 ≠ X.Z 0 := by
  intro h
  have hA : X.Q 0 ⊓ X.Q 2 = X.Z 1 := by
    rw [h]; exact d1_Z0_inf_Q2_eq X H hd₀ hd₁ hna hodd₀ h3
  have h1 := d1_card_Aprime X H hd₀ hd₁ hna hodd₀ h3
  rw [hA, (X.s45_step11 H hd₀ hd₁ hna hodd₀).2.1] at h1
  have h2 := Nat.pow_right_injective (a := 2) (by norm_num : 2 ≤ 2) h1
  have := H.two_le_n 1
  omega

private theorem d1_Aprime_comm_self_le_Z1 (H : X.Sec4Hyp s r) {d₀ d₁ : ℕ}
    (hd₀ : X.HasB 0 d₀) (hd₁ : X.HasB 1 d₁)
    (hna : ¬ ⁅X.Z 1, X.Z ((d₁ : ℤ) + 1)⁆ ≤ X.Z 1 ⊓ X.Z ((d₁ : ℤ) + 1))
    (hodd₀ : Odd d₀) (h3 : d₁ = 3) :
    ⁅X.Q 0 ⊓ X.Q 2, X.Q 0 ⊓ X.Q 2⁆ ≤ X.Z 1 := by
  obtain ⟨hd0, hr, hs⟩ := d1_numeric X H hd₀ hd₁ hna hodd₀ h3
  subst h3; subst hd0; subst hr; subst hs
  have hZ1Qg : X.Z 1 = pCoreOf 2 (X.arcStab (-2) 4) := by
    have h := (X.s45_step11 H hd₀ hd₁ hna hodd₀).2.2.1
    rw [h]; norm_num [Setup.Qg']
  have h0 := (X.Q_quot H.char H.sing (by norm_num : 4 ≤ 5) 0).2.2.1
  have h2 := (X.Q_quot H.char H.sing (by norm_num : 4 ≤ 5) 2).2.2.1
  rw [show (0:ℤ) - 1 = -1 by norm_num, show (0:ℤ) + 1 = 1 by norm_num] at h0
  rw [show (2:ℤ) - 1 = 1 by norm_num, show (2:ℤ) + 1 = 3 by norm_num] at h2
  have hm : X.Q (-1) ≤ X.Gi (-2) := by
    simpa using (X.Q_le_Gi_adj (-1)).trans inf_le_left
  have hp : X.Q 3 ≤ X.Gi 4 := by
    simpa using (X.Q_le_Gi_adj 3).trans inf_le_right
  have hC : ⁅X.Q 0 ⊓ X.Q 2, X.Q 0 ⊓ X.Q 2⁆ ≤ X.arcStab (-2) 4 := by
    rw [X.arcStab_eq_inf (by norm_num : (-2:ℤ) ≤ 4)]
    exact le_inf
      ((Subgroup.commutator_mono inf_le_left inf_le_left).trans
        (h0.trans (inf_le_left.trans hm)))
      ((Subgroup.commutator_mono inf_le_right inf_le_right).trans
        (h2.trans (inf_le_right.trans hp)))
  have hC2 : IsPGroup 2 ↥⁅X.Q 0 ⊓ X.Q 2, X.Q 0 ⊓ X.Q 2⁆ :=
    (pCoreOf_isPGroup' (X.Gi 0)).to_le ((Subgroup.commutator_le_self _).trans inf_le_left)
  have h := X.le_pCoreOf_arcStab_r H (a := -2) hC2 (by simpa using hC)
  rw [hZ1Qg]
  simpa using h

private theorem commutator_eq_bot_of_le_Q {U : Subgroup G} (i : ℤ) (hU : U ≤ X.Q i) :
    ⁅U, X.Z i⁆ = ⊥ := by
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro u hu
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  have hcent : z ∈ Subgroup.centralizer (X.Q i : Set G) :=
    (Subgroup.mem_inf.mp (X.Z_le_center i hz)).2
  exact (Subgroup.mem_centralizer_iff.mp hcent u (hU hu)).symm

private theorem d1_Aprime_le_Q1 (H : X.Sec4Hyp s r) {d₀ d₁ : ℕ} (hd₀ : X.HasB 0 d₀)
    (hd₁ : X.HasB 1 d₁)
    (hna : ¬ ⁅X.Z 1, X.Z ((d₁ : ℤ) + 1)⁆ ≤ X.Z 1 ⊓ X.Z ((d₁ : ℤ) + 1))
    (hodd₀ : Odd d₀) (h3 : d₁ = 3) :
    X.Q 0 ⊓ X.Q 2 ≤ X.Q 1 := by
  obtain ⟨hd0, hr, hs⟩ := d1_numeric X H hd₀ hd₁ hna hodd₀ h3
  subst h3; subst hd0; subst hr; subst hs
  have hquot := X.Q_quot H.char H.sing (by norm_num : 4 ≤ 5) 1
  have h := hquot.1
  rwa [show (1 : ℤ) - 1 = 0 by norm_num, show (1 : ℤ) + 1 = 2 by norm_num] at h

private theorem d1_Aprime_comm_Q1_le_Z1 (H : X.Sec4Hyp s r) {d₀ d₁ : ℕ}
    (hd₀ : X.HasB 0 d₀) (hd₁ : X.HasB 1 d₁)
    (hna : ¬ ⁅X.Z 1, X.Z ((d₁ : ℤ) + 1)⁆ ≤ X.Z 1 ⊓ X.Z ((d₁ : ℤ) + 1))
    (hodd₀ : Odd d₀) (h3 : d₁ = 3) :
    ⁅X.Q 0 ⊓ X.Q 2, X.Q 1⁆ ≤ X.Z 1 := by
  have hQ1 := d1_Q1_decomp X H hd₀ hd₁ hna hodd₀ h3
  have hApQ1 := d1_Aprime_le_Q1 X H hd₀ hd₁ hna hodd₀ h3
  have hNW0 : X.Z 0 ⊓ X.Q 1 ≤ Subgroup.normalizer (X.Z 1 : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact X.Z_normal 1 x (X.Q_le_Gi 1 hx.2)
  have hNW2 : X.Z 2 ⊓ X.Q 1 ≤ Subgroup.normalizer (X.Z 1 : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact X.Z_normal 1 x (X.Q_le_Gi 1 hx.2)
  have hNA : X.Q 0 ⊓ X.Q 2 ≤ Subgroup.normalizer (X.Z 1 : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact X.Z_normal 1 x (X.Q_le_Gi 1 (hApQ1 hx))
  have hW0 : ⁅X.Q 0 ⊓ X.Q 2, X.Z 0 ⊓ X.Q 1⁆ = ⊥ := eq_bot_iff.mpr <|
    (Subgroup.commutator_mono le_rfl inf_le_left).trans
      (X.commutator_eq_bot_of_le_Q (U := X.Q 0 ⊓ X.Q 2) 0 inf_le_left).le
  have hW2 : ⁅X.Q 0 ⊓ X.Q 2, X.Z 2 ⊓ X.Q 1⁆ = ⊥ := eq_bot_iff.mpr <|
    (Subgroup.commutator_mono le_rfl inf_le_left).trans
      (X.commutator_eq_bot_of_le_Q (U := X.Q 0 ⊓ X.Q 2) 2 inf_le_right).le
  have hA := d1_Aprime_comm_self_le_Z1 X H hd₀ hd₁ hna hodd₀ h3
  have hW : ⁅X.Q 0 ⊓ X.Q 2, (X.Z 0 ⊓ X.Q 1) ⊔ (X.Z 2 ⊓ X.Q 1)⁆ ≤ X.Z 1 :=
    CFSG.GroupTheory.commutator_sup_right_le_of_le_normalizer hNW0 hNW2
      (by rw [hW0]; exact bot_le)
      (by rw [hW2]; exact bot_le)
  rw [hQ1]
  exact CFSG.GroupTheory.commutator_sup_right_le_of_le_normalizer (sup_le hNW0 hNW2)
    hNA hW hA

private theorem d1_Aprime_comm_L1_le_Z1 (H : X.Sec4Hyp s r) {d₀ d₁ : ℕ}
    (hd₀ : X.HasB 0 d₀) (hd₁ : X.HasB 1 d₁)
    (hna : ¬ ⁅X.Z 1, X.Z ((d₁ : ℤ) + 1)⁆ ≤ X.Z 1 ⊓ X.Z ((d₁ : ℤ) + 1))
    (hodd₀ : Odd d₀) (h3 : d₁ = 3) :
    ⁅X.Q 0 ⊓ X.Q 2, X.L 1⁆ ≤ X.Z 1 := by
  obtain ⟨hd0, hr, hs⟩ := d1_numeric X H hd₀ hd₁ hna hodd₀ h3
  subst h3; subst hd0; subst hr; subst hs
  have hL1 := d1_L1_eq X H hd₀ hd₁ hna hodd₀ rfl
  have hB21 : X.HasB 2 1 :=
    (X.hasB_iff_of_even (i := 2) (j := 0) (by norm_num) 1).mpr hd₀
  have hZ0G1 : X.Z 0 ≤ X.Gi 1 := by
    have h := hd₀.1 1 (by norm_num)
    simpa using h
  have hZ2G1 : X.Z 2 ≤ X.Gi 1 := by
    have h := hB21.1 (-1) (by norm_num)
    simpa using h
  have hNZ0 : X.Z 0 ≤ Subgroup.normalizer (X.Z 1 : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact X.Z_normal 1 x (hZ0G1 hx)
  have hNZ2 : X.Z 2 ≤ Subgroup.normalizer (X.Z 1 : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact X.Z_normal 1 x (hZ2G1 hx)
  have hNQ1 : X.Q 1 ≤ Subgroup.normalizer (X.Z 1 : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact X.Z_normal 1 x (X.Q_le_Gi 1 hx)
  have hZ0 : ⁅X.Q 0 ⊓ X.Q 2, X.Z 0⁆ = ⊥ := X.commutator_eq_bot_of_le_Q 0 inf_le_left
  have hZ2 : ⁅X.Q 0 ⊓ X.Q 2, X.Z 2⁆ = ⊥ := X.commutator_eq_bot_of_le_Q 2 inf_le_right
  have hQ1 := d1_Aprime_comm_Q1_le_Z1 X H hd₀ hd₁ hna hodd₀ rfl
  have hZ : ⁅X.Q 0 ⊓ X.Q 2, X.Z 0 ⊔ X.Z 2⁆ ≤ X.Z 1 :=
    CFSG.GroupTheory.commutator_sup_right_le_of_le_normalizer hNZ0 hNZ2
      (by rw [hZ0]; exact bot_le)
      (by rw [hZ2]; exact bot_le)
  rw [hL1]
  exact CFSG.GroupTheory.commutator_sup_right_le_of_le_normalizer (sup_le hNZ0 hNZ2)
    hNQ1 hZ hQ1

private theorem d1_Aprime_comm_Ki1_le_Z0 (H : X.Sec4Hyp s r) {d₀ d₁ : ℕ}
    (hd₀ : X.HasB 0 d₀) (hd₁ : X.HasB 1 d₁)
    (hna : ¬ ⁅X.Z 1, X.Z ((d₁ : ℤ) + 1)⁆ ≤ X.Z 1 ⊓ X.Z ((d₁ : ℤ) + 1))
    (hodd₀ : Odd d₀) (h3 : d₁ = 3) :
    ⁅X.Q 0 ⊓ X.Q 2, X.Ki 1⁆ ≤ X.Z 0 := by
  have hL := d1_Aprime_comm_L1_le_Z1 X H hd₀ hd₁ hna hodd₀ h3
  have hZ := d1_Z1_le_Z0 X H hd₀ hd₁ hna hodd₀ h3
  exact (Subgroup.commutator_mono le_rfl (inf_le_right : X.Ki 1 ≤ X.L 1)).trans
    (hL.trans hZ)

private theorem d1_Q0_comm_Ki1_le_Z0 (H : X.Sec4Hyp s r) {d₀ d₁ : ℕ}
    (hd₀ : X.HasB 0 d₀) (hd₁ : X.HasB 1 d₁)
    (hna : ¬ ⁅X.Z 1, X.Z ((d₁ : ℤ) + 1)⁆ ≤ X.Z 1 ⊓ X.Z ((d₁ : ℤ) + 1))
    (hodd₀ : Odd d₀) (h3 : d₁ = 3) :
    ⁅X.Q 0, X.Ki 1⁆ ≤ X.Z 0 := by
  have hQ0 := d1_Q0_eq X H hd₀ hd₁ hna hodd₀ h3
  have hA := d1_Aprime_comm_Ki1_le_Z0 X H hd₀ hd₁ hna hodd₀ h3
  have hNZ : X.Z 0 ≤ Subgroup.normalizer (X.Z 0 : Set G) := Subgroup.le_normalizer
  have hNA : X.Q 0 ⊓ X.Q 2 ≤ Subgroup.normalizer (X.Z 0 : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact X.Z_normal 0 x (X.Q_le_Gi 0 hx.1)
  have hZK : ⁅X.Ki 1, X.Z 0⁆ ≤ X.Z 0 := by
    have hK : X.Ki 1 ≤ Subgroup.normalizer (X.Z 0 : Set G) := by
      intro k hk
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      exact X.Z_normal 0 k (X.K_le_Gi 0 (Subgroup.mem_inf.mp hk).1)
    exact Subgroup.le_normalizer_iff_commutator_le_right.mp hK
  have hA' : ⁅X.Ki 1, X.Q 0 ⊓ X.Q 2⁆ ≤ X.Z 0 := by
    rw [Subgroup.commutator_comm]
    exact hA
  rw [Subgroup.commutator_comm, hQ0]
  exact CFSG.GroupTheory.commutator_sup_right_le_of_le_normalizer hNZ hNA hZK hA'

private theorem d1_Q0_comm_Q1_le_Z0 (H : X.Sec4Hyp s r) {d₀ d₁ : ℕ}
    (hd₀ : X.HasB 0 d₀) (hd₁ : X.HasB 1 d₁)
    (hna : ¬ ⁅X.Z 1, X.Z ((d₁ : ℤ) + 1)⁆ ≤ X.Z 1 ⊓ X.Z ((d₁ : ℤ) + 1))
    (hodd₀ : Odd d₀) (h3 : d₁ = 3) :
    ⁅X.Q 0, X.Q 1⁆ ≤ X.Z 0 := by
  have hQ0 := d1_Q0_eq X H hd₀ hd₁ hna hodd₀ h3
  have hA := d1_Aprime_comm_Q1_le_Z1 X H hd₀ hd₁ hna hodd₀ h3
  have hZ := d1_Z1_le_Z0 X H hd₀ hd₁ hna hodd₀ h3
  have hNZ : X.Z 0 ≤ Subgroup.normalizer (X.Z 0 : Set G) := Subgroup.le_normalizer
  have hNA : X.Q 0 ⊓ X.Q 2 ≤ Subgroup.normalizer (X.Z 0 : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact X.Z_normal 0 x (X.Q_le_Gi 0 hx.1)
  have hZQ1 : ⁅X.Q 1, X.Z 0⁆ ≤ X.Z 0 := by
    have hQ1N : X.Q 1 ≤ Subgroup.normalizer (X.Z 0 : Set G) := by
      intro q hq
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      exact X.Z_normal 0 q (Subgroup.mem_inf.mp (X.Q_le_Gi_adj 1 hq)).1
    exact Subgroup.le_normalizer_iff_commutator_le_right.mp hQ1N
  have hA' : ⁅X.Q 1, X.Q 0 ⊓ X.Q 2⁆ ≤ X.Z 0 := by
    rw [Subgroup.commutator_comm]
    exact hA.trans hZ
  rw [Subgroup.commutator_comm, hQ0]
  exact CFSG.GroupTheory.commutator_sup_right_le_of_le_normalizer hNZ hNA hZQ1 hA'

private theorem d1_Q0_comm_S_le_Z0 (H : X.Sec4Hyp s r) {d₀ d₁ : ℕ}
    (hd₀ : X.HasB 0 d₀) (hd₁ : X.HasB 1 d₁)
    (hna : ¬ ⁅X.Z 1, X.Z ((d₁ : ℤ) + 1)⁆ ≤ X.Z 1 ⊓ X.Z ((d₁ : ℤ) + 1))
    (hodd₀ : Odd d₀) (h3 : d₁ = 3) :
    ⁅X.Q 0, X.S⁆ ≤ X.Z 0 := by
  have hQ1 := d1_Q0_comm_Q1_le_Z0 X H hd₀ hd₁ hna hodd₀ h3
  have hNQ1 : X.Q 1 ≤ Subgroup.normalizer (X.Z 0 : Set G) := by
    intro q hq
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact X.Z_normal 0 q (Subgroup.mem_inf.mp (X.Q_le_Gi_adj 1 hq)).1
  have hZ : ⁅X.Q 0, X.Z 0⁆ ≤ X.Z 0 :=
    (le_of_eq (X.commutator_eq_bot_of_le_Q (U := X.Q 0) 0 le_rfl)).trans bot_le
  rw [← d1_Z0_sup_Q1 X H hd₀ hd₁ hna hodd₀ h3]
  exact CFSG.GroupTheory.commutator_sup_right_le_of_le_normalizer
    Subgroup.le_normalizer hNQ1 hZ hQ1

private theorem d1_Q0_comm_L0_le_Z0 (H : X.Sec4Hyp s r) {d₀ d₁ : ℕ}
    (hd₀ : X.HasB 0 d₀) (hd₁ : X.HasB 1 d₁)
    (hna : ¬ ⁅X.Z 1, X.Z ((d₁ : ℤ) + 1)⁆ ≤ X.Z 1 ⊓ X.Z ((d₁ : ℤ) + 1))
    (hodd₀ : Odd d₀) (h3 : d₁ = 3) :
    ⁅X.Q 0, X.L 0⁆ ≤ X.Z 0 := by
  obtain ⟨hd0, hr, hs⟩ := d1_numeric X H hd₀ hd₁ hna hodd₀ h3
  subst h3; subst hd0; subst hr; subst hs
  haveI : Finite ↥(X.Gi 0) := X.hyp.finite_stab (X.vert 0)
  haveI : Finite ↥(X.L 0) := finite_of_le_stabilizer X.hyp (X.L_le_Gi 0)
  have hS := d1_Q0_comm_S_le_Z0 X H hd₀ hd₁ hna hodd₀ rfl
  let D : Subgroup G :=
    { carrier := {g | g ∈ Subgroup.normalizer (X.Z 0 : Set G) ∧ ∀ q ∈ X.Q 0, ⁅g, q⁆ ∈ X.Z 0}
      one_mem' := ⟨Subgroup.one_mem _, fun q _ => by
        rw [commutatorElement_one_left]
        exact (X.Z 0).one_mem⟩
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨Subgroup.mul_mem _ ha hb, fun q hq => ?_⟩
        have e : ⁅a * b, q⁆ = a * ⁅b, q⁆ * a⁻¹ * ⁅a, q⁆ := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact (X.Z 0).mul_mem ((Subgroup.mem_normalizer_iff.mp ha _).mp (hb' q hq))
          (ha' q hq)
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        refine ⟨Subgroup.inv_mem _ ha, fun q hq => ?_⟩
        have e : ⁅a⁻¹, q⁆ = a⁻¹ * (⁅a, q⁆)⁻¹ * a := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact (Subgroup.mem_normalizer_iff''.mp ha _).mp ((X.Z 0).inv_mem (ha' q hq)) }
  have hL0D : X.L 0 ≤ D := by
    change Subgroup.closure {x : G | x ∈ X.Gi 0 ∧ ∃ n : ℕ, x ^ 2 ^ n = 1} ≤ D
    rw [Subgroup.closure_le]
    rintro x ⟨hxG0, n, hxn⟩
    have hxL : x ∈ X.L 0 := Subgroup.subset_closure ⟨hxG0, n, hxn⟩
    have hxpow : IsPGroup 2 (Subgroup.zpowers x) := by
      have hdvd : orderOf x ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hxn
      obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
      refine IsPGroup.of_card (n := k) ?_
      rw [Nat.card_zpowers, hk]
    have hxP : Subgroup.zpowers x ≤ X.L 0 := Subgroup.zpowers_le.mpr hxL
    obtain ⟨l, hlL, hle⟩ :=
      CFSG.Quasithin.RonanF713.isSylowTwoOf_exists_conj_le_loc (T := X.edgeSylow 0)
        (X.isSylowTwoOf_edgeSylow_L 0) hxP hxpow
    have hxmem : x ∈ conjSub l (X.edgeSylow 0) := hle (Subgroup.mem_zpowers x)
    have hsS : l⁻¹ * x * l ∈ X.edgeSylow 0 := CFSG.Quasithin.mem_conjSub.mp hxmem
    have hxeq : x = l * (l⁻¹ * x * l) * l⁻¹ := by group
    rw [hxeq]
    have hlG0 : l ∈ X.Gi 0 := X.L_le_Gi 0 hlL
    have hsG0 : l⁻¹ * x * l ∈ X.Gi 0 :=
      (X.Gi 0).mul_mem ((X.Gi 0).mul_mem ((X.Gi 0).inv_mem hlG0) hxG0) hlG0
    have hconjG0 : l * (l⁻¹ * x * l) * l⁻¹ ∈ X.Gi 0 :=
      (X.Gi 0).mul_mem ((X.Gi 0).mul_mem hlG0 hsG0) ((X.Gi 0).inv_mem hlG0)
    refine ⟨?_, ?_⟩
    · rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      exact X.Z_normal 0 _ hconjG0
    · intro q hq
      have hq' : l⁻¹ * q * l ∈ X.Q 0 :=
        (Subgroup.mem_normalizer_iff''.mp
          ((CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 0)) hlG0) q).mp hq
      have hsS' : l⁻¹ * x * l ∈ X.S := by
        rwa [X.edgeSylow_zero] at hsS
      have hcomm : ⁅l⁻¹ * x * l, l⁻¹ * q * l⁆ ∈ X.Z 0 := by
        have h := hS (Subgroup.commutator_mem_commutator hq' hsS')
        have e : ⁅l⁻¹ * x * l, l⁻¹ * q * l⁆ = ⁅l⁻¹ * q * l, l⁻¹ * x * l⁆⁻¹ := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact (X.Z 0).inv_mem h
      have hconjZ : conjSub l (X.Z 0) = X.Z 0 := X.Z_normal 0 l hlG0
      have hZmem : l * ⁅l⁻¹ * x * l, l⁻¹ * q * l⁆ * l⁻¹ ∈ X.Z 0 := by
        rw [← hconjZ]
        exact CFSG.Quasithin.mem_conjSub.mpr (by
          rw [show l⁻¹ * (l * ⁅l⁻¹ * x * l, l⁻¹ * q * l⁆ * l⁻¹) * l
            = ⁅l⁻¹ * x * l, l⁻¹ * q * l⁆ by group]
          exact hcomm)
      have e : ⁅l * (l⁻¹ * x * l) * l⁻¹, q⁆
          = l * ⁅l⁻¹ * x * l, l⁻¹ * q * l⁆ * l⁻¹ := by
        simp only [commutatorElement_def]; group
      rw [e]
      exact hZmem
  rw [Subgroup.commutator_comm]
  refine Subgroup.commutator_le.mpr ?_
  intro l hl q hq
  exact (hL0D hl).2 q hq

private theorem d1_Q0_comm_Ki0_le_Z0 (H : X.Sec4Hyp s r) {d₀ d₁ : ℕ}
    (hd₀ : X.HasB 0 d₀) (hd₁ : X.HasB 1 d₁)
    (hna : ¬ ⁅X.Z 1, X.Z ((d₁ : ℤ) + 1)⁆ ≤ X.Z 1 ⊓ X.Z ((d₁ : ℤ) + 1))
    (hodd₀ : Odd d₀) (h3 : d₁ = 3) :
    ⁅X.Q 0, X.Ki 0⁆ ≤ X.Z 0 :=
  (Subgroup.commutator_mono le_rfl (inf_le_right : X.Ki 0 ≤ X.L 0)).trans
    (d1_Q0_comm_L0_le_Z0 X H hd₀ hd₁ hna hodd₀ h3)

private theorem K_le_normalizer_Q_zero_inf_centralizer_Ki_one :
    X.K ≤ Subgroup.normalizer
      ((X.Q 0 ⊓ Subgroup.centralizer (X.Ki 1 : Set G) : Subgroup G) : Set G) := by
  have hKQ0 : X.K ≤ Subgroup.normalizer (X.Q 0 : Set G) := by
    intro k hk
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp
      ((CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 0)) (X.K_le_Gi 0 hk))
  have hKKi1 : X.K ≤ Subgroup.normalizer (X.Ki 1 : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    change conjSub g (X.K ⊓ X.L 1) = X.K ⊓ X.L 1
    have hL : conjSub g (X.L 1) = X.L 1 := by
      simpa [conjSub] using Subgroup.mem_normalizer_iff_map_conj_eq.mp
        (le_normalizer_oTwoPrime (X.Gi 1) (X.K_le_Gi 1 hg))
    rw [conjSub_inf, conjSub_eq_of_mem hg, hL]
  intro k hk
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  change conjSub k (X.Q 0 ⊓ Subgroup.centralizer (X.Ki 1 : Set G)) =
    X.Q 0 ⊓ Subgroup.centralizer (X.Ki 1 : Set G)
  have hQ : conjSub k (X.Q 0) = X.Q 0 := by
    simpa [conjSub] using Subgroup.mem_normalizer_iff_map_conj_eq.mp (hKQ0 hk)
  have hKi : conjSub k (X.Ki 1) = X.Ki 1 := by
    simpa [conjSub] using Subgroup.mem_normalizer_iff_map_conj_eq.mp (hKKi1 hk)
  rw [conjSub_inf, hQ, ← conjSub_centralizer, hKi]

private theorem Q_zero_inf_centralizer_K_eq_bot (H : X.Sec4Hyp s r) :
    X.Q 0 ⊓ Subgroup.centralizer (X.K : Set G) = ⊥ := by
  have hle : X.Q 0 ⊓ Subgroup.centralizer (X.K : Set G) ≤ X.GT :=
    (le_inf inf_le_right (inf_le_left.trans (X.Q_le_Gi 0))).trans
      (X.centralizer_K_le_GT (H.two_le_n 0) (H.two_le_n 1) 0)
  have hT : IsPGroup 2 ↥(X.Q 0 ⊓ Subgroup.centralizer (X.K : Set G)) :=
    (pCoreOf_isPGroup' (X.Gi 0)).to_le
      (inf_le_left : X.Q 0 ⊓ Subgroup.centralizer (X.K : Set G) ≤ X.Q 0)
  have hbot := CFSG.Quasithin.RonanF13.inf_eq_bot_of_odd
    (T := X.Q 0 ⊓ Subgroup.centralizer (X.K : Set G)) (D := X.GT) hT H.odd_GT
  rwa [inf_eq_left.mpr hle] at hbot

private theorem d1_Q0_inf_centralizer_Ki1_le_Z0 (H : X.Sec4Hyp s r) {d₀ d₁ : ℕ}
    (hd₀ : X.HasB 0 d₀) (hd₁ : X.HasB 1 d₁)
    (hna : ¬ ⁅X.Z 1, X.Z ((d₁ : ℤ) + 1)⁆ ≤ X.Z 1 ⊓ X.Z ((d₁ : ℤ) + 1))
    (hodd₀ : Odd d₀) (h3 : d₁ = 3) :
    X.Q 0 ⊓ Subgroup.centralizer (X.Ki 1 : Set G) ≤ X.Z 0 := by
  let C : Subgroup G := X.Q 0 ⊓ Subgroup.centralizer (X.Ki 1 : Set G)
  have hCQ0 : C ≤ X.Q 0 := inf_le_left
  have hC2 : IsPGroup 2 ↥C := (pCoreOf_isPGroup' (X.Gi 0)).to_le hCQ0
  haveI hCfin : Finite ↥C :=
    finite_of_le_stabilizer X.hyp (H := C) (hCQ0.trans (X.Q_le_Gi 0))
  haveI hKifin : Finite ↥(X.Ki 0) :=
    finite_of_le_stabilizer X.hyp (H := X.Ki 0)
      ((inf_le_left : X.Ki 0 ≤ X.K).trans (X.K_le_Gi 0))
  have hN : X.Ki 0 ≤ Subgroup.normalizer (C : Set G) :=
    (inf_le_left : X.Ki 0 ≤ X.K).trans X.K_le_normalizer_Q_zero_inf_centralizer_Ki_one
  have hoddKi : Odd (Nat.card ↥(X.Ki 0)) :=
    X.odd_card_K.of_dvd_nat (Subgroup.card_dvd_of_le (inf_le_left : X.Ki 0 ≤ X.K))
  have hcop : Nat.Coprime (Nat.card ↥(X.Ki 0)) (Nat.card ↥C) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hC2
    rw [hk]
    exact (hoddKi.coprime_two_left.symm).pow_right k
  haveI : Group.IsNilpotent ↥C := hC2.isNilpotent
  have hsolv : Group.IsSolvable ↥C := inferInstance
  have hdec : C ≤ ⁅C, X.Ki 0⁆ ⊔ C ⊓ Subgroup.centralizer (X.Ki 0 : Set G) :=
    CFSG.GroupTheory.le_commutator_sup_inf_centralizer_of_coprime_of_finite hN hcop hsolv
  have h1 : ⁅C, X.Ki 0⁆ ≤ X.Z 0 :=
    (Subgroup.commutator_mono hCQ0 le_rfl).trans
      (d1_Q0_comm_Ki0_le_Z0 X H hd₀ hd₁ hna hodd₀ h3)
  have h2 : C ⊓ Subgroup.centralizer (X.Ki 0 : Set G) ≤ ⊥ := by
    have hle : C ⊓ Subgroup.centralizer (X.Ki 0 : Set G) ≤
        X.Q 0 ⊓ Subgroup.centralizer (X.K : Set G) := by
      refine le_inf ((inf_le_left : C ⊓ Subgroup.centralizer (X.Ki 0 : Set G) ≤ C).trans
        hCQ0) ?_
      rw [X.K_eq_sup]
      exact CFSG.GorensteinWalter.le_centralizer_sup_of_le_centralizers inf_le_right
        ((inf_le_left : C ⊓ Subgroup.centralizer (X.Ki 0 : Set G) ≤ C).trans
          (inf_le_right : C ≤ Subgroup.centralizer (X.Ki 1 : Set G)))
    exact hle.trans (le_of_eq (X.Q_zero_inf_centralizer_K_eq_bot H))
  have hCZ : C ≤ X.Z 0 := hdec.trans (sup_le h1 (h2.trans bot_le))
  simpa [C] using hCZ

private theorem d1_false_of_d1_eq_three (H : X.Sec4Hyp s r) {d₀ d₁ : ℕ}
    (hd₀ : X.HasB 0 d₀) (hd₁ : X.HasB 1 d₁)
    (hna : ¬ ⁅X.Z 1, X.Z ((d₁ : ℤ) + 1)⁆ ≤ X.Z 1 ⊓ X.Z ((d₁ : ℤ) + 1))
    (hodd₀ : Odd d₀) (h3 : d₁ = 3) : False := by
  have hQ0ne := d1_Q0_ne_Z0 X H hd₀ hd₁ hna hodd₀ h3
  have hCZ := d1_Q0_inf_centralizer_Ki1_le_Z0 X H hd₀ hd₁ hna hodd₀ h3
  haveI hQ0fin : Finite ↥(X.Q 0) :=
    finite_of_le_stabilizer X.hyp (H := X.Q 0) (X.Q_le_Gi 0)
  haveI hKi1fin : Finite ↥(X.Ki 1) :=
    finite_of_le_stabilizer X.hyp (H := X.Ki 1)
      ((inf_le_left : X.Ki 1 ≤ X.K).trans (X.K_le_Gi 1))
  have hQ2 : IsPGroup 2 ↥(X.Q 0) := pCoreOf_isPGroup' (X.Gi 0)
  have hN : X.Ki 1 ≤ Subgroup.normalizer (X.Q 0 : Set G) :=
    ((inf_le_left : X.Ki 1 ≤ X.K).trans (X.K_le_Gi 0)).trans
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 0))
  have hoddKi : Odd (Nat.card ↥(X.Ki 1)) :=
    X.odd_card_K.of_dvd_nat (Subgroup.card_dvd_of_le (inf_le_left : X.Ki 1 ≤ X.K))
  have hcop : Nat.Coprime (Nat.card ↥(X.Ki 1)) (Nat.card ↥(X.Q 0)) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hQ2
    rw [hk]
    exact (hoddKi.coprime_two_left.symm).pow_right k
  haveI : Group.IsNilpotent ↥(X.Q 0) := hQ2.isNilpotent
  have hsolv : Group.IsSolvable ↥(X.Q 0) := inferInstance
  have hdec : X.Q 0 ≤ ⁅X.Q 0, X.Ki 1⁆ ⊔ X.Q 0 ⊓ Subgroup.centralizer (X.Ki 1 : Set G) :=
    CFSG.GroupTheory.le_commutator_sup_inf_centralizer_of_coprime_of_finite hN hcop hsolv
  have h1 : ⁅X.Q 0, X.Ki 1⁆ ≤ X.Z 0 := d1_Q0_comm_Ki1_le_Z0 X H hd₀ hd₁ hna hodd₀ h3
  exact hQ0ne (le_antisymm (hdec.trans (sup_le h1 hCZ)) (X.Z_le_Q 0))

private theorem s45_d₁_ne_three (H : X.Sec4Hyp s r) {d₀ d₁ : ℕ} (hd₀ : X.HasB 0 d₀)
    (hd₁ : X.HasB 1 d₁)
    (hna : ¬ ⁅X.Z 1, X.Z ((d₁ : ℤ) + 1)⁆ ≤ X.Z 1 ⊓ X.Z ((d₁ : ℤ) + 1))
    (hodd₀ : Odd d₀) :
    d₁ ≠ 3 :=
  fun h3 => d1_false_of_d1_eq_three X H hd₀ hd₁ hna hodd₀ h3

private theorem commutatorElement_smul_eq_self {x y : G} {v : V} (hx : x • v = v)
    (hy : x • (y⁻¹ • v) = y⁻¹ • v) : ⁅x, y⁆ • v = v := by
  have hinv : x⁻¹ • (y⁻¹ • v) = y⁻¹ • v := by
    have h := congrArg (fun w : V => x⁻¹ • w) hy
    rw [← mul_smul, inv_mul_cancel, one_smul] at h
    exact h.symm
  rw [commutatorElement_def, mul_smul, mul_smul, hinv, ← mul_smul,
    mul_inv_cancel_right, hx]

private theorem s45_facts (H : X.Sec4Hyp s r) {d₀ d₁ : ℕ} (hd₀ : X.HasB 0 d₀)
    (hd₁ : X.HasB 1 d₁)
    (hna : ¬ ⁅X.Z 1, X.Z ((d₁ : ℤ) + 1)⁆ ≤ X.Z 1 ⊓ X.Z ((d₁ : ℤ) + 1))
    (hodd₀ : Odd d₀) :
    2 * d₁ = r ∧ d₀ + 2 = d₁ ∧ 5 ≤ d₁ ∧ s < r ∧
      X.HasB ((d₁ : ℤ) + 1) d₀ ∧ ⁅X.Z 1, X.Z ((d₁ : ℤ) + 1)⁆ ≠ ⊥ := by
  have h10 := X.s45_step10 H hd₀ hd₁ hna hodd₀
  have h12 := X.s45_step12 H hd₀ hd₁ hna hodd₀
  obtain ⟨hlt, hodd1, hdh, hRne⟩ := X.s45_lt_odd_of_not_comm_le H hd₀ hd₁ hna
  have hne3 := X.s45_d₁_ne_three H hd₀ hd₁ hna hodd₀
  have hpos0 : 1 ≤ d₀ := X.one_le_of_hasB hd₀
  obtain ⟨k, hk⟩ := hodd1
  refine ⟨h10.2, by omega, ?_, h12, hdh, hRne⟩
  omega

private def arc123 (w : V) (hw : Γ.Adj (X.vert 3) w) (hw2 : w ≠ X.vert 2) : Arc Γ 3 where
  vert
    | 0 => X.vert 1
    | 1 => X.vert 2
    | 2 => X.vert 3
    | _ => w
  adj i hi := by
    match i with
    | 0 => simpa using X.adj 1
    | 1 => simpa using X.adj 2
    | 2 => exact hw
    | n + 3 => omega
  nb i hi := by
    match i with
    | 0 =>
        intro h
        have h' := X.vert_injective h
        norm_num at h'
    | 1 => exact fun h => hw2 h.symm
    | n + 2 => omega

private theorem commutator_fixes_vert_one (H : X.Sec4Hyp s r) {d₁ : ℕ} (hd₁ : X.HasB 1 d₁)
    (hd1ge : 5 ≤ d₁) {x y : G} (hx : x ∈ X.Z 1) (hy3 : y • X.vert 3 = X.vert 3) :
    ⁅x, y⁆ • X.vert 1 = X.vert 1 := by
  have hx1 : x • X.vert 1 = X.vert 1 := MulAction.mem_stabilizer_iff.mp (X.Z_le_Gi 1 hx)
  by_cases hy1 : y • X.vert 1 = X.vert 1
  · refine commutatorElement_smul_eq_self hx1 ?_
    have hyi1 : y⁻¹ • X.vert 1 = X.vert 1 := by
      have h := congrArg (fun w : V => y⁻¹ • w) hy1
      rw [← mul_smul, inv_mul_cancel, one_smul] at h
      exact h.symm
    rw [hyi1]
    exact hx1
  · by_cases hy2 : y • X.vert 2 = X.vert 2
    ·
      refine commutatorElement_smul_eq_self hx1 ?_
      have hyi2 : y⁻¹ • X.vert 2 = X.vert 2 := by
        have h := congrArg (fun w : V => y⁻¹ • w) hy2
        rw [← mul_smul, inv_mul_cancel, one_smul] at h
        exact h.symm
      have hvadj : Γ.Adj (X.vert 2) (y⁻¹ • X.vert 1) := by
        have h := (X.hyp.adj_smul y⁻¹ (X.vert 1) (X.vert 2)).mpr (X.adj 1)
        rw [hyi2] at h
        exact h.symm
      have hxQ : x ∈ X.Q 2 :=
        X.Z_le_Q_of_lt hd₁ (i := 1) (j := 2) (by norm_num; omega) hx
      exact X.Q_fixes_neighbors_vert 2 (y⁻¹ • X.vert 1) hvadj x hxQ
    ·
      refine commutatorElement_smul_eq_self hx1 ?_
      have hyi3 : y⁻¹ • X.vert 3 = X.vert 3 := by
        have h := congrArg (fun w : V => y⁻¹ • w) hy3
        rw [← mul_smul, inv_mul_cancel, one_smul] at h
        exact h.symm
      let w : V := y⁻¹ • X.vert 2
      have hw3 : Γ.Adj (X.vert 3) w := by
        have h := (X.hyp.adj_smul y⁻¹ (X.vert 2) (X.vert 3)).mpr (X.adj 2)
        rw [hyi3] at h
        exact h.symm
      have hw2 : w ≠ X.vert 2 := by
        intro h
        apply hy2
        have h1 : y • w = y • X.vert 2 := by rw [h]
        have h2 : y • w = X.vert 2 := by
          show y • (y⁻¹ • X.vert 2) = X.vert 2
          rw [← mul_smul]
          simp
        rw [← h1]
        exact h2
      let P : Arc Γ 3 := X.arc123 (X.vert 4) (X.adj 3) (by
        intro h
        have h' := X.vert_injective h
        norm_num at h')
      let Qa : Arc Γ 3 := X.arc123 w hw3 hw2
      have hstart : (1 : G) • P.vert 0 = Qa.vert 0 := by
        simp [P, Qa, arc123]
      obtain ⟨g, hg⟩ := arc_conj_of_le X.hyp.adj_smul
        (fun v a b ha hb => X.hyp.locTrans ha hb) H.sing
        (show 3 ≤ s by have h5 := H.five_le; omega) P Qa 1 hstart
      have hg1 : g • X.vert 1 = X.vert 1 := by
        have h := hg 0 (by norm_num)
        simpa [P, Qa, arc123] using h
      have hg4 : g • X.vert 4 = w := by
        have h := hg 3 le_rfl
        simpa [P, Qa, arc123] using h
      have hgG1 : g ∈ X.Gi 1 := MulAction.mem_stabilizer_iff.mpr hg1
      have hZeq : conjSub g (X.Z 1) = X.Z 1 := X.Z_normal 1 g hgG1
      have hQC : conjSub g (pCoreOf 2 (MulAction.stabilizer G (X.vert 4))) =
          pCoreOf 2 (MulAction.stabilizer G w) := by
        rw [← pCoreOf_conjSub, ← stabilizer_smul_eq_conjSub g (X.vert 4), hg4]
      have hZleQC : X.Z 1 ≤ pCoreOf 2 (MulAction.stabilizer G w) := by
        calc X.Z 1 = conjSub g (X.Z 1) := hZeq.symm
          _ ≤ conjSub g (X.Q 4) :=
              conjSub_mono g (X.Z_le_Q_of_lt hd₁ (i := 1) (j := 4) (by norm_num; omega))
          _ = conjSub g (pCoreOf 2 (MulAction.stabilizer G (X.vert 4))) := rfl
          _ = pCoreOf 2 (MulAction.stabilizer G w) := hQC
      have hvadj : Γ.Adj w (y⁻¹ • X.vert 1) := by
        have h := (X.hyp.adj_smul y⁻¹ (X.vert 2) (X.vert 1)).mpr (X.adj 1).symm
        exact h
      exact (X.hyp.isLocL2_oTwoPrime w).Q_fixes_neighbors X.hyp.adj_smul
        (X.hyp.finite_stab w) (X.hyp.valency w).2 (X.hyp.valency w).1
        (y⁻¹ • X.vert 1) hvadj x (hZleQC hx)

private theorem commutator_Z_one_Z_h_fixes_vert_one (H : X.Sec4Hyp s r) {d₀ d₁ : ℕ}
    (hd₀ : X.HasB 0 d₀) (hd₁ : X.HasB 1 d₁)
    (hna : ¬ ⁅X.Z 1, X.Z ((d₁ : ℤ) + 1)⁆ ≤ X.Z 1 ⊓ X.Z ((d₁ : ℤ) + 1))
    (hodd₀ : Odd d₀) :
    ⁅X.Z 1, X.Z ((d₁ : ℤ) + 1)⁆ ≤ X.Gi 1 := by
  obtain ⟨-, hd0, hd1ge, -, hdh, -⟩ := X.s45_facts H hd₀ hd₁ hna hodd₀
  have hfixh : X.fixSet (X.Z ((d₁ : ℤ) + 1)) =
      Set.Icc 3 (2 * ((d₁ : ℤ) + 1) - 3) := by
    have h := X.fixSet_Z ((d₁ : ℤ) + 1) hdh
    rw [show (d₁ : ℤ) + 1 - (d₀ : ℤ) = 3 by omega,
      show (d₁ : ℤ) + 1 + (d₀ : ℤ) = 2 * ((d₁ : ℤ) + 1) - 3 by omega] at h
    exact h
  rw [Subgroup.commutator_le]
  intro x hx y hy
  have hy3 : y • X.vert 3 = X.vert 3 := by
    have hmem : (3 : ℤ) ∈ X.fixSet (X.Z ((d₁ : ℤ) + 1)) := by
      rw [hfixh]
      exact Set.mem_Icc.mpr ⟨le_rfl, by omega⟩
    exact hmem y hy
  exact MulAction.mem_stabilizer_iff.mpr (X.commutator_fixes_vert_one H hd₁ hd1ge hx hy3)

private theorem s45_shortArc_fixes (H : X.Sec4Hyp s r) {d₁ : ℕ} (hd₁ : X.HasB 1 d₁)
    {m : ℕ} (hmd : m ≤ d₁) (hms : m ≤ s) (ε : Arc Γ m) (hε : ε.vert 0 = X.vert 1)
    {x : G} (hx : x ∈ X.Z 1) : ∀ i : ℕ, i ≤ m → x • ε.vert i = ε.vert i := by
  classical
  have hfix : X.fixSet (X.Z 1) = Set.Icc (1 - (d₁ : ℤ)) (1 + (d₁ : ℤ)) :=
    X.fixSet_Z 1 hd₁
  let A : Arc Γ m := X.line.arc 1 m
  have hstart : (1 : G) • ε.vert 0 = A.vert 0 := by
    simp only [one_smul]
    simpa [A, Line.arc] using hε
  obtain ⟨g, hg⟩ := arc_conj_of_le X.hyp.adj_smul
    (fun v a b ha hb => X.hyp.locTrans ha hb) H.sing hms ε A 1 hstart
  have hgG1 : g ∈ X.Gi 1 := by
    refine MulAction.mem_stabilizer_iff.mpr ?_
    have h := hg 0 (Nat.zero_le _)
    simpa [A, Line.arc, hε] using h
  have hZg : conjSub g (X.Z 1) = X.Z 1 := X.Z_normal 1 g hgG1
  have hxg : g * x * g⁻¹ ∈ X.Z 1 := by
    have hmem : g * x * g⁻¹ ∈ conjSub g (X.Z 1) := by
      rw [mem_conjSub]
      rw [show g⁻¹ * (g * x * g⁻¹) * g = x by group]
      exact hx
    rwa [hZg] at hmem
  intro i hi
  have hmem : ((1 : ℤ) + (i : ℤ)) ∈ X.fixSet (X.Z 1) := by
    rw [hfix]
    refine Set.mem_Icc.mpr ⟨by omega, by omega⟩
  have hxA : (g * x * g⁻¹) • A.vert i = A.vert i := by
    show (g * x * g⁻¹) • X.vert ((1 : ℤ) + (i : ℤ)) = X.vert ((1 : ℤ) + (i : ℤ))
    exact hmem _ hxg
  have h1 : (g * x * g⁻¹) • (g • ε.vert i) = g • ε.vert i := by
    rw [hg i hi]
    exact hxA
  have h2 : g • (x • ε.vert i) = g • ε.vert i := by
    simpa [mul_smul] using h1
  have h3 := congrArg (fun w : V => g⁻¹ • w) h2
  simpa [mul_smul] using h3

private def arcEps1 (y : G) (hy1 : y • X.vert 1 = X.vert 1) : Arc Γ 1 where
  vert
    | 0 => X.vert 1
    | _ => y⁻¹ • X.vert 0
  adj i hi := by
    have hi0 : i = 0 := by omega
    subst hi0
    have hyi1 : y⁻¹ • X.vert 1 = X.vert 1 := by
      have h := congrArg (fun w : V => y⁻¹ • w) hy1
      rw [← mul_smul, inv_mul_cancel, one_smul] at h
      exact h.symm
    have h := (X.hyp.adj_smul y⁻¹ (X.vert 0) (X.vert 1)).mpr (X.adj 0)
    rw [hyi1] at h
    exact h.symm
  nb i hi := by omega

private def arcEps2 (y : G) (hy2 : y • X.vert 2 = X.vert 2)
    (hy1 : y • X.vert 1 ≠ X.vert 1) : Arc Γ 3 where
  vert
    | 0 => X.vert 1
    | 1 => X.vert 2
    | 2 => y⁻¹ • X.vert 1
    | _ => y⁻¹ • X.vert 0
  adj i hi := by
    match i with
    | 0 =>
        change Γ.Adj (X.vert 1) (X.vert 2)
        exact X.adj 1
    | 1 =>
        change Γ.Adj (X.vert 2) (y⁻¹ • X.vert 1)
        have hyi2 : y⁻¹ • X.vert 2 = X.vert 2 := by
          have h := congrArg (fun w : V => y⁻¹ • w) hy2
          rw [← mul_smul, inv_mul_cancel, one_smul] at h
          exact h.symm
        have h := (X.hyp.adj_smul y⁻¹ (X.vert 1) (X.vert 2)).mpr (X.adj 1)
        rw [hyi2] at h
        exact h.symm
    | 2 =>
        change Γ.Adj (y⁻¹ • X.vert 1) (y⁻¹ • X.vert 0)
        exact ((X.hyp.adj_smul y⁻¹ (X.vert 0) (X.vert 1)).mpr (X.adj 0)).symm
    | n + 3 => omega
  nb i hi := by
    match i with
    | 0 =>
        change X.vert 1 ≠ y⁻¹ • X.vert 1
        intro h
        apply hy1
        have h' := congrArg (fun w : V => y • w) h
        rwa [← mul_smul, mul_inv_cancel, one_smul] at h'
    | 1 =>
        change X.vert 2 ≠ y⁻¹ • X.vert 0
        intro h
        have h1 : y • X.vert 2 = X.vert 0 := by
          rw [h, ← mul_smul, mul_inv_cancel, one_smul]
        rw [hy2] at h1
        have := X.vert_injective h1
        norm_num at this
    | n + 2 => omega

private def arcEps3 (y : G) (hy3 : y • X.vert 3 = X.vert 3)
    (hy2 : y • X.vert 2 ≠ X.vert 2) (hy1 : y • X.vert 1 ≠ X.vert 1) : Arc Γ 5 where
  vert
    | 0 => X.vert 1
    | 1 => X.vert 2
    | 2 => X.vert 3
    | 3 => y⁻¹ • X.vert 2
    | 4 => y⁻¹ • X.vert 1
    | _ => y⁻¹ • X.vert 0
  adj i hi := by
    match i with
    | 0 =>
        change Γ.Adj (X.vert 1) (X.vert 2)
        exact X.adj 1
    | 1 =>
        change Γ.Adj (X.vert 2) (X.vert 3)
        exact X.adj 2
    | 2 =>
        change Γ.Adj (X.vert 3) (y⁻¹ • X.vert 2)
        have hyi3 : y⁻¹ • X.vert 3 = X.vert 3 := by
          have h := congrArg (fun w : V => y⁻¹ • w) hy3
          rw [← mul_smul, inv_mul_cancel, one_smul] at h
          exact h.symm
        have h := (X.hyp.adj_smul y⁻¹ (X.vert 2) (X.vert 3)).mpr (X.adj 2)
        rw [hyi3] at h
        exact h.symm
    | 3 =>
        change Γ.Adj (y⁻¹ • X.vert 2) (y⁻¹ • X.vert 1)
        exact ((X.hyp.adj_smul y⁻¹ (X.vert 1) (X.vert 2)).mpr (X.adj 1)).symm
    | 4 =>
        change Γ.Adj (y⁻¹ • X.vert 1) (y⁻¹ • X.vert 0)
        exact ((X.hyp.adj_smul y⁻¹ (X.vert 0) (X.vert 1)).mpr (X.adj 0)).symm
    | n + 5 => omega
  nb i hi := by
    match i with
    | 0 =>
        change X.vert 1 ≠ X.vert 3
        intro h
        have h' := X.vert_injective h
        norm_num at h'
    | 1 =>
        change X.vert 2 ≠ y⁻¹ • X.vert 2
        intro h
        apply hy2
        have h' := congrArg (fun w : V => y • w) h
        rwa [← mul_smul, mul_inv_cancel, one_smul] at h'
    | 2 =>
        change X.vert 3 ≠ y⁻¹ • X.vert 1
        intro h
        have h1 : y • X.vert 3 = X.vert 1 := by
          rw [h, ← mul_smul, mul_inv_cancel, one_smul]
        rw [hy3] at h1
        have := X.vert_injective h1
        norm_num at this
    | 3 =>
        change y⁻¹ • X.vert 2 ≠ y⁻¹ • X.vert 0
        intro h
        have h1 : X.vert 2 = X.vert 0 := by
          have h' := congrArg (fun w : V => y • w) h
          simpa [← mul_smul, mul_inv_cancel, one_smul] using h'
        have := X.vert_injective h1
        norm_num at this
    | n + 4 => omega

private theorem commutator_Z_one_Z_h_le_Z_h (H : X.Sec4Hyp s r) {d₁ : ℕ}
    (hd₁ : X.HasB 1 d₁) : ⁅X.Z 1, X.Z ((d₁ : ℤ) + 1)⁆ ≤ X.Z ((d₁ : ℤ) + 1) := by
  have hfix1 : X.fixSet (X.Z 1) = Set.Icc (2 - ((d₁ : ℤ) + 1)) ((d₁ : ℤ) + 1) := by
    have h := X.fixSet_Z 1 hd₁
    rw [show (1 : ℤ) - (d₁ : ℤ) = 2 - ((d₁ : ℤ) + 1) by ring,
      show (1 : ℤ) + (d₁ : ℤ) = (d₁ : ℤ) + 1 by ring] at h
    exact h
  have hZ1n : X.Z 1 ≤ Subgroup.normalizer (X.Z ((d₁ : ℤ) + 1) : Set G) := by
    intro z hz
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    change conjSub z (X.Z ((d₁ : ℤ) + 1)) = X.Z ((d₁ : ℤ) + 1)
    apply X.Z_normal
    have hmem : ((d₁ : ℤ) + 1) ∈ X.fixSet (X.Z 1) := by
      rw [hfix1]
      exact Set.mem_Icc.mpr ⟨by omega, le_rfl⟩
    exact hmem z hz
  exact Subgroup.le_normalizer_iff_commutator_le_right.mp hZ1n

private theorem commutator_Z_one_Z_h_le_Gi_zero (H : X.Sec4Hyp s r) {d₀ d₁ : ℕ}
    (hd₀ : X.HasB 0 d₀) (hd₁ : X.HasB 1 d₁)
    (hna : ¬ ⁅X.Z 1, X.Z ((d₁ : ℤ) + 1)⁆ ≤ X.Z 1 ⊓ X.Z ((d₁ : ℤ) + 1))
    (hodd₀ : Odd d₀) :
    ⁅X.Z 1, X.Z ((d₁ : ℤ) + 1)⁆ ≤ X.Gi 0 := by
  obtain ⟨-, hd0, hd1ge, -, hdh, -⟩ := X.s45_facts H hd₀ hd₁ hna hodd₀
  have hfix1 : X.fixSet (X.Z 1) = Set.Icc (2 - ((d₁ : ℤ) + 1)) ((d₁ : ℤ) + 1) := by
    have h := X.fixSet_Z 1 hd₁
    rw [show (1 : ℤ) - (d₁ : ℤ) = 2 - ((d₁ : ℤ) + 1) by ring,
      show (1 : ℤ) + (d₁ : ℤ) = (d₁ : ℤ) + 1 by ring] at h
    exact h
  have hfixh : X.fixSet (X.Z ((d₁ : ℤ) + 1)) =
      Set.Icc 3 (2 * ((d₁ : ℤ) + 1) - 3) := by
    have h := X.fixSet_Z ((d₁ : ℤ) + 1) hdh
    rw [show (d₁ : ℤ) + 1 - (d₀ : ℤ) = 3 by omega,
      show (d₁ : ℤ) + 1 + (d₀ : ℤ) = 2 * ((d₁ : ℤ) + 1) - 3 by omega] at h
    exact h
  rw [Subgroup.commutator_le]
  intro x hx y hy
  have hx0 : x • X.vert 0 = X.vert 0 := by
    have hmem : (0 : ℤ) ∈ X.fixSet (X.Z 1) := by
      rw [hfix1]
      exact Set.mem_Icc.mpr ⟨by omega, by omega⟩
    exact hmem x hx
  have hyfix : ∀ j : ℤ, 3 ≤ j → j ≤ 2 * ((d₁ : ℤ) + 1) - 3 →
      y • X.vert j = X.vert j := by
    intro j hj1 hj2
    have hmem : j ∈ X.fixSet (X.Z ((d₁ : ℤ) + 1)) := by
      rw [hfixh]
      exact Set.mem_Icc.mpr ⟨hj1, hj2⟩
    exact hmem y hy
  have hy3 : y • X.vert 3 = X.vert 3 := hyfix 3 (by omega) (by omega)
  have hxy0 : x • (y⁻¹ • X.vert 0) = y⁻¹ • X.vert 0 := by
    by_cases hy0 : y • X.vert 0 = X.vert 0
    · have hyi0 : y⁻¹ • X.vert 0 = X.vert 0 := by
        have h := congrArg (fun w : V => y⁻¹ • w) hy0
        rw [← mul_smul, inv_mul_cancel, one_smul] at h
        exact h.symm
      rw [hyi0]
      exact hx0
    · by_cases hy1 : y • X.vert 1 = X.vert 1
      · have hε := X.s45_shortArc_fixes H hd₁ (m := 1) (by omega)
          (by have h5 := H.five_le; omega) (X.arcEps1 y hy1) (by simp [arcEps1]) hx 1
          (le_rfl)
        simpa [arcEps1] using hε
      · by_cases hy2 : y • X.vert 2 = X.vert 2
        · have hε := X.s45_shortArc_fixes H hd₁ (m := 3) (by omega)
            (by have h5 := H.five_le; omega) (X.arcEps2 y hy2 hy1)
            (by simp [arcEps2]) hx 3 (le_rfl)
          simpa [arcEps2] using hε
        · have hε := X.s45_shortArc_fixes H hd₁ (m := 5) (by omega)
            (by have h5 := H.five_le; omega) (X.arcEps3 y hy3 hy2 hy1)
            (by simp [arcEps3]) hx 5 (le_rfl)
          simpa [arcEps3] using hε
  exact commutatorElement_smul_eq_self hx0 hxy0

private theorem commutator_Z_one_Z_h_le_Qg (H : X.Sec4Hyp s r) {d₀ d₁ : ℕ}
    (hd₀ : X.HasB 0 d₀) (hd₁ : X.HasB 1 d₁)
    (hna : ¬ ⁅X.Z 1, X.Z ((d₁ : ℤ) + 1)⁆ ≤ X.Z 1 ⊓ X.Z ((d₁ : ℤ) + 1))
    (hodd₀ : Odd d₀) :
    ⁅X.Z 1, X.Z ((d₁ : ℤ) + 1)⁆ ≤ X.Qg r := by
  classical
  obtain ⟨hr, hd0, hd1ge, hsr, hdh, -⟩ := X.s45_facts H hd₀ hd₁ hna hodd₀
  have hRZh := X.commutator_Z_one_Z_h_le_Z_h H hd₁
  have hR2 : IsPGroup 2 (⁅X.Z 1, X.Z ((d₁ : ℤ) + 1)⁆ : Subgroup G) :=
    ((pCoreOf_isPGroup' (X.Gi ((d₁ : ℤ) + 1))).to_le (X.Z_le_Q _)).to_le hRZh
  have hRGi1 : ⁅X.Z 1, X.Z ((d₁ : ℤ) + 1)⁆ ≤ X.Gi 1 :=
    X.commutator_Z_one_Z_h_fixes_vert_one H hd₀ hd₁ hna hodd₀
  have hRGi0 : ⁅X.Z 1, X.Z ((d₁ : ℤ) + 1)⁆ ≤ X.Gi 0 :=
    X.commutator_Z_one_Z_h_le_Gi_zero H hd₀ hd₁ hna hodd₀
  have hRGiEnd : ⁅X.Z 1, X.Z ((d₁ : ℤ) + 1)⁆ ≤ X.Gi ((r : ℤ) - 1) := by
    intro u hu
    have hmem : ((r : ℤ) - 1) ∈ X.fixSet (X.Z ((d₁ : ℤ) + 1)) := by
      rw [X.fixSet_Z ((d₁ : ℤ) + 1) hdh]
      exact Set.mem_Icc.mpr ⟨by omega, by omega⟩
    exact hmem u (hRZh hu)
  have hRarc0 : ⁅X.Z 1, X.Z ((d₁ : ℤ) + 1)⁆ ≤ X.arcStab 0 ((r : ℤ) - 1) := by
    refine X.le_arcStab_of_fixSet ?_
    intro j hj
    rw [Set.mem_Icc] at hj
    intro u hu
    have h0 : u ∈ X.Gi 0 := hRGi0 hu
    have h2 : u ∈ X.Gi ((r : ℤ) - 1) := hRGiEnd hu
    exact X.mem_Gi_of_between h0 h2 (by omega) (by omega)
  haveI hfin01 : Finite ↥(X.Gi 0 ⊓ X.Gi (0 + 1)) :=
    finite_of_le_stabilizer X.hyp (H := X.Gi 0 ⊓ X.Gi (0 + 1)) inf_le_left
  have hRedge0 : ⁅X.Z 1, X.Z ((d₁ : ℤ) + 1)⁆ ≤ X.edgeSylow 0 :=
    le_of_normal_isSylowTwoOf (X.isSylowTwoOf_edgeSylow 0)
      (X.edgeSylow_subgroupOf_normal 0) (le_inf hRGi0 hRGi1) hR2
  have hKA : X.K ≤ X.arcStab 0 ((r : ℤ) - 1) :=
    X.K_le_GT.trans (X.GT_le_arcStab _ _)
  have hA : X.arcStab 0 ((r : ℤ) - 1) ≤ X.Gi 0 ⊓ X.Gi 1 :=
    le_inf (X.arcStab_le_Gi_left (show (0 : ℤ) < (r : ℤ) - 1 by omega))
      (X.arcStab_le_Gi_left_succ (show (0 : ℤ) < (r : ℤ) - 1 by omega))
  have hRO2 : ⁅X.Z 1, X.Z ((d₁ : ℤ) + 1)⁆ ≤
      pCoreOf 2 (X.arcStab 0 ((r : ℤ) - 1)) := by
    have hEq := (X.pCoreOf_eq_inf_edgeSylow 0 hKA hA).1
    rw [hEq]
    exact le_inf hRarc0 hRedge0
  have hsing : ¬ X.RightTransAt 0 ((r : ℤ) - 1) := by
    intro h
    have h' : X.RightTransAt 0 (0 + ((r - 1 : ℕ) : ℤ)) := by
      simpa [show ((r - 1 : ℕ) : ℤ) = (r : ℤ) - 1 by push_cast; omega] using h
    have hpar := (H.ends_even 0 (r - 1) (by omega)).1 h'
    obtain ⟨n, hn⟩ := H.even_r
    obtain ⟨m, hm⟩ := hpar
    omega
  have hO2R : pCoreOf 2 (X.arcStab 0 ((r : ℤ) - 1)) ≤ X.Gi (r : ℤ) := by
    rw [X.rightTransAt_iff H (m := 0) (r' := (r : ℤ) - 1) (by omega)] at hsing
    have h := not_not.mp hsing
    simpa [show ((r : ℤ) - 1 + 1) = (r : ℤ) by ring] using h
  have hRGiR : ⁅X.Z 1, X.Z ((d₁ : ℤ) + 1)⁆ ≤ X.Gi (r : ℤ) := hRO2.trans hO2R
  have hRarc : ⁅X.Z 1, X.Z ((d₁ : ℤ) + 1)⁆ ≤ X.arcStab 0 (r : ℤ) := by
    rw [X.arcStab_eq_inf (show (0 : ℤ) ≤ (r : ℤ) by omega)]
    exact le_inf hRGi0 hRGiR
  change ⁅X.Z 1, X.Z ((d₁ : ℤ) + 1)⁆ ≤ pCoreOf 2 (X.arcStab 0 (r : ℤ))
  have h := X.le_pCoreOf_arcStab_r (H := H)
    (U := ⁅X.Z 1, X.Z ((d₁ : ℤ) + 1)⁆) (a := 0) hR2 (by simpa using hRarc)
  simpa using h

private theorem card_Z_of_odd (H : X.Sec4Hyp s r) {d₀ d₁ : ℕ} (hd₀ : X.HasB 0 d₀)
    (hd₁ : X.HasB 1 d₁)
    (hna : ¬ ⁅X.Z 1, X.Z ((d₁ : ℤ) + 1)⁆ ≤ X.Z 1 ⊓ X.Z ((d₁ : ℤ) + 1))
    (hodd₀ : Odd d₀) {j : ℤ} (hj : Odd j) : Nat.card (X.Z j) = 2 ^ X.n 0 := by
  obtain ⟨m, hm⟩ := hj
  have hcard := (X.s45_step11 H hd₀ hd₁ hna hodd₀).2.1
  have h := X.Z_add m 1
  have hjeq : (1 : ℤ) + 2 * (m : ℤ) = j := by omega
  rw [hjeq] at h
  rw [h, card_conjSub, hcard]

private theorem centerOf_L_zero_eq_bot (H : X.Sec4Hyp s r) {d₀ d₁ : ℕ}
    (hd₀ : X.HasB 0 d₀) (hd₁ : X.HasB 1 d₁)
    (hna : ¬ ⁅X.Z 1, X.Z ((d₁ : ℤ) + 1)⁆ ≤ X.Z 1 ⊓ X.Z ((d₁ : ℤ) + 1))
    (hodd₀ : Odd d₀) : centerOf (X.L 0) = ⊥ := by
  obtain ⟨hr, hd0, hd1ge, -, hdh, -⟩ := X.s45_facts H hd₀ hd₁ hna hodd₀
  have hZ1 : X.Z 1 = centerOf (X.L 1) := (X.s45_step11 H hd₀ hd₁ hna hodd₀).1
  have hZL0Z0 : centerOf (X.L 0) ≤ X.Z 0 := X.centerOf_L_le_Z H.char 0
  have hZ0Q1 : X.Z 0 ≤ X.Q 1 :=
    X.Z_le_Q_of_lt hd₀ (i := 0) (j := 1) (by
      rw [show ((1 : ℤ) - 0).natAbs = 1 by norm_num]
      omega)
  have hSleL0 : X.edgeSylow 0 ≤ X.L 0 := X.edgeSylow_le_L 0
  have hcent : centerOf (X.L 0) ≤ Subgroup.centralizer (X.edgeSylow 0 : Set G) := by
    intro z hz
    obtain ⟨hzL, hzC⟩ := Subgroup.mem_inf.mp hz
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    exact Subgroup.mem_centralizer_iff.mp hzC s (hSleL0 hs)
  have hP1 : IsSylowTwoOf (X.edgeSylow 0) (X.Gi 1) := by
    simpa using X.isSylowTwoOf_edgeSylow_Gi_succ 0
  have hzfacts := X.centerOf_sylow_le_Z H.char 1 hP1
  have hQ1S : X.Q 1 ≤ X.edgeSylow 0 := X.Q_le_edgeSylow_right 1
  have hZL0S : centerOf (X.L 0) ≤ X.edgeSylow 0 := (hZL0Z0.trans hZ0Q1).trans hQ1S
  have hZL0center : centerOf (X.L 0) ≤ centerOf (X.edgeSylow 0) :=
    le_inf hZL0S hcent
  have hZL0Z1 : centerOf (X.L 0) ≤ X.Z 1 := hZL0center.trans hzfacts.1
  have hZL0L1 : centerOf (X.L 0) ≤ centerOf (X.L 1) := by
    rw [← hZ1]
    exact hZL0Z1
  have hinf := X.centerOf_L_inf_succ H.char 0
  refine eq_bot_iff.mpr ?_
  intro z hz
  have hmem : z ∈ centerOf (X.L 0) ⊓ centerOf (X.L (0 + 1)) := by
    refine Subgroup.mem_inf.mpr ⟨hz, ?_⟩
    simpa using hZL0L1 hz
  rw [hinf] at hmem
  exact Subgroup.mem_bot.mp hmem

private theorem centerOf_L_h_eq_bot (H : X.Sec4Hyp s r) {d₀ d₁ : ℕ}
    (hd₀ : X.HasB 0 d₀) (hd₁ : X.HasB 1 d₁)
    (hna : ¬ ⁅X.Z 1, X.Z ((d₁ : ℤ) + 1)⁆ ≤ X.Z 1 ⊓ X.Z ((d₁ : ℤ) + 1))
    (hodd₀ : Odd d₀) : centerOf (X.L ((d₁ : ℤ) + 1)) = ⊥ := by
  obtain ⟨hr, hd0, hd1ge, -, hdh, -⟩ := X.s45_facts H hd₀ hd₁ hna hodd₀
  obtain ⟨hlt, hodd1, -, -⟩ := X.s45_lt_odd_of_not_comm_le H hd₀ hd₁ hna
  obtain ⟨k, hk⟩ := hodd1
  have hh : (d₁ : ℤ) + 1 = 0 + 2 * ((k : ℤ) + 1) := by omega
  have hZh : centerOf (X.L ((d₁ : ℤ) + 1)) =
      conjSub (X.τ ^ ((k : ℤ) + 1)) (centerOf (X.L 0)) := by
    rw [hh]; exact X.centerOf_L_add _ 0
  rw [hZh, X.centerOf_L_zero_eq_bot H hd₀ hd₁ hna hodd₀]
  simp [conjSub]

private theorem C_Z_h_L_h_eq_bot (H : X.Sec4Hyp s r) {d₀ d₁ : ℕ}
    (hd₀ : X.HasB 0 d₀) (hd₁ : X.HasB 1 d₁)
    (hna : ¬ ⁅X.Z 1, X.Z ((d₁ : ℤ) + 1)⁆ ≤ X.Z 1 ⊓ X.Z ((d₁ : ℤ) + 1))
    (hodd₀ : Odd d₀) :
    X.Z ((d₁ : ℤ) + 1) ⊓ Subgroup.centralizer (X.L ((d₁ : ℤ) + 1) : Set G) = ⊥ := by
  have hZL : X.Z ((d₁ : ℤ) + 1) ≤ X.L ((d₁ : ℤ) + 1) :=
    (X.Z_le_Q _).trans (X.Q_le_L _)
  refine eq_bot_iff.mpr ?_
  intro x hx
  obtain ⟨hxZ, hxC⟩ := Subgroup.mem_inf.mp hx
  have hxcenter : x ∈ centerOf (X.L ((d₁ : ℤ) + 1)) :=
    Subgroup.mem_inf.mpr ⟨hZL hxZ, hxC⟩
  rw [X.centerOf_L_h_eq_bot H hd₀ hd₁ hna hodd₀] at hxcenter
  exact Subgroup.mem_bot.mp hxcenter

private theorem s45_R_le_Z_pred (H : X.Sec4Hyp s r) {d₀ d₁ : ℕ} (hd₀ : X.HasB 0 d₀)
    (hd₁ : X.HasB 1 d₁)
    (hna : ¬ ⁅X.Z 1, X.Z ((d₁ : ℤ) + 1)⁆ ≤ X.Z 1 ⊓ X.Z ((d₁ : ℤ) + 1))
    (hodd₀ : Odd d₀) :
    ⁅X.Z 1, X.Z ((d₁ : ℤ) + 1)⁆ ≤ X.Z (d₁ : ℤ) := by
  obtain ⟨hr, hd0, hd1ge, -, hdh, -⟩ := X.s45_facts H hd₀ hd₁ hna hodd₀
  have hF2 : ⁅X.Z 1, X.Z ((d₁ : ℤ) + 1)⁆ ≤ X.Qg r :=
    X.commutator_Z_one_Z_h_le_Qg H hd₀ hd₁ hna hodd₀
  have hodd1 : Odd d₁ := (X.s45_lt_odd_of_not_comm_le H hd₀ hd₁ hna).2.1
  have hodd1Z : Odd ((d₁ : ℤ) + 1 - 1) := by
    rw [show (d₁ : ℤ) + 1 - 1 = (d₁ : ℤ) by ring]
    exact (Int.odd_coe_nat d₁).mpr hodd1
  have hcardZ : Nat.card (X.Z ((d₁ : ℤ) + 1 - 1)) = 2 ^ X.n 0 :=
    X.card_Z_of_odd H hd₀ hd₁ hna hodd₀ hodd1Z
  have hZhm1le : X.Z ((d₁ : ℤ) + 1 - 1) ≤ X.Qg r := by
    have hhasB : X.HasB ((d₁ : ℤ) + 1 - 1) d₁ := by
      have hpar : Even (((d₁ : ℤ) + 1 - 1) - 1) := by
        obtain ⟨k, hk⟩ := hodd1
        exact ⟨(k : ℤ), by omega⟩
      have h := (X.hasB_iff_of_even hpar d₁).mpr hd₁
      simpa using h
    have hfix : X.Z ((d₁ : ℤ) + 1 - 1) ≤ X.arcStab 0 (r : ℤ) := by
      refine X.le_arcStab_of_fixSet ?_
      intro j hj
      rw [Set.mem_Icc] at hj
      intro u hu
      have hmem : j ∈ X.fixSet (X.Z ((d₁ : ℤ) + 1 - 1)) := by
        have h := X.fixSet_Z ((d₁ : ℤ) + 1 - 1) hhasB
        rw [h]
        constructor <;> omega
      exact hmem u hu
    have hZ2 : IsPGroup 2 (X.Z ((d₁ : ℤ) + 1 - 1)) :=
      (pCoreOf_isPGroup' (X.Gi _)).to_le (X.Z_le_Q _)
    change X.Z ((d₁ : ℤ) + 1 - 1) ≤ pCoreOf 2 (X.arcStab 0 (r : ℤ))
    have h := X.le_pCoreOf_arcStab_r (H := H) (U := X.Z ((d₁ : ℤ) + 1 - 1)) (a := 0)
      hZ2 (by simpa using hfix)
    simpa using h
  have hQg : X.Qg r ≤ X.Z ((d₁ : ℤ) + 1 - 1) := by
    have hne : X.Qg r ≠ ⊥ := X.Qg_ne_bot H
    have hne' : pCoreOf 2 (X.arcStab 0 (0 + (r : ℤ))) ≠ ⊥ := by simpa using hne
    obtain ⟨hcardQg, -, -, -, -⟩ := X.pCoreOf_arcStab_r H 0 hne'
    have hcardQg' : Nat.card (X.Qg r) = 2 ^ X.n 0 := by simpa using hcardQg
    haveI : Finite ↥(X.Qg r) := by
      haveI : Finite ↥(X.arcStab 0 (r : ℤ)) :=
        finite_of_le_stabilizer X.hyp (H := X.arcStab 0 (r : ℤ))
          (X.arcStab_le_Gi_left (show (0 : ℤ) < (r : ℤ) by omega))
      exact Finite.of_injective
        (Subgroup.inclusion (CFSG.LieType.BorelTits.pCoreOf_le 2 _))
        (Subgroup.inclusion_injective _)
    haveI : Finite ↥(X.Z ((d₁ : ℤ) + 1 - 1)) :=
      finite_of_le_stabilizer X.hyp (H := X.Z ((d₁ : ℤ) + 1 - 1)) (X.Z_le_Gi _)
    have heq : X.Z ((d₁ : ℤ) + 1 - 1) = X.Qg r :=
      Subgroup.eq_of_le_of_card_ge hZhm1le (by rw [hcardQg', hcardZ])
    exact heq.ge
  have hleZ : ⁅X.Z 1, X.Z ((d₁ : ℤ) + 1)⁆ ≤ X.Z ((d₁ : ℤ) + 1 - 1) :=
    hF2.trans hQg
  rwa [show (d₁ : ℤ) + 1 - 1 = (d₁ : ℤ) by ring] at hleZ

private theorem hasB_of_odd {d₁ : ℕ} (hd₁ : X.HasB 1 d₁) {j : ℤ}
    (hj : Odd j) : X.HasB j d₁ := by
  have hpar : Even (j - 1) := by
    obtain ⟨k, hk⟩ := hj
    exact ⟨k, by omega⟩
  exact (X.hasB_iff_of_even hpar d₁).mpr hd₁

private theorem Z_pred_le_Z_h (H : X.Sec4Hyp s r) {d₀ d₁ : ℕ} (hd₀ : X.HasB 0 d₀)
    (hd₁ : X.HasB 1 d₁)
    (hna : ¬ ⁅X.Z 1, X.Z ((d₁ : ℤ) + 1)⁆ ≤ X.Z 1 ⊓ X.Z ((d₁ : ℤ) + 1))
    (hodd₀ : Odd d₀) : X.Z (d₁ : ℤ) ≤ X.Z ((d₁ : ℤ) + 1) := by
  obtain ⟨hlt, hodd1, -, -⟩ := X.s45_lt_odd_of_not_comm_le H hd₀ hd₁ hna
  have hd1ge : 5 ≤ d₁ := (X.s45_facts H hd₀ hd₁ hna hodd₀).2.2.1
  have hodd1Z : Odd (d₁ : ℤ) := (Int.odd_coe_nat d₁).mpr hodd1
  have hZ1 : X.Z 1 = centerOf (X.L 1) := (X.s45_step11 H hd₀ hd₁ hna hodd₀).1
  have hB1 : X.HasB (d₁ : ℤ) d₁ := X.hasB_of_odd hd₁ hodd1Z
  have hZc : X.Z (d₁ : ℤ) = centerOf (X.L (d₁ : ℤ)) :=
    X.Z_eq_centerOf_of_even_sub (hodd1Z.sub_odd odd_one) hZ1
  have hQ : X.Z (d₁ : ℤ) ≤ X.Q ((d₁ : ℤ) + 1) :=
    X.Z_le_Q_of_lt hB1 (j := (d₁ : ℤ) + 1) (by
      rw [show (((d₁ : ℤ) + 1) - (d₁ : ℤ)).natAbs = 1 by norm_num]
      omega)
  have hP : X.Z (d₁ : ℤ) ≤ X.edgeSylow (d₁ : ℤ) :=
    hQ.trans (by
      simpa [show ((d₁ : ℤ) + 1 - 1) = (d₁ : ℤ) by ring]
        using X.Q_le_edgeSylow_right ((d₁ : ℤ) + 1))
  have hcent : X.Z (d₁ : ℤ) ≤ Subgroup.centralizer (X.edgeSylow (d₁ : ℤ) : Set G) := by
    intro z hz
    rw [hZc] at hz
    obtain ⟨hzL, hzC⟩ := Subgroup.mem_inf.mp hz
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    exact Subgroup.mem_centralizer_iff.mp hzC s (X.edgeSylow_le_L (d₁ : ℤ) hs)
  have hP1 : IsSylowTwoOf (X.edgeSylow (d₁ : ℤ)) (X.Gi ((d₁ : ℤ) + 1)) :=
    X.isSylowTwoOf_edgeSylow_Gi_succ (d₁ : ℤ)
  have hzfacts := X.centerOf_sylow_le_Z H.char ((d₁ : ℤ) + 1) hP1
  have hcenter : X.Z (d₁ : ℤ) ≤ centerOf (X.edgeSylow (d₁ : ℤ)) := le_inf hP hcent
  have hzle : centerOf (X.edgeSylow (d₁ : ℤ)) ≤ X.Z ((d₁ : ℤ) + 1) := hzfacts.1
  exact hcenter.trans hzle

private theorem Z_succ_le_Z_h (H : X.Sec4Hyp s r) {d₀ d₁ : ℕ} (hd₀ : X.HasB 0 d₀)
    (hd₁ : X.HasB 1 d₁)
    (hna : ¬ ⁅X.Z 1, X.Z ((d₁ : ℤ) + 1)⁆ ≤ X.Z 1 ⊓ X.Z ((d₁ : ℤ) + 1))
    (hodd₀ : Odd d₀) : X.Z ((d₁ : ℤ) + 2) ≤ X.Z ((d₁ : ℤ) + 1) := by
  obtain ⟨t, -, htref⟩ := X.exists_reflection H ((d₁ : ℤ) + 1)
  have ht_succ : t • X.vert ((d₁ : ℤ) + 2) = X.vert (d₁ : ℤ) := by
    have h := htref 1
    rw [show (d₁ : ℤ) + 1 + 1 = (d₁ : ℤ) + 2 by ring,
      show (d₁ : ℤ) + 1 - 1 = (d₁ : ℤ) by ring] at h
    exact h
  have ht_h : t • X.vert ((d₁ : ℤ) + 1) = X.vert ((d₁ : ℤ) + 1) := by
    have h := htref 0
    simpa using h
  have ht_inv : t⁻¹ • X.vert (d₁ : ℤ) = X.vert ((d₁ : ℤ) + 2) := by
    have h := congrArg (fun w : V => t⁻¹ • w) ht_succ
    rw [← mul_smul, inv_mul_cancel, one_smul] at h
    exact h.symm
  have ht_h_inv : t⁻¹ • X.vert ((d₁ : ℤ) + 1) = X.vert ((d₁ : ℤ) + 1) := by
    have h := congrArg (fun w : V => t⁻¹ • w) ht_h
    rw [← mul_smul, inv_mul_cancel, one_smul] at h
    exact h.symm
  have h1 : X.Z ((d₁ : ℤ) + 2) = conjSub t⁻¹ (X.Z (d₁ : ℤ)) := X.Z_smul X ht_inv
  have h2 : X.Z ((d₁ : ℤ) + 1) = conjSub t⁻¹ (X.Z ((d₁ : ℤ) + 1)) :=
    X.Z_smul X ht_h_inv
  have h := conjSub_mono t⁻¹ (X.Z_pred_le_Z_h H hd₀ hd₁ hna hodd₀)
  rw [h1, h2]
  exact h

private theorem Z_pred_inf_Z_succ_eq_bot (H : X.Sec4Hyp s r) {d₀ d₁ : ℕ}
    (hd₀ : X.HasB 0 d₀) (hd₁ : X.HasB 1 d₁)
    (hna : ¬ ⁅X.Z 1, X.Z ((d₁ : ℤ) + 1)⁆ ≤ X.Z 1 ⊓ X.Z ((d₁ : ℤ) + 1))
    (hodd₀ : Odd d₀) :
    X.Z (d₁ : ℤ) ⊓ X.Z ((d₁ : ℤ) + 2) = ⊥ := by
  have hZ1 : X.Z 1 = centerOf (X.L 1) := (X.s45_step11 H hd₀ hd₁ hna hodd₀).1
  have hodd1 : Odd (d₁ : ℤ) :=
    (Int.odd_coe_nat d₁).mpr (X.s45_lt_odd_of_not_comm_le H hd₀ hd₁ hna).2.1
  have hodd2 : Odd ((d₁ : ℤ) + 2) := by
    obtain ⟨k, hk⟩ := hodd1
    exact ⟨k + 1, by omega⟩
  have hpred : X.Z (d₁ : ℤ) = centerOf (X.L (d₁ : ℤ)) :=
    X.Z_eq_centerOf_of_even_sub (hodd1.sub_odd odd_one) hZ1
  have hsucc : X.Z ((d₁ : ℤ) + 2) = centerOf (X.L ((d₁ : ℤ) + 2)) :=
    X.Z_eq_centerOf_of_even_sub (hodd2.sub_odd odd_one) hZ1
  set D : Subgroup G := X.Z (d₁ : ℤ) ⊓ X.Z ((d₁ : ℤ) + 2) with hD
  have hDZ : D ≤ X.Z ((d₁ : ℤ) + 1) :=
    inf_le_left.trans (X.Z_pred_le_Z_h H hd₀ hd₁ hna hodd₀)
  have hDpred : D ≤ Subgroup.centralizer (X.L (d₁ : ℤ) : Set G) := by
    have h : D ≤ centerOf (X.L (d₁ : ℤ)) := by rw [← hpred]; exact inf_le_left
    exact h.trans inf_le_right
  have hDsucc : D ≤ Subgroup.centralizer (X.L ((d₁ : ℤ) + 2) : Set G) := by
    have h : D ≤ centerOf (X.L ((d₁ : ℤ) + 2)) := by rw [← hsucc]; exact inf_le_right
    exact h.trans inf_le_right
  have hDQ : D ≤ Subgroup.centralizer (X.Q ((d₁ : ℤ) + 1) : Set G) :=
    hDZ.trans ((X.Z_le_center _).trans inf_le_right)
  have hLgen : X.L ((d₁ : ℤ) + 1) ≤
      X.L (d₁ : ℤ) ⊔ X.L ((d₁ : ℤ) + 2) ⊔ X.Q ((d₁ : ℤ) + 1) := by
    have hLh : X.L ((d₁ : ℤ) + 1) =
        X.edgeSylow ((d₁ : ℤ) + 1 - 1) ⊔ X.edgeSylow ((d₁ : ℤ) + 1) :=
      (X.edgeSylow_sup_edgeSylow ((d₁ : ℤ) + 1)).symm
    rw [hLh, show (d₁ : ℤ) + 1 - 1 = (d₁ : ℤ) by ring]
    refine sup_le ?_ ?_
    · exact (X.edgeSylow_le_L (d₁ : ℤ)).trans (le_sup_left.trans le_sup_left)
    · exact (X.isSylowTwoOf_edgeSylow_L_succ ((d₁ : ℤ) + 1)).1.trans
        (le_sup_right.trans le_sup_left)
  have hDpred' : X.L (d₁ : ℤ) ≤ Subgroup.centralizer (D : Set G) := by
    intro l hl
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (Subgroup.mem_centralizer_iff.mp (hDpred hx) l hl).symm
  have hDsucc' : X.L ((d₁ : ℤ) + 2) ≤ Subgroup.centralizer (D : Set G) := by
    intro l hl
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (Subgroup.mem_centralizer_iff.mp (hDsucc hx) l hl).symm
  have hDQ' : X.Q ((d₁ : ℤ) + 1) ≤ Subgroup.centralizer (D : Set G) := by
    intro l hl
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (Subgroup.mem_centralizer_iff.mp (hDQ hx) l hl).symm
  have hDcent : X.L ((d₁ : ℤ) + 1) ≤ Subgroup.centralizer (D : Set G) :=
    hLgen.trans (sup_le (sup_le hDpred' hDsucc') hDQ')
  have hmem : D ≤ X.Z ((d₁ : ℤ) + 1) ⊓
      Subgroup.centralizer (X.L ((d₁ : ℤ) + 1) : Set G) :=
    le_inf hDZ (by
      intro x hx
      exact Subgroup.mem_centralizer_iff.mpr fun l hl =>
        (Subgroup.mem_centralizer_iff.mp (hDcent hl) x hx).symm)
  rw [X.C_Z_h_L_h_eq_bot H hd₀ hd₁ hna hodd₀] at hmem
  exact le_bot_iff.mp hmem

private theorem W_le_Z_h (H : X.Sec4Hyp s r) {d₀ d₁ : ℕ} (hd₀ : X.HasB 0 d₀)
    (hd₁ : X.HasB 1 d₁)
    (hna : ¬ ⁅X.Z 1, X.Z ((d₁ : ℤ) + 1)⁆ ≤ X.Z 1 ⊓ X.Z ((d₁ : ℤ) + 1))
    (hodd₀ : Odd d₀) :
    X.Z (d₁ : ℤ) ⊔ X.Z ((d₁ : ℤ) + 2) ≤ X.Z ((d₁ : ℤ) + 1) :=
  sup_le (X.Z_pred_le_Z_h H hd₀ hd₁ hna hodd₀) (X.Z_succ_le_Z_h H hd₀ hd₁ hna hodd₀)

private theorem s45_card_W (H : X.Sec4Hyp s r) {d₀ d₁ : ℕ} (hd₀ : X.HasB 0 d₀)
    (hd₁ : X.HasB 1 d₁)
    (hna : ¬ ⁅X.Z 1, X.Z ((d₁ : ℤ) + 1)⁆ ≤ X.Z 1 ⊓ X.Z ((d₁ : ℤ) + 1))
    (hodd₀ : Odd d₀) :
    Nat.card (↥(X.Z (d₁ : ℤ) ⊔ X.Z ((d₁ : ℤ) + 2) : Subgroup G)) = 2 ^ (2 * X.n 0) := by
  have hinf : X.Z (d₁ : ℤ) ⊓ X.Z ((d₁ : ℤ) + 2) = ⊥ :=
    X.Z_pred_inf_Z_succ_eq_bot H hd₀ hd₁ hna hodd₀
  have hodd1 : Odd (d₁ : ℤ) :=
    (Int.odd_coe_nat d₁).mpr (X.s45_lt_odd_of_not_comm_le H hd₀ hd₁ hna).2.1
  have hodd2 : Odd ((d₁ : ℤ) + 2) := by
    obtain ⟨k, hk⟩ := hodd1
    exact ⟨k + 1, by omega⟩
  have hcard1 : Nat.card (X.Z (d₁ : ℤ)) = 2 ^ X.n 0 :=
    X.card_Z_of_odd H hd₀ hd₁ hna hodd₀ hodd1
  have hcard2 : Nat.card (X.Z ((d₁ : ℤ) + 2)) = 2 ^ X.n 0 :=
    X.card_Z_of_odd H hd₀ hd₁ hna hodd₀ hodd2
  have hcomm : ∀ a ∈ X.Z (d₁ : ℤ), ∀ b ∈ X.Z ((d₁ : ℤ) + 2),
      a * b * a⁻¹ ∈ X.Z ((d₁ : ℤ) + 2) := by
    intro a ha b hb
    have haZ : a ∈ X.Z ((d₁ : ℤ) + 1) := X.Z_pred_le_Z_h H hd₀ hd₁ hna hodd₀ ha
    have hbZ : b ∈ X.Z ((d₁ : ℤ) + 1) := X.Z_succ_le_Z_h H hd₀ hd₁ hna hodd₀ hb
    have hc : a * b = b * a := X.Z_commute ((d₁ : ℤ) + 1) a haZ b hbZ
    have hform : a * b * a⁻¹ = b := by
      rw [hc]; group
    rw [hform]
    exact hb
  have h := CFSG.Timmesfeld.LocalTwoSubgroups.FrobeniusFixedSpaceBounds.card_sup_mul_card_inf
    (X.Z (d₁ : ℤ)) (X.Z ((d₁ : ℤ) + 2)) hcomm
  have hbot : Nat.card ↥(⊥ : Subgroup G) = 1 := by simp
  rw [hinf, hcard1, hcard2, hbot, mul_one] at h
  rw [two_mul, pow_add]
  exact h

section NatModAux

open Matrix

private def vecE1 {K : Type*} [Field K] : K →+ (Fin 2 → K) where
  toFun s := ![s, 0]
  map_zero' := by ext i; fin_cases i <;> simp
  map_add' s t := by ext i; fin_cases i <;> simp [add_comm]

private theorem vecE1_injective {K : Type*} [Field K] : Function.Injective (vecE1 (K := K)) := by
  intro s t h
  have := congrFun h 0
  simpa [vecE1] using this

private theorem natural_fixed_upper_eq_commutator {K : Type*} [Field K] [CharP K 2] {W : Type*}
    [AddCommGroup W] [DistribMulAction (Matrix.SpecialLinearGroup (Fin 2) K) W]
    {θ : (Fin 2 → K) →+ W}
    (hθ : ∀ (x : Matrix.SpecialLinearGroup (Fin 2) K) (v : Fin 2 → K),
      θ ((x : Matrix (Fin 2) (Fin 2) K) *ᵥ v) = x • θ v)
    (hinj : Function.Injective θ) :
    (∀ y : W, y ∈ (θ.comp (vecE1 (K := K))).range ↔
        (y ∈ θ.range ∧ ∀ a ∈ CFSG.Timmesfeld.upperUnipotent K, a • y = y)) ∧
      (∀ y : W, y ∈ (θ.comp (vecE1 (K := K))).range ↔
        ∃ a ∈ CFSG.Timmesfeld.upperUnipotent K, ∃ v ∈ θ.range, y = a • v - v) ∧
      Nat.card ↥((θ.comp (vecE1 (K := K))).range) = Nat.card K := by
  classical
  constructor
  · intro y
    have h := CFSG.Timmesfeld.ARS.NaturalModule.mem_fixed_upper_iff (K := K) (θ := θ)
      (y := y) hθ hinj
    constructor
    · intro hy
      exact h.mpr (AddMonoidHom.mem_range.mp hy)
    · intro hy
      exact AddMonoidHom.mem_range.mpr (h.mp hy)
  constructor
  · intro y
    constructor
    · intro hy
      obtain ⟨s, hs⟩ := AddMonoidHom.mem_range.mp hy
      refine ⟨CFSG.Timmesfeld.RankOne.upperElt K 1,
        (CFSG.Timmesfeld.RankOne.mem_upperUnipotent_iff K).2 ⟨1, rfl⟩, θ ![0, s], ?_, ?_⟩
      · exact AddMonoidHom.mem_range.mpr ⟨![0, s], rfl⟩
      · rw [← hs]
        have h := CFSG.Timmesfeld.ARS.NaturalModule.upperElt_smul_sub_eq (K := K) (θ := θ)
          hθ 1 ![0, s]
        simpa [vecE1] using h.symm
    · rintro ⟨a, ha, v, hv, rfl⟩
      obtain ⟨t, rfl⟩ := (CFSG.Timmesfeld.RankOne.mem_upperUnipotent_iff K).1 ha
      obtain ⟨u, rfl⟩ := AddMonoidHom.mem_range.mp hv
      have h := CFSG.Timmesfeld.ARS.NaturalModule.upperElt_smul_sub_eq (K := K) (θ := θ) hθ t u
      rw [h]
      exact AddMonoidHom.mem_range.mpr ⟨_, rfl⟩
  · have hinj' : Function.Injective (θ.comp (vecE1 (K := K))) := hinj.comp vecE1_injective
    have e : K ≃ ↥((θ.comp (vecE1 (K := K))).range) :=
      Equiv.ofBijective
        (fun s => (⟨(θ.comp (vecE1 (K := K))) s,
          AddMonoidHom.mem_range.mpr ⟨s, rfl⟩⟩ : ↥((θ.comp (vecE1 (K := K))).range)))
        ⟨fun a b h => hinj' (Subtype.ext_iff.mp h), fun y => by
          obtain ⟨s, hs⟩ := AddMonoidHom.mem_range.mp y.2
          exact ⟨s, Subtype.ext hs⟩⟩
    exact (Nat.card_congr e).symm

end NatModAux

private theorem two_pow_factorization_card_sl_local {K : Type*} [Field K] [Finite K] [CharP K 2] :
    2 ^ Nat.factorization (Nat.card (Matrix.SpecialLinearGroup (Fin 2) K)) 2 = Nat.card K := by
  classical
  let _ : Fintype K := Fintype.ofFinite K
  obtain ⟨n, h2, hq⟩ := FiniteField.card K 2
  have hqnat : Nat.card K = 2 ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hq]
  have hn1 : 1 ≤ (n : ℕ) := n.pos
  have hq2 : 2 ≤ Nat.card K := by
    rw [hqnat]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (n : ℕ) := Nat.pow_le_pow_right (by norm_num) hn1
  have hcardSL : Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) =
      Nat.card K * (Nat.card K ^ 2 - 1) :=
    CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two K
  have hqne : Nat.card K ≠ 0 := by omega
  have hsubne : Nat.card K ^ 2 - 1 ≠ 0 := by
    have : 4 ≤ Nat.card K ^ 2 := by nlinarith
    omega
  have hodd : ¬ 2 ∣ Nat.card K ^ 2 - 1 := by
    have h2dvd : 2 ∣ Nat.card K := by
      rw [hqnat]
      exact dvd_pow_self 2 (by omega : (n : ℕ) ≠ 0)
    obtain ⟨c, hc⟩ := h2dvd
    intro h
    obtain ⟨d, hd⟩ := h
    have hsq : Nat.card K ^ 2 = 2 * (2 * c ^ 2) := by rw [hc]; ring
    omega
  have hfac : Nat.factorization (Nat.card (Matrix.SpecialLinearGroup (Fin 2) K)) 2 = (n : ℕ) := by
    rw [hcardSL, Nat.factorization_mul hqne hsubne]
    have h1 : Nat.factorization (Nat.card K) 2 = (n : ℕ) := by
      rw [hqnat, Nat.factorization_pow_self Nat.prime_two]
    have h2' : Nat.factorization (Nat.card K ^ 2 - 1) 2 = 0 :=
      Nat.factorization_eq_zero_of_not_dvd hodd
    rw [Finsupp.coe_add, Pi.add_apply, h1, h2', add_zero]
  rw [hfac, hqnat]

private theorem card_map_sylow_local {K : Type*} [Field K] [Finite K] [CharP K 2]
    {G : Type*} [Group G] {L P : Subgroup G} [Finite ↥L]
    {φ : ↥L →* Matrix.SpecialLinearGroup (Fin 2) K}
    (hφs : Function.Surjective φ)
    (hker : φ.ker = (pCoreOf 2 L).subgroupOf L)
    (hP : IsSylowTwoOf P L) (hOleP : pCoreOf 2 L ≤ P) :
    Nat.card ↥((P.subgroupOf L).map φ) = Nat.card K := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H : Subgroup ↥L := P.subgroupOf L with hH
  have hHgrp : IsPGroup 2 H := by
    rw [hH, Subgroup.subgroupOf]
    exact hP.2.1.comap_of_injective L.subtype L.subtype_injective
  have hkerH : φ.ker ≤ H := by
    rw [hker, hH]
    exact Subgroup.subgroupOf_mono L hOleP
  have hHidx_map : ¬ 2 ∣ (H.map φ).index := by
    rw [Subgroup.index_map_eq H hφs hkerH]
    exact hP.2.2
  let U : Sylow 2 (Matrix.SpecialLinearGroup (Fin 2) K) :=
    (hHgrp.map φ).toSylow hHidx_map
  have hcard : Nat.card U = 2 ^ Nat.factorization
      (Nat.card (Matrix.SpecialLinearGroup (Fin 2) K)) 2 := Sylow.card_eq_multiplicity U
  rw [IsPGroup.toSylow_coe] at hcard
  rw [hcard, two_pow_factorization_card_sl_local]

private theorem exists_SL2_hom_map_eq_upperUnipotent {L P : Subgroup G} [Finite ↥L]
    {n : ℕ} (hL2 : IsL2Quot n (oTwoQuot ↥L)) (hP : IsSylowTwoOf P L) :
    ∃ φ : ↥L →* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n),
      Function.Surjective φ ∧ φ.ker = (pCoreOf 2 L).subgroupOf L ∧
      (P.subgroupOf L).map φ = CFSG.Timmesfeld.upperUnipotent (GaloisField 2 n) := by
  classical
  let K := GaloisField 2 n
  obtain ⟨e2⟩ := hL2
  let eSL : Matrix.ProjectiveSpecialLinearGroup (Fin 2) K ≃*
      Matrix.SpecialLinearGroup (Fin 2) K := CFSG.Quasithin.pslTwoGf2EquivSl n
  let q : ↥L →* oTwoQuot ↥L := QuotientGroup.mk' (CFSG.pCore 2 ↥L)
  let φ : ↥L →* Matrix.SpecialLinearGroup (Fin 2) K :=
    eSL.toMonoidHom.comp (e2.toMonoidHom.comp q)
  have hφs : Function.Surjective φ :=
    eSL.surjective.comp (e2.surjective.comp (QuotientGroup.mk'_surjective _))
  have hφker : φ.ker = (pCoreOf 2 L).subgroupOf L := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hx
      have h1 : e2 (q x) = 1 := eSL.injective (by simpa [φ] using hx)
      have h2 : q x = 1 := e2.injective (by simpa using h1)
      have h3 : x ∈ CFSG.pCore 2 ↥L := (QuotientGroup.eq_one_iff x).mp h2
      exact Subgroup.mem_map.mpr ⟨x, h3, rfl⟩
    · intro hx
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
      have hxy : x = y := Subtype.ext hyx.symm
      have h3 : x ∈ CFSG.pCore 2 ↥L := hxy ▸ hy
      have h2 : q x = 1 := (QuotientGroup.eq_one_iff x).mpr h3
      simpa [φ, h2]
  have hOleP : pCoreOf 2 L ≤ P := pCoreOf_le_of_isSylowTwoOf hP
  have hUcard : Nat.card ↥((P.subgroupOf L).map φ) = Nat.card K :=
    card_map_sylow_local hφs hφker hP hOleP
  let _ : Fintype K := Fintype.ofFinite K
  obtain ⟨m, -, hKcard'⟩ := FiniteField.card K 2
  have hKcard'' : Nat.card K = 2 ^ (m : ℕ) := by rw [Nat.card_eq_fintype_card, hKcard']
  obtain ⟨g, hg⟩ := CFSG.SL2MinimalFaithful.exists_conj_unipotent_mem
    (F := K) (p := 2) (f := (m : ℕ)) Nat.prime_two hKcard'' hUcard
  have huni : ∀ t : K, CFSG.SL2MinimalFaithful.unipotent t = CFSG.Timmesfeld.RankOne.upperElt K t :=
    fun t => Subtype.ext rfl
  have hle : (CFSG.Timmesfeld.upperUnipotent K).map (MulAut.conj g).toMonoidHom ≤
      (P.subgroupOf L).map φ := by
    intro y hy
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hy
    obtain ⟨t, rfl⟩ := (CFSG.Timmesfeld.RankOne.mem_upperUnipotent_iff K).1 hz
    change (MulAut.conj g) (CFSG.Timmesfeld.RankOne.upperElt K t) ∈ (P.subgroupOf L).map φ
    rw [MulAut.conj_apply]
    simpa [huni] using hg t
  have hUeq : (CFSG.Timmesfeld.upperUnipotent K).map (MulAut.conj g).toMonoidHom =
      (P.subgroupOf L).map φ :=
    Subgroup.eq_of_le_of_card_ge hle (by
      rw [Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom)
        (MulAut.conj g).injective, CFSG.Timmesfeld.RankOne.card_upperUnipotent, hUcard])
  let φ' : ↥L →* Matrix.SpecialLinearGroup (Fin 2) K :=
    (MulAut.conj g⁻¹).toMonoidHom.comp φ
  have hφ's : Function.Surjective φ' := (MulAut.conj g⁻¹).surjective.comp hφs
  have hφ'ker : φ'.ker = (pCoreOf 2 L).subgroupOf L := by
    ext x
    show (MulAut.conj g⁻¹) (φ x) = 1 ↔ x ∈ (pCoreOf 2 L).subgroupOf L
    rw [MulEquiv.map_eq_one_iff, ← hφker]
    rfl
  have hcomp : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom
      = MonoidHom.id (Matrix.SpecialLinearGroup (Fin 2) K) := by
    refine MonoidHom.ext fun x => ?_
    apply Subtype.ext
    simp only [MonoidHom.comp_apply, MonoidHom.id_apply, MulEquiv.coe_toMonoidHom]
    rw [MulAut.conj_apply, MulAut.conj_apply]
    group
  have hU'eq : (P.subgroupOf L).map φ' = CFSG.Timmesfeld.upperUnipotent K := by
    have h1 : (P.subgroupOf L).map φ' = ((P.subgroupOf L).map φ).map
        (MulAut.conj g⁻¹).toMonoidHom := by
      rw [Subgroup.map_map]
    rw [h1, ← hUeq, Subgroup.map_map, hcomp, Subgroup.map_id]
  exact ⟨φ', hφ's, hφ'ker, hU'eq⟩

private theorem nonempty_sectionModule_Z (i : ℤ) {K : Type*} [Field K]
    {φ : ↥(X.L i) →* Matrix.SpecialLinearGroup (Fin 2) K} (hφs : Function.Surjective φ)
    (hφker : φ.ker = (pCoreOf 2 (X.L i)).subgroupOf (X.L i)) :
    Nonempty (CFSG.RankThree.GF2n.SectionModule (X.L i) (X.Z i) ⊥ φ) := by
  have hXX : ∀ x ∈ X.Z i, ∀ y ∈ X.Z i, ⁅x, y⁆ ∈ (⊥ : Subgroup G) := by
    intro x hx y hy
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact X.Z_commute i x hx y hy
  have hLV : X.L i ≤ Subgroup.normalizer (X.Z i : Set G) := by
    intro a ha
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr
      (X.Z_normal i a (X.L_le_Gi i ha))
  have hAX : ∀ a ∈ X.L i, ∀ x ∈ X.Z i, a * x * a⁻¹ ∈ X.Z i :=
    fun a ha x hx => (Subgroup.mem_normalizer_iff.mp (hLV ha) x).mp hx
  have hAC : ∀ a ∈ X.L i, ∀ x ∈ (⊥ : Subgroup G), a * x * a⁻¹ ∈ (⊥ : Subgroup G) := by
    intro a ha x hx
    rw [Subgroup.mem_bot] at hx ⊢
    rw [hx, mul_one, mul_inv_cancel]
  have hQeq : pCoreOf 2 (X.L i) = X.Q i := by
    simpa using (X.hyp.isLocL2_oTwoPrime (X.vert i)).pCoreOf_eq
  have hker : ∀ a : ↥(X.L i), φ a = 1 → ∀ x ∈ X.Z i, ⁅(a : G), x⁆ ∈ (⊥ : Subgroup G) := by
    intro a ha x hx
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    have hamem : (a : G) ∈ pCoreOf 2 (X.L i) := by
      have h : a ∈ φ.ker := MonoidHom.mem_ker.mpr ha
      rw [hφker] at h
      exact Subgroup.mem_subgroupOf.mp h
    have haQ : (a : G) ∈ X.Q i := by rwa [hQeq] at hamem
    exact Subgroup.mem_centralizer_iff.mp
      (Subgroup.mem_inf.mp (X.Z_le_center i hx)).2 (a : G) haQ
  exact CFSG.RankThree.GF2n.exists_sectionModule φ hφs bot_le hXX hAX hAC hker

private theorem edgeSylow_eq_Z_one_sup_Q (H : X.Sec4Hyp s r) {d₁ : ℕ}
    (hd₁ : X.HasB 1 d₁) : X.edgeSylow (d₁ : ℤ) = X.Z 1 ⊔ X.Q ((d₁ : ℤ) + 1) := by
  have hK : X.K ≤ Subgroup.normalizer (X.Z 1 : Set G) := by
    intro k hk
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact X.Z_normal 1 k (X.K_le_Gi 1 hk)
  have hA : X.Z 1 ≤ X.edgeSylow (d₁ : ℤ) := X.Z_one_le_edgeSylow H hd₁
  have hnot : ¬ X.Z 1 ≤ X.Q ((d₁ : ℤ) + 1) := by
    intro hle
    apply hd₁.2.1
    have hq := (X.Q_le_Gi_adj ((d₁ : ℤ) + 1)).trans inf_le_right
    refine hle.trans ?_
    simpa [show (d₁ : ℤ) + 1 + 1 = 1 + (d₁ : ℤ) + 1 by ring] using hq
  simpa using (X.sup_Q_eq_edgeSylow_of_gen (d₁ : ℤ) (inf_le_left.trans hK) hA hnot).symm

private theorem commutator_Z_h_edgeSylow_le (H : X.Sec4Hyp s r) {d₀ d₁ : ℕ}
    (hd₀ : X.HasB 0 d₀) (hd₁ : X.HasB 1 d₁)
    (hna : ¬ ⁅X.Z 1, X.Z ((d₁ : ℤ) + 1)⁆ ≤ X.Z 1 ⊓ X.Z ((d₁ : ℤ) + 1))
    (hodd₀ : Odd d₀) :
    ⁅X.Z ((d₁ : ℤ) + 1), X.edgeSylow (d₁ : ℤ)⁆ ≤ X.Z (d₁ : ℤ) := by
  have hPN : X.edgeSylow (d₁ : ℤ) ≤ Subgroup.normalizer (X.Z (d₁ : ℤ) : Set G) :=
    fun p hp => Subgroup.mem_normalizer_iff_map_conj_eq.mpr
      (X.Z_normal (d₁ : ℤ) p (X.L_le_Gi _ (X.edgeSylow_le_L (d₁ : ℤ) hp)))
  have hdec := X.edgeSylow_eq_Z_one_sup_Q H hd₁
  have hVQbot : ⁅X.Z ((d₁ : ℤ) + 1), X.Q ((d₁ : ℤ) + 1)⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro v hv
    exact (Subgroup.mem_inf.mp (X.Z_le_center ((d₁ : ℤ) + 1) hv)).2
  rw [hdec, Subgroup.commutator_comm]
  exact CFSG.GorensteinWalter.commutator_sup_le_of_commutator_le_and_normalize _ _ _ _
    (X.s45_R_le_Z_pred H hd₀ hd₁ hna hodd₀)
    (by rw [Subgroup.commutator_comm, hVQbot]; exact bot_le)
    ((le_sup_left.trans hdec.ge).trans hPN) ((le_sup_right.trans hdec.ge).trans hPN)

private theorem commutator_Z_h_edgeSylow_ne_bot (H : X.Sec4Hyp s r) {d₀ d₁ : ℕ}
    (hd₀ : X.HasB 0 d₀) (hd₁ : X.HasB 1 d₁)
    (hna : ¬ ⁅X.Z 1, X.Z ((d₁ : ℤ) + 1)⁆ ≤ X.Z 1 ⊓ X.Z ((d₁ : ℤ) + 1))
    (hodd₀ : Odd d₀) : ⁅X.Z ((d₁ : ℤ) + 1), X.edgeSylow (d₁ : ℤ)⁆ ≠ ⊥ := by
  intro hbot
  apply (X.s45_facts H hd₀ hd₁ hna hodd₀).2.2.2.2.2
  rw [Subgroup.commutator_comm, eq_bot_iff, ← hbot]
  exact Subgroup.commutator_mono le_rfl (X.Z_one_le_edgeSylow H hd₁)

private theorem fixed_eq_zero_of_inf_centralizer_eq_bot {A Y : Subgroup G} {K : Type*}
    [Field K] {φ : ↥A →* Matrix.SpecialLinearGroup (Fin 2) K}
    (S : CFSG.RankThree.GF2n.SectionModule A Y ⊥ φ)
    (hAY : A ≤ Subgroup.normalizer (Y : Set G))
    (hC : Y ⊓ Subgroup.centralizer (A : Set G) = ⊥) (v : S.W)
    (hv : ∀ x : Matrix.SpecialLinearGroup (Fin 2) K, x • v = v) : v = 0 := by
  obtain ⟨x, rfl⟩ := S.surjective v
  have hcomm : ∀ l : ↥A, ⁅(x : G), (l : G)⁆ ∈ (⊥ : Subgroup G) := by
    intro l
    have hxl : (l : G) * (x : G) * (l : G)⁻¹ ∈ Y :=
      (Subgroup.mem_normalizer_iff.mp (hAY l.2) x).mp x.2
    let y : ↥Y := ⟨(l : G) * (x : G) * (l : G)⁻¹, hxl⟩
    have h2 : φ l • S.π x = S.π y := S.smul_eq l x y rfl
    have h3 : S.π y = S.π x := by rw [← h2]; exact hv (φ l)
    have h4 : S.π (y * x⁻¹) = 0 := by
      rw [S.map_mul, S.map_inv, h3, add_neg_cancel]
    have h5 : ((y * x⁻¹ : ↥Y) : G) ∈ (⊥ : Subgroup G) := (S.eq_zero_iff _).mp h4
    have h6 : ((y * x⁻¹ : ↥Y) : G) = ⁅(l : G), (x : G)⁆ := by
      simp only [y, Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
    rw [h6] at h5
    rw [show ⁅(x : G), (l : G)⁆ = ⁅(l : G), (x : G)⁆⁻¹ from by
      rw [commutatorElement_def, commutatorElement_def]; group]
    exact (⊥ : Subgroup G).inv_mem h5
  have hxZ : (x : G) ∈ (⊥ : Subgroup G) := by
    have hmem := Subgroup.mem_inf.mpr ⟨x.2, Subgroup.mem_centralizer_iff.mpr
      (fun l hl => by
        have h := hcomm ⟨l, hl⟩
        rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h
        exact h.symm)⟩
    rwa [hC] at hmem
  rw [← (S.eq_zero_iff x).mpr hxZ]

private theorem Z_le_iSup_conj_inf_centralizer (H : X.Sec4Hyp s r) (i : ℤ)
    {P : Subgroup G} (hP : IsSylowTwoOf P (X.L i)) (hPG : IsSylowTwoOf P (X.Gi i)) :
    X.Z i ≤ ⨆ l : ↥(X.L i), (X.Z i ⊓ Subgroup.centralizer (P : Set G)).map
      (MulAut.conj (l : G)).toMonoidHom := by
  haveI : Finite ↥(X.L i) := finite_of_le_stabilizer X.hyp (X.L_le_Gi i)
  have hVdef : X.Z i = ⨆ (Q : Subgroup G) (_ : IsSylowTwoOf Q (X.Gi (i))),
      centerOf Q ⊓ X.Q (i) := rfl
  rw [hVdef]
  refine iSup_le fun Q => iSup_le fun hQ => ?_
  have hQL : Q ≤ X.L i := le_oTwoPrime_of_isPGroup hQ.2.1 hQ.1
  have hQsyl : IsSylowTwoOf Q (X.L i) := F7.isSylowTwoOf_mono_right hQ hQL (X.L_le_Gi _)
  obtain ⟨l, hlL, hleQ⟩ := CFSG.Quasithin.RonanF713.isSylowTwoOf_exists_conj_le_loc hP hQL hQ.2.1
  have hcardQ : Nat.card ↥Q = Nat.card ↥P := by
    have hcard : ∀ {S : Subgroup G} (hSL : S ≤ X.L i) (hSs : IsSylowTwoOf S (X.L i)),
        Nat.card ↥S = 2 ^ Nat.factorization (Nat.card ↥(X.L i)) 2 := by
      intro Ss hSL hSs
      obtain ⟨SY, hSY⟩ := F7.isSylowTwoOf_exists_sylow hSs
      have h1 : Nat.card SY = Nat.card ↥Ss := by
        have e1 : ↥SY ≃ ↥(Ss.subgroupOf (X.L i)) :=
          Equiv.cast (congrArg (fun K : Subgroup (X.L i) => ↥K) hSY)
        exact Nat.card_congr (e1.trans (Subgroup.subgroupOfEquivOfLe hSL))
      rw [← h1]
      exact Sylow.card_eq_multiplicity _
    rw [hcard hQL hQsyl, hcard hP.1 hP]
  haveI : Finite ↥P :=
    Finite.of_injective (fun x : ↥P => (⟨x.1, hP.1 x.2⟩ : ↥(X.L i)))
      (fun a b h => Subtype.ext (congrArg (fun z : ↥(X.L i) => (z : G)) h))
  haveI : Finite ↥(conjSub l P) := by
    have hsurj : Function.Surjective (fun p : ↥P =>
        (⟨(MulAut.conj (l : G)) (p : G),
          Subgroup.mem_map_of_mem (f := (MulAut.conj (l : G)).toMonoidHom) p.2⟩ :
          ↥(conjSub l P))) := by
      rintro ⟨q, hq⟩
      rw [conjSub] at hq
      obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.mp hq
      exact ⟨⟨p, hp⟩, rfl⟩
    exact Finite.of_surjective _ hsurj
  have hQeq : Q = conjSub l P :=
    Subgroup.eq_of_le_of_card_ge hleQ (by rw [card_conjSub, hcardQ])
  have hQhconj : conjSub l (X.Q (i)) = X.Q (i) := by
    refine Subgroup.mem_normalizer_iff_map_conj_eq.mp ?_
    exact (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi (i)))
      (X.L_le_Gi _ hlL)
  have hcenterP : centerOf P ⊓ X.Q (i) =
      X.Z i ⊓ Subgroup.centralizer (P : Set G) := by
    have hcent := X.centerOf_sylow_le_Z H.char (i) hPG
    apply le_antisymm
    · rintro y ⟨hyc, hyq⟩
      exact Subgroup.mem_inf.mpr ⟨hcent.1 hyc, (Subgroup.mem_inf.mp hyc).2⟩
    · rintro y hy
      have hy' : y ∈ centerOf P := by
        rw [← hcent.2]
        exact hy
      exact Subgroup.mem_inf.mpr ⟨hy', X.Z_le_Q _ (Subgroup.mem_inf.mp hy).1⟩
  intro x hx
  obtain ⟨hxc, hxq⟩ := Subgroup.mem_inf.mp hx
  have hxc' : x ∈ conjSub l (centerOf P) := by
    rw [← centerOf_conjSub]
    rw [hQeq] at hxc
    exact hxc
  have hxq' : x ∈ conjSub l (X.Q (i)) := by
    rw [hQhconj]
    exact hxq
  have hmem : x ∈ conjSub l (centerOf P ⊓ X.Q (i)) := by
    rw [conjSub_inf]
    exact Subgroup.mem_inf.mpr ⟨hxc', hxq'⟩
  rw [hcenterP] at hmem
  exact le_iSup (fun l : ↥(X.L i) => (X.Z i ⊓ Subgroup.centralizer (P : Set G)).map
    (MulAut.conj (l : G)).toMonoidHom) ⟨l, hlL⟩ hmem

private theorem sectionModule_pi_injective {A Y : Subgroup G} {K : Type*} [Field K]
    {φ : ↥A →* Matrix.SpecialLinearGroup (Fin 2) K}
    (S : CFSG.RankThree.GF2n.SectionModule A Y ⊥ φ) : Function.Injective S.π := by
  intro a b hab
  have h0 : S.π (a * b⁻¹) = 0 := by
    rw [S.map_mul, S.map_inv, hab, add_neg_cancel]
  have hmem : ((a * b⁻¹ : ↥Y) : G) = 1 := by
    have h := (S.eq_zero_iff (a * b⁻¹)).mp h0
    rwa [Subgroup.mem_bot] at h
  have h1 : a * b⁻¹ = 1 := Subtype.ext hmem
  calc a = a * b⁻¹ * b := by group
    _ = 1 * b := by rw [h1]
    _ = b := one_mul b

private theorem card_Z_h (H : X.Sec4Hyp s r) {d₀ d₁ : ℕ} (hd₀ : X.HasB 0 d₀)
    (hd₁ : X.HasB 1 d₁)
    (hna : ¬ ⁅X.Z 1, X.Z ((d₁ : ℤ) + 1)⁆ ≤ X.Z 1 ⊓ X.Z ((d₁ : ℤ) + 1))
    (hodd₀ : Odd d₀) :
    Nat.card (X.Z ((d₁ : ℤ) + 1)) = 2 ^ (2 * X.n 0) := by
  classical
  let K := GaloisField 2 (X.n 0)
  let L : Subgroup G := X.L ((d₁ : ℤ) + 1)
  let V : Subgroup G := X.Z ((d₁ : ℤ) + 1)
  let P : Subgroup G := X.edgeSylow (d₁ : ℤ)
  have hKcard : Nat.card K = 2 ^ X.n 0 :=
    GaloisField.card 2 (X.n 0) (by have := H.two_le_n 0; omega)
  haveI hfL : Finite ↥L := by
    haveI : Finite ↥(X.Gi ((d₁ : ℤ) + 1)) := X.hyp.finite_stab (X.vert _)
    exact Finite.of_injective (Subgroup.inclusion (X.L_le_Gi _)) (Subgroup.inclusion_injective _)
  haveI hfV : Finite ↥V :=
    finite_of_le_stabilizer X.hyp (H := V) (X.Z_le_Gi _)
  have hnh : X.n ((d₁ : ℤ) + 1) = X.n 0 := by
    obtain ⟨k, hk⟩ := (X.s45_lt_odd_of_not_comm_le H hd₀ hd₁ hna).2.1
    rw [show (d₁ : ℤ) + 1 = 0 + 2 * ((k : ℤ) + 1) by omega, X.n_add]
  have hL2 : IsL2Quot (X.n 0) (oTwoQuot ↥L) := by
    have h := (X.hyp.isLocL2_oTwoPrime (X.vert ((d₁ : ℤ) + 1))).quot
    rw [show nOf Γ (X.vert ((d₁ : ℤ) + 1)) = X.n 0 from hnh] at h
    simpa [IsL2Quot, L] using h
  have hP : IsSylowTwoOf P L := X.isSylowTwoOf_edgeSylow_L_succ (d₁ : ℤ)
  obtain ⟨φ', hφ's, hφ'ker, hU'eq⟩ : ∃ φ : ↥L →* Matrix.SpecialLinearGroup (Fin 2) K,
      Function.Surjective φ ∧ φ.ker = (pCoreOf 2 L).subgroupOf L ∧
      (P.subgroupOf L).map φ = CFSG.Timmesfeld.upperUnipotent K :=
    exists_SL2_hom_map_eq_upperUnipotent hL2 hP
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := by
    intro a ha
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr
      (X.Z_normal ((d₁ : ℤ) + 1) a (X.L_le_Gi _ ha))
  have hAX : ∀ a ∈ L, ∀ x ∈ V, a * x * a⁻¹ ∈ V :=
    fun a ha x hx => (Subgroup.mem_normalizer_iff.mp (hLV ha) x).mp hx
  obtain ⟨S⟩ : Nonempty (CFSG.RankThree.GF2n.SectionModule L V ⊥ φ') :=
    X.nonempty_sectionModule_Z ((d₁ : ℤ) + 1) hφ's hφ'ker
  haveI hfW : Finite S.W := Finite.of_surjective S.π S.surjective
  have hP_Gi : IsSylowTwoOf P (X.Gi ((d₁ : ℤ) + 1)) := by
    simpa [P] using X.isSylowTwoOf_edgeSylow_Gi_succ (d₁ : ℤ)
  have hPleL : P ≤ X.L (d₁ : ℤ) := by
    have h := X.edgeSylow_le_L (d₁ : ℤ)
    simpa [P] using h
  have hRV : ⁅V, P⁆ ≤ X.Z (d₁ : ℤ) := X.commutator_Z_h_edgeSylow_le H hd₀ hd₁ hna hodd₀
  have hRleV : ⁅V, P⁆ ≤ V := by
    refine Subgroup.commutator_le.mpr ?_
    intro v hv p hp
    rw [commutatorElement_def]
    rw [show v * p * v⁻¹ * p⁻¹ = v * (p * v⁻¹ * p⁻¹) by group]
    exact V.mul_mem hv ((Subgroup.mem_normalizer_iff.mp (hLV (hP.1 hp)) (v⁻¹)).mp (V.inv_mem hv))
  have hodd1 : Odd (d₁ : ℤ) :=
    (Int.odd_coe_nat d₁).mpr (X.s45_lt_odd_of_not_comm_le H hd₀ hd₁ hna).2.1
  have hZc : X.Z (d₁ : ℤ) = centerOf (X.L (d₁ : ℤ)) :=
    X.Z_eq_centerOf_of_even_sub (hodd1.sub_odd odd_one) (X.s45_step11 H hd₀ hd₁ hna hodd₀).1
  haveI hfZ : Finite ↥(X.Z (d₁ : ℤ)) :=
    finite_of_le_stabilizer X.hyp (H := X.Z (d₁ : ℤ)) (X.Z_le_Gi _)
  have hcardRle : Nat.card ↥⁅V, P⁆ ≤ 2 ^ X.n 0 := by
    calc Nat.card ↥⁅V, P⁆ ≤ Nat.card ↥(X.Z (d₁ : ℤ)) := Subgroup.card_le_of_le hRV
      _ = 2 ^ X.n 0 := X.card_Z_of_odd H hd₀ hd₁ hna hodd₀ hodd1
  have hRne : ⁅V, P⁆ ≠ ⊥ := X.commutator_Z_h_edgeSylow_ne_bot H hd₀ hd₁ hna hodd₀
  have hquadComm : ∀ a ∈ P, ∀ b ∈ P, ∀ x ∈ V, ⁅b, ⁅a, x⁆⁆ ∈ (⊥ : Subgroup G) := by
    intro a ha b hb x hx
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    have hx2 : ⁅x, a⁆ ∈ V := by
      have h1 : (a : G) * x * (a : G)⁻¹ ∈ V :=
        (Subgroup.mem_normalizer_iff.mp (hLV (hP.1 ha)) x).mp hx
      rw [commutatorElement_def]
      rw [show x * a * x⁻¹ * a⁻¹ = x * (a * x⁻¹ * a⁻¹) by group]
      exact V.mul_mem hx ((Subgroup.mem_normalizer_iff.mp (hLV (hP.1 ha)) (x⁻¹)).mp (V.inv_mem hx))
    have hxR : ⁅x, a⁆ ∈ ⁅V, P⁆ := Subgroup.commutator_mem_commutator hx ha
    have hxZ : ⁅x, a⁆ ∈ X.Z (d₁ : ℤ) := hRV hxR
    have hxc : ⁅x, a⁆ ∈ centerOf (X.L (d₁ : ℤ)) := by rwa [← hZc]
    have hbc : b * ⁅x, a⁆ = ⁅x, a⁆ * b :=
      Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hxc).2 b (hPleL hb)
    have hax : ⁅a, x⁆ = ⁅x, a⁆⁻¹ := by rw [commutatorElement_inv]
    rw [hax]
    have h1 : ⁅x, a⁆⁻¹ * b = b * ⁅x, a⁆⁻¹ := by
      calc ⁅x, a⁆⁻¹ * b = ⁅x, a⁆⁻¹ * (b * ⁅x, a⁆) * ⁅x, a⁆⁻¹ := by group
        _ = ⁅x, a⁆⁻¹ * (⁅x, a⁆ * b) * ⁅x, a⁆⁻¹ := by rw [← hbc]
        _ = b * ⁅x, a⁆⁻¹ := by group
    exact h1.symm
  have hquadA : ∀ a ∈ CFSG.Timmesfeld.upperUnipotent K,
      ∀ a' ∈ CFSG.Timmesfeld.upperUnipotent K, ∀ v : S.W,
        a' • (a • v - v) = a • v - v := by
    have h := S.quadratic (A := L) (C := (⊥ : Subgroup G)) (X := V) (Q := P) hAX hP.1 hquadComm
    rwa [hU'eq] at h
  have hfix : ∀ v : S.W, (∀ x : Matrix.SpecialLinearGroup (Fin 2) K, x • v = v) → v = 0 :=
    fixed_eq_zero_of_inf_centralizer_eq_bot S hLV (X.C_Z_h_L_h_eq_bot H hd₀ hd₁ hna hodd₀)
  have hCgen : V ≤ ⨆ l : ↥L, (V ⊓ Subgroup.centralizer (P : Set G)).map
      (MulAut.conj (l : G)).toMonoidHom :=
    X.Z_le_iSup_conj_inf_centralizer H ((d₁ : ℤ) + 1) hP hP_Gi
  let R : Subgroup G := ⁅V, P⁆
  let πR : AddSubgroup S.W :=
    { carrier := {y | ∃ r : ↥R, S.π ⟨(r : G), hRleV r.2⟩ = y}
      zero_mem' := ⟨1, by
        rw [show (⟨((1 : ↥R) : G), hRleV (1 : ↥R).2⟩ : ↥V) = 1 from Subtype.ext rfl,
          S.map_one]⟩
      add_mem' := by
        rintro y z ⟨r, rfl⟩ ⟨s, rfl⟩
        refine ⟨r * s, ?_⟩
        change S.π ⟨((r : G) * (s : G)), hRleV (R.mul_mem r.2 s.2)⟩ =
          S.π ⟨(r : G), hRleV r.2⟩ + S.π ⟨(s : G), hRleV s.2⟩
        rw [show (⟨((r : G) * (s : G)), hRleV (R.mul_mem r.2 s.2)⟩ : ↥V) =
          ⟨(r : G), hRleV r.2⟩ * ⟨(s : G), hRleV s.2⟩ from rfl, S.map_mul]
      neg_mem' := by
        rintro y ⟨r, rfl⟩
        refine ⟨r⁻¹, ?_⟩
        change S.π ⟨((r : G)⁻¹), hRleV (R.inv_mem r.2)⟩ =
          -S.π ⟨(r : G), hRleV r.2⟩
        rw [show (⟨((r : G)⁻¹), hRleV (R.inv_mem r.2)⟩ : ↥V) =
          (⟨(r : G), hRleV r.2⟩ : ↥V)⁻¹ from rfl, S.map_inv] }
  let WA : AddSubgroup S.W := AddSubgroup.closure
    {y | ∃ a ∈ CFSG.Timmesfeld.upperUnipotent K, ∃ v : S.W, y = a • v - v}
  have hWA_le : WA ≤ πR := by
    rw [AddSubgroup.closure_le]
    rintro y ⟨a, ha, v, rfl⟩
    obtain ⟨x, rfl⟩ := S.surjective v
    obtain ⟨t, rfl⟩ := (CFSG.Timmesfeld.RankOne.mem_upperUnipotent_iff K).1 ha
    have hmemU : CFSG.Timmesfeld.RankOne.upperElt K t ∈
        CFSG.Timmesfeld.upperUnipotent K :=
      (CFSG.Timmesfeld.RankOne.mem_upperUnipotent_iff K).2 ⟨t, rfl⟩
    rw [← hU'eq] at hmemU
    obtain ⟨p, hp, hpa⟩ := Subgroup.mem_map.mp hmemU
    have hpP : (p : G) ∈ P := Subgroup.mem_subgroupOf.mp hp
    have hpL : (p : G) ∈ L := hP.1 hpP
    have hpa' : φ' p = CFSG.Timmesfeld.RankOne.upperElt K t := hpa
    have hconjV : (p : G) * (x : G) * (p : G)⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (hLV hpL) x).mp x.2
    have hsm : φ' p • S.π x = S.π ⟨(p : G) * (x : G) * (p : G)⁻¹, hconjV⟩ :=
      S.smul_eq p x ⟨_, hconjV⟩ rfl
    have hval : CFSG.Timmesfeld.RankOne.upperElt K t • S.π x - S.π x =
        S.π ⟨(p : G) * (x : G) * (p : G)⁻¹ * (x : G)⁻¹,
          V.mul_mem hconjV (V.inv_mem x.2)⟩ := by
      rw [← hpa', hsm]
      have h1 : S.π ((⟨(p : G) * (x : G) * (p : G)⁻¹, hconjV⟩ : ↥V) * x⁻¹) =
          S.π ⟨(p : G) * (x : G) * (p : G)⁻¹, hconjV⟩ + S.π x⁻¹ := S.map_mul _ _
      rw [S.map_inv] at h1
      rw [show (⟨(p : G) * (x : G) * (p : G)⁻¹, hconjV⟩ : ↥V) * x⁻¹ =
        ⟨(p : G) * (x : G) * (p : G)⁻¹ * (x : G)⁻¹,
          V.mul_mem hconjV (V.inv_mem x.2)⟩ from rfl] at h1
      rw [h1]
      abel
    rw [hval]
    have hcomm_mem : ⁅(x : G), (p : G)⁆ ∈ R :=
      Subgroup.commutator_mem_commutator x.2 hpP
    have hinv_mem : ⁅(x : G), (p : G)⁆⁻¹ ∈ R := R.inv_mem hcomm_mem
    refine ⟨⟨⁅(x : G), (p : G)⁆⁻¹, hinv_mem⟩, ?_⟩
    apply congrArg S.π
    apply Subtype.ext
    show ⁅(x : G), (p : G)⁆⁻¹ = (p : G) * (x : G) * (p : G)⁻¹ * (x : G)⁻¹
    rw [commutatorElement_def]
    group
  have hπR_le : πR ≤ WA := by
    let Kpre : Subgroup G :=
      { carrier := {r | ∃ hr : r ∈ V, S.π ⟨r, hr⟩ ∈ WA}
        one_mem' := ⟨V.one_mem, by
          rw [show (⟨(1 : G), V.one_mem⟩ : ↥V) = 1 from Subtype.ext rfl, S.map_one]
          exact WA.zero_mem⟩
        mul_mem' := by
          rintro r s ⟨hrV, hrw⟩ ⟨hsV, hsw⟩
          refine ⟨V.mul_mem hrV hsV, ?_⟩
          rw [show (⟨r * s, V.mul_mem hrV hsV⟩ : ↥V) =
            ⟨r, hrV⟩ * ⟨s, hsV⟩ from rfl, S.map_mul]
          exact WA.add_mem hrw hsw
        inv_mem' := by
          rintro r ⟨hrV, hrw⟩
          refine ⟨V.inv_mem hrV, ?_⟩
          rw [show (⟨r⁻¹, V.inv_mem hrV⟩ : ↥V) = (⟨r, hrV⟩ : ↥V)⁻¹ from rfl, S.map_inv]
          exact WA.neg_mem hrw }
    have hcomm_le : R ≤ Kpre := by
      refine Subgroup.commutator_le.mpr ?_
      intro v hv p hp
      have hcomm_mem : ⁅v, p⁆ ∈ R := Subgroup.commutator_mem_commutator hv hp
      refine ⟨hRleV hcomm_mem, ?_⟩
      have hconjV : (p : G) * (v : G)⁻¹ * (p : G)⁻¹ ∈ V :=
        (Subgroup.mem_normalizer_iff.mp (hLV (hP.1 hp)) ((v : G)⁻¹)).mp (V.inv_mem hv)
      have hsm : φ' ⟨p, hP.1 hp⟩ • S.π ⟨v, hv⟩ =
          S.π ⟨(p : G) * (v : G) * (p : G)⁻¹,
            (Subgroup.mem_normalizer_iff.mp (hLV (hP.1 hp)) (v : G)).mp hv⟩ := by
        exact S.smul_eq ⟨p, hP.1 hp⟩ ⟨v, hv⟩
          ⟨_, (Subgroup.mem_normalizer_iff.mp (hLV (hP.1 hp)) (v : G)).mp hv⟩ rfl
      have hsm' : φ' ⟨p, hP.1 hp⟩ • S.π ⟨v⁻¹, V.inv_mem hv⟩ =
          S.π ⟨(p : G) * (v : G)⁻¹ * (p : G)⁻¹, hconjV⟩ :=
        S.smul_eq ⟨p, hP.1 hp⟩ ⟨v⁻¹, V.inv_mem hv⟩ ⟨_, hconjV⟩ rfl
      have hval : S.π ⟨⁅v, p⁆, hRleV hcomm_mem⟩ =
          -(φ' ⟨p, hP.1 hp⟩ • S.π ⟨v, hv⟩ - S.π ⟨v, hv⟩) := by
        have hv1 : ((⟨v, hv⟩ : ↥V) * (⟨(p : G) * (v : G)⁻¹ * (p : G)⁻¹, hconjV⟩) : ↥V) =
            ⟨⁅v, p⁆, hRleV hcomm_mem⟩ := by
          apply Subtype.ext
          simp only [Subgroup.coe_mul, commutatorElement_def]
          group
        have hconjv : (⟨(p : G) * (v : G)⁻¹ * (p : G)⁻¹, hconjV⟩ : ↥V) =
            (⟨(p : G) * (v : G) * (p : G)⁻¹,
              (Subgroup.mem_normalizer_iff.mp (hLV (hP.1 hp)) (v : G)).mp hv⟩ : ↥V)⁻¹ := by
          apply Subtype.ext
          show (p : G) * (v : G)⁻¹ * (p : G)⁻¹ =
            ((p : G) * (v : G) * (p : G)⁻¹)⁻¹
          group
        have hsmv : φ' ⟨p, hP.1 hp⟩ • S.π ⟨v, hv⟩ =
            S.π ⟨(p : G) * (v : G) * (p : G)⁻¹,
              (Subgroup.mem_normalizer_iff.mp (hLV (hP.1 hp)) (v : G)).mp hv⟩ :=
          S.smul_eq ⟨p, hP.1 hp⟩ ⟨v, hv⟩ _ rfl
        rw [← hv1, S.map_mul, hconjv, S.map_inv, ← hsm]
        abel
      rw [hval]
      have hmemU' : φ' ⟨p, hP.1 hp⟩ ∈ CFSG.Timmesfeld.upperUnipotent K := by
        rw [← hU'eq]
        exact Subgroup.mem_map_of_mem _ hp
      exact WA.neg_mem (AddSubgroup.subset_closure
        ⟨φ' ⟨p, hP.1 hp⟩, hmemU', S.π ⟨v, hv⟩, rfl⟩)
    rintro y ⟨r, rfl⟩
    exact (hcomm_le r.2).2
  have hWA_eq : WA = πR := le_antisymm hWA_le hπR_le
  have hVw_of_fixed : ∀ (w : S.W), w ≠ 0 →
      (∀ a ∈ CFSG.Timmesfeld.upperUnipotent K, a • w = w) →
      ∃ (Vw : AddSubgroup S.W) (θw : (Fin 2 → K) →+ S.W),
        Function.Injective θw ∧
        (∀ (x : Matrix.SpecialLinearGroup (Fin 2) K) (v : S.W),
          v ∈ Vw → x • v ∈ Vw) ∧
        θw.range = Vw ∧ Nat.card ↥Vw = 2 ^ (2 * X.n 0) ∧
        Nat.card ↥((θw.comp (vecE1 (K := K))).range) = 2 ^ X.n 0 ∧
        w ∈ (θw.comp (vecE1 (K := K))).range ∧
        (θw.comp (vecE1 (K := K))).range ≤ WA := by
    intro w hw0 hw
    obtain ⟨θw, hinjw, hrange, hew, hθw⟩ :=
      CFSG.Timmesfeld.ARS.exists_natural_of_quadratic (K := K) (V := S.W)
        (hfix := hfix) (hquad := hquadA) (w := w) hw hw0
    have hCwcard : Nat.card ↥((θw.comp (vecE1 (K := K))).range) = 2 ^ X.n 0 := by
      have h := (natural_fixed_upper_eq_commutator (K := K) (W := S.W) (θ := θw) hθw hinjw).2.2
      rw [h, hKcard]
    have hwCw : w ∈ (θw.comp (vecE1 (K := K))).range := by
      have h := (natural_fixed_upper_eq_commutator (K := K) (W := S.W) (θ := θw) hθw hinjw).1 w
      rw [h]
      exact ⟨AddMonoidHom.mem_range.mpr ⟨![1, 0], hew⟩, hw⟩
    have hCwWA : (θw.comp (vecE1 (K := K))).range ≤ WA := by
      have h := (natural_fixed_upper_eq_commutator (K := K) (W := S.W) (θ := θw) hθw hinjw).2.1
      intro y hy
      rw [h] at hy
      obtain ⟨a, ha, v, hv, rfl⟩ := hy
      exact AddSubgroup.subset_closure ⟨a, ha, v, rfl⟩
    have hVwinv : ∀ (x : Matrix.SpecialLinearGroup (Fin 2) K) (v : S.W),
        v ∈ θw.range → x • v ∈ θw.range := by
      intro x v hv
      obtain ⟨u, rfl⟩ := AddMonoidHom.mem_range.mp hv
      rw [← hθw x u]
      exact AddMonoidHom.mem_range.mpr ⟨_, rfl⟩
    refine ⟨θw.range, θw, hinjw, hVwinv, rfl, ?_, hCwcard, hwCw, hCwWA⟩
    have e : (Fin 2 → K) ≃ ↥θw.range :=
      Equiv.ofBijective
        (fun v => (⟨θw v, AddMonoidHom.mem_range.mpr ⟨v, rfl⟩⟩ : ↥θw.range))
        ⟨fun a b h => hinjw (Subtype.ext_iff.mp h), fun y => by
          obtain ⟨v, hv⟩ := AddMonoidHom.mem_range.mp y.2
          exact ⟨v, Subtype.ext hv⟩⟩
    have h1 : Nat.card ↥θw.range = Nat.card (Fin 2 → K) := (Nat.card_congr e).symm
    rw [h1, Nat.card_fun, Nat.card_fin, hKcard, ← pow_mul, Nat.mul_comm (X.n 0) 2]
  have hCSe : V ⊓ Subgroup.centralizer (P : Set G) = R := by
    apply le_antisymm
    · rintro x ⟨hxV, hxC⟩
      have hxC' : ∀ a ∈ CFSG.Timmesfeld.upperUnipotent K,
          a • S.π ⟨x, hxV⟩ = S.π ⟨x, hxV⟩ := by
        intro a ha
        rw [← hU'eq] at ha
        obtain ⟨p, hp, hpa⟩ := Subgroup.mem_map.mp ha
        have hpx : (p : G) * x * (p : G)⁻¹ = x := by
          rw [Subgroup.mem_centralizer_iff.mp hxC (p : G) (Subgroup.mem_subgroupOf.mp hp)]
          group
        have hconjV : (p : G) * x * (p : G)⁻¹ ∈ V :=
          (Subgroup.mem_normalizer_iff.mp (hLV (hP.1 (Subgroup.mem_subgroupOf.mp hp))) x).mp hxV
        have hsm : φ' p • S.π ⟨x, hxV⟩ = S.π ⟨(p : G) * x * (p : G)⁻¹, hconjV⟩ :=
          S.smul_eq p ⟨x, hxV⟩ ⟨_, hconjV⟩ rfl
        rw [← hpa]
        rw [hsm]
        congr 1
        exact Subtype.ext hpx
      by_cases hw0 : S.π ⟨x, hxV⟩ = 0
      · have hxbot : x ∈ (⊥ : Subgroup G) := (S.eq_zero_iff ⟨x, hxV⟩).mp hw0
        rw [Subgroup.mem_bot] at hxbot
        rw [hxbot]
        exact R.one_mem
      · obtain ⟨Vw', θw', hinjw', hVwinv', hEq', hVwcard', hCwcard, hwCw, hCwWA⟩ :=
          hVw_of_fixed _ hw0 hxC'
        have hwπR : S.π ⟨x, hxV⟩ ∈ πR := hWA_eq ▸ hCwWA hwCw
        obtain ⟨r, hr⟩ := hwπR
        have hxr : x = (r : G) :=
          (congrArg Subtype.val (sectionModule_pi_injective S hr)).symm
        rw [hxr]
        exact r.2
    · rintro x hx
      refine ⟨hRleV hx, ?_⟩
      refine Subgroup.mem_centralizer_iff.mpr ?_
      intro p hp
      have hxp : ⁅x, p⁆ ∈ R := Subgroup.commutator_mem_commutator (hRleV hx) hp
      have hxZ : x ∈ X.Z (d₁ : ℤ) := hRV hx
      have hxc : x ∈ centerOf (X.L (d₁ : ℤ)) := by rwa [← hZc]
      exact Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hxc).2 p (hPleL hp)
  obtain ⟨r₀, hr₀R⟩ : ∃ r : ↥R, (r : G) ≠ 1 := by
    by_contra hcon
    push Not at hcon
    apply hRne
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    exact hcon ⟨x, hx⟩
  have hr₀V : (r₀ : G) ∈ V := hRleV r₀.2
  have hw₀ne : S.π ⟨(r₀ : G), hr₀V⟩ ≠ 0 := by
    intro h0
    apply hr₀R
    have h := (S.eq_zero_iff ⟨(r₀ : G), hr₀V⟩).mp h0
    rwa [Subgroup.mem_bot] at h
  have hw₀fix : ∀ a ∈ CFSG.Timmesfeld.upperUnipotent K,
      a • S.π ⟨(r₀ : G), hr₀V⟩ = S.π ⟨(r₀ : G), hr₀V⟩ := by
    intro a ha
    rw [← hU'eq] at ha
    obtain ⟨p, hp, hpa⟩ := Subgroup.mem_map.mp ha
    have hpP : (p : G) ∈ P := Subgroup.mem_subgroupOf.mp hp
    have hrZ : (r₀ : G) ∈ centerOf (X.L (d₁ : ℤ)) := by
      rw [← hZc]
      exact hRV r₀.2
    have hconjR : (p : G) * (r₀ : G) * (p : G)⁻¹ = (r₀ : G) := by
      rw [Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hrZ).2 (p : G) (hPleL hpP)]
      group
    have hconjV : (p : G) * (r₀ : G) * (p : G)⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (hLV (hP.1 hpP)) (r₀ : G)).mp hr₀V
    have hsm : φ' p • S.π ⟨(r₀ : G), hr₀V⟩ =
        S.π ⟨(p : G) * (r₀ : G) * (p : G)⁻¹, hconjV⟩ :=
      S.smul_eq p ⟨(r₀ : G), hr₀V⟩ ⟨_, hconjV⟩ rfl
    rw [← hpa]
    rw [hsm]
    congr 1
    exact Subtype.ext hconjR
  obtain ⟨Vw, θw, hinjw, hVwinv, hVw_eq, hVwcard, hC₀card, hw₀C, hC₀WA⟩ :=
    hVw_of_fixed _ hw₀ne hw₀fix
  let C₀ : AddSubgroup S.W := (θw.comp (vecE1 (K := K))).range
  have hcardπR : Nat.card ↥πR = Nat.card ↥R := by
    have hinjR : Function.Injective (fun r : ↥R => S.π ⟨(r : G), hRleV r.2⟩) :=
      fun a b hab =>
        Subtype.ext (congrArg (fun x : ↥V => (x : G)) (sectionModule_pi_injective S hab))
    have e : ↥R ≃ ↥πR :=
      Equiv.ofBijective
        (fun r => (⟨S.π ⟨(r : G), hRleV r.2⟩, ⟨r, rfl⟩⟩ : ↥πR))
        ⟨fun a b h => hinjR (Subtype.ext_iff.mp h), fun y => by
          obtain ⟨r, hr⟩ := y.2
          exact ⟨r, Subtype.ext hr⟩⟩
    exact (Nat.card_congr e).symm
  have hC₀πR : C₀ ≤ πR := by
    rw [← hWA_eq]
    exact hC₀WA
  have hπR_eq_C₀ : πR = C₀ := by
    symm
    apply AddSubgroup.eq_of_le_of_card_ge hC₀πR
    rw [hcardπR]
    calc Nat.card ↥R ≤ 2 ^ X.n 0 := hcardRle
      _ = Nat.card ↥C₀ := hC₀card.symm
  have hC₀Vw : C₀ ≤ Vw := by
    intro y hy
    obtain ⟨u, rfl⟩ := AddMonoidHom.mem_range.mp hy
    rw [← hVw_eq]
    exact AddMonoidHom.mem_range.mpr ⟨vecE1 u, rfl⟩
  let Hsub : Subgroup G :=
    { carrier := {x | ∃ hx : x ∈ V, S.π ⟨x, hx⟩ ∈ Vw}
      one_mem' := ⟨V.one_mem, by
        rw [show (⟨(1 : G), V.one_mem⟩ : ↥V) = 1 from Subtype.ext rfl, S.map_one]
        exact Vw.zero_mem⟩
      mul_mem' := by
        rintro x y ⟨hxV, hxw⟩ ⟨hyV, hyw⟩
        refine ⟨V.mul_mem hxV hyV, ?_⟩
        rw [show (⟨x * y, V.mul_mem hxV hyV⟩ : ↥V) =
          ⟨x, hxV⟩ * ⟨y, hyV⟩ from rfl, S.map_mul]
        exact Vw.add_mem hxw hyw
      inv_mem' := by
        rintro x ⟨hxV, hxw⟩
        refine ⟨V.inv_mem hxV, ?_⟩
        rw [show (⟨x⁻¹, V.inv_mem hxV⟩ : ↥V) = (⟨x, hxV⟩ : ↥V)⁻¹ from rfl, S.map_inv]
        exact Vw.neg_mem hxw }
  have hR_le_H : R ≤ Hsub := by
    intro r hr
    refine ⟨hRleV hr, ?_⟩
    have hmem : S.π ⟨(r : G), hRleV hr⟩ ∈ πR := ⟨⟨r, hr⟩, rfl⟩
    rw [hπR_eq_C₀] at hmem
    exact hC₀Vw hmem
  have hH_conj : ∀ l ∈ L, ∀ x ∈ Hsub, (l : G) * x * (l : G)⁻¹ ∈ Hsub := by
    intro l hl x hx
    obtain ⟨hxV, hxw⟩ := hx
    have hconjV : (l : G) * x * (l : G)⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (hLV hl) x).mp hxV
    refine ⟨hconjV, ?_⟩
    have hsm : φ' ⟨l, hl⟩ • S.π ⟨x, hxV⟩ = S.π ⟨(l : G) * x * (l : G)⁻¹, hconjV⟩ :=
      S.smul_eq ⟨l, hl⟩ ⟨x, hxV⟩ ⟨_, hconjV⟩ rfl
    rw [← hsm]
    exact hVwinv (φ' ⟨l, hl⟩) _ hxw
  have hV_le_H : V ≤ Hsub := by
    have hgenR : V ≤ ⨆ l : ↥L, R.map (MulAut.conj (l : G)).toMonoidHom := by
      have h := hCgen
      rwa [hCSe] at h
    refine hgenR.trans (iSup_le fun l => ?_)
    intro x hx
    rw [Subgroup.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    have hl : (l : G) ∈ L := l.2
    have hyH : y ∈ Hsub := hR_le_H hy
    have := hH_conj (l : G) hl y hyH
    simpa [MulAut.conj_apply] using this
  have hHV : Hsub = V := le_antisymm (fun x hx => hx.1) hV_le_H
  have hVw_top : Vw = ⊤ := by
    rw [eq_top_iff]
    intro y _
    obtain ⟨x, rfl⟩ := S.surjective y
    have hxH : ((x : G)) ∈ Hsub := by rw [hHV]; exact x.2
    exact hxH.2
  have hcardVW : Nat.card ↥V = Nat.card S.W := by
    have hinjV : Function.Injective (fun x : ↥V => S.π x) := sectionModule_pi_injective S
    have e : ↥V ≃ S.W := Equiv.ofBijective (fun x : ↥V => S.π x) ⟨hinjV, S.surjective⟩
    exact Nat.card_congr e
  have hcardV : Nat.card ↥V = 2 ^ (2 * X.n 0) := by
    calc Nat.card ↥V = Nat.card S.W := hcardVW
      _ = Nat.card ↥Vw := by rw [hVw_top]; simp
      _ = 2 ^ (2 * X.n 0) := hVwcard
  simpa [V] using hcardV

theorem s45_false_of_b₀_odd (H : X.Sec4Hyp s r) {d₀ d₁ : ℕ} (hd₀ : X.HasB 0 d₀)
    (hd₁ : X.HasB 1 d₁)
    (hna : ¬ ⁅X.Z 1, X.Z ((d₁ : ℤ) + 1)⁆ ≤ X.Z 1 ⊓ X.Z ((d₁ : ℤ) + 1))
    (hodd₀ : Odd d₀) :
    False := by
  obtain ⟨-, hd0, -, -, hdh, -⟩ := X.s45_facts H hd₀ hd₁ hna hodd₀
  have hEq : X.Z ((d₁ : ℤ) + 1) = X.Z (d₁ : ℤ) ⊔ X.Z ((d₁ : ℤ) + 2) := by
    haveI : Finite ↥(X.Z ((d₁ : ℤ) + 1)) :=
      finite_of_le_stabilizer X.hyp (H := X.Z ((d₁ : ℤ) + 1)) (X.Z_le_Gi _)
    refine (Subgroup.eq_of_le_of_card_ge (X.W_le_Z_h H hd₀ hd₁ hna hodd₀) ?_).symm
    exact ((X.card_Z_h H hd₀ hd₁ hna hodd₀).trans
      (X.s45_card_W H hd₀ hd₁ hna hodd₀).symm).le
  have hpred2 : X.Z (d₁ : ℤ) ≤ X.Gi 2 := by
    have hodd1 : Odd (d₁ : ℤ) :=
      (Int.odd_coe_nat d₁).mpr (X.s45_lt_odd_of_not_comm_le H hd₀ hd₁ hna).2.1
    have hB1 : X.HasB (d₁ : ℤ) d₁ := X.hasB_of_odd hd₁ hodd1
    have hmem : (2 : ℤ) ∈ X.fixSet (X.Z (d₁ : ℤ)) := by
      rw [X.fixSet_Z (d₁ : ℤ) hB1]
      exact Set.mem_Icc.mpr ⟨by omega, by omega⟩
    exact (X.mem_fixSet_iff_le_Gi (X.Z (d₁ : ℤ)) 2).mpr hmem
  have hsucc2 : X.Z ((d₁ : ℤ) + 2) ≤ X.Gi 2 := by
    obtain ⟨hlt, hodd1, -, -⟩ := X.s45_lt_odd_of_not_comm_le H hd₀ hd₁ hna
    have hodd2 : Odd ((d₁ : ℤ) + 2) := by
      obtain ⟨k, hk⟩ := hodd1
      exact ⟨k + 1, by omega⟩
    have hB2 : X.HasB ((d₁ : ℤ) + 2) d₁ := X.hasB_of_odd hd₁ hodd2
    have hmem : (2 : ℤ) ∈ X.fixSet (X.Z ((d₁ : ℤ) + 2)) := by
      rw [X.fixSet_Z ((d₁ : ℤ) + 2) hB2]
      exact Set.mem_Icc.mpr ⟨by omega, by omega⟩
    exact (X.mem_fixSet_iff_le_Gi (X.Z ((d₁ : ℤ) + 2)) 2).mpr hmem
  have hW2 : X.Z (d₁ : ℤ) ⊔ X.Z ((d₁ : ℤ) + 2) ≤ X.Gi 2 :=
    sup_le hpred2 hsucc2
  have hZ2 : X.Z ((d₁ : ℤ) + 1) ≤ X.Gi 2 := hEq ▸ hW2
  have hnot : ¬ X.Z ((d₁ : ℤ) + 1) ≤ X.Gi 2 := by
    intro hle
    have hmem : (2 : ℤ) ∈ X.fixSet (X.Z ((d₁ : ℤ) + 1)) :=
      (X.mem_fixSet_iff_le_Gi (X.Z ((d₁ : ℤ) + 1)) 2).mpr hle
    rw [X.fixSet_Z ((d₁ : ℤ) + 1) hdh] at hmem
    simp only [Set.mem_Icc] at hmem
    omega
  exact hnot hZ2

end Setup

end CFSG.Quasithin.St84
