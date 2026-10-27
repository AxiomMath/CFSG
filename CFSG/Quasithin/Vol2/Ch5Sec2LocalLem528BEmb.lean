module

public import CFSG.Quasithin.Vol2.Ch1Eight
public import CFSG.Quasithin.EmptyFaithful.Setting
public import CFSG.Quasithin.Background.C2Nine
public import CFSG.Quasithin.Background.G2
public import CFSG.Quasithin.Vol2.Ch5ModulesNat

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

structure Emb528 (T K Kh : Subgroup G) : Prop where
  qtke : quasithinIsQTKECat G
  simple : IsSimpleGroup G
  nonab : ∃ a b : G, a * b ≠ b * a
  sylow : quasithinIsSylowTwo T
  locK : quasithinIsLocal T K
  locKh : quasithinIsLocal T Kh
  le : K ≤ Kh
  normK : T ≤ Subgroup.normalizer (K : Set G)

omit [Finite G] in
theorem commutator_commutator_eq_of_oTwoUpper {X P : Subgroup G} (hX : oTwoUpper X = X)
    (hXP : X ≤ Subgroup.normalizer (P : Set G)) (hPX : P ≤ Subgroup.normalizer (X : Set G))
    (hP : IsPGroup 2 P) : ⁅⁅P, X⁆, X⁆ = ⁅P, X⁆ := by
  have hXB : X ≤ Subgroup.normalizer ((⁅P, X⁆ : Subgroup G) : Set G) :=
    le_normalizer_commutator_of hXP Subgroup.le_normalizer
  have hPB : P ≤ Subgroup.normalizer ((⁅P, X⁆ : Subgroup G) : Set G) :=
    le_normalizer_commutator_of Subgroup.le_normalizer hPX
  refine le_antisymm (Subgroup.le_normalizer_iff_commutator_le_left.mp hXB) ?_
  have key := CFSG.Quasithin.A4.commutator_le_of_oTwoUpper (A := X) (N := ⁅⁅P, X⁆, X⁆)
    (B := ⁅P, X⁆) (D := P) (le_normalizer_commutator_of hXB Subgroup.le_normalizer)
    (le_normalizer_commutator_of hPB hPX) (Subgroup.le_normalizer_iff_commutator_le_left.mp hXP)
    (fun d hd => by
      obtain ⟨j, hj⟩ := hP ⟨d, hd⟩
      exact ⟨j, by rw [show d ^ 2 ^ j = 1 from congrArg Subtype.val hj]; exact one_mem _⟩)
    (by rw [Subgroup.commutator_comm])
    (by rw [Subgroup.commutator_comm])
  rw [hX] at key
  exact (Subgroup.commutator_comm P X).trans_le key

namespace Emb528

variable {T K Kh : Subgroup G}

theorem le_normalizer (e : Emb528 T K Kh) (h37 : A37ForSQTK) :
    T ≤ Subgroup.normalizer (Kh : Set G) := fun _ ht =>
  (lemma_1_2_8_one_le e.qtke e.simple e.nonab h37 e.locK e.locKh e.le ⟨ht, e.normK ht⟩).2

theorem sup_le_normalizer (e : Emb528 T K Kh) (h37 : A37ForSQTK) :
    Kh ⊔ T ≤ Subgroup.normalizer (Kh : Set G) :=
  sup_le Subgroup.le_normalizer (e.le_normalizer h37)

theorem isSylowTwoOf (e : Emb528 T K Kh) : IsSylowTwoOf T (Kh ⊔ T) :=
  ⟨le_sup_right, e.locKh.1, e.locKh.2.2.1⟩

theorem pCoreOf_le_T (e : Emb528 T K Kh) : pCoreOf 2 (Kh ⊔ T) ≤ T :=
  CFSG.Quasithin.pCoreOf_two_le_of_isSylowTwoOf e.isSylowTwoOf

theorem pCoreOf_le_sup (e : Emb528 T K Kh) (h37 : A37ForSQTK) :
    pCoreOf 2 Kh ≤ pCoreOf 2 (Kh ⊔ T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 Kh).trans le_sup_left)
    ((e.sup_le_normalizer h37).trans (normalizer_le_normalizer_pCoreOf 2 Kh))
    (pCoreOf_isPGroup 2 Kh)

theorem inf_pCoreOf_eq (e : Emb528 T K Kh) (h37 : A37ForSQTK) :
    Kh ⊓ pCoreOf 2 (Kh ⊔ T) = pCoreOf 2 Kh := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_antisymm ?_ (le_inf (pCoreOf_le 2 Kh) (e.pCoreOf_le_sup h37))
  refine le_pCoreOf_of_le_normalizer 2 inf_le_left ?_
    ((pCoreOf_isPGroup 2 (Kh ⊔ T)).to_le inf_le_right)
  intro k hk
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have h1 := Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hk) x
  have h2 := Subgroup.mem_normalizer_iff.mp
    (le_normalizer_pCoreOf 2 (Kh ⊔ T) ((le_sup_left : Kh ≤ Kh ⊔ T) hk)) x
  simp only [Subgroup.mem_inf]
  exact ⟨fun h => ⟨h1.mp h.1, h2.mp h.2⟩, fun h => ⟨h1.mpr h.1, h2.mpr h.2⟩⟩

theorem pCoreOf_le_pCoreOf_KT (e : Emb528 T K Kh) (h37 : A37ForSQTK) :
    pCoreOf 2 Kh ≤ pCoreOf 2 (K ⊔ T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_pCoreOf_of_le_normalizer 2
    (((e.pCoreOf_le_sup h37).trans e.pCoreOf_le_T).trans le_sup_right) ?_
    (pCoreOf_isPGroup 2 Kh)
  exact sup_le (e.le.trans (le_normalizer_pCoreOf 2 Kh))
    ((e.le_normalizer h37).trans (normalizer_le_normalizer_pCoreOf 2 Kh))

theorem K_le_normalizer (e : Emb528 T K Kh) :
    K ≤ Subgroup.normalizer (pCoreOf 2 (Kh ⊔ T) : Set G) :=
  (e.le.trans le_sup_left).trans (le_normalizer_pCoreOf 2 (Kh ⊔ T))

theorem commutator_le_inf (e : Emb528 T K Kh) :
    ⁅pCoreOf 2 (Kh ⊔ T), K⁆ ≤ K ⊓ pCoreOf 2 (Kh ⊔ T) := by
  rw [Subgroup.commutator_le]
  intro x hx k hk
  have hxN : x ∈ Subgroup.normalizer (K : Set G) := e.normK (e.pCoreOf_le_T hx)
  have hkN : k ∈ Subgroup.normalizer (pCoreOf 2 (Kh ⊔ T) : Set G) := e.K_le_normalizer hk
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · rw [commutatorElement_def]
    exact mul_mem ((Subgroup.mem_normalizer_iff.mp hxN k).mp hk) (inv_mem hk)
  · rw [commutatorElement_def, show x * k * x⁻¹ * k⁻¹ = x * (k * x⁻¹ * k⁻¹) by group]
    exact mul_mem hx ((Subgroup.mem_normalizer_iff.mp hkN x⁻¹).mp (inv_mem hx))

theorem charTwo (e : Emb528 T K Kh) : CharTwo (Kh ⊔ T) := by
  obtain ⟨S', hS'⟩ := CFSG.Quasithin.exists_sylow_of_quasithinIsSylowTwo e.sylow
  exact CFSG.Quasithin.charTwo_of_inH e.qtke.2.1 S'
    ⟨by rw [hS']; exact le_sup_right, e.locKh.2.2.2⟩

theorem commutator_ne_bot (e : Emb528 T K Kh) : ⁅pCoreOf 2 (Kh ⊔ T), K⁆ ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hbot
  have hKO : K ≤ pCoreOf 2 (Kh ⊔ T) := by
    intro k hk
    refine e.charTwo (Subgroup.mem_inf.mpr ⟨(le_sup_left : Kh ≤ Kh ⊔ T) (e.le hk), ?_⟩)
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hc : ⁅x, k⁆ ∈ ⁅pCoreOf 2 (Kh ⊔ T), K⁆ := Subgroup.commutator_mem_commutator hx hk
    rw [hbot, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
    exact hc
  have hp : IsPGroup 2 K := (pCoreOf_isPGroup 2 (Kh ⊔ T)).to_le hKO
  have hperf : Group.IsPerfect ↥K := Subgroup.isPerfect_iff.mpr e.locK.2.1.2.1
  have hnt : Nontrivial ↥K := by
    rw [Subgroup.nontrivial_iff_ne_bot]
    exact e.locK.2.1.1
  have := Fintype.ofFinite G
  have : Group.IsNilpotent ↥K := hp.isNilpotent
  exact Group.IsPerfect.not_isNilpotent ↥K inferInstance

theorem oTwoUpper_eq (e : Emb528 T K Kh) : oTwoUpper K = K :=
  CFSG.Quasithin.C2Nine.oTwoUpper_eq_of_perfect e.locK.2.1.2.1

theorem commutator_commutator (e : Emb528 T K Kh) :
    ⁅⁅pCoreOf 2 (Kh ⊔ T), K⁆, K⁆ = ⁅pCoreOf 2 (Kh ⊔ T), K⁆ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact commutator_commutator_eq_of_oTwoUpper e.oTwoUpper_eq e.K_le_normalizer
    (e.pCoreOf_le_T.trans e.normK) (pCoreOf_isPGroup 2 (Kh ⊔ T))

theorem inf_le_blockQ (e : Emb528 T K Kh) : K ⊓ pCoreOf 2 (Kh ⊔ T) ≤ blockQ K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_pCoreOf_of_le_normalizer 2 inf_le_left ?_
    ((pCoreOf_isPGroup 2 (Kh ⊔ T)).to_le inf_le_right)
  intro k hk
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have h1 := Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hk) x
  have h2 := Subgroup.mem_normalizer_iff.mp (e.K_le_normalizer hk) x
  simp only [Subgroup.mem_inf]
  exact ⟨fun h => ⟨h1.mp h.1, h2.mp h.2⟩, fun h => ⟨h1.mpr h.1, h2.mpr h.2⟩⟩

theorem blockU_eq_commutator (e : Emb528 T K Kh) : ⁅blockU K, K⁆ = blockU K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact commutator_commutator_eq_of_oTwoUpper e.oTwoUpper_eq (le_normalizer_pCoreOf 2 K)
    ((pCoreOf_le 2 K).trans Subgroup.le_normalizer) (pCoreOf_isPGroup 2 K)

theorem blockU_le (e : Emb528 T K Kh) (h37 : A37ForSQTK) (hshort : IsShort2 K) :
    blockU K ≤ pCoreOf 2 Kh := by
  set P := pCoreOf 2 (Kh ⊔ T) with hP
  set W := ⁅P, K⁆ with hW
  have hWQ : W ≤ blockQ K := e.commutator_le_inf.trans e.inf_le_blockQ
  have hWW : ⁅W, K⁆ = W := e.commutator_commutator
  have hWU : W ≤ blockU K := hWW ▸ Subgroup.commutator_mono_left hWQ
  have hKW : K ≤ Subgroup.normalizer (W : Set G) :=
    le_normalizer_commutator_of e.K_le_normalizer Subgroup.le_normalizer
  have hKZ : K ≤ Subgroup.normalizer (blockZ K : Set G) := by
    intro k hk
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have h1 := Subgroup.mem_normalizer_iff.mp
      (le_normalizer_commutator_of (le_normalizer_pCoreOf 2 K) Subgroup.le_normalizer hk) x
    have h2 : x ∈ Subgroup.centralizer (K : Set G) ↔
        k * x * k⁻¹ ∈ Subgroup.centralizer (K : Set G) := by
      simp only [Subgroup.mem_centralizer_iff]
      constructor
      · intro hc y hy
        have h3 := hc (k⁻¹ * y * k) (mul_mem (mul_mem (inv_mem hk) hy) hk)
        calc y * (k * x * k⁻¹) = k * ((k⁻¹ * y * k) * x) * k⁻¹ := by group
          _ = k * (x * (k⁻¹ * y * k)) * k⁻¹ := by rw [h3]
          _ = k * x * k⁻¹ * y := by group
      · intro hc y hy
        have h3 := hc (k * y * k⁻¹) (mul_mem (mul_mem hk hy) (inv_mem hk))
        calc y * x = k⁻¹ * ((k * y * k⁻¹) * (k * x * k⁻¹)) * k := by group
          _ = k⁻¹ * ((k * x * k⁻¹) * (k * y * k⁻¹)) * k := by rw [h3]
          _ = x * y := by group
    simp only [blockZ, Subgroup.mem_inf]
    exact ⟨fun h => ⟨h1.mp h.1, h2.mp h.2⟩, fun h => ⟨h1.mpr h.1, h2.mpr h.2⟩⟩
  have hUab : ∀ a ∈ blockU K, ∀ b ∈ blockU K, a * b = b * a := by
    intro a ha b hb
    have hb' : b ∈ Subgroup.centralizer (blockQ K : Set G) :=
      (Subgroup.mem_inf.mp (hshort.2.2.1.1 hb)).2
    exact Subgroup.mem_centralizer_iff.mp hb' a (Subgroup.mem_inf.mp (hshort.2.2.1.1 ha)).1
  have hWZn : W ≤ Subgroup.normalizer (blockZ K : Set G) := by
    intro w hw
    rw [Subgroup.mem_normalizer_iff]
    intro z
    have hc : ∀ y ∈ blockU K, w * y * w⁻¹ = y := fun y hy => by
      rw [hUab w (hWU hw) y hy, mul_inv_cancel_right]
    constructor
    · intro hz
      rw [hc z hz.1]
      exact hz
    · intro hz
      have hy : z = w⁻¹ * (w * z * w⁻¹) * w := by group
      rw [hy, show w⁻¹ * (w * z * w⁻¹) * w = w⁻¹ * (w * z * w⁻¹) * w⁻¹⁻¹ by group]
      have hwU : w⁻¹ ∈ blockU K := inv_mem (hWU hw)
      rw [hUab w⁻¹ hwU _ hz.1, mul_inv_cancel_right]
      exact hz
  have hsupN : K ≤ Subgroup.normalizer ((W ⊔ blockZ K : Subgroup G) : Set G) := by
    intro k hk
    rw [← CFSG.Quasithin.A38.map_conj_eq_iff, Subgroup.map_sup,
      CFSG.Quasithin.A38.map_conj_eq_iff.mpr (hKW hk),
      CFSG.Quasithin.A38.map_conj_eq_iff.mpr (hKZ hk)]
  rcases hshort.2.2.2.2.2 (W ⊔ blockZ K) le_sup_right (sup_le hWU inf_le_left) hsupN with
    h | h
  ·
    exfalso
    apply e.commutator_ne_bot
    rw [← hW, ← hWW, eq_bot_iff, Subgroup.commutator_le]
    intro w hw k _
    have hwZ : w ∈ blockZ K := h ▸ (le_sup_left : W ≤ W ⊔ blockZ K) hw
    have hwc := (Subgroup.mem_centralizer_iff.mp hwZ.2) k ‹k ∈ K›
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact hwc.symm
  ·
    have hUW : blockU K ≤ W := by
      rw [← e.blockU_eq_commutator, Subgroup.commutator_le]
      intro u hu k hk
      have hu' : u ∈ ((W : Set G) * (blockZ K : Set G)) := by
        rw [← Subgroup.coe_mul_of_left_le_normalizer_right W (blockZ K) hWZn, h]
        exact hu
      obtain ⟨w, hw, z, hz, rfl⟩ := hu'
      have hzk : z * k = k * z := ((Subgroup.mem_centralizer_iff.mp hz.2) k hk).symm
      have : ⁅w * z, k⁆ = ⁅w, k⁆ := by
        rw [commutatorElement_def, commutatorElement_def]
        calc w * z * k * (w * z)⁻¹ * k⁻¹ = w * (z * k) * z⁻¹ * w⁻¹ * k⁻¹ := by group
          _ = w * (k * z) * z⁻¹ * w⁻¹ * k⁻¹ := by rw [hzk]
          _ = w * k * w⁻¹ * k⁻¹ := by group
      rw [this, ← hWW]
      exact Subgroup.commutator_mem_commutator hw hk
    rw [← e.inf_pCoreOf_eq h37]
    have hUK : blockU K ≤ K :=
      (Subgroup.commutator_mono (pCoreOf_le 2 K) le_rfl).trans e.locK.2.1.2.1.le
    exact le_inf (hUK.trans e.le)
      (hUW.trans (Subgroup.le_normalizer_iff_commutator_le_left.mp e.K_le_normalizer))

end Emb528

end CFSG.Quasithin.H13
