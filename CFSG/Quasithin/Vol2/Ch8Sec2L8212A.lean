module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.E3Defs

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.E3
open scoped IsMulCommutative commutatorElement

section L8212A

variable {G : Type} [Group G]

theorem centralizer_eq_normalizer_zpowers_82 {z : G} (hz : orderOf z = 2) :
    Subgroup.centralizer ({z} : Set G) =
      Subgroup.normalizer ((Subgroup.zpowers z : Subgroup G) : Set G) := by
  have hz2 : z ^ 2 = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
  have hmem : ∀ x : G, x ∈ Subgroup.zpowers z ↔ x = 1 ∨ x = z := by
    intro x
    constructor
    · intro hx
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      have hk : z ^ k = z ^ (k % 2) := by
        have := zpow_mod_orderOf z k
        rw [hz] at this
        exact_mod_cast this.symm
      rcases Int.emod_two_eq_zero_or_one k with h | h
      · left
        rw [hk, h, zpow_zero]
      · right
        rw [hk, h, zpow_one]
    · rintro (h | h) <;> rw [h]
      · exact Subgroup.one_mem _
      · exact Subgroup.mem_zpowers z
  have hz1 : z ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hz
    norm_num at hz
  ext g
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro hg x
    rw [hmem, hmem]
    constructor
    · rintro (h | h) <;> rw [h]
      · left
        group
      · right
        rw [hg, mul_inv_cancel_right]
    · rintro (h | h)
      · left
        have := congrArg (fun y => g⁻¹ * y * g) h
        simpa [mul_assoc] using this
      · right
        have h1 : g * x * g⁻¹ = g * z * g⁻¹ := by rw [h, hg, mul_inv_cancel_right]
        have := congrArg (fun y => g⁻¹ * y * g) h1
        simpa [mul_assoc] using this
  · intro hg
    have h1 := ((hg z).mp (Subgroup.mem_zpowers z))
    rw [hmem] at h1
    rcases h1 with h | h
    · exfalso
      apply hz1
      have := congrArg (fun y => g⁻¹ * y * g) h
      simpa [mul_assoc] using this
    · calc g * z = g * z * g⁻¹ * g := by group
        _ = z * g := by rw [h]

theorem charTwo_centralizer_82 {T : Subgroup G}
    (hEven : CFSG.Assembly.Quasithin.quasithinEvenCharacteristic G)
    (hT : quasithinIsSylowTwo T) {z : G} (hz : orderOf z = 2)
    (hzT : z ∈ Subgroup.centralizer (T : Set G)) :
    Subgroup.centralizer ({z} : Set G) ⊓
        Subgroup.centralizer (pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) : Set G) ≤
      pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine hEven _ ⟨Subgroup.zpowers z, ?_, ?_, centralizer_eq_normalizer_zpowers_82 hz⟩ ?_
  · intro h
    have h1 : z ∈ (⊥ : Subgroup G) := h ▸ Subgroup.mem_zpowers z
    rw [Subgroup.mem_bot] at h1
    rw [h1, orderOf_one] at hz
    norm_num at hz
  · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz, pow_one])
  · refine ⟨hT.1.toSylow hT.2, ?_⟩
    intro t ht
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp hzT t ht

theorem mem_pCoreOf_of_commutator_82 {C : Subgroup G} {z : G} (hz2 : z ^ 2 = 1)
    (hzC : ∀ c ∈ C, c * z = z * c)
    (hchar : C ⊓ Subgroup.centralizer (pCoreOf 2 C : Set G) ≤ pCoreOf 2 C) {c : G}
    (hc : c ∈ C) (hcq : ∀ q ∈ pCoreOf 2 C, ⁅c, q⁆ ∈ Subgroup.zpowers z) [Finite G] :
    c ∈ pCoreOf 2 C := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := pCoreOf 2 C with hQ
  have hQC : Q ≤ C := CFSG.LieType.BorelTits.pCoreOf_le 2 C
  have hCQ : C ≤ Subgroup.normalizer (Q : Set G) := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 C
  have hQp : IsPGroup 2 ↥Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 C
  have hZc : ∀ ζ ∈ Subgroup.zpowers z, ∀ g ∈ C, g * ζ = ζ * g := by
    intro ζ hζ g hg
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hζ
    exact ((Commute.zpow_right (hzC g hg) k))
  let D : Subgroup G :=
    { carrier := {g | g ∈ C ∧ ∀ q ∈ Q, ⁅g, q⁆ ∈ Subgroup.zpowers z}
      one_mem' := ⟨C.one_mem, fun q _ => by
        rw [commutatorElement_one_left]
        exact Subgroup.one_mem _⟩
      mul_mem' := by
        rintro a b ⟨haC, ha⟩ ⟨hbC, hb⟩
        refine ⟨C.mul_mem haC hbC, fun q hq => ?_⟩
        have e : ⁅a * b, q⁆ = a * ⁅b, q⁆ * a⁻¹ * ⁅a, q⁆ := by
          simp only [commutatorElement_def]
          group
        rw [e]
        have h1 : a * ⁅b, q⁆ * a⁻¹ = ⁅b, q⁆ := by
          rw [hZc _ (hb q hq) a haC, mul_inv_cancel_right]
        rw [h1]
        exact Subgroup.mul_mem _ (hb q hq) (ha q hq)
      inv_mem' := by
        rintro a ⟨haC, ha⟩
        refine ⟨C.inv_mem haC, fun q hq => ?_⟩
        have e : ⁅a⁻¹, q⁆ = a⁻¹ * ⁅a, q⁆⁻¹ * a := by
          simp only [commutatorElement_def]
          group
        rw [e]
        have h1 : a⁻¹ * ⁅a, q⁆⁻¹ * a = ⁅a, q⁆⁻¹ := by
          rw [mul_assoc, ← hZc _ (Subgroup.inv_mem _ (ha q hq)) a haC, ← mul_assoc,
            inv_mul_cancel, one_mul]
        rw [h1]
        exact Subgroup.inv_mem _ (ha q hq) }
  have hD : ∀ g, g ∈ D ↔ g ∈ C ∧ ∀ q ∈ Q, ⁅g, q⁆ ∈ Subgroup.zpowers z := fun g => Iff.rfl
  have hodd : ∀ g ∈ D, ∀ m : ℕ, Odd m → g ^ m = 1 → g = 1 := by
    intro g hg m hm hgm
    obtain ⟨hgC, hgq⟩ := (hD g).mp hg
    have hcent : ∀ q ∈ Q, g * q * g⁻¹ = q := by
      intro q hq
      set ζ := ⁅g, q⁆ with hζ
      have hζZ : ζ ∈ Subgroup.zpowers z := hgq q hq
      have hgq' : g * q * g⁻¹ = ζ * q := by
        rw [hζ, commutatorElement_def]
        group
      have hpow : ∀ n : ℕ, g ^ n * q * (g ^ n)⁻¹ = ζ ^ n * q := by
        intro n
        induction n with
        | zero => simp
        | succ n ih =>
          have e1 : g ^ (n + 1) * q * (g ^ (n + 1))⁻¹ = g * (g ^ n * q * (g ^ n)⁻¹) * g⁻¹ := by
            group
          rw [e1, ih]
          have hζn : g * ζ ^ n * g⁻¹ = ζ ^ n := by
            rw [hZc _ (Subgroup.pow_mem _ hζZ n) g hgC, mul_inv_cancel_right]
          calc g * (ζ ^ n * q) * g⁻¹ = (g * ζ ^ n * g⁻¹) * (g * q * g⁻¹) := by group
            _ = ζ ^ n * (ζ * q) := by rw [hζn, hgq']
            _ = ζ ^ (n + 1) * q := by rw [pow_succ]; group
      have h1 := hpow m
      rw [hgm, one_mul, inv_one, mul_one] at h1
      have hζm : ζ ^ m = 1 := by
        have := congrArg (· * q⁻¹) h1
        simpa using this.symm
      have hζ2 : ζ ^ 2 = 1 := by
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hζZ
        rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]
        norm_num [hz2]
      have hζ1 : ζ = 1 := by
        have h3 : ζ ^ Nat.gcd m 2 = 1 := pow_gcd_eq_one.mpr ⟨hζm, hζ2⟩
        rwa [Nat.Coprime.gcd_eq_one ((Nat.coprime_two_right).mpr hm), pow_one] at h3
      rw [hgq', hζ1, one_mul]
    have hgQ : g ∈ Q := by
      refine hchar ⟨hgC, Subgroup.mem_centralizer_iff.mpr fun q hq => ?_⟩
      calc q * g = g * q * g⁻¹ * g := by rw [hcent q hq]
        _ = g * q := by group
    obtain ⟨k, hk⟩ := hQp ⟨g, hgQ⟩
    have hk' : g ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have h3 : g ^ Nat.gcd m (2 ^ k) = 1 := pow_gcd_eq_one.mpr ⟨hgm, hk'⟩
    rwa [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_right k ((Nat.coprime_two_right).mpr hm)),
      pow_one] at h3
  have hDp : IsPGroup 2 ↥D := by
    intro g
    obtain ⟨a, m, hm, he⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos g).ne'
    refine ⟨a, ?_⟩
    have h1 : (g ^ 2 ^ a : ↥D) ^ m = 1 := by
      rw [← pow_mul, ← he, pow_orderOf_eq_one]
    have h2 := hodd ((g ^ 2 ^ a : ↥D) : G) (g ^ 2 ^ a).2 m hm
      (by simpa using congrArg Subtype.val h1)
    exact Subtype.ext (by simpa using h2)
  have hDN : C ≤ Subgroup.normalizer (D : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    have hconj : ∀ a ∈ C, ∀ x ∈ D, a * x * a⁻¹ ∈ D := by
      intro a ha x hx
      obtain ⟨hxC, hxq⟩ := (hD x).mp hx
      refine (hD _).mpr ⟨C.mul_mem (C.mul_mem ha hxC) (C.inv_mem ha), fun q hq => ?_⟩
      have hq' : a⁻¹ * q * a ∈ Q := by
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hCQ ha)) q).mp hq
        simpa using this
      have e : ⁅a * x * a⁻¹, q⁆ = a * ⁅x, a⁻¹ * q * a⁆ * a⁻¹ := by
        simp only [commutatorElement_def]
        group
      rw [e, hZc _ (hxq _ hq') a ha, mul_inv_cancel_right]
      exact hxq _ hq'
    intro x
    refine ⟨hconj g hg x, fun hx => ?_⟩
    have := hconj g⁻¹ (C.inv_mem hg) _ hx
    simpa [mul_assoc] using this
  have hDle : D ≤ Q :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (fun g hg => ((hD g).mp hg).1) hDN hDp
  exact hDle ((hD c).mpr ⟨hc, hcq⟩)

theorem commutator_mem_of_inf_centralizer_82 {T L V : Subgroup G}
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (hCLV : L ⊓ Subgroup.centralizer (V : Set G) = V) {x l : G}
    (hx : x ∈ T ⊓ Subgroup.centralizer (V : Set G)) (hl : l ∈ L) : ⁅x, l⁆ ∈ V := by
  rw [← hCLV]
  refine ⟨?_, Subgroup.mem_centralizer_iff.mpr fun v hv => ?_⟩
  · rw [commutatorElement_def]
    exact L.mul_mem ((Subgroup.mem_normalizer_iff.mp (hTL hx.1) l).mp hl) (L.inv_mem hl)
  · have hv' : l⁻¹ * v * l ∈ V := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hLV hl)) v).mp hv
      simpa using this
    have hvx : v * x = x * v := (Subgroup.mem_centralizer_iff.mp hx.2 v hv)
    have hxw : x * (l⁻¹ * v * l) * x⁻¹ = l⁻¹ * v * l := by
      rw [← Subgroup.mem_centralizer_iff.mp hx.2 _ hv', mul_inv_cancel_right]
    rw [commutatorElement_def]
    calc v * (x * l * x⁻¹ * l⁻¹) = (v * x) * l * x⁻¹ * l⁻¹ := by group
      _ = (x * v) * l * x⁻¹ * l⁻¹ := by rw [hvx]
      _ = x * l * x⁻¹ * (x * (l⁻¹ * v * l) * x⁻¹) * l⁻¹ := by group
      _ = x * l * x⁻¹ * (l⁻¹ * v * l) * l⁻¹ := by rw [hxw]
      _ = x * l * x⁻¹ * l⁻¹ * v := by group

theorem commute_of_inf_centralizer_82 {T L V : Subgroup G}
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (hCLV : L ⊓ Subgroup.centralizer (V : Set G) = V)
    (hVC : V ≤ Subgroup.centralizer (V : Set G))
    (hTCL : T ⊓ Subgroup.centralizer (L : Set G) = ⊥) {x y : G}
    (hx : x ∈ T ⊓ Subgroup.centralizer (V : Set G))
    (hy : y ∈ T ⊓ Subgroup.centralizer (V : Set G)) : x * y = y * x := by
  have key : ∀ l ∈ L, ⁅x * y, l⁆ = ⁅y * x, l⁆ := by
    intro l hl
    have hxl := commutator_mem_of_inf_centralizer_82 hTL hLV hCLV hx hl
    have hyl := commutator_mem_of_inf_centralizer_82 hTL hLV hCLV hy hl
    have e1 : ⁅x * y, l⁆ = x * ⁅y, l⁆ * x⁻¹ * ⁅x, l⁆ := by
      simp only [commutatorElement_def]
      group
    have e2 : ⁅y * x, l⁆ = y * ⁅x, l⁆ * y⁻¹ * ⁅y, l⁆ := by
      simp only [commutatorElement_def]
      group
    have h1 : x * ⁅y, l⁆ * x⁻¹ = ⁅y, l⁆ := by
      rw [← Subgroup.mem_centralizer_iff.mp hx.2 _ hyl, mul_inv_cancel_right]
    have h2 : y * ⁅x, l⁆ * y⁻¹ = ⁅x, l⁆ := by
      rw [← Subgroup.mem_centralizer_iff.mp hy.2 _ hxl, mul_inv_cancel_right]
    rw [e1, e2, h1, h2]
    exact (Subgroup.mem_centralizer_iff.mp (hVC hyl) _ hxl).symm
  have hmem : (y * x)⁻¹ * (x * y) ∈ T ⊓ Subgroup.centralizer (L : Set G) := by
    refine ⟨T.mul_mem (T.inv_mem (T.mul_mem hy.1 hx.1)) (T.mul_mem hx.1 hy.1),
      Subgroup.mem_centralizer_iff.mpr fun l hl => ?_⟩
    have h := key l hl
    simp only [commutatorElement_def] at h
    have h' : x * y * l * (x * y)⁻¹ = y * x * l * (y * x)⁻¹ := by
      have := congrArg (· * l) h
      simpa [mul_assoc] using this
    calc l * ((y * x)⁻¹ * (x * y)) = (y * x)⁻¹ * (y * x * l * (y * x)⁻¹) * (x * y) := by group
      _ = (y * x)⁻¹ * (x * y * l * (x * y)⁻¹) * (x * y) := by rw [h']
      _ = (y * x)⁻¹ * (x * y) * l := by group
  rw [hTCL, Subgroup.mem_bot] at hmem
  exact (inv_mul_eq_one.mp hmem).symm

end L8212A

end CFSG.Quasithin.H13
