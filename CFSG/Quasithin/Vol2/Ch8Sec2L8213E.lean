module

public import CFSG.Quasithin.Vol2.Ch8Sec2L8210E
public import CFSG.Quasithin.Vol2.Ch8Sec2L8212C

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint
open scoped commutatorElement

section L8213E

theorem card_two_part_82 {C : Type} [Group C] [Finite C] (P : Subgroup C) [P.Normal]
    (hP : Nat.card ↥P = 2 ^ 13) (K : Subgroup (C ⧸ P)) (hK : Nat.card ↥K = 3 * 443520)
    (hX : Nat.card (C ⧸ P) ≤ 2 * Nat.card ↥K) (S : Subgroup C) (hS : IsPGroup 2 ↥S)
    (hSc : 2 ^ 21 ≤ Nat.card ↥S) :
    Nat.card ↥S = 2 ^ 21 ∧ Nat.card (C ⧸ P) = 2 * Nat.card ↥K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card (p := 2)).mp hS
  have hdvd : Nat.card ↥S ∣ Nat.card C := Subgroup.card_subgroup_dvd_card S
  have hC := Subgroup.card_eq_card_quotient_mul_card_subgroup P
  obtain ⟨j, hj⟩ := Subgroup.card_subgroup_dvd_card K
  have hpos : 0 < Nat.card (C ⧸ P) := Nat.card_pos
  have key : ∀ b c : ℕ, Nat.Coprime 2 c → 2 ^ a ∣ 2 ^ b * c → a ≤ b := by
    intro b c hc h
    have h1 : 2 ^ a ∣ 2 ^ b := (Nat.Coprime.pow_left a hc).dvd_of_dvd_mul_right h
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp h1
  have hj2 : j ≤ 2 := by
    rw [hj, hK] at hX
    omega
  have hj1 : 1 ≤ j := by
    rcases Nat.eq_zero_or_pos j with h0 | h0
    · rw [hj, h0, mul_zero] at hpos
      exact absurd hpos (lt_irrefl 0)
    · exact h0
  have h21 : 21 ≤ a := by
    rw [ha] at hSc
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp hSc
  rw [ha, hC, hP, hj, hK] at hdvd
  interval_cases j
  · exfalso
    have h1 : 2 ^ a ∣ 2 ^ 20 * 10395 := by
      have : 3 * 443520 * 1 * 2 ^ 13 = 2 ^ 20 * 10395 := by norm_num
      rwa [this] at hdvd
    have := key 20 10395 (by norm_num) h1
    omega
  · have h1 : 2 ^ a ∣ 2 ^ 21 * 10395 := by
      have : 3 * 443520 * 2 * 2 ^ 13 = 2 ^ 21 * 10395 := by norm_num
      rwa [this] at hdvd
    have := key 21 10395 (by norm_num) h1
    have ha21 : a = 21 := by omega
    refine ⟨by rw [ha, ha21], ?_⟩
    rw [hj, hK]

variable {G : Type} [Group G] [Finite G]

theorem centralizer_le_of_even_82 {T : Subgroup G}
    (hEven : CFSG.Assembly.Quasithin.quasithinEvenCharacteristic G)
    (hT : quasithinIsSylowTwo T) (hT1 : T ≠ ⊥) : Subgroup.centralizer (T : Set G) ≤ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := Subgroup.normalizer (T : Set G) with hN
  have h1 := hEven N ⟨T, hT1, hT.1, rfl⟩ ⟨hT.1.toSylow hT.2, Subgroup.le_normalizer⟩
  have hPT : pCoreOf 2 N ≤ T :=
    le_of_le_normalizer_82 hT (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 N)
      (Subgroup.le_normalizer.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 N))
  intro x hx
  have hxN : x ∈ N := Subgroup.centralizer_le_normalizer _ hx
  have hxC : x ∈ Subgroup.centralizer (pCoreOf 2 N : Set G) :=
    Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hPT) hx
  exact hPT (h1 ⟨hxN, hxC⟩)

omit [Finite G] in
theorem sq_mem_centralizer_82 {L V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (hCLV : L ⊓ Subgroup.centralizer (V : Set G) = V) {y : G}
    (hyL : y ∈ Subgroup.normalizer (L : Set G)) (hyV : y ∈ Subgroup.centralizer (V : Set G)) :
    y ^ 2 ∈ Subgroup.centralizer (L : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  have hyl : y * l * y⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hyL l).mp hl
  set d := l⁻¹ * (y * l * y⁻¹) with hd
  have hdL : d ∈ L := L.mul_mem (L.inv_mem hl) hyl
  have hdC : d ∈ Subgroup.centralizer (V : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have hv' : l * v * l⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp (hLV hl) v).mp hv
    have h1 : y * (l * v * l⁻¹) = (l * v * l⁻¹) * y :=
      (Subgroup.mem_centralizer_iff.mp hyV _ hv').symm
    have h2 : y * v = v * y := (Subgroup.mem_centralizer_iff.mp hyV v hv).symm
    have h2' : v * y⁻¹ = y⁻¹ * v := by
      calc v * y⁻¹ = y⁻¹ * (y * v) * y⁻¹ := by group
        _ = y⁻¹ * (v * y) * y⁻¹ := by rw [h2]
        _ = y⁻¹ * v := by group
    rw [hd]
    calc v * (l⁻¹ * (y * l * y⁻¹)) = l⁻¹ * ((l * v * l⁻¹) * y) * l * y⁻¹ := by group
      _ = l⁻¹ * (y * (l * v * l⁻¹)) * l * y⁻¹ := by rw [← h1]
      _ = l⁻¹ * y * l * (v * y⁻¹) := by group
      _ = l⁻¹ * y * l * (y⁻¹ * v) := by rw [h2']
      _ = l⁻¹ * (y * l * y⁻¹) * v := by group
  have hdV : d ∈ V := by
    rw [← hCLV]
    exact ⟨hdL, hdC⟩
  have hd2 : d * d = 1 := by
    have := hV.2 d hdV
    rwa [sq] at this
  have hyd : y * d * y⁻¹ = d := by
    rw [(Subgroup.mem_centralizer_iff.mp hyV d hdV).symm, mul_inv_cancel_right]
  have h3 : y * l * y⁻¹ = l * d := by
    rw [hd]
    group
  have h4 : y * y * l = l * (y * y) := by
    calc y * y * l = y * (y * l * y⁻¹) * y⁻¹ * (y * y) := by group
      _ = y * (l * d) * y⁻¹ * (y * y) := by rw [h3]
      _ = (y * l * y⁻¹) * (y * d * y⁻¹) * (y * y) := by group
      _ = (l * d) * d * (y * y) := by rw [h3, hyd]
      _ = l * (d * d) * (y * y) := by group
      _ = l * (y * y) := by rw [hd2, mul_one]
  rw [sq]
  exact h4.symm

omit [Finite G] in
theorem conj_mem_centralizer_82 {V : Subgroup G} {t y : G}
    (ht : t ∈ Subgroup.normalizer (V : Set G)) (hy : y ∈ Subgroup.centralizer (V : Set G)) :
    t * y * t⁻¹ ∈ Subgroup.centralizer (V : Set G) := by
  rw [Subgroup.mem_centralizer_iff] at hy ⊢
  intro v hv
  have hv' : t⁻¹ * v * t⁻¹⁻¹ ∈ V :=
    (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ ht) v).mp hv
  rw [inv_inv] at hv'
  have h1 := hy _ hv'
  calc v * (t * y * t⁻¹) = t * ((t⁻¹ * v * t) * y) * t⁻¹ := by group
    _ = t * (y * (t⁻¹ * v * t)) * t⁻¹ := by rw [h1]
    _ = t * y * t⁻¹ * v := by group

theorem normalizer_eq_of_82 {T L V : Subgroup G}
    (hEven : CFSG.Assembly.Quasithin.quasithinEvenCharacteristic G)
    (hT : quasithinIsSylowTwo T) (hT1 : T ≠ ⊥) (hV : IsElemAbelian 2 V) (hTL : T ≤ L)
    (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (hCLV : L ⊓ Subgroup.centralizer (V : Set G) = V)
    (hTCL : T ⊓ Subgroup.centralizer (L : Set G) = ⊥)
    (hNV : Subgroup.normalizer (L : Set G) ≤ Subgroup.normalizer (V : Set G))
    (hnorm : Subgroup.normalizer (autOn L V : Set (MulAut ↥V)) = autOn L V) :
    Subgroup.normalizer (L : Set G) = L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply le_antisymm _ Subgroup.le_normalizer
  set Y := Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer (V : Set G) with hYdef
  have hCT := centralizer_le_of_even_82 hEven hT hT1
  have hY2 : ∀ y ∈ Y, y ^ 2 = 1 := by
    intro y hy
    have h1 := sq_mem_centralizer_82 hV hLV hCLV hy.1 hy.2
    have h2 : y ^ 2 ∈ T := hCT (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hTL) h1)
    have h3 : y ^ 2 ∈ T ⊓ Subgroup.centralizer (L : Set G) := ⟨h2, h1⟩
    rw [hTCL] at h3
    exact h3
  have hYp : IsPGroup 2 ↥Y := fun y => ⟨1, Subtype.ext (by simpa using hY2 y y.2)⟩
  have hTY : T ≤ Subgroup.normalizer (Y : Set G) := by
    intro t ht
    have htL : t ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer (hTL ht)
    have htV : t ∈ Subgroup.normalizer (V : Set G) := hLV (hTL ht)
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      obtain ⟨hyL, hyV⟩ := Subgroup.mem_inf.mp (show y ∈ Y from hy)
      show t * y * t⁻¹ ∈ Y
      exact Subgroup.mem_inf.mpr ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ htL hyL)
        (Subgroup.inv_mem _ htL), conj_mem_centralizer_82 htV hyV⟩
    · intro hy
      obtain ⟨hyL, hyV⟩ := Subgroup.mem_inf.mp (show t * y * t⁻¹ ∈ Y from hy)
      show y ∈ Y
      have e1 : y = t⁻¹ * (t * y * t⁻¹) * t⁻¹⁻¹ := by group
      rw [e1]
      exact Subgroup.mem_inf.mpr ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _
        (Subgroup.inv_mem _ htL) hyL) (Subgroup.inv_mem _ (Subgroup.inv_mem _ htL)),
        conj_mem_centralizer_82 (Subgroup.inv_mem _ htV) hyV⟩
  have hYT : Y ≤ T := le_of_le_normalizer_82 hT hYp hTY
  intro m hm
  have hmV : m ∈ Subgroup.normalizer (V : Set G) := hNV hm
  have h1 : conjAct V ⟨m, hmV⟩ ∈ autOn L V := by
    rw [← hnorm]
    exact autOn_le_normalizer_82 (X := Subgroup.normalizer (L : Set G)) le_rfl
      ⟨⟨m, hmV⟩, hm, rfl⟩
  obtain ⟨⟨l, hlV⟩, hlL, hlm⟩ := h1
  have hlL' : l ∈ L := hlL
  have hyV : l⁻¹ * m ∈ Subgroup.centralizer (V : Set G) := by
    have h2 : conjAct V ((⟨l, hlV⟩ : ↥(Subgroup.normalizer (V : Set G)))⁻¹ * ⟨m, hmV⟩) = 1 := by
      rw [map_mul, map_inv, hlm, inv_mul_cancel]
    exact (conjAct_eq_one_iff_82 _).mp h2
  have hyL : l⁻¹ * m ∈ Subgroup.normalizer (L : Set G) :=
    mul_mem (inv_mem (Subgroup.le_normalizer hlL')) hm
  have hyT : l⁻¹ * m ∈ T := hYT ⟨hyL, hyV⟩
  have := L.mul_mem hlL' (hTL hyT)
  simpa using this

end L8213E

end CFSG.Quasithin.H13
