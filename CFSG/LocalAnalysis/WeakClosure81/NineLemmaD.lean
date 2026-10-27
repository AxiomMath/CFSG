module

public import CFSG.LocalAnalysis.WeakClosure81.NineStruct
public import CFSG.Quasithin.Background.RonanD33
public import CFSG.Goldschmidt.Steps.G37Basic

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace TwoPTwoIrred

variable {K S X : Subgroup G} {p : ℕ}

theorem nineFrattini_le (X : Subgroup G) : nineFrattini X ≤ X :=
  Subgroup.map_subtype_le (frattini ↥X)

theorem normalizer_le_normalizer_nineFrattini (X : Subgroup G) :
    Subgroup.normalizer (X : Set G) ≤ Subgroup.normalizer (nineFrattini X : Set G) :=
  CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic (K := frattini ↥X)

theorem eq_of_sup_nineFrattini_eq {Z X : Subgroup G} (hZX : Z ≤ X)
    (h : Z ⊔ nineFrattini X = X) : Z = X := by
  have hΦ : (nineFrattini X).subgroupOf X = frattini ↥X := by
    show ((frattini ↥X).map X.subtype).comap X.subtype = frattini ↥X
    rw [Subgroup.comap_map_eq, Subgroup.ker_subtype, sup_bot_eq]
  have htop : Z.subgroupOf X ⊔ frattini ↥X = ⊤ := by
    rw [← hΦ, ← Subgroup.subgroupOf_sup hZX (nineFrattini_le X), h, Subgroup.subgroupOf_self]
  have hZt : Z.subgroupOf X = ⊤ := frattini_nongenerating htop
  rw [← Subgroup.map_subgroupOf_eq_of_le hZX, hZt]
  show (⊤ : Subgroup ↥X).map X.subtype = X
  rw [← MonoidHom.range_eq_map]
  exact Subgroup.range_subtype X

theorem inf_sup_le_frattiniR {N X K : Subgroup G} (hXK : X ≤ K)
    (hZleΦ : X ⊓ (N ⊔ pCoreOf 2 K) ≤ nineFrattini X) :
    (N ⊔ pCoreOf 2 K) ⊓ (pCoreOf 2 K ⊔ X) ≤ nineFrattiniR K X := by
  intro c hc
  rw [Subgroup.mem_inf] at hc
  obtain ⟨hcNR, hcRX⟩ := hc
  have hXR : X ≤ Subgroup.normalizer (pCoreOf 2 K : Set G) :=
    hXK.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K)
  obtain ⟨x, hx, r, hr, hxr⟩ :=
    CFSG.Goldschmidt.G37.mem_sup_of_le_normalizer hXR (by rwa [sup_comm] at hcRX)
  have hxZ : x ∈ X ⊓ (N ⊔ pCoreOf 2 K) := by
    refine ⟨hx, ?_⟩
    have hx' : x = c * r⁻¹ := by rw [← hxr]; group
    rw [hx']
    exact (N ⊔ pCoreOf 2 K).mul_mem hcNR
      ((N ⊔ pCoreOf 2 K).inv_mem (Subgroup.mem_sup_right hr))
  rw [nineFrattiniR]
  rw [← hxr]
  exact Subgroup.mul_mem_sup (hZleΦ hxZ) hr

theorem normal_le_frattiniR_or (h : TwoPTwoIrred K S X p) {N : Subgroup G} (hNK : N ≤ K)
    (hN : (N.subgroupOf K).Normal) :
    N ≤ nineFrattiniR K X ∨ (X ≤ N ⊔ pCoreOf 2 K ∧ twoResidual K ≤ N) := by
  have h₀ := h.toTwoPTwo
  have hXK : X ≤ K := h.sylowP.le
  have hSK : S ≤ K := h.sylowTwo.le
  have hKN : K ≤ Subgroup.normalizer (N : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNK).1 hN
  have hKR : K ≤ Subgroup.normalizer (pCoreOf 2 K : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K
  have hRXK : pCoreOf 2 K ⊔ X ≤ K :=
    sup_le (CFSG.LieType.BorelTits.pCoreOf_le 2 K) hXK
  have hK_RX : K ≤ Subgroup.normalizer ((pCoreOf 2 K ⊔ X : Subgroup G) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hRXK).1 h₀.normal_pCoreOf_sup
  have hnormY : ∀ s ∈ S ⊓ Subgroup.normalizer (X : Set G),
      ∀ y ∈ (X ⊓ (N ⊔ pCoreOf 2 K)) ⊔ nineFrattini X,
        s * y * s⁻¹ ∈ (X ⊓ (N ⊔ pCoreOf 2 K)) ⊔ nineFrattini X := by
    intro s hs y hy
    have hsS : s ∈ S := hs.1
    have hsX : s ∈ Subgroup.normalizer (X : Set G) := hs.2
    have hsK : s ∈ K := hSK hsS
    have hsNR : s ∈ Subgroup.normalizer ((N ⊔ pCoreOf 2 K : Subgroup G) : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro z
      constructor
      · intro hz
        exact RonanD33.conj_mem_sup
          (fun n hn => (Subgroup.mem_normalizer_iff.mp (hKN hsK) n).mp hn)
          (fun r hr => (Subgroup.mem_normalizer_iff.mp (hKR hsK) r).mp hr) hz
      · intro hz
        have hsK' : s⁻¹ ∈ K := K.inv_mem hsK
        have h2 := RonanD33.conj_mem_sup
          (fun n hn => (Subgroup.mem_normalizer_iff.mp (hKN hsK') n).mp hn)
          (fun r hr => (Subgroup.mem_normalizer_iff.mp (hKR hsK') r).mp hr) hz
        have heq : s⁻¹ * (s * z * s⁻¹) * (s⁻¹)⁻¹ = z := by group
        rwa [heq] at h2
    have hsZ : s ∈ Subgroup.normalizer
        ((X ⊓ (N ⊔ pCoreOf 2 K) : Subgroup G) : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro z
      rw [Subgroup.mem_inf, Subgroup.mem_inf]
      constructor
      · rintro ⟨hzX, hzNR⟩
        exact ⟨(Subgroup.mem_normalizer_iff.mp hsX z).mp hzX,
          (Subgroup.mem_normalizer_iff.mp hsNR z).mp hzNR⟩
      · rintro ⟨hzX, hzNR⟩
        exact ⟨(Subgroup.mem_normalizer_iff.mp hsX z).mpr hzX,
          (Subgroup.mem_normalizer_iff.mp hsNR z).mpr hzNR⟩
    have hsΦ : s ∈ Subgroup.normalizer (nineFrattini X : Set G) :=
      normalizer_le_normalizer_nineFrattini X hsX
    have hsY : s ∈ Subgroup.normalizer
        (((X ⊓ (N ⊔ pCoreOf 2 K)) ⊔ nineFrattini X : Subgroup G) : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro z
      constructor
      · intro hz
        exact RonanD33.conj_mem_sup
          (fun a ha => (Subgroup.mem_normalizer_iff.mp hsZ a).mp ha)
          (fun a ha => (Subgroup.mem_normalizer_iff.mp hsΦ a).mp ha) hz
      · intro hz
        have hsZ' : s⁻¹ ∈ Subgroup.normalizer
            ((X ⊓ (N ⊔ pCoreOf 2 K) : Subgroup G) : Set G) := Subgroup.inv_mem _ hsZ
        have hsΦ' : s⁻¹ ∈ Subgroup.normalizer (nineFrattini X : Set G) :=
          Subgroup.inv_mem _ hsΦ
        have h2 := RonanD33.conj_mem_sup
          (fun a ha => (Subgroup.mem_normalizer_iff.mp hsZ' a).mp ha)
          (fun a ha => (Subgroup.mem_normalizer_iff.mp hsΦ' a).mp ha) hz
        have heq : s⁻¹ * (s * z * s⁻¹) * (s⁻¹)⁻¹ = z := by group
        rwa [heq] at h2
    exact (Subgroup.mem_normalizer_iff.mp hsY y).mp hy
  rcases h.irred.2 ((X ⊓ (N ⊔ pCoreOf 2 K)) ⊔ nineFrattini X) le_sup_right
      (sup_le inf_le_left (nineFrattini_le X)) hnormY with hY | hY
  ·
    left
    have hZleΦ : X ⊓ (N ⊔ pCoreOf 2 K) ≤ nineFrattini X := by
      have h1 : X ⊓ (N ⊔ pCoreOf 2 K) ≤
          (X ⊓ (N ⊔ pCoreOf 2 K)) ⊔ nineFrattini X := le_sup_left
      rwa [hY] at h1
    have device := inf_sup_le_frattiniR (K := K) (N := N) (X := X) hXK hZleΦ
    have hcomm : ∀ n ∈ N, ∀ x ∈ X, ⁅n, x⁆ ∈ nineFrattiniR K X := by
      intro n hn x hx
      apply device
      rw [Subgroup.mem_inf]
      constructor
      · refine Subgroup.mem_sup_left ?_
        have hxn : x * n⁻¹ * x⁻¹ ∈ N :=
          (Subgroup.mem_normalizer_iff.mp (hKN (hXK hx)) n⁻¹).mp (N.inv_mem hn)
        simpa [commutatorElement_def, mul_assoc] using N.mul_mem hn hxn
      · have hnK : n ∈ K := hNK hn
        have h1 : n * x * n⁻¹ ∈ pCoreOf 2 K ⊔ X :=
          (Subgroup.mem_normalizer_iff.mp (hK_RX hnK) x).mp (Subgroup.mem_sup_right hx)
        simpa [commutatorElement_def, mul_assoc] using
          (pCoreOf 2 K ⊔ X).mul_mem h1
            ((pCoreOf 2 K ⊔ X).inv_mem (Subgroup.mem_sup_right hx))
    have hb : ∀ n ∈ N, ∀ a : ℕ, n ^ 2 ^ a = 1 → n ∈ pCoreOf 2 K := by
      intro n hn a ha
      exact h₀.mem_pCoreOf_of_commutator_mem_frattiniR (hNK hn) ha (hcomm n hn)
    have hc : N ≤ pCoreOf 2 K ⊔ X := by
      intro n hn
      obtain ⟨k, m, hm_odd, horder⟩ :=
        Nat.exists_eq_two_pow_mul_odd (n := orderOf n) (orderOf_pos n).ne'
      have hcop : Nat.Coprime m (2 ^ k) := by
        rcases k with _ | j
        · simp
        · exact (Nat.coprime_pow_right_iff (Nat.succ_pos j) m 2).mpr
            (Nat.coprime_two_right.mpr hm_odd)
      refine RonanD33.mem_of_pow_mem_of_coprime hcop ?_ ?_
      · refine Subgroup.mem_sup_left (hb (n ^ m) (N.pow_mem hn m) k ?_)
        rw [← pow_mul]
        have hm : m * 2 ^ k = orderOf n := by rw [horder, mul_comm]
        rw [hm, pow_orderOf_eq_one]
      · refine h₀.mem_sup_of_odd_orderOf (K.pow_mem (hNK hn) (2 ^ k)) ?_
        refine Odd.of_dvd_nat hm_odd ?_
        rw [orderOf_dvd_iff_pow_eq_one, ← pow_mul]
        have hk : 2 ^ k * m = orderOf n := horder.symm
        rw [hk, pow_orderOf_eq_one]
    intro n hn
    exact device (by
      rw [Subgroup.mem_inf]
      exact ⟨Subgroup.mem_sup_left hn, hc hn⟩)
  ·
    right
    have hZeqX : X ⊓ (N ⊔ pCoreOf 2 K) = X :=
      eq_of_sup_nineFrattini_eq inf_le_left hY
    constructor
    · intro x hx
      have hxZ : x ∈ X ⊓ (N ⊔ pCoreOf 2 K) := by rw [hZeqX]; exact hx
      exact hxZ.2
    · refine h₀.twoResidual_le_of_le_sup hNK hN ?_
      intro x hx
      have hxZ : x ∈ X ⊓ (N ⊔ pCoreOf 2 K) := by rw [hZeqX]; exact hx
      exact hxZ.2

theorem twoResidual_le_of_not_le_frattiniR (h : TwoPTwoIrred K S X p) {N : Subgroup G}
    (hNK : N ≤ K) (hN : (N.subgroupOf K).Normal) (hnot : ¬ N ≤ nineFrattiniR K X) :
    twoResidual K ≤ N := by
  rcases normal_le_frattiniR_or h hNK hN with hle | ⟨-, hres⟩
  · exact absurd hle hnot
  · exact hres

end TwoPTwoIrred

end CFSG.LocalAnalysis.WeakClosure81
