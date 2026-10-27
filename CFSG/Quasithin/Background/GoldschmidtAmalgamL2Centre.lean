module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL2Label
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL1Bound

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom

namespace F6

namespace GoldAmL

variable {D : Type*} [Group D] [Finite D] {G₁ G₂ : Subgroup D}

theorem IsNaturalAt.not_le_of_not_le (h : GoldHyp G₁ G₂) {z₁ z₂ : D} {V₁ V₂ : Subgroup D}
    (hn₁ : IsNaturalAt G₁ (G₁ ⊓ G₂) z₁ V₁) (hn₂ : IsNaturalAt G₂ (G₁ ⊓ G₂) z₂ V₂)
    (hV₁ : ¬ V₁ ≤ pCoreOf 2 G₂) : ¬ V₂ ≤ pCoreOf 2 G₁ := by
  intro hV₂
  obtain ⟨v, hvV, hvQ⟩ : ∃ v ∈ V₁, v ∉ pCoreOf 2 G₂ := by
    by_contra hcon
    push Not at hcon
    exact hV₁ (fun x hx => hcon x hx)
  have hvT : v ∈ G₁ ⊓ G₂ := h.pCoreOf_left_le (hn₁.le_pCoreOf hvV)
  obtain ⟨a, ha1, haz, hVset⟩ := hn₂.basis
  have haV : a ∈ V₂ := by
    have : a ∈ (V₂ : Set D) := by rw [hVset]; simp
    exact this
  have h1 : v * a * v⁻¹ = a * z₂ := hn₂.conj_eq_mul inf_le_right hvT hvQ haV ha1 haz
  have h2 : v * a * v⁻¹ = a := by
    have hc : a * v = v * a := Subgroup.mem_centralizer_iff.mp (hn₁.le_center hvV).2 a
      (hV₂ haV)
    rw [← hc]; group
  have h3 : a * z₂ = a * 1 := by rw [← h1, h2, mul_one]
  exact hn₂.z_ne (mul_left_cancel h3)

theorem IsNaturalAt.le_pCoreOf_of_large (h : GoldHyp G₁ G₂) (h32 : 32 ≤ Nat.card ↥(G₁ ⊓ G₂))
    {z : D} {V : Subgroup D} (hn : IsNaturalAt G₁ (G₁ ⊓ G₂) z V) : V ≤ pCoreOf 2 G₂ := by
  by_contra hV
  rcases natural_step h hn with hV' | ⟨z₂, V₂, hn₂, -, -⟩
  · exact hV hV'
  · have hV₂ := hn.not_le_of_not_le h hn₂ hV
    have := card_le_sixteen_of_b_one h hn hn₂ hV hV₂
    omega

theorem centre_unique (h : GoldHyp G₁ G₂) (h32 : 32 ≤ Nat.card ↥(G₁ ⊓ G₂)) {z z' : D}
    {V V' : Subgroup D} (hn : IsNaturalAt G₁ (G₁ ⊓ G₂) z V)
    (hb : critDist (G₁ ⊔ G₂) G₁ G₂ V = 2) (hn' : IsNaturalAt G₁ (G₁ ⊓ G₂) z' V') : z' = z := by
  have hV'Q := hn'.le_pCoreOf_of_large h h32
  have hzG₂ := centralizes_of_critDist_two h hn hb
  have hcomm := (two_structure_of_critDist_two h hn hb).2.1
  obtain ⟨-, hUQ, -, x, hxG₂, hWU, -, hQW, -, -, -, -, -⟩ :=
    critDist_two_structure_of_natural h hn hb
  obtain ⟨w, hwW, hwQ⟩ : ∃ w ∈ conjSub x V, w ∉ pCoreOf 2 G₁ := by
    by_contra hcon
    push Not at hcon
    have hle : conjSub x V ≤ pCoreOf 2 G₁ := fun w hw => hcon w hw
    rw [sup_eq_left.mpr hle] at hQW
    have h1 := h.relIndex_pCoreOf_T_left
    rw [hQW, Subgroup.relIndex_self] at h1
    omega
  have hwQ₂ : w ∈ pCoreOf 2 G₂ := hUQ (hWU hwW)
  have hwT : w ∈ G₁ ⊓ G₂ := h.pCoreOf_right_le hwQ₂
  have hv : x⁻¹ * w * x ∈ V := mem_conjSub.mp hwW
  obtain ⟨a, ha1, haz, hVset⟩ := hn'.basis
  have haV' : a ∈ V' := by
    have : a ∈ (V' : Set D) := by rw [hVset]; simp
    exact this
  have haQ₂ : a ∈ pCoreOf 2 G₂ := hV'Q haV'
  have haT : a ∈ G₁ ⊓ G₂ := h.pCoreOf_right_le haQ₂
  have h1 : w * a * w⁻¹ = a * z' := hn'.conj_eq_mul inf_le_left hwT hwQ haV' ha1 haz
  have hxQ : x⁻¹ ∈ Subgroup.normalizer (pCoreOf 2 G₂ : Set D) :=
    le_normalizer_pCoreOf 2 G₂ (G₂.inv_mem hxG₂)
  have haQ' : x⁻¹ * a * x ∈ pCoreOf 2 G₂ := by
    have := (Subgroup.mem_normalizer_iff.mp hxQ a).mp haQ₂
    simpa using this
  have hmem : (x⁻¹ * w * x) * (x⁻¹ * a * x) * (x⁻¹ * w * x)⁻¹ * (x⁻¹ * a * x)⁻¹ ∈
      Subgroup.zpowers z := by
    have := Subgroup.commutator_mem_commutator hv haQ'
    rw [hcomm] at this
    exact this
  have hconjz : ∀ y ∈ Subgroup.zpowers z, x * y * x⁻¹ ∈ Subgroup.zpowers z := by
    intro y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    rw [← conj_zpow, hzG₂ x hxG₂]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers z) k
  have hcw : w * a * w⁻¹ * a⁻¹ ∈ Subgroup.zpowers z := by
    have := hconjz _ hmem
    have e : x * ((x⁻¹ * w * x) * (x⁻¹ * a * x) * (x⁻¹ * w * x)⁻¹ * (x⁻¹ * a * x)⁻¹) * x⁻¹
        = w * a * w⁻¹ * a⁻¹ := by group
    rwa [e] at this
  have haz' : a * z' = z' * a := Subgroup.mem_centralizer_iff.mp hn'.z_mem.2 a haT
  have hcw' : w * a * w⁻¹ * a⁻¹ = z' := by
    rw [h1, haz']; group
  rw [hcw'] at hcw
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hcw
  rcases zpow_eq_one_or_self hn.z_sq k with h2 | h2
  · exact absurd (hk.symm.trans h2) hn'.z_ne
  · exact hk.symm.trans h2

theorem Vertex.centralizes_norm {H T : Subgroup D} (hv : Vertex H T) {ω x z' : D}
    (hωZ : ω ∈ centerOf T) (hxH : x ∈ H) (hx3 : x * x * x = 1) (hxω : x * ω * x⁻¹ ≠ ω)
    (hz' : z' = (x * ω * x⁻¹) * (x * x * ω * (x * x)⁻¹)) (hz'Z : z' ∈ centerOf T) :
    ∀ y ∈ H, y * (ω * z') = (ω * z') * y := by
  have hTH : T ≤ H := hv.T_le
  have hQT : pCoreOf 2 H ≤ T := hv.pCoreOf_le
  have hQN : H ≤ Subgroup.normalizer (pCoreOf 2 H : Set D) := le_normalizer_pCoreOf 2 H
  have hωQ : ω ∈ centerOf (pCoreOf 2 H) :=
    ⟨hv.centerOf_le hωZ, Subgroup.centralizer_le hQT hωZ.2⟩
  have hcomm : ∀ u ∈ centerOf (pCoreOf 2 H), ∀ v ∈ centerOf (pCoreOf 2 H), u * v = v * u :=
    fun u hu v hv' => Subgroup.mem_centralizer_iff.mp hv'.2 u hu.1
  obtain ⟨w₁, hw₁⟩ : ∃ w : D, w = x * ω * x⁻¹ := ⟨_, rfl⟩
  obtain ⟨w₂, hw₂⟩ : ∃ w : D, w = x * x * ω * (x * x)⁻¹ := ⟨_, rfl⟩
  have hw₁Q : w₁ ∈ centerOf (pCoreOf 2 H) := by
    rw [hw₁]; exact conj_mem_centerOf' (hQN hxH) hωQ
  have hw₂Q : w₂ ∈ centerOf (pCoreOf 2 H) := by
    rw [hw₂]; exact conj_mem_centerOf' (hQN (H.mul_mem hxH hxH)) hωQ
  have hz'e : z' = w₁ * w₂ := by rw [hz', hw₁, hw₂]
  have hxN : x * (ω * z') * x⁻¹ = ω * z' := by
    have hx₁ : x * w₁ * x⁻¹ = w₂ := by rw [hw₁, hw₂]; group
    have hx₂ : x * w₂ * x⁻¹ = ω := by
      rw [hw₂]
      calc x * (x * x * ω * (x * x)⁻¹) * x⁻¹ = (x * x * x) * ω * (x * x * x)⁻¹ := by group
        _ = ω := by rw [hx3]; group
    calc x * (ω * z') * x⁻¹ = (x * ω * x⁻¹) * ((x * w₁ * x⁻¹) * (x * w₂ * x⁻¹)) := by
          rw [hz'e]; group
      _ = w₁ * (w₂ * ω) := by rw [hx₁, hx₂, ← hw₁]
      _ = ω * (w₁ * w₂) := by
          calc w₁ * (w₂ * ω) = w₁ * (ω * w₂) := by rw [hcomm w₂ hw₂Q ω hωQ]
            _ = (w₁ * ω) * w₂ := (mul_assoc _ _ _).symm
            _ = (ω * w₁) * w₂ := by rw [hcomm w₁ hw₁Q ω hωQ]
            _ = ω * (w₁ * w₂) := mul_assoc _ _ _
      _ = ω * z' := by rw [hz'e]
  have hxT : x ∉ T := fun hxT => hxω ((Subgroup.mem_centralizer_iff.mp hωZ.2 x hxT).symm ▸
    by group)
  have hNZ : ω * z' ∈ centerOf T := (centerOf T).mul_mem hωZ hz'Z
  let C : Subgroup D := H ⊓ Subgroup.centralizer ({ω * z'} : Set D)
  have hTC : T ≤ C := fun t ht =>
    ⟨hTH ht, Subgroup.mem_centralizer_iff.mpr fun y hy => by
      rw [Set.mem_singleton_iff] at hy
      rw [hy]; exact (Subgroup.mem_centralizer_iff.mp hNZ.2 t ht).symm⟩
  have hxC : x ∈ C := ⟨hxH, Subgroup.mem_centralizer_iff.mpr fun y hy => by
    rw [Set.mem_singleton_iff] at hy
    rw [hy]; exact (mul_eq_of_conj_eq hxN).symm⟩
  have hHC : H ≤ C := hv.le_of_not_mem hTC inf_le_left hxC hxT
  intro y hy
  exact (Subgroup.mem_centralizer_iff.mp (hHC hy).2 (ω * z') rfl).symm

theorem omega_involution_mem_mul (h : GoldHyp G₁ G₂) (h32 : 32 ≤ Nat.card ↥(G₁ ⊓ G₂)) {z : D}
    {V : Subgroup D} (hn : IsNaturalAt G₁ (G₁ ⊓ G₂) z V)
    (hb : critDist (G₁ ⊔ G₂) G₁ G₂ V = 2) {ω : D} (hωZ : ω ∈ centerOf (G₁ ⊓ G₂))
    (hω2 : ω ^ 2 = 1) :
    ∃ ε ∈ centerOf (G₁ ⊓ G₂), ε * ε = 1 ∧ (∀ y ∈ G₁, y * ε = ε * y) ∧
      ∃ e ∈ Subgroup.zpowers z, ω = ε * e := by
  by_cases hfix : ∀ g ∈ G₁, g * ω * g⁻¹ = ω
  · exact ⟨ω, hωZ, by rw [← pow_two]; exact hω2, fun y hy => mul_eq_of_conj_eq (hfix y hy), 1,
      Subgroup.one_mem _, by simp⟩
  · push Not at hfix
    obtain ⟨g, hg, hgω⟩ := hfix
    obtain ⟨x, z', V', hxH, hx3, hxω, hz', hn', -⟩ :=
      exists_natural_data h.vertex_left hωZ hω2 ⟨g, hg, hgω⟩
    have hz'z : z' = z := centre_unique h h32 hn hb hn'
    have hz'2 : z' * z' = 1 := by have := hn'.z_sq; rwa [pow_two] at this
    have hωz' : ω * z' = z' * ω := Subgroup.mem_centralizer_iff.mp hn'.z_mem.2 ω hωZ.1
    refine ⟨ω * z', (centerOf (G₁ ⊓ G₂)).mul_mem hωZ hn'.z_mem, ?_,
      h.vertex_left.centralizes_norm hωZ hxH hx3 hxω hz' hn'.z_mem, z',
      hz'z ▸ Subgroup.mem_zpowers z, ?_⟩
    · calc ω * z' * (ω * z') = ω * (z' * ω) * z' := by group
        _ = ω * (ω * z') * z' := by rw [← hωz']
        _ = (ω * ω) * (z' * z') := by group
        _ = 1 := by rw [hz'2, mul_one, ← pow_two, hω2]
    · rw [mul_assoc, hz'2, mul_one]

theorem eq_one_or_eq_of_trivial_central (h : GoldHyp G₁ G₂) (h32 : 32 ≤ Nat.card ↥(G₁ ⊓ G₂))
    {z : D} {V : Subgroup D} (hn : IsNaturalAt G₁ (G₁ ⊓ G₂) z V)
    (hb : critDist (G₁ ⊔ G₂) G₁ G₂ V = 2)
    (hA : ∀ ε ∈ centerOf (G₁ ⊓ G₂), ε * ε = 1 → (∀ y ∈ G₁, y * ε = ε * y) → ε = 1) {ω : D}
    (hωZ : ω ∈ centerOf (G₁ ⊓ G₂)) (hω2 : ω ^ 2 = 1) : ω = 1 ∨ ω = z := by
  obtain ⟨ε, hεZ, hε2, hεc, e, he, rfl⟩ := omega_involution_mem_mul h h32 hn hb hωZ hω2
  rw [hA ε hεZ hε2 hεc, one_mul]
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp he
  exact zpow_eq_one_or_self hn.z_sq k

theorem V_le_of_normal (h : GoldHyp G₁ G₂) (h32 : 32 ≤ Nat.card ↥(G₁ ⊓ G₂)) {z : D}
    {V : Subgroup D} (hn : IsNaturalAt G₁ (G₁ ⊓ G₂) z V)
    (hb : critDist (G₁ ⊔ G₂) G₁ G₂ V = 2)
    (hA : ∀ ε ∈ centerOf (G₁ ⊓ G₂), ε * ε = 1 → (∀ y ∈ G₁, y * ε = ε * y) → ε = 1)
    {N : Subgroup D} (hNT : N ≤ G₁ ⊓ G₂) (hN1 : N ≠ ⊥)
    (hNn : ∀ l ∈ G₁, ∀ n ∈ N, l * n * l⁻¹ ∈ N) : V ≤ N := by
  have hT2 : IsPGroup 2 ↥(G₁ ⊓ G₂) := h.amalgam.toIsGoldschmidtVTriple.isPGroup_inf
  have hTN : G₁ ⊓ G₂ ≤ Subgroup.normalizer (N : Set D) := by
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy; exact hNn t ht.1 y hy
    · intro hy
      have := hNn t⁻¹ (G₁.inv_mem ht.1) _ hy
      simpa [mul_assoc] using this
  have hTbot : G₁ ⊓ G₂ ≤ Subgroup.normalizer ((⊥ : Subgroup D) : Set D) := by
    intro t _
    rw [Subgroup.mem_normalizer_iff]
    intro y
    simp [Subgroup.mem_bot]
  obtain ⟨x, hxN, hx1, hxT⟩ :=
    D14.exists_fixed_of_lt hT2 hNT (bot_lt_iff_ne_bot.mpr hN1) hTN hTbot
  have hxcent : x ∈ Subgroup.centralizer ((G₁ ⊓ G₂ : Subgroup D) : Set D) := by
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    have h' := Subgroup.mem_bot.mp (hxT t ht)
    calc t * x = (t * x * t⁻¹ * x⁻¹) * (x * t) := by group
      _ = x * t := by rw [h', one_mul]
  obtain ⟨C, hCdef⟩ : ∃ C : Subgroup D, C = N ⊓ centerOf (G₁ ⊓ G₂) := ⟨_, rfl⟩
  have hxC : x ∈ C := by rw [hCdef]; exact ⟨hxN, hNT hxN, hxcent⟩
  have hCT : IsPGroup 2 C := hT2.to_le (by rw [hCdef]; exact inf_le_left.trans hNT)
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ω', hω'⟩ : ∃ ω : ↥C, orderOf ω = 2 := by
    refine exists_prime_orderOf_dvd_card' 2 ?_
    obtain ⟨k, hk⟩ := hCT.exists_card_eq
    have hk0 : k ≠ 0 := by
      rintro rfl
      have hC1 : C = ⊥ := Subgroup.eq_bot_of_card_eq C (by simpa using hk)
      exact hx1 (by rw [hC1] at hxC; exact hxC)
    rw [hk]
    exact dvd_pow_self 2 hk0
  have hωo : orderOf (ω' : D) = 2 := by rw [Subgroup.orderOf_coe, hω']
  have hω2 : (ω' : D) ^ 2 = 1 := by rw [← hωo]; exact pow_orderOf_eq_one _
  have hω1 : (ω' : D) ≠ 1 := fun e => by rw [e, orderOf_one] at hωo; omega
  have hωC : (ω' : D) ∈ (N ⊓ centerOf (G₁ ⊓ G₂) : Subgroup D) := by
    rw [← hCdef]; exact ω'.2
  have hωz := eq_one_or_eq_of_trivial_central h h32 hn hb hA hωC.2 hω2
  have hzN : z ∈ N := by
    rcases hωz with h1 | h1
    · exact absurd h1 hω1
    · rw [← h1]; exact hωC.1
  rw [hn.V_eq]
  refine conjClosure_le fun g hg u hu => ?_
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
  rw [← conj_zpow]
  exact N.zpow_mem (hNn g hg z hzN) k

end GoldAmL

end F6

end CFSG.Quasithin
