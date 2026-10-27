module

public import CFSG.Quasithin.Recognition.GoldschmidtF112FA5Beta

public section

namespace CFSG.Quasithin.Kleidman.F204

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7 CFSG.Quasithin
  CFSG.Quasithin.FA5 CFSG.QuasithinUnique.A5.Delta5

variable {G : Type} [Group G] [Finite G] {L1 L2 S D X : Subgroup G}

omit [Finite G] in
theorem P2_le_sup_Q2 (F : Frame L1 L2 S D X) : P2 L1 L2 S ≤ L2 ⊔ Q2 L1 L2 S := by
  have hB : bigB L1 L2 S ≤ L2 ⊔ Q2 L1 L2 S := by
    rw [F.bigB_eq]
    refine sup_le ?_ (F.D_le.trans le_sup_left)
    intro s hs
    obtain ⟨l, hl, q, hq, rfl⟩ := F.untw s hs
    exact Subgroup.mul_mem _ ((le_sup_left : L2 ≤ L2 ⊔ Q2 L1 L2 S) hl)
      ((le_sup_right : Q2 L1 L2 S ≤ L2 ⊔ Q2 L1 L2 S) hq)
  exact sup_le le_sup_left hB

theorem exists_mul_P2 (F : Frame L1 L2 S D X) {x : G} (hx : x ∈ P2 L1 L2 S) :
    ∃ l ∈ L2, ∃ q ∈ Q2 L1 L2 S, x = l * q := by
  have hL : L2 ≤ Subgroup.normalizer (Q2 L1 L2 S : Set G) :=
    (le_sup_left : L2 ≤ P2 L1 L2 S).trans (P2_le_normalizer_Q2 L1 L2 S)
  have hx' : x ∈ Q2 L1 L2 S ⊔ L2 := by rw [sup_comm]; exact P2_le_sup_Q2 F hx
  obtain ⟨q, hq, l, hl, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hL).mp hx'
  refine ⟨l, hl, l⁻¹ * q * l, ?_, by group⟩
  have := (Subgroup.mem_normalizer_iff.mp (hL ((L2).inv_mem hl)) q).mp hq
  simpa using this

theorem Q2_of_commute_three (F : Frame L1 L2 S D X) {z t : G} (hz : z ∈ P2 L1 L2 S)
    (ht : t ∈ P2 L1 L2 S) {k : ℕ} (hz2 : z ^ 2 ^ k = 1) (ht3 : t ^ 3 = 1) (ht1 : t ≠ 1)
    (hc : z * t = t * z) : z ∈ Q2 L1 L2 S := by
  obtain ⟨φ, -, hφ⟩ := F.exists_phi
  obtain ⟨lz, hlz, qz, hqz, rfl⟩ := exists_mul_P2 F hz
  obtain ⟨lt, hlt, qt, hqt, rfl⟩ := exists_mul_P2 F ht
  set π : ↥(P2 L1 L2 S) →* oTwoQuot ↥(P2 L1 L2 S) :=
    QuotientGroup.mk' (CFSG.Open.pCore 2 ↥(P2 L1 L2 S)) with hπ
  have hπ1 : ∀ g : ↥(P2 L1 L2 S), π g = 1 ↔ (g : G) ∈ Q2 L1 L2 S := fun g => by
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact F1.mem_pCore_iff_coe g
  have hπeq : ∀ g h : ↥(P2 L1 L2 S), π g = π h ↔ (g : G)⁻¹ * (h : G) ∈ Q2 L1 L2 S := fun g h => by
    rw [← inv_mul_eq_one, ← map_inv, ← map_mul, hπ1]; rfl
  have hLP : ∀ {l : G}, l ∈ L2 → l ∈ P2 L1 L2 S := fun hl => (le_sup_left : L2 ≤ P2 L1 L2 S) hl
  have hQP : ∀ {q : G}, q ∈ Q2 L1 L2 S → q ∈ P2 L1 L2 S := fun hq =>
    (pCoreOf_le 2 (P2 L1 L2 S)) hq
  set zl : ↥(P2 L1 L2 S) := ⟨lz, hLP hlz⟩ with hzl
  set tl : ↥(P2 L1 L2 S) := ⟨lt, hLP hlt⟩ with htl
  set zq : ↥(P2 L1 L2 S) := ⟨qz, hQP hqz⟩ with hzq
  set tq : ↥(P2 L1 L2 S) := ⟨qt, hQP hqt⟩ with htq
  have hπz : π (zl * zq) = π zl := by
    rw [map_mul, (hπ1 zq).mpr hqz, mul_one]
  have hπt : π (tl * tq) = π tl := by
    rw [map_mul, (hπ1 tq).mpr hqt, mul_one]
  have hz2' : (zl * zq) ^ 2 ^ k = 1 := Subtype.ext (by simpa using hz2)
  have ht3' : (tl * tq) ^ 3 = 1 := Subtype.ext (by simpa using ht3)
  have hc' : (zl * zq) * (tl * tq) = (tl * tq) * (zl * zq) := Subtype.ext (by simpa using hc)
  have ht1' : (tl * tq) ≠ 1 := fun h => ht1 (by simpa using congrArg Subtype.val h)
  have hrel2 : π zl ^ 2 ^ k = 1 := by rw [← hπz, ← map_pow, hz2', map_one]
  have hrel3 : π tl ^ 3 = 1 := by rw [← hπt, ← map_pow, ht3', map_one]
  have hrelc : π zl * π tl = π tl * π zl := by
    rw [← hπz, ← hπt, ← map_mul, ← map_mul, hc']
  have hQL : ∀ l : ↥L2, (l : G) ∈ Q2 L1 L2 S → φ l = 1 := fun l hl =>
    (hφ l).mpr (Frame.inf_Q2_le ⟨l.2, hl⟩)
  set zL : ↥L2 := ⟨lz, hlz⟩ with hzL
  set tL : ↥L2 := ⟨lt, hlt⟩ with htL
  have hQ2pow : lz ^ 2 ^ k ∈ Q2 L1 L2 S := by
    have := (hπ1 (zl ^ 2 ^ k)).mp (by rw [map_pow]; exact hrel2)
    simpa [hzl] using this
  have hQ3pow : lt ^ 3 ∈ Q2 L1 L2 S := by
    have := (hπ1 (tl ^ 3)).mp (by rw [map_pow]; exact hrel3)
    simpa [htl] using this
  have hQcomm : lz * lt * lz⁻¹ * lt⁻¹ ∈ Q2 L1 L2 S := by
    have := (hπ1 (zl * tl * zl⁻¹ * tl⁻¹)).mp (by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hrelc]; group)
    simpa [hzl, htl] using this
  have hφz : φ zL ^ 2 ^ k = 1 := by
    rw [← map_pow]
    exact hQL _ (by simpa [hzL] using hQ2pow)
  have hφt : φ tL ^ 3 = 1 := by
    rw [← map_pow]
    exact hQL _ (by simpa [htL] using hQ3pow)
  have hφc : φ zL * φ tL = φ tL * φ zL := by
    have h0 : φ (zL * tL * zL⁻¹ * tL⁻¹) = 1 :=
      hQL _ (by simpa [hzL, htL] using hQcomm)
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h0
    exact mul_inv_eq_one.mp (mul_inv_eq_one.mp h0)
  have hφt1 : φ tL ≠ 1 := by
    intro h
    apply ht1
    have hlt' : lt ∈ pCoreOf 2 L2 := (hφ tL).mp h
    have hmem : lt * qt ∈ Q2 L1 L2 S := (Q2 L1 L2 S).mul_mem (F.pCore_L2_le_Q2 hlt') hqt
    obtain ⟨j, hj⟩ := pCoreOf_isPGroup 2 (P2 L1 L2 S) ⟨lt * qt, hmem⟩
    have hj' : (lt * qt) ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
    have hcop : Nat.gcd (2 ^ j) 3 = 1 := Nat.Coprime.pow_left j (by norm_num)
    have := pow_gcd_eq_one.mpr ⟨hj', ht3⟩
    rwa [hcop, pow_one] at this
  have hsq : φ zL ^ 2 = 1 := alt5_sq_eq_one_of_two_power hφz
  have h1 : φ zL = 1 := alt5_eq_one_of_commute_three hφt hφt1 hφc hsq
  have hlz' : lz ∈ pCoreOf 2 L2 := (hφ zL).mp h1
  exact (Q2 L1 L2 S).mul_mem (F.pCore_L2_le_Q2 hlz') hqz

end CFSG.Quasithin.Kleidman.F204
