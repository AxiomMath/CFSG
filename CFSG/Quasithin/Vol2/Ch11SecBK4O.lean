module

public import CFSG.Quasithin.Vol2.Ch11SecBK4N
public import CFSG.Quasithin.Vol2.Ch11SecBK4L

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Quasithin CFSG.Quasithin.JonesParshall
open CFSG.Open (quasithinG2 IsElemAbelian)
open scoped IsMulCommutative

namespace BK4

variable {G : Type} [Group G] {L V : Subgroup G} {n : ℕ} {K : Type} [Field K]

theorem oddCodim_g2 [Finite G] [IsMulCommutative ↥V] [Finite K] [CharP K 2]
    (hV : IsElemAbelian 2 V) (hLV : L ≤ Subgroup.normalizer (V : Set G)) (hVL : ⁅V, L⁆ = V)
    (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n)
    {π : ↥⁅quasithinG2 K, quasithinG2 K⁆ →* ↥(autOn L V)} {f : ↥V → (Ix3 → K)}
    (hf : KGNat.IsCoord (G2Q8.lmG K) (autOn L V)
      ((Subgroup.centralizer (L : Set G)).subgroupOf V) π f) {x : G}
    (hxV : x ∈ Subgroup.normalizer (V : Set G)) (hxL : x ∈ Subgroup.normalizer (L : Set G))
    (hx1 : x ∉ Subgroup.centralizer (V : Set G)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hxp : x ^ p ∈ Subgroup.centralizer (V : Set G))
    (hdiag : p ∣ 2 ^ n - 1 → x ∈ L ⊔ Subgroup.centralizer (V : Set G)) :
    2 * (2 * n) ≤ rkIdx (fixV (Subgroup.zpowers (SecA.conjV V x hxV))) := by
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  obtain ⟨c₀, hc0, hc1⟩ := G2Q8.exists_ne_zero_ne_one_of_card hn hK
  obtain ⟨c, γ, σ, hc, hact⟩ := G2Q8.exists_smul_frob_conjV
    (X := Subgroup.normalizer (L : Set G)) hf hc0 hc1 hK hn inf_le_left (e := x) ⟨hxL, hxV⟩
  let T' : (Ix3 → K) →+ (Ix3 → K) :=
    { toFun := fun y => c • g2Act γ (G2Q8.frobQ (σ : K →+* K) y)
      map_zero' := by
        have : G2Q8.frobQ (σ : K →+* K) 0 = 0 := funext fun j => map_zero σ
        rw [this, map_zero, smul_zero]
      map_add' := fun y y' => by
        have : G2Q8.frobQ (σ : K →+* K) (y + y') =
            G2Q8.frobQ (σ : K →+* K) y + G2Q8.frobQ (σ : K →+* K) y' :=
          funext fun j => map_add σ (y j) (y' j)
        simp only [this, map_add, smul_add] }
  have hT : ∀ w, f (SecA.conjV V x hxV w) = T' (f w) := hact
  have hsemi : ∀ (a : K) (y : Ix3 → K), T' (a • y) = (σ : K →+* K) a • T' y := by
    intro a y
    show c • g2Act γ (G2Q8.frobQ (σ : K →+* K) (a • y)) =
      (σ : K →+* K) a • (c • g2Act γ (G2Q8.frobQ (σ : K →+* K) y))
    rw [G2Q8.frobQ_smul, G2Q8.g2Act_smul, smul_comm]
  have hTp := iterate_eq_of_pow hf hxV hT hxp
  obtain ⟨y₀, hy₀⟩ : ∃ y, T' y ≠ y := by
    by_contra h
    simp only [not_exists, ne_eq, not_not] at h
    exact hx1 (mem_centralizer_of_g2 hLV hVL hf hc0 hc1 hxV hxL fun v => by rw [hT, h])
  have hy₀0 : y₀ ≠ 0 := by
    rintro rfl
    exact hy₀ (map_zero T')
  have hM := card_fun_six hK
  have hbound : Nat.card {z : Ix3 → K // T' z = z} ≤ 2 ^ (2 * n) := by
    by_cases hσ1 : ∃ θ, σ θ ≠ θ
    · have h1 := card_fix_cube_of_odd T' (σ : K →+* K) hsemi hpodd hTp hy₀0 hσ1
      rw [hM, show 6 * n = 2 * n * 3 by ring, pow_mul] at h1
      exact (Nat.pow_le_pow_iff_left (by norm_num)).mp h1
    simp only [not_exists, ne_eq, not_not] at hσ1
    have hT' : ∀ y, T' y = c • g2Act γ y := fun y => by
      show c • g2Act γ (G2Q8.frobQ (σ : K →+* K) y) = _
      congr 2
      exact funext fun j => hσ1 (y j)
    have hiter : ∀ (k : ℕ) (y : Ix3 → K), T'^[k] y = c ^ k • g2Act (γ ^ k) y := by
      intro k
      induction k with
      | zero => intro y; simp
      | succ k ih =>
        intro y
        rw [Function.iterate_succ_apply', ih, hT', G2Q8.g2Act_smul, smul_smul,
          ← G2Q8.g2Act_mul_apply, pow_succ', pow_succ']
    have hγp : ∀ y, g2Act (γ ^ p) y = (c ^ p)⁻¹ • y := by
      intro y
      have h1 := hiter p y
      rw [hTp] at h1
      have hcp : c ^ p ≠ 0 := pow_ne_zero p hc
      calc g2Act (γ ^ p) y = (c ^ p)⁻¹ • (c ^ p • g2Act (γ ^ p) y) := by
            rw [smul_smul, inv_mul_cancel₀ hcp, one_smul]
        _ = (c ^ p)⁻¹ • y := by rw [← h1]
    have hcp : (c ^ p)⁻¹ = 1 := G2Q8.scalar_eq_one hγp
    have hcp' : c ^ p = 1 := by
      have := congrArg (·⁻¹) hcp
      simpa using this
    have hγp1 : γ ^ p = 1 := G2Q8.cayley_eq_one fun y => by rw [hγp, hcp, one_smul]
    have hc1' : c = 1 := by
      by_contra hne
      have hpq := dvd_card_sub_one hp hne hcp'
      rw [hK] at hpq
      obtain ⟨a, ha⟩ := (G2Q8.rhoG_bijective hf hc0 hc1).2
        ⟨SecA.conjV V x hxV, conjV_mem_autOn_of_mem_sup hLV (hdiag hpq) hxV⟩
      have hTa : ∀ y, T' y = g2Act a y := by
        intro y
        obtain ⟨w, rfl⟩ := hf.surj y
        rw [← hT, ← G2Q8.IsCoord.actG hf hc0 hc1, ha]
      have hγa : ∀ y, g2Act γ y = c⁻¹ • g2Act a y := fun y => by
        rw [← hTa, hT', smul_smul, inv_mul_cancel₀ hc, one_smul]
      have hsc : ∀ y, g2Act (a⁻¹ * γ) y = c⁻¹ • y := fun y => by
        rw [G2Q8.g2Act_mul_apply, hγa, G2Q8.g2Act_smul, G2Q8.g2Act_inv_apply]
      have := G2Q8.scalar_eq_one hsc
      exact hne (inv_eq_one.mp this)
    have hγ1 : γ ≠ 1 := by
      rintro rfl
      exact hy₀ (by rw [hT', hc1', one_smul, map_one]; rfl)
    have h1 := card_fixQ_le_of_odd hpodd hγp1 hγ1
    rw [hK, ← pow_mul, mul_comm] at h1
    refine le_trans (le_of_eq (Nat.card_congr (Equiv.subtypeEquivRight fun z => ?_))) h1
    rw [G2Q8.mem_fixQ, hT', hc1', one_smul]
  have hC : ∀ w ∈ fixV (Subgroup.zpowers (SecA.conjV V x hxV)), T' (f w) = f w :=
    fun w hw => by rw [← hT, mem_fixV_zpowers.mp hw]
  have h3 := le_rkIdx_add hV hf hC hM hbound
  omega

end BK4

theorem factOddCodim_holds : FactOddCodim := by
  intro G _ _ L V X n m hV hn hLV hVL hnat hm _ hXN hdiag x hx p hp hp2 hxp hx1
  obtain ⟨hc, hnat'⟩ := hnat
  have hG2 : SecA.FactG2DerivedOrder := KGNat.factG2DerivedOrder_holds
  have hxV := hx.2
  have hxL := hXN hx
  have hdiag' : p ∣ 2 ^ n - 1 → x ∈ L ⊔ Subgroup.centralizer (V : Set G) :=
    fun hpq => hdiag x hx p hp hpq hxp
  rw [BK4.mQuot_inf_centralizer hxV]
  rcases hnat' with ⟨K, _, _, hK, π, hπ⟩ | ⟨K, _, _, hK, π, hπ⟩ | ⟨K, _, _, hK, π, hπ⟩
  · have : CharP K 2 := KGNat.charP_two_of_card (by omega) hK
    obtain ⟨f, hf⟩ := KGNat.exists_isCoord (KGNat.linModelNat _) hπ
    have hmn : m = n := by
      rcases hm with ⟨hk, -⟩ | ⟨-, hmn⟩
      · exact (SecA.kind_not_SL3_G2 hG2 hn (BK4.kindSL3_of_isCoord hK hf) hk).elim
      · exact hmn
    subst hmn
    exact BK4.oddCodim_sl3 hV hLV hVL hK hf hxV hxL hx1 hp hp2 hxp hdiag'
  · have : CharP K 2 := KGNat.charP_two_of_card (by omega) hK
    obtain ⟨f, hf⟩ := KGNat.exists_isCoord (KGNat.linModelNat _) hπ
    have hmn : m = n := by
      rcases hm with ⟨hk, -⟩ | ⟨-, hmn⟩
      · exact (SecA.kind_not_Sp4_G2 hG2 hn (BK4.kindSp4_of_isCoord hK hf) hk).elim
      · exact hmn
    subst hmn
    exact BK4.oddCodim_sp4 hV hLV hVL hK hf hxV hxL hx1 hp hp2 hxp
  · have : CharP K 2 := KGNat.charP_two_of_card (by omega) hK
    obtain ⟨f, hf⟩ := KGNat.exists_isCoord (G2Q8.lmG K) hπ
    have hmn : m = 2 * n := by
      rcases hm with ⟨-, hmn⟩ | ⟨hk, -⟩
      · exact hmn
      · exact (hk (BK4.kindG2_of_isCoord hn hK hf)).elim
    subst hmn
    exact BK4.oddCodim_g2 hV hLV hVL hn hK hf hxV hxL hx1 hp hp2 hxp hdiag'

end CFSG.Quasithin.Vol2.Ch11.SecB
