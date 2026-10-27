module

public import CFSG.Quasithin.EmptyFaithful.S152Defs
public import CFSG.Quasithin.EmptyFaithful.S151Basic
public import CFSG.Quasithin.EmptyFaithful.S1417Glue
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G]

namespace S152N

theorem mem_Qset_autI {V M B : Subgroup G} (hV : IsElemAbelian 2 V)
    (hMN : M ≤ Subgroup.normalizer (V : Set G)) (hBM : B ≤ M) (hBe : IsElemAbelian 2 B)
    (hne : ⁅V, B⁆ ≠ ⊥)
    (hcount : Nat.card B ^ 2 * Nat.card ↥(V ⊓ Subgroup.centralizer (B : Set G)) =
      Nat.card ↥(B ⊓ Subgroup.centralizer (V : Set G)) ^ 2 * Nat.card V)
    (hquad : ⁅⁅V, B⁆, B⁆ = ⊥) : autI hV B ∈ Qset (autI hV M) := by
  have hBN : B ≤ Subgroup.normalizer (V : Set G) := hBM.trans hMN
  have hA2 : IsA2 (autI hV M) (autI hV B) :=
    isA2_autI hV hMN hBM hBe (fun h => hne (commutator_eq_bot_of_le_centralizer h))
  refine ⟨⟨hA2, ?_⟩, ?_⟩
  ·
    have hi := card_autI_mul_card_inf hV hBN
    have hii := card_fixV_autI hV hBN
    have hVcard : Nat.card (fixV (autI hV B)) * (fixV (autI hV B)).index = Nat.card V :=
      Subgroup.card_mul_index _
    rw [hii] at hVcard
    have hposB : 0 < Nat.card ↥(B ⊓ Subgroup.centralizer (V : Set G)) := Nat.card_pos
    have hposC : 0 < Nat.card ↥(V ⊓ Subgroup.centralizer (B : Set G)) := Nat.card_pos
    have hidx : (fixV (autI hV B)).index = Nat.card (autI hV B) ^ 2 := by
      have h1 : Nat.card B ^ 2 * Nat.card ↥(V ⊓ Subgroup.centralizer (B : Set G)) =
          Nat.card ↥(B ⊓ Subgroup.centralizer (V : Set G)) ^ 2 *
            (Nat.card ↥(V ⊓ Subgroup.centralizer (B : Set G)) * (fixV (autI hV B)).index) := by
        rw [hVcard]
        exact hcount
      rw [← hi] at h1
      have hpos2 : 0 < Nat.card ↥(B ⊓ Subgroup.centralizer (V : Set G)) ^ 2 *
          Nat.card ↥(V ⊓ Subgroup.centralizer (B : Set G)) := by positivity
      have h3 : (Nat.card ↥(B ⊓ Subgroup.centralizer (V : Set G)) ^ 2 *
            Nat.card ↥(V ⊓ Subgroup.centralizer (B : Set G))) * Nat.card (autI hV B) ^ 2 =
          (Nat.card ↥(B ⊓ Subgroup.centralizer (V : Set G)) ^ 2 *
            Nat.card ↥(V ⊓ Subgroup.centralizer (B : Set G))) * (fixV (autI hV B)).index := by
        calc _ = (Nat.card (autI hV B) *
                Nat.card ↥(B ⊓ Subgroup.centralizer (V : Set G))) ^ 2 *
              Nat.card ↥(V ⊓ Subgroup.centralizer (B : Set G)) := by ring
          _ = _ := h1
          _ = _ := by ring
      exact (Nat.eq_of_mul_eq_mul_left hpos2 h3).symm
    have hpos : 0 < rk (autI hV B) := hA2.rk_pos
    have hrk : rkIdx (fixV (autI hV B)) = 2 * rk (autI hV B) := by
      unfold rkIdx rk
      rw [hidx, padicValNat.pow]
    show rAV (autI hV B) ≤ 2
    unfold rAV
    rw [hrk]
    have : (rk (autI hV B) : ℚ) ≠ 0 := by exact_mod_cast hpos.ne'
    push_cast
    rw [mul_div_assoc, div_self this]
    norm_num
  ·
    rw [← isQuadratic_iff_commSeries_two]
    intro w hw
    have hw' : w.val ∈ ⁅V, B⁆ := by
      rw [S1417.commutator_eq_map_commV hV hBN]
      exact ⟨w, hw, rfl⟩
    have hcent : w.val ∈ Subgroup.centralizer (B : Set G) := by
      have h1 : B ≤ Subgroup.centralizer ((⁅V, B⁆ : Subgroup G) : Set G) :=
        le_centralizer_of_commutator_eq_bot hquad
      exact Subgroup.mem_centralizer_iff.mpr fun b hb => (Subgroup.mem_centralizer_iff.mp
        (h1 hb) w.val hw').symm
    exact (mem_fixV_autI hV hBN w).mpr hcent

theorem mem_QsetOn_of_counts {V M B : Subgroup G} (hV : IsElemAbelian 2 V)
    (hMN : M ≤ Subgroup.normalizer (V : Set G)) (hBM : B ≤ M) (hBe : IsElemAbelian 2 B)
    (hne : ⁅V, B⁆ ≠ ⊥)
    (hcount : Nat.card B ^ 2 * Nat.card ↥(V ⊓ Subgroup.centralizer (B : Set G)) =
      Nat.card ↥(B ⊓ Subgroup.centralizer (V : Set G)) ^ 2 * Nat.card V)
    (hquad : ⁅⁅V, B⁆, B⁆ = ⊥) : autOn B V ∈ QsetOn M V := by
  unfold QsetOn
  rw [dite_eq_left hV]
  exact mem_Qset_autI hV hMN hBM hBe hne hcount hquad

omit [Finite G] in
theorem commutator_preOn_autOn {V T B : Subgroup G} (hV : IsElemAbelian 2 V)
    (hT : T ≤ Subgroup.normalizer (V : Set G)) (hBT : B ≤ T) :
    ⁅V, preOn T V (autOn B V)⁆ = ⁅V, B⁆ := by
  have h1 : autI hV (preOn T V (autOn B V)) = autOn B V := autOn_preOn (A4.autOn_mono hBT)
  rw [S1417.commutator_eq_map_commV hV ((preOn_le T V _).trans hT),
    S1417.commutator_eq_map_commV hV (hBT.trans hT)]
  exact congrArg (fun X : Subgroup (IntMod V hV) => X.map (S1417.inclMod hV)) (by rw [h1]; rfl)

end S152N

end CFSG.Quasithin
