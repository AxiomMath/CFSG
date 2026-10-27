module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23Six5D1Aux
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23Six5D1Syl
public import CFSG.Quasithin.EmptyFaithful.S151bW3Five
public import CFSG.Quasithin.EmptyFaithful.T1515C6Gl

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Six5Data

variable {T M V : Subgroup G} {hV : IsElemAbelian 2 V} (d : Six5Data T M V hV)

theorem p_sub_aux
    (h19six : autOn (M ⊓ Subgroup.normalizer
      ((T ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G)) V = autOn M V)
    (hJR : thompsonJ T = thompsonJ (T ⊓ Subgroup.centralizer (V : Set G))) :
    ∃ Y' : Subgroup G, Y' ≤ M ⊓ g1_1516 d.Z₁ ∧ Y' ≤ Subgroup.normalizer (thompsonJ T : Set G) ∧
      IsPGroup 5 Y' ∧
      ((s1516 T d.Z₁ : Set G) * (Y' : Set G) = (Y' : Set G) * (s1516 T d.Z₁ : Set G)) ∧
      ⁅d.V₂, Y'⁆ = d.V₂ ∧ autI hV Y' = Subgroup.zpowers d.S.a₂ := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hZ₁V : d.Z₁ ≤ V := d.Z₁_le_V₁.trans d.V₁_le_V
  set R : Subgroup G := T ⊓ Subgroup.centralizer (V : Set G) with hR
  set NR : Subgroup G := M ⊓ Subgroup.normalizer (R : Set G) with hNR
  set L : Subgroup G := NR ⊓ Subgroup.centralizer (d.Z₁ : Set G) with hL
  set S : Subgroup G := T ⊓ Subgroup.centralizer (d.Z₁ : Set G) with hS
  let a : MulAut ↥V := d.S.a₂
  set O : Subgroup (MulAut ↥V) := Subgroup.zpowers a with hO
  set Z₁' : Subgroup ↥V := d.Z₁.subgroupOf V with hZ₁'
  have hNRN : NR ≤ Subgroup.normalizer (V : Set G) := inf_le_left.trans d.hMN
  have hLN : L ≤ Subgroup.normalizer (V : Set G) := inf_le_left.trans hNRN
  have hCV : Subgroup.centralizer (V : Set G) ≤ Subgroup.centralizer (d.Z₁ : Set G) :=
    Subgroup.centralizer_le hZ₁V
  have hmapZ : Z₁'.map V.subtype = d.Z₁ := Subgroup.map_subgroupOf_eq_of_le hZ₁V
  have hautL : autOn L V = autOn M V ⊓ fixingV (Z₁' : Set ↥V) := by
    have h1 : L = preOn NR V (fixingV (Z₁' : Set ↥V)) := by
      rw [hL, ← hmapZ]
      exact inf_centralizer_eq_preOn hNRN Z₁'
    rw [h1, autOn_preOn_inf, h19six, inf_comm]
  have ha₂fix : a ∈ fixingV (Z₁' : Set ↥V) := by
    intro z hz
    obtain ⟨w, hw, hwz⟩ := (d.mem_V₁_iff).1 (d.Z₁_le_V₁ (Subgroup.mem_subgroupOf.mp hz))
    have hwz' : w = z := Subtype.ext hwz
    have h1 : d.S.a₂ w = w := d.S.a₂_fix_W₁ hw
    rw [hwz'] at h1
    exact h1
  have hOC : O ≤ autOn M V ⊓ fixingV (Z₁' : Set ↥V) :=
    Subgroup.zpowers_le.mpr ⟨d.hA₂ d.S.a₂_mem, ha₂fix⟩
  have hOnorm : ∀ g ∈ autOn M V ⊓ fixingV (Z₁' : Set ↥V), ∀ o ∈ O, g * o * g⁻¹ ∈ O := by
    intro g hg o ho
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ho
    have hga : g * a * g⁻¹ ∈ O := by
      rw [← hautL] at hg
      obtain ⟨m, hmN, hmL, rfl⟩ := mem_autOn_iff_exists.mp hg
      have hmM : m ∈ M := hmL.1.1
      have hmV₁ : m ∈ Subgroup.normalizer (d.V₁ : Set G) :=
        d.centralizer_le_normalizer ⟨hmM, hmL.2⟩
      have hmV₂ : m ∈ Subgroup.normalizer (d.V₂ : Set G) := d.mem_normalizer_V₂ hmM hmV₁
      have hst : d.S.Stab₁ (convI hV ⟨m, hmN⟩) ∧ d.S.Stab₂ (convI hV ⟨m, hmN⟩) :=
        ⟨stab_of_mem_normalizer_map hmN hmV₁, stab_of_mem_normalizer_map hmN hmV₂⟩
      exact d.S.mem_zpowers_a₂_conj (fun w => IntMod.sq_eq_one w) d.hcard
        (d.hnorm _ (convI_mem_autI hV hmM hmN)) hst
    have : g * a ^ k * g⁻¹ = (g * a * g⁻¹) ^ k := by simp [conj_zpow]
    rw [this]
    exact O.zpow_mem hga k
  set P : Subgroup G := preOn L V O with hP
  have hPL : P ≤ L := preOn_le L V O
  have hautP : autOn P V = O := by
    rw [hP, autOn_preOn_inf, hautL]
    exact inf_eq_left.mpr hOC
  have hRP : R ≤ P := by
    intro r hr
    have hrL : r ∈ L := ⟨⟨d.hTM hr.1, Subgroup.le_normalizer hr⟩, hCV hr.2⟩
    refine mem_preOn.mpr ⟨hrL, hLN hrL, ?_⟩
    have : conjAct V ⟨r, hLN hrL⟩ = 1 := A4.conjAct_eq_one_iff.mpr hr.2
    rw [this]
    exact O.one_mem
  have hTR : T ≤ Subgroup.normalizer (R : Set G) :=
    le_normalizer_inf_centralizer' (fun y hy => Subgroup.le_normalizer hy) d.hTN
  have hSR : S ≤ Subgroup.normalizer (R : Set G) := inf_le_left.trans hTR
  have hRS : R ≤ S := fun x hx => ⟨hx.1, hCV hx.2⟩
  have hSL : S ≤ L := le_inf (le_inf (inf_le_left.trans d.hTM) hSR) inf_le_right
  have hPR : P ≤ Subgroup.normalizer (R : Set G) := fun x hx => (hPL hx).1.2
  have hLP : L ≤ Subgroup.normalizer (P : Set G) := by
    have key : ∀ x ∈ L, ∀ y ∈ P, x * y * x⁻¹ ∈ P := by
      intro x hx y hy
      have hxyL : x * y * x⁻¹ ∈ L := L.mul_mem (L.mul_mem hx (hPL hy)) (L.inv_mem hx)
      obtain ⟨_, _, hyO⟩ := mem_preOn.mp hy
      refine mem_preOn.mpr ⟨hxyL, hLN hxyL, ?_⟩
      have h1 : conjAct V ⟨x * y * x⁻¹, hLN hxyL⟩ =
          conjAct V ⟨x, hLN hx⟩ * conjAct V ⟨y, hLN (hPL hy)⟩ * (conjAct V ⟨x, hLN hx⟩)⁻¹ := by
        rw [← map_inv, ← map_mul, ← map_mul]
        congr 1
      rw [h1]
      have hxC : conjAct V ⟨x, hLN hx⟩ ∈ autOn M V ⊓ fixingV (Z₁' : Set ↥V) := by
        rw [← hautL]
        exact mem_autOn_of_mem (hLN hx) hx
      exact hOnorm _ hxC _ hyO
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · exact fun hy => key x hx y hy
    · intro hy
      have := key x⁻¹ (L.inv_mem hx) _ hy
      simpa [mul_assoc] using this
  have hSP : S ≤ Subgroup.normalizer (P : Set G) := fun x hx => hLP (hSL hx)
  have hS2 : IsPGroup 2 S := d.hsyl.2.1.to_le inf_le_left
  have hP_N : P ≤ Subgroup.normalizer (V : Set G) := hPL.trans hLN
  have hKP : (P ⊓ Subgroup.centralizer (V : Set G)).relIndex P = 5 := by
    have h5 : orderOf a = 5 := d.S.orderOf_a₂_five
    have := card_autOn_eq_relIndex hP_N
    rw [hautP, hO, Nat.card_zpowers, h5] at this
    exact this.symm
  have hMN_N : M ≤ Subgroup.normalizer (M ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) :=
    fun x hx => le_normalizer_inf_centralizer' (fun y hy => Subgroup.le_normalizer hy) d.hMN hx
  have hRM : IsSylowTwoOf R (M ⊓ Subgroup.centralizer (V : Set G)) := by
    have := A4.isSylowTwoOf_inf_normal d.hsyl inf_le_left hMN_N
    have hTM : T ⊓ (M ⊓ Subgroup.centralizer (V : Set G)) = R := by
      ext x
      simp only [hR, Subgroup.mem_inf]
      exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, d.hTM h.1, h.2⟩⟩
    rwa [hTM] at this
  have hRK : R ≤ P ⊓ Subgroup.centralizer (V : Set G) := le_inf hRP inf_le_right
  have hKM : P ⊓ Subgroup.centralizer (V : Set G) ≤ M ⊓ Subgroup.centralizer (V : Set G) :=
    inf_le_inf_right _ (hPL.trans (inf_le_left.trans inf_le_left))
  have hodd2 : ¬ 2 ∣ R.relIndex P := by
    have h1 : R.relIndex (P ⊓ Subgroup.centralizer (V : Set G)) *
        (P ⊓ Subgroup.centralizer (V : Set G)).relIndex P = R.relIndex P :=
      Subgroup.relIndex_mul_relIndex R _ P hRK inf_le_left
    have h2 : R.relIndex (P ⊓ Subgroup.centralizer (V : Set G)) *
        (P ⊓ Subgroup.centralizer (V : Set G)).relIndex (M ⊓ Subgroup.centralizer (V : Set G)) =
        R.relIndex (M ⊓ Subgroup.centralizer (V : Set G)) :=
      Subgroup.relIndex_mul_relIndex R _ _ hRK hKM
    have h3 : ¬ 2 ∣ R.relIndex (M ⊓ Subgroup.centralizer (V : Set G)) := hRM.2.2
    have h4 : ¬ 2 ∣ R.relIndex (P ⊓ Subgroup.centralizer (V : Set G)) := fun hd =>
      h3 (h2 ▸ dvd_mul_of_dvd_left hd _)
    rw [← h1, hKP]
    intro hd
    rcases (Nat.Prime.dvd_mul Nat.prime_two).mp hd with h5 | h5
    · exact h4 h5
    · omega
  obtain ⟨Y, hY, hSY⟩ := exists_invariant_R_sylow_of_prime 5 hRP hRS hSP hSR hPR hS2 hodd2
  have hYP : Y ≤ P := hY.1
  have hYL : Y ≤ L := hYP.trans hPL
  have hYM : Y ≤ M := hYL.trans (inf_le_left.trans inf_le_left)
  have hYK : Y ≤ M ⊓ g1_1516 d.Z₁ := fun x hx => ⟨hYM hx, (hYL.trans inf_le_right) hx⟩
  have hYa : autOn Y V ≤ O := by
    rw [← hautP]
    exact autOn_le_autOn V hYP
  have hYnot : autOn Y V ≠ ⊥ := by
    intro hbot
    have hYC : Y ≤ P ⊓ Subgroup.centralizer (V : Set G) := by
      intro y hy
      refine ⟨hYP hy, ?_⟩
      have hyN : y ∈ Subgroup.normalizer (V : Set G) := hP_N (hYP hy)
      have : conjAct V ⟨y, hyN⟩ ∈ autOn Y V := mem_autOn_of_mem hyN hy
      rw [hbot, Subgroup.mem_bot] at this
      exact A4.conjAct_eq_one_iff.mp this
    have h1 : Y.relIndex (P ⊓ Subgroup.centralizer (V : Set G)) *
        (P ⊓ Subgroup.centralizer (V : Set G)).relIndex P = Y.relIndex P :=
      Subgroup.relIndex_mul_relIndex Y _ P hYC inf_le_left
    have h2 : ¬ 5 ∣ Y.relIndex P := hY.2.2
    rw [hKP] at h1
    exact h2 (h1 ▸ dvd_mul_left 5 _)
  have hcard : Nat.card (autOn Y V) = 5 := by
    have h5 : orderOf a = 5 := d.S.orderOf_a₂_five
    have hd : Nat.card (autOn Y V) ∣ Nat.card O := Subgroup.card_dvd_of_le hYa
    rw [hO, Nat.card_zpowers, h5] at hd
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp hd with h1 | h1
    · exact absurd (Subgroup.card_eq_one.mp h1) hYnot
    · exact h1
  have hYO : autOn Y V = O := by
    have h5 : orderOf a = 5 := d.S.orderOf_a₂_five
    refine Subgroup.eq_of_le_of_card_ge hYa ?_
    rw [hcard, hO, Nat.card_zpowers, h5]
  refine ⟨Y, hYK, ?_, hY.2.1, ?_, d.comm_V₂_eq hYK hYO, hYO⟩
  ·
    have hYR : Y ≤ Subgroup.normalizer (R : Set G) := fun x hx => hPR (hYP hx)
    rw [hJR, thompsonJ_eq_thompsonJi_zero]
    exact fun x hx => normalizer_le_normalizer_thompsonJi151 R 0 (hYR hx)
  ·
    have hYnR : Y ≤ Subgroup.normalizer (R : Set G) := fun x hx => hPR (hYP hx)
    have hQ : ((R ⊔ Y : Subgroup G) : Set G) = (R : Set G) * (Y : Set G) :=
      Subgroup.coe_mul_of_right_le_normalizer_left R Y hYnR
    have hRsub : ∀ r ∈ R, ∀ y ∈ Y, y⁻¹ * r * y ∈ R := fun r hr y hy => by
      have := (Subgroup.mem_normalizer_iff.mp (hYnR (Y.inv_mem hy)) r).mp hr
      simpa using this
    ext x
    constructor
    · rintro ⟨s, hs, y, hy, rfl⟩
      have h1 : s * y * s⁻¹ ∈ R ⊔ Y :=
        (Subgroup.mem_normalizer_iff.mp (hSY hs) y).mp (Subgroup.mem_sup_right hy)
      rw [← SetLike.mem_coe, hQ] at h1
      obtain ⟨r', hr', y', hy', hry⟩ := h1
      have hry' : r' * y' = s * y * s⁻¹ := hry
      refine ⟨y', hy', y'⁻¹ * r' * y' * s, S.mul_mem (hRS (hRsub r' hr' y' hy')) hs, ?_⟩
      calc y' * (y'⁻¹ * r' * y' * s) = (r' * y') * s := by group
        _ = (s * y * s⁻¹) * s := by rw [hry']
        _ = s * y := by group
    · rintro ⟨y, hy, s, hs, rfl⟩
      have h1 : s⁻¹ * y * s ∈ R ⊔ Y := by
        have := (Subgroup.mem_normalizer_iff.mp (hSY (S.inv_mem hs)) y).mp
          (Subgroup.mem_sup_right hy)
        simpa using this
      rw [← SetLike.mem_coe, hQ] at h1
      obtain ⟨r', hr', y', hy', hry⟩ := h1
      have hry' : r' * y' = s⁻¹ * y * s := hry
      refine ⟨s * r', S.mul_mem hs (hRS hr'), y', hy', ?_⟩
      calc s * r' * y' = s * (r' * y') := by group
        _ = s * (s⁻¹ * y * s) := by rw [hry']
        _ = y * s := by group

end Six5Data

end CFSG.Quasithin
