module

public import CFSG.Quasithin.EmptyFaithful.T1515C6Set
public import CFSG.Quasithin.EmptyFaithful.T1515C6P

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped Pointwise commutatorElement

variable {G : Type} [Group G]

namespace Six3Data

variable {V M T : Subgroup G} {hVe : IsElemAbelian 2 V} (d : Six3Data V M T hVe)
include d

theorem p_sub [Finite G]
    (h19six : autOn (M ⊓ Subgroup.normalizer
      ((T ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G)) V = autOn M V)
    (hJR : thompsonJ T = thompsonJ (T ⊓ Subgroup.centralizer (V : Set G))) :
    ∃ p : ℕ, (p = 3 ∨ p = 5) ∧ ∃ Y' : Subgroup G,
      Y' ≤ M ⊓ g1_1516 d.Z₁ ∧ Y' ≤ Subgroup.normalizer (thompsonJ T : Set G) ∧ IsPGroup p Y' ∧
        ((s1516 T d.Z₁ : Set G) * (Y' : Set G) = (Y' : Set G) * (s1516 T d.Z₁ : Set G)) ∧
        ⁅d.V₂, Y'⁆ = d.V₂ := by
  let _ : CommGroup ↥V := commGroupOfElemAbelian hVe
  obtain ⟨c, t, hcA, htA, hc3, hc3', ht2, htc, hnf, hodd, hfix⟩ := d.ctx.rot₂
  set R : Subgroup G := T ⊓ Subgroup.centralizer (V : Set G) with hR
  set NR : Subgroup G := M ⊓ Subgroup.normalizer (R : Set G) with hNR
  set L : Subgroup G := NR ⊓ Subgroup.centralizer (d.Z₁ : Set G) with hL
  set S : Subgroup G := T ⊓ Subgroup.centralizer (d.Z₁ : Set G) with hS
  set O : Subgroup (MulAut V) := Subgroup.zpowers c with hO
  have hNRN : NR ≤ Subgroup.normalizer (V : Set G) := inf_le_left.trans d.hMN
  have hLN : L ≤ Subgroup.normalizer (V : Set G) := inf_le_left.trans hNRN
  have hCV : Subgroup.centralizer (V : Set G) ≤ Subgroup.centralizer (d.Z₁ : Set G) :=
    Subgroup.centralizer_le d.Z₁_le_V
  have hautL : autOn L V = @sixCbar ↥V _ (autOn M V) d.Z₁' := by
    rw [hL, show Subgroup.centralizer (d.Z₁ : Set G) =
      Subgroup.centralizer ((d.Z₁'.map V.subtype : Subgroup G) : Set G) from rfl,
      inf_centralizer_eq_preOn hNRN d.Z₁', autOn_preOn_inf, h19six, inf_comm]
    rfl
  have hOC : O ≤ @sixCbar ↥V _ (autOn M V) d.Z₁' :=
    Subgroup.zpowers_le.mpr (SixGens.A₂_le_Cbar d.ctx hcA)
  have hOnorm : ∀ g ∈ @sixCbar ↥V _ (autOn M V) d.Z₁', ∀ o ∈ O, g * o * g⁻¹ ∈ O := by
    intro g hg o ho
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ho
    have hgc : g * c * g⁻¹ ∈ O := by
      have hCb : g * c * g⁻¹ ∈ @sixCbar ↥V _ (autOn M V) d.Z₁' :=
        (sixCbar (autOn M V) d.Z₁').mul_mem ((sixCbar (autOn M V) d.Z₁').mul_mem hg (hOC
          (Subgroup.mem_zpowers c))) ((sixCbar (autOn M V) d.Z₁').inv_mem hg)
      have h3 : (g * c * g⁻¹) ^ 3 = 1 := by
        rw [conj_pow, hc3']
        group
      have hodd3 : Odd (orderOf (g * c * g⁻¹)) :=
        Odd.of_dvd_nat (by decide : Odd 3) (orderOf_dvd_of_pow_eq_one h3)
      exact SixGens.odd_mem d.ctx d.gens hodd hCb hodd3
    have : g * c ^ k * g⁻¹ = (g * c * g⁻¹) ^ k := by simp [conj_zpow]
    rw [this]
    exact O.zpow_mem hgc k
  set P : Subgroup G := preOn L V O with hP
  have hPL : P ≤ L := preOn_le L V O
  have hautP : autOn P V = O := by
    rw [hP, autOn_preOn_inf, hautL]
    exact inf_eq_left.mpr hOC
  have hRT : R ≤ T := inf_le_left
  have hRP : R ≤ P := by
    intro r hr
    have hrM : r ∈ M := d.hsyl.1 hr.1
    have hrL : r ∈ L := ⟨⟨hrM, Subgroup.le_normalizer hr⟩, hCV hr.2⟩
    refine mem_preOn.mpr ⟨hrL, hLN hrL, ?_⟩
    have : conjAct V ⟨r, hLN hrL⟩ = 1 := A4.conjAct_eq_one_iff.mpr hr.2
    rw [this]
    exact O.one_mem
  have hTR : T ≤ Subgroup.normalizer (R : Set G) :=
    le_normalizer_inf_centralizer' (fun y hy => Subgroup.le_normalizer hy) d.hTN
  have hSR : S ≤ Subgroup.normalizer (R : Set G) := inf_le_left.trans hTR
  have hRS : R ≤ S := fun x hx => ⟨hx.1, hCV hx.2⟩
  have hSL : S ≤ L := le_inf (le_inf (inf_le_left.trans d.hsyl.1) hSR) inf_le_right
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
      have hxC : conjAct V ⟨x, hLN hx⟩ ∈ @sixCbar ↥V _ (autOn M V) d.Z₁' := by
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
  have hKP : (P ⊓ Subgroup.centralizer (V : Set G)).relIndex P = 3 := by
    have := card_autOn_eq_relIndex hP_N
    rw [hautP, hO, Nat.card_zpowers, hc3] at this
    exact this.symm
  have hRM : IsSylowTwoOf R (M ⊓ Subgroup.centralizer (V : Set G)) := by
    have := A4.isSylowTwoOf_inf_normal d.hsyl inf_le_left d.hMN_N
    have hTM : T ⊓ (M ⊓ Subgroup.centralizer (V : Set G)) = R := by
      ext x
      simp only [hR, Subgroup.mem_inf]
      exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, d.hsyl.1 h.1, h.2⟩⟩
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
  obtain ⟨Y, hY, hSY⟩ := exists_invariant_R_sylow hRP hRS hSP hSR hPR hS2 hodd2
  have hYP : Y ≤ P := hY.1
  have hYL : Y ≤ L := hYP.trans hPL
  have hYM : Y ≤ M := hYL.trans (inf_le_left.trans inf_le_left)
  refine ⟨3, Or.inl rfl, Y, fun x hx => ⟨hYM hx, (hYL.trans inf_le_right) hx⟩, ?_, hY.2.1, ?_, ?_⟩
  ·
    have hYR : Y ≤ Subgroup.normalizer (R : Set G) := fun x hx => hPR (hYP hx)
    rw [hJR, thompsonJ_eq_thompsonJi_zero]
    exact fun x hx => normalizer_le_normalizer_thompsonJi151 R 0 (hYR hx)
  ·
    have hYnR : Y ≤ Subgroup.normalizer (R : Set G) := fun x hx => hPR (hYP hx)
    have hQ : ((R ⊔ Y : Subgroup G) : Set G) = (R : Set G) * (Y : Set G) :=
      Subgroup.coe_mul_of_right_le_normalizer_left R Y hYnR
    have hRsub : ∀ r ∈ R, ∀ y ∈ Y, y⁻¹ * r * y ∈ R := fun r hr y hy => by
      have := hYnR (Y.inv_mem hy)
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
        have := (Subgroup.mem_normalizer_iff.mp (hSY (S.inv_mem hs)) y).mp (Subgroup.mem_sup_right hy)
        simpa using this
      rw [← SetLike.mem_coe, hQ] at h1
      obtain ⟨r', hr', y', hy', hry⟩ := h1
      have hry' : r' * y' = s⁻¹ * y * s := hry
      refine ⟨s * r', S.mul_mem hs (hRS hr'), y', hy', ?_⟩
      calc s * r' * y' = s * (r' * y') := by group
        _ = s * (s⁻¹ * y * s) := by rw [hry']
        _ = y * s := by group
  ·
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
      have h2 : ¬ 3 ∣ Y.relIndex P := hY.2.2
      rw [hKP] at h1
      exact h2 (h1 ▸ dvd_mul_left 3 _)
    have hcard : Nat.card (autOn Y V) = 3 := by
      have hd : Nat.card (autOn Y V) ∣ Nat.card O := Subgroup.card_dvd_of_le hYa
      rw [hO, Nat.card_zpowers, hc3] at hd
      rcases (Nat.dvd_prime Nat.prime_three).mp hd with h1 | h1
      · exact absurd (Subgroup.card_eq_one.mp h1) hYnot
      · exact h1
    have hYO : autOn Y V = O := by
      refine Subgroup.eq_of_le_of_card_ge hYa ?_
      rw [hcard, hO, Nat.card_zpowers, hc3]
    exact d.commutator_V₂_eq hYM hcA hfix (by rw [hYO])

end Six3Data

end CFSG.Quasithin
