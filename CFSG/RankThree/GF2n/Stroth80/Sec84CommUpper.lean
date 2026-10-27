module

public import CFSG.RankThree.GF2n.Stroth80.Sec84TypeLemma
public import CFSG.RankThree.GF2n.Stroth80.Sec84PointRadicalBridge
public import CFSG.RankThree.GF2n.Stroth80.Sec84CommSecElem
public import CFSG.RankThree.GF2n.Stroth80.Sec86NormH
public import CFSG.RankThree.GF2n.Stroth80.Sec84CaseOnePrep

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalGroups.Symplectic
open scoped commutatorElement Matrix


theorem sec84CommUpper_of (h34 : Stroth34Statement) (h51 : Stroth51Statement)
    (h53 : Stroth53Statement) (hPts : Sec5NatPointsSpStatement) (hA : Sec8AExistsStatement) :
    Sec84CommUpperStatement := by
  classical
  intro G _ _ M Q Z B hc n t hs hsp4 Z0 hZ0 hN16 hNab hsq hSC hTI ν hνM hνL hνZ x hxX hxQ
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hQZ0 : Q ≤ Z0 := hc.Q_le_centre ht hZ0
  have hZ0card : Nat.card ↥Z0 = Nat.card Q * Nat.card Z :=
    sec86ZCard_of_51 h51 hA G M Q Z B hc n t hs Z0 hZ0
  have hN17 : Nat.card ↥(hc.CN t) = Nat.card Q * Nat.card Z ^ 17 := by
    rw [hN16, hZ0card]
    ring
  have hZLB : Z0 ≤ LB M Q B := sec8_Z0_le_LB h51 hA hc hs hZ0
  have hRM : Rt M (LB M Q B) t ≤ M := hc.Rt_le_M t
  have hNR : hc.CN t ≤ Rt M (LB M Q B) t := fun y hy => (Ctx.mem_CN.1 hy).1
  have hLR : LB M Q B ≤ Rt M (LB M Q B) t := le_Rt (M := M) (LB M Q B) ht
  have hQn : ∀ g ∈ M, ∀ y ∈ Q, g * y * g⁻¹ ∈ Q := fun g hg y hy =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hg) y).mp hy
  have hQLB : Q ≤ LB M Q B := sec39_Q_le_LB
  have hQCN : Q ≤ hc.CN t := sec8_Q_le_CN hc ht
  have hZ0CN : Z0 ≤ hc.CN t := sec8_Z0_le_CN hc hs hZ0
  obtain ⟨r, hr⟩ := hA G M Q Z B hc n t hs
  obtain ⟨K, fK, finK, φ, u, u', hpts⟩ := sec8_exists_pts hPts hc hs hsp4 hr
  haveI := hpts.charP
  obtain ⟨s, hs0, rfl⟩ : ∃ s ∈ Z0, x = ν * s * ν⁻¹ :=
    ⟨ν⁻¹ * x * ν, mem_conjSubgroup.mp hxX, by group⟩
  have hsQ : s ∉ Q := by
    intro h
    apply hxQ
    exact hQn ν hνM s h
  have hνi : ν⁻¹ ∈ Subgroup.normalizer (LB M Q B : Set G) := Subgroup.inv_mem _ hνL
  have hxL : ν * s * ν⁻¹ ∈ LB M Q B := (Subgroup.mem_normalizer_iff.mp hνL s).mp (hZLB hs0)
  have hxR : ν * s * ν⁻¹ ∈ Rt M (LB M Q B) t := hLR hxL
  have hxM : ν * s * ν⁻¹ ∈ M := hRM hxR
  have hxCN : ∀ c ∈ hc.CN t, (ν * s * ν⁻¹) * c * (ν * s * ν⁻¹)⁻¹ ∈ hc.CN t := fun c hc' =>
    hc.CN_conj_mem ht hxR hc'
  have hxQ' : ∀ q ∈ Q, (ν * s * ν⁻¹) * q * (ν * s * ν⁻¹)⁻¹ ∈ Q := hQn _ hxM
  have hNQ : ∀ c ∈ hc.CN t, ∀ q ∈ Q, c * q * c⁻¹ ∈ Q := fun c hc' q hq =>
    hQn c (hRM (hNR hc')) q hq
  have hNab' : ∀ a ∈ hc.CN t, ∀ b ∈ hc.CN t, ⁅a, b⁆ ∈ Q := fun a ha b hb =>
    hNab (Subgroup.commutator_mem_commutator ha hb)
  have hY := commSec_elem hNab' hQCN hxCN hxQ' hNQ
  have hYLN : ∀ y ∈ CommSec (hc.CN t) Q (ν * s * ν⁻¹), y ∈ LB M Q B ∧ y ∈ hc.CN t := by
    intro y hy
    obtain ⟨c, hc', q, hq, rfl⟩ := hY y hy
    have hcL : c ∈ Subgroup.normalizer (LB M Q B : Set G) :=
      sec8_CN_normalizes_LB h34 hc hs.toSec5 hc'
    refine ⟨(LB M Q B).mul_mem ?_ (hQLB hq), (hc.CN t).mul_mem ?_ (hQCN hq)⟩
    · have e : ⁅c, ν * s * ν⁻¹⁆ = (c * (ν * s * ν⁻¹) * c⁻¹) * (ν * s * ν⁻¹)⁻¹ := by
        simp only [commutatorElement_def]
      rw [e]
      exact (LB M Q B).mul_mem ((Subgroup.mem_normalizer_iff.mp hcL _).mp hxL)
        ((LB M Q B).inv_mem hxL)
    · have e : ⁅c, ν * s * ν⁻¹⁆ = c * ((ν * s * ν⁻¹) * c⁻¹ * (ν * s * ν⁻¹)⁻¹) := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact (hc.CN t).mul_mem hc' (hxCN _ ((hc.CN t).inv_mem hc'))
  set Y : Subgroup G := CommSec (hc.CN t) Q (ν * s * ν⁻¹) with hYdef
  set Y' : Subgroup G := conjSubgroup ν⁻¹ Y with hY'def
  have hY'mem : ∀ y, y ∈ Y' ↔ ν * y * ν⁻¹ ∈ Y := by
    intro y
    rw [hY'def, mem_conjSubgroup]
    simp
  have hY'LB : ∀ y ∈ Y', y ∈ LB M Q B := by
    intro y hy
    have h1 : ν * y * ν⁻¹ ∈ LB M Q B := (hYLN _ ((hY'mem y).mp hy)).1
    have h2 : ν⁻¹ * (ν * y * ν⁻¹) * ν⁻¹⁻¹ ∈ LB M Q B :=
      (Subgroup.mem_normalizer_iff.mp hνi _).mp h1
    have e : ν⁻¹ * (ν * y * ν⁻¹) * ν⁻¹⁻¹ = y := by group
    rwa [e] at h2
  have hY'R : Y' ≤ Rt M (LB M Q B) t := fun y hy => hLR (hY'LB y hy)
  have hQY' : ∀ q ∈ Q, q ∈ Y' := fun q hq =>
    (hY'mem q).mpr (Subgroup.mem_sup_right (hQn ν hνM q hq))
  have hshape : ∀ y ∈ Y', ∃ n' ∈ M, ∃ q' ∈ Q, y = ⁅n', s⁆ * q' := by
    intro y hy
    obtain ⟨c, hc', q, hq, hyc⟩ := hY _ ((hY'mem y).mp hy)
    have hq' : ν⁻¹ * q * ν ∈ Q := by simpa using hQn ν⁻¹ (M.inv_mem hνM) q hq
    refine ⟨ν⁻¹ * c * ν, M.mul_mem (M.mul_mem (M.inv_mem hνM) (hRM (hNR hc'))) hνM,
      ν⁻¹ * q * ν, hq', ?_⟩
    calc y = ν⁻¹ * (ν * y * ν⁻¹) * ν := by group
      _ = ν⁻¹ * (⁅c, ν * s * ν⁻¹⁆ * q) * ν := by rw [hyc]
      _ = ⁅ν⁻¹ * c * ν, s⁆ * (ν⁻¹ * q * ν) := by
        simp only [commutatorElement_def]
        group
  have hz : ∀ y ∈ Y', ∀ n' q' : G, q' ∈ Q → y = ⁅n', s⁆ * q' → n' * s * n'⁻¹ ∈ LB M Q B := by
    intro y hy n' q' hq' hyeq
    have h1 : ⁅n', s⁆ ∈ LB M Q B := by
      have e : ⁅n', s⁆ = y * q'⁻¹ := by
        rw [hyeq]; simp only [commutatorElement_def]; group
      rw [e]
      exact (LB M Q B).mul_mem (hY'LB y hy) ((LB M Q B).inv_mem (hQLB hq'))
    have e : n' * s * n'⁻¹ = ⁅n', s⁆ * s := by simp only [commutatorElement_def]; group
    rw [e]
    exact (LB M Q B).mul_mem h1 (hZLB hs0)
  have hzN : ∀ y n' q' : G, q' ∈ Q → y = ⁅n', s⁆ * q' →
      (y ∈ hc.CN t ↔ n' * s * n'⁻¹ ∈ hc.CN t) := by
    intro y n' q' hq' hyeq
    constructor
    · intro hyN
      have h1 : ⁅n', s⁆ ∈ hc.CN t := by
        have e : ⁅n', s⁆ = y * q'⁻¹ := by
          rw [hyeq]; simp only [commutatorElement_def]; group
        rw [e]
        exact (hc.CN t).mul_mem hyN ((hc.CN t).inv_mem (hQCN hq'))
      have e : n' * s * n'⁻¹ = ⁅n', s⁆ * s := by simp only [commutatorElement_def]; group
      rw [e]
      exact (hc.CN t).mul_mem h1 (hZ0CN hs0)
    · intro hzN
      have h1 : ⁅n', s⁆ ∈ hc.CN t := by
        have e : ⁅n', s⁆ = (n' * s * n'⁻¹) * s⁻¹ := by simp only [commutatorElement_def]
        rw [e]
        exact (hc.CN t).mul_mem hzN ((hc.CN t).inv_mem (hZ0CN hs0))
      rw [hyeq]
      exact (hc.CN t).mul_mem h1 (hQCN hq')
  have hK : ∀ y ∈ Y', y ∈ hc.CN t → y ∈ Q := by
    intro y hy hyN
    obtain ⟨n', hn'M, q', hq', hyeq⟩ := hshape y hy
    have hzL := hz y hy n' q' hq' hyeq
    have hzC : n' * s * n'⁻¹ ∈ hc.CN t := (hzN y n' q' hq' hyeq).mp hyN
    have hzZ : n' * s * n'⁻¹ ∈ Z0 := hSC s hs0 n' hn'M ⟨hzL, hzC⟩
    have hyZ : y ∈ Z0 := by
      have e : y = (n' * s * n'⁻¹) * s⁻¹ * q' := by
        rw [hyeq]; simp only [commutatorElement_def]
      rw [e]
      exact Z0.mul_mem (Z0.mul_mem hzZ (Z0.inv_mem hs0)) (hQZ0 hq')
    by_contra hyQ
    have hy0 : ν * y * ν⁻¹ ∈ Z0 := hSC y hyZ ν hνM (hYLN _ ((hY'mem y).mp hy))
    exact hνZ (hTI ν hνM y hyZ hyQ hy0)
  have hker1 : ∀ (a : G) (ha : a ∈ Rt M (LB M Q B) t), a ∈ hc.CN t → φ ⟨a, ha⟩ = 1 := by
    intro a ha h
    have : (⟨a, ha⟩ : ↥(Rt M (LB M Q B) t)) ∈ φ.ker := by
      rw [hpts.ker]
      exact Subgroup.mem_subgroupOf.mpr h
    exact this
  have hT : ∀ (y : G) (hy : y ∈ Y'), y ∉ Q → ¬ SpNonA2 (φ ⟨y, hY'R hy⟩) := by
    intro y hy hyQ
    obtain ⟨n', hn'M, q', hq', hyeq⟩ := hshape y hy
    have hzL := hz y hy n' q' hq' hyeq
    have hzC : n' * s * n'⁻¹ ∉ hc.CN t := fun h =>
      hyQ (hK y hy ((hzN y n' q' hq' hyeq).mpr h))
    have htyp := sec84_not_nonA2 h34 h51 h53 hPts hA hc hs hr hpts hN17 hZ0 hs0 hn'M hzL hzC
    have hEq : φ ⟨y, hY'R hy⟩ = φ ⟨n' * s * n'⁻¹, hLR hzL⟩ := by
      have e : (⟨y, hY'R hy⟩ : ↥(Rt M (LB M Q B) t)) =
          ⟨n' * s * n'⁻¹, hLR hzL⟩ * ⟨s, hZ0.le hs0⟩⁻¹ * ⟨q', hc.Q_le_Rt ht hq'⟩ := by
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        rw [hyeq]
        simp only [commutatorElement_def]
      rw [e, map_mul, map_mul, map_inv, hker1 s _ (hZ0CN hs0), hker1 q' _ (hQCN hq')]
      simp
    rw [hEq]
    exact htyp
  let ρ : ↥Y' →* GL (Fin 4 ⊕ Fin 4) K := φ.comp (Subgroup.inclusion hY'R)
  have hρle : ρ.range ≤ LspGL 4 K u := by
    rintro _ ⟨⟨y, hy⟩, rfl⟩
    rw [← hpts.hL]
    exact Subgroup.mem_map_of_mem φ (Subgroup.mem_subgroupOf.mpr (hY'LB y hy))
  have hρno : ∀ A ∈ ρ.range, ¬ SpNonA2 A := by
    rintro _ ⟨⟨y, hy⟩, rfl⟩
    by_cases hyQ : y ∈ Q
    · have h1 : φ ⟨y, hY'R hy⟩ = 1 := hker1 y _ (hQCN hyQ)
      show ¬ SpNonA2 (φ ⟨y, hY'R hy⟩)
      rw [h1]
      rintro ⟨w, hw⟩
      apply hw
      simp [spForm_self]
    · exact hT y hy hyQ
  have hcardρ : Nat.card ↥ρ.range ≤ Nat.card K ^ (4 - 1) :=
    card_le_of_no_nonA2 hpts.two_le hpts.u_ne_zero ρ.range hρle hρno
  have hkerQ : ∀ k : ↥ρ.ker, ((k.1 : ↥Y') : G) ∈ Q := by
    intro k
    have h1 : ρ k.1 = 1 := k.2
    have h2 : (⟨((k.1 : ↥Y') : G), hY'R k.1.2⟩ : ↥(Rt M (LB M Q B) t)) ∈ φ.ker := h1
    rw [hpts.ker] at h2
    exact hK _ k.1.2 (Subgroup.mem_subgroupOf.mp h2)
  have hker : Nat.card ↥ρ.ker ≤ Nat.card Q := by
    refine Nat.card_le_card_of_injective
      (fun k : ↥ρ.ker => (⟨((k.1 : ↥Y') : G), hkerQ k⟩ : ↥Q)) ?_
    intro a b hab
    have h := congrArg Subtype.val hab
    exact Subtype.ext (Subtype.ext h)
  have hcardY' : Nat.card ↥ρ.ker * Nat.card ↥ρ.range = Nat.card ↥Y' :=
    Subgroup.card_ker_mul_card_range ρ
  have hcardconj : Nat.card ↥Y' = Nat.card ↥Y := CFSG.RankThree.GF2n.card_conjSubgroup ν⁻¹ Y
  calc Nat.card ↥Y = Nat.card ↥Y' := hcardconj.symm
    _ = Nat.card ↥ρ.ker * Nat.card ↥ρ.range := hcardY'.symm
    _ ≤ Nat.card Q * Nat.card K ^ (4 - 1) := Nat.mul_le_mul hker hcardρ
    _ = Nat.card Q * Nat.card Z ^ 3 := by rw [hpts.card]

end CFSG.RankThree.GF2n.Stroth80
