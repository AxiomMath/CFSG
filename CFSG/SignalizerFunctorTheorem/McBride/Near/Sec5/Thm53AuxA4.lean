module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec5.Thm53AuxA3
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.SolQuot.Sol
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec5.Thm53AuxA2

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Near

namespace Thm53A

open CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

variable {Γ : Type u} [Group Γ] [Finite Γ]

@[expose] def CompInput (p : ℕ) (W : Subgroup Γ) : Prop :=
  (∀ J ∈ lcal (AChief.qimg (sol W) W), ∀ P : Subgroup (MulAut ↥J), Group.IsPerfect ↥P →
      P ≤ (MulAut.conj : ↥J →* MulAut ↥J).range) ∧
    (∀ J ∈ lcal (AChief.qimg (sol W) W), ∀ P : Subgroup (MulAut ↥J), IsPGroup p ↥P →
      Nat.card P ∣ p)

theorem qimg_perfRes {R Y : Subgroup Γ} (hY : Y ≤ AChief.nrm R) :
    AChief.qimg R (perfRes Y) = perfRes (AChief.qimg R Y) := by
  have h1 := CFSG.RankThreeCoreUniqueness.Helpers.finite_perfectResidual_map_eq
    (SolQuot.qres R Y hY) (SolQuot.qres_surjective hY)
  unfold perfRes
  rw [SolQuot.qimg_map_subtype hY]
  exact congrArg (fun S => S.map (AChief.qimg R Y).subtype) h1

section Transfer

variable {p : ℕ} {W : Subgroup Γ}

theorem perfRes_le_kOf_of_isSolvable_cen' (hp : p.Prime) (hnear : signalizerNearPSolvable p ↥W)
    (hin : CompInput p W) {a : Γ} (haW : a ∈ Subgroup.normalizer (W : Set Γ)) (hap : a ^ p = 1)
    (hcen : Group.IsSolvable ↥(W ⊓ Subgroup.centralizer {a})) : perfRes W ≤ kOf W := by
  have hR : Group.IsSolvable (sol W) := isSolvable_sol W
  have hWN : W ≤ AChief.nrm (sol W) := SolQuot.le_nrm_sol W
  have haN : a ∈ AChief.nrm (sol W) := SolQuot.normalizer_le_nrm_sol W haW
  have hzE : IsElemAbelian p (Subgroup.zpowers a) := isElemAbelian_zpowers hap
  have hzY : Subgroup.zpowers a ≤ Subgroup.normalizer (W : Set Γ) := Subgroup.zpowers_le.mpr haW
  have hzN : Subgroup.zpowers a ≤ AChief.nrm (sol W) := Subgroup.zpowers_le.mpr haN
  set a' : AChief.QG (sol W) := AChief.qmap (sol W) ⟨a, haN⟩ with ha'
  have hqz : AChief.qimg (sol W) (Subgroup.zpowers a) = Subgroup.zpowers a' :=
    SolQuot.qimg_zpowers haN
  have hsol : sol (AChief.qimg (sol W) W) = ⊥ := SolQuot.sol_qimg_sol W
  have hcop : Nat.Coprime p (Nat.card W) := hnear.1
  have hcopX : Nat.Coprime p (Nat.card (AChief.qimg (sol W) W)) :=
    hcop.coprime_dvd_right (Subgroup.card_dvd_of_surjective (SolQuot.qres_surjective hWN))
  have ha'X : a' ∈ Subgroup.normalizer ((AChief.qimg (sol W) W : Subgroup _) : Set _) := by
    have := AChief.qimg_le_normalizer (N := sol W) hzY
    rw [hqz] at this
    exact Subgroup.zpowers_le.mp this
  have ha'p : a' ^ p = 1 := by
    rw [ha', ← map_pow]
    have : (⟨a, haN⟩ : AChief.nrm (sol W)) ^ p = 1 := Subtype.ext (by simpa using hap)
    rw [this, map_one]
  have hcenY : AChief.qimg (sol W) (W ⊓ Subgroup.centralizer {a}) =
      AChief.qimg (sol W) W ⊓ Subgroup.centralizer {a'} := by
    rw [← Thm52Aux.centralizer_zpowers_eq,
      AChief.qimg_inf_centralizer hp hzE hzY hzN hWN hcop, hqz, Thm52Aux.centralizer_zpowers_eq]
  have hcen' : Group.IsSolvable ↥(AChief.qimg (sol W) W ⊓ Subgroup.centralizer {a'}) := by
    have h := Group.isSolvable_of_surjective (G := ↥(W ⊓ Subgroup.centralizer {a}))
      (SolQuot.qres_surjective (inf_le_left.trans hWN))
    rw [hcenY] at h
    exact h
  have key := perfRes_le_kOf_of_isSolvable_cen hp hsol hcopX ha'X ha'p hcen' hin.1
  rw [← qimg_perfRes hWN, SolQuot.kOf_qimg (isSolvable_sol W) hWN] at key
  have h2 := (SolQuot.qimg_le_qimg_iff ((perfRes_le W).trans hWN)
    ((kOf_le W).trans hWN)).mp key
  rwa [sup_eq_left.mpr (sol_le_kOf W)] at h2

theorem kOf_le_iSup_perfRes_cenIn_sup_sol (hp : p.Prime) (hnear : signalizerNearPSolvable p ↥W)
    (hin : CompInput p W) {B : Subgroup Γ} (hB : IsElemAbelian p B)
    (hBW : B ≤ Subgroup.normalizer (W : Set Γ)) (hcard : Nat.card B = p ^ 2) :
    kOf W ≤ (⨆ b ∈ B, ⨆ (_ : b ≠ 1), perfRes (cenIn (kOf W) {b})) ⊔ sol W := by
  set R := sol W with hRdef
  have hR : Group.IsSolvable R := isSolvable_sol W
  have hWN : W ≤ AChief.nrm R := SolQuot.le_nrm_sol W
  have hBN : B ≤ AChief.nrm R := hBW.trans (SolQuot.normalizer_le_nrm_sol W)
  have hKN : kOf W ≤ AChief.nrm R := (kOf_le W).trans hWN
  have hsol : sol (AChief.qimg R W) = ⊥ := SolQuot.sol_qimg_sol W
  have hcop : Nat.Coprime p (Nat.card W) := hnear.1
  have hBR : B ⊓ R = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).mpr fun x hx => ?_
    obtain ⟨hxB, hxR⟩ := Subgroup.mem_inf.mp hx
    have h1 : orderOf x ∣ p := orderOf_dvd_of_pow_eq_one (hB.2 x hxB)
    have h2 : orderOf x ∣ Nat.card W := Subgroup.orderOf_dvd_natCard W ((sol_le W) hxR)
    exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd (hcop.coprime_dvd_left h1) h2)
  have hBq : IsElemAbelian p (AChief.qimg R B) := AChief.isElemAbelian_qimg hB
  have hBqX : AChief.qimg R B ≤
      Subgroup.normalizer ((AChief.qimg R W : Subgroup _) : Set _) :=
    AChief.qimg_le_normalizer hBW
  have hinj : Function.Injective (SolQuot.qres R B hBN) := by
    rw [injective_iff_map_eq_one]
    intro y hy
    have hy' : y ∈ (SolQuot.qres R B hBN).ker := hy
    rw [SolQuot.ker_qres hBN, Subgroup.mem_subgroupOf] at hy'
    have : (y : Γ) ∈ B ⊓ R := Subgroup.mem_inf.mpr ⟨y.2, hy'⟩
    rw [hBR] at this
    exact Subtype.ext (Subgroup.mem_bot.mp this)
  have hcardq : Nat.card (AChief.qimg R B) = p ^ 2 := by
    rw [← hcard]
    exact (Nat.card_congr
      (Equiv.ofBijective _ ⟨hinj, SolQuot.qres_surjective hBN⟩)).symm
  have hRb := kOf_le_iSup_perfRes_cenIn hp hsol hBq hBqX hcardq hin.2
  have hUK : (⨆ b ∈ B, ⨆ (_ : b ≠ 1), perfRes (cenIn (kOf W) {b})) ≤ kOf W :=
    iSup₂_le fun b _ => iSup_le fun _ => (perfRes_le _).trans inf_le_left
  have hcopK : Nat.Coprime p (Nat.card (kOf W)) :=
    hcop.coprime_dvd_right (Subgroup.card_dvd_of_le (kOf_le W))
  have hqU : (⨆ b' ∈ AChief.qimg R B, ⨆ (_ : b' ≠ 1),
      perfRes (cenIn (kOf (AChief.qimg R W)) {b'})) ≤
      AChief.qimg R (⨆ b ∈ B, ⨆ (_ : b ≠ 1), perfRes (cenIn (kOf W) {b})) := by
    refine iSup₂_le fun b' hb' => iSup_le fun hb'1 => ?_
    obtain ⟨y, hyB, rfl⟩ := (AChief.mem_qimg_iff R B b').mp hb'
    have hy1 : (y : Γ) ≠ 1 := fun h => hb'1 (by rw [show y = 1 from Subtype.ext h, map_one])
    have hzE : IsElemAbelian p (Subgroup.zpowers (y : Γ)) := isElemAbelian_zpowers (hB.2 y hyB)
    have hyW : (y : Γ) ∈ Subgroup.normalizer (W : Set Γ) := hBW hyB
    have hzK : Subgroup.zpowers (y : Γ) ≤ Subgroup.normalizer (kOf W : Set Γ) :=
      (Subgroup.zpowers_le.mpr hyW).trans (Thm52Aux.normalizer_le_normalizer_kOf W)
    have hzN : Subgroup.zpowers (y : Γ) ≤ AChief.nrm R := Subgroup.zpowers_le.mpr y.2
    have hqz : AChief.qimg R (Subgroup.zpowers (y : Γ)) = Subgroup.zpowers (AChief.qmap R y) :=
      SolQuot.qimg_zpowers y.2
    have hcenK : AChief.qimg R (cenIn (kOf W) {(y : Γ)}) =
        kOf (AChief.qimg R W) ⊓ Subgroup.centralizer {AChief.qmap R y} := by
      unfold cenIn
      rw [← Thm52Aux.centralizer_zpowers_eq, SolQuot.kOf_qimg hR hWN,
        AChief.qimg_inf_centralizer hp hzE hzK hzN hKN hcopK, hqz,
        Thm52Aux.centralizer_zpowers_eq]
    have hgoal : perfRes (cenIn (kOf (AChief.qimg R W)) {AChief.qmap R y}) =
        perfRes (kOf (AChief.qimg R W) ⊓ Subgroup.centralizer {AChief.qmap R y}) := rfl
    have hcN : cenIn (kOf W) {(y : Γ)} ≤ AChief.nrm R :=
      (inf_le_left : cenIn (kOf W) {(y : Γ)} ≤ kOf W).trans hKN
    rw [hgoal, ← hcenK, ← qimg_perfRes hcN]
    exact SolQuot.qimg_mono (le_iSup₂_of_le (y : Γ) hyB (le_iSup_of_le hy1 le_rfl))
  have h1 := hRb.trans hqU
  rw [SolQuot.kOf_qimg hR hWN] at h1
  exact (SolQuot.qimg_le_qimg_iff hKN (hUK.trans hKN)).mp h1

end Transfer

end Thm53A

end CFSG.SignalizerFunctorTheorem.McBride.Near
