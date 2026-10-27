module

import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ThreeLStarClosure
import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.K35Lift
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102Basic
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229Diag2
import CFSG.LocalAnalysis.UniquenessCase.UC22P20d
import CFSG.LocalAnalysis.UniquenessCase.UC6Dict
public import CFSG.LocalAnalysis.UniquenessCase.UC22P21c
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22l

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC6
open CFSG.LocalAnalysis.AGL81TheoremCD.Section15.K35
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem uc22r3t_uniqueFourConj_mul (a b : G) (Y : Subgroup G) :
    uniqueFourConj a (uniqueFourConj b Y) = uniqueFourConj (b * a) Y := by
  ext x
  rw [mem_uniqueFourConj_iff, mem_uniqueFourConj_iff, mem_uniqueFourConj_iff]
  rw [show b * (a * x * a⁻¹) * b⁻¹ = (b * a) * x * (b * a)⁻¹ by group]

private theorem uc22r3t_orbit_eq (K : Subgroup G) {T : Subgroup G} (a : G) (t : T) :
    uniqueFourConj a (K.map (MulAut.conj (t : G)).toMonoidHom) =
      uniqueFourConj ((t : G)⁻¹ * a) K := by
  rw [show K.map (MulAut.conj (t : G)).toMonoidHom = uniqueFourConj (t : G)⁻¹ K by
    change K.map (MulAut.conj (t : G)).toMonoidHom =
      K.map (MulAut.conj (((t : G)⁻¹)⁻¹)).toMonoidHom
    rw [inv_inv]]
  rw [uc22r3t_uniqueFourConj_mul]

private theorem uc22r3t_orbit_mem (K : Subgroup G) {T : Subgroup G} {a : G}
    (haT : a ∈ normalizer (T : Set G)) (t w : T) :
    uniqueFourConj (w : G) (uniqueFourConj ((t : G)⁻¹ * a) K) =
      uniqueFourConj (((⟨a * (w : G)⁻¹ * a⁻¹ * (t : G),
        T.mul_mem ((Subgroup.mem_normalizer_iff.1 haT ((w : G)⁻¹)).1 (T.inv_mem w.2)) t.2⟩ :
          T) : G)⁻¹ * a) K := by
  rw [uc22r3t_uniqueFourConj_mul]
  congr 1
  group

private theorem uc22r3t_iSup_orbit_canon {K : Subgroup G} {T : Subgroup G} {a : G}
    (haT : a ∈ normalizer (T : Set G)) (t : T) :
    (⨆ u : T, uniqueFourConj ((u : G)⁻¹ * a) K) =
      ⨆ w : T, uniqueFourConj (w : G) (uniqueFourConj ((t : G)⁻¹ * a) K) := by
  apply le_antisymm
  · refine iSup_le fun u => ?_
    let w : T := ⟨a⁻¹ * (t : G) * (u : G)⁻¹ * a, ?_⟩
    · have h := uc22r3t_orbit_mem (K := K) haT (t := t) w
      have hu : (⟨a * (w : G)⁻¹ * a⁻¹ * (t : G),
          T.mul_mem ((Subgroup.mem_normalizer_iff.1 haT ((w : G)⁻¹)).1 (T.inv_mem w.2)) t.2⟩ :
            T) = u := by
        apply Subtype.ext
        simp only [w]
        group
      rw [hu] at h
      rw [← h]
      exact le_iSup (fun w : T => uniqueFourConj (w : G)
        (uniqueFourConj ((t : G)⁻¹ * a) K)) w
    · simpa [mul_assoc] using (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ haT)
        ((t : G) * (u : G)⁻¹)).1 (T.mul_mem t.2 (T.inv_mem u.2))
  · refine iSup_le fun w => ?_
    have h := uc22r3t_orbit_mem (K := K) haT (t := t) w
    rw [h]
    exact le_iSup (fun u : T => uniqueFourConj ((u : G)⁻¹ * a) K) _

private theorem uc22r3t_iSup_eq_of_orbit_eq {K : Subgroup G} {T : Subgroup G} {a b : G}
    (haT : a ∈ normalizer (T : Set G)) (hbT : b ∈ normalizer (T : Set G)) {t s : T}
    (h : uniqueFourConj ((t : G)⁻¹ * a) K =
      uniqueFourConj ((s : G)⁻¹ * b) K) :
    (⨆ u : T, uniqueFourConj a (K.map (MulAut.conj (u : G)).toMonoidHom)) =
      ⨆ u : T, uniqueFourConj b (K.map (MulAut.conj (u : G)).toMonoidHom) := by
  calc
    (⨆ u : T, uniqueFourConj a (K.map (MulAut.conj (u : G)).toMonoidHom)) =
        ⨆ u : T, uniqueFourConj ((u : G)⁻¹ * a) K := by
      congr 1; ext u; rw [uc22r3t_orbit_eq]
    _ = ⨆ w : T, uniqueFourConj (w : G)
          (uniqueFourConj ((t : G)⁻¹ * a) K) := uc22r3t_iSup_orbit_canon haT t
    _ = ⨆ w : T, uniqueFourConj (w : G)
          (uniqueFourConj ((s : G)⁻¹ * b) K) := by rw [h]
    _ = ⨆ u : T, uniqueFourConj ((u : G)⁻¹ * b) K :=
      (uc22r3t_iSup_orbit_canon hbT s).symm
    _ = ⨆ u : T, uniqueFourConj b (K.map (MulAut.conj (u : G)).toMonoidHom) := by
      congr 1; ext u; rw [uc22r3t_orbit_eq]

private theorem uc22r3t_conj_calC {H K : Subgroup G} (hKH : K ∈ calC H)
    {c u : G} (hcH : c ∈ H) (huH : u ∈ H) :
    uniqueFourConj c (K.map (MulAut.conj u).toMonoidHom) ∈ calC H := by
  have hKu : K.map (MulAut.conj u).toMonoidHom ∈ calC H :=
    calC_map_conj_of_mem_normalizer hKH (Subgroup.le_normalizer huH)
  have := calC_map_conj_of_mem_normalizer hKu (Subgroup.le_normalizer (H.inv_mem hcH))
  simpa [CFSG.Open.uniqueFourConj] using this

private theorem uc22r3t_conj_eq_iSup {T K K₁ : Subgroup G}
    (hKjoin : K₁ = ⨆ u : T, K.map (MulAut.conj (u : G)).toMonoidHom) (c : G) :
    uniqueFourConj c K₁ =
      ⨆ u : T, uniqueFourConj c (K.map (MulAut.conj (u : G)).toMonoidHom) := by
  rw [hKjoin]
  change (⨆ u : T, K.map (MulAut.conj (u : G)).toMonoidHom).map
    (MulAut.conj c⁻¹).toMonoidHom = ⨆ u : T,
      uniqueFourConj c (K.map (MulAut.conj (u : G)).toMonoidHom)
  rw [Subgroup.map_iSup]
  rfl

private theorem uc22r3t_barImage_conj_eq_iSup {T H K K₁ : Subgroup G}
    (hTH : T ≤ H) (hKH : K ∈ calC H)
    (hKjoin : K₁ = ⨆ u : T, K.map (MulAut.conj (u : G)).toMonoidHom) {c : G}
    (hcH : c ∈ H) :
    barImage H (uniqueFourConj c K₁) =
      ⨆ u : T, barImage H (uniqueFourConj c (K.map (MulAut.conj (u : G)).toMonoidHom)) := by
  rw [uc22r3t_conj_eq_iSup hKjoin c]
  exact barImage_iSup _ fun u => CFSG.Quasithin.A3.subnormal_le
    (uc22r3t_conj_calC hKH hcH (hTH u.2)).1

private theorem uc22r3t_fam_pair_ne {T K K₁ : Subgroup G}
    (hKjoin : K₁ = ⨆ u : T, K.map (MulAut.conj (u : G)).toMonoidHom)
    {a b : G} (haT : a ∈ normalizer (T : Set G)) (hbT : b ∈ normalizer (T : Set G))
    (hKne : uniqueFourConj a K₁ ≠ uniqueFourConj b K₁) :
    ∀ u v : T, uniqueFourConj a (K.map (MulAut.conj (u : G)).toMonoidHom) ≠
      uniqueFourConj b (K.map (MulAut.conj (v : G)).toMonoidHom) := by
  intro u v hEq
  apply hKne
  have hbase : uniqueFourConj ((u : G)⁻¹ * a) K =
      uniqueFourConj ((v : G)⁻¹ * b) K := by
    have hu := uc22r3t_orbit_eq K a u
    have hv := uc22r3t_orbit_eq K b v
    rw [hu, hv] at hEq
    exact hEq
  rw [uc22r3t_conj_eq_iSup hKjoin a, uc22r3t_conj_eq_iSup hKjoin b]
  exact uc22r3t_iSup_eq_of_orbit_eq haT hbT hbase

private theorem uc22r3t_fam_centralizer {T H K : Subgroup G} (hTH : T ≤ H)
    (hKH : K ∈ calC H) {a b : G} (haH : a ∈ H) (hbH : b ∈ H)
    (hpair : ∀ u v : T, uniqueFourConj a (K.map (MulAut.conj (u : G)).toMonoidHom) ≠
      uniqueFourConj b (K.map (MulAut.conj (v : G)).toMonoidHom)) :
    (⨆ u : T, barImage H (uniqueFourConj a (K.map (MulAut.conj (u : G)).toMonoidHom))) ≤
      Subgroup.centralizer (((⨆ v : T,
        barImage H (uniqueFourConj b (K.map (MulAut.conj (v : G)).toMonoidHom))) :
          Subgroup (Bar2 H)) : Set (Bar2 H)) := by
  refine CFSG.subgroup_le_centralizer_iSup_of_le_centralizer
    (P := ⨆ u : T,
      barImage H (uniqueFourConj a (K.map (MulAut.conj (u : G)).toMonoidHom)))
    (fun v : T =>
      barImage H (uniqueFourConj b (K.map (MulAut.conj (v : G)).toMonoidHom))) ?_
  intro v
  refine iSup_le fun u => ?_
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact (uc22p22l_barImage_commute (uc22r3t_conj_calC hKH haH (hTH u.2))
    (uc22r3t_conj_calC hKH hbH (hTH v.2)) (hpair u v) x hx y hy).symm

theorem uc22r3t_barImage_conj_commute {T M H K₁ : Subgroup G} (hTH : T ≤ H)
    (hK₁ : K₁ ∈ calLOf T M H) {a b : G} (haH : a ∈ H) (hbH : b ∈ H)
    (haT : a ∈ normalizer (T : Set G)) (hbT : b ∈ normalizer (T : Set G))
    (hKne : uniqueFourConj a K₁ ≠ uniqueFourConj b K₁) :
    ∀ x ∈ barImage H (uniqueFourConj a K₁),
      ∀ y ∈ barImage H (uniqueFourConj b K₁), x * y = y * x := by
  obtain ⟨⟨-, -, -, K, hK, hKjoin⟩, hsub⟩ := hK₁
  have hKH : K ∈ calC H := calC_of_calC_of_isSubnormal hK hsub
  have hpair := uc22r3t_fam_pair_ne hKjoin haT hbT hKne
  have hle := uc22r3t_fam_centralizer hTH hKH haH hbH hpair
  have hbarA := uc22r3t_barImage_conj_eq_iSup hTH hKH hKjoin haH
  have hbarB := uc22r3t_barImage_conj_eq_iSup hTH hKH hKjoin hbH
  intro x hx y hy
  rw [hbarA] at hx
  rw [hbarB] at hy
  exact (Subgroup.mem_centralizer_iff.mp (hle hx) y hy).symm

private theorem uc22r3t_mem_normalizer_of_zpow {K : Subgroup G} {z : G} {r k d : ℕ}
    (hr : r.Prime) (hr5 : 5 ≤ r) (hzo : orderOf z = r ^ k)
    (hd1 : 1 ≤ d) (hd3 : d ≤ 3) (h : z ^ d ∈ normalizer (K : Set G)) :
    z ∈ normalizer (K : Set G) := by
  have hdr : ¬ r ∣ d := by
    intro hdvd
    have hle := Nat.le_of_dvd (by omega) hdvd
    omega
  have hcopd : Nat.Coprime d (r ^ k) :=
    (((hr.coprime_iff_not_dvd).mpr hdr).pow_left k).symm
  have hcop : Nat.Coprime d (orderOf z) := by rwa [hzo]
  exact (Subgroup.zpowers_le.mpr h) (mem_zpowers_pow_iff.mpr hcop)

private theorem uc22r3t_mem_normalizer_of_uniqueFourConj {K : Subgroup G} {z g : G}
    (hcomm : z * g = g * z)
    (h : z ∈ normalizer (uniqueFourConj g K : Set G)) :
    z ∈ normalizer (K : Set G) := by
  change z ∈ normalizer (K.map (MulAut.conj g⁻¹).toMonoidHom : Set G) at h
  have hmap : z ∈ (normalizer (K : Set G)).map (MulAut.conj g⁻¹).toMonoidHom := by
    rw [Subgroup.map_equiv_normalizer_eq]
    exact h
  obtain ⟨n, hn, hne⟩ := Subgroup.mem_map.mp hmap
  have hne' : g⁻¹ * n * g = z := by
    change (MulAut.conj g⁻¹) n = z at hne
    rw [MulAut.conj_apply, inv_inv] at hne
    exact hne
  have hn_eq : n = z := by
    calc n = g * (g⁻¹ * n * g) * g⁻¹ := by group
      _ = g * z * g⁻¹ := by rw [hne']
      _ = z := by rw [← hcomm]; group
  rwa [hn_eq] at hn

private theorem uc22r3t_conj_ne_of_lt {K₁ : Subgroup G} {z : G} {r k : ℕ}
    (hr : r.Prime) (hr5 : 5 ≤ r) (hzo : orderOf z = r ^ k)
    (hznot : z ∉ normalizer (K₁ : Set G)) {i j : Fin 4} (hij : (i : ℕ) < (j : ℕ)) :
    uniqueFourConj (z ^ (i : ℕ)) K₁ ≠ uniqueFourConj (z ^ (j : ℕ)) K₁ := by
  intro h
  let d : ℕ := (j : ℕ) - (i : ℕ)
  have hd1 : 1 ≤ d := by simp only [d]; omega
  have hd3 : d ≤ 3 := by simp only [d]; omega
  have hcomp : uniqueFourConj (z ^ (j : ℕ)) K₁ =
      uniqueFourConj (z ^ d) (uniqueFourConj (z ^ (i : ℕ)) K₁) := by
    rw [uc22r3t_uniqueFourConj_mul]
    congr 1
    rw [← pow_add]
    congr 1
    simp only [d]
    omega
  have hfix : uniqueFourConj (z ^ d) (uniqueFourConj (z ^ (i : ℕ)) K₁) =
      uniqueFourConj (z ^ (i : ℕ)) K₁ := by rw [← hcomp, ← h]
  have hcomm : z ^ d * z ^ (i : ℕ) = z ^ (i : ℕ) * z ^ d := by
    rw [← pow_add, ← pow_add, add_comm]
  have hzN_i : z ^ d ∈ normalizer (uniqueFourConj (z ^ (i : ℕ)) K₁ : Set G) :=
    (uniqueFourConj_eq_self_iff).1 hfix
  have hzN : z ^ d ∈ normalizer (K₁ : Set G) :=
    uc22r3t_mem_normalizer_of_uniqueFourConj (g := z ^ (i : ℕ)) hcomm hzN_i
  exact hznot (uc22r3t_mem_normalizer_of_zpow hr hr5 hzo hd1 hd3 hzN)

private theorem uc22r3t_conj_ne_of_gt {K₁ : Subgroup G} {z : G} {r k : ℕ}
    (hr : r.Prime) (hr5 : 5 ≤ r) (hzo : orderOf z = r ^ k)
    (hznot : z ∉ normalizer (K₁ : Set G)) {i j : Fin 4} (hij : (j : ℕ) < (i : ℕ)) :
    uniqueFourConj (z ^ (i : ℕ)) K₁ ≠ uniqueFourConj (z ^ (j : ℕ)) K₁ := by
  intro h
  let d : ℕ := (i : ℕ) - (j : ℕ)
  have hd1 : 1 ≤ d := by simp only [d]; omega
  have hd3 : d ≤ 3 := by simp only [d]; omega
  have hcomp : uniqueFourConj (z ^ (i : ℕ)) K₁ =
      uniqueFourConj (z ^ d) (uniqueFourConj (z ^ (j : ℕ)) K₁) := by
    rw [uc22r3t_uniqueFourConj_mul]
    congr 1
    rw [← pow_add]
    congr 1
    simp only [d]
    omega
  have hfix : uniqueFourConj (z ^ d) (uniqueFourConj (z ^ (j : ℕ)) K₁) =
      uniqueFourConj (z ^ (j : ℕ)) K₁ := by rw [← hcomp, h]
  have hcomm : z ^ d * z ^ (j : ℕ) = z ^ (j : ℕ) * z ^ d := by
    rw [← pow_add, ← pow_add, add_comm]
  have hzN_i : z ^ d ∈ normalizer (uniqueFourConj (z ^ (j : ℕ)) K₁ : Set G) :=
    (uniqueFourConj_eq_self_iff).1 hfix
  have hzN : z ^ d ∈ normalizer (K₁ : Set G) :=
    uc22r3t_mem_normalizer_of_uniqueFourConj (g := z ^ (j : ℕ)) hcomm hzN_i
  exact hznot (uc22r3t_mem_normalizer_of_zpow hr hr5 hzo hd1 hd3 hzN)

theorem uc22r3t_conj_ne_of_not_mem_normalizer {K₁ : Subgroup G} {z : G} {r k : ℕ}
    (hr : r.Prime) (hr5 : 5 ≤ r) (hzo : orderOf z = r ^ k)
    (hznot : z ∉ normalizer (K₁ : Set G)) {i j : Fin 4} (hij : i ≠ j) :
    uniqueFourConj (z ^ (i : ℕ)) K₁ ≠ uniqueFourConj (z ^ (j : ℕ)) K₁ := by
  intro h
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact uc22r3t_conj_ne_of_lt hr hr5 hzo hznot hlt h
  · exact uc22r3t_conj_ne_of_gt hr hr5 hzo hznot hgt h

private def uc22r3tHConj (H : Subgroup G) (z b : G) (hz : z ∈ H) (hb : b ∈ H)
    (i : Fin 4) : ↥H :=
  ⟨(z ^ (i : ℕ))⁻¹ * b * z ^ (i : ℕ),
    H.mul_mem (H.mul_mem (H.inv_mem (H.pow_mem hz _)) hb) (H.pow_mem hz _)⟩

private def uc22r3tBarConj (H : Subgroup G) (z b : G) (hz : z ∈ H) (hb : b ∈ H)
    (i : Fin 4) : Bar2 H :=
  uc22p21cPi H (uc22r3tHConj H z b hz hb i)

private theorem uc22r3tHConj_mem_conj {H K₁ : Subgroup G} {z b : G}
    (hz : z ∈ H) (hb : b ∈ H) (hbK : b ∈ K₁) (i : Fin 4) :
    (uc22r3tHConj H z b hz hb i : G) ∈ uniqueFourConj (z ^ (i : ℕ)) K₁ := by
  rw [mem_uniqueFourConj_iff]
  simpa [uc22r3tHConj, mul_assoc] using hbK

private theorem uc22r3tBarConj_mem {H K₁ : Subgroup G} {z b : G}
    (hz : z ∈ H) (hb : b ∈ H) (hbK : b ∈ K₁) (i : Fin 4) :
    uc22r3tBarConj H z b hz hb i ∈ barImage H (uniqueFourConj (z ^ (i : ℕ)) K₁) :=
  uc22p21c_mem_barImage.2 ⟨uc22r3tHConj H z b hz hb i,
    uc22r3tHConj_mem_conj hz hb hbK i, rfl⟩

private theorem uc22r3tHConj_order {H : Subgroup G} {z b : G} (hz : z ∈ H) (hb : b ∈ H)
    {q : ℕ} (hbo : orderOf b = q) (i : Fin 4) :
    orderOf (uc22r3tHConj H z b hz hb i) = q := by
  have hconj : orderOf ((z ^ (i : ℕ))⁻¹ * b * z ^ (i : ℕ)) = q := by
    have h := SemiconjBy.orderOf_eq ((z ^ (i : ℕ))⁻¹)
      (show SemiconjBy ((z ^ (i : ℕ))⁻¹) b
        ((z ^ (i : ℕ))⁻¹ * b * z ^ (i : ℕ)) by unfold SemiconjBy; group)
    rw [hbo] at h
    exact h.symm
  simpa [uc22r3tHConj] using hconj

private theorem uc22r3tBarConj_order {H : Subgroup G} {z b : G} (hz : z ∈ H) (hb : b ∈ H)
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hbo : orderOf b = q) (i : Fin 4) :
    orderOf (uc22r3tBarConj H z b hz hb i) = q :=
  uc22ine229_orderOf_mk (uc22r3tHConj H z b hz hb i) hq hq2
    (uc22r3tHConj_order hz hb hbo i)

private theorem uc22r3tBarConj_pow {H : Subgroup G} {z b : G} (hz : z ∈ H) (hb : b ∈ H)
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hbo : orderOf b = q) (i : Fin 4) :
    uc22r3tBarConj H z b hz hb i ^ q = 1 := by
  rw [← uc22r3tBarConj_order hz hb hq hq2 hbo i]
  exact pow_orderOf_eq_one _

private theorem uc22r3tHConj_inverts {H : Subgroup G} {z b t : G}
    (hz : z ∈ H) (hb : b ∈ H) (ht : t ∈ H) (hinv : t * b * t⁻¹ = b⁻¹) (i : Fin 4) :
    uc22r3tHConj H z t hz ht i * uc22r3tHConj H z b hz hb i *
      (uc22r3tHConj H z t hz ht i)⁻¹ = (uc22r3tHConj H z b hz hb i)⁻¹ := by
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, uc22r3tHConj]
  calc
    (z ^ (i : ℕ))⁻¹ * t * z ^ (i : ℕ) * ((z ^ (i : ℕ))⁻¹ * b * z ^ (i : ℕ)) *
        ((z ^ (i : ℕ))⁻¹ * t * z ^ (i : ℕ))⁻¹ =
        (z ^ (i : ℕ))⁻¹ * (t * b * t⁻¹) * z ^ (i : ℕ) := by group
    _ = (z ^ (i : ℕ))⁻¹ * b⁻¹ * z ^ (i : ℕ) := by rw [hinv]
    _ = ((z ^ (i : ℕ))⁻¹ * b * z ^ (i : ℕ))⁻¹ := by group

private theorem uc22r3tBarConj_inverts {H : Subgroup G} {z b t : G}
    (hz : z ∈ H) (hb : b ∈ H) (ht : t ∈ H) (hinv : t * b * t⁻¹ = b⁻¹) (i : Fin 4) :
    uc22r3tBarConj H z t hz ht i * uc22r3tBarConj H z b hz hb i *
      (uc22r3tBarConj H z t hz ht i)⁻¹ = (uc22r3tBarConj H z b hz hb i)⁻¹ := by
  have h := congrArg (uc22p21cPi H) (uc22r3tHConj_inverts hz hb ht hinv i)
  simpa [uc22r3tBarConj, map_mul, map_inv] using h

private theorem uc22r3tBarConj_ne_inv {H : Subgroup G} {z b : G} (hz : z ∈ H) (hb : b ∈ H)
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hbo : orderOf b = q) (i : Fin 4) :
    uc22r3tBarConj H z b hz hb i ≠ (uc22r3tBarConj H z b hz hb i)⁻¹ := by
  intro h
  have h2 : uc22r3tBarConj H z b hz hb i ^ 2 = 1 := by
    rw [pow_two]
    nth_rewrite 2 [h]
    exact mul_inv_cancel _
  have hdvd : orderOf (uc22r3tBarConj H z b hz hb i) ∣ 2 :=
    orderOf_dvd_of_pow_eq_one h2
  rw [uc22r3tBarConj_order hz hb hq hq2 hbo i] at hdvd
  exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 hdvd)

private theorem uc22r3tBarConj_not_central {H K₁ : Subgroup G} {z b t : G}
    (hz : z ∈ H) (hb : b ∈ H) (ht : t ∈ H) (hbK : b ∈ K₁) (htK : t ∈ K₁)
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hbo : orderOf b = q)
    (hinv : t * b * t⁻¹ = b⁻¹) (i : Fin 4) :
    ∃ h ∈ barImage H (uniqueFourConj (z ^ (i : ℕ)) K₁),
      ¬ Commute (uc22r3tBarConj H z b hz hb i) h := by
  refine ⟨uc22r3tBarConj H z t hz ht i, uc22r3tBarConj_mem hz ht htK i, fun hc => ?_⟩
  have hc' : Commute (uc22r3tBarConj H z t hz ht i) (uc22r3tBarConj H z b hz hb i) :=
    hc.symm
  have heq : uc22r3tBarConj H z t hz ht i * uc22r3tBarConj H z b hz hb i *
      (uc22r3tBarConj H z t hz ht i)⁻¹ = uc22r3tBarConj H z b hz hb i := by
    calc uc22r3tBarConj H z t hz ht i * uc22r3tBarConj H z b hz hb i *
          (uc22r3tBarConj H z t hz ht i)⁻¹ =
          uc22r3tBarConj H z b hz hb i * uc22r3tBarConj H z t hz ht i *
            (uc22r3tBarConj H z t hz ht i)⁻¹ := by rw [hc'.eq]
      _ = uc22r3tBarConj H z b hz hb i := by group
  rw [uc22r3tBarConj_inverts hz hb ht hinv i] at heq
  exact uc22r3tBarConj_ne_inv hz hb hq hq2 hbo i heq.symm

private theorem uc22r3t_closure_card {H K₁ : Subgroup G} {z b t : G}
    (hz : z ∈ H) (hb : b ∈ H) (ht : t ∈ H) (hbK : b ∈ K₁) (htK : t ∈ K₁)
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hbo : orderOf b = q)
    (hinv : t * b * t⁻¹ = b⁻¹)
    (hcommA : ∀ i j : Fin 4, i ≠ j →
      ∀ x ∈ barImage H (uniqueFourConj (z ^ (i : ℕ)) K₁),
        ∀ y ∈ barImage H (uniqueFourConj (z ^ (j : ℕ)) K₁), x * y = y * x) :
    Nat.card (Subgroup.closure (Set.range (fun i : Fin 4 =>
      uc22r3tBarConj H z b hz hb i))) = q ^ 4 := by
  refine card_closure_eq (p := q) (r := 4) hq
    (fun i : Fin 4 => barImage H (uniqueFourConj (z ^ (i : ℕ)) K₁))
    (fun i => uc22r3tBarConj H z b hz hb i) hcommA ?_ ?_ ?_
  · exact fun i => uc22r3tBarConj_mem hz hb hbK i
  · exact fun i => uc22r3tBarConj_pow hz hb hq hq2 hbo i
  · exact fun i => uc22r3tBarConj_not_central hz hb ht hbK htK hq hq2 hbo hinv i

private theorem uc22r3t_closure_elemAbelian {H K₁ : Subgroup G} {z b : G}
    (hz : z ∈ H) (hb : b ∈ H) (hbK : b ∈ K₁)
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hbo : orderOf b = q)
    (hcommA : ∀ i j : Fin 4, i ≠ j →
      ∀ x ∈ barImage H (uniqueFourConj (z ^ (i : ℕ)) K₁),
        ∀ y ∈ barImage H (uniqueFourConj (z ^ (j : ℕ)) K₁), x * y = y * x) :
    IsElemAbelian q (Subgroup.closure (Set.range (fun i : Fin 4 =>
      uc22r3tBarConj H z b hz hb i))) := by
  refine IsElemAbelian.closure_of_commute ?_ ?_
  · rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    by_cases hij : i = j
    · subst hij
      exact Commute.refl _
    · exact hcommA i j hij _ (uc22r3tBarConj_mem hz hb hbK i) _
        (uc22r3tBarConj_mem hz hb hbK j)
  · rintro _ ⟨i, rfl⟩
    exact uc22r3tBarConj_pow hz hb hq hq2 hbo i

private theorem uc22r3t_B_le_M (D : Data G) {H : Subgroup G} {z b : G}
    (hz : z ∈ H) (hb : b ∈ H) (hbM : b ∈ D.M) (hzM : z ∈ D.M) :
    Subgroup.closure (Set.range (fun i : Fin 4 => uc22r3tHConj H z b hz hb i)) ≤
      D.M.subgroupOf H := by
  rw [Subgroup.closure_le]
  rintro _ ⟨i, rfl⟩
  change (uc22r3tHConj H z b hz hb i : G) ∈ D.M
  simpa [uc22r3tHConj] using
    (D.M.mul_mem (D.M.mul_mem (D.M.inv_mem (D.M.pow_mem hzM _)) hbM)
      (D.M.pow_mem hzM _))

private theorem uc22r3t_closure_le_map {H : Subgroup G} {z b : G} (hz : z ∈ H) (hb : b ∈ H) :
    Subgroup.closure (Set.range (fun i : Fin 4 => uc22r3tBarConj H z b hz hb i)) ≤
      (Subgroup.closure (Set.range (fun i : Fin 4 => uc22r3tHConj H z b hz hb i))).map
        (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) := by
  rw [Subgroup.closure_le]
  rintro _ ⟨i, rfl⟩
  exact ⟨uc22r3tHConj H z b hz hb i, Subgroup.subset_closure ⟨i, rfl⟩, rfl⟩

private theorem uc22r3t_map_le_M {D : Data G} {H : Subgroup G} {B E : Subgroup ↥H}
    (hEB : E ≤ B) (hB : B ≤ D.M.subgroupOf H) : E.map H.subtype ≤ D.M := by
  intro x hx
  obtain ⟨h, hhE, rfl⟩ := Subgroup.mem_map.mp hx
  exact Subgroup.mem_subgroupOf.mp (hB (hEB hhE))

private theorem uc22r3t_rank_contradiction (D : Data G) (he : evenRank G = 3)
    {H : Subgroup G} {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    {E : Subgroup ↥H} (hEel : IsElemAbelian q E) (hEcard : Nat.card E = q ^ 4)
    (hEM : E.map H.subtype ≤ D.M) : False := by
  have hEGel : IsElemAbelian q (E.map H.subtype) := hEel.map H.subtype
  have hEGcard : Nat.card (E.map H.subtype) = q ^ 4 := by
    rw [Subgroup.card_map_of_injective H.subtype_injective, hEcard]
  have h4 := le_pRank_of_elemAbelian hq hEM hEGel hEGcard
  have h3 := CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.pRank_le_three_of_evenRank
    D he hq hq2
  omega

private theorem uc22r3t_rank_four_core (D : Data G) (he : evenRank G = 3)
    {H K₁ : Subgroup G} {b t z : G}
    (hbK : b ∈ K₁) (htK : t ∈ K₁) (hbH : b ∈ H) (htH : t ∈ H) (hzH : z ∈ H)
    (hbM : b ∈ D.M) (hzM : z ∈ D.M)
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hbo : orderOf b = q)
    (hinv : t * b * t⁻¹ = b⁻¹)
    (hcommA : ∀ i j : Fin 4, i ≠ j →
      ∀ x ∈ barImage H (uniqueFourConj (z ^ (i : ℕ)) K₁),
        ∀ y ∈ barImage H (uniqueFourConj (z ^ (j : ℕ)) K₁), x * y = y * x) : False := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let B : Subgroup ↥H := Subgroup.closure (Set.range (fun i : Fin 4 =>
    uc22r3tHConj H z b hzH hbH i))
  let E₀ : Subgroup (Bar2 H) := Subgroup.closure (Set.range (fun i : Fin 4 =>
    uc22r3tBarConj H z b hzH hbH i))
  have hcard : Nat.card E₀ = q ^ 4 :=
    uc22r3t_closure_card hzH hbH htH hbK htK hq hq2 hbo hinv hcommA
  have hE₀el : IsElemAbelian q E₀ :=
    uc22r3t_closure_elemAbelian hzH hbH hbK hq hq2 hbo hcommA
  have hB_le_M : B ≤ D.M.subgroupOf H := uc22r3t_B_le_M D hzH hbH hbM hzM
  have hE₀_le : E₀ ≤ B.map (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) :=
    uc22r3t_closure_le_map hzH hbH
  obtain ⟨E, hEB, hEel, hEcard⟩ :=
    uc22p20d_lift_elemAbelian (CFSG.pCore 2 ↥H) CFSG.pCore_isPGroup hq hq2 B E₀ hE₀el
      (n := 4) hcard hE₀_le
  exact uc22r3t_rank_contradiction D he hq hq2 hEel hEcard
    (uc22r3t_map_le_M hEB hB_le_M)

theorem uc22r3t_false_of_rank_four (D : Data G) (he : evenRank G = 3)
    {H K₁ : Subgroup G} {b t z : G}
    (hbK : b ∈ K₁) (htK : t ∈ K₁)
    (hbH : b ∈ H) (htH : t ∈ H) (hzH : z ∈ H) (hbM : b ∈ D.M) (hzM : z ∈ D.M)
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hbo : orderOf b = q)
    (hinv : t * b * t⁻¹ = b⁻¹)
    (hcommA : ∀ i j : Fin 4, i ≠ j →
      ∀ x ∈ barImage H (uniqueFourConj (z ^ (i : ℕ)) K₁),
        ∀ y ∈ barImage H (uniqueFourConj (z ^ (j : ℕ)) K₁), x * y = y * x) :
    False :=
  uc22r3t_rank_four_core D he hbK htK hbH htH hzH hbM hzM hq hq2 hbo hinv hcommA

end CFSG.LocalAnalysis.UniquenessCase.UC22
