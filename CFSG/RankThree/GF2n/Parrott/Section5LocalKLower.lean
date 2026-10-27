module

public import CFSG.RankThree.GF2n.Parrott.SylowH
public import CFSG.RankThree.GF2n.Parrott.Section5LocalJ
public import CFSG.RankThree.GF2n.Parrott.Section5Basic
public import CFSG.RankThree.GF2n.Parrott.LiftSquare
public import CFSG.Holt.PSL2Natural.Defs
public import CFSG.Holt.PermFacts
public import CFSG.Holt.ThreePoint
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporJ4Quot
public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalBender
public import CFSG.LocalAnalysis.QuasithinUnique.K1.ExceptionalCatSuzuki
public import CFSG.Quasithin.Background.E2NParamStar
public import CFSG.Quasithin.Vol2.Ch11StatementsInputsAS2
public import CFSG.Quasithin.Vol2.Ch11StatementsInputsAS3
public import CFSG.Quasithin.Vol2.E2TenEight
public import CFSG.RankThree.GF2n.Parrott.ZFusionControl
public import CFSG.RankThree.Holt.Basic
public import CFSG.RankThree.PartTwo.Sec21.HoltCatalog

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.ABGLocalTools Subgroup
open CFSG.ComponentClassification.CatFactsSmall.PSp43
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G}
variable [hN : ((J z).subgroupOf (H z)).Normal] (D : QuotientData (z := z) hN)

private def k52ZSub (h : Tim79a.ParrottHyp z) : Subgroup (J z) :=
  (Subgroup.zpowers z).subgroupOf (J z)

private instance zSub_normal (h : Tim79a.ParrottHyp z) : (k52ZSub (z := z) h).Normal := by
  apply Subgroup.normal_of_le_center
  intro x hx
  rw [Subgroup.mem_center_iff]
  intro y
  apply Subtype.ext
  have hxz : (x : G) ∈ Subgroup.zpowers z := Subgroup.mem_subgroupOf.mp hx
  exact Subgroup.mem_centralizer_iff.mp (zpowers_centralizes_J h hxz) (y : G) y.2

private abbrev JModZ (h : Tim79a.ParrottHyp z) : Type := J z ⧸ k52ZSub (z := z) h

private noncomputable def k52jm (h : Tim79a.ParrottHyp z) : J z →* JModZ h :=
  QuotientGroup.mk' (k52ZSub (z := z) h)

private theorem jm_eq_one_iff (h : Tim79a.ParrottHyp z) (a : J z) :
    k52jm h a = 1 ↔ (a : G) ∈ Subgroup.zpowers z := by
  change (QuotientGroup.mk a : J z ⧸ k52ZSub h) = 1 ↔ _
  rw [QuotientGroup.eq_one_iff, k52ZSub, Subgroup.mem_subgroupOf]

private theorem jm_eq_iff (h : Tim79a.ParrottHyp z) (a b : J z) :
    k52jm h a = k52jm h b ↔ ((a * b⁻¹ : J z) : G) ∈ Subgroup.zpowers z := by
  constructor
  · intro hab
    have h2 : k52jm h (a * b⁻¹) = 1 := by
      rw [map_mul, map_inv, hab, mul_inv_cancel]
    exact (jm_eq_one_iff h _).mp h2
  · intro h1
    have h2 : k52jm h (a * b⁻¹) = 1 := (jm_eq_one_iff h _).mpr h1
    rw [map_mul, map_inv] at h2
    exact mul_inv_eq_one.mp h2

private instance jm_commutative (h : Tim79a.ParrottHyp z) : IsMulCommutative (JModZ h) := by
  change IsMulCommutative (J z ⧸ k52ZSub h)
  rw [Subgroup.Normal.quotient_commutative_iff_commutator_le]
  rw [commutator_def, Subgroup.commutator_le]
  intro a _ b _
  exact Subgroup.mem_subgroupOf.mpr (commutator_mem_zpowers_z h a.2 b.2)

private theorem jm_mul_comm (h : Tim79a.ParrottHyp z) (a b : JModZ h) : a * b = b * a :=
  (IsMulCommutative.is_comm).comm a b

private theorem jm_conj_mem_J (h : Tim79a.ParrottHyp z) {g : ↥(H z)} (hg : (g : G) ∈ J z)
    (a : J z) : k52jm h (conjJ' z g a) = k52jm h a := by
  rw [jm_eq_iff]
  have hc := commutator_mem_zpowers_z h hg a.2
  simpa [conjJ'_apply_coe, commutatorElement_def, mul_assoc] using hc

private theorem conj_centerIn_mul_inv_mem_zpowers (h : Tim79a.ParrottHyp z) {e : G}
    (he : e ∈ centerIn (J z)) (g : ↥(H z)) :
    (g : G) * e * (g : G)⁻¹ * e⁻¹ ∈ Subgroup.zpowers z := by
  classical
  obtain ⟨z₁, hz₁sup, hz₁z, hord⟩ := exists_z1 h
  have hz₁ : z₁ ∈ centerIn (J z) := by
    rw [hz₁sup]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers z₁)
  have hgz₁ : (g : G) * z₁ * (g : G)⁻¹ = z₁ ∨ (g : G) * z₁ * (g : G)⁻¹ = z * z₁ := by
    by_cases hc : (g : G) ∈ Subgroup.centralizer ({z₁} : Set G)
    · left
      have h' : (g : G) * z₁ = z₁ * (g : G) := Subgroup.mem_centralizer_singleton_iff.mp hc
      rw [h', mul_inv_cancel_right]
    · right
      exact conj_z1_eq_of_not_mem_centralizer h hz₁ hz₁z hord g.2 hc
  have hgz : (g : G) * z * (g : G)⁻¹ = z := by
    have hcomm : (g : G) * z = z * (g : G) :=
      Subgroup.mem_centralizer_singleton_iff.mp g.2
    rw [hcomm, mul_inv_cancel_right]
  have hcomm : z * z₁ = z₁ * z :=
    Subgroup.mem_centralizer_iff.mp hz₁.2 z (z_mem_J h)
  have hz2 : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rwa [h.1, pow_two] at this
  have hz₁2 : z₁ * z₁ = 1 := by
    have := pow_orderOf_eq_one z₁
    rwa [hord, pow_two] at this
  have hzz₁2 : (z * z₁) * (z * z₁) = 1 := by
    calc (z * z₁) * (z * z₁) = z * (z₁ * z) * z₁ := by group
      _ = z * (z * z₁) * z₁ := by rw [hcomm]
      _ = (z * z) * (z₁ * z₁) := by group
      _ = 1 := by rw [hz2, hz₁2, one_mul]
  rcases (mem_centerIn_J_iff h hz₁ hz₁z hord).mp he with rfl | rfl | rfl | rfl
  · simp
  · rw [hgz]; simp
  · rcases hgz₁ with h' | h' <;> rw [h'] <;> simp
  · rw [show (g : G) * (z * z₁) * (g : G)⁻¹ =
        ((g : G) * z * (g : G)⁻¹) * ((g : G) * z₁ * (g : G)⁻¹) by group, hgz]
    rcases hgz₁ with h' | h'
    · rw [h']; simp
    · rw [h']
      have h2 : z * (z * z₁) = z₁ := by rw [← mul_assoc, hz2, one_mul]
      have h3 : (z₁ * (z * z₁)) = z := by
        calc z₁ * (z * z₁) = z₁ * z * z₁ := by group
          _ = z * z₁ * z₁ := by rw [hcomm]
          _ = z * (z₁ * z₁) := by group
          _ = z := by rw [hz₁2, mul_one]
      have hinv : (z * z₁)⁻¹ = z * z₁ := inv_eq_of_mul_eq_one_right hzz₁2
      rw [hinv, h2, h3]
      exact Subgroup.mem_zpowers z

private theorem jm_conj_centerIn (h : Tim79a.ParrottHyp z) {c : J z}
    (hc : (c : G) ∈ centerIn (J z)) (g : ↥(H z)) : k52jm h (conjJ' z g c) = k52jm h c := by
  rw [jm_eq_iff]
  have hc' := conj_centerIn_mul_inv_mem_zpowers h hc g
  simpa [conjJ'_apply_coe, mul_assoc] using hc'

private theorem jm_surjective (h : Tim79a.ParrottHyp z) : Function.Surjective (k52jm h) :=
  QuotientGroup.mk'_surjective _

private noncomputable def k52ConjJM (h : Tim79a.ParrottHyp z) (g : ↥(H z)) :
    JModZ h →* JModZ h :=
  QuotientGroup.lift (k52ZSub h) ((k52jm h).comp (conjJ' z g)) (by
    intro a ha
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, jm_eq_one_iff]
    change ((conjJ' z g a : J z) : G) ∈ Subgroup.zpowers z
    have haz : (a : G) ∈ Subgroup.zpowers z := Subgroup.mem_subgroupOf.mp ha
    rw [conjJ'_apply_coe]
    have hcomm : (g : G) * (a : G) = (a : G) * (g : G) :=
      Subgroup.mem_centralizer_iff.mp (zpowers_centralizes_H h haz) (g : G) g.2
    rw [hcomm, mul_inv_cancel_right]
    exact haz)

private theorem conjJM_apply (h : Tim79a.ParrottHyp z) (g : ↥(H z)) (a : J z) :
    k52ConjJM h g (k52jm h a) = k52jm h (conjJ' z g a) :=
  QuotientGroup.lift_mk' _ _ a

private theorem conjJM_mul (h : Tim79a.ParrottHyp z) (g g' : ↥(H z)) (a : JModZ h) :
    k52ConjJM h (g * g') a = k52ConjJM h g (k52ConjJM h g' a) := by
  obtain ⟨b, rfl⟩ := jm_surjective h a
  rw [conjJM_apply, map_mul, MulAut.mul_apply, conjJM_apply, conjJM_apply]

private theorem conjJM_one (h : Tim79a.ParrottHyp z) (a : JModZ h) :
    k52ConjJM h 1 a = a := by
  obtain ⟨b, rfl⟩ := jm_surjective h a
  rw [conjJM_apply, map_one, MulAut.one_apply]

private theorem conjJM_inv_left (h : Tim79a.ParrottHyp z) (g : ↥(H z)) (a : JModZ h) :
    k52ConjJM h g (k52ConjJM h g⁻¹ a) = a := by
  rw [← conjJM_mul, mul_inv_cancel, conjJM_one]

private theorem conjJM_inv_right (h : Tim79a.ParrottHyp z) (g : ↥(H z)) (a : JModZ h) :
    k52ConjJM h g⁻¹ (k52ConjJM h g a) = a := by
  rw [← conjJM_mul, inv_mul_cancel, conjJM_one]

private theorem conjJM_congr (h : Tim79a.ParrottHyp z) {g g' : ↥(H z)}
    (hq : qH D g = qH D g') : k52ConjJM h g = k52ConjJM h g' := by
  apply MonoidHom.ext
  intro a
  obtain ⟨b, rfl⟩ := jm_surjective h a
  rw [conjJM_apply, conjJM_apply]
  have hgg' : g * g'⁻¹ ∈ (J z).subgroupOf (H z) := by
    rw [J_mem_iff D, map_mul, map_inv, hq, mul_inv_cancel]
  let k : J z := ⟨(((g * g'⁻¹ : ↥(H z)) : G)), Subgroup.mem_subgroupOf.mp hgg'⟩
  have hkH : (⟨(k : G), J_le_H k.2⟩ : ↥(H z)) = g * g'⁻¹ := Subtype.ext rfl
  have hgeq : g = (⟨(k : G), J_le_H k.2⟩ : ↥(H z)) * g' := by
    rw [hkH]; group
  conv_lhs => rw [hgeq, map_mul, MulAut.mul_apply]
  rw [jm_conj_mem_J h k.2]

private theorem conjJM_centerIn (h : Tim79a.ParrottHyp z) {c : J z}
    (hc : (c : G) ∈ centerIn (J z)) (g : ↥(H z)) :
    k52ConjJM h g (k52jm h c) = k52jm h c := by
  rw [conjJM_apply, jm_conj_centerIn h hc g]

private theorem conjJM_three (h : Tim79a.ParrottHyp z) {x : ↥(H z)}
    (hx3J : x ^ 3 ∈ (J z).subgroupOf (H z)) (a : JModZ h) :
    k52ConjJM h x (k52ConjJM h x (k52ConjJM h x a)) = a := by
  rw [← conjJM_mul, ← conjJM_mul]
  have h3 : x * x * x = x ^ 3 := by
    rw [show (3:ℕ) = 2 + 1 from rfl, pow_succ, pow_two]
  rw [h3]
  obtain ⟨b, rfl⟩ := jm_surjective h a
  rw [conjJM_apply, jm_conj_mem_J h (Subgroup.mem_subgroupOf.mp hx3J) b]

private theorem conjJM_inv_apply (h : Tim79a.ParrottHyp z) {x : ↥(H z)}
    (hx3J : x ^ 3 ∈ (J z).subgroupOf (H z)) (a : JModZ h) :
    k52ConjJM h x⁻¹ a = k52ConjJM h x (k52ConjJM h x a) := by
  have h1 := conjJM_three h hx3J (k52ConjJM h x⁻¹ a)
  rw [conjJM_inv_left h x a] at h1
  exact h1.symm

private theorem jm_word {M : Type*} [CommGroup M] (p q r s : M) (hs : s * s = 1) :
    (p * s) * (q * s) * (r * s) = p * q * r * s := by
  calc (p * s) * (q * s) * (r * s) = (p * q * r) * (s * s) * s := by ac_rfl
    _ = p * q * r * s := by rw [hs, mul_one]


private noncomputable def k52Jx {j : G} (hj : j ∈ J z) : J z := ⟨j, hj⟩

private noncomputable def k52U (jx : J z) (y : ↥(H z)) : J z := conjJ' z y jx

private noncomputable def k52C (jx : J z) (y : ↥(H z)) : J z := jx⁻¹ * k52U jx y

private noncomputable def k52N (jx : J z) (x : ↥(H z)) : J z :=
  jx * conjJ' z x jx * conjJ' z x (conjJ' z x jx)

private theorem k52C_mem_centerIn (h : Tim79a.ParrottHyp z) {j : G} (hj : j ∈ J z)
    {y : ↥(H z)} (hyj : conjV h y (QuotientV.pi z ⟨j, hj⟩) = QuotientV.pi z ⟨j, hj⟩) :
    ((k52C (k52Jx hj) y : J z) : G) ∈ centerIn (J z) := by
  rw [← pi_eq_one_iff_mem_centerIn (z := z) (k52C (k52Jx hj) y).2]
  change QuotientV.pi z (k52C (k52Jx hj) y) = 1
  simp only [k52C, k52U, k52Jx, map_mul, map_inv]
  rw [← conjV_mk h y ⟨j, hj⟩, hyj]
  simp

private theorem k52N_mem_centerIn (h : Tim79a.ParrottHyp z) {j : G} (hj : j ∈ J z)
    {x : ↥(H z)}
    (htr : QuotientV.pi z ⟨j, hj⟩ * conjV h x (QuotientV.pi z ⟨j, hj⟩) *
      conjV h x (conjV h x (QuotientV.pi z ⟨j, hj⟩)) = 1) :
    ((k52N (k52Jx hj) x : J z) : G) ∈ centerIn (J z) := by
  rw [← pi_eq_one_iff_mem_centerIn (z := z) (k52N (k52Jx hj) x).2]
  change QuotientV.pi z (k52N (k52Jx hj) x) = 1
  simp only [k52N, k52Jx, map_mul]
  rw [← conjV_mk h x ⟨j, hj⟩, ← conjV_mk h x (conjJ' z x ⟨j, hj⟩),
    ← conjV_mk h x ⟨j, hj⟩]
  exact htr

private theorem k52_trace_expansion (h : Tim79a.ParrottHyp z) {j : G} (hj : j ∈ J z)
    {x y : ↥(H z)} :
    conjJ' z y (k52N (k52Jx hj) x) =
      k52U (k52Jx hj) y * conjJ' z (y * x * y⁻¹) (k52U (k52Jx hj) y) *
        conjJ' z (y * x * y⁻¹) (conjJ' z (y * x * y⁻¹) (k52U (k52Jx hj) y)) := by
  have hA : conjJ' z y (conjJ' z x (k52Jx hj)) =
      conjJ' z (y * x * y⁻¹) (k52U (k52Jx hj) y) := by
    rw [k52U, ← MulAut.mul_apply, ← map_mul, ← MulAut.mul_apply, ← map_mul]
    congr 1
    group
  have hB : conjJ' z y (conjJ' z x (conjJ' z x (k52Jx hj))) =
      conjJ' z (y * x * y⁻¹) (conjJ' z (y * x * y⁻¹) (k52U (k52Jx hj) y)) := by
    rw [k52U, ← MulAut.mul_apply, ← map_mul, ← MulAut.mul_apply, ← map_mul,
      ← MulAut.mul_apply, ← map_mul, ← MulAut.mul_apply, ← map_mul]
    congr 1
    group
  simp only [k52N]
  rw [map_mul, map_mul]
  change conjJ' z y (k52Jx hj) * conjJ' z y (conjJ' z x (k52Jx hj)) *
      conjJ' z y (conjJ' z x (conjJ' z x (k52Jx hj))) = _
  rw [show conjJ' z y (k52Jx hj) = k52U (k52Jx hj) y from rfl, hA, hB]

private theorem k52_Njm (h : Tim79a.ParrottHyp z) {j : G} (hj : j ∈ J z) {x : ↥(H z)} :
    k52jm h (k52N (k52Jx hj) x) =
      k52jm h (k52Jx hj) * k52ConjJM h x (k52jm h (k52Jx hj)) *
        k52ConjJM h x (k52ConjJM h x (k52jm h (k52Jx hj))) := by
  simp only [k52N]
  rw [map_mul, map_mul, ← conjJM_apply h x (k52Jx hj),
    ← conjJM_apply h x (conjJ' z x (k52Jx hj)), ← conjJM_apply h x (k52Jx hj)]

private theorem k52_Ujm (h : Tim79a.ParrottHyp z) {j : G} (hj : j ∈ J z) {y : ↥(H z)} :
    k52jm h (k52U (k52Jx hj) y) =
      k52jm h (k52Jx hj) * k52jm h (k52C (k52Jx hj) y) := by
  have hU : k52U (k52Jx hj) y = k52Jx hj * k52C (k52Jx hj) y := by
    simp only [k52C]; group
  rw [hU, map_mul]

private theorem k52_key_same (h : Tim79a.ParrottHyp z) {j : G} (hj : j ∈ J z)
    {x y : ↥(H z)} (hxZ : conjZ z x = 1)
    (hyj : conjV h y (QuotientV.pi z ⟨j, hj⟩) = QuotientV.pi z ⟨j, hj⟩)
    (hcase : qH D (y * x * y⁻¹) = qH D x) :
    k52jm h (conjJ' z y (k52N (k52Jx hj) x)) =
      k52jm h (k52N (k52Jx hj) x) * k52jm h (k52C (k52Jx hj) y) := by
  haveI : IsMulCommutative (JModZ h) := jm_commutative h
  letI : CommGroup (JModZ h) :=
    { (inferInstance : Group (JModZ h)) with
      mul_comm := fun a b => jm_mul_comm h a b }
  have hc_mem : ((k52C (k52Jx hj) y : J z) : G) ∈ centerIn (J z) :=
    k52C_mem_centerIn h hj hyj
  have hc_sq : k52jm h (k52C (k52Jx hj) y) * k52jm h (k52C (k52Jx hj) y) = 1 := by
    rw [← map_mul]
    exact (jm_eq_one_iff h _).mpr (by
      simpa using sq_mem_zpowers_z h (k52C (k52Jx hj) y).2)
  have hφ : k52ConjJM h (y * x * y⁻¹) = k52ConjJM h x := conjJM_congr h (D := D) hcase
  rw [k52_trace_expansion h hj, map_mul, map_mul, k52_Ujm h hj, k52_Njm h hj,
    ← conjJM_apply h (y * x * y⁻¹) (k52U (k52Jx hj) y),
    ← conjJM_apply h (y * x * y⁻¹) (conjJ' z (y * x * y⁻¹) (k52U (k52Jx hj) y)),
    ← conjJM_apply h (y * x * y⁻¹) (k52U (k52Jx hj) y), k52_Ujm h hj, hφ]
  have hmid : k52ConjJM h x (k52jm h (k52Jx hj) * k52jm h (k52C (k52Jx hj) y)) =
      k52ConjJM h x (k52jm h (k52Jx hj)) * k52jm h (k52C (k52Jx hj) y) := by
    rw [map_mul, conjJM_centerIn h hc_mem x]
  have hlast : k52ConjJM h x (k52ConjJM h x
      (k52jm h (k52Jx hj) * k52jm h (k52C (k52Jx hj) y))) =
      k52ConjJM h x (k52ConjJM h x (k52jm h (k52Jx hj))) *
        k52jm h (k52C (k52Jx hj) y) := by
    rw [hmid, map_mul, conjJM_centerIn h hc_mem x]
  rw [hlast, hmid]
  exact jm_word _ _ _ _ hc_sq

private theorem k52_key_inv (h : Tim79a.ParrottHyp z) {j : G} (hj : j ∈ J z)
    {x y : ↥(H z)} (hxZ : conjZ z x = 1) (hx3 : qH D x ^ 3 = 1)
    (hyj : conjV h y (QuotientV.pi z ⟨j, hj⟩) = QuotientV.pi z ⟨j, hj⟩)
    (hcase : qH D (y * x * y⁻¹) = qH D x⁻¹) :
    k52jm h (conjJ' z y (k52N (k52Jx hj) x)) =
      k52jm h (k52N (k52Jx hj) x) * k52jm h (k52C (k52Jx hj) y) := by
  haveI : IsMulCommutative (JModZ h) := jm_commutative h
  letI : CommGroup (JModZ h) :=
    { (inferInstance : Group (JModZ h)) with
      mul_comm := fun a b => jm_mul_comm h a b }
  have hc_mem : ((k52C (k52Jx hj) y : J z) : G) ∈ centerIn (J z) :=
    k52C_mem_centerIn h hj hyj
  have hc_sq : k52jm h (k52C (k52Jx hj) y) * k52jm h (k52C (k52Jx hj) y) = 1 := by
    rw [← map_mul]
    exact (jm_eq_one_iff h _).mpr (by
      simpa using sq_mem_zpowers_z h (k52C (k52Jx hj) y).2)
  have hx3J : x ^ 3 ∈ (J z).subgroupOf (H z) := by
    rw [J_mem_iff D]; simpa using hx3
  have hφ : k52ConjJM h (y * x * y⁻¹) = k52ConjJM h x⁻¹ := conjJM_congr h (D := D) hcase
  rw [k52_trace_expansion h hj, map_mul, map_mul, k52_Ujm h hj, k52_Njm h hj,
    ← conjJM_apply h (y * x * y⁻¹) (k52U (k52Jx hj) y),
    ← conjJM_apply h (y * x * y⁻¹) (conjJ' z (y * x * y⁻¹) (k52U (k52Jx hj) y)),
    ← conjJM_apply h (y * x * y⁻¹) (k52U (k52Jx hj) y), k52_Ujm h hj, hφ]
  have hmid : k52ConjJM h x⁻¹ (k52jm h (k52Jx hj) * k52jm h (k52C (k52Jx hj) y)) =
      k52ConjJM h x (k52ConjJM h x (k52jm h (k52Jx hj))) *
        k52jm h (k52C (k52Jx hj) y) := by
    rw [map_mul, conjJM_centerIn h hc_mem x⁻¹, conjJM_inv_apply h hx3J]
  have hlast : k52ConjJM h x⁻¹ (k52ConjJM h x⁻¹
      (k52jm h (k52Jx hj) * k52jm h (k52C (k52Jx hj) y))) =
      k52ConjJM h x (k52jm h (k52Jx hj)) * k52jm h (k52C (k52Jx hj) y) := by
    rw [hmid, map_mul, conjJM_inv_right h x (k52ConjJM h x (k52jm h (k52Jx hj))),
      conjJM_centerIn h hc_mem x⁻¹]
  rw [hlast, hmid]
  calc (k52jm h (k52Jx hj) * k52jm h (k52C (k52Jx hj) y)) *
        (k52ConjJM h x (k52ConjJM h x (k52jm h (k52Jx hj))) *
          k52jm h (k52C (k52Jx hj) y)) *
        (k52ConjJM h x (k52jm h (k52Jx hj)) * k52jm h (k52C (k52Jx hj) y))
      = (k52jm h (k52Jx hj) * k52jm h (k52C (k52Jx hj) y)) *
          (k52ConjJM h x (k52jm h (k52Jx hj)) * k52jm h (k52C (k52Jx hj) y)) *
          (k52ConjJM h x (k52ConjJM h x (k52jm h (k52Jx hj))) *
            k52jm h (k52C (k52Jx hj) y)) := by ac_rfl
    _ = k52jm h (k52Jx hj) * k52ConjJM h x (k52jm h (k52Jx hj)) *
          k52ConjJM h x (k52ConjJM h x (k52jm h (k52Jx hj))) *
            k52jm h (k52C (k52Jx hj) y) := jm_word _ _ _ _ hc_sq

private theorem k52_trace_key (h : Tim79a.ParrottHyp z) {j : G} (hj : j ∈ J z)
    {x y : ↥(H z)} (hxZ : conjZ z x = 1) (hx3 : qH D x ^ 3 = 1)
    (hyx : qH D y * qH D x * (qH D y)⁻¹ = qH D x ∨
      qH D y * qH D x * (qH D y)⁻¹ = (qH D x)⁻¹)
    (hyj : conjV h y (QuotientV.pi z ⟨j, hj⟩) = QuotientV.pi z ⟨j, hj⟩) :
    k52jm h (conjJ' z y (k52N (k52Jx hj) x)) =
      k52jm h (k52N (k52Jx hj) x) * k52jm h (k52C (k52Jx hj) y) := by
  have hyx' : qH D (y * x * y⁻¹) = qH D x ∨ qH D (y * x * y⁻¹) = qH D x⁻¹ := by
    rw [map_mul, map_mul, map_inv]
    rcases hyx with h | h
    · exact Or.inl h
    · exact Or.inr (by rw [h, map_inv])
  rcases hyx' with hcase | hcase
  · exact k52_key_same D h hj hxZ hyj hcase
  · exact k52_key_inv D h hj hxZ hx3 hyj hcase

theorem conj_eq_or_eq_mul_z_of_trace (h : Tim79a.ParrottHyp z) {j : G} (hj : j ∈ J z)
    {x y : ↥(H z)} (hxZ : conjZ z x = 1) (hx3 : qH D x ^ 3 = 1)
    (hyx : qH D y * qH D x * (qH D y)⁻¹ = qH D x ∨
      qH D y * qH D x * (qH D y)⁻¹ = (qH D x)⁻¹)
    (hyj : conjV h y (QuotientV.pi z ⟨j, hj⟩) = QuotientV.pi z ⟨j, hj⟩)
    (htr : QuotientV.pi z ⟨j, hj⟩ * conjV h x (QuotientV.pi z ⟨j, hj⟩) *
      conjV h x (conjV h x (QuotientV.pi z ⟨j, hj⟩)) = 1) :
    (y : G) * j * (y : G)⁻¹ = j ∨ (y : G) * j * (y : G)⁻¹ = j * z := by
  have hN_mem : ((k52N (k52Jx hj) x : J z) : G) ∈ centerIn (J z) :=
    k52N_mem_centerIn h hj htr
  have key := k52_trace_key D h hj hxZ hx3 hyx hyj
  have hNy : k52jm h (conjJ' z y (k52N (k52Jx hj) x)) =
      k52jm h (k52N (k52Jx hj) x) := by
    rw [jm_eq_iff]
    have h' := conj_centerIn_mul_inv_mem_zpowers h hN_mem y
    simpa [conjJ'_apply_coe, mul_assoc] using h'
  have hc_one : k52jm h (k52C (k52Jx hj) y) = 1 := by
    have h1 : k52jm h (k52N (k52Jx hj) x) * k52jm h (k52C (k52Jx hj) y) =
        k52jm h (k52N (k52Jx hj) x) * 1 := by rw [mul_one, ← key, hNy]
    exact mul_left_cancel h1
  have hc_zp : ((k52C (k52Jx hj) y : J z) : G) ∈ Subgroup.zpowers z :=
    (jm_eq_one_iff h _).mp hc_one
  have hUcoe : ((k52U (k52Jx hj) y : J z) : G) = (y : G) * j * (y : G)⁻¹ := by
    rw [k52U, conjJ'_apply_coe]
    rfl
  have hUc : ((k52U (k52Jx hj) y : J z) : G) =
      j * ((k52C (k52Jx hj) y : J z) : G) := by
    have hU : k52U (k52Jx hj) y = k52Jx hj * k52C (k52Jx hj) y := by
      simp only [k52C]; group
    rw [hU]
    rfl
  rcases CFSG.GF2Type.Aschbacher1976Full.Z4Q8.mem_zpowers_two h.1 hc_zp with h1 | hz
  · left; rw [← hUcoe, hUc, h1, mul_one]
  · right; rw [← hUcoe, hUc, hz]

private def k52GoodSet (h : Tim79a.ParrottHyp z) (j' : G) : Set ↥(H z) :=
  {y | ∃ e ∈ Subgroup.zpowers z, (y : G) * j' * (y : G)⁻¹ = j' * e}

private theorem k52GoodSet_mul (h : Tim79a.ParrottHyp z) (j' : G) (y u : ↥(H z))
    (hy : y ∈ k52GoodSet h j') (hu : u ∈ k52GoodSet h j') :
    y * u ∈ k52GoodSet h j' := by
  simp only [k52GoodSet, Set.mem_setOf_eq] at hy hu ⊢
  rcases hy with ⟨e, he, hy⟩
  rcases hu with ⟨f, hf, hu⟩
  refine ⟨e * f, Subgroup.mul_mem _ he hf, ?_⟩
  have hyu : ((y * u : ↥(H z)) : G) * j' * ((y * u : ↥(H z)) : G)⁻¹ =
      (y : G) * ((u : G) * j' * (u : G)⁻¹) * (y : G)⁻¹ := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rw [hyu, hu]
  have hfy : (y : G) * f = f * (y : G) :=
    Subgroup.mem_centralizer_iff.mp (zpowers_centralizes_H h hf) (y : G) y.2
  have hfy' : f * (y : G)⁻¹ = (y : G)⁻¹ * f := by
    have := congrArg (fun t => (y : G)⁻¹ * t * (y : G)⁻¹) hfy
    simpa [mul_assoc] using this
  calc (y : G) * (j' * f) * (y : G)⁻¹
      = (y : G) * j' * (f * (y : G)⁻¹) := by group
    _ = (y : G) * j' * ((y : G)⁻¹ * f) := by rw [hfy']
    _ = ((y : G) * j' * (y : G)⁻¹) * f := by group
    _ = (j' * e) * f := by rw [hy]
    _ = j' * (e * f) := by group

private theorem k52GoodSet_inv (h : Tim79a.ParrottHyp z) (j' : G) (y : ↥(H z))
    (hy : y ∈ k52GoodSet h j') : y⁻¹ ∈ k52GoodSet h j' := by
  simp only [k52GoodSet, Set.mem_setOf_eq] at hy ⊢
  rcases hy with ⟨e, he, hy⟩
  refine ⟨e⁻¹, Subgroup.inv_mem _ he, ?_⟩
  have hey : (e : G) * (y : G) = (y : G) * e :=
    (Subgroup.mem_centralizer_iff.mp (zpowers_centralizes_H h he) (y : G) y.2).symm
  have h3 : ((y : G)⁻¹ * j' * (y : G)) * e = j' := by
    have hey' : (y : G) * e = e * (y : G) := hey.symm
    calc (y : G)⁻¹ * j' * (y : G) * e
        = (y : G)⁻¹ * j' * ((y : G) * e) := by group
      _ = (y : G)⁻¹ * j' * (e * (y : G)) := by rw [hey']
      _ = (y : G)⁻¹ * (j' * e) * (y : G) := by group
      _ = (y : G)⁻¹ * ((y : G) * j' * (y : G)⁻¹) * (y : G) := by rw [hy]
      _ = j' := by group
  have h4 : (y : G)⁻¹ * j' * (y : G) = j' * e⁻¹ := by
    have := congrArg (fun t => t * (e : G)⁻¹) h3
    simpa [mul_assoc] using this
  simpa using h4

private def k52GoodSubgroup (h : Tim79a.ParrottHyp z) (j' : G) : Subgroup ↥(H z) where
  carrier := k52GoodSet h j'
  mul_mem' := fun {y u} hy hu => k52GoodSet_mul h j' y u hy hu
  one_mem' := ⟨1, Subgroup.one_mem _, by simp⟩
  inv_mem' := fun {y} hy => k52GoodSet_inv h j' y hy

private theorem J_le_goodSubgroup (h : Tim79a.ParrottHyp z) {j' : G} (hj' : j' ∈ J z) :
    (J z).subgroupOf (H z) ≤ k52GoodSubgroup h j' := by
  intro y hy
  simp only [k52GoodSubgroup, k52GoodSet, Set.mem_setOf_eq]
  have hyJ : (y : G) ∈ J z := Subgroup.mem_subgroupOf.mp hy
  have hc := commutator_mem_zpowers_z h hyJ hj'
  refine ⟨⁅(y : G), j'⁆, hc, ?_⟩
  have hcc : ⁅(y : G), j'⁆ * j' = j' * ⁅(y : G), j'⁆ :=
    (Subgroup.mem_centralizer_iff.mp (zpowers_centralizes_J h hc) j' hj').symm
  calc (y : G) * j' * (y : G)⁻¹
      = ((y : G) * j' * (y : G)⁻¹ * j'⁻¹) * j' := by group
    _ = (⁅(y : G), j'⁆) * j' := by rw [commutatorElement_def]
    _ = j' * ⁅(y : G), j'⁆ := hcc

private theorem gen_mem_goodSubgroup (h : Tim79a.ParrottHyp z) {v₀ : QuotientV.V z}
    (hgen : ∀ y ∈ ({uH D, vH D, a1H D, b1H D, a2H D, b2H D} : Set ↥(H z)),
      conjV h y v₀ = v₀ ∧ ∃ x : ↥(H z), conjZ z x = 1 ∧ qH D x ^ 3 = 1 ∧
        (qH D y * qH D x * (qH D y)⁻¹ = qH D x ∨
          qH D y * qH D x * (qH D y)⁻¹ = (qH D x)⁻¹) ∧
        v₀ * conjV h x v₀ * conjV h x (conjV h x v₀) = 1)
    {j' : G} (hj' : j' ∈ J z) (hπj' : QuotientV.pi z ⟨j', hj'⟩ = v₀) :
    ({uH D, vH D, a1H D, b1H D, a2H D, b2H D} : Set ↥(H z)) ⊆ k52GoodSubgroup h j' := by
  intro y hy
  obtain ⟨hyv, x, hxZ, hx3, hyx, htr⟩ := hgen y hy
  have hmain := conj_eq_or_eq_mul_z_of_trace D h hj' hxZ hx3 hyx
    (by rw [hπj']; exact hyv)
    (by rw [hπj']; exact htr)
  rcases hmain with h1 | h1
  · simp only [k52GoodSubgroup, k52GoodSet, Set.mem_setOf_eq]
    exact ⟨1, Subgroup.one_mem _, by rw [h1, mul_one]⟩
  · simp only [k52GoodSubgroup, k52GoodSet, Set.mem_setOf_eq]
    exact ⟨z, Subgroup.mem_zpowers z, by rw [h1]⟩

private theorem sylowTwoH_le_goodSubgroup (h : Tim79a.ParrottHyp z) {v₀ : QuotientV.V z}
    (hgen : ∀ y ∈ ({uH D, vH D, a1H D, b1H D, a2H D, b2H D} : Set ↥(H z)),
      conjV h y v₀ = v₀ ∧ ∃ x : ↥(H z), conjZ z x = 1 ∧ qH D x ^ 3 = 1 ∧
        (qH D y * qH D x * (qH D y)⁻¹ = qH D x ∨
          qH D y * qH D x * (qH D y)⁻¹ = (qH D x)⁻¹) ∧
        v₀ * conjV h x v₀ * conjV h x (conjV h x v₀) = 1)
    {j' : G} (hj' : j' ∈ J z) (hπj' : QuotientV.pi z ⟨j', hj'⟩ = v₀) :
    sylowTwoH D ≤ k52GoodSubgroup h j' := by
  rw [sylowTwoH]
  exact sup_le (J_le_goodSubgroup h hj')
    ((Subgroup.closure_le (k52GoodSubgroup h j')).mpr
      (gen_mem_goodSubgroup D h hgen hj' hπj'))

private def k52JH {j' : G} (hj' : j' ∈ J z) : ↥(H z) := ⟨j', J_le_H hj'⟩

private def k52ZH (z : G) : ↥(H z) := ⟨z, z_mem_H⟩

private noncomputable def k52CT (D : QuotientData (z := z) hN) {j' : G} (hj' : j' ∈ J z) : Subgroup ↥(H z) :=
  sylowTwoH D ⊓ Subgroup.centralizer ({k52JH hj'} : Set ↥(H z))

private theorem k52_hfmem (h : Tim79a.ParrottHyp z) {j' : G} (hj' : j' ∈ J z)
    (hTgood : sylowTwoH D ≤ k52GoodSubgroup h j') :
    ∀ y : ↥(sylowTwoH D), y.1 * k52JH hj' * y.1⁻¹ = k52JH hj' ∨
      y.1 * k52JH hj' * y.1⁻¹ = k52JH hj' * k52ZH z := by
  intro y
  have hygood : y.1 ∈ k52GoodSubgroup h j' := hTgood y.2
  simp only [k52GoodSubgroup, k52GoodSet, Set.mem_setOf_eq] at hygood
  rcases hygood with ⟨e, he, heq⟩
  have heJ : e ∈ J z := Subgroup.zpowers_le_of_mem (z_mem_J h) he
  let eH : ↥(H z) := ⟨e, J_le_H heJ⟩
  have heqH : y.1 * k52JH hj' * y.1⁻¹ = k52JH hj' * eH := by
    apply Subtype.ext
    simpa [k52JH, eH] using heq
  rcases CFSG.GF2Type.Aschbacher1976Full.Z4Q8.mem_zpowers_two h.1 he with h1 | hz
  · left
    rw [heqH, show eH = 1 from Subtype.ext h1, mul_one]
  · right
    rw [heqH, show eH = k52ZH z from Subtype.ext hz]

private theorem k52_hconj (h : Tim79a.ParrottHyp z) {j' : G} (hj' : j' ∈ J z)
    (hzH2 : k52ZH z * k52ZH z = 1) :
    ∀ a b : ↥(H z), a * k52JH hj' * a⁻¹ = k52JH hj' * k52ZH z →
      b * k52JH hj' * b⁻¹ = k52JH hj' * k52ZH z →
      (a⁻¹ * b) * k52JH hj' * (a⁻¹ * b)⁻¹ = k52JH hj' := by
  intro a b ha hb
  have hzHcent : ∀ w : ↥(H z), k52ZH z * w = w * k52ZH z := by
    intro w
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp
      (zpowers_centralizes_H h (Subgroup.mem_zpowers z)) (w : G) w.2).symm
  have hstep : a⁻¹ * (k52JH hj' * k52ZH z) * a = (a⁻¹ * k52JH hj' * a) * k52ZH z := by
    calc a⁻¹ * (k52JH hj' * k52ZH z) * a = (a⁻¹ * k52JH hj') * (k52ZH z * a) := by group
      _ = (a⁻¹ * k52JH hj') * (a * k52ZH z) := by rw [hzHcent a]
      _ = (a⁻¹ * k52JH hj' * a) * k52ZH z := by group
  have hA : a⁻¹ * k52JH hj' * a = k52JH hj' * k52ZH z := by
    have h2 : k52JH hj' = (a⁻¹ * k52JH hj' * a) * k52ZH z := by
      calc k52JH hj' = a⁻¹ * (a * k52JH hj' * a⁻¹) * a := by group
        _ = a⁻¹ * (k52JH hj' * k52ZH z) * a := by rw [ha]
        _ = (a⁻¹ * k52JH hj' * a) * k52ZH z := hstep
    have := congrArg (fun t => t * k52ZH z) h2
    simpa [mul_assoc, hzH2] using this.symm
  calc (a⁻¹ * b) * k52JH hj' * (a⁻¹ * b)⁻¹
      = a⁻¹ * (b * k52JH hj' * b⁻¹) * a := by group
    _ = a⁻¹ * (k52JH hj' * k52ZH z) * a := by rw [hb]
    _ = (a⁻¹ * k52JH hj' * a) * k52ZH z := hstep
    _ = (k52JH hj' * k52ZH z) * k52ZH z := by rw [hA]
    _ = k52JH hj' := by rw [mul_assoc, hzH2, mul_one]

private theorem k52_injection_exists (h : Tim79a.ParrottHyp z) {j' : G} (hj' : j' ∈ J z)
    (hTgood : sylowTwoH D ≤ k52GoodSubgroup h j')
    (hzH2 : k52ZH z * k52ZH z = 1)
    {y₀ : ↥(sylowTwoH D)}
    (hy₀ : y₀.1 * k52JH hj' * y₀.1⁻¹ = k52JH hj' * k52ZH z) :
    Nat.card ↥(sylowTwoH D) ≤ Nat.card ↥(k52CT D hj') * 2 := by
  classical
  have hfmem := k52_hfmem D h hj' hTgood
  have hconj := k52_hconj h hj' hzH2
  let F : ↥(sylowTwoH D) → ↥(k52CT D hj') × Fin 2 := fun y =>
    if h : y.1 * k52JH hj' * y.1⁻¹ = k52JH hj' then
      (⟨y.1, by
          rw [k52CT]
          refine Subgroup.mem_inf.mpr ⟨y.2, ?_⟩
          refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
          calc y.1 * k52JH hj' = (y.1 * k52JH hj' * y.1⁻¹) * y.1 := by group
            _ = k52JH hj' * y.1 := by rw [h]⟩, 0)
    else
      (⟨y₀.1⁻¹ * y.1, by
          rw [k52CT]
          refine Subgroup.mem_inf.mpr
            ⟨(sylowTwoH D).mul_mem ((sylowTwoH D).inv_mem y₀.2) y.2, ?_⟩
          have hyz : y.1 * k52JH hj' * y.1⁻¹ = k52JH hj' * k52ZH z :=
            (hfmem y).resolve_left h
          refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
          calc (y₀.1⁻¹ * y.1) * k52JH hj'
              = ((y₀.1⁻¹ * y.1) * k52JH hj' * (y₀.1⁻¹ * y.1)⁻¹) *
                  (y₀.1⁻¹ * y.1) := by group
            _ = k52JH hj' * (y₀.1⁻¹ * y.1) := by rw [hconj y₀.1 y.1 hy₀ hyz]⟩, 1)
  have hinj : Function.Injective F := by
    intro a b hab
    by_cases ha : a.1 * k52JH hj' * a.1⁻¹ = k52JH hj'
    · by_cases hb : b.1 * k52JH hj' * b.1⁻¹ = k52JH hj'
      · have h1 := congrArg (fun p : ↥(k52CT D hj') × Fin 2 => (p.1 : ↥(k52CT D hj'))) hab
        simp only [F, dif_pos ha, dif_pos hb] at h1
        exact Subtype.ext (congrArg (fun x : ↥(k52CT D hj') => (x : ↥(H z))) h1)
      · exfalso
        have h2 := congrArg (fun p : ↥(k52CT D hj') × Fin 2 => p.2) hab
        simp only [F, dif_pos ha, dif_neg hb] at h2
        exact absurd h2 (by decide)
    · by_cases hb : b.1 * k52JH hj' * b.1⁻¹ = k52JH hj'
      · exfalso
        have h2 := congrArg (fun p : ↥(k52CT D hj') × Fin 2 => p.2) hab
        simp only [F, dif_neg ha, dif_pos hb] at h2
        exact absurd h2 (by decide)
      · have h1 := congrArg (fun p : ↥(k52CT D hj') × Fin 2 => (p.1 : ↥(k52CT D hj'))) hab
        simp only [F, dif_neg ha, dif_neg hb] at h1
        have h2 : y₀.1⁻¹ * a.1 = y₀.1⁻¹ * b.1 :=
          congrArg (fun x : ↥(k52CT D hj') => (x : ↥(H z))) h1
        exact Subtype.ext (mul_left_cancel h2)
  have h := Nat.card_le_card_of_injective F hinj
  simpa [Nat.card_prod, Nat.card_fin] using h

private theorem k52_injection_none (h : Tim79a.ParrottHyp z) {j' : G} (hj' : j' ∈ J z)
    (hTgood : sylowTwoH D ≤ k52GoodSubgroup h j')
    (hex : ¬ ∃ y : ↥(sylowTwoH D), y.1 * k52JH hj' * y.1⁻¹ = k52JH hj' * k52ZH z) :
    Nat.card ↥(sylowTwoH D) ≤ Nat.card ↥(k52CT D hj') * 2 := by
  classical
  push Not at hex
  have hfmem := k52_hfmem D h hj' hTgood
  let F : ↥(sylowTwoH D) → ↥(k52CT D hj') × Fin 2 := fun y =>
    (⟨y.1, by
        rw [k52CT]
        refine Subgroup.mem_inf.mpr ⟨y.2, ?_⟩
        have hyj : y.1 * k52JH hj' * y.1⁻¹ = k52JH hj' := (hfmem y).resolve_right (hex y)
        refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
        calc y.1 * k52JH hj' = (y.1 * k52JH hj' * y.1⁻¹) * y.1 := by group
          _ = k52JH hj' * y.1 := by rw [hyj]⟩, 0)
  have hinj : Function.Injective F := by
    intro a b hab
    have h1 := congrArg (fun p : ↥(k52CT D hj') × Fin 2 => (p.1 : ↥(k52CT D hj'))) hab
    simp only [F] at h1
    exact Subtype.ext (congrArg (fun x : ↥(k52CT D hj') => (x : ↥(H z))) h1)
  have h := Nat.card_le_card_of_injective F hinj
  simpa [Nat.card_prod, Nat.card_fin] using h

private theorem k52_injection (h : Tim79a.ParrottHyp z) {j' : G} (hj' : j' ∈ J z)
    (hTgood : sylowTwoH D ≤ k52GoodSubgroup h j') (hzH2 : k52ZH z * k52ZH z = 1) :
    Nat.card ↥(sylowTwoH D) ≤ Nat.card ↥(k52CT D hj') * 2 := by
  by_cases hex : ∃ y : ↥(sylowTwoH D), y.1 * k52JH hj' * y.1⁻¹ = k52JH hj' * k52ZH z
  · obtain ⟨y₀, hy₀⟩ := hex
    exact k52_injection_exists D h hj' hTgood hzH2 hy₀
  · exact k52_injection_none D h hj' hTgood hex

private theorem k52_ct_sixteen (h : Tim79a.ParrottHyp z) {j' : G} (hj' : j' ∈ J z)
    (hTgood : sylowTwoH D ≤ k52GoodSubgroup h j') :
    (2 : ℕ) ^ 16 ≤ Nat.card ↥(k52CT D hj') := by
  have hz2 : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rwa [h.1, pow_two] at this
  have hzH2 : k52ZH z * k52ZH z = 1 := by
    apply Subtype.ext
    exact hz2
  have hle := k52_injection D h hj' hTgood hzH2
  rw [card_sylowTwoH D h] at hle
  have h2 : (2:ℕ)^17 = 2^16 * 2 := by norm_num
  rw [h2] at hle
  omega

private theorem two_pow_sixteen_le_card_CT (h : Tim79a.ParrottHyp z) {j' : G} (hj' : j' ∈ J z)
    (hTgood : sylowTwoH D ≤ k52GoodSubgroup h j') :
    (2 : ℕ) ^ 16 ≤ Nat.card ↥(sylowTwoH D ⊓
      Subgroup.centralizer ({⟨j', J_le_H hj'⟩} : Set ↥(H z))) := by
  simpa [k52CT, k52JH] using k52_ct_sixteen D h hj' hTgood

private theorem k52_find_j' (h : Tim79a.ParrottHyp z) {v₀ : QuotientV.V z}
    (htrans : ∀ v : QuotientV.V z, v ≠ 1 → qVZMod h v = 0 → ∃ g : ↥(H z), conjV h g v = v₀)
    {j : G} (hj : j ∈ J z) (hj2 : orderOf j = 2) (hjZ : j ∉ centerIn (J z)) :
    ∃ (g : ↥(H z)) (j' : G) (hj' : j' ∈ J z),
      j' = (g : G) * j * (g : G)⁻¹ ∧ QuotientV.pi z ⟨j', hj'⟩ = v₀ := by
  have hj2' : (j : G) * j = 1 := by
    have := pow_orderOf_eq_one j
    rwa [hj2, pow_two] at this
  have hjπ : QuotientV.pi z ⟨j, hj⟩ ≠ 1 := by
    intro h1
    exact hjZ ((pi_eq_one_iff_mem_centerIn hj).mp h1)
  have hjq : qVZMod h (QuotientV.pi z ⟨j, hj⟩) = 0 := by
    have hq : qJ h ⟨j, hj⟩ = 1 := by
      apply Subtype.ext
      rw [qJ_coe, pow_two, hj2']
      rfl
    unfold qVZMod
    rw [qV_pi, hq, map_one]
    simp
  obtain ⟨g, hg⟩ := htrans (QuotientV.pi z ⟨j, hj⟩) hjπ hjq
  refine ⟨g, (g : G) * j * (g : G)⁻¹, ?_, rfl, ?_⟩
  · exact H_conj_mem_J g hj
  · rw [← hg, conjV_mk]
    congr 1

private theorem k52_dvd_Cj' (h : Tim79a.ParrottHyp z) {j' : G} (hj' : j' ∈ J z)
    (hCT16 : (2:ℕ) ^ 16 ≤ Nat.card ↥(k52CT D hj')) :
    (2:ℕ) ^ 16 ∣ Nat.card ↥(H z ⊓ Subgroup.centralizer ({j'} : Set G)) := by
  have hCT_pgroup : IsPGroup 2 (k52CT D hj') :=
    (isPGroup_sylowTwoH D h).to_le inf_le_left
  obtain ⟨n, hn⟩ := hCT_pgroup.exists_card_eq
  have hn16 : 16 ≤ n := by
    have h2 : (2:ℕ) ^ 16 ≤ 2 ^ n := by rwa [hn] at hCT16
    exact (pow_le_pow_iff_right₀ (by norm_num : 1 < 2)).mp h2
  have hdvdCT : (2:ℕ) ^ 16 ∣ Nat.card ↥(k52CT D hj') := by
    rw [hn]
    exact Nat.pow_dvd_pow 2 hn16
  have hCTleCj' : ((k52CT D hj').map (H z).subtype) ≤
      H z ⊓ Subgroup.centralizer ({j'} : Set G) := by
    rintro x ⟨y, hy, rfl⟩
    rw [k52CT] at hy
    refine Subgroup.mem_inf.mpr ⟨y.2, ?_⟩
    have hyc : (y : ↥(H z)) * k52JH hj' = k52JH hj' * y :=
      Subgroup.mem_centralizer_singleton_iff.mp hy.2
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    exact congrArg Subtype.val hyc
  have h1 : Nat.card ↥((k52CT D hj').map (H z).subtype) = Nat.card ↥(k52CT D hj') :=
    Subgroup.card_map_of_injective (K := k52CT D hj') (H z).subtype_injective
  rw [← h1] at hdvdCT
  exact hdvdCT.trans (Subgroup.card_dvd_of_le hCTleCj')

private theorem k52_map_inf_centralizer {j j' g : G} (hgH : g ∈ H z)
    (hj'def : j' = g * j * g⁻¹) :
    (H z ⊓ Subgroup.centralizer ({j} : Set G)).map (MulAut.conj g).toMonoidHom =
      H z ⊓ Subgroup.centralizer ({j'} : Set G) := by
  let φ : MulAut G := MulAut.conj g
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hxe : φ.toMonoidHom y = g * y * g⁻¹ := MulAut.conj_apply g y
    rw [hxe]
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · exact (H z).mul_mem ((H z).mul_mem hgH hy.1) (inv_mem hgH)
    · have hyc : y * j = j * y := Subgroup.mem_centralizer_singleton_iff.mp hy.2
      refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
      rw [hj'def]
      calc (g * y * g⁻¹) * (g * j * g⁻¹) = g * (y * j) * g⁻¹ := by group
        _ = g * (j * y) * g⁻¹ := by rw [hyc]
        _ = (g * j * g⁻¹) * (g * y * g⁻¹) := by group
  · intro hx
    have hxe : φ.symm x = g⁻¹ * x * g := MulAut.conj_symm_apply g x
    refine ⟨φ.symm x, ?_, ?_⟩
    · rw [hxe]
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · exact (H z).mul_mem ((H z).mul_mem (inv_mem hgH) hx.1) hgH
      · have hxc : x * j' = j' * x := Subgroup.mem_centralizer_singleton_iff.mp hx.2
        refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
        rw [hj'def] at hxc
        calc g⁻¹ * x * g * j
            = g⁻¹ * (x * (g * j * g⁻¹)) * g := by group
          _ = g⁻¹ * ((g * j * g⁻¹) * x) * g := by rw [hxc]
          _ = j * (g⁻¹ * x * g) := by group
    · exact MulEquiv.apply_symm_apply φ x

private theorem k52_card_eq_conj {j j' g : G} (hgH : g ∈ H z) (hj'def : j' = g * j * g⁻¹) :
    Nat.card ↥(H z ⊓ Subgroup.centralizer ({j} : Set G)) =
      Nat.card ↥(H z ⊓ Subgroup.centralizer ({j'} : Set G)) := by
  have hcardmap : Nat.card ↥((H z ⊓ Subgroup.centralizer ({j} : Set G)).map
        (MulAut.conj g).toMonoidHom) =
      Nat.card ↥(H z ⊓ Subgroup.centralizer ({j} : Set G)) :=
    Subgroup.card_map_of_injective (K := H z ⊓ Subgroup.centralizer ({j} : Set G))
      (MulAut.conj g).injective
  rw [k52_map_inf_centralizer hgH hj'def] at hcardmap
  exact hcardmap.symm

private theorem k52_factorization_ge_sixteen {j j' : G}
    (hcard_eq : Nat.card ↥(H z ⊓ Subgroup.centralizer ({j} : Set G)) =
      Nat.card ↥(H z ⊓ Subgroup.centralizer ({j'} : Set G)))
    (hdvd : (2:ℕ) ^ 16 ∣ Nat.card ↥(H z ⊓ Subgroup.centralizer ({j'} : Set G))) :
    16 ≤ (Nat.card ↥(H z ⊓ Subgroup.centralizer ({j} : Set G))).factorization 2 := by
  have hne : Nat.card ↥(H z ⊓ Subgroup.centralizer ({j} : Set G)) ≠ 0 :=
    Nat.card_pos.ne'
  refine (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hne).mp ?_
  rw [hcard_eq]
  exact hdvd

theorem two_pow_sixteen_le_card_of_isSylowOf_centralizer (h : Tim79a.ParrottHyp z)
    {v₀ : QuotientV.V z}
    (htrans : ∀ v : QuotientV.V z, v ≠ 1 → qVZMod h v = 0 → ∃ g : ↥(H z), conjV h g v = v₀)
    (hgen : ∀ y ∈ ({uH D, vH D, a1H D, b1H D, a2H D, b2H D} : Set ↥(H z)),
      conjV h y v₀ = v₀ ∧ ∃ x : ↥(H z), conjZ z x = 1 ∧ qH D x ^ 3 = 1 ∧
        (qH D y * qH D x * (qH D y)⁻¹ = qH D x ∨
          qH D y * qH D x * (qH D y)⁻¹ = (qH D x)⁻¹) ∧
        v₀ * conjV h x v₀ * conjV h x (conjV h x v₀) = 1)
    {j : G} (hj : j ∈ J z) (hj2 : orderOf j = 2) (hjZ : j ∉ centerIn (J z))
    {K : Subgroup G} (hK : IsSylowOf 2 K (H z ⊓ centralizer ({j} : Set G))) :
    2 ^ 16 ≤ Nat.card K := by
  obtain ⟨g, j', hj', hj'def, hπj'⟩ := k52_find_j' h htrans hj hj2 hjZ
  have hTgood : sylowTwoH D ≤ k52GoodSubgroup h j' :=
    sylowTwoH_le_goodSubgroup D h hgen hj' hπj'
  have hCT0 := two_pow_sixteen_le_card_CT D h hj' hTgood
  have hCT16 : (2:ℕ) ^ 16 ≤ Nat.card ↥(k52CT D hj') := by
    simpa [k52CT, k52JH] using hCT0
  have hdvdCj' := k52_dvd_Cj' D h hj' hCT16
  have hcard_eq := k52_card_eq_conj (z := z) g.2 hj'def
  have hdvdCj : (2:ℕ) ^ 16 ∣
      Nat.card ↥(H z ⊓ Subgroup.centralizer ({j} : Set G)) := by
    rw [hcard_eq]; exact hdvdCj'
  have hfac := k52_factorization_ge_sixteen hcard_eq hdvdCj'
  calc (2:ℕ) ^ 16
      ≤ 2 ^ (Nat.card ↥(H z ⊓ Subgroup.centralizer ({j} : Set G))).factorization 2 :=
        Nat.pow_le_pow_right (by norm_num) hfac
    _ = Nat.card K := (hK.card_eq).symm
