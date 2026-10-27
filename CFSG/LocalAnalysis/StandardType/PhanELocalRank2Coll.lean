module

public import CFSG.LocalAnalysis.StandardType.PhanELocalModels
import CFSG.LocalAnalysis.StandardType.PhanELocalPlane
import CFSG.LocalAnalysis.StandardType.PhanELocalSigma
import CFSG.LocalAnalysis.StandardType.PhanELocalGate
public import CFSG.Certificates.Kernel.ThDemp.OrbCent
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanEDefs
public import CFSG.LocalAnalysis.StandardType.PhanEReduction

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE

open CFSG.Monster.B.Geometry Module

section

variable {K : Type} [Field K] [Finite K] {f : ℕ} [CharP K 2]

private theorem plco_blockU_a2coll (E : ℕ → Submodule K (Fin 3 → K)) (r : ℕ) :
    blockU K 3 [0, 3] E 0 r = E r := by
  show (E (3 - [0, 3].getD (0 + 1) 0 + r) ⊓ Vsub 3 ([0, 3].getD (0 + 1) 0)) ⊔
      Vsub 3 ([0, 3].getD 0 0) = E r
  rw [show [0, 3].getD (0 + 1) 0 = 3 by decide, show [0, 3].getD 0 0 = 0 by decide]
  simp only [Vsub_self, Vsub_zero, inf_top_eq, sup_bot_eq]
  congr 1
  omega

private theorem plco_mem_genSet_iff (hK : Nat.card K = (2 ^ f) ^ 2) (x : FlagK K 3) :
    x ∈ genSet K f 3 [0, 3] [false] ↔ x.E 1 ⊓ sgS K f 3 (x.E 2) = ⊥ := by
  have hle : ∀ i, i < [0, 3].length → [0, 3].getD i 0 ≤ 3 := by
    intro i hi
    have hi2 : i < 2 := by simpa using hi
    interval_cases i <;> decide
  have hmono : ∀ i, i + 1 < [0, 3].length → [0, 3].getD i 0 ≤ [0, 3].getD (i + 1) 0 := by
    intro i hi
    have hi1 : i < 1 := by
      have : i + 1 < 2 := by simpa using hi
      omega
    interval_cases i
    decide
  have hfar : x ∈ farSet 3 [0, 3] := by
    intro i hi j hj
    have hi2 : i < 2 := by simpa using hi
    interval_cases i
    · show finrank K ↥(x.E j ⊓ Vsub 3 ([0, 3].getD 0 0)) = j + [0, 3].getD 0 0 - 3
      rw [show [0, 3].getD 0 0 = 0 by decide, Vsub_zero, inf_bot_eq, finrank_bot]
      omega
    · show finrank K ↥(x.E j ⊓ Vsub 3 ([0, 3].getD 1 0)) = j + [0, 3].getD 1 0 - 3
      rw [show [0, 3].getD 1 0 = 3 by decide, Vsub_self, inf_top_eq, x.dim j hj]
      omega
  rw [genSet, Set.mem_setOf_eq]
  constructor
  · rintro ⟨-, hok⟩
    have h1 := (blockOK_iff_of_far f hle hmono hfar (i := 0) (by decide)).mp
      (hok 0 (by decide))
    have h1' := h1 1 (by decide) (by decide)
    simpa [plco_blockU_a2coll, Vsub_zero, show (3 - 0 - 1 : ℕ) = 2 by decide] using h1'
  · intro h1
    refine ⟨hfar, ?_⟩
    intro i hi
    have hi0 : i = 0 := by
      have : i + 1 < 2 := by simpa using hi
      omega
    subst hi0
    refine (blockOK_iff_of_far f hle hmono hfar (i := 0) (by decide)).mpr ?_
    intro r hr0 hrm
    have hr3 : r < 3 := by simpa using hrm
    interval_cases r
    · simpa [plco_blockU_a2coll, Vsub_zero, show (3 - 0 - 1 : ℕ) = 2 by decide] using h1
    · have h2 : sgS K f 3 (x.E 1 ⊓ sgS K f 3 (x.E 2)) =
          sgS K f 3 (⊥ : Submodule K (Fin 3 → K)) := by rw [h1]
      rw [sgS_inf, sgS_sgS hK (x.E 2), sgS_bot hK] at h2
      have : x.E 2 ⊓ sgS K f 3 (x.E 1) = ⊥ := by
        rw [inf_comm]
        exact h2
      simpa [plco_blockU_a2coll, Vsub_zero, show (3 - 0 - 2 : ℕ) = 1 by decide] using this

private theorem plco_inf_sgS_bot_iff (hK : Nat.card K = (2 ^ f) ^ 2)
    {p m : Submodule K (Fin 3 → K)} (hp : finrank K p = 1) (hm : finrank K m = 2)
    (hpm : p ≤ m) :
    p ⊓ sgS K f 3 m = ⊥ ↔ sgS K f 3 p ≠ p ∧ sgS K f 3 m ≠ m := by
  constructor
  · intro hbot
    constructor
    · intro hsp
      have hle : p ≤ sgS K f 3 m := by
        rw [← hsp]
        exact sgS_mono hpm
      have hpb : p ≤ ⊥ := by
        rw [← hbot]
        exact le_inf le_rfl hle
      have hpbot : p = ⊥ := le_bot_iff.mp hpb
      have hfin : finrank K p = 0 := by rw [hpbot]; simp
      omega
    · intro hsm
      have hpb : p ≤ ⊥ := by
        rw [← hbot]
        exact le_inf le_rfl (by rw [hsm]; exact hpm)
      have hpbot : p = ⊥ := le_bot_iff.mp hpb
      have hfin : finrank K p = 0 := by rw [hpbot]; simp
      omega
  · rintro ⟨hsp, hsm⟩
    have hfin_sgS : finrank K ↥(sgS K f 3 m) = 2 := by
      rw [finrank_sgS hK m, hm]
    have hI1 : finrank K ↥(m ⊓ sgS K f 3 m) = 1 := by
      have hsum := Submodule.finrank_sup_add_finrank_inf_eq m (sgS K f 3 m)
      have hsum' : finrank K ↥(m ⊔ sgS K f 3 m) + finrank K ↥(m ⊓ sgS K f 3 m) = 4 := by
        rw [hsum, hm, hfin_sgS]
      have htop : finrank K ↥(m ⊔ sgS K f 3 m) ≤ 3 := by
        have := Submodule.finrank_mono (le_top : m ⊔ sgS K f 3 m ≤ ⊤)
        rwa [finrank_top K (Fin 3 → K), Module.finrank_fin_fun K] at this
      have hle_m : finrank K ↥(m ⊓ sgS K f 3 m) ≤ 2 := by
        have := Submodule.finrank_mono (inf_le_left : m ⊓ sgS K f 3 m ≤ m)
        rwa [hm] at this
      have hlt : finrank K ↥(m ⊓ sgS K f 3 m) < 2 := by
        by_contra h
        have hge : 2 ≤ finrank K ↥(m ⊓ sgS K f 3 m) := le_of_not_gt h
        have heq : finrank K ↥(m ⊓ sgS K f 3 m) = 2 := le_antisymm hle_m hge
        have hIm : (m ⊓ sgS K f 3 m) = m :=
          Submodule.eq_of_le_of_finrank_eq inf_le_left (by rw [heq, hm])
        have hle : m ≤ sgS K f 3 m :=
          (le_of_eq hIm.symm).trans inf_le_right
        exact hsm (Submodule.eq_of_le_of_finrank_eq hle (by rw [hfin_sgS, hm])).symm
      omega
    by_contra hne
    have hJle : p ⊓ sgS K f 3 m ≤ p := inf_le_left
    have hJfin : finrank K ↥(p ⊓ sgS K f 3 m) = 1 := by
      have hpos : 0 < finrank K ↥(p ⊓ sgS K f 3 m) := by
        rw [Nat.pos_iff_ne_zero]
        intro h0
        exact hne (Submodule.finrank_eq_zero.mp h0)
      have hle1 : finrank K ↥(p ⊓ sgS K f 3 m) ≤ 1 := by
        have := Submodule.finrank_mono hJle
        rwa [hp] at this
      omega
    have hJp : p ⊓ sgS K f 3 m = p :=
      Submodule.eq_of_le_of_finrank_eq hJle (by rw [hJfin, hp])
    have hpsg : p ≤ sgS K f 3 m := by
      rw [← hJp]
      exact inf_le_right
    have hpI : p ≤ m ⊓ sgS K f 3 m := le_inf hpm hpsg
    have hpIeq : p = m ⊓ sgS K f 3 m :=
      Submodule.eq_of_le_of_finrank_eq hpI (by rw [hp, hI1])
    have : sgS K f 3 p = p := by
      rw [hpIeq, sgS_inf, sgS_sgS hK m, inf_comm]
    exact hsp this

private theorem plco_finrank_sup_one {p z : Submodule K (Fin 3 → K)}
    (hp : finrank K p = 1) (hz : finrank K z = 1) (hne : z ≠ p) :
    finrank K ↥(p ⊔ z) = 2 := by
  have hdisj : p ⊓ z = ⊥ := by
    by_contra h
    have h0 : finrank K ↥(p ⊓ z) ≠ 0 := fun h0 => h (Submodule.finrank_eq_zero.mp h0)
    have hle1 : finrank K ↥(p ⊓ z) ≤ 1 := by
      have := Submodule.finrank_mono (inf_le_left : p ⊓ z ≤ p)
      rwa [hp] at this
    have h1 : finrank K ↥(p ⊓ z) = 1 := by omega
    have e1 : p ⊓ z = p := Submodule.eq_of_le_of_finrank_eq inf_le_left (by rw [h1, hp])
    have e2 : p ⊓ z = z := Submodule.eq_of_le_of_finrank_eq inf_le_right (by rw [h1, hz])
    exact hne (e2.symm.trans e1)
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq p z
  rw [hdisj, finrank_bot, add_zero, hp, hz] at hsum
  exact hsum

private theorem plco_sup_sgS_eq_of (hK : Nat.card K = (2 ^ f) ^ 2)
    {p r : Submodule K (Fin 3 → K)} (hp : finrank K p = 1) (hr : finrank K r = 2)
    (hpr : p ≤ r) (hrat : sgS K f 3 r = r) (hsp : sgS K f 3 p ≠ p) :
    p ⊔ sgS K f 3 p = r := by
  have hle : p ⊔ sgS K f 3 p ≤ r := sup_le hpr (by rw [← hrat]; exact sgS_mono hpr)
  have hfin : finrank K ↥(p ⊔ sgS K f 3 p) = 2 :=
    plco_finrank_sup_one hp (by rw [finrank_sgS hK p, hp]) hsp
  exact Submodule.eq_of_le_of_finrank_eq hle (by rw [hfin, hr])

private theorem plco_sgS_sup_ne (hK : Nat.card K = (2 ^ f) ^ 2)
    {p z : Submodule K (Fin 3 → K)} (hp : finrank K p = 1) (hz : finrank K z = 1)
    (hsp : sgS K f 3 p ≠ p) (hzr : ¬ z ≤ p ⊔ sgS K f 3 p) :
    sgS K f 3 (p ⊔ z) ≠ p ⊔ z := by
  intro hrat
  have hzp : z ≠ p := by
    intro h
    rw [h] at hzr
    exact hzr le_sup_left
  have hfin : finrank K ↥(p ⊔ z) = 2 := plco_finrank_sup_one hp hz hzp
  have hEq : p ⊔ sgS K f 3 p = p ⊔ z :=
    plco_sup_sgS_eq_of hK hp hfin le_sup_left hrat hsp
  exact hzr (hEq.symm ▸ le_sup_right)

private theorem plco_sgS_span_add (hK : Nat.card K = (2 ^ f) ^ 2)
    {u w : Fin 3 → K} {r : Submodule K (Fin 3 → K)}
    (hr : sgS K f 3 r = r) (hw : w ∈ r) (hu : u ∉ r) (hw0 : w ≠ 0)
    (h1 : sgS K f 3 (Submodule.span K {u}) = Submodule.span K {u})
    (h2 : sgS K f 3 (Submodule.span K {u + w}) = Submodule.span K {u + w}) :
    sgS K f 3 (Submodule.span K {w}) = Submodule.span K {w} := by
  have hsgu_mem : sgv K f 3 u ∈ Submodule.span K {u} := by
    have h := h1
    rw [sgS_span_singleton hK u] at h
    exact h.le (Submodule.mem_span_singleton_self (sgv K f 3 u))
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hsgu_mem
  have hsgw_mem : sgv K f 3 (u + w) ∈ Submodule.span K {u + w} := by
    have h := h2
    rw [sgS_span_singleton hK (u + w)] at h
    exact h.le (Submodule.mem_span_singleton_self (sgv K f 3 (u + w)))
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hsgw_mem
  have hsadd : sgv K f 3 (u + w) = sgv K f 3 u + sgv K f 3 w := by
    ext i
    simp [sgv_apply, map_add]
  have hkey : sgv K f 3 u + sgv K f 3 w = c • (u + w) := by
    rw [← hsadd]
    exact hc.symm
  have hsw : sgv K f 3 w ∈ r := by
    have : w ∈ sgS K f 3 r := by rw [hr]; exact hw
    exact mem_sgS.mp this
  have hcw : c • w ∈ r := r.smul_mem c hw
  have hdiff : (a - c) • u ∈ r := by
    have hEq : (a - c) • u = c • w - sgv K f 3 w := by
      rw [show sgv K f 3 w = c • (u + w) - sgv K f 3 u from by
        rw [← hkey, add_sub_cancel_left]]
      rw [← ha, smul_add]
      module
    rw [hEq]
    exact r.sub_mem hcw hsw
  have hd0 : a - c = 0 := by
    by_contra hd
    have hu' : u ∈ r := by
      have hmem : (a - c)⁻¹ • ((a - c) • u) ∈ r := r.smul_mem _ hdiff
      rwa [smul_smul, inv_mul_cancel₀ hd, one_smul] at hmem
    exact hu hu'
  have hac : a = c := sub_eq_zero.mp hd0
  have hsgvw : sgv K f 3 w = c • w := by
    have h := hkey
    rw [← ha, hac, smul_add] at h
    exact add_left_cancel h
  have hc0 : c ≠ 0 := by
    intro hc0
    have hsw0 : sgv K f 3 w = 0 := by rw [hsgvw, hc0, zero_smul]
    have hwzero : w = 0 := by
      have h := congrArg (sgv K f 3) hsw0
      rw [sgv_sgv hK w, map_zero] at h
      exact h
    exact hw0 hwzero
  rw [sgS_span_singleton hK w, hsgvw]
  exact Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr hc0) w

private theorem plco_exists_nonrat_point (hK : Nat.card K = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f)
    {p r : Submodule K (Fin 3 → K)} (hp : finrank K p = 1) (hr : finrank K r = 2)
    (hpr : p ≤ r) (hrat : sgS K f 3 r = r) (hsp : sgS K f 3 p ≠ p) :
    ∃ z : Submodule K (Fin 3 → K), finrank K z = 1 ∧ sgS K f 3 z ≠ z ∧ ¬ z ≤ r := by
  have hrne : r ≠ ⊤ := by
    intro h
    have := hr
    rw [h, finrank_top K (Fin 3 → K), Module.finrank_fin_fun K] at this
    omega
  obtain ⟨u, hu⟩ : ∃ u : Fin 3 → K, u ∉ r := by
    have hnot : ¬ ∀ u : Fin 3 → K, u ∈ r :=
      fun hall => hrne (Submodule.eq_top_iff'.mpr hall)
    exact not_forall.mp hnot
  have hpne : p ≠ ⊥ := by
    intro hpbot
    have : finrank K p = 0 := by rw [hpbot]; simp
    omega
  obtain ⟨w, hwmem, hw0⟩ := (Submodule.ne_bot_iff p).mp hpne
  have hpw : p = Submodule.span K {w} :=
    eq_span_singleton_of_mem_of_finrank_eq_one hp hwmem hw0
  have hwr : w ∈ r := hpr hwmem
  by_cases h1 : sgS K f 3 (Submodule.span K {u}) ≠ Submodule.span K {u}
  · refine ⟨Submodule.span K {u}, ?_, h1, ?_⟩
    · exact finrank_span_singleton (fun hzero => hu (by rw [hzero]; exact r.zero_mem))
    · intro hle
      exact hu (hle (Submodule.mem_span_singleton_self u))
  · have h1rat : sgS K f 3 (Submodule.span K {u}) = Submodule.span K {u} := not_ne_iff.mp h1
    refine ⟨Submodule.span K {u + w}, ?_, ?_, ?_⟩
    · exact finrank_span_singleton (fun hz => hu (by
        have huw : u + w ∈ r := by rw [hz]; exact r.zero_mem
        have hone : u = (u + w) - w := by abel
        rw [hone]
        exact r.sub_mem huw hwr))
    · intro h2rat
      apply hsp
      rw [hpw]
      exact plco_sgS_span_add hK hrat hwr hu hw0 h1rat h2rat
    · intro hle
      apply hu
      have huw : u + w ∈ r := hle (Submodule.mem_span_singleton_self (u + w))
      have hone : u = (u + w) - w := by abel
      rw [hone]
      exact r.sub_mem huw hwr

private theorem plco_hasFl (hK : Nat.card K = (2 ^ f) ^ 2)
    {p m : Submodule K (Fin 3 → K)} (hp : finrank K p = 1) (hm : finrank K m = 2)
    (hpm : p ≤ m) (hsp : sgS K f 3 p ≠ p) (hsm : sgS K f 3 m ≠ m) :
    Plane.HasFl (genSet K f 3 [0, 3] [false]) p m := by
  refine Plane.hasFl_ofChain hp hm hpm ?_
  rw [plco_mem_genSet_iff hK, Plane.ofChain_E_one p m hp hm hpm,
    Plane.ofChain_E_two p m hp hm hpm]
  exact (plco_inf_sgS_bot_iff hK hp hm hpm).mpr ⟨hsp, hsm⟩

end

variable (K : Type) [Field K] [Finite K] (f : ℕ) [CharP K 2]

theorem a2coll_connected (hK : Nat.card K = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f) :
    ((flagSys K 2).restrict (genSet K f 3 [0, 3] [false])).Connected := by
  refine Plane.connected_of_common_nbr _ ?_
  intro x hx y hy
  have hx' := (plco_inf_sgS_bot_iff hK (Plane.finrank_E_one x) (Plane.finrank_E_two x)
    (Plane.E_one_le_two x)).mp ((plco_mem_genSet_iff hK x).mp hx)
  have hy' := (plco_inf_sgS_bot_iff hK (Plane.finrank_E_one y) (Plane.finrank_E_two y)
    (Plane.E_one_le_two y)).mp ((plco_mem_genSet_iff hK y).mp hy)
  by_cases heq : x.E 1 = y.E 1
  · exact ⟨x.E 1, x.E 2, x.E 2, ⟨x, hx, rfl, rfl⟩, ⟨x, hx, rfl, rfl⟩,
      ⟨x, hx, rfl, rfl⟩, ⟨x, hx, heq, rfl⟩⟩
  · by_cases hle : y.E 1 ≤ x.E 1 ⊔ sgS K f 3 (x.E 1)
    · have hr : finrank K ↥(x.E 1 ⊔ sgS K f 3 (x.E 1)) = 2 :=
        plco_finrank_sup_one (Plane.finrank_E_one x)
          (by rw [finrank_sgS hK (x.E 1), Plane.finrank_E_one x]) hx'.1
      have hrat : sgS K f 3 (x.E 1 ⊔ sgS K f 3 (x.E 1)) = x.E 1 ⊔ sgS K f 3 (x.E 1) := by
        rw [sgS_sup hK, sgS_sgS hK, sup_comm]
      obtain ⟨z, hz1, hsz, hzr⟩ :=
        plco_exists_nonrat_point hK hq (Plane.finrank_E_one x) hr le_sup_left hrat hx'.1
      have hzy : z ≠ y.E 1 := by
        intro h
        apply hzr
        rw [← plco_sup_sgS_eq_of hK (Plane.finrank_E_one y) hr hle hrat hy'.1, h]
        exact le_sup_left
      have hzx : z ≠ x.E 1 := by
        intro h
        apply hzr
        rw [h]
        exact le_sup_left
      have hm : finrank K ↥(x.E 1 ⊔ z) = 2 :=
        plco_finrank_sup_one (Plane.finrank_E_one x) hz1 hzx
      have hsm : sgS K f 3 (x.E 1 ⊔ z) ≠ x.E 1 ⊔ z :=
        plco_sgS_sup_ne hK (Plane.finrank_E_one x) hz1 hx'.1 hzr
      have hm' : finrank K ↥(z ⊔ y.E 1) = 2 := by
        rw [sup_comm]
        exact plco_finrank_sup_one (Plane.finrank_E_one y) hz1 hzy
      have hsm' : sgS K f 3 (z ⊔ y.E 1) ≠ z ⊔ y.E 1 := by
        rw [sup_comm]
        refine plco_sgS_sup_ne hK (Plane.finrank_E_one y) hz1 hy'.1 ?_
        rw [plco_sup_sgS_eq_of hK (Plane.finrank_E_one y) hr hle hrat hy'.1]
        exact hzr
      exact ⟨z, x.E 1 ⊔ z, z ⊔ y.E 1,
        plco_hasFl hK (Plane.finrank_E_one x) hm le_sup_left hx'.1 hsm,
        plco_hasFl hK hz1 hm le_sup_right hsz hsm,
        plco_hasFl hK hz1 hm' le_sup_left hsz hsm',
        plco_hasFl hK (Plane.finrank_E_one y) hm' le_sup_right hy'.1 hsm'⟩
    · have hne : y.E 1 ≠ x.E 1 := fun h => heq h.symm
      have hm : finrank K ↥(x.E 1 ⊔ y.E 1) = 2 :=
        plco_finrank_sup_one (Plane.finrank_E_one x) (Plane.finrank_E_one y) hne
      have hsm : sgS K f 3 (x.E 1 ⊔ y.E 1) ≠ x.E 1 ⊔ y.E 1 :=
        plco_sgS_sup_ne hK (Plane.finrank_E_one x) (Plane.finrank_E_one y) hx'.1 hle
      exact ⟨y.E 1, x.E 1 ⊔ y.E 1, x.E 1 ⊔ y.E 1,
        plco_hasFl hK (Plane.finrank_E_one x) hm le_sup_left hx'.1 hsm,
        plco_hasFl hK (Plane.finrank_E_one y) hm le_sup_right hy'.1 hsm,
        plco_hasFl hK (Plane.finrank_E_one y) hm le_sup_right hy'.1 hsm,
        plco_hasFl hK (Plane.finrank_E_one y) hm le_sup_right hy'.1 hsm⟩

end CFSG.ClassicalInvolution.Phan.PhanE

end
