module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3EUniq
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3ESq

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL

namespace F6

namespace GoldAmL3E

open GoldAmL3

open scoped commutatorElement

variable {D : Type*} [Group D] [Finite D] {A B : Subgroup D} {z : D} {V : Subgroup D}

theorem Ctx.V_le_centerQ (c : Ctx A B z V) {v : D} (hv : v ∈ V) : v ∈ centerOf (pCoreOf 2 A) :=
  ⟨c.U_le_Q (le_conjClosure V B hv), Subgroup.mem_centralizer_iff.mpr fun _ hq =>
    (c.V_comm hv hq).symm⟩

namespace Gen

variable {c : Ctx A B z V} (g : Gen c)

omit [Finite D] in
theorem Zcomm {y y' : D} (hy : y ∈ centerOf (pCoreOf 2 A)) (hy' : y' ∈ centerOf (pCoreOf 2 A)) :
    y * y' = y' * y :=
  (Subgroup.mem_centralizer_iff.mp hy.2 y' hy'.1).symm

theorem T_eq_Q_sup_τ : A ⊓ B = pCoreOf 2 A ⊔ Subgroup.zpowers g.τ := by
  have hle : pCoreOf 2 A ⊔ Subgroup.zpowers g.τ ≤ A ⊓ B :=
    sup_le c.Q_le_T (Subgroup.zpowers_le.mpr g.τ_mem)
  have hmul := Subgroup.relIndex_mul_relIndex (pCoreOf 2 A)
    (pCoreOf 2 A ⊔ Subgroup.zpowers g.τ) (A ⊓ B) le_sup_left hle
  rw [c.hyp.gold.relIndex_pCoreOf_T_left] at hmul
  have hdvd : (pCoreOf 2 A ⊔ Subgroup.zpowers g.τ).relIndex (A ⊓ B) ∣ 2 :=
    Dvd.intro_left _ hmul
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
  · exact le_antisymm (Subgroup.relIndex_eq_one.mp h1) hle
  · exfalso
    rw [h2] at hmul
    have h3 : (pCoreOf 2 A).relIndex (pCoreOf 2 A ⊔ Subgroup.zpowers g.τ) = 1 := by omega
    exact g.τ_not_Q ((Subgroup.relIndex_eq_one.mp h3)
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers g.τ)))

@[expose] def nrm (y : D) : D := y * (g.τ * y * g.τ⁻¹)

omit [Finite D] in
theorem nrm_mem_centerQ {y : D} (hy : y ∈ centerOf (pCoreOf 2 A)) :
    g.nrm y ∈ centerOf (pCoreOf 2 A) :=
  (centerOf (pCoreOf 2 A)).mul_mem hy (c.centerQ_conj g.τ_mem.1 hy)

omit [Finite D] in
theorem nrm_mul {y y' : D} (hy : y ∈ centerOf (pCoreOf 2 A))
    (hy' : y' ∈ centerOf (pCoreOf 2 A)) : g.nrm (y * y') = g.nrm y * g.nrm y' := by
  have hc := Zcomm hy' (c.centerQ_conj g.τ_mem.1 hy)
  unfold nrm
  calc y * y' * (g.τ * (y * y') * g.τ⁻¹) = y * (y' * (g.τ * y * g.τ⁻¹)) * (g.τ * y' * g.τ⁻¹) := by
        group
    _ = y * ((g.τ * y * g.τ⁻¹) * y') * (g.τ * y' * g.τ⁻¹) := by rw [hc]
    _ = y * (g.τ * y * g.τ⁻¹) * (y' * (g.τ * y' * g.τ⁻¹)) := by group

theorem nrm_mem_centerT {y : D} (hy : y ∈ centerOf (pCoreOf 2 A)) :
    g.nrm y ∈ centerOf (A ⊓ B) := by
  have hN := g.nrm_mem_centerQ hy
  refine ⟨c.Q_le_T hN.1, ?_⟩
  have hτ : g.τ * g.nrm y * g.τ⁻¹ = g.nrm y := by
    have hsq : g.τ * g.τ ∈ pCoreOf 2 A := g.τ_sq_mem
    have h1 : (g.τ * g.τ) * y = y * (g.τ * g.τ) := Subgroup.mem_centralizer_iff.mp hy.2 _ hsq
    have hc := Zcomm hy (c.centerQ_conj g.τ_mem.1 hy)
    unfold nrm
    calc g.τ * (y * (g.τ * y * g.τ⁻¹)) * g.τ⁻¹
        = (g.τ * y * g.τ⁻¹) * ((g.τ * g.τ) * y * (g.τ * g.τ)⁻¹) := by group
      _ = (g.τ * y * g.τ⁻¹) * y := by rw [h1]; group
      _ = y * (g.τ * y * g.τ⁻¹) := hc.symm
  have hle : A ⊓ B ≤ Subgroup.centralizer ({g.nrm y} : Set D) := by
    rw [g.T_eq_Q_sup_τ]
    refine sup_le (fun q hq => ?_) (Subgroup.zpowers_le.mpr ?_)
    · rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact Subgroup.mem_centralizer_iff.mp hN.2 q hq |>.symm
    · rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact (mul_eq_of_conj_eq hτ).symm
  refine Subgroup.mem_centralizer_iff.mpr fun t ht => ?_
  exact (Subgroup.mem_centralizer_iff.mp (hle ht) _ (Set.mem_singleton _)).symm

omit [Finite D] in
theorem nrm_sq {y : D} (hy : y ∈ centerOf (pCoreOf 2 A)) (hy2 : y * y = 1) :
    g.nrm y * g.nrm y = 1 := by
  have hy' := c.centerQ_conj g.τ_mem.1 hy
  have hc := Zcomm hy hy'
  have h2 : (g.τ * y * g.τ⁻¹) * (g.τ * y * g.τ⁻¹) = 1 := by
    calc (g.τ * y * g.τ⁻¹) * (g.τ * y * g.τ⁻¹) = g.τ * (y * y) * g.τ⁻¹ := by group
      _ = 1 := by rw [hy2]; group
  unfold nrm
  calc y * (g.τ * y * g.τ⁻¹) * (y * (g.τ * y * g.τ⁻¹))
      = y * ((g.τ * y * g.τ⁻¹) * y) * (g.τ * y * g.τ⁻¹) := by group
    _ = y * (y * (g.τ * y * g.τ⁻¹)) * (g.τ * y * g.τ⁻¹) := by rw [← hc]
    _ = (y * y) * ((g.τ * y * g.τ⁻¹) * (g.τ * y * g.τ⁻¹)) := by group
    _ = 1 := by rw [hy2, h2, one_mul]

theorem mem_centerT_of_fixed {y : D} (hy : y ∈ centerOf (pCoreOf 2 A))
    (hτ : g.τ * y * g.τ⁻¹ = y) : y ∈ centerOf (A ⊓ B) := by
  refine ⟨c.Q_le_T hy.1, ?_⟩
  have hle : A ⊓ B ≤ Subgroup.centralizer ({y} : Set D) := by
    rw [g.T_eq_Q_sup_τ]
    refine sup_le (fun q hq => ?_) (Subgroup.zpowers_le.mpr ?_)
    · rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact (Subgroup.mem_centralizer_iff.mp hy.2 q hq).symm
    · rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact (mul_eq_of_conj_eq hτ).symm
  refine Subgroup.mem_centralizer_iff.mpr fun t ht => ?_
  exact (Subgroup.mem_centralizer_iff.mp (hle ht) _ (Set.mem_singleton _)).symm

theorem τ_conj_z₁ : g.τ * g.z₁ * g.τ⁻¹ = g.z₂ := by
  have hV : g.τ * g.z₁ * g.τ⁻¹ ∈ V := c.V_normal g.τ_mem.1 g.z₁_mem
  have hzfix : g.τ * z * g.τ⁻¹ = z := by
    have := Subgroup.mem_centralizer_iff.mp c.hyp.natural.z_mem.2 g.τ g.τ_mem
    rw [this]; group
  rcases g.V_cases hV with e | e | e | e
  · exfalso
    apply g.z₁_ne_one
    have : g.z₁ = g.τ⁻¹ * (g.τ * g.z₁ * g.τ⁻¹) * g.τ := by group
    rw [this, e]; group
  · exfalso
    apply g.z₁_ne_z
    have : g.z₁ = g.τ⁻¹ * (g.τ * g.z₁ * g.τ⁻¹) * g.τ := by group
    rw [this, e]
    calc g.τ⁻¹ * z * g.τ = g.τ⁻¹ * (g.τ * z * g.τ⁻¹) * g.τ := by rw [hzfix]
      _ = z := by group
  · exfalso
    rcases g.fix_tau g.z₁_mem e with h | h
    · exact g.z₁_ne_one h
    · exact g.z₁_ne_z h
  · exact e

include g in
theorem mem_zpowers_of_nrm_eq_one {y : D} (hy : y ∈ centerOf (pCoreOf 2 A)) (hy2 : y * y = 1)
    (hf : g.nrm y = 1) : y ∈ Subgroup.zpowers z := by
  have hτy : g.τ * y * g.τ⁻¹ = y := by
    have h1 : g.τ * y * g.τ⁻¹ = y⁻¹ := eq_inv_of_mul_eq_one_right hf
    rw [h1]; exact inv_eq_of_mul_eq_one_right hy2
  exact g.eq_zpowers_of_centerT_involution (g.mem_centerT_of_fixed hy hτy) hy2

include g in
theorem mem_V_of_centerQ_involution {y : D} (hy : y ∈ centerOf (pCoreOf 2 A)) (hy2 : y * y = 1) :
    y ∈ V := by
  have hN := g.nrm_mem_centerT hy
  have hNz : g.nrm y ∈ Subgroup.zpowers z :=
    g.eq_zpowers_of_centerT_involution hN (g.nrm_sq hy hy2)
  have hzV : Subgroup.zpowers z ≤ V := Subgroup.zpowers_le.mpr c.z_mem_V
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hNz
  rcases zpow_eq_one_or_self c.hyp.natural.z_sq k with h | h
  · exact hzV (g.mem_zpowers_of_nrm_eq_one hy hy2 (by rw [← hk, h]))
  · have hz₁Q : g.z₁ ∈ centerOf (pCoreOf 2 A) := c.V_le_centerQ g.z₁_mem
    have hc := Zcomm hy hz₁Q
    have hnz₁ : g.nrm g.z₁ = z := by
      unfold nrm; rw [g.τ_conj_z₁, g.z₁_mul_z₂]
    have hy'Q : y * g.z₁ ∈ centerOf (pCoreOf 2 A) := (centerOf (pCoreOf 2 A)).mul_mem hy hz₁Q
    have hy'2 : (y * g.z₁) * (y * g.z₁) = 1 := by
      calc (y * g.z₁) * (y * g.z₁) = y * (g.z₁ * y) * g.z₁ := by group
        _ = y * (y * g.z₁) * g.z₁ := by rw [← hc]
        _ = (y * y) * (g.z₁ * g.z₁) := by group
        _ = 1 := by rw [hy2, g.z₁_mul_z₁, one_mul]
    have hf : g.nrm (y * g.z₁) = 1 := by
      rw [g.nrm_mul hy hz₁Q, hnz₁, ← hk, h]
      exact c.z_sq
    have hmem := hzV (g.mem_zpowers_of_nrm_eq_one hy'Q hy'2 hf)
    have e : y = (y * g.z₁) * g.z₁ := by
      rw [mul_assoc, g.z₁_mul_z₁, mul_one]
    rw [e]
    exact V.mul_mem hmem g.z₁_mem

include g in
theorem centerQ_le_V {ζ : D} (hζ : ζ ∈ centerOf (pCoreOf 2 A)) : ζ ∈ V := by
  obtain ⟨n, hn⟩ := (pCoreOf_isPGroup 2 A) ⟨ζ, hζ.1⟩
  have hn' : ζ ^ (2 ^ n) = 1 := by
    have := congrArg Subtype.val hn
    simpa using this
  clear hn
  induction n generalizing ζ with
  | zero =>
    have : ζ = 1 := by simpa using hn'
    rw [this]; exact V.one_mem
  | succ n ih =>
    have hζ2 : ζ * ζ ∈ centerOf (pCoreOf 2 A) := (centerOf (pCoreOf 2 A)).mul_mem hζ hζ
    have h2 : (ζ * ζ) ^ (2 ^ n) = 1 := by
      rw [← pow_two, ← pow_mul, ← pow_succ']
      exact hn'
    have hV := ih hζ2 h2
    exact g.mem_V_of_centerQ_involution hζ (g.sq_eq_one hζ hV)

end Gen

end GoldAmL3E

end F6

end CFSG.Quasithin
