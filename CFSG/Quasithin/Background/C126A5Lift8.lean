module

public import CFSG.Quasithin.Background.C126A5Lift6

set_option linter.unusedSectionVars false

public section

namespace CFSG.Quasithin.C126.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.B6 Equiv
  CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G]

theorem mem_of_pow_three_of_two_element {K : Subgroup G} {q k y : G}
    (hq : q ∈ Subgroup.normalizer (K : Set G)) (hk : k ∈ K) (hy : y = q * k) {m : ℕ}
    (hqm : q ^ 2 ^ m = 1) (hy3 : y ^ 3 = 1) : y ∈ K := by
  set N : Subgroup G := Subgroup.normalizer (K : Set G) with hN
  have hkN : k ∈ N := Subgroup.le_normalizer hk
  have hyN : y ∈ N := hy ▸ N.mul_mem hq hkN
  have hnorm : (K.subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer Subgroup.le_normalizer).2 le_rfl
  let π := QuotientGroup.mk' (K.subgroupOf N)
  have h1 : π ⟨k, hkN⟩ = 1 := (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_subgroupOf.2 hk)
  have h2 : π ⟨y, hyN⟩ = π ⟨q, hq⟩ := by
    have : (⟨y, hyN⟩ : ↥N) = ⟨q, hq⟩ * ⟨k, hkN⟩ := Subtype.ext hy
    rw [this, map_mul, h1, mul_one]
  have h3 : (π ⟨y, hyN⟩) ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨y, hyN⟩ : ↥N) ^ 3 = 1 := Subtype.ext (by simpa using hy3)
    rw [this, map_one]
  have h4 : (π ⟨y, hyN⟩) ^ 2 ^ m = 1 := by
    rw [h2, ← map_pow]
    have : (⟨q, hq⟩ : ↥N) ^ 2 ^ m = 1 := Subtype.ext (by simpa using hqm)
    rw [this, map_one]
  exact Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff _).1 (eq_one_of_pow_three h3 h4))

theorem mem_alt_of_pow_three {g : Perm (Fin 5)} (h : g ^ 3 = 1) :
    g ∈ alternatingGroup (Fin 5) := by
  rw [Equiv.Perm.mem_alternatingGroup]
  have h1 : Equiv.Perm.sign g ^ 3 = 1 := by rw [← map_pow, h, map_one]
  rcases Int.units_eq_one_or (Equiv.Perm.sign g) with h2 | h2
  · exact h2
  · rw [h2] at h1
    exact absurd h1 (by decide)

section CV

variable {V : Subgroup G} (hV : IsElemAbelian 2 V)

theorem cv_pow {g : G} (hg : g ∈ Subgroup.normalizer (V : Set G)) :
    ∀ n : ℕ, cv hV (g ^ n) = (cv hV g) ^ n
  | 0 => by simp [cv_one]
  | n + 1 => by
    rw [pow_succ, cv_mul hV (Subgroup.pow_mem _ hg n) hg, cv_pow hg n, pow_succ]

end CV

theorem Data.th_pow {H T V Y : Subgroup G} {hV : IsElemAbelian 2 V} (d : Data H T V Y hV)
    {φ : MulAut (IntMod V hV)} (hφ : φ ∈ d.L) : ∀ n : ℕ, d.th (φ ^ n) = (d.th φ) ^ n
  | 0 => by simp [d.th_one]
  | n + 1 => by
    rw [pow_succ, d.th_mul (d.L.pow_mem hφ n) hφ, Data.th_pow d hφ n, pow_succ]

namespace Lift

variable {H T M V Y : Subgroup G} {hV : IsElemAbelian 2 V} {s : Setting H T M V Y hV}
  {d : Data H T V Y hV}

namespace XData

variable {x : G} (hx : XData s d x)

include hx

theorem mem_Khat_of_pow_three
    (hRad : twoResidual H ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 H) {y : G}
    (hy : y ∈ A₁ s d) (hyK : y ∈ twoResidual H) (hy3 : y ^ 3 = 1) : y ∈ Khat s d x := by
  have hyH : y ∈ H := (mem_A₁.1 hy).1
  have hyL : cv hV y ∈ d.L := (mem_A₁.1 hy).2
  have hyN : y ∈ Subgroup.normalizer (V : Set G) := s.H_le_N hyH
  have hcube : (d.th (cv hV y)) ^ 3 = 1 := by
    rw [← d.th_pow hyL, ← cv_pow hV hyN, hy3, cv_one, d.th_one]
  have hsign : d.th (cv hV y) ∈ alternatingGroup (Fin 5) := mem_alt_of_pow_three hcube
  obtain ⟨k, hk⟩ := hx.alpha_surj ⟨d.th (cv hV y), hsign⟩
  have hk' : d.th (cv hV (k : G)) = d.th (cv hV y) := by
    have := congrArg Subtype.val hk
    rwa [alpha_apply] at this
  have hkcv : cv hV (k : G) = cv hV y := d.th_inj (hx.cv_mem_L k.2) hyL hk'
  have hkN : (k : G) ∈ Subgroup.normalizer (V : Set G) := s.H_le_N (hx.Khat_le_H k.2)
  have hkinv : (k : G)⁻¹ ∈ Subgroup.normalizer (V : Set G) := Subgroup.inv_mem _ hkN
  have hq1 : y * (k : G)⁻¹ ∈ Subgroup.centralizer (V : Set G) := by
    rw [← cv_eq_one_iff hV (Subgroup.mul_mem _ hyN hkinv), cv_mul hV hyN hkinv,
      cv_inv hV hkN, hkcv, mul_inv_cancel]
  have hq2 : y * (k : G)⁻¹ ∈ twoResidual H :=
    (twoResidual H).mul_mem hyK ((twoResidual H).inv_mem (hx.Khat_le_twoResidual k.2))
  have hqQ : y * (k : G)⁻¹ ∈ pCoreOf 2 H := hRad ⟨hq2, hq1⟩
  obtain ⟨m, hm⟩ := pCoreOf_isPGroup 2 H ⟨_, hqQ⟩
  refine mem_of_pow_three_of_two_element (K := Khat s d x)
    (hx.A₁_le_normalizer_Khat (Q_le_A₁ (s := s) (d := d) hqQ)) k.2 ?_
    (congrArg Subtype.val hm) hy3
  group

theorem Jt_conj_mem_Khat
    (hRad : twoResidual H ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 H) {t k : G}
    (ht : t ∈ Jt s) (hk : k ∈ Khat s d x) : t * k * t⁻¹ ∈ Khat s d x := by
  have hxK : x ∈ twoResidual H :=
    mem_O2_of_odd (s.Y_le hx.mem) (by rw [hx.ord]; decide)
  have hx3 : x ^ 3 = 1 := by rw [← hx.ord]; exact pow_orderOf_eq_one x
  have htH : t ∈ H := ht.1
  have hxt : t * x * t⁻¹ ∈ Khat s d x := by
    refine hx.mem_Khat_of_pow_three hRad (conj_mem_A₁ ht hx.x_mem_A₁) ?_ ?_
    · exact (Subgroup.mem_normalizer_iff.1 (le_normalizer_twoResidual H htH) x).1 hxK
    · rw [conj_pow, hx3]; simp
  have hle : Khat s d x ≤ (Khat s d x).comap (MulAut.conj t).toMonoidHom := by
    refine conjClosure_le fun a ha z hz => ?_
    have hta : t * a * t⁻¹ ∈ A₁ s d := conj_mem_A₁ ht ha
    have hz' : z ∈ Subgroup.zpowers x := hz
    have htz : t * z * t⁻¹ ∈ Khat s d x := by
      have hzle : Subgroup.zpowers x ≤ (Khat s d x).comap (MulAut.conj t).toMonoidHom := by
        rw [Subgroup.zpowers_le]
        exact hxt
      exact hzle hz'
    have := (Subgroup.mem_normalizer_iff.1 (hx.A₁_le_normalizer_Khat hta) (t * z * t⁻¹)).1 htz
    show t * (a * z * a⁻¹) * t⁻¹ ∈ Khat s d x
    convert this using 1
    group
  exact hle hk

end XData

theorem thompsonJ_le_Jt (s : Setting H T M V Y hV) : thompsonJ T ≤ Jt s := by
  intro t ht
  refine ⟨s.hT.1 ((thompsonJ_le T) ht), ?_⟩
  exact (mem_autI_iff hV ((thompsonJ_le H).trans s.H_le_N)).2
    ⟨t, thompsonJ_le_of_sylow s.hT ht, rfl⟩

end Lift

end CFSG.Quasithin.C126.A5
