module

public import CFSG.Quasithin.Vol2.Ch8Sec2L829CS5Rk2
public import CFSG.Quasithin.Vol2.Ch8Sec2L829Coc
public import CFSG.Quasithin.Vol2.Ch8Sec2L829CS5Cop

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.E3 CFSG.Quasithin.H
open scoped IsMulCommutative commutatorElement


section S7

variable {G : Type} [Group G] [Finite G]

theorem step7_core_cs5 {H T M V L : Subgroup G} {h x : G}
    (hT2 : IsPGroup 2 T) (hVe : IsElemAbelian 2 V)
    (hP7 : H ⊓ M ≤ Subgroup.normalizer (V : Set G)) (hh : h ∈ H) (hhI : h ∈ ch82I V h)
    (hker : kerIn (M ⊓ ch82I V h) (ch82I V h) = pCoreOf 2 (ch82I V h))
    (hMI : M ⊓ ch82I V h = ch82I V h ⊓ Subgroup.normalizer (V : Set G))
    (hHIT : H = ch82I V h ⊔ T)
    (hIU : ch82I V h ≤ Subgroup.centralizer (ch82U V h : Set G))
    (hTU : T ≤ Subgroup.normalizer (ch82U V h : Set G))
    (h828 : ⁅ch82LU L (ch82U V h), Subgroup.centralizer (ch82U V h : Set G)⁆ ≤
      pCoreOf 2 (ch82LU L (ch82U V h)))
    (hPP : ∀ p ∈ pCoreOf 2 (ch82I V h), ∀ q ∈ pCoreOf 2 (ch82I V h), ⁅p, q⁆ ∈ ch82U V h)
    (hOP : ∀ w ∈ pCoreOf 2 (ch82LU L (ch82U V h)), ∀ p ∈ pCoreOf 2 (ch82I V h),
      ⁅w, p⁆ ∈ ch82U V h)
    (hGL : ∀ x : G, x ∈ Subgroup.normalizer (pCoreOf 2 (ch82I V h) : Set G) →
      x ∈ Subgroup.normalizer (ch82U V h : Set G) → (∃ a : ℕ, x ^ 5 ^ a = 1) →
      (∀ w ∈ ch82LU L (ch82U V h), ∀ p ∈ pCoreOf 2 (ch82I V h),
        ⁅⁅x, w⁆, p⁆ ∈ ch82U V h) →
      (∀ w ∈ ch82I V h, ∀ p ∈ pCoreOf 2 (ch82I V h), ⁅⁅x, w⁆, p⁆ ∈ ch82U V h) →
      ∀ p ∈ pCoreOf 2 (ch82I V h), ⁅x, p⁆ ∈ ch82U V h)
    (hxH : x ∈ H) (hxM : x ∈ M) (hx5 : ∃ a : ℕ, x ^ 5 ^ a = 1)
    (hxI : ∀ i ∈ ch82I V h, x * i * x⁻¹ * i⁻¹ ∈ kerIn (H ⊓ M) H) :
    ∀ i ∈ ch82I V h, x * i = i * x := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  set I := ch82I V h with hIdef
  set U := ch82U V h with hUdef
  set P := pCoreOf 2 I with hPdef
  have hIH : I ≤ H := hHIT ▸ le_sup_left
  have hxV : x ∈ Subgroup.normalizer (V : Set G) := hP7 ⟨hxH, hxM⟩
  have hJ : kerIn (H ⊓ M) H ≤ Subgroup.normalizer (V : Set G) := kerIn_le.trans hP7
  have hJH : ∀ g ∈ H, ∀ j ∈ kerIn (H ⊓ M) H, g * j * g⁻¹ ∈ kerIn (H ⊓ M) H := fun g hg j hj =>
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_kerIn (H ⊓ M) H hg) j).mp hj
  have hxVh : x ∈ Subgroup.normalizer ((B6.conjSub h V : Subgroup G) : Set G) := by
    refine mem_normalizer_conjSub_cs5.mpr ?_
    have hj : x * h * x⁻¹ * h⁻¹ ∈ kerIn (H ⊓ M) H := hxI h hhI
    have hj' := hJH h⁻¹ (H.inv_mem hh) _ hj
    have e : h⁻¹ * x * h = (h⁻¹ * (x * h * x⁻¹ * h⁻¹) * h⁻¹⁻¹) * x := by group
    rw [e]
    exact Subgroup.mul_mem _ (hJ hj') hxV
  have hxI' : x ∈ Subgroup.normalizer (I : Set G) :=
    Subgroup.zpowers_le.mp (le_normalizer_sup_829 (T := Subgroup.zpowers x) (A := V)
      (B := B6.conjSub h V) (Subgroup.zpowers_le.mpr hxV) (Subgroup.zpowers_le.mpr hxVh))
  have hxP : ∀ i ∈ I, x * i * x⁻¹ * i⁻¹ ∈ P := by
    intro i hi
    have hI1 : x * i * x⁻¹ * i⁻¹ ∈ I := by
      have := (Subgroup.mem_normalizer_iff.mp hxI' i).mp hi
      exact I.mul_mem this (I.inv_mem hi)
    have hJ1 := hxI i hi
    rw [← hker]
    intro b hb
    exact ⟨(kerIn_le (hJH b (hIH hb) _ hJ1)).2, I.mul_mem (I.mul_mem hb hI1) (I.inv_mem hb)⟩
  have hxo : Odd (orderOf x) := by
    obtain ⟨a, ha⟩ := hx5
    exact Odd.of_dvd_nat (Odd.pow (by decide)) (orderOf_dvd_of_pow_eq_one ha)
  have hxO : x ∈ oTwoUpper H := Subgroup.subset_closure ⟨hxH, hxo⟩
  have hY : oTwoUpper H ≤ Subgroup.centralizer (U : Set G) :=
    oTwoUpper_le_centralizer_U_829 hT2 hHIT hIU hTU
  have hxU : ∀ u ∈ U, x * u = u * x := fun u hu =>
    (Subgroup.mem_centralizer_iff.mp (hY hxO) u hu).symm
  have hxNU : x ∈ Subgroup.normalizer (U : Set G) := Subgroup.centralizer_le_normalizer _ (hY hxO)
  have hxNP : x ∈ Subgroup.normalizer (P : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 I hxI'
  have hcomm := commutator_oTwoUpper_LU_829 hY h828
  have hxLU : ∀ w ∈ ch82LU L U, ⁅x, w⁆ ∈ pCoreOf 2 (ch82LU L U) := fun w hw =>
    hcomm (Subgroup.commutator_mem_commutator hxO hw)
  have hPU : ∀ p ∈ P, ⁅x, p⁆ ∈ U := hGL x hxNP hxNU hx5
    (fun w hw p hp => hOP _ (hxLU w hw) p hp)
    (fun w hw p hp => hPP _ (by simpa [commutatorElement_def] using hxP w hw) p hp)
  have hU2 : IsPGroup 2 U :=
    isPGroup_of_sq_eq_one_cs5 fun u hu => hVe.2 u hu.1
  have hPc : ∀ p ∈ P, x * p = p * x :=
    centralizes_of_quot_cs5 hU2 hxo hxU (fun p hp => by simpa [commutatorElement_def] using hPU p hp)
  have hVI : V ≤ I := le_sup_left
  have hVc : ∀ v ∈ V, x * v = v * x := by
    refine centralizes_of_quot_cs5 (P := V) (U := V ⊓ P) ?_ hxo
      (fun u hu => hPc u hu.2) ?_
    · exact isPGroup_of_sq_eq_one_cs5 fun u hu => hVe.2 u hu.1
    · intro v hv
      refine ⟨?_, hxP v (hVI hv)⟩
      exact V.mul_mem ((Subgroup.mem_normalizer_iff.mp hxV v).mp hv) (V.inv_mem hv)
  have hPV : ∀ p ∈ P, p ∈ Subgroup.normalizer (V : Set G) := by
    intro p hp
    have h1 : p ∈ M ⊓ I := kerIn_le (hker ▸ hp)
    rw [hMI] at h1
    exact h1.2
  have hP2 : IsPGroup 2 P := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 I
  have hPI : P ≤ I := CFSG.LieType.BorelTits.pCoreOf_le 2 I
  obtain ⟨q, hqP, hfix⟩ := exists_fixed_mem_coset_cs5 (p := 5) (by norm_num) hx5 hP2 hxNP
    (hxP h hhI)
  have hcI : q * h ∈ I := I.mul_mem (hPI hqP) hhI
  have hxc : x * (q * h) = (q * h) * x := by
    have := congrArg (· * x) hfix
    simpa [mul_assoc] using this
  have hVhc : ∀ y ∈ B6.conjSub h V, x * y = y * x := by
    intro y hy
    rw [B6.mem_conjSub] at hy
    set v := h⁻¹ * y * h with hv
    set c := q * h with hc
    set q' := c⁻¹ * q * c with hq'
    have hq'P : q' ∈ P := by
      have := (Subgroup.mem_normalizer_iff.mp
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 I (I.inv_mem hcI)) q).mp hqP
      simpa [hq'] using this
    have hq'V : q'⁻¹ * v * q' ∈ V := by
      have := (Subgroup.mem_normalizer_iff.mp (hPV _ (P.inv_mem hq'P)) v).mp hy
      simpa using this
    have hy_eq : y = c * (q'⁻¹ * v * q') * c⁻¹ := by
      simp only [hc, hq', hv]
      group
    rw [hy_eq]
    have hxc' : Commute x c := hxc
    have hxv : Commute x (q'⁻¹ * v * q') := hVc _ hq'V
    exact (((hxc'.mul_right hxv).mul_right hxc'.inv_right) : Commute _ _).eq
  have hIle : I ≤ Subgroup.centralizer ({x} : Set G) := by
    refine sup_le ?_ ?_
    · intro v hv
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      rw [Set.mem_singleton_iff.mp hz]
      exact hVc v hv
    · intro y hy
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      rw [Set.mem_singleton_iff.mp hz]
      exact hVhc y hy
  intro i hi
  have := Subgroup.mem_centralizer_iff.mp (hIle hi) x (Set.mem_singleton x)
  exact this

end S7

end CFSG.Quasithin.H13
