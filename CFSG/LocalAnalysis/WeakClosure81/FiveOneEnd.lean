module

public import CFSG.LocalAnalysis.WeakClosure81.FiveSylow
public import CFSG.Quasithin.Background.A4Defs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin Subgroup

theorem exists_odd_coatom_of_unique_max {K : Type} [Group K] [Finite K] {M : Subgroup K}
    (hM : IsCoatom M) (hodd : Odd M.index) (hev : Even (Nat.card M)) (hnn : ¬ M.Normal)
    (hu : ∀ X L : Subgroup K, X ≤ M → X ≠ ⊥ → IsPGroup 2 X → IsCoatom L → X ≤ L → L = M) :
    ∃ N : Subgroup K, IsCoatom N ∧ Odd (Nat.card N) := by
  have hL1 : ∀ R : Subgroup K, R ≤ M → IsPGroup 2 R → R.Normal → R = ⊥ := by
    intro R hRM hR2 hRnorm
    by_contra hRne
    have hnorm : ∀ g : K, g ∈ Subgroup.normalizer (M : Set K) := by
      intro g
      have hMg : IsCoatom (M.comap (MulAut.conj g).toMonoidHom) :=
        Subgroup.isCoatom_comap_of_surjective (MulAut.conj g).surjective hM
      have hle : R ≤ M.comap (MulAut.conj g).toMonoidHom := by
        intro r hr
        rw [Subgroup.mem_comap]
        change g * r * g⁻¹ ∈ M
        exact hRM (hRnorm.conj_mem r hr g)
      have hEq : M.comap (MulAut.conj g).toMonoidHom = M := hu R _ hRM hRne hR2 hMg hle
      rw [Subgroup.mem_normalizer_iff]
      intro m
      have hm : m ∈ M.comap (MulAut.conj g).toMonoidHom ↔ m ∈ M := by rw [hEq]
      rw [Subgroup.mem_comap] at hm
      change g * m * g⁻¹ ∈ M ↔ m ∈ M at hm
      exact hm.symm
    have htop : Subgroup.normalizer (M : Set K) = ⊤ := by
      rw [eq_top_iff]
      intro g _
      exact hnorm g
    exact hnn (Subgroup.normalizer_eq_top_iff.mp htop)
  have hL2 : ∀ R : Subgroup K, R ≤ M → IsPGroup 2 R → R ≠ ⊥ →
      Subgroup.normalizer (R : Set K) ≤ M := by
    intro R hRM hR2 hRne
    by_contra hle
    have hne_top : Subgroup.normalizer (R : Set K) ≠ ⊤ := by
      intro htop
      exact hRne (hL1 R hRM hR2 (Subgroup.normalizer_eq_top_iff.mp htop))
    obtain ⟨L, hLcoat, hNL⟩ :=
      (eq_top_or_exists_le_coatom (Subgroup.normalizer (R : Set K))).resolve_left hne_top
    have hRL : R ≤ L := Subgroup.le_normalizer.trans hNL
    have hLM : L = M := hu R L hRM hRne hR2 hLcoat hRL
    exact hle (hLM ▸ hNL)
  have hL3 : ∀ x ∈ M, orderOf x = 2 → ∃ g : K, g * x * g⁻¹ ∉ M := by
    intro x hxM hxord
    by_contra hcon
    have hall : ∀ g : K, g * x * g⁻¹ ∈ M := fun g => not_not.mp (not_exists.mp hcon g)
    set L : Subgroup K := Subgroup.normalClosure ({x} : Set K) with hLdef
    have hLnorm : L.Normal := Subgroup.normalClosure_normal
    have hLM : L ≤ M := by
      rw [hLdef]
      change Subgroup.closure (Group.conjugatesOfSet ({x} : Set K)) ≤ M
      refine (Subgroup.closure_le M).mpr ?_
      intro y hy
      rw [Group.mem_conjugatesOfSet_iff] at hy
      obtain ⟨a, ha, hconj⟩ := hy
      rw [Set.mem_singleton_iff] at ha
      subst ha
      rw [isConj_iff] at hconj
      obtain ⟨c, hc⟩ := hconj
      rw [← hc]
      exact hall c
    have hxL : x ∈ L := by
      rw [hLdef]
      exact Subgroup.subset_normalClosure (Set.mem_singleton x)
    have hzpL : Subgroup.zpowers x ≤ L := Subgroup.zpowers_le.mpr hxL
    have hzp2 : IsPGroup 2 (Subgroup.zpowers x) :=
      IsPGroup.of_card (n := 1) (by simp [Nat.card_zpowers, hxord])
    obtain ⟨R, hRsyl, hzpR⟩ := exists_isSylowIn_ge 2 hzpL hzp2
    have hxR : x ∈ R := hzpR (Subgroup.mem_zpowers x)
    have hRne : R ≠ ⊥ := by
      intro hbot
      have hx1 : x = 1 := by
        have : x ∈ (⊥ : Subgroup K) := hbot ▸ hxR
        rwa [Subgroup.mem_bot] at this
      have h1 : orderOf x = 1 := by rw [hx1]; exact orderOf_one
      omega
    have hRM : R ≤ M := hRsyl.le.trans hLM
    have hR2 : IsPGroup 2 R := hRsyl.isPGroup
    have hfrat := frattini_isSylowIn (H := ⊤) (Y := L) (S := R) le_top
      (hLnorm.subgroupOf ⊤) hRsyl
    have hMtop : M = ⊤ := by
      rw [eq_top_iff]
      intro k _
      obtain ⟨y, hyL, n, _, hnN, hyn⟩ := hfrat k (Subgroup.mem_top k)
      have hyM : y ∈ M := hLM hyL
      have hnM : n ∈ M := hL2 R hRM hR2 hRne hnN
      rw [← hyn]
      exact M.mul_mem hyM hnM
    exact hM.1 hMtop
  obtain ⟨x₀, hx₀ord⟩ :=
    exists_prime_orderOf_dvd_card' (G := ↥M) 2 (even_iff_two_dvd.mp hev)
  set x : K := (x₀ : K) with hxdef
  have hxM : x ∈ M := by rw [hxdef]; exact x₀.2
  have hxord : orderOf x = 2 := by rw [hxdef, Subgroup.orderOf_coe, hx₀ord]
  obtain ⟨g, hgx⟩ := hL3 x hxM hxord
  set y : K := g * x * g⁻¹ with hydef
  have hyM : y ∉ M := by rw [hydef]; exact hgx
  have hx2 : x * x = 1 := by
    have := pow_orderOf_eq_one x
    rwa [hxord, pow_two] at this
  have hyord : orderOf y = 2 := by
    rw [hydef, ← MulAut.conj_apply g x, MulEquiv.orderOf_eq, hxord]
  have hy2 : y * y = 1 := by
    have := pow_orderOf_eq_one y
    rwa [hyord, pow_two] at this
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy2
  have hgen : Subgroup.closure ({x, y} : Set K) = ⊤ := by
    by_contra hne
    obtain ⟨L, hLcoat, hclL⟩ :=
      (eq_top_or_exists_le_coatom (Subgroup.closure ({x, y} : Set K))).resolve_left hne
    have hxcl : x ∈ Subgroup.closure ({x, y} : Set K) := Subgroup.subset_closure (by simp)
    have hzpL : Subgroup.zpowers x ≤ L := Subgroup.zpowers_le.mpr (hclL hxcl)
    have hzpM : Subgroup.zpowers x ≤ M := Subgroup.zpowers_le.mpr hxM
    have hxne1 : x ≠ 1 := by
      intro h1
      have : orderOf x = 1 := by rw [h1]; exact orderOf_one
      omega
    have hzpne : Subgroup.zpowers x ≠ ⊥ := Subgroup.zpowers_ne_bot.mpr hxne1
    have hzp2 : IsPGroup 2 (Subgroup.zpowers x) :=
      IsPGroup.of_card (n := 1) (by simp [Nat.card_zpowers, hxord])
    have hLM : L = M := hu (Subgroup.zpowers x) L hzpM hzpne hzp2 hLcoat hzpL
    have hyL : y ∈ L := hclL (Subgroup.subset_closure (by simp))
    rw [hLM] at hyL
    exact hyM hyL
  set c : K := x * y with hcdef
  set C : Subgroup K := Subgroup.zpowers c with hCdef
  have hxc : x * c * x⁻¹ = c⁻¹ := by
    have hcx : c⁻¹ = y * x := by rw [hcdef, mul_inv_rev, hxinv, hyinv]
    rw [hcx, hcdef, ← mul_assoc x x y, hx2, one_mul, hxinv]
  have hyc : y * c * y⁻¹ = c⁻¹ := by
    have hcx : c⁻¹ = y * x := by rw [hcdef, mul_inv_rev, hxinv, hyinv]
    rw [hcx, hcdef]
    group
  have hxN : x ∈ Subgroup.normalizer (C : Set K) := by
    refine A4.mem_normalizer_of_conj_mem fun k hk => ?_
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hk
    have hpow : x * c ^ n * x⁻¹ = (c⁻¹) ^ n := by
      have h1 : x * c ^ n * x⁻¹ = (x * c * x⁻¹) ^ n := by
        rw [← MulAut.conj_apply x c, ← map_zpow, MulAut.conj_apply]
      rw [h1, hxc]
    rw [hpow, inv_zpow]
    exact C.inv_mem (Subgroup.zpow_mem_zpowers c n)
  have hyN : y ∈ Subgroup.normalizer (C : Set K) := by
    refine A4.mem_normalizer_of_conj_mem fun k hk => ?_
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hk
    have hpow : y * c ^ n * y⁻¹ = (c⁻¹) ^ n := by
      have h1 : y * c ^ n * y⁻¹ = (y * c * y⁻¹) ^ n := by
        rw [← MulAut.conj_apply y c, ← map_zpow, MulAut.conj_apply]
      rw [h1, hyc]
    rw [hpow, inv_zpow]
    exact C.inv_mem (Subgroup.zpow_mem_zpowers c n)
  have hCnormal : C.Normal := by
    have htop : Subgroup.normalizer (C : Set K) = ⊤ := by
      rw [eq_top_iff, ← hgen]
      refine (Subgroup.closure_le _).mpr ?_
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · exact hxN
      · exact hyN
    exact Subgroup.normalizer_eq_top_iff.mp htop
  have hy_eq : y = x * c := by
    rw [hcdef, ← mul_assoc x x y, hx2, one_mul]
  have hsup : Subgroup.zpowers x ⊔ C = ⊤ := by
    rw [eq_top_iff, ← hgen]
    refine (Subgroup.closure_le _).mpr ?_
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact Subgroup.mem_sup_left (Subgroup.mem_zpowers x)
    · rw [hy_eq]
      exact Subgroup.mul_mem_sup (Subgroup.mem_zpowers x) (Subgroup.mem_zpowers c)
  have hclub : ∀ k : K, k ∈ C ∨ x * k ∈ C := by
    haveI : C.Normal := hCnormal
    intro k
    have hk : k ∈ Subgroup.zpowers x ⊔ C := by rw [hsup]; exact Subgroup.mem_top k
    rw [Subgroup.mem_sup_of_normal_right] at hk
    obtain ⟨u, hu, v, hv, huv⟩ := hk
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hu
    have hu2 : u = 1 ∨ u = x := by
      rw [← hn, ← zpow_mod_orderOf x n, hxord]
      rw [show ((2 : ℕ) : ℤ) = (2 : ℤ) from rfl]
      rcases Int.emod_two_eq_zero_or_one n with h | h
      · left; rw [h]; simp
      · right; rw [h]; simp
    rcases hu2 with rfl | rfl
    · left; rw [← huv]; simpa using hv
    · right
      rw [← huv, ← mul_assoc x x v, hx2, one_mul]
      exact hv
  have hCodd : Odd (Nat.card C) := by
    by_contra hnotodd
    have hEven : Even (Nat.card C) := Nat.not_odd_iff_even.mp hnotodd
    have hEven' : Even (orderOf c) := by rwa [hCdef, Nat.card_zpowers] at hEven
    have h2dvd : 2 ∣ orderOf c := even_iff_two_dvd.mp hEven'
    have hc0 : orderOf c ≠ 0 := (orderOf_pos c).ne'
    set z : K := c ^ (orderOf c / 2) with hzdef
    have hzord : orderOf z = 2 := by
      rw [hzdef]
      exact orderOf_pow_orderOf_div hc0 h2dvd
    have hz2 : z * z = 1 := by
      have := pow_orderOf_eq_one z
      rwa [hzord, pow_two] at this
    have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
    have hxz : x * z * x⁻¹ = z := by
      have h1 : x * c ^ (orderOf c / 2) * x⁻¹ = (c⁻¹) ^ (orderOf c / 2) := by
        have h2 : x * c ^ (orderOf c / 2) * x⁻¹ = (x * c * x⁻¹) ^ (orderOf c / 2) := by
          rw [← MulAut.conj_apply x c, ← map_pow, MulAut.conj_apply]
        rw [h2, hxc]
      rw [hzdef]
      rw [h1, inv_pow, ← hzdef, hzinv]
    have hzx_comm : z * x = x * z := by
      have h : x * z = z * x := by
        calc x * z = (x * z * x⁻¹) * x := by group
          _ = z * x := by rw [hxz]
      exact h.symm
    have hzc_comm : z * c = c * z := by
      have hzmem : z ∈ Subgroup.zpowers c := by
        rw [hzdef]
        exact Subgroup.npow_mem_zpowers c (orderOf c / 2)
      exact setLike_mul_comm hzmem (Subgroup.mem_zpowers c)
    have hzy : z * y = y * z := by
      rw [hy_eq]
      calc z * (x * c) = (z * x) * c := by group
        _ = (x * z) * c := by rw [hzx_comm]
        _ = x * (z * c) := by group
        _ = x * (c * z) := by rw [hzc_comm]
        _ = (x * c) * z := by group
    have hcent : Subgroup.closure ({x, y} : Set K) ≤ Subgroup.centralizer ({z} : Set K) := by
      refine (Subgroup.closure_le _).mpr ?_
      intro w hw
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
      refine (Subgroup.mem_centralizer_iff).mpr ?_
      rintro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      rcases hw with rfl | rfl
      · exact hzx_comm
      · exact hzy
    have hz_center : z ∈ Subgroup.center K := by
      rw [Subgroup.mem_center_iff]
      intro g
      have hgcl : g ∈ Subgroup.closure ({x, y} : Set K) := by
        rw [hgen]; exact Subgroup.mem_top g
      have hg := hcent hgcl
      exact ((Subgroup.mem_centralizer_iff.mp hg) z (Set.mem_singleton z)).symm
    have hzR2 : IsPGroup 2 (Subgroup.zpowers z) :=
      IsPGroup.of_card (n := 1) (by simp [Nat.card_zpowers, hzord])
    have hzRne : Subgroup.zpowers z ≠ ⊥ := by
      rw [Subgroup.zpowers_ne_bot]
      intro hz1
      have : orderOf z = 1 := by rw [hz1]; exact orderOf_one
      omega
    have hRnormal : (Subgroup.zpowers z).Normal :=
      Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr hz_center)
    have hRM : Subgroup.zpowers z ≤ M := by
      obtain ⟨S, hS, hSM⟩ := A4.exists_isSylowTwoOf_le_of_odd (K := M) (H := ⊤) le_top
        (by rw [Subgroup.relIndex_top_right M]; exact hodd)
      exact (A4.le_of_normal_of_isSylowTwoOf hS le_top (hRnormal.subgroupOf ⊤) hzR2).trans hSM
    exact hzRne (hL1 (Subgroup.zpowers z) hRM hzR2 hRnormal)
  refine ⟨C, ?_, hCodd⟩
  refine ⟨?_, ?_⟩
  · intro hCtop
    have hxmem : x ∈ C := by rw [hCtop]; exact Subgroup.mem_top x
    have hdvd : orderOf x ∣ Nat.card C := Subgroup.orderOf_dvd_natCard C hxmem
    rw [hxord] at hdvd
    exact (Nat.not_even_iff_odd.mpr hCodd) (even_iff_two_dvd.mpr hdvd)
  · intro V hCV
    have hCVle : C ≤ V := le_of_lt hCV
    obtain ⟨v, hvV, hvC⟩ := IsConcreteLE.exists_of_lt hCV
    have hxvC : x * v ∈ C := (hclub v).resolve_left hvC
    have hxV : x ∈ V := by
      have h1 : (x * v) * v⁻¹ ∈ V := V.mul_mem (hCVle hxvC) (V.inv_mem hvV)
      simpa using h1
    rw [eq_top_iff]
    intro k _
    rcases hclub k with hkC | hxkC
    · exact hCVle hkC
    · have hxkV : x * k ∈ V := hCVle hxkC
      have h2 : x⁻¹ * (x * k) ∈ V := V.mul_mem (V.inv_mem hxV) hxkV
      simpa using h2

end CFSG.LocalAnalysis.WeakClosure81
