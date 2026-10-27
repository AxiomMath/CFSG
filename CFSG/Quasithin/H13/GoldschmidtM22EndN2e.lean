module

public import CFSG.Quasithin.H13.GoldschmidtM22EndN2d
public import CFSG.Quasithin.H13.GoldschmidtM22EndN2a
public import CFSG.Quasithin.H13.GoldschmidtM22EndN2b
public import CFSG.Quasithin.H13.GoldschmidtM22EndN2c
public import CFSG.Quasithin.H13.GoldschmidtM22EndPerm

public section

namespace CFSG.Quasithin.H13.GM22

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.E3 CFSG.Quasithin

variable {G : Type} [Group G] [Finite G] {T M L V : Subgroup G}

namespace PsiData

variable {n : ℕ} (P : PsiData T L V n) (h : Hyp6Sec2 G T M L V)

include P h in
theorem false_of_five_le (hZ : Nat.card (quasithinOmegaOneCenter T) = 2) (h621 : Stmt6_2_1)
    (h626 : Stmt6_2_6) (h629 : Stmt6_2_9) (h6210 : Stmt6_2_10) (h6211 : Stmt6_2_11)
    (h6212 : Stmt6_2_12) (hn : 5 ≤ n) : False := by
  have hsw : ∀ a : ↥(HH T), (a : G) ∈ V → (a : G) ∉ CHU T L V → (P.ψ a).IsSwap :=
    fun a h1 h2 => (P.swap_norm a h1 h2).1
  have hVX := V_inf_X_eq_bot h hZ h6212 (not_V_le_oTwoUpper h hZ h6210 P.ψ hsw)
  obtain ⟨v₀, hv₀V, hv₀C⟩ : ∃ v₀ ∈ V, v₀ ∉ CHU T L V := by
    by_contra hcon
    push Not at hcon
    exact not_V_le_CHU h h6210 fun v hv => hcon v hv
  set a : ↥(HH T) := ⟨v₀, V_le_HH h hZ hv₀V⟩ with ha
  have haV : (a : G) ∈ V := hv₀V
  have haC : (a : G) ∉ CHU T L V := hv₀C
  obtain ⟨hτ, hNa⟩ := P.swap_norm a haV haC
  obtain ⟨α, β, hcα, hcβ, hncomm, hord⟩ := exists_swap_pair n hn (P.ψ a) hτ
  obtain ⟨x, hx⟩ := P.surj α
  obtain ⟨y, hy⟩ := P.surj β
  have hVx := P.conj_le_Mz h hZ h629 h6211 a x haV haC (by rw [hx]; exact hcα.symm)
  have hVy := P.conj_le_Mz h hZ h629 h6211 a y haV haC (by rw [hy]; exact hcβ.symm)
  set g : ↥(HH T) := y * x⁻¹ with hg
  have hψg : P.ψ g = β * α⁻¹ := by rw [hg, map_mul, map_inv, hx, hy]
  have hτα : P.ψ a = α * (α⁻¹ * P.ψ a * α) * α⁻¹ := by group
  have hτβ : P.ψ a = β * (β⁻¹ * P.ψ a * β) * β⁻¹ := by group
  have hψc₁ : P.ψ (g⁻¹ * a * g) = α * (β⁻¹ * P.ψ a * β) * α⁻¹ := by
    rw [map_mul, map_mul, map_inv, hψg]
    group
  have hψc₂ : P.ψ (g * a * g⁻¹) = β * (α⁻¹ * P.ψ a * α) * β⁻¹ := by
    rw [map_mul, map_mul, map_inv, hψg]
    group
  have hnc₁ : ¬ Commute (P.ψ (g⁻¹ * a * g)) (P.ψ a) := by
    intro hc
    have hc' : Commute (α * (β⁻¹ * P.ψ a * β) * α⁻¹) (α * (α⁻¹ * P.ψ a * α) * α⁻¹) := by
      rw [← hτα, ← hψc₁]
      exact hc
    exact hncomm ((commute_conj_iff α _ _).mp hc').symm
  have hnc₂ : ¬ Commute (P.ψ (g * a * g⁻¹)) (P.ψ a) := by
    intro hc
    have hc' : Commute (β * (α⁻¹ * P.ψ a * α) * β⁻¹) (β * (β⁻¹ * P.ψ a * β) * β⁻¹) := by
      rw [← hτβ, ← hψc₂]
      exact hc
    exact hncomm ((commute_conj_iff β _ _).mp hc')
  have hgH : (g : G) ∈ HH T := g.2
  have hU : (V ⊓ Subgroup.normalizer ((conjSubgroup V (g : G) : Subgroup G) : Set G)).relIndex V
      = 2 := by
    refine relIndex_eq_two_of_lt (A := V ⊓ CHU T L V)
      (inf_le_inf_left _ (CHU_le_normalizer_conj_V h hZ h621 hgH)) inf_le_left
      (relIndex_V_CHU h h6211) fun hle => ?_
    have haN := (Subgroup.mem_inf.mp (hle haV)).2
    rw [← CFSG.QuasithinUnique.C5.conjSubgroup_normalizer] at haN
    exact hnc₂ ((hNa (g * a * g⁻¹)).mp (mem_conjSubgroup_iff.mp haN))
  have hc₁V : ((g⁻¹ * a * g : ↥(HH T)) : G) ∈ conjSubgroup V (g : G) := by
    refine mem_conjSubgroup_iff.mpr ?_
    have e : (g : G) * ((g : G)⁻¹ * (a : G) * (g : G)) * (g : G)⁻¹ = (a : G) := by group
    exact e ▸ haV
  have hA : (conjSubgroup V (g : G) ⊓ Subgroup.normalizer (V : Set G)).relIndex
      (conjSubgroup V (g : G)) = 2 := by
    have hrel : (conjSubgroup V (g : G) ⊓ CHU T L V).relIndex (conjSubgroup V (g : G)) = 2 := by
      have := CFSG.QuasithinUnique.C5.relIndex_conjSubgroup (V ⊓ CHU T L V) V (g : G)
      rw [CFSG.QuasithinUnique.C5.conjSubgroup_inf,
        CFSG.Quasithin.conjSubgroup_eq_iff_mem_normalizer.mpr
          (HH_le_normalizer_CHU h hZ hgH)] at this
      rw [this]
      exact relIndex_V_CHU h h6211
    refine relIndex_eq_two_of_lt (A := conjSubgroup V (g : G) ⊓ CHU T L V)
      (inf_le_inf_left _ (CHU_le_normalizer_V h h6210)) inf_le_left hrel fun hle => ?_
    have hN := (Subgroup.mem_inf.mp (hle hc₁V)).2
    exact hnc₁ ((hNa (g⁻¹ * a * g)).mp hN)
  rcases h626 G T M L V h (g : G) hA hU with ⟨-, -, -, -, hpg⟩ | ⟨-, -, -, -, -, -, hpc⟩
  ·
    have hmem : (a : G) * ((g⁻¹ * a * g : ↥(HH T)) : G) ∈ V ⊔ conjSubgroup V (g : G) :=
      Subgroup.mul_mem_sup haV hc₁V
    obtain ⟨k, hk⟩ := hpg ⟨(a : G) * ((g⁻¹ * a * g : ↥(HH T)) : G), hmem⟩
    have hk' : (a * (g⁻¹ * a * g) : ↥(HH T)) ^ 2 ^ k = 1 :=
      Subtype.ext (by simpa using congrArg Subtype.val hk)
    have hψk : (P.ψ a * (α * (β⁻¹ * P.ψ a * β) * α⁻¹)) ^ 2 ^ k = 1 := by
      rw [← hψc₁, ← map_mul, ← map_pow, hk', map_one]
    have hord3 : orderOf (P.ψ a * (α * (β⁻¹ * P.ψ a * β) * α⁻¹)) = 3 := by
      have e : P.ψ a * (α * (β⁻¹ * P.ψ a * β) * α⁻¹) =
          α * ((α⁻¹ * P.ψ a * α) * (β⁻¹ * P.ψ a * β)) * α⁻¹ := by group
      rw [e]
      have := (MulAut.conj α).orderOf_eq ((α⁻¹ * P.ψ a * α) * (β⁻¹ * P.ψ a * β))
      rw [MulAut.conj_apply] at this
      rw [this]
      exact hord
    have h3 : 3 ∣ 2 ^ k := hord3 ▸ orderOf_dvd_of_pow_eq_one hψk
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
    omega
  ·
    have hYH : V ⊔ conjSubgroup V (g : G) ≤ HH T := by
      refine sup_le (V_le_HH h hZ) fun u hu => ?_
      have hxH := V_le_HH h hZ (mem_conjSubgroup_iff.mp hu)
      have h1 := (HH T).mul_mem ((HH T).mul_mem ((HH T).inv_mem hgH) hxH) hgH
      have e : (g : G)⁻¹ * ((g : G) * u * (g : G)⁻¹) * (g : G) = u := by group
      rwa [e] at h1
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hZpc : quasithinOmegaOneCenter T ≤ pCoreOf 2 (V ⊔ conjSubgroup V (g : G)) :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
        ((Z_le_V h hZ).trans le_sup_left) (hYH.trans (HH_le_normalizer_Z T))
        (IsPGroup.of_card (n := 1) (by rw [hZ]; norm_num))
    have hZ2 := hZpc.trans hpc
    set I := conjSubgroup V (x : G) ⊔ conjSubgroup V (y : G) with hI
    have hY : V ⊔ conjSubgroup V (g : G) = conjSubgroup I (x : G)⁻¹ := by
      rw [hI, CFSG.QuasithinUnique.C5.conjSubgroup_sup, CFSG.Quasithin.conjSubgroup_conjSubgroup,
        CFSG.Quasithin.conjSubgroup_conjSubgroup, mul_inv_cancel,
        CFSG.Quasithin.conjSubgroup_one]
      rfl
    have hIM : I ≤ HH T ⊓ M := sup_le hVx hVy
    obtain ⟨z, hzZ, hz1⟩ : ∃ z ∈ quasithinOmegaOneCenter T, z ≠ 1 := by
      by_contra hcon
      push Not at hcon
      have : quasithinOmegaOneCenter T = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr hcon
      rw [this] at hZ
      simp at hZ
    have hz : z ∈ oTwoUpper I := by
      have h1 := hZ2 hzZ
      rw [hY, oTwoUpper_conjSubgroup, mem_conjSubgroup_iff] at h1
      have e : (x : G)⁻¹ * z * ((x : G)⁻¹)⁻¹ = z := by
        calc (x : G)⁻¹ * z * ((x : G)⁻¹)⁻¹ = (x : G)⁻¹ * (z * x) := by group
          _ = (x : G)⁻¹ * (x * z) := by rw [Z_central T x.2 hzZ]
          _ = z := by group
      rwa [e] at h1
    have hzX : z ∈ oTwoUpper (HH T ⊓ M) := oTwoUpper_mono hIM hz
    have hzV : z ∈ V ⊓ oTwoUpper (HH T ⊓ M) := ⟨Z_le_V h hZ hzZ, hzX⟩
    rw [hVX] at hzV
    exact hz1 (Subgroup.mem_bot.mp hzV)

end PsiData

end CFSG.Quasithin.H13.GM22
