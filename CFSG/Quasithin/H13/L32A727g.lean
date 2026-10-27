module

public import CFSG.Quasithin.H13.A5S136c
public import CFSG.Quasithin.H13.L32A727b
public import CFSG.Quasithin.H13.L32ASk7

public section

namespace CFSG.Quasithin.H13.L32A.R727

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G] {T L V H : Subgroup G}

theorem isSolvable_star (S : Setting147 G T L V H) (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4)
    {K : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)} (hKn : K.Normal) (hK : IsPGroup 3 ↥K)
    (hHe : H = pre H K ⊔ (l1 T L V ⊔ T)) : Group.IsSolvable (↥H ⧸ CFSG.pCore 2 ↥H) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hl1H : l1 T L V ≤ H := le_sup_left.trans S.hz.1.1
  have hTH : T ≤ H := le_sup_right.trans S.hz.1.1
  have hMod := stmtL32NModule_of_inputs h1332 h1334 G T L V S.hyp.hyp S.hyp.fsu
  have h34 := h1334 G T L V S.hyp.hyp.h13 (S.hyp.hyp1223 (stmt13_3_2_two_of h1332)).irrPlus
  have hl1L : l1 T L V ≤ L := (oTwoUpper_le _).trans inf_le_left
  have hlt : l1 T L V ⊔ T < L ⊔ T := by
    refine lt_of_le_of_ne (sup_le_sup_right hl1L T) fun h => ?_
    have hLN : L ≤ Subgroup.normalizer (fsuV1 T V : Set G) :=
      le_sup_left.trans (h ▸ sup_le ((oTwoUpper_le _).trans inf_le_right)
        (hTH.trans S.hz.2.1))
    have hVV : V ≤ fsuV1 T V :=
      h34.2.1.symm.le.trans (conjClosure_le fun g hg z hz =>
        (Subgroup.mem_normalizer_iff.mp (hLN hg) z).mp hz)
    have h1 := Subgroup.card_le_of_le hVV
    rw [hMod.2.1, hMod.2.2.2.1] at h1
    norm_num at h1
  have : Group.IsSolvable ↥(l1 T L V ⊔ T) :=
    A5.isSolvable_of_isTwoThreeGroup (h34.2.2 _ le_sup_right hlt)
  have : Group.IsSolvable ↥K := by
    have := hK.isNilpotent
    infer_instance
  have hLT : l1 T L V ⊔ T ≤ H := sup_le hl1H hTH
  let φ : ↥(l1 T L V ⊔ T) →* (↥H ⧸ CFSG.pCore 2 ↥H) ⧸ K :=
    (QuotientGroup.mk' K).comp
      ((QuotientGroup.mk' (CFSG.pCore 2 ↥H)).comp (Subgroup.inclusion hLT))
  have htop : (⊤ : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) = K ⊔ modO2Image H (l1 T L V ⊔ T) := by
    have e := congrArg (modO2Image H) hHe
    rwa [modO2Image_self, modO2Image_sup (pre_le K) hLT, modO2Image_pre] at e
  have hsurj : Function.Surjective φ := by
    intro z
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective K z
    have hy : y ∈ ((K ⊔ modO2Image H (l1 T L V ⊔ T) : Subgroup _) : Set _) := by
      rw [← htop]
      exact Subgroup.mem_top y
    rw [Subgroup.normal_mul] at hy
    obtain ⟨k, hk, w, hw, rfl⟩ := hy
    obtain ⟨u, hu, rfl⟩ := mem_modO2Image'.mp hw
    refine ⟨⟨u, hu⟩, ?_⟩
    show QuotientGroup.mk' K (QuotientGroup.mk' (CFSG.pCore 2 ↥H) u) = _
    have hk1 : QuotientGroup.mk' K k = 1 := (QuotientGroup.eq_one_iff k).mpr hk
    rw [map_mul, hk1, one_mul]
  have : Group.IsSolvable ((↥H ⧸ CFSG.pCore 2 ↥H) ⧸ K) := Group.isSolvable_of_surjective hsurj
  exact Group.isSolvable_of_ker_le_range K.subtype (QuotientGroup.mk' K)
    (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])

theorem not_fix_frattini (S : Setting147 G T L V H) (h76 : Lemma14_7_6)
    (hs : Group.IsSolvable (↥H ⧸ CFSG.pCore 2 ↥H))
    {X : Subgroup ↥(CFSG.pCore 3 (↥H ⧸ CFSG.pCore 2 ↥H))}
    (hXf : ∀ α : MulAut ↥(CFSG.pCore 3 (↥H ⧸ CFSG.pCore 2 ↥H)), (orderOf α).Coprime 3 →
      (∀ x ∈ X, x⁻¹ * α x ∈ frattiniIn X) → α = 1)
    {j : ↥H ⧸ CFSG.pCore 2 ↥H} {k : ℕ} (hj : j ^ 2 ^ k = 1) (hj1 : j ≠ 1) :
    ∃ x ∈ X, x⁻¹ * MulAut.conjNormal j x ∉ frattiniIn X := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : (CFSG.pCore 3 (↥H ⧸ CFSG.pCore 2 ↥H)).Normal := CFSG.pCore_normal
  by_contra hcon
  have hfix : ∀ x ∈ X, x⁻¹ * MulAut.conjNormal j x ∈ frattiniIn X := fun x hx => by
    by_contra h
    exact hcon ⟨x, hx, h⟩
  have hord : (orderOf
      (MulAut.conjNormal j : MulAut ↥(CFSG.pCore 3 (↥H ⧸ CFSG.pCore 2 ↥H)))).Coprime 3 := by
    have h1 : (MulAut.conjNormal j : MulAut ↥(CFSG.pCore 3 (↥H ⧸ CFSG.pCore 2 ↥H))) ^ 2 ^ k =
        1 := by
      rw [← map_pow, hj, map_one]
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one h1)
    rw [hi]
    exact Nat.Coprime.pow_left i (by norm_num)
  have hα := hXf _ hord hfix
  have hF3 := h76 G T L V H S
  have hFP : CFSG.fittingSubgroup (↥H ⧸ CFSG.pCore 2 ↥H) ≤ CFSG.pCore 3 (↥H ⧸ CFSG.pCore 2 ↥H) :=
    le_sSup ⟨inferInstance, hF3⟩
  have hjC : j ∈ Subgroup.centralizer
      (CFSG.fittingSubgroup (↥H ⧸ CFSG.pCore 2 ↥H) : Set (↥H ⧸ CFSG.pCore 2 ↥H)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    have h1 := congrArg (fun φ : MulAut ↥(CFSG.pCore 3 (↥H ⧸ CFSG.pCore 2 ↥H)) =>
      ((φ ⟨f, hFP hf⟩ : ↥(CFSG.pCore 3 (↥H ⧸ CFSG.pCore 2 ↥H))) : ↥H ⧸ CFSG.pCore 2 ↥H)) hα
    simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h1
    calc f * j = j * f * j⁻¹ * j := by rw [h1]
      _ = j * f := by group
  have hjP : j ∈ CFSG.pCore 3 (↥H ⧸ CFSG.pCore 2 ↥H) :=
    hFP (CFSG.centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hs hjC)
  obtain ⟨m, hm⟩ := CFSG.pCore_isPGroup (p := 3) (G := ↥H ⧸ CFSG.pCore 2 ↥H) ⟨j, hjP⟩
  have hm' : j ^ 3 ^ m = 1 := by simpa using congrArg Subtype.val hm
  have h1 : orderOf j ∣ Nat.gcd (2 ^ k) (3 ^ m) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hj) (orderOf_dvd_of_pow_eq_one hm')
  rw [(Nat.Coprime.pow k m (by norm_num : Nat.Coprime 2 3)).gcd_eq_one, Nat.dvd_one,
    orderOf_eq_one_iff] at h1
  exact hj1 h1

end CFSG.Quasithin.H13.L32A.R727
