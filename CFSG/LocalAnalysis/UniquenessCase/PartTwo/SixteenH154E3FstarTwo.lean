module

public import CFSG.LargeExtraspecial.S5Comp
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970_19
public import CFSG.Adapters.GeneralizedFitting
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.Quasithin.Background.A1aFStar

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

open scoped Pointwise commutatorElement

private theorem s16h_e3_gw_of_open {Γ : Type*} [Group Γ] {A X : Subgroup Γ}
    (h : IsComponentOf A X) : CFSG.GorensteinWalter.IsComponentOf A X := by
  obtain ⟨hAX, hsub, hqs⟩ := h
  obtain ⟨hcomm, hsimple⟩ := hqs
  refine ⟨hAX, ?_, ?_⟩
  · exact (CFSG.Adapters.isSubnormal_top_iff (A.subgroupOf X)).mp
      ((CFSG.Quasithin.isSubnormal_subgroupOf_top_iff hAX).mpr hsub)
  · refine ⟨?_, hcomm, hsimple⟩
    haveI : Nontrivial (↥A ⧸ Subgroup.center ↥A) := hsimple.toNontrivial
    exact (QuotientGroup.mk'_surjective (Subgroup.center ↥A)).nontrivial

private theorem s16h_e3_open_of_gw {Γ : Type*} [Group Γ] {A X : Subgroup Γ}
    (h : CFSG.GorensteinWalter.IsComponentOf A X) : IsComponentOf A X := by
  obtain ⟨hAX, hsub, hqs⟩ := h
  obtain ⟨_hnt, hcomm, hsimple⟩ := hqs
  exact ⟨hAX, (CFSG.Quasithin.isSubnormal_subgroupOf_top_iff hAX).mp
    ((CFSG.Adapters.isSubnormal_top_iff (A.subgroupOf X)).mpr hsub), hcomm, hsimple⟩

public theorem s16h_e3_solvable_centralizer {Γ : Type} [Group Γ] [Finite Γ]
    {X A B Z : Subgroup Γ} (hA : IsComponentOf A X) (t : Γ) (htX : t ∈ X)
    (hBt : B = A.map (MulAut.conj t).toMonoidHom)
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hAc : ∀ a ∈ A, (∀ b ∈ A, a * b = b * a) → a = 1) (hZX : Z ≤ X)
    (hZ : Nat.card ↥Z = 3)
    (hZn : ∀ x ∈ X, Z.map (MulAut.conj x).toMonoidHom = Z)
    (hZc : ∀ z ∈ Z, ∀ a ∈ A ⊔ B, z * a = a * z)
    (hK : ∀ k ∈ X, (∀ a ∈ A ⊔ B, k * a = a * k) →
      k ∈ Z ∨ (k ^ 2 = 1 ∧ ∀ z ∈ Z, k * z * k⁻¹ = z⁻¹)) :
    Group.IsSolvable ↥(X ⊓ Subgroup.centralizer ((A ⊔ B : Subgroup Γ) : Set Γ)) := by
  let K : Subgroup Γ := X ⊓ Subgroup.centralizer ((A ⊔ B : Subgroup Γ) : Set Γ)
  change Group.IsSolvable ↥K
  have hZK : Z ≤ K := by
    refine le_inf hZX ?_
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact (hZc z hz a ha).symm
  have hKK : ∀ k ∈ K, k ∈ Z ∨ (k ^ 2 = 1 ∧ ∀ z ∈ Z, k * z * k⁻¹ = z⁻¹) := by
    intro k hk
    exact hK k hk.1 (fun a ha => (Subgroup.mem_centralizer_iff.mp hk.2 a ha).symm)
  have hsq : ∀ k : ↥K, (k : Γ) ^ 2 ∈ Z := by
    intro k
    rcases hKK k k.2 with h | ⟨h2, _⟩
    · rw [pow_two]; exact Z.mul_mem h h
    · rw [h2]; exact Z.one_mem
  have hZnormK : (Z.subgroupOf K).Normal := by
    refine ⟨fun z hz g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hz ⊢
    have hg := hZn (g : Γ) g.2.1
    have hmem : MulAut.conj (g : Γ) (z : Γ) ∈ Z := by
      have hmem' : MulAut.conj (g : Γ) (z : Γ) ∈
          Z.map (MulAut.conj (g : Γ)).toMonoidHom :=
        Subgroup.mem_map.mpr ⟨(z : Γ), hz, rfl⟩
      rwa [hg] at hmem'
    simpa [MulAut.conj_apply] using hmem
  haveI : (Z.subgroupOf K).Normal := hZnormK
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : IsCyclic ↥Z := isCyclic_of_prime_card (p := 3) hZ
  haveI : IsMulCommutative ↥Z := IsCyclic.isMulCommutative
  haveI : Group.IsSolvable ↥Z := inferInstance
  haveI : Group.IsSolvable ↥(Z.subgroupOf K) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hZK).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hZK).injective
  have hsqN : ∀ k : ↥K, k ^ 2 ∈ Z.subgroupOf K := by
    intro k
    rw [Subgroup.mem_subgroupOf]
    simpa using hsq k
  have hsqQ : ∀ q : ↥K ⧸ Z.subgroupOf K, q ^ 2 = 1 := by
    intro q
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf K) q
    rw [← map_pow, QuotientGroup.mk'_apply]
    exact (QuotientGroup.eq_one_iff (N := Z.subgroupOf K) (k ^ 2)).mpr (hsqN k)
  have hcommQ : ∀ q r : ↥K ⧸ Z.subgroupOf K, q * r = r * q := by
    intro q r
    have hqr : q * (r * q * r) = 1 := by
      have h := hsqQ (q * r)
      rw [pow_two] at h
      simpa [mul_assoc] using h
    have hq : q * q = 1 := by
      have h := hsqQ q
      rwa [pow_two] at h
    have hr : r * r = 1 := by
      have h := hsqQ r
      rwa [pow_two] at h
    have h1 : r * q * r = q := by
      apply mul_left_cancel (a := q)
      calc q * (r * q * r) = 1 := hqr
        _ = q * q := by rw [← hq]
    have h2 : r * q = q * r := by
      calc r * q = r * q * 1 := (mul_one _).symm
        _ = r * q * (r * r) := by rw [hr]
        _ = (r * q * r) * r := by group
        _ = q * r := by rw [h1]
    exact h2.symm
  haveI : Group.IsSolvable (↥K ⧸ Z.subgroupOf K) := Group.isSolvable_of_comm hcommQ
  exact Group.isSolvable_of_subgroup_quotient (Z.subgroupOf K)

public theorem s16h_e3_nilpotent_le_center {Γ : Type} [Group Γ] [Finite Γ]
    {X A B Z : Subgroup Γ} (hA : IsComponentOf A X) (t : Γ) (htX : t ∈ X)
    (hBt : B = A.map (MulAut.conj t).toMonoidHom)
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hAc : ∀ a ∈ A, (∀ b ∈ A, a * b = b * a) → a = 1) (hZX : Z ≤ X)
    (hZ : Nat.card ↥Z = 3)
    (hZn : ∀ x ∈ X, Z.map (MulAut.conj x).toMonoidHom = Z)
    (hZc : ∀ z ∈ Z, ∀ a ∈ A ⊔ B, z * a = a * z)
    (hK : ∀ k ∈ X, (∀ a ∈ A ⊔ B, k * a = a * k) →
      k ∈ Z ∨ (k ^ 2 = 1 ∧ ∀ z ∈ Z, k * z * k⁻¹ = z⁻¹)) :
    ∀ N : Subgroup Γ, N ≤ X ⊓ Subgroup.centralizer ((A ⊔ B : Subgroup Γ) : Set Γ) →
      (∀ x ∈ X, N.map (MulAut.conj x).toMonoidHom = N) →
      Group.IsNilpotent ↥N → N ≤ Z := by
  intro N hNK hNnorm hNnil
  by_cases hNbot : N = ⊥
  · rw [hNbot]; exact bot_le
  have hNX : N ≤ X := fun n hn => (hNK hn).1
  have hNc : N ≤ Subgroup.centralizer ((A ⊔ B : Subgroup Γ) : Set Γ) :=
    fun n hn => (hNK hn).2
  have hNin : CFSG.GorensteinWalter.IsNormalIn N X := by
    refine ⟨hNX, fun x hx n hn => ?_⟩
    have h := hNnorm x hx
    have hmem : x * n * x⁻¹ ∈ N.map (MulAut.conj x).toMonoidHom :=
      Subgroup.mem_map.mpr ⟨n, hn, by simp [MulAut.conj_apply]⟩
    rwa [h] at hmem
  by_contra hNZ
  obtain ⟨k, hkN, hkZ⟩ := SetLike.not_le_iff_exists.mp hNZ
  have hkX : k ∈ X := hNX hkN
  have hkc : ∀ a ∈ A ⊔ B, k * a = a * k :=
    fun a ha => (Subgroup.mem_centralizer_iff.mp (hNc hkN) a ha).symm
  have hkinv : k ^ 2 = 1 ∧ ∀ z ∈ Z, k * z * k⁻¹ = z⁻¹ := by
    rcases hK k hkX hkc with h | h
    · exact absurd h hkZ
    · exact h
  have hk1 : k ≠ 1 := fun h => hkZ (h ▸ Z.one_mem)
  haveI : Nontrivial ↥N :=
    ⟨⟨k, hkN⟩, ⟨1, N.one_mem⟩, fun h => hk1 (Subtype.ext_iff.mp h)⟩
  haveI : Group.IsNilpotent ↥N := hNnil
  have hcenter : ∃ c : ↥N, c ∈ Subgroup.center ↥N ∧ c ≠ 1 := by
    by_contra h
    apply Group.IsNilpotent.center_ne_bot ↥N
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    by_contra hx1
    exact h ⟨x, hx, hx1⟩
  obtain ⟨c, hccent, hc1⟩ := hcenter
  have hcX : (c : Γ) ∈ X := hNX c.2
  have hcc : ∀ a ∈ A ⊔ B, (c : Γ) * a = a * (c : Γ) :=
    fun a ha => (Subgroup.mem_centralizer_iff.mp (hNc c.2) a ha).symm
  have hc1' : (c : Γ) ≠ 1 := fun h => hc1 (Subtype.ext h)
  have hZN : Z ≤ N := by
    intro z hz
    have hzX : z ∈ X := hZX hz
    have hconj : z * k * z⁻¹ ∈ N := hNin.2 z hzX k hkN
    have hz3 : z ^ 3 = 1 := by
      have h : (⟨z, hz⟩ : ↥Z) ^ 3 = 1 := by
        rw [← orderOf_dvd_iff_pow_eq_one]
        have := orderOf_dvd_natCard (⟨z, hz⟩ : ↥Z)
        rwa [hZ] at this
      simpa using congrArg Subtype.val h
    have hkz : ⁅k, z⁆ = z := by
      rw [commutatorElement_def, hkinv.2 z hz]
      calc z⁻¹ * z⁻¹ = z⁻¹ * z⁻¹ * 1 := (mul_one _).symm
        _ = z⁻¹ * z⁻¹ * z ^ 3 := by rw [← hz3]
        _ = z := by group
    have hmem : ⁅k, z⁆ ∈ N := by
      have := N.mul_mem hkN (N.inv_mem hconj)
      simpa [commutatorElement_def, mul_assoc] using this
    rwa [hkz] at hmem
  rcases hK c.1 hcX hcc with hcZ | ⟨_hc2, hcinv⟩
  · have hcomm : (c : Γ) * k = k * (c : Γ) :=
      (congrArg Subtype.val
        ((Subgroup.mem_center_iff.mp hccent) ⟨k, hkN⟩)).symm
    have hceq : (c : Γ) = (c : Γ)⁻¹ := by
      have h1 : k * (c : Γ) * k⁻¹ = (c : Γ) := by rw [← hcomm]; group
      exact h1.symm.trans (hkinv.2 (c : Γ) hcZ)
    have hc2' : (c : Γ) ^ 2 = 1 := by
      rw [pow_two]
      exact (mul_eq_one_iff_eq_inv).mpr hceq
    have h2 : orderOf (⟨(c : Γ), hcZ⟩ : ↥Z) ∣ 2 := by
      rw [orderOf_dvd_iff_pow_eq_one]; exact Subtype.ext hc2'
    have h3 : orderOf (⟨(c : Γ), hcZ⟩ : ↥Z) ∣ 3 := by
      have := orderOf_dvd_natCard (⟨(c : Γ), hcZ⟩ : ↥Z)
      rwa [hZ] at this
    have h1 : orderOf (⟨(c : Γ), hcZ⟩ : ↥Z) = 1 := by
      have hg := Nat.dvd_gcd h2 h3
      rw [show Nat.gcd 2 3 = 1 by norm_num] at hg
      exact Nat.dvd_one.mp hg
    exact hc1' (Subtype.ext_iff.mp (orderOf_eq_one_iff.mp h1))
  · have hinvZ : ∀ z ∈ Z, z = z⁻¹ := by
      intro z hz
      have hcomm : (c : Γ) * z = z * (c : Γ) :=
        (congrArg Subtype.val
          ((Subgroup.mem_center_iff.mp hccent) ⟨z, hZN hz⟩)).symm
      have h1 : (c : Γ) * z * (c : Γ)⁻¹ = z := by rw [hcomm]; group
      exact h1.symm.trans (hcinv z hz)
    haveI : Nontrivial ↥Z := by
      rw [Subgroup.nontrivial_iff_ne_bot]
      intro hbot
      have : Nat.card ↥Z = 1 := by rw [hbot]; simp
      omega
    obtain ⟨z, hz, hz1⟩ : ∃ z ∈ Z, z ≠ 1 := by
      obtain ⟨z, hz⟩ := exists_ne (1 : ↥Z)
      exact ⟨z.1, z.2, fun h => hz (Subtype.ext h)⟩
    have hz2 : z ^ 2 = 1 := by
      rw [pow_two]
      exact (mul_eq_one_iff_eq_inv).mpr (hinvZ z hz)
    have h2 : orderOf (⟨z, hz⟩ : ↥Z) ∣ 2 := by
      rw [orderOf_dvd_iff_pow_eq_one]; exact Subtype.ext hz2
    have h3 : orderOf (⟨z, hz⟩ : ↥Z) ∣ 3 := by
      have := orderOf_dvd_natCard (⟨z, hz⟩ : ↥Z)
      rwa [hZ] at this
    have h1 : orderOf (⟨z, hz⟩ : ↥Z) = 1 := by
      have hg := Nat.dvd_gcd h2 h3
      rw [show Nat.gcd 2 3 = 1 by norm_num] at hg
      exact Nat.dvd_one.mp hg
    exact hz1 (Subtype.ext_iff.mp (orderOf_eq_one_iff.mp h1))

public theorem s16h_e3_fstar_eq_of_two_components {Γ : Type} [Group Γ] [Finite Γ]
    {X A B Z : Subgroup Γ} {p : ℕ} (hp : p.Prime)
    (hA : IsComponentOf A X) (t : Γ) (htX : t ∈ X)
    (hBt : B = A.map (MulAut.conj t).toMonoidHom)
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hAc : ∀ a ∈ A, (∀ b ∈ A, a * b = b * a) → a = 1) (hZX : Z ≤ X)
    (hZ : Nat.card ↥Z = p)
    (hZn : ∀ x ∈ X, Z.map (MulAut.conj x).toMonoidHom = Z)
    (hZc : ∀ z ∈ Z, ∀ a ∈ A ⊔ B, z * a = a * z)
    (hKs : Group.IsSolvable ↥(X ⊓ Subgroup.centralizer ((A ⊔ B : Subgroup Γ) : Set Γ)))
    (hFit : ∀ N : Subgroup Γ, N ≤ X ⊓ Subgroup.centralizer ((A ⊔ B : Subgroup Γ) : Set Γ) →
      (∀ x ∈ X, N.map (MulAut.conj x).toMonoidHom = N) →
      Group.IsNilpotent ↥N → N ≤ Z) :
    Fstar X = Z ⊔ (A ⊔ B) := by
  have hB : IsComponentOf B X := by
    rw [hBt]
    exact CFSG.LargeExtraspecial.S5.isComponentOf_map_conj hA htX
  have hlayer : CFSG.GorensteinWalter.componentLayerOf X = A ⊔ B := by
    refine le_antisymm ?_ (sup_le (le_sSup (s16h_e3_gw_of_open hA))
      (le_sSup (s16h_e3_gw_of_open hB)))
    refine sSup_le fun L hL => ?_
    by_cases hLA : L = A
    · rw [hLA]; exact le_sup_left
    by_cases hLB : L = B
    · rw [hLB]; exact le_sup_right
    have hLopen : IsComponentOf L X := s16h_e3_open_of_gw hL
    have hcA := CFSG.LargeExtraspecial.S5.commute_of_isComponentOf_ne hLopen hA hLA
    have hcB := CFSG.LargeExtraspecial.S5.commute_of_isComponentOf_ne hLopen hB hLB
    have hLcAB : L ≤ Subgroup.centralizer ((A ⊔ B : Subgroup Γ) : Set Γ) :=
      Subgroup.le_centralizer_iff.mpr (sup_le
        (Subgroup.le_centralizer_iff.mp
          (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcA))
        (Subgroup.le_centralizer_iff.mp
          (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcB)))
    have hLK : L ≤ X ⊓ Subgroup.centralizer ((A ⊔ B : Subgroup Γ) : Set Γ) :=
      le_inf hL.1 hLcAB
    haveI : Group.IsSolvable ↥(X ⊓ Subgroup.centralizer
        ((A ⊔ B : Subgroup Γ) : Set Γ)) := hKs
    have hLsolv : Group.IsSolvable ↥L :=
      Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hLK)
    haveI : Group.IsPerfect ↥L := ⟨hLopen.2.2.1⟩
    haveI : Nontrivial ↥L := by
      haveI : Nontrivial (↥L ⧸ Subgroup.center ↥L) := hLopen.2.2.2.toNontrivial
      exact (QuotientGroup.mk'_surjective (Subgroup.center ↥L)).nontrivial
    exact absurd hLsolv (Group.IsPerfect.not_isSolvable ↥L)
  have hfit : CFSG.fittingSubgroupOf X = Z := by
    refine le_antisymm ?_ ?_
    · set N := CFSG.fittingSubgroupOf X with hNdef
      have hNX : N ≤ X := CFSG.fittingSubgroupOf_le X
      have hNnil : Group.IsNilpotent ↥N := by
        have he : ↥(CFSG.fittingSubgroup ↥X) ≃* ↥N := by
          rw [hNdef]
          exact Subgroup.equivMapOfInjective (CFSG.fittingSubgroup ↥X) X.subtype
            X.subtype_injective
        exact Group.nilpotent_of_mulEquiv he
      have hNn : CFSG.GorensteinWalter.IsNormalIn N X :=
        CFSG.GorensteinWalter.fittingSubgroupOf_isNormalIn X
      have hNconj : ∀ x ∈ X, N.map (MulAut.conj x).toMonoidHom = N := by
        intro x hx
        refine le_antisymm ?_ ?_
        · rintro y ⟨n, hn, rfl⟩
          exact hNn.2 x hx n hn
        · intro n hn
          refine ⟨x⁻¹ * n * x, ?_, ?_⟩
          · simpa using hNn.2 x⁻¹ (X.inv_mem hx) n hn
          · simp [MulAut.conj_apply, mul_assoc]
      have hNc : N ≤ Subgroup.centralizer ((A ⊔ B : Subgroup Γ) : Set Γ) := by
        have hcomm := CFSG.GorensteinWalter.layer_centralizes_fitting X
        rw [Subgroup.commutator_comm] at hcomm
        have := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
        rwa [hlayer] at this
      exact hFit N (le_inf hNX hNc) hNconj hNnil
    · haveI : Fact p.Prime := ⟨hp⟩
      have hZpg : IsPGroup p ↥Z := IsPGroup.of_card (n := 1) (by simpa using hZ)
      haveI : Group.IsNilpotent ↥Z := hZpg.isNilpotent
      have hZnorm' : (Z.subgroupOf X).Normal := by
        refine ⟨fun z hz g => ?_⟩
        rw [Subgroup.mem_subgroupOf] at hz ⊢
        have hg := hZn (g : Γ) g.2
        have hmem : MulAut.conj (g : Γ) (z : Γ) ∈ Z := by
          have hmem' : MulAut.conj (g : Γ) (z : Γ) ∈
              Z.map (MulAut.conj (g : Γ)).toMonoidHom :=
            Subgroup.mem_map.mpr ⟨(z : Γ), hz, rfl⟩
          rwa [hg] at hmem'
        simpa [MulAut.conj_apply] using hmem
      have hZnil' : Group.IsNilpotent ↥(Z.subgroupOf X) :=
        Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hZX).symm
      have hZsub : Z.subgroupOf X ≤ CFSG.fittingSubgroup ↥X :=
        le_sSup ⟨hZnorm', hZnil'⟩
      calc Z = (Z.subgroupOf X).map X.subtype := (Subgroup.map_subgroupOf_eq_of_le hZX).symm
        _ ≤ (CFSG.fittingSubgroup ↥X).map X.subtype := Subgroup.map_mono hZsub
        _ = CFSG.fittingSubgroupOf X := rfl
  have hFstar : Fstar X = CFSG.GorensteinWalter.generalizedFittingSubgroupOf X := by
    unfold Fstar
    rw [CFSG.Adapters.genFittingFStar_eq ↥X]
    exact CFSG.GorensteinWalter.generalizedFittingSubgroupOf_subgroup_top_eq X
  rw [hFstar]
  unfold CFSG.GorensteinWalter.generalizedFittingSubgroupOf
  rw [hlayer, show CFSG.GorensteinWalter.fittingSubgroupOf X = Z from hfit]

private noncomputable def s16h_e3_supProdEquiv {Γ : Type*} [Group Γ] {H K : Subgroup Γ}
    (hcomm : ∀ h ∈ H, ∀ k ∈ K, h * k = k * h) (hinf : H ⊓ K = ⊥) :
    ↥(H ⊔ K) ≃* ↥H × ↥K := by
  have hHcent : H ≤ Subgroup.centralizer (K : Set Γ) := by
    intro h hh
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact (hcomm h hh k hk).symm
  have hHnorm : H ≤ Subgroup.normalizer (K : Set Γ) :=
    hHcent.trans (Subgroup.centralizer_le_normalizer _)
  have hset : (↑(H ⊔ K) : Set Γ) = (H : Set Γ) * (K : Set Γ) :=
    Subgroup.coe_mul_of_left_le_normalizer_right H K hHnorm
  let hφ : ↥H × ↥K →* ↥(H ⊔ K) :=
    { toFun := fun q => ⟨(q.1 : Γ) * (q.2 : Γ),
        (H ⊔ K).mul_mem (mem_sup_left q.1.2) (mem_sup_right q.2.2)⟩
      map_one' := by ext; simp
      map_mul' := by
        intro q r
        ext
        have hc : (r.1 : Γ) * q.2 = q.2 * r.1 := hcomm r.1 r.1.2 q.2 q.2.2
        calc ((q.1 : Γ) * r.1) * ((q.2 : Γ) * r.2)
            = (q.1 : Γ) * (r.1 * ((q.2 : Γ) * r.2)) := by group
          _ = (q.1 : Γ) * ((r.1 * q.2) * r.2) := by group
          _ = (q.1 : Γ) * ((q.2 : Γ) * (r.1 * r.2)) := by rw [hc]; group
          _ = ((q.1 : Γ) * q.2) * (r.1 * r.2) := by group }
  refine (MulEquiv.ofBijective hφ ⟨?_, ?_⟩).symm
  · intro q r hqr
    have h1 : (q.1 : Γ) * q.2 = r.1 * r.2 := by
      have h := congrArg Subtype.val hqr
      dsimp only [hφ] at h
      exact h
    have hmem : (r.1 : Γ)⁻¹ * q.1 ∈ H ⊓ K := by
      refine ⟨H.mul_mem (H.inv_mem r.1.2) q.1.2, ?_⟩
      have heq : (r.1 : Γ)⁻¹ * q.1 = r.2 * (q.2 : Γ)⁻¹ :=
        mul_right_cancel (b := (q.2 : Γ)) (by
          calc (r.1 : Γ)⁻¹ * q.1 * q.2 = (r.1 : Γ)⁻¹ * (q.1 * q.2) := by group
            _ = (r.1 : Γ)⁻¹ * (r.1 * r.2) := by rw [h1]
            _ = r.2 := by group
            _ = (r.2 * (q.2 : Γ)⁻¹) * q.2 := by group)
      rw [heq]
      exact K.mul_mem r.2.2 (K.inv_mem q.2.2)
    rw [hinf] at hmem
    have hrq : (r.1 : Γ)⁻¹ * q.1 = 1 := Subgroup.mem_bot.mp hmem
    have hq1 : q.1 = r.1 := by
      have := congrArg (fun x => (r.1 : Γ) * x) hrq
      simpa [mul_assoc] using this
    have hq2 : q.2 = r.2 := by
      have h1' : (q.1 : Γ) * q.2 = q.1 * r.2 := by rw [h1, hq1]
      exact Subtype.ext (mul_left_cancel h1')
    exact Prod.ext hq1 hq2
  · intro x
    have hx : (x : Γ) ∈ (H : Set Γ) * (K : Set Γ) := by
      rw [← hset]
      exact x.2
    obtain ⟨h, hh, k, hk, hk_eq⟩ := Set.mem_mul.mp hx
    refine ⟨(⟨h, hh⟩, ⟨k, hk⟩), Subtype.ext ?_⟩
    dsimp only [hφ]
    exact hk_eq

private theorem s16h_e3_iso_of_fstar_eq {Γ : Type} [Group Γ] {X A B Z : Subgroup Γ} {p : ℕ}
    (hp : p.Prime) (hF : Fstar X = Z ⊔ (A ⊔ B))
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hABinf : A ⊓ B = ⊥) (hZc : ∀ z ∈ Z, ∀ a ∈ A ⊔ B, z * a = a * z)
    (hZinf : Z ⊓ (A ⊔ B) = ⊥) (hZ : Nat.card ↥Z = p)
    (eB : ↥B ≃* ↥A) :
    Nonempty (↥(Fstar X) ≃* Multiplicative (ZMod p) × ↥A × ↥A) := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [hF]
  have eZK : ↥(Z ⊔ (A ⊔ B)) ≃* ↥Z × ↥(A ⊔ B) :=
    s16h_e3_supProdEquiv hZc hZinf
  have eAB : ↥(A ⊔ B) ≃* ↥A × ↥B := s16h_e3_supProdEquiv hAB hABinf
  have eZ : ↥Z ≃* Multiplicative (ZMod p) := mulEquivOfPrimeCardEq hZ (by simp)
  refine ⟨(eZK.trans ((MulEquiv.prodCongr (MulEquiv.refl ↥Z) eAB).trans
      (MulEquiv.prodCongr (MulEquiv.refl ↥Z) (MulEquiv.prodCongr (MulEquiv.refl ↥A) eB)))).trans
    (MulEquiv.prodCongr eZ (MulEquiv.refl (↥A × ↥A)))⟩

theorem s16h_fstar_iso_of_two_components_gen {Γ : Type} [Group Γ] [Finite Γ]
    {X A B Z : Subgroup Γ} {p : ℕ} (hp : p.Prime)
    (hA : IsComponentOf A X) (t : Γ) (htX : t ∈ X)
    (hBt : B = A.map (MulAut.conj t).toMonoidHom)
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hAc : ∀ a ∈ A, (∀ b ∈ A, a * b = b * a) → a = 1) (hZX : Z ≤ X) (hZ : Nat.card ↥Z = p)
    (hZn : ∀ x ∈ X, Z.map (MulAut.conj x).toMonoidHom = Z)
    (hZc : ∀ z ∈ Z, ∀ a ∈ A ⊔ B, z * a = a * z)
    (hKs : Group.IsSolvable ↥(X ⊓ Subgroup.centralizer ((A ⊔ B : Subgroup Γ) : Set Γ)))
    (hFit : ∀ N : Subgroup Γ, N ≤ X ⊓ Subgroup.centralizer ((A ⊔ B : Subgroup Γ) : Set Γ) →
      (∀ x ∈ X, N.map (MulAut.conj x).toMonoidHom = N) → Group.IsNilpotent ↥N → N ≤ Z) :
    Nonempty (↥(Fstar X) ≃* Multiplicative (ZMod p) × ↥A × ↥A) := by
  have hB : IsComponentOf B X := by
    rw [hBt]
    exact CFSG.LargeExtraspecial.S5.isComponentOf_map_conj hA htX
  have heB : ↥B ≃* ↥A := by
    have hABe : ↥A ≃* ↥B := by
      rw [hBt]
      exact Subgroup.equivMapOfInjective A (MulAut.conj t).toMonoidHom
        (MulAut.conj t).injective
    exact hABe.symm
  have hABinf : A ⊓ B = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    exact hAc x hx.1 fun b hb => (hAB b hb x hx.2).symm
  have hBc : ∀ b ∈ B, (∀ c ∈ B, b * c = c * b) → b = 1 := by
    intro b hb hbc
    have he : ↥A ≃* ↥B := by
      rw [hBt]
      exact Subgroup.equivMapOfInjective A (MulAut.conj t).toMonoidHom
        (MulAut.conj t).injective
    have h1 : he.symm ⟨b, hb⟩ = 1 :=
      Subtype.ext (hAc (he.symm ⟨b, hb⟩).1 (he.symm ⟨b, hb⟩).2 fun a ha => by
        show ((he.symm ⟨b, hb⟩ * ⟨a, ha⟩ : ↥A) : Γ) =
          ((⟨a, ha⟩ * he.symm ⟨b, hb⟩ : ↥A) : Γ)
        apply congrArg Subtype.val
        apply he.injective
        rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
        refine Subtype.ext ?_
        exact hbc (he ⟨a, ha⟩) (he ⟨a, ha⟩).2)
    have h2 : (⟨b, hb⟩ : ↥B) = 1 := by
      rw [← MulEquiv.apply_symm_apply he ⟨b, hb⟩, h1, map_one]
    exact Subtype.ext_iff.mp h2
  have hZinf : Z ⊓ (A ⊔ B) = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    rw [Subgroup.mem_bot]
    have hsetAB : (↑(A ⊔ B) : Set Γ) = (A : Set Γ) * (B : Set Γ) :=
      Subgroup.coe_mul_of_left_le_normalizer_right A B
        ((show A ≤ Subgroup.centralizer (B : Set Γ) from fun a ha => by
          rw [Subgroup.mem_centralizer_iff]
          intro b hb
          exact (hAB a ha b hb).symm).trans (Subgroup.centralizer_le_normalizer _))
    have hzmem : z ∈ (A : Set Γ) * (B : Set Γ) := by
      rw [← hsetAB]
      exact hz.2
    obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_mul.mp hzmem
    have ha1 : a = 1 := hAc a ha fun a' ha' => by
      have h := hZc z hz.1 a' (mem_sup_left ha')
      rw [← hab] at h
      have h2 : (a * b) * a' = a' * (a * b) := h
      exact mul_right_cancel (show (a * a') * b = (a' * a) * b by
        calc (a * a') * b = a * (a' * b) := by group
          _ = a * (b * a') := by rw [hAB a' ha' b hb]
          _ = (a * b) * a' := by group
          _ = a' * (a * b) := h2
          _ = (a' * a) * b := by group)
    have hz_eq : z = b := by rw [← hab, ha1, one_mul]
    have hb1 : b = 1 := hBc b hb fun c hc => by
      have h := hZc z hz.1 c (mem_sup_right hc)
      rw [hz_eq] at h
      exact h
    rw [hz_eq, hb1]
  exact s16h_e3_iso_of_fstar_eq hp
    (s16h_e3_fstar_eq_of_two_components hp hA t htX hBt hAB hAc hZX hZ hZn hZc hKs hFit)
    hAB hABinf hZc hZinf hZ heB

theorem s16h_fstar_iso_of_two_components {Γ : Type} [Group Γ] [Finite Γ] {X A B Z : Subgroup Γ}
    (hA : IsComponentOf A X) (t : Γ) (htX : t ∈ X)
    (hBt : B = A.map (MulAut.conj t).toMonoidHom)
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hAc : ∀ a ∈ A, (∀ b ∈ A, a * b = b * a) → a = 1) (hZX : Z ≤ X) (hZ : Nat.card ↥Z = 3)
    (hZn : ∀ x ∈ X, Z.map (MulAut.conj x).toMonoidHom = Z)
    (hZc : ∀ z ∈ Z, ∀ a ∈ A ⊔ B, z * a = a * z)
    (hK : ∀ k ∈ X, (∀ a ∈ A ⊔ B, k * a = a * k) →
      k ∈ Z ∨ (k ^ 2 = 1 ∧ ∀ z ∈ Z, k * z * k⁻¹ = z⁻¹)) :
    Nonempty (↥(Fstar X) ≃* Multiplicative (ZMod 3) × ↥A × ↥A) :=
  s16h_fstar_iso_of_two_components_gen Nat.prime_three hA t htX hBt hAB hAc hZX hZ hZn hZc
    (s16h_e3_solvable_centralizer hA t htX hBt hAB hAc hZX hZ hZn hZc hK)
    (s16h_e3_nilpotent_le_center hA t htX hBt hAB hAc hZX hZ hZn hZc hK)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
