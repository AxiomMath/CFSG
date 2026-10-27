module

public import CFSG.RankThree.PartTwo.Sec15.Item15Res11ProofDefs
public import CFSG.RankThree.PartTwo.Sec14.ONCoverProofModel
public import CFSG.RankThree.PartTwo.Sec13.Item134ONProof
public import CFSG.Sporadic.Suz.Simple

public section

namespace CFSG.RankThree.PartTwo.Sec15

attribute [local irreducible] dotProduct

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.Native.ONTriple Subgroup

namespace ONCoverCent

theorem isTripleCover_congr {X X' Y : Type*} [Group X] [Group X'] [Group Y] (e : X ≃* X')
    (h : Sec4.IsTripleCover X Y) : Sec4.IsTripleCover X' Y := by
  obtain ⟨hcard, ⟨φ⟩⟩ := h
  have hc : (Subgroup.center X).map e.toMonoidHom = Subgroup.center X' :=
    Subgroup.map_center_eq e
  refine ⟨?_, ⟨(QuotientGroup.congr _ _ e hc).symm.trans φ⟩⟩
  rw [← hc, Subgroup.card_map_of_injective e.injective, hcard]

theorem eq_bot_of_normal_of_not_dvd {X Y : Type*} [Group X] [Finite X] [Group Y]
    [IsSimpleGroup Y] (h3 : 3 ∣ Nat.card Y) (hT : Sec4.IsTripleCover X Y) {N : Subgroup X}
    (hN : N.Normal) (hN3 : ¬ 3 ∣ Nat.card N) : N = ⊥ := by
  obtain ⟨hZ, ⟨e⟩⟩ := hT
  set π := QuotientGroup.mk' (center X) with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hn : ((N.map π).map e.toMonoidHom).Normal :=
    (hN.map π hπs).map e.toMonoidHom e.surjective
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((N.map π).map e.toMonoidHom) with h | h
  · rw [map_eq_bot_iff_of_injective _ e.injective, Subgroup.map_eq_bot_iff, hπ,
      QuotientGroup.ker_mk'] at h
    have hdvd : Nat.card N ∣ 3 := hZ ▸ Subgroup.card_dvd_of_le h
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3'
    · exact Subgroup.eq_bot_of_card_eq N h1
    · exact absurd (by rw [h3'] : 3 ∣ Nat.card N) hN3
  · exfalso
    apply hN3
    have hc : Nat.card ((N.map π).map e.toMonoidHom) = Nat.card Y := by
      rw [h, Subgroup.card_top]
    rw [card_map_of_injective e.injective] at hc
    exact h3.trans (hc ▸ Subgroup.card_map_dvd N π)

theorem isPerfect_of_isTripleCover {X Y : Type*} [Group X] [Finite X] [Group Y]
    [IsSimpleGroup Y] (hY : ¬ (Nat.card Y).Prime) (hT : Sec4.IsTripleCover X Y)
    {P : Subgroup X} [Group.IsPerfect P] {z : X} (hzP : z ∈ P) (hzZ : z ∈ center X)
    (hz1 : z ≠ 1) : Group.IsPerfect X := by
  obtain ⟨hZ, ⟨e⟩⟩ := hT
  have hYc : commutator Y = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator Y) with h | h
    · exfalso
      rw [_root_.commutator_def, commutator_eq_bot_iff_le_centralizer] at h
      have hc : IsMulCommutative Y := ⟨⟨fun a b =>
        (mem_centralizer_iff.mp (h (mem_top a)) b (mem_top b)).symm⟩⟩
      exact hY (Group.is_simple_iff_prime_card.mp inferInstance)
    · exact h
  have hYp : Group.IsPerfect Y := ⟨hYc⟩
  have hQp : Group.IsPerfect (X ⧸ center X) :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  set π := QuotientGroup.mk' (center X) with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hD : (commutator X).map π = ⊤ := by
    rw [_root_.commutator_def, Subgroup.map_commutator, Subgroup.map_top_of_surjective π hπs,
      ← _root_.commutator_def]
    exact Group.IsPerfect.commutator_eq_top
  have hDZ : commutator X ⊔ center X = ⊤ := by
    have h1 := Subgroup.comap_map_eq π (commutator X)
    rw [hD, Subgroup.comap_top, hπ, QuotientGroup.ker_mk'] at h1
    exact h1.symm
  have hPD : P ≤ commutator X := by
    rw [← Subgroup.commutator_eq_self (H := P), _root_.commutator_def]
    exact Subgroup.commutator_mono le_top le_top
  have hz3 : z ^ 3 = 1 := by
    have h1 := pow_card_eq_one' (G := center X) (x := ⟨z, hzZ⟩)
    rw [hZ] at h1
    exact congrArg Subtype.val h1
  have hZz : center X = zpowers z := by
    symm
    apply eq_of_le_of_card_ge (zpowers_le.mpr hzZ)
    rw [hZ, Nat.card_zpowers, orderOf_eq_prime hz3 hz1]
  have hZD : center X ≤ commutator X := by
    rw [hZz, zpowers_le]
    exact hPD hzP
  exact ⟨(sup_eq_left.mpr hZD).symm.trans hDZ⟩

@[expose] def conjRestrict {G : Type*} [Group G] (N : Subgroup G) {y : G}
    (hy : y ∈ normalizer (N : Set G)) : N ≃* N where
  toFun n := ⟨y * n * y⁻¹, (mem_normalizer_iff.mp hy n).mp n.2⟩
  invFun n := ⟨y⁻¹ * n * y, (mem_normalizer_iff.mp hy (y⁻¹ * n * y)).mpr (by
    rw [show y * (y⁻¹ * (n : G) * y) * y⁻¹ = n by group]
    exact n.2)⟩
  left_inv n := Subtype.ext (by simp only; group)
  right_inv n := Subtype.ext (by simp only; group)
  map_mul' a b := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

theorem coe_conjRestrict {G : Type*} [Group G] (N : Subgroup G) {y : G}
    (hy : y ∈ normalizer (N : Set G)) (n : N) : (conjRestrict N hy n : G) = y * n * y⁻¹ :=
  rfl

theorem map_conjRestrict_subgroupOf {G : Type*} [Group G] {N M : Subgroup G} {y : G}
    (hy : y ∈ normalizer (N : Set G)) (hyM : y ∈ normalizer (M : Set G)) :
    (M.subgroupOf N).map (conjRestrict N hy : N →* N) = M.subgroupOf N := by
  ext n
  simp only [mem_map, mem_subgroupOf]
  constructor
  · rintro ⟨m, hm, rfl⟩
    exact (mem_normalizer_iff.mp hyM m).mp hm
  · intro hn
    refine ⟨(conjRestrict N hy).symm n, ?_, (conjRestrict N hy).apply_symm_apply n⟩
    show y⁻¹ * (n : G) * y ∈ M
    refine (mem_normalizer_iff.mp hyM (y⁻¹ * n * y)).mpr ?_
    rw [show y * (y⁻¹ * (n : G) * y) * y⁻¹ = n by group]
    exact hn

end ONCoverCent

open ONCoverCent

theorem ks1515ONCent_holds :
    KS1515ONCent := by
  intro H _ _ M K X₀ T y h3M hKM hKcov hθM hX₀N hX₀M hX₀p hX₀cov hz hTN hTM hT2 hTX hyM hyN
    hyX hy3 hyT hTy
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hONs : IsSimpleGroup Blueprint.NativeSporadic.ON := CFSG.Sporadic.ON.isSimpleGroup_ON
  have h3ON : 3 ∣ Nat.card Blueprint.NativeSporadic.ON := by
    rw [CFSG.Sporadic.ON.card_ON_eq]; norm_num
  have hONp : ¬ (Nat.card Blueprint.NativeSporadic.ON).Prime := by
    rw [CFSG.Sporadic.ON.card_ON_eq]; norm_num
  set N := K ⊔ M with hNdef
  have hX₀N' : X₀ ≤ N := by rw [hNdef, sup_comm]; exact hX₀N
  have hTN' : T ≤ N := by rw [hNdef, sup_comm]; exact hTN
  have hyN' : y ∈ normalizer (N : Set H) := by rw [hNdef, sup_comm]; exact hyN
  have hKN : K ≤ N := le_sup_left
  have hMn : (M.subgroupOf N).Normal := Subgroup.normal_subgroupOf_sup_of_le_normalizer hKM
  have hMK : (M.subgroupOf K).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hKM
  set q := QuotientGroup.mk' (M.subgroupOf N) with hq
  have hq1 : ∀ n : N, q n = 1 ↔ (n : H) ∈ M := fun n => by
    rw [hq, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_subgroupOf]
  have hθeq : M.subgroupOf K = aschbacherSolvableCore 3 ↥K := by
    apply le_antisymm
    · set θ := aschbacherSolvableCore 3 ↥K
      have hmap := eq_bot_of_normal_of_not_dvd h3ON hKcov
        (N := (M.subgroupOf K).map (QuotientGroup.mk' θ))
        (hMK.map _ (QuotientGroup.mk'_surjective θ)) (by
          intro h3
          apply h3M
          refine h3.trans ((card_map_dvd _ _).trans ?_)
          rw [← card_map_of_injective K.subtype_injective, subgroupOf_map_subtype]
          exact Subgroup.card_dvd_of_le inf_le_left)
      rwa [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hmap
    · intro x hx
      rw [mem_subgroupOf]
      exact hθM ⟨x, hx, rfl⟩
  have hQT : Sec4.IsTripleCover (↥N ⧸ M.subgroupOf N) Blueprint.NativeSporadic.ON :=
    isTripleCover_congr ((QuotientGroup.quotientMulEquivOfEq hθeq.symm).trans
      (QuotientGroup.quotientInfEquivProdNormalizerQuotient K M hKM)) hKcov
  have hsurj : ∀ x : ↥N ⧸ M.subgroupOf N, ∃ k ∈ K, ∃ hk : k ∈ N, q ⟨k, hk⟩ = x := by
    intro x
    obtain ⟨n, rfl⟩ := QuotientGroup.mk'_surjective (M.subgroupOf N) x
    have hn : (n : H) ∈ (K ⊔ M : Subgroup H) := n.2
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right K M hKM] at hn
    obtain ⟨k, hk, m, hm, hkm⟩ := hn
    refine ⟨k, hk, hKN hk, ?_⟩
    rw [hq, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, mem_subgroupOf]
    have e : ((⟨k, hKN hk⟩ : N)⁻¹ * n : N) = (m : H) := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, ← hkm]
      group
    rw [e]
    exact hm
  obtain ⟨z, hzX, hz1, hKz⟩ := hz
  set zq := q ⟨z, hX₀N' hzX⟩ with hzq
  have hzq1 : zq ≠ 1 := by
    rw [hzq, Ne, hq1]
    intro hzM
    have : z ∈ X₀ ⊓ M := mem_inf.mpr ⟨hzX, hzM⟩
    rw [hX₀M, mem_bot] at this
    exact hz1 this
  have hzqZ : zq ∈ center (↥N ⧸ M.subgroupOf N) := by
    rw [mem_center_iff]
    intro x
    obtain ⟨k, hk, hkN, rfl⟩ := hsurj x
    rw [hzq, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (mem_centralizer_iff.mp (hKz hk) z (Set.mem_singleton z)).symm
  set fX : ↥X₀ →* (↥N ⧸ M.subgroupOf N) := q.comp (Subgroup.inclusion hX₀N') with hfX
  have hfXinj : Function.Injective fX := by
    rw [injective_iff_map_eq_one]
    intro x hx
    rw [hfX, MonoidHom.comp_apply, hq1] at hx
    have : (x : H) ∈ X₀ ⊓ M := mem_inf.mpr ⟨x.2, hx⟩
    rw [hX₀M, mem_bot] at this
    exact Subtype.ext this
  set fT : ↥T →* (↥N ⧸ M.subgroupOf N) := q.comp (Subgroup.inclusion hTN') with hfT
  have hfTinj : Function.Injective fT := by
    rw [injective_iff_map_eq_one]
    intro t ht
    rw [hfT, MonoidHom.comp_apply, hq1] at ht
    have : (t : H) ∈ T ⊓ M := mem_inf.mpr ⟨t.2, ht⟩
    rw [hTM, mem_bot] at this
    exact Subtype.ext this
  have := hX₀p
  have hXp : Group.IsPerfect fX.range := Group.IsPerfect.range fX
  have hX₀c : Nat.card X₀ = 1080 := by
    obtain ⟨hZc, ⟨eA⟩⟩ := hX₀cov
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (center ↥X₀), hZc,
      Nat.card_congr eA.toEquiv, card_alt_six]
  have hXc : Nat.card fX.range = 1080 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hfXinj).toEquiv, hX₀c]
  have hzqX : zq ∈ fX.range := ⟨⟨z, hzX⟩, rfl⟩
  have hQp : Group.IsPerfect (↥N ⧸ M.subgroupOf N) :=
    isPerfect_of_isTripleCover hONp hQT hzqX hzqZ hzq1
  obtain ⟨ψ⟩ := Sec13.ON134.nonempty_equiv_model hQp hQT
  set α := QuotientGroup.congr (M.subgroupOf N) (M.subgroupOf N) (conjRestrict N hyN')
    (map_conjRestrict_subgroupOf hyN' hyM) with hα
  have hαq : ∀ n : N, α (q n) = q (conjRestrict N hyN' n) := fun n => rfl
  have hαz : α zq = zq := by
    rw [hzq, hαq]
    congr 1
    apply Subtype.ext
    rw [coe_conjRestrict]
    show y * z * y⁻¹ = z
    rw [← mem_centralizer_iff.mp hyX z hzX, mul_inv_cancel_right]
  have hz3 : zq ^ 3 = 1 := by
    have h1 := pow_card_eq_one' (G := center (↥N ⧸ M.subgroupOf N)) (x := ⟨zq, hzqZ⟩)
    rw [hQT.1] at h1
    exact congrArg Subtype.val h1
  have hZeq : center (↥N ⧸ M.subgroupOf N) = zpowers zq := by
    symm
    apply eq_of_le_of_card_ge (zpowers_le.mpr hzqZ)
    rw [hQT.1, Nat.card_zpowers, orderOf_eq_prime hz3 hzq1]
  have hαZ : ∀ w ∈ center (↥N ⧸ M.subgroupOf N), α w = w := by
    intro w hw
    rw [hZeq] at hw
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hw
    rw [map_zpow, hαz]
  obtain ⟨g, hg⟩ := Sec13.ON134.aut_inner ψ α hαZ
  have hgX : ∀ x : ↥X₀, g * fX x * g⁻¹ = fX x := by
    intro x
    rw [← hg, hfX, MonoidHom.comp_apply, hαq]
    congr 1
    apply Subtype.ext
    rw [coe_conjRestrict]
    show y * x * y⁻¹ = x
    rw [← mem_centralizer_iff.mp hyX x x.2, mul_inv_cancel_right]
  have hgTr : ∀ t : ↥T, g * fT t * g⁻¹ =
      fT ⟨y * t * y⁻¹, (mem_normalizer_iff.mp hyT t).mp t.2⟩ := by
    intro t
    rw [← hg, hfT, MonoidHom.comp_apply, hαq]
    rfl
  have hg3Z : g ^ 3 ∈ center (↥N ⧸ M.subgroupOf N) := by
    rw [mem_center_iff]
    intro x
    obtain ⟨n, rfl⟩ := QuotientGroup.mk'_surjective (M.subgroupOf N) x
    have h3 : α (α (α (q n))) = q n := by
      rw [hαq, hαq, hαq]
      congr 1
      apply Subtype.ext
      rw [coe_conjRestrict, coe_conjRestrict, coe_conjRestrict]
      have hy3' : y * (y * y) = 1 := by rw [← pow_three]; exact hy3
      have e : y * (y * (y * (n : H) * y⁻¹) * y⁻¹) * y⁻¹ =
          y * (y * y) * n * (y * (y * y))⁻¹ := by group
      rw [e, hy3', one_mul, inv_one, mul_one]
    rw [hg, hg, hg] at h3
    calc q n * g ^ 3 = g * (g * (g * q n * g⁻¹) * g⁻¹) * g⁻¹ * g ^ 3 := by rw [h3]
      _ = g ^ 3 * q n := by rw [pow_three]; group
  have hg3 : g ^ 3 = 1 := by
    have h1 := pow_card_eq_one' (G := center (↥N ⧸ M.subgroupOf N)) (x := ⟨g ^ 3, hg3Z⟩)
    rw [hQT.1] at h1
    have h2 : (g ^ 3) ^ 3 = 1 := congrArg Subtype.val h1
    exact Sec13.ON134.pow_three_eq_one ψ (k := 2)
      (by rw [show (3 : ℕ) ^ 2 = 3 * 3 by norm_num, pow_mul]; exact h2)
  by_cases hgZ : g ∈ center (↥N ⧸ M.subgroupOf N)
  ·
    have hyt : ∀ t ∈ T, y * t = t * y := by
      intro t ht
      have h1 := hgTr ⟨t, ht⟩
      rw [(mem_center_iff.mp hgZ _).symm, mul_inv_cancel_right] at h1
      have h2 := hfTinj h1
      have h3 : y * t * y⁻¹ = t := congrArg Subtype.val h2.symm
      calc y * t = y * t * y⁻¹ * y := by group
        _ = t * y := by rw [h3]
    have hTc : T ≤ centralizer (zpowers y : Set H) := by
      intro t ht
      rw [mem_centralizer_iff]
      intro w hw
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hw
      exact (Commute.zpow_left (hyt t ht) k).eq
    exact hTy.trans (commutator_eq_bot_iff_le_centralizer.mpr hTc)
  ·
    have hg'3 : ψ g ^ 3 = 1 := by rw [← map_pow, hg3, map_one]
    have hg'z : ψ g ∉ zpowers zG := fun h => hgZ ((Sec13.ON134.mem_center_iff_model ψ).mpr h)
    have hX'p : Group.IsPerfect (fX.range.map ψ.toMonoidHom) := Group.IsPerfect.map _
    have hX'c : Nat.card (fX.range.map ψ.toMonoidHom) = 1080 := by
      rw [card_map_of_injective ψ.injective, hXc]
    have hX'g : fX.range.map ψ.toMonoidHom ≤ centralizer {ψ g} := by
      rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
      rw [mem_centralizer_singleton_iff]
      have h1 : g * fX x = fX x * g := by
        calc g * fX x = g * fX x * g⁻¹ * g := by group
          _ = fX x * g := by rw [hgX x]
      rw [MulEquiv.coe_toMonoidHom, ← map_mul, ← map_mul, h1]
    have hT'2 : IsPGroup 2 (fT.range.map ψ.toMonoidHom) :=
      (hT2.of_equiv (MonoidHom.ofInjective hfTinj)).map _
    have hT'X : fT.range.map ψ.toMonoidHom ≤
        centralizer ((fX.range.map ψ.toMonoidHom : Subgroup GM) : Set GM) := by
      rintro _ ⟨_, ⟨t, rfl⟩, rfl⟩
      rw [mem_centralizer_iff]
      rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
      have h1 : (x : H) * t = t * x := mem_centralizer_iff.mp (hTX t.2) x x.2
      rw [MulEquiv.coe_toMonoidHom, ← map_mul, ← map_mul]
      congr 1
      rw [hfX, hfT, MonoidHom.comp_apply, MonoidHom.comp_apply, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext h1
    have hgT : g ∈ normalizer (fT.range : Set (↥N ⧸ M.subgroupOf N)) := by
      rw [mem_normalizer_iff_map_conj_eq]
      apply eq_of_le_of_card_ge
      · rintro _ ⟨_, ⟨t, rfl⟩, rfl⟩
        exact ⟨_, (hgTr t).symm⟩
      · rw [card_map_of_injective (MulAut.conj g).injective]
    have hg'T : ψ g ∈ normalizer ((fT.range.map ψ.toMonoidHom : Subgroup GM) : Set GM) := by
      rw [← Subgroup.map_equiv_normalizer_eq]
      exact mem_map_of_mem _ hgT
    have hT' := eq_bot_of_le_centralizer hg'3 hg'z hX'p hX'c hX'g hT'2 hT'X hg'T
    rw [map_eq_bot_iff_of_injective _ ψ.injective] at hT'
    rw [eq_bot_iff]
    intro t ht
    have h1 : fT ⟨t, ht⟩ ∈ fT.range := ⟨⟨t, ht⟩, rfl⟩
    rw [hT', mem_bot, ← map_one fT] at h1
    exact congrArg Subtype.val (hfTinj h1)

end CFSG.RankThree.PartTwo.Sec15
