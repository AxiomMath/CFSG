module

public import CFSG.RankThree.PartTwo.Sec13.Item134Arg128FailPoint
import CFSG.RankThree.PartTwo.Sec13.Item136Lift
import CFSG.RankThree.PartTwo.Sec13.Item137Tools
import CFSG.RankThree.PartTwo.Sec14.Item14J2
import CFSG.RankThree.PartTwo.Sec13.Item13Prod

public section

namespace CFSG.RankThree.PartTwo.Sec13.Item134Arg128Fail

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec13.Item134SylowBarProof
open CFSG.ABGLocalTools (IsSylowOf)
open scoped commutatorElement

section Heis

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem heis_inf_centralizer_le_of_card_nine {P : Subgroup X} (hH : Sec4.IsHeisThree P)
    {E : Subgroup X} (hEP : E ≤ P) (hE9 : Nat.card E = 9) :
    P ⊓ Subgroup.centralizer (P : Set X) ≤ E := by
  obtain ⟨⟨-, hcomm, -, -⟩, h27, -⟩ := hH
  set E' := E.subgroupOf P with hE'
  have hE'9 : Nat.card E' = 9 := by
    rw [hE', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEP).toEquiv, hE9]
  have hidx : E'.index = 3 := by
    have h := E'.card_mul_index
    rw [hE'9, h27] at h
    omega
  have hnorm : E'.Normal := Subgroup.normal_of_index_eq_minFac_card (by
    rw [hidx, h27]
    norm_num)
  have hQ3 : Nat.card (↥P ⧸ E') = 3 := by
    rw [← Subgroup.index_eq_card, hidx]
  have hQcomm : ∀ q r : ↥P ⧸ E', q * r = r * q := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hcyc : IsCyclic (↥P ⧸ E') := isCyclic_of_prime_card hQ3
    intro q r
    obtain ⟨g, hg⟩ := hcyc.exists_generator
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg q)
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg r)
    exact zpow_mul_comm g m n
  have hcle : commutator ↥P ≤ E' := by
    rw [commutator_def, Subgroup.commutator_le]
    intro p _ q _
    rw [← QuotientGroup.eq_one_iff]
    change QuotientGroup.mk' E' ⁅p, q⁆ = 1
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hQcomm _ _
  rw [hcomm] at hcle
  intro z hz
  have hzc : (⟨z, hz.1⟩ : ↥P) ∈ Subgroup.center ↥P := by
    rw [← Sec14.map_subtype_center_eq] at hz
    obtain ⟨w, hw, hwz⟩ := hz
    have : w = ⟨z, hz.1⟩ := Subtype.ext hwz
    rw [← this]
    exact hw
  exact Subgroup.mem_subgroupOf.mp (hcle hzc)

omit [Finite X] in
theorem card_inf_centralizer_of_heis {P : Subgroup X} (hH : Sec4.IsHeisThree P) :
    Nat.card (P ⊓ Subgroup.centralizer (P : Set X) : Subgroup X) = 3 := by
  rw [← Sec14.map_subtype_center_eq, Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
  exact hH.1.2.2.2

omit [Finite X] in
theorem commutator_mem_inf_centralizer_of_heis {P : Subgroup X} (hH : Sec4.IsHeisThree P)
    {x y : X} (hx : x ∈ P) (hy : y ∈ P) :
    x * y * x⁻¹ * y⁻¹ ∈ P ⊓ Subgroup.centralizer (P : Set X) := by
  have h1 : ⁅(⟨x, hx⟩ : ↥P), (⟨y, hy⟩ : ↥P)⁆ ∈ Subgroup.center ↥P := by
    rw [← hH.1.2.1, commutator_def]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  rw [← Sec14.map_subtype_center_eq]
  refine ⟨_, h1, ?_⟩
  simp [commutatorElement_def]

end Heis

section Central

variable {G : Type} [Group G] [Finite G]

theorem exists_mem_inf_centralizer {J : Subgroup G}
    (hHeis : ∀ P : Sylow 3 (J ⧸ aschbacherSolvableCore 3 J),
      Sec4.IsHeisThree (P : Subgroup (J ⧸ aschbacherSolvableCore 3 J)))
    {E : Subgroup G} (hEJ : E ≤ J) (hE9 : Nat.card E = 9) {d : G} (hd1 : d ≠ 1)
    (hd3 : d ^ 3 = 1)
    (hcomm : ∀ x ∈ J, (∃ k : ℕ, x ^ 3 ^ k = 1) → x ∈ Subgroup.normalizer (E : Set G) →
      ∀ e ∈ E, x * e * x⁻¹ * e⁻¹ ∈ Subgroup.zpowers d) :
    ∃ hdJ : d ∈ J, ∃ P : Sylow 3 (J ⧸ aschbacherSolvableCore 3 J),
      QuotientGroup.mk' (aschbacherSolvableCore 3 J) (⟨d, hdJ⟩ : J) ∈
          (P : Subgroup (J ⧸ aschbacherSolvableCore 3 J)) ⊓
            Subgroup.centralizer ((P : Subgroup (J ⧸ aschbacherSolvableCore 3 J)) :
              Set (J ⧸ aschbacherSolvableCore 3 J)) ∧
        QuotientGroup.mk' (aschbacherSolvableCore 3 J) (⟨d, hdJ⟩ : J) ≠ 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 J) with hπ
  set E' := E.subgroupOf J with hE'
  have hE'9 : Nat.card E' = 9 := by
    rw [hE', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEJ).toEquiv, hE9]
  have hE'p : IsPGroup 3 E' := IsPGroup.of_card (n := 2) (by rw [hE'9]; norm_num)
  obtain ⟨S', hES'⟩ := hE'p.exists_le_sylow
  have hinj : Set.InjOn π (S' : Set J) := injOn_mk_of_isPGroup Nat.prime_three S'.isPGroup'
  set P : Sylow 3 (J ⧸ aschbacherSolvableCore 3 J) :=
    S'.mapSurjective (QuotientGroup.mk'_surjective _) with hPdef
  have hP : (P : Subgroup _) = (S' : Subgroup J).map π := Sylow.coe_mapSurjective _ _
  have hH := hHeis P
  set Eb := E'.map π with hEb
  have hEbP : Eb ≤ P := by
    rw [hP]
    exact Subgroup.map_mono hES'
  have hEb9 : Nat.card Eb = 9 := by rw [hEb, card_map_eq_of_injOn π (hinj.mono hES'), hE'9]
  have hZle := heis_inf_centralizer_le_of_card_nine hH hEbP hEb9
  have hZ3 := card_inf_centralizer_of_heis hH
  obtain ⟨eb, hebE, hebZ⟩ : ∃ eb ∈ Eb, eb ∉ (P : Subgroup (J ⧸ aschbacherSolvableCore 3 J)) ⊓
      Subgroup.centralizer ((P : Subgroup (J ⧸ aschbacherSolvableCore 3 J)) :
        Set (J ⧸ aschbacherSolvableCore 3 J)) := by
    by_contra hcon
    push Not at hcon
    have := Subgroup.card_le_of_le (show Eb ≤ (P : Subgroup (J ⧸ aschbacherSolvableCore 3 J)) ⊓
      Subgroup.centralizer ((P : Subgroup (J ⧸ aschbacherSolvableCore 3 J)) :
        Set (J ⧸ aschbacherSolvableCore 3 J)) from hcon)
    rw [hEb9, hZ3] at this
    omega
  have hebC : eb ∉ Subgroup.centralizer ((P : Subgroup (J ⧸ aschbacherSolvableCore 3 J)) :
      Set (J ⧸ aschbacherSolvableCore 3 J)) :=
    fun h => hebZ ⟨hEbP hebE, h⟩
  rw [Subgroup.mem_centralizer_iff] at hebC
  push Not at hebC
  obtain ⟨xb, hxbP, hxb⟩ := hebC
  obtain ⟨e, he, rfl⟩ := hebE
  have hxbP' := hxbP
  rw [hP] at hxbP'
  obtain ⟨x, hx, rfl⟩ := hxbP'
  have heS : e ∈ S' := hES' he
  set u : J := x * e * x⁻¹ * e⁻¹ with hu
  have huS : u ∈ S' := mul_mem (mul_mem (mul_mem hx heS) (inv_mem hx)) (inv_mem heS)
  have hπu : π u ∈ (P : Subgroup (J ⧸ aschbacherSolvableCore 3 J)) ⊓
      Subgroup.centralizer ((P : Subgroup (J ⧸ aschbacherSolvableCore 3 J)) :
        Set (J ⧸ aschbacherSolvableCore 3 J)) := by
    have h1 := commutator_mem_inf_centralizer_of_heis hH hxbP (hEbP ⟨e, he, rfl⟩)
    rw [hu, map_mul, map_mul, map_mul, map_inv, map_inv]
    exact h1
  have hu1 : (u : G) ≠ 1 := by
    intro h
    apply hxb
    have hu1' : u = 1 := Subtype.ext h
    have h2 : π u = 1 := by rw [hu1', map_one]
    rw [hu, map_mul, map_mul, map_mul, map_inv, map_inv] at h2
    calc π x * π e = (π x * π e * (π x)⁻¹ * (π e)⁻¹) * (π e * π x) := by group
      _ = π e * π x := by rw [h2, one_mul]
  have hS'27 : Nat.card (S' : Subgroup J) = 27 := by
    rw [← card_map_eq_of_injOn π hinj, ← hP]
    exact hH.2.1
  have hxE : (x : G) ∈ Subgroup.normalizer (E : Set G) := by
    set E'' := E'.subgroupOf (S' : Subgroup J) with hE''
    have hE''9 : Nat.card E'' = 9 := by
      rw [hE'', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hES').toEquiv, hE'9]
    have hidx : E''.index = 3 := by
      have h := E''.card_mul_index
      rw [hE''9, hS'27] at h
      omega
    have hnorm : E''.Normal := Subgroup.normal_of_index_eq_minFac_card (by
      rw [hidx, hS'27]
      norm_num)
    refine Subgroup.mem_normalizer_fintype fun y hy => ?_
    have hyE'' : (⟨⟨y, hEJ hy⟩, hES' (Subgroup.mem_subgroupOf.mpr hy)⟩ : (S' : Subgroup J)) ∈ E'' :=
      Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mpr hy)
    have h1 := hnorm.conj_mem _ hyE'' ⟨x, hx⟩
    exact Subgroup.mem_subgroupOf.mp (Subgroup.mem_subgroupOf.mp h1)
  have hx3 : ∃ k : ℕ, (x : G) ^ 3 ^ k = 1 := by
    obtain ⟨k, hk⟩ := S'.isPGroup' ⟨x, hx⟩
    have := congrArg (fun z : (S' : Subgroup J) => ((z : J) : G)) hk
    exact ⟨k, by simpa using this⟩
  have hud : (u : G) ∈ Subgroup.zpowers d := by
    have := hcomm x x.2 hx3 hxE e (Subgroup.mem_subgroupOf.mp he)
    simpa [hu] using this
  have hu3 : (u : G) ^ 3 = 1 := by
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hud
    rw [← hj, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hd3, one_zpow]
  have hzz : Subgroup.zpowers (u : G) = Subgroup.zpowers d :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hud) (by
      rw [card_zpowers_of_pow_three hd3 hd1, card_zpowers_of_pow_three hu3 hu1])
  have hdu : d ∈ Subgroup.zpowers (u : G) := hzz ▸ Subgroup.mem_zpowers d
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hdu
  have hdJ : d ∈ J := hj ▸ J.zpow_mem u.2 j
  have hdu' : (⟨d, hdJ⟩ : J) = u ^ j := by
    apply Subtype.ext
    change d = ((u ^ j : J) : G)
    rw [Subgroup.coe_zpow, hj]
  refine ⟨hdJ, P, ?_, ?_⟩
  · rw [hdu', map_zpow]
    exact zpow_mem hπu j
  · intro h
    apply hd1
    have hdS : (⟨d, hdJ⟩ : J) ∈ S' := by
      rw [hdu']
      exact zpow_mem huS j
    have h1 : π (⟨d, hdJ⟩ : J) = π 1 := by rw [h, map_one]
    have := hinj hdS (one_mem _) h1
    exact congrArg Subtype.val this

theorem exists_mem_conj_eq_inv_of_mk {J : Subgroup G} {d : G} (hdJ : d ∈ J) (hd3 : d ^ 3 = 1)
    {gb : J ⧸ aschbacherSolvableCore 3 J}
    (hgb : gb * QuotientGroup.mk' (aschbacherSolvableCore 3 J) (⟨d, hdJ⟩ : J) * gb⁻¹ =
      (QuotientGroup.mk' (aschbacherSolvableCore 3 J) (⟨d, hdJ⟩ : J))⁻¹) :
    ∃ t ∈ J, t * d * t⁻¹ = d⁻¹ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 J) with hπ
  set d' : J := ⟨d, hdJ⟩ with hd'
  have hD3 : IsPGroup 3 (Subgroup.zpowers d') :=
    isPGroup_zpowers_of_pow (k := 1) (by rw [pow_one]; exact Subtype.ext (by simpa using hd3))
  have hgbN : gb ∈ Subgroup.normalizer (((Subgroup.zpowers d').map π :
      Subgroup (J ⧸ aschbacherSolvableCore 3 J)) : Set (J ⧸ aschbacherSolvableCore 3 J)) := by
    refine Subgroup.mem_normalizer_fintype fun y hy => ?_
    rw [SetLike.mem_coe, MonoidHom.map_zpowers] at hy ⊢
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    rw [← conj_zpow, hgb]
    exact Subgroup.zpow_mem _ (inv_mem (Subgroup.mem_zpowers _)) k
  rw [normalizer_map_mk_eq hD3] at hgbN
  obtain ⟨t, htN, rfl⟩ := hgbN
  have htd : t * d' * t⁻¹ ∈ Subgroup.zpowers d' :=
    (Subgroup.mem_normalizer_iff.mp htN d').mp (Subgroup.mem_zpowers d')
  have hinj := injOn_mk_of_isPGroup Nat.prime_three hD3
  have heq : t * d' * t⁻¹ = d'⁻¹ := hinj htd (inv_mem (Subgroup.mem_zpowers d'))
    (by rw [map_inv, map_mul, map_mul, map_inv]; exact hgb)
  exact ⟨t, t.2, congrArg Subtype.val heq⟩

end Central

section Sporadic

variable {G : Type} [Group G] [Finite G] {A L K : Subgroup G} {c d : G}

theorem false_of_sporadic
    (h414 : Sec4.Item4_14_local) (H : Base A c L d K) {S T : Subgroup G}
    (hSD : SylowData A L d K S) (hTD : TData A c L d S T)
    (hW : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers d : Set G))
    {a : G} (hac : a ∉ Subgroup.zpowers c) (had : a ∉ Subgroup.zpowers d) {J : Subgroup G}
    (hJ : Sec13Data G A a J) (haJ : a ∉ J) (h9 : Nat.card (A ⊓ J : Subgroup G) = 9)
    (hMJ : Nonempty (lBarA a J A ≃* Multiplicative (ZMod 3) × CFSG.Blueprint.NativeSporadic.M12) ∨
      Nonempty (lBarA a J A ≃* Multiplicative (ZMod 3) × CFSG.Blueprint.NativeSporadic.J2))
    (hS3 : Nonempty (Sec4.autIn J A ≃* Equiv.Perm (Fin 3))) : False := by
  have haA := hJ.mem_A
  have hJa : J ≤ Subgroup.centralizer ({a} : Set G) := hJ.le_centralizer
  have hd3 := H.d_pow
  have haB : a ∈ Subgroup.zpowers c ⊔ Subgroup.zpowers d := by
    obtain ⟨e⟩ := hS3
    set σ := e.symm (finRotate 3) with hσ
    have hσ3 : σ ^ 3 = 1 := by
      rw [hσ, ← map_pow, show (finRotate 3) ^ 3 = 1 by decide, map_one]
    have hσ1 : σ ≠ 1 := by
      intro h
      have := congrArg e h
      rw [hσ, MulEquiv.apply_symm_apply, map_one] at this
      exact absurd this (by decide)
    exact mem_B_of_autIn H hW haA hJa σ.2
      (by rw [← Subgroup.coe_pow, hσ3, Subgroup.coe_one])
      (fun h => hσ1 (Subtype.ext h))
  have ha3 : a ^ 3 = 1 := hJ.isElemAbelian.2 a haA
  have hAeq : A = Subgroup.zpowers a ⊔ (A ⊓ J) := by
    have hle : Subgroup.zpowers a ⊔ (A ⊓ J) ≤ A :=
      sup_le (Subgroup.zpowers_le.mpr haA) inf_le_left
    have hcard := (isElemAbelian_zpowers_sup_of_card_nine ha3
      (fun h => haJ (Subgroup.mem_inf.mp h).2) le_rfl h9
      (fun b hb => hJ.isElemAbelian.2 b hb.1) (fun b hb => hJ.commute haA hb.1)).2
    exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hJ.card_eq, hcard])).symm
  have hcomm : ∀ x ∈ J, (∃ k : ℕ, x ^ 3 ^ k = 1) →
      x ∈ Subgroup.normalizer ((A ⊓ J : Subgroup G) : Set G) →
      ∀ e ∈ A ⊓ J, x * e * x⁻¹ * e⁻¹ ∈ Subgroup.zpowers d := by
    intro x hxJ ⟨k, hk⟩ hxE e he
    have hxa : x * a = a * x := Subgroup.mem_centralizer_singleton_iff.mp (hJa hxJ)
    have hxA : x ∈ Subgroup.normalizer (A : Set G) := by
      have hle : Subgroup.zpowers a ⊔ (A ⊓ J) ≤
          (Subgroup.zpowers a ⊔ (A ⊓ J)).comap (MulAut.conj x).toMonoidHom := by
        refine sup_le (Subgroup.zpowers_le.mpr ?_) fun y hy => ?_
        · change x * a * x⁻¹ ∈ Subgroup.zpowers a ⊔ (A ⊓ J)
          rw [hxa, mul_inv_cancel_right]
          exact Subgroup.mem_sup_left (Subgroup.mem_zpowers a)
        · exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp hxE y).mp hy)
      refine Subgroup.mem_normalizer_fintype fun y hy => ?_
      rw [hAeq] at hy ⊢
      exact hle hy
    exact conj_mem_zpowers_of_pow hTD ⟨hxA, hW hxA⟩ hk he.1
  have hJ' : (∀ P : Sylow 3 (J ⧸ aschbacherSolvableCore 3 J),
        Sec4.IsHeisThree (P : Subgroup (J ⧸ aschbacherSolvableCore 3 J))) ∧
      ∀ P : Sylow 3 (J ⧸ aschbacherSolvableCore 3 J),
        ∀ z ∈ (P : Subgroup (J ⧸ aschbacherSolvableCore 3 J)) ⊓
          Subgroup.centralizer ((P : Subgroup (J ⧸ aschbacherSolvableCore 3 J)) :
            Set (J ⧸ aschbacherSolvableCore 3 J)), z ≠ 1 →
        ∃ g : J ⧸ aschbacherSolvableCore 3 J, g * z * g⁻¹ = z⁻¹ := by
    obtain ⟨-, ⟨hM12p, -⟩, ⟨hJ2p, -⟩⟩ := H.hspor
    rcases hMJ with hM | hJ2
    · obtain ⟨φ⟩ := hM
      have hX := nonempty_thetaQuot_equiv hJ hM12p φ
      refine ⟨fun P => (h414 _ hX P).1, fun P z hz _ => ?_⟩
      obtain ⟨-, -, -, -, -, t, -, htinv, -⟩ := h414 _ hX P
      exact ⟨t, htinv z hz⟩
    · obtain ⟨φ⟩ := hJ2
      have hX := nonempty_thetaQuot_equiv hJ hJ2p φ
      refine ⟨fun P => (H.h415 _ hX P _ rfl _ rfl).1.1, fun P z hz hz1 => ?_⟩
      exact j2_exists_conj_eq_inv H.h415 hX P hz1 hz
  obtain ⟨hHeis, hinv⟩ := hJ'
  obtain ⟨hdJ, P, hdP, hd1'⟩ := exists_mem_inf_centralizer hHeis inf_le_right h9 H.ne_one hd3
    (fun x hxJ hk hxE e he => hcomm x hxJ hk hxE e he)
  obtain ⟨gb, hgb⟩ := hinv P _ hdP hd1'
  obtain ⟨s, hsJ, hsd⟩ := exists_mem_conj_eq_inv_of_mk hdJ hd3 hgb
  exact false_of_inverts H hSD hTD haA haB hac had
    (Subgroup.mem_centralizer_singleton_iff.mp (hJa hsJ)) hsd

end Sporadic

end CFSG.RankThree.PartTwo.Sec13.Item134Arg128Fail
