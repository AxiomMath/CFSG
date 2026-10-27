module

public import CFSG.RankThree.PartTwo.Sec10.Item1012Res3ProofGL
import CFSG.RankThree.PartTwo.KFacts.K71Residual
import CFSG.RankThree.PartTwo.KFacts.K72SLPiCField
public import CFSG.RankThree.PartTwo.Sec10.Step1012ClaimProofTools

public section

namespace CFSG.RankThree.PartTwo.Sec10

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.GroupTheory
open CFSG.ABGLocalTools (IsSylowOf)

namespace Item1012Res3Proof

variable {G : Type} [Group G] [Finite G]

theorem exists_conj_eq_of_isSylowOf {T S₁ S₂ : Subgroup G} {d : G} (hd3 : d ^ 3 = 1)
    (hdT : d ∈ Subgroup.normalizer (T : Set G)) (hT3 : ¬ 3 ∣ Nat.card T)
    (h₁ : IsSylowOf 2 S₁ T) (h₂ : IsSylowOf 2 S₂ T)
    (hd₁ : d ∈ Subgroup.normalizer (S₁ : Set G)) (hd₂ : d ∈ Subgroup.normalizer (S₂ : Set G)) :
    ∃ t ∈ T, t * d = d * t ∧ S₁.map (MulAut.conj t).toMonoidHom = S₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set D := Subgroup.zpowers d with hD
  have hDT : D ≤ Subgroup.normalizer (T : Set G) := Subgroup.zpowers_le.mpr hdT
  have hD3 : IsPGroup 3 D := fun g => by
    obtain ⟨g, hg⟩ := g
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    refine ⟨1, Subtype.ext ?_⟩
    simp only [pow_one, SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hd3, one_zpow]
  set ρ : D →* MulAut T := T.normalizerMonoidHom.comp (Subgroup.inclusion hDT) with hρ
  have hρapp : ∀ (g : D) (x : T), ((ρ g x : T) : G) = (g : G) * x * (g : G)⁻¹ := fun g x =>
    Sec4.normalizerMonoidHom_apply_coe (hDT g.2) x
  obtain ⟨Q₁, hQ₁⟩ := h₁
  obtain ⟨Q₂, hQ₂⟩ := h₂
  have hinv : ∀ (Q : Sylow 2 T) {S' : Subgroup G}, (Q : Subgroup T).map T.subtype = S' →
      d ∈ Subgroup.normalizer (S' : Set G) →
      ∀ g : D, (Q : Subgroup T).map (ρ g).toMonoidHom = Q := by
    intro Q S' hQ hdS' g
    apply Subgroup.map_injective T.subtype_injective
    have hgS : (g : G) ∈ Subgroup.normalizer (S' : Set G) :=
      (Subgroup.zpowers_le.mpr hdS') g.2
    have hcomp : T.subtype.comp (ρ g).toMonoidHom =
        (MulAut.conj (g : G)).toMonoidHom.comp T.subtype := by
      ext x
      exact hρapp g x
    rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, hQ]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp hgS
  obtain ⟨t, ht, hfix⟩ := CFSG.OrderReductions.FixedConjugator.invariant_sylows_conjugate_of_coprime
    3 2 hD3 hT3 ρ Q₁ Q₂ (hinv Q₁ hQ₁ hd₁) (hinv Q₂ hQ₂ hd₂)
  refine ⟨t, t.2, ?_, ?_⟩
  · have h1 := congrArg Subtype.val (hfix ⟨d, Subgroup.mem_zpowers d⟩)
    rw [hρapp] at h1
    calc (t : G) * d = d * t * d⁻¹ * d := by rw [h1]
      _ = d * t := by group
  · rw [← hQ₁, ← hQ₂, ← ht, Subgroup.map_map, Subgroup.map_map]
    congr 1

theorem exists_eq_mul_of_isSylowOf {H T S : Subgroup G} {d : G} (hd3 : d ^ 3 = 1)
    (hHT : H ≤ Subgroup.normalizer (T : Set G)) (hTs : Group.IsSolvable T)
    (hT3 : ¬ 3 ∣ Nat.card T) (hS : IsSylowOf 2 S T)
    (hdT : d ∈ Subgroup.normalizer (T : Set G)) (hdS : d ∈ Subgroup.normalizer (S : Set G))
    (hHd : ∀ h ∈ H, h * d = d * h) (hTH : ∀ t ∈ T, t * d = d * t → t ∈ H) {h : G}
    (hh : h ∈ H) :
    ∃ t ∈ inSubgroup (aschbacherSolvableCore 3) H,
      ∃ n ∈ H ⊓ Subgroup.normalizer (S : Set G), h = t * n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set S' := S.map (MulAut.conj h).toMonoidHom with hS'def
  have hS'T : S' ≤ T := by
    rintro _ ⟨s, hs, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp (hHT hh) s).mp (hS.le hs)
  have hS' : IsSylowOf 2 S' T := CFSG.ABGLocalTools.isSylowOf_of_card hS'T (by
    rw [hS'def, Subgroup.card_map_of_injective (MulAut.conj h).injective]
    exact hS.card_eq)
  have hmemS' : ∀ x : G, x ∈ S' ↔ h⁻¹ * x * h ∈ S := fun x => by
    rw [hS'def, Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
  have hdS' : d ∈ Subgroup.normalizer (S' : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [hmemS', hmemS']
    have hdh := hHd h hh
    have heq : h⁻¹ * (d * x * d⁻¹) * h = d * (h⁻¹ * x * h) * d⁻¹ := by
      have hdh' : h⁻¹ * d = d * h⁻¹ := by
        calc h⁻¹ * d = h⁻¹ * (d * h) * h⁻¹ := by group
          _ = h⁻¹ * (h * d) * h⁻¹ := by rw [hdh]
          _ = d * h⁻¹ := by group
      calc h⁻¹ * (d * x * d⁻¹) * h = (h⁻¹ * d) * x * (d⁻¹ * h) := by group
        _ = (d * h⁻¹) * x * (d⁻¹ * h) := by rw [hdh']
        _ = (d * h⁻¹) * x * (h * d⁻¹) := by
          congr 1
          calc d⁻¹ * h = d⁻¹ * (h * d) * d⁻¹ := by group
            _ = d⁻¹ * (d * h) * d⁻¹ := by rw [hdh]
            _ = h * d⁻¹ := by group
        _ = d * (h⁻¹ * x * h) * d⁻¹ := by group
    rw [heq]
    exact Subgroup.mem_normalizer_iff.mp hdS _
  obtain ⟨t, htT, htd, hSt⟩ := exists_conj_eq_of_isSylowOf hd3 hdT hT3 hS hS' hdS hdS'
  have htH : t ∈ H := hTH t htT htd
  have hTHθ : T ⊓ H ≤ inSubgroup (aschbacherSolvableCore 3) H := by
    refine Sec6.le_theta_of_normal inf_le_right (fun x hx => ?_) ?_ ?_
    · exact SteinbergBY.mem_normalizer_inf (hHT hx) (Subgroup.le_normalizer hx)
    · exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective inf_le_left)
    · exact fun h3 => hT3 (h3.trans (Subgroup.card_dvd_of_le inf_le_left))
  have hnS : t⁻¹ * h ∈ Subgroup.normalizer (S : Set G) := by
    have hmemSt : ∀ y : G, y ∈ S' ↔ t⁻¹ * y * t ∈ S := fun y => by
      rw [← hSt, Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have heq : t⁻¹ * h * x * (t⁻¹ * h)⁻¹ = t⁻¹ * (h * x * h⁻¹) * t := by group
    rw [heq, ← hmemSt, hmemS', show h⁻¹ * (h * x * h⁻¹) * h = x by group]
  exact ⟨t, hTHθ ⟨htT, htH⟩, t⁻¹ * h, ⟨H.mul_mem (H.inv_mem htH) hh, hnS⟩, by group⟩

theorem inf_centralizer_le_theta {H S J : Subgroup G}
    (hfrat : ∀ h ∈ H, ∃ t ∈ inSubgroup (aschbacherSolvableCore 3) H,
      ∃ n ∈ H ⊓ Subgroup.normalizer (S : Set G), h = t * n)
    (hJH : J ≤ H) (hJnorm : H ⊓ Subgroup.normalizer (S : Set G) ≤ Subgroup.normalizer (J : Set G))
    (hs : Group.IsSolvable (J ⊓ Subgroup.centralizer (S : Set G) : Subgroup G))
    (h3 : ¬ 3 ∣ Nat.card (J ⊓ Subgroup.centralizer (S : Set G) : Subgroup G)) :
    J ⊓ Subgroup.centralizer (S : Set G) ≤ inSubgroup (aschbacherSolvableCore 3) H := by
  set Θ := inSubgroup (aschbacherSolvableCore 3) H with hΘ
  set X := J ⊓ Subgroup.centralizer (S : Set G) with hX
  obtain ⟨hΘs, hΘ3⟩ := Sec6.theta_solvable_and_not_dvd H
  have hΘH : Θ ≤ H := Sec6.theta_le H
  have hHΘ : H ≤ Subgroup.normalizer (Θ : Set G) := Sec6.le_normalizer_theta H
  have hXH : X ≤ H := inf_le_left.trans hJH
  have hXΘ : X ≤ Subgroup.normalizer (Θ : Set G) := hXH.trans hHΘ
  set Y := Θ ⊔ X with hY
  have hYH : Y ≤ H := sup_le hΘH hXH
  have hHY : H ≤ Subgroup.normalizer (Y : Set G) := by
    intro h hh
    obtain ⟨t, ht, n, ⟨hnH, hnS⟩, rfl⟩ := hfrat h hh
    have hnX : n ∈ Subgroup.normalizer (X : Set G) :=
      SteinbergBY.mem_normalizer_inf (hJnorm ⟨hnH, hnS⟩)
        (Sec10XSteps.normalizer_le_normalizer_centralizer_of hnS)
    refine Subgroup.mul_mem _ (Subgroup.le_normalizer ((le_sup_left : Θ ≤ Y) ht)) ?_
    exact Sec10XSteps.mem_normalizer_sup_of_mem (hHΘ hnH) hnX
  have hYs : Group.IsSolvable Y := isSolvable_sup_of_le_normalizer hXΘ hΘs hs
  have hY3 : ¬ 3 ∣ Nat.card Y :=
    Step1012ClaimProof.not_dvd_card_sup_of_le_normalizer Nat.prime_three hXΘ hΘ3 h3
  exact le_sup_right.trans (Sec6.le_theta_of_normal hYH hHY hYs hY3)

theorem isSLThreePiAt_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) {q : ℕ}
    (hX : Sec4.IsSLThreePiAt X q) : Sec4.IsSLThreePiAt Y q := by
  obtain ⟨K, hK, hKf, h1 | h1⟩ := hX
  · obtain ⟨hq, hq3, ⟨f⟩⟩ := h1
    exact ⟨K, hK, hKf, Or.inl ⟨hq, hq3, ⟨e.symm.trans f⟩⟩⟩
  · obtain ⟨hq, hq3, ⟨f⟩⟩ := h1
    exact ⟨K, hK, hKf, Or.inr ⟨hq, hq3, ⟨e.symm.trans f⟩⟩⟩

theorem type_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (hX : Sec4.IsSLThreePiAt X 4 ∨ Sec4.IsTripleCover X (alternatingGroup (Fin 6))) :
    Sec4.IsSLThreePiAt Y 4 ∨ Sec4.IsTripleCover Y (alternatingGroup (Fin 6)) := by
  rcases hX with h4 | h6
  · exact Or.inl (isSLThreePiAt_of_mulEquiv e h4)
  · exact Or.inr (KFacts.KS14.isTripleCover_congr e h6)

theorem isQuasisimple_and_center_of_type {P : Type} [Group P] [Finite P]
    (hperf : Group.IsPerfect P)
    (htype : Sec4.IsSLThreePiAt P 4 ∨ Sec4.IsTripleCover P (alternatingGroup (Fin 6))) :
    IsQuasisimple P ∧ ∀ z ∈ Subgroup.center P, z ^ 3 = 1 := by
  have hcen : Nat.card (Subgroup.center P) = 3 → ∀ z ∈ Subgroup.center P, z ^ 3 = 1 := by
    intro h3 z hz
    have h := pow_card_eq_one' (G := Subgroup.center P) (x := ⟨z, hz⟩)
    rw [h3] at h
    exact congrArg Subtype.val h
  rcases htype with h4 | h6
  · have h4' : Sec4.IsSLThreePiAt P (2 ^ 2) := h4
    exact ⟨KFacts.isQuasisimple_of_isSLThreePiAt_two_pow le_rfl h4',
      hcen (KFacts.card_center_of_isSLThreePiAt_two_pow (by norm_num) h4')⟩
  · obtain ⟨h3, ⟨e⟩⟩ := h6
    have : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
    refine ⟨⟨hperf, e.isSimpleGroup, ?_⟩, hcen h3⟩
    have hsign : ∀ i j : Fin 6, i ≠ 0 → j ≠ 0 →
        Equiv.swap (0 : Fin 6) i * Equiv.swap 0 j ∈ alternatingGroup (Fin 6) := by
      intro i j hi hj
      rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hi.symm,
        Equiv.Perm.sign_swap hj.symm]
      rfl
    let σ : alternatingGroup (Fin 6) := ⟨Equiv.swap 0 1 * Equiv.swap 0 2, hsign 1 2 (by decide)
      (by decide)⟩
    let τ : alternatingGroup (Fin 6) := ⟨Equiv.swap 0 1 * Equiv.swap 0 3, hsign 1 3 (by decide)
      (by decide)⟩
    have hnc : Equiv.swap (0 : Fin 6) 1 * Equiv.swap 0 2 * (Equiv.swap 0 1 * Equiv.swap 0 3) ≠
        Equiv.swap 0 1 * Equiv.swap 0 3 * (Equiv.swap 0 1 * Equiv.swap 0 2) := by decide
    refine ⟨e.symm σ, e.symm τ, fun h => ?_⟩
    have h' := congrArg e h
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at h'
    exact hnc (congrArg Subtype.val h')

omit [Finite G] in
theorem inf_le_centralizer_of_quasisimple {J S Θ : Subgroup G}
    (hJS : J ≤ Subgroup.normalizer (S : Set G)) (hJΘ : J ≤ Subgroup.normalizer (Θ : Set G))
    (hΘs : Group.IsSolvable Θ) (hΘ3 : ¬ 3 ∣ Nat.card Θ) {P : Subgroup (MulAut S)}
    (hJP : Sec4.autIn J S = P) (hPq : IsQuasisimple P)
    (hPZ : ∀ z ∈ Subgroup.center P, z ^ 3 = 1) :
    J ⊓ Θ ≤ Subgroup.centralizer (S : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set ξ₀ : J →* MulAut S := S.normalizerMonoidHom.comp (Subgroup.inclusion hJS) with hξ₀
  have hξ₀P : ∀ j : J, ξ₀ j ∈ P := fun j => by
    rw [← hJP]
    exact Sec4.mem_autIn_iff.mpr ⟨j, hJS j.2, j.2, rfl⟩
  set ξ : J →* P := ξ₀.codRestrict P hξ₀P with hξ
  have hξs : Function.Surjective ξ := by
    rintro ⟨σ, hσ⟩
    rw [← hJP] at hσ
    obtain ⟨j, hjN, hjJ, rfl⟩ := Sec4.mem_autIn_iff.mp hσ
    exact ⟨⟨j, hjJ⟩, rfl⟩
  have hξker : ∀ j : J, ξ j = 1 → (j : G) ∈ Subgroup.centralizer (S : Set G) := by
    intro j hj
    have h1 : S.normalizerMonoidHom ⟨(j : G), hJS j.2⟩ = 1 := congrArg Subtype.val hj
    have h2 := (MonoidHom.mem_ker).mpr h1
    rw [Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf] at h2
    exact h2
  set M : Subgroup J := Θ.subgroupOf J with hM
  have hMn : M.Normal := ⟨fun m hm g => by
    rw [hM, Subgroup.mem_subgroupOf] at hm ⊢
    simpa using (Subgroup.mem_normalizer_iff.mp (hJΘ g.2) m).mp hm⟩
  set ι : M →* Θ := { toFun := fun m => ⟨((m : J) : G), m.2⟩
                      map_one' := rfl
                      map_mul' := fun _ _ => rfl } with hι
  have hι : Function.Injective ι := fun m m' h => by
    have h' : ((ι m : Θ) : G) = ((ι m' : Θ) : G) := congrArg Subtype.val h
    exact Subtype.ext (Subtype.ext h')
  have hMs : Group.IsSolvable M := Group.isSolvable_of_isSolvable_injective hι
  have hM3 : Nat.Coprime 3 (Nat.card M) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr fun h3 =>
      hΘ3 (h3.trans (Subgroup.card_dvd_of_injective ι hι))
  have hMP : (M.map ξ).Normal := Subgroup.Normal.map hMn ξ hξs
  have hMPs : Group.IsSolvable (M.map ξ) :=
    Group.isSolvable_of_surjective (ξ.subgroupMap_surjective M)
  rcases CFSG.LieType.CurtisTits.le_center_or_eq_top_of_isQuasisimple hPq (M.map ξ) with hc | ht
  · rintro x ⟨hxJ, hxΘ⟩
    have hm : (⟨x, hxJ⟩ : J) ∈ M := hxΘ
    apply hξker ⟨x, hxJ⟩
    have h1 : ξ ⟨x, hxJ⟩ ∈ Subgroup.center P := hc ⟨_, hm, rfl⟩
    have h2 : orderOf (ξ ⟨x, hxJ⟩) ∣ 3 := orderOf_dvd_of_pow_eq_one (hPZ _ h1)
    have h3 : orderOf (ξ ⟨x, hxJ⟩) ∣ Nat.card M := by
      refine (orderOf_map_dvd ξ _).trans ?_
      rw [← Subgroup.orderOf_mk (⟨x, hxJ⟩ : J) hm]
      exact orderOf_dvd_natCard _
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hM3 h2 h3)
  · exfalso
    have hPs : Group.IsSolvable P := by
      have e : (M.map ξ : Subgroup P) ≃* P :=
        (MulEquiv.subgroupCongr ht).trans Subgroup.topEquiv
      exact Group.isSolvable_of_isSolvable_injective (f := e.symm.toMonoidHom) e.symm.injective
    obtain ⟨-, hsimple, a', b', hab⟩ := hPq
    have : Group.IsSolvable (P ⧸ Subgroup.center P) := inferInstance
    exact hab ((IsSimpleGroup.comm_iff_isSolvable).mpr this a' b')

theorem autIn_le_perfectResidual {H S J : Subgroup G} (hJH : J ≤ H)
    (hJS : J ≤ Subgroup.normalizer (S : Set G)) (hJperf : Group.IsPerfect J) :
    Sec4.autIn J S ≤ inSubgroup perfectResidual (Sec4.autIn H S) := by
  set ξ₀ : J →* MulAut S := S.normalizerMonoidHom.comp (Subgroup.inclusion hJS) with hξ₀
  have hrange : ξ₀.range = Sec4.autIn J S := by
    ext σ
    rw [MonoidHom.mem_range, Sec4.mem_autIn_iff]
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨j, hJS j.2, j.2, rfl⟩
    · rintro ⟨g, hgN, hgJ, rfl⟩
      exact ⟨⟨g, hgJ⟩, rfl⟩
  have hAJperf : Group.IsPerfect (Sec4.autIn J S) := by
    rw [← hrange]
    exact Group.IsPerfect.ofSurjective (f := ξ₀.rangeRestrict) ξ₀.rangeRestrict_surjective
  have hAJH : Sec4.autIn J S ≤ Sec4.autIn H S := by
    intro σ hσ
    obtain ⟨g, hgN, hgJ, rfl⟩ := Sec4.mem_autIn_iff.mp hσ
    exact Sec4.mem_autIn_iff.mpr ⟨g, hgN, hJH hgJ, rfl⟩
  exact KFacts.le_inSubgroup_perfectResidual hAJperf hAJH

theorem exists_mem_thetaComponentsIn_of_cover {H S J : Subgroup G}
    (hfrat : ∀ h ∈ H, ∃ t ∈ inSubgroup (aschbacherSolvableCore 3) H,
      ∃ n ∈ H ⊓ Subgroup.normalizer (S : Set G), h = t * n)
    (hJH : J ≤ H) (hJS : J ≤ Subgroup.normalizer (S : Set G)) (hJperf : Group.IsPerfect J)
    (hJnorm : H ⊓ Subgroup.normalizer (S : Set G) ≤ Subgroup.normalizer (J : Set G))
    (hcov : inSubgroup perfectResidual (Sec4.autIn H S) ≤ Sec4.autIn J S)
    (hker : J ⊓ Subgroup.centralizer (S : Set G) ≤ inSubgroup (aschbacherSolvableCore 3) H)
    (htype : Sec4.IsSLThreePiAt (inSubgroup perfectResidual (Sec4.autIn H S)) 4 ∨
      Sec4.IsTripleCover (inSubgroup perfectResidual (Sec4.autIn H S))
        (alternatingGroup (Fin 6))) :
    ∃ K ∈ thetaComponentsIn H,
      (Sec4.IsSLThreePiAt (K ⧸ aschbacherSolvableCore 3 K) 4 ∨
        Sec4.IsTripleCover (K ⧸ aschbacherSolvableCore 3 K) (alternatingGroup (Fin 6))) ∧
      inSubgroup perfectResidual (Sec4.autIn H S) ≤ Sec4.autIn K S := by
  set Θ := inSubgroup (aschbacherSolvableCore 3) H with hΘ
  set P := inSubgroup perfectResidual (Sec4.autIn H S) with hP
  obtain ⟨hPq, hPZ⟩ := isQuasisimple_and_center_of_type
    (Sec6.isPerfect_inSubgroup_perfectResidual (Sec4.autIn H S)) htype
  set ξ₀ : J →* MulAut S := S.normalizerMonoidHom.comp (Subgroup.inclusion hJS) with hξ₀
  have hJP : Sec4.autIn J S = P := le_antisymm (autIn_le_perfectResidual hJH hJS hJperf) hcov
  obtain ⟨hΘs, hΘ3⟩ := Sec6.theta_solvable_and_not_dvd H
  have hJΘ : J ≤ Subgroup.normalizer (Θ : Set G) := hJH.trans (Sec6.le_normalizer_theta H)
  have hJΘC := inf_le_centralizer_of_quasisimple hJS hJΘ hΘs hΘ3 hJP hPq hPZ
  have hmemiff : ∀ x ∈ J, x ∈ Θ ↔ x ∈ Subgroup.centralizer (S : Set G) := fun x hx =>
    ⟨fun h => hJΘC ⟨hx, h⟩, fun h => hker ⟨hx, h⟩⟩
  set J' := J.subgroupOf H with hJ'
  set eJ : J' ≃* J := Subgroup.subgroupOfEquivOfLe hJH with heJ
  have hξ₀P : ∀ j : J, ξ₀ j ∈ P := fun j => by
    rw [← hJP]
    exact Sec4.mem_autIn_iff.mpr ⟨j, hJS j.2, j.2, rfl⟩
  set ψ : J' →* P := (ξ₀.codRestrict P hξ₀P).comp eJ.toMonoidHom with hψ
  have hψs : Function.Surjective ψ := by
    rintro ⟨σ, hσ⟩
    have hσ' := hσ
    rw [← hJP] at hσ'
    obtain ⟨j, hjN, hjJ, hj⟩ := Sec4.mem_autIn_iff.mp hσ'
    refine ⟨eJ.symm ⟨j, hjJ⟩, Subtype.ext ?_⟩
    simp only [hψ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply,
      MonoidHom.codRestrict_apply]
    exact hj
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 H) with hπ
  set κ : J' →* H ⧸ aschbacherSolvableCore 3 H := π.comp J'.subtype with hκ
  set Jbar := J'.map π with hJbar
  have hκrange : κ.range = Jbar := by rw [hκ, MonoidHom.range_comp, Subgroup.range_subtype]
  have hkereq : κ.ker = ψ.ker := by
    ext j
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    have hjJ : (((j : H) : G)) ∈ J := Subgroup.mem_subgroupOf.mp j.2
    have hκ1 : κ j = 1 ↔ ((j : H) : G) ∈ Θ := by
      rw [hκ, MonoidHom.comp_apply, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
        hΘ, inSubgroup, Subgroup.coe_subtype, ← Subgroup.mem_map_iff_mem H.subtype_injective]
      rfl
    have hψ1 : ψ j = 1 ↔ ((j : H) : G) ∈ Subgroup.centralizer (S : Set G) := by
      constructor
      · intro h1
        have h2 : S.normalizerMonoidHom ⟨((j : H) : G), hJS hjJ⟩ = 1 := congrArg Subtype.val h1
        have h3 := (MonoidHom.mem_ker).mpr h2
        rw [Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf] at h3
        exact h3
      · intro h1
        apply Subtype.ext
        change S.normalizerMonoidHom ⟨((j : H) : G), hJS hjJ⟩ = 1
        rw [← MonoidHom.mem_ker, Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf]
        exact h1
    rw [hκ1, hψ1]
    exact hmemiff _ hjJ
  set eJbar : Jbar ≃* P := (MulEquiv.subgroupCongr hκrange).symm.trans
    ((QuotientGroup.quotientKerEquivRange κ).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hkereq).trans
        (QuotientGroup.quotientKerEquivOfSurjective ψ hψs))) with heJbar
  have hJbarN : Jbar.Normal := by
    constructor
    rintro _ ⟨j, hj, rfl⟩ q
    obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective (aschbacherSolvableCore 3 H) q
    obtain ⟨t, ⟨t', ht', htt'⟩, n, ⟨hnH, hnS⟩, hhtn⟩ := hfrat (h : G) h.2
    have hh : h = t' * ⟨n, hnH⟩ := Subtype.ext (by rw [hhtn, Subgroup.coe_mul, ← htt']; rfl)
    have hπt : π t' = 1 := by
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact ht'
    have hnJ : ((⟨n, hnH⟩ : H) * j * (⟨n, hnH⟩ : H)⁻¹ : H) ∈ J' := by
      rw [hJ', Subgroup.mem_subgroupOf]
      exact (Subgroup.mem_normalizer_iff.mp (hJnorm ⟨hnH, hnS⟩) _).mp
        (Subgroup.mem_subgroupOf.mp hj)
    refine ⟨_, hnJ, ?_⟩
    have hπt' : QuotientGroup.mk' (aschbacherSolvableCore 3 H) t' = 1 := hπt
    rw [hh]
    simp only [hπ, map_mul, map_inv, hπt', one_mul]
  have hJbarC : IsComponent Jbar :=
    ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv eJbar.symm hPq, hJbarN.isSubnormal⟩
  obtain ⟨hK', hK'map⟩ := perfectResidual_comap_mem_thetaComponents Nat.prime_three hJbarC
  set K' := inSubgroup perfectResidual (Jbar.comap π) with hK'def
  refine ⟨K'.map H.subtype, ⟨K', hK', rfl⟩, ?_, ?_⟩
  ·
    set eK : K' ≃* K'.map H.subtype := K'.equivMapOfInjective H.subtype H.subtype_injective
    obtain ⟨η, -⟩ := exists_thetaQuotient_mulEquiv_map Nat.prime_three hK'.2.1
    have e : (K'.map H.subtype) ⧸ aschbacherSolvableCore 3 (K'.map H.subtype) ≃* P :=
      (QuotientGroup.congr _ _ eK
        (aschbacherSolvableCore_map_mulEquiv Nat.prime_three eK)).symm.trans
        (η.trans ((MulEquiv.subgroupCongr hK'map).trans eJbar))
    exact type_of_mulEquiv e.symm htype
  ·
    have hJ'perf : Group.IsPerfect J' :=
      Group.IsPerfect.ofSurjective (f := eJ.symm.toMonoidHom) eJ.symm.surjective
    have hJ'K' : J' ≤ K' :=
      KFacts.le_inSubgroup_perfectResidual hJ'perf (Subgroup.le_comap_map π J')
    have hJK : J ≤ K'.map H.subtype := fun x hx =>
      ⟨⟨x, hJH hx⟩, hJ'K' (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
    rw [← hJP]
    intro σ hσ
    obtain ⟨g, hgN, hgJ, rfl⟩ := Sec4.mem_autIn_iff.mp hσ
    exact Sec4.mem_autIn_iff.mpr ⟨g, hgN, hJK hgJ, rfl⟩

theorem residual_cover (H S : Subgroup G) :
    inSubgroup perfectResidual (H ⊓ Subgroup.normalizer (S : Set G)) ≤
        H ⊓ Subgroup.normalizer (S : Set G) ∧
      Group.IsPerfect (inSubgroup perfectResidual (H ⊓ Subgroup.normalizer (S : Set G))) ∧
      H ⊓ Subgroup.normalizer (S : Set G) ≤ Subgroup.normalizer
        (inSubgroup perfectResidual (H ⊓ Subgroup.normalizer (S : Set G)) : Set G) ∧
      inSubgroup perfectResidual (Sec4.autIn H S) ≤
        Sec4.autIn (inSubgroup perfectResidual (H ⊓ Subgroup.normalizer (S : Set G))) S := by
  set NS := Subgroup.normalizer (S : Set G) with hNS
  set J := inSubgroup perfectResidual (H ⊓ NS) with hJdef
  have hJHN : J ≤ H ⊓ NS := Subgroup.map_subtype_le _
  have hJS : J ≤ NS := hJHN.trans inf_le_right
  refine ⟨hJHN, Sec6.isPerfect_inSubgroup_perfectResidual _, fun n hn =>
    SteinbergBY.normalizer_le_normalizer_inSubgroup_perfectResidual _ (Subgroup.le_normalizer hn),
    ?_⟩
  set f := S.normalizerMonoidHom with hf
  set X := (H ⊓ NS).subgroupOf NS with hX
  have hXmap : X.map NS.subtype = H ⊓ NS := Subgroup.map_subgroupOf_eq_of_le inf_le_right
  have hJsub : J.subgroupOf NS = inSubgroup perfectResidual X := by
    have h1 :=
      SteinbergBY.map_inSubgroup_perfectResidual_of_injective NS.subtype NS.subtype_injective X
    rw [hXmap, ← hJdef] at h1
    rw [← h1, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective NS.subtype_injective]
  have hAJ : Sec4.autIn J S = inSubgroup perfectResidual (Sec4.autIn H S) := by
    have h1 : Sec4.autIn J S = (J.subgroupOf NS).map f := by
      rw [Sec4.autIn, inf_eq_left.mpr hJS]
    rw [h1, hJsub, KFacts.map_inSubgroup_perfectResidual_hom f X]
    rfl
  exact hAJ.ge

end Item1012Res3Proof

@[expose] def Step1012KAutJ : Prop :=
  Sec4.Item4_5 → Sec9.Item97 →
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G)
    (R : Subgroup G), Sec10Std G A c L a R → ∀ d : G, A ⊓ L = Subgroup.zpowers d →
      sec10U L a ≤ inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({a} : Set G)) →
      sec10U L a ∈
        maxInvariantPiSubgroups (Subgroup.normalizer (Subgroup.zpowers c : Set G)) A (piOf 2) →
      ∀ S ∈ maxInvariantPiSubgroups
          (inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({a} : Set G))) A (piOf 2),
        sec10U L a ≤ S → S ⊓ Subgroup.centralizer ({c} : Set G) = sec10U L a →
        S ⊓ Subgroup.centralizer ({d} : Set G) = ⊥ → IsMulCommutative S →
      ∀ w ∈ Subgroup.normalizer (A : Set G), w ∈ Subgroup.normalizer (S : Set G) →
        w * a * w⁻¹ = a → w * d * w⁻¹ = d → w * c * w⁻¹ = c * d →
      ∀ V : Subgroup G, IsPGroup 2 V → A ≤ Subgroup.normalizer (V : Set G) →
        V ≤ Subgroup.normalizer (S : Set G) →
        V ≤ Subgroup.centralizer ((Subgroup.closure {a, d} : Subgroup G) : Set G) →
        V ≤ inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer (sec10U L a : Set G)) →
        ¬ V ≤ Subgroup.centralizer (S : Set G) →
        ¬ V ≤ inSubgroup (aschbacherSolvableCore 3)
          (Subgroup.centralizer ((Subgroup.closure {a, d} : Subgroup G) : Set G)) →
      (Sec4.IsSLThreePiAt (inSubgroup perfectResidual (Sec4.autIn
          (Subgroup.centralizer ((Subgroup.closure {a, d} : Subgroup G) : Set G)) S)) 4 ∨
        Sec4.IsTripleCover (inSubgroup perfectResidual (Sec4.autIn
          (Subgroup.centralizer ((Subgroup.closure {a, d} : Subgroup G) : Set G)) S))
          (alternatingGroup (Fin 6))) →
      (∀ x ∈ Subgroup.centralizer (S : Set G) ⊓
          Subgroup.centralizer ((Subgroup.closure {a, d} : Subgroup G) : Set G),
        x ^ 3 = 1 → x ∈ Subgroup.zpowers a) →
      ∃ J : Subgroup G,
        J ≤ Subgroup.centralizer ((Subgroup.closure {a, d} : Subgroup G) : Set G) ⊓
          Subgroup.normalizer (S : Set G) ∧
        Group.IsPerfect J ∧
        Subgroup.centralizer ((Subgroup.closure {a, d} : Subgroup G) : Set G) ⊓
          Subgroup.normalizer (S : Set G) ≤ Subgroup.normalizer (J : Set G) ∧
        inSubgroup perfectResidual (Sec4.autIn
          (Subgroup.centralizer ((Subgroup.closure {a, d} : Subgroup G) : Set G)) S) ≤
          Sec4.autIn J S ∧
        Group.IsSolvable (J ⊓ Subgroup.centralizer (S : Set G) : Subgroup G) ∧
        ¬ 3 ∣ Nat.card (J ⊓ Subgroup.centralizer (S : Set G) : Subgroup G)

namespace Item1012Res3Proof

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
  {R : Subgroup G}

theorem exists_eq_mul_of_sec10 (h : Sec10Std G A c L a R) {d : G} (hdA : d ∈ A)
    {S : Subgroup G} (hS : S ∈ maxInvariantPiSubgroups
      (inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({a} : Set G))) A (piOf 2))
    {x : G} (hx : x ∈ Subgroup.centralizer ((Subgroup.closure {a, d} : Subgroup G) : Set G)) :
    ∃ t ∈ inSubgroup (aschbacherSolvableCore 3)
        (Subgroup.centralizer ((Subgroup.closure {a, d} : Subgroup G) : Set G)),
      ∃ n ∈ Subgroup.centralizer ((Subgroup.closure {a, d} : Subgroup G) : Set G) ⊓
        Subgroup.normalizer (S : Set G), x = t * n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Ca := Subgroup.centralizer ({a} : Set G) with hCa
  set T := inSubgroup (aschbacherSolvableCore 3) Ca with hT
  obtain ⟨⟨hST, hS2', hSA⟩, hSmax⟩ := mem_maxInvariantPiSubgroups_iff.mp hS
  have hS2 : IsPGroup 2 S := (isPiSubgroup_piOf_iff Nat.prime_two _).mp hS2'
  have hA3 : IsPGroup 3 A := IsPGroup.of_card (n := 3) (by rw [h.card_eq]; norm_num)
  have hAab : IsMulCommutative A := h.mem_partTwoF.1.1
  have hACa : A ≤ Ca := fun y hy =>
    Subgroup.mem_centralizer_singleton_iff.mpr (h.comm hy h.a_mem)
  obtain ⟨S', hS'syl, hS'A, hSS', -⟩ := Step1012ClaimProof.exists_isSylowOf_theta_normalized
    hA3 hAab hACa hS2 hST hSA (X := ⊥) IsPGroup.of_bot bot_le
    (fun y _ => Subgroup.mem_normalizer_iff.mpr fun z => by simp) bot_le
  have hS'eq : S' = S := hSmax S' ⟨hS'syl.le,
    (isPiSubgroup_piOf_iff Nat.prime_two S').mpr hS'syl.isPGroup, hS'A⟩ hSS'
  rw [hS'eq] at hS'syl
  obtain ⟨hTs, hT3⟩ := Sec6.theta_solvable_and_not_dvd Ca
  have hCaT : Ca ≤ Subgroup.normalizer (T : Set G) := Sec6.le_normalizer_theta Ca
  have hmemH : ∀ y : G, y ∈ Subgroup.centralizer ((Subgroup.closure {a, d} : Subgroup G) :
      Set G) ↔ y * a = a * y ∧ y * d = d * y := fun y =>
    Step1012ClaimProof.mem_centralizer_closure_pair_iff
  refine exists_eq_mul_of_isSylowOf (h.pow_three hdA) (fun y hy => hCaT ?_) hTs hT3 hS'syl
    (hCaT (hACa hdA)) (hSA hdA) (fun y hy => ((hmemH y).mp hy).2) (fun t ht htd => ?_) hx
  · exact Subgroup.mem_centralizer_singleton_iff.mpr ((hmemH y).mp hy).1
  · exact (hmemH t).mpr ⟨Subgroup.mem_centralizer_singleton_iff.mp (Sec6.theta_le Ca ht), htd⟩

end Item1012Res3Proof

open Item1012Res3Proof in
theorem step1012KAutCover_of_autJ (hJ : Step1012KAutJ) : Step1012KAutCover := by
  intro h45 h97 G _ _ A c L a R h d hdL hUθ hUmax S hS hUS hSc hSd hSab w hwA hwS hwa hwd hwc V
    hV2 hVA hVS hVB hVθU hVS' hVθ hauto hm3
  obtain ⟨J, hJN, hJperf, hJnorm, hJcov, hJs, hJ3⟩ := hJ h45 h97 G A c L a R h d hdL hUθ hUmax S
    hS hUS hSc hSd hSab w hwA hwS hwa hwd hwc V hV2 hVA hVS hVB hVθU hVS' hVθ hauto hm3
  have hfrat := fun x hx => exists_eq_mul_of_sec10 h (h.d_mem_A hdL) hS (x := x) hx
  exact exists_mem_thetaComponentsIn_of_cover hfrat (hJN.trans inf_le_left)
    (hJN.trans inf_le_right) hJperf hJnorm hJcov
    (inf_centralizer_le_theta hfrat (hJN.trans inf_le_left) hJnorm hJs hJ3) hauto

theorem step1012ClaimKd_of_autJ (hJ : Step1012KAutJ) : Step1012ClaimKd :=
  step1012ClaimKd_of_autCover Item1012Res3Proof.ks1012GL34Inf_holds (step1012KAutCover_of_autJ hJ)

end CFSG.RankThree.PartTwo.Sec10
