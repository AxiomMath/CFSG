module

public import CFSG.RankThree.PartTwo.Sec13.Item134
public import CFSG.RankThree.PartTwo.Sec13.Item13Inputs
import CFSG.RankThree.PartTwo.Sec13.Item134Residual
import CFSG.RankThree.PartTwo.Sec13.Item137Tools
import CFSG.RankThree.PartTwo.Sec13.Item136Lift
import CFSG.RankThree.PartTwo.Sec13.Item136Pair
import CFSG.RankThree.PartTwo.Sec13.Item136PGL
import CFSG.RankThree.PartTwo.Sec13.Item13SLTwo
import CFSG.RankThree.PartTwo.Sec12.Item124Bar
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
import CFSG.RankThree.PartOne.S10.EmbeddingFixedResidual
import CFSG.CharacterTheory.Semidihedral.Local.CoprimeCentralizerQuotient
import CFSG.GroupTheory.PerfectResidualNodes

public section

namespace CFSG.RankThree.PartTwo.Sec13

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

section General

variable {Λ : Type*} [Group Λ] [Finite Λ]

omit [Finite Λ] in
theorem mem_of_pow_three_of_map_eq {Q : Type*} [Group Q] (f : Λ →* Q) (N : Subgroup Λ)
    [N.Normal] (hN : N.map f = f.range) (hk : ¬ 3 ∣ Nat.card f.ker) {x : Λ} {k : ℕ}
    (hx : x ^ 3 ^ k = 1) : x ∈ N := by
  have hfx : f x ∈ N.map f := hN ▸ ⟨x, rfl⟩
  obtain ⟨n, hn, hnx⟩ := hfx
  have hu : n⁻¹ * x ∈ f.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hnx, inv_mul_cancel]
  have hmk : (QuotientGroup.mk x : Λ ⧸ N) = QuotientGroup.mk (n⁻¹ * x) := by
    rw [QuotientGroup.eq]
    have := (inferInstance : N.Normal).conj_mem n⁻¹ (inv_mem hn) x⁻¹
    simpa [mul_assoc] using this
  have h1 : orderOf (QuotientGroup.mk x : Λ ⧸ N) ∣ 3 ^ k :=
    orderOf_dvd_of_pow_eq_one (by rw [← QuotientGroup.mk_pow, hx, QuotientGroup.mk_one])
  have h2 : orderOf (QuotientGroup.mk x : Λ ⧸ N) ∣ orderOf (n⁻¹ * x) := by
    rw [hmk]
    exact orderOf_map_dvd (QuotientGroup.mk' N) _
  have hu3 : Nat.Coprime (3 ^ k) (orderOf (n⁻¹ * x)) :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr fun h3 =>
      hk (h3.trans (Subgroup.orderOf_dvd_natCard f.ker hu)))
  have h3 : orderOf (QuotientGroup.mk x : Λ ⧸ N) = 1 := by
    have := Nat.dvd_gcd h1 h2
    rw [hu3] at this
    exact Nat.dvd_one.mp this
  rw [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at h3
  exact h3

end General

section LSide

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem map_centralizer_singleton_mk {Λ : Type} [Group Λ] [Finite Λ] {z : Λ}
    (hz : IsPGroup 3 (Subgroup.zpowers z)) :
    (Subgroup.centralizer ({z} : Set Λ)).map (QuotientGroup.mk' (aschbacherSolvableCore 3 Λ)) =
      Subgroup.centralizer ({QuotientGroup.mk' (aschbacherSolvableCore 3 Λ) z} : Set _) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h := CFSG.Semidihedral.Local.map_centralizer_eq_of_coprime 3 (aschbacherSolvableCore 3 Λ)
    (solvable_prime_complement_core_characterization (H := Λ) Nat.prime_three).2.2.1
    (Subgroup.zpowers z) hz
  rw [MonoidHom.map_zpowers, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure,
    Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure] at h
  exact h

theorem mem_residual_of_pow_three (h415 : Sec4.Item4_15)
    (hJ2 : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    {d : G} (hdL : d ∈ L) (hd1 : d ≠ 1)
    (hc : ∃ S : Sylow 3 ↥L, (⟨d, hdL⟩ : ↥L) ∈ (S : Subgroup ↥L) ∧
      (S : Subgroup ↥L) ≤ Subgroup.centralizer ({(⟨d, hdL⟩ : ↥L)} : Set ↥L))
    {x : G} (hxL : x ∈ L) (hxd : x ∈ Subgroup.centralizer ({d} : Set G)) {k : ℕ}
    (hx : x ^ 3 ^ k = 1) :
    x ∈ inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hd'1 : (⟨d, hdL⟩ : ↥L) ≠ 1 := fun h => hd1 (congrArg Subtype.val h)
  rw [residual_inf_centralizer_eq_map hdL]
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) with hπ
  set CL := Subgroup.centralizer ({(⟨d, hdL⟩ : ↥L)} : Set ↥L) with hCL
  have hJQ := map_residual_centralizer_eq h415 hJ2 hd'1 hc
  obtain ⟨S, hdS, -⟩ := hc
  have hz3 : IsPGroup 3 (Subgroup.zpowers (⟨d, hdL⟩ : ↥L)) :=
    S.isPGroup'.to_le (Subgroup.zpowers_le.mpr hdS)
  have hCmap := map_centralizer_singleton_mk hz3
  let f : ↥CL →* ↥L ⧸ aschbacherSolvableCore 3 ↥L := π.comp CL.subtype
  have hN : (perfectResidual ↥CL).map f = f.range := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype, hCmap, ← Subgroup.map_map]
    exact hJQ
  obtain ⟨hθs, -, hθp, -, -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three
  obtain ⟨-, hk⟩ := ker_facts_of_injective f CL.subtype CL.subtype_injective
    (aschbacherSolvableCore 3 ↥L)
    (fun y hy => by
      have h2 : π (y : ↥L) = 1 := hy
      rwa [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2) hθs hθp
  have hxCL : (⟨x, hxL⟩ : ↥L) ∈ CL := by
    rw [hCL, Subgroup.mem_centralizer_singleton_iff]
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hxd)
  have hx' : (⟨⟨x, hxL⟩, hxCL⟩ : ↥CL) ^ 3 ^ k = 1 := Subtype.ext (Subtype.ext (by simpa using hx))
  have := mem_of_pow_three_of_map_eq f (perfectResidual ↥CL) hN hk hx'
  exact ⟨⟨x, hxL⟩, ⟨_, this, rfl⟩, rfl⟩

theorem conj_mem_thetaComponentsAt_of_mem_centralizer {d x : G}
    (hx : x ∈ Subgroup.centralizer ({d} : Set G)) {K : Subgroup G}
    (hK : K ∈ thetaComponentsAt 3 d) :
    K.map (MulAut.conj x).toMonoidHom ∈ thetaComponentsAt 3 d := by
  set H := Subgroup.centralizer ({d} : Set G) with hH
  obtain ⟨K', hK', rfl⟩ := hK
  refine ⟨K'.map (MulAut.conj (⟨x, hx⟩ : H)).toMonoidHom,
    map_mulEquiv_mem_thetaComponents Nat.prime_three (MulAut.conj (⟨x, hx⟩ : H)) hK', ?_⟩
  show (K'.map (MulAut.conj (⟨x, hx⟩ : H)).toMonoidHom).map H.subtype =
    (K'.map H.subtype).map (MulAut.conj x).toMonoidHom
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1

end LSide

section Bar

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem exists_sylow_of_center_eq {L : Subgroup G} {d : G}
    (hS : ∃ S : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 3 S L ∧
      (Subgroup.center S).map S.subtype = Subgroup.zpowers d) :
    ∃ hdL : d ∈ L, ∃ S' : Sylow 3 ↥L, (⟨d, hdL⟩ : ↥L) ∈ (S' : Subgroup ↥L) ∧
      (S' : Subgroup ↥L) ≤ Subgroup.centralizer ({(⟨d, hdL⟩ : ↥L)} : Set ↥L) := by
  obtain ⟨S, ⟨Q, hQ⟩, hZS⟩ := hS
  have hdZ : d ∈ (Subgroup.center S).map S.subtype := hZS ▸ Subgroup.mem_zpowers d
  obtain ⟨s, hs, hsd⟩ := hdZ
  have hdS : d ∈ S := hsd ▸ s.2
  have hdQ : d ∈ (Q : Subgroup ↥L).map L.subtype := hQ ▸ hdS
  obtain ⟨q₀, hq₀, hq₀d⟩ := hdQ
  have hdL : d ∈ L := hq₀d ▸ q₀.2
  refine ⟨hdL, Q, ?_, fun q hq => ?_⟩
  · have : q₀ = ⟨d, hdL⟩ := Subtype.ext hq₀d
    exact this ▸ hq₀
  · rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    have hqS : (q : G) ∈ S := hQ ▸ Subgroup.mem_map_of_mem L.subtype hq
    have h1 := congrArg Subtype.val (Subgroup.mem_center_iff.mp hs ⟨q, hqS⟩)
    have hsd' : (s : G) = d := hsd
    simp only [Subgroup.coe_mul] at h1
    rw [hsd'] at h1
    exact h1

theorem le_normalizer_inSubgroup_theta (K : Subgroup G) :
    K ≤ Subgroup.normalizer (inSubgroup (aschbacherSolvableCore 3) K : Set G) := by
  intro k hk
  rw [Subgroup.mem_normalizer_iff]
  intro t
  constructor
  · exact Sec12.conj_mem_inSubgroup_theta (Subgroup.le_normalizer hk)
  · intro ht
    have := Sec12.conj_mem_inSubgroup_theta (Subgroup.le_normalizer (inv_mem hk)) ht
    simpa [mul_assoc] using this

theorem mem_thetaQuotCentralizer_of_centralizes {J K : Subgroup G} {g : G}
    (hgN : g ∈ Subgroup.normalizer (K : Set G)) (hgJ : ∀ j ∈ J, g * j = j * g)
    (hJK : J ≤ K) (hK : K = J ⊔ inSubgroup (aschbacherSolvableCore 3) K) :
    g ∈ Sec4.thetaQuotCentralizer K := by
  refine Sec6.mem_thetaQuotCentralizer_iff.mpr ⟨hgN, fun l hl => ?_⟩
  have hJN : J ≤ Subgroup.normalizer (inSubgroup (aschbacherSolvableCore 3) K : Set G) :=
    hJK.trans (le_normalizer_inSubgroup_theta K)
  have hset := Subgroup.coe_mul_of_left_le_normalizer_right J _ hJN
  have hl' : l ∈ ((J ⊔ inSubgroup (aschbacherSolvableCore 3) K : Subgroup G) : Set G) := by
    rw [← hK]
    exact hl
  rw [hset] at hl'
  obtain ⟨j, hj, t, ht, rfl⟩ := hl'
  have hgt := Sec12.conj_mem_inSubgroup_theta hgN ht
  have e : (j * t)⁻¹ * (g * (j * t) * g⁻¹) = t⁻¹ * (g * t * g⁻¹) := by
    rw [← mul_assoc g j t, hgJ j hj]
    group
  rw [e]
  exact mul_mem (inv_mem ht) hgt

theorem facts134 (h131 : Item131) (hspor : SporadicModels131) (h415 : Sec4.Item4_15)
    {A L : Subgroup G} {c : G} (h : Sec13Data G A c L)
    (hJ : Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* CFSG.Blueprint.NativeSporadic.J2))
    {d : G} (hdA : d ∈ A) (hd1 : d ≠ 1)
    (hS : ∃ S : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 3 S L ∧
      (Subgroup.center S).map S.subtype = Subgroup.zpowers d)
    {K : Subgroup G} (hK : K ∈ thetaComponentsAt 3 d)
    (hLK : inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G)) ≤ K)
    (hKeq : K = inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G)) ⊔
      inSubgroup (aschbacherSolvableCore 3) K)
    (hA6 : Sec4.IsTripleCover (K ⧸ aschbacherSolvableCore 3 K) (alternatingGroup (Fin 6))) :
    d ∈ K ∧ A ⊓ Sec4.thetaQuotCentralizer K = Subgroup.zpowers c ⊔ Subgroup.zpowers d ∧
      Nat.card (A ⊓ Sec4.thetaQuotCentralizer K : Subgroup G) = 9 ∧
      (A ⊓ Sec4.thetaQuotCentralizer K) ⊔ (A ⊓ K) = A := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set J := inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G)) with hJdef
  obtain ⟨hdL, hc⟩ := exists_sylow_of_center_eq hS
  obtain ⟨hqs, -, hdJ, -⟩ := residual_facts h415 hJ hdL hd1 hc
  replace hdJ : d ∈ J := hdJ
  have hdK : d ∈ K := hLK hdJ
  have hc3 : c ^ 3 = 1 := h.isElemAbelian.2 c h.mem_A
  have hd3 : d ^ 3 = 1 := h.isElemAbelian.2 d hdA
  have hLc : ∀ l ∈ L, l * c = c * l := fun l hl =>
    Subgroup.mem_centralizer_singleton_iff.mp (h.le_centralizer hl)
  have hspor' := hspor
  obtain ⟨-, -, -, hJ2z⟩ := hspor'
  obtain ⟨φ⟩ := hJ
  have hZ : Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) = ⊥ :=
    center_eq_bot_of_mulEquiv φ hJ2z
  have hcL : c ∉ L := not_mem_of_center_eq_bot h hZ
  have h9 : Nat.card (A ⊓ L : Subgroup G) = 9 := by
    obtain ⟨-, -, h9 | hPGL⟩ := facts_of_not_mem h131 hspor slTwoCenter h hcL
    · exact h9
    · exfalso
      obtain ⟨p, e, hp, -, hiso⟩ := (facts_of_isZ3PGLThreePi h hPGL).1
      apply KFacts.KS14.ks17J2NotList.1 p e
      rcases hiso with ⟨hq, ⟨ψ⟩⟩ | ⟨hq, ⟨ψ⟩⟩
      · exact Or.inl ⟨hq, ⟨φ.symm.trans ψ⟩⟩
      · exact Or.inr ⟨hq, ⟨φ.symm.trans ψ⟩⟩
  have hAL : A ⊓ L ≤ J := fun a ha =>
    mem_residual_of_pow_three h415 ⟨φ⟩ hdL hd1 hc ha.2
      (Subgroup.mem_centralizer_singleton_iff.mpr (h.commute ha.1 hdA))
      (k := 1) (by rw [pow_one]; exact h.isElemAbelian.2 a ha.1)
  have hAB : A = Subgroup.zpowers c ⊔ (A ⊓ L) := by
    have hle : Subgroup.zpowers c ⊔ (A ⊓ L) ≤ A :=
      sup_le (Subgroup.zpowers_le.mpr h.mem_A) inf_le_left
    have hcard := (isElemAbelian_zpowers_sup_of_card_nine hc3
      (fun hcB => hcL (Subgroup.mem_inf.mp hcB).2) le_rfl h9
      (fun b hb => h.isElemAbelian.2 b hb.1) (fun b hb => h.commute h.mem_A hb.1)).2
    exact (Subgroup.eq_of_le_of_card_ge hle (by rw [h.card_eq, hcard])).symm
  have hcd : c ∈ Subgroup.centralizer ({d} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (h.commute h.mem_A hdA)
  have hcJ : ∀ j ∈ J, c * j = j * c := fun j hj =>
    (hLc j ((Subgroup.map_subtype_le _ hj : j ∈ L ⊓ _).1)).symm
  have hJperf : Group.IsPerfect J := by
    have h := (perfect_residual_characterization
      (G := ↥(L ⊓ Subgroup.centralizer ({d} : Set G)))).2.2.1
    exact Group.IsPerfect.ofSurjective
      (f := ((perfectResidual ↥(L ⊓ Subgroup.centralizer ({d} : Set G))).equivMapOfInjective _
        (Subgroup.subtype_injective _)).toMonoidHom) (MulEquiv.surjective _)
  have hJne : J ≠ ⊥ := fun hb => hd1 (by rw [hb] at hdJ; exact Subgroup.mem_bot.mp hdJ)
  have hJc : J.map (MulAut.conj c).toMonoidHom = J := by
    ext x
    constructor
    · rintro ⟨j, hj, rfl⟩
      change c * j * c⁻¹ ∈ J
      rw [hcJ j hj, mul_inv_cancel_right]
      exact hj
    · intro hx
      refine ⟨x, hx, ?_⟩
      change c * x * c⁻¹ = x
      rw [hcJ x hx, mul_inv_cancel_right]
  have hKc : K.map (MulAut.conj c).toMonoidHom = K :=
    CFSG.RankThree.PartOne.EmbeddingFixedResidual.eq_of_perfect_le_of_mem_thetaComponentsAt
      Nat.prime_three
      (conj_mem_thetaComponentsAt_of_mem_centralizer hcd hK) hK hJne hJperf
      (hJc ▸ Subgroup.map_mono hLK) hLK
  have hcN : c ∈ Subgroup.normalizer (K : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr hKc
  have hcθ : c ∈ Sec4.thetaQuotCentralizer K :=
    mem_thetaQuotCentralizer_of_centralizes hcN hcJ hLK hKeq
  have hdθ : d ∈ Sec4.thetaQuotCentralizer K :=
    Sec12.mem_thetaQuotCentralizer_of_central hdK (PartOne.mem_thetaComponentsAt_iff.mp hK).1
  have hle : Subgroup.zpowers c ⊔ Subgroup.zpowers d ≤ A ⊓ Sec4.thetaQuotCentralizer K :=
    sup_le (Subgroup.zpowers_le.mpr ⟨h.mem_A, hcθ⟩) (Subgroup.zpowers_le.mpr ⟨hdA, hdθ⟩)
  have hcdZ : c ∉ Subgroup.zpowers d := fun hc' =>
    hcL ((Subgroup.zpowers_le.mpr hdL) hc')
  have hcard9 : Nat.card (Subgroup.zpowers c ⊔ Subgroup.zpowers d : Subgroup G) = 9 := by
    have hcomm : ∀ x ∈ Subgroup.zpowers c, ∀ y ∈ Subgroup.zpowers d, x * y = y * x := by
      intro x hx y hy
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      exact (Commute.zpow_zpow (h.commute h.mem_A hdA) i j).eq
    obtain ⟨hcard, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcomm
    rw [zpowers_inf_eq_bot hc3 hcdZ, Subgroup.card_bot, mul_one,
      card_zpowers_of_pow_three hc3 h.ne_one, card_zpowers_of_pow_three hd3 hd1] at hcard
    exact hcard
  have hnotA : ¬ A ≤ Sec4.thetaQuotCentralizer K := by
    intro hAθ
    set B := (A ⊓ L).subgroupOf K with hBdef
    have hALK : A ⊓ L ≤ K := hAL.trans hLK
    set πK := QuotientGroup.mk' (aschbacherSolvableCore 3 K) with hπK
    have hBp : IsPGroup 3 B := IsPGroup.of_card (n := 2) (by
      rw [show (3 : ℕ) ^ 2 = 9 by norm_num, ← h9]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hALK).toEquiv)
    have hBZ : B.map πK ≤ Subgroup.center (K ⧸ aschbacherSolvableCore 3 K) := by
      rintro _ ⟨b, hb, rfl⟩
      rw [Subgroup.mem_center_iff]
      intro q
      obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective _ q
      have hbθ := (Sec6.mem_thetaQuotCentralizer_iff.mp
        (hAθ (Subgroup.mem_subgroupOf.mp hb).1)).2 l l.2
      have hmem : l⁻¹ * (b * l * b⁻¹) ∈ aschbacherSolvableCore 3 K := by
        obtain ⟨u, hu, hu'⟩ := hbθ
        have : u = l⁻¹ * (b * l * b⁻¹) := Subtype.ext (by simpa using hu')
        exact this ▸ hu
      have h1 : πK (l⁻¹ * (b * l * b⁻¹)) = 1 := by
        rw [hπK, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
        exact hmem
      simp only [map_mul, map_inv] at h1
      calc πK l * πK b = πK l * ((πK l)⁻¹ * (πK b * πK l * (πK b)⁻¹)) * πK b := by
            rw [h1, mul_one]
        _ = πK b * πK l := by group
    have hcardB : Nat.card (B.map πK) = 9 := by
      rw [card_map_eq_of_injOn _ (injOn_mk_of_isPGroup Nat.prime_three hBp)]
      rw [← h9]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hALK).toEquiv
    have := Subgroup.card_le_of_le hBZ
    rw [hcardB, hA6.1] at this
    norm_num at this
  have hdvd : Nat.card (A ⊓ Sec4.thetaQuotCentralizer K : Subgroup G) ∣ 3 ^ 3 := by
    rw [show (3 : ℕ) ^ 3 = 27 by norm_num, ← h.card_eq]
    exact Subgroup.card_dvd_of_le inf_le_left
  obtain ⟨m, hm3, hm⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
  have hge : 9 ≤ Nat.card (A ⊓ Sec4.thetaQuotCentralizer K : Subgroup G) :=
    hcard9 ▸ Subgroup.card_le_of_le hle
  have heq : A ⊓ Sec4.thetaQuotCentralizer K = Subgroup.zpowers c ⊔ Subgroup.zpowers d := by
    interval_cases m
    · rw [hm] at hge; norm_num at hge
    · rw [hm] at hge; norm_num at hge
    · exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hm, hcard9]; norm_num)).symm
    · exfalso
      apply hnotA
      have hAA : A ⊓ Sec4.thetaQuotCentralizer K = A :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hm, h.card_eq]; norm_num)
      exact hAA ▸ inf_le_right
  refine ⟨hdK, heq, heq ▸ hcard9, le_antisymm (sup_le inf_le_left inf_le_left) ?_⟩
  calc A = Subgroup.zpowers c ⊔ (A ⊓ L) := hAB
    _ ≤ (A ⊓ Sec4.thetaQuotCentralizer K) ⊔ (A ⊓ K) :=
      sup_le_sup (Subgroup.zpowers_le.mpr ⟨h.mem_A, hcθ⟩)
        (le_inf inf_le_left (hAL.trans hLK))

theorem le_center_of_not_le_normalizer (h45 : Sec4.Item4_5) (h131 : Item131)
    (hspor : SporadicModels131) (h415 : Sec4.Item4_15)
    {A L : Subgroup G} {c : G} (h : Sec13Data G A c L)
    (hJ : Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* CFSG.Blueprint.NativeSporadic.J2))
    {d : G} (hdA : d ∈ A) (hd1 : d ≠ 1)
    (hS : ∃ S : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 3 S L ∧
      (Subgroup.center S).map S.subtype = Subgroup.zpowers d)
    {K : Subgroup G} (hK : K ∈ thetaComponentsAt 3 d)
    (hLK : inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G)) ≤ K)
    (hKeq : K = inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G)) ⊔
      inSubgroup (aschbacherSolvableCore 3) K)
    (hA6 : Sec4.IsTripleCover (K ⧸ aschbacherSolvableCore 3 K) (alternatingGroup (Fin 6)))
    (hW : ¬ Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers d : Set G)) :
    ∀ P : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 3 P
        (Subgroup.normalizer (A : Set G) ⊓ Subgroup.normalizer (Subgroup.zpowers d : Set G)) →
      Subgroup.zpowers c ⊔ Subgroup.zpowers d ≤ (Subgroup.center P).map P.subtype := by
  obtain ⟨hdK, heq, h9, hsup⟩ := facts134 h131 hspor h415 h hJ hdA hd1 hS hK hLK hKeq hA6
  intro P hP
  by_contra hPB
  apply hW
  have hFE := (h.toTheoremFourHyp.partTwoF_eq_partTwoE h.partTwoS_eq).1
  have hstd : Sec12.Sec12StdBar G A d K :=
    { h.toPartTwoStanding with
      partTwoF_eq := hFE
      isE27 := ⟨h.isElemAbelian, h.card_eq⟩
      mem_A := hdA
      ne_one := hd1
      mem_thetaComponentsAt := hK
      mem_L := hdK
      card_B := h9
      sup_eq := hsup
      exists_sylow := ⟨P, hP, by rwa [heq]⟩ }
  exact Sec12.normalizer_le_of_sec12StdBar_A6 h45 hstd hA6

end Bar

@[expose] def Item134SylowBar : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec13Data G A c L →
    Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* CFSG.Blueprint.NativeSporadic.J2) →
    ∀ d ∈ A, d ≠ 1 →
    (∃ S : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 3 S L ∧
      (Subgroup.center S).map S.subtype = Subgroup.zpowers d) →
    ∀ K ∈ thetaComponentsAt 3 d,
      inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G)) ≤ K →
      K = inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G)) ⊔
          inSubgroup (aschbacherSolvableCore 3) K →
      Sec4.IsTripleCover (K ⧸ aschbacherSolvableCore 3 K) (alternatingGroup (Fin 6)) →
      ¬ Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers d : Set G) →
      (∀ P : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 3 P
          (Subgroup.normalizer (A : Set G) ⊓ Subgroup.normalizer (Subgroup.zpowers d : Set G)) →
        Subgroup.zpowers c ⊔ Subgroup.zpowers d ≤ (Subgroup.center P).map P.subtype) →
        omegaA A = {Subgroup.zpowers c}

theorem item134Sylow_of (h45 : Sec4.Item4_5) (h131 : Item131) (hspor : SporadicModels131)
    (h415 : Sec4.Item4_15) (hBar : Item134SylowBar) : Item134Sylow := by
  intro G _ _ A c L h hJ d hdA hd1 hS K hK hLK hKeq hA6 hW
  exact hBar G A c L h hJ d hdA hd1 hS K hK hLK hKeq hA6 hW
    (le_center_of_not_le_normalizer h45 h131 hspor h415 h hJ hdA hd1 hS hK hLK hKeq hA6 hW)

end CFSG.RankThree.PartTwo.Sec13
