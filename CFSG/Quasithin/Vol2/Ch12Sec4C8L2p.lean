module

public import CFSG.Quasithin.Vol2.Ch12Sec4C8Lift
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListL2sq

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.BenderSuzuki.MatrixGroups CFSG.Glauberman.Dickson

namespace KGL2

theorem exists_psl2_equiv {X : Type} [Group X] {p : ℕ}
    (h : CFSG.Assembly.LowTwoRank.StatedClassicalModel X .PSL 2 p 1) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ∧
      Nonempty (X ≃* PSL2MatrixGroup F) ∧ p.Prime ∧ p ≠ 2 ∧ p ≠ 3 := by
  obtain ⟨⟨hp, -, -, h22, h23⟩, F, _, _, hF, ⟨e⟩⟩ := h
  refine ⟨F, inferInstance, inferInstance, by rw [hF, pow_one],
    ⟨e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F).symm⟩,
    hp, ?_, ?_⟩
  · intro h2
    apply h22
    rw [h2]
    rfl
  · intro h3
    apply h23
    rw [h3]
    rfl

theorem card_mul_two {X : Type} [Group X] {F : Type} [Field F] [Finite F] {q : ℕ}
    (hq : q.Prime) (hq2 : q ≠ 2) (hF : Nat.card F = q) (e : X ≃* PSL2MatrixGroup F) :
    Nat.card X * 2 = q * (q ^ 2 - 1) := by
  have hodd : Odd q := hq.odd_of_ne_two hq2
  have hc := CFSG.GorensteinWalter.psl2_card_formula F
    ⟨q, 1, hq, hodd, le_rfl, by rw [hF, pow_one]⟩
  rw [Nat.card_congr e.toEquiv, show Nat.card (PSL2MatrixGroup F) =
    Nat.card (CFSG.GorensteinWalter.PSL2 F) from rfl, hc, hF]
  have h2 : 2 ∣ q * (q ^ 2 - 1) := by
    have h1 : (q ^ 2) % 2 = 1 := by
      rw [Nat.pow_mod, Nat.odd_iff.1 hodd]
    have : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq.pos
    exact Dvd.dvd.mul_left (by omega) _
  exact Nat.div_mul_cancel h2

theorem sixteen_dvd {q : ℕ} (hq : QuasithinUnique.Ch1.IsFermatOrMersennePrime q) (h3 : q ≠ 3)
    (h5 : q ≠ 5) : 16 ∣ q * (q ^ 2 - 1) := by
  obtain ⟨-, ⟨k, rfl⟩ | ⟨k, hk, rfl⟩⟩ := hq
  ·
    have hk : 2 ≤ k := by
      by_contra h
      push Not at h
      interval_cases k <;> simp_all
    have h16 : 16 ∣ 2 ^ 2 ^ k := by
      have : 4 ≤ 2 ^ k := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
      have h := pow_dvd_pow 2 this
      norm_num at h
      exact h
    obtain ⟨m, hm⟩ := h16
    rw [hm]
    have e : (16 * m + 1) ^ 2 - 1 = 16 * (m * (16 * m + 2)) := by
      have : 1 ≤ (16 * m + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
      zify [this]
      ring
    rw [e]
    exact Dvd.dvd.mul_left (Dvd.intro _ rfl) _
  ·
    have hk3 : 3 ≤ k := by
      by_contra h
      push Not at h
      interval_cases k
      simp_all
    have h8 : 8 ∣ 2 ^ k := by
      have h := pow_dvd_pow 2 hk3
      norm_num at h
      exact h
    obtain ⟨m, hm⟩ := h8
    have hm1 : 1 ≤ m := by
      rcases Nat.eq_zero_or_pos m with h | h
      · rw [h] at hm
        have := Nat.one_le_two_pow (n := k)
        omega
      · exact h
    rw [hm]
    have e : (8 * m - 1) ^ 2 - 1 = 16 * (m * (4 * m - 1)) := by
      have h1 : 1 ≤ 8 * m := by omega
      have h2 : 1 ≤ (8 * m - 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
      have h3 : 1 ≤ 4 * m := by omega
      zify [h1, h2, h3]
      ring
    rw [e]
    exact Dvd.dvd.mul_left (Dvd.intro _ rfl) _

theorem not_isSolvable_of_model {X : Type} [Group X] {p : ℕ}
    (h : CFSG.Assembly.LowTwoRank.StatedClassicalModel X .PSL 2 p 1) : ¬ Group.IsSolvable X := by
  obtain ⟨hnt, -⟩ := CFSG.LieType.Simplicity.fam_PSL_simplicity _ _ _ _ h
  obtain ⟨F, _, _, hF, ⟨e⟩, hpp, hp2, hp3⟩ := exists_psl2_equiv h
  have h3 : 3 < Nat.card F := by
    rw [hF]
    have := hpp.two_le
    omega
  have : Group.IsPerfect (PSL2MatrixGroup F) :=
    CFSG.GorensteinWalter.psl2_isPerfect_of_card_gt_three F h3
  have : Group.IsPerfect X :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  exact Group.IsPerfect.not_isSolvable X

end KGL2

open KGL2

theorem l2pThreeFact1248 : L2pThreeFact1248 := by
  intro X _ _ p hp h
  refine ⟨S1248.three_dvd_card_psl2 h, ?_⟩
  obtain ⟨F, _, _, hF, ⟨e⟩, hpp, hp2, hp3⟩ := exists_psl2_equiv h
  have : Fact p.Prime := ⟨hpp⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hr
  push Not at hr
  obtain ⟨E, -, hEab, hEcard⟩ :=
    CFSG.SectionRank.exists_pRank (p := 3) (by norm_num) (⊤ : Subgroup X)
  have h9 : 3 ^ 2 ∣ Nat.card E := by
    rw [hEcard]
    exact pow_dvd_pow 3 hr
  obtain ⟨E₉, hE₉⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥E) 3 (n := 2) h9
  set H : Subgroup (PSL2MatrixGroup F) := (E₉.map E.subtype).map e.toMonoidHom with hH
  have hH9 : Nat.card H = 9 := by
    rw [hH, Subgroup.card_map_of_injective e.injective,
      Subgroup.card_map_of_injective E.subtype_injective, hE₉]
    norm_num
  have hH3 : ∀ x : ↥H, x ^ 3 = 1 := by
    rintro ⟨_, ⟨_, ⟨y, -, rfl⟩, rfl⟩⟩
    apply Subtype.ext
    change e.toMonoidHom (E.subtype y) ^ 3 = 1
    have hy3 : y ^ 3 = 1 := Subtype.ext (by simpa using hEab.2 _ y.2)
    rw [← map_pow, ← map_pow, hy3, map_one, map_one]
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥H) 3 (by rw [hH9]; norm_num)
  have hnot_cyc : ¬ IsCyclic ↥H := by
    intro hc
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥H)
    have hg9 : orderOf g = 9 := by
      rw [orderOf_eq_card_of_forall_mem_zpowers hg, hH9]
    have := orderOf_dvd_of_pow_eq_one (hH3 g)
    rw [hg9] at this
    norm_num at this
  rcases huppert_II_8_27_dickson_psl2_subgroup_classification (p := p) (f := 1)
      (by rw [hF, pow_one]) H with
    h1 | ⟨z, -, hz, hcyc⟩ | ⟨z, -, hz, -⟩ | ⟨-, ⟨eA⟩⟩ | ⟨-, ⟨eS⟩⟩ | ⟨-, ⟨eA5⟩⟩ |
      ⟨m, t, -, -, N, C, hN, hNel, hNcard, hC, hCcard, hdisj, hsup⟩ | ⟨m, -, hm, ⟨eP⟩⟩ |
      ⟨m, hm0, hm, -⟩
  ·
    have hxp : x ^ p = 1 := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p p ↥H) x
    have := orderOf_dvd_of_pow_eq_one hxp
    rw [hx] at this
    exact hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hpp).1 this).symm
  · exact hnot_cyc hcyc
  · rw [hH9] at hz
    omega
  · have := Nat.card_congr eA.toEquiv
    rw [hH9, Nat.card_eq_fintype_card] at this
    revert this
    decide
  · have := Nat.card_congr eS.toEquiv
    rw [hH9, Nat.card_perm, Nat.card_fin] at this
    revert this
    decide
  · have := Nat.card_congr eA5.toEquiv
    rw [hH9, Nat.card_eq_fintype_card] at this
    revert this
    decide
  ·
    have hNd : Nat.card N ∣ 9 := hH9 ▸ Subgroup.card_subgroup_dvd_card N
    have hm0 : m = 0 := by
      by_contra hm
      have h1 : p ∣ 3 ^ 2 := (dvd_pow_self p hm).trans (hNcard ▸ (by simpa using hNd))
      exact hp3 ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_three).1 (hpp.dvd_of_dvd_pow h1))
    rw [hm0, pow_zero] at hNcard
    have hNbot : N = ⊥ := Subgroup.eq_bot_of_card_eq N hNcard
    rw [hNbot, bot_sup_eq] at hsup
    apply hnot_cyc
    have hCt : IsCyclic ↥(⊤ : Subgroup ↥H) := hsup ▸ hC
    exact isCyclic_of_surjective (⊤ : Subgroup ↥H).subtype fun x => ⟨⟨x, trivial⟩, rfl⟩
  · obtain rfl : m = 1 := Nat.dvd_one.1 hm
    have h2 := card_mul_two hpp hp2 (by rw [GaloisField.card p 1 one_ne_zero, pow_one]) eP
    rw [hH9] at h2
    have hpd : p ∣ 2 * 3 ^ 2 := Dvd.intro _ (by rw [← h2]; norm_num)
    rcases (Nat.Prime.dvd_mul hpp).1 hpd with h | h
    · exact hp2 ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).1 h)
    · exact hp3 ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_three).1 (hpp.dvd_of_dvd_pow h))
  · have := Nat.le_of_dvd one_pos hm
    omega

theorem l2pEmbedFact1248 : L2pEmbedFact1248 := by
  intro Y _ _ K K₁ S p q hp hq hK hK₁ hKK₁ hS hSN
  obtain ⟨F₁, _, _, hF₁, ⟨e₁⟩, hqp, hq2, hq3⟩ := exists_psl2_equiv hK₁
  have : Fact q.Prime := ⟨hqp⟩
  obtain ⟨hKnt, -⟩ := CFSG.LieType.Simplicity.fam_PSL_simplicity _ _ _ _ hK
  obtain ⟨-, hK₁s⟩ := CFSG.LieType.Simplicity.fam_PSL_simplicity _ _ _ _ hK₁
  have hc₁ := card_mul_two hqp hq2 hF₁ e₁
  set N : Subgroup ↥K₁ := (Subgroup.normalizer (K : Set Y)).subgroupOf K₁ with hNdef
  have hKN : K.subgroupOf K₁ ≤ N := fun x hx =>
    Subgroup.mem_subgroupOf.2 (Subgroup.le_normalizer (Subgroup.mem_subgroupOf.1 hx))
  have hSN' : S.subgroupOf K₁ ≤ N := fun x hx =>
    Subgroup.mem_subgroupOf.2 (hSN (Subgroup.mem_subgroupOf.1 hx))
  have hNns : ¬ Group.IsSolvable ↥(N.map e₁.toMonoidHom) := by
    intro hs
    have : Group.IsSolvable ↥N := Group.isSolvable_of_isSolvable_injective
      (f := (N.equivMapOfInjective e₁.toMonoidHom e₁.injective).toMonoidHom)
      (N.equivMapOfInjective e₁.toMonoidHom e₁.injective).injective
    have : Group.IsSolvable ↥(K.subgroupOf K₁) := Group.isSolvable_of_isSolvable_injective
      (f := Subgroup.inclusion hKN) (Subgroup.inclusion_injective hKN)
    exact not_isSolvable_of_model hK (Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hKK₁).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hKK₁).symm.injective)
  have hcN : Nat.card ↥(N.map e₁.toMonoidHom) = Nat.card N :=
    Subgroup.card_map_of_injective e₁.injective
  have hNtop : N = ⊤ := by
    rcases Vol2Native.A312L.dickson_nonsolvable_cases (p := q) (f := 1) (by rw [hF₁, pow_one]) _
        hNns with
      ⟨⟨eA⟩, -⟩ | ⟨m, -, hm1, ⟨eP⟩⟩ | ⟨m, hm0, hm1, -⟩
    · have h60 : Nat.card N = 60 := by
        rw [← hcN, Nat.card_congr eA.toEquiv, Nat.card_eq_fintype_card]
        rfl
      by_cases hq5 : q = 5
      · subst hq5
        apply Subgroup.eq_top_of_card_eq
        norm_num at hc₁
        omega
      · exfalso
        have h16 := sixteen_dvd hq hq3 hq5
        rw [← hc₁] at h16
        have h8 : 8 ∣ Nat.card ↥K₁ := by omega
        have hT : IsSylowTwoOf (S.subgroupOf K₁) ⊤ := by
          refine ⟨le_top, hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS.1).symm, ?_⟩
          rw [show ((S.subgroupOf K₁).subgroupOf ⊤).index = (S.subgroupOf K₁).index from
            Subgroup.relIndex_top_right _]
          exact hS.2.2
        have h8S := Vol2Native.A312L.eight_dvd_card_of_isSylowTwoOf hT h8
        have hdvd : Nat.card ↥(S.subgroupOf K₁) ∣ Nat.card N := Subgroup.card_dvd_of_le hSN'
        rw [h60] at hdvd
        have := h8S.trans hdvd
        norm_num at this
    · obtain rfl : m = 1 := Nat.dvd_one.1 hm1
      apply Subgroup.eq_top_of_card_eq
      have h2 := Vol2Native.A312L.card_psl2_prime' (p := q) hq2
      rw [Nat.card_congr eP.toEquiv] at hcN
      omega
    · have := Nat.le_of_dvd one_pos hm1
      omega
  have hnormal : (K.subgroupOf K₁).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hKK₁]
    intro h k hh hk
    have hkN : (⟨k, hk⟩ : ↥K₁) ∈ N := hNtop ▸ Subgroup.mem_top _
    exact (Subgroup.mem_normalizer_iff.1 (Subgroup.mem_subgroupOf.1 hkN) h).1 hh
  have := hK₁s
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (K.subgroupOf K₁) with hbot | htop
  · exfalso
    obtain ⟨x, hx⟩ := exists_ne (1 : ↥K)
    have hxK : (⟨x.1, hKK₁ x.2⟩ : ↥K₁) ∈ K.subgroupOf K₁ := Subgroup.mem_subgroupOf.2 x.2
    rw [hbot, Subgroup.mem_bot] at hxK
    have h1 : (x : Y) = 1 := congrArg Subtype.val hxK
    exact hx (Subtype.ext h1)
  · exact le_antisymm hKK₁ (Subgroup.subgroupOf_eq_top.1 htop)

end CFSG.Quasithin.H13
