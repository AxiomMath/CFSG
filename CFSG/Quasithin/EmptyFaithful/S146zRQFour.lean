module

public import CFSG.Quasithin.EmptyFaithful.S146zRImg
public import CFSG.Quasithin.EmptyFaithful.S146zMSol
public import CFSG.Quasithin.EmptyFaithful.S146zQLists

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native CFSG.SectionRank
  CFSG.LieType.BorelTits

section Setup

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

theorem Setting146.sqtkHyp_quotient (S : Setting146 G T M) : SQTKHyp (OTwoQuot (mcOf T)) := by
  have := sqtkHyp_quotient_of_pCoreOf_ne_bot S.hyp.qtke S.hyp.simple S.hyp.nonabelian
    S.isHTM_mcOf.1.2
  convert this using 3
  all_goals exact (CFSG.pCore_eq_open _ _).symm

theorem Setting146.pRank_quotient_le_two (S : Setting146 G T M) {r : ℕ} (hr : r.Prime)
    (hr2 : r ≠ 2) : CFSG.Open.pRank r (⊤ : Subgroup (OTwoQuot (mcOf T))) ≤ 2 := by
  have hSQ : CFSG.IsStronglyQuasithin ↥(mcOf T) :=
    isStronglyQuasithin_of_pCoreOf_ne_bot_of_evenRank S.hyp.qtke.2.2 S.isHTM_mcOf.1.2
  have hrX : CFSG.Open.pRank r (⊤ : Subgroup ↥(mcOf T)) ≤ 2 :=
    (CFSG.SectionRank.isStronglyQuasithin_iff.mp hSQ) r hr hr2
  have hRp : IsPGroup 2 (CFSG.Open.pCore 2 ↥(mcOf T)) :=
    CFSG.LieType.BorelTits.pCore_isPGroup 2
  have := CFSG.SectionRank.pRank_quotient_two_group (CFSG.Open.pCore 2 ↥(mcOf T)) hRp hr hr2
  exact (this.trans_le hrX)

theorem q_pCore_two_quotient_eq_bot (G₁ : Subgroup G) :
    CFSG.Open.pCore 2 (OTwoQuot G₁) = ⊥ := by
  have := pCore_two_quot_eq_bot G₁
  assumption

end Setup

section Fit

variable {G : Type} [Group G] [Finite G] {T M H PQ : Subgroup G} {p : ℕ}

theorem q_solvable_normal_eq_bot (S : Setting146 G T M) (hred : IsRedCE T M H PQ p)
    (hmax : PMaximal T M p) (A : Subgroup (OTwoQuot (mcOf T))) [hAn : A.Normal]
    (hAs : Group.IsSolvable ↥A) (h3 : ∀ x ∈ A, orderOf x ≠ 3)
    (h5 : p = 5 → ∀ x ∈ A, orderOf x ≠ 5) : A = ⊥ := by
  classical
  by_contra hAbot
  have hHG : H ≤ (mcOf T) := S.le_mcOf hred.isHTM
  obtain ⟨N, hNn, hNle, hNbot, hNmin⟩ := CFSG.exists_minimal_normal_le A hAn hAbot
  have : N.Normal := hNn
  have : CFSG.IsMinimalNormal N := ⟨fun K hK hKN => by
    by_cases hKb : K = ⊥
    · exact Or.inl hKb
    · exact Or.inr (hNmin K hK hKN hKb)⟩
  have : Group.IsSolvable ↥N :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hNle)
  obtain ⟨q, hq, hel⟩ := CFSG.minimalNormal_solvable_exists_isElementaryAbelian N
  have : Fact q.Prime := ⟨hq⟩
  have hqg : IsPGroup q ↥N := CFSG.IsElementaryAbelian.isPGroup q ↥N
  obtain ⟨x, hxN, hxq⟩ : ∃ x ∈ N, orderOf x = q := by
    obtain ⟨n, hn⟩ := hqg.exists_card_eq
    have hn0 : n ≠ 0 := by
      rintro rfl
      apply hNbot
      rw [pow_zero] at hn
      exact Subgroup.card_eq_one.mp hn
    have hdvd : q ∣ Nat.card N := by rw [hn]; exact dvd_pow_self q hn0
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥N) q hdvd
    exact ⟨y, y.2, by rw [← hy, Subgroup.orderOf_coe]⟩
  have hq3 : q ≠ 3 := fun h => h3 x (hNle hxN) (hxq.trans h)
  have hq5 : p = 5 → q ≠ 5 := fun hp h => h5 hp x (hNle hxN) (hxq.trans h)
  have hq2 : q ≠ 2 := by
    rintro rfl
    have hle : N ≤ CFSG.Open.pCore 2 (OTwoQuot (mcOf T)) := le_pCore 2 hNn hqg
    rw [q_pCore_two_quotient_eq_bot (mcOf T), le_bot_iff] at hle
    exact hNbot hle
  set Ñ : Subgroup G := (N.comap (qPi (mcOf T))).map (mcOf T).subtype with hÑ
  have hRp : IsPGroup 2 (CFSG.Open.pCore 2 ↥(mcOf T)) := CFSG.LieType.BorelTits.pCore_isPGroup 2
  have hÑs : Group.IsSolvable ↥Ñ := by
    have h1 : Group.IsSolvable ↥(N.comap (qPi (mcOf T))) :=
      isSolvable_comap_quotient _ hRp inferInstance
    exact Group.isSolvable_of_surjective
      (f := ((N.comap (qPi (mcOf T))).equivMapOfInjective (mcOf T).subtype
        (mcOf T).subtype_injective).toMonoidHom)
      ((N.comap (qPi (mcOf T))).equivMapOfInjective (mcOf T).subtype
        (mcOf T).subtype_injective).surjective
  have hÑn : (mcOf T) ≤ Subgroup.normalizer (Ñ : Set G) := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.map_subtype_le _)).mp ?_
    have : Ñ.subgroupOf (mcOf T) = N.comap (qPi (mcOf T)) :=
      Subgroup.comap_map_eq_self_of_injective (mcOf T).subtype_injective _
    rw [this]
    exact Subgroup.Normal.comap hNn _
  have hHs : Group.IsSolvable ↥H := hred.isSolvable S
  have hHp : Group.IsSolvable ↥(H ⊔ Ñ) := isSolvable_sup_of_normalizes (hHG.trans hÑn) hHs hÑs
  have hHHp : H ≤ H ⊔ Ñ := le_sup_left
  have hHpM : H ⊔ Ñ ≤ mcOf T := sup_le hHG (Subgroup.map_subtype_le _)
  have hdvd : q ∣ Nat.card ↥(H ⊔ Ñ) := by
    have h1 : Nat.card N ∣ Nat.card ↥(N.comap (qPi (mcOf T))) := card_dvd_comap_quotient _ N
    have h2 : Nat.card ↥(N.comap (qPi (mcOf T))) = Nat.card ↥Ñ :=
      Nat.card_congr ((N.comap (qPi (mcOf T))).equivMapOfInjective (mcOf T).subtype
        (mcOf T).subtype_injective).toEquiv
    have h3' : Nat.card ↥Ñ ∣ Nat.card ↥(H ⊔ Ñ) := Subgroup.card_dvd_of_le le_sup_right
    have hqN : q ∣ Nat.card N := by
      obtain ⟨n, hn⟩ := hqg.exists_card_eq
      have hn0 : n ≠ 0 := by
        rintro rfl
        apply hNbot
        rw [pow_zero] at hn
        exact Subgroup.card_eq_one.mp hn
      rw [hn]
      exact dvd_pow_self q hn0
    exact hqN.trans (h1.trans (h2 ▸ h3'.trans dvd_rfl))
  have hsolv := input14614Solv_proved G T M S H PQ p hred hmax (H ⊔ Ñ) hHHp hHpM hHp
  rcases S.p_eq_three_or_five_of_isRedCE hred with hp | hp
  · rcases hsolv.1 hp q hq hdvd with h | h
    · exact hq2 h
    · exact hq3 h
  · rcases hsolv.2 hp q hq hdvd with h | h | h
    · exact hq2 h
    · exact hq3 h
    · exact hq5 hp h

theorem q_suzuki_of_not_three_dvd {Q : Type} [Group Q] [Finite Q] (hlist : SQTKList3Dvd)
    {J : Subgroup Q} (hA : A36StrongCat J) (h3 : ¬ 3 ∣ Nat.card J) :
    ∃ f : ℕ, Odd f ∧ 3 ≤ f ∧ CFSG.Blueprint.SuzukiModel ↥J 2 f := by
  rcases hA.1 with ⟨hc, hsimp, hlistJ⟩ | ⟨hc, hZ3, -⟩ | h3' | h4
  · exact hlist ↥J hlistJ h3
  · exfalso
    exact h3 (hZ3 ▸ Subgroup.card_subgroup_dvd_card (Subgroup.center ↥J))
  · exfalso
    obtain ⟨p, hp, hp3, -, hel, ψdata⟩ := h3'
    obtain ⟨-, ψ, hψs, -, -⟩ := ψdata
    exact h3 ((three_dvd_card_sl_two p hp.one_lt).trans (Subgroup.card_dvd_of_surjective hψs))
  · exfalso
    obtain ⟨-, -, ⟨eSL⟩, hF⟩ := h4
    have h1 : 3 ∣ Nat.card (↥J ⧸ CFSG.fittingSubgroup ↥J) := by
      rw [Nat.card_congr eSL.toEquiv]
      exact three_dvd_card_sl_two 5 (by norm_num)
    exact h3 (h1.trans (Subgroup.card_quotient_dvd_card _))

theorem q_normal_eq_bot (h36 : A36ForSQTK) (hlist : SQTKList3Dvd) (iS : Input14614NoSz)
    (S : Setting146 G T M) (hred : IsRedCE T M H PQ p) (hmax : PMaximal T M p)
    (C : Subgroup (OTwoQuot (mcOf T))) [hCn : C.Normal] (h3 : ∀ x ∈ C, orderOf x ≠ 3)
    (h5 : p = 5 → ∀ x ∈ C, orderOf x ≠ 5) : C = ⊥ := by
  classical
  by_cases hsolv : Group.IsSolvable ↥C
  · exact q_solvable_normal_eq_bot S hred hmax C hsolv h3 h5
  · exfalso
    obtain ⟨J, hJ, hJC⟩ := exists_cComp_le_of_not_solvable (H := (⊤ : Subgroup (OTwoQuot (mcOf T))))
      (X := C) le_top inferInstance hsolv
    have hA : A36StrongCat J := h36 _ S.sqtkHyp_quotient J hJ
    have h3J : ¬ 3 ∣ Nat.card J := by
      intro hd
      obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥J) 3 hd
      exact h3 (y : OTwoQuot (mcOf T)) (hJC y.2) (by rw [Subgroup.orderOf_coe]; exact hy)
    obtain ⟨f, -, -, hf⟩ := q_suzuki_of_not_three_dvd hlist hA h3J
    exact q_no_suzuki_component (iS G T M S H PQ p hred hmax) hJ hf

theorem q_centralizer_eq_bot (h36 : A36ForSQTK) (hlist : SQTKList3Dvd) (iS : Input14614NoSz)
    (S : Setting146 G T M) (hred : IsRedCE T M H PQ p) (hmax : PMaximal T M p)
    (N : Subgroup (OTwoQuot (mcOf T))) [hNn : N.Normal]
    (hZ : ∀ n ∈ N, (∀ m ∈ N, n * m = m * n) → n = 1)
    (hE3 : ∃ E : Subgroup (OTwoQuot (mcOf T)), E ≤ N ∧ IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 2)
    (hE5 : p = 5 → ∃ E : Subgroup (OTwoQuot (mcOf T)), E ≤ N ∧ IsElemAbelian 5 E ∧
      Nat.card E = 5 ^ 2) :
    Subgroup.centralizer (N : Set (OTwoQuot (mcOf T))) = ⊥ := by
  classical
  have key : ∀ (r : ℕ) [Fact r.Prime], r ≠ 2 → ∀ E : Subgroup (OTwoQuot (mcOf T)), E ≤ N →
      IsElemAbelian r E → Nat.card E = r ^ 2 →
      ∀ x ∈ Subgroup.centralizer (N : Set (OTwoQuot (mcOf T))), orderOf x ≠ r := by
    intro r _ hr2 E hEN hE hEc x hx hxr
    have hxE : x ∈ E := zmEq_of_orderOf_centralizes
      (S.pRank_quotient_le_two (Fact.out) hr2) hE hEc hxr
      fun e he => (Subgroup.mem_centralizer_iff.mp hx e (hEN he)).symm ▸ rfl
    have hx1 : x = 1 := hZ x (hEN hxE) fun m hm => (Subgroup.mem_centralizer_iff.mp hx m hm).symm
    rw [hx1, orderOf_one] at hxr
    exact absurd hxr.symm (Fact.out : r.Prime).one_lt.ne'
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨E3, hE3N, hE3a, hE3c⟩ := hE3
  refine q_normal_eq_bot h36 hlist iS S hred hmax _ (fun x hx => ?_) (fun hp x hx => ?_)
  · exact key 3 (by norm_num) E3 hE3N hE3a hE3c x hx
  · have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    obtain ⟨E5, hE5N, hE5a, hE5c⟩ := hE5 hp
    exact key 5 (by norm_num) E5 hE5N hE5a hE5c x hx

end Fit

end CFSG.Quasithin
