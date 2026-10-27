module

public import CFSG.Quasithin.EmptyFaithful.Insp9Cases10
public import CFSG.Quasithin.Background.F6CatRecogTools3
public import CFSG.Quasithin.EmptyFaithful.Insp9Cases7

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.InternalSec
open scoped commutatorElement

namespace Insp9

theorem B56Setting.normal_quasisimple_cases₂ {D : Type} [Group D] [Finite D] {N K : Subgroup D}
    (hs : B56Setting D N) (hKN : K ≤ N) (hKn : ∀ x ∈ N, ∀ k ∈ K, x * k * x⁻¹ ∈ K)
    (hKq : CFSG.IsQuasisimple ↥K) (h8 : ¬ 2 ^ 8 ∣ Nat.card ↥N) :
    (B56QuasisimpleList ↥K ∧ (N = K ∨ (∃ n : ℕ, 5 ≤ n ∧ n ≤ 8 ∧ Nat.card ↥N ∣ n.factorial) ∨
        (Nat.card ↥N ∣ 12096 ∧ ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ∧
          ∃ π : ↥(quasithinG2 F) →* ↥N, Function.Surjective π))) ∨
      (∃ c ∈ flOrders, Nat.card ↥K ∣ c) ∨ Nat.card ↥K ∣ 360 ∨ Nat.card ↥K ∣ 168 ∨
      ∃ c : ℕ, Nat.card ↥K ∣ c ∧ 168 * c ∣ Nat.card ↥N := by
  obtain ⟨W, _, _, _, ρ, hρ, -, hcases⟩ := hs
  have eK : ↥K ≃* ↥(K.map ρ) := Subgroup.equivMapOfInjective K ρ hρ
  have hKJ : K.map ρ ≤ N.map ρ := Subgroup.map_mono hKN
  have hn : ∀ x ∈ N.map ρ, ∀ k ∈ K.map ρ, x * k * x⁻¹ ∈ K.map ρ := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨k, hk, rfl⟩
    exact ⟨x * k * x⁻¹, hKn x hx k hk, by simp⟩
  have hq' : CFSG.IsQuasisimple ↥(K.map ρ) := CFSG.LocalCores.isQuasisimple_of_mulEquiv eK hKq
  have hcK : Nat.card ↥(K.map ρ) = Nat.card ↥K := Subgroup.card_map_of_injective hρ
  have hcN : Nat.card ↥(N.map ρ) = Nat.card ↥N := Subgroup.card_map_of_injective hρ
  have h8' : ¬ 2 ^ 8 ∣ Nat.card ↥(N.map ρ) := by rw [hcN]; exact h8
  have hle8 : ∀ {X : Subgroup (MulAut W)}, X ≤ N.map ρ → ¬ 2 ^ 8 ∣ Nat.card ↥X :=
    fun hX hd => h8' (hd.trans (Subgroup.card_dvd_of_le hX))
  rcases hcases with h1 | ⟨⟨e⟩, -⟩ | ⟨G₁, G₂, hsup, hinf, hc, hf₁, hf₂, -⟩ |
      ⟨G₁, G₂, t, hJt, -, hc, ⟨e₁⟩, hc₂, -, -, -, -, -, ht₁, ht₂, -⟩ |
      ⟨G₁, G₂, hsup, hinf, hc, -, ⟨e₁⟩, -, -, -⟩
  ·
    have hE : quasithinGenFitting (N.map ρ) = K.map ρ := eq_of_le_quasisimple hKJ hn hq' h1.1
    have hQL := h1.2.2
    have hB51 := h1.2.1
    rw [hE] at hQL hB51
    left
    refine ⟨b56QL_of_mulEquiv eK hQL, ?_⟩
    have hNK : N.map ρ = K.map ρ → N = K := fun h => Subgroup.map_injective hρ h
    rcases hB51.1.2 with hi | hii | ⟨n, hiii⟩ | hiv
    · obtain ⟨S, hS⟩ := B5.exists_isSylowTwoOf (N.map ρ)
      rcases hi.2.2 S hS with hJ | ⟨-, hsym | hg2⟩
      · exact Or.inl (hNK hJ)
      · obtain ⟨n, hn5, hn8, π, hπ, -⟩ := hsym
        refine Or.inr (Or.inl ⟨n, hn5, hn8, ?_⟩)
        have h1 := Subgroup.card_dvd_of_surjective hπ
        rw [hcN] at h1
        have h2 : Nat.card (Equiv.Perm (Fin n)) = n.factorial := by
          rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
        have h1' : Nat.card ↥N ∣ Nat.card (Equiv.Perm (Fin n)) := h1
        rw [h2] at h1'
        exact h1'
      · obtain ⟨F, _, _, hF, π, hπ, -⟩ := hg2
        have hF2 : Nat.card F = 2 := by simpa using hF
        refine Or.inr (Or.inr ⟨?_, F, inferInstance, inferInstance, hF2, ?_⟩)
        · have h1 := Subgroup.card_dvd_of_surjective hπ
          rw [hcN] at h1
          have h2 : Nat.card ↥(quasithinG2 F) = 12096 := by
            rw [card_quasithinG2_1527d hF, hF]
            norm_num
          have h1' : Nat.card ↥N ∣ Nat.card ↥(quasithinG2 F) := h1
          rw [h2] at h1'
          exact h1'
        · let π₀ : ↥(quasithinG2 F) →* ↥(N.map ρ) := π
          exact ⟨((Subgroup.equivMapOfInjective N ρ hρ).symm.toMonoidHom).comp π₀,
            (Subgroup.equivMapOfInjective N ρ hρ).symm.surjective.comp hπ⟩
    · exact Or.inl (hNK hii.1)
    · exact Or.inl (hNK hiii.1)
    · exact Or.inl (hNK hiv.1)
  · exact (not_le_perm_three hq' hKJ e).elim
  ·
    have h₁J : G₁ ≤ N.map ρ := by rw [← hsup]; exact le_sup_left
    have h₂J : G₂ ≤ N.map ρ := by rw [← hsup]; exact le_sup_right
    rcases le_or_le_of_sup_eq hsup hc hKJ hn hq' with h | h
    · have hfin₁ : Finite ↥G₁ := Finite.of_injective (Subgroup.inclusion h₁J)
        (Subgroup.inclusion_injective h₁J)
      rw [← hcK]
      exact Or.inr (Or.inl ⟨_, b56FL_card_le7 hf₁ (hle8 h₁J), Subgroup.card_dvd_of_le h⟩)
    · have hfin₂ : Finite ↥G₂ := Finite.of_injective (Subgroup.inclusion h₂J)
        (Subgroup.inclusion_injective h₂J)
      rw [← hcK]
      exact Or.inr (Or.inl ⟨_, b56FL_card_le7 hf₂ (hle8 h₂J), Subgroup.card_dvd_of_le h⟩)
  ·
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    rcases le_or_le_of_sup_zpowers hJt hc ht₁ ht₂ hKJ hn hq' with h | h
    · have hG1 : Nat.card ↥G₁ = 360 := by
        rw [Nat.card_congr e₁.toEquiv, card_alternatingGroup1527d 6 (by norm_num)]
        simp [Nat.factorial]
      rw [← hcK]
      exact Or.inr (Or.inr (Or.inl ((Subgroup.card_dvd_of_le h).trans hG1.dvd)))
    · exact (not_le_of_card_prime hq' h hc₂).elim
  ·
    have hG1 : Nat.card ↥G₁ = 168 := by
      rw [Nat.card_congr e₁.toEquiv, card_statedSL_three1527d, Nat.card_zmod]
      norm_num
    rcases le_or_le_of_sup_eq hsup hc hKJ hn hq' with h | h
    · rw [← hcK]
      exact Or.inr (Or.inr (Or.inr (Or.inl ((Subgroup.card_dvd_of_le h).trans hG1.dvd))))
    · rw [← hcK]
      refine Or.inr (Or.inr (Or.inr (Or.inr ⟨Nat.card ↥G₂, Subgroup.card_dvd_of_le h, ?_⟩)))
      have hprod := card_sup_eq_mul hc hinf
      rw [hsup, hG1] at hprod
      rw [← hcN, hprod]

section Case8

variable {D : Type} [Group D] [Finite D] {D₁ D₂ J N : Subgroup D}

theorem case8_s6 (h : Data D₁ D₂ J N) (hs : B56Setting D N) (e : D ≃* Equiv.Perm (Fin 6)) :
    InspGoal D N := by
  have hA : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  let K : Subgroup D := (alternatingGroup (Fin 6)).map e.symm.toMonoidHom
  have hKn : K.Normal := Subgroup.Normal.map inferInstance _ e.symm.surjective
  let eK : ↥(alternatingGroup (Fin 6)) ≃* ↥K :=
    Subgroup.equivMapOfInjective _ e.symm.toMonoidHom e.symm.injective
  have hsK : IsSimpleGroup ↥K := eK.symm.isSimpleGroup
  have hnc : ∃ a b : ↥K, a * b ≠ b * a := by
    by_contra hcomm
    push Not at hcomm
    have : IsMulCommutative ↥K := ⟨⟨fun a b => hcomm a b⟩⟩
    have hq : (Nat.card ↥K).Prime := IsSimpleGroup.prime_card
    rw [Nat.card_congr eK.symm.toEquiv, card_alternatingGroup1527d 6 (by norm_num)] at hq
    norm_num [Nat.factorial] at hq
  have hKq : CFSG.IsQuasisimple ↥K := (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnc).1
  have hZ : Nat.card ↥(Subgroup.center ↥K) ∣ 3 := by
    rw [CFSG.LocalAnalysis.ComponentInitial.center_eq_bot_of_isSimpleGroup hnc, Subgroup.card_bot]
    exact one_dvd _
  have hK2 : K.index = 2 := by
    rw [Subgroup.index_map_of_bijective e.symm.bijective, alternatingGroup.index_eq_two]
  rcases h.le_or_card_dvd_six hKq hK2.dvd hZ with hKN | hsmall
  · have hrel : K.relIndex N * N.index = K.index := Subgroup.relIndex_mul_index hKN
    have hN1 : N.index ∣ 2 := ⟨K.relIndex N, by rw [← hK2, ← hrel]; ring⟩
    rcases (Nat.dvd_prime Nat.prime_two).mp hN1 with h1 | h2
    · have hN : N = ⊤ := Subgroup.index_eq_one.mp h1
      right
      refine ⟨?_, by rw [hN]; exact le_top⟩
      exact Or.inr (Or.inr (Or.inl ⟨(topEquivOfEq hN).trans e⟩))
    · have hrel1 : K.relIndex N = 1 := by rw [h2, hK2] at hrel; omega
      have hNK : N ≤ K := Subgroup.relIndex_eq_one.mp hrel1
      have hNKeq : N = K := le_antisymm hNK hKN
      right
      refine ⟨Or.inr (Or.inl ⟨(MulEquiv.subgroupCongr hNKeq).trans eK.symm⟩), ?_⟩
      rw [hNKeq]
      refine oTwoUpper_le_of_pow_mem (fun x _ => ⟨1, ?_⟩)
      have := Subgroup.pow_index_mem K x
      rw [hK2] at this
      simpa using this
  · left
    exact hs.s3_of_small (card_small_of_dvd_six hsmall).1 (card_small_of_dvd_six hsmall).2

theorem case8_hat6 (h : Data D₁ D₂ J N) (hs : B56Setting D N) (hH : F6.IsHatSym 6 D)
    (hT : Nat.card ↥(D₁ ⊓ D₂) = 2 ^ 4) : InspGoal D N := by
  obtain ⟨φ, hφ, -, hQ⟩ := hH
  set K : Subgroup D := (alternatingGroup (Fin 6)).comap φ with hKdef
  have hKn : K.Normal := inferInstance
  have hKq : CFSG.IsQuasisimple ↥K := isQuasisimple_of_open hQ.1
  have hZ : Nat.card ↥(Subgroup.center ↥K) ∣ 3 := by rw [hQ.2.1]
  have hK2 : K.index = 2 := by
    rw [hKdef, Subgroup.index_comap_of_surjective _ hφ, alternatingGroup.index_eq_two]
  rcases h.le_or_card_dvd_six hKq hK2.dvd hZ with hKN | hsmall
  · have hKcard : Nat.card ↥K = 1080 := by
      rw [card_hatAlt hQ (by norm_num)]
      simp [Nat.factorial]
    have hrel : K.relIndex N * N.index = K.index := Subgroup.relIndex_mul_index hKN
    have hN1 : N.index ∣ 2 := ⟨K.relIndex N, by rw [← hK2, ← hrel]; ring⟩
    rcases (Nat.dvd_prime Nat.prime_two).mp hN1 with h1 | h2
    ·
      exfalso
      have hN : N = ⊤ := Subgroup.index_eq_one.mp h1
      have hNcard : Nat.card ↥N = 2160 := by
        rw [Nat.card_congr (topEquivOfEq hN).toEquiv]
        have := Subgroup.card_mul_index K
        rw [hKcard, hK2] at this
        omega
      have h5 : ¬ 2 ^ 5 ∣ Nat.card D := h.not_two_pow_dvd hT (m := 5) (by norm_num)
      have h5N : ¬ 2 ^ 5 ∣ Nat.card ↥N := fun hd =>
        h5 (hd.trans (Subgroup.card_subgroup_dvd_card N))
      have h8N : ¬ 2 ^ 8 ∣ Nat.card ↥N := fun hd =>
        h5N ((Nat.pow_dvd_pow 2 (by norm_num : 5 ≤ 8)).trans hd)
      have hKn' : ∀ x ∈ N, ∀ k ∈ K, x * k * x⁻¹ ∈ K := fun x _ k hk => hKn.conj_mem k hk x
      have keyFL : ∀ c ∈ flOrders, 1080 ∣ c → False := by
        unfold flOrders; decide +kernel
      rcases hs.normal_quasisimple_cases₂ hKN hKn' hKq h8N with
        ⟨-, hNK | ⟨n, hn5, hn8, hdvd⟩ | ⟨hd, -⟩⟩ | ⟨c, hc, hdc⟩ | hd | hd | ⟨c, hdc, hcN⟩
      · have : N.index = 2 := by rw [hNK]; exact hK2
        omega
      · rw [hNcard] at hdvd
        interval_cases n <;> norm_num [Nat.factorial] at hdvd
      · rw [hNcard] at hd
        omega
      · rw [hKcard] at hdc
        exact keyFL c hc hdc
      · rw [hKcard] at hd
        omega
      · rw [hKcard] at hd
        omega
      · rw [hKcard] at hdc
        have h1 : 8 ∣ c := (show 8 ∣ 1080 by norm_num).trans hdc
        have h2 : 168 * 8 ∣ 168 * c := Nat.mul_dvd_mul_left 168 h1
        exact h5N ((show 2 ^ 5 ∣ 168 * 8 by norm_num).trans (h2.trans hcN))
    · have hrel1 : K.relIndex N = 1 := by rw [h2, hK2] at hrel; omega
      have hNK : N ≤ K := Subgroup.relIndex_eq_one.mp hrel1
      have hNKeq : N = K := le_antisymm hNK hKN
      right
      refine ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        (isHatAlt_of_mulEquiv (MulEquiv.subgroupCongr hNKeq.symm) hQ)))))), ?_⟩
      rw [hNKeq]
      refine oTwoUpper_le_of_pow_mem (fun x _ => ⟨1, ?_⟩)
      have := Subgroup.pow_index_mem K x
      rw [hK2] at this
      simpa using this
  · left
    exact hs.s3_of_small (card_small_of_dvd_six hsmall).1 (card_small_of_dvd_six hsmall).2

theorem inspCase8 :
    InspCase fun {_} _ H₁ H₂ => F6.IsF618CaseEightCat H₁ H₂ := by
  intro D _ _ D₁ D₂ J N h hs hP
  have key : ∀ H₁ H₂ : Subgroup D, H₁ ⊓ H₂ = D₁ ⊓ D₂ → F6.IsF618CaseEightCat H₁ H₂ →
      InspGoal D N := by
    intro H₁ H₂ hHH hc
    obtain ⟨hD, ⟨eT⟩, -⟩ := hc
    have hT : Nat.card ↥(D₁ ⊓ D₂) = 2 ^ 4 := by
      rw [← hHH, Nat.card_congr eT.toEquiv, Nat.card_prod, DihedralGroup.nat_card]
      simp
    rcases hD with hH | ⟨p, hp, hmod, hL2⟩
    · exact case8_hat6 h hs hH hT
    · obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hL2
      by_cases hp3 : p = 3
      · subst hp3
        have hK9 : Nat.card K = 9 := by rw [hK]; norm_num
        obtain ⟨e6⟩ := F6.nonempty_pSigmaL2_mulEquiv_perm_six K hK9
        exact case8_s6 h hs (e.trans e6)
      · have := hp.two_le
        exact case9_psigma h hs hp (by omega) K hK e hT
  rcases hP with hP | hP
  · exact key D₁ D₂ rfl hP
  · exact key D₂ D₁ (inf_comm _ _) hP

end Case8

section GraphExt

theorem exists_index_two_isSLEps3 {D : Type} [Group D] {p : ℕ} (h : F6.IsSLEps3GraphExt p D) :
    ∃ Kq : Subgroup D, Kq.index = 2 ∧ F6.IsSLEps3 p ↥Kq := by
  obtain ⟨hp, F, _, _, h1 | h3⟩ := h
  · obtain ⟨hmod, hF, hext | hext⟩ := h1
    · obtain ⟨M, e, t, g, hidx, -, -⟩ := hext
      refine ⟨M, hidx, hp, F, inferInstance, inferInstance, Or.inl ⟨hmod, hF, Or.inl ⟨?_⟩⟩⟩
      exact e.trans ((QuotientGroup.quotientMulEquivOfEq (Subgroup.bot_subgroupOf _)).trans
        QuotientGroup.quotientBot)
    · obtain ⟨M, e, t, g, hidx, -, -⟩ := hext
      exact ⟨M, hidx, hp, F, inferInstance, inferInstance, Or.inl ⟨hmod, hF, Or.inr ⟨e⟩⟩⟩
  · obtain ⟨hmod, hF, hext | hext⟩ := h3
    · obtain ⟨M, e, t, g, hidx, -, -⟩ := hext
      refine ⟨M, hidx, hp, F, inferInstance, inferInstance, Or.inr ⟨hmod, hF, Or.inl ⟨?_⟩⟩⟩
      exact e.trans ((QuotientGroup.quotientMulEquivOfEq (Subgroup.bot_subgroupOf _)).trans
        QuotientGroup.quotientBot)
    · obtain ⟨M, e, t, g, hidx, -, -⟩ := hext
      exact ⟨M, hidx, hp, F, inferInstance, inferInstance, Or.inr ⟨hmod, hF, Or.inr ⟨e⟩⟩⟩

theorem center_eq_bot_of_simple_of_qs {X : Type} [Group X] [IsSimpleGroup X]
    (hq : CFSG.IsQuasisimple X) : Subgroup.center X = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h | h
  · exact h
  · exfalso
    have := hq.2.1.toNontrivial
    obtain ⟨x, y, hxy⟩ := exists_pair_ne (X ⧸ Subgroup.center X)
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
    exact hxy (QuotientGroup.eq.mpr (by rw [h]; trivial))

theorem card_center_congr {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) :
    Nat.card ↥(Subgroup.center X) = Nat.card ↥(Subgroup.center Y) := by
  rw [← map_center_mulEquiv e, Subgroup.card_map_of_injective e.injective]

theorem isSimpleGroup_statedProj_statedSL_three (K : Type) [Field K] [Finite K] :
    IsSimpleGroup (CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSL 3 K)) := by
  obtain ⟨-, hs, -⟩ := CFSG.LinearGroups.linear_projective_simple (K := K) (n := 3)
    (by norm_num) (Or.inl le_rfl)
  exact (projectiveSpecialLinearGroupEquivStatedProj 3 K).symm.isSimpleGroup

theorem isSimpleGroup_statedProj_statedSU_three {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (K : Type)
    [Field K] [Finite K] (hK : Nat.card K = p ^ 2) :
    IsSimpleGroup (CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSU 3 p K)) := by
  have : Fact p.Prime := ⟨hp⟩
  have h1 := CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU K p 1
    (by simpa using hK) 3 le_rfl (by intro h; simp at h; omega)
  rw [pow_one] at h1
  exact h1

theorem card_statedProj_statedSU_three {p : ℕ} (hp : p.Prime) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = p ^ 2) :
    Nat.card (CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSU 3 p K)) =
      p ^ 3 * ((p ^ 2 - 1) * (p ^ 3 + 1)) / Nat.gcd 3 (p + 1) := by
  have h := CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSU (K := K) (p := p) (f := 1)
    (n := 3) hp le_rfl (by simpa using hK) (by norm_num)
  simp only [pow_one] at h
  have e2 : ((((p : ℕ) : ℤ) ^ 2 - (-1) ^ 2).toNat) = p ^ 2 - 1 := by
    have : (1 : ℕ) ≤ p ^ 2 := Nat.one_le_pow _ _ hp.pos
    rw [show ((-1 : ℤ)) ^ 2 = 1 by norm_num, show (((p : ℕ) : ℤ) ^ 2 - 1) =
      (((p ^ 2 - 1 : ℕ)) : ℤ) by push_cast [this]; ring, Int.toNat_natCast]
  have e3 : ((((p : ℕ) : ℤ) ^ 3 - (-1) ^ 3).toNat) = p ^ 3 + 1 := by
    rw [show ((-1 : ℤ)) ^ 3 = -1 by norm_num, show (((p : ℕ) : ℤ) ^ 3 - -1) =
      ((p ^ 3 + 1 : ℕ) : ℤ) by push_cast; ring, Int.toNat_natCast]
  rw [h, show 3 * (3 - 1) / 2 = 3 from rfl, show Finset.Icc 2 3 = ({2, 3} : Finset ℕ) by decide,
    Finset.prod_pair (by norm_num), e2, e3]

theorem card_center_statedSU_dvd_three {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (F : Type) [Field F]
    [Finite F] (hF : Nat.card F = p ^ 2) :
    Nat.card ↥(Subgroup.center ↥(CFSG.Assembly.LowTwoRank.StatedSU 3 p F)) ∣ 3 := by
  have : Fact p.Prime := ⟨hp⟩
  have hq := CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card (F := F) (p := p)
    (f := 1) (n := 3) (by simpa using hF) le_rfl (by intro h; simp at h; omega)
  have hcen := hq.2
  rw [pow_one] at hcen
  have hc := Subgroup.card_eq_card_quotient_mul_card_subgroup
    ((CFSG.Assembly.LowTwoRank.StatedScalars (Fin 3) F).subgroupOf
      (CFSG.Assembly.LowTwoRank.StatedSU 3 p F))
  have hP : Nat.card (CFSG.Assembly.LowTwoRank.StatedProj
      (CFSG.Assembly.LowTwoRank.StatedSU 3 p F)) = Nat.card (↥(CFSG.Assembly.LowTwoRank.StatedSU 3 p F) ⧸
      (CFSG.Assembly.LowTwoRank.StatedScalars (Fin 3) F).subgroupOf
        (CFSG.Assembly.LowTwoRank.StatedSU 3 p F)) := rfl
  have hPcard := card_statedProj_statedSU_three hp F hF
  have hX : Nat.card ↥(CFSG.Assembly.LowTwoRank.StatedSU 3 p F) =
      p ^ 3 * ((p ^ 2 - 1) * (p ^ 3 + 1)) := by
    have hCharP : CharP F p := by
      have : Fintype F := Fintype.ofFinite F
      exact charP_of_card_eq_prime_pow (f := 2) (by rw [← Nat.card_eq_fintype_card, hF])
    have h1 := CFSG.SectionRank.OddCover.card_statedSU_three (K := F) (p := p) (f := 1)
      (by simpa using hF)
    rw [pow_one] at h1
    rw [h1]
    ring
  rw [hcen]
  set Y := p ^ 3 * ((p ^ 2 - 1) * (p ^ 3 + 1)) with hY
  set g := Nat.gcd 3 (p + 1) with hg
  have hgY : g ∣ Y := by
    have h1 : g ∣ p ^ 3 + 1 := by
      refine (Nat.gcd_dvd_right 3 (p + 1)).trans ?_
      simpa using Odd.nat_add_dvd_pow_add_pow p 1 (by decide : Odd 3)
    exact Dvd.dvd.mul_left (Dvd.dvd.mul_left h1 _) _
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left _ (by norm_num)
  have hPpos : 0 < Y / g := by
    apply Nat.div_pos (Nat.le_of_dvd _ hgY) hgpos
    have : 0 < p ^ 3 := pow_pos hp.pos 3
    have : 0 < p ^ 2 - 1 := by
      have : 9 ≤ p ^ 2 := by nlinarith
      omega
    have : 0 < p ^ 3 + 1 := by omega
    positivity
  have hmul : Y = (Y / g) * Nat.card ↥((CFSG.Assembly.LowTwoRank.StatedScalars (Fin 3) F).subgroupOf
      (CFSG.Assembly.LowTwoRank.StatedSU 3 p F)) := by
    have h1 : Y = Nat.card (↥(CFSG.Assembly.LowTwoRank.StatedSU 3 p F) ⧸
        (CFSG.Assembly.LowTwoRank.StatedScalars (Fin 3) F).subgroupOf
          (CFSG.Assembly.LowTwoRank.StatedSU 3 p F)) *
        Nat.card ↥((CFSG.Assembly.LowTwoRank.StatedScalars (Fin 3) F).subgroupOf
          (CFSG.Assembly.LowTwoRank.StatedSU 3 p F)) := by
      rw [← hX]
      exact hc
    have h2 : Nat.card (↥(CFSG.Assembly.LowTwoRank.StatedSU 3 p F) ⧸
        (CFSG.Assembly.LowTwoRank.StatedScalars (Fin 3) F).subgroupOf
          (CFSG.Assembly.LowTwoRank.StatedSU 3 p F)) = Y / g := by
      rw [← hP]
      exact hPcard
    calc Y = _ := h1
      _ = (Y / g) * _ := by rw [h2]
  have hmul2 : Y = (Y / g) * g := (Nat.div_mul_cancel hgY).symm
  have : Nat.card ↥((CFSG.Assembly.LowTwoRank.StatedScalars (Fin 3) F).subgroupOf
      (CFSG.Assembly.LowTwoRank.StatedSU 3 p F)) = g :=
    Nat.eq_of_mul_eq_mul_left hPpos (hmul.symm.trans hmul2)
  rw [this]
  exact Nat.gcd_dvd_left 3 (p + 1)

theorem isSLEps3_center_dvd_three {D : Type} [Group D] [Finite D] {p : ℕ} (h : F6.IsSLEps3 p D) :
    Nat.card ↥(Subgroup.center D) ∣ 3 := by
  have hq := isSLEps3_qs_dvd h
  obtain ⟨hp, K, _, _, h1 | h3⟩ := h
  · obtain ⟨hmod, hK, he | he⟩ := h1
    · obtain ⟨e⟩ := he
      have h2 := Nat.card_congr (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity'
        (R := K) (⟨0, by norm_num⟩ : Fin 3)).toEquiv
      rw [Fintype.card_fin, CFSG.Timmesfeld.ClassicalOrders.card_rootsOfUnity_eq_gcd] at h2
      rw [card_center_congr e,
        card_center_congr (specialLinearGroupEquivStatedSL 3 K).symm, h2]
      exact Nat.gcd_dvd_right _ _
    · obtain ⟨e⟩ := he
      have : IsSimpleGroup (CFSG.Assembly.LowTwoRank.StatedProj
          (CFSG.Assembly.LowTwoRank.StatedSL 3 K)) := isSimpleGroup_statedProj_statedSL_three K
      have : IsSimpleGroup D := e.isSimpleGroup
      rw [center_eq_bot_of_simple_of_qs hq.1, Subgroup.card_bot]
      exact one_dvd _
  · have hp3 : 3 ≤ p := by have := hp.two_le; omega
    obtain ⟨hmod, hK, he | he⟩ := h3
    · obtain ⟨e⟩ := he
      rw [card_center_congr e]
      exact card_center_statedSU_dvd_three hp hp3 K hK
    · obtain ⟨e⟩ := he
      have : IsSimpleGroup (CFSG.Assembly.LowTwoRank.StatedProj
          (CFSG.Assembly.LowTwoRank.StatedSU 3 p K)) :=
        isSimpleGroup_statedProj_statedSU_three hp hp3 K hK
      have : IsSimpleGroup D := e.isSimpleGroup
      rw [center_eq_bot_of_simple_of_qs hq.1, Subgroup.card_bot]
      exact one_dvd _

end GraphExt

section Case11

variable {D : Type} [Group D] [Finite D] {D₁ D₂ J N : Subgroup D}

theorem card_isSLEps3_three {X : Type} [Group X] [Finite X] (h : F6.IsSLEps3 3 X) :
    Nat.card X = 6048 := by
  obtain ⟨hp, K, _, _, h1 | h3⟩ := h
  · obtain ⟨hmod, -⟩ := h1
    omega
  · obtain ⟨hmod, hK, he | he⟩ := h3
    · obtain ⟨e⟩ := he
      rw [Nat.card_congr e.toEquiv]
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      rw [CFSG.SectionRank.OddCover.card_statedSU_three_eq_mul hK]
      norm_num
    · obtain ⟨e⟩ := he
      rw [Nat.card_congr e.toEquiv, card_statedProj_statedSU_three Nat.prime_three K hK]
      norm_num

theorem isInspList_of_qs (hs : B56Setting D N) (hqN : CFSG.IsQuasisimple ↥N) {p : ℕ}
    (hp : p % 8 = 3 ∨ p % 8 = 5) (hp3 : p ^ 3 ∣ Nat.card ↥N) (h6 : ¬ 2 ^ 6 ∣ Nat.card ↥N) :
    IsInspList ↥N := by
  have hql := hs.ql_of_quasisimple hqN
  have h8 : ¬ 2 ^ 8 ∣ Nat.card ↥N := fun hd =>
    h6 ((Nat.pow_dvd_pow 2 (by norm_num : 6 ≤ 8)).trans hd)
  rcases inspList_or_bad hql h8 with hgood | hbad
  · exact hgood
  · exfalso
    have hp130 : p < 130 := by
      by_contra hcon
      have hle : p ^ 3 ≤ 2097024 := by
        have h1 : p ^ 3 ≤ Nat.card ↥N := Nat.le_of_dvd Nat.card_pos hp3
        have h2 : Nat.card ↥N ≤ 2097024 := by
          revert hbad
          unfold badQL
          rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_insert, Finset.mem_insert,
            Finset.mem_insert, Finset.mem_insert, Finset.mem_insert, Finset.mem_insert,
            Finset.mem_insert, Finset.mem_singleton]
          omega
        omega
      have : 130 ^ 3 ≤ p ^ 3 := Nat.pow_le_pow_left (by omega) 3
      omega
    have hdec : ∀ q ∈ Finset.range 130, (q % 8 = 3 ∨ q % 8 = 5) → ∀ n ∈ badQL,
        q ^ 3 ∣ n → 2 ^ 6 ∣ n := by
      unfold badQL; decide +kernel
    exact h6 (hdec p (Finset.mem_range.mpr hp130) hp _ hbad hp3)

theorem case11_core (h : Data D₁ D₂ J N) (hs : B56Setting D N) {p : ℕ}
    (hp8 : p % 8 = 3 ∨ p % 8 = 5) (hT : Nat.card ↥(D₁ ⊓ D₂) = 2 ^ 6) {K : Subgroup D}
    (hK2 : K.index = 2) (hKS : F6.IsSLEps3 p ↥K) : InspGoal D N := by
  have hKn : K.Normal := Subgroup.normal_of_index_eq_two hK2
  obtain ⟨hKq, hp3K⟩ := isSLEps3_qs_dvd hKS
  have hZ := isSLEps3_center_dvd_three hKS
  rcases h.le_or_card_dvd_six hKq hK2.dvd hZ with hKN | hsmall
  · have h7 : ¬ 2 ^ 7 ∣ Nat.card D := h.not_two_pow_dvd hT (m := 7) (by norm_num)
    have h6D : 2 ^ 6 ∣ Nat.card D := hT ▸ Subgroup.card_subgroup_dvd_card (D₁ ⊓ D₂)
    have hDK : Nat.card ↥K * 2 = Nat.card D := by
      have := Subgroup.card_mul_index K
      rwa [hK2] at this
    have h5K : 2 ^ 5 ∣ Nat.card ↥K := by
      have : 2 ^ 5 * 2 ∣ Nat.card ↥K * 2 := by rw [hDK]; exact h6D
      exact Nat.dvd_of_mul_dvd_mul_right (by norm_num) this
    have h6K : ¬ 2 ^ 6 ∣ Nat.card ↥K := fun hd => h7 (by
      rw [← hDK]
      exact (show 2 ^ 7 = 2 ^ 6 * 2 by norm_num) ▸ Nat.mul_dvd_mul_right hd 2)
    have h7N : ¬ 2 ^ 7 ∣ Nat.card ↥N := fun hd =>
      h7 (hd.trans (Subgroup.card_subgroup_dvd_card N))
    have h8N : ¬ 2 ^ 8 ∣ Nat.card ↥N := fun hd =>
      h7N ((Nat.pow_dvd_pow 2 (by norm_num : 7 ≤ 8)).trans hd)
    have hKn' : ∀ x ∈ N, ∀ k ∈ K, x * k * x⁻¹ ∈ K := fun x _ k hk => hKn.conj_mem k hk x
    have hrel : K.relIndex N * N.index = K.index := Subgroup.relIndex_mul_index hKN
    have hN1 : N.index ∣ 2 := ⟨K.relIndex N, by rw [← hK2, ← hrel]; ring⟩
    have hpK : p ^ 3 ∣ Nat.card ↥K := hp3K
    rcases (Nat.dvd_prime Nat.prime_two).mp hN1 with h1 | h2
    ·
      have hN : N = ⊤ := Subgroup.index_eq_one.mp h1
      have hNcard : Nat.card ↥N = Nat.card ↥K * 2 := by
        rw [Nat.card_congr (topEquivOfEq hN).toEquiv, hDK]
      have keyFL : ∀ q ∈ Finset.range 130, (q % 8 = 3 ∨ q % 8 = 5) →
          ∀ c ∈ flOrders, q ^ 3 ∣ c → False := by
        unfold flOrders; decide +kernel
      have hp130 : ∀ {n : ℕ}, p ^ 3 ∣ n → n ≤ 2097024 → 0 < n → p < 130 := by
        intro n hd hn hn0
        by_contra hcon
        have h1 : p ^ 3 ≤ n := Nat.le_of_dvd hn0 hd
        have : 130 ^ 3 ≤ p ^ 3 := Nat.pow_le_pow_left (by omega) 3
        omega
      rcases hs.normal_quasisimple_cases₂ hKN hKn' hKq h8N with
        ⟨-, hNK | ⟨n, hn5, hn8, hdvd⟩ | ⟨hd12, F, _, _, hF, π, hπ⟩⟩ | ⟨c, hc, hdc⟩ | hd | hd |
          ⟨c, hdc, hcN⟩
      · have : N.index = 2 := by rw [hNK]; exact hK2
        omega
      ·
        exfalso
        have hdN : p ^ 3 ∣ n.factorial := (hpK.trans (hNcard ▸ Dvd.intro _ rfl)).trans hdvd
        have hn40 : n.factorial ≤ 40320 := by
          interval_cases n <;> simp [Nat.factorial]
        have hp40 : p < 40 := by
          by_contra hcon
          have h1 : p ^ 3 ≤ n.factorial := Nat.le_of_dvd (Nat.factorial_pos n) hdN
          have : 40 ^ 3 ≤ p ^ 3 := Nat.pow_le_pow_left (by omega) 3
          omega
        have key : ∀ q ∈ Finset.range 40, (q % 8 = 3 ∨ q % 8 = 5) →
            ∀ m ∈ ({5, 6, 7, 8} : Finset ℕ), q ^ 3 ∣ m.factorial → False := by decide +kernel
        exact key p (Finset.mem_range.mpr hp40) hp8 n (by simp; omega) hdN
      ·
        have hp22 : p < 23 := by
          by_contra hcon
          have h1 : p ^ 3 ∣ 12096 := (hpK.trans (hNcard ▸ Dvd.intro _ rfl)).trans hd12
          have h2 : p ^ 3 ≤ 12096 := Nat.le_of_dvd (by norm_num) h1
          have : 23 ^ 3 ≤ p ^ 3 := Nat.pow_le_pow_left (by omega) 3
          omega
        have hp3 : p = 3 := by
          have h1 : p ^ 3 ∣ 12096 := (hpK.trans (hNcard ▸ Dvd.intro _ rfl)).trans hd12
          have hdec : ∀ q ∈ Finset.range 23, (q % 8 = 3 ∨ q % 8 = 5) → q ^ 3 ∣ 12096 → q = 3 := by
            decide +kernel
          exact hdec p (Finset.mem_range.mpr hp22) hp8 h1
        subst hp3
        have hKc : Nat.card ↥K = 6048 := card_isSLEps3_three hKS
        have hNc : Nat.card ↥N = 12096 := by rw [hNcard, hKc]
        have hF' : Nat.card F = 2 ^ 1 := by rw [pow_one]; exact hF
        have hG2 : Nat.card ↥(quasithinG2 F) = 12096 := by
          rw [card_quasithinG2_1527d hF', hF]
          norm_num
        have hk : Nat.card π.ker = 1 := by
          have := Subgroup.card_ker_mul_card_of_surjective hπ
          rw [hNc, hG2] at this
          omega
        have hinj : Function.Injective π :=
          (MonoidHom.ker_eq_bot_iff π).mp (Subgroup.eq_bot_of_card_eq _ hk)
        have e1 : ↥(quasithinG2 F) ≃* ↥N := MulEquiv.ofBijective π ⟨hinj, hπ⟩
        right
        refine ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨e1.symm.trans
          (g2EquivZMod2 F (by simpa using hF))⟩)))))), by rw [hN]; exact le_top⟩
      · exfalso
        have hb : ∀ m ∈ flOrders, 0 < m ∧ m ≤ 2097024 := by unfold flOrders; decide +kernel
        have hcb := hb c hc
        exact keyFL p (Finset.mem_range.mpr (hp130 (hpK.trans hdc) hcb.2 hcb.1)) hp8 c hc
          (hpK.trans hdc)
      · exfalso
        have key : ∀ q ∈ Finset.range 130, (q % 8 = 3 ∨ q % 8 = 5) → ¬ q ^ 3 ∣ 360 := by
          decide +kernel
        exact key p (Finset.mem_range.mpr (hp130 (hpK.trans hd) (by norm_num) (by norm_num))) hp8
          (hpK.trans hd)
      · exfalso
        have key : ∀ q ∈ Finset.range 130, (q % 8 = 3 ∨ q % 8 = 5) → ¬ q ^ 3 ∣ 168 := by
          decide +kernel
        exact key p (Finset.mem_range.mpr (hp130 (hpK.trans hd) (by norm_num) (by norm_num))) hp8
          (hpK.trans hd)
      · exfalso
        have h1 : 2 ^ 5 ∣ c := h5K.trans hdc
        have h2 : 168 * 2 ^ 5 ∣ 168 * c := Nat.mul_dvd_mul_left 168 h1
        exact h8N ((show 2 ^ 8 ∣ 168 * 2 ^ 5 by norm_num).trans (h2.trans hcN))
    ·
      have hrel1 : K.relIndex N = 1 := by rw [h2, hK2] at hrel; omega
      have hNK : N ≤ K := Subgroup.relIndex_eq_one.mp hrel1
      have hNKeq : N = K := le_antisymm hNK hKN
      right
      have hqN : CFSG.IsQuasisimple ↥N := by rw [hNKeq]; exact hKq
      have hp3N : p ^ 3 ∣ Nat.card ↥N := by rw [hNKeq]; exact hpK
      have h6N : ¬ 2 ^ 6 ∣ Nat.card ↥N := by rw [hNKeq]; exact h6K
      refine ⟨isInspList_of_qs hs hqN hp8 hp3N h6N, ?_⟩
      rw [hNKeq]
      refine oTwoUpper_le_of_pow_mem (fun x _ => ⟨1, ?_⟩)
      have := Subgroup.pow_index_mem K x
      rw [hK2] at this
      simpa using this
  · left
    exact hs.s3_of_small (card_small_of_dvd_six hsmall).1 (card_small_of_dvd_six hsmall).2

theorem inspCase11 : InspCase fun {_} _ H₁ H₂ => F6.IsF618CaseEleven H₁ H₂ := by
  intro D _ _ D₁ D₂ J N h hs hP
  have key : ∀ H₁ H₂ : Subgroup D, H₁ ⊓ H₂ = D₁ ⊓ D₂ → F6.IsF618CaseEleven H₁ H₂ →
      InspGoal D N := by
    intro H₁ H₂ hHH hc
    have hT : Nat.card ↥(D₁ ⊓ D₂) = 2 ^ 6 := by rw [← hHH, hc.card_inf]; norm_num
    obtain ⟨⟨p, hp8, hD⟩, -⟩ := hc
    obtain ⟨K, hK2, hKS⟩ := exists_index_two_isSLEps3 hD
    exact case11_core h hs hp8 hT hK2 hKS
  rcases hP with hP | hP
  · exact key D₁ D₂ rfl hP
  · exact key D₂ D₁ (inf_comm _ _) hP

end Case11

end Insp9

end CFSG.Quasithin
