module

public import CFSG.Quasithin.EmptyFaithful.SzF53Defs
public import CFSG.Quasithin.Recognition.F112J2Setup
public import CFSG.Quasithin.Background.GoldschmidtRankOneSmall
public import CFSG.Quasithin.EmptyFaithful.SBdK36Abs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S152X

namespace SzF53A2

theorem card_alternatingGroup : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  rw [Nat.card_eq_fintype_card]
  decide

theorem pow_two_or_pow_three_of_pow_six :
    ∀ g : alternatingGroup (Fin 5), g ^ 6 = 1 → g ^ 2 = 1 ∨ g ^ 3 = 1 := by
  decide +kernel

theorem index_ne_three {X : Type*} [Group X] [Finite X] [IsSimpleGroup X]
    (hX : Nat.card X = 60) (M : Subgroup X) : M.index ≠ 3 := by
  intro h3
  have hfi : M.FiniteIndex := ⟨by omega⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal M.normalCore with h | h
  · have hdvd := M.index_normalCore_dvd_factorial_index
    rw [h, Subgroup.index_bot, hX, h3] at hdvd
    norm_num [Nat.factorial] at hdvd
  · have hM : M = ⊤ := top_le_iff.mp (h ▸ M.normalCore_le)
    rw [hM, Subgroup.index_top] at h3
    omega

theorem normal_of_card_twelve {X : Type*} [Group X] [Finite X] (hX : Nat.card X = 12)
    (hsix : ∀ g : X, g ^ 6 = 1 → g ^ 2 = 1 ∨ g ^ 3 = 1) (T : Subgroup X) (hT : Nat.card T = 4) :
    T.Normal := by
  have hidx : T.index = 3 := by
    have := T.card_mul_index
    rw [hT, hX] at this
    omega
  have hfi : T.FiniteIndex := ⟨by omega⟩
  have hdvd : T.normalCore.index ∣ 6 := by
    have h := T.index_normalCore_dvd_factorial_index
    rw [hidx] at h
    exact h
  have hcn : T.normalCore.Normal := inferInstance
  have hmul := T.normalCore.card_mul_index
  rw [hX] at hmul
  have hle : T.normalCore ≤ T := T.normalCore_le
  have hcT : Nat.card T.normalCore ∣ 4 := hT ▸ Subgroup.card_dvd_of_le hle
  have hcases : Nat.card T.normalCore = 4 ∨ Nat.card T.normalCore = 2 := by
    have h1 : Nat.card T.normalCore ≤ 4 := Nat.le_of_dvd (by norm_num) hcT
    have h2 : T.normalCore.index ≤ 6 := Nat.le_of_dvd (by norm_num) hdvd
    generalize Nat.card T.normalCore = a at *
    generalize T.normalCore.index = i at *
    interval_cases a <;> interval_cases i <;> omega
  rcases hcases with h4 | h2
  · have heq : T.normalCore = T := Subgroup.eq_of_le_of_card_ge hle (by omega)
    rw [heq] at hcn
    exact hcn
  · exfalso
    obtain ⟨z, hz1, hzu⟩ := (Nat.card_eq_two_iff' (1 : T.normalCore)).mp h2
    have hzc : ∀ g : X, g * (z : X) * g⁻¹ = z := by
      intro g
      have hmem : g * (z : X) * g⁻¹ ∈ T.normalCore := hcn.conj_mem z z.2 g
      have hne : (⟨g * (z : X) * g⁻¹, hmem⟩ : T.normalCore) ≠ 1 := by
        intro h
        apply hz1
        have h' : g * (z : X) * g⁻¹ = 1 := congrArg Subtype.val h
        exact Subtype.ext (by simpa using h')
      exact congrArg Subtype.val (hzu _ hne)
    have hz2 : (z : X) ^ 2 = 1 := by
      have := pow_card_eq_one' (G := T.normalCore) (x := z)
      rw [h2] at this
      exact congrArg Subtype.val this
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' 3 (by rw [hX]; norm_num : 3 ∣ Nat.card X)
    have hc3 : c ^ 3 = 1 := by rw [← hc]; exact pow_orderOf_eq_one c
    have hcomm : Commute (z : X) c := by
      have h := hzc c
      show (z : X) * c = c * z
      calc (z : X) * c = c * z * c⁻¹ * c := by rw [h]
        _ = c * z := by group
    have hz1' : (z : X) ≠ 1 := fun h => hz1 (Subtype.ext h)
    have hz6 : (z : X) ^ 6 = 1 := by
      rw [show (6 : ℕ) = 2 * 3 from rfl, pow_mul, hz2, one_pow]
    have hc6 : c ^ 6 = 1 := by
      rw [show (6 : ℕ) = 3 * 2 from rfl, pow_mul, hc3, one_pow]
    have h6 : ((z : X) * c) ^ 6 = 1 := by
      rw [hcomm.mul_pow, hz6, hc6, one_mul]
    rcases hsix _ h6 with h | h
    · rw [hcomm.mul_pow, hz2, one_mul] at h
      have hord : orderOf c ∣ 2 := orderOf_dvd_of_pow_eq_one h
      rw [hc] at hord
      omega
    · rw [hcomm.mul_pow, hc3, mul_one] at h
      have hord : orderOf (z : X) ∣ 3 := orderOf_dvd_of_pow_eq_one h
      have hord2 : orderOf (z : X) ∣ 2 := orderOf_dvd_of_pow_eq_one hz2
      have h1 : orderOf (z : X) = 1 := by
        have := Nat.dvd_gcd hord hord2
        simpa using this
      exact hz1' (orderOf_eq_one_iff.mp h1)

theorem card_eq_four {T : Subgroup (alternatingGroup (Fin 5))} (hT : IsPGroup 2 T)
    (hodd : ¬ 2 ∣ T.index) : Nat.card T = 4 := by
  obtain ⟨b, hb⟩ := hT.exists_card_eq
  have hmul := T.card_mul_index
  rw [hb, card_alternatingGroup] at hmul
  have hb5 : b ≤ 5 := by
    by_contra h
    push Not at h
    have h1 : 2 ^ 6 ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) h
    have h2 : 0 < T.index := Nat.pos_of_ne_zero (fun h0 => by rw [h0] at hmul; omega)
    have h3 : 2 ^ b ≤ 60 := by nlinarith
    omega
  have hb2 : 2 ^ b = 4 := by
    interval_cases b <;> omega
  rw [hb, hb2]

theorem normalizer_ne_top {T : Subgroup (alternatingGroup (Fin 5))} (h4 : Nat.card T = 4) :
    Subgroup.normalizer (T : Set (alternatingGroup (Fin 5))) ≠ ⊤ := by
  intro htop
  have : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  have hN : T.Normal := Subgroup.normalizer_eq_top_iff.mp htop
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal T with h | h
  · rw [h, Subgroup.card_bot] at h4
    omega
  · rw [h, Subgroup.card_top, card_alternatingGroup] at h4
    omega

theorem card_overgroup {T M : Subgroup (alternatingGroup (Fin 5))} (h4 : Nat.card T = 4)
    (hTM : T ≤ M) (hM : M ≠ ⊤) : Nat.card M = 4 ∨ Nat.card M = 12 := by
  have : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  have h1 : 4 ∣ Nat.card M := h4 ▸ Subgroup.card_dvd_of_le hTM
  have h2 : Nat.card M ∣ 60 := card_alternatingGroup ▸ Subgroup.card_subgroup_dvd_card M
  have h3 : Nat.card M ≠ 60 := fun h =>
    hM (Subgroup.eq_top_of_card_eq M (h.trans card_alternatingGroup.symm))
  have h5 : Nat.card M ≠ 20 := by
    intro h
    refine index_ne_three card_alternatingGroup M ?_
    have := M.card_mul_index
    rw [h, card_alternatingGroup] at this
    omega
  have hle : Nat.card M ≤ 60 := Nat.le_of_dvd (by norm_num) h2
  obtain ⟨k, hk⟩ := h1
  rw [hk] at h2 h3 h5 hle ⊢
  have hk15 : k ≤ 15 := by omega
  interval_cases k <;> omega

theorem le_normalizer_of_overgroup {T M : Subgroup (alternatingGroup (Fin 5))}
    (h4 : Nat.card T = 4) (hTM : T ≤ M) (hM : M ≠ ⊤) :
    M ≤ Subgroup.normalizer (T : Set (alternatingGroup (Fin 5))) := by
  rcases card_overgroup h4 hTM hM with h | h
  · have heq : T = M := Subgroup.eq_of_le_of_card_ge hTM (by omega)
    rw [← heq]
    exact Subgroup.le_normalizer
  · rw [← Subgroup.normal_subgroupOf_iff_le_normalizer hTM]
    refine normal_of_card_twelve (X := ↥M) h ?_ (T.subgroupOf M) ?_
    · intro g hg
      have hg' : (g : alternatingGroup (Fin 5)) ^ 6 = 1 := by
        have := congrArg Subtype.val hg
        simpa using this
      rcases pow_two_or_pow_three_of_pow_six _ hg' with h' | h'
      · left
        exact Subtype.ext (by simpa using h')
      · right
        exact Subtype.ext (by simpa using h')
    · rw [← h4]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTM).toEquiv

theorem commutator_mem {T : Subgroup (alternatingGroup (Fin 5))} (h4 : Nat.card T = 4)
    {x y : alternatingGroup (Fin 5)} (hx : x ∈ Subgroup.normalizer (T : Set _))
    (hy : y ∈ Subgroup.normalizer (T : Set _)) : x * y * x⁻¹ * y⁻¹ ∈ T := by
  set N := Subgroup.normalizer (T : Set (alternatingGroup (Fin 5)))
  have hTN : T ≤ N := Subgroup.le_normalizer
  have hNtop : N ≠ ⊤ := normalizer_ne_top h4
  have hnorm : (T.subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hTN).mpr le_rfl
  have hT' : Nat.card (T.subgroupOf N) = 4 := by
    rw [← h4]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTN).toEquiv
  have hidx : (T.subgroupOf N).index ∣ 3 := by
    have hmul := (T.subgroupOf N).card_mul_index
    rw [hT'] at hmul
    rcases card_overgroup h4 hTN hNtop with h | h
    · rw [h] at hmul
      have : (T.subgroupOf N).index = 1 := by omega
      rw [this]
      exact one_dvd _
    · rw [h] at hmul
      have : (T.subgroupOf N).index = 3 := by omega
      rw [this]
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcyc : IsCyclic (↥N ⧸ T.subgroupOf N) :=
    isCyclic_of_card_dvd_prime (p := 3) hidx
  have hcomm := (IsCyclic.isMulCommutative (α := ↥N ⧸ T.subgroupOf N)).is_comm.comm
  set a : ↥N := ⟨x, hx⟩
  set b : ↥N := ⟨y, hy⟩
  have key : (a * b * a⁻¹ * b⁻¹ : ↥N) ∈ T.subgroupOf N := by
    rw [← QuotientGroup.ker_mk' (T.subgroupOf N), MonoidHom.mem_ker]
    simp only [map_mul, map_inv]
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul]
    exact hcomm _ _
  exact Subgroup.mem_subgroupOf.mp key

end SzF53A2

theorem isRankOneSylow_alternatingGroup_five : IsRankOneSylow (alternatingGroup (Fin 5)) := by
  intro T hT hodd
  have h4 := SzF53A2.card_eq_four hT hodd
  exact ⟨SzF53A2.normalizer_ne_top h4,
    fun M hTM hM => SzF53A2.le_normalizer_of_overgroup h4 hTM hM,
    fun x hx y hy => SzF53A2.commutator_mem h4 hx hy⟩

theorem nonempty_oTwoQuot_sup_perm_three {G : Type*} [Group G] [Finite G] {L S : Subgroup G}
    (hS : S ≤ Subgroup.normalizer (L : Set G)) (hS2 : IsPGroup 2 S)
    (e : OTwoQuot L ≃* Equiv.Perm (Fin 3)) :
    Nonempty (OTwoQuot (L ⊔ S) ≃* Equiv.Perm (Fin 3)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M : Subgroup G := L ⊔ S
  have hLM : L ≤ M := le_sup_left
  have hMN : M ≤ Subgroup.normalizer (L : Set G) := sup_le Subgroup.le_normalizer hS
  have hcore : pCoreOf 2 L ≤ pCoreOf 2 M := F7.pCoreOf_mono_of_le_normalizer hLM hMN
  have hcore' : pCoreOf 2 M ⊓ L ≤ pCoreOf 2 L := F7.pCoreOf_inf_le hLM
  let π : ↥M →* OTwoQuot M := QuotientGroup.mk' (CFSG.Open.pCore 2 ↥M)
  let f : ↥L →* OTwoQuot M := π.comp (Subgroup.inclusion hLM)
  have hfker : f.ker = CFSG.Open.pCore 2 ↥L := by
    ext l
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, F1.mem_pCore_iff_coe, F1.mem_pCore_iff_coe]
    exact ⟨fun h => hcore' ⟨h, l.2⟩, fun h => hcore h⟩
  let K : Subgroup (OTwoQuot M) := f.range
  have hKn : K.Normal := by
    refine ⟨fun k hk q => ?_⟩
    obtain ⟨l, rfl⟩ := hk
    obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.Open.pCore 2 ↥M) q
    have hmem : (m : G) * (l : G) * (m : G)⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.mp (hMN m.2) l).mp l.2
    refine ⟨⟨(m : G) * (l : G) * (m : G)⁻¹, hmem⟩, ?_⟩
    simp only [f, MonoidHom.comp_apply]
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  have eK : K ≃* Equiv.Perm (Fin 3) :=
    (QuotientGroup.quotientKerEquivRange f).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hfker).trans e)
  obtain ⟨ψ, hψ⟩ := SBd.exists_hom_extending_perm_three K eK
  have hsurj : Function.Surjective ψ := fun σ =>
    ⟨((eK.symm σ : K) : OTwoQuot M), by rw [hψ]; simp⟩
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLM).mpr hMN
  have hker2 : ∀ x ∈ ψ.ker, ∃ k : ℕ, x ^ 2 ^ k = 1 := by
    intro x hx
    obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.Open.pCore 2 ↥M) x
    obtain ⟨a, ha, b, hb, hab⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hS).mp m.2
    obtain ⟨j, hj⟩ := hS2 ⟨b, hb⟩
    refine ⟨j, ?_⟩
    have hbM : b ∈ M := (le_sup_right : S ≤ L ⊔ S) hb
    have haM : a ∈ M := (le_sup_left : L ≤ L ⊔ S) ha
    have hmab : m = ⟨a, haM⟩ * ⟨b, hbM⟩ := Subtype.ext hab
    have hb1 : (⟨b, hbM⟩ : ↥M) ^ 2 ^ j = 1 :=
      Subtype.ext (by simpa using congrArg Subtype.val hj)
    have hL1 : m ^ 2 ^ j ∈ L.subgroupOf M := by
      have h1 : QuotientGroup.mk' (L.subgroupOf M) (m ^ 2 ^ j) = 1 := by
        rw [map_pow, hmab, map_mul]
        have h2 : QuotientGroup.mk' (L.subgroupOf M) ⟨a, haM⟩ = 1 :=
          (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr ha)
        rw [h2, one_mul, ← map_pow, hb1, map_one]
      exact (QuotientGroup.eq_one_iff _).mp h1
    set l : ↥L := ⟨((m ^ 2 ^ j : ↥M) : G), Subgroup.mem_subgroupOf.mp hL1⟩
    have hfl : f l = π m ^ 2 ^ j := by
      simp only [f, MonoidHom.comp_apply, π, ← map_pow]
      rfl
    have hmem : f l ∈ K := ⟨l, rfl⟩
    have h1 : eK ⟨f l, hmem⟩ = 1 := by
      rw [← hψ]
      show ψ (f l) = 1
      rw [hfl, map_pow, MonoidHom.mem_ker.mp hx, one_pow]
    have h2 : (⟨f l, hmem⟩ : K) = 1 := eK.injective (by rw [h1, map_one])
    rw [← hfl]
    exact congrArg Subtype.val h2
  have hker3 : IsPGroup 2 ψ.ker := by
    rintro ⟨x, hx⟩
    obtain ⟨k, hk⟩ := hker2 x hx
    exact ⟨k, Subtype.ext (by simpa using hk)⟩
  have hO : CFSG.Open.pCore 2 (OTwoQuot M) = ⊥ := by
    have h := pCore_two_quot_eq_bot M
    exact h
  have hinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hle : ψ.ker ≤ CFSG.Open.pCore 2 (OTwoQuot M) :=
      le_pCore 2 (MonoidHom.normal_ker ψ) hker3
    rw [hO] at hle
    exact Subgroup.mem_bot.mp (hle (MonoidHom.mem_ker.mpr hx))
  exact ⟨MulEquiv.ofBijective ψ ⟨hinj, hsurj⟩⟩

theorem hyp111R_of_perm_three_alt_five {G : Type} [Group G] [Finite G] {L₁ L₂ S : Subgroup G}
    (hyp : Hyp111 L₁ L₂ S) (h₁ : Nonempty (OTwoQuot L₁ ≃* Equiv.Perm (Fin 3)))
    (h₂ : Nonempty (OTwoQuot L₂ ≃* ↥(alternatingGroup (Fin 5)))) : Hyp111R L₁ L₂ S := by
  obtain ⟨e₁⟩ := h₁
  obtain ⟨e₂⟩ := h₂
  exact ⟨hyp,
    F1.rankOneAt_of_isRankOneSylow hyp.h1.sylow (isRankOneSylow_perm_three.of_mulEquiv e₁.symm),
    F1.rankOneAt_of_isRankOneSylow hyp.h2.sylow
      (isRankOneSylow_alternatingGroup_five.of_mulEquiv e₂.symm)⟩

theorem F53Amalgam.of_hyp111 {G : Type} [Group G] [Finite G] {L₁ L₂ S : Subgroup G}
    (hyp : Hyp111 L₁ L₂ S) (hq : IsQuasithinSub (L₁ ⊔ L₂ ⊔ S))
    (h₁ : Nonempty (OTwoQuot L₁ ≃* Equiv.Perm (Fin 3)))
    (h₂ : Nonempty (OTwoQuot L₂ ≃* ↥(alternatingGroup (Fin 5))))
    (h₃ : Nonempty (OTwoQuot (L₂ ⊔ S) ≃* Equiv.Perm (Fin 5))) :
    F53Amalgam (L₂ ⊔ S) (L₁ ⊔ S) S := by
  have hR := hyp111R_of_perm_three_alt_five hyp h₁ h₂
  have hA := F112J2.amalgamHyp_thesis hR
  have hgen : (L₂ ⊔ S) ⊔ (L₁ ⊔ S) = L₁ ⊔ L₂ ⊔ S := hA.gen.symm
  obtain ⟨e₁⟩ := h₁
  exact
    { amalgam := by rw [hgen]; exact hA
      inf_eq := by rw [inf_comm]; exact F112J2.inf_L2S_K1S hR.symm ⟨e₁⟩
      charTwo_right := (F112J2.amalgamHyp_thesis hR.symm).charTwo
      quot_left := h₃
      quot_right := nonempty_oTwoQuot_sup_perm_three hyp.h1.normalizes hyp.h1.pgroup e₁
      quasithin := by rw [hgen]; exact hq }

end CFSG.Quasithin
