module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.A6Exp4Models
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.A6AutOrder8Holds
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.CentralThreeLift
public import CFSG.LocalAnalysis.AGLEmbedding.AltAlpha
public import CFSG.Quasithin.Background.RonanE43M22Real
public import CFSG.GroupTheory.InnerCentralizerProjection

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise commutatorElement

section Center

theorem card_center_dvd_three_of_odd {K : Type} [Group K]
    [Group.IsPerfect K] (hodd : Odd (Nat.card (Subgroup.center K)))
    (e : K ⧸ Subgroup.center K ≃* alternatingGroup (Fin 6)) :
    Nat.card (Subgroup.center K) ∣ 3 := by
  have h := CFSG.AGLEmbedding.card_center_dvd_card_hopfMultiplier e
  rw [(CFSG.Alternating.Multipliers.schurAlternatingMultiplierInput 6 (by norm_num)).2] at h
  have h6 : Nat.card (Subgroup.center K) ∣ 2 * 3 := by simpa using h
  exact Nat.Coprime.dvd_of_dvd_mul_left hodd.coprime_two_right h6

end Center

section A6Exp4

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts

theorem tMul_pow_eight : A6Models.tMul ^ 8 = 1 := by decide +kernel

theorem tMul_pow_four_ne_one : A6Models.tMul ^ 4 ≠ 1 := by decide +kernel

theorem m10_eight_mem : A6Models.tMulFrob * A6Models.tInv ∈ A6Models.m10 :=
  A6Models.m10.mul_mem Out21.A6.tMulFrob_mem_m10 (Out21.A6.psl29_le_m10 Out21.A6.tInv_mem_psl29)

theorem m10_eight_pow_eight : (A6Models.tMulFrob * A6Models.tInv) ^ 8 = 1 := by decide +kernel

theorem m10_eight_pow_four_ne_one : (A6Models.tMulFrob * A6Models.tInv) ^ 4 ≠ 1 := by
  decide +kernel

open CFSG.QuasithinUnique.Unc25K1.A6Model in
theorem exists_sThree_pair_of_faithful {Y : Type} [Group Y] [Finite Y] {K S : Subgroup Y}
    [K.Normal] (e : ↥K ≃* alternatingGroup (Fin 6))
    (hC : Subgroup.centralizer (K : Set Y) = ⊥) (hS : IsSylowTwoOf S ⊤)
    (hS4 : ∀ s ∈ S, s ^ 4 = 1) :
    ∃ Q₀ Q₁ : Subgroup Y, IsSThreeOver S Q₀ ∧ IsSThreeOver S Q₁ ∧ Q₀ ⊔ Q₁ = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨θ, ψ, hθinj, -⟩ := exists_pslEquiv
  obtain ⟨ι, hι, hpsl⟩ := exists_autA6_embedding K e hC
  set B : Subgroup P10 := ι.range.map A6Models.autA6.subtype with hB
  have hBle : B ≤ A6Models.autA6 := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hAB : Y ≃* ↥B := (MonoidHom.ofInjective hι).trans
    (ι.range.equivMapOfInjective _ A6Models.autA6.subtype_injective)
  obtain ⟨k, hk⟩ := hS.2.1.exists_card_eq
  have hidx : ¬ 2 ∣ S.index := by
    have := hS.2.2
    rwa [show (S.subgroupOf ⊤).index = S.index from Subgroup.relIndex_top_right S] at this
  have hB8 : ∀ σ ∈ B, σ ^ 8 = 1 → σ ^ 4 = 1 := by
    rintro _ ⟨_, ⟨y, rfl⟩, rfl⟩ h8
    have hy8 : y ^ (2 ^ 3) = 1 := by
      apply hι
      rw [map_pow, map_one]
      apply Subtype.ext
      simpa using h8
    have hy4 := pow_eq_one_of_index S hk hidx hS4 hy8
    rw [← map_pow, ← map_pow, hy4, map_one, map_one]
  have htA : A6Models.tMul ∈ A6Models.autA6 :=
    Out21.A6.pgl29_le_autA6 Out21.A6.tMul_mem_pgl29
  have hBs6 : B ≤ s6 := by
    intro σ hσ
    by_contra hσs
    rcases classify B hBle hpsl ⟨σ, hσ, hσs⟩ with h | h | h
    · exact tMul_pow_four_ne_one (hB8 _ (by rw [h]; exact Out21.A6.tMul_mem_pgl29) tMul_pow_eight)
    · exact m10_eight_pow_four_ne_one (hB8 _ (by rw [h]; exact m10_eight_mem) m10_eight_pow_eight)
    · exact tMul_pow_four_ne_one (hB8 _ (by rw [h]; exact htA) tMul_pow_eight)
  let j : ↥B →* Equiv.Perm (Fin 6) := θ.comp (Subgroup.inclusion hBs6)
  have hj : Function.Injective j := hθinj.comp (Subgroup.inclusion_injective hBs6)
  have h720 : Nat.card (Equiv.Perm (Fin 6)) = 720 := by
    rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
    rfl
  have hle : Nat.card B ≤ 720 := h720 ▸ Nat.card_le_card_of_injective j hj
  obtain ⟨m, hm⟩ : 360 ∣ Nat.card B := card_psl29 ▸ Subgroup.card_dvd_of_le hpsl
  have hpos : 0 < Nat.card B := Nat.card_pos
  have hm2 : m = 1 ∨ m = 2 := by
    rcases m with _ | _ | _ | m
    · omega
    · exact Or.inl rfl
    · exact Or.inr rfl
    · omega
  rcases hm2 with rfl | rfl
  · have hBc : Nat.card ↥B = 360 := by omega
    have hBeq : A6Models.psl29 = B :=
      Subgroup.eq_of_le_of_card_ge hpsl (le_of_eq (hBc.trans card_psl29.symm))
    exact exists_sThree_pair_of_alt_six hS
      ((hAB.trans (MulEquiv.subgroupCongr hBeq.symm)).trans ψ)
  · have hBc : Nat.card ↥B = 720 := by omega
    have hbij : Function.Bijective j :=
      hj.bijective_of_nat_card_le (le_of_eq (h720.trans hBc.symm))
    exact exists_sThree_pair_of_perm_six hS (hAB.trans (MulEquiv.ofBijective j hbij))

end A6Exp4

open scoped IsMulCommutative in
open CFSG.Quasithin.RonanE43 in
theorem exists_sThree_pair_of_center_three {Y : Type} [Group Y] [Finite Y] {K S : Subgroup Y}
    (hKY : KYForm Y K S) (hZ3 : Nat.card (Subgroup.center ↥K) = 3)
    (e : (↥K ⧸ Subgroup.center ↥K) ≃* alternatingGroup (Fin 6)) (hS4 : ∀ s ∈ S, s ^ 4 = 1) :
    ∃ Q₀ Q₁ : Subgroup Y, IsSThreeOver S Q₀ ∧ IsSThreeOver S Q₁ ∧ Q₀ ⊔ Q₁ = ⊤ := by
  classical
  have hK : K.Normal := hKY.1
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hperfK : Group.IsPerfect ↥K := Group.isPerfect_def.2 hKY.2.1.1
  have hS : CFSG.QuasithinUnique.IsSylowTwoOf S ⊤ := hKY.2.2.2.2.2
  set Z : Subgroup Y := (Subgroup.center ↥K).map K.subtype with hZdef
  have hZn : Z.Normal := by
    have : (Subgroup.center ↥K).Characteristic := Subgroup.centerCharacteristic
    exact ConjAct.normal_of_characteristic_of_normal (H := K) (K := Subgroup.center ↥K)
  have hZK : Z ≤ K := by
    rintro _ ⟨c, -, rfl⟩
    exact c.2
  have hZc : ∀ z ∈ Z, ∀ k ∈ K, z * k = k * z := by
    rintro _ ⟨c, hc, rfl⟩ k hk
    have h1 := congrArg Subtype.val (Subgroup.mem_center_iff.mp hc ⟨k, hk⟩)
    simpa using h1.symm
  have hZcard : Nat.card Z = 3 := (Subgroup.card_subtype K (Subgroup.center ↥K)).trans hZ3
  have hπ : Function.Surjective (QuotientGroup.mk' Z) := QuotientGroup.mk'_surjective Z
  have hS' : CFSG.QuasithinUnique.IsSylowTwoOf (S.map (QuotientGroup.mk' Z)) ⊤ :=
    ⟨le_top, hS.2.1.map _, by
      rw [show ((S.map (QuotientGroup.mk' Z)).subgroupOf ⊤).index =
        (S.map (QuotientGroup.mk' Z)).index from Subgroup.relIndex_top_right _]
      exact isSylowIn_map _ hπ hS⟩
  have : (K.map (QuotientGroup.mk' Z)).Normal := hK.map _ hπ
  let ψ : ↥K →* Y ⧸ Z := (QuotientGroup.mk' Z).comp K.subtype
  have hψker : ψ.ker = Subgroup.center ↥K := by
    ext x
    rw [MonoidHom.mem_ker]
    show QuotientGroup.mk' Z (x : Y) = 1 ↔ _
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    constructor
    · rintro ⟨y, hy, hyx⟩
      have : y = x := Subtype.ext hyx
      rw [← this]
      exact hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  have hψrange : ψ.range = K.map (QuotientGroup.mk' Z) := by
    show ((QuotientGroup.mk' Z).comp K.subtype).range = _
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  let eQ : (↥K ⧸ Subgroup.center ↥K) ≃* ↥ψ.range :=
    (QuotientGroup.quotientMulEquivOfEq hψker.symm).trans (QuotientGroup.quotientKerEquivRange ψ)
  let e₀ : ↥(K.map (QuotientGroup.mk' Z)) ≃* alternatingGroup (Fin 6) :=
    (MulEquiv.subgroupCongr hψrange.symm).trans (eQ.symm.trans e)
  have hC' : Subgroup.centralizer
      ((K.map (QuotientGroup.mk' Z) : Subgroup (Y ⧸ Z)) : Set (Y ⧸ Z)) = ⊥ := by
    rw [eq_bot_iff]
    intro yb hyb
    obtain ⟨y, rfl⟩ := hπ yb
    rw [Subgroup.mem_bot]
    have hyN : y ∈ Subgroup.normalizer (K : Set Y) := by
      rw [Subgroup.normalizer_eq_top_iff.mpr hK]
      trivial
    have hyC : y ∈ Subgroup.centralizer (K : Set Y) := by
      refine CFSG.mem_centralizer_of_commutator_mem_center hperfK hyN fun k hk => ?_
      have h1 : QuotientGroup.mk' Z k * QuotientGroup.mk' Z y =
          QuotientGroup.mk' Z y * QuotientGroup.mk' Z k :=
        Subgroup.mem_centralizer_iff.mp hyb _ ⟨k, hk, rfl⟩
      have h2 : QuotientGroup.mk' Z (y * k * y⁻¹ * k⁻¹) = 1 := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← h1]
        group
      exact (QuotientGroup.eq_one_iff _).mp h2
    have hyZ : y ∈ Z := by
      rw [hZdef, ← hKY.2.2.2.1]
      exact hyC
    exact (QuotientGroup.eq_one_iff y).mpr hyZ
  have hS4' : ∀ s ∈ S.map (QuotientGroup.mk' Z), s ^ 4 = 1 := by
    rintro _ ⟨s, hs, rfl⟩
    rw [← map_pow, hS4 s hs, map_one]
  obtain ⟨H₀, H₁, hH₀, hH₁, hgen⟩ := exists_sThree_pair_of_faithful e₀ hC' hS' hS4'
  have hZS : Z ⊓ S = ⊥ := by
    refine Subgroup.inf_eq_bot_of_coprime ?_
    obtain ⟨k, hk⟩ := hS.2.1.exists_card_eq
    rw [hZcard, hk]
    exact Nat.Coprime.pow_right _ (by norm_num)
  have hSc : Nat.card (S.map (QuotientGroup.mk' Z)) = Nat.card S := by
    refine card_map_of_injOn _ fun x hx h1 => ?_
    have hxZ : x ∈ Z := (QuotientGroup.eq_one_iff x).mp h1
    have : x ∈ Z ⊓ S := ⟨hxZ, hx⟩
    rw [hZS] at this
    exact Subgroup.mem_bot.mp this
  have hreal : ∀ y : ↥K ⧸ Subgroup.center ↥K, y ^ 3 = 1 →
      ∃ g : ↥K ⧸ Subgroup.center ↥K, g * y * g⁻¹ = y⁻¹ := by
    intro y hy
    obtain ⟨g, hg⟩ := real_A6 (e y) (by rw [← map_pow, hy, map_one])
    refine ⟨e.symm g, ?_⟩
    apply e.injective
    rw [map_mul, map_mul, map_inv, map_inv, MulEquiv.apply_symm_apply]
    exact hg
  have hker9 : (QuotientGroup.mk' (Subgroup.center ↥K)).ker =
      (Subgroup.center ↥K).subtype.range := by
    rw [QuotientGroup.ker_mk', Subgroup.range_subtype]
  have h9K := cube_eq_one_of_real (Λ := ↥K) (Γ := ↥K ⧸ Subgroup.center ↥K)
    (Zc := ↥(Subgroup.center ↥K)) hZ3 (Subgroup.center ↥K).subtype
    (Subgroup.subtype_injective _) (fun z => z.2) (QuotientGroup.mk' (Subgroup.center ↥K))
    (QuotientGroup.mk'_surjective _) hker9 hreal
  have h9 : ∀ x ∈ K, x ^ 3 ∈ Z → x ^ 3 = 1 := by
    intro x hx hx3
    have h1 : (⟨x, hx⟩ : ↥K) ^ 3 ∈ (Subgroup.center ↥K).subtype.range := by
      obtain ⟨w, hw, hwx⟩ := Subgroup.mem_map.mp hx3
      refine ⟨⟨w, hw⟩, ?_⟩
      apply Subtype.ext
      simpa using hwx
    have := h9K ⟨x, hx⟩ h1
    simpa using congrArg Subtype.val this
  have lift : ∀ H : Subgroup (Y ⧸ Z), IsSThreeOver (S.map (QuotientGroup.mk' Z)) H →
      ∃ P : Subgroup Y, IsSThreeOver S P ∧ P.map (QuotientGroup.mk' Z) = H := by
    rintro H ⟨hSH, hHc, hHn⟩
    obtain ⟨X, hXK, hXH, hXc, -, hXZ, hPc⟩ := exists_permutes_three_of_lift hKY.2.2.2.2.1 hS
      hZK hZcard hZc h9 hSH (by rw [hHc, hSc])
    have hPH : X ⊔ S ≤ H.comap (QuotientGroup.mk' Z) :=
      sup_le hXH (Subgroup.map_le_iff_le_comap.1 hSH)
    have hPZ : (X ⊔ S) ⊓ Z = ⊥ := by
      by_contra hne
      have hZle : Z ≤ X ⊔ S := by
        have hc : Nat.card ↥((X ⊔ S) ⊓ Z) ∣ 3 := hZcard ▸ Subgroup.card_dvd_of_le inf_le_right
        rcases (Nat.dvd_prime Nat.prime_three).mp hc with h | h
        · exact absurd (Subgroup.eq_bot_of_card_eq _ h) hne
        · have : (X ⊔ S) ⊓ Z = Z :=
            Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h, hZcard])
          rw [← this]
          exact inf_le_left
      have hXZc : Nat.card ↥(Z ⊔ X) = 9 := by
        have h :=
          CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
            (H := X) (K := Z) (by rw [Subgroup.normalizer_eq_top_iff.mpr hZn]; exact le_top)
        rw [hXZ, Subgroup.card_bot, mul_one, hXc, hZcard, sup_comm] at h
        exact h
      have hdvd : 9 ∣ 3 * Nat.card S := by
        rw [← hXZc, ← hPc]
        exact Subgroup.card_dvd_of_le (sup_le hZle le_sup_left)
      obtain ⟨k, hk⟩ := hS.2.1.exists_card_eq
      rw [hk] at hdvd
      obtain ⟨c, hc⟩ := hdvd
      have h3 : 3 ∣ 2 ^ k := ⟨c, by omega⟩
      have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
      omega
    have hmapc : Nat.card ((X ⊔ S).map (QuotientGroup.mk' Z)) = Nat.card ↥(X ⊔ S) := by
      refine card_map_of_injOn _ fun x hx h1 => ?_
      have hxZ : x ∈ Z := (QuotientGroup.eq_one_iff x).mp h1
      have : x ∈ (X ⊔ S) ⊓ Z := ⟨hx, hxZ⟩
      rw [hPZ] at this
      exact Subgroup.mem_bot.mp this
    have hmap : (X ⊔ S).map (QuotientGroup.mk' Z) = H :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.map_le_iff_le_comap.2 hPH)
        (by rw [hHc, hSc, hmapc, hPc])
    refine ⟨X ⊔ S, ⟨le_sup_right, hPc, fun hle => hHn ?_⟩, hmap⟩
    rw [← hmap]
    exact (Subgroup.map_mono hle).trans (Subgroup.le_normalizer_map _)
  obtain ⟨P₀, hP₀, hm₀⟩ := lift H₀ hH₀
  obtain ⟨P₁, hP₁, hm₁⟩ := lift H₁ hH₁
  refine ⟨P₀, P₁, hP₀, hP₁, ?_⟩
  have hJ : P₀ ⊔ P₁ ⊔ Z = ⊤ := by
    have h := Subgroup.comap_map_eq (QuotientGroup.mk' Z) (P₀ ⊔ P₁)
    rw [Subgroup.map_sup, hm₀, hm₁, hgen, Subgroup.comap_top, QuotientGroup.ker_mk'] at h
    exact h.symm
  exact eq_top_of_sup_eq_top_of_central hZK hZc (Subgroup.commutator_eq_self (H := K)).ge hJ

theorem k_A6Exp4SThreePair_holds : K_A6Exp4SThreePair := by
  intro Y _ _ K S hKY ⟨e⟩ hS4
  have hS : CFSG.QuasithinUnique.IsSylowTwoOf S ⊤ := hKY.2.2.2.2.2
  have : Group.IsPerfect ↥K := Group.isPerfect_def.2 hKY.2.1.1
  have : K.Normal := hKY.1
  obtain ⟨Q₀, Q₁, h₀, h₁, hgen⟩ :
      ∃ Q₀ Q₁ : Subgroup Y, IsSThreeOver S Q₀ ∧ IsSThreeOver S Q₁ ∧ Q₀ ⊔ Q₁ = ⊤ := by
    rcases (Nat.dvd_prime Nat.prime_three).1 (card_center_dvd_three_of_odd hKY.2.2.1 e) with
      h1 | h3
    · have hZ : Subgroup.center ↥K = ⊥ := Subgroup.eq_bot_of_card_eq _ h1
      exact exists_sThree_pair_of_faithful
        ((QuotientGroup.quotientBot.symm.trans
            (QuotientGroup.quotientMulEquivOfEq hZ).symm).trans e)
        (by rw [hKY.2.2.2.1, hZ, Subgroup.map_bot]) hS hS4
    · exact exists_sThree_pair_of_center_three hKY h3 e hS4
  exact ⟨Q₀, Q₁, h₀.1, h₁.1, hgen, h₀.bar2 hS, h₁.bar2 hS⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

end
