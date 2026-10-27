module

public import CFSG.Quasithin.EmptyFaithful.Der6CSec
public import CFSG.Quasithin.EmptyFaithful.S146C7

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement

namespace Der6C

variable {G : Type} [Group G] [Finite G] {K P Z U₁ : Subgroup G}

theorem exists_fixed_not_centralized_of_irred
    (hZU : Z ≤ U₁) (hUN : U₁ ≤ Subgroup.normalizer (Z : Set G))
    (hsq : ∀ a ∈ U₁, a ^ 2 ∈ Z) (hcomm : ∀ a ∈ U₁, ∀ b ∈ U₁, a * b * a⁻¹ * b⁻¹ ∈ Z)
    (hKZ : K ≤ Subgroup.normalizer (Z : Set G)) (hKU : K ≤ Subgroup.normalizer (U₁ : Set G))
    (hPZ : P ≤ Subgroup.normalizer (Z : Set G)) (hPU : P ≤ Subgroup.normalizer (U₁ : Set G))
    (hP2 : IsPGroup 2 P) (hirr : IsIrredOnSection K U₁ Z) (hperf : ⁅U₁, K⁆ ⊔ Z = U₁) :
    ∃ u ∈ U₁, (∃ k ∈ K, k * u * k⁻¹ * u⁻¹ ∉ Z) ∧ ∀ p ∈ P, p * u * p⁻¹ * u⁻¹ ∈ Z := by
  classical
  have hel : IsElemAbelian 2 (tildeOf Z U₁) := isElemAbelian_secImg_normalizer hcomm hsq
  let _ : CommGroup ↥(tildeOf Z U₁) := commGroupOfElemAbelian hel
  have hKN : K ≤ NN Z U₁ := le_inf hKZ hKU
  have hPN : P ≤ NN Z U₁ := le_inf hPZ hPU
  set ψK : ↥K →* MulAut ↥(tildeOf Z U₁) := (rhoN Z U₁).comp (Subgroup.inclusion hKN) with hψK
  set ψP : ↥P →* MulAut ↥(tildeOf Z U₁) := (rhoN Z U₁).comp (Subgroup.inclusion hPN) with hψP
  have hW2 : ∀ w : ↥(tildeOf Z U₁), w ^ 2 = 1 := fun a =>
    Subtype.ext (by simpa [pow_two] using isElemAbelian_pow_eq_one hel a.2)
  have hW : centralizerMod Z U₁ K = Z := by
    have hZW : Z ≤ centralizerMod Z U₁ K := fun z hz =>
      ⟨hZU hz, Subgroup.le_normalizer hz, fun k hk => by
        have h1 : k * z⁻¹ * k⁻¹ ∈ Z := (Subgroup.mem_normalizer_iff.mp (hKZ hk) z⁻¹).mp (Z.inv_mem hz)
        have e : z * k * z⁻¹ * k⁻¹ = z * (k * z⁻¹ * k⁻¹) := by group
        rw [e]
        exact Z.mul_mem hz h1⟩
    rcases hirr.2.2.2 (centralizerMod Z U₁ K) hZW (centralizerMod_le_left _ _ _)
        (le_normalizer_centralizerMod hKZ hKU Subgroup.le_normalizer) with h | h
    · exact h
    · exfalso
      have hle : ⁅U₁, K⁆ ≤ Z := by
        refine Subgroup.commutator_le.mpr fun u hu k hk => ?_
        have : u ∈ centralizerMod Z U₁ K := by rw [h]; exact hu
        exact this.2.2 k hk
      rw [sup_eq_right.mpr hle] at hperf
      exact hirr.1.ne hperf
  have hfixK : ∀ w ∈ fixV ψK.range, w = 1 := by
    intro w hw
    obtain ⟨u₀, hu₀, rfl⟩ := exists_wOf hUN w
    have hc : ∀ k ∈ K, k * u₀ * k⁻¹ * u₀⁻¹ ∈ Z := fun k hk =>
      (rhoN_wOf_eq_iff hUN (hKN hk) hu₀).mp (mem_fixV.mp hw (ψK ⟨k, hk⟩) ⟨⟨k, hk⟩, rfl⟩)
    have hu₀W : u₀ ∈ centralizerMod Z U₁ K :=
      ⟨hu₀, hUN hu₀, fun k hk => by
        have := Z.inv_mem (hc k hk)
        have e : (k * u₀ * k⁻¹ * u₀⁻¹)⁻¹ = u₀ * k * u₀⁻¹ * k⁻¹ := by group
        rwa [e] at this⟩
    rw [hW] at hu₀W
    exact wOf_eq_one hUN hu₀W hu₀
  obtain ⟨u₁, hu₁, hu₁Z⟩ := IsConcreteLE.exists_of_lt hirr.1
  have hntw : wOf hUN hu₁ ≠ 1 := fun h => hu₁Z (secMk_eq_one_iff.mp (congrArg Subtype.val h))
  have hP2' : IsPGroup 2 ↥ψP.range := hP2.of_surjective ψP.rangeRestrict ψP.rangeRestrict_surjective
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let act : MulAction ↥ψP.range ↥(tildeOf Z U₁) :=
    { smul := fun s u => (s : MulAut ↥(tildeOf Z U₁)) u
      one_smul := fun u => rfl
      mul_smul := fun s t u => rfl }
  have hdvd : 2 ∣ Nat.card ↥(tildeOf Z U₁) := by
    have hox : orderOf (wOf hUN hu₁) = 2 := orderOf_eq_prime (hW2 _) hntw
    exact hox ▸ orderOf_dvd_natCard _
  have h1 : (1 : ↥(tildeOf Z U₁)) ∈ MulAction.fixedPoints ↥ψP.range ↥(tildeOf Z U₁) := fun s =>
    map_one (s : MulAut ↥(tildeOf Z U₁))
  obtain ⟨b, hb, hb1⟩ := hP2'.exists_fixed_point_of_prime_dvd_card_of_fixed_point _ hdvd h1
  obtain ⟨u, hu, rfl⟩ := exists_wOf hUN b
  refine ⟨u, hu, ?_, fun p hp => ?_⟩
  · by_contra hcon
    push Not at hcon
    apply hb1
    symm
    refine hfixK _ (mem_fixV.mpr ?_)
    rintro _ ⟨k, rfl⟩
    exact (rhoN_wOf_eq_iff hUN (hKN k.2) hu).mpr (hcon k k.2)
  · exact (rhoN_wOf_eq_iff hUN (hPN hp) hu).mp
      (hb ⟨ψP ⟨p, hp⟩, ⟨⟨p, hp⟩, rfl⟩⟩)

end Der6C

theorem stage146D4A6_of (hI : AsI231A6) : Stage146D4A6 := by
  intro G _ _ T M S hB K hK c21 c22 c23 U₁ U₂ s hdec hA
  have hG : IsHTM T M (mcOf T) := S.isHTM_mcOf
  have hKG : K ≤ mcOf T := le_of_mem_cComp hK
  have hTG : T ≤ mcOf T := hG.1.1
  have hT2 : IsPGroup 2 T := S.hyp.sylow.1
  have hUab : IsElemAbelian 2 (conjClosure (VZ T M) (mcOf T)) := S.lemma_14_5_15_two hG
  have hUQ : conjClosure (VZ T M) (mcOf T) ≤ pCoreOf 2 (mcOf T) := S.conjClosure_le_pCoreOf hG
  have hQT : pCoreOf 2 (mcOf T) ≤ T := S.pCoreOf_le_T hG
  have hUN : conjClosure (VZ T M) (mcOf T) ≤
      Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) := S.conjClosure_le_normalizer_Z hG
  have hZU : quasithinOmegaOneCenter T ≤ conjClosure (VZ T M) (mcOf T) :=
    Z_le_conjClosure_VZ T M (mcOf T)
  have hG₁Z : mcOf T ≤ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) := fun x hx =>
    S.normalizer_Z.ge hx
  have hTZ : T ≤ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) := fun x hx =>
    hG₁Z (hTG hx)
  have hpc : perfectCore (mcOf T) = K := by
    rcases c21 with ⟨h, -⟩ | ⟨-, h3⟩ | ⟨Kp, -, -, -, -, -, h3, -⟩
    · exact h
    · exact (not_kbarIsA6_of_kbarIsL3Two h3 hA).elim
    · exact (not_kbarIsA6_of_kbarIsL3Two h3 hA).elim
  have hTK : T ≤ Subgroup.normalizer (K : Set G) := fun x hx => by
    have h1 : x ∈ Subgroup.normalizer ((mcOf T : Subgroup G) : Set G) :=
      Subgroup.le_normalizer (hTG hx)
    have h2 := normalizer_le_normalizer_perfectCore (mcOf T) h1
    rwa [hpc] at h2
  have hC2 : ¬ IsCase2 T K := by
    rintro ⟨t, htT, htK, -⟩
    exact htK (hTK htT)
  obtain ⟨hnat, hperf⟩ : (mIdx U₁ (quasithinOmegaOneCenter T) = 5 ∨
        (mIdx U₁ (quasithinOmegaOneCenter T) = 4 ∧
          IsIrredOnSection K U₁ (quasithinOmegaOneCenter T))) ∧
      ⁅U₁, K⁆ ⊔ quasithinOmegaOneCenter T = U₁ := by
    rcases hdec.natural with ⟨h3, -, -⟩ | ⟨-, ⟨h4, hirr, hperf⟩ | ⟨h5, hperf⟩⟩
    · exact (not_kbarIsA6_of_kbarIsL3Two h3 hA).elim
    · exact ⟨Or.inr ⟨h4, hirr⟩, hperf⟩
    · exact ⟨Or.inl h5, hperf⟩
  have hsup : ⁅conjClosure (VZ T M) (mcOf T), K⁆ ⊔ quasithinOmegaOneCenter T = U₁ ⊔ U₂ :=
    hdec.sup
  have hU₁U : U₁ ≤ conjClosure (VZ T M) (mcOf T) := by
    have hKU : K ≤ Subgroup.normalizer (conjClosure (VZ T M) (mcOf T) : Set G) :=
      hKG.trans (le_normalizer_conjClosure _ _)
    have h1 : ⁅conjClosure (VZ T M) (mcOf T), K⁆ ≤ conjClosure (VZ T M) (mcOf T) :=
      S145.commutator_le_of_le_normalizer hKU
    have h2 : U₁ ⊔ U₂ ≤ conjClosure (VZ T M) (mcOf T) := by
      rw [← hsup]
      exact sup_le h1 hZU
    exact le_sup_left.trans h2
  have hU₁2 : IsPGroup 2 U₁ := (pCoreOf_isPGroup 2 (mcOf T)).to_le (hU₁U.trans hUQ)
  have hsq : ∀ a ∈ U₁, a ^ 2 ∈ quasithinOmegaOneCenter T := fun a ha => by
    rw [isElemAbelian_pow_eq_one hUab (hU₁U ha)]
    exact Subgroup.one_mem _
  have hcomm : ∀ a ∈ U₁, ∀ b ∈ U₁, a * b * a⁻¹ * b⁻¹ ∈ quasithinOmegaOneCenter T :=
    fun a ha b hb => by
      have e : a * b * a⁻¹ * b⁻¹ = 1 := by
        rw [isElemAbelian_comm hUab (hU₁U ha) (hU₁U hb)]
        group
      rw [e]
      exact Subgroup.one_mem _
  have hQ : ∀ q ∈ pCoreOf 2 K, ∀ u ∈ U₁, q * u * q⁻¹ * u⁻¹ ∈ quasithinOmegaOneCenter T := by
    intro q hq u hu
    have hqG : q ∈ pCoreOf 2 (mcOf T) :=
      A4.pCoreOf_le_of_subnormal 2 (subnormal_of_mem_cComp hK) hq
    have := S.comm_mem_Z hG (hU₁U hu) hqG
    simpa [commutatorElement_def] using this
  have hKU : K ≤ Subgroup.normalizer (U₁ : Set G) := Der6C.le_normalizer_of_commutator_sup hperf
  obtain ⟨u, hu, ⟨k, hk, hnk⟩, hP⟩ : ∃ u ∈ U₁, (∃ k ∈ K, k * u * k⁻¹ * u⁻¹ ∉ quasithinOmegaOneCenter T) ∧
      ∀ p ∈ T ⊓ Subgroup.normalizer (U₁ : Set G), p * u * p⁻¹ * u⁻¹ ∈ quasithinOmegaOneCenter T := by
    rcases hnat with h5 | ⟨-, hirr⟩
    · have hcard : (quasithinOmegaOneCenter T).relIndex U₁ = 2 ^ 5 := by
        rw [HypF98.relIndex_eq_two_pow_mIdx hU₁2, h5]
      exact Der6C.exists_fixed_not_centralized_of_asI231A6 hI hdec.Z₁
        (hU₁U.trans hUN) hsq hcomm (hKG.trans hG₁Z) hKU
        (P := T ⊓ Subgroup.normalizer (U₁ : Set G)) (inf_le_left.trans hTZ) inf_le_right
        (inf_le_left.trans hTK) (hT2.to_le inf_le_left) hcard hperf hQ hA
    · exact Der6C.exists_fixed_not_centralized_of_irred hdec.Z₁
        (hU₁U.trans hUN) hsq hcomm (hKG.trans hG₁Z) hKU
        (P := T ⊓ Subgroup.normalizer (U₁ : Set G)) (inf_le_left.trans hTZ) inf_le_right
        (hT2.to_le inf_le_left) hirr hperf
  have huG : u ∈ mcOf T := S.mem_mcOf_of_mem_conjClosure hG (hU₁U hu)
  refine ⟨u, Or.inl ⟨hC2, hu, fun hle => ?_, fun t ht => ?_⟩⟩
  · have h1 := Subgroup.commutator_le.mp hle u (Subgroup.mem_zpowers u) k hk
    apply hnk
    have e : k * u * k⁻¹ * u⁻¹ = (u * k * u⁻¹ * k⁻¹)⁻¹ := by group
    rw [e]
    exact (quasithinOmegaOneCenter T).inv_mem (by simpa [commutatorElement_def] using h1)
  · exact (S146T.mem_tZero_iff huG).mpr ⟨ht.1, by simpa [commutatorElement_def] using hP t ht⟩

end CFSG.Quasithin
