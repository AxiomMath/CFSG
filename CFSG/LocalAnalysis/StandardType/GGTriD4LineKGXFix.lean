module

public import CFSG.LocalAnalysis.StandardType.GGTriD4LineKGXLang
public import CFSG.LocalAnalysis.StandardType.GGTriD4LineKGXFixedTorus

public section

namespace CFSG.StandardType

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartOne.KGD

@[expose] noncomputable def triD4LineH1
    (K : Type) [Field K] (σ : K ≃+* K) :
    Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :=
  (graphFixedRootTorus TwistTag.D4 K σ.toRingHom).subgroupOf
    (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)

@[expose] noncomputable def triD4LineNR
    (K : Type) [Field K] (σ : K ≃+* K) (L : Type) [Field L]
    [Algebra K L] : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :=
  (d4A2Qv L triD4LineV).comap (triEmb K σ L)

@[expose] noncomputable def triD4LineZ0
    (K : Type) [Field K] (σ : K ≃+* K) (ω : Kˣ)
    (hz : trialityOuterTorus K σ ω ∈ graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
    graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
  ⟨trialityOuterTorus K σ ω, hz⟩

theorem triD4Line_centralizer_z0_eq
    {n : ℕ} (K : Type) [Field K] (hK : Nat.card K = (2 ^ n) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ 2 ^ n) (ω : Kˣ) (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1)
    (hz : trialityOuterTorus K σ ω ∈ graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
    (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] :
    Subgroup.centralizer {triD4LineZ0 K σ ω hz} = triD4LineH1 K σ ⊔ triD4LineNR K σ L := by
  haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  letI : Fintype K := Fintype.ofFinite K
  have hcard : ∀ c : K, c ^ Nat.card K = c := fun c => by
    rw [Nat.card_eq_fintype_card]
    exact FiniteField.pow_card c
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · exfalso
      have h1 : Nat.card K = 1 := by rw [hK, hn]; norm_num
      have hsub : Subsingleton K := (Nat.card_eq_one_iff_unique.1 h1).1
      exact zero_ne_one (Subsingleton.elim (0 : K) 1)
    · exact hn
  have hq : 2 ≤ 2 ^ n := by
    have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) hn
    simpa using this
  haveI : CharP K 2 := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact charP_of_card_eq_prime_pow (p := 2) (f := n * 3)
      (by rw [← Nat.card_eq_fintype_card, hK, ← pow_mul])
  haveI : CharP L 2 := charP_of_injective_algebraMap (algebraMap K L).injective 2
  haveI : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have hσ3 : σ ^ 3 = 1 := by
    ext c
    rw [ringEquiv_pow_three_apply]
    have hiter : σ (σ (σ c)) = c ^ Nat.card K := by
      rw [hσ, hσ, hσ]
      calc ((c ^ 2 ^ n) ^ 2 ^ n) ^ 2 ^ n
          = (c ^ 2 ^ n) ^ (2 ^ n * 2 ^ n) := (pow_mul _ _ _).symm
        _ = c ^ (2 ^ n * (2 ^ n * 2 ^ n)) := (pow_mul _ _ _).symm
        _ = c ^ (2 ^ n) ^ 3 := by congr 1; ring
        _ = c ^ Nat.card K := by rw [hK]
    rw [hiter]
    simpa using hcard c
  have h3 : ∀ c, σ (σ (σ c)) = c := by
    intro c
    rw [← ringEquiv_pow_three_apply σ c, hσ3]
    rfl
  have hΓ : CFSG.Blueprint.twistedFixedGroup TwistTag.D4 K σ.toRingHom =
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
    (even_triality_fixed_group_eq_root_group K (ringChar.eq K 2) σ h3).1
  let Fr : L →+* L := iterateFrobenius L 2 n
  have hFr : ∀ c, Fr c = c ^ 2 ^ n := fun c => iterateFrobenius_def 2 n c
  have hcomm : (algebraMap K L).comp σ.toRingHom = Fr.comp (algebraMap K L) := by
    ext x
    simp only [RingHom.comp_apply]
    change algebraMap K L (σ x) = Fr (algebraMap K L x)
    rw [hσ, hFr, map_pow]
  let A : Lˣ := Units.map (algebraMap K L).toMonoidHom (ω ^ 2)
  have hA3 : A ^ 3 = 1 := by
    change (Units.map (algebraMap K L).toMonoidHom (ω ^ 2)) ^ 3 = 1
    rw [← map_pow]
    rw [show (ω ^ 2 : Kˣ) ^ 3 = 1 by
      calc (ω ^ 2 : Kˣ) ^ 3 = ω ^ (2 * 3) := (pow_mul ω 2 3).symm
        _ = ω ^ (3 * 2) := by rw [show 2 * 3 = 3 * 2 by norm_num]
        _ = (ω ^ 3) ^ 2 := pow_mul ω 3 2
        _ = 1 := by rw [hω3, one_pow]]
    exact map_one _
  have hA1 : A ≠ 1 := by
    intro h
    apply hω1
    have h2 : (ω ^ 2 : Kˣ) = 1 :=
      Units.ext ((algebraMap K L).injective (by
        have h' := congrArg Units.val h
        simpa [A] using h'))
    have hωeq : ω ^ 3 = ω := by
      calc ω ^ 3 = ω ^ 2 * ω := by rw [show (3 : ℕ) = 2 + 1 by norm_num, pow_succ]
        _ = 1 * ω := by rw [h2]
        _ = ω := one_mul ω
    rw [← hωeq, hω3]
  have hmid : trialityMiddleTorus K σ (1 : (trialityFixedField K σ.toRingHom)ˣ) = 1 := by
    rw [trialityMiddleTorus]
    exact CFSG.Blueprint.Chevalley.torusElt_one ⟨2, by decide⟩
  have hzT : trialityOuterTorus K σ ω ∈ torusGroup TwistTag.D4.tag K := by
    have h := trialityTorusHom_mem_graphFixedTorus (σ := σ) hσ3 (ω, 1)
    rw [trialityTorusHom_apply, hmid, mul_one] at h
    exact (Subgroup.mem_inf.1 h).1
  have hz0ι : triEmb K σ L (triD4LineZ0 K σ ω hz) = rootDiagUnit TwistTag.D4.tag ![A, A, 1, A] := by
    obtain ⟨hz', -, -, hιz'⟩ := triD4Line_trialityOuterTorus_z0 (K := K) (σ := σ) hσ3 ω hω3 hω1
    have hz_eq : triD4LineZ0 K σ ω hz = ⟨trialityOuterTorus K σ ω, hz'⟩ := Subtype.ext rfl
    have hιz := hιz' L
    rw [← hz_eq] at hιz
    exact hιz
  have hQvTc : d4A2Qv L triD4LineV ≤ toralCentralizer TwistTag.D4.tag L ![A, A, 1, A] :=
    (triD4Line_toralCentralizer_z0 L A hA3 hA1).2.2.2.1
  apply le_antisymm
  · intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff] at hy
    have hyι : triEmb K σ L y * triEmb K σ L (triD4LineZ0 K σ ω hz) =
        triEmb K σ L (triD4LineZ0 K σ ω hz) * triEmb K σ L y := by
      rw [← map_mul, ← map_mul, hy]
    have hmem_adj : triEmb K σ L y ∈ adjointGroup TwistTag.D4.tag L := triEmb_mem_adjointGroup y
    have hmem_cent : triEmb K σ L y ∈
        Subgroup.centralizer {rootDiagUnit TwistTag.D4.tag ![A, A, 1, A]} := by
      rw [Subgroup.mem_centralizer_singleton_iff, ← hz0ι]
      exact hyι
    have hmem_tc : triEmb K σ L y ∈ toralCentralizer TwistTag.D4.tag L ![A, A, 1, A] :=
      Subgroup.mem_inf.2 ⟨hmem_adj, hmem_cent⟩
    have hΦy : twistHom TwistTag.D4 L Fr (triEmb K σ L y) = triEmb K σ L y :=
      triEmb_fixed Fr hcomm y
    obtain ⟨h, hhT, hhF, m, hmQ, hmF, heq⟩ :=
      triD4Line_fixed_mul_Qv L (2 ^ n) hq Fr hFr A hA3 hA1
        (triEmb K σ L y) hmem_tc hΦy
    obtain ⟨p, hp⟩ :=
      triD4Line_exists_trialityTorusHom_baseChange (n := n) K hK σ hσ L Fr hFr h hhT hhF
    have hgramT : trialityTorusHom σ p ∈ graphFixedTorus TwistTag.D4 K σ.toRingHom :=
      trialityTorusHom_mem_graphFixedTorus (σ := σ) hσ3 p
    have hgram : trialityTorusHom σ p ∈ graphFixedRootGroup TwistTag.D4 K σ.toRingHom := by
      rw [← hΓ]
      exact (Subgroup.mem_inf.1 hgramT).2
    let h₁ : graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
      ⟨trialityTorusHom σ p, hgram⟩
    have hh₁_mem : h₁ ∈ triD4LineH1 K σ := by
      rw [triD4LineH1]
      exact Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.2 ⟨hgramT, hgram⟩)
    have hιh₁ : triEmb K σ L h₁ = h := by
      rw [triEmb_apply]
      change baseChangeGL (algebraMap K L) (trialityTorusHom σ p) = h
      exact hp
    have hrange := triEmb_range (K := K) (σ := σ) (L := L) (ℓ := 2) (f := n)
      Nat.prime_two hn hK hσ Fr hFr
    have hm_adj : m ∈ adjointGroup TwistTag.D4.tag L := (Subgroup.mem_inf.1 (hQvTc hmQ)).1
    have hm_eqLocus : m ∈ (twistHom TwistTag.D4 L Fr).eqLocus (MonoidHom.id _) := by
      change twistHom TwistTag.D4 L Fr m = (MonoidHom.id _) m
      simpa using hmF
    have hm_range : m ∈ (triEmb K σ L).range :=
      hrange ▸ Subgroup.mem_inf.mpr ⟨hm_adj, hm_eqLocus⟩
    obtain ⟨nn, hnn⟩ := MonoidHom.mem_range.1 hm_range
    have hnnNR : nn ∈ triD4LineNR K σ L :=
      Subgroup.mem_comap.mpr (hnn ▸ hmQ)
    have hy_eq : y = h₁ * nn := by
      apply (triEmb_injective (K := K) (σ := σ) (L := L))
      rw [map_mul, hιh₁, heq]
      exact congrArg (fun z : ModGL Tag.D4 L => (show ModGL Tag.D4 L from h) * z)
        (show m = (triEmb K σ L) nn from hnn.symm)
    rw [hy_eq]
    exact Subgroup.mul_mem_sup hh₁_mem hnnNR
  · apply sup_le
    · intro x hx
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply Subtype.ext
      have hxroot : (x : ModGL TwistTag.D4.tag K) ∈ graphFixedRootTorus TwistTag.D4 K σ.toRingHom :=
        Subgroup.mem_subgroupOf.1 hx
      have hxT : (x : ModGL TwistTag.D4.tag K) ∈ torusGroup TwistTag.D4.tag K :=
        (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hxroot).1).1
      exact torusGroup_mul_comm hxT hzT
    · intro x hx
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hxQ : triEmb K σ L x ∈ d4A2Qv L triD4LineV := Subgroup.mem_comap.1 hx
      have hxTc : triEmb K σ L x ∈ toralCentralizer TwistTag.D4.tag L ![A, A, 1, A] := hQvTc hxQ
      have hxCent : triEmb K σ L x ∈
          Subgroup.centralizer {rootDiagUnit TwistTag.D4.tag ![A, A, 1, A]} :=
        (Subgroup.mem_inf.1 hxTc).2
      rw [Subgroup.mem_centralizer_singleton_iff] at hxCent
      rw [← hz0ι] at hxCent
      apply (triEmb_injective (K := K) (σ := σ) (L := L))
      rw [map_mul, map_mul]
      exact hxCent

end CFSG.StandardType
