module

public import CFSG.RankThree.PartTwo.Sec10.Step1012ClaimKProof
import CFSG.RankThree.PartTwo.Sec10.Item1012Res2ProofTools
public import CFSG.RankThree.PartTwo.Sec10.Step1012ClaimProofAut
public import CFSG.RankThree.PartTwo.Sec10.Step1012ClaimProofLift
public import CFSG.RankThree.PartTwo.Sec10.Step1012ClaimProofSe
import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.RankThree.PartTwo.Sec10

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

@[expose] def KS1012GL34Inf : Prop :=
  ∀ (S : Type) [Group S] [Finite S], (∀ s t : S, s * t = t * s) → (∀ s : S, s ^ 2 = 1) →
    ∀ (Y : Subgroup (MulAut S)) (z x w : MulAut S), z ∈ Y → x ∈ Y → w ∈ Y →
      (∀ y ∈ Y, y * z = z * y) → z ^ 3 = 1 → (∀ s : S, z s = s → s = 1) →
      x ^ 3 = 1 → Nat.card {s : S // x s = s} = 4 → w * x * w⁻¹ = x * z →
      (Sec4.IsSLThreePiAt (inSubgroup perfectResidual Y) 4 ∨
        Sec4.IsTripleCover (inSubgroup perfectResidual Y) (alternatingGroup (Fin 6))) →
      x ∈ inSubgroup perfectResidual Y

@[expose] def Step1012KAutCover : Prop :=
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
      ∃ K ∈ thetaComponentsIn
          (Subgroup.centralizer ((Subgroup.closure {a, d} : Subgroup G) : Set G)),
        (Sec4.IsSLThreePiAt (K ⧸ aschbacherSolvableCore 3 K) 4 ∨
          Sec4.IsTripleCover (K ⧸ aschbacherSolvableCore 3 K) (alternatingGroup (Fin 6))) ∧
        inSubgroup perfectResidual (Sec4.autIn
          (Subgroup.centralizer ((Subgroup.closure {a, d} : Subgroup G) : Set G)) S) ≤
          Sec4.autIn K S

namespace Item1012Res2Proof

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
  {R : Subgroup G}

theorem c_mem_perfectResidual (hInf : KS1012GL34Inf) (h : Sec10Std G A c L a R)
    {d : G} (hdL : A ⊓ L = Subgroup.zpowers d) {S : Subgroup G}
    (hSab : IsMulCommutative S) (hSpow : ∀ s ∈ S, s ^ 2 = 1)
    (hSA : A ≤ Subgroup.normalizer (S : Set G))
    (hSc : S ⊓ Subgroup.centralizer ({c} : Set G) = sec10U L a)
    (hSd : S ⊓ Subgroup.centralizer ({d} : Set G) = ⊥) {w : G}
    (hwS : w ∈ Subgroup.normalizer (S : Set G)) (hwa : w * a * w⁻¹ = a)
    (hwd : w * d * w⁻¹ = d) (hwc : w * c * w⁻¹ = c * d)
    (hauto : Sec4.IsSLThreePiAt (inSubgroup perfectResidual (Sec4.autIn
        (Subgroup.centralizer ((Subgroup.closure {a, d} : Subgroup G) : Set G)) S)) 4 ∨
      Sec4.IsTripleCover (inSubgroup perfectResidual (Sec4.autIn
        (Subgroup.centralizer ((Subgroup.closure {a, d} : Subgroup G) : Set G)) S))
        (alternatingGroup (Fin 6))) :
    S.normalizerMonoidHom ⟨c, hSA h.mem_A⟩ ∈ inSubgroup perfectResidual (Sec4.autIn
      (Subgroup.centralizer ((Subgroup.closure {a, d} : Subgroup G) : Set G)) S) := by
  have hdA := h.d_mem_A hdL
  set CB := Subgroup.centralizer ((Subgroup.closure {a, d} : Subgroup G) : Set G) with hCB
  set Y := Sec4.autIn CB S with hY
  set φ := S.normalizerMonoidHom with hφ
  have hφapp : ∀ {g : G} (hg : g ∈ Subgroup.normalizer (S : Set G)) (s : S),
      ((φ ⟨g, hg⟩ s : S) : G) = g * s * g⁻¹ := fun hg s =>
    Sec4.normalizerMonoidHom_apply_coe hg s
  have hdN : d ∈ Subgroup.normalizer (S : Set G) := hSA hdA
  have hcN : c ∈ Subgroup.normalizer (S : Set G) := hSA h.mem_A
  have hdCB : d ∈ CB :=
    Step1012ClaimProof.mem_centralizer_closure_pair_iff.mpr ⟨h.comm hdA h.a_mem, rfl⟩
  have hcCB : c ∈ CB := Step1012ClaimProof.mem_centralizer_closure_pair_iff.mpr
    ⟨h.comm h.mem_A h.a_mem, h.comm h.mem_A hdA⟩
  have hwCB : w ∈ CB := by
    refine Step1012ClaimProof.mem_centralizer_closure_pair_iff.mpr ⟨?_, ?_⟩
    · calc w * a = w * a * w⁻¹ * w := by group
        _ = a * w := by rw [hwa]
    · calc w * d = w * d * w⁻¹ * w := by group
        _ = d * w := by rw [hwd]
  set z := φ ⟨d, hdN⟩ with hz
  set x := φ ⟨c, hcN⟩ with hx
  set w' := φ ⟨w, hwS⟩ with hw'
  have hzY : z ∈ Y := Sec4.mem_autIn_iff.mpr ⟨d, hdN, hdCB, rfl⟩
  have hxY : x ∈ Y := Sec4.mem_autIn_iff.mpr ⟨c, hcN, hcCB, rfl⟩
  have hwY : w' ∈ Y := Sec4.mem_autIn_iff.mpr ⟨w, hwS, hwCB, rfl⟩
  have hzc : ∀ y ∈ Y, y * z = z * y := by
    intro y hy
    obtain ⟨g, hgN, hgCB, rfl⟩ := Sec4.mem_autIn_iff.mp hy
    rw [hz, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Step1012ClaimProof.mem_centralizer_closure_pair_iff.mp hgCB).2
  have hz3 : z ^ 3 = 1 := by
    rw [hz, ← map_pow]
    have : (⟨d, hdN⟩ : Subgroup.normalizer (S : Set G)) ^ 3 = 1 :=
      Subtype.ext (by simpa using h.pow_three hdA)
    rw [this, map_one]
  have hzfix : ∀ s : S, z s = s → s = 1 := by
    intro s hs
    have h1 := congrArg Subtype.val hs
    rw [hz, hφapp] at h1
    have hsd : (s : G) * d = d * s := by
      calc (s : G) * d = d * s * d⁻¹ * d := by rw [h1]
        _ = d * s := by group
    have hmem : (s : G) ∈ S ⊓ Subgroup.centralizer ({d} : Set G) :=
      ⟨s.2, Subgroup.mem_centralizer_singleton_iff.mpr hsd⟩
    rw [hSd, Subgroup.mem_bot] at hmem
    exact Subtype.ext hmem
  have hx3 : x ^ 3 = 1 := by
    rw [hx, ← map_pow]
    have : (⟨c, hcN⟩ : Subgroup.normalizer (S : Set G)) ^ 3 = 1 :=
      Subtype.ext (by simpa using h.pow_three h.mem_A)
    rw [this, map_one]
  have hxfix : ∀ s : S, x s = s ↔ (s : G) ∈ Subgroup.centralizer ({c} : Set G) := by
    intro s
    rw [Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro hs
      have h1 := congrArg Subtype.val hs
      rw [hx, hφapp] at h1
      calc (s : G) * c = c * s * c⁻¹ * c := by rw [h1]
        _ = c * s := by group
    · intro hs
      apply Subtype.ext
      rw [hx, hφapp, ← hs, mul_inv_cancel_right]
  have hx4 : Nat.card {s : S // x s = s} = 4 := by
    rw [← (Sec10XSteps.sec10U_facts h).2.1, ← hSc]
    exact Nat.card_congr
      { toFun := fun s => ⟨s.1, s.1.2, (hxfix s.1).mp s.2⟩
        invFun := fun t => ⟨⟨t, t.2.1⟩, (hxfix ⟨t, t.2.1⟩).mpr t.2.2⟩
        left_inv := fun s => rfl
        right_inv := fun t => rfl }
  have hwx : w' * x * w'⁻¹ = x * z := by
    rw [hw', hx, hz, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hwc
  exact hInf S (fun s t => hSab.1.comm s t) (fun s => Subtype.ext (by simpa using hSpow s s.2))
    Y z x w' hzY hxY hwY hzc hz3 hzfix hx3 hx4 hwx hauto

end Item1012Res2Proof

open Item1012Res2Proof in
theorem step1012ClaimKd_of_autCover (hInf : KS1012GL34Inf) (hCov : Step1012KAutCover) :
    Step1012ClaimKd := by
  intro h45 h97 G _ _ A c L a R h d hdL hUθ hUmax S hS hUS hSc hSd hSab w hwA hwS hwa hwd hwc V
    hV2 hVA hVS hVB hVθU hVS' hVθ hauto hm3
  obtain ⟨K, hK, htype, hKcov⟩ := hCov h45 h97 G A c L a R h d hdL hUθ hUmax S hS hUS hSc hSd
    hSab w hwA hwS hwa hwd hwc V hV2 hVA hVS hVB hVθU hVS' hVθ hauto hm3
  refine ⟨K, hK, htype, ?_⟩
  set H := Subgroup.centralizer ((Subgroup.closure {a, d} : Subgroup G) : Set G) with hH
  have hmemH : ∀ y : G, y ∈ H ↔ y * a = a * y ∧ y * d = d * y := fun y =>
    Step1012ClaimProof.mem_centralizer_closure_pair_iff
  have hdA := h.d_mem_A hdL
  obtain ⟨⟨-, hS2', hSA⟩, -⟩ := mem_maxInvariantPiSubgroups_iff.mp hS
  have hS2 : IsPGroup 2 S := (isPiSubgroup_piOf_iff Nat.prime_two _).mp hS2'
  have hSpow := Step1012ClaimProof.pow_two_eq_one h97 h hdL hS2 hSab hSA hSc hSd hwS hwd hwc
  have hKH : K ≤ H := (mem_thetaComponentsIn_iff.mp hK).1
  have hcH : c ∈ H := (hmemH c).mpr ⟨h.comm h.mem_A h.a_mem, h.comm h.mem_A hdA⟩
  have hwa' : w * a = a * w := by
    calc w * a = w * a * w⁻¹ * w := by group
      _ = a * w := by rw [hwa]
  have hwH : w ∈ H := by
    refine (hmemH w).mpr ⟨hwa', ?_⟩
    calc w * d = w * d * w⁻¹ * w := by group
      _ = d * w := by rw [hwd]
  have hcN : c ∈ Subgroup.normalizer (S : Set G) := hSA h.mem_A
  have h27 : 27 ∣ Nat.card (inSubgroup perfectResidual (Sec4.autIn H S)) := by
    rcases hauto with h4 | h6
    · rw [Step1012ClaimProof.card_of_isSLThreePiAt_four h4]
      norm_num
    · rw [KFacts.KS14.card_eq_of_isExtOf_alternating_six h6.isExtOf]
      norm_num
  have h3 : 3 ∣ Nat.card (inSubgroup perfectResidual (Sec4.autIn H S)) :=
    (by norm_num : 3 ∣ 27).trans h27
  have hcK := mem_normalizer_of_le_autIn hK hKcov h3 hcH hcN
  have hwK := mem_normalizer_of_le_autIn hK hKcov h3 hwH hwS
  have hcInf := c_mem_perfectResidual hInf h hdL hSab hSpow hSA hSc hSd hwS hwa hwd hwc hauto
  obtain ⟨k, hkN, hkK, hk⟩ := Sec4.mem_autIn_iff.mp (hKcov hcInf)
  have hkc : k⁻¹ * c ∈ Subgroup.centralizer (S : Set G) := by
    have h1 : S.normalizerMonoidHom ((⟨k, hkN⟩ : Subgroup.normalizer (S : Set G))⁻¹ *
        ⟨c, hcN⟩) = 1 := by
      rw [map_mul, map_inv, hk, inv_mul_cancel]
    have h2 := (MonoidHom.mem_ker).mpr h1
    rw [Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf] at h2
    exact h2
  have hKC := not_three_dvd_card_inf_centralizer
    (h27.trans (Subgroup.card_dvd_of_le hKcov)) (not_dvd_card_of_type htype)
  have hKC' : ¬ 3 ∣ Nat.card (K ⊓ (Subgroup.centralizer (S : Set G) ⊓ H) : Subgroup G) := by
    intro h3'
    exact hKC (h3'.trans (Subgroup.card_dvd_of_le (inf_le_inf_left _ inf_le_left)))
  obtain ⟨k', hk'K, z, hz, hcz⟩ := exists_eq_mul_of_mem_normalizer
    (C := Subgroup.centralizer (S : Set G) ⊓ H) (Z := Subgroup.zpowers a) hcK hkK
    ⟨hkc, H.mul_mem (H.inv_mem (hKH hkK)) hcH⟩ (h.pow_three h.mem_A) hKC' hm3
  have hdeq : c⁻¹ * (w * c * w⁻¹) = d := by rw [hwc, inv_mul_cancel_left]
  rw [← hdeq]
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  refine inv_mul_conj_mem_of_eq_mul hwK hk'K hcz ?_ ?_
  · exact ((show Commute a w from hwa'.symm).zpow_left j).eq
  · intro x hx
    exact ((show Commute a x from ((hmemH x).mp (hKH hx)).1.symm).zpow_left j).eq

end CFSG.RankThree.PartTwo.Sec10
