module

public import CFSG.RankThree.PartOne.KE6.Tw6A2A2Case
public import CFSG.RankThree.PartOne.KE6.Tw6D4Case
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwInnerLineData
public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitTwE6SixDvdCard
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate122
public import Certificates.Certificate123
public import Certificates.Certificate3951
public import CFSG.RankThree.PartOne.KE.E8TwoA2Family

public noncomputable section

namespace CFSG.StandardType.TwE6Nonsplit

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6 CFSG.RankThree.Chevalley
  CFSG.RankThree.Classical2 CFSG.RankThree.PartOne.KE6
  CFSG.HardMathSupport.Lang.SeitzPlane CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
open CFSG.RankThree.PartOne.KE (twistedTorusOf mem_twistedTorusOf twistedFixedPoints
  mem_twistedFixedPoints)
open CFSG.RankThree.Lattice (e6T3W toMat lget)
open CFSG.HardMathSupport.Timmesfeld.LocalTwo.SeitzRows
open scoped Matrix MatrixGroups Pointwise


variable {Ω : Type} [Field Ω] {Fr : Ω →+* Ω}

theorem nat_dvd_phiSix_of_int {p q : ℕ} (hq : 1 ≤ q)
    (h : (p : ℤ) ∣ (q : ℤ) ^ 2 - (q : ℤ) + 1) : p ∣ q ^ 2 - q + 1 := by
  have h2 : q ≤ q ^ 2 := by nlinarith
  rw [← Int.natCast_dvd_natCast]
  have e : ((q ^ 2 - q + 1 : ℕ) : ℤ) = (q : ℤ) ^ 2 - (q : ℤ) + 1 := by
    zify [hq, h2]
  rw [e]
  exact h

private theorem tw6SixSwap_support56 :
    (((twE6FrameWeyl 2) * (twLineYW)⁻¹) • ·) '' parabolicRoots Tag.E6 support56 =
      parabolicRoots Tag.E6 support13 := by
  rw [← twLineYW_image_two, ← twE6FrameS_conj 2]
  have hcomp : ∀ T : Set (Fin Tag.E6.rank → ℤ),
      (((twE6FrameWeyl 2) * (twLineYW)⁻¹) • ·) '' (((twLineYW) • ·) '' T) =
        ((twE6FrameWeyl 2) • ·) '' T := by
    intro T
    ext α
    constructor
    · rintro ⟨β, ⟨γ, hγ, rfl⟩, rfl⟩
      exact ⟨γ, hγ, by simp [mul_smul]⟩
    · rintro ⟨γ, hγ, rfl⟩
      exact ⟨twLineYW • γ, ⟨γ, hγ, rfl⟩, by simp [mul_smul]⟩
  rw [hcomp]

theorem tw6_A2_kernelLayer_dvd {K : Type} [Field K] [Finite K] [Algebra K Ω]
    [IsAlgClosure K Ω] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP Ω ℓ] (hf : 1 ≤ f)
    (hK : Nat.card K = ℓ ^ f) (hq3 : 3 ≤ ℓ ^ f) (hFr : ∀ c, Fr c = c ^ (ℓ ^ f))
    {x : ModGL Tag.E6 Ω} (hx : x ∈ twistedTorusOf (tw6N Ω) (twistE6 Ω Fr))
    (hA2 : ∃ w : WeylGroup Tag.E6,
      (w • ·) '' torusRootKernel x = parabolicRoots Tag.E6 support13) {p : ℕ}
    (hpq : p ∣ Nat.card K ^ 2 - Nat.card K + 1) :
    ∃ KL : KernelLayer (tw6N Ω) (twistE6 Ω Fr) (torusRootKernel x) K Unit,
      ∀ i, p ∣ Nat.card ↥(KL.P i) := by
  obtain ⟨w, hw⟩ := hA2
  have hpq' : p ∣ (ℓ ^ f) ^ 2 - ℓ ^ f + 1 := by simpa [hK] using hpq
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  obtain ⟨hQ, hfin, hq, hcomm, h₀, hsl⟩ := tw6_A2_layer_gen hf hK hq3 hFr
    (fun α hα => hα.1) (tw6_torusRootKernel_smul_stable hFr hx) hw
  let KL : KernelLayer (tw6N Ω) (twistE6 Ω Fr) (torusRootKernel x) K Unit :=
    { P := fun _ => rootSpan Tag.E6 Ω (torusRootKernel x) ⊓
        twistedFixedPoints (tw6N Ω) (twistE6 Ω Fr)
      fin := fun _ => hfin
      quasi := fun _ => hq
      le_span := fun _ => inf_le_left
      le_fixed := fun _ => inf_le_right
      norm := fun _ y hy hyR u hu => by
        refine ⟨(Subgroup.mem_normalizer_iff.1
          (torusGroup_sup_rootSpan_le_normalizer' (fun α hα => hα.1) hy) u).1 hu.1, ?_⟩
        have hy' : tw6N Ω * twistE6 Ω Fr y * (tw6N Ω)⁻¹ = y :=
          mem_twistedFixedPoints.1 hyR
        have hu' : tw6N Ω * twistE6 Ω Fr u * (tw6N Ω)⁻¹ = u :=
          mem_twistedFixedPoints.1 hu.2
        refine mem_twistedFixedPoints.2 ?_
        rw [map_mul, map_mul, map_inv]
        calc tw6N Ω * (twistE6 Ω Fr y * twistE6 Ω Fr u * (twistE6 Ω Fr y)⁻¹) *
              (tw6N Ω)⁻¹ =
            (tw6N Ω * twistE6 Ω Fr y * (tw6N Ω)⁻¹) *
              (tw6N Ω * twistE6 Ω Fr u * (tw6N Ω)⁻¹) *
              (tw6N Ω * twistE6 Ω Fr y * (tw6N Ω)⁻¹)⁻¹ := by group
          _ = y * u * y⁻¹ := by rw [hy', hu']
      cent := fun y hy hc => hPcent_of_std (fun α hα => hα.1) hQ hcomm y hy
        (fun u hu => hc () u hu)
      comm := fun X hX g hg => by
        have hcomm' : e6Commutant (((rootSpan Tag.E6 Ω (torusRootKernel x) ⊓
            twistedFixedPoints (tw6N Ω) (twistE6 Ω Fr)).map
              (MulAut.conj (canonicalRep (coxeterSystem Tag.E6) Ω w)).toMonoidHom :
                Subgroup (ModGL Tag.E6 Ω)) : Set (ModGL Tag.E6 Ω)) =
            e6Commutant (subsystemGroup Tag.E6 Ω support13 : Set (ModGL Tag.E6 Ω)) := by
          simpa only [twistedFixedPoints_tw6N] using hcomm
        have hP : e6Commutant ((rootSpan Tag.E6 Ω (torusRootKernel x) ⊓
            twistedFixedPoints (tw6N Ω) (twistE6 Ω Fr) : Subgroup (ModGL Tag.E6 Ω)) :
              Set (ModGL Tag.E6 Ω)) =
            e6Commutant (rootSpan Tag.E6 Ω (torusRootKernel x) : Set (ModGL Tag.E6 Ω)) := by
          refine e6Commutant_eq_of_conj_eq (canonicalRep (coxeterSystem Tag.E6) Ω w) ?_
          have h1 : (fun g => canonicalRep (coxeterSystem Tag.E6) Ω w * g *
              (canonicalRep (coxeterSystem Tag.E6) Ω w)⁻¹) ''
                (rootSpan Tag.E6 Ω (torusRootKernel x) : Set (ModGL Tag.E6 Ω)) =
              (subsystemGroup Tag.E6 Ω support13 : Set (ModGL Tag.E6 Ω)) := by
            rw [← hQ, Subgroup.coe_map]
            rfl
          have h2 : (fun g => canonicalRep (coxeterSystem Tag.E6) Ω w * g *
              (canonicalRep (coxeterSystem Tag.E6) Ω w)⁻¹) ''
                ((rootSpan Tag.E6 Ω (torusRootKernel x) ⊓
                  twistedFixedPoints (tw6N Ω) (twistE6 Ω Fr) : Subgroup (ModGL Tag.E6 Ω)) :
                    Set (ModGL Tag.E6 Ω)) =
              (((rootSpan Tag.E6 Ω (torusRootKernel x) ⊓
                twistedFixedPoints (tw6N Ω) (twistE6 Ω Fr)).map
                  (MulAut.conj (canonicalRep (coxeterSystem Tag.E6) Ω w)).toMonoidHom :
                    Subgroup (ModGL Tag.E6 Ω)) : Set (ModGL Tag.E6 Ω)) := by
            rw [Subgroup.coe_map]
            rfl
          rw [h1, h2, hcomm']
        have hX' : X ∈ e6Commutant ((rootSpan Tag.E6 Ω (torusRootKernel x) ⊓
            twistedFixedPoints (tw6N Ω) (twistE6 Ω Fr) : Subgroup (ModGL Tag.E6 Ω)) :
              Set (ModGL Tag.E6 Ω)) := fun u hu => hX () u hu
        rw [hP] at hX'
        exact hX' g hg
      sl2 := fun _ => ⟨(), e6Index 0, h₀, hsl⟩ }
  refine ⟨KL, ?_⟩
  intro i
  change p ∣ Nat.card ↥(rootSpan Tag.E6 Ω (torusRootKernel x) ⊓
    twistedFixedPoints (tw6N Ω) (twistE6 Ω Fr))
  rw [tw6_A2_layer_card (K := K) (Ω := Ω) (Fr := Fr) hf hK hFr
    (fun α hα => hα.1) (tw6_torusRootKernel_smul_stable hFr hx) hw]
  exact dvd_card_SU3_of_dvd hpq'

theorem tw6_A2A2_kernelLayer_dvd {K : Type} [Field K] [Finite K] [Algebra K Ω]
    [IsAlgClosure K Ω] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP Ω ℓ] (hf : 1 ≤ f)
    (hK : Nat.card K = ℓ ^ f) (hq3 : 3 ≤ ℓ ^ f) (hFr : ∀ c, Fr c = c ^ (ℓ ^ f))
    {x : ModGL Tag.E6 Ω} (hx : x ∈ twistedTorusOf (tw6N Ω) (twistE6 Ω Fr))
    (hA : ∃ w : WeylGroup Tag.E6,
      (w • ·) '' torusRootKernel x = parabolicRoots Tag.E6 supportA2A2) {p : ℕ}
    (hpq : p ∣ Nat.card K ^ 2 - Nat.card K + 1) :
    ∃ KL : KernelLayer (tw6N Ω) (twistE6 Ω Fr) (torusRootKernel x) K (Fin 2),
      ∀ i, p ∣ Nat.card ↥(KL.P i) := by
  classical
  obtain ⟨w, hw⟩ := hA
  have hpq' : p ∣ (ℓ ^ f) ^ 2 - ℓ ^ f + 1 := by simpa [hK] using hpq
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  have hℓ : ℓ.Prime := Fact.out
  set Sx := torusRootKernel x with hSxdef
  set n := canonicalRep (coxeterSystem Tag.E6) Ω w with hn
  have hvS := tw6_torusRootKernel_smul_stable hFr hx
  have hT : ∀ β ∈ parabolicRoots Tag.E6 supportA2A2,
      (w * e6T3W * w⁻¹) • β ∈ parabolicRoots Tag.E6 supportA2A2 := by
    intro β hβ
    rw [← hw] at hβ ⊢
    obtain ⟨α, hα, rfl⟩ := hβ
    exact ⟨e6T3W • α, hvS α hα, by simp [mul_smul]⟩
  obtain ⟨L, hL, hLT⟩ := weylMatrix_conj_e6T3W_mem_orbit w
  have hcolJ : ∀ j ∈ supportA2A2, ∀ i ∉ supportA2A2, lget L i j = 0 := by
    intro j hj i hi
    have hsingle : (Pi.single j 1 : Fin Tag.E6.rank → ℤ) ∈
        parabolicRoots Tag.E6 supportA2A2 :=
      ⟨isRoot_single Tag.E6 j, fun i' hi' => Pi.single_eq_of_ne (fun h => hi' (by rw [h]; exact hj)) 1⟩
    have h := (hT _ hsingle).2 i hi
    rw [smul_single_apply_eq_lget hLT] at h
    exact h
  have hmemJ : ∀ j : Fin Tag.E6.rank, (j = 0 ∨ j = 2 ∨ j = 4 ∨ j = 5) → j ∈ supportA2A2 := by
    intro j hj
    rw [mem_supportA2A2]
    exact hj
  have hnJ : ∀ i : Fin Tag.E6.rank, (i = 1 ∨ i = 3) → i ∉ supportA2A2 := by
    intro i hi hmem
    rw [mem_supportA2A2] at hmem
    revert hi hmem
    revert i
    decide
  obtain ⟨hblk, hA13, hA56⟩ := e6T3Orbit_A2A2_shape L hL
    ⟨hcolJ 0 (hmemJ 0 (Or.inl rfl)) 1 (hnJ 1 (Or.inl rfl)),
      hcolJ 0 (hmemJ 0 (Or.inl rfl)) 3 (hnJ 3 (Or.inr rfl)),
      hcolJ 2 (hmemJ 2 (Or.inr (Or.inl rfl))) 1 (hnJ 1 (Or.inl rfl)),
      hcolJ 2 (hmemJ 2 (Or.inr (Or.inl rfl))) 3 (hnJ 3 (Or.inr rfl)),
      hcolJ 4 (hmemJ 4 (Or.inr (Or.inr (Or.inl rfl)))) 1 (hnJ 1 (Or.inl rfl)),
      hcolJ 4 (hmemJ 4 (Or.inr (Or.inr (Or.inl rfl)))) 3 (hnJ 3 (Or.inr rfl)),
      hcolJ 5 (hmemJ 5 (Or.inr (Or.inr (Or.inr rfl)))) 1 (hnJ 1 (Or.inl rfl)),
      hcolJ 5 (hmemJ 5 (Or.inr (Or.inr (Or.inr rfl)))) 3 (hnJ 3 (Or.inr rfl))⟩
  obtain ⟨hb40, hb50, hb42, hb52, hb04, hb24, hb05, hb25⟩ := hblk
  have hcol13 : ∀ j ∈ support13, ∀ i ∉ support13, lget L i j = 0 := by
    intro j hj i hi
    have hj' : j = e6Index 0 ∨ j = e6Index 2 := hj
    by_cases hiJ : i ∈ supportA2A2
    · rw [mem_supportA2A2] at hiJ
      rcases hj' with rfl | rfl <;> rcases hiJ with rfl | rfl | rfl | rfl <;>
        first
        | exact absurd (Or.inl rfl) hi
        | exact absurd (Or.inr rfl) hi
        | assumption
    · refine hcolJ j ?_ i hiJ
      rw [mem_supportA2A2]
      rcases hj' with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
  have hcol56 : ∀ j ∈ support56, ∀ i ∉ support56, lget L i j = 0 := by
    intro j hj i hi
    have hj' : j = e6Index 4 ∨ j = e6Index 5 := hj
    by_cases hiJ : i ∈ supportA2A2
    · rw [mem_supportA2A2] at hiJ
      rcases hj' with rfl | rfl <;> rcases hiJ with rfl | rfl | rfl | rfl <;>
        first
        | exact absurd (Or.inl rfl) hi
        | exact absurd (Or.inr rfl) hi
        | assumption
    · refine hcolJ j ?_ i hiJ
      rw [mem_supportA2A2]
      rcases hj' with h | h
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr h))
  have hT13 : ∀ β ∈ parabolicRoots Tag.E6 support13,
      (w * e6T3W * w⁻¹) • β ∈ parabolicRoots Tag.E6 support13 := fun β hβ =>
    smul_mem_parabolicRoots_of_lget hLT hcol13 hβ
  have hT56 : ∀ β ∈ parabolicRoots Tag.E6 support56,
      (w * e6T3W * w⁻¹) • β ∈ parabolicRoots Tag.E6 support56 := fun β hβ =>
    smul_mem_parabolicRoots_of_lget hLT hcol56 hβ
  set S₁ : Set (Fin Tag.E6.rank → ℤ) :=
    (fun α => w⁻¹ • α) '' parabolicRoots Tag.E6 support13 with hS₁
  set S₂ : Set (Fin Tag.E6.rank → ℤ) :=
    (fun α => w⁻¹ • α) '' parabolicRoots Tag.E6 support56 with hS₂
  have hw₁ : (w • ·) '' S₁ = parabolicRoots Tag.E6 support13 := by
    rw [hS₁, Set.image_image]
    simp
  have hw₂ : (w • ·) '' S₂ = parabolicRoots Tag.E6 support56 := by
    rw [hS₂, Set.image_image]
    simp
  have hS₁roots : ∀ α ∈ S₁, IsRoot Tag.E6 α := by
    rintro _ ⟨β, hβ, rfl⟩
    exact IsRoot.smul hβ.1 w⁻¹
  have hS₂roots : ∀ α ∈ S₂, IsRoot Tag.E6 α := by
    rintro _ ⟨β, hβ, rfl⟩
    exact IsRoot.smul hβ.1 w⁻¹
  have hvS₁ : ∀ α ∈ S₁, e6T3W • α ∈ S₁ := by
    rintro _ ⟨β, hβ, rfl⟩
    exact ⟨(w * e6T3W * w⁻¹) • β, hT13 β hβ, by simp [mul_smul]⟩
  have hvS₂ : ∀ α ∈ S₂, e6T3W • α ∈ S₂ := by
    rintro _ ⟨β, hβ, rfl⟩
    exact ⟨(w * e6T3W * w⁻¹) • β, hT56 β hβ, by simp [mul_smul]⟩
  have h13A : support13 ⊆ supportA2A2 := fun i hi => by
    rw [mem_supportA2A2]
    have hi' : i = e6Index 0 ∨ i = e6Index 2 := hi
    rcases hi' with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  have h56A : support56 ⊆ supportA2A2 := fun i hi => by
    rw [mem_supportA2A2]
    have hi' : i = e6Index 4 ∨ i = e6Index 5 := hi
    rcases hi' with h | h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
  have hsub : ∀ {J : Set (Fin Tag.E6.rank)}, J ⊆ supportA2A2 →
      (fun α => w⁻¹ • α) '' parabolicRoots Tag.E6 J ⊆ Sx := by
    intro J hJ
    rintro _ ⟨β, hβ, rfl⟩
    have hβJ : β ∈ parabolicRoots Tag.E6 supportA2A2 :=
      ⟨hβ.1, fun i hi => hβ.2 i (fun hiJ => hi (hJ hiJ))⟩
    rw [← hw] at hβJ
    obtain ⟨α, hα, rfl⟩ := hβJ
    simpa using hα
  have hQ : (rootSpan Tag.E6 Ω Sx).map (MulAut.conj n).toMonoidHom =
      subsystemGroup Tag.E6 Ω supportA2A2 := by
    rw [(canonical_weyl_root_transport Tag.E6 Ω).1 w Sx (fun α hα => hα.1), hw,
      subsystemGroup_eq_rootSpan]
  obtain ⟨hQ₁, hfin₁, hq₁, hcomm₁, h₀, hsl₁⟩ := tw6_A2_layer_gen hf hK hq3 hFr hS₁roots hvS₁ hw₁
  obtain ⟨hQ₂, hfin₂, hq₂, hcomm₂, -⟩ := tw6_A2_layer_gen₂ hf hK hq3 hFr hS₂roots hvS₂ hw₂
  have hsep₁₂ : CFSG.RankThree.Lattice.IsSeparated support13 support56 := by
    intro a ha b hb
    have ha' : a = e6Index 0 ∨ a = e6Index 2 := ha
    have hb' : b = e6Index 4 ∨ b = e6Index 5 := hb
    rcases ha' with rfl | rfl <;> rcases hb' with rfl | rfl <;> decide
  have hsep₂₁ : CFSG.RankThree.Lattice.IsSeparated support56 support13 := by
    intro a ha b hb
    have ha' : a = e6Index 4 ∨ a = e6Index 5 := ha
    have hb' : b = e6Index 0 ∨ b = e6Index 2 := hb
    rcases ha' with rfl | rfl <;> rcases hb' with rfl | rfl <;> decide
  have hunion : supportA2A2 = support13 ∪ support56 := by
    ext i
    rw [mem_supportA2A2]
    constructor
    · rintro (h | h | h | h)
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr h)
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    · rintro (h | h)
      · have h' : i = e6Index 0 ∨ i = e6Index 2 := h
        rcases h' with h' | h'
        · exact Or.inl h'
        · exact Or.inr (Or.inl h')
      · have h' : i = e6Index 4 ∨ i = e6Index 5 := h
        rcases h' with h' | h'
        · exact Or.inr (Or.inr (Or.inl h'))
        · exact Or.inr (Or.inr (Or.inr h'))
  set P₁ : Subgroup (ModGL Tag.E6 Ω) := rootSpan Tag.E6 Ω S₁ ⊓
    twistedFixedPoints (tw6N Ω) (twistE6 Ω Fr) with hP₁
  set P₂ : Subgroup (ModGL Tag.E6 Ω) := rootSpan Tag.E6 Ω S₂ ⊓
    twistedFixedPoints (tw6N Ω) (twistE6 Ω Fr) with hP₂
  have hle : ∀ k : Fin 2, ((![P₁, P₂] k).map (MulAut.conj n).toMonoidHom) ≤
      subsystemGroup Tag.E6 Ω (![support13, support56] k) := by
    rw [Fin.forall_fin_two]
    exact ⟨hQ₁ ▸ Subgroup.map_mono inf_le_left, hQ₂ ▸ Subgroup.map_mono inf_le_left⟩
  have hC : ∀ k : Fin 2, e6Commutant ((((![P₁, P₂] k).map (MulAut.conj n).toMonoidHom :
      Subgroup (ModGL Tag.E6 Ω)) : Set (ModGL Tag.E6 Ω))) =
      e6Commutant (subsystemGroup Tag.E6 Ω (![support13, support56] k) :
        Set (ModGL Tag.E6 Ω)) := by
    rw [Fin.forall_fin_two]
    exact ⟨hcomm₁, hcomm₂⟩
  have hsep : ∀ k l : Fin 2, k ≠ l → CFSG.RankThree.Lattice.IsSeparated
      (![support13, support56] k) (![support13, support56] l) := by
    intro k l hkl
    fin_cases k <;> fin_cases l
    · exact absurd rfl hkl
    · exact hsep₁₂
    · exact hsep₂₁
    · exact absurd rfl hkl
  have hJ : supportA2A2 = ⋃ k, ![support13, support56] k := by
    rw [hunion]
    ext i
    simp [Set.mem_iUnion, Fin.exists_fin_two]
  obtain ⟨-, μ, -, hμrange, hμcomm, -, -⟩ := CFSG.RankThree.Lattice.e6_product_layers
    (Ω := Ω) supportA2A2 ![support13, support56]
    (fun k => (![P₁, P₂] k).map (MulAut.conj n).toMonoidHom) hsep hJ hle hC
  have hcommP : e6Commutant ((((⨆ k : Fin 2, ![P₁, P₂] k).map (MulAut.conj n).toMonoidHom :
      Subgroup (ModGL Tag.E6 Ω)) : Set (ModGL Tag.E6 Ω))) =
      e6Commutant (subsystemGroup Tag.E6 Ω supportA2A2 : Set (ModGL Tag.E6 Ω)) := by
    rw [Subgroup.map_iSup, ← hμrange]
    exact hμcomm
  have hspan : ∀ k : Fin 2, ![P₁, P₂] k ≤ rootSpan Tag.E6 Ω Sx := by
    rw [Fin.forall_fin_two]
    exact ⟨inf_le_left.trans (rootSpan_mono (hsub h13A)),
      inf_le_left.trans (rootSpan_mono (hsub h56A))⟩
  have hfix : ∀ k : Fin 2, ![P₁, P₂] k ≤
      twistedFixedPoints (tw6N Ω) (twistE6 Ω Fr) := by
    rw [Fin.forall_fin_two]
    exact ⟨inf_le_right, inf_le_right⟩
  have hfinF : ∀ k : Fin 2, Finite ↥(![P₁, P₂] k) := by
    rw [Fin.forall_fin_two]
    exact ⟨hfin₁, hfin₂⟩
  have hqF : ∀ k : Fin 2, CFSG.IsQuasisimple ↥(![P₁, P₂] k) := by
    rw [Fin.forall_fin_two]
    exact ⟨hq₁, hq₂⟩
  have hnormF : ∀ k : Fin 2, ∀ y ∈ torusGroup Tag.E6 Ω ⊔ rootSpan Tag.E6 Ω Sx,
      y ∈ twistedFixedPoints (tw6N Ω) (twistE6 Ω Fr) →
      ∀ u ∈ ![P₁, P₂] k, y * u * y⁻¹ ∈ ![P₁, P₂] k := by
    rw [Fin.forall_fin_two]
    constructor
    · intro y hy hyR u hu
      have hy' := conj_mem_torus_sup (fun α hα => hα.1) hQ hy
      rw [hunion] at hy'
      have hn₁ := torus_sup_subsystemGroup_le_normalizer (Ω := Ω) (J₁ := support13)
        (J₂ := support56) hsep₂₁ hy'
      exact thetaQ_conj_mem (mem_normalizer_of_conj hQ₁ hn₁) hyR hu
    · intro y hy hyR u hu
      have hy' := conj_mem_torus_sup (fun α hα => hα.1) hQ hy
      rw [hunion, Set.union_comm] at hy'
      have hn₂ := torus_sup_subsystemGroup_le_normalizer (Ω := Ω) (J₁ := support56)
        (J₂ := support13) hsep₁₂ hy'
      exact thetaQ_conj_mem (mem_normalizer_of_conj hQ₂ hn₂) hyR hu
  let KL : KernelLayer (tw6N Ω) (twistE6 Ω Fr) (torusRootKernel x) K (Fin 2) :=
    { P := ![P₁, P₂]
      fin := hfinF
      quasi := hqF
      le_span := hspan
      le_fixed := hfix
      norm := hnormF
      cent := fun y hy hc => hPcent_of_std (fun α hα => hα.1) hQ hcommP y hy
        (fun u hu => by
          have hle : (⨆ i, ![P₁, P₂] i) ≤
              Subgroup.centralizer ({y} : Set (ModGL Tag.E6 Ω)) :=
            iSup_le fun i u' hu' =>
              Subgroup.mem_centralizer_singleton_iff.2 (hc i u' hu').symm
          exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hu)).symm)
      comm := fun X hX g hg => by
        have hP := e6Commutant_eq_of_conj_commutant hQ hcommP
        have hX' : X ∈ e6Commutant (((⨆ i, ![P₁, P₂] i : Subgroup (ModGL Tag.E6 Ω)) :
            Set (ModGL Tag.E6 Ω))) := by
          rw [CFSG.RankThree.Lattice.e6Commutant_iSup, Set.mem_iInter]
          exact fun i u hu => hX i u hu
        rw [hP] at hX'
        exact hX' g hg
      sl2 := fun _ => ⟨0, e6Index 0, h₀, hsl₁⟩ }
  refine ⟨KL, ?_⟩
  have hw' : (((twE6FrameWeyl 2) * (twLineYW)⁻¹ * w) • ·) '' S₂ =
      parabolicRoots Tag.E6 support13 := by
    have h1 : (fun x : Fin Tag.E6.rank → ℤ =>
        ((twE6FrameWeyl 2) * (twLineYW)⁻¹ * w) • x) =
        (fun x : Fin Tag.E6.rank → ℤ => ((twE6FrameWeyl 2) * (twLineYW)⁻¹) • (w • x)) := by
      funext x
      rw [mul_smul]
    have himg : (fun x : Fin Tag.E6.rank → ℤ =>
        ((twE6FrameWeyl 2) * (twLineYW)⁻¹) • (w • x)) '' S₂ =
        (((twE6FrameWeyl 2) * (twLineYW)⁻¹) • ·) '' (((w) • ·) '' S₂) := by
      rw [← Set.image_image]
    rw [h1, himg, hw₂]
    exact tw6SixSwap_support56
  intro i
  fin_cases i
  · change p ∣ Nat.card ↥P₁
    rw [tw6_A2_layer_card (K := K) (Ω := Ω) (Fr := Fr) hf hK hFr hS₁roots hvS₁ hw₁]
    exact dvd_card_SU3_of_dvd hpq'
  · change p ∣ Nat.card ↥P₂
    rw [tw6_A2_layer_card (K := K) (Ω := Ω) (Fr := Fr) hf hK hFr hS₂roots hvS₂ hw']
    exact dvd_card_SU3_of_dvd hpq'

theorem tw6_D4_kernelLayer_dvd {K : Type} [Field K] [Finite K] [Algebra K Ω]
    [IsAlgClosure K Ω] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP Ω ℓ] (hf : 1 ≤ f)
    (hK : Nat.card K = ℓ ^ f) (hFr : ∀ c, Fr c = c ^ (ℓ ^ f))
    {x : ModGL Tag.E6 Ω} (hx : x ∈ twistedTorusOf (tw6N Ω) (twistE6 Ω Fr))
    (hD4 : ∃ w : WeylGroup Tag.E6,
      (w • ·) '' torusRootKernel x = parabolicRoots Tag.E6 d4Support) {p : ℕ}
    (hpq : p ∣ Nat.card K ^ 2 - Nat.card K + 1) :
    ∃ KL : KernelLayer (tw6N Ω) (twistE6 Ω Fr) (torusRootKernel x) K Unit,
      ∀ i, p ∣ Nat.card ↥(KL.P i) := by
  obtain ⟨w, hw⟩ := hD4
  have hpq' : p ∣ (ℓ ^ f) ^ 2 - ℓ ^ f + 1 := by simpa [hK] using hpq
  have hℓ : ℓ.Prime := Fact.out
  have hq1 : 1 ≤ ℓ ^ f := by rw [← hK]; exact Nat.card_pos
  obtain ⟨hQ, hfin, hq, hcomm, h₀, hsl⟩ := tw6_D4_layer_data hf hK hFr hx hw
  let KL : KernelLayer (tw6N Ω) (twistE6 Ω Fr) (torusRootKernel x) K Unit :=
    { P := fun _ => rootSpan Tag.E6 Ω (torusRootKernel x) ⊓
        twistedFixedPoints (tw6N Ω) (twistE6 Ω Fr)
      fin := fun _ => hfin
      quasi := fun _ => hq
      le_span := fun _ => inf_le_left
      le_fixed := fun _ => inf_le_right
      norm := fun _ y hy hyR u hu => by
        refine ⟨(Subgroup.mem_normalizer_iff.1
          (torusGroup_sup_rootSpan_le_normalizer' (fun α hα => hα.1) hy) u).1 hu.1, ?_⟩
        have hy' : tw6N Ω * twistE6 Ω Fr y * (tw6N Ω)⁻¹ = y :=
          mem_twistedFixedPoints.1 hyR
        have hu' : tw6N Ω * twistE6 Ω Fr u * (tw6N Ω)⁻¹ = u :=
          mem_twistedFixedPoints.1 hu.2
        refine mem_twistedFixedPoints.2 ?_
        rw [map_mul, map_mul, map_inv]
        calc tw6N Ω * (twistE6 Ω Fr y * twistE6 Ω Fr u * (twistE6 Ω Fr y)⁻¹) *
              (tw6N Ω)⁻¹ =
            (tw6N Ω * twistE6 Ω Fr y * (tw6N Ω)⁻¹) *
              (tw6N Ω * twistE6 Ω Fr u * (tw6N Ω)⁻¹) *
              (tw6N Ω * twistE6 Ω Fr y * (tw6N Ω)⁻¹)⁻¹ := by group
          _ = y * u * y⁻¹ := by rw [hy', hu']
      cent := fun y hy hc => hPcent_of_std (fun α hα => hα.1) hQ hcomm y hy
        (fun u hu => hc () u hu)
      comm := fun X hX g hg => by
        have hcomm' : e6Commutant (((rootSpan Tag.E6 Ω (torusRootKernel x) ⊓
            twistedFixedPoints (tw6N Ω) (twistE6 Ω Fr)).map
              (MulAut.conj (canonicalRep (coxeterSystem Tag.E6) Ω w)).toMonoidHom :
                Subgroup (ModGL Tag.E6 Ω)) : Set (ModGL Tag.E6 Ω)) =
            e6Commutant (subsystemGroup Tag.E6 Ω d4Support : Set (ModGL Tag.E6 Ω)) := by
          simpa only [twistedFixedPoints_tw6N] using hcomm
        have hP : e6Commutant ((rootSpan Tag.E6 Ω (torusRootKernel x) ⊓
            twistedFixedPoints (tw6N Ω) (twistE6 Ω Fr) : Subgroup (ModGL Tag.E6 Ω)) :
              Set (ModGL Tag.E6 Ω)) =
            e6Commutant (rootSpan Tag.E6 Ω (torusRootKernel x) : Set (ModGL Tag.E6 Ω)) := by
          refine e6Commutant_eq_of_conj_eq (canonicalRep (coxeterSystem Tag.E6) Ω w) ?_
          have h1 : (fun g => canonicalRep (coxeterSystem Tag.E6) Ω w * g *
              (canonicalRep (coxeterSystem Tag.E6) Ω w)⁻¹) ''
                (rootSpan Tag.E6 Ω (torusRootKernel x) : Set (ModGL Tag.E6 Ω)) =
              (subsystemGroup Tag.E6 Ω d4Support : Set (ModGL Tag.E6 Ω)) := by
            rw [← hQ, Subgroup.coe_map]
            rfl
          have h2 : (fun g => canonicalRep (coxeterSystem Tag.E6) Ω w * g *
              (canonicalRep (coxeterSystem Tag.E6) Ω w)⁻¹) ''
                ((rootSpan Tag.E6 Ω (torusRootKernel x) ⊓
                  twistedFixedPoints (tw6N Ω) (twistE6 Ω Fr) : Subgroup (ModGL Tag.E6 Ω)) :
                    Set (ModGL Tag.E6 Ω)) =
              (((rootSpan Tag.E6 Ω (torusRootKernel x) ⊓
                twistedFixedPoints (tw6N Ω) (twistE6 Ω Fr)).map
                  (MulAut.conj (canonicalRep (coxeterSystem Tag.E6) Ω w)).toMonoidHom :
                    Subgroup (ModGL Tag.E6 Ω)) : Set (ModGL Tag.E6 Ω)) := by
            rw [Subgroup.coe_map]
            rfl
          rw [h1, h2, hcomm']
        have hX' : X ∈ e6Commutant ((rootSpan Tag.E6 Ω (torusRootKernel x) ⊓
            twistedFixedPoints (tw6N Ω) (twistE6 Ω Fr) : Subgroup (ModGL Tag.E6 Ω)) :
              Set (ModGL Tag.E6 Ω)) := fun u hu => hX () u hu
        rw [hP] at hX'
        exact hX' g hg
      sl2 := fun _ => ⟨(), d4Idx 2, h₀, hsl⟩ }
  refine ⟨KL, ?_⟩
  intro i
  change p ∣ Nat.card ↥(rootSpan Tag.E6 Ω (torusRootKernel x) ⊓
    twistedFixedPoints (tw6N Ω) (twistE6 Ω Fr))
  rw [tw6_D4_layer_card (K := K) (Ω := Ω) (Fr := Fr) hf hK hFr hx hw]
  exact dvd_card_trialityD4_of_dvd_phiSix hq1 hpq'

end CFSG.StandardType.TwE6Nonsplit
