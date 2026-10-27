module

public import CFSG.RankThree.PartTwo.Sec8.Hering611KFS6
public import CFSG.RankThree.PartTwo.Sec8.Hering611KFInvMap
public import CFSG.RankThree.PartTwo.Sec8.Hering611KFInvLift
public import CFSG.RankThree.PartTwo.Sec8.Hering611KFInvConj
import CFSG.RankThree.PartTwo.Sec8.Hering611K
import CFSG.RankThree.PartTwo.Sec15.Y4CoreProofMem
import CFSG.RankThree.PartTwo.Sec6.Item611Res3ProofTools
public import CFSG.RankThree.PartTwo.KFacts.AutPSL2OrderThree
public import CFSG.RankThree.PartTwo.Sec4.ProjSLEquiv
public import CFSG.RankThree.PartTwo.Sec6.Item612Local
public import CFSG.RankThree.PartTwo.Sec8.Hering611Defs

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering611

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.RankThreeEven (projSL)
open CFSG.GorensteinWalter (PSL2 IsOddPrimePower)
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo (pglAction)

section Transfer


variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L E T : Subgroup G} {d : G}
  {S K : Subgroup G}

theorem cfg611_transfer_facts (h45 : Sec4.Item4_5) (C : Cfg611 G A c L E T d S K) :
    ∃ (hcN : c ∈ Subgroup.normalizer (K : Set G)) (hdN : d ∈ Subgroup.normalizer (L : Set G)),
      Odd (Nat.card (inSubgroup (aschbacherSolvableCore 3) K)) ∧
      IsQuasisimple ((Sec4.thetaQuotMulAut L (Sec4.compAction L ⟨d, hdN⟩)).toMonoidHom.eqLocus
        (MonoidHom.id (L ⧸ aschbacherSolvableCore 3 L))) ∧
      Subgroup.center ((Sec4.thetaQuotMulAut L (Sec4.compAction L ⟨d, hdN⟩)).toMonoidHom.eqLocus
        (MonoidHom.id (L ⧸ aschbacherSolvableCore 3 L))) = ⊥ ∧
      Sec11.sec11K L d ∈ thetaComponentsIn (K ⊓ Subgroup.centralizer ({c} : Set G)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hst := C.standing
  have hAe : CFSG.Assembly.IsElemAbelian 3 A := C.mem_S.1.1
  have hcA := C.c_mem
  have hdE : d ∈ E := C.d_mem.1
  have hdA : d ∈ A := C.mem_E.2 hdE
  have hd1 : d ≠ 1 := fun h => C.d_not_mem (h ▸ Subgroup.one_mem _)
  have hd3 : d ^ 3 = 1 := hAe.2 d hdA
  have hLc : L ∈ thetaComponentsAt 3 c := lZeroStarAt_subset A c C.mem_L
  have hKd : K ∈ thetaComponentsAt 3 d := lZeroStarAt_subset A d C.mem_K
  obtain ⟨φ⟩ := C.iso_L
  have hAK : A ≤ Subgroup.normalizer (K : Set G) :=
    Sec6.le_normalizer_of_mem_thetaComponentsAt h45 hst.toTheoremFourHyp hAe hdA hd1 K hKd
  obtain ⟨hdN, hQ, hZ⟩ := Sec6.Hering611.fieldCent_facts_two φ C.d_field hd3
  have hY : Sec11.sec11K L d ∈ thetaComponentsIn
      (Subgroup.centralizer ({d} : Set G) ⊓ Subgroup.centralizer ({c} : Set G)) :=
    Sec6.Res611Res7.sec11K_mem_thetaComponentsIn_centralizer hLc hdN hd3 hQ hZ
  have hDK : Sec11.sec11K L d ≤ K := C.perf_le
  have hLcC : L ≤ Subgroup.centralizer ({c} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hLc
  have hKdC : K ≤ Subgroup.centralizer ({d} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hKd
  have hD : Sec11.sec11K L d ∈ thetaComponentsIn (K ⊓ Subgroup.centralizer ({c} : Set G)) :=
    Sec15.Y4Core.mem_thetaComponentsIn_mid hY (le_inf hDK ((Sec11.sec11K_le L d).trans hLcC))
      (inf_le_inf_right _ hKdC)
  exact ⟨hAK hcA, hdN, Sec6.Res611Res3.odd_card_theta hst.evenRank_eq hAe
    (by rw [C.card_A]) hAK, hQ, hZ, hD⟩

theorem mem_aschbacherSolvableCore_iff {K : Subgroup G} {x : K} :
    x ∈ aschbacherSolvableCore 3 K ↔ (x : G) ∈ inSubgroup (aschbacherSolvableCore 3) K := by
  constructor
  · intro hx
    exact ⟨x, hx, rfl⟩
  · rintro ⟨y, hy, hyx⟩
    have : y = x := Subtype.ext hyx
    rwa [this] at hy

theorem exists_field_involution_of_s6
    (h45 : Sec4.Item4_5) (C : Cfg611 G A c L E T d S K)
    {e : G} (hce : e = c ∨ e = c⁻¹) {t₀ : G} (ht₀K : t₀ ∈ K)
    (ht₀θ : t₀ ∉ inSubgroup (aschbacherSolvableCore 3) K)
    (ht₀sq : t₀ ^ 2 ∈ inSubgroup (aschbacherSolvableCore 3) K)
    (hrel : t₀ * c * t₀⁻¹ * e⁻¹ ∈ inSubgroup (aschbacherSolvableCore 3) K)
    (hS6 : S6Act (imageSub K (Sec11.sec11K L d))
      (QuotientGroup.mk' (aschbacherSolvableCore 3 K) ⟨t₀, ht₀K⟩)) :
    ∃ s : G, s ^ 2 = 1 ∧ KFacts.InducesKindPSL2 (GaloisField 3 (3 * 2)) L s .field := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hcN, hdN, hθodd, hQ, hZ, hD⟩ := cfg611_transfer_facts h45 C
  have hAe : CFSG.Assembly.IsElemAbelian 3 A := C.mem_S.1.1
  have hcA := C.c_mem
  have hc1 := C.c_ne_one
  have hdA : d ∈ A := C.mem_E.2 C.d_mem.1
  have hd3 : d ^ 3 = 1 := hAe.2 d hdA
  have hc3 : c ^ 3 = 1 := hAe.2 c hcA
  have hc3' : orderOf c = 3 := orderOf_eq_prime hc3 hc1
  have hLc : L ∈ thetaComponentsAt 3 c := lZeroStarAt_subset A c C.mem_L
  have hDK : Sec11.sec11K L d ≤ K := C.perf_le
  obtain ⟨φ⟩ := C.iso_L
  obtain ⟨s, hsK, hs2, hsθ, hsc⟩ :=
    exists_involution_lift hcN hc3' hθodd hce ht₀K ht₀θ ht₀sq hrel
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 K) with hπ
  have hπs : π ⟨s, hsK⟩ = π ⟨t₀, ht₀K⟩ := by
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    exact mem_aschbacherSolvableCore_iff.mpr hsθ
  have himg : ∀ x ∈ Sec11.sec11K L d, ∃ y ∈ Sec11.sec11K L d,
      y⁻¹ * (s * x * s⁻¹) ∈ inSubgroup (aschbacherSolvableCore 3) K := by
    intro x hx
    have hxP : π (Subgroup.inclusion hDK ⟨x, hx⟩) ∈ imageSub K (Sec11.sec11K L d) :=
      Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr hx)
    have hnorm := (Subgroup.mem_normalizer_iff.mp hS6.mem_normalizer
      (π (Subgroup.inclusion hDK ⟨x, hx⟩))).mp hxP
    obtain ⟨w, hw, hwπ⟩ := hnorm
    refine ⟨(w : G), Subgroup.mem_subgroupOf.mp hw, ?_⟩
    have hsx : s * x * s⁻¹ ∈ K := K.mul_mem (K.mul_mem hsK (hDK hx)) (K.inv_mem hsK)
    have h1 : π w = π ⟨s * x * s⁻¹, hsx⟩ := by
      rw [hwπ, ← hπs]
      have : (⟨s * x * s⁻¹, hsx⟩ : K) = ⟨s, hsK⟩ * Subgroup.inclusion hDK ⟨x, hx⟩ * ⟨s, hsK⟩⁻¹ :=
        rfl
      rw [this, map_mul, map_mul, map_inv, hπs]
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at h1
    exact mem_aschbacherSolvableCore_iff.mp h1
  have hsD := map_conj_eq_of_image hD hsK hsc hce himg
  have hDne : Sec11.sec11K L d ≠ ⊥ := by
    intro hbot
    obtain ⟨x, hxP, hx⟩ := hS6.nontrivial
    obtain ⟨w, hw, rfl⟩ := hxP
    have : (w : G) ∈ Sec11.sec11K L d := Subgroup.mem_subgroupOf.mp hw
    rw [hbot, Subgroup.mem_bot] at this
    have hw1 : w = 1 := Subtype.ext this
    apply hx
    rw [hw1, map_one]
    group
  have hDp := isPerfect_of_mem_thetaComponentsIn hD
  have hsL := mem_normalizer_of_map_conj_eq hLc (Sec11.sec11K_le L d) hDne hDp hsD hsc hce
  obtain ⟨ψ, hψinj, hψ⟩ := exists_embedding hdN hd3 hQ hZ hDK hS6.theta_bot
  set τ := Sec4.Item426.thetaAut L hsL with hτ
  have hequiv : ∀ x y : imageSub K (Sec11.sec11K L d),
      (y : K ⧸ aschbacherSolvableCore 3 K) = π ⟨s, hsK⟩ * x * (π ⟨s, hsK⟩)⁻¹ →
      ψ y = τ (ψ x) := by
    intro x y hxy
    obtain ⟨w, hw, hwx⟩ := x.2
    set z : Sec11.sec11K L d := ⟨(w : G), Subgroup.mem_subgroupOf.mp hw⟩ with hz
    have hz' : s * (z : G) * s⁻¹ ∈ Sec11.sec11K L d := by
      have : s * (z : G) * s⁻¹ ∈ (Sec11.sec11K L d).map (MulAut.conj s).toMonoidHom :=
        ⟨z, z.2, rfl⟩
      rwa [hsD] at this
    set z' : Sec11.sec11K L d := ⟨s * (z : G) * s⁻¹, hz'⟩ with hz'def
    have hincl : Subgroup.inclusion hDK z = w := Subtype.ext rfl
    have h1 : ψ x = Sec11.kMap L d z := hψ z x (by rw [hincl]; exact hwx.symm)
    have h2 : ψ y = Sec11.kMap L d z' := by
      apply hψ z' y
      rw [mk_inclusion_conj hsK hDK z z' rfl, hincl, hwx]
      exact hxy
    rw [h1, h2]
    exact kMap_conj_apply hsL z z' rfl
  set F := GaloisField 3 (3 * 2) with hF
  set eL : L ⧸ aschbacherSolvableCore 3 L ≃* PSL2 F := φ.trans (projSLEquivPSL F) with heL
  set α := KFacts.inducedAutHom L eL ⟨s, hsL⟩ with hα
  have hαapp : ∀ x, α (eL x) = eL (τ x) := fun x => by
    rw [hα, KFacts.inducedAutHom_apply]
    simp [MulAut.congr_apply]
    rfl
  have hαord2 : α ^ 2 = 1 := KFacts.inducedAutHom_pow_eq_one L eL hsL hs2
  obtain ⟨v₁, v₂, h, hv₁P, hv₂P, hhP, hv1, hv2, hv12, hsq1, hsq2, hcm, hh1, hh2, ht1, ht2, hth⟩ :=
    hS6.data
  set a₁ : imageSub K (Sec11.sec11K L d) := ⟨v₁, hv₁P⟩ with ha₁
  set a₂ : imageSub K (Sec11.sec11K L d) := ⟨v₂, hv₂P⟩ with ha₂
  set b : imageSub K (Sec11.sec11K L d) := ⟨h, hhP⟩ with hb
  have hfix : ∀ a : imageSub K (Sec11.sec11K L d),
      π ⟨t₀, ht₀K⟩ * (a : K ⧸ aschbacherSolvableCore 3 K) * (π ⟨t₀, ht₀K⟩)⁻¹ = a →
      α (eL (ψ a)) = eL (ψ a) := by
    intro a ha
    rw [hαapp]
    congr 1
    exact (hequiv a a (by rw [hπs]; exact ha.symm)).symm
  set ρ : imageSub K (Sec11.sec11K L d) →* PSL2 F := eL.toMonoidHom.comp ψ with hρ
  have hρinj : Function.Injective ρ := fun x y hxy => hψinj (eL.injective hxy)
  have hα₁ : α (ρ a₁) = ρ a₁ := hfix a₁ ht1
  have hα₂ : α (ρ a₂) = ρ a₂ := hfix a₂ ht2
  have hαb : α (ρ b) = ρ b := hfix b hth
  have hne1 : ∀ a : imageSub K (Sec11.sec11K L d), (a : K ⧸ aschbacherSolvableCore 3 K) ≠ 1 →
      ρ a ≠ 1 := fun a ha h1 => ha (congrArg Subtype.val (hρinj (h1.trans (map_one ρ).symm)))
  have e1 : b * a₁ * b⁻¹ = a₂ := Subtype.ext (by simpa using hh1)
  have e2 : b * a₂ * b⁻¹ = a₁ * a₂ := Subtype.ext (by simpa using hh2)
  have e3 : a₁ * a₁ = 1 := Subtype.ext (by simpa using hsq1)
  have e4 : a₂ * a₂ = 1 := Subtype.ext (by simpa using hsq2)
  have e5 : a₁ * a₂ = a₂ * a₁ := Subtype.ext (by simpa using hcm)
  have hα1 : α ≠ 1 := by
    obtain ⟨x, hxP, hx⟩ := hS6.nontrivial
    have hx' : π ⟨t₀, ht₀K⟩ * x * (π ⟨t₀, ht₀K⟩)⁻¹ ∈ imageSub K (Sec11.sec11K L d) :=
      (Subgroup.mem_normalizer_iff.mp hS6.mem_normalizer x).mp hxP
    intro h1
    have h3 : ψ ⟨_, hx'⟩ = τ (ψ ⟨x, hxP⟩) := hequiv ⟨x, hxP⟩ ⟨_, hx'⟩ (by rw [hπs])
    have h4 : α (ρ ⟨x, hxP⟩) = ρ ⟨_, hx'⟩ := by
      change α (eL (ψ ⟨x, hxP⟩)) = eL (ψ ⟨_, hx'⟩)
      rw [hαapp, h3]
    rw [h1] at h4
    exact hx (congrArg Subtype.val (hρinj h4)).symm
  have hαord : orderOf α = 2 := orderOf_eq_prime hαord2 hα1
  have hFodd : IsOddPrimePower (Nat.card F) :=
    ⟨3, 6, Nat.prime_three, ⟨1, rfl⟩, by norm_num, by
      rw [hF, GaloisField.card 3 (3 * 2) (by omega)]⟩
  have hαD : α ∉ (pglAction F).range := by
    intro hD
    apply hα1
    refine eq_one_of_mem_range_pglAction hFodd hD (v₁ := ρ a₁) (v₂ := ρ a₂) (h := ρ b)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hα₁ hα₂ hαb
    · exact hne1 a₁ hv1
    · exact hne1 a₂ hv2
    · intro h12
      exact hv12 (congrArg Subtype.val (hρinj h12))
    · rw [← map_mul, e3, map_one]
    · rw [← map_mul, e4, map_one]
    · rw [← map_mul, ← map_mul, e5]
    · rw [← map_inv, ← map_mul, ← map_mul, e1]
    · rw [← map_inv, ← map_mul, ← map_mul, e2, map_mul]
  exact ⟨s, hs2, eL, hsL, KFacts.isField_psl2_of_orderOf_prime Nat.prime_two hαord hαD⟩

end Transfer

end CFSG.RankThree.PartTwo.Sec8.Hering611
