module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148ATwelve
import CFSG.RankThree.PartTwo.Sec14.Item148HJProofLB
import CFSG.RankThree.PartTwo.Sec14.Item1417
import CFSG.RankThree.PartTwo.Sec14.Item148RankProofTenTools
import CFSG.RankThree.PartTwo.Sec4.Sporadic.Item415
import CFSG.RankThree.PartTwo.Sec19.Item19Res4ProofTripleA6
import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
public import CFSG.RankThree.PartTwo.Sec14.Item14ListStatements
import CFSG.RankThree.PartTwo.Sec14.Item148MainProofLift

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148A

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.GH74.GLS Main148

theorem isTwelveType_of_mulEquiv_A5 {F : Type} [Group F] [Finite F]
    (e : F ≃* alternatingGroup (Fin 5)) : IsTwelveType F := by
  have hA5s : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup_five
  have hFs : IsSimpleGroup F := MulEquiv.isSimpleGroup e
  set σ : alternatingGroup (Fin 5) := ⟨Equiv.swap 0 1 * Equiv.swap 0 2,
    Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩ with hσ
  set τ : alternatingGroup (Fin 5) := ⟨Equiv.swap 0 3 * Equiv.swap 0 4,
    Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩ with hτ
  have hστ : σ * τ ≠ τ * σ := fun h0 => by
    have := congrArg Subtype.val h0
    revert this
    decide
  have hnc : ∃ a b : F, a * b ≠ b * a := ⟨e.symm σ, e.symm τ, fun h0 => hστ (by
    have := congrArg e h0
    simpa using this)⟩
  obtain ⟨hq, hZ⟩ := CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnc
  have hσ1 : σ ≠ 1 := fun h0 => by
    have := congrArg Subtype.val h0
    revert this
    decide
  refine ⟨hq, ?_, ⟨e.symm σ, ?_, ?_⟩, ?_⟩
  · rw [hZ]
    exact IsPGroup.of_bot
  · have h3 : σ ^ 3 = 1 := Subtype.ext (by decide)
    rw [← map_pow, h3, map_one]
  · rw [hZ, Subgroup.mem_bot]
    intro h0
    apply hσ1
    simpa using congrArg e h0
  · rw [hZ]
    have hc : Nat.card (F ⧸ (⊥ : Subgroup F)) = Nat.card F :=
      Nat.card_congr (QuotientGroup.quotientBot).toEquiv
    rw [hc, Nat.card_congr e.toEquiv, KFacts.KS14.card_alternatingGroup_five_seven_ten.1]
    norm_num

theorem isTwelveType_of_tripleCover_A6 {F : Type} [Group F] [Finite F]
    (h : Sec4.IsTripleCover F (alternatingGroup (Fin 6))) (hp : Group.IsPerfect F) :
    IsTwelveType F := by
  obtain ⟨hZ, ⟨e⟩⟩ := h
  have hA6s : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  have hQs : IsSimpleGroup (F ⧸ Subgroup.center F) := MulEquiv.isSimpleGroup e
  set σ : alternatingGroup (Fin 6) := ⟨Equiv.swap 0 1 * Equiv.swap 0 2,
    Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩ with hσ
  set τ : alternatingGroup (Fin 6) := ⟨Equiv.swap 0 3 * Equiv.swap 0 4,
    Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩ with hτ
  have hστ : σ * τ ≠ τ * σ := fun h0 => by
    have := congrArg Subtype.val h0
    revert this
    decide
  have hT : Sec19.IsTripleA6 F := ⟨hZ, ⟨e⟩⟩
  refine ⟨⟨hp, hQs, e.symm σ, e.symm τ, fun h0 => hστ (by simpa using congrArg e h0)⟩, ?_,
    Sec19.Item19Res4Proof.exists_noncentral_of_isTripleA6 hT, ?_⟩
  · exact IsPGroup.of_card (n := 1) (by rw [hZ, pow_one])
  · rw [Nat.card_congr e.toEquiv, Sec19.Item19Res4Proof.card_alternatingGroup_six']
    norm_num

variable {G : Type} [Group G] [Finite G]

theorem exists_tripleCover_ON_of_ncard_twelve
    (h134 : Item134) (h48 : Sec4.Item4_8) {A L : Subgroup G} {c : G} (h : Sec14Std G A c L)
    {B Lb : Subgroup G} {b d : G} (hB : IsHyperplane A B) (hc : IsLBConfig A B b d Lb)
    (h12 : (omegaA A).ncard = 12) :
    ∃ K ∈ thetaComponentsAt 3 d, Sec4.IsTripleCover (↥K ⧸ aschbacherSolvableCore 3 ↥K)
      CFSG.Blueprint.NativeSporadic.ON := by
  have h415 : Sec4.Item4_15 := Sec4.Sporadic.rank3II_4_15
  have hA : Late.IsE27 A := h.isE27
  have hJ := Item148HJ.j2_of_isLBConfig hc
  obtain ⟨hb1, hd1⟩ := hc.ne_one hB hA
  obtain ⟨hBbd, hbΩ, hLbeq, -, hdL, S, hdS, hSd⟩ := hc
  have hLb : Lb ∈ lA A b := hLbeq ▸ Set.mem_singleton Lb
  have hbA : b ∈ A := (zpowers_mem_omegaA_iff.mp hbΩ).1
  have hdA : d ∈ A := hB.1 (hBbd ▸ Subgroup.subset_closure (Set.mem_insert_of_mem b rfl))
  obtain ⟨hθs, -, hθ3, -, -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥Lb) Nat.prime_three
  have hS := center_sylow_eq_zpowers_of_quot_j2 h415 hθ3 hJ hdL hd1 S hdS hSd
  have hG4 : SectionFourHyp ↥(Subgroup.centralizer ({d} : Set G)) :=
    h.toTheoremFourHyp.sectionFourHyp
      (centralizer_singleton_ne_top h.isSimpleGroup h.nonabelian hd1)
  have hJq := residual_inf_centralizer_quasisimple_of_quot h415 hθ3 hθs hJ hdL hd1
    ⟨S, hdS, hSd⟩
  obtain ⟨K, hK, hJK⟩ :=
    exists_mem_thetaComponentsAt_le_residual h48 hG4 hA hbA hdA hb1 hLb.1 hJq
  have hdata : Sec13Data G A b Lb :=
    { h.toSec13Data with zpowers_mem_omegaA := hbΩ, mem_lA := hLb }
  refine ⟨K, hK, ?_⟩
  rcases h134 G A b Lb hdata hJ d hdA hd1 ⟨_, hS⟩ K hK hJK with
    ⟨-, -, h1⟩ | ⟨-, -, -, -, -, -, hΩ⟩ | ⟨hON, -, -, -⟩
  · rw [h1, Set.ncard_singleton] at h12
    norm_num at h12
  · rcases hΩ with ⟨-, h3⟩ | ⟨-, -, -, -, -, -, -, -, h6, -⟩
    · rw [h3] at h12
      norm_num at h12
    · rw [h6] at h12
      norm_num at h12
  · exact hON

theorem exists_preimage_img148 {A Y : Subgroup G} [(ker148 A Y).Normal] {d : G}
    {F : Subgroup (↥(Y ⊔ A) ⧸ ker148 A Y)}
    (hF : F ≤ img148 A Y (Y ⊓ Subgroup.centralizer ({d} : Set G))) :
    ∃ (P : Subgroup G) (φ : ↥P →* ↥F), P ≤ Y ⊓ Subgroup.centralizer ({d} : Set G) ∧
      Function.Surjective φ ∧ ¬ 3 ∣ Nat.card φ.ker ∧
      ∀ (p : ↥P) (hp : (p : G) ∈ Y ⊔ A),
        ((φ p : ↥F) : ↥(Y ⊔ A) ⧸ ker148 A Y) = QuotientGroup.mk' (ker148 A Y) ⟨p, hp⟩ := by
  set ν := QuotientGroup.mk' (ker148 A Y) with hν
  set P := ((F.comap ν).map (Y ⊔ A).subtype) ⊓ (Y ⊓ Subgroup.centralizer ({d} : Set G)) with hP
  have hPM : ∀ p ∈ P, p ∈ Y ⊔ A := fun p hp => (hp.2.1 : p ∈ Y) |> Subgroup.mem_sup_left
  have hPF : ∀ (p : G) (hp : p ∈ P), ν ⟨p, hPM p hp⟩ ∈ F := by
    intro p hp
    obtain ⟨m, hm, hmp⟩ := hp.1
    have : (⟨p, hPM p hp⟩ : ↥(Y ⊔ A)) = m := Subtype.ext hmp.symm
    rw [this]
    exact hm
  let φ : ↥P →* ↥F :=
    { toFun := fun p => ⟨ν ⟨p, hPM p p.2⟩, hPF p p.2⟩
      map_one' := Subtype.ext (by
        show ν ⟨(1 : G), _⟩ = 1
        exact (map_one ν))
      map_mul' := fun p q => Subtype.ext (by
        show ν ⟨(p : G) * q, _⟩ = ν ⟨p, _⟩ * ν ⟨q, _⟩
        rw [← map_mul]
        rfl) }
  refine ⟨P, φ, inf_le_right, ?_, ?_, fun p hp => rfl⟩
  · rintro ⟨f, hf⟩
    obtain ⟨g, hgM, hgYC, hgf⟩ := mem_img148_iff.mp (hF hf)
    have hgP : g ∈ P := ⟨⟨⟨g, hgM⟩, by
      show ν ⟨g, hgM⟩ ∈ F
      rw [hgf]
      exact hf, rfl⟩, hgYC⟩
    exact ⟨⟨g, hgP⟩, Subtype.ext hgf⟩
  · intro h3
    have hle : φ.ker.map P.subtype ≤ pPrimeCoreOf 3 Y := by
      rintro _ ⟨p, hp, rfl⟩
      have h1 : ν ⟨p, hPM p p.2⟩ = 1 := congrArg Subtype.val hp
      exact mk'_ker148_eq_one_iff.mp h1
    have hc : Nat.card φ.ker ∣ Nat.card (pPrimeCoreOf 3 Y) := by
      rw [← Subgroup.card_map_of_injective P.subtype_injective]
      exact Subgroup.card_dvd_of_le hle
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 Y)
      (h3.trans hc)

theorem false_of_ncard_twelve_img148
    (h134 : Item134) (h48 : Sec4.Item4_8) {A L : Subgroup G} {c : G} (h : Sec14Std G A c L)
    {Y : Subgroup G} (hY : Y ∈ scriptY A) {B Lb : Subgroup G} {b d : G}
    (hB : IsHyperplane A B) (hc : IsLBConfig A B b d Lb) (h12 : (omegaA A).ncard = 12) :
    letI := ker148_normal hY.2
    ∀ F₁ F₂ : Subgroup (↥(Y ⊔ A) ⧸ ker148 A Y),
      F₁ ≤ img148 A Y (Y ⊓ Subgroup.centralizer ({d} : Set G)) →
      F₂ ≤ img148 A Y (Y ⊓ Subgroup.centralizer ({d} : Set G)) →
      F₁ ≤ Subgroup.centralizer (F₂ : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) →
      IsTwelveType ↥F₁ → IsTwelveType ↥F₂ → False := by
  intro F₁ F₂ hF₁ hF₂ hF₁₂ hT₁ hT₂
  letI := ker148_normal hY.2
  obtain ⟨K, hK, hKON⟩ := exists_tripleCover_ON_of_ncard_twelve h134 h48 h hB hc h12
  obtain ⟨P₁, φ₁, hP₁, hφ₁, hφ₁3, hφ₁e⟩ := exists_preimage_img148 hF₁
  obtain ⟨P₂, φ₂, hP₂, hφ₂, hφ₂3, hφ₂e⟩ := exists_preimage_img148 hF₂
  set N := pPrimeCoreOf 3 Y ⊓ Subgroup.centralizer ({d} : Set G) with hN
  have hN3 : ¬ 3 ∣ Nat.card N := fun h3 =>
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 Y)
      (h3.trans (Subgroup.card_dvd_of_le inf_le_left))
  have hNn : ∀ {P : Subgroup G}, P ≤ Y ⊓ Subgroup.centralizer ({d} : Set G) →
      P ≤ Subgroup.normalizer (N : Set G) := by
    intro P hP p hp
    have hpY : p ∈ Subgroup.normalizer (pPrimeCoreOf 3 Y : Set G) :=
      le_normalizer_pPrimeCoreOf 3 Y (hP hp).1
    have hpC : p ∈ Subgroup.normalizer
        (Subgroup.centralizer ({d} : Set G) : Set G) := Subgroup.le_normalizer (hP hp).2
    rw [Subgroup.mem_normalizer_iff] at hpY hpC ⊢
    intro n
    rw [hN, Subgroup.mem_inf, Subgroup.mem_inf, hpY n, hpC n]
  have hcomm : ⁅P₁, P₂⁆ ≤ N := by
    rw [Subgroup.commutator_le]
    intro p hp q hq
    have hpM : p ∈ Y ⊔ A := Subgroup.mem_sup_left (hP₁ hp).1
    have hqM : q ∈ Y ⊔ A := Subgroup.mem_sup_left (hP₂ hq).1
    rw [commutatorElement_def]
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · have hpq := Subgroup.mem_centralizer_iff.mp (hF₁₂ (φ₁ ⟨p, hp⟩).2) _ (φ₂ ⟨q, hq⟩).2
      rw [hφ₁e ⟨p, hp⟩ hpM, hφ₂e ⟨q, hq⟩ hqM] at hpq
      have h1 : QuotientGroup.mk' (ker148 A Y)
          (⟨p, hpM⟩ * ⟨q, hqM⟩ * (⟨p, hpM⟩)⁻¹ * (⟨q, hqM⟩)⁻¹) = 1 := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← hpq]
        group
      have h2 := mk'_ker148_eq_one_iff.mp h1
      simpa using h2
    · have h1 := (hP₁ hp).2
      have h2 := (hP₂ hq).2
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ h1 h2)
        (Subgroup.inv_mem _ h1)) (Subgroup.inv_mem _ h2)
  exact false_of_commuting_of_tripleCover_ON h hK hKON (hP₁.trans inf_le_right)
    (hP₂.trans inf_le_right) inf_le_right hN3 (hNn hP₁) (hNn hP₂) hcomm φ₁ φ₂ hφ₁ hφ₂ hφ₁3 hφ₂3
    hT₁ hT₂

theorem le_img148_inf_centralizer {A Y : Subgroup G} [(ker148 A Y).Normal]
    (hAY : A ≤ Subgroup.normalizer (Y : Set G)) {d : G} (hdA : d ∈ A) (hd3 : d ^ 3 = 1)
    {U : Subgroup G} (hUY : U ≤ Y) {F : Subgroup (↥(Y ⊔ A) ⧸ ker148 A Y)}
    (hFU : F ≤ img148 A Y U) (hFd : F ≤ Subgroup.centralizer {alpha148 A Y d hdA}) :
    F ≤ img148 A Y (Y ⊓ Subgroup.centralizer ({d} : Set G)) := fun x hx =>
  Item148Rank.mem_img148_centralizer_of_commute148 hAY hdA hd3 hUY (hFU hx)
    (Subgroup.mem_centralizer_singleton_iff.mp (hFd hx)).symm

theorem false_of_ncard_twelve_img148'
    (h134 : Item134) (h48 : Sec4.Item4_8) {A L : Subgroup G} {c : G} (h : Sec14Std G A c L)
    {Y : Subgroup G} (hY : Y ∈ scriptY A) {B Lb : Subgroup G} {b d : G}
    (hB : IsHyperplane A B) (hc : IsLBConfig A B b d Lb) (h12 : (omegaA A).ncard = 12)
    (hdA : d ∈ A) :
    letI := ker148_normal hY.2
    ∀ F₁ F₂ : Subgroup (↥(Y ⊔ A) ⧸ ker148 A Y), F₁ ≤ img148 A Y Y → F₂ ≤ img148 A Y Y →
      F₁ ≤ Subgroup.centralizer {alpha148 A Y d hdA} →
      F₂ ≤ Subgroup.centralizer {alpha148 A Y d hdA} →
      F₁ ≤ Subgroup.centralizer (F₂ : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) →
      IsTwelveType ↥F₁ → IsTwelveType ↥F₂ → False := by
  intro F₁ F₂ hF₁ hF₂ hF₁d hF₂d hF₁₂ hT₁ hT₂
  letI := ker148_normal hY.2
  have hd3 : d ^ 3 = 1 := h.isE27.1.2 d hdA
  exact false_of_ncard_twelve_img148 h134 h48 h hY hB hc h12 F₁ F₂
    (le_img148_inf_centralizer hY.2 hdA hd3 le_rfl hF₁ hF₁d)
    (le_img148_inf_centralizer hY.2 hdA hd3 le_rfl hF₂ hF₂d) hF₁₂ hT₁ hT₂

end CFSG.RankThree.PartTwo.Sec14.Ronan148A
