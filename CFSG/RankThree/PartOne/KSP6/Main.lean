module

public import CFSG.RankThree.PartOne.KSP6.Torus
public import CFSG.RankThree.PartOne.KSP6.Outer
public import CFSG.RankThree.PartOne.KSP6.Transport
public import CFSG.RankThree.PartOne.KC.SymplecticInnerPlaneCore
public import CFSG.RankThree.PartOne.S15K.Row2

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory

namespace KSP6

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher CFSG.RankThree.Classical
  CFSG.Assembly.LowTwoRank AUTSL
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl (torusHom torus)

section Setup

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem conj_injective_sp :
    Function.Injective (MulAut.conj : StatedSp 3 K →* MulAut (StatedSp 3 K)) := by
  obtain ⟨f, hf⟩ := exists_card_eq_two_pow (K := K)
  have hf1 : 1 ≤ f := by
    by_contra h
    have : f = 0 := by omega
    have h1 := Finite.one_lt_card (α := K)
    rw [hf, this] at h1
    simp at h1
  have hbij : Function.Bijective (proj 3 K) := UnitaryHigher.proj_bijective_of_charTwo
  obtain ⟨-, hcenter, -⟩ := spProj_facts (K := K) (r := 3) Nat.prime_two hf1 hf (by norm_num)
    (by intro h; omega)
  rw [injective_iff_map_eq_one]
  intro s hs
  have h1 : proj 3 K s ∈ Subgroup.center (StatedProj (StatedSp 3 K)) := by
    rw [Subgroup.mem_center_iff]
    intro z
    obtain ⟨y, rfl⟩ := proj_surjective z
    have h2 : s * y * s⁻¹ = y := by
      have := congrArg (fun φ : MulAut (StatedSp 3 K) => φ y) hs
      simpa [MulAut.conj_apply] using this
    have h3 : y * s = s * y := by
      calc y * s = (s * y * s⁻¹) * s := by rw [h2]
        _ = s * y := by group
    rw [← map_mul, ← map_mul, h3]
  rw [hcenter, Subgroup.mem_bot] at h1
  exact hbij.1 (h1.trans (map_one (proj 3 K)).symm)

theorem mulAut_mul_conj_mul_inv {L : Type} [Group L] (t : MulAut L) (g : L) :
    t * MulAut.conj g * t⁻¹ = MulAut.conj (t g) := by
  ext x
  simp [MulAut.mul_apply, MulAut.conj_apply]

theorem isSylowOf_unipotent :
    IsSylowOf 2 ((unipotent 3 K).map (MulAut.conj : StatedSp 3 K →* MulAut (StatedSp 3 K)))
      (InnL (StatedSp 3 K)) := by
  obtain ⟨P, hP⟩ := exists_sylow_unipotent (K := K) 2 3
  have hinj := conj_injective_sp (K := K)
  have hmap : InnL (StatedSp 3 K) = (⊤ : Subgroup (StatedSp 3 K)).map
      (MulAut.conj : StatedSp 3 K →* MulAut (StatedSp 3 K)) := MonoidHom.range_eq_map _
  refine ⟨?_, ?_, ?_⟩
  · rw [hmap]
    exact Subgroup.map_mono le_top
  · rw [← hP]
    exact P.isPGroup'.map _
  · rw [hmap, Subgroup.relIndex_map_map_of_injective _ _ hinj, Subgroup.relIndex_top_right, ← hP]
    exact P.not_dvd_index

theorem stable_unipotent {T : Subgroup (MulAut (StatedSp 3 K))}
    (hT : T ⊓ InnL (StatedSp 3 K) =
      (unipotent 3 K).map (MulAut.conj : StatedSp 3 K →* MulAut (StatedSp 3 K)))
    {t : MulAut (StatedSp 3 K)} (ht : t ∈ T) : ∀ u ∈ unipotent 3 K, t u ∈ unipotent 3 K := by
  intro u hu
  have hcj : (MulAut.conj u : MulAut (StatedSp 3 K)) ∈ T := by
    have : (MulAut.conj u : MulAut (StatedSp 3 K)) ∈ T ⊓ InnL (StatedSp 3 K) := by
      rw [hT]
      exact ⟨u, hu, rfl⟩
    exact this.1
  have h1 : t * MulAut.conj u * t⁻¹ ∈ T ⊓ InnL (StatedSp 3 K) := by
    refine ⟨T.mul_mem (T.mul_mem ht hcj) (T.inv_mem ht), ?_⟩
    rw [mulAut_mul_conj_mul_inv]
    exact ⟨t u, rfl⟩
  rw [hT, mulAut_mul_conj_mul_inv] at h1
  obtain ⟨u', hu', hu'e⟩ := h1
  have := conj_injective_sp hu'e
  rwa [← this]

theorem card_siegel_centralizer_le {T : Subgroup (MulAut (StatedSp 3 K))}
    (hT : T ⊓ InnL (StatedSp 3 K) =
      (unipotent 3 K).map (MulAut.conj : StatedSp 3 K →* MulAut (StatedSp 3 K)))
    {t : MulAut (StatedSp 3 K)} (ht : t ∈ T)
    (htU : t ∉ (unipotent 3 K).map (MulAut.conj : StatedSp 3 K →* MulAut (StatedSp 3 K))) :
    Nat.card ↥(((siegelRadicalSp 3 K).map
      (MulAut.conj : StatedSp 3 K →* MulAut (StatedSp 3 K))) ⊓
        Subgroup.centralizer ({t} : Set (MulAut (StatedSp 3 K)))) ≤ Nat.card K ^ 5 := by
  classical
  have hinj := conj_injective_sp (K := K)
  have hUt := stable_unipotent hT ht
  have hVt := siegel_char hUt
  have htI : t ∉ (MulAut.conj : StatedSp 3 K →* MulAut (StatedSp 3 K)).range := by
    intro hI
    exact htU (by rw [← hT]; exact ⟨ht, hI⟩)
  have hfix := fixed_card_le hVt htI
  have key : ∀ y : ↥(((siegelRadicalSp 3 K).map
      (MulAut.conj : StatedSp 3 K →* MulAut (StatedSp 3 K))) ⊓
        Subgroup.centralizer ({t} : Set (MulAut (StatedSp 3 K)))),
      ∃ v : ↥(siegelRadicalSp 3 K), t (v : StatedSp 3 K) = v ∧
        MulAut.conj (v : StatedSp 3 K) = y.1 := by
    intro y
    obtain ⟨v, hv, hvy⟩ := y.2.1
    refine ⟨⟨v, hv⟩, ?_, hvy⟩
    have hcomm := Subgroup.mem_centralizer_iff.1 y.2.2 t rfl
    rw [← hvy] at hcomm
    have h2 : t * MulAut.conj v * t⁻¹ = MulAut.conj v := by
      rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
    rw [mulAut_mul_conj_mul_inv] at h2
    exact hinj h2
  choose vof hvof1 hvof2 using key
  have hle : Nat.card ↥(((siegelRadicalSp 3 K).map
      (MulAut.conj : StatedSp 3 K →* MulAut (StatedSp 3 K))) ⊓
        Subgroup.centralizer ({t} : Set (MulAut (StatedSp 3 K)))) ≤
      Nat.card {v : ↥(siegelRadicalSp 3 K) // t (v : StatedSp 3 K) = v} := by
    refine Nat.card_le_card_of_injective (fun y => ⟨vof y, hvof1 y⟩) ?_
    intro y z h
    have h' : vof y = vof z := congrArg Subtype.val h
    apply Subtype.ext
    rw [← hvof2 y, ← hvof2 z, h']
  have hq : 0 < Nat.card K := Nat.card_pos
  have h6 : Nat.card K ^ 6 = Nat.card K ^ 5 * Nat.card K := pow_succ _ _
  rw [h6] at hfix
  exact hle.trans (Nat.le_of_mul_le_mul_right hfix hq)

theorem pushingUpS_eq_siegel (hq : 2 < Nat.card K) {T : Subgroup (MulAut (StatedSp 3 K))}
    (hT : T ⊓ InnL (StatedSp 3 K) =
      (unipotent 3 K).map (MulAut.conj : StatedSp 3 K →* MulAut (StatedSp 3 K))) :
    pushingUpS T =
      (siegelRadicalSp 3 K).map (MulAut.conj : StatedSp 3 K →* MulAut (StatedSp 3 K)) := by
  classical
  obtain ⟨f, hf⟩ := exists_card_eq_two_pow (K := K)
  have hinj := conj_injective_sp (K := K)
  set cj : StatedSp 3 K →* MulAut (StatedSp 3 K) := MulAut.conj with hcj
  have hVU : (siegelRadicalSp 3 K).map cj ≤ (unipotent 3 K).map cj :=
    Subgroup.map_mono siegel_le_unipotent
  have hUT : (unipotent 3 K).map cj ≤ T := by
    rw [← hT]
    exact inf_le_left
  obtain ⟨hVc0, hVs0⟩ := siegel_elemAbelian (K := K)
  have hVc : ∀ x ∈ (siegelRadicalSp 3 K).map cj, ∀ y ∈ (siegelRadicalSp 3 K).map cj,
      x * y = y * x := by
    rintro _ ⟨v, hv, rfl⟩ _ ⟨w, hw, rfl⟩
    rw [← map_mul, ← map_mul, hVc0 v hv w hw]
  have hVs : ∀ x ∈ (siegelRadicalSp 3 K).map cj, x ^ 2 = 1 := by
    rintro _ ⟨v, hv, rfl⟩
    rw [← map_pow, hVs0 v hv, map_one]
  have hqV : Nat.card ↥((siegelRadicalSp 3 K).map cj) = Nat.card K ^ 6 := by
    rw [Subgroup.card_map_of_injective hinj, card_siegel]
  have hVcard : Nat.card ↥((siegelRadicalSp 3 K).map cj) = 2 ^ (f * 6) := by
    rw [hqV, hf, ← pow_mul]
  have hc : ∀ t ∈ T, t ∉ (unipotent 3 K).map cj →
      Nat.card ↥(((siegelRadicalSp 3 K).map cj) ⊓ Subgroup.centralizer ({t} : Set _)) ≤
        Nat.card K ^ 5 := fun t ht htU => card_siegel_centralizer_le hT ht htU
  have hCT : ∀ t ∈ T, (∀ v ∈ (siegelRadicalSp 3 K).map cj, v * t = t * v) →
      t ∈ (siegelRadicalSp 3 K).map cj := by
    intro t ht hcomm
    by_cases htU : t ∈ (unipotent 3 K).map cj
    · obtain ⟨u, hu, rfl⟩ := htU
      refine ⟨u, eq_siegel_of_comm hu (fun v hv => ?_), rfl⟩
      apply hinj
      rw [map_mul, map_mul]
      exact (hcomm (cj v) ⟨v, hv, rfl⟩).symm
    · exfalso
      have h1 := hc t ht htU
      have h2 : Nat.card ↥((siegelRadicalSp 3 K).map cj) ≤
          Nat.card ↥(((siegelRadicalSp 3 K).map cj) ⊓ Subgroup.centralizer ({t} : Set _)) := by
        apply Subgroup.card_le_of_le
        intro v hv
        refine ⟨hv, Subgroup.mem_centralizer_iff.2 fun w hw => ?_⟩
        rw [Set.mem_singleton_iff] at hw
        subst hw
        exact (hcomm v hv).symm
      rw [hqV] at h2
      have h3 : Nat.card K ^ 5 < Nat.card K ^ 6 := Nat.pow_lt_pow_right (by omega) (by norm_num)
      omega
  have ha : ∀ F : Subgroup (MulAut (StatedSp 3 K)), F ≤ T →
      (∀ x ∈ F, ∀ y ∈ F, x * y = y * x) → (∀ x ∈ F, x ^ 2 = 1) →
        (F ⊓ (unipotent 3 K).map cj).relIndex F ≤ 2 := by
    intro F hFT hFc hFs
    have hF : F ⊓ (unipotent 3 K).map cj = F ⊓ InnL (StatedSp 3 K) := by
      rw [← hT]
      ext x
      simp only [Subgroup.mem_inf]
      exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, hFT h.1, h.2⟩⟩
    rw [hF]
    exact relIndex_inf_inner_le_two outPChain_two_statedSp F hFc hFs
  have hb : ∀ F : Subgroup (MulAut (StatedSp 3 K)), F ≤ (unipotent 3 K).map cj →
      (∀ x ∈ F, ∀ y ∈ F, x * y = y * x) → (∀ x ∈ F, x ^ 2 = 1) →
        ¬ F ≤ (siegelRadicalSp 3 K).map cj →
          (F ⊓ (siegelRadicalSp 3 K).map cj).relIndex F *
            Nat.card ↥(((siegelRadicalSp 3 K).map cj) ⊓
              Subgroup.centralizer (F : Set (MulAut (StatedSp 3 K)))) ≤ Nat.card K ^ 5 := by
    intro F hFU hFc hFs hFV
    set F₀ : Subgroup (StatedSp 3 K) := F.comap cj with hF₀
    have hFrange : F ≤ cj.range := hFU.trans (Subgroup.map_le_range cj _)
    have hFF₀ : F₀.map cj = F := by
      rw [hF₀, Subgroup.map_comap_eq, inf_eq_right.mpr hFrange]
    have hF₀U : F₀ ≤ unipotent 3 K := by
      intro x hx
      obtain ⟨u, hu, hux⟩ := hFU hx
      have := hinj hux
      rwa [← this]
    have hF₀c : ∀ x ∈ F₀, ∀ y ∈ F₀, x * y = y * x := by
      intro x hx y hy
      apply hinj
      rw [map_mul, map_mul]
      exact hFc _ hx _ hy
    have hF₀s : ∀ x ∈ F₀, x ^ 2 = 1 := by
      intro x hx
      apply hinj
      rw [map_pow, map_one]
      exact hFs _ hx
    have hF₀V : ¬ F₀ ≤ siegelRadicalSp 3 K := by
      intro h
      apply hFV
      rw [← hFF₀]
      exact Subgroup.map_mono h
    have h1 := offender_bound_sp F₀ hF₀U hF₀c hF₀s hF₀V
    have e1 : F ⊓ (siegelRadicalSp 3 K).map cj = (F₀ ⊓ siegelRadicalSp 3 K).map cj := by
      rw [Subgroup.map_inf _ _ _ hinj, hFF₀]
    have e2 : (F ⊓ (siegelRadicalSp 3 K).map cj).relIndex F =
        (F₀ ⊓ siegelRadicalSp 3 K).relIndex F₀ := by
      rw [← Subgroup.relIndex_map_map_of_injective (F₀ ⊓ siegelRadicalSp 3 K) F₀ hinj, ← e1,
        hFF₀]
    have e3 : ((siegelRadicalSp 3 K).map cj) ⊓
        Subgroup.centralizer (F : Set (MulAut (StatedSp 3 K))) =
          ((siegelRadicalSp 3 K) ⊓ Subgroup.centralizer (F₀ : Set (StatedSp 3 K))).map cj := by
      rw [Sec9B.map_inf_centralizer_map hinj, hFF₀]
    rw [e2, e3, Subgroup.card_map_of_injective hinj]
    exact h1
  refine pushingUpS_eq_of_bounds (n := f * 6) (m := 2) (B₁ := Nat.card K ^ 5)
    (B₂ := Nat.card K ^ 5) hVU (hVU.trans hUT) hVc hVs hVcard hCT (by norm_num) ha hb hc ?_ ?_
  · rw [hqV]
    have h5 : 0 < Nat.card K ^ 5 := pow_pos Nat.card_pos 5
    calc 2 * Nat.card K ^ 5 < Nat.card K * Nat.card K ^ 5 :=
          Nat.mul_lt_mul_of_pos_right hq h5
      _ = Nat.card K ^ 6 := by ring
  · rw [hqV]
    have h5 : 0 < Nat.card K ^ 5 := pow_pos Nat.card_pos 5
    calc 2 * Nat.card K ^ 5 < Nat.card K * Nat.card K ^ 5 :=
          Nat.mul_lt_mul_of_pos_right hq h5
      _ = Nat.card K ^ 6 := by ring

omit [Finite K] [CharP K 2] in
theorem conj_mem_normalizer_siegel {t : StatedSp 3 K} (ht : t ∈ torus 3 K) :
    (MulAut.conj t : MulAut (StatedSp 3 K)) ∈ Subgroup.normalizer
      ((((siegelRadicalSp 3 K).map
        (MulAut.conj : StatedSp 3 K →* MulAut (StatedSp 3 K)) :
          Subgroup (MulAut (StatedSp 3 K)))) : Set (MulAut (StatedSp 3 K))) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · rintro ⟨v, hv, rfl⟩
    refine ⟨t * v * t⁻¹, torus_conj_mem_siegel ht hv, ?_⟩
    simp [map_mul, map_inv]
  · rintro ⟨v, hv, hvh⟩
    refine ⟨t⁻¹ * v * t, ?_, ?_⟩
    · have := torus_conj_mem_siegel (inv_mem ht) hv
      simpa using this
    · have h1 : (MulAut.conj v : MulAut (StatedSp 3 K)) =
          MulAut.conj t * h * (MulAut.conj t)⁻¹ := by
        rw [← hvh]
      simp only [map_mul, map_inv, h1]
      group

theorem xHat_normalized {T : Subgroup (MulAut (StatedSp 3 K))}
    (hT : T ⊓ InnL (StatedSp 3 K) =
      (unipotent 3 K).map (MulAut.conj : StatedSp 3 K →* MulAut (StatedSp 3 K))) :
    ∀ t ∈ T, ∀ x ∈ (longRoot K).map
        (MulAut.conj : StatedSp 3 K →* MulAut (StatedSp 3 K)), t * x * t⁻¹ ∈ (longRoot K).map
          (MulAut.conj : StatedSp 3 K →* MulAut (StatedSp 3 K)) := by
  intro t ht x hx
  obtain ⟨x₀, hx₀, rfl⟩ := hx
  rw [mulAut_mul_conj_mul_inv]
  exact ⟨t x₀, longRoot_stable (stable_unipotent hT ht) x₀ hx₀, rfl⟩

theorem hA_sp {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ Nat.card K - 1) :
    ∀ A₀ : Subgroup (MulAut (StatedSp 3 K)), A₀ ≤ InnL (StatedSp 3 K) →
      IsElementaryAbelian p ↥A₀ → Nat.card ↥A₀ = p ^ 3 →
      ∃ g ∈ InnL (StatedSp 3 K),
        (∃ B : Subgroup (MulAut (StatedSp 3 K)), B ≤ A₀ ∧ Nat.card ↥A₀ ≤ p * Nat.card ↥B ∧
          B.map (MulAut.conj g).toMonoidHom ≤ Subgroup.normalizer
            ((((siegelRadicalSp 3 K).map
              (MulAut.conj : StatedSp 3 K →* MulAut (StatedSp 3 K)) :
                Subgroup (MulAut (StatedSp 3 K)))) : Set (MulAut (StatedSp 3 K)))) ∧
        (∃ B : Subgroup (MulAut (StatedSp 3 K)), B ≤ A₀ ∧ Nat.card ↥A₀ ≤ p * Nat.card ↥B ∧
          ∀ x ∈ (longRoot K).map (MulAut.conj : StatedSp 3 K →* MulAut (StatedSp 3 K)), x ≠ 1 →
            B.map (MulAut.conj g).toMonoidHom ≤
              Subgroup.centralizer ({x} : Set (MulAut (StatedSp 3 K)))) := by
  intro A₀ hA₀Inn hel hcard
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hinj := conj_injective_sp (K := K)
  set cj : StatedSp 3 K →* MulAut (StatedSp 3 K) := MulAut.conj with hcj
  set A' : Subgroup (StatedSp 3 K) := A₀.comap cj with hA'
  have hA'map : A'.map cj = A₀ := by
    rw [hA', Subgroup.map_comap_eq, inf_eq_right.mpr hA₀Inn]
  have hApow : ∀ a ∈ A', a ^ p = 1 := by
    intro a ha
    have h1 : (cj a) ^ p = 1 := elemPow_eq_one_of_isElementaryAbelian (p := p) (A := A₀) (cj a) ha
    apply hinj
    rw [map_pow, map_one]
    exact h1
  have hpg : IsPGroup p A' := fun a => ⟨1, by
    rw [pow_one]
    exact Subtype.ext (hApow a a.2)⟩
  obtain ⟨s, hs⟩ := exists_conj_torus hp hp5 hpq hpg
  obtain ⟨B₀, hB₀A, hB₀c, hB₀τ⟩ := exists_index_le_torus hp.pos hApow s hs
  have hcardA : Nat.card ↥A₀ = Nat.card ↥A' := by
    rw [← hA'map, Subgroup.card_map_of_injective hinj]
  have hconj : ∀ a : StatedSp 3 K, (MulAut.conj (cj s⁻¹) : MulAut (MulAut (StatedSp 3 K)))
      (cj a) = cj (s⁻¹ * a * s) := fun a => by
    simp [map_mul, map_inv]
  refine ⟨cj s⁻¹, ⟨s⁻¹, rfl⟩, ⟨A₀, le_rfl, Nat.le_mul_of_pos_left _ hp.pos, ?_⟩,
    ⟨B₀.map cj, ?_, ?_, ?_⟩⟩
  · rintro _ ⟨b, hb, rfl⟩
    rw [← hA'map] at hb
    obtain ⟨a, ha, rfl⟩ := hb
    show (MulAut.conj (cj s⁻¹) : MulAut (MulAut (StatedSp 3 K))) (cj a) ∈ _
    rw [hconj]
    exact conj_mem_normalizer_siegel (hs a ha)
  · rw [← hA'map]
    exact Subgroup.map_mono hB₀A
  · rw [Subgroup.card_map_of_injective hinj, hcardA]
    exact hB₀c
  · intro x hx hx1
    obtain ⟨x₀, hx₀, rfl⟩ := hx
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨b, hb, rfl⟩ := hy
    obtain ⟨τ, hτ0, hτ⟩ := hB₀τ b hb
    show (MulAut.conj (cj s⁻¹) : MulAut (MulAut (StatedSp 3 K))) (cj b) ∈ _
    rw [hconj, hτ, Subgroup.mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    subst hw
    rw [← map_mul, ← map_mul, ← torusHom_comm_longRoot hτ0 hx₀]

theorem kf1514PAutGen_sp {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ Nat.card K - 1) :
    KF1514PAutGen (StatedSp 3 K) p := by
  have hq : 2 < Nat.card K := by
    have h2 : 1 < Nat.card K := Finite.one_lt_card
    have h1 : 0 < Nat.card K - 1 := by omega
    have := Nat.le_of_dvd h1 hpq
    omega
  have hinj := conj_injective_sp (K := K)
  refine kf1514PAutGen_of_data (p := p) _ _ _ isSylowOf_unipotent ?_ ?_ ?_ ?_ ?_ (hA_sp hp hp5 hpq)
  · intro T _ hT
    exact pushingUpS_eq_siegel hq hT
  · obtain ⟨x, hx, hx1⟩ := exists_ne_one_mem_longRoot (K := K)
    rw [Ne, Subgroup.eq_bot_iff_forall]
    intro h
    exact hx1 (hinj ((h _ ⟨x, hx, rfl⟩).trans (map_one _).symm))
  · exact Subgroup.map_mono (longRoot_le_siegel.trans siegel_le_unipotent)
  · rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, (siegel_elemAbelian (K := K)).2 x (longRoot_le_siegel hx), map_one]
  · intro T _ hT
    exact xHat_normalized hT

end Setup

theorem kf1514PAut_two : KF1514PAut 2 := by
  show ∀ (p f : ℕ), p.Prime → 5 ≤ p → 1 ≤ f → p ∣ 2 ^ f - 1 →
    KF1514PAutGen ↥(projSp 3 (GaloisField 2 f)) p
  intro p f hp hp5 hf hpf
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : NeZero f := ⟨by omega⟩
  have hcardK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hpq : p ∣ Nat.card (GaloisField 2 f) - 1 := by
    rw [hcardK]
    exact hpf
  have hS := kf1514PAutGen_sp (K := GaloisField 2 f) hp hp5 hpq
  have hbij : Function.Bijective (proj 3 (GaloisField 2 f)) :=
    UnitaryHigher.proj_bijective_of_charTwo
  let ψ : StatedSp 3 (GaloisField 2 f) ≃* StatedProj (StatedSp 3 (GaloisField 2 f)) :=
    MulEquiv.ofBijective (proj 3 (GaloisField 2 f)) hbij
  let e : ↥(projSp 3 (GaloisField 2 f)) ≃* StatedSp 3 (GaloisField 2 f) :=
    (ψ.trans (S15K.statedProjEquivProjSp 3 (GaloisField 2 f))).symm
  have : Finite ↥(projSp 3 (GaloisField 2 f)) := Finite.of_equiv _ e.symm.toEquiv
  exact kf1514PAutGen_of_mulEquiv e hp hS

end KSP6

end CFSG.RankThree.PartOne
