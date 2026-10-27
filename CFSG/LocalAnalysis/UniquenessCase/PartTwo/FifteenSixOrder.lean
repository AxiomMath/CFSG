module

public import CFSG.GF2Type.Aschbacher1976Full.HSGL3
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenTwo
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs15
public import CFSG.Quasithin.Background.D2Basic
public import CFSG.LocalAnalysis.SectionRank.Ccomm.Supercritical

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem s15_Six_mem_stabSub_of_map {U : Type} [CommGroup U] {A : Subgroup U} {φ : MulAut U}
    (h : A.map φ.toMonoidHom = A) : φ ∈ stabSub A := by
  intro u
  constructor
  · intro hu
    rw [← h] at hu
    obtain ⟨a, ha, hau⟩ := Subgroup.mem_map.1 hu
    exact φ.injective hau ▸ ha
  · intro hu
    rw [← h]
    exact Subgroup.mem_map.2 ⟨u, hu, rfl⟩

theorem s15_Six_card_dvd_of_two_summands {U : Type} [CommGroup U] [Finite U]
    (hsq : ∀ a : U, a * a = 1) {A B : Subgroup U}
    (hA : Nat.card A = 8) (hB : Nat.card B = 8) (hinf : A ⊓ B = ⊥) (hsup : A ⊔ B = ⊤)
    {X : Subgroup (MulAut U)}
    (hperm : ∀ φ ∈ X, (A.map φ.toMonoidHom = A ∨ A.map φ.toMonoidHom = B) ∧
      (B.map φ.toMonoidHom = A ∨ B.map φ.toMonoidHom = B)) :
    Nat.card X ∣ 2 * 168 ^ 2 := by
  have hAB : A ≠ B := by
    rintro rfl
    rw [inf_idem] at hinf
    rw [hinf, Subgroup.card_bot] at hA
    omega
  set S : Subgroup X := MulAction.stabilizer X A with hS
  have hSA : ∀ φ : S, A.map (φ.1 : MulAut U).toMonoidHom = A := fun φ =>
    (Subgroup.pointwise_smul_def A).symm.trans (MulAction.mem_stabilizer_iff.1 φ.2)
  have hSB : ∀ φ : S, B.map (φ.1 : MulAut U).toMonoidHom = B := fun φ => by
    rcases (hperm φ.1.1 φ.1.2).2 with h | h
    · exact absurd (Subgroup.map_injective (φ.1 : MulAut U).injective (h.trans (hSA φ).symm)).symm
        hAB
    · exact h
  let f₁ : S →* stabSub A := ((X.subtype).comp S.subtype).codRestrict (stabSub A)
    fun φ => s15_Six_mem_stabSub_of_map (hSA φ)
  let f₂ : S →* stabSub B := ((X.subtype).comp S.subtype).codRestrict (stabSub B)
    fun φ => s15_Six_mem_stabSub_of_map (hSB φ)
  let ι : S →* MulAut A × MulAut B := ((resHom A).comp f₁).prod ((resHom B).comp f₂)
  have hinj : Function.Injective ι := by
    rw [injective_iff_map_eq_one]
    intro φ hφ
    have h1 : resHom A (f₁ φ) = 1 := congrArg Prod.fst hφ
    have h2 : resHom B (f₂ φ) = 1 := congrArg Prod.snd hφ
    have hfixA : ∀ a ∈ A, (φ.1 : MulAut U) a = a := fun a ha =>
      congrArg (fun ψ : MulAut A => (ψ ⟨a, ha⟩ : U)) h1
    have hfixB : ∀ b ∈ B, (φ.1 : MulAut U) b = b := fun b hb =>
      congrArg (fun ψ : MulAut B => (ψ ⟨b, hb⟩ : U)) h2
    refine Subtype.ext (Subtype.ext (MulEquiv.ext fun u => ?_))
    have hu : u ∈ A ⊔ B := hsup ▸ Subgroup.mem_top u
    obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.1 hu
    show (φ.1 : MulAut U) (a * b) = a * b
    rw [map_mul, hfixA a ha, hfixB b hb]
  have hcomm : ∀ (C : Subgroup U) (a b : C), a * b = b * a := fun C a b =>
    Subtype.ext (mul_comm a.1 b.1)
  have hsqC : ∀ (C : Subgroup U) (a : C), a * a = 1 := fun C a => Subtype.ext (hsq a.1)
  have hS168 : Nat.card S ∣ 168 ^ 2 := by
    have h := Subgroup.card_dvd_of_injective ι hinj
    rwa [Nat.card_prod, CFSG.GF2Type.Aschbacher1976Full.HS.card_mulAut_eq_168 hA (hcomm A) (hsqC A),
      CFSG.GF2Type.Aschbacher1976Full.HS.card_mulAut_eq_168 hB (hcomm B) (hsqC B), ← pow_two] at h
  have hidx : S.index ≤ 2 := by
    rw [hS, MulAction.index_stabilizer]
    have hsub : MulAction.orbit X A ⊆ {A, B} := by
      rintro _ ⟨φ, rfl⟩
      have h1 := (hperm φ.1 φ.2).1
      have h2 : φ • A = A.map (φ : MulAut U).toMonoidHom := Subgroup.pointwise_smul_def A
      show φ • A ∈ ({A, B} : Set (Subgroup U))
      rw [h2]
      simpa using h1
    exact (Set.ncard_le_ncard hsub (Set.toFinite _)).trans (Set.ncard_pair hAB ▸ le_rfl)
  have hpos : 0 < S.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  rw [← Subgroup.card_mul_index S]
  obtain h | h : S.index = 1 ∨ S.index = 2 := by omega
  · rw [h, mul_one]
    exact hS168.trans (Dvd.intro_left 2 rfl)
  · rw [h, mul_comm]
    exact mul_dvd_mul_left 2 hS168

theorem s15_Six_map_mem_wStarConj {D : Data G} {V₀ V L : Subgroup G}
    (h : Hyp125 D V₀ V) (hV : IsElemAbelian 2 V)
    {e : MulAut (vStar D.M V₀ V hV L)} (he : e ∈ Mbar D.M (v1Sub D.M V₀ V hV L) V hV)
    {Z : Subgroup (vStar D.M V₀ V hV L)} (hZ : Z ∈ wStarConj D.M V₀ V hV L) :
    Z.map e.toMonoidHom ∈ wStarConj D.M V₀ V hV L := by
  obtain ⟨m, hm, rfl⟩ := hZ
  have hm_st : m ∈ stabTil (v1Sub D.M V₀ V hV L) V :=
    le_stabTil h.pairFacts.le_normalizer (s15_Infra_le_normalizer_v1Sub h hV) hm
  have he' : (actTil (v1Sub D.M V₀ V hV L) V hV ⟨m, hm_st⟩)⁻¹ ∈
      Mbar D.M (v1Sub D.M V₀ V hV L) V hV :=
    Subgroup.inv_mem _ (actTil_mem_barSub _ V hV hm hm_st)
  have h1 := s15_Infra_map_wStar_mem_wStarConj (L := L) h hV (Subgroup.mul_mem _ he he')
  rw [s15_Infra_imgTil_conjSubgroup (v1Sub D.M V₀ V hV L) V (wSub V₀ V hV L) hV hm_st,
    Subgroup.map_map]
  exact h1

theorem s15_Six_card_mbar_dvd (D : Data G) (h1217 : R1217 D) {V₀ V L : Subgroup G}
    (h : Hyp151 D V₀ V L) (hV : IsElemAbelian 2 V) (hL : barSub V₀ V hV L ≠ ⊥)
    (hγ : gamma15 D.M V₀ V hV L = 3) (hs : s15 D.M V₀ V hV L = 2) :
    Nat.card (Mbar D.M (v1Sub D.M V₀ V hV L) V hV) ∣ 2 * 168 ^ 2 := by
  obtain ⟨hind, hsup⟩ := fifteen_two_directSum D h1217 h hV hL
  obtain ⟨x, y, hxy, hP⟩ := Set.ncard_eq_two.1 ((ncard_wStarConj D h hV).trans hs)
  have hx : x ∈ wStarConj D.M V₀ V hV L := hP ▸ Set.mem_insert x {y}
  have hy : y ∈ wStarConj D.M V₀ V hV L := hP ▸ Set.mem_insert_of_mem x rfl
  rw [hP] at hind hsup
  have hdisj : x ⊓ y = ⊥ := disjoint_iff.1 ((sSupIndep_pair hxy).1 hind)
  rw [sSup_pair] at hsup
  have hsq : ∀ a : vStar D.M V₀ V hV L, a * a = 1 := fun a => by
    rw [← pow_two]
    exact s15_Infra_vtil_sq_eq_one _ V hV a
  have hpg : ∀ Z : Subgroup (vStar D.M V₀ V hV L), IsPGroup 2 Z := fun Z =>
    isPGroup_two_of_sq_eq_one fun a => Subtype.ext (by simpa [pow_two] using hsq a.1)
  have hcard : ∀ Z ∈ wStarConj D.M V₀ V hV L, Nat.card Z = 8 := fun Z hZ => by
    rw [card_eq_two_pow_mSub (hpg Z)]
    show 2 ^ rk ↥Z = 8
    rw [s15_Two_rk_wStarConj h hV hZ, hγ]
    norm_num
  refine s15_Six_card_dvd_of_two_summands hsq (hcard x hx) (hcard y hy) hdisj hsup fun φ hφ => ?_
  have h1 := fun Z (hZ : Z ∈ wStarConj D.M V₀ V hV L) => by
    have := s15_Six_map_mem_wStarConj (L := L) h.hyp125 hV hφ hZ
    rwa [hP] at this
  refine ⟨?_, ?_⟩
  · simpa using h1 x hx
  · simpa using h1 y hy

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
