module

import CFSG.LocalAnalysis.EvenBN.GMSK.SzFacts
import CFSG.Models.BenderSuzuki
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Sz5

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22

private theorem sz5e1_s13_exists_mulEquiv_suzukiMatrixGroup_of_lieModel_twistedB2
    {X : Type} [Group X] {n : ℕ} (h : CFSG.Blueprint.LieModel X .twistedB2 0 2 n) :
    ∃ a : ℕ, 1 ≤ a ∧ n = 2 * a + 1 ∧
      Nonempty (X ≃* CFSG.BenderSuzuki.MatrixGroups.SuzukiMatrixGroup a) := by
  obtain ⟨a, ha, hn, ⟨e⟩⟩ :=
    CFSG.LocalAnalysis.EvenBN.GMSK.exists_mulEquiv_sz_of_lieModel_twistedB2 h
  have hmodel : CFSG.Theory.Comparator.SzModel a = CFSG.Open.Sz a :=
    CFSG.Models.benderSzModel_eq_sz a
  exact ⟨a, ha, hn, ⟨e.trans (MulEquiv.subgroupCongr
    (hmodel.symm.trans (CFSG.BenderSuzuki.szModel_eq_suzukiMatrixGroup a)))⟩⟩

theorem sz5e1_sz8_thirteen_dvd {X : Type} [Group X] (h : IsSz X 3) : 13 ∣ Nat.card X := by
  unfold IsSz at h
  obtain ⟨a, _ha, hthree, ⟨e⟩⟩ :=
    sz5e1_s13_exists_mulEquiv_suzukiMatrixGroup_of_lieModel_twistedB2 h
  have ha1 : a = 1 := by omega
  rw [ha1] at e
  rw [Nat.card_congr e.toEquiv]
  let K := CFSG.BenderSuzuki.PFAppendixIII.BinaryGaloisField (2 * 1 + 1)
  let pi : K ≃+* K := iterateFrobeniusEquiv K 2 (1 + 1)
  have hpi : ∀ x : K, pi x = x ^ (2 ^ (1 + 1)) := by
    intro x
    exact iterateFrobeniusEquiv_def K 2 (1 + 1) x
  rcases CFSG.BenderSuzuki.External.huppert_blackburn_XI_3_3 1 (by norm_num) pi hpi with
    ⟨_, _, _, _, _, _, hGcard, _⟩
  rw [hGcard]
  norm_num

private theorem sz5e1_sfr_exists_mulEquiv_suzukiMatrixGroup_of_lieModel_twistedB2
    {X : Type} [Group X] {n : ℕ} (h : CFSG.Blueprint.LieModel X .twistedB2 0 2 n) :
    ∃ a : ℕ, 1 ≤ a ∧ n = 2 * a + 1 ∧
      Nonempty (X ≃* CFSG.BenderSuzuki.MatrixGroups.SuzukiMatrixGroup a) := by
  obtain ⟨a, ha, hn, ⟨e⟩⟩ :=
    CFSG.LocalAnalysis.EvenBN.GMSK.exists_mulEquiv_sz_of_lieModel_twistedB2 h
  have hmodel : CFSG.Theory.Comparator.SzModel a = CFSG.Open.Sz a :=
    CFSG.Models.benderSzModel_eq_sz a
  exact ⟨a, ha, hn, ⟨e.trans (MulEquiv.subgroupCongr
    (hmodel.symm.trans (CFSG.BenderSuzuki.szModel_eq_suzukiMatrixGroup a)))⟩⟩

private theorem sz5e1_sfr_matrix :
    ∃ (S Z : Subgroup (CFSG.BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 1))
      (y : CFSG.BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 1),
      Z ≤ S ∧ (∀ z ∈ Z, ∀ s ∈ S, z * s = s * z) ∧ Nat.card Z = 8 ∧
      (∀ z ∈ Z, z ^ 2 = 1) ∧
      (∃ a ∈ S, ∃ b ∈ S, a * b ≠ b * a) ∧
      orderOf y = 7 ∧ (∀ z ∈ Z, y * z * y⁻¹ ∈ Z) ∧
      (∀ z ∈ Z, y * z * y⁻¹ = z → z = 1) := by
  classical
  let K := CFSG.BenderSuzuki.PFAppendixIII.BinaryGaloisField (2 * 1 + 1)
  let G := CFSG.BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 1
  let pi : K ≃+* K := iterateFrobeniusEquiv K 2 (1 + 1)
  have hpi : ∀ x : K, pi x = x ^ (2 ^ (1 + 1)) :=
    fun x => iterateFrobeniusEquiv_def K 2 (1 + 1) x
  have hpi_sq : ∀ x : K, pi (pi x) = x ^ 2 :=
    CFSG.BenderSuzuki.External.binaryGaloisField_tits_formula_sq 1 pi hpi
  let F : Subgroup (GL (Fin 4) K) :=
    Subgroup.closure {A | ∃ a b : K, A = CFSG.BenderSuzuki.MatrixGroups.SuzukiRootGL 1 a b}
  let H : Subgroup (GL (Fin 4) K) :=
    Subgroup.closure {A | ∃ x : Kˣ, A = CFSG.BenderSuzuki.MatrixGroups.SuzukiTorusGL 1 x}
  rcases CFSG.BenderSuzuki.External.huppert_blackburn_XI_3_1 1 (by norm_num) pi hpi_sq with
    ⟨_hpi_unique, hpi_formula, _hFp, _hF_pow_four, _hF_order_four, _hF_class,
      hFcard, _hF_typeA, _hroot_mul, _hcommutator, _hcommutator_coordinates,
      htorus_equiv, _htorus_conj, _hdisjoint, hfixed_point_free⟩
  obtain ⟨hFcenterPow, hFcenterCard⟩ :=
    CFSG.BenderSuzuki.External.suzukiRootClosure_center_data 1 (by norm_num) pi hpi_sq
  have hF_le_G : F ≤ G := by
    dsimp only [F]
    rw [Subgroup.closure_le]
    intro A hA
    exact Subgroup.subset_closure (Or.inl hA)
  have hH_le_G : H ≤ G := by
    dsimp only [H]
    rw [Subgroup.closure_le]
    intro A hA
    exact Subgroup.subset_closure (Or.inr (Or.inl hA))
  have hH_le_normalizerF : H ≤ Subgroup.normalizer (F : Set (GL (Fin 4) K)) :=
    CFSG.BenderSuzuki.External.suzukiTorusClosure_le_normalizer_rootClosure 1 pi hpi_sq
      hpi_formula
  let Z₀ : Subgroup (GL (Fin 4) K) := (Subgroup.center F).map F.subtype
  have hZ₀_le_F : Z₀ ≤ F := Subgroup.map_subtype_le (Subgroup.center F)
  have hZ₀_le_G : Z₀ ≤ G := hZ₀_le_F.trans hF_le_G
  let S : Subgroup G := F.subgroupOf G
  let Z : Subgroup G := Z₀.subgroupOf G
  have hZS : Z ≤ S := by
    intro z hz
    rw [Subgroup.mem_subgroupOf] at hz ⊢
    exact hZ₀_le_F hz
  have hcent : ∀ z ∈ Z, ∀ s ∈ S, z * s = s * z := by
    intro z hz s hs
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_map] at hz
    rw [Subgroup.mem_subgroupOf] at hs
    obtain ⟨z', hz', hz'z⟩ := hz
    let s' : F := ⟨(s : GL (Fin 4) K), hs⟩
    have hs' : F.subtype s' = (s : GL (Fin 4) K) := rfl
    apply Subtype.ext
    show ((z : G) : GL (Fin 4) K) * ((s : G) : GL (Fin 4) K) =
         ((s : G) : GL (Fin 4) K) * ((z : G) : GL (Fin 4) K)
    rw [← hz'z, ← hs']
    show (F.subtype z' : GL (Fin 4) K) * (F.subtype s' : GL (Fin 4) K) =
         (F.subtype s' : GL (Fin 4) K) * (F.subtype z' : GL (Fin 4) K)
    calc (F.subtype z' : GL (Fin 4) K) * (F.subtype s' : GL (Fin 4) K)
        = F.subtype (z' * s') := (map_mul F.subtype z' s').symm
      _ = F.subtype (s' * z') :=
          (congrArg F.subtype (Subgroup.mem_center_iff.mp hz' s')).symm
      _ = (F.subtype s' : GL (Fin 4) K) * (F.subtype z' : GL (Fin 4) K) :=
          map_mul F.subtype s' z'
  have hZcard : Nat.card Z = 8 := by
    calc Nat.card Z = Nat.card Z₀ :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZ₀_le_G).toEquiv
      _ = Nat.card (Subgroup.center F) := Subgroup.card_subtype F (Subgroup.center F)
      _ = 2 ^ (2 * 1 + 1) := hFcenterCard
      _ = 8 := by norm_num
  have hZsq : ∀ z ∈ Z, z ^ 2 = 1 := by
    intro z hz
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_map] at hz
    obtain ⟨z', hz', hz'z⟩ := hz
    apply Subtype.ext
    show ((z : G) : GL (Fin 4) K) ^ 2 = 1
    rw [← hz'z]
    show (F.subtype z' : GL (Fin 4) K) ^ 2 = 1
    rw [pow_two, ← map_mul, ← pow_two, hFcenterPow z' hz', map_one]
  have hnonab : ∃ a ∈ S, ∃ b ∈ S, a * b ≠ b * a := by
    have hF_not_comm : ∃ a b : F, a * b ≠ b * a := by
      by_contra hcon
      push Not at hcon
      have hcenter_top : Subgroup.center F = ⊤ := by
        rw [Subgroup.center_eq_top_iff]
        exact isMulCommutative_iff.mpr hcon
      have hcard_eq : Nat.card F = Nat.card (Subgroup.center F) := by
        rw [hcenter_top]
        exact (Subgroup.card_top (G := ↥F)).symm
      rw [hFcard, hFcenterCard] at hcard_eq
      exact absurd hcard_eq (by norm_num)
    have hF_not_comm_GL : ∃ a b : GL (Fin 4) K, a ∈ F ∧ b ∈ F ∧ a * b ≠ b * a := by
      obtain ⟨a₀, b₀, hab₀⟩ := hF_not_comm
      exact ⟨(a₀ : GL (Fin 4) K), (b₀ : GL (Fin 4) K), a₀.2, b₀.2,
        fun h => hab₀ (Subtype.ext h)⟩
    obtain ⟨a₀, b₀, ha₀, hb₀, hab₀⟩ := hF_not_comm_GL
    refine ⟨⟨a₀, hF_le_G ha₀⟩, ha₀, ⟨b₀, hF_le_G hb₀⟩, hb₀, ?_⟩
    intro h
    exact hab₀ (Subtype.ext_iff.mp h)
  obtain ⟨eH, heH⟩ := htorus_equiv
  have hKcard : Nat.card K = 8 := by
    have h : Nat.card K = 2 ^ (2 * 1 + 1) :=
      GaloisField.card 2 (2 * 1 + 1) (by norm_num)
    rw [h]
    norm_num
  have hKunits : Nat.card Kˣ = 7 := by
    rw [Nat.card_units K, hKcard]
  obtain ⟨u, hu⟩ := IsCyclic.exists_generator (α := Kˣ)
  have huord : orderOf u = 7 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hu, hKunits]
  let y : G := ⟨CFSG.BenderSuzuki.MatrixGroups.SuzukiTorusGL 1 u,
    hH_le_G (Subgroup.subset_closure ⟨u, rfl⟩)⟩
  have hyH : (y : GL (Fin 4) K) ∈ H :=
    Subgroup.subset_closure ⟨u, rfl⟩
  have hyord : orderOf y = 7 := by
    have h1 : orderOf y = orderOf (y : GL (Fin 4) K) :=
      Subgroup.orderOf_mk (y : GL (Fin 4) K) y.2
    rw [h1]
    change orderOf (CFSG.BenderSuzuki.MatrixGroups.SuzukiTorusGL 1 u) = 7
    rw [← heH u, Subgroup.orderOf_coe, MulEquiv.orderOf_eq eH u, huord]
  have hyN : (y : GL (Fin 4) K) ∈ Subgroup.normalizer (F : Set (GL (Fin 4) K)) :=
    hH_le_normalizerF hyH
  have hynorm : ∀ z ∈ Z, y * z * y⁻¹ ∈ Z := by
    intro z hz
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_map] at hz
    obtain ⟨z', hz', hz'z⟩ := hz
    have hwF : (y : GL (Fin 4) K) * (z' : GL (Fin 4) K) * (y : GL (Fin 4) K)⁻¹ ∈ F :=
      (Subgroup.mem_normalizer_iff.mp hyN z').mp z'.2
    let w : F := ⟨(y : GL (Fin 4) K) * (z' : GL (Fin 4) K) * (y : GL (Fin 4) K)⁻¹, hwF⟩
    have hwcenter : w ∈ Subgroup.center F := by
      rw [Subgroup.mem_center_iff]
      intro g
      have hg''F : (y : GL (Fin 4) K)⁻¹ * (g : GL (Fin 4) K) * (y : GL (Fin 4) K) ∈ F :=
        (Subgroup.mem_normalizer_iff''.mp hyN (g : GL (Fin 4) K)).mp g.2
      let g'' : F :=
        ⟨(y : GL (Fin 4) K)⁻¹ * (g : GL (Fin 4) K) * (y : GL (Fin 4) K), hg''F⟩
      have hcomm :
          ((y : GL (Fin 4) K)⁻¹ * (g : GL (Fin 4) K) * (y : GL (Fin 4) K)) *
              (z' : GL (Fin 4) K) =
            (z' : GL (Fin 4) K) *
              ((y : GL (Fin 4) K)⁻¹ * (g : GL (Fin 4) K) * (y : GL (Fin 4) K)) :=
        congrArg Subtype.val (Subgroup.mem_center_iff.mp hz' g'')
      apply Subtype.ext
      show (g : GL (Fin 4) K) *
            ((y : GL (Fin 4) K) * (z' : GL (Fin 4) K) * (y : GL (Fin 4) K)⁻¹) =
          ((y : GL (Fin 4) K) * (z' : GL (Fin 4) K) * (y : GL (Fin 4) K)⁻¹) *
            (g : GL (Fin 4) K)
      calc (g : GL (Fin 4) K) *
            ((y : GL (Fin 4) K) * (z' : GL (Fin 4) K) * (y : GL (Fin 4) K)⁻¹)
          = (y : GL (Fin 4) K) *
              (((y : GL (Fin 4) K)⁻¹ * (g : GL (Fin 4) K) * (y : GL (Fin 4) K)) *
                (z' : GL (Fin 4) K)) * (y : GL (Fin 4) K)⁻¹ := by group
        _ = (y : GL (Fin 4) K) *
              ((z' : GL (Fin 4) K) *
                ((y : GL (Fin 4) K)⁻¹ * (g : GL (Fin 4) K) * (y : GL (Fin 4) K))) *
              (y : GL (Fin 4) K)⁻¹ := by rw [hcomm]
        _ = ((y : GL (Fin 4) K) * (z' : GL (Fin 4) K) * (y : GL (Fin 4) K)⁻¹) *
              (g : GL (Fin 4) K) := by group
    refine Subgroup.mem_map.mpr ⟨w, hwcenter, ?_⟩
    show (y : GL (Fin 4) K) * (z' : GL (Fin 4) K) * (y : GL (Fin 4) K)⁻¹ =
         (y : GL (Fin 4) K) * (z : GL (Fin 4) K) * (y : GL (Fin 4) K)⁻¹
    rw [← hz'z]
    rfl
  have hfixfree : ∀ z ∈ Z, y * z * y⁻¹ = z → z = 1 := by
    intro z hz hfix
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_map] at hz
    obtain ⟨z', hz', hz'z⟩ := hz
    have hyGL_ne_one : (y : GL (Fin 4) K) ≠ 1 := by
      intro h
      have hy1 : y = 1 := Subtype.ext h
      have h1 : orderOf y = 1 := by rw [hy1, orderOf_one]
      omega
    have hh_ne : (y : GL (Fin 4) K)⁻¹ ≠ 1 := fun h => hyGL_ne_one (inv_eq_one.mp h)
    have hfixGL : (y : GL (Fin 4) K) * (z' : GL (Fin 4) K) * (y : GL (Fin 4) K)⁻¹ =
        (z' : GL (Fin 4) K) := by
      have hh : (y : GL (Fin 4) K) * (z : GL (Fin 4) K) * (y : GL (Fin 4) K)⁻¹ =
          (z : GL (Fin 4) K) := by
        have := congrArg Subtype.val hfix
        simpa using this
      rw [← hz'z] at hh
      simpa using hh
    have hz'GL1 : (z' : GL (Fin 4) K) = 1 :=
      hfixed_point_free ((y : GL (Fin 4) K)⁻¹) (H.inv_mem hyH) hh_ne (z' : GL (Fin 4) K) z'.2
        (by simpa [inv_inv] using hfixGL)
    have hz'1 : z' = 1 := Subtype.ext hz'GL1
    apply Subtype.ext
    show (z : GL (Fin 4) K) = 1
    rw [← hz'z, hz'1, map_one]
  exact ⟨S, Z, y, hZS, hcent, hZcard, hZsq, hnonab, hyord, hynorm, hfixfree⟩

theorem sz5e1_sz8_frobenius {X : Type} [Group X] (h : IsSz X 3) :
    ∃ (S Z : Subgroup X) (y : X),
      Z ≤ S ∧ (∀ z ∈ Z, ∀ s ∈ S, z * s = s * z) ∧ Nat.card Z = 8 ∧ (∀ z ∈ Z, z ^ 2 = 1) ∧
      (∃ a ∈ S, ∃ b ∈ S, a * b ≠ b * a) ∧
      orderOf y = 7 ∧ (∀ z ∈ Z, y * z * y⁻¹ ∈ Z) ∧ (∀ z ∈ Z, y * z * y⁻¹ = z → z = 1) := by
  unfold IsSz at h
  obtain ⟨a, ha, hn, ⟨e⟩⟩ :=
    sz5e1_sfr_exists_mulEquiv_suzukiMatrixGroup_of_lieModel_twistedB2 h
  have ha1 : a = 1 := by omega
  subst a
  obtain ⟨S₀, Z₀, y₀, hZ₀S₀, hcent₀, hcard₀, hsq₀, hnonab₀, horder₀, hnorm₀, hfix₀⟩ :=
    sz5e1_sfr_matrix
  refine ⟨S₀.map e.symm.toMonoidHom, Z₀.map e.symm.toMonoidHom, e.symm y₀,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    rw [Subgroup.mem_map] at hz ⊢
    obtain ⟨z₀, hz₀, rfl⟩ := hz
    exact ⟨z₀, hZ₀S₀ hz₀, rfl⟩
  · intro z hz s hs
    rw [Subgroup.mem_map] at hz hs
    obtain ⟨z₀, hz₀, rfl⟩ := hz
    obtain ⟨s₀, hs₀, rfl⟩ := hs
    show e.symm z₀ * e.symm s₀ = e.symm s₀ * e.symm z₀
    rw [← map_mul, ← map_mul, hcent₀ z₀ hz₀ s₀ hs₀]
  · rw [Subgroup.card_map_of_injective (f := e.symm.toMonoidHom) e.symm.injective, hcard₀]
  · intro z hz
    rw [Subgroup.mem_map] at hz
    obtain ⟨z₀, hz₀, rfl⟩ := hz
    show e.symm z₀ ^ 2 = 1
    rw [← map_pow, hsq₀ z₀ hz₀, map_one]
  · obtain ⟨a₀, ha₀, b₀, hb₀, hab₀⟩ := hnonab₀
    refine ⟨e.symm a₀, ?_, e.symm b₀, ?_, ?_⟩
    · exact Subgroup.mem_map.mpr ⟨a₀, ha₀, rfl⟩
    · exact Subgroup.mem_map.mpr ⟨b₀, hb₀, rfl⟩
    · intro hh
      exact hab₀ (by simpa using congrArg e hh)
  · rw [MulEquiv.orderOf_eq e.symm y₀, horder₀]
  · intro z hz
    rw [Subgroup.mem_map] at hz
    obtain ⟨z₀, hz₀, rfl⟩ := hz
    exact Subgroup.mem_map.mpr ⟨y₀ * z₀ * y₀⁻¹, hnorm₀ z₀ hz₀, by simp [map_mul, map_inv]⟩
  · intro z hz hfix
    rw [Subgroup.mem_map] at hz
    obtain ⟨z₀, hz₀, rfl⟩ := hz
    have hh : y₀ * z₀ * y₀⁻¹ = z₀ := by
      have := congrArg e hfix
      simpa [map_mul, map_inv] using this
    rw [hfix₀ z₀ hz₀ hh, map_one]

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Sz5
