module

public import CFSG.RankThree.PartTwo.Sec13.Item13Prod
import CFSG.RankThree.PartTwo.Sec13.Item131Facts
import CFSG.RankThree.PartTwo.Sec13.Item136Lift
import CFSG.RankThree.PartTwo.Sec4.LThreePiCaseI
import CFSG.RankThree.PartOne.S12.ModelTransport
import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.RankThree.PartTwo.Sec13

open CFSG CFSG.Assembly.LowTwoRank Matrix
open CFSG.Assembly.RankThreeEven (projImage projSL projSU)
open CFSG.RankThree.PartTwo.Sec4 (slPi glPi PiField ModThree)
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

section Elem

variable {X : Type*} [Group X]

theorem isElemAbelian_zpowers_sup {x y : X} (hx : x ^ 3 = 1) (hy : y ^ 3 = 1)
    (hxy : x * y = y * x) :
    CFSG.Assembly.IsElemAbelian 3 (Subgroup.zpowers x ⊔ Subgroup.zpowers y) := by
  have hn : Subgroup.zpowers x ≤ Subgroup.normalizer (Subgroup.zpowers y : Set X) := by
    rw [Subgroup.zpowers_le]
    refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr ?_)
    intro z hz
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    exact (Commute.zpow_left (show Commute y x from hxy.symm) j)
  have hdec : ∀ z ∈ Subgroup.zpowers x ⊔ Subgroup.zpowers y, ∃ i j : ℤ, x ^ i * y ^ j = z := by
    intro z hz
    have hz' : z ∈ ((Subgroup.zpowers x ⊔ Subgroup.zpowers y : Subgroup X) : Set X) := hz
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hn] at hz'
    obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.mp hz'
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact ⟨i, j, rfl⟩
  have hc : Commute x y := hxy
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun z hz => ?_⟩
  · obtain ⟨i, j, hij⟩ := hdec a a.2
    obtain ⟨k, l, hkl⟩ := hdec b b.2
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [← hij, ← hkl]
    exact (Commute.mul_left (Commute.mul_right (Commute.zpow_zpow_self x i k)
      (hc.zpow_zpow i l)) (Commute.mul_right (hc.zpow_zpow k j).symm
        (Commute.zpow_zpow_self y j l))).eq
  · obtain ⟨i, j, rfl⟩ := hdec z hz
    rw [((hc.zpow_zpow i j).mul_pow 3), ← zpow_natCast, ← zpow_natCast (y ^ j), ← _root_.zpow_mul,
      ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, mul_comm (j : ℤ), _root_.zpow_mul,
      zpow_natCast, zpow_natCast, hx, hy, _root_.one_zpow, _root_.one_zpow, one_mul]

theorem isElemAbelian_zpowers {x : X} (hx : x ^ 3 = 1) :
    CFSG.Assembly.IsElemAbelian 3 (Subgroup.zpowers x) := CFSG.Open.isElemAbelian_zpowers hx

theorem isElemAbelian_sup [Finite X] {H K : Subgroup X} (hH : CFSG.Assembly.IsElemAbelian 3 H)
    (hK : CFSG.Assembly.IsElemAbelian 3 K) (hc : ∀ x ∈ H, ∀ y ∈ K, x * y = y * x) :
    CFSG.Assembly.IsElemAbelian 3 (H ⊔ K) := by
  have hcoe := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute H K hc).2
  have hdec : ∀ z ∈ H ⊔ K, ∃ x ∈ H, ∃ y ∈ K, x * y = z := by
    intro z hz
    have hz' : z ∈ ((H ⊔ K : Subgroup X) : Set X) := hz
    rw [hcoe] at hz'
    obtain ⟨x, hx, y, hy, rfl⟩ := Set.mem_mul.mp hz'
    exact ⟨x, hx, y, hy, rfl⟩
  have := hH.1
  have := hK.1
  have hHc : ∀ x ∈ H, ∀ x' ∈ H, x * x' = x' * x := fun x hx x' hx' =>
    congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : H) ⟨x', hx'⟩)
  have hKc : ∀ y ∈ K, ∀ y' ∈ K, y * y' = y' * y := fun y hy y' hy' =>
    congrArg Subtype.val (mul_comm' (⟨y, hy⟩ : K) ⟨y', hy'⟩)
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun z hz => ?_⟩
  · obtain ⟨x, hx, y, hy, hxy⟩ := hdec a a.2
    obtain ⟨x', hx', y', hy', hxy'⟩ := hdec b b.2
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [← hxy, ← hxy']
    have h1 : Commute x x' := hHc x hx x' hx'
    have h2 : Commute y y' := hKc y hy y' hy'
    have h3 : Commute x y' := hc x hx y' hy'
    have h4 : Commute y x' := (hc x' hx' y hy).symm
    exact (Commute.mul_left (Commute.mul_right h1 h3) (Commute.mul_right h4 h2)).eq
  · obtain ⟨x, hx, y, hy, rfl⟩ := hdec z hz
    rw [(show Commute x y from hc x hx y hy).mul_pow, hH.2 x hx, hK.2 y hy, one_mul]

end Elem

section PGL

variable {K : Type} [Field K] {p f : ℕ} {π : Bool}

theorem commutator_glPi (hK : PiField π p f K) (hq2 : 2 < p ^ f) :
    ⁅glPi π 3 (p ^ f) K, glPi π 3 (p ^ f) K⁆ = slPi π 3 (p ^ f) K := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [Sec4.mem_slPi_iff hπ]
    refine ⟨?_, ?_⟩
    · rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
    · have h1 : GeneralLinearGroup.det ⁅a, b⁆ = 1 := by
        rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
        exact mul_comm _ _
      have h2 : ((GeneralLinearGroup.det ⁅a, b⁆ : Kˣ) : K) = 1 := by rw [h1, Units.val_one]
      rwa [GeneralLinearGroup.val_det_apply] at h2
  · have : Group.IsPerfect (slPi π 3 (p ^ f) K) := isPerfect_slPi hK hq2
    have h1 : (⊤ : Subgroup (slPi π 3 (p ^ f) K)).map (slPi π 3 (p ^ f) K).subtype =
        slPi π 3 (p ^ f) K := by
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    calc slPi π 3 (p ^ f) K = (commutator (slPi π 3 (p ^ f) K)).map
          (slPi π 3 (p ^ f) K).subtype := by
            rw [Group.IsPerfect.commutator_eq_top, h1]
      _ = ⁅slPi π 3 (p ^ f) K, slPi π 3 (p ^ f) K⁆ := by
            rw [commutator_def, Subgroup.map_commutator, h1]
      _ ≤ ⁅glPi π 3 (p ^ f) K, glPi π 3 (p ^ f) K⁆ :=
            Subgroup.commutator_mono (Sec4.slPi_le_glPi hπ) (Sec4.slPi_le_glPi hπ)

theorem commutator_projImage_glPi (hK : PiField π p f K) (hq2 : 2 < p ^ f) :
    commutator (projImage (glPi π 3 (p ^ f) K)) =
      (projImage (slPi π 3 (p ^ f) K)).subgroupOf (projImage (glPi π 3 (p ^ f) K)) := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  set P := projImage (glPi π 3 (p ^ f) K)
  have hSP : projImage (slPi π 3 (p ^ f) K) ≤ P := Subgroup.map_mono (Sec4.slPi_le_glPi hπ)
  apply Subgroup.map_injective P.subtype_injective
  have h1 : (⊤ : Subgroup P).map P.subtype = P := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hSP, commutator_def,
    Subgroup.map_commutator, h1]
  change ⁅(glPi π 3 (p ^ f) K).map _, (glPi π 3 (p ^ f) K).map _⁆ =
    (slPi π 3 (p ^ f) K).map _
  rw [← Subgroup.map_commutator, commutator_glPi hK hq2]

theorem isLThreePi_projImage_slPi (hK : PiField π p f K) (hq : ModThree π (p ^ f)) :
    IsLThreePi (projImage (slPi π 3 (p ^ f) K)) := by
  have : Fact p.Prime := ⟨hK.prime⟩
  have := hK.finite
  have hf := hK.one_le
  refine ⟨p, f, inferInstance, hf, ?_⟩
  cases π
  · right
    refine ⟨hq, ?_⟩
    have hcard : Nat.card K = p ^ (2 * f) := by
      rw [hK.card]
      simp only [Sec4.piCard, Bool.cond_false]
      rw [← pow_mul, mul_comm]
    let φ : K ≃+* GaloisField p (2 * f) :=
      CFSG.ClassicalModels.finiteFieldEquivGaloisField K p (2 * f) (by omega) hcard
    rw [projSU_eq]
    exact ⟨(CFSG.Adapters.RankTwoModelTransports.statedProjEquivMapMk _).symm.trans
      (CFSG.RankThree.PartOne.statedProjEquivOfGLEquiv
        (CFSG.Adapters.RankTwoModelTransports.glCongr φ)
        (CFSG.Adapters.RankTwoModelTransports.glCongr_statedSU φ 3 (p ^ f))
        (CFSG.Adapters.RankTwoModelTransports.glCongr_statedScalars φ) rfl)⟩
  · left
    refine ⟨hq, ?_⟩
    have hcard : Nat.card K = p ^ f := hK.card
    let φ : K ≃+* GaloisField p f :=
      CFSG.ClassicalModels.finiteFieldEquivGaloisField K p f (by omega) hcard
    rw [projSL_eq]
    exact ⟨(CFSG.Adapters.RankTwoModelTransports.statedProjEquivMapMk _).symm.trans
      (CFSG.RankThree.PartOne.statedProjEquivOfGLEquiv
        (CFSG.Adapters.RankTwoModelTransports.glCongr φ)
        (CFSG.ClassicalInvolution.Upgrade.glCongr_statedSL φ 3)
        (CFSG.Adapters.RankTwoModelTransports.glCongr_statedScalars φ) rfl)⟩

theorem mk_scalar (s : Kˣ) :
    ProjGenLinGroup.mk (GeneralLinearGroup.scalar (Fin 3) s : GL (Fin 3) K) = 1 := by
  rw [ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.center_eq_range_scalar]
  exact ⟨s, rfl⟩

theorem exists_elemAbelian_nine_projImage_slPi (hK : PiField π p f K) (hq : ModThree π (p ^ f)) :
    ∃ D : Subgroup (projImage (slPi π 3 (p ^ f) K)), CFSG.Assembly.IsElemAbelian 3 D ∧
      Nat.card D = 9 := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hq' : π = false → ModThree false (p ^ f) := fun h => by subst h; exact hq
  have := hK.finite
  obtain ⟨τ, hτ, hτ1⟩ := Sec4.exists_tau hK hq
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    simp at hτ
  set d := Sec4.diagTau hτ with hd_def
  set y := (Sec4.cycThree : GL (Fin 3) K) with hy_def
  have hd : d ∈ slPi π 3 (p ^ f) K := Sec4.diagTau_mem_slPi hπ hq' hτ
  have hy : y ∈ slPi π 3 (p ^ f) K := Sec4.cycThree_mem_slPi hπ
  set u : projImage (slPi π 3 (p ^ f) K) := ⟨ProjGenLinGroup.mk d, Subgroup.mem_map_of_mem _ hd⟩
  set v : projImage (slPi π 3 (p ^ f) K) := ⟨ProjGenLinGroup.mk y, Subgroup.mem_map_of_mem _ hy⟩
  have h4 : τ ^ 2 * τ ^ 2 = τ := by
    calc τ ^ 2 * τ ^ 2 = τ ^ 3 * τ := by ring
      _ = τ := by rw [hτ, one_mul]
  have h5 : τ ^ 2 * τ = 1 := by
    calc τ ^ 2 * τ = τ ^ 3 := by ring
      _ = 1 := hτ
  have hyd : y * d = GeneralLinearGroup.scalar (Fin 3) (Units.mk0 τ hτ0 ^ 2) * (d * y) := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, Units.val_mul, Sec4.coe_scalar_eq_smul, hy_def,
      Sec4.coe_cycThree, hd_def, Sec4.coe_diagTau]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, h4, h5]
  have huv : u * v = v * u := by
    apply Subtype.ext
    change ProjGenLinGroup.mk d * ProjGenLinGroup.mk y =
      ProjGenLinGroup.mk y * ProjGenLinGroup.mk d
    calc ProjGenLinGroup.mk d * ProjGenLinGroup.mk y = ProjGenLinGroup.mk (d * y) :=
          (map_mul _ _ _).symm
      _ = ProjGenLinGroup.mk (GeneralLinearGroup.scalar (Fin 3) (Units.mk0 τ hτ0 ^ 2) *
            (d * y)) := by rw [map_mul ProjGenLinGroup.mk (GeneralLinearGroup.scalar _ _),
              mk_scalar, one_mul]
      _ = ProjGenLinGroup.mk (y * d) := by rw [hyd]
      _ = ProjGenLinGroup.mk y * ProjGenLinGroup.mk d := map_mul _ _ _
  have hd3 : d ^ 3 = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, hd_def, Sec4.coe_diagTau_eq_diagonal hτ, diagonal_pow,
      Units.val_one, ← diagonal_one]
    congr 1
    funext i
    have h6 : (τ ^ 2) ^ 3 = 1 := by rw [← pow_mul, pow_mul', hτ, one_pow]
    fin_cases i <;> simp [hτ, h6]
  have hu3 : u ^ 3 = 1 := by
    apply Subtype.ext
    change ProjGenLinGroup.mk d ^ 3 = 1
    rw [← map_pow, hd3, map_one]
  have hv3 : v ^ 3 = 1 := by
    apply Subtype.ext
    change ProjGenLinGroup.mk y ^ 3 = 1
    have hc3 : (Sec4.cycThree : GL (Fin 3) K) ^ 3 = 1 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, Sec4.coe_cycThree, Units.val_one]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_three]
    rw [← map_pow, hy_def, hc3, map_one]
  have hu1 : u ≠ 1 := by
    intro h1
    have h2 : ProjGenLinGroup.mk d = 1 := congrArg Subtype.val h1
    rw [ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.center_eq_range_scalar] at h2
    obtain ⟨t, ht⟩ := h2
    have e0 := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 0 0) ht
    have e2 := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 2 2) ht
    simp only [Sec4.coe_scalar_eq_smul, hd_def, Sec4.coe_diagTau] at e0 e2
    simp at e0 e2
    rw [e2] at e0
    simp at e0
    exact hτ1 e0.symm
  have hvu : v ∉ Subgroup.zpowers u := by
    intro hmem
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have h1 : ProjGenLinGroup.mk (d ^ i) = ProjGenLinGroup.mk y := by
      rw [map_zpow]
      exact congrArg Subtype.val hi
    have h2 : ProjGenLinGroup.mk (y * (d ^ i)⁻¹) = 1 := by
      rw [map_mul, map_inv, ← h1, mul_inv_cancel]
    rw [ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.center_eq_range_scalar] at h2
    obtain ⟨t, ht⟩ := h2
    have hdiag : d = Sec4.diagHom (Units.mk0 τ hτ0, Units.mk0 τ hτ0 ^ 2, 1) := by
      rw [hd_def, Sec4.diagTau_eq_diagUnits hτ hτ0]
      rfl
    have e11 := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 1 1) ht
    rw [hdiag, ← map_zpow, ← map_inv, Units.val_mul, Sec4.coe_diagHom, Sec4.coe_scalar_eq_smul,
      hy_def, Sec4.coe_cycThree] at e11
    simp [Matrix.mul_apply, Matrix.diagonal] at e11
  have : Finite (ProjGenLinGroup (Fin 3) K) :=
    Finite.of_surjective (ProjGenLinGroup.mk : GL (Fin 3) K →* _) (QuotientGroup.mk'_surjective _)
  refine ⟨Subgroup.zpowers u ⊔ Subgroup.zpowers v, isElemAbelian_zpowers_sup hu3 hv3 huv, ?_⟩
  exact Sec4.card_zpowers_sup_zpowers hv3 (orderOf_eq_prime hu3 hu1) hvu huv.symm

end PGL


section Data

open CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

variable {G : Type} [Group G] [Finite G] {A L : Subgroup G} {c : G}

theorem isLThreePi_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (hY : IsLThreePi Y) : IsLThreePi X := by
  obtain ⟨p, f, hp, hf, h⟩ := hY
  refine ⟨p, f, hp, hf, ?_⟩
  rcases h with ⟨hq, ⟨φ⟩⟩ | ⟨hq, ⟨φ⟩⟩
  · exact Or.inl ⟨hq, ⟨e.trans φ⟩⟩
  · exact Or.inr ⟨hq, ⟨e.trans φ⟩⟩

theorem isElemAbelian_map {M M' : Type*} [Group M] [Group M'] {p : ℕ} {E : Subgroup M}
    (hE : CFSG.Assembly.IsElemAbelian p E) (φ : M →* M') :
    CFSG.Assembly.IsElemAbelian p (E.map φ) := CFSG.SectionRank.isElemAbelian_map hE _

theorem exists_projImage_slPi_equiv (h : Sec13Data G A c L)
    (hPGL : Sec8.IsZ3PGLThreePi (lBarA c L A)) :
    ∃ (π : Bool) (p f : ℕ) (K : Type) (_ : Field K), PiField π p f K ∧ ModThree π (p ^ f) ∧
      2 < p ^ f ∧ Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* projImage (slPi π 3 (p ^ f) K)) := by
  obtain ⟨π, p, f, K, _, hK, hq, ⟨φ⟩⟩ := hPGL
  have hq2 : 2 < p ^ f := by
    by_contra hle
    have h2 : p ^ f = 2 := by
      have hf : f ≠ 0 := by have := hK.one_le; omega
      have : 2 ≤ p ^ f := le_trans hK.prime.two_le (Nat.le_self_pow hf _)
      omega
    cases π
    · exact false_of_isSolvable h (isSolvable_projImage_glPi_two hK h2) φ
    · change p ^ f % 3 = 1 at hq
      omega
  refine ⟨π, p, f, K, inferInstance, hK, hq, hq2, ?_⟩
  obtain ⟨η, -⟩ := exists_lBarEquiv h.mem_thetaComponentsAt
  obtain ⟨e⟩ := nonempty_lBar_equiv h φ
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hSP : projImage (slPi π 3 (p ^ f) K) ≤ projImage (glPi π 3 (p ^ f) K) :=
    Subgroup.map_mono (Sec4.slPi_le_glPi hπ)
  exact ⟨η.trans (e.trans ((MulEquiv.subgroupCongr (commutator_projImage_glPi hK hq2)).trans
    (Subgroup.subgroupOfEquivOfLe hSP)))⟩

theorem facts_of_isZ3PGLThreePi (h : Sec13Data G A c L)
    (hPGL : Sec8.IsZ3PGLThreePi (lBarA c L A)) :
    IsLThreePi (L ⧸ aschbacherSolvableCore 3 L) ∧
      Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) = ⊥ ∧
      ∃ D : Subgroup G, D ≤ L ∧ CFSG.Assembly.IsElemAbelian 3 D ∧ Nat.card D = 9 := by
  obtain ⟨π, p, f, K, _, hK, hq, hq2, ⟨ψ⟩⟩ := exists_projImage_slPi_equiv h hPGL
  refine ⟨isLThreePi_of_mulEquiv ψ (isLThreePi_projImage_slPi hK hq), ?_, ?_⟩
  · rw [eq_bot_iff]
    intro x hx
    have h1 : ψ x ∈ Subgroup.center (projImage (slPi π 3 (p ^ f) K)) := by
      rw [Subgroup.mem_center_iff] at hx ⊢
      intro m
      obtain ⟨y, rfl⟩ := ψ.surjective m
      rw [← map_mul, ← map_mul, hx y]
    rw [center_projImage_slPi hK hq hq2, Subgroup.mem_bot] at h1
    rw [Subgroup.mem_bot]
    exact ψ.injective (h1.trans ψ.map_one.symm)
  · obtain ⟨D, hD, hD9⟩ := exists_elemAbelian_nine_projImage_slPi hK hq
    have hDb := isElemAbelian_map hD ψ.symm.toMonoidHom
    have hDb9 : Nat.card (D.map ψ.symm.toMonoidHom) = 9 := by
      rw [Subgroup.card_map_of_injective ψ.symm.injective, hD9]
    obtain ⟨S, -, hS, hS9, -⟩ := exists_elemAbelian_map_eq (H := L) (M := ⊤) hDb
      (by rw [Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]; exact le_top)
    refine ⟨S.map L.subtype, ?_, isElemAbelian_map hS _, ?_⟩
    · rintro _ ⟨s, -, rfl⟩
      exact s.2
    · rw [Subgroup.card_map_of_injective L.subtype_injective, hS9, hDb9]

end Data

end CFSG.RankThree.PartTwo.Sec13
