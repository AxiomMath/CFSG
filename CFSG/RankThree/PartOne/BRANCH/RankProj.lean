module

public import CFSG.RankThree.PartOne.BRANCH.RankDet
public import CFSG.RankThree.PartOne.BRANCH.RankTrace
public import CFSG.RankThree.PartOne.S11c.CentralLift
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian

public section

namespace CFSG.RankThree.PartOne.BRANCH

open Subgroup CFSG CFSG.Assembly.LowTwoRank CFSG.RankThree.PartOne

theorem card_le_of_projective_cover {n q m : ℕ} {K : Type} [Field K] (hq : q.Prime)
    (hqK : (q : K) ≠ 0) (hnK : (n : K) ≠ 0) {P : Type} [Group P] [Finite P]
    (ρ : P →* GL (Fin n) K) (hρ : Function.Injective ρ)
    (hdet : ∀ g : P, ((ρ g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det = 1)
    (Z₀ : Subgroup P) (hZ₀ : ∀ z ∈ Z₀, ∃ c : Kˣ, ρ z = Matrix.GeneralLinearGroup.scalar (Fin n) c)
    (hcomm : ∀ g h : P, g * h * g⁻¹ * h⁻¹ ∈ Z₀) (hpow : ∀ x : P, x ^ q ∈ Z₀)
    (hcard : Nat.card P = q ^ m * Nat.card Z₀) : q ^ m ≤ n ^ 2 * q ^ (n - 1) := by
  classical
  have hcommρ : ∀ g h : P, ∃ c : Kˣ,
      ρ (g * h * g⁻¹ * h⁻¹) = Matrix.GeneralLinearGroup.scalar (Fin n) c :=
    fun g h => hZ₀ _ (hcomm g h)
  have hquot := card_quotient_center_le_sq ρ hρ hnK hcommρ
  set C : Subgroup P := Subgroup.center P with hC
  let _ : CommGroup C :=
    { (inferInstance : Group C) with
      mul_comm := fun a b => Subtype.ext (Subgroup.mem_center_iff.mp b.2 a) }
  let φ : C →* C := powMonoidHom q
  have hsq : Nat.card C = Nat.card φ.ker * Nat.card φ.range :=
    (Subgroup.card_ker_mul_card_range φ).symm
  have hrange : Nat.card φ.range ≤ Nat.card Z₀ := by
    have hle : φ.range.map C.subtype ≤ Z₀ := by
      rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
      exact hpow x
    calc Nat.card φ.range = Nat.card (φ.range.map C.subtype) :=
          (Subgroup.card_map_of_injective C.subtype_injective).symm
      _ ≤ Nat.card Z₀ := Nat.card_le_card_of_injective (Subgroup.inclusion hle)
          (Subgroup.inclusion_injective hle)
  set Y : Subgroup (GL (Fin n) K) := (φ.ker.map C.subtype).map ρ with hY
  have hYcard : Nat.card Y = Nat.card φ.ker := by
    rw [hY, Subgroup.card_map_of_injective hρ, Subgroup.card_map_of_injective C.subtype_injective]
  have hYmem : ∀ g ∈ Y, ∃ a : C, a ∈ φ.ker ∧ ρ (a : P) = g := by
    rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨a, ha, rfl⟩
  have : Finite Y :=
    (Set.Finite.subset (Set.finite_range ρ) (fun g hg => by
      obtain ⟨a, -, rfl⟩ := hYmem g hg
      exact ⟨(a : P), rfl⟩)).to_subtype
  have hYcomm : ∀ g ∈ Y, ∀ h ∈ Y, g * h = h * g := by
    intro g hg h hh
    obtain ⟨a, -, rfl⟩ := hYmem g hg
    obtain ⟨b, -, rfl⟩ := hYmem h hh
    rw [← map_mul, ← map_mul]
    congr 1
    exact (Subgroup.mem_center_iff.mp a.2 (b : P)).symm
  have hYexp : ∀ g ∈ Y, g ^ q = 1 := by
    intro g hg
    obtain ⟨a, ha, rfl⟩ := hYmem g hg
    rw [← map_pow]
    have h1 : (a : C) ^ q = 1 := ha
    have h2 : (a : P) ^ q = 1 := by
      have := congrArg (fun x : C => (x : P)) h1
      simpa using this
    rw [h2, map_one]
  have hYdet : ∀ g ∈ Y, (g : Matrix (Fin n) (Fin n) K).det = 1 := by
    intro g hg
    obtain ⟨a, -, rfl⟩ := hYmem g hg
    exact hdet a
  have hYbound : Nat.card Y ≤ q ^ (n - 1) := by
    have := card_le_pow_pred_of_det_gl hq hqK Y hYcomm hYexp hYdet
    simpa using this
  have hCcard : Nat.card C ≤ q ^ (n - 1) * Nat.card Z₀ := by
    rw [hsq]
    exact Nat.mul_le_mul (hYcard ▸ hYbound) hrange
  have hPcard : Nat.card P = Nat.card (P ⧸ C) * Nat.card C :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup C
  have hZpos : 0 < Nat.card Z₀ := Nat.card_pos
  have hchain : q ^ m * Nat.card Z₀ ≤ n ^ 2 * q ^ (n - 1) * Nat.card Z₀ := by
    calc q ^ m * Nat.card Z₀ = Nat.card P := hcard.symm
      _ = Nat.card (P ⧸ C) * Nat.card C := hPcard
      _ ≤ n ^ 2 * (q ^ (n - 1) * Nat.card Z₀) := Nat.mul_le_mul hquot hCcard
      _ = n ^ 2 * q ^ (n - 1) * Nat.card Z₀ := by ring
  exact Nat.le_of_mul_le_mul_right hchain hZpos

theorem card_le_of_statedProj {n q : ℕ} {K : Type} [Field K] [Finite K] (hq : q.Prime)
    (hqK : (q : K) ≠ 0) (hnK : (n : K) ≠ 0) (M : Subgroup (GL (Fin n) K))
    (hdet : ∀ g ∈ M, ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det = 1)
    {T : Type} [Group T] (e : T ≃* StatedProj M) {D : Subgroup T} (hD : IsElementaryAbelian q D) :
    Nat.card D ≤ n ^ 2 * q ^ (n - 1) := by
  classical
  have : Fact q.Prime := ⟨hq⟩
  have : Finite T := Finite.of_equiv (StatedProj M) e.symm.toEquiv
  let N : Subgroup M := (StatedScalars (Fin n) K).subgroupOf M
  let π : M →* T := e.symm.toMonoidHom.comp (QuotientGroup.mk' N)
  have hπ : Function.Surjective π := e.symm.surjective.comp (QuotientGroup.mk'_surjective N)
  have hπker : π.ker = N := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hDp : IsPGroup q D := by
    have := hD
    exact IsElementaryAbelian.isPGroup q D
  obtain ⟨P⟩ : Nonempty (Sylow q (D.comap π)) := inferInstance
  set P' : Subgroup M := (P : Subgroup (D.comap π)).map (D.comap π).subtype with hP'
  have hmap : P'.map π = D := map_sylow_comap π hπ hDp P
  have hP'fin : Finite P' := inferInstance
  let ρ : P' →* GL (Fin n) K := M.subtype.comp P'.subtype
  have hρ : Function.Injective ρ := M.subtype_injective.comp P'.subtype_injective
  let f : P' →* T := π.comp P'.subtype
  have hfrange : f.range = D := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype, hmap]
  have hfmem : ∀ x : P', f x ∈ D := fun x => by
    rw [← hfrange]
    exact ⟨x, rfl⟩
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hDp
  have hcard : Nat.card P' = q ^ m * Nat.card f.ker := by
    have h := Subgroup.card_ker_mul_card_range f
    rw [hfrange, hm] at h
    rw [← h, mul_comm]
  have hq1 : ∀ x : P', (f x) ^ q = 1 := fun x =>
    elemPow_eq_one_of_isElementaryAbelian (f x) (hfmem x)
  have := card_le_of_projective_cover (m := m) hq hqK hnK ρ hρ
    (fun g => hdet g.1 g.1.2) f.ker (fun z hz => ?_) (fun g h => ?_) (fun x => ?_) hcard
  · rw [hm]
    exact this
  ·
    have hzM : (z : M) ∈ π.ker := hz
    rw [hπker] at hzM
    obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.mp hzM
    exact ⟨c, hc.symm⟩
  ·
    rw [MonoidHom.mem_ker]
    have h1 : f g * f h = f h * f g := by
      have := hD.is_comm.comm (⟨f g, hfmem g⟩ : D) ⟨f h, hfmem h⟩
      exact congrArg Subtype.val this
    rw [map_mul, map_mul, map_mul, map_inv, map_inv]
    calc f g * f h * (f g)⁻¹ * (f h)⁻¹ = (f h * f g) * (f g)⁻¹ * (f h)⁻¹ := by rw [h1]
      _ = 1 := by group
  · rw [MonoidHom.mem_ker, map_pow]
    exact hq1 x

end CFSG.RankThree.PartOne.BRANCH
