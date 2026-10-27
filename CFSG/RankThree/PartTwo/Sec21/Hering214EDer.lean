module

public import CFSG.RankThree.PartTwo.Sec21.Item211Res2ProofSmall

public section

namespace CFSG.RankThree.PartTwo.Sec21.Hering214Even

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)
open Item211Res2Proof
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem barAct_eq_conj_of_mem {L : Subgroup G} {y : G} (hy : y ∈ L)
    (hyN : y ∈ Subgroup.normalizer (L : Set G)) :
    barAct L ⟨y, hyN⟩ = MulAut.conj ((⟨y, hy⟩ : L) : L ⧸ aschbacherSolvableCore 3 L) := by
  ext q
  induction q using QuotientGroup.induction_on with
  | H w => rfl

theorem derived_centralizer_le_barImage {L U : Subgroup G}
    (hθc : aschbacherSolvableCore 3 L ≤ Subgroup.center L)
    (hZ : Subgroup.center (lBar L) = ⊥) (hU : U ≤ Subgroup.normalizer (L : Set G)) :
    ⁅(MulAut.conj : lBar L →* MulAut (lBar L)).range ⊓
        Subgroup.centralizer (barImage L U : Set (MulAut (lBar L))),
      (MulAut.conj : lBar L →* MulAut (lBar L)).range ⊓
        Subgroup.centralizer (barImage L U : Set (MulAut (lBar L)))⁆ ≤
      barImage L (L ⊓ Subgroup.centralizer (U : Set G)) := by
  have cen_left : ∀ x g a : L, (∀ h : L, h * a = a * h) → ⁅x * a, g⁆ = ⁅x, g⁆ := by
    intro x g a ha
    rw [commutatorElement_def, commutatorElement_def, mul_inv_rev]
    calc x * a * g * (a⁻¹ * x⁻¹) * g⁻¹ = x * (a * g) * a⁻¹ * x⁻¹ * g⁻¹ := by group
      _ = x * (g * a) * a⁻¹ * x⁻¹ * g⁻¹ := by rw [ha g]
      _ = x * g * x⁻¹ * g⁻¹ := by group
  have cen_right : ∀ x g b : L, (∀ h : L, h * b = b * h) → ⁅x, g * b⁆ = ⁅x, g⁆ := by
    intro x g b hb
    rw [commutatorElement_def, commutatorElement_def, mul_inv_rev]
    calc x * (g * b) * x⁻¹ * (b⁻¹ * g⁻¹) = x * g * (b * x⁻¹) * b⁻¹ * g⁻¹ := by group
      _ = x * g * (x⁻¹ * b) * b⁻¹ * g⁻¹ := by rw [hb x⁻¹]
      _ = x * g * x⁻¹ * g⁻¹ := by group
  have hgen : ∀ (σ : MulAut (lBar L)) (y : lBar L),
      MulAut.conj (σ y) = σ * MulAut.conj y * σ⁻¹ := by
    intro σ y
    ext z
    simp [MulAut.mul_apply, map_mul, map_inv, MulAut.conj_apply]
  have hcen_of : ∀ x s : lBar L, (∀ g : lBar L, s * g * s⁻¹ = x * g * x⁻¹) →
      x⁻¹ * s ∈ Subgroup.center (lBar L) := by
    intro x s hs
    rw [Subgroup.mem_center_iff]
    intro g
    have hg : x⁻¹ * s * g * (x⁻¹ * s)⁻¹ = g := by
      calc x⁻¹ * s * g * (x⁻¹ * s)⁻¹ = x⁻¹ * (s * g * s⁻¹) * x := by group
        _ = x⁻¹ * (x * g * x⁻¹) * x := by rw [hs g]
        _ = g := by group
    exact (mul_inv_eq_iff_eq_mul.mp hg).symm
  have hfix : ∀ {l : L}, MulAut.conj (l : lBar L) ∈
      Subgroup.centralizer (barImage L U : Set (MulAut (lBar L))) →
      ∀ u, u ∈ U → ∀ hu : u ∈ Subgroup.normalizer (L : Set G),
        barAct L ⟨u, hu⟩ (l : lBar L) = (l : lBar L) := by
    intro l hc u huU hu
    have hσ : barAct L ⟨u, hu⟩ ∈ barImage L U := mem_barImage_iff.mpr ⟨u, hu, huU, rfl⟩
    have hc' := Subgroup.mem_centralizer_iff.mp hc (barAct L ⟨u, hu⟩) hσ
    have hconj : MulAut.conj (barAct L ⟨u, hu⟩ (l : lBar L)) = MulAut.conj (l : lBar L) := by
      rw [hgen, hc', mul_inv_cancel_right]
    have hcen := hcen_of (l : lBar L) (barAct L ⟨u, hu⟩ (l : lBar L))
      (fun g => DFunLike.congr_fun hconj g)
    rw [hZ, Subgroup.mem_bot, inv_mul_eq_one] at hcen
    exact hcen.symm
  have hcU : ∀ {l m : L},
      (∀ u, u ∈ U → ∀ hu : u ∈ Subgroup.normalizer (L : Set G),
        barAct L ⟨u, hu⟩ (l : lBar L) = (l : lBar L)) →
      (∀ u, u ∈ U → ∀ hu : u ∈ Subgroup.normalizer (L : Set G),
        barAct L ⟨u, hu⟩ (m : lBar L) = (m : lBar L)) →
      ∀ u, u ∈ U → u * ((⁅l, m⁆ : L) : G) = ((⁅l, m⁆ : L) : G) * u := by
    intro l m hl hm u huU
    have hu : u ∈ Subgroup.normalizer (L : Set G) := hU huU
    set φ : MulAut L := L.normalizerMonoidHom ⟨u, hu⟩ with hφdef
    have hφG : ∀ x : L, ((φ x : L) : G) = u * x * u⁻¹ := fun x => rfl
    have hpart : ∀ n : L, barAct L ⟨u, hu⟩ (n : lBar L) = (n : lBar L) →
        ∀ g : L, g * (n⁻¹ * φ n) = (n⁻¹ * φ n) * g := by
      intro n hn
      have h1 : ((φ n : L) : lBar L) = (n : lBar L) :=
        (Sec4.thetaQuotMulAut_mk φ n).symm.trans hn
      exact fun g => Subgroup.mem_center_iff.mp (hθc (QuotientGroup.eq.mp h1.symm)) g
    have ha := hpart l (hl u huU hu)
    have hb := hpart m (hm u huU hu)
    have hφcomm : φ ⁅l, m⁆ = ⁅l, m⁆ := by
      calc φ ⁅l, m⁆ = ⁅φ l, φ m⁆ := map_commutatorElement φ l m
        _ = ⁅l * (l⁻¹ * φ l), m * (m⁻¹ * φ m)⁆ := by
          rw [mul_inv_cancel_left, mul_inv_cancel_left]
        _ = ⁅l, m⁆ := by rw [cen_left _ _ _ ha, cen_right _ _ _ hb]
    have hG : u * ((⁅l, m⁆ : L) : G) * u⁻¹ = ((⁅l, m⁆ : L) : G) := by
      have h := congrArg Subtype.val hφcomm
      rwa [hφG] at h
    exact mul_inv_eq_iff_eq_mul.mp hG
  refine Subgroup.commutator_le.mpr ?_
  rintro x ⟨hxR, hxC⟩ y ⟨hyR, hyC⟩
  obtain ⟨p, rfl⟩ := MonoidHom.mem_range.mp hxR
  obtain ⟨q, rfl⟩ := MonoidHom.mem_range.mp hyR
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective p
  obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective q
  have hcq : ((⁅l, m⁆ : L) : lBar L) = ⁅(l : lBar L), (m : lBar L)⁆ :=
    map_commutatorElement (QuotientGroup.mk' (aschbacherSolvableCore 3 L)) l m
  have hcomm_eq : ⁅MulAut.conj (l : lBar L), MulAut.conj (m : lBar L)⁆ =
      MulAut.conj ((⁅l, m⁆ : L) : lBar L) := by
    rw [← map_commutatorElement MulAut.conj, ← hcq]
  have hmem : ((⁅l, m⁆ : L) : G) ∈ L ⊓ Subgroup.centralizer (U : Set G) :=
    Subgroup.mem_inf.mpr ⟨(⁅l, m⁆ : L).2, Subgroup.mem_centralizer_iff.mpr fun u huU =>
      hcU (hfix hxC) (hfix hyC) u huU⟩
  rw [hcomm_eq]
  exact mem_barImage_iff.mpr ⟨((⁅l, m⁆ : L) : G), Subgroup.le_normalizer (⁅l, m⁆ : L).2, hmem,
    barAct_eq_conj_of_mem (⁅l, m⁆ : L).2 (Subgroup.le_normalizer (⁅l, m⁆ : L).2)⟩

end CFSG.RankThree.PartTwo.Sec21.Hering214Even
