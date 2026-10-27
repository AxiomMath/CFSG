module

public import CFSG.Quasithin.Vol2.Ch11SecS12ZE
public import CFSG.LocalAnalysis.SectionRank.Ccomm.Supercritical
public import CFSG.LocalAnalysis.SectionRank.Ccomm.ElementaryAut
public import CFSG.RankThree.PartOne.S10.PlaneCoreBounds

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS.S12

open CFSG.SectionRank.Ccomm
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem hom_eq_one_of_le_one {A : Type*} [Group A] (hA : commutator A = ⊤) {p n : ℕ}
    [Fact p.Prime] (hn : n ≤ 1) (ρ : A →* GL (Fin n) (ZMod p)) : ρ = 1 := by
  ext a : 1
  have h1 := Abelianization.commutator_subset_ker ((Matrix.GeneralLinearGroup.det).comp ρ)
    (hA ▸ Subgroup.mem_top a : a ∈ commutator A)
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at h1
  have hd : ((ρ a : GL (Fin n) (ZMod p)) : Matrix (Fin n) (Fin n) (ZMod p)).det = 1 := by
    have := congrArg Units.val h1
    simpa [Matrix.GeneralLinearGroup.val_det_apply] using this
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hn with rfl | rfl
  · exact Subsingleton.elim _ _
  · refine Units.ext ?_
    ext i j
    fin_cases i
    fin_cases j
    simpa [Matrix.det_fin_one] using hd

theorem le_pRank_of_elementary {p : ℕ} {P : Subgroup G} {D : Subgroup ↥P} (E : Subgroup ↥D)
    [hE : CFSG.IsElementaryAbelian p ↥E] {k : ℕ} (hk : Nat.card ↥E = p ^ k) (hp : 1 < p) :
    k ≤ CFSG.Open.pRank p P := by
  set E' : Subgroup G := (E.map D.subtype).map P.subtype with hE'
  have hinj : Function.Injective (P.subtype.comp D.subtype) :=
    P.subtype_injective.comp D.subtype_injective
  have hcard : Nat.card ↥E' = p ^ k := by
    rw [hE', Subgroup.map_map, Subgroup.card_map_of_injective hinj, hk]
  have hE'el : CFSG.Open.IsElemAbelian p E' := by
    refine ⟨⟨⟨?_⟩⟩, ?_⟩
    · rintro ⟨_, _, ⟨x, hx, rfl⟩, rfl⟩ ⟨_, _, ⟨y, hy, rfl⟩, rfl⟩
      have := hE.toIsMulCommutative.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩
      exact Subtype.ext (by simpa using congrArg (fun z : ↥E => ((z : ↥D) : ↥P).1) this)
    · rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      have h1 : (⟨x, hx⟩ : ↥E) ^ p = 1 :=
        Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
          (CFSG.IsElementaryAbelian.exponent_dvd_p p ↥E) _
      simpa using congrArg (fun z : ↥E => ((z : ↥D) : ↥P).1) h1
  refine le_csSup ⟨Nat.card G, fun j hj => ?_⟩ ⟨E', ?_, hE'el, hcard⟩
  · obtain ⟨E'', -, -, hE''⟩ := hj
    have h1 : j < p ^ j := Nat.lt_pow_self hp
    have h2 : Nat.card E'' ≤ Nat.card G := Subgroup.card_le_card_group E''
    omega
  · rintro _ ⟨y, -, rfl⟩
    exact y.2

theorem le_centralizer_of_pRank_le_two {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    {P A : Subgroup G} (hP : IsPGroup p ↥P) (hrank : CFSG.Open.pRank p P ≤ 2)
    (hAP : A ≤ Subgroup.normalizer (P : Set G)) (hA : commutator ↥A = ⊤)
    (hρ : ∀ ρ : ↥A →* GL (Fin 2) (ZMod p), ρ = 1) :
    A ≤ Subgroup.centralizer (P : Set G) := by
  set φ : ↥A →* MulAut ↥P := P.normalizerMonoidHom.comp (Subgroup.inclusion hAP) with hφ
  suffices hφ1 : φ = 1 by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have h1 := congrArg (fun σ : MulAut ↥P => ((σ ⟨x, hx⟩ : ↥P) : G))
      (DFunLike.congr_fun hφ1 ⟨a, ha⟩)
    have h2 : a * x * a⁻¹ = x := h1
    exact (mul_inv_eq_iff_eq_mul.mp h2).symm
  rcases subsingleton_or_nontrivial ↥P with hs | hnt
  · ext a x
    exact congrArg Subtype.val (Subsingleton.elim _ _)
  obtain ⟨D, hDc, hD1, hDexp, hDZ, -, hker⟩ := supercritical_witness hp2 hP
  have hDp : IsPGroup p ↥D := hP.to_subgroup D
  have hcardD : Nat.card (↥D ⧸ frattini ↥D) ≤ p ^ 2 := by
    refine CFSG.RankThree.PartOne.PlaneCore.card_frattini_quotient_le hp.out hDp
      (fun x => Subtype.ext (hDexp x x.2)) ?_ ?_
    · rw [commutator_def, Subgroup.commutator_le]
      intro g₁ _ g₂ _
      rw [Subgroup.mem_center_iff]
      intro z
      have hmem : ((⁅g₁, g₂⁆ : ↥D) : ↥P) ∈ ⁅D, (⊤ : Subgroup ↥P)⁆ :=
        Subgroup.commutator_mem_commutator g₁.2 (Subgroup.mem_top _)
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hDZ hmem).2 z z.2)
    · intro E hE k hk
      have := le_pRank_of_elementary E hk hp.out.one_lt
      omega
  obtain ⟨-, hWcomm, hWpow⟩ := frattini_quotient_elementary hDp
  have hWp : IsPGroup p (↥D ⧸ frattini ↥D) := fun x => ⟨1, by rw [pow_one, hWpow]⟩
  obtain ⟨n, hn⟩ := hWp.exists_card_eq
  obtain ⟨e⟩ := nonempty_mulEquiv_of_elementary hWcomm hWpow hn
  have hn2 : n ≤ 2 := by
    rw [hn] at hcardD
    exact (Nat.pow_le_pow_iff_right hp.out.one_lt).mp hcardD
  have hρ0 : ∀ a : ↥A, frattiniAction D (φ a) = 1 := by
    have key : (elemAutEquivGL e).toMonoidHom.comp ((frattiniAction D).comp φ) = 1 := by
      rcases Nat.lt_or_ge n 2 with hlt | hge
      · exact hom_eq_one_of_le_one hA (by omega) _
      · obtain rfl : n = 2 := le_antisymm hn2 hge
        exact hρ _
    intro a
    have h1 := DFunLike.congr_fun key a
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MonoidHom.one_apply] at h1
    exact (elemAutEquivGL e).injective (h1.trans (map_one _).symm)
  refine eq_one_of_isPGroup_range hA φ (p := p) ?_
  exact hker.to_le (by rintro _ ⟨a, rfl⟩; exact hρ0 a)

end CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS.S12
