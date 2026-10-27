module

public import CFSG.RankThree.PartOne.S12.Sec159Defs
public import CFSG.RankThree.PartOne.S12.Sec159Node
public import CFSG.RankThree.PartOne.S12.Sec1511Y2Quot
public import CFSG.RankThree.PartOne.K159.CenterRank
public import CFSG.RankThree.PartOne.N143.SectionCenter
import CFSG.RankThree.PartOne.S10.EmbeddingFixedResidual
public import CFSG.RankThree.PartOne.CTP.StrongPSylow
public import CFSG.RankThree.PartOne.S12.Sec12A

public section

namespace CFSG.RankThree.PartOne.K159

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory CFSG.RankThree.PartOne StrongP

section Omega

variable {H : Type*} [Group H]

theorem omegaOne_map_of_injective' {K : Type*} [Group K] {f : K →* H} (hf : Function.Injective f)
    (p : ℕ) (T : Subgroup K) : omegaOne p (T.map f) = (omegaOne p T).map f := by
  unfold omegaOne
  rw [MonoidHom.map_closure]
  congr 1
  ext y
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, hy⟩
    exact ⟨x, ⟨hx, hf (by rw [map_pow, hy, map_one])⟩, rfl⟩
  · rintro ⟨x, ⟨hx, hxp⟩, rfl⟩
    exact ⟨⟨x, hx, rfl⟩, by rw [← map_pow, hxp, map_one]⟩

theorem omegaOne_le' (p : ℕ) (T : Subgroup H) : omegaOne p T ≤ T :=
  (Subgroup.closure_le _).2 fun _ hx => hx.1

theorem omegaOne_subgroupOf' (p : ℕ) {T Y : Subgroup H} (hT : T ≤ Y) :
    omegaOne p (T.subgroupOf Y) = (omegaOne p T).subgroupOf Y := by
  apply Subgroup.map_injective Y.subtype_injective
  rw [← omegaOne_map_of_injective' Y.subtype_injective, Subgroup.map_subgroupOf_eq_of_le hT,
    Subgroup.map_subgroupOf_eq_of_le ((omegaOne_le' p T).trans hT)]

variable [Finite H] {p : ℕ} [Fact p.Prime]

theorem card_omegaOne_le_card_omegaOne {P Q : Subgroup H} (hP : IsSylowOf p P ⊤)
    (hQ : IsPGroup p Q) : Nat.card (omegaOne p Q) ≤ Nat.card (omegaOne p P) := by
  obtain ⟨g, hg⟩ := exists_conj_le_sylow hP hQ
  have hle : conjSub g (omegaOne p Q) ≤ omegaOne p P := by
    rw [conjSub, Subgroup.map_le_iff_le_comap]
    refine (Subgroup.closure_le _).2 ?_
    rintro y ⟨hyQ, hy⟩
    exact conj_mem_omegaOne hg hyQ hy
  calc Nat.card (omegaOne p Q) = Nat.card (conjSub g (omegaOne p Q)) := card_conjSub.symm
    _ ≤ Nat.card (omegaOne p P) := Subgroup.card_le_of_le hle

end Omega

section Lift

variable {M : Type} [Group M] [Finite M] {p : ℕ} [Fact p.Prime] {O : Subgroup M} [O.Normal]

theorem card_le_card_omegaOne_of_quotient (hO : ¬ p ∣ Nat.card O) {P₀ : Subgroup M}
    (hP₀ : IsSylowOf p P₀ ⊤) {R : Subgroup (M ⧸ O)} (hR : ∀ b ∈ R, b ^ p = 1) :
    Nat.card R ≤ Nat.card (omegaOne p P₀) := by
  have hPbar := Sec1511.isSylowOf_map_mk' (O := O) hP₀
  have hRp : IsPGroup p R := fun g => ⟨1, Subtype.ext (by simpa using hR g g.2)⟩
  have h1 := card_le_card_omegaOne hPbar hRp hR
  rw [Sec1511.omegaOne_map_mk' hP₀.2.1 hO,
    Sec1511.card_map_mk' ((hP₀.2.1).to_le (omegaOne_le' p P₀)) hO] at h1
  exact h1

end Lift

section Contradiction

variable {G : Type} [Group G] [Finite G] {p : ℕ}

theorem false_of_rank_four (hp : p.Prime) {X M₀ P : Subgroup G} (hXM : X ≤ M₀)
    (hP : IsSylowOf p P M₀) (hΩ : Nat.card (omegaOne p P) = p ^ 3) {O : Subgroup ↥X} [O.Normal]
    (hO : ¬ p ∣ Nat.card O) {R : Subgroup (↥X ⧸ O)} (hR : ∀ b ∈ R, b ^ p = 1)
    (hRcard : p ^ 4 ≤ Nat.card R) : False := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨P₀, hP₀⟩ : ∃ P₀ : Subgroup ↥X, IsSylowOf p P₀ ⊤ := by
    obtain ⟨P₀, hP₀⟩ := CFSG.ABGLocalTools.exists_isSylowOf p (⊤ : Subgroup ↥X)
    exact ⟨P₀, CFSG.ABGLocalTools.isSylowOf_iff.1 hP₀⟩
  have h1 : p ^ 4 ≤ Nat.card (omegaOne p P₀) :=
    hRcard.trans (card_le_card_omegaOne_of_quotient hO hP₀ hR)
  let ι : ↥X →* ↥M₀ := Subgroup.inclusion hXM
  have hι : Function.Injective ι := Subgroup.inclusion_injective hXM
  set P₁ : Subgroup ↥M₀ := P₀.map ι with hP₁
  have hP₁p : IsPGroup p P₁ := hP₀.2.1.map ι
  have hΩ₁ : Nat.card (omegaOne p P₁) = Nat.card (omegaOne p P₀) := by
    rw [hP₁, omegaOne_map_of_injective' hι, Subgroup.card_map_of_injective hι]
  have hP' : IsSylowOf p (P.subgroupOf M₀) ⊤ :=
    ⟨le_top, hP.2.1.comap_subtype, by
      rw [Subgroup.relIndex_top_right]
      exact hP.2.2⟩
  have h2 := card_omegaOne_le_card_omegaOne hP' hP₁p
  rw [omegaOne_subgroupOf' p hP.1, hΩ₁] at h2
  have h3 : Nat.card ((omegaOne p P).subgroupOf M₀) = Nat.card (omegaOne p P) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe ((omegaOne_le' p P).trans hP.1)).toEquiv
  rw [h3, hΩ] at h2
  have h4 := h1.trans h2
  have h5 : p ^ 3 < p ^ 4 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
  omega

end Contradiction

section Main

theorem kf159Z_of_rank (h155 : Node155) (hrank : CenterRankFour) : KF159Z := by
  classical
  intro G _ _ p A c L E h15 hF hout hEA X hX0 _ hpZ
  have h := h15.h12
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have hp5 : 5 ≤ p := by
    have h3 := h.three_lt
    by_contra hlt
    have h4 : p = 4 := by omega
    exact absurd (h4 ▸ hp) (by norm_num)
  have hEcard : Nat.card ↥E = p ^ 3 := hEA ▸ h.A_card
  have hnonab : ∃ a b : G, a * b ≠ b * a := h.setup.2.1
  have hKP : IsKProper G := h.setup.2.2.1
  have hsimple : IsSimpleGroup G := h.setup.1
  have hrk3 : CFSG.twoLocalOddRank G ≤ 3 := h.setup.2.2.2.2.1.le
  have hx0 : ∃ x ∈ E, x ≠ 1 ∧ X ∈ thetaComponentsAt p x := by
    obtain ⟨B, hB, hXB⟩ := hX0
    obtain ⟨hBE, -, hBcard, -⟩ := hB
    have hBeq : B = E := Subgroup.eq_of_le_of_card_ge hBE (by rw [hEcard, hBcard])
    rw [hBeq] at hXB
    obtain ⟨x, hxE, hx1, hXx⟩ := mem_thetaComponentFamily_iff.1 hXB
    exact ⟨x, hxE, hx1, hXx⟩
  obtain ⟨x, hxE, hx1, hXx⟩ := hx0
  have hXC : X ≤ Subgroup.centralizer ({x} : Set G) := (mem_thetaComponentsAt_iff.1 hXx).1
  have hXtop : X ≠ ⊤ := by
    intro htop
    exact EmbeddingFixedResidual.centralizer_ne_top_of_simple hnonab hx1
      (eq_top_iff.2 (htop ▸ hXC))
  have hKX : CFSG.IsKGroup ↥X := hKP X hXtop
  have hQq : CFSG.IsQuasisimple (↥X ⧸ aschbacherSolvableCore p ↥X) :=
    isQuasisimple_thetaQuotient_of_mem_thetaComponentsAt hp hXx
  have hZ2 : ¬ 2 ∣ Nat.card (Subgroup.center (↥X ⧸ aschbacherSolvableCore p ↥X)) :=
    N143.not_dvd_card_center_theta_quotient (L := ↥X) hp Nat.prime_two (by omega)
  have hrkX : CFSG.twoLocalOddRank ↥X ≤ 3 := by
    have h1 := Sec9A.evenRank_subgroup_le X
    rw [CFSG.RankThree.OddKernel.evenRank_eq_twoLocalOddRank,
      CFSG.RankThree.OddKernel.evenRank_eq_twoLocalOddRank] at h1
    exact h1.trans hrk3
  obtain ⟨R, hRexp, -, hRcard⟩ := hrank ↥X hrkX hKX (aschbacherSolvableCore p ↥X) hQq p hp
    (by omega) hpZ (Nat.odd_iff.2 (by omega))
  obtain ⟨P, hPsyl, -, -, hPΩ⟩ := Sec159Node.exists_sylow hp h155 (X := X) h15 hF hout hEA
  exact false_of_rank_four hp (X := X) (M₀ := X ⊔ E) le_sup_left hPsyl (by rw [hPΩ]; exact hEcard)
    (O := aschbacherSolvableCore p ↥X) ((solvable_prime_complement_core_characterization hp).2.2.1)
    hRexp hRcard

end Main

end CFSG.RankThree.PartOne.K159
