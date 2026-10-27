module

public import CFSG.LocalAnalysis.WeakClosure81.SevenSixteenL2
public import CFSG.Milestones.ASVolI.I6
public import CFSG.Quasithin.Background.ONanE68RankOneSz
public import CFSG.SignalizerFunctorTheorem.McBride.Models.Suzuki.Local

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup CFSG.ASVolI.ChIJK

variable {G : Type} [Group G] [Finite G]

theorem s716F_isSolvable_dihedralGroup (z : ℕ) [NeZero z] :
    Group.IsSolvable (DihedralGroup z) := by
  classical
  let R : Subgroup (DihedralGroup z) := Subgroup.zpowers (DihedralGroup.r 1 : DihedralGroup z)
  have hRnormal : R.Normal := by
    refine ⟨fun x hx g => ?_⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rcases g with i | i
    · refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
      simp [DihedralGroup.r_mul_r]
    · refine Subgroup.mem_zpowers_iff.mpr ⟨-k, ?_⟩
      simp [DihedralGroup.sr_mul_r, DihedralGroup.sr_mul_sr, DihedralGroup.inv_sr]
  have : IsCyclic R := Subgroup.isCyclic_zpowers _
  let : CommGroup R := IsCyclic.commGroup
  have hRcard : Nat.card R = z := by rw [Nat.card_zpowers, DihedralGroup.orderOf_r_one]
  have hQcard : Nat.card (DihedralGroup z ⧸ R) = 2 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup R
    rw [DihedralGroup.nat_card, hRcard] at h
    have hz : 0 < z := Nat.pos_of_ne_zero (NeZero.ne z)
    exact (Nat.eq_of_mul_eq_mul_right hz h).symm
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsCyclic (DihedralGroup z ⧸ R) := isCyclic_of_prime_card hQcard
  let : CommGroup (DihedralGroup z ⧸ R) := IsCyclic.commGroup
  exact Group.isSolvable_of_ker_le_range R.subtype (QuotientGroup.mk' R)
    (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])

theorem exists_natural_l2_of_isNaturalSection {X Y P Q : Subgroup G}
    [(Y.subgroupOf X).Normal] {n : ℕ} (hn : 2 ≤ n)
    (hX : IsL2Gp (↥X ⧸ Y.subgroupOf X) n) (h : IsNaturalSection X Y P Q) :
    ∃ (k : ℕ) (e : ↥X ⧸ Y.subgroupOf X ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 k)),
      IsConjModuleIso X P Q (Fin 2 → GaloisField 2 k)
        (fun x v => ((e (x : ↥X ⧸ Y.subgroupOf X) :
          Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 k)) :
            Matrix (Fin 2) (Fin 2) (GaloisField 2 k)).mulVec v) := by
  rcases h with ⟨m, hm, hm1, ⟨e⟩, _⟩ | ⟨k, hk, e, hmod⟩ | ⟨k, hk, e, _⟩
  · exfalso
    haveI : NeZero m := ⟨hm.pos.ne'⟩
    haveI := s716F_isSolvable_dihedralGroup m
    have hsol : Group.IsSolvable (↥X ⧸ Y.subgroupOf X) :=
      solvable_of_solvable_injective (f := e.toMonoidHom) e.injective
    exact not_isSolvable_of_isL2Gp hn hX hsol
  · exact ⟨k, e, hmod⟩
  · exfalso
    have h3 := three_dvd_card_of_isL2Gp hX
    rw [Nat.card_congr e.toEquiv] at h3
    exact CFSG.Quasithin.E6.E68Proof.RankOne.not_three_dvd_card_sz hk h3

theorem inf_centralizer_le_of_natural {X Y P Q : Subgroup G} [(Y.subgroupOf X).Normal]
    {n : ℕ} (hn : 2 ≤ n) (hX : IsL2Gp (↥X ⧸ Y.subgroupOf X) n)
    (hnat : IsNaturalSection X Y P Q) {l : G} (hl : l ∈ X) (hlY : l ∉ Y) {m : ℕ} (hm : Odd m)
    (hlm : l ^ m ∈ Y) : P ⊓ Subgroup.centralizer ({l} : Set G) ≤ Q := by
  obtain ⟨k, e, -, -, φ, -, hker, hact⟩ := exists_natural_l2_of_isNaturalSection hn hX hnat
  intro w hw
  have hwP : w ∈ P := hw.1
  have hcomm : w * l = l * w := Subgroup.mem_centralizer_singleton_iff.mp hw.2
  have hg1 : e (QuotientGroup.mk ⟨l, hl⟩) ≠ 1 := by
    intro h1
    have h2 : (QuotientGroup.mk ⟨l, hl⟩ : ↥X ⧸ Y.subgroupOf X) = 1 :=
      e.injective (by rw [h1, map_one])
    rw [QuotientGroup.eq_one_iff] at h2
    exact hlY (Subgroup.mem_subgroupOf.mp h2)
  have hmem : (⟨l, hl⟩ : ↥X) ^ m ∈ Y.subgroupOf X := by
    rw [Subgroup.mem_subgroupOf]
    simpa using hlm
  have hgm : e (QuotientGroup.mk ⟨l, hl⟩) ^ m = 1 := by
    rw [← map_pow, ← QuotientGroup.mk_pow, (QuotientGroup.eq_one_iff _).mpr hmem, map_one]
  have hq : ((⟨w, hwP⟩ : ↥P) : G) = ((⟨l, hl⟩ : ↥X) : G) * ((⟨w, hwP⟩ : ↥P) : G) *
      ((⟨l, hl⟩ : ↥X) : G)⁻¹ := by
    simp only
    rw [← hcomm, mul_assoc, mul_inv_cancel, mul_one]
  have hv := hact ⟨l, hl⟩ ⟨w, hwP⟩ ⟨w, hwP⟩ hq
  have hv' : ((e (QuotientGroup.mk ⟨l, hl⟩) : Matrix.SpecialLinearGroup (Fin 2)
      (GaloisField 2 k)) : Matrix (Fin 2) (Fin 2) (GaloisField 2 k)).mulVec
        (Multiplicative.toAdd (φ ⟨w, hwP⟩)) = Multiplicative.toAdd (φ ⟨w, hwP⟩) :=
    (congrArg Multiplicative.toAdd hv).symm
  by_cases hv0 : Multiplicative.toAdd (φ ⟨w, hwP⟩) = 0
  · have h1 : φ ⟨w, hwP⟩ = 1 := hv0
    have h2 : (⟨w, hwP⟩ : ↥P) ∈ φ.ker := h1
    rw [hker] at h2
    exact Subgroup.mem_subgroupOf.mp h2
  · exfalso
    have hgg := mul_self_eq_one_of_mulVec_eq hv0 hv'
    obtain ⟨j, rfl⟩ := hm
    have h3 : e (QuotientGroup.mk ⟨l, hl⟩) ^ (2 * j + 1) = e (QuotientGroup.mk ⟨l, hl⟩) := by
      rw [pow_succ, pow_mul, sq, hgg, one_pow, one_mul]
    rw [hgm] at h3
    exact hg1 h3.symm

theorem inf_centralizer_eq_bot_of_natural {X Y : Subgroup G} [(Y.subgroupOf X).Normal]
    (hYX : Y ≤ X) {n : ℕ} (hn : 2 ≤ n) (hX : IsL2Gp (↥X ⧸ Y.subgroupOf X) n)
    (hnat : ∀ P Q : Subgroup G, IsChiefSection X Y P Q → IsNaturalSection X Y P Q)
    {l : G} (hl : l ∈ X) (hlY : l ∉ Y) {m : ℕ} (hm : Odd m) (hlm : l ^ m ∈ Y) :
    Y ⊓ Subgroup.centralizer ({l} : Set G) = ⊥ := by
  have hXY : IsInvariantUnder X Y :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hYX).mp inferInstance
  have key : ∀ (N : ℕ) (B : Subgroup G), Nat.card ↥B ≤ N → IsInvariantUnder X B → B ≤ Y →
      B ⊓ Subgroup.centralizer ({l} : Set G) = ⊥ := by
    intro N
    induction N with
    | zero =>
      intro B hB _ _
      exact absurd hB (by have := Nat.card_pos (α := ↥B); omega)
    | succ N ih =>
      intro B hB hBinv hBY
      by_cases hB0 : B = ⊥
      · rw [hB0, bot_inf_eq]
      · have hbot_inv : IsInvariantUnder X (⊥ : Subgroup G) := by
          unfold IsInvariantUnder
          rw [(Subgroup.normalizer_eq_top_iff (H := (⊥ : Subgroup G))).mpr inferInstance]
          exact le_top
        obtain ⟨B₀, ⟨hB₀inv, hB₀lt⟩, hB₀max⟩ := Set.exists_max_image
          {C : Subgroup G | IsInvariantUnder X C ∧ C < B} (fun C => Nat.card ↥C)
          (Set.toFinite _) ⟨⊥, hbot_inv, bot_lt_iff_ne_bot.mpr hB0⟩
        have hchief : IsChiefSection X Y B B₀ := by
          refine ⟨hB₀lt, hBY, hBinv, hB₀inv, ?_⟩
          intro C hCinv hB₀C hCB
          rcases eq_or_lt_of_le hCB with hCB' | hCB'
          · exact Or.inr hCB'
          · left
            have hle : Nat.card ↥C ≤ Nat.card ↥B₀ := hB₀max C ⟨hCinv, hCB'⟩
            exact (Subgroup.eq_of_le_of_card_ge hB₀C hle).symm
        have hle := inf_centralizer_le_of_natural hn hX (hnat B B₀ hchief) hl hlY hm hlm
        have hcard : Nat.card ↥B₀ < Nat.card ↥B := Subgroup.card_lt_of_lt hB₀lt
        have h0 : B₀ ⊓ Subgroup.centralizer ({l} : Set G) = ⊥ :=
          ih B₀ (by omega) hB₀inv (hB₀lt.le.trans hBY)
        rw [eq_bot_iff]
        calc B ⊓ Subgroup.centralizer ({l} : Set G) ≤ B₀ ⊓ Subgroup.centralizer ({l} : Set G) :=
              le_inf hle inf_le_right
          _ = ⊥ := h0
          _ ≤ ⊥ := le_rfl
  exact key _ Y le_rfl hXY le_rfl

theorem isSimpleGroup_of_surjective_isL2Gp {Γ S : Type} [Group Γ] [Group S] {n : ℕ} (hn : 2 ≤ n)
    (hS : IsL2Gp S n)
    (hΓ : (∃ m : ℕ, Odd m ∧ Nonempty (Γ ≃* DihedralGroup m)) ∨
      (∃ k : ℕ, 1 ≤ k ∧ Nonempty (Γ ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 k))) ∨
      (∃ k : ℕ, 1 ≤ k ∧ Nonempty (Γ ≃* Sz k)))
    {f : Γ →* S} (hf : Function.Surjective f) : IsSimpleGroup Γ := by
  rcases hΓ with ⟨m, hm, ⟨e⟩⟩ | ⟨k, hk, ⟨e⟩⟩ | ⟨k, hk, ⟨e⟩⟩
  · exfalso
    haveI : NeZero m := ⟨hm.pos.ne'⟩
    haveI := s716F_isSolvable_dihedralGroup m
    haveI : Group.IsSolvable Γ := solvable_of_solvable_injective (f := e.toMonoidHom) e.injective
    haveI : Group.IsSolvable S := solvable_of_surjective hf
    exact not_isSolvable_of_isL2Gp hn hS inferInstance
  · have hΓL : IsL2Gp Γ k :=
      ⟨GaloisField 2 k, inferInstance, inferInstance, GaloisField.card 2 k (by omega), ⟨e⟩⟩
    haveI : Finite Γ := finite_of_isL2Gp hΓL
    by_cases hk2 : 2 ≤ k
    · exact isSimpleGroup_of_isL2Gp hk2 hΓL
    · exfalso
      have hk1 : k = 1 := by omega
      subst hk1
      have h60 := sixty_le_card_of_isL2Gp hn hS
      have hle := Nat.card_le_card_of_surjective f hf
      have hcard := card_eq_of_isL2Gp hΓL
      norm_num at hcard
      omega
  · haveI := CFSG.SignalizerFunctorTheorem.McBride.SzModel.sz_isSimpleGroup hk
    exact e.isSimpleGroup

theorem eq_of_quotient_dihedral_l2_sz {X Y N : Subgroup G} [(Y.subgroupOf X).Normal]
    [(N.subgroupOf X).Normal] (hQ : QuotientIsDihedralL2OrSz X Y) (hYN : Y ≤ N) (hNX : N ≤ X)
    {n : ℕ} (hn : 2 ≤ n) (hS : IsL2Gp (↥X ⧸ N.subgroupOf X) n) : N = Y := by
  have hle : Y.subgroupOf X ≤ Subgroup.comap (MonoidHom.id ↥X) (N.subgroupOf X) :=
    fun x hx => hYN hx
  set f : (↥X ⧸ Y.subgroupOf X) →* (↥X ⧸ N.subgroupOf X) :=
    QuotientGroup.map (Y.subgroupOf X) (N.subgroupOf X) (MonoidHom.id ↥X) hle with hf
  have hfmk : ∀ x : ↥X, f (QuotientGroup.mk x) = QuotientGroup.mk x := fun x => rfl
  have hfs : Function.Surjective f := by
    intro s
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective s
    exact ⟨QuotientGroup.mk x, hfmk x⟩
  haveI hsimple : IsSimpleGroup (↥X ⧸ Y.subgroupOf X) :=
    isSimpleGroup_of_surjective_isL2Gp hn hS hQ hfs
  rcases hsimple.eq_bot_or_eq_top_of_normal f.ker with hker | hker
  · refine le_antisymm (fun x hx => ?_) hYN
    have h1 : (QuotientGroup.mk (⟨x, hNX hx⟩ : ↥X) : ↥X ⧸ N.subgroupOf X) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr hx
    have h2 : (QuotientGroup.mk (⟨x, hNX hx⟩ : ↥X) : ↥X ⧸ Y.subgroupOf X) ∈ f.ker := by
      rw [MonoidHom.mem_ker, hfmk]; exact h1
    rw [hker, Subgroup.mem_bot] at h2
    exact (QuotientGroup.eq_one_iff (N := Y.subgroupOf X) (⟨x, hNX hx⟩ : ↥X)).mp h2
  · exfalso
    haveI : Subsingleton (↥X ⧸ N.subgroupOf X) := by
      refine ⟨fun a b => ?_⟩
      obtain ⟨g, rfl⟩ := hfs a
      obtain ⟨g', rfl⟩ := hfs b
      have hg : f g = 1 := MonoidHom.mem_ker.mp (hker ▸ Subgroup.mem_top g)
      have hg' : f g' = 1 := MonoidHom.mem_ker.mp (hker ▸ Subgroup.mem_top g')
      rw [hg, hg']
    have h1 : Nat.card (↥X ⧸ N.subgroupOf X) = 1 := Nat.card_eq_one_iff_unique.mpr
      ⟨inferInstance, inferInstance⟩
    have h60 := sixty_le_card_of_isL2Gp hn hS
    omega

end CFSG.LocalAnalysis.WeakClosure81
