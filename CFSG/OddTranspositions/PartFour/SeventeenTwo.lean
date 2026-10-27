module

public import CFSG.OddTranspositions.HalphaQuotient
public import CFSG.OddTranspositions.PartThree.Statements
public import CFSG.OddTranspositions.PartFour.Line
public import CFSG.GroupTheory.PCore.SolvableRadical
public import CFSG.GroupTheory.SquareMemTwoGroup
public import CFSG.Timmesfeld.Bridge.Asc72Central

public section

namespace CFSG.OddTranspositions.PartFour

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
open CFSG.Timmesfeld.Connectivity

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem commutator_mem_pCore_of_mem_solvableRadical (h113 : PartThree.Theorem11_3)
    (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hn3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    {x : Halpha D hC.alpha} (hx : x ∈ CFSG.solvableRadical (Halpha D hC.alpha))
    (y : Halpha D hC.alpha) :
    x * y * x⁻¹ * y⁻¹ ∈ CFSG.pCore 2 (Halpha D hC.alpha) := by
  let H := Halpha D hC.alpha
  let Q := CFSG.pCore 2 H
  letI : Q.Normal := CFSG.pCore_normal
  have hxcenter : QuotientGroup.mk' Q x ∈ Subgroup.center (H ⧸ Q) := by
    have hmem : QuotientGroup.mk' Q x ∈ (CFSG.solvableRadical H).map (QuotientGroup.mk' Q) :=
      Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
    rwa [h113 (G := G) (D := D) hC hrad hn3] at hmem
  have hcomm : QuotientGroup.mk' Q x * QuotientGroup.mk' Q y =
      QuotientGroup.mk' Q y * QuotientGroup.mk' Q x :=
    ((Subgroup.mem_center_iff.mp hxcenter) (QuotientGroup.mk' Q y)).symm
  have hone : QuotientGroup.mk' Q (x * y * x⁻¹ * y⁻¹) = 1 := by
    simp only [map_mul, map_inv]
    rw [hcomm]
    group
  exact (QuotientGroup.eq_one_iff _).mp hone

theorem Halpha_le_normalizer_block (D α : Set G) : Halpha D α ≤ Subgroup.normalizer α := by
  rw [Halpha, Subgroup.closure_le]
  rintro x ⟨β, hβ, hxβ⟩
  exact OddLocal.mem_normalizer_of_commute
    (fun y hy => ((mem_Dalpha_iff.mp hβ).2.2.2 y hy x hxβ).symm)

theorem conj_mem_Dalpha_of_mem_normalizer {D α β : Set G} (hN : IsNormalSet D)
    (hβ : β ∈ Dalpha D α) {x : G} (hx : x ∈ Subgroup.normalizer α) :
    (fun y => x * y * x⁻¹) '' β ∈ Dalpha D α := by
  have hxα : (fun y => x * y * x⁻¹) '' α = α := by
    have h := Subgroup.mem_normalizer_iff_conj_image_eq.mp hx
    rwa [show (⇑(MulAut.conj x) : G → G) = (fun y => x * y * x⁻¹) by
      funext y; rw [MulAut.conj_apply]] at h
  have h := Dalpha.conj hN hβ x
  rwa [hxα] at h

theorem commute_conj_of_mem_radical (h113 : PartThree.Theorem11_3) (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hn3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    {c b : G} (hc : c ∈ DalphaStar D hC.alpha) (hb : b ∈ DalphaStar D hC.alpha)
    (hcb : Commute c b) {x : Halpha D hC.alpha}
    (hx : x ∈ CFSG.solvableRadical (Halpha D hC.alpha)) :
    Commute c ((x : G) * b * (x : G)⁻¹) := by
  have hcD : c ∈ D := DalphaStar_subset hC.isBlock_alpha hc
  have hbD : b ∈ D := DalphaStar_subset hC.isBlock_alpha hb
  rcases hC.setup.oddT.commute_or_odd hcD (hC.setup.normal (x : G) b hbD) with h | hodd
  · exact h
  haveI : (CFSG.pCore 2 (Halpha D hC.alpha)).Normal := CFSG.pCore_normal
  let cH : Halpha D hC.alpha := ⟨c, Subgroup.subset_closure hc⟩
  let bH : Halpha D hC.alpha := ⟨b, Subgroup.subset_closure hb⟩
  have hcb2 : (cH * bH) ^ 2 = 1 := Subtype.ext (by
    show (c * b) ^ 2 = 1
    rw [hcb.mul_pow, pow_two, pow_two, hC.setup.oddT.mul_self_eq_one hcD,
      hC.setup.oddT.mul_self_eq_one hbD, one_mul])
  have hsq : (cH * (x * bH * x⁻¹)) ^ 2 ∈ CFSG.pCore 2 (Halpha D hC.alpha) :=
    (CFSG.GroupTheory.sq_mul_mem_iff_of_mul_inv_mem
      (commutator_mem_pCore_of_mem_solvableRadical h113 hC hrad hn3 hx bH)).mpr
      (hcb2 ▸ Subgroup.one_mem _)
  have h1 := CFSG.GroupTheory.eq_one_of_odd_orderOf_of_sq_mem
    (CFSG.pCore_isPGroup (p := 2) (G := Halpha D hC.alpha))
    (by rw [← Subgroup.orderOf_coe]; exact hodd) hsq
  have h2 : c * ((x : G) * b * (x : G)⁻¹) = 1 := congrArg Subtype.val h1
  rw [eq_inv_of_mul_eq_one_right h2]
  exact (Commute.refl c).inv_right

theorem conj_mem_perp_of_mem_Dalpha (h113 : PartThree.Theorem11_3) (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hn3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    {β γ : Set G} (hβ : β ∈ Dalpha D hC.alpha) (hγ : γ ∈ Dalpha D hC.alpha)
    (hγβ : γ ∈ perp D β) {x : Halpha D hC.alpha}
    (hx : x ∈ CFSG.solvableRadical (Halpha D hC.alpha)) :
    (fun y => (x : G) * y * (x : G)⁻¹) '' β ∈ perp D γ := by
  classical
  let β' : Set G := (fun y => (x : G) * y * (x : G)⁻¹) '' β
  change β' ∈ perp D γ
  have hβ'Dα : β' ∈ Dalpha D hC.alpha :=
    conj_mem_Dalpha_of_mem_normalizer hC.setup.normal hβ
      (Halpha_le_normalizer_block D hC.alpha x.2)
  by_cases hβ'γ : β' = γ
  · rw [hβ'γ]
    exact mem_perp_iff.mpr (Or.inr rfl)
  · have hβ'classγ : β' ∈ blockClass γ :=
      mem_blockClass_of_mem_blockClass hγ.1 hβ'Dα.1
    obtain ⟨k, hk⟩ := mem_blockClass_iff.mp hβ'classγ
    obtain ⟨g, hg⟩ := mem_blockClass_iff'.mp hγ.1
    have hγblock : IsBlock D γ := by
      rw [hg]
      exact hC.isBlock_alpha.conj hC.setup.normal g
    obtain ⟨b, hbβ⟩ := nonempty_of_mem_blockClass hC.isBlock_alpha.nonempty hβ.1
    have hcb : ∃ c ∈ γ, Commute c b := by
      rcases mem_perp_iff.mp hγβ with hγDβ | hγeqβ
      · obtain ⟨c, hcγ⟩ := hγblock.nonempty
        exact ⟨c, hcγ, ((mem_Dalpha_iff.mp hγDβ).2.2.2 b hbβ c hcγ).symm⟩
      · exact ⟨b, by rw [hγeqβ]; exact hbβ, Commute.refl b⟩
    obtain ⟨c, hcγ, hcb⟩ := hcb
    have hb'β' : (x : G) * b * (x : G)⁻¹ ∈ β' := ⟨b, hbβ, rfl⟩
    have hcStar : c ∈ DalphaStar D hC.alpha := ⟨γ, hγ, hcγ⟩
    have hbStar : b ∈ DalphaStar D hC.alpha := ⟨β, hβ, hbβ⟩
    have hcb' : Commute c ((x : G) * b * (x : G)⁻¹) :=
      commute_conj_of_mem_radical h113 hC hrad hn3 hcStar hbStar hcb hx
    have hneimg : (fun y => k * y * k⁻¹) '' γ ≠ γ := by
      rw [← hk]
      exact hβ'γ
    have hmemimg : (x : G) * b * (x : G)⁻¹ ∈ (fun y => k * y * k⁻¹) '' γ := by
      rw [← hk]
      exact hb'β'
    have hcomm := commute_block_of_mem_apply hC.setup.normal hC.setup.oddT hγblock hneimg
      hcγ hmemimg hcb'
    refine mem_perp_iff.mpr (Or.inl ?_)
    refine mem_Dalpha_iff.mpr ⟨hβ'classγ, hβ'Dα.2.1, hβ'γ, ?_⟩
    intro a ha b'' hb''
    exact hcomm a ha b'' (by rw [← hk]; exact hb'')

theorem conj_mem_blockLine (h113 : PartThree.Theorem11_3) (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hn3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    {β : Set G} (hβ : β ∈ Dalpha D hC.alpha) {x : Halpha D hC.alpha}
    (hx : x ∈ CFSG.solvableRadical (Halpha D hC.alpha)) :
    (fun y => (x : G) * y * (x : G)⁻¹) '' β ∈ blockLine D hC.alpha β := by
  have hβ'Dα : (fun y => (x : G) * y * (x : G)⁻¹) '' β ∈ Dalpha D hC.alpha :=
    conj_mem_Dalpha_of_mem_normalizer hC.setup.normal hβ
      (Halpha_le_normalizer_block D hC.alpha x.2)
  refine ⟨hβ'Dα.1, ?_⟩
  intro γ hγ
  rcases mem_perp_iff.mp hγ.1 with hγDα | hγα
  · exact conj_mem_perp_of_mem_Dalpha h113 hC hrad hn3 hβ hγDα hγ.2 hx
  · rw [hγα]
    exact mem_perp_iff.mpr (Or.inl hβ'Dα)

theorem pCore_le_center_of_forall_conj_eq (hC : HypothesisC D) {b : G}
    (hb : b ∈ DalphaStar D hC.alpha)
    (hfix : ∀ q ∈ CFSG.pCore 2 (Halpha D hC.alpha),
      (q : G) * b * (q : G)⁻¹ = b) :
    CFSG.pCore 2 (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha) := by
  classical
  let H := Halpha D hC.alpha
  let Q := CFSG.pCore 2 H
  letI : Q.Normal := CFSG.pCore_normal
  intro q hq
  rw [Subgroup.mem_center_iff]
  intro y
  have hcent : ∀ s ∈ DstarH hC, s * q = q * s := by
    intro s hs
    let bH : H := ⟨b, Subgroup.subset_closure hb⟩
    have hbH : bH ∈ DstarH hC := hb
    obtain ⟨k, hk⟩ := DstarH_transitive hC hbH hs
    have hkq : k⁻¹ * q * k ∈ Q := by
      simpa using (inferInstance : Q.Normal).conj_mem q hq k⁻¹
    have hfix' : (k⁻¹ * q * k) * bH * (k⁻¹ * q * k)⁻¹ = bH := by
      apply Subtype.ext
      simpa [bH] using hfix (k⁻¹ * q * k) hkq
    have hconj : q * s * q⁻¹ = s := by
      rw [← hk]
      calc q * (k * bH * k⁻¹) * q⁻¹
          = k * ((k⁻¹ * q * k) * bH * (k⁻¹ * q * k)⁻¹) * k⁻¹ := by group
        _ = k * bH * k⁻¹ := by rw [hfix']
    calc s * q = (q * s * q⁻¹) * q := by rw [hconj]
      _ = q * s := by group
  have hle : Subgroup.closure (DstarH hC) ≤ Subgroup.centralizer ({q} : Set H) := by
    rw [Subgroup.closure_le]
    intro s hs
    exact Subgroup.mem_centralizer_singleton_iff.mpr (hcent s hs)
  have hy : y ∈ Subgroup.centralizer ({q} : Set H) :=
    hle (by rw [DstarH_closure_eq_top hC]; exact Subgroup.mem_top y)
  exact Subgroup.mem_centralizer_singleton_iff.mp
    (show y ∈ Subgroup.centralizer ({q} : Set H) from hy)

theorem exists_conj_ne_of_not_mem_center (hC : HypothesisC D)
    {x : Halpha D hC.alpha} (hxZ : x ∉ Subgroup.center (Halpha D hC.alpha)) :
    ∃ s ∈ DstarH hC, x * s * x⁻¹ ≠ s := by
  classical
  by_contra hno
  push Not at hno
  apply hxZ
  change x ∈ Subgroup.center (Halpha D hC.alpha)
  rw [Subgroup.mem_center_iff]
  intro y
  have hle : Subgroup.closure (DstarH hC) ≤
      Subgroup.centralizer ({x} : Set (Halpha D hC.alpha)) := by
    rw [Subgroup.closure_le]
    intro s hs
    have hfix := hno s hs
    exact Subgroup.mem_centralizer_singleton_iff.mpr (by
      calc s * x = (x * s * x⁻¹) * x := by rw [hfix]
        _ = x * s := by group)
  have hy : y ∈ Subgroup.centralizer ({x} : Set (Halpha D hC.alpha)) :=
    hle (by rw [DstarH_closure_eq_top hC]; exact Subgroup.mem_top y)
  exact Subgroup.mem_centralizer_singleton_iff.mp
    (show y ∈ Subgroup.centralizer ({x} : Set (Halpha D hC.alpha)) from hy)

theorem exists_pCore_conj_ne (h113 : PartThree.Theorem11_3) (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hn3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    (hMZ : ¬ CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    {b : G} (hb : b ∈ DalphaStar D hC.alpha) :
    ∃ x ∈ CFSG.pCore 2 (Halpha D hC.alpha), (x : G) * b * (x : G)⁻¹ ≠ b := by
  classical
  let H := Halpha D hC.alpha
  let Q := CFSG.pCore 2 H
  letI : Q.Normal := CFSG.pCore_normal
  by_contra hcon
  push Not at hcon
  have hQcenter : Q ≤ Subgroup.center H := pCore_le_center_of_forall_conj_eq hC hb hcon
  have hnot : ¬ (CFSG.solvableRadical H : Set H) ⊆ (Subgroup.center H : Set H) := hMZ
  obtain ⟨x, hxM, hxZ⟩ := Set.not_subset.mp hnot
  obtain ⟨b₀, hb₀D, hb₀ne⟩ := exists_conj_ne_of_not_mem_center hC hxZ
  let b₁ : H := x * b₀ * x⁻¹
  have hb₁D : b₁ ∈ DstarH hC := by
    dsimp [b₁]
    exact DstarH_conj_mem hC (h := x) (x := b₀) hb₀D
  let z : H := b₀⁻¹ * b₁
  have hw : x * b₀ * x⁻¹ * b₀⁻¹ ∈ Q :=
    commutator_mem_pCore_of_mem_solvableRadical h113 hC hrad hn3 hxM b₀
  have hzQ : z ∈ Q := by
    have hz : z = b₀⁻¹ * (x * b₀ * x⁻¹ * b₀⁻¹) * b₀ := by
      dsimp [z, b₁]
      group
    rw [hz]
    simpa using (inferInstance : Q.Normal).conj_mem (x * b₀ * x⁻¹ * b₀⁻¹) hw b₀⁻¹
  have hzcenter : z ∈ Subgroup.center H := hQcenter hzQ
  have hz1 : z ≠ 1 := by
    have hbz : b₀ * z = b₁ := by
      dsimp [z, b₁]
      group
    intro hz1
    rw [hz1, mul_one] at hbz
    exact hb₀ne hbz.symm
  have hsetup : Setup H (DstarH hC) :=
    { isClass := DstarH_isClass hC
      oddT := DstarH_isOddTransp hC
      gen := DstarH_closure_eq_top hC }
  have hb₀z : b₀ * z ∈ DstarH hC := by
    have hbz : b₀ * z = b₁ := by
      dsimp [z, b₁]
      group
    rwa [hbz]
  exact hsetup.false_of_mul_mem_center hb₀D hb₀z hzcenter hz1

theorem commute_of_mem_of_conj_mem_Dalpha (h113 : PartThree.Theorem11_3) (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hn3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    {β : Set G} (hβ : β ∈ Dalpha D hC.alpha) {a b : G} (ha : a ∈ β) (hb : b ∈ β)
    {x : Halpha D hC.alpha} (hxQ : x ∈ CFSG.pCore 2 (Halpha D hC.alpha))
    (hb'notβ : (x : G) * b * (x : G)⁻¹ ∉ β) :
    Commute a ((x : G) * b * (x : G)⁻¹) := by
  let H := Halpha D hC.alpha
  have hxM : x ∈ CFSG.solvableRadical H := CFSG.pCore_le_solvableRadical 2 H hxQ
  have hβ'BL : (fun y => (x : G) * y * (x : G)⁻¹) '' β ∈ blockLine D hC.alpha β :=
    conj_mem_blockLine h113 hC hrad hn3 hβ hxM
  have hβ'ne : (fun y => (x : G) * y * (x : G)⁻¹) '' β ≠ β := by
    intro heq
    apply hb'notβ
    rw [← heq]
    exact ⟨b, hb, rfl⟩
  have hβ'perpβ : (fun y => (x : G) * y * (x : G)⁻¹) '' β ∈ perp D β :=
    hβ'BL.2 β ⟨mem_perp_iff.mpr (Or.inl hβ), mem_perp_iff.mpr (Or.inr rfl)⟩
  have hβ'Dβ : (fun y => (x : G) * y * (x : G)⁻¹) '' β ∈ Dalpha D β := by
    rcases mem_perp_iff.mp hβ'perpβ with h | h
    · exact h
    · exact absurd h hβ'ne
  exact (mem_Dalpha_iff.mp hβ'Dβ).2.2.2 a ha _ ⟨b, hb, rfl⟩

theorem commute_of_mem_Dalpha (h89 : PartThree.Lemma8_9) (h113 : PartThree.Theorem11_3)
    (hC : HypothesisC D) (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hW : ¬ ∃ f n : ℕ, 2 ≤ f ∧ Nonempty (G ≃* L2Wreath f n))
    (hn3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    (hMZ : ¬ CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    {β : Set G} (hβ : β ∈ Dalpha D hC.alpha) {a b : G} (ha : a ∈ β) (hb : b ∈ β) :
    Commute a b := by
  by_contra hnab
  haveI : (CFSG.pCore 2 (Halpha D hC.alpha)).Normal := CFSG.pCore_normal
  have haD : a ∈ D := hβ.2.1 ha
  have hbD : b ∈ D := hβ.2.1 hb
  have hbStar : b ∈ DalphaStar D hC.alpha := ⟨β, hβ, hb⟩
  obtain ⟨x, hxQ, hxne⟩ := exists_pCore_conj_ne h113 hC hrad hn3 hMZ hbStar
  have hcomm : Commute a ((x : G) * b * (x : G)⁻¹) :=
    commute_of_mem_of_conj_mem_Dalpha h113 hC hrad hn3 hβ ha hb hxQ
      (fun hmem => hxne (h89 (G := G) (D := D) hC hrad hW β hβ b hb x hxQ hmem))
  let aH : Halpha D hC.alpha := ⟨a, Subgroup.subset_closure ⟨β, hβ, ha⟩⟩
  let bH : Halpha D hC.alpha := ⟨b, Subgroup.subset_closure hbStar⟩
  have hab2 : (aH * (x * bH * x⁻¹)) ^ 2 = 1 := Subtype.ext (by
    show (a * ((x : G) * b * (x : G)⁻¹)) ^ 2 = 1
    rw [hcomm.mul_pow, conj_pow, pow_two, pow_two, hC.setup.oddT.mul_self_eq_one haD,
      hC.setup.oddT.mul_self_eq_one hbD, mul_one, mul_inv_cancel, one_mul])
  have hsq : (aH * bH) ^ 2 ∈ CFSG.pCore 2 (Halpha D hC.alpha) :=
    (CFSG.GroupTheory.sq_mul_mem_iff_of_mul_inv_mem
      (commutator_mem_pCore_of_mem_solvableRadical h113 hC hrad hn3
        (CFSG.pCore_le_solvableRadical 2 _ hxQ) bH)).mp (hab2 ▸ Subgroup.one_mem _)
  have h1 := CFSG.GroupTheory.eq_one_of_odd_orderOf_of_sq_mem
    (CFSG.pCore_isPGroup (p := 2) (G := Halpha D hC.alpha))
    (by rw [← Subgroup.orderOf_coe]; exact hC.setup.oddT.odd_of_not_commute haD hbD hnab) hsq
  have h2 : a * b = 1 := congrArg Subtype.val h1
  apply hnab
  rw [eq_inv_of_mul_eq_one_right h2]
  exact (Commute.refl a).inv_right

theorem commute_of_mem_alpha (h89 : PartThree.Lemma8_9) (h113 : PartThree.Theorem11_3)
    (hC : HypothesisC D) (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hW : ¬ ∃ f n : ℕ, 2 ≤ f ∧ Nonempty (G ≃* L2Wreath f n))
    (hn3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    (hMZ : ¬ CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    {a b : G} (ha : a ∈ hC.alpha) (hb : b ∈ hC.alpha) : Commute a b := by
  obtain ⟨e, he⟩ := DstarH_nonempty hC
  obtain ⟨β, hβ, heβ⟩ := mem_DalphaStar_iff.mp ((mem_DstarH_iff hC).mp he)
  obtain ⟨g, hg⟩ := mem_blockClass_iff.mp (mem_Dalpha_iff.mp hβ).1
  have haβ : g * a * g⁻¹ ∈ β := by
    rw [hg]
    exact ⟨a, ha, rfl⟩
  have hbβ : g * b * g⁻¹ ∈ β := by
    rw [hg]
    exact ⟨b, hb, rfl⟩
  have hcomm := commute_of_mem_Dalpha h89 h113 hC hrad hW hn3 hMZ hβ haβ hbβ
  have hconj := hcomm.conj g⁻¹
  rw [inv_inv] at hconj
  have h1 : g⁻¹ * (g * a * g⁻¹) * g = a := by group
  have h2 : g⁻¹ * (g * b * g⁻¹) * g = b := by group
  rwa [h1, h2] at hconj

theorem two_lt_encard_blockLine (h89 : PartThree.Lemma8_9) (h113 : PartThree.Theorem11_3)
    (hC : HypothesisC D) (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hW : ¬ ∃ f n : ℕ, 2 ≤ f ∧ Nonempty (G ≃* L2Wreath f n))
    (hn3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    (hMZ : ¬ CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    {β : Set G} (hβ : β ∈ Dalpha D hC.alpha) :
    2 < (blockLine D hC.alpha β).encard := by
  classical
  obtain ⟨b, hb⟩ := nonempty_of_mem_blockClass hC.isBlock_alpha.nonempty hβ.1
  have hbStar : b ∈ DalphaStar D hC.alpha := ⟨β, hβ, hb⟩
  obtain ⟨x, hxQ, hxne⟩ := exists_pCore_conj_ne h113 hC hrad hn3 hMZ hbStar
  let H := Halpha D hC.alpha
  have hxM : x ∈ CFSG.solvableRadical H := CFSG.pCore_le_solvableRadical 2 H hxQ
  let β' : Set G := (fun y => (x : G) * y * (x : G)⁻¹) '' β
  have hβ'BL : β' ∈ blockLine D hC.alpha β := by
    dsimp [β']
    exact conj_mem_blockLine h113 hC hrad hn3 hβ hxM
  have hb'β' : (x : G) * b * (x : G)⁻¹ ∈ β' := ⟨b, hb, rfl⟩
  have hb'notβ : (x : G) * b * (x : G)⁻¹ ∉ β := by
    intro hmem
    exact hxne (h89 (G := G) (D := D) hC hrad hW β hβ b hb x hxQ hmem)
  have hβ'neβ : β' ≠ β := by
    intro h
    exact hb'notβ (h ▸ hb'β')
  have hβ'Dα : β' ∈ Dalpha D hC.alpha := by
    dsimp [β']
    exact conj_mem_Dalpha_of_mem_normalizer hC.setup.normal hβ
      (Halpha_le_normalizer_block D hC.alpha x.2)
  have hβ'neα : β' ≠ hC.alpha := Dalpha.ne_self hβ'Dα
  have hαneβ : hC.alpha ≠ β := (Dalpha.ne_self hβ).symm
  have hαmem : hC.alpha ∈ blockLine D hC.alpha β := left_mem_blockLine hC.isBlock_alpha.subset
  have hβmem : β ∈ blockLine D hC.alpha β := right_mem_blockLine hβ.1 hβ.2.1
  have hsub : ({hC.alpha, β, β'} : Set (Set G)) ⊆ blockLine D hC.alpha β := by
    intro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl | rfl
    · exact hαmem
    · exact hβmem
    · exact hβ'BL
  have hthree : ({hC.alpha, β, β'} : Set (Set G)).encard = 3 := by
    rw [Set.encard_eq_three]
    exact ⟨hC.alpha, β, β', hαneβ, hβ'neα.symm, hβ'neβ.symm, rfl⟩
  have hlt : (2 : ℕ∞) < ({hC.alpha, β, β'} : Set (Set G)).encard := by
    rw [hthree]
    norm_num
  exact lt_of_lt_of_le hlt (Set.encard_le_encard hsub)

end CFSG.OddTranspositions.PartFour
