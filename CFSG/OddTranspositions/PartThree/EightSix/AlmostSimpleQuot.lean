module

public import CFSG.OddTranspositions.PartThree.EightSix.SecondKindSolvable
import CFSG.GroupTheory.InvolutionPow
import CFSG.OddTranspositions.WidthOne
import CFSG.OddTranspositions.SecondKindCoset

public section

namespace CFSG.OddTranspositions.PartThree.EightSix

open CFSG.Timmesfeld.Connectivity CFSG.Timmesfeld.Bridge.Asc72

theorem not_mem_of_index_gt {X : Type*} [Group X] {D : Set X} (hS : Setup X D) {M : Subgroup X}
    [M.Normal] (hidx : 2 < M.index) {d : X} (hd : d ∈ D) : d ∉ M := by
  have hMtop : M ≠ ⊤ := by
    intro h
    have h1 : M.index = 1 := by rw [h, Subgroup.index_top]
    omega
  intro hdM
  have hsub : D ⊆ M := by
    rcases hS.subset_or_disjoint M with h | h
    · exact h
    · exact absurd hdM (h d hd)
  exact hMtop (hS.eq_top_of_subset M hsub)

theorem setup_quotient {X : Type*} [Group X] {D : Set X} (hS : Setup X D) {M : Subgroup X}
    [M.Normal] (hidx : 2 < M.index) : Setup (X ⧸ M) (QuotientGroup.mk' M '' D) :=
  hS.map (QuotientGroup.mk' M) (QuotientGroup.mk'_surjective M) (by
    intro d hd h
    exact not_mem_of_index_gt hS hidx hd ((QuotientGroup.eq_one_iff d).mp h))

theorem closure_map_eq_top {X : Type*} [Group X] {M : Subgroup X} [M.Normal] {u w v : X}
    (hgen : Subgroup.closure ({u, w, v} : Set X) = ⊤)
    (hvbar : QuotientGroup.mk' M v = QuotientGroup.mk' M u) :
    Subgroup.closure ({QuotientGroup.mk' M u, QuotientGroup.mk' M w} : Set (X ⧸ M)) = ⊤ := by
  have hmap : Subgroup.closure ((QuotientGroup.mk' M) '' ({u, w, v} : Set X)) = ⊤ := by
    rw [← Subgroup.map_top_of_surjective (QuotientGroup.mk' M)
      (QuotientGroup.mk'_surjective M), ← hgen, MonoidHom.map_closure]
  refine le_antisymm le_top ?_
  rw [← hmap]
  refine (Subgroup.closure_le (K := Subgroup.closure
    ({QuotientGroup.mk' M u, QuotientGroup.mk' M w} : Set (X ⧸ M)))).mpr ?_
  rintro z ⟨y, hy, rfl⟩
  rcases hy with hy | hy | hy
  · rw [hy]; exact Subgroup.subset_closure (by simp)
  · rw [hy]; exact Subgroup.subset_closure (by simp)
  · rw [hy, hvbar]; exact Subgroup.subset_closure (by simp)

theorem map_eq_of_widthOne {X : Type} [Group X] [Finite X] {D : Set X} {M : Subgroup X}
    [M.Normal] (hSbar : Setup (X ⧸ M) (QuotientGroup.mk' M '' D))
    (hW : WidthOne (QuotientGroup.mk' M '' D)) {u w v : X} (htri : IsTriangle D u w v) :
    QuotientGroup.mk' M v = QuotientGroup.mk' M u := by
  have hv : QuotientGroup.mk' M v ∈ QuotientGroup.mk' M '' D := ⟨v, htri.2.1, rfl⟩
  have hu : QuotientGroup.mk' M u ∈ QuotientGroup.mk' M '' D := ⟨u, htri.1, rfl⟩
  exact eq_of_commute_of_widthOne hSbar hW hv hu
    (Commute.map htri.2.2.2.2.1 (QuotientGroup.mk' M)).symm

theorem mul_not_mem_of_index {X : Type*} [Group X] {M : Subgroup X} [M.Normal]
    (hidx : 2 < M.index) {u w : X}
    (hu2 : QuotientGroup.mk' M u * QuotientGroup.mk' M u = 1)
    (hgen : Subgroup.closure ({QuotientGroup.mk' M u, QuotientGroup.mk' M w} :
      Set (X ⧸ M)) = ⊤) : u * w ∉ M := by
  intro hmem
  have h1 : QuotientGroup.mk' M u * QuotientGroup.mk' M w = 1 := by
    rw [← map_mul]
    exact (QuotientGroup.eq_one_iff _).mpr hmem
  have hwbar : QuotientGroup.mk' M w = QuotientGroup.mk' M u := by
    rw [eq_inv_of_mul_eq_one_right h1, inv_eq_of_mul_eq_one_right hu2]
  have htop : (⊤ : Subgroup (X ⧸ M)) = Subgroup.zpowers (QuotientGroup.mk' M u) := by
    rw [← hgen, Subgroup.zpowers_eq_closure, hwbar]
    congr 1
    simp
  have hcard : Nat.card (X ⧸ M) ≤ 2 := by
    rw [← Subgroup.card_top (G := X ⧸ M), htop, Nat.card_zpowers]
    have h2 : orderOf (QuotientGroup.mk' M u) ∣ 2 :=
      orderOf_dvd_of_pow_eq_one (by simpa [pow_two] using hu2)
    exact Nat.le_of_dvd (by norm_num) h2
  have hidx' : 2 < Nat.card (X ⧸ M) := hidx
  omega

theorem conj_eq_inv_of_mem_zpowers_mul {Y : Type} [Group Y] {a b : Y} (ha : a * a = 1)
    (hb : b * b = 1) {x : Y} (hx : x ∈ Subgroup.zpowers (a * b)) : a * x * a⁻¹ = x⁻¹ := by
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have h1 : a * (a * b) * a⁻¹ = (a * b)⁻¹ := by
    rw [mul_inv_rev, hbi, hai]
    calc a * (a * b) * a = (a * a) * (b * a) := by group
      _ = b * a := by rw [ha, one_mul]
  calc a * (a * b) ^ k * a⁻¹ = (a * (a * b) * a⁻¹) ^ k := conj_zpow.symm
    _ = ((a * b)⁻¹) ^ k := by rw [h1]
    _ = ((a * b) ^ k)⁻¹ := by rw [inv_zpow]

theorem eq_one_or_eq_of_commute_of_odd {Y : Type} [Group Y] {a b : Y} (ha : a * a = 1)
    (hb : b * b = 1) (hodd : Odd (orderOf (a * b)))
    (hgen : Subgroup.closure ({a, b} : Set Y) = ⊤) {g : Y} (hg : Commute g a) :
    g = 1 ∨ g = a := by
  have hkey : ∀ x : Y, x ∈ Subgroup.zpowers (a * b) → x * x = 1 → x = 1 := by
    intro x hx hx2
    have hdvd : orderOf x ∣ orderOf (a * b) := orderOf_dvd_of_mem_zpowers hx
    have h2 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by simpa [pow_two] using hx2)
    rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h | h
    · exact orderOf_eq_one_iff.mp h
    · exact absurd h (hodd.ne_two_of_dvd_nat hdvd)
  have hmem : g ∈ Subgroup.closure ({a, b} : Set Y) := hgen ▸ Subgroup.mem_top g
  rcases CFSG.OddTranspositions.dihedral_cover ha hb hmem with hrot | href
  ·
    have h1 : a * g * a⁻¹ = g := by
      calc a * g * a⁻¹ = (g * a) * a⁻¹ := by rw [hg.eq]
        _ = g := by group
    have h2 := conj_eq_inv_of_mem_zpowers_mul ha hb hrot
    rw [h1] at h2
    have hsq : g * g = 1 := by
      have h3 := congrArg (fun x : Y => x * g) h2
      rwa [inv_mul_cancel] at h3
    exact Or.inl (hkey g hrot hsq)
  ·
    have h1 : a * (g * a) * a⁻¹ = g * a := by
      calc a * (g * a) * a⁻¹ = a * g := by group
        _ = g * a := hg.eq.symm
    have h2 := conj_eq_inv_of_mem_zpowers_mul ha hb href
    rw [h1] at h2
    have hsq : (g * a) * (g * a) = 1 := by
      have h3 := congrArg (fun x : Y => x * (g * a)) h2
      rwa [inv_mul_cancel] at h3
    have hga : g * a = 1 := hkey (g * a) href hsq
    refine Or.inr ?_
    calc g = g * (a * a) := by rw [ha, mul_one]
      _ = (g * a) * a := by group
      _ = 1 * a := by rw [hga]
      _ = a := one_mul a

theorem exists_conj_of_map_eq_of_ker {X : Type*} [Group X] {Y : Type} [Group Y]
    {D : Set X} (hS : Setup X D) (φ : X →* Y) {u w : X} (hu : u ∈ D) (hw : w ∈ D)
    (hodd : Odd (orderOf (φ u * φ w)))
    (hgen : Subgroup.closure ({φ u, φ w} : Set Y) = ⊤) {d : X} (hd : d ∈ D)
    (hdu : φ d = φ u) : ∃ m ∈ φ.ker, d = m * u * m⁻¹ := by
  obtain ⟨g, hg⟩ := isConj_iff.mp (hS.isConj hu hd)
  have hu2 : φ u * φ u = 1 := by rw [← map_mul, hS.oddT.mul_self_eq_one hu, map_one]
  have hw2 : φ w * φ w = 1 := by rw [← map_mul, hS.oddT.mul_self_eq_one hw, map_one]
  have hcomm : Commute (φ g) (φ u) := by
    have h1 : φ (g * u * g⁻¹) = φ g * φ u * (φ g)⁻¹ := by rw [map_mul, map_mul, map_inv]
    have h2 : φ (g * u * g⁻¹) = φ u := by rw [hg]; exact hdu
    show φ g * φ u = φ u * φ g
    calc φ g * φ u = (φ g * φ u * (φ g)⁻¹) * φ g := by group
      _ = φ u * φ g := by rw [← h1, h2]
  rcases eq_one_or_eq_of_commute_of_odd hu2 hw2 hodd hgen hcomm with h1 | h1
  · exact ⟨g, MonoidHom.mem_ker.mpr h1, hg.symm⟩
  · refine ⟨g * u⁻¹, MonoidHom.mem_ker.mpr ?_, ?_⟩
    · rw [map_mul, map_inv, h1, mul_inv_cancel]
    · rw [← hg]
      group

theorem exists_conj_of_map_eq {X : Type} [Group X] {D : Set X} (hS : Setup X D)
    {M : Subgroup X} [M.Normal] {u w : X} (hu : u ∈ D) (hw : w ∈ D)
    (hodd : Odd (orderOf (u * w)))
    (hgen : Subgroup.closure ({QuotientGroup.mk' M u, QuotientGroup.mk' M w} :
      Set (X ⧸ M)) = ⊤) {d : X} (hd : d ∈ D)
    (hdu : QuotientGroup.mk' M d = QuotientGroup.mk' M u) :
    ∃ m ∈ M, d = m * u * m⁻¹ := by
  have hoddbar : Odd (orderOf (QuotientGroup.mk' M u * QuotientGroup.mk' M w)) := by
    have h1 : QuotientGroup.mk' M u * QuotientGroup.mk' M w = QuotientGroup.mk' M (u * w) :=
      (map_mul _ _ _).symm
    rw [h1]
    exact Odd.of_dvd_nat hodd (orderOf_map_dvd _ _)
  obtain ⟨m, hm, hmd⟩ :=
    exists_conj_of_map_eq_of_ker hS (QuotientGroup.mk' M) hu hw hoddbar hgen hd hdu
  exact ⟨m, (QuotientGroup.eq_one_iff m).mp (MonoidHom.mem_ker.mp hm), hmd⟩

theorem not_isSolvable_of_simple_normal {X : Type*} [Group X] {M : Subgroup X} [M.Normal]
    (hMs : IsSimpleGroup M) (hC : Subgroup.centralizer (M : Set X) = ⊥) :
    ¬ Group.IsSolvable X := by
  intro hsolv
  have hcomm : ∀ a b : M, a * b = b * a :=
    (IsSimpleGroup.comm_iff_isSolvable (G := M)).mpr inferInstance
  have hle : M ≤ Subgroup.centralizer (M : Set X) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact congrArg Subtype.val (hcomm ⟨y, hy⟩ ⟨x, hx⟩)
  rw [hC] at hle
  have hbot : M = ⊥ := le_bot_iff.mp hle
  obtain ⟨m, hm⟩ := exists_ne (1 : M)
  exact hm (Subtype.ext (Subgroup.mem_bot.mp (hbot ▸ m.2)))

theorem map_eq_of_thirdKind {X : Type} [Group X] [Finite X] {D : Set X}
    (hodd : IsOddTransp D) (hnormal : IsNormalSet D) {M : Subgroup X} [M.Normal]
    (hSbar : Setup (X ⧸ M) (QuotientGroup.mk' M '' D))
    (hW : WidthOne (QuotientGroup.mk' M '' D)) {u v a : X} (hu : u ∈ D) (ha : a ∈ D)
    (htri : IsTriangle D u a v) (hthird : IsThirdKind u a v)
    (hu2 : QuotientGroup.mk' M u * QuotientGroup.mk' M u = 1)
    (hvbar : QuotientGroup.mk' M v = QuotientGroup.mk' M u) :
    QuotientGroup.mk' M a = QuotientGroup.mk' M u := by
  obtain ⟨n, hnodd, -, hord⟩ := hthird
  obtain ⟨-, -, hzu, -, -, hzD⟩ := IsTriangle.third_kind hodd hnormal htri hnodd hord
  set z : X := (u * v * a) ^ n with hzdef
  have huvz : QuotientGroup.mk' M (u * v * z) = QuotientGroup.mk' M z := by
    rw [map_mul, map_mul, hvbar, hu2, one_mul]
  have hzm : QuotientGroup.mk' M z ∈ QuotientGroup.mk' M '' D := ⟨u * v * z, hzD, huvz⟩
  have hum : QuotientGroup.mk' M u ∈ QuotientGroup.mk' M '' D := ⟨u, hu, rfl⟩
  have hπz : QuotientGroup.mk' M z = QuotientGroup.mk' M u :=
    eq_of_commute_of_widthOne hSbar hW hzm hum (Commute.map hzu (QuotientGroup.mk' M))
  have ha2 : QuotientGroup.mk' M a * QuotientGroup.mk' M a = 1 := by
    rw [← map_mul, hodd.mul_self_eq_one ha, map_one]
  have hπuva : QuotientGroup.mk' M (u * v * a) = QuotientGroup.mk' M a := by
    rw [map_mul, map_mul, hvbar, hu2, one_mul]
  calc QuotientGroup.mk' M a = (QuotientGroup.mk' M a) ^ n :=
        (CFSG.GroupTheory.pow_eq_self_of_odd_of_mul_self_eq_one ha2 hnodd).symm
    _ = QuotientGroup.mk' M ((u * v * a) ^ n) := by rw [map_pow, hπuva]
    _ = QuotientGroup.mk' M z := by rw [hzdef]
    _ = QuotientGroup.mk' M u := hπz

theorem exists_thirdKind_conj_of_almostSimple {X : Type} [Group X] [Finite X] {D : Set X}
    (hS : Setup X D) {M : Subgroup X} [M.Normal] (hMs : IsSimpleGroup M)
    (hC : Subgroup.centralizer (M : Set X) = ⊥) (hidx : 2 < M.index)
    (hW : WidthOne (QuotientGroup.mk' M '' D)) {u w v : X} (htri : IsTriangle D u w v)
    (h4 : orderOf (u * v * w) = 4) (hgen : Subgroup.closure ({u, w, v} : Set X) = ⊤) :
    u ∉ M ∧ u * w ∉ M ∧ (∃ m ∈ M, v = m * u * m⁻¹) ∧
      ∃ a ∈ D, a ∈ Subgroup.closure {u, w} ∧ IsTriangle D u a v ∧ IsThirdKind u a v ∧
        ∃ m ∈ M, a = m * u * m⁻¹ := by
  have hSbar : Setup (X ⧸ M) (QuotientGroup.mk' M '' D) := setup_quotient hS hidx
  have hvbar : QuotientGroup.mk' M v = QuotientGroup.mk' M u := map_eq_of_widthOne hSbar hW htri
  have hgenbar : Subgroup.closure ({QuotientGroup.mk' M u, QuotientGroup.mk' M w} :
      Set (X ⧸ M)) = ⊤ := closure_map_eq_top hgen hvbar
  have hu2 : QuotientGroup.mk' M u * QuotientGroup.mk' M u = 1 := by
    rw [← map_mul, hS.oddT.mul_self_eq_one htri.1, map_one]
  have hodd : Odd (orderOf (u * w)) :=
    hS.oddT.odd_of_not_commute htri.1 htri.2.2.1 htri.2.2.2.2.2.1
  have huwM : u * w ∉ M := mul_not_mem_of_index hidx hu2 hgenbar
  have hvconj : ∃ m ∈ M, v = m * u * m⁻¹ :=
    exists_conj_of_map_eq (u := u) (w := w) hS htri.1 htri.2.2.1 hodd hgenbar (d := v)
      htri.2.1 hvbar
  have hns : ¬ Group.IsSolvable (Subgroup.closure ({u, w, v} : Set X)) := by
    rw [hgen]
    intro htop
    exact not_isSolvable_of_simple_normal hMs hC (Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.topEquiv (G := X)).symm.toMonoidHom) (MulEquiv.injective _))
  obtain ⟨a, haD, haX, htri_a, hthird_a⟩ :=
    exists_thirdKind_of_not_isSolvable hS.oddT hS.normal htri h4 hns
  have hπa : QuotientGroup.mk' M a = QuotientGroup.mk' M u :=
    map_eq_of_thirdKind hS.oddT hS.normal hSbar hW htri.1 haD htri_a hthird_a hu2 hvbar
  have hac : ∃ m ∈ M, a = m * u * m⁻¹ :=
    exists_conj_of_map_eq (u := u) (w := w) hS htri.1 htri.2.2.1 hodd hgenbar (d := a) haD
      hπa
  exact ⟨not_mem_of_index_gt hS hidx htri.1, huwM, hvconj, a, haD, haX, htri_a, hthird_a,
    hac⟩

end CFSG.OddTranspositions.PartThree.EightSix
