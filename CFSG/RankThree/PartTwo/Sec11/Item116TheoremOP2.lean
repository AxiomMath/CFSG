module

public import CFSG.RankThree.PartTwo.Sec11.Item116TheoremOCor
import CFSG.RankThree.PartTwo.Sec6.Item65Tools

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

namespace TheoremO

section General

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_normalizer_zpowers_of_conj_eq {w c : G} (hwc : w * c * w⁻¹ = c) :
    w ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) := by
  have hwC : w ∈ Subgroup.centralizer ({c} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc w * c = w * c * w⁻¹ * w := by group
      _ = c * w := by rw [hwc]
  rw [GroupTheory.SteinbergBY.centralizer_singleton_eq_centralizer_zpowers] at hwC
  exact Subgroup.centralizer_le_normalizer _ hwC

theorem mem_normalizer_zpowers_of_conj_mem {w c : G} (hwc : w * c * w⁻¹ ∈ Subgroup.zpowers c) :
    w ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) := by
  have hw : w⁻¹ ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) := by
    apply mem_normalizer_of_forall_conj_mem
    intro u hu
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hwc
    rw [inv_inv, ← conj_zpow, ← hj, ← zpow_mul]
    exact Subgroup.zpow_mem_zpowers c _
  have := Subgroup.inv_mem _ hw
  rwa [inv_inv] at this

omit [Finite G] in
theorem conj_mem_zpowers_of_mem {c d n x : G} (hnc : n * c * n⁻¹ ∈ Subgroup.zpowers d)
    (hx : x ∈ Subgroup.zpowers c) : n * x * n⁻¹ ∈ Subgroup.zpowers d := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  rw [← conj_zpow]
  exact Subgroup.zpow_mem _ hnc k

theorem eq_one_of_mem_zpowers_of_mem_zpowers {c d y : G} (hd3 : d ^ 3 = 1)
    (hdc : d ∉ Subgroup.zpowers c) (hyc : y ∈ Subgroup.zpowers c) (hyd : y ∈ Subgroup.zpowers d) :
    y = 1 := by
  by_contra hy1
  apply hdc
  have heq := zpowers_eq_of_mem_of_ne_one hd3 hyd hy1
  exact Subgroup.zpowers_le.mpr hyc (heq ▸ Subgroup.mem_zpowers d)

theorem eq_bot_of_invariant {c d m n : G} (hcd : c * d = d * c) (hd3 : d ^ 3 = 1)
    (hdc : d ∉ Subgroup.zpowers c) {X : Subgroup G}
    (hXB : X ≤ Subgroup.closure ({c, d} : Set G)) (hdX : d ∉ X) (hmc : m * c * m⁻¹ = c)
    (hmd : m * d * m⁻¹ = d⁻¹) (hmX : ∀ x ∈ X, m * x * m⁻¹ ∈ X)
    (hnc : n * c * n⁻¹ ∈ Subgroup.zpowers d) (hnX : ∀ x ∈ X, n * x * n⁻¹ ∈ X) : X = ⊥ := by
  have hXc : ∀ x ∈ X, x ∈ Subgroup.zpowers c := by
    intro x hx
    obtain ⟨i, j, rfl⟩ := exists_zpow_mul_zpow_of_mem_closure_pair hcd (hXB hx)
    have hm : m * (c ^ i * d ^ j) * m⁻¹ = c ^ i * d ^ (-j) := by
      calc m * (c ^ i * d ^ j) * m⁻¹ = (m * c * m⁻¹) ^ i * (m * d * m⁻¹) ^ j := by
            rw [conj_zpow, conj_zpow]; group
        _ = c ^ i * d ^ (-j) := by rw [hmc, hmd, inv_zpow']
    have hcomm' : c ^ i * d ^ (2 * j) = d ^ (2 * j) * c ^ i :=
      (Commute.zpow_zpow (hcd : Commute c d) i (2 * j)).eq
    have h2 : d ^ (2 * j) ∈ X := by
      have := X.mul_mem hx (X.inv_mem (hmX _ hx))
      rwa [hm, show c ^ i * d ^ j * (c ^ i * d ^ (-j))⁻¹ = d ^ (2 * j) by
        calc c ^ i * d ^ j * (c ^ i * d ^ (-j))⁻¹ = c ^ i * (d ^ j * d ^ j) * (c ^ i)⁻¹ := by
              rw [zpow_neg]; group
          _ = c ^ i * d ^ (2 * j) * (c ^ i)⁻¹ := by rw [← zpow_add, two_mul]
          _ = d ^ (2 * j) := by rw [hcomm', mul_inv_cancel_right]] at this
    have h2' : d ^ (2 * j) = 1 := by
      by_contra hne
      exact hdX (Subgroup.zpowers_le.mpr h2 ((zpowers_eq_of_mem_of_ne_one hd3
        (Subgroup.zpow_mem_zpowers d _) hne).symm ▸ Subgroup.mem_zpowers d))
    have hd3' : d ^ (3 : ℤ) = 1 := by exact_mod_cast hd3
    have hdj : d ^ j = 1 := by
      calc d ^ j = d ^ (3 * j) * (d ^ (2 * j))⁻¹ := by
            rw [← zpow_neg, ← zpow_add]
            congr 1
            ring
        _ = 1 := by rw [zpow_mul, hd3', one_zpow, h2', inv_one, mul_one]
    rw [hdj, mul_one]
    exact Subgroup.zpow_mem_zpowers c i
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  have h3 := eq_one_of_mem_zpowers_of_mem_zpowers hd3 hdc (hXc _ (hnX x hx))
    (conj_mem_zpowers_of_mem hnc (hXc x hx))
  calc x = n⁻¹ * (n * x * n⁻¹) * n := by group
    _ = 1 := by rw [h3]; group

theorem conj_mem_sectionCentralizer {A Y : Subgroup G} {g x : G}
    (hgA : g ∈ Subgroup.normalizer (A : Set G)) (hgY : g ∈ Subgroup.normalizer (Y : Set G))
    (hx : x ∈ Late.sectionCentralizer A Y (inSubgroup (aschbacherSolvableCore 3) Y)) :
    g * x * g⁻¹ ∈ Late.sectionCentralizer A Y (inSubgroup (aschbacherSolvableCore 3) Y) := by
  obtain ⟨hxA, hxY⟩ := hx
  refine ⟨(Subgroup.mem_normalizer_iff.mp hgA x).mp hxA, fun y hy => ?_⟩
  have hy' : g⁻¹ * y * g ∈ Y := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgY) y).mp hy
    rwa [inv_inv] at this
  have h1 := hxY _ hy'
  have h2 := (Subgroup.mem_normalizer_iff.mp (Sec6.normalizer_le_normalizer_theta Y hgY) _).mp h1
  rwa [show g * (x * (g⁻¹ * y * g) * x⁻¹ * (g⁻¹ * y * g)⁻¹) * g⁻¹ =
    g * x * g⁻¹ * y * (g * x * g⁻¹)⁻¹ * y⁻¹ by group] at h2

end General

section Certified


variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
  {R Y : Subgroup G}

theorem conj_mem_zpowers_of_conj_eq (h : Sec11Std G A c L a R Y) {d : G}
    (hdL : A ⊓ L = Subgroup.zpowers d) (hdc : d ∉ Subgroup.zpowers c)
    (hD8 : ∀ w ∈ Subgroup.normalizer (A : Set G),
      (w * c * w⁻¹ ∈ Subgroup.zpowers c ∧ w * d * w⁻¹ ∈ Subgroup.zpowers d) ∨
      (w * c * w⁻¹ ∈ Subgroup.zpowers d ∧ w * d * w⁻¹ ∈ Subgroup.zpowers c))
    {n : G} (hnW : n ∈ Subgroup.normalizer (A : Set G)) (hnc : n * c * n⁻¹ ∈ Subgroup.zpowers d)
    (hna : n * a * n⁻¹ = a⁻¹) {w : G} (hwW : w ∈ Subgroup.normalizer (A : Set G))
    (hwa : w * a * w⁻¹ = a) :
    w * c * w⁻¹ ∈ Subgroup.zpowers c ∧ w * d * w⁻¹ ∈ Subgroup.zpowers d := by
  rcases hD8 w hwW with h1 | ⟨hwc, -⟩
  · exact h1
  exfalso
  have hAe := h.mem_partTwoF.1
  have hexp : ∀ u ∈ A, u ^ 3 = 1 := hAe.2
  have hdA : d ∈ A := (show d ∈ A ⊓ L by rw [hdL]; exact Subgroup.mem_zpowers d).1
  have haB : a ∉ Subgroup.closure ({c, d} : Set G) := fun ha =>
    Item116Fusion.not_mem_innerPreimage h (Item116Fusion.closure_le_innerPreimage h hdL ha)
  have hnc1 : n * c * n⁻¹ ≠ 1 := fun h1 => h.ne_one (by
    calc c = n⁻¹ * (n * c * n⁻¹) * n := by group
      _ = 1 := by rw [h1]; group)
  have heq := zpowers_eq_of_mem_of_ne_one (hexp d hdA) hnc hnc1
  have hdn : n⁻¹ * d * n ∈ Subgroup.zpowers c := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (heq ▸ Subgroup.mem_zpowers d :
      d ∈ Subgroup.zpowers (n * c * n⁻¹))
    rw [← hk, conj_zpow, show n⁻¹ * (n * c ^ k * n⁻¹) * n = c ^ k by group]
    exact Subgroup.zpow_mem_zpowers c k
  have huc : n⁻¹ * w * c * (n⁻¹ * w)⁻¹ ∈ Subgroup.zpowers c := by
    rw [show n⁻¹ * w * c * (n⁻¹ * w)⁻¹ = n⁻¹⁻¹⁻¹ * (w * c * w⁻¹) * n⁻¹⁻¹ by group, inv_inv]
    exact conj_mem_zpowers_of_mem (by rwa [inv_inv]) hwc
  have huW : n⁻¹ * w ∈ Subgroup.normalizer (A : Set G) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ hnW) hwW
  have hu := Item116Fusion.conj_mem_of_mem_normalizer_zpowers h hdL hdc huW
    (mem_normalizer_zpowers_of_conj_mem huc) a h.a_mem
  have hwa' : w⁻¹ * a * w = a := by
    calc w⁻¹ * a * w = w⁻¹ * (w * a * w⁻¹) * w := by rw [hwa]
      _ = a := by group
  have hua : (n⁻¹ * w)⁻¹ * a * (n⁻¹ * w) = a⁻¹ := by
    calc (n⁻¹ * w)⁻¹ * a * (n⁻¹ * w) = w⁻¹ * (n * a * n⁻¹) * w := by group
      _ = (w⁻¹ * a * w)⁻¹ := by rw [hna]; group
      _ = a⁻¹ := by rw [hwa']
  rw [hua] at hu
  apply haB
  have ha3 := hexp a h.a_mem
  have hai : a⁻¹ = a ^ 2 := inv_eq_of_mul_eq_one_right (by rw [← pow_succ', ha3])
  rwa [hai, ← pow_add, show 2 + 2 = 3 + 1 by norm_num, pow_succ, ha3, one_mul] at hu

theorem map_conj_eq_of_mem_normalizer (h45 : Sec4.Item4_5) (h : Sec11Std G A c L a R Y) {d : G}
    (hdL : A ⊓ L = Subgroup.zpowers d) (hdc : d ∉ Subgroup.zpowers c) {g : G}
    (hgH : g ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G))
    (hga : g * a * g⁻¹ ∈ Subgroup.zpowers a) : Y.map (MulAut.conj g).toMonoidHom = Y := by
  have ha3 : a ^ 3 = 1 := h.mem_partTwoF.1.2 a h.a_mem
  have hga1 : g * a * g⁻¹ ≠ 1 := fun h1 => h.a_ne_one (by
    calc a = g⁻¹ * (g * a * g⁻¹) * g := by group
      _ = 1 := by rw [h1]; group)
  have hza := zpowers_eq_of_mem_of_ne_one ha3 hga hga1
  have hgL : L.map (MulAut.conj g).toMonoidHom = L :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (h.normalizer_le_normalizer_L h45 hgH)
  have hK : (sec11K L a).map (MulAut.conj g).toMonoidHom = sec11K L a := by
    rw [map_conj_sec11K, hgL, sec11K, sec11K, centralizer_eq_of_zpowers_eq hza]
  have hYg : Y.map (MulAut.conj g).toMonoidHom ∈ thetaComponentsAt 3 a := by
    have h1 := map_mem_thetaComponentsAt (MulAut.conj g) h.mem_thetaComponentsAt_Y
    rwa [MulAut.conj_apply, thetaComponentsAt_eq_of_zpowers_eq hza] at h1
  have hdK := mem_sec11K_d h45 h hdL hdc
  have hd1 : d ≠ 1 := fun h1 => hdc (by rw [h1]; exact Subgroup.one_mem _)
  have hK1 : sec11K L a ≠ ⊥ := fun hK0 => hd1 (by rwa [hK0, Subgroup.mem_bot] at hdK)
  have hKYg : sec11K L a ≤ Y.map (MulAut.conj g).toMonoidHom :=
    calc sec11K L a = (sec11K L a).map (MulAut.conj g).toMonoidHom := hK.symm
      _ ≤ Y.map (MulAut.conj g).toMonoidHom := Subgroup.map_mono h.sec11K_le
  exact Sec6.eq_of_mem_thetaComponentsIn_of_le hYg h.mem_thetaComponentsAt_Y
    (PartOne.EmbeddingFixedResidual.isPerfect_inSubgroup_perfectResidual _) hK1 hKYg h.sec11K_le

theorem exists_inverting_fixing (h : Sec11Std G A c L a R Y) {d : G}
    (hdL : A ⊓ L = Subgroup.zpowers d)
    (hWB : Subgroup.normalizer (A : Set G) ≤
      Subgroup.normalizer ((Subgroup.closure {c, d} : Subgroup G) : Set G))
    (hirr : Sec21.IsIrreducibleOn
      (Sec4.autIn (Subgroup.normalizer (A : Set G)) (Subgroup.closure {c, d})))
    (hdc : d ∉ Subgroup.zpowers c) :
    ∃ m ∈ Subgroup.normalizer (A : Set G), m * c * m⁻¹ = c ∧ m * d * m⁻¹ = d⁻¹ ∧
      m * a * m⁻¹ = a := by
  have hAe := h.mem_partTwoF.1
  have hcomm : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u := fun u hu v hv =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
  set B := Subgroup.closure ({c, d} : Set G) with hB
  have hdA : d ∈ A := (show d ∈ A ⊓ L by rw [hdL]; exact Subgroup.mem_zpowers d).1
  have hBA : B ≤ A := by
    rw [hB, Subgroup.closure_le]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · exact h.mem_A
    · exact hdA
  obtain ⟨l, ⟨hlL, hlW⟩, hld⟩ := Item116Fusion.exists_inverting h hdL hdc
  have hlc := conj_eq_of_mem_inf_normalizer h.toHyp91 hlL hlW
  have hlc' : l⁻¹ * c * l⁻¹⁻¹ = c := by
    calc l⁻¹ * c * l⁻¹⁻¹ = l⁻¹ * (l * c * l⁻¹) * l := by rw [inv_inv, hlc]
      _ = c := by group
  have hχ := Item116Fusion.conj_mem_of_mem_normalizer_zpowers h hdL hdc
    (Subgroup.inv_mem _ hlW) (mem_normalizer_zpowers_of_conj_eq hlc') a h.a_mem
  rw [inv_inv] at hχ
  set b := a⁻¹ * (l * a * l⁻¹) with hbdef
  obtain ⟨t, htW, htB, hta⟩ :=
    Item116Fusion.exists_transvection_eq h hdL hWB hirr hdc b⁻¹ (B.inv_mem hχ)
  have hcB : c ∈ B := Subgroup.subset_closure (by simp)
  have hdB : d ∈ B := Subgroup.subset_closure (by simp)
  refine ⟨t * l, Subgroup.mul_mem _ htW hlW, ?_, ?_, ?_⟩
  · rw [show t * l * c * (t * l)⁻¹ = t * (l * c * l⁻¹) * t⁻¹ by group, hlc, htB c hcB]
  · rw [show t * l * d * (t * l)⁻¹ = t * (l * d * l⁻¹) * t⁻¹ by group, hld,
      htB _ (B.inv_mem hdB)]
  · have hla : l * a * l⁻¹ = a * b := by rw [hbdef]; group
    rw [show t * l * a * (t * l)⁻¹ = t * (l * a * l⁻¹) * t⁻¹ by group, hla,
      show t * (a * b) * t⁻¹ = (t * a * t⁻¹) * (t * b * t⁻¹) by group, hta, htB b hχ]
    group

theorem not_mem_sectionCentralizer (h45 : Sec4.Item4_5) (h : Sec11Std G A c L a R Y) {d : G}
    (hdL : A ⊓ L = Subgroup.zpowers d) (hdc : d ∉ Subgroup.zpowers c) :
    d ∉ Late.sectionCentralizer A Y (inSubgroup (aschbacherSolvableCore 3) Y) := by
  rintro ⟨-, hdY⟩
  have hA : A = Subgroup.closure {c, a, d} := by
    rw [← Item116Fusion.closure_cda_eq h hdL hdc, Set.pair_comm d a]
  have haB : a ∉ Subgroup.closure ({c, d} : Set G) := fun ha =>
    Item116Fusion.not_mem_innerPreimage h (Item116Fusion.closure_le_innerPreimage h hdL ha)
  obtain ⟨hxN, hx3, hZ, hQ, hdK⟩ := basic_facts_of_conj h45 h hdL hA h.a_mem haB
  have hd1 : d ≠ 1 := fun h1 => hdc (by rw [h1]; exact Subgroup.one_mem _)
  have hdA : d ∈ A := (show d ∈ A ⊓ L by rw [hdL]; exact Subgroup.mem_zpowers d).1
  have hd3 : d ^ 3 = 1 := h.mem_partTwoF.1.2 d hdA
  set N₀ : Subgroup (sec11K L a) :=
    (inSubgroup (aschbacherSolvableCore 3) Y).comap (sec11K L a).subtype with hN₀
  have hN₀n : N₀.Normal := by
    constructor
    intro u hu k
    have hkY : (k : G) ∈ Y := h.sec11K_le k.2
    exact (Subgroup.mem_normalizer_iff.mp
      (Sec6.normalizer_le_normalizer_theta Y (Subgroup.le_normalizer hkY)) _).mp hu
  have hθs : Group.IsSolvable (inSubgroup (aschbacherSolvableCore 3) Y) := by
    have := (solvable_prime_complement_core_characterization (H := Y) Nat.prime_three).1
    exact Group.isSolvable_of_surjective (f := ((aschbacherSolvableCore 3 Y).equivMapOfInjective
      Y.subtype Y.subtype_injective).toMonoidHom) (MulEquiv.surjective _)
  have hN₀s : Group.IsSolvable N₀ :=
    Group.isSolvable_of_isSolvable_injective
      (f := ((sec11K L a).subtype.comp N₀.subtype).codRestrict
        (inSubgroup (aschbacherSolvableCore 3) Y) fun u => u.2)
      (fun u v huv => by
        have h' := congrArg (fun z : inSubgroup (aschbacherSolvableCore 3) Y => (z : G)) huv
        exact Subtype.ext (Subtype.ext h'))
  have hker := le_ker_kMap_of_normal_solvable hxN hx3 hQ hZ N₀ hN₀s
  set d' : sec11K L a := ⟨d, hdK⟩ with hd'
  have h1 : kMap L a d' = 1 := by
    refine kMap_eq_one_of_commute hxN hx3 hQ hZ d' fun k' => ?_
    have hmem : d' * k' * d'⁻¹ * k'⁻¹ ∈ N₀ := hdY _ (h.sec11K_le k'.2)
    have h2 := hker hmem
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv] at h2
    calc kMap L a d' * kMap L a k' =
        (kMap L a d' * kMap L a k' * (kMap L a d')⁻¹ * (kMap L a k')⁻¹) *
          (kMap L a k' * kMap L a d') := by group
      _ = kMap L a k' * kMap L a d' := by rw [h2, one_mul]
  have h2 : (⟨d, sec11K_le L a hdK⟩ : L) ∈ aschbacherSolvableCore 3 L := by
    have h3 : QuotientGroup.mk' (aschbacherSolvableCore 3 L)
        (Subgroup.inclusion (sec11K_le L a) d') = 1 := h1
    rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h3
  have h4 := eq_one_of_mem_theta_of_pow_eq_one h2 (k := 1)
    (Subtype.ext (by simpa using hd3))
  exact hd1 (congrArg Subtype.val h4)

theorem sectionCentralizer_eq_zpowers (h45 : Sec4.Item4_5) (h : Sec11Std G A c L a R Y) {d : G}
    (hdL : A ⊓ L = Subgroup.zpowers d)
    (hWB : Subgroup.normalizer (A : Set G) ≤
      Subgroup.normalizer ((Subgroup.closure {c, d} : Subgroup G) : Set G))
    (hirr : Sec21.IsIrreducibleOn
      (Sec4.autIn (Subgroup.normalizer (A : Set G)) (Subgroup.closure {c, d})))
    (hdc : d ∉ Subgroup.zpowers c) {n : G} (hnW : n ∈ Subgroup.normalizer (A : Set G))
    (hnc : n * c * n⁻¹ ∈ Subgroup.zpowers d) (hYn : Y.map (MulAut.conj n).toMonoidHom = Y) :
    Late.sectionCentralizer A Y (inSubgroup (aschbacherSolvableCore 3) Y) =
      (Subgroup.zpowers a : Set G) := by
  have hAe := h.mem_partTwoF.1
  have hexp : ∀ u ∈ A, u ^ 3 = 1 := hAe.2
  have hcomm : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u := fun u hu v hv =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
  have hdA : d ∈ A := (show d ∈ A ⊓ L by rw [hdL]; exact Subgroup.mem_zpowers d).1
  have hAY : A ≤ Subgroup.normalizer (Y : Set G) :=
    Sec6.le_normalizer_of_mem_thetaComponentsAt h45 h.toTheoremFourHyp hAe h.a_mem h.a_ne_one Y
      h.mem_thetaComponentsAt_Y
  have hAθ : A ≤ Subgroup.normalizer (inSubgroup (aschbacherSolvableCore 3) Y : Set G) :=
    hAY.trans (Sec6.normalizer_le_normalizer_theta Y)
  set S := sectionCentralizerSubgroup A Y (inSubgroup (aschbacherSolvableCore 3) Y) hAY hAθ
    with hS
  set B := Subgroup.closure ({c, d} : Set G) with hB
  obtain ⟨m, hmW, hmc, hmd, hma⟩ := exists_inverting_fixing h hdL hWB hirr hdc
  have hmY : Y.map (MulAut.conj m).toMonoidHom = Y :=
    map_conj_eq_of_mem_normalizer h45 h hdL hdc (mem_normalizer_zpowers_of_conj_eq hmc)
      (by rw [hma]; exact Subgroup.mem_zpowers a)
  have hinv : ∀ g ∈ Subgroup.normalizer (A : Set G), Y.map (MulAut.conj g).toMonoidHom = Y →
      ∀ x ∈ S ⊓ B, g * x * g⁻¹ ∈ S ⊓ B := by
    intro g hgA hgY x hx
    exact ⟨conj_mem_sectionCentralizer hgA (Subgroup.mem_normalizer_iff_map_conj_eq.mpr hgY) hx.1,
      (Subgroup.mem_normalizer_iff.mp (hWB hgA) x).mp hx.2⟩
  have hX : S ⊓ B = ⊥ :=
    eq_bot_of_invariant (hcomm c h.mem_A d hdA) (hexp d hdA) hdc inf_le_right
      (fun hd => not_mem_sectionCentralizer h45 h hdL hdc hd.1) hmc hmd (hinv m hmW hmY) hnc
      (hinv n hnW hYn)
  have hYa := Sec6.le_centralizer_of_mem_thetaComponentsAt h.mem_thetaComponentsAt_Y
  have hak : ∀ k : ℤ, a ^ k ∈ S := by
    intro k
    refine ⟨A.zpow_mem h.a_mem k, fun y hy => ?_⟩
    have hya : y * a = a * y := Subgroup.mem_centralizer_singleton_iff.mp (hYa hy)
    rw [(Commute.zpow_left (hya.symm : Commute a y) k).eq, mul_inv_cancel_right,
      mul_inv_cancel]
    exact Subgroup.one_mem _
  ext x
  constructor
  · intro hx
    obtain ⟨b, hb, k, -, rfl⟩ := Item116Fusion.exists_mem_closure_mul_pow h hdL hdc hx.1
    have hbS : b ∈ S := by
      have := S.mul_mem (show b * a ^ k ∈ S from hx) (S.inv_mem (hak k))
      rwa [zpow_natCast, mul_inv_cancel_right] at this
    have hb1 : b = 1 := by
      have : b ∈ S ⊓ B := ⟨hbS, hb⟩
      rwa [hX, Subgroup.mem_bot] at this
    rw [hb1, one_mul, SetLike.mem_coe]
    exact Subgroup.npow_mem_zpowers a k
  · intro hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact hak k

end Certified

end TheoremO

section Main


@[expose] def Item116P2bCore : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G)
    (R Y : Subgroup G), Sec11Std G A c L a R Y → ∀ d : G, A ⊓ L = Subgroup.zpowers d →
      Subgroup.normalizer (A : Set G) ≤
          Subgroup.normalizer ((Subgroup.closure {c, d} : Subgroup G) : Set G) →
        Sec21.IsIrreducibleOn
            (Sec4.autIn (Subgroup.normalizer (A : Set G)) (Subgroup.closure {c, d})) →
          CFSG.ABGLocalTools.IsSylowOf 3 R ⊤ → d ∉ Subgroup.zpowers c →
          (∀ w ∈ Subgroup.normalizer (A : Set G),
            (w * c * w⁻¹ ∈ Subgroup.zpowers c ∧ w * d * w⁻¹ ∈ Subgroup.zpowers d) ∨
            (w * c * w⁻¹ ∈ Subgroup.zpowers d ∧ w * d * w⁻¹ ∈ Subgroup.zpowers c)) →
          ∀ n ∈ Subgroup.normalizer (A : Set G), n * c * n⁻¹ ∈ Subgroup.zpowers d →
            n * d * n⁻¹ ∈ Subgroup.zpowers c → n * a * n⁻¹ = a⁻¹ →
            Y.map (MulAut.conj n).toMonoidHom = Y →
            d ∈ sec11K L a → c ∈ Y →
            Late.sectionCentralizer A Y (inSubgroup (aschbacherSolvableCore 3) Y) =
              (Subgroup.zpowers a : Set G) →
            (∀ w ∈ Subgroup.normalizer (A : Set G), w * a * w⁻¹ = a →
              w * c * w⁻¹ ∈ Subgroup.zpowers c ∧ w * d * w⁻¹ ∈ Subgroup.zpowers d) →
              False

theorem item116P2b_of_core (h45 : Sec4.Item4_5) (hcore : Item116P2bCore) : Item116P2b := by
  intro G _ _ A c L a R Y h d hdL hWB hirr hRG hdc hD8 n hnW hnc hnd hna hYn
  have hcY : c ∈ Y := by
    have := TheoremO.mem_map_conj_of_conj_mem_zpowers h45 h hdL hdc hnd
    rwa [hYn] at this
  exact hcore G A c L a R Y h d hdL hWB hirr hRG hdc hD8 n hnW hnc hnd hna hYn
    (TheoremO.mem_sec11K_d h45 h hdL hdc) hcY
    (TheoremO.sectionCentralizer_eq_zpowers h45 h hdL hWB hirr hdc hnW hnc hYn)
    (fun w hwW hwa => TheoremO.conj_mem_zpowers_of_conj_eq h hdL hdc hD8 hnW hnc hna hwW hwa)

theorem item116FusionE9_of_even_of_core (hEven : Item116FusionE9Even)
    (hcore : Item116P2bCore) (h45 : Sec4.Item4_5) : Item116FusionE9 :=
  item116FusionE9_of_even hEven (item116P2b_of_core h45 hcore) h45

end Main

end CFSG.RankThree.PartTwo.Sec11
