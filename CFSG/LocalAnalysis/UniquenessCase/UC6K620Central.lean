module

public import CFSG.RankThree.PartOne.KC.EvenCenterSection
import CFSG.GroupTheory.Fitting.LayerTopBot

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open Subgroup CFSG CFSG.RankThree.Coprime
open scoped IsMulCommutative commutatorElement

theorem le_center_of_normal_pRank_le {K : Type*} [Group K] [Finite K] [Group.IsPerfect K]
    (m : ℕ) (C : Subgroup K) [C.Normal] (hCsolv : Group.IsSolvable C) (hCodd : Odd (Nat.card C))
    (hsimple : IsSimpleGroup (K ⧸ C)) (U : Subgroup (K ⧸ C)) (hU : IsElementaryAbelian 2 U)
    (hUcard : Nat.card U = 2 ^ (m + 1)) {r : ℕ} [hr : Fact r.Prime] (hr2 : r ≠ 2) (R : Subgroup K)
    [R.Normal] (hR : IsPGroup r R) (hRrank : CFSG.Open.pRank r R ≤ m) : R ≤ center K := by
  classical
  rcases subsingleton_or_nontrivial R with hRs | hRnt
  · intro x hx
    have hx1 : x = 1 := congrArg Subtype.val (Subsingleton.elim (⟨x, hx⟩ : R) 1)
    rw [hx1]
    exact one_mem _
  obtain ⟨D, hDchar, -, hDcomm, hDexp, hDfix⟩ :=
    CFSG.SectionRank.Ccomm.odd_critical_exponent_subgroup hr2 hR
  set D' : Subgroup K := D.map R.subtype with hD'
  have hD'n : D'.Normal := inferInstance
  set K₀ := centralizer (D' : Set K) with hK₀
  have hK₀n : K₀.Normal := inferInstance
  have : (K₀.map (QuotientGroup.mk' C)).Normal :=
    hK₀n.map (QuotientGroup.mk' C) (QuotientGroup.mk'_surjective C)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (K₀.map (QuotientGroup.mk' C)) with hbot | htop
  ·
    exfalso
    have hK₀C : K₀ ≤ C := by
      intro k hk
      have hmem : QuotientGroup.mk' C k ∈ K₀.map (QuotientGroup.mk' C) := ⟨k, hk, rfl⟩
      rw [hbot, Subgroup.mem_bot] at hmem
      exact (QuotientGroup.eq_one_iff k).mp hmem
    obtain ⟨V, hV, hVcard, hVC⟩ := exists_elementary_two_lift C hCodd U hU hUcard
    have := hV
    have hD'exp : ∀ x : D', x ^ r = 1 := by
      intro x
      obtain ⟨x', hx', hxx⟩ := Subgroup.mem_map.mp x.2
      apply Subtype.ext
      rw [Subgroup.coe_pow, ← hxx, ← map_pow, hDexp x' hx', map_one, Subgroup.coe_one]
    have hD'cz : ∀ x y z : D', ⁅x, y⁆ * z = z * ⁅x, y⁆ := by
      intro x y z
      obtain ⟨x', hx', hxx⟩ := Subgroup.mem_map.mp x.2
      obtain ⟨y', hy', hyy⟩ := Subgroup.mem_map.mp y.2
      obtain ⟨z', hz', hzz⟩ := Subgroup.mem_map.mp z.2
      have hc : ⁅x', y'⁆ ∈ centralizer (D : Set R) :=
        (hDcomm (Subgroup.commutator_mem_commutator hx' (mem_top y'))).2
      have hcz : z' * ⁅x', y'⁆ = ⁅x', y'⁆ * z' := mem_centralizer_iff.mp hc z' hz'
      have h1 := congrArg R.subtype hcz
      simp only [map_mul, commutatorElement_def, map_inv] at h1
      apply Subtype.ext
      simp only [Subgroup.coe_mul, commutatorElement_def, Subgroup.coe_inv]
      rw [← hxx, ← hyy, ← hzz]
      exact h1.symm
    let act : MulDistribMulAction V D' :=
      MulDistribMulAction.compHom D' ((MulAut.conjNormal (H := D')).comp V.subtype)
    have hsmul : ∀ (v : V) (d : D'), ((v • d : D') : K) = (v : K) * d * (v : K)⁻¹ :=
      fun v d => MulAut.conjNormal_apply (v : K) d
    have hfaith : ∀ a : V, (∀ d : D', a • d = d) → a = 1 := by
      intro a hfix
      have hK₀mem : (a : K) ∈ K₀ := by
        rw [mem_centralizer_iff]
        intro x hx
        have h1 := congrArg Subtype.val (hfix ⟨x, hx⟩)
        rw [hsmul] at h1
        calc x * (a : K) = (a : K) * x * (a : K)⁻¹ * (a : K) := by rw [h1]
          _ = (a : K) * x := by group
      exact Subtype.ext (Subgroup.disjoint_def.mp hVC a.2 (hK₀C hK₀mem))
    have hcommV : ∀ a b : V, a * b = b * a := fun a b => mul_comm' a b
    have hsqV : ∀ a : V, a ^ 2 = 1 := fun a => Subtype.ext
      (by simpa using elemPow_eq_one_of_isElementaryAbelian (a : K) a.2)
    have hbound :=
      CFSG.RankThree.GroupTheory.SteinbergBK.elementary_two_action_class_two_global_odd_rank_bound
        hr.out hr2 hD'exp
        (CFSG.RankThree.PartOne.commutator_le_center_of_commutator_central hD'cz) hcommV hsqV
        hfaith
    have hV2 : m + 1 ≤ CFSG.Assembly.pRank 2 (⊤ : Subgroup V) :=
      CFSG.SectionRank.le_pRank_of_injective (G := V) (p := 2) Nat.one_lt_two hcommV hsqV hVcard
        (MonoidHom.id V) Function.injective_id (H := ⊤) (by simp)
    have hDr : CFSG.Assembly.pRank r (⊤ : Subgroup D') ≤ m :=
      calc CFSG.Assembly.pRank r (⊤ : Subgroup D') = CFSG.Open.pRank r (⊤ : Subgroup D') := rfl
        _ ≤ CFSG.Open.pRank r ((⊤ : Subgroup D').map D'.subtype) :=
            CFSG.SectionRank.pRank_le_map hr.out.one_lt D'.subtype D'.subtype_injective ⊤
        _ ≤ CFSG.Open.pRank r R :=
            CFSG.SectionRank.pRank_mono hr.out.one_lt
              ((Subgroup.map_subtype_le _).trans (Subgroup.map_subtype_le D))
        _ ≤ m := hRrank
    omega
  ·
    have hsurj : Function.Surjective ((QuotientGroup.mk' K₀).comp C.subtype) := by
      intro q
      obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective K₀ q
      have hk : QuotientGroup.mk' C k ∈ K₀.map (QuotientGroup.mk' C) := by
        rw [htop]
        exact mem_top _
      obtain ⟨k₀, hk₀, hkk⟩ := hk
      refine ⟨⟨k₀⁻¹ * k, QuotientGroup.eq.mp hkk⟩, ?_⟩
      change QuotientGroup.mk' K₀ (k₀⁻¹ * k) = QuotientGroup.mk' K₀ k
      have hk₀1 : QuotientGroup.mk' K₀ k₀ = 1 := (QuotientGroup.eq_one_iff k₀).mpr hk₀
      rw [map_mul, map_inv, hk₀1, inv_one, one_mul]
    have hKK₀ : ∀ k : K, k ∈ K₀ := by
      have : Group.IsSolvable (K ⧸ K₀) := Group.isSolvable_of_surjective hsurj
      have hsolv : Group.IsSolvable (QuotientGroup.mk' K₀).range := by
        rw [MonoidHom.range_eq_top_of_surjective _ (QuotientGroup.mk'_surjective K₀)]
        infer_instance
      intro k
      exact (QuotientGroup.eq_one_iff k).mp (eq_one_of_isSolvable_range _ hsolv k)
    let g : K →* MulAut R := MulAut.conjNormal
    have hrange : g.range ≤ fixingSubgroup (MulAut R) (D : Set R) := by
      rintro _ ⟨k, rfl⟩
      rw [mem_fixingSubgroup_iff]
      intro d hd
      apply Subtype.ext
      change k * (d : K) * k⁻¹ = d
      have h1 := mem_centralizer_iff.mp (hKK₀ k) (d : K) ⟨d, hd, rfl⟩
      rw [← h1, mul_inv_cancel_right]
    have hgp : IsPGroup r g.range := hDfix.to_le hrange
    have hgs : Group.IsSolvable g.range := by
      have := hgp.isNilpotent
      infer_instance
    intro x hx
    rw [mem_center_iff]
    intro k
    have h1 := congrArg (fun φ : MulAut R => ((φ ⟨x, hx⟩ : R) : K))
      (eq_one_of_isSolvable_range g hgs k)
    simp only [g, MulAut.conjNormal_apply, MulAut.one_apply] at h1
    calc k * x = k * x * k⁻¹ * k := by group
      _ = x * k := by rw [h1]

theorem le_center_of_sylow_pRank_le {K : Type*} [Group K] [Finite K] [Group.IsPerfect K] (m : ℕ)
    (C : Subgroup K) [C.Normal] (hCnil : Group.IsNilpotent C) (hCodd : Odd (Nat.card C))
    (hCsyl : ∀ (q : ℕ) [Fact q.Prime] (Q : Sylow q C), ((Q : Subgroup C).map C.subtype).Normal)
    (hCrank : ∀ r : ℕ, r.Prime → r ≠ 2 → CFSG.Open.pRank r C ≤ m)
    (hsimple : IsSimpleGroup (K ⧸ C)) (U : Subgroup (K ⧸ C)) (hU : IsElementaryAbelian 2 U)
    (hUcard : Nat.card U = 2 ^ (m + 1)) : C ≤ center K := by
  have hCsolv : Group.IsSolvable C := by
    have := hCnil
    infer_instance
  have hC : C = (⨆ p ∈ (Nat.card C).primeFactors, ((default : Sylow p C) : Subgroup C)).map
      C.subtype := by
    rw [Sylow.iSup_sylow_eq_top, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rw [hC, Subgroup.map_le_iff_le_comap]
  refine iSup₂_le fun p hp => ?_
  rw [← Subgroup.map_le_iff_le_comap]
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have : Fact p.Prime := ⟨hpp⟩
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr hCodd)
      (even_iff_two_dvd.mpr (Nat.dvd_of_mem_primeFactors hp))
  have := hCsyl p default
  exact le_center_of_normal_pRank_le m C hCsolv hCodd hsimple U hU hUcard hp2 _
    ((default : Sylow p C).isPGroup'.map _)
    ((CFSG.SectionRank.pRank_mono hpp.one_lt (Subgroup.map_subtype_le _)).trans
      (hCrank p hpp hp2))

theorem exists_central_cover_of_odd_kernel {X : Type*} [Group X] [Finite X] (m : ℕ)
    (Y : Subgroup X) [Y.Normal] (hYodd : Odd (Nat.card Y))
    (hYrank : ∀ r : ℕ, r.Prime → r ≠ 2 → CFSG.Open.pRank r Y ≤ m) [IsSimpleGroup (X ⧸ Y)]
    (hnc : ∃ a b : X ⧸ Y, a * b ≠ b * a)
    (hU : ∃ U : Subgroup (X ⧸ Y), IsElementaryAbelian 2 U ∧ Nat.card U = 2 ^ (m + 1)) :
    ∃ K : Subgroup X, Function.Surjective ((QuotientGroup.mk' Y).comp K.subtype) ∧
      ((QuotientGroup.mk' Y).comp K.subtype).ker ≤ center K ∧
      Odd (Nat.card ((QuotientGroup.mk' Y).comp K.subtype).ker) := by
  classical
  obtain ⟨U, hUel, hUcard⟩ := hU
  have hZ : center (X ⧸ Y) = ⊥ := by
    obtain ⟨a, b, hab⟩ := hnc
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center (X ⧸ Y)) with h | h
    · exact h
    · exact absurd (mem_center_iff.1 (h ▸ mem_top b) a) hab
  obtain ⟨K, -, hKmin⟩ := Finite.exists_le_minimal
    (p := fun K : Subgroup X => K.map (QuotientGroup.mk' Y) = ⊤) (a := ⊤)
    (by rw [Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective Y)])
  set πK : K →* X ⧸ Y := (QuotientGroup.mk' Y).comp K.subtype with hπK
  have hπKs : Function.Surjective πK := by
    intro x
    have hx : x ∈ K.map (QuotientGroup.mk' Y) := by
      rw [hKmin.prop]
      exact mem_top x
    obtain ⟨k, hk, rfl⟩ := hx
    exact ⟨⟨k, hk⟩, rfl⟩
  have hmin : ∀ L : Subgroup K, L ≠ ⊤ → L.map πK ≠ ⊤ := by
    intro L hL hLmap
    apply hL
    have h1 : (L.map K.subtype).map (QuotientGroup.mk' Y) = ⊤ := by
      rw [Subgroup.map_map]
      exact hLmap
    have h2 := hKmin.le_of_le h1 (Subgroup.map_subtype_le L)
    rw [eq_top_iff]
    intro y _
    obtain ⟨y', hy', hyy⟩ := h2 y.2
    rwa [show y' = y from Subtype.ext hyy] at hy'
  obtain ⟨hKperf, hCn, hCnil, hCsyl, -, -, -, -, -⟩ :=
    CFSG.SectionRank.minimal_semisimple_cover (CFSG.WholeGroup.layer_eq_top_of_isSimpleGroup hnc)
      πK hπKs hmin
  set C : Subgroup K := (center (X ⧸ Y)).comap πK with hC
  have hCker : C = πK.ker := by
    rw [hC, hZ]
    exact πK.comap_bot
  have hCmap : C.map K.subtype ≤ Y := by
    rintro _ ⟨x, hx, rfl⟩
    have hx' : πK x = 1 := by
      rw [← MonoidHom.mem_ker, ← hCker]
      exact hx
    exact (QuotientGroup.eq_one_iff (x : X)).1 hx'
  have hCodd : Odd (Nat.card C) := by
    rw [← Subgroup.card_map_of_injective K.subtype_injective]
    exact Odd.of_dvd_nat hYodd (Subgroup.card_dvd_of_le hCmap)
  have hCrank : ∀ r : ℕ, r.Prime → r ≠ 2 → CFSG.Open.pRank r C ≤ m := fun r hr hr2 =>
    ((CFSG.SectionRank.pRank_le_map hr.one_lt K.subtype K.subtype_injective C).trans
      (CFSG.SectionRank.pRank_mono hr.one_lt hCmap)).trans (hYrank r hr hr2)
  set iso : K ⧸ C ≃* X ⧸ Y := (QuotientGroup.quotientMulEquivOfEq hCker).trans
    (QuotientGroup.quotientKerEquivOfSurjective πK hπKs) with hiso
  have hsimple : IsSimpleGroup (K ⧸ C) := iso.isSimpleGroup
  obtain ⟨hU', hU'card⟩ := isElementaryAbelian_map_mulEquiv iso.symm hUel
  have : Group.IsPerfect K := hKperf
  have hCcen : C ≤ center K := le_center_of_sylow_pRank_le m C hCnil hCodd hCsyl hCrank hsimple
    (U.map iso.symm.toMonoidHom) hU' (hU'card.trans hUcard)
  refine ⟨K, hπKs, ?_, ?_⟩
  · rw [← hCker]
    exact hCcen
  · rw [← hCker]
    exact hCodd

end CFSG.LocalAnalysis.UniquenessCase.UCK
