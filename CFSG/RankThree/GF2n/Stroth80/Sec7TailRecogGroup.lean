module

public import CFSG.RankThree.GF2n.Stroth80.Sec7TailCoprimeAdjust
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailLieStmts
public import CFSG.GroupTheory.PerfectResidualNodes

public section

namespace CFSG.RankThree.GF2n.Stroth80

open Subgroup CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

theorem exists_perfect_sup_eq {Y : Type*} [Group Y] [Finite Y] {R N : Subgroup Y} (hNR : N ≤ R)
    [(N.subgroupOf R).Normal] (hperf : commutator (↥R ⧸ N.subgroupOf R) = ⊤) :
    ∃ E : Subgroup Y, E ≤ R ∧ commutator ↥E = ⊤ ∧ E ⊔ N = R ∧
      ∀ k ∈ normalizer (R : Set Y), k ∈ normalizer (E : Set Y) := by
  have hchar : (CFSG.perfectResidual ↥R).Characteristic :=
    (CFSG.perfect_residual_characterization (G := ↥R)).2.1
  have hP : Group.IsPerfect (CFSG.perfectResidual ↥R) :=
    (CFSG.perfect_residual_characterization (G := ↥R)).2.2.1
  have hQ : Group.IsPerfect (↥R ⧸ N.subgroupOf R) := Group.isPerfect_def.mpr hperf
  refine ⟨(CFSG.perfectResidual ↥R).map R.subtype, Subgroup.map_subtype_le _, ?_, ?_, ?_⟩
  · exact (Group.IsPerfect.map R.subtype (H := CFSG.perfectResidual ↥R)).commutator_eq_top
  · apply le_antisymm (sup_le (Subgroup.map_subtype_le (CFSG.perfectResidual ↥R)) hNR)
    intro x hx
    have hsurj : Function.Surjective (QuotientGroup.mk' (N.subgroupOf R)) :=
      QuotientGroup.mk'_surjective (N.subgroupOf R)
    have hmap : Subgroup.map (QuotientGroup.mk' (N.subgroupOf R)) (CFSG.perfectResidual ↥R) = ⊤ :=
      CFSG.RankThreeCoreUniqueness.Helpers.finite_perfectResidual_surjects_to_perfect_image
        (G := ↥R) (Image := ↥R ⧸ N.subgroupOf R) (QuotientGroup.mk' (N.subgroupOf R)) hsurj
    have hmem : QuotientGroup.mk' (N.subgroupOf R) (⟨x, hx⟩ : ↥R) ∈
        Subgroup.map (QuotientGroup.mk' (N.subgroupOf R)) (CFSG.perfectResidual ↥R) := by
      rw [hmap]
      exact Subgroup.mem_top _
    obtain ⟨e, he, hpe⟩ := Subgroup.mem_map.mp hmem
    simp only [QuotientGroup.mk'_apply, QuotientGroup.eq] at hpe
    have hn : (e : Y)⁻¹ * x ∈ N := by
      simpa using Subgroup.mem_subgroupOf.mp hpe
    have hE : (e : Y) ∈ (CFSG.perfectResidual ↥R).map R.subtype :=
      Subgroup.mem_map_of_mem R.subtype he
    have hprod : (e : Y) * ((e : Y)⁻¹ * x) ∈ (CFSG.perfectResidual ↥R).map R.subtype ⊔ N :=
      mul_mem (Subgroup.mem_sup_left hE) (Subgroup.mem_sup_right hn)
    rwa [mul_inv_cancel_left] at hprod
  · intro k hk
    exact CFSG.RankThreeCoreUniqueness.Helpers.normalizer_le_normalizer_characteristic_map
      R (CFSG.perfectResidual ↥R) hchar hk

theorem mem_of_orderOf_three {Y : Type*} [Group Y] [Finite Y] {Gs E N : Subgroup Y} [Gs.Normal]
    (hE : E ≤ Gs) (hN2 : IsPGroup 2 N) {y : Y} (hy : orderOf y = 3) (hyEN : y ∈ E ⊔ N) :
    y ∈ Gs := by
  classical
  set π := QuotientGroup.mk' Gs with hπ
  have h1 : π y ∈ (E ⊔ N).map π := Subgroup.mem_map_of_mem _ hyEN
  rw [Subgroup.map_sup] at h1
  have hE1 : E.map π = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨e, he, rfl⟩
    exact Subgroup.mem_bot.mpr ((QuotientGroup.eq_one_iff e).mpr (hE he))
  rw [hE1, bot_sup_eq] at h1
  have hp : IsPGroup 2 ↥(N.map π) := hN2.map π
  obtain ⟨j, hj⟩ := hp ⟨π y, h1⟩
  have hj' : (π y) ^ (2 ^ j) = 1 := by simpa using congrArg Subtype.val hj
  have h3 : (π y) ^ 3 = 1 := by
    rw [← map_pow, ← hy, pow_orderOf_eq_one, map_one]
  have hcop : Nat.Coprime (2 ^ j) 3 := Nat.Coprime.pow_left j (by norm_num)
  have h4 : π y = 1 := (pow_eq_one_iff_of_coprime hcop).mp ⟨hj', h3⟩
  exact (QuotientGroup.eq_one_iff y).mp h4

theorem le_normal_of_coprime_element {Y : Type*} [Group Y] [Finite Y] {Gs N V : Subgroup Y}
    [Gs.Normal] (hN2 : IsPGroup 2 N) {y : Y} (hy : orderOf y = 3)
    (hyN : y ∈ normalizer (N : Set Y)) (hyGs : y ∈ Gs) (hCy : ∀ x ∈ N, y * x = x * y → x ∈ V)
    (hV : V ≤ Gs) : N ≤ Gs := by
  classical
  let φ : ↥N →* Y ⧸ Gs := (QuotientGroup.mk' Gs).comp N.subtype
  have hφ := hom_trivial_of_centralizer hN2 hy hyN hCy φ ?_ ?_
  · intro x hx
    have := hφ ⟨x, hx⟩
    exact (QuotientGroup.eq_one_iff x).mp this
  · intro x x' hx'
    show QuotientGroup.mk' Gs (x' : Y) = QuotientGroup.mk' Gs (x : Y)
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, hx']
    have h1 : (y * (x : Y) * y⁻¹)⁻¹ * (x : Y) = y * ((x : Y)⁻¹ * y⁻¹ * (x : Y)) := by group
    rw [h1]
    refine Gs.mul_mem hyGs ?_
    have := Subgroup.Normal.conj_mem inferInstance y⁻¹ (Gs.inv_mem hyGs) ((x : Y)⁻¹)
    simpa [mul_assoc] using this
  · intro x hx
    exact (QuotientGroup.eq_one_iff (x : Y)).mpr (hV hx)

theorem normalizer_le_normalizer_of_center {Y : Type*} [Group Y] {N V : Subgroup Y}
    (hVN : V ≤ N) (hZN : ∀ x ∈ N, (∀ n ∈ N, x * n = n * x) → x ∈ V)
    (hVc : ∀ v ∈ V, ∀ n ∈ N, v * n = n * v) :
    normalizer (N : Set Y) ≤ normalizer (V : Set Y) := by
  have key : ∀ g ∈ normalizer (N : Set Y), ∀ v ∈ V, g * v * g⁻¹ ∈ V := by
    intro g hg v hv
    have hgN : ∀ h : Y, h ∈ N ↔ g * h * g⁻¹ ∈ N :=
      fun h => Subgroup.mem_normalizer_iff.mp hg h
    refine hZN _ ?_ ?_
    · exact (hgN v).mp (hVN hv)
    · intro n hn
      have hm : g⁻¹ * n * g ∈ N := by
        rw [hgN (g⁻¹ * n * g)]
        have e1 : g * (g⁻¹ * n * g) * g⁻¹ = n := by group
        rw [e1]
        exact hn
      have hc := hVc v hv _ hm
      calc g * v * g⁻¹ * n = g * (v * (g⁻¹ * n * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * n * g) * v) * g⁻¹ := by rw [hc]
        _ = n * (g * v * g⁻¹) := by group
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    exact key g hg h hh
  · intro hh
    have h2 := key g⁻¹ (inv_mem hg) (g * h * g⁻¹) hh
    have e2 : g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ = h := by group
    rw [e2] at h2
    exact h2

theorem inSubgroup_pCore_inf_eq {Y : Type*} [Group Y] [Finite Y] {Gs K N : Subgroup Y} [Gs.Normal]
    (hNGs : N ≤ Gs) (hNK : N ≤ K) (hNn : ∀ k ∈ K, k ∈ normalizer (N : Set Y))
    (hN2 : IsPGroup 2 N)
    (hpc : ∀ P : Subgroup Y, P ≤ K → (∀ k ∈ K, k ∈ normalizer (P : Set Y)) → IsPGroup 2 P →
      P ≤ N) :
    inSubgroup (pCore 2) (K ⊓ Gs) = N := by
  have hNA : N ≤ K ⊓ Gs := le_inf hNK hNGs
  have hconjA : ∀ g ∈ K, ∀ a : ↥(K ⊓ Gs), g * (a : Y) * g⁻¹ ∈ K ⊓ Gs := by
    intro g hg a
    obtain ⟨ha1, ha2⟩ := Subgroup.mem_inf.mp a.2
    exact Subgroup.mem_inf.mpr ⟨K.mul_mem (K.mul_mem hg ha1) (K.inv_mem hg),
      (inferInstance : Gs.Normal).conj_mem _ ha2 g⟩
  have hconj : ∀ g ∈ K, ∃ ψ : ↥(K ⊓ Gs) ≃* ↥(K ⊓ Gs),
      ∀ a : ↥(K ⊓ Gs), (ψ a : Y) = g * (a : Y) * g⁻¹ := by
    intro g hg
    refine ⟨{ toFun := fun a => ⟨g * (a : Y) * g⁻¹, hconjA g hg a⟩
              invFun := fun a => ⟨g⁻¹ * (a : Y) * g⁻¹⁻¹, hconjA g⁻¹ (K.inv_mem hg) a⟩
              left_inv := fun a => Subtype.ext (by simp [mul_assoc])
              right_inv := fun a => Subtype.ext (by simp [mul_assoc])
              map_mul' := fun a b => Subtype.ext (by simp [mul_assoc]) }, fun a => rfl⟩
  have hstab : ∀ g ∈ K, ∀ z ∈ (CFSG.pCore 2 ↥(K ⊓ Gs)).map (K ⊓ Gs).subtype,
      g * z * g⁻¹ ∈ (CFSG.pCore 2 ↥(K ⊓ Gs)).map (K ⊓ Gs).subtype := by
    intro g hg z hz
    obtain ⟨ψ, hψ⟩ := hconj g hg
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hz
    have h1 : ψ y ∈ (CFSG.pCore 2 ↥(K ⊓ Gs)).map ψ.toMonoidHom :=
      Subgroup.mem_map_of_mem ψ.toMonoidHom hy
    rw [CFSG.pCore_map_iso 2 ψ] at h1
    exact Subgroup.mem_map.mpr ⟨ψ y, h1, hψ y⟩
  have hP1K : (CFSG.pCore 2 ↥(K ⊓ Gs)).map (K ⊓ Gs).subtype ≤ K := by
    intro x hx
    obtain ⟨y, _, rfl⟩ := Subgroup.mem_map.mp hx
    exact (Subgroup.mem_inf.mp y.2).1
  have hP1n : ∀ g ∈ K,
      g ∈ normalizer ((CFSG.pCore 2 ↥(K ⊓ Gs)).map (K ⊓ Gs).subtype : Set Y) :=
    fun g hg => Subgroup.mem_normalizer_fintype fun n hn => hstab g hg n hn
  have hP1_2 : IsPGroup 2 ((CFSG.pCore 2 ↥(K ⊓ Gs)).map (K ⊓ Gs).subtype) :=
    IsPGroup.map (CFSG.pCore_isPGroup (p := 2) (G := ↥(K ⊓ Gs))) (K ⊓ Gs).subtype
  have hP1N : (CFSG.pCore 2 ↥(K ⊓ Gs)).map (K ⊓ Gs).subtype ≤ N :=
    hpc _ hP1K hP1n hP1_2
  have hNAn : (N.subgroupOf (K ⊓ Gs)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNA).mpr fun g hg =>
      hNn g (Subgroup.mem_inf.mp hg).1
  have hN1 : IsPGroup 2 ↥(N.subgroupOf (K ⊓ Gs)) :=
    hN2.of_equiv (Subgroup.subgroupOfEquivOfLe hNA).symm
  have hNcore : N.subgroupOf (K ⊓ Gs) ≤ CFSG.pCore 2 ↥(K ⊓ Gs) := le_sSup ⟨hNAn, hN1⟩
  unfold inSubgroup
  apply le_antisymm hP1N
  intro n hn
  have hmem : (⟨n, hNA hn⟩ : ↥(K ⊓ Gs)) ∈ N.subgroupOf (K ⊓ Gs) :=
    Subgroup.mem_subgroupOf.mpr hn
  exact Subgroup.mem_map.mpr ⟨⟨n, hNA hn⟩, hNcore hmem, rfl⟩

theorem inSubgroup_pCore_subgroupOf {Y : Type*} [Group Y] {Gs H : Subgroup Y} (hH : H ≤ Gs) :
    inSubgroup (pCore 2) (H.subgroupOf Gs) = (inSubgroup (pCore 2) H).subgroupOf Gs := by
  unfold inSubgroup
  have hiso := CFSG.pCore_map_iso 2 (Subgroup.subgroupOfEquivOfLe hH)
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    have hy' : Subgroup.subgroupOfEquivOfLe hH y ∈ CFSG.pCore 2 ↥H := by
      rw [← hiso]
      exact Subgroup.mem_map_of_mem (Subgroup.subgroupOfEquivOfLe hH).toMonoidHom hy
    rw [Subgroup.mem_subgroupOf]
    exact Subgroup.mem_map.mpr ⟨Subgroup.subgroupOfEquivOfLe hH y, hy', rfl⟩
  · intro hx
    rw [Subgroup.mem_subgroupOf] at hx
    obtain ⟨z, hz, hzx⟩ := Subgroup.mem_map.mp hx
    have hz' : z ∈ (CFSG.pCore 2 ↥(H.subgroupOf Gs)).map
        (Subgroup.subgroupOfEquivOfLe hH).toMonoidHom := by
      rw [hiso]
      exact hz
    obtain ⟨y, hy, hyz⟩ := Subgroup.mem_map.mp hz'
    refine Subgroup.mem_map.mpr ⟨y, hy, ?_⟩
    apply Subtype.ext
    have h1 : ((Subgroup.subgroupOfEquivOfLe hH y : H) : Y) = (z : Y) :=
      congrArg Subtype.val hyz
    exact h1.trans hzx

theorem nonempty_quot_equiv_subgroupOf {Y : Type*} [Group Y] {Gs R N : Subgroup Y}
    (hRG : R ≤ Gs) (hNR : N ≤ R) [hN : (N.subgroupOf R).Normal] {A : Type*} [Group A]
    (h : Nonempty ((↥R ⧸ N.subgroupOf R) ≃* A)) :
    ∃ _ : ((N.subgroupOf Gs).subgroupOf (R.subgroupOf Gs)).Normal,
      Nonempty ((↥(R.subgroupOf Gs) ⧸ (N.subgroupOf Gs).subgroupOf (R.subgroupOf Gs)) ≃* A) := by
  obtain ⟨φ⟩ := h
  have hK : (N.subgroupOf Gs).subgroupOf (R.subgroupOf Gs)
      = (N.subgroupOf R).comap (Subgroup.subgroupOfEquivOfLe hRG).toMonoidHom := by
    ext x
    exact Iff.rfl
  have hnorm : ((N.subgroupOf Gs).subgroupOf (R.subgroupOf Gs)).Normal := by
    rw [hK]
    exact Subgroup.Normal.comap hN _
  have he : ((N.subgroupOf Gs).subgroupOf (R.subgroupOf Gs)).map
      (Subgroup.subgroupOfEquivOfLe hRG).toMonoidHom = N.subgroupOf R := by
    rw [hK]
    exact Subgroup.map_comap_eq_self_of_surjective
      (f := (Subgroup.subgroupOfEquivOfLe hRG).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hRG).surjective _
  exact ⟨hnorm, ⟨(QuotientGroup.congr _ _ (Subgroup.subgroupOfEquivOfLe hRG) he).trans φ⟩⟩

theorem eq_bot_of_perfect_le_solvable {X : Type*} [Group X] {P S : Subgroup X}
    (hP : commutator ↥P = ⊤) (hPS : P ≤ S) (hS : Group.IsSolvable ↥S) : P = ⊥ := by
  have hPs : Group.IsSolvable ↥P :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hPS)
  obtain ⟨n, hn⟩ := hPs
  have key : ∀ m : ℕ, derivedSeries ↥P (m + 1) = ⊤ := by
    intro m
    induction m with
    | zero => simpa using hP
    | succ m ih => rw [derivedSeries_succ, ih]; exact hP
  have htop : (⊤ : Subgroup ↥P) = ⊥ := by
    cases n with
    | zero => rw [derivedSeries_zero] at hn; exact hn
    | succ m => rw [key m] at hn; exact hn
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  have hmem : (⟨x, hx⟩ : ↥P) ∈ (⊤ : Subgroup ↥P) := Subgroup.mem_top _
  rw [htop, Subgroup.mem_bot] at hmem
  simpa using congrArg Subtype.val hmem

theorem recog_commutator_subgroupOf {Y : Type} [Group Y] {Gs E : Subgroup Y} (hEGs : E ≤ Gs)
    (hE : commutator ↥E = ⊤) : commutator ↥(E.subgroupOf Gs) = ⊤ := by
  have h1 := map_derivedSeries_eq (f := (Subgroup.subgroupOfEquivOfLe hEGs).toMonoidHom)
    (Subgroup.subgroupOfEquivOfLe hEGs).surjective 1
  simp only [derivedSeries_one] at h1
  rw [hE] at h1
  apply Subgroup.map_injective (f := (Subgroup.subgroupOfEquivOfLe hEGs).toMonoidHom)
    (Subgroup.subgroupOfEquivOfLe hEGs).injective
  rw [h1, Subgroup.map_top_of_surjective (Subgroup.subgroupOfEquivOfLe hEGs).toMonoidHom
    (Subgroup.subgroupOfEquivOfLe hEGs).surjective]

theorem recog_isElemAbelian_subgroupOf {Y : Type} [Group Y] {Gs L : Subgroup Y}
    (hLab : IsElemAbelian 2 L) : IsElemAbelian 2 (L.subgroupOf Gs) := by
  have hc : ∀ a b : ↥(L.subgroupOf Gs), a * b = b * a := by
    intro a b
    apply Subtype.ext
    apply Subtype.ext
    have h := congrArg Subtype.val
      (hLab.1.is_comm.comm (⟨((a : ↥Gs) : Y), Subgroup.mem_subgroupOf.mp a.2⟩ : ↥L)
        ⟨((b : ↥Gs) : Y), Subgroup.mem_subgroupOf.mp b.2⟩)
    simpa using h
  unfold IsElemAbelian
  refine ⟨⟨⟨hc⟩⟩, fun x hx => ?_⟩
  apply Subtype.ext
  simpa using hLab.2 _ (Subgroup.mem_subgroupOf.mp hx)

theorem recog_isPGroup_two {Y : Type} [Group Y] {Gs L : Subgroup Y}
    (hLab : IsElemAbelian 2 L) : IsPGroup 2 ↥(L.subgroupOf Gs) := by
  intro x
  refine ⟨1, Subtype.ext (Subtype.ext ?_)⟩
  simpa using hLab.2 _ (Subgroup.mem_subgroupOf.mp x.2)

theorem recog_false_two_rank {Y : Type} [Group Y] {Gs L : Subgroup Y}
    (hR : ∀ A : Subgroup ↥Gs, IsElemAbelian 2 A → Nat.card A ≤ 2 ^ 6)
    (hLGs : L ≤ Gs) (hLab : IsElemAbelian 2 L) (hL : 2 ^ 6 < Nat.card L) : False := by
  have hA := hR (L.subgroupOf Gs) (recog_isElemAbelian_subgroupOf hLab)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLGs).toEquiv] at hA
  exact absurd hL (not_lt.mpr hA)

theorem recog_false_borel {Y : Type} [Group Y] {Gs E L : Subgroup Y}
    (hBor : ∀ T : Subgroup ↥Gs, T ≠ ⊥ → IsPGroup 2 T →
      Group.IsSolvable ↥(Subgroup.normalizer (T : Set ↥Gs)))
    (hEGs : E ≤ Gs) (hEperf : commutator ↥E = ⊤) (hEne : E ≠ ⊥)
    (hEL : ∀ k ∈ E, k ∈ Subgroup.normalizer (L : Set Y)) (hLGs : L ≤ Gs)
    (hLab : IsElemAbelian 2 L) (hLne : L ≠ ⊥) : False := by
  have hT : L.subgroupOf Gs ≠ ⊥ := by
    intro h
    apply hLne
    rw [eq_bot_iff]
    intro y hy
    have hmem : (⟨y, hLGs hy⟩ : ↥Gs) ∈ L.subgroupOf Gs := Subgroup.mem_subgroupOf.mpr hy
    rw [h, Subgroup.mem_bot] at hmem
    rw [Subgroup.mem_bot]
    simpa using congrArg Subtype.val hmem
  have hSolv := hBor (L.subgroupOf Gs) hT (recog_isPGroup_two hLab)
  have hEN : E.subgroupOf Gs ≤
      Subgroup.normalizer ((L.subgroupOf Gs : Subgroup ↥Gs) : Set ↥Gs) := by
    intro k hk
    have hkN := Subgroup.mem_normalizer_iff.mp (hEL _ (Subgroup.mem_subgroupOf.mp hk))
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have hh := hkN (h : Y)
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
    exact hh
  have hbot : E.subgroupOf Gs = ⊥ :=
    eq_bot_of_perfect_le_solvable (recog_commutator_subgroupOf hEGs hEperf) hEN hSolv
  apply hEne
  rw [eq_bot_iff]
  intro y hy
  have hmem : (⟨y, hEGs hy⟩ : ↥Gs) ∈ E.subgroupOf Gs := Subgroup.mem_subgroupOf.mpr hy
  rw [hbot, Subgroup.mem_bot] at hmem
  rw [Subgroup.mem_bot]
  simpa using congrArg Subtype.val hmem

theorem exists_psl_of_listGroup (hBorel : BorelRankOneSolvableStatement)
    (hRank : TwoRankSporadicAltStatement) {Y : Type} [Group Y] [Finite Y] {Gs E L : Subgroup Y}
    [Gs.Normal] (hlist : ListGroup ↥Gs) (hEGs : E ≤ Gs) (hEperf : commutator ↥E = ⊤)
    (hEne : E ≠ ⊥) (hEL : ∀ k ∈ E, k ∈ normalizer (L : Set Y)) (hLGs : L ≤ Gs)
    (hLab : IsElemAbelian 2 L) (hL : 2 ^ 6 < Nat.card L) (hLne : L ≠ ⊥) :
    ∃ (r : ℕ) (K : Type) (_ : Field K) (_ : Finite K), 3 ≤ r ∧
      (∃ f : ℕ, 1 ≤ f ∧ Nat.card K = 2 ^ f) ∧
      Nonempty (↥Gs ≃* StatedProj (StatedSL r K)) := by
  rcases hlist with ⟨m, s, hm2, hs1, hmodel⟩ | ⟨s, hs2, hmodel⟩ | ⟨s, hodd, hs3, hmodel⟩ |
    ⟨k, hk6, hk9, hAlt⟩ | hM22 | hM23 | hM24
  · rcases Nat.lt_or_ge m 3 with hm3 | hm3
    · obtain rfl : m = 2 := by omega
      have hs2 : 2 ≤ s := by
        have hne : ((2 : ℕ), 2 ^ s) ≠ ((2 : ℕ), (2 : ℕ)) := hmodel.1.2.2.2.1
        by_contra hlt
        obtain rfl : s = 1 := by omega
        exact hne (by norm_num)
      exact (recog_false_borel (hBorel ↥Gs (Or.inl ⟨s, hs2, hmodel⟩)) hEGs hEperf hEne hEL
        hLGs hLab hLne).elim
    · obtain ⟨-, K, hKf, hKfin, hcard, ⟨e⟩⟩ := hmodel
      exact ⟨m, K, hKf, hKfin, hm3, ⟨s, hs1, hcard⟩, ⟨e⟩⟩
  · exact (recog_false_borel (hBorel ↥Gs (Or.inr (Or.inl ⟨s, hs2, hmodel⟩))) hEGs hEperf hEne
      hEL hLGs hLab hLne).elim
  · exact (recog_false_borel (hBorel ↥Gs (Or.inr (Or.inr ⟨s, hodd, hs3, hmodel⟩))) hEGs hEperf
      hEne hEL hLGs hLab hLne).elim
  · exact (recog_false_two_rank (hRank ↥Gs (Or.inl ⟨k, hk6, hk9, hAlt⟩)) hLGs hLab hL).elim
  · exact (recog_false_two_rank (hRank ↥Gs (Or.inr (Or.inl hM22))) hLGs hLab hL).elim
  · exact (recog_false_two_rank (hRank ↥Gs (Or.inr (Or.inr (Or.inl hM23)))) hLGs hLab hL).elim
  · exact (recog_false_two_rank (hRank ↥Gs (Or.inr (Or.inr (Or.inr hM24)))) hLGs hLab hL).elim

end CFSG.RankThree.GF2n.Stroth80

