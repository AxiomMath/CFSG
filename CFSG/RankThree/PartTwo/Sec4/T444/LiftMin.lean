module

public import CFSG.RankThree.PartTwo.Sec4.T444.Lift
public import CFSG.RankThree.PartTwo.KFacts.KS44OutSz
import CFSG.RankThree.PartTwo.Sec5.Tools
import CFSG.GroupTheory.QuasisimpleCommutingProductBound
import CFSG.GroupTheory.Fitting.CharacteristicP
import CFSG.GroupTheory.LocalCores.Layer
import CFSG.RankThree.GroupTheory.ThetaQuotientTransport
import CFSG.GroupTheory.PerfectResidualNodes
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.LocalCores
open CFSG.Assembly.RankThreeEven (localRank)

section General

variable {Y : Type*} [Group Y] [Finite Y]

theorem le_localRank_of_le_centralizer {s : ℕ} (hs : s.Prime) {E : Subgroup Y}
    (hE : CFSG.Assembly.IsElemAbelian s E) {k : ℕ} (hcard : Nat.card E = s ^ k) {u : Y}
    (hu : u ≠ 1) (hu2 : u ^ 2 = 1) (hEu : ∀ e ∈ E, e * u = u * e) : k ≤ localRank s Y := by
  have hord : orderOf u = 2 := orderOf_eq_prime hu2 hu
  have hP2 : IsPGroup 2 (Subgroup.zpowers u) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord, pow_one])
  have hPne : Subgroup.zpowers u ≠ ⊥ := fun h => hu (by
    have : u ∈ Subgroup.zpowers u := Subgroup.mem_zpowers u
    rwa [h, Subgroup.mem_bot] at this)
  have hloc : CFSG.Assembly.IsTwoLocal (Subgroup.normalizer (Subgroup.zpowers u : Set Y)) :=
    ⟨_, hPne, hP2, rfl⟩
  have hEN : E ≤ Subgroup.normalizer (Subgroup.zpowers u : Set Y) := by
    intro e he
    refine Subgroup.centralizer_le_normalizer _ ?_
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
    rintro _ rfl
    exact (hEu e he).symm
  have hk := Sec5.le_pRank_of_elemAbelian hs hEN hE hcard
  refine hk.trans (le_csSup ⟨Nat.card Y, ?_⟩ ⟨_, hloc, rfl⟩)
  rintro _ ⟨Z, -, rfl⟩
  exact (CFSG.RankThreeEvenClassification.Helpers.pRank_le_card s hs Z).trans
    (Subgroup.card_le_card_group Z)

theorem exists_prime_dvd_card_gt_three {K : Type*} [Group K] [Finite K] [Nontrivial K]
    [Group.IsPerfect K] (h3 : ¬ 3 ∣ Nat.card K) : ∃ s : ℕ, s.Prime ∧ 3 < s ∧ s ∣ Nat.card K := by
  by_contra hno
  push Not at hno
  have h2 : IsPGroup 2 K := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine IsPGroup.of_card (Nat.eq_prime_pow_of_unique_prime_dvd (p := 2)
      (Nat.card_pos (α := K)).ne' fun {d} hd hdK => ?_)
    by_contra hd2
    have hd3 : d ≠ 3 := fun h => h3 (h ▸ hdK)
    have := hno d hd (by have := hd.two_le; omega)
    exact this hdK
  have : Group.IsNilpotent K := h2.isNilpotent
  exact Group.IsPerfect.not_isSolvable K inferInstance

omit [Finite Y] in
theorem isElemAbelian_zpowers {s : ℕ} {c : Y} (hc : c ^ s = 1) :
    CFSG.Assembly.IsElemAbelian s (Subgroup.zpowers c) := CFSG.Open.isElemAbelian_zpowers hc

theorem four_le_localRank_of_conj {K : Subgroup Y} (hK : IsComponent K)
    (hZ : K ⊓ Subgroup.centralizer (K : Set Y) = ⊥) (h2 : 2 ∣ Nat.card K) {s : ℕ}
    (hs : s.Prime) (hsK : s ∣ Nat.card K) (r : Fin 5 → Y)
    (hr : ∀ i j, K.map (MulAut.conj (r i)).toMonoidHom = K.map (MulAut.conj (r j)).toMonoidHom →
      i = j) : 4 ≤ localRank s Y := by
  have : Fact s.Prime := ⟨hs⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Kc : Fin 5 → Subgroup Y := fun i => K.map (MulAut.conj (r i)).toMonoidHom with hKc
  have hcomp : ∀ i, IsComponent (Kc i) := fun i => isComponent_map_mulEquiv (MulAut.conj (r i)) hK
  have hcard : ∀ i, Nat.card (Kc i) = Nat.card K := fun i =>
    Subgroup.card_map_of_injective (MulAut.conj (r i)).injective
  have hZc : ∀ i, ∀ x ∈ Kc i, x ∈ Subgroup.centralizer (Kc i : Set Y) → x = 1 := by
    intro i x hx hxc
    obtain ⟨y, hy, rfl⟩ := hx
    have hyc : y ∈ Subgroup.centralizer (K : Set Y) := by
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      have h := Subgroup.mem_centralizer_iff.mp hxc _ ⟨z, hz, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h
      have h' : r i * (z * y) * (r i)⁻¹ = r i * (y * z) * (r i)⁻¹ := by
        calc r i * (z * y) * (r i)⁻¹ = (r i * z * (r i)⁻¹) * (r i * y * (r i)⁻¹) := by group
          _ = (r i * y * (r i)⁻¹) * (r i * z * (r i)⁻¹) := h
          _ = r i * (y * z) * (r i)⁻¹ := by group
      exact mul_left_cancel (mul_right_cancel h')
    have hy1 : y ∈ K ⊓ Subgroup.centralizer (K : Set Y) := ⟨hy, hyc⟩
    rw [hZ, Subgroup.mem_bot] at hy1
    simp [hy1]
  have hcomm : ∀ i j, i ≠ j → ∀ a ∈ Kc i, ∀ b ∈ Kc j, a * b = b * a := by
    intro i j hij a ha b hb
    rcases distinct_components_commute (hcomp i) (hcomp j) with h | h
    · exact absurd (hr i j h) hij
    · have hle := Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
      exact (Subgroup.mem_centralizer_iff.mp (hle ha) b hb).symm
  have hc : ∀ i, ∃ c ∈ Kc i, orderOf c = s := by
    intro i
    obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := Kc i) s (by rw [hcard]; exact hsK)
    exact ⟨c, c.2, by rw [← Subgroup.orderOf_coe] at hc; exact hc⟩
  choose c hcK hco using hc
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := Kc 4) 2 (by rw [hcard]; exact h2)
  have hcs : ∀ i, c i ^ s = 1 := fun i => by rw [← hco i, pow_orderOf_eq_one]
  have hc1 : ∀ i, c i ≠ 1 := fun i h => by
    have := hco i
    rw [h, orderOf_one] at this
    exact hs.one_lt.ne this
  have hcC : ∀ i m, i ≠ m → c i ∈ Subgroup.centralizer (Kc m : Set Y) := fun i m him =>
    Subgroup.mem_centralizer_iff.mpr fun b hb => (hcomm i m him _ (hcK i) b hb).symm
  have hnotin : ∀ (E : Subgroup Y) (m : Fin 5), E ≤ Subgroup.centralizer (Kc m : Set Y) →
      c m ∉ E := fun E m hE hmem => hc1 m (hZc m _ (hcK m) (hE hmem))
  have hcommE : ∀ (E : Subgroup Y) (m : Fin 5), E ≤ Subgroup.centralizer (Kc m : Set Y) →
      ∀ a ∈ E, a * c m = c m * a := fun E m hE a ha =>
    (Subgroup.mem_centralizer_iff.mp (hE ha) _ (hcK m)).symm
  set E1 := Subgroup.zpowers (c 0)
  set E2 := E1 ⊔ Subgroup.zpowers (c 1)
  set E3 := E2 ⊔ Subgroup.zpowers (c 2)
  set E4 := E3 ⊔ Subgroup.zpowers (c 3)
  have hzle : ∀ i m, i ≠ m → Subgroup.zpowers (c i) ≤ Subgroup.centralizer (Kc m : Set Y) :=
    fun i m him => Subgroup.zpowers_le.mpr (hcC i m him)
  have hE1 : ∀ m : Fin 5, m ≠ 0 → E1 ≤ Subgroup.centralizer (Kc m : Set Y) :=
    fun m hm => hzle 0 m (Ne.symm hm)
  have hE2 : ∀ m : Fin 5, m ≠ 0 → m ≠ 1 → E2 ≤ Subgroup.centralizer (Kc m : Set Y) :=
    fun m h0 h1 => sup_le (hE1 m h0) (hzle 1 m (Ne.symm h1))
  have hE3 : ∀ m : Fin 5, m ≠ 0 → m ≠ 1 → m ≠ 2 → E3 ≤ Subgroup.centralizer (Kc m : Set Y) :=
    fun m h0 h1 h2 => sup_le (hE2 m h0 h1) (hzle 2 m (Ne.symm h2))
  have hE4 : E4 ≤ Subgroup.centralizer (Kc 4 : Set Y) :=
    sup_le (hE3 4 (by decide) (by decide) (by decide)) (hzle 3 4 (by decide))
  obtain ⟨hA2, hc2⟩ := Sec5.isElemAbelian_sup_zpowers (isElemAbelian_zpowers (hcs 0))
    (hnotin E1 1 (hE1 1 (by decide))) (hcs 1) (hcommE E1 1 (hE1 1 (by decide)))
  obtain ⟨hA3, hc3⟩ := Sec5.isElemAbelian_sup_zpowers hA2
    (hnotin E2 2 (hE2 2 (by decide) (by decide))) (hcs 2)
    (hcommE E2 2 (hE2 2 (by decide) (by decide)))
  obtain ⟨hA4, hc4⟩ := Sec5.isElemAbelian_sup_zpowers hA3
    (hnotin E3 3 (hE3 3 (by decide) (by decide) (by decide))) (hcs 3)
    (hcommE E3 3 (hE3 3 (by decide) (by decide) (by decide)))
  have hcard4 : Nat.card E4 = s ^ 4 := by
    rw [hc4, hc3, hc2, Nat.card_zpowers, hco 0]
    ring
  have hu1 : (u : Y) ≠ 1 := fun h => by
    have : u = 1 := Subtype.ext h
    rw [this, orderOf_one] at hu
    omega
  have hu2 : (u : Y) ^ 2 = 1 := by
    rw [← Subgroup.coe_pow, ← hu, pow_orderOf_eq_one, Subgroup.coe_one]
  exact le_localRank_of_le_centralizer hs hA4 hcard4 hu1 hu2 fun e he =>
    (Subgroup.mem_centralizer_iff.mp (hE4 he) _ u.2).symm

theorem le_normalizer_of_isComponent (hY : ∀ s : ℕ, s.Prime → 3 < s → localRank s Y ≤ 3)
    {K : Subgroup Y} (hK : IsComponent K) (hZ : K ⊓ Subgroup.centralizer (K : Set Y) = ⊥)
    (h3 : ¬ 3 ∣ Nat.card K) (h2 : 2 ∣ Nat.card K) (R : Subgroup Y) [Group.IsPerfect R] :
    R ≤ Subgroup.normalizer (K : Set Y) := by
  classical
  have : Nontrivial K := isQuasisimple_nontrivial hK.1
  have : Group.IsPerfect K := hK.1.1
  obtain ⟨s, hs, hs3, hsK⟩ := exists_prime_dvd_card_gt_three (K := K) h3
  set N : Subgroup R := (Subgroup.normalizer (K : Set Y)).subgroupOf R with hN
  have hcard : Nat.card (R ⧸ N) ≤ 4 := by
    by_contra h5
    push Not at h5
    have : Fintype (R ⧸ N) := Fintype.ofFinite _
    obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le (α := Fin 5) (β := R ⧸ N)
      (by rw [Fintype.card_fin, ← Nat.card_eq_fintype_card]; omega)
    set r : Fin 5 → Y := fun i => ((f i).out : R)
    have hmap : ∀ a b : Y, K.map (MulAut.conj (a * b)).toMonoidHom =
        (K.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom := by
      intro a b
      rw [Subgroup.map_map]
      congr 1
      ext x
      simp [MulAut.conj_apply, mul_assoc]
    have hr : ∀ i j, K.map (MulAut.conj (r i)).toMonoidHom =
        K.map (MulAut.conj (r j)).toMonoidHom → i = j := by
      intro i j hij
      apply f.injective
      have hmem : (r j)⁻¹ * r i ∈ Subgroup.normalizer (K : Set Y) := by
        rw [Subgroup.mem_normalizer_iff_map_conj_eq]
        show K.map (MulAut.conj ((r j)⁻¹ * r i)).toMonoidHom = K
        rw [hmap, hij, ← hmap, inv_mul_cancel]
        ext x
        simp
      have h1 : (((f j).out : R) : R ⧸ N) = (((f i).out : R) : R ⧸ N) := by
        rw [QuotientGroup.eq]
        exact Subgroup.mem_subgroupOf.mpr (by simpa [r] using hmem)
      rw [QuotientGroup.out_eq', QuotientGroup.out_eq'] at h1
      exact h1.symm
    have := four_le_localRank_of_conj hK hZ h2 hs hsK r hr
    have := hY s hs hs3
    omega
  have hsolv : Group.IsSolvable (Equiv.Perm (R ⧸ N)) :=
    CFSG.OrderReductions.PermutationReduction.permutation_solvable_of_card_le_four _ hcard
  set φ := MulAction.toPermHom R (R ⧸ N)
  have hperf : Group.IsPerfect φ.range := Group.IsPerfect.range φ
  have htriv : ∀ x : R, φ x = 1 := by
    by_contra hx
    push Not at hx
    obtain ⟨x, hx⟩ := hx
    have : Nontrivial φ.range := ⟨⟨⟨φ x, x, rfl⟩, 1, fun h => hx (congrArg Subtype.val h)⟩⟩
    exact Group.IsPerfect.not_isSolvable φ.range inferInstance
  intro x hx
  have h := congrArg (fun σ : Equiv.Perm (R ⧸ N) => σ ((1 : R) : R ⧸ N)) (htriv ⟨x, hx⟩)
  simp only [Equiv.Perm.coe_one, id_eq, φ, MulAction.toPermHom_apply, MulAction.toPerm_apply,
    MulAction.Quotient.smul_mk, smul_eq_mul, mul_one] at h
  rw [QuotientGroup.eq, mul_one] at h
  have h' := N.inv_mem h
  rw [inv_inv] at h'
  exact Subgroup.mem_subgroupOf.mp h'

omit [Finite Y] in
theorem exists_mem_inv_mul_mem_centralizer {K R : Subgroup Y} [Group.IsPerfect R]
    (hRK : R ≤ Subgroup.normalizer (K : Set Y))
    (hout : commutator (MulAut K) ≤ (MulAut.conj : K →* MulAut K).range) {r : Y} (hr : r ∈ R) :
    ∃ k ∈ K, k⁻¹ * r ∈ Subgroup.centralizer (K : Set Y) := by
  set φ : R →* MulAut K := K.normalizerMonoidHom.comp (Subgroup.inclusion hRK) with hφ
  have hperf : Group.IsPerfect φ.range := Group.IsPerfect.range φ
  have hle : φ.range ≤ (MulAut.conj : K →* MulAut K).range := by
    rw [← Subgroup.commutator_eq_self (H := φ.range)]
    exact (Subgroup.commutator_mono le_top le_top).trans (by rw [← commutator_def]; exact hout)
  obtain ⟨k, hk⟩ := hle ⟨⟨r, hr⟩, rfl⟩
  refine ⟨k, k.2, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
  have h : (k : Y) * y * (k : Y)⁻¹ = r * y * r⁻¹ := by
    have := congrArg (fun σ : MulAut K => ((σ ⟨y, hy⟩ : K) : Y)) hk
    simpa [hφ, MulAut.conj_apply, normalizerMonoidHom_apply_coe] using this
  calc y * ((k : Y)⁻¹ * r) = (k : Y)⁻¹ * ((k : Y) * y * (k : Y)⁻¹) * r := by group
    _ = (k : Y)⁻¹ * (r * y * r⁻¹) * r := by rw [h]
    _ = (k : Y)⁻¹ * r * y := by group

theorem exists_isComponent_le_of_isSubnormal (hθ : aschbacherSolvableCore 3 Y = ⊥)
    {Z : Subgroup Y} (hsub : Z.IsSubnormal) (hne : Z ≠ ⊥) (h3 : ¬ 3 ∣ Nat.card Z) :
    ∃ K : Subgroup Y, IsComponent K ∧ K ≤ Z := by
  have hF : fittingSubgroup Z = ⊥ := by
    have hle := le_aschbacherSolvableCore_of_isSubnormal
      (T := (fittingSubgroup Z).map Z.subtype)
      (Subgroup.IsSubnormal.trans' fittingSubgroup_normal.isSubnormal hsub)
      (Group.isSolvable_of_isSolvable_injective (f :=
        ((fittingSubgroup Z).equivMapOfInjective _ Z.subtype_injective).symm.toMonoidHom)
        (MulEquiv.injective _))
      (fun h => h3 (h.trans (by
        rw [Subgroup.card_map_of_injective Z.subtype_injective]
        exact Subgroup.card_subgroup_dvd_card _)))
    rw [hθ, le_bot_iff, Subgroup.map_eq_bot_iff_of_injective _ Z.subtype_injective] at hle
    exact hle
  by_contra hno
  push Not at hno
  have hE : layer Z = ⊥ := layer_eq_bot_of_forall fun K hK => by
    have hKc : IsComponent (K.map Z.subtype) :=
      ⟨isQuasisimple_of_mulEquiv (K.equivMapOfInjective _ Z.subtype_injective) hK.1,
        Subgroup.IsSubnormal.trans' hK.2 hsub⟩
    exact hno _ hKc (Subgroup.map_subtype_le K)
  have hC := centralizer_generalizedFitting_le Z
  rw [generalizedFitting, hF, hE, bot_sup_eq, Subgroup.coe_bot,
    Subgroup.centralizer_eq_top_iff_subset.mpr (by simp), top_le_iff] at hC
  apply hne
  rw [eq_bot_iff]
  intro x hx
  have : (⟨x, hx⟩ : Z) ∈ (⊥ : Subgroup Z) := hC ▸ Subgroup.mem_top _
  rw [Subgroup.mem_bot] at this
  exact (congrArg Subtype.val this : _)

theorem inCatalog_of_le_quotient {G : Type} [Group G] (hK : CFSG.IsKGroup G) {N : Subgroup G}
    [N.Normal] {K : Subgroup (G ⧸ N)} [IsSimpleGroup K] : CFSG.Assembly.InCatalog K := by
  set H := K.comap (QuotientGroup.mk' N)
  set N' : Subgroup H := N.subgroupOf H
  obtain ⟨η, -⟩ := exists_quotient_mulEquiv_map (QuotientGroup.mk' N) H N' fun h => by
    rw [Subgroup.mem_subgroupOf, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hHK : H.map (QuotientGroup.mk' N) = K :=
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective N) K
  let e : H ⧸ N' ≃* K := η.trans (MulEquiv.subgroupCongr hHK)
  have : Nontrivial (H ⧸ N') := e.toEquiv.nontrivial
  have : IsSimpleGroup (H ⧸ N') :=
    IsSimpleGroup.isSimpleGroup_of_surjective e.symm.toMonoidHom e.symm.surjective
  obtain ⟨i, ⟨f⟩⟩ := hK H N' inferInstance
  exact ⟨i, ⟨e.symm.trans f⟩⟩

end General


section Main

variable {G : Type} [Group G] [Finite G]

theorem isSolvable_inf_pPrimeCore_of_minimal (hSz : KFacts.KPSz) (hK : CFSG.IsKGroup G)
    (hrank : ∀ s : ℕ, s.Prime → 3 < s → localRank s (G ⧸ aschbacherSolvableCore 3 G) ≤ 3)
    {J : Subgroup (G ⧸ CFSG.pPrimeCore 3 G)} (hJ : IsComponent J) {L : Subgroup G}
    [hLp : Group.IsPerfect L] (hLs : L.IsSubnormal) (hLJ : L.map (starQuot G) = J)
    (hmin : ∀ L' : Subgroup G, Group.IsPerfect L' → L'.IsSubnormal → L'.map (starQuot G) = J →
      Nat.card L ≤ Nat.card L') :
    Group.IsSolvable (L ⊓ CFSG.pPrimeCore 3 G : Subgroup G) := by
  by_contra hns
  set P := CFSG.pPrimeCore 3 G with hP
  set θ := aschbacherSolvableCore 3 G with hθdef
  set ρ := QuotientGroup.mk' θ with hρ
  set LP : Subgroup G := L ⊓ P with hLP
  obtain ⟨-, hchar, hperf, -, -, hbot⟩ := perfect_residual_characterization (G := LP)
  set Y0 : Subgroup G := (perfectResidual LP).map LP.subtype with hY0
  have hY0ne : perfectResidual LP ≠ ⊥ := fun h => hns (hbot.mp h)
  have hY0LP : Y0 ≤ LP := Subgroup.map_subtype_le _
  have hY0sub : Y0.IsSubnormal := by
    refine Subgroup.IsSubnormal.trans' (Subgroup.normal_of_characteristic _).isSubnormal ?_
    exact hLs.inf (inferInstance : P.Normal).isSubnormal
  have hY0p : Group.IsPerfect Y0 := isPerfect_map_subtype hperf
  have hP3 : ¬ 3 ∣ Nat.card P := not_three_dvd_card_pPrimeCore
  have hY03 : ¬ 3 ∣ Nat.card Y0 := fun h =>
    hP3 (h.trans (Subgroup.card_dvd_of_le (hY0LP.trans inf_le_right)))
  set Yb : Subgroup (G ⧸ θ) := Y0.map ρ with hYb
  have hYbne : Yb ≠ ⊥ := by
    intro h
    rw [hYb, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
    have hsolv : Group.IsSolvable Y0 := by
      have := (solvable_prime_complement_core_characterization Nat.prime_three (H := G)).1
      exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective h)
    have : Subsingleton Y0 := by
      by_contra hnt
      rw [not_subsingleton_iff_nontrivial] at hnt
      exact Group.IsPerfect.not_isSolvable Y0 hsolv
    apply hY0ne
    rw [eq_bot_iff]
    intro x hx
    have h1 : (⟨(x : G), Subgroup.mem_map_of_mem _ hx⟩ : Y0) = 1 := Subsingleton.elim _ _
    have h2 : (x : G) = 1 := congrArg Subtype.val h1
    exact (Subgroup.mem_bot).mpr (Subtype.ext h2)
  have hθX : aschbacherSolvableCore 3 (G ⧸ θ) = ⊥ := (theta_quotient_core_and_ranks (G := G)).1
  have hYb3 : ¬ 3 ∣ Nat.card Yb := fun h => hY03 (h.trans (Subgroup.card_map_dvd _ _))
  obtain ⟨Kb, hKb, hKbY⟩ := exists_isComponent_le_of_isSubnormal hθX
    (hY0sub.map (QuotientGroup.mk'_surjective θ)) hYbne hYb3
  have hKb3 : ¬ 3 ∣ Nat.card Kb := fun h => hYb3 (h.trans (Subgroup.card_dvd_of_le hKbY))
  have hKbZ : Kb ⊓ Subgroup.centralizer (Kb : Set (G ⧸ θ)) = ⊥ := by
    rw [CFSG.GroupTheory.inf_centralizer_eq_map_center]
    have hle := le_aschbacherSolvableCore_of_isSubnormal
      (T := (Subgroup.center Kb).map Kb.subtype)
      (Subgroup.IsSubnormal.trans' (Subgroup.normal_of_characteristic _).isSubnormal hKb.2)
      (Group.isSolvable_of_isSolvable_injective (f :=
        ((Subgroup.center Kb).equivMapOfInjective _ Kb.subtype_injective).symm.toMonoidHom)
        (MulEquiv.injective _))
      (fun h => hKb3 (h.trans (by
        rw [Subgroup.card_map_of_injective Kb.subtype_injective]
        exact Subgroup.card_subgroup_dvd_card _)))
    rwa [hθX, le_bot_iff] at hle
  have hcenter : Subgroup.center Kb = ⊥ := by
    rw [← Subgroup.map_eq_bot_iff_of_injective _ Kb.subtype_injective,
      ← CFSG.GroupTheory.inf_centralizer_eq_map_center, hKbZ]
  have hsimp : IsSimpleGroup Kb := by
    have hinj : Function.Injective (QuotientGroup.mk' (Subgroup.center Kb)) := by
      rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hcenter]
    have e := MulEquiv.ofBijective (QuotientGroup.mk' (Subgroup.center Kb))
      ⟨hinj, QuotientGroup.mk'_surjective _⟩
    have : IsSimpleGroup (Kb ⧸ Subgroup.center Kb) := hKb.1.2.1
    have : Nontrivial Kb := isQuasisimple_nontrivial hKb.1
    exact IsSimpleGroup.isSimpleGroup_of_surjective e.symm.toMonoidHom e.symm.surjective
  have hnab : ∃ a b : Kb, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hKb.1.2.2
    induction a using QuotientGroup.induction_on with
    | H a =>
      induction b using QuotientGroup.induction_on with
      | H b => exact ⟨a, b, fun h => hab (by rw [← QuotientGroup.mk_mul, h, QuotientGroup.mk_mul])⟩
  have hcat : CFSG.Assembly.InCatalog Kb := inCatalog_of_le_quotient hK
  have hKb2 := KFacts.two_dvd_card_of_not_three_dvd hSz hnab hcat hKb3
  have hout := KFacts.commutator_le_inner_of_not_three_dvd hSz hnab hcat hKb3
  set Rb : Subgroup (G ⧸ θ) := L.map ρ with hRb
  have : Group.IsPerfect Rb := Group.IsPerfect.map ρ
  have hRbN : Rb ≤ Subgroup.normalizer (Kb : Set (G ⧸ θ)) :=
    le_normalizer_of_isComponent hrank hKb hKbZ hKb3 hKb2 Rb
  set C' : Subgroup G := L ⊓ (Subgroup.centralizer (Kb : Set (G ⧸ θ))).comap ρ with hC'
  have hC'L : C' ≤ L := inf_le_left
  have hC'n : (C'.subgroupOf L).Normal := by
    refine ⟨fun x hx l => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    refine ⟨L.mul_mem (L.mul_mem l.2 hx.1) (L.inv_mem l.2), ?_⟩
    have hl : ρ l ∈ Subgroup.normalizer (Kb : Set (G ⧸ θ)) := hRbN ⟨l, l.2, rfl⟩
    change ρ ((l : G) * x * (l : G)⁻¹) ∈ Subgroup.centralizer (Kb : Set (G ⧸ θ))
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have hk' : (ρ l)⁻¹ * k * (ρ l) ∈ Kb := by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem hl) k).mp hk
      rwa [inv_inv] at this
    have hc : (ρ l)⁻¹ * k * ρ l * ρ x = ρ x * ((ρ l)⁻¹ * k * ρ l) :=
      Subgroup.mem_centralizer_iff.mp hx.2 _ hk'
    rw [map_mul, map_mul, map_inv]
    calc k * (ρ l * ρ x * (ρ l)⁻¹) = ρ l * ((ρ l)⁻¹ * k * ρ l * ρ x) * (ρ l)⁻¹ := by group
      _ = ρ l * (ρ x * ((ρ l)⁻¹ * k * ρ l)) * (ρ l)⁻¹ := by rw [hc]
      _ = ρ l * ρ x * (ρ l)⁻¹ * k := by group
  have hC'sub : C'.IsSubnormal := Subgroup.IsSubnormal.trans hC'L hC'n.isSubnormal hLs
  have hC'J : C'.map (starQuot G) = J := by
    refine le_antisymm (hLJ ▸ Subgroup.map_mono hC'L) ?_
    rw [← hLJ]
    rintro _ ⟨l, hl, rfl⟩
    obtain ⟨k, hk, hkc⟩ := exists_mem_inv_mul_mem_centralizer hRbN hout
      (Subgroup.mem_map_of_mem ρ hl)
    obtain ⟨y, hy, rfl⟩ := hKbY hk
    have hyP : y ∈ P := (hY0LP hy).2
    refine ⟨y⁻¹ * l, ⟨L.mul_mem (L.inv_mem (hY0LP hy).1) hl, ?_⟩, ?_⟩
    · change ρ (y⁻¹ * l) ∈ Subgroup.centralizer (Kb : Set (G ⧸ θ))
      rw [map_mul, map_inv]
      exact hkc
    · have hy1 : starQuot G y = 1 := (QuotientGroup.eq_one_iff y).mpr hyP
      rw [map_mul, map_inv, hy1, inv_one, one_mul]
  obtain ⟨⟨n, hn, -⟩, -, hperf', -, -, -⟩ := perfect_residual_characterization (G := C')
  set L1 : Subgroup G := (perfectResidual C').map C'.subtype with hL1
  have : Group.IsPerfect J := hJ.1.1
  have hL1J : L1.map (starQuot G) = J := by
    rw [hL1, hn]
    exact map_derivedSeries_eq_of_isPerfect (starQuot G) hC'J n
  have hL1sub : L1.IsSubnormal :=
    Subgroup.IsSubnormal.trans' (Subgroup.normal_of_characteristic _).isSubnormal hC'sub
  have hL1L : L1 ≤ L := (Subgroup.map_subtype_le _).trans hC'L
  have hL1ne : L1 ≠ L := by
    intro h
    have hLC : L ≤ C' := h ▸ Subgroup.map_subtype_le _
    have hKbC : Kb ≤ Subgroup.centralizer (Kb : Set (G ⧸ θ)) := by
      intro k hk
      obtain ⟨y, hy, rfl⟩ := hKbY hk
      exact (hLC (hY0LP hy).1).2
    have hKbb : Kb = ⊥ := by
      rw [eq_bot_iff, ← hKbZ]
      exact le_inf le_rfl hKbC
    have : Nontrivial Kb := isQuasisimple_nontrivial hKb.1
    exact (Subgroup.nontrivial_iff_ne_bot _).mp this hKbb
  have hlt : Nat.card L1 < Nat.card L :=
    Subgroup.card_lt_of_lt (lt_of_le_of_ne hL1L hL1ne)
  have := hmin L1 (isPerfect_map_subtype hperf') hL1sub hL1J
  omega

theorem exists_mem_thetaComponents_map_eq (hSz : KFacts.KPSz) (hK : CFSG.IsKGroup G)
    (hrank : ∀ s : ℕ, s.Prime → 3 < s → localRank s (G ⧸ aschbacherSolvableCore 3 G) ≤ 3)
    {J : Subgroup (G ⧸ CFSG.pPrimeCore 3 G)} (hJ : IsComponent J) :
    ∃ L ∈ thetaComponents 3 G, L.map (starQuot G) = J := by
  classical
  have hex : ∃ n, ∃ L : Subgroup G, Group.IsPerfect L ∧ L.IsSubnormal ∧
      L.map (starQuot G) = J ∧ Nat.card L = n := by
    obtain ⟨L, h1, h2, h3⟩ := exists_perfect_isSubnormal_map_eq hJ
    exact ⟨_, L, h1, h2, h3, rfl⟩
  obtain ⟨L, hLp, hLs, hLJ, hLn⟩ := Nat.find_spec hex
  have hmin : ∀ L' : Subgroup G, Group.IsPerfect L' → L'.IsSubnormal →
      L'.map (starQuot G) = J → Nat.card L ≤ Nat.card L' := fun L' h1 h2 h3 =>
    hLn ▸ Nat.find_min' hex ⟨L', h1, h2, h3, rfl⟩
  have hsolv := isSolvable_inf_pPrimeCore_of_minimal hSz hK hrank hJ hLs hLJ hmin
  set P := CFSG.pPrimeCore 3 G with hP
  have hLPθ : (L ⊓ P).subgroupOf L ≤ aschbacherSolvableCore 3 L := by
    refine (solvable_prime_complement_core_characterization Nat.prime_three).2.2.2.1 _ ?_ ?_ ?_
    · refine ⟨fun x hx l => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      exact ⟨L.mul_mem (L.mul_mem l.2 hx.1) (L.inv_mem l.2),
        (inferInstance : P.Normal).conj_mem _ hx.2 l⟩
    · exact Group.isSolvable_of_isSolvable_injective (f :=
        (Subgroup.subgroupOfEquivOfLe (inf_le_left : L ⊓ P ≤ L)).toMonoidHom)
        (MulEquiv.injective _)
    · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : L ⊓ P ≤ L)).toEquiv]
      exact fun h => not_three_dvd_card_pPrimeCore (G := G)
        (h.trans (Subgroup.card_dvd_of_le inf_le_right))
  have hθL := solvable_prime_complement_core_subnormal_intersection Nat.prime_three hLs
  obtain ⟨η, -⟩ := exists_quotient_mulEquiv_map (starQuot G) L (aschbacherSolvableCore 3 L)
    fun l => by
      rw [starQuot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      constructor
      · intro hl
        have hmem : (l : G) ∈ inSubgroup (aschbacherSolvableCore 3) L := ⟨l, hl, rfl⟩
        rw [hθL] at hmem
        exact aschbacherSolvableCore_le_pPrimeCore hmem.2
      · intro hl
        exact hLPθ (Subgroup.mem_subgroupOf.mpr ⟨l.2, hl⟩)
  exact ⟨L, ⟨hLp, hLs,
    isQuasisimple_of_mulEquiv (η.trans (MulEquiv.subgroupCongr hLJ)).symm hJ.1⟩, hLJ⟩

end Main

end CFSG.RankThree.PartTwo.Sec4
