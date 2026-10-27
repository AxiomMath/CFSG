module

public import CFSG.RankThree.PartTwo.Sec13.Item13Basic
public import CFSG.RankThree.GroupTheory.ThetaQuotientTransport
public import CFSG.RankThree.PartTwo.Sec13.Steps

public section

namespace CFSG.RankThree.PartTwo.Sec13

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open scoped commutatorElement

section Theta

variable {G : Type} [Group G] [Finite G] {c : G} {L A : Subgroup G}

omit [Finite G] in
theorem centralizer_singleton_eq_zpowers (c : G) :
    Subgroup.centralizer ({c} : Set G) = Subgroup.centralizer (Subgroup.zpowers c : Set G) := by
  rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]

omit [Finite G] in
theorem centralizer_le_normalizer_zpowers (c : G) :
    Subgroup.centralizer ({c} : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) := by
  rw [centralizer_singleton_eq_zpowers]
  exact Subgroup.centralizer_le_normalizer _

omit [Finite G] in
theorem centralizer_normal_in_normalizer_zpowers (c : G) :
    ((Subgroup.centralizer ({c} : Set G)).subgroupOf
      (Subgroup.normalizer (Subgroup.zpowers c : Set G))).Normal := by
  rw [centralizer_singleton_eq_zpowers]
  infer_instance

theorem subgroupOf_normalizer_mem_thetaComponents (hL : L ∈ thetaComponentsAt 3 c) :
    L.subgroupOf (Subgroup.normalizer (Subgroup.zpowers c : Set G)) ∈
      thetaComponents 3 (Subgroup.normalizer (Subgroup.zpowers c : Set G)) := by
  set N := Subgroup.normalizer (Subgroup.zpowers c : Set G) with hN
  set C := Subgroup.centralizer ({c} : Set G) with hC
  obtain ⟨hLC, hL'⟩ := mem_thetaComponentsIn_iff.mp hL
  have hCN : C ≤ N := centralizer_le_normalizer_zpowers c
  have hLN : L ≤ N := hLC.trans hCN
  set e : L.subgroupOf C ≃* L.subgroupOf N :=
    (Subgroup.subgroupOfEquivOfLe hLC).trans (Subgroup.subgroupOfEquivOfLe hLN).symm
  refine ⟨?_, ?_, ?_⟩
  · have := hL'.1
    exact Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  · have hK : (C.subgroupOf N).IsSubnormal :=
      (centralizer_normal_in_normalizer_zpowers c).isSubnormal
    refine Subgroup.IsSubnormal.trans (fun x hx => Subgroup.mem_subgroupOf.mpr
      (hLC (Subgroup.mem_subgroupOf.mp hx))) ?_ hK
    have h := hL'.2.1.comap (Subgroup.subgroupOfEquivOfLe hCN).toMonoidHom
    convert h using 1
    ext x
    simp [Subgroup.mem_subgroupOf]
  · exact LocalCores.isQuasisimple_of_mulEquiv
      (QuotientGroup.congr _ _ e (aschbacherSolvableCore_map_mulEquiv Nat.prime_three e)) hL'.2.2

theorem theta_le_normalizer_lBar (hL : L ∈ thetaComponentsAt 3 c) :
    aschbacherSolvableCore 3 (Subgroup.normalizer (Subgroup.zpowers c : Set G)) ≤
      Subgroup.normalizer
        ((L.subgroupOf (Subgroup.normalizer (Subgroup.zpowers c : Set G)) :
          Subgroup (Subgroup.normalizer (Subgroup.zpowers c : Set G))) :
          Set (Subgroup.normalizer (Subgroup.zpowers c : Set G))) :=
  (theta_component_quotient_structure Nat.prime_three
    (subgroupOf_normalizer_mem_thetaComponents hL)).2.2.2.2.2.2.1

theorem exists_lBarEquiv (hL : L ∈ thetaComponentsAt 3 c) :
    ∃ η : (L ⧸ aschbacherSolvableCore 3 L) ≃* Sec12.lBar c L,
      ∀ l : L, (η (l : L ⧸ aschbacherSolvableCore 3 L) :
        Subgroup.normalizer (Subgroup.zpowers c : Set G) ⧸
          aschbacherSolvableCore 3 (Subgroup.normalizer (Subgroup.zpowers c : Set G))) =
        QuotientGroup.mk' _ ⟨(l : G), (Sec6.le_centralizer_of_mem_thetaComponentsAt hL).trans
          (centralizer_le_normalizer_zpowers c) l.2⟩ := by
  set N := Subgroup.normalizer (Subgroup.zpowers c : Set G) with hN
  have hLN : L ≤ N := (Sec6.le_centralizer_of_mem_thetaComponentsAt hL).trans
    (centralizer_le_normalizer_zpowers c)
  obtain ⟨-, -, ⟨η, hη⟩, -⟩ := theta_component_quotient_structure Nat.prime_three
    (subgroupOf_normalizer_mem_thetaComponents hL)
  set e : L ≃* L.subgroupOf N := (Subgroup.subgroupOfEquivOfLe hLN).symm
  exact ⟨(QuotientGroup.congr _ _ e
    (aschbacherSolvableCore_map_mulEquiv Nat.prime_three e)).trans η, fun l => hη (e l)⟩

theorem mem_of_mk_mem_lBar (hL : L ∈ thetaComponentsAt 3 c)
    {x : Subgroup.normalizer (Subgroup.zpowers c : Set G)} {k : ℕ} (hx : x ^ 3 ^ k = 1)
    (hmem : QuotientGroup.mk' _ x ∈ Sec12.lBar c L) : (x : G) ∈ L := by
  obtain ⟨l, hl, hlx⟩ := hmem
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hlx
  have htN := theta_le_normalizer_lBar hL hlx
  have hxe : x = l * (l⁻¹ * x) := by rw [mul_inv_cancel_left]
  have hpow : ∀ n : ℕ, ∃ ln ∈ L.subgroupOf (Subgroup.normalizer (Subgroup.zpowers c : Set G)),
      (l * (l⁻¹ * x)) ^ n = ln * (l⁻¹ * x) ^ n := by
    intro n
    induction n with
    | zero => exact ⟨1, Subgroup.one_mem _, by simp⟩
    | succ n ih =>
      obtain ⟨ln, hln, hn⟩ := ih
      refine ⟨ln * ((l⁻¹ * x) ^ n * l * ((l⁻¹ * x) ^ n)⁻¹), Subgroup.mul_mem _ hln ?_, ?_⟩
      · exact (Subgroup.mem_normalizer_iff.mp (Subgroup.pow_mem _ htN n) l).mp hl
      · rw [pow_succ, hn]
        group
  obtain ⟨ln, hln, hn⟩ := hpow (3 ^ k)
  rw [← hxe, hx] at hn
  have htk : (l⁻¹ * x) ^ 3 ^ k ∈
      L.subgroupOf (Subgroup.normalizer (Subgroup.zpowers c : Set G)) := by
    have : (l⁻¹ * x) ^ 3 ^ k = ln⁻¹ := eq_inv_of_mul_eq_one_right hn.symm
    rw [this]
    exact Subgroup.inv_mem _ hln
  have hcop : (3 ^ k).Coprime (orderOf (l⁻¹ * x)) := by
    apply Nat.Coprime.pow_left
    rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
    intro h3
    apply (solvable_prime_complement_core_characterization
      (H := Subgroup.normalizer (Subgroup.zpowers c : Set G)) Nat.prime_three).2.2.1
    exact h3.trans (Subgroup.orderOf_dvd_natCard _ hlx)
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  have htL : l⁻¹ * x ∈ L.subgroupOf (Subgroup.normalizer (Subgroup.zpowers c : Set G)) :=
    hm ▸ Subgroup.pow_mem _ htk m
  have hxL : x ∈ L.subgroupOf (Subgroup.normalizer (Subgroup.zpowers c : Set G)) :=
    hxe ▸ Subgroup.mul_mem _ hl htL
  exact hxL

omit [Finite G] in
theorem le_normalizer_zpowers_of_mem (hL : L ∈ thetaComponentsAt 3 c) :
    L ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) :=
  (Sec6.le_centralizer_of_mem_thetaComponentsAt hL).trans
    (centralizer_le_normalizer_zpowers c)

end Theta

section Bar

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G}

omit [Finite G] in
theorem lBar_le_lBarA : Sec12.lBar c L ≤ lBarA c L A :=
  Subgroup.map_mono fun _ hx => Subgroup.mem_subgroupOf.mpr
    (le_sup_left (a := L) (b := A) (Subgroup.mem_subgroupOf.mp hx))

omit [Finite G] in
theorem mkC_mem_subgroupOf (hcA : c ∈ A) :
    (⟨c, Subgroup.le_normalizer (Subgroup.mem_zpowers c)⟩ :
      Subgroup.normalizer (Subgroup.zpowers c : Set G)) ∈
      (L ⊔ A).subgroupOf (Subgroup.normalizer (Subgroup.zpowers c : Set G)) :=
  Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_right hcA)

@[expose] noncomputable def mkC (hcA : c ∈ A) : lBarA c L A :=
  ⟨QuotientGroup.mk' _ ⟨c, Subgroup.le_normalizer (Subgroup.mem_zpowers c)⟩,
    Subgroup.mem_map_of_mem _ (mkC_mem_subgroupOf hcA)⟩

theorem mkC_mem_center (h : Sec13Data G A c L) :
    mkC (L := L) h.mem_A ∈ Subgroup.center (lBarA c L A) := by
  rw [Subgroup.mem_center_iff]
  rintro ⟨_, ⟨z, hz, rfl⟩⟩
  apply Subtype.ext
  have hzC : (z : G) ∈ Subgroup.centralizer ({c} : Set G) :=
    sup_le h.le_centralizer h.A_le_centralizer (Subgroup.mem_subgroupOf.mp hz)
  have hcomm : z * ⟨c, Subgroup.le_normalizer (Subgroup.mem_zpowers c)⟩ =
      ⟨c, Subgroup.le_normalizer (Subgroup.mem_zpowers c)⟩ * z :=
    Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hzC)
  simp only [mkC, Subgroup.coe_mul, ← map_mul, hcomm]

theorem mkC_ne_one (h : Sec13Data G A c L) : mkC (L := L) h.mem_A ≠ 1 := by
  intro h1
  have h2 : QuotientGroup.mk' (aschbacherSolvableCore 3
      (Subgroup.normalizer (Subgroup.zpowers c : Set G)))
      (⟨c, Subgroup.le_normalizer (Subgroup.mem_zpowers c)⟩ :
        Subgroup.normalizer (Subgroup.zpowers c : Set G)) = 1 :=
    congrArg Subtype.val h1
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
  set N := Subgroup.normalizer (Subgroup.zpowers c : Set G)
  have hdvd : orderOf (⟨c, Subgroup.le_normalizer (Subgroup.mem_zpowers c)⟩ : N) ∣
      Nat.card (aschbacherSolvableCore 3 N) := Subgroup.orderOf_dvd_natCard _ h2
  rw [Subgroup.orderOf_mk, h.orderOf_eq] at hdvd
  exact (solvable_prime_complement_core_characterization (H := N) Nat.prime_three).2.2.1 hdvd

theorem mem_of_mkC_mem (h : Sec13Data G A c L)
    (hmem : (mkC (L := L) h.mem_A : _) ∈ (Sec12.lBar c L).subgroupOf (lBarA c L A)) : c ∈ L := by
  have h3 : (⟨c, Subgroup.le_normalizer (Subgroup.mem_zpowers c)⟩ :
      Subgroup.normalizer (Subgroup.zpowers c : Set G)) ^ 3 ^ 1 = 1 := by
    apply Subtype.ext
    simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    rw [← h.orderOf_eq]
    exact pow_orderOf_eq_one c
  exact mem_of_mk_mem_lBar h.mem_thetaComponentsAt h3 (Subgroup.mem_subgroupOf.mp hmem)

theorem lBar_normal (h : Sec13Data G A c L) :
    ((Sec12.lBar c L).subgroupOf (lBarA c L A)).Normal := by
  refine ⟨fun x hx g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hx ⊢
  obtain ⟨_, ⟨z, hz, rfl⟩⟩ := g
  obtain ⟨l, hl, hlx⟩ := hx
  have hzN : (z : G) ∈ Subgroup.normalizer (L : Set G) :=
    sup_le Subgroup.le_normalizer h.le_normalizer (Subgroup.mem_subgroupOf.mp hz)
  refine ⟨z * l * z⁻¹, Subgroup.mem_subgroupOf.mpr ?_, ?_⟩
  · exact (Subgroup.mem_normalizer_iff.mp hzN _).mp (Subgroup.mem_subgroupOf.mp hl)
  · simp only [map_mul, map_inv, hlx, Subgroup.coe_mul, Subgroup.coe_inv]

theorem isPerfect_lBar (h : Sec13Data G A c L) : Group.IsPerfect (Sec12.lBar c L) := by
  have hLp : Group.IsPerfect L := Sec6.isPerfect_of_mem_thetaComponentsAt h.mem_thetaComponentsAt
  have hLN := le_normalizer_zpowers_of_mem h.mem_thetaComponentsAt
  set e : L ≃* L.subgroupOf (Subgroup.normalizer (Subgroup.zpowers c : Set G)) :=
    (Subgroup.subgroupOfEquivOfLe hLN).symm
  have : Group.IsPerfect (L.subgroupOf (Subgroup.normalizer (Subgroup.zpowers c : Set G))) :=
    Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  exact Group.IsPerfect.ofSurjective
    (f := (QuotientGroup.mk' _).subgroupMap (L.subgroupOf _))
    ((QuotientGroup.mk' _).subgroupMap_surjective _)

theorem lBar_ne_bot (h : Sec13Data G A c L) : Sec12.lBar c L ≠ ⊥ := by
  obtain ⟨η, -⟩ := exists_lBarEquiv h.mem_thetaComponentsAt
  have hq := Sec6.isQuasisimple_of_mem_thetaComponentsAt h.mem_thetaComponentsAt
  have : IsSimpleGroup ((L ⧸ aschbacherSolvableCore 3 L) ⧸
      Subgroup.center (L ⧸ aschbacherSolvableCore 3 L)) := hq.2.1
  have : Nontrivial (L ⧸ aschbacherSolvableCore 3 L) :=
    (QuotientGroup.mk_surjective (s := Subgroup.center (L ⧸ aschbacherSolvableCore 3 L))).nontrivial
  have : Nontrivial (Sec12.lBar c L) := η.symm.surjective.nontrivial
  exact (Subgroup.nontrivial_iff_ne_bot _).mp this

theorem mem_of_isHeisCentral (h : Sec13Data G A c L)
    (hH : Sec4.IsHeisCentral (lBarA c L A) (L ⧸ aschbacherSolvableCore 3 L)) : c ∈ L := by
  obtain ⟨U, V, hUV, hcomm, hU, ⟨eV⟩, hcard⟩ := hH
  set Λ := (Sec12.lBar c L).subgroupOf (lBarA c L A) with hΛ
  have hZU : (Subgroup.center U).map U.subtype = U ⊓ V := by
    symm
    apply Subgroup.eq_of_le_of_card_ge
    · rintro w ⟨hwU, hwV⟩
      refine ⟨⟨w, hwU⟩, Subgroup.mem_center_iff.mpr fun u => Subtype.ext ?_, rfl⟩
      exact hcomm u u.2 w hwV
    · rw [hcard, Subgroup.card_map_of_injective U.subtype_injective, hU.1.2.2.2]
  let φ : U × V →* lBarA c L A := MonoidHom.noncommCoprod U.subtype V.subtype
    (fun u v => hcomm u u.2 v v.2)
  have hφapp : ∀ y : U × V, φ y = (y.1 : lBarA c L A) * y.2 := fun y => rfl
  have hφ : ∀ x : lBarA c L A, ∃ y : U × V, φ y = x := by
    have hrange : φ.range = ⊤ := by
      rw [eq_top_iff, ← hUV, sup_le_iff]
      constructor
      · intro u hu
        exact ⟨(⟨u, hu⟩, 1), by rw [hφapp]; simp⟩
      · intro v hv
        exact ⟨(1, ⟨v, hv⟩), by rw [hφapp]; simp⟩
    intro x
    exact MonoidHom.mem_range.mp (hrange ▸ Subgroup.mem_top x)
  have hZ : Subgroup.center (lBarA c L A) ≤ V := by
    intro x hx
    obtain ⟨⟨u, v⟩, rfl⟩ := hφ x
    rw [hφapp]
    have huZ : (u : lBarA c L A) ∈ (Subgroup.center U).map U.subtype := by
      refine ⟨u, Subgroup.mem_center_iff.mpr fun u' => Subtype.ext ?_, rfl⟩
      have h1 := Subgroup.mem_center_iff.mp hx (u' : lBarA c L A)
      rw [hφapp] at h1
      have h2 : (v : lBarA c L A) * u' = u' * v := (hcomm u' u'.2 v v.2).symm
      have : (u' : lBarA c L A) * u * v = u * u' * v := by
        calc (u' : lBarA c L A) * u * v = u' * (u * v) := by group
          _ = u * v * u' := h1
          _ = u * (v * u') := by group
          _ = u * (u' * v) := by rw [h2]
          _ = u * u' * v := by group
      exact mul_right_cancel this
    rw [hZU] at huZ
    exact V.mul_mem huZ.2 v.2
  have hcommV : commutator (lBarA c L A) ≤ V := by
    rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    obtain ⟨⟨u, v⟩, rfl⟩ := hφ x
    obtain ⟨⟨u', v'⟩, rfl⟩ := hφ y
    rw [← map_commutatorElement, hφapp]
    have h1 : ((⁅(u, v), (u', v')⁆ : U × V).1 : lBarA c L A) ∈ V := by
      have h2 : (⁅u, u'⁆ : U) ∈ commutator U :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
      rw [hU.1.2.1] at h2
      have h3 : ((⁅u, u'⁆ : U) : lBarA c L A) ∈ (Subgroup.center U).map U.subtype := ⟨_, h2, rfl⟩
      rw [hZU] at h3
      exact h3.2
    exact V.mul_mem h1 (⁅(u, v), (u', v')⁆ : U × V).2.2
  have hΛperf : Group.IsPerfect Λ := by
    have := isPerfect_lBar h
    exact Group.IsPerfect.ofSurjective
      (f := (Subgroup.subgroupOfEquivOfLe lBar_le_lBarA).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe lBar_le_lBarA).symm.surjective
  have hΛV : Λ ≤ V := by
    have h1 : (⊤ : Subgroup Λ).map Λ.subtype = Λ := by
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    calc Λ = (commutator Λ).map Λ.subtype := by rw [hΛperf.commutator_eq_top, h1]
      _ = ⁅Λ, Λ⁆ := by rw [commutator_def, Subgroup.map_commutator, h1]
      _ ≤ commutator (lBarA c L A) := Subgroup.commutator_mono le_top le_top
      _ ≤ V := hcommV
  have hVq : IsQuasisimple V := LocalCores.isQuasisimple_of_mulEquiv eV.symm
    (Sec6.isQuasisimple_of_mem_thetaComponentsAt h.mem_thetaComponentsAt)
  have hΛn : (Λ.subgroupOf V).Normal := (lBar_normal h).subgroupOf V
  have hVΛ : V ≤ Λ := by
    rcases LocalCores.quasisimple_normal_subgroups hVq hΛn with htop | hcen
    · intro v hv
      have : (⟨v, hv⟩ : V) ∈ Λ.subgroupOf V := htop ▸ Subgroup.mem_top _
      exact this
    · exfalso
      have hab : ∀ x y : Λ, x * y = y * x := by
        intro x y
        have hx : (⟨x, hΛV x.2⟩ : V) ∈ Subgroup.center V := hcen x.2
        have := Subgroup.mem_center_iff.mp hx ⟨y, hΛV y.2⟩
        exact Subtype.ext (congrArg Subtype.val this).symm
      have hbot : commutator Λ = ⊥ := by
        rw [commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
        intro x _
        rw [Subgroup.mem_centralizer_iff]
        intro y _
        exact hab y x
      rw [hΛperf.commutator_eq_top] at hbot
      apply lBar_ne_bot h
      rw [eq_bot_iff]
      intro x hx
      have hxΛ : (⟨x, lBar_le_lBarA hx⟩ : lBarA c L A) ∈ Λ := hx
      have h1 : (⟨⟨x, lBar_le_lBarA hx⟩, hxΛ⟩ : Λ) ∈ (⊥ : Subgroup Λ) :=
        hbot ▸ Subgroup.mem_top _
      rw [Subgroup.mem_bot] at h1
      have h2 := congrArg (fun y : Λ => ((y : lBarA c L A) :
        Subgroup.normalizer (Subgroup.zpowers c : Set G) ⧸
          aschbacherSolvableCore 3 (Subgroup.normalizer (Subgroup.zpowers c : Set G)))) h1
      simpa using h2
  exact mem_of_mkC_mem h (hVΛ (hZ (mkC_mem_center h)))

end Bar

end CFSG.RankThree.PartTwo.Sec13
