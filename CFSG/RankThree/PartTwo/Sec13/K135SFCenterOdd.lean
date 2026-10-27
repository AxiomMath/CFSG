module

public import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.RankThree.PartTwo.Sec13.K135SF

open CFSG

private theorem sf_center_normal_map_of_characteristic {N : Type*} [Group N] (Q : Subgroup N) [Q.Normal]
    (P : Subgroup Q) [P.Characteristic] : (P.map Q.subtype).Normal := by
  refine ⟨?_⟩
  rintro _ ⟨r, hr, rfl⟩ g
  have hchar : P.Characteristic := inferInstance
  refine ⟨MulAut.conjNormal g r, ?_, ?_⟩
  · exact (Subgroup.characteristic_iff_le_comap.mp hchar (MulAut.conjNormal g)) hr
  · simp [MulAut.conjNormal_apply]

theorem eq_bot_of_normal_two_group {M : Type*} [Group M] [Finite M] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (R : Subgroup M) [R.Normal] (hRp : Nat.Coprime p (Nat.card R))
    (hR : ∀ K : Subgroup M, K.Normal → Nat.Coprime p (Nat.card K) → K ≤ R)
    (T : Subgroup (M ⧸ R)) [T.Normal] (hT : ∃ k : ℕ, Nat.card T = 2 ^ k) : T = ⊥ := by
  obtain ⟨k, hk⟩ := hT
  have hfs : Function.Surjective (QuotientGroup.mk' R : M →* M ⧸ R) :=
    QuotientGroup.mk'_surjective R
  set K : Subgroup M := T.comap (QuotientGroup.mk' R : M →* M ⧸ R) with hKdef
  have hKn : K.Normal := inferInstance
  have hRK : R ≤ K := by
    intro r hr
    show (QuotientGroup.mk' R : M →* M ⧸ R) r ∈ T
    have h1 : (QuotientGroup.mk' R : M →* M ⧸ R) r = 1 := (QuotientGroup.eq_one_iff r).mpr hr
    rw [h1]
    exact T.one_mem
  set φ : K →* T :=
    ((QuotientGroup.mk' R : M →* M ⧸ R).comp K.subtype).codRestrict T (fun x => x.2) with hφdef
  have hφs : Function.Surjective φ := by
    rintro ⟨t, ht⟩
    obtain ⟨m, rfl⟩ := hfs t
    exact ⟨⟨m, ht⟩, rfl⟩
  have hker : φ.ker = R.subgroupOf K := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← QuotientGroup.eq_one_iff]
    constructor
    · intro h
      exact congrArg Subtype.val h
    · intro h
      exact Subtype.ext h
  have hquot : Nat.card (K ⧸ R.subgroupOf K) = Nat.card T := by
    rw [← hker]
    exact Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hφs).toEquiv
  have hKcard : Nat.card K = Nat.card T * Nat.card R := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (R.subgroupOf K)
    rw [hquot, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRK).toEquiv] at h1
    exact h1
  have hp2' : Nat.Coprime p 2 := (Nat.coprime_primes hp Nat.prime_two).mpr hp2
  have hKp : Nat.Coprime p (Nat.card K) := by
    rw [hKcard]
    refine Nat.Coprime.mul_right ?_ hRp
    rw [hk]
    exact Nat.Coprime.pow_right k hp2'
  have hKR : K ≤ R := hR K hKn hKp
  have hle : T ≤ ⊥ := by
    calc T = K.map (QuotientGroup.mk' R : M →* M ⧸ R) :=
          (Subgroup.map_comap_eq_self_of_surjective hfs T).symm
      _ ≤ R.map (QuotientGroup.mk' R : M →* M ⧸ R) := Subgroup.map_mono hKR
      _ = ⊥ := QuotientGroup.map_mk'_self R
  exact le_bot_iff.mp hle

theorem comm_layer_of_center {N : Type*} [Group N] [Finite N] {J : Subgroup N}
    (hJ : CFSG.IsComponent J) {x : N} (hxJ : x ∈ J) (hxc : ∀ j ∈ J, j * x = x * j) :
    ∀ g ∈ CFSG.layer N, g * x = x * g := by
  have hle : CFSG.layer N ≤ Subgroup.centralizer ({x} : Set N) := by
    rw [CFSG.layer.eq_sSup]
    refine sSup_le fun K hK => ?_
    intro k hk
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    rcases CFSG.LocalCores.distinct_components_commute hJ hK with hJK | hJK
    · rw [← hJK] at hk
      exact (hxc k hk).symm
    · have hxK : x ∈ Subgroup.centralizer (K : Set N) :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mp hJK hxJ
      exact (Subgroup.mem_centralizer_iff.mp hxK k hk).symm
  intro g hg
  exact (Subgroup.mem_centralizer_iff.mp (hle hg) x (Set.mem_singleton x)).symm

theorem map_center_le_of_component {N : Type*} [Group N] [Finite N] {J : Subgroup N}
    (hJ : CFSG.IsComponent J) (hJW : J ≤ CFSG.layer N) :
    (Subgroup.center J).map J.subtype ≤
      (Subgroup.center (CFSG.layer N)).map (CFSG.layer N).subtype := by
  rintro _ ⟨x, hx, rfl⟩
  refine Subgroup.mem_map.mpr ⟨⟨(x : N), hJW x.2⟩, ?_, rfl⟩
  have hxc : ∀ j ∈ J, j * (x : N) = (x : N) * j := fun j hj =>
    congrArg Subtype.val (Subgroup.mem_center_iff.mp hx ⟨j, hj⟩)
  rw [Subgroup.mem_center_iff]
  intro g
  apply Subtype.ext
  exact comm_layer_of_center hJ x.2 hxc (g : N) g.2

theorem comm_of_mem_map_center {N : Type*} [Group N] (W : Subgroup N) {a b : N}
    (ha : a ∈ (Subgroup.center W).map W.subtype) (hb : b ∈ (Subgroup.center W).map W.subtype) :
    a * b = b * a := by
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp ha
  obtain ⟨z, -, rfl⟩ := Subgroup.mem_map.mp hb
  exact (congrArg Subtype.val (Subgroup.mem_center_iff.mp hy z)).symm

theorem not_two_dvd_card_map_center {N : Type*} [Group N] [Finite N] (W : Subgroup N) [W.Normal]
    (hN2 : ∀ T : Subgroup N, T.Normal → (∃ k : ℕ, Nat.card T = 2 ^ k) → T = ⊥) :
    ¬ 2 ∣ Nat.card ((Subgroup.center W).map W.subtype) := by
  set Q : Subgroup N := (Subgroup.center W).map W.subtype with hQdef
  haveI hQn : Q.Normal := sf_center_normal_map_of_characteristic W (Subgroup.center W)
  haveI hQc : IsMulCommutative Q :=
    ⟨⟨fun a b => Subtype.ext (comm_of_mem_map_center W a.2 b.2)⟩⟩
  haveI hfin : Finite (Sylow 2 Q) :=
    Finite.of_injective (fun P : Sylow 2 Q => (P : Set Q)) SetLike.coe_injective
  let S : Sylow 2 Q := default
  have hSn : (S : Subgroup Q).Normal := inferInstance
  haveI hSc : (S : Subgroup Q).Characteristic := Sylow.characteristic_of_normal S hSn
  haveI hPn : ((S : Subgroup Q).map Q.subtype).Normal :=
    sf_center_normal_map_of_characteristic Q (S : Subgroup Q)
  have hP2 : ∃ k : ℕ, Nat.card ((S : Subgroup Q).map Q.subtype) = 2 ^ k := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp S.isPGroup'
    exact ⟨k, by rw [Subgroup.card_subtype Q (S : Subgroup Q)]; exact hk⟩
  have hPbot : (S : Subgroup Q).map Q.subtype = ⊥ := hN2 _ hPn hP2
  have hSone : Nat.card (S : Subgroup Q) = 1 := by
    have h := Subgroup.card_subtype Q (S : Subgroup Q)
    rw [hPbot, Subgroup.card_bot] at h
    exact h.symm
  have hpow : 2 ^ (Nat.card Q).factorization 2 = Nat.card (S : Subgroup Q) :=
    (Sylow.card_eq_multiplicity S).symm
  rw [hSone] at hpow
  have hf : (Nat.card Q).factorization 2 = 0 :=
    (Nat.pow_eq_one.mp hpow).resolve_left (by norm_num)
  intro h2
  have hQne : Nat.card Q ≠ 0 := Nat.card_pos.ne'
  have hpos := Nat.prime_two.factorization_pos_of_dvd hQne h2
  omega

theorem not_two_dvd_card_center_component {M : Type*} [Group M] [Finite M] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (R : Subgroup M) [R.Normal] (hRp : Nat.Coprime p (Nat.card R))
    (hR : ∀ K : Subgroup M, K.Normal → Nat.Coprime p (Nat.card K) → K ≤ R)
    (J : Subgroup (M ⧸ R)) (hJ : CFSG.IsComponent J) : ¬ 2 ∣ Nat.card (Subgroup.center J) := by
  haveI hWc : (CFSG.layer (M ⧸ R)).Characteristic := CFSG.LocalCores.layer_characteristic
  haveI hWn : (CFSG.layer (M ⧸ R)).Normal := inferInstance
  have hN2 : ∀ T : Subgroup (M ⧸ R), T.Normal → (∃ k : ℕ, Nat.card T = 2 ^ k) → T = ⊥ :=
    fun T hT hk => eq_bot_of_normal_two_group hp hp2 R hRp hR T hk
  have hQodd := not_two_dvd_card_map_center (CFSG.layer (M ⧸ R)) hN2
  have hJW : J ≤ CFSG.layer (M ⧸ R) := by
    rw [CFSG.layer.eq_sSup]
    exact le_sSup hJ
  have hdvd := Subgroup.card_dvd_of_le (map_center_le_of_component hJ hJW)
  rw [Subgroup.card_subtype J (Subgroup.center J)] at hdvd
  intro h2
  exact hQodd (h2.trans hdvd)

end CFSG.RankThree.PartTwo.Sec13.K135SF
