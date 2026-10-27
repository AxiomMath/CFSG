module

public import CFSG.Quasithin.Vol2.GoldschmidtF431L3LieAbs

public section

namespace CFSG.Quasithin.H13.F431.L3

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open

section Generic

variable {G : Type} [Group G]

theorem exists_central_of_normalized [Finite G] {R Z : Subgroup G} (hR : IsPGroup 2 R)
    (hZR : Z ≤ R) (hZn : ∀ r ∈ R, ∀ z ∈ Z, r * z * r⁻¹ ∈ Z) (hZne : ∃ z ∈ Z, z ≠ 1) :
    ∃ z ∈ Z, z ≠ 1 ∧ ∀ r ∈ R, r * z = z * r := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent R := hR.isNilpotent
  set Z0 : Subgroup R := Z.subgroupOf R with hZ0
  have hZ0n : Z0.Normal := by
    refine ⟨fun x hx g => ?_⟩
    have hx' : (x : G) ∈ Z := Subgroup.mem_subgroupOf.mp hx
    exact Subgroup.mem_subgroupOf.mpr (by simpa using hZn g g.2 x hx')
  obtain ⟨z0, hz0Z, hz01⟩ := hZne
  have hZ0ne : Z0 ≠ ⊥ := by
    intro h
    have hmem : (⟨z0, hZR hz0Z⟩ : R) ∈ Z0 := Subgroup.mem_subgroupOf.mpr hz0Z
    rw [h, Subgroup.mem_bot] at hmem
    exact hz01 (congrArg Subtype.val hmem)
  have hinf := Group.IsNilpotent.inf_center_ne_bot_of_normal hZ0ne
  obtain ⟨a, ha⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hinf
  have haC : (a : R) ∈ Subgroup.center R := a.2.2
  refine ⟨((a : R) : G), Subgroup.mem_subgroupOf.mp (a.2.1 : (a : R) ∈ Z0), ?_, fun r hr => ?_⟩
  · intro h
    apply ha
    apply Subtype.ext
    apply Subtype.ext
    exact h
  · have := Subgroup.mem_center_iff.mp haC ⟨r, hr⟩
    exact congrArg Subtype.val this

theorem le_of_pgroup_of_normalizer [Finite G] {T J X : Subgroup G} (hSyl : IsSylowTwoOf T J)
    (hTn : J ≤ Subgroup.normalizer (T : Set G)) (hXJ : X ≤ J) (hX : IsPGroup 2 X) : X ≤ T := by
  obtain ⟨x, hx, hXx⟩ := F7.isSylowTwoOf_exists_conj_le hSyl hXJ hX
  rwa [conjSub_eq_of_mem_normalizer (hTn hx)] at hXx

theorem card_le_card_inf_centralizer_sq [Finite G] {V : Subgroup G} {f : G}
    (hV : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x) (hV2 : ∀ x ∈ V, x * x = 1) (hf2 : f * f = 1)
    (hf : ∀ v ∈ V, f * v * f⁻¹ ∈ V) :
    Nat.card V ≤ Nat.card ↥(V ⊓ Subgroup.centralizer ({f} : Set G)) ^ 2 := by
  classical
  set C : Subgroup G := V ⊓ Subgroup.centralizer ({f} : Set G) with hC
  have hfinv : f⁻¹ = f := inv_eq_of_mul_eq_one_right hf2
  let φ : ↥V →* ↥V :=
    { toFun := fun v => ⟨f * v * f⁻¹ * v, V.mul_mem (hf v v.2) v.2⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := by
        intro v w
        apply Subtype.ext
        show f * ((v : G) * w) * f⁻¹ * ((v : G) * w) =
          (f * v * f⁻¹ * v) * (f * w * f⁻¹ * w)
        have hc : (v : G) * (f * w * f⁻¹) = (f * w * f⁻¹) * v := hV _ v.2 _ (hf w w.2)
        calc f * ((v : G) * w) * f⁻¹ * ((v : G) * w)
            = (f * v * f⁻¹) * (f * w * f⁻¹) * v * w := by group
          _ = (f * v * f⁻¹) * ((f * w * f⁻¹) * v) * w := by group
          _ = (f * v * f⁻¹) * (v * (f * w * f⁻¹)) * w := by rw [hc]
          _ = (f * v * f⁻¹ * v) * (f * w * f⁻¹ * w) := by group }
  have hφ : ∀ v : ↥V, ((φ v : ↥V) : G) = f * v * f⁻¹ * v := fun v => rfl
  have h1 : Nat.card φ.ker * Nat.card φ.range = Nat.card V := by
    rw [← Subgroup.index_ker φ]
    exact Subgroup.card_mul_index _
  have hkerC : ∀ v : ↥φ.ker, ((v : ↥V) : G) ∈ C := by
    intro v
    refine ⟨v.1.2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have h := congrArg Subtype.val (MonoidHom.mem_ker.mp v.2)
    rw [hφ] at h
    have hv2 : ((v : ↥V) : G) * ((v : ↥V) : G) = 1 := hV2 _ v.1.2
    have hvinv : ((v : ↥V) : G)⁻¹ = ((v : ↥V) : G) := inv_eq_of_mul_eq_one_right hv2
    have h' : f * ((v : ↥V) : G) * f⁻¹ = ((v : ↥V) : G) := by
      have := mul_eq_one_iff_eq_inv.mp h
      rw [this, hvinv]
    exact (mul_inv_eq_iff_eq_mul.mp h').symm
  have hrangeC : ∀ y : ↥φ.range, ((y : ↥V) : G) ∈ C := by
    rintro ⟨_, v, rfl⟩
    refine ⟨(φ v).2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    rw [hφ]
    have hc : (v : G) * (f * v * f⁻¹) = (f * v * f⁻¹) * v := hV _ v.2 _ (hf v v.2)
    rw [hfinv] at hc ⊢
    have hc' : f * v * f * v = v * f * v * f := by
      calc f * (v : G) * f * v = (f * v * f) * v := by group
        _ = v * (f * v * f) := hc.symm
        _ = v * f * v * f := by group
    calc f * (v : G) * f * v * f = (v * f * v * f) * f := by rw [hc']
      _ = (v : G) * f * v * (f * f) := by group
      _ = (f * f) * v * f * v := by rw [hf2, mul_one, one_mul]
      _ = f * (f * v * f * v) := by group
  have hker : Nat.card φ.ker ≤ Nat.card C :=
    Nat.card_le_card_of_injective (fun v => (⟨((v : ↥V) : G), hkerC v⟩ : ↥C)) (fun a b hab =>
      Subtype.ext (Subtype.ext (congrArg (fun x : ↥C => (x : G)) hab)))
  have hrange : Nat.card φ.range ≤ Nat.card C :=
    Nat.card_le_card_of_injective (fun y => (⟨((y : ↥V) : G), hrangeC y⟩ : ↥C)) (fun a b hab =>
      Subtype.ext (Subtype.ext (congrArg (fun x : ↥C => (x : G)) hab)))
  calc Nat.card V = Nat.card φ.ker * Nat.card φ.range := h1.symm
    _ ≤ Nat.card C * Nat.card C := Nat.mul_le_mul hker hrange
    _ = Nat.card C ^ 2 := (sq _).symm

theorem commute_of_isCyclic {B : Subgroup G} [IsCyclic B] {x y : G} (hx : x ∈ B) (hy : y ∈ B) :
    x * y = y * x := by
  have := (IsCyclic.commGroup (α := ↥B)).mul_comm ⟨x, hx⟩ ⟨y, hy⟩
  exact congrArg Subtype.val this

theorem eq_of_sq_eq_one_of_isCyclic {B : Subgroup G} [IsCyclic B] [Finite B] {s t : G}
    (hs : s ∈ B) (ht : t ∈ B) (hs2 : s * s = 1) (ht2 : t * t = 1) (hs1 : s ≠ 1) (ht1 : t ≠ 1) :
    s = t := by
  classical
  have : Fintype B := Fintype.ofFinite B
  by_contra hne
  set s' : B := ⟨s, hs⟩ with hs'
  set t' : B := ⟨t, ht⟩ with ht'
  have hs'1 : s' ≠ 1 := fun h => hs1 (congrArg Subtype.val h)
  have ht'1 : t' ≠ 1 := fun h => ht1 (congrArg Subtype.val h)
  have hst : s' ≠ t' := fun h => hne (congrArg Subtype.val h)
  have h3 : ({1, s', t'} : Finset B).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair hst]
    simp [hs'1.symm, ht'1.symm]
  have hsub : ({1, s', t'} : Finset B) ⊆ Finset.univ.filter (fun a : B => a ^ 2 = 1) := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases ha with rfl | rfl | rfl
    · simp
    · apply Subtype.ext
      simpa [pow_two] using hs2
    · apply Subtype.ext
      simpa [pow_two] using ht2
  have h1 := IsCyclic.card_pow_eq_one_le (α := B) (n := 2) (by norm_num)
  have h2 := Finset.card_le_card hsub
  have : (Finset.univ.filter (fun a : B => a ^ 2 = 1)).card ≤ 2 := by simpa using h1
  omega

end Generic

section ProdSub

variable {G : Type} [Group G]

@[expose] def prodSub (A B : Subgroup G) (h : B ≤ Subgroup.normalizer (A : Set G)) :
    Subgroup G where
  carrier := {x | ∃ a ∈ A, ∃ b ∈ B, x = a * b}
  one_mem' := ⟨1, A.one_mem, 1, B.one_mem, (mul_one 1).symm⟩
  mul_mem' := by
    rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
    refine ⟨a * (b * a' * b⁻¹), A.mul_mem ha ?_, b * b', B.mul_mem hb hb', by group⟩
    exact (Subgroup.mem_normalizer_iff.mp (h hb) a').mp ha'
  inv_mem' := by
    rintro _ ⟨a, ha, b, hb, rfl⟩
    refine ⟨b⁻¹ * a⁻¹ * b, ?_, b⁻¹, B.inv_mem hb, by group⟩
    have := (Subgroup.mem_normalizer_iff.mp (h (B.inv_mem hb)) a⁻¹).mp (A.inv_mem ha)
    simpa using this

theorem left_le_prodSub {A B : Subgroup G} (h : B ≤ Subgroup.normalizer (A : Set G)) :
    A ≤ prodSub A B h := fun a ha => ⟨a, ha, 1, B.one_mem, (mul_one a).symm⟩

theorem right_le_prodSub {A B : Subgroup G} (h : B ≤ Subgroup.normalizer (A : Set G)) :
    B ≤ prodSub A B h := fun b hb => ⟨1, A.one_mem, b, hb, (one_mul b).symm⟩

theorem card_prodSub [Finite G] {A B : Subgroup G} (h : B ≤ Subgroup.normalizer (A : Set G))
    (hdis : ∀ x ∈ A, x ∈ B → x = 1) :
    Nat.card (prodSub A B h) = Nat.card A * Nat.card B :=
  card_eq_mul_of_split (left_le_prodSub h) (right_le_prodSub h) hdis fun _ hx => hx

variable {A B : Subgroup G} (h : B ≤ Subgroup.normalizer (A : Set G))

include h

theorem prodSub_commutator_mem (hB : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) {x y : G}
    (hx : x ∈ prodSub A B h) (hy : y ∈ prodSub A B h) : x * y * x⁻¹ * y⁻¹ ∈ A := by
  obtain ⟨u, hu, t, ht, rfl⟩ := hx
  obtain ⟨v, hv, s, hs, rfl⟩ := hy
  have hts : t * s = s * t := hB t ht s hs
  have ha : t * v * t⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp (h ht) v).mp hv
  have hb : s * u * s⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp (h hs) u).mp hu
  have e1 : u * t * (v * s) = (u * (t * v * t⁻¹)) * (t * s) := by group
  have e2 : v * s * (u * t) = (v * (s * u * s⁻¹)) * (t * s) := by
    calc v * s * (u * t) = (v * (s * u * s⁻¹)) * (s * t) := by group
      _ = (v * (s * u * s⁻¹)) * (t * s) := by rw [← hts]
  have e3 : u * t * (v * s) * (u * t)⁻¹ * (v * s)⁻¹ =
      (u * t * (v * s)) * (v * s * (u * t))⁻¹ := by group
  rw [e3, e1, e2]
  have e4 : (u * (t * v * t⁻¹)) * (t * s) * ((v * (s * u * s⁻¹)) * (t * s))⁻¹ =
      u * (t * v * t⁻¹) * (v * (s * u * s⁻¹))⁻¹ := by group
  rw [e4]
  exact A.mul_mem (A.mul_mem hu ha) (A.inv_mem (A.mul_mem hv hb))

theorem prodSub_cyc_mem (hdis : ∀ x ∈ A, x ∈ B → x = 1)
    (hB : ∀ s ∈ B, ∀ t ∈ B, s * s = 1 → t * t = 1 → s ≠ 1 → t ≠ 1 → s = t) {x y : G}
    (hx : x ∈ prodSub A B h) (hy : y ∈ prodSub A B h) (hxA : x ∉ A) (hyA : y ∉ A)
    (hx2 : x * x ∈ A) (hy2 : y * y ∈ A) : x⁻¹ * y ∈ A := by
  obtain ⟨u, hu, t, ht, rfl⟩ := hx
  obtain ⟨v, hv, s, hs, rfl⟩ := hy
  have hsq : ∀ (u : G) (_ : u ∈ A) (t : G) (_ : t ∈ B), u * t * (u * t) ∈ A → t * t = 1 := by
    intro u hu t ht hx2
    have ha : t * u * t⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp (h ht) u).mp hu
    have e : t * t = (u * (t * u * t⁻¹))⁻¹ * (u * t * (u * t)) := by group
    refine hdis _ ?_ (B.mul_mem ht ht)
    rw [e]
    exact A.mul_mem (A.inv_mem (A.mul_mem hu ha)) hx2
  have ht2 : t * t = 1 := hsq u hu t ht hx2
  have hs2 : s * s = 1 := hsq v hv s hs hy2
  have ht1 : t ≠ 1 := by
    rintro rfl
    exact hxA (by simpa using hu)
  have hs1 : s ≠ 1 := by
    rintro rfl
    exact hyA (by simpa using hv)
  have hts : t = s := hB t ht s hs ht2 hs2 ht1 hs1
  subst hts
  have := (Subgroup.mem_normalizer_iff.mp (h (B.inv_mem ht)) (u⁻¹ * v)).mp
    (A.mul_mem (A.inv_mem hu) hv)
  have e : (u * t)⁻¹ * (v * t) = t⁻¹ * (u⁻¹ * v) * t⁻¹⁻¹ := by group
  rw [e]
  exact this

end ProdSub

section Skeleton

variable {H : Type} [Group H]

structure OutSkel (I T0 B0 : Subgroup H) : Prop where
  sylow : IsSylowTwoOf T0 I
  B0_le_I : B0 ≤ I
  B0_le_N : B0 ≤ Subgroup.normalizer (T0 : Set H)
  B0_odd : Odd (Nat.card B0)
  centS : ∀ x ∈ T0, (∀ b ∈ B0, x * b = b * x) → x = 1
  card_N : Nat.card ↥(Subgroup.normalizer (T0 : Set H) ⊓ I) = Nat.card T0 * Nat.card B0

@[expose] def Bt (T0 B0 : Subgroup H) : Subgroup H :=
  Subgroup.normalizer (T0 : Set H) ⊓ Subgroup.normalizer (B0 : Set H)

theorem le_normalizer_of_le_Bt {T0 B0 Tt : Subgroup H} (hTt : Tt ≤ Bt T0 B0) :
    Tt ≤ Subgroup.normalizer (T0 : Set H) := hTt.trans inf_le_left

variable {I T0 B0 : Subgroup H} [Finite H] (S : OutSkel I T0 B0)

include S

omit [Finite H] in
theorem OutSkel.T0_le_I : T0 ≤ I := S.sylow.1

omit [Finite H] in
theorem OutSkel.T0_pgroup : IsPGroup 2 T0 := S.sylow.2.1

theorem OutSkel.T0_inf : ∀ x ∈ T0, x ∈ B0 → x = 1 := fun _ hx hxB =>
  eq_one_of_pgroup_of_odd S.T0_pgroup S.B0_odd hx hxB

theorem OutSkel.mul [I.Normal] :
    ∀ n ∈ Subgroup.normalizer (T0 : Set H), ∃ t ∈ T0, ∃ b ∈ Bt T0 B0, n = t * b :=
  fun _ hn => star_mul S.T0_le_I S.B0_le_I S.B0_le_N S.card_N
    (by
      obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp S.T0_pgroup
      rw [hk]
      exact Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr S.B0_odd)) hn

theorem OutSkel.disj : ∀ x ∈ T0, x ∈ Bt T0 B0 → x = 1 := fun _ hx hxB =>
  star_disjoint S.B0_le_N S.T0_inf S.centS hx hxB.2

theorem OutSkel.card_N' [I.Normal] :
    Nat.card ↥(Subgroup.normalizer (T0 : Set H)) = Nat.card T0 * Nat.card ↥(Bt T0 B0) :=
  card_eq_mul_of_split Subgroup.le_normalizer (inf_le_left : Bt T0 B0 ≤ _) S.disj
    (fun n hn => S.mul n hn)

theorem OutSkel.le_of_pgroup {X : Subgroup H} (hX : X ≤ Subgroup.normalizer (T0 : Set H) ⊓ I)
    (hp : IsPGroup 2 X) : X ≤ T0 :=
  le_of_pgroup_of_normalizer (J := Subgroup.normalizer (T0 : Set H) ⊓ I)
    (A4.isSylowTwoOf_mono S.sylow (le_inf Subgroup.le_normalizer S.T0_le_I) inf_le_right)
    inf_le_left hX hp

theorem OutSkel.isSylow_top [I.Normal] {T : Subgroup H}
    (hT : IsSylowTwoOf T (Subgroup.normalizer (T0 : Set H))) (hT0 : T0 ≤ T) :
    IsSylowTwoOf T ⊤ := by
  obtain ⟨S₁, hS₁, hTS⟩ := A4.exists_isSylowTwoOf_ge (H := ⊤) (le_top : T ≤ ⊤) hT.2.1
  have hS₁p : IsPGroup 2 S₁ := hS₁.2.1
  have hinf : S₁ ⊓ I = T0 :=
    eq_of_isSylowTwoOf_of_isPGroup S.sylow (le_inf (hT0.trans hTS) S.T0_le_I) inf_le_right
      (hS₁p.to_inf_left)
  have hS₁N : S₁ ≤ Subgroup.normalizer (T0 : Set H) := by
    intro s hs
    apply mem_normalizer_of_conjSub_eq
    rw [← hinf, conjSub_inf, conjSub_eq_of_mem_normalizer (Subgroup.le_normalizer hs),
      conjSub_eq_of_normal_subgroup (Inn := I)]
  have : S₁ = T := eq_of_isSylowTwoOf_of_isPGroup hT hTS hS₁N hS₁p
  rw [← this]
  exact hS₁

theorem OutSkel.sylow_N_of_odd [I.Normal] (hodd : Odd (Nat.card ↥(Bt T0 B0))) :
    IsSylowTwoOf T0 (Subgroup.normalizer (T0 : Set H)) := by
  refine F7.isSylowTwoOf_of_relIndex Subgroup.le_normalizer S.T0_pgroup ?_
  have h1 := Subgroup.relIndex_mul_card T0 (Subgroup.normalizer (T0 : Set H))
  rw [inf_of_le_left Subgroup.le_normalizer, S.card_N'] at h1
  have hpos : 0 < Nat.card T0 := Nat.card_pos
  have h2 : T0.relIndex (Subgroup.normalizer (T0 : Set H)) = Nat.card ↥(Bt T0 B0) := by
    have : T0.relIndex (Subgroup.normalizer (T0 : Set H)) * Nat.card T0 =
        Nat.card ↥(Bt T0 B0) * Nat.card T0 := by rw [h1, mul_comm]
    exact Nat.eq_of_mul_eq_mul_right hpos this
  rw [h2]
  exact Nat.not_even_iff_odd.mpr hodd ∘ even_iff_two_dvd.mpr

theorem OutSkel.even_of_index [I.Normal] (heven : ¬ Odd I.index) :
    ¬ Odd (Nat.card ↥(Bt T0 B0)) := by
  intro hodd
  have hS := S.isSylow_top (S.sylow_N_of_odd hodd) le_rfl
  apply heven
  have h1 : ¬ 2 ∣ T0.index := by
    have := F7.isSylowTwoOf_odd_relIndex hS
    rwa [Subgroup.relIndex_top_right] at this
  have h2 : I.index ∣ T0.index := Subgroup.index_dvd_of_le S.T0_le_I
  have h3 : ¬ 2 ∣ I.index := fun h => h1 (dvd_trans h h2)
  exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp h3)

theorem OutSkel.sylow_prod [I.Normal] {Tt : Subgroup H} (hTt : IsSylowTwoOf Tt (Bt T0 B0)) :
    IsSylowTwoOf (prodSub T0 Tt (le_normalizer_of_le_Bt hTt.1))
      (Subgroup.normalizer (T0 : Set H)) := by
  have hN := le_normalizer_of_le_Bt hTt.1
  have hdis : ∀ x ∈ T0, x ∈ Tt → x = 1 := fun x hx hxT => S.disj x hx (hTt.1 hxT)
  have hcT := card_prodSub hN hdis
  have hTp : IsPGroup 2 (prodSub T0 Tt hN) := by
    obtain ⟨a, ha⟩ := (IsPGroup.iff_card).mp S.T0_pgroup
    obtain ⟨b, hb⟩ := (IsPGroup.iff_card).mp hTt.2.1
    exact IsPGroup.of_card (n := a + b) (by rw [hcT, ha, hb, pow_add])
  have hTN : prodSub T0 Tt hN ≤ Subgroup.normalizer (T0 : Set H) := by
    rintro _ ⟨a, ha, b, hb, rfl⟩
    exact Subgroup.mul_mem _ (Subgroup.le_normalizer ha) (hN hb)
  refine F7.isSylowTwoOf_of_relIndex hTN hTp ?_
  have h1 := Subgroup.relIndex_mul_card (prodSub T0 Tt hN) (Subgroup.normalizer (T0 : Set H))
  have h2 := Subgroup.relIndex_mul_card Tt (Bt T0 B0)
  rw [inf_of_le_left hTN, S.card_N', hcT] at h1
  rw [inf_of_le_left hTt.1] at h2
  have hpos : 0 < Nat.card T0 := Nat.card_pos
  have hpos' : 0 < Nat.card Tt := Nat.card_pos
  have h3 : (prodSub T0 Tt hN).relIndex (Subgroup.normalizer (T0 : Set H)) =
      Tt.relIndex (Bt T0 B0) := by
    have h4 : (prodSub T0 Tt hN).relIndex (Subgroup.normalizer (T0 : Set H)) *
        (Nat.card T0 * Nat.card Tt) = Tt.relIndex (Bt T0 B0) * (Nat.card T0 * Nat.card Tt) := by
      calc _ = Nat.card T0 * Nat.card ↥(Bt T0 B0) := h1
        _ = Nat.card T0 * (Tt.relIndex (Bt T0 B0) * Nat.card Tt) := by rw [h2]
        _ = _ := by ring
    exact Nat.eq_of_mul_eq_mul_right (Nat.mul_pos hpos hpos') h4
  rw [h3]
  exact hTt.2.2

theorem OutSkel.pCore_le [I.Normal] {Z : Subgroup H} (hZ : Z = centerOf T0)
    (hZtrans : ∀ x ∈ Z, x ≠ 1 → ∀ y ∈ Z, y ≠ 1 → ∃ c ∈ B0, c * x * c⁻¹ = y)
    (hZne : ∃ z ∈ Z, z ≠ 1)
    (hout : ∀ b ∈ Subgroup.normalizer (T0 : Set H), (∃ k : ℕ, orderOf b = 2 ^ k) → b ∉ I →
      ¬ ∀ z ∈ Z, b * z = z * b) :
    pCoreOf 2 (Subgroup.normalizer (T0 : Set H)) ≤ T0 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N : Subgroup H := Subgroup.normalizer (T0 : Set H) with hN
  set R : Subgroup H := pCoreOf 2 N with hR
  have hR2 : IsPGroup 2 R := LieType.BorelTits.pCoreOf_isPGroup 2 N
  have hRN : R ≤ N := LieType.BorelTits.pCoreOf_le 2 N
  have hRnorm : N ≤ Subgroup.normalizer (R : Set H) := LieType.BorelTits.le_normalizer_pCoreOf 2 N
  have hT0R : T0 ≤ R := le_pCoreOf_of_le_normalizer Subgroup.le_normalizer le_rfl S.T0_pgroup
  have hZle : Z ≤ R := by
    rw [hZ]
    exact (inf_le_left : centerOf T0 ≤ T0).trans hT0R
  have hZn : ∀ r ∈ R, ∀ z ∈ Z, r * z * r⁻¹ ∈ Z := by
    intro r hr z hz
    have h1 : conjSub r Z = Z := by
      rw [hZ, ← centerOf_conjSub, conjSub_eq_of_mem_normalizer (hRN hr)]
    rw [← h1]
    exact mul_mem_conjSub hz
  intro r hr
  obtain ⟨t, ht, b, hb, rfl⟩ := S.mul r (hRN hr)
  have hbR : b ∈ R := by
    have := R.mul_mem (R.inv_mem (hT0R ht)) hr
    simpa using this
  have hcomm : ∀ c ∈ B0, b * c = c * b := by
    intro c hc
    have hcN : c ∈ N := S.B0_le_N hc
    have h1 : b * c * b⁻¹ ∈ B0 := (Subgroup.mem_normalizer_iff.mp hb.2 c).mp hc
    have h2 : c * b⁻¹ * c⁻¹ ∈ R := by
      have := (Subgroup.mem_normalizer_iff.mp (hRnorm hcN) b⁻¹).mp (R.inv_mem hbR)
      simpa [mul_assoc] using this
    have h3 : b * c * b⁻¹ * c⁻¹ ∈ B0 := B0.mul_mem h1 (B0.inv_mem hc)
    have h4 : b * c * b⁻¹ * c⁻¹ ∈ R := by
      have := R.mul_mem hbR h2
      simpa [mul_assoc] using this
    have h5 : b * c * b⁻¹ * c⁻¹ = 1 := eq_one_of_pgroup_of_odd hR2 S.B0_odd h4 h3
    calc b * c = b * c * b⁻¹ * c⁻¹ * (c * b) := by group
      _ = c * b := by rw [h5, one_mul]
  have hbZ : ∀ z ∈ Z, b * z = z * b := by
    obtain ⟨z0, hz0Z, hz01, hz0c⟩ := exists_central_of_normalized hR2 hZle hZn hZne
    intro z hz
    by_cases hz1 : z = 1
    · rw [hz1]; simp
    · obtain ⟨c, hc, hcz⟩ := hZtrans z0 hz0Z hz01 z hz hz1
      have hbc : Commute b c := hcomm c hc
      have hbz0 : Commute b z0 := hz0c b hbR
      have : Commute b z := by
        rw [← hcz]
        exact (hbc.mul_right hbz0).mul_right hbc.inv_right
      exact this
  by_cases hbI : b ∈ I
  · have hbT : b ∈ T0 :=
      S.le_of_pgroup (X := R ⊓ I) (inf_le_inf_right I hRN) hR2.to_inf_left ⟨hbR, hbI⟩
    have hb1 : b = 1 := S.centS b hbT hcomm
    rw [hb1, mul_one]
    exact ht
  · exfalso
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hR2) ⟨b, hbR⟩
    refine hout b hb.1 ⟨k, ?_⟩ hbI hbZ
    rw [← Subgroup.orderOf_mk b hbR]
    exact hk

theorem OutSkel.cent_mul [I.Normal] {f : H} (hf : f ∈ Bt T0 B0) {h : H}
    (hh : h ∈ Subgroup.normalizer (T0 : Set H) ⊓ Subgroup.centralizer ({f} : Set H)) :
    ∃ u ∈ T0 ⊓ Subgroup.centralizer ({f} : Set H),
      ∃ b ∈ Bt T0 B0 ⊓ Subgroup.centralizer ({f} : Set H), h = u * b := by
  obtain ⟨hN, hC⟩ := hh
  obtain ⟨t, ht, b, hb, rfl⟩ := S.mul h hN
  have hC' : t * b ∈ Subgroup.centralizer ({f} : Set H) := hC
  have hfC : (t * b) * f = f * (t * b) := Subgroup.mem_centralizer_singleton_iff.mp hC'
  have h1 : b * f * b⁻¹ ∈ Bt T0 B0 :=
    (Bt T0 B0).mul_mem ((Bt T0 B0).mul_mem hb hf) ((Bt T0 B0).inv_mem hb)
  have h2 : b * f * b⁻¹ * f⁻¹ ∈ Bt T0 B0 := (Bt T0 B0).mul_mem h1 ((Bt T0 B0).inv_mem hf)
  have h3 : b * f * b⁻¹ * f⁻¹ = t⁻¹ * (f * t * f⁻¹) := by
    calc b * f * b⁻¹ * f⁻¹ = t⁻¹ * ((t * b) * f) * b⁻¹ * f⁻¹ := by group
      _ = t⁻¹ * (f * (t * b)) * b⁻¹ * f⁻¹ := by rw [hfC]
      _ = t⁻¹ * (f * t * f⁻¹) := by group
  have h4 : t⁻¹ * (f * t * f⁻¹) ∈ T0 := by
    have : f * t * f⁻¹ ∈ T0 := (Subgroup.mem_normalizer_iff.mp hf.1 t).mp ht
    exact T0.mul_mem (T0.inv_mem ht) this
  have h5 : b * f * b⁻¹ * f⁻¹ = 1 := S.disj _ (h3 ▸ h4) h2
  have hbf : b * f = f * b := by
    calc b * f = (b * f * b⁻¹ * f⁻¹) * (f * b) := by group
      _ = f * b := by rw [h5, one_mul]
  have htf : t * f = f * t := by
    have : (t * f) * b = (f * t) * b := by
      calc (t * f) * b = t * (f * b) := by group
        _ = t * (b * f) := by rw [hbf]
        _ = (t * b) * f := by group
        _ = f * (t * b) := hfC
        _ = (f * t) * b := by group
    exact mul_right_cancel this
  refine ⟨t, ⟨ht, Subgroup.mem_centralizer_singleton_iff.mpr htf⟩, b,
    ⟨hb, Subgroup.mem_centralizer_singleton_iff.mpr hbf⟩, rfl⟩

theorem OutSkel.sylow_cent [I.Normal] {Tt : Subgroup H} (hTt : IsSylowTwoOf Tt (Bt T0 B0))
    {f : H} (hf : f ∈ Tt) (hTc : ∀ x ∈ Tt, x * f = f * x) :
    IsSylowTwoOf (prodSub T0 Tt (le_normalizer_of_le_Bt hTt.1) ⊓ Subgroup.centralizer ({f} : Set H))
      (Subgroup.normalizer (T0 : Set H) ⊓ Subgroup.centralizer ({f} : Set H)) ∧
    Nat.card ↥(prodSub T0 Tt (le_normalizer_of_le_Bt hTt.1) ⊓ Subgroup.centralizer ({f} : Set H)) =
      Nat.card ↥(T0 ⊓ Subgroup.centralizer ({f} : Set H)) * Nat.card Tt := by
  have hN := le_normalizer_of_le_Bt hTt.1
  have hTS := S.sylow_prod hTt
  set C : Subgroup H := Subgroup.centralizer ({f} : Set H) with hC
  set T : Subgroup H := prodSub T0 Tt hN with hT
  have hfBt : f ∈ Bt T0 B0 := hTt.1 hf
  have hTtC : Tt ≤ C := fun x hx => Subgroup.mem_centralizer_singleton_iff.mpr (hTc x hx)
  have hTle : T ≤ Subgroup.normalizer (T0 : Set H) := hTS.1
  have hcard1 : Nat.card ↥(T ⊓ C) = Nat.card ↥(T0 ⊓ C) * Nat.card Tt := by
    refine card_eq_mul_of_split (N := T ⊓ C) (U := T0 ⊓ C) (B₀ := Tt) ?_ ?_ ?_ ?_
    · exact inf_le_inf_right C (left_le_prodSub hN)
    · exact le_inf (right_le_prodSub hN) hTtC
    · exact fun x hx hxT => S.disj x hx.1 (hTt.1 hxT)
    · intro h hh
      obtain ⟨u, hu, t, ht, rfl⟩ := hh.1
      have htf : t * f = f * t := hTc t ht
      have hh' : u * t ∈ C := hh.2
      have h1 : (u * t) * f = f * (u * t) := Subgroup.mem_centralizer_singleton_iff.mp hh'
      have huf : u * f = f * u := by
        have : (u * f) * t = (f * u) * t := by
          calc (u * f) * t = u * (f * t) := by group
            _ = u * (t * f) := by rw [htf]
            _ = (u * t) * f := by group
            _ = f * (u * t) := h1
            _ = (f * u) * t := by group
        exact mul_right_cancel this
      exact ⟨u, ⟨hu, Subgroup.mem_centralizer_singleton_iff.mpr huf⟩, t, ht, rfl⟩
  have hcard2 : Nat.card ↥(Subgroup.normalizer (T0 : Set H) ⊓ C) =
      Nat.card ↥(T0 ⊓ C) * Nat.card ↥(Bt T0 B0 ⊓ C) := by
    refine card_eq_mul_of_split (N := Subgroup.normalizer (T0 : Set H) ⊓ C) (U := T0 ⊓ C)
      (B₀ := Bt T0 B0 ⊓ C) ?_ ?_ ?_ ?_
    · exact inf_le_inf_right C Subgroup.le_normalizer
    · exact inf_le_inf_right C inf_le_left
    · exact fun x hx hxB => S.disj x hx.1 hxB.1
    · exact fun h hh => S.cent_mul hfBt hh
  have hSylBtC : IsSylowTwoOf Tt (Bt T0 B0 ⊓ C) :=
    F7.isSylowTwoOf_mono_right hTt (le_inf hTt.1 hTtC) inf_le_left
  refine ⟨?_, hcard1⟩
  refine F7.isSylowTwoOf_of_relIndex (inf_le_inf_right C hTle) (hTS.2.1.to_inf_left) ?_
  have h1 := Subgroup.relIndex_mul_card (T ⊓ C) (Subgroup.normalizer (T0 : Set H) ⊓ C)
  have h2 := Subgroup.relIndex_mul_card Tt (Bt T0 B0 ⊓ C)
  rw [inf_of_le_left (inf_le_inf_right C hTle), hcard2, hcard1] at h1
  rw [inf_of_le_left (le_inf hTt.1 hTtC)] at h2
  have hpos : 0 < Nat.card ↥(T0 ⊓ C) := Nat.card_pos
  have hpos' : 0 < Nat.card Tt := Nat.card_pos
  have h3 : (T ⊓ C).relIndex (Subgroup.normalizer (T0 : Set H) ⊓ C) =
      Tt.relIndex (Bt T0 B0 ⊓ C) := by
    have h4 : (T ⊓ C).relIndex (Subgroup.normalizer (T0 : Set H) ⊓ C) *
        (Nat.card ↥(T0 ⊓ C) * Nat.card Tt) =
        Tt.relIndex (Bt T0 B0 ⊓ C) * (Nat.card ↥(T0 ⊓ C) * Nat.card Tt) := by
      calc _ = Nat.card ↥(T0 ⊓ C) * Nat.card ↥(Bt T0 B0 ⊓ C) := h1
        _ = Nat.card ↥(T0 ⊓ C) * (Tt.relIndex (Bt T0 B0 ⊓ C) * Nat.card Tt) := by rw [h2]
        _ = _ := by ring
    exact Nat.eq_of_mul_eq_mul_right (Nat.mul_pos hpos hpos') h4
  rw [h3]
  exact hSylBtC.2.2

end Skeleton

end CFSG.Quasithin.H13.F431.L3
