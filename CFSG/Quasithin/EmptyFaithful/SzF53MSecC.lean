module

public import CFSG.Quasithin.EmptyFaithful.SzF53MSecA

public section

namespace CFSG.Quasithin.F53Mod

variable {G : Type} [Group G]

theorem relIndex_fixSecIn_zpowers_conj {A B : Subgroup G}
    (hBA : B ≤ Subgroup.normalizer (A : Set G)) {a h : G}
    (ha : a ∈ Subgroup.normalizer (A : Set G)) (hhA : h ∈ Subgroup.normalizer (A : Set G))
    (hhB : h ∈ Subgroup.normalizer (B : Set G)) :
    (fixSecIn (Subgroup.zpowers (h * a * h⁻¹)) A B).relIndex B =
      (fixSecIn (Subgroup.zpowers a) A B).relIndex B := by
  have ha' : h * a * h⁻¹ ∈ Subgroup.normalizer (A : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hhA ha) (Subgroup.inv_mem _ hhA)
  let f : G →* G := (MulAut.conj h).toMonoidHom
  have hf : ∀ x, f x = h * x * h⁻¹ := fun x => rfl
  have hinj : Function.Injective f := (MulAut.conj h).injective
  have hBf : B.map f = B := by
    ext z
    rw [Subgroup.mem_map]
    refine ⟨fun ⟨x, hx, hxz⟩ => ?_, fun hz => ⟨h⁻¹ * z * h, ?_, ?_⟩⟩
    · rw [← hxz, hf]
      exact (Subgroup.mem_normalizer_iff.mp hhB x).mp hx
    · simpa using (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hhB) z).mp hz
    · rw [hf]; group
  have hFf : (fixSecIn (Subgroup.zpowers a) A B).map f =
      fixSecIn (Subgroup.zpowers (h * a * h⁻¹)) A B := by
    ext z
    rw [Subgroup.mem_map, mem_fixSecIn_zpowers_iff hBA ha']
    refine ⟨fun ⟨x, hx, hxz⟩ => ?_, fun hz => ⟨h⁻¹ * z * h, ?_, ?_⟩⟩
    · rw [mem_fixSecIn_zpowers_iff hBA ha] at hx
      rw [← hxz, hf]
      refine ⟨(Subgroup.mem_normalizer_iff.mp hhB x).mp hx.1, ?_⟩
      have e : h * a * h⁻¹ * (h * x * h⁻¹) * (h * a * h⁻¹)⁻¹ * (h * x * h⁻¹)⁻¹ =
          h * (a * x * a⁻¹ * x⁻¹) * h⁻¹ := by group
      rw [e]
      exact (Subgroup.mem_normalizer_iff.mp hhA _).mp hx.2
    · rw [mem_fixSecIn_zpowers_iff hBA ha]
      refine ⟨by simpa using
        (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hhB) z).mp hz.1, ?_⟩
      have e : a * (h⁻¹ * z * h) * a⁻¹ * (h⁻¹ * z * h)⁻¹ =
          h⁻¹ * (h * a * h⁻¹ * z * (h * a * h⁻¹)⁻¹ * z⁻¹) * h := by group
      rw [e]
      simpa using (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hhA) _).mp hz.2
    · rw [hf]; group
  calc (fixSecIn (Subgroup.zpowers (h * a * h⁻¹)) A B).relIndex B
      = ((fixSecIn (Subgroup.zpowers a) A B).map f).relIndex (B.map f) := by rw [hFf, hBf]
    _ = (fixSecIn (Subgroup.zpowers a) A B).relIndex B :=
      Subgroup.relIndex_map_map_of_injective _ _ hinj

theorem relIndex_fixSecIn_zpowers_mul_le [Finite G] {A B : Subgroup G}
    (hBA : B ≤ Subgroup.normalizer (A : Set G)) {a a' : G}
    (ha : a ∈ Subgroup.normalizer (A : Set G)) (ha' : a' ∈ Subgroup.normalizer (A : Set G)) :
    (fixSecIn (Subgroup.zpowers (a * a')) A B).relIndex B ≤
      (fixSecIn (Subgroup.zpowers a) A B).relIndex B *
        (fixSecIn (Subgroup.zpowers a') A B).relIndex B := by
  have hle : fixSecIn (Subgroup.zpowers a) A B ⊓ fixSecIn (Subgroup.zpowers a') A B ≤
      fixSecIn (Subgroup.zpowers (a * a')) A B := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.mp hx
    rw [mem_fixSecIn_zpowers_iff hBA ha] at hx1
    rw [mem_fixSecIn_zpowers_iff hBA ha'] at hx2
    rw [mem_fixSecIn_zpowers_iff hBA (Subgroup.mul_mem _ ha ha')]
    refine ⟨hx1.1, ?_⟩
    have h1 : a ∈ fixer A x := mem_fixer_iff.mpr ⟨ha, hx1.2⟩
    have h2 : a' ∈ fixer A x := mem_fixer_iff.mpr ⟨ha', hx2.2⟩
    exact (mem_fixer_iff.mp (Subgroup.mul_mem _ h1 h2)).2
  have hdvd := Subgroup.relIndex_dvd_of_le_left B hle
  have hne : (fixSecIn (Subgroup.zpowers a) A B ⊓ fixSecIn (Subgroup.zpowers a') A B).relIndex B
      ≠ 0 := D15Proof.relIndex_ne_zero _ _
  exact (Nat.le_of_dvd (Nat.pos_of_ne_zero hne) hdvd).trans Subgroup.relIndex_inf_le

theorem mk_eq_mk_iff {A B : Subgroup G} (hBA : B ≤ Subgroup.normalizer (A : Set G))
    [(A.subgroupOf B).Normal] (y z : ↥B) :
    (QuotientGroup.mk y : ↥B ⧸ A.subgroupOf B) = QuotientGroup.mk z ↔ (z : G) * (y : G)⁻¹ ∈ A := by
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
  constructor
  · intro h
    have := (Subgroup.mem_normalizer_iff.mp (hBA y.2) _).mp h
    simpa [mul_assoc] using this
  · intro h
    have := (Subgroup.mem_normalizer_iff.mp (hBA (Subgroup.inv_mem _ y.2)) _).mp h
    simpa [mul_assoc] using this

variable [Finite G]

theorem commutator_mem_of_relIndex_le_four {A B : Subgroup G} (hAB : A ≤ B)
    (hBA : B ≤ Subgroup.normalizer (A : Set G)) (hB2 : IsPGroup 2 B) {c : G}
    (hcA : c ∈ Subgroup.normalizer (A : Set G)) (hcB : c ∈ Subgroup.normalizer (B : Set G))
    (hc5 : ∀ x ∈ B, c ^ 5 * x * (c ^ 5)⁻¹ * x⁻¹ ∈ A)
    (hidx : (fixSecIn (Subgroup.zpowers c) A B).relIndex B ≤ 4) :
    ∀ x ∈ B, c * x * c⁻¹ * x⁻¹ ∈ A := by
  classical
  have : Fintype (↥B ⧸ A.subgroupOf B) := Fintype.ofFinite _
  have hnorm : (A.subgroupOf B).Normal :=
    (Subgroup.normal_subgroupOf_iff hAB).mpr fun h k hh hk =>
      (Subgroup.mem_normalizer_iff.mp (hBA hk) h).mp hh
  let φc : ↥B →* ↥B :=
    { toFun := fun x => ⟨c * x * c⁻¹, (Subgroup.mem_normalizer_iff.mp hcB x).mp x.2⟩
      map_one' := by ext; simp
      map_mul' := fun x y => by ext; simp [mul_assoc] }
  have hφc : ∀ x : ↥B, (φc x : G) = c * x * c⁻¹ := fun x => rfl
  have hle : A.subgroupOf B ≤ (A.subgroupOf B).comap φc := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp hcA x).mp hx
  let f : (↥B ⧸ A.subgroupOf B) →* (↥B ⧸ A.subgroupOf B) := QuotientGroup.map _ _ φc hle
  have hfmk : ∀ x : ↥B, f (QuotientGroup.mk x) = QuotientGroup.mk (φc x) := fun x => rfl
  have hiter : ∀ (n : ℕ) (x y : ↥B), (y : G) = c ^ n * x * (c ^ n)⁻¹ →
      f^[n] (QuotientGroup.mk x) = QuotientGroup.mk y := by
    intro n
    induction n with
    | zero =>
      intro x y h
      have : y = x := Subtype.ext (by simpa using h)
      simp [this]
    | succ n ih =>
      intro x y h
      rw [Function.iterate_succ_apply, hfmk]
      refine ih (φc x) y ?_
      rw [h, hφc, pow_succ]
      group
  have hf5 : ∀ v : ↥B ⧸ A.subgroupOf B, f^[5] v = v := by
    intro v
    induction v using QuotientGroup.induction_on with
    | H x =>
      have hy : c ^ 5 * x * (c ^ 5)⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.mp
        (Subgroup.pow_mem _ hcB 5) x).mp x.2
      rw [hiter 5 x ⟨c ^ 5 * x * (c ^ 5)⁻¹, hy⟩ rfl]
      symm
      rw [mk_eq_mk_iff hBA]
      exact hc5 x x.2
  have hfix : ∀ x : ↥B, f (QuotientGroup.mk x) = QuotientGroup.mk x ↔
      c * x * c⁻¹ * x⁻¹ ∈ A := by
    intro x
    rw [hfmk, mk_eq_mk_iff hBA, hφc, ← inv_mem_iff (x := c * x * c⁻¹ * x⁻¹)]
    simp [mul_assoc]
  let Fix : Subgroup (↥B ⧸ A.subgroupOf B) := MonoidHom.eqLocus f (MonoidHom.id _)
  have hmemFix : ∀ v, v ∈ Fix ↔ f v = v := fun v => Iff.rfl
  have hFix : Fix.comap (QuotientGroup.mk' (A.subgroupOf B)) =
      (fixSecIn (Subgroup.zpowers c) A B).subgroupOf B := by
    ext x
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf, mem_fixSecIn_zpowers_iff hBA hcA, hmemFix]
    exact ⟨fun h => ⟨x.2, (hfix x).mp h⟩, fun h => (hfix x).mpr h.2⟩
  have hindex : Fix.index = (fixSecIn (Subgroup.zpowers c) A B).relIndex B := by
    rw [← Subgroup.index_comap_of_surjective Fix (QuotientGroup.mk'_surjective _), hFix]
    rfl
  have hp5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  let g : Function.End (↥B ⧸ A.subgroupOf B) := ⇑f
  have hfn : g ^ 5 ^ 1 = 1 := by
    show (⇑f)^[5 ^ 1] = id
    rw [pow_one]
    exact funext hf5
  have hmod := Equiv.Perm.card_fixedPoints_modEq hfn
  have hcardfix : Fintype.card (Function.fixedPoints g) = Nat.card Fix := by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun v => (hmemFix v).symm)
  rw [← Nat.card_eq_fintype_card, hcardfix] at hmod
  have hcard : Nat.card Fix * Fix.index = Nat.card (↥B ⧸ A.subgroupOf B) :=
    Subgroup.card_mul_index Fix
  obtain ⟨n, hn⟩ := ((hB2.to_quotient (A.subgroupOf B)).to_subgroup Fix).exists_card_eq
  have hcop : Nat.gcd 5 (Nat.card Fix) = 1 := by
    rw [hn]
    exact Nat.Coprime.pow_right n (by norm_num)
  have h1 : Fix.index ≡ 1 [MOD 5] := by
    refine Nat.ModEq.cancel_left_of_coprime hcop ?_
    rw [mul_one, hcard]
    exact hmod
  have hpos : 0 < Fix.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have h5 : Fix.index = 1 := by
    have h4 : Fix.index ≤ 4 := hindex ▸ hidx
    unfold Nat.ModEq at h1
    omega
  have htop : Fix = ⊤ := Subgroup.index_eq_one.mp h5
  intro x hx
  have hmem : QuotientGroup.mk' (A.subgroupOf B) ⟨x, hx⟩ ∈ Fix := by rw [htop]; trivial
  exact (hfix ⟨x, hx⟩).mp hmem

end CFSG.Quasithin.F53Mod
