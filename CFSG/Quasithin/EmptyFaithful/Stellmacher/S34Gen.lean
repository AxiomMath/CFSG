module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S34Base
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.Step3Chain
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.StepF2
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.ModS5Irr
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S41Module

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod

namespace F53.Stellmacher

open CosetGeom F53 Equiv S42B1

namespace S34

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

omit [Finite G] in
theorem map_sq_eq_one {X K : Subgroup G} (hK : IsElemAbelian 2 K) (ψ : ↥X →* Perm (Fin 5))
    (x : Perm (Fin 5)) (hx : x ∈ (K.subgroupOf X).map ψ) : x ^ 2 = 1 := by
  obtain ⟨a, ha, rfl⟩ := hx
  have ha2 : a ^ 2 = 1 := Subtype.ext (hK.2 _ (Subgroup.mem_subgroupOf.mp ha))
  rw [← map_pow, ha2, map_one]

omit [Finite G] in
theorem card_map_eq_two_pow {X K : Subgroup G} (hK : IsElemAbelian 2 K)
    (ψ : ↥X →* Perm (Fin 5)) : ∃ n : ℕ, Nat.card ((K.subgroupOf X).map ψ) = 2 ^ n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hB2 : IsPGroup 2 ((K.subgroupOf X).map ψ) := fun x =>
    ⟨1, Subtype.ext (by simpa using map_sq_eq_one hK ψ x.1 x.2)⟩
  obtain ⟨n, hn⟩ := hB2.exists_card_eq
  exact ⟨n, hn⟩

omit [Finite G] in
theorem ker_iff {X : Subgroup G} {ψ : ↥X →* Perm (Fin 5)}
    (hψ : ψ.ker = (pCoreOf 2 X).subgroupOf X) (x : ↥X) : ψ x = 1 ↔ (x : G) ∈ pCoreOf 2 X := by
  rw [← MonoidHom.mem_ker, hψ, Subgroup.mem_subgroupOf]

theorem mem_sup_iff_alt {X : Subgroup G} {ψ : ↥X →* Perm (Fin 5)} (hs : Function.Surjective ψ)
    (hψ : ψ.ker = (pCoreOf 2 X).subgroupOf X) {f : G} (hf : f ∈ X) :
    f ∈ oTwoRes X ⊔ pCoreOf 2 X ↔ ψ ⟨f, hf⟩ ∈ alternatingGroup (Fin 5) := by
  refine ⟨fun h => ?_, fun h => mem_oTwoRes_sup_of_alt hs (ker_iff hψ) hf h⟩
  have hle : oTwoRes X ⊔ pCoreOf 2 X ≤ ((alternatingGroup (Fin 5)).comap ψ).map X.subtype := by
    refine sup_le (fun x hx => ?_) (fun x hx => ?_)
    · obtain ⟨hxX, hxA⟩ := psi_mem_alt_of_mem_oTwoRes ψ hx
      exact ⟨⟨x, hxX⟩, hxA, rfl⟩
    · refine ⟨⟨x, pCoreOf_le 2 X hx⟩, ?_, rfl⟩
      show ψ _ ∈ alternatingGroup (Fin 5)
      rw [(ker_iff hψ _).mpr hx]
      exact one_mem _
  obtain ⟨y, hy, hyf⟩ := hle h
  have : y = ⟨f, hf⟩ := Subtype.ext hyf
  rw [← this]
  exact hy

omit [Finite G] in
theorem klein_le_four {X K : Subgroup G} (hX : Nonempty (OTwoQuot X ≃* Perm (Fin 5)))
    (hKX : K ≤ X) (hK : IsElemAbelian 2 K) : (K ⊓ pCoreOf 2 X).relIndex K ≤ 4 :=
  relIndex_le_four_of_elemAbelian hX hKX hK

theorem klein_le_two {X K : Subgroup G} (hX : Nonempty (OTwoQuot X ≃* Perm (Fin 5)))
    (hKX : K ≤ X) (hK : IsElemAbelian 2 K)
    (hno : ∀ g ∈ K, g ∈ oTwoRes X ⊔ pCoreOf 2 X → g ∈ pCoreOf 2 X) :
    (K ⊓ pCoreOf 2 X).relIndex K ≤ 2 := by
  obtain ⟨ψ, hs, hψ⟩ := exists_quotHom_five hX
  rw [relIndex_inf_eq_card_map hψ hKX]
  have h4 := klein_le_four hX hKX hK
  rw [relIndex_inf_eq_card_map hψ hKX] at h4
  obtain ⟨n, hn⟩ := card_map_eq_two_pow hK ψ
  have hne : Nat.card ((K.subgroupOf X).map ψ) ≠ 4 := by
    intro h4'
    obtain ⟨a, ha, ha1, hsg⟩ := exists_even_of_klein h4' (fun x hx => by
      rw [← pow_two]; exact map_sq_eq_one hK ψ x hx)
    obtain ⟨⟨g, hgX⟩, hgK, rfl⟩ := ha
    have hg : g ∈ K := Subgroup.mem_subgroupOf.mp hgK
    have hgs : g ∈ oTwoRes X ⊔ pCoreOf 2 X := (mem_sup_iff_alt hs hψ hgX).mpr
      (Equiv.Perm.mem_alternatingGroup.mpr hsg)
    exact ha1 ((ker_iff hψ ⟨g, hgX⟩).mpr (hno g hg hgs))
  rw [hn] at h4 hne ⊢
  have hn2 : n ≤ 2 := by
    by_contra hc
    have : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  interval_cases n <;> simp_all

theorem klein_exists_over {X K : Subgroup G} (hX : Nonempty (OTwoQuot X ≃* Perm (Fin 5)))
    (hKX : K ≤ X) (hK : IsElemAbelian 2 K) (h4 : (K ⊓ pCoreOf 2 X).relIndex K = 4) :
    ∃ g ∈ K, OverIn X g := by
  obtain ⟨ψ, hs, hψ⟩ := exists_quotHom_five hX
  rw [relIndex_inf_eq_card_map hψ hKX] at h4
  obtain ⟨a, ha, ha1, hsg⟩ := exists_even_of_klein h4 (fun x hx => by
    rw [← pow_two]; exact map_sq_eq_one hK ψ x hx)
  obtain ⟨⟨g, hgX⟩, hgK, rfl⟩ := ha
  have hg : g ∈ K := Subgroup.mem_subgroupOf.mp hgK
  refine ⟨g, hg, ?_⟩
  show _ ∧ _ ∧ _
  refine ⟨(mem_sup_iff_alt hs hψ hgX).mpr (Equiv.Perm.mem_alternatingGroup.mpr hsg),
    fun h => ha1 ((ker_iff hψ ⟨g, hgX⟩).mpr h), Or.inl ?_⟩
  rw [hK.2 g hg]
  exact (pCoreOf 2 X).one_mem

theorem card_range_le_index_mul {K V : Type*} [Group K] [Group V] [Finite V] (f : V →* K)
    (A : Subgroup V) : Nat.card f.range ≤ A.index * Nat.card (A.map f) := by
  have hQ : A.map f ≤ f.range := A.map_le_range f
  have h1 := Subgroup.relIndex_mul_card (H := A.map f) (K := f.range)
  rw [inf_eq_left.mpr hQ] at h1
  have h2 : (A.map f).relIndex f.range = (A ⊔ f.ker).index := by
    rw [MonoidHom.range_eq_map, Subgroup.relIndex_map_map, top_sup_eq, Subgroup.relIndex_top_right]
  have h3 : (A ⊔ f.ker).index ≤ A.index :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero A.index_ne_zero_of_finite)
      (Subgroup.index_dvd_of_le le_sup_left)
  rw [← h1, h2]
  exact Nat.mul_le_mul_right _ h3

section CommHom

variable {V : Subgroup G} {y : G}

omit [Finite G] in
theorem comm_mem_of_normalizer (hy : y ∈ Subgroup.normalizer (V : Set G)) {a : G} (ha : a ∈ V) :
    y * a * y⁻¹ * a⁻¹ ∈ V :=
  V.mul_mem ((Subgroup.mem_normalizer_iff.mp hy a).mp ha) (V.inv_mem ha)

@[expose] def yCommHom (hV : IsMulCommutative V) (hy : y ∈ Subgroup.normalizer (V : Set G)) :
    ↥V →* ↥V :=
  MonoidHom.mk' (fun a => ⟨y * a * y⁻¹ * (a : G)⁻¹, comm_mem_of_normalizer hy a.2⟩)
    (fun a b => by
      apply Subtype.ext
      have hc : (a : G)⁻¹ * (y * b * y⁻¹ * (b : G)⁻¹) = (y * b * y⁻¹ * (b : G)⁻¹) * (a : G)⁻¹ :=
        congrArg Subtype.val
          (isMulCommutative_iff.mp hV ⟨_, V.inv_mem a.2⟩ ⟨_, comm_mem_of_normalizer hy b.2⟩)
      show y * (a * b) * y⁻¹ * ((a : G) * b)⁻¹ =
        (y * a * y⁻¹ * (a : G)⁻¹) * (y * b * y⁻¹ * (b : G)⁻¹)
      calc y * (a * b) * y⁻¹ * ((a : G) * b)⁻¹
          = (y * a * y⁻¹) * ((y * b * y⁻¹ * (b : G)⁻¹) * (a : G)⁻¹) := by group
        _ = (y * a * y⁻¹) * ((a : G)⁻¹ * (y * b * y⁻¹ * (b : G)⁻¹)) := by rw [hc]
        _ = _ := by group)

omit [Finite G] in
theorem coe_yCommHom (hV : IsMulCommutative V) (hy : y ∈ Subgroup.normalizer (V : Set G))
    (a : ↥V) : (yCommHom hV hy a : G) = y * a * y⁻¹ * (a : G)⁻¹ := rfl

end CommHom

section Count

variable {V C A₀ Z : Subgroup G} {y : G}

omit [Finite G] in
theorem normal_subgroupOf_of_comm (hV : IsMulCommutative V) (C : Subgroup G) :
    (C.subgroupOf V).Normal :=
  ⟨fun n hn g => by
    have h : g * n = n * g := IsMulCommutative.is_comm.comm g n
    rwa [h, mul_inv_cancel_right]⟩

omit [Finite G] in
theorem ker_comm_eq (hV : IsMulCommutative V) (hy : y ∈ Subgroup.normalizer (V : Set G))
    (hyC : y ∈ Subgroup.normalizer (C : Set G)) (hCV : C ≤ V) :
    letI := normal_subgroupOf_of_comm hV C
    ((QuotientGroup.mk' (C.subgroupOf V)).comp (yCommHom hV hy)).ker =
      (fixSecIn (Subgroup.zpowers y) C V).subgroupOf V := by
  have hcomm : ∀ x ∈ V, ∀ d ∈ C, x * d * x⁻¹ = d := fun x hx d hd => by
    have : x * d = d * x :=
      congrArg Subtype.val (isMulCommutative_iff.mp hV ⟨x, hx⟩ ⟨d, hCV hd⟩)
    rw [this, mul_inv_cancel_right]
  have hVC : V ≤ Subgroup.normalizer (C : Set G) := fun x hx =>
    Subgroup.mem_normalizer_iff.mpr fun c => ⟨fun hc => by rwa [hcomm x hx c hc], fun hc => by
      have := hcomm x⁻¹ (V.inv_mem hx) _ hc
      have e : c = x⁻¹ * (x * c * x⁻¹) * x⁻¹⁻¹ := by group
      rw [e, this]
      exact hc⟩
  ext a
  simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, mem_fixSecIn_zpowers_iff hVC hyC]
  exact ⟨fun h => ⟨a.2, h⟩, fun h => h.2⟩

end Count

theorem secIdx_le_of_comm {V C A₀ Z : Subgroup G} {y : G} (hV : IsElemAbelian 2 V)
    (hy : y ∈ Subgroup.normalizer (V : Set G)) (hyC : y ∈ Subgroup.normalizer (C : Set G))
    (hCV : C ≤ V) (_hA₀ : A₀ ≤ V) (hZ : Z ≤ V)
    (h : ∀ a ∈ A₀, y * a * y⁻¹ * a⁻¹ ∈ Z) :
    secIdx (Subgroup.zpowers y) C V ≤ A₀.relIndex V * (Z ⊓ C).relIndex Z := by
  have := normal_subgroupOf_of_comm hV.1 C
  have hker := ker_comm_eq hV.1 hy hyC hCV
  set ψ := (QuotientGroup.mk' (C.subgroupOf V)).comp (yCommHom hV.1 hy) with hψ
  have h1 : secIdx (Subgroup.zpowers y) C V = Nat.card ψ.range := by
    unfold secIdx Subgroup.relIndex
    rw [← hker, Subgroup.index_ker]
  have h2 := card_range_le_index_mul ψ (A₀.subgroupOf V)
  have h3 : Nat.card ((A₀.subgroupOf V).map ψ) ≤ (Z ⊓ C).relIndex Z := by
    rw [relIndex_inf_eq_card_map (ψ := QuotientGroup.mk' (C.subgroupOf V))
      (QuotientGroup.ker_mk' _) hZ]
    apply Subgroup.card_le_of_le
    rintro _ ⟨a, ha, rfl⟩
    refine ⟨yCommHom hV.1 hy a, ?_, rfl⟩
    exact Subgroup.mem_subgroupOf.mpr (h a (Subgroup.mem_subgroupOf.mp ha))
  rw [h1]
  exact h2.trans (Nat.mul_le_mul le_rfl h3)

omit [Finite G] in
theorem comm_zpow_mem_range {V : Subgroup G} {y : G} (hV : IsMulCommutative V)
    (hy : y ∈ Subgroup.normalizer (V : Set G)) :
    ⁅V, Subgroup.zpowers y⁆ ≤ (yCommHom hV hy).range.map V.subtype := by
  set R := (yCommHom hV hy).range.map V.subtype with hR
  have hφ : ∀ a ∈ V, y * a * y⁻¹ * a⁻¹ ∈ R := fun a ha =>
    ⟨yCommHom hV hy ⟨a, ha⟩, ⟨⟨a, ha⟩, rfl⟩, rfl⟩
  have hconj : ∀ r ∈ R, y * r * y⁻¹ ∈ R := by
    rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
    have ha' : y * (a : G) * y⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hy a).mp a.2
    have := hφ _ ha'
    convert this using 1
    simp only [Subgroup.coe_subtype, coe_yCommHom]
    group
  have hy' : y⁻¹ ∈ Subgroup.normalizer (V : Set G) := Subgroup.inv_mem _ hy
  have hφ' : ∀ v ∈ V, y⁻¹ * v * y * v⁻¹ ∈ R := by
    intro v hv
    have hv' : y⁻¹ * v * y ∈ V := by
      simpa using (Subgroup.mem_normalizer_iff.mp hy' v).mp hv
    have := R.inv_mem (hφ _ hv')
    convert this using 1
    group
  have up : ∀ k : ℤ, (∀ v ∈ V, y ^ k * v * (y ^ k)⁻¹ * v⁻¹ ∈ R) →
      ∀ v ∈ V, y ^ (k + 1) * v * (y ^ (k + 1))⁻¹ * v⁻¹ ∈ R := by
    intro k ih v hv
    have := R.mul_mem (hconj _ (ih v hv)) (hφ v hv)
    convert this using 1
    group
  have down : ∀ k : ℤ, (∀ v ∈ V, y ^ k * v * (y ^ k)⁻¹ * v⁻¹ ∈ R) →
      ∀ v ∈ V, y ^ (k - 1) * v * (y ^ (k - 1))⁻¹ * v⁻¹ ∈ R := by
    intro k ih v hv
    have hv' : y⁻¹ * v * y ∈ V := by
      simpa using (Subgroup.mem_normalizer_iff.mp hy' v).mp hv
    have := R.mul_mem (ih _ hv') (hφ' v hv)
    convert this using 1
    group
  have key : ∀ k : ℤ, ∀ v ∈ V, y ^ k * v * (y ^ k)⁻¹ * v⁻¹ ∈ R := by
    intro k
    induction k using Int.induction_on with
    | zero => intro v _; simp
    | succ i ih => exact up _ ih
    | pred i ih => exact down _ ih
  rw [Subgroup.commutator_le]
  intro v hv z hz
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  have := R.inv_mem (key k v hv)
  convert this using 1
  simp only [commutatorElement_def]
  group

theorem card_comm_le {V A₀ Z : Subgroup G} {y : G} (hV : IsElemAbelian 2 V)
    (hy : y ∈ Subgroup.normalizer (V : Set G)) (_hA₀ : A₀ ≤ V) (hZ : Z ≤ V)
    (h : ∀ a ∈ A₀, y * a * y⁻¹ * a⁻¹ ∈ Z) :
    Nat.card ↥⁅V, Subgroup.zpowers y⁆ ≤ A₀.relIndex V * Nat.card Z := by
  have h1 := Subgroup.card_le_of_le (comm_zpow_mem_range hV.1 hy)
  have h2 := card_range_le_index_mul (yCommHom hV.1 hy) (A₀.subgroupOf V)
  have h3 : Nat.card ((A₀.subgroupOf V).map (yCommHom hV.1 hy)) ≤ Nat.card Z := by
    have : Nat.card ((A₀.subgroupOf V).map (yCommHom hV.1 hy)) ≤
        Nat.card (Z.subgroupOf V) := by
      apply Subgroup.card_le_of_le
      rintro _ ⟨a, ha, rfl⟩
      exact Subgroup.mem_subgroupOf.mpr (h a (Subgroup.mem_subgroupOf.mp ha))
    exact this.trans (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZ).toEquiv).le
  have h4 : Nat.card ((yCommHom hV.1 hy).range.map V.subtype) =
      Nat.card (yCommHom hV.1 hy).range :=
    Nat.card_congr (((yCommHom hV.1 hy).range.equivMapOfInjective V.subtype
      V.subtype_injective).toEquiv.symm)
  rw [h4] at h1
  exact h1.trans (h2.trans (Nat.mul_le_mul le_rfl h3))

end S34

end F53.Stellmacher

end CFSG.Quasithin
