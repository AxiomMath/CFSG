module

public import CFSG.Quasithin.EmptyFaithful.S146zYCfg
public import CFSG.Quasithin.H13.NQCoreP134Normal

public section

namespace CFSG.Quasithin.S146zY

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.NQCore

namespace E25Quot

theorem injOn_mk_of_disjoint {A : Type*} [Group A] {Z K : Subgroup A} [Z.Normal]
    (hd : Disjoint K Z) : Set.InjOn (QuotientGroup.mk' Z) (K : Set A) := by
  intro x hx y hy hxy
  have h1 : x⁻¹ * y ∈ Z := QuotientGroup.eq.mp hxy
  have h2 : x⁻¹ * y ∈ K := K.mul_mem (K.inv_mem hx) hy
  exact inv_mul_eq_one.mp (Subgroup.disjoint_def.mp hd h2 h1)

theorem card_map_mk_of_disjoint {A : Type*} [Group A] {Z K : Subgroup A} [Z.Normal]
    (hd : Disjoint K Z) : Nat.card (K.map (QuotientGroup.mk' Z)) = Nat.card K := by
  have h := Nat.card_image_of_injOn (injOn_mk_of_disjoint hd)
  rw [← Subgroup.coe_map] at h
  exact h

theorem map_mem_normalizer {A B : Type*} [Group A] [Group B] (f : A →* B) {P : Subgroup A}
    {t : A} (ht : t ∈ Subgroup.normalizer (P : Set A)) :
    f t ∈ Subgroup.normalizer ((P.map f : Subgroup B) : Set B) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    exact Subgroup.mem_map.mpr
      ⟨t * x * t⁻¹, (Subgroup.mem_normalizer_iff.mp ht x).mp hx, by simp⟩
  · intro hy
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp hy
    refine Subgroup.mem_map.mpr ⟨t⁻¹ * x * t, ?_, ?_⟩
    · simpa using (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ ht) x).mp hx
    · rw [map_mul, map_mul, map_inv, hxy]
      group

theorem mem_normalizer_comap {A B : Type*} [Group A] [Group B] (f : A →* B) {U : Subgroup B}
    {t : A} (ht : f t ∈ Subgroup.normalizer (U : Set B)) :
    t ∈ Subgroup.normalizer ((U.comap f : Subgroup A) : Set A) := by
  rw [Subgroup.mem_normalizer_iff]
  intro a
  rw [Subgroup.mem_comap, Subgroup.mem_comap, map_mul, map_mul, map_inv]
  exact Subgroup.mem_normalizer_iff.mp ht (f a)

theorem isSylowTwoOf_map_mk {A : Type*} [Group A] {T : Subgroup A} (Z : Subgroup A) [Z.Normal]
    (hT : IsSylowTwoOf T ⊤) : IsSylowTwoOf (T.map (QuotientGroup.mk' Z)) ⊤ := by
  refine ⟨le_top, hT.2.1.map _, ?_⟩
  have hidx : (T.map (QuotientGroup.mk' Z)).index = (T ⊔ Z).index := by
    rw [← Subgroup.index_comap_of_surjective (T.map (QuotientGroup.mk' Z))
      (QuotientGroup.mk'_surjective Z), Subgroup.comap_map_eq, QuotientGroup.ker_mk']
  have hrel : ∀ {G : Type _} [Group G] (S : Subgroup G), (S.subgroupOf ⊤).index = S.index :=
    fun S => Subgroup.relIndex_top_right S
  rw [hrel, hidx]
  intro h2
  exact hT.2.2 ((hrel T).symm ▸ h2.trans (Subgroup.index_dvd_of_le le_sup_left))

theorem pow_three_eq_one {A : Type*} [Group A] {Z : Subgroup A}
    (hZ : Nat.card Z = 1 ∨ Nat.card Z = 3) : ∀ z ∈ Z, z ^ 3 = 1 := by
  intro z hz
  have h : (⟨z, hz⟩ : Z) ^ Nat.card Z = 1 := pow_card_eq_one'
  rcases hZ with h1 | h3
  · rw [h1, pow_one] at h
    have hz1 : z = 1 := congrArg Subtype.val h
    rw [hz1, one_pow]
  · rw [h3] at h
    exact congrArg Subtype.val h

theorem conj_mem_of_mk_mem_normalizer {A : Type*} [Group A] {P Z : Subgroup A} [Z.Normal]
    (hcomm : ∀ x ∈ P, ∀ z ∈ Z, x * z = z * x) (hZ : ∀ z ∈ Z, z ^ 3 = 1)
    (hexp : ∀ x ∈ P, x ^ 5 = 1) {g : A}
    (hg : QuotientGroup.mk' Z g ∈
      Subgroup.normalizer ((P.map (QuotientGroup.mk' Z) : Subgroup (A ⧸ Z)) : Set (A ⧸ Z)))
    {x : A} (hx : x ∈ P) : g * x * g⁻¹ ∈ P := by
  have h1 : QuotientGroup.mk' Z (g * x * g⁻¹) ∈ P.map (QuotientGroup.mk' Z) := by
    have := (Subgroup.mem_normalizer_iff.mp hg (QuotientGroup.mk' Z x)).mp
      (Subgroup.mem_map_of_mem _ hx)
    simpa using this
  obtain ⟨p, hp, hpw⟩ := Subgroup.mem_map.mp h1
  have hz : p⁻¹ * (g * x * g⁻¹) ∈ Z := QuotientGroup.eq.mp hpw
  have hw : g * x * g⁻¹ = p * (p⁻¹ * (g * x * g⁻¹)) := by group
  have h5 : (g * x * g⁻¹) ^ 5 = 1 := by rw [conj_pow, hexp x hx]; simp
  have hz5 : (p⁻¹ * (g * x * g⁻¹)) ^ 5 = 1 := by
    have hc : Commute p (p⁻¹ * (g * x * g⁻¹)) := hcomm p hp _ hz
    rw [hw, hc.mul_pow, hexp p hp, one_mul] at h5
    exact h5
  have hz1 : p⁻¹ * (g * x * g⁻¹) = 1 := by
    have hd : orderOf (p⁻¹ * (g * x * g⁻¹)) ∣ Nat.gcd 5 3 :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hz5) (orderOf_dvd_of_pow_eq_one (hZ _ hz))
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp (by simpa using hd))
  rw [hw, hz1, mul_one]
  exact hp

theorem nonempty_mulEquiv_map_mk {A : Type*} [Group A] {L Z : Subgroup A} [Z.Normal]
    (hZ : Z = L ⊓ Subgroup.centralizer (L : Set A)) :
    Nonempty (↥(L.map (QuotientGroup.mk' Z)) ≃* ↥L ⧸ Subgroup.center ↥L) := by
  let φ : ↥L →* A ⧸ Z := (QuotientGroup.mk' Z).comp L.subtype
  have hker : φ.ker = Subgroup.center ↥L := by
    ext l
    simp only [MonoidHom.mem_ker, φ, MonoidHom.comp_apply, Subgroup.coe_subtype,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hZ, Subgroup.mem_inf,
      Subgroup.mem_center_iff]
    constructor
    · rintro ⟨-, hc⟩ g
      exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp hc) g g.2)
    · intro hc
      exact ⟨l.2, Subgroup.mem_centralizer_iff.mpr fun g hg => congrArg Subtype.val (hc ⟨g, hg⟩)⟩
  have hrange : φ.range = L.map (QuotientGroup.mk' Z) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    ((QuotientGroup.quotientKerEquivRange φ).trans (MulEquiv.subgroupCongr hrange))).symm⟩

end E25Quot

theorem E25Config.map_mk_of_disjoint {A : Type} [Group A] {L P T : Subgroup A}
    (h : E25Config L P T) (Z : Subgroup A) [Z.Normal] (hPZ : Disjoint P Z) :
    E25Config (L.map (QuotientGroup.mk' Z)) (P.map (QuotientGroup.mk' Z))
      (T.map (QuotientGroup.mk' Z)) where
  normal := h.normal.map _ (QuotientGroup.mk'_surjective Z)
  le := Subgroup.map_mono h.le
  card := by rw [E25Quot.card_map_mk_of_disjoint hPZ, h.card]
  exp := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    rw [← map_pow, h.exp x hx, map_one]
  sylow := E25Quot.isSylowTwoOf_map_mk Z h.sylow
  mul := by
    intro t' ht' x' hx'
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp ht'
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hx'
    obtain ⟨y, hy, s, hs, he⟩ := h.mul t ht x hx
    exact ⟨QuotientGroup.mk' Z y, Subgroup.mem_map_of_mem _ hy, QuotientGroup.mk' Z s,
      Subgroup.mem_map_of_mem _ hs, by rw [← map_mul, ← map_mul, he]⟩
  irred := by
    intro U hUP hN
    have hN₀ : T ⊓ Subgroup.normalizer (P : Set A) ≤
        Subgroup.normalizer ((P ⊓ U.comap (QuotientGroup.mk' Z) : Subgroup A) : Set A) := by
      intro t ht
      have hπt : QuotientGroup.mk' Z t ∈ T.map (QuotientGroup.mk' Z) ⊓
          Subgroup.normalizer ((P.map (QuotientGroup.mk' Z) : Subgroup (A ⧸ Z)) : Set (A ⧸ Z)) :=
        ⟨Subgroup.mem_map_of_mem _ ht.1, E25Quot.map_mem_normalizer _ ht.2⟩
      exact Subgroup.inf_normalizer_le_normalizer_inf
        ⟨ht.2, E25Quot.mem_normalizer_comap _ (hN hπt)⟩
    have hU : U = (P ⊓ U.comap (QuotientGroup.mk' Z)).map (QuotientGroup.mk' Z) := by
      apply le_antisymm
      · intro u hu
        obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp (hUP hu)
        exact Subgroup.mem_map.mpr ⟨x, ⟨hx, Subgroup.mem_comap.mpr hu⟩, rfl⟩
      · intro u hu
        obtain ⟨x, ⟨-, hx⟩, rfl⟩ := Subgroup.mem_map.mp hu
        exact Subgroup.mem_comap.mp hx
    rcases h.irred _ inf_le_left hN₀ with h0 | h0
    · left
      rw [hU, h0, Subgroup.map_bot]
    · right
      rw [hU, h0]

theorem E25Config.quotient_center {A : Type} [Group A] [Finite A] {L P T : Subgroup A}
    (h : E25Config L P T)
    (hZ : Nat.card (Subgroup.center ↥L) = 1 ∨ Nat.card (Subgroup.center ↥L) = 3) :
    ∃ (B : Type) (_ : Group B) (_ : Finite B) (L' P' T' : Subgroup B), E25Config L' P' T' ∧
      Nonempty (↥L' ≃* ↥L ⧸ Subgroup.center ↥L) ∧
      (EmptyFaithfulMultiple.AutCyclic T' P' → EmptyFaithfulMultiple.AutCyclic T P) := by
  have : L.Normal := h.normal
  obtain ⟨Z, hZdef⟩ : ∃ Z : Subgroup A, Z = L ⊓ Subgroup.centralizer (L : Set A) := ⟨_, rfl⟩
  have hZn : Z.Normal := by rw [hZdef]; infer_instance
  have hZcard : Nat.card Z = 1 ∨ Nat.card Z = 3 := by
    rw [hZdef, card_inf_centralizer]
    exact hZ
  have hZ3 : ∀ z ∈ Z, z ^ 3 = 1 := E25Quot.pow_three_eq_one hZcard
  have hPZ : Disjoint P Z := by
    refine Subgroup.disjoint_of_coprime_natCard ?_
    rw [h.card]
    rcases hZcard with h1 | h3
    · rw [h1]
      norm_num
    · rw [h3]
      norm_num
  have hcomm : ∀ x ∈ P, ∀ z ∈ Z, x * z = z * x := fun x hx z hz => by
    rw [hZdef] at hz
    exact Subgroup.mem_centralizer_iff.mp hz.2 x (h.le hx)
  refine ⟨A ⧸ Z, inferInstance, inferInstance, L.map (QuotientGroup.mk' Z),
    P.map (QuotientGroup.mk' Z), T.map (QuotientGroup.mk' Z),
    E25Config.map_mk_of_disjoint h Z hPZ, E25Quot.nonempty_mulEquiv_map_mk hZdef, ?_⟩
  rintro ⟨c', ⟨hc'T, hc'N⟩, hcyc⟩
  obtain ⟨c, hcT, rfl⟩ := Subgroup.mem_map.mp hc'T
  have hinj : Set.InjOn (QuotientGroup.mk' Z) (P : Set A) := E25Quot.injOn_mk_of_disjoint hPZ
  have hconj : ∀ g : A, QuotientGroup.mk' Z g ∈ Subgroup.normalizer
      ((P.map (QuotientGroup.mk' Z) : Subgroup (A ⧸ Z)) : Set (A ⧸ Z)) →
      ∀ x ∈ P, g * x * g⁻¹ ∈ P := fun g hg x hx =>
    E25Quot.conj_mem_of_mk_mem_normalizer hcomm hZ3 h.exp hg hx
  have hcN : c ∈ Subgroup.normalizer (P : Set A) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨hconj c hc'N x, fun hx => ?_⟩
    have := hconj c⁻¹ (by rw [map_inv]; exact Subgroup.inv_mem _ hc'N) _ hx
    rwa [show c⁻¹ * (c * x * c⁻¹) * c⁻¹⁻¹ = x by group] at this
  refine ⟨c, ⟨hcT, hcN⟩, fun s hs => ?_⟩
  obtain ⟨k, hk⟩ := hcyc (QuotientGroup.mk' Z s)
    ⟨Subgroup.mem_map_of_mem _ hs.1, E25Quot.map_mem_normalizer _ hs.2⟩
  refine ⟨k, fun x hx => ?_⟩
  have hcks : c ^ k ∈ Subgroup.normalizer (P : Set A) := Subgroup.pow_mem _ hcN k
  refine hinj ?_ ?_ ?_
  · exact (Subgroup.mem_normalizer_iff.mp hs.2 x).mp hx
  · exact (Subgroup.mem_normalizer_iff.mp hcks x).mp hx
  · have := hk (QuotientGroup.mk' Z x) (Subgroup.mem_map_of_mem _ hx)
    simpa using this

end CFSG.Quasithin.S146zY
