module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.A4Defs
public import CFSG.Quasithin.Background.B6Basic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

section Power

variable {G : Type*} [Group G]

theorem exists_mul_pow_eq_of_mem_normalizer {H : Subgroup G} {a b : G} (ha : a ∈ H)
    (hb : b ∈ Subgroup.normalizer (H : Set G)) (n : ℕ) :
    ∃ a' ∈ H, (a * b) ^ n = a' * b ^ n := by
  induction n with
  | zero => exact ⟨1, H.one_mem, by simp⟩
  | succ n ih =>
    obtain ⟨a', ha', h⟩ := ih
    have hbn : b ^ n ∈ Subgroup.normalizer (H : Set G) := Subgroup.pow_mem _ hb n
    have h2 : b ^ n * a * (b ^ n)⁻¹ ∈ H := (Subgroup.mem_normalizer_iff.mp hbn a).mp ha
    refine ⟨a' * (b ^ n * a * (b ^ n)⁻¹), H.mul_mem ha' h2, ?_⟩
    rw [pow_succ, h]
    group

theorem exists_pow_two_pow_mem_sup {H K : Subgroup G} (hK : IsPGroup 2 ↥K)
    (hKN : K ≤ Subgroup.normalizer (H : Set G)) {x : G} (hx : x ∈ H ⊔ K) :
    ∃ k : ℕ, x ^ 2 ^ k ∈ H := by
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left H K hKN] at hx
  obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.mp hx
  obtain ⟨k, hk⟩ := hK ⟨b, hb⟩
  have hbk : b ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  obtain ⟨a', ha', h⟩ := exists_mul_pow_eq_of_mem_normalizer ha (hKN hb) (2 ^ k)
  exact ⟨k, by rw [h, hbk, mul_one]; exact ha'⟩

theorem mem_of_mem_sup_of_odd {H K : Subgroup G} (hK : IsPGroup 2 ↥K)
    (hKN : K ≤ Subgroup.normalizer (H : Set G)) {y : G} (hy : y ∈ H ⊔ K)
    (ho : Odd (orderOf y)) : y ∈ H := by
  obtain ⟨k, hk⟩ := exists_pow_two_pow_mem_sup hK hKN hy
  have hcop : Nat.Coprime (2 ^ k) (orderOf y) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr ho)
  exact (Subgroup.zpowers_le.mpr hk) (A4.mem_zpowers_pow_of_coprime hcop)

theorem oTwoUpper_sup_eq {H K : Subgroup G} (hH : H = oTwoUpper H) (hK : IsPGroup 2 ↥K)
    (hKN : K ≤ Subgroup.normalizer (H : Set G)) : oTwoUpper (H ⊔ K) = H := by
  refine (eq_oTwoUpper_of_pow_mem le_sup_left (fun x hx => ?_) hH).symm
  exact exists_pow_two_pow_mem_sup hK hKN hx

end Power

section Bar

variable {G : Type} [Group G] (I : Subgroup G) (Q : Subgroup ↥I) [Q.Normal]

abbrev barQ (A : Subgroup G) : Subgroup (↥I ⧸ Q) :=
  (A.subgroupOf I).map (QuotientGroup.mk' Q)

variable {I Q}

theorem mem_barQ {A : Subgroup G} {d : ↥I ⧸ Q} :
    d ∈ barQ I Q A ↔ ∃ x : ↥I, (x : G) ∈ A ∧ (QuotientGroup.mk x : ↥I ⧸ Q) = d := by
  simp only [barQ, Subgroup.mem_map, Subgroup.mem_subgroupOf, QuotientGroup.mk'_apply]

theorem barQ_mono {A B : Subgroup G} (h : A ≤ B) : barQ I Q A ≤ barQ I Q B :=
  Subgroup.map_mono fun _ hx => h hx

theorem isPGroup_barQ {A : Subgroup G} (hAI : A ≤ I) (hA : IsPGroup 2 ↥A) :
    IsPGroup 2 ↥(barQ I Q A) :=
  (hA.of_equiv (Subgroup.subgroupOfEquivOfLe hAI).symm).map _

theorem barQ_le_normalizer {A B : Subgroup G} (hBN : B ≤ Subgroup.normalizer (A : Set G)) :
    barQ I Q B ≤ Subgroup.normalizer (barQ I Q A : Set (↥I ⧸ Q)) := by
  have key : ∀ b ∈ B.subgroupOf I, ∀ x ∈ barQ I Q A,
      QuotientGroup.mk' Q b * x * (QuotientGroup.mk' Q b)⁻¹ ∈ barQ I Q A := by
    intro b hb x hx
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
    refine Subgroup.mem_map.mpr ⟨b * a * b⁻¹, ?_, by simp⟩
    have hb' : (b : G) ∈ B := hb
    have := (Subgroup.mem_normalizer_iff.mp (hBN hb') (a : G)).mp ha
    rw [Subgroup.mem_subgroupOf]
    simpa using this
  intro d hd
  obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hd
  refine B6.mem_normalizer_of_forall_mem (key b hb) (fun x hx => ?_)
  simpa using key b⁻¹ ((B.subgroupOf I).inv_mem hb) x hx

theorem commutator_subgroupOf_insp {A B : Subgroup G} (hA : A ≤ I) (hB : B ≤ I) :
    ⁅A, B⁆.subgroupOf I = ⁅A.subgroupOf I, B.subgroupOf I⁆ := by
  have hAB : ⁅A, B⁆ ≤ I := Subgroup.commutator_le.mpr fun a ha b hb => by
    rw [commutatorElement_def]
    exact I.mul_mem (I.mul_mem (I.mul_mem (hA ha) (hB hb)) (I.inv_mem (hA ha))) (I.inv_mem (hB hb))
  apply Subgroup.map_injective I.subtype_injective
  rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hA,
    Subgroup.map_subgroupOf_eq_of_le hB, Subgroup.map_subgroupOf_eq_of_le hAB]

theorem barQ_commutator {A B : Subgroup G} (hA : A ≤ I) (hB : B ≤ I) :
    barQ I Q ⁅A, B⁆ = ⁅barQ I Q A, barQ I Q B⁆ := by
  unfold barQ
  rw [commutator_subgroupOf_insp hA hB, Subgroup.map_commutator]

variable [Finite G]

theorem oTwoUpper_subgroupOf {A : Subgroup G} (hA : A ≤ I) :
    oTwoUpper (A.subgroupOf I) = (oTwoUpper A).subgroupOf I := by
  apply Subgroup.map_injective I.subtype_injective
  have h1 := oTwoUpper_map I.subtype (A.subgroupOf I)
  rw [Subgroup.map_subgroupOf_eq_of_le hA] at h1
  rw [← h1, Subgroup.map_subgroupOf_eq_of_le ((oTwoUpper_le A).trans hA)]

theorem barQ_oTwoUpper {A : Subgroup G} (hA : A ≤ I) :
    barQ I Q (oTwoUpper A) = oTwoUpper (barQ I Q A) := by
  unfold barQ
  rw [oTwoUpper_map, oTwoUpper_subgroupOf hA]

theorem barQ_thompsonJ_le_of_normal {T : Subgroup G} (hT : IsSylowTwoOf T I)
    {K : Subgroup (↥I ⧸ Q)} [K.Normal] (hJK : barQ I Q (thompsonJ T) ≤ K) :
    barQ I Q (thompsonJ I) ≤ K := by
  set K' : Subgroup ↥I := K.comap (QuotientGroup.mk' Q) with hK'
  have : K'.Normal := Subgroup.Normal.comap inferInstance _
  set Kh : Subgroup G := K'.map I.subtype with hKh
  have h1 : thompsonJ T ≤ Kh := by
    intro x hx
    have hxI : x ∈ I := hT.1 (B6.thompsonJ_le T hx)
    refine ⟨⟨x, hxI⟩, ?_, rfl⟩
    exact hJK (Subgroup.mem_map.mpr ⟨⟨x, hxI⟩, hx, rfl⟩)
  have h2 : I ≤ Subgroup.normalizer (Kh : Set G) := by
    intro g hg
    have key : ∀ g' ∈ I, ∀ y ∈ Kh, g' * y * g'⁻¹ ∈ Kh := by
      intro g' hg' y hy
      obtain ⟨y', hy', rfl⟩ := hy
      exact ⟨⟨g', hg'⟩ * y' * ⟨g', hg'⟩⁻¹, Subgroup.Normal.conj_mem inferInstance y' hy' _, by simp⟩
    exact B6.mem_normalizer_of_forall_mem (key g hg) (fun y hy => by
      simpa using key g⁻¹ (I.inv_mem hg) y hy)
  have h3 : thompsonJ I ≤ Kh := B6.thompsonJ_le_of_sylow_of_le hT h1 h2
  intro d hd
  obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hd
  obtain ⟨y', hy', hy'a⟩ := h3 ha
  have : y' = a := Subtype.ext hy'a
  subst this
  exact hy'

end Bar

end CFSG.Quasithin
