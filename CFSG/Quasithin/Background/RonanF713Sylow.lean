module

public import CFSG.Quasithin.Background.F7Basic
public import CFSG.Quasithin.Background.E1Inherit

public section

namespace CFSG.Quasithin.RonanF713

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7

variable {G : Type*} [Group G]

theorem finite_conjSub (g : G) (H : Subgroup G) [Finite ↥H] : Finite ↥(conjSub g H) :=
  Finite.of_equiv ↥H
    (Subgroup.equivMapOfInjective H (MulAut.conj g).toMonoidHom
      (MulEquiv.injective (MulAut.conj g))).toEquiv

theorem isSylowTwoOf_pCoreOf_le_loc {T H : Subgroup G} (h : IsSylowTwoOf T H) :
    pCoreOf 2 H ≤ T := by
  obtain ⟨S, hS⟩ := F7.isSylowTwoOf_exists_sylow h
  have : (CFSG.pCore 2 ↥H).Normal := CFSG.pCore_normal (p := 2) (G := ↥H)
  have hle : CFSG.pCore 2 ↥H ≤ (S : Subgroup ↥H) :=
    (CFSG.pCore_isPGroup (p := 2) (G := ↥H)).le_sylow_of_normal S
  rintro _ ⟨y, hy, rfl⟩
  have := hle hy
  rw [hS] at this
  simpa [Subgroup.mem_subgroupOf] using this

theorem isSylowTwoOf_exists_conj_le_loc {T H : Subgroup G} [Finite ↥H] (h : IsSylowTwoOf T H)
    {P : Subgroup G} (hPH : P ≤ H) (hP : IsPGroup 2 P) : ∃ x ∈ H, P ≤ conjSub x T := by
  obtain ⟨S, hS⟩ := F7.isSylowTwoOf_exists_sylow h
  have hP' : IsPGroup 2 (P.subgroupOf H) :=
    hP.of_equiv (Subgroup.subgroupOfEquivOfLe hPH).symm
  obtain ⟨Q, hQ⟩ := hP'.exists_le_sylow
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq H S Q
  refine ⟨x, x.2, fun y hy => ?_⟩
  have h1 : (⟨y, hPH hy⟩ : H) ∈ Q := hQ (by simpa [Subgroup.mem_subgroupOf] using hy)
  rw [← hx] at h1
  have h2 : (⟨y, hPH hy⟩ : H) ∈ ((x • S : Sylow 2 H) : Subgroup H) := h1
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at h2
  have h3 : (MulAut.conj x)⁻¹ • (⟨y, hPH hy⟩ : H) ∈ (S : Subgroup H) := h2
  rw [hS] at h3
  rw [mem_conjSub]
  simpa [Subgroup.mem_subgroupOf, MulAut.conj_inv_apply, mul_assoc] using h3

theorem exists_isMaxSubgroupIn_loc {H X : Subgroup G} [Finite ↥H] (h : X < H) :
    ∃ N, IsMaxSubgroupIn H N ∧ X ≤ N := by
  haveI : Finite ↥{K : Subgroup G | X ≤ K ∧ K < H} := by
    haveI : Finite (Subgroup ↥H) :=
      Finite.of_injective (fun K : Subgroup H => (K : Set H)) SetLike.coe_injective
    refine Finite.of_injective
      (fun K : {K : Subgroup G | X ≤ K ∧ K < H} => K.1.subgroupOf H) ?_
    intro K₁ K₂ hK
    have hK' : K₁.1.subgroupOf H = K₂.1.subgroupOf H := hK
    apply Subtype.ext
    calc K₁.1 = (K₁.1.subgroupOf H).map H.subtype :=
          (Subgroup.map_subgroupOf_eq_of_le K₁.2.2.le).symm
      _ = (K₂.1.subgroupOf H).map H.subtype := by rw [hK']
      _ = K₂.1 := Subgroup.map_subgroupOf_eq_of_le K₂.2.2.le
  obtain ⟨N, hXN, hN⟩ :=
    (Set.toFinite {K : Subgroup G | X ≤ K ∧ K < H}).exists_le_maximal ⟨le_rfl, h⟩
  refine ⟨N, ⟨hN.1.2, fun K hNK hKH => ?_⟩, hXN⟩
  by_contra hne
  have hKH' : K < H := lt_of_le_of_ne hKH hne
  exact absurd (hN.2 ⟨hXN.trans hNK.le, hKH'⟩ hNK.le) (not_le_of_gt hNK)

theorem twoResidual_isTwoQuotient_loc {H : Subgroup G} [Finite ↥H] :
    ∀ x ∈ H, ∃ k : ℕ, x ^ 2 ^ k ∈ twoResidual H := by
  intro x hx
  have hex : ∀ N : {N : Subgroup G // N ≤ H}, ∃ k : ℕ,
      (H ≤ Subgroup.normalizer (N.1 : Set G) ∧ ∀ y ∈ H, ∃ k : ℕ, y ^ 2 ^ k ∈ N.1) →
        x ^ 2 ^ k ∈ N.1 := by
    intro N
    by_cases h : H ≤ Subgroup.normalizer (N.1 : Set G) ∧ ∀ y ∈ H, ∃ k : ℕ, y ^ 2 ^ k ∈ N.1
    · obtain ⟨k, hk⟩ := h.2 x hx
      exact ⟨k, fun _ => hk⟩
    · exact ⟨0, fun h' => absurd h' h⟩
  choose f hf using hex
  haveI : Finite (Subgroup ↥H) :=
    Finite.of_injective (fun K : Subgroup H => (K : Set H)) SetLike.coe_injective
  haveI : Finite {N : Subgroup G // N ≤ H} :=
    Finite.of_injective (fun N : {N : Subgroup G // N ≤ H} => N.1.subgroupOf H) (by
      rintro ⟨N₁, h₁⟩ ⟨N₂, h₂⟩ hN
      have hN' : N₁.subgroupOf H = N₂.subgroupOf H := hN
      apply Subtype.ext
      calc N₁ = (N₁.subgroupOf H).map H.subtype := (Subgroup.map_subgroupOf_eq_of_le h₁).symm
        _ = (N₂.subgroupOf H).map H.subtype := by rw [hN']
        _ = N₂ := Subgroup.map_subgroupOf_eq_of_le h₂)
  obtain ⟨k, hk⟩ := (Set.finite_range f).bddAbove
  refine ⟨k, ?_⟩
  rw [mem_twoResidual_iff]
  intro N h1 h2 h3
  have hfN : x ^ 2 ^ (f ⟨N, h1⟩) ∈ N := hf ⟨N, h1⟩ ⟨h2, h3⟩
  have hle : f ⟨N, h1⟩ ≤ k := hk ⟨⟨N, h1⟩, rfl⟩
  have : x ^ 2 ^ k = (x ^ 2 ^ (f ⟨N, h1⟩)) ^ 2 ^ (k - f ⟨N, h1⟩) := by
    rw [← pow_mul, ← pow_add, Nat.add_sub_cancel' hle]
  rw [this]
  exact N.pow_mem hfN _

private theorem loc_exists_relIndex_eq_two_pow {K H : Subgroup G} [Finite ↥H]
    (hHK : H ≤ Subgroup.normalizer (K : Set G)) (hH : ∀ d ∈ H, ∃ k : ℕ, d ^ (2 ^ k) ∈ K) :
    ∃ n : ℕ, K.relIndex H = 2 ^ n := by
  have := Subgroup.normal_subgroupOf_of_le_normalizer hHK
  have hp : IsPGroup 2 (↥H ⧸ K.subgroupOf H) := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H d =>
      obtain ⟨k, hk⟩ := hH d d.2
      refine ⟨k, ?_⟩
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      simpa using hk
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hp
  exact ⟨n, hn⟩

theorem sup_twoResidual_eq_loc {H T : Subgroup G} [Finite ↥H] (hT : IsSylowTwoOf T H) :
    T ⊔ twoResidual H = H := by
  have hKH : twoResidual H ≤ H := twoResidual_le H
  obtain ⟨n, hn⟩ := loc_exists_relIndex_eq_two_pow (le_normalizer_twoResidual H)
    (twoResidual_isTwoQuotient_loc (H := H))
  have h1 : (T ⊔ twoResidual H).relIndex H ∣ (twoResidual H).relIndex H :=
    Subgroup.relIndex_dvd_of_le_left H le_sup_right
  have h2 : (T ⊔ twoResidual H).relIndex H ∣ T.relIndex H :=
    Subgroup.relIndex_dvd_of_le_left H le_sup_left
  have hodd : ¬ 2 ∣ (T ⊔ twoResidual H).relIndex H := fun hd => hT.2.2 (hd.trans h2)
  rw [hn] at h1
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
  have hm0 : m = 0 := by
    by_contra hne
    exact hodd (hm ▸ dvd_pow_self 2 hne)
  rw [hm0, pow_zero] at hm
  exact le_antisymm (sup_le hT.1 hKH) (Subgroup.relIndex_eq_one.mp hm)

theorem le_tauOf_loc {H T A : Subgroup G} (hT : IsSylowTwoOf T H) (hA : A ≤ T)
    (hAab : IsElemAbelian 2 A) : A ⊔ pCoreOf 2 H ≤ E1.tauOf H T A := by
  refine sup_le ?_ ?_
  · intro a ha
    refine (E1.mem_tauOf_of_le hT.1).mpr ⟨hA ha, fun b hb => ?_⟩
    have h := E1.commute_of_isElemAbelian hAab ha hb
    rw [commutatorElement_def, h]
    simp
  · intro o ho
    have hoT : o ∈ T := isSylowTwoOf_pCoreOf_le_loc hT ho
    refine (E1.mem_tauOf_of_le hT.1).mpr ⟨hoT, fun b hb => ?_⟩
    have hbH : b ∈ H := hT.1 (hA hb)
    have h1 := (Subgroup.mem_normalizer_iff.mp
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H hbH) o⁻¹).mp (inv_mem ho)
    have h2 : o * b * o⁻¹ * b⁻¹ = o * (b * o⁻¹ * b⁻¹) := by
      simp only [mul_assoc]
    rw [commutatorElement_def, h2]
    exact Subgroup.mul_mem _ ho h1

end CFSG.Quasithin.RonanF713
