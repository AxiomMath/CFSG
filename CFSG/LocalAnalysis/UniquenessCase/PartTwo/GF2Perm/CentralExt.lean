module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveNineteenPerm
import CFSG.GroupTheory.HuppertProduct.CubeIdentity

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.GF2Perm

open CFSG.LocalAnalysis.UniquenessCase.UC22

open scoped commutatorElement Pointwise

private theorem exists_normal_complement_central_odd {G : Type*} [Group G] [Finite G]
    {R₀ Z : Subgroup G} (hZR : Z ≤ R₀)
    (hZc : ∀ z ∈ Z, ∀ r ∈ R₀, z * r = r * z)
    (hZodd : Odd (Nat.card Z)) (hR2 : ∀ r ∈ R₀, ∃ n : ℕ, r ^ 2 ^ n ∈ Z) :
    ∃ Rc : Subgroup ↥R₀, (Z.subgroupOf R₀).IsComplement' Rc ∧ Rc.Normal := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let N : Subgroup ↥R₀ := Z.subgroupOf R₀
  have hNcenter : N ≤ Subgroup.center ↥R₀ := by
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro r
    apply Subtype.ext
    exact (hZc z.1 (Subgroup.mem_subgroupOf.mp hz) r.1 r.2).symm
  have hNnormal : N.Normal := Subgroup.normal_of_le_center hNcenter
  haveI := hNnormal
  have hquot2 : IsPGroup 2 (↥R₀ ⧸ N) := by
    intro q
    obtain ⟨r, rfl⟩ := QuotientGroup.mk'_surjective N q
    obtain ⟨n, hn⟩ := hR2 r.1 r.2
    refine ⟨n, ?_⟩
    rw [← map_pow (QuotientGroup.mk' N) r (2 ^ n)]
    exact (QuotientGroup.eq_one_iff (r ^ 2 ^ n)).mpr (Subgroup.mem_subgroupOf.mpr hn)
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hquot2
  have hidx : N.index = 2 ^ k := by
    rw [Subgroup.index_eq_card]
    exact hk
  have hNcard : Nat.card N = Nat.card Z :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZR).toEquiv
  have hNodd : Odd (Nat.card N) := by rwa [hNcard]
  have hcop : Nat.Coprime (Nat.card N) N.index := by
    rw [hidx]
    exact Nat.Coprime.pow_right k (Nat.coprime_two_left.mpr hNodd).symm
  obtain ⟨Rc, hRc⟩ := Subgroup.exists_right_complement'_of_coprime (N := N) hcop
  have hRcNormal : Rc.Normal := by
    refine Subgroup.Normal.mk fun h hh d => ?_
    obtain ⟨⟨⟨n, hn⟩, ⟨h', hh'⟩⟩, hd, -⟩ := Subgroup.IsComplement.existsUnique hRc d
    simp only at hd
    rw [← hd]
    have hcen : (h' * h * h'⁻¹) * n = n * (h' * h * h'⁻¹) :=
      Subgroup.mem_center_iff.mp (hNcenter hn) _
    have heq : n * h' * h * (n * h')⁻¹ = h' * h * h'⁻¹ := by
      calc n * h' * h * (n * h')⁻¹ = n * (h' * h * h'⁻¹) * n⁻¹ := by group
        _ = h' * h * h'⁻¹ := by rw [← hcen]; group
    rw [heq]
    exact Rc.mul_mem (Rc.mul_mem hh' hh) (Rc.inv_mem hh')
  exact ⟨Rc, hRc, hRcNormal⟩

private theorem exists_isPGroup_two_complement_of_normalComplement {G : Type*} [Group G]
    [Finite G] {R₀ Z : Subgroup G} {Rc : Subgroup ↥R₀}
    (hZR : Z ≤ R₀) (hZc : ∀ z ∈ Z, ∀ r ∈ R₀, z * r = r * z)
    (hR2 : ∀ r ∈ R₀, ∃ n : ℕ, r ^ 2 ^ n ∈ Z)
    (hRc : (Z.subgroupOf R₀).IsComplement' Rc) (hRcNormal : Rc.Normal) :
    ∃ R : Subgroup G, R ≤ R₀ ∧ IsPGroup 2 R ∧ R₀ ≤ Subgroup.normalizer (R : Set G) ∧
      Z ⊔ R = R₀ ∧ Z ⊓ R = ⊥ ∧ R.relIndex R₀ = Nat.card Z := by
  let N : Subgroup ↥R₀ := Z.subgroupOf R₀
  set R : Subgroup G := Rc.map R₀.subtype with hRdef
  have hRle : R ≤ R₀ := Subgroup.map_subtype_le Rc
  have hR2grp : IsPGroup 2 R := by
    intro r
    obtain ⟨rc, hrc, hrcr⟩ := Subgroup.mem_map.mp r.2
    obtain ⟨n, hn⟩ := hR2 (rc : ↥R₀).1 rc.2
    have hpow : (rc ^ 2 ^ n : ↥R₀) = 1 := by
      have hbot : (rc ^ 2 ^ n : ↥R₀) ∈ (⊥ : Subgroup ↥R₀) := by
        rw [← hRc.disjoint.eq_bot]
        exact ⟨Subgroup.mem_subgroupOf.mpr hn, Rc.pow_mem hrc _⟩
      simpa using Subgroup.mem_bot.mp hbot
    refine ⟨n, ?_⟩
    have hr : r = ⟨rc.1, Subgroup.mem_map.mpr ⟨rc, hrc, rfl⟩⟩ := Subtype.ext hrcr.symm
    rw [hr]
    exact Subtype.ext (by simpa using congrArg Subtype.val hpow)
  have hRsub : R.subgroupOf R₀ = Rc := by
    ext x
    constructor
    · intro hx
      rw [Subgroup.mem_subgroupOf] at hx
      obtain ⟨rc, hrc, hrcx⟩ := Subgroup.mem_map.mp hx
      have hx' : rc = x := Subtype.ext hrcx
      rwa [← hx']
    · intro hx
      exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)
  have hRnorm : R₀ ≤ Subgroup.normalizer (R : Set G) := by
    rw [← Subgroup.normal_subgroupOf_iff_le_normalizer hRle]
    rw [hRsub]
    exact hRcNormal
  have hsup : Z ⊔ R = R₀ := by
    have h := congrArg (Subgroup.map R₀.subtype) hRc.sup_eq_top
    rw [Subgroup.map_sup, Subgroup.map_top, Subgroup.range_subtype,
      Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hZR] at h
    exact h
  have hinf : Z ⊓ R = ⊥ := by
    have h := congrArg (Subgroup.map R₀.subtype) hRc.disjoint.eq_bot
    rw [Subgroup.map_inf_eq _ _ _ R₀.subtype_injective, Subgroup.map_bot,
      Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hZR] at h
    exact h
  have hRrel : R.relIndex R₀ = Nat.card Z := by
    have hcardR : Nat.card R = N.index :=
      (Subgroup.card_subtype R₀ Rc).trans hRc.symm.index_eq_card.symm
    have hcard2 : R.relIndex R₀ * Nat.card R = Nat.card R₀ := by
      have h := Subgroup.relIndex_mul_card (H := R) (K := R₀)
      rwa [inf_eq_left.mpr hRle] at h
    rw [hcardR] at hcard2
    have hNcard : Nat.card N = Nat.card Z :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZR).toEquiv
    have hcardN : Nat.card N * N.index = Nat.card R₀ := N.card_mul_index
    rw [hNcard] at hcardN
    have hpos : 0 < N.index := by
      rw [Subgroup.index_eq_card]
      exact Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_right hpos (hcard2.trans hcardN.symm)
  exact ⟨R, hRle, hR2grp, hRnorm, hsup, hinf, hRrel⟩

theorem exists_isPGroup_two_complement_central_odd {G : Type*} [Group G] [Finite G]
    {R₀ Z : Subgroup G} (hZR : Z ≤ R₀)
    (hZc : ∀ z ∈ Z, ∀ r ∈ R₀, z * r = r * z)
    (hZodd : Odd (Nat.card Z)) (hR2 : ∀ r ∈ R₀, ∃ n : ℕ, r ^ 2 ^ n ∈ Z) :
    ∃ R : Subgroup G, R ≤ R₀ ∧ IsPGroup 2 R ∧ R₀ ≤ Subgroup.normalizer (R : Set G) ∧
      Z ⊔ R = R₀ ∧ Z ⊓ R = ⊥ ∧ R.relIndex R₀ = Nat.card Z := by
  obtain ⟨Rc, hRc, hRcNormal⟩ := exists_normal_complement_central_odd hZR hZc hZodd hR2
  exact exists_isPGroup_two_complement_of_normalComplement hZR hZc hR2 hRc hRcNormal

theorem mul_pow_three_eq_of_commutator_mem_center {Q : Type*} [Group Q] {C : Subgroup Q}
    (hC : C ≤ Subgroup.center Q) (hcomm : ∀ x y : Q, ⁅x, y⁆ ∈ C)
    (hcube : ∀ x : Q, x ^ 3 ∈ C) (x y : Q) : (x * y) ^ 3 = x ^ 3 * y ^ 3 := by
  have hcx : Commute ⁅y, x⁆ x :=
    (Subgroup.mem_center_iff.mp (hC (hcomm y x)) x).symm
  have hcy : Commute ⁅y, x⁆ y :=
    (Subgroup.mem_center_iff.mp (hC (hcomm y x)) y).symm
  have h3 : ⁅y, x⁆ ^ 3 = 1 := by
    rw [← CFSG.GroupTheory.HuppertProduct.commutatorElement_pow_three_of_commute hcx]
    exact commutatorElement_eq_one_iff_commute.mpr (Subgroup.mem_center_iff.mp (hC (hcube x)) y)
  rw [CFSG.GroupTheory.HuppertProduct.mul_pow_three_of_commute hcx hcy, h3, one_mul]

private theorem exists_expThree_noncyclic_of_central_commutator
    {Q : Type*} [Group Q] [Finite Q] {C : Subgroup Q}
    (hC : C ≤ Subgroup.center Q) (hcomm : ∀ x y : Q, ⁅x, y⁆ ∈ C)
    (hcube : ∀ x : Q, x ^ 3 ∈ C) (hcard : 9 * Nat.card C ≤ Nat.card Q) :
    ∃ K : Subgroup Q, K ≠ ⊥ ∧ IsPGroup 3 ↥K ∧ (∀ k : Q, k ∈ K ↔ k ^ 3 = 1) ∧
      ¬ IsCyclic ↥K ∧ 9 ≤ Nat.card ↥K := by
  classical
  let φ : Q →* C :=
    { toFun := fun q => ⟨q ^ 3, hcube q⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun q₁ q₂ =>
        Subtype.ext (mul_pow_three_eq_of_commutator_mem_center hC hcomm hcube q₁ q₂) }
  let K : Subgroup Q := φ.ker
  have hKchar : ∀ k : Q, k ∈ K ↔ k ^ 3 = 1 := by
    intro k
    rw [MonoidHom.mem_ker]
    constructor
    · intro hk
      exact congrArg Subtype.val hk
    · intro hk
      exact Subtype.ext hk
  have hKmem : ∀ k ∈ K, k ^ 3 = 1 := fun k hk => (hKchar k).mp hk
  have hKcard : 9 ≤ Nat.card ↥K := by
    have h1 : Nat.card Q = Nat.card (Q ⧸ K) * Nat.card ↥K :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup K
    have h2 : Nat.card (Q ⧸ K) = Nat.card ↥φ.range :=
      Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv
    have h3 : Nat.card ↥φ.range ≤ Nat.card C := Subgroup.card_le_card_group _
    have h4 : Nat.card Q ≤ Nat.card ↥K * Nat.card C := by
      calc Nat.card Q = Nat.card (Q ⧸ K) * Nat.card ↥K := h1
        _ = Nat.card ↥φ.range * Nat.card ↥K := by rw [h2]
        _ ≤ Nat.card C * Nat.card ↥K := Nat.mul_le_mul_right _ h3
        _ = Nat.card ↥K * Nat.card C := mul_comm _ _
    exact Nat.le_of_mul_le_mul_right (hcard.trans h4) Nat.card_pos
  have hK3sub : ∀ k : ↥K, k ^ 3 = 1 := fun k => Subtype.ext (hKmem k.1 k.2)
  have hKnoncyc : ¬ IsCyclic ↥K := by
    intro hcyc
    haveI := hcyc
    haveI : Fintype ↥K := Fintype.ofFinite ↥K
    have hfilter : Finset.univ.filter (fun a : ↥K => a ^ 3 = 1) = Finset.univ :=
      Finset.filter_eq_self.mpr (fun a _ => hK3sub a)
    have hle := IsCyclic.card_pow_eq_one_le (α := ↥K) (n := 3) (by norm_num)
    rw [hfilter, Finset.card_univ] at hle
    have hc : Nat.card ↥K = Fintype.card ↥K := Nat.card_eq_fintype_card
    omega
  refine ⟨K, ?_, fun k => ⟨1, by simpa using hK3sub k⟩, hKchar, hKnoncyc, hKcard⟩
  intro hbot
  rw [hbot, Subgroup.card_bot] at hKcard
  omega

private theorem exists_expThree_complement_of_pow_three {X : Type*} [Group X] [Finite X]
    {R K : Subgroup X} [R.Normal] (hRK : R ≤ K) (hR2 : IsPGroup 2 R)
    (hK3 : ∀ k ∈ K, k ^ 3 ∈ R) :
    ∃ E : Subgroup X, E ≤ K ∧ E ⊓ R = ⊥ ∧ E ⊔ R = K ∧ (∀ x ∈ E, x ^ 3 = 1) ∧
      IsPGroup 3 ↥E ∧ Nat.card ↥E = R.relIndex K := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let N : Subgroup ↥K := R.subgroupOf K
  have hNnormal : N.Normal := (inferInstance : R.Normal).subgroupOf K
  haveI := hNnormal
  have hquot3 : IsPGroup 3 (↥K ⧸ N) := by
    intro q
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective N q
    refine ⟨1, ?_⟩
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff (k ^ 3)).mpr
      (Subgroup.mem_subgroupOf.mpr (hK3 k.1 k.2))
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hR2
  obtain ⟨b, hb⟩ := IsPGroup.iff_card.mp hquot3
  have hNcard : Nat.card N = 2 ^ a := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRK).toEquiv, ha]
  have hidx : N.index = 3 ^ b := by
    rw [Subgroup.index_eq_card]
    exact hb
  have hcop : Nat.Coprime (Nat.card N) N.index := by
    rw [hNcard, hidx]
    exact Nat.Coprime.pow_left a (Nat.Coprime.pow_right b (by norm_num))
  obtain ⟨Ec, hEc⟩ := Subgroup.exists_right_complement'_of_coprime (N := N) hcop
  have hE3 : ∀ x ∈ Ec.map K.subtype, x ^ 3 = 1 := by
    intro x hx
    obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp hx
    have hmemN : (e ^ 3 : ↥K) ∈ N := Subgroup.mem_subgroupOf.mpr (hK3 e.1 e.2)
    have hmemEc : (e ^ 3 : ↥K) ∈ Ec := Ec.pow_mem he 3
    have hbot : (e ^ 3 : ↥K) ∈ (⊥ : Subgroup ↥K) := by
      rw [← hEc.disjoint.eq_bot]
      exact ⟨hmemN, hmemEc⟩
    have h1 : e ^ 3 = 1 := by simpa using Subgroup.mem_bot.mp hbot
    simpa using congrArg Subtype.val h1
  refine ⟨Ec.map K.subtype, Subgroup.map_subtype_le _, ?_, ?_, hE3,
    fun x => ⟨1, Subtype.ext (by simpa using hE3 x.1 x.2)⟩, ?_⟩
  · have h := congrArg (Subgroup.map K.subtype) hEc.disjoint.eq_bot
    rw [Subgroup.map_inf_eq _ _ _ K.subtype_injective, Subgroup.map_bot,
      Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hRK] at h
    rw [inf_comm]
    exact h
  · have h := congrArg (Subgroup.map K.subtype) hEc.sup_eq_top
    rw [Subgroup.map_sup, Subgroup.map_top, Subgroup.range_subtype,
      Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hRK] at h
    rw [sup_comm]
    exact h
  · have hcardEc : Nat.card Ec = N.index := by
      have h1 := hEc.card_mul_card
      have h2 := N.card_mul_index
      exact Nat.eq_of_mul_eq_mul_left Nat.card_pos (h1.trans h2.symm)
    rw [Subgroup.card_subtype, hcardEc]
    rfl

variable {Y : Type} [Group Y] [Finite Y]

private theorem mem_normalizer_of_unique_sylow {G : Type*} [Group G] {R R₀ : Subgroup G}
    (hRle : R ≤ R₀) (hR2 : IsPGroup 2 R)
    (huniq : ∀ P : Subgroup G, P ≤ R₀ → IsPGroup 2 P → P ≤ R)
    {g : G} (hg : g ∈ Subgroup.normalizer (R₀ : Set G)) :
    g ∈ Subgroup.normalizer (R : Set G) := by
  have hfwd : ∀ h ∈ Subgroup.normalizer (R₀ : Set G), ∀ r ∈ R, h * r * h⁻¹ ∈ R := by
    intro h hh r hr
    rw [Subgroup.mem_normalizer_iff] at hh
    have hPle : Subgroup.map (MulAut.conj h).toMonoidHom R ≤ R₀ := by
      rintro _ ⟨r', hr', rfl⟩
      simpa [MulAut.conj_apply] using (hh r').mp (hRle hr')
    have hP2 : IsPGroup 2 (Subgroup.map (MulAut.conj h).toMonoidHom R) := hR2.map _
    exact huniq _ hPle hP2 (Subgroup.mem_map.mpr ⟨r, hr, rfl⟩)
  rw [Subgroup.mem_normalizer_iff]
  intro r
  refine ⟨hfwd g hg r, fun hr => ?_⟩
  have h2 := hfwd g⁻¹ (Subgroup.inv_mem _ hg) (g * r * g⁻¹) hr
  have h3 : g⁻¹ * (g * r * g⁻¹) * (g⁻¹)⁻¹ = r := by group
  rwa [h3] at h2

private theorem exists_sylow_two_data {S X R₀ Z : Subgroup Y}
    (hS : CFSG.Quasithin.IsSylowIn 2 S ⊤)
    (hSR : S ≤ Subgroup.normalizer (R₀ : Set Y)) (hRX : R₀ ≤ X)
    (hXR : X ≤ Subgroup.normalizer (R₀ : Set Y))
    (hZR : Z ≤ R₀) (hZc : ∀ z ∈ Z, ∀ x ∈ X, z * x = x * z) (hZodd : Odd (Nat.card Z))
    (hR2 : ∀ r ∈ R₀, ∃ n : ℕ, r ^ 2 ^ n ∈ Z) :
    ∃ R : Subgroup Y, R ≤ R₀ ∧ IsPGroup 2 R ∧ R₀ ≤ Subgroup.normalizer (R : Set Y) ∧
      Z ⊔ R = R₀ ∧ R.relIndex R₀ = Nat.card Z ∧
      (∀ P : Subgroup Y, P ≤ R₀ → IsPGroup 2 P → P ≤ R) ∧
      S ≤ Subgroup.normalizer (R : Set Y) ∧ X ≤ Subgroup.normalizer (R : Set Y) ∧ R ≤ S := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZcR : ∀ z ∈ Z, ∀ r ∈ R₀, z * r = r * z := fun z hz r hr => hZc z hz r (hRX hr)
  obtain ⟨R, hRR₀, hR2grp, hRnorm, hZsup, -, hRrel⟩ :=
    exists_isPGroup_two_complement_central_odd hZR hZcR hZodd hR2
  have huniq : ∀ P : Subgroup Y, P ≤ R₀ → IsPGroup 2 P → P ≤ R := by
    intro P hPR₀ hP
    have hNnormal : (R.subgroupOf R₀).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hRR₀).mpr hRnorm
    have hN2 : IsPGroup 2 (R.subgroupOf R₀) :=
      hR2grp.of_equiv (Subgroup.subgroupOfEquivOfLe hRR₀).symm
    have hodd : Odd (R.subgroupOf R₀).index := by
      rw [show (R.subgroupOf R₀).index = R.relIndex R₀ from rfl, hRrel]
      exact hZodd
    have hP2 : IsPGroup 2 (P.subgroupOf R₀) :=
      hP.of_equiv (Subgroup.subgroupOfEquivOfLe hPR₀).symm
    have hle : P.subgroupOf R₀ ≤ R.subgroupOf R₀ := by
      have hNnot : ¬ 2 ∣ (R.subgroupOf R₀).index :=
        (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp (Nat.coprime_two_left.mpr hodd)
      let QN : Sylow 2 R₀ := hN2.toSylow hNnot
      have hQN : (QN : Subgroup R₀) = R.subgroupOf R₀ := by
        ext x
        exact IsPGroup.mem_toSylow hN2 hNnot
      obtain ⟨Q, hPQ⟩ := IsPGroup.exists_le_sylow hP2
      have hNQ : R.subgroupOf R₀ ≤ (Q : Subgroup R₀) := IsPGroup.le_sylow_of_normal hN2 Q
      have hQeq : (Q : Subgroup R₀) = R.subgroupOf R₀ := by
        have h := Sylow.is_maximal' QN (Q := (Q : Subgroup R₀)) Q.isPGroup' (hQN ▸ hNQ)
        rwa [hQN] at h
      exact hPQ.trans hQeq.le
    have hmap := Subgroup.map_mono (f := R₀.subtype) hle
    rwa [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hPR₀,
      Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hRR₀] at hmap
  have hSRnorm : S ≤ Subgroup.normalizer (R : Set Y) :=
    fun s hs => mem_normalizer_of_unique_sylow hRR₀ hR2grp huniq (hSR hs)
  have hXRnorm : X ≤ Subgroup.normalizer (R : Set Y) :=
    fun x hx => mem_normalizer_of_unique_sylow hRR₀ hR2grp huniq (hXR hx)
  have hRS : R ≤ S := by
    have hSp : IsPGroup 2 S := hS.isPGroup
    have hSnot : ¬ 2 ∣ S.index := by
      rw [← Subgroup.relIndex_top_right]
      exact hS.not_dvd_relIndex
    let Ss : Sylow 2 Y := IsPGroup.toSylow (P := S) hSp hSnot
    have hSs : (Ss : Subgroup Y) = S := by
      ext x
      exact IsPGroup.mem_toSylow (P := S) hSp hSnot
    have hsup2 : IsPGroup 2 ↥(S ⊔ R) :=
      IsPGroup.to_sup_of_normal_right' (H := S) (K := R) hSp hR2grp hSRnorm
    have hmax : S ⊔ R = S :=
      (Sylow.is_maximal' Ss hsup2 (by rw [hSs]; exact le_sup_left)).trans hSs
    intro r hr
    rw [← hmax]
    exact Subgroup.mem_sup_right hr
  exact ⟨R, hRR₀, hR2grp, hRnorm, hZsup, hRrel, huniq, hSRnorm, hXRnorm, hRS⟩

private theorem image_subgroupOf_le_center_quotient {X R R₀ Z : Subgroup Y}
    [(R.subgroupOf X).Normal]
    (hRR₀ : R ≤ R₀) (hR₀X : R₀ ≤ X) (hZR : Z ≤ R₀)
    (hZc : ∀ z ∈ Z, ∀ x ∈ X, z * x = x * z) (hZsup : Z ⊔ R = R₀) :
    (R₀.subgroupOf X).map (QuotientGroup.mk' (R.subgroupOf X)) ≤
      Subgroup.center (↥X ⧸ R.subgroupOf X) := by
  intro c hc
  obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.mp hc
  have hrR₀ : (r : Y) ∈ R₀ := Subgroup.mem_subgroupOf.mp hr
  have hmem : (r : Y) ∈ Z ⊔ R := by rwa [← hZsup] at hrR₀
  have hZnormR : Z ≤ Subgroup.normalizer (R : Set Y) := by
    rw [Subgroup.le_normalizer_iff]
    intro z hz r' hr'
    rw [show z * r' * z⁻¹ = r' by
      rw [hZc z hz r' (hRR₀.trans hR₀X hr'), mul_assoc, mul_inv_cancel, mul_one]]
    exact hr'
  have hset : ((Z ⊔ R : Subgroup Y) : Set Y) = (Z : Set Y) * (R : Set Y) :=
    Subgroup.coe_mul_of_left_le_normalizer_right Z R hZnormR
  have hmem' : (r : Y) ∈ (Z : Set Y) * (R : Set Y) := by
    rw [← hset]
    exact hmem
  obtain ⟨z, hz, r', hr', hzr⟩ := Set.mem_mul.mp hmem'
  have hzX : z ∈ X := (hZR.trans hR₀X) hz
  have hr'X : r' ∈ X := (hRR₀.trans hR₀X) hr'
  have hmk : (QuotientGroup.mk' (R.subgroupOf X)) r =
      (QuotientGroup.mk' (R.subgroupOf X)) ⟨z, hzX⟩ := by
    have hr_eq : (r : ↥X) = ⟨z, hzX⟩ * ⟨r', hr'X⟩ := Subtype.ext hzr.symm
    calc (QuotientGroup.mk' (R.subgroupOf X)) r
        = (QuotientGroup.mk' (R.subgroupOf X)) (⟨z, hzX⟩ * ⟨r', hr'X⟩) := by rw [hr_eq]
      _ = (QuotientGroup.mk' (R.subgroupOf X)) ⟨z, hzX⟩ *
            (QuotientGroup.mk' (R.subgroupOf X)) ⟨r', hr'X⟩ := map_mul _ _ _
      _ = (QuotientGroup.mk' (R.subgroupOf X)) ⟨z, hzX⟩ := by
          rw [show (QuotientGroup.mk' (R.subgroupOf X)) ⟨r', hr'X⟩ = 1 from
            (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hr'), mul_one]
  rw [hmk, Subgroup.mem_center_iff]
  intro q
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (R.subgroupOf X) q
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (hZc z hz x.1 x.2).symm

private theorem card_image_subgroupOf_quotient {X R R₀ : Subgroup Y}
    [(R.subgroupOf X).Normal] (hRR₀ : R ≤ R₀) (hR₀X : R₀ ≤ X) :
    Nat.card ((R₀.subgroupOf X).map (QuotientGroup.mk' (R.subgroupOf X))) = R.relIndex R₀ := by
  have h := Subgroup.relIndex_ker (K := R₀.subgroupOf X) (QuotientGroup.mk' (R.subgroupOf X))
  rw [QuotientGroup.ker_mk'] at h
  rw [← h]
  exact Subgroup.relIndex_subgroupOf (H := R) (K := R₀) (L := X) hR₀X

private theorem nine_mul_card_image_le {X R R₀ : Subgroup Y}
    [(R.subgroupOf X).Normal] (hRR₀ : R ≤ R₀) (hR₀X : R₀ ≤ X)
    (hcard : 9 * Nat.card R₀ ≤ Nat.card X) :
    9 * Nat.card ((R₀.subgroupOf X).map (QuotientGroup.mk' (R.subgroupOf X))) ≤
      Nat.card (↥X ⧸ R.subgroupOf X) := by
  have hRX : R ≤ X := hRR₀.trans hR₀X
  have hCcard := card_image_subgroupOf_quotient (X := X) hRR₀ hR₀X
  have hQ : Nat.card (↥X ⧸ R.subgroupOf X) = R.relIndex X := rfl
  have hrelX : R.relIndex X * Nat.card R = Nat.card X := by
    have h := Subgroup.relIndex_mul_card (H := R) (K := X)
    rwa [inf_eq_left.mpr hRX] at h
  have hrelR₀ : R.relIndex R₀ * Nat.card R = Nat.card R₀ := by
    have h := Subgroup.relIndex_mul_card (H := R) (K := R₀)
    rwa [inf_eq_left.mpr hRR₀] at h
  rw [hCcard, hQ]
  have hmul : 9 * R.relIndex R₀ * Nat.card R ≤ R.relIndex X * Nat.card R := by
    calc 9 * R.relIndex R₀ * Nat.card R = 9 * (R.relIndex R₀ * Nat.card R) := by
          rw [mul_assoc]
      _ = 9 * Nat.card R₀ := by rw [hrelR₀]
      _ ≤ Nat.card X := hcard
      _ = R.relIndex X * Nat.card R := hrelX.symm
  exact Nat.le_of_mul_le_mul_right hmul Nat.card_pos

private theorem exists_expThree_quotientK {X R R₀ Z : Subgroup Y}
    [(R.subgroupOf X).Normal]
    (hRR₀ : R ≤ R₀) (hR₀X : R₀ ≤ X)
    (hZR : Z ≤ R₀) (hZc : ∀ z ∈ Z, ∀ x ∈ X, z * x = x * z) (hZsup : Z ⊔ R = R₀)
    (hexp : ∀ x ∈ X, x ^ 3 ∈ R₀)
    (hcomm : ∀ x ∈ X, ∀ y ∈ X, x * y * x⁻¹ * y⁻¹ ∈ R₀)
    (hcard : 9 * Nat.card R₀ ≤ Nat.card X) :
    ∃ K : Subgroup (↥X ⧸ R.subgroupOf X), K ≠ ⊥ ∧ IsPGroup 3 ↥K ∧
      (∀ k : ↥X ⧸ R.subgroupOf X, k ∈ K ↔ k ^ 3 = 1) ∧ ¬ IsCyclic ↥K ∧
      9 ≤ Nat.card ↥K := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let N : Subgroup ↥X := R.subgroupOf X
  let Q := ↥X ⧸ N
  let mk : ↥X →* Q := QuotientGroup.mk' N
  let C : Subgroup Q := (R₀.subgroupOf X).map mk
  have hCcenter : C ≤ Subgroup.center Q :=
    image_subgroupOf_le_center_quotient hRR₀ hR₀X hZR hZc hZsup
  have hcommQ : ∀ q₁ q₂ : Q, ⁅q₁, q₂⁆ ∈ C := by
    intro q₁ q₂
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N q₁
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective N q₂
    rw [← map_commutatorElement]
    exact Subgroup.mem_map.mpr
      ⟨⟨⁅x.1, y.1⁆, hR₀X (hcomm x.1 x.2 y.1 y.2)⟩,
        Subgroup.mem_subgroupOf.mpr (hcomm x.1 x.2 y.1 y.2), rfl⟩
  have hcubeQ : ∀ q : Q, q ^ 3 ∈ C := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N q
    rw [← map_pow]
    exact Subgroup.mem_map.mpr
      ⟨⟨x.1 ^ 3, hR₀X (hexp x.1 x.2)⟩,
        Subgroup.mem_subgroupOf.mpr (hexp x.1 x.2), rfl⟩
  have hcardQ : 9 * Nat.card C ≤ Nat.card Q := nine_mul_card_image_le hRR₀ hR₀X hcard
  exact exists_expThree_noncyclic_of_central_commutator hCcenter hcommQ hcubeQ hcardQ

private theorem exists_expThree_preimage_complement {X R R₀ : Subgroup Y}
    [(R.subgroupOf X).Normal] (hRR₀ : R ≤ R₀) (hR₀X : R₀ ≤ X)
    (hXR : X ≤ Subgroup.normalizer (R : Set Y)) (hR2 : IsPGroup 2 R)
    (K : Subgroup (↥X ⧸ R.subgroupOf X))
    (hKchar : ∀ k : ↥X ⧸ R.subgroupOf X, k ∈ K ↔ k ^ 3 = 1) :
    ∃ Wx E₀ : Subgroup ↥X,
      E₀ ⊓ R.subgroupOf X = ⊥ ∧ E₀ ⊔ R.subgroupOf X = Wx ∧
      (∀ x ∈ E₀, x ^ 3 = 1) ∧ IsPGroup 3 ↥E₀ ∧ Nat.card ↥E₀ = Nat.card ↥K ∧
      (∀ w ∈ Wx, w ^ 3 ∈ R.subgroupOf X) ∧
      (∀ w : ↥X, w ∈ Wx ↔ (QuotientGroup.mk' (R.subgroupOf X)) w ∈ K) := by
  let N : Subgroup ↥X := R.subgroupOf X
  let mk : ↥X →* (↥X ⧸ N) := QuotientGroup.mk' N
  let Wx : Subgroup ↥X := K.comap mk
  have hNWx : N ≤ Wx := by
    intro n hn
    rw [Subgroup.mem_comap]
    rw [show mk n = 1 from (QuotientGroup.eq_one_iff n).mpr hn]
    exact K.one_mem
  have hWx3 : ∀ w ∈ Wx, w ^ 3 ∈ N := by
    intro w hw
    have h4 : (mk w) ^ 3 = 1 := (hKchar (mk w)).mp (Subgroup.mem_comap.mp hw)
    refine (QuotientGroup.eq_one_iff (w ^ 3)).mp ?_
    change (QuotientGroup.mk' N) (w ^ 3) = 1
    rwa [map_pow]
  have hN2grp : IsPGroup 2 N :=
    hR2.of_equiv (Subgroup.subgroupOfEquivOfLe (hRR₀.trans hR₀X)).symm
  obtain ⟨E₀, -, hE₀inf, hE₀sup, hE₀exp, hE₀grp, hE₀card⟩ :=
    exists_expThree_complement_of_pow_three hNWx hN2grp hWx3
  have hWxrel : N.relIndex Wx = Nat.card ↥K := by
    let f : ↥Wx →* ↥K :=
      { toFun := fun w => ⟨mk w.1, w.2⟩
        map_one' := Subtype.ext (map_one mk)
        map_mul' := fun a b => Subtype.ext (map_mul mk a.1 b.1) }
    have hfker : f.ker = N.subgroupOf Wx := by
      ext w
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      refine ⟨fun h => ?_, fun hw => Subtype.ext ((QuotientGroup.eq_one_iff w.1).mpr hw)⟩
      have h1 : mk w.1 = 1 := congrArg (fun x : ↥K => (x : ↥X ⧸ N)) h
      exact (QuotientGroup.eq_one_iff w.1).mp h1
    have hfsurj : Function.Surjective f := by
      intro k
      obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective N (k : ↥X ⧸ N)
      have hxW : x ∈ Wx := by
        rw [Subgroup.mem_comap, hx]
        exact k.2
      exact ⟨⟨x, hxW⟩, Subtype.ext hx⟩
    have h := Subgroup.index_ker f
    rw [hfker, MonoidHom.range_eq_top.mpr hfsurj, Subgroup.card_top] at h
    rwa [show (N.subgroupOf Wx).index = N.relIndex Wx from rfl] at h
  have hEcard : Nat.card ↥E₀ = Nat.card ↥K := hE₀card.trans hWxrel
  exact ⟨Wx, E₀, hE₀inf, hE₀sup, hE₀exp, hE₀grp, hEcard, hWx3,
    fun w => Subgroup.mem_comap⟩

private theorem sylow_le_normalizer_of_cubePreimage {S X R : Subgroup Y}
    [(R.subgroupOf X).Normal] {K : Subgroup (↥X ⧸ R.subgroupOf X)} {Wx : Subgroup ↥X}
    (hSX : S ≤ Subgroup.normalizer (X : Set Y)) (hSR : S ≤ Subgroup.normalizer (R : Set Y))
    (hKchar : ∀ k : ↥X ⧸ R.subgroupOf X, k ∈ K ↔ k ^ 3 = 1)
    (hWxmem : ∀ w : ↥X, w ∈ Wx ↔ (QuotientGroup.mk' (R.subgroupOf X)) w ∈ K)
    (hWx3 : ∀ w ∈ Wx, w ^ 3 ∈ R.subgroupOf X) :
    S ≤ Subgroup.normalizer (Wx.map X.subtype : Set Y) := by
  have hWmem : ∀ y : Y, y ∈ Wx.map X.subtype ↔ y ∈ X ∧ y ^ 3 ∈ R := by
    intro y
    refine ⟨?_, fun hy => ?_⟩
    · rintro ⟨x, hxW, rfl⟩
      exact ⟨x.2, by simpa using Subgroup.mem_subgroupOf.mp (hWx3 x hxW)⟩
    · refine ⟨⟨y, hy.1⟩, (hWxmem ⟨y, hy.1⟩).mpr ?_, rfl⟩
      refine (hKchar _).mpr ?_
      rw [← map_pow]
      exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hy.2)
  have hSWpre : ∀ s ∈ S, ∀ y ∈ Wx.map X.subtype, s * y * s⁻¹ ∈ Wx.map X.subtype := by
    intro s hs y hy
    rw [hWmem] at hy ⊢
    refine ⟨(Subgroup.mem_normalizer_iff.mp (hSX hs) y).mp hy.1, ?_⟩
    rw [conj_pow]
    exact (Subgroup.mem_normalizer_iff.mp (hSR hs) (y ^ 3)).mp hy.2
  intro s hs
  rw [Subgroup.mem_normalizer_iff]
  refine fun y => ⟨hSWpre s hs y, fun hy => ?_⟩
  have h2 := hSWpre s⁻¹ (S.inv_mem hs) (s * y * s⁻¹) hy
  have h3 : s⁻¹ * (s * y * s⁻¹) * (s⁻¹)⁻¹ = y := by group
  rwa [h3] at h2

theorem exists_permutes_of_centralExt {S X R₀ Z : Subgroup Y}
    (hS : CFSG.Quasithin.IsSylowIn 2 S ⊤)
    (hSX : S ≤ Subgroup.normalizer (X : Set Y)) (hSR : S ≤ Subgroup.normalizer (R₀ : Set Y))
    (hRX : R₀ ≤ X) (hXR : X ≤ Subgroup.normalizer (R₀ : Set Y))
    (hZR : Z ≤ R₀) (hZc : ∀ z ∈ Z, ∀ x ∈ X, z * x = x * z) (hZodd : Odd (Nat.card Z))
    (hR2 : ∀ r ∈ R₀, ∃ n : ℕ, r ^ 2 ^ n ∈ Z)
    (hexp : ∀ x ∈ X, x ^ 3 ∈ R₀) (hcomm : ∀ x ∈ X, ∀ y ∈ X, x * y * x⁻¹ * y⁻¹ ∈ R₀)
    (hcard : 9 * Nat.card R₀ ≤ Nat.card X) :
    ∃ E : Subgroup Y, E ≤ X ∧ E ≠ ⊥ ∧ IsPGroup 3 ↥E ∧ (∀ x ∈ E, x ^ 3 = 1) ∧
      ¬ IsCyclic ↥E ∧ Permutes E S := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨R, hRR₀, hR2grp, -, hZsup, -, -, hSRnorm', hXRnorm, hRS⟩ :=
    exists_sylow_two_data hS hSR hRX hXR hZR hZc hZodd hR2
  have hNnormalX : (R.subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (hRR₀.trans hRX)).mpr hXRnorm
  haveI := hNnormalX
  obtain ⟨K, -, -, hKchar, -, hKcard⟩ :=
    exists_expThree_quotientK hRR₀ hRX hZR hZc hZsup hexp hcomm hcard
  obtain ⟨Wx, E₀, hE₀inf, hE₀sup, hE₀exp, hE₀grp, hEcard, hWx3, hWxmem⟩ :=
    exists_expThree_preimage_complement hRR₀ hRX hXRnorm hR2grp K hKchar
  have hEcard' : Nat.card ↥(E₀.map X.subtype) = Nat.card ↥K := by
    rw [Subgroup.card_subtype, hEcard]
  have hE9 : 9 ≤ Nat.card ↥(E₀.map X.subtype) := by rw [hEcard']; exact hKcard
  have hEexp : ∀ x ∈ E₀.map X.subtype, x ^ 3 = 1 := by
    intro x hx
    obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp hx
    simpa using congrArg Subtype.val (hE₀exp e he)
  have hEexp' : ∀ x : ↥(E₀.map X.subtype), x ^ 3 = 1 := by
    intro x
    exact Subtype.ext (by simpa using hEexp x.1 x.2)
  have hEgrp : IsPGroup 3 ↥(E₀.map X.subtype) := fun x => ⟨1, by simpa using hEexp' x⟩
  have hEnoncyc : ¬ IsCyclic ↥(E₀.map X.subtype) := by
    classical
    intro hcyc
    haveI := hcyc
    haveI : Fintype ↥(E₀.map X.subtype) := Fintype.ofFinite _
    have hfilter : Finset.univ.filter (fun a : ↥(E₀.map X.subtype) => a ^ 3 = 1) = Finset.univ :=
      Finset.filter_eq_self.mpr (fun a _ => hEexp' a)
    have hle := IsCyclic.card_pow_eq_one_le (α := ↥(E₀.map X.subtype)) (n := 3) (by norm_num)
    rw [hfilter, Finset.card_univ] at hle
    have hc : Nat.card ↥(E₀.map X.subtype) = Fintype.card ↥(E₀.map X.subtype) :=
      Nat.card_eq_fintype_card
    omega
  have hEinfR : E₀.map X.subtype ⊓ R = ⊥ := by
    have h := congrArg (Subgroup.map X.subtype) hE₀inf
    rw [Subgroup.map_inf_eq _ _ _ X.subtype_injective, Subgroup.map_bot,
      Subgroup.subgroupOf_map_subtype (H := R) (K := X),
      inf_eq_left.mpr (hRR₀.trans hRX)] at h
    exact h
  have hEsupR : E₀.map X.subtype ⊔ R = Wx.map X.subtype := by
    have h := congrArg (Subgroup.map X.subtype) hE₀sup
    rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype (H := R) (K := X),
      inf_eq_left.mpr (hRR₀.trans hRX)] at h
    exact h
  have hSW : S ≤ Subgroup.normalizer (Wx.map X.subtype : Set Y) :=
    sylow_le_normalizer_of_cubePreimage hSX hSRnorm' hKchar hWxmem hWx3
  refine ⟨E₀.map X.subtype, Subgroup.map_subtype_le _, ?_, hEgrp, hEexp, hEnoncyc, ?_⟩
  · intro hbot
    rw [hbot, Subgroup.card_bot] at hE9
    omega
  · refine TwelveNineteen.permutes_of_le_normalizer_sup (X := E₀.map X.subtype) (R := R)
      (T := S) hRS ?_ ((Subgroup.map_subtype_le _).trans hXRnorm)
    rw [hEsupR]
    exact hSW

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.GF2Perm
