module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3Kbar

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped Pointwise

variable {W : Type} [CommGroup W] [Finite W] {A L T : Subgroup (MulAut W)}

private theorem s16t3_le_normalizer_of_comm {G : Type*} [Group G] {H K : Subgroup G}
    (hcomm : ∀ h ∈ H, ∀ k ∈ K, h * k = k * h) : H ≤ Subgroup.normalizer K := by
  intro h hh
  rw [Subgroup.mem_normalizer_iff]
  intro k
  have hconj : ∀ m ∈ K, h * m * h⁻¹ = m := by
    intro m hm
    rw [hcomm h hh m hm, mul_assoc, mul_inv_cancel, mul_one]
  constructor
  · intro hk
    rw [hconj k hk]
    exact hk
  · intro hk
    have h1 : h * (h * k * h⁻¹) * h⁻¹ = h * k * h⁻¹ := hconj (h * k * h⁻¹) hk
    have h2 : h * k * h⁻¹ = k := by
      have := congrArg (fun z => h⁻¹ * z * h) h1
      simpa [mul_assoc] using this
    rw [← h2]
    exact hk

private theorem s16t3_mem_sup_of_commute {G : Type*} [Group G] {H K : Subgroup G}
    (hcomm : ∀ h ∈ H, ∀ k ∈ K, h * k = k * h) {x : G} (hx : x ∈ H ⊔ K) :
    ∃ h ∈ H, ∃ k ∈ K, h * k = x := by
  have hnorm : H ≤ Subgroup.normalizer K := s16t3_le_normalizer_of_comm hcomm
  haveI : (K.subgroupOf (H ⊔ K)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (sup_le hnorm Subgroup.le_normalizer)
  have hx' : (⟨x, hx⟩ : ↥(H ⊔ K)) ∈ H.subgroupOf (H ⊔ K) ⊔ K.subgroupOf (H ⊔ K) := by
    rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right, Subgroup.subgroupOf_self]
    exact Subgroup.mem_top _
  obtain ⟨y, hy, z, hz, hyz⟩ :=
    (Subgroup.mem_sup_of_normal_right (s := H.subgroupOf (H ⊔ K))
      (t := K.subgroupOf (H ⊔ K)) (x := ⟨x, hx⟩)).1 hx'
  exact ⟨(y : G), Subgroup.mem_subgroupOf.mp hy, (z : G), Subgroup.mem_subgroupOf.mp hz,
    by simpa using congrArg Subtype.val hyz⟩

private theorem s16t3_map_mem_irrSet_of_mem {A L : Subgroup (MulAut W)}
    (hA : A ≤ Subgroup.normalizer (L : Set (MulAut W))) {g : MulAut W} (hg : g ∈ A)
    {I : Subgroup W} (hI : I ∈ irrSet L) : I.map g.toMonoidHom ∈ irrSet L :=
  CFSG.LocalAnalysis.WeakClosure81.map_mem_irrSet
    (fun x hx => (Subgroup.mem_normalizer_iff.1 (hA hg) x).1 hx)
    (fun x hx => by
      have := (Subgroup.mem_normalizer_iff.1 (hA (A.inv_mem hg)) x).1 hx
      simpa using this) hI

private theorem s16t3_smul_eq_self_of_stableUnder {X : Subgroup (MulAut W)} {I : Subgroup W}
    (h : StableUnder X I) {x : MulAut W} (hx : x ∈ X) : x • I = I := by
  refine le_antisymm ?_ ?_
  · intro u hu
    obtain ⟨v, hv, hvx⟩ := (Subgroup.mem_smul_pointwise_iff_exists u x I).1 hu
    rw [← hvx]
    exact h x hx v hv
  · intro v hv
    refine (Subgroup.mem_smul_pointwise_iff_exists v x I).2 ⟨x⁻¹ • v, ?_, ?_⟩
    · rw [MulAut.smul_def]
      exact h x⁻¹ (X.inv_mem hx) v hv
    · simp

private theorem s16t3_K0_trans {A L T N : Subgroup (MulAut W)} (h : ThreeNat A L T)
    (hNA : N ≤ A) (hNfix : ∀ a ∈ N, ∀ I ∈ irrSet L, I.map a.toMonoidHom = I)
    (hNcomm : ∀ n ∈ N, ∀ k ∈ s1t3KBar A L, n * k = k * n)
    (hNKsup : N ⊔ s1t3KBar A L = A) :
    ∀ I₁ ∈ irrSet L, ∀ I₂ ∈ irrSet L,
      ∃ k ∈ s1t3KBar A L, I₂ = I₁.map k.toMonoidHom := by
  intro I₁ hI₁ I₂ hI₂
  obtain ⟨g, hgA, hg⟩ := h.trans I₁ hI₁ I₂ hI₂
  have hgNK : g ∈ N ⊔ s1t3KBar A L := by
    rw [hNKsup]
    exact hgA.1
  obtain ⟨n, hn, k, hk, hnk⟩ := s16t3_mem_sup_of_commute hNcomm hgNK
  refine ⟨k, hk, ?_⟩
  rw [hg, ← hnk]
  have hkA : k ∈ A := (Subgroup.mem_inf.1 hk).1
  have hIk : I₁.map k.toMonoidHom ∈ irrSet L :=
    s16t3_map_mem_irrSet_of_mem h.normal hkA hI₁
  have h1 : I₁.map (n * k).toMonoidHom =
      (I₁.map k.toMonoidHom).map n.toMonoidHom := by
    rw [Subgroup.map_map]
    rfl
  rw [h1, hNfix n hn (I₁.map k.toMonoidHom) hIk]

theorem ThreeNat.exists_point_stabilizer (h : ThreeNat A L T) (h7 : Nat.card ↥(irrSet L) = 7)
    (hK : Nat.card ↥(s1t3KBar A L) = 168) :
    ∃ I₀ ∈ irrSet L, StableUnder T I₀ ∧
      ∃ J₂ : Subgroup (MulAut W), J₂ ≤ s1t3KBar A L ∧ T ⊓ s1t3KBar A L ≤ J₂ ∧
        (∀ k ∈ s1t3KBar A L, k ∈ J₂ ↔ I₀.map k.toMonoidHom = I₀) ∧
        Nat.card ↥J₂ = 3 * Nat.card ↥(T ⊓ s1t3KBar A L) ∧
        ∀ k ∈ J₂, IsPGroup 3 (Subgroup.zpowers k) → k ^ 3 = 1 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨I₀, hI₀, hI₀T⟩ := h.exists_stable_irr h.odd_card_irrSet
  obtain ⟨N, hNA, -, hNfix, hNcomm, hNKbot, hNKsup, -⟩ := h.structure_of_seven h7
  have hK0trans := s16t3_K0_trans h hNA hNfix hNcomm hNKsup
  have hK0A : s1t3KBar A L ≤ A := inf_le_left
  have hNnorm : N ≤ Subgroup.normalizer (s1t3KBar A L : Set (MulAut W)) :=
    s16t3_le_normalizer_of_comm hNcomm
  have hA_norm_K0 : A ≤ Subgroup.normalizer (s1t3KBar A L : Set (MulAut W)) :=
    calc A = N ⊔ s1t3KBar A L := hNKsup.symm
      _ ≤ Subgroup.normalizer (s1t3KBar A L : Set (MulAut W)) :=
          sup_le hNnorm Subgroup.le_normalizer
  letI : MulAction ↥(s1t3KBar A L) (Subgroup W) :=
    MulAction.compHom (Subgroup W) (Subgroup.subtype (s1t3KBar A L))
  let StabSub : Subgroup ↥(s1t3KBar A L) := MulAction.stabilizer ↥(s1t3KBar A L) I₀
  let J₂ : Subgroup (MulAut W) := StabSub.map (s1t3KBar A L).subtype
  have horbit : MulAction.orbit ↥(s1t3KBar A L) I₀ = irrSet L := by
    ext I
    constructor
    · rintro ⟨k, rfl⟩
      change (k : ↥(s1t3KBar A L)) • I₀ ∈ irrSet L
      have hk : (k : MulAut W) ∈ A := (Subgroup.mem_inf.1 k.2).1
      rw [MulAction.compHom_smul_def, Subgroup.pointwise_smul_def]
      exact s16t3_map_mem_irrSet_of_mem h.normal hk hI₀
    · intro hI
      obtain ⟨k, hkK0, hkI⟩ := hK0trans I₀ hI₀ I hI
      refine ⟨⟨k, hkK0⟩, ?_⟩
      change (⟨k, hkK0⟩ : ↥(s1t3KBar A L)) • I₀ = I
      rw [MulAction.compHom_smul_def, Subgroup.pointwise_smul_def]
      exact hkI.symm
  have hJ₂card : Nat.card ↥J₂ = 24 := by
    haveI : Fintype ↥(s1t3KBar A L) := Fintype.ofFinite _
    haveI : Fintype (MulAction.orbit ↥(s1t3KBar A L) I₀) := Fintype.ofFinite _
    haveI : Fintype (MulAction.stabilizer ↥(s1t3KBar A L) I₀) := Fintype.ofFinite _
    have hOS := MulAction.card_orbit_mul_card_stabilizer_eq_card_group
      (G := ↥(s1t3KBar A L)) I₀
    have hOS' : Nat.card (MulAction.orbit ↥(s1t3KBar A L) I₀) *
        Nat.card (MulAction.stabilizer ↥(s1t3KBar A L) I₀) =
        Nat.card ↥(s1t3KBar A L) := by
      simpa only [Nat.card_eq_fintype_card] using hOS
    have h1 : Nat.card (MulAction.orbit ↥(s1t3KBar A L) I₀) = 7 := by rw [horbit, h7]
    have h2 : Nat.card (MulAction.stabilizer ↥(s1t3KBar A L) I₀) = 24 := by
      have h := hOS'
      rw [h1, hK] at h
      omega
    rw [show J₂ = (MulAction.stabilizer ↥(s1t3KBar A L) I₀).map
        (s1t3KBar A L).subtype from rfl,
      Subgroup.card_map_of_injective (s1t3KBar A L).subtype_injective]
    exact h2
  have hTK0syl : CFSG.ABGLocalTools.IsSylowOf 2 (T ⊓ s1t3KBar A L) (s1t3KBar A L) :=
    h.sylow.inf_of_le_normalizer hK0A hA_norm_K0
  have hTK0card : Nat.card ↥(T ⊓ s1t3KBar A L) = 8 := by
    rw [hTK0syl.card_eq, hK]
    have h168 : 168 = 2 ^ 3 * 21 := by norm_num
    rw [h168, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.factorization_pow_self Nat.prime_two,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
    norm_num
  have hJ₂le : J₂ ≤ s1t3KBar A L := Subgroup.map_subtype_le _
  have hJ₂mem : ∀ k ∈ s1t3KBar A L, k ∈ J₂ ↔ I₀.map k.toMonoidHom = I₀ := by
    intro k hk
    constructor
    · intro hkJ
      obtain ⟨s, hs, hsk⟩ := Subgroup.mem_map.1 hkJ
      have hs' : (⟨k, hk⟩ : ↥(s1t3KBar A L)) ∈ StabSub := by
        have hseq : (⟨k, hk⟩ : ↥(s1t3KBar A L)) = s := Subtype.ext hsk.symm
        rw [hseq]
        exact hs
      have hsm : (⟨k, hk⟩ : ↥(s1t3KBar A L)) • I₀ = I₀ := hs'
      rw [MulAction.compHom_smul_def, Subgroup.pointwise_smul_def] at hsm
      exact hsm
    · intro hmap
      have hsm : (⟨k, hk⟩ : ↥(s1t3KBar A L)) • I₀ = I₀ := by
        rw [MulAction.compHom_smul_def, Subgroup.pointwise_smul_def]
        exact hmap
      exact Subgroup.mem_map.2 ⟨⟨k, hk⟩, hsm, rfl⟩
  have hTle : T ⊓ s1t3KBar A L ≤ J₂ := by
    have hI₀stable : StableUnder (T ⊓ s1t3KBar A L) I₀ :=
      fun x hx u hu => hI₀T x hx.1 u hu
    intro x hx
    have hsm : (⟨x, hx.2⟩ : ↥(s1t3KBar A L)) • I₀ = I₀ := by
      rw [MulAction.compHom_smul_def]
      exact s16t3_smul_eq_self_of_stableUnder hI₀stable hx
    exact Subgroup.mem_map.2 ⟨⟨x, hx.2⟩, hsm, rfl⟩
  have hJ₂card' : Nat.card ↥J₂ = 3 * Nat.card ↥(T ⊓ s1t3KBar A L) := by
    simpa only [hJ₂card, hTK0card]
  refine ⟨I₀, hI₀, hI₀T, J₂, hJ₂le, hTle, hJ₂mem, hJ₂card', ?_⟩
  intro k hkJ h3
  have hkK : k ∈ s1t3KBar A L := hJ₂le hkJ
  obtain ⟨m, hm⟩ := (IsPGroup.iff_card (p := 3) (G := Subgroup.zpowers k)).1 h3
  have horder : orderOf k = 3 ^ m := by
    rw [← Nat.card_zpowers]
    exact hm
  have hdvd168 : 3 ^ m ∣ 168 := by
    have h := Subgroup.orderOf_dvd_natCard (s1t3KBar A L) hkK
    rw [hK] at h
    rwa [horder] at h
  have hmle : m ≤ 1 := by
    by_contra hlt
    have h2 : 2 ≤ m := by omega
    have h9m : 9 ∣ 3 ^ m := by
      obtain ⟨j, hmj⟩ := Nat.exists_eq_add_of_le h2
      rw [hmj, pow_add]
      exact dvd_mul_right 9 (3 ^ j)
    exact (by norm_num : ¬ (9 : ℕ) ∣ 168) (h9m.trans hdvd168)
  have h3dvd : orderOf k ∣ 3 := by
    rw [horder]
    rcases (by omega : m = 0 ∨ m = 1) with rfl | rfl <;> norm_num
  exact (orderOf_dvd_iff_pow_eq_one).1 h3dvd

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
