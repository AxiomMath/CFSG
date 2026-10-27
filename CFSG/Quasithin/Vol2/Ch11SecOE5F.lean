module

public import CFSG.Quasithin.Vol2.Ch11SecO11C

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS.OE5

open CFSG.Open CFSG.Blueprint

variable {Q : Type} [Group Q] [Finite Q]

omit [Finite Q] in
theorem le_of_isPGroup {S : Subgroup Q} (hS : QuasithinUnique.IsSylowTwoOf S ⊤)
    {P : Subgroup Q} (hP : IsPGroup 2 P) (hSP : S ≤ Subgroup.normalizer (P : Set Q)) : P ≤ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hi : ¬ 2 ∣ S.index := by
    rw [← show (S.subgroupOf (⊤ : Subgroup Q)).index = S.index from Subgroup.relIndex_top_right S]
    exact hS.2.2
  have hS' : ((hS.2.1.toSylow hi : Sylow 2 Q) : Subgroup Q) = S := IsPGroup.toSylow_coe hS.2.1 hi
  have h1 : IsPGroup 2 (S ⊔ P : Subgroup Q) := IsPGroup.to_sup_of_normal_right' hS.2.1 hP hSP
  rw [← hS'] at h1 ⊢
  have h2 := (hS.2.1.toSylow hi).is_maximal' h1 le_sup_left
  rw [← h2]
  exact le_sup_right

theorem mem_of_normal {S N : Subgroup Q} {z : Q} (hS2 : IsPGroup 2 S)
    (hZ : ∀ y ∈ S, (∀ x ∈ S, x * y = y * x) → y = 1 ∨ y = z) (hNS : N ≤ S)
    (hSN : S ≤ Subgroup.normalizer (N : Set Q)) (hN : N ≠ ⊥) : z ∈ N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hS2.isNilpotent
  have hNn : (N.subgroupOf S).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNS).mpr hSN
  have hNb : N.subgroupOf S ≠ ⊥ := by
    intro h
    apply hN
    rw [eq_bot_iff]
    intro x hx
    have : (⟨x, hNS hx⟩ : S) ∈ N.subgroupOf S := Subgroup.mem_subgroupOf.mpr hx
    rw [h, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)
  obtain ⟨y, hy1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hNb)
  have hyN : ((y : S) : Q) ∈ N := Subgroup.mem_subgroupOf.mp (y.2.1)
  have hyc : ∀ x ∈ S, x * ((y : S) : Q) = ((y : S) : Q) * x := fun x hx => by
    have := Subgroup.mem_center_iff.mp y.2.2 ⟨x, hx⟩
    exact congrArg Subtype.val this
  rcases hZ _ (y : S).2 hyc with h | h
  · exact absurd (Subtype.ext (Subtype.ext h)) hy1
  · rwa [← h]

theorem subsingleton_of_perfect_solvable {R : Type*} [Group R] [Group.IsPerfect R]
    [Group.IsSolvable R] : Subsingleton R := by
  by_contra h
  rw [not_subsingleton_iff_nontrivial] at h
  exact Group.IsPerfect.not_isSolvable R ‹_›

omit [Finite Q] in
theorem card_eq_sixty_mul {S B : Subgroup Q} (hB : IsL24Sub S B) :
    Nat.card B = 60 * Nat.card (CFSG.pCore 2 ↥B) := by
  obtain ⟨-, -, -, F, _, _, hF, ⟨e⟩⟩ := hB
  rw [(CFSG.pCore 2 ↥B).card_eq_card_quotient_mul_card_subgroup, Nat.card_congr e.toEquiv,
    O11.card_sl2_four hF]

theorem card_pCore_le {S B : Subgroup Q} (hQ : Nat.card Q = 126000) (hB : IsL24Sub S B) :
    Nat.card (CFSG.pCore 2 ↥B) ≤ 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hBdvd : Nat.card B ∣ 126000 := hQ ▸ Subgroup.card_subgroup_dvd_card B
  obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥B)).exists_card_eq
  rw [card_eq_sixty_mul hB, hk] at hBdvd
  rw [hk]
  by_contra h
  have hk3 : 3 ≤ k := by
    by_contra hk'
    interval_cases k <;> simp_all
  have := (Nat.mul_dvd_mul_left 60 (Nat.pow_dvd_pow 2 hk3)).trans hBdvd
  norm_num at this

theorem le_centralizer_of_ne_bot {S B : Subgroup Q} {z : Q}
    (hS : QuasithinUnique.IsSylowTwoOf S ⊤) (hQ : Nat.card Q = 126000)
    (hZN : ∀ N : Subgroup Q, N ≤ S → S ≤ Subgroup.normalizer (N : Set Q) → N ≠ ⊥ → z ∈ N)
    (hB : IsL24Sub S B) (hP1 : CFSG.pCore 2 ↥B ≠ ⊥) : B ≤ Subgroup.centralizer {z} := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P0 : Subgroup ↥B := CFSG.pCore 2 ↥B with hP0
  have hP2 : IsPGroup 2 (P0.map B.subtype) := (CFSG.pCore_isPGroup (p := 2) (G := ↥B)).map _
  have hPeq : P0.map B.subtype = pCoreOf 2 B := by
    rw [pCoreOf]
  have hPn : S ≤ Subgroup.normalizer ((P0.map B.subtype : Subgroup Q) : Set Q) := by
    rw [hPeq]
    exact hB.2.2.1.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 B)
  have hPne : P0.map B.subtype ≠ ⊥ := by
    rw [Ne, Subgroup.map_eq_bot_iff_of_injective _ B.subtype_injective]
    exact hP1
  obtain ⟨p0, hp0, rfl⟩ := hZN _ (le_of_isPGroup hS hP2 hPn) hPn hPne
  have : Group.IsSolvable (Equiv.Perm ↥P0) := Equiv.Perm.isSolvable (card_pCore_le hQ hB)
  set ψ : ↥B →* Equiv.Perm ↥P0 := (MulAut.toPerm ↥P0).comp (MulAut.conjNormal (H := P0)) with hψ
  have : Group.IsPerfect ↥B := Subgroup.isPerfect_iff.mpr hB.2.1
  have : Group.IsPerfect ↥ψ.range :=
    Group.IsPerfect.ofSurjective (f := ψ.rangeRestrict) ψ.rangeRestrict_surjective
  have hsub := subsingleton_of_perfect_solvable (R := ↥ψ.range)
  intro b hb
  have h1 : ψ ⟨b, hb⟩ = 1 := by
    have := hsub.elim ⟨ψ ⟨b, hb⟩, ⟨⟨b, hb⟩, rfl⟩⟩ 1
    exact congrArg Subtype.val this
  have h2 : (MulAut.conjNormal (H := P0) ⟨b, hb⟩) ⟨p0, hp0⟩ = ⟨p0, hp0⟩ := by
    have := congrArg (fun σ : Equiv.Perm ↥P0 => σ ⟨p0, hp0⟩) h1
    exact this
  have h3 := congrArg (fun x : ↥P0 => ((x : ↥B) : Q)) h2
  simp only [MulAut.conjNormal_apply] at h3
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc b * B.subtype p0 = (b * B.subtype p0 * b⁻¹) * b := by group
    _ = B.subtype p0 * b := by
      rw [show b * B.subtype p0 * b⁻¹ = B.subtype p0 from by simpa using h3]

end CFSG.Quasithin.Vol2.Ch11.SecS.OE5
