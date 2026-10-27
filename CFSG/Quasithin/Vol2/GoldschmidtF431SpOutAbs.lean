module

import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.F3Dihedral
public import CFSG.Quasithin.Background.F7Basic

public section

namespace CFSG.Quasithin.H13.F431

open CFSG.QuasithinUnique CFSG.Open CFSG.Quasithin CFSG.Quasithin.F7

section Alperin

variable {G : Type*} [Group G]

structure SpShapeA (T : Subgroup G) (Q : Fin 2 → Subgroup G) : Prop where
  Q_le : ∀ j, Q j ≤ T
  Q_norm : ∀ j, T ≤ Subgroup.normalizer (Q j : Set G)
  Q_abel : ∀ j, ∀ x ∈ Q j, ∀ y ∈ Q j, x * y = y * x
  Q_card : Nat.card (Q 1) = Nat.card (Q 0)
  A_eq : ∀ A : Subgroup G, A ≤ T → (∀ x ∈ A, ∀ y ∈ A, x * y = y * x) →
    Nat.card A = Nat.card (Q 0) → A = Q 0 ∨ A = Q 1

@[expose] def ConjToA (n : G) (Q Q' : Subgroup G) : Prop := ∀ x : G, x ∈ Q' ↔ n⁻¹ * x * n ∈ Q

theorem conjToA_iff_normalizer {n : G} {Q : Subgroup G} :
    ConjToA n Q Q ↔ n ∈ Subgroup.normalizer (Q : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  constructor
  · intro h x
    have := h (n * x * n⁻¹)
    rw [show n⁻¹ * (n * x * n⁻¹) * n = x by group] at this
    exact this.symm
  · intro h x
    have := h (n⁻¹ * x * n)
    rw [show n * (n⁻¹ * x * n) * n⁻¹ = x by group] at this
    exact this.symm

theorem fin_two_eq' : ∀ a b c : Fin 2, a ≠ b → b ≠ c → a = c := by decide

theorem mem_map_conj_iff {n x : G} {Q : Subgroup G} :
    x ∈ Q.map (MulAut.conj n).toMonoidHom ↔ n⁻¹ * x * n ∈ Q := by
  constructor
  · rintro ⟨q, hq, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rwa [show n⁻¹ * (n * q * n⁻¹) * n = q by group]
  · intro h
    refine ⟨n⁻¹ * x * n, h, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

theorem SpShapeA.conj_mem {T : Subgroup G} {Q : Fin 2 → Subgroup G} (S : SpShapeA T Q) {n : G}
    (hn : n ∈ Subgroup.normalizer (T : Set G)) (j : Fin 2) : ∃ k, ConjToA n (Q j) (Q k) := by
  set A : Subgroup G := (Q j).map (MulAut.conj n).toMonoidHom with hA
  have hAT : A ≤ T := by
    rintro _ ⟨q, hq, rfl⟩
    have := (Subgroup.mem_normalizer_iff.mp hn q).mp (S.Q_le j hq)
    simpa [MulAut.conj_apply] using this
  have hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc n * x * n⁻¹ * (n * y * n⁻¹) = n * (x * y) * n⁻¹ := by group
      _ = n * (y * x) * n⁻¹ := by rw [S.Q_abel j x hx y hy]
      _ = n * y * n⁻¹ * (n * x * n⁻¹) := by group
  have hcard : Nat.card A = Nat.card (Q 0) := by
    rw [hA, Subgroup.card_map_of_injective (MulAut.conj n).injective]
    fin_cases j
    · rfl
    · exact S.Q_card
  rcases S.A_eq A hAT hAab hcard with h | h
  · exact ⟨0, fun x => by rw [← h]; exact mem_map_conj_iff⟩
  · exact ⟨1, fun x => by rw [← h]; exact mem_map_conj_iff⟩

theorem normalizer_le_of_conj_mem {T : Subgroup G} {Q : Fin 2 → Subgroup G}
    (hT : IsSylowTwoOf T ⊤) (hQ : ∀ j, T ≤ Subgroup.normalizer (Q j : Set G))
    (hconj : ∀ n ∈ Subgroup.normalizer (T : Set G), ∀ j, ∃ k, ConjToA n (Q j) (Q k)) {n : G}
    (hn : n ∈ Subgroup.normalizer (T : Set G)) (j : Fin 2) :
    n ∈ Subgroup.normalizer (Q j : Set G) := by
  by_contra hnj
  obtain ⟨k, hk⟩ := hconj n hn j
  obtain ⟨l, hl⟩ := hconj n hn k
  have hkj : k ≠ j := by
    rintro rfl
    exact hnj (conjToA_iff_normalizer.mp hk)
  have hlk : l ≠ k := by
    rintro rfl
    apply hnj
    refine conjToA_iff_normalizer.mp fun x => ?_
    have hQ' : ∀ y, y ∈ Q j ↔ y ∈ Q l := fun y => by
      have h1 := hk (n * y * n⁻¹)
      have h2 := hl (n * y * n⁻¹)
      rw [show n⁻¹ * (n * y * n⁻¹) * n = y by group] at h1 h2
      exact h1.symm.trans h2
    rw [hQ' x]
    exact hk x
  have hlj : l = j := fin_two_eq' l k j hlk hkj
  subst hlj
  have hn2 : n * n ∈ Subgroup.normalizer (Q l : Set G) := by
    refine conjToA_iff_normalizer.mp fun x => ?_
    rw [hl x, hk (n⁻¹ * x * n), show n⁻¹ * (n⁻¹ * x * n) * n = (n * n)⁻¹ * x * (n * n) by group]
  set N := Subgroup.normalizer (T : Set G) with hN
  have hTN : T ≤ N := Subgroup.le_normalizer
  have hSyl : IsSylowTwoOf T N := F7.isSylowTwoOf_mono_right hT hTN le_top
  have hodd : ¬ 2 ∣ (T.subgroupOf N).index := F7.isSylowTwoOf_odd_relIndex hSyl
  have : (T.subgroupOf N).Normal := Subgroup.normal_subgroupOf_of_le_normalizer le_rfl
  have hpow := Subgroup.pow_index_mem (T.subgroupOf N) (⟨n, hn⟩ : N)
  have hpowT : n ^ (T.subgroupOf N).index ∈ T := by
    rw [Subgroup.mem_subgroupOf] at hpow
    simpa using hpow
  obtain ⟨r, hr⟩ : Odd (T.subgroupOf N).index := Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hodd)
  have h1 : n ^ (T.subgroupOf N).index ∈ Subgroup.normalizer (Q l : Set G) := hQ l hpowT
  have h2 : n ^ ((T.subgroupOf N).index + 1) ∈ Subgroup.normalizer (Q l : Set G) := by
    have : n ^ ((T.subgroupOf N).index + 1) = (n * n) ^ (r + 1) := by
      rw [hr, ← sq, ← pow_mul]
      congr 1
    rw [this]
    exact Subgroup.pow_mem _ hn2 _
  have h3 : n = n ^ ((T.subgroupOf N).index + 1) * (n ^ (T.subgroupOf N).index)⁻¹ := by group
  exact hnj (h3 ▸ Subgroup.mul_mem _ h2 (Subgroup.inv_mem _ h1))

theorem SpShapeA.normalizer_le {T : Subgroup G} {Q : Fin 2 → Subgroup G} (S : SpShapeA T Q)
    (hT : IsSylowTwoOf T ⊤) {n : G} (hn : n ∈ Subgroup.normalizer (T : Set G)) (j : Fin 2) :
    n ∈ Subgroup.normalizer (Q j : Set G) :=
  normalizer_le_of_conj_mem hT S.Q_norm (fun _ hn' j' => S.conj_mem hn' j') hn j

end Alperin

section Fixed

variable {G : Type*} [Group G] [Finite G]

theorem exists_fixed_ne_one {P W : Subgroup G} (hP : IsPGroup 2 P) (hW : IsPGroup 2 W)
    (hWne : W ≠ ⊥) (hnorm : ∀ n ∈ P, ∀ x ∈ W, n * x * n⁻¹ ∈ W) :
    ∃ z ∈ W, z ≠ 1 ∧ ∀ n ∈ P, n * z * n⁻¹ = z := by
  classical
  let _ : SMul ↥P ↥W := ⟨fun n x => ⟨(n : G) * (x : G) * (n : G)⁻¹, hnorm n n.2 x x.2⟩⟩
  let _ : MulAction ↥P ↥W :=
    { one_smul := fun x => Subtype.ext (by
        show (1 : G) * (x : G) * (1 : G)⁻¹ = x
        simp)
      mul_smul := fun a b x => Subtype.ext (by
        show ((a * b : ↥P) : G) * (x : G) * ((a * b : ↥P) : G)⁻¹ =
          (a : G) * ((b : G) * (x : G) * (b : G)⁻¹) * (a : G)⁻¹
        simp [mul_assoc]) }
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmod := hP.card_modEq_card_fixedPoints (α := ↥W)
  obtain ⟨k, hk⟩ := hW.exists_card_eq
  have hk1 : k ≠ 0 := by
    rintro rfl
    apply hWne
    rw [pow_zero] at hk
    exact (Subgroup.card_eq_one).mp hk
  have heven : 2 ∣ Nat.card ↥W := by
    rw [hk]
    exact dvd_pow_self 2 hk1
  have hfix_even : 2 ∣ Nat.card (MulAction.fixedPoints ↥P ↥W) := by
    have h1 : Nat.card ↥W % 2 = Nat.card (MulAction.fixedPoints ↥P ↥W) % 2 := hmod
    exact Nat.dvd_of_mod_eq_zero (by rw [← h1]; exact Nat.mod_eq_zero_of_dvd heven)
  have h1fix : (1 : ↥W) ∈ MulAction.fixedPoints ↥P ↥W := by
    rw [MulAction.mem_fixedPoints]
    intro n
    apply Subtype.ext
    show (n : G) * ((1 : ↥W) : G) * (n : G)⁻¹ = ((1 : ↥W) : G)
    simp
  have hpos : 0 < Nat.card (MulAction.fixedPoints ↥P ↥W) :=
    Nat.card_pos_iff.mpr ⟨⟨⟨1, h1fix⟩⟩, inferInstance⟩
  have hgt : 1 < Nat.card (MulAction.fixedPoints ↥P ↥W) := by
    obtain ⟨c, hc⟩ := hfix_even
    omega
  have := Finite.one_lt_card_iff_nontrivial.mp hgt
  obtain ⟨y, hy⟩ := exists_ne (⟨1, h1fix⟩ : MulAction.fixedPoints ↥P ↥W)
  refine ⟨(y.1 : ↥W), y.1.2, fun h => hy (Subtype.ext (Subtype.ext h)), fun n hn => ?_⟩
  have := (MulAction.mem_fixedPoints.mp y.2) ⟨n, hn⟩
  exact congrArg Subtype.val this

end Fixed

section ClaimA

variable {G : Type*} [Group G] [Finite G]

theorem exists_mem_normalizer_not_mem {R Tf : Subgroup G} (hR : IsPGroup 2 R) (hTfR : Tf ≤ R)
    (hne : Tf ≠ R) : ∃ x ∈ R, x ∈ Subgroup.normalizer (Tf : Set G) ∧ x ∉ Tf := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnil : Group.IsNilpotent ↥R := hR.isNilpotent
  have hU : Tf.subgroupOf R < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun h => hne ?_
    refine le_antisymm hTfR fun x hx => ?_
    have : (⟨x, hx⟩ : ↥R) ∈ Tf.subgroupOf R := h ▸ Subgroup.mem_top _
    exact this
  obtain ⟨x, hxN, hxU⟩ := IsConcreteLE.exists_of_lt
    (Group.normalizerCondition_of_isNilpotent (Tf.subgroupOf R) hU)
  refine ⟨x.1, x.2, ?_, fun h => hxU h⟩
  rw [Subgroup.mem_normalizer_iff]
  intro g
  have hx' := Subgroup.mem_normalizer_iff.mp hxN
  constructor
  · intro hg
    have := (hx' ⟨g, hTfR hg⟩).mp hg
    exact this
  · intro hg
    have hgR : g ∈ R := by
      have h1 : x.1 * g * x.1⁻¹ ∈ R := hTfR hg
      have := R.mul_mem (R.mul_mem (R.inv_mem x.2) h1) x.2
      rwa [show x.1⁻¹ * (x.1 * g * x.1⁻¹) * x.1 = g by group] at this
    have := (hx' ⟨g, hgR⟩).mpr hg
    exact this

theorem eq_of_weakly_closed {f : G} {Tf W1 M R : Subgroup G}
    (hR : IsSylowTwoOf R (Subgroup.centralizer ({f} : Set G))) (hTfR : Tf ≤ R)
    (hTf : IsSylowTwoOf Tf (M ⊓ Subgroup.centralizer ({f} : Set G)))
    (hW1p : IsPGroup 2 W1) (hW1ne : W1 ≠ ⊥)
    (hnorm : ∀ n ∈ R, n ∈ Subgroup.normalizer (Tf : Set G) → ∀ x ∈ W1, n * x * n⁻¹ ∈ W1)
    (hcent : ∀ z ∈ W1, z ≠ 1 → Subgroup.centralizer ({z} : Set G) ≤ M) : R = Tf := by
  by_contra hne
  obtain ⟨x, hxR, hxN, hxT⟩ := exists_mem_normalizer_not_mem hR.isPGroup hTfR (Ne.symm hne)
  set P : Subgroup G := R ⊓ Subgroup.normalizer (Tf : Set G) with hP
  have hPp : IsPGroup 2 P := hR.isPGroup.to_le inf_le_left
  obtain ⟨z, hzW, hz1, hzfix⟩ := exists_fixed_ne_one hPp hW1p hW1ne
    (fun n hn y hy => hnorm n hn.1 hn.2 y hy)
  have hPM : P ≤ M ⊓ Subgroup.centralizer ({f} : Set G) := by
    intro n hn
    refine ⟨?_, hR.le hn.1⟩
    refine hcent z hzW hz1 ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := hzfix n hn
    calc n * z = n * z * n⁻¹ * n := by group
      _ = z * n := by rw [this]
  set K : Subgroup G := Subgroup.normalizer (Tf : Set G) ⊓ (M ⊓ Subgroup.centralizer ({f} : Set G))
    with hK
  have hTfK : Tf ≤ K := fun t ht => ⟨Subgroup.le_normalizer ht, hTf.le ht⟩
  have hTfSyl : IsSylowTwoOf Tf K := F7.isSylowTwoOf_mono_right hTf hTfK inf_le_right
  have hPK : P ≤ K := fun n hn => ⟨hn.2, hPM hn⟩
  obtain ⟨S', hPS', hS'⟩ := exists_isSylowTwoOf_of_le hPK hPp
  obtain ⟨h, hhK, hconj⟩ := IsSylowTwoOf.exists_conj hTfSyl hS'
  have hS'Tf : S' = Tf := by
    rw [hconj]
    ext y
    rw [Subgroup.mem_map]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp hhK.1 t).mp ht
    · intro hy
      refine ⟨h⁻¹ * y * h, ?_, by group⟩
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hhK.1) y).mp hy
      simpa using this
  exact hxT (hS'Tf ▸ hPS' ⟨hxR, hxN⟩)

end ClaimA

end CFSG.Quasithin.H13.F431
