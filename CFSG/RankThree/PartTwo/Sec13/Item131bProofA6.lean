module

public import CFSG.RankThree.PartTwo.KFacts.K412AlternatingSix
public import CFSG.RankThree.PartTwo.Sec4.Vocabulary
import CFSG.RankThree.PartTwo.KFacts.KS14MathieuAutCore
import CFSG.RankThree.PartTwo.Sec4.T444.Item434AltSix
import CFSG.LocalAnalysis.SignalizerFunctor.InvariantSylowAmbient

public section

namespace CFSG.RankThree.PartTwo.Sec13.Item131bProof

open CFSG Equiv CFSG.RankThree.PartTwo.KFacts

section Klein

variable {H : Type*} [Group H] [Finite H]

theorem isPGroup_two_sup {v w : H} (hv : v ^ 2 = 1) (hw : w ^ 2 = 1) (hvw : v * w = w * v) :
    IsPGroup 2 (Subgroup.zpowers v ⊔ Subgroup.zpowers w : Subgroup H) := by
  have h2 : ∀ {x : H}, x ^ 2 = 1 → IsPGroup 2 (Subgroup.zpowers x) := fun {x} hx g =>
    ⟨1, Subtype.ext (by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp g.2
      simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
      rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx, one_zpow])⟩
  refine (h2 hv).to_sup_of_normal_right' (h2 hw) ?_
  rw [Subgroup.zpowers_le]
  refine Subgroup.mem_normalizer_fintype fun y hy => ?_
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  rw [((Commute.zpow_right (hvw : Commute v w) k)).eq, mul_inv_cancel_right]
  exact Subgroup.zpow_mem_zpowers w k

theorem mem_normalizer_sup {v w x : H}
    (hv : x * v * x⁻¹ ∈ (Subgroup.zpowers v ⊔ Subgroup.zpowers w : Subgroup H))
    (hw : x * w * x⁻¹ ∈ (Subgroup.zpowers v ⊔ Subgroup.zpowers w : Subgroup H)) :
    x ∈ Subgroup.normalizer
      ((Subgroup.zpowers v ⊔ Subgroup.zpowers w : Subgroup H) : Set H) := by
  have hle : Subgroup.zpowers v ⊔ Subgroup.zpowers w ≤
      (Subgroup.zpowers v ⊔ Subgroup.zpowers w).comap (MulAut.conj x).toMonoidHom := by
    refine sup_le ?_ ?_ <;> rw [Subgroup.zpowers_le, Subgroup.mem_comap] <;>
      simpa [MulAut.conj_apply]
  exact Subgroup.mem_normalizer_fintype fun y hy => by
    simpa [MulAut.conj_apply] using hle hy

end Klein

@[expose] def kleinGens (i j : Fin 3) : Perm (Fin 6) × Perm (Fin 6) :=
  if j = 0 then (swap 0 1 * swap 2 3, swap 0 2 * swap 1 3)
  else if i = 0 then (swap 3 4 * swap 0 5, swap 3 5 * swap 0 4)
  else if i = j then (swap 0 3 * swap 1 4, swap 1 4 * swap 2 5)
  else (swap 0 3 * swap 1 5, swap 1 5 * swap 2 4)

theorem kleinGens_spec : ∀ i j : Fin 3,
    Perm.sign (kleinGens i j).1 = 1 ∧ Perm.sign (kleinGens i j).2 = 1 ∧
    (kleinGens i j).1 ≠ 1 ∧ (kleinGens i j).1 ^ 2 = 1 ∧ (kleinGens i j).2 ^ 2 = 1 ∧
    (kleinGens i j).1 * (kleinGens i j).2 = (kleinGens i j).2 * (kleinGens i j).1 ∧
    (K412.sixF i j * (kleinGens i j).1 * (K412.sixF i j)⁻¹ = (kleinGens i j).1 ∨
      K412.sixF i j * (kleinGens i j).1 * (K412.sixF i j)⁻¹ = (kleinGens i j).2 ∨
      K412.sixF i j * (kleinGens i j).1 * (K412.sixF i j)⁻¹ =
        (kleinGens i j).1 * (kleinGens i j).2) ∧
    (K412.sixF i j * (kleinGens i j).2 * (K412.sixF i j)⁻¹ = (kleinGens i j).1 ∨
      K412.sixF i j * (kleinGens i j).2 * (K412.sixF i j)⁻¹ = (kleinGens i j).2 ∨
      K412.sixF i j * (kleinGens i j).2 * (K412.sixF i j)⁻¹ =
        (kleinGens i j).1 * (kleinGens i j).2) := by
  decide +kernel

theorem exists_two_subgroup_alt6 (x : alternatingGroup (Fin 6)) (hx : ∃ k : ℕ, x ^ 3 ^ k = 1) :
    ∃ V : Subgroup (alternatingGroup (Fin 6)), V ≠ ⊥ ∧ IsPGroup 2 V ∧
      x ∈ Subgroup.normalizer (V : Set (alternatingGroup (Fin 6))) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set E := K412.eSix.subgroupOf (alternatingGroup (Fin 6)) with hEdef
  have hE : Nat.card E = 9 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe K412.eSix_le_alternatingGroup).toEquiv,
      K412.card_eSix]
  have hfac := Sec4.Item434Alt.factorization_alternating_six
  obtain ⟨k, hk⟩ := hx
  obtain ⟨j₀, -, hj₀⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hk)
  have hQ : IsPGroup 3 (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := j₀) (by rw [Nat.card_zpowers, hj₀])
  obtain ⟨h, hh⟩ := KS14.exists_conj_mem_of_card_nine hE hfac hQ
  obtain ⟨i, j, hij⟩ := Subgroup.mem_subgroupOf.mp (hh x (Subgroup.mem_zpowers x))
  obtain ⟨hs1, hs2, hne, hv2, hw2, hvw, hcv, hcw⟩ := kleinGens_spec i j
  set v : alternatingGroup (Fin 6) := ⟨(kleinGens i j).1, hs1⟩ with hv
  set w : alternatingGroup (Fin 6) := ⟨(kleinGens i j).2, hs2⟩ with hw
  set p := h⁻¹ * x * h with hp
  have hpv : ((p : alternatingGroup (Fin 6)) : Perm (Fin 6)) = K412.sixF i j := hij
  have hv2' : v ^ 2 = 1 := Subtype.ext (by simpa [hv] using hv2)
  have hw2' : w ^ 2 = 1 := Subtype.ext (by simpa [hw] using hw2)
  have hvw' : v * w = w * v := Subtype.ext (by simpa [hv, hw] using hvw)
  have hmem : ∀ y : alternatingGroup (Fin 6),
      ((y : Perm (Fin 6)) = (kleinGens i j).1 ∨ (y : Perm (Fin 6)) = (kleinGens i j).2 ∨
        (y : Perm (Fin 6)) = (kleinGens i j).1 * (kleinGens i j).2) →
      y ∈ (Subgroup.zpowers v ⊔ Subgroup.zpowers w : Subgroup (alternatingGroup (Fin 6))) := by
    intro y hy
    rcases hy with hy | hy | hy
    · have : y = v := Subtype.ext hy
      rw [this]
      exact Subgroup.mem_sup_left (Subgroup.mem_zpowers v)
    · have : y = w := Subtype.ext hy
      rw [this]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers w)
    · have : y = v * w := Subtype.ext hy
      rw [this]
      exact mul_mem (Subgroup.mem_sup_left (Subgroup.mem_zpowers v))
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers w))
  have hpN : p ∈ Subgroup.normalizer
      ((Subgroup.zpowers v ⊔ Subgroup.zpowers w : Subgroup (alternatingGroup (Fin 6))) :
        Set (alternatingGroup (Fin 6))) := by
    refine mem_normalizer_sup (hmem _ ?_) (hmem _ ?_)
    · simpa [hpv, hv] using hcv
    · simpa [hpv, hw] using hcw
  refine ⟨(Subgroup.zpowers v ⊔ Subgroup.zpowers w).map (MulAut.conj h).toMonoidHom, ?_,
    (isPGroup_two_sup hv2' hw2' hvw').map _, ?_⟩
  · intro hbot
    have hv1 : v ≠ 1 := fun h1 => hne (by simpa [hv] using congrArg Subtype.val h1)
    apply hv1
    have hmv : h * v * h⁻¹ ∈ (Subgroup.zpowers v ⊔ Subgroup.zpowers w).map
        (MulAut.conj h).toMonoidHom :=
      ⟨v, Subgroup.mem_sup_left (Subgroup.mem_zpowers v), by simp [MulAut.conj_apply]⟩
    rw [hbot, Subgroup.mem_bot] at hmv
    calc v = h⁻¹ * (h * v * h⁻¹) * h := by group
      _ = 1 := by rw [hmv]; group
  · refine Subgroup.mem_normalizer_fintype fun y hy => ?_
    obtain ⟨m, hm, rfl⟩ := hy
    refine ⟨p * m * p⁻¹, (Subgroup.mem_normalizer_iff.mp hpN m).mp hm, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hp]
    group

theorem exists_two_subgroup_of_isTripleCover {X : Type*} [Group X] [Finite X]
    (hX : Sec4.IsTripleCover X (alternatingGroup (Fin 6))) (x : X)
    (hx : ∃ k : ℕ, x ^ 3 ^ k = 1) :
    ∃ R : Subgroup X, R ≠ ⊥ ∧ IsPGroup 2 R ∧ x ∈ Subgroup.normalizer (R : Set X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, ⟨e⟩⟩ := hX
  set φ : X →* alternatingGroup (Fin 6) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center X)) with hφ
  obtain ⟨k, hk⟩ := hx
  obtain ⟨V, hV1, hV2, hVN⟩ := exists_two_subgroup_alt6 (φ x) ⟨k, by rw [← map_pow, hk, map_one]⟩
  set W := V.comap φ with hW
  have hxW : x ∈ Subgroup.normalizer (W : Set X) := by
    refine Subgroup.mem_normalizer_fintype fun g hg => ?_
    have hg' : φ g ∈ V := hg
    show φ (x * g * x⁻¹) ∈ V
    rw [map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.mp hVN _).mp hg'
  have hφs : Function.Surjective φ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  set f := φ.subgroupComap V with hf
  have hfs : Function.Surjective f := φ.subgroupComap_surjective V hφs
  have hker : f.ker ≤ Subgroup.center W := by
    intro g hg
    have h1 : φ g = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hg)
    have h2 : QuotientGroup.mk' (Subgroup.center X) (g : X) = 1 :=
      e.injective (by simpa [hφ] using h1)
    have hgZ : (g : X) ∈ Subgroup.center X := (QuotientGroup.eq_one_iff _).mp h2
    exact Subgroup.mem_center_iff.mpr fun y =>
      Subtype.ext ((Subgroup.mem_center_iff.mp hgZ) y)
  have : Group.IsNilpotent V := hV2.isNilpotent
  have : Group.IsNilpotent W := Subgroup.isNilpotent_of_ker_le_center f hker
  obtain ⟨P⟩ := Sylow.nonempty (p := 2) (G := W)
  have hPc := Sylow.characteristic_of_normal P inferInstance
  refine ⟨(P : Subgroup W).map W.subtype, ?_, P.isPGroup'.map _, ?_⟩
  ·
    have hV2d : 2 ∣ Nat.card V := by
      obtain ⟨n, hn⟩ := hV2.exists_card_eq
      rcases n with _ | n
      · exact absurd ((Subgroup.card_eq_one).mp (by simpa using hn)) hV1
      · rw [hn, pow_succ]
        exact dvd_mul_left 2 _
    have hVW : Nat.card V ∣ Nat.card W := by
      have h := Subgroup.card_quotient_dvd_card f.ker
      rwa [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hfs).toEquiv] at h
    have hW2 : 2 ∣ Nat.card W := hV2d.trans hVW
    intro hbot
    rw [Subgroup.map_eq_bot_iff_of_injective _ W.subtype_injective] at hbot
    have h1 := P.dvd_card_of_dvd_card hW2
    rw [hbot, Subgroup.card_bot] at h1
    omega
  · have h := SignalizerFunctor.Helpers.characteristic_subgroup_map_normalized
      (Subgroup.zpowers x) W (Subgroup.zpowers_le.mpr hxW) (P : Subgroup W)
    exact h (Subgroup.mem_zpowers x)

end CFSG.RankThree.PartTwo.Sec13.Item131bProof
