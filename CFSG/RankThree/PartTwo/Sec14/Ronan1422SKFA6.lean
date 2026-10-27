module

public import CFSG.RankThree.PartTwo.Sec14.Ronan1422SKFBase
public import CFSG.RankThree.PartTwo.Sec14.Ronan1422SDefs

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan1422S

open Equiv Equiv.Perm Subgroup
open CFSG.RankThree.PartTwo.Sec4.Item434AltPerm

theorem kfA6_aut_fix (B : Subgroup (alternatingGroup (Fin 6))) (hB : Nat.card B = 9)
    (α : MulAut (alternatingGroup (Fin 6))) (hα : ∀ b ∈ B, α b = b) :
    ∃ b ∈ B, α = MulAut.conj b := by
  obtain ⟨g, rfl⟩ := exists_eq_map_conj_F06 hB
  have hfix : ∀ f ∈ F06, ((MulAut.conj g)⁻¹ * α * MulAut.conj g) f = f := by
    intro f hf
    have h1 : α (MulAut.conj g f) = MulAut.conj g f :=
      hα _ (Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hf)
    rw [MulAut.mul_apply, MulAut.mul_apply, h1, MulAut.inv_apply_self]
  obtain ⟨b₀, hb₀, hα'⟩ :=
    exists_mem_F06_eq_conj_of_fix ((MulAut.conj g)⁻¹ * α * MulAut.conj g) hfix
  refine ⟨g * b₀ * g⁻¹, Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hb₀, ?_⟩
  rw [map_mul, map_mul, map_inv, ← hα']
  group

theorem kfA6_no_two_normalized (B : Subgroup (alternatingGroup (Fin 6))) (hB : Nat.card B = 9)
    (Q : Subgroup (MulAut (alternatingGroup (Fin 6)))) (hQ : IsPGroup 2 Q)
    (hN : ∀ b ∈ B, ∀ q ∈ Q, MulAut.conj b * q * (MulAut.conj b)⁻¹ ∈ Q) : Q = ⊥ := by
  obtain ⟨g, rfl⟩ := exists_eq_map_conj_F06 hB
  have hinj : Function.Injective (MulAut.conj (MulAut.conj g)⁻¹).toMonoidHom :=
    (MulAut.conj (MulAut.conj g)⁻¹).injective
  obtain ⟨k, hk⟩ : ∃ k : ℕ, Nat.card Q = 2 ^ k := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact hQ.exists_card_eq
  obtain ⟨Q', hQ'⟩ : ∃ Q' : Subgroup (MulAut (alternatingGroup (Fin 6))),
      Q' = Q.map (MulAut.conj (MulAut.conj g)⁻¹).toMonoidHom := ⟨_, rfl⟩
  have hX : ¬ 3 ∣ Nat.card Q' := by
    rw [hQ', Subgroup.card_map_of_injective hinj, hk]
    intro h
    have h3 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
    norm_num at h3
  have hN' : F06.map MulAut.conj ≤
      Subgroup.normalizer (Q' : Set (MulAut (alternatingGroup (Fin 6)))) := by
    rintro _ ⟨f, hf, rfl⟩
    apply Subgroup.mem_normalizer_fintype
    intro n hn
    rw [SetLike.mem_coe, hQ'] at hn ⊢
    obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.mp hn
    have hxB : g * f * g⁻¹ ∈ F06.map (MulAut.conj g).toMonoidHom :=
      Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hf
    have hx := hN _ hxB q hq
    have hc : MulAut.conj (g * f * g⁻¹) =
        MulAut.conj g * MulAut.conj f * (MulAut.conj g)⁻¹ := by
      rw [map_mul, map_mul, map_inv]
    have key : MulAut.conj f * (MulAut.conj (MulAut.conj g)⁻¹).toMonoidHom q *
        (MulAut.conj f)⁻¹ = (MulAut.conj (MulAut.conj g)⁻¹).toMonoidHom
          (MulAut.conj (g * f * g⁻¹) * q * (MulAut.conj (g * f * g⁻¹))⁻¹) := by
      rw [hc]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [key]
    exact Subgroup.mem_map_of_mem _ hx
  have hQbot : Q' = ⊥ := eq_bot_of_F06_le_normalizer hX hN'
  rw [hQ'] at hQbot
  exact (Subgroup.map_eq_bot_iff_of_injective Q hinj).mp hQbot

theorem kfA6_mem_normalizer_F06 (x : alternatingGroup (Fin 6)) :
    x ∈ Subgroup.normalizer (F06 : Set (alternatingGroup (Fin 6))) ↔
      ∀ v : Fin 2 → ZMod 3, ∃ w : Fin 2 → ZMod 3,
        (x : Perm (Fin 6)) * vecPerm2 6 v = vecPerm2 6 w * (x : Perm (Fin 6)) := by
  constructor
  · intro hx v
    have hv : alt6 (vecPerm2 6 v) (sign_vecPerm2_six v) ∈ F06 := mem_F06.mpr ⟨v, rfl⟩
    obtain ⟨w, hw⟩ := mem_F06.mp ((Subgroup.mem_normalizer_iff.mp hx _).mp hv)
    have hw' : vecPerm2 6 w = (x : Perm (Fin 6)) * vecPerm2 6 v * (x : Perm (Fin 6))⁻¹ := hw
    exact ⟨w, by rw [hw']; group⟩
  · intro hv
    apply Subgroup.mem_normalizer_fintype
    intro n hn
    rw [SetLike.mem_coe] at hn
    obtain ⟨v, hv'⟩ := mem_F06.mp hn
    obtain ⟨w, hw⟩ := hv v
    rw [SetLike.mem_coe]
    refine mem_F06.mpr ⟨w, ?_⟩
    show vecPerm2 6 w = (x : Perm (Fin 6)) * (n : Perm (Fin 6)) * (x : Perm (Fin 6))⁻¹
    rw [← hv', eq_mul_inv_iff_mul_eq]
    exact hw.symm

theorem kfA6_card_normalizer_F06 :
    Nat.card (Subgroup.normalizer (F06 : Set (alternatingGroup (Fin 6)))) = 36 := by
  have hmem : ∀ σ : Perm (Fin 6),
      σ ∈ (Subgroup.normalizer (F06 : Set (alternatingGroup (Fin 6)))).map
          (alternatingGroup (Fin 6)).subtype ↔
        (sign σ = 1 ∧ ∀ v : Fin 2 → ZMod 3, ∃ w : Fin 2 → ZMod 3,
          σ * vecPerm2 6 v = vecPerm2 6 w * σ) := by
    intro σ
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨mem_alternatingGroup.mp x.2, (kfA6_mem_normalizer_F06 x).mp hx⟩
    · rintro ⟨hs, hv⟩
      exact ⟨alt6 σ hs, (kfA6_mem_normalizer_F06 (alt6 σ hs)).mpr hv, rfl⟩
  rw [← Subgroup.card_map_of_injective (alternatingGroup (Fin 6)).subtype_injective,
    Nat.card_congr (Equiv.subtypeEquivRight hmem), Nat.card_eq_fintype_card,
    Fintype.card_subtype]
  decide +kernel

theorem kfA6_card_normalizer_conj (B : Subgroup (alternatingGroup (Fin 6)))
    (hB : Nat.card B = 9) :
    Nat.card (Subgroup.normalizer (B : Set (alternatingGroup (Fin 6)))) = 36 := by
  obtain ⟨g, rfl⟩ := exists_eq_map_conj_F06 hB
  rw [← Subgroup.map_equiv_normalizer_eq F06 (MulAut.conj g),
    Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective]
  exact kfA6_card_normalizer_F06

@[expose] def kfA6_inv6 : Perm (Fin 6) := swap 1 2 * swap 4 5

theorem kfA6_sign_inv6 : sign kfA6_inv6 = 1 := by decide +kernel

theorem kfA6_inv6_conj : ∀ v : Fin 2 → ZMod 3,
    kfA6_inv6 * vecPerm2 6 v * kfA6_inv6⁻¹ = (vecPerm2 6 v)⁻¹ := by
  decide +kernel

theorem kfA6_inverts_F06 (f : alternatingGroup (Fin 6)) (hf : f ∈ F06) :
    alt6 kfA6_inv6 kfA6_sign_inv6 * f * (alt6 kfA6_inv6 kfA6_sign_inv6)⁻¹ = f⁻¹ := by
  obtain ⟨v, hv⟩ := mem_F06.mp hf
  apply Subtype.ext
  show kfA6_inv6 * (f : Perm (Fin 6)) * kfA6_inv6⁻¹ = (f : Perm (Fin 6))⁻¹
  rw [← hv]
  exact kfA6_inv6_conj v

theorem kfA6_conj_inverts {G : Type*} [Group G] (h t f : G) (htf : t * f * t⁻¹ = f⁻¹) :
    h * t * h⁻¹ * (h * f * h⁻¹) * (h * t * h⁻¹)⁻¹ = (h * f * h⁻¹)⁻¹ := by
  calc h * t * h⁻¹ * (h * f * h⁻¹) * (h * t * h⁻¹)⁻¹ = h * (t * f * t⁻¹) * h⁻¹ := by group
    _ = h * f⁻¹ * h⁻¹ := by rw [htf]
    _ = (h * f * h⁻¹)⁻¹ := by group

theorem kfA6_inverts (B : Subgroup (alternatingGroup (Fin 6))) (hB : Nat.card B = 9) :
    ∃ g : alternatingGroup (Fin 6), ∀ b ∈ B, g * b * g⁻¹ = b⁻¹ := by
  obtain ⟨h, rfl⟩ := exists_eq_map_conj_F06 hB
  refine ⟨h * alt6 kfA6_inv6 kfA6_sign_inv6 * h⁻¹, ?_⟩
  rintro _ ⟨f, hf, rfl⟩
  exact kfA6_conj_inverts h _ f (kfA6_inverts_F06 f hf)

theorem kf1422AutA6_holds : KF1422AutA6 := by
  unfold KF1422AutA6
  exact ⟨fun B hB α hα => kfA6_aut_fix B hB α hα,
    fun B hB Q hQ hN => kfA6_no_two_normalized B hB Q hQ hN,
    fun B hB => kfA6_card_normalizer_conj B hB,
    fun B hB => kfA6_inverts B hB⟩

end CFSG.RankThree.PartTwo.Sec14.Ronan1422S
