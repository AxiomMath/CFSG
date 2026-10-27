module

public import CFSG.RankThree.PartTwo.Sec12.Notation

public section

namespace CFSG.RankThree.PartTwo.Sec12

open CFSG.ABGLocalTools (IsSylowOf)

variable {G : Type*} [Group G]

theorem isSylowOf_exists_conj [Finite G] {p : ℕ} [Fact p.Prime] {P P' D : Subgroup G}
    (hP : IsSylowOf p P D) (hP' : IsSylowOf p P' D) :
    ∃ x ∈ D, P' = P.map (MulAut.conj x).toMonoidHom := by
  obtain ⟨Q, rfl⟩ := hP
  obtain ⟨Q', rfl⟩ := hP'
  obtain ⟨d, hd⟩ := MulAction.exists_smul_eq D Q Q'
  refine ⟨d, d.2, ?_⟩
  rw [← hd, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
  ext y
  constructor
  · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨_, ⟨z, hz, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨_, ⟨z, hz, rfl⟩, rfl⟩

theorem map_conj_center (P : Subgroup G) (x : G) :
    (Subgroup.center (P.map (MulAut.conj x).toMonoidHom)).map
        (P.map (MulAut.conj x).toMonoidHom).subtype =
      ((Subgroup.center P).map P.subtype).map (MulAut.conj x).toMonoidHom := by
  ext y
  simp only [Subgroup.mem_map, Subgroup.mem_center_iff, Subgroup.coe_subtype]
  constructor
  · rintro ⟨⟨_, ⟨z, hz, rfl⟩⟩, hc, rfl⟩
    refine ⟨z, ⟨⟨z, hz⟩, fun w => ?_, rfl⟩, rfl⟩
    have := hc ⟨(MulAut.conj x).toMonoidHom w, w, w.2, rfl⟩
    have := congrArg Subtype.val this
    simp only [Subgroup.coe_mul, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    have h2 := congrArg (fun t => x⁻¹ * t * x) this
    simpa [mul_assoc] using h2
  · rintro ⟨_, ⟨z, hc, rfl⟩, rfl⟩
    refine ⟨⟨(MulAut.conj x).toMonoidHom z, z, z.2, rfl⟩, fun w => ?_, rfl⟩
    obtain ⟨_, ⟨v, hv, rfl⟩⟩ := w
    have e : v * (z : G) = z * v := congrArg Subtype.val (hc ⟨v, hv⟩)
    apply Subtype.ext
    simp only [Subgroup.coe_mul, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc x * v * x⁻¹ * (x * z * x⁻¹) = x * (v * z) * x⁻¹ := by group
      _ = x * (z * v) * x⁻¹ := by rw [e]
      _ = x * z * x⁻¹ * (x * v * x⁻¹) := by group

theorem map_conj_inf_centralizer {A L : Subgroup G} {x : G}
    (hA : x ∈ Subgroup.normalizer (A : Set G)) (hL : x ∈ Subgroup.normalizer (L : Set G)) :
    (A ⊓ Subgroup.centralizer (L : Set G)).map (MulAut.conj x).toMonoidHom =
      A ⊓ Subgroup.centralizer (L : Set G) := by
  have key : ∀ y : G, ∀ z ∈ Subgroup.normalizer (A : Set G),
      z ∈ Subgroup.normalizer (L : Set G) → y ∈ A ⊓ Subgroup.centralizer (L : Set G) →
        z * y * z⁻¹ ∈ A ⊓ Subgroup.centralizer (L : Set G) := by
    intro y z hzA hzL hy
    obtain ⟨hyA, hyL⟩ := Subgroup.mem_inf.mp hy
    refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp hzA y).mp hyA, ?_⟩
    rw [Subgroup.mem_centralizer_iff] at hyL ⊢
    intro l hl
    have hl' : z⁻¹ * l * z ∈ L := by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem hzL) l).mp hl
      simpa using this
    have e := hyL _ hl'
    calc l * (z * y * z⁻¹) = z * ((z⁻¹ * l * z) * y) * z⁻¹ := by group
      _ = z * (y * (z⁻¹ * l * z)) * z⁻¹ := by rw [e]
      _ = z * y * z⁻¹ * l := by group
  ext y
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact key w x hA hL hw
  · intro hy
    refine ⟨x⁻¹ * y * x, ?_, by simp [MulAut.conj_apply, mul_assoc]⟩
    have := key y x⁻¹ (inv_mem hA) (inv_mem hL) hy
    simpa using this

theorem le_center_iff_of_isSylowOf [Finite G] {p : ℕ} [Fact p.Prime] {X A L : Subgroup G}
    (hXA : X ≤ Subgroup.normalizer (A : Set G))
    (hN : ∀ Q : Subgroup G, IsSylowOf p Q X → Q ≤ Subgroup.normalizer (L : Set G))
    {P P' : Subgroup G} (hP : IsSylowOf p P X) (hP' : IsSylowOf p P' X) :
    A ⊓ Subgroup.centralizer (L : Set G) ≤ (Subgroup.center P).map P.subtype ↔
      A ⊓ Subgroup.centralizer (L : Set G) ≤ (Subgroup.center P').map P'.subtype := by
  have key : ∀ Q Q' : Subgroup G, IsSylowOf p Q X → IsSylowOf p Q' X →
      A ⊓ Subgroup.centralizer (L : Set G) ≤ (Subgroup.center Q).map Q.subtype →
        A ⊓ Subgroup.centralizer (L : Set G) ≤ (Subgroup.center Q').map Q'.subtype := by
    intro Q Q' hQ hQ' hle
    have hDX : Q ⊔ Q' ≤ X := sup_le hQ.le hQ'.le
    obtain ⟨x, hx, rfl⟩ := isSylowOf_exists_conj (hQ.of_le le_sup_left hDX)
      (hQ'.of_le le_sup_right hDX)
    have hxL : x ∈ Subgroup.normalizer (L : Set G) := sup_le (hN Q hQ) (hN _ hQ') hx
    rw [map_conj_center, ← map_conj_inf_centralizer (hXA (hDX hx)) hxL]
    exact Subgroup.map_mono hle
  exact ⟨key P P' hP hP', key P' P hP' hP⟩

theorem Sec12Std.not_le_center {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G}
    {L : Subgroup G} (h : Sec12Std G A c L)
    (hN : ∀ Q : Subgroup G, IsSylowOf 3 Q
      (Subgroup.normalizer (A : Set G) ⊓ Subgroup.normalizer (Subgroup.zpowers c : Set G)) →
        Q ≤ Subgroup.normalizer (L : Set G))
    {P : Subgroup G} (hP : IsSylowOf 3 P
      (Subgroup.normalizer (A : Set G) ⊓ Subgroup.normalizer (Subgroup.zpowers c : Set G))) :
    ¬ A ⊓ Subgroup.centralizer (L : Set G) ≤ (Subgroup.center P).map P.subtype := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P₀, hP₀, hB⟩ := h.exists_sylow
  exact fun hle => hB ((le_center_iff_of_isSylowOf inf_le_left hN hP₀ hP).mpr hle)

end CFSG.RankThree.PartTwo.Sec12
