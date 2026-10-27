module

public import CFSG.Sporadic.Recognition.LyonsAS4Centr

public section

namespace CFSG.Sporadic.Recognition.LyonsSims

open Subgroup

section Generic

variable {G : Type*} [Group G] (X : G)

abbrev NormX : Subgroup G := normalizer (zpowers X : Set G)

theorem self_mem_normX : X ∈ NormX X := by
  rw [mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
    exact Subgroup.mem_zpowers_iff.2 ⟨k, by group⟩
  · intro hh
    have : X⁻¹ * (X * h * X⁻¹) * X ∈ zpowers X :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers X)) hh)
        (Subgroup.mem_zpowers X)
    simpa [mul_assoc] using this

variable {X}

theorem conj_mem_centralizer {n : G} (hn : n ∈ NormX X) {m : G}
    (hm : m ∈ centralizer ({X} : Set G)) :
    n * m * n⁻¹ ∈ centralizer ({X} : Set G) := by
  rw [mem_centralizer_singleton_iff] at hm ⊢
  have hX : n⁻¹ * X * n ∈ zpowers X := by
    have hn' : n⁻¹ ∈ NormX X := Subgroup.inv_mem _ hn
    have := (mem_normalizer_iff.1 hn' X).1 (Subgroup.mem_zpowers X)
    simpa using this
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hX
  have hmk : m * X ^ k = X ^ k * m := (Commute.zpow_right (show Commute m X from hm) k).eq
  calc n * m * n⁻¹ * X = n * m * (n⁻¹ * X * n) * n⁻¹ := by group
    _ = n * m * X ^ k * n⁻¹ := by rw [hk]
    _ = n * (X ^ k * m) * n⁻¹ := by rw [mul_assoc n m, hmk, ← mul_assoc]
    _ = n * (n⁻¹ * X * n) * m * n⁻¹ := by rw [hk]; group
    _ = X * (n * m * n⁻¹) := by group

@[expose] def conjCent (n : ↥(NormX X)) : MulAut ↥(centralizer ({X} : Set G)) where
  toFun m := ⟨(n : G) * m * (n : G)⁻¹, conj_mem_centralizer n.2 m.2⟩
  invFun m := ⟨(n : G)⁻¹ * m * (n : G), by
    simpa using conj_mem_centralizer (Subgroup.inv_mem _ n.2) m.2⟩
  left_inv m := Subtype.ext (by simp [mul_assoc])
  right_inv m := Subtype.ext (by simp [mul_assoc])
  map_mul' a b := Subtype.ext (by simp [mul_assoc])

theorem conjCent_apply (n : ↥(NormX X)) (m : ↥(centralizer ({X} : Set G))) :
    ((conjCent n m : ↥(centralizer ({X} : Set G))) : G) = (n : G) * m * (n : G)⁻¹ := rfl

theorem zpowers_conj_eq {n : G} (hn : n ∈ NormX X) : zpowers (n * X * n⁻¹) = zpowers X := by
  have := mem_normalizer_iff_map_conj_eq.1 hn
  rw [MonoidHom.map_zpowers] at this
  exact this

theorem map_zpowers_conjCent (n : ↥(NormX X)) :
    (zpowers (⟨X, self_mem_centralizer_singleton X⟩ : ↥(centralizer ({X} : Set G)))).map
      (conjCent n).toMonoidHom =
    zpowers (⟨X, self_mem_centralizer_singleton X⟩ : ↥(centralizer ({X} : Set G))) := by
  rw [MonoidHom.map_zpowers]
  have h1 := zpowers_conj_eq n.2
  set a : ↥(centralizer ({X} : Set G)) := (conjCent n).toMonoidHom
    ⟨X, self_mem_centralizer_singleton X⟩ with ha
  have haG : (a : G) = (n : G) * X * (n : G)⁻¹ := rfl
  apply le_antisymm
  · rw [Subgroup.zpowers_le, Subgroup.mem_zpowers_iff]
    have : (a : G) ∈ zpowers X := by
      rw [haG, ← h1]; exact Subgroup.mem_zpowers _
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 this
    exact ⟨k, Subtype.ext (by rw [Subgroup.coe_zpow]; exact hk)⟩
  · rw [Subgroup.zpowers_le, Subgroup.mem_zpowers_iff]
    have : X ∈ zpowers (a : G) := by
      rw [haG, h1]; exact Subgroup.mem_zpowers _
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 this
    exact ⟨k, Subtype.ext (by rw [Subgroup.coe_zpow]; exact hk)⟩

@[expose] def conjQuot (n : ↥(NormX X)) : CentQuot X ≃* CentQuot X :=
  QuotientGroup.congr _ _ (conjCent n) (map_zpowers_conjCent n)

theorem conjQuot_mk (n : ↥(NormX X)) (m : ↥(centralizer ({X} : Set G))) :
    conjQuot n (QuotientGroup.mk m) = QuotientGroup.mk (conjCent n m) :=
  QuotientGroup.congr_mk _ _ _ _ _

@[expose] def normQuotAut : ↥(NormX X) →* MulAut (CentQuot X) where
  toFun := conjQuot
  map_one' := by
    ext q
    induction q using QuotientGroup.induction_on with
    | H m =>
      change conjQuot 1 (QuotientGroup.mk m) = QuotientGroup.mk m
      rw [conjQuot_mk]
      congr 1
      exact Subtype.ext (by simp [conjCent_apply])
  map_mul' a b := by
    ext q
    induction q using QuotientGroup.induction_on with
    | H m =>
      change conjQuot (a * b) (QuotientGroup.mk m) =
        conjQuot a (conjQuot b (QuotientGroup.mk m))
      rw [conjQuot_mk, conjQuot_mk, conjQuot_mk]
      congr 1
      exact Subtype.ext (by simp [conjCent_apply, mul_assoc])

theorem normQuotAut_mk (n : ↥(NormX X)) (m : ↥(centralizer ({X} : Set G))) :
    normQuotAut n (QuotientGroup.mk m) = QuotientGroup.mk (conjCent n m) :=
  conjQuot_mk n m

theorem centralizer_le_normX : centralizer ({X} : Set G) ≤ NormX X := by
  intro g hg
  rw [mem_normalizer_iff]
  intro h
  have hgX : g * X = X * g := mem_centralizer_singleton_iff.1 hg
  constructor
  · intro hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
    have : g * X ^ k = X ^ k * g := (Commute.zpow_right (show Commute g X from hgX) k).eq
    exact Subgroup.mem_zpowers_iff.2 ⟨k, by rw [this]; group⟩
  · intro hh
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hh
    have : g * X ^ k = X ^ k * g := (Commute.zpow_right (show Commute g X from hgX) k).eq
    refine Subgroup.mem_zpowers_iff.2 ⟨k, ?_⟩
    calc X ^ k = g⁻¹ * (g * X ^ k) := by group
      _ = g⁻¹ * (X ^ k * g) := by rw [this]
      _ = g⁻¹ * (g * h * g⁻¹) * g := by rw [← hk]; group
      _ = h := by group

theorem normQuotAut_of_mem_zpowers {y : G} (hy : y ∈ zpowers X) :
    normQuotAut (⟨y, Subgroup.le_normalizer hy⟩ : ↥(NormX X)) = 1 := by
  ext q
  induction q using QuotientGroup.induction_on with
  | H m =>
    change normQuotAut (⟨y, Subgroup.le_normalizer hy⟩ : ↥(NormX X)) (QuotientGroup.mk m) =
      QuotientGroup.mk m
    rw [normQuotAut_mk]
    congr 1
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    apply Subtype.ext
    have hm : (m : G) * X ^ k = X ^ k * (m : G) :=
      (Commute.zpow_right (show Commute (m : G) X from mem_centralizer_singleton_iff.1 m.2) k).eq
    show X ^ k * (m : G) * (X ^ k)⁻¹ = (m : G)
    rw [← hm]
    group

abbrev NormQuot (X : G) : Type _ :=
  ↥(NormX X) ⧸ (zpowers X).subgroupOf (NormX X)

@[expose] def normQuotAutQuot : NormQuot X →* MulAut (CentQuot X) :=
  QuotientGroup.lift _ normQuotAut (by
    intro n hn
    obtain ⟨y, hy⟩ : ∃ y : G, y ∈ zpowers X ∧ y = (n : G) := ⟨n, hn, rfl⟩
    have := normQuotAut_of_mem_zpowers (X := X) hy.1
    rw [MonoidHom.mem_ker]
    have h2 : n = (⟨y, Subgroup.le_normalizer hy.1⟩ : ↥(NormX X)) := Subtype.ext hy.2.symm
    rw [h2]
    exact this)

end Generic

end CFSG.Sporadic.Recognition.LyonsSims
