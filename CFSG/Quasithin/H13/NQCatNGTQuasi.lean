module

public import CFSG.Quasithin.Background.A3ComponentsQuotient
public import CFSG.Quasithin.Background.Module

public section

namespace CFSG.Quasithin.H13.NQCat.NGT

open CFSG.Open CFSG.Quasithin

section Group

variable {G : Type*} [Group G]

theorem not_commute_of_isQuasisimple {X : Subgroup G} (hX : CFSG.IsQuasisimple ↥X) :
    ¬ ∀ a ∈ X, ∀ b ∈ X, a * b = b * a := by
  intro h
  have := CFSG.LocalCores.isQuasisimple_nontrivial hX
  have hp := hX.1
  have hbot : commutator ↥X = ⊥ := by
    rw [commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro a _
    rw [Subgroup.mem_centralizer_iff]
    intro b _
    exact Subtype.ext (h b b.2 a a.2)
  rw [Group.isPerfect_def] at hp
  rw [hp] at hbot
  obtain ⟨x, hx⟩ := exists_ne (1 : ↥X)
  exact hx (by simpa [hbot] using (Subgroup.mem_top x : x ∈ (⊤ : Subgroup ↥X)))

theorem commutator_eq_of_isQuasisimple {X : Subgroup G} (hX : CFSG.IsQuasisimple ↥X) :
    ⁅X, X⁆ = X := by
  have hp := hX.1
  rw [Group.isPerfect_def, commutator_def] at hp
  have h := congrArg (Subgroup.map X.subtype) hp
  rwa [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h

theorem eq_of_normal_quasisimple {X L : Subgroup G} (hXL : X ≤ L)
    (hn : ∀ l ∈ L, ∀ x ∈ X, l * x * l⁻¹ ∈ X) (hX : CFSG.IsQuasisimple ↥X)
    (hL : CFSG.IsQuasisimple ↥L) : X = L := by
  have hN : (X.subgroupOf L).Normal := ⟨fun x hx l => hn l l.2 x hx⟩
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hL hN with h | h
  · refine le_antisymm hXL fun l hl => ?_
    have : (⟨l, hl⟩ : L) ∈ X.subgroupOf L := h ▸ Subgroup.mem_top _
    exact this
  · exfalso
    refine not_commute_of_isQuasisimple hX fun a ha b hb => ?_
    have h1 := Subgroup.mem_center_iff.1 (h (show (⟨a, hXL ha⟩ : L) ∈ X.subgroupOf L from ha))
      ⟨b, hXL hb⟩
    exact (congrArg Subtype.val h1).symm

theorem le_quasithinGenFitting {X J : Subgroup G} (hXJ : X ≤ J)
    (hn : ∀ y ∈ J, ∀ x ∈ X, y * x * y⁻¹ ∈ X) (hX : CFSG.IsQuasisimple ↥X) :
    X ≤ quasithinGenFitting J := by
  have hN : (X.subgroupOf J).Normal := ⟨fun x hx y => hn y y.2 x hx⟩
  have hc : IsComponentOf X J :=
    ⟨hXJ, IsSubnormal.step hXJ hN (IsSubnormal.refl J), A3.isQuasisimple_iff_open.1 hX⟩
  exact le_sup_of_le_right (le_sSup hc)

theorem le_or_le_of_commute {X J G₁ G₂ : Subgroup G} (hJ : G₁ ⊔ G₂ = J)
    (hc : ∀ a ∈ G₁, ∀ b ∈ G₂, a * b = b * a) (hXJ : X ≤ J)
    (hn : ∀ y ∈ J, ∀ x ∈ X, y * x * y⁻¹ ∈ X) (hX : CFSG.IsQuasisimple ↥X) : X ≤ G₁ ∨ X ≤ G₂ := by
  have hcent : ∀ {A B : Subgroup G}, (∀ a ∈ A, ∀ b ∈ B, a * b = b * a) →
      B ≤ Subgroup.normalizer (A : Set G) := by
    intro A B hAB b hb
    rw [Subgroup.mem_normalizer_iff]
    intro a
    constructor
    · intro ha
      rw [← hAB a ha b hb, mul_assoc, mul_inv_cancel, mul_one]
      exact ha
    · intro ha
      have := hAB _ ha b hb
      have e2 : a = b * a * b⁻¹ := by
        have h3 : b * a * b⁻¹ * b = b * (b * a * b⁻¹) := this
        have h4 : b * a = b * (b * a * b⁻¹) := by simpa [mul_assoc] using h3
        exact (mul_left_cancel h4)
      rw [e2]
      exact ha
  have hn₁ : J ≤ Subgroup.normalizer (G₁ : Set G) :=
    hJ ▸ sup_le Subgroup.le_normalizer (hcent hc)
  have hn₂ : J ≤ Subgroup.normalizer (G₂ : Set G) :=
    hJ ▸ sup_le (hcent fun a ha b hb => (hc b hb a ha).symm) Subgroup.le_normalizer
  have hcomm : ∀ {A : Subgroup G}, J ≤ Subgroup.normalizer (A : Set G) → A ≤ J →
      ⁅X, A⁆ ≤ X ⊓ A := by
    intro A hA hAJ
    rw [Subgroup.commutator_le]
    intro x hx a ha
    refine ⟨?_, ?_⟩
    · rw [commutatorElement_def]
      have h1 : a * x⁻¹ * a⁻¹ ∈ X := hn a (hAJ ha) _ (X.inv_mem hx)
      have := X.mul_mem hx h1
      simpa [mul_assoc] using this
    · rw [commutatorElement_def]
      have h1 : x * a * x⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.1 (hA (hXJ hx)) a).1 ha
      exact A.mul_mem h1 (A.inv_mem ha)
  have hG₁J : G₁ ≤ J := hJ ▸ le_sup_left
  have hG₂J : G₂ ≤ J := hJ ▸ le_sup_right
  have hXA : ∀ {A : Subgroup G}, J ≤ Subgroup.normalizer (A : Set G) → A ≤ J →
      X ≤ A ∨ ⁅X, A⁆ = ⊥ := by
    intro A hA hAJ
    have hN : ((X ⊓ A).subgroupOf X).Normal := ⟨fun y hy x => by
      rw [Subgroup.mem_subgroupOf] at hy ⊢
      exact ⟨X.mul_mem (X.mul_mem x.2 hy.1) (X.inv_mem x.2),
        (Subgroup.mem_normalizer_iff.1 (hA (hXJ x.2)) _).1 hy.2⟩⟩
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hX hN with h | h
    · left
      intro x hx
      have : (⟨x, hx⟩ : X) ∈ (X ⊓ A).subgroupOf X := h ▸ Subgroup.mem_top _
      exact this.2
    · right
      have hZ : ∀ c ∈ ⁅X, A⁆, ∀ x ∈ X, c * x = x * c := by
        intro c hc x hx
        have hc' := hcomm hA hAJ hc
        have := Subgroup.mem_center_iff.1 (h (show (⟨c, hc'.1⟩ : X) ∈ (X ⊓ A).subgroupOf X
          from hc')) ⟨x, hx⟩
        exact (congrArg Subtype.val this).symm
      have h1 : ⁅⁅X, A⁆, X⁆ = ⊥ := by
        rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
        intro c hc
        rw [Subgroup.mem_centralizer_iff]
        intro x hx
        exact (hZ c hc x hx).symm
      have h2 : ⁅⁅A, X⁆, X⁆ = ⊥ := by rwa [Subgroup.commutator_comm A X]
      have h3 := Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2
      rwa [commutator_eq_of_isQuasisimple hX] at h3
  rcases hXA hn₁ hG₁J with h | h₁
  · exact Or.inl h
  rcases hXA hn₂ hG₂J with h | h₂
  · exact Or.inr h
  exfalso
  refine not_commute_of_isQuasisimple hX fun a ha b hb => ?_
  have hb' : b ∈ G₁ ⊔ G₂ := hJ ▸ hXJ hb
  have hcen : G₁ ⊔ G₂ ≤ Subgroup.centralizer (X : Set G) := by
    refine sup_le ?_ ?_
    · rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
      exact h₁
    · rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
      exact h₂
  exact Subgroup.mem_centralizer_iff.1 (hcen hb') a ha

theorem le_of_sup_zpowers {X N : Subgroup G} {t : G}
    (ht : t ∈ Subgroup.normalizer (N : Set G)) (hXJ : X ≤ N ⊔ Subgroup.zpowers t)
    (hX : CFSG.IsQuasisimple ↥X) : X ≤ N := by
  set J := N ⊔ Subgroup.zpowers t with hJ
  have hNJ : N ≤ J := le_sup_left
  have hJn : J ≤ Subgroup.normalizer (N : Set G) :=
    sup_le Subgroup.le_normalizer ((Subgroup.zpowers_le).2 ht)
  have hN : (N.subgroupOf J).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hNJ).2 hJn
  have hdec : ∀ x ∈ J, ∃ n ∈ N, ∃ k : ℤ, x = n * t ^ k := by
    intro x hx
    rw [← SetLike.mem_coe, hJ, Subgroup.coe_mul_of_right_le_normalizer_left N _
      ((Subgroup.zpowers_le).2 ht)] at hx
    obtain ⟨n, hn, s, ⟨k, rfl⟩, rfl⟩ := hx
    exact ⟨n, hn, k, rfl⟩
  have hcomm : ⁅J, J⁆ ≤ N := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    obtain ⟨n, hn, k, rfl⟩ := hdec x hx
    obtain ⟨m, hm, l, rfl⟩ := hdec y hy
    have hconj : ∀ z ∈ N, ∀ j : ℤ, t ^ j * z * (t ^ j)⁻¹ ∈ N := fun z hz j =>
      (Subgroup.mem_normalizer_iff.1 (Subgroup.zpow_mem _ ht j) z).1 hz
    rw [commutatorElement_def]
    have e : n * t ^ k * (m * t ^ l) * (n * t ^ k)⁻¹ * (m * t ^ l)⁻¹ =
        n * (t ^ k * m * (t ^ k)⁻¹) * (t ^ l * n⁻¹ * (t ^ l)⁻¹) * m⁻¹ := by
      group
    rw [e]
    exact N.mul_mem (N.mul_mem (N.mul_mem hn (hconj m hm k)) (hconj _ (N.inv_mem hn) l))
      (N.inv_mem hm)
  calc X = ⁅X, X⁆ := (commutator_eq_of_isQuasisimple hX).symm
    _ ≤ ⁅J, J⁆ := Subgroup.commutator_mono hXJ hXJ
    _ ≤ N := hcomm

end Group

section Module

variable {V : Type*} [CommGroup V]

theorem map_commV_eq {X : Subgroup (MulAut V)} {g : MulAut V}
    (hg : g ∈ Subgroup.normalizer (X : Set (MulAut V))) :
    (commV X).map g.toMonoidHom = commV X := by
  have key : ∀ h : MulAut V, h ∈ Subgroup.normalizer (X : Set (MulAut V)) →
      (commV X).map h.toMonoidHom ≤ commV X := by
    intro h hh
    rw [Subgroup.map_le_iff_le_comap, commV, Subgroup.closure_le]
    rintro _ ⟨x, hx, v, rfl⟩
    refine Subgroup.subset_closure ⟨h * x * h⁻¹, (Subgroup.mem_normalizer_iff.1 hh x).1 hx, h v, ?_⟩
    simp [MulAut.mul_apply]
  refine le_antisymm (key g hg) ?_
  have h1 := Subgroup.map_mono (f := g.toMonoidHom) (key g⁻¹ (inv_mem hg))
  rwa [Subgroup.map_map, show g.toMonoidHom.comp g⁻¹.toMonoidHom = MonoidHom.id V from by
    ext v; exact MulAut.apply_inv_self V g v, Subgroup.map_id] at h1

theorem map_fixV_eq {X : Subgroup (MulAut V)} {g : MulAut V}
    (hg : g ∈ Subgroup.normalizer (X : Set (MulAut V))) :
    (fixV X).map g.toMonoidHom = fixV X := by
  have key : ∀ h : MulAut V, h ∈ Subgroup.normalizer (X : Set (MulAut V)) →
      (fixV X).map h.toMonoidHom ≤ fixV X := by
    rintro h hh _ ⟨v, hv, rfl⟩ x hx
    have hx' : h⁻¹ * x * h⁻¹⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.1 (inv_mem hh) x).1 hx
    have := hv _ hx'
    simp only [MulAut.mul_apply, inv_inv] at this
    simp only [MulEquiv.coe_toMonoidHom]
    calc x (h v) = h (h⁻¹ (x (h v))) := (MulAut.apply_inv_self V h _).symm
      _ = h v := by rw [this]
  refine le_antisymm (key g hg) ?_
  have h1 := Subgroup.map_mono (f := g.toMonoidHom) (key g⁻¹ (inv_mem hg))
  rwa [Subgroup.map_map, show g.toMonoidHom.comp g⁻¹.toMonoidHom = MonoidHom.id V from by
    ext v; exact MulAut.apply_inv_self V g v, Subgroup.map_id] at h1

end Module

end CFSG.Quasithin.H13.NQCat.NGT
