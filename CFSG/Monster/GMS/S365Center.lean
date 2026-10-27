module

public import CFSG.Monster.GMS.S365CenterModel
public import CFSG.Monster.GMS.S365
public import CFSG.Monster.GMS.S4FamilyDefs

public section

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic

namespace S365

section Transport

variable {G : Type*} [Group G]

theorem mem_eightSet_iff {x y t h : G} :
    h ∈ ({1, x, y, t, x * y, x * t, y * t, x * y * t} : Set G) ↔
      ∃ c, InKlein x y c ∧ (h = c ∨ h = c * t) := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro (hh | hh | hh | hh | hh | hh | hh | hh)
    · exact ⟨1, Or.inl rfl, Or.inl hh⟩
    · exact ⟨x, Or.inr (Or.inl rfl), Or.inl hh⟩
    · exact ⟨y, Or.inr (Or.inr (Or.inl rfl)), Or.inl hh⟩
    · exact ⟨1, Or.inl rfl, Or.inr (hh.trans (one_mul t).symm)⟩
    · exact ⟨x * y, Or.inr (Or.inr (Or.inr rfl)), Or.inl hh⟩
    · exact ⟨x, Or.inr (Or.inl rfl), Or.inr hh⟩
    · exact ⟨y, Or.inr (Or.inr (Or.inl rfl)), Or.inr hh⟩
    · exact ⟨x * y, Or.inr (Or.inr (Or.inr rfl)), Or.inr hh⟩
  · rintro ⟨c, hc | hc | hc | hc, hh | hh⟩ <;> simp [hh, hc]

theorem commute_of_inKlein {x y c g : G} (hx : g * x = x * g) (hy : g * y = y * g)
    (hc : InKlein x y c) : g * c = c * g := by
  rcases hc with rfl | rfl | rfl | rfl
  · simp
  · exact hx
  · exact hy
  · calc g * (x * y) = g * x * y := (mul_assoc _ _ _).symm
      _ = x * g * y := by rw [hx]
      _ = x * (g * y) := mul_assoc _ _ _
      _ = x * (y * g) := by rw [hy]
      _ = x * y * g := (mul_assoc _ _ _).symm

theorem centralizer_inf_inf_eq_of_inKlein {x y c : G} (hc : InKlein x y c) :
    Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({y} : Set G) ⊓
        Subgroup.centralizer ({c} : Set G) =
      Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({y} : Set G) := by
  ext g
  simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨hxy, -⟩
    exact hxy
  · rintro ⟨hx, hy⟩
    exact ⟨⟨hx, hy⟩, commute_of_inKlein hx hy hc⟩

theorem conj_commute_iff (g k x : G) :
    g * k * g⁻¹ * (g * x * g⁻¹) = g * x * g⁻¹ * (g * k * g⁻¹) ↔ k * x = x * k := by
  have e1 : g * k * g⁻¹ * (g * x * g⁻¹) = g * (k * x) * g⁻¹ := by group
  have e2 : g * x * g⁻¹ * (g * k * g⁻¹) = g * (x * k) * g⁻¹ := by group
  rw [e1, e2]
  exact conj_eq_conj_iff g _ _

theorem centerIn_conj {x y t : G} (h : CenterIn x y t) (g : G) :
    CenterIn (g * x * g⁻¹) (g * y * g⁻¹) (g * t * g⁻¹) := by
  intro h' hh' hcen
  obtain ⟨k, rfl⟩ : ∃ k, h' = g * k * g⁻¹ := ⟨g⁻¹ * h' * g, by group⟩
  have hmem : ∀ k' : G, g * k' * g⁻¹ ∈ Subgroup.centralizer ({g * x * g⁻¹} : Set G) ⊓
      Subgroup.centralizer ({g * y * g⁻¹} : Set G) ⊓ Subgroup.centralizer ({g * t * g⁻¹} : Set G) ↔
      k' ∈ Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({y} : Set G) ⊓
        Subgroup.centralizer ({t} : Set G) := by
    intro k'
    simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff, conj_commute_iff]
  have hkcen : ∀ m ∈ Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({y} : Set G) ⊓
      Subgroup.centralizer ({t} : Set G), k * m = m * k := by
    intro m hm
    have h1 := hcen (g * m * g⁻¹) ((hmem m).2 hm)
    have e1 : g * k * g⁻¹ * (g * m * g⁻¹) = g * (k * m) * g⁻¹ := by group
    have e2 : g * m * g⁻¹ * (g * k * g⁻¹) = g * (m * k) * g⁻¹ := by group
    rw [e1, e2] at h1
    exact (conj_eq_conj_iff g _ _).1 h1
  obtain ⟨c, hc, hkc⟩ := mem_eightSet_iff.1 (h k ((hmem k).1 hh') hkcen)
  refine mem_eightSet_iff.2 ⟨g * c * g⁻¹, hc.conj g, ?_⟩
  rcases hkc with h1 | h1
  · exact Or.inl (by rw [h1])
  · exact Or.inr (by rw [h1]; group)

theorem centerIn_of_mem_cosetSet {x y t w : G} (hK : IsKlein x y) (he : IsEightExt x y t)
    (hw : w ∈ cosetSet x y t) (h : CenterIn x y w) : CenterIn x y t := by
  intro h' hh' hcen
  rw [centralizer_inf_inf_eq_of_mem_cosetSet hw] at hh' hcen
  obtain ⟨c, hc, hhc⟩ := mem_eightSet_iff.1 (h h' hh' hcen)
  obtain ⟨c₀, hc₀, rfl⟩ := mem_cosetSet_iff.1 hw
  refine mem_eightSet_iff.2 ?_
  rcases hhc with h1 | h1
  · exact ⟨c, hc, Or.inl h1⟩
  · refine ⟨c * c₀, hK.mul_mem hc hc₀, Or.inr ?_⟩
    rw [h1, commute_of_inKlein he.2.1 he.2.2.1 hc₀, ← mul_assoc]

theorem centerIn_of_conj {x y t x' y' t' : G} (hK' : IsKlein x' y') (he' : IsEightExt x' y' t')
    (hcl : ∃ g : G, g * x * g⁻¹ = x' ∧ g * y * g⁻¹ = y' ∧ g * t * g⁻¹ ∈ cosetSet x' y' t')
    (h : CenterIn x y t) : CenterIn x' y' t' := by
  obtain ⟨g, hgx, hgy, hgt⟩ := hcl
  have h1 := centerIn_conj h g
  rw [hgx, hgy] at h1
  exact centerIn_of_mem_cosetSet hK' he' hgt h1

theorem inKlein_of_mem_eightSet_of_notMem_cosetSet {x y t₁ t₃ h : G} (hK : IsKlein x y)
    (h1 : IsEightExt x y t₁) (hn : t₃ ∉ cosetSet x y t₁)
    (hh1 : h ∈ ({1, x, y, t₁, x * y, x * t₁, y * t₁, x * y * t₁} : Set G))
    (hh3 : h ∈ ({1, x, y, t₃, x * y, x * t₃, y * t₃, x * y * t₃} : Set G)) : InKlein x y h := by
  obtain ⟨c, hc, hhc⟩ := mem_eightSet_iff.1 hh1
  obtain ⟨c', hc', hhc'⟩ := mem_eightSet_iff.1 hh3
  rcases hhc with e1 | e1
  · rw [e1]
    exact hc
  rcases hhc' with e3 | e3
  · rw [e3]
    exact hc'
  exfalso
  apply hn
  have hc'c' : c' * c' = 1 := hK.mul_self_of_mem hc'
  have e' : t₃ = c' * c * t₁ := by
    calc t₃ = c' * (c' * t₃) := by rw [← mul_assoc, hc'c', one_mul]
      _ = c' * (c * t₁) := by rw [← e3, e1]
      _ = c' * c * t₁ := (mul_assoc _ _ _).symm
  refine mem_cosetSet_iff.2 ⟨c' * c, hK.mul_mem hc' hc, ?_⟩
  rw [e', commute_of_inKlein h1.2.1 h1.2.2.1 (hK.mul_mem hc' hc)]

end Transport

section Main

variable {G : Type} [Group G] [Finite G] {d₀ : B} {a z₀ : G}

theorem centerIn_of_isEightExt
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀) {x y t : G}
    (hl : IsLineTriple a x y) (he : IsEightExt x y t) : CenterIn x y t := by
  have key : ∀ n : ℕ, (n = 1 ∨ n = 3 ∨ n = 4) → twoBCount z₀ x y t = n → CenterIn x y t := by
    intro n hn hc
    obtain ⟨x₀, y₀, t₀, hl₀, he₀, hc₀, hC₀⟩ := exists_model_center I hG n hn
    obtain ⟨g, hgx, hgy, hgt⟩ := (eightGroupLines_of I hG).2 x₀ y₀ t₀ x y t hl₀ he₀ hl he
      (hc₀.trans hc.symm)
    exact centerIn_of_conj (isKlein_of_isLineTriple hG.1.1 hl) he ⟨g, hgx, hgy, hgt⟩ hC₀
  rcases twoBCount_cases I hG x y t hl he with hc | hc | hc
  · exact key 1 (Or.inl rfl) hc
  · exact key 3 (Or.inr (Or.inl rfl)) hc
  · exact key 4 (Or.inr (Or.inr rfl)) hc

end Main

end S365

theorem tripleCenter_of
    {G : Type} [Group G] [Finite G] {d₀ : B} {a z₀ : G}
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀) : TripleCenter a := by
  intro x b t hx hb ht ho h hh hcen
  have hl : IsLineTriple a x b := ⟨hx, hb.1, hb.2⟩
  have hK := S365.isKlein_of_isLineTriple hG.1.1 hl
  have htt : t * t = 1 := mul_self_eq_one_of_orderOf ho
  obtain ⟨htx', htb'⟩ := Subgroup.mem_inf.1 ht
  have htx : t * x = x * t := Subgroup.mem_centralizer_singleton_iff.1 htx'
  have htb : t * b = b * t := Subgroup.mem_centralizer_singleton_iff.1 htb'
  by_cases he : IsEightExt x b t
  · exact S365.centerIn_of_isEightExt I hG hl he h hh hcen
  have ht1 : S365.InKlein x b t := by
    by_contra hnot
    exact he ⟨htt, htx, htb, fun h' => hnot (Or.inl h'), fun h' => hnot (Or.inr (Or.inl h')),
      fun h' => hnot (Or.inr (Or.inr (Or.inl h'))), fun h' => hnot (Or.inr (Or.inr (Or.inr h')))⟩
  rw [S365.centralizer_inf_inf_eq_of_inKlein ht1] at hh hcen
  have hex : ∀ n : ℕ, (n = 1 ∨ n = 3) → ∃ s : G, IsEightExt x b s ∧
      twoBCount z₀ x b s = n ∧ h ∈ ({1, x, b, s, x * b, x * s, b * s, x * b * s} : Set G) := by
    intro n hn
    obtain ⟨s, hs, hsn⟩ := eightGroupExists_of I hG x b hl n (by omega)
    have hsmem : s ∈ Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer {b} :=
      Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2 hs.2.1,
        Subgroup.mem_centralizer_singleton_iff.2 hs.2.2.1⟩
    have hhs : h * s = s * h := hcen s hsmem
    refine ⟨s, hs, hsn, S365.centerIn_of_isEightExt I hG hl hs h ?_ ?_⟩
    · exact Subgroup.mem_inf.2 ⟨hh, Subgroup.mem_centralizer_singleton_iff.2 hhs⟩
    · intro g hg
      exact hcen g (Subgroup.mem_inf.1 hg).1
  obtain ⟨s₁, hs₁, hn₁, hh₁⟩ := hex 1 (Or.inl rfl)
  obtain ⟨s₃, hs₃, hn₃, hh₃⟩ := hex 3 (Or.inr rfl)
  have hnot : s₃ ∉ S365.cosetSet x b s₁ := by
    intro hmem
    have := S365.twoBCount_eq_of_mem_cosetSet (z₀ := z₀) hK hmem
    omega
  have hhK := S365.inKlein_of_mem_eightSet_of_notMem_cosetSet hK hs₁ hnot hh₁ hh₃
  exact S365.mem_eightSet_iff.2 ⟨h, hhK, Or.inl rfl⟩

end CFSG.Monster.GMS
