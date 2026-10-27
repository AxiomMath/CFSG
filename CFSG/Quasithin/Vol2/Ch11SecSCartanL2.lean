module

public import CFSG.Quasithin.Vol2.Ch11SecSCartanL

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 SecA

variable {G : Type} [Group G] {T L I V₁ V₂ X : Subgroup G} {n : ℕ}

theorem autOn_bot (V : Subgroup G) : autOn ⊥ V = ⊥ := by
  unfold autOn
  simp

structure TransportData (T L I V₁ V₂ X : Subgroup G) : Prop where
  hXV : X ≤ Subgroup.normalizer (fsuV T I : Set G)
  hXC : X ⊓ Subgroup.centralizer (fsuV T I : Set G) = ⊥
  e₁ : autOn (X ⊓ LOf L V₁) (fsuV T I) =
    autOn X (fsuV T I) ⊓ gammaW (autOn L (fsuV T I)) (V₁.subgroupOf (fsuV T I))
  f₁ : autOn (xOne X (LOf L V₁)) (fsuV T I) =
    centW (autOn X (fsuV T I)) (gammaW (autOn L (fsuV T I)) (V₁.subgroupOf (fsuV T I)))
  e₂ : autOn (X ⊓ LOf L V₂) (fsuV T I) =
    autOn X (fsuV T I) ⊓ gammaW (autOn L (fsuV T I)) (V₂.subgroupOf (fsuV T I))
  f₂ : autOn (xOne X (LOf L V₂)) (fsuV T I) =
    centW (autOn X (fsuV T I)) (gammaW (autOn L (fsuV T I)) (V₂.subgroupOf (fsuV T I)))

theorem transportData [Finite G] (hN : NatFacts) (h1102 : Stmt11_0_2) (h : Hyp11 G T L I n)
    (hV₁ : IsVi T L I n 1 V₁) (hV₂ : IsVi T L I n 2 V₂) (hX : IsCartanX T L X) :
    TransportData T L I V₁ V₂ X := by
  obtain ⟨e₁, f₁⟩ := autOn_cartan_data hN h1102 h (Or.inl rfl) hV₁ hX
  obtain ⟨e₂, f₂⟩ := autOn_cartan_data hN h1102 h (Or.inr rfl) hV₂ hX
  exact ⟨fun x hx => L_le_normalizer_fsuV h (hX.1 hx).1, cartan_inf_centralizer h1102 h hX,
    e₁, f₁, e₂, f₂⟩

namespace TransportData

variable (d : TransportData T L I V₁ V₂ X)
include d

theorem card {Y : Subgroup G} (hY : Y ≤ X) : Nat.card ↥(autOn Y (fsuV T I)) = Nat.card ↥Y :=
  card_autOn_eq d.hXV d.hXC hY

theorem le {Y Z : Subgroup G} (hY : Y ≤ X) (hZ : Z ≤ X)
    (h : autOn Y (fsuV T I) ≤ autOn Z (fsuV T I)) : Y ≤ Z :=
  le_of_autOn_le d.hXV d.hXC hY hZ h

theorem eq {Y Z : Subgroup G} (hY : Y ≤ X) (hZ : Z ≤ X)
    (h : autOn Y (fsuV T I) = autOn Z (fsuV T I)) : Y = Z :=
  le_antisymm (d.le hY hZ h.le) (d.le hZ hY h.ge)

theorem le_sup {Y Z : Subgroup G} (hY : Y ≤ X) (hZ : Z ≤ X)
    (h : autOn X (fsuV T I) ≤ autOn Y (fsuV T I) ⊔ autOn Z (fsuV T I)) : X ≤ Y ⊔ Z := by
  refine d.le le_rfl (sup_le hY hZ) ?_
  rwa [autOn_sup (hY.trans d.hXV) (hZ.trans d.hXV)]

end TransportData

theorem cartanL_of_concl (d : TransportData T L I V₁ V₂ X)
    (hc : CartanConcl (autOn L (fsuV T I)) (V₁.subgroupOf (fsuV T I))
      (V₂.subgroupOf (fsuV T I)) (autOn X (fsuV T I)) (2 ^ 2)) : CartanL L V₁ V₂ X := by
  obtain ⟨ha, hb, hcc, h1, h2, h3, h4⟩ := hc
  have hx1 : xOne X (LOf L V₁) ≤ X := inf_le_left
  have hx2 : xOne X (LOf L V₂) ≤ X := inf_le_left
  refine ⟨d.le_sup hx1 inf_le_left ?_, d.le_sup inf_le_left inf_le_left ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [d.f₁, d.e₁]
    exact ha
  · rw [d.e₁, d.e₂]
    exact hb
  · set Y := X ⊓ LOf L V₁ ⊓ sectionCentralizer (LOf L V₂) (pCoreOf 2 (LOf L V₂))
    have hYX : Y ≤ X := inf_le_left.trans inf_le_left
    have h1' : autOn Y (fsuV T I) ≤ autOn (X ⊓ LOf L V₁) (fsuV T I) := autOn_mono inf_le_left
    have h2' : autOn Y (fsuV T I) ≤ autOn (xOne X (LOf L V₂)) (fsuV T I) :=
      autOn_mono (le_inf hYX inf_le_right)
    rw [d.e₁] at h1'
    rw [d.f₂] at h2'
    have h3' : autOn Y (fsuV T I) ≤ autOn ⊥ (fsuV T I) := by
      rw [autOn_bot, ← hcc]
      exact le_inf h1' (h2'.trans inf_le_right)
    exact le_bot_iff.mp (d.le hYX bot_le h3')
  · rw [← d.card inf_le_left, d.e₁, h1]; rfl
  · rw [← d.card hx1, d.f₁, h2]; rfl
  · rw [← d.card inf_le_left, d.e₂, h3]; rfl
  · rw [← d.card hx2, d.f₂, h4]; rfl

theorem cartanSp4_of_fourDiag (d : TransportData T L I V₁ V₂ X)
    (hc : FourDiag (autOn L (fsuV T I)) (V₁.subgroupOf (fsuV T I))
      (V₂.subgroupOf (fsuV T I)) (autOn X (fsuV T I))) : CartanSp4 L V₁ V₂ X := by
  obtain ⟨n1, n2, n3, n4, n5, n6, hall⟩ := hc
  have hx1 : xOne X (LOf L V₁) ≤ X := inf_le_left
  have hx2 : xOne X (LOf L V₂) ≤ X := inf_le_left
  have hi1 : X ⊓ LOf L V₁ ≤ X := inf_le_left
  have hi2 : X ⊓ LOf L V₂ ≤ X := inf_le_left
  refine ⟨fun e => n1 ?_, fun e => n2 ?_, fun e => n3 ?_, fun e => n4 ?_, fun e => n5 ?_,
    fun e => n6 ?_, fun E hE hE3 => ?_⟩
  · rw [← d.e₁, ← d.f₁, e]
  · rw [← d.e₁, ← d.e₂, e]
  · rw [← d.e₁, ← d.f₂, e]
  · rw [← d.f₁, ← d.e₂, e]
  · rw [← d.f₁, ← d.f₂, e]
  · rw [← d.e₂, ← d.f₂, e]
  · have hE' : autOn E (fsuV T I) ≤ autOn X (fsuV T I) := autOn_mono hE
    rcases hall _ hE' (by rw [d.card hE, hE3]) with h | h | h | h
    · exact Or.inl (d.eq hE hi1 (h.trans d.e₁.symm))
    · exact Or.inr (Or.inl (d.eq hE hx1 (h.trans d.f₁.symm)))
    · exact Or.inr (Or.inr (Or.inl (d.eq hE hi2 (h.trans d.e₂.symm))))
    · exact Or.inr (Or.inr (Or.inr (d.eq hE hx2 (h.trans d.f₂.symm))))

theorem cartanG2_of_le (d : TransportData T L I V₁ V₂ X)
    (hc : centW (autOn X (fsuV T I)) (gammaW (autOn L (fsuV T I)) (V₁.subgroupOf (fsuV T I))) ≤
      gammaW (autOn L (fsuV T I)) (V₂.subgroupOf (fsuV T I))) : CartanG2 L V₁ V₂ X := by
  have hx1 : xOne X (LOf L V₁) ≤ X := inf_le_left
  have hle : autOn (xOne X (LOf L V₁)) (fsuV T I) ≤ autOn (X ⊓ LOf L V₂) (fsuV T I) := by
    rw [d.f₁, d.e₂]
    exact le_inf inf_le_left hc
  exact (d.le hx1 inf_le_left hle).trans inf_le_right

end CFSG.Quasithin.Vol2.Ch11.SecS
