module

public import CFSG.Quasithin.Background.F3Coset
public import CFSG.Quasithin.Background.F3Lemma35
public import CFSG.Quasithin.Background.F3Lemma36
public import CFSG.Quasithin.Background.F3Lemma37

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Quasithin.F7

universe u

namespace CosetGeom

variable {G : Type u} [Group G] {G₁ G₂ : Subgroup G}

@[expose] noncomputable def Qy {G₀ : Subgroup G} (y : CosetGeom G₀ G₁ G₂) : Subgroup G :=
  pCoreOf 2 (stab y)

theorem exists_nbr_ne (h0 : 2 < (nbrs (γ₀ (G₁ ⊔ G₂) G₁ G₂)).encard)
    (h1 : 2 < (nbrs (γ₁ (G₁ ⊔ G₂) G₁ G₂)).encard) (v a b : CosetGeom (G₁ ⊔ G₂) G₁ G₂) :
    ∃ w, (graph (G₁ ⊔ G₂) G₁ G₂).Adj v w ∧ w ≠ a ∧ w ≠ b := by
  have key : ∀ (v₀ : CosetGeom (G₁ ⊔ G₂) G₁ G₂), 2 < (nbrs v₀).encard →
      ∀ (g : ↥(G₁ ⊔ G₂)) (a b : CosetGeom (G₁ ⊔ G₂) G₁ G₂),
      ∃ w, (graph (G₁ ⊔ G₂) G₁ G₂).Adj (g • v₀) w ∧ w ≠ a ∧ w ≠ b := by
    intro v₀ hv₀ g a b
    by_contra hcon
    have hsub : nbrs v₀ ⊆ {g⁻¹ • a, g⁻¹ • b} := by
      intro w' hw'
      have hadj : (graph (G₁ ⊔ G₂) G₁ G₂).Adj (g • v₀) (g • w') := (smul_adj g).mpr hw'
      by_contra hn
      apply hcon
      refine ⟨g • w', hadj, ?_, ?_⟩
      · intro h
        apply hn
        left
        rw [← h, inv_smul_smul]
      · intro h
        apply hn
        right
        rw [Set.mem_singleton_iff, ← h, inv_smul_smul]
    have h2 : ({g⁻¹ • a, g⁻¹ • b} : Set (CosetGeom (G₁ ⊔ G₂) G₁ G₂)).encard ≤ 2 := by
      calc ({g⁻¹ • a, g⁻¹ • b} : Set (CosetGeom (G₁ ⊔ G₂) G₁ G₂)).encard
          ≤ ({g⁻¹ • b} : Set (CosetGeom (G₁ ⊔ G₂) G₁ G₂)).encard + 1 := Set.encard_insert_le _ _
        _ = 2 := by rw [Set.encard_singleton]; rfl
    exact absurd (lt_of_lt_of_le hv₀ ((Set.encard_le_encard hsub).trans h2)) (lt_irrefl _)
  cases hv : vtype v with
  | false =>
    obtain ⟨g, rfl⟩ := exists_smul_eq_γ₀ hv
    exact key _ h0 g a b
  | true =>
    obtain ⟨g, rfl⟩ := exists_smul_eq_γ₁ hv
    exact key _ h1 g a b

theorem lemma_F35 (h0 : 2 < (nbrs (γ₀ (G₁ ⊔ G₂) G₁ G₂)).encard)
    (h1 : 2 < (nbrs (γ₁ (G₁ ⊔ G₂) G₁ G₂)).encard) {u : CosetGeom (G₁ ⊔ G₂) G₁ G₂} {m : ℕ}
    (hm : 1 ≤ m)
    (htrans : ∀ q q' : GPath (graph (G₁ ⊔ G₂) G₁ G₂) (m + 1),
      q ∈ GPath.nbPaths (graph (G₁ ⊔ G₂) G₁ G₂) u (m + 1) →
      q' ∈ GPath.nbPaths (graph (G₁ ⊔ G₂) G₁ G₂) u (m + 1) →
      ∃ g : ↥(G₁ ⊔ G₂), g • u = u ∧ g • q = q')
    {p : GPath (graph (G₁ ⊔ G₂) G₁ G₂) (m + 1)}
    (hp : p ∈ GPath.nbPaths (graph (G₁ ⊔ G₂) G₁ G₂) u (m + 1)) :
    GPath.F35Conclusion (graph (G₁ ⊔ G₂) G₁ G₂) ↥(G₁ ⊔ G₂) u m p :=
  GPath.lemma_F35 (exists_nbr_ne h0 h1) htrans (connected rfl)
    (fun _ _ h => vtype_ne_of_adj h) hm hp

theorem lemma_F36 {m : ℕ} (hm : 1 < m) (hU : UniqueGeod (graph (G₁ ⊔ G₂) G₁ G₂) m)
    {s t : ↥(G₁ ⊔ G₂)} (hs : s * s = 1) (ht : t * t = 1) (hs1 : (s : G) ∈ G₁)
    (hs12 : (s : G) ∉ G₁ ⊓ G₂) (ht2 : (t : G) ∈ G₂) (ht12 : (t : G) ∉ G₁ ⊓ G₂) {n : ℕ} (hn : 0 < n)
    (hnm : n ≤ m) (hst : (((s * t) ^ n : ↥(G₁ ⊔ G₂)) : G) ∈ G₁ ⊓ G₂) :
    n = m ∧
      IsPolygon (graph (G₁ ⊔ G₂) G₁ G₂)
        (MulAction.orbit (Subgroup.closure {s, t}) (γ₀ (G₁ ⊔ G₂) G₁ G₂) ∪
          MulAction.orbit (Subgroup.closure {s, t}) (γ₁ (G₁ ⊔ G₂) G₁ G₂)) (2 * m) ∧
      (∀ w ∈ Subgroup.closure {s, t},
        (∀ v ∈ MulAction.orbit (Subgroup.closure {s, t}) (γ₀ (G₁ ⊔ G₂) G₁ G₂) ∪
          MulAction.orbit (Subgroup.closure {s, t}) (γ₁ (G₁ ⊔ G₂) G₁ G₂), w • v = v) ↔
          w ∈ Subgroup.zpowers ((s * t) ^ m)) ∧
      (Subgroup.zpowers ((s * t) ^ m)).relIndex (Subgroup.closure {s, t}) = 2 * m := by
  have hG1 : G₁ ≤ G₁ ⊔ G₂ := le_sup_left
  have hG2 : G₂ ≤ G₁ ⊔ G₂ := le_sup_right
  have hs2 : (s : G) ∉ G₂ := fun h => hs12 ⟨hs1, h⟩
  have ht1 : (t : G) ∉ G₁ := fun h => ht12 ⟨h, ht2⟩
  have hsx : s • γ₀ (G₁ ⊔ G₂) G₁ G₂ = γ₀ (G₁ ⊔ G₂) G₁ G₂ :=
    smul_eq_of_mem_stab (by rw [stab_γ₀ hG1]; exact hs1)
  have htl : t • γ₁ (G₁ ⊔ G₂) G₁ G₂ = γ₁ (G₁ ⊔ G₂) G₁ G₂ :=
    smul_eq_of_mem_stab (by rw [stab_γ₁ hG2]; exact ht2)
  have hsl : s • γ₁ (G₁ ⊔ G₂) G₁ G₂ ≠ γ₁ (G₁ ⊔ G₂) G₁ G₂ := fun h => by
    have := mem_stab_of_smul_eq h
    rw [stab_γ₁ hG2] at this
    exact hs2 this
  have htx : t • γ₀ (G₁ ⊔ G₂) G₁ G₂ ≠ γ₀ (G₁ ⊔ G₂) G₁ G₂ := fun h => by
    have := mem_stab_of_smul_eq h
    rw [stab_γ₀ hG1] at this
    exact ht1 this
  have hx : (s * t) ^ n • γ₀ (G₁ ⊔ G₂) G₁ G₂ = γ₀ (G₁ ⊔ G₂) G₁ G₂ :=
    smul_eq_of_mem_stab (by rw [stab_γ₀ hG1]; exact hst.1)
  have hl : (s * t) ^ n • γ₁ (G₁ ⊔ G₂) G₁ G₂ = γ₁ (G₁ ⊔ G₂) G₁ G₂ :=
    smul_eq_of_mem_stab (by rw [stab_γ₁ hG2]; exact hst.2)
  exact Lemma36.lemma_F36 hs ht adj_γ₀_γ₁ hsx htl hsl htx (connected rfl)
    (fun _ _ h => vtype_ne_of_adj h) hm hU hn hnm hx hl

theorem lemma_F37 {m : ℕ} (hm4 : 4 ≤ m) (hmeven : Even m)
    (hU : UniqueGeod (graph (G₁ ⊔ G₂) G₁ G₂) m) {c : CosetGeom (G₁ ⊔ G₂) G₁ G₂}
    (hxc : (graph (G₁ ⊔ G₂) G₁ G₂).Adj (γ₀ (G₁ ⊔ G₂) G₁ G₂) c) (hlc : c ≠ γ₁ (G₁ ⊔ G₂) G₁ G₂)
    {s t : ↥(G₁ ⊔ G₂)} (hs : s * s = 1) (ht : t * t = 1) (hsc : (s : G) ∈ stab c)
    (hsxc : (s : G) ∉ G₁ ⊓ stab c) (ht2 : (t : G) ∈ G₂) (ht12 : (t : G) ∉ G₁ ⊓ G₂) {n : ℕ}
    (hn : 0 < n) (hnm : n ≤ m / 2) (hst : (((s * t) ^ n : ↥(G₁ ⊔ G₂)) : G) ∈ G₁ ⊓ G₂ ⊓ stab c) :
    n = m / 2 ∧
      IsPolygon (graph (G₁ ⊔ G₂) G₁ G₂)
        (MulAction.orbit (Subgroup.closure {s, t}) (γ₀ (G₁ ⊔ G₂) G₁ G₂) ∪
          MulAction.orbit (Subgroup.closure {s, t}) (γ₁ (G₁ ⊔ G₂) G₁ G₂) ∪
          MulAction.orbit (Subgroup.closure {s, t}) c) (2 * m) ∧
      (∀ w ∈ Subgroup.closure {s, t},
        (∀ v ∈ MulAction.orbit (Subgroup.closure {s, t}) (γ₀ (G₁ ⊔ G₂) G₁ G₂) ∪
          MulAction.orbit (Subgroup.closure {s, t}) (γ₁ (G₁ ⊔ G₂) G₁ G₂) ∪
          MulAction.orbit (Subgroup.closure {s, t}) c, w • v = v) ↔
          w ∈ Subgroup.zpowers ((s * t) ^ n)) ∧
      (Subgroup.zpowers ((s * t) ^ n)).relIndex (Subgroup.closure {s, t}) = 2 * n := by
  have hG1 : G₁ ≤ G₁ ⊔ G₂ := le_sup_left
  have hG2 : G₂ ≤ G₁ ⊔ G₂ := le_sup_right
  have hsx : (s : G) ∉ G₁ := fun h => hsxc ⟨h, hsc⟩
  have ht1 : (t : G) ∉ G₁ := fun h => ht12 ⟨h, ht2⟩
  have hsc' : s • c = c := smul_eq_of_mem_stab hsc
  have htl : t • γ₁ (G₁ ⊔ G₂) G₁ G₂ = γ₁ (G₁ ⊔ G₂) G₁ G₂ :=
    smul_eq_of_mem_stab (by rw [stab_γ₁ hG2]; exact ht2)
  have hsx' : s • γ₀ (G₁ ⊔ G₂) G₁ G₂ ≠ γ₀ (G₁ ⊔ G₂) G₁ G₂ := fun h => by
    have := mem_stab_of_smul_eq h
    rw [stab_γ₀ hG1] at this
    exact hsx this
  have htx : t • γ₀ (G₁ ⊔ G₂) G₁ G₂ ≠ γ₀ (G₁ ⊔ G₂) G₁ G₂ := fun h => by
    have := mem_stab_of_smul_eq h
    rw [stab_γ₀ hG1] at this
    exact ht1 this
  have hx : (s * t) ^ n • γ₀ (G₁ ⊔ G₂) G₁ G₂ = γ₀ (G₁ ⊔ G₂) G₁ G₂ :=
    smul_eq_of_mem_stab (by rw [stab_γ₀ hG1]; exact hst.1.1)
  have hl : (s * t) ^ n • γ₁ (G₁ ⊔ G₂) G₁ G₂ = γ₁ (G₁ ⊔ G₂) G₁ G₂ :=
    smul_eq_of_mem_stab (by rw [stab_γ₁ hG2]; exact hst.1.2)
  have hcc : (s * t) ^ n • c = c := smul_eq_of_mem_stab hst.2
  exact Lemma37.lemma_F37 hs ht adj_γ₀_γ₁ hxc hlc.symm hsc' htl hsx' htx (connected rfl)
    (fun _ _ h => vtype_ne_of_adj h) hm4 hmeven hU hn hnm hx hl hcc

end CosetGeom

end CFSG.Quasithin
