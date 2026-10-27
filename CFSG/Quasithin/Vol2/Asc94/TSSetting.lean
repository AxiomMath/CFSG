module

public import CFSG.Quasithin.Vol2.Asc94.TSModel1
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.Quasithin.A94

open CFSG.CGT.M24S CFSG.Open

variable {G : Type} [Group G]

abbrev Cz (z : G) : Subgroup G := Subgroup.centralizer ({z} : Set G)

structure Setting (G : Type) [Group G] [Finite G] (z : G) (e : ↥(Cz z) ≃* L52.Hc) : Prop where
  ord : orderOf z = 2
  notWC : ∃ g : G, g⁻¹ * z * g ∈ pCoreOf 2 (Cz z) ∧ g⁻¹ * z * g ≠ z

variable {z : G} (e : ↥(Cz z) ≃* L52.Hc)

@[expose] def emb : L52.Hc →* G := (Cz z).subtype.comp e.symm.toMonoidHom

theorem emb_injective : Function.Injective (emb e) :=
  Subtype.val_injective.comp e.symm.injective

@[expose] def tr (X : Subgroup L52.Hc) : Subgroup G := X.map (emb e)

theorem mem_tr {X : Subgroup L52.Hc} {x : G} : x ∈ tr e X ↔ ∃ y ∈ X, emb e y = x := Iff.rfl

theorem emb_mem_tr {X : Subgroup L52.Hc} {y : L52.Hc} (hy : y ∈ X) : emb e y ∈ tr e X :=
  ⟨y, hy, rfl⟩

theorem emb_mem_tr_iff {X : Subgroup L52.Hc} {y : L52.Hc} : emb e y ∈ tr e X ↔ y ∈ X := by
  constructor
  · rintro ⟨y', hy', h⟩
    exact (emb_injective e h) ▸ hy'
  · exact fun hy => emb_mem_tr e hy

theorem card_tr (X : Subgroup L52.Hc) : Nat.card (tr e X) = Nat.card X :=
  Subgroup.card_map_of_injective (emb_injective e)

theorem tr_le_Cz (X : Subgroup L52.Hc) : tr e X ≤ Cz z := by
  rintro _ ⟨y, -, rfl⟩
  exact (e.symm y).2

theorem tr_mono {X Y : Subgroup L52.Hc} (h : X ≤ Y) : tr e X ≤ tr e Y := Subgroup.map_mono h

theorem tr_inf (X Y : Subgroup L52.Hc) : tr e (X ⊓ Y) = tr e X ⊓ tr e Y :=
  Subgroup.map_inf_eq X Y _ (emb_injective e)

theorem tr_sup (X Y : Subgroup L52.Hc) : tr e (X ⊔ Y) = tr e X ⊔ tr e Y := Subgroup.map_sup X Y _

theorem tr_top : tr e (⊤ : Subgroup L52.Hc) = Cz z := by
  apply le_antisymm (tr_le_Cz e ⊤)
  intro x hx
  exact ⟨e ⟨x, hx⟩, trivial, by simp [emb]⟩

theorem tr_bot : tr e (⊥ : Subgroup L52.Hc) = ⊥ := Subgroup.map_bot _

theorem tr_le_iff {X Y : Subgroup L52.Hc} : tr e X ≤ tr e Y ↔ X ≤ Y :=
  Subgroup.map_le_map_iff_of_injective (emb_injective e)

theorem emb_conj (g y : L52.Hc) : emb e (g⁻¹ * y * g) = (emb e g)⁻¹ * emb e y * emb e g := by
  simp [map_mul, map_inv]

theorem emb_mul_comm {y y' : L52.Hc} : emb e y * emb e y' = emb e y' * emb e y ↔ y * y' = y' * y := by
  rw [← map_mul, ← map_mul]
  exact ⟨fun h => emb_injective e h, fun h => congrArg _ h⟩

theorem emb_mem_Cz (y : L52.Hc) : emb e y ∈ Cz z := (e.symm y).2

theorem exists_emb {x : G} (hx : x ∈ Cz z) : ∃ y, emb e y = x :=
  ⟨e ⟨x, hx⟩, by simp [emb]⟩


theorem center_Hc : Subgroup.center L52.Hc = Subgroup.zpowers L52.zt := by
  apply le_antisymm
  · intro x hx
    have h1 : x ∈ L52.U1 := by
      rw [← L52.centralizer_U1]
      exact Subgroup.center_le_centralizer _ hx
    have h2 : x ∈ L52.U2 := by
      rw [← L52.centralizer_U2]
      exact Subgroup.center_le_centralizer _ hx
    rw [← L52.U1_inf_U2]
    exact Subgroup.mem_inf.2 ⟨h1, h2⟩
  · rw [Subgroup.zpowers_le]
    exact L52.zt_central

theorem eq_one_or_zt_of_mem_zpowers {x : L52.Hc} (hx : x ∈ Subgroup.zpowers L52.zt) :
    x = 1 ∨ x = L52.zt := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
  have h2 : orderOf L52.zt = 2 := L52.zt_order
  have h1 : L52.zt ^ (n % (2 : ℤ)) = L52.zt ^ n := by
    have := zpow_mod_orderOf L52.zt n
    rwa [h2] at this
  rw [← h1]
  have : n % (2 : ℤ) = 0 ∨ n % (2 : ℤ) = 1 := by omega
  rcases this with h | h
  · left
    rw [h, zpow_zero]
  · right
    rw [h, zpow_one]

theorem emb_zt (hz : orderOf z = 2) : emb e L52.zt = z := by
  have hz1 : z ≠ 1 := by
    rintro rfl
    simp at hz
  set z' : ↥(Cz z) := ⟨z, by simp [Subgroup.mem_centralizer_iff]⟩ with hz'
  have hc : z' ∈ Subgroup.center ↥(Cz z) := by
    rw [Subgroup.mem_center_iff]
    intro g
    have := Subgroup.mem_centralizer_singleton_iff.1 g.2
    exact Subtype.ext this
  have hcenter : e z' ∈ Subgroup.center L52.Hc := by
    rw [Subgroup.mem_center_iff]
    intro g
    have := Subgroup.mem_center_iff.1 hc (e.symm g)
    have h2 := congrArg e this
    simpa using h2
  rw [center_Hc] at hcenter
  have hne : e z' ≠ 1 := by
    intro h
    have : z' = 1 := e.injective (by simpa using h)
    exact hz1 (congrArg Subtype.val this)
  rcases eq_one_or_zt_of_mem_zpowers hcenter with h | h
  · exact absurd h hne
  · rw [← h]
    simp [emb, hz']

end CFSG.Quasithin.A94
