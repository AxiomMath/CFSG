module

public import CFSG.Quasithin.Background.B6Sections

public section

namespace CFSG.Quasithin.H13.L319

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

variable {G : Type} [Group G] [Finite G]

theorem kerIn_eq_pCoreOf_of_index {H T M₂ C : Subgroup G} (hmp : MinParabolic H T M₂)
    (hCJ : C ≤ kerIn M₂ H) (hC : ∀ q : ℕ, q.Prime → q ∣ C.relIndex H → q = 2 ∨ q = 3)
    (h3 : ¬ 3 ∣ Nat.card (kerIn M₂ H)) : kerIn M₂ H = pCoreOf 2 H := by
  classical
  set J := kerIn M₂ H with hJ
  have hJH : J ≤ H := hmp.kerIn_le_H
  set P : Subgroup ↥H := CFSG.Open.pCore 2 ↥H with hP
  have hOP : pCoreOf 2 H = P.map H.subtype := rfl
  have hOJ : pCoreOf 2 H ≤ J := hmp.pCoreOf_le_kerIn
  refine le_antisymm ?_ hOJ
  set J' : Subgroup ↥H := J.subgroupOf H with hJ'
  have hPJ' : P ≤ J' := by
    intro x hx
    have : (x : G) ∈ pCoreOf 2 H := ⟨x, hx, rfl⟩
    exact hOJ this
  set φ : ↥H →* ↥H ⧸ P := QuotientGroup.mk' P with hφ
  have hfr := MinParabolic.map_kerIn_subgroupOf_eq_frattini hmp
  obtain ⟨Jb, hJb⟩ : ∃ Jb : Subgroup (↥H ⧸ P), Jb = J'.map φ := ⟨_, rfl⟩
  have hJbfr : Jb = frattini (↥H ⧸ P) := hJb.trans hfr
  suffices hbot : Jb = ⊥ by
    intro x hx
    have hxJ' : (⟨x, hJH hx⟩ : ↥H) ∈ J' := hx
    have : (⟨x, hJH hx⟩ : ↥H) ∈ φ.ker := by
      rw [hJb] at hbot
      exact (Subgroup.map_eq_bot_iff _).mp hbot hxJ'
    rw [hφ, QuotientGroup.ker_mk'] at this
    exact ⟨_, this, rfl⟩
  by_contra hne
  haveI : Jb.Normal := by rw [hJbfr]; infer_instance
  have hcardJb : Nat.card Jb = (P.subgroupOf J').index := by
    have e1 : (φ.domRestrict J').range = Jb := by rw [hJb]; exact MonoidHom.domRestrict_range J' φ
    have e2 : (φ.domRestrict J').ker = P.subgroupOf J' := by
      ext x
      simp [hφ, MonoidHom.domRestrict, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    rw [← e1, ← Subgroup.index_ker, e2]
  have hidxJb : Jb.index = J.relIndex H := by
    have hsurj : Function.Surjective φ := QuotientGroup.mk'_surjective P
    have e : Jb.comap φ = J' := by
      rw [hJb, Subgroup.comap_map_eq]
      refine sup_eq_left.mpr ?_
      rw [hφ, QuotientGroup.ker_mk']
      exact hPJ'
    rw [← Subgroup.index_comap_of_surjective Jb hsurj, e]
    rfl
  have hcop : Nat.Coprime (Nat.card Jb) Jb.index := by
    refine Nat.coprime_of_dvd fun q hq hqJb hqidx => ?_
    have hq23 : q = 2 ∨ q = 3 := by
      refine hC q hq ?_
      rw [hidxJb] at hqidx
      exact hqidx.trans (Subgroup.relIndex_dvd_of_le_left H hCJ)
    rcases hq23 with rfl | rfl
    ·
      rw [hcardJb] at hqJb
      apply hmp.isSylowTwoOf_pCoreOf_kerIn.2.2
      have e : (P.subgroupOf J').index = (pCoreOf 2 H).relIndex J := by
        rw [hOP]
        have : J = J'.map H.subtype := (Subgroup.map_subgroupOf_eq_of_le hJH).symm
        conv_rhs => rw [this]
        rw [Subgroup.relIndex_map_map_of_injective (f := H.subtype) P J' H.subtype_injective]
        rfl
      rwa [e] at hqJb
    · apply h3
      have h1 : Nat.card Jb ∣ Nat.card J' := by rw [hJb]; exact Subgroup.card_map_dvd J' φ
      have h2 : Nat.card J' = Nat.card J := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hJH).toEquiv
      exact hqJb.trans (h1.trans (h2 ▸ dvd_refl _))
  obtain ⟨K, hK⟩ := Subgroup.exists_right_complement'_of_coprime hcop
  have hKtop : K ≠ ⊤ := by
    intro h
    apply hne
    have := hK.disjoint
    rw [h, disjoint_top] at this
    exact this
  obtain ⟨M₁, hM₁, hKM₁⟩ := (IsCoatomic.eq_top_or_exists_le_coatom K).resolve_left hKtop
  have hJbM₁ : Jb ≤ M₁ := hJbfr ▸ frattini_le_coatom hM₁
  have : (⊤ : Subgroup (↥H ⧸ P)) ≤ M₁ := hK.sup_eq_top ▸ sup_le hJbM₁ hKM₁
  exact hM₁.1 (top_le_iff.mp this)

end CFSG.Quasithin.H13.L319
