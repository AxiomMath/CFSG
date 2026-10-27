module

public import CFSG.Quasithin.Vol2.Ch11SecOE7N

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE3.Lie3

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique.Setup.X6

variable {G : Type} [Group G] [Finite G]

theorem eq_top_of_not_isSolvable_of_isDiagramNontrivial {L T : Subgroup G} [hLn : L.Normal]
    (hT : IsSylowIn 2 T ⊤) (hLT : L ⊔ T = ⊤) {P : Fin 2 → Subgroup ↥L}
    (hres : ResidualOvergroupsAt ↥L ((T ⊓ L).subgroupOf L) P)
    (hnorm : ∀ j, Subgroup.normalizer
      (((T ⊓ L).subgroupOf L : Subgroup ↥L) : Set ↥L) ≤ P j)
    (htw : E2.IsDiagramNontrivial T L (T ⊓ L)) {H : Subgroup G} (hTH : T ≤ H)
    (hs : ¬ Group.IsSolvable ↥(H ⊓ L)) : H = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hne, hUP, hmax, -, hunique, -⟩ := hres
  set U := (T ⊓ L).subgroupOf L with hUdef
  set M := (H ⊓ L).subgroupOf L with hMdef
  have hUM : U ≤ M := fun x hx => by
    rw [hUdef, Subgroup.mem_subgroupOf] at hx
    rw [hMdef, Subgroup.mem_subgroupOf]
    exact ⟨hTH hx.1, hx.2⟩
  have hMs : ¬ Group.IsSolvable ↥M := fun hM => hs
    (Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe (inf_le_right : H ⊓ L ≤ L)).symm.toMonoidHom)
      (MulEquiv.injective _))
  by_cases hMtop : M = ⊤
  · have hLH : L ≤ H := fun x hx => by
      have : (⟨x, hx⟩ : ↥L) ∈ M := hMtop ▸ Subgroup.mem_top _
      exact (Subgroup.mem_subgroupOf.mp this).1
    exact eq_top_iff.mpr (hLT.symm.le.trans (sup_le hLH hTH))
  obtain ⟨j, hj, -⟩ := hunique M hUM hMtop hMs
  have hMj : M ≤ P j := (hj j).mpr rfl
  have hTL : QuasithinUnique.IsSylowTwoOf (T ⊓ L) L :=
    B6.isSylowTwoOf_inf_normal (⟨hT.1, hT.2.1, hT.2.2⟩ : QuasithinUnique.IsSylowTwoOf T ⊤) le_top
      (by rw [Subgroup.normalizer_eq_top_iff.mpr hLn])
  have hcoat : ∀ k, IsCoatom (P k) := fun k => ((hmax (P k) (hUP k)).mpr ⟨k, rfl⟩).isCoatom
  have hBP : ∀ k, L ⊓ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) ≤
      (P k).map L.subtype := by
    intro k x hx
    obtain ⟨hxL, hxN⟩ := Subgroup.mem_inf.mp hx
    refine ⟨⟨x, hxL⟩, hnorm k ?_, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro y
    rw [hUdef, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact Subgroup.mem_normalizer_iff.mp hxN y
  have hmaxpar : ∀ k, IsMaxParabolic2 L ((P k).map L.subtype) := by
    intro k
    have hPne : (P k).map L.subtype ≠ L := by
      intro h
      apply (hcoat k).1
      rw [eq_top_iff]
      intro x _
      have : (x : G) ∈ (P k).map L.subtype := by rw [h]; exact x.2
      obtain ⟨y, hy, hyx⟩ := this
      rwa [show y = x from Subtype.ext hyx] at hy
    refine ⟨⟨Subgroup.map_subtype_le _, T ⊓ L, hTL, hBP k⟩, hPne, fun Q hQp hQne hle => ?_⟩
    have hQL : Q ≤ L := hQp.1
    have hQ : Q.subgroupOf L ≠ ⊤ := by
      intro h
      apply hQne
      refine le_antisymm hQL fun x hx => ?_
      have : (⟨x, hx⟩ : ↥L) ∈ Q.subgroupOf L := h ▸ Subgroup.mem_top _
      exact this
    have hPQ : P k ≤ Q.subgroupOf L := fun x hx => by
      rw [Subgroup.mem_subgroupOf]
      exact hle ⟨x, hx, rfl⟩
    have heq := ((hcoat k).le_iff.mp hPQ).resolve_left hQ
    rw [← heq, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hQL]
  obtain ⟨t, htT, htN⟩ : ∃ t ∈ T, t ∉ Subgroup.normalizer
      (((P j).map L.subtype : Subgroup G) : Set G) := by
    by_contra h
    push Not at h
    exact htw _ (hmaxpar j) (hBP j) fun t ht => h t ht
  set φ : MulAut ↥L := MulAut.conjNormal t with hφ
  have hφinv : ∀ X : Subgroup G, T ≤ X → ∀ m ∈ (X ⊓ L).subgroupOf L,
      φ m ∈ (X ⊓ L).subgroupOf L := by
    intro X hTX m hm
    have hm' : (m : G) ∈ X ⊓ L := Subgroup.mem_subgroupOf.mp hm
    rw [Subgroup.mem_subgroupOf]
    show ((φ m : ↥L) : G) ∈ X ⊓ L
    rw [hφ, MulAut.conjNormal_apply]
    exact ⟨X.mul_mem (X.mul_mem (hTX htT) hm'.1) (X.inv_mem (hTX htT)), hLn.conj_mem _ hm'.2 t⟩
  have hφmap : ∀ X : Subgroup G, T ≤ X →
      ((X ⊓ L).subgroupOf L).map φ.toMonoidHom = (X ⊓ L).subgroupOf L := fun X hTX =>
    Subgroup.eq_of_le_of_card_ge (by rintro _ ⟨m, hm, rfl⟩; exact hφinv X hTX m hm)
      (Subgroup.card_map_of_injective (f := φ.toMonoidHom) φ.injective).ge
  have hφU : U.map φ.toMonoidHom = U := hφmap T le_rfl
  have hφM : M.map φ.toMonoidHom = M := hφmap H hTH
  obtain ⟨k, hk⟩ : ∃ k, (P j).map φ.toMonoidHom = P k := by
    have hc : (P j).map φ.toMonoidHom ⋖ ⊤ := by
      have h1 := (hmax (P j) (hUP j)).mpr ⟨j, rfl⟩
      have h2 := (apply_covBy_apply_iff (MulEquiv.mapSubgroup φ)).mpr h1
      simpa [MulEquiv.mapSubgroup_apply, Subgroup.map_top_of_surjective _ φ.surjective] using h2
    refine (hmax _ ?_).mp hc
    rw [← hφU]
    exact Subgroup.map_mono (hUP j)
  have hkj : k ≠ j := by
    rintro rfl
    apply htN
    rw [← A1b.conjSub_eq_iff_mem_normalizer, conjSub_map_subtype, hk]
  have hMk : M ≤ P k := by
    rw [← hφM, ← hk]
    exact Subgroup.map_mono hMj
  exact absurd ((hj k).mp hMk) hkj

end CFSG.Quasithin.Vol2.Ch11.SecE3.Lie3
