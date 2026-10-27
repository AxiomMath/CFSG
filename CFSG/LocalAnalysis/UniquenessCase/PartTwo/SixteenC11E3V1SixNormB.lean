module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11E3V1SixNormA
public import CFSG.LargeExtraspecial.S12TriG2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Quasithin.G6 Equiv

private theorem s1611e3_sixSwap_inv : sixSwap⁻¹ = sixSwap :=
  inv_eq_of_mul_eq_one_right sixSwap_mul_self

private theorem s1611e3_swap_conj_rho_swap (σ : Perm (Fin 6)) :
    sixSwap * sixRho σ * sixSwap = sixRho (sixAlpha σ) := by
  simpa [s1611e3_sixSwap_inv] using sixSwap_conj_rho σ

private theorem s1611e3_mem_closure_pair_union {G : Type*} [Group G] (H : Subgroup G) {y : G}
    (hy : y * y = 1) (hH : ∀ h ∈ H, y * h * y ∈ H) {g : G}
    (hg : g ∈ Subgroup.closure ((H : Set G) ∪ {y})) :
    g ∈ H ∨ ∃ h ∈ H, g = y * h := by
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy
  have hmid : ∀ a : G, y * (y * a * y) = a * y := by
    intro a
    rw [show y * (y * a * y) = (y * y) * (a * y) by group, hy, one_mul]
  let S : Subgroup G :=
    { carrier := (H : Set G) ∪ {x | ∃ h ∈ H, x = y * h}
      one_mem' := Or.inl H.one_mem
      mul_mem' := by
        rintro a b (ha | ⟨a', ha', rfl⟩) (hb | ⟨b', hb', rfl⟩)
        · exact Or.inl (H.mul_mem ha hb)
        · refine Or.inr ⟨(y * a * y) * b', H.mul_mem (hH a ha) hb', ?_⟩
          rw [show a * (y * b') = (a * y) * b' by group, ← hmid a]
          group
        · exact Or.inr ⟨a' * b, H.mul_mem ha' hb, by group⟩
        · exact Or.inl (by
            rw [show (y * a') * (y * b') = (y * a' * y) * b' by group]
            exact H.mul_mem (hH a' ha') hb')
      inv_mem' := by
        rintro a (ha | ⟨a', ha', rfl⟩)
        · exact Or.inl (H.inv_mem ha)
        · refine Or.inr ⟨y * a'⁻¹ * y, hH a'⁻¹ (H.inv_mem ha'), ?_⟩
          rw [show (y * a')⁻¹ = a'⁻¹ * y by rw [mul_inv_rev, hyinv], ← hmid a'⁻¹] }
  have hle : Subgroup.closure ((H : Set G) ∪ {y}) ≤ S := by
    rw [Subgroup.closure_le]
    rintro z (hz | hz)
    · exact Or.inl hz
    · exact Or.inr ⟨1, H.one_mem, by rw [Set.mem_singleton_iff.mp hz, mul_one]⟩
  exact hle hg

private theorem s1611e3_mem_sixGhat {g : MulAut (SixE6 × SixE6)} (hg : g ∈ sixGhat) :
    (∃ σ : Perm (Fin 6), sixRho σ = g) ∨
      ∃ σ : Perm (Fin 6), sixSwap * sixRho σ = g := by
  have hghat : sixGhat =
      Subgroup.closure ((sixRho.range : Set (MulAut (SixE6 × SixE6))) ∪ {sixSwap}) := by
    rw [sixGhat, ← MonoidHom.coe_range]
  rw [hghat] at hg
  rcases s1611e3_mem_closure_pair_union sixRho.range sixSwap_mul_self
      (fun h hh => by
        obtain ⟨σ, rfl⟩ := MonoidHom.mem_range.mp hh
        exact ⟨sixAlpha σ, (s1611e3_swap_conj_rho_swap σ).symm⟩) hg with hg | ⟨h, hh, rfl⟩
  · obtain ⟨σ, rfl⟩ := MonoidHom.mem_range.mp hg
    exact Or.inl ⟨σ, rfl⟩
  · obtain ⟨σ, rfl⟩ := MonoidHom.mem_range.mp hh
    exact Or.inr ⟨σ, rfl⟩

private theorem s1611e3_sixRho_mem (σ : Perm (Fin 6)) : sixRho σ ∈ sixGhat :=
  Subgroup.subset_closure (Or.inl ⟨σ, rfl⟩)

private theorem s1611e3_sixSwap_mem : sixSwap ∈ sixGhat :=
  Subgroup.subset_closure (Or.inr rfl)

private def s1611e3_ghatMap : Perm (Fin 6) ⊕ Perm (Fin 6) → ↥sixGhat
  | Sum.inl σ => ⟨sixRho σ, s1611e3_sixRho_mem σ⟩
  | Sum.inr σ => ⟨sixSwap * sixRho σ, sixGhat.mul_mem s1611e3_sixSwap_mem
      (s1611e3_sixRho_mem σ)⟩

private theorem s1611e3_sixZ_ne_one : sixZ ≠ (1 : SixE6) := by
  intro h
  have h1 : (allOnes 6 : PermMod 6) = 1 := by simpa [sixZ] using congrArg Subtype.val h
  have h2 := congrFun (congrArg Multiplicative.toAdd h1) 0
  have h3 : (1 : ZMod 2) = 0 := by simpa [allOnes] using h2
  exact one_ne_zero h3

private theorem s1611e3_sixRho_ne_sixSwap (σ : Perm (Fin 6)) : sixRho σ ≠ sixSwap := by
  intro h
  have h2 := congrArg (fun f : MulAut (SixE6 × SixE6) => (f (sixZ, (1 : SixE6))).2) h
  simp [sixRho, sixSwap] at h2
  exact s1611e3_sixZ_ne_one h2.symm

private theorem s1611e3_ghatMap_injective : Function.Injective s1611e3_ghatMap := by
  intro x y h
  cases x with
  | inl σ =>
    cases y with
    | inl τ =>
      have h' : sixRho σ = sixRho τ := Subtype.ext_iff.mp h
      rw [sixRho_injective h']
    | inr τ =>
      exfalso
      have h' : sixRho σ = sixSwap * sixRho τ := Subtype.ext_iff.mp h
      refine s1611e3_sixRho_ne_sixSwap (σ * τ⁻¹) ?_
      rw [map_mul, map_inv, h']
      group
  | inr σ =>
    cases y with
    | inl τ =>
      exfalso
      have h' : sixSwap * sixRho σ = sixRho τ := Subtype.ext_iff.mp h
      refine s1611e3_sixRho_ne_sixSwap (τ * σ⁻¹) ?_
      rw [map_mul, map_inv, ← h']
      group
    | inr τ =>
      have h' : sixSwap * sixRho σ = sixSwap * sixRho τ := Subtype.ext_iff.mp h
      have h2 : sixRho σ = sixRho τ := mul_left_cancel h'
      rw [sixRho_injective h2]

private theorem s1611e3_ghatMap_surjective : Function.Surjective s1611e3_ghatMap := by
  intro g
  rcases s1611e3_mem_sixGhat g.2 with ⟨σ, hσ⟩ | ⟨σ, hσ⟩
  · exact ⟨Sum.inl σ, Subtype.ext hσ⟩
  · exact ⟨Sum.inr σ, Subtype.ext hσ⟩

theorem sixGhat_card : Nat.card ↥sixGhat = 1440 := by
  have hPerm : Nat.card (Perm (Fin 6)) = 720 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    norm_num
  have hbij : Function.Bijective s1611e3_ghatMap :=
    ⟨s1611e3_ghatMap_injective, s1611e3_ghatMap_surjective⟩
  calc Nat.card ↥sixGhat = Nat.card (Perm (Fin 6) ⊕ Perm (Fin 6)) :=
        (Nat.card_congr (Equiv.ofBijective s1611e3_ghatMap hbij)).symm
    _ = Nat.card (Perm (Fin 6)) + Nat.card (Perm (Fin 6)) := Nat.card_sum
    _ = 1440 := by rw [hPerm]

private def s1611e3_conjGhat (g : ↥sixGhat) : MulAut ↥sixLhat where
  toFun l :=
    ⟨(g : MulAut (SixE6 × SixE6)) * (l : MulAut (SixE6 × SixE6)) *
        (g : MulAut (SixE6 × SixE6))⁻¹,
      sixGhat_normalizes (g : MulAut (SixE6 × SixE6)) g.2 (l : MulAut (SixE6 × SixE6)) l.2⟩
  invFun l :=
    ⟨(g : MulAut (SixE6 × SixE6))⁻¹ * (l : MulAut (SixE6 × SixE6)) *
        (g : MulAut (SixE6 × SixE6)),
      sixGhat_normalizes (g : MulAut (SixE6 × SixE6))⁻¹ (sixGhat.inv_mem g.2)
        (l : MulAut (SixE6 × SixE6)) l.2⟩
  left_inv l := Subtype.ext (by group)
  right_inv l := Subtype.ext (by group)
  map_mul' l m := Subtype.ext (by simp only [Subtype.coe_mk, Subgroup.coe_mul]; group)

private def s1611e3_conjHom : ↥sixGhat →* MulAut ↥sixLhat where
  toFun := s1611e3_conjGhat
  map_one' := by
    apply MulEquiv.ext
    intro l
    apply Subtype.ext
    simp [s1611e3_conjGhat]
  map_mul' := by
    intro a b
    apply MulEquiv.ext
    intro l
    apply Subtype.ext
    change (a : MulAut (SixE6 × SixE6)) * (b : MulAut (SixE6 × SixE6)) *
        (l : MulAut (SixE6 × SixE6)) *
        ((a : MulAut (SixE6 × SixE6)) * (b : MulAut (SixE6 × SixE6)))⁻¹ =
      (a : MulAut (SixE6 × SixE6)) *
        ((b : MulAut (SixE6 × SixE6)) * (l : MulAut (SixE6 × SixE6)) *
          (b : MulAut (SixE6 × SixE6))⁻¹) * (a : MulAut (SixE6 × SixE6))⁻¹
    group

private theorem s1611e3_conjHom_injective : Function.Injective s1611e3_conjHom := by
  rw [injective_iff_map_eq_one]
  intro g hg
  apply Subtype.ext
  apply sixGhat_cent_eq_one (g : MulAut (SixE6 × SixE6)) g.2
  intro l hl
  have h2 : (g : MulAut (SixE6 × SixE6)) * l * (g : MulAut (SixE6 × SixE6))⁻¹ = l := by
    have := congrArg Subtype.val (congrArg (fun f : MulAut ↥sixLhat => f ⟨l, hl⟩) hg)
    simpa [s1611e3_conjHom, s1611e3_conjGhat] using this
  calc (g : MulAut (SixE6 × SixE6)) * l
      = ((g : MulAut (SixE6 × SixE6)) * l * (g : MulAut (SixE6 × SixE6))⁻¹) *
          (g : MulAut (SixE6 × SixE6)) := by group
    _ = l * (g : MulAut (SixE6 × SixE6)) := by rw [h2]

private theorem s1611e3_card_mulAut_sixLhat_le :
    Nat.card (MulAut ↥sixLhat) ≤ 1440 := by
  obtain ⟨e⟩ := sixLhat_isAlt
  calc Nat.card (MulAut ↥sixLhat) = Nat.card (MulAut (alternatingGroup (Fin 6))) :=
        Nat.card_congr (MulAut.congr e).toEquiv
    _ ≤ 1440 := CFSG.LargeExtraspecial.S12Tri.card_mulAut_alternatingGroup_six_le

theorem sixGhat_exists_conj (ε : MulAut ↥sixLhat) :
    ∃ g ∈ sixGhat, ∀ l : ↥sixLhat,
      g * (l : MulAut (SixE6 × SixE6)) * g⁻¹ = ((ε l : ↥sixLhat) : MulAut (SixE6 × SixE6)) := by
  have hle := s1611e3_card_mulAut_sixLhat_le
  have hcardG := sixGhat_card
  have hinj := s1611e3_conjHom_injective
  have hcard : Nat.card ↥sixGhat = Nat.card (MulAut ↥sixLhat) := by
    refine le_antisymm ?_ ?_
    · exact Nat.card_le_card_of_injective
        (s1611e3_conjHom : ↥sixGhat → MulAut ↥sixLhat) hinj
    · rw [← hcardG] at hle
      exact hle
  have hsurj : Function.Surjective s1611e3_conjHom :=
    ((Nat.bijective_iff_injective_and_card s1611e3_conjHom).2 ⟨hinj, hcard⟩).2
  obtain ⟨g, hg⟩ := hsurj ε
  refine ⟨(g : MulAut (SixE6 × SixE6)), g.2, fun l => ?_⟩
  have h2 : ((s1611e3_conjHom g) l : MulAut (SixE6 × SixE6)) =
      (ε l : MulAut (SixE6 × SixE6)) :=
    congrArg Subtype.val (congrArg (fun f : MulAut ↥sixLhat => f l) hg)
  simpa [s1611e3_conjHom, s1611e3_conjGhat] using h2

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
