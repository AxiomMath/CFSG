module

public import CFSG.Quasithin.Vol2.Asc94.He42Ident

public section

namespace CFSG.Quasithin.L34CIT

open CFSG.ComponentClassification.WittDesign CFSG.Quasithin.A94.He42Plane
  CFSG.Quasithin.A94.He42Ident

theorem typeL34_of_steinerPlane
    {L : Type} [Group L] [Finite L] (L₁ L₂ : Subgroup L)
    (hplane : IsSteinerPlane (lineSet L₁ L₂))
    (hL₁ : Nat.card L₁ = 960)
    (hker : ∀ g : L, (∀ p : L ⧸ L₁, g • p = p) → g = 1) (hperf : commutator L = ⊤) :
    CFSG.ComponentClassification.AS81.TypeL34 L := by
  classical
  set α : L →* Equiv.Perm (L ⧸ L₁) := MulAction.toPermHom L (L ⧸ L₁) with hα
  have hαapply : ∀ (g : L) (p : L ⧸ L₁), α g p = g • p := fun _ _ => rfl
  have hαker : α.ker = ⊥ := by
    ext g
    rw [MonoidHom.mem_ker, Equiv.Perm.ext_iff, Subgroup.mem_bot]
    constructor
    · intro hg
      exact hker g fun p => by
        have h := hg p
        rwa [hαapply, Equiv.Perm.one_apply] at h
    · rintro rfl p
      simp
  have hPcard : Nat.card (L ⧸ L₁) = 21 := by
    rw [Nat.card_eq_fintype_card, hplane.card_points]
  have hcardL : Nat.card L = 20160 := by
    have h := Subgroup.card_mul_index L₁
    rw [Subgroup.index_eq_card, hPcard, hL₁] at h
    omega
  obtain ⟨-, -, -, hcomp4, -, -, -, -, -, -, -, hcardS, -, hnorm, hrel⟩ :=
    pg24_unique_and_collineation_group.{0}
  obtain ⟨e, he⟩ := hcomp4 (lineSet L₁ L₂) hplane
  set ψ : L →* Equiv.Perm PG24Point := e.permCongrHom.toMonoidHom.comp α with hψdef
  have hψapply : ∀ g : L, ψ g = e.permCongr (MulAction.toPerm g) := fun _ => rfl
  have hψmem : ∀ g : L, ψ g ∈ blockAut PG24Lines := by
    intro g
    rw [mem_blockAut]
    intro B'
    rw [hψapply, he42id_map_permCongr, ← he]
    rw [mem_blockAut.1 (he42id_perm_mem_blockAut L₁ L₂ g) (B'.map e.symm.toEmbedding), he,
      he42id_map_symm_map]
  haveI := hnorm
  set ψ' : L →* ↥(blockAut PG24Lines) := ψ.codRestrict (blockAut PG24Lines) hψmem with hψ'
  set S := (rhoGL.comp slHom).range with hS
  have hNcard : Nat.card (↥(blockAut PG24Lines) ⧸ S.subgroupOf (blockAut PG24Lines)) = 6 := by
    rw [← Subgroup.index_eq_card]
    exact hrel
  haveI : Group.IsSolvable (↥(blockAut PG24Lines) ⧸ S.subgroupOf (blockAut PG24Lines)) :=
    he42id_isSolvable_of_card_six _ hNcard
  have hf := he42id_eq_one_of_perfect_of_solvable hperf
    ((QuotientGroup.mk' (S.subgroupOf (blockAut PG24Lines))).comp ψ')
  have hψS : ∀ g : L, ψ g ∈ S := by
    intro g
    have h1 := hf g
    simp only [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact Subgroup.mem_subgroupOf.1 h1
  set ψS : L →* S := ψ.codRestrict S hψS with hψS_def
  have hψker_iff : ∀ g : L, ψ g = 1 ↔ α g = 1 := fun g =>
    map_eq_one_iff e.permCongrHom e.permCongrHom.injective
  have hψSker : ψS.ker = ⊥ := by
    rw [← hαker]
    ext g
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, ← hψker_iff g]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  haveI : Finite S := Nat.finite_of_card_ne_zero (by rw [hcardS]; norm_num)
  have hrange : ψS.range = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange ψS).toEquiv, hψSker,
      Nat.card_congr QuotientGroup.quotientBot.toEquiv, hcardL, hcardS]
  have hsurj : Function.Surjective ψS := MonoidHom.range_eq_top.1 hrange
  have hinj : Function.Injective ψS := by
    rw [← MonoidHom.ker_eq_bot_iff, hψSker]
  let e₁ : L ≃* S := MulEquiv.ofBijective ψS ⟨hinj, hsurj⟩
  let e₂ : L ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) CFSG.Fischer.F4 :=
    e₁.trans rangeSLEquivPSL
  exact CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv e₂.symm he42id_stated_psl34

end CFSG.Quasithin.L34CIT
