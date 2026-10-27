module

public import CFSG.Quasithin.EmptyFaithful.S153Q3Ac

public section

namespace CFSG.Quasithin

namespace S153Q

namespace Q3A

open scoped Pointwise

section Hom

variable {G H : Type*} [Group G] [Group H]

theorem hom_one_of_perfect {A : Subgroup G} (hA : A ≤ ⁅A, A⁆) (f : A →* H)
    (hcomm : ∀ a b : A, f a * f b = f b * f a) (a : A) : f a = 1 := by
  have hle : ⁅A, A⁆ ≤ f.ker.map A.subtype := by
    rw [Subgroup.commutator_le]
    intro g₁ hg₁ g₂ hg₂
    have hmem : (⟨g₁, hg₁⟩ * ⟨g₂, hg₂⟩ * ⟨g₁, hg₁⟩⁻¹ * ⟨g₂, hg₂⟩⁻¹ : A) ∈ f.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv,
        hcomm ⟨g₁, hg₁⟩ ⟨g₂, hg₂⟩, mul_inv_cancel_right, mul_inv_cancel]
    exact ⟨_, hmem, rfl⟩
  obtain ⟨b, hb, hba⟩ := hle (hA a.2)
  have hba' : b = a := Subtype.ext hba
  rw [← hba']
  exact hb

end Hom

section Rep

variable {W : Type} [CommGroup W] [Finite W] {z : MulAut W}

theorem card_alt6 : Nat.card ↥(alternatingGroup (Fin 6)) = 360 := by
  rw [nat_card_alternatingGroup]
  simp [Nat.factorial]

theorem exists_rep {Γ Ah : Subgroup (MulAut W)} (hG : HatGrp Γ Ah z) (hWc : Nat.card W = 2 ^ 6)
    (hfpf : ∀ w : W, z w = w → w = 1) :
    ∃ (ρ : ↥Ah →* Equiv.Perm (Fin 6)) (H : Fin 6 → Subgroup W),
      (∀ i, IsPt z (H i)) ∧ Function.Injective H ∧
      (∀ (g : ↥Ah) (i : Fin 6), H (ρ g i) = (g : MulAut W) • H i) ∧
      (∀ g : ↥Ah, ρ g ∈ alternatingGroup (Fin 6)) ∧
      (∀ σ ∈ alternatingGroup (Fin 6), ∃ g : ↥Ah, ρ g = σ) ∧
      (∀ g : ↥Ah, ρ g = 1 → (g : MulAut W) ∈ Subgroup.zpowers z) := by
  obtain ⟨o₀, hpt, hcard6, g₀, hg₀, u₀, hu₀, hgu₀⟩ :=
    exists_orbit_six hWc hG.z_cube hfpf hG.z_mem hG.z_central hG.perfect hG.card
  have hpts : ∀ O ∈ MulAction.orbit Ah o₀, IsPt z O := by
    rintro O ⟨g, rfl⟩
    exact isPt_smul hpt (hG.z_central g g.2)
  have hNat : Nat.card (MulAction.orbit Ah o₀) = 6 := by rw [Nat.card_coe_set_eq, hcard6]
  let e : MulAction.orbit Ah o₀ ≃ Fin 6 := (Finite.equivFin _).trans (finCongr hNat)
  let ρ : ↥Ah →* Equiv.Perm (Fin 6) :=
    (Equiv.permCongrHom e).toMonoidHom.comp (MulAction.toPermHom Ah (MulAction.orbit Ah o₀))
  have hρ : ∀ (g : ↥Ah) (i : Fin 6), e.symm (ρ g i) = g • e.symm i := by
    intro g i
    show e.symm (e ((MulAction.toPerm g) (e.symm i))) = _
    rw [e.symm_apply_apply, MulAction.toPerm_apply]
  let H : Fin 6 → Subgroup W := fun i => ((e.symm i : MulAction.orbit Ah o₀) : Subgroup W)
  have hH : ∀ (g : ↥Ah) (i : Fin 6), H (ρ g i) = (g : MulAut W) • H i := by
    intro g i
    show ((e.symm (ρ g i) : MulAction.orbit Ah o₀) : Subgroup W) = _
    rw [hρ]
    rfl
  have hHinj : Function.Injective H := by
    intro i j hij
    have : (e.symm i : MulAction.orbit Ah o₀) = e.symm j := Subtype.ext hij
    exact e.symm.injective this
  have hHpt : ∀ i, IsPt z (H i) := fun i => hpts _ (e.symm i).2
  have hnontriv : ¬ ∀ g : ↥Ah, ρ g = 1 := by
    intro hall
    have hi0 : H (e ⟨o₀, MulAction.mem_orbit_self o₀⟩) = o₀ := by
      show ((e.symm (e ⟨o₀, MulAction.mem_orbit_self o₀⟩) : MulAction.orbit Ah o₀) :
        Subgroup W) = o₀
      rw [e.symm_apply_apply]
    have h2 := hH ⟨g₀, hg₀⟩ (e ⟨o₀, MulAction.mem_orbit_self o₀⟩)
    rw [hall, Equiv.Perm.coe_one, id_eq, hi0] at h2
    apply hgu₀
    rw [h2]
    exact Subgroup.smul_mem_pointwise_smul u₀ g₀ o₀ hu₀
  obtain ⟨ψ, hψsurj, hψker⟩ := hG.psi
  let zA : ↥Ah := ⟨z, hG.z_mem⟩
  have hzρ : ρ zA = 1 := by
    apply Equiv.ext
    intro i
    apply hHinj
    have h1 : (zA : MulAut W) • H i = H i := smul_eq_of_le (fun w hw => (hHpt i).2 w hw)
    rw [hH zA i, h1]
    rfl
  have hcoe_zpow : ∀ g : ↥Ah, (g : MulAut W) ∈ Subgroup.zpowers z → g ∈ ρ.ker := by
    intro g hg
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hg
    have : g = zA ^ n := Subtype.ext (by rw [← hn]; simp [zA])
    rw [this]
    exact zpow_mem (MonoidHom.mem_ker.mpr hzρ) n
  have hsimple : IsSimpleGroup ↥(alternatingGroup (Fin 6)) :=
    alternatingGroup.isSimpleGroup (by simp)
  have hker_le : ρ.ker ≤ ψ.ker := by
    have hnorm : (ρ.ker.map ψ).Normal := Subgroup.Normal.map inferInstance ψ hψsurj
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (ρ.ker.map ψ) with h | h
    · intro g hg
      have : ψ g ∈ ρ.ker.map ψ := Subgroup.mem_map_of_mem ψ hg
      rw [h, Subgroup.mem_bot] at this
      exact this
    · exfalso
      apply hnontriv
      intro g
      have hg : ψ g ∈ ρ.ker.map ψ := h ▸ Subgroup.mem_top _
      obtain ⟨k, hk, hkg⟩ := hg
      have h1 : ψ (k⁻¹ * g) = 1 := by rw [map_mul, map_inv, hkg, inv_mul_cancel]
      have h2 : (k⁻¹ * g : ↥Ah) ∈ ρ.ker := hcoe_zpow _ ((hψker _).mp h1)
      have h3 : g = k * (k⁻¹ * g) := by group
      rw [h3, map_mul, MonoidHom.mem_ker.mp hk, MonoidHom.mem_ker.mp h2, one_mul]
  have hker_eq : ρ.ker = ψ.ker :=
    le_antisymm hker_le (fun g hg => hcoe_zpow g ((hψker g).mp hg))
  have hψcard : Nat.card ↥ψ.ker = 3 := by
    have h := Subgroup.card_ker_mul_card_range ψ
    rw [MonoidHom.range_eq_top_of_surjective ψ hψsurj, Subgroup.card_top, card_alt6, hG.card] at h
    omega
  have hsign : ∀ g : ↥Ah, ρ g ∈ alternatingGroup (Fin 6) := by
    intro g
    have h := hom_one_of_perfect hG.perfect (Equiv.Perm.sign.comp ρ) (fun a b => mul_comm _ _) g
    exact Equiv.Perm.mem_alternatingGroup.mpr h
  have hsurj : ∀ σ ∈ alternatingGroup (Fin 6), ∃ g : ↥Ah, ρ g = σ := by
    have hle : ρ.range ≤ alternatingGroup (Fin 6) := by
      rintro _ ⟨g, rfl⟩
      exact hsign g
    have hcard : Nat.card ↥ρ.range = 360 := by
      have h := Subgroup.card_ker_mul_card_range ρ
      rw [hker_eq, hψcard, hG.card] at h
      omega
    have heq : ρ.range = alternatingGroup (Fin 6) :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [card_alt6, hcard])
    intro σ hσ
    have : σ ∈ ρ.range := heq ▸ hσ
    exact this
  exact ⟨ρ, H, hHpt, hHinj, hH, hsign, hsurj,
    fun g hg => (hψker g).mp (hker_le (MonoidHom.mem_ker.mpr hg))⟩

end Rep

end Q3A

open scoped Pointwise in
theorem exists_ovals0 {W : Type} [CommGroup W] [Finite W] (hW2 : ∀ w : W, w * w = 1)
    (hWc : Nat.card W = 2 ^ 6) {Γ Ah : Subgroup (MulAut W)} {z : MulAut W} (hG : HatGrp Γ Ah z)
    (hfpf : ∀ w : W, z w = w → w = 1) : ∃ lab : Fin 6 → Subgroup W, OvalData0 Ah z lab := by
  have _ := hW2
  obtain ⟨ρ, H, hpt, hinj, hH, halt, hsurj, hker⟩ := Q3A.exists_rep hG hWc hfpf
  refine ⟨H, ⟨hpt, hinj, ?_, ?_, ?_⟩⟩
  · intro g hg
    refine ⟨ρ ⟨g, hg⟩, halt _, fun k w hw => ?_⟩
    rw [hH ⟨g, hg⟩ k]
    exact Subgroup.smul_mem_pointwise_smul w g _ hw
  · intro σ hσ
    obtain ⟨g, hg⟩ := hsurj σ hσ
    refine ⟨g, g.2, fun k w hw => ?_⟩
    rw [← hg, hH g k]
    exact Subgroup.smul_mem_pointwise_smul w (g : MulAut W) _ hw
  · intro g hg hfix
    apply hker ⟨g, hg⟩
    apply Equiv.ext
    intro k
    apply hinj
    have h1 : (g : MulAut W) • H k = H k := Q3A.smul_eq_of_le (fun w hw => hfix k w hw)
    rw [hH ⟨g, hg⟩ k, h1]
    rfl

end S153Q

end CFSG.Quasithin
