module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B42A57Glue

public section

namespace CFSG.Quasithin

namespace B42Alt7

open CFSG.Open CFSG.QuasithinUnique Equiv Equiv.Perm

variable {S : Type} [CommGroup S] [Finite S] {G L : Subgroup (MulAut S)}

structure SymModel (C : Bridge.Alt57.Ctx G L 7) where
  ι : ↥L ≃* alternatingGroup (Fin 7)
  e : ↥G →* Perm (Fin 7)
  ρ : Perm (Fin 7) →* MulAut S
  β : S ≃* ↥(G6.coreMod 7)
  e_inj : Function.Injective e
  e_ι : ∀ l : ↥L, e ⟨(l : MulAut S), C.le_G l.2⟩ = (ι l : Perm (Fin 7))
  ρ_inj : Function.Injective ρ
  ρ_e : ∀ g : ↥G, ρ (e g) = (g : MulAut S)
  ρ_mem : ∀ σ, ρ σ ∈ G
  β_equiv : ∀ (σ : Perm (Fin 7)) (s : S),
    ((β (ρ σ s) : ↥(G6.coreMod 7)) : G6.PermMod 7) = G6.permAct 7 σ (β s)
  transp : ∃ a b : Fin 7, a ≠ b ∧ IsFFStarOffender G (Subgroup.zpowers (ρ (swap a b)))

theorem exists_symModel (hS : ∀ s : S, s * s = 1)
    (C : Bridge.Alt57.Ctx G L 7) (hirr : XMod.IsIrrSec ↥L (⊥ : Subgroup S) ⊤)
    {A : Subgroup (MulAut S)} (hA : IsFFStarOffender G A) (hbig : 32 ≤ Nat.card S) :
    Nonempty (SymModel C) := by
  obtain ⟨A₀, hA₀, hmin⟩ := B42A57.exists_minimal_offender hA
  obtain ⟨ι, e, hinj, hL, -⟩ := B42A57.exists_embedding C
  obtain ⟨h1, hc, h2, hcard⟩ := B42A57.offender_image hA₀ e hinj
  rcases B42A57.classify7 h1 hc h2 with ⟨r, f, hf, hbound, hcl⟩ | hres
  · exfalso
    have := B42A57.card_le_of_cert C hirr hA₀ ι e hinj hL f hf (N := 2 ^ 4)
      (by rw [← hcard]; exact hbound) hcl
    omega
  have hex : ∃ a b : Fin 7, a ≠ b ∧ swap a b ∈ (A₀.subgroupOf G).map e := by
    rcases hres with ⟨-, a, b, hab, h⟩ | ⟨-, a, b, c', d, hnd, h, -⟩ |
      ⟨-, a, b, c', d, e', f', hnd, h, -, -⟩ | ⟨-, a, b, c', d, e', f', hnd, h, -, -⟩
    · exact ⟨a, b, hab, h⟩
    · exact ⟨a, b, B42A57.ne_of_nodup4 hnd, h⟩
    · exact ⟨a, b, B42A57.ne_of_nodup6' hnd, h⟩
    · exact ⟨e', f', B42A57.ne_of_nodup6 hnd, h⟩
  obtain ⟨a, b, hab, hsw⟩ := hex
  obtain ⟨t, htA, het⟩ := Subgroup.mem_map.1 hsw
  obtain ⟨ρ, hρinj, hρe, hρG, hρι⟩ := B42A57.exists_rho C ι e hinj hL t a b hab het
  have hE : ((A₀.subgroupOf G).map e).map ρ = A₀ := by
    rw [Subgroup.map_map]
    have : ρ.comp e = G.subtype := MonoidHom.ext hρe
    rw [this, Subgroup.subgroupOf_map_subtype]
    exact inf_eq_left.2 hA₀.1
  have D := B42A57.minOffData_of hirr hA₀ hmin ι ρ hρinj hρG hρι hE hbig
  have hc2 : Nat.card ((A₀.subgroupOf G).map e) = 2 := by
    rcases hres with ⟨hc2, -⟩ | ⟨hc4, a', b', c', d', hnd, hs1, hs2⟩ |
      ⟨hc8, a', b', c', d', e', f', hnd, hs1, hs2, hs3⟩ |
      ⟨hc8, a', b', c', d', e', f', hnd, hs1, hs2, hs3⟩
    · exact hc2
    · exact (B42A57.R2_false D hc4 hnd hs1 hs2).elim
    · exact (B42A57.R3_false D hc8 hnd hs1 hs2 hs3).elim
    · exact (B42A57.R4_false D hc8 hnd hs1 hs2 hs3).elim
  have htA' : (t : MulAut S) ∈ A₀ := Subgroup.mem_subgroupOf.1 htA
  have hρt : ρ (swap a b) = (t : MulAut S) := by rw [← het]; exact hρe t
  have ht1 : (t : MulAut S) ≠ 1 := by
    intro h
    have : t = 1 := Subtype.ext h
    rw [this, map_one] at het
    exact hab (by simpa [Equiv.swap_eq_one_iff] using het.symm)
  have hle : fixV A₀ ≤ B42A57.fixSub (t : MulAut S) := fun v hv => hv _ htA'
  have hidx : (B42A57.fixSub (t : MulAut S)).index ≤ 2 := by
    have h3 : (B42A57.fixSub (t : MulAut S)).index ≤ (fixV A₀).index :=
      Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
        (Subgroup.index_dvd_of_le hle)
    have h4 := B42A57.index_fixV_le hA₀
    rw [← hcard, hc2] at h4
    omega
  have hzA : Subgroup.zpowers (t : MulAut S) = A₀ := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 htA') ?_
    rw [Nat.card_zpowers, orderOf_eq_prime (hA₀.2.2.1.2 _ htA') ht1, ← hcard, hc2]
  obtain ⟨w, hw1, hwD⟩ := B42A57.exists_disp_of_index_le_two hS (t : MulAut S) ht1 hidx
  have e01 : swap 0 1 = (B42A57.gOf a b)⁻¹ * swap a b * B42A57.gOf a b := by
    have h1 : swap a b = B42A57.gOf a b * swap 0 1 * (B42A57.gOf a b)⁻¹ := by
      rw [← Equiv.swap_apply_apply, B42A57.gOf_zero _ _ hab, B42A57.gOf_one _ _ hab]
    rw [h1]
    group
  have hD01 : B42A57.Disp (ρ (swap 0 1)) = {1, ρ (B42A57.gOf a b)⁻¹ w} := by
    have : ρ (swap 0 1) = ρ (B42A57.gOf a b)⁻¹ * ρ (swap a b) * (ρ (B42A57.gOf a b)⁻¹)⁻¹ := by
      rw [e01]
      simp only [map_mul, map_inv, inv_inv]
    rw [this, B42A57.Disp_conj, hρt, hwD, Set.image_pair, map_one]
  have T : B42A57.TransvData ρ (ρ (B42A57.gOf a b)⁻¹ w) :=
    ⟨hρinj, hS, fun h => hw1 ((ρ (B42A57.gOf a b)⁻¹).injective (by rw [h, map_one])), hD01⟩
  have hirrρ : ∀ U : Subgroup S, (∀ σ ∈ alternatingGroup (Fin 7), ∀ u ∈ U, ρ σ u ∈ U) →
      U = ⊥ ∨ U = ⊤ := by
    intro U hU
    have hinv : XMod.IsInv ↥L U := by
      intro x u hu
      have := hU (ι x : Perm (Fin 7)) (ι x).2 u hu
      rwa [hρι] at this
    exact hirr.2 U hinv bot_le le_top
  obtain ⟨β, hβ⟩ := B42A57.exists_iso_coreMod T hirrρ
  refine ⟨⟨ι, e, ρ, β, hinj, hL, hρinj, hρe, hρG, hβ, a, b, hab, ?_⟩⟩
  rw [hρt, hzA]
  exact hA₀

end B42Alt7

end CFSG.Quasithin
