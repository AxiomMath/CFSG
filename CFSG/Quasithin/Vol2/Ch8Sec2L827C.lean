module

public import CFSG.Quasithin.Vol2.Ch8Sec2L828I
public import Certificates.Data.A5

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin

section L827C

@[expose] def tau2_827 : Equiv.Perm (Fin 5) := Equiv.swap 2 3 * Equiv.swap 3 4

theorem tau2_827_mem : tau2_827 ∈ alternatingGroup (Fin 5) := by
  rw [Equiv.Perm.mem_alternatingGroup, tau2_827, Equiv.Perm.sign_mul,
    Equiv.Perm.sign_swap (by decide), Equiv.Perm.sign_swap (by decide)]
  decide

@[expose] def sig827 : Equiv.Perm (Fin 5) := Equiv.swap 0 2 * Equiv.swap 1 3

theorem sig827_mem : sig827 ∈ alternatingGroup (Fin 5) := by
  rw [Equiv.Perm.mem_alternatingGroup, sig827, Equiv.Perm.sign_mul,
    Equiv.Perm.sign_swap (by decide), Equiv.Perm.sign_swap (by decide)]
  decide

theorem fix_tvec828_827 : ∀ v : Fin 5 → ZMod 2, ∑ j, v j = 0 →
    (∀ j, v (tau828⁻¹ j) = v j) → (∀ j, v (tau2_827⁻¹ j) = v j) → v = 0 ∨ v = tvec828 0 := by
  decide

theorem evec828_add_827 : evec828 + (fun j => evec828 (sig827⁻¹ j)) = tvec828 4 := by
  decide

theorem exists_zeta828_pow_827 : ∀ i j : Fin 5, ∃ k : Fin 5, (zeta828 ^ (k : ℕ)) i = j := by
  decide

theorem zeta828_pow_mem_827 (k : ℕ) : zeta828 ^ k ∈ alternatingGroup (Fin 5) :=
  Subgroup.pow_mem _ zeta828_mem _

theorem eq_top_of_invariant_alt5D_827 {S : Subgroup ↥(G6.coreMod 5)}
    (hS : ∀ γ : ↥(alternatingGroup (Fin 5)), ∀ s ∈ S, alt5D_828 γ s ∈ S) (hne : S ≠ ⊥) :
    S = ⊤ := by
  have hall : ∀ i, t828 i ∈ S → S = ⊤ := by
    intro i hi
    have hT : ∀ j, t828 j ∈ S := by
      intro j
      obtain ⟨k, hk⟩ := exists_zeta828_pow_827 i j
      have h := hS ⟨_, zeta828_pow_mem_827 k⟩ _ hi
      rwa [alt5D_828_apply, coreAct_t828, hk] at h
    rw [eq_top_iff]
    intro v _
    have hsum : ∑ j, Multiplicative.toAdd (v : G6.PermMod 5) j = 0 := v.2
    have hv : v = ∏ i ∈ Finset.univ.filter
        (fun i => Multiplicative.toAdd (v : G6.PermMod 5) i = 1), t828 i := by
      apply Subtype.ext
      rw [show ((∏ i ∈ Finset.univ.filter
          (fun i => Multiplicative.toAdd (v : G6.PermMod 5) i = 1), t828 i : ↥(G6.coreMod 5)) :
            G6.PermMod 5) = ∏ i ∈ Finset.univ.filter
          (fun i => Multiplicative.toAdd (v : G6.PermMod 5) i = 1),
            ((t828 i : ↥(G6.coreMod 5)) : G6.PermMod 5) from map_prod (G6.coreMod 5).subtype _ _]
      apply Multiplicative.toAdd.injective
      rw [toAdd_prod]
      exact eq_sum_tvec828 _ hsum
    rw [hv]
    exact prod_mem fun i _ => hT i
  obtain ⟨⟨v, hvS⟩, hv1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
  have hv1' : v ≠ 1 := fun h => hv1 (Subtype.ext h)
  by_cases hvt : ∃ i, (v : ↥(G6.coreMod 5)) = t828 i
  · obtain ⟨i, hi⟩ := hvt
    exact hall i (hi ▸ hvS)
  · push Not at hvt
    obtain ⟨γ, hγ⟩ := exists_alt5_e828 v hv1' hvt
    set e : ↥(G6.coreMod 5) := ⟨Multiplicative.ofAdd evec828, by rw [G6.mem_coreMod]; decide⟩
      with hedef
    have heS : e ∈ S := by
      have h := hS γ⁻¹ _ hvS
      rw [hγ, ← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply] at h
      exact h
    have he2 : alt5D_828 ⟨sig827, sig827_mem⟩ e ∈ S := hS _ _ heS
    apply hall 4
    have h4 : e * alt5D_828 ⟨sig827, sig827_mem⟩ e = t828 4 := by
      apply Subtype.ext
      apply Multiplicative.toAdd.injective
      rw [Subgroup.coe_mul, toAdd_mul, alt5D_828_apply, G6.coreAct_coe, coe_t828, toAdd_ofAdd]
      funext j
      rw [Pi.add_apply, G6.permAct_apply]
      exact congrFun evec828_add_827 j
    rw [← h4]
    exact S.mul_mem heS he2

theorem eq_one_of_commute_alt5D_827 {φ : MulAut ↥(G6.coreMod 5)}
    (hφ : ∀ γ : ↥(alternatingGroup (Fin 5)), φ * alt5D_828 γ = alt5D_828 γ * φ) : φ = 1 := by
  have hfix : ∀ σ : ↥(alternatingGroup (Fin 5)), (σ : Equiv.Perm (Fin 5)) 0 = 0 →
      alt5D_828 σ (φ (t828 0)) = φ (t828 0) := by
    intro σ hσ
    rw [← MulAut.mul_apply, ← hφ σ, MulAut.mul_apply, alt5D_828_apply, coreAct_t828, hσ]
  have h1 := hfix ⟨tau828, tau828_mem⟩ (by decide)
  have h2 := hfix ⟨tau2_827, tau2_827_mem⟩ (by decide)
  set w := φ (t828 0) with hwdef
  have hw : Multiplicative.toAdd (w : G6.PermMod 5) = 0 ∨
      Multiplicative.toAdd (w : G6.PermMod 5) = tvec828 0 := by
    refine fix_tvec828_827 _ w.2 (fun j => ?_) (fun j => ?_)
    · have h := congrArg (fun x : ↥(G6.coreMod 5) => Multiplicative.toAdd (x : G6.PermMod 5) j) h1
      simp only [alt5D_828_apply, G6.coreAct_coe, G6.permAct_apply] at h
      exact h
    · have h := congrArg (fun x : ↥(G6.coreMod 5) => Multiplicative.toAdd (x : G6.PermMod 5) j) h2
      simp only [alt5D_828_apply, G6.coreAct_coe, G6.permAct_apply] at h
      exact h
  have hw0 : w = t828 0 := by
    rcases hw with hw | hw
    · exfalso
      have h1' : w = 1 := Subtype.ext (Multiplicative.toAdd.injective hw)
      exact t828_ne_one 0 (φ.injective (h1'.trans (map_one φ).symm))
    · exact Subtype.ext (Multiplicative.toAdd.injective hw)
  apply eq_one_of_fix_t828
  intro i
  obtain ⟨k, hk⟩ := exists_zeta828_pow_827 0 i
  have hti : t828 i = alt5D_828 ⟨_, zeta828_pow_mem_827 k⟩ (t828 0) := by
    rw [alt5D_828_apply, coreAct_t828, hk]
  rw [hti, ← MulAut.mul_apply, hφ, MulAut.mul_apply, ← hwdef, hw0]

theorem range_le_of_zeta_mem_827 {Q : Subgroup (MulAut ↥(G6.coreMod 5))}
    (hQ : ∀ γ : ↥(alternatingGroup (Fin 5)), ∀ q ∈ Q, alt5D_828 γ * q * (alt5D_828 γ)⁻¹ ∈ Q)
    (hζ : alt5D_828 ⟨zeta828, zeta828_mem⟩ ∈ Q) : alt5D_828.range ≤ Q := by
  set N := Q.comap alt5D_828 with hNdef
  have hNn : N.Normal := ⟨fun n hn g => by
    rw [hNdef, Subgroup.mem_comap] at hn ⊢
    rw [map_mul, map_mul, map_inv]
    exact hQ g _ hn⟩
  have hζN : (⟨zeta828, zeta828_mem⟩ : ↥(alternatingGroup (Fin 5))) ∈ N := hζ
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
  · exfalso
    have h1 := (Subgroup.mem_bot.mp (h ▸ hζN))
    have h2 := congrArg Subtype.val h1
    revert h2
    decide
  · rintro _ ⟨γ, rfl⟩
    have hγ : γ ∈ N := h ▸ Subgroup.mem_top γ
    exact hγ

variable {W : Type} [CommGroup W]

theorem eq_top_of_invariant_827 {X : Subgroup (MulAut W)} (hX : AlternatingNatural X ⊤ ⊥ 5)
    {S : Subgroup W} (hS : ∀ x ∈ X, ∀ s ∈ S, x s ∈ S) (hne : S ≠ ⊥) : S = ⊤ := by
  obtain ⟨e, he⟩ := exists_equiv_alt5_828 hX
  set S' := S.map e.toMonoidHom with hS'def
  have hS' : ∀ γ : ↥(alternatingGroup (Fin 5)), ∀ s ∈ S', alt5D_828 γ s ∈ S' := by
    intro γ s hs
    have hγ : alt5D_828 γ ∈ X.map (MulAut.congr e).toMonoidHom := he ▸ ⟨γ, rfl⟩
    obtain ⟨x, hx, hxγ⟩ := hγ
    obtain ⟨u, hu, rfl⟩ := hs
    rw [← hxγ]
    refine ⟨x u, hS x hx u hu, ?_⟩
    simp [MulAut.congr_apply]
  have hne' : S' ≠ ⊥ := by
    intro h
    apply hne
    rw [eq_bot_iff]
    intro s hs
    have h1 : e s ∈ S' := ⟨s, hs, rfl⟩
    rw [h, Subgroup.mem_bot] at h1
    rw [Subgroup.mem_bot]
    exact e.injective (h1.trans (map_one e).symm)
  have htop := eq_top_of_invariant_alt5D_827 hS' hne'
  rw [eq_top_iff]
  intro w _
  have h1 : e w ∈ S' := htop ▸ Subgroup.mem_top _
  obtain ⟨u, hu, hue⟩ := h1
  have : u = w := e.injective hue
  exact this ▸ hu

theorem eq_one_of_commute_827 {X : Subgroup (MulAut W)} (hX : AlternatingNatural X ⊤ ⊥ 5)
    {φ : MulAut W} (hφ : ∀ x ∈ X, φ * x = x * φ) : φ = 1 := by
  obtain ⟨e, he⟩ := exists_equiv_alt5_828 hX
  have h := eq_one_of_commute_alt5D_827 (φ := MulAut.congr e φ) (fun γ => by
    have hγ : alt5D_828 γ ∈ X.map (MulAut.congr e).toMonoidHom := he ▸ ⟨γ, rfl⟩
    obtain ⟨x, hx, hxγ⟩ := hγ
    rw [← hxγ]
    show MulAut.congr e φ * MulAut.congr e x = MulAut.congr e x * MulAut.congr e φ
    rw [← map_mul, ← map_mul, hφ x hx])
  exact (MulAut.congr e).injective (h.trans (map_one _).symm)

theorem le_of_pow_five_827 {X Q : Subgroup (MulAut W)} (hX : AlternatingNatural X ⊤ ⊥ 5)
    (hQ : ∀ x ∈ X, ∀ q ∈ Q, x * q * x⁻¹ ∈ Q) (h5 : ∀ x ∈ X, x ^ 5 = 1 → x ∈ Q) : X ≤ Q := by
  obtain ⟨e, he⟩ := exists_equiv_alt5_828 hX
  set c := (MulAut.congr e).toMonoidHom with hcdef
  have hc : Function.Injective c := (MulAut.congr e).injective
  have hpre : ∀ γ : ↥(alternatingGroup (Fin 5)), ∃ x ∈ X, c x = alt5D_828 γ := fun γ => by
    have hγ : alt5D_828 γ ∈ X.map c := he ▸ ⟨γ, rfl⟩
    exact hγ
  have hQ' : ∀ γ : ↥(alternatingGroup (Fin 5)), ∀ q ∈ Q.map c,
      alt5D_828 γ * q * (alt5D_828 γ)⁻¹ ∈ Q.map c := by
    intro γ q hq
    obtain ⟨x, hx, hxγ⟩ := hpre γ
    obtain ⟨q', hq', rfl⟩ := hq
    rw [← hxγ, ← map_inv, ← map_mul, ← map_mul]
    exact ⟨_, hQ x hx q' hq', rfl⟩
  have hζ : alt5D_828 ⟨zeta828, zeta828_mem⟩ ∈ Q.map c := by
    obtain ⟨x, hx, hxζ⟩ := hpre ⟨zeta828, zeta828_mem⟩
    have hx5 : x ^ 5 = 1 := by
      apply hc
      rw [map_pow, hxζ, map_one, ← map_pow]
      have : (⟨zeta828, zeta828_mem⟩ : ↥(alternatingGroup (Fin 5))) ^ 5 = 1 :=
        Subtype.ext (by decide)
      rw [this, map_one]
    exact ⟨x, h5 x hx hx5, hxζ⟩
  have hle := range_le_of_zeta_mem_827 hQ' hζ
  rw [← he] at hle
  exact (Subgroup.map_le_map_iff_of_injective hc).mp hle

end L827C

end CFSG.Quasithin.H13
