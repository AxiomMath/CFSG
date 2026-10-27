module

public import CFSG.Sporadic.Schreier.RuCentersMain
public import CFSG.Sporadic.Schreier.RuElemAut

public noncomputable section

namespace CFSG.Sporadic.RuSchreier

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native

theorem card_mulAut_ruESub :
    Nat.card (MulAut ruESub) = 168 :=
  ru_card_mulAut_eight ruESub_comm ruESub_sq card_ruESub

theorem ruP_centralizer_E :
    ruP ⊓ Subgroup.centralizer (ruESub : Set (Equiv.Perm (Fin 4060))) = ruK := by
  apply le_antisymm
  · rintro g ⟨hgP, hgE⟩
    have hgC : g ∈ ruC := by
      rw [ruC_eq_centralizer]
      exact ⟨hgP, Subgroup.mem_centralizer_singleton_iff.2
        (Subgroup.mem_centralizer_iff.1 hgE ruZ ruZ_memE).symm⟩
    rw [← ruCentralizer_E]
    exact ⟨hgC, hgE⟩
  · intro k hk
    have := ruCentralizer_E.symm ▸ hk
    exact ⟨ruC_le this.1, this.2⟩

theorem normalizer_K_le_normalizer_E :
    Subgroup.normalizer (ruK : Set (Equiv.Perm (Fin 4060))) ≤
      Subgroup.normalizer (ruESub : Set (Equiv.Perm (Fin 4060))) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff] at hg ⊢
  have key : ∀ g : Equiv.Perm (Fin 4060), (∀ h, h ∈ ruK ↔ g * h * g⁻¹ ∈ ruK) →
      ∀ x ∈ ruESub, g * x * g⁻¹ ∈ ruESub := by
    intro g hg x hx
    rw [ruE_eq_center] at hx ⊢
    obtain ⟨y, hy, rfl⟩ := hx
    refine ⟨⟨g * y * g⁻¹, (hg y).1 y.2⟩, Subgroup.mem_center_iff.2 fun k => ?_, rfl⟩
    apply Subtype.ext
    have hk' : g⁻¹ * k * g ∈ ruK := by
      have := (hg (g⁻¹ * k * g)).2
      simp only [mul_assoc, mul_inv_cancel, mul_one, mul_inv_cancel_left] at this
      exact this k.2
    have hc := congrArg Subtype.val (Subgroup.mem_center_iff.1 hy ⟨_, hk'⟩)
    simp only [Subgroup.coe_mul] at hc ⊢
    calc (k : Equiv.Perm (Fin 4060)) * (g * y * g⁻¹) = g * ((g⁻¹ * k * g) * y) * g⁻¹ := by group
      _ = g * (y * (g⁻¹ * k * g)) * g⁻¹ := by rw [hc]
      _ = g * y * g⁻¹ * k := by group
  have hinv : ∀ h, h ∈ ruK ↔ g⁻¹ * h * g⁻¹⁻¹ ∈ ruK := by
    intro h
    constructor
    · intro hh
      have := (hg (g⁻¹ * h * g)).2
      simp only [mul_assoc, mul_inv_cancel, mul_one, mul_inv_cancel_left] at this
      simpa [mul_assoc] using this hh
    · intro hh
      have := (hg (g⁻¹ * h * g)).1 (by simpa [mul_assoc] using hh)
      simpa [mul_assoc] using this
  intro h
  constructor
  · exact key g hg h
  · intro hh
    have := key g⁻¹ hinv _ hh
    simpa [mul_assoc] using this

theorem ruN_le_normalizer_K :
    ruN ≤ Subgroup.normalizer (ruK : Set (Equiv.Perm (Fin 4060))) := by
  intro n hn
  rw [Subgroup.mem_normalizer_iff]
  have hN := (Subgroup.normal_subgroupOf_iff ruK_leN).1 ruK_normal
  intro h
  constructor
  · intro hh
    exact hN h n hh hn
  · intro hh
    have := hN _ n⁻¹ hh (ruN.inv_mem hn)
    simpa [mul_assoc] using this

theorem card_normalizer_E_le :
    Nat.card (ruP ⊓ Subgroup.normalizer (ruESub : Set (Equiv.Perm (Fin 4060))) : Subgroup _) ≤
      344064 := by
  set V := ruP ⊓ Subgroup.normalizer (ruESub : Set (Equiv.Perm (Fin 4060)))
  let ψ : V →* MulAut ruESub :=
    (Subgroup.normalizerMonoidHom ruESub).comp (Subgroup.inclusion inf_le_right)
  have hker : Nat.card ψ.ker ≤ 2048 := by
    let f : ψ.ker → ruK := fun x => ⟨((x : V) : Equiv.Perm (Fin 4060)), by
      rw [← ruP_centralizer_E]
      refine ⟨(x : V).2.1, Subgroup.mem_centralizer_iff.2 fun e he => ?_⟩
      have h1 := DFunLike.congr_fun x.2 ⟨e, he⟩
      have h2 := congrArg Subtype.val h1
      simp only [MonoidHom.comp_apply, MulAut.one_apply, ψ,
        Subgroup.normalizerMonoidHom_apply_apply_coe] at h2
      have h3 : ((x : V) : Equiv.Perm (Fin 4060)) * e * ((x : V) : Equiv.Perm (Fin 4060))⁻¹ = e :=
        h2
      calc e * ((x : V) : Equiv.Perm (Fin 4060))
          = (((x : V) : Equiv.Perm (Fin 4060)) * e * ((x : V) : Equiv.Perm (Fin 4060))⁻¹) *
            ((x : V) : Equiv.Perm (Fin 4060)) := by rw [h3]
        _ = ((x : V) : Equiv.Perm (Fin 4060)) * e := by group⟩
    have hf : Function.Injective f := fun x y h => by
      have h' := congrArg (fun k : ruK => (k : Equiv.Perm (Fin 4060))) h
      exact Subtype.ext (Subtype.ext h')
    rw [← card_ruK]
    exact Nat.card_le_card_of_injective f hf
  have hrange : Nat.card ψ.range ≤ 168 := by
    rw [← card_mulAut_ruESub]
    exact Subgroup.card_le_card_group _
  have h := card_ker_mul_card_range ψ
  have : Nat.card V ≤ 2048 * 168 := by
    rw [← h]
    exact Nat.mul_le_mul hker hrange
  simpa using this

theorem ruN_eq_normalizer :
    ruN = ruP ⊓ Subgroup.normalizer (ruK : Set (Equiv.Perm (Fin 4060))) := by
  have h1 : ruN ≤ ruP ⊓ Subgroup.normalizer (ruK : Set (Equiv.Perm (Fin 4060))) :=
    le_inf ruN_le ruN_le_normalizer_K
  have h2 : ruP ⊓ Subgroup.normalizer (ruK : Set (Equiv.Perm (Fin 4060))) ≤
      ruP ⊓ Subgroup.normalizer (ruESub : Set (Equiv.Perm (Fin 4060))) :=
    inf_le_inf_left _ normalizer_K_le_normalizer_E
  have h3 : ruN = ruP ⊓ Subgroup.normalizer (ruESub : Set (Equiv.Perm (Fin 4060))) :=
    Subgroup.eq_of_le_of_card_ge (h1.trans h2) (card_normalizer_E_le.trans card_ruN.ge)
  exact le_antisymm h1 (h3 ▸ h2)

theorem isPGroup_ruJ :
    IsPGroup 2 ruJ := IsPGroup.of_card (n := 11) (by rw [card_ruJ]; norm_num)

theorem isPGroup_ruK :
    IsPGroup 2 ruK := IsPGroup.of_card (n := 11) (by rw [card_ruK]; norm_num)

theorem AT_Ru_intrinsic_local_pair :
    (∃ T : Sylow 2 ruP, (T : Subgroup ruP) = ruS.subgroupOf ruP) ∧
    ruC = ruP ⊓ Subgroup.centralizer ((Subgroup.center ruS).map ruS.subtype : Set _) ∧
    ruN = ruP ⊓ Subgroup.normalizer (ruK : Set (Equiv.Perm (Fin 4060))) ∧ ruC ⊔ ruN = ruP ∧
    IsPGroup 2 ruJ ∧ IsPGroup 2 ruK ∧ ruJ ≤ ruC ∧ ruK ≤ ruN ∧ (ruJ.subgroupOf ruC).Normal ∧
    (ruK.subgroupOf ruN).Normal ∧ ruJ ≤ ruS ∧ ruK ≤ ruS ∧
    ruC ⊓ Subgroup.centralizer (ruJ : Set (Equiv.Perm (Fin 4060))) ≤ ruJ ∧
    ruN ⊓ Subgroup.centralizer (ruK : Set (Equiv.Perm (Fin 4060))) ≤ ruK :=
  ⟨⟨ruSylow, rfl⟩, ruC_eq_centralizer_center, ruN_eq_normalizer, ruP_eq_sup.symm, isPGroup_ruJ,
    isPGroup_ruK, ruJ_leC, ruK_leN, ruJ_normal, ruK_normal, ruJ_leS, ruK_leS, ruCentralizer_J,
    ruCentralizer_K⟩

end CFSG.Sporadic.RuSchreier
