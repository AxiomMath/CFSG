module

public import CFSG.Quasithin.Vol2.Ch3wLift
public import CFSG.Quasithin.Vol2.Ch3zStep

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique G6 RegularWreathProduct CFSG.Quasithin.Ch3z

namespace Ch3w

section OddFF

variable {V : Type} [CommGroup V] {X T M : Subgroup (MulAut V)} {𝓗 : Finset (Subgroup (MulAut V))}

theorem oTwoUpper_le_of_normal_sup {Γ : Type*} [Group Γ] {H N S : Subgroup Γ} (hNH : N ≤ H)
    (hN : (N.subgroupOf H).Normal) (hS : IsPGroup 2 S) (hSH : S ≤ H) (hH : H ≤ N ⊔ S) :
    oTwoUpper H ≤ N := by
  refine oTwoUpper_le_of_pow_mem fun x hx => ?_
  have hsup : N.subgroupOf H ⊔ S.subgroupOf H = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hNH hSH]
    exact Subgroup.subgroupOf_eq_top.mpr hH
  have hx' : (⟨x, hx⟩ : ↥H) ∈ N.subgroupOf H ⊔ S.subgroupOf H := by
    rw [hsup]
    exact Subgroup.mem_top _
  obtain ⟨n, hn, s, hs, hns⟩ := Subgroup.mem_sup_of_normal_left.mp hx'
  have hS' : IsPGroup 2 (S.subgroupOf H) := hS.of_equiv (Subgroup.subgroupOfEquivOfLe hSH).symm
  obtain ⟨k, hk⟩ := hS' ⟨s, hs⟩
  refine ⟨k, ?_⟩
  have hs1 : s ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have h1 : (QuotientGroup.mk (⟨x, hx⟩ : ↥H) : ↥H ⧸ N.subgroupOf H) = QuotientGroup.mk s := by
    rw [← hns, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff n).mpr hn, one_mul]
  have h2 : (QuotientGroup.mk ((⟨x, hx⟩ : ↥H) ^ 2 ^ k) : ↥H ⧸ N.subgroupOf H) = 1 := by
    rw [QuotientGroup.mk_pow, h1, ← QuotientGroup.mk_pow, hs1, QuotientGroup.mk_one]
  rw [QuotientGroup.eq_one_iff] at h2
  simpa using Subgroup.mem_subgroupOf.mp h2

theorem odd_mem_ffJ (h : BlkCtx X T M 𝓗) {y : MulAut V} (hy : y ∈ X) (ho : Odd (orderOf y)) :
    y ∈ ffJ X := by
  have hJX : ffJ X ≤ X := by
    rw [h.ffJ_eq]
    exact iSup₂_le fun H' hH' => h.mem_le hH'
  have hN : ((ffJ X).subgroupOf X).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (B6.le_normalizer_ffJ X)
  exact oTwoUpper_le_of_normal_sup hJX hN h.mp.isSylow.2.1 h.mp.isSylow.1 h.eq_sup.le
    (mem_oTwoUpper_of_odd hy ho)

end OddFF

section AbstractJ

variable {G : Type} [Group G] [Finite G] {V : Type} [CommGroup V] {X T : Subgroup (MulAut V)}

theorem map_J_eq_base_of_wreathData {H J : Subgroup G} {m : ℕ} {H₁ H₂ : Subgroup (MulAut V)}
    {θ₁ : ↥H₁ ≃* Equiv.Perm (Fin m)} {θ₂ : ↥H₂ ≃* Equiv.Perm (Fin m)} {β₁ β₂ : ↥(coreMod m) →* V}
    {Ψ : (Equiv.Perm (Fin m) ≀ᵣ Q2) ≃* ↥X} (hd : WreathData X T m H₁ H₂ θ₁ θ₂ β₁ β₂ Ψ)
    (ψ : ↥H →* ↥X) (hψ : Function.Surjective ψ) (hKJ : oTwoUpper H ≤ J)
    (hJn : ∀ g ∈ H, ∀ x ∈ J, g * x * g⁻¹ ∈ J)
    (hle : ∀ x : ↥H, (x : G) ∈ J → ((ψ x : ↥X) : MulAut V) ∈ ffJ X)
    (hodd : ∃ x : ↥H, (x : G) ∈ J ∧
      ((∃ ha : ((ψ x : ↥X) : MulAut V) ∈ H₁, Equiv.Perm.sign (θ₁ ⟨_, ha⟩) = -1) ∨
        ∃ ha : ((ψ x : ↥X) : MulAut V) ∈ H₂, Equiv.Perm.sign (θ₂ ⟨_, ha⟩) = -1)) :
    (J.subgroupOf H).map (Ψ.symm.toMonoidHom.comp ψ) =
      (RegularWreathProduct.rightHom : Equiv.Perm (Fin m) ≀ᵣ Q2 →* Q2).ker := by
  refine map_eq_base hKJ hJn _ (Ψ.symm.surjective.comp hψ) ?_ ?_
  · intro x hx
    have h1 : ((ψ x : ↥X) : MulAut V) ∈ H₁ ⊔ H₂ := hd.ffJ_eq ▸ hle x hx
    have h2 := (hd.Ψmem (Ψ.symm (ψ x))).mp (by rw [MulEquiv.apply_symm_apply]; exact h1)
    exact h2
  · obtain ⟨x, hxJ, hx⟩ := hodd
    refine ⟨x, hxJ, ?_⟩
    rcases hx with ⟨ha, hs⟩ | ⟨ha, hs⟩
    · refine ⟨θ₁ ⟨_, ha⟩, hs, Or.inl ?_⟩
      show Ψ.symm (ψ x) = _
      rw [MulEquiv.symm_apply_eq]
      apply Subtype.ext
      rw [hd.Ψ₁, MulEquiv.symm_apply_apply]
    · refine ⟨θ₂ ⟨_, ha⟩, hs, Or.inr ?_⟩
      show Ψ.symm (ψ x) = _
      rw [MulEquiv.symm_apply_eq]
      apply Subtype.ext
      rw [hd.Ψ₂, MulEquiv.symm_apply_apply]

end AbstractJ

section SettingJ

variable {G : Type} [Group G] [Finite G] {H T M₂ U A L N : Subgroup G}

theorem oTwoUpper_le_thompsonJ (h : Setting H T M₂ U A) : oTwoUpper H ≤ thompsonJ H := by
  rw [← F6.twoResidual_eq_oTwoUpper, thompsonJ_eq_sup_of_not_le h.mp h.AT h.An]
  exact le_sup_left

omit [Finite G] in
theorem thompsonJ_conj_mem (H : Subgroup G) : ∀ g ∈ H, ∀ x ∈ thompsonJ H, g * x * g⁻¹ ∈ thompsonJ H :=
  fun _ hg _ hx => (Subgroup.mem_normalizer_iff.mp (B6.le_normalizer_thompsonJ H hg) _).mp hx

theorem exists_mem_of_chiefImg (h : Setting H T M₂ U A) (hstep : IsChiefStep H U L N)
    {a : MulAut ↥(chiefMod L N)}
    (haA : a ∈ chiefImg (Setting.hHL hstep) (Setting.hHN hstep) A) :
    ∃ x : ↥H, (x : G) ∈ thompsonJ H ∧ chiefPsi (Setting.hHL hstep) (Setting.hHN hstep) x = a := by
  obtain ⟨x₀, hx₀, hxa⟩ := haA
  have hx₀A : (x₀ : G) ∈ A := Subgroup.mem_subgroupOf.mp hx₀
  exact ⟨x₀, (B6.thompsonJ_le_of_sylow h.mp.isSylow) (B6.le_thompsonJ h.AT hx₀A), hxa⟩

theorem map_J_top_of_oneWit (h : Setting H T M₂ U A) (hstep : IsChiefStep H U L N) {m : ℕ}
    (θ : ↥(chiefAut H L N) ≃* Equiv.Perm (Fin m)) {a : MulAut ↥(chiefMod L N)}
    (haA : a ∈ chiefImg (Setting.hHL hstep) (Setting.hHN hstep) A) (haX : a ∈ chiefAut H L N)
    (hsign : Equiv.Perm.sign (θ ⟨a, haX⟩) = -1) :
    ((thompsonJ H).subgroupOf H).map
      (θ.toMonoidHom.comp (chiefHom (Setting.hHL hstep) (Setting.hHN hstep))) = ⊤ := by
  obtain ⟨x₀, hxJ, hxa⟩ := exists_mem_of_chiefImg h hstep haA
  refine map_eq_top_of_sign (oTwoUpper_le_thompsonJ h) _
    (θ.surjective.comp (chiefHom_surjective _ _)) hxJ ?_
  show Equiv.Perm.sign (θ (chiefHom _ _ x₀)) = -1
  have : chiefHom (Setting.hHL hstep) (Setting.hHN hstep) x₀ = ⟨a, haX⟩ := Subtype.ext hxa
  rw [this]
  exact hsign

end SettingJ

end Ch3w

end CFSG.Quasithin
