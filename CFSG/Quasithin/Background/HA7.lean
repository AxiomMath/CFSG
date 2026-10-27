module

public import CFSG.Quasithin.Background.HA7Data
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating
public import CFSG.Quasithin.Background.HPairGen

public section

namespace CFSG.Quasithin

namespace H

namespace A7

open CFSG.Open CFSG.Assembly.LowTwoRank Matrix Equiv PairG
open scoped Matrix

theorem index_eq_one_of_simple {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (S : Subgroup G) (h : (S.index).factorial < Nat.card G) : S.index = 1 := by
  classical
  let φ := MulAction.toPermHom G (G ⧸ S)
  rcases (MonoidHom.normal_ker φ).eq_bot_or_eq_top with hk | hk
  · exfalso
    have hinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).mp hk
    have h1 := Nat.card_le_card_of_injective φ hinj
    rw [Nat.card_perm] at h1
    change Nat.card G ≤ S.index.factorial at h1
    omega
  · rw [Subgroup.index_eq_one, eq_top_iff]
    intro g _
    have hg : g ∈ φ.ker := hk ▸ Subgroup.mem_top g
    have h1 : φ g (QuotientGroup.mk 1 : G ⧸ S) = QuotientGroup.mk 1 := by
      rw [MonoidHom.mem_ker.mp hg]
      rfl
    have h2 : φ g (QuotientGroup.mk 1 : G ⧸ S) = QuotientGroup.mk g := by
      change g • (QuotientGroup.mk 1 : G ⧸ S) = _
      rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one]
    rw [h2] at h1
    have h3 := QuotientGroup.eq.mp h1
    rw [mul_one] at h3
    exact inv_mem_iff.mp h3

theorem card_A7 : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
  rw [nat_card_alternatingGroup, Nat.card_fin]
  rfl

theorem isSimpleGroup_A7 : IsSimpleGroup (alternatingGroup (Fin 7)) :=
  alternatingGroup.isSimpleGroup (by simp)

instance : IsSimpleGroup (alternatingGroup (Fin 7)) := isSimpleGroup_A7

theorem not_comm_A7 : ¬ ∀ σ τ : alternatingGroup (Fin 7), σ * τ = τ * σ := by
  intro h
  have h1 := congrArg Subtype.val (h ⟨swap 0 1 * swap 1 2, by
      rw [Equiv.Perm.mem_alternatingGroup, map_mul, Perm.sign_swap (by decide),
        Perm.sign_swap (by decide)]
      rfl⟩ ⟨swap 0 1 * swap 1 3, by
      rw [Equiv.Perm.mem_alternatingGroup, map_mul, Perm.sign_swap (by decide),
        Perm.sign_swap (by decide)]
      rfl⟩)
  revert h1
  decide

theorem eq_one_of_comm_A7 {σ : alternatingGroup (Fin 7)} (h : ∀ τ, σ * τ = τ * σ) : σ = 1 := by
  have hσ : σ ∈ Subgroup.center (alternatingGroup (Fin 7)) :=
    Subgroup.mem_center_iff.mpr fun τ => (h τ).symm
  rcases (Subgroup.center (alternatingGroup (Fin 7))).normal_of_characteristic.eq_bot_or_eq_top
    with hc | hc
  · rwa [hc, Subgroup.mem_bot] at hσ
  · exfalso
    apply not_comm_A7
    intro a b
    have ha : a ∈ Subgroup.center (alternatingGroup (Fin 7)) := hc ▸ Subgroup.mem_top a
    exact (Subgroup.mem_center_iff.mp ha b).symm

variable (α : ↥(alternatingGroup (Fin 8)) ≃* GL (Fin 4) (ZMod 2))

@[expose] noncomputable def rep : ↥(alternatingGroup (Fin 7)) →* GL (Fin 4) (ZMod 2) :=
  α.toMonoidHom.comp altLift7

omit α in
theorem altLift7_injective : Function.Injective altLift7 := by
  intro σ τ h
  apply Subtype.ext
  have h' := congrArg (fun x : alternatingGroup (Fin 8) => (x : Perm (Fin 8))) h
  simp only [coe_altLift7] at h'
  exact Equiv.Perm.viaEmbeddingHom_injective Fin.castSuccEmb h'

theorem rep_injective : Function.Injective (rep α) := α.injective.comp altLift7_injective

@[expose] noncomputable def Γ : Subgroup (GL (Fin 4) (ZMod 2)) := (rep α).range

@[expose] noncomputable def ψ : ↥(alternatingGroup (Fin 7)) ≃* ↥(Γ α) :=
  MonoidHom.ofInjective (rep_injective α)

theorem coe_ψ (σ : alternatingGroup (Fin 7)) :
    ((ψ α σ : Γ α) : GL (Fin 4) (ZMod 2)) = rep α σ :=
  MonoidHom.ofInjective_apply _

theorem card_Γ : Nat.card (Γ α) = 2520 := by
  rw [← Nat.card_congr (ψ α).toEquiv, card_A7]

include α in
theorem card_GL : Nat.card (GL (Fin 4) (ZMod 2)) = 20160 := by
  rw [← Nat.card_congr α.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
  rfl

include α in
theorem isSimpleGroup_GL : IsSimpleGroup (GL (Fin 4) (ZMod 2)) := by
  have : IsSimpleGroup (alternatingGroup (Fin 8)) := alternatingGroup.isSimpleGroup (by simp)
  exact MulEquiv.isSimpleGroup α.symm

theorem eq_one_of_comm {γ : Γ α} (h : ∀ δ : Γ α, γ * δ = δ * γ) : γ = 1 := by
  have h1 : (ψ α).symm γ = 1 := eq_one_of_comm_A7 fun τ => by
    apply (ψ α).injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact h _
  rw [← (ψ α).apply_symm_apply γ, h1, map_one]

theorem card_normalizer :
    Nat.card (Subgroup.centralizer (Γ α : Set (GL (Fin 4) (ZMod 2)))) * 2520 ≤
      Nat.card (Subgroup.normalizer (Γ α : Set (GL (Fin 4) (ZMod 2)))) ∧
    Nat.card (Subgroup.normalizer (Γ α : Set (GL (Fin 4) (ZMod 2)))) ≤
      Nat.card (Subgroup.centralizer (Γ α : Set (GL (Fin 4) (ZMod 2)))) * 5040 := by
  classical
  set N := Subgroup.normalizer (Γ α : Set (GL (Fin 4) (ZMod 2))) with hN
  set C := Subgroup.centralizer (Γ α : Set (GL (Fin 4) (ZMod 2))) with hC
  set φ := (Γ α).normalizerMonoidHom with hφ
  have hCN : C ≤ N := Subgroup.centralizer_le_normalizer _
  have hker : Nat.card φ.ker = Nat.card C := by
    rw [hφ, Subgroup.normalizerMonoidHom_ker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCN).toEquiv
  have hcard : Nat.card N = Nat.card φ.ker * Nat.card φ.range := by
    rw [← Subgroup.card_mul_index φ.ker, Subgroup.index_ker]
  have hrange : 2520 ≤ Nat.card φ.range := by
    rw [← card_Γ α]
    refine Nat.card_le_card_of_injective
      (fun γ : Γ α => (⟨φ ⟨γ, Subgroup.le_normalizer γ.2⟩, ⟨_, rfl⟩⟩ : φ.range))
      fun γ δ h => ?_
    have h1 : φ ⟨γ, Subgroup.le_normalizer γ.2⟩ = φ ⟨δ, Subgroup.le_normalizer δ.2⟩ :=
      congrArg Subtype.val h
    have h2 : δ⁻¹ * γ = 1 := eq_one_of_comm α fun ε => by
      have h3 := congrArg (fun f : MulAut (Γ α) => (f ε : GL (Fin 4) (ZMod 2))) h1
      simp only [hφ, Subgroup.normalizerMonoidHom_apply_apply_coe] at h3
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      calc (δ : GL (Fin 4) (ZMod 2))⁻¹ * γ * ε
          = (δ : GL (Fin 4) (ZMod 2))⁻¹ * (γ * ε * (γ : GL (Fin 4) (ZMod 2))⁻¹) * γ := by group
        _ = (δ : GL (Fin 4) (ZMod 2))⁻¹ * (δ * ε * (δ : GL (Fin 4) (ZMod 2))⁻¹) * γ := by rw [h3]
        _ = ε * ((δ : GL (Fin 4) (ZMod 2))⁻¹ * γ) := by group
    exact (inv_mul_eq_one.mp h2).symm
  have haut : Nat.card (MulAut (Γ α)) = 5040 := by
    rw [Nat.card_congr (MulAut.congr (ψ α)).symm.toEquiv,
      ← Nat.card_congr (Equiv.ofBijective _
        (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7 (by norm_num)
          (by norm_num))),
      Nat.card_perm, Nat.card_fin]
    rfl
  have hrange' : Nat.card φ.range ≤ 5040 := by
    rw [← haut]
    exact Finite.card_subtype_le _
  refine ⟨?_, ?_⟩
  · rw [hcard, hker]
    exact Nat.mul_le_mul_left _ hrange
  · rw [hcard, hker]
    exact Nat.mul_le_mul_left _ hrange'

theorem normalizer_ne_top : Subgroup.normalizer (Γ α : Set (GL (Fin 4) (ZMod 2))) ≠ ⊤ := by
  intro h
  have : IsSimpleGroup (GL (Fin 4) (ZMod 2)) := isSimpleGroup_GL α
  have hn : (Γ α).Normal := Subgroup.normalizer_eq_top_iff.mp h
  rcases hn.eq_bot_or_eq_top with h1 | h1
  · have := card_Γ α
    rw [h1, Subgroup.card_bot] at this
    omega
  · have := card_Γ α
    rw [h1, Subgroup.card_top, card_GL α] at this
    omega

include α in
theorem eight_le_index {S : Subgroup (GL (Fin 4) (ZMod 2))} (hS : S ≠ ⊤) : 8 ≤ S.index := by
  have : IsSimpleGroup (GL (Fin 4) (ZMod 2)) := isSimpleGroup_GL α
  by_contra h
  push Not at h
  apply hS
  rw [← Subgroup.index_eq_one]
  refine index_eq_one_of_simple S ?_
  rw [card_GL α]
  have : S.index.factorial ≤ Nat.factorial 7 := Nat.factorial_le (by omega)
  have h7 : Nat.factorial 7 = 5040 := rfl
  omega

theorem centralizer_eq_bot :
    Subgroup.centralizer (Γ α : Set (GL (Fin 4) (ZMod 2))) = ⊥ := by
  by_contra hC
  have h2 : 2 ≤ Nat.card (Subgroup.centralizer (Γ α : Set (GL (Fin 4) (ZMod 2)))) := by
    obtain ⟨⟨c, hc⟩, hc1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hC
    have := (Finite.one_lt_card_iff_nontrivial (α := ↥(Subgroup.centralizer
      (Γ α : Set (GL (Fin 4) (ZMod 2)))))).mpr ⟨⟨⟨c, hc⟩, 1, hc1⟩⟩
    omega
  have h1 := (card_normalizer α).1
  have h3 := (Subgroup.normalizer (Γ α : Set (GL (Fin 4) (ZMod 2)))).index_mul_card
  rw [card_GL α] at h3
  have h4 := eight_le_index α (normalizer_ne_top α)
  nlinarith

theorem normalizer_eq : Subgroup.normalizer (Γ α : Set (GL (Fin 4) (ZMod 2))) = Γ α := by
  have h1 := (card_normalizer α).2
  rw [centralizer_eq_bot α, Subgroup.card_bot, one_mul] at h1
  have hle : Γ α ≤ Subgroup.normalizer (Γ α : Set (GL (Fin 4) (ZMod 2))) :=
    Subgroup.le_normalizer
  obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hle
  rw [card_Γ α] at hk
  have h3 := (Subgroup.normalizer (Γ α : Set (GL (Fin 4) (ZMod 2)))).index_mul_card
  rw [card_GL α] at h3
  have h4 := eight_le_index α (normalizer_ne_top α)
  have hk1 : k = 1 := by
    rcases Nat.lt_or_ge k 2 with h | h
    · have : k ≠ 0 := by
        rintro rfl
        rw [mul_zero] at hk
        exact Nat.card_pos.ne' hk
      omega
    · exfalso
      rw [hk] at h3
      nlinarith
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [hk, hk1, mul_one, card_Γ α]

@[expose] def s : Perm (Fin 7) := swap 0 1

theorem sign_s : Perm.sign s = -1 := Perm.sign_swap (by decide)

@[expose] noncomputable def θ : MulAut (Γ α) :=
  (ψ α).symm.trans ((MulAut.conjNormal (H := alternatingGroup (Fin 7)) s).trans (ψ α))

theorem θ_apply (σ : alternatingGroup (Fin 7)) :
    θ α (ψ α σ) = ψ α (MulAut.conjNormal (H := alternatingGroup (Fin 7)) s σ) := by
  simp [θ]

theorem θ_θ (γ : Γ α) : θ α (θ α γ) = γ := by
  obtain ⟨σ, rfl⟩ := (ψ α).surjective γ
  rw [θ_apply, θ_apply, ← MulAut.mul_apply, ← map_mul]
  have : s * s = 1 := swap_mul_self 0 1
  rw [this, map_one]
  rfl

theorem exists_aut (β : MulAut (Γ α)) : ∃ A : Γ α,
    (∀ γ, β γ = A * γ * A⁻¹) ∨ ∀ γ, β γ = A * θ α γ * A⁻¹ := by
  obtain ⟨π, hπ⟩ := (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7
    (by norm_num) (by norm_num)).2 ((ψ α).trans (β.trans (ψ α).symm))
  have hβ : ∀ σ, β (ψ α σ) = ψ α (MulAut.conjNormal (H := alternatingGroup (Fin 7)) π σ) := by
    intro σ
    have h := congrArg (fun f : MulAut (alternatingGroup (Fin 7)) => ψ α (f σ)) hπ
    simp only [MulEquiv.trans_apply, MulEquiv.apply_symm_apply] at h
    exact h.symm
  rcases Int.units_eq_one_or (Perm.sign π) with hs | hs
  · refine ⟨ψ α ⟨π, Equiv.Perm.mem_alternatingGroup.mpr hs⟩, Or.inl fun γ => ?_⟩
    obtain ⟨σ, rfl⟩ := (ψ α).surjective γ
    rw [hβ, ← map_inv, ← map_mul, ← map_mul]
    congr 1
  · have hs' : Perm.sign (π * s) = 1 := by rw [map_mul, hs, sign_s]; rfl
    refine ⟨ψ α ⟨π * s, Equiv.Perm.mem_alternatingGroup.mpr hs'⟩, Or.inr fun γ => ?_⟩
    obtain ⟨σ, rfl⟩ := (ψ α).surjective γ
    rw [hβ, θ_apply, ← map_inv, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, MulAut.conjNormal_apply]
    have hss : s * s = 1 := swap_mul_self 0 1
    have hsi : s⁻¹ = s := swap_inv 0 1
    calc π * (σ : Perm (Fin 7)) * π⁻¹ = π * (s * s) * σ * (s⁻¹ * s⁻¹) * π⁻¹ := by
          rw [hss, hsi, hss, mul_one, mul_one]
      _ = π * s * (s * σ * s⁻¹) * (π * s)⁻¹ := by group

end A7

end H

end CFSG.Quasithin
