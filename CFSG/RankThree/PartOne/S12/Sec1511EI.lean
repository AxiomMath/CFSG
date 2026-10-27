module

public import CFSG.RankThree.PartOne.S12.Sec1511EILin
public import CFSG.RankThree.PartOne.S12.Sec1511Tools
public import CFSG.RankThree.PartOne.S12.LinAlg
public import CFSG.RankThree.PartOne.S12.LAMaschke
public import CFSG.RankThree.PartOne.S12.WeylIso
public import CFSG.RankThree.PartOne.S12.Sec12Three

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.RankThree.PartOne.LinAlg

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace Sec1511

section Generation

variable {G : Type} [Group G] [Finite G]

theorem not_dvd_weyl_order {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    ¬ p ∣ 24 ∧ ¬ p ∣ 48 := by
  constructor
  · intro hd
    have h : p ∣ 2 ^ 3 * 3 := by norm_num; exact hd
    rcases (Nat.Prime.dvd_mul hp).1 h with h | h
    · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h)
      omega
    · have := Nat.le_of_dvd (by norm_num) h
      omega
  · intro hd
    have h : p ∣ 2 ^ 4 * 3 := by norm_num; exact hd
    rcases (Nat.Prime.dvd_mul hp).1 h with h | h
    · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h)
      omega
    · have := Nat.le_of_dvd (by norm_num) h
      omega

theorem iSup_autMoved_eq {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) {E : Subgroup G}
    [IsElementaryAbelian p ↥E] (hcard : Nat.card E = p ^ 3)
    (hX : Nonempty (↥(reflectionGroup p E) ≃* Equiv.Perm (Fin 4)) ∨
      Nonempty (↥(reflectionGroup p E) ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 4)))
    (hne : (reflectionSet p E).Nonempty) :
    (⨆ (t : MulAut E) (_ : t ∈ reflectionSet p E), autMovedInG E t) = E := by
  classical
  have hp : p.Prime := Fact.out
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have h1 : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h1
    have := Nat.le_of_dvd (by norm_num) h1
    omega
  set X := reflectionGroup p E with hXdef
  obtain ⟨ι, hι, hXord⟩ : ∃ ι : Equiv.Perm (Fin 4) →* ↥(reflectionGroup p E),
      Function.Injective ι ∧ ¬ p ∣ Nat.card (reflectionGroup p E) := by
    obtain ⟨h24, h48⟩ := not_dvd_weyl_order hp hp5
    rcases hX with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
    · refine ⟨e.symm.toMonoidHom, e.symm.injective, ?_⟩
      rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm]
      simpa [Nat.factorial] using h24
    · have hinr : Function.Injective
          (MonoidHom.inr (Multiplicative (ZMod 2)) (Equiv.Perm (Fin 4))) := fun a b h =>
        congrArg Prod.snd h
      refine ⟨e.symm.toMonoidHom.comp (MonoidHom.inr _ _), e.symm.injective.comp hinr, ?_⟩
      rw [Nat.card_congr e.toEquiv, Nat.card_prod, Nat.card_eq_fintype_card (α := Equiv.Perm (Fin 4)),
        Fintype.card_perm]
      have : Nat.card (Multiplicative (ZMod 2)) = 2 := by
        rw [Nat.card_eq_fintype_card]
        decide
      rw [this]
      simpa [Nat.factorial] using h48
  set M : Subgroup G := ⨆ (t : MulAut E) (_ : t ∈ reflectionSet p E), autMovedInG E t with hM
  have hME : M ≤ E := iSup₂_le fun t _ => Subgroup.map_subtype_le _
  have hMinv : ∀ w ∈ Subgroup.normalizer (E : Set G), ∀ b ∈ M, w * b * w⁻¹ ∈ M := by
    intro w hwN b hb
    have hle : conjBy w M ≤ M := by
      unfold conjBy
      rw [hM, Subgroup.map_iSup]
      refine iSup_le fun t => ?_
      rw [Subgroup.map_iSup]
      refine iSup_le fun ht => ?_
      have h1 := Equivariance.autMovedInG_conj t hwN
      have hR : conjAut E w hwN * t * (conjAut E w hwN)⁻¹ ∈ reflectionSet p E :=
        conj_mem_reflectionSet hp ht hwN
      calc Subgroup.map (MulAut.conj w).toMonoidHom (autMovedInG E t)
          = autMovedInG E (conjAut E w hwN * t * (conjAut E w hwN)⁻¹) := h1.symm
        _ ≤ M := le_iSup₂ (f := fun (t : MulAut E) (_ : t ∈ reflectionSet p E) =>
              autMovedInG E t) _ hR
    exact hle (Subgroup.mem_map_of_mem _ hb)
  have hM0 : M ≠ ⊥ := by
    obtain ⟨t, ht⟩ := hne
    intro hbot
    have h1 : autMovedInG E t ≤ M := le_iSup₂ (f := fun (t : MulAut E)
      (_ : t ∈ reflectionSet p E) => autMovedInG E t) t ht
    rw [hbot, le_bot_iff] at h1
    have h2 : Nat.card (autMovedInG E t) = p := by
      unfold autMovedInG
      rw [Subgroup.card_map_of_injective E.subtype_injective]
      exact ht.1.2
    rw [h1, Subgroup.card_bot] at h2
    have := hp.two_le
    omega
  refine le_antisymm hME ?_
  by_contra hEM
  have hMlt : M ≠ E := fun h => hEM (h ▸ le_rfl)
  obtain ⟨f⟩ := LinAlg.exists_coords E hcard
  have hXW : X ≤ torusWeyl E := WeylIso.closure_le_weyl
  set U := bsub f M with hU
  have hMX : ∀ φ ∈ X, ∀ b (hb : b ∈ M), ((φ ⟨b, hME hb⟩ : E) : G) ∈ M := by
    intro φ hφ b hb
    obtain ⟨w, hw, rfl⟩ := WeylIso.exists_lift (hXW hφ)
    rw [Equivariance.coe_conjAut hw]
    exact hMinv w hw b hb
  have hUinv : ∀ φ ∈ X, ∀ u ∈ U, coordLin f φ u ∈ U := fun φ hφ u hu =>
    (preserves_iff_map_coordLin_le_of_subgroup f X hME).1 hMX φ hφ (Submodule.mem_map_of_mem hu)
  set Γ : Subgroup ((Fin 3 → ZMod p) ≃ₗ[ZMod p] (Fin 3 → ZMod p)) := X.map (coordHom f) with hΓ
  have hΓord : ¬ p ∣ Nat.card Γ := by
    rw [hΓ, Subgroup.card_map_of_injective (coordHom_injective f)]
    exact hXord
  have hΓU : ∀ g ∈ Γ, ∀ u ∈ U, g u ∈ U := by
    rintro _ ⟨φ, hφ, rfl⟩ u hu
    exact hUinv φ hφ u hu
  obtain ⟨U', hC, hU'inv⟩ := exists_invariant_compl_of_not_dvd Γ hΓord U hΓU
  have hgen : ∀ φ ∈ X, ∀ v, coordLin f φ v - v ∈ U := by
    intro φ hφ
    refine Subgroup.closure_induction (p := fun φ _ => ∀ v, coordLin f φ v - v ∈ U) ?_ ?_ ?_ ?_ hφ
    · intro t ht v
      have h1 : coordLin f t v - v ∈ LinearMap.range (coordSub f t) := ⟨v, rfl⟩
      rw [← bsub_autMovedInG f t] at h1
      exact (bsub_le_bsub_iff f (Subgroup.map_subtype_le _) hME).2
        (le_iSup₂ (f := fun (t : MulAut E) (_ : t ∈ reflectionSet p E) => autMovedInG E t) t ht) h1
    · intro v
      have h : coordLin f 1 v = v := by
        rw [show coordLin f 1 v = coordHom f 1 v from rfl, map_one]
        rfl
      rw [h, sub_self]
      exact U.zero_mem
    · intro a b ha hb iha ihb v
      have h1 : coordLin f (a * b) v - v =
          coordLin f a (coordLin f b v - v) + (coordLin f a v - v) := by
        have : coordLin f (a * b) v = coordLin f a (coordLin f b v) := by
          have := LinearEquiv.mul_apply (coordHom f a) (coordHom f b) v
          rw [← map_mul] at this
          exact this
        rw [this, map_sub]
        abel
      rw [h1]
      exact U.add_mem (hUinv a ha _ (ihb v)) (iha v)
    · intro a ha iha v
      have h1 : coordLin f a⁻¹ v - v = -(coordLin f a⁻¹ (coordLin f a v - v)) := by
        have : coordLin f a⁻¹ (coordLin f a v) = v := by
          have := LinearEquiv.mul_apply (coordHom f a⁻¹) (coordHom f a) v
          rw [← map_mul, inv_mul_cancel, map_one] at this
          exact this.symm
        rw [map_sub, this]
        abel
      rw [h1]
      exact U.neg_mem (hUinv a⁻¹ (X.inv_mem ha) _ (iha v))
  have hfix : ∀ φ ∈ X, ∀ u ∈ U', coordLin f φ u = u := by
    intro φ hφ u hu
    have h1 : coordLin f φ u - u ∈ U := hgen φ hφ u
    have h2 : coordLin f φ u ∈ U' := hU'inv (coordHom f φ) ⟨φ, hφ, rfl⟩ u hu
    have h3 : coordLin f φ u - u ∈ U' := U'.sub_mem h2 hu
    have h4 : coordLin f φ u - u ∈ U ⊓ U' := ⟨h1, h3⟩
    rw [hC.inf_eq_bot, Submodule.mem_bot, sub_eq_zero] at h4
    exact h4
  have hU'bot : U' ≠ ⊥ := by
    intro hbot
    have htop : U = ⊤ := by
      have := hC.sup_eq_top
      rwa [hbot, sup_bot_eq] at this
    apply hMlt
    have h5 : bsub f M = bsub f E := by rw [bsub_self, ← hU, htop]
    exact (bsub_injective f hME le_rfl).1 h5
  let ψ : Equiv.Perm (Fin 4) →* ((Fin 3 → ZMod p) ≃ₗ[ZMod p] (Fin 3 → ZMod p)) :=
    (coordHom f).comp (X.subtype.comp ι)
  have hψ : Function.Injective ψ :=
    (coordHom_injective f).comp (X.subtype_injective.comp hι)
  exact false_of_fixed_complement h2 (by simp) ψ hψ U U' hC
    (fun σ u hu => hUinv _ (ι σ).2 u hu) (fun σ u hu => hfix _ (ι σ).2 u hu) hU'bot

end Generation

@[expose] def KFEIMoved : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec15Hyp G p A c L E → Sec12Facts G p A c L E → Outcome152 p E A (lieGenerated p E) →
    ¬ Outcome152Five p E A (lieGenerated p E) →
    ∀ t ∈ reflectionSet p E, autMovedInG E t ≤ lieGenerated p E

theorem kfEI_of_moved (hMoved : KFEIMoved) : KFEI := by
  intro G _ _ p A c L E h15 hF hout hnot
  have h := h15.h12
  have hp : p.Prime := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have hp5 : 5 ≤ p := Sec12Three.five_le h
  have := h.E_elem
  have hEA : E = A ∧ (Nonempty (↥(reflectionGroup p E) ≃* Equiv.Perm (Fin 4)) ∨
      Nonempty (↥(reflectionGroup p E) ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 4))) := by
    rcases hout with ⟨-, -, -, -, h4, hEA, -⟩ | ⟨-, -, -, -, h4, hEA, -⟩ |
      ⟨-, -, -, -, h4, hEA, -⟩ | ⟨-, -, -, -, h4, hEA, -⟩ | h5
    · exact ⟨hEA, Or.inl h4⟩
    · exact ⟨hEA, Or.inr h4⟩
    · exact ⟨hEA, Or.inr h4⟩
    · exact ⟨hEA, Or.inr h4⟩
    · exact absurd h5 hnot
  obtain ⟨hEA, hX⟩ := hEA
  have hcard : Nat.card E = p ^ 3 := by rw [hEA]; exact h.A_card
  have hne : (reflectionSet p E).Nonempty := by
    by_contra hcon
    have hempty : reflectionSet p E = ∅ := Set.not_nonempty_iff_eq_empty.1 hcon
    have hbot : reflectionGroup p E = ⊥ := by
      unfold reflectionGroup
      rw [hempty, Subgroup.closure_empty]
    obtain ⟨h24, h48⟩ := not_dvd_weyl_order hp hp5
    have hcard1 : Nat.card (reflectionGroup p E) = 1 := by rw [hbot, Subgroup.card_bot]
    rcases hX with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
    · rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm] at hcard1
      simp [Nat.factorial] at hcard1
    · rw [Nat.card_congr e.toEquiv, Nat.card_prod, Nat.card_eq_fintype_card (α := Equiv.Perm (Fin 4)),
        Fintype.card_perm] at hcard1
      have : Nat.card (Multiplicative (ZMod 2)) = 2 := by
        rw [Nat.card_eq_fintype_card]
        decide
      rw [this] at hcard1
      simp [Nat.factorial] at hcard1
  have hgen := iSup_autMoved_eq hp5 hcard hX hne
  calc E = ⨆ (t : MulAut E) (_ : t ∈ reflectionSet p E), autMovedInG E t := hgen.symm
    _ ≤ lieGenerated p E := iSup₂_le fun t ht => hMoved G p A c L E h15 hF hout hnot t ht

end Sec1511

end CFSG.RankThree.PartOne
