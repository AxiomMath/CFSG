module

public import CFSG.Quasithin.AppendixH.H16.Vocab
public import CFSG.Quasithin.Background.B4ModelsAction
public import CFSG.Quasithin.Background.HF166B
public import CFSG.Quasithin.Background.HF1607M22B
public import CFSG.Quasithin.Background.HMathieuCode23
public import CFSG.Quasithin.Background.RonanH164Main
import CFSG.Quasithin.AppendixH.H16.Concl161
import CFSG.Quasithin.AppendixH.H16.H162Final
import CFSG.Quasithin.AppendixH.H16.H165FourGlue
import CFSG.Quasithin.AppendixH.H16.H165Glue
import CFSG.Quasithin.AppendixH.H16.H165One
import CFSG.Quasithin.AppendixH.H16.H165Three
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Milestones.ASVolI.H14

public section

open scoped Pointwise Matrix commutatorElement

namespace CFSG.ASVolI

open CFSG.Quasithin CFSG.ASVolI.ChH CFSG.Open CFSG.Monster.Code

open CFSG.Quasithin.H.Mathieu

theorem h16_pair_cases {a b : Fin 24} (hab : a ≠ b) {σ : Equiv.Perm (Fin 24)}
    (hσ : σ ∈ M2ab a b) : (σ a = a ∧ σ b = b) ∨ (σ a = b ∧ σ b = a) := by
  have hst : σ • ({a, b} : Finset (Fin 24)) = {a, b} :=
    MulAction.mem_stabilizer_iff.1 (Subgroup.mem_inf.1 hσ).2
  have ha : σ a ∈ ({a, b} : Finset (Fin 24)) := by
    have h' : σ • a ∈ σ • ({a, b} : Finset (Fin 24)) := Finset.smul_mem_smul_finset (by simp)
    rw [hst] at h'
    exact h'
  have hb : σ b ∈ ({a, b} : Finset (Fin 24)) := by
    have h' : σ • b ∈ σ • ({a, b} : Finset (Fin 24)) := Finset.smul_mem_smul_finset (by simp)
    rw [hst] at h'
    exact h'
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · exact absurd (σ.injective (ha.trans hb.symm)) hab
  · exact Or.inl ⟨ha, hb⟩
  · exact Or.inr ⟨ha, hb⟩
  · exact absurd (σ.injective (ha.trans hb.symm)) hab

theorem h16_preserves_pair {a b : Fin 24} {σ : Equiv.Perm (Fin 24)} (hσ : σ ∈ AutPerm)
    (hc : (σ a = a ∧ σ b = b) ∨ (σ a = b ∧ σ b = a)) :
    Preserves (golayC ⊓ pairKer a b) (Subgroup.zpowers (G6.allOnes 24)) σ := by
  have hpk : ∀ m ∈ pairKer a b, G6.permAct 24 σ m ∈ pairKer a b := by
    intro m hm
    rw [CFSG.Quasithin.H.Mathieu.mem_pairKer] at hm ⊢
    rw [G6.permAct_apply, G6.permAct_apply]
    rcases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [Equiv.Perm.inv_eq_iff_eq.2 h1.symm, Equiv.Perm.inv_eq_iff_eq.2 h2.symm]
      exact hm
    · rw [Equiv.Perm.inv_eq_iff_eq.2 h2.symm, Equiv.Perm.inv_eq_iff_eq.2 h1.symm, add_comm]
      exact hm
  refine ⟨fun m hm => Subgroup.mem_inf.2
    ⟨CFSG.Quasithin.golayC_inv hσ (Subgroup.mem_inf.1 hm).1, hpk m (Subgroup.mem_inf.1 hm).2⟩,
    fun _ hm => CFSG.Quasithin.H.Mathieu.permAct_mem_zpowers_allOnes σ hm⟩

theorem h16_conj_mem_stabPair {a b : Fin 24} {τ γ : Equiv.Perm (Fin 24)} (hτ0 : τ 0 = a)
    (hτ1 : τ 1 = b) (hγ : (γ a = a ∧ γ b = b) ∨ (γ a = b ∧ γ b = a)) :
    τ⁻¹ * γ * τ ∈ stabPair01 := by
  have ha : τ⁻¹ a = 0 := Equiv.Perm.inv_eq_iff_eq.2 hτ0.symm
  have hb : τ⁻¹ b = 1 := Equiv.Perm.inv_eq_iff_eq.2 hτ1.symm
  show ((τ⁻¹ * γ * τ) 0 = 0 ∧ (τ⁻¹ * γ * τ) 1 = 1) ∨ ((τ⁻¹ * γ * τ) 0 = 1 ∧ (τ⁻¹ * γ * τ) 1 = 0)
  simp only [Equiv.Perm.mul_apply, hτ0, hτ1]
  rcases hγ with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
    exact Or.inl ⟨ha, hb⟩
  · rw [h1, h2]
    exact Or.inr ⟨hb, ha⟩

theorem h16_conj_mem_stab0 {a : Fin 24} {τ γ : Equiv.Perm (Fin 24)} (hτ0 : τ 0 = a) (hγ : γ a = a) :
    τ⁻¹ * γ * τ ∈ MulAction.stabilizer (Equiv.Perm (Fin 24)) (0 : Fin 24) := by
  rw [MulAction.mem_stabilizer_iff]
  show (τ⁻¹ * γ * τ) 0 = 0
  simp only [Equiv.Perm.mul_apply, hτ0, hγ]
  exact Equiv.Perm.inv_eq_iff_eq.2 hτ0.symm

theorem h16_conj_mem_M22 {a b : Fin 24} (hab : a ≠ b) {σ k : Equiv.Perm (Fin 24)}
    (hσ : σ ∈ M2ab a b) (hk : k ∈ M22g a b) : σ * k * σ⁻¹ ∈ M22g a b := by
  have hk_a : k a = a := MulAction.mem_stabilizer_iff.1 (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hk).1).2
  have hk_b : k b = b := MulAction.mem_stabilizer_iff.1 (Subgroup.mem_inf.1 hk).2
  have hk24 : k ∈ M24g := (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hk).1).1
  have hσ24 : σ ∈ M24g := (Subgroup.mem_inf.1 hσ).1
  have hconj : σ * k * σ⁻¹ ∈ M24g :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hσ24 hk24) (Subgroup.inv_mem _ hσ24)
  have hA : (σ * k * σ⁻¹) a = a ∧ (σ * k * σ⁻¹) b = b := by
    rcases h16_pair_cases hab hσ with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have e1 : σ⁻¹ a = a := Equiv.Perm.inv_eq_iff_eq.2 h1.symm
      have e2 : σ⁻¹ b = b := Equiv.Perm.inv_eq_iff_eq.2 h2.symm
      exact ⟨by simp only [Equiv.Perm.mul_apply, e1, hk_a, h1],
        by simp only [Equiv.Perm.mul_apply, e2, hk_b, h2]⟩
    · have e1 : σ⁻¹ a = b := Equiv.Perm.inv_eq_iff_eq.2 h2.symm
      have e2 : σ⁻¹ b = a := Equiv.Perm.inv_eq_iff_eq.2 h1.symm
      exact ⟨by simp only [Equiv.Perm.mul_apply, e1, hk_b, h2],
        by simp only [Equiv.Perm.mul_apply, e2, hk_a, h1]⟩
  exact Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨hconj, MulAction.mem_stabilizer_iff.2 hA.1⟩,
    MulAction.mem_stabilizer_iff.2 hA.2⟩

theorem h16_faithful_of_coords {V : Type*} [CommGroup V] {numer denom : Subgroup (G6.PermMod 24)}
    {W : Type*} [CommGroup W] (c : SecCoords numer denom W)
    {Γ : Subgroup (Equiv.Perm (Fin 24))} (hΓ : ∀ σ ∈ Γ, Preserves numer denom σ)
    {H : Subgroup (MulAut V)} {π : (FFModel.golaySec Γ numer denom).Gam →* ↥H}
    {β : ↥(⊤ : Subgroup V) →* ↥numer ⧸ denom.subgroupOf numer}
    (h : RealizesBy (FFModel.golaySec Γ numer denom) H ⊤ ⊥ π β)
    (hc : ∀ γ : ↥Γ, c.rho Γ hΓ γ = 1 → γ = 1) :
    ∀ γ : ↥Γ, ((π γ : ↥H) : MulAut V) = 1 → γ = 1 := by
  obtain ⟨e, he⟩ := c.exists_equiv hΓ h
  intro γ hγ
  apply hc
  refine MulEquiv.ext (fun w => ?_)
  have hv := he γ (e.symm w)
  rw [hγ] at hv
  simp only [MulAut.one_apply, MulEquiv.apply_symm_apply] at hv
  simp only [MulAut.one_apply]
  exact hv.symm

theorem h16_finite_of_coords {V : Type*} [CommGroup V] {numer denom : Subgroup (G6.PermMod 24)}
    {W : Type*} [CommGroup W] [Finite W] (c : SecCoords numer denom W)
    {Γ : Subgroup (Equiv.Perm (Fin 24))} (hΓ : ∀ σ ∈ Γ, Preserves numer denom σ)
    {H : Subgroup (MulAut V)} {π : (FFModel.golaySec Γ numer denom).Gam →* ↥H}
    {β : ↥(⊤ : Subgroup V) →* ↥numer ⧸ denom.subgroupOf numer}
    (h : RealizesBy (FFModel.golaySec Γ numer denom) H ⊤ ⊥ π β) : Finite V := by
  obtain ⟨e, -⟩ := c.exists_equiv hΓ h
  exact Finite.of_equiv W e.symm.toEquiv

theorem h16_faithful24 {V : Type*} [CommGroup V] {ρ : ↥M24g →* MulAut V}
    (hinj : Function.Injective (rhoC11 AutPerm le_rfl)) {β : _}
    (h : RealizesBy (FFModel.golaySec M24g golayC (Subgroup.zpowers (G6.allOnes 24)))
      ρ.range ⊤ ⊥ ρ.rangeRestrict β) : Function.Injective ρ := by
  rw [injective_iff_map_eq_one]
  intro γ hγ
  refine h16_faithful_of_coords codeCoords (fun σ hσ => preserves_code hσ) h ?_ γ hγ
  intro γ' hγ'
  exact hinj (show rhoC11 AutPerm le_rfl γ' = rhoC11 AutPerm le_rfl 1 by
    rw [map_one]; exact hγ')

theorem h16_faithful23 {V : Type*} [CommGroup V] {a : Fin 24}
    (hτex : ∃ p ∈ AutPerm, p 0 = a) (hinj : Function.Injective (rhoC11 mog23 inf_le_left))
    {ρ : ↥(M23g a) →* MulAut V} {β : _}
    (h : RealizesBy (FFModel.golaySec (M23g a) golayC (Subgroup.zpowers (G6.allOnes 24)))
      ρ.range ⊤ ⊥ ρ.rangeRestrict β) : Function.Injective ρ := by
  obtain ⟨τ, hτ, hτ0⟩ := hτex
  have hn : ∀ m, m ∈ golayC ↔ G6.permAct 24 τ⁻¹ m ∈ golayC := (preserves_iff_of_mem hτ).2
  have hd := zpowers_allOnes_iff τ
  have hΓ : ∀ σ ∈ M23g a, Preserves golayC (Subgroup.zpowers (G6.allOnes 24)) σ :=
    fun σ hσ => preserves_code (Subgroup.mem_inf.1 hσ).1
  have hc : ∀ γ : ↥(M23g a), (codeCoords.conj τ hn hd).rho (M23g a) hΓ γ = 1 → γ = 1 := by
    intro γ hγ
    have hγa : (γ : Equiv.Perm (Fin 24)) a = a :=
      MulAction.mem_stabilizer_iff.1 (Subgroup.mem_inf.1 γ.2).2
    have hmem : τ⁻¹ * (γ : Equiv.Perm (Fin 24)) * τ ∈ mog23 :=
      Subgroup.mem_inf.2 ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hτ)
        (Subgroup.mem_inf.1 γ.2).1) hτ, h16_conj_mem_stab0 hτ0 hγa⟩
    have key := SecCoords.conj_rhoHom codeCoords τ hn hd (γ : Equiv.Perm (Fin 24))
    have hp : rhoC11 mog23 inf_le_left ⟨τ⁻¹ * (γ : Equiv.Perm (Fin 24)) * τ, hmem⟩ = 1 := by
      refine MulEquiv.ext (fun w => ?_)
      have h1 := congrArg (fun f : Multiplicative (Fin 11 → ZMod 2) →* Multiplicative (Fin 11 → ZMod 2) => f w) key
      have h2 : (codeCoords.conj τ hn hd).rho (M23g a) hΓ γ w = w := by
        rw [hγ, MulAut.one_apply]
      rw [MulAut.one_apply]
      exact h1.symm.trans h2
    have hp' : (⟨τ⁻¹ * (γ : Equiv.Perm (Fin 24)) * τ, hmem⟩ : ↥mog23) = 1 :=
      hinj (by rw [hp, map_one])
    have hp'' : τ⁻¹ * (γ : Equiv.Perm (Fin 24)) * τ = 1 := congrArg Subtype.val hp'
    have h3 : (γ : Equiv.Perm (Fin 24)) = 1 := by
      rw [show (γ : Equiv.Perm (Fin 24)) = τ * (τ⁻¹ * (γ : Equiv.Perm (Fin 24)) * τ) * τ⁻¹ by group, hp'']
      group
    exact Subtype.ext h3
  exact (injective_iff_map_eq_one ρ).2 fun γ hγ => h16_faithful_of_coords (codeCoords.conj τ hn hd) hΓ h hc γ hγ

theorem h16_faithful22 {V : Type*} [CommGroup V] {a b : Fin 24} (hab : a ≠ b)
    (hτex : ∃ p ∈ AutPerm, p 0 = a ∧ p 1 = b) (hinj : Function.Injective (rhoC10 mog22plus le_rfl))
    {Γ : Subgroup (Equiv.Perm (Fin 24))} (hle : Γ ≤ M2ab a b)
    {ρ : ↥Γ →* MulAut V} {β : _}
    (h : RealizesBy (FFModel.golaySec Γ (golayC ⊓ pairKer a b) (Subgroup.zpowers (G6.allOnes 24)))
      ρ.range ⊤ ⊥ ρ.rangeRestrict β) : Finite V ∧ Function.Injective ρ := by
  obtain ⟨τ, hτ, hτ0, hτ1⟩ := hτex
  have hn : ∀ m, m ∈ golayC ⊓ pairKer a b ↔ G6.permAct 24 τ⁻¹ m ∈ golayC ⊓ pairKer 0 1 := by
    intro m
    rw [Subgroup.mem_inf, Subgroup.mem_inf]
    refine and_congr ((preserves_iff_of_mem hτ).2 m) ?_
    rw [CFSG.Quasithin.H.Mathieu.mem_pairKer, CFSG.Quasithin.H.Mathieu.mem_pairKer,
      G6.permAct_apply, G6.permAct_apply, inv_inv, hτ0, hτ1]
  have hd := zpowers_allOnes_iff τ
  have hΓ : ∀ σ ∈ Γ, Preserves (golayC ⊓ pairKer a b) (Subgroup.zpowers (G6.allOnes 24)) σ :=
    fun σ hσ => h16_preserves_pair (Subgroup.mem_inf.1 (hle hσ)).1 (h16_pair_cases hab (hle hσ))
  have hc : ∀ γ : ↥Γ, (code22Coords.conj τ hn hd).rho Γ hΓ γ = 1 → γ = 1 := by
    intro γ hγ
    have hγM : (γ : Equiv.Perm (Fin 24)) ∈ M2ab a b := hle γ.2
    have hmem : τ⁻¹ * (γ : Equiv.Perm (Fin 24)) * τ ∈ mog22plus :=
      Subgroup.mem_inf.2 ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hτ)
        (Subgroup.mem_inf.1 hγM).1) hτ, h16_conj_mem_stabPair hτ0 hτ1 (h16_pair_cases hab hγM)⟩
    have hp : rhoC10 mog22plus le_rfl ⟨τ⁻¹ * (γ : Equiv.Perm (Fin 24)) * τ, hmem⟩ = 1 := by
      refine MulEquiv.ext (fun w => ?_)
      have h1 := congrArg (fun f : Multiplicative (Fin 10 → ZMod 2) →* Multiplicative (Fin 10 → ZMod 2) => f w)
        (SecCoords.conj_rhoHom code22Coords τ hn hd (γ : Equiv.Perm (Fin 24)))
      have h2 : (code22Coords.conj τ hn hd).rho Γ hΓ γ w = w := by
        rw [hγ, MulAut.one_apply]
      rw [MulAut.one_apply]
      exact h1.symm.trans h2
    have hp' : (⟨τ⁻¹ * (γ : Equiv.Perm (Fin 24)) * τ, hmem⟩ : ↥mog22plus) = 1 :=
      hinj (by rw [hp, map_one])
    have hp'' : τ⁻¹ * (γ : Equiv.Perm (Fin 24)) * τ = 1 := congrArg Subtype.val hp'
    have h3 : (γ : Equiv.Perm (Fin 24)) = 1 := by
      rw [show (γ : Equiv.Perm (Fin 24)) = τ * (τ⁻¹ * (γ : Equiv.Perm (Fin 24)) * τ) * τ⁻¹ by group, hp'']
      group
    exact Subtype.ext h3
  exact ⟨h16_finite_of_coords (code22Coords.conj τ hn hd) hΓ h,
    (injective_iff_map_eq_one ρ).2 fun γ hγ => h16_faithful_of_coords (code22Coords.conj τ hn hd) hΓ h hc γ hγ⟩

@[expose] def h16Restrict {V : Type*} [CommGroup V] {a b : Fin 24} {Γ : Subgroup (Equiv.Perm (Fin 24))}
    (ρ : ↥Γ →* MulAut V) (hK : M22g a b ≤ Γ) : Subgroup (MulAut V) :=
  (ρ.comp (Subgroup.inclusion hK)).range

theorem h16_mathieu24 {V : Type*} [CommGroup V] {ρ : ↥M24g →* MulAut V} {β : _}
    (h : RealizesBy (FFModel.golaySec M24g golayC (Subgroup.zpowers (G6.allOnes 24)))
      ρ.range ⊤ ⊥ ρ.rangeRestrict β) : CFSG.Quasithin.MathieuCode24 ρ.range ⊤ ⊥ :=
  (realizes_iff _ _ _ _).2 ⟨ρ.rangeRestrict, β, h⟩

theorem h16_mathieu23 {V : Type*} [CommGroup V] (a : Fin 24) {ρ : ↥(M23g a) →* MulAut V} {β : _}
    (h : RealizesBy (FFModel.golaySec (M23g a) golayC (Subgroup.zpowers (G6.allOnes 24)))
      ρ.range ⊤ ⊥ ρ.rangeRestrict β) : CFSG.Quasithin.MathieuCode23 ρ.range ⊤ ⊥ := by
  unfold CFSG.Quasithin.MathieuCode23
  exact ⟨a, (realizes_iff _ _ _ _).2 ⟨ρ.rangeRestrict, β, h⟩⟩

theorem h16_mathieu22 {V : Type*} [CommGroup V] {a b : Fin 24} (hab : a ≠ b)
    {Γ : Subgroup (Equiv.Perm (Fin 24))} (hK : M22g a b ≤ Γ) {ρ : ↥Γ →* MulAut V} {β : _}
    (h : RealizesBy (FFModel.golaySec Γ (golayC ⊓ pairKer a b) (Subgroup.zpowers (G6.allOnes 24)))
      ρ.range ⊤ ⊥ ρ.rangeRestrict β) : CFSG.Quasithin.MathieuCode22 (h16Restrict ρ hK) ⊤ ⊥ := by
  obtain ⟨-, -, h3, -, -, h6, h7, h8, h9, h10⟩ := h
  unfold CFSG.Quasithin.MathieuCode22
  refine ⟨a, b, hab, (realizes_iff _ _ _ _).2 ⟨(ρ.comp (Subgroup.inclusion hK)).rangeRestrict, β, ?_⟩⟩
  unfold CFSG.Quasithin.H.Mathieu.RealizesBy
  refine ⟨MonoidHom.rangeRestrict_surjective _, bot_le, h3, fun _ _ _ => Subgroup.mem_top _, ?_, ?_, ?_,
    h8, h9, ?_⟩
  · intro x z hz
    rw [Subgroup.mem_bot.1 hz, map_one]
    exact Subgroup.one_mem _
  · intro γ m hm
    exact h6 ⟨Subtype.val γ, hK (Subtype.property γ)⟩ m hm
  · intro γ m hm
    exact h7 ⟨Subtype.val γ, hK (Subtype.property γ)⟩ m hm
  · intro γ u m hu hm hβ
    exact h10 ⟨Subtype.val γ, hK (Subtype.property γ)⟩ u m hu hm hβ

theorem h16_isOver {V : Type*} [CommGroup V] {a b : Fin 24} (hab : a ≠ b)
    {Γ : Subgroup (Equiv.Perm (Fin 24))} (hK : M22g a b ≤ Γ) (hle : Γ ≤ M2ab a b)
    (ρ : ↥Γ →* MulAut V) : CFSG.Quasithin.H.Mathieu.IsOver (h16Restrict ρ hK) ρ.range := by
  unfold CFSG.Quasithin.H.Mathieu.IsOver
  refine ⟨?_, ?_⟩
  · rintro _ ⟨x, rfl⟩
    exact MonoidHom.mem_range.2 ⟨_, rfl⟩
  · rintro _ ⟨γ, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro g
    show _ ∈ h16Restrict ρ hK ↔ _ ∈ h16Restrict ρ hK
    constructor
    · rintro ⟨k, rfl⟩
      have hmem := h16_conj_mem_M22 hab (hle γ.2) k.2
      refine MonoidHom.mem_range.2 ⟨⟨(γ : Equiv.Perm (Fin 24)) * k * (γ : Equiv.Perm (Fin 24))⁻¹, hmem⟩, ?_⟩
      have e : (Subgroup.inclusion hK ⟨(γ : Equiv.Perm (Fin 24)) * k * (γ : Equiv.Perm (Fin 24))⁻¹, hmem⟩ : ↥Γ)
          = γ * Subgroup.inclusion hK k * γ⁻¹ := Subtype.ext rfl
      rw [MonoidHom.comp_apply, e, map_mul, map_mul, map_inv]
      rfl
    · rintro ⟨k, hk⟩
      have hmem : (γ : Equiv.Perm (Fin 24))⁻¹ * k * (γ : Equiv.Perm (Fin 24)) ∈ M22g a b := by
        have := h16_conj_mem_M22 hab (Subgroup.inv_mem _ (hle γ.2)) k.2
        rwa [inv_inv] at this
      refine MonoidHom.mem_range.2 ⟨⟨(γ : Equiv.Perm (Fin 24))⁻¹ * k * (γ : Equiv.Perm (Fin 24)), hmem⟩, ?_⟩
      have e : (Subgroup.inclusion hK ⟨(γ : Equiv.Perm (Fin 24))⁻¹ * k * (γ : Equiv.Perm (Fin 24)), hmem⟩ : ↥Γ)
          = γ⁻¹ * Subgroup.inclusion hK k * γ := Subtype.ext rfl
      rw [MonoidHom.comp_apply, e, map_mul, map_mul, map_inv]
      rw [MonoidHom.comp_apply] at hk
      rw [hk]
      group

theorem h16_isOver_self {V : Type*} [CommGroup V] {Γ : Subgroup (Equiv.Perm (Fin 24))}
    (ρ : ↥Γ →* MulAut V) : CFSG.Quasithin.H.Mathieu.IsOver ρ.range ρ.range := by
  unfold CFSG.Quasithin.H.Mathieu.IsOver
  exact ⟨le_rfl, Subgroup.le_normalizer⟩

theorem h16_rImg_le {V : Type*} [CommGroup V] {Γ : Subgroup (Equiv.Perm (Fin 24))}
    (ρ : ↥Γ →* MulAut V) {A : Subgroup (Equiv.Perm (Fin 24))} : rImg ρ A ≤ ρ.range := by
  intro y hy
  obtain ⟨x, -, rfl⟩ := Subgroup.mem_map.1 hy
  exact MonoidHom.mem_range.2 ⟨x, rfl⟩

theorem h16_rImg_card {V : Type*} [CommGroup V] {Γ : Subgroup (Equiv.Perm (Fin 24))}
    {ρ : ↥Γ →* MulAut V} (hρ : Function.Injective ρ) {A : Subgroup (Equiv.Perm (Fin 24))}
    (hA : A ≤ Γ) : Nat.card (rImg ρ A) = Nat.card A := by
  unfold rImg
  rw [Subgroup.card_map_of_injective hρ]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA).toEquiv

theorem h16_rImg_isElemAbelian2 {V : Type*} [CommGroup V] {Γ : Subgroup (Equiv.Perm (Fin 24))}
    (ρ : ↥Γ →* MulAut V) {A : Subgroup (Equiv.Perm (Fin 24))} (hA : A ≤ Γ)
    (hE : IsElemAbelian 2 A) : IsElemAbelian2 (rImg ρ A) := by
  unfold IsElemAbelian2
  refine ⟨?_, ?_⟩
  · intro y hy z hz
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hy
    obtain ⟨x', hx', rfl⟩ := Subgroup.mem_map.1 hz
    rw [← map_mul, ← map_mul]
    congr 1
    have hcomm : (x : Equiv.Perm (Fin 24)) * (x' : Equiv.Perm (Fin 24))
        = (x' : Equiv.Perm (Fin 24)) * (x : Equiv.Perm (Fin 24)) :=
      congrArg Subtype.val (hE.1.is_comm.comm
        ⟨(x : Equiv.Perm (Fin 24)), Subgroup.mem_subgroupOf.1 hx⟩
        ⟨(x' : Equiv.Perm (Fin 24)), Subgroup.mem_subgroupOf.1 hx'⟩)
    exact Subtype.ext hcomm
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hy
    rw [← map_pow]
    have h2 : (x : Equiv.Perm (Fin 24)) ^ 2 = 1 := hE.2 _ (Subgroup.mem_subgroupOf.1 hx)
    rw [show x ^ 2 = 1 from Subtype.ext (by simpa using h2), map_one]

theorem h16_rImg_sup {V : Type*} [CommGroup V] {Γ : Subgroup (Equiv.Perm (Fin 24))}
    (ρ : ↥Γ →* MulAut V) {A Y : Subgroup (Equiv.Perm (Fin 24))} (hA : A ≤ Γ) (hY : Y ≤ Γ) :
    rImg ρ (A ⊔ Y) = rImg ρ A ⊔ rImg ρ Y := by
  unfold rImg
  rw [Subgroup.subgroupOf_sup hA hY, Subgroup.map_sup]

theorem h16_subgroupOf_commutator {Γ A Y : Subgroup (Equiv.Perm (Fin 24))} (hA : A ≤ Γ)
    (hY : Y ≤ Γ) : ⁅A.subgroupOf Γ, Y.subgroupOf Γ⁆ = ⁅A, Y⁆.subgroupOf Γ := by
  have h1 : Subgroup.map Γ.subtype ⁅A.subgroupOf Γ, Y.subgroupOf Γ⁆ = ⁅A, Y⁆ := by
    rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.2 hA, inf_eq_left.2 hY]
  rw [← Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective Γ) ⁅A.subgroupOf Γ, Y.subgroupOf Γ⁆, h1]
  rfl

theorem h16_rImg_commutator {V : Type*} [CommGroup V] {Γ : Subgroup (Equiv.Perm (Fin 24))}
    (ρ : ↥Γ →* MulAut V) {A Y : Subgroup (Equiv.Perm (Fin 24))} (hA : A ≤ Γ) (hY : Y ≤ Γ) :
    ⁅rImg ρ A, rImg ρ Y⁆ = rImg ρ ⁅A, Y⁆ := by
  unfold rImg
  rw [← h16_subgroupOf_commutator hA hY, Subgroup.map_commutator]

@[expose] def H_16_1 : Prop :=
  AllMCtxAt true 24 fun _ _ _ _ S _ _ Γ V _ ρ _ =>
    ∃ V₁₀ : Subgroup V,
      (IsChiefFactorUnder (actsOnModule (rImg ρ (MY Γ S))) ⊥ (fixV (rImg ρ (KY Γ S))) ∧
        rk ↥(fixV (rImg ρ (KY Γ S))) = 4 ∧
        IsChiefFactorUnder (actsOnModule (rImg ρ (MY Γ S))) (fixV (rImg ρ (KY Γ S))) V₁₀ ∧
        IsChiefFactorUnder (actsOnModule (rImg ρ (MY Γ S))) V₁₀ ⊤ ∧
        V₁₀ = commV (rImg ρ (perfectCore (MY Γ S))) ∧ rkIdx V₁₀ = 1) ∧
      (∃ N : Subgroup S24, IsO23 (MY Γ S) N ∧
        (∃ π : ↥(MY Γ S) →* ↥(CFSG.Open.StatedSp 2 (ZMod 2)), Function.Surjective π ∧
          π.ker = N.subgroupOf (MY Γ S)) ∧
        (∀ g : ↥Γ, (g : S24) ∈ MY Γ S →
          ((∀ x ∈ fixV (rImg ρ (KY Γ S)), ρ g x = x) ↔ (g : S24) ∈ N)) ∧
        InducesOn (rImg ρ (MY Γ S)) (fixV (rImg ρ (KY Γ S))) ⊥
          (Multiplicative (Fin 2 ⊕ Fin 2 → ZMod 2))
          (natSubI (Fin 2 ⊕ Fin 2) (ZMod 2) (CFSG.Open.StatedSp 2 (ZMod 2)))) ∧
      FullTranspAxis (rImg ρ (MY Γ S)) (rImg ρ (KY Γ S)) (fixV (rImg ρ (KY Γ S))) V₁₀

section H16_1


theorem as_H_16_1 : H_16_1 := by
  intro a b O Tr S B T₀ Γ V _ ρ β hM
  have hΓ : Γ = M24g :=
    le_antisymm (by simpa [AutLd, Ld] using hM.le_Aut) (by simpa [Ld] using hM.L_le)
  subst hΓ
  have hreal : RealizesBy (FFModel.golaySec M24g golayC (Subgroup.zpowers (G6.allOnes 24)))
      ρ.range ⊤ ⊥ ρ.rangeRestrict β := hM.real
  obtain ⟨e, he⟩ := codeCoords.exists_equiv (fun σ hσ => preserves_code hσ) hreal
  exact H16.h161_of_coords ρ e he hM.cfg.sextet

end H16_1

@[expose] def H_16_2 : Prop :=
  AllMCtxAt true 24 fun _ _ O _ S _ T₀ Γ V _ ρ _ =>
    ∃ V₅ : Subgroup V,
      (IsChiefFactorUnder (actsOnModule (rImg ρ (MY Γ O))) ⊥ (fixV (rImg ρ (KY Γ O))) ∧
        rk ↥(fixV (rImg ρ (KY Γ O))) = 1 ∧
        IsChiefFactorUnder (actsOnModule (rImg ρ (MY Γ O))) (fixV (rImg ρ (KY Γ O))) V₅ ∧
        rk ↥V₅ = 5 ∧ IsChiefFactorUnder (actsOnModule (rImg ρ (MY Γ O))) V₅ ⊤) ∧
      (FullTranspCenter (rImg ρ (MY Γ O)) (rImg ρ (KY Γ O)) V₅ (fixV (rImg ρ (KY Γ O))) ∧
        IsDualOfConj ρ (MY Γ O) V₅ (fixV (rImg ρ (KY Γ O))) (KY Γ O)) ∧
      (∃ β' : V →* Multiplicative (Fin 6 → ZMod 2),
        InducesOnVia (rImg ρ (MY Γ O)) ⊤ V₅ (Multiplicative (Fin 6 → ZMod 2)) (omegaN 6 qPlus6)
          (β'.comp (⊤ : Subgroup V).subtype) ∧
        (∀ g : ↥Γ, (g : S24) ∈ MY Γ O → ((∀ x : V, ρ g x * x⁻¹ ∈ V₅) ↔ (g : S24) ∈ KY Γ O)) ∧
        rk ↥(fixV (rImg ρ (KY Γ S)) ⊔ V₅) = 6 ∧
        (∀ x ∈ fixV (rImg ρ (KY Γ S)) ⊔ V₅, qPlus6 (Multiplicative.toAdd (β' x)) = 0) ∧
        (fixV (rImg ρ (KY Γ S)) = fixV (rImg ρ (KY Γ O ⊓ KY Γ S))) ∧
        ∀ z : S24, IsCenterGen T₀ z →
          (rk ↥(fixV (rImg ρ (Subgroup.zpowers z)) ⊔ V₅) = 8 ∧
            ∀ x ∈ fixV (rImg ρ (Subgroup.zpowers z)) ⊔ V₅, qPlus6 (Multiplicative.toAdd (β' x)) = 0) ∧
          cenM ρ (fixV (rImg ρ (Subgroup.zpowers z))) = (Subgroup.zpowers z).subgroupOf Γ ∧
          (rk ↥(V₅ ⊓ fixV (rImg ρ (Subgroup.zpowers z))) = 4 ∧
            IsE2k 4 (cenMS ρ (V₅ ⊓ fixV (rImg ρ (Subgroup.zpowers z)))) ∧
            pCoreOf 2 (Γ ⊓ Subgroup.centralizer ({z} : Set S24)) =
              KY Γ O ⊔ cenMS ρ (V₅ ⊓ fixV (rImg ρ (Subgroup.zpowers z))) ∧
            ∀ element ∈ pCoreOf 2 (Γ ⊓ Subgroup.centralizer ({z} : Set S24)),
              ∃ kernelElement ∈ KY Γ O,
                ∃ centralizerElement ∈ cenMS ρ (V₅ ⊓ fixV (rImg ρ (Subgroup.zpowers z))),
                  element = kernelElement * centralizerElement) ∧
          (∀ B : Subgroup S24, z ∈ B → B ≤ cenMS ρ (V₅ ⊓ fixV (rImg ρ (Subgroup.zpowers z))) →
            rk ↥(fixV (rImg ρ B)) = 8 - rk ↥B) ∧
          (∀ g ∈ Γ ⊓ Subgroup.centralizer ({z} : Set S24),
            rk ↥(commOn (fixV (rImg ρ (Subgroup.zpowers z))) (rImg ρ (Subgroup.zpowers g))) = 1 →
              g ∈ pCoreOf 2 (Γ ⊓ Subgroup.centralizer ({z} : Set S24))))

section H16_2


theorem as_H_16_2 : H_16_2 := by
  intro a b O Tr S B T₀ Γ V _ ρ β hM
  have hΓ : Γ = M24g :=
    le_antisymm (by simpa [AutLd, Ld] using hM.le_Aut) (by simpa [Ld] using hM.L_le)
  subst hΓ
  have hreal : RealizesBy (FFModel.golaySec M24g golayC (Subgroup.zpowers (G6.allOnes 24)))
      ρ.range ⊤ ⊥ ρ.rangeRestrict β := hM.real
  obtain ⟨e, he⟩ := codeCoords.exists_equiv (fun σ hσ => preserves_code hσ) hreal
  exact H16.h162_of_coords ρ e he hM.cfg

end H16_2

@[expose] def H_16_3 : Prop :=
  AllMCtxAt true 22 fun a b _ _ S B _ Γ V _ ρ _ =>
    Γ = M2ab a b →
      (∃ V₈ V₉ : Subgroup V,
        Chain163 ρ (S.erase B) V₈ V₉ ∧
        FullTranspAxis (rImg ρ (MY Γ (S.erase B))) (rImg ρ (KY Γ (S.erase B)))
          (fixV (rImg ρ (KY Γ (S.erase B)))) V₉) ∧
      InducesOnSub (rImg ρ (MY Γ (S.erase B))) (fixV (rImg ρ (KY Γ (S.erase B)))) ⊥ (G6.PermMod 5)
        (G6.coreMod 5) (G6.permAct 5).range ∧
      (cenM ρ (fixV (rImg ρ (KY Γ (S.erase B)))) = (KY Γ (S.erase B)).subgroupOf Γ ∧
        IsPGroup 2 ↥(KY Γ (S.erase B)))

section H16_3


theorem as_H_16_3 : H_16_3 := by
  intro a b O Tr S B T₀ Γ V _ ρ β hM hΓ
  have hreal : RealizesBy (FFModel.golaySec Γ (golayC ⊓ pairKer a b) (Subgroup.zpowers (G6.allOnes 24)))
      ρ.range ⊤ ⊥ ρ.rangeRestrict β := hM.real
  have hL : M22g a b ≤ Γ := by simpa [Ld] using hM.L_le
  exact CFSG.Quasithin.RonanH163.main163 hM.cfg.ne hM.cfg.octad.1 hM.cfg.a_O hM.cfg.b_O hM.cfg.sextet
    hM.cfg.B_mem hM.cfg.a_B hM.cfg.b_B hM.cfg.stab_O hM.cfg.stab_S hL hM.sylow hreal hΓ

end H16_3

@[expose] def H_16_4 : Prop :=
  AllMCtxAt true 22 fun a b O _ S B _ Γ V _ ρ _ =>
    Γ = M2ab a b →
      ∃ V₅ V₆ : Subgroup V,
        Chain164 ρ ((O.erase a).erase b) V₅ V₆ ∧
        (FullTranspCenter (rImg ρ (MY Γ ((O.erase a).erase b))) (rImg ρ (KY Γ ((O.erase a).erase b))) V₅
            (fixV (rImg ρ (KY Γ ((O.erase a).erase b)))) ∧
          IsDualOfConj ρ (MY Γ ((O.erase a).erase b)) V₅ (fixV (rImg ρ (KY Γ ((O.erase a).erase b))))
            (KY Γ ((O.erase a).erase b))) ∧
        ((∃ π : ↥(MY Γ ((O.erase a).erase b)) →* Equiv.Perm (Fin 6), Function.Surjective π ∧
            π.ker = (KY Γ ((O.erase a).erase b)).subgroupOf (MY Γ ((O.erase a).erase b))) ∧
          InducesOnSub (rImg ρ (MY Γ ((O.erase a).erase b))) ⊤ V₅ (G6.PermMod 6) (G6.coreMod 6)
            (G6.permAct 6).range) ∧
        ((∃ V₈ V₉ : Subgroup V, Chain163 ρ (S.erase B) V₈ V₉ ∧
            V₅ ≤ V₉ ∧ ¬ V₅ ≤ fixV (rImg ρ (KY Γ (S.erase B)))) ∧
          (∀ V₈ V₉ : Subgroup V, Chain163 ρ (S.erase B) V₈ V₉ →
            V₅ ≤ V₉ ∧ ¬ V₅ ≤ fixV (rImg ρ (KY Γ (S.erase B))))) ∧
        (∀ x : V, x ∈ V₅ ↔ ∀ g ∈ rImg ρ (KY Γ ((O.erase a).erase b)),
          g x * x⁻¹ ∈ fixV (rImg ρ (KY Γ ((O.erase a).erase b))))

section H16_4


theorem as_H_16_4 : H_16_4 := by
  intro a b O Tr S B T₀ Γ V _ ρ β hM hΓ
  have hreal : RealizesBy (FFModel.golaySec Γ (golayC ⊓ pairKer a b) (Subgroup.zpowers (G6.allOnes 24)))
      ρ.range ⊤ ⊥ ρ.rangeRestrict β := hM.real
  have hL : M22g a b ≤ Γ := by simpa [Ld] using hM.L_le
  exact CFSG.Quasithin.RonanH163.main164 hM.cfg.ne hM.cfg.octad.1 hM.cfg.a_O hM.cfg.b_O hM.cfg.sextet
    hM.cfg.B_mem hM.cfg.a_B hM.cfg.b_B hM.cfg.stab_O hM.cfg.stab_S hL hM.sylow hreal hΓ

end H16_4

@[expose] def H_16_5 : Prop :=
  (AllMCtxAt true 24 fun _ _ _ _ S _ _ Γ _ _ ρ _ =>
    H.IsFOneOffender ρ.range (rImg ρ (KY Γ S)) ∧
    ∀ A : Subgroup S24, A ≤ Γ → H.IsFOneOffender ρ.range (rImg ρ A) →
      ∃ g ∈ Γ, conjSubg g A = KY Γ S) ∧
  (AllMCtxAt true 23 fun _ _ _ _ _ _ _ Γ _ _ ρ _ =>
    ∀ A : Subgroup S24, A ≤ Γ → ¬ H.IsFOneOffender ρ.range (rImg ρ A)) ∧
  (AllMCtxAt true 22 fun a b _ _ S B _ Γ _ _ ρ _ =>
    Γ = M2ab a b →
      H.IsFOneOffender ρ.range (rImg ρ (KY Γ (S.erase B))) ∧
      ∀ A : Subgroup S24, A ≤ Γ → H.IsFOneOffender ρ.range (rImg ρ A) →
        ∃ g ∈ Γ, conjSubg g A = KY Γ (S.erase B)) ∧
  (AllMCtxAt true 22 fun a b _ _ _ _ _ Γ _ _ ρ _ =>
    Γ = M2ab a b → ∀ z ∈ Γ, orderOf z = 2 → IsTwoCentralElt Γ z →
      cenMS ρ (fixV (rImg ρ (Subgroup.zpowers z))) =
          Γ ⊓ Subgroup.centralizer ((twoResidual (Γ ⊓ Subgroup.centralizer ({z} : Set S24)) :
            Subgroup S24) : Set S24) ∧
      IsE2k 2 (cenMS ρ (fixV (rImg ρ (Subgroup.zpowers z)))))

section H165One

open CFSG.ASVolI.H16


private theorem h16_5_clause_one :
    AllMCtxAt true 24 fun _ _ _ _ S _ _ Γ _ _ ρ _ =>
      H.IsFOneOffender ρ.range (rImg ρ (KY Γ S)) ∧
      ∀ A : Subgroup S24, A ≤ Γ → H.IsFOneOffender ρ.range (rImg ρ A) →
        ∃ g ∈ Γ, conjSubg g A = KY Γ S := by
  intro a b O Tr S B T₀ Γ V _ ρ β hM
  have hΓ : Γ = M24g :=
    le_antisymm (by simpa [AutLd, Ld] using hM.le_Aut) (by simpa [Ld] using hM.L_le)
  subst hΓ
  have hreal : RealizesBy (FFModel.golaySec M24g golayC (Subgroup.zpowers (G6.allOnes 24)))
      ρ.range ⊤ ⊥ ρ.rangeRestrict β := hM.real
  have hinj : Function.Injective ρ := h16_faithful24 (rhoC11_injective AutPerm le_rfl) hreal
  haveI : Finite V := h16_finite_of_coords codeCoords (fun σ hσ => preserves_code hσ) hreal
  have hLM : CFSG.Quasithin.H.Mathieu.IsOver ρ.range ρ.range := h16_isOver_self ρ
  have hMC : CFSG.Quasithin.MathieuCode24 ρ.range ⊤ ⊥ := h16_mathieu24 hreal
  obtain ⟨hKc, hKe⟩ := KY_sextet_facts hM.cfg.sextet
  have hKle : KY M24g S ≤ M24g := KY_le M24g S
  obtain ⟨V₁₀, ⟨-, hfix4, -⟩, -⟩ := as_H_16_1 a b O Tr S B T₀ M24g V ρ β hM
  have hKcard : Nat.card (rImg ρ (KY M24g S)) = 2 ^ 6 := (h16_rImg_card hinj hKle).trans hKc
  have hoff : H.IsFOneOffender ρ.range (rImg ρ (KY M24g S)) := by
    refine ⟨⟨h16_rImg_le ρ, ?_, h16_rImg_isElemAbelian2 ρ hKle hKe⟩, ?_⟩
    · intro h
      rw [h, Subgroup.card_bot] at hKcard
      norm_num at hKcard
    · have h1 := rk_add_rkIdx (fixV (rImg ρ (KY M24g S)))
      have hV : rk V = 11 := by
        unfold rk
        rw [code24_card hMC, padicValNat.prime_pow]
      have hA : rk ↥(rImg ρ (KY M24g S)) = 6 := by
        unfold rk
        rw [hKcard, padicValNat.prime_pow]
      omega
  refine ⟨hoff, fun A hAΓ hAoff => ?_⟩
  obtain ⟨c, hc, hcA⟩ := h165_one hLM hMC hAoff hoff
  obtain ⟨g, rfl⟩ := MonoidHom.mem_range.1 hc
  refine ⟨(g : S24), g.2, ?_⟩
  apply eq_of_rImg_eq hinj (conjSubg_le_of_mem g.2 hAΓ) hKle
  rw [rImg_conjSubg, hcA]

end H165One

section H165Two


private theorem h16_5_clause_two :
    AllMCtxAt true 23 fun _ _ _ _ _ _ _ Γ _ _ ρ _ =>
      ∀ A : Subgroup S24, A ≤ Γ → ¬ H.IsFOneOffender ρ.range (rImg ρ A) := by
  intro a b O Tr S B T₀ Γ V _ ρ β hM A hA hoff
  have hΓ : Γ = M23g a :=
    le_antisymm (by simpa [AutLd, Ld] using hM.le_Aut) (by simpa [Ld] using hM.L_le)
  subst hΓ
  have hreal : RealizesBy (FFModel.golaySec (M23g a) golayC (Subgroup.zpowers (G6.allOnes 24)))
      ρ.range ⊤ ⊥ ρ.rangeRestrict β := hM.real
  haveI : Finite V :=
    h16_finite_of_coords codeCoords (fun σ hσ => preserves_code (Subgroup.mem_inf.1 hσ).1) hreal
  exact code23_not_isFOneModule (h16_isOver_self ρ) (h16_mathieu23 a hreal) ⟨_, hoff⟩

end H165Two

section H165Three

open CFSG.ASVolI.H16


private theorem h16_5_clause_three :
    AllMCtxAt true 22 fun a b _ _ S B _ Γ _ _ ρ _ =>
      Γ = M2ab a b →
        H.IsFOneOffender ρ.range (rImg ρ (KY Γ (S.erase B))) ∧
        ∀ A : Subgroup S24, A ≤ Γ → H.IsFOneOffender ρ.range (rImg ρ A) →
          ∃ g ∈ Γ, conjSubg g A = KY Γ (S.erase B) := by
  intro a b O Tr S B T₀ Γ V _ ρ β hM hΓ
  have hab : a ≠ b := hM.cfg.ne
  have hK : M22g a b ≤ Γ := by simpa [Ld] using hM.L_le
  have hle : Γ ≤ M2ab a b := by simpa [AutLd] using hM.le_Aut
  have hreal : RealizesBy (FFModel.golaySec Γ (golayC ⊓ pairKer a b)
      (Subgroup.zpowers (G6.allOnes 24))) ρ.range ⊤ ⊥ ρ.rangeRestrict β := hM.real
  obtain ⟨hfin, hinj⟩ := h16_faithful22 hab (CFSG.Monster.B.TwoA.autPerm_maps_two a b hab)
    rhoC10_mog22plus_injective hle hreal
  haveI := hfin
  have hMC := h16_mathieu22 hab hK hreal
  have hLM := h16_isOver hab hK hle ρ
  have hne : Γ ≠ M22g a b := by
    intro h
    obtain ⟨p, hp, hp0, hp1⟩ := CFSG.Monster.B.TwoA.autPerm_maps_two a b hab
    have hM01 : M2ab 0 1 = mog22plus := CFSG.Quasithin.RonanH143.M2ab_zero_one
    have hconj : conjSubg p (M2ab 0 1) = M2ab a b := by
      have h := CFSG.Quasithin.RonanH143.M2ab_conj hp 0 1
      rw [hp0, hp1] at h
      exact h
    have hmem : p * CFSG.Quasithin.RonanH143.ePerm * p⁻¹ ∈ M2ab a b := by
      rw [← hconj, mem_conjSubg_iff]
      have e : p⁻¹ * (p * CFSG.Quasithin.RonanH143.ePerm * p⁻¹) * p =
          CFSG.Quasithin.RonanH143.ePerm := by group
      rw [e, hM01]
      exact CFSG.Quasithin.RonanH143.ePerm_mem_mog22plus
    rw [← hΓ, h] at hmem
    have ha : (p * CFSG.Quasithin.RonanH143.ePerm * p⁻¹) a = a :=
      MulAction.mem_stabilizer_iff.1 (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hmem).1).2
    have hp0' : p⁻¹ a = 0 := Equiv.Perm.inv_eq_iff_eq.2 hp0.symm
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hp0', CFSG.Quasithin.RonanH163.ePerm_zero,
      hp1] at ha
    exact hab ha.symm
  have h143 := as_H_14_3 a b O Tr S B T₀ hM.cfg Γ hK hle hM.sylow
  have h1c := h143.1.2.2 hne
  have hKQ := (h1c (KY Γ (S.erase B))).2 rfl
  have hKle : KY Γ (S.erase B) ≤ Γ := KY_le Γ _
  obtain ⟨⟨V₈, V₉, ⟨-, hfix4, -⟩, -⟩, -⟩ := as_H_16_3 a b O Tr S B T₀ Γ V ρ β hM hΓ
  have hKcard : Nat.card (rImg ρ (KY Γ (S.erase B))) = 2 ^ 5 :=
    (h16_rImg_card hinj hKle).trans hKQ.2.2
  have hoff : H.IsFOneOffender ρ.range (rImg ρ (KY Γ (S.erase B))) := by
    refine ⟨⟨h16_rImg_le ρ, ?_, h16_rImg_isElemAbelian2 ρ hKle hKQ.2.1⟩, ?_⟩
    · intro h
      rw [h, Subgroup.card_bot] at hKcard
      norm_num at hKcard
    · have h1 := rk_add_rkIdx (fixV (rImg ρ (KY Γ (S.erase B))))
      have hV : rk V = 10 := by
        unfold rk
        rw [code22_card hMC, padicValNat.prime_pow]
      have hA : rk ↥(rImg ρ (KY Γ (S.erase B))) = 5 := by
        unfold rk
        rw [hKcard, padicValNat.prime_pow]
      omega
  refine ⟨hoff, fun A hAΓ hAoff => ?_⟩
  have hcard := h165_offender22_card hLM hMC hAoff
  have hAcard : Nat.card A = 2 ^ 5 := (h16_rImg_card hinj hAΓ).symm.trans hcard
  have hAe : IsElemAbelian 2 A := isElemAbelian_of_rImg hinj hAΓ hAoff.1.2.2
  obtain ⟨g, hg, hgA⟩ :=
    exists_conj_le_of_isSylowIn_glue hM.sylow hAΓ (isPGroup_of_isElemAbelian hAe)
  exact ⟨g, hg, (h1c _).1 ⟨hgA, isElemAbelian_conjSubg hAe g,
    (h165_card_conjSubg g A).trans hAcard⟩⟩

end H165Three

section H165Four

open CFSG.ASVolI.H16


private theorem h16_5_clause_four :
    AllMCtxAt true 22 fun a b _ _ _ _ _ Γ _ _ ρ _ =>
      Γ = M2ab a b → ∀ z ∈ Γ, orderOf z = 2 → IsTwoCentralElt Γ z →
        cenMS ρ (fixV (rImg ρ (Subgroup.zpowers z))) =
            Γ ⊓ Subgroup.centralizer ((twoResidual (Γ ⊓ Subgroup.centralizer ({z} : Set S24)) :
              Subgroup S24) : Set S24) ∧
        IsE2k 2 (cenMS ρ (fixV (rImg ρ (Subgroup.zpowers z)))) := by
  intro a b O Tr S B T₀ Γ V _ ρ β hM hΓ z hz hz2 hzc
  have hreal : RealizesBy (FFModel.golaySec Γ (golayC ⊓ pairKer a b)
      (Subgroup.zpowers (G6.allOnes 24))) ρ.range ⊤ ⊥ ρ.rangeRestrict β := hM.real
  have hL : M22g a b ≤ Γ := by simpa [Ld] using hM.L_le
  exact main165_four hM.cfg.ne hM.cfg.octad.1 hM.cfg.a_O hM.cfg.b_O hM.cfg.sextet
    hM.cfg.B_mem hM.cfg.a_B hM.cfg.b_B hM.cfg.stab_O hM.cfg.stab_S hL hM.sylow hreal hΓ hz hz2 hzc

end H165Four

section H165


theorem as_H_16_5 : H_16_5 :=
  And.intro h16_5_clause_one <| And.intro h16_5_clause_two <|
    And.intro h16_5_clause_three h16_5_clause_four

end H165

@[expose] def H_16_6 : Prop :=
  AllMCtxAt true 24 fun _ _ _ _ _ _ _ Γ _ _ ρ _ =>
    ∀ Y : Subgroup S24, Y ≤ Γ → Nat.card ↥Y = 3 → rkIdx (fixV (rImg ρ Y)) = 6 →
      cenMS ρ (fixV (rImg ρ Y)) = Y

section H16_6


theorem as_H_16_6 : H_16_6 := by
  intro a b O Tr S B T₀ Γ V _ ρ β hM Y hY hY3 hY6
  have hΓ : Γ = M24g :=
    le_antisymm (by simpa [AutLd, Ld] using hM.le_Aut) (by simpa [Ld] using hM.L_le)
  subst hΓ
  have hreal : RealizesBy (FFModel.golaySec M24g golayC (Subgroup.zpowers (G6.allOnes 24)))
      ρ.range ⊤ ⊥ ρ.rangeRestrict β := hM.real
  have hinj : Function.Injective ρ := h16_faithful24 (rhoC11_injective AutPerm le_rfl) hreal
  haveI : Finite V := h16_finite_of_coords codeCoords (fun σ hσ => preserves_code hσ) hreal
  have hLM : CFSG.Quasithin.H.Mathieu.IsOver ρ.range ρ.range := h16_isOver_self ρ
  have hMC : CFSG.Quasithin.MathieuCode24 ρ.range ⊤ ⊥ := h16_mathieu24 hreal
  have hYc : Nat.card (rImg ρ Y) = 3 := (h16_rImg_card hinj hY).trans hY3
  have key := code24_h1606 hLM hMC (h16_rImg_le ρ) hYc hY6
  unfold cenMS cenM
  ext g
  constructor
  · intro hg
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hg
    have hmem : ρ x ∈ rImg ρ Y := by
      rw [← key]
      exact Subgroup.mem_inf.2 ⟨MonoidHom.mem_range.2 ⟨x, rfl⟩, hx⟩
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 hmem
    rw [hinj hyx] at hy
    exact Subgroup.mem_subgroupOf.1 hy
  · intro hg
    have hmem : ρ ⟨g, hY hg⟩ ∈ ρ.range ⊓ centSub (fixV (rImg ρ Y)) := by
      rw [key]
      exact Subgroup.mem_map.2 ⟨⟨g, hY hg⟩, Subgroup.mem_subgroupOf.2 hg, rfl⟩
    exact Subgroup.mem_map.2 ⟨⟨g, hY hg⟩, (Subgroup.mem_inf.1 hmem).2, rfl⟩

end H16_6

@[expose] def H_16_7 : Prop :=
  AllMCtx true (fun d => d = 22 ∨ d = 24) fun _ _ _ _ _ _ _ _ Γ _ _ ρ _ =>
    ∀ s : ℕ, (s = 2 ∨ s = 3) → ∀ A Y : Subgroup S24, A ≤ Γ → Y ≤ Γ → IsE2k (2 * s) A →
      Nat.card ↥Y = 3 → Y ≤ Subgroup.normalizer (A : Set S24) → ⁅A, Y⁆ = A →
        rkIdx (fixV (rImg ρ (A ⊔ Y))) ≠ 2 * (s + 1)

section H16_7


theorem as_H_16_7 : H_16_7 := by
  intro d hd a b O Tr S B T₀ Γ V _ ρ β hM s hs A Y hA hY hAE hYc _ hAY
  rcases hd with rfl | rfl
  ·
    have hab : a ≠ b := hM.cfg.ne
    have hK : M22g a b ≤ Γ := by simpa [Ld] using hM.L_le
    have hle : Γ ≤ M2ab a b := by simpa [AutLd] using hM.le_Aut
    have hreal : RealizesBy (FFModel.golaySec Γ (golayC ⊓ pairKer a b) (Subgroup.zpowers (G6.allOnes 24)))
        ρ.range ⊤ ⊥ ρ.rangeRestrict β := hM.real
    obtain ⟨hfin, hinj⟩ := h16_faithful22 hab (CFSG.Monster.B.TwoA.autPerm_maps_two a b hab)
      rhoC10_mog22plus_injective hle hreal
    haveI := hfin
    have hMC := h16_mathieu22 hab hK hreal
    have hLM := h16_isOver hab hK hle ρ
    obtain ⟨hAE1, hAE2⟩ := hAE
    have hAe := h16_rImg_isElemAbelian2 ρ hA hAE1
    have hAc : Nat.card (rImg ρ A) = 2 ^ (2 * s) := by
      rw [h16_rImg_card hinj hA, hAE2]
    have hYc' : Nat.card (rImg ρ Y) = 3 := by
      rw [h16_rImg_card hinj hY, hYc]
    have key := code22_h1607 hLM hMC hs (h16_rImg_le ρ) (h16_rImg_le ρ) hAe hAc hYc'
    rw [h16_rImg_sup ρ hA hY]
    exact key
  ·
    have hΓ : Γ = M24g :=
      le_antisymm (by simpa [AutLd, Ld] using hM.le_Aut) (by simpa [Ld] using hM.L_le)
    subst hΓ
    have hreal : RealizesBy (FFModel.golaySec M24g golayC (Subgroup.zpowers (G6.allOnes 24)))
        ρ.range ⊤ ⊥ ρ.rangeRestrict β := hM.real
    have hinj : Function.Injective ρ := h16_faithful24 (rhoC11_injective AutPerm le_rfl) hreal
    haveI : Finite V := h16_finite_of_coords codeCoords (fun σ hσ => preserves_code hσ) hreal
    have hLM : CFSG.Quasithin.H.Mathieu.IsOver ρ.range ρ.range := h16_isOver_self ρ
    have hMC : CFSG.Quasithin.MathieuCode24 ρ.range ⊤ ⊥ := h16_mathieu24 hreal
    obtain ⟨hAE1, hAE2⟩ := hAE
    have hAe := h16_rImg_isElemAbelian2 ρ hA hAE1
    have hAc : Nat.card (rImg ρ A) = 2 ^ (2 * s) := by
      rw [h16_rImg_card hinj hA, hAE2]
    have hYc' : Nat.card (rImg ρ Y) = 3 := by
      rw [h16_rImg_card hinj hY, hYc]
    have hAY' : ⁅rImg ρ A, rImg ρ Y⁆ = rImg ρ A := by
      rw [h16_rImg_commutator ρ hA hY, hAY]
    have key := code24_h1607 hLM hMC hs (h16_rImg_le ρ) hAe hAc hYc' hAY'
    rw [h16_rImg_sup ρ hA hY]
    exact key

end H16_7

@[expose] def H_16_8 : Prop :=
  AllMCtxAt true 23 fun _ _ _ _ _ _ T₀ Γ _ _ ρ _ =>
    ∀ A : Subgroup S24, A ≤ T₀ ⊓ Γ → IsE2k 4 A → rkIdx (xiSub (rImg ρ A)) ≤ 1

section H16_8


theorem as_H_16_8 : H_16_8 := by
  intro a b O Tr S B T₀ Γ V _ ρ β hM A hA hE
  obtain ⟨hE1, hE2⟩ := hE
  have hΓ : Γ = M23g a :=
    le_antisymm (by simpa [AutLd, Ld] using hM.le_Aut) (by simpa [Ld] using hM.L_le)
  subst hΓ
  have hreal : RealizesBy (FFModel.golaySec (M23g a) golayC (Subgroup.zpowers (G6.allOnes 24)))
      ρ.range ⊤ ⊥ ρ.rangeRestrict β := hM.real
  have hne : a ≠ a + 1 := by
    intro h
    have := congrArg Fin.val h
    simp [Fin.val_add] at this
    omega
  have hτex : ∃ p ∈ AutPerm, p 0 = a := by
    obtain ⟨p, hp, h0, -⟩ := CFSG.Monster.B.TwoA.autPerm_maps_two a (a + 1) hne
    exact ⟨p, hp, h0⟩
  have hinj : Function.Injective ρ :=
    h16_faithful23 hτex (rhoC11_injective mog23 inf_le_left) hreal
  have hA' : A ≤ M23g a := hA.trans inf_le_right
  have hcard : Nat.card (rImg ρ A) = 16 := by
    rw [h16_rImg_card hinj hA', hE2]
    norm_num
  have hAe := h16_rImg_isElemAbelian2 ρ hA' hE1
  have hLM : CFSG.Quasithin.H.Mathieu.IsOver ρ.range ρ.range := h16_isOver_self ρ
  have hMC : CFSG.Quasithin.MathieuCode23 ρ.range ⊤ ⊥ := h16_mathieu23 a hreal
  exact code23_xi hLM hMC (h16_rImg_le ρ) hAe hcard

end H16_8

end CFSG.ASVolI
