module

public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelSpNsSylv
public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordShapeAlign
public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelSLCompParts

public section

open Polynomial Module Multiplicative
open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Symplectic
open CFSG.RankThree.Classical (spForm spLin spLin_injective)

namespace CFSG.StandardType

namespace CoordSpNs

section FrameEnd

variable {F : Type} [Field F] {n : ℕ} {D : Type} [AddCommGroup D] [Module F D] {s : ℕ}
  {κ : Type} (Φ : ((Fin s → D) × (κ → F)) ≃ₗ[F] (Fin n ⊕ Fin n → F))

@[expose] noncomputable def frameEnd (Y : StatedSp n F) : Module.End F ((Fin s → D) × (κ → F)) :=
  Φ.symm.toLinearMap ∘ₗ
    ((spLin n F Y : LinearMap.GeneralLinearGroup F (Fin n ⊕ Fin n → F)) :
      Module.End F (Fin n ⊕ Fin n → F)) ∘ₗ Φ.toLinearMap

theorem frameEnd_apply (Y : StatedSp n F) (x : (Fin s → D) × (κ → F)) :
    frameEnd Φ Y x = Φ.symm (((spLin n F Y : LinearMap.GeneralLinearGroup F
      (Fin n ⊕ Fin n → F)) : Module.End F (Fin n ⊕ Fin n → F)) (Φ x)) := rfl

theorem frameEnd_mul (Y Z : StatedSp n F) (x : (Fin s → D) × (κ → F)) :
    frameEnd Φ (Y * Z) x = frameEnd Φ Y (frameEnd Φ Z x) := by
  rw [frameEnd_apply, frameEnd_apply, frameEnd_apply, LinearEquiv.apply_symm_apply, map_mul]
  rfl

theorem frameEnd_one (x : (Fin s → D) × (κ → F)) : frameEnd Φ (1 : StatedSp n F) x = x := by
  rw [frameEnd_apply, map_one]
  exact Φ.symm_apply_apply x

theorem frameEnd_inv_apply (Y : StatedSp n F) (x : (Fin s → D) × (κ → F)) :
    frameEnd Φ Y⁻¹ (frameEnd Φ Y x) = x := by
  rw [← frameEnd_mul, inv_mul_cancel, frameEnd_one]

theorem frameEnd_apply_inv (Y : StatedSp n F) (x : (Fin s → D) × (κ → F)) :
    frameEnd Φ Y (frameEnd Φ Y⁻¹ x) = x := by
  rw [← frameEnd_mul, mul_inv_cancel, frameEnd_one]

theorem eq_one_of_frameEnd (Y : StatedSp n F) (h : ∀ x, frameEnd Φ Y x = x) : Y = 1 := by
  apply spLin_injective
  refine Units.ext (LinearMap.ext fun v => ?_)
  obtain ⟨x, rfl⟩ := Φ.surjective v
  have h1 := congrArg Φ (h x)
  rw [frameEnd_apply, LinearEquiv.apply_symm_apply] at h1
  rw [map_one]
  exact h1

end FrameEnd

section Torus

variable {G : Type} [Group G] {F : Type} [Field F] {n p : ℕ} [NeZero p] {D : Type}
  [AddCommGroup D] [Module F D] {s : ℕ} {κ : Type} {c : D ≃ₗ[F] D} (hc : c ^ p = 1)
  {Φ : ((Fin s → D) × (κ → F)) ≃ₗ[F] (Fin n ⊕ Fin n → F)} {ω : LinearMap.BilinForm F D}
  (hdec : ∀ d d' w w', spForm n F (Φ (d, w)) (Φ (d', w')) =
    ∑ i, ω (d i) (d' i) + spForm n F (Φ (0, w)) (Φ (0, w')))
  (hcω : ∀ x y, ω (c x) (c y) = ω x y)

@[expose] noncomputable def torElt (t : Fin s → ZMod p) : StatedSp n F :=
  (spIso n F).symm (torHomD hc hdec hcω (ofAdd t))

theorem nsCoord_eq_torElt (ψ : StatedSp n F →* G) (t : Fin s → ZMod p) :
    nsCoord ψ hc hdec hcω (ofAdd t) = ψ (torElt hc hdec hcω t) := rfl

theorem frameEnd_torElt (t : Fin s → ZMod p) (x : (Fin s → D) × (κ → F)) :
    frameEnd Φ (torElt hc hdec hcω t) x = torD c t x := by
  rw [frameEnd_apply, ← coe_spIso, torElt, MulEquiv.apply_symm_apply, coe_torHomD,
    SpNS.frameUnit_apply, LinearEquiv.symm_apply_apply]

theorem frameEnd_comm_torD {ψ : StatedSp n F →* G} (hψ : Function.Injective ψ) {E : Subgroup G}
    {Y : StatedSp n F} (hY : ψ Y ∈ Subgroup.centralizer (E : Set G)) {t : Fin s → ZMod p}
    (ht : nsCoord ψ hc hdec hcω (ofAdd t) ∈ E) (x : (Fin s → D) × (κ → F)) :
    frameEnd Φ Y (torD c t x) = torD c t (frameEnd Φ Y x) := by
  have h1 : Y * torElt hc hdec hcω t = torElt hc hdec hcω t * Y := hψ (by
    rw [map_mul, map_mul, ← nsCoord_eq_torElt]
    exact ((Subgroup.mem_centralizer_iff.mp hY) _ ht).symm)
  have h2 := congrArg (fun Z => frameEnd Φ Z x) h1
  simp only [frameEnd_mul, frameEnd_torElt] at h2
  exact h2

end Torus

section Invariance

variable {F : Type} [Field F] {g : F[X]} [Fact (Irreducible g)] {p : ℕ} [Fact p.Prime]
  {D : Type} [AddCommGroup D] [Module F D] {c : D ≃ₗ[F] D} {s : ℕ} {κ : Type}

omit [Fact (Irreducible g)] [Fact p.Prime] in
theorem torD_apply' (t : Fin s → ZMod p) (y : (Fin s → D) × (κ → F)) :
    torD c t y = (fun i => (c ^ (t i).val) (y.1 i), y.2) := rfl

omit [Fact (Irreducible g)] [Fact p.Prime] in
theorem torD_single (t : Fin s → ZMod p) (i : Fin s) (y : D) :
    torD (κ := κ) c t (Pi.single i y, 0) = (Pi.single i ((c ^ (t i).val) y), 0) := by
  rw [torD_apply]
  congr 1
  funext j
  by_cases hj : j = i
  · subst hj
    simp
  · simp [Pi.single_eq_of_ne hj]

omit [Fact (Irreducible g)] [Fact p.Prime] in
theorem torD_zero_fst (t : Fin s → ZMod p) (w : κ → F) : torD c t (0, w) = (0, w) := by
  rw [torD_apply]
  congr 1
  funext j
  simp

variable [Finite F] (hbt : NsBlockType g p D c) (hζ : AdjoinRoot.root g ^ p = 1)
  (hprim : IsPrimitiveRoot (AdjoinRoot.root g) p) {T' : Set (Fin s → ZMod p)}
  {M : Module.End F ((Fin s → D) × (κ → F))}
  (hM : ∀ t ∈ T', ∀ x, M (torD c t x) = torD c t (M x))
include hbt hζ hprim hM

omit [Finite F] in
theorem fst_zero_of_comm (hZ : ∀ i, ∃ t ∈ T', t i ≠ 0) (w : κ → F) : (M (0, w)).1 = 0 := by
  funext i
  obtain ⟨t, ht, hti⟩ := hZ i
  have h1 := hM t ht (0, w)
  rw [torD_zero_fst, torD_apply'] at h1
  have h2 := congrArg (fun y : (Fin s → D) × (κ → F) => y.1 i) h1
  exact block_pow_fix hbt hζ hprim hti h2.symm

omit [Finite F] in
theorem single_snd_of_comm [FiniteDimensional F D] (hZ : ∀ i, ∃ t ∈ T', t i ≠ 0) (i : Fin s)
    (x : D) : (M (Pi.single i x, 0)).2 = 0 := by
  obtain ⟨t, ht, hti⟩ := hZ i
  set h : D →ₗ[F] (κ → F) := LinearMap.snd F _ _ ∘ₗ M ∘ₗ LinearMap.inl F _ _ ∘ₗ
    LinearMap.single F (fun _ => D) i with hhdef
  have hh : ∀ y, h ((c ^ (t i).val) y) = h y := fun y => by
    have h1 := hM t ht (Pi.single i y, 0)
    rw [torD_single, torD_apply'] at h1
    have h2 := congrArg Prod.snd h1
    exact h2
  set φ : D →ₗ[F] D := ((c ^ (t i).val : D ≃ₗ[F] D) : D →ₗ[F] D) - LinearMap.id with hφ
  have hinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    rw [hφ, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at hy
    exact block_pow_fix hbt hζ hprim hti hy
  obtain ⟨y, rfl⟩ := LinearMap.injective_iff_surjective.mp hinj x
  change h (φ y) = 0
  rw [hφ, LinearMap.sub_apply, LinearMap.id_apply, map_sub, LinearEquiv.coe_coe, hh, sub_self]

theorem single_fst_of_comm {i k : Fin s} (hsep : ∃ t ∈ T',
    (∀ u ∈ galSigns p (Nat.card F), t k ≠ u * t i) ∧ (t k ≠ 0 ∨ t i ≠ 0)) (x : D) :
    (M (Pi.single i x, 0)).1 k = 0 := by
  obtain ⟨t, ht, hab, h0⟩ := hsep
  set f : D →ₗ[F] D := LinearMap.proj k ∘ₗ LinearMap.fst F _ _ ∘ₗ M ∘ₗ LinearMap.inl F _ _ ∘ₗ
    LinearMap.single F (fun _ => D) i with hfdef
  have hf : ∀ y, f ((c ^ (t i).val) y) = (c ^ (t k).val) (f y) := fun y => by
    have h1 := hM t ht (Pi.single i y, 0)
    rw [torD_single, torD_apply'] at h1
    have h2 := congrArg (fun z : (Fin s → D) × (κ → F) => z.1 k) h1
    exact h2
  exact LinearMap.congr_fun (block_sylvester hbt hζ hprim hab h0 hf) x

theorem mem_classSpace_of_comm [FiniteDimensional F D] (hZ : ∀ i, ∃ t ∈ T', t i ≠ 0)
    {X : Set (Fin s)} (hsepX : ∀ i ∈ X, ∀ k ∉ X, ∃ t ∈ T',
      (∀ u ∈ galSigns p (Nat.card F), t k ≠ u * t i) ∧ (t k ≠ 0 ∨ t i ≠ 0))
    {d : Fin s → D} (hd : ∀ i ∉ X, d i = 0) :
    (M (d, 0)).2 = 0 ∧ ∀ k ∉ X, (M (d, 0)).1 k = 0 := by
  classical
  have hsum : (d, (0 : κ → F)) = ∑ i, ((Pi.single i (d i) : Fin s → D), (0 : κ → F)) := by
    refine Prod.ext ?_ ?_
    · rw [Prod.fst_sum]
      exact (Finset.univ_sum_single d).symm
    · rw [Prod.snd_sum]
      simp
  rw [hsum, map_sum]
  refine ⟨?_, fun k hk => ?_⟩
  · rw [Prod.snd_sum]
    exact Finset.sum_eq_zero fun i _ => single_snd_of_comm hbt hζ hprim hM hZ i (d i)
  · rw [Prod.fst_sum, Finset.sum_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    by_cases hi : i ∈ X
    · exact single_fst_of_comm hbt hζ hprim hM (hsepX i hi k hk) (d i)
    · rw [hd i hi, Pi.single_zero, Prod.mk_zero_zero, map_zero]
      rfl

end Invariance

section Fix

variable {G : Type} [Group G] {F : Type} [Field F] {n : ℕ} {D : Type} [AddCommGroup D]
  [Module F D] {s : ℕ} {κ : Type} (Φ : ((Fin s → D) × (κ → F)) ≃ₗ[F] (Fin n ⊕ Fin n → F))

@[expose] def fixGrp (S : Set ((Fin s → D) × (κ → F))) : Subgroup (StatedSp n F) where
  carrier := {Y | ∀ x ∈ S, frameEnd Φ Y x = x}
  mul_mem' := by
    intro Y Z hY hZ x hx
    change frameEnd Φ (Y * Z) x = x
    rw [frameEnd_mul, hZ x hx, hY x hx]
  one_mem' := fun x _ => frameEnd_one Φ x
  inv_mem' := by
    intro Y hY x hx
    have h1 := frameEnd_inv_apply Φ Y x
    rwa [hY x hx] at h1

theorem mem_fixGrp {S : Set ((Fin s → D) × (κ → F))} {Y : StatedSp n F} :
    Y ∈ fixGrp Φ S ↔ ∀ x ∈ S, frameEnd Φ Y x = x :=
  Iff.rfl

theorem normal_fixGrp {ψ : StatedSp n F →* G} {H : Subgroup G} (hH : H ≤ ψ.range)
    {S : Set ((Fin s → D) × (κ → F))}
    (hS : ∀ Y : StatedSp n F, ψ Y ∈ H → ∀ x ∈ S, frameEnd Φ Y x ∈ S) :
    (((fixGrp Φ S).map ψ ⊓ H).subgroupOf H).Normal := by
  constructor
  intro m hm h
  rw [Subgroup.mem_subgroupOf] at hm ⊢
  obtain ⟨⟨Z, hZ, hZm⟩, hmH⟩ := Subgroup.mem_inf.mp hm
  obtain ⟨Y, hY⟩ := hH h.2
  have hYi : ψ Y⁻¹ ∈ H := by
    rw [map_inv, hY]
    exact H.inv_mem h.2
  refine Subgroup.mem_inf.mpr ⟨⟨Y * Z * Y⁻¹, fun x hx => ?_, ?_⟩, ?_⟩
  · rw [frameEnd_mul, frameEnd_mul, hZ _ (hS _ hYi x hx), frameEnd_apply_inv]
  · rw [map_mul, map_mul, map_inv, hY, hZm]
    simp
  · simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact H.mul_mem (H.mul_mem h.2 hmH) (H.inv_mem h.2)

theorem exists_cover_two (P : Fin s → Prop)
    (h : ∀ a b c, a ≠ b → a ≠ c → b ≠ c → P a → P b → P c → False) (i₀ : Fin s) :
    ∃ j₁ j₂, ∀ i, P i → i = j₁ ∨ i = j₂ := by
  by_cases h1 : ∃ a, P a
  · obtain ⟨a, ha⟩ := h1
    by_cases h2 : ∃ b, P b ∧ b ≠ a
    · obtain ⟨b, hb, hba⟩ := h2
      refine ⟨a, b, fun i hi => ?_⟩
      by_contra hne
      push Not at hne
      exact h a b i (Ne.symm hba) (Ne.symm hne.1) (Ne.symm hne.2) ha hb hi
    · refine ⟨a, a, fun i hi => ?_⟩
      by_contra hne
      push Not at hne
      exact h2 ⟨i, hi, hne.1⟩
  · exact ⟨i₀, i₀, fun i hi => absurd ⟨i, hi⟩ h1⟩

end Fix

theorem sep_of_jointAligned {s p : ℕ} [Fact p.Prime] {O : Subgroup (ZMod p)ˣ}
    {T' : Set (Fin s → ZMod p)} (hT : ∀ t ∈ T', ∀ t₀ ∈ T', ∀ a : ZMod p, t - a • t₀ ∈ T')
    {η : Fin s → (ZMod p)ˣ} (hηO : ∀ i, η i ∈ O)
    (hal : CoordShape.JointAligned O ((fun t i => (η i : ZMod p) * t i) '' T')) {i k : Fin s}
    {t₀ : Fin s → ZMod p} (ht₀ : t₀ ∈ T') (hi : t₀ i ≠ 0)
    (hki : ¬ ∀ t ∈ T', (η k : ZMod p) * t k = η i * t i) :
    ∃ t ∈ T', (∀ u ∈ O, t k ≠ u * t i) ∧ (t k ≠ 0 ∨ t i ≠ 0) := by
  set T'' := (fun t i => (η i : ZMod p) * t i) '' T' with hT''
  have hT2 : ∀ t ∈ T'', ∀ t₀ ∈ T'', ∀ a : ZMod p, t - a • t₀ ∈ T'' := by
    rintro _ ⟨t, ht, rfl⟩ _ ⟨t₁, ht₁, rfl⟩ a
    refine ⟨t - a • t₁, hT t ht t₁ ht₁ a, ?_⟩
    funext j
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hki' : ¬ ∀ t ∈ T'', t k = t i := by
    intro h
    apply hki
    intro t ht
    exact h _ ⟨t, ht, rfl⟩
  obtain ⟨_, ⟨t, ht, rfl⟩, hsep⟩ := CoordShape.exists_sep hT2 hal ⟨t₀, ht₀, rfl⟩
    (mul_ne_zero (η i).ne_zero hi) hki'
  refine ⟨t, ht, ?_⟩
  rcases hsep with ⟨hti, hu⟩ | ⟨hti, htk⟩
  · have hti' : t i ≠ 0 := fun h0 => hti (by simp only; rw [h0, mul_zero])
    refine ⟨fun u huO h => ?_, Or.inr hti'⟩
    apply hu (η k * u * (η i)⁻¹) (O.mul_mem (O.mul_mem (hηO k) huO) (O.inv_mem (hηO i)))
    simp only
    rw [h, Units.val_mul, Units.val_mul, mul_assoc, mul_assoc, ← mul_assoc _ (η i : ZMod p),
      ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
  · have hti' : t i = 0 := by
      simp only at hti
      exact (mul_eq_zero.mp hti).resolve_left (η i).ne_zero
    have htk' : t k ≠ 0 := fun h0 => htk (by simp only; rw [h0, mul_zero])
    refine ⟨fun u _ h => htk' (by rw [h, hti', mul_zero]), Or.inl htk'⟩

theorem ofAdd_sum_smul_mem {G : Type} [Group G] {p s m : ℕ} [NeZero p]
    {ι : Multiplicative (Fin s → ZMod p) →* G} {H : Subgroup G} (w : Fin m → Fin s → ZMod p)
    (hw : ∀ a, ι (ofAdd (w a)) ∈ H) (x : Fin m → ZMod p) : ι (ofAdd (∑ a, x a • w a)) ∈ H := by
  refine Finset.sum_induction _ (fun u => ι (ofAdd u) ∈ H) (fun a b ha hb => ?_) ?_
    fun a _ => StepTwoToral.ofAdd_smul_mem (hw a) (x a)
  · rw [ofAdd_add, map_mul]
    exact H.mul_mem ha hb
  · rw [ofAdd_zero, map_one]
    exact H.one_mem

theorem mem_centralizer_of_commutator_eq_bot {G : Type} [Group G] {J N : Subgroup G}
    (hN : ⁅J, N⁆ = ⊥) {b : G} (hb : b ∈ N) : b ∈ Subgroup.centralizer (J : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  have h1 := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hN ha
  exact ((Subgroup.mem_centralizer_iff.mp h1) b hb).symm

end CoordSpNs

open CoordSpNs

theorem ggSpNsFrameShapeInput_holds : GGSpNsFrameShapeInput := by
  intro G _ _ F _ _ _ n p _ hp2 hns ψ hψ g _ hgd D _ _ c hbt hc s κ _ Φ ω hdec hcω hs4 E J hE hJ
    hcard
  classical
  have hpp : p.Prime := Fact.out
  have hpF : (p : F) ≠ 0 := TableBSymp.natCast_ne_zero_of_charTwo hpp hp2
  have hprim := NSFrame.root_isPrimitiveRoot (g := g) hpp hpF hgd
  have hζ : AdjoinRoot.root g ^ p = 1 := hprim.pow_eq_one
  have : Module.Finite F (AdjoinRoot g) := (CoordSL.rootPB g).finite
  have : FiniteDimensional F D := by
    rcases hbt with ⟨-, e, -⟩ | ⟨-, e, -⟩
    · exact Module.Finite.equiv e.symm
    · exact Module.Finite.equiv e.symm
  have : Nontrivial D := by
    rcases hbt with ⟨-, e, -⟩ | ⟨-, e, -⟩
    · exact e.toEquiv.nontrivial
    · exact e.toEquiv.nontrivial
  have hτinj := torHomD_injective (κ := κ) hpp hc (fun x hx => block_pow_fix hbt hζ hprim
    one_ne_zero (by rw [CoordSL.pow_val_one hc]; exact hx)) hdec hcω
  have hιinj : Function.Injective (nsCoord ψ hc hdec hcω) := fun a b hab => by
    rw [nsCoord_apply, nsCoord_apply] at hab
    exact hτinj ((spIso n F).symm.injective (hψ hab))
  have hlt : p ^ 3 < p ^ 4 := Nat.pow_lt_pow_right hpp.one_lt (by norm_num)
  obtain ⟨T', hT'⟩ : ∃ T' : Set (Fin s → ZMod p),
      ∀ t, t ∈ T' ↔ nsCoord ψ hc hdec hcω (ofAdd t) ∈ E :=
    ⟨{t | nsCoord ψ hc hdec hcω (ofAdd t) ∈ E}, fun _ => Iff.rfl⟩
  by_cases hZ0 : ∃ k, ∀ t ∈ T', t k = 0
  · obtain ⟨k, hk⟩ := hZ0
    exact Or.inl ⟨k, fun t ht => hk t ((hT' t).mpr ht)⟩
  push Not at hZ0
  obtain ⟨η, hηO, hal⟩ := CoordShape.exists_jointAligned (galSigns p (Nat.card F)) T'
  have hTsub : ∀ t ∈ T', ∀ t₀ ∈ T', ∀ a : ZMod p, t - a • t₀ ∈ T' := fun t ht t₀ ht₀ a =>
    (hT' _).mpr (CoordShape.sub_smul_mem ((hT' t).mp ht) ((hT' t₀).mp ht₀) a)
  obtain ⟨X, hX⟩ : ∃ X : Fin s → Set (Fin s), ∀ i k, k ∈ X i ↔
      ∀ t ∈ T', (η k : ZMod p) * t k = η i * t i :=
    ⟨fun i => {k | ∀ t ∈ T', (η k : ZMod p) * t k = η i * t i}, fun _ _ => Iff.rfl⟩
  have hXself : ∀ i, i ∈ X i := fun i => (hX i i).mpr fun _ _ => rfl
  obtain ⟨S₀, hS₀⟩ : ∃ S₀ : Set ((Fin s → D) × (κ → F)), ∀ x, x ∈ S₀ ↔ x.1 = 0 :=
    ⟨{x | x.1 = 0}, fun _ => Iff.rfl⟩
  obtain ⟨SX, hSX⟩ : ∃ SX : Fin s → Set ((Fin s → D) × (κ → F)), ∀ i x, x ∈ SX i ↔
      x.2 = 0 ∧ ∀ k, k ∉ X i → x.1 k = 0 :=
    ⟨fun i => {x | x.2 = 0 ∧ ∀ k, k ∉ X i → x.1 k = 0}, fun _ _ => Iff.rfl⟩
  have hMc : ∀ Y : StatedSp n F, ψ Y ∈ ψ.range ⊓ Subgroup.centralizer (E : Set G) →
      ∀ t ∈ T', ∀ x, frameEnd Φ Y (torD c t x) = torD c t (frameEnd Φ Y x) :=
    fun Y hY t ht x => frameEnd_comm_torD hc hdec hcω hψ (Subgroup.mem_inf.mp hY).2
      ((hT' t).mp ht) x
  have hHle : ψ.range ⊓ Subgroup.centralizer (E : Set G) ≤ ψ.range := inf_le_left
  have hN₀ : (((fixGrp Φ S₀).map ψ ⊓ (ψ.range ⊓ Subgroup.centralizer (E : Set G))).subgroupOf
      (ψ.range ⊓ Subgroup.centralizer (E : Set G))).Normal :=
    normal_fixGrp Φ hHle fun Y hY x hx => by
      obtain ⟨d, w⟩ := x
      have hd : d = 0 := (hS₀ _).mp hx
      subst hd
      exact (hS₀ _).mpr (fst_zero_of_comm hbt hζ hprim (hMc Y hY) hZ0 w)
  have hsep : ∀ i, ∀ i' ∈ X i, ∀ k ∉ X i, ∃ t ∈ T',
      (∀ u ∈ galSigns p (Nat.card F), t k ≠ u * t i') ∧ (t k ≠ 0 ∨ t i' ≠ 0) := by
    intro i i' hi' k hk
    obtain ⟨t₀, ht₀, ht₀i⟩ := hZ0 i'
    refine sep_of_jointAligned hTsub hηO hal ht₀ ht₀i fun h => hk ((hX i k).mpr fun t ht => ?_)
    rw [h t ht]
    exact (hX i i').mp hi' t ht
  have hNX : ∀ i, (((fixGrp Φ (SX i)).map ψ ⊓
      (ψ.range ⊓ Subgroup.centralizer (E : Set G))).subgroupOf
      (ψ.range ⊓ Subgroup.centralizer (E : Set G))).Normal := fun i =>
    normal_fixGrp Φ hHle fun Y hY x hx => by
      obtain ⟨d, w⟩ := x
      obtain ⟨hw, hd⟩ := (hSX i _).mp hx
      change w = 0 at hw
      subst hw
      exact (hSX i _).mpr (mem_classSpace_of_comm hbt hζ hprim (hMc Y hY) hZ0 (hsep i) hd)
  have htorH : ∀ u : Fin s → ZMod p,
      ψ (torElt hc hdec hcω u) ∈ ψ.range ⊓ Subgroup.centralizer (E : Set G) := by
    intro u
    refine Subgroup.mem_inf.mpr ⟨⟨_, rfl⟩, Subgroup.mem_centralizer_iff.mpr fun e he => ?_⟩
    obtain ⟨a, rfl⟩ := hE he
    rw [← nsCoord_eq_torElt, ← map_mul, ← map_mul, mul_comm]
  have htorN₀ : ∀ u : Fin s → ZMod p, ψ (torElt hc hdec hcω u) ∈
      (fixGrp Φ S₀).map ψ ⊓ (ψ.range ⊓ Subgroup.centralizer (E : Set G)) := fun u =>
    Subgroup.mem_inf.mpr ⟨⟨_, (mem_fixGrp Φ).mpr fun x hx => by
      obtain ⟨d, w⟩ := x
      have hd : d = 0 := (hS₀ _).mp hx
      subst hd
      rw [frameEnd_torElt, torD_zero_fst], rfl⟩, htorH u⟩
  have htorNX : ∀ i (u : Fin s → ZMod p), (∀ k ∈ X i, u k = 0) → ψ (torElt hc hdec hcω u) ∈
      (fixGrp Φ (SX i)).map ψ ⊓ (ψ.range ⊓ Subgroup.centralizer (E : Set G)) := fun i u hu =>
    Subgroup.mem_inf.mpr ⟨⟨_, (mem_fixGrp Φ).mpr fun x hx => by
      obtain ⟨d, w⟩ := x
      obtain ⟨hw, hd⟩ := (hSX i _).mp hx
      change w = 0 at hw
      subst hw
      rw [frameEnd_torElt, torD_apply]
      congr 1
      funext k
      by_cases hk : k ∈ X i
      · rw [hu k hk, ZMod.val_zero, pow_zero]
        rfl
      · rw [show d k = 0 from hd k hk, map_zero], rfl⟩, htorH u⟩
  have hdich : ∀ N : Subgroup G, N ≤ ψ.range ⊓ Subgroup.centralizer (E : Set G) →
      (N.subgroupOf (ψ.range ⊓ Subgroup.centralizer (E : Set G))).Normal →
        J ≤ N ∨ ⁅J, N⁆ = ⊥ :=
    fun N hNH hN => CoordSL.le_or_commutator_eq_bot_of_normal hJ hNH hN
  by_cases hcase : ∃ i, ⁅J, (fixGrp Φ (SX i)).map ψ ⊓
      (ψ.range ⊓ Subgroup.centralizer (E : Set G))⁆ = ⊥
  ·
    obtain ⟨i₀, hi₀⟩ := hcase
    have hCJ : ∀ u : Fin s → ZMod p, (∀ k ∈ X i₀, u k = 0) → nsCoord ψ hc hdec hcω (ofAdd u) ∈
        (nsCoord ψ hc hdec hcω).range ⊓ Subgroup.centralizer (J : Set G) := fun u hu =>
      Subgroup.mem_inf.mpr ⟨⟨_, rfl⟩,
        mem_centralizer_of_commutator_eq_bot hi₀ (htorNX i₀ u hu)⟩
    have hEJ : ∀ t ∈ T', nsCoord ψ hc hdec hcω (ofAdd t) ∈
        (nsCoord ψ hc hdec hcω).range ⊓ Subgroup.centralizer (J : Set G) := by
      intro t ht
      refine Subgroup.mem_inf.mpr ⟨⟨_, rfl⟩, Subgroup.mem_centralizer_iff.mpr fun a ha => ?_⟩
      have h1 := (Subgroup.mem_inf.mp (hJ.1 ha)).2
      exact ((Subgroup.mem_centralizer_iff.mp h1) _ ((hT' t).mp ht)).symm
    have hcov : ∃ j₁ j₂, ∀ k, k ∉ X i₀ → k = j₁ ∨ k = j₂ := by
      refine exists_cover_two (fun k => k ∉ X i₀) (fun a b c' hab hac hbc ha hb hc' => ?_) i₀
      obtain ⟨t₀, ht₀, ht₀i⟩ := hZ0 i₀
      have hai : a ≠ i₀ := fun h => ha (h ▸ hXself i₀)
      have hbi : b ≠ i₀ := fun h => hb (h ▸ hXself i₀)
      have hci : c' ≠ i₀ := fun h => hc' (h ▸ hXself i₀)
      have hvmem : nsCoord ψ hc hdec hcω (ofAdd fun j => if j ∈ X i₀ then t₀ j else 0) ∈
          (nsCoord ψ hc hdec hcω).range ⊓ Subgroup.centralizer (J : Set G) := by
        have h1 : (fun j => if j ∈ X i₀ then t₀ j else 0) =
            t₀ - fun j => if j ∈ X i₀ then 0 else t₀ j := by
          funext j
          simp only [Pi.sub_apply]
          split_ifs <;> ring
        rw [h1, ofAdd_sub, _root_.map_div]
        exact Subgroup.div_mem _ (hEJ t₀ ht₀)
          (hCJ _ fun k hk => ite_eq_left_iff.mpr fun h => absurd hk h)
      have hwc : ∀ x y : Fin 4,
          (![Pi.single a 1, Pi.single b 1, Pi.single c' 1,
            (t₀ i₀)⁻¹ • fun j => if j ∈ X i₀ then t₀ j else 0] : Fin 4 → Fin s → ZMod p) x
            (![a, b, c', i₀] y) = if x = y then 1 else 0 := by
        intro x y
        fin_cases x <;> fin_cases y <;>
          simp [hab, hac, hbc, hab.symm, hac.symm, hbc.symm, hai.symm, hbi.symm, hci.symm, ha, hb,
            hc', hXself i₀, ht₀i]
      have hwm : ∀ x : Fin 4, nsCoord ψ hc hdec hcω (ofAdd
          ((![Pi.single a 1, Pi.single b 1, Pi.single c' 1,
            (t₀ i₀)⁻¹ • fun j => if j ∈ X i₀ then t₀ j else 0] : Fin 4 → Fin s → ZMod p) x)) ∈
          (nsCoord ψ hc hdec hcω).range ⊓ Subgroup.centralizer (J : Set G) := by
        have hsingle : ∀ k, k ∉ X i₀ → nsCoord ψ hc hdec hcω (ofAdd (Pi.single k 1)) ∈
            (nsCoord ψ hc hdec hcω).range ⊓ Subgroup.centralizer (J : Set G) := fun k hk =>
          hCJ _ fun j hj => Pi.single_eq_of_ne (fun h : j = k => hk (h ▸ hj)) 1
        intro x
        fin_cases x
        · exact hsingle a ha
        · exact hsingle b hb
        · exact hsingle c' hc'
        · exact StepTwoToral.ofAdd_smul_mem hvmem _
      have h4 := CoordShape.pow_four_le_of_dual hιinj _ _ hwc (ofAdd_sum_smul_mem _ hwm)
      omega
    obtain ⟨j₁, j₂, hj⟩ := hcov
    refine Or.inr ⟨j₁, j₂, fun k => (η k)⁻¹, fun k => (galSigns p (Nat.card F)).inv_mem (hηO k),
      fun t ht => ⟨(η i₀ : ZMod p) * t i₀, fun k hk1 hk2 => ?_⟩⟩
    have hkX : k ∈ X i₀ := by
      by_contra h
      rcases hj k h with h' | h'
      · exact hk1 h'
      · exact hk2 h'
    rw [← (hX i₀ k).mp hkX t ((hT' t).mpr ht), ← mul_assoc, ← Units.val_mul, inv_mul_cancel,
      Units.val_one, one_mul]
  · push Not at hcase
    have hJX : ∀ i, J ≤ (fixGrp Φ (SX i)).map ψ ⊓
        (ψ.range ⊓ Subgroup.centralizer (E : Set G)) := fun i =>
      (hdich _ inf_le_right (hNX i)).resolve_right (hcase i)
    exfalso
    rcases hdich _ inf_le_right hN₀ with hJ0 | hJ0
    ·
      apply LinSemisimple.false_of_isQuasisimple_of_commute hJ.2.2
      have h1 : ∀ a ∈ J, a = 1 := by
        intro a ha
        obtain ⟨⟨Z, hZ, rfl⟩, -⟩ := Subgroup.mem_inf.mp (hJ0 ha)
        have hfix : ∀ i (x : D), frameEnd Φ Z (Pi.single i x, 0) = (Pi.single i x, 0) := by
          intro i x
          obtain ⟨⟨Z', hZ', hZZ'⟩, -⟩ := Subgroup.mem_inf.mp (hJX i ha)
          have hZe : Z' = Z := hψ hZZ'
          have hZ'' : Z ∈ fixGrp Φ (SX i) := hZe ▸ hZ'
          refine (mem_fixGrp Φ).mp hZ'' _ ((hSX i _).mpr ⟨rfl, fun k hk => ?_⟩)
          change (Pi.single i x : Fin s → D) k = 0
          rw [Pi.single_apply, ite_eq_right fun h : k = i => hk (h ▸ hXself i)]
        have hfix0 : ∀ w : κ → F, frameEnd Φ Z (0, w) = (0, w) := fun w =>
          (mem_fixGrp Φ).mp hZ _ ((hS₀ _).mpr rfl)
        have hall : ∀ x, frameEnd Φ Z x = x := by
          rintro ⟨d, w⟩
          have hsum : ((d, w) : (Fin s → D) × (κ → F)) =
              ∑ i, ((Pi.single i (d i) : Fin s → D), (0 : κ → F)) + (0, w) := by
            refine Prod.ext ?_ ?_
            · rw [Prod.fst_add, Prod.fst_sum, Finset.univ_sum_single, add_zero]
            · rw [Prod.snd_add, Prod.snd_sum]
              simp
          rw [hsum, map_add, map_sum, hfix0]
          congr 1
          exact Finset.sum_congr rfl fun i _ => hfix i (d i)
        rw [eq_one_of_frameEnd Φ Z hall, map_one]
      intro x hx y hy
      rw [h1 x hx, h1 y hy]
    ·
      have hall : ∀ u : Fin s → ZMod p, nsCoord ψ hc hdec hcω (ofAdd u) ∈
          (nsCoord ψ hc hdec hcω).range ⊓ Subgroup.centralizer (J : Set G) := fun u =>
        Subgroup.mem_inf.mpr ⟨⟨_, rfl⟩, mem_centralizer_of_commutator_eq_bot hJ0 (htorN₀ u)⟩
      have h4 := CoordShape.pow_four_le_of_dual hιinj
        (H := (nsCoord ψ hc hdec hcω).range ⊓ Subgroup.centralizer (J : Set G))
        (fun a => Pi.single (Fin.castLE hs4 a) 1) (Fin.castLE hs4) (fun a b => by
          simp only [Pi.single_apply, (Fin.castLE_injective hs4).eq_iff]
          by_cases hab : a = b
          · simp [hab]
          · simp [hab, Ne.symm hab]) fun x => hall _
      omega

section Certified

theorem ggSpCoordModelNonsplitInput_of_comp (hcomp : GGSpNsFrameCompInput) :
    GGSpCoordModelNonsplitInput :=
  ggSpCoordModelNonsplitInput_of_frame hcomp ggSpNsFrameShapeInput_holds

end Certified

end CFSG.StandardType
