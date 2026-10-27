module

public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelSpNsShape

public section

open Polynomial Module Multiplicative
open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Symplectic
open CFSG.RankThree.Classical (spForm spLin spLin_injective)

namespace CFSG.StandardType

open CoordSpNs

namespace CoordSpNs

section PerCoord

variable {F : Type} [Field F] {g : F[X]} [Fact (Irreducible g)] {p : ℕ} [Fact p.Prime]
  {D : Type} [AddCommGroup D] [Module F D] {c : D ≃ₗ[F] D} {s : ℕ} {κ : Type}
  (hbt : NsBlockType g p D c) (hζ : AdjoinRoot.root g ^ p = 1)
  (hprim : IsPrimitiveRoot (AdjoinRoot.root g) p) {T' : Set (Fin s → ZMod p)}
  {M : Module.End F ((Fin s → D) × (κ → F))}
  (hM : ∀ t ∈ T', ∀ x, M (torD c t x) = torD c t (M x))
include hbt hζ hprim hM

theorem fst_zero_apply_of_comm {k : Fin s} {t : Fin s → ZMod p} (ht : t ∈ T') (htk : t k ≠ 0)
    (w : κ → F) : (M (0, w)).1 k = 0 := by
  have h1 := hM t ht (0, w)
  rw [torD_zero_fst, torD_apply'] at h1
  have h2 := congrArg (fun y : (Fin s → D) × (κ → F) => y.1 k) h1
  exact block_pow_fix hbt hζ hprim htk h2.symm

theorem single_snd_of_comm' [FiniteDimensional F D] {i : Fin s} {t : Fin s → ZMod p}
    (ht : t ∈ T') (hti : t i ≠ 0) (x : D) : (M (Pi.single i x, 0)).2 = 0 := by
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

end PerCoord

section Count

variable {G : Type} [Group G] {p s : ℕ}

theorem pow_three_le_of_dual [Finite G] {ι : Multiplicative (Fin s → ZMod p) →* G}
    (hinj : Function.Injective ι) {H : Subgroup G} (w : Fin 3 → Fin s → ZMod p) (c : Fin 3 → Fin s)
    (hwc : ∀ a b, w a (c b) = if a = b then 1 else 0)
    (hH : ∀ x : Fin 3 → ZMod p, ι (ofAdd (∑ a, x a • w a)) ∈ H) : p ^ 3 ≤ Nat.card H := by
  have heval : ∀ (x : Fin 3 → ZMod p) b, (∑ a, x a • w a) (c b) = x b := by
    intro x b
    rw [Finset.sum_apply]
    simp [hwc]
  have hf : Function.Injective fun x : Fin 3 → ZMod p =>
      (⟨ι (ofAdd (∑ a, x a • w a)), hH x⟩ : H) := by
    intro x y hxy
    have h1 := ofAdd.injective (hinj (congrArg Subtype.val hxy))
    funext b
    have h2 := congrFun h1 (c b)
    rwa [heval, heval] at h2
  have h := Nat.card_le_card_of_injective _ hf
  rwa [Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card (α := Fin 3), Fintype.card_fin] at h

theorem mem_of_supported [NeZero p] {ι : Multiplicative (Fin s → ZMod p) →* G} {H : Subgroup G}
    {X : Set (Fin s)} (hX : ∀ k ∉ X, ι (ofAdd (Pi.single k 1)) ∈ H) {u : Fin s → ZMod p}
    (hu : ∀ k ∈ X, u k = 0) : ι (ofAdd u) ∈ H := by
  classical
  have hsum : u = ∑ k, u k • (Pi.single k 1 : Fin s → ZMod p) := by
    funext j
    rw [Finset.sum_apply]
    simp [Pi.single_apply]
  rw [hsum]
  refine Finset.sum_induction _ (fun v => ι (ofAdd v) ∈ H) (fun a b ha hb => ?_) ?_
    fun k _ => ?_
  · rw [ofAdd_add, map_mul]
    exact H.mul_mem ha hb
  · rw [ofAdd_zero, map_one]
    exact H.one_mem
  · by_cases hk : k ∈ X
    · rw [hu k hk, zero_smul, ofAdd_zero, map_one]
      exact H.one_mem
    · exact StepTwoToral.ofAdd_smul_mem (hX k hk) (u k)

end Count

theorem frameEnd_comm_torD_of_comm {G : Type} [Group G] {F : Type} [Field F] {n p : ℕ} [NeZero p]
    {D : Type} [AddCommGroup D] [Module F D] {s : ℕ} {κ : Type} {c : D ≃ₗ[F] D} (hc : c ^ p = 1)
    {Φ : ((Fin s → D) × (κ → F)) ≃ₗ[F] (Fin n ⊕ Fin n → F)} {ω : LinearMap.BilinForm F D}
    (hdec : ∀ d d' w w', spForm n F (Φ (d, w)) (Φ (d', w')) =
      ∑ i, ω (d i) (d' i) + spForm n F (Φ (0, w)) (Φ (0, w')))
    (hcω : ∀ x y, ω (c x) (c y) = ω x y) {ψ : StatedSp n F →* G} (hψ : Function.Injective ψ)
    {Y : StatedSp n F} {t : Fin s → ZMod p}
    (h : ψ Y * nsCoord ψ hc hdec hcω (ofAdd t) = nsCoord ψ hc hdec hcω (ofAdd t) * ψ Y)
    (x : (Fin s → D) × (κ → F)) :
    frameEnd Φ Y (torD c t x) = torD c t (frameEnd Φ Y x) := by
  have h1 : Y * torElt hc hdec hcω t = torElt hc hdec hcω t * Y := hψ (by
    rw [map_mul, map_mul, ← nsCoord_eq_torElt]
    exact h)
  have h2 := congrArg (fun Z => frameEnd Φ Z x) h1
  simp only [frameEnd_mul, frameEnd_torElt] at h2
  exact h2

theorem apply_eq_sum_single {F D κ : Type} [Field F] [AddCommGroup D] [Module F D] {s : ℕ}
    (M : Module.End F ((Fin s → D) × (κ → F))) (d : Fin s → D) :
    M (d, 0) = ∑ i, M (Pi.single i (d i), 0) := by
  classical
  rw [← map_sum]
  congr 1
  refine Prod.ext ?_ ?_
  · rw [Prod.fst_sum]
    exact (Finset.univ_sum_single d).symm
  · rw [Prod.snd_sum]
    simp

theorem eq_one_of_frameEnd_basic {F D κ : Type} [Field F] [AddCommGroup D] [Module F D] {n s : ℕ}
    (Φ : ((Fin s → D) × (κ → F)) ≃ₗ[F] (Fin n ⊕ Fin n → F)) {Z : StatedSp n F}
    (h0 : ∀ w, frameEnd Φ Z (0, w) = (0, w))
    (h1 : ∀ i (x : D), frameEnd Φ Z (Pi.single i x, 0) = (Pi.single i x, 0)) : Z = 1 := by
  classical
  refine eq_one_of_frameEnd Φ Z fun x => ?_
  obtain ⟨d, w⟩ := x
  have hsum : ((d, w) : (Fin s → D) × (κ → F)) =
      ∑ i, ((Pi.single i (d i) : Fin s → D), (0 : κ → F)) + (0, w) := by
    refine Prod.ext ?_ ?_
    · rw [Prod.fst_add, Prod.fst_sum, Finset.univ_sum_single, add_zero]
    · rw [Prod.snd_add, Prod.snd_sum]
      simp
  rw [hsum, map_add, map_sum, h0]
  congr 1
  exact Finset.sum_congr rfl fun i _ => h1 i (d i)

end CoordSpNs

@[expose] def GGSpNsZeroContInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (F : Type) [Field F] [Finite F] [CharP F 2] (n p : ℕ)
    [Fact p.Prime], p ≠ 2 → ¬ p ∣ Nat.card F - 1 →
    ∀ ψ : StatedSp n F →* G, Function.Injective ψ →
    ∀ (g : F[X]) [Fact (Irreducible g)], g ∣ cyclotomic p F →
    ∀ (D : Type) [AddCommGroup D] [Module F D] (c : D ≃ₗ[F] D), NsBlockType g p D c →
    ∀ (hc : c ^ p = 1) (s : ℕ) (κ : Type) [Fintype κ]
      (Φ : ((Fin s → D) × (κ → F)) ≃ₗ[F] (Fin n ⊕ Fin n → F)) (ω : LinearMap.BilinForm F D)
      (hdec : ∀ d d' w w', spForm n F (Φ (d, w)) (Φ (d', w')) =
        ∑ i, ω (d i) (d' i) + spForm n F (Φ (0, w)) (Φ (0, w')))
      (hcω : ∀ x y, ω (c x) (c y) = ω x y),
    ∀ (β : Fin s → ZMod p) (L₁ : Subgroup G), β ≠ 0 → (∃ i j, i ≠ j ∧ β i = 0 ∧ β j = 0) →
      IsComponentOf L₁ (ψ.range ⊓ Subgroup.centralizer {nsCoord ψ hc hdec hcω (ofAdd β)}) →
      L₁ ≤ (fixGrp Φ {x | x.2 = 0 ∧ ∀ i, β i = 0 → x.1 i = 0}).map ψ →
      ∀ t : Fin s → ZMod p, (∀ i, β i ≠ 0 → t i = 0) → nsCoord ψ hc hdec hcω (ofAdd t) ∈ L₁

@[expose] def GGSpNsClassContInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (F : Type) [Field F] [Finite F] [CharP F 2] (n p : ℕ)
    [Fact p.Prime], p ≠ 2 → ¬ p ∣ Nat.card F - 1 →
    ∀ ψ : StatedSp n F →* G, Function.Injective ψ →
    ∀ (g : F[X]) [Fact (Irreducible g)], g ∣ cyclotomic p F →
    ∀ (D : Type) [AddCommGroup D] [Module F D] (c : D ≃ₗ[F] D), NsBlockType g p D c →
    ∀ (hc : c ^ p = 1) (s : ℕ) (κ : Type) [Fintype κ]
      (Φ : ((Fin s → D) × (κ → F)) ≃ₗ[F] (Fin n ⊕ Fin n → F)) (ω : LinearMap.BilinForm F D)
      (hdec : ∀ d d' w w', spForm n F (Φ (d, w)) (Φ (d', w')) =
        ∑ i, ω (d i) (d' i) + spForm n F (Φ (0, w)) (Φ (0, w')))
      (hcω : ∀ x y, ω (c x) (c y) = ω x y),
    ∀ (β : Fin s → ZMod p) (L₁ : Subgroup G) (X : Set (Fin s)) (η : Fin s → (ZMod p)ˣ)
      (c₀ : ZMod p), c₀ ≠ 0 → (∀ i, η i ∈ galSigns p (Nat.card F)) →
      (∀ i ∈ X, (η i : ZMod p) * β i = c₀) →
      IsComponentOf L₁ (ψ.range ⊓ Subgroup.centralizer {nsCoord ψ hc hdec hcω (ofAdd β)}) →
      L₁ ≤ (fixGrp Φ {x | ∀ i ∈ X, x.1 i = 0}).map ψ →
      ∀ t : Fin s → ZMod p, (∀ i ∉ X, t i = 0) → ∑ i, (η i : ZMod p) * t i = 0 →
        nsCoord ψ hc hdec hcω (ofAdd t) ∈ L₁

theorem ggSpNsFrameCompInput_of_cont (hZc : GGSpNsZeroContInput) (hXc : GGSpNsClassContInput) :
    GGSpNsFrameCompInput := by
  intro G _ _ F _ _ _ n p _ hp2 hns ψ hψ g _ hgd D _ _ c hbt hc s κ _ Φ ω hdec hcω hs4 b L₁ _ hb1
    hL₁ hcard β hβ
  classical
  subst hβ
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
  have hlt : p ^ 2 < p ^ 3 := Nat.pow_lt_pow_right hpp.one_lt (by norm_num)
  have hβ0 : β ≠ 0 := fun h => hb1 (by rw [h, ofAdd_zero, map_one])
  obtain ⟨i₁, hi₁⟩ : ∃ i, β i ≠ 0 := by
    by_contra h
    push Not at h
    exact hβ0 (funext h)
  have hs2 : 2 < s := by omega
  have hMc : ∀ Y : StatedSp n F,
      ψ Y ∈ ψ.range ⊓ Subgroup.centralizer {nsCoord ψ hc hdec hcω (ofAdd β)} →
      ∀ t ∈ ({β} : Set (Fin s → ZMod p)), ∀ x,
        frameEnd Φ Y (torD c t x) = torD c t (frameEnd Φ Y x) := by
    intro Y hY t ht x
    rw [Set.mem_singleton_iff] at ht
    subst ht
    exact frameEnd_comm_torD_of_comm hc hdec hcω hψ
      (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hY).2) x
  have hβmem : β ∈ ({β} : Set (Fin s → ZMod p)) := rfl
  obtain ⟨X, hX⟩ : ∃ X : Fin s → Set (Fin s), ∀ i k, k ∈ X i ↔
      ∃ u ∈ galSigns p (Nat.card F), β k = (u : ZMod p) * β i :=
    ⟨fun i => {k | ∃ u ∈ galSigns p (Nat.card F), β k = (u : ZMod p) * β i},
      fun _ _ => Iff.rfl⟩
  have hXself : ∀ i, i ∈ X i := fun i =>
    (hX i i).mpr ⟨1, (galSigns _ _).one_mem, by rw [Units.val_one, one_mul]⟩
  have hXne : ∀ i, β i ≠ 0 → ∀ k ∈ X i, β k ≠ 0 := by
    intro i hi k hk
    obtain ⟨u, -, hu⟩ := (hX i k).mp hk
    rw [hu]
    exact mul_ne_zero u.ne_zero hi
  have hXsep : ∀ i, ∀ k ∈ X i, ∀ j ∉ X i, ∀ u ∈ galSigns p (Nat.card F),
      β k ≠ (u : ZMod p) * β j := by
    intro i k hk j hj u hu h
    obtain ⟨u', hu'O, hu'⟩ := (hX i k).mp hk
    apply hj
    refine (hX i j).mpr ⟨u⁻¹ * u', (galSigns _ _).mul_mem ((galSigns _ _).inv_mem hu) hu'O, ?_⟩
    calc β j = ((u⁻¹ : (ZMod p)ˣ) : ZMod p) * ((u : ZMod p) * β j) := by
          rw [← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
      _ = _ := by rw [← h, hu', Units.val_mul, mul_assoc]
  have hXdisj : ∀ i j, j ∉ X i → ∀ k ∈ X j, k ∉ X i := by
    intro i j hj k hkj hki
    obtain ⟨u, huO, hu⟩ := (hX j k).mp hkj
    exact hXsep i k hki j hj u huO hu
  set H := ψ.range ⊓ Subgroup.centralizer {nsCoord ψ hc hdec hcω (ofAdd β)} with hHdef
  have hHle : H ≤ ψ.range := inf_le_left
  obtain ⟨Snz, hSnz⟩ : ∃ S : Set ((Fin s → D) × (κ → F)),
      ∀ x, x ∈ S ↔ x.2 = 0 ∧ ∀ i, β i = 0 → x.1 i = 0 :=
    ⟨{x | x.2 = 0 ∧ ∀ i, β i = 0 → x.1 i = 0}, fun _ => Iff.rfl⟩
  obtain ⟨Soff, hSoff⟩ : ∃ S : Fin s → Set ((Fin s → D) × (κ → F)),
      ∀ i x, x ∈ S i ↔ ∀ k ∈ X i, x.1 k = 0 :=
    ⟨fun i => {x | ∀ k ∈ X i, x.1 k = 0}, fun _ _ => Iff.rfl⟩
  have hNZ : (((fixGrp Φ Snz).map ψ ⊓ H).subgroupOf H).Normal :=
    normal_fixGrp Φ hHle fun Y hY x hx => by
      obtain ⟨d, w⟩ := x
      obtain ⟨hw, hd⟩ := (hSnz _).mp hx
      change w = 0 at hw
      subst hw
      have hM := hMc Y hY
      refine (hSnz _).mpr ⟨?_, fun k hk => ?_⟩
      · rw [apply_eq_sum_single, Prod.snd_sum]
        refine Finset.sum_eq_zero fun i _ => ?_
        by_cases hi : β i = 0
        · rw [show d i = 0 from hd i hi, Pi.single_zero, Prod.mk_zero_zero, map_zero]
          rfl
        · exact single_snd_of_comm' hbt hζ hprim hM hβmem hi (d i)
      · rw [apply_eq_sum_single, Prod.fst_sum, Finset.sum_apply]
        refine Finset.sum_eq_zero fun i _ => ?_
        by_cases hi : β i = 0
        · rw [show d i = 0 from hd i hi, Pi.single_zero, Prod.mk_zero_zero, map_zero]
          rfl
        · refine single_fst_of_comm hbt hζ hprim hM ⟨β, hβmem, fun u _ h => ?_, Or.inr hi⟩ (d i)
          rw [hk] at h
          exact (mul_ne_zero u.ne_zero hi) h.symm
  have hNX : ∀ i, β i ≠ 0 → (((fixGrp Φ (Soff i)).map ψ ⊓ H).subgroupOf H).Normal :=
    fun i hi => normal_fixGrp Φ hHle fun Y hY x hx => by
      obtain ⟨d, w⟩ := x
      have hd := (hSoff i _).mp hx
      have hM := hMc Y hY
      refine (hSoff i _).mpr fun k hk => ?_
      have hsplit : frameEnd Φ Y (d, w) = frameEnd Φ Y (d, 0) + frameEnd Φ Y (0, w) := by
        rw [← map_add, Prod.mk_add_mk, add_zero, zero_add]
      rw [hsplit, Prod.fst_add, Pi.add_apply,
        fst_zero_apply_of_comm hbt hζ hprim hM hβmem (hXne i hi k hk) w, add_zero,
        apply_eq_sum_single, Prod.fst_sum, Finset.sum_apply]
      refine Finset.sum_eq_zero fun j _ => ?_
      by_cases hj : j ∈ X i
      · rw [show d j = 0 from hd j hj, Pi.single_zero, Prod.mk_zero_zero, map_zero]
        rfl
      · exact single_fst_of_comm hbt hζ hprim hM
          ⟨β, hβmem, fun u hu => hXsep i k hk j hj u hu, Or.inl (hXne i hi k hk)⟩ (d j)
  have hdich : ∀ N : Subgroup G, N ≤ H → (N.subgroupOf H).Normal → L₁ ≤ N ∨ ⁅L₁, N⁆ = ⊥ :=
    fun N hNH hN => CoordSL.le_or_commutator_eq_bot_of_normal hL₁ hNH hN
  have htorH : ∀ u : Fin s → ZMod p, ψ (torElt hc hdec hcω u) ∈ H := by
    intro u
    refine Subgroup.mem_inf.mpr ⟨⟨_, rfl⟩, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    rw [← nsCoord_eq_torElt, ← map_mul (nsCoord ψ hc hdec hcω),
      ← map_mul (nsCoord ψ hc hdec hcω), mul_comm]
  have htorNZ : ∀ u : Fin s → ZMod p, (∀ i, β i ≠ 0 → u i = 0) →
      ψ (torElt hc hdec hcω u) ∈ (fixGrp Φ Snz).map ψ ⊓ H := fun u hu =>
    Subgroup.mem_inf.mpr ⟨⟨_, (mem_fixGrp Φ).mpr fun x hx => by
      obtain ⟨d, w⟩ := x
      obtain ⟨hw, hd⟩ := (hSnz _).mp hx
      change w = 0 at hw
      subst hw
      rw [frameEnd_torElt, torD_apply]
      congr 1
      funext k
      by_cases hk : β k = 0
      · rw [show d k = 0 from hd k hk, map_zero]
      · rw [hu k hk, ZMod.val_zero, pow_zero]
        rfl, rfl⟩, htorH u⟩
  have htorNX : ∀ i (u : Fin s → ZMod p), (∀ k ∉ X i, u k = 0) →
      ψ (torElt hc hdec hcω u) ∈ (fixGrp Φ (Soff i)).map ψ ⊓ H := fun i u hu =>
    Subgroup.mem_inf.mpr ⟨⟨_, (mem_fixGrp Φ).mpr fun x hx => by
      obtain ⟨d, w⟩ := x
      have hd := (hSoff i _).mp hx
      rw [frameEnd_torElt, torD_apply]
      congr 1
      funext k
      by_cases hk : k ∈ X i
      · rw [show d k = 0 from hd k hk, map_zero]
      · rw [hu k hk, ZMod.val_zero, pow_zero]
        rfl, rfl⟩, htorH u⟩
  have hcontra : ∀ S₁ S₂ : Set ((Fin s → D) × (κ → F)),
      (∀ w : κ → F, ((0 : Fin s → D), w) ∈ S₁ ∨ ((0 : Fin s → D), w) ∈ S₂) →
      (∀ i (x : D), ((Pi.single i x : Fin s → D), (0 : κ → F)) ∈ S₁ ∨
        ((Pi.single i x : Fin s → D), (0 : κ → F)) ∈ S₂) →
      L₁ ≤ (fixGrp Φ S₁).map ψ → L₁ ≤ (fixGrp Φ S₂).map ψ → False := by
    intro S₁ S₂ h0 h1 hL1 hL2
    apply LinSemisimple.false_of_isQuasisimple_of_commute hL₁.2.2
    have hone : ∀ a ∈ L₁, a = 1 := by
      intro a ha
      obtain ⟨Z, hZ, rfl⟩ := hL1 ha
      obtain ⟨Z', hZ', hZZ'⟩ := hL2 ha
      have hZe : Z' = Z := hψ hZZ'
      rw [hZe] at hZ'
      have hfx : ∀ x, x ∈ S₁ ∨ x ∈ S₂ → frameEnd Φ Z x = x := fun x hx =>
        hx.elim ((mem_fixGrp Φ).mp hZ x) ((mem_fixGrp Φ).mp hZ' x)
      rw [eq_one_of_frameEnd_basic Φ (fun w => hfx _ (h0 w)) (fun i x => hfx _ (h1 i x)),
        map_one]
    intro x hx y hy
    rw [hone x hx, hone y hy]
  have hZX : ∀ i₀, β i₀ ≠ 0 → L₁ ≤ (fixGrp Φ Snz).map ψ →
      L₁ ≤ (fixGrp Φ (Soff i₀)).map ψ → False := by
    intro i₀ hi₀ h1 h2
    refine hcontra Snz (Soff i₀) (fun w => Or.inr ((hSoff i₀ _).mpr fun k _ => rfl))
      (fun i x => ?_) h1 h2
    by_cases hi : β i = 0
    · refine Or.inr ((hSoff i₀ _).mpr fun k hk => ?_)
      have hki : k ≠ i := fun h => hXne i₀ hi₀ k hk (h ▸ hi)
      change (Pi.single i x : Fin s → D) k = 0
      rw [Pi.single_apply, ite_eq_right hki]
    · refine Or.inl ((hSnz _).mpr ⟨rfl, fun k hk => ?_⟩)
      have hki : k ≠ i := fun h => hi (h ▸ hk)
      change (Pi.single i x : Fin s → D) k = 0
      rw [Pi.single_apply, ite_eq_right hki]
  have hXX : ∀ i₀ i, i ∉ X i₀ → L₁ ≤ (fixGrp Φ (Soff i₀)).map ψ →
      L₁ ≤ (fixGrp Φ (Soff i)).map ψ → False := by
    intro i₀ i hi h1 h2
    refine hcontra (Soff i₀) (Soff i) (fun w => Or.inl ((hSoff i₀ _).mpr fun k _ => rfl))
      (fun j x => ?_) h1 h2
    by_cases hj : j ∈ X i₀
    · refine Or.inr ((hSoff i _).mpr fun k hk => ?_)
      have hkj : k ≠ j := fun h => hXdisj i₀ i hi k hk (h ▸ hj)
      change (Pi.single j x : Fin s → D) k = 0
      rw [Pi.single_apply, ite_eq_right hkj]
    · refine Or.inl ((hSoff i₀ _).mpr fun k hk => ?_)
      have hkj : k ≠ j := fun h => hj (h ▸ hk)
      change (Pi.single j x : Fin s → D) k = 0
      rw [Pi.single_apply, ite_eq_right hkj]
  set H' := (nsCoord ψ hc hdec hcω).range ⊓ Subgroup.centralizer (L₁ : Set G) with hH'
  have hunitZ : ⁅L₁, (fixGrp Φ Snz).map ψ ⊓ H⁆ = ⊥ → ∀ k, β k = 0 →
      nsCoord ψ hc hdec hcω (ofAdd (Pi.single k 1)) ∈ H' := fun hN k hk0 =>
    Subgroup.mem_inf.mpr ⟨⟨_, rfl⟩, mem_centralizer_of_commutator_eq_bot hN
      (htorNZ _ fun i hi => by rw [Pi.single_apply, ite_eq_right fun h : i = k => hi (h ▸ hk0)])⟩
  have hunitX : ∀ k, ⁅L₁, (fixGrp Φ (Soff k)).map ψ ⊓ H⁆ = ⊥ →
      nsCoord ψ hc hdec hcω (ofAdd (Pi.single k 1)) ∈ H' := fun k hN =>
    Subgroup.mem_inf.mpr ⟨⟨_, rfl⟩, mem_centralizer_of_commutator_eq_bot hN
      (htorNX k _ fun j hj => by
        rw [Pi.single_apply, ite_eq_right fun h : j = k => hj (h ▸ hXself k)])⟩
  by_cases hA : L₁ ≤ (fixGrp Φ Snz).map ψ ⊓ H
  ·
    have hA' : L₁ ≤ (fixGrp Φ Snz).map ψ := hA.trans inf_le_left
    have hcomm : ∀ k, β k ≠ 0 → nsCoord ψ hc hdec hcω (ofAdd (Pi.single k 1)) ∈ H' :=
      fun k hk => hunitX k ((hdich _ inf_le_right (hNX k hk)).resolve_left fun h =>
        hZX k hk hA' (h.trans inf_le_left))
    have hcov : ∃ j₁ j₂, ∀ i, β i ≠ 0 → i = j₁ ∨ i = j₂ := by
      refine exists_cover_two (fun i => β i ≠ 0) (fun a b c' hab hac hbc ha hb hc' => ?_) i₁
      have h3 := pow_three_le_of_dual hιinj (H := H')
        ![Pi.single a 1, Pi.single b 1, Pi.single c' 1] ![a, b, c'] (fun x y => by
          fin_cases x <;> fin_cases y <;> simp [hab, hac, hbc, hab.symm, hac.symm, hbc.symm])
        (ofAdd_sum_smul_mem _ fun x => by
          fin_cases x
          · exact hcomm a ha
          · exact hcomm b hb
          · exact hcomm c' hc')
      omega
    obtain ⟨j₁, j₂, hj⟩ := hcov
    refine Or.inl ⟨j₁, j₂, fun i h1 h2 => ?_, fun t h1 h2 => ?_⟩
    · by_contra h
      rcases hj i h with h' | h'
      · exact h1 h'
      · exact h2 h'
    ·
      have hZ2 : ∃ i j, i ≠ j ∧ β i = 0 ∧ β j = 0 := by
        have hcardA : 1 < (Finset.univ.filter fun i : Fin s => i ≠ j₁ ∧ i ≠ j₂).card := by
          have hneg : (Finset.univ.filter fun i : Fin s => ¬ (i ≠ j₁ ∧ i ≠ j₂)) ⊆ {j₁, j₂} := by
            intro i hi
            rw [Finset.mem_filter] at hi
            rw [Finset.mem_insert, Finset.mem_singleton]
            by_contra h
            push Not at h
            exact hi.2 h
          have h1 := Finset.card_le_card hneg
          have h2 : ({j₁, j₂} : Finset (Fin s)).card ≤ 2 := Finset.card_le_two
          have h3 := Finset.card_filter_add_card_filter_not (s := Finset.univ)
            (fun i : Fin s => i ≠ j₁ ∧ i ≠ j₂)
          rw [Finset.card_univ, Fintype.card_fin] at h3
          omega
        obtain ⟨i, hi, j, hj', hij⟩ := Finset.one_lt_card.mp hcardA
        rw [Finset.mem_filter] at hi hj'
        refine ⟨i, j, hij, ?_, ?_⟩
        · by_contra h
          rcases hj i h with h' | h'
          · exact hi.2.1 h'
          · exact hi.2.2 h'
        · by_contra h
          rcases hj j h with h' | h'
          · exact hj'.2.1 h'
          · exact hj'.2.2 h'
      refine hZc G F n p hp2 hns ψ hψ g hgd D c hbt hc s κ Φ ω hdec hcω β L₁ hβ0 hZ2 hL₁ ?_ t
        fun i hi => ?_
      · intro a ha
        obtain ⟨Z, hZ, hZa⟩ := hA' ha
        exact ⟨Z, (mem_fixGrp Φ).mpr fun x hx => (mem_fixGrp Φ).mp hZ x ((hSnz x).mpr hx), hZa⟩
      · rcases hj i hi with h | h
        · rw [h]
          exact h1
        · rw [h]
          exact h2
  have hNZb : ⁅L₁, (fixGrp Φ Snz).map ψ ⊓ H⁆ = ⊥ := (hdich _ inf_le_right hNZ).resolve_left hA
  by_cases hB : ∃ i₀, β i₀ ≠ 0 ∧ L₁ ≤ (fixGrp Φ (Soff i₀)).map ψ ⊓ H
  ·
    obtain ⟨i₀, hi₀, hL⟩ := hB
    have hL' : L₁ ≤ (fixGrp Φ (Soff i₀)).map ψ := hL.trans inf_le_left
    have hcomm : ∀ k, k ∉ X i₀ → nsCoord ψ hc hdec hcω (ofAdd (Pi.single k 1)) ∈ H' := by
      intro k hk
      by_cases hk0 : β k = 0
      · exact hunitZ hNZb k hk0
      · exact hunitX k ((hdich _ inf_le_right (hNX k hk0)).resolve_left fun h =>
          hXX i₀ k hk hL' (h.trans inf_le_left))
    have hbL : nsCoord ψ hc hdec hcω (ofAdd β) ∈ H' := by
      refine Subgroup.mem_inf.mpr ⟨⟨_, rfl⟩, Subgroup.mem_centralizer_iff.mpr fun a ha => ?_⟩
      exact Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp (hL₁.1 ha)).2
    have hvmem : nsCoord ψ hc hdec hcω (ofAdd fun j => if j ∈ X i₀ then β j else 0) ∈ H' := by
      have h1 : (fun j => if j ∈ X i₀ then β j else 0) =
          β - fun j => if j ∈ X i₀ then 0 else β j := by
        funext j
        simp only [Pi.sub_apply]
        split_ifs <;> ring
      rw [h1, ofAdd_sub, _root_.map_div]
      exact Subgroup.div_mem _ hbL
        (mem_of_supported hcomm fun k hk => ite_eq_left_iff.mpr fun h => absurd hk h)
    have hcov : ∃ k₀, ∀ k, k ∉ X i₀ → k = k₀ := by
      by_cases h : ∃ k₁, k₁ ∉ X i₀
      · obtain ⟨k₁, hk₁⟩ := h
        refine ⟨k₁, fun k₂ hk₂ => ?_⟩
        by_contra hne
        have hk1i : k₁ ≠ i₀ := fun h => hk₁ (h ▸ hXself i₀)
        have hk2i : k₂ ≠ i₀ := fun h => hk₂ (h ▸ hXself i₀)
        have h3 := pow_three_le_of_dual hιinj (H := H')
          ![Pi.single k₁ 1, Pi.single k₂ 1,
            (β i₀)⁻¹ • fun j => if j ∈ X i₀ then β j else 0] ![k₁, k₂, i₀] (fun x y => by
            fin_cases x <;> fin_cases y <;>
              simp [hne, Ne.symm hne, hk1i.symm, hk2i.symm, hk₁, hk₂, hXself i₀, hi₀])
          (ofAdd_sum_smul_mem _ fun x => by
            fin_cases x
            · exact hcomm k₁ hk₁
            · exact hcomm k₂ hk₂
            · exact StepTwoToral.ofAdd_smul_mem hvmem _)
        omega
      · push Not at h
        exact ⟨i₀, fun k hk => absurd (h k) hk⟩
    obtain ⟨k₀, hk₀⟩ := hcov
    have hch : ∀ j, ∃ u : (ZMod p)ˣ, u ∈ galSigns p (Nat.card F) ∧
        (j ∈ X i₀ → β j = (u : ZMod p) * β i₀) := by
      intro j
      by_cases hj : j ∈ X i₀
      · obtain ⟨u, huO, hu⟩ := (hX i₀ j).mp hj
        exact ⟨u, huO, fun _ => hu⟩
      · exact ⟨1, (galSigns _ _).one_mem, fun h => absurd h hj⟩
    choose ε hεO hε using hch
    refine Or.inr ⟨k₀, β i₀, ε, hi₀, hεO, fun j hj => hε j ?_, fun t ht0 hsum => ?_⟩
    · by_contra h
      exact hj (hk₀ j h)
    · refine hXc G F n p hp2 hns ψ hψ g hgd D c hbt hc s κ Φ ω hdec hcω β L₁ (X i₀)
        (fun j => (ε j)⁻¹) (β i₀) hi₀ (fun j => (galSigns _ _).inv_mem (hεO j))
        (fun j hj => ?_) hL₁ ?_ t (fun j hj => ?_) hsum
      · rw [hε j hj, ← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
      · intro a ha
        obtain ⟨Z, hZ, hZa⟩ := hL' ha
        exact ⟨Z, (mem_fixGrp Φ).mpr fun x hx => (mem_fixGrp Φ).mp hZ x ((hSoff i₀ x).mpr hx),
          hZa⟩
      · rw [hk₀ j hj]
        exact ht0
  ·
    exfalso
    push Not at hB
    have hcomm : ∀ k, nsCoord ψ hc hdec hcω (ofAdd (Pi.single k 1)) ∈ H' := by
      intro k
      by_cases hk0 : β k = 0
      · exact hunitZ hNZb k hk0
      · exact hunitX k ((hdich _ inf_le_right (hNX k hk0)).resolve_left (hB k hk0))
    have hs3 : 3 ≤ s := hs2
    have h3 := pow_three_le_of_dual hιinj (H := H')
      (fun a => Pi.single (Fin.castLE hs3 a) 1) (Fin.castLE hs3) (fun a b => by
        simp only [Pi.single_apply, (Fin.castLE_injective hs3).eq_iff]
        by_cases hab : a = b
        · simp [hab]
        · simp [hab, Ne.symm hab]) (ofAdd_sum_smul_mem _ fun a => hcomm _)
    omega

section Certified

theorem ggSpCoordModelNonsplitInput_of_cont (hZc : GGSpNsZeroContInput)
    (hXc : GGSpNsClassContInput) : GGSpCoordModelNonsplitInput :=
  ggSpCoordModelNonsplitInput_of_comp (ggSpNsFrameCompInput_of_cont hZc hXc)

end Certified

end CFSG.StandardType
