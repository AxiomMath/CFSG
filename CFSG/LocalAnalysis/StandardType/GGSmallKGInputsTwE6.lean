module

public import CFSG.LocalAnalysis.StandardType.GGSmallKGInputsTwE6Cent
public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6ThreeDelta

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley TableBExc.E6Three

namespace SmallKG

theorem isElemAbelian_map_comap {M R' A : Type*} [Group M] [Group R'] [Group A] {p : ℕ}
    {κ : M →* R'} (hκ : Function.Injective κ) (χ : M →* A) {X : Subgroup R'}
    (hX : IsElemAbelian p X) (hXr : X ≤ κ.range) :
    IsElemAbelian p ((X.comap κ).map χ) ∧ Nat.card (X.comap κ) = Nat.card X := by
  have hY : IsElemAbelian p (X.comap κ) := by
    refine ⟨⟨⟨fun a b => Subtype.ext (hκ ?_)⟩⟩, fun y hy => hκ ?_⟩
    · rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
      exact TableB.IsElemAbelian.comm hX a.2 b.2
    · rw [map_pow, hX.2 _ hy, map_one]
  refine ⟨TableB.isElemAbelian_map hY χ, ?_⟩
  conv_rhs => rw [← Subgroup.map_comap_eq_self hXr]
  exact (Subgroup.card_map_of_injective hκ).symm


variable {K : Type} [Field K]

variable (K) in
@[expose] def compatParam (σ : K →+* K) : Subgroup (Fin TwistTag.E6.tag.rank → Kˣ) where
  carrier := {b | ∀ i, b (TwistTag.E6.perm i) = Units.map σ.toMonoidHom (b i)}
  mul_mem' {a b} ha hb i := by
    rw [Pi.mul_apply, Pi.mul_apply, ha i, hb i, map_mul]
  one_mem' i := by
    simp
  inv_mem' {a} ha i := by
    rw [Pi.inv_apply, Pi.inv_apply, ha i, map_inv]

variable (K) in
@[expose] noncomputable def compatHat (σ : K →+* K) : Subgroup (ModGL TwistTag.E6.tag K) where
  carrier := {x | ∃ h ∈ graphFixedRootGroup TwistTag.E6 K σ, ∃ b ∈ compatParam K σ,
    x = h * rootDiagUnit TwistTag.E6.tag b}
  mul_mem' := by
    rintro _ _ ⟨h, hh, b, hb, rfl⟩ ⟨h', hh', b', hb', rfl⟩
    refine ⟨h * (rootDiagUnit TwistTag.E6.tag b * h' * (rootDiagUnit TwistTag.E6.tag b)⁻¹),
      mul_mem hh ((Subgroup.mem_normalizer_iff.1
        (rootDiagUnit_mem_normalizer_graphFixedRootGroup (t := TwistTag.E6) hb) h').1 hh'), b * b',
      mul_mem hb hb', ?_⟩
    rw [rootDiagUnit_mul]
    group
  one_mem' := ⟨1, one_mem _, 1, one_mem _, by rw [rootDiagUnit_one, mul_one]⟩
  inv_mem' := by
    rintro _ ⟨h, hh, b, hb, rfl⟩
    refine ⟨rootDiagUnit TwistTag.E6.tag b⁻¹ * h⁻¹ * (rootDiagUnit TwistTag.E6.tag b⁻¹)⁻¹,
      (Subgroup.mem_normalizer_iff.1 (rootDiagUnit_mem_normalizer_graphFixedRootGroup
        (t := TwistTag.E6) (inv_mem hb)) _).1 (inv_mem hh), b⁻¹, inv_mem hb, ?_⟩
    rw [← rootDiagUnit_inv]
    group

theorem compatHat_le_normalizer (σ : K →+* K) :
    compatHat K σ ≤ Subgroup.normalizer
      (graphFixedRootGroup TwistTag.E6 K σ : Set (ModGL TwistTag.E6.tag K)) := by
  rintro _ ⟨h, hh, b, hb, rfl⟩
  exact mul_mem (Subgroup.le_normalizer hh)
    (rootDiagUnit_mem_normalizer_graphFixedRootGroup (t := TwistTag.E6) hb)

theorem compatHat_le_hatGroup (σ : K →+* K) : compatHat K σ ≤ hatGroup TwistTag.E6.tag K := by
  rintro _ ⟨h, hh, b, -, rfl⟩
  exact ⟨h, (Subgroup.mem_inf.1 (graphFixedRootGroup_le TwistTag.E6 K σ hh)).1, b, rfl⟩

theorem eq_one_of_mem_compatHat_of_commute {σ : K →+* K} (hσ : Function.Surjective σ)
    {x : ModGL TwistTag.E6.tag K} (hx : x ∈ compatHat K σ)
    (hc : ∀ y ∈ graphFixedRootGroup TwistTag.E6 K σ, x * y = y * x) : x = 1 := by
  obtain ⟨h, hh, b, hb, rfl⟩ := hx
  exact eq_one_of_mul_rootDiagUnit_of_commute hσ hb hh hc

variable (K) in
noncomputable abbrev twH (n : ℕ) : Subgroup (LargeEvenChevGL TwistTag.E6.tag.cartan K) :=
  LargeEvenTwistedH TwistTag.E6.tag.cartan K TwistTag.E6.perm n

variable (K) in
abbrev twR (n : ℕ) : Type :=
  LargeEvenCenterQuot (twH K n)

section Transport

variable {n : ℕ} {σ : K →+* K}
  (T : ↥(graphFixedRootGroup TwistTag.E6 K σ) ≃* ↥(twH K n))
  (hZ : Subgroup.center ↥(twH K n) = ⊥)

@[expose] noncomputable def recipeEquiv :
    ↥(graphFixedRootGroup TwistTag.E6 K σ) ≃* twR K n :=
  MulEquiv.ofBijective ((LargeEvenCenterMk (twH K n)).comp T.toMonoidHom)
    ⟨by
      have hmk : Function.Injective (LargeEvenCenterMk (twH K n)) := by
        rw [← MonoidHom.ker_eq_bot_iff, LargeEvenCenterMk, QuotientGroup.ker_mk', hZ]
      exact hmk.comp T.injective,
    (QuotientGroup.mk'_surjective _).comp T.surjective⟩

theorem recipeEquiv_apply (g : ↥(graphFixedRootGroup TwistTag.E6 K σ)) :
    recipeEquiv T hZ g = LargeEvenCenterMk (twH K n) (T g) :=
  rfl

@[expose] noncomputable def recipeKappa :
    ↥(compatHat K σ) →* MulAut (twR K n) :=
  (MulAut.congr (recipeEquiv T hZ)).toMonoidHom.comp
    ((graphFixedRootGroup TwistTag.E6 K σ).normalizerMonoidHom.comp
      (Subgroup.inclusion (compatHat_le_normalizer σ)))

theorem recipeKappa_apply (x : ↥(compatHat K σ)) (g : ↥(graphFixedRootGroup TwistTag.E6 K σ)) :
    recipeKappa T hZ x (recipeEquiv T hZ g) = recipeEquiv T hZ
      ⟨(x : ModGL TwistTag.E6.tag K) * g * (x : ModGL TwistTag.E6.tag K)⁻¹,
        (Subgroup.mem_normalizer_iff.1 (compatHat_le_normalizer σ x.2) g).1 g.2⟩ := by
  simp only [recipeKappa, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.congr_apply,
    MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  rfl

theorem recipeKappa_injective (hσ : Function.Surjective σ) :
    Function.Injective (recipeKappa T hZ) := by
  refine (injective_iff_map_eq_one _).2 fun x hx => Subtype.ext ?_
  refine eq_one_of_mem_compatHat_of_commute hσ x.2 fun y hy => ?_
  have h1 := congrArg (fun f : MulAut (twR K n) => f (recipeEquiv T hZ ⟨y, hy⟩)) hx
  simp only [MulAut.one_apply] at h1
  rw [recipeKappa_apply] at h1
  have h2 : (x : ModGL TwistTag.E6.tag K) * y * (x : ModGL TwistTag.E6.tag K)⁻¹ = y :=
    congrArg Subtype.val ((recipeEquiv T hZ).injective h1)
  calc (x : ModGL TwistTag.E6.tag K) * y = (x : ModGL TwistTag.E6.tag K) * y *
        (x : ModGL TwistTag.E6.tag K)⁻¹ * x := by group
    _ = y * x := by rw [h2]

theorem conj_mem_range_recipeKappa (r : twR K n) :
    MulAut.conj r ∈ (recipeKappa T hZ).range := by
  obtain ⟨g, rfl⟩ := (recipeEquiv T hZ).surjective r
  refine ⟨⟨g, g, g.2, 1, one_mem _, by rw [rootDiagUnit_one, mul_one]⟩, ?_⟩
  ext r'
  obtain ⟨g', rfl⟩ := (recipeEquiv T hZ).surjective r'
  rw [recipeKappa_apply, MulAut.conj_apply, ← map_mul, ← map_inv, ← map_mul]
  rfl

theorem diag_mem_range_recipeKappa
    (e : Module.End K (RootModule TwistTag.E6.tag K) ≃*
      Module.End K (LargeEvenChevModule TwistTag.E6.tag.cartan K))
    (hT : ∀ g : ↥(graphFixedRootGroup TwistTag.E6 K σ),
      ((T g : LargeEvenChevGL TwistTag.E6.tag.cartan K) :
          Module.End K (LargeEvenChevModule TwistTag.E6.tag.cartan K)) =
        e ((g : ModGL TwistTag.E6.tag K) : Module.End K (RootModule TwistTag.E6.tag K)))
    (he : ∀ b : Fin TwistTag.E6.tag.rank → Kˣ,
      e (rootDiag b) = LargeEvenDiagMap TwistTag.E6.tag.cartan K b)
    {φ : MulAut (twR K n)} (hφ : φ ∈ LargeEvenChevDiagImage TwistTag.E6.tag.cartan K (twH K n)) :
    φ ∈ (recipeKappa T hZ).range := by
  obtain ⟨a, ha₁, -, ha⟩ := hφ
  have hrel : ∀ g g' : ↥(graphFixedRootGroup TwistTag.E6 K σ),
      ((T g' : LargeEvenChevGL TwistTag.E6.tag.cartan K) :
          Module.End K (LargeEvenChevModule TwistTag.E6.tag.cartan K)) *
          LargeEvenDiagMap TwistTag.E6.tag.cartan K a =
        LargeEvenDiagMap TwistTag.E6.tag.cartan K a *
          ((T g : LargeEvenChevGL TwistTag.E6.tag.cartan K) :
            Module.End K (LargeEvenChevModule TwistTag.E6.tag.cartan K)) ↔
      (g' : ModGL TwistTag.E6.tag K) * rootDiagUnit TwistTag.E6.tag a =
        rootDiagUnit TwistTag.E6.tag a * g := by
    intro g g'
    rw [hT, hT, ← he, ← map_mul, ← map_mul, e.injective.eq_iff, Units.ext_iff, Units.val_mul,
      Units.val_mul]
    rfl
  have hconj : ∀ g : ↥(graphFixedRootGroup TwistTag.E6 K σ), rootDiagUnit TwistTag.E6.tag a *
      (g : ModGL TwistTag.E6.tag K) * (rootDiagUnit TwistTag.E6.tag a)⁻¹ ∈
        graphFixedRootGroup TwistTag.E6 K σ := by
    intro g
    obtain ⟨h', hh'⟩ := ha₁ (T g)
    have h1 := (hrel g (T.symm h')).1 (by rw [T.apply_symm_apply]; exact hh')
    rw [← h1, mul_inv_cancel_right]
    exact (T.symm h').2
  have hca : a ∈ compatParam K σ := fun i =>
    TableB.TwE6.compat_of_forall_conj_mem (t := TwistTag.E6) (fun g hg => hconj ⟨g, hg⟩) i
  refine ⟨⟨rootDiagUnit TwistTag.E6.tag a, 1, one_mem _, a, hca, (one_mul _).symm⟩, ?_⟩
  ext r
  obtain ⟨g, rfl⟩ := (recipeEquiv T hZ).surjective r
  rw [recipeKappa_apply, recipeEquiv_apply, recipeEquiv_apply]
  refine (ha _ _ ((hrel g _).2 ?_)).symm
  change rootDiagUnit TwistTag.E6.tag a * g * (rootDiagUnit TwistTag.E6.tag a)⁻¹ *
      rootDiagUnit TwistTag.E6.tag a = rootDiagUnit TwistTag.E6.tag a * g
  group

theorem recipeI_subset_range
    (e : Module.End K (RootModule TwistTag.E6.tag K) ≃*
      Module.End K (LargeEvenChevModule TwistTag.E6.tag.cartan K))
    (hT : ∀ g : ↥(graphFixedRootGroup TwistTag.E6 K σ),
      ((T g : LargeEvenChevGL TwistTag.E6.tag.cartan K) :
          Module.End K (LargeEvenChevModule TwistTag.E6.tag.cartan K)) =
        e ((g : ModGL TwistTag.E6.tag K) : Module.End K (RootModule TwistTag.E6.tag K)))
    (he : ∀ b : Fin TwistTag.E6.tag.rank → Kˣ,
      e (rootDiag b) = LargeEvenDiagMap TwistTag.E6.tag.cartan K b) :
    LargeEvenChevIDImage TwistTag.E6.tag.cartan K (twH K n) ⊆
      ((recipeKappa T hZ).range : Set (MulAut (twR K n))) := by
  intro φ hφ
  refine (Subgroup.closure_le _).2 ?_ hφ
  rintro ψ (⟨r, rfl⟩ | hψ)
  · exact conj_mem_range_recipeKappa T hZ r
  · exact diag_mem_range_recipeKappa T hZ e hT he hψ

end Transport

theorem card_le_of_subset_recipeI [Finite K] {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 2) {X : Subgroup (MulAut (twR K n))} (hX : IsElemAbelian 3 X)
    (hXI : (X : Set (MulAut (twR K n))) ⊆
      LargeEvenChevIDImage TwistTag.E6.tag.cartan K (twH K n)) :
    Nat.card X ≤ 3 ^ 6 := by
  have : CharP K 2 := charP_two_of_card (m := n * 2) (by rw [hK, pow_mul])
  have h3 : 3 ∣ Nat.card K - 1 := by
    have h := Nat.sub_dvd_pow_sub_pow 4 1 n
    rw [hK, ← pow_mul, mul_comm, pow_mul]
    norm_num at h ⊢
    exact h
  set σ : K →+* K := iterateFrobenius K 2 n with hσdef
  have hσ : ∀ c, σ c = c ^ 2 ^ n := fun c => iterateFrobenius_def 2 n c
  have hsurj : Function.Surjective σ := Finite.surjective_of_injective σ.injective
  obtain ⟨e, T₀, hT₀, he⟩ := InnerDiagTwE6.exists_twistedTransport (K := K) n σ hσ
  have hΓ := (finite_fixed_root_group_perfect TwistTag.E6 Nat.prime_two hn K hK σ hσ).2.2.1
  have hZ : Subgroup.center ↥(twH K n) = ⊥ := TwE6Delta.center_recipeH_eq_bot hn hK
  set T : ↥(graphFixedRootGroup TwistTag.E6 K σ) ≃* ↥(twH K n) :=
    (MulEquiv.subgroupCongr hΓ.symm).trans T₀ with hTdef
  have hT : ∀ g : ↥(graphFixedRootGroup TwistTag.E6 K σ),
      ((T g : LargeEvenChevGL TwistTag.E6.tag.cartan K) :
          Module.End K (LargeEvenChevModule TwistTag.E6.tag.cartan K)) =
        e ((g : ModGL TwistTag.E6.tag K) : Module.End K (RootModule TwistTag.E6.tag K)) :=
    fun g => hT₀ _
  have hκ := recipeKappa_injective T hZ hsurj
  have hXr : X ≤ (recipeKappa T hZ).range := fun φ hφ =>
    recipeI_subset_range T hZ e hT he (hXI hφ)
  set χ : ↥(compatHat K σ) →* MulAut (adjointGroup TwistTag.E6.tag K) :=
    (hatAut TwistTag.E6.tag K).comp (Subgroup.inclusion (compatHat_le_hatGroup σ)) with hχdef
  have hχ : Function.Injective χ := by
    refine (injective_iff_map_eq_one _).2 fun x hx => Subtype.ext ?_
    refine eq_one_of_mem_compatHat_of_commute hsurj x.2 fun y hy => ?_
    have hyC : y ∈ adjointGroup TwistTag.E6.tag K :=
      (Subgroup.mem_inf.1 (graphFixedRootGroup_le TwistTag.E6 K σ hy)).1
    have h1 := congrArg (fun f : MulAut (adjointGroup TwistTag.E6.tag K) =>
      ((f ⟨y, hyC⟩ : adjointGroup TwistTag.E6.tag K) : ModGL TwistTag.E6.tag K)) hx
    have h2 : (x : ModGL TwistTag.E6.tag K) * y * (x : ModGL TwistTag.E6.tag K)⁻¹ = y := h1
    calc (x : ModGL TwistTag.E6.tag K) * y = (x : ModGL TwistTag.E6.tag K) * y *
          (x : ModGL TwistTag.E6.tag K)⁻¹ * x := by group
      _ = y * x := by rw [h2]
  obtain ⟨hab, hcard⟩ := isElemAbelian_map_comap hκ χ hX hXr
  have hle : (X.comap (recipeKappa T hZ)).map χ ≤ (hatAut TwistTag.E6.tag K).range := by
    rintro _ ⟨y, -, rfl⟩
    exact ⟨_, rfl⟩
  have h6 : Nat.card ((X.comap (recipeKappa T hZ)).map χ) ≤ 3 ^ 6 :=
    (card_le_and_normalizes_of_le_hatAut h3 hab hle).1
  rwa [Subgroup.card_map_of_injective hχ, hcard] at h6

end SmallKG

theorem ggTwE6ThreeInndiagRankInput_holds :
    GGTwE6ThreeInndiagRankInput :=
  fun _ _ _ _ hn hK _ _ hX hXI => SmallKG.card_le_of_subset_recipeI hn hK hX hXI

end CFSG.StandardType
