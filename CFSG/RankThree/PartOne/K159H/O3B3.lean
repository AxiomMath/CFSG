module

public import CFSG.RankThree.PartOne.K159H.O3B3Blocks
public import CFSG.RankThree.PartOne.K159H.O3Comm

public noncomputable section

namespace CFSG.RankThree.PartOne.K159H

open CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
  CFSG.ClassicalGroups.Orthogonal QuadraticMap CFSG.LieType.Universal.Spin
  CFSG.RankThree.OrthogonalInvolutions Module CFSG.RankThree.PartOne.KFR4

variable {K : Type} [Field K] {A : Type} [AddCommGroup A] [Module K A] {p : ℕ} [NeZero p] {ζ : Kˣ}

@[expose] def torP (hζ : IsPrimitiveRoot ζ p) : Multiplicative (Vec p) →* VG K A 3 :=
  (torH K A 3).comp (dHom hζ.pow_eq_one)

theorem torP_apply (hζ : IsPrimitiveRoot ζ p) (v : Vec p) :
    torP (K := K) (A := A) hζ (Multiplicative.ofAdd v) = torH K A 3 (dOf ζ v) := rfl

theorem torP_injective (hζ : IsPrimitiveRoot ζ p) : Function.Injective (torP (K := K) (A := A) hζ) :=
  (torH_injective 3).comp (dHom_injective hζ)

variable (qA : QuadraticForm K A)

@[expose] def Tg (hζ : IsPrimitiveRoot ζ p) : Subgroup ↥(Om qA 3) :=
  (torP (K := K) (A := A) hζ).range.subgroupOf (Om qA 3)

variable {qA}

section Model

variable [Finite K] [CharP K 2] [FiniteDimensional K A]

theorem torP_range_le (hreg : (polarBilin qA).Nondegenerate) (hζ : IsPrimitiveRoot ζ p) :
    (torP (K := K) (A := A) hζ).range ≤ Om qA 3 := by
  rintro _ ⟨v, rfl⟩
  exact torH_mem_Om hreg le_rfl _

@[expose] def eT (hreg : (polarBilin qA).Nondegenerate) (hζ : IsPrimitiveRoot ζ p) :
    Multiplicative (Vec p) ≃* ↥(Tg qA hζ) :=
  (MonoidHom.ofInjective (torP_injective (K := K) (A := A) hζ)).trans
    (Subgroup.subgroupOfEquivOfLe (torP_range_le hreg hζ)).symm

theorem eT_val (hreg : (polarBilin qA).Nondegenerate) (hζ : IsPrimitiveRoot ζ p) (v : Vec p) :
    ((eT hreg hζ (Multiplicative.ofAdd v) : ↥(Tg qA hζ)) : ↥(Om qA 3)).1 = torH K A 3 (dOf ζ v) := rfl

theorem val_eq_torH (hreg : (polarBilin qA).Nondegenerate) (hζ : IsPrimitiveRoot ζ p) (x : ↥(Tg qA hζ)) :
    ((x : ↥(Om qA 3)) : VG K A 3) = torH K A 3 (dOf ζ (lin (eT hreg hζ).symm x)) := by
  have h : eT hreg hζ (Multiplicative.ofAdd (lin (eT hreg hζ).symm x)) = x := by
    simp [lin]
  have := eT_val hreg hζ (lin (eT hreg hζ).symm x)
  rw [h] at this
  exact this

theorem card_Tg (hreg : (polarBilin qA).Nondegenerate) (hζ : IsPrimitiveRoot ζ p) :
    Nat.card ↥(Tg qA hζ) = p ^ 3 := by
  rw [← Nat.card_congr (eT hreg hζ).toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_zmod]
  simp


theorem normal_bot_or_eq {Γ : Type*} [Group Γ] (B : Subgroup Γ) [IsSimpleGroup ↥B] (N : Subgroup Γ) (hN : N ≤ B)
    (hnorm : (N.subgroupOf B).Normal) : N = ⊥ ∨ N = B := by
  have : (N.subgroupOf B).Normal := hnorm
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.subgroupOf B) with h | h
  · left
    have := congrArg (Subgroup.map B.subtype) h
    rwa [Subgroup.map_subgroupOf_eq_of_le hN, Subgroup.map_bot] at this
  · right
    have := congrArg (Subgroup.map B.subtype) h
    rwa [Subgroup.map_subgroupOf_eq_of_le hN, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at this

omit [Finite K] [CharP K 2] [FiniteDimensional K A] in
theorem exists_ne_one_unit (hK : 4 ≤ Nat.card K) : ∃ u : Kˣ, u ≠ 1 := by
  by_contra hno
  push Not at hno
  have : Nat.card K ≤ 2 := by
    have hsub : Subsingleton Kˣ := ⟨fun a b => (hno a).trans (hno b).symm⟩
    have : Nat.card Kˣ = 1 := Nat.card_eq_one_iff_unique.2 ⟨hsub, ⟨1⟩⟩
    rw [Nat.card_units] at this
    omega
  omega

theorem block_simple_aux (hK : 4 ≤ Nat.card K) (hreg : (polarBilin qA).Nondegenerate) (hani : qA.Anisotropic)
    (hdim : finrank K A = 2) (ρ : Root) (N : Subgroup ↥(Om qA 3))
    (hN : N ≤ (Bblock qA ρ).subgroupOf (Om qA 3))
    (hnorm : (N.subgroupOf ((Bblock qA ρ).subgroupOf (Om qA 3))).Normal) :
    N = ⊥ ∨ N = (Bblock qA ρ).subgroupOf (Om qA 3) := by
  have : IsSimpleGroup ↥(Bblock qA ρ) := Bblock_simple hK hreg hani hdim ρ
  have : IsSimpleGroup ↥((Bblock qA ρ).subgroupOf (Om qA 3)) :=
    (Subgroup.subgroupOfEquivOfLe (Bblock_le_Om hreg ρ)).isSimpleGroup
  exact normal_bot_or_eq _ N hN hnorm

theorem block_perfect_aux (hK : 4 ≤ Nat.card K) (hreg : (polarBilin qA).Nondegenerate) (hani : qA.Anisotropic)
    (hdim : finrank K A = 2) (ρ : Root) :
    ⁅(Bblock qA ρ).subgroupOf (Om qA 3), (Bblock qA ρ).subgroupOf (Om qA 3)⁆ =
      (Bblock qA ρ).subgroupOf (Om qA 3) :=
  CFSG.RankThree.PartOne.KFCL.commutator_subgroupOf_eq' (Bblock_le_Om hreg ρ)
    (Bblock_perfect hK hreg hani hdim ρ)

theorem block_cent_aux (hK : 4 ≤ Nat.card K) (hreg : (polarBilin qA).Nondegenerate)
    (hζ : IsPrimitiveRoot ζ p) (ρ : Root) :
    (Bblock qA ρ).subgroupOf (Om qA 3) ≤
      Subgroup.centralizer ((hypS (eT hreg hζ).symm ρ : Subgroup ↥(Om qA 3)) : Set ↥(Om qA 3)) := by
  intro y hy
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  obtain ⟨hxT, hx0⟩ := mem_hypS.1 hx
  apply Subtype.ext
  have h1 := Bblock_comm_torH (exists_ne_one_unit hK) hreg hζ hx0 (Subgroup.mem_subgroupOf.1 hy)
  have h2 := val_eq_torH hreg hζ ⟨x, hxT⟩
  change x.1 * y.1 = y.1 * x.1
  rw [show x.1 = torH K A 3 (dOf ζ (lin (eT hreg hζ).symm ⟨x, hxT⟩)) from h2]
  exact h1.symm

theorem block_T_aux (hreg : (polarBilin qA).Nondegenerate) (hζ : IsPrimitiveRoot ζ p) (ρ : Root)
    (x : ↥(Tg qA hζ)) :
    (x : ↥(Om qA 3)) ∈ (Bblock qA ρ).subgroupOf (Om qA 3) ↔ x ∈ lineT (eT hreg hζ).symm ρ := by
  rw [Subgroup.mem_subgroupOf, val_eq_torH hreg hζ x, torH_dOf_mem_Bblock_iff hreg hζ, mem_lineT]


abbrev S0 (S : Subgroup ↥(Om qA 3)) : Subgroup (Fin 3 → Kˣ) :=
  (S.map (Om qA 3).subtype).comap (torH K A 3)

theorem dOf_mem_S0 (hreg : (polarBilin qA).Nondegenerate) (hζ : IsPrimitiveRoot ζ p) {S : Subgroup ↥(Om qA 3)}
    (hST : S ≤ Tg qA hζ) {x : ↥(Om qA 3)} (hx : x ∈ S) :
    dOf ζ (lin (eT hreg hζ).symm ⟨x, hST hx⟩) ∈ S0 S :=
  ⟨x, hx, val_eq_torH hreg hζ ⟨x, hST hx⟩⟩

theorem derived_le_aux (hreg : (polarBilin qA).Nondegenerate) (hani : qA.Anisotropic) (hdim : finrank K A = 2)
    (hζ : IsPrimitiveRoot ζ p) {S : Subgroup ↥(Om qA 3)} (hST : S ≤ Tg qA hζ) (hS : S ≠ ⊥) :
    ⁅Subgroup.centralizer (S : Set ↥(Om qA 3)), Subgroup.centralizer (S : Set ↥(Om qA 3))⁆ ≤
      ⨆ i : {i : Root // S ≤ hypS (eT hreg hζ).symm i}, (Bblock qA i.1).subgroupOf (Om qA 3) := by
  classical
  have hnt : ∃ j, ¬ TrivOn (S0 S) j := by
    obtain ⟨⟨x, hxS⟩, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hS
    by_contra hno
    push Not at hno
    apply hx1
    have hd := dOf_mem_S0 hreg hζ hST hxS
    have hd1 : dOf ζ (lin (eT hreg hζ).symm ⟨x, hST hxS⟩) = 1 := by
      funext k
      have := hno (Sum.inl k) _ hd
      simpa [wt_inl] using this
    have hx' : (x : VG K A 3) = 1 := by
      rw [show (x : VG K A 3) = torH K A 3 (dOf ζ (lin (eT hreg hζ).symm ⟨x, hST hxS⟩)) from
        val_eq_torH hreg hζ ⟨x, hST hxS⟩, hd1, map_one]
    exact Subtype.ext (Subtype.ext hx')
  have hC : ∀ y ∈ Subgroup.centralizer (S : Set ↥(Om qA 3)), (y : VG K A 3) ∈ Csub qA (S0 S) := by
    intro y hy
    refine mem_Csub.2 ⟨y.2, mem_CO.2 ⟨Om_le_orth y.2, fun d hd => ?_⟩⟩
    obtain ⟨s, hs, hsd⟩ := Subgroup.mem_map.1 hd
    have h1 := congrArg Subtype.val (Subgroup.mem_centralizer_iff.1 hy s hs)
    have h2 : (s : VG K A 3) * (y : VG K A 3) = (y : VG K A 3) * (s : VG K A 3) := h1
    have h3 : (s : VG K A 3) = torH K A 3 d := hsd
    rw [← h3]
    exact h2.symm
  have hcomm : ∀ z ∈ ⁅Subgroup.centralizer (S : Set ↥(Om qA 3)), Subgroup.centralizer (S : Set ↥(Om qA 3))⁆,
      (z : VG K A 3) ∈ Rts qA (S0 S) := by
    intro z hz
    have hmap : (⁅Subgroup.centralizer (S : Set ↥(Om qA 3)), Subgroup.centralizer (S : Set ↥(Om qA 3))⁆).map
        (Om qA 3).subtype ≤ ⁅Csub qA (S0 S), Csub qA (S0 S)⁆ := by
      rw [Subgroup.map_commutator]
      refine Subgroup.commutator_mono ?_ ?_ <;> (rintro _ ⟨y, hy, rfl⟩; exact hC y hy)
    exact derived_Csub_le hreg hani hdim rfl hnt (hmap ⟨z, hz, rfl⟩)
  have hyp : ∀ ρ : Root, (∀ v : Vec p, dOf ζ v ∈ S0 S → ρ.vecp p ⬝ᵥ v = 0) →
      S ≤ hypS (eT hreg hζ).symm ρ := by
    intro ρ hρ x hx
    exact (mem_hypS_coe (eT hreg hζ).symm (ρ := ρ) (x := ⟨x, hST hx⟩)).2
      (hρ _ (dOf_mem_S0 hreg hζ hST hx))
  have hRts : Rts qA (S0 S) ≤ ⨆ i : {i : Root // S ≤ hypS (eT hreg hζ).symm i}, Bblock qA i.1 := by
    refine (Subgroup.closure_le _).2 ?_
    rintro g (⟨t, j, j', hne, hsim, rfl⟩ | ⟨j, a, hj, rfl⟩)
    · obtain ⟨ρ, hρ, hv⟩ := rEl_block (qA := qA) hζ hne
      have hSρ : S ≤ hypS (eT hreg hζ).symm ρ := hyp ρ fun v hvS => hv v (hsim _ hvS)
      exact le_iSup (fun i : {i : Root // S ≤ hypS (eT hreg hζ).symm i} => Bblock qA i.1) ⟨ρ, hSρ⟩ (hρ t)
    · obtain ⟨ρ, hρ, hv⟩ := eichler_block hreg hζ j
      have hSρ : S ≤ hypS (eT hreg hζ).symm ρ := hyp ρ fun v hvS => hv v (hj _ hvS)
      exact le_iSup (fun i : {i : Root // S ≤ hypS (eT hreg hζ).symm i} => Bblock qA i.1) ⟨ρ, hSρ⟩ (hρ a)
  intro z hz
  have hz1 : (z : VG K A 3) ∈ ⨆ i : {i : Root // S ≤ hypS (eT hreg hζ).symm i}, Bblock qA i.1 :=
    hRts (hcomm z hz)
  rw [← CFSG.RankThree.PartOne.KFCL.subgroupOf_iSup (C := Om qA 3)
    (fun i : {i : Root // S ≤ hypS (eT hreg hζ).symm i} => Bblock qA i.1) (fun i => Bblock_le_Om hreg i.1)]
  exact hz1

theorem realize_aux (hreg : (polarBilin qA).Nondegenerate) (hani : qA.Anisotropic) (hdim : finrank K A = 2)
    (hζ : IsPrimitiveRoot ζ p) (ρ : Root) :
    ∃ w ∈ Subgroup.normalizer ((Tg qA hζ : Subgroup ↥(Om qA 3)) : Set ↥(Om qA 3)),
      ∀ x : ↥(Tg qA hζ), w * (x : ↥(Om qA 3)) * w⁻¹ = (reflT (eT hreg hζ).symm ρ x : ↥(Om qA 3)) := by
  obtain ⟨n, hnΩ, hnn, hconj⟩ := exists_realize hreg hani hdim hζ ρ
  set w : ↥(Om qA 3) := ⟨n, hnΩ⟩ with hw
  have hww : w * w = 1 := Subtype.ext hnn
  have hwinv : w⁻¹ = w := inv_eq_of_mul_eq_one_right hww
  have key : ∀ x : ↥(Tg qA hζ), w * (x : ↥(Om qA 3)) * w⁻¹ =
      (reflT (eT hreg hζ).symm ρ x : ↥(Om qA 3)) := by
    intro x
    apply Subtype.ext
    rw [hwinv]
    have h1 : ((reflT (eT hreg hζ).symm ρ x : ↥(Tg qA hζ)) : ↥(Om qA 3)).1 =
        torH K A 3 (dOf ζ (reflLin p ρ (lin (eT hreg hζ).symm x))) := by
      rw [val_eq_torH hreg hζ, lin_reflT]
    show n * ((x : ↥(Om qA 3)) : VG K A 3) * n = _
    rw [h1, val_eq_torH hreg hζ x]
    exact hconj _
  refine ⟨w, ?_, key⟩
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    have h2 := (reflT (eT hreg hζ).symm ρ ⟨y, hy⟩).2
    rwa [← key ⟨y, hy⟩] at h2
  · intro hy
    have h2 := (reflT (eT hreg hζ).symm ρ ⟨w * y * w⁻¹, hy⟩).2
    rw [← key ⟨w * y * w⁻¹, hy⟩] at h2
    have h3 : w * (w * y * w⁻¹) * w⁻¹ = y := by
      rw [hwinv]
      calc w * (w * y * w) * w = (w * w) * y * (w * w) := by group
        _ = y := by rw [hww]; simp
    rwa [h3] at h2


@[expose] def b3Data (hp : p.Prime) (hK : 4 ≤ Nat.card K) (hreg : (polarBilin qA).Nondegenerate)
    (hani : qA.Anisotropic) (hdim : finrank K A = 2) (hζ : IsPrimitiveRoot ζ p) :
    B3Data p (Tg qA hζ) where
  c := (eT hreg hζ).symm
  block ρ := (Bblock qA ρ).subgroupOf (Om qA 3)
  block_simple := fun ρ N hN hnorm => block_simple_aux hK hreg hani hdim ρ N hN hnorm
  block_perfect := fun ρ => block_perfect_aux hK hreg hani hdim ρ
  block_cent := fun ρ => block_cent_aux hK hreg hζ ρ
  block_T := fun ρ x => block_T_aux hreg hζ ρ x
  derived_le := fun S hST hshape => derived_le_aux hreg hani hdim hζ hST (by
    rintro rfl
    rcases hshape with h | ⟨e, -, he1, he⟩
    · rw [Subgroup.relIndex_bot_left, card_Tg hreg hζ] at h
      have h' : p ^ 3 = p ^ 1 := by rw [pow_one]; exact h
      have := Nat.pow_right_injective hp.two_le h'
      omega
    · exact he1 (Subgroup.zpowers_eq_bot.1 he.symm))
  realize := fun ρ => realize_aux hreg hani hdim hζ ρ

theorem exists_rootData_tail (hp : p.Prime) (hp5 : 5 ≤ p) (hK : 4 ≤ Nat.card K)
    (hreg : (polarBilin qA).Nondegenerate) (hani : qA.Anisotropic) (hdim : finrank K A = 2)
    (hζ : IsPrimitiveRoot ζ p) :
    ∃ R : CFSG.RankThree.PartOne.KFCL.RootData p (Tg qA hζ), Nonempty (R.ReflData 48) :=
  (b3Data hp hK hreg hani hdim hζ).exists_rootData hp hp5

end Model

end CFSG.RankThree.PartOne.K159H
