module

public import CFSG.RankThree.PartTwo.Sec21.Item211LieProofL3
import CFSG.RankThree.PartTwo.Sec21.Item211Lie2ProofL3Minus
import CFSG.RankThree.PartTwo.Sec21.Item211Lie2ProofL3Inner
import CFSG.RankThree.PartTwo.Sec21.Item211Lie2ProofU42Char
import CFSG.Quasithin.EmptyFaithful.E22SUFrame
import CFSG.RankThree.PartTwo.Sec4.Item47Bridges
import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
public import CFSG.Quasithin.EmptyFaithful.E22SLift

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.ClassicalGroups.UnitaryFlag
open scoped commutatorElement

namespace Item211Lie2Proof

@[expose] def L3PlusFor (Y : Type*) [Group Y] : Prop :=
  ∀ D T V W : Subgroup (MulAut Y), IsElemAbelian 3 D → Nat.card D = 9 → IsPGroup 2 T →
    T ≠ ⊥ → T ≤ Subgroup.centralizer (D : Set (MulAut Y)) →
    V ≤ (MulAut.conj : Y →* MulAut Y).range → IsPGroup 2 V →
    D ≤ Subgroup.normalizer (V : Set (MulAut Y)) → ⁅V, D⁆ = V →
    V ≤ Subgroup.centralizer (T : Set (MulAut Y)) → IsPGroup 2 W → V ≤ W →
    W ≤ Subgroup.centralizer (T : Set (MulAut Y)) →
    (∀ τ ∈ (MulAut.conj : Y →* MulAut Y).range ⊓ Subgroup.centralizer (T : Set (MulAut Y)),
      τ ^ 3 = 1 → τ ∈ Subgroup.normalizer (W : Set (MulAut Y))) →
    V = ⊥

@[expose] def L3PlusCoreFor (Y : Type*) [Group Y] : Prop :=
  ∀ D T V W : Subgroup (MulAut Y), IsElemAbelian 3 D → Nat.card D = 9 → IsPGroup 2 T →
    T ≠ ⊥ → T ≤ Subgroup.centralizer (D : Set (MulAut Y)) →
    ¬ (∀ a ∈ (MulAut.conj : Y →* MulAut Y).range ⊓ Subgroup.centralizer
        ((T ⊓ (MulAut.conj : Y →* MulAut Y).range : Subgroup (MulAut Y)) : Set (MulAut Y)),
      ∀ b ∈ (MulAut.conj : Y →* MulAut Y).range ⊓ Subgroup.centralizer
        ((T ⊓ (MulAut.conj : Y →* MulAut Y).range : Subgroup (MulAut Y)) : Set (MulAut Y)),
      a * b = b * a) →
    V ≤ (MulAut.conj : Y →* MulAut Y).range → IsPGroup 2 V →
    D ≤ Subgroup.normalizer (V : Set (MulAut Y)) → ⁅V, D⁆ = V →
    V ≤ Subgroup.centralizer (T : Set (MulAut Y)) → IsPGroup 2 W → V ≤ W →
    W ≤ Subgroup.centralizer (T : Set (MulAut Y)) →
    (∀ τ ∈ (MulAut.conj : Y →* MulAut Y).range ⊓ Subgroup.centralizer (T : Set (MulAut Y)),
      τ ^ 3 = 1 → τ ∈ Subgroup.normalizer (W : Set (MulAut Y))) →
    V = ⊥

theorem l3PlusFor_of_hom {X Y : Type*} [Group X] [Group Y] (Φ : MulAut X →* MulAut Y)
    (hΦ : Function.Injective Φ)
    (hinn : ∀ x : X, Φ (MulAut.conj x) ∈ (MulAut.conj : Y →* MulAut Y).range)
    (hsurj : ∀ y : Y, ∃ x : X, Φ (MulAut.conj x) = MulAut.conj y)
    (hY : L3PlusFor Y) : L3PlusFor X := by
  intro D T V W hDe hD9 hT2 hT1 hTD hVi hV2 hDV hVD hVT hW2 hVW hWT hτ
  have hinn' : ∀ τ ∈ (MulAut.conj : X →* MulAut X).range,
      Φ τ ∈ (MulAut.conj : Y →* MulAut Y).range := by
    rintro _ ⟨x, rfl⟩
    exact hinn x
  have hcentle : ∀ {S R : Subgroup (MulAut X)}, R ≤ Subgroup.centralizer (S : Set (MulAut X)) →
      R.map Φ ≤ Subgroup.centralizer ((S.map Φ : Subgroup (MulAut Y)) : Set (MulAut Y)) := by
    intro S R hR
    rintro _ ⟨r, hr, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨s, hs, rfl⟩
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.mp (hR hr) s hs]
  have hDe' : IsElemAbelian 3 (D.map Φ) := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, ?_⟩
    · obtain ⟨_, ⟨x, hx, rfl⟩⟩ := a
      obtain ⟨_, ⟨y, hy, rfl⟩⟩ := b
      simp only [Subgroup.coe_mul]
      have h0 : x * y = y * x := congrArg Subtype.val (hDe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
      rw [← map_mul, ← map_mul, h0]
    · rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow, hDe.2 x hx, map_one]
  have hτ' : ∀ τ' ∈ (MulAut.conj : Y →* MulAut Y).range ⊓
      Subgroup.centralizer ((T.map Φ : Subgroup (MulAut Y)) : Set (MulAut Y)),
      τ' ^ 3 = 1 → τ' ∈ Subgroup.normalizer ((W.map Φ : Subgroup (MulAut Y)) : Set (MulAut Y)) := by
    intro τ' hτ' hτ'3
    obtain ⟨⟨y, rfl⟩, hτ'T⟩ := Subgroup.mem_inf.mp hτ'
    obtain ⟨x, hx⟩ := hsurj y
    have hxT : MulAut.conj x ∈ Subgroup.centralizer (T : Set (MulAut X)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro s hs
      apply hΦ
      rw [map_mul, map_mul, hx]
      exact Subgroup.mem_centralizer_iff.mp hτ'T _ ⟨s, hs, rfl⟩
    have hx3 : (MulAut.conj x) ^ 3 = 1 := by
      apply hΦ
      rw [map_pow, hx, map_one]
      exact hτ'3
    have h1 := hτ _ (Subgroup.mem_inf.mpr ⟨⟨x, rfl⟩, hxT⟩) hx3
    rw [← hx]
    exact Subgroup.le_normalizer_map Φ ⟨_, h1, rfl⟩
  have hV' := hY (D.map Φ) (T.map Φ) (V.map Φ) (W.map Φ) hDe'
    (by rw [Subgroup.card_map_of_injective hΦ, hD9]) (hT2.map Φ)
    (fun h => hT1 ((Subgroup.map_eq_bot_iff_of_injective T hΦ).mp h)) (hcentle hTD)
    (fun _ ⟨v, hv, e⟩ => e ▸ hinn' v (hVi hv)) (hV2.map Φ)
    ((Subgroup.map_mono hDV).trans (Subgroup.le_normalizer_map Φ))
    (by rw [← Subgroup.map_commutator, hVD]) (hcentle hVT) (hW2.map Φ) (Subgroup.map_mono hVW)
    (hcentle hWT) hτ'
  exact (Subgroup.map_eq_bot_iff_of_injective V hΦ).mp hV'

theorem l3PlusFor_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (hY : L3PlusFor Y) : L3PlusFor X :=
  l3PlusFor_of_hom (MulAut.congr e).toMonoidHom (MulAut.congr e).injective
    (fun x => ⟨e x, by
      ext y
      simp [MulAut.conj_apply, MulAut.congr_apply]⟩)
    (fun y => ⟨e.symm y, by
      ext z
      simp [MulAut.conj_apply, MulAut.congr_apply]⟩) hY

theorem l3PlusFor_of_perfect {S : Type*} [Group S] [Group.IsPerfect S]
    (hP : L3PlusFor (S ⧸ Subgroup.center S)) : L3PlusFor S := by
  refine l3PlusFor_of_hom (KFacts.centerDescend S) (fun α β hαβ => ?_) (fun s => ⟨s, ?_⟩)
    (fun y => ?_) hP
  · refine Sec4.mulAut_eq_of_inv_mul_mem_center fun x => ?_
    have h1 := congrArg (fun σ : MulAut (S ⧸ Subgroup.center S) =>
      σ (x : S ⧸ Subgroup.center S)) hαβ
    simp only [KFacts.centerDescend_mk] at h1
    exact (QuotientGroup.eq).mp h1.symm
  · ext x
    induction x using QuotientGroup.induction_on with
    | H y => rfl
  · obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective y
    refine ⟨s, ?_⟩
    ext x
    induction x using QuotientGroup.induction_on with
    | H y => rfl

theorem eq_bot_of_comm_of_fixed {M : Type*} [Group M] {V D : Subgroup M} [Finite V] [Finite D]
    (hVc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a) (hDodd : Odd (Nat.card D)) (hV2 : IsPGroup 2 V)
    (hDV : D ≤ Subgroup.normalizer (V : Set M)) (hVD : ⁅V, D⁆ = V)
    (hfix : ∀ v ∈ V, v ^ 2 = 1 → ∀ d ∈ D, d * v = v * d) : V = ⊥ := by
  classical
  have : Fintype D := Fintype.ofFinite D
  have : Fintype V := Fintype.ofFinite V
  let : CommGroup V := { (inferInstance : Group V) with
    mul_comm := fun a b => Subtype.ext (hVc _ a.2 _ b.2) }
  have hact : ∀ d : D, ∀ v : V, (d : M) * v * (d : M)⁻¹ ∈ V := fun d v =>
    (Subgroup.mem_normalizer_iff.mp (hDV d.2) v).mp v.2
  let act : D → V → V := fun d v => ⟨(d : M) * v * (d : M)⁻¹, hact d v⟩
  let N : V → V := fun v => ∏ d : D, act d v
  have hNmul : ∀ v w : V, N (v * w) = N v * N w := by
    intro v w
    simp only [N, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun d _ => Subtype.ext ?_
    simp only [act, Subgroup.coe_mul]
    group
  have hNone : N 1 = 1 := by
    simp only [N]
    refine Finset.prod_eq_one fun d _ => Subtype.ext ?_
    simp [act]
  have hNact : ∀ (d₀ : D) (v : V), N (act d₀ v) = N v := by
    intro d₀ v
    simp only [N]
    refine Fintype.prod_equiv (Equiv.mulRight d₀) _ _ fun d => Subtype.ext ?_
    simp only [act, Equiv.coe_mulRight, Subgroup.coe_mul, mul_inv_rev]
    group
  let Nh : V →* V := { toFun := N, map_one' := hNone, map_mul' := hNmul }
  have hle : ⁅V, D⁆ ≤ Nh.ker.map V.subtype := by
    rw [Subgroup.commutator_le]
    intro v hv d hd
    have hcV : ⁅v, d⁆ ∈ V := by
      rw [commutatorElement_def]
      have h1 : d * v⁻¹ * d⁻¹ ∈ V := hact ⟨d, hd⟩ ⟨v⁻¹, V.inv_mem hv⟩
      have e : v * d * v⁻¹ * d⁻¹ = v * (d * v⁻¹ * d⁻¹) := by group
      rw [e]
      exact V.mul_mem hv h1
    refine ⟨⟨⁅v, d⁆, hcV⟩, ?_, rfl⟩
    have e : (⟨⁅v, d⁆, hcV⟩ : V) = ⟨v, hv⟩ * act ⟨d, hd⟩ (⟨v, hv⟩⁻¹) := by
      apply Subtype.ext
      simp only [act, Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
      group
    change Nh ⟨⁅v, d⁆, hcV⟩ = 1
    rw [e]
    change N (⟨v, hv⟩ * act ⟨d, hd⟩ (⟨v, hv⟩⁻¹)) = 1
    rw [hNmul, hNact, ← hNmul, mul_inv_cancel, hNone]
  by_contra hV
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hV2
  have hn0 : n ≠ 0 := by
    rintro rfl
    apply hV
    rw [pow_zero] at hn
    exact Subgroup.eq_bot_of_card_eq V hn
  have h2 : 2 ∣ Fintype.card V := by
    rw [← Nat.card_eq_fintype_card, hn]
    exact dvd_pow_self 2 hn0
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card 2 h2
  have ht2 : t ^ 2 = 1 := by rw [← ht]; exact pow_orderOf_eq_one t
  have ht1 : t ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ht
    omega
  have hfixt : ∀ d : D, act d t = t := by
    intro d
    apply Subtype.ext
    have h1 := hfix t t.2 (by rw [← Subgroup.coe_pow, ht2, Subgroup.coe_one]) d d.2
    change (d : M) * t * (d : M)⁻¹ = t
    rw [h1, mul_inv_cancel_right]
  have hNt : N t = t ^ Fintype.card D := by
    simp only [N, hfixt, Finset.prod_const, Finset.card_univ]
  obtain ⟨y, hy, hyt⟩ := hle (by rw [hVD]; exact t.2)
  have hyt' : y = t := Subtype.ext hyt
  have hy' : N t = 1 := by
    rw [← hyt']
    exact hy
  rw [hNt] at hy'
  have hy := hy'
  obtain ⟨k, hk⟩ := hDodd
  rw [← Nat.card_eq_fintype_card, hk, pow_succ, pow_mul, ht2, one_pow, one_mul] at hy
  exact ht1 hy

theorem commute_of_card_le_four {M : Type*} [Group M] {F : Subgroup M} (hF4 : Nat.card F ≤ 4)
    [Finite F] {d t : M} (hd3 : d ^ 3 = 1) (htF : t ∈ F) (ht1 : t ≠ 1) (hdt : d * t = t * d)
    (hdF : ∀ c ∈ F, d * c * d⁻¹ ∈ F) {c : M} (hc : c ∈ F) : d * c = c * d := by
  by_contra hdc
  have hinj : ∀ x y : M, d * x * d⁻¹ = d * y * d⁻¹ → x = y := fun x y h => by
    simpa using h
  have hd1 : d * 1 * d⁻¹ = 1 := by group
  have hdt' : d * t * d⁻¹ = t := by rw [hdt, mul_inv_cancel_right]
  set c₁ := d * c * d⁻¹ with hc₁
  set c₂ := d * c₁ * d⁻¹ with hc₂
  have hc₁c : c₁ ≠ c := fun h => hdc (by rw [← mul_inv_eq_iff_eq_mul, ← hc₁, h])
  have hc₂' : d * c₂ * d⁻¹ = c := by
    have e : d * c₂ * d⁻¹ = d ^ 3 * c * (d ^ 3)⁻¹ := by
      rw [hc₂, hc₁, pow_three]
      group
    rw [e, hd3, one_mul, inv_one, mul_one]
  have hc1 : c ≠ 1 := fun h => hc₁c (by rw [hc₁, h, hd1])
  have hct : c ≠ t := fun h => hc₁c (by rw [hc₁, h, hdt'])
  have hc₁1 : c₁ ≠ 1 := fun h => hc1 (hinj _ _ (by rw [← hc₁, h, hd1]))
  have hc₁t : c₁ ≠ t := fun h => hct (hinj _ _ (by rw [← hc₁, h, hdt']))
  have hc₂1 : c₂ ≠ 1 := fun h => hc₁1 (hinj _ _ (by rw [← hc₂, h, hd1]))
  have hc₂t : c₂ ≠ t := fun h => hc₁t (hinj _ _ (by rw [← hc₂, h, hdt']))
  have hc₂c₁ : c₂ ≠ c₁ := fun h => hc₁c (hinj _ _ (by rw [← hc₁, ← hc₂, h]))
  have hc₂c : c₂ ≠ c := fun h => hc₁c (by rw [← hc₂', h])
  have hc₁F : c₁ ∈ F := hdF c hc
  have hc₂F : c₂ ∈ F := hdF c₁ hc₁F
  let f : Fin 5 → F := ![⟨1, F.one_mem⟩, ⟨t, htF⟩, ⟨c, hc⟩, ⟨c₁, hc₁F⟩, ⟨c₂, hc₂F⟩]
  have hf : Function.Injective f := by
    intro i j hij
    have hij' := congrArg Subtype.val hij
    fin_cases i <;> fin_cases j <;> simp only [f] at hij' <;>
      first
        | rfl
        | exact absurd hij' (Ne.symm ht1) | exact absurd hij' ht1
        | exact absurd hij' (Ne.symm hc1) | exact absurd hij' hc1
        | exact absurd hij' (Ne.symm hc₁1) | exact absurd hij' hc₁1
        | exact absurd hij' (Ne.symm hc₂1) | exact absurd hij' hc₂1
        | exact absurd hij' (Ne.symm hct) | exact absurd hij' hct
        | exact absurd hij' (Ne.symm hc₁t) | exact absurd hij' hc₁t
        | exact absurd hij' (Ne.symm hc₂t) | exact absurd hij' hc₂t
        | exact absurd hij' (Ne.symm hc₁c) | exact absurd hij' hc₁c
        | exact absurd hij' (Ne.symm hc₂c) | exact absurd hij' hc₂c
        | exact absurd hij' (Ne.symm hc₂c₁) | exact absurd hij' hc₂c₁
  have h5 := Nat.card_le_card_of_injective f hf
  rw [Nat.card_eq_fintype_card, Fintype.card_fin] at h5
  omega

theorem eq_bot_of_commute_centralizer {Y : Type*} [Group Y] [Finite Y]
    (h2r : ∀ F : Subgroup (MulAut Y), F ≤ (MulAut.conj : Y →* MulAut Y).range →
      IsElemAbelian 2 F → Nat.card F ≤ 4)
    {D T V : Subgroup (MulAut Y)} (hDe : IsElemAbelian 3 D) (hD9 : Nat.card D = 9)
    (hT2 : IsPGroup 2 T) (hTD : T ≤ Subgroup.centralizer (D : Set (MulAut Y)))
    (hVi : V ≤ (MulAut.conj : Y →* MulAut Y).range) (hV2 : IsPGroup 2 V)
    (hDV : D ≤ Subgroup.normalizer (V : Set (MulAut Y))) (hVD : ⁅V, D⁆ = V)
    (hVT : V ≤ Subgroup.centralizer (T : Set (MulAut Y)))
    (hT0 : T ⊓ (MulAut.conj : Y →* MulAut Y).range ≠ ⊥)
    (hab : ∀ a ∈ (MulAut.conj : Y →* MulAut Y).range ⊓ Subgroup.centralizer
        ((T ⊓ (MulAut.conj : Y →* MulAut Y).range : Subgroup (MulAut Y)) : Set (MulAut Y)),
      ∀ b ∈ (MulAut.conj : Y →* MulAut Y).range ⊓ Subgroup.centralizer
        ((T ⊓ (MulAut.conj : Y →* MulAut Y).range : Subgroup (MulAut Y)) : Set (MulAut Y)),
      a * b = b * a) : V = ⊥ := by
  classical
  have : Finite (MulAut Y) :=
    Finite.of_injective (fun σ : MulAut Y => (σ : Y → Y)) (fun a b h => MulEquiv.ext (congrFun h))
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Inn := (MulAut.conj : Y →* MulAut Y).range with hInn
  set T₀ := T ⊓ Inn with hT₀
  set C := Inn ⊓ Subgroup.centralizer (T₀ : Set (MulAut Y)) with hC
  have hT₀2 : IsPGroup 2 T₀ := hT2.to_le inf_le_left
  have : Nontrivial T₀ := (Subgroup.nontrivial_iff_ne_bot T₀).mpr hT0
  have : Nontrivial (Subgroup.center T₀) := hT₀2.center_nontrivial
  have : Fintype (Subgroup.center T₀) := Fintype.ofFinite _
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp (hT₀2.to_subgroup (Subgroup.center T₀))
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hn
    have := Finite.one_lt_card (α := Subgroup.center T₀)
    omega
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card 2
    (show 2 ∣ Fintype.card (Subgroup.center T₀) by
      rw [← Nat.card_eq_fintype_card, hn]
      exact dvd_pow_self 2 hn0)
  set t : MulAut Y := ((z : T₀) : MulAut Y) with ht
  have htT₀ : t ∈ T₀ := (z : T₀).2
  have ht2 : t ^ 2 = 1 := by
    have h1 : z ^ 2 = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
    have h2 := congrArg (fun w : Subgroup.center T₀ => ((w : T₀) : MulAut Y)) h1
    simpa using h2
  have ht1 : t ≠ 1 := by
    intro h
    have h1 : z = 1 := Subtype.ext (Subtype.ext h)
    rw [h1, orderOf_one] at hz
    omega
  have htC : t ∈ C := by
    refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp htT₀).2, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have h1 := Subgroup.mem_center_iff.mp z.2 ⟨s, hs⟩
    exact congrArg Subtype.val h1
  have hDt : ∀ d ∈ D, d * t = t * d := fun d hd =>
    Subgroup.mem_centralizer_iff.mp (hTD (Subgroup.mem_inf.mp htT₀).1) d hd
  have hDC : ∀ d ∈ D, ∀ c ∈ C, d * c * d⁻¹ ∈ C := by
    intro d hd c hc
    obtain ⟨⟨y, rfl⟩, hcT⟩ := Subgroup.mem_inf.mp hc
    refine Subgroup.mem_inf.mpr ⟨⟨d y, (mul_conj_mul_inv' d y).symm⟩, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have hds : d * s = s * d :=
      Subgroup.mem_centralizer_iff.mp (hTD (Subgroup.mem_inf.mp hs).1) d hd
    have hcs := Subgroup.mem_centralizer_iff.mp hcT s hs
    calc s * (d * MulAut.conj y * d⁻¹) = (s * d) * MulAut.conj y * d⁻¹ := by group
      _ = d * (s * MulAut.conj y) * d⁻¹ := by rw [← hds]; group
      _ = d * (MulAut.conj y * s) * d⁻¹ := by rw [hcs]
      _ = d * MulAut.conj y * (d⁻¹ * (d * s)) * d⁻¹ := by group
      _ = d * MulAut.conj y * d⁻¹ * s := by rw [hds]; group
  let F : Subgroup (MulAut Y) :=
    { carrier := {c | c ∈ C ∧ c ^ 2 = 1}
      mul_mem' := by
        rintro a b ⟨haC, ha2⟩ ⟨hbC, hb2⟩
        refine ⟨C.mul_mem haC hbC, ?_⟩
        have hab' := hab a haC b hbC
        calc (a * b) ^ 2 = a ^ 2 * b ^ 2 := by
              rw [pow_two, pow_two, pow_two, mul_assoc, ← mul_assoc b a b, ← hab']; group
          _ = 1 := by rw [ha2, hb2, one_mul]
      one_mem' := ⟨C.one_mem, one_pow 2⟩
      inv_mem' := by
        rintro a ⟨haC, ha2⟩
        exact ⟨C.inv_mem haC, by rw [inv_pow, ha2, inv_one]⟩ }
  have hFe : IsElemAbelian 2 F := by
    refine ⟨⟨⟨fun a b => Subtype.ext (hab _ a.2.1 _ b.2.1)⟩⟩, fun x hx => hx.2⟩
  have hF4 : Nat.card F ≤ 4 := h2r F (fun x hx => (Subgroup.mem_inf.mp hx.1).1) hFe
  have hDF : ∀ d ∈ D, ∀ c ∈ F, d * c * d⁻¹ ∈ F := by
    intro d hd c hc
    refine ⟨hDC d hd c hc.1, ?_⟩
    rw [conj_pow, hc.2, mul_one, mul_inv_cancel]
  have hfixF : ∀ d ∈ D, ∀ c ∈ F, d * c = c * d := fun d hd c hc =>
    commute_of_card_le_four hF4 (hDe.2 d hd) ⟨htC, ht2⟩ ht1 (hDt d hd) (hDF d hd) hc
  have hVC : V ≤ C := by
    intro v hv
    refine Subgroup.mem_inf.mpr ⟨hVi hv, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    exact Subgroup.mem_centralizer_iff.mp (hVT hv) s (Subgroup.mem_inf.mp hs).1
  have : Finite D := Nat.finite_of_card_ne_zero (by rw [hD9]; norm_num)
  refine eq_bot_of_comm_of_fixed (fun a ha b hb => hab a (hVC ha) b (hVC hb))
    (by rw [hD9]; decide) hV2 hDV hVD fun v hv hv2 d hd => ?_
  exact hfixF d hd v ⟨hVC hv, hv2⟩

theorem l3PlusFor_of_core {Y : Type*} [Group Y] [Finite Y]
    (h2r : ∀ F : Subgroup (MulAut Y), F ≤ (MulAut.conj : Y →* MulAut Y).range →
      IsElemAbelian 2 F → Nat.card F ≤ 4)
    (hInn : ∃ a ∈ (MulAut.conj : Y →* MulAut Y).range,
      ∃ b ∈ (MulAut.conj : Y →* MulAut Y).range, a * b ≠ b * a)
    (hcore : L3PlusCoreFor Y) : L3PlusFor Y := by
  intro D T V W hDe hD9 hT2 hT1 hTD hVi hV2 hDV hVD hVT hW2 hVW hWT hτ
  by_cases hab : ∀ a ∈ (MulAut.conj : Y →* MulAut Y).range ⊓ Subgroup.centralizer
        ((T ⊓ (MulAut.conj : Y →* MulAut Y).range : Subgroup (MulAut Y)) : Set (MulAut Y)),
      ∀ b ∈ (MulAut.conj : Y →* MulAut Y).range ⊓ Subgroup.centralizer
        ((T ⊓ (MulAut.conj : Y →* MulAut Y).range : Subgroup (MulAut Y)) : Set (MulAut Y)),
      a * b = b * a
  · refine eq_bot_of_commute_centralizer h2r hDe hD9 hT2 hTD hVi hV2 hDV hVD hVT ?_ hab
    intro h0
    obtain ⟨a, ha, b, hb, hab'⟩ := hInn
    have hcent : ∀ x : MulAut Y, x ∈ Subgroup.centralizer
        ((T ⊓ (MulAut.conj : Y →* MulAut Y).range : Subgroup (MulAut Y)) : Set (MulAut Y)) := by
      intro x
      rw [Subgroup.mem_centralizer_iff, h0]
      intro s hs
      rw [SetLike.mem_coe, Subgroup.mem_bot] at hs
      rw [hs, one_mul, mul_one]
    exact hab' (hab a (Subgroup.mem_inf.mpr ⟨ha, hcent a⟩) b (Subgroup.mem_inf.mpr ⟨hb, hcent b⟩))
  · exact hcore D T V W hDe hD9 hT2 hT1 hTD hab hVi hV2 hDV hVD hVT hW2 hVW hWT hτ

theorem exists_inn_ne_comm {Y : Type*} [Group Y] [Nontrivial Y]
    (hZ : Subgroup.center Y = ⊥) :
    ∃ a ∈ (MulAut.conj : Y →* MulAut Y).range,
      ∃ b ∈ (MulAut.conj : Y →* MulAut Y).range, a * b ≠ b * a := by
  by_contra h
  push Not at h
  have hcomm : ∀ a b : Y, a * b = b * a := by
    intro a b
    have h1 := h _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    rw [← map_mul, ← map_mul] at h1
    exact conj_injective' hZ h1
  have htop : Subgroup.center Y = ⊤ := by
    ext x
    simp only [Subgroup.mem_top, iff_true, Subgroup.mem_center_iff]
    exact fun g => hcomm g x
  rw [htop] at hZ
  exact top_ne_bot hZ

section Linear

open LinearFlag
open scoped MatrixGroups

variable {K : Type} [Field K]

theorem card_elemAbelian_le_four_projectiveSL [Finite K] {p : ℕ} [Fact p.Prime] [CharP K p]
    (hp2 : p ≠ 2) {A : Subgroup (projectiveSL 3 K)} (hA : IsElemAbelian 2 A) :
    Nat.card A ≤ 4 := by
  obtain ⟨g, hg⟩ := CFSG.Quasithin.E22S.exists_frame hp2 hA
  have hsq : ∀ x : CFSG.Quasithin.E22S.invLifts A hA,
      CFSG.Quasithin.E22S.dg g x 0 * CFSG.Quasithin.E22S.dg g x 0 = 1 ∧
      CFSG.Quasithin.E22S.dg g x 1 * CFSG.Quasithin.E22S.dg g x 1 = 1 := fun x =>
    ⟨CFSG.Quasithin.E22S.dg_sq (hg x x.2) x.2.2 0, CFSG.Quasithin.E22S.dg_sq (hg x x.2) x.2.2 1⟩
  let φ : CFSG.Quasithin.E22S.invLifts A hA →
      {e : K // e = 1 ∨ e = -1} × {e : K // e = 1 ∨ e = -1} := fun x =>
    (⟨CFSG.Quasithin.E22S.dg g x 0, mul_self_eq_one_iff.mp (hsq x).1⟩,
      ⟨CFSG.Quasithin.E22S.dg g x 1, mul_self_eq_one_iff.mp (hsq x).2⟩)
  have hφ : Function.Injective φ := by
    intro x y hxy
    have h0 : CFSG.Quasithin.E22S.dg g x 0 = CFSG.Quasithin.E22S.dg g y 0 :=
      congrArg Subtype.val (congrArg Prod.fst hxy)
    have h1 : CFSG.Quasithin.E22S.dg g x 1 = CFSG.Quasithin.E22S.dg g y 1 :=
      congrArg Subtype.val (congrArg Prod.snd hxy)
    have hxd : ∀ z : CFSG.Quasithin.E22S.invLifts A hA, CFSG.Quasithin.E22S.dg g z 2 =
        CFSG.Quasithin.E22S.dg g z 0 * CFSG.Quasithin.E22S.dg g z 1 := by
      intro z
      have hp := CFSG.Quasithin.E22S.dg_prod (hg z z.2)
      rw [Fin.prod_univ_three] at hp
      have h0 := (hsq z).1
      have h1 := (hsq z).2
      linear_combination (CFSG.Quasithin.E22S.dg g z 0 * CFSG.Quasithin.E22S.dg g z 1) * hp -
        CFSG.Quasithin.E22S.dg g z 2 * CFSG.Quasithin.E22S.dg g z 1 *
          CFSG.Quasithin.E22S.dg g z 1 * h0 - CFSG.Quasithin.E22S.dg g z 2 * h1
    apply Subtype.ext
    apply CFSG.Quasithin.E22S.dg_inj (hg x x.2) (hg y y.2)
    intro i
    fin_cases i
    · exact h0
    · exact h1
    · show CFSG.Quasithin.E22S.dg g x 2 = CFSG.Quasithin.E22S.dg g y 2
      rw [hxd x, hxd y, h0, h1]
  have h1 := Nat.card_le_card_of_injective φ hφ
  have h2 := CFSG.Quasithin.E22S.card_le_card_invLifts hA
  have h3 : Nat.card ({e : K // e = 1 ∨ e = -1} × {e : K // e = 1 ∨ e = -1}) ≤ 4 := by
    rw [Nat.card_prod]
    have := CFSG.Quasithin.E22S.card_sign_le_two (K := K)
    nlinarith [this, Nat.zero_le (Nat.card {e : K // e = 1 ∨ e = -1})]
  omega

theorem isSimpleGroup_projectiveSL_three : IsSimpleGroup (projectiveSL 3 K) := by
  have := (CFSG.LinearGroups.linear_projective_simple (K := K) (n := 3) (by omega)
    (Or.inl le_rfl)).2.1
  exact (LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 K).symm.isSimpleGroup

theorem l3PlusFor_projectiveSL [Finite K] {p : ℕ} [Fact p.Prime] [CharP K p] (hp2 : p ≠ 2)
    (hcore : L3PlusCoreFor (projectiveSL 3 K)) : L3PlusFor (projectiveSL 3 K) := by
  have hZ := center_projectiveSL_three_eq_bot' (K := K)
  have : IsSimpleGroup (projectiveSL 3 K) := isSimpleGroup_projectiveSL_three
  refine l3PlusFor_of_core (fun F hF hFe => ?_) (exists_inn_ne_comm hZ) hcore
  rw [← Item211LieProof.card_comap_conj hZ hF]
  exact card_elemAbelian_le_four_projectiveSL hp2
    (Item211LieProof.isElemAbelian_comap_of_injective (conj_injective' hZ) hFe)

end Linear

section Unitary

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

theorem isSimpleGroup_unitaryPSU_three (hq : 2 < p ^ f) : IsSimpleGroup (unitaryPSU h 3) := by
  have := h.finite
  have : Fact p.Prime := ⟨h.prime⟩
  have hK : Nat.card K = (p ^ f) ^ 2 := by rw [h.card, ← pow_mul, mul_comm]
  have hnq : (3, p ^ f) ≠ (3, 2) := fun h' => by
    have := (Prod.mk.inj h').2
    omega
  have := CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU K p f hK 3 le_rfl hnq
  exact (unitaryPSUEquiv h (n := 3) (by norm_num)).isSimpleGroup

theorem l3PlusFor_unitaryPSU (hp2 : p ≠ 2) (hq : 2 < p ^ f)
    (hcore : L3PlusCoreFor (unitaryPSU h 3)) : L3PlusFor (unitaryPSU h 3) := by
  have := h.finite
  have hZ := center_unitaryPSU_three_eq_bot h hq
  have : IsSimpleGroup (unitaryPSU h 3) := isSimpleGroup_unitaryPSU_three h hq
  refine l3PlusFor_of_core (fun F hF hFe => ?_) (exists_inn_ne_comm hZ) hcore
  rw [← Item211LieProof.card_comap_conj hZ hF]
  set A := F.comap (MulAut.conj : unitaryPSU h 3 →* MulAut (unitaryPSU h 3)) with hA
  have hAe : IsElemAbelian 2 A :=
    Item211LieProof.isElemAbelian_comap_of_injective (conj_injective' hZ) hFe
  set Eq := unitaryPSUEquiv h (n := 3) (by norm_num) with hEq
  have hA'e : IsElemAbelian 2 (A.map Eq.toMonoidHom) := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, ?_⟩
    · obtain ⟨_, ⟨x, hx, rfl⟩⟩ := a
      obtain ⟨_, ⟨y, hy, rfl⟩⟩ := b
      simp only [Subgroup.coe_mul]
      have h0 : x * y = y * x := congrArg Subtype.val (hAe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
      rw [← map_mul, ← map_mul, h0]
    · rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow, hAe.2 x hx, map_one]
  have h1 := CFSG.Quasithin.E22S.card_elemAbelian_le_four h hp2 hA'e
  rwa [Subgroup.card_map_of_injective Eq.injective] at h1

end Unitary

end Item211Lie2Proof

open Item211Lie2Proof
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (projectiveSL)

@[expose] def KS211L3PlusLinearCore : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p], 3 < p →
    Nat.card K % 3 = 1 → L3PlusCoreFor (projectiveSL 3 K)

@[expose] def KS211L3PlusUnitaryCore : Prop :=
  ∀ (p f : ℕ) (K : Type) [Field K] (h : UnitaryFieldData p f K), 3 < p → p ^ f % 3 = 2 →
    L3PlusCoreFor (unitaryPSU h 3)

theorem ks211L3Plus_of_cores (hL : KS211L3PlusLinearCore) (hU : KS211L3PlusUnitaryCore) :
    KS211L3Plus := by
  intro X _ _ hX hM
  obtain ⟨p, hp, hp3, e, he, hcase⟩ := hM
  have hp2 : p ≠ 2 := by omega
  have hpe : 2 < p ^ e := lt_of_lt_of_le (by omega) (Nat.le_self_pow (by omega) p)
  change L3PlusFor X
  have : Group.IsPerfect X := hX.1
  rcases hcase with ⟨K, _, _, hK⟩ | hL'
  · rcases hK with ⟨hcard, hmod, ⟨φ⟩⟩ | ⟨hcard, hmod, ⟨φ⟩⟩
    · have : Fintype K := Fintype.ofFinite K
      have : CharP K p := charP_of_card_eq_prime_pow (f := e)
        (by rw [← Nat.card_eq_fintype_card, hcard])
      exact l3PlusFor_of_perfect (l3PlusFor_of_mulEquiv
        ((quotientCenterCongr (φ.trans (Sec4.statedSLEquiv 3 K))).trans
          (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL
            3 K))
        (l3PlusFor_projectiveSL hp2 (hL K p hp3 (by rw [hcard]; exact hmod))))
    · have h : UnitaryFieldData p e K := ⟨hp.out, he, by rw [hcard, ← pow_mul, mul_comm]⟩
      exact l3PlusFor_of_perfect (l3PlusFor_of_mulEquiv
        ((quotientCenterCongr φ).trans (KFacts.suCenterEquiv h hpe))
        (l3PlusFor_unitaryPSU h hp2 hpe (hU p e K h hp3 hmod)))
  · rcases hL' with ⟨hmod, ⟨φ⟩⟩ | ⟨hmod, ⟨φ⟩⟩
    · have hcardG : Nat.card (GaloisField p e) = p ^ e := by
        exact GaloisField.card p e (by omega)
      exact l3PlusFor_of_mulEquiv (φ.trans (Sec4.projSLEquivProjectiveSL 3 (GaloisField p e)))
        (l3PlusFor_projectiveSL hp2
          (hL (GaloisField p e) p hp3 (by rw [hcardG]; exact hmod)))
    · have h := Sec4.unitaryFieldData_galoisField p e he
      exact l3PlusFor_of_mulEquiv (φ.trans (Sec4.projSUEquivUnitaryPSU p e h))
        (l3PlusFor_unitaryPSU h hp2 hpe (hU p e (GaloisField p (2 * e)) h hp3 hmod))

end CFSG.RankThree.PartTwo.Sec21
