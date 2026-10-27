module

public import CFSG.RankThree.PartTwo.KFacts.KS44OutSz
import CFSG.Adapters.WholeGroupLayer
import CFSG.LocalAnalysis.SteinbergCCExistingCLS
import CFSG.LocalAnalysis.UniquenessCase.UC22P22uk
import CFSG.Permutation.FiveTransitive.CharacteristicAutomorphism
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.GroupTheory.LocalCores.Layer
public import CFSG.LieType.Ree.SuzukiOrder
public import CFSG.RankThree.PartTwo.Setup

public section

namespace CFSG.RankThree.PartTwo.Sec14.Liebeck1418Bridge

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.LocalCores (ComponentIndex)
open CFSG.SignalizerFunctorTheorem.Nonsolvable (exists_perfect_isSubnormal_map_eq
  isPerfect_perfectResidual_map isSubnormal_perfectResidual_map map_perfectResidual_map
  perfectResidual_map_eq_of_isPerfect isSolvable_solvableRadical solvableRadical_quotient
  le_solvableRadical)

section Inner

variable {Q : Type} [Group Q] [Finite Q] {P : Type} [Group P]

private noncomputable def compPerm (e : MulAut Q) : Equiv.Perm (ComponentIndex Q) where
  toFun K := ⟨K.1.map e.toMonoidHom, CFSG.LocalCores.isComponent_map_mulEquiv e K.2⟩
  invFun K := ⟨K.1.map e.symm.toMonoidHom, CFSG.LocalCores.isComponent_map_mulEquiv e.symm K.2⟩
  left_inv K := Subtype.ext (CFSG.LocalCores.map_map_symm e K.1)
  right_inv K := Subtype.ext (by
    simpa only [MulEquiv.symm_symm] using CFSG.LocalCores.map_map_symm e.symm K.1)

private noncomputable def compPermHom : MulAut Q →* Equiv.Perm (ComponentIndex Q) where
  toFun := compPerm
  map_one' := Equiv.ext fun K => Subtype.ext (by
    ext x
    change x ∈ K.1.map (1 : MulAut Q).toMonoidHom ↔ x ∈ K.1
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨x, hx, rfl⟩)
  map_mul' e f := Equiv.ext fun K => Subtype.ext (by
    change K.1.map (e * f).toMonoidHom = (K.1.map f.toMonoidHom).map e.toMonoidHom
    rw [Subgroup.map_map]
    rfl)

private theorem map_eq_of_perfect (hP : Group.IsPerfect P)
    (hcard : Nat.card (ComponentIndex Q) ≤ 4) (φ : P →* MulAut Q) (p : P)
    (L : ComponentIndex Q) : L.1.map (φ p).toMonoidHom = L.1 := by
  have hsolv : Group.IsSolvable (Equiv.Perm (ComponentIndex Q)) := Equiv.Perm.isSolvable hcard
  set ρ : P →* Equiv.Perm (ComponentIndex Q) := compPermHom.comp φ
  have hrp : Group.IsPerfect ↥ρ.range := Group.IsPerfect.range ρ
  have hrs : Group.IsSolvable ↥ρ.range := inferInstance
  have hsub : Subsingleton ↥ρ.range := by
    by_contra hnt
    rw [not_subsingleton_iff_nontrivial] at hnt
    exact Group.IsPerfect.not_isSolvable _ hrs
  have h1 : ρ p = 1 := by
    have : (⟨ρ p, p, rfl⟩ : ↥ρ.range) = 1 := Subsingleton.elim _ _
    exact congrArg Subtype.val this
  exact congrArg (fun f : Equiv.Perm (ComponentIndex Q) => (f L).1) h1

private def restrictAut (φ : P →* MulAut Q) (L : Subgroup Q)
    (h : ∀ p, L.map (φ p).toMonoidHom = L) : P →* MulAut L where
  toFun p := ((φ p).subgroupMap L).trans (MulEquiv.subgroupCongr (h p))
  map_one' := MulEquiv.ext fun x => Subtype.ext (by
    show φ 1 (x : Q) = x
    rw [map_one]
    rfl)
  map_mul' p q := MulEquiv.ext fun x => Subtype.ext (by
    show φ (p * q) (x : Q) = φ p (φ q (x : Q))
    rw [map_mul]
    rfl)

private theorem coe_restrictAut (φ : P →* MulAut Q) (L : Subgroup Q)
    (h : ∀ p, L.map (φ p).toMonoidHom = L) (p : P) (x : L) :
    ((restrictAut φ L h p x : L) : Q) = φ p x := rfl

private theorem isSolvable_outer_of_commutator_le_inner (L : Type) [Group L]
    (h : commutator (MulAut L) ≤ (MulAut.conj : L →* MulAut L).range) :
    Group.IsSolvable (CFSG.ComponentClassification.OuterAutomorphisms.Outer L) := by
  have : (MulAut.conj : L →* MulAut L).range.Normal :=
    CFSG.ComponentClassification.OuterAutomorphisms.inner_normal L
  have hcomm : IsMulCommutative (MulAut L ⧸ (MulAut.conj : L →* MulAut L).range) :=
    (Subgroup.Normal.quotient_commutative_iff_commutator_le).mpr h
  exact Group.isSolvable_of_comm (fun a b => hcomm.is_comm.comm a b)

private theorem exists_conj_of_perfect_action
    (hP : Group.IsPerfect P) (hrad : CFSG.solvableRadical Q = ⊥)
    (hcard : Nat.card (ComponentIndex Q) ≤ 4)
    (hOut : ∀ L : Subgroup Q, IsComponent L →
      commutator (MulAut L) ≤ (MulAut.conj : L →* MulAut L).range)
    (φ : P →* MulAut Q) (p : P) : ∃ q : Q, φ p = MulAut.conj q := by
  have stab := map_eq_of_perfect hP hcard φ
  have hinner : ∀ K : Subgroup Q, IsComponent K →
      ∃ c ∈ K, ∀ x ∈ K, (φ p).toMonoidHom x = c * x * c⁻¹ := by
    intro K hK
    haveI : Group.IsSolvable (CFSG.ComponentClassification.OuterAutomorphisms.Outer K) :=
      isSolvable_outer_of_commutator_le_inner K (hOut K hK)
    obtain ⟨c, hc⟩ := CFSG.ComponentClassification.OuterAutomorphisms.perfect_action_inner
      (restrictAut φ K (fun p => stab p ⟨K, hK⟩)) p
    refine ⟨c, c.2, fun x hx => ?_⟩
    have := congrArg (fun a : MulAut K => (a ⟨x, hx⟩ : Q)) hc
    simpa [coe_restrictAut, MulAut.conj_apply] using this
  obtain ⟨e, -, hxe⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p22u_exists_layer_implementer (φ p).toMonoidHom
      hinner
  obtain ⟨hF, hFL⟩ := CFSG.LocalAnalysis.radical_free_generalized_fitting_layer hrad
  have hN : (layer Q).Normal := by
    have := CFSG.LocalCores.layer_characteristic (G := Q)
    infer_instance
  refine ⟨e, MulEquiv.ext fun x => ?_⟩
  set a := φ p x with ha
  set z := x * (e⁻¹ * a * e)⁻¹ with hz
  have hzc : z ∈ Subgroup.centralizer ((generalizedFitting Q : Subgroup Q) : Set Q) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [hFL] at hy
    have hy' : x⁻¹ * y * x ∈ layer Q := by
      simpa using hN.conj_mem y hy x⁻¹
    have h1 : e * (x⁻¹ * y * x) * e⁻¹ = a⁻¹ * (e * y * e⁻¹) * a := by
      have := hxe _ hy'
      rw [← this]
      change φ p (x⁻¹ * y * x) = _
      rw [map_mul, map_mul, map_inv, ← ha]
      change a⁻¹ * (φ p y) * a = _
      rw [show φ p y = (φ p).toMonoidHom y from rfl, hxe y hy]
    have h2 : z⁻¹ * y * z = y := by
      calc z⁻¹ * y * z = e⁻¹ * a * (e * (x⁻¹ * y * x) * e⁻¹) * a⁻¹ * e := by rw [hz]; group
        _ = e⁻¹ * a * (a⁻¹ * (e * y * e⁻¹) * a) * a⁻¹ * e := by rw [h1]
        _ = y := by group
    calc y * z = z * (z⁻¹ * y * z) := by group
      _ = z * y := by rw [h2]
  have hz1 := CFSG.Adapters.centralizer_generalizedFitting_le_fittingSubgroup Q hzc
  rw [hF, Subgroup.mem_bot] at hz1
  have hxw : x = e⁻¹ * a * e := mul_inv_eq_one.mp hz1
  rw [MulAut.conj_apply]
  calc a = e * (e⁻¹ * a * e) * e⁻¹ := by group
    _ = e * x * e⁻¹ := by rw [← hxw]

end Inner

section Components

open CFSG.Blueprint

private theorem five_dvd_card_of_suzukiModel {H : Type} [Group H]
    {p f : ℕ} (h : SuzukiModel H p f) : 5 ∣ Nat.card H := by
  obtain ⟨-, a, -, K, _, _, rfl, hcard, ⟨e⟩⟩ := h
  rw [Nat.card_congr e.toEquiv, CFSG.LieType.Ree.suzuki_order hcard]
  refine Dvd.dvd.mul_left ?_ _
  have h1 : ((2 : ℕ) ^ (2 * a + 1)) ^ 2 = 4 * 16 ^ a := by
    rw [← pow_mul, show (2 * a + 1) * 2 = 2 + 4 * a by ring, pow_add, pow_mul]
    norm_num
  rw [h1, Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.mul_mod, Nat.pow_mod]
  norm_num

private theorem component_suzukiModel {X : Type} [Group X] [Finite X] (hX : SectionFourHyp X)
    (hSz : KFacts.KPSz) {D : Subgroup X} (hD3 : ¬ 3 ∣ Nat.card D)
    {L : Subgroup (↥D ⧸ CFSG.solvableRadical ↥D)} (hL : IsComponent L) :
    IsSimpleGroup L ∧ (∃ a b : L, a * b ≠ b * a) ∧ ∃ f : ℕ, SuzukiModel L 2 f := by
  set Q := ↥D ⧸ CFSG.solvableRadical ↥D
  have hrad : CFSG.solvableRadical Q = ⊥ := solvableRadical_quotient
  have hfree : CFSG.ComponentClassification.SolvableRadical.Free Q :=
    (CFSG.ComponentClassification.SolvableRadical.free_iff_eq_bot Q).mpr hrad
  have hsimple : IsSimpleGroup L :=
    CFSG.ComponentClassification.RadicalFreeLayer.component_simple hfree L
      ((CFSG.isComponent_iff_open L).mp hL)
  have hnab : ∃ a b : L, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hL.1.2.2
    obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
    exact ⟨a', b', fun h => hab (by rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h])⟩
  have h3 : ¬ 3 ∣ Nat.card L := fun h =>
    hD3 (h.trans ((Subgroup.card_subgroup_dvd_card L).trans (Subgroup.card_quotient_dvd_card _)))
  have hcat : CFSG.Assembly.InCatalog L :=
    ((hX.kGroup.subgroup D).quotient (CFSG.solvableRadical ↥D)).inCatalog_of_surjective L
      (MonoidHom.id L) Function.surjective_id
  exact ⟨hsimple, hnab, hSz L hnab hcat h3⟩

private theorem card_componentIndex_le_three {X : Type} [Group X]
    [Finite X] (hX : SectionFourHyp X) (hSz : KFacts.KPSz)
    (hFour : ∀ (D : Subgroup X) (S : Subgroup D) [S.Normal] (Y : Fin 4 → Subgroup (D ⧸ S)),
      (∀ i, IsComponent (Y i)) → Function.Injective Y → (∀ i, IsSimpleGroup (Y i)) →
      (∀ i, 5 ∣ Nat.card (Y i)) → (∀ i, 2 ∣ Nat.card (Y i)) → False)
    {D : Subgroup X} (hD3 : ¬ 3 ∣ Nat.card D) :
    Nat.card (ComponentIndex (↥D ⧸ CFSG.solvableRadical ↥D)) ≤ 3 := by
  by_contra hlt
  replace hlt := not_le.1 hlt
  haveI : Fintype (ComponentIndex (↥D ⧸ CFSG.solvableRadical ↥D)) := Fintype.ofFinite _
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le (α := Fin 4)
    (β := ComponentIndex (↥D ⧸ CFSG.solvableRadical ↥D))
    (by rw [Fintype.card_fin, ← Nat.card_eq_fintype_card]; omega)
  have hdata := fun i => component_suzukiModel hX hSz hD3 (e i).2
  refine hFour D (CFSG.solvableRadical ↥D) (fun i => (e i).1) (fun i => (e i).2)
    (fun i j h => e.injective (Subtype.ext h)) (fun i => (hdata i).1) (fun i => ?_) (fun i => ?_)
  · obtain ⟨-, -, f, hf⟩ := hdata i
    exact five_dvd_card_of_suzukiModel hf
  · obtain ⟨hs, -, f, hf⟩ := hdata i
    haveI := hs
    exact KFacts.two_dvd_card_of_suzukiModel hf

private theorem component_commutator_le_inner {X : Type} [Group X]
    [Finite X] (hX : SectionFourHyp X) (hSz : KFacts.KPSz) {D : Subgroup X}
    (hD3 : ¬ 3 ∣ Nat.card D) {L : Subgroup (↥D ⧸ CFSG.solvableRadical ↥D)} (hL : IsComponent L) :
    commutator (MulAut L) ≤ (MulAut.conj : L →* MulAut L).range := by
  obtain ⟨-, -, f, hf⟩ := component_suzukiModel hX hSz hD3 hL
  exact KFacts.commutator_le_inner_of_suzukiModel hf

end Components

section Theta

open CFSG.RankThree.LocalRank

private theorem mem_thetaComponents_of_inf_le {X : Type} [Group X] [Finite X] {J T : Subgroup X}
    (hJp : Group.IsPerfect J) (hJs : J.IsSubnormal) (hT : Group.IsSolvable T)
    (hJT : ∀ x ∈ J, x ∈ CFSG.pPrimeCore 3 X → x ∈ T)
    (hq : IsComponent (J.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X)))) :
    J ∈ thetaComponents 3 X := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set O := CFSG.pPrimeCore 3 X
  set N : Subgroup J := O.subgroupOf J
  have hinj : ∀ a b : N, ((a : J) : X) = ((b : J) : X) → a = b := fun a b h =>
    Subtype.ext (Subtype.ext h)
  have hNsol : Group.IsSolvable N :=
    Group.isSolvable_of_isSolvable_injective
      (f := (J.subtype.comp N.subtype).codRestrict T fun x => hJT _ x.1.2 x.2)
      fun a b h => hinj a b (congrArg (fun z : T => (z : X)) h)
  have hN3 : ¬ 3 ∣ Nat.card N := fun h =>
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
      (CFSG.pPrimeCore_coprime_card (p := 3) (G := X))) (h.trans
        (Subgroup.card_dvd_of_injective ((J.subtype.comp N.subtype).codRestrict O fun x => x.2)
          fun a b h => hinj a b (congrArg (fun z : O => (z : X)) h)))
  have hNθ : N ≤ aschbacherSolvableCore 3 J :=
    (solvable_prime_complement_core_characterization Nat.prime_three).2.2.2.1 N inferInstance hNsol
      hN3
  have hθO : aschbacherSolvableCore 3 X ≤ O := by
    obtain ⟨-, -, hcop, -⟩ := solvable_prime_complement_core_characterization (H := X)
      Nat.prime_three
    exact le_sSup ⟨inferInstance, (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hcop⟩
  have hθ : ∀ l : J, l ∈ aschbacherSolvableCore 3 J ↔ QuotientGroup.mk' O l = 1 := by
    intro l
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    constructor
    · intro hl
      rw [aschbacherSolvableCore_eq_subgroupOf Nat.prime_three hJs, Subgroup.mem_subgroupOf] at hl
      exact hθO hl
    · intro hl
      exact hNθ hl
  obtain ⟨η, -⟩ := exists_quotient_mulEquiv_map (QuotientGroup.mk' O) J
    (aschbacherSolvableCore 3 J) hθ
  exact ⟨hJp, hJs, CFSG.LocalCores.isQuasisimple_of_mulEquiv η.symm hq.1⟩

end Theta

section Action

variable {X : Type} [Group X]

private noncomputable def actOnQuot (K D : Subgroup X)
    (hKD : K ≤ Subgroup.normalizer (D : Set X)) :
    K →* MulAut (↥D ⧸ CFSG.solvableRadical ↥D) :=
  (CFSG.FiveTransitive.CharacteristicAutomorphism.quotient (CFSG.solvableRadical ↥D)).comp
    (D.normalizerMonoidHom.comp (Subgroup.inclusion hKD))

private theorem actOnQuot_mk (K D : Subgroup X) (hKD : K ≤ Subgroup.normalizer (D : Set X))
    (k : K) (x y : D) (hxy : (y : X) = (k : X) * x * (k : X)⁻¹) :
    actOnQuot K D hKD k (x : ↥D ⧸ CFSG.solvableRadical ↥D) =
      (y : ↥D ⧸ CFSG.solvableRadical ↥D) := by
  have hy : y = D.normalizerMonoidHom (Subgroup.inclusion hKD k) x := Subtype.ext (by
    rw [hxy]
    rfl)
  rw [hy]
  exact CFSG.FiveTransitive.CharacteristicAutomorphism.quotient_apply_mk _ _ _

private theorem actOnQuot_of_mem (K D : Subgroup X) (hKD : K ≤ Subgroup.normalizer (D : Set X))
    (d : D) (hdK : (d : X) ∈ K) :
    actOnQuot K D hKD ⟨d, hdK⟩ = MulAut.conj (d : ↥D ⧸ CFSG.solvableRadical ↥D) := by
  refine MulEquiv.ext fun z => ?_
  induction z using QuotientGroup.induction_on with
  | H x =>
    rw [actOnQuot_mk K D hKD ⟨d, hdK⟩ x (d * x * d⁻¹) rfl, MulAut.conj_apply]
    rfl

private theorem mem_radical_of_act_eq_one [Finite X] (K D : Subgroup X)
    (hKD : K ≤ Subgroup.normalizer (D : Set X)) (d : D) (hdK : (d : X) ∈ K)
    (h : actOnQuot K D hKD ⟨d, hdK⟩ = 1) : d ∈ CFSG.solvableRadical ↥D := by
  rw [actOnQuot_of_mem K D hKD d hdK] at h
  have hz : ∀ (G : Type) [Group G] (q : G), MulAut.conj q = 1 → q ∈ Subgroup.center G := by
    intro G _ q hq
    rw [Subgroup.mem_center_iff]
    intro g
    have := congrArg (fun a : MulAut G => a g) hq
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    calc g * q = (q * g * q⁻¹) * q := by rw [this]
      _ = q * g := by group
  have hz := hz _ _ h
  have hle := le_solvableRadical
    (inferInstance : (Subgroup.center (↥D ⧸ CFSG.solvableRadical ↥D)).Normal) inferInstance
  rw [solvableRadical_quotient] at hle
  exact (QuotientGroup.eq_one_iff d).mp (Subgroup.mem_bot.mp (hle hz))

end Action

theorem exists_mem_thetaComponents_map_eq_of_four {X : Type}
    [Group X] [Finite X] (hX : SectionFourHyp X) (hSz : KFacts.KPSz)
    (hFour : ∀ (D : Subgroup X) (S : Subgroup D) [S.Normal] (Y : Fin 4 → Subgroup (D ⧸ S)),
      (∀ i, IsComponent (Y i)) → Function.Injective Y → (∀ i, IsSimpleGroup (Y i)) →
      (∀ i, 5 ∣ Nat.card (Y i)) → (∀ i, 2 ∣ Nat.card (Y i)) → False)
    {K : Subgroup (X ⧸ CFSG.pPrimeCore 3 X)} (hK : IsComponent K) :
    ∃ J ∈ thetaComponents 3 X, J.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X)) = K := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set O := CFSG.pPrimeCore 3 X
  set π := QuotientGroup.mk' O
  obtain ⟨hK₁p, hK₁s, hK₁m⟩ := exists_perfect_isSubnormal_map_eq (R := O) hK.1.1 hK.2
  set K₁ : Subgroup X := (CFSG.perfectResidual (K.comap π)).map (K.comap π).subtype
  set D : Subgroup X := K₁ ⊓ O
  have hD3 : ¬ 3 ∣ Nat.card D := fun h =>
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
      (CFSG.pPrimeCore_coprime_card (p := 3) (G := X)))
        (h.trans (Subgroup.card_dvd_of_le (inf_le_right : D ≤ O)))
  have hKD : K₁ ≤ Subgroup.normalizer (D : Set X) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (inf_le_left : D ≤ K₁)).mp
      (by rw [Subgroup.inf_subgroupOf_left]; infer_instance)
  set act := actOnQuot K₁ D hKD with hact
  have hinner : ∀ k : K₁, ∃ q : ↥D ⧸ CFSG.solvableRadical ↥D, act k = MulAut.conj q := fun k =>
    exists_conj_of_perfect_action hK₁p solvableRadical_quotient
      ((card_componentIndex_le_three hX hSz hFour hD3).trans (by norm_num))
      (fun L hL => component_commutator_le_inner hX hSz hD3 hL) act k
  set C : Subgroup X := act.ker.map K₁.subtype
  have hCK : C ≤ K₁ := Subgroup.map_subtype_le _
  have hlift : ∀ k : K₁, ∃ c ∈ C, π c = π (k : X) := by
    intro k
    obtain ⟨q, hq⟩ := hinner k
    obtain ⟨d, rfl⟩ := QuotientGroup.mk_surjective q
    have hdK : (d : X) ∈ K₁ := d.2.1
    refine ⟨(d : X)⁻¹ * k, ⟨⟨(d : X)⁻¹ * k, K₁.mul_mem (K₁.inv_mem hdK) k.2⟩,
      MonoidHom.mem_ker.mpr ?_, rfl⟩, ?_⟩
    · have : (⟨(d : X)⁻¹ * k, K₁.mul_mem (K₁.inv_mem hdK) k.2⟩ : K₁) = ⟨d, hdK⟩⁻¹ * k := rfl
      rw [this, map_mul, map_inv, hact, actOnQuot_of_mem K₁ D hKD d hdK, ← hact, hq]
      exact inv_mul_cancel _
    · have : π (d : X) = 1 := (QuotientGroup.eq_one_iff _).mpr d.2.2
      rw [map_mul, map_inv, this, inv_one, one_mul]
  have hπC : C.map π = K := by
    rw [← hK₁m]
    refine le_antisymm (Subgroup.map_mono hCK) ?_
    rintro _ ⟨k, hk, rfl⟩
    obtain ⟨c, hc, hck⟩ := hlift ⟨k, hk⟩
    exact ⟨c, hc, hck⟩
  set J : Subgroup X := (CFSG.perfectResidual C).map C.subtype with hJ
  have hJp : Group.IsPerfect J := isPerfect_perfectResidual_map C
  have hCs : C.IsSubnormal :=
    Subgroup.IsSubnormal.trans' (Subgroup.Normal.isSubnormal (inferInstance : act.ker.Normal)) hK₁s
  have hJs : J.IsSubnormal := isSubnormal_perfectResidual_map hCs
  have hJm : J.map π = K := by
    rw [hJ, map_perfectResidual_map π C, hπC]
    exact perfectResidual_map_eq_of_isPerfect hK.1.1
  set T : Subgroup X := (CFSG.solvableRadical ↥D).map D.subtype
  have hTs : Group.IsSolvable T := by
    have : Group.IsSolvable (CFSG.solvableRadical ↥D) := isSolvable_solvableRadical
    exact Group.isSolvable_of_surjective (D.subtype.subgroupMap_surjective _)
  have hJT : ∀ x ∈ J, x ∈ O → x ∈ T := by
    intro x hxJ hxO
    obtain ⟨c, hc, rfl⟩ := (Subgroup.map_subtype_le _ : J ≤ C) hxJ
    have hxD : (c : X) ∈ D := ⟨c.2, hxO⟩
    exact ⟨⟨c, hxD⟩, mem_radical_of_act_eq_one K₁ D hKD ⟨c, hxD⟩ c.2 hc, rfl⟩
  exact ⟨J, mem_thetaComponents_of_inf_le hJp hJs hTs hJT (by rw [hJm]; exact hK), hJm⟩

end CFSG.RankThree.PartTwo.Sec14.Liebeck1418Bridge
