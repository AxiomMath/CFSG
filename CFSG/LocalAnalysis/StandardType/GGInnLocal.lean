module

public import CFSG.LocalAnalysis.StandardType.GGInnLocalDichotomy
public import CFSG.LocalAnalysis.StandardType.GGStdSubExist
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeA
public import CFSG.LieType.CentralExt.CoprimeLift

public section

namespace CFSG.StandardType

open CFSG.Assembly TableB

section Prime

variable {L' R : Type} [Group L'] [Group R]

theorem mem_range_conj_of_induces_inn {ψ : L' →* R} (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤) {a : MulAut L'}
    {φ : MulAut R} (h : ∀ l, φ (ψ l) = ψ (a l))
    (hφ : φ ∈ (MulAut.conj : R →* MulAut R).range) :
    a ∈ (MulAut.conj : L' →* MulAut L').range := by
  obtain ⟨r, rfl⟩ := hφ
  obtain ⟨t, rfl⟩ := hψ r
  refine ⟨t, ?_⟩
  set c : MulAut L' := (MulAut.conj t)⁻¹ * a with hc
  have hcψ : ∀ l, ψ (c l) = ψ l := by
    intro l
    have h1 : c l = t⁻¹ * a l * t := by
      rw [hc, MulAut.mul_apply, MulAut.conj_inv_apply]
    rw [h1, map_mul, map_mul, map_inv, ← h l, MulAut.conj_apply]
    group
  have hz : ∀ l, c l * l⁻¹ ∈ Subgroup.center L' := fun l => hker (by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hcψ l, mul_inv_cancel])
  let f : L' →* L' :=
    { toFun := fun l => c l * l⁻¹
      map_one' := by simp
      map_mul' := fun a' b' => by
        have h' := (Subgroup.mem_center_iff.mp (hz b')) a'⁻¹
        simp only [map_mul, mul_inv_rev]
        calc c a' * c b' * (b'⁻¹ * a'⁻¹) = c a' * ((c b' * b'⁻¹) * a'⁻¹) := by group
          _ = c a' * (a'⁻¹ * (c b' * b'⁻¹)) := by rw [h']
          _ = c a' * a'⁻¹ * (c b' * b'⁻¹) := by group }
  have hfker : commutator L' ≤ f.ker := by
    rw [commutator_def, Subgroup.commutator_le]
    intro u _ v _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact (Subgroup.mem_center_iff.mp (hz v)) (f u)
  have hc1 : c = 1 := by
    ext l
    have h1 : f l = 1 := hfker (by rw [hperf]; exact Subgroup.mem_top _)
    exact mul_inv_eq_one.mp h1
  rw [hc, inv_mul_eq_one] at hc1
  exact hc1

theorem not_ggDeltaAdm_of_prime {p : ℕ} {I : Set (MulAut R)} (hO : GGOutdiagPrime p R I)
    (hZ : GGCenterPrime p R) [Finite L'] {ψ : L' →* R} (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    {A : Subgroup (MulAut L')} (hA : IsElemAbelian p A)
    (hAI : ∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) : ¬ GGDeltaAdm p L' A := by
  rintro ⟨-, ⟨⟨a, haA, hout⟩, -⟩ | ⟨hdvd, -⟩⟩
  · obtain ⟨φ, hφI, hφ⟩ := hAI a haA
    have hφp : φ ^ p = 1 := by
      ext r
      obtain ⟨l, rfl⟩ := hψ r
      rw [MulAut.one_apply]
      have h1 : ∀ n : ℕ, ∀ l, (φ ^ n) (ψ l) = ψ ((a ^ n) l) := by
        intro n
        induction n with
        | zero => intro l; rfl
        | succ n ih =>
          intro l
          rw [pow_succ, pow_succ, MulAut.mul_apply, MulAut.mul_apply, hφ, ih]
      rw [h1 p l, hA.2 a haA, MulAut.one_apply]
    exact hout (mem_range_conj_of_induces_inn hψ hker hperf hφ (hO φ hφI hφp))
  · exact hZ L' ψ hψ hker hperf hdvd

theorem ggDeltaLocal_of_prime {p r : ℕ} {I : Set (MulAut R)} (hO : GGOutdiagPrime p R I)
    (hZ : GGCenterPrime p R) : GGDeltaLocal p r R I :=
  fun _ _ _ _ hψ hker hperf _ hA hAI _ _ hadm =>
    (not_ggDeltaAdm_of_prime hO hZ hψ hker hperf hA hAI hadm).elim

theorem ggBstarBoundDelta_of_prime {p r : ℕ} {I : Set (MulAut R)} (hO : GGOutdiagPrime p R I)
    (hZ : GGCenterPrime p R) : GGBstarBoundDelta p r R I :=
  fun _ _ _ _ hψ hker hperf _ _ hA hAI _ _ hadm _ _ =>
    (not_ggDeltaAdm_of_prime hO hZ hψ hker hperf hA hAI hadm).elim

end Prime

section Config

variable {G : Type} [Group G]

theorem exists_two_subgroup_of_ggGamma {B L : Subgroup G}
    (hBN : B ≤ Subgroup.normalizer (L : Set G))
    (h : ∃ U : Subgroup L, U ≠ ⊥ ∧ IsPGroup 2 U ∧
      ∀ a ∈ (ggGamma L hBN).range, ∀ u ∈ U, a u ∈ U) :
    ∃ U : Subgroup G, U ≤ L ∧ U ≠ ⊥ ∧ IsPGroup 2 U ∧ B ≤ Subgroup.normalizer (U : Set G) := by
  obtain ⟨U, hU1, hU2, hAU⟩ := h
  refine ⟨U.map L.subtype, Subgroup.map_subtype_le _, ?_, hU2.map _, ?_⟩
  · rw [Ne, Subgroup.map_eq_bot_iff_of_injective _ L.subtype_injective]
    exact hU1
  · rw [Subgroup.le_normalizer_iff]
    rintro b hb _ ⟨u, hu, rfl⟩
    exact ⟨_, hAU _ ⟨⟨b, hb⟩, rfl⟩ u hu, ggGamma_coe L hBN ⟨b, hb⟩ u⟩

variable [Finite G]

theorem exists_two_subgroup_of_ggBeta {B L : Subgroup G}
    (hBN : B ≤ Subgroup.normalizer (L : Set G))
    {R : Type} [Group R] (θ : L ⧸ Subgroup.center L ≃* R)
    (h : ∃ U : Subgroup R, U ≠ ⊥ ∧ IsPGroup 2 U ∧
      ∀ a ∈ (ggBeta L θ hBN).range, ∀ u ∈ U, a u ∈ U) :
    ∃ U : Subgroup G, U ≤ L ∧ U ≠ ⊥ ∧ IsPGroup 2 U ∧
      B ≤ Subgroup.normalizer (U : Set G) := by
  obtain ⟨U, hU1, hU2, hAU⟩ := h
  let W := CFSG.LieType.CentralExt.liftSubgroup 2 (ggQuotHom θ) U
  have hcen : (ggQuotHom θ).ker ≤ Subgroup.center L := (ker_ggQuotHom θ).le
  have hW1 : W ≠ ⊥ :=
    CFSG.LieType.CentralExt.liftSubgroup_ne_bot (ggQuotHom_surjective θ) hcen hU2 hU1
  have hW2 : IsPGroup 2 W :=
    CFSG.LieType.CentralExt.liftSubgroup_isPGroup hcen hU2
  apply exists_two_subgroup_of_ggGamma hBN
  refine ⟨W, hW1, hW2, ?_⟩
  rintro a ⟨b, rfl⟩ u hu
  obtain ⟨huU, n, hn⟩ :=
    (CFSG.LieType.CentralExt.mem_liftSubgroup_iff hcen hU2).mp hu
  apply (CFSG.LieType.CentralExt.mem_liftSubgroup_iff hcen hU2).mpr
  refine ⟨?_, n, ?_⟩
  · rw [← ggBeta_ggQuotHom L hBN θ b u]
    exact hAU _ ⟨b, rfl⟩ _ huU
  · rw [MulEquiv.orderOf_eq, hn]

theorem exists_innLocal_of_data {p r : ℕ} {B : Subgroup G} {x : G} {L : Subgroup G}
    (hT : GGThmIHyp p B x L) (hnc : ∃ S : Subgroup G, S ≤ L ∧ IsPGroup p S ∧ ¬ IsCyclic S)
    (hL : commutator L = ⊤) {R : Type} [Group R] (θ : L ⧸ Subgroup.center L ≃* R)
    {I : Set (MulAut R)} (hBN : B ≤ Subgroup.normalizer (L : Set G))
    (h3 : ∀ b ∈ B, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ)
    (hOD : GGOutdiagOdd p R I) (hlift : GGTorusLift p r R) (hloc : GGDeltaLocal p r R I) :
    ∃ U : Subgroup G, U ≤ L ∧ U ≠ ⊥ ∧ IsPGroup 2 U ∧ B ≤ Subgroup.normalizer (U : Set G) := by
  obtain ⟨-, -, -, -, -, hβ, hS, hst⟩ := hT
  have hp : p.Prime := hβ.1
  rcases ggInnLocal_or_delta hp hβ.2.1 hS hnc hL θ hBN h3 hOD hst.2.1 with hU | hδ
  · exact hU
  · obtain ⟨hA, hAI, hr, h3'⟩ := ggGamma_range_props hp hS hβ.2.2.2 hL θ hBN h3 hlift
    exact exists_two_subgroup_of_ggGamma hBN (hloc L (ggQuotHom θ) (ggQuotHom_surjective θ)
      (by rw [ker_ggQuotHom]) hL _ hA hAI hr h3' (ggDeltaAdm_of_delta hp hS hBN hδ))

theorem card_le_of_bstarBoundDelta {p r : ℕ} (hp : p.Prime) {B : Subgroup G} {x : G}
    {L : Subgroup G} (hS : LargeEvenSStar p B x L) (h4 : 4 ≤ LargeEvenTwoLocalRank p G)
    (hnc : ∃ S : Subgroup G, S ≤ L ∧ IsPGroup p S ∧ ¬ IsCyclic S) (hL : commutator L = ⊤)
    {R : Type} [Group R] (θ : L ⧸ Subgroup.center L ≃* R) {I : Set (MulAut R)}
    (hBN : B ≤ Subgroup.normalizer (L : Set G))
    (h3 : ∀ b ∈ B, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ)
    (hadm : GGDeltaAdm p L (ggGamma L hBN).range) (hlift : GGTorusLift p r R)
    (hbound : GGBstarBoundDelta p r R I) {E : Subgroup G} (hE : IsElemAbelian p E)
    (hBE : B ≤ E) : Nat.card E ≤ p * Nat.card B := by
  have := Fact.mk hp
  have hEC : E ≤ Subgroup.centralizer ({x} : Set G) := fun e he =>
    Subgroup.mem_centralizer_singleton_iff.mpr (IsElemAbelian.comm hE he (hBE hS.2.1))
  have hEN : E ≤ Subgroup.normalizer (L : Set G) := fun e he =>
    mem_normalizer_of_sstar hS hnc (hEC he)
  obtain ⟨hA, hAI, hr, h3'⟩ := ggGamma_range_props hp hS h4 hL θ hBN h3 hlift
  have hAAh : (ggGamma L hBN).range ≤ (ggGamma L hEN).range := by
    rintro _ ⟨b, rfl⟩
    exact ⟨⟨b, hBE b.2⟩, rfl⟩
  have hAh : IsElemAbelian p (ggGamma L hEN).range := isElemAbelian_range
    (fun a b => Subtype.ext (IsElemAbelian.comm hE a.2 b.2))
    (fun a => Subtype.ext (by simpa using hE.2 a a.2)) _
  have hle := hbound L (ggQuotHom θ) (ggQuotHom_surjective θ) (by rw [ker_ggQuotHom]) hL _ _
    hA hAI hr h3' hadm hAAh hAh
  have hcB := card_range_ggGamma_mul L hBN hp hS
  have hcE := card_range_ggGamma_mul_of hp hE (hBE hS.2.1) hS.2.2.1 hS.2.2.2.1.1 hS.2.2.2.2 hEN
  rw [← hcE, ← hcB]
  calc Nat.card (ggGamma L hEN).range * p ≤ p * Nat.card (ggGamma L hBN).range * p :=
        Nat.mul_le_mul_right p hle
    _ = p * (Nat.card (ggGamma L hBN).range * p) := by ring

theorem exists_ggBstar_of_data {p r : ℕ} {B : Subgroup G} {x : G} {L : Subgroup G}
    (hT : GGThmIHyp p B x L) (hnc : ∃ S : Subgroup G, S ≤ L ∧ IsPGroup p S ∧ ¬ IsCyclic S)
    (hL : commutator L = ⊤) {R : Type} [Group R] (θ : L ⧸ Subgroup.center L ≃* R)
    {I : Set (MulAut R)} (hBN : B ≤ Subgroup.normalizer (L : Set G))
    (h3 : ∀ b ∈ B, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ)
    (hOD : GGOutdiagOdd p R I) (hlift : GGTorusLift p r R) (hinn : GGBstarBoundInn p r R I)
    (hdel : GGDeltaLocal p r R I ∨ GGBstarBoundDelta p r R I) :
    ∃ Bs : Subgroup G, GGBstar p B Bs := by
  obtain ⟨-, -, -, -, -, hβ, hS, hst⟩ := hT
  have hp : p.Prime := hβ.1
  have hcase : (∃ U : Subgroup G, U ≤ L ∧ U ≠ ⊥ ∧ IsPGroup 2 U ∧
      B ≤ Subgroup.normalizer (U : Set G)) → ∃ Bs : Subgroup G, GGBstar p B Bs :=
    fun hU => exists_ggBstar_of_card_le hS.1.1 fun E hE hBE =>
      card_le_of_bstarBoundInn hp hS hβ.2.2.2 hnc hL θ hBN h3 hU hlift hinn hE hBE
  rcases ggInnLocal_or_delta hp hβ.2.1 hS hnc hL θ hBN h3 hOD hst.2.1 with hU | hδ
  · exact hcase hU
  · have hadm := ggDeltaAdm_of_delta hp hS hBN hδ
    rcases hdel with hloc | hbd
    · obtain ⟨hA, hAI, hr, h3'⟩ := ggGamma_range_props hp hS hβ.2.2.2 hL θ hBN h3 hlift
      exact hcase (exists_two_subgroup_of_ggGamma hBN (hloc L (ggQuotHom θ)
        (ggQuotHom_surjective θ) (by rw [ker_ggQuotHom]) hL _ hA hAI hr h3' hadm))
    · exact exists_ggBstar_of_card_le hS.1.1 fun E hE hBE =>
        card_le_of_bstarBoundDelta hp hS hβ.2.2.2 hnc hL θ hBN h3 hadm hlift hbd hE hBE

end Config

theorem ggInnLocalInputOn_of_labels {S : ℕ → LargeEvenLabel → Prop} (ha₀ : GGLNoncyclicInput)
    (h : ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → LargeEvenInLambda2 lab → S p lab →
      LargeEvenSplit p lab →
      LargeEvenLabelAll lab fun R _ I _ => GGOutdiagOdd p R I ∧
        ∃ r, GGTorusLift p r R ∧ GGDeltaLocal p r R I) :
    ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B : Subgroup G) (x : G) (L : Subgroup G),
      GGThmIHyp p B x L →
      LargeEvenMarking L (fun lab _ _ I _ θ => S p lab ∧ LargeEvenSplit p lab ∧
        B ≤ Subgroup.normalizer (L : Set G) ∧
        ∀ b ∈ B, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ) →
      ∃ U : Subgroup G, U ≤ L ∧ U ≠ ⊥ ∧ IsPGroup 2 U ∧ B ≤ Subgroup.normalizer (U : Set G) := by
  intro G _ _ p B x L hT hM
  have hnc := ha₀ G p B x L hT
  have hp : p.Prime := hT.2.2.2.2.2.1.1
  have hM' := largeEvenMarking_and_labelAll (S := fun lab => S p lab ∧ LargeEvenSplit p lab)
    (fun lab hlab hs => h p lab hp hlab hs.1 hs.2) (fun _ _ _ _ _ _ hP => ⟨hP.1, hP.2.1⟩) hM
  obtain ⟨hL, lab, -, hraw⟩ := hM'
  obtain ⟨R, _, I, F, -, -, θ, ⟨-, -, hBN, h3⟩, hOD, r, hlift, hloc⟩ :=
    largeEvenRawDatum_exists hraw
  exact exists_innLocal_of_data hT hnc hL θ hBN h3 hOD hlift hloc

theorem ggInnLocalInput_of_labels (ha₀ : GGLNoncyclicInput)
    (h : ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → LargeEvenInLambda2 lab →
      LargeEvenSplit p lab →
      LargeEvenLabelAll lab fun R _ I _ => GGOutdiagOdd p R I ∧
        ∃ r, GGTorusLift p r R ∧ GGDeltaLocal p r R I) :
    GGInnLocalInput := by
  intro G _ _ p B x L hT
  have hnc := ha₀ G p B x L hT
  have hp : p.Prime := hT.2.2.2.2.2.1.1
  have hM := largeEvenMarking_and_labelAll (S := fun lab => LargeEvenSplit p lab)
    (fun lab hlab hs => h p lab hp hlab hs) (fun _ _ _ _ _ _ hP => hP.1) hT.2.2.2.2.2.2.2.1
  obtain ⟨hL, lab, -, hraw⟩ := hM
  obtain ⟨R, _, I, F, -, -, θ, ⟨-, hBN, h3⟩, hOD, r, hlift, hloc⟩ :=
    largeEvenRawDatum_exists hraw
  exact exists_innLocal_of_data hT hnc hL θ hBN h3 hOD hlift hloc

theorem ggBstarInputOn_of_labels_delta {S : ℕ → LargeEvenLabel → Prop}
    (ha₀ : GGLNoncyclicInput)
    (h : ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → LargeEvenInLambda2 lab → S p lab →
      LargeEvenSplit p lab →
      LargeEvenLabelAll lab fun R _ I _ => GGOutdiagOdd p R I ∧ ∃ r, GGTorusLift p r R ∧
        GGBstarBoundInn p r R I ∧ (GGDeltaLocal p r R I ∨ GGBstarBoundDelta p r R I)) :
    GGBstarInputOn S := by
  intro G _ _ p B x L hT hM
  have hnc := ha₀ G p B x L hT
  have hp : p.Prime := hT.2.2.2.2.2.1.1
  have hM' := largeEvenMarking_and_labelAll (S := fun lab => S p lab ∧ LargeEvenSplit p lab)
    (fun lab hlab hs => h p lab hp hlab hs.1 hs.2) (fun _ _ _ _ _ _ hP => ⟨hP.1, hP.2.1⟩) hM
  obtain ⟨hL, lab, -, hraw⟩ := hM'
  obtain ⟨R, _, I, F, -, -, θ, ⟨-, -, hBN, h3⟩, hOD, r, hlift, hinn, hdel⟩ :=
    largeEvenRawDatum_exists hraw
  exact exists_ggBstar_of_data hT hnc hL θ hBN h3 hOD hlift hinn hdel

theorem ggBstarInput_of_labels_delta (ha₀ : GGLNoncyclicInput)
    (h : ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → LargeEvenInLambda2 lab →
      LargeEvenSplit p lab →
      LargeEvenLabelAll lab fun R _ I _ => GGOutdiagOdd p R I ∧ ∃ r, GGTorusLift p r R ∧
        GGBstarBoundInn p r R I ∧ (GGDeltaLocal p r R I ∨ GGBstarBoundDelta p r R I)) :
    GGBstarInput := by
  intro G _ _ p B x L hT
  have hnc := ha₀ G p B x L hT
  have hp : p.Prime := hT.2.2.2.2.2.1.1
  have hM := largeEvenMarking_and_labelAll (S := fun lab => LargeEvenSplit p lab)
    (fun lab hlab hs => h p lab hp hlab hs) (fun _ _ _ _ _ _ hP => hP.1) hT.2.2.2.2.2.2.2.1
  obtain ⟨hL, lab, -, hraw⟩ := hM
  obtain ⟨R, _, I, F, -, -, θ, ⟨-, hBN, h3⟩, hOD, r, hlift, hinn, hdel⟩ :=
    largeEvenRawDatum_exists hraw
  exact exists_ggBstar_of_data hT hnc hL θ hBN h3 hOD hlift hinn hdel

end CFSG.StandardType
