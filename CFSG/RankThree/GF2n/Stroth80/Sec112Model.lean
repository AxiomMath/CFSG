module

public import CFSG.RankThree.GF2n.Stroth80.Sec112Basic
public import CFSG.RankThree.GF2n.Stroth80.Sec114
public import CFSG.RankThree.GF2n.Smith81.OrthRootInvol
import CFSG.RankThree.GF2n.Stroth80.Sec123Order
import CFSG.RankThree.GF2n.Stroth80.GuralnickSec1110EbarSiegel
import CFSG.Timmesfeld.RootInvolutionConj

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.RankThree.OrthogonalInvolutions (commSpace commSpace_conj)
open CFSG.RankThree.GF2n.Smith81 (IsOrthA2)
open CFSG.Timmesfeld (IsRootInvolutionSet)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
variable {K : Type} [Field K] [Finite K] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}

theorem isA2_iff_isOrthA2 (H : StrothHyp M Q Z) (h : GlobalModelData M Q Z γ M₀)
    {φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)}
    (hφπ : ∀ (g : ↥(H0 M Z)) (x : G), x ∈ Q → M₀.π ((g : G) * x * (g : G)⁻¹) = φ g (M₀.π x))
    (hφker : ∀ g : ↥(H0 M Z), φ g = 1 ↔ (g : G) ∈ Q)
    (hφiso : ∀ (g : ↥(H0 M Z)) (e : M₀.E), M₀.Qf (φ g e) = M₀.Qf e) (g : ↥(H0 M Z)) :
    IsA2 Q Z (g : G) ↔ IsOrthA2 M₀.toQuadraticForm (φ g) := by
  have hgM : (g : G) ∈ M := g.2.1
  have hQn : ∀ x ∈ Q, (g : G) * x * (g : G)⁻¹ ∈ Q := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp (H.Q_normal.2 hgM) x).mp hx
  have hQn' : ∀ x ∈ Q, (g : G)⁻¹ * x * (g : G) ∈ Q := fun x hx => by
    have := (Subgroup.mem_normalizer_iff.mp (H.Q_normal.2 (M.inv_mem hgM)) x).mp hx
    simpa using this
  have hK : 1 < Nat.card K := by
    rw [h.card]
    have := H.q4
    omega
  rw [isA2_iff M₀ h.reg h.card hK (φ g) hQn hQn' (hφπ g)]
  have hsq : φ g * φ g = 1 ↔ (g : G) ^ 2 ∈ Q := by
    rw [← map_mul, hφker, Subgroup.coe_mul, ← pow_two]
  have hO : φ g ∈ TauCeti.QuadraticMap.orthogonalGroup M₀.toQuadraticForm :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr (hφiso g)
  constructor
  · rintro ⟨-, hg2, hfin, hvan⟩
    exact ⟨hO, hsq.mpr hg2, hfin, hvan⟩
  · intro hA
    exact ⟨fun hgQ => hA.ne_one ((hφker g).mpr hgQ), hsq.mp hA.mul_self, hA.finrank_eq,
      hA.vanish⟩

@[expose] noncomputable def barH0Act [(Q.subgroupOf M).Normal]
    (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)) (hφker : ∀ g : ↥(H0 M Z), φ g = 1 ↔ (g : G) ∈ Q) :
    ↥(bar M Q (H0 M Z)) →* (M₀.E ≃ₗ[K] M₀.E) where
  toFun c := liftF φ c
  map_one' := liftF_one hφker
  map_mul' c d := liftF_mul hφker (mem_bar_H0_iff.mp c.2) (mem_bar_H0_iff.mp d.2)

omit [Finite K] in
theorem barH0Act_apply [(Q.subgroupOf M).Normal] (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφker : ∀ g : ↥(H0 M Z), φ g = 1 ↔ (g : G) ∈ Q) (c : ↥(bar M Q (H0 M Z))) :
    barH0Act φ hφker c = liftF φ c :=
  rfl

omit [Finite K] in
theorem barH0Act_injective [(Q.subgroupOf M).Normal] {φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)}
    (hφker : ∀ g : ↥(H0 M Z), φ g = 1 ↔ (g : G) ∈ Q) :
    Function.Injective (barH0Act φ hφker) := by
  refine (injective_iff_map_eq_one _).mpr fun c hc => ?_
  obtain ⟨g, hg⟩ := mem_bar_H0_iff.mp c.2
  have h1 : φ g = 1 := by
    rw [← liftF_mkH hφker g, hg]
    exact hc
  apply Subtype.ext
  show (c : Mbar M Q) = 1
  rw [← hg]
  exact (mkH_eq_one_iff g).mpr ((hφker g).mp h1)

omit [Finite K] in
theorem orderOf_liftF [(Q.subgroupOf M).Normal] {φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)}
    (hφker : ∀ g : ↥(H0 M Z), φ g = 1 ↔ (g : G) ∈ Q) {c : Mbar M Q}
    (hc : c ∈ bar M Q (H0 M Z)) : orderOf (liftF φ c) = orderOf c := by
  have h1 := orderOf_injective (barH0Act φ hφker) (barH0Act_injective hφker) ⟨c, hc⟩
  rw [Subgroup.orderOf_mk] at h1
  exact h1

theorem mem_A2Set_iff_isOrthA2 [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B)
    (h : GlobalModelData M Q Z γ M₀) {φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)}
    (hφπ : ∀ (g : ↥(H0 M Z)) (x : G), x ∈ Q → M₀.π ((g : G) * x * (g : G)⁻¹) = φ g (M₀.π x))
    (hφker : ∀ g : ↥(H0 M Z), φ g = 1 ↔ (g : G) ∈ Q)
    (hφiso : ∀ (g : ↥(H0 M Z)) (e : M₀.E), M₀.Qf (φ g e) = M₀.Qf e) {τ : Mbar M Q}
    (hτ : τ ∈ bar M Q (H0 M Z)) :
    τ ∈ A2Set M Q Z ↔ IsOrthA2 M₀.toQuadraticForm (liftF φ τ) := by
  have hQH : Q ≤ H0 M Z := (le_sup_left : Q ≤ LB M Q B).trans hc.LB_le_H0
  obtain ⟨g, rfl⟩ := mem_bar_H0_iff.mp hτ
  rw [liftF_mkH hφker]
  constructor
  · rintro ⟨e, he, hA⟩
    have heb : QuotientGroup.mk' (Q.subgroupOf M) e ∈ bar M Q (H0 M Z) := by
      rw [QuotientGroup.mk'_apply, he]
      exact hτ
    have heH : (e : G) ∈ H0 M Z := (mk_mem_bar_iff_sec4 hQH e).mp heb
    have h1 : mkH M Q Z ⟨e, heH⟩ = mkH M Q Z g := he
    rw [← phi_eq_of_mkH_eq hφker h1]
    exact (isA2_iff_isOrthA2 hc.hyp h hφπ hφker hφiso ⟨e, heH⟩).mp hA
  · intro hO
    exact ⟨⟨g, H0_le_M g.2⟩, rfl, (isA2_iff_isOrthA2 hc.hyp h hφπ hφker hφiso g).mpr hO⟩

theorem Ctx.isOrthA2_liftF_of_mem_Ebar [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B)
    (h : GlobalModelData M Q Z γ M₀) {φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)}
    (hφπ : ∀ (g : ↥(H0 M Z)) (x : G), x ∈ Q → M₀.π ((g : G) * x * (g : G)⁻¹) = φ g (M₀.π x))
    (hφker : ∀ g : ↥(H0 M Z), φ g = 1 ↔ (g : G) ∈ Q) {e : Mbar M Q}
    (he : e ∈ Ebar M Q Z B) : IsOrthA2 M₀.toQuadraticForm (liftF φ e) := by
  obtain ⟨g, rfl⟩ := mem_bar_H0_iff.mp (hc.Ebar_subset_H he)
  rw [liftF_mkH hφker]
  exact hc.isOrthA2_of_mem_Ebar h h.card g.2 he (hφπ g)

omit [Finite K] in
theorem commSpace_liftF_conj [(Q.subgroupOf M).Normal] {φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)}
    (hφker : ∀ g : ↥(H0 M Z), φ g = 1 ↔ (g : G) ∈ Q) {c t : Mbar M Q}
    (hc : c ∈ bar M Q (H0 M Z)) (ht : t ∈ bar M Q (H0 M Z)) :
    commSpace (liftF φ (c * t * c⁻¹)) =
      (commSpace (liftF φ t)).map (liftF φ c : M₀.E →ₗ[K] M₀.E) := by
  have e1 : liftF φ (c * t * c⁻¹) = liftF φ c * liftF φ t * (liftF φ c)⁻¹ := by
    have h1 : barH0Act φ hφker (⟨c, hc⟩ * ⟨t, ht⟩ * (⟨c, hc⟩ : ↥(bar M Q (H0 M Z)))⁻¹) =
        barH0Act φ hφker ⟨c, hc⟩ * barH0Act φ hφker ⟨t, ht⟩ * (barH0Act φ hφker ⟨c, hc⟩)⁻¹ := by
      rw [map_mul, map_mul, map_inv]
    exact h1
  rw [e1, commSpace_conj]

theorem isRootInvolutionSet_A2Set_inter [(Q.subgroupOf M).Normal] [CharP K 2]
    (hc : Ctx M Q Z B) (h : GlobalModelData M Q Z γ M₀) {φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)}
    (hφπ : ∀ (g : ↥(H0 M Z)) (x : G), x ∈ Q → M₀.π ((g : G) * x * (g : G)⁻¹) = φ g (M₀.π x))
    (hφker : ∀ g : ↥(H0 M Z), φ g = 1 ↔ (g : G) ∈ Q)
    (hφiso : ∀ (g : ↥(H0 M Z)) (e : M₀.E), M₀.Qf (φ g e) = M₀.Qf e) :
    IsRootInvolutionSet (A2Set M Q Z ∩ (bar M Q (H0 M Z) : Set (Mbar M Q))) := by
  have hD0 := Smith81.isRootInvolutionSet_isOrthA2
    (polarBilin_toQuadraticForm_nondegenerate M₀) (⊤ : Subgroup (M₀.E ≃ₗ[K] M₀.E))
  have hD1 := Smith81.isRootInvolutionSet_preimage (barH0Act φ hφker)
    (barH0Act_injective hφker) hD0
  have hD2 := CFSG.Timmesfeld.isRootInvolutionSet_image_ne_one (bar M Q (H0 M Z)).subtype hD1
  have hset : A2Set M Q Z ∩ (bar M Q (H0 M Z) : Set (Mbar M Q)) =
      (bar M Q (H0 M Z)).subtype '' {x | x ∈ barH0Act φ hφker ⁻¹'
        {t | t ∈ (⊤ : Subgroup (M₀.E ≃ₗ[K] M₀.E)) ∧ IsOrthA2 M₀.toQuadraticForm t} ∧
          (bar M Q (H0 M Z)).subtype x ≠ 1} := by
    ext τ
    constructor
    · rintro ⟨hτA, hτH⟩
      have hO := (mem_A2Set_iff_isOrthA2 hc h hφπ hφker hφiso hτH).mp hτA
      refine ⟨⟨τ, hτH⟩, ⟨⟨Subgroup.mem_top _, hO⟩, fun h1 => hO.ne_one ?_⟩, rfl⟩
      rw [show τ = 1 from h1]
      exact liftF_one hφker
    · rintro ⟨x, ⟨⟨-, hO⟩, -⟩, rfl⟩
      exact ⟨(mem_A2Set_iff_isOrthA2 hc h hφπ hφker hφiso x.2).mpr hO, x.2⟩
  rw [hset]
  exact hD2

theorem Ctx.conj_mem_A2Set_inter [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) (g : Mbar M Q)
    {x : Mbar M Q} (hx : x ∈ A2Set M Q Z ∩ (bar M Q (H0 M Z) : Set (Mbar M Q))) :
    g * x * g⁻¹ ∈ A2Set M Q Z ∩ (bar M Q (H0 M Z) : Set (Mbar M Q)) := by
  obtain ⟨⟨e, rfl, hA⟩, hH⟩ := hx
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective g
  refine ⟨⟨y * e * y⁻¹, ?_, ?_⟩, hc.normal_bar_H0.conj_mem _ hH _⟩
  · simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  · have h1 := hA.conj (y : G)
    rw [hc.conj_Q_eq y.2, hc.conj_Z_eq y.2] at h1
    exact h1

theorem Ctx.Ebar_subset_A2Set_inter [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) :
    Ebar M Q Z B ⊆ A2Set M Q Z ∩ (bar M Q (H0 M Z) : Set (Mbar M Q)) :=
  fun _ hd => ⟨hd.1, hc.Ebar_subset_H hd⟩

end CFSG.RankThree.GF2n.Stroth80
