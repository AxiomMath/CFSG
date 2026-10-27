module

public import CFSG.LocalAnalysis.StandardType.GGSixStepOneInputs
public import CFSG.LocalAnalysis.StandardType.GGOneFiveNbr
public import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeAmbientCentralizerGeneration
public import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeFactorization
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

open scoped commutatorElement

section General

variable {G : Type} [Group G]

theorem conj_mem_normalizer_of_mem_normalizer_map {H : Subgroup G} {y δ : G}
    (h : δ ∈ Subgroup.normalizer ((H.map (MulAut.conj y⁻¹).toMonoidHom : Subgroup G) : Set G)) :
    y * δ * y⁻¹ ∈ Subgroup.normalizer (H : Set G) := by
  rw [mem_normalizer_iff_map_conj] at h ⊢
  calc H.map (MulAut.conj (y * δ * y⁻¹)).toMonoidHom
      = ((H.map (MulAut.conj y⁻¹).toMonoidHom).map (MulAut.conj δ).toMonoidHom).map
          (MulAut.conj y).toMonoidHom := by
        rw [map_conj_map_conj, map_conj_map_conj, mul_assoc]
    _ = H := by rw [h, map_conj_inv_map_conj]

variable [Finite G]

theorem le_of_signalizer_plane {p : ℕ} (hp : p.Prime) {D M : Subgroup G} (K : G → Subgroup G)
    (hD : IsElemAbelian p D) (hDcard : Nat.card D = p ^ 2)
    (hCD : Subgroup.centralizer (D : Set G) ≤ M)
    (hcomp : ∀ d ∈ D, d ≠ 1 → IsComponentOf (K d) (Subgroup.centralizer {d}))
    (hnorm : ∀ d ∈ D, d ≠ 1 → ∀ K' : Subgroup G, IsComponentOf K' (Subgroup.centralizer {d}) →
      D ≤ Subgroup.normalizer (K' : Set G))
    (hinner : ∀ d ∈ D, d ≠ 1 → ∀ X : Subgroup G, X ≤ Subgroup.centralizer {d} →
      X ≤ Subgroup.normalizer (K d : Set G) → D ≤ Subgroup.normalizer (X : Set G) →
      Nat.Coprime p (Nat.card X) → ⁅X, D⁆ = X → X ≤ K d ⊔ Subgroup.centralizer (K d : Set G))
    (hKM : ∀ d ∈ D, d ≠ 1 → K d ⊔ Subgroup.centralizer (K d : Set G) ≤ M)
    (Q : Subgroup G) (hDQ : D ≤ Subgroup.normalizer (Q : Set G))
    (hQ : Nat.Coprime p (Nat.card Q)) : Q ≤ M := by
  have hpD : IsPGroup p D := fun e => ⟨1, Subtype.ext (by simpa using hD.2 e e.2)⟩
  have hcommD : ∀ a ∈ D, ∀ c ∈ D, a * c = c * a := fun a ha c hc =>
    congrArg Subtype.val (hD.1.is_comm.comm (⟨a, ha⟩ : ↥D) ⟨c, hc⟩)
  have hnd : ∀ {Y : Subgroup G}, Y ≤ Q → ¬ p ∣ Nat.card Y := fun hYQ hdvd =>
    (Nat.Prime.coprime_iff_not_dvd hp).mp hQ (hdvd.trans (Subgroup.card_dvd_of_le hYQ))
  rw [CFSG.RankThreeEvenClassification.Helpers.coprime_centralizer_generation_of_plane p hp D Q
    (fun e => Subtype.ext (by simpa using hD.2 e e.2)) hDcard (hnd le_rfl) hDQ]
  refine iSup₂_le fun e he => ?_
  have hdD : (e : G) ∈ D := e.2
  have hd1 : (e : G) ≠ 1 := fun h => he (Subtype.ext h)
  set d : G := (e : G) with hd
  set Y : Subgroup G := Q ⊓ Subgroup.centralizer ({d} : Set G) with hY
  have hDCd : D ≤ Subgroup.centralizer ({d} : Set G) := fun δ hδ =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hcommD δ hδ d hdD)
  have hDY : D ≤ Subgroup.normalizer (Y : Set G) := fun δ hδ =>
    mem_normalizer_inf (hDQ hδ) (Subgroup.le_normalizer (hDCd hδ))
  have hYp : ¬ p ∣ Nat.card Y := hnd inf_le_left
  rw [CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_centralizer_factorization p hp
    D Y hpD hYp hDY]
  refine sup_le ?_ (inf_le_right.trans hCD)
  have hXY : ⁅Y, D⁆ ≤ Y := Subgroup.le_normalizer_iff_commutator_le_left.mp hDY
  have hXd : ⁅Y, D⁆ ≤ Subgroup.centralizer {d} := hXY.trans inf_le_right
  have hDX : D ≤ Subgroup.normalizer ((⁅Y, D⁆ : Subgroup G) : Set G) :=
    Subgroup.normalizer_commutator_ge_right Y D
  have hXp : Nat.Coprime p (Nat.card (⁅Y, D⁆ : Subgroup G)) :=
    (Nat.Prime.coprime_iff_not_dvd hp).mpr (hnd (hXY.trans inf_le_left))
  have hXX : ⁅⁅Y, D⁆, D⁆ = ⁅Y, D⁆ :=
    CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_idempotent p hp D Y hpD hYp hDY
  have hXN : ⁅Y, D⁆ ≤ Subgroup.normalizer (K d : Set G) := by
    rw [Subgroup.commutator_le]
    intro y hy δ hδ
    have hyd : y ∈ Subgroup.centralizer ({d} : Set G) := hy.2
    have hcomp' : IsComponentOf ((K d).map (MulAut.conj y⁻¹).toMonoidHom)
        (Subgroup.centralizer {d}) := by
      have := CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_conj (hcomp d hdD hd1) y⁻¹
      rwa [map_conj_eq_of_mem (Subgroup.inv_mem _ hyd)] at this
    have h1 : y * δ * y⁻¹ ∈ Subgroup.normalizer (K d : Set G) :=
      conj_mem_normalizer_of_mem_normalizer_map (hnorm d hdD hd1 _ hcomp' hδ)
    have h2 : δ⁻¹ ∈ Subgroup.normalizer (K d : Set G) :=
      Subgroup.inv_mem _ (hnorm d hdD hd1 _ (hcomp d hdD hd1) hδ)
    rw [commutatorElement_def]
    exact Subgroup.mul_mem _ h1 h2
  exact (hinner d hdD hd1 _ hXd hXN hDX hXp hXX).trans (hKM d hdD hd1)

end General

section Ctx

variable {G : Type} [Group G] [Finite G] {U : Type} [Group U] {p : ℕ} {B Bs : Subgroup G}
  {x : G} {L D J : Subgroup G} {Δ : UniversalRootDatum U} {t : StatedLieTag} {n f : ℕ}
  {ψ : U →* G}

theorem GGSixCtxV2.ggKd_sup_centralizer_le (h : GGSixCtxV2 p B Bs x L D J Δ t n f ψ)
    (h66 : Subgroup.centralizer (J : Set G) ≤ ggM p B x L D J) {d : G} (hd : d ∈ D) :
    ggKd p B x L D J d ⊔ Subgroup.centralizer (ggKd p B x L D J d : Set G) ≤ ggM p B x L D J :=
  sup_le ((h.ggKd_le_ggG0 hd).trans Subgroup.le_normalizer)
    ((Subgroup.centralizer_le fun _ hj => le_ggKd p B x L D J d hj).trans h66)

theorem GGSixCtxV2.signalizer_le (h : GGSixCtxV2 p B Bs x L D J Δ t n f ψ)
    (h62 : Subgroup.centralizer (D : Set G) ≤ ggM p B x L D J)
    (h65 : ∀ d ∈ D, d ≠ 1 → IsComponentOf (ggKd p B x L D J d) (Subgroup.centralizer {d}))
    (h66 : Subgroup.centralizer (J : Set G) ≤ ggM p B x L D J)
    (h68 : ∀ d ∈ D, d ≠ 1 → ∀ K : Subgroup G, IsComponentOf K (Subgroup.centralizer {d}) →
      D ≤ Subgroup.normalizer (K : Set G))
    (hinner : ∀ d ∈ D, d ≠ 1 → ∀ X : Subgroup G, X ≤ Subgroup.centralizer {d} →
      X ≤ Subgroup.normalizer (ggKd p B x L D J d : Set G) →
      D ≤ Subgroup.normalizer (X : Set G) → Nat.Coprime p (Nat.card X) → ⁅X, D⁆ = X →
        X ≤ ggKd p B x L D J d ⊔ Subgroup.centralizer (ggKd p B x L D J d : Set G)) :
    ∀ Q : Subgroup G, D ≤ Subgroup.normalizer (Q : Set G) → Nat.Coprime p (Nat.card Q) →
      Q ≤ ggM p B x L D J :=
  le_of_signalizer_plane h.prime (ggKd p B x L D J) h.d_elem h.card_d h62 h65 h68 hinner
    fun _ hd _ => h.ggKd_sup_centralizer_le h66 hd

end Ctx

end CFSG.StandardType
