module

public import CFSG.LocalAnalysis.WeakClosure81.SevenElevenTri
public import CFSG.LocalAnalysis.WeakClosure81.OddTranspListTriality

public section

namespace CFSG.LocalAnalysis.WeakClosure81.SevenElevenTri

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open CFSG.LocalAnalysis.WeakClosure81.SevenK

theorem isTrialityOddTransp_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) {s : X}
    (h : IsTrialityOddTransp Y (e s)) : IsTrialityOddTransp X s := by
  rw [IsTrialityOddTransp] at h ⊢
  obtain ⟨ε, hT⟩ := h
  refine ⟨ε.comp e.toMonoidHom, ?_, ?_, ?_, ?_⟩
  · exact hT.surjective.comp e.surjective
  · simpa using hT.isSwap
  · rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    have hx' : e x ∈ Subgroup.centralizer (ε.ker : Set Y) := by
      rw [Subgroup.mem_centralizer_iff] at hx ⊢
      intro y hy
      obtain ⟨z, rfl⟩ := e.surjective y
      have hz : z ∈ (ε.comp e.toMonoidHom).ker := by
        rw [MonoidHom.mem_ker]
        simpa using (MonoidHom.mem_ker.mp hy)
      rw [← map_mul, ← map_mul, hx z hz]
    rw [hT.centralizer_ker, Subgroup.mem_bot] at hx'
    exact e.injective (by rw [hx', map_one])
  · obtain ⟨f, F, hF, hFin, hcard, ψ₀, hrank⟩ := hT.orth
    refine ⟨f, F, hF, hFin, hcard, ?_⟩
    let LX : Subgroup X := (ε.comp e.toMonoidHom).ker ⊔ Subgroup.zpowers s
    let LY : Subgroup Y := ε.ker ⊔ Subgroup.zpowers (e s)
    have hLXmap : LX.map e.toMonoidHom = LY := by
      have hk : (ε.comp e.toMonoidHom).ker.map e.toMonoidHom = ε.ker := by
        rw [← MonoidHom.comap_ker]
        exact Subgroup.map_comap_eq_self_of_surjective e.surjective ε.ker
      show ((ε.comp e.toMonoidHom).ker ⊔ Subgroup.zpowers s).map e.toMonoidHom = LY
      rw [Subgroup.map_sup, hk, MonoidHom.map_zpowers]
      rfl
    let θ : LX ≃* LY := (MulEquiv.subgroupMap e LX).trans (MulEquiv.subgroupCongr hLXmap)
    have hθ : θ ⟨s, Subgroup.mem_sup_right (Subgroup.mem_zpowers s)⟩ =
        ⟨e s, Subgroup.mem_sup_right (Subgroup.mem_zpowers (e s))⟩ := by
      apply Subtype.ext
      rfl
    let ψ : (↥LX ⧸ Subgroup.center ↥LX) ≃* ↥(CFSG.PGLModel.orthogonalPlus 4 F) :=
      (QuotientGroup.congr (Subgroup.center LX) (Subgroup.center LY) θ
        (Subgroup.map_center_eq θ)).trans ψ₀
    refine ⟨ψ, ?_⟩
    have hgl : (ψ (QuotientGroup.mk ⟨s, Subgroup.mem_sup_right (Subgroup.mem_zpowers s)⟩) :
          GL (Fin 4 ⊕ Fin 4) F) =
        (ψ₀ (QuotientGroup.mk
          ⟨e s, Subgroup.mem_sup_right (Subgroup.mem_zpowers (e s))⟩) :
            GL (Fin 4 ⊕ Fin 4) F) := by
      have hval : ψ (QuotientGroup.mk
            ⟨s, Subgroup.mem_sup_right (Subgroup.mem_zpowers s)⟩) =
          ψ₀ (QuotientGroup.mk
            ⟨e s, Subgroup.mem_sup_right (Subgroup.mem_zpowers (e s))⟩) := by
        dsimp only [ψ]
        rw [MulEquiv.trans_apply, QuotientGroup.congr_mk, hθ]
      rw [hval]
    rw [hgl]
    exact hrank

theorem odd_card_center_of_pCore_eq_bot {X : Type} [Group X] [Finite X]
    (h : CFSG.pCore 2 X = ⊥) : Odd (Nat.card (Subgroup.center X)) := by
  by_contra hodd
  rw [Nat.not_odd_iff_even, even_iff_two_dvd] at hodd
  haveI : Finite ↥(Subgroup.center X) :=
    Finite.of_injective (Subtype.val : ↥(Subgroup.center X) → X) Subtype.coe_injective
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 hodd
  let y : X := (z : X)
  have hy : orderOf y = 2 := (Subgroup.orderOf_coe z).trans hz
  have hnormal : (Subgroup.zpowers y).Normal :=
    Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr z.2)
  have hpgroup : IsPGroup 2 (Subgroup.zpowers y) :=
    IsPGroup.of_card_dvd_pow (n := 1) (by rw [Nat.card_zpowers, hy]; norm_num)
  have hle : Subgroup.zpowers y ≤ CFSG.pCore 2 X := by
    rw [CFSG.pCore]
    exact le_sSup ⟨hnormal, hpgroup⟩
  rw [h] at hle
  have hy1 : y = 1 := by
    have : y ∈ (⊥ : Subgroup X) := hle (Subgroup.mem_zpowers y)
    simpa using this
  rw [hy1, orderOf_one] at hy
  exact absurd hy (by decide)

theorem isTrialityOddTransp_of_center_eq_bot {X : Type} [Group X] {s : X}
    (hZ : Subgroup.center X = ⊥)
    (h : IsTrialityOddTransp (X ⧸ Subgroup.center X) (QuotientGroup.mk s)) :
    IsTrialityOddTransp X s := by
  have hker : MonoidHom.ker (QuotientGroup.mk' (Subgroup.center X)) = ⊥ := by
    rw [QuotientGroup.ker_mk', hZ]
  let e : X ≃* X ⧸ Subgroup.center X :=
    MulEquiv.ofBijective (QuotientGroup.mk' (Subgroup.center X))
      ⟨(MonoidHom.ker_eq_bot_iff _).mp hker, QuotientGroup.mk'_surjective (Subgroup.center X)⟩
  exact isTrialityOddTransp_of_mulEquiv (s := s) e h

variable {G : Type} [Group G] [Finite G] {V H E : Subgroup G}


theorem not_isTrialityOddTransp_quotient (hMarked : TrialityMarkedInput)
    (hCentral : TrialityCentralInput) (h : Hyp711 V H E) {X : Type} [Group X]
    {φ : ↥(kSub V H E) →* X} (hφ : IsBarMap (kSub V H E) (pCoreOf 2 (kSub V H E)) φ)
    (hS : Nat.card (barSub (kSub V H E) φ V) = 2) {s : X}
    (hs : s ∈ barSub (kSub V H E) φ V) (hs1 : s ≠ 1) :
    ¬ IsTrialityOddTransp (X ⧸ Subgroup.center X) (QuotientGroup.mk s) := by
  intro hT
  haveI : Finite X := Finite.of_surjective φ hφ.surjective
  obtain ⟨hord, -, hncl, hpc⟩ := seven_eleven_small_hyps h hφ hS hs hs1
  have hZ : Subgroup.center X = ⊥ :=
    hCentral X s hord hncl (odd_card_center_of_pCore_eq_bot hpc) hT
  exact not_isTrialityOddTransp hMarked h hφ hS hs hs1
    (isTrialityOddTransp_of_center_eq_bot hZ hT)

end CFSG.LocalAnalysis.WeakClosure81.SevenElevenTri
