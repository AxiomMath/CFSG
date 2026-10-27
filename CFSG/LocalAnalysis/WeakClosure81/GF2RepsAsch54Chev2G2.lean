module

import CFSG.Quasithin.Background.GoldschmidtShultLink
import CFSG.Quasithin.H13.NQCatNGTG2
public import CFSG.Adapters.TauCetiExceptional.EvenBridgeG2
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.GroupTheory.QuasiDihedralFusion.Transport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.SmithB42G2Id
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Chev2Orbit

open CFSG.Quasithin CFSG.Open Subgroup

theorem false_of_swap_g2
    {Q : Type} [Group Q] [Finite Q] {L T P : Subgroup Q} (hLn : L.Normal) {n f : ℕ}
    (hm : CFSG.Models.LieModel ↥L .G2 n 2 f) (hT : IsSylowIn 2 T ⊤) {t : Q} (ht : t ∈ T)
    (hPL : P < L) (hmax : ∀ Y : Subgroup Q, P < Y → Y ≤ L → Y = L)
    (hN : L ⊓ normalizer ((T ⊓ L : Subgroup Q) : Set Q) ≤ P)
    (hne : P.map (MulAut.conj t).toMonoidHom ≠ P) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : L.Normal := hLn
  have hf : 2 ≤ f := by
    have h3 : 3 ≤ 2 ^ f := by
      have hadm := hm.1
      simp only [StatedLieAdmissible] at hadm
      exact hadm.2.2.2
    by_contra hfnot
    have hf1 : f ≤ 1 := by omega
    interval_cases f <;> norm_num at h3
  have hf0 : f ≠ 0 := by omega
  have hF : Nat.card (GaloisField 2 f) = 2 ^ f :=
    GaloisField.card 2 f hf0
  have hm' := hm.2
  rcases hm' with hclass | ⟨-, d, hd, ⟨eL⟩⟩
  · simp only [StatedClassicalModel] at hclass
    exact hclass.2
  obtain ⟨i, hv⟩ := d
  have hi : ∃ q, i = .G2 q := by
    cases i with
    | G2 q => exact ⟨q, rfl⟩
    | _ => simp only [CFSG.Models.NamesTag] at hd
  obtain ⟨q, rfl⟩ := hi
  simp only [CFSG.Models.NamesTag] at hd
  obtain ⟨hqp, hqe⟩ := hd
  have hKq : Nat.card (GaloisField 2 f) = q.card := by
    rw [hF, TauCeti.PrimePower.card_def, hqp, hqe]
  obtain ⟨b⟩ := CFSG.TauCetiBridge.Even.untwistedBridgeEven_G2 q hv hqp
    (GaloisField 2 f) hKq
  have : CharP (GaloisField 2 f) 2 :=
    CFSG.Quasithin.B42G2Id.charP_two_of_card hF
  obtain ⟨c⟩ := CFSG.Quasithin.B42G2Id.nonempty_quasithinG2_mulEquiv_adjointQuotient
    (K := GaloisField 2 f) hF hf
  have e : ↥L ≃* ↥(CFSG.Open.quasithinG2 (GaloisField 2 f)) :=
    (eL.trans b.symm).trans c.symm
  let ψ : Q ≃* Q := MulAut.conj t
  let χ : Q ≃* Q := MulAut.conj t⁻¹
  have hψχ : ∀ z : Q, ψ (χ z) = z := by
    intro z
    simp [ψ, χ, MulAut.conj_apply]
    group
  have hχψ : ∀ z : Q, χ (ψ z) = z := by
    intro z
    simp [ψ, χ, MulAut.conj_apply]
    group
  have hTmap : T.map ψ.toMonoidHom = T := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa [ψ, MulAut.conj_apply] using T.mul_mem (T.mul_mem ht hy) (T.inv_mem ht)
    · intro hx
      refine ⟨t⁻¹ * x * t, ?_, ?_⟩
      · exact T.mul_mem (T.mul_mem (T.inv_mem ht) hx) ht
      · simp [ψ, MulAut.conj_apply]
        group
  have hLmap : L.map ψ.toMonoidHom = L :=
    CFSG.QuasiDihedralFusion.map_conj_eq_of_normal (K := L) t
  have hSmap : (T ⊓ L).map ψ.toMonoidHom = T ⊓ L := by
    rw [Subgroup.map_inf_eq T L ψ.toMonoidHom ψ.injective, hTmap, hLmap]
  have hTmapχ : T.map χ.toMonoidHom = T := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa [χ, MulAut.conj_apply] using T.mul_mem (T.mul_mem (T.inv_mem ht) hy) ht
    · intro hx
      refine ⟨t * x * t⁻¹, ?_, ?_⟩
      · exact T.mul_mem (T.mul_mem ht hx) (T.inv_mem ht)
      · simp [χ]
        group
  have hLmapχ : L.map χ.toMonoidHom = L :=
    CFSG.QuasiDihedralFusion.map_conj_eq_of_normal (K := L) t⁻¹
  have hS : CFSG.QuasithinUnique.IsSylowTwoOf (T ⊓ L) L :=
    CFSG.Quasithin.Shult.isSylowTwoOf_inf_normal hT
  have hM0 : (T ⊓ L) ≤ P ∧ P < L ∧
      ∀ M' : Subgroup Q, P ≤ M' → M' < L → M' = P := by
    refine ⟨?_, hPL, ?_⟩
    · exact (le_inf inf_le_right Subgroup.le_normalizer).trans hN
    · intro M' hle hlt
      by_contra hne'
      exact hlt.ne (hmax M' (lt_of_le_of_ne hle (Ne.symm hne')) hlt.le)
  have hM1 : (T ⊓ L) ≤ P.map ψ.toMonoidHom ∧ P.map ψ.toMonoidHom < L ∧
      ∀ M' : Subgroup Q, P.map ψ.toMonoidHom ≤ M' → M' < L →
        M' = P.map ψ.toMonoidHom := by
    refine ⟨?_, ?_, ?_⟩
    · have hmap := Subgroup.map_mono (f := ψ.toMonoidHom) hM0.1
      rwa [hSmap] at hmap
    · have hlt : P.map ψ.toMonoidHom < L.map ψ.toMonoidHom :=
        (Subgroup.map_lt_map_iff_of_injective (f := ψ.toMonoidHom) ψ.injective).2 hPL
      rwa [hLmap] at hlt
    · intro M' hle hlt
      have hYle : M'.map χ.toMonoidHom ≤ L := by
        calc M'.map χ.toMonoidHom ≤ L.map χ.toMonoidHom := Subgroup.map_mono hlt.le
          _ = L := hLmapχ
      have hPY : P ≤ M'.map χ.toMonoidHom := by
        have hmap := Subgroup.map_mono (f := χ.toMonoidHom) hle
        have hPP : (P.map ψ.toMonoidHom).map χ.toMonoidHom = P := by
          rw [Subgroup.map_map]
          have hcomp : χ.toMonoidHom.comp ψ.toMonoidHom = MonoidHom.id Q := by
            ext x
            exact hχψ x
          rw [hcomp, Subgroup.map_id]
        rwa [hPP] at hmap
      have hYlt : M'.map χ.toMonoidHom < L := by
        have hlt' : M'.map χ.toMonoidHom < L.map χ.toMonoidHom :=
          (Subgroup.map_lt_map_iff_of_injective (f := χ.toMonoidHom) χ.injective).2 hlt
        rwa [hLmapχ] at hlt'
      have hYP : M'.map χ.toMonoidHom = P := by
        by_contra hne'
        exact hYlt.ne (hmax _ (lt_of_le_of_ne hPY (Ne.symm hne')) hYle)
      have hback : (M'.map χ.toMonoidHom).map ψ.toMonoidHom = M' := by
        rw [Subgroup.map_map]
        have hcomp : ψ.toMonoidHom.comp χ.toMonoidHom = MonoidHom.id Q := by
          ext x
          exact hψχ x
        rw [hcomp, Subgroup.map_id]
      calc M' = (M'.map χ.toMonoidHom).map ψ.toMonoidHom := hback.symm
        _ = P.map ψ.toMonoidHom := by rw [hYP]
  exact CFSG.Quasithin.H13.NQCat.NGT.no_swap_g2
    (F := GaloisField 2 f) (n := f) hf hF e hS hM0 hM1 (Ne.symm hne) ψ rfl

end CFSG.LocalAnalysis.WeakClosure81.Chev2Orbit
