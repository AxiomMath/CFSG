module

public import CFSG.LocalAnalysis.StandardType.GGSixA6RedDefs
public import CFSG.LocalAnalysis.StandardType.GGSixA6RedClDefs
public import CFSG.LocalAnalysis.StandardType.GGSixA6RedF4ClassDefs
public import CFSG.LocalAnalysis.StandardType.GGExclNoIso
public import CFSG.LocalAnalysis.StandardType.Marking
public import CFSG.LocalAnalysis.StandardType.GGSixA6RedNotShape
public import CFSG.LocalAnalysis.StandardType.GGSixA6RedCenter
public import CFSG.LocalAnalysis.StandardType.GGSixA6RedF4Proof
public import CFSG.LocalAnalysis.StandardType.GGSixA6RedPSpCore
public import CFSG.LocalAnalysis.StandardType.GGSixA6RedShapeSL
public import CFSG.LocalAnalysis.StandardType.GGSixA6RedShapeSU
public import CFSG.LocalAnalysis.StandardType.GGSixA6RedShapeOmega
public import CFSG.LocalAnalysis.StandardType.GGSixA6RedTransportPSL
public import CFSG.LocalAnalysis.StandardType.GGSixA6RedTransportPSU
public import CFSG.LocalAnalysis.StandardType.GGSixA6RedTransportOmega

public section

namespace CFSG.StandardType.A6Red

open CFSG.Assembly CFSG.Blueprint CFSG.Assembly.LowTwoRank

section Genuine

theorem ggA6_isElemAbelian_of_le {G : Type} [Group G] {p : ℕ} {A B : Subgroup G}
    (hA : IsElemAbelian p A) (h : B ≤ A) : IsElemAbelian p B :=
  ⟨⟨⟨fun a b => Subtype.ext (by
      have := hA.1.is_comm.comm (⟨a.1, h a.2⟩ : ↥A) ⟨b.1, h b.2⟩
      exact congrArg (Subtype.val : ↥A → G) this)⟩⟩, fun x hx => hA.2 x (h hx)⟩

theorem ggSixA6KnownRedAt_of_noJ
    (t : StatedLieTag) (h : GGA6NoJAt t) : GGSixA6KnownRedAt t := by
  intro X _ _ n f ψ p G₀ B₁ D J L x hr hk hLie hp hp2 _ hBN hdiag hab _ hDB hDc hJ _ _ _ _ _ _ _ hA6
  exact absurd hA6 (h X n f ψ p G₀ D J hr hk hLie hp hp2 (hDB.trans hBN)
    (fun d hd => hdiag d (hDB hd)) (ggA6_isElemAbelian_of_le hab hDB) hDc hJ)

theorem ggA6NoJ_classical
    (t : StatedLieTag)
    (ht : t = .PSL ∨ t = .PSU ∨ t = .POmegaPlus ∨ t = .POmegaMinus) : GGA6NoJAt t := by
  rcases ht with rfl | rfl | rfl | rfl
  · intro X _ _ n f ψ p G₀ D J hr hk hLie hp hp2 hDN hdiag hab hD hJ hA6
    have hadm := LieModel.admissible hLie
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := hadm.2.2.1; omega⟩
    obtain ⟨P, J', hP, hJ', hJJ⟩ := ggA6_transport_PSL m f X ψ p G₀ D J hr hk hLie hp hp2 hDN hdiag
      hab hD hJ
    exact ggA6_not_shape_of_a6 J J' hA6 hJJ (ggA6_shape_SL (m + 1) P hP J' hJ')
  · intro X _ _ n f ψ p G₀ D J hr hk hLie hp hp2 hDN hdiag hab hD hJ hA6
    have hadm := LieModel.admissible hLie
    obtain ⟨P, J', hPU, hP, hJ', hJJ⟩ := ggA6_transport_PSU n f X ψ p G₀ D J hr hk hLie hp hp2 hDN
      hdiag hab hD hJ
    exact ggA6_not_shape_of_a6 J J' hA6 hJJ
      (ggA6_shape_SU f (by rw [GaloisField.card 2 (2 * f) (by have := hadm.2.1; omega), pow_mul'])
        n P hPU hP J' hJ')
  · intro X _ _ n f ψ p G₀ D J hr hk hLie hp hp2 hDN hdiag hab hD hJ hA6
    obtain ⟨F, _, _, _, ι, _, _, Φ, P, J', hPO, hP, hPn, hJ', hJJ⟩ :=
      ggA6_transport_Omega .POmegaPlus (Or.inl rfl) n f X ψ p G₀ D J hr hk hLie hp hp2 hDN hdiag hab
        hD hJ
    exact ggA6_not_shape_of_a6 J J' hA6 hJJ (ggA6_shape_Omega Φ P hPO hP hPn J' hJ')
  · intro X _ _ n f ψ p G₀ D J hr hk hLie hp hp2 hDN hdiag hab hD hJ hA6
    obtain ⟨F, _, _, _, ι, _, _, Φ, P, J', hPO, hP, hPn, hJ', hJJ⟩ :=
      ggA6_transport_Omega .POmegaMinus (Or.inr rfl) n f X ψ p G₀ D J hr hk hLie hp hp2 hDN hdiag
        hab hD hJ
    exact ggA6_not_shape_of_a6 J J' hA6 hJJ (ggA6_shape_Omega Φ P hPO hP hPn J' hJ')

theorem ggSixA6KnownRedAt_PSp
    : GGSixA6KnownRedAt .PSp := by
  intro X _ _ n f ψ p G₀ B₁ D J L x hr hk hLie hp hp2 hcop hBN hdiag hab _ hDB hDc hJ hx hx1 hLG
    hL hJL hDL hmk hA6
  obtain ⟨hp3, hf, hn, m, hm, hLm⟩ := ggA6_PSp_core X n f ψ p G₀ B₁ D J L x hr hk hLie hp hp2 hcop
    hBN hdiag hab hDB hDc hJ hx hx1 hLG hL hJL hDL hmk hA6
  obtain ⟨hZ, hB⟩ := ggA6_center_le .PSp (Or.inl rfl) X n f ψ p G₀ B₁ hr hk hLie hp hp2 hcop hBN
    hdiag hab
  exact ⟨hp3, hf, Or.inl ⟨rfl, hn⟩, hZ, hB, m, hm, hLm⟩

end Genuine

end CFSG.StandardType.A6Red
