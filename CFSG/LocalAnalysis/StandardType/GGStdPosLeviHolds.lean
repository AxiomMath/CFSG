module

public import CFSG.LocalAnalysis.StandardType.GGStdPosLeviDefs
public import CFSG.LocalAnalysis.StandardType.GGStdPosLeviCent
public import CFSG.LocalAnalysis.StandardType.GGStdPosLeviSub
public import CFSG.LocalAnalysis.StandardType.GGStdPosTagData
public import CFSG.LocalAnalysis.StandardType.GGStdPosRootKerHolds

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg CFSG.LieType.CurtisTits

private theorem ggStdPosLevi_mem_hyperplane {G : Type} [Group G] {Bs : Subgroup G}
    {a : MulAut ↥Bs} {g : G} (ha : ∀ b : ↥Bs, ((a b : ↥Bs) : G) = g * b * g⁻¹) (b : G) :
    b ∈ (ggHyperplane Bs a : Set G) ↔ b ∈ Bs ∧ b * g = g * b := by
  constructor
  · rintro ⟨b', hb', rfl⟩
    have h1 : ((a b' : ↥Bs) : G) = b' := congrArg Subtype.val hb'
    rw [ha] at h1
    exact ⟨b'.2, (mul_inv_eq_iff_eq_mul.mp h1).symm⟩
  · rintro ⟨hb, hbg⟩
    refine ⟨⟨b, hb⟩, Subtype.ext ?_, rfl⟩
    show ((a ⟨b, hb⟩ : ↥Bs) : G) = b
    rw [ha, ← hbg, mul_inv_cancel_right]

theorem ggKGPosLeviStmt_holds :
    GGKGPosLeviStmt := by
  intro G _ _ p Bs X t n f ψ hloc hstd ν ε hν hind w i
  obtain ⟨⟨hp, hp2, hadm, hrank⟩, ⟨hker, hrange, ht, hpdvd⟩, ⟨-, -, hC3⟩, -, -⟩ := hloc
  subst hrange
  obtain ⟨hdiv, ⟨nn, H, hct, hext, hBU⟩, x, C, O, hE⟩ := ggStdPos_bruhatData hrank ht
  obtain ⟨hR1, hR2⟩ := ggRootKerStmt_holds t n f hadm hrank ht p hp hp2 hpdvd ν hν w i
  haveI : Fact p.Prime := ⟨hp⟩
  have hcard : Nat.card (GaloisField 2 f)ˣ = 2 ^ f - 1 := by
    rw [Nat.card_units, GaloisField.card 2 f (by have := hadm.2.1; omega)]
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := (GaloisField 2 f)ˣ) p (hcard ▸ hpdvd)
  have hζ1 : ζ ≠ 1 := fun h => hp.one_lt.ne (by rw [← hζ, h, orderOf_one])
  have hS := ggStdPosLevi_mem_hyperplane
    (hind (w * (coxeterMatrix (ggU t n f).D.isFiniteType).simple i * w⁻¹))
  have hγ : weylAction (ggU t n f).D.isFiniteType w (Pi.single i 1) ∈ (ggU t n f).D.roots :=
    weylAction_mem_roots (single_mem_roots i) w
  have hsq : ∀ β ∈ (ggU t n f).D.roots, ∀ z ∈ (ggU t n f).D.rootGroup β, ψ z ^ 2 ^ 1 = 1 := by
    intro β hβ z hz
    obtain ⟨c, rfl⟩ := ((hE.param β hβ).1 z).mp hz
    rw [pow_one, ← map_pow, sq, ← (hE.param β hβ).2.1, CharTwo.add_self_eq_zero, hE.x_zero hβ,
      map_one]
  rw [ggRankOneIn, ggOTwoPrime, ggRootLevi]
  refine le_antisymm ((Subgroup.closure_le _).mpr fun y hy => ?_) ?_
  · obtain ⟨⟨hyX, hyC⟩, e, he⟩ := hy
    exact ggStdPosLevi_mem_map hct hext hBU hE hdiv hζ1 ψ hker hstd hC3 hν w i hR1 hR2 hS hyX hyC he
  · rw [Subgroup.map_le_iff_le_comap]
    refine sup_le (fun z hz => Subgroup.mem_comap.mpr (Subgroup.subset_closure ?_))
      (fun z hz => Subgroup.mem_comap.mpr (Subgroup.subset_closure ?_))
    · exact ⟨⟨⟨z, rfl⟩, Subgroup.mem_centralizer_iff.mpr fun b hb =>
        ggStdPosLevi_commute hct hext hBU hE ψ hker hstd hν w i ((hS b).mp hb).1
          ((hS b).mp hb).2 z (Subgroup.mem_sup_left hz)⟩, 1, hsq _ hγ z hz⟩
    · exact ⟨⟨⟨z, rfl⟩, Subgroup.mem_centralizer_iff.mpr fun b hb =>
        ggStdPosLevi_commute hct hext hBU hE ψ hker hstd hν w i ((hS b).mp hb).1
          ((hS b).mp hb).2 z (Subgroup.mem_sup_right hz)⟩, 1,
        hsq _ (OfCartan.neg_mem_roots _ hγ) z hz⟩

end CFSG.StandardType

end
