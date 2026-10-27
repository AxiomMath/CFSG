module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSpFrameDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBSpDefs
import CFSG.LocalAnalysis.StandardType.GGNbrLineCover

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
  {𝒦 : Finset (Subgroup G)}

theorem GGSecFiveRouteCfg.card_inf_centralizer_nbr_le (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (hBB : B = Bs) {y : G} {K : Subgroup G} (hNy : GGNbr p B x D J y K) :
    Nat.card ↥(Bs ⊓ Subgroup.centralizer (K : Set G)) ≤ p := by
  obtain ⟨hp, hE, -, -, -⟩ := hR.1.1.tableB_facts
  have hyBs : y ∈ Bs := hR.1.1.2.1.1 hNy.1.2.1
  have hcen : Bs ⊓ Subgroup.centralizer (K : Set G) = Subgroup.zpowers y := by
    rw [← hBB]
    exact inf_centralizer_eq_zpowers_of_sHat hNy.1
  rw [hcen, Nat.card_zpowers]
  exact Nat.le_of_dvd hp.pos (orderOf_dvd_of_pow_eq_one (hE.2 y hyBs))

theorem GGSecFiveRouteCfg.largeEvenPComponent_L (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (hpL : p ∣ Nat.card L) :
    LargeEvenPComponent p (Subgroup.centralizer ({x} : Set G)) L := by
  have hp : p.Prime := (hR.1.1.tableB_facts).1
  exact largeEvenPComponent_of_isComponentOf_of_dvd hp
    (hR.1.1.1.2.2.2.2.2.2.1 : LargeEvenSStar p B x L).2.2.2.1 hpL

omit [Finite G] in
theorem GGSecFiveBPermSpKFrame.prime_dvd_card {n r f : ℕ} (hp : p.Prime) {X : Subgroup G}
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))} {π : Fin (r + 2) ≃ Fin n}
    {κ : StatedSp (r + 1) (GaloisField 2 f) →* G}
    {χ : Multiplicative (ZMod p) →* (GaloisField 2 f)ˣ}
    (hF : GGSecFiveBPermSpKFrame Bs X eta π κ χ) : p ∣ Nat.card X := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hcardχ : Nat.card (Multiplicative (ZMod p)) = p := by
    rw [Nat.card_congr (Multiplicative.toAdd (α := ZMod p)), Nat.card_zmod]
  have hrange : Nat.card ↥χ.range = p :=
    (Nat.card_congr (MonoidHom.ofInjective hF.2.2.1).toEquiv).symm.trans hcardχ
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' (G := ↥χ.range) p (by rw [hrange])
  have horder : orderOf (w : (GaloisField 2 f)ˣ) = p := by
    rw [Subgroup.orderOf_coe, hw]
  have hu1 : (w : (GaloisField 2 f)ˣ) ≠ 1 := by
    intro h
    exact hp.ne_one (horder.symm.trans (orderOf_eq_one_iff.mpr h))
  have hup : (w : (GaloisField 2 f)ˣ) ^ p = 1 := by
    have h := pow_orderOf_eq_one (w : (GaloisField 2 f)ˣ)
    rwa [horder] at h
  let d : Fin (r + 1) → (GaloisField 2 f)ˣ := fun _ => w
  have hdpow : d ^ p = 1 := by
    funext i
    simpa [d] using hup
  have hdiagpow : TauCeti.GLSymplecticFin.diagonal d ^ p = 1 := by
    rw [← map_pow, hdpow, map_one]
  have hdiagne : TauCeti.GLSymplecticFin.diagonal d ≠ 1 := by
    intro h
    have hd : d = 1 := TauCeti.GLSymplecticFin.diagonal_injective (by simpa using h)
    have h0 : (w : (GaloisField 2 f)ˣ) = 1 := by simpa [d] using congrFun hd 0
    exact hu1 h0
  set t : StatedSp (r + 1) (GaloisField 2 f) :=
    CFSG.LieType.Universal.Symplectic.equivStatedSp (r + 1) (GaloisField 2 f)
      (TauCeti.GLSymplecticFin.diagonal d) with ht
  have htorder : orderOf t = p := by
    rw [ht, MulEquiv.orderOf_eq,
      orderOf_eq_prime hdiagpow hdiagne]
  have hcard : Nat.card X = Nat.card (StatedSp (r + 1) (GaloisField 2 f)) := by
    rw [← hF.2.1]
    exact (Nat.card_congr (MonoidHom.ofInjective hF.1).toEquiv).symm
  rw [hcard]
  exact htorder ▸ orderOf_dvd_natCard t

end CFSG.StandardType

end
