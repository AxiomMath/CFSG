module

public import CFSG.Blueprint.NativeSporadic
public import CFSG.Sporadic.Schreier.MathieuOddCoreCentral
public import CFSG.Sporadic.Schreier.MathieuOddCoreClasses
public import CFSG.Sporadic.Schreier.MathieuOddCoreTransport
public import CFSG.Sporadic.Schreier.PairHSFaithful
public import CFSG.Sporadic.Schreier.PairMcLFaithful
public import CFSG.Sporadic.SmallOddCore.HS
public import CFSG.Sporadic.SmallOddCore.HSAut
public import CFSG.Sporadic.SmallOddCore.McL
public import CFSG.Sporadic.SmallOddCore.McLAut
public import Certificates.Certificate2218
public import Certificates.Certificate2219
public import Certificates.Certificate2221
public import Certificates.Certificate2240
public import Certificates.Certificate2241
public import Certificates.Certificate2242
public import Certificates.Certificate2243
public import Certificates.Certificate2244
public import Certificates.Certificate2245
public import Certificates.Certificate2272
public import Certificates.Certificate2274
public import Certificates.Certificate2284
public import Certificates.Certificate2285
public import Certificates.Certificate2288
public import Certificates.Certificate3167
public import Certificates.Certificate3170
public import CFSG.Sporadic.Schreier.MathieuOddCoreModel

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Sporadic.Schreier

variable {M : Type*} [Group M]

theorem fixSubCard_eq_centralizerIn (P : Subgroup M) (α : MulAut P) (x : M)
    (hα : ∀ p : P, ((α p : P) : M) = x * p * x⁻¹) :
    Nat.card (fixSub α) = Nat.card (centralizerIn P x) := by
  rw [← map_fixSub_conjOn P α x hα, Subgroup.card_map_of_injective P.subtype_injective]

theorem fixSubCard_centralizerIn_conj (P : Subgroup M) {g : M} (hg : g ∈ P) (t : M) :
    Nat.card (centralizerIn P (g * t * g⁻¹)) = Nat.card (centralizerIn P t) := by
  rw [centralizerIn_conj P hg t, Subgroup.card_map_of_injective (MulAut.conj g).injective]

theorem fixSubCard_congr_equiv {G H : Type*} [Group G] [Group H] (φ : G ≃* H) (β : MulAut G) :
    Nat.card (fixSub (MulAut.congr φ β)) = Nat.card (fixSub β) := by
  rw [← map_fixSub_equiv φ β, Subgroup.card_map_of_injective (f := φ.toMonoidHom) φ.injective]

theorem fixSubCard_not_dvd_of_model {P R : Subgroup M}
    (e : R ≃* MulAut P)
    (he : ∀ (x : R) (p : P), ((e x p : P) : M) = (x : M) * p * (x : M)⁻¹)
    (hinv : ∀ t ∈ R, orderOf t = 2 → ¬ 443520 ∣ Nat.card (centralizerIn P t))
    (β : MulAut P) (h2 : β ^ 2 = 1) (h1 : β ≠ 1) :
    ¬ 443520 ∣ Nat.card (fixSub β) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨y, rfl⟩ := e.surjective β
  have hy2 : y ^ 2 = 1 := e.injective (by rw [map_pow, h2, map_one])
  have hy1 : y ≠ 1 := fun h => h1 (by rw [h, map_one])
  have hord : orderOf (y : M) = 2 := by
    rw [Subgroup.orderOf_coe]
    exact orderOf_eq_prime hy2 hy1
  rw [fixSubCard_eq_centralizerIn P (e y) (y : M) (he y)]
  exact hinv _ y.2 hord

theorem fixSubCard_not_dvd_of_equiv {P R : Subgroup M} {G : Type*} [Group G] (φ : G ≃* P)
    (e : R ≃* MulAut P)
    (he : ∀ (x : R) (p : P), ((e x p : P) : M) = (x : M) * p * (x : M)⁻¹)
    (hinv : ∀ t ∈ R, orderOf t = 2 → ¬ 443520 ∣ Nat.card (centralizerIn P t))
    (β : MulAut G) (h2 : β ^ 2 = 1) (h1 : β ≠ 1) :
    ¬ 443520 ∣ Nat.card (fixSub β) := by
  have h2' : MulAut.congr φ β ^ 2 = 1 := by
    rw [← map_pow, h2, map_one]
  have h1' : MulAut.congr φ β ≠ 1 := fun h =>
    h1 ((MulAut.congr φ).injective (by rw [h, map_one]))
  rw [← fixSubCard_congr_equiv φ β]
  exact fixSubCard_not_dvd_of_model e he hinv (MulAut.congr φ β) h2' h1'

theorem hs_fixSub_card_not_dvd (L : Type) [Group L]
    (e : L ≃* CFSG.Blueprint.NativeSporadic.Carrier .HS) (β : MulAut L)
    (h2 : β ^ 2 = 1) (h1 : β ≠ 1) :
    ¬ 443520 ∣ Nat.card (CFSG.Sporadic.Schreier.fixSub β) := by
  obtain ⟨e', he', -⟩ := CFSG.Sporadic.SmallOddCore.hs_full_automorphism_model
  obtain ⟨-, -, -, hrows, hconj, -, hlist, -⟩ :=
    CFSG.Sporadic.SmallOddCore.hs_involution_centralizers
  refine fixSubCard_not_dvd_of_equiv (e.trans CFSG.Sporadic.Schreier.hsPermEquiv) e' he' ?_ β h2 h1
  intro t ht ho
  obtain ⟨r, hr, g, hg, rfl⟩ := hconj t ht ho
  rw [fixSubCard_centralizerIn_conj _ hg]
  have hc := (hrows r hr).2.2.2.2.1
  have hmem : (r.outer, r.classSize, r.centOrder) ∈
      CFSG.Sporadic.SmallOddCore.hsRows.map (fun r => (r.outer, r.classSize, r.centOrder)) :=
    List.mem_map_of_mem hr
  rw [hlist] at hmem
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false, Prod.mk.injEq] at hmem
  unfold CFSG.Sporadic.Schreier.centralizerIn
  rw [hc]
  rcases hmem with ⟨-, -, h⟩ | ⟨-, -, h⟩ | ⟨-, -, h⟩ | ⟨-, -, h⟩ <;> omega

theorem mcl_fixSub_card_not_dvd (L : Type) [Group L]
    (e : L ≃* CFSG.Blueprint.NativeSporadic.Carrier .McL) (β : MulAut L)
    (h2 : β ^ 2 = 1) (h1 : β ≠ 1) :
    ¬ 443520 ∣ Nat.card (CFSG.Sporadic.Schreier.fixSub β) := by
  obtain ⟨e', he', -⟩ := CFSG.Sporadic.SmallOddCore.mcl_full_automorphism_model
  obtain ⟨-, -, -, hrows, hconj, -, hlist, -⟩ :=
    CFSG.Sporadic.SmallOddCore.mcl_involution_centralizers
  refine fixSubCard_not_dvd_of_equiv (e.trans CFSG.Sporadic.Schreier.mclPermEquiv) e' he' ?_ β h2 h1
  intro t ht ho
  obtain ⟨r, hr, g, hg, rfl⟩ := hconj t ht ho
  rw [fixSubCard_centralizerIn_conj _ hg]
  have hc := (hrows r hr).2.2.2.2.1
  have hmem : (r.outer, r.classSize, r.centOrder) ∈
      CFSG.Sporadic.SmallOddCore.mclRows.map (fun r => (r.outer, r.classSize, r.centOrder)) :=
    List.mem_map_of_mem hr
  rw [hlist] at hmem
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false, Prod.mk.injEq] at hmem
  unfold CFSG.Sporadic.Schreier.centralizerIn
  rw [hc]
  rcases hmem with ⟨-, -, h⟩ | ⟨-, -, h⟩ <;> omega

end CFSG.Quasithin.H13.Ch4

end
