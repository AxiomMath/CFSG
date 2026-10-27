module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeConfigID
public import Certificates.Certificate14972
import CFSG.LocalAnalysis.StandardType.GGPsiDiagInnerAdj
import CFSG.LocalAnalysis.StandardType.E8SevenCentralizerComponent
import CFSG.LieType.Chevalley.AdjointCenter
import Mathlib.Tactic.Group

public section
namespace CFSG.StandardType.RCKC1
open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.StandardType



theorem exists_e8_native_centralizer_of_innerDiag
    {X : Type} [Group X] [Finite X] {n p : ℕ}
    {ψ : (ggU .E8 n 1).K →* X} {G₀ A : Subgroup X} {e : X}
    (hpres : GGPresentsG0 G₀ (ggU .E8 n 1).D .E8 n 1 ψ)
    (hp : p.Prime) (heA : e ∈ A) (he1 : e ≠ 1) (hep : e ^ p = 1)
    (heN : e ∈ Subgroup.normalizer (G₀ : Set X))
    (heID : GGPsiInnerDiag (ggU .E8 n 1).D ψ e)
    (hfaith : A ⊓ Subgroup.centralizer (G₀ : Set X) = ⊥) :
    Function.Injective ψ ∧ ∃ u : (ggU .E8 n 1).K,
      orderOf u = p ∧
      (Subgroup.centralizer {u}).map ψ = G₀ ⊓ Subgroup.centralizer {e} := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZ : Subgroup.center (ggU .E8 n 1).K = ⊥ := by
    change Subgroup.center (CFSG.Blueprint.Chevalley.adjointGroup .E8 (GaloisField 2 1)) = ⊥
    exact CFSG.LieType.Chevalley.center_adjointGroup_eq_bot
  have hψ : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff, ← hZ]
    exact hpres.2.1.2
  have hrange : ψ.range = G₀ := hpres.2.1.1
  obtain ⟨g, hg, hcent⟩ := ggPsiDiagInner_E8 X n 1 ψ G₀ hpres e heN heID
  have hgRange : g ∈ ψ.range := hrange.symm ▸ hg
  obtain ⟨u, hu⟩ := hgRange
  have hge : g * e = e * g := mul_right_cancel (show (g * e) * g = (e * g) * g by
    simpa only [mul_assoc] using Subgroup.mem_centralizer_iff.mp hcent g hg)
  have heg : Commute e g := hge.symm
  have hgpc : g ^ p ∈ Subgroup.centralizer (G₀ : Set X) := by
    have hc := (Subgroup.centralizer (G₀ : Set X)).pow_mem hcent p
    rw [heg.mul_pow, hep, one_mul] at hc
    exact hc
  have huc : u ^ p ∈ Subgroup.center (ggU .E8 n 1).K := by
    rw [Subgroup.mem_center_iff]
    intro v
    apply hψ
    simpa only [map_mul, map_pow, hu] using
      Subgroup.mem_centralizer_iff.mp hgpc (ψ v) (hrange ▸ (show ψ v ∈ ψ.range from ⟨v, rfl⟩))
  have hup : u ^ p = 1 := by
    rw [hZ] at huc
    simpa only [Subgroup.mem_bot] using huc
  have hu1 : u ≠ 1 := by
    intro h
    have hg1 : g = 1 := by simpa [h] using hu.symm
    have heC : e ∈ Subgroup.centralizer (G₀ : Set X) := by simpa [hg1] using hcent
    have heBot : e ∈ (⊥ : Subgroup X) := hfaith ▸ (show e ∈ A ⊓ Subgroup.centralizer (G₀ : Set X) from ⟨heA, heC⟩)
    exact he1 (by simpa only [Subgroup.mem_bot] using heBot)
  have huo : orderOf u = p := by
    rcases (Nat.dvd_prime hp).mp (orderOf_dvd_of_pow_eq_one hup) with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hu1
    · exact h
  refine ⟨hψ, u, huo, ?_⟩
  ext x
  simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_iff,
    Set.mem_singleton_iff, forall_eq]
  constructor
  · rintro ⟨v, hv, rfl⟩
    have hxG : ψ v ∈ G₀ := hrange ▸ (show ψ v ∈ ψ.range from ⟨v, rfl⟩)
    refine ⟨hxG, ?_⟩
    have hgv : g * ψ v = ψ v * g := by simpa only [map_mul, hu] using congrArg ψ hv
    have hc := Subgroup.mem_centralizer_iff.mp hcent (ψ v) hxG
    have hxe : ψ v * e = e * ψ v := mul_right_cancel (show (ψ v * e) * g = (e * ψ v) * g by
      calc (ψ v * e) * g = ψ v * (e * g) := by group
        _ = (e * g) * ψ v := hc
        _ = e * (g * ψ v) := by group
        _ = e * (ψ v * g) := by rw [hgv]
        _ = (e * ψ v) * g := by group)
    exact hxe.symm
  · rintro ⟨hxG, hxe⟩
    have hxRange : x ∈ ψ.range := hrange.symm ▸ hxG
    obtain ⟨v, rfl⟩ := hxRange
    refine ⟨v, ?_, rfl⟩
    apply hψ
    simp only [map_mul, hu]
    have hxG : ψ v ∈ G₀ := hrange ▸ (show ψ v ∈ ψ.range from ⟨v, rfl⟩)
    have hc := Subgroup.mem_centralizer_iff.mp hcent (ψ v) hxG
    apply mul_left_cancel (show e * (g * ψ v) = e * (ψ v * g) from ?_)
    calc e * (g * ψ v) = (e * g) * ψ v := by group
      _ = ψ v * (e * g) := hc.symm
      _ = (ψ v * e) * g := by group
      _ = (e * ψ v) * g := by rw [← hxe]
      _ = e * (ψ v * g) := by group

theorem e8_compConfig_native_centralizer
    {X : Type} [Group X] [Finite X] {n p : ℕ}
    {ψ : (ggU .E8 n 1).K →* X} {G₀ A B₁ D J L K : Subgroup X} {e : X}
    (h : RCKRP.RCKCompConfig .E8 n 1 ψ p G₀ A B₁ D J L K e) :
    Function.Injective ψ ∧ ∃ u : (ggU .E8 n 1).K,
      orderOf u = p ∧
      (Subgroup.centralizer {u}).map ψ = G₀ ⊓ Subgroup.centralizer {e} ∧
      IsComponentOf (K.comap ψ) (Subgroup.centralizer {u}) ∧ (K.comap ψ).map ψ = K := by
  have hdiag := RCKRP.rckRPConfigInnerDiag_holds X .E8 n 1 ψ p G₀ A B₁ D J L K e h
  obtain ⟨hpres, -, hp, -, hA, hBA, hDB, -, hAN, -, -, -, -, -, -, hfaith,
    -, -, -, -, -, -, -, -, -, heD, he1, hKcomp, -, -⟩ := h
  have heA := hBA (hDB heD)
  obtain ⟨hψ, u, hup, hC⟩ := exists_e8_native_centralizer_of_innerDiag hpres hp heA he1
    (hA.2 e heA) (hAN heA) (hdiag e heA) hfaith
  have hKrange : K ≤ ψ.range := hpres.2.1.1.symm ▸ (hKcomp.1.trans inf_le_left : K ≤ G₀)
  have hKmap : (K.comap ψ).map ψ = K := Subgroup.map_comap_eq_self hKrange
  refine ⟨hψ, u, hup, hC, ?_, hKmap⟩
  rw [← CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_iff hψ, hKmap, hC]
  exact hKcomp


theorem e8_seven_compConfig_has_component_label
    {X : Type} [Group X] [Finite X] {n : ℕ}
    {ψ : (ggU .E8 n 1).K →* X} {G₀ A B₁ D J L K : Subgroup X} {e : X}
    (hcfg : RCKRP.RCKCompConfig .E8 n 1 ψ 7 G₀ A B₁ D J L K e) :
    ∃ labK : LargeEvenLabel,
      labK ∈ [⟨.E6, 0, 1⟩, ⟨.triD4, 0, 1⟩, ⟨.A, 2, 1⟩] ∧
      GGHasLabel labK (↥K ⧸ Subgroup.center ↥K) := by
  obtain ⟨hinj, u, hu, _, hKcomp, hKmap⟩ := e8_compConfig_native_centralizer hcfg
  obtain ⟨labK, hlist, hlabel⟩ := e8TwoSeven_component_has_label u hu (K.comap ψ) hKcomp
  let eK : (K.comap ψ) ≃* K :=
    (Subgroup.equivMapOfInjective (K.comap ψ) ψ hinj).trans (MulEquiv.subgroupCongr hKmap)
  let eQ := QuotientGroup.congr _ _ eK (Subgroup.map_center_eq eK)
  exact ⟨labK, hlist, largeEvenRawDatum_mono (fun _ _ _ _ ⟨f⟩ => ⟨eQ.symm.trans f⟩) hlabel⟩

end CFSG.StandardType.RCKC1
