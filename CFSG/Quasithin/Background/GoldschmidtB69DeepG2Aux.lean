module

public import CFSG.Quasithin.Background.B69E22Main
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42TypeListAux
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Quasithin.Background.P3G2Iso
public import CFSG.Quasithin.EmptyFaithful.Insp9Tr

public section

namespace CFSG.Quasithin

open CFSG.Open
open scoped commutatorElement

namespace B69

theorem le_ffJ_of_fitting {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    {G L A : Subgroup (MulAut V)} (hL : L = quasithinGenFitting G) (hq : CFSG.IsQuasisimple ↥L)
    (hirr : XMod.IsIrrSec ↥L (⊥ : Subgroup V) ⊤) (hA : IsFFStarOffender G A) : L ≤ ffJ G := by
  have hLG : L ≤ G := by rw [hL]; exact CFSG.Quasithin.quasithinGenFitting_le G
  have hAN : A ≤ Subgroup.normalizer (L : Set (MulAut V)) := by
    intro a ha
    have := CFSG.Quasithin.le_normalizer_quasithinGenFitting G (hA.1 ha)
    rw [← hL] at this
    exact this
  have hne : ⁅L, A⁆ ≠ ⊥ := by
    intro hbot
    have hcomm : ∀ a ∈ A, ∀ l ∈ L, a * l = l * a := by
      intro a ha l hl
      have hmem : ⁅l, a⁆ ∈ ⁅L, A⁆ := Subgroup.commutator_mem_commutator hl ha
      rw [hbot, Subgroup.mem_bot] at hmem
      exact (commutatorElement_eq_one_iff_mul_comm.1 hmem).symm
    obtain ⟨a, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hA.2.1
    have haA : (a : MulAut V) ∈ A := a.2
    have ha2 : (a : MulAut V) ^ 2 = 1 := hA.2.2.1.2 _ haA
    exact ha1 (Subtype.ext (CFSG.QuasithinUnique.Bridge.TypeList.eq_one_of_commute_of_irr hV
      (CFSG.QuasithinUnique.Bridge.TypeList.irr_of_isIrrSec hirr) ha2 (hcomm _ haA)))
  exact B1Red.K_le_ffJ hLG hA (CFSG.QuasithinUnique.Setup.Layer.comm_eq_of_quasisimple hq hAN hne)

theorem exists_odd_card_mul {L Q F : Type} [Group L] [Finite L] [Group Q] [Group F]
    [IsSimpleGroup F] (hL : CFSG.Open.IsQuasisimple L)
    (hz : ∀ z ∈ Subgroup.center L, Odd (orderOf z)) (ℓ : L →* Q) (hℓ : Function.Surjective ℓ)
    (hcent : ℓ.ker ≤ Subgroup.center L) (π : L →* F) (hπ : Function.Surjective π) :
    ∃ c : ℕ, Odd c ∧ Nat.card Q = Nat.card F * c := by
  have hLperf : Group.IsPerfect L := Group.isPerfect_def.mpr hL.1
  have hFperf : Group.IsPerfect F := Group.IsPerfect.ofSurjective hπ
  have hker : π.ker = Subgroup.center L := by
    have hne : π.ker ≠ ⊤ := by
      intro htop
      obtain ⟨a, b, hab⟩ := (inferInstance : Nontrivial F).exists_pair_ne
      obtain ⟨x, rfl⟩ := hπ a
      obtain ⟨y, rfl⟩ := hπ b
      apply hab
      have hx : x ∈ π.ker := by rw [htop]; trivial
      have hy : y ∈ π.ker := by rw [htop]; trivial
      rw [MonoidHom.mem_ker.mp hx, MonoidHom.mem_ker.mp hy]
    apply le_antisymm
    · exact CFSG.ComponentClassification.Quasisimple.normal_le_center_of_ne_top hL π.ker hne
    · intro z hz'
      rw [MonoidHom.mem_ker]
      have : π z ∈ Subgroup.center F := by
        rw [Subgroup.mem_center_iff]
        intro q
        obtain ⟨x, rfl⟩ := hπ q
        rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp hz' x).symm]
      rw [center_eq_bot_of_perfect_simple] at this
      exact Subgroup.mem_bot.mp this
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup π.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective π hπ).toEquiv, hker] at h1
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup ℓ.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective ℓ hℓ).toEquiv] at h2
  obtain ⟨c, hc⟩ := Subgroup.card_dvd_of_le hcent
  have hpos : 0 < Nat.card ↥ℓ.ker := Nat.card_pos
  have hQ : Nat.card Q = Nat.card F * c := by
    refine Nat.eq_of_mul_eq_mul_right hpos ?_
    calc Nat.card Q * Nat.card ↥ℓ.ker = Nat.card L := h2.symm
      _ = Nat.card F * Nat.card ↥(Subgroup.center L) := h1
      _ = Nat.card F * c * Nat.card ↥ℓ.ker := by rw [hc]; ring
  refine ⟨c, ?_, hQ⟩
  have hodd : Odd (Nat.card ↥(Subgroup.center L)) := by
    by_contra hev
    rw [Nat.not_odd_iff_even, even_iff_two_dvd] at hev
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨z, hz2⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.center L)) 2 hev
    have := hz z.1 z.2
    rw [Subgroup.orderOf_coe, hz2] at this
    exact absurd this (by decide)
  exact Odd.of_dvd_nat hodd ⟨Nat.card ↥ℓ.ker, by rw [hc]; ring⟩

theorem eq_commutator_of_perfect_normal {Γ : Type} [Group Γ] {H N : Subgroup Γ} (hNH : N ≤ H)
    (hN : ∀ h ∈ H, ∀ n ∈ N, h * n * h⁻¹ ∈ N) (hperf : ⁅N, N⁆ = N) (hnt : N ≠ ⊥)
    (hs : IsSimpleGroup ↥⁅H, H⁆) : N = ⁅H, H⁆ := by
  have hle : N ≤ ⁅H, H⁆ := by
    rw [← hperf]
    exact Subgroup.commutator_mono hNH hNH
  have hDH : ⁅H, H⁆ ≤ H := by
    refine Subgroup.commutator_le.2 fun a ha b hb => ?_
    rw [commutatorElement_def]
    exact H.mul_mem (H.mul_mem (H.mul_mem ha hb) (H.inv_mem ha)) (H.inv_mem hb)
  have hnorm : (N.subgroupOf ⁅H, H⁆).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hN _ (hDH g.2) _ hn
  rcases CFSG.eq_bot_or_eq_top_of_normal _ hnorm with hbot | htop
  · have hd := Subgroup.subgroupOf_eq_bot.1 hbot
    exact absurd (disjoint_self.1 (hd.mono_right hle)) hnt
  · exact le_antisymm hle (Subgroup.subgroupOf_eq_top.1 htop)

theorem g2Derived_simple_card
    {K : Type} [Field K] [Finite K] (h2 : Nat.card K = 2) :
    IsSimpleGroup ↥⁅quasithinG2 K, quasithinG2 K⁆ ∧
      Nat.card ↥⁅quasithinG2 K, quasithinG2 K⁆ = 6048 := by
  have hGF : Nat.card (GaloisField 2 1) = 2 := by
    rw [GaloisField.card 2 1 one_ne_zero]
    norm_num
  let e : ↥⁅quasithinG2 K, quasithinG2 K⁆ ≃* ↥(StatedSU 3 3 CFSG.Quasithin.G2U.F9) :=
    (Insp9.g2DerivedEquivZMod2 K h2).trans
      ((Insp9.g2DerivedEquivZMod2 (GaloisField 2 1) hGF).symm.trans
        CFSG.Quasithin.G11.P3G2.commutatorG2EquivSU)
  have hmod := CFSG.LinearGroups.UnitaryThreeOverNine.classicalModel_statedSU
    (F := CFSG.Quasithin.G2U.F9) CFSG.Quasithin.G2U.card_F9
  refine ⟨(MulEquiv.isSimpleGroup_congr e).mpr
    (CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity _ 3 3 1 hmod).2, ?_⟩
  rw [Nat.card_congr ((Insp9.g2DerivedEquivZMod2 K h2).trans
    (Insp9.g2DerivedEquivZMod2 (GaloisField 2 1) hGF).symm).toEquiv]
  exact CFSG.Quasithin.G11.P3G2.card_commutatorG2

theorem card_eq_6048_of_normal
    {K : Type} [Field K] [Finite K] (h2 : Nat.card K = 2)
    {N : Subgroup ↥(quasithinG2 K)} (hN : N.Normal) (hperf : ⁅N, N⁆ = N) (hnt : N ≠ ⊥) :
    Nat.card ↥N = 6048 := by
  obtain ⟨hs, hc⟩ := g2Derived_simple_card h2
  have hinj := (quasithinG2 K).subtype_injective
  have hNeq : N.map (quasithinG2 K).subtype = ⁅quasithinG2 K, quasithinG2 K⁆ := by
    refine eq_commutator_of_perfect_normal (H := quasithinG2 K) ?_ ?_ ?_ ?_ hs
    · rintro _ ⟨n, -, rfl⟩
      exact n.2
    · rintro h hh _ ⟨n, hn, rfl⟩
      exact ⟨⟨h, hh⟩ * n * ⟨h, hh⟩⁻¹, hN.conj_mem n hn ⟨h, hh⟩, rfl⟩
    · rw [← Subgroup.map_commutator, hperf]
    · intro hbot
      exact hnt ((Subgroup.map_eq_bot_iff_of_injective N hinj).1 hbot)
  rw [Nat.card_congr (N.equivMapOfInjective (quasithinG2 K).subtype hinj).toEquiv, hNeq]
  exact hc

end B69

end CFSG.Quasithin
