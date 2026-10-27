module

public import CFSG.LocalAnalysis.StandardType.GGQ2CentTransport
public import CFSG.LocalAnalysis.StandardType.GGQ2CentTwE6Frame
public import CFSG.LocalAnalysis.StandardType.GGQ2CentTwE6Cube
public import CFSG.LocalAnalysis.StandardType.GGQ2CentTwE6Rank
public import CFSG.LocalAnalysis.StandardType.GGQTwoAssemble
public import CFSG.Mathlib.GroupTheory.Automorphism.ConjCommute
public import CFSG.Quasithin.Vol2.Ch12Sec7L5zh
public import CFSG.Quasithin.H13.L32NLem14328e
public import CFSG.Quasithin.H13.L32NLem14332g
public import CFSG.Quasithin.Vol2.Ch12Sec7L23a
public import CFSG.Quasithin.Vol2.Ch12Sec7L5c
public import CFSG.Quasithin.Vol2.Ch12Sec7L5u
public import CFSG.Quasithin.Vol2.Ch12Sec7Mod3B

public section

namespace CFSG.StandardType.GGQ2CentPort

open CFSG CFSG.Assembly
open CFSG.Blueprint.Chevalley (ModGL TwistTag)

theorem twistedESixTwoInput_holds :
    twistedESixTwoInput := by
  unfold twistedESixTwoInput
  apply labelTUInput_of_exists (fun lab => lab.tag = .twE6)
  intro G _ _ p B Bs x L D J hS hL
  have hp3 : p = 3 := ggQ2_pThree hS
  subst hp3
  obtain ⟨K, _, _, σ, θ, Fr, ζ, hζ, g, t, κ, hK, hσ, hFr, hζo, hg, hgF, ht, hκ, hβ,
      hcent, h5⟩ := Q2TwE6.exists_frame hS hL
  let R := ↥(LieType.Chevalley.twistedE6RootGroup K σ)
  refine ⟨R, inferInstance, θ, ?_⟩
  intro hN
  let q : L →* R := θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))
  let E : Subgroup R := (Bs.subgroupOf L).map q
  let A : Subgroup (MulAut R) := (ggBeta L θ hN).range
  have hqker : q.ker = Subgroup.center L := by
    change (θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))).ker = Subgroup.center L
    rw [MonoidHom.ker_comp_of_injective _ _ θ.injective]
    exact QuotientGroup.ker_mk' (Subgroup.center L)
  have hEcard : 3 ^ 5 ≤ Nat.card E := by
    have hker : q.ker = (MulAut.conj : ↥L →* MulAut ↥L).ker := by
      rw [hqker, CFSG.mulAut_conj_ker]
    have hcard := CFSG.Quasithin.Lift3.card_map_eq_of_ker_eq q
      (MulAut.conj : ↥L →* MulAut ↥L) hker (Bs.subgroupOf L)
    rw [show E = (Bs.subgroupOf L).map q from rfl, hcard]
    exact h5
  have hconj_gen : ∀ (u : L) (hu : u ∈ Bs.subgroupOf L),
      MulAut.conj (q u) = ggBeta L θ hN ⟨(u : G), Subgroup.mem_subgroupOf.mp hu⟩ := by
    intro u hu
    refine MulEquiv.ext fun s => ?_
    obtain ⟨q', rfl⟩ := θ.surjective s
    induction q' using QuotientGroup.induction_on with
    | H l =>
      rw [ggBeta_eq, ggLAut_apply, MulAut.conj_apply]
      change θ (u : L ⧸ Subgroup.center L) * θ l * (θ (u : L ⧸ Subgroup.center L))⁻¹ = _
      rw [← map_inv, ← map_mul, ← map_mul, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
        ← QuotientGroup.mk_mul]
      congr 2
  constructor
  ·
    unfold toralAt actionThree
    intro r hr h3r
    have hr3 : r ^ 3 = 1 := by
      have hc : ∀ v ∈ NoOffRest.hypE6, t v * (r : ModGL TwistTag.E6.tag K) =
          (r : ModGL TwistTag.E6.tag K) * t v := by
        intro v hv
        obtain ⟨b, hb⟩ := MonoidHom.mem_range.mp (hκ v hv)
        have h1 := hβ hN b r
        rw [show Multiplicative.toAdd (κ b) = v from congrArg Multiplicative.toAdd hb,
          hr _ (MonoidHom.mem_range.mpr ⟨b, rfl⟩)] at h1
        exact (eq_mul_inv_iff_mul_eq.mp h1).symm
      have hr3_mod : ((r : R) : ModGL TwistTag.E6.tag K) ^ 3 = 1 :=
        Q2TwE6.cube_eq_one_of_commute_hypE6 σ hσ hFr hζ hζo hg hgF ht r.2 hc
      apply Subtype.ext
      exact hr3_mod
    have hH_elem : IsElemAbelian 3 (E ⊔ Subgroup.zpowers r : Subgroup R) := by
      have hU_elem : IsElemAbelian 3 (Bs.subgroupOf L) :=
        CFSG.Open.IsElemAbelian.subgroupOf hS.1.1.2.1.2.1 L
      have hE_elem : IsElemAbelian 3 E := CFSG.Open.IsElemAbelian.map hU_elem q
      have hz_elem : IsElemAbelian 3 (Subgroup.zpowers r) :=
        CFSG.Open.isElemAbelian_zpowers hr3
      refine CFSG.Open.IsElemAbelian.sup_of_commute hE_elem hz_elem ?_
      intro a ha b hb
      have har : a * r = r * a := by
        obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp ha
        have hconj : MulAut.conj (q u) =
            ggBeta L θ hN ⟨(u : G), Subgroup.mem_subgroupOf.mp hu⟩ := hconj_gen u hu
        have hfix : ggBeta L θ hN ⟨(u : G), Subgroup.mem_subgroupOf.mp hu⟩ r = r :=
          hr _ (MonoidHom.mem_range.mpr ⟨⟨(u : G), Subgroup.mem_subgroupOf.mp hu⟩, rfl⟩)
        rw [← hconj] at hfix
        rw [MulAut.conj_apply] at hfix
        calc
          q u * r = q u * r * (q u)⁻¹ * q u := by
            rw [mul_assoc, inv_mul_cancel, mul_one]
          _ = r * q u := by rw [hfix]
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hb
      rw [← hn]
      exact (Commute.zpow_right har n).eq
    have hH_card : Nat.card (E ⊔ Subgroup.zpowers r : Subgroup R) ≤ 3 ^ 5 :=
      Q2TwE6.card_le_of_isElemAbelian hK σ hσ hH_elem
    have hEr : E = E ⊔ Subgroup.zpowers r := by
      exact Subgroup.eq_of_le_of_card_ge le_sup_left (le_trans hH_card hEcard)
    have hrE : r ∈ E := by
      rw [hEr]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers_iff.mpr ⟨1, by simp⟩)
    obtain ⟨y, hy, hry⟩ := Subgroup.mem_map.mp hrE
    have hconj : MulAut.conj r =
        ggBeta L θ hN ⟨(y : G), Subgroup.mem_subgroupOf.mp hy⟩ := by
      rw [← hry]
      exact hconj_gen y hy
    rw [hconj]
    exact MonoidHom.mem_range.mpr ⟨_, rfl⟩
  ·
    intro hx
    unfold internalAt
    refine ⟨Bs.subgroupOf L, ?_, le_rfl, ?_, ?_⟩
    · exact CFSG.Open.IsElemAbelian.subgroupOf hS.1.1.2.1.2.1 L
    ·
      let S : Subgroup R :=
        (A ⊓ (MulAut.conj : R →* MulAut R).range).comap (MulAut.conj : R →* MulAut R)
      have hZ : Subgroup.center R = ⊥ := by
        have h := CFSG.StandardType.InndiagE6.diagNF_twistedE6 (n := 1) (by norm_num) K
          (by simpa using hK) σ hσ
        simpa using h.1
      have hinj : Function.Injective (MulAut.conj : R →* MulAut R) :=
        CFSG.mulAut_conj_injective hZ
      have hA_elem : IsElemAbelian 3 A := by
        have hU_top : IsElemAbelian 3 (Bs.subgroupOf Bs) :=
          CFSG.Open.IsElemAbelian.subgroupOf hS.1.1.2.1.2.1 Bs
        have h := CFSG.Open.IsElemAbelian.map hU_top (ggBeta L θ hN)
        simpa [A, Subgroup.subgroupOf_self, MonoidHom.range_eq_map] using h
      have hS_elem : IsElemAbelian 3 S := by
        have h : IsElemAbelian 3 (A ⊓ (MulAut.conj : R →* MulAut R).range) :=
          CFSG.Open.IsElemAbelian.mono hA_elem inf_le_left
        exact CFSG.Open.IsElemAbelian.comap h hinj
      have hS_card : Nat.card S ≤ 3 ^ 5 :=
        Q2TwE6.card_le_of_isElemAbelian hK σ hσ hS_elem
      have hE_le_S : E ≤ S := by
        intro e he
        obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp he
        have hconj : MulAut.conj (q u) =
            ggBeta L θ hN ⟨(u : G), Subgroup.mem_subgroupOf.mp hu⟩ := hconj_gen u hu
        refine ⟨?_, ⟨q u, rfl⟩⟩
        change MulAut.conj (q u) ∈ A
        rw [hconj]
        exact MonoidHom.mem_range.mpr ⟨_, rfl⟩
      have hES : E = S := by
        exact Subgroup.eq_of_le_of_card_ge hE_le_S (le_trans hS_card hEcard)
      ext φ
      constructor
      · intro hφ
        obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hφ
        have hconj : MulAut.conj (q u) =
            ggBeta L θ hN ⟨(u : G), Subgroup.mem_subgroupOf.mp hu⟩ := hconj_gen u hu
        refine ⟨?_, ⟨q u, rfl⟩⟩
        change MulAut.conj (q u) ∈ A
        rw [hconj]
        exact MonoidHom.mem_range.mpr ⟨_, rfl⟩
      · intro hφ
        obtain ⟨hφA, hφconj⟩ := hφ
        obtain ⟨r, rfl⟩ := hφconj
        have hrS : r ∈ S := ⟨hφA, ⟨r, rfl⟩⟩
        rw [← hES] at hrS
        obtain ⟨u, hu, hru⟩ := Subgroup.mem_map.mp hrS
        refine ⟨u, hu, ?_⟩
        change MulAut.conj (q u) = MulAut.conj r
        rw [hru]
    ·
      intro z hz hz3
      have hcentz : (z : G) ∈ Subgroup.centralizer (Bs : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro b hb
        exact hcent z hz hz3 b hb
      have hz3G : (z : G) ^ 3 = 1 := by
        have hψ : Function.Surjective q := by
          intro x
          obtain ⟨r, rfl⟩ := θ.surjective x
          obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center L) r
          exact ⟨l, rfl⟩
        have hker : q.ker ≤ Subgroup.center L := le_of_eq hqker
        have hperf : commutator L = ⊤ := hS.1.1.1.2.2.2.2.2.2.1.2.2.2.1.2.2.1
        have hzL : z ^ 3 = 1 := Q2TwE6.center_pow_three hK σ hσ hψ hker hperf hz hz3
        simpa using congrArg Subtype.val hzL
      have hzBs : (z : G) ∈ Bs := hS.1.1.2.1.2.2.2 (z : G) hcentz hz3G
      exact Subgroup.mem_subgroupOf.mpr hzBs

end CFSG.StandardType.GGQ2CentPort

end
