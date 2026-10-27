module

public import CFSG.RankThree.PartTwo.Sec16.Item16Tail13Defs
public import CFSG.RankThree.PartTwo.Sec15.HypS
public import CFSG.RankThree.PartTwo.Sec13.Item138N
import CFSG.RankThree.PartTwo.Sec16.Item1613ResProofDL
import CFSG.RankThree.PartTwo.Sec16.Item1613ResProofFixMat
import CFSG.RankThree.PartTwo.Sec16.Item1613ResProofFixAut
import CFSG.RankThree.PartTwo.Sec16.Item1613StepsProofFix
import CFSG.RankThree.PartTwo.Sec16.Item1613StepsProofTrans
import CFSG.RankThree.PartTwo.Sec16.Item16Tail14Tools
import CFSG.RankThree.PartTwo.Sec16.Item16Tail13
import CFSG.RankThree.PartTwo.Sec16.Item16Tail13PGL
import CFSG.RankThree.PartTwo.Sec16.Item16Tail
import CFSG.RankThree.PartTwo.Sec13.Item131Facts
import CFSG.RankThree.PartTwo.Sec13.Item13Sporadic
import CFSG.RankThree.PartTwo.Sec13.Item13SLTwo
import CFSG.RankThree.PartTwo.Sec13.Item138ProofExists
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
import CFSG.RankThree.PartTwo.Sec4.LThreePiHessian
import CFSG.RankThree.PartTwo.Sec4.T444.Step453
import CFSG.RankThree.PartTwo.Sec5.Tools
public import CFSG.RankThree.PartTwo.Sec13.Item136PGL

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.GH74.GLS
open CFSG.Assembly.RankThreeEven (projImage)
open Matrix (ProjGenLinGroup)

theorem kSL3PiCommInner :
    ∀ (X : Type) [Group X] (π : Bool) (p f : ℕ) (K : Type) [Field K], Sec4.PiField π p f K →
      Sec4.ModThree π (p ^ f) → 2 < p ^ f →
      Nonempty (X ≃* projImage (Sec4.slPi π 3 (p ^ f) K)) →
        ∀ α β : MulAut X, (∃ k : ℕ, (α * β * α⁻¹ * β⁻¹) ^ 2 ^ k = 1) →
          α * β * α⁻¹ * β⁻¹ ∈ (MulAut.conj : X →* MulAut X).range := by
  intro X _ π p f K _ hK _ hq2 ⟨e⟩ α β ⟨k, hk⟩
  exact Proof1613Res.isInnerAut_commutator_of_two_pow hK hq2 e α β hk

theorem kSL3PiType1Inv :
    ∀ (π : Bool) (p f : ℕ) (K : Type) [Field K], Sec4.PiField π p f K →
      Sec4.ModThree π (p ^ f) →
      ∀ y ∈ Sec4.glPi π 3 (p ^ f) K, Sec4.Type123 π (p ^ f) K y 3 →
      ∀ s ∈ Sec4.slPi π 3 (p ^ f) K, ProjGenLinGroup.mk s ≠ 1 → ProjGenLinGroup.mk s ^ 3 = 1 →
        ProjGenLinGroup.mk y * ProjGenLinGroup.mk s * (ProjGenLinGroup.mk y)⁻¹ =
          ProjGenLinGroup.mk s →
        ∀ u ∈ projImage (Sec4.slPi π 3 (p ^ f) K), ∀ v ∈ projImage (Sec4.slPi π 3 (p ^ f) K),
          u ^ 2 = 1 → v ^ 2 = 1 →
          u * ProjGenLinGroup.mk s = ProjGenLinGroup.mk s * u →
          v * ProjGenLinGroup.mk s = ProjGenLinGroup.mk s * v → u * v = v * u := by
  intro π p f K _ hK hq y _ hy3 s hs hs1 hs3 hys u hu v hv hu2 hv2 hus hvs
  have htype := Proof1613Res.type1_of_commute_type3 hK hq hy3 hs hs1 hs3 hys
  obtain ⟨h, -, rfl⟩ := hu
  obtain ⟨k, -, rfl⟩ := hv
  have hh2 : h ^ 2 ∈ CFSG.Assembly.LowTwoRank.StatedScalars (Fin 3) K := by
    rw [← Sec4.mk_eq_one_iff_mem_statedScalars, map_pow]
    exact hu2
  have hk2 : k ^ 2 ∈ CFSG.Assembly.LowTwoRank.StatedScalars (Fin 3) K := by
    rw [← Sec4.mk_eq_one_iff_mem_statedScalars, map_pow]
    exact hv2
  exact Proof1613Res.commute_of_sq_of_commute_type1 hK hq htype hh2 hk2 hus hvs

end CFSG.RankThree.PartTwo.Sec16

namespace CFSG.RankThree.PartTwo.Sec16.Proof1613Res

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14
  CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Sec16 CFSG.RankThree.PartTwo.Sec16.Proof169
  CFSG.RankThree.PartTwo.Sec16.Proof1613 CFSG.RankThree.PartTwo.Sec16.Proof1614 CFSG.GH74.GLS
open CFSG.Assembly.RankThreeEven (projImage)
open CFSG.Assembly.LowTwoRank (StatedScalars)
open Matrix (ProjGenLinGroup GeneralLinearGroup)
open scoped commutatorElement

section Elementary

variable {X : Type*} [Group X]

theorem eq_one_of_conj_eq_one (hZ : Subgroup.center X = ⊥) {u : X}
    (h : MulAut.conj u = 1) : u = 1 := by
  have hu : u ∈ Subgroup.center X := Subgroup.mem_center_iff.mpr fun z => by
    have h1 := congrArg (fun σ : MulAut X => σ z) h
    simp only [MulAut.conj_apply, MulAut.one_apply] at h1
    calc z * u = u * z * u⁻¹ * u := by rw [h1]
      _ = u * z := by group
  rw [hZ] at hu
  exact Subgroup.mem_bot.mp hu

theorem commute_of_conj_commute (hZ : Subgroup.center X = ⊥) {u w : X}
    (h : MulAut.conj u * MulAut.conj w = MulAut.conj w * MulAut.conj u) : u * w = w * u := by
  have h1 : MulAut.conj (u * w * u⁻¹ * w⁻¹) = 1 := by
    simp only [map_mul, map_inv, h]
    group
  have h2 := eq_one_of_conj_eq_one hZ h1
  calc u * w = u * w * u⁻¹ * w⁻¹ * (w * u) := by group
    _ = w * u := by rw [h2, one_mul]

theorem exists_pow_two_pow_ne_one {u : X} (hu : u ≠ 1) :
    ∀ m : ℕ, u ^ 2 ^ m = 1 → ∃ k : ℕ, u ^ 2 ^ k ≠ 1 ∧ (u ^ 2 ^ k) ^ 2 = 1 := by
  intro m
  induction m with
  | zero => intro h; exact absurd (by simpa using h) hu
  | succ m ih =>
    intro h
    by_cases hm : u ^ 2 ^ m = 1
    · exact ih hm
    · exact ⟨m, hm, by rw [← pow_mul, ← pow_succ, h]⟩

end Elementary

section Simple

variable {G : Type} [Group G] [Finite G]

theorem aschbacherSolvableCore_eq_bot_of_isSimpleGroup {a : G} {L : Subgroup G}
    (hL : L ∈ thetaComponentsAt 3 a) (hsimp : IsSimpleGroup ↥L) :
    aschbacherSolvableCore 3 ↥L = ⊥ := by
  have := Sec4.aschbacherSolvableCore_characteristic ↥L
  rcases hsimp.eq_bot_or_eq_top_of_normal (aschbacherSolvableCore 3 ↥L) with h | h
  · exact h
  · exfalso
    have := CFSG.LocalCores.isQuasisimple_nontrivial
      (Sec6.isQuasisimple_of_mem_thetaComponentsAt hL)
    obtain ⟨u, v, huv⟩ := exists_pair_ne (↥L ⧸ aschbacherSolvableCore 3 ↥L)
    induction u using QuotientGroup.induction_on with
    | H u =>
      induction v using QuotientGroup.induction_on with
      | H v =>
        apply huv
        rw [QuotientGroup.eq, h]
        exact Subgroup.mem_top _

omit [Finite G] in
theorem eq_of_mk_eq {L : Subgroup G} (hθ : aschbacherSolvableCore 3 ↥L = ⊥) {u v : ↥L}
    (h : (u : ↥L ⧸ aschbacherSolvableCore 3 ↥L) = v) : u = v := by
  rw [QuotientGroup.eq, hθ, Subgroup.mem_bot] at h
  calc u = u * (u⁻¹ * v) := by rw [h, mul_one]
    _ = v := by group

theorem mem_centralizer_of_act_eq_one {L : Subgroup G} (hθ : aschbacherSolvableCore 3 ↥L = ⊥)
    {g : G} (hg : g ∈ Subgroup.normalizer (L : Set G))
    (h1 : thetaQuotMulAut ↥L (L.normalizerMonoidHom ⟨g, hg⟩) = 1) :
    g ∈ Subgroup.centralizer (L : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  have h2 := congrArg (fun σ : MulAut (↥L ⧸ aschbacherSolvableCore 3 ↥L) =>
    σ ((⟨l, hl⟩ : ↥L) : ↥L ⧸ aschbacherSolvableCore 3 ↥L)) h1
  simp only [MulAut.one_apply, thetaQuotMulAut_mk] at h2
  have h3 := congrArg Subtype.val (eq_of_mk_eq hθ h2)
  rw [normalizerMonoidHom_apply_coe] at h3
  calc l * g = g * l * g⁻¹ * g := by rw [h3]
    _ = g * l := by group

theorem act_eq_conj_of_mem {L : Subgroup G} {d : G} (hdL : d ∈ L)
    (hd : d ∈ Subgroup.normalizer (L : Set G)) :
    thetaQuotMulAut ↥L (L.normalizerMonoidHom ⟨d, hd⟩) =
      MulAut.conj ((⟨d, hdL⟩ : ↥L) : ↥L ⧸ aschbacherSolvableCore 3 ↥L) := by
  ext y
  induction y using QuotientGroup.induction_on with
  | H y => rfl

omit [Finite G] in
theorem le_normalizer_centralizer {A L : Subgroup G}
    (hAL : A ≤ Subgroup.normalizer (L : Set G)) :
    A ≤ Subgroup.normalizer ((Subgroup.centralizer (L : Set G) : Subgroup G) : Set G) := by
  intro a ha
  have haL := hAL ha
  have hkey : ∀ b ∈ Subgroup.normalizer (L : Set G), ∀ g ∈ Subgroup.centralizer (L : Set G),
      b * g * b⁻¹ ∈ Subgroup.centralizer (L : Set G) := by
    intro b hb g hg
    rw [Subgroup.mem_centralizer_iff] at hg ⊢
    intro l hl
    have hl' : b⁻¹ * l * b⁻¹⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp (inv_mem hb) l).mp hl
    have h1 := hg _ hl'
    calc l * (b * g * b⁻¹) = b * ((b⁻¹ * l * b⁻¹⁻¹) * g) * b⁻¹ := by group
      _ = b * (g * (b⁻¹ * l * b⁻¹⁻¹)) * b⁻¹ := by rw [h1]
      _ = b * g * b⁻¹ * l := by group
  rw [Subgroup.mem_normalizer_iff]
  intro g
  refine ⟨hkey a haL g, fun hg => ?_⟩
  have := hkey a⁻¹ (inv_mem haL) _ hg
  rwa [show a⁻¹ * (a * g * a⁻¹) * a⁻¹⁻¹ = g by group] at this

end Simple

section TypeThree


variable {G : Type} [Group G] [Finite G]

theorem exists_type_three (h131 : Item131) {A L : Subgroup G} {c : G} (h : Ctx169 G A c L)
    (hPGL : Sec8.IsZ3PGLThreePi ↥(lBarA c L A)) : ∃ x ∈ A, InducesTypeOn L x 3 := by
  have hcL : c ∉ L := h.toSec15R.hypS.2.2 c h.zpowers_mem_omegaA L h.mem_lA
  obtain ⟨-, ⟨hM12p, hM12z⟩, ⟨hJ2p, hJ2z⟩⟩ := sporadicModels131
  obtain ⟨hL3, -, -⟩ := facts_of_isZ3PGLThreePi h.toSec13Data hPGL
  obtain ⟨p, e, hp, -, hisoL⟩ := hL3
  rcases cases131 h131 sporadicModels131 slTwoCenter h.toSec13Data with
      ⟨-, -, ⟨ψ⟩, -⟩ | ⟨-, -, hMJ, -⟩ | ⟨-, -, -, x, hxA, hx⟩ | ⟨hcL', -⟩
  · exact (false_of_pgl_of_prod kSPGLProper h.toSec13Data hPGL ψ).elim
  · exfalso
    rcases hMJ with ⟨⟨χ⟩⟩ | ⟨⟨χ⟩⟩
    · obtain ⟨-, -, -, ⟨χ'⟩⟩ := facts_of_prod h.toSec13Data hM12p hM12z χ
      exact KFacts.KS14.not_isoLThreePi_M12 p e (Proof169.isoLThreePi_of_mulEquiv χ' hisoL)
    · obtain ⟨-, -, -, ⟨χ'⟩⟩ := facts_of_prod h.toSec13Data hJ2p hJ2z χ
      exact KFacts.KS14.ks17J2NotList.1 p e (Proof169.isoLThreePi_of_mulEquiv χ' hisoL)
  · exact ⟨x, hxA, hx⟩
  · exact (hcL hcL').elim

end TypeThree

section Outer

variable {G : Type} [Group G] [Finite G]

theorem not_inner_of_inducesTypeOn_three {a : G} {L : Subgroup G}
    (hL : L ∈ thetaComponentsAt 3 a) {x : G} (hx : InducesTypeOn L x 3)
    (hxN : x ∈ Subgroup.normalizer (L : Set G)) (w : ↥L ⧸ aschbacherSolvableCore 3 ↥L)
    (hw : thetaQuotMulAut ↥L (L.normalizerMonoidHom ⟨x, hxN⟩) = MulAut.conj w) : False := by
  obtain ⟨hxN', π, p, f, K, _, hK, hq, e, y, hyH, hy3, hact⟩ := hx
  have hPerfL : Group.IsPerfect (L ⧸ aschbacherSolvableCore 3 L) :=
    (Sec6.isQuasisimple_of_mem_thetaComponentsAt hL).1
  have hPerf : Group.IsPerfect (projImage (slPi π 3 (p ^ f) K)) :=
    Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  apply not_inner_of_type3 hK hq hyH hy3
  obtain ⟨s, hs, hse⟩ := (e w).2
  refine ⟨s, hs, ?_⟩
  have hmod : ∀ m ∈ slPi π 3 (p ^ f) K,
      s⁻¹ * y * m * (s⁻¹ * y)⁻¹ * m⁻¹ ∈ StatedScalars (Fin 3) K := by
    intro m hm
    rw [← mk_eq_one_iff_mem_statedScalars]
    set z := e.symm ⟨ProjGenLinGroup.mk m, Subgroup.mem_map_of_mem _ hm⟩ with hz
    have hez : (e z : ProjGenLinGroup (Fin 3) K) = ProjGenLinGroup.mk m := by
      rw [hz, MulEquiv.apply_symm_apply]
    have h1 := hact z
    have h2 : thetaQuotMulAut L (L.normalizerMonoidHom ⟨x, hxN'⟩) z = w * z * w⁻¹ := by
      rw [show (⟨x, hxN'⟩ : Subgroup.normalizer (L : Set G)) = ⟨x, hxN⟩ from rfl, hw,
        MulAut.conj_apply]
    rw [h2, map_mul, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
      ← hse, hez] at h1
    simp only [map_mul, map_inv]
    calc (ProjGenLinGroup.mk s)⁻¹ * ProjGenLinGroup.mk y * ProjGenLinGroup.mk m *
          ((ProjGenLinGroup.mk s)⁻¹ * ProjGenLinGroup.mk y)⁻¹ * (ProjGenLinGroup.mk m)⁻¹ =
        (ProjGenLinGroup.mk s)⁻¹ * (ProjGenLinGroup.mk y * ProjGenLinGroup.mk m *
          (ProjGenLinGroup.mk y)⁻¹) * ProjGenLinGroup.mk s * (ProjGenLinGroup.mk m)⁻¹ := by group
      _ = 1 := by rw [← h1]; group
  intro m hm
  have hc := commute_of_comm_mod_scalars hmod m hm
  calc y * m * y⁻¹ = s * (s⁻¹ * y * m) * y⁻¹ := by group
    _ = s * (m * (s⁻¹ * y)) * y⁻¹ := by rw [hc]
    _ = s * m * s⁻¹ := by group

end Outer

section Involutions

variable {G : Type} [Group G] [Finite G]

theorem commute_of_ksl3PiType1Inv {L : Subgroup G}
    (hθ : aschbacherSolvableCore 3 ↥L = ⊥) {x d : G} (hx : InducesTypeOn L x 3) (hdL : d ∈ L)
    (hd1 : d ≠ 1) (hd3 : d ^ 3 = 1) (hxd : x * d = d * x) {g k : G} (hgL : g ∈ L) (hkL : k ∈ L)
    (hg2 : g ^ 2 = 1) (hk2 : k ^ 2 = 1) (hgd : g * d = d * g) (hkd : k * d = d * k) :
    g * k = k * g := by
  have hInv1 := kSL3PiType1Inv
  obtain ⟨hxN, π, p, f, K, _, hK, hq, e, y, hyH, hy3, hact⟩ := hx
  set σx := thetaQuotMulAut L (L.normalizerMonoidHom ⟨x, hxN⟩) with hσx
  set d' : ↥L := ⟨d, hdL⟩ with hd'
  set g' : ↥L := ⟨g, hgL⟩ with hg'
  set k' : ↥L := ⟨k, hkL⟩ with hk'
  set db : ↥L ⧸ aschbacherSolvableCore 3 ↥L := QuotientGroup.mk' _ d' with hdb
  set gb : ↥L ⧸ aschbacherSolvableCore 3 ↥L := QuotientGroup.mk' _ g' with hgb
  set kb : ↥L ⧸ aschbacherSolvableCore 3 ↥L := QuotientGroup.mk' _ k' with hkb
  have hmkeq : ∀ u v : ↥L, QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) u =
      QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) v → u = v := fun u v huv =>
    eq_of_mk_eq hθ huv
  obtain ⟨s, hs, hse⟩ := Subgroup.mem_map.mp (e db).2
  have hdb1 : db ≠ 1 := by
    intro h1
    apply hd1
    have h2 : d' = 1 := hmkeq d' 1 (by rw [map_one]; exact h1)
    exact congrArg Subtype.val h2
  have hs1 : ProjGenLinGroup.mk s ≠ 1 := by
    rw [hse]
    intro h1
    apply hdb1
    apply e.injective
    rw [map_one]
    exact Subtype.ext h1
  have hd'3 : d' ^ 3 = 1 := Subtype.ext (by simpa using hd3)
  have hs3 : ProjGenLinGroup.mk s ^ 3 = 1 := by
    rw [hse, ← Subgroup.coe_pow, ← map_pow, hdb, ← map_pow, hd'3, map_one, map_one,
      Subgroup.coe_one]
  have hfix : σx db = db := by
    rw [hσx, hdb, QuotientGroup.mk'_apply, thetaQuotMulAut_mk]
    congr 1
    apply Subtype.ext
    rw [normalizerMonoidHom_apply_coe, hxd, mul_inv_cancel_right]
  have hys : ProjGenLinGroup.mk y * ProjGenLinGroup.mk s * (ProjGenLinGroup.mk y)⁻¹ =
      ProjGenLinGroup.mk s := by
    have h1 := hact db
    rw [hfix, ← hse] at h1
    exact h1.symm
  have hsq : ∀ u : ↥L, u ^ 2 = 1 →
      ((e (QuotientGroup.mk' _ u) : projImage (Sec4.slPi π 3 (p ^ f) K)) :
        ProjGenLinGroup (Fin 3) K) ^ 2 = 1 := fun u hu => by
    rw [← Subgroup.coe_pow, ← map_pow, ← map_pow, hu, map_one, map_one, Subgroup.coe_one]
  have hcm : ∀ u : ↥L, (u : G) * d = d * u →
      ((e (QuotientGroup.mk' _ u) : projImage (Sec4.slPi π 3 (p ^ f) K)) :
        ProjGenLinGroup (Fin 3) K) * ProjGenLinGroup.mk s =
      ProjGenLinGroup.mk s * ((e (QuotientGroup.mk' _ u) :
        projImage (Sec4.slPi π 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) := fun u hu => by
    have hu' : u * d' = d' * u := Subtype.ext hu
    rw [hse, ← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul, hdb, ← map_mul,
      ← map_mul, hu']
  have hg'2 : g' ^ 2 = 1 := Subtype.ext (by simpa using hg2)
  have hk'2 : k' ^ 2 = 1 := Subtype.ext (by simpa using hk2)
  have key := hInv1 π p f K hK hq y hyH hy3 s hs hs1 hs3 hys _ (e gb).2 _ (e kb).2
    (hsq g' hg'2) (hsq k' hk'2) (hcm g' hgd) (hcm k' hkd)
  have h1 : e (gb * kb) = e (kb * gb) := by
    apply Subtype.ext
    rw [map_mul, map_mul, Subgroup.coe_mul, Subgroup.coe_mul]
    exact key
  have h2 : g' * k' = k' * g' := hmkeq _ _ (by rw [map_mul, map_mul]; exact e.injective h1)
  exact congrArg Subtype.val h2

theorem not_odd_thetaCen_of_involution
    {A L : Subgroup G} {c d : G}
    (h : Ctx169 G A c L) (hALd : A ⊓ L = Subgroup.zpowers d)
    (hcomm : ∀ g ∈ L, ∀ k ∈ L, g ^ 2 = 1 → k ^ 2 = 1 → g * d = d * g → k * d = d * k →
      g * k = k * g)
    {ℓ : G} (hℓL : ℓ ∈ L) (hℓ1 : ℓ ≠ 1) (hℓ2 : ℓ ^ 2 = 1) (hℓd : ℓ * d = d * ℓ) :
    ¬ Odd (Nat.card (thetaCen ((Subgroup.zpowers c ⊔ (A ⊓ L) : Subgroup G) : Set G))) := by
  set B := Subgroup.zpowers c ⊔ (A ⊓ L) with hB
  let V : Subgroup G :=
    { carrier := {g | g ∈ L ∧ g ^ 2 = 1 ∧ g * d = d * g}
      mul_mem' := by
        rintro a b ⟨haL, ha2, had⟩ ⟨hbL, hb2, hbd⟩
        have hab : Commute a b := hcomm a haL b hbL ha2 hb2 had hbd
        refine ⟨L.mul_mem haL hbL, by rw [hab.mul_pow, ha2, hb2, one_mul], ?_⟩
        calc a * b * d = a * (b * d) := by group
          _ = a * (d * b) := by rw [hbd]
          _ = a * d * b := by group
          _ = d * a * b := by rw [had]
          _ = d * (a * b) := by group
      one_mem' := ⟨L.one_mem, one_pow 2, by group⟩
      inv_mem' := by
        rintro a ⟨haL, ha2, had⟩
        refine ⟨L.inv_mem haL, by rw [inv_pow, ha2, inv_one], ?_⟩
        calc a⁻¹ * d = a⁻¹ * (d * a) * a⁻¹ := by group
          _ = a⁻¹ * (a * d) * a⁻¹ := by rw [had]
          _ = d * a⁻¹ := by group }
  have hmemV : ∀ g, g ∈ V ↔ g ∈ L ∧ g ^ 2 = 1 ∧ g * d = d * g := fun g => Iff.rfl
  have hV2 : IsPGroup 2 V := fun g => ⟨1, Subtype.ext (by
    simpa using ((hmemV g).mp g.2).2.1)⟩
  have hV1 : V ≠ ⊥ := by
    intro hbot
    have hℓV : ℓ ∈ V := (hmemV ℓ).mpr ⟨hℓL, hℓ2, hℓd⟩
    rw [hbot, Subgroup.mem_bot] at hℓV
    exact hℓ1 hℓV
  have hBV : B ≤ Subgroup.centralizer (V : Set G) := by
    refine sup_le (Subgroup.zpowers_le.mpr ?_) ?_
    · rw [Subgroup.mem_centralizer_iff]
      intro g hg
      exact Subgroup.mem_centralizer_singleton_iff.mp (h.le_centralizer ((hmemV g).mp hg).1)
    · rw [hALd, Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
      intro g hg
      exact ((hmemV g).mp hg).2.2
  have hVC : V ≤ Subgroup.centralizer (B : Set G) := Subgroup.le_centralizer_iff.mp hBV
  have hcB : c ∈ B := (le_sup_left : Subgroup.zpowers c ≤ B) (Subgroup.mem_zpowers c)
  have hdB : d ∈ B := (le_sup_right : A ⊓ L ≤ B) (hALd ▸ Subgroup.mem_zpowers d)
  have hfwd : ∀ g ∈ Subgroup.centralizer (B : Set G), ∀ v ∈ V, g * v * g⁻¹ ∈ V := by
    intro g hg v hv
    obtain ⟨hvL, hv2, hvd⟩ := (hmemV v).mp hv
    have hgc : g ∈ Subgroup.centralizer ({c} : Set G) :=
      Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hcB) hg
    have hgN : g ∈ Subgroup.normalizer (L : Set G) :=
      centralizer_le_normalizer_L h.toSec14Std hgc
    have hgd : g * d = d * g := (Subgroup.mem_centralizer_iff.mp hg d hdB).symm
    refine (hmemV _).mpr ⟨(Subgroup.mem_normalizer_iff.mp hgN v).mp hvL, ?_, ?_⟩
    · rw [conj_pow, hv2]
      group
    · have hgd' : g⁻¹ * d = d * g⁻¹ := by
        calc g⁻¹ * d = g⁻¹ * (d * g) * g⁻¹ := by group
          _ = g⁻¹ * (g * d) * g⁻¹ := by rw [hgd]
          _ = d * g⁻¹ := by group
      calc g * v * g⁻¹ * d = g * v * (g⁻¹ * d) := by group
        _ = g * v * (d * g⁻¹) := by rw [hgd']
        _ = g * (v * d) * g⁻¹ := by group
        _ = g * (d * v) * g⁻¹ := by rw [hvd]
        _ = (g * d) * v * g⁻¹ := by group
        _ = (d * g) * v * g⁻¹ := by rw [hgd]
        _ = d * (g * v * g⁻¹) := by group
  have hCN : Subgroup.centralizer (B : Set G) ≤ Subgroup.normalizer (V : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro v
    refine ⟨hfwd g hg v, fun hv => ?_⟩
    have := hfwd g⁻¹ (inv_mem hg) _ hv
    rwa [show g⁻¹ * (g * v * g⁻¹) * g⁻¹⁻¹ = v by group] at this
  have hVθ : V ≤ thetaCen (B : Set G) :=
    Sec4.le_inSubgroup_aschbacherSolvableCore_of_isPGroup_two hVC hCN hV2
  exact not_odd_of_le hVθ hV2 hV1

end Involutions

end CFSG.RankThree.PartTwo.Sec16.Proof1613Res

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14
  CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Sec16.Proof169
  CFSG.RankThree.PartTwo.Sec16.Proof1613 CFSG.RankThree.PartTwo.Sec16.Proof1614
  CFSG.RankThree.PartTwo.Sec16.Proof1613Res CFSG.GH74.GLS
open CFSG.Assembly.RankThreeEven (projImage)

section Item1616Fix


theorem step1616Fix_of (h1612 : Step1612) (h131 : Item131) (hFix : KS1613Fix)
    : Step1616Fix := by
  have hComm := kSL3PiCommInner
  intro G _ _ A c L h hPGL S hS hSc
  by_cases hθ : Odd (Nat.card (thetaCen ((Subgroup.zpowers c ⊔ (A ⊓ L) : Subgroup G) : Set G)))
  swap
  · exact Or.inr hθ
  left
  have hA := h.isElemAbelian
  have hA27 : Nat.card A = 27 := h.card_eq
  have hcA : c ∈ A := h.mem_A
  have hc1 : c ≠ 1 := h.toSec13Data.ne_one
  have hcL : c ∉ L := h.toSec15R.hypS.2.2 c h.zpowers_mem_omegaA L h.mem_lA
  have hS2 : IsPGroup 2 S := (isPiSubgroup_piOf_iff Nat.prime_two S).mp hS.prop.2
  have hAS : A ≤ Subgroup.normalizer (S : Set G) := hS.prop.1.1.1.2.2
  have hLc : L ∈ thetaComponentsAt 3 c := h.mem_thetaComponentsAt
  obtain ⟨hsimp, hCL⟩ : IsSimpleGroup ↥L ∧
      ∀ T ∈ invariantPiSubgroups (Subgroup.centralizer (L : Set G)) A (piOf 2), T = ⊥ := by
    rcases h1612 G A c L h with h1 | ⟨⟨ψ⟩⟩
    · exact h1
    · exfalso
      obtain ⟨-, -, ⟨ψ'⟩, -⟩ := facts_l34 h ψ
      exact false_of_pgl_of_prod kSPGLProper h.toSec13Data hPGL ψ'
  have hθL : aschbacherSolvableCore 3 ↥L = ⊥ :=
    aschbacherSolvableCore_eq_bot_of_isSimpleGroup hLc hsimp
  have hZ : Subgroup.center (↥L ⧸ aschbacherSolvableCore 3 ↥L) = ⊥ :=
    (facts_of_isZ3PGLThreePi h.toSec13Data hPGL).2.1
  have hSCL : S ⊓ Subgroup.centralizer (L : Set G) = ⊥ :=
    hCL _ ⟨inf_le_right, (isPiSubgroup_piOf_iff Nat.prime_two _).mpr (hS2.to_le inf_le_left),
      le_normalizer_inf hAS (le_normalizer_centralizer h.le_normalizer)⟩
  obtain ⟨d, hdAL, hd1, hALd⟩ := Sec5.exists_eq_zpowers_of_card_eq_prime Nat.prime_three
    (Proof1614Trans.card_inf_eq_three_of_pgl h.toSec13Data hPGL)
  have hdA : d ∈ A := (Subgroup.mem_inf.mp hdAL).1
  have hdL : d ∈ L := (Subgroup.mem_inf.mp hdAL).2
  have hd3 : d ^ 3 = 1 := hA.2 d hdA
  obtain ⟨x, hxA, hx⟩ := exists_type_three h131 h hPGL
  have hxd : x * d = d * x := h.commute hxA hdA
  have hdN : d ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer hdL
  have hxN : x ∈ Subgroup.normalizer (L : Set G) := h.le_normalizer hxA
  have hSC : S ≤ Subgroup.centralizer ({c} : Set G) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hSc).trans
      (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr (Subgroup.mem_zpowers c)))
  have hSN : S ≤ Subgroup.normalizer (L : Set G) :=
    hSC.trans (centralizer_le_normalizer_L h.toSec14Std)
  have hpow : ∀ v ∈ S, ∃ m : ℕ, v ^ 2 ^ m = 1 := fun v hv => by
    obtain ⟨m, hm⟩ := hS2 ⟨v, hv⟩
    exact ⟨m, by simpa using congrArg Subtype.val hm⟩
  have hfix := hFix G A c L h (Or.inl hPGL) (Subgroup.zpowers d) (by rw [hALd])
    (card_zpowers_eq_three hd3 hd1) (S ⊓ L) ⟨inf_le_right,
      (isPiSubgroup_piOf_iff Nat.prime_two _).mpr (hS2.to_le inf_le_left),
      le_normalizer_inf hAS h.le_normalizer⟩
  rw [inSubgroup, hθL, Subgroup.map_bot] at hfix
  have hSd : ∀ s ∈ S, s * d = d * s := by
    intro s hs
    set v := s * d * s⁻¹ * d⁻¹ with hv
    have hvS : v ∈ S := by
      have h1 : d * s⁻¹ * d⁻¹ ∈ S :=
        (Subgroup.mem_normalizer_iff.mp (hAS hdA) s⁻¹).mp (S.inv_mem hs)
      rw [hv, show s * d * s⁻¹ * d⁻¹ = s * (d * s⁻¹ * d⁻¹) by group]
      exact S.mul_mem hs h1
    have hvL : v ∈ L := L.mul_mem ((Subgroup.mem_normalizer_iff.mp (hSN hs) d).mp hdL)
      (L.inv_mem hdL)
    have hvd : v * d = d * v := by
      have h1 := hfix (Subgroup.commutator_mem_commutator (Subgroup.mem_inf.mpr ⟨hvS, hvL⟩)
        (Subgroup.mem_zpowers d))
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
      exact h1
    have hud : Commute (s * d * s⁻¹) d := by
      have h1 : s * d * s⁻¹ = v * d := by rw [hv]; group
      change s * d * s⁻¹ * d = d * (s * d * s⁻¹)
      rw [h1]
      calc v * d * d = (d * v) * d := by rw [hvd]
        _ = d * (v * d) := by group
    have hv3 : v ^ 3 = 1 := by
      have h1 : v = s * d * s⁻¹ * d⁻¹ := hv
      rw [h1, hud.inv_right.mul_pow, conj_pow, hd3, inv_pow, hd3]
      group
    obtain ⟨m, hm⟩ := hpow v hvS
    have hv1 : v = 1 := by
      have h1 : orderOf v ∣ 3 := orderOf_dvd_of_pow_eq_one hv3
      have h2 : orderOf v ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one hm
      exact orderOf_eq_one_iff.mp
        (Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow_right m (by norm_num)) h1 h2)
    have h1 : s * d * s⁻¹ = d := by rw [hv, mul_inv_eq_one] at hv1; exact hv1
    calc s * d = s * d * s⁻¹ * s := by group
      _ = d * s := by rw [h1]
  have hcomm : ∀ g ∈ L, ∀ k ∈ L, g ^ 2 = 1 → k ^ 2 = 1 → g * d = d * g → k * d = d * k →
      g * k = k * g := fun g hg k hk hg2 hk2 hgd hkd =>
    commute_of_ksl3PiType1Inv hθL hx hdL hd1 hd3 hxd hg hk hg2 hk2 hgd hkd
  set ρ : Subgroup.normalizer (L : Set G) →* MulAut (↥L ⧸ aschbacherSolvableCore 3 ↥L) :=
    (thetaQuotMulAut ↥L).comp L.normalizerMonoidHom with hρ
  have hρd : ρ ⟨d, hdN⟩ = MulAut.conj ((⟨d, hdL⟩ : ↥L) : ↥L ⧸ aschbacherSolvableCore 3 ↥L) :=
    act_eq_conj_of_mem hdL hdN
  obtain ⟨-, π, p, f, K, _, hK, hq, e, -, -, -, -⟩ := id hx
  have hq2 : 2 < p ^ f := Item138Proof.two_lt_of_mulEquiv
    (Sec6.isQuasisimple_of_mem_thetaComponentsAt hLc) hK hq e
  have hSx : ∀ s ∈ S, s * x = x * s := by
    intro s hs
    by_contra hsx
    set v := s * x * s⁻¹ * x⁻¹ with hv
    have hvS : v ∈ S := by
      have h1 : x * s⁻¹ * x⁻¹ ∈ S :=
        (Subgroup.mem_normalizer_iff.mp (hAS hxA) s⁻¹).mp (S.inv_mem hs)
      rw [hv, show s * x * s⁻¹ * x⁻¹ = s * (x * s⁻¹ * x⁻¹) by group]
      exact S.mul_mem hs h1
    have hv1 : v ≠ 1 := by
      intro h1
      apply hsx
      rw [hv, mul_inv_eq_one] at h1
      calc s * x = s * x * s⁻¹ * s := by group
        _ = x * s := by rw [h1]
    have hvN : v ∈ Subgroup.normalizer (L : Set G) := hSN hvS
    have hsN : s ∈ Subgroup.normalizer (L : Set G) := hSN hs
    have hρv : ρ ⟨v, hvN⟩ = ρ ⟨s, hsN⟩ * ρ ⟨x, hxN⟩ * (ρ ⟨s, hsN⟩)⁻¹ * (ρ ⟨x, hxN⟩)⁻¹ := by
      rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
      rfl
    obtain ⟨m, hm⟩ := hpow v hvS
    have hρm : (ρ ⟨v, hvN⟩) ^ 2 ^ m = 1 := by
      rw [← map_pow]
      have : (⟨v, hvN⟩ : Subgroup.normalizer (L : Set G)) ^ 2 ^ m = 1 :=
        Subtype.ext (by simpa using hm)
      rw [this, map_one]
    obtain ⟨u, hu⟩ := hComm _ π p f K hK hq hq2 ⟨e⟩ (ρ ⟨s, hsN⟩) (ρ ⟨x, hxN⟩)
      ⟨m, hρv ▸ hρm⟩
    rw [← hρv] at hu
    have hu1 : u ≠ 1 := by
      rintro rfl
      rw [map_one] at hu
      have hvC := mem_centralizer_of_act_eq_one hθL hvN hu.symm
      have : v ∈ S ⊓ Subgroup.centralizer (L : Set G) := Subgroup.mem_inf.mpr ⟨hvS, hvC⟩
      rw [hSCL, Subgroup.mem_bot] at this
      exact hv1 this
    have hum : u ^ 2 ^ m = 1 := by
      apply eq_one_of_conj_eq_one hZ
      rw [map_pow, hu, hρm]
    have hvd : v * d = d * v := (hSd v hvS)
    have hud : u * ((⟨d, hdL⟩ : ↥L) : ↥L ⧸ aschbacherSolvableCore 3 ↥L) =
        ((⟨d, hdL⟩ : ↥L) : ↥L ⧸ aschbacherSolvableCore 3 ↥L) * u := by
      refine commute_of_conj_commute hZ ?_
      rw [hu, ← hρd, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext hvd
    obtain ⟨k, hk1, hk2⟩ := exists_pow_two_pow_ne_one hu1 m hum
    set w := u ^ 2 ^ k with hw
    have hwd : w * ((⟨d, hdL⟩ : ↥L) : ↥L ⧸ aschbacherSolvableCore 3 ↥L) =
        ((⟨d, hdL⟩ : ↥L) : ↥L ⧸ aschbacherSolvableCore 3 ↥L) * w :=
      ((Commute.pow_left hud (2 ^ k)) : _)
    obtain ⟨ℓ, hℓ⟩ := QuotientGroup.mk_surjective w
    have hℓ1 : (ℓ : G) ≠ 1 := by
      intro h1
      apply hk1
      rw [← hℓ, show ℓ = 1 from Subtype.ext h1, QuotientGroup.mk_one]
    have hℓ2 : (ℓ : G) ^ 2 = 1 := by
      have h1 : ℓ ^ 2 = 1 := eq_of_mk_eq hθL (by rw [QuotientGroup.mk_pow, hℓ, hk2,
        QuotientGroup.mk_one])
      simpa using congrArg Subtype.val h1
    have hℓd : (ℓ : G) * d = d * ℓ := by
      have h1 : ℓ * ⟨d, hdL⟩ = ⟨d, hdL⟩ * ℓ := eq_of_mk_eq hθL (by
        rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, hℓ]
        exact hwd)
      exact congrArg Subtype.val h1
    exact not_odd_thetaCen_of_involution h hALd hcomm ℓ.2 hℓ1 hℓ2 hℓd hθ
  have hdc : d ∉ Subgroup.zpowers c := by
    intro hdc'
    apply hcL
    have hzd := zpowers_eq_of_mem_of_ne_one h.card_zpowers hdc' hd1
    exact (Subgroup.zpowers_le.mpr hdL) (hzd ▸ Subgroup.mem_zpowers c)
  have hB : Subgroup.zpowers c ⊔ (A ⊓ L) = Subgroup.zpowers c ⊔ Subgroup.zpowers d := by
    rw [hALd]
  have hB9 : Nat.card (Subgroup.zpowers c ⊔ Subgroup.zpowers d : Subgroup G) = 9 :=
    card_sup_eq_nine hA hA27 hcA hdA hc1 hdc
  have hBhyp : IsHyperplane A (Subgroup.zpowers c ⊔ Subgroup.zpowers d) :=
    ⟨sup_le (Subgroup.zpowers_le.mpr hcA) (Subgroup.zpowers_le.mpr hdA), by rw [hA27, hB9]⟩
  have hxB : x ∉ Subgroup.zpowers c ⊔ Subgroup.zpowers d := by
    intro hxB
    obtain ⟨i, j, hij⟩ := exists_zpow_mul_of_mem_sup (h.commute hcA hdA) hxB
    have hcC : c ∈ Subgroup.centralizer (L : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      exact Subgroup.mem_centralizer_singleton_iff.mp (h.le_centralizer hl)
    have hcN : c ∈ Subgroup.normalizer (L : Set G) := Subgroup.centralizer_le_normalizer _ hcC
    have hρc : ρ ⟨c, hcN⟩ = 1 := by
      ext y
      induction y using QuotientGroup.induction_on with
      | H y =>
        rw [MulAut.one_apply]
        change thetaQuotMulAut ↥L (L.normalizerMonoidHom ⟨c, hcN⟩) _ = _
        rw [thetaQuotMulAut_mk]
        congr 1
        apply Subtype.ext
        rw [normalizerMonoidHom_apply_coe]
        have := Subgroup.mem_centralizer_iff.mp hcC (y : G) y.2
        calc c * (y : G) * c⁻¹ = (y : G) * c * c⁻¹ := by rw [this]
          _ = y := by group
    have hρx : ρ ⟨x, hxN⟩ = MulAut.conj
        (((⟨d, hdL⟩ : ↥L) : ↥L ⧸ aschbacherSolvableCore 3 ↥L) ^ j) := by
      have h1 : (⟨x, hxN⟩ : Subgroup.normalizer (L : Set G)) = ⟨c, hcN⟩ ^ i * ⟨d, hdN⟩ ^ j :=
        Subtype.ext (by simp [hij])
      rw [h1, map_mul, map_zpow, map_zpow, hρc, one_zpow, one_mul, hρd, map_zpow]
    exact not_inner_of_inducesTypeOn_three hLc hx hxN _ hρx
  have hAle : A ≤ Subgroup.zpowers x ⊔ (Subgroup.zpowers c ⊔ Subgroup.zpowers d) :=
    le_zpowers_sup_of_not_mem hBhyp hxA hxB
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.le_centralizer_iff]
  refine hAle.trans (sup_le (Subgroup.zpowers_le.mpr ?_) (sup_le (Subgroup.zpowers_le.mpr ?_)
    (Subgroup.zpowers_le.mpr ?_)))
  · rw [Subgroup.mem_centralizer_iff]
    intro s hs
    exact hSx s hs
  · rw [Subgroup.mem_centralizer_iff]
    intro s hs
    exact Subgroup.mem_centralizer_singleton_iff.mp (hSC hs)
  · rw [Subgroup.mem_centralizer_iff]
    intro s hs
    exact hSd s hs

theorem step1616Fix_of_items (h1612 : Step1612) (h131 : Item131) (h138 : Item138N)
    : Step1616Fix :=
  step1616Fix_of h1612 h131 (ks1613Fix_of h131 h138)

theorem step1616Fix_of_steps (h1612 : Step1612) (h131 : Item131) (h138 : Item138N) :
    Step1616Fix :=
  step1616Fix_of_items h1612 h131 h138

end Item1616Fix

end CFSG.RankThree.PartTwo.Sec16
