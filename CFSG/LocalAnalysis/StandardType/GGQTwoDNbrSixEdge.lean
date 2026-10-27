module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDNbrSixFrame
public import CFSG.LocalAnalysis.StandardType.GGNsq2RankOne
public import CFSG.LocalAnalysis.StandardType.GGQTwoDShared
public import Certificates.Certificate3143
import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitRankTwo
import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitBlock
import CFSG.LocalAnalysis.StandardType.GGQTwoDL1Edge
import CFSG.LocalAnalysis.StandardType.GGNsq2U62
import CFSG.ClassicalGroups.Unitary.SUThreeTwoDiagHom
import CFSG.LocalAnalysis.StandardType.GGQTwoDCoxEvenOrbit
import CFSG.LocalAnalysis.StandardType.GGQTwoDSlConj
import CFSG.LocalAnalysis.StandardType.GGNsq2Main
import CFSG.LocalAnalysis.StandardType.GGNsq2QuotCover
import CFSG.LocalAnalysis.StandardType.GGQTwoDNbrSixGen
import CFSG.LocalAnalysis.StandardType.GGQTwoDL1UOdd
import CFSG.LocalAnalysis.StandardType.GGQTwoDL1BaseU
import CFSG.LocalAnalysis.StandardType.GGQTwoDL1Lift
import CFSG.LocalAnalysis.StandardType.GGLinearFusionSLCent
import CFSG.LocalAnalysis.StandardType.GGQTwoDNbrDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly

namespace NsQuot

variable {G : Type} [Group G] [Finite G] {Q : Type} [Group Q]
variable {p : ℕ} {N : Subgroup G} {f : ↥N →* Q} {L Bs Z : Subgroup G}

theorem Datum.img_inf (hD : Datum p N f L Bs Z) {U V : Subgroup G} (hU : U ≤ Bs) (hV : V ≤ Bs) :
    img N f (U ⊓ V) = img N f U ⊓ img N f V := by
  apply le_antisymm
  · exact le_inf (img_mono inf_le_left) (img_mono inf_le_right)
  · intro q hq
    obtain ⟨u, huU, rfl⟩ := mem_img.1 (Subgroup.mem_inf.1 hq).1
    obtain ⟨v, hvV, hvu⟩ := mem_img.1 (Subgroup.mem_inf.1 hq).2
    have hinj := hD.injOn (U := Bs) le_rfl
    have huv : v = u := by
      have h := @hinj ⟨v, Subgroup.mem_subgroupOf.mpr (hV hvV)⟩
        ⟨u, Subgroup.mem_subgroupOf.mpr (hU huU)⟩ hvu
      exact congrArg (fun w : ↥(Bs.subgroupOf N) => (w : ↥N)) h
    rw [huv] at hvV
    exact mem_img.2 ⟨u, Subgroup.mem_inf.2 ⟨huU, hvV⟩, rfl⟩

theorem Datum.img_rankTwoIn (hD : Datum p N f L Bs Z) {r r' : MulAut ↥Bs}
    (hfix : ∀ z ∈ Z, (∀ h ∈ ggHyperplane Bs r ⊓ ggHyperplane Bs r', h * z = z * h) → z = 1) :
    img N f (QTwo.ggRankTwoIn L Bs r r') =
      QTwo.ggRankTwoIn (img N f L) (img N f Bs) (MulAut.congr hD.tau r)
        (MulAut.congr hD.tau r') := by
  have hH : ggHyperplane Bs r ⊓ ggHyperplane Bs r' ≤ Bs :=
    inf_le_left.trans (Subgroup.map_subtype_le _)
  unfold QTwo.ggRankTwoIn
  rw [hD.hyperplane_img r, hD.hyperplane_img r',
    ← hD.img_inf (U := ggHyperplane Bs r) (V := ggHyperplane Bs r') (Subgroup.map_subtype_le _)
      (Subgroup.map_subtype_le _),
    ← hD.centralizer_img hH]
  exact hD.img_ggOTwoPrime (inf_le_left.trans hD.LN) (hD.injOn_centralizer hfix)

theorem Datum.card_rankTwoIn_img_le [Finite Q] (hD : Datum p N f L Bs Z) (r r' : MulAut ↥Bs) :
    Nat.card ↥(QTwo.ggRankTwoIn (img N f L) (img N f Bs) (MulAut.congr hD.tau r)
        (MulAut.congr hD.tau r')) ≤ Nat.card ↥(QTwo.ggRankTwoIn L Bs r r') := by
  have hH : ggHyperplane Bs r ⊓ ggHyperplane Bs r' ≤ Bs :=
    inf_le_left.trans (Subgroup.map_subtype_le _)
  set C : Subgroup G := L ⊓ Subgroup.centralizer
    ((ggHyperplane Bs r ⊓ ggHyperplane Bs r' : Subgroup G) : Set G) with hC
  have hCN : ggOTwoPrime C ≤ N := (ggOTwoPrime_le C).trans (inf_le_left.trans hD.LN)
  have himgH : img N f (ggHyperplane Bs r ⊓ ggHyperplane Bs r') =
      ggHyperplane (img N f Bs) (MulAut.congr hD.tau r) ⊓
        ggHyperplane (img N f Bs) (MulAut.congr hD.tau r') := by
    rw [hD.img_inf (U := ggHyperplane Bs r) (V := ggHyperplane Bs r')
      (Subgroup.map_subtype_le _) (Subgroup.map_subtype_le _), hD.hyperplane_img r,
      hD.hyperplane_img r']
  have hle : ggOTwoPrime (img N f C) ≤ img N f (ggOTwoPrime C) := by
    rw [ggOTwoPrime, Subgroup.closure_le]
    rintro q ⟨hq, k, hqk⟩
    obtain ⟨u, huC, rfl⟩ := mem_img.1 hq
    have hker : u ^ (2 ^ k) ∈ f.ker := by rw [MonoidHom.mem_ker, map_pow, hqk]
    obtain ⟨l, hl⟩ := hD.ker_two _ hker
    have hu : u ^ (2 ^ (k + l)) = 1 := by
      rw [pow_add, pow_mul]
      exact hl
    refine mem_img.2 ⟨u, Subgroup.subset_closure ⟨huC, k + l, ?_⟩, rfl⟩
    simpa using congrArg Subtype.val hu
  have hcard : Nat.card ↥(img N f (ggOTwoPrime C)) ≤ Nat.card ↥(ggOTwoPrime C) := by
    unfold img
    refine Nat.le_of_dvd Nat.card_pos (((ggOTwoPrime C).subgroupOf N).card_map_dvd f) |>.trans ?_
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCN).toEquiv).le
  unfold QTwo.ggRankTwoIn
  rw [← himgH, ← hD.centralizer_img hH, ← hC]
  exact (Subgroup.card_le_of_le hle).trans hcard

theorem Datum.odd_card_centralizer_img [Finite Q] (hD : Datum p N f L Bs Z)
    (hodd : Odd (Nat.card ↥(Subgroup.centralizer (Bs : Set G)))) :
    Odd (Nat.card ↥(Subgroup.centralizer (img N f Bs : Set Q))) := by
  have hle : Subgroup.centralizer (img N f Bs : Set Q) ≤
      img N f (Subgroup.centralizer (Bs : Set G)) := by
    intro q hq
    obtain ⟨n0, rfl⟩ := hD.surj q
    have hcomm : ∀ b : ↥N, (b : G) ∈ Bs → f b * f n0 = f n0 * f b := fun b hb =>
      (Subgroup.mem_centralizer_iff.1 hq) (f b) (mem_img.2 ⟨b, hb, rfl⟩)
    have hconj : ∀ b : ↥N, (b : G) ∈ Bs →
        ∃ b' : ↥N, (b' : G) ∈ Bs ∧ f b' = f (n0 * b * n0⁻¹) := fun b hb =>
      ⟨b, hb, by rw [map_mul, map_mul, map_inv, ← hcomm b hb]; group⟩
    obtain ⟨z, hz, hzN⟩ := hD.exists_normalizer_correction n0 hconj
    have hfz : f z = 1 := MonoidHom.mem_ker.1 hz
    refine mem_img.2 ⟨z⁻¹ * n0, ?_, by rw [map_mul, map_inv, hfz, inv_one, one_mul]⟩
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    have hbN : b ∈ N := hD.BsN hb
    have hwb : ((z⁻¹ * n0 : ↥N) : G) * b * ((z⁻¹ * n0 : ↥N) : G)⁻¹ ∈ Bs :=
      (Subgroup.mem_normalizer_iff.1 hzN b).1 hb
    have hf : f ⟨((z⁻¹ * n0 : ↥N) : G) * b * ((z⁻¹ * n0 : ↥N) : G)⁻¹, hD.BsN hwb⟩ =
        f ⟨b, hbN⟩ := by
      have e : (⟨((z⁻¹ * n0 : ↥N) : G) * b * ((z⁻¹ * n0 : ↥N) : G)⁻¹, hD.BsN hwb⟩ : ↥N) =
          (z⁻¹ * n0) * ⟨b, hbN⟩ * (z⁻¹ * n0)⁻¹ := rfl
      rw [e, map_mul, map_mul, map_inv, map_mul, map_inv, hfz, inv_one, one_mul,
        ← hcomm ⟨b, hbN⟩ hb]
      group
    have h := hD.injOn (U := Bs) le_rfl
      (a₁ := ⟨⟨_, hD.BsN hwb⟩, Subgroup.mem_subgroupOf.mpr hwb⟩)
      (a₂ := ⟨⟨b, hbN⟩, Subgroup.mem_subgroupOf.mpr hb⟩) hf
    have e2 : ((z⁻¹ * n0 : ↥N) : G) * b * ((z⁻¹ * n0 : ↥N) : G)⁻¹ = b :=
      congrArg (fun u : ↥(Bs.subgroupOf N) => ((u : ↥N) : G)) h
    calc b * ((z⁻¹ * n0 : ↥N) : G)
        = ((z⁻¹ * n0 : ↥N) : G) * b * ((z⁻¹ * n0 : ↥N) : G)⁻¹ * ((z⁻¹ * n0 : ↥N) : G) := by
          rw [e2]
      _ = ((z⁻¹ * n0 : ↥N) : G) * b := by group
  refine Odd.of_dvd_nat hodd ((Subgroup.card_dvd_of_le hle).trans ?_)
  refine ((((Subgroup.centralizer (Bs : Set G)).subgroupOf N).card_map_dvd f)).trans ?_
  rw [← Subgroup.card_map_of_injective (f := N.subtype) Subtype.val_injective,
    Subgroup.subgroupOf_map_subtype]
  exact Subgroup.card_dvd_of_le inf_le_left

end NsQuot

namespace QTwo

open CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace GGQTwoDNbrSixFrame

variable {G : Type} [Group G] [Finite G] {B Bs X : Subgroup G} {z : Additive ↥Bs ≃+ DVec 6}

theorem mem_hyperplane_iff (Φ : GGQTwoDNbrSixFrame B Bs X z) (i j : Fin 6) (s : ↥Bs) :
    (s : G) ∈ ggHyperplane Bs ((Φ.φ₀ (Equiv.swap i j) : ↥(ggAutomizer X Bs)) : MulAut ↥Bs) ↔
      Φ.P (z (Additive.ofMul s)) i = Φ.P (z (Additive.ofMul s)) j := by
  have hfix : (s : G) ∈ ggHyperplane Bs
      ((Φ.φ₀ (Equiv.swap i j) : ↥(ggAutomizer X Bs)) : MulAut ↥Bs) ↔
      ((Φ.φ₀ (Equiv.swap i j) : ↥(ggAutomizer X Bs)) : MulAut ↥Bs) s = s := by
    constructor
    · rintro ⟨s', hs', hss'⟩
      obtain rfl : s' = s := Subtype.ext hss'
      exact hs'
    · intro h
      exact ⟨s, h, rfl⟩
  rw [hfix]
  constructor
  · intro h
    have h' := Φ.P_equivariant (Equiv.swap i j) s
    rw [h] at h'
    have hi := congrFun h' i
    rwa [dPerm_apply_apply, Equiv.symm_swap, Equiv.swap_apply_left] at hi
  · intro h
    apply Additive.ofMul.injective
    apply z.injective
    apply Φ.P.injective
    rw [Φ.P_equivariant]
    funext k
    rw [dPerm_apply_apply, Equiv.symm_swap]
    rcases eq_or_ne k i with rfl | hki
    · rw [Equiv.swap_apply_left]
      exact h.symm
    rcases eq_or_ne k j with rfl | hkj
    · rw [Equiv.swap_apply_right]
      exact h
    · rw [Equiv.swap_apply_of_ne_of_ne hki hkj]

@[expose] def eqSub (Φ : GGQTwoDNbrSixFrame B Bs X z) (T : Finset (Fin 6)) : Subgroup G :=
  Bs ⊓ ⨅ i ∈ T, ⨅ j ∈ T,
    ggHyperplane Bs ((Φ.φ₀ (Equiv.swap i j) : ↥(ggAutomizer X Bs)) : MulAut ↥Bs)

theorem eqSub_le (Φ : GGQTwoDNbrSixFrame B Bs X z) (T : Finset (Fin 6)) : Φ.eqSub T ≤ Bs :=
  inf_le_left

theorem mem_eqSub (Φ : GGQTwoDNbrSixFrame B Bs X z) (T : Finset (Fin 6)) (s : ↥Bs) :
    (s : G) ∈ Φ.eqSub T ↔
      ∀ i ∈ T, ∀ j ∈ T, Φ.P (z (Additive.ofMul s)) i = Φ.P (z (Additive.ofMul s)) j := by
  simp only [eqSub, Subgroup.mem_inf, Subgroup.mem_iInf, SetLike.coe_mem, true_and]
  exact forall₂_congr fun i _ => forall₂_congr fun j _ => Φ.mem_hyperplane_iff i j s

theorem eqSub_triple (Φ : GGQTwoDNbrSixFrame B Bs X z) (a b c : Fin 6) :
    Φ.eqSub {a, b, c} =
      ggHyperplane Bs ((Φ.φ₀ (Equiv.swap a b) : ↥(ggAutomizer X Bs)) : MulAut ↥Bs) ⊓
        ggHyperplane Bs ((Φ.φ₀ (Equiv.swap b c) : ↥(ggAutomizer X Bs)) : MulAut ↥Bs) := by
  ext g
  constructor
  · intro hg
    obtain ⟨s, rfl⟩ : ∃ s : ↥Bs, (s : G) = g := ⟨⟨g, Φ.eqSub_le _ hg⟩, rfl⟩
    have h := (Φ.mem_eqSub _ s).1 hg
    exact Subgroup.mem_inf.2 ⟨(Φ.mem_hyperplane_iff a b s).2 (h a (by simp) b (by simp)),
      (Φ.mem_hyperplane_iff b c s).2 (h b (by simp) c (by simp))⟩
  · intro hg
    obtain ⟨hab, hbc⟩ := Subgroup.mem_inf.1 hg
    obtain ⟨s, rfl⟩ : ∃ s : ↥Bs, (s : G) = g :=
      ⟨⟨g, Subgroup.map_subtype_le _ hab⟩, rfl⟩
    have h1 := (Φ.mem_hyperplane_iff a b s).1 hab
    have h2 := (Φ.mem_hyperplane_iff b c s).1 hbc
    refine (Φ.mem_eqSub _ s).2 fun i hi j hj => ?_
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj
    rcases hi with rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl <;> simp only [h1, h2]

@[expose] noncomputable def edge (Φ : GGQTwoDNbrSixFrame B Bs X z) (T : Finset (Fin 6)) :
    Subgroup G :=
  ggOTwoPrime (X ⊓ Subgroup.centralizer (Φ.eqSub T : Set G))

theorem edge_le (Φ : GGQTwoDNbrSixFrame B Bs X z) (T : Finset (Fin 6)) : Φ.edge T ≤ X :=
  (ggOTwoPrime_le _).trans inf_le_left

theorem edge_triple (Φ : GGQTwoDNbrSixFrame B Bs X z) (a b c : Fin 6) :
    Φ.edge {a, b, c} = ggRankTwoIn X Bs
      ((Φ.φ₀ (Equiv.swap a b) : ↥(ggAutomizer X Bs)) : MulAut ↥Bs)
      ((Φ.φ₀ (Equiv.swap b c) : ↥(ggAutomizer X Bs)) : MulAut ↥Bs) := by
  rw [edge, Φ.eqSub_triple]
  rfl

@[expose] noncomputable def ambEdge (Φ : GGQTwoDNbrSixFrame B Bs X z) (T : Finset (Fin 6)) :
    Subgroup G :=
  ggOTwoPrime (Subgroup.centralizer (Φ.eqSub T : Set G))

theorem ambEdge_triple (Φ : GGQTwoDNbrSixFrame B Bs X z) (a b c : Fin 6) :
    Φ.ambEdge {a, b, c} = ggRankTwo Bs
      ((Φ.φ₀ (Equiv.swap a b) : ↥(ggAutomizer X Bs)) : MulAut ↥Bs)
      ((Φ.φ₀ (Equiv.swap b c) : ↥(ggAutomizer X Bs)) : MulAut ↥Bs) := by
  rw [ambEdge, Φ.eqSub_triple]
  rfl

theorem refl_mul_ne (Φ : GGQTwoDNbrSixFrame B Bs X z) {a b c : Fin 6} (hab : a ≠ b)
    (hbc : b ≠ c) (hac : a ≠ c) :
    ((Φ.φ₀ (Equiv.swap a b) : ↥(ggAutomizer X Bs)) : MulAut ↥Bs) *
        ((Φ.φ₀ (Equiv.swap b c) : ↥(ggAutomizer X Bs)) : MulAut ↥Bs) ≠
      ((Φ.φ₀ (Equiv.swap b c) : ↥(ggAutomizer X Bs)) : MulAut ↥Bs) *
        ((Φ.φ₀ (Equiv.swap a b) : ↥(ggAutomizer X Bs)) : MulAut ↥Bs) := by
  intro h
  have h' : Φ.φ₀ (Equiv.swap a b * Equiv.swap b c) = Φ.φ₀ (Equiv.swap b c * Equiv.swap a b) := by
    rw [map_mul, map_mul]
    exact Subtype.ext h
  have ha := congrArg (fun σ : Equiv.Perm (Fin 6) => σ a) (Φ.φ₀_injective h')
  simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hab hac, Equiv.swap_apply_left]
    at ha
  exact hbc ha

theorem congr_tau_swap (Φ : GGQTwoDNbrSixFrame B Bs X z) (i j : Fin 6)
    (q : ↥(NsQuot.img _ Φ.f Bs)) :
    ((MulAut.congr Φ.datum.tau ((Φ.φ₀ (Equiv.swap i j) : ↥(ggAutomizer X Bs)) : MulAut ↥Bs) q :
        ↥(NsQuot.img _ Φ.f Bs)) : Φ.Q) =
      Φ.ψ (ggPermSU (Equiv.swap i j)) * q * (Φ.ψ (ggPermSU (Equiv.swap i j)))⁻¹ := by
  obtain ⟨s, rfl⟩ := Φ.datum.tau.surjective q
  rw [congr_apply_tau, Φ.datum.tau_apply, Φ.datum.tau_apply, Φ.perm (Equiv.swap i j) s,
    Equiv.swap_inv]

section Edges

theorem twoCentral_fix (Φ : GGQTwoDNbrSixFrame B Bs X z) {T : Finset (Fin 6)} {k : Fin 6}
    (hk : k ∉ T) : ∀ w ∈ twoCentral X, (∀ h ∈ Φ.eqSub T, h * w = w * h) → w = 1 := by
  classical
  intro w hw hcw
  have hD := Φ.datum
  set s₀ : ↥Bs := Additive.toMul (z.symm (Φ.P.symm (dBasis 6 k))) with hs₀
  have hv : Φ.P (z (Additive.ofMul s₀)) = dBasis 6 k := by
    rw [hs₀, ofMul_toMul, AddEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  have hs₀T : (s₀ : G) ∈ Φ.eqSub T := by
    refine (Φ.mem_eqSub T s₀).2 fun i hi j hj => ?_
    have hik : i ≠ k := fun h => hk (h ▸ hi)
    have hjk : j ≠ k := fun h => hk (h ▸ hj)
    rw [hv, Sl.dBasis_apply, Sl.dBasis_apply, if_neg hik, if_neg hjk]
  set c : Fin 6 → Φ.Kˣ := fun i => Φ.ω ^ (Φ.P (z (Additive.ofMul s₀)) i).val with hc
  have hci : ∀ i, c i = if i = k then Φ.ω else 1 := by
    intro i
    rw [hc]
    simp only [hv, Sl.dBasis_apply]
    split_ifs
    · rw [show (1 : ZMod 3).val = 1 from rfl, pow_one]
    · rw [show (0 : ZMod 3).val = 0 from rfl, pow_zero]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hunit : ggIsUnitaryMat (p := 2) (f := 1) (qTwoChartTwoThree_diag c) :=
    CFSG.ClassicalGroups.Unitary.SUThreeTwoDiag.conjTr_diagGL_mul_self Φ.card_K c
  have hdet : Matrix.GeneralLinearGroup.det (qTwoChartTwoThree_diag c) ≠ 1 := by
    intro h
    have h1 := congrArg Units.val h
    rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one] at h1
    change Matrix.det (Matrix.diagonal fun i => ((c i : Φ.Kˣ) : Φ.K)) = 1 at h1
    rw [Matrix.det_diagonal, Finset.prod_eq_single k
      (fun i _ hik => by rw [hci, if_neg hik, Units.val_one])
      (fun h => absurd (Finset.mem_univ k) h), hci, if_pos rfl, Units.val_eq_one] at h1
    have h3 := Φ.ω_order
    rw [h1, orderOf_one] at h3
    exact absurd h3 (by norm_num)
  have hb0 : (s₀ : G) ∈ Bs := s₀.2
  let σX : MulAut ↥X := X.normalizerMonoidHom ⟨(s₀ : G), hD.BsN hb0⟩
  let τX : MulAut ↥(NsQuot.img _ Φ.f X) := (NsQuot.img _ Φ.f X).normalizerMonoidHom
    ⟨Φ.f ⟨(s₀ : G), hD.BsN hb0⟩, hD.f_mem_normalizer_img hD.BsN hb0⟩
  let ψ₀ : Su Φ.K 2 1 6 →* ↥(NsQuot.img _ Φ.f X) := Φ.ψ.codRestrict _ fun u => by
    rw [← Φ.range]
    exact MonoidHom.mem_range.mpr ⟨u, rfl⟩
  have hψ₀ : Function.Surjective ψ₀ := by
    intro q
    have hq : (q : Φ.Q) ∈ Φ.ψ.range := by
      rw [Φ.range]
      exact q.2
    obtain ⟨u, hu⟩ := MonoidHom.mem_range.mp hq
    exact ⟨u, Subtype.ext hu⟩
  have hwX : w ∈ X := twoCentral_le X hw
  have hres := ggU62OuterDiagInput_holds Φ.K (by rw [Φ.card_K]; norm_num) ↥X
    ↥(NsQuot.img _ Φ.f X) hD.fL ψ₀ σX τX (qTwoChartTwoThree_diag c) Φ.perfect hD.fL_surjective
    (fun u hu l' => Subgroup.mem_center_iff.1
      (hD.mem_center_of_mem ((hD.fL_eq_one_iff u).1 hu)) l')
    (fun u hu => by
      obtain ⟨m, hm⟩ := hD.Z2 _ ((hD.fL_eq_one_iff u).1 hu)
      exact ⟨m, Subtype.ext (by simpa using hm)⟩)
    hψ₀
    (fun s hs => Φ.hyp.ker (by
      rw [MonoidHom.mem_ker] at hs ⊢
      exact congrArg Subtype.val hs))
    (fun l => Subtype.ext (by
      have e : (⟨((σX l : ↥X) : G), hD.LN (σX l).2⟩ : ↥(Subgroup.normalizer (X : Set G))) =
          ⟨(s₀ : G), hD.BsN hb0⟩ * ⟨(l : G), hD.LN l.2⟩ * ⟨(s₀ : G), hD.BsN hb0⟩⁻¹ := rfl
      change Φ.f ⟨((σX l : ↥X) : G), hD.LN (σX l).2⟩ =
        Φ.f ⟨(s₀ : G), hD.BsN hb0⟩ * Φ.f ⟨(l : G), hD.LN l.2⟩ * (Φ.f ⟨(s₀ : G), hD.BsN hb0⟩)⁻¹
      rw [e, map_mul, map_mul, map_inv]))
    hunit hdet
    (fun u => by
      obtain ⟨u', hu', hψu'⟩ := Φ.induces s₀ (hD.BsN hb0) u
      exact ⟨u', hu', Subtype.ext hψu'.symm⟩)
    ⟨w, hwX⟩ ((hD.fL_eq_one_iff _).2 hw) (Subtype.ext (by
      show (s₀ : G) * w * (s₀ : G)⁻¹ = w
      rw [mul_inv_eq_iff_eq_mul]
      exact hcw _ hs₀T))
  exact congrArg Subtype.val hres

theorem twoCentral_fix_triple (Φ : GGQTwoDNbrSixFrame B Bs X z) (a b c : Fin 6) :
    ∀ w ∈ twoCentral X,
      (∀ h ∈ ggHyperplane Bs ((Φ.φ₀ (Equiv.swap a b) : ↥(ggAutomizer X Bs)) : MulAut ↥Bs) ⊓
        ggHyperplane Bs ((Φ.φ₀ (Equiv.swap b c) : ↥(ggAutomizer X Bs)) : MulAut ↥Bs),
          h * w = w * h) → w = 1 := by
  obtain ⟨k, -, hk⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({a, b, c} : Finset (Fin 6))) (t := Finset.univ)
    (by rw [Finset.card_univ, Fintype.card_fin]; exact Finset.card_le_three.trans_lt (by norm_num))
  rw [← Φ.eqSub_triple]
  exact Φ.twoCentral_fix hk

theorem img_edge_triple (Φ : GGQTwoDNbrSixFrame B Bs X z) {a b c : Fin 6} (hab : a ≠ b)
    (hbc : b ≠ c) (hac : a ≠ c) :
    NsQuot.img _ Φ.f (Φ.edge {a, b, c}) = (coordBlockSU Φ.K 2 1 {a, b, c}).map Φ.ψ := by
  rw [edge_triple, Φ.datum.img_rankTwoIn (Φ.twoCentral_fix_triple a b c), ← Φ.range]
  exact ggQTwoDUnit_rankTwoIn_eq Φ.hyp Φ.card_K Φ.diag hab hbc hac (Φ.congr_tau_swap a b)
    (Φ.congr_tau_swap b c)

theorem card_ambEdge_triple_le (Φ : GGQTwoDNbrSixFrame B Bs X z)
    (hodd : Odd (Nat.card ↥(Subgroup.centralizer (Bs : Set G))))
    {a b c : Fin 6} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (hN : Subgroup.centralizer (Φ.eqSub {a, b, c} : Set G) ≤
      Subgroup.normalizer (X : Set G)) :
    Nat.card ↥(Φ.ambEdge {a, b, c}) ≤ 216 := by
  have hD := Φ.datum
  set r := ((Φ.φ₀ (Equiv.swap a b) : ↥(ggAutomizer X Bs)) : MulAut ↥Bs) with hr_def
  set r' := ((Φ.φ₀ (Equiv.swap b c) : ↥(ggAutomizer X Bs)) : MulAut ↥Bs) with hr'_def
  set H : Subgroup G := ggHyperplane Bs r ⊓ ggHyperplane Bs r' with hH
  have hCN : Subgroup.centralizer (H : Set G) ≤ Subgroup.normalizer (X : Set G) := by
    rw [hH, ← Φ.eqSub_triple]
    exact hN
  have hfix := Φ.twoCentral_fix_triple a b c
  have hinj : Function.Injective fun u : ↥((Subgroup.centralizer (H : Set G)).subgroupOf
      (Subgroup.normalizer (X : Set G))) => Φ.f (u : ↥(Subgroup.normalizer (X : Set G))) := by
    intro u₁ u₂ h12
    have hk : (u₁ : ↥(Subgroup.normalizer (X : Set G)))⁻¹ * u₂ ∈ Φ.f.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv]
      exact inv_mul_eq_one.2 h12
    have hZ := (hD.mem_ker_iff _).1 hk
    have hc₁ := Subgroup.mem_subgroupOf.1 u₁.2
    have hc₂ := Subgroup.mem_subgroupOf.1 u₂.2
    have h1 := hfix _ hZ fun h hh => by
      have e₁ := (Subgroup.mem_centralizer_iff.1 hc₁) h hh
      have e₂ := (Subgroup.mem_centralizer_iff.1 hc₂) h hh
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      generalize ((u₁ : ↥(Subgroup.normalizer (X : Set G))) : G) = g₁ at e₁ ⊢
      generalize ((u₂ : ↥(Subgroup.normalizer (X : Set G))) : G) = g₂ at e₂ ⊢
      calc h * (g₁⁻¹ * g₂) = g₁⁻¹ * (g₁ * h) * g₁⁻¹ * g₂ := by group
        _ = g₁⁻¹ * (h * g₁) * g₁⁻¹ * g₂ := by rw [← e₁]
        _ = g₁⁻¹ * (h * g₂) := by group
        _ = g₁⁻¹ * (g₂ * h) := by rw [e₂]
        _ = g₁⁻¹ * g₂ * h := by group
    apply Subtype.ext
    apply Subtype.ext
    simpa [inv_mul_eq_one] using h1
  have hr := Φ.congr_tau_swap a b
  have hr' := Φ.congr_tau_swap b c
  have hfullQ : Nat.card ↥(NsQuot.img _ Φ.f Bs) = 3 ^ (6 - 1) *
      Nat.card ↥(NsQuot.img _ Φ.f Bs ⊓
        Subgroup.centralizer (NsQuot.img _ Φ.f X : Set Φ.Q)) := by
    rw [hD.card_img le_rfl, card_bs_of_module z, hD.cent Φ.perfect le_rfl, Φ.cent]
    norm_num
  rw [← Φ.range] at hfullQ
  have hnormal : ∀ q : Φ.Q, q ∈ Subgroup.normalizer (Φ.ψ.range : Set Φ.Q) := by
    intro q
    obtain ⟨n, rfl⟩ := hD.surj q
    rw [Φ.range, Subgroup.mem_normalizer_iff]
    intro w
    constructor
    · intro hw
      obtain ⟨u, hu, rfl⟩ := NsQuot.mem_img.1 hw
      refine NsQuot.mem_img.2 ⟨n * u * n⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
      exact (Subgroup.mem_normalizer_iff.1 n.2 _).1 hu
    · intro hw
      obtain ⟨u, hu, hut⟩ := NsQuot.mem_img.1 hw
      refine NsQuot.mem_img.2 ⟨n⁻¹ * u * n, ?_, ?_⟩
      · have h' := (Subgroup.mem_normalizer_iff.1 (inv_mem n.2) _).1 hu
        simpa using h'
      · rw [map_mul, map_mul, map_inv, hut]
        group
  have hoddQ := hD.odd_card_centralizer_img hodd
  have hoddC := QTwo.qtwoDL1_baseU_oddC hoddQ Φ.card_K Φ.hyp rfl Φ.diag hab hbc hac hr hr'
  have hin := QTwo.qtwoDL1_baseU_inner Φ.card_K Φ.hyp rfl Φ.diag hfullQ hab hbc hac hr hr'
  have hlift := QTwo.qtwoDL1_ggOTwoPrime_eq_of_inner hoddC
    fun t ht h2 => hin t ht (hnormal t) h2
  have hcardQ : Nat.card ↥(ggOTwoPrime (Subgroup.centralizer
      ((ggHyperplane (NsQuot.img _ Φ.f Bs) (MulAut.congr hD.tau r) ⊓
        ggHyperplane (NsQuot.img _ Φ.f Bs) (MulAut.congr hD.tau r') : Subgroup Φ.Q) :
          Set Φ.Q))) = 216 := by
    rw [hlift]
    change Nat.card ↥(ggRankTwoIn Φ.ψ.range (NsQuot.img _ Φ.f Bs) (MulAut.congr hD.tau r)
      (MulAut.congr hD.tau r')) = 216
    rw [ggQTwoDUnit_rankTwoIn_eq Φ.hyp Φ.card_K Φ.diag hab hbc hac hr hr']
    exact ggQTwoDUnit_card_map_coordBlockSU_three Φ.card_K Φ.ψ Φ.hyp.ker (by norm_num) hab hbc
      hac
  have himgH : NsQuot.img _ Φ.f H = ggHyperplane (NsQuot.img _ Φ.f Bs) (MulAut.congr hD.tau r) ⊓
      ggHyperplane (NsQuot.img _ Φ.f Bs) (MulAut.congr hD.tau r') := by
    rw [hH, hD.img_inf (U := ggHyperplane Bs r) (V := ggHyperplane Bs r')
      (Subgroup.map_subtype_le _) (Subgroup.map_subtype_le _), hD.hyperplane_img r,
      hD.hyperplane_img r']
  have himgle : NsQuot.img _ Φ.f (Subgroup.centralizer (H : Set G)) ≤
      Subgroup.centralizer ((NsQuot.img _ Φ.f H : Subgroup Φ.Q) : Set Φ.Q) := by
    intro q hq
    obtain ⟨u, hu, rfl⟩ := NsQuot.mem_img.1 hq
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    obtain ⟨v, hv, rfl⟩ := NsQuot.mem_img.1 hw
    rw [← map_mul, ← map_mul]
    exact congrArg Φ.f (Subtype.ext ((Subgroup.mem_centralizer_iff.1 hu) _ hv))
  rw [Φ.ambEdge_triple]
  change Nat.card ↥(ggOTwoPrime (Subgroup.centralizer (H : Set G))) ≤ 216
  rw [← hD.card_ggOTwoPrime_img hCN hinj, ← hcardQ, ← himgH]
  exact Subgroup.card_le_of_le (LinFusion.ggOTwoPrime_mono himgle)

theorem img_edge (Φ : GGQTwoDNbrSixFrame B Bs X z) {T : Finset (Fin 6)} (hT : T.card = 3) :
    NsQuot.img _ Φ.f (Φ.edge T) = (coordBlockSU Φ.K 2 1 T).map Φ.ψ := by
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.1 hT
  exact Φ.img_edge_triple hab hbc hac

theorem eq_iSup_edge (Φ : GGQTwoDNbrSixFrame B Bs X z) :
    X = ⨆ (T : Finset (Fin 6)) (_ : T.card = 3), Φ.edge T :=
  Φ.datum.eq_iSup_of_img_coordBlockSU Φ.perfect.commutator_eq_top Φ.card_K (by norm_num) Φ.ψ
    Φ.range Φ.edge (fun T _ => Φ.edge_le T) fun _ hT => Φ.img_edge hT

end Edges

end GGQTwoDNbrSixFrame

end QTwo

end CFSG.StandardType

end
