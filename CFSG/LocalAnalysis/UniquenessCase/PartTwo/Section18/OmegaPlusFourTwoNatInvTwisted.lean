module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.OmegaPlusFourModel
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.MultNatCoordsRestrict
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56Nat
public import CFSG.Quasithin.Background.SmithD321Ext
public import CFSG.GroupTheory.E3Params
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.EmptyFaithful.T1515C4Mod
public import CFSG.Quasithin.Vol2.Ch10SecD32A
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.Quasithin CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit
open CFSG.Quasithin.Vol2.Ch10.SecD (eq_of_mul_eq_mul_of_inf_eq_bot)
open scoped Pointwise Matrix

variable {W : Type} [CommGroup W] [Finite W]

theorem natOmegaPlus_invariant {X : Subgroup (MulAut W)} {I : Subgroup W} {n a : ℕ}
    (h : NatOmegaPlus X I ⊥ n a) : ∀ x ∈ X, ∀ v ∈ I, x v ∈ I := by
  obtain ⟨-, K, hF, hFin, -, π, hRV⟩ := h
  exact fun x hx => hRV.2.2.2.1 ⟨x, hx⟩

theorem exists_omegaModel_summand {X : Subgroup (MulAut W)} {I : Subgroup W}
    (h : NatOmegaPlus X I ⊥ 4 2) :
    ∃ (S : OmegaModel ↥I), Nat.card S.K = 4 ∧
      S.omega = (actOnSub (natOmegaPlus_invariant h)).range := by
  obtain ⟨-, K, hF, hFin, hcard, π, hRV⟩ := h
  obtain ⟨H', π', hH', -, hRV'⟩ := exists_realizesVia_restrict hRV
  have hNat : NatOmegaPlus H' ⊤ ⊥ 4 2 :=
    ⟨by norm_num, K, hF, hFin, hcard, π', hRV'⟩
  obtain ⟨S, hSω, hSK⟩ :=
    exists_omegaModel_of_natOmegaPlus (W := ↥I) (H := H') (a := 2) (by norm_num) hNat
  exact ⟨S, by rw [hSK]; norm_num, hSω.trans hH'⟩

private theorem decomp_exists_of_sup_eq_top {I J : Subgroup W} (hsup : I ⊔ J = ⊤) (v : W) :
    ∃ p : ↥I × ↥J, ((p.1 : W) * (p.2 : W)) = v := by
  obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup.1 (hsup ▸ Subgroup.mem_top v)
  exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), hab⟩

private noncomputable def decompOfSup {I J : Subgroup W} (hsup : I ⊔ J = ⊤) (v : W) : ↥I × ↥J :=
  Classical.choose (decomp_exists_of_sup_eq_top hsup v)

private theorem decompOfSup_spec {I J : Subgroup W} (hsup : I ⊔ J = ⊤) (v : W) :
    ((decompOfSup hsup v).1 : W) * ((decompOfSup hsup v).2 : W) = v :=
  Classical.choose_spec (decomp_exists_of_sup_eq_top hsup v)

private theorem decompOfSup_eq {I J : Subgroup W} (hinf : I ⊓ J = ⊥) (hsup : I ⊔ J = ⊤)
    {a : ↥I} {b : ↥J} {v : W} (h : ((a : W) * (b : W)) = v) : decompOfSup hsup v = (a, b) := by
  have hu := eq_of_mul_eq_mul_of_inf_eq_bot hinf a.2 (decompOfSup hsup v).1.2 b.2
    (decompOfSup hsup v).2.2 (h.trans (decompOfSup_spec hsup v).symm)
  exact Prod.ext (Subtype.ext hu.1.symm) (Subtype.ext hu.2.symm)

theorem card_fixV_eq_mul_of_preserves {I J : Subgroup W} (hinf : I ⊓ J = ⊥) (hsup : I ⊔ J = ⊤)
    {w : MulAut W} (hI : ∀ v ∈ I, w v ∈ I) (hJ : ∀ v ∈ J, w v ∈ J) :
    Nat.card ↥(fixV (Subgroup.zpowers w)) =
      Nat.card ↥(I ⊓ fixV (Subgroup.zpowers w)) *
        Nat.card ↥(J ⊓ fixV (Subgroup.zpowers w)) := by
  classical
  have hmem : ∀ v : W, v ∈ fixV (Subgroup.zpowers w) ↔ w v = v := fun v =>
    mem_fixV_zpowers_iff_apply
  have hdec : ∀ v : W, ∃ p : ↥I × ↥J, ((p.1 : W) * (p.2 : W)) = v := by
    intro v
    obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup.1 (hsup ▸ Subgroup.mem_top v)
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), hab⟩
  let p : W → ↥I × ↥J := fun v => Classical.choose (hdec v)
  have hp : ∀ v : W, ((p v).1 : W) * ((p v).2 : W) = v := fun v =>
    Classical.choose_spec (hdec v)
  have hp_eq : ∀ (a : ↥I) (b : ↥J) (v : W), ((a : W) * (b : W)) = v → p v = (a, b) := by
    intro a b v h
    have hu := eq_of_mul_eq_mul_of_inf_eq_bot hinf a.2 (p v).1.2 b.2 (p v).2.2
      (h.trans (hp v).symm)
    exact Prod.ext (Subtype.ext hu.1.symm) (Subtype.ext hu.2.symm)
  have hfix1 : ∀ v ∈ fixV (Subgroup.zpowers w), w ((p v).1 : W) = ((p v).1 : W) := by
    intro v hv
    have h2 : w ((p v).1 : W) * w ((p v).2 : W) =
        ((p v).1 : W) * ((p v).2 : W) := by
      rw [← map_mul, hp v, (hmem v).1 hv]
    exact (eq_of_mul_eq_mul_of_inf_eq_bot hinf (hI _ (p v).1.2) (p v).1.2 (hJ _ (p v).2.2)
      (p v).2.2 h2).1
  have hfix2 : ∀ v ∈ fixV (Subgroup.zpowers w), w ((p v).2 : W) = ((p v).2 : W) := by
    intro v hv
    have h2 : w ((p v).1 : W) * w ((p v).2 : W) =
        ((p v).1 : W) * ((p v).2 : W) := by
      rw [← map_mul, hp v, (hmem v).1 hv]
    exact (eq_of_mul_eq_mul_of_inf_eq_bot hinf (hI _ (p v).1.2) (p v).1.2 (hJ _ (p v).2.2)
      (p v).2.2 h2).2
  let F : ↥(fixV (Subgroup.zpowers w)) →
      ↥(I ⊓ fixV (Subgroup.zpowers w)) × ↥(J ⊓ fixV (Subgroup.zpowers w)) := fun v =>
    (⟨((p (v : W)).1 : W), (p (v : W)).1.2,
      (hmem ((p (v : W)).1 : W)).2 (hfix1 (v : W) v.2)⟩,
     ⟨((p (v : W)).2 : W), (p (v : W)).2.2,
      (hmem ((p (v : W)).2 : W)).2 (hfix2 (v : W) v.2)⟩)
  let G : ↥(I ⊓ fixV (Subgroup.zpowers w)) × ↥(J ⊓ fixV (Subgroup.zpowers w)) →
      ↥(fixV (Subgroup.zpowers w)) := fun q =>
    ⟨(q.1 : W) * (q.2 : W), (hmem ((q.1 : W) * (q.2 : W))).2 (by
      rw [map_mul, (hmem (q.1 : W)).1 q.1.2.2, (hmem (q.2 : W)).1 q.2.2.2])⟩
  have hFG : ∀ v : ↥(fixV (Subgroup.zpowers w)), G (F v) = v := by
    intro v
    exact Subtype.ext (hp (v : W))
  have hGF : ∀ q, F (G q) = q := by
    intro q
    have h2 : p ((q.1 : W) * (q.2 : W)) =
        (⟨(q.1 : W), q.1.2.1⟩, ⟨(q.2 : W), q.2.2.1⟩) :=
      hp_eq ⟨(q.1 : W), q.1.2.1⟩ ⟨(q.2 : W), q.2.2.1⟩ _ rfl
    have h3 : ((p ((q.1 : W) * (q.2 : W))).1 : W) = (q.1 : W) := by rw [h2]
    have h4 : ((p ((q.1 : W) * (q.2 : W))).2 : W) = (q.2 : W) := by rw [h2]
    exact Prod.ext (Subtype.ext h3) (Subtype.ext h4)
  have heq : Nat.card ↥(fixV (Subgroup.zpowers w)) = Nat.card
      (↥(I ⊓ fixV (Subgroup.zpowers w)) × ↥(J ⊓ fixV (Subgroup.zpowers w))) :=
    Nat.card_congr { toFun := F, invFun := G, left_inv := hFG, right_inv := hGF }
  rw [heq, Nat.card_prod]

theorem card_fixV_of_swap {I J : Subgroup W} (hinf : I ⊓ J = ⊥) (hsup : I ⊔ J = ⊤)
    {w : MulAut W} (hw2 : w ^ 2 = 1) (hIJ : I.map w.toMonoidHom = J) :
    Nat.card ↥(fixV (Subgroup.zpowers w)) = Nat.card ↥I := by
  classical
  have hw1 : w * w = 1 := by rwa [pow_two] at hw2
  have hww : ∀ x : W, w (w x) = x := by
    intro x
    have h1 : (w * w) x = (1 : MulAut W) x := by rw [hw1]
    simpa using h1
  have hJI : J.map w.toMonoidHom = I := by
    conv_lhs => rw [← hIJ]
    rw [Subgroup.map_map]
    have hcomp : w.toMonoidHom.comp w.toMonoidHom = ((w * w).toMonoidHom) := by
      ext x
      rfl
    rw [hcomp, hw1]
    exact Subgroup.map_id I
  have hmem : ∀ v : W, v ∈ fixV (Subgroup.zpowers w) ↔ w v = v := fun v =>
    mem_fixV_zpowers_iff_apply
  have hI : ∀ a : ↥I, w (a : W) ∈ J := by
    intro a
    have h : w (a : W) ∈ I.map w.toMonoidHom := Subgroup.mem_map_of_mem _ a.2
    rwa [hIJ] at h
  have hJ : ∀ b : ↥J, w (b : W) ∈ I := by
    intro b
    have h : w (b : W) ∈ J.map w.toMonoidHom := Subgroup.mem_map_of_mem _ b.2
    rwa [hJI] at h
  let F : ↥(fixV (Subgroup.zpowers w)) → ↥I := fun v =>
    ⟨((decompOfSup hsup (v : W)).1 : W), (decompOfSup hsup (v : W)).1.2⟩
  let G : ↥I → ↥(fixV (Subgroup.zpowers w)) := fun a =>
    ⟨(a : W) * w (a : W), (hmem _).2 (by rw [map_mul, hww, mul_comm])⟩
  have hFG : ∀ v, G (F v) = v := by
    intro v
    have hv : w (v : W) = (v : W) := (hmem _).1 v.2
    have hp := decompOfSup_spec hsup (v : W)
    have hkey : w ((decompOfSup hsup (v : W)).1 : W) * w ((decompOfSup hsup (v : W)).2 : W) =
        (v : W) := by
      rw [← map_mul, hp, hv]
    have hkey' : ((decompOfSup hsup (v : W)).1 : W) * ((decompOfSup hsup (v : W)).2 : W) =
        w ((decompOfSup hsup (v : W)).2 : W) * w ((decompOfSup hsup (v : W)).1 : W) := by
      calc ((decompOfSup hsup (v : W)).1 : W) * ((decompOfSup hsup (v : W)).2 : W)
          = (v : W) := hp
        _ = w ((decompOfSup hsup (v : W)).1 : W) * w ((decompOfSup hsup (v : W)).2 : W) :=
            hkey.symm
        _ = w ((decompOfSup hsup (v : W)).2 : W) * w ((decompOfSup hsup (v : W)).1 : W) :=
            mul_comm _ _
    have huniq := eq_of_mul_eq_mul_of_inf_eq_bot hinf (decompOfSup hsup (v : W)).1.2
      (hJ (decompOfSup hsup (v : W)).2) (decompOfSup hsup (v : W)).2.2
      (hI (decompOfSup hsup (v : W)).1) hkey'
    refine Subtype.ext ?_
    change ((decompOfSup hsup (v : W)).1 : W) * w ((decompOfSup hsup (v : W)).1 : W) = (v : W)
    rw [← huniq.2, hp]
  have hGF : ∀ a, F (G a) = a := by
    intro a
    have h2 : decompOfSup hsup ((a : W) * w (a : W)) = (a, ⟨w (a : W), hI a⟩) :=
      decompOfSup_eq hinf hsup rfl
    refine Subtype.ext ?_
    change ((decompOfSup hsup ((a : W) * w (a : W))).1 : W) = (a : W)
    rw [h2]
  exact Nat.card_congr { toFun := F, invFun := G, left_inv := hFG, right_inv := hGF }

theorem natCard_eq_mul_of_sup_eq_top {I J : Subgroup W} (hinf : I ⊓ J = ⊥) (hsup : I ⊔ J = ⊤) :
    Nat.card W = Nat.card ↥I * Nat.card ↥J := by
  have hdisj : Disjoint I J := by
    rw [disjoint_iff_inf_le, hinf]
  have hmul : (↑I * ↑J : Set W) = Set.univ := by
    ext v
    exact ⟨fun _ => Set.mem_univ v, fun _ => by
      obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup.1 (hsup ▸ Subgroup.mem_top v)
      exact Set.mem_mul.2 ⟨a, ha, b, hb, hab⟩⟩
  exact (Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisj hmul).card_mul.symm

theorem card_of_natOmegaPlus {X : Subgroup (MulAut W)} {I : Subgroup W}
    (h : NatOmegaPlus X I ⊥ 4 2) : Nat.card ↥I = 256 := by
  obtain ⟨-, K, hF, hFin, hcard, π, hRV⟩ := h
  obtain ⟨H', π', hH', -, hRV'⟩ := exists_realizesVia_restrict hRV
  have hNat : NatOmegaPlus H' ⊤ ⊥ 4 2 := ⟨by norm_num, K, hF, hFin, hcard, π', hRV'⟩
  obtain ⟨S, -, hSK⟩ :=
    exists_omegaModel_of_natOmegaPlus (W := ↥I) (H := H') (a := 2) (by norm_num) hNat
  rw [Nat.card_congr S.e.toEquiv, CFSG.Quasithin.H.card_stdMod, hSK]
  norm_num [Fintype.card_sum]

theorem card_fixV_of_mQuot_top {w : MulAut W} (hW : Nat.card W = 2 ^ 16)
    (hm : E3.mQuot ⊤ (fixV (Subgroup.zpowers w)) = 4) :
    Nat.card ↥(fixV (Subgroup.zpowers w)) = 2 ^ 12 := by
  have h1 : rkIdx (fixV (Subgroup.zpowers w)) = 4 := by
    rw [← CFSG.GroupTheory.mQuot_top_eq_rkIdx]
    exact hm
  unfold rkIdx at h1
  have hidx_dvd : (fixV (Subgroup.zpowers w)).index ∣ 2 ^ 16 := by
    rw [← hW]
    exact Subgroup.index_dvd_card _
  obtain ⟨k, hk_le, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hidx_dvd
  have hk4 : k = 4 := by
    have hpk : padicValNat 2 (2 ^ k) = k := padicValNat.prime_pow (p := 2) k
    rw [← hk] at hpk
    omega
  have hidx : (fixV (Subgroup.zpowers w)).index = 16 := by
    rw [hk, hk4]
    norm_num
  have hmul := (fixV (Subgroup.zpowers w)).card_mul_index
  rw [hidx, hW] at hmul
  omega

theorem isIrr_natOmegaPlus {X : Subgroup (MulAut W)} {I : Subgroup W}
    (h : NatOmegaPlus X I ⊥ 4 2) : CFSG.Quasithin.H.Pair.IsIrr X I := by
  classical
  obtain ⟨S, hSK, hSω⟩ := exists_omegaModel_summand h
  have h4 : 4 ≤ Nat.card S.K := by rw [hSK]
  have hIne : I ≠ ⊥ := by
    rintro rfl
    have hcard := card_of_natOmegaPlus h
    have h1 : Nat.card ↥(⊥ : Subgroup W) = 1 := by simp
    omega
  refine ⟨hIne, ?_⟩
  intro U hUI hUinv
  let V : AddSubgroup (OmI → S.K) :=
    Subgroup.toAddSubgroup' ((U.subgroupOf I).map S.e.toMonoidHom)
  have hV1 : ∀ v : OmI → S.K, v ∈ V ↔ Multiplicative.ofAdd v ∈
      (U.subgroupOf I).map S.e.toMonoidHom := fun v => Iff.rfl
  have hV : ∀ γ : ↥(StatedOmega (StatedQuadPlus 2 S.K)), ∀ v ∈ V,
      ((γ : GL OmI S.K) : Matrix OmI OmI S.K) *ᵥ v ∈ V := by
    intro γ v hv
    have hv' : Multiplicative.ofAdd v ∈ (U.subgroupOf I).map S.e.toMonoidHom := hv
    obtain ⟨u, hu, hue⟩ := Subgroup.mem_map.1 hv'
    have hmem : S.actHom γ ∈ S.omega := by
      show S.actHom γ ∈ (StatedOmega (StatedQuadPlus 2 S.K)).map S.actHom
      exact Subgroup.mem_map_of_mem _ γ.2
    rw [hSω] at hmem
    obtain ⟨x, hx⟩ := hmem
    have hxu : ((actOnSub (natOmegaPlus_invariant h) x u : ↥I) : W) ∈ U :=
      hUinv x x.2 ((u : ↥I) : W) hu
    refine Subgroup.mem_map.2 ⟨actOnSub (natOmegaPlus_invariant h) x u, hxu, ?_⟩
    have h1 : actOnSub (natOmegaPlus_invariant h) x u = (S.actHom γ) u := by rw [hx]
    rw [h1]
    have h2 : S.e.toMonoidHom ((S.actHom γ) u) =
        Multiplicative.ofAdd (S.vec ((S.actHom γ) u)) := rfl
    have hvu : S.vec u = v := congrArg Multiplicative.toAdd hue
    rw [h2, S.actHom_vec, hvu]
    rfl
  have hV' : ∀ γ ∈ StatedOmega (StatedQuadPlus 2 S.K), ∀ u ∈ V,
      ((γ : GL OmI S.K) : Matrix OmI OmI S.K) *ᵥ u ∈ V :=
    fun γ hγ => hV ⟨γ, hγ⟩
  rcases isNatIrr_statedOmegaPlus h4 V hV' with hVbot | hVtop
  · left
    rw [eq_bot_iff]
    intro v hv
    have h1 : (⟨v, hUI hv⟩ : ↥I) ∈ U.subgroupOf I := hv
    have h2 : S.vec (⟨v, hUI hv⟩ : ↥I) ∈ V :=
      Subgroup.mem_map_of_mem _ h1
    rw [hVbot] at h2
    have h3 : S.vec (⟨v, hUI hv⟩ : ↥I) = 0 := by simpa using h2
    have h4 : (⟨v, hUI hv⟩ : ↥I) = 1 := by
      apply S.vec_injective
      rw [h3, S.vec_one]
    simpa using congrArg Subtype.val h4
  · right
    apply le_antisymm hUI
    intro v hv
    have h2 : S.vec (⟨v, hv⟩ : ↥I) ∈ V := by
      rw [hVtop]
      exact AddSubgroup.mem_top _
    have h2' : S.e (⟨v, hv⟩ : ↥I) ∈ (U.subgroupOf I).map S.e.toMonoidHom := h2
    obtain ⟨u, hu, hue⟩ := Subgroup.mem_map.1 h2'
    have h3 : u = ⟨v, hv⟩ := S.e.injective hue
    rw [h3] at hu
    exact hu

@[expose] noncomputable def mulAutOnSub {V : Type} [CommGroup V] [Finite V] (g : MulAut V)
    {I : Subgroup V} (h : ∀ v ∈ I, g v ∈ I) : MulAut ↥I :=
  MulEquiv.ofBijective
    ({ toFun := fun v => ⟨g (v : V), h (v : V) v.2⟩
       map_one' := Subtype.ext (map_one g)
       map_mul' := fun a b => Subtype.ext (map_mul g (a : V) (b : V)) } : ↥I →* ↥I)
    ⟨fun a b hab => Subtype.ext (g.injective (congrArg Subtype.val hab)),
     Finite.surjective_of_injective
       (fun a b hab => Subtype.ext (g.injective (congrArg Subtype.val hab)))⟩

theorem mulAutOnSub_apply {V : Type} [CommGroup V] [Finite V] (g : MulAut V)
    {I : Subgroup V} (h : ∀ v ∈ I, g v ∈ I) (v : ↥I) :
    ((mulAutOnSub g h v : ↥I) : V) = g (v : V) := rfl

theorem conj_mulAutOnSub_actOnSub {X : Subgroup (MulAut W)} {I : Subgroup W}
    (hInv : ∀ x ∈ X, ∀ v ∈ I, x v ∈ I) {w : MulAut W}
    (hwN : w ∈ Subgroup.normalizer (X : Set (MulAut W)))
    (hpres : ∀ v ∈ I, w v ∈ I) (hpres' : ∀ v ∈ I, w⁻¹ v ∈ I) (x : ↥X) :
    mulAutOnSub w hpres * (actOnSub hInv x) * (mulAutOnSub w hpres)⁻¹ =
      actOnSub hInv (⟨w * (x : MulAut W) * w⁻¹,
        (Subgroup.mem_normalizer_iff.mp hwN (x : MulAut W)).mp x.2⟩ : ↥X) := by
  ext v
  have hginv : ((((mulAutOnSub w hpres)⁻¹) v : ↥I) : W) = w⁻¹ (v : W) := by
    have h1 : mulAutOnSub w hpres (((mulAutOnSub w hpres)⁻¹) v) = v := by simp
    have h2 := congrArg (fun u : ↥I => (u : W)) h1
    rw [mulAutOnSub_apply] at h2
    have h3 := congrArg (fun t : W => w⁻¹ t) h2
    simpa using h3
  have hgv : ∀ u : ↥I, ((mulAutOnSub w hpres u : ↥I) : W) = w (u : W) :=
    fun u => mulAutOnSub_apply w hpres u
  rw [MulAut.mul_apply, MulAut.mul_apply, hgv, actOnSub_apply, hginv, actOnSub_apply]
  rfl

theorem exists_reflection_of_preserving
    {X : Subgroup (MulAut W)} {I : Subgroup W} (h : NatOmegaPlus X I ⊥ 4 2)
    {w : MulAut W} (hwN : w ∈ Subgroup.normalizer (X : Set (MulAut W)))
    (hpres : ∀ v ∈ I, w v ∈ I) (hw2 : w ^ 2 = 1)
    (hc64 : Nat.card ↥(I ⊓ fixV (Subgroup.zpowers w)) = 64) :
    ∃ (S : OmegaModel ↥I) (evec : OmI → S.K),
      Nat.card S.K = 4 ∧
      S.omega = (actOnSub (natOmegaPlus_invariant h)).range ∧
      StatedQuadPlus 2 S.K evec ≠ 0 ∧
      (∀ (c : S.K) (v : ↥I),
        mulAutOnSub w hpres (S.smul c v) = S.smul c (mulAutOnSub w hpres v)) ∧
      (∀ v : ↥I, S.vec (mulAutOnSub w hpres v) =
        S.vec v + (polQ (S.vec v) evec / StatedQuadPlus 2 S.K evec) • evec) := by
  classical
  obtain ⟨S, hSK, hSω⟩ := exists_omegaModel_summand h
  set g := mulAutOnSub w hpres with hgdef
  have hgval : ∀ v : ↥I, ((g v : ↥I) : W) = w (v : W) := fun v => mulAutOnSub_apply w hpres v
  have hle : I.map w.toMonoidHom ≤ I := by
    rintro _ ⟨u, hu, rfl⟩
    exact hpres u hu
  have hcardmap : Nat.card ↥(I.map w.toMonoidHom) = Nat.card ↥I :=
    Subgroup.card_map_of_injective (MulEquiv.injective w)
  have hmapI : I.map w.toMonoidHom = I :=
    Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcardmap.symm)
  have hpres' : ∀ v ∈ I, w⁻¹ v ∈ I := by
    intro v hv
    have hv' : v ∈ I.map w.toMonoidHom := by rw [hmapI]; exact hv
    obtain ⟨u, hu, hue⟩ := Subgroup.mem_map.1 hv'
    rw [← hue]
    simpa using hu
  have hcard_eq : Nat.card ↥(I ⊓ fixV (Subgroup.zpowers w)) =
      Nat.card {v : ↥I // g v = v} := by
    refine Nat.card_congr ?_
    exact
      { toFun := fun v => ⟨⟨(v : W), v.2.1⟩, by
          apply Subtype.ext
          rw [hgval]
          exact mem_fixV_zpowers_iff_apply.1 v.2.2⟩
        invFun := fun v => ⟨(v.1 : W), v.1.2, by
          have h1 : w (v.1 : W) = (v.1 : W) := by
            rw [← hgval (v.1)]
            exact congrArg Subtype.val v.2
          exact mem_fixV_zpowers_iff_apply.2 h1⟩
        left_inv := fun v => Subtype.ext rfl
        right_inv := fun v => Subtype.ext rfl }
  have hginv_eq : g⁻¹ = mulAutOnSub w⁻¹ hpres' := by
    have h1 : g * mulAutOnSub w⁻¹ hpres' = 1 := by
      ext u
      show w (w⁻¹ ((u : ↥I) : W)) = ((u : ↥I) : W)
      simp
    calc g⁻¹ = g⁻¹ * 1 := (mul_one _).symm
      _ = g⁻¹ * (g * mulAutOnSub w⁻¹ hpres') := by rw [h1]
      _ = mulAutOnSub w⁻¹ hpres' := by rw [← mul_assoc, inv_mul_cancel, one_mul]
  have hgN : g ∈ Subgroup.normalizer (S.omega : Set (MulAut ↥I)) := by
    rw [hSω, Subgroup.mem_normalizer_iff_map_conj_eq]
    ext y
    constructor
    · intro hy
      obtain ⟨u, hu, huy⟩ := Subgroup.mem_map.1 hy
      obtain ⟨x, rfl⟩ := hu
      refine ⟨⟨w * (x : MulAut W) * w⁻¹,
        (Subgroup.mem_normalizer_iff.mp hwN (x : MulAut W)).mp x.2⟩, ?_⟩
      exact (conj_mulAutOnSub_actOnSub (natOmegaPlus_invariant h) hwN hpres hpres' x).symm.trans
        huy
    · intro hy
      obtain ⟨x, rfl⟩ := hy
      refine Subgroup.mem_map.2 ⟨MulAut.conj g⁻¹ (actOnSub (natOmegaPlus_invariant h) x),
        ?_, ?_⟩
      · refine ⟨⟨w⁻¹ * (x : MulAut W) * (w⁻¹)⁻¹,
          (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hwN) (x : MulAut W)).mp x.2⟩, ?_⟩
        rw [hginv_eq]
        exact (conj_mulAutOnSub_actOnSub (natOmegaPlus_invariant h)
          (Subgroup.inv_mem _ hwN) hpres' hpres x).symm
      · show (MulAut.conj g) ((MulAut.conj g⁻¹) (actOnSub (natOmegaPlus_invariant h) x)) =
          actOnSub (natOmegaPlus_invariant h) x
        simp only [MulAut.conj_apply]
        group

  have hww : ∀ x : W, w (w x) = x := by
    intro x
    have h1 : (w * w) x = (1 : MulAut W) x := by
      rw [show w * w = 1 from by rwa [pow_two] at hw2]
    simpa using h1
  have hg2 : g * g = 1 := by
    ext u
    show w (w ((u : ↥I) : W)) = ((u : ↥I) : W)
    rw [hww]
  have hfixcard : Nat.card S.K ^ 2 < Nat.card {v : ↥I // g v = v} := by
    rw [hSK, ← hcard_eq, hc64]
    norm_num
  obtain ⟨hlin, hiso⟩ := S.linear_isometry_of_card_fixed_gt hgN hg2 hfixcard
  have hg1 : g ≠ 1 := by
    intro h1
    have htop : Nat.card {v : ↥I // g v = v} = Nat.card ↥I := by
      refine Nat.card_congr ?_
      exact
        { toFun := fun v => v.1
          invFun := fun u => ⟨u, by rw [h1]; rfl⟩
          left_inv := fun v => Subtype.ext rfl
          right_inv := fun u => rfl }
    rw [← hcard_eq, hc64, card_of_natOmegaPlus h] at htop
    omega
  obtain ⟨eW, hQe, -, hline⟩ := S.exists_line_of_card_fixed_gt hlin hiso hg1 hfixcard
  have hrefl := S.reflection_formula hlin hiso hg1 hQe hline
  refine ⟨S, S.vec eW, hSK, hSω, hQe, hlin, ?_⟩
  · intro v
    obtain ⟨a, ha⟩ := hline v
    have hspec := hrefl v a ha
    have hcoef : a = polQ (S.vec v) (S.vec eW) / S.Q eW := by
      rw [eq_div_iff hQe, hspec]
      change StatedQuadPlus 2 S.K (S.vec (v * eW)) - StatedQuadPlus 2 S.K (S.vec v) -
        StatedQuadPlus 2 S.K (S.vec eW) = polQ (S.vec v) (S.vec eW)
      rw [S.vec_mul]
      rfl
    have hgv : g v = S.smul a eW * v := by
      rw [← ha]
      group
    have hvec : S.vec (g v) = S.vec (S.smul a eW * v) := congrArg S.vec hgv
    rw [hvec, S.vec_mul, S.vec_smul, hcoef]
    exact add_comm _ _

theorem centralizer_of_natOmegaPlus {X : Subgroup (MulAut W)} {I : Subgroup W}
    (h : NatOmegaPlus X I ⊥ 4 2) : ∀ x ∈ X, (∀ v ∈ I, x v = v) → x = 1 := by
  classical
  have hInv : ∀ x ∈ X, ∀ v ∈ I, x v ∈ I := natOmegaPlus_invariant h
  obtain ⟨-, K, hF, hFin, hcard, π, hRV⟩ := h
  obtain ⟨H', π', hH', hπ', hRV'⟩ := exists_realizesVia_restrict hRV
  obtain ⟨e, he⟩ := H.exists_mulEquiv_of_realizesVia
    (StatedOmega (StatedQuadPlus (4 / 2) K)) hRV'
  have hmap : H'.map (H.congrHom e) =
      H.natImage (StatedOmega (StatedQuadPlus (4 / 2) K)) :=
    H.map_congrHom_eq_natImage _ hRV'.1 e he
  set φ := actOnSub hInv with hφ
  have hle1 : Nat.card ↥X ≤ Nat.card ↥(StatedOmega (StatedQuadPlus (4 / 2) K)) :=
    Nat.card_le_card_of_surjective π hRV.1
  have heqΓ : Nat.card ↥(StatedOmega (StatedQuadPlus (4 / 2) K)) = Nat.card ↥H' := by
    rw [← Subgroup.card_map_of_injective H.matHom_injective, ← H.natImage_eq_map, ← hmap,
      Subgroup.card_map_of_injective (MulEquiv.injective _)]
  have hle2 : Nat.card ↥H' ≤ Nat.card ↥X := by
    have hsurj : Function.Surjective (fun x : ↥X =>
        (⟨φ x, by rw [hH']; exact ⟨x, rfl⟩⟩ : ↥H')) := by
      intro y
      have hy : (y : MulAut ↥I) ∈ φ.range := by
        rw [← hH']
        exact y.2
      obtain ⟨x, hx⟩ := hy
      exact ⟨x, Subtype.ext hx⟩
    exact Nat.card_le_card_of_surjective _ hsurj
  have hcardX : Nat.card ↥X = Nat.card ↥H' := le_antisymm (hle1.trans_eq heqΓ) hle2
  have hker : MonoidHom.ker φ = ⊥ := by
    have h1 : Nat.card ↥X = Nat.card ↥H' * Nat.card ↥(MonoidHom.ker φ) := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (MonoidHom.ker φ)]
      congr 1
      refine (Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv).trans ?_
      rw [show φ.range = H' from hH'.symm]
    have hpos : 0 < Nat.card ↥H' := Nat.card_pos
    have h2 : Nat.card ↥H' = Nat.card ↥H' * Nat.card ↥(MonoidHom.ker φ) := by
      calc Nat.card ↥H' = Nat.card ↥X := hcardX.symm
        _ = Nat.card ↥H' * Nat.card ↥(MonoidHom.ker φ) := h1
    have h3 : Nat.card ↥H' * Nat.card ↥(MonoidHom.ker φ) = Nat.card ↥H' * 1 := by
      rw [← h2, mul_one]
    have hk1 : Nat.card ↥(MonoidHom.ker φ) = 1 :=
      Nat.eq_of_mul_eq_mul_left hpos h3
    rw [eq_bot_iff]
    intro y hy
    rw [Subgroup.mem_bot]
    have h4 : (⟨y, hy⟩ : ↥(MonoidHom.ker φ)) = 1 :=
      @Subsingleton.elim _ (Nat.card_eq_one_iff_unique.mp hk1).1 ⟨y, hy⟩ 1
    exact congrArg Subtype.val h4
  intro x hx hfix
  have hx1 : φ ⟨x, hx⟩ = 1 := by
    ext v
    rw [hφ, actOnSub_apply]
    exact hfix v v.2
  have hinj : Function.Injective φ := by
    intro a b hab
    have h1 : a * b⁻¹ = 1 := by
      have h2 : a * b⁻¹ ∈ MonoidHom.ker φ := by
        rw [MonoidHom.mem_ker]
        simp [map_mul, hab]
      simpa [hker] using h2
    calc a = a * b⁻¹ * b := by group
      _ = b := by rw [h1, one_mul]
  have h3 : (⟨x, hx⟩ : ↥X) = 1 := hinj (by rw [hx1, map_one])
  exact congrArg Subtype.val h3

theorem preserves_summands {X : Subgroup (MulAut W)} {I : Fin 2 → Subgroup W}
    (hIbot : I 0 ⊓ I 1 = ⊥) (hItop : I 0 ⊔ I 1 = ⊤)
    (hIN : ∀ i, NatOmegaPlus X (I i) ⊥ 4 2) (hniso : ¬ H.Pair.IsoMod X (I 0) (I 1))
    {w : MulAut W} (hwN : w ∈ Subgroup.normalizer (X : Set (MulAut W))) (hw2 : w ^ 2 = 1)
    (hm : E3.mQuot ⊤ (fixV (Subgroup.zpowers w)) = 4) :
    (∀ v ∈ I 0, w v ∈ I 0) ∧ (∀ v ∈ I 1, w v ∈ I 1) := by
  classical
  have hw1 : w * w = 1 := by rwa [pow_two] at hw2
  have hcard0 : Nat.card ↥(I 0) = 256 := card_of_natOmegaPlus (hIN 0)
  have hcard1 : Nat.card ↥(I 1) = 256 := card_of_natOmegaPlus (hIN 1)
  have hIrr0 : H.Pair.IsIrr X (I 0) := isIrr_natOmegaPlus (hIN 0)
  have hIrr1 : H.Pair.IsIrr X (I 1) := isIrr_natOmegaPlus (hIN 1)
  have hInv0 : H.Pair.IsInv X (I 0) := natOmegaPlus_invariant (hIN 0)
  have hInv1 : H.Pair.IsInv X (I 1) := natOmegaPlus_invariant (hIN 1)
  have hW : Nat.card W = 2 ^ 16 := by
    have h := natCard_eq_mul_of_sup_eq_top hIbot hItop
    rw [hcard0, hcard1] at h
    norm_num at h ⊢
    exact h
  have hfix : Nat.card ↥(fixV (Subgroup.zpowers w)) = 2 ^ 12 :=
    card_fixV_of_mQuot_top hW hm
  have hmap1 : ((I 1).map w.toMonoidHom).map w.toMonoidHom = I 1 := by
    rw [Subgroup.map_map]
    have hcomp : w.toMonoidHom.comp w.toMonoidHom = (w * w).toMonoidHom := by
      ext x
      rfl
    rw [hcomp, hw1]
    exact Subgroup.map_id _
  rcases H.Pair.map_eq_or_map_eq hIbot hItop hInv0 hInv1 hIrr0 hIrr1 hniso hwN with h | h
  ·
    have h1 : (I 1).map w.toMonoidHom = I 1 := by
      have hinf' : I 1 ⊓ I 0 = ⊥ := by rw [inf_comm]; exact hIbot
      have hsup' : I 1 ⊔ I 0 = ⊤ := by rw [sup_comm]; exact hItop
      rcases H.Pair.map_eq_or_map_eq hinf' hsup' hInv1 hInv0 hIrr1 hIrr0
        (fun h' => hniso (H.Pair.IsoMod.symm hInv1 h')) hwN with h' | h'
      · exact h'
      · exfalso
        rw [h'] at hmap1
        rw [h] at hmap1
        have h3 : I 0 = ⊥ := by
          rw [← hIbot, hmap1, inf_idem]
        rw [h3, Subgroup.card_bot] at hcard0
        omega
    exact ⟨fun v hv => by
        have := Subgroup.mem_map_of_mem w.toMonoidHom hv
        rwa [h] at this,
      fun v hv => by
        have := Subgroup.mem_map_of_mem w.toMonoidHom hv
        rwa [h1] at this⟩
  ·
    exfalso
    have hc := card_fixV_of_swap hIbot hItop hw2 h
    rw [hc, hcard0] at hfix
    norm_num at hfix

private theorem card_fixV_eq_pow_four {X : Subgroup (MulAut W)} {I : Subgroup W}
    (h : NatOmegaPlus X I ⊥ 4 2) {w : MulAut W}
    (hwN : w ∈ Subgroup.normalizer (X : Set (MulAut W)))
    (hpres : ∀ v ∈ I, w v ∈ I) (hw2 : w ^ 2 = 1)
    (hlarge : 16 < Nat.card ↥(I ⊓ fixV (Subgroup.zpowers w))) :
    ∃ d : ℕ, d ≤ 4 ∧ Nat.card ↥(I ⊓ fixV (Subgroup.zpowers w)) = 4 ^ d := by
  classical
  obtain ⟨S, hSK, hSω⟩ := exists_omegaModel_summand h
  set g := mulAutOnSub w hpres with hgdef
  have hgval : ∀ v : ↥I, ((g v : ↥I) : W) = w (v : W) := fun v => mulAutOnSub_apply w hpres v
  have hle : I.map w.toMonoidHom ≤ I := by
    rintro _ ⟨u, hu, rfl⟩
    exact hpres u hu
  have hcardmap : Nat.card ↥(I.map w.toMonoidHom) = Nat.card ↥I :=
    Subgroup.card_map_of_injective (MulEquiv.injective w)
  have hmapI : I.map w.toMonoidHom = I :=
    Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcardmap.symm)
  have hpres' : ∀ v ∈ I, w⁻¹ v ∈ I := by
    intro v hv
    have hv' : v ∈ I.map w.toMonoidHom := by rw [hmapI]; exact hv
    obtain ⟨u, hu, hue⟩ := Subgroup.mem_map.1 hv'
    rw [← hue]
    simpa using hu
  have hcard_eq : Nat.card ↥(I ⊓ fixV (Subgroup.zpowers w)) =
      Nat.card {v : ↥I // g v = v} := by
    refine Nat.card_congr ?_
    exact
      { toFun := fun v => ⟨⟨(v : W), v.2.1⟩, by
          apply Subtype.ext
          rw [hgval]
          exact mem_fixV_zpowers_iff_apply.1 v.2.2⟩
        invFun := fun v => ⟨(v.1 : W), v.1.2, by
          have h1 : w (v.1 : W) = (v.1 : W) := by
            rw [← hgval (v.1)]
            exact congrArg Subtype.val v.2
          exact mem_fixV_zpowers_iff_apply.2 h1⟩
        left_inv := fun v => Subtype.ext rfl
        right_inv := fun v => Subtype.ext rfl }
  have hginv_eq : g⁻¹ = mulAutOnSub w⁻¹ hpres' := by
    have h1 : g * mulAutOnSub w⁻¹ hpres' = 1 := by
      ext u
      show w (w⁻¹ ((u : ↥I) : W)) = ((u : ↥I) : W)
      simp
    calc g⁻¹ = g⁻¹ * 1 := (mul_one _).symm
      _ = g⁻¹ * (g * mulAutOnSub w⁻¹ hpres') := by rw [h1]
      _ = mulAutOnSub w⁻¹ hpres' := by rw [← mul_assoc, inv_mul_cancel, one_mul]
  have hgN : g ∈ Subgroup.normalizer (S.omega : Set (MulAut ↥I)) := by
    rw [hSω, Subgroup.mem_normalizer_iff_map_conj_eq]
    ext y
    constructor
    · intro hy
      obtain ⟨u, hu, huy⟩ := Subgroup.mem_map.1 hy
      obtain ⟨x, rfl⟩ := hu
      refine ⟨⟨w * (x : MulAut W) * w⁻¹,
        (Subgroup.mem_normalizer_iff.mp hwN (x : MulAut W)).mp x.2⟩, ?_⟩
      exact (conj_mulAutOnSub_actOnSub (natOmegaPlus_invariant h) hwN hpres hpres' x).symm.trans
        huy
    · intro hy
      obtain ⟨x, rfl⟩ := hy
      refine Subgroup.mem_map.2 ⟨MulAut.conj g⁻¹ (actOnSub (natOmegaPlus_invariant h) x),
        ?_, ?_⟩
      · refine ⟨⟨w⁻¹ * (x : MulAut W) * (w⁻¹)⁻¹,
          (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hwN) (x : MulAut W)).mp x.2⟩, ?_⟩
        rw [hginv_eq]
        exact (conj_mulAutOnSub_actOnSub (natOmegaPlus_invariant h)
          (Subgroup.inv_mem _ hwN) hpres' hpres x).symm
      · show (MulAut.conj g) ((MulAut.conj g⁻¹) (actOnSub (natOmegaPlus_invariant h) x)) =
          actOnSub (natOmegaPlus_invariant h) x
        simp only [MulAut.conj_apply]
        group
  have hww : ∀ x : W, w (w x) = x := by
    intro x
    have h1 : (w * w) x = (1 : MulAut W) x := by
      rw [show w * w = 1 from by rwa [pow_two] at hw2]
    simpa using h1
  have hg2 : g * g = 1 := by
    ext u
    show w (w ((u : ↥I) : W)) = ((u : ↥I) : W)
    rw [hww]
  have hfixcard : Nat.card S.K ^ 2 < Nat.card {v : ↥I // g v = v} := by
    rw [hSK, ← hcard_eq]
    exact hlarge
  obtain ⟨hlin, -⟩ := S.linear_isometry_of_card_fixed_gt hgN hg2 hfixcard
  set gb : MulAut (CFSG.Quasithin.H.StdMod OmI S.K) := MulAut.congr S.e g with hgb
  have hvecg : ∀ v : OmI → S.K,
      H.toAddMap gb v = S.vec (g (S.e.symm (Multiplicative.ofAdd v))) := fun v => rfl
  have hvecgI : ∀ u : ↥I, H.toAddMap gb (S.vec u) = S.vec (g u) := by
    intro u
    rw [hvecg]
    exact congrArg (fun x => S.vec (g x)) (S.ofVec_vec u)
  have hlinb : ∀ (c : S.K) (v : OmI → S.K), H.toAddMap gb (c • v) = c • H.toAddMap gb v := by
    intro c v
    set u : ↥I := S.e.symm (Multiplicative.ofAdd v) with hu
    have h1 := congrArg S.vec (hlin c u)
    have h3 : S.vec (S.smul c u) = c • v := by
      rw [S.vec_smul, hu]
      congr 1
      exact S.vec_ofVec v
    have h4 : S.vec (S.smul c (g u)) = c • S.vec (g u) := S.vec_smul c (g u)
    have h5 : S.vec (g u) = H.toAddMap gb v := by
      rw [← hvecgI]
      have hu2 : S.vec u = v := by
        rw [hu]
        exact S.vec_ofVec v
      rw [hu2]
    rw [← hvecgI, h3, h4, h5] at h1
    exact h1
  let f : (OmI → S.K) →ₗ[S.K] (OmI → S.K) :=
    { toFun := fun v => H.toAddMap gb v
      map_add' := fun v w => by
        have h1 : H.toAddMap gb (v + w) =
            Multiplicative.toAdd (gb (Multiplicative.ofAdd v * Multiplicative.ofAdd w)) := rfl
        rw [h1, map_mul]
        rfl
      map_smul' := hlinb }
  let f' : (OmI → S.K) →ₗ[S.K] (OmI → S.K) :=
    f - (LinearMap.id : (OmI → S.K) →ₗ[S.K] (OmI → S.K))
  let Vsub : Submodule S.K (OmI → S.K) := LinearMap.ker f'
  have hVsub : ∀ v : OmI → S.K, v ∈ Vsub ↔ H.toAddMap gb v = v := by
    intro v
    have h1 : v ∈ Vsub ↔ f' v = 0 := LinearMap.mem_ker
    have h2 : f' v = H.toAddMap gb v - v := rfl
    rw [h1, h2, sub_eq_zero]
  have hmemVsub : ∀ u : ↥I, S.vec u ∈ Vsub ↔ g u = u := by
    intro u
    rw [hVsub, hvecgI]
    exact ⟨fun h => S.vec_injective h, fun h => by rw [h]⟩
  have hbij : Nat.card {v : ↥I // g v = v} = Nat.card ↥Vsub := by
    refine Nat.card_congr ?_
    exact
      { toFun := fun u => ⟨S.vec u.1, (hmemVsub u.1).2 u.2⟩
        invFun := fun v => ⟨S.ofVec (v : OmI → S.K), by
          apply S.vec_injective
          rw [← hvecgI, S.vec_ofVec]
          exact (hVsub v.1).1 v.2⟩
        left_inv := fun u => Subtype.ext (S.ofVec_vec u.1)
        right_inv := fun v => Subtype.ext (S.vec_ofVec v.1) }
  refine ⟨Module.finrank S.K Vsub, ?_, ?_⟩
  · have h1 := Submodule.finrank_le Vsub
    have h2 : Module.finrank S.K (OmI → S.K) = 4 := by
      rw [Module.finrank_fintype_fun_eq_card]
      decide
    omega
  · have hfin : Module.Finite S.K ↥Vsub :=
      Module.Finite.of_injective (Submodule.subtype Vsub) Subtype.val_injective
    rw [hcard_eq, hbij, @Module.natCard_eq_pow_finrank S.K ↥Vsub _ _ _ hfin, hSK]

private theorem card_fixV_eq_one_or_card {X : Subgroup (MulAut W)} {I : Subgroup W}
    (h : NatOmegaPlus X I ⊥ 4 2) {w : MulAut W}
    (hpres : ∀ v ∈ I, w v ∈ I) (hcomm : ∀ x ∈ X, w * x = x * w) :
    Nat.card ↥(I ⊓ fixV (Subgroup.zpowers w)) = 1 ∨
      Nat.card ↥(I ⊓ fixV (Subgroup.zpowers w)) = Nat.card ↥I := by
  classical
  obtain ⟨S, hSK, hSω⟩ := exists_omegaModel_summand h
  set g := mulAutOnSub w hpres with hgdef
  have hgval : ∀ v : ↥I, ((g v : ↥I) : W) = w (v : W) := fun v => mulAutOnSub_apply w hpres v
  have hcard_eq : Nat.card ↥(I ⊓ fixV (Subgroup.zpowers w)) =
      Nat.card {v : ↥I // g v = v} := by
    refine Nat.card_congr ?_
    exact
      { toFun := fun v => ⟨⟨(v : W), v.2.1⟩, by
          apply Subtype.ext
          rw [hgval]
          exact mem_fixV_zpowers_iff_apply.1 v.2.2⟩
        invFun := fun v => ⟨(v.1 : W), v.1.2, by
          have h1 : w (v.1 : W) = (v.1 : W) := by
            rw [← hgval (v.1)]
            exact congrArg Subtype.val v.2
          exact mem_fixV_zpowers_iff_apply.2 h1⟩
        left_inv := fun v => Subtype.ext rfl
        right_inv := fun v => Subtype.ext rfl }
  have hgc : ∀ y ∈ S.omega0, ∀ v : ↥I, g (y v) = y (g v) := by
    intro y hy v
    have hy' : y ∈ S.omega := S.omega0_le_omega hy
    rw [hSω] at hy'
    obtain ⟨x, hx⟩ := hy'
    apply Subtype.ext
    have h1 : ((y v : ↥I) : W) = (x : MulAut W) (v : W) := by
      rw [← hx]
      exact actOnSub_apply _ x v
    have h2 : ((g (y v) : ↥I) : W) = w ((y v : ↥I) : W) := mulAutOnSub_apply w hpres (y v)
    have h3 : ((y (g v) : ↥I) : W) = (x : MulAut W) ((g v : ↥I) : W) := by
      rw [← hx]
      exact actOnSub_apply _ x (g v)
    rw [h2, h1, h3, mulAutOnSub_apply]
    have h4 := congrArg (fun f : MulAut W => f (v : W)) (hcomm (x : MulAut W) x.2)
    simpa [MulAut.mul_apply] using h4
  obtain ⟨c, hc⟩ := S.exists_smul_of_commute_omega0 g.toMonoidHom hgc
  have hc' : ∀ v : ↥I, g v = S.smul c v := fun v => hc v
  by_cases hc1 : c = 1
  · right
    have htop : Nat.card {v : ↥I // g v = v} = Nat.card ↥I := by
      refine Nat.card_congr ?_
      exact
        { toFun := fun v => v.1
          invFun := fun u => ⟨u, by rw [hc' u, hc1]; exact S.smul_one_eq u⟩
          left_inv := fun v => Subtype.ext rfl
          right_inv := fun u => rfl }
    rw [hcard_eq, htop]
  · left
    have hsingle : ∀ v : {v : ↥I // g v = v}, v = ⟨1, map_one g⟩ := by
      rintro ⟨v, hv⟩
      have hv1 : v = 1 := by
        by_contra hne
        have hvec : S.vec v ≠ 0 := by
          intro h0
          exact hne (S.vec_injective (by rw [h0, S.vec_one]))
        have hsm : c • S.vec v = S.vec v := by
          have h5 := congrArg S.vec (hc' v)
          rw [hv, S.vec_smul] at h5
          exact h5.symm
        have h6 : (c - 1) • S.vec v = 0 := by
          rw [sub_smul, one_smul, hsm, sub_self]
        rcases smul_eq_zero.1 h6 with h7 | h7
        · exact hc1 (sub_eq_zero.1 h7)
        · exact hvec h7
      exact Subtype.ext hv1
    have hcard1 : Nat.card {v : ↥I // g v = v} = 1 := by
      refine Nat.card_eq_one_iff_unique.mpr ⟨⟨fun a b => ?_⟩, ⟨⟨1, map_one g⟩⟩⟩
      rw [hsingle a, hsingle b]
    rw [hcard_eq, hcard1]

theorem fixV_card_eq_64 {X : Subgroup (MulAut W)} {I : Fin 2 → Subgroup W}
    (hIbot : I 0 ⊓ I 1 = ⊥) (hItop : I 0 ⊔ I 1 = ⊤)
    (hIN : ∀ i, NatOmegaPlus X (I i) ⊥ 4 2)
    {w : MulAut W} (hpres : (∀ v ∈ I 0, w v ∈ I 0) ∧ (∀ v ∈ I 1, w v ∈ I 1))
    (hwN : w ∈ Subgroup.normalizer (X : Set (MulAut W))) (hw2 : w ^ 2 = 1)
    (hm : E3.mQuot ⊤ (fixV (Subgroup.zpowers w)) = 4) :
    Nat.card ↥(I 0 ⊓ fixV (Subgroup.zpowers w)) = 64 ∧
      Nat.card ↥(I 1 ⊓ fixV (Subgroup.zpowers w)) = 64 := by
  classical
  have hW : Nat.card W = 2 ^ 16 := by
    have h := natCard_eq_mul_of_sup_eq_top hIbot hItop
    rw [card_of_natOmegaPlus (hIN 0), card_of_natOmegaPlus (hIN 1)] at h
    norm_num at h ⊢
    exact h
  have hfix : Nat.card ↥(fixV (Subgroup.zpowers w)) = 2 ^ 12 :=
    card_fixV_of_mQuot_top hW hm
  set c0 := Nat.card ↥(I 0 ⊓ fixV (Subgroup.zpowers w)) with hc0
  set c1 := Nat.card ↥(I 1 ⊓ fixV (Subgroup.zpowers w)) with hc1
  have h4096 : c0 * c1 = 4096 := by
    have h := card_fixV_eq_mul_of_preserves hIbot hItop hpres.1 hpres.2
    rw [hfix] at h
    rw [hc0, hc1, ← h]
    norm_num
  have hc0le : c0 ≤ 256 := by
    have hinj : Function.Injective
        (fun x : ↥(I 0 ⊓ fixV (Subgroup.zpowers w)) => (⟨(x : W), x.2.1⟩ : ↥(I 0))) := by
      intro a b hab
      exact Subtype.ext (congrArg (fun y : ↥(I 0) => (y : W)) hab)
    have h := Nat.card_le_card_of_injective _ hinj
    rw [card_of_natOmegaPlus (hIN 0)] at h
    exact h
  have hc1le : c1 ≤ 256 := by
    have hinj : Function.Injective
        (fun x : ↥(I 1 ⊓ fixV (Subgroup.zpowers w)) => (⟨(x : W), x.2.1⟩ : ↥(I 1))) := by
      intro a b hab
      exact Subtype.ext (congrArg (fun y : ↥(I 1) => (y : W)) hab)
    have h := Nat.card_le_card_of_injective _ hinj
    rw [card_of_natOmegaPlus (hIN 1)] at h
    exact h
  have hc0gt : 16 < c0 := by
    by_contra h
    push Not at h
    have h16 : c1 = 256 := by
      have h1 : 256 ≤ c1 := by
        by_contra h2
        push Not at h2
        have h3 : c0 * c1 ≤ 16 * 255 := Nat.mul_le_mul h (by omega)
        omega
      exact le_antisymm hc1le h1
    have htriv : ∀ v ∈ I 1, w v = v := by
      intro v hv
      have heq : I 1 ⊓ fixV (Subgroup.zpowers w) = I 1 :=
        Subgroup.eq_of_le_of_card_ge inf_le_left
          (by rw [card_of_natOmegaPlus (hIN 1), ← hc1, h16])
      have hv' : v ∈ I 1 ⊓ fixV (Subgroup.zpowers w) := by rw [heq]; exact hv
      exact mem_fixV_zpowers_iff_apply.1 hv'.2
    have hw_inv_v : ∀ v ∈ I 1, w⁻¹ v ∈ I 1 := by
      intro v hv
      have h1 : w⁻¹ v = v := w.injective (by simp [htriv v hv])
      rw [h1]
      exact hv
    have hcomm : ∀ x ∈ X, w * x = x * w :=
      SmithD321.comm_of_trivial_on hwN (natOmegaPlus_invariant (hIN 1))
        (centralizer_of_natOmegaPlus (hIN 1)) htriv hw_inv_v
    have hsc := card_fixV_eq_one_or_card (hIN 0) hpres.1 hcomm
    have hc0eq : c0 = 16 := by
      have h1 : c0 * 256 = 16 * 256 := by rw [← h16, h4096, h16]
      exact Nat.eq_of_mul_eq_mul_right (by norm_num) h1
    rcases hsc with h1 | h1
    · rw [← hc0] at h1
      omega
    · rw [← hc0, card_of_natOmegaPlus (hIN 0)] at h1
      omega
  have hc1gt : 16 < c1 := by
    by_contra h
    push Not at h
    have h16 : c0 = 256 := by
      have h1 : 256 ≤ c0 := by
        by_contra h2
        push Not at h2
        have h3 : c0 * c1 ≤ 255 * 16 := Nat.mul_le_mul (by omega) h
        omega
      exact le_antisymm hc0le h1
    have htriv : ∀ v ∈ I 0, w v = v := by
      intro v hv
      have heq : I 0 ⊓ fixV (Subgroup.zpowers w) = I 0 :=
        Subgroup.eq_of_le_of_card_ge inf_le_left
          (by rw [card_of_natOmegaPlus (hIN 0), ← hc0, h16])
      have hv' : v ∈ I 0 ⊓ fixV (Subgroup.zpowers w) := by rw [heq]; exact hv
      exact mem_fixV_zpowers_iff_apply.1 hv'.2
    have hw_inv_v : ∀ v ∈ I 0, w⁻¹ v ∈ I 0 := by
      intro v hv
      have h1 : w⁻¹ v = v := w.injective (by simp [htriv v hv])
      rw [h1]
      exact hv
    have hcomm : ∀ x ∈ X, w * x = x * w :=
      SmithD321.comm_of_trivial_on hwN (natOmegaPlus_invariant (hIN 0))
        (centralizer_of_natOmegaPlus (hIN 0)) htriv hw_inv_v
    have hsc := card_fixV_eq_one_or_card (hIN 1) hpres.2 hcomm
    have hc1eq : c1 = 16 := by
      have h1 : c1 * 256 = 16 * 256 := by
        rw [← h16, mul_comm c1 c0, h4096, h16]
      exact Nat.eq_of_mul_eq_mul_right (by norm_num) h1
    rcases hsc with h1 | h1
    · rw [← hc1] at h1
      omega
    · rw [← hc1, card_of_natOmegaPlus (hIN 1)] at h1
      omega
  obtain ⟨d0, hd0le, hd0⟩ :=
    card_fixV_eq_pow_four (hIN 0) hwN hpres.1 hw2 (by rw [← hc0]; exact hc0gt)
  obtain ⟨d1, hd1le, hd1⟩ :=
    card_fixV_eq_pow_four (hIN 1) hwN hpres.2 hw2 (by rw [← hc1]; exact hc1gt)
  have hc0cases : c0 = 64 ∨ c0 = 256 := by
    have h3 : 3 ≤ d0 := by
      by_contra h
      push Not at h
      have h4 : 4 ^ d0 ≤ 4 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h5 : c0 ≤ 16 := by rw [hc0, hd0]; simpa using h4
      omega
    have h4 : d0 = 3 ∨ d0 = 4 := by omega
    rcases h4 with h4 | h4 <;> rw [hc0, hd0, h4] <;> norm_num
  have hc1cases : c1 = 64 ∨ c1 = 256 := by
    have h3 : 3 ≤ d1 := by
      by_contra h
      push Not at h
      have h4 : 4 ^ d1 ≤ 4 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h5 : c1 ≤ 16 := by rw [hc1, hd1]; simpa using h4
      omega
    have h4 : d1 = 3 ∨ d1 = 4 := by omega
    rcases h4 with h4 | h4 <;> rw [hc1, hd1, h4] <;> norm_num
  rcases hc0cases with h0 | h0 <;> rcases hc1cases with h1 | h1
  · exact ⟨h0, h1⟩
  · rw [h0, h1] at h4096
    norm_num at h4096
  · rw [h0, h1] at h4096
    norm_num at h4096
  · rw [h0, h1] at h4096
    norm_num at h4096

private theorem congr_actHom {I : Subgroup W} {S : OmegaModel ↥I}
    (γ : GL OmI S.K) : MulAut.congr S.e (S.actHom γ) = H.matAut γ := by
  apply MulEquiv.ext
  intro u
  show Multiplicative.toAdd (S.e (S.actHom γ (S.e.symm u))) =
    Multiplicative.toAdd (H.matAut γ u)
  have h2 : ∀ w : ↥I, S.e w = Multiplicative.ofAdd (S.vec w) := fun w => rfl
  rw [h2, S.actHom_vec]
  rw [show S.vec (S.e.symm u) = Multiplicative.toAdd u from S.vec_ofVec (Multiplicative.toAdd u)]
  rfl

theorem omega_map_congr_eq_natImage {I : Subgroup W}
    {S : OmegaModel ↥I} :
    S.omega.map (H.congrHom S.e) =
      CFSG.Quasithin.H.natImage (StatedOmega (StatedQuadPlus 2 S.K)) := by
  have h1 : S.omega = (StatedOmega (StatedQuadPlus 2 S.K)).map S.actHom := rfl
  rw [h1, Subgroup.map_map]
  have h2 : (H.congrHom S.e).comp S.actHom = H.matHom := by
    refine MonoidHom.ext (fun γ => ?_)
    exact congr_actHom γ
  rw [h2, CFSG.Quasithin.H.natImage_eq_map]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18
