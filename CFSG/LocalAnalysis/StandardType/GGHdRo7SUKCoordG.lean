module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7SUKCoordF
public import CFSG.LocalAnalysis.StandardType.GGHdRo7SULCoordModel

public section

namespace CFSG.StandardType.HdRo7SU

open CFSG.StandardType.HdRo7C
open CFSG.Assembly
open CFSG.StandardType.UCoord
open Multiplicative

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem hdRo7SUKCoordAux_torus
    {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hRig : GGLabelRigidInput)
    (hrow : GGResRowAt ggRowSUCorank2 p J K) (hy : y ∈ Bs) :
    ∃ e : ↥(sumZero (hdRo7SUKCoordAux_rowRank hrow) p) ≃* ↥(Bs ⊓ K),
      p = 3 ∧ 7 ≤ hdRo7SUKCoordAux_rowRank hrow ∧ ¬ 3 ∣ hdRo7SUKCoordAux_rowRank hrow ∧
      ∀ a : MulAut ↥Bs,
        a ∈ ggAutomizer K Bs ↔
          (a ⟨y, hy⟩ : ↥Bs) = ⟨y, hy⟩ ∧
          ∃ σ : Equiv.Perm (Fin (hdRo7SUKCoordAux_rowRank hrow)),
            ∀ f : ↥(sumZero (hdRo7SUKCoordAux_rowRank hrow) p),
              ((a ⟨(e f : ↥(Bs ⊓ K)).1, (e f).2.1⟩ : ↥Bs) : G) =
                ((e (permAutV σ f) : ↥(Bs ⊓ K)) : G) := by
  obtain ⟨e, hperm, hnorm⟩ := hdRo7SUKCoordAux_permData hH hRig hrow
  have hspec := hdRo7SUKCoordAux_rowRank_spec hrow
  have hKCy : K ≤ Subgroup.centralizer ({y} : Set G) := hH.2.2.2.2.1.1.2.2.2.1
  refine ⟨e, hspec.1, hspec.2.1, hspec.2.2, ?_⟩
  intro a
  constructor
  · intro ha
    rw [mem_ggAutomizer_iff] at ha
    obtain ⟨g, hgK, hgN, hag⟩ := ha
    have hyg : g * y = y * g :=
      (Subgroup.mem_centralizer_iff.mp (hKCy hgK) y (Set.mem_singleton y)).symm
    have hyfix : (a ⟨y, hy⟩ : ↥Bs) = ⟨y, hy⟩ := by
      apply Subtype.ext
      rw [hag ⟨y, hy⟩]
      calc g * y * g⁻¹ = y * g * g⁻¹ := by rw [hyg]
        _ = y := by group
    refine ⟨hyfix, ?_⟩
    have hgNorm : ∀ t : ↥(Bs ⊓ K), ∃ t' : ↥(Bs ⊓ K),
        (g : G) * (t : G) * (g : G)⁻¹ = (t' : G) := by
      intro t
      refine ⟨⟨g * (t : G) * g⁻¹, ?_, ?_⟩, rfl⟩
      · exact (Subgroup.mem_normalizer_iff.mp hgN (t : G)).mp (Subgroup.mem_inf.mp t.2).1
      · exact K.mul_mem (K.mul_mem hgK (Subgroup.mem_inf.mp t.2).2) (K.inv_mem hgK)
    obtain ⟨π, hπ⟩ := hnorm g hgK hgNorm
    refine ⟨π, fun f => ?_⟩
    rw [hag ⟨(e f).1, (e f).2.1⟩]
    simpa using hπ f
  · rintro ⟨hay, σ, hσ⟩
    obtain ⟨w, hwK, hwperm⟩ := hperm σ
    have hwT : ∀ t : ↥(Bs ⊓ K), ∃ t' : ↥(Bs ⊓ K),
        (w : G) * (t : G) * (w : G)⁻¹ = (t' : G) := by
      intro t
      obtain ⟨f, hf⟩ := e.surjective t
      refine ⟨e (permAutV σ f), ?_⟩
      have h := hwperm f
      rwa [hf] at h
    have hwC : ∀ c : ↥(Bs ⊓ Subgroup.centralizer (K : Set G)),
        (w : G) * (c : G) * (w : G)⁻¹ = (c : G) := by
      intro c
      have hcw : (w : G) * (c : G) = (c : G) * (w : G) :=
        Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp c.2).2 (w : G) hwK
      rw [hcw]; group
    rw [mem_ggAutomizer_iff]
    refine ⟨w, hwK, ?_, ?_⟩
    · have hmaple : Bs.map (MulAut.conj w).toMonoidHom ≤ Bs := by
        rintro y' ⟨u, hu, rfl⟩
        show (w : G) * u * (w : G)⁻¹ ∈ Bs
        obtain ⟨t, ht, c, hc, hbc⟩ := hdRo7SUKCoordAux_split hH hRig hrow u hu
        obtain ⟨t', hwt'⟩ := hwT ⟨t, ht⟩
        rw [hbc, show (w : G) * (t * (c : G)) * (w : G)⁻¹ =
            ((w : G) * t * (w : G)⁻¹) * ((w : G) * (c : G) * (w : G)⁻¹) by group,
          hwt', hwC ⟨c, hc⟩]
        exact Bs.mul_mem (Subgroup.mem_inf.mp t'.2).1 (Subgroup.mem_inf.mp hc).1
      have hconjinj : Function.Injective (MulAut.conj w) := by
        intro u v huv
        rw [MulAut.conj_apply, MulAut.conj_apply] at huv
        exact mul_left_cancel (mul_right_cancel huv)
      have hcard : Nat.card ↥(Bs.map (MulAut.conj w).toMonoidHom) = Nat.card ↥Bs :=
        Subgroup.card_map_of_injective hconjinj
      have hmap : Bs.map (MulAut.conj w).toMonoidHom = Bs :=
        Subgroup.eq_of_le_of_card_ge hmaple (by rw [hcard])
      rw [Subgroup.mem_normalizer_iff]
      intro u
      constructor
      · intro hu
        exact hmaple ⟨u, hu, rfl⟩
      · intro hu
        have hu' : (MulAut.conj w) u ∈ Bs.map (MulAut.conj w).toMonoidHom := by
          rw [hmap]; exact hu
        obtain ⟨v, hv, hvu⟩ := hu'
        rw [← hconjinj hvu]
        exact hv
    · intro b
      obtain ⟨t, ht, c, hc, hbc⟩ := hdRo7SUKCoordAux_split hH hRig hrow (b : G) b.2
      obtain ⟨f, hf⟩ := e.surjective ⟨t, ht⟩
      have hat : (a ⟨t, ht.1⟩ : G) = (w : G) * t * (w : G)⁻¹ := by
        have h1 := hσ f
        rw [hf] at h1
        have h2 := hwperm f
        rw [hf] at h2
        rw [h1, h2]
      have hac' : a (⟨(c : G), (Subgroup.mem_inf.mp hc).1⟩ : ↥Bs) =
          ⟨(c : G), (Subgroup.mem_inf.mp hc).1⟩ := by
        have hcZ : (c : G) ∈ Subgroup.zpowers y := by
          rw [← hdRo7SUKCoordAux_centralizer hH hRig hrow]; exact hc
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hcZ
        have hyk : (⟨y, hy⟩ : ↥Bs) ^ k = (⟨(c : G), (Subgroup.mem_inf.mp hc).1⟩ : ↥Bs) := by
          apply Subtype.ext
          simpa using hk
        calc a (⟨(c : G), (Subgroup.mem_inf.mp hc).1⟩ : ↥Bs) = a ((⟨y, hy⟩ : ↥Bs) ^ k) := by
              rw [hyk]
          _ = (a ⟨y, hy⟩) ^ k := by rw [map_zpow]
          _ = (⟨y, hy⟩ : ↥Bs) ^ k := by rw [hay]
          _ = ⟨(c : G), (Subgroup.mem_inf.mp hc).1⟩ := hyk
      have hac : (a ⟨(c : G), (Subgroup.mem_inf.mp hc).1⟩ : G) = (c : G) :=
        congrArg Subtype.val hac'
      have hb_eq : b = ⟨t, (Subgroup.mem_inf.mp ht).1⟩ * ⟨(c : G), (Subgroup.mem_inf.mp hc).1⟩ :=
        Subtype.ext hbc
      calc (↑(a b) : G) = (↑(a (⟨t, (Subgroup.mem_inf.mp ht).1⟩ *
            ⟨(c : G), (Subgroup.mem_inf.mp hc).1⟩)) : G) := by rw [hb_eq]
        _ = (↑(a ⟨t, (Subgroup.mem_inf.mp ht).1⟩ *
            a ⟨(c : G), (Subgroup.mem_inf.mp hc).1⟩) : G) := by rw [map_mul]
        _ = (a ⟨t, (Subgroup.mem_inf.mp ht).1⟩ : G) *
            (a ⟨(c : G), (Subgroup.mem_inf.mp hc).1⟩ : G) := rfl
        _ = ((w : G) * t * (w : G)⁻¹) * ((w : G) * (c : G) * (w : G)⁻¹) := by
              rw [hat, hac, hwC ⟨c, hc⟩]
        _ = (w : G) * (t * (c : G)) * (w : G)⁻¹ := by group
        _ = (w : G) * (b : G) * (w : G)⁻¹ := by rw [hb_eq]; rfl

theorem hdRo7SUKCoordAux_model
    {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G} [Fact p.Prime]
    (hH : GGResHyp p B Bs x L D J y K) (hRig : GGLabelRigidInput)
    (hrow : GGResRowAt ggRowSUCorank2 p J K) :
    ∃ (hy : y ∈ Bs) (τ : (Fin (hdRo7SUKCoordAux_rowRank hrow)
        → Multiplicative (ZMod p)) ≃* ↥Bs),
      p = 3 ∧ 7 ≤ hdRo7SUKCoordAux_rowRank hrow ∧ ¬ 3 ∣ hdRo7SUKCoordAux_rowRank hrow ∧
      τ (fun _ => Multiplicative.ofAdd (1 : ZMod p)) = ⟨y, hy⟩ ∧
      SUCoordModel p Bs K (hdRo7SUKCoordAux_rowRank hrow) τ := by
  let M := hdRo7SUKCoordAux_rowRank hrow
  have hy : y ∈ Bs := hH.1.2.1.1 hH.2.2.2.2.1.1.2.1
  obtain ⟨e, hp3, hm7, hm3d, hiff⟩ := hdRo7SUKCoordAux_torus hH hRig hrow hy
  have hm0 : (M : ZMod p) ≠ 0 := by
    intro h
    exact hm3d (hp3 ▸ (CharP.cast_eq_zero_iff (ZMod p) p M).mp h)
  let dec := hdRo7SULCoordAux_decomp M p hm0
  let τC := hdRo7SUKCoordAux_axisEquiv hH hRig hrow
  let Φ := hdRo7SUKCoordAux_prodEquiv hH hRig hrow
  let τ : (Fin M → Multiplicative (ZMod p)) ≃* ↥Bs := dec.trans ((e.prodCongr τC).trans Φ)
  let eB : ↥(sumZero M p) →* ↥Bs :=
    { toFun := fun g => ⟨(e g : G), (e g).2.1⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun g h => Subtype.ext (by simp) }
  let τCB : Multiplicative (ZMod p) →* ↥Bs :=
    { toFun := fun b => ⟨(τC b : G), (τC b).2.1⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun b c => Subtype.ext (by simp) }
  have hτ : ∀ f : Fin M → Multiplicative (ZMod p), τ f = eB ((dec f).1) * τCB ((dec f).2) :=
    fun _ => rfl
  have hτCB1 : τCB (Multiplicative.ofAdd (1 : ZMod p)) = ⟨y, hy⟩ := by
    apply Subtype.ext
    show (τC (Multiplicative.ofAdd (1 : ZMod p)) : G) = y
    exact congrArg Subtype.val (hdRo7SUKCoordAux_axisEquiv_apply_one hH hRig hrow)
  have hS_perm : ∀ (σ : Equiv.Perm (Fin M)) (f : Fin M → Multiplicative (ZMod p)),
      (∑ j, Multiplicative.toAdd (f (σ⁻¹ j))) = (∑ j, Multiplicative.toAdd (f j)) :=
    fun σ f => Equiv.sum_comp σ⁻¹ (fun j => Multiplicative.toAdd (f j))
  have hdec_perm : ∀ (σ : Equiv.Perm (Fin M)) (f : Fin M → Multiplicative (ZMod p)),
      dec (fun i => f (σ⁻¹ i)) = (permAutV σ (dec f).1, (dec f).2) := by
    intro σ f
    apply Prod.ext
    · apply ext_crd
      intro i
      rw [hdRo7SULCoordAux_decomp_crd, crd_permAutV, hdRo7SULCoordAux_decomp_crd, hS_perm σ f]
    · rw [hdRo7SULCoordAux_decomp_snd_apply, hdRo7SULCoordAux_decomp_snd_apply, hS_perm σ f]
  have hfixC : ∀ (a : MulAut ↥Bs), a ⟨y, hy⟩ = ⟨y, hy⟩ →
      ∀ b : Multiplicative (ZMod p), a (τCB b) = τCB b := by
    intro a hay b
    have hb : (τC b : G) ∈ Subgroup.zpowers y := by
      rw [← hdRo7SUKCoordAux_centralizer hH hRig hrow]
      exact (τC b).2
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hb
    have hb_eq : τCB b = (⟨y, hy⟩ : ↥Bs) ^ k := by
      apply Subtype.ext
      show (τC b : G) = y ^ k
      exact hk.symm
    rw [hb_eq, map_zpow, hay]
  have hmain : ∀ a : MulAut ↥Bs,
      (a ⟨y, hy⟩ = ⟨y, hy⟩ ∧ ∃ σ : Equiv.Perm (Fin M),
        ∀ g : ↥(sumZero M p), a (eB g) = eB (permAutV σ g)) ↔
      (∃ σ : Equiv.Perm (Fin M), ∀ f : Fin M → Multiplicative (ZMod p),
          a (τ f) = τ (fun i => f (σ⁻¹ i))) := by
    intro a
    constructor
    · rintro ⟨hay, σ, hσ⟩
      refine ⟨σ, fun f => ?_⟩
      rw [hτ f, hτ (fun i => f (σ⁻¹ i)), hdec_perm σ f, map_mul, hσ (dec f).1,
        hfixC a hay (dec f).2]
    · rintro ⟨σ, hσ⟩
      have hay : a ⟨y, hy⟩ = ⟨y, hy⟩ := by
        have h1 : a (τ (fun _ => Multiplicative.ofAdd (1 : ZMod p))) =
            τ (fun i => (fun _ => Multiplicative.ofAdd (1 : ZMod p)) (σ⁻¹ i)) := hσ _
        have h2 : (fun i => (fun _ => Multiplicative.ofAdd (1 : ZMod p)) (σ⁻¹ i)) =
            (fun _ => Multiplicative.ofAdd (1 : ZMod p)) := rfl
        rw [h2, hτ (fun _ => Multiplicative.ofAdd (1 : ZMod p)),
          hdRo7SULCoordAux_decomp_ones M p hm0, map_one, hτCB1, one_mul] at h1
        exact h1
      refine ⟨hay, σ, fun g => ?_⟩
      have h1 : a (τ (dec.symm (g, (1 : Multiplicative (ZMod p))))) =
          τ (fun i => (dec.symm (g, (1 : Multiplicative (ZMod p)))) (σ⁻¹ i)) := hσ _
      have hfst : (dec (dec.symm (g, (1 : Multiplicative (ZMod p))))).1 = g := by simp
      have hsnd : (dec (dec.symm (g, (1 : Multiplicative (ZMod p))))).2 = 1 := by simp
      simp only [hτ (dec.symm (g, 1)), hτ (fun i => (dec.symm (g, 1)) (σ⁻¹ i)),
        hdec_perm σ (dec.symm (g, 1)), hfst, hsnd, map_mul, map_one, mul_one] at h1
      exact h1
  refine ⟨hy, τ, hp3, hm7, hm3d, ?_, ?_⟩
  · rw [hτ (fun _ => Multiplicative.ofAdd (1 : ZMod p)),
      hdRo7SULCoordAux_decomp_ones M p hm0, map_one, hτCB1, one_mul]
  · intro a
    rw [hiff a]
    have hiffB : (a ⟨y, hy⟩ = ⟨y, hy⟩ ∧ ∃ σ : Equiv.Perm (Fin M),
        ∀ f : ↥(sumZero M p),
          ((a ⟨(e f).1, (e f).2.1⟩ : ↥Bs) : G) =
            ((e (permAutV σ f) : ↥(Bs ⊓ K)) : G)) ↔
        (a ⟨y, hy⟩ = ⟨y, hy⟩ ∧ ∃ σ : Equiv.Perm (Fin M),
          ∀ g : ↥(sumZero M p), a (eB g) = eB (permAutV σ g)) := by
      constructor
      · rintro ⟨hay, σ, hσ⟩
        exact ⟨hay, σ, fun g => Subtype.ext (by simpa [eB] using hσ g)⟩
      · rintro ⟨hay, σ, hσ⟩
        exact ⟨hay, σ, fun g => by
          simpa [eB] using congrArg Subtype.val (hσ g)⟩
    rw [hiffB, hmain a]
    constructor
    · rintro ⟨σ, hσ⟩
      refine ⟨σ, fun f i => ?_⟩
      have h1 : τ.symm (a (τ f)) = fun i => f (σ⁻¹ i) := by
        rw [hσ f, MulEquiv.symm_apply_apply]
      rw [h1]
      simp
    · rintro ⟨σ, hσ⟩
      refine ⟨σ, fun f => ?_⟩
      have hg : τ.symm (a (τ f)) = fun i => f (σ⁻¹ i) := by
        funext k
        have h1 := hσ f (σ⁻¹ k)
        exact Multiplicative.toAdd.injective (by simpa using h1)
      rw [← hg, MulEquiv.apply_symm_apply]

end CFSG.StandardType.HdRo7SU

end