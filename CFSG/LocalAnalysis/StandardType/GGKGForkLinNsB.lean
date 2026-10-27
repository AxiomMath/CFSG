module

public import CFSG.LocalAnalysis.StandardType.GGKGForkLinNsA
public import CFSG.LocalAnalysis.StandardType.GGNbrFrameOneLinearLabel
public import CFSG.LocalAnalysis.StandardType.GGSpNonsplitFrameTorus
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeATransport
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerLinearNonsplit

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.LocalAnalysis.ComponentInitial.LinearFlag SpCoord Multiplicative

theorem ggKGLn_signedEltSC_of_centralQuotient {p : ℕ} (hp : p.Prime) {G R : Type} [Group G]
    [Finite G] [Group R] (q : G →* R) (hq : Function.Surjective q)
    (hker : q.ker ≤ Subgroup.center G) (hcp : ¬ p ∣ Nat.card (Subgroup.center G))
    (h : GGTorusSignedEltSC p G) : GGTorusSignedEltSC p R := by
  intro E hE h3 hsc
  let Et : Subgroup G :=
    { carrier := {g | g ^ p = 1 ∧ q g ∈ E}
      one_mem' := ⟨one_pow p, by rw [map_one]; exact E.one_mem⟩
      mul_mem' := by
        intro x y hx hy
        have hxy : Commute x y :=
          commute_of_lift_pow_eq_one hp hker hcp
            (TableB.IsElemAbelian.comm hE hx.2 hy.2) hy.1
        exact ⟨by rw [hxy.mul_pow, hx.1, hy.1, one_mul],
          by rw [map_mul]; exact E.mul_mem hx.2 hy.2⟩
      inv_mem' := by
        intro x hx
        exact ⟨by rw [inv_pow, hx.1, inv_one], by rw [map_inv]; exact E.inv_mem hx.2⟩ }
  have hEt_ab : IsElemAbelian p Et := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => hx.1⟩
    exact commute_of_lift_pow_eq_one hp hker hcp
      (TableB.IsElemAbelian.comm hE a.2.2 b.2.2) b.2.1
  have hcard : Nat.card Et = Nat.card E := by
    refine Nat.card_congr (Equiv.ofBijective (fun x : Et => (⟨q x, x.2.2⟩ : E)) ⟨?_, ?_⟩)
    · intro x y hxy
      exact Subtype.ext
        (eq_of_lift_pow_eq_one hp hker hcp (Subtype.ext_iff.mp hxy) x.2.1 y.2.1)
    · intro e
      obtain ⟨x, hxq, hxp⟩ := exists_lift_pow_eq_one hp hq hker hcp (hE.2 e e.2)
      exact ⟨⟨x, hxp, hxq ▸ e.2⟩, Subtype.ext hxq⟩
  have hscEt : ∀ g : G, (∀ e ∈ Et, g * e = e * g) → g ^ p = 1 → g ∈ Et := by
    intro g hg hgp
    refine ⟨hgp, ?_⟩
    refine hsc (q g) (fun e he => ?_) (by rw [← map_pow, hgp, map_one])
    obtain ⟨x, hxq, hxp⟩ := exists_lift_pow_eq_one hp hq hker hcp (hE.2 e he)
    have hxEt : x ∈ Et := ⟨hxp, hxq ▸ he⟩
    have h1 : q (g * x) = q (x * g) := congrArg q (hg x hxEt)
    rwa [map_mul, map_mul, hxq] at h1
  have hmap : Et.map q = E := by
    refine le_antisymm ?_ ?_
    · intro e he
      obtain ⟨x, hxEt, rfl⟩ := Subgroup.mem_map.mp he
      exact hxEt.2
    · intro e he
      obtain ⟨x, hxq, hxp⟩ := exists_lift_pow_eq_one hp hq hker hcp (hE.2 e he)
      exact Subgroup.mem_map.mpr ⟨x, ⟨hxp, hxq ▸ he⟩, hxq⟩
  obtain ⟨k, τG, hτGinj, hτGrange, hsgn, hperm, hnorm⟩ :=
    h Et hEt_ab (by rw [hcard]; exact h3) hscEt
  let τ : (Fin k → Multiplicative (ZMod p)) →* R := q.comp τG
  have hτinj : Function.Injective τ := by
    intro x y hxy
    have hxEt : τG x ∈ Et := hτGrange ▸ ⟨x, rfl⟩
    have hyEt : τG y ∈ Et := hτGrange ▸ ⟨y, rfl⟩
    exact hτGinj (eq_of_lift_pow_eq_one hp hker hcp hxy hxEt.1 hyEt.1)
  have hτrange : τ.range = E := by
    change (q.comp τG).range = E
    rw [MonoidHom.range_comp, hτGrange]
    exact hmap
  refine ⟨k, τ, hτinj, hτrange, fun i => ?_, fun σ => ?_, fun g hg => ?_⟩
  · obtain ⟨w, hw⟩ := hsgn i
    exact ⟨q w, fun f => by
      change q w * q (τG f) * (q w)⁻¹ = q (τG (sgnAut i f))
      rw [← map_inv, ← map_mul, ← map_mul, hw f]⟩
  · obtain ⟨w, hw⟩ := hperm σ
    exact ⟨q w, fun f => by
      change q w * q (τG f) * (q w)⁻¹ = q (τG (permAut σ f))
      rw [← map_inv, ← map_mul, ← map_mul, hw f]⟩
  · obtain ⟨ĝ, rfl⟩ := hq g
    have hĝN : ∀ e ∈ Et, ĝ * e * ĝ⁻¹ ∈ Et := by
      intro e he
      refine ⟨?_, ?_⟩
      · rw [conj_pow, he.1, mul_one, mul_inv_cancel]
      · rw [map_mul, map_mul, map_inv]
        exact hg (q e) he.2
    obtain ⟨π, ε, hε, hrel⟩ := hnorm ĝ hĝN
    refine ⟨π, ε, hε, fun f f' hff' => ?_⟩
    have h1 : ĝ * τG f * ĝ⁻¹ ∈ τG.range := by
      rw [hτGrange]
      exact hĝN _ (hτGrange ▸ ⟨f, rfl⟩)
    obtain ⟨f'', hf''⟩ := h1
    have hqf : q (τG f'') = τ f' := by
      rw [hf'']
      change q (ĝ * τG f * ĝ⁻¹) = τ f'
      rw [map_mul, map_mul, map_inv]
      exact hff'
    have hff'' : f'' = f' := hτinj hqf
    have := hrel f f'' hf''.symm
    rwa [hff''] at this


theorem ggKGLn_signedEltSC_projectiveSL {d p : ℕ} {K : Type} [Field K] [Finite K]
    (hp : p.Prime) (hp2 : p ≠ 2) (hpK0 : (p : K) ≠ 0) (hpq : p ∣ Nat.card K + 1)
    (hd : 0 < d) : GGTorusSignedEltSC p (projectiveSL d K) := by
  haveI : Nonempty K := ⟨0⟩
  have hpK' : ¬ p ∣ Nat.card K - 1 := SpNS.not_dvd_card_sub_one hp hp2 hpq
  refine ggKGLn_signedEltSC_of_centralQuotient hp (proj d K) (proj_surjective d K) ?_ ?_
    (ggKGLn_signedEltSC_specialLinear hp hp2 hpK0 hpq)
  · intro g hg
    rw [← scalars_eq_center]
    exact proj_eq_one_iff.mp hg
  · intro h
    exact hpK' (h.trans (card_center_specialLinear_dvd hd))

theorem ggKGLn_signedEltSC_linearNonsplit {d p : ℕ} {K : Type} [Field K] [Finite K]
    (hp : p.Prime) (hp2 : p ≠ 2) (hpK0 : (p : K) ≠ 0) (hpq : p ∣ Nat.card K + 1) (hd : 0 < d) :
    GGTorusSignedEltSC p (LargeEvenProj (LargeEvenSLGroup (Fin d) K)) :=
  ggTorusSignedEltSC_of_mulEquiv (TypeA.recipeEquiv d K)
    (ggKGLn_signedEltSC_projectiveSL hp hp2 hpK0 hpq hd)

end CFSG.StandardType
