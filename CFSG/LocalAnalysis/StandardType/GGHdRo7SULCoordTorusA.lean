module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7SULCoordModelA
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyUCoord

public section

namespace CFSG.StandardType.HdRo7SU

open CFSG.StandardType.HdRo7C
open CFSG.Assembly
open CFSG.StandardType.UCoord

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem hdRo7SULCoordAux_card_inf_geCfg
    {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hH : GGHdRo7SULCoordHyp p B Bs x L D J) (hRig : GGLabelRigidInput)
    (hrow : GGHdRo7SULabL p L) :
    p ^ 3 ≤ Nat.card ↥(Bs ⊓ L) := by
  obtain ⟨hp, hBsE, hxBs, hLx, h4⟩ := GGConfig.tableB_facts hH.1
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, -, hp3, -, -⟩ := hdRo7SULCoordAux_rowDataCfg hH hrow
  obtain ⟨-, -, -, -, -, -, hSStar, -⟩ := hH.1.1
  have hxne : x ≠ 1 := hSStar.2.2.1
  let C := Subgroup.centralizer (L : Set G)
  have hCeq : Bs ⊓ C = Subgroup.zpowers x := hdRo7SULCoordAux_centralizerCfg hH hp3
  have hCcard : Nat.card ↥(Bs ⊓ C) = p := by
    rw [hCeq, Nat.card_zpowers, orderOf_eq_prime (hBsE.2 x hxBs) hxne]
  have hcard_split : Nat.card ↥Bs ≤ Nat.card ↥(Bs ⊓ L) * Nat.card ↥(Bs ⊓ C) := by
    let f : ↥(Bs ⊓ L) × ↥(Bs ⊓ C) → ↥Bs :=
      fun q => ⟨(q.1 : G) * (q.2 : G), Bs.mul_mem q.1.2.1 q.2.2.1⟩
    have hf : Function.Surjective f := by
      rintro ⟨b, hb⟩
      obtain ⟨t, ht, c, hc, hbc⟩ := hdRo7SULCoordAux_splitCfg hH hRig hrow b hb
      exact ⟨(⟨t, ht⟩, ⟨c, hc⟩), Subtype.ext hbc.symm⟩
    calc Nat.card ↥Bs ≤ Nat.card (↥(Bs ⊓ L) × ↥(Bs ⊓ C)) :=
          Nat.card_le_card_of_surjective f hf
      _ = Nat.card ↥(Bs ⊓ L) * Nat.card ↥(Bs ⊓ C) := Nat.card_prod _ _
  have hle : p ^ 3 * p ≤ Nat.card ↥(Bs ⊓ L) * p := by
    calc p ^ 3 * p = p ^ 4 := by ring
      _ ≤ Nat.card ↥Bs := h4
      _ ≤ Nat.card ↥(Bs ⊓ L) * Nat.card ↥(Bs ⊓ C) := hcard_split
      _ = Nat.card ↥(Bs ⊓ L) * p := by rw [hCcard]
  exact Nat.le_of_mul_le_mul_right hle hp.pos

theorem hdRo7SULCoordAux_permEltSC_recipe {m : ℕ} (F : Type) [Field F] [Finite F]
    (hFcard : Nat.card F = 4) (hm3 : 3 ≤ m) (hm3d : ¬ 3 ∣ m) :
    GGTorusPermEltSC 3 m (LargeEvenProj (LargeEvenSUGroup (Fin m) F (2 ^ 1))) := by
  have hK : Nat.card F = (2 ^ 1) ^ 2 := by rw [hFcard]; norm_num
  exact UModel.ggTorusPermEltSC_unitary hK le_rfl (by omega) Nat.prime_three (by norm_num)
    (by norm_num) hm3d

theorem hdRo7SULCoordAux_permDataCfg
    {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hH : GGHdRo7SULCoordHyp p B Bs x L D J) (hRig : GGLabelRigidInput)
    (hrow : GGHdRo7SULabL p L) :
    ∃ (m : ℕ) (e : ↥(sumZero m p) ≃* ↥(Bs ⊓ L)),
      p = 3 ∧ 7 ≤ m ∧ ¬ 3 ∣ m ∧
      (∀ σ : Equiv.Perm (Fin m), ∃ w ∈ L, ∀ f : ↥(sumZero m p),
        (w : G) * (e f : G) * (w : G)⁻¹ = (e (permAutV σ f) : G)) ∧
      (∀ g ∈ L, (∀ t : ↥(Bs ⊓ L), ∃ t' : ↥(Bs ⊓ L),
          (g : G) * (t : G) * (g : G)⁻¹ = (t' : G)) →
        ∃ π : Equiv.Perm (Fin m), ∀ f : ↥(sumZero m p),
          (g : G) * (e f : G) * (g : G)⁻¹ = (e (permAutV π f) : G)) := by
  obtain ⟨m, F, hF, hFfin, θ, I, hFcard, hm7, hm3d, hnorm, hprop, -⟩ :=
    hdRo7SULCoordAux_markingDataCfg hH hRig hrow
  obtain ⟨-, -, hp3, -, -⟩ := hdRo7SULCoordAux_rowDataCfg hH hrow
  have hp : Nat.Prime p := by rw [hp3]; exact Nat.prime_three
  haveI : Fact p.Prime := ⟨hp⟩
  have hBsE : IsElemAbelian p Bs := hH.1.2.1.2.1
  have hBsSC : ∀ z ∈ Subgroup.centralizer (Bs : Set G), z ^ p = 1 → z ∈ Bs :=
    hH.1.2.1.2.2.2
  have hcop : Nat.Coprime p (Nat.card (Subgroup.center ↥L)) := by
    rw [hp3]; exact hdRo7SULCoordAux_centerCoprimeCfg hH hRig hrow
  have hnotdvd : ¬ p ∣ Nat.card (Subgroup.center ↥L) :=
    (Nat.Prime.coprime_iff_not_dvd hp).mp hcop
  let R := LargeEvenProj (LargeEvenSUGroup (Fin m) F 2)
  let ψ : ↥L →* R := θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥L))
  let T : Subgroup G := Bs ⊓ L
  let incl : ↥T →* ↥L := Subgroup.inclusion (fun _ hx => hx.2)
  let φ : ↥T →* R := ψ.comp incl
  have hψsurj : Function.Surjective ψ :=
    θ.surjective.comp (QuotientGroup.mk'_surjective (Subgroup.center ↥L))
  have hker_psi : ψ.ker = Subgroup.center ↥L := by
    ext z
    rw [MonoidHom.mem_ker]
    show θ (QuotientGroup.mk' (Subgroup.center ↥L) z) = 1 ↔ z ∈ Subgroup.center ↥L
    rw [← map_one θ, θ.injective.eq_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hφinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
    intro t ht
    rw [MonoidHom.mem_ker] at ht
    have htL : incl t ∈ Subgroup.center ↥L := by
      rw [← hker_psi, MonoidHom.mem_ker]
      exact ht
    have hzC : (t : G) ∈ Subgroup.centralizer (L : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      have h := Subgroup.mem_center_iff.mp htL (⟨l, hl⟩ : ↥L)
      simpa [incl] using congrArg Subtype.val h
    exact Subtype.ext (hdRo7SULCoordAux_inf_center_eq_botCfg hH hRig hrow (t : G) t.2.1 t.2.2 hzC)
  let E : Subgroup R := φ.range
  have hEab : IsElemAbelian p E := by
    refine isElemAbelian_range (fun a b => ?_) (fun a => ?_) φ
    · exact Subtype.ext (hBsE.comm a.2.1 b.2.1)
    · exact Subtype.ext (by simpa using hBsE.2 (a : G) a.2.1)
  have hEcard : Nat.card ↥E = Nat.card ↥T :=
    (Nat.card_congr (MonoidHom.ofInjective hφinj).toEquiv).symm
  have h3 : p ^ 3 ≤ Nat.card E := by
    rw [hEcard]
    exact hdRo7SULCoordAux_card_inf_geCfg hH hRig hrow
  have hpowT : ∀ t : ↥T, (incl t) ^ p = 1 := by
    intro t
    apply Subtype.ext
    show (incl t : G) ^ p = 1
    rw [Subgroup.coe_inclusion]
    exact hBsE.2 (t : G) t.2.1
  have hscE : ∀ g : R, (∀ e ∈ E, g * e = e * g) → g ^ p = 1 → g ∈ E := by
    intro g hgcen hgp
    obtain ⟨n, hn, hnp⟩ := exists_lift_pow_eq_one hp hψsurj (by rw [hker_psi]) hnotdvd
      (g := g) hgp
    have hnC : (n : G) ∈ Subgroup.centralizer (Bs : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      obtain ⟨t, ht, c, hc, hbc⟩ := hdRo7SULCoordAux_splitCfg hH hRig hrow b hb
      let tT : ↥T := ⟨t, ht⟩
      have hcomm : ψ n * ψ (incl tT) = ψ (incl tT) * ψ n := by
        have h1 : g * φ tT = φ tT * g :=
          hgcen (φ tT) (MonoidHom.mem_range.mpr ⟨tT, rfl⟩)
        rw [← hn] at h1
        simpa only [φ, MonoidHom.comp_apply] using h1
      have hnt : n * incl tT = incl tT * n :=
        commute_of_lift_pow_eq_one hp (by rw [hker_psi]) hnotdvd hcomm (hpowT tT)
      have hntG : (n : G) * t = t * (n : G) := by
        simpa [incl, tT] using congrArg Subtype.val hnt
      have hnc : (n : G) * (c : G) = (c : G) * (n : G) :=
        Subgroup.mem_centralizer_iff.mp hc.2 (n : G) n.2
      rw [hbc]
      calc (t * (c : G)) * (n : G) = t * ((c : G) * (n : G)) := by group
        _ = t * ((n : G) * (c : G)) := by rw [← hnc]
        _ = (t * (n : G)) * (c : G) := by group
        _ = ((n : G) * t) * (c : G) := by rw [hntG]
        _ = (n : G) * (t * (c : G)) := by group
    have hnpG : (n : G) ^ p = 1 := by
      simpa using congrArg (fun x : ↥L => (x : G)) hnp
    have hnBs : (n : G) ∈ Bs := hBsSC (n : G) hnC hnpG
    have hnT : (n : G) ∈ T := ⟨hnBs, n.2⟩
    refine ⟨⟨(n : G), hnT⟩, ?_⟩
    show φ ⟨(n : G), hnT⟩ = g
    have hsub : incl (⟨(n : G), hnT⟩ : ↥T) = n := Subtype.ext rfl
    rw [show φ ⟨(n : G), hnT⟩ = ψ (incl ⟨(n : G), hnT⟩) from rfl, hsub, hn]
  have hTSC : GGTorusPermEltSC p m R := by
    rw [hp3]
    exact hdRo7SULCoordAux_permEltSC_recipe (m := m) F hFcard (by omega) hm3d
  obtain ⟨τ, hτinj, hτrange, hτperm, hτnorm⟩ := hTSC E hEab h3 hscE
  let eτ : ↥(sumZero m p) ≃* E :=
    (MonoidHom.ofInjective hτinj).trans (MulEquiv.subgroupCongr hτrange)
  let eφ : ↥T ≃* E := MonoidHom.ofInjective hφinj
  let e : ↥(sumZero m p) ≃* ↥T := eτ.trans eφ.symm
  have heφ : ∀ f : ↥(sumZero m p), φ (e f) = τ f := by
    intro f
    have h1 : eφ (e f) = eτ f := by
      change eφ (eφ.symm (eτ f)) = eτ f
      rw [MulEquiv.apply_symm_apply]
    have h2 : (eφ (e f) : R) = (eτ f : R) := congrArg Subtype.val h1
    rw [show (eφ (e f) : R) = φ (e f) from rfl, show (eτ f : R) = τ f from rfl] at h2
    exact h2
  have hkey : ∀ (σ : Equiv.Perm (Fin m)) (w : R) (l : ↥L), ψ l = w →
      (∀ f, w * τ f * w⁻¹ = τ (permAutV σ f)) →
      ∀ f, (l : G) * (e f : G) * (l : G)⁻¹ = (e (permAutV σ f) : G) := by
    intro σ w l hl hw f
    have hψeq : ψ (l * incl (e f) * l⁻¹) =
        ψ (incl (e (permAutV σ f))) := by
      rw [map_mul, map_mul, map_inv, hl]
      change w * φ (e f) * w⁻¹ = φ (e (permAutV σ f))
      rw [heφ f, heφ (permAutV σ f), hw f]
    have h1 : (l * incl (e f) * l⁻¹) ^ p = 1 := by
      rw [conj_pow, hpowT (e f), mul_one, mul_inv_cancel]
    have heq := eq_of_lift_pow_eq_one hp (by rw [hker_psi]) hnotdvd hψeq h1
      (hpowT (e (permAutV σ f)))
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv, incl, Subgroup.coe_inclusion] using
      congrArg Subtype.val heq
  refine ⟨m, e, hp3, hm7, hm3d, ?_, ?_⟩
  · intro σ
    obtain ⟨w, hw⟩ := hτperm σ
    obtain ⟨l, hl⟩ := hψsurj w
    exact ⟨(l : G), l.2, hkey σ w l hl hw⟩
  · intro g hgL hgnorm
    let l : ↥L := ⟨g, hgL⟩
    let w : R := ψ l
    have hwE : ∀ x ∈ E, w * x * w⁻¹ ∈ E := by
      intro x hx
      obtain ⟨t, rfl⟩ := hx
      obtain ⟨t', ht'⟩ := hgnorm t
      refine ⟨t', ?_⟩
      have hlt' : l * incl t * l⁻¹ = incl t' := by
        apply Subtype.ext
        show (l : G) * (t : G) * (l : G)⁻¹ = (t' : G)
        simpa only [incl, Subgroup.coe_inclusion] using ht'
      have hval : ψ (incl t') = w * φ t * w⁻¹ := by
        rw [← hlt', map_mul, map_mul, map_inv]
        rfl
      exact hval
    obtain ⟨π, hπ⟩ := hτnorm w hwE
    exact ⟨π, hkey π w l rfl hπ⟩

end CFSG.StandardType.HdRo7SU

end
