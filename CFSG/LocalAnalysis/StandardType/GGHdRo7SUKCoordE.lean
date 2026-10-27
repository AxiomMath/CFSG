module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7SUKCoordC
import CFSG.LocalAnalysis.StandardType.GGHdRo7SULCoordTorusA

public section

namespace CFSG.StandardType.HdRo7SU

open CFSG.StandardType.HdRo7C
open CFSG.Assembly
open CFSG.StandardType.UCoord

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem hdRo7SUKCoordAux_permData
    {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hRig : GGLabelRigidInput)
    (hrow : GGResRowAt ggRowSUCorank2 p J K) :
    ∃ e : ↥(sumZero (hdRo7SUKCoordAux_rowRank hrow) p) ≃* ↥(Bs ⊓ K),
      (∀ σ : Equiv.Perm (Fin (hdRo7SUKCoordAux_rowRank hrow)),
        ∃ w ∈ K, ∀ f : ↥(sumZero (hdRo7SUKCoordAux_rowRank hrow) p),
          (w : G) * (e f : G) * (w : G)⁻¹ = (e (permAutV σ f) : G)) ∧
      (∀ g ∈ K, (∀ t : ↥(Bs ⊓ K), ∃ t' : ↥(Bs ⊓ K),
          (g : G) * (t : G) * (g : G)⁻¹ = (t' : G)) →
        ∃ π : Equiv.Perm (Fin (hdRo7SUKCoordAux_rowRank hrow)),
          ∀ f : ↥(sumZero (hdRo7SUKCoordAux_rowRank hrow) p),
            (g : G) * (e f : G) * (g : G)⁻¹ = (e (permAutV π f) : G)) := by
  obtain ⟨F, hF, hFfin, θ, I, hFcard, hm3, hm3d, hnorm, hprop⟩ :=
    hdRo7SUKCoordAux_markingData_rowRank hH hRig hrow
  let m := hdRo7SUKCoordAux_rowRank hrow
  have hp3 : p = 3 := (hdRo7SUKCoordAux_rowRank_spec hrow).1
  have hp : Nat.Prime p := by rw [hp3]; exact Nat.prime_three
  haveI : Fact p.Prime := ⟨hp⟩
  have hBsE : CFSG.Open.IsElemAbelian p Bs := hH.1.2.1.2.1
  have hBsSC : ∀ z ∈ Subgroup.centralizer (Bs : Set G), z ^ p = 1 → z ∈ Bs :=
    hH.1.2.1.2.2.2
  have hcop : Nat.Coprime p (Nat.card (Subgroup.center ↥K)) := by
    rw [hp3]; exact hdRo7SUKCoordAux_centerCoprime hH hRig hrow
  have hnotdvd : ¬ p ∣ Nat.card (Subgroup.center ↥K) :=
    (Nat.Prime.coprime_iff_not_dvd hp).mp hcop
  let R := LargeEvenProj (LargeEvenSUGroup (Fin m) F 2)
  let ψ : ↥K →* R := θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥K))
  let T : Subgroup G := Bs ⊓ K
  let incl : ↥T →* ↥K := Subgroup.inclusion (fun _ hx => hx.2)
  let φ : ↥T →* R := ψ.comp incl
  have hψsurj : Function.Surjective ψ :=
    θ.surjective.comp (QuotientGroup.mk'_surjective (Subgroup.center ↥K))
  have hker_psi : ψ.ker = Subgroup.center ↥K := by
    ext z
    rw [MonoidHom.mem_ker]
    show θ (QuotientGroup.mk' (Subgroup.center ↥K) z) = 1 ↔ z ∈ Subgroup.center ↥K
    rw [← map_one θ, θ.injective.eq_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hφinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
    intro t ht
    rw [MonoidHom.mem_ker] at ht
    have htK : incl t ∈ Subgroup.center ↥K := by
      rw [← hker_psi, MonoidHom.mem_ker]
      exact ht
    have hzC : (t : G) ∈ Subgroup.centralizer (K : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      have h := Subgroup.mem_center_iff.mp htK (⟨l, hl⟩ : ↥K)
      simpa [incl] using congrArg Subtype.val h
    exact Subtype.ext
      (hdRo7SUKCoordAux_inf_center_eq_bot hH hRig hrow (t : G) (Subgroup.mem_inf.mp t.2).1
        (Subgroup.mem_inf.mp t.2).2 hzC)
  let E : Subgroup R := φ.range
  have hEab : CFSG.Open.IsElemAbelian p E := by
    refine isElemAbelian_range (fun a b => ?_) (fun a => ?_) φ
    · exact Subtype.ext (congrArg (fun x : ↥Bs => (x : G))
        (isMulCommutative_iff.mp hBsE.1 ⟨a.1, (Subgroup.mem_inf.mp a.2).1⟩
          ⟨b.1, (Subgroup.mem_inf.mp b.2).1⟩))
    · apply Subtype.ext
      show (a.1 : G) ^ p = 1
      exact hBsE.2 a.1 (Subgroup.mem_inf.mp a.2).1
  have hEcard : Nat.card ↥E = Nat.card ↥T :=
    (Nat.card_congr (MonoidHom.ofInjective hφinj).toEquiv).symm
  have h3 : p ^ 3 ≤ Nat.card ↥E := by
    rw [hEcard, show Nat.card ↥T = p ^ (hdRo7SUKCoordAux_rowRank hrow - 1) from
      hdRo7SUKCoordAux_torusLower hH hRig hrow]
    exact Nat.pow_le_pow_right hp.one_le (by omega)
  have hpowT : ∀ t : ↥T, (incl t) ^ p = 1 := by
    intro t
    apply Subtype.ext
    show (incl t : G) ^ p = 1
    rw [Subgroup.coe_inclusion]
    exact hBsE.2 (t : G) (Subgroup.mem_inf.mp t.2).1
  have hscE : ∀ g : R, (∀ e ∈ E, g * e = e * g) → g ^ p = 1 → g ∈ E := by
    intro g hgcen hgp
    obtain ⟨n, hn, hnp⟩ := exists_lift_pow_eq_one hp hψsurj (by rw [hker_psi]) hnotdvd
      (g := g) hgp
    have hnC : (n : G) ∈ Subgroup.centralizer (Bs : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      obtain ⟨t, ht, c, hc, hbc⟩ := hdRo7SUKCoordAux_split hH hRig hrow b hb
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
      simpa using congrArg (fun x : ↥K => (x : G)) hnp
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
  have hkey : ∀ (σ : Equiv.Perm (Fin m)) (w : R) (l : ↥K), ψ l = w →
      (∀ f, w * τ f * w⁻¹ = τ (permAutV σ f)) →
      ∀ f, (l : G) * (e f : G) * (l : G)⁻¹ = (e (permAutV σ f) : G) := by
    intro σ w l hl hw f
    have hψeq : ψ (l * incl (e f) * l⁻¹) = ψ (incl (e (permAutV σ f))) := by
      rw [map_mul, map_mul, map_inv, hl]
      change w * φ (e f) * w⁻¹ = φ (e (permAutV σ f))
      rw [heφ f, heφ (permAutV σ f), hw f]
    have h1 : (l * incl (e f) * l⁻¹) ^ p = 1 := by
      rw [conj_pow, hpowT (e f), mul_one, mul_inv_cancel]
    have heq := eq_of_lift_pow_eq_one hp (by rw [hker_psi]) hnotdvd hψeq h1
      (hpowT (e (permAutV σ f)))
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv, incl, Subgroup.coe_inclusion] using
      congrArg Subtype.val heq
  refine ⟨e, ?_, ?_⟩
  · intro σ
    obtain ⟨w, hw⟩ := hτperm σ
    obtain ⟨l, hl⟩ := hψsurj w
    exact ⟨(l : G), l.2, hkey σ w l hl hw⟩
  · intro g hgK hgnorm
    let l : ↥K := ⟨g, hgK⟩
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
