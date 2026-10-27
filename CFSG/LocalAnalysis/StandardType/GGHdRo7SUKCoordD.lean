module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7SUKCoordA
import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherClassicalRk2U3
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyUCoord

public section

namespace CFSG.StandardType.HdRo7SU

open CFSG.StandardType.HdRo7C
open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem hdRo7SUKCoordAux_sumZeroCard (d p : ℕ) (hp : p.Prime) (hd : 1 ≤ d) :
    Nat.card ↥(UCoord.sumZero d p) = p ^ (d - 1) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  let f : (Fin d → ZMod p) →ₗ[ZMod p] ZMod p := ∑ i, LinearMap.proj (R := ZMod p) i
  have hf : ∀ v : Fin d → ZMod p, f v = ∑ i, v i := by
    intro v
    simp only [f, LinearMap.sum_apply, LinearMap.proj_apply]
  have hsurj : Function.Surjective f := by
    intro x
    refine ⟨Pi.single ⟨0, hd⟩ x, ?_⟩
    rw [hf]
    simp [Pi.single_apply]
  have hfr : Module.finrank (ZMod p) f.range = 1 := by
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_self]
  have hker : Module.finrank (ZMod p) f.ker = d - 1 := by
    have h := LinearMap.finrank_range_add_finrank_ker f
    rw [hfr, Module.finrank_fin_fun] at h
    omega
  have hcard : Nat.card ↥f.ker = p ^ (d - 1) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod p) (V := ↥f.ker),
      show Module.finrank (ZMod p) ↥f.ker = d - 1 from hker, Nat.card_zmod]
  rw [← hcard]
  refine Nat.card_congr ?_
  refine
    { toFun := fun x => ⟨fun i => Multiplicative.toAdd (x.1 i), ?_⟩
      invFun := fun x => ⟨fun i => Multiplicative.ofAdd (x.1 i), ?_⟩
      left_inv := fun x => by ext i; simp
      right_inv := fun x => by ext i; simp }
  · rw [LinearMap.mem_ker, hf]
    exact UCoord.mem_sumZero.mp x.2
  · rw [UCoord.mem_sumZero]
    have h := LinearMap.mem_ker.mp x.2
    rw [hf] at h
    simpa using h

theorem hdRo7SUKCoordAux_mem_map_comm {G H : Type} [Group G] [Group H]
    {E : Subgroup G} (f : G →* H) (hE : IsMulCommutative ↥E)
    {a b : H} (ha : a ∈ E.map f) (hb : b ∈ E.map f) : a * b = b * a := by
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp ha
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hb
  rw [← map_mul, ← map_mul]
  exact congrArg f (congrArg Subtype.val
    (isMulCommutative_iff.mp hE ⟨x, hx⟩ ⟨y, hy⟩))

theorem hdRo7SUKCoordAux_mem_map_pow {G H : Type} [Group G] [Group H] {p : ℕ}
    {E : Subgroup G} (f : G →* H) (hE : ∀ x ∈ E, x ^ p = 1)
    {a : H} (ha : a ∈ E.map f) : a ^ p = 1 := by
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp ha
  rw [← map_pow, hE x hx, map_one]

theorem hdRo7SUKCoordAux_isElemAbelian_map {G H : Type} [Group G] [Group H] {p : ℕ}
    {E : Subgroup G} (f : G →* H) (hE : CFSG.Open.IsElemAbelian p E) :
    CFSG.Open.IsElemAbelian p (E.map f) := by
  refine ⟨?_, ?_⟩
  · rw [isMulCommutative_iff]
    intro a b
    apply Subtype.ext
    exact hdRo7SUKCoordAux_mem_map_comm f hE.1 a.2 b.2
  · intro a ha
    exact hdRo7SUKCoordAux_mem_map_pow (p := p) f hE.2 ha

theorem hdRo7SUKCoordAux_inf_center_eq_bot
    {G : Type} [Group G] [Finite G]
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hRig : GGLabelRigidInput)
    (hrow : GGResRowAt ggRowSUCorank2 p J K) :
    ∀ z ∈ Bs, z ∈ K → z ∈ Subgroup.centralizer (K : Set G) → z = 1 := by
  have hp3 : p = 3 := (hdRo7SUKCoordAux_rowRank_spec hrow).1
  have hp : Nat.Prime p := by rw [hp3]; exact Nat.prime_three
  haveI : Fact p.Prime := ⟨hp⟩
  have hcop : Nat.Coprime p (Nat.card (Subgroup.center ↥K)) := by
    rw [hp3]; exact hdRo7SUKCoordAux_centerCoprime hH hRig hrow
  have hpBs : CFSG.Open.IsElemAbelian p Bs := hH.1.2.1.2.1
  intro z hzB hzK hzC
  have hzp : z ^ p = 1 := hpBs.2 z hzB
  have hordp : orderOf z ∣ p := orderOf_dvd_iff_pow_eq_one.mpr hzp
  have hzcen : (⟨z, hzK⟩ : ↥K) ∈ Subgroup.center ↥K := by
    rw [Subgroup.mem_center_iff]
    intro w
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp hzC (w : G) w.2
  have hordZ : orderOf z ∣ Nat.card (Subgroup.center ↥K) := by
    have h1 : orderOf (⟨⟨z, hzK⟩, hzcen⟩ : Subgroup.center ↥K) ∣
        Nat.card ↥(Subgroup.center ↥K) := orderOf_dvd_natCard _
    rwa [Subgroup.orderOf_mk, Subgroup.orderOf_mk] at h1
  have hg1 : orderOf z = 1 := by
    have h2 : orderOf z ∣ p.gcd (Nat.card (Subgroup.center ↥K)) := Nat.dvd_gcd hordp hordZ
    rw [hcop.gcd_eq_one] at h2
    exact Nat.dvd_one.mp h2
  exact orderOf_eq_one_iff.mp hg1

theorem hdRo7SUKCoordAux_infFrame
    {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hRig : GGLabelRigidInput)
    (hrow : GGResRowAt ggRowSUCorank2 p J K) :
    Nonempty (↥(UCoord.sumZero (hdRo7SUKCoordAux_rowRank hrow) p) ≃* ↥(Bs ⊓ K)) := by
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
      (hdRo7SUKCoordAux_inf_center_eq_bot hH hRig hrow (t : G) (Subgroup.mem_inf.mp t.2).1 (Subgroup.mem_inf.mp t.2).2 hzC)
  let E : Subgroup R := φ.range
  have hEab : CFSG.Open.IsElemAbelian p E := by
    refine isElemAbelian_range (fun a b => ?_) (fun a => ?_) φ
    · exact Subtype.ext (congrArg (fun x : ↥Bs => (x : G))
        (isMulCommutative_iff.mp hBsE.1 ⟨a.1, (Subgroup.mem_inf.mp a.2).1⟩
          ⟨b.1, (Subgroup.mem_inf.mp b.2).1⟩))
    · apply Subtype.ext
      show (a.1 : G) ^ p = 1
      exact hBsE.2 a.1 (Subgroup.mem_inf.mp a.2).1
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
  have hKcard : Nat.card F = (2 ^ 1) ^ 2 := by rw [hFcard]; norm_num
  obtain ⟨τ, hτinj, hτrange, _hτperm⟩ :=
    Rk2U3.exists_frameTorus hKcard le_rfl hp (by rw [hp3]; norm_num)
    (by rw [hp3]; exact hm3d) hEab hscE
  have hτrangeE : τ.range = φ.range := by rw [hτrange]
  let eτ : ↥(UCoord.sumZero m p) ≃* E :=
    (MonoidHom.ofInjective hτinj).trans (MulEquiv.subgroupCongr hτrangeE)
  let eφ : ↥T ≃* E := MonoidHom.ofInjective hφinj
  exact ⟨eτ.trans eφ.symm⟩

end CFSG.StandardType.HdRo7SU