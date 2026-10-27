module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKA6Sylow
public import CFSG.LocalAnalysis.StandardType.GGSixRCKA6F4Shape
public import CFSG.LocalAnalysis.StandardType.GGSixRCKA6Label
public import CFSG.LieType.Chevalley.AdjointCenter

public section

namespace CFSG.StandardType.RCKA6

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.StandardType
open CFSG.Blueprint.Chevalley (adjointGroup Tag)

@[expose] def RCKA6F4Center :
    Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n f : ℕ) (ψ : (ggU .F4 n f).K →* X) (p : ℕ)
    (G₀ D J : Subgroup X),
    GGPresentsG0 G₀ (ggU .F4 n f).D .F4 n f ψ → p.Prime → p ≠ 2 →
    D ≤ Subgroup.normalizer (G₀ : Set X) → (∀ d ∈ D, GGPsiInnerDiag (ggU .F4 n f).D ψ d) →
    IsElemAbelian p D → Nat.card D = p ^ 2 →
    IsComponentOf J (G₀ ⊓ Subgroup.centralizer (D : Set X)) →
    Odd (Nat.card (Subgroup.center ↥J)) → GGSixRCKJRow .A6 J →
    Subgroup.center ↥J = ⊥

theorem rckF4_center_three
    (X : Type) [Group X] [Finite X] (n : ℕ) (ψ : (ggU .F4 n 1).K →* X) (G₀ J : Subgroup X)
    (hr : ψ.range = G₀) (hk : ψ.ker ≤ Subgroup.center (ggU .F4 n 1).K) (hJG : J ≤ G₀)
    (hJ : ⁅J, J⁆ = J) {z : X} (hzJ : z ∈ J) (hzc : ∀ j ∈ J, z * j = j * z)
    (hz3 : orderOf z = 3) : False := by
  have hcenterK : Subgroup.center (ggU .F4 n 1).K = ⊥ := by
    change Subgroup.center ↥(CFSG.Blueprint.Chevalley.adjointGroup .F4 (GaloisField 2 1)) = ⊥
    exact CFSG.LieType.Chevalley.center_adjointGroup_eq_bot
  have hkerbot : ψ.ker = ⊥ := le_bot_iff.mp (hk.trans_eq hcenterK)
  have hinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    exact hkerbot
  let e : (ggU .F4 n 1).K ≃* ↥G₀ :=
    (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hr)
  let z' : ↥G₀ := ⟨z, hJG hzJ⟩
  let x : (ggU .F4 n 1).K := e.symm z'
  have hxdef : x = e.symm z' := rfl
  have hxord : orderOf x = 3 := by
    change orderOf (e.symm (⟨z, hJG hzJ⟩ : ↥G₀)) = 3
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hz3]
  let C : Subgroup (ggU .F4 n 1).K :=
    CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (MulAut.conj x)
  have hK2 : Nat.card (GaloisField 2 1) = 2 := by
    rw [GaloisField.card 2 1 (by norm_num)]
    norm_num
  have hcomp := CFSG.HardMathSupport.Dickson.Bal207.FamF42.compShape_conj_F4_two
    (K := GaloisField 2 1) hK2 x hxord
  have hshape := rckF4_comp_shape (K := GaloisField 2 1) hK2 x hxord
  have huniq : ∀ L L' : Subgroup (ggU .F4 n 1).K,
      CFSG.Open.IsComponentOf L C → CFSG.Open.IsComponentOf L' C → L = L' := hshape.1
  have hcenterC : ∀ L : Subgroup (ggU .F4 n 1).K,
      CFSG.Open.IsComponentOf L C → Subgroup.center ↥L = ⊥ := hshape.2
  have hJ''perf : ⁅J.subgroupOf G₀, J.subgroupOf G₀⁆ = J.subgroupOf G₀ := by
    apply Subgroup.map_injective G₀.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hJG]
    exact hJ
  have hJ'perf :
      ⁅(J.subgroupOf G₀).map (e.symm : ↥G₀ →* (ggU .F4 n 1).K),
        (J.subgroupOf G₀).map (e.symm : ↥G₀ →* (ggU .F4 n 1).K)⁆ =
      (J.subgroupOf G₀).map (e.symm : ↥G₀ →* (ggU .F4 n 1).K) := by
    rw [← Subgroup.map_commutator, hJ''perf]
  have hJ'fix :
      (J.subgroupOf G₀).map (e.symm : ↥G₀ →* (ggU .F4 n 1).K) ≤ C := by
    rintro y ⟨u, hu, rfl⟩
    change MulAut.conj x (e.symm u) = e.symm u
    rw [MulAut.conj_apply, hxdef]
    apply e.injective
    simp only [map_mul, map_inv, MulEquiv.apply_symm_apply]
    have huJ : (u : X) ∈ J := Subgroup.mem_subgroupOf.mp hu
    have hzu : z' * (⟨(u : X), hJG huJ⟩ : ↥G₀) =
        (⟨(u : X), hJG huJ⟩ : ↥G₀) * z' := Subtype.ext (hzc (u : X) huJ)
    have hu_eq : u = (⟨(u : X), hJG huJ⟩ : ↥G₀) := Subtype.ext rfl
    rw [hu_eq, hzu]
    group
  have hJ'le : (J.subgroupOf G₀).map (e.symm : ↥G₀ →* (ggU .F4 n 1).K) ≤
      CFSG.Open.GLALayer C := hcomp.layer _ hJ'fix hJ'perf
  have hxJ' : x ∈ (J.subgroupOf G₀).map (e.symm : ↥G₀ →* (ggU .F4 n 1).K) := by
    change ∃ a ∈ J.subgroupOf G₀, e.symm a = x
    exact ⟨z', Subgroup.mem_subgroupOf.mpr hzJ, hxdef.symm⟩
  by_cases hex : ∃ L : Subgroup (ggU .F4 n 1).K, CFSG.Open.IsComponentOf L C
  · obtain ⟨L, hL⟩ := hex
    have hle : CFSG.Open.GLALayer C ≤ L := by
      unfold CFSG.Open.GLALayer
      refine sSup_le ?_
      intro K hK
      exact le_of_eq (huniq K L hK hL)
    have hxL : x ∈ L := hle (hJ'le hxJ')
    have hxcomm : ∀ l ∈ L, x * l = l * x := by
      intro l hl
      have hconj : MulAut.conj x l = l := hL.1 hl
      rw [MulAut.conj_apply] at hconj
      calc x * l = (x * l * x⁻¹) * x := by group
        _ = l * x := by rw [hconj]
    have hxcenter : (⟨x, hxL⟩ : ↥L) ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro l
      apply Subtype.ext
      exact (hxcomm (l : (ggU .F4 n 1).K) l.2).symm
    have hx1 : x = 1 := by
      have hmem : (⟨x, hxL⟩ : ↥L) ∈ (⊥ : Subgroup ↥L) := (hcenterC L hL) ▸ hxcenter
      exact congrArg Subtype.val (Subgroup.mem_bot.mp hmem)
    rw [hx1] at hxord
    norm_num at hxord
  · push Not at hex
    have hbot : CFSG.Open.GLALayer C = ⊥ := by
      unfold CFSG.Open.GLALayer
      have hset : {K : Subgroup (ggU .F4 n 1).K | CFSG.Open.IsComponentOf K C} = ∅ := by
        ext K
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        exact hex K
      rw [hset, sSup_empty]
    have hxbot : x ∈ (⊥ : Subgroup (ggU .F4 n 1).K) := hbot ▸ (hJ'le hxJ')
    have hx1 : x = 1 := Subgroup.mem_bot.mp hxbot
    rw [hx1] at hxord
    norm_num at hxord

theorem rck_A6F4Center_of_f
    (hf1 : ∀ (X : Type) [Group X] [Finite X] (n f : ℕ) (ψ : (ggU .F4 n f).K →* X) (p : ℕ) (G₀ D J :
        Subgroup X), GGPresentsG0 G₀ (ggU .F4 n f).D .F4 n f ψ → p.Prime → p ≠ 2 → D ≤
        Subgroup.normalizer (G₀ : Set X) → (∀ d ∈ D, GGPsiInnerDiag (ggU .F4 n f).D ψ d) →
        IsElemAbelian p D → Nat.card D = p ^ 2 → IsComponentOf J (G₀ ⊓ Subgroup.centralizer (D : Set
        X)) → GGSixRCKJRow .A6 J → f = 1) : RCKA6F4Center := by
  intro X _ _ n f ψ p G₀ D J hG₀ hp hp2 hDN hdiag hD hD2 hJ hodd hrow
  have hf : f = 1 := hf1 X n f ψ p G₀ D J hG₀ hp hp2 hDN hdiag hD hD2 hJ hrow
  subst hf
  obtain ⟨⟨_, _⟩, ⟨hrange, hker⟩, _, _⟩ := hG₀
  have hJG : J ≤ G₀ := hJ.1.trans inf_le_left
  have hperfJ : commutator ↥J = ⊤ := (hJ.2.2).1
  have hJJ : ⁅J, J⁆ = J := by
    rw [← Subgroup.map_subtype_commutator J, hperfJ]
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  obtain ⟨lab, _hlab, R, _instR, _I, _F, θ, _hs, _hna, hP, hM⟩ :=
    largeEvenMarking_exists_markedModel hrow
  have htag : lab.tag = .B2der := by
    obtain ⟨t, l, nn⟩ := lab
    cases t <;> dsimp only [ggSixRCKLabelRow] at hP <;>
      (try split_ifs at hP) <;>
      first
        | rfl
        | exact absurd hP (by decide)
  obtain ⟨eR⟩ := nonempty_alternatingGroup_of_markedModel_b2der htag hM
  have eA6 : (↥J ⧸ Subgroup.center ↥J) ≃* alternatingGroup (Fin 6) := θ.trans eR
  by_contra hne
  obtain ⟨w, hw, hw1⟩ :=
    (Subgroup.bot_or_exists_ne_one (Subgroup.center ↥J)).resolve_left hne
  have hword1 : orderOf w ≠ 1 := fun h => hw1 (orderOf_eq_one_iff.mp h)
  obtain ⟨r, hrprime, hrdvd⟩ := Nat.exists_prime_and_dvd hword1
  have hw'mem : w ^ (orderOf w / r) ∈ Subgroup.center ↥J :=
    (Subgroup.center ↥J).pow_mem hw _
  have hw'ord : orderOf (w ^ (orderOf w / r)) = r :=
    orderOf_pow_orderOf_div ((isOfFinOrder_of_finite w).orderOf_pos).ne' hrdvd
  have hword_odd : Odd (orderOf w) :=
    Odd.of_dvd_nat hodd (Subgroup.orderOf_dvd_natCard (Subgroup.center ↥J) hw)
  have hr_odd : Odd r := Odd.of_dvd_nat hword_odd hrdvd
  by_cases hr3 : r = 3
  · have hz3 : orderOf ((w ^ (orderOf w / r) : ↥J) : X) = 3 := by
      rw [Subgroup.orderOf_coe, hw'ord, hr3]
    have hzc : ∀ j ∈ J, ((w ^ (orderOf w / r) : ↥J) : X) * j =
        j * ((w ^ (orderOf w / r) : ↥J) : X) := by
      intro j hj
      have hcomm := Subgroup.mem_center_iff.1 hw'mem (⟨j, hj⟩ : ↥J)
      exact (congrArg Subtype.val hcomm).symm
    exact rckF4_center_three X n ψ G₀ J hrange hker hJG hJJ
      (w ^ (orderOf w / r)).2 hzc hz3
  · have hr5 : 5 ≤ r := by
      obtain ⟨k, hk⟩ := hr_odd
      have h2 : 2 ≤ r := hrprime.two_le
      omega
    have hcyc : ∀ P : Sylow r (↥J ⧸ Subgroup.center ↥J), IsCyclic P := by
      intro P
      haveI : Fact r.Prime := ⟨hrprime⟩
      exact rckF4_A6_sylow_isCyclic eA6 hr5 P
    exact rckF4_no_center_prime_of_isCyclic hperfJ hrprime hcyc hw'mem hw'ord

end CFSG.StandardType.RCKA6
