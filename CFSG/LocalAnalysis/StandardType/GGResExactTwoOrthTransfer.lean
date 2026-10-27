module

public import CFSG.LocalAnalysis.StandardType.GGResExactTwoOrthSmallDefs
import CFSG.LocalAnalysis.StandardType.GGHdRo7DKSqueezeAux
import CFSG.LocalAnalysis.StandardType.GGHdRo7DFrameOmega
import CFSG.LocalAnalysis.StandardType.GGHdRo7DSideData
import CFSG.LocalAnalysis.StandardType.GGHdRo7CoprimeSplit
import CFSG.LocalAnalysis.StandardType.GGTableBBstar
import CFSG.LocalAnalysis.StandardType.GGTBTorRelDCoverTwo
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyOrthTorus
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut
import CFSG.RankThree.PartOne.S11d.LieFieldTransfer
import CFSG.GroupTheory.PCore.PCoreOfMulEquiv
import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem ggResX2TrAux_charSum_qPlus (K : Type) [Field K] [Finite K] [CharP K 2]
    (hK2 : Nat.card K = 2) (m : ℕ) (hm : 1 ≤ m) :
    OrdPNsOm.charSum (TableBOrth.qPlusForm K m) ⊤ = (2 : ℤ) ^ m := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  rw [OrthTorus.charSum_qPlusForm, hK2]
  norm_num

private theorem ggResX2TrAux_charSum_qMinus (K : Type) [Field K] [Finite K] [CharP K 2]
    (hK2 : Nat.card K = 2) (m : ℕ) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    OrdPNsOm.charSum (TableBOrth.qMinusForm K m b c) ⊤ = -((2 : ℤ) ^ (m + 1)) := by
  obtain ⟨h0, -⟩ := OrthTorus.charSum_qMinusForm (K := K) (m := m) hirr
  rw [h0, hK2]
  norm_num

private theorem ggResX2TrAux_model {R : Type} [Group R] {lab : LargeEvenLabel}
    (hhas : GGHasLabel lab R) (htag : lab.tag = .D ∨ lab.tag = .twD) (hn : lab.n = 1)
    (hr : 4 ≤ lab.rank) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2) (V : Type) (_ : AddCommGroup V)
      (_ : Module F V) (_ : FiniteDimensional F V) (Q : QuadraticForm F V),
      Nat.card F = 2 ∧ (QuadraticMap.polarBilin Q).Nondegenerate ∧
      Module.finrank F V = 2 * lab.rank ∧
      ((lab.tag = .D ∧ OrdPNsOm.charSum Q ⊤ = (2 : ℤ) ^ lab.rank) ∨
        (lab.tag = .twD ∧ OrdPNsOm.charSum Q ⊤ = -((2 : ℤ) ^ lab.rank))) ∧
      Nonempty (R ≃* ↥(CFSG.RankThree.Classical2.orthDerived Q)) := by
  have hrank : lab.rank = (lab.rank - 1) + 1 := by omega
  have hr3 : lab.rank ≠ 3 := by omega
  have hr2 : lab.rank ≠ 2 := by omega
  have hraw := hhas
  rcases htag with hD | hD
  · simp only [GGHasLabel, CFSG.StandardType.LargeEvenRawDatum, hD, ite_eq_right hr3] at hraw
    obtain ⟨K, hKfield, hKfin, hKcard, hdata⟩ := hraw
    let : Field K := hKfield
    let : Finite K := hKfin
    have hK2 : Nat.card K = 2 := by rw [hKcard, hn]; norm_num
    have hKchar : CharP K 2 :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
        (k := 1) Nat.prime_two (by norm_num) (by rw [hK2]; norm_num)
    let : CharP K 2 := hKchar
    have hfin : Module.finrank K (Fin lab.rank ⊕ Fin lab.rank → K) = 2 * lab.rank := by
      rw [Module.finrank_fintype_fun_eq_card (R := K) (η := Fin lab.rank ⊕ Fin lab.rank)]
      simp only [Fintype.card_sum, Fintype.card_fin]
      omega
    have hchar : OrdPNsOm.charSum (TableBOrth.qPlusForm K lab.rank) ⊤ = (2 : ℤ) ^ lab.rank :=
      ggResX2TrAux_charSum_qPlus K hK2 lab.rank (by omega)
    exact ⟨K, hKfield, hKfin, inferInstance, Fin lab.rank ⊕ Fin lab.rank → K, inferInstance,
      inferInstance, inferInstance, TableBOrth.qPlusForm K lab.rank, hK2,
      TableBOrth.nondegenerate_qPlusForm lab.rank, hfin, Or.inl ⟨hD, hchar⟩,
      ⟨hdata.some.trans (OrthTorus.rPlusEquiv K (by omega))⟩⟩
  · have hn2 : lab.rank ≠ 2 := by omega
    simp only [GGHasLabel, CFSG.StandardType.LargeEvenRawDatum, hD, ite_eq_right hr2,
      ite_eq_right hr3] at hraw
    obtain ⟨K, hKfield, hKfin, hKcard, b, c, hirr, hdata⟩ := hraw
    let : Field K := hKfield
    let : Finite K := hKfin
    have hK2 : Nat.card K = 2 := by rw [hKcard, hn]; norm_num
    have hKchar : CharP K 2 :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
        (k := 1) Nat.prime_two (by norm_num) (by rw [hK2]; norm_num)
    let : CharP K 2 := hKchar
    have hfin : Module.finrank K (LargeEvenMinusIdx (lab.rank - 1) → K) = 2 * lab.rank := by
      rw [Module.finrank_fintype_fun_eq_card (R := K) (η := LargeEvenMinusIdx (lab.rank - 1))]
      simp only [LargeEvenMinusIdx, Fintype.card_sum, Fintype.card_fin]
      omega
    have hchar : OrdPNsOm.charSum (TableBOrth.qMinusForm K (lab.rank - 1) b c) ⊤ =
        -((2 : ℤ) ^ lab.rank) := by
      have h0 := ggResX2TrAux_charSum_qMinus K hK2 (lab.rank - 1) hirr
      rwa [← hrank] at h0
    exact ⟨K, hKfield, hKfin, inferInstance, LargeEvenMinusIdx (lab.rank - 1) → K, inferInstance,
      inferInstance, inferInstance, TableBOrth.qMinusForm K (lab.rank - 1) b c, hK2,
      TableBOrth.nondegenerate_qMinusForm (lab.rank - 1) hirr, hfin, Or.inr ⟨hD, hchar⟩,
      ⟨hdata.some.trans (OrthTorus.rMinusEquiv K (lab.rank - 1) b c)⟩⟩

end CFSG.StandardType

namespace CFSG.StandardType

open CFSG.Assembly

private theorem ggResX2TrAux_side (hRig : GGLabelRigidInput) {G : Type} [Group G] [Finite G]
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J)
    (hlab : GGInnerDiagOnLabel (fun p lab => p = 3 ∧ (lab.tag = .D ∨ lab.tag = .twD) ∧
      lab.n = 1 ∧ 4 ≤ lab.rank) p Bs L) :
    ∃ t : G, t ∈ Bs ∧ t ∈ L ∧ t ≠ 1 ∧ IsElemAbelian p Bs ∧
      (∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs) ∧
      (∀ b ∈ Bs, ∃ u ∈ Bs ⊓ L, ∃ c ∈ Bs ⊓ Subgroup.centralizer (L : Set G), b = u * c) ∧
      Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x ∧
      Nat.card ↥(Subgroup.zpowers x) = p ∧
      (Bs ⊓ L) ⊓ Subgroup.centralizer (L : Set G) = ⊥ ∧
      IsComponentOf J (L ⊓ Subgroup.centralizer ({t} : Set G)) ∧
      ¬ p ∣ Nat.card (Subgroup.center ↥L) := by
  obtain ⟨hIH, hBs, hstd⟩ := hcfg
  obtain ⟨-, -, -, -, -, -, hS, -⟩ := hIH
  obtain ⟨lab, hΛ2, hhas, R₀, _, I, F, θ, ⟨hp3, htag, hn, hr⟩, -⟩ :=
    largeEvenMarking_exists_hasLabel hlab
  have hM : GGInnerDiagOn Bs L :=
    largeEvenMarking_mono (fun _ _ _ _ _ _ hP => hP.2) hlab
  obtain ⟨hBsN, hinner, hcopL, -⟩ :=
    HdRo7D.d_sideData hRig HdRo7D.d_frameOmega_holds hp3 hM hΛ2 hhas htag hn hr
  have hp : p.Prime := hp3 ▸ Nat.prime_three
  have : Fact p.Prime := ⟨hp⟩
  have hBsB : B ≤ Bs := hBs.1
  have hBsEA : IsElemAbelian p Bs := hBs.2.1
  have hxBs : x ∈ Bs := hBsB hS.2.1
  have hx1 : x ≠ 1 := hS.2.2.1
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := hS.2.2.2.1.1
  have hcyc := hS.2.2.2.2
  have hcop' : Nat.Coprime p (Nat.card (Subgroup.center ↥L)) :=
    (Nat.Prime.coprime_iff_not_dvd hp).mpr hcopL
  have hsplit := ggBstar_split_of_inner_coprime hp hBs hcop' hBsN hinner
  have hCenL : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x :=
    inf_centralizer_eq_zpowers_of_elemAbelian hp hBsEA hxBs hx1 hLx hcyc
  have hxcard : Nat.card ↥(Subgroup.zpowers x) = p := by
    rw [Nat.card_zpowers, orderOf_eq_prime (hBsEA.2 x hxBs) hx1]
  have htriv : (Bs ⊓ L) ⊓ Subgroup.centralizer (L : Set G) = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro z hz
    obtain ⟨⟨hzBs, hzK⟩, hzC⟩ := hz
    have hzKq : (⟨z, hzK⟩ : ↥L) ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro w
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hzC (w : G) w.2)
    have h1 : orderOf (⟨z, hzK⟩ : ↥L) ∣ Nat.card (Subgroup.center ↥L) :=
      Subgroup.orderOf_dvd_natCard _ hzKq
    have h2 : orderOf (⟨z, hzK⟩ : ↥L) ∣ p := by
      rw [orderOf_dvd_iff_pow_eq_one]
      exact Subtype.ext (by simpa using hBsEA.2 z hzBs)
    have h3 : orderOf (⟨z, hzK⟩ : ↥L) = 1 := by
      rcases (Nat.dvd_prime hp).mp h2 with h | h
      · exact h
      · exfalso
        exact hcopL (h ▸ h1)
    have h4 : (⟨z, hzK⟩ : ↥L) = 1 := orderOf_eq_one_iff.mp h3
    simpa using congrArg Subtype.val h4
  have hstdPre : LargeEvenStdSubPre p B x L D J := hstd.1
  have hDleB : D ≤ B := hstdPre.1
  have hDcard : Nat.card ↥D = p ^ 2 := hstdPre.2.2.1
  have hxD : x ∈ D := hstdPre.2.2.2.1
  have hJtD : IsComponentOf J (L ⊓ Subgroup.centralizer (D : Set G)) := hstdPre.2.2.2.2.2.1
  have hlt : Nat.card ↥(Subgroup.zpowers x) < Nat.card ↥D := by
    rw [hxcard, hDcard]
    nlinarith [hp.two_le]
  obtain ⟨d, hdD, hdz⟩ : ∃ d ∈ D, d ∉ Subgroup.zpowers x := by
    by_contra h
    push Not at h
    have hle : D ≤ Subgroup.zpowers x := fun y hy => h y hy
    have hcard : Nat.card ↥D ≤ Nat.card ↥(Subgroup.zpowers x) :=
      Nat.card_le_card_of_injective (fun z : ↥D => (⟨z.1, hle z.2⟩ : ↥(Subgroup.zpowers x)))
        (fun a b hab => Subtype.ext (by simpa using congrArg Subtype.val hab))
    omega
  obtain ⟨t, ht, c, hc, hdEq⟩ := hsplit d (hBsB (hDleB hdD))
  have htBs : t ∈ Bs := ht.1
  have htL : t ∈ L := ht.2
  have hcC : c ∈ Subgroup.centralizer (L : Set G) := hc.2
  have htne : t ≠ 1 := by
    intro h1
    apply hdz
    have hd : d = c := by rw [hdEq, h1, one_mul]
    rw [hd, ← hCenL]
    exact hc
  have hDgen : D = Subgroup.zpowers x ⊔ Subgroup.zpowers d := by
    have hsup_le : Subgroup.zpowers x ⊔ Subgroup.zpowers d ≤ D :=
      sup_le (Subgroup.zpowers_le.mpr hxD) (Subgroup.zpowers_le.mpr hdD)
    have hcard : Nat.card ↥(Subgroup.zpowers x ⊔ Subgroup.zpowers d) = p ^ 2 :=
      card_zpowers_sup_zpowers hp hBsEA (hBsB (hDleB hxD)) (hBsB (hDleB hdD)) hx1 hdz
    exact (Subgroup.eq_of_le_of_card_ge hsup_le (by rw [hcard, hDcard])).symm
  have htEq : t = d * c⁻¹ := by rw [hdEq]; group
  have hcentD : L ⊓ Subgroup.centralizer (D : Set G) =
      L ⊓ Subgroup.centralizer ({t} : Set G) := by
    ext z
    constructor
    · rintro ⟨hzL, hzC⟩
      refine ⟨hzL, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      have hzd : Commute z d := ((Subgroup.mem_centralizer_iff.mp hzC) d hdD).symm
      have hzc : Commute z c := (Subgroup.mem_centralizer_iff.mp hcC) z hzL
      rw [htEq]
      exact (hzd.mul_right hzc.inv_right).eq
    · rintro ⟨hzL, hzt⟩
      refine ⟨hzL, Subgroup.mem_centralizer_iff.mpr ?_⟩
      intro y hy
      have hzc : Commute z c := (Subgroup.mem_centralizer_iff.mp hcC) z hzL
      have hzt' : Commute z t := Subgroup.mem_centralizer_singleton_iff.mp hzt
      have hzd : Commute z d := hdEq ▸ hzt'.mul_right hzc
      have hzx : Commute z x := Subgroup.mem_centralizer_singleton_iff.mp (hLx hzL)
      have hle : Subgroup.zpowers x ⊔ Subgroup.zpowers d ≤
          Subgroup.centralizer ({z} : Set G) := by
        refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_)
        · exact Subgroup.mem_centralizer_singleton_iff.mpr hzx.symm
        · exact Subgroup.mem_centralizer_singleton_iff.mpr hzd.symm
      have hy' : y ∈ Subgroup.centralizer ({z} : Set G) := by
        rw [hDgen] at hy
        exact hle hy
      exact Subgroup.mem_centralizer_singleton_iff.mp hy'
  exact ⟨t, htBs, htL, htne, hBsEA, hBs.2.2.2, hsplit, hCenL, hxcard, htriv, by
    rw [← hcentD]; exact hJtD, hcopL⟩

private theorem ggResX2TrAux_count {G : Type} [Group G] [Finite G] {Bs L J : Subgroup G} {x : G}
    (hsplit : ∀ b ∈ Bs, ∃ u ∈ Bs ⊓ L, ∃ c ∈ Bs ⊓ Subgroup.centralizer (L : Set G), b = u * c)
    (hCenL : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x)
    (hxcard : Nat.card ↥(Subgroup.zpowers x) = 3) (hJleL : J ≤ L) :
    Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) ≤
      Nat.card ↥((Bs ⊓ L) ⊓ Subgroup.centralizer (J : Set G)) * 3 := by
  classical
  have key : ∀ b : ↥(Bs ⊓ Subgroup.centralizer (J : Set G)),
      ∃ p : ↥((Bs ⊓ L) ⊓ Subgroup.centralizer (J : Set G)) ×
        ↥(Bs ⊓ Subgroup.centralizer (L : Set G)),
        ((b : G) = (p.1 : G) * (p.2 : G)) := by
    intro b
    obtain ⟨u, hu, c, hc, hbc⟩ := hsplit (b : G) b.2.1
    have hcJ : c ∈ Subgroup.centralizer (J : Set G) :=
      Subgroup.centralizer_le hJleL hc.2
    have huJ : u ∈ Subgroup.centralizer (J : Set G) := by
      have hbcc : (b : G) * c⁻¹ = u := by rw [hbc]; group
      rw [← hbcc]
      exact (Subgroup.centralizer (J : Set G)).mul_mem b.2.2
        ((Subgroup.centralizer (J : Set G)).inv_mem hcJ)
    refine ⟨(⟨u, ?_⟩, ⟨c, ?_⟩), hbc⟩
    · exact ⟨⟨hu.1, hu.2⟩, huJ⟩
    · exact ⟨hc.1, hc.2⟩
  choose f hf using key
  have hinj : Function.Injective f := by
    intro a b hab
    exact Subtype.ext (by rw [hf a, hab, ← hf b])
  calc Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G))
      ≤ Nat.card (↥((Bs ⊓ L) ⊓ Subgroup.centralizer (J : Set G)) ×
          ↥(Bs ⊓ Subgroup.centralizer (L : Set G))) :=
        Nat.card_le_card_of_injective f hinj
    _ = Nat.card ↥((Bs ⊓ L) ⊓ Subgroup.centralizer (J : Set G)) *
          Nat.card ↥(Bs ⊓ Subgroup.centralizer (L : Set G)) := Nat.card_prod _ _
    _ = Nat.card ↥((Bs ⊓ L) ⊓ Subgroup.centralizer (J : Set G)) * 3 := by rw [hCenL, hxcard]

private theorem ggResX2TrAux_image {G : Type} [Group G] [Finite G] {p : ℕ} {Bs : Subgroup G}
    {L : Subgroup G} {R : Type} [Group R] (ψ : ↥L →* R) (hψ : Function.Surjective ψ)
    (hkerle : ψ.ker ≤ Subgroup.center ↥L) (hcopψ : ¬ p ∣ Nat.card ↥ψ.ker)
    (hp : p.Prime) (hp3 : p = 3) (hBsEA : IsElemAbelian p Bs)
    (hBsSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hsplit : ∀ b ∈ Bs, ∃ u ∈ Bs ⊓ L, ∃ c ∈ Bs ⊓ Subgroup.centralizer (L : Set G), b = u * c) :
    IsElemAbelian 3 (((Bs ⊓ L).subgroupOf L).map ψ) ∧
      (∀ g : R, (∀ e ∈ ((Bs ⊓ L).subgroupOf L).map ψ, g * e = e * g) → g ^ 3 = 1 →
        g ∈ ((Bs ⊓ L).subgroupOf L).map ψ) := by
  have hEea : IsElemAbelian p ((Bs ⊓ L).subgroupOf L) := hBsEA.mono inf_le_left |>.subgroupOf L
  have hEsc : ∀ g : ↥L, (∀ e ∈ (Bs ⊓ L).subgroupOf L, g * e = e * g) → g ^ p = 1 →
      g ∈ (Bs ⊓ L).subgroupOf L := by
    intro g hg hgp
    rw [Subgroup.mem_subgroupOf]
    refine ⟨?_, g.2⟩
    have hcommBs : ∀ b ∈ Bs, b * (g : G) = (g : G) * b := by
      intro b hb
      obtain ⟨t', ht', c', hc', rfl⟩ := hsplit b hb
      have h1 : t' * (g : G) = (g : G) * t' := by
        have h := hg ⟨t', ht'.2⟩ (Subgroup.mem_subgroupOf.mpr ht')
        exact (congrArg Subtype.val h).symm
      have h2 : c' * (g : G) = (g : G) * c' :=
        (Subgroup.mem_centralizer_iff.mp hc'.2 (g : G) g.2).symm
      calc (t' * c') * (g : G) = t' * (c' * (g : G)) := by group
        _ = t' * ((g : G) * c') := by rw [h2]
        _ = t' * (g : G) * c' := by group
        _ = ((g : G) * t') * c' := by rw [h1]
        _ = (g : G) * (t' * c') := by group
    refine hBsSC (g : G) ?_ ?_
    · exact Subgroup.mem_centralizer_iff.mpr hcommBs
    · simpa only [Subgroup.coe_pow, Subgroup.coe_one] using congrArg Subtype.val hgp
  obtain ⟨hEab, hEsc'⟩ :=
    HdRo7D.d_scMap_of_central hp ψ hψ hkerle hcopψ hEea hEsc
  exact ⟨by simpa [hp3] using hEab, by simpa [hp3] using hEsc'⟩

private theorem ggResX2TrAux_component {G : Type} [Group G] [Finite G] {p : ℕ} {L J : Subgroup G}
    {R : Type} [Group R] (θ : ↥L ⧸ Subgroup.center ↥L ≃* R) (hp : p.Prime)
    (hcopL : ¬ p ∣ Nat.card (Subgroup.center ↥L))
    {t : G} (htL : t ∈ L) (htp : t ^ p = 1)
    (hJt : IsComponentOf J (L ⊓ Subgroup.centralizer ({t} : Set G))) :
    IsComponentOf
      ((J.subgroupOf L).map (θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥L))))
      (Subgroup.centralizer ({θ (QuotientGroup.mk ⟨t, htL⟩)} : Set R)) := by
  have hDpart : CFSG.RankThree.PartOne.IsComponentOf
      (L ⊓ Subgroup.centralizer ({t} : Set G)) J :=
    ⟨hJt.1, (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mp
      hJt.2.2, (CFSG.Assembly.IsSubnormal.iff_subgroupOf hJt.1).mp hJt.2.1⟩
  have hDq := CFSG.RankThree.PartOne.isComponentOf_map_centerQuotient
    (p := p) hp hcopL htL htp hDpart
  have hDqA : IsComponentOf
      ((J.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L)))
      (Subgroup.centralizer
        ({((⟨t, htL⟩ : ↥L) : ↥L ⧸ Subgroup.center ↥L)} :
          Set (↥L ⧸ Subgroup.center ↥L))) :=
    ⟨hDq.1, (CFSG.Assembly.IsSubnormal.iff_subgroupOf hDq.1).mpr hDq.2.2,
      (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mpr hDq.2.1⟩
  have hDθ : IsComponentOf
      (((J.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L))).map θ.toMonoidHom)
      ((Subgroup.centralizer
        ({((⟨t, htL⟩ : ↥L) : ↥L ⧸ Subgroup.center ↥L)} :
          Set (↥L ⧸ Subgroup.center ↥L))).map θ.toMonoidHom) := by
    refine ⟨Subgroup.map_mono hDqA.1, CFSG.Assembly.IsSubnormal.map θ.toMonoidHom hDqA.2.1, ?_⟩
    exact (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mpr
      (CFSG.LocalCores.isQuasisimple_of_mulEquiv
        (Subgroup.equivMapOfInjective _ θ.toMonoidHom θ.injective)
        ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mp hDqA.2.2))
  have hCmap : (Subgroup.centralizer
        ({((⟨t, htL⟩ : ↥L) : ↥L ⧸ Subgroup.center ↥L)} :
          Set (↥L ⧸ Subgroup.center ↥L))).map θ.toMonoidHom =
      Subgroup.centralizer ({θ (QuotientGroup.mk ⟨t, htL⟩)} : Set R) := by
    rw [CFSG.GroupTheory.map_centralizer_eq_of_mulEquiv, Set.image_singleton]
    rfl
  have hJbarEq : (((J.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L))).map
        θ.toMonoidHom) =
      (J.subgroupOf L).map (θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥L))) := by
    rw [Subgroup.map_map]
  rw [← hJbarEq, ← hCmap]
  exact hDθ

private theorem ggResX2TrAux_conj_mem {G : Type} [Group G] [Finite G] {p : ℕ} {Bs L : Subgroup G}
    {R : Type} [Group R] (ψ : ↥L →* R) (hker : ψ.ker = Subgroup.center ↥L)
    (hp : p.Prime) (hcopL : ¬ p ∣ Nat.card (Subgroup.center ↥L))
    (hBsEA : IsElemAbelian p Bs)
    {n : R} (hnorm : ∀ a ∈ ((Bs ⊓ L).subgroupOf L).map ψ, n * a * n⁻¹ ∈
      ((Bs ⊓ L).subgroupOf L).map ψ)
    {n₀ : ↥L} (hn₀ : ψ n₀ = n) {y' : ↥L} (hy' : y' ∈ (Bs ⊓ L).subgroupOf L) :
    n₀ * y' * n₀⁻¹ ∈ (Bs ⊓ L).subgroupOf L := by
  have hpp : ∀ z : ↥L, z ∈ (Bs ⊓ L).subgroupOf L → z ^ p = 1 :=
    fun z hz => (hBsEA.mono inf_le_left |>.subgroupOf L).2 z hz
  set w : ↥L := n₀ * y' * n₀⁻¹ with hw
  have hmem : ψ w ∈ ((Bs ⊓ L).subgroupOf L).map ψ := by
    have h1 := hnorm (ψ y') (Subgroup.mem_map_of_mem ψ hy')
    rw [← hn₀] at h1
    simpa only [hw, map_mul, map_inv] using h1
  obtain ⟨e', he', he'eq⟩ := Subgroup.mem_map.mp hmem
  set z : ↥L := w * e'⁻¹ with hz
  have hzC : z ∈ Subgroup.center ↥L := by
    rw [← hker, MonoidHom.mem_ker]
    show ψ (w * e'⁻¹) = 1
    rw [map_mul, map_inv, he'eq, mul_inv_cancel]
  have hweq : w = z * e' := by rw [hz]; group
  have hwp : w ^ p = 1 := by
    have hconj : ∀ k : ℕ, w ^ k = n₀ * y' ^ k * n₀⁻¹ := by
      intro k
      induction k with
      | zero => rw [pow_zero, pow_zero, mul_one, mul_inv_cancel]
      | succ k ih => rw [pow_succ, ih, hw, pow_succ]; group
    rw [hconj, hpp y' hy', mul_one, mul_inv_cancel]
  have he'p : e' ^ p = 1 := hpp e' he'
  have hcomm : Commute z e' := (Subgroup.mem_center_iff.mp hzC e').symm
  have hzp : z ^ p = 1 := by
    have h1 : z ^ p * e' ^ p = 1 := by
      rw [← hcomm.mul_pow, ← hweq, hwp]
    rwa [he'p, mul_one] at h1
  have hz1 : z = 1 := by
    have hd1 : orderOf z ∣ p := orderOf_dvd_iff_pow_eq_one.mpr hzp
    have hd2 : orderOf z ∣ Nat.card (Subgroup.center ↥L) :=
      Subgroup.orderOf_dvd_natCard (Subgroup.center ↥L) hzC
    rcases (Nat.dvd_prime hp).mp hd1 with hh | hh
    · exact orderOf_eq_one_iff.mp hh
    · exact absurd (hh ▸ hd2) hcopL
  have hw' : w = e' := by rw [hweq, hz1, one_mul]
  rw [hw']
  exact he'

private theorem ggResX2TrAux_normalizer {G : Type} [Group G] [Finite G] {p : ℕ} {Bs L : Subgroup G}
    {R : Type} [Group R] (ψ : ↥L →* R) (hker : ψ.ker = Subgroup.center ↥L)
    (hp : p.Prime) (hcopL : ¬ p ∣ Nat.card (Subgroup.center ↥L))
    (hBsEA : IsElemAbelian p Bs)
    (hsplit : ∀ b ∈ Bs, ∃ u ∈ Bs ⊓ L, ∃ c ∈ Bs ⊓ Subgroup.centralizer (L : Set G), b = u * c)
    {n : R} (hnorm : ∀ a ∈ ((Bs ⊓ L).subgroupOf L).map ψ, n * a * n⁻¹ ∈
      ((Bs ⊓ L).subgroupOf L).map ψ)
    {n₀ : ↥L} (hn₀ : ψ n₀ = n) :
    (n₀ : G) ∈ Subgroup.normalizer (Bs : Set G) := by
  have hstep : ∀ (m : R) (m₀ : ↥L), ψ m₀ = m →
      (∀ a ∈ ((Bs ⊓ L).subgroupOf L).map ψ, m * a * m⁻¹ ∈
        ((Bs ⊓ L).subgroupOf L).map ψ) →
      ∀ x ∈ Bs, (m₀ : G) * x * (m₀ : G)⁻¹ ∈ Bs := by
    intro m m₀ hm₀ hnorm' x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := hsplit x hx
    have hy' : (⟨y, hy.2⟩ : ↥L) ∈ (Bs ⊓ L).subgroupOf L := Subgroup.mem_subgroupOf.mpr hy
    have hconj := ggResX2TrAux_conj_mem ψ hker hp hcopL hBsEA hnorm' hm₀ hy'
    have hmem : (m₀ : G) * y * (m₀ : G)⁻¹ ∈ Bs := by
      simpa using (Subgroup.mem_subgroupOf.mp hconj).1
    have hcz : Commute (m₀ : G) z :=
      Subgroup.mem_centralizer_iff.mp hz.2 (m₀ : G) m₀.2
    have hzc : (m₀ : G) * z * (m₀ : G)⁻¹ = z := by rw [hcz.eq]; group
    have hmul : (m₀ : G) * (y * z) * (m₀ : G)⁻¹ = ((m₀ : G) * y * (m₀ : G)⁻¹) * z := by
      calc (m₀ : G) * (y * z) * (m₀ : G)⁻¹
          = ((m₀ : G) * y * (m₀ : G)⁻¹) * ((m₀ : G) * z * (m₀ : G)⁻¹) := by group
        _ = ((m₀ : G) * y * (m₀ : G)⁻¹) * z := by rw [hzc]
    rw [hmul]
    exact Bs.mul_mem hmem hz.1
  have hEbar_inv : ∀ a ∈ ((Bs ⊓ L).subgroupOf L).map ψ, n⁻¹ * a * n ∈
      ((Bs ⊓ L).subgroupOf L).map ψ := by
    have hfin : Finite ↥(((Bs ⊓ L).subgroupOf L).map ψ) :=
      Finite.of_surjective
        (fun x : ↥((Bs ⊓ L).subgroupOf L) =>
          (⟨ψ x, Subgroup.mem_map_of_mem ψ x.2⟩ : ↥(((Bs ⊓ L).subgroupOf L).map ψ)))
        (by
          intro y
          obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp y.2
          exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩)
    let f : ↥(((Bs ⊓ L).subgroupOf L).map ψ) → ↥(((Bs ⊓ L).subgroupOf L).map ψ) :=
      fun a => ⟨n * (a : R) * n⁻¹, hnorm a a.2⟩
    have hfinj : Function.Injective f := by
      intro a b hab
      have h1 : n * (a : R) * n⁻¹ = n * (b : R) * n⁻¹ := congrArg Subtype.val hab
      refine Subtype.ext ?_
      have h2 := congrArg (fun w => n⁻¹ * w * n) h1
      simpa using h2
    have hfsurj : Function.Surjective f := Finite.injective_iff_surjective.mp hfinj
    intro a ha
    obtain ⟨b, hb⟩ := hfsurj ⟨a, ha⟩
    have hb' : n * (b : R) * n⁻¹ = a := congrArg Subtype.val hb
    have h1 : n⁻¹ * a * n = (b : R) := by rw [← hb']; group
    rw [h1]; exact b.2
  have hstep_inv : ∀ x ∈ Bs, (n₀ : G)⁻¹ * x * ((n₀ : G)⁻¹)⁻¹ ∈ Bs :=
    hstep n⁻¹ n₀⁻¹ (by rw [map_inv, hn₀]) (by simpa using hEbar_inv)
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact fun hx => hstep n n₀ hn₀ hnorm x hx
  · intro hx
    have h1 := hstep_inv ((n₀ : G) * x * (n₀ : G)⁻¹) hx
    rwa [show (n₀ : G)⁻¹ * ((n₀ : G) * x * (n₀ : G)⁻¹) * ((n₀ : G)⁻¹)⁻¹ = x from by
      group] at h1

theorem ggResExactTwoOrthFixLeaf_of_omega (h : GGResExactTwoOrthFixOmega) :
    GGResExactTwoOrthFixLeaf := by
  intro hRig G _ _ p B Bs x L D J hcfg hlab b hb
  obtain ⟨t₀, ht₀Bs, ht₀L, ht₀ne, hBsEA, hBsSC, hsplit, hCenL, hxcard, htriv, hJt, hcopL⟩ :=
    ggResX2TrAux_side hRig hcfg hlab
  obtain ⟨lab, hΛ2, hhas, -, -, -, -, -, ⟨hp3, htag, hn, hr⟩, -⟩ :=
    largeEvenMarking_exists_hasLabel hlab
  obtain ⟨F, hF, hFfin, hFchar, V, hV, hVmod, hVfd, Q, hF2, hQnd, hdim, -, ⟨θ⟩⟩ :=
    ggResX2TrAux_model hhas htag hn hr
  let : Field F := hF
  let : Finite F := hFfin
  let : CharP F 2 := hFchar
  let : AddCommGroup V := hV
  let : Module F V := hVmod
  let : FiniteDimensional F V := hVfd
  let R : Type := ↥(CFSG.RankThree.Classical2.orthDerived Q)
  let : Group R := inferInstanceAs (Group ↥(CFSG.RankThree.Classical2.orthDerived Q))
  let ψ : ↥L →* R := θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥L))
  have hψ : Function.Surjective ψ :=
    θ.surjective.comp (QuotientGroup.mk'_surjective (Subgroup.center ↥L))
  have hkerψ : ψ.ker = Subgroup.center ↥L := by
    ext z
    rw [MonoidHom.mem_ker]
    show θ ((QuotientGroup.mk' (Subgroup.center ↥L)) z) = 1 ↔ z ∈ Subgroup.center ↥L
    rw [MulEquiv.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff z
  have hkerle : ψ.ker ≤ Subgroup.center ↥L := le_of_eq hkerψ
  have hcopψ : ¬ p ∣ Nat.card ↥ψ.ker := by rw [hkerψ]; exact hcopL
  have hp : p.Prime := hp3 ▸ Nat.prime_three
  have : Fact p.Prime := ⟨hp⟩
  have h8 : 8 ≤ Module.finrank F V := by rw [hdim]; omega
  have hJleL : J ≤ L := hJt.1.trans inf_le_left
  have ht₀p : t₀ ^ p = 1 := hBsEA.2 t₀ ht₀Bs
  have himage := ggResX2TrAux_image ψ hψ hkerle hcopψ hp hp3 hBsEA hBsSC hsplit
  have hEab3 : IsElemAbelian 3 (((Bs ⊓ L).subgroupOf L).map ψ) := himage.1
  have hEsc3 : ∀ g : R, (∀ e ∈ ((Bs ⊓ L).subgroupOf L).map ψ, g * e = e * g) → g ^ 3 = 1 →
      g ∈ ((Bs ⊓ L).subgroupOf L).map ψ := himage.2
  have hcomp : IsComponentOf (((J.subgroupOf L).map ψ))
      (Subgroup.centralizer ({ψ ⟨t₀, ht₀L⟩} : Set R)) :=
    ggResX2TrAux_component θ hp hcopL ht₀L ht₀p hJt
  obtain ⟨tb, htb, cb, hcb, hbeq⟩ := hsplit (b : G) b.2
  have htbL : tb ∈ L := htb.2
  have hcbC : cb ∈ Subgroup.centralizer (L : Set G) := hcb.2
  have htransfer : ∀ n ∈ ((J.subgroupOf L).map ψ),
      (∀ a ∈ ((Bs ⊓ L).subgroupOf L).map ψ, n * a * n⁻¹ ∈ ((Bs ⊓ L).subgroupOf L).map ψ) →
      n * ψ ⟨tb, htbL⟩ = ψ ⟨tb, htbL⟩ * n := by
    intro n hn hnorm
    obtain ⟨n₀, hn₀, rfl⟩ := Subgroup.mem_map.mp hn
    have hn₀J : (n₀ : G) ∈ J := Subgroup.mem_subgroupOf.mp hn₀
    have hn₀N : (n₀ : G) ∈ Subgroup.normalizer (Bs : Set G) :=
      ggResX2TrAux_normalizer ψ hkerψ hp hcopL hBsEA hsplit hnorm rfl
    have hfix : ggConjAut Bs hn₀N b = b :=
      hb (ggConjAut Bs hn₀N) (Subgroup.subset_closure (ggConjAut_mem_ggInduced hn₀J hn₀N))
    have hcomm_b : Commute (n₀ : G) (b : G) := by
      have h1 : ((ggConjAut Bs hn₀N b : ↥Bs) : G) = (b : G) := by rw [hfix]
      rw [ggConjAut_apply] at h1
      calc (n₀ : G) * (b : G) = ((n₀ : G) * (b : G) * (n₀ : G)⁻¹) * (n₀ : G) := by group
        _ = (b : G) * (n₀ : G) := by rw [h1]
    have hcomm_c : Commute (n₀ : G) cb :=
      Subgroup.mem_centralizer_iff.mp hcbC (n₀ : G) n₀.2
    have hcomm_t : Commute (n₀ : G) tb := by
      have htbeq : tb = (b : G) * cb⁻¹ := by rw [hbeq]; group
      rw [htbeq]
      exact hcomm_b.mul_right hcomm_c.inv_right
    have h1 : ψ n₀ * ψ ⟨tb, htbL⟩ = ψ ⟨tb, htbL⟩ * ψ n₀ := by
      rw [← map_mul, ← map_mul]
      exact congrArg ψ (Subtype.ext hcomm_t.eq)
    exact h1
  have htbbarE : ψ ⟨tb, htbL⟩ ∈ ((Bs ⊓ L).subgroupOf L).map ψ :=
    Subgroup.mem_map_of_mem ψ (Subgroup.mem_subgroupOf.mpr htb)
  have ht₀barE : ψ ⟨t₀, ht₀L⟩ ∈ ((Bs ⊓ L).subgroupOf L).map ψ :=
    Subgroup.mem_map_of_mem ψ (Subgroup.mem_subgroupOf.mpr ⟨ht₀Bs, ht₀L⟩)
  have ht₀bar1 : ψ ⟨t₀, ht₀L⟩ ≠ 1 := by
    intro h1
    have hmem : (⟨t₀, ht₀L⟩ : ↥L) ∈ Subgroup.center ↥L := by
      rw [← hkerψ]; exact MonoidHom.mem_ker.mpr h1
    have hcent : t₀ ∈ Subgroup.centralizer (L : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hmem ⟨y, hy⟩)
    have hbot : t₀ ∈ (Bs ⊓ L) ⊓ Subgroup.centralizer (L : Set G) :=
      ⟨⟨ht₀Bs, ht₀L⟩, hcent⟩
    rw [htriv, Subgroup.mem_bot] at hbot
    exact ht₀ne hbot
  have hcentral : ψ ⟨tb, htbL⟩ ∈ Subgroup.centralizer
      ((((J.subgroupOf L).map ψ)) : Set R) :=
    h F hF2 V Q hQnd h8 (((Bs ⊓ L).subgroupOf L).map ψ)
      hEab3 hEsc3 (ψ ⟨t₀, ht₀L⟩) ht₀barE ht₀bar1 (((J.subgroupOf L).map ψ)) hcomp
      (ψ ⟨tb, htbL⟩) htbbarE htransfer
  have hperfSub : Group.IsPerfect ↥(J.subgroupOf L) := by
    have hJperf : Group.IsPerfect ↥J := ⟨hJt.2.2.1⟩
    exact Group.IsPerfect.ofSurjective
      (f := (Subgroup.subgroupOfEquivOfLe hJleL).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hJleL).symm.surjective
  have hecomm : ∀ j ∈ (J.subgroupOf L), ψ ⟨tb, htbL⟩ * ψ j = ψ j * ψ ⟨tb, htbL⟩ := by
    intro j hj
    exact (Subgroup.mem_centralizer_iff.mp hcentral (ψ j)
      (Subgroup.mem_map_of_mem ψ hj)).symm
  have hlift := HdRo7D.d_centralizer_lift ψ hkerle hperfSub.commutator_eq_top hecomm
  have htb_cent : ∀ j ∈ J, tb * j = j * tb := by
    intro j hj
    have hjL : j ∈ L := hJleL hj
    exact congrArg Subtype.val (hlift ⟨j, hjL⟩ (Subgroup.mem_subgroupOf.mpr hj))
  refine Subgroup.mem_centralizer_iff.mpr ?_
  intro j hj
  have htj : tb * j = j * tb := htb_cent j hj
  have hcj : Commute cb j :=
    (Subgroup.mem_centralizer_iff.mp hcbC j (hJleL hj)).symm
  rw [hbeq]
  calc j * (tb * cb) = (j * tb) * cb := by group
    _ = (tb * j) * cb := by rw [htj]
    _ = tb * (j * cb) := by group
    _ = tb * (cb * j) := by rw [hcj.eq]
    _ = (tb * cb) * j := by group

private theorem ggResX2TrAux_card_le_three {X : Type} [Group X] {A : Subgroup X} [Finite ↥A]
    (hX : IsElemAbelian 3 A) (h9 : ¬ 9 ≤ Nat.card ↥A) : Nat.card ↥A ≤ 3 := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (isPGroup_of_isElemAbelian hX)
  have hn1 : n ≤ 1 := by
    by_contra h
    push Not at h
    have h2 : 2 ≤ n := h
    have h3 : 9 ≤ 3 ^ n := by
      calc 9 = 3 ^ 2 := by norm_num
        _ ≤ 3 ^ n := Nat.pow_le_pow_right (by norm_num) h2
    exact h9 (hn.symm ▸ h3)
  calc Nat.card ↥A = 3 ^ n := hn
    _ ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) hn1
    _ = 3 := by norm_num

private theorem ggResX2TrAux_injE {G : Type} [Group G] {Bs L : Subgroup G}
    {R : Type} [Group R] (ψ : ↥L →* R) (hker : ψ.ker = Subgroup.center ↥L)
    (htrivL : ((Bs ⊓ L).subgroupOf L) ⊓ Subgroup.center ↥L = ⊥) :
    ∀ a b : ↥L, a ∈ (Bs ⊓ L).subgroupOf L → b ∈ (Bs ⊓ L).subgroupOf L → ψ a = ψ b → a = b := by
  intro a b ha hb hab
  have h1 : ψ (a * b⁻¹) = 1 := by rw [map_mul, map_inv, hab, mul_inv_cancel]
  have hmem : a * b⁻¹ ∈ ψ.ker := MonoidHom.mem_ker.mpr h1
  rw [hker] at hmem
  have hmem' : a * b⁻¹ ∈ ((Bs ⊓ L).subgroupOf L) ⊓ Subgroup.center ↥L :=
    ⟨Subgroup.mul_mem _ ha (Subgroup.inv_mem _ hb), hmem⟩
  rw [htrivL, Subgroup.mem_bot] at hmem'
  rwa [mul_inv_eq_one] at hmem'

private theorem ggResX2TrAux_Abar {G : Type} [Group G] [Finite G] {Bs L J : Subgroup G}
    {R : Type} [Group R] (ψ : ↥L →* R) (hker : ψ.ker = Subgroup.center ↥L)
    (hinjE : ∀ a b : ↥L, a ∈ (Bs ⊓ L).subgroupOf L → b ∈ (Bs ⊓ L).subgroupOf L → ψ a = ψ b →
      a = b)
    (hJleL : J ≤ L) (hJcomm : commutator ↥(J.subgroupOf L) = ⊤) :
    ((((Bs ⊓ L) ⊓ Subgroup.centralizer (J : Set G)).subgroupOf L).map ψ =
        (((Bs ⊓ L).subgroupOf L).map ψ ⊓ Subgroup.centralizer
          (((J.subgroupOf L).map ψ) : Set R))) ∧
      Nat.card ↥((((Bs ⊓ L) ⊓ Subgroup.centralizer (J : Set G)).subgroupOf L)) =
        Nat.card ↥((((Bs ⊓ L).subgroupOf L).map ψ ⊓ Subgroup.centralizer
          (((J.subgroupOf L).map ψ) : Set R))) := by
  have hAeq : ((((Bs ⊓ L) ⊓ Subgroup.centralizer (J : Set G)).subgroupOf L).map ψ =
      (((Bs ⊓ L).subgroupOf L).map ψ ⊓ Subgroup.centralizer
        (((J.subgroupOf L).map ψ) : Set R))) := by
    ext y
    constructor
    · rintro ⟨a, ha, rfl⟩
      refine ⟨Subgroup.mem_map_of_mem ψ ha.1, Subgroup.mem_centralizer_iff.mpr (fun c hc => ?_)⟩
      obtain ⟨j, hj, rfl⟩ := Subgroup.mem_map.mp hc
      have h1 : j * a = a * j := Subtype.ext
        (Subgroup.mem_centralizer_iff.mp ha.2 (j : G) (Subgroup.mem_subgroupOf.mp hj))
      simpa only [map_mul] using congrArg ψ h1
    · rintro ⟨hyE, hyC⟩
      obtain ⟨e, heE, rfl⟩ := Subgroup.mem_map.mp hyE
      refine ⟨e, Subgroup.mem_subgroupOf.mpr ⟨Subgroup.mem_subgroupOf.mp heE, ?_⟩, rfl⟩
      have hcomm : ∀ j ∈ (J.subgroupOf L), ψ e * ψ j = ψ j * ψ e := by
        intro j hj
        exact (Subgroup.mem_centralizer_iff.mp hyC (ψ j)
          (Subgroup.mem_map_of_mem ψ hj)).symm
      refine Subgroup.mem_centralizer_iff.mpr (fun j hj => ?_)
      have h3 := HdRo7D.d_centralizer_lift (X := ↥L) (J := J.subgroupOf L) (e := e) ψ
        (le_of_eq hker) hJcomm hcomm ⟨j, hJleL hj⟩ (Subgroup.mem_subgroupOf.mpr hj)
      exact (congrArg Subtype.val h3).symm
  refine ⟨hAeq, ?_⟩
  have hbij : Function.Bijective
      (fun a : ↥((((Bs ⊓ L) ⊓ Subgroup.centralizer (J : Set G)).subgroupOf L)) =>
        (⟨ψ a, by rw [← hAeq]; exact Subgroup.mem_map_of_mem ψ a.2⟩ :
        ↥((((Bs ⊓ L).subgroupOf L).map ψ ⊓ Subgroup.centralizer
          (((J.subgroupOf L).map ψ) : Set R))))) := by
    constructor
    · intro a b hab
      refine Subtype.ext (hinjE (a : ↥L) (b : ↥L) a.2.1 b.2.1 ?_)
      exact congrArg Subtype.val hab
    · rintro ⟨y, hy⟩
      have hym : y ∈ (((Bs ⊓ L) ⊓ Subgroup.centralizer (J : Set G)).subgroupOf L).map ψ := by
        rw [hAeq]; exact hy
      obtain ⟨a, ha, hay⟩ := Subgroup.mem_map.mp hym
      exact ⟨⟨a, ha⟩, Subtype.ext hay⟩
  exact Nat.card_congr (Equiv.ofBijective _ hbij)

private theorem ggResX2TrAux_finite_Ebar {G : Type} [Group G] [Finite G] {Bs L : Subgroup G}
    {R : Type} [Group R] (ψ : ↥L →* R) : Finite ↥(((Bs ⊓ L).subgroupOf L).map ψ) :=
  Finite.of_surjective
    (fun x : ↥((Bs ⊓ L).subgroupOf L) =>
      (⟨ψ x, Subgroup.mem_map_of_mem ψ x.2⟩ : ↥(((Bs ⊓ L).subgroupOf L).map ψ)))
    (by
      intro y
      obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp y.2
      exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩)

private theorem ggResX2TrAux_center_bot_of_twD
    {G : Type} [Group G] [Finite G]
    {L : Subgroup G} {lab : LargeEvenLabel}
    (hhas : GGHasLabel lab (↥L ⧸ Subgroup.center ↥L)) (htag : lab.tag = .twD) (hn : lab.n = 1)
    (hr : lab.rank = 5) (hperf : commutator ↥L = ⊤) :
    Subgroup.center ↥L = ⊥ := by
  have hraw := hhas
  have hr2 : lab.rank ≠ 2 := by omega
  have hr3 : lab.rank ≠ 3 := by omega
  simp only [GGHasLabel, CFSG.StandardType.LargeEvenRawDatum, htag, ite_eq_right hr2,
    ite_eq_right hr3] at hraw
  obtain ⟨K, hKfield, hKfin, hKcard, b, c, hirr, ⟨e⟩⟩ := hraw
  let : Field K := hKfield
  let : Finite K := hKfin
  have hK2 : Nat.card K = 2 := by rw [hKcard, hn]; norm_num
  let ψ' : ↥L →* OrthRest.RMinus K (lab.rank - 1) b c :=
    e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥L))
  have hψ' : Function.Surjective ψ' :=
    e.surjective.comp (QuotientGroup.mk'_surjective (Subgroup.center ↥L))
  have hker' : ψ'.ker = Subgroup.center ↥L := by
    ext z
    rw [MonoidHom.mem_ker]
    show e ((QuotientGroup.mk' (Subgroup.center ↥L)) z) = 1 ↔ z ∈ Subgroup.center ↥L
    rw [MulEquiv.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff z
  have hinj := rMinus_injective_of_cover_two hK2 (by omega : 3 ≤ lab.rank - 1) hirr ↥L ψ'
    hψ' (le_of_eq hker') hperf
  have hbot : ψ'.ker = ⊥ := (MonoidHom.ker_eq_bot_iff ψ').mpr hinj
  rw [hker'] at hbot
  exact hbot

theorem ggResExactTwoOrthDFourLeaf_of_omega (h : GGResExactTwoOrthFormsOmega) :
    GGResExactTwoOrthDFourLeaf := by
  intro hRig G _ _ p B Bs x L D J hcfg hlab
  have hlab' : GGInnerDiagOnLabel (fun p lab => p = 3 ∧ (lab.tag = .D ∨ lab.tag = .twD) ∧
      lab.n = 1 ∧ 4 ≤ lab.rank) p Bs L :=
    largeEvenMarking_mono (fun _ _ _ _ _ _ hP =>
      ⟨⟨hP.1.1, Or.inl hP.1.2.1, hP.1.2.2.1, le_of_eq hP.1.2.2.2.symm⟩, hP.2⟩) hlab
  obtain ⟨t₀, ht₀Bs, ht₀L, ht₀ne, hBsEA, hBsSC, hsplit, hCenL, hxcard, htriv, hJt, hcopL⟩ :=
    ggResX2TrAux_side hRig hcfg hlab'
  obtain ⟨lab, hΛ2, hhas, -, -, -, -, -, ⟨hp3, htagD, hn, hr4⟩, -⟩ :=
    largeEvenMarking_exists_hasLabel hlab
  obtain ⟨F, hF, hFfin, hFchar, V, hV, hVmod, hVfd, Q, hF2, hQnd, hdim, hcharDisj, ⟨θ⟩⟩ :=
    ggResX2TrAux_model hhas (Or.inl htagD) hn (by omega)
  let : Field F := hF
  let : Finite F := hFfin
  let : CharP F 2 := hFchar
  let : AddCommGroup V := hV
  let : Module F V := hVmod
  let : FiniteDimensional F V := hVfd
  let R : Type := ↥(CFSG.RankThree.Classical2.orthDerived Q)
  let : Group R := inferInstanceAs (Group ↥(CFSG.RankThree.Classical2.orthDerived Q))
  let ψ : ↥L →* R := θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥L))
  have hψ : Function.Surjective ψ :=
    θ.surjective.comp (QuotientGroup.mk'_surjective (Subgroup.center ↥L))
  have hkerψ : ψ.ker = Subgroup.center ↥L := by
    ext z
    rw [MonoidHom.mem_ker]
    show θ ((QuotientGroup.mk' (Subgroup.center ↥L)) z) = 1 ↔ z ∈ Subgroup.center ↥L
    rw [MulEquiv.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff z
  have hkerle : ψ.ker ≤ Subgroup.center ↥L := le_of_eq hkerψ
  have hcopψ : ¬ p ∣ Nat.card ↥ψ.ker := by rw [hkerψ]; exact hcopL
  have hp : p.Prime := hp3 ▸ Nat.prime_three
  have : Fact p.Prime := ⟨hp⟩
  have hdim8 : Module.finrank F V = 8 := by rw [hdim, hr4]
  have hJleL : J ≤ L := hJt.1.trans inf_le_left
  have ht₀p : t₀ ^ p = 1 := hBsEA.2 t₀ ht₀Bs
  have himage := ggResX2TrAux_image ψ hψ hkerle hcopψ hp hp3 hBsEA hBsSC hsplit
  have hEab3 : IsElemAbelian 3 (((Bs ⊓ L).subgroupOf L).map ψ) := himage.1
  have hEsc3 : ∀ g : R, (∀ e ∈ ((Bs ⊓ L).subgroupOf L).map ψ, g * e = e * g) → g ^ 3 = 1 →
      g ∈ ((Bs ⊓ L).subgroupOf L).map ψ := himage.2
  have hcomp : IsComponentOf (((J.subgroupOf L).map ψ))
      (Subgroup.centralizer ({ψ ⟨t₀, ht₀L⟩} : Set R)) :=
    ggResX2TrAux_component θ hp hcopL ht₀L ht₀p hJt
  have ht₀barE : ψ ⟨t₀, ht₀L⟩ ∈ ((Bs ⊓ L).subgroupOf L).map ψ :=
    Subgroup.mem_map_of_mem ψ (Subgroup.mem_subgroupOf.mpr ⟨ht₀Bs, ht₀L⟩)
  have ht₀bar1 : ψ ⟨t₀, ht₀L⟩ ≠ 1 := by
    intro h1
    have hmem : (⟨t₀, ht₀L⟩ : ↥L) ∈ Subgroup.center ↥L := by
      rw [← hkerψ]; exact MonoidHom.mem_ker.mpr h1
    have hcent : t₀ ∈ Subgroup.centralizer (L : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hmem ⟨y, hy⟩)
    have hbot : t₀ ∈ (Bs ⊓ L) ⊓ Subgroup.centralizer (L : Set G) :=
      ⟨⟨ht₀Bs, ht₀L⟩, hcent⟩
    rw [htriv, Subgroup.mem_bot] at hbot
    exact ht₀ne hbot
  have hchar : OrdPNsOm.charSum Q ⊤ ≡ 1 [ZMOD 3] := by
    rcases hcharDisj with ⟨-, he⟩ | ⟨htw, he⟩
    · rw [he, hr4]; norm_num
    · exact absurd (htagD.symm.trans htw) (by simp)
  have hperfSub : Group.IsPerfect ↥(J.subgroupOf L) := by
    have hJperf : Group.IsPerfect ↥J := ⟨hJt.2.2.1⟩
    exact Group.IsPerfect.ofSurjective
      (f := (Subgroup.subgroupOfEquivOfLe hJleL).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hJleL).symm.surjective
  have htrivL : ((Bs ⊓ L).subgroupOf L) ⊓ Subgroup.center ↥L = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro z hz
    obtain ⟨hzE, hzC⟩ := hz
    have hzG : (z : G) ∈ (Bs ⊓ L) ⊓ Subgroup.centralizer (L : Set G) :=
      ⟨Subgroup.mem_subgroupOf.mp hzE, Subgroup.mem_centralizer_iff.mpr
        (fun y hy => congrArg Subtype.val (Subgroup.mem_center_iff.mp hzC ⟨y, hy⟩))⟩
    rw [htriv, Subgroup.mem_bot] at hzG
    exact Subtype.ext hzG
  have hinjE := ggResX2TrAux_injE ψ hkerψ htrivL
  have hA := ggResX2TrAux_Abar ψ hkerψ hinjE hJleL hperfSub.commutator_eq_top
  have hnot9 : ¬ 9 ≤ Nat.card ↥((((Bs ⊓ L).subgroupOf L).map ψ ⊓
      Subgroup.centralizer (((J.subgroupOf L).map ψ) : Set R))) := by
    intro h9
    have hres := h F hF2 V Q hQnd (Or.inl hdim8) hchar (((Bs ⊓ L).subgroupOf L).map ψ)
      hEab3 hEsc3 (ψ ⟨t₀, ht₀L⟩) ht₀barE ht₀bar1 (((J.subgroupOf L).map ψ)) hcomp h9
    rw [hdim8] at hres
    omega
  let : Finite ↥(((Bs ⊓ L).subgroupOf L).map ψ) := ggResX2TrAux_finite_Ebar ψ
  have hAbarFin : Finite ↥((((Bs ⊓ L).subgroupOf L).map ψ ⊓
      Subgroup.centralizer (((J.subgroupOf L).map ψ) : Set R))) :=
    Finite.of_injective
      (fun a : ↥((((Bs ⊓ L).subgroupOf L).map ψ ⊓
        Subgroup.centralizer (((J.subgroupOf L).map ψ) : Set R))) =>
        (⟨a, a.2.1⟩ : ↥(((Bs ⊓ L).subgroupOf L).map ψ)))
      (fun a b hab => Subtype.ext
        (congrArg (fun w : ↥(((Bs ⊓ L).subgroupOf L).map ψ) => (w : R)) hab))
  have hAbar3 : Nat.card ↥((((Bs ⊓ L).subgroupOf L).map ψ ⊓
      Subgroup.centralizer (((J.subgroupOf L).map ψ) : Set R))) ≤ 3 :=
    ggResX2TrAux_card_le_three (hEab3.mono inf_le_left) hnot9
  have hleAG : (Bs ⊓ L) ⊓ Subgroup.centralizer (J : Set G) ≤ L :=
    le_trans (inf_le_left : (Bs ⊓ L) ⊓ Subgroup.centralizer (J : Set G) ≤ Bs ⊓ L)
      (inf_le_right : Bs ⊓ L ≤ L)
  have hAG : Nat.card ↥((Bs ⊓ L) ⊓ Subgroup.centralizer (J : Set G)) =
      Nat.card ↥((((Bs ⊓ L).subgroupOf L).map ψ ⊓
        Subgroup.centralizer (((J.subgroupOf L).map ψ) : Set R))) := by
    rw [← hA.2]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (H := (Bs ⊓ L) ⊓ Subgroup.centralizer (J : Set G)) (K := L) hleAG).toEquiv).symm
  have hcount := ggResX2TrAux_count hsplit hCenL (by rw [hxcard, hp3]) hJleL
  calc Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G))
      ≤ Nat.card ↥((Bs ⊓ L) ⊓ Subgroup.centralizer (J : Set G)) * 3 := hcount
    _ = Nat.card ↥((((Bs ⊓ L).subgroupOf L).map ψ ⊓
          Subgroup.centralizer (((J.subgroupOf L).map ψ) : Set R))) * 3 := by rw [hAG]
    _ ≤ 3 * 3 := Nat.mul_le_mul_right 3 hAbar3
    _ ≤ 9 := by norm_num

theorem ggResExactTwoOrthTwDFiveLeaf_of_omega
    (h : GGResExactTwoOrthFormsOmega) :
    GGResExactTwoOrthTwDFiveLeaf := by
  intro hRig G _ _ p B Bs x L D J hcfg hlab h27
  have hlab' : GGInnerDiagOnLabel (fun p lab => p = 3 ∧ (lab.tag = .D ∨ lab.tag = .twD) ∧
      lab.n = 1 ∧ 4 ≤ lab.rank) p Bs L :=
    largeEvenMarking_mono (fun _ _ _ _ _ _ hP =>
      ⟨⟨hP.1.1, Or.inr hP.1.2.1, hP.1.2.2.1, by omega⟩, hP.2⟩) hlab
  obtain ⟨t₀, ht₀Bs, ht₀L, ht₀ne, hBsEA, hBsSC, hsplit, hCenL, hxcard, htriv, hJt, hcopL⟩ :=
    ggResX2TrAux_side hRig hcfg hlab'
  obtain ⟨lab, hΛ2, hhas, -, -, -, -, -, ⟨hp3, htagTw, hn, hr5⟩, -⟩ :=
    largeEvenMarking_exists_hasLabel hlab
  obtain ⟨F, hF, hFfin, hFchar, V, hV, hVmod, hVfd, Q, hF2, hQnd, hdim, hcharDisj, ⟨θ⟩⟩ :=
    ggResX2TrAux_model hhas (Or.inr htagTw) hn (by omega)
  let : Field F := hF
  let : Finite F := hFfin
  let : CharP F 2 := hFchar
  let : AddCommGroup V := hV
  let : Module F V := hVmod
  let : FiniteDimensional F V := hVfd
  let R : Type := ↥(CFSG.RankThree.Classical2.orthDerived Q)
  let : Group R := inferInstanceAs (Group ↥(CFSG.RankThree.Classical2.orthDerived Q))
  let ψ : ↥L →* R := θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥L))
  have hψ : Function.Surjective ψ :=
    θ.surjective.comp (QuotientGroup.mk'_surjective (Subgroup.center ↥L))
  have hkerψ : ψ.ker = Subgroup.center ↥L := by
    ext z
    rw [MonoidHom.mem_ker]
    show θ ((QuotientGroup.mk' (Subgroup.center ↥L)) z) = 1 ↔ z ∈ Subgroup.center ↥L
    rw [MulEquiv.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff z
  have hkerle : ψ.ker ≤ Subgroup.center ↥L := le_of_eq hkerψ
  have hcopψ : ¬ p ∣ Nat.card ↥ψ.ker := by rw [hkerψ]; exact hcopL
  have hp : p.Prime := hp3 ▸ Nat.prime_three
  have : Fact p.Prime := ⟨hp⟩
  have hdim10 : Module.finrank F V = 10 := by rw [hdim, hr5]
  have hJleL : J ≤ L := hJt.1.trans inf_le_left
  have ht₀p : t₀ ^ p = 1 := hBsEA.2 t₀ ht₀Bs
  have himage := ggResX2TrAux_image ψ hψ hkerle hcopψ hp hp3 hBsEA hBsSC hsplit
  have hEab3 : IsElemAbelian 3 (((Bs ⊓ L).subgroupOf L).map ψ) := himage.1
  have hEsc3 : ∀ g : R, (∀ e ∈ ((Bs ⊓ L).subgroupOf L).map ψ, g * e = e * g) → g ^ 3 = 1 →
      g ∈ ((Bs ⊓ L).subgroupOf L).map ψ := himage.2
  have hcomp : IsComponentOf (((J.subgroupOf L).map ψ))
      (Subgroup.centralizer ({ψ ⟨t₀, ht₀L⟩} : Set R)) :=
    ggResX2TrAux_component θ hp hcopL ht₀L ht₀p hJt
  have ht₀barE : ψ ⟨t₀, ht₀L⟩ ∈ ((Bs ⊓ L).subgroupOf L).map ψ :=
    Subgroup.mem_map_of_mem ψ (Subgroup.mem_subgroupOf.mpr ⟨ht₀Bs, ht₀L⟩)
  have ht₀bar1 : ψ ⟨t₀, ht₀L⟩ ≠ 1 := by
    intro h1
    have hmem : (⟨t₀, ht₀L⟩ : ↥L) ∈ Subgroup.center ↥L := by
      rw [← hkerψ]; exact MonoidHom.mem_ker.mpr h1
    have hcent : t₀ ∈ Subgroup.centralizer (L : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hmem ⟨y, hy⟩)
    have hbot : t₀ ∈ (Bs ⊓ L) ⊓ Subgroup.centralizer (L : Set G) :=
      ⟨⟨ht₀Bs, ht₀L⟩, hcent⟩
    rw [htriv, Subgroup.mem_bot] at hbot
    exact ht₀ne hbot
  have hchar : OrdPNsOm.charSum Q ⊤ ≡ 1 [ZMOD 3] := by
    rcases hcharDisj with ⟨htD, he⟩ | ⟨-, he⟩
    · exact absurd (htD.symm.trans htagTw) (by simp)
    · rw [he, hr5]; norm_num
  have hperfSub : Group.IsPerfect ↥(J.subgroupOf L) := by
    have hJperf : Group.IsPerfect ↥J := ⟨hJt.2.2.1⟩
    exact Group.IsPerfect.ofSurjective
      (f := (Subgroup.subgroupOfEquivOfLe hJleL).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hJleL).symm.surjective
  have htrivL : ((Bs ⊓ L).subgroupOf L) ⊓ Subgroup.center ↥L = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro z hz
    obtain ⟨hzE, hzC⟩ := hz
    have hzG : (z : G) ∈ (Bs ⊓ L) ⊓ Subgroup.centralizer (L : Set G) :=
      ⟨Subgroup.mem_subgroupOf.mp hzE, Subgroup.mem_centralizer_iff.mpr
        (fun y hy => congrArg Subtype.val (Subgroup.mem_center_iff.mp hzC ⟨y, hy⟩))⟩
    rw [htriv, Subgroup.mem_bot] at hzG
    exact Subtype.ext hzG
  have hinjE := ggResX2TrAux_injE ψ hkerψ htrivL
  have hA := ggResX2TrAux_Abar ψ hkerψ hinjE hJleL hperfSub.commutator_eq_top
  have hleAG : (Bs ⊓ L) ⊓ Subgroup.centralizer (J : Set G) ≤ L :=
    le_trans (inf_le_left : (Bs ⊓ L) ⊓ Subgroup.centralizer (J : Set G) ≤ Bs ⊓ L)
      (inf_le_right : Bs ⊓ L ≤ L)
  have hAG : Nat.card ↥((Bs ⊓ L) ⊓ Subgroup.centralizer (J : Set G)) =
      Nat.card ↥((((Bs ⊓ L).subgroupOf L).map ψ ⊓
        Subgroup.centralizer (((J.subgroupOf L).map ψ) : Set R))) := by
    rw [← hA.2]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (H := (Bs ⊓ L) ⊓ Subgroup.centralizer (J : Set G)) (K := L) hleAG).toEquiv).symm
  have hcount := ggResX2TrAux_count hsplit hCenL (by rw [hxcard, hp3]) hJleL
  rw [hAG] at hcount
  have h9 : 9 ≤ Nat.card ↥((((Bs ⊓ L).subgroupOf L).map ψ ⊓
      Subgroup.centralizer (((J.subgroupOf L).map ψ) : Set R))) := by omega
  have hres := h F hF2 V Q hQnd (Or.inr hdim10) hchar (((Bs ⊓ L).subgroupOf L).map ψ)
    hEab3 hEsc3 (ψ ⟨t₀, ht₀L⟩) ht₀barE ht₀bar1 (((J.subgroupOf L).map ψ)) hcomp h9
  have hsmall : LargeEvenIsU42 ↥(((J.subgroupOf L).map ψ)) := hres.2
  have hZbot : Subgroup.center ↥L = ⊥ :=
    ggResX2TrAux_center_bot_of_twD hhas htagTw hn hr5 hlab.1
  have hkerbot : ψ.ker = ⊥ := by rw [hkerψ]; exact hZbot
  have hinjψ : Function.Injective ψ := (MonoidHom.ker_eq_bot_iff ψ).mp hkerbot
  have eJ : ↥J ≃* ↥(((J.subgroupOf L).map ψ)) :=
    (Subgroup.subgroupOfEquivOfLe hJleL).symm.trans
      (Subgroup.equivMapOfInjective (J.subgroupOf L) ψ hinjψ)
  simp only [LargeEvenIsU42] at hsmall
  change LargeEvenIsU42 ↥J ∨ Nonempty (↥J ≃* alternatingGroup (Fin 6))
  obtain ⟨K', hKf, hKfi, hc, ⟨f⟩⟩ := hsmall
  exact Or.inl ⟨K', hKf, hKfi, hc, ⟨eJ.trans f⟩⟩

end CFSG.StandardType
