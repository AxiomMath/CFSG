module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1CollinearDefs
public import CFSG.LieType.HighestRoot.RootInvolution
public import CFSG.Timmesfeld.Special.TwoCore
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2ShortTransport
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2OddCenter
public import CFSG.Mathlib.GroupTheory.CardTwo

public section

namespace CFSG.StandardType.RCKC1

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.StandardType CFSG.StandardType.S2MathFi1035Pos
  CFSG.LieType.Steinberg CFSG.LieType.CurtisTits CFSG.LieType.HighestRoot
open CFSG.ComponentClassification.RankTwoOddLie (CenterPPrime)
open CFSG.ClassicalInvolution.ModelFacts (IsIrreducible)
open CFSG.GroupTheory (eq_one_or_eq_of_mem_of_card_eq_two)

open scoped commutatorElement

private lemma eq_one_of_central_mul_involution {U : Type*} [Group U] {c y : U}
    (hc : c ∈ Subgroup.center U) (hcy : (c * y) ^ 2 = 1) (hy : y * y = 1)
    (hZ : CenterPPrime U 2) : c = 1 := by
  have hcomm : Commute c y := (Subgroup.mem_center_iff.mp hc y).symm
  have h2 : c ^ 2 = 1 := by
    have hy2 : y ^ 2 = 1 := by rw [pow_two]; exact hy
    have h : (c * y) ^ 2 = c ^ 2 * y ^ 2 := hcomm.mul_pow 2
    rw [hy2, mul_one] at h
    rwa [h] at hcy
  exact hZ c hc h2

private lemma commute_of_map_commute {U X : Type} [Group U] [Group X] {φ : U →* X}
    (hker : φ.ker ≤ Subgroup.center U) (hZ : CenterPPrime U 2) {a b : U}
    (ha : a * a = 1) (hb : b * b = 1) (hcomm : φ a * φ b = φ b * φ a) : a * b = b * a := by
  have hker' : a * b * a⁻¹ * b⁻¹ ∈ φ.ker := by
    rw [MonoidHom.mem_ker]
    have h1 : φ a * φ b * (φ a)⁻¹ = φ b := by rw [hcomm]; group
    simp only [map_mul, map_inv, h1, mul_inv_cancel]
  have hc : a * b * a⁻¹ * b⁻¹ ∈ Subgroup.center U := hker hker'
  have hca : a * b * a⁻¹ = (a * b * a⁻¹ * b⁻¹) * b := by group
  have hconj : ((a * b * a⁻¹ * b⁻¹) * b) ^ 2 = 1 := by
    rw [← hca, pow_two]
    calc (a * b * a⁻¹) * (a * b * a⁻¹) = a * (b * b) * a⁻¹ := by group
      _ = 1 := by rw [hb]; group
  have h1 : a * b * a⁻¹ * b⁻¹ = 1 := eq_one_of_central_mul_involution hc hconj hb hZ
  calc a * b = a * b * a⁻¹ * a := by group
    _ = b * a := by rw [hca, h1, one_mul]

theorem le_normalizer_of_commutator_le {G : Type*} [Group G] {Q R V : Subgroup G}
    (hVQ : V ≤ Q) (hQQ : ⁅Q, Q⁆ ≤ R) (hRV : R ≤ V) : Q ≤ Subgroup.normalizer (V : Set G) := by
  intro q hq
  rw [Subgroup.mem_normalizer_iff]
  intro v
  constructor
  · intro hv
    have hqv : ⁅q, v⁆ ∈ V := hRV (hQQ (Subgroup.commutator_mem_commutator hq (hVQ hv)))
    have h : q * v * q⁻¹ = ⁅q, v⁆ * v := by rw [commutatorElement_def]; group
    rw [h]
    exact V.mul_mem hqv hv
  · intro hv
    have hqinv : q⁻¹ ∈ Q := Q.inv_mem hq
    have hqv : ⁅q⁻¹, q * v * q⁻¹⁆ ∈ V :=
      hRV (hQQ (Subgroup.commutator_mem_commutator hqinv (hVQ hv)))
    have h : q⁻¹ * (q * v * q⁻¹) * q = ⁅q⁻¹, q * v * q⁻¹⁆ * (q * v * q⁻¹) := by
      rw [commutatorElement_def]; group
    have hveq : v = q⁻¹ * (q * v * q⁻¹) * q := by group
    rw [hveq, h]
    exact V.mul_mem hqv hv

theorem le_pCoreOf_of_isRootInvolutionSet {U X : Type} [Group U] [Finite U] [Group X] [Finite X]
    {φ : U →* X} (hker : φ.ker ≤ Subgroup.center U) (hZ : CenterPPrime U 2) {x : U}
    (hD : CFSG.Timmesfeld.IsRootInvolutionSet {g : U | IsConj x g}) {V : Subgroup X}
    (hxV : φ x ∈ V) (hV : IsElemAbelian 2 V)
    (hconj : ∀ v ∈ V, v ≠ 1 → ∃ k ∈ φ.range, v = k * φ x * k⁻¹) :
    V ≤ pCoreOf 2 (φ.range ⊓ Subgroup.centralizer ({φ x} : Set X)) := by
  classical
  have hx2 : x * x = 1 := by
    have hord : orderOf x = 2 := hD.1 x (IsConj.refl x)
    calc x * x = x ^ 2 := (pow_two x).symm
      _ = 1 := by rw [← hord]; exact pow_orderOf_eq_one x
  have hφx2 : φ x * φ x = 1 := by rw [← map_mul, hx2, map_one]
  have hodd : Odd (Nat.card φ.ker) :=
    Odd.of_dvd_nat (LieKnownR2.OddCenter.odd_card_center_of_centerPPrime_two hZ)
      (Subgroup.card_dvd_of_le hker)
  have hkerC : φ.ker ≤ Subgroup.centralizer ({x} : Set U) := by
    intro z hz
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_center_iff.mp (hker hz) x).symm
  have hVcomm : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hV.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hCmap : (Subgroup.centralizer ({x} : Set U)).map φ =
      φ.range ⊓ Subgroup.centralizer ({φ x} : Set X) := by
    apply le_antisymm
    · rintro _ ⟨g, hg, rfl⟩
      refine ⟨⟨g, rfl⟩, ?_⟩
      have hgx : g * x = x * g := Subgroup.mem_centralizer_singleton_iff.mp hg
      exact Subgroup.mem_centralizer_singleton_iff.mpr (by rw [← map_mul, ← map_mul, hgx])
    · rintro y ⟨⟨g, rfl⟩, hy⟩
      have hgx : φ g * φ x = φ x * φ g := Subgroup.mem_centralizer_singleton_iff.mp hy
      have hcker : g * x * g⁻¹ * x⁻¹ ∈ φ.ker := by
        rw [MonoidHom.mem_ker]
        have h1 : φ g * φ x * (φ g)⁻¹ = φ x := by rw [hgx]; group
        simp only [map_mul, map_inv, h1, mul_inv_cancel]
      have hc1 : g * x * g⁻¹ * x⁻¹ = 1 := by
        refine eq_one_of_central_mul_involution (y := x) (hker hcker) ?_ hx2 hZ
        have hsplit : (g * x * g⁻¹ * x⁻¹) * x = g * x * g⁻¹ := by group
        rw [hsplit, pow_two]
        calc (g * x * g⁻¹) * (g * x * g⁻¹) = g * (x * x) * g⁻¹ := by group
          _ = 1 := by rw [hx2]; group
      refine ⟨g, ?_, rfl⟩
      refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
      have h : g * x * g⁻¹ = x := by
        have hsplit : g * x * g⁻¹ = (g * x * g⁻¹ * x⁻¹) * x := by group
        rw [hsplit, hc1, one_mul]
      calc g * x = g * x * g⁻¹ * g := by group
        _ = x * g := by rw [h]
  have hcore : (pCoreOf 2 (Subgroup.centralizer ({x} : Set U))).map φ =
      pCoreOf 2 ((Subgroup.centralizer ({x} : Set U)).map φ) :=
    LieKnownR2.map_pCoreOf_eq_of_odd_central_ker hker hodd hkerC
  have hxmem : x ∈ pCoreOf 2 (Subgroup.centralizer ({x} : Set U)) := by
    have h := CFSG.Timmesfeld.mem_map_pCore_centralizer (G := U) (D := {g : U | IsConj x g})
      ⟨x, rfl⟩ hD (IsConj.refl x) (IsConj.refl x) (Commute.refl x) (Or.inr rfl)
    simpa [pCoreOf] using h
  have hVle : V ≤ (pCoreOf 2 (Subgroup.centralizer ({x} : Set U))).map φ := by
    intro v hv
    by_cases hv1 : v = 1
    · rw [hv1]
      simpa using Subgroup.mem_map_of_mem φ
        (Subgroup.one_mem (pCoreOf 2 (Subgroup.centralizer ({x} : Set U))))
    · obtain ⟨k, hk, hvk⟩ := hconj v hv hv1
      obtain ⟨g, hg⟩ := hk
      rw [← hg] at hvk
      have hvφ : v = φ (g * x * g⁻¹) := by rw [hvk]; simp only [map_mul, map_inv]
      by_cases hveq : v = φ x
      · rw [hveq]
        exact Subgroup.mem_map_of_mem φ hxmem
      ·
        set gt : U := g * x * g⁻¹ with hgtdef
        have hφgt : φ gt = v := by rw [hgtdef]; exact hvφ.symm
        have hgt2 : gt * gt = 1 := by
          rw [hgtdef]
          calc (g * x * g⁻¹) * (g * x * g⁻¹) = g * (x * x) * g⁻¹ := by group
            _ = 1 := by rw [hx2]; group
        have hgtcomm : gt * x = x * gt :=
          commute_of_map_commute hker hZ hgt2 hx2 (by
            rw [hφgt]; exact hVcomm v hv (φ x) hxV)
        have hvin : v * φ x ∈ V := V.mul_mem hv hxV
        have hvine : v * φ x ≠ 1 := by
          intro h
          apply hveq
          have h1 : v = (φ x)⁻¹ := by
            calc v = v * φ x * (φ x)⁻¹ := by group
              _ = 1 * (φ x)⁻¹ := by rw [h]
              _ = (φ x)⁻¹ := one_mul _
          rw [h1, inv_eq_of_mul_eq_one_right hφx2]
        obtain ⟨k', hk', hvk'⟩ := hconj (v * φ x) hvin hvine
        obtain ⟨g', hg'⟩ := hk'
        rw [← hg'] at hvk'
        have hvk'' : v * φ x = φ (g' * x * g'⁻¹) := by
          rw [hvk']; simp only [map_mul, map_inv]
        have hgtxφ : φ (gt * x) = φ (g' * x * g'⁻¹) := by
          rw [map_mul, hφgt, hvk'']
        have hker' : (gt * x) * (g' * x * g'⁻¹)⁻¹ ∈ φ.ker := by
          rw [MonoidHom.mem_ker]
          simp only [map_mul, map_inv, hgtxφ, mul_inv_cancel]
        have hc' : (gt * x) * (g' * x * g'⁻¹)⁻¹ ∈ Subgroup.center U := hker hker'
        have hgtx2 : (gt * x) * (gt * x) = 1 := by
          calc (gt * x) * (gt * x) = gt * (x * gt) * x := by group
            _ = gt * (gt * x) * x := by rw [← hgtcomm]
            _ = (gt * gt) * (x * x) := by group
            _ = 1 := by rw [hgt2, hx2, mul_one]
        have hw2 : (g' * x * g'⁻¹) * (g' * x * g'⁻¹) = 1 := by
          calc (g' * x * g'⁻¹) * (g' * x * g'⁻¹) = g' * (x * x) * g'⁻¹ := by group
            _ = 1 := by rw [hx2]; group
        have hc'1 : (gt * x) * (g' * x * g'⁻¹)⁻¹ = 1 := by
          refine eq_one_of_central_mul_involution (y := g' * x * g'⁻¹) hc' ?_ hw2 hZ
          have hsplit : ((gt * x) * (g' * x * g'⁻¹)⁻¹) * (g' * x * g'⁻¹) = gt * x := by
            group
          rw [hsplit, pow_two]
          exact hgtx2
        have hgtxD : gt * x ∈ ({g : U | IsConj x g} : Set U) := by
          refine isConj_iff.mpr ⟨g', ?_⟩
          have hsplit : ((gt * x) * (g' * x * g'⁻¹)⁻¹) * (g' * x * g'⁻¹) = gt * x := by
            group
          rw [← hsplit, hc'1, one_mul]
        have hgtD : gt ∈ ({g : U | IsConj x g} : Set U) := isConj_iff.mpr ⟨g, hgtdef.symm⟩
        have hgtQ : gt ∈ pCoreOf 2 (Subgroup.centralizer ({x} : Set U)) := by
          have h := CFSG.Timmesfeld.mem_map_pCore_centralizer (G := U)
            (D := {g : U | IsConj x g}) ⟨x, rfl⟩ hD (IsConj.refl x) hgtD hgtcomm
            (Or.inl hgtxD)
          simpa [pCoreOf] using h
        rw [← hφgt]
        exact Subgroup.mem_map_of_mem φ hgtQ
  rw [← hCmap, ← hcore]
  exact hVle

theorem rckCollinearVia_of_long {M : LieUniversal} [Finite M.K] {n : Fin M.D.rank → M.K}
    {H : Fin M.D.rank → Subgroup M.K}
    (hct : IsCTGroupDatum (coxeterMatrix M.D.isFiniteType).toCoxeterSystem
      (weylAction M.D.isFiniteType) M.D.roots M.D.rootGroup n H)
    (hext : SteinbergExtras M.D n H) (hirr : IsIrreducible M.D.cartan)
    (hdiv : M.D.divisible = ∅) (hZ : CenterPPrime M.K 2) {β : Fin M.D.rank → ℤ}
    (hl : GGLongRoot M.D β) (hX : IsPGroup 2 (M.D.rootGroup β))
    (hC : ∀ u : M.K,
      ⁅pCoreOf 2 (Subgroup.normalizer (ggRootSub M.D (MonoidHom.id M.K) β u : Set M.K)),
        pCoreOf 2 (Subgroup.normalizer (ggRootSub M.D (MonoidHom.id M.K) β u : Set M.K))⁆ ≤
        ggRootSub M.D (MonoidHom.id M.K) β u) :
    RCKCollinearVia M β := by
  intro X _ _ K R V hvia hR2 r hr hr1 hrV _hVK hV _hV4 hconj
  obtain ⟨φ, hφrange, hφker, u, hR⟩ := hvia
  classical
  set Rr : Subgroup M.K := ggRootSub M.D (MonoidHom.id M.K) β u with hRrdef
  have hRmap : R = Rr.map φ := by
    rw [hR, hRrdef]
    exact LieKnownR2.Short.ggRootSub_eq_map M.D φ β u
  have hodd : Odd (Nat.card φ.ker) :=
    Odd.of_dvd_nat (LieKnownR2.OddCenter.odd_card_center_of_centerPPrime_two hZ)
      (Subgroup.card_dvd_of_le hφker)
  have hRrp : IsPGroup 2 Rr := by
    rw [hRrdef]
    exact (hX.map (MulAut.conj u).toMonoidHom).map (MonoidHom.id M.K)
  have hdisj : Rr ⊓ φ.ker = ⊥ := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hRrp
    have hdvd : Nat.card ↥(Rr ⊓ φ.ker) ∣ 2 ^ k := by
      rw [← hk]
      exact Subgroup.card_dvd_of_le inf_le_left
    have hodd' : Odd (Nat.card ↥(Rr ⊓ φ.ker)) :=
      Odd.of_dvd_nat hodd (Subgroup.card_dvd_of_le inf_le_right)
    rw [← Subgroup.card_eq_one]
    exact CFSG.Timmesfeld.Special.eq_one_of_odd_of_dvd_two_pow hodd' hdvd
  obtain ⟨x, hxRr, hxr⟩ := Subgroup.mem_map.mp (hRmap ▸ hr)
  have hxne : x ≠ 1 := by
    intro h
    apply hr1
    rw [← hxr, h, map_one]
  have hRr2 : Nat.card Rr = 2 := by
    have hinjOn : ∀ a ∈ Rr, ∀ b ∈ Rr, φ a = φ b → a = b := by
      intro a ha b hb hab
      have h1 : a * b⁻¹ ∈ Rr ⊓ φ.ker := by
        refine ⟨Rr.mul_mem ha (Rr.inv_mem hb), ?_⟩
        change a * b⁻¹ ∈ φ.ker
        rw [MonoidHom.mem_ker, map_mul, map_inv, hab, mul_inv_cancel]
      rw [hdisj] at h1
      have h2 : a * b⁻¹ = 1 := Subgroup.mem_bot.mp h1
      exact mul_right_cancel (h2.trans (mul_inv_cancel b).symm)
    have hinj : Function.Injective
        (fun a : Rr => (⟨φ a, by rw [hRmap]; exact Subgroup.mem_map_of_mem φ a.2⟩ : R)) := by
      intro a b hab
      exact Subtype.ext (hinjOn a a.2 b b.2 (congrArg Subtype.val hab))
    have hle : Nat.card Rr ≤ Nat.card R := Nat.card_le_card_of_injective _ hinj
    have hgt : 1 < Nat.card Rr := by
      rw [Subgroup.one_lt_card_iff_ne_bot]
      intro hbot
      exact hxne (Subgroup.mem_bot.mp (hbot ▸ hxRr))
    omega
  obtain ⟨w, γ₀, hγ₀mem, hγ₀max, hβ⟩ := hl
  have hγ₀ : CFSG.LieType.HighestRoot.IsHighestRoot M.D γ₀ :=
    isHighestRoot_of_forall_ht_le hirr hdiv hγ₀mem (by
      intro δ hδ
      simpa [ht] using hγ₀max δ hδ)
  set nw : M.K := nrep hct w with hnwdef
  have hroot : (M.D.rootGroup γ₀).map (MulAut.conj nw).toMonoidHom = M.D.rootGroup β := by
    rw [hnwdef, hβ]
    exact actsAs_nrep hct w γ₀ hγ₀mem
  have hcomp : (MulAut.conj u).toMonoidHom.comp (MulAut.conj nw).toMonoidHom =
      (MulAut.conj (u * nw)).toMonoidHom := by
    ext z
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hRrroot : Rr = (M.D.rootGroup γ₀).map (MulAut.conj (u * nw)).toMonoidHom := by
    rw [hRrdef]
    simp only [ggRootSub, Subgroup.map_id]
    rw [← hroot, Subgroup.map_map, hcomp]
  have hcardγ₀ : Nat.card (M.D.rootGroup γ₀) = 2 := by
    rw [← hRr2, hRrroot]
    exact (Subgroup.card_map_of_injective (K := M.D.rootGroup γ₀)
      (f := (MulAut.conj (u * nw)).toMonoidHom) (MulAut.conj (u * nw)).injective).symm
  set x₀ : M.K := (u * nw)⁻¹ * x * (u * nw) with hx₀def
  have hx₀mem : x₀ ∈ M.D.rootGroup γ₀ := by
    rw [hRrroot] at hxRr
    obtain ⟨z, hz, hzx⟩ := Subgroup.mem_map.mp hxRr
    have hzx' : (u * nw) * z * (u * nw)⁻¹ = x := by
      simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hzx
    have hx₀eq : x₀ = z := by rw [hx₀def, ← hzx']; group
    rw [hx₀eq]
    exact hz
  have hx₀ne : x₀ ≠ 1 := by
    intro h
    apply hxne
    calc x = (u * nw) * x₀ * (u * nw)⁻¹ := by rw [hx₀def]; group
      _ = 1 := by rw [h]; group
  have hD₀ : CFSG.Timmesfeld.IsRootInvolutionSet {g : M.K | IsConj x₀ g} :=
    isRootInvolutionSet_conj_rootGroup (D := M.D) (n := n) (H := H) hct hext hirr hdiv
      hγ₀ hcardγ₀ hx₀mem hx₀ne
  have hxconj : (u * nw) * x₀ * (u * nw)⁻¹ = x := by rw [hx₀def]; group
  have hconjx : IsConj x₀ x := isConj_iff.mpr ⟨u * nw, hxconj⟩
  have hD : CFSG.Timmesfeld.IsRootInvolutionSet {g : M.K | IsConj x g} := by
    have hset : {g : M.K | IsConj x₀ g} = {g : M.K | IsConj x g} := by
      ext g
      simp only [Set.mem_setOf_eq]
      exact ⟨fun h => hconjx.symm.trans h, fun h => hconjx.trans h⟩
    rwa [hset] at hD₀
  have hxrV : φ x ∈ V := by rw [hxr]; exact hrV
  have hconjφ : ∀ v ∈ V, v ≠ 1 → ∃ k ∈ φ.range, v = k * φ x * k⁻¹ := by
    intro v hv hv1
    obtain ⟨k, hk, hvk⟩ := hconj v hv hv1
    refine ⟨k, ?_, ?_⟩
    · rw [hφrange]; exact hk
    · rw [hxr]; exact hvk
  have hVQ : V ≤ pCoreOf 2 (K ⊓ Subgroup.centralizer ({r} : Set X)) := by
    have h := le_pCoreOf_of_isRootInvolutionSet (U := M.K) (X := X) (φ := φ) (x := x)
      hφker hZ hD hxrV hV hconjφ
    rwa [hφrange, hxr] at h
  have hcentRr : pCoreOf 2 (Subgroup.normalizer (Rr : Set M.K)) ≤
      Subgroup.centralizer (Rr : Set M.K) := by
    refine (GGRootNorm.pCoreOf_le (Subgroup.normalizer (Rr : Set M.K))).trans ?_
    intro k hk
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have hks : k * s * k⁻¹ ∈ Rr := (Subgroup.mem_normalizer_iff.mp hk s).mp hs
    rcases eq_one_or_eq_of_mem_of_card_eq_two hRr2 hxRr hxne hs with hs1 | hsx
    · rw [hs1, mul_one, one_mul]
    · rw [hsx] at hks ⊢
      have hksne : k * x * k⁻¹ ≠ 1 := by
        intro h
        apply hxne
        calc x = k⁻¹ * (k * x * k⁻¹) * k := by group
          _ = 1 := by rw [h]; group
      rcases eq_one_or_eq_of_mem_of_card_eq_two hRr2 hxRr hxne hks with h1 | h1
      · exact absurd h1 hksne
      · have hkx : k * x = x * k := by
          calc k * x = (k * x * k⁻¹) * k := by group
            _ = x * k := by rw [h1]
        exact hkx.symm
  have hcommC : ⁅pCoreOf 2 (Subgroup.normalizer (Rr : Set M.K)),
      pCoreOf 2 (Subgroup.normalizer (Rr : Set M.K))⁆ ≤ Rr := by
    rw [hRrdef]
    exact hC u
  have hNR : K ⊓ Subgroup.normalizer (R : Set X) =
      K ⊓ Subgroup.centralizer ({r} : Set X) := by
    apply le_antisymm
    · rintro k ⟨hkK, hk⟩
      refine ⟨hkK, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      have hkr : k * r * k⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp hk r).mp hr
      have hkrne : k * r * k⁻¹ ≠ 1 := by
        intro h
        apply hr1
        calc r = k⁻¹ * (k * r * k⁻¹) * k := by group
          _ = 1 := by rw [h]; group
      rcases eq_one_or_eq_of_mem_of_card_eq_two hR2 hr hr1 hkr with h1 | h1
      · exact absurd h1 hkrne
      · have h2 : k * r = r * k := by
          calc k * r = (k * r * k⁻¹) * k := by group
            _ = r * k := by rw [h1]
        exact h2
    · rintro k ⟨hkK, hk⟩
      have hkr : k * r = r * k := Subgroup.mem_centralizer_singleton_iff.mp hk
      refine ⟨hkK, Subgroup.mem_normalizer_iff.mpr fun s => ?_⟩
      constructor
      · intro hs
        rcases eq_one_or_eq_of_mem_of_card_eq_two hR2 hr hr1 hs with hs1 | hsr
        · rw [hs1]; simp
        · rw [hsr]
          rwa [show k * r * k⁻¹ = r by rw [hkr]; group]
      · intro hs
        rcases eq_one_or_eq_of_mem_of_card_eq_two hR2 hr hr1 hs with h1 | h1
        · have hs1 : s = 1 := by
            calc s = k⁻¹ * (k * s * k⁻¹) * k := by group
              _ = 1 := by rw [h1]; group
          rw [hs1]; exact R.one_mem
        · have hsr : s = r := by
            calc s = k⁻¹ * (k * s * k⁻¹) * k := by group
              _ = k⁻¹ * r * k := by rw [h1]
              _ = k⁻¹ * (r * k) := by group
              _ = k⁻¹ * (k * r) := by rw [← hkr]
              _ = r := by group
          rw [hsr]; exact hr
  have hQQ : ⁅pCoreOf 2 (K ⊓ Subgroup.centralizer ({r} : Set X)),
      pCoreOf 2 (K ⊓ Subgroup.centralizer ({r} : Set X))⁆ ≤ R := by
    have h := (LieKnownR2.Short.itemFour_of_core (U := M.K) (X := X) (ψ := φ) (Rr := Rr)
      hφker hodd hRrp hcommC hcentRr).1
    rw [← hRmap, hφrange, hNR] at h
    exact h
  have hRV : R ≤ V := by
    intro s hs
    rcases eq_one_or_eq_of_mem_of_card_eq_two hR2 hr hr1 hs with hs1 | hsr
    · rw [hs1]; exact V.one_mem
    · rw [hsr]; exact hrV
  exact le_normalizer_of_commutator_le hVQ hQQ hRV

end CFSG.StandardType.RCKC1
