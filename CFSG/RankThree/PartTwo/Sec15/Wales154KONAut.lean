module

public import CFSG.RankThree.PartTwo.Sec15.Wales154KFacts
import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCF23ONOutCard
import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCF23ONOutK3Main
import CFSG.LocalAnalysis.GLTheoremA.S8.I1425ONNative
import CFSG.RankThree.PartTwo.Sec15.Item15Res8ProofDiagK

public section

namespace CFSG.RankThree.PartTwo.Sec15.Wales154

open Subgroup CFSG.ComponentClassification CFSG.Blueprint

private theorem exists_perfect_le_centralizer {Y : Type*} [Group Y] [Finite Y]
    {V O : Subgroup Y} [Group.IsPerfect V] (hOV : O ≤ V) (hO : IsPGroup 2 O)
    (hVO : ∀ v ∈ V, ∀ o ∈ O, v * o * v⁻¹ ∈ O) {g : Y} (hg : g ^ 3 = 1)
    (hgO : ∀ o ∈ O, g * o * g⁻¹ ∈ O) (hgV : ∀ v ∈ V, v⁻¹ * (g * v * g⁻¹) ∈ O)
    (h5 : 5 ∣ Nat.card V) :
    ∃ V₀ : Subgroup Y, V₀ ≤ V ∧ V₀ ≤ centralizer ({g} : Set Y) ∧ Group.IsPerfect V₀ ∧
      5 ∣ Nat.card V₀ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hfix : ∀ v ∈ V, ∃ o ∈ O, v * o ∈ centralizer ({g} : Set Y) := by
    intro v hv
    have hθ : MulAut.conj g ^ (3 ^ 1) = 1 := by rw [pow_one, ← map_pow, hg, map_one]
    have hcop : ¬ 3 ∣ Nat.card O := by
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hO
      rw [hn]
      intro h
      have := Nat.prime_three.dvd_of_dvd_pow h
      norm_num at this
    obtain ⟨o, ho, hfx⟩ := CFSG.GH74.GLS.SP.exists_fixed_mul_mem_of_coprime (MulAut.conj g) hθ O
      (fun o ho => by rw [MulAut.conj_apply]; exact hgO o ho) hcop
      (by rw [MulAut.conj_apply]; exact hgV v hv)
    refine ⟨o, ho, mem_centralizer_singleton_iff.mpr ?_⟩
    rw [MulAut.conj_apply] at hfx
    calc v * o * g = g * (v * o) * g⁻¹ * g := by rw [hfx]
      _ = g * (v * o) := by group
  set N : Subgroup V := O.subgroupOf V with hN
  haveI : N.Normal := ⟨fun n hn v => by
    rw [hN, mem_subgroupOf] at hn ⊢
    simpa using hVO v v.2 n hn⟩
  set C : Subgroup Y := V ⊓ centralizer ({g} : Set Y)
  set ψ : C →* V ⧸ N := (QuotientGroup.mk' N).comp (inclusion inf_le_left) with hψdef
  have hψ : Function.Surjective ψ := by
    intro y
    obtain ⟨v, rfl⟩ := QuotientGroup.mk'_surjective N y
    obtain ⟨o, ho, hvo⟩ := hfix v v.2
    refine ⟨⟨v * o, V.mul_mem v.2 (hOV ho), hvo⟩, ?_⟩
    rw [hψdef, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq, hN, mem_subgroupOf]
    have h1 : (((inclusion (inf_le_left : C ≤ V) ⟨(v : Y) * o, V.mul_mem v.2 (hOV ho), hvo⟩)⁻¹ *
        v : V) : Y) = o⁻¹ := by
      simp [mul_assoc]
    rw [h1]
    exact O.inv_mem ho
  obtain ⟨n, -, hn⟩ := CFSG.exists_perfectResidual_eq_derivedSeries (G := C)
  haveI : Group.IsPerfect (derivedSeries C n) :=
    isPerfect_iff.mpr (by rw [← derivedSeries_succ, ← hn])
  have hmap : (derivedSeries C n).map ψ = ⊤ := by
    rw [map_derivedSeries_eq hψ, Group.IsPerfect.derivedSeries_eq_top]
  have h5q : 5 ∣ Nat.card (V ⧸ N) := by
    have h1 := card_eq_card_quotient_mul_card_subgroup N
    obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp (hO.of_equiv (subgroupOfEquivOfLe hOV).symm)
    rw [ha] at h1
    rw [h1] at h5
    exact (Nat.Coprime.pow_right a (by norm_num : Nat.Coprime 5 2)).dvd_of_dvd_mul_right h5
  have h5D : 5 ∣ Nat.card (derivedSeries C n) := by
    have h1 := card_map_dvd (H := derivedSeries C n) ψ
    rw [hmap, card_top] at h1
    exact h5q.trans h1
  refine ⟨(derivedSeries C n).map C.subtype, (map_subtype_le _).trans inf_le_left,
    (map_subtype_le _).trans inf_le_right, Group.IsPerfect.map _, ?_⟩
  rw [card_map_of_injective C.subtype_injective]
  exact h5D

section ON


private theorem false_of_outer_fix {Y : Type} [Group Y] [Finite Y] (e : Y ≃* NativeSporadic.ON)
    {g : Y} (hg : orderOf g = 3) {V₀ : Subgroup Y} (hV₀p : Group.IsPerfect V₀)
    (h5 : 5 ∣ Nat.card V₀) (hV₀ : V₀ ≤ centralizer ({g} : Set Y)) {τ : MulAut Y}
    (hτ2 : τ * τ = 1) (hτ : τ ∉ OuterAutomorphisms.inner Y) (hτV : ∀ v ∈ V₀, τ v = v)
    (hτg : τ g = g) : False := by
  classical
  haveI := hV₀p
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Cg := centralizer ({g} : Set Y)
  obtain ⟨E, hEn, ⟨eE⟩, hidx⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.S8.L84.alt6_normal_centralizer_ON e hg
  haveI := hEn
  obtain ⟨-, hZE, -⟩ := CFSG.LocalAnalysis.GLTheoremA.S8.L84.alt6_split eE hidx
  set W : Subgroup Cg := V₀.subgroupOf Cg
  have eW : W ≃* V₀ := subgroupOfEquivOfLe hV₀
  haveI : Group.IsPerfect W :=
    Group.IsPerfect.ofSurjective (f := eW.symm.toMonoidHom) eW.symm.surjective
  have hWE : W ≤ E := by
    have hab := IsPGroup.commutative_of_card_eq_prime_sq (p := 3) (G := Cg ⧸ E)
      (by rw [← index_eq_card, hidx]; norm_num)
    haveI : Group.IsPerfect (W.map (QuotientGroup.mk' E)) := Group.IsPerfect.map _
    haveI : IsMulCommutative (W.map (QuotientGroup.mk' E)) :=
      ⟨⟨fun a b => Subtype.ext (hab a b)⟩⟩
    intro w hw
    have h1 : (⟨QuotientGroup.mk' E w, mem_map_of_mem _ hw⟩ : W.map (QuotientGroup.mk' E)) = 1 :=
      Subsingleton.elim _ _
    have h2 : QuotientGroup.mk' E w = 1 := congrArg Subtype.val h1
    rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
  have hdisj : ∀ y ∈ V₀, y ∈ zpowers g → y = 1 := by
    intro y hyV hyg
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hyg
    have hcen : (⟨g ^ k, hV₀ hyV⟩ : Cg) ∈ center Cg := by
      rw [mem_center_iff]
      intro c
      apply Subtype.ext
      exact (Commute.zpow_right (mem_centralizer_singleton_iff.mp c.2) k).eq
    have hE : (⟨g ^ k, hV₀ hyV⟩ : Cg) ∈ E := hWE (mem_subgroupOf.mpr hyV)
    have h1 : (⟨g ^ k, hV₀ hyV⟩ : Cg) ∈ center Cg ⊓ E := ⟨hcen, hE⟩
    rw [hZE, mem_bot] at h1
    exact congrArg Subtype.val h1
  set W' : Subgroup E := W.subgroupOf E
  have eW' : W' ≃* W := subgroupOfEquivOfLe hWE
  haveI hW'p : Group.IsPerfect W' :=
    Group.IsPerfect.ofSurjective (f := eW'.symm.toMonoidHom) eW'.symm.surjective
  have hcard : Nat.card W' = Nat.card V₀ :=
    (Nat.card_congr eW'.toEquiv).trans (Nat.card_congr eW.toEquiv)
  have hW'1 : W' ≠ ⊥ := by
    intro hb
    rw [hb, card_bot] at hcard
    rw [← hcard] at h5
    norm_num at h5
  have hV₀card : Nat.card V₀ = 360 ∨ Nat.card V₀ = 60 := by
    rcases RankThree.PartTwo.Sec15.Proof15Res8Diag.eq_top_or_card_eq_sixty_six eE hW'p hW'1 with
      ht | ⟨-, h60⟩
    · left
      rw [← hcard, ht, card_top]
      exact RankThree.PartTwo.Sec15.Proof15Res8Diag.card_six eE
    · right
      rw [← hcard, h60]
  have hF : Nat.card (Sporadic.Schreier.fixSub τ) = 175560 :=
    SolMax.card_fixSub_of_local SolMax.ONOut.onOuterLocalInput_holds ⟨e⟩ τ hτ2 hτ
  have hcomm : ∀ (a : V₀) (b : zpowers g), Commute (V₀.subtype a) ((zpowers g).subtype b) := by
    rintro ⟨a, ha⟩ ⟨b, hb⟩
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hb
    exact Commute.zpow_right (mem_centralizer_singleton_iff.mp (hV₀ ha)) k
  set f : V₀ × zpowers g →* Y := V₀.subtype.noncommCoprod (zpowers g).subtype hcomm
  have hfinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ hab
    have hab' : a * b = 1 := hab
    have ha1 : a = 1 := hdisj a ha (by rw [eq_inv_of_mul_eq_one_left hab']; exact inv_mem hb)
    subst ha1
    rw [one_mul] at hab'
    subst hab'
    rfl
  have hle : f.range ≤ Sporadic.Schreier.fixSub τ := by
    rintro _ ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, rfl⟩
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hb
    show τ (a * g ^ k) = a * g ^ k
    rw [map_mul, map_zpow, hτV a ha, hτg]
  have hdvd : Nat.card V₀ * 3 ∣ 175560 := by
    have h1 : Nat.card f.range = Nat.card V₀ * 3 := by
      rw [← Nat.card_congr (MonoidHom.ofInjective hfinj).toEquiv, Nat.card_prod, Nat.card_zpowers,
        hg]
    rw [← h1, ← hF]
    exact card_dvd_of_le hle
  rcases hV₀card with h | h <;> rw [h] at hdvd <;> norm_num at hdvd

theorem ks154ON_of_core (h : KS154ONCore) : KS154ON := by
  intro Q _ _ hQ htc K hKp h5 α hα3 _ hαO P hP hKP hαP
  unfold KS154ONCore at h
  classical
  haveI : Group.IsPerfect Q := hQ.1
  haveI : Group.IsPerfect K := hKp
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have : Finite (MulAut Q) :=
    Finite.of_injective (fun f : MulAut Q => (f : Q → Q)) DFunLike.coe_injective
  obtain ⟨hZ3, ⟨φ⟩⟩ := htc
  set Z := center Q with hZ
  haveI : Finite (Q ⧸ Z) := Finite.of_surjective _ (QuotientGroup.mk'_surjective Z)
  set π : Q →* Q ⧸ Z := QuotientGroup.mk' Z with hπ
  set c : Q →* MulAut Q := MulAut.conj with hc
  have hπZ : ∀ q : Q, π q = 1 ↔ q ∈ Z := fun q => by
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hcZ : ∀ q : Q, c q = 1 ↔ q ∈ Z := by
    intro q
    constructor
    · intro hq
      rw [hZ, mem_center_iff]
      intro x
      have h1 := congrArg (fun σ : MulAut Q => σ x) hq
      simp only [hc, MulAut.conj_apply, MulAut.one_apply] at h1
      calc x * q = q * x * q⁻¹ * q := by rw [h1]
        _ = q * x := by group
    · intro hq
      ext x
      rw [hc, MulAut.conj_apply, MulAut.one_apply, ← mem_center_iff.mp hq x,
        mul_inv_cancel_right]
  have hαinn : α ∈ OuterAutomorphisms.inner Q := by
    have hout : Nat.card (OuterAutomorphisms.Outer (Q ⧸ Z)) ∣ 2 :=
      Sporadic.SteinbergBI.cti_on_outer_order_divides_two ⟨φ⟩
    have ho3 : (QuotientGroup.mk (s := OuterAutomorphisms.inner Q) α) ^ 3 = 1 := by
      rw [← QuotientGroup.mk_pow, ← hα3, pow_orderOf_eq_one, QuotientGroup.mk_one]
    have ho2 : (QuotientGroup.mk (s := OuterAutomorphisms.inner Q) α) ^ 2 = 1 := by
      apply OuterAutomorphisms.centerQuotient_outer_injective Q
      rw [map_pow, map_one]
      exact orderOf_dvd_iff_pow_eq_one.mp ((_root_.orderOf_dvd_natCard _).trans hout)
    have ho1 : (QuotientGroup.mk (s := OuterAutomorphisms.inner Q) α) = 1 := by
      calc (QuotientGroup.mk (s := OuterAutomorphisms.inner Q) α) =
            (QuotientGroup.mk (s := OuterAutomorphisms.inner Q) α) ^ 3 *
              ((QuotientGroup.mk (s := OuterAutomorphisms.inner Q) α) ^ 2)⁻¹ := by group
        _ = 1 := by rw [ho3, ho2, inv_one, mul_one]
    exact (QuotientGroup.eq_one_iff α).mp ho1
  obtain ⟨q₀, hq₀⟩ := hαinn
  change c q₀ = α at hq₀
  have hq₀N : c q₀ ∈ normalizer (P : Set (MulAut Q)) := hq₀ ▸ hαP
  set g : Q ⧸ Z := π q₀ with hg
  have hgπ : ∀ q : Q, g * π q * g⁻¹ = π (α q) := by
    intro q
    rw [← hq₀, hc, MulAut.conj_apply, map_mul, map_mul, map_inv]
  have hg3 : orderOf g = 3 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [hg, ← map_pow, hπZ, ← hcZ, map_pow, hq₀, ← hα3, pow_orderOf_eq_one]
    · intro h1
      rw [hg, hπZ, ← hcZ, hq₀] at h1
      rw [h1, orderOf_one] at hα3
      exact absurd hα3 (by norm_num)
  set OK : Subgroup Q := (CFSG.pCore 2 ↥K).map K.subtype
  have hOKK : OK ≤ K := map_subtype_le _
  have hKOK : ∀ k ∈ K, ∀ p ∈ OK, k * p * k⁻¹ ∈ OK := by
    rintro k hk _ ⟨p, hp, rfl⟩
    exact ⟨⟨k, hk⟩ * p * ⟨k, hk⟩⁻¹, (CFSG.pCore_normal (p := 2) (G := ↥K)).conj_mem p hp ⟨k, hk⟩,
      by simp⟩
  set V : Subgroup (Q ⧸ Z) := K.map π
  set O : Subgroup (Q ⧸ Z) := OK.map π
  haveI : Group.IsPerfect V := Group.IsPerfect.map π
  have hVO : ∀ v ∈ V, ∀ o ∈ O, v * o * v⁻¹ ∈ O := by
    rintro _ ⟨k, hk, rfl⟩ _ ⟨p, hp, rfl⟩
    exact ⟨k * p * k⁻¹, hKOK k hk p hp, by simp only [map_mul, map_inv]⟩
  have hgO : ∀ o ∈ O, g * o * g⁻¹ ∈ O := by
    rintro _ ⟨p, hp, rfl⟩
    rw [hgπ]
    refine ⟨α p, ?_, rfl⟩
    simpa using OK.mul_mem (hαO p (hOKK hp)) hp
  have hgV : ∀ v ∈ V, v⁻¹ * (g * v * g⁻¹) ∈ O := by
    rintro _ ⟨k, hk, rfl⟩
    rw [hgπ]
    refine ⟨k⁻¹ * α k, ?_, by simp only [map_mul, map_inv]⟩
    simpa [mul_assoc] using hKOK k⁻¹ (K.inv_mem hk) _ (hαO k hk)
  have h5V : 5 ∣ Nat.card V := by
    obtain ⟨⟨y, hyK⟩, hy⟩ := exists_prime_orderOf_dvd_card' (G := K) 5 h5
    rw [Subgroup.orderOf_mk] at hy
    have hdvd : orderOf (π y) ∣ 5 := by
      rw [← hy]
      exact orderOf_map_dvd π y
    have hπy : orderOf (π y) = 5 := by
      rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp hdvd with h1 | h1
      · rw [orderOf_eq_one_iff, hπZ] at h1
        have h3 := Subgroup.orderOf_dvd_natCard Z h1
        rw [hy, hZ3] at h3
        norm_num at h3
      · exact h1
    rw [← hπy]
    exact Subgroup.orderOf_dvd_natCard V ⟨y, hyK, rfl⟩
  have hg3' : g ^ 3 = 1 := by
    rw [← hg3]
    exact pow_orderOf_eq_one g
  obtain ⟨V₀, hV₀V, hV₀C, hV₀p, hV₀5⟩ := exists_perfect_le_centralizer (map_mono hOKK : O ≤ V)
    (((CFSG.pCore_isPGroup (p := 2) (G := ↥K)).map K.subtype).map π) hVO hg3' hgO hgV h5V
  set S : Subgroup (Q ⧸ Z) := (P.comap c).map π
  have hS2 : IsPGroup 2 S := by
    rintro ⟨_, q, hq, rfl⟩
    rw [SetLike.mem_coe, mem_comap] at hq
    obtain ⟨n, hn⟩ := hP ⟨c q, hq⟩
    refine ⟨n, Subtype.ext ?_⟩
    have h1 : c (q ^ 2 ^ n) = 1 := by
      rw [map_pow]
      simpa using congrArg Subtype.val hn
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [← map_pow, hπZ, ← hcZ]
    exact h1
  have hVS : V ≤ normalizer (S : Set (Q ⧸ Z)) :=
    (map_mono fun k hk => le_normalizer_comap c (mem_comap.mpr (hKP k hk))).trans
      (le_normalizer_map π)
  have hgS : g ∈ normalizer (S : Set (Q ⧸ Z)) :=
    le_normalizer_map π (mem_map_of_mem π (le_normalizer_comap c (mem_comap.mpr hq₀N)))
  have hSbot : S = ⊥ :=
    h (Q ⧸ Z) ⟨φ⟩ V₀ g hV₀p hV₀5 hg3 hV₀C S hS2 (hV₀V.trans hVS) hgS
  have hPinn : ∀ q : Q, c q ∈ P → q ∈ Z := by
    intro q hq
    have hqS : π q ∈ S := mem_map_of_mem π (mem_comap.mpr hq)
    rwa [hSbot, mem_bot, hπZ] at hqS
  by_contra hne
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hP
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hne (eq_bot_of_card_eq _ (by rw [hm, pow_zero]))
  obtain ⟨⟨τ, hτP⟩, hτ⟩ := exists_prime_orderOf_dvd_card' 2 (by rw [hm]; exact dvd_pow_self 2 hm0)
  rw [Subgroup.orderOf_mk] at hτ
  have hτ2 : τ * τ = 1 := by rw [← sq, ← hτ, pow_orderOf_eq_one]
  have hτ1 : τ ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hτ
    exact absurd hτ (by norm_num)
  have hτc : ∀ q : Q, c (τ q * q⁻¹) = τ * (c q * τ⁻¹ * (c q)⁻¹) := by
    intro q
    ext x
    simp [hc, MulAut.conj_apply, MulAut.mul_apply, MulAut.inv_apply, mul_assoc]
  have hτZ : ∀ q : Q, c q ∈ normalizer (P : Set (MulAut Q)) → τ q * q⁻¹ ∈ Z := by
    intro q hq
    apply hPinn
    rw [hτc]
    exact P.mul_mem hτP ((mem_normalizer_iff.mp hq τ⁻¹).mp (P.inv_mem hτP))
  set τb : MulAut (Q ⧸ Z) := PerfectAutomorphisms.centerQuotientHom Q τ with hτb
  have hτbπ : ∀ q : Q, c q ∈ normalizer (P : Set (MulAut Q)) → τb (π q) = π q := by
    intro q hq
    have h1 : π (τ q * q⁻¹) = 1 := (hπZ _).mpr (hτZ q hq)
    rw [map_mul, map_inv, mul_inv_eq_one] at h1
    exact (PerfectAutomorphisms.onCenterQuotient_apply_mk τ q).trans h1
  have hτbV : ∀ v ∈ V₀, τb v = v := by
    intro v hv
    obtain ⟨k, hk, rfl⟩ := hV₀V hv
    exact hτbπ k (hKP k hk)
  have hτbg : τb g = g := hτbπ q₀ hq₀N
  have hτb2 : τb * τb = 1 := by rw [hτb, ← map_mul, hτ2, map_one]
  have hτbout : τb ∉ OuterAutomorphisms.inner (Q ⧸ Z) := by
    rintro ⟨x, hx⟩
    obtain ⟨q, rfl⟩ := QuotientGroup.mk'_surjective Z x
    have h2 : c q = τ := PerfectAutomorphisms.centerQuotientHom_injective Q
      ((OuterAutomorphisms.centerQuotient_conj q).trans hx)
    have h3 : c q = 1 := (hcZ q).mpr (hPinn q (h2 ▸ hτP))
    exact hτ1 (h2.symm.trans h3)
  exact false_of_outer_fix φ hg3 hV₀p hV₀5 hV₀C hτb2 hτbout hτbV hτbg

end ON

end CFSG.RankThree.PartTwo.Sec15.Wales154
