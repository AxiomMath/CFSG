module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeTools
public import CFSG.GroupTheory.SupMulCommutative
public import CFSG.LocalAnalysis.GLTheoremA.Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

private theorem s168e3_isElemAbelianOfRank_of_card {p n : ℕ} [hp : Fact p.Prime] {X : Type*}
    [Group X] [Finite X] (hc : ∀ x y : X, x * y = y * x) (hexp : ∀ x : X, x ^ p = 1)
    (hcard : Nat.card X = p ^ n) : IsElemAbelianOfRank p n X := by
  classical
  letI : CommGroup X := { ‹Group X› with mul_comm := hc }
  let inst : Module (ZMod p) (Additive X) := AddCommGroup.zmodModule fun x => by
    change Additive.ofMul (x.toMul ^ p) = 0
    rw [hexp]
    rfl
  have hfinite : Module.Finite (ZMod p) (Additive X) := Module.Finite.of_finite
  have hfin : Module.finrank (ZMod p) (Additive X) = n := by
    have h := @Module.natCard_eq_pow_finrank (ZMod p) (Additive X) _ _ inst hfinite
    rw [Nat.card_zmod, show Nat.card (Additive X) = Nat.card X from rfl, hcard] at h
    exact (Nat.pow_right_injective hp.out.two_le h).symm
  have hfree : @Module.Free (ZMod p) (Additive X) _ _ inst :=
    @Module.Free.of_divisionRing (ZMod p) (Additive X) _ _ inst
  let b : Module.Basis (Fin n) (ZMod p) (Additive X) :=
    @Module.finBasisOfFinrankEq (ZMod p) (Additive X) _ _ inst hfree _ hfinite n hfin
  exact ⟨MulEquiv.toAdditiveLeft.symm
    (LinearEquiv.toAddEquiv (@Module.Basis.equivFun _ _ _ _ _ inst _ b))⟩

theorem s168e3_kernel_cap {M Q : Type*} [Group M] [Finite M] [Group Q] [Finite Q] (φ : M →* Q)
    {p : ℕ} (hp : p.Prime) (hker : CFSG.Open.pRank p φ.ker ≤ 1)
    (hrange : CFSG.Open.pRank p φ.range ≤ 2) {A : Subgroup M} (hA : IsElemAbelian p A)
    (hcard : Nat.card ↥A = p ^ 3) :
    Nat.card ↥(A ⊓ φ.ker) = p ∧ IsElemAbelianOfRank p 2 ↥(A.map φ) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hAk : IsElemAbelian p (A ⊓ φ.ker) := hA.mono inf_le_left
  have hAm : IsElemAbelian p (A.map φ) := hA.map φ
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hAk.isPGroup
  obtain ⟨b, hb⟩ := IsPGroup.iff_card.mp hAm.isPGroup
  have hrik : φ.ker.relIndex A = Nat.card ↥(A.map φ) := Subgroup.relIndex_ker (K := A) φ
  have hprod := Subgroup.relIndex_mul_card (H := φ.ker) (K := A)
  rw [hrik, inf_comm, ha, hb, hcard, ← pow_add] at hprod
  have hsum : b + a = 3 := Nat.pow_right_injective hp.two_le hprod
  have ha1 : a ≤ 1 := by
    have h := CFSG.SectionRank.le_pRank hp.one_lt (H := φ.ker) (E := A ⊓ φ.ker)
      inf_le_right hAk ha
    omega
  have hb2 : b ≤ 2 := by
    have h := CFSG.SectionRank.le_pRank hp.one_lt (H := φ.range) (E := A.map φ)
      (Subgroup.map_le_range φ A) hAm hb
    omega
  have haeq : a = 1 := by omega
  have hbeq : b = 2 := by omega
  refine ⟨?_, ?_⟩
  · rw [ha, haeq, pow_one]
  · exact s168e3_isElemAbelianOfRank_of_card (p := p) (n := 2)
      (fun x y => hAm.1.is_comm.comm x y)
      (fun x => by
        refine Subtype.ext ?_
        rw [Subgroup.coe_pow, Subgroup.coe_one]
        exact hAm.2 x.1 x.2)
      (by rw [hb, hbeq])

theorem s168e3_noncyclic_fix_of_conj {M T : Type*} [Group M] [CommGroup T] (φ : M →* MulAut T)
    {p : ℕ} (hp : p.Prime) {A : Subgroup M} (hA : IsElemAbelian p A) {z : M} (hzA : z ∈ A)
    (hz1 : z ≠ 1) (hzφ : φ z = 1) {a : M} (haA : a ∈ A) (ha1 : φ a ≠ 1) (g : M) {x : T}
    (hfix : φ (g * a * g⁻¹) x = x) :
    ∃ B : Subgroup M, IsPGroup p ↥B ∧ ¬ IsCyclic ↥B ∧ ∀ b ∈ B, φ b x = x := by
  haveI : Fact p.Prime := ⟨hp⟩
  let z' : M := g * z * g⁻¹
  let a' : M := g * a * g⁻¹
  have hzp : z ^ p = 1 := hA.2 z hzA
  have hap : a ^ p = 1 := hA.2 a haA
  have hz'p : z' ^ p = 1 := by
    simp only [z']
    rw [conj_pow, hzp]
    group
  have ha'p : a' ^ p = 1 := by
    simp only [a']
    rw [conj_pow, hap]
    group
  have hza : z * a = a * z :=
    congrArg Subtype.val (hA.1.is_comm.comm ⟨z, hzA⟩ ⟨a, haA⟩)
  have hcomm : z' * a' = a' * z' := by
    calc z' * a' = g * (z * a) * g⁻¹ := by simp only [z', a']; group
      _ = g * (a * z) * g⁻¹ := by rw [hza]
      _ = a' * z' := by simp only [z', a']; group
  have hz'1 : z' ≠ 1 := by
    intro h
    apply hz1
    have h2 : g⁻¹ * z' * g = z := by simp only [z']; group
    rw [h] at h2
    simpa using h2.symm
  have hz'φ : φ z' = 1 := by
    simp only [z', map_mul, map_inv, hzφ]
    group
  have ha'φ : φ a' ≠ 1 := by
    intro h
    apply ha1
    have h2 : (φ g)⁻¹ * φ a' * φ g = φ a := by
      simp only [a', map_mul, map_inv]
      group
    rw [h] at h2
    simpa using h2.symm
  have hnya : a' ∉ Subgroup.zpowers z' := by
    intro hmem
    have hmem' : ∃ k : ℤ, z' ^ k = a' := Subgroup.mem_zpowers_iff.mp hmem
    obtain ⟨k, hk⟩ := hmem'
    apply ha'φ
    rw [← hk, map_zpow, hz'φ, one_zpow]
  have hz'ord : orderOf z' = p := by
    have hdvd : orderOf z' ∣ p := orderOf_dvd_iff_pow_eq_one.mpr hz'p
    rcases (Nat.dvd_prime hp).1 hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hz'1
    · exact h
  have ha'1 : a' ≠ 1 := fun h => ha'φ (by rw [h, map_one])
  have ha'ord : orderOf a' = p := by
    have hdvd : orderOf a' ∣ p := orderOf_dvd_iff_pow_eq_one.mpr ha'p
    rcases (Nat.dvd_prime hp).1 hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) ha'1
    · exact h
  have hHcard : Nat.card (Subgroup.zpowers z') = p := by
    rw [Nat.card_zpowers, hz'ord]
  have hKcard : Nat.card (Subgroup.zpowers a') = p := by
    rw [Nat.card_zpowers, ha'ord]
  have hfinH : Finite ↥(Subgroup.zpowers z') :=
    Nat.finite_of_card_ne_zero (by rw [hHcard]; exact hp.ne_zero)
  have hfinK : Finite ↥(Subgroup.zpowers a') :=
    Nat.finite_of_card_ne_zero (by rw [hKcard]; exact hp.ne_zero)
  have hinf : Subgroup.zpowers z' ⊓ Subgroup.zpowers a' = ⊥ := by
    by_contra hne
    have hdvd : Nat.card ↥(Subgroup.zpowers z' ⊓ Subgroup.zpowers a') ∣ p := by
      rw [← hHcard]
      exact Subgroup.card_dvd_of_le inf_le_left
    have hne1 : Nat.card ↥(Subgroup.zpowers z' ⊓ Subgroup.zpowers a') ≠ 1 := by
      intro h1
      exact hne (Subgroup.eq_bot_of_card_eq
        (H := Subgroup.zpowers z' ⊓ Subgroup.zpowers a') h1)
    have hcardp : Nat.card ↥(Subgroup.zpowers z' ⊓ Subgroup.zpowers a') = p := by
      rcases (Nat.dvd_prime hp).1 hdvd with h | h
      · exact absurd h hne1
      · exact h
    have hEqH : Subgroup.zpowers z' ⊓ Subgroup.zpowers a' = Subgroup.zpowers z' :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hcardp, hHcard])
    have hEqK : Subgroup.zpowers z' ⊓ Subgroup.zpowers a' = Subgroup.zpowers a' :=
      Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [hcardp, hKcard])
    have hHK : Subgroup.zpowers z' = Subgroup.zpowers a' := hEqH.symm.trans hEqK
    apply hnya
    rw [hHK]
    exact Subgroup.mem_zpowers a'
  have hcent : Subgroup.zpowers a' ≤ Subgroup.centralizer (Subgroup.zpowers z' : Set M) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro w hw
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    exact ((Commute.zpow_right (show Commute a' z' from hcomm.symm) i).eq).symm
  have hnorm : Subgroup.zpowers a' ≤ Subgroup.normalizer (Subgroup.zpowers z' : Set M) :=
    hcent.trans (Subgroup.centralizer_le_normalizer (Subgroup.zpowers z' : Set M))
  have hcardB : Nat.card ↥(Subgroup.zpowers z' ⊔ Subgroup.zpowers a') = p ^ 2 := by
    have hcard := CFSG.LocalAnalysis.GLTheoremA.card_sup_mul_card_inf_of_le_normalizer
      (A := Subgroup.zpowers z') (B := Subgroup.zpowers a') hnorm
    rw [hinf, Subgroup.card_bot, hHcard, hKcard, mul_one, ← pow_two] at hcard
    exact hcard
  haveI : Finite ↥(Subgroup.zpowers z' ⊔ Subgroup.zpowers a') :=
    Nat.finite_of_card_ne_zero (by rw [hcardB]; exact pow_ne_zero 2 hp.ne_zero)
  have hsup_closure : Subgroup.zpowers z' ⊔ Subgroup.zpowers a' =
      Subgroup.closure ({z', a'} : Set M) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure, ← Subgroup.closure_union,
      Set.singleton_union]
  have hBcomm : IsMulCommutative ↥(Subgroup.zpowers z' ⊔ Subgroup.zpowers a') :=
    CFSG.GroupTheory.isMulCommutative_sup_of_elementwise_commute
      (fun h hh k hk => by
        obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
        obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hk
        exact (Commute.zpow_zpow (show Commute z' a' from hcomm) i j).eq)
      (inferInstance : IsMulCommutative ↥(Subgroup.zpowers z'))
      (inferInstance : IsMulCommutative ↥(Subgroup.zpowers a'))
  have hBexp : ∀ x ∈ Subgroup.zpowers z' ⊔ Subgroup.zpowers a', x ^ p = 1 := by
    intro x hx
    rw [hsup_closure] at hx
    have h := Subgroup.closure_induction
      (p := fun y _ => y ∈ (Subgroup.zpowers z' ⊔ Subgroup.zpowers a') ∧ y ^ p = 1)
      (k := ({z', a'} : Set M))
      (fun y hy => by
        rcases hy with rfl | rfl
        · exact ⟨Subgroup.mem_sup_left (Subgroup.mem_zpowers z'), hz'p⟩
        · exact ⟨Subgroup.mem_sup_right (Subgroup.mem_zpowers a'), ha'p⟩)
      ⟨(Subgroup.zpowers z' ⊔ Subgroup.zpowers a').one_mem, one_pow p⟩
      (fun y z _ _ hpy hpz => by
        refine ⟨(Subgroup.zpowers z' ⊔ Subgroup.zpowers a').mul_mem hpy.1 hpz.1, ?_⟩
        have hcyz : Commute y z :=
          (commute_iff_eq y z).2 (congrArg Subtype.val
            (hBcomm.is_comm.comm ⟨y, hpy.1⟩ ⟨z, hpz.1⟩))
        rw [hcyz.mul_pow, hpy.2, hpz.2, mul_one])
      (fun y _ hpy => by
        refine ⟨(Subgroup.zpowers z' ⊔ Subgroup.zpowers a').inv_mem hpy.1, ?_⟩
        rw [inv_pow, hpy.2, inv_one])
      hx
    exact h.2
  have hE : IsElemAbelian p (Subgroup.zpowers z' ⊔ Subgroup.zpowers a') :=
    ⟨hBcomm, hBexp⟩
  let F : Subgroup M :=
    { carrier := {b | φ b x = x}
      one_mem' := by simp
      mul_mem' := fun {b c} hb hc => by
        show φ (b * c) x = x
        rw [map_mul, MulAut.mul_apply, hc, hb]
      inv_mem' := fun {b} hb => by
        show φ b⁻¹ x = x
        rw [map_inv]
        have h := congrArg (fun y => (φ b)⁻¹ y) hb
        simpa using h.symm }
  have hz'F : z' ∈ F := by
    show φ z' x = x
    rw [hz'φ, MulAut.one_apply]
  have ha'F : a' ∈ F := hfix
  have hBF : Subgroup.zpowers z' ⊔ Subgroup.zpowers a' ≤ F :=
    sup_le (Subgroup.zpowers_le.2 hz'F) (Subgroup.zpowers_le.2 ha'F)
  refine ⟨Subgroup.zpowers z' ⊔ Subgroup.zpowers a', hE.isPGroup, ?_, fun b hb => hBF hb⟩
  haveI : CFSG.IsElementaryAbelian p ↥(Subgroup.zpowers z' ⊔ Subgroup.zpowers a') :=
    CFSG.Open.IsElemAbelian.isElementaryAbelian hE
  exact CFSG.IsElementaryAbelian.not_isCyclic_of_card_eq_prime_sq hcardB


theorem s168e3_false_of_kernel {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV) {p : ℕ} (hp : p.Prime) (hpσ : p ∈ D.sig)
    (hk : S168e3Kernel (Mbar D.M V₀ V hV) p) : False := by
  classical
  have hP : PairFacts D.M V₀ V := c.setting.hyp16.hyp125.pairFacts
  let φ : ↥D.M →* MulAut (Vtil V₀ V hV) := barHom V₀ V hV c.m_le_stabTil
  have hkerφ : φ.ker = (F11.CTilde D.M V₀ V).subgroupOf D.M :=
    ker_barHom V₀ V hV hP.le_normalizer c.m_le_stabTil
  have hrangeφ : φ.range = Mbar D.M V₀ V hV :=
    range_barHom V₀ V hV c.m_le_stabTil
  have hCM : F11.CTilde D.M V₀ V ≤ D.M := fun g hg =>
    ((mem_cTilde_iff hV hP.le_normalizer).1 hg).1
  have hsub : CFSG.Open.pRank p ((F11.CTilde D.M V₀ V).subgroupOf D.M) ≤
      CFSG.Open.pRank p (F11.CTilde D.M V₀ V) := by
    have h3 := CFSG.SectionRank.pRank_le_map hp.one_lt D.M.subtype D.M.subtype_injective
      ((F11.CTilde D.M V₀ V).subgroupOf D.M)
    rwa [Subgroup.map_subgroupOf_eq_of_le hCM] at h3
  have h115 : CFSG.Open.pRank p (F11.CTilde D.M V₀ V) ≤ 1 :=
    uc22p22q_pRank_ctilde_le_one D c.std.h61
      (Hyp125.hyp11 c.std.h127 c.setting.hyp16.hyp125)
      (c23_card_v0_le_four D c.setting.hyp16) hpσ
  have hker : CFSG.Open.pRank p φ.ker ≤ 1 := by
    rw [hkerφ]
    exact hsub.trans h115
  have hrange : CFSG.Open.pRank p φ.range ≤ 2 := by
    rw [hrangeφ]
    exact hk.1
  obtain ⟨E, hEM, hEel, hEcard⟩ :=
    c23_exists_elemAbelian_card_pow (p := p) (M := D.M) (k := 3) hp
      (by rw [UC6.groupPRank_eq_pRank]; exact c.std.hx.three_le p hpσ)
  let A : Subgroup ↥D.M := E.subgroupOf D.M
  have hA : IsElemAbelian p A := hEel.subgroupOf D.M
  have hAcard : Nat.card ↥A = p ^ 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEM).toEquiv, hEcard]
  obtain ⟨hzcard, hE2⟩ := s168e3_kernel_cap φ hp hker hrange hA hAcard
  haveI : Nontrivial ↥(A ⊓ φ.ker) := by
    rw [← Finite.one_lt_card_iff_nontrivial, hzcard]
    exact hp.one_lt
  obtain ⟨z, hz1⟩ := exists_ne (1 : ↥(A ⊓ φ.ker))
  have hzA : (z : ↥D.M) ∈ A := z.2.1
  have hzker : (z : ↥D.M) ∈ φ.ker := z.2.2
  have hzφ : φ (z : ↥D.M) = 1 := MonoidHom.mem_ker.mp hzker
  have hz1' : (z : ↥D.M) ≠ 1 := by
    intro h
    exact hz1 (Subtype.ext (by simpa using h))
  refine s168e3_false_of_fix_M c hp hpσ (fun x hx => ?_)
  have hle : A.map φ ≤ Mbar D.M V₀ V hV := by
    rw [← hrangeφ]
    exact Subgroup.map_le_range φ A
  obtain ⟨g₀, hg₀, b, hb, hb1, hfixb⟩ := hk.2 x hx (A.map φ) hle hE2
  obtain ⟨a, haA, rfl⟩ := Subgroup.mem_map.mp hb
  have hg₀' : g₀ ∈ φ.range := by
    rw [hrangeφ]
    exact hg₀
  obtain ⟨gg, hgg⟩ := MonoidHom.mem_range.mp hg₀'
  have ha1 : φ a ≠ 1 := hb1
  have hfix : φ (gg * a * gg⁻¹) x = x := by
    have h := hfixb
    rw [← hgg] at h
    simpa only [map_mul, map_inv] using h
  exact s168e3_noncyclic_fix_of_conj φ hp hA hzA hz1' hzφ haA ha1 gg hfix

theorem s168e3_false_of_tool {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV) {p : ℕ} (hp : p.Prime) (hpσ : p ∈ D.sig)
    (h : S168e3Tool (Mbar D.M V₀ V hV) p) : False := by
  rcases h with h | h
  · exact s168e3_false_of_fix c hp hpσ h
  · exact s168e3_false_of_kernel c hp hpσ h

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
