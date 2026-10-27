module

public import CFSG.Quasithin.Vol2.Ch12Sec2Lem22K
public import CFSG.Quasithin.Vol2.KGFactMinParL42
public import CFSG.Quasithin.Vol2.KGFactMinParL52
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B113OverCertL32
public import CFSG.LocalAnalysis.SectionRank.Ccomm.ElementaryAut
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyLinearBinary
public import CFSG.GH74.Exceptional.LinearFourTwo
public import CFSG.Dihedral.FourgroupCycleControl
public import CFSG.Dihedral.OriginalCentralizerOddCore
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.AschbacherCanonicalRemaining
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.ExceptionalEightPlaneCentralizer
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppCCases
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.A3A3Perm
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Basic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.L2_4_27
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Statements
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InA3Conj
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellMotion
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryRootAutomorphism
public import CFSG.Open.SplitBNPair
public import CFSG.Permutation.BurnsideSchur
public import CFSG.Quasithin.Background.B1More13A
public import CFSG.Quasithin.Background.B1More13Defs
public import CFSG.Quasithin.Background.B1MoreEleven
public import CFSG.Quasithin.Background.B5Basic
public import CFSG.Quasithin.Background.B5CompA
public import CFSG.Quasithin.Background.B5CompB
public import CFSG.Quasithin.Background.B5FinOut
public import CFSG.Quasithin.Background.B6
public import CFSG.Quasithin.Background.B6Example
public import CFSG.Quasithin.Background.E3
public import CFSG.Quasithin.Background.E3Nprime
public import CFSG.Quasithin.Background.E3OffenderB
public import CFSG.Quasithin.Background.E3Uniq
public import CFSG.Quasithin.Background.E4Solv
public import CFSG.Quasithin.Background.FFC4Real
public import CFSG.Quasithin.Background.InternalSecData
public import CFSG.Quasithin.Vol2.Ch10StatementsE
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS2
public import CFSG.Quasithin.Vol2.Ch11SecA02Setup
public import CFSG.Quasithin.Vol2.Ch11SecA11Arith
public import CFSG.Quasithin.Vol2.Ch11StatementsC
public import CFSG.Quasithin.Vol2.Ch12Sec2Lem20
public import CFSG.Sporadic.Schreier.J4SProfileNode
public import CFSG.Timmesfeld.Moufang.Three
public import CFSG.Timmesfeld.RankOne
public import CFSG.Timmesfeld.Special.TwoCore

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

namespace Lem22

variable {A : Type} [Group A] [Finite A]

@[expose] def mulSub (X S : Subgroup A)
    (hSX : ∀ s ∈ S, ∀ x ∈ X, ∃ x' ∈ X, ∃ s' ∈ S, s * x = x' * s') : Subgroup A where
  carrier := {g | ∃ x ∈ X, ∃ s ∈ S, g = x * s}
  one_mem' := ⟨1, X.one_mem, 1, S.one_mem, by simp⟩
  mul_mem' := by
    rintro _ _ ⟨x₁, hx₁, s₁, hs₁, rfl⟩ ⟨x₂, hx₂, s₂, hs₂, rfl⟩
    obtain ⟨x', hx', s', hs', he⟩ := hSX s₁ hs₁ x₂ hx₂
    refine ⟨x₁ * x', X.mul_mem hx₁ hx', s' * s₂, S.mul_mem hs' hs₂, ?_⟩
    calc x₁ * s₁ * (x₂ * s₂) = x₁ * (s₁ * x₂) * s₂ := by group
      _ = x₁ * (x' * s') * s₂ := by rw [he]
      _ = x₁ * x' * (s' * s₂) := by group
  inv_mem' := by
    rintro _ ⟨x, hx, s, hs, rfl⟩
    obtain ⟨x', hx', s', hs', he⟩ := hSX s⁻¹ (S.inv_mem hs) x⁻¹ (X.inv_mem hx)
    exact ⟨x', hx', s', hs', by rw [mul_inv_rev, he]⟩

omit [Finite A] in
theorem card_mulSub {X S : Subgroup A}
    (hSX : ∀ s ∈ S, ∀ x ∈ X, ∃ x' ∈ X, ∃ s' ∈ S, s * x = x' * s')
    (hXS : ∀ y ∈ X, y ∈ S → y = 1) : Nat.card (mulSub X S hSX) = Nat.card X * Nat.card S := by
  rw [← Nat.card_prod]
  symm
  refine Nat.card_congr (Equiv.ofBijective (fun xs : ↥X × ↥S =>
    (⟨(xs.1 : A) * xs.2, xs.1, xs.1.2, xs.2, xs.2.2, rfl⟩ : ↥(mulSub X S hSX))) ⟨?_, ?_⟩)
  · rintro ⟨x₁, s₁⟩ ⟨x₂, s₂⟩ h
    have h' : (x₁ : A) * s₁ = x₂ * s₂ := congrArg Subtype.val h
    have h1 : (x₂ : A)⁻¹ * x₁ = s₂ * (s₁ : A)⁻¹ := by
      calc (x₂ : A)⁻¹ * x₁ = (x₂ : A)⁻¹ * ((x₁ : A) * s₁) * (s₁ : A)⁻¹ := by group
        _ = (x₂ : A)⁻¹ * ((x₂ : A) * s₂) * (s₁ : A)⁻¹ := by rw [h']
        _ = s₂ * (s₁ : A)⁻¹ := by group
    have h2 := hXS _ (X.mul_mem (X.inv_mem x₂.2) x₁.2) (h1 ▸ S.mul_mem s₂.2 (S.inv_mem s₁.2))
    have hx : x₁ = x₂ := Subtype.ext (by
      have := h2
      rw [inv_mul_eq_one] at this
      exact this.symm)
    have hs : s₁ = s₂ := Subtype.ext (by
      rw [hx] at h'
      exact mul_left_cancel h')
    rw [hx, hs]
  · rintro ⟨_, x, hx, s, hs, rfl⟩
    exact ⟨(⟨x, hx⟩, ⟨s, hs⟩), rfl⟩

theorem prime_eq_three_of_model {Γ : Type} [Group Γ] [Finite Γ] (e : A ≃* Γ)
    {S₀ : Subgroup Γ} (hS₀ : IsSylowTwoOf S₀ ⊤)
    (hlat : ∀ Z : Subgroup Γ, S₀ ≤ Z → Z ≠ S₀ → 3 ∣ Nat.card Z)
    {S X : Subgroup A} {p : ℕ} (hS : IsSylowTwoOf S ⊤) (hp : p.Prime) (hp2 : p ≠ 2)
    (hXp : IsPGroup p ↥X) (hX1 : X ≠ ⊥)
    (hSX : ∀ s ∈ S, ∀ x ∈ X, ∃ x' ∈ X, ∃ s' ∈ S, s * x = x' * s') : p = 3 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact p.Prime := ⟨hp⟩
  have hXS : ∀ y ∈ X, y ∈ S → y = 1 := fun y hyX hyS =>
    eq_one_of_mem_of_mem hp hp2 hXp hS.2.1 hyX hyS
  set Y := mulSub X S hSX with hY
  have hcard := card_mulSub hSX hXS
  have hSY : S ≤ Y := fun s hs => ⟨1, X.one_mem, s, hs, by rw [one_mul]⟩
  have hS' : IsSylowTwoOf (S.map e.toMonoidHom) ⊤ := by
    have h1 := Lem22.isSylowTwoOf_map_hom hS e.toMonoidHom
    rwa [Subgroup.map_top_of_surjective _ e.surjective] at h1
  obtain ⟨g, -, hg⟩ := A4.exists_conj_of_isSylowTwoOf hS₀ hS'
  set Z := (Y.map e.toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom with hZ
  have hS₀Z : S₀ ≤ Z := by
    intro s₀ hs₀
    have h1 : g * s₀ * g⁻¹ ∈ S.map e.toMonoidHom := by
      rw [hg]
      simpa [mul_assoc] using hs₀
    refine ⟨g * s₀ * g⁻¹, Subgroup.map_mono hSY h1, ?_⟩
    simp [mul_assoc]
  have hZcard : Nat.card Z = Nat.card X * Nat.card S := by
    rw [hZ, Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective,
      Subgroup.card_map_of_injective e.injective, hcard]
  have hS₀card : Nat.card S₀ = Nat.card S := by
    have h1 := Subgroup.card_mul_index S₀
    have h2 := Subgroup.card_mul_index S
    obtain ⟨a, ha⟩ := hS₀.2.1.exists_card_eq
    obtain ⟨b, hb⟩ := hS.2.1.exists_card_eq
    have hcΓ : Nat.card Γ = Nat.card A := Nat.card_congr e.toEquiv.symm
    have hi₀ : ¬ 2 ∣ S₀.index := by
      have := hS₀.2.2
      rwa [show (S₀.subgroupOf ⊤).index = S₀.index from Subgroup.relIndex_top_right S₀] at this
    have hi : ¬ 2 ∣ S.index := by
      have := hS.2.2
      rwa [show (S.subgroupOf ⊤).index = S.index from Subgroup.relIndex_top_right S] at this
    rw [ha] at h1 ⊢
    rw [hb] at h2 ⊢
    rw [hcΓ] at h1
    have hcop₀ : Nat.Coprime (2 ^ a) S₀.index :=
      Nat.Coprime.pow_left a ((Nat.coprime_two_left).mpr (Nat.odd_iff.mpr (by omega)))
    have hcop : Nat.Coprime (2 ^ b) S.index :=
      Nat.Coprime.pow_left b ((Nat.coprime_two_left).mpr (Nat.odd_iff.mpr (by omega)))
    have hdvd₁ : 2 ^ a ∣ 2 ^ b := by
      have : 2 ^ a ∣ 2 ^ b * S.index := ⟨S₀.index, by rw [h2, ← h1]⟩
      exact (Nat.Coprime.pow_left a ((Nat.coprime_two_left).mpr
        (Nat.odd_iff.mpr (by omega)))).dvd_of_dvd_mul_right this
    have hdvd₂ : 2 ^ b ∣ 2 ^ a := by
      have : 2 ^ b ∣ 2 ^ a * S₀.index := ⟨S.index, by rw [h1, ← h2]⟩
      exact (Nat.Coprime.pow_left b ((Nat.coprime_two_left).mpr
        (Nat.odd_iff.mpr (by omega)))).dvd_of_dvd_mul_right this
    exact Nat.dvd_antisymm hdvd₁ hdvd₂
  have hX1' : 1 < Nat.card X := by
    obtain ⟨⟨x, hx⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hX1
    exact Finite.one_lt_card_iff_nontrivial.mpr ⟨⟨⟨x, hx⟩, 1, hx1⟩⟩
  have hZne : Z ≠ S₀ := by
    intro h0
    have h1 := hZcard
    rw [h0, hS₀card] at h1
    have hpos : 0 < Nat.card S := Nat.card_pos
    nlinarith
  have h3 := hlat Z hS₀Z hZne
  rw [hZcard] at h3
  obtain ⟨b, hb⟩ := hS.2.1.exists_card_eq
  rw [hb] at h3
  have h3X : 3 ∣ Nat.card X :=
    (Nat.Coprime.pow_right b (by norm_num : Nat.Coprime 3 2)).dvd_of_dvd_mul_right h3
  obtain ⟨k, hk⟩ := hXp.exists_card_eq
  rw [hk] at h3X
  exact ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp
    (Nat.prime_three.dvd_of_dvd_pow h3X)).symm

end Lem22

namespace KGBorelThree

open Equiv CFSG.QuasithinUnique.Vol2Native.A312L.PermLat CFSG.QuasithinUnique.Bridge.Over
  CFSG.QuasithinUnique.Ch1.SporLat CFSG.Quasithin.H13.KGMinPar

theorem z8_three_dvd :
    ∀ Z : Subgroup ↥(Vol2Native.A312L.Seven.Z 8),
      CertL32.D.subgroupOf (Vol2Native.A312L.Seven.Z 8) ≤ Z →
      Z ≠ CertL32.D.subgroupOf (Vol2Native.A312L.Seven.Z 8) → 3 ∣ Nat.card Z := by
  intro Z hZ hne
  let Z' : Subgroup (Perm (Fin 7)) := Z.map (Vol2Native.A312L.Seven.Z 8).subtype
  have hDZ : Subgroup.closure {g | g ∈ CertL32.cert.tGens} ≤ Z' := fun t ht => by
    have htD : t ∈ CertL32.D := ht
    have htM : t ∈ Vol2Native.A312L.Seven.Z 8 := CertL32.D_le htD
    have h1 : (⟨t, htM⟩ : ↥(Vol2Native.A312L.Seven.Z 8)) ∈ Z :=
      hZ (Subgroup.mem_subgroupOf.mpr htD)
    exact ⟨⟨t, htM⟩, h1, rfl⟩
  have hZM : Z' ≤ Subgroup.closure {g | g ∈ CertL32.cert.mGens} := by
    show Z' ≤ Subgroup.closure {g | g ∈ CertL32.mGens}
    rw [CertL32.closure_mGens]
    rintro _ ⟨z, -, rfl⟩
    exact z.2
  obtain ⟨Lg, hL, hZL⟩ := CertL32.cert.overgroups (rawIsEnc 7) CertL32.cert_check Z' hDZ hZM
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hL
  have hcardZ : Nat.card Z = Nat.card Z' :=
    (Subgroup.card_map_of_injective (Vol2Native.A312L.Seven.Z 8).subtype_injective).symm
  have hcard := CertL32.cert.card_member_idx (rawIsEnc 7)
    (CertL32.cert.closedOK_of_check CertL32.cert_check)
    (CertL32.cert.sizesOK_of_check CertL32.cert_check) j hj
  rw [← hZL, ← hcardZ] at hcard
  have hj4 : j < 4 := hj
  rw [hcard]
  interval_cases j
  · exfalso
    apply hne
    have hZZ : Z'.subgroupOf (Vol2Native.A312L.Seven.Z 8) = Z :=
      Subgroup.comap_map_eq_self_of_injective (Vol2Native.A312L.Seven.Z 8).subtype_injective Z
    rw [← hZZ, hZL]
    rfl
  all_goals decide

theorem a8_three_dvd :
    ∀ Z : Subgroup ↥(alternatingGroup (Fin 8)),
      CFSG.QuasithinUnique.L246C127.Even8.D.subgroupOf (alternatingGroup (Fin 8)) ≤ Z →
      Z ≠ CFSG.QuasithinUnique.L246C127.Even8.D.subgroupOf (alternatingGroup (Fin 8)) →
      3 ∣ Nat.card Z := by
  intro Z hZ hne
  obtain ⟨j, hj, rfl⟩ := a8_complete Z hZ
  rcases Nat.lt_or_ge j 8 with h | h
  · simp only [memberOrTop, h, ite_true] at hne ⊢
    rw [card_a8Y h]
    interval_cases j
    · exact absurd rfl hne
    all_goals decide
  · have hj8 : j = 8 := by omega
    subst hj8
    simp only [memberOrTop, lt_irrefl, ite_false]
    rw [Subgroup.card_top, CFSG.QuasithinUnique.L246C127.Even8.card_alt]
    decide

theorem l52_three_dvd :
    ∀ Z : Subgroup CFSG.Literature.GL52.G, l52S ≤ Z → Z ≠ l52S → 3 ∣ Nat.card Z := by
  intro Z hZ hne
  obtain ⟨j, hj, rfl⟩ := l52_complete Z hZ
  rcases Nat.lt_or_ge j 15 with h | h
  · simp only [memberOrTop, h, ite_true] at hne ⊢
    rw [l52_member_card j h]
    interval_cases j
    · exact absurd l52_Y_zero hne
    all_goals decide
  · have hj15 : j = 15 := by omega
    subst hj15
    simp only [memberOrTop, lt_irrefl, ite_false]
    rw [Subgroup.card_top, CFSG.Literature.GL52.card_GL52]
    decide

end KGBorelThree

open KGBorelThree in
theorem kgBorelOvergroupThree :
    KGBorelOvergroupThree := by
  intro V _ _ n hn hcard hcomm hsq S X p hS hp hp2 hXp hX1 hSX
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpow : ∀ a : V, a ^ 2 = 1 := hsq
  obtain ⟨e₀⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (p := 2) hcomm hpow hcard
  have eGL := CFSG.SectionRank.Ccomm.elemAutEquivGL e₀
  have : Finite (MulAut V) := Finite.of_equiv _ eGL.symm.toEquiv
  rcases hn with rfl | rfl | rfl
  ·
    let e : MulAut V ≃* ↥(Vol2Native.A312L.Seven.Z 8) :=
      eGL.trans ((CFSG.QuasithinUnique.Setup.Family.slEquivGL 3).symm.trans
        Vol2Native.A312L.Seven.z8Equiv)
    exact Lem22.prime_eq_three_of_model e Bridge.Over.CertL32.isSylow_D z8_three_dvd hS hp hp2
      hXp hX1 hSX
  ·
    let e : MulAut V ≃* ↥(alternatingGroup (Fin 8)) :=
      eGL.trans CFSG.GH74.Exceptional.alternatingEightEquivGLFourTwo.symm
    exact Lem22.prime_eq_three_of_model e KGMinPar.a8_sylow a8_three_dvd hS hp hp2 hXp hX1 hSX
  ·
    exact Lem22.prime_eq_three_of_model eGL KGMinPar.l52_S_sylow l52_three_dvd hS hp hp2 hXp
      hX1 hSX

end CFSG.Quasithin.H13
