module

public import CFSG.Quasithin.Vol2.Ch5Sec2LocalProp526SndB
public import CFSG.Quasithin.H13.NQCatT3J2
public import CFSG.Quasithin.Recognition.CertTitsAmalgamLocal
public import CFSG.Quasithin.Recognition.CertTwoLocalPair
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListM12

public section

namespace CFSG.Quasithin.H13

open CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.QuasithinUnique.Vol2Native.A312L PermLat CFSG.Blueprint

namespace Sec526

theorem ne_top_of_pair {Y : Type*} [Group Y] {T M₁ M₂ : Subgroup Y}
    (hpair : IsYAmalgamPair T M₁ M₂) : M₁ ≠ ⊤ ∧ M₂ ≠ ⊤ := by
  have h1 := ((hpair.2.2 M₁).mpr (Or.inl rfl)).1
  have h2 := ((hpair.2.2 M₂).mpr (Or.inr rfl)).1
  refine ⟨fun h => hpair.2.1 (h2.2 M₁ h1.1 (by rw [h]; exact le_top)),
    fun h => hpair.2.1 (h1.2 M₂ h2.1 (by rw [h]; exact le_top)).symm⟩

theorem le_inf_of_pair {Y : Type*} [Group Y] {T M₁ M₂ : Subgroup Y}
    (hpair : IsYAmalgamPair T M₁ M₂) : T ≤ M₁ ∧ T ≤ M₂ :=
  ⟨Subgroup.le_normalizer.trans ((hpair.2.2 M₁).mpr (Or.inl rfl)).2,
    Subgroup.le_normalizer.trans ((hpair.2.2 M₂).mpr (Or.inr rfl)).2⟩

theorem not_five_dvd_member_m12 {Y : Type} [Group Y]
    (hY : Nonempty (Y ≃* CFSG.Open.quasithinM12)) {T M₁ M₂ : Subgroup Y}
    (hpair : IsYAmalgamPair T M₁ M₂) : ¬ 5 ∣ Nat.card M₁ ∧ ¬ 5 ∣ Nat.card M₂ := by
  obtain ⟨e⟩ := hY
  have hck := M12Lat.cert_check
  have hU := M12Lat.cert.isSylowTwoOf_top (rawIsEnc 12) hck (k := 6) (m := 1485) (by decide)
    (by decide) (by omega)
  have hM : Nat.card (Subgroup.closure {g | g ∈ M12Lat.cert.mGens}) = 95040 :=
    M12Lat.cert.card_m (rawIsEnc 12) (LatCert.closedOK_of_check hck)
      (LatCert.sizesOK_of_check hck)
  let φ : Y ≃* ↥(Subgroup.closure {g | g ∈ M12Lat.cert.mGens}) :=
    e.trans (MulEquiv.subgroupCongr M12Lat.mGens_closure).symm
  have hpair' := IsYAmalgamPair.map φ hpair
  obtain ⟨ρ, hρ⟩ := exists_mulEquiv_map_sylow hU hpair'.1
  let f : Y ≃* ↥(Subgroup.closure {g | g ∈ M12Lat.cert.mGens}) := φ.trans ρ
  have hmap : ∀ M : Subgroup Y,
      (M.map φ.toMonoidHom).map ρ.toMonoidHom = M.map f.toMonoidHom := fun M =>
    Subgroup.map_map _ _ _
  have hpairf := IsYAmalgamPair.map ρ hpair'
  rw [hρ, hmap, hmap] at hpairf
  have hle := le_inf_of_pair hpairf
  have hne := ne_top_of_pair hpairf
  have key : ∀ M : Subgroup ↥(Subgroup.closure {g | g ∈ M12Lat.cert.mGens}),
      (Subgroup.closure {g | g ∈ M12Lat.cert.tGens}).subgroupOf
        (Subgroup.closure {g | g ∈ M12Lat.cert.mGens}) ≤ M → M ≠ ⊤ →
      ¬ 5 ∣ Nat.card M := by
    intro M hUM hMt
    obtain ⟨L, -, hLM, hML, hcardL⟩ := M12Lat.cert.overgroup_cases (rawIsEnc 12) hck M hUM
    have hsz : Nat.card (Subgroup.closure {g | g ∈ L}) ∈ [64, 95040, 192, 192] := hcardL
    have hMc : Nat.card M = Nat.card (Subgroup.closure {g | g ∈ L}) := by
      rw [hML]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLM).toEquiv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hsz
    rcases hsz with h | h | h | h
    · rw [hMc, h]
      norm_num
    · exfalso
      apply hMt
      have heq : Subgroup.closure {g | g ∈ L} = Subgroup.closure {g | g ∈ M12Lat.cert.mGens} :=
        Subgroup.eq_of_le_of_card_ge hLM (by rw [h, hM])
      rw [hML, heq, Subgroup.subgroupOf_self]
    · rw [hMc, h]
      norm_num
    · rw [hMc, h]
      norm_num
  refine ⟨fun h5 => key _ hle.1 hne.1 ?_, fun h5 => key _ hle.2 hne.2 ?_⟩
  · rwa [Subgroup.card_map_of_injective f.injective]
  · rwa [Subgroup.card_map_of_injective f.injective]

theorem eq_of_five_dvd_overgroup_lattice {Γ P : Type} [Group Γ] [Finite Γ] [Group P] [Finite P]
    (ψ : P ≃* Γ) {S₀ : Subgroup Γ} (hS₀ : IsSylowTwoOf S₀ ⊤) {Yl : ℕ → Subgroup Γ}
    (hover : ∀ Z : Subgroup Γ, S₀ ≤ Z →
      Z = ⊤ ∨ ∃ j < 5, Z = Yl j ∧ Nat.card ↥Z = #[1, 3, 9, 15, 3][j]! * 2 ^ 7)
    {T₀ Z₁ Z₂ : Subgroup P} (hT : IsSylowTwoOf T₀ ⊤) (h1 : T₀ ≤ Z₁) (h2 : T₀ ≤ Z₂)
    (hZ1 : Z₁ ≠ ⊤) (hZ2 : Z₂ ≠ ⊤) (h51 : 5 ∣ Nat.card Z₁) (h52 : 5 ∣ Nat.card Z₂) : Z₁ = Z₂ := by
  obtain ⟨ρ, hρ⟩ := exists_mulEquiv_map_sylow hS₀ (isSylowTwoOf_top_map ψ hT)
  let f : P ≃* Γ := ψ.trans ρ
  have hS : T₀.map f.toMonoidHom = S₀ := by
    rw [← hρ, Subgroup.map_map]
    rfl
  have key : ∀ Z : Subgroup P, T₀ ≤ Z → Z ≠ ⊤ → 5 ∣ Nat.card Z →
      Z.map f.toMonoidHom = Yl 3 := by
    intro Z hTZ hZ h5
    have hSZ : S₀ ≤ Z.map f.toMonoidHom := hS ▸ Subgroup.map_mono hTZ
    rcases hover _ hSZ with htop | ⟨j, hj, hZj, hcj⟩
    · exact absurd (Subgroup.map_injective f.injective
        (htop.trans (Subgroup.map_top_of_surjective _ f.surjective).symm)) hZ
    · have h5' : 5 ∣ Nat.card ↥(Z.map f.toMonoidHom) := by
        rwa [Subgroup.card_map_of_injective f.injective]
      rw [hcj] at h5'
      have hj3 : j = 3 := by
        revert h5'
        interval_cases j <;> decide
      subst hj3
      exact hZj
  exact Subgroup.map_injective f.injective ((key Z₁ h1 hZ1 h51).trans (key Z₂ h2 hZ2 h52).symm)

theorem false_of_five_dvd_members_of_index_two
    {Y : Type} [Group Y] [Finite Y]
    (hYc : Nat.card Y = 1209600) {J₀ : Subgroup Y} (hJi : J₀.index = 2)
    (ψ : ↥J₀ ≃* ↥CFSG.Sporadic.J2.J) {T M₁ M₂ : Subgroup Y} (hpair : IsYAmalgamPair T M₁ M₂)
    (h51 : 5 ∣ Nat.card M₁) (h52 : 5 ∣ Nat.card M₂) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hJc : Nat.card J₀ = 604800 := by
    have h := J₀.card_mul_index
    rw [hJi, hYc] at h
    omega
  have hJn : J₀.Normal := Subgroup.normal_of_index_eq_two hJi
  obtain ⟨-, hT2, hTi⟩ := hpair.1
  have hTi' : ¬ 2 ∣ T.index := by
    have e1 : (T.subgroupOf ⊤).index = T.index := Subgroup.relIndex_top_right T
    rwa [e1] at hTi
  have hTc : Nat.card T = 2 ^ 8 := by
    rw [card_eq_two_pow_of_odd_index hT2 hTi', hYc,
      factorization_two_of_eq (k := 8) (m := 4725) (by norm_num) (by norm_num)]
  obtain ⟨t, htT, htJ⟩ : ∃ t ∈ T, t ∉ J₀ := by
    by_contra h
    push Not at h
    have hd := Subgroup.card_dvd_of_le (show T ≤ J₀ from h)
    rw [hTc, hJc] at hd
    norm_num at hd
  have hTJ : Nat.card ↥(T ⊓ J₀) = 2 ^ 7 := by
    have hr := Subgroup.relIndex_mul_card (H := J₀) (K := T)
    have hrd : J₀.relIndex T ∣ 2 := hJi ▸ Subgroup.relIndex_dvd_index_of_normal J₀ T
    have hinf : J₀ ⊓ T = T ⊓ J₀ := inf_comm _ _
    rw [hinf, hTc] at hr
    have hd2 : Nat.card ↥(T ⊓ J₀) ∣ 2 ^ 8 := ⟨_, by rw [mul_comm] at hr; exact hr.symm⟩
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd2
    have hdJ : Nat.card ↥(T ⊓ J₀) ∣ 604800 := hJc ▸ Subgroup.card_dvd_of_le inf_le_right
    rw [hk'] at hdJ hr
    have hk8 : k ≠ 8 := by
      rintro rfl
      norm_num at hdJ
    rcases (Nat.dvd_prime Nat.prime_two).mp hrd with h1 | h1
    · rw [h1, one_mul] at hr
      exact absurd (Nat.pow_right_injective le_rfl hr) hk8
    · rw [h1] at hr
      rw [hk']
      have : 2 ^ k = 2 ^ 7 := by omega
      exact this
  set T₀ := T.subgroupOf J₀ with hT₀
  have hT₀c : Nat.card T₀ = 2 ^ 7 := by
    rw [hT₀, ← Subgroup.inf_subgroupOf_right,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : T ⊓ J₀ ≤ J₀)).toEquiv]
    exact hTJ
  have hT₀s : IsSylowTwoOf T₀ ⊤ := by
    refine ⟨le_top, IsPGroup.of_card hT₀c, ?_⟩
    have e1 : (T₀.subgroupOf ⊤).index = T₀.index := Subgroup.relIndex_top_right T₀
    rw [e1]
    have h := T₀.card_mul_index
    rw [hT₀c, hJc] at h
    have h2 : T₀.index = 4725 := by omega
    rw [h2]
    norm_num
  have hle := le_inf_of_pair hpair
  have hne := ne_top_of_pair hpair
  have hZ : ∀ M : Subgroup Y, T ≤ M → M ≠ ⊤ → 5 ∣ Nat.card M →
      T₀ ≤ M.subgroupOf J₀ ∧ M.subgroupOf J₀ ≠ ⊤ ∧ 5 ∣ Nat.card (M.subgroupOf J₀) := by
    intro M hTM hMt h5
    refine ⟨fun x hx => Subgroup.mem_subgroupOf.mpr (hTM (Subgroup.mem_subgroupOf.mp hx)), ?_, ?_⟩
    · intro htop
      apply hMt
      have hJM : J₀ ≤ M := Subgroup.subgroupOf_eq_top.mp htop
      rw [eq_top_iff]
      intro y _
      by_cases hy : y ∈ J₀
      · exact hJM hy
      · have hty : t⁻¹ * y ∈ J₀ := by
          rw [Subgroup.mul_mem_iff_of_index_two hJi]
          exact ⟨fun h => absurd (J₀.inv_mem_iff.mp h) htJ, fun h => absurd h hy⟩
        have := M.mul_mem (hTM htT) (hJM hty)
        simpa using this
    · have hr := Subgroup.relIndex_mul_card (H := J₀) (K := M)
      have hrd : J₀.relIndex M ∣ 2 := hJi ▸ Subgroup.relIndex_dvd_index_of_normal J₀ M
      rw [← hr] at h5
      have hcop : Nat.Coprime 5 (J₀.relIndex M) := by
        rcases (Nat.dvd_prime Nat.prime_two).mp hrd with h1 | h1 <;> rw [h1] <;> norm_num
      have h5' := hcop.dvd_of_dvd_mul_left h5
      rw [inf_comm] at h5'
      rw [← Subgroup.inf_subgroupOf_right,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : M ⊓ J₀ ≤ J₀)).toEquiv]
      exact h5'
  obtain ⟨h1a, h1b, h1c⟩ := hZ M₁ hle.1 hne.1 h51
  obtain ⟨h2a, h2b, h2c⟩ := hZ M₂ hle.2 hne.2 h52
  have : Finite ↥J₀ := inferInstance
  have hEq := @eq_of_five_dvd_overgroup_lattice ↥CFSG.Sporadic.J2.J ↥J₀ (Subgroup.toGroup _) _ _ _
    ψ E2P.SporB.j2Ctx.S S146zY.j2_S_sylow E2P.SporB.j2Ctx.Y
    (fun Z hZ => NQCat.T3.j2_overgroup hZ) _ _ _ hT₀s h1a h2a h1b h2b h1c h2c
  have hiff : ∀ y ∈ J₀, y ∈ M₁ ↔ y ∈ M₂ := fun y hy => by
    have := congrArg (fun Z : Subgroup ↥J₀ => (⟨y, hy⟩ : ↥J₀) ∈ Z) hEq
    simpa [Subgroup.mem_subgroupOf] using this
  have hsub : ∀ {A B : Subgroup Y}, T ≤ A → T ≤ B → (∀ y ∈ J₀, y ∈ A ↔ y ∈ B) → A ≤ B := by
    intro A B hTA hTB hAB y hy
    by_cases hyJ : y ∈ J₀
    · exact (hAB y hyJ).mp hy
    · have hty : t⁻¹ * y ∈ J₀ := by
        rw [Subgroup.mul_mem_iff_of_index_two hJi]
        exact ⟨fun h => absurd (J₀.inv_mem_iff.mp h) htJ, fun h => absurd h hyJ⟩
      have h1 : t⁻¹ * y ∈ B := (hAB _ hty).mp (A.mul_mem (A.inv_mem (hTA htT)) hy)
      have := B.mul_mem (hTB htT) h1
      simpa using this
  exact hpair.2.1 (le_antisymm (hsub hle.1 hle.2 hiff)
    (hsub hle.2 hle.1 fun y hy => (hiff y hy).symm))

theorem false_of_five_dvd_members_autj2
    {Y : Type} [Group Y] (hY : Nonempty (Y ≃* MulAut CFSG.Open.quasithinJ2))
    {T M₁ M₂ : Subgroup Y} (hpair : IsYAmalgamPair T M₁ M₂) (h51 : 5 ∣ Nat.card M₁)
    (h52 : 5 ∣ Nat.card M₂) : False := by
  obtain ⟨e₀⟩ := hY
  let e : Y ≃* ↥CFSG.ComponentClassification.J2Cover.R :=
    e₀.trans ((mulAutCongrOfMulEquiv (quasithinJ2MulEquivNative.trans
      CFSG.ComponentClassification.J2Cover.nativeEquivP)).trans
        CFSG.ComponentClassification.J2Cover.rAutEquiv.symm)
  have hYc : Nat.card Y = 1209600 := by
    rw [Nat.card_congr e.toEquiv, CFSG.ComponentClassification.J2Cover.card_R]
  have : Finite Y := Nat.finite_of_card_ne_zero (by rw [hYc]; norm_num)
  set J₀ : Subgroup Y := (CFSG.ComponentClassification.J2Cover.P.subgroupOf
    CFSG.ComponentClassification.J2Cover.R).map e.symm.toMonoidHom with hJ₀
  let ψ : ↥J₀ ≃* ↥CFSG.Sporadic.J2.J :=
    ((CFSG.ComponentClassification.J2Cover.P.subgroupOf
      CFSG.ComponentClassification.J2Cover.R).equivMapOfInjective e.symm.toMonoidHom
        e.symm.injective).symm.trans
      ((Subgroup.subgroupOfEquivOfLe CFSG.ComponentClassification.J2Cover.P_le_R).trans
        CFSG.ComponentClassification.J2Cover.jEquivP.symm)
  have hJc : Nat.card J₀ = 604800 := by
    rw [Nat.card_congr ψ.toEquiv, CFSG.Sporadic.J2.card_J]
  have hJi : J₀.index = 2 := by
    have h := J₀.card_mul_index
    rw [hJc, hYc] at h
    omega
  exact false_of_five_dvd_members_of_index_two hYc hJi ψ hpair h51 h52

end Sec526

end CFSG.Quasithin.H13
