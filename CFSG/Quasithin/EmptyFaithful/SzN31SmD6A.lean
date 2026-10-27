module

public import CFSG.Quasithin.EmptyFaithful.SzN31SmallStmt
public import CFSG.Quasithin.EmptyFaithful.SzN31Cover
public import CFSG.Quasithin.EmptyFaithful.SzN31CntM3p
import CFSG.GroupTheory.PCore.OpenTransport

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.SzN31

open CFSG.Quasithin.G11 CFSG.Open CFSG.Quasithin.G8

namespace SmD6

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem card_le_27_of_isPGroup (hT : SylowGL6NoCover) (hd : Module.finrank (ZMod 2) V = 6)
    {Γ : Subgroup (GLV V)} (hq : IsQuotientOfSQTKTauCeti ↥Γ) {S : Subgroup (GLV V)} (hSΓ : S ≤ Γ)
    (hS : IsPGroup 3 S) : Nat.card S ≤ 27 := by
  by_contra hlt
  push Not at hlt
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := hS.exists_card_eq
  have hk4 : 4 ≤ k := by
    by_contra h
    have : k ≤ 3 := by omega
    have : 3 ^ k ≤ 3 ^ 3 := Nat.pow_le_pow_right (by norm_num) this
    omega
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥S) 3
    (n := 4) (by rw [hk]; exact pow_dvd_pow 3 hk4)
  set S' : Subgroup (GLV V) := K.map S.subtype with hS'
  have hS'card : Nat.card S' = 81 := by
    rw [hS', Subgroup.card_map_of_injective S.subtype_injective, hK]
    norm_num
  have hS'S : S' ≤ S := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hS'Γ : S' ≤ Γ := hS'S.trans hSΓ
  have hS'p : IsPGroup 3 S' := hS.to_le hS'S
  set P'' : Subgroup ↥Γ := S'.subgroupOf Γ with hP''
  have hP''card : Nat.card P'' = 3 ^ 4 := by
    rw [hP'']
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS'Γ).toEquiv, hS'card]
    norm_num
  have hP''p : IsPGroup 3 P'' := IsPGroup.of_card hP''card
  obtain ⟨Phat, Bhat, _, _, _, _, act, π, β, hPp, hrank, -, hπ, -, -⟩ :=
    sqtk_cover_equivariant hq Nat.prime_three (by norm_num) P'' ⊥ hP''p
      (fun b hb => by
        rw [Subgroup.mem_bot] at hb
        subst hb
        exact ⟨by simp, fun c hc => by rw [Subgroup.mem_bot] at hc; subst hc; simp⟩)
      (fun b hb x _ => by
        rw [Subgroup.mem_bot] at hb
        subst hb
        simpa using ‹x ∈ P''›)
  let f : Phat →* GLV V := Γ.subtype.comp π
  have hf : ∀ x, f x ∈ S' := fun x => by
    have : π x ∈ P'' := hπ ▸ MonoidHom.mem_range.2 ⟨x, rfl⟩
    exact this
  let π' : Phat →* ↥S' := f.codRestrict S' hf
  have hsurj : Function.Surjective π' := by
    intro s
    have hs : (⟨s.1, hS'Γ s.2⟩ : ↥Γ) ∈ P'' := s.2
    rw [← hπ] at hs
    obtain ⟨x, hx⟩ := MonoidHom.mem_range.1 hs
    refine ⟨x, Subtype.ext ?_⟩
    show (π x : GLV V) = s.1
    rw [hx]
  exact hT V hd S' hS'p hS'card Phat hPp hrank π' hsurj

theorem three_dvd_of_seven_dvd_two_pow_sub_one {n : ℕ} (h : 7 ∣ 2 ^ n - 1) : 3 ∣ n := by
  have hpos : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have h1 : 2 ^ n % 7 = 1 := by omega
  obtain ⟨k, r, hr, rfl⟩ : ∃ k r, r < 3 ∧ n = 3 * k + r :=
    ⟨n / 3, n % 3, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod n 3).symm⟩
  have h2 : 2 ^ (3 * k + r) % 7 = 2 ^ r % 7 := by
    rw [pow_add, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  interval_cases r <;> omega

variable {Γ A : Subgroup (GLV V)}

omit [Finite V] in
theorem pCoreOf_le (p : ℕ) (Γ : Subgroup (GLV V)) : pCoreOf p Γ ≤ Γ := CFSG.openPCoreOf_le p Γ

omit [Finite V] in
theorem commute_of_pCoreOf_ne {p r : ℕ} [Fact p.Prime] [Fact r.Prime] (hpr : p ≠ r)
    {x y : GLV V} (hx : x ∈ pCoreOf p Γ) (hy : y ∈ pCoreOf r Γ) : x * y = y * x := by
  have hxΓ : x ∈ Γ := pCoreOf_le p Γ hx
  have hyΓ : y ∈ Γ := pCoreOf_le r Γ hy
  have hdisj : Disjoint (pCoreOf p Γ) (pCoreOf r Γ) :=
    IsPGroup.disjoint_of_ne p r hpr _ _ (isPGroup_pCoreOf p Γ) (isPGroup_pCoreOf r Γ)
  have hc1 : x * y * x⁻¹ * y⁻¹ ∈ pCoreOf r Γ :=
    (pCoreOf r Γ).mul_mem (pCoreOf_normal_conj r Γ x hxΓ y hy) ((pCoreOf r Γ).inv_mem hy)
  have hc2 : x * y * x⁻¹ * y⁻¹ ∈ pCoreOf p Γ := by
    have : x * (y * x⁻¹ * y⁻¹) ∈ pCoreOf p Γ :=
      (pCoreOf p Γ).mul_mem hx (pCoreOf_normal_conj p Γ y hyΓ x⁻¹ ((pCoreOf p Γ).inv_mem hx))
    simpa [mul_assoc] using this
  have h1 : x * y * x⁻¹ * y⁻¹ = 1 := Subgroup.disjoint_def.1 hdisj hc2 hc1
  calc x * y = x * y * x⁻¹ * y⁻¹ * (y * x) := by group
    _ = y * x := by rw [h1, one_mul]


structure Ctx (Γ A : Subgroup (GLV V)) : Prop where
  hyp : G94Hyp Γ A 2
  hd : Module.finrank (ZMod 2) V = 6
  solv : Group.IsSolvable ↥Γ
  three : ∀ S : Subgroup (GLV V), S ≤ Γ → IsPGroup 3 S → Nat.card S ≤ 27


theorem Ctx.A_le_centralizer (hC : Ctx Γ A) {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) :
    A ≤ Subgroup.centralizer (pCoreOf p Γ : Set (GLV V)) := by
  by_contra hnot
  have h4 := (counting_prime_ge_five hC.hyp hp h5 hnot).2.2
  have h6 := hC.hd
  omega

theorem Ctx.inf_centralizer_eq_bot (hC : Ctx Γ A) :
    A ⊓ Subgroup.centralizer (pCoreOf 3 Γ : Set (GLV V)) = ⊥ :=
  g94_inf_centralizer_pCoreOf_three_eq_bot hC.hyp fun _ hp h5 => hC.A_le_centralizer hp h5

theorem Ctx.pCoreOf_three_ne_bot (hC : Ctx Γ A) : pCoreOf 3 Γ ≠ ⊥ := by
  intro h
  have hA : A = ⊥ := by
    rw [eq_bot_iff]
    intro a ha
    have : a ∈ A ⊓ Subgroup.centralizer (pCoreOf 3 Γ : Set (GLV V)) := by
      refine ⟨ha, Subgroup.mem_centralizer_iff.2 fun x hx => ?_⟩
      rw [h, Subgroup.coe_bot, Set.mem_singleton_iff] at hx
      rw [hx]
      simp
    rwa [hC.inf_centralizer_eq_bot] at this
  have h1 := hC.hyp.A_card
  rw [hA, Subgroup.card_bot] at h1
  omega

theorem Ctx.exists_frame (hC : Ctx Γ A) :
    ∃ Fr : Frame V (Fin 2), (∀ i, Fr.x i ∈ pCoreOf 3 Γ) ∧ (∀ i, Fr.x i ≠ 1) ∧ (∀ i, Fr.p i = 3) ∧
      ∀ i, Fr.a i ∈ A := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have := finite_linearEquiv_zmod2 V
  have hyp := hC.hyp
  have hYp : IsPGroup 3 (pCoreOf 3 Γ) := isPGroup_pCoreOf 3 Γ
  have h81 : G81 (pCoreOf 3 Γ) A A :=
    { elemAbelian := hyp.A_elem
      le_pGroup := le_rfl
      pGroup := isPGroup_of_isElemAbelian hyp.A_elem
      le_normalizer := fun a ha => le_normalizer_pCoreOf 3 Γ (hyp.A_le ha)
      nilpotent := hYp.isNilpotent
      odd := odd_card_pCoreOf Nat.prime_three (by norm_num) Γ
      ne_bot := hC.pCoreOf_three_ne_bot }
  obtain ⟨Hs, q, hH, hAle, -, hx⟩ := g8_6 h81 hyp.A_ne hyp.A_card hC.inf_centralizer_eq_bot
  choose x hxY hxH hxo using hx
  obtain ⟨Fr, hFx, hFp, hFa⟩ :=
    exists_frame_of_dihedralFamily hH hyp.A_elem hAle hyp.A_card x hxH hxo
  have hq : ∀ i, q i = 3 := fun i =>
    G8.prime_orderOf_eq_of_mem_pGroup hYp (hxY i) (hxo i) (hH.prime i)
  refine ⟨Fr, fun i => by rw [congrFun hFx i]; exact hxY i, fun i h1 => ?_,
    fun i => by rw [congrFun hFp i]; exact hq i, fun i => (hFa i).1⟩
  have h2 := hxo i
  rw [← congrFun hFx i, h1, orderOf_one, hq i] at h2
  exact absurd h2 (by norm_num)


section Seven

open CntLin

theorem seven_pair {ι : Type} (Fr : Frame V ι) (i : ι) (hp3 : Fr.p i = 3) (hx1 : Fr.x i ≠ 1)
    (hd : Module.finrank (ZMod 2) V = 6) {Q : Subgroup (GLV V)} (hQ7 : IsPGroup 7 Q)
    (hQfix : fixedSpace Q = ⊥) (hcx : ∀ q ∈ Q, q * Fr.x i = Fr.x i * q)
    (hca : ∀ q ∈ Q, q * Fr.a i = Fr.a i * q) :
    fixSp V (Fr.x i) ⊤ = ⊥ ∧
      Module.finrank (ZMod 2) (fixSp V (Fr.a i) (commSp V (Fr.x i) ⊤)) = 3 := by
  have hxS : ∀ s ∈ (⊤ : Submodule (ZMod 2) V), Fr.x i s ∈ (⊤ : Submodule (ZMod 2) V) :=
    fun _ _ => Submodule.mem_top
  have haS : ∀ s ∈ (⊤ : Submodule (ZMod 2) V), Fr.a i s ∈ (⊤ : Submodule (ZMod 2) V) :=
    fun _ _ => Submodule.mem_top
  have hfin := finrank_peel Fr i hxS haS
  rw [finrank_top] at hfin
  have hTfin := dihedral_finrank (Fr.x i) (Fr.a i) (Fr.xpow i) (frame_odd Fr i) (Fr.asq i) (Fr.conj i)
    (commSp V (Fr.x i) ⊤) (peel_T_x Fr i hxS) (peel_T_a Fr i hxS haS) (peel_fix_T Fr i hxS)
  have hadm : Adm Fr ⊤ {i} := fun j hj => by
    rw [Finset.mem_singleton] at hj
    subst hj
    refine ⟨hxS, haS, ?_⟩
    by_contra hcon
    push Not at hcon
    exact hx1 (LinearEquiv.ext fun v => hcon v Submodule.mem_top)
  have hWne := peel_W_ne_bot Fr {i} ⊤ hadm (Finset.mem_singleton_self i)
  have hWpos : 0 < Module.finrank (ZMod 2) (fixSp V (Fr.a i) (commSp V (Fr.x i) ⊤)) := by
    have : Module.Finite (ZMod 2) (fixSp V (Fr.a i) (commSp V (Fr.x i) ⊤)) :=
      Module.Finite.of_finite
    exact Nat.pos_of_ne_zero fun h => hWne (Submodule.finrank_eq_zero.1 h)
  have hTinv : ∀ q ∈ Q, ∀ t ∈ commSp V (Fr.x i) ⊤, q t ∈ commSp V (Fr.x i) ⊤ :=
    fun q hq => commSp_invariant (hcx q hq) fun _ _ => Submodule.mem_top
  have h0 : ∀ v ∈ commSp V (Fr.x i) ⊤, (∀ q ∈ Q, q v = v) → v = 0 := by
    intro v _ hv
    have hv' : v ∈ fixedSpace Q := fun q hq => hv q hq
    rw [hQfix] at hv'
    exact (Submodule.mem_bot (ZMod 2)).1 hv'
  have hdvd := pgroup_dvd_two_pow (by norm_num : Nat.Prime 7) Q hQ7 _ hTinv h0
  rw [hTfin] at hdvd
  have h3 := three_dvd_of_seven_dvd_two_pow_sub_one hdvd
  have hu : Module.finrank (ZMod 2) (fixSp V (Fr.x i) ⊤) = 0 := by omega
  refine ⟨?_, by omega⟩
  have : Module.Finite (ZMod 2) (fixSp V (Fr.x i) ⊤) := Module.Finite.of_finite
  exact Submodule.finrank_eq_zero.1 hu

theorem Ctx.pCoreOf_seven_eq_bot (hC : Ctx Γ A) : pCoreOf 7 Γ = ⊥ := by
  by_contra hne
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Fr, hFxP, hFx1, hFp, hFaA⟩ := hC.exists_frame
  have hQfix : fixedSpace (pCoreOf 7 Γ) = ⊥ := g94_fixedSpace_pCoreOf_eq_bot hC.hyp hne
  have hQ7 : IsPGroup 7 (pCoreOf 7 Γ) := isPGroup_pCoreOf 7 Γ
  have hAQ : A ≤ Subgroup.centralizer (pCoreOf 7 Γ : Set (GLV V)) :=
    hC.A_le_centralizer (by norm_num) (by norm_num)
  have hcx : ∀ i, ∀ q ∈ pCoreOf 7 Γ, q * Fr.x i = Fr.x i * q := fun i q hq =>
    (commute_of_pCoreOf_ne (by norm_num : (3 : ℕ) ≠ 7) (hFxP i) hq).symm
  have hca : ∀ i, ∀ q ∈ pCoreOf 7 Γ, q * Fr.a i = Fr.a i * q := fun i q hq =>
    Subgroup.mem_centralizer_iff.1 (hAQ (hFaA i)) q hq
  have h0 := seven_pair Fr 0 (hFp 0) (hFx1 0) hC.hd hQ7 hQfix (hcx 0) (hca 0)
  have h1 := seven_pair Fr 1 (hFp 1) (hFx1 1) hC.hd hQ7 hQfix (hcx 1) (hca 1)
  have hadm : Adm Fr ⊤ Finset.univ := adm_top Fr Finset.univ fun i _ => hFx1 i
  obtain ⟨hWx, -⟩ := peel_W_invariant Fr Finset.univ ⊤ hadm (Finset.mem_univ 1)
    (show (1 : Fin 2) ≠ 0 by decide)
  have hx1p : Fr.x 1 ^ 3 = 1 := by
    have := Fr.xpow 1
    rwa [hFp 1] at this
  have hdvd := cyclic_dvd_two_pow Nat.prime_three (Fr.x 1) hx1p _ hWx (fun t _ ht => by
    have : t ∈ fixSp V (Fr.x 1) ⊤ := mem_fixSp.2 ⟨Submodule.mem_top, ht⟩
    rw [h1.1] at this
    exact (Submodule.mem_bot (ZMod 2)).1 this)
  rw [h0.2] at hdvd
  norm_num at hdvd

theorem Ctx.pCoreOf_eq_bot (hC : Ctx Γ A) {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) :
    pCoreOf p Γ = ⊥ := by
  by_cases h2 : p = 2
  · subst h2
    exact g94_pCoreOf_two_eq_bot hC.hyp
  by_contra hne
  have hfix := g94_fixedSpace_pCoreOf_eq_bot hC.hyp hne
  have hdvd := pgroup_dvd_two_pow hp (pCoreOf p Γ) (isPGroup_pCoreOf p Γ) ⊤
    (fun _ _ _ _ => Submodule.mem_top) (fun v _ hv => by
      have hv' : v ∈ fixedSpace (pCoreOf p Γ) := fun q hq => hv q hq
      rw [hfix] at hv'
      exact (Submodule.mem_bot (ZMod 2)).1 hv')
  rw [finrank_top, hC.hd] at hdvd
  have h63 : p ∣ 3 * (3 * 7) := by simpa using hdvd
  rcases (Nat.Prime.dvd_mul hp).1 h63 with h | h
  · exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h)
  · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
    · exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h)
    · have hp7 : p = 7 := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h
      subst hp7
      exact hne hC.pCoreOf_seven_eq_bot

theorem Ctx.fitting_eq (hC : Ctx Γ A) :
    (genFittingFitting ↥Γ).map Γ.subtype = pCoreOf 3 Γ := by
  have hle : pCoreOf 3 Γ ≤ (genFittingFitting ↥Γ).map Γ.subtype :=
    pCoreOf_le_fitting Nat.prime_three Γ
  have hcard3 := card_pCoreOf_eq_fitting Nat.prime_three Γ
  have hFpos : Nat.card ↥((genFittingFitting ↥Γ).map Γ.subtype) ≠ 0 := Nat.card_pos.ne'
  have hall : ∀ {d : ℕ}, d.Prime → d ∣ Nat.card ↥((genFittingFitting ↥Γ).map Γ.subtype) → d = 3 := by
    intro d hd hdF
    by_contra hd3
    have hbot := hC.pCoreOf_eq_bot hd hd3
    have hcd := card_pCoreOf_eq_fitting hd Γ
    rw [hbot, Subgroup.card_bot] at hcd
    have hpos := Nat.Prime.factorization_pos_of_dvd hd hFpos hdF
    have := Nat.one_lt_pow hpos.ne' hd.one_lt
    omega
  have hFeq := Nat.eq_prime_pow_of_unique_prime_dvd hFpos hall
  have hv : (Nat.card ↥((genFittingFitting ↥Γ).map Γ.subtype)).factorization 3 =
      (Nat.card ↥((genFittingFitting ↥Γ).map Γ.subtype)).primeFactorsList.length := by
    conv_lhs => rw [hFeq]
    rw [Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same]
  have hcard : Nat.card ↥((genFittingFitting ↥Γ).map Γ.subtype) ≤ Nat.card ↥(pCoreOf 3 Γ) := by
    rw [hcard3, hv]
    exact hFeq.le
  exact (Subgroup.eq_of_le_of_card_ge hle hcard).symm

theorem Ctx.mem_pCoreOf_of_centralizes (hC : Ctx Γ A) {g : GLV V} (hg : g ∈ Γ)
    (h : ∀ x ∈ pCoreOf 3 Γ, g * x = x * g) : g ∈ pCoreOf 3 Γ := by
  have hcent := CFSG.centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hC.solv
  have hmem : (⟨g, hg⟩ : ↥Γ) ∈ Subgroup.centralizer (CFSG.fittingSubgroup ↥Γ : Set ↥Γ) := by
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    have hf' : (f : GLV V) ∈ pCoreOf 3 Γ := by
      rw [← hC.fitting_eq]
      exact Subgroup.mem_map_of_mem _ hf
    exact Subtype.ext (h f hf').symm
  have := hcent hmem
  rw [← hC.fitting_eq]
  exact Subgroup.mem_map.2 ⟨_, this, rfl⟩

end Seven

theorem Ctx.fixedSpace_eq_bot (hC : Ctx Γ A) : fixedSpace (pCoreOf 3 Γ) = ⊥ :=
  g94_fixedSpace_pCoreOf_eq_bot hC.hyp hC.pCoreOf_three_ne_bot

omit [Finite V] in
theorem Ctx.card_le (hC : Ctx Γ A) : Nat.card (pCoreOf 3 Γ) ≤ 27 :=
  hC.three _ (pCoreOf_le 3 Γ) (isPGroup_pCoreOf 3 Γ)

theorem Ctx.exists_frame_elements (hC : Ctx Γ A) :
    ∃ x₀ x₁ a₀ a₁ : GLV V, x₀ ∈ pCoreOf 3 Γ ∧ x₁ ∈ pCoreOf 3 Γ ∧ a₀ ∈ A ∧ a₁ ∈ A ∧
      x₀ ^ 3 = 1 ∧ x₁ ^ 3 = 1 ∧ x₀ ≠ 1 ∧ x₁ ≠ 1 ∧ x₀ * x₁ = x₁ * x₀ ∧ a₀ * a₀ = 1 ∧
      a₁ * a₁ = 1 ∧ a₀ * x₀ * a₀⁻¹ = x₀⁻¹ ∧ a₁ * x₁ * a₁⁻¹ = x₁⁻¹ ∧ a₀ * x₁ = x₁ * a₀ ∧
      a₁ * x₀ = x₀ * a₁ ∧ x₁ ∉ Subgroup.zpowers x₀ := by
  obtain ⟨Fr, hFxP, hFx1, hFp, hFaA⟩ := hC.exists_frame
  have h3 : ∀ i, Fr.x i ^ 3 = 1 := fun i => by
    have := Fr.xpow i
    rwa [hFp i] at this
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  have hx1a0 : Fr.a 0 * Fr.x 1 = Fr.x 1 * Fr.a 0 := (Fr.xa 1 0 h10).symm
  have hx0a1 : Fr.a 1 * Fr.x 0 = Fr.x 0 * Fr.a 1 := (Fr.xa 0 1 h01).symm
  refine ⟨Fr.x 0, Fr.x 1, Fr.a 0, Fr.a 1, hFxP 0, hFxP 1, hFaA 0, hFaA 1, h3 0, h3 1, hFx1 0, hFx1 1,
    Fr.xx 0 1 h01, Fr.asq 0, Fr.asq 1, Fr.conj 0, Fr.conj 1, hx1a0, hx0a1, ?_⟩
  intro hmem
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
  have hconj : Fr.a 0 * Fr.x 1 * (Fr.a 0)⁻¹ = Fr.x 1 := by
    rw [hx1a0]; group
  have h2 : Fr.a 0 * Fr.x 1 * (Fr.a 0)⁻¹ = (Fr.x 1)⁻¹ := by
    rw [← hk]
    have := map_zpow (MulAut.conj (Fr.a 0)) (Fr.x 0) k
    simp only [MulAut.conj_apply] at this
    rw [this, Fr.conj 0, inv_zpow]
  have hsq : Fr.x 1 * Fr.x 1 = 1 := by
    have h3' : Fr.x 1 = (Fr.x 1)⁻¹ := hconj.symm.trans h2
    calc Fr.x 1 * Fr.x 1 = Fr.x 1 * (Fr.x 1)⁻¹ := by rw [← h3']
      _ = 1 := mul_inv_cancel _
  apply hFx1 1
  calc Fr.x 1 = Fr.x 1 ^ 3 * (Fr.x 1 * Fr.x 1)⁻¹ := by group
    _ = 1 := by rw [h3 1, hsq]; simp


theorem Ctx.nine_le_card (hC : Ctx Γ A) : 9 ≤ Nat.card (pCoreOf 3 Γ) := by
  obtain ⟨x₀, x₁, a₀, a₁, hx₀, hx₁, -, -, h30, -, hne0, -, -, -, -, -, -, -, -, hne⟩ :=
    hC.exists_frame_elements
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := (isPGroup_pCoreOf 3 Γ).exists_card_eq
  by_contra hlt
  push Not at hlt
  have hk1 : k ≤ 1 := by
    by_contra h
    have h2 : 2 ≤ k := by omega
    have := Nat.pow_le_pow_right (show 0 < 3 by norm_num) h2
    omega
  have hord : orderOf x₀ = 3 := orderOf_eq_prime h30 hne0
  have hz : Nat.card (Subgroup.zpowers x₀) = 3 := by rw [Nat.card_zpowers, hord]
  have hle : Subgroup.zpowers x₀ ≤ pCoreOf 3 Γ := (Subgroup.zpowers_le).2 hx₀
  have hcard : Nat.card (pCoreOf 3 Γ) ≤ Nat.card (Subgroup.zpowers x₀) := by
    rw [hk, hz]
    calc 3 ^ k ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) hk1
      _ = 3 := by norm_num
  exact hne ((Subgroup.eq_of_le_of_card_ge hle hcard) ▸ hx₁)


end SmD6

end CFSG.Quasithin.SzN31
