module

public import CFSG.RankThree.PartTwo.Sec16.Kcd166.MainAlg
public import CFSG.RankThree.PartTwo.Sec16.Kcd166.ChiefRep
public import CFSG.RankThree.PartTwo.Sec16.Kcd166.BaseChange
public import CFSG.GroupTheory.PerfectSubgroupNormalMeet
public import CFSG.ThirdParty.BrauerInduction.Background.Group.PDecomposition
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.kerRepresentation

public section

namespace CFSG.RankThree.PartTwo.Sec16.Kcd166

open scoped commutatorElement

private lemma normal_le_center_or_top_of_isTripleCover {T : Type*} [Group T]
    (hperf : Group.IsPerfect T)
    (hT : Sec4.IsTripleCover T (alternatingGroup (Fin 6)))
    {N : Subgroup T} (hN : N.Normal) :
    N ≤ Subgroup.center T ∨ N = ⊤ := by
  classical
  haveI : Group.IsPerfect T := hperf
  haveI : N.Normal := hN
  haveI : IsSimpleGroup (T ⧸ Subgroup.center T) := by
    haveI : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
    exact MulEquiv.isSimpleGroup hT.2.some
  have hperfTop : ⁅(⊤ : Subgroup T), (⊤ : Subgroup T)⁆ = ⊤ :=
    Subgroup.commutator_eq_self
  have hsimpleTop :
      IsSimpleGroup (↥(⊤ : Subgroup T) ⧸ Subgroup.center ↥(⊤ : Subgroup T)) := by
    have hcenter : Subgroup.map (Subgroup.topEquiv.toMonoidHom)
        (Subgroup.center ↥(⊤ : Subgroup T)) = Subgroup.center T :=
      Subgroup.map_center_eq (f := Subgroup.topEquiv)
    exact MulEquiv.isSimpleGroup (QuotientGroup.congr
      (G' := Subgroup.center ↥(⊤ : Subgroup T)) (H' := Subgroup.center T)
      Subgroup.topEquiv hcenter)
  have h := Subgroup.le_or_subgroupOf_le_center_of_perfect
    (H := (⊤ : Subgroup T)) (N := N) hperfTop hsimpleTop
  rcases h with htop | hcenter
  · exact Or.inr (eq_top_iff.mpr htop)
  · refine Or.inl fun x hx => ?_
    have hx' : (⟨x, Subgroup.mem_top x⟩ : ↥(⊤ : Subgroup T)) ∈
        (N).subgroupOf (⊤ : Subgroup T) :=
      (Subgroup.mem_subgroupOf (H := N) (K := (⊤ : Subgroup T))).mpr hx
    have hxc := hcenter hx'
    rw [Subgroup.mem_center_iff] at hxc ⊢
    intro y
    simpa using hxc ⟨y, Subgroup.mem_top y⟩

private lemma pi_d_mem_map_of_ne_bot {X T : Type*} [Group X] [Finite X] [Group T]
    (hXperf : Group.IsPerfect X) (π : X →* T) (hπ : Function.Surjective π)
    (hT : Sec4.IsTripleCover T (alternatingGroup (Fin 6)))
    {d : X} (hdZ : π d ∈ Subgroup.center T) {K : Subgroup X} (hK : K.Normal)
    (hbot : K.map π ≠ ⊥) :
    π d ∈ K.map π := by
  classical
  haveI : Group.IsPerfect X := hXperf
  haveI : Finite T := Finite.of_surjective π hπ
  haveI : Group.IsPerfect T := Group.IsPerfect.ofSurjective hπ
  haveI : (K.map π).Normal := hK.map π hπ
  have hdich := normal_le_center_or_top_of_isTripleCover (Group.IsPerfect.ofSurjective hπ) hT
    (N := K.map π) (hK.map π hπ)
  rcases hdich with hle | htop
  · have hcarddvd : Nat.card (K.map π) ∣ 3 := by
      have := Subgroup.card_dvd_of_le hle
      simpa [hT.1] using this
    have hgt1 : 1 < Nat.card (K.map π) :=
      (Subgroup.one_lt_card_iff_ne_bot (K.map π)).mpr hbot
    have hcard3 : Nat.card (K.map π) = 3 := by
      rcases (Nat.dvd_prime Nat.prime_three).mp hcarddvd with h | h
      · exact absurd h hgt1.ne'
      · exact h
    have heq : K.map π = Subgroup.center T :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hcard3, hT.1])
    rw [heq]
    exact hdZ
  · rw [htop]
    exact Subgroup.mem_top _

private lemma mem_of_pi_mem_map {X T : Type*} [Group X] [Group T]
    (π : X →* T) (hker3 : Nat.Coprime (Nat.card π.ker) 3) {d : X} (hd3 : d ^ 3 = 1)
    {K : Subgroup X} (hK : K.Normal) (hπd : π d ∈ K.map π) :
    d ∈ K := by
  classical
  haveI : K.Normal := hK
  obtain ⟨k, hk, hkπ⟩ := Subgroup.mem_map.mp hπd
  let e : X := k⁻¹ * d
  have he : e ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hkπ, inv_mul_cancel]
  have hd_eq : d = k * e := by
    dsimp only [e]
    group
  let qK : X →* X ⧸ K := QuotientGroup.mk' K
  have hqd : qK d = qK e := by
    rw [hd_eq, map_mul]
    have hk1 : qK k = 1 := (QuotientGroup.eq_one_iff k).mpr hk
    rw [hk1, one_mul]
  have hmem : qK d ∈ (π.ker).map qK := by
    rw [hqd]
    exact Subgroup.mem_map_of_mem qK he
  have h3 : (qK d) ^ 3 = 1 := by
    rw [← map_pow, hd3, map_one]
  have hdvd3 : orderOf (qK d) ∣ 3 := orderOf_dvd_of_pow_eq_one h3
  have hdvdker : orderOf (qK d) ∣ Nat.card π.ker :=
    (Subgroup.orderOf_dvd_natCard ((π.ker).map qK) hmem).trans
      (Subgroup.card_map_dvd (H := π.ker) qK)
  have horder1 : orderOf (qK d) = 1 :=
    Nat.eq_one_of_dvd_coprimes hker3 hdvdker hdvd3
  exact (QuotientGroup.eq_one_iff d).mp (orderOf_eq_one_iff.mp horder1)

theorem mem_or_le_ker_of_normal {X T : Type*} [Group X] [Finite X] [Group T]
    (hXperf : Group.IsPerfect X) (π : X →* T) (hπ : Function.Surjective π)
    (hT : Sec4.IsTripleCover T (alternatingGroup (Fin 6)))
    (hker3 : Nat.Coprime (Nat.card π.ker) 3) {d : X} (hd3 : d ^ 3 = 1)
    (hdZ : π d ∈ Subgroup.center T) {K : Subgroup X} (hK : K.Normal) :
    d ∈ K ∨ K ≤ π.ker := by
  classical
  by_cases hbot : K.map π = ⊥
  · exact Or.inr ((Subgroup.map_eq_bot_iff K).mp hbot)
  · exact Or.inl (mem_of_pi_mem_map π hker3 hd3 hK
      (pi_d_mem_map_of_ne_bot hXperf π hπ hT hdZ hK hbot))

private lemma exists_isPGroup_lift {X Γ : Type*} [Group X] [Finite X] [Group Γ] [Finite Γ]
    {f : X →* Γ} (hf : Function.Surjective f) {t : Γ}
    (ht2 : IsPGroup 2 (Subgroup.zpowers t)) :
    ∃ x : X, f x = t ∧ IsPGroup 2 (Subgroup.zpowers x) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨y, rfl⟩ := hf t
  let x := Group.pSingular 2 y
  let z := Group.pRegular 2 y
  have hy : IsOfFinOrder y := isOfFinOrder_of_finite y
  have hdec : z * x = y := Group.pDecomp' 2 hy
  have hcomm : Commute x z := Group.pDecomp_commute 2 y
  have hxs : IsPSingular 2 x := Group.isPSingular_pSingular 2 y
  have hzr : IsPRegular 2 z := Group.isPRegular_pRegular 2 hy
  have hfy : IsOfFinOrder (f y) := isOfFinOrder_of_finite (f y)
  have h1 : f x * f z = f y := by rw [← map_mul, hcomm.eq, hdec]
  have h2 : f z * f x = f y := by rw [← map_mul, hdec]
  have hfxs : IsPSingular 2 (f x) := IsPSingular.map 2 f hxs
  have hfzr : IsPRegular 2 (f z) := IsPRegular.map 2 f hzr
  have hty : IsPSingular 2 (f y) := (IsPSingular.iff_zpowers_isPGroup 2 (f y)).mpr ht2
  obtain ⟨hfx, -⟩ := Group.pSingular_pRegular_unique 2 hfy h1 h2 hfxs hfzr
  refine ⟨x, ?_, ?_⟩
  · rw [hfx, Group.pSingular_eq_self_of_isPSingular 2 hfy hty]
  · exact (IsPSingular.iff_zpowers_isPGroup 2 x).mp hxs

private lemma fixedSubgroup_data {X : Type} [Group X] {N M : Subgroup X} (hN : N.Normal)
    (hNM : N ≤ M) {x : X} :
    ∃ F₀ : Subgroup X, N ≤ F₀ ∧ F₀ ≤ M ∧
      ∀ m ∈ M, x * m * x⁻¹ * m⁻¹ ∈ N ↔ m ∈ F₀ := by
  classical
  letI : N.Normal := hN
  let qN : X →* X ⧸ N := QuotientGroup.mk' N
  let F₀ : Subgroup X :=
    (Subgroup.centralizer ({qN x} : Set (X ⧸ N))).comap qN ⊓ M
  have hF₀M : F₀ ≤ M := inf_le_right
  have hNF₀ : N ≤ F₀ := by
    intro n hn
    refine ⟨?_, hNM hn⟩
    change qN n ∈ Subgroup.centralizer ({qN x} : Set (X ⧸ N))
    have hn1 : qN n = 1 := (QuotientGroup.eq_one_iff n).mpr hn
    rw [hn1]
    exact Subgroup.one_mem _
  refine ⟨F₀, hNF₀, hF₀M, ?_⟩
  intro m hm
  have hmem : m ∈ F₀ ↔ qN m ∈ Subgroup.centralizer ({qN x} : Set (X ⧸ N)) := by
    have h : m ∈ F₀ ↔ m ∈ M ∧ qN m ∈ Subgroup.centralizer ({qN x} : Set (X ⧸ N)) := by
      dsimp only [F₀]
      rw [Subgroup.mem_inf, Subgroup.mem_comap]
      exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
    rw [h]
    exact ⟨fun hh => hh.2, fun hh => ⟨hm, hh⟩⟩
  rw [hmem, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro hc
    have hx : ⁅x, m⁆ ∈ N := by simpa [commutatorElement_def] using hc
    have hq : ⁅qN x, qN m⁆ = 1 := by
      rw [← map_commutatorElement]
      exact (QuotientGroup.eq_one_iff ⁅x, m⁆).mpr hx
    exact (commutatorElement_eq_one_iff_mul_comm.mp hq).symm
  · intro hc
    have hq : ⁅qN x, qN m⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr hc.symm
    rw [← map_commutatorElement] at hq
    have hx : ⁅x, m⁆ ∈ N := (QuotientGroup.eq_one_iff ⁅x, m⁆).mp hq
    simpa [commutatorElement_def] using hx

private lemma range_chiefQ {X : Type} [Group X] {p : ℕ} [Fact p.Prime]
    {N M F₀ : Subgroup X} (hMn : M.Normal) (hF₀M : F₀ ≤ M)
    {F : Type} [AddCommGroup F] [Module (ZMod p) F]
    (ρ : Representation (ZMod p) X F) (q : X → F)
    (hqadd : ∀ m ∈ M, ∀ m' ∈ M, q (m * m') = q m + q m')
    (hqker : ∀ m ∈ M, q m = 0 ↔ m ∈ N)
    (hρ : ∀ x : X, ∀ m ∈ M, ρ x (q m) = q (x * m * x⁻¹))
    (hqsurj : ∀ f : F, ∃ m ∈ M, q m = f)
    {x : X} (hfix : ∀ m ∈ M, x * m * x⁻¹ * m⁻¹ ∈ N ↔ m ∈ F₀)
    (qF : F₀ →* Multiplicative F)
    (hqF : ∀ a : F₀, qF a = Multiplicative.ofAdd (q a)) :
  qF.range = (LinearMap.ker (ρ x - 1)).toAddSubgroup.toSubgroup := by
  ext v
  constructor
  · rintro ⟨a, rfl⟩
    rw [Multiplicative.mem_toSubgroup, hqF a]
    change (ρ x - 1) (q (a : X)) = 0
    rw [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
    have hP : x * (a : X) * x⁻¹ * (a : X)⁻¹ ∈ N :=
      (hfix a (hF₀M a.2)).mpr a.2
    have hc : (a : X) * x * (a : X)⁻¹ * x⁻¹ ∈ N := by
      have := N.inv_mem hP
      rwa [show (x * (a : X) * x⁻¹ * (a : X)⁻¹)⁻¹ =
        (a : X) * x * (a : X)⁻¹ * x⁻¹ by group] at this
    exact (@rho_apply_eq_iff X _ N M p F _ _ ρ q hqadd hqker hρ hMn (a : X) (hF₀M a.2) x).mpr hc
  · intro hv
    rw [Multiplicative.mem_toSubgroup] at hv
    change (ρ x - 1) (Multiplicative.toAdd v) = 0 at hv
    rw [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hv
    obtain ⟨m, hmM, hqm⟩ := hqsurj (Multiplicative.toAdd v)
    have hcomm : m * x * m⁻¹ * x⁻¹ ∈ N := by
      apply (@rho_apply_eq_iff X _ N M p F _ _ ρ q hqadd hqker hρ hMn m hmM x).mp
      rw [hqm]
      exact hv
    have hmF₀ : m ∈ F₀ := by
      apply (hfix m hmM).mp
      have := N.inv_mem hcomm
      rwa [show (m * x * m⁻¹ * x⁻¹)⁻¹ = x * m * x⁻¹ * m⁻¹ by group] at this
    refine ⟨⟨m, hmF₀⟩, ?_⟩
    rw [hqF]
    change Multiplicative.ofAdd (q m) = v
    rw [hqm]
    simp

private lemma natCard_ker_le_relIndex {X : Type} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    {N M F₀ : Subgroup X} (hN : N.Normal) (hMn : M.Normal) (hF₀M : F₀ ≤ M)
    (hNF₀ : N ≤ F₀) {F : Type} [AddCommGroup F] [Module (ZMod p) F]
    (ρ : Representation (ZMod p) X F) (q : X → F)
    (hqadd : ∀ m ∈ M, ∀ m' ∈ M, q (m * m') = q m + q m')
    (hqker : ∀ m ∈ M, q m = 0 ↔ m ∈ N)
    (hρ : ∀ x : X, ∀ m ∈ M, ρ x (q m) = q (x * m * x⁻¹))
    (hqsurj : ∀ f : F, ∃ m ∈ M, q m = f)
    {x : X} (hfix : ∀ m ∈ M, x * m * x⁻¹ * m⁻¹ ∈ N ↔ m ∈ F₀) :
    Nat.card (LinearMap.ker (ρ x - 1)) ≤ N.relIndex F₀ := by
  classical
  letI : N.Normal := hN
  haveI : M.Normal := hMn
  let qF : F₀ →* Multiplicative F :=
    { toFun := fun a => Multiplicative.ofAdd (q a)
      map_one' := by
        have h1 : q (1 : X) = 0 := (hqker 1 M.one_mem).mpr N.one_mem
        simp [h1]
      map_mul' := fun a b => by
        have h := hqadd (a : X) (hF₀M a.2) (b : X) (hF₀M b.2)
        change Multiplicative.ofAdd (q ((a : X) * (b : X))) =
          Multiplicative.ofAdd (q (a : X)) * Multiplicative.ofAdd (q (b : X))
        rw [h]
        rfl }
  have hqFker : qF.ker = N.subgroupOf F₀ := by
    ext a
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    change Multiplicative.ofAdd (q (a : X)) = 1 ↔ (a : X) ∈ N
    simpa using hqker (a : X) (hF₀M a.2)
  let Kx : AddSubgroup F := (LinearMap.ker (ρ x - 1)).toAddSubgroup
  have hqFrange : qF.range = Kx.toSubgroup :=
    range_chiefQ hMn hF₀M ρ q hqadd hqker hρ hqsurj hfix qF (fun a => rfl)
  have hcardrange : Nat.card qF.range = Nat.card Kx := by
    refine Nat.card_congr ?_
    refine
      { toFun := fun a => ⟨Multiplicative.toAdd a.val,
          (Multiplicative.mem_toSubgroup Kx a.val).mp ?_⟩
        invFun := fun a => ⟨Multiplicative.ofAdd a.val, ?_⟩
        left_inv := fun a => by ext; rfl
        right_inv := fun a => by ext; rfl }
    · rw [← hqFrange]
      exact a.2
    · rw [hqFrange]
      exact (Multiplicative.mem_toSubgroup Kx a.val).mpr a.2
  have hfirst : Nat.card (F₀ ⧸ N.subgroupOf F₀) = Nat.card qF.range := by
    rw [← hqFker]
    exact Nat.card_congr (QuotientGroup.quotientKerEquivRange qF).toEquiv
  change Nat.card Kx ≤ N.relIndex F₀
  rw [Subgroup.relIndex, Subgroup.index_eq_card, hfirst, hcardrange]

private lemma finrank_ker_le_three {X : Type} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    (hp5 : 5 ≤ p) {N M : Subgroup X} (hNn : N.Normal) (hMn : M.Normal) (hNM : N < M)
    (hcomm : ∀ x ∈ M, ∀ y ∈ M, x * y * x⁻¹ * y⁻¹ ∈ N)
    (hexp : ∀ x ∈ M, x ^ p ∈ N)
    (hR3 : ∀ N M : Subgroup X, N.Normal → M.Normal → N ≤ M →
      (∀ x ∈ M, ∀ y ∈ M, x * y * x⁻¹ * y⁻¹ ∈ N) → (∀ x ∈ M, x ^ p ∈ N) →
      ∀ t : X, IsPGroup 2 (Subgroup.zpowers t) →
        (∃ m ∈ M, t * m * t⁻¹ * m⁻¹ ∉ N) →
      ∀ F : Subgroup X, N ≤ F → F ≤ M →
        (∀ f ∈ F, t * f * t⁻¹ * f⁻¹ ∈ N) → N.relIndex F ≤ p ^ 3)
    {F : Type} [AddCommGroup F] [Module (ZMod p) F] [Module.Finite (ZMod p) F]
    (ρ : Representation (ZMod p) X F) (q : X → F)
    (hqadd : ∀ m ∈ M, ∀ m' ∈ M, q (m * m') = q m + q m')
    (hqker : ∀ m ∈ M, q m = 0 ↔ m ∈ N)
    (hρ : ∀ x : X, ∀ m ∈ M, ρ x (q m) = q (x * m * x⁻¹))
    (hqsurj : ∀ f : F, ∃ m ∈ M, q m = f)
    {x : X} (hx2 : IsPGroup 2 (Subgroup.zpowers x)) (hxker : x ∉ ρ.ker) :
    Module.finrank (ZMod p) (LinearMap.ker (ρ x - 1)) ≤ 3 := by
  classical
  haveI : N.Normal := hNn
  haveI : M.Normal := hMn
  obtain ⟨F₀, hNF₀, hF₀M, hfix⟩ := fixedSubgroup_data hNn hNM.le
  have hnonfix : ∃ m ∈ M, x * m * x⁻¹ * m⁻¹ ∉ N := by
    by_contra h
    push Not at h
    have hρx1 : ρ x = 1 := by
      ext f
      obtain ⟨m, hmM, rfl⟩ := hqsurj f
      have hfixm : x * m * x⁻¹ * m⁻¹ ∈ N := h m hmM
      have hc : m * x * m⁻¹ * x⁻¹ ∈ N := by
        have := N.inv_mem hfixm
        rwa [show (x * m * x⁻¹ * m⁻¹)⁻¹ = m * x * m⁻¹ * x⁻¹ by group] at this
      exact (@rho_apply_eq_iff X _ N M p F _ _ ρ q hqadd hqker hρ hMn m hmM x).mpr hc
    exact hxker (MonoidHom.mem_ker.mpr hρx1)
  have hR3app : N.relIndex F₀ ≤ p ^ 3 :=
    hR3 N M hNn hMn hNM.le hcomm hexp x hx2 hnonfix F₀ hNF₀ hF₀M
      (fun f hf => (hfix f (hF₀M hf)).mpr hf)
  have hcard : Nat.card (LinearMap.ker (ρ x - 1)) ≤ p ^ 3 :=
    (natCard_ker_le_relIndex hNn hMn hF₀M hNF₀ ρ q hqadd hqker hρ hqsurj hfix).trans
      hR3app
  have hcard' : p ^ Module.finrank (ZMod p) (LinearMap.ker (ρ x - 1)) ≤ p ^ 3 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod p)
      (V := LinearMap.ker (ρ x - 1)), Nat.card_eq_fintype_card, ZMod.card] at hcard
    exact hcard
  exact (Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt).mp hcard'



private lemma fixed_of_mainAlg166 (hmain : MainAlg166) {Γ T : Type} [Group Γ] [Finite Γ]
    [Group T] {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p)
    {F : Type} [AddCommGroup F] [Module (ZMod p) F] [Module.Finite (ZMod p) F]
    (ρbar : Representation (ZMod p) Γ F) (hirr : ρbar.IsIrreducible)
    (hfaith : Function.Injective ρbar) (hΓperf : Group.IsPerfect Γ)
    (hR3bar : ∀ t : Γ, IsPGroup 2 (Subgroup.zpowers t) → t ≠ 1 →
      Module.finrank (ZMod p) (LinearMap.ker (ρbar t - 1)) ≤ 3)
    (πbar : Γ →* T) (hπbar : Function.Surjective πbar)
    (hT : Sec4.IsTripleCover T (alternatingGroup (Fin 6)))
    (hker3 : Nat.Coprime (Nat.card πbar.ker) 3) (hkerS : Group.IsSolvable πbar.ker)
    (g : Γ) (hg3 : g ^ 3 = 1) (hgZ : πbar g ∈ Subgroup.center T)
    (J : Subgroup Γ) (hJperf : Group.IsPerfect J)
    (hJA5 : Nonempty (↥(J.map πbar) ≃* alternatingGroup (Fin 5)))
    (hJ2 : IsPGroup 2 ↥(J ⊓ πbar.ker))
    (hJd : J ≤ Subgroup.centralizer ({g} : Set Γ)) :
    ∀ f : F, (∀ j ∈ J, ρbar j f = f) → ρbar g f = f := by
  obtain ⟨𝕜, h𝕜field, h𝕜alg, h𝕜char, V, hVadd, hVmod, hVfin, σ,
    hσirr, hσinj, hσbound, hσdesc⟩ :=
    exists_isAlgClosed_extension (p := p) ρbar hirr hfaith
  letI := h𝕜field
  letI := h𝕜alg
  letI := h𝕜char
  letI := hVadd
  letI := hVmod
  letI := hVfin
  have hR3σ : ∀ t : Γ, IsPGroup 2 (Subgroup.zpowers t) → t ≠ 1 →
      Module.finrank 𝕜 (LinearMap.ker (σ t - 1)) ≤ 3 :=
    fun t ht2 htne => (hσbound t).trans (hR3bar t ht2 htne)
  have hσmain : ∀ v : V, (∀ j ∈ J, σ j v = v) → σ g v = v :=
    hmain 𝕜 p (Fact.out : p.Prime) hp5 Γ hΓperf V σ hσirr hσinj hR3σ
      T πbar hπbar hT hker3 hkerS g hg3 hgZ J hJperf hJA5 hJ2 hJd
  exact hσdesc J g hσmain

private lemma quotient_basic {X T : Type*} [Group X] [Group T]
    (π : X →* T) (hπ : Function.Surjective π)
    (hkerS : Group.IsSolvable π.ker) (hker3 : Nat.Coprime (Nat.card π.ker) 3)
    {K : Subgroup X} (hK : K.Normal) (hKle : K ≤ π.ker)
    {d : X} (hd3 : d ^ 3 = 1) (hdZ : π d ∈ Subgroup.center T) :
    Function.Surjective (QuotientGroup.lift K π hKle) ∧
    Nat.Coprime (Nat.card (QuotientGroup.lift K π hKle).ker) 3 ∧
    Group.IsSolvable (QuotientGroup.lift K π hKle).ker ∧
    (QuotientGroup.mk' K d) ^ 3 = 1 ∧
    (QuotientGroup.lift K π hKle) (QuotientGroup.mk' K d) ∈ Subgroup.center T := by
  classical
  haveI : K.Normal := hK
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact QuotientGroup.lift_surjective_of_surjective (N := K) π hπ hKle
  · have hker : (QuotientGroup.lift K π hKle).ker = (π.ker).map (QuotientGroup.mk' K) :=
      QuotientGroup.ker_lift (N := K) π hKle
    rw [hker]
    exact hker3.coprime_dvd_left
      (Subgroup.card_map_dvd (H := π.ker) (QuotientGroup.mk' K))
  · have hker : (QuotientGroup.lift K π hKle).ker = (π.ker).map (QuotientGroup.mk' K) :=
      QuotientGroup.ker_lift (N := K) π hKle
    rw [hker]
    haveI : Group.IsSolvable ↥π.ker := hkerS
    exact Group.isSolvable_of_surjective
      (f := (QuotientGroup.mk' K).subgroupMap π.ker)
      ((QuotientGroup.mk' K).subgroupMap_surjective π.ker)
  · rw [← map_pow, hd3, map_one]
  · change π d ∈ Subgroup.center T
    exact hdZ

private lemma quotient_I1 {X T : Type*} [Group X] [Group T]
    (π : X →* T) {K : Subgroup X} (hK : K.Normal) (hKle : K ≤ π.ker)
    {d : X} {I₁ : Subgroup X} (hI₁ : Group.IsPerfect I₁)
    (hI₁A5 : Nonempty (↥(I₁.map π) ≃* alternatingGroup (Fin 5)))
    (hI₁2 : IsPGroup 2 ↥(I₁ ⊓ π.ker))
    (hI₁d : I₁ ≤ Subgroup.centralizer ({d} : Set X)) :
    Group.IsPerfect (I₁.map (QuotientGroup.mk' K)) ∧
    Nonempty (↥((I₁.map (QuotientGroup.mk' K)).map (QuotientGroup.lift K π hKle))
      ≃* alternatingGroup (Fin 5)) ∧
    IsPGroup 2 ↥((I₁.map (QuotientGroup.mk' K)) ⊓
      (QuotientGroup.lift K π hKle).ker) ∧
    I₁.map (QuotientGroup.mk' K) ≤
      Subgroup.centralizer ({QuotientGroup.mk' K d} : Set (X ⧸ K)) := by
  classical
  haveI : K.Normal := hK
  refine ⟨?_, ?_, ?_, ?_⟩
  · haveI : Group.IsPerfect I₁ := hI₁
    exact Group.IsPerfect.map (QuotientGroup.mk' K)
  · have hcomp : (QuotientGroup.lift K π hKle).comp (QuotientGroup.mk' K) = π :=
      MonoidHom.ext fun x => rfl
    have hmap : (I₁.map (QuotientGroup.mk' K)).map (QuotientGroup.lift K π hKle) =
        I₁.map π := by
      rw [Subgroup.map_map, hcomp]
    rw [hmap]
    exact hI₁A5
  · have hle : (I₁.map (QuotientGroup.mk' K)) ⊓ (QuotientGroup.lift K π hKle).ker ≤
        (I₁ ⊓ π.ker).map (QuotientGroup.mk' K) := by
      rintro x ⟨hxI, hxK⟩
      obtain ⟨i, hi, rfl⟩ := hxI
      have h1 : π i = 1 := by
        have h2 := MonoidHom.mem_ker.mp hxK
        change π i = 1 at h2
        exact h2
      exact Subgroup.mem_map.mpr ⟨i, ⟨hi, MonoidHom.mem_ker.mpr h1⟩, rfl⟩
    haveI : IsPGroup 2 ↥((I₁ ⊓ π.ker).map (QuotientGroup.mk' K)) :=
      hI₁2.map (QuotientGroup.mk' K)
    exact IsPGroup.to_le this hle
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := hx
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    exact congrArg (QuotientGroup.mk' K)
      (Subgroup.mem_centralizer_singleton_iff.mp (hI₁d hi))

private lemma hR3bar_of_chiefRep {X : Type} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    (hp5 : 5 ≤ p) {N M : Subgroup X} (hNn : N.Normal) (hMn : M.Normal) (hNM : N < M)
    (hcomm : ∀ x ∈ M, ∀ y ∈ M, x * y * x⁻¹ * y⁻¹ ∈ N)
    (hexp : ∀ x ∈ M, x ^ p ∈ N)
    (hR3 : ∀ N M : Subgroup X, N.Normal → M.Normal → N ≤ M →
      (∀ x ∈ M, ∀ y ∈ M, x * y * x⁻¹ * y⁻¹ ∈ N) → (∀ x ∈ M, x ^ p ∈ N) →
      ∀ t : X, IsPGroup 2 (Subgroup.zpowers t) →
        (∃ m ∈ M, t * m * t⁻¹ * m⁻¹ ∉ N) →
      ∀ F : Subgroup X, N ≤ F → F ≤ M →
        (∀ f ∈ F, t * f * t⁻¹ * f⁻¹ ∈ N) → N.relIndex F ≤ p ^ 3)
    {F : Type} [AddCommGroup F] [Module (ZMod p) F] [Module.Finite (ZMod p) F]
    (ρ : Representation (ZMod p) X F) (q : X → F)
    (hqadd : ∀ m ∈ M, ∀ m' ∈ M, q (m * m') = q m + q m')
    (hqker : ∀ m ∈ M, q m = 0 ↔ m ∈ N)
    (hρ : ∀ x : X, ∀ m ∈ M, ρ x (q m) = q (x * m * x⁻¹))
    (hqsurj : ∀ f : F, ∃ m ∈ M, q m = f) :
    ∀ t : X ⧸ ρ.ker, IsPGroup 2 (Subgroup.zpowers t) → t ≠ 1 →
      Module.finrank (ZMod p) (LinearMap.ker
        (CFSG.Theory.Representation.kerRepresentation ρ t - 1)) ≤ 3 := by
  intro t ht2 htne
  obtain ⟨x, hfx, hx2⟩ := exists_isPGroup_lift
    (f := QuotientGroup.mk' ρ.ker) (QuotientGroup.mk'_surjective ρ.ker) ht2
  have hxker : x ∉ ρ.ker := by
    intro hx
    have h1 : QuotientGroup.mk' ρ.ker x = 1 := (QuotientGroup.eq_one_iff x).mpr hx
    exact htne (hfx.symm.trans h1)
  have hfin : Module.finrank (ZMod p) (LinearMap.ker (ρ x - 1)) ≤ 3 :=
    finrank_ker_le_three hp5 hNn hMn hNM hcomm hexp hR3 ρ q hqadd hqker hρ
      hqsurj hx2 hxker
  have hρbar : CFSG.Theory.Representation.kerRepresentation ρ t = ρ x := by
    rw [← hfx]
    rfl
  rwa [← hρbar] at hfin

theorem gflat_of_mainAlg166 (hmain : MainAlg166) {X : Type} [Group X] [Finite X]
    (hXperf : Group.IsPerfect X) {T : Type} [Group T] (π : X →* T)
    (hπ : Function.Surjective π) (hT : Sec4.IsTripleCover T (alternatingGroup (Fin 6)))
    (hkerS : Group.IsSolvable π.ker) (hker3 : Nat.Coprime (Nat.card π.ker) 3)
    {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p)
    (hR3 : ∀ N M : Subgroup X, N.Normal → M.Normal → N ≤ M →
      (∀ x ∈ M, ∀ y ∈ M, x * y * x⁻¹ * y⁻¹ ∈ N) → (∀ x ∈ M, x ^ p ∈ N) →
      ∀ t : X, IsPGroup 2 (Subgroup.zpowers t) → (∃ m ∈ M, t * m * t⁻¹ * m⁻¹ ∉ N) →
      ∀ F : Subgroup X, N ≤ F → F ≤ M → (∀ f ∈ F, t * f * t⁻¹ * f⁻¹ ∈ N) →
        N.relIndex F ≤ p ^ 3)
    {d : X} (hd3 : d ^ 3 = 1) (hdZ : π d ∈ Subgroup.center T)
    {I₁ : Subgroup X} (hI₁ : Group.IsPerfect I₁)
    (hI₁A5 : Nonempty (↥(I₁.map π) ≃* alternatingGroup (Fin 5)))
    (hI₁2 : IsPGroup 2 ↥(I₁ ⊓ π.ker)) (hI₁d : I₁ ≤ Subgroup.centralizer ({d} : Set X)) :
    ∀ N M : Subgroup X, N.Normal → M.Normal → N < M → M ≤ π.ker →
      (∀ K : Subgroup X, K.Normal → N ≤ K → K ≤ M → K = N ∨ K = M) →
      (∀ x ∈ M, ∀ y ∈ M, x * y * x⁻¹ * y⁻¹ ∈ N) → (∀ x ∈ M, x ^ p ∈ N) →
      ∀ m ∈ M, (∀ i ∈ I₁, m * i * m⁻¹ * i⁻¹ ∈ N) → m * d * m⁻¹ * d⁻¹ ∈ N := by
  classical
  haveI : Group.IsPerfect X := hXperf
  intro N M hNn hMn hNM hMD hChief hcomm hexp m hmM hfixI
  obtain ⟨F, hFadd, hFmod, hFfin, ρ, q, hirr, hqsurj, hqadd, hqker, hρ⟩ :=
    exists_chiefRep (p := p) hNn hMn hNM hChief hcomm hexp
  letI := hFadd
  letI := hFmod
  letI := hFfin
  have hfixρ : ∀ i ∈ I₁, ρ i (q m) = q m := fun i hi =>
    (@rho_apply_eq_iff X _ N M p F _ _ ρ q hqadd hqker hρ hMn m hmM i).mpr (hfixI i hi)
  suffices hgoal : ρ d (q m) = q m by
    exact (@rho_apply_eq_iff X _ N M p F _ _ ρ q hqadd hqker hρ hMn m hmM d).mp hgoal
  let K : Subgroup X := ρ.ker
  have hKn : K.Normal := by
    change (MonoidHom.ker ρ).Normal
    infer_instance
  rcases mem_or_le_ker_of_normal hXperf π hπ hT hker3 hd3 hdZ hKn with hdK | hKle
  · have hρd : ρ d = 1 := MonoidHom.mem_ker.mp hdK
    rw [hρd]
    exact Module.End.one_apply (q m)
  · let Γ := X ⧸ K
    let ρbar : Representation (ZMod p) Γ F :=
      CFSG.Theory.Representation.kerRepresentation ρ
    let πbar : Γ →* T := QuotientGroup.lift K π hKle
    let Ī₁ : Subgroup Γ := I₁.map (QuotientGroup.mk' K)
    haveI : Group.IsPerfect Γ := by
      change Group.IsPerfect (X ⧸ K)
      infer_instance
    haveI : Finite Γ := by
      change Finite (X ⧸ K)
      infer_instance
    obtain ⟨hπbar_surj, hker3bar, hkerSbar, hd3bar, hdZbar⟩ :=
      quotient_basic π hπ hkerS hker3 hKn hKle hd3 hdZ
    obtain ⟨hI₁perf, hI₁A5bar, hI₁2bar, hI₁dbar⟩ :=
      quotient_I1 π hKn hKle hI₁ hI₁A5 hI₁2 hI₁d
    have hR3bar := hR3bar_of_chiefRep hp5 hNn hMn hNM hcomm hexp hR3 ρ q hqadd hqker hρ hqsurj
    have hfixbar : ∀ h ∈ Ī₁, ρbar h (q m) = q m := by
      intro h hh
      obtain ⟨i, hi, rfl⟩ := hh
      change ρ i (q m) = q m
      exact hfixρ i hi
    have hfinal : ρbar (QuotientGroup.mk' K d) (q m) = q m :=
      fixed_of_mainAlg166 hmain hp5 ρbar
        ((CFSG.Theory.Representation.kerRepresentation_irreducible_iff ρ).mpr hirr)
        (CFSG.Theory.Representation.kerRepresentation_faithful ρ)
        inferInstance hR3bar πbar hπbar_surj hT hker3bar hkerSbar
        (QuotientGroup.mk' K d) hd3bar hdZbar Ī₁ hI₁perf hI₁A5bar hI₁2bar hI₁dbar
        (q m) hfixbar
    change ρ d (q m) = q m
    exact hfinal
end CFSG.RankThree.PartTwo.Sec16.Kcd166
