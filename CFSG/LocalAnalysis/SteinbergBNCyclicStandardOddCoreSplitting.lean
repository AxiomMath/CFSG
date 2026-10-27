module

public import CFSG.LocalAnalysis.ComponentClassification.StandardRecognitionKernel
public import CFSG.GroupTheory.CyclicSylowNormalOddComplement

public section

namespace CFSG.LocalAnalysis

open Subgroup
open scoped Pointwise

@[expose] def conjActOn {G : Type*} [Group G] {K H : Subgroup G}
    (hK : ∀ h ∈ H, ∀ k ∈ K, h * k * h⁻¹ ∈ K) : H →* MulAut K where
  toFun h :=
    { toFun := fun k => ⟨h * k * (h : G)⁻¹, hK h h.2 k k.2⟩
      invFun := fun k => ⟨(h : G)⁻¹ * k * (h : G)⁻¹⁻¹, hK _ (inv_mem h.2) k k.2⟩
      left_inv := fun k => Subtype.ext (by simp [mul_assoc])
      right_inv := fun k => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun k k' => Subtype.ext (by simp [mul_assoc]) }
  map_one' := by
    ext k
    simp
  map_mul' h h' := by
    ext k
    simp [mul_assoc]

theorem coe_conjActOn_apply {G : Type*} [Group G] {K H : Subgroup G}
    (hK : ∀ h ∈ H, ∀ k ∈ K, h * k * h⁻¹ ∈ K) (h : H) (k : K) :
    ((conjActOn hK h k : K) : G) = h * k * (h : G)⁻¹ := rfl

theorem exists_semidirectProduct_mulEquiv {G : Type*} [Group G] {K H M : Subgroup G}
    (hKM : K ≤ M) (hHM : H ≤ M) (hK : ∀ h ∈ H, ∀ k ∈ K, h * k * h⁻¹ ∈ K)
    (hinter : K ⊓ H = ⊥) (hprod : (K : Set G) * (H : Set G) = M) :
    ∃ φ : H →* MulAut K, (∀ h k, ((φ h k : K) : G) = h * k * (h : G)⁻¹) ∧
      ∃ e : K ⋊[φ] H ≃* M, ∀ k h, ((e ⟨k, h⟩ : M) : G) = k * h := by
  refine ⟨conjActOn hK, fun h k => rfl, ?_⟩
  let f : K ⋊[conjActOn hK] H →* M := SemidirectProduct.lift (inclusion hKM) (inclusion hHM)
    fun h => by
      ext k
      simp [coe_conjActOn_apply, MulAut.conj_apply]
  have hf : ∀ x : K ⋊[conjActOn hK] H, ((f x : M) : G) = x.1 * x.2 := fun x => rfl
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have h1 : (x.1 : G) * x.2 = 1 := by rw [← hf, hx]; rfl
    have h2 : (x.1 : G) = (x.2 : G)⁻¹ := eq_inv_of_mul_eq_one_left h1
    have h3 : (x.1 : G) ∈ K ⊓ H := mem_inf.mpr ⟨x.1.2, h2 ▸ inv_mem x.2.2⟩
    rw [hinter, mem_bot] at h3
    have h4 : (x.2 : G) = 1 := by rw [h3, eq_comm, inv_eq_one] at h2; exact h2
    exact SemidirectProduct.ext (Subtype.ext h3) (Subtype.ext h4)
  have hsurj : Function.Surjective f := by
    intro m
    have hm : (m : G) ∈ (K : Set G) * (H : Set G) := by rw [hprod]; exact m.2
    obtain ⟨k, hk, h, hh, hkh⟩ := hm
    exact ⟨⟨⟨k, hk⟩, ⟨h, hh⟩⟩, Subtype.ext hkh⟩
  exact ⟨MulEquiv.ofBijective f ⟨hinj, hsurj⟩, fun k h => rfl⟩

theorem oddCore_eq_pPrimeCore_two (X : Type*) [Group X] :
    CFSG.oddCore X = CFSG.pPrimeCore 2 X := by
  unfold CFSG.oddCore CFSG.pPrimeCore
  congr 1
  ext N
  simp [Nat.coprime_two_left]

theorem cyclic_standard_full_normalizer_odd_core_splitting {G : Type*} [Group G] [Finite G]
    {L : Subgroup G} (hL : CFSG.Assembly.ComponentType.IsStandardSubgroup L)
    (S : Sylow 2 (centralizer (L : Set G)))
    (hS : IsCyclic (S : Subgroup (centralizer (L : Set G))))
    {t : centralizer (L : Set G)} (htS : t ∈ S) (ht : orderOf t = 2)
    (hcore : CFSG.oddCore (centralizer ({(t : G)} : Set G)) = ⊥) :
    let C := centralizer (L : Set G)
    let Sg := (S : Subgroup C).map C.subtype
    let H := centralizer ({(t : G)} : Set G)
    let M := normalizer (L : Set G)
    let K := (CFSG.oddCore C).map C.subtype
    Sg ≠ ⊥ ∧ C ⊓ H = Sg ∧ (Sg.subgroupOf H).Normal ∧ K = (CFSG.oddCore M).map M.subtype ∧
      (∀ k₁ ∈ K, ∀ k₂ ∈ K, k₁ * k₂ = k₂ * k₁) ∧ (∀ k ∈ K, (t : G)⁻¹ * k * t = k⁻¹) ∧
      K ⊓ H = ⊥ ∧ (K : Set G) * (Sg : Set G) = C ∧ (K : Set G) * (H : Set G) = M ∧
      (∃ φ : H →* MulAut K, (∀ h k, ((φ h k : K) : G) = h * k * (h : G)⁻¹) ∧
        ∃ e : K ⋊[φ] H ≃* M, ∀ k h, ((e ⟨k, h⟩ : M) : G) = k * h) ∧
      (∃ ψ : Sg →* MulAut K, (∀ s k, ((ψ s k : K) : G) = s * k * (s : G)⁻¹) ∧
        ∃ e : K ⋊[ψ] Sg ≃* C, ∀ k s, ((e ⟨k, s⟩ : C) : G) = k * s) ∧
      (∃ hHM : H ≤ M, ∃ _ : (K.subgroupOf M).Normal,
        (QuotientGroup.mk' (K.subgroupOf M)).ker = K.subgroupOf M ∧
        Function.Bijective ((QuotientGroup.mk' (K.subgroupOf M)).comp (inclusion hHM)) ∧
        (Sg.subgroupOf M).map (QuotientGroup.mk' (K.subgroupOf M)) =
          (C.subgroupOf M).map (QuotientGroup.mk' (K.subgroupOf M))) ∧
      ∀ T : Sylow 2 H, Sg ≤ (T : Subgroup H).map H.subtype ∧
        ∃ T' : Sylow 2 M, (T' : Subgroup M) = ((T : Subgroup H).map H.subtype).subgroupOf M := by
  intro C Sg H M K
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hSne, huniq, -, -, -, -, hCH, hSn, -⟩ :=
    CFSG.ComponentClassification.StandardRecognition.standard_cyclic_local_centralizer_kernel hL S
      hS htS ht hcore
  have hCH' : C ⊓ H = Sg := hCH
  have hSn' : (Sg.subgroupOf H).Normal := hSn
  have ht2 : orderOf (t : G) = 2 := by rwa [Subgroup.orderOf_coe]
  have hHM : H ≤ M :=
    (CFSG.LocalAnalysis.ComponentInitial.standard_involution_centralizer_normality hL t.2 ht2).1
  have hCM : C ≤ M := centralizer_le_normalizer _
  have hSgne : Sg ≠ ⊥ := fun h => hSne ((map_eq_bot_iff_of_injective _ C.subtype_injective).mp h)
  have hCnorm : ∀ m ∈ M, ∀ c ∈ C, m * c * m⁻¹ ∈ C := fun m hm c hc => by
    rw [mem_centralizer_iff] at hc ⊢
    intro l hl
    have hl' : m⁻¹ * l * m⁻¹⁻¹ ∈ L := (mem_normalizer_iff.mp (inv_mem hm) l).mp hl
    rw [inv_inv] at hl'
    have h1 := hc _ hl'
    calc l * (m * c * m⁻¹) = m * ((m⁻¹ * l * m) * c) * m⁻¹ := by group
      _ = m * (c * (m⁻¹ * l * m)) * m⁻¹ := by rw [h1]
      _ = m * c * m⁻¹ * l := by group
  obtain ⟨-, hprodC, hinterC, ⟨-, hoddC, -, -⟩, hcharC⟩ :=
    CFSG.cyclic_sylow_normal_odd_complement S hS
  rw [← oddCore_eq_pPrimeCore_two] at hprodC hinterC hoddC hcharC
  have hKC : K ≤ C := map_subtype_le _
  have hKSg : K ⊓ Sg = ⊥ := by
    show (CFSG.oddCore C).map C.subtype ⊓ (S : Subgroup C).map C.subtype = ⊥
    rw [← map_inf_eq _ _ C.subtype C.subtype_injective, hinterC, Subgroup.map_bot]
  have hKH : K ⊓ H = ⊥ := by
    rw [eq_bot_iff, ← hKSg]
    intro x hx
    have h1 : x ∈ C ⊓ H := mem_inf.mpr ⟨hKC (mem_inf.mp hx).1, (mem_inf.mp hx).2⟩
    rw [hCH'] at h1
    exact mem_inf.mpr ⟨(mem_inf.mp hx).1, h1⟩
  have hKSgC : (K : Set G) * (Sg : Set G) = C := by
    ext x
    constructor
    · rintro ⟨k, hk, s, hs, rfl⟩
      exact mul_mem (hKC hk) (map_subtype_le _ hs)
    · intro hx
      have h1 : (⟨x, hx⟩ : C) ∈ ((CFSG.oddCore C : Set C) * (S : Set C)) := by
        rw [hprodC]
        exact Set.mem_univ _
      obtain ⟨a, ha, b, hb, hab⟩ := h1
      exact ⟨a, ⟨a, ha, rfl⟩, b, ⟨b, hb, rfl⟩, congrArg Subtype.val hab⟩
  have hKnorm : ∀ m ∈ M, ∀ k ∈ K, m * k * m⁻¹ ∈ K := by
    intro m hm k hk
    obtain ⟨c, hc, rfl⟩ := hk
    have h1 := (characteristic_iff_map_eq.mp hcharC) (conjActOn hCnorm ⟨m, hm⟩)
    have h2 : conjActOn hCnorm ⟨m, hm⟩ c ∈ CFSG.oddCore C := by
      rw [← h1]
      exact ⟨c, hc, rfl⟩
    exact ⟨_, h2, rfl⟩
  have htM : (t : G) ∈ M := hCM t.2
  have hKt : ∀ k ∈ K, (t : G)⁻¹ * k * t ∈ K := fun k hk => by
    have h := hKnorm _ (inv_mem htM) k hk
    rwa [inv_inv] at h
  have htt : (t : G) * t = 1 := by rw [← sq, ← ht2, pow_orderOf_eq_one]
  have htinv : (t : G)⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have hfix : ∀ k ∈ K, (t : G)⁻¹ * k * t = k → k = 1 := fun k hk hkt => by
    have h1 : k ∈ K ⊓ H := mem_inf.mpr ⟨hk, mem_centralizer_singleton_iff.mpr (by
      calc k * t = t * ((t : G)⁻¹ * k * t) := by group
        _ = t * k := by rw [hkt])⟩
    rw [hKH, mem_bot] at h1
    exact h1
  let a : K → K := fun k => ⟨(t : G)⁻¹ * k * t, hKt k k.2⟩
  let f : K → K := fun x => x⁻¹ * a x
  have hfinj : Function.Injective f := by
    intro x y hxy
    have h2 : (x : G)⁻¹ * ((t : G)⁻¹ * x * t) = (y : G)⁻¹ * ((t : G)⁻¹ * y * t) :=
      congrArg Subtype.val hxy
    have h3 : (y : G) * (x : G)⁻¹ * ((t : G)⁻¹ * x * t) = (t : G)⁻¹ * y * t := by
      calc (y : G) * (x : G)⁻¹ * ((t : G)⁻¹ * x * t) =
          y * ((x : G)⁻¹ * ((t : G)⁻¹ * x * t)) := by group
        _ = y * ((y : G)⁻¹ * ((t : G)⁻¹ * y * t)) := by rw [h2]
        _ = (t : G)⁻¹ * y * t := by group
    have h4 : (t : G)⁻¹ * ((y : G) * (x : G)⁻¹) * t = (y : G) * (x : G)⁻¹ := by
      calc (t : G)⁻¹ * ((y : G) * (x : G)⁻¹) * t =
          ((t : G)⁻¹ * y * t) * ((t : G)⁻¹ * x * t)⁻¹ := by group
        _ = (y : G) * (x : G)⁻¹ * ((t : G)⁻¹ * x * t) * ((t : G)⁻¹ * x * t)⁻¹ := by rw [h3]
        _ = (y : G) * (x : G)⁻¹ := by group
    have h5 := hfix _ (mul_mem y.2 (inv_mem x.2)) h4
    exact Subtype.ext (mul_inv_eq_one.mp h5).symm
  have hinv : ∀ k ∈ K, (t : G)⁻¹ * k * t = k⁻¹ := by
    intro k hk
    obtain ⟨x, hx⟩ := Finite.surjective_of_injective hfinj ⟨k, hk⟩
    have hx' : (x : G)⁻¹ * ((t : G)⁻¹ * x * t) = k := congrArg Subtype.val hx
    rw [← hx']
    have htt' : (t : G)⁻¹ * (t : G)⁻¹ = 1 := by rw [htinv, htt]
    calc (t : G)⁻¹ * ((x : G)⁻¹ * ((t : G)⁻¹ * x * t)) * t
        = ((t : G)⁻¹ * (x : G)⁻¹ * t) * (((t : G)⁻¹ * (t : G)⁻¹) * x * (t * t)) := by group
      _ = ((t : G)⁻¹ * (x : G)⁻¹ * t) * x := by rw [htt', htt, one_mul, mul_one]
      _ = ((x : G)⁻¹ * ((t : G)⁻¹ * x * t))⁻¹ := by group
  have hab : ∀ k₁ ∈ K, ∀ k₂ ∈ K, k₁ * k₂ = k₂ * k₁ := by
    intro k₁ hk₁ k₂ hk₂
    have h1 := hinv _ (mul_mem hk₁ hk₂)
    have h2 : (t : G)⁻¹ * (k₁ * k₂) * t = ((t : G)⁻¹ * k₁ * t) * ((t : G)⁻¹ * k₂ * t) := by
      group
    rw [h2, hinv k₁ hk₁, hinv k₂ hk₂, mul_inv_rev] at h1
    have h3 := congrArg (·⁻¹) h1
    simp only [mul_inv_rev, inv_inv] at h3
    exact h3.symm
  have hMKH : ∀ m ∈ M, m ∈ (K : Set G) * (H : Set G) := by
    intro m hm
    let ψ : MulAut C := conjActOn hCnorm ⟨m, hm⟩
    obtain ⟨c, hc⟩ := MulAction.exists_smul_eq C S (ψ • S)
    have h1 : ψ t ∈ ((ψ • S : Sylow 2 C) : Subgroup C) := by
      rw [Sylow.pointwise_smul_def]
      exact smul_mem_pointwise_smul t ψ (S : Subgroup C) htS
    rw [← hc, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at h1
    have hyo : orderOf ((MulAut.conj c)⁻¹ • ψ t) = 2 := by
      rw [MulAut.smul_def, MulEquiv.orderOf_eq, MulEquiv.orderOf_eq, ht]
    have hyt := huniq _ h1 hyo
    have hyG : (c : G)⁻¹ * (m * t * m⁻¹) * c = t := by
      have h2 := congrArg Subtype.val hyt
      rw [MulAut.smul_def, MulAut.inv_def, MulAut.conj_symm_apply] at h2
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h2
      exact h2
    have hcm : (c : G)⁻¹ * m ∈ H := by
      rw [mem_centralizer_singleton_iff]
      calc (c : G)⁻¹ * m * t = ((c : G)⁻¹ * (m * t * m⁻¹) * c) * ((c : G)⁻¹ * m) := by group
        _ = t * ((c : G)⁻¹ * m) := by rw [hyG]
    have hcKS : (c : G) ∈ (K : Set G) * (Sg : Set G) := by rw [hKSgC]; exact c.2
    obtain ⟨k, hk, s, hs, hks⟩ := hcKS
    have hsH : s ∈ H := by
      rw [← hCH'] at hs
      exact (mem_inf.mp hs).2
    refine ⟨k, hk, s * ((c : G)⁻¹ * m), mul_mem hsH hcm, ?_⟩
    have hks' : k * s = c := hks
    calc k * (s * ((c : G)⁻¹ * m)) = (k * s) * (c : G)⁻¹ * m := by group
      _ = m := by rw [hks', mul_inv_cancel, one_mul]
  have hKM : K ≤ M := hKC.trans hCM
  have hKHprod : (K : Set G) * (H : Set G) = M := Set.Subset.antisymm
    (by rintro _ ⟨k, hk, h, hh, rfl⟩; exact mul_mem (hKM hk) (hHM hh)) (fun m hm => hMKH m hm)
  have hKMn : (K.subgroupOf M).Normal := ⟨fun x hx g => by
    rw [mem_subgroupOf] at hx ⊢
    exact hKnorm g g.2 x hx⟩
  have hKodd : Odd (Nat.card K) := by
    rw [show Nat.card K = Nat.card (CFSG.oddCore C) from
      Subgroup.card_map_of_injective C.subtype_injective]
    exact hoddC
  have hoddCore : ∀ (X : Type _) [Group X] [Finite X], Odd (Nat.card (CFSG.oddCore X)) :=
    fun X _ _ => by
      rw [oddCore_eq_pPrimeCore_two, ← Nat.coprime_two_left]
      exact CFSG.pPrimeCore_coprime_card
  have hKle : K ≤ (CFSG.oddCore M).map M.subtype := by
    have hodd' : Odd (Nat.card (K.subgroupOf M)) := by
      rw [Nat.card_congr (subgroupOfEquivOfLe hKM).toEquiv]
      exact hKodd
    have h1 : K.subgroupOf M ≤ CFSG.oddCore M := le_sSup ⟨hKMn, hodd'⟩
    have h2 := map_mono (f := M.subtype) h1
    rwa [subgroupOf_map_subtype, inf_of_le_left hKM] at h2
  have hMcore : K = (CFSG.oddCore M).map M.subtype := by
    refine le_antisymm hKle fun n hn => ?_
    set N := (CFSG.oddCore M).map M.subtype with hN
    obtain ⟨k, hk, h, hh, hkh⟩ := hMKH n (map_subtype_le _ hn)
    have hkh' : k * h = n := hkh
    have hhN : h ∈ N := by
      have h1 := mul_mem (inv_mem (hKle hk)) hn
      rwa [← hkh', inv_mul_cancel_left] at h1
    have hNH : N.subgroupOf H ≤ CFSG.oddCore H := by
      refine le_sSup ⟨⟨fun x hx g => ?_⟩, ?_⟩
      · rw [mem_subgroupOf] at hx ⊢
        obtain ⟨y, hy, hyx⟩ := hx
        refine ⟨⟨g, hHM g.2⟩ * y * (⟨g, hHM g.2⟩ : M)⁻¹,
          (CFSG.oddCore_normal M).conj_mem y hy _, ?_⟩
        simp [← hyx]
      · have h1 : Nat.card (N.subgroupOf H) ∣ Nat.card N := by
          rw [← Subgroup.card_map_of_injective H.subtype_injective, subgroupOf_map_subtype]
          exact Subgroup.card_dvd_of_le inf_le_left
        have h2 : Nat.card N = Nat.card (CFSG.oddCore M) :=
          Subgroup.card_map_of_injective M.subtype_injective
        exact Odd.of_dvd_nat (h2 ▸ hoddCore M) h1
    rw [hcore] at hNH
    have h1 : (⟨h, hh⟩ : H) ∈ N.subgroupOf H := hhN
    have h2 : h = 1 := congrArg Subtype.val (mem_bot.mp (hNH h1))
    rw [← hkh', h2, mul_one]
    exact hk
  have semiM := exists_semidirectProduct_mulEquiv hKM hHM (fun h hh k hk => hKnorm h (hHM hh) k hk)
    hKH hKHprod
  have semiC := exists_semidirectProduct_mulEquiv hKC (map_subtype_le _)
    (fun s hs k hk => hKnorm s (hCM (map_subtype_le _ hs)) k hk) hKSg hKSgC
  have hbij : Function.Bijective ((QuotientGroup.mk' (K.subgroupOf M)).comp (inclusion hHM)) := by
    refine ⟨(injective_iff_map_eq_one _).mpr fun h hh => ?_, fun q => ?_⟩
    · rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
        mem_subgroupOf] at hh
      have h1 : (h : G) ∈ K ⊓ H := mem_inf.mpr ⟨hh, h.2⟩
      rw [hKH, mem_bot] at h1
      exact Subtype.ext h1
    · obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective _ q
      obtain ⟨k, hk, h, hh, hkh⟩ := hMKH m m.2
      have hkh' : k * h = m := hkh
      refine ⟨⟨h, hh⟩, ?_⟩
      rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
        mem_subgroupOf]
      show ((⟨h, hHM hh⟩ : M)⁻¹ * m : M).1 ∈ K
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, ← hkh']
      have h1 := hKnorm _ (inv_mem (hHM hh)) k hk
      rw [inv_inv] at h1
      rwa [show h⁻¹ * (k * h) = h⁻¹ * k * h from by group]
  have hSgC : Sg ≤ C := map_subtype_le _
  have himage : (Sg.subgroupOf M).map (QuotientGroup.mk' (K.subgroupOf M)) =
      (C.subgroupOf M).map (QuotientGroup.mk' (K.subgroupOf M)) := by
    refine le_antisymm (map_mono fun x hx => ?_) ?_
    · rw [mem_subgroupOf] at hx ⊢
      exact hSgC hx
    · rintro _ ⟨x, hx, rfl⟩
      have hxC : (x : G) ∈ C := hx
      have hx' : (x : G) ∈ (K : Set G) * (Sg : Set G) := by rw [hKSgC]; exact hxC
      obtain ⟨k, hk, s, hs, hks⟩ := hx'
      have hks' : k * s = x := hks
      refine ⟨⟨s, hCM (hSgC hs)⟩, hs, ?_⟩
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, mem_subgroupOf]
      show ((⟨s, hCM (hSgC hs)⟩ : M)⁻¹ * x : M).1 ∈ K
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, ← hks']
      have h1 := hKnorm _ (inv_mem (hCM (hSgC hs))) k hk
      rw [inv_inv] at h1
      rwa [show s⁻¹ * (k * s) = s⁻¹ * k * s from by group]
  have hSgH : Sg ≤ H := by
    rw [← hCH']
    exact inf_le_right
  have hSg2 : IsPGroup 2 (Sg.subgroupOf H) :=
    ((S.isPGroup'.map C.subtype)).of_equiv (subgroupOfEquivOfLe hSgH).symm
  obtain ⟨φ, hφ, e, he⟩ := semiM
  have hMcard : Nat.card M = Nat.card K * Nat.card H := by
    rw [← Nat.card_congr e.toEquiv, SemidirectProduct.card]
  have hfac : (Nat.card M).factorization 2 = (Nat.card H).factorization 2 := by
    rw [hMcard, Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne', Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd (fun h => (Nat.not_even_iff_odd.mpr hKodd)
        (even_iff_two_dvd.mpr h)), zero_add]
  refine ⟨hSgne, hCH', hSn', hMcore, hab, hinv, hKH, hKSgC, hKHprod, ⟨φ, hφ, e, he⟩, semiC,
    ⟨hHM, hKMn, QuotientGroup.ker_mk' _, hbij, himage⟩, fun T => ⟨?_, ?_⟩⟩
  · have := hSn'
    have h1 : Sg.subgroupOf H ≤ T := hSg2.le_sylow_of_normal T
    have h2 := map_mono (f := H.subtype) h1
    rwa [subgroupOf_map_subtype, inf_of_le_left hSgH] at h2
  · have hTM : (T : Subgroup H).map H.subtype ≤ M := (map_subtype_le _).trans hHM
    have hcard : Nat.card (((T : Subgroup H).map H.subtype).subgroupOf M) =
        2 ^ (Nat.card M).factorization 2 := by
      rw [Nat.card_congr (subgroupOfEquivOfLe hTM).toEquiv,
        Subgroup.card_map_of_injective H.subtype_injective, Sylow.card_eq_multiplicity, hfac]
    exact ⟨Sylow.ofCard _ hcard, rfl⟩

end CFSG.LocalAnalysis
