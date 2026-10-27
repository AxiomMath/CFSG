module

public import CFSG.Quasithin.H13.NQRigidLocalize
public import CFSG.LocalAnalysis.SteinbergCCCharacteristicPExtension
public import CFSG.RankThree.PGroups.CentralCoprimeKernel
public import CFSG.Quasithin.H13.NQRigidOverlapSylow
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyBasic
public import CFSG.Quasithin.Background.B6Sections
public import CFSG.Quasithin.H13.NQRigidCPUModule

public section

namespace CFSG.Quasithin.H13.NQRigid

open Subgroup CFSG.Open CFSG.Quasithin
open CFSG.Quasithin.BlueprintB2 (centerTorsion mem_centerTorsion_iff)
open CFSG.QuasithinUnique.Setup.Family (IsComp IsBestOffender)
open scoped Pointwise IsMulCommutative

section Centralizer

variable {Γ : Type*} [Group Γ] [Finite Γ]

omit [Finite Γ] in
theorem exists_pow_eq_mul_pow {L₀ : Subgroup Γ} {s : Γ} (hs : s ∈ normalizer (L₀ : Set Γ))
    {l : Γ} (hl : l ∈ L₀) (k : ℕ) : ∃ l' ∈ L₀, (l * s) ^ k = l' * s ^ k := by
  induction k with
  | zero => exact ⟨1, one_mem _, by simp⟩
  | succ k ih =>
    obtain ⟨l', hl', he⟩ := ih
    have hk : s ^ k ∈ normalizer (L₀ : Set Γ) := pow_mem hs k
    refine ⟨l' * (s ^ k * l * (s ^ k)⁻¹), mul_mem hl' ((mem_normalizer_iff.mp hk l).mp hl), ?_⟩
    rw [pow_succ, he, pow_succ]
    group

theorem eq_bot_of_le_centralizer {G₀ L₀ P X : Subgroup Γ}
    (hO2 : ∀ N : Subgroup Γ, N ≤ G₀ → G₀ ≤ normalizer (N : Set Γ) → IsPGroup 2 N → N = ⊥)
    (hGL : G₀ ≤ normalizer (L₀ : Set Γ)) (hP : IsPGroup 2 P) (hPG : P ≤ G₀)
    (hGLP : ∀ g ∈ G₀, ∃ l ∈ L₀, ∃ s ∈ P, g = l * s) (hX : IsPGroup 2 X) (hXG : X ≤ G₀)
    (hXL : X ≤ centralizer (L₀ : Set Γ)) : X = ⊥ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set E := G₀ ⊓ centralizer (L₀ : Set Γ) with hE
  have hconj : ∀ g ∈ G₀, ∀ e ∈ E, g * e * g⁻¹ ∈ E := by
    intro g hg e he
    obtain ⟨heG, heC⟩ := mem_inf.mp he
    refine mem_inf.mpr ⟨mul_mem (mul_mem hg heG) (inv_mem hg), ?_⟩
    rw [mem_centralizer_iff] at heC ⊢
    intro l hl
    have hl' : g⁻¹ * l * g⁻¹⁻¹ ∈ L₀ := (mem_normalizer_iff.mp (hGL (inv_mem hg)) l).mp hl
    have h1 := heC _ hl'
    calc l * (g * e * g⁻¹) = g * ((g⁻¹ * l * g⁻¹⁻¹) * e) * g⁻¹ := by group
      _ = g * (e * (g⁻¹ * l * g⁻¹⁻¹)) * g⁻¹ := by rw [h1]
      _ = g * e * g⁻¹ * l := by group
  have hGE : G₀ ≤ normalizer (E : Set Γ) := by
    intro g hg
    rw [mem_normalizer_iff]
    intro e
    refine ⟨hconj g hg e, fun h => ?_⟩
    have h1 := hconj g⁻¹ (inv_mem hg) _ h
    simpa [mul_assoc] using h1
  set N : Subgroup ↥E := L₀.subgroupOf E with hN
  have hNZ : N ≤ center ↥E := by
    intro z hz
    rw [mem_center_iff]
    intro e
    apply Subtype.ext
    have hz' : (z : Γ) ∈ L₀ := hz
    exact ((mem_centralizer_iff.mp e.2.2) z hz').symm
  have hNn : N.Normal := normal_of_le_center hNZ
  have hEN : IsPGroup 2 (↥E ⧸ N) := by
    intro q
    obtain ⟨e, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨l, hl, s, hs, hls⟩ := hGLP e e.2.1
    obtain ⟨n, hn⟩ := hP ⟨s, hs⟩
    refine ⟨n, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    show ((e ^ 2 ^ n : ↥E) : Γ) ∈ L₀
    have hsn : s ^ 2 ^ n = 1 := by
      have := congrArg Subtype.val hn
      simpa using this
    obtain ⟨l', hl', he⟩ := exists_pow_eq_mul_pow (hGL (hPG hs)) hl (2 ^ n)
    rw [SubgroupClass.coe_pow, hls, he, hsn, mul_one]
    exact hl'
  obtain ⟨Q⟩ : Nonempty (Sylow 2 ↥E) := inferInstance
  obtain ⟨hQn, -, hQall⟩ :=
    CFSG.RankThree.PGroups.sylow_normal_of_le_center_of_isPGroup_quotient Nat.prime_two hNZ hEN Q
  have hQc : (Q : Subgroup ↥E).Characteristic := Sylow.characteristic_of_normal Q hQn
  have hQG : G₀ ≤ normalizer ((((Q : Subgroup ↥E).map E.subtype : Subgroup Γ)) : Set Γ) := by
    intro g hg
    rw [mem_normalizer_iff]
    intro x
    refine ⟨fun hx => CFSG.LyonsUnitaryFour.conj_mem_map_of_characteristic (hGE hg) hx,
      fun hx => ?_⟩
    have h1 := CFSG.LyonsUnitaryFour.conj_mem_map_of_characteristic (hGE (inv_mem hg)) hx
    simpa [mul_assoc] using h1
  have hQ0 := hO2 _ ((map_subtype_le _).trans inf_le_left) hQG (Q.isPGroup'.map _)
  rw [eq_bot_iff]
  intro x hx
  have hxE : x ∈ E := ⟨hXG hx, hXL hx⟩
  obtain ⟨k, hk⟩ := hX ⟨x, hx⟩
  have hxk : (⟨x, hxE⟩ : ↥E) ^ 2 ^ k = 1 := Subtype.ext (by
    have := congrArg Subtype.val hk
    simpa using this)
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hxk)
  have hxQ := hQall ⟨x, hxE⟩ ⟨j, hj⟩
  have h1 : x ∈ (Q : Subgroup ↥E).map E.subtype := ⟨_, hxQ, rfl⟩
  rw [hQ0] at h1
  exact h1

end Centralizer

section Main

variable {H : Type} [Group H] [Finite H]

omit [Finite H] in
theorem characteristic_map_of_mulEquiv {A A' : Type*} [Group A] [Group A'] (e : A ≃* A')
    {D : Subgroup A} (hD : D.Characteristic) : (D.map e.toMonoidHom).Characteristic := by
  refine characteristic_iff_map_eq.mpr fun σ => ?_
  have h1 := characteristic_iff_map_eq.mp hD ((e.trans σ).trans e.symm)
  calc (D.map e.toMonoidHom).map σ.toMonoidHom
      = (D.map ((e.trans σ).trans e.symm).toMonoidHom).map e.toMonoidHom := by
        rw [map_map, map_map]
        congr 1
        ext x
        simp
    _ = D.map e.toMonoidHom := by rw [h1]

theorem cpu_component_offender {R K M : Subgroup H}
    (hR2 : IsPGroup 2 R)
    (hRpush : R = (CFSG.pCore 2 ↥(normalizer (R : Set H))).map (normalizer (R : Set H)).subtype)
    (hK : CFSG.IsCComponent K) (hF : CFSG.generalizedFitting ↥K = CFSG.pCore 2 ↥K)
    (hKq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K)) (hRK : R ≤ normalizer (K : Set H))
    (hKM : ¬ K ≤ M)
    (hRchar : ∀ D : Subgroup ↥R, D.Characteristic → D ≠ ⊥ →
      normalizer ((D.map R.subtype : Subgroup H) : Set H) ≤ M) :
    ∃ (V : Type) (_ : CommGroup V) (_ : Finite V), (∀ v : V, v * v = 1) ∧
      ∃ G₀ L₀ B : Subgroup (MulAut V), IsComp L₀ G₀ ∧ IsBestOffender G₀ B ∧ ⁅L₀, B⁆ ≠ ⊥ ∧
        Nonempty (↥L₀ ⧸ center ↥L₀ ≃*
          (↥K ⧸ CFSG.pCore 2 ↥K) ⧸ center (↥K ⧸ CFSG.pCore 2 ↥K)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set B := K ⊔ R with hB
  have hKB : K ≤ B := le_sup_left
  have hRB : R ≤ B := le_sup_right
  have hBK : B ≤ normalizer (K : Set H) := sup_le le_normalizer hRK
  have hKR : ((K ⊔ R : Subgroup H) : Set H) = (K : Set H) * (R : Set H) :=
    coe_mul_of_right_le_normalizer_left K R hRK
  set L := K.subgroupOf B with hL
  set S := R.subgroupOf B with hS
  have hLn : L.Normal := (normal_subgroupOf_iff_le_normalizer hKB).mpr hBK
  have hS2 : IsPGroup 2 S := hR2.comap_subtype
  have hBkr : ∀ x : ↥B, ∃ k ∈ L, ∃ r ∈ S, x = k * r := by
    intro x
    have hx : (x : H) ∈ ((K ⊔ R : Subgroup H) : Set H) := x.2
    rw [hKR] at hx
    obtain ⟨k, hk, r, hr, hkr⟩ := hx
    exact ⟨⟨k, hKB hk⟩, hk, ⟨r, hRB hr⟩, hr, Subtype.ext hkr.symm⟩
  have hKc : CFSG.IsCharacteristicP 2 ↥K :=
    (CFSG.isCharacteristicP_iff_generalizedFitting_eq_pCore ↥K 2).mpr hF
  let eL : ↥L ≃* ↥K := subgroupOfEquivOfLe hKB
  have hLc : CFSG.IsCharacteristicP 2 ↥L :=
    CFSG.LocalAnalysis.ComponentInitial.isCharacteristicP_of_mulEquiv eL.symm hKc
  have hBL : IsPGroup 2 (↥B ⧸ L) := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨k, hk, r, hr, rfl⟩ := hBkr x
    obtain ⟨n, hn⟩ := hS2 ⟨r, hr⟩
    refine ⟨n, ?_⟩
    have e2 : ((k : ↥B) : ↥B ⧸ L) = 1 := (QuotientGroup.eq_one_iff _).mpr hk
    have e3 : r ^ 2 ^ n = 1 := by
      have := congrArg Subtype.val hn
      simpa using this
    rw [QuotientGroup.mk_mul, e2, one_mul, ← QuotientGroup.mk_pow, e3, QuotientGroup.mk_one]
  have hchar : CFSG.IsCharacteristicP 2 ↥B :=
    CFSG.LocalAnalysis.characteristic_p_normal_p_extension hLc hBL
  have hSO : R = pCoreOf 2 (normalizer (R : Set H)) := by
    rw [pCoreOf]
    exact hRpush
  obtain ⟨-, -, -, hloc⟩ :=
    prime_radical_normalizers_localize_to_actual_Ccomponents Nat.prime_two hR2 hSO hK hKq
  rw [inf_eq_left.mpr hRK] at hloc
  have hpc : ∀ X : Subgroup ↥B, (pCoreOf 2 X).map B.subtype = pCoreOf 2 (X.map B.subtype) := by
    intro X
    rw [← NQBlock.map_inSubgroup_pCore]
    unfold inSubgroup pCoreOf
    try with_reducible rfl
  have hSmap : S.map B.subtype = R := by
    rw [hS, subgroupOf_map_subtype, inf_eq_left.mpr hRB]
  have hSO' : S = pCoreOf 2 (normalizer (S : Set ↥B)) := by
    apply map_injective B.subtype_injective
    rw [hpc, hSmap, hS, ← subgroupOf_normalizer_eq hRB, subgroupOf_map_subtype, inf_comm]
    exact hloc
  have hQS : CFSG.pCore 2 ↥B ≤ S :=
    NQTerm.le_of_isPGroup_of_le_normalizer hS2 hSO' CFSG.pCore_isPGroup (by
      rw [normalizer_eq_top_iff.mpr CFSG.pCore_normal]
      exact le_top)
  have hLQ : (CFSG.pCore 2 ↥B).subgroupOf L = CFSG.pCore 2 ↥L := by
    apply le_antisymm
    · refine SteinbergCC.le_pCore_of_normal_of_isPGroup ?_ CFSG.pCore_isPGroup.comap_subtype
      exact (CFSG.pCore_normal (p := 2) (G := ↥B)).subgroupOf L
    · intro x hx
      rw [mem_subgroupOf]
      exact CFSG.LyonsUnitaryFour.map_pCore_le_pCore_of_isSubnormal hLn.isSubnormal ⟨x, hx, rfl⟩
  have hLq : CFSG.IsQuasisimple (↥L ⧸ (CFSG.pCore 2 ↥B).subgroupOf L) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv
      ((QuotientGroup.quotientMulEquivOfEq hLQ).trans
        (QuotientGroup.congr _ _ eL (CFSG.LieType.SteinbergBR.pCore_map_equiv 2 eL))).symm hKq
  have hLM : ¬ L ≤ M.subgroupOf B := fun hle => hKM fun k hk =>
    mem_subgroupOf.mp (hle (show (⟨k, hKB hk⟩ : ↥B) ∈ L from hk))
  have hM : ∀ D : Subgroup ↥S, D.Characteristic → D ≠ ⊥ →
      normalizer ((D.map S.subtype : Subgroup ↥B) : Set ↥B) ≤ M.subgroupOf B := by
    intro D hDc hD1 x hx
    let eS : ↥S ≃* ↥R := subgroupOfEquivOfLe hRB
    have hD'c := characteristic_map_of_mulEquiv eS hDc
    have hD'1 : D.map eS.toMonoidHom ≠ ⊥ := by
      intro h0
      apply hD1
      rw [eq_bot_iff]
      intro d hd
      have h1 : eS d ∈ D.map eS.toMonoidHom := ⟨d, hd, rfl⟩
      rw [h0, mem_bot] at h1
      rw [mem_bot]
      exact eS.injective (h1.trans (map_one eS).symm)
    have himg : (D.map S.subtype).map B.subtype = (D.map eS.toMonoidHom).map R.subtype := by
      rw [map_map, map_map]
      rfl
    have h1 := coe_mem_normalizer_map hx
    rw [himg] at h1
    exact mem_subgroupOf.mpr (hRchar _ hD'c hD'1 h1)
  have hLS : (L : Set ↥B) * (S : Set ↥B) = Set.univ := by
    refine Set.eq_univ_of_forall fun x => ?_
    obtain ⟨k, hk, r, hr, rfl⟩ := hBkr x
    exact ⟨k, hk, r, hr, rfl⟩
  set V : Subgroup ↥B := centerTorsion 2 (CFSG.pCore 2 ↥B) with hV
  have hVn : V.Normal := CFSG.QuasithinUnique.Setup.normal_centerTorsion_pCore 2
  set ρ : ↥B →* MulAut ↥V := MulAut.conjNormal with hρ
  have hρapp : ∀ (g : ↥B) (v : ↥V), ((ρ g v : ↥V) : ↥B) = g * v * g⁻¹ :=
    fun g v => MulAut.conjNormal_apply g v
  obtain ⟨hred, -, hQC, hCZ, -, -, -, -, A, -, hAne, hAel, hAbest⟩ :=
    NQBlock.characteristic_normalizer_control_produces_central_core_best_offender hchar hS2 hQS
      hLn hLS hLq hLM hM hV ρ hρapp
  obtain ⟨hVn', hVe, hVO⟩ := hred
  have : IsMulCommutative ↥V := hVe.toIsMulCommutative
  have hVv : ∀ v : ↥V, v * v = 1 := by
    intro v
    rw [← pow_two]
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hVe.exponent_dvd_p v
  have hkerρ : ∀ g : ↥B, ρ g = 1 ↔ g ∈ centralizer (V : Set ↥B) := by
    intro g
    rw [mem_centralizer_iff]
    constructor
    · intro h v hv
      have h1 := congrArg (fun φ : MulAut ↥V => ((φ ⟨v, hv⟩ : ↥V) : ↥B)) h
      simp only [MulAut.one_apply, hρapp] at h1
      calc v * g = g * v * g⁻¹ * g := by rw [h1]
        _ = g * v := by group
    · intro h
      refine MulEquiv.ext fun v => Subtype.ext ?_
      rw [hρapp, MulAut.one_apply, ← h v v.2, mul_inv_cancel_right]
  set G₀ := ρ.range with hG₀
  set L₀ := L.map ρ with hL₀
  set P₀ := S.map ρ with hP₀
  have hO2 : ∀ N : Subgroup (MulAut ↥V), N ≤ G₀ → G₀ ≤ normalizer (N : Set (MulAut ↥V)) →
      IsPGroup 2 N → N = ⊥ := by
    intro N hNG hGN hN2
    set N' : Subgroup ↥B := N.comap ρ with hN'
    have hN'n : N'.Normal := by
      refine ⟨fun x hx b => ?_⟩
      show ρ (b * x * b⁻¹) ∈ N
      rw [map_mul, map_mul, map_inv]
      exact (mem_normalizer_iff.mp (hGN ⟨b, rfl⟩) (ρ x)).mp hx
    set N'' : Subgroup (↥B ⧸ centralizer (V : Set ↥B)) := N'.map (QuotientGroup.mk' _)
    have hN''n : N''.Normal := hN'n.map _ (QuotientGroup.mk'_surjective _)
    have hN''2 : IsPGroup 2 N'' := by
      rintro ⟨_, ⟨x, hx, rfl⟩⟩
      obtain ⟨n, hn⟩ := hN2 ⟨ρ x, hx⟩
      refine ⟨n, Subtype.ext ?_⟩
      have h1 : ρ (x ^ 2 ^ n) = 1 := by
        rw [map_pow]
        have := congrArg Subtype.val hn
        simpa using this
      rw [SubgroupClass.coe_pow, OneMemClass.coe_one, ← map_pow, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff]
      exact (hkerρ _).mp h1
    have hle : N'' ≤ CFSG.pCore 2 (↥B ⧸ centralizer (V : Set ↥B)) :=
      SteinbergCC.le_pCore_of_normal_of_isPGroup hN''n hN''2
    rw [hVO, le_bot_iff] at hle
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨x, rfl⟩ := hNG hy
    have hx : x ∈ N' := hy
    have h1 : QuotientGroup.mk' (centralizer (V : Set ↥B)) x ∈ N'' := mem_map_of_mem _ hx
    rw [hle, mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact (mem_bot).mpr ((hkerρ x).mpr h1)
  have hGL : G₀ ≤ normalizer (L₀ : Set (MulAut ↥V)) := by
    rintro _ ⟨b, rfl⟩
    exact le_normalizer_map ρ ⟨b, normalizer_eq_top_iff.mpr hLn ▸ mem_top b, rfl⟩
  have hLG : L₀ ≤ G₀ := map_le_range ρ L
  have hPG : P₀ ≤ G₀ := map_le_range ρ S
  have hP₀2 : IsPGroup 2 P₀ := hS2.map ρ
  have hGLP : ∀ g ∈ G₀, ∃ l ∈ L₀, ∃ s ∈ P₀, g = l * s := by
    rintro _ ⟨b, rfl⟩
    obtain ⟨k, hk, r, hr, rfl⟩ := hBkr b
    exact ⟨ρ k, mem_map_of_mem ρ hk, ρ r, mem_map_of_mem ρ hr, map_mul ρ k r⟩
  set ψ₀ : ↥L →* ↥L₀ := ρ.subgroupMap L with hψ₀
  have hψ₀s : Function.Surjective ψ₀ := ρ.subgroupMap_surjective L
  have hpL : CFSG.pCore 2 ↥L ≤ ψ₀.ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    show ρ (x : ↥B) = 1
    rw [hkerρ]
    apply hQC
    rw [← hLQ] at hx
    exact hx
  set ψ : (↥L ⧸ CFSG.pCore 2 ↥L) →* ↥L₀ := QuotientGroup.lift (CFSG.pCore 2 ↥L) ψ₀ hpL
    with hψ
  have hψs : Function.Surjective ψ := by
    intro y
    obtain ⟨x, rfl⟩ := hψ₀s y
    exact ⟨x, rfl⟩
  set Lb := L.map (QuotientGroup.mk' (CFSG.pCore 2 ↥B)) with hLb
  set θ : (↥L ⧸ CFSG.pCore 2 ↥L) ≃* ↥Lb :=
    (QuotientGroup.quotientMulEquivOfEq (by
      rw [← hLQ]
      ext x
      rw [MonoidHom.mem_ker, mem_subgroupOf]
      constructor
      · intro h
        apply Subtype.ext
        show QuotientGroup.mk' (CFSG.pCore 2 ↥B) (x : ↥B) = 1
        rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
        exact h
      · intro h
        have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥B) (x : ↥B) = 1 := congrArg Subtype.val h
        rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1)).trans
      (QuotientGroup.quotientKerEquivOfSurjective _
        ((QuotientGroup.mk' (CFSG.pCore 2 ↥B)).subgroupMap_surjective L)) with hθ
  have hθmk : ∀ x : ↥L, ((θ (x : ↥L ⧸ CFSG.pCore 2 ↥L) : ↥Lb) : ↥B ⧸ CFSG.pCore 2 ↥B) =
      QuotientGroup.mk' (CFSG.pCore 2 ↥B) x := fun _ => rfl
  have hJ'q : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (QuotientGroup.quotientMulEquivOfEq hLQ) hLq
  have hψker : ψ.ker ≤ center (↥L ⧸ CFSG.pCore 2 ↥L) := by
    intro y hy
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    have hx1 : ρ (x : ↥B) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hy)
    have hxC := (hkerρ _).mp hx1
    have h1 := hCZ (mem_map_of_mem (QuotientGroup.mk' (CFSG.pCore 2 ↥B)) hxC)
    obtain ⟨z, hz, hzx⟩ := h1
    have hzθ : z = θ (x : ↥L ⧸ CFSG.pCore 2 ↥L) := Subtype.ext (by rw [hθmk]; exact hzx)
    rw [hzθ, SetLike.mem_coe, mem_center_iff] at hz
    rw [mem_center_iff]
    intro g
    apply θ.injective
    rw [map_mul, map_mul]
    exact hz (θ g)
  have hL₀q : CFSG.IsQuasisimple ↥L₀ :=
    CFSG.LocalCores.isQuasisimple_of_surjective hJ'q ψ hψs hψker
  let eJ : (↥L ⧸ CFSG.pCore 2 ↥L) ≃* (↥K ⧸ CFSG.pCore 2 ↥K) :=
    QuotientGroup.congr _ _ eL (CFSG.LieType.SteinbergBR.pCore_map_equiv 2 eL)
  have hiso : Nonempty (↥L₀ ⧸ center ↥L₀ ≃*
      (↥K ⧸ CFSG.pCore 2 ↥K) ⧸ center (↥K ⧸ CFSG.pCore 2 ↥K)) :=
    ⟨(centerQuotEquivOfSurjective hJ'q.1 ψ hψs hψker).symm.trans (centerQuotEquivOfMulEquiv eJ)⟩
  have hcomp : IsComp L₀ G₀ := by
    refine ⟨hLG, CFSG.Open.IsSubnormal.step hLG
      ((normal_subgroupOf_iff_le_normalizer hLG).mpr hGL) (CFSG.Open.IsSubnormal.refl G₀), ?_⟩
    exact (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_open _).mp
      ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mpr hL₀q)
  set B₀ := (A.map S.subtype).map ρ with hB₀
  have hB₀G : B₀ ≤ G₀ := map_le_range ρ _
  have hB₀2 : IsPGroup 2 B₀ := (hS2.to_le (map_subtype_le A)).map ρ
  set w : Subgroup (MulAut ↥V) → ℕ := fun X => Nat.card X * Nat.card (fixV X) with hw
  have hwfix : ∀ X : Subgroup (MulAut ↥V),
      Nat.card X * Nat.card {v : ↥V // ∀ d ∈ X, d v = v} = w X := fun X => rfl
  have hbest : ∀ X ≤ B₀, w X ≤ w B₀ := fun X hX => by
    rw [← hwfix, ← hwfix]
    exact hAbest X hX
  have hex : ∃ n, ∃ X : Subgroup (MulAut ↥V), X ≤ B₀ ∧ X ≠ ⊥ ∧ w X = w B₀ ∧ Nat.card X = n :=
    ⟨_, B₀, le_rfl, hAne, rfl, rfl⟩
  obtain ⟨X, hXB₀, hX1, hXw, hXn⟩ := Nat.find_spec hex
  have hXmin : ∀ Y : Subgroup (MulAut ↥V), Y ≤ B₀ → Y ≠ ⊥ → w Y = w B₀ →
      Nat.find hex ≤ Nat.card Y := fun Y hY1 hY2 hY3 => Nat.find_min' hex ⟨Y, hY1, hY2, hY3, rfl⟩
  have hXbest : IsBestOffender G₀ X := by
    refine ⟨hXB₀.trans hB₀G, hX1, ⟨fun a ha b hb => ?_, fun a ha => ?_⟩, ?_, ?_⟩
    · exact congrArg Subtype.val (hAel.toIsMulCommutative.is_comm.comm ⟨a, hXB₀ ha⟩ ⟨b, hXB₀ hb⟩)
    · have h1 := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hAel.exponent_dvd_p ⟨a, hXB₀ ha⟩
      exact congrArg Subtype.val h1
    · have h1 := hbest ⊥ bot_le
      rw [← hXw] at h1
      have h2 : w ⊥ = Nat.card ↥V := by
        rw [hw]
        simp only [card_bot, one_mul]
        exact Nat.card_congr ((Equiv.subtypeUnivEquiv fun v => by
          intro x hx
          rw [mem_bot] at hx
          rw [hx, MulAut.one_apply]))
      rw [h2] at h1
      exact h1
    · intro Y hYX hY1 hYX'
      have hYw : w Y ≤ w X := hXw ▸ hbest Y (hYX.trans hXB₀)
      refine lt_of_le_of_ne hYw fun heq => ?_
      have h1 := hXmin Y (hYX.trans hXB₀) hY1 (heq.trans hXw)
      rw [← hXn] at h1
      have h2 : Nat.card Y < Nat.card X :=
        card_lt_of_lt (lt_of_le_of_ne hYX hYX')
      omega
  have hLX : ⁅L₀, X⁆ ≠ ⊥ := by
    intro h0
    apply hX1
    refine eq_bot_of_le_centralizer hO2 hGL hP₀2 hPG hGLP (hB₀2.to_le hXB₀)
      (hXB₀.trans hB₀G) ?_
    rw [commutator_comm, commutator_eq_bot_iff_le_centralizer] at h0
    exact h0
  exact ⟨↥V, inferInstance, inferInstance, hVv, G₀, L₀, X, hcomp, hXbest, hLX, hiso⟩

end Main

end CFSG.Quasithin.H13.NQRigid
