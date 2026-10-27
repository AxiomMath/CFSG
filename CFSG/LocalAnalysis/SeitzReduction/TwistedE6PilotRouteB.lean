module

public import CFSG.LocalAnalysis.SeitzReduction.E6PilotCentralizerZLeviStab
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotCatAlt
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotCatAlt
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotInnerActionOuter
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPositionTransport
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotPerfectV

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.TwistedE6Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.EvenSmallLie
  CFSG.LieType.Steinberg.Adjoint
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.Quasithin (perfectCore perfectCore_le)

section Weyl

@[expose] def vWord : List ℕ := [0, 3, 2, 0, 4, 3, 2, 0, 5, 4, 3, 1, 2, 0, 3, 2, 4]

@[expose] def vFrame : List (Fin Tag.E6.rank → ℤ) := vReprRoots

@[expose] def vPos : List ℕ := [48, 52, 66]

theorem vPos_map : vPos.map Tag.E6.rootCertificate.root = vFrame := by
  apply List.map_injective_iff.2 List.ofFn_injective
  decide +kernel

theorem vPos_lt : ∀ k ∈ vPos, k < Tag.E6.rootCertificate.roots.length := by
  decide +kernel

theorem vWord_wordPos : vPos.map (wordPos Tag.E6.rootCertificate vWord) = E6Pilot.e6RepPos 2 := by
  decide +kernel


theorem vWeyl_smul_vReprRoots :
    vFrame.map (weylOfWord .E6 vWord • ·) = E6Pilot.e6RepFrame 2 := by
  rw [← vPos_map, ← E6Pilot.e6RepPos_map, ← vWord_wordPos, List.map_map, List.map_map]
  refine List.map_congr_left fun k hk => ?_
  exact (wordPos_spec (Tag.rootCertificate_check .E6) vWord (vPos_lt k hk)).2.symm

end Weyl


section Conj

variable (K : Type) [Field K]

@[expose] noncomputable def vConj : adjointGroup .E6 K :=
  (E6Pilot.e6RepConj K 2)⁻¹ *
    ⟨canonicalRep (coxeterSystem .E6) K (weylOfWord .E6 vWord), canonicalRep_mem_adjointGroup _ K _⟩

@[expose] noncomputable def vE6 : ModGL .E6 K := twistedE6ClassV K

variable {K}

theorem vE6_eq_list_prod : vE6 K = (vFrame.map fun α => pinnedX .E6 K α 1).prod :=
  twistedE6ClassV_eq_list_prod

theorem canonicalRep_vWord_mul_classV_mul_inv [CharP K 2] :
    canonicalRep (coxeterSystem .E6) K (weylOfWord .E6 vWord) * vE6 K *
        (canonicalRep (coxeterSystem .E6) K (weylOfWord .E6 vWord))⁻¹ =
      (E6Pilot.e6Rep K 2 : ModGL .E6 K) := by
  have hR : ∀ α ∈ vFrame, IsRoot .E6 α := by
    intro α hα
    obtain ⟨-, -, hA, hA', hB⟩ := isRoot_twistedE6ClassRoots
    unfold vFrame vReprRoots at hα
    rcases List.mem_cons.1 hα with rfl | hα
    · exact hA
    rcases List.mem_cons.1 hα with rfl | hα
    · exact hA'
    rcases List.mem_cons.1 hα with rfl | hα
    · exact hB
    exact absurd hα List.not_mem_nil
  rw [E6Pilot.coe_e6Rep, vE6_eq_list_prod]
  change canonicalRep (coxeterSystem .E6) K (weylOfWord .E6 vWord) *
      (vFrame.map fun α => pinnedX .E6 K α ((fun _ => (1 : K)) α)).prod *
        (canonicalRep (coxeterSystem .E6) K (weylOfWord .E6 vWord))⁻¹ = _
  rw [E6Pilot.canonicalRep_mul_list_prod_mul_inv_of_charTwo (weylOfWord .E6 vWord) hR,
    ← vWeyl_smul_vReprRoots, List.map_map]
  rfl

theorem vConj_mul_classV_mul_inv [CharP K 2] :
    (vConj K : ModGL .E6 K) * vE6 K * (vConj K : ModGL .E6 K)⁻¹ = E6Pilot.zAS K := by
  have h1 := canonicalRep_vWord_mul_classV_mul_inv (K := K)
  have h2 := congrArg (fun x : adjointGroup .E6 K => (x : ModGL .E6 K))
    (E6Pilot.e6RepConj_mul_e6ASRep_mul_inv (K := K) 2)
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h2
  rw [← E6Pilot.coe_e6ASRep_two]
  have h3 : (E6Pilot.e6ASRep K 2 : ModGL .E6 K) =
      (E6Pilot.e6RepConj K 2 : ModGL .E6 K)⁻¹ * (E6Pilot.e6Rep K 2 : ModGL .E6 K) *
        (E6Pilot.e6RepConj K 2 : ModGL .E6 K) := by
    rw [← h2]
    group
  rw [h3, ← h1, vConj]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  change _ = _ * (canonicalRep (coxeterSystem .E6) K (weylOfWord .E6 vWord) * vE6 K *
    (canonicalRep (coxeterSystem .E6) K (weylOfWord .E6 vWord))⁻¹) * _
  group

end Conj

section TypeFree

theorem card_dvd_card_of_le_sup_of_forall_normal {G : Type*} [Group G] [Finite G]
    {Q M S : Subgroup G} (hQ : IsPGroup 2 Q) (hMN : M ≤ normalizer (Q : Set G))
    (hQM : Disjoint Q M) (hS : S ≤ Q ⊔ M)
    (hO2 : ∀ N : Subgroup S, N.Normal → IsPGroup 2 N → N = ⊥) :
    Nat.card S ∣ Nat.card M := by
  have hQN : Q ⊔ M ≤ normalizer (Q : Set G) := sup_le le_normalizer hMN
  have hSN : S ≤ normalizer (Q : Set G) := hS.trans hQN
  have hnormal : (Q.subgroupOf S).Normal := by
    rw [normal_subgroupOf_iff_le_normalizer_inf]
    exact (le_inf hSN le_normalizer).trans inf_normalizer_le_normalizer_inf
  have hbot := hO2 _ hnormal (hQ.comap_of_injective S.subtype S.subtype_injective)
  have hdisj : Disjoint Q S := Subgroup.subgroupOf_eq_bot.1 hbot
  have h3 : Nat.card (Q ⊔ S : Subgroup G) ∣ Nat.card (Q ⊔ M : Subgroup G) :=
    card_dvd_of_le (sup_le le_sup_left hS)
  rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer Q S hSN hdisj,
    CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer Q M hMN hQM] at h3
  exact Nat.dvd_of_mul_dvd_mul_left Nat.card_pos h3

end TypeFree

section Orders

theorem factorization_card_SL_two_pow {K : Type} [Field K] [Finite K] {n m : ℕ} (hn : 1 ≤ n)
    (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ n) :
    (Nat.card (Matrix.SpecialLinearGroup (Fin m) K)).factorization 2 = n * (m * (m - 1) / 2) := by
  rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq hm, hK]
  have hodd : Odd (∏ j ∈ Finset.Icc 2 m, ((2 ^ n) ^ j - 1)) :=
    Finset.prod_induction _ (fun x => Odd x) (fun a b ha hb => ha.mul hb) odd_one
      fun j hj => E6Pilot.odd_two_pow_pow_sub_one (by omega)
        (by simp only [Finset.mem_Icc] at hj; omega)
  rw [E6Pilot.factorization_two_mul_odd (by positivity) hodd, ← pow_mul,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same]

variable {K : Type} [Field K]

theorem factorization_card_zJ_sup_zS_le [Finite K] [CharP K 2] {n : ℕ}
    (hK : Nat.card K = 2 ^ n) :
    (Nat.card (E6Pilot.zJ K ⊔ E6Pilot.zS K : Subgroup (ModGL .E6 K))).factorization 2 ≤ 4 * n := by
  have : Finite (ModGL .E6 K) := finite_modGL
  have hn : 1 ≤ n := by
    by_contra h
    have h0 : n = 0 := by omega
    have := Finite.one_lt_card (α := K)
    rw [hK, h0, pow_zero] at this
    exact absurd this (lt_irrefl 1)
  have hdisj : Disjoint (E6Pilot.zJ K) (E6Pilot.zS K) := disjoint_iff.2 E6Pilot.zJ_inf_zS_eq_bot
  have hnorm : E6Pilot.zS K ≤ normalizer (E6Pilot.zJ K : Set (ModGL .E6 K)) :=
    E6Pilot.zS_le_centralizer_zJ.trans (centralizer_le_normalizer _)
  have hJ : Nat.card (E6Pilot.zJ K) = Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) :=
    Nat.card_congr (E6Pilot.zJEquiv (K := K)).symm.toEquiv
  have hS : Nat.card (E6Pilot.zS K) ∣ Nat.card (Matrix.SpecialLinearGroup (Fin 3) K) := by
    rw [← E6Pilot.map_range_zSL3Hom, card_map_of_injective (adjointGroup .E6 K).subtype_injective]
    exact Subgroup.card_range_dvd _
  have hJ0 : Nat.card (E6Pilot.zJ K) ≠ 0 := Nat.card_pos.ne'
  have hS0 : Nat.card (E6Pilot.zS K) ≠ 0 := Nat.card_pos.ne'
  have hSL0 : Nat.card (Matrix.SpecialLinearGroup (Fin 3) K) ≠ 0 := Nat.card_pos.ne'
  have h3 := (Nat.factorization_le_iff_dvd hS0 hSL0).2 hS 2
  rw [factorization_card_SL_two_pow hn (by norm_num) hK] at h3
  rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hnorm hdisj,
    Nat.factorization_mul hJ0 hS0, Finsupp.add_apply, hJ,
    factorization_card_SL_two_pow hn (by norm_num) hK]
  norm_num at h3 ⊢
  omega

theorem factorization_card_le_of_le_centralizer_zAS [Finite K] [CharP K 2] {n : ℕ}
    (hK : Nat.card K = 2 ^ n) {S : Subgroup (ModGL .E6 K)}
    (hS : S ≤ centralizer ({E6Pilot.zAS K} : Set (ModGL .E6 K)) ⊓ adjointGroup .E6 K)
    (hO2 : ∀ N : Subgroup S, N.Normal → IsPGroup 2 N → N = ⊥) :
    (Nat.card S).factorization 2 ≤ 4 * n := by
  have : Finite (ModGL .E6 K) := finite_modGL
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hQp, -⟩ :=
    (parabolic_root_radical_Levi_factors .E6 K E6Pilot.zNodes).2.2.2.2.2.2.2.2.2.2.2.2 2
  have hQ : IsPGroup 2 (parabolicRadical .E6 K E6Pilot.zNodes ⊓
      centralizer ({E6Pilot.zAS K} : Set (ModGL .E6 K)) : Subgroup (ModGL .E6 K)) :=
    hQp.to_le inf_le_left
  have hdvd := card_dvd_card_of_le_sup_of_forall_normal hQ
    E6Pilot.levi_inf_le_normalizer_radical_inf (disjoint_iff.2 E6Pilot.radical_inf_inf_levi_inf)
    (hS.trans E6Pilot.centralizer_zAS_inf_eq.le) hO2
  rw [E6Pilot.levi_inf_centralizer_zAS_eq] at hdvd
  calc (Nat.card S).factorization 2
      ≤ (Nat.card (E6Pilot.zJ K ⊔ E6Pilot.zS K : Subgroup (ModGL .E6 K))).factorization 2 :=
        (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').2 hdvd 2
    _ ≤ 4 * n := factorization_card_zJ_sup_zS_le hK

theorem factorization_card_le_of_le_centralizer_vE6 [Finite K] [CharP K 2] {n : ℕ}
    (hK : Nat.card K = 2 ^ n) {S : Subgroup (ModGL .E6 K)}
    (hS : S ≤ centralizer ({vE6 K} : Set (ModGL .E6 K)) ⊓ adjointGroup .E6 K)
    (hO2 : ∀ N : Subgroup S, N.Normal → IsPGroup 2 N → N = ⊥) :
    (Nat.card S).factorization 2 ≤ 4 * n := by
  set m : ModGL .E6 K := (vConj K : ModGL .E6 K) with hm
  have hmA : m ∈ adjointGroup .E6 K := (vConj K).2
  set S' := S.map (MulAut.conj m).toMonoidHom with hS'
  have eS : S ≃* S' := S.equivMapOfInjective _ (MulAut.conj m).injective
  have hS'le : S' ≤ centralizer ({E6Pilot.zAS K} : Set (ModGL .E6 K)) ⊓ adjointGroup .E6 K := by
    rintro _ ⟨s, hs, rfl⟩
    obtain ⟨hsc, hsA⟩ := mem_inf.1 (hS hs)
    have hsv : s * vE6 K = vE6 K * s := mem_centralizer_singleton_iff.1 hsc
    refine mem_inf.2 ⟨mem_centralizer_singleton_iff.2 ?_, ?_⟩
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [← vConj_mul_classV_mul_inv, ← hm]
      calc m * s * m⁻¹ * (m * vE6 K * m⁻¹) = m * (s * vE6 K) * m⁻¹ := by group
        _ = m * (vE6 K * s) * m⁻¹ := by rw [hsv]
        _ = m * vE6 K * m⁻¹ * (m * s * m⁻¹) := by group
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact mul_mem (mul_mem hmA hsA) (inv_mem hmA)
  have h := factorization_card_le_of_le_centralizer_zAS hK hS'le
    (EPilot.forall_normal_isPGroup_eq_bot_of_mulEquiv eS hO2)
  rwa [← Nat.card_congr eS.toEquiv] at h

end Orders

section Levi

theorem two_pow_dvd_card_of_lieModel_PSU_six {X : Type} [Group X] {f : ℕ} (hf : 1 ≤ f)
    (h : LieModel X .PSU 6 2 f) : 2 ^ (8 * f + 1) ∣ Nat.card X := by
  rw [UnitaryPilot.card_of_lieModel_PSU_two_pow h]
  exact (pow_dvd_pow 2 (by omega : 8 * f + 1 ≤ f * (5 * (5 + 1) / 2))).trans
    (UnitaryPilot.ordTwistedA_two_pow_bounds (n := 5) (by norm_num) hf).1

theorem two_pow_dvd_card_of_lieModel_PSp_three {X : Type} [Group X] {f : ℕ} (hf : 1 ≤ f)
    (h : LieModel X .PSp 3 2 f) : 2 ^ (8 * f + 1) ∣ Nat.card X := by
  rw [SymplecticPilot.card_of_lieModel_PSp_two_pow h]
  exact (pow_dvd_pow 2 (by omega : 8 * f + 1 ≤ f * (3 * 3))).trans
    (SymplecticPilot.ordBC_two_pow_bounds (m := 3) hf).1

theorem card_ne_of_lieModel_PSU_six_PSp_three {A B : Type} [Group A] [Group B] {f : ℕ}
    (hf : 1 ≤ f) (hA : LieModel A .PSU 6 2 f) (hB : LieModel B .PSp 3 2 f) :
    Nat.card A ≠ Nat.card B := by
  rw [UnitaryPilot.card_of_lieModel_PSU_two_pow hA, SymplecticPilot.card_of_lieModel_PSp_two_pow hB]
  obtain ⟨r, hr, hm⟩ := (Timmesfeld.Orders.profile_ordTwistedA (n := 5) (by norm_num) hf).two
  obtain ⟨r', hr', hm'⟩ := (Timmesfeld.Orders.profile_ordBC (n := 3) hf).two
  intro h
  have h5 : (6 - 1 : ℕ) = 5 := rfl
  rw [h5, hm, hm'] at h
  have h2 := congrArg (fun n => n.factorization 2) h
  rw [E6Pilot.factorization_two_mul_odd (by positivity) hr,
    E6Pilot.factorization_two_mul_odd (by positivity) hr',
    Nat.Prime.factorization_pow Nat.prime_two, Nat.Prime.factorization_pow Nat.prime_two,
    Finsupp.single_eq_same, Finsupp.single_eq_same] at h2
  norm_num at h2
  omega

theorem isEmpty_mulEquiv_of_lieModel_PSU_six_PSp_three {A B : Type} [Group A] [Group B] {f : ℕ}
    (hf : 1 ≤ f) (hA : LieModel A .PSU 6 2 f) (hB : LieModel B .PSp 3 2 f) : IsEmpty (A ≃* B) :=
  ⟨fun ι => card_ne_of_lieModel_PSU_six_PSp_three hf hA hB (Nat.card_congr ι.toEquiv)⟩

end Levi

section ClassPredicate

variable {f : ℕ} {K : Type} [Field K]

theorem exists_conj_repXC_of_nonempty_mulEquiv [CharP K 2] (hf : 1 ≤ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f)
    {x : graphFixedRootGroup TwistTag.E6 K σ} (hx : orderOf x = 2) {Λ : Type*} [Group Λ]
    {M : Subgroup Λ} (hM : ∀ N : Subgroup M, N.Normal → IsPGroup 2 N → N = ⊥)
    (h2 : 2 ^ (8 * f + 1) ∣ Nat.card M)
    (hψ : Nonempty (perfectCore (centralizer ({x} : Set (graphFixedRootGroup TwistTag.E6 K σ))) ≃*
      Λ)) :
    ∃ (κ : Fin 2) (c : graphFixedRootGroup TwistTag.E6 K σ),
      c * x * c⁻¹ = repXC (apply_apply_eq hK hσ) κ := by
  have := finite_of_card hK
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  obtain ⟨ψ⟩ := hψ
  have hx2 : x ^ 2 = 1 := hx ▸ pow_orderOf_eq_one x
  have hx1 : x ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hx
    exact absurd hx (by norm_num)
  obtain ⟨g, hg⟩ := exists_conj_repX_or_classV hf hK hσ hx2 hx1
  rcases hg with h | h | h
  · exact ⟨0, g, Subtype.ext h⟩
  · exact ⟨1, g, Subtype.ext h⟩
  · exfalso
    have : Finite Λ := Finite.of_equiv _ ψ.toEquiv
    set P := perfectCore (centralizer ({x} : Set (graphFixedRootGroup TwistTag.E6 K σ)))
      with hPdef
    set θ : M →* ModGL .E6 K := (graphFixedRootGroup TwistTag.E6 K σ).subtype.comp
      ((MulAut.conj g).toMonoidHom.comp (P.subtype.comp (ψ.symm.toMonoidHom.comp M.subtype)))
      with hθdef
    have hθ : Function.Injective θ :=
      (graphFixedRootGroup TwistTag.E6 K σ).subtype_injective.comp
        ((MulAut.conj g).injective.comp
          (P.subtype_injective.comp (ψ.symm.injective.comp M.subtype_injective)))
    have hθv : ∀ m : M, θ m * vE6 K = vE6 K * θ m := by
      intro m
      set y : graphFixedRootGroup TwistTag.E6 K σ := ((ψ.symm (m : Λ) : P) :
        graphFixedRootGroup TwistTag.E6 K σ) with hy
      have hyx : y * x = x * y := mem_centralizer_singleton_iff.1 (perfectCore_le _ (ψ.symm m).2)
      have hθm : θ m = ((g * y * g⁻¹ : graphFixedRootGroup TwistTag.E6 K σ) :
        ModGL TwistTag.E6.tag K) := rfl
      have hv : vE6 K = ((g * x * g⁻¹ : graphFixedRootGroup TwistTag.E6 K σ) :
        ModGL TwistTag.E6.tag K) := h.symm
      rw [hθm, hv]
      have : g * y * g⁻¹ * (g * x * g⁻¹) = g * x * g⁻¹ * (g * y * g⁻¹) := by
        calc g * y * g⁻¹ * (g * x * g⁻¹) = g * (y * x) * g⁻¹ := by group
          _ = g * (x * y) * g⁻¹ := by rw [hyx]
          _ = g * x * g⁻¹ * (g * y * g⁻¹) := by group
      exact congrArg Subtype.val this
    have hle : θ.range ≤ centralizer ({vE6 K} : Set (ModGL .E6 K)) ⊓ adjointGroup .E6 K := by
      rintro _ ⟨m, rfl⟩
      refine mem_inf.2 ⟨mem_centralizer_singleton_iff.2 (hθv m), ?_⟩
      exact (graphFixedRootGroup_le _ _ _ (g * ((ψ.symm (m : Λ) : P) :
        graphFixedRootGroup TwistTag.E6 K σ) * g⁻¹).2).1
    have eM : M ≃* θ.range := MonoidHom.ofInjective hθ
    have hK' : Nat.card K = 2 ^ (2 * f) := by rw [hK, ← pow_mul, mul_comm]
    have hb := factorization_card_le_of_le_centralizer_vE6 hK' hle
      (EPilot.forall_normal_isPGroup_eq_bot_of_mulEquiv eM hM)
    rw [← Nat.card_congr eM.toEquiv] at hb
    have h2' := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').1 h2
    omega

theorem exists_conj_repYC_of_nonempty_mulEquiv [CharP K 2] (hf : 1 ≤ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f)
    {x : graphFixedRootGroup TwistTag.E6 K σ} (hx : orderOf x = 2) {Λ : Type*} [Group Λ]
    {M : Subgroup Λ} (hM : ∀ N : Subgroup M, N.Normal → IsPGroup 2 N → N = ⊥)
    (h2 : 2 ^ (8 * f + 1) ∣ Nat.card M)
    (hψ : Nonempty (perfectCore (centralizer ({x} : Set (graphFixedRootGroup TwistTag.E6 K σ))) ≃*
      Λ)) :
    ∃ (κ : Fin 2) (c : graphFixedRootGroup TwistTag.E6 K σ),
      c * x * c⁻¹ = repYC (apply_apply_eq hK hσ) κ := by
  obtain ⟨κ, c, hc⟩ := exists_conj_repXC_of_nonempty_mulEquiv hf hK hσ hx hM h2 hψ
  obtain ⟨c₀, hc₀⟩ := isConj_iff.1 (isConj_repXC_repYC (apply_apply_eq hK hσ) κ)
  refine ⟨κ, c₀ * c, ?_⟩
  rw [← hc₀, ← hc]
  group

end ClassPredicate

end CFSG.SeitzReduction.TwistedE6Pilot
