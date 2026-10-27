module

public import CFSG.RankThree.PartTwo.Sec14.Item148PtRes2ProofInner
public import CFSG.RankThree.PartTwo.Sec8.Item82OneProofDefs
import CFSG.RankThree.PartTwo.Sec14.Item148StepPGLAbel
import CFSG.RankThree.PartTwo.Sec8.Item8KFactsProofE9
import CFSG.RankThree.PartTwo.Sec13.Item136PGL

public section

namespace CFSG.RankThree.PartTwo.Sec14

namespace Item148Res6

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.RankThreeEven (projImage)
open Matrix (ProjGenLinGroup GeneralLinearGroup)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)

section Cube

variable {K : Type} [Field K]

theorem three_dvd_qSubPi {π : Bool} {q : ℕ} (hq : ModThree π q) : 3 ∣ qSubPi π q := by
  cases π
  · change q % 3 = 2 at hq
    change 3 ∣ q + 1
    omega
  · change q % 3 = 1 at hq
    change 3 ∣ q - 1
    omega

theorem exists_cube_root_of_pow_div_three {π : Bool} {p f : ℕ} (hK : PiField π p f K)
    (hq : ModThree π (p ^ f)) {x : Kˣ} (hxm : x ^ (qSubPi π (p ^ f) / 3) = 1) :
    ∃ μ ∈ rootsOfUnity (qSubPi π (p ^ f)) K, μ ^ 3 = x := by
  have := hK.finite
  have hcyc : IsCyclic Kˣ := inferInstance
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  have hog : orderOf g = Nat.card Kˣ := orderOf_eq_card_of_forall_mem_zpowers hg
  have hKu : Nat.card Kˣ = Nat.card K - 1 := Nat.card_units K
  have hq1 : 1 < p ^ f := Nat.one_lt_pow (by have := hK.one_le; omega) hK.prime.one_lt
  obtain ⟨r, hr⟩ : ∃ r, Nat.card Kˣ = qSubPi π (p ^ f) * r := by
    cases π with
    | true =>
      refine ⟨1, ?_⟩
      rw [hKu, hK.card, mul_one]
      rfl
    | false =>
      refine ⟨p ^ f - 1, ?_⟩
      rw [hKu, hK.card]
      change (p ^ f) ^ 2 - 1 = (p ^ f + 1) * (p ^ f - 1)
      have h1 : 1 ≤ p ^ f := by omega
      zify [h1, Nat.one_le_pow 2 (p ^ f) (by omega)]
      ring
  obtain ⟨m, hm⟩ := three_dvd_qSubPi hq
  have hmpos : 0 < m := by
    have : 0 < qSubPi π (p ^ f) := by
      cases π
      · change 0 < p ^ f + 1
        omega
      · change 0 < p ^ f - 1
        omega
    omega
  rw [hm, Nat.mul_div_cancel_left _ (by norm_num)] at hxm
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, g ^ k = x :=
    (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr (hg x))
  have hdvd : orderOf g ∣ k * m := by
    rw [orderOf_dvd_iff_pow_eq_one, pow_mul]
    exact hxm
  rw [hog, hr, hm] at hdvd
  have h3r : 3 * r ∣ k := by
    have h1 : 3 * r * m ∣ k * m := by
      rw [show 3 * r * m = 3 * m * r by ring]
      exact hdvd
    exact Nat.dvd_of_mul_dvd_mul_right hmpos h1
  obtain ⟨j, rfl⟩ := h3r
  refine ⟨g ^ (r * j), ?_, ?_⟩
  · rw [mem_rootsOfUnity, ← pow_mul, hm, show r * j * (3 * m) = 3 * m * r * j by ring,
      pow_mul, ← hm, ← hr, ← hog, pow_orderOf_eq_one, one_pow]
  · rw [← pow_mul, show r * j * 3 = 3 * r * j by ring]

theorem detPow_eq_one_of_mem_center {π : Bool} {p f : ℕ} (hK : PiField π p f K)
    (hq : ModThree π (p ^ f)) (A : GL (Fin 3) K) (hA : A ∈ glPi π 3 (p ^ f) K)
    (hAc : A ∈ Subgroup.center (GL (Fin 3) K)) :
    GeneralLinearGroup.det A ^ (qSubPi π (p ^ f) / 3) = 1 := by
  rw [GeneralLinearGroup.center_eq_range_scalar] at hAc
  obtain ⟨u, rfl⟩ := hAc
  have hu := (scalar_mem_glPi_iff hK u).mp hA
  rw [mem_rootsOfUnity] at hu
  rw [det_scalar148, ← pow_mul, Nat.mul_div_cancel' (three_dvd_qSubPi hq), hu]

theorem mk_mem_projImage_slPi_of_detPow {π : Bool} {p f : ℕ} (hK : PiField π p f K)
    (hq : ModThree π (p ^ f)) {g : GL (Fin 3) K} (hg : g ∈ glPi π 3 (p ^ f) K)
    (hdet : GeneralLinearGroup.det g ^ (qSubPi π (p ^ f) / 3) = 1) :
    ProjGenLinGroup.mk g ∈ projImage (slPi π 3 (p ^ f) K) := by
  obtain ⟨μ, hμ, hμ3⟩ := exists_cube_root_of_pow_div_three hK hq hdet
  have hμG : GeneralLinearGroup.scalar (Fin 3) μ ∈ glPi π 3 (p ^ f) K :=
    (scalar_mem_glPi_iff hK μ).mpr hμ
  have hdet' : (g : Matrix (Fin 3) (Fin 3) K).det = (μ : K) ^ 3 := by
    rw [← GeneralLinearGroup.val_det_apply, ← hμ3, Units.val_pow_eq_pow_val]
  obtain ⟨l, hl, ⟨z, hz⟩, -⟩ := exists_inner_of_det_eq_cube hK hg hμG hdet'
  refine ⟨l, hl, ?_⟩
  rw [hz, map_mul, ProjGenLinGroup.mk_scalar, mul_one]

end Cube

section Tau

variable {Γ : Type} [Group Γ] [Finite Γ] {J E : Subgroup Γ} {p f : ℕ}

omit [Finite Γ] in
theorem exists_tau_of_isZ3PGLThreeAt (hX : IsZ3PGLThreeAt ↥(J ⊔ E) p f)
    (hJp : Group.IsPerfect ↥J) (hJnt : Nontrivial ↥J)
    (hEJ : E ≤ Subgroup.normalizer (J : Set Γ)) :
    ∃ (π : Bool) (K : Type) (_ : Field K) (_ : PiField π p f K) (_ : ModThree π (p ^ f))
      (φ : ↥(J ⊔ E) ≃* Multiplicative (ZMod 3) × ↥(projImage (glPi π 3 (p ^ f) K))),
      (∀ j : ↥J, (φ (Subgroup.inclusion le_sup_left j)).1 = 1) ∧
      (∀ s ∈ projImage (slPi π 3 (p ^ f) K), ∃ j : ↥J,
        ((φ (Subgroup.inclusion le_sup_left j)).2 : ProjGenLinGroup (Fin 3) K) = s) ∧
      (∀ j : ↥J, ((φ (Subgroup.inclusion le_sup_left j)).2 : ProjGenLinGroup (Fin 3) K) ∈
        projImage (slPi π 3 (p ^ f) K)) := by
  classical
  have := hJp
  obtain ⟨π, K, _, hK, hq, ⟨φ⟩⟩ := hX
  have := hK.finite
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hJX : J ≤ J ⊔ E := le_sup_left
  have hXN : J ⊔ E ≤ Subgroup.normalizer (J : Set Γ) := sup_le Subgroup.le_normalizer hEJ
  have hSP : projImage (slPi π 3 (p ^ f) K) ≤ projImage (glPi π 3 (p ^ f) K) :=
    Subgroup.map_mono (slPi_le_glPi hπ)
  set φ₀ : ↥J →* Multiplicative (ZMod 3) × ↥(projImage (glPi π 3 (p ^ f) K)) :=
    φ.toMonoidHom.comp (Subgroup.inclusion hJX) with hφ₀
  set τ : ↥J →* ProjGenLinGroup (Fin 3) K :=
    (projImage (glPi π 3 (p ^ f) K)).subtype.comp ((MonoidHom.snd _ _).comp φ₀) with hτ
  have hτapp : ∀ j : ↥J, τ j = ((φ₀ j).2 : ProjGenLinGroup (Fin 3) K) := fun j => rfl
  have h1 : ∀ j : ↥J, (φ₀ j).1 = 1 := fun j =>
    Item148PtRes2.eq_one_of_isPerfect ((MonoidHom.fst _ _).comp φ₀) j
  have hτinj : Function.Injective τ := by
    rw [injective_iff_map_eq_one]
    intro j hj
    have h2 : (φ₀ j).2 = 1 := Subtype.ext (by rw [← hτapp]; exact hj)
    have h12 : φ (Subgroup.inclusion hJX j) = 1 := Prod.ext (h1 j) h2
    have h3 : Subgroup.inclusion hJX j = 1 := φ.injective (h12.trans (map_one φ).symm)
    exact Subgroup.inclusion_injective hJX (h3.trans (map_one _).symm)
  have hrangeP : τ.range ≤ projImage (glPi π 3 (p ^ f) K) := by
    rintro _ ⟨j, rfl⟩
    exact (φ₀ j).2.2
  have hrangeS : τ.range ≤ projImage (slPi π 3 (p ^ f) K) := by
    have : Group.IsPerfect τ.range := Group.IsPerfect.range τ
    rw [← Subgroup.commutator_eq_self (H := τ.range)]
    exact (Subgroup.commutator_mono hrangeP hrangeP).trans
      (Item148PtRes2.commutator_projImage_glPi_le hπ)
  have hconj : ∀ (x : ↥(J ⊔ E)) (j : ↥J) (hj : (x : Γ) * (j : Γ) * (x : Γ)⁻¹ ∈ J),
      τ ⟨_, hj⟩ = ((φ x).2 : ProjGenLinGroup (Fin 3) K) * τ j *
        ((φ x).2 : ProjGenLinGroup (Fin 3) K)⁻¹ := by
    intro x j hj
    have e1 : Subgroup.inclusion hJX ⟨_, hj⟩ = x * Subgroup.inclusion hJX j * x⁻¹ :=
      Subtype.ext rfl
    rw [hτapp, hτapp, hφ₀, MonoidHom.comp_apply, e1]
    simp only [MulEquiv.coe_toMonoidHom, map_mul, Prod.snd_mul, Subgroup.coe_mul,
      MonoidHom.comp_apply]
    rw [map_inv φ x]
    rfl
  have hnorm : ∀ s ∈ projImage (slPi π 3 (p ^ f) K), ∀ t ∈ τ.range, s * t * s⁻¹ ∈ τ.range := by
    rintro s hs _ ⟨j, rfl⟩
    set x : ↥(J ⊔ E) := φ.symm (1, ⟨s, hSP hs⟩) with hx
    have hxs : ((φ x).2 : ProjGenLinGroup (Fin 3) K) = s := by
      rw [hx, MulEquiv.apply_symm_apply]
    have hj' : (x : Γ) * (j : Γ) * (x : Γ)⁻¹ ∈ J :=
      (Subgroup.mem_normalizer_iff.mp (hXN x.2) j).mp j.2
    exact ⟨⟨_, hj'⟩, by rw [hconj x j hj', hxs]⟩
  obtain ⟨j₀, hj₀⟩ := exists_ne (1 : ↥J)
  rcases Item148PtRes2.solvable_or_simple hK hq with hsol | ⟨-, hsimp⟩
  · exfalso
    have hJs : Group.IsSolvable ↥J :=
      Group.isSolvable_of_isSolvable_injective
        (f := τ.codRestrict (projImage (slPi π 3 (p ^ f) K)) fun j => hrangeS ⟨j, rfl⟩)
        (fun a b hab => hτinj (by simpa using congrArg Subtype.val hab))
    exact Group.IsPerfect.not_isSolvable ↥J hJs
  have hrange : τ.range = projImage (slPi π 3 (p ^ f) K) := by
    have hN : (τ.range.subgroupOf (projImage (slPi π 3 (p ^ f) K))).Normal :=
      ⟨fun t ht s => by
        rw [Subgroup.mem_subgroupOf] at ht ⊢
        exact hnorm s s.2 t ht⟩
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
        (τ.range.subgroupOf (projImage (slPi π 3 (p ^ f) K))) with hb | ht
    · exfalso
      have hj₀' : τ j₀ = 1 := by
        have h1 : (⟨τ j₀, hrangeS ⟨_, rfl⟩⟩ : ↥(projImage (slPi π 3 (p ^ f) K))) ∈
            τ.range.subgroupOf (projImage (slPi π 3 (p ^ f) K)) :=
          Subgroup.mem_subgroupOf.mpr ⟨_, rfl⟩
        rw [hb, Subgroup.mem_bot] at h1
        exact congrArg Subtype.val h1
      exact hj₀ (hτinj (hj₀'.trans (map_one τ).symm))
    · refine le_antisymm hrangeS fun s hs => ?_
      have h1 : (⟨s, hs⟩ : ↥(projImage (slPi π 3 (p ^ f) K))) ∈
          τ.range.subgroupOf (projImage (slPi π 3 (p ^ f) K)) := by
        rw [ht]
        exact Subgroup.mem_top _
      exact Subgroup.mem_subgroupOf.mp h1
  refine ⟨π, K, inferInstance, hK, hq, φ, h1, fun s hs => ?_, fun j => hrangeS ⟨j, rfl⟩⟩
  rw [← hrange] at hs
  obtain ⟨j, hj⟩ := hs
  exact ⟨j, hj⟩

theorem e9Closed_of_isZ3PGLThreeAt (hX : IsZ3PGLThreeAt ↥(J ⊔ E) p f)
    (hJp : Group.IsPerfect ↥J) (hJnt : Nontrivial ↥J)
    (hEJ : E ≤ Subgroup.normalizer (J : Set Γ)) : Sec8.E9Closed ↥J := by
  classical
  obtain ⟨π, K, _, hK, hq, φ, -, hsurj, hmem⟩ := exists_tau_of_isZ3PGLThreeAt hX hJp hJnt hEJ
  set τ : ↥J →* ↥(projImage (slPi π 3 (p ^ f) K)) :=
    { toFun := fun j => ⟨((φ (Subgroup.inclusion le_sup_left j)).2 :
        ProjGenLinGroup (Fin 3) K), hmem j⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun j j' => by
        apply Subtype.ext
        simp } with hτ
  have hτinj : Function.Injective τ := by
    rw [injective_iff_map_eq_one]
    intro j hj
    have h2 : (φ (Subgroup.inclusion le_sup_left j)).2 = 1 :=
      Subtype.ext (show ((φ (Subgroup.inclusion le_sup_left j)).2 : ProjGenLinGroup (Fin 3) K) =
        1 from congrArg Subtype.val hj)
    have h1 : (φ (Subgroup.inclusion le_sup_left j)).1 = 1 :=
      Item148PtRes2.eq_one_of_isPerfect
        ((MonoidHom.fst _ _).comp (φ.toMonoidHom.comp (Subgroup.inclusion le_sup_left))) j
    have h12 : φ (Subgroup.inclusion le_sup_left j) = 1 := Prod.ext h1 h2
    have h3 : Subgroup.inclusion (le_sup_left : J ≤ J ⊔ E) j = 1 :=
      φ.injective (h12.trans (map_one φ).symm)
    exact Subgroup.inclusion_injective le_sup_left (h3.trans (map_one _).symm)
  have hτsurj : Function.Surjective τ := by
    rintro ⟨s, hs⟩
    obtain ⟨j, hj⟩ := hsurj s hs
    exact ⟨j, Subtype.ext hj⟩
  set ψ := MulEquiv.ofBijective τ ⟨hτinj, hτsurj⟩ with hψ
  obtain ⟨D, hD, h9⟩ := Sec13.exists_elemAbelian_nine_projImage_slPi hK hq
  obtain ⟨u, v, hu1, hu3, hv3, huv, hvu⟩ :=
    Sec8.Item8KFactsProof.exists_pair_of_injective ψ.symm.toMonoidHom ψ.symm.injective
      (Sec8.Item8KFactsProof.exists_pair_of_isElemAbelian hD h9)
  exact Sec8.Item8KFactsProof.e9Closed_of_commuting hu1 hu3 hv3 huv hvu

omit [Finite Γ] in
theorem exists_ne_one_mem_inf_of_isZ3PGLThreeAt (hX : IsZ3PGLThreeAt ↥(J ⊔ E) p f)
    (hJp : Group.IsPerfect ↥J) (hJnt : Nontrivial ↥J)
    (hEJ : E ≤ Subgroup.normalizer (J : Set Γ)) (hE3 : ∀ a ∈ E, a ^ 3 = 1)
    (hE27 : Nat.card E = 27) : ∃ b ∈ E ⊓ J, b ≠ 1 := by
  classical
  obtain ⟨π, K, _, hK, hq, φ, h1, hsurj, -⟩ := exists_tau_of_isZ3PGLThreeAt hX hJp hJnt hEJ
  have := hK.finite
  obtain ⟨δ, hδ⟩ := exists_detPow_projImage (glPi π 3 (p ^ f) K) (qSubPi π (p ^ f) / 3)
    (detPow_eq_one_of_mem_center hK hq)
  set ψ₀ : ↥E →* Multiplicative (ZMod 3) × Kˣ :=
    (MonoidHom.prodMap (MonoidHom.id _) δ).comp
      (φ.toMonoidHom.comp (Subgroup.inclusion (le_sup_right : E ≤ J ⊔ E))) with hψ₀
  set T : Subgroup (Multiplicative (ZMod 3) × Kˣ) := (⊤ : Subgroup (Multiplicative (ZMod 3))).prod
    (rootsOfUnity 3 K) with hT
  have hrT : ψ₀.range ≤ T := by
    rintro _ ⟨a, rfl⟩
    refine Subgroup.mem_prod.mpr ⟨Subgroup.mem_top _, ?_⟩
    rw [mem_rootsOfUnity]
    have ha3 : a ^ 3 = 1 := Subtype.ext (by simpa using hE3 a a.2)
    have h := congrArg Prod.snd (show ψ₀ a ^ 3 = 1 by rw [← map_pow, ha3, map_one])
    simpa using h
  have hTcard : Nat.card T ≤ 9 := by
    have h3 : Nat.card (Multiplicative (ZMod 3)) = 3 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
    rw [hT, Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod, Subgroup.card_top,
      h3]
    have := card_rootsOfUnity (R := K) 3
    omega
  have hrcard : Nat.card ψ₀.range ≤ 9 := (Subgroup.card_le_of_le hrT).trans hTcard
  have hcard : Nat.card ψ₀.ker * Nat.card ψ₀.range = 27 := by
    rw [Subgroup.card_ker_mul_card_range, hE27]
  have hker : ψ₀.ker ≠ ⊥ := by
    intro hb
    rw [hb, Subgroup.card_bot, one_mul] at hcard
    omega
  obtain ⟨⟨b, hb⟩, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hker
  have hb1' : b ≠ 1 := fun h => hb1 (Subtype.ext h)
  refine ⟨b, ⟨b.2, ?_⟩, fun h => hb1' (Subtype.ext h)⟩
  rw [MonoidHom.mem_ker] at hb
  have hb₁ : (φ (Subgroup.inclusion le_sup_right b)).1 = 1 := congrArg Prod.fst hb
  have hb₂ : δ (φ (Subgroup.inclusion le_sup_right b)).2 = 1 := congrArg Prod.snd hb
  obtain ⟨g, hg, hgeq⟩ := (φ (Subgroup.inclusion le_sup_right b)).2.2
  have hδg : δ (φ (Subgroup.inclusion le_sup_right b)).2 =
      GeneralLinearGroup.det g ^ (qSubPi π (p ^ f) / 3) := by
    rw [← hδ g hg]
    congr 1
    exact Subtype.ext hgeq.symm
  rw [hδg] at hb₂
  obtain ⟨j, hj⟩ := hsurj _ (mk_mem_projImage_slPi_of_detPow hK hq hg hb₂)
  have hφ : φ (Subgroup.inclusion le_sup_left j) = φ (Subgroup.inclusion le_sup_right b) := by
    refine Prod.ext (by rw [h1, hb₁]) (Subtype.ext ?_)
    rw [hj, hgeq]
  have h2 := congrArg Subtype.val (φ.injective hφ)
  change (j : Γ) = (b : Γ) at h2
  rw [← h2]
  exact j.2

end Tau

end Item148Res6

end CFSG.RankThree.PartTwo.Sec14
