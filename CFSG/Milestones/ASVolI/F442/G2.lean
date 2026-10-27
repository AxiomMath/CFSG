module

public import CFSG.Milestones.ASVolI.F442.Amal
public import CFSG.Milestones.ASVolI.F431.RA35G2
import all CFSG.Milestones.ASVolI.F4
import all CFSG.Milestones.ASVolI.F4Conjugacy
public import CFSG.Milestones.ASVolI.F431.AInvSpAll

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.ASVolI.ChF CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431
  CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion

section G2Model

set_option linter.unusedSectionVars false


open CFSG.Quasithin.F6 CFSG.Quasithin.F6.G22Perm CFSG.Quasithin.F6.G22Shape

variable {k : Type} [Field k] (h2 : (2 : k) = 0) (hk2 : ∀ c : k, c = 0 ∨ c = 1)

@[expose] def burnsideF42g_g2_cnt (i : ℕ) : ℕ :=
  ((Finset.range 64).filter (fun j => G2Two.Tab.mulT j i = G2Two.Tab.mulT i j)).card

theorem burnsideF42g_g2_card_SC {i : ℕ} (hi : i < 64) :
    Nat.card ↥((lat h2 hk2).S ⊓ Subgroup.centralizer ({sEl h2 i} : Set (G2Group k))) =
      burnsideF42g_g2_cnt i := by
  classical
  symm
  rw [burnsideF42g_g2_cnt, ← Nat.card_eq_finsetCard]
  have hmem : ∀ j : ℕ, j ∈ (Finset.range 64).filter
      (fun j => G2Two.Tab.mulT j i = G2Two.Tab.mulT i j) ↔
      j < 64 ∧ G2Two.Tab.mulT j i = G2Two.Tab.mulT i j := by
    intro j
    simp
  refine Nat.card_congr (Equiv.ofBijective (fun j => ⟨sEl h2 j.1,
    Subgroup.mem_inf.mpr ⟨sEl_mem_S h2 hk2 ((hmem j.1).mp j.2).1, ?_⟩⟩) ⟨?_, ?_⟩)
  · obtain ⟨hj, hji⟩ := (hmem j.1).mp j.2
    rw [Subgroup.mem_centralizer_singleton_iff, G2Two.Model.sEl_mulT h2 hk2 hj hi,
      G2Two.Model.sEl_mulT h2 hk2 hi hj, hji]
  · intro j j' hjj
    have hj := ((hmem j.1).mp j.2).1
    have hj' := ((hmem j'.1).mp j'.2).1
    exact Subtype.ext (sEl_injective h2 hk2 hj hj' (congrArg Subtype.val hjj))
  · rintro ⟨g, hgS, hgc⟩
    obtain ⟨j, hj, rfl⟩ := (mem_S_iff h2 hk2).mp hgS
    have hc := Subgroup.mem_centralizer_singleton_iff.mp hgc
    rw [G2Two.Model.sEl_mulT h2 hk2 hj hi, G2Two.Model.sEl_mulT h2 hk2 hi hj] at hc
    have hji : G2Two.Tab.mulT j i = G2Two.Tab.mulT i j :=
      sEl_injective h2 hk2 (G2Two.Tab.mulT_spec j hj i hi).1 (G2Two.Tab.mulT_spec i hi j hj).1 hc
    exact ⟨⟨j, (hmem j).mpr ⟨hj, hji⟩⟩, rfl⟩

theorem burnsideF42g_g2_cnt_chk : burnsideF42g_g2_cnt 32 = 16 ∧
    ∀ i < 64, 32 ≤ i → G2Two.Tab.mulT i i = 0 → burnsideF42g_g2_cnt i ≤ 16 := by
  unfold burnsideF42g_g2_cnt
  decide +kernel

theorem burnsideF42g_g2_sylow_rho [Finite k] :
    IsSylowTwoOf ((lat h2 hk2).S ⊓ Subgroup.centralizer ({g2RhoC h2} : Set (G2Group k)))
      (Subgroup.centralizer ({g2RhoC h2} : Set (G2Group k))) := by
  haveI : Finite (G2Group k) := finite_g2Group
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have D := g2IndexTwoData h2 hk2
  have hρ2 : g2RhoC h2 * g2RhoC h2 = 1 := D.sq
  have hCP : Subgroup.centralizer ({g2RhoC h2} : Set (G2Group k)) ≤ (lat h2 hk2).P₁ :=
    fun c hc => burnsideF4gG2TwoInv_cent_rho_le_P₁ h2 hk2
      (Subgroup.mem_centralizer_singleton_iff.mp hc)
  set C := Subgroup.centralizer ({g2RhoC h2} : Set (G2Group k)) with hCdef
  set P := (lat h2 hk2).S ⊓ C with hPdef
  have hPcard : Nat.card P = 16 := by
    rw [hPdef, hCdef, ← burnsideF4gG2TwoInv_sEl32 h2, burnsideF42g_g2_card_SC h2 hk2 (by norm_num)]
    exact burnsideF42g_g2_cnt_chk.1
  have hPp : IsPGroup 2 P := (lat h2 hk2).sylow.1.to_le inf_le_left
  obtain ⟨T, hT, hPT⟩ := CFSG.Quasithin.Loc442Q.exists_sylowTwo_ge (inf_le_right : P ≤ C) hPp
  have hStop : IsSylowTwoOf (lat h2 hk2).S ⊤ := by
    refine ⟨le_top, (lat h2 hk2).sylow.1, ?_⟩
    rw [show ((lat h2 hk2).S.subgroupOf ⊤).index = (lat h2 hk2).S.relIndex ⊤ from rfl,
      Subgroup.relIndex_top_right]
    exact (lat h2 hk2).sylow.2
  have hSP : IsSylowTwoOf (lat h2 hk2).S (lat h2 hk2).P₁ :=
    F7.isSylowTwoOf_mono_right hStop (lat h2 hk2).S_le_P₁ le_top
  obtain ⟨x, -, hTx⟩ := F7.isSylowTwoOf_exists_conj_le hSP (hT.1.trans hCP) hT.2.1
  have hρS : g2RhoC h2 ∈ (lat h2 hk2).S := by
    rw [← burnsideF4gG2TwoInv_sEl32 h2]
    exact sEl_mem_S h2 hk2 (by norm_num)
  have hρP : g2RhoC h2 ∈ P := ⟨hρS, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  have hsS : x⁻¹ * g2RhoC h2 * x ∈ (lat h2 hk2).S := mem_conjSub.mp (hTx (hPT hρP))
  obtain ⟨i, hi, hsi⟩ := (mem_S_iff h2 hk2).mp hsS
  have hi32 : 32 ≤ i := by
    by_contra hlt
    rw [not_le] at hlt
    apply D.rho_not_mem
    have hJ : sEl h2 i ∈ (g2HomC h2).range := ⟨u33Tel u33GenPG i, by simp [sEl, hlt]⟩
    rw [← hsi] at hJ
    have := (burnsideF4gG2TwoInv_J_normal h2 hk2).conj_mem _ hJ x
    rwa [show x * (x⁻¹ * g2RhoC h2 * x) * x⁻¹ = g2RhoC h2 by group] at this
  have hsq : G2Two.Tab.mulT i i = 0 := by
    rw [← G2Two.Model.sEl_sq h2 hk2 hi, ← hsi]
    calc x⁻¹ * g2RhoC h2 * x * (x⁻¹ * g2RhoC h2 * x) = x⁻¹ * (g2RhoC h2 * g2RhoC h2) * x := by
          group
      _ = 1 := by rw [hρ2]; group
  have hle : conjSub x⁻¹ T ≤
      (lat h2 hk2).S ⊓ Subgroup.centralizer ({sEl h2 i} : Set (G2Group k)) := by
    intro y hy
    rw [mem_conjSub, inv_inv] at hy
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · have := mem_conjSub.mp (hTx hy)
      rwa [show x⁻¹ * (x * y * x⁻¹) * x = y by group] at this
    · rw [Subgroup.mem_centralizer_singleton_iff, ← hsi]
      have hc := Subgroup.mem_centralizer_singleton_iff.mp (hT.1 hy)
      calc y * (x⁻¹ * g2RhoC h2 * x) = x⁻¹ * ((x * y * x⁻¹) * g2RhoC h2) * x := by group
        _ = x⁻¹ * (g2RhoC h2 * (x * y * x⁻¹)) * x := by rw [hc]
        _ = x⁻¹ * g2RhoC h2 * x * y := by group
  have hTcard : Nat.card T ≤ 16 := by
    calc Nat.card T = Nat.card (conjSub x⁻¹ T) :=
          (CFSG.Quasithin.Loc442Q.card_conjSub_eq x⁻¹ T).symm
      _ ≤ Nat.card ↥((lat h2 hk2).S ⊓ Subgroup.centralizer ({sEl h2 i} : Set (G2Group k))) :=
          Subgroup.card_le_of_le hle
      _ = burnsideF42g_g2_cnt i := burnsideF42g_g2_card_SC h2 hk2 hi
      _ ≤ 16 := burnsideF42g_g2_cnt_chk.2 i hi hi32 hsq
  have hPT' : P = T := Subgroup.eq_of_le_of_card_ge hPT (by rw [hPcard]; exact hTcard)
  rw [hPT']
  exact hT

include hk2 in
theorem burnsideF42g_g2_cent_inv [Finite k] {c : G2Group k} (hc : c * g2RhoC h2 = g2RhoC h2 * c)
    (hc2 : c * c = 1 ∨ c * c = g2RhoC h2) (hc1 : c ≠ 1) (hcρ : c ≠ g2RhoC h2) :
    IsConj (sEl h2 26) c ∨ IsConj (sEl h2 26) (c * g2RhoC h2) := by
  have D := g2IndexTwoData h2 hk2
  have hρ2 : g2RhoC h2 * g2RhoC h2 = 1 := D.sq
  have hρJ : g2RhoC h2 ∉ (g2HomC h2).range := D.rho_not_mem
  have hsqJ : ∀ y ∈ (g2HomC h2).range, y * y = 1 ∨ y * y = g2RhoC h2 → y * y = 1 := by
    intro y hy h
    rcases h with h | h
    · exact h
    · exact absurd (h ▸ (g2HomC h2).range.mul_mem hy hy) hρJ
  obtain ⟨x, ε, hcx⟩ := exists_rep h2 hk2 c
  cases ε with
  | false =>
    have hcJ : c ∈ (g2HomC h2).range := ⟨x, by rw [hcx]; simp [rhoPow]⟩
    left
    exact (burnsideF4gG2TwoInv_inner_inv_conj h2 hcJ hc1 (hsqJ c hcJ hc2)).symm
  | true =>
    have hcJ : c * g2RhoC h2 ∈ (g2HomC h2).range := ⟨x, by
      rw [hcx]; simp only [rhoPow, ite_true]; rw [mul_assoc, hρ2, mul_one]⟩
    right
    have hsq : (c * g2RhoC h2) * (c * g2RhoC h2) = c * c := by
      calc c * g2RhoC h2 * (c * g2RhoC h2) = c * (g2RhoC h2 * c) * g2RhoC h2 := by group
        _ = c * (c * g2RhoC h2) * g2RhoC h2 := by rw [hc]
        _ = c * c * (g2RhoC h2 * g2RhoC h2) := by group
        _ = c * c := by rw [hρ2, mul_one]
    have hcρ1 : c * g2RhoC h2 ≠ 1 := by
      intro h
      apply hcρ
      calc c = c * g2RhoC h2 * g2RhoC h2 := by rw [mul_assoc, hρ2, mul_one]
        _ = g2RhoC h2 := by rw [h, one_mul]
    have hcc : c * c = 1 := by
      rw [← hsq]
      exact hsqJ _ hcJ (by rw [hsq]; exact hc2)
    exact (burnsideF4gG2TwoInv_inner_inv_conj h2 hcJ hcρ1 (by rw [hsq, hcc])).symm

include hk2 in
theorem burnsideF42g_g2_ab [Finite k] :
    sEl h2 26 * g2RhoC h2 = g2RhoC h2 * sEl h2 26 ∧
      sEl h2 21 * g2RhoC h2 = g2RhoC h2 * sEl h2 21 ∧ sEl h2 26 * sEl h2 26 = 1 ∧
      sEl h2 21 * sEl h2 21 = 1 ∧ IsConj (sEl h2 26) (sEl h2 21) ∧
      ∀ x : G2Group k, x * g2RhoC h2 = g2RhoC h2 * x →
        x * sEl h2 26 * x⁻¹ ≠ sEl h2 21 ∧ x * sEl h2 26 * x⁻¹ ≠ sEl h2 21 * g2RhoC h2 := by
  rw [← burnsideF4gG2TwoInv_sEl32 h2]
  have hm : ∀ i j : ℕ, i < 64 → j < 64 → G2Two.Tab.mulT i j = G2Two.Tab.mulT j i →
      sEl h2 i * sEl h2 j = sEl h2 j * sEl h2 i := fun i j hi hj h => by
    rw [G2Two.Model.sEl_mulT h2 hk2 hi hj, G2Two.Model.sEl_mulT h2 hk2 hj hi, h]
  have h21 : sEl h2 21 * sEl h2 21 = 1 := (G2Two.Model.sEl_sq h2 hk2 (by norm_num)).mpr
    (by decide +kernel)
  have h21J : sEl h2 21 ∈ (g2HomC h2).range := ⟨u33Tel u33GenPG 21, by simp [sEl]⟩
  have h21ne : sEl h2 21 ≠ 1 := by
    rw [← sEl_zero h2 hk2]
    exact G2Two.Model.sEl_ne h2 hk2 (by norm_num) (by norm_num) (by norm_num)
  have hR1n : ∀ y ∈ (lat h2 hk2).P₁, ∀ r ∈ R1 h2 hk2, y * r * y⁻¹ ∈ R1 h2 hk2 := fun y hy r hr =>
    (Subgroup.mem_normalizer_iff.mp (P₁_le_normalizer h2 hk2 g22_R1_lt_chk (fun _ => Iff.rfl)
      g22_R1_norm_chk hy) r).mp hr
  have hnR1 : ∀ j < 64, j ∉ g22R1Idx → sEl h2 j ∉ R1 h2 hk2 := by
    rintro j hj hjR ⟨i, hi, hij⟩
    have := sEl_injective h2 hk2 hj (g22_R1_lt_chk i hi) hij
    exact hjR (this ▸ hi)
  refine ⟨hm 26 32 (by norm_num) (by norm_num) (by decide +kernel),
    hm 21 32 (by norm_num) (by norm_num) (by decide +kernel),
    (G2Two.Model.sEl_sq h2 hk2 (by norm_num)).mpr (by decide +kernel), h21,
    (burnsideF4gG2TwoInv_inner_inv_conj h2 h21J h21ne h21).symm, fun x hx => ?_⟩
  have hxP : x ∈ (lat h2 hk2).P₁ := burnsideF4gG2TwoInv_cent_rho_le_P₁ h2 hk2
    (by rw [← burnsideF4gG2TwoInv_sEl32 h2]; exact hx)
  have ha : x * sEl h2 26 * x⁻¹ ∈ R1 h2 hk2 := hR1n x hxP _ ⟨26, by decide +kernel, rfl⟩
  refine ⟨fun h => hnR1 21 (by norm_num) (by decide +kernel) (h ▸ ha), fun h => ?_⟩
  rw [G2Two.Model.sEl_mulT h2 hk2 (by norm_num) (by norm_num)] at h
  have h53 : G2Two.Tab.mulT 21 32 = 53 := by decide +kernel
  rw [h53] at h
  exact hnR1 53 (by norm_num) (by decide +kernel) (h ▸ ha)

include hk2 in
theorem burnsideF42g_g2_not_conj :
    ¬ IsConj (sEl h2 26) (g2RhoC h2) := by
  intro h
  obtain ⟨c, hc⟩ := isConj_iff.mp h
  apply (g2IndexTwoData h2 hk2).rho_not_mem
  rw [← hc, burnsideF4gG2TwoInv_sEl26 h2]
  exact (burnsideF4gG2TwoInv_J_normal h2 hk2).conj_mem _ ⟨u33z, rfl⟩ c

end G2Model

section G2Main

set_option linter.unusedSectionVars false


open CFSG.Quasithin.F6 CFSG.Quasithin.F6.G22Perm CFSG.Quasithin.F6.G22Shape
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

variable {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E} {Y : Type} [Group Y]
  {β : Cpl M₁ M₂ Y} {M : Type} [Group M] {ε : Y →* M} {z : M}

theorem burnsideF42g_A42_G2two (hyp : HypF_4_31 .G2 1 Gp M₁ M₂ β ε z) (_hL43 : ¬ IsL43 M)
    (hGp : Gp = ⊤) :
    ∃ t : ↥M₂, (t : E) ∈ pCoreOf 2 (Gp ⊓ M₂) ∧ IsShortRootInv .G2 Gp M₁ M₂ (t : E) ∧
      Subgroup.centralizer ({epsG β ε (f2 (c := β) t)} : Set M) ≤ MiTwo β ε := by
  classical
  haveI := hyp.amalgam.finite
  haveI := hyp.finite_M
  obtain ⟨chart, hm⟩ := hyp.amalgam.lie_amalgam
  rcases chart.coordinates with ⟨c, hk, -⟩ |
      ⟨-, hp, hd, K, fK, finK, hcard, marking, h1, h2', h3, h4, h5⟩ |
      ⟨hk, -⟩ | ⟨hk, -⟩ | ⟨-, e, K', fK', finK', charK', scope, hcase⟩
  · cases c <;> exact absurd hk (by decide)
  · have hcard' : Nat.card K = 2 := by simpa using hcard
    haveI := finK
    haveI := Fintype.ofFinite K
    haveI : CharP K 2 := charP_of_card_eq_prime (p := 2)
      (by rw [← Nat.card_eq_fintype_card, hcard'])
    have h2 : (2 : K) = 0 := two_eq_zero_of_card_two hcard'
    have hk2 : ∀ c : K, c = 0 ∨ c = 1 := eq_zero_or_eq_one_of_card_two hcard'
    have D := g2IndexTwoData h2 hk2
    have hψi := burnsideF4gG2TwoInv_psiC_injective marking
    have hψs := burnsideF4gG2TwoInv_psiC_surjective marking hGp
    set ψ := burnsideF4gG2TwoInv_psiC marking with hψdef
    have hle : ∀ X : Subgroup E, Gp ⊓ X = X := fun X => inf_eq_right.2 (hGp ▸ le_top)
    have hM1 : M₁ = (G2Native.pointParabolic K).map ψ := by
      rw [← hle M₁, hm.2.1, h2', burnsideF4gG2TwoInv_psiC_map marking]
    have hM2 : M₂ = (G2Native.lineParabolic K).map ψ := by
      rw [← hle M₂, hm.2.2, h3, burnsideF4gG2TwoInv_psiC_map marking]
    have hBo : M₁ ⊓ M₂ = (G2Native.positiveBorel K).map ψ := by
      rw [← hle (M₁ ⊓ M₂), hm.1, h1, burnsideF4gG2TwoInv_psiC_map marking]
    have hsup : G2Native.pointParabolic K ⊔ G2Native.lineParabolic K = ⊤ := by
      apply Subgroup.map_injective hψi
      rw [Subgroup.map_sup, ← hM1, ← hM2, hyp.amalgam.gen,
        Subgroup.map_top_of_surjective _ hψs]
    have hinf : G2Native.pointParabolic K ⊓ G2Native.lineParabolic K =
        G2Native.positiveBorel K := by
      apply Subgroup.map_injective hψi
      rw [Subgroup.map_inf _ _ _ hψi, ← hM1, ← hM2, hBo]
    obtain ⟨h, hh⟩ := burnsideF4gG2TwoInv_borel_conj hcard' h2 hk2
    obtain ⟨hPc, -⟩ := burnsideF4gG2TwoInv_Pc_conj hcard' h2 hk2 hh
    have hQc := burnsideF4gG2TwoInv_Qc_conj hcard' h2 hk2 hh hsup hinf
    have hBS : (G2Native.positiveBorel K).map (MulAut.conj h).toMonoidHom = (lat h2 hk2).S := by
      ext g
      rw [Subgroup.mem_map, hh g]
      simp [MulAut.conj_apply]
    set ψ' : G2Group K →* E := ψ.comp (MulAut.conj h⁻¹).toMonoidHom with hψ'def
    have hψ'i : Function.Injective ψ' := hψi.comp (MulAut.conj h⁻¹).injective
    have hψ's : Function.Surjective ψ' := hψs.comp (MulAut.conj h⁻¹).surjective
    set θ : G2Group K ≃* E := MulEquiv.ofBijective ψ' ⟨hψ'i, hψ's⟩ with hθdef
    have hθ : θ.toMonoidHom = ψ' := rfl
    have hψψ' : ψ'.comp (MulAut.conj h).toMonoidHom = ψ := by
      ext g
      simp only [hψ'def, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      congr 1
      group
    have hθ1 : M₁ = (lat h2 hk2).P₂.map θ.toMonoidHom := by
      rw [hθ, ← hPc, Subgroup.map_map, hψψ', hM1]
    have hθ2 : M₂ = (lat h2 hk2).P₁.map θ.toMonoidHom := by
      rw [hθ, ← hQc, Subgroup.map_map, hψψ', hM2]
    have hθ12 : M₁ ⊓ M₂ = (lat h2 hk2).S.map θ.toMonoidHom := by
      rw [hθ, ← hBS, Subgroup.map_map, hψψ', hBo]
    have hθinj : Function.Injective θ := θ.injective
    have hBp : IsPGroup 2 (M₁ ⊓ M₂ : Subgroup E) := by
      rw [hθ12]
      exact (lat h2 hk2).sylow.1.map _
    have hpc12 : pCoreOf 2 (M₁ ⊓ M₂) = M₁ ⊓ M₂ := burnsideF4gG2TwoInv_pCoreOf_eq_self hBp
    have hS' : pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) = (lat h2 hk2).S.map θ.toMonoidHom := by
      rw [hle, hpc12, hθ12]
    have hρS : g2RhoC h2 ∈ (lat h2 hk2).S := by
      rw [← burnsideF4gG2TwoInv_sEl32 h2]
      exact sEl_mem_S h2 hk2 (by norm_num)
    have hρ1 : g2RhoC h2 ≠ 1 := fun e => D.rho_not_mem ⟨1, by rw [map_one, e]⟩
    have hρ2 : g2RhoC h2 * g2RhoC h2 = 1 := D.sq
    have hz26S : sEl h2 26 ∈ (lat h2 hk2).S := sEl_mem_S h2 hk2 (by norm_num)
    have hz26c : sEl h2 26 ∈ ctr (lat h2 hk2).S := by
      refine burnsideF4gG2TwoInv_mem_ctr.2 ⟨hz26S, fun g hg => ?_⟩
      obtain ⟨j, hj, rfl⟩ := (mem_S_iff h2 hk2).mp hg
      rw [G2Two.Model.sEl_mulT h2 hk2 hj (by norm_num), G2Two.Model.sEl_mulT h2 hk2 (by norm_num) hj,
        G2Two.Tab.zc_chk j hj]
    have hz261 : sEl h2 26 ≠ 1 := by
      rw [← sEl_zero h2 hk2]
      exact G2Two.Model.sEl_ne h2 hk2 (by norm_num) (by norm_num) (by norm_num)
    have hz262 : sEl h2 26 * sEl h2 26 = 1 :=
      (G2Two.Model.sEl_sq h2 hk2 (by norm_num)).mpr G2Two.Tab.zz_chk
    have hθne : ∀ g : G2Group K, g ≠ 1 → θ g ≠ 1 := fun g hg e =>
      hg (hθinj (by rw [e, map_one]))
    have hθsq : ∀ g : G2Group K, g * g = 1 → θ g * θ g = 1 := fun g hg => by
      rw [← map_mul, hg, map_one]
    have hCθ : Subgroup.centralizer ({θ (g2RhoC h2)} : Set E) =
        (Subgroup.centralizer ({g2RhoC h2} : Set (G2Group K))).map θ.toMonoidHom :=
      burnsideF4gG2TwoInv_centralizer_map θ (g2RhoC h2)
    have hCθmem : ∀ c : G2Group K, θ c ∈ Subgroup.centralizer ({θ (g2RhoC h2)} : Set E) ↔
        c * g2RhoC h2 = g2RhoC h2 * c := by
      intro c
      rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
      exact ⟨fun e => hθinj e, fun e => by rw [e]⟩
    obtain ⟨haρ, hbρ, ha2, hb2, hab, hnc⟩ := burnsideF42g_g2_ab h2 hk2
    refine burnsideF42g_A42_of_lemmaB (z₀ := θ (sEl h2 26)) (tb := θ (g2RhoC h2))
      (a := θ (sEl h2 26)) (b := θ (sEl h2 21)) hyp hGp (by decide)
      (fun i j hi hj hi1 hj1 hi2 hj2 =>
        burnsideF4r_A35_G2 hyp (by norm_num) i j hi hj hi1 hj1 hi2 hj2) ?_
      (hθne _ hz261) (hθsq _ hz262) ?_ ?_ (hθne _ hρ1) (hθsq _ hρ2) ?_ ?_ ?_ ?_
      ((hCθmem _).mpr haρ) ((hCθmem _).mpr hbρ) (hθsq _ ha2) (hθsq _ hb2) (IsConj.refl _)
      ((burnsideF4gG2TwoInv_isConj_map θ).mpr hab) ?_
    ·
      rw [hpc12, hθ12, burnsideF4gG2TwoInv_ctr_map θ]
      exact ⟨_, hz26c, rfl⟩
    ·
      rw [hle, hθ2, burnsideF4gG2TwoInv_pCoreOf_map θ]
      exact ⟨_, burnsideF4gG2TwoInv_rho_mem_pCore h2 hk2, rfl⟩
    ·
      rw [hS']
      exact ⟨_, hρS, rfl⟩
    ·
      rw [burnsideF4gG2TwoInv_isConj_map θ]
      exact burnsideF42g_g2_not_conj h2 hk2
    ·
      rw [hCθ, hθ2]
      exact Subgroup.map_mono fun c hc => burnsideF4gG2TwoInv_cent_rho_le_P₁ h2 hk2
        (Subgroup.mem_centralizer_singleton_iff.mp hc)
    ·
      rw [hS', hle, hCθ, ← Subgroup.map_inf _ _ _ hθinj]
      exact burnsideF4m_isSylowTwoOf_map_inj θ.toMonoidHom hθinj (burnsideF42g_g2_sylow_rho h2 hk2)
    ·
      intro c hc hc2 hc1 hct
      obtain ⟨c', rfl⟩ := θ.surjective c
      have hc' : c' * g2RhoC h2 = g2RhoC h2 * c' := (hCθmem c').mp hc
      have hc2' : c' * c' = 1 ∨ c' * c' = g2RhoC h2 := by
        rw [← map_mul, ← map_one θ] at hc2
        rcases hc2 with e | e
        · exact Or.inl (hθinj e)
        · exact Or.inr (hθinj e)
      have hc1' : c' ≠ 1 := fun e => hc1 (by rw [e, map_one])
      have hct' : c' ≠ g2RhoC h2 := fun e => hct (by rw [e])
      rcases burnsideF42g_g2_cent_inv h2 hk2 hc' hc2' hc1' hct' with e | e
      · exact Or.inl ((burnsideF4gG2TwoInv_isConj_map θ).mpr e)
      · right
        rw [← map_mul]
        exact (burnsideF4gG2TwoInv_isConj_map θ).mpr e
    ·
      intro x hx
      obtain ⟨x', rfl⟩ := θ.surjective x
      have hx' : x' * g2RhoC h2 = g2RhoC h2 * x' := (hCθmem x').mp hx
      obtain ⟨n1, n2⟩ := hnc x' hx'
      rw [← map_inv, ← map_mul, ← map_mul, ← map_mul]
      exact ⟨fun e => n1 (hθinj e), fun e => n2 (hθinj e)⟩
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · rcases hcase with ⟨hk, -⟩ | ⟨hk, -⟩ <;> exact absurd hk (by decide)

end G2Main


end CFSG.ASVolI
