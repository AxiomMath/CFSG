module

public import CFSG.Quasithin.EmptyFaithful.SBd16A6

public section

namespace CFSG.Quasithin.SBd14

open CFSG.QuasithinUnique CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.Quasithin

section AutL34

theorem card_le_of_isPGroup_mulAut_L34 {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 4)
    (B : Subgroup (MulAut (projectiveSL 3 K))) (hB : IsPGroup 2 ↥B) : Nat.card ↥B ≤ 2 ^ 8 := by
  classical
  have hσ : ∀ a, frobeniusEquiv K 2 a = a ^ 2 := fun a => frobeniusEquiv_apply K 2 a
  obtain ⟨hcenter, hunits, ⟨e, -⟩, -⟩ :=
    LinearThreeFourOuter.linear_three_four_outer_quotient_rank_two_restriction K hK _ hσ
  have hq : Nat.card (MulAut (projectiveSL 3 K) ⧸
      LinearThreeFourOuter.innerAutGroup (projectiveSL 3 K)) = 12 := by
    rw [Nat.card_congr e.toEquiv, SemidirectProduct.card, hunits, Nat.card_prod]
    simp
  have hinj : Function.Injective
      (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro g hg
    rw [MonoidHom.mem_ker] at hg
    have hgc : g ∈ Subgroup.center (projectiveSL 3 K) := by
      rw [Subgroup.mem_center_iff]
      intro y
      have h := congrArg (fun φ : MulAut (projectiveSL 3 K) => φ y) hg
      simp only [MulAut.conj_apply, MulAut.one_apply] at h
      calc y * g = (g * y * g⁻¹) * g := by rw [h]
        _ = g * y := by group
    rw [hcenter] at hgc
    exact hgc
  have hinn : Nat.card (LinearThreeFourOuter.innerAutGroup (projectiveSL 3 K)) =
      Nat.card (projectiveSL 3 K) :=
    (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hAut : Nat.card (MulAut (projectiveSL 3 K)) = 12 * Nat.card (projectiveSL 3 K) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup
      (LinearThreeFourOuter.innerAutGroup (projectiveSL 3 K)), hq, hinn]
  obtain ⟨-, hUidx⟩ := K1.isSylowTwoOf_top_iff.mp (SBd9.isSylowTwoOf_projUnitriangular (K := K))
  have hUcard : Nat.card (projUnitriangular 3 K) = 2 ^ 6 := by
    rw [card_projUnitriangular, hK]
    norm_num
  have hP : Nat.card (projectiveSL 3 K) = 2 ^ 6 * (projUnitriangular 3 K).index := by
    rw [← hUcard, Subgroup.card_mul_index]
  have hodd : Odd (projUnitriangular 3 K).index := by
    rcases Nat.even_or_odd (projUnitriangular 3 K).index with h | h
    · exact absurd (even_iff_two_dvd.mp h) hUidx
    · exact h
  have hfin : Finite (MulAut (projectiveSL 3 K)) :=
    Nat.finite_of_card_ne_zero (by rw [hAut]; exact Nat.mul_ne_zero (by norm_num) Nat.card_pos.ne')
  obtain ⟨n, hn⟩ := hB.exists_card_eq
  have hdvd : Nat.card ↥B ∣ Nat.card (MulAut (projectiveSL 3 K)) := Subgroup.card_subgroup_dvd_card B
  rw [hn, hAut, hP] at hdvd
  have h8 : 2 ^ n ∣ 2 ^ 8 * (3 * (projUnitriangular 3 K).index) := by
    have e8 : 12 * (2 ^ 6 * (projUnitriangular 3 K).index) =
        2 ^ 8 * (3 * (projUnitriangular 3 K).index) := by ring
    rwa [e8] at hdvd
  have hcop : Nat.Coprime (2 ^ n) (3 * (projUnitriangular 3 K).index) :=
    Nat.Coprime.pow_left n (Nat.coprime_two_left.mpr (Odd.mul (by decide) hodd))
  have h8' : 2 ^ n ∣ 2 ^ 8 := hcop.dvd_of_dvd_mul_right h8
  rw [hn]
  exact Nat.le_of_dvd (by positivity) h8'

end AutL34

section Main

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}

theorem RestHyp.card_Q (r : RestHyp T Mc M V₁ V₂ Yp I L t) (h113 : StageLemma14113) :
    Nat.card ↥(Sgp153 T V₁ ⊓ L) = 256 := by
  classical
  obtain ⟨K, _, _, _, ρ, hK4, hmod⟩ := exists_borelModel r.ctx.c33.center_eq r.sylow r.hn2
  have hQL : Sgp153 T V₁ ⊓ L ≤ L := r.sylow.1
  set Q' : Subgroup ↥L := (Sgp153 T V₁ ⊓ L).subgroupOf L
  have hcardQ : Nat.card ↥Q' = Nat.card ↥(Sgp153 T V₁ ⊓ L) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQL).toEquiv
  let f : ↥Q' →* projectiveSL 3 K := ρ.comp Q'.subtype
  have hrange : f.range = projUnitriangular 3 K := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    exact hmod.map_eq
  have hker : f.ker = ρ.ker.subgroupOf Q' := (MonoidHom.comap_ker ρ Q'.subtype).symm
  have hkerle : ρ.ker ≤ Q' := hmod.ker_le r.sylow
  have hcardker : Nat.card ↥f.ker = Nat.card ↥ρ.ker := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hkerle).toEquiv
  have hZ : Nat.card ↥ρ.ker = 4 := by
    have h2 : Nat.card ↥(centerOf L) = Nat.card ↥(Subgroup.center ↥L) := by
      rw [SBd9.centerOf_eq_map]
      exact Subgroup.card_map_of_injective L.subtype_injective
    rw [hmod.ker_eq, ← h2, ← r.V₁_eq_center h113]
    exact r.ctx.hyp.decomp.card₁
  have hU : Nat.card ↥f.range = 2 ^ 6 := by
    rw [hrange, card_projUnitriangular, hK4]
    norm_num
  have h1 : Nat.card ↥f.ker * f.ker.index = Nat.card ↥Q' := Subgroup.card_mul_index f.ker
  rw [Subgroup.index_ker, hcardker, hZ, hU] at h1
  omega

theorem RestHyp.card_S_le (r : RestHyp T Mc M V₁ V₂ Yp I L t) (h113 : StageLemma14113) :
    Nat.card ↥(Sgp153 T V₁) ≤ 1024 := by
  classical
  have hyp : Hyp153 G T Mc M := r.ctx.hyp.hyp
  have D0 := r.ctx.hyp.decomp
  obtain ⟨K, _, _, _, ρ, hK4, hmod⟩ := exists_borelModel r.ctx.c33.center_eq r.sylow r.hn2
  have hperf : Group.IsPerfect ↥L := r.ctx.c33.quasisimple.1
  have hS2 : IsPGroup 2 ↥(Sgp153 T V₁) := hyp.qtfe.sylow.1.to_le inf_le_left
  have hSL : Sgp153 T V₁ ≤ Subgroup.normalizer (L : Set G) := r.S_le_L
  let φ : ↥(Sgp153 T V₁) →* MulAut ↥L := (conjAct L).comp (Subgroup.inclusion hSL)
  have hφ : ∀ (s : ↥(Sgp153 T V₁)) (x : ↥L),
      ((φ s x : ↥L) : G) = (s : G) * (x : G) * (s : G)⁻¹ := fun s x =>
    Subgroup.normalizerMonoidHom_apply_apply_coe L
      (Subgroup.inclusion le_rfl (Subgroup.inclusion hSL s)) x
  have hex : ∀ s : ↥(Sgp153 T V₁), ∃ α : MulAut (projectiveSL 3 K),
      ∀ x : ↥L, α (ρ x) = ρ (φ s x) :=
    fun s => exists_induced_aut hmod.surj hmod.ker_eq (φ s)
  choose α hα using hex
  have hαmul : ∀ s s' : ↥(Sgp153 T V₁), α (s * s') = α s * α s' := by
    intro s s'
    ext p
    obtain ⟨x, rfl⟩ := hmod.surj p
    calc α (s * s') (ρ x) = ρ (φ (s * s') x) := hα _ x
      _ = ρ (φ s (φ s' x)) := by rw [map_mul, MulAut.mul_apply]
      _ = α s (ρ (φ s' x)) := (hα s _).symm
      _ = α s (α s' (ρ x)) := by rw [hα s' x]
      _ = (α s * α s') (ρ x) := rfl
  let Φ : ↥(Sgp153 T V₁) →* MulAut (projectiveSL 3 K) := MonoidHom.mk' α hαmul
  have hΦ : ∀ s, Φ s = α s := fun _ => rfl
  have hV₁S : V₁ ≤ Sgp153 T V₁ := le_inf (D0.le₁.trans hyp.VZ_le_T) Subgroup.le_normalizer
  have hkerΦ : Φ.ker = V₁.subgroupOf (Sgp153 T V₁) := by
    ext s
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hΦ]
    constructor
    · intro h1
      have hψ : φ s = 1 := by
        apply eq_one_of_central_perfect hperf
        intro x
        rw [← hmod.ker_eq, MonoidHom.mem_ker, map_mul, map_inv, ← hα s x, h1, MulAut.one_apply,
          mul_inv_cancel]
      have hc : (s : G) ∈ Subgroup.centralizer (L : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        have h2 := congrArg (fun ψ : MulAut ↥L => ((ψ ⟨y, hy⟩ : ↥L) : G)) hψ
        simp only [hφ, MulAut.one_apply] at h2
        have h3 : (s : G) * y = y * (s : G) :=
          calc (s : G) * y = ((s : G) * y * (s : G)⁻¹) * (s : G) := by group
            _ = y * (s : G) := by rw [h2]
        exact h3.symm
      exact (r.CSL_eq h113).le ⟨s.2, hc⟩
    · intro h1
      have hc : (s : G) ∈ Sgp153 T V₁ ⊓ Subgroup.centralizer (L : Set G) := (r.CSL_eq h113).ge h1
      have hψ : φ s = 1 := by
        ext x
        rw [MulAut.one_apply, hφ]
        have h2 : (x : G) * (s : G) = (s : G) * (x : G) := Subgroup.mem_centralizer_iff.mp hc.2 x x.2
        calc (s : G) * x * (s : G)⁻¹ = x * s * (s : G)⁻¹ := by rw [h2]
          _ = x := by group
      ext p
      obtain ⟨x, rfl⟩ := hmod.surj p
      rw [hα s x, hψ, MulAut.one_apply, MulAut.one_apply]
  have hcardker : Nat.card ↥Φ.ker = 4 := by
    rw [hkerΦ, ← D0.card₁]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hV₁S).toEquiv
  have hrange2 : IsPGroup 2 ↥Φ.range :=
    hS2.of_surjective Φ.rangeRestrict Φ.rangeRestrict_surjective
  have hrange : Nat.card ↥Φ.range ≤ 2 ^ 8 := card_le_of_isPGroup_mulAut_L34 hK4 Φ.range hrange2
  have h1 : Nat.card ↥Φ.ker * Φ.ker.index = Nat.card ↥(Sgp153 T V₁) := Subgroup.card_mul_index Φ.ker
  rw [Subgroup.index_ker, hcardker] at h1
  omega

theorem RestHyp.R_eq_Q (r : RestHyp T Mc M V₁ V₂ Yp I L t) (h113 : StageLemma14113) :
    T ⊓ Subgroup.centralizer (VZ T M : Set G) = Sgp153 T V₁ ⊓ L := by
  classical
  have hyp : Hyp153 G T Mc M := r.ctx.hyp.hyp
  have D0 := r.ctx.hyp.decomp
  have hV := hyp.elemAbelian
  have hTN : T ≤ Subgroup.normalizer (VZ T M : Set G) := hyp.T_le.trans hyp.le_normalizer
  obtain ⟨hV', L₁, L₂, tb, hS, -, -, -⟩ := D0.model
  have hT8 : Nat.card ↥(autI hV T) = 8 := hS.card_T hyp.isSylowTwoOf_autI
  have h1 : 8 * Nat.card ↥(T ⊓ Subgroup.centralizer (VZ T M : Set G)) = Nat.card ↥T := by
    rw [← hT8]
    exact card_autI_mul_card_inf hV hTN
  have h2 : 2 * Nat.card ↥(Sgp153 T V₁) = Nat.card ↥T := by
    have h := Subgroup.relIndex_mul_card (Sgp153 T V₁) T
    rw [inf_eq_left.2 (inf_le_left : Sgp153 T V₁ ≤ T), D0.relIndex_nS hyp] at h
    exact h
  have h3 := r.card_S_le h113
  have h4 := r.card_Q h113
  have hQR : Sgp153 T V₁ ⊓ L ≤ T ⊓ Subgroup.centralizer (VZ T M : Set G) :=
    le_inf (inf_le_left.trans inf_le_left) r.hQV
  exact (Subgroup.eq_of_le_of_card_ge hQR (by omega)).symm

end Main

end CFSG.Quasithin.SBd14
