module

public import CFSG.RankThree.PartOne.N143.JAct
public import CFSG.RankThree.PartOne.N143.JSL2

public section

namespace CFSG.RankThree.PartOne.N143

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open CFSG.RankThree.PartOne.KFOUT3 (SL3 Tor IsZeta diagSL tSep tNon ent ent_ext diagSL_mem_Tor tSep_mem)
open scoped commutatorElement

section Abstract

theorem conj_commutator_le {G : Type} [Group G] (u : G) {N : Subgroup G}
    (hN : ∀ n ∈ N, u * n * u⁻¹ ∈ N) : ∀ y ∈ ⁅N, N⁆, u * y * u⁻¹ ∈ ⁅N, N⁆ := by
  intro y hy
  have h1 : (⁅N, N⁆).map (MulAut.conj u).toMonoidHom ≤ ⁅N, N⁆ := by
    rw [Subgroup.map_commutator]
    apply Subgroup.commutator_mono <;> rintro _ ⟨n, hn, rfl⟩ <;> exact hN n hn
  exact h1 ⟨y, hy, rfl⟩

variable {G H : Type} [Group G] [Group H]

theorem iter_stab (u : G) (S : Subgroup G) (h : ∀ x ∈ S, u * x * u⁻¹ ∈ S) :
    ∀ m : ℕ, ∀ x ∈ S, u ^ m * x * (u ^ m)⁻¹ ∈ S := by
  intro m
  induction m with
  | zero =>
    intro x hx
    simpa using hx
  | succ m ih =>
    intro x hx
    have e : u ^ (m + 1) * x * (u ^ (m + 1))⁻¹ = u ^ m * (u * x * u⁻¹) * (u ^ m)⁻¹ := by
      rw [pow_succ, mul_inv_rev]
      group
    rw [e]
    exact ih _ (h x hx)

theorem iter_sub (u : G) (S T : Subgroup G) (hST : ∀ x ∈ S, u * x * u⁻¹ ∈ T)
    (hTT : ∀ x ∈ T, u * x * u⁻¹ ∈ T) :
    ∀ m : ℕ, ∀ x ∈ S, u ^ (m + 1) * x * (u ^ (m + 1))⁻¹ ∈ T := by
  intro m
  induction m with
  | zero =>
    intro x hx
    simpa using hST x hx
  | succ m ih =>
    intro x hx
    have e : u ^ (m + 1 + 1) * x * (u ^ (m + 1 + 1))⁻¹ =
        u * (u ^ (m + 1) * x * (u ^ (m + 1))⁻¹) * u⁻¹ := by
      rw [pow_succ' u (m + 1), mul_inv_rev]
      group
    rw [e]
    exact hTT _ (ih x hx)

theorem comap_dichotomy (φ : H →* G) (hφ : Function.Injective φ) (u : G) (h : H)
    (T P₁ P₂ : Subgroup H) (hsq : ∀ M ∈ T, M * M = 1)
    (hTh : ∀ k : ℕ, ∀ M ∈ T, h ^ k * M * (h ^ k)⁻¹ ∈ T)
    (hcls : ∀ W : Subgroup H, (∀ M ∈ W, M * M = 1) → (∀ M ∈ W, h * M * h⁻¹ ∈ W) →
      W ≤ P₁ ∨ W ≤ P₂)
    (hrange : ∀ y ∈ φ.range, u * y * u⁻¹ ∈ φ.range) (hh : ∃ k : ℕ, u⁻¹ * φ h * u = φ h ^ k) :
    (∀ x ∈ T.map φ, u * x * u⁻¹ ∈ P₁.map φ) ∨ (∀ x ∈ T.map φ, u * x * u⁻¹ ∈ P₂.map φ) := by
  obtain ⟨k, hk⟩ := hh
  let Su : Subgroup G := (T.map φ).map (MulAut.conj u).toMonoidHom
  have hSu : ∀ y, y ∈ Su ↔ ∃ N ∈ T, u * φ N * u⁻¹ = y := by
    intro y
    constructor
    · rintro ⟨y', ⟨N, hN, rfl⟩, rfl⟩
      exact ⟨N, hN, rfl⟩
    · rintro ⟨N, hN, rfl⟩
      exact ⟨φ N, ⟨N, hN, rfl⟩, rfl⟩
  have hW1 : ∀ M ∈ Su.comap φ, M * M = 1 := by
    intro M hM
    obtain ⟨N, hN, hNM⟩ := (hSu _).1 hM
    apply hφ
    rw [map_mul, ← hNM, map_one]
    calc u * φ N * u⁻¹ * (u * φ N * u⁻¹) = u * φ (N * N) * u⁻¹ := by rw [map_mul]; group
      _ = 1 := by rw [hsq N hN, map_one]; group
  have hW2 : ∀ M ∈ Su.comap φ, h * M * h⁻¹ ∈ Su.comap φ := by
    intro M hM
    obtain ⟨N, hN, hNM⟩ := (hSu _).1 hM
    refine (hSu _).2 ⟨h ^ k * N * (h ^ k)⁻¹, hTh k N hN, ?_⟩
    simp only [map_mul, map_inv, map_pow]
    rw [← hNM, ← hk]
    group
  have key : ∀ P : Subgroup H, Su.comap φ ≤ P → ∀ x ∈ T.map φ, u * x * u⁻¹ ∈ P.map φ := by
    intro P hP x hx
    obtain ⟨N, hN, rfl⟩ := hx
    have hy : u * φ N * u⁻¹ ∈ Su := (hSu _).2 ⟨N, hN, rfl⟩
    obtain ⟨M, hM⟩ := hrange (φ N) ⟨N, rfl⟩
    refine Subgroup.mem_map.2 ⟨M, hP ?_, hM⟩
    show φ M ∈ Su
    rw [hM]
    exact hy
  rcases hcls (Su.comap φ) hW1 hW2 with h1 | h1
  · exact Or.inl (key _ h1)
  · exact Or.inr (key _ h1)

theorem normalizes_of_dichotomy (S₁ S₂ : Subgroup G) (hne : ¬ S₁ ≤ S₂) (R : Subgroup G)
    (hR : IsPGroup 3 R)
    (hd : ∀ u ∈ R, ((∀ x ∈ S₁, u * x * u⁻¹ ∈ S₁) ∨ (∀ x ∈ S₁, u * x * u⁻¹ ∈ S₂)) ∧
      ((∀ x ∈ S₂, u * x * u⁻¹ ∈ S₁) ∨ (∀ x ∈ S₂, u * x * u⁻¹ ∈ S₂))) :
    R ≤ Subgroup.normalizer (S₁ : Set G) := by
  have hord : ∀ u ∈ R, ∃ e : ℕ, u ^ (3 ^ e) = 1 := by
    intro u hu
    obtain ⟨e, he⟩ := hR ⟨u, hu⟩
    exact ⟨e, congrArg Subtype.val he⟩
  have hS1 : ∀ u ∈ R, ∀ x ∈ S₁, u * x * u⁻¹ ∈ S₁ := by
    intro u hu
    obtain ⟨hd1, hd2⟩ := hd u hu
    rcases hd1 with h1 | h1
    · exact h1
    · have h2 : ∀ x ∈ S₂, u * x * u⁻¹ ∈ S₁ := by
        rcases hd2 with h2 | h2
        · exact h2
        · exfalso
          apply hne
          intro x hx
          obtain ⟨e, he⟩ := hord u hu
          obtain ⟨m, hm⟩ : ∃ m, 3 ^ e = m + 1 :=
            ⟨3 ^ e - 1, (Nat.sub_add_cancel (Nat.one_le_pow _ _ (by norm_num))).symm⟩
          have := iter_sub u S₁ S₂ h1 h2 m x hx
          rw [← hm, he] at this
          simpa using this
      have h3 : ∀ x ∈ S₁, (u * u) * x * (u * u)⁻¹ ∈ S₁ := by
        intro x hx
        have e : u * u * x * (u * u)⁻¹ = u * (u * x * u⁻¹) * u⁻¹ := by group
        rw [e]
        exact h2 _ (h1 x hx)
      obtain ⟨e, he⟩ := hord u hu
      obtain ⟨k, hk⟩ : Odd (3 ^ e) := Odd.pow (by decide)
      have hu' : u = (u * u) ^ (k + 1) := by
        rw [← sq, ← pow_mul, show 2 * (k + 1) = 3 ^ e + 1 by rw [hk]; ring, pow_succ, he, one_mul]
      intro x hx
      have := iter_stab (u * u) S₁ h3 (k + 1) x hx
      rw [← hu'] at this
      exact this
  intro u hu
  refine Subgroup.mem_normalizer_iff.2 fun x => ⟨fun hx => hS1 u hu x hx, fun hx => ?_⟩
  have h1 := hS1 u⁻¹ (R.inv_mem hu) _ hx
  have e : u⁻¹ * (u * x * u⁻¹) * u⁻¹⁻¹ = x := by group
  rw [e] at h1
  exact h1

theorem normalizes_P₁ (φ : H →* G) (hφ : Function.Injective φ) (h : H) (P₁ P₂ : Subgroup H)
    (hsq₁ : ∀ M ∈ P₁, M * M = 1) (hsq₂ : ∀ M ∈ P₂, M * M = 1)
    (hh₁ : ∀ k : ℕ, ∀ M ∈ P₁, h ^ k * M * (h ^ k)⁻¹ ∈ P₁)
    (hh₂ : ∀ k : ℕ, ∀ M ∈ P₂, h ^ k * M * (h ^ k)⁻¹ ∈ P₂)
    (hcls : ∀ W : Subgroup H, (∀ M ∈ W, M * M = 1) → (∀ M ∈ W, h * M * h⁻¹ ∈ W) →
      W ≤ P₁ ∨ W ≤ P₂)
    (hne : ¬ P₁ ≤ P₂) (R : Subgroup G) (hR : IsPGroup 3 R)
    (hrange : ∀ u ∈ R, ∀ y ∈ φ.range, u * y * u⁻¹ ∈ φ.range)
    (hh : ∀ u ∈ R, ∃ k : ℕ, u⁻¹ * φ h * u = φ h ^ k) :
    R ≤ Subgroup.normalizer ((P₁.map φ : Subgroup G) : Set G) := by
  have hne' : ¬ P₁.map φ ≤ P₂.map φ := by
    intro hle
    apply hne
    intro M hM
    obtain ⟨N, hN, hNM⟩ := hle (Subgroup.mem_map_of_mem φ hM)
    have : N = M := hφ hNM
    rw [← this]
    exact hN
  refine normalizes_of_dichotomy (P₁.map φ) (P₂.map φ) hne' R hR (fun u hu => ⟨?_, ?_⟩)
  · exact comap_dichotomy φ hφ u h P₁ P₁ P₂ hsq₁ hh₁ hcls (hrange u hu) (hh u hu)
  · exact comap_dichotomy φ hφ u h P₂ P₁ P₂ hsq₂ hh₂ hcls (hrange u hu) (hh u hu)

end Abstract

section Model

variable {K : Type} [Field K]

theorem blkSL_hmat (ζ : Kˣ) (hv0 : ∏ k, tSep ζ 0 1 k = 1) :
    (blkSL (hmat ζ) : SL3 K) = diagSL (tSep ζ 0 1) hv0 := by
  have e0 : tSep ζ 0 1 0 = ζ := KFU.torusElt_apply_left (by decide) ζ
  have e1 : tSep ζ 0 1 1 = ζ⁻¹ := KFU.torusElt_apply_right (by decide) ζ
  have e2' : tSep ζ 0 1 2 = 1 := KFU.torusElt_apply_other (by decide) (by decide) ζ
  apply ent_ext
  intro a b
  rw [KFOUT3.diagSL_apply]
  fin_cases a <;> fin_cases b <;> simp [ent, coe_blkSL, blkMat, e2_hmat_00, e2_hmat_01, e2_hmat_10, e2_hmat_11, e0, e1, e2']

end Model

theorem jLemmaKt_holds (hGA : CFSG.Open.GriessAllModelsStatement) :
    JLemmaKt := by
  intro G _ _ p A c J h R hR hRN hRs
  classical
  obtain ⟨f, -, hf, hm⟩ := h.model
  obtain ⟨K, hKf, hKfin, hK, ρ, hρ⟩ := exists_psl3Data hGA h hf hm
  have hp := h.hyp.prime
  have h5 := Sec12Three.five_le h.hyp
  have hchar : CharP K 2 := charP_two_of_card hK
  have hf1 : 1 ≤ f := hm.1.2.1
  have hf3 := three_le_of_dvd_pred h5 hf1 hf
  have h4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 ≤ 2 ^ 3 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf3
  obtain ⟨ζ, hζ⟩ := exists_isZeta hp h5 (by rw [hK]; exact hf)
  have hv0 : ∏ k, tSep ζ 0 1 k = 1 := KFU.prod_torusElt 0 1 ζ
  have hz : tNon ζ 2 ∈ Tor p K := KFOUT3.tNon_mem hζ 2
  have hzT : ρ (tNon ζ 2) ∈ Tof A J := hρ.map_torus ▸ Subgroup.mem_map_of_mem ρ hz
  have hw : diagSL (tSep ζ 0 1) hv0 ∈ Tor p K := tSep_mem hζ (by decide)
  have hwT : ρ (diagSL (tSep ζ 0 1) hv0) ∈ Tof A J :=
    hρ.map_torus ▸ Subgroup.mem_map_of_mem ρ hw
  have hφh : blkφ ρ (hmat ζ) = ρ (diagSL (tSep ζ 0 1) hv0) := by
    rw [blkφ_apply, blkSL_hmat ζ hv0]
  have hφinj := blkφ_injective hρ
  have hN' : ∀ u ∈ R, ∀ n ∈ J ⊓ Subgroup.centralizer ({ρ (tNon ζ 2)} : Set G),
      u * n * u⁻¹ ∈ J ⊓ Subgroup.centralizer ({ρ (tNon ζ 2)} : Set G) := by
    intro u hu n hn
    refine Subgroup.mem_inf.2 ⟨(Subgroup.mem_normalizer_iff.1 (hRN hu).1 n).1 hn.1, ?_⟩
    obtain ⟨k₂, hk₂⟩ := hRs u⁻¹ (R.inv_mem hu)
    have e1 : u⁻¹ * ρ (tNon ζ 2) * u = ρ (tNon ζ 2) ^ k₂ := by
      have := hk₂ _ hzT
      rwa [inv_inv] at this
    have hcomm : n * ρ (tNon ζ 2) ^ k₂ = ρ (tNon ζ 2) ^ k₂ * n :=
      (Commute.pow_right (Subgroup.mem_centralizer_singleton_iff.1 hn.2) k₂).eq
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc u * n * u⁻¹ * ρ (tNon ζ 2) = u * n * (u⁻¹ * ρ (tNon ζ 2) * u) * u⁻¹ := by group
      _ = u * n * ρ (tNon ζ 2) ^ k₂ * u⁻¹ := by rw [e1]
      _ = u * (n * ρ (tNon ζ 2) ^ k₂) * u⁻¹ := by group
      _ = u * (ρ (tNon ζ 2) ^ k₂ * n) * u⁻¹ := by rw [hcomm]
      _ = (u * ρ (tNon ζ 2) ^ k₂ * u⁻¹) * (u * n * u⁻¹) := by group
      _ = ρ (tNon ζ 2) * (u * n * u⁻¹) := by rw [← e1]; group
  have hK'eq : (blkφ ρ).range = ⁅J ⊓ Subgroup.centralizer ({ρ (tNon ζ 2)} : Set G),
      J ⊓ Subgroup.centralizer ({ρ (tNon ζ 2)} : Set G)⁆ := by
    rw [hρ.commutator_inf_centralizer_tNon hp hζ h4, map_blkSL_range_eq]
  have hrange : ∀ u ∈ R, ∀ y ∈ (blkφ ρ).range, u * y * u⁻¹ ∈ (blkφ ρ).range := by
    intro u hu y hy
    rw [hK'eq] at hy ⊢
    exact conj_commutator_le u (hN' u hu) y hy
  have hh : ∀ u ∈ R, ∃ k : ℕ, u⁻¹ * blkφ ρ (hmat ζ) * u = blkφ ρ (hmat ζ) ^ k := by
    intro u hu
    obtain ⟨k, hk⟩ := hRs u⁻¹ (R.inv_mem hu)
    refine ⟨k, ?_⟩
    have := hk _ hwT
    rw [inv_inv] at this
    rw [hφh]
    exact this
  have hnorm := normalizes_P₁ (blkφ ρ) hφinj (hmat ζ) (Uplus K) (Uminus K)
    (fun M hM => Uplus_sq hM) (fun M hM => Uminus_sq hM)
    (fun k M hM => hmat_pow_conj_Uplus ζ k hM) (fun k M hM => hmat_pow_conj_Uminus ζ k hM)
    (fun W hsq hn => sl2_two_group_cases hζ.sq hsq hn) Uplus_not_le_Uminus R hR hrange hh
  refine ⟨(Uplus K).map (blkφ ρ), ?_, ?_, ?_, hnorm⟩
  · intro hbot
    have h1 : blkφ ρ trv ∈ (Uplus K).map (blkφ ρ) := Subgroup.mem_map_of_mem _ trv_mem_Uplus
    rw [hbot, Subgroup.mem_bot] at h1
    exact trv_ne_one (hφinj (h1.trans (map_one _).symm))
  · intro g
    obtain ⟨N, hN, hNg⟩ := g.2
    refine ⟨1, Subtype.ext ?_⟩
    show (g : G) ^ (2 ^ 1) = 1
    have h1 : blkφ ρ N * blkφ ρ N = 1 := by rw [← map_mul, Uplus_sq hN, map_one]
    calc (g : G) ^ (2 ^ 1) = blkφ ρ N * blkφ ρ N := by rw [← hNg, pow_one, sq]
      _ = 1 := h1
  · rintro y ⟨N, -, rfl⟩
    rw [← hρ.range_eq]
    exact ⟨blkSL N, rfl⟩

end CFSG.RankThree.PartOne.N143
