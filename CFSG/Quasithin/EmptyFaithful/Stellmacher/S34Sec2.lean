module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S34Sec1
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S34AON
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.SecIrrHss15
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.ModSecOrthNatIff

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod

namespace F53.Stellmacher

open CosetGeom F53 Equiv S42B1

namespace S34

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

open CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs
  (fixW_top_bot normalize_ker_five model5_faithful_of_fixW_top_bot secData_secModule)

theorem vbar_ker_le_cSecIn (hG : Glob H M S) {δ : Geo H M} (hδ : vtype δ = false) {n : ℕ}
    (θ : ↥(stab δ) →* Perm (Fin n)) (hker : ∀ x : ↥(stab δ), θ x = 1 ↔ (x : G) ∈ Qv δ) :
    θ.ker ≤ (cSecIn (stab δ) (Cb δ) (Vn δ)).subgroupOf (stab δ) := fun x hx =>
  Subgroup.mem_subgroupOf.mpr ((secFacts hG hδ).2.1 ((hker x).mp hx))

theorem vbar_fixW_top_eq_bot (hG : Glob H M S) {δ : Geo H M} (hδ : vtype δ = false)
    {θ : ↥(stab δ) →* Perm (Fin 5)} (hθ : Function.Surjective θ)
    (hs : IsSec (stab δ) (Cb δ) (Vn δ))
    (hk : θ.ker ≤ (cSecIn (stab δ) (Cb δ) (Vn δ)).subgroupOf (stab δ)) :
    fixW (secModule hs θ hθ hk) ⊤ = ⊥ :=
  fixW_top_bot hs θ hθ hk (secFacts hG hδ).2.2.1

theorem exists_ne_one_secModule (hG : Glob H M S) {δ : Geo H M} (hδ : vtype δ = false)
    {θ : ↥(stab δ) →* Perm (Fin 5)} (hθ : Function.Surjective θ)
    (hs : IsSec (stab δ) (Cb δ) (Vn δ))
    (hk : θ.ker ≤ (cSecIn (stab δ) (Cb δ) (Vn δ)).subgroupOf (stab δ)) :
    ∃ w : (secModule hs θ hθ hk).W, w ≠ 1 := by
  have : ∃ v ∈ Vn δ, v ∉ Cb δ := by
    by_contra h
    push Not at h
    exact (secFacts hG hδ).2.2.2 (le_antisymm hs.le h)
  obtain ⟨v, hvV, hvC⟩ := this
  exact ⟨hs.proj ⟨v, hvV⟩, fun h => hvC ((hs.proj_eq_one_iff ⟨v, hvV⟩).mp h)⟩

theorem faithful_secModule (hG : Glob H M S) {δ : Geo H M} (hδ : vtype δ = false)
    {θ : ↥(stab δ) →* Perm (Fin 5)} (hθ : Function.Surjective θ)
    (hs : IsSec (stab δ) (Cb δ) (Vn δ))
    (hk : θ.ker ≤ (cSecIn (stab δ) (Cb δ) (Vn δ)).subgroupOf (stab δ)) :
    (secModule hs θ hθ hk).Faithful :=
  model5_faithful_of_fixW_top_bot _ (vbar_fixW_top_eq_bot hG hδ hθ hs hk)
    (exists_ne_one_secModule hG hδ hθ hs hk)

theorem gen_secModule (hG : Glob H M S) {δ μ : Geo H M} (hδ : vtype δ = false)
    (hμ : μ ∈ nbrs δ) {θ : ↥(stab δ) →* Perm (Fin 5)} (hθ : Function.Surjective θ)
    (hs : IsSec (stab δ) (Cb δ) (Vn δ))
    (hk : θ.ker ≤ (cSecIn (stab δ) (Cb δ) (Vn δ)).subgroupOf (stab δ))
    (hPS : ((stab δ ⊓ stab μ).subgroupOf (stab δ)).map θ = S5Syl)
    (U : Subgroup (secModule hs θ hθ hk).W) (hU : IsInvSub (secModule hs θ hθ hk) ⊤ U)
    (hfixU : fixW (secModule hs θ hθ hk) S5Syl ≤ U) : U = ⊤ := by
  have := hs.normal_subgroupOf
  set U' : Subgroup G := (U.comap hs.proj).map (Vn δ).subtype with hU'
  have hmem : ∀ x : G, x ∈ U' ↔ ∃ hx : x ∈ Vn δ, hs.proj ⟨x, hx⟩ ∈ U := by
    intro x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, hy⟩
    · rintro ⟨hx, h⟩
      exact ⟨⟨x, hx⟩, h, rfl⟩
  have hinv : ∀ k ∈ stab δ, ∀ x ∈ U', k * x * k⁻¹ ∈ U' := by
    intro k hk' x hx
    obtain ⟨hxV, hxU⟩ := (hmem x).mp hx
    refine (hmem _).mpr ⟨hs.conj_mem_N ⟨k, hk'⟩ ⟨x, hxV⟩, ?_⟩
    have h1 := hU (θ ⟨k, hk'⟩) (Subgroup.mem_top _) _ hxU
    rw [secModule_act_proj hs θ hθ hk] at h1
    exact h1
  have hZμ : Zv μ ≤ U' := by
    intro z hz
    have hzV : z ∈ Vn δ :=
      le_iSup₂_of_le (f := fun (ν : Geo H M) (_ : ν ∈ nbrs δ) => Zv ν) μ hμ le_rfl hz
    refine (hmem z).mpr ⟨hzV, hfixU ?_⟩
    intro b hb
    rw [← hPS] at hb
    obtain ⟨t, ht, rfl⟩ := hb
    have htE : (t : G) ∈ stab δ ⊓ stab μ := Subgroup.mem_subgroupOf.mp ht
    rw [secModule_act_proj hs θ hθ hk]
    refine (hs.proj_eq_proj_iff _ _).mpr ?_
    have h1 := Subgroup.commutator_mem_commutator (Subgroup.mem_zpowers (t : G))
      ((Zv μ).inv_mem hz)
    rw [Subgroup.commutator_comm] at h1
    have h2 := (aon_edge hG hδ hμ (g := (t : G)) ⟨htE.2, htE.1⟩)
    have h3 : ⁅Zv μ, Subgroup.zpowers (t : G)⁆ ≤ Zv δ := by
      by_cases hq : (t : G) ∈ Qv μ
      · rw [h2.1 hq]; exact bot_le
      · rw [h2.2 hq]
    have h4 := Zv_le_Cb hG hδ (h3 h1)
    convert h4 using 1
    simp [commutatorElement_def, IsSec.conjN, mul_assoc]
  have hVU : Vn δ ≤ U' := by
    refine iSup₂_le fun ν hν => ?_
    obtain ⟨g, hgδ, hgν⟩ := stab_transitive_on_nbrs hμ hν
    have hν' : Zv ν = conjSub (g : G) (Zv μ) := by rw [← hgν]; exact Zv_smul g μ
    intro x hx
    rw [hν', mem_conjSub] at hx
    have h1 := hinv (g : G) hgδ _ (hZμ hx)
    have e : (g : G) * ((g : G)⁻¹ * x * (g : G)) * (g : G)⁻¹ = x := by group
    rwa [e] at h1
  rw [eq_top_iff]
  intro w _
  obtain ⟨v, rfl⟩ := hs.proj_surjective w
  exact ((hmem _).mp (hVU v.2)).2

theorem exists_vmodel (hG : Glob H M S) {δ μ : Geo H M} (hδ : vtype δ = false)
    (hμ : μ ∈ nbrs δ) :
    ∃ (θ : ↥(stab δ) →* Perm (Fin 5)) (hθ : Function.Surjective θ)
      (hs : IsSec (stab δ) (Cb δ) (Vn δ))
      (hk : θ.ker ≤ (cSecIn (stab δ) (Cb δ) (Vn δ)).subgroupOf (stab δ)),
      (∀ x : ↥(stab δ), θ x = 1 ↔ (x : G) ∈ Qv δ) ∧
      ((stab δ ⊓ stab μ).subgroupOf (stab δ)).map θ = S5Syl ∧
      (secModule hs θ hθ hk).Faithful ∧ fixW (secModule hs θ hθ hk) ⊤ = ⊥ ∧
      (∃ w : (secModule hs θ hθ hk).W, w ≠ 1) ∧
      (∀ U : Subgroup (secModule hs θ hθ hk).W, IsInvSub (secModule hs θ hθ hk) ⊤ U →
        fixW (secModule hs θ hθ hk) S5Syl ≤ U → U = ⊤) := by
  obtain ⟨n, ψ, hn, hψ, hker⟩ := exists_quotHom hG.amalg δ
  rcases hn with ⟨rfl, -⟩ | ⟨-, hv⟩
  swap
  · rw [hδ] at hv
    exact absurd hv (by decide)
  obtain ⟨Ψ, hΨs, hΨk, hPS⟩ := normalize_ker_five hψ (sylow_stab_inf_left hG.amalg hμ)
  have hΨker : ∀ x : ↥(stab δ), Ψ x = 1 ↔ (x : G) ∈ Qv δ := fun x => by
    rw [← hker x, ← MonoidHom.mem_ker, ← MonoidHom.mem_ker, hΨk]
  have hs := (secFacts hG hδ).1
  have hk := vbar_ker_le_cSecIn hG hδ Ψ hΨker
  exact ⟨Ψ, hΨs, hs, hk, hΨker, hPS, faithful_secModule hG hδ hΨs hs hk,
    vbar_fixW_top_eq_bot hG hδ hΨs hs hk, exists_ne_one_secModule hG hδ hΨs hs hk,
    fun U hU hf => gen_secModule hG hδ hμ hΨs hs hk hPS U hU hf⟩

theorem rk_eq_idx (_hG : Glob H M S) {δ : Geo H M} (_hδ : vtype δ = false)
    {θ : ↥(stab δ) →* Perm (Fin 5)} (hθ : Function.Surjective θ)
    (hs : IsSec (stab δ) (Cb δ) (Vn δ))
    (hk : θ.ker ≤ (cSecIn (stab δ) (Cb δ) (Vn δ)).subgroupOf (stab δ))
    (_hker : ∀ x : ↥(stab δ), θ x = 1 ↔ (x : G) ∈ Qv δ) {g : G} (hg : g ∈ stab δ) :
    rk δ g = idx (secModule hs θ hθ hk) (θ ⟨g, hg⟩) := by
  have := hs.normal_subgroupOf
  exact (secData_secModule hs θ hθ hk).secIdx_eq_idx hs.le hg

theorem good_iff_iso (hG : Glob H M S) {δ : Geo H M} (hδ : vtype δ = false)
    {θ : ↥(stab δ) →* Perm (Fin 5)} (hθ : Function.Surjective θ)
    (hs : IsSec (stab δ) (Cb δ) (Vn δ))
    (hk : θ.ker ≤ (cSecIn (stab δ) (Cb δ) (Vn δ)).subgroupOf (stab δ))
    (_hker : ∀ x : ↥(stab δ), θ x = 1 ↔ (x : G) ∈ Qv δ) :
    Good δ ↔ (Nonempty ((secModule hs θ hθ hk).Iso orth) ∨
      Nonempty ((secModule hs θ hθ hk).Iso nat)) := by
  have hsf := secFacts hG hδ
  have hq := quot_stab_five hG.amalg hδ
  have := hs.normal_subgroupOf
  have hnorm : IsNormalIn (stab δ) (Vn δ) (Vn δ) :=
    ⟨le_rfl, fun g hg x hx => (Subgroup.mem_normalizer_iff.mp (hs.normN hg) x).mp hx⟩
  have hnormC : IsNormalIn (stab δ) (Vn δ) (Cb δ) :=
    ⟨hs.le, fun g hg x hx => hs.conj_mem_L hg hx⟩
  have key : Good δ ↔ IsNatOrOrthMod (stab δ) (Vn δ) (Cb δ) := by
    unfold Good
    rw [isNatOrOrthMod_iff hq hsf.2.1 hs, or_comm]
  rw [key]
  constructor
  · rintro ⟨hstep, hcard⟩
    have hirr := secModule_isIrred_of_isChiefStep hs θ hθ hk hstep
    have hc : Nat.card (secModule hs θ hθ hk).W = 16 :=
      (natCard_secModule hs θ hθ hk).trans hcard
    have hnt : ∃ σ w, (secModule hs θ hθ hk).act σ w ≠ w := by
      by_contra hall
      push Not at hall
      have := card_le_two_of_irred_trivial hirr hall
      omega
    exact model5_irred_classification _ hirr hnt
  · intro h
    have key2 : (secModule hs θ hθ hk).IsIrred → Nat.card (secModule hs θ hθ hk).W = 16 →
        IsNatOrOrthMod (stab δ) (Vn δ) (Cb δ) := fun hirr hc =>
      ⟨isChiefStep_of_secModule_isIrred hs θ hθ hk hnorm hnormC hirr,
        (natCard_secModule hs θ hθ hk).symm.trans hc⟩
    rcases h with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
    · exact key2 (orth_isIrred.of_iso e.symm) (e.card_eq.trans card_orth)
    · exact key2 (nat_isIrred.of_iso e.symm) (e.card_eq.trans card_nat)

theorem NG.rk_gt (hG : Glob H M S) (hirr : IrrSecSec) (hng : NG H M) {δ : Geo H M}
    (hδ : vtype δ = false) {g : G} (hg : g ∈ stab δ) (ho : OverInv δ g) : 8 < rk δ g := by
  by_contra h
  exact hng δ hδ (good_of_overInv hG hirr hδ hg ho (not_lt.mp h))

theorem idx_eq_two_pow {n : ℕ} (M : Model n) (σ : Perm (Fin n)) : ∃ j : ℕ, idx M σ = 2 ^ j := by
  have := M.fin
  have hp : IsPGroup 2 M.W := fun w => ⟨1, by simpa [pow_two] using M.sq w⟩
  obtain ⟨m, hm⟩ := hp.exists_card_eq
  have hd : idx M σ ∣ 2 ^ m := hm ▸ Subgroup.index_dvd_card _
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
  exact ⟨j, hj⟩

theorem idx_ne_one_of_faithful {n : ℕ} {M : Model n} (hf : M.Faithful) {σ : Perm (Fin n)}
    (hσ : σ ≠ 1) : idx M σ ≠ 1 := by
  intro h
  have htop : fixW M (Subgroup.zpowers σ) = ⊤ := Subgroup.index_eq_one.mp h
  apply hσ
  apply hf
  ext w
  have := (eq_top_iff.mp htop (Subgroup.mem_top w)) σ (Subgroup.mem_zpowers σ)
  simpa using this

theorem NG.four_le_rk (hG : Glob H M S) (h15 : Hss15Sec) (hng : NG H M) {δ : Geo H M}
    (hδ : vtype δ = false) {g : G} (hg : g ∈ stab δ) (hgQ : g ∉ Qv δ) : 4 ≤ rk δ g := by
  obtain ⟨μ, hμ⟩ := exists_adj δ
  obtain ⟨θ, hθ, hs, hk, hker, -, hf, -⟩ := exists_vmodel hG hδ hμ
  have hr := rk_eq_idx hG hδ hθ hs hk hker hg
  have h1 : rk δ g ≠ 1 := by
    rw [hr]
    exact idx_ne_one_of_faithful hf fun h => hgQ ((hker _).mp h)
  have h2 : rk δ g ≠ 2 := fun h => hng δ hδ (good_of_transv hG h15 hδ hg h)
  obtain ⟨j, hj⟩ := idx_eq_two_pow (secModule hs θ hθ hk) (θ ⟨g, hg⟩)
  rw [hr, hj] at h1 h2 ⊢
  rcases j with _ | _ | j
  · exact absurd rfl h1
  · exact absurd rfl h2
  · calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (j + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)

end S34

end F53.Stellmacher

end CFSG.Quasithin
