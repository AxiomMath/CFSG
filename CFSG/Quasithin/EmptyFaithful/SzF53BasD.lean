module

public import CFSG.Quasithin.EmptyFaithful.SzF53BasC
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S152X CFSG.Quasithin.F7

namespace F53

variable {G : Type} [Group G] [Finite G]

open CosetGeom

variable {H M S : Subgroup G}

theorem Qv_eq_iInf (hA : F53Amalgam H M S) (δ : Geo H M) :
    Qv δ = ⨅ (μ : Geo H M) (_ : μ ∈ nbrs δ), stab δ ⊓ stab μ := by
  rw [← Qv_eq_ballStab_one hA δ]
  apply le_antisymm
  · refine le_iInf₂ fun μ hμ => le_inf (ballStab_le_stab 1 δ) ?_
    exact ballStab_le_stab_of_dist_le
      (dist_eq_one_iff_adj.mpr (show (graph (H ⊔ M) H M).Adj δ μ from hμ)).le
  · intro x hx
    rw [mem_ballStab]
    intro μ hμ
    rcases (dist_le_one_iff hA.amalgam.gen).mp hμ with rfl | hadj
    · obtain ⟨ν, hν⟩ := exists_adj δ
      have := Subgroup.mem_iInf.mp (Subgroup.mem_iInf.mp hx ν) hν
      exact this.1
    · have := Subgroup.mem_iInf.mp (Subgroup.mem_iInf.mp hx μ) hadj
      exact this.2

omit [Finite G] in
theorem omegaOneCenter_le_centerOf_self (T : Subgroup G) :
    quasithinOmegaOneCenter T ≤ centerOf T := by
  unfold quasithinOmegaOneCenter
  rw [Subgroup.closure_le]
  exact fun x hx => hx.1

theorem Qv_le_centralizer_Zv (hA : F53Amalgam H M S) (δ : Geo H M) :
    Qv δ ≤ Subgroup.centralizer (Zv δ : Set G) := by
  intro q hq
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  exact ((Subgroup.mem_centralizer_iff.mp (Zv_le_centerOf_Qv hA δ hv).2) q hq).symm

theorem centralizer_Zv_dichotomy (hA : F53Amalgam H M S) (δ : Geo H M) :
    stab δ ⊓ Subgroup.centralizer (Zv δ : Set G) = Qv δ ∨
      Zv δ = quasithinOmegaOneCenter (stab δ) := by
  by_cases hQ : stab δ ⊓ Subgroup.centralizer (Zv δ : Set G) ≤ Qv δ
  · left
    exact le_antisymm hQ (le_inf (pCoreOf_le 2 _) (Qv_le_centralizer_Zv hA δ))
  · right
    obtain ⟨μ, hμ⟩ := exists_adj δ
    have hm : μ ∈ nbrs δ := hμ
    have hT := sylow_stab_inf_left hA hm
    have hcn : stab δ ≤ Subgroup.normalizer
        ((stab δ ⊓ Subgroup.centralizer (Zv δ : Set G) : Subgroup G) : Set G) :=
      le_normalizer_inf Subgroup.le_normalizer
        ((stab_le_normalizer_Zv hA δ).trans (normalizer_le_normalizer_centralizer _))
    have hn : ∃ n, (n = 3 ∨ n = 5) ∧ Nonempty (OTwoQuot (stab δ) ≃* Equiv.Perm (Fin n)) := by
      cases hv : vtype δ with
      | false => exact ⟨5, Or.inr rfl, quot_stab_five hA hv⟩
      | true => exact ⟨3, Or.inl rfl, quot_stab_three hA hv⟩
    obtain ⟨n, hn3, hq⟩ := hn
    have hsup := sup_sylow_eq_of_normal_not_le hn3 hq hT inf_le_left hcn hQ
    have hTN : stab δ ⊓ stab μ ≤ Subgroup.normalizer
        ((stab δ ⊓ Subgroup.centralizer (Zv δ : Set G) : Subgroup G) : Set G) :=
      inf_le_left.trans hcn
    have hZ := Zv_eq_conjClosure hT
    set Ω := quasithinOmegaOneCenter (stab δ ⊓ stab μ) with hΩ
    have hΩV : Ω ≤ Zv δ := by rw [hZ]; exact le_conjClosure _ _
    have hfix : ∀ x ∈ stab δ, ∀ z ∈ Ω, x * z * x⁻¹ = z := by
      intro x hx z hz
      obtain ⟨c, hc, t, ht, hct⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hTN).mp (hsup hx)
      have hzT : z ∈ centerOf (stab δ ⊓ stab μ) := omegaOneCenter_le_centerOf_self _ hz
      have h1 : t * z * t⁻¹ = z := by
        have := (Subgroup.mem_centralizer_iff.mp hzT.2) t ht
        calc t * z * t⁻¹ = (z * t) * t⁻¹ := by rw [this]
          _ = z := by group
      have h2 : c * z * c⁻¹ = z := by
        have := (Subgroup.mem_centralizer_iff.mp hc.2) z (hΩV hz)
        calc c * z * c⁻¹ = (z * c) * c⁻¹ := by rw [this]
          _ = z := by group
      rw [hct, show c * t * z * (c * t)⁻¹ = c * (t * z * t⁻¹) * c⁻¹ by group, h1, h2]
    have hle : Zv δ ≤ Ω := by
      rw [hZ]
      refine conjClosure_le fun h hh z hz => ?_
      rw [hfix h hh z hz]; exact hz
    have hΩc : Ω ≤ quasithinOmegaOneCenter (stab δ) := by
      unfold quasithinOmegaOneCenter
      refine (Subgroup.closure_le _).mpr fun z hz => ?_
      refine Subgroup.subset_closure ⟨⟨(inf_le_left : stab δ ⊓ stab μ ≤ stab δ) hz.1.1, ?_⟩, hz.2⟩
      show z ∈ Subgroup.centralizer (stab δ : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have := hfix x hx z (Subgroup.subset_closure hz)
      calc x * z = (x * z * x⁻¹) * x := by group
        _ = z * x := by rw [this]
    refine le_antisymm (hle.trans hΩc) ?_
    exact (omegaOneCenter_le_Zv hA hm).1.trans (omegaOneCenter_le_Zv hA hm).2.1

theorem pCoreOf_ne_stab (hA : F53Amalgam H M S) (δ : Geo H M) : Qv δ ≠ stab δ := by
  intro h
  have htop : CFSG.Open.pCore 2 ↥(stab δ) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : (x : G) ∈ pCoreOf 2 (stab δ) := by
      show (x : G) ∈ Qv δ
      rw [h]; exact x.2
    obtain ⟨y, hy, hyx⟩ := hx
    have : y = x := Subtype.ext hyx
    rw [← this]; exact hy
  have h1 : Nat.card (OTwoQuot (stab δ)) = 1 := by
    have : Nat.card (↥(stab δ) ⧸ CFSG.Open.pCore 2 ↥(stab δ)) = 1 := by
      rw [htop]; simp
    exact this
  cases hv : vtype δ with
  | false =>
    obtain ⟨φ⟩ := quot_stab_five hA hv
    rw [Nat.card_congr φ.toEquiv, S152Fin.card_Perm_five] at h1
    omega
  | true =>
    obtain ⟨φ⟩ := quot_stab_three hA hv
    rw [Nat.card_congr φ.toEquiv, Nat.card_perm] at h1
    simp [Nat.factorial] at h1

theorem eq_bot_of_normalizes_both (hA : F53Amalgam H M S) {α β : Geo H M}
    (hαβ : (graph (H ⊔ M) H M).Adj α β) {U : Subgroup G} (hU : U ≤ stab α ⊓ stab β)
    (hα : stab α ≤ Subgroup.normalizer (U : Set G))
    (hβ : stab β ≤ Subgroup.normalizer (U : Set G)) : U = ⊥ := by
  refine eq_bot_of_normalizer_transitive_vertex hA hαβ hU ?_ ?_
  · intro ε hε ε' hε'
    obtain ⟨x, hx, hxε⟩ := stab_transitive_on_nbrs hε hε'
    exact ⟨x, hα hx, smul_eq_of_mem_stab hx, hxε⟩
  · intro ε hε ε' hε'
    obtain ⟨x, hx, hxε⟩ := stab_transitive_on_nbrs hε hε'
    exact ⟨x, hβ hx, smul_eq_of_mem_stab hx, hxε⟩

theorem centerOf_nbr_eq_bot (hA : F53Amalgam H M S) {δ μ : Geo H M} (h : μ ∈ nbrs δ)
    (hz : Zv δ = quasithinOmegaOneCenter (stab δ)) : centerOf (stab μ) = ⊥ := by
  have hm' : δ ∈ nbrs μ := SimpleGraph.Adj.symm (show (graph (H ⊔ M) H M).Adj δ μ from h)
  set U := quasithinOmegaOneCenter (stab μ) with hU
  have hUZ : U ≤ Zv δ :=
    (omegaOneCenter_le_Zv hA hm').1.trans (omegaOneCenter_le_Zv hA hm').2.2
  have hUB : U ≤ stab μ ⊓ stab δ :=
    ((omegaOneCenter_le_Zv hA hm').1.trans
      ((omegaOneCenter_le_centerOf_self _).trans inf_le_left))
  have hnμ : stab μ ≤ Subgroup.normalizer (U : Set G) := by
    intro x hx
    refine Subgroup.centralizer_le_normalizer _ ?_
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have hu' : u ∈ centerOf (stab μ) := omegaOneCenter_le_centerOf_self _ hu
    exact ((Subgroup.mem_centralizer_iff.mp hu'.2) x hx).symm
  have hnδ : stab δ ≤ Subgroup.normalizer (U : Set G) := by
    intro x hx
    refine Subgroup.centralizer_le_normalizer _ ?_
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have hu' : u ∈ centerOf (stab δ) := by
      have : u ∈ quasithinOmegaOneCenter (stab δ) := hz ▸ hUZ hu
      exact omegaOneCenter_le_centerOf_self _ this
    exact ((Subgroup.mem_centralizer_iff.mp hu'.2) x hx).symm
  have hUb : U = ⊥ :=
    eq_bot_of_normalizes_both hA (show (graph (H ⊔ M) H M).Adj μ δ from hm') hUB hnμ hnδ
  by_contra hY
  have hYp : IsPGroup 2 (centerOf (stab μ)) := by
    refine (pCoreOf_isPGroup 2 (stab μ)).to_le ?_
    intro y hy
    refine charTwo_stab hA μ ⟨hy.1, ?_⟩
    exact Subgroup.centralizer_le (pCoreOf_le 2 (stab μ)) hy.2
  have h1 := quasithinOmegaOneCenter_ne_bot hYp hY
  apply h1
  rw [eq_bot_iff]
  refine le_trans ?_ hUb.le
  unfold quasithinOmegaOneCenter
  refine Subgroup.closure_mono ?_
  rintro z ⟨hz1, hz2⟩
  exact ⟨hz1.1, hz2⟩

theorem centralizer_Zv_eq_Qv_of_bAt (hA : F53Amalgam H M S) {δ : Geo H M}
    (h : bAt δ = bMin H M) : stab δ ⊓ Subgroup.centralizer (Zv δ : Set G) = Qv δ := by
  rcases centralizer_Zv_dichotomy hA δ with h1 | h2
  · exact h1
  · exfalso
    obtain ⟨μ, hd, hn⟩ := bAt_spec hA δ
    have hb := bAt_pos hA δ
    obtain ⟨β, hβ, hdβ⟩ := exists_adj_dist_eq hA.amalgam.gen (α := μ) (δ := δ)
      (d := bAt δ - 1) (by rw [CosetGeom.dist_comm]; omega)
    have hle : Zv δ ≤ Zv β := by
      rw [h2]
      exact (omegaOneCenter_le_Zv hA (show β ∈ nbrs δ from hβ)).1.trans
        (omegaOneCenter_le_Zv hA (show β ∈ nbrs δ from hβ)).2.2
    have hnb : ¬ Zv β ≤ Qv μ := fun hh => hn (hle.trans hh)
    have h3 : bAt β ≤ CosetGeom.dist β μ := Nat.sInf_le ⟨μ, rfl, hnb⟩
    have h4 : bMin H M ≤ bAt β := bMin_le_bAt β
    rw [CosetGeom.dist_comm, hdβ] at h3
    omega

theorem Zv_eq_omegaOneCenter_of_central (hA : F53Amalgam H M S) {β : Geo H M}
    (h : Zv β ≤ centerOf (stab β)) : Zv β = quasithinOmegaOneCenter (stab β) := by
  rcases centralizer_Zv_dichotomy hA β with hQ | hZ
  · exfalso
    have hcen : stab β ≤ Subgroup.centralizer (Zv β : Set G) := by
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      exact ((Subgroup.mem_centralizer_iff.mp (h hz).2) x hx).symm
    rw [inf_eq_left.mpr hcen] at hQ
    exact pCoreOf_ne_stab hA β hQ.symm
  · exact hZ

theorem Zv_eq_omegaOneCenter_inf (hA : F53Amalgam H M S) {α β : Geo H M} (hαβ : α ∈ nbrs β)
    (h : Zv β ≤ centerOf (stab β)) :
    Zv β = quasithinOmegaOneCenter (stab β ⊓ stab α) ∧ Zv β ≤ Zv α := by
  have hZ := Zv_eq_omegaOneCenter_of_central hA h
  obtain ⟨h1, h2, h3⟩ := omegaOneCenter_le_Zv hA hαβ
  refine ⟨le_antisymm (hZ ▸ h1) h2, ?_⟩
  rw [hZ]; exact h1.trans h3

theorem centerOf_eq_bot_of_Zv_central (hA : F53Amalgam H M S) {α β : Geo H M}
    (hαβ : α ∈ nbrs β) (h : Zv β ≤ centerOf (stab β)) : centerOf (stab α) = ⊥ :=
  centerOf_nbr_eq_bot hA hαβ (Zv_eq_omegaOneCenter_of_central hA h)

theorem pCoreOf_pCoreOf (X : Subgroup G) : pCoreOf 2 (pCoreOf 2 X) = pCoreOf 2 X :=
  le_antisymm (pCoreOf_le 2 _)
    (le_pCoreOf_of_le_normalizer 2 le_rfl Subgroup.le_normalizer (pCoreOf_isPGroup 2 X))

theorem amalgamHypV_Zv_inr (hA : F53Amalgam H M S)
    (hC : M ⊓ Subgroup.centralizer (Zv (γ₁ (H ⊔ M) H M) : Set G) ≤ pCoreOf 2 M) :
    AmalgamHypV (H ⊔ M) M H S (Zv (γ₁ (H ⊔ M) H M)) := by
  have h₂ := hA.amalgam.le₂
  have hS := hA.amalgam.sylow₂
  have hST : IsSylowTwoOf S (stab (γ₁ (H ⊔ M) H M)) := by rw [stab_γ₁ h₂]; exact hS
  have hZ := Zv_eq_conjClosure hST
  rw [stab_γ₁ h₂] at hZ
  have hQC : pCoreOf 2 M ≤ Subgroup.centralizer (Zv (γ₁ (H ⊔ M) H M) : Set G) := by
    have := Qv_le_centralizer_Zv hA (γ₁ (H ⊔ M) H M)
    unfold Qv at this
    rwa [stab_γ₁ h₂] at this
  have h1 : M ⊓ Subgroup.centralizer (Zv (γ₁ (H ⊔ M) H M) : Set G) = pCoreOf 2 M :=
    le_antisymm hC (le_inf (pCoreOf_le 2 M) hQC)
  refine { toAmalgamHyp := amalgamSymm hA, reduced := ?_, cT := ?_ }
  · rw [hZ]
    exact isTwoReducedIn_conjClosure_of_sylowIn hS.1 hS.2.1 hS.2.2 hA.charTwo_right
      (Z := quasithinOmegaOneCenter S) le_rfl
  · rw [h1, pCoreOf_pCoreOf]
    apply le_antisymm
    · exact (inf_le_inf_right _ hS.1).trans h1.le
    · exact le_inf (isSylowTwoOf_pCoreOf_le hS) hQC

theorem bAt_γ₁_eq_critDist (hA : F53Amalgam H M S)
    (hC : M ⊓ Subgroup.centralizer (Zv (γ₁ (H ⊔ M) H M) : Set G) ≤ pCoreOf 2 M) :
    bAt (γ₁ (H ⊔ M) H M) = critDist (H ⊔ M) M H (Zv (γ₁ (H ⊔ M) H M)) := by
  have hyp := amalgamHypV_Zv_inr hA hC
  have hV : Zv (γ₁ (H ⊔ M) H M) ≠ ⊥ := Zv_ne_bot hA _
  have hL := isLeast_critDist hyp hV
  have hset : {n : ℕ | ∃ γ ∈ sphere n (γ₀ (H ⊔ M) M H),
      ¬ Zv (γ₁ (H ⊔ M) H M) ≤ ballStab 1 γ} =
      {n : ℕ | ∃ μ : Geo H M, dist (γ₁ (H ⊔ M) H M) μ = n ∧
        ¬ Zv (γ₁ (H ⊔ M) H M) ≤ Qv μ} := by
    ext n
    constructor
    · rintro ⟨γ, hγ, hn⟩
      obtain ⟨μ, rfl⟩ : ∃ μ, γ = CosetGeom.swapEquiv μ := ⟨CosetGeom.swapEquiv.symm γ, by simp⟩
      refine ⟨μ, ?_, ?_⟩
      · have : dist (γ₀ (H ⊔ M) M H) (CosetGeom.swapEquiv μ) = n := hγ
        rwa [← CosetGeom.swapEquiv_γ₁ (G₀ := H ⊔ M) (G₁ := H) (G₂ := M),
          CosetGeom.dist_swapEquiv] at this
      · rw [CosetGeom.ballStab_swapEquiv, Qv_eq_ballStab_one hA] at hn
        exact hn
    · rintro ⟨μ, hμ, hn⟩
      refine ⟨CosetGeom.swapEquiv μ, ?_, ?_⟩
      · show dist (γ₀ (H ⊔ M) M H) (CosetGeom.swapEquiv μ) = n
        rw [← CosetGeom.swapEquiv_γ₁ (G₀ := H ⊔ M) (G₁ := H) (G₂ := M), CosetGeom.dist_swapEquiv]
        exact hμ
      · rw [CosetGeom.ballStab_swapEquiv, Qv_eq_ballStab_one hA]
        exact hn
  unfold bAt
  rw [← hset]
  exact hL.csInf_eq

end F53

end CFSG.Quasithin
