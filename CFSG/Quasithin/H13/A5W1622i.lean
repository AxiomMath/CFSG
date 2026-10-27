module

public import CFSG.Quasithin.H13.A5W1622h
public import CFSG.Quasithin.EmptyFaithful.ModDGlue
public import CFSG.Quasithin.H13.U3U33Fixed

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

theorem eq_of_card_subtype_two {V : Type*} [Group V] {F : V → Prop}
    (h : Nat.card {v // F v} = 2) (h1 : F 1) {n p : V} (hn : n ≠ 1) (hp : p ≠ 1) (hFn : F n)
    (hFp : F p) : n = p := by
  classical
  by_contra hne
  have : Finite {v // F v} := Nat.finite_of_card_ne_zero (by rw [h]; norm_num)
  let f : Fin 3 → {v // F v} := ![⟨1, h1⟩, ⟨n, hFn⟩, ⟨p, hFp⟩]
  have hf : Function.Injective f := by
    intro i j hij
    have hij' := congrArg Subtype.val hij
    fin_cases i <;> fin_cases j <;> simp_all [f, eq_comm]
  have := Nat.card_le_card_of_injective f hf
  rw [h, Nat.card_fin] at this
  omega

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting G T L V)

theorem false_of_g2Block
    (h1222 : Stmt12_2_2)
    (h517 : Stmt5_1_7_one) (h132two : Stmt13_3_2_two) (h132fsu : Stmt13_3_2_three_fsu)
    (h132A5 : Stmt13_3_2_three_A5) (h331 : Stmt3_3_1) (h1327 : Stmt13_2_7)
    (h39 : Vol2Native.A39ForSQTKCat) (hF : CharTwo (Subgroup.centralizer ({S.v12} : Set G)))
    {K₀ : Subgroup G} (hK₀G : K₀ ≤ Subgroup.centralizer ({S.v12} : Set G))
    (hK₀ : K₀ ∈ lFamily S.Tv) (hTK₀ : S.Tv ≤ Subgroup.normalizer (K₀ : Set G))
    (hz : ¬ K₀ ≤ Subgroup.centralizer ({S.z} : Set G)) (hLvK₀ : S.Lv ≤ K₀)
    (hchar : CharTwo (K₀ ⊔ S.Tv)) (hblk : IsG2Block K₀) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hshort, hQ, hidx⟩ := hblk
  have : Finite U33G := (CFSG.Quasithin.u33Pres_finite_card_le).1
  obtain ⟨P⟩ : Nonempty (Sylow 2 ↥K₀) := inferInstance
  obtain ⟨ψ, hψs, hψk, -⟩ := ModD.exists_psi hQ P
  have hcard : Nat.card (blockQuot K₀) = 64 := hidx.1
  have hT : IsSylowTwoOf u33Data.T ⊤ := by
    refine ⟨le_top, u33_syl.1, ?_⟩
    rw [show (u33Data.T.subgroupOf ⊤).index = u33Data.T.index from Subgroup.relIndex_top_right _]
    exact u33_syl.2
  refine S.false_of_blockModel h1222 h517 h132two h132fsu h132A5 h331 h1327 h39 hF hK₀G hK₀ hTK₀
    hz hLvK₀ hchar hshort ψ hψs hψk hT ?_
  intro n p hn hp hnS hpS x hx
  set act := blockLiftAct hshort ψ hψs hψk with hact
  have hfix : ∀ v : blockQuot K₀, (∀ g, act g v = v) → v = 1 := fun v hv =>
    fixed_eq_one_of_short hshort (by rw [hcard]; norm_num) fun ℓ => by
      rw [← blockLiftAct_apply hshort ψ hψs hψk ℓ]
      exact hv _
  have hV2 : ∀ v : blockQuot K₀, v * v = 1 := fun v => by
    rw [← pow_two]
    exact blockQuot_sq hshort v
  have hc := U3.u33_sylow_fixed_card_two hV2 hcard act hfix (u33_syl.1.toSylow u33_syl.2)
  have hnp : n = p :=
    eq_of_card_subtype_two hc (fun s _ => map_one _) hn hp hnS hpS
  rw [← hnp]
  exact hx

end Setting

end CFSG.Quasithin.H13.A5
