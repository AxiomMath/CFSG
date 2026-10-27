module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SporadicModelGlue
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.CoverThree
public import CFSG.RankThree.Asc83Table.E9
public import CFSG.GroupTheory.Frattini.PSubgroupLift

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement

theorem exists_permutes_of_normalizer_cover {Y : Type} [Group Y] [Finite Y] {K S : Subgroup Y}
    [hK : K.Normal] {Γ : Type} [Group Γ] [Finite Γ] {U : Subgroup Γ}
    (hU : CFSG.QuasithinUnique.IsSylowTwoOf U ⊤)
    (hN : Nat.card (Subgroup.normalizer (U : Set Γ)) = 3 * Nat.card U)
    {a g : Γ} (ha : a ∈ Subgroup.normalizer (U : Set Γ)) (ha1 : a ≠ 1) (ha3 : a ^ 3 = 1)
    (hg : g * a * g⁻¹ = a⁻¹)
    (f : ↥K →* Γ) (hf : Function.Surjective f) (hker : f.ker = Subgroup.center ↥K)
    (hZ : Nat.card (Subgroup.center ↥K) = 3) (hS : CFSG.QuasithinUnique.IsSylowTwoOf S ⊤) :
    ∃ E : Subgroup Y, E ≤ K ∧ E ≠ ⊥ ∧ IsPGroup 3 ↥E ∧ (∀ x ∈ E, x ^ 3 = 1) ∧
      ¬ IsCyclic ↥E ∧ CFSG.LocalAnalysis.UniquenessCase.UC22.Permutes E S := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSK : CFSG.QuasithinUnique.IsSylowTwoOf (S ⊓ K) K :=
    CFSG.Quasithin.B6.isSylowTwoOf_inf_normal hS le_top fun x _ => by
      rw [Subgroup.normalizer_eq_top_iff.mpr hK]; trivial
  let T : Subgroup ↥K := (S ⊓ K).subgroupOf K
  have hT : CFSG.QuasithinUnique.IsSylowTwoOf T ⊤ := by
    refine ⟨le_top, ?_, ?_⟩
    · exact hSK.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe inf_le_right).symm
    · rw [show (T.subgroupOf ⊤).index = T.index from Subgroup.relIndex_top_right T]
      exact hSK.2.2
  have hTindex : ¬ 2 ∣ T.index := hSK.2.2
  let P : Sylow 2 ↥K := hT.2.1.toSylow hTindex
  let Q : Sylow 2 Γ := P.mapSurjective hf
  have hQ : (Q : Subgroup Γ) = T.map f := Sylow.coe_mapSurjective hf P
  have hUindex : ¬ 2 ∣ U.index := by
    have h := hU.2.2
    rw [show (U.subgroupOf ⊤).index = U.index from Subgroup.relIndex_top_right U] at h
    exact h
  let U' : Sylow 2 Γ := hU.2.1.toSylow hUindex
  have hU'coe : (U' : Subgroup Γ) = U := IsPGroup.toSylow_coe hU.2.1 hUindex
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq Γ Q U'
  have hcQ : (Q : Subgroup Γ).map (MulAut.conj c).toMonoidHom = U := by
    have h1 := congrArg (fun X : Sylow 2 Γ => (X : Subgroup Γ)) hc
    rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def, hU'coe] at h1
    exact h1
  let f' : ↥K →* Γ := (MulAut.conj c).toMonoidHom.comp f
  have hf' : Function.Surjective f' := (MulAut.conj c).surjective.comp hf
  have hker' : f'.ker = Subgroup.center ↥K := by
    dsimp only [f']
    rw [MonoidHom.ker_comp_of_injective f (MulAut.conj c).toMonoidHom
      (MulAut.conj c).injective, hker]
  have hTmap : T.map f' = U := by
    dsimp only [f']
    rw [← Subgroup.map_map, ← hQ, hcQ]
  let H' : Subgroup ↥K := (Subgroup.normalizer (U : Set Γ)).comap f'
  have hH'card : Nat.card H' = 9 * Nat.card U := by
    dsimp only [H']
    rw [CFSG.GroupTheory.card_comap_eq_card_ker_mul_card f' hf', hker', hZ, hN]
    ring
  let Zc : Subgroup Y := (Subgroup.center ↥K).map K.subtype
  let T₀ : Subgroup Y := (S ⊓ K) ⊔ Zc
  let H₀ : Subgroup Y := H'.map K.subtype
  have hH₀card : Nat.card H₀ = 9 * Nat.card U := by
    dsimp only [H₀]
    rw [Subgroup.card_map_of_injective K.subtype_injective, hH'card]
  have hTdisj : T ⊓ f'.ker = ⊥ := by
    obtain ⟨n, hn⟩ := hT.2.1.exists_card_eq
    have hcop : Nat.Coprime (Nat.card T) (Nat.card f'.ker) := by
      rw [hker', hZ, hn]
      exact Nat.Coprime.pow_left _ (by norm_num)
    exact (Subgroup.disjoint_of_coprime_natCard hcop).eq_bot
  have hTmapcard : Nat.card (T.map f') = Nat.card T := by
    have hkercomp : (f'.comp T.subtype).ker = ⊥ := by
      ext x
      rw [Subgroup.mem_bot, MonoidHom.mem_ker, MonoidHom.comp_apply]
      change f' (x : ↥K) = 1 ↔ x = 1
      constructor
      · intro hx
        have hmem : (x : ↥K) ∈ T ⊓ f'.ker := ⟨x.2, by
          change f' (x : ↥K) = 1
          exact hx⟩
        rw [hTdisj] at hmem
        exact Subtype.ext hmem
      · intro hx
        rw [hx]
        simp
    have h := Subgroup.card_ker_mul_card_range (f'.comp T.subtype)
    rw [hkercomp, MonoidHom.range_comp, Subgroup.range_subtype, Subgroup.card_bot] at h
    simpa using h
  have hTs : Nat.card T = Nat.card ↥(S ⊓ K) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  have hUT : Nat.card U = Nat.card T := by
    rw [← hTmap]
    exact hTmapcard
  have hTcard : Nat.card ↥(S ⊓ K) = Nat.card U := hTs.symm.trans hUT.symm
  have hH₀card9 : Nat.card H₀ = 9 * Nat.card ↥(S ⊓ K) := by
    rw [hH₀card, hTcard]
  have hT₀K : T₀ ≤ K := by
    dsimp only [T₀, Zc]
    exact sup_le inf_le_right (Subgroup.map_subtype_le _)
  have hcenterSub : Zc.subgroupOf K = Subgroup.center ↥K := by
    dsimp only [Zc]
    rw [← Subgroup.comap_subtype]
    exact Subgroup.comap_map_eq_self (h := by rw [Subgroup.ker_subtype]; exact bot_le)
  have hT₀sub : T₀.subgroupOf K = T ⊔ Subgroup.center ↥K := by
    dsimp only [T₀, Zc]
    rw [Subgroup.subgroupOf_sup inf_le_right (Subgroup.map_subtype_le _), hcenterSub]
  have hmap_sup : (T ⊔ Subgroup.center ↥K).map f' = U := by
    rw [Subgroup.map_sup, hTmap]
    have hkerbot : (Subgroup.center ↥K).map f' = ⊥ := by
      rw [Subgroup.map_eq_bot_iff, ← hker']
    rw [hkerbot, sup_bot_eq]
  have hpre : U.comap f' = T ⊔ Subgroup.center ↥K := by
    rw [← hmap_sup]
    exact Subgroup.comap_map_eq_self (h := by rw [hker']; exact le_sup_right)
  have hH'eq : H' = (K ⊓ Subgroup.normalizer (T₀ : Set Y)).subgroupOf K := by
    dsimp only [H']
    rw [Subgroup.comap_normalizer_eq_of_surjective U hf', hpre,
      Subgroup.inf_subgroupOf_left, Subgroup.subgroupOf_normalizer_eq hT₀K, hT₀sub]
  have hH₀eq : H₀ = K ⊓ Subgroup.normalizer (T₀ : Set Y) := by
    dsimp only [H₀]
    rw [hH'eq, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr (inf_le_left : K ⊓ Subgroup.normalizer (T₀ : Set Y) ≤ K)]
  letI : Fintype ↥(Subgroup.center ↥K) := Fintype.ofFinite _
  have hZnt : 1 < Fintype.card ↥(Subgroup.center ↥K) := by
    rw [← Nat.card_eq_fintype_card, hZ]
    norm_num
  obtain ⟨ζc, hζc⟩ := Fintype.exists_ne_of_one_lt_card hZnt (1 : ↥(Subgroup.center ↥K))
  let ζ : ↥K := (ζc : ↥K)
  have hζmem : ζ ∈ Subgroup.center ↥K := ζc.2
  have hζne : ζ ≠ 1 := by
    intro h
    exact hζc (Subtype.ext h)
  have hζ3 : ζ ^ 3 = 1 := by
    have h := congrArg (fun x : ↥(Subgroup.center ↥K) => (x : ↥K))
      (pow_card_eq_one' (x := ζc))
    rw [hZ] at h
    simpa using h
  have hζker : ζ ∈ f'.ker := by rw [hker']; exact hζmem
  have hζf : f' ζ = 1 := MonoidHom.mem_ker.mp hζker
  obtain ⟨â, hâ⟩ := hf' a
  obtain ⟨ĝ, hĝ⟩ := hf' g
  have hâ3 : â ^ 3 = 1 := by
    refine CFSG.SectionRank.QTK.Insp443.CoverThree.pow_three_eq_one_of_inv
      (K := ↥K) (X := Γ) (f := f') (a := â) (g := ĝ) ?_ ?_ ?_ ?_
    · rw [hker']
    · intro z hz
      rw [hker'] at hz
      have h := congrArg (fun x : ↥(Subgroup.center ↥K) => (x : ↥K))
        (pow_card_eq_one' (x := ⟨z, hz⟩))
      rw [hZ] at h
      simpa using h
    · rw [hâ, ha3]
    · rw [hâ, hĝ, hg]
  have hâne : â ≠ 1 := by
    intro h
    rw [h, map_one] at hâ
    exact ha1 hâ.symm
  have hζa : ζ ≠ â := by
    intro h
    have h1 := congrArg f' h
    rw [hζf, hâ] at h1
    exact ha1 h1.symm
  have hζa2 : ζ ≠ â ^ 2 := by
    intro h
    have h1 : a ^ 2 = 1 := by
      have h2 := congrArg f' h
      rw [hζf, map_pow, hâ] at h2
      exact h2.symm
    have h2 : a = 1 := by
      calc a = a ^ 3 * (a ^ 2)⁻¹ := by group
        _ = 1 := by rw [ha3, h1]; simp
    exact ha1 h2
  have hcomm : Commute â ζ := Subgroup.mem_center_iff.mp hζmem â
  have hζnot : ζ ∉ Subgroup.zpowers â :=
    CFSG.RankThree.Asc83Table.not_mem_zpowers_of_ne hâ3 hζne hζa hζa2
  have hcardcl : Nat.card (Subgroup.closure ({â, ζ} : Set ↥K)) = 9 :=
    CFSG.RankThree.Asc83Table.card_closure_pair_eq_nine hâ3 hζ3 hcomm hâne hζnot
  let E : Subgroup Y := (Subgroup.closure ({â, ζ} : Set ↥K)).map K.subtype
  have hEcard : Nat.card E = 9 := by
    dsimp only [E]
    rw [Subgroup.card_map_of_injective K.subtype_injective, hcardcl]
  have hEne : E ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hEcard
    norm_num at hEcard
  have hE3pg : IsPGroup 3 ↥E := IsPGroup.of_card (n := 2) (by rw [hEcard]; norm_num)
  have hE3 : ∀ x ∈ E, x ^ 3 = 1 := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    have hc : ⁅â, ζ⁆ = 1 := hcomm.commutator_eq
    have hzx : Commute ⁅â, ζ⁆ â := by rw [hc]; exact Commute.one_left _
    have hzy : Commute ⁅â, ζ⁆ ζ := by rw [hc]; exact Commute.one_left _
    have hy3 : y ^ 3 = 1 :=
      CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.pow_three_eq_one_of_mem_closure_cubic
        hâ3 hζ3 hzx hzy hy
    exact congrArg (fun z : ↥K => (z : Y)) hy3
  have hEnoncyc : ¬ IsCyclic ↥E := by
    intro hcyc
    have hexpdvd : Monoid.exponent ↥E ∣ 3 :=
      Monoid.exponent_dvd_of_forall_pow_eq_one fun g => Subtype.ext (by simpa using hE3 g g.2)
    rw [IsCyclic.exponent_eq_card, hEcard] at hexpdvd
    norm_num at hexpdvd
  have hEH' : Subgroup.closure ({â, ζ} : Set ↥K) ≤ H' := by
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | rfl
    · dsimp only [H']
      exact Subgroup.mem_comap.mpr (by rw [hâ]; exact ha)
    · dsimp only [H']
      exact Subgroup.mem_comap.mpr (by
        rw [hζf]
        exact (Subgroup.normalizer (U : Set Γ)).one_mem)
  have hEH₀ : E ≤ H₀ := by
    dsimp only [E, H₀]
    exact Subgroup.map_mono hEH'
  have hKconj : ∀ t : Y, K.map (MulAut.conj t).toMonoidHom = K := fun t =>
    Subgroup.Normal.map_conj_eq K t
  have hZcconj : ∀ t : Y, Zc.map (MulAut.conj t).toMonoidHom = Zc := by
    intro t
    dsimp only [Zc]
    have hcenter := Subgroup.characteristic_iff_map_eq.mp
      (Subgroup.centerCharacteristic (G := ↥K)) (MulAut.conjNormal (H := K) t)
    calc ((Subgroup.center ↥K).map K.subtype).map (MulAut.conj t).toMonoidHom
        = Subgroup.map ((MulAut.conj t).toMonoidHom.comp K.subtype)
            (Subgroup.center ↥K) := by
          rw [Subgroup.map_map]
      _ = Subgroup.map (K.subtype.comp (MulAut.conjNormal (H := K) t).toMonoidHom)
            (Subgroup.center ↥K) := by
          congr 1
      _ = ((Subgroup.center ↥K).map (MulAut.conjNormal (H := K) t).toMonoidHom).map
            K.subtype := by
          rw [Subgroup.map_map]
      _ = (Subgroup.center ↥K).map K.subtype := by rw [hcenter]
  have hSconj : ∀ t ∈ S, S.map (MulAut.conj t).toMonoidHom = S := by
    intro t ht
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact S.mul_mem (S.mul_mem ht hy) (S.inv_mem ht)
    · intro hx
      refine ⟨t⁻¹ * x * t, ?_, ?_⟩
      · exact S.mul_mem (S.mul_mem (S.inv_mem ht) hx) ht
      · change t * (t⁻¹ * x * t) * t⁻¹ = x
        group
  have hS₀conj : ∀ t ∈ S, (S ⊓ K).map (MulAut.conj t).toMonoidHom = S ⊓ K := by
    intro t ht
    rw [Subgroup.map_inf _ _ _ (MulAut.conj t).injective, hSconj t ht, hKconj t]
  have hT₀conj : ∀ t ∈ S, T₀.map (MulAut.conj t).toMonoidHom = T₀ := by
    intro t ht
    dsimp only [T₀]
    rw [Subgroup.map_sup, hS₀conj t ht, hZcconj t]
  have hH₀conj : ∀ t ∈ S, H₀.map (MulAut.conj t).toMonoidHom = H₀ := by
    intro t ht
    rw [hH₀eq,
      Subgroup.map_inf K (Subgroup.normalizer (T₀ : Set Y)) (MulAut.conj t).toMonoidHom
        (MulAut.conj t).injective,
      hKconj t, Subgroup.map_equiv_normalizer_eq T₀ (MulAut.conj t), hT₀conj t ht]
  have hnorm : S ≤ Subgroup.normalizer (H₀ : Set Y) := fun t ht =>
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr (hH₀conj t ht)
  have hS₀leH₀ : S ⊓ K ≤ H₀ := by
    intro s hs
    rw [hH₀eq]
    refine ⟨hs.2, ?_⟩
    change s ∈ Subgroup.normalizer (T₀ : Set Y)
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    dsimp only [T₀]
    rw [Subgroup.map_sup]
    change Subgroup.map (MulAut.conj s).toMonoidHom (S ⊓ K) ⊔
      Subgroup.map (MulAut.conj s).toMonoidHom Zc = S ⊓ K ⊔ Zc
    rw [hS₀conj s hs.1, hZcconj s]
  have hH₀leK : H₀ ≤ K := hH₀eq ▸ inf_le_left
  have hSH : S ⊓ H₀ = S ⊓ K :=
    le_antisymm (inf_le_inf_left _ hH₀leK) (le_inf inf_le_left hS₀leH₀)
  have hSHcard : Nat.card ↥(S ⊔ H₀) = 9 * Nat.card S := by
    have h := CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
      (H := S) (K := H₀) hnorm
    rw [hSH, hH₀card9] at h
    have h2 : Nat.card ↥(S ⊔ H₀) * Nat.card ↥(S ⊓ K) =
        (9 * Nat.card S) * Nat.card ↥(S ⊓ K) := by
      rw [h]; ring
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h2
  have hEinfS : E ⊓ S = ⊥ := by
    have hcop : Nat.Coprime (Nat.card E) (Nat.card S) := by
      obtain ⟨k, hk⟩ := hS.2.1.exists_card_eq
      rw [hEcard, hk]
      exact Nat.Coprime.pow_right k (by norm_num)
    exact (Subgroup.disjoint_of_coprime_natCard hcop).eq_bot
  have hperm : CFSG.LocalAnalysis.UniquenessCase.UC22.Permutes E S := by
    refine CFSG.Quasithin.H.L3Wr.permute_of_card hEinfS ?_
    calc Nat.card ↥(E ⊔ S) ≤ Nat.card ↥(S ⊔ H₀) :=
          Subgroup.card_le_of_le (sup_le (hEH₀.trans le_sup_right) le_sup_left)
      _ = 9 * Nat.card S := hSHcard
      _ = Nat.card E * Nat.card S := by rw [hEcard]
  exact ⟨E, Subgroup.map_subtype_le _, hEne, hE3pg, hE3, hEnoncyc, hperm⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

end
