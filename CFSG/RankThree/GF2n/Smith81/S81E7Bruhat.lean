module

public import CFSG.RankThree.GF2n.Smith81.S81E7Frame
public import CFSG.LieType.Steinberg.Bruhat
public import CFSG.LieType.Steinberg.Minuscule.BruhatExtras

public noncomputable section

namespace CFSG.RankThree.GF2n.Smith81.E7Model

open CFSG.LieType.Steinberg.Minuscule CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.CurtisTits


variable {K : Type} [Field K]

abbrev Bor (K : Type) [Field K] : Subgroup ↥(e7Data_valid.minGroup K) :=
  borel (e7Datum K) (e7Data_valid.torus K)

abbrev Uni (K : Type) [Field K] : Subgroup ↥(e7Data_valid.minGroup K) := posUnipotent (e7Datum K)

abbrev W7 (K : Type) [Field K] : Type := (coxeterMatrix (e7Datum K).isFiniteType).Group

abbrev nW (K : Type) [Field K] (w : W7 K) : ↥(e7Data_valid.minGroup K) :=
  nrep (e7Datum_isCTGroupDatum K) w

abbrev Tor (K : Type) [Field K] : Subgroup ↥(e7Data_valid.minGroup K) :=
  ⨆ i, e7Data_valid.torus K i

abbrev endoE (g : ↥(e7Data_valid.minGroup K)) : Module.End K (V K) := e7Data_valid.endo K g

abbrev w0 : V K := Finsupp.single ⟨0, by decide⟩ 1

theorem bruhat_decomp (g : ↥(e7Data_valid.minGroup K)) :
    ∃ w, ∃ b₁ ∈ Bor K, ∃ b₂ ∈ Bor K, g = b₁ * nW K w * b₂ := by
  have h := iUnion_bruhatCell (e7Datum_isCTGroupDatum K) (e7Datum_steinbergExtras K)
  have hg : g ∈ ⋃ w, bruhatCell (e7Datum_isCTGroupDatum K) w := by rw [h]; trivial
  obtain ⟨w, hw⟩ := Set.mem_iUnion.1 hg
  exact ⟨w, hw⟩

theorem prod_nm_endo_single [CharP K 2] (l : List (Fin (Tag.rank .E7))) (a : Fin e7Data.d) :
    ∃ b : Fin e7Data.d,
      e7Data_valid.endo K ((l.map (e7Data_valid.nm K)).prod) (Finsupp.single a 1) =
        Finsupp.single b 1 := by
  induction l generalizing a with
  | nil =>
    refine ⟨a, ?_⟩
    rw [List.map_nil, List.prod_nil, e7Data_valid.endo_one, Module.End.one_apply]
  | cons i l ih =>
    obtain ⟨c, hc⟩ := ih a
    refine ⟨e7Data_valid.sRefl i c, ?_⟩
    rw [List.map_cons, List.prod_cons, e7Data_valid.endo_mul, Module.End.mul_apply, hc,
      e7Data_valid.endo_nm, e7Data_valid.nOp_single]
    split_ifs
    · rw [← Finsupp.single_neg, CharTwo.neg_eq]
    · rfl

theorem pr_zero_ne_neg_one_of_pos {γ : Fin (Tag.rank .E7) → ℤ} (hγ : IsRoot .E7 γ)
    (hpos : 0 < ht γ) : pr ⟨0, by decide⟩ γ ≠ -1 := by
  revert hpos
  refine (forall_isRoot_iff fun γ => 0 < ht γ → pr ⟨0, by decide⟩ γ ≠ -1).2 ?_ γ hγ
  unfold pr
  decide +kernel

theorem rootOp_w0_eq_zero_of_pos [CharP K 2] {γ : Fin (Tag.rank .E7) → ℤ} (hγ : IsRoot .E7 γ)
    (hpos : 0 < ht γ) : e7Data.rootOp K γ (w0 : V K) = 0 := by
  rw [rootOp_single (K := K) hγ ⟨0, by decide⟩, if_neg (pr_zero_ne_neg_one_of_pos hγ hpos)]

theorem endo_nW_single [CharP K 2] (w : W7 K) (a : Fin e7Data.d) :
    ∃ b : Fin e7Data.d, endoE (nW K w) (Finsupp.single a 1) = Finsupp.single b 1 := by
  obtain ⟨ω, hω, hw⟩ :=
    (coxeterMatrix (e7Datum K).isFiniteType).toCoxeterSystem.exists_isReduced w
  have h : nW K w = (ω.map (e7Data_valid.nm K)).prod := by
    rw [hw]
    exact CFSG.LieType.Steinberg.nrep_wordProd (e7Datum_isCTGroupDatum K) hω
  rw [h]
  exact prod_nm_endo_single (K := K) ω a

theorem endo_tor_single {t : ↥(e7Data_valid.minGroup K)} (ht : t ∈ Tor K) (a : Fin e7Data.d) :
    ∃ c : K, endoE t (Finsupp.single a 1) = c • Finsupp.single a 1 := by
  refine Subgroup.iSup_induction (fun i => e7Data_valid.torus K i)
    (C := fun s => ∃ c : K, endoE s (Finsupp.single a 1) = c • Finsupp.single a 1) ht ?_ ?_ ?_
  · intro i x hx
    obtain ⟨s, rfl⟩ := (e7Data_valid.mem_torus K).1 hx
    refine ⟨((s ^ e7Data.wt a i : Kˣ) : K), ?_⟩
    change e7Data_valid.endo K (e7Data_valid.hm K i s) (Finsupp.single a 1) = _
    rw [e7Data_valid.endo_hm, e7Data.hDiag_single]
  · refine ⟨1, ?_⟩
    change e7Data_valid.endo K 1 (Finsupp.single a 1) = _
    rw [e7Data_valid.endo_one, Module.End.one_apply, one_smul]
  · rintro x y ⟨c, hc⟩ ⟨d, hd⟩
    refine ⟨d * c, ?_⟩
    change e7Data_valid.endo K (x * y) (Finsupp.single a 1) = _
    rw [e7Data_valid.endo_mul, Module.End.mul_apply, hd, map_smul, hc, smul_smul]

theorem endo_uni_w0 [CharP K 2] {u : ↥(e7Data_valid.minGroup K)} (hu : u ∈ Uni K) :
    endoE u w0 = w0 := by
  have hu' : u ∈ ⨆ γ ∈ {γ | γ ∈ (e7Datum K).roots ∧ 0 < ht γ}, (e7Datum K).rootGroup γ := hu
  have hone : endoE (1 : ↥(e7Data_valid.minGroup K)) w0 = w0 := by
    change e7Data_valid.endo K 1 w0 = w0
    rw [e7Data_valid.endo_one, Module.End.one_apply]
  refine Subgroup.iSup_induction _ (C := fun v => endoE v w0 = w0) hu' ?_ hone ?_
  · intro γ x hx
    by_cases hγ : γ ∈ {γ | γ ∈ (e7Datum K).roots ∧ 0 < ht γ}
    · rw [iSup_pos hγ] at hx
      obtain ⟨c, rfl⟩ := (e7Data_valid.mem_rootGroup K).1 hx
      obtain ⟨hγr, hγp⟩ : γ ∈ (e7Datum K).roots ∧ 0 < ht γ := hγ
      have hr : IsRoot .E7 γ := (e7Data_valid.mem_minDatum_roots isFiniteType_cartan_E7 K).1 hγr
      change e7Data_valid.endo K (e7Data_valid.xm K γ c) w0 = w0
      rw [e7Data_valid.endo_xm, LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply,
        rootOp_w0_eq_zero_of_pos (K := K) hr hγp, smul_zero, add_zero]
    · rw [iSup_neg hγ, Subgroup.mem_bot] at hx
      subst hx
      exact hone
  · intro x y hx hy
    change endoE x w0 = w0 at hx
    change endoE y w0 = w0 at hy
    change e7Data_valid.endo K (x * y) w0 = w0
    rw [e7Data_valid.endo_mul, Module.End.mul_apply, hy]
    exact hx

theorem endo_bor_w0 [CharP K 2] {b : ↥(e7Data_valid.minGroup K)} (hb : b ∈ Bor K) :
    ∃ c : K, endoE b w0 = c • w0 := by
  have hb' := hb
  rw [← SetLike.mem_coe, CFSG.LieType.Steinberg.coe_borel (e7Datum_isCTGroupDatum K),
    Set.mem_mul] at hb'
  obtain ⟨t, ht, u, hu, rfl⟩ := hb'
  obtain ⟨c, hc⟩ := endo_tor_single (K := K) (SetLike.mem_coe.1 ht) ⟨0, by decide⟩
  refine ⟨c, ?_⟩
  have e : endoE (t * u) w0 = endoE t w0 := by
    change e7Data_valid.endo K (t * u) w0 = e7Data_valid.endo K t w0
    rw [e7Data_valid.endo_mul, Module.End.mul_apply, endo_uni_w0 (K := K) (SetLike.mem_coe.1 hu)]
  rw [e]
  exact hc

theorem bor_eq_mul {b : ↥(e7Data_valid.minGroup K)} (hb : b ∈ Bor K) :
    ∃ u ∈ Uni K, ∃ t ∈ Tor K, b = u * t := by
  have hb' := hb
  rw [← SetLike.mem_coe, CFSG.LieType.Steinberg.coe_borel (e7Datum_isCTGroupDatum K),
    Set.mem_mul] at hb'
  obtain ⟨t, ht, u, hu, rfl⟩ := hb'
  have htB : t ∈ Bor K := CFSG.LieType.Steinberg.iSup_le_borel (SetLike.mem_coe.1 ht)
  have hn := CFSG.LieType.Steinberg.borel_le_normalizer_posUnipotent
    (e7Datum_isCTGroupDatum K) htB
  refine ⟨t * u * t⁻¹, ?_, t, SetLike.mem_coe.1 ht, ?_⟩
  · exact (Subgroup.mem_normalizer_iff.1 hn u).1 hu
  · exact (inv_mul_cancel_right _ _).symm

end CFSG.RankThree.GF2n.Smith81.E7Model
