module

public import CFSG.RankThree.GF2n.Smith81.S81TFin
public import CFSG.RankThree.GF2n.Smith81.S81E7Fe7

public section

namespace CFSG.RankThree.GF2n.Smith81.MinuscT

open CFSG.RankThree.GF2n.Smith81.E7Model CFSG.LieType.Steinberg.Minuscule CFSG.Blueprint.Chevalley


section Clique

variable {K : Type} [Field K] [CharP K 2]

theorem pr_eq_neg_one_of_wt_eq {α : Rt} (hα : IsRoot .E7 α) {a μ : Fin e7Data.d}
    (h : e7Data.wt a = e7Data.wt μ + MinData.toWeight α) : pr μ α = -1 ∧ shift α μ = a := by
  refine ⟨?_, shift_eq h⟩
  have h1 : pr a α = pr μ α + ipR α α := by
    unfold pr ipR
    rw [h, add_dotProduct]
  rw [ipR_self hα] at h1
  have h2 := pr_mem hα a
  have h3 := pr_mem hα μ
  omega

private theorem aux_clq_isRoot_rt (k : Fin 126) : IsRoot .E7 (rt k) := by
  have hlen : (Tag.rootCertificate .E7).roots.length = 126 := Tag.rootCertificate_length .E7
  exact RootCertificate.isRoot_root (Tag.rootCertificate_check .E7) k (by omega)

private theorem aux_clq_rootOp_sum (d : Fin e7Data.d → K) {γ : Rt} (hγ : IsRoot .E7 γ) :
    ∀ L : List (Fin e7Data.d), (∀ b ∈ L, pr b γ ≠ -1) →
      e7Data.rootOp K γ ((L.map fun b => d b • (Finsupp.single b 1 : V K)).sum) = 0 := by
  intro L
  induction L with
  | nil => intro _; simp
  | cons b L ih =>
    intro h
    have hb : pr b γ ≠ -1 := h b (List.mem_cons_self ..)
    have h' : ∀ c ∈ L, pr c γ ≠ -1 := fun c hc => h c (List.mem_cons_of_mem _ hc)
    rw [List.map_cons, List.sum_cons, map_add, map_smul, rootOp_single (K := K) hγ b, if_neg hb,
      smul_zero, zero_add]
    exact ih h'

private theorem aux_clq_prod (μ : Fin e7Data.d) (α : Fin e7Data.d → Rt) (d : Fin e7Data.d → K) :
    ∀ L : List (Fin e7Data.d), L.Nodup →
      (∀ a ∈ L, IsRoot .E7 (α a) ∧ e7Data.wt a = e7Data.wt μ + MinData.toWeight (α a)) →
      (∀ a ∈ L, ∀ b ∈ L, b ≠ a → pr b (α a) ≠ -1) →
      (((L.map fun a => e7Data_valid.xu K (α a) (d a)).prod : (Module.End K (V K))ˣ) :
          Module.End K (V K)) (Finsupp.single μ 1) =
        Finsupp.single μ 1 + (L.map fun a => d a • (Finsupp.single a 1 : V K)).sum := by
  intro L
  induction L with
  | nil => intro _ _ _; simp
  | cons a L ih =>
    intro hnd hroot horth
    obtain ⟨haL, hL⟩ := List.nodup_cons.1 hnd
    have hroot' : ∀ c ∈ L, IsRoot .E7 (α c) ∧ e7Data.wt c = e7Data.wt μ + MinData.toWeight (α c) :=
      fun c hc => hroot c (List.mem_cons_of_mem _ hc)
    have horth' : ∀ c ∈ L, ∀ b ∈ L, b ≠ c → pr b (α c) ≠ -1 :=
      fun c hc b hb hbc => horth c (List.mem_cons_of_mem _ hc) b (List.mem_cons_of_mem _ hb) hbc
    obtain ⟨hαroot, hwt⟩ := hroot a (List.mem_cons_self ..)
    obtain ⟨hpr, hsh⟩ := pr_eq_neg_one_of_wt_eq hαroot hwt
    have hE1 : e7Data.rootOp K (α a) (Finsupp.single μ 1) = Finsupp.single a 1 := by
      rw [rootOp_single (K := K) hαroot μ, if_pos hpr, hsh]
    have hEL : e7Data.rootOp K (α a) ((L.map fun b => d b • (Finsupp.single b 1 : V K)).sum) = 0 :=
      aux_clq_rootOp_sum (K := K) d hαroot L fun b hb =>
        horth a (List.mem_cons_self ..) b (List.mem_cons_of_mem _ hb) fun e => haL (e ▸ hb)
    simp only [List.map_cons, List.prod_cons, Units.val_mul, Module.End.mul_apply,
      ih hL hroot' horth', e7Data_valid.xu_val K (α a) (d a), List.sum_cons, LinearMap.add_apply,
      Module.End.one_apply, LinearMap.smul_apply, map_add, hE1, hEL, smul_zero, add_zero]
    abel

theorem isHWLine_of_clique {inL : Fin e7Data.d → Prop} {A2 S : List Rt} (hCl : CliqueOK inL A2 S)
    (s : V K) (hs0 : s ≠ 0) (hsupp : ∀ a, s a ≠ 0 → inMtop inL A2 S a) :
    IsHWLine K (Submodule.span K {s}) := by
  obtain ⟨μ, hμ⟩ : ∃ μ, s μ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hs0 (Finsupp.ext fun b => by simpa using hcon b)
  have hμM : inMtop inL A2 S μ := hsupp μ hμ
  have hex : ∀ a : Fin e7Data.d, ∃ k : Fin 126, (inMtop inL A2 S a ∧ a ≠ μ) →
      MinData.toWeight (rt k) = e7Data.wt a - e7Data.wt μ ∧
        ∀ ξ : Fin e7Data.d, inMtop inL A2 S ξ → ξ ≠ μ → ξ ≠ a → pr ξ (rt k) = 0 := by
    intro a
    by_cases ha : inMtop inL A2 S a ∧ a ≠ μ
    · obtain ⟨k, hk1, hk2⟩ := hCl μ a hμM ha.1 (Ne.symm ha.2)
      exact ⟨k, fun _ => ⟨hk1, hk2⟩⟩
    · exact ⟨0, fun h => absurd h ha⟩
  choose kf hkf using hex
  obtain ⟨α, hα⟩ : ∃ α : Fin e7Data.d → Rt, ∀ a, α a = rt (kf a) :=
    ⟨fun a => rt (kf a), fun _ => rfl⟩
  obtain ⟨d, hd⟩ : ∃ d : Fin e7Data.d → K, ∀ a, d a = s a / s μ :=
    ⟨fun a => s a / s μ, fun _ => rfl⟩
  obtain ⟨T, hT⟩ : ∃ T : Finset (Fin e7Data.d), T = s.support.erase μ := ⟨_, rfl⟩
  have hmemT : ∀ a, a ∈ T ↔ a ≠ μ ∧ s a ≠ 0 := fun a => by
    rw [hT, Finset.mem_erase, Finsupp.mem_support_iff]
  have hμT : μ ∉ T := fun h => ((hmemT μ).1 h).1 rfl
  obtain ⟨L, hL⟩ : ∃ L : List (Fin e7Data.d), L = T.toList := ⟨_, rfl⟩
  have hmemL : ∀ a, a ∈ L ↔ a ∈ T := fun a => by rw [hL, Finset.mem_toList]
  have hLnd : L.Nodup := by rw [hL]; exact Finset.nodup_toList T
  have hLprop : ∀ a ∈ L, inMtop inL A2 S a ∧ a ≠ μ := by
    intro a ha
    obtain ⟨h1, h2⟩ := (hmemT a).1 ((hmemL a).1 ha)
    exact ⟨hsupp a h2, h1⟩
  have hroot : ∀ a ∈ L, IsRoot .E7 (α a) ∧
      e7Data.wt a = e7Data.wt μ + MinData.toWeight (α a) := by
    intro a ha
    obtain ⟨hM, hne⟩ := hLprop a ha
    obtain ⟨hk1, -⟩ := hkf a ⟨hM, hne⟩
    rw [hα a]
    refine ⟨aux_clq_isRoot_rt (kf a), ?_⟩
    rw [hk1]
    abel
  have horth : ∀ a ∈ L, ∀ b ∈ L, b ≠ a → pr b (α a) ≠ -1 := by
    intro a ha b hb hba
    obtain ⟨hM, hne⟩ := hLprop a ha
    obtain ⟨hMb, hneb⟩ := hLprop b hb
    obtain ⟨-, hk2⟩ := hkf a ⟨hM, hne⟩
    rw [hα a, hk2 b hMb hneb hba]
    norm_num
  obtain ⟨G, hG⟩ : ∃ G : (Module.End K (V K))ˣ,
      G = (L.map fun a => e7Data_valid.xu K (α a) (d a)).prod := ⟨_, rfl⟩
  have hprod := aux_clq_prod (K := K) μ α d L hLnd hroot horth
  rw [← hG] at hprod
  have hGmem : G ∈ EGrp K := by
    rw [hG]
    refine Subgroup.list_prod_mem _ fun x hx => ?_
    obtain ⟨a, -, rfl⟩ := List.mem_map.1 hx
    exact e7Data_valid.xu_mem K (α a) (d a)
  have hsum : (L.map fun a => d a • (Finsupp.single a 1 : V K)).sum =
      ∑ a ∈ T, (s a / s μ) • (Finsupp.single a 1 : V K) := by
    rw [hL, Finset.sum_map_toList]
    exact Finset.sum_congr rfl fun a _ => by rw [hd a]
  have hsplit : s = s μ • (Finsupp.single μ 1 : V K) +
      ∑ a ∈ T, s a • (Finsupp.single a 1 : V K) := by
    ext b
    rw [Finsupp.add_apply, Finsupp.finsetSum_apply]
    simp only [Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
    by_cases hb : b = μ
    · rw [hb]
      simp [hμT]
    · by_cases hsb : s b = 0
      · simp [hsb, Ne.symm hb]
      · have hbT : b ∈ T := (hmemT b).2 ⟨hb, hsb⟩
        simp [hbT, Ne.symm hb]
  have hs' : s = s μ • (G : Module.End K (V K)) (Finsupp.single μ 1) := by
    rw [hprod, hsum, smul_add, Finset.smul_sum]
    conv_lhs => rw [hsplit]
    congr 1
    exact Finset.sum_congr rfl fun a _ => by rw [smul_smul, mul_div_cancel₀ _ hμ]
  have hspan : Submodule.span K {s} =
      (Submodule.span K {(Finsupp.single μ 1 : V K)}).map (G : Module.End K (V K)) := by
    rw [hs', Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.2 hμ), Submodule.map_span,
      Set.image_singleton]
  rw [hspan]
  exact IsHWLine.map (isHWLine_weight (K := K) μ) hGmem

end Clique

end CFSG.RankThree.GF2n.Smith81.MinuscT
