module

public import CFSG.Quasithin.MS93.S5A52
public import CFSG.Quasithin.MS93.S5A52Stmt
public import CFSG.Quasithin.MS93.S5A56
public import CFSG.Quasithin.MS93.S38EPU
public import CFSG.Quasithin.MS93.MSPLevi
public import CFSG.Quasithin.MS93.S33SpS5

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix

namespace S5

section Sp

variable {F : Type} [Field F] [Fintype F] [CharP F 2]

theorem commute_transv_of_mem_stab {v : MSP.V4 F} (hv : v ≠ 0) {g : MSP.Sp4 F}
    (hg : g ∈ MSP.stab (F ∙ v)) {e : ℕ} (hge : g ^ 2 ^ e = 1) (c : F) :
    g * MSP.transv v c = MSP.transv v c * g := by
  obtain ⟨l, hl⟩ : ∃ l : F, MSP.mat g *ᵥ v = l • v := by
    obtain ⟨l, hl⟩ := Submodule.mem_span_singleton.1
      (MSP.mulVec_mem_of_mem_stab hg (Submodule.mem_span_singleton_self v))
    exact ⟨l, hl.symm⟩
  have hpow : ∀ n : ℕ, MSP.mat (g ^ n) *ᵥ v = l ^ n • v := by
    intro n
    induction n with
    | zero => rw [pow_zero, pow_zero, one_smul, MSP.mat_one, Matrix.one_mulVec]
    | succ n ih => rw [pow_succ, MSP.mat_mul_mulVec, hl, Matrix.mulVec_smul, ih, smul_smul,
        pow_succ, mul_comm]
  have h1 : l ^ 2 ^ e = 1 := by
    have := hpow (2 ^ e)
    rw [hge, MSP.mat_one, Matrix.one_mulVec] at this
    have h0 : (l ^ 2 ^ e - 1) • v = 0 := by rw [sub_smul, ← this, one_smul, sub_self]
    rcases smul_eq_zero.1 h0 with h0 | h0
    · exact sub_eq_zero.1 h0
    · exact absurd h0 hv
  have hl0 : l ≠ 0 := by
    rintro rfl
    rw [zero_pow (pow_ne_zero _ two_ne_zero)] at h1
    exact zero_ne_one h1
  have hq : l ^ (Fintype.card F - 1) = 1 := FiniteField.pow_card_sub_one_eq_one l hl0
  obtain ⟨n, -, hn⟩ := FiniteField.card F 2
  have hodd : Odd (Fintype.card F - 1) := by
    rw [hn]
    have : 1 ≤ 2 ^ (n : ℕ) := Nat.one_le_two_pow
    have h2 : Even (2 ^ (n : ℕ)) := (Nat.even_pow' n.ne_zero).2 even_two
    obtain ⟨m, hm⟩ := h2
    exact ⟨m - 1, by omega⟩
  have hcop : Nat.Coprime (2 ^ e) (Fintype.card F - 1) :=
    Nat.Coprime.pow_left _ (Nat.coprime_two_left.2 hodd)
  have hl1 : l = 1 := by
    have := (pow_gcd_eq_one (a := l) (m := 2 ^ e) (n := Fintype.card F - 1)).2 ⟨h1, hq⟩
    rwa [hcop.gcd_eq_one, pow_one] at this
  have hc := MSP.transv_conj g v c
  rw [hl, hl1, one_smul] at hc
  calc g * MSP.transv v c = g * MSP.transv v c * g⁻¹ * g := by group
    _ = MSP.transv v c * g := by rw [hc]

end Sp

section Shape

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} {k : ℕ} {F : Type} [Field F]
  [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)} (h : PUHyp M T L)

theorem commutator_zm_le_centralizer_of_xPoint (hd : IsSp4Data M T L k F a)
    {γ : Vtx (puAmalgam h.le)} (hZst : ZM (puAmalgam h.le) γ ≤ stab _ (baseA _))
    {p : Submodule F (MSP.V4 F)} (hp : MSP.IsPoint p) (hZp : vIm h.le a (ZM _ γ) = MSP.xPoint p)
    {P : Subgroup (puAmalgam h.le).Universal} (hPst : P ≤ stab _ (baseA (puAmalgam h.le)))
    (hP2 : IsPGroup 2 P) (hPn : P ≤ Subgroup.normalizer (ZM (puAmalgam h.le) γ : Set _)) :
    ⁅ZM (puAmalgam h.le) γ, P⁆ ≤
      Subgroup.centralizer (ZM (puAmalgam h.le) (baseA _) : Set _) := by
  have := hd.charP
  have hst : stab (puAmalgam h.le) (baseA _) = (puAmalgam h.le).ofA.range :=
    (ofA_range_eq h.le).symm
  have hZα : ZM (puAmalgam h.le) (baseA _) = imM h.le (Z0q M T) := puAmalgam.zm_baseA h.le
  obtain ⟨v, hv, rfl⟩ := MSP.exists_eq_span_of_isPoint hp
  rw [Subgroup.commutator_le]
  intro z hz x hx
  obtain ⟨z₀, rfl⟩ : ∃ z₀ : ↥M, (puAmalgam h.le).ofA z₀ = z := by
    have := hZst hz
    rw [hst] at this
    exact this
  obtain ⟨x₀, rfl⟩ : ∃ x₀ : ↥M, (puAmalgam h.le).ofA x₀ = x := by
    have := hPst hx
    rw [hst] at this
    exact this
  have hconj : ∀ y : ↥M, (puAmalgam h.le).ofA y ∈ P → ∀ w ∈ MSP.xPoint (F ∙ v),
      a y * w * (a y)⁻¹ ∈ MSP.xPoint (F ∙ v) := by
    intro y hy w hw
    rw [← hZp] at hw ⊢
    obtain ⟨m, hm, rfl⟩ := hw
    refine ⟨y * m * y⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
    change (puAmalgam h.le).ofA (y * m * y⁻¹) ∈ ZM _ γ
    rw [map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.1 (hPn hy) _).1 hm
  have hxn : a x₀ ∈ Subgroup.normalizer (MSP.xPoint (F ∙ v) : Set _) := by
    rw [Subgroup.mem_normalizer_iff]
    intro w
    refine ⟨hconj x₀ hx w, fun hw => ?_⟩
    have hx' : (puAmalgam h.le).ofA x₀⁻¹ ∈ P := by rw [map_inv]; exact inv_mem hx
    have := hconj x₀⁻¹ hx' _ hw
    rwa [map_inv, inv_inv, ← mul_assoc, ← mul_assoc, inv_mul_cancel, one_mul,
      mul_assoc, inv_mul_cancel, mul_one] at this
  rw [MSP.normalizer_xPoint hp] at hxn
  obtain ⟨e, he⟩ := hP2 ⟨_, hx⟩
  have hxe : a x₀ ^ 2 ^ e = 1 := by
    have h1 : (puAmalgam h.le).ofA (x₀ ^ 2 ^ e) = (puAmalgam h.le).ofA 1 := by
      rw [map_pow, map_one]
      simpa using congrArg Subtype.val he
    rw [← map_pow, (puAmalgam h.le).ofA_injective h1, map_one]
  have hzp : a z₀ ∈ MSP.xPoint (F ∙ v) := hZp ▸ ⟨z₀, hz, rfl⟩
  obtain ⟨c, hc⟩ := (MSP.mem_xPoint_span hv).1 hzp
  have hcomm := commute_transv_of_mem_stab hv hxn hxe c
  rw [hc] at hcomm
  have hk : a (z₀ * x₀ * z₀⁻¹ * x₀⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← hcomm]
    group
  have hkZ := hd.kerG_le_centralizer_Z0q h ((mem_kerG a).2 ⟨(z₀ * x₀ * z₀⁻¹ * x₀⁻¹).2, hk⟩)
  refine Subgroup.mem_centralizer_iff.2 fun w hw => ?_
  rw [hZα] at hw
  obtain ⟨w₀, hw₀, rfl⟩ := hw
  have e1 : ⁅(puAmalgam h.le).ofA z₀, (puAmalgam h.le).ofA x₀⁆ =
      (puAmalgam h.le).ofA (z₀ * x₀ * z₀⁻¹ * x₀⁻¹) := by
    rw [commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv]
  rw [e1, ← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hkZ _ (Subgroup.mem_subgroupOf.1 hw₀))

theorem qv_le_stab_of_dist_le_two {α γ : Vtx (puAmalgam h.le)} (hα : IsMVtx _ α)
    (hd : (puAmalgam h.le).treeGraph.dist α γ ≤ 2) : Qv _ α ≤ stab _ γ := by
  rcases Nat.lt_or_ge ((puAmalgam h.le).treeGraph.dist α γ) 2 with h1 | h2
  · exact iInf₂_le (f := fun ρ (_ : ρ ∈ {ρ : Vtx (puAmalgam h.le) |
      (puAmalgam h.le).treeGraph.dist α ρ ≤ 1}) => stab _ ρ) γ (by
        simp only [Set.mem_ofPred_eq]
        omega)
  · have hd2 : (puAmalgam h.le).treeGraph.dist α γ = 2 := le_antisymm hd h2
    have hadj := adj_geo_one (puAmalgam h.le) (show 0 < (puAmalgam h.le).treeGraph.dist α γ by
      omega)
    have hadj' : (puAmalgam h.le).treeGraph.Adj (geo _ α γ 1) γ := by
      have := adj_geo (puAmalgam h.le) (i := 1)
        (show 1 < (puAmalgam h.le).treeGraph.dist α γ by omega)
      rwa [show (1 + 1 : ℕ) = (puAmalgam h.le).treeGraph.dist α γ by omega, geo_dist] at this
    exact (qv_le_qv _ h.hyp20 hα hadj).trans (qv_le_stab_of_adj _ hadj')

theorem commutator_zm_le_centralizer_of_small (hd : IsSp4Data M T L k F a)
    (hsmall : ∀ α'' : Vtx (puAmalgam h.le), IsCritical _ (baseA (puAmalgam h.le)) α'' →
      ¬ (2 ^ k) ^ 2 ≤ (Qv _ α'').relIndex (ZM _ (baseA (puAmalgam h.le))))
    {δ γ : Vtx (puAmalgam h.le)} (hc : IsCritical _ δ γ)
    {P : Subgroup (puAmalgam h.le).Universal} (hP2 : IsPGroup 2 P) (hPδ : P ≤ stab _ δ)
    (hPn : P ≤ Subgroup.normalizer (ZM (puAmalgam h.le) γ : Set _)) :
    ⁅ZM (puAmalgam h.le) γ, P⁆ ≤ Subgroup.centralizer (ZM (puAmalgam h.le) δ : Set _) := by
  obtain ⟨c, rfl⟩ := exists_eq_smul_baseA _ hc.1
  have hcrit : IsCritical _ (baseA (puAmalgam h.le)) (c⁻¹ • γ) := by
    have := (isCritical_smul _ c⁻¹ _ _).2 hc
    rwa [inv_smul_smul] at this
  rcases S33.shape_of_sp4Data h hd hcrit with ⟨-, -, p, hp, hZp⟩ | ⟨hrel1, -, -⟩
  swap
  · exact absurd hrel1 (hsmall _ hcrit)
  have hZγ' : ZM (puAmalgam h.le) (c⁻¹ • γ) = (ZM _ γ).map (MulAut.conj c⁻¹).toMonoidHom :=
    zm_smul _ c⁻¹ γ
  have hZα : ZM (puAmalgam h.le) (baseA _) =
      (ZM _ (c • baseA (puAmalgam h.le))).map (MulAut.conj c⁻¹).toMonoidHom := by
    rw [← zm_smul, inv_smul_smul]
  have hZst : ZM (puAmalgam h.le) (c⁻¹ • γ) ≤ stab _ (baseA _) :=
    zm_le_stab_of_isCritical _ h.hyp20 h.critDist_pos hcrit
  set P' := P.map (MulAut.conj c⁻¹).toMonoidHom with hP'
  have hP'st : P' ≤ stab _ (baseA (puAmalgam h.le)) := by
    rintro _ ⟨x, hx, rfl⟩
    have := (mem_stab_smul _).1 (hPδ hx)
    change c⁻¹ * x * c⁻¹⁻¹ ∈ _
    rwa [inv_inv]
  have hP'2 : IsPGroup 2 P' := hP2.map _
  have hmemγ : ∀ w, w ∈ ZM (puAmalgam h.le) (c⁻¹ • γ) ↔ c * w * c⁻¹ ∈ ZM _ γ := by
    intro w
    rw [hZγ', mem_map_conj, inv_inv]
  have hP'n : P' ≤ Subgroup.normalizer (ZM (puAmalgam h.le) (c⁻¹ • γ) : Set _) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro w
    change w ∈ _ ↔ c⁻¹ * x * c⁻¹⁻¹ * w * (c⁻¹ * x * c⁻¹⁻¹)⁻¹ ∈ _
    rw [hmemγ, hmemγ]
    have e : c * (c⁻¹ * x * c⁻¹⁻¹ * w * (c⁻¹ * x * c⁻¹⁻¹)⁻¹) * c⁻¹ =
        x * (c * w * c⁻¹) * x⁻¹ := by group
    rw [e]
    exact Subgroup.mem_normalizer_iff.1 (hPn hx) _
  have key := commutator_zm_le_centralizer_of_xPoint h hd hZst hp hZp hP'st hP'2 hP'n
  rw [Subgroup.commutator_le]
  intro z hz x hx
  refine Subgroup.mem_centralizer_iff.2 fun w hw => ?_
  have hz' : c⁻¹ * z * c⁻¹⁻¹ ∈ ZM (puAmalgam h.le) (c⁻¹ • γ) := by
    rw [hZγ']
    exact ⟨z, hz, rfl⟩
  have hx' : c⁻¹ * x * c⁻¹⁻¹ ∈ P' := ⟨x, hx, rfl⟩
  have hw' : c⁻¹ * w * c⁻¹⁻¹ ∈ ZM (puAmalgam h.le) (baseA _) := by
    rw [hZα]
    exact ⟨w, hw, rfl⟩
  have h1 := Subgroup.mem_centralizer_iff.1 (key (Subgroup.commutator_mem_commutator hz' hx'))
    _ hw'
  have e : ⁅c⁻¹ * z * c⁻¹⁻¹, c⁻¹ * x * c⁻¹⁻¹⁆ = c⁻¹ * ⁅z, x⁆ * c⁻¹⁻¹ := by
    simp only [commutatorElement_def]
    group
  rw [e] at h1
  calc w * ⁅z, x⁆ = c * ((c⁻¹ * w * c⁻¹⁻¹) * (c⁻¹ * ⁅z, x⁆ * c⁻¹⁻¹)) * c⁻¹ := by group
    _ = c * ((c⁻¹ * ⁅z, x⁆ * c⁻¹⁻¹) * (c⁻¹ * w * c⁻¹⁻¹)) * c⁻¹ := by rw [h1]
    _ = ⁅z, x⁆ * w := by group

theorem commutator_zm_qv_le_of_small (hd : IsSp4Data M T L k F a)
    (hb : critDist (puAmalgam h.le) = 4)
    (hsmall : ∀ α'' : Vtx (puAmalgam h.le), IsCritical _ (baseA (puAmalgam h.le)) α'' →
      ¬ (2 ^ k) ^ 2 ≤ (Qv _ α'').relIndex (ZM _ (baseA (puAmalgam h.le))))
    (γ δ : Vtx (puAmalgam h.le)) (hγ : IsMVtx _ γ) (hδ : IsMVtx _ δ)
    (hdγ : (puAmalgam h.le).treeGraph.dist (baseA _) γ ≤ 2)
    (hdδ : (puAmalgam h.le).treeGraph.dist (baseA _) δ ≤ 2) :
    ⁅ZM (puAmalgam h.le) γ, Qv (puAmalgam h.le) (baseA _)⁆ ≤
      Subgroup.centralizer (ZM (puAmalgam h.le) δ : Set (puAmalgam h.le).Universal) := by
  have hyp := h.hyp20
  have hb0 := h.critDist_pos
  have hα := isMVtx_baseA (puAmalgam h.le)
  have hQγ := qv_le_stab_of_dist_le_two h hα hdγ
  have hQδ := qv_le_stab_of_dist_le_two h hα hdδ
  have hle : ⁅ZM (puAmalgam h.le) γ, Qv _ (baseA _)⁆ ≤ ZM _ γ :=
    Subgroup.le_normalizer_iff_commutator_le_left.1 (hQγ.trans (stab_le_normalizer_zm _ γ))
  have hQZ : ∀ ε : Vtx (puAmalgam h.le), IsMVtx _ ε →
      Qv _ ε ≤ Subgroup.centralizer (ZM (puAmalgam h.le) ε : Set (puAmalgam h.le).Universal) :=
    fun ε hε =>
    (qv_le_centralizer_xm _ ε).trans (Subgroup.centralizer_le (zm_le_xm _ hyp hb0 hε))
  by_cases h1 : ZM (puAmalgam h.le) γ ≤ Qv _ δ
  · exact hle.trans (h1.trans (hQZ δ hδ))
  by_cases h2 : ZM (puAmalgam h.le) δ ≤ Qv _ γ
  · intro x hx
    refine Subgroup.mem_centralizer_iff.2 fun w hw => ?_
    exact (Subgroup.mem_centralizer_iff.1 (hQZ γ hγ (h2 hw)) x (hle hx)).symm
  have hdist : (puAmalgam h.le).treeGraph.dist γ δ = critDist (puAmalgam h.le) := by
    have hge : critDist (puAmalgam h.le) ≤ (puAmalgam h.le).treeGraph.dist γ δ := by
      by_contra hlt
      exact h1 (zm_le_qv_of_dist_lt _ hγ (by omega))
    have htri := dist_triangle (puAmalgam h.le) γ (baseA _) δ
    rw [tdist_comm _ γ (baseA _)] at htri
    omega
  have hcγδ : IsCritical _ γ δ := ⟨hγ, hdist, h1⟩
  have hcδγ := ms22_iii _ hyp hb0 h.centHyp hcγδ
  have hQ2 : IsPGroup 2 (Qv (puAmalgam h.le) (baseA _)) := by
    have hnot : ¬ IsMVtx _ (baseB (puAmalgam h.le)) :=
      (isMVtx_iff_of_adj _ (adj_baseA_baseB _)).1 hα
    exact (isPGroup_qv _ hyp hnot).to_le (qv_le_qv _ hyp hα (adj_baseA_baseB _))
  exact commutator_zm_le_centralizer_of_small h hd hsmall hcδγ hQ2 hQδ
    (hQγ.trans (stab_le_normalizer_zm _ γ))

end Shape

end S5

open S5 in
theorem s52_of (h52i : S52i) : S52 := by
  intro G _ _ M T L h hmin hb k F _ _ a hd α' hc
  have hyp := h.hyp20
  have hα := isMVtx_baseA (puAmalgam h.le)
  have hVQ : ⁅Vv (puAmalgam h.le) (baseA _), Qv (puAmalgam h.le) (baseA _)⁆ ≤
      centerOf (Vv (puAmalgam h.le) (baseA _)) := by
    have hev := ms21_v _ hyp
    rcases (show critDist (puAmalgam h.le) = 4 ∨ 4 < critDist (puAmalgam h.le) by
      obtain ⟨m, hm⟩ := hev
      omega) with hb4 | hb6
    · by_cases hΛ : ∃ α'' : Vtx (puAmalgam h.le), IsCritical _ (baseA (puAmalgam h.le)) α'' ∧
          (2 ^ k) ^ 2 ≤ (Qv _ α'').relIndex (ZM _ (baseA (puAmalgam h.le)))
      · obtain ⟨α'', hc'', hrel⟩ := hΛ
        have hON := h52i G M T L h hmin hb k F _ _ a hd α'' hc'' hrel
        set V := Vv (puAmalgam h.le) (baseA _)
        set Q := Qv (puAmalgam h.le) (baseA _)
        have hVs : stab (puAmalgam h.le) (baseA _) ≤ Subgroup.normalizer (V : Set _) :=
          stab_le_normalizer_of_smul _ (F := fun ρ => Vi _ ρ 2) (fun g ρ => vi_smul _ g ρ 2) _
        have hQs : stab (puAmalgam h.le) (baseA _) ≤ Subgroup.normalizer (Q : Set _) :=
          stab_le_normalizer_qv _ _
        have hZs : stab (puAmalgam h.le) (baseA _) ≤
            Subgroup.normalizer (ZM (puAmalgam h.le) (baseA _) : Set _) :=
          stab_le_normalizer_zm _ _
        have hVQV : ⁅V, Q⁆ ≤ V :=
          Subgroup.le_normalizer_iff_commutator_le_left.1 ((qv_le_stab _ _).trans hVs)
        have hZV : ZM (puAmalgam h.le) (baseA _) ≤ V := S38E.zm_le_vv _ hα (by simp)
        refine commutator_vv_qv_le_center_of _ hyp hb hα (adj_baseA_baseB _)
          (S38E.stab_baseA_eq h) ?_
        exact hON.2 _ _ _ le_rfl le_sup_right (sup_le hVQV hZV) le_rfl hZs
          (le_normalizer_sup (S38E.le_normalizer_commutator' hVs hQs) hZs) hVs
      · push Not at hΛ
        exact commutator_vv_qv_le_center_of_pairs _ hα
          (commutator_zm_qv_le_of_small h hd hb4 fun α'' hc'' => not_le.2 (hΛ α'' hc''))
    · have hab := commutator_vv_eq_bot _ hyp hb6 hα
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at hab
      have hVs : stab (puAmalgam h.le) (baseA _) ≤
          Subgroup.normalizer (Vv (puAmalgam h.le) (baseA _) : Set _) :=
        stab_le_normalizer_of_smul _ (F := fun ρ => Vi _ ρ 2) (fun g ρ => vi_smul _ g ρ 2) _
      have hVQV := Subgroup.le_normalizer_iff_commutator_le_left.1 ((qv_le_stab _ _).trans hVs)
      exact le_inf hVQV (hVQV.trans hab)
  exact ⟨fun hrel => h52i G M T L h hmin hb k F _ _ a hd α' hc hrel, hVQ,
    commutator_vv_le_xm_of _ hyp hb hα hVQ, commutator_xm_vv_eq_bot_of _ hVQ α' _⟩

end CFSG.Quasithin.MS93
