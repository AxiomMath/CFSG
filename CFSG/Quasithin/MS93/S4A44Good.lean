module

public import CFSG.Quasithin.MS93.S4A44Lin
public import CFSG.Quasithin.MS93.S45Path

public section

namespace CFSG.Quasithin.MS93.S4A

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
  CFSG.LocalAnalysis.ComponentInitial
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix

section Plane

open Matrix LinearFlag

variable {F : Type} [Field F]

theorem sub_mem_of_mem_stabilizer_of_pow [CharP F 2] {K : Submodule F (Fin 3 → F)}
    (hK : Module.finrank F K = 2) {s : SL3 F} (hs : s ∈ LinearFlag.stabilizer K) {m : ℕ}
    (hm : s ^ 2 ^ m = 1) (w : Fin 3 → F) :
    (s : Matrix (Fin 3) (Fin 3) F) *ᵥ w - w ∈ K := by
  have hsK : ∀ x ∈ K, (s : Matrix (Fin 3) (Fin 3) F) *ᵥ x ∈ K := fun x hx => by
    rw [← (mem_stabilizer.mp hs)]
    exact ⟨x, hx, rfl⟩
  by_cases hw : w ∈ K
  · exact K.sub_mem (hsK w hw) hw
  have htop := sup_eq_top_of_not_le hK (c := F ∙ w) (fun hle =>
    hw (hle (Submodule.mem_span_singleton_self w)))
  have hsw : (s : Matrix (Fin 3) (Fin 3) F) *ᵥ w ∈ K ⊔ F ∙ w := by
    rw [htop]; exact Submodule.mem_top
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hsw
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hz
  have key : ∀ n : ℕ, ∃ k ∈ K,
      ((s : Matrix (Fin 3) (Fin 3) F) ^ n) *ᵥ w = k + c ^ n • w := by
    intro n
    induction n with
    | zero => exact ⟨0, K.zero_mem, by simp⟩
    | succ n ih =>
      obtain ⟨k, hk, hkn⟩ := ih
      refine ⟨(s : Matrix (Fin 3) (Fin 3) F) *ᵥ k + c ^ n • y,
        K.add_mem (hsK k hk) (K.smul_mem _ hy), ?_⟩
      rw [pow_succ', ← Matrix.mulVec_mulVec, hkn, Matrix.mulVec_add, Matrix.mulVec_smul,
        ← hyz, smul_add, smul_smul, pow_succ]
      abel
  obtain ⟨k, hk, hkw⟩ := key (2 ^ m)
  have hone : ((s : Matrix (Fin 3) (Fin 3) F) ^ 2 ^ m) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_pow, hm, Matrix.SpecialLinearGroup.coe_one]
  rw [hone, Matrix.one_mulVec] at hkw
  have hc1 : c ^ 2 ^ m = 1 := by
    by_contra hne
    apply hw
    have h1 : (1 - c ^ 2 ^ m) • w = k := by
      rw [sub_smul, one_smul]
      nth_rewrite 1 [hkw]
      abel
    have h2 : (1 - c ^ 2 ^ m) ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
    have h3 : w = (1 - c ^ 2 ^ m)⁻¹ • k := by
      rw [← h1, smul_smul, inv_mul_cancel₀ h2, one_smul]
    rw [h3]
    exact K.smul_mem _ hk
  have hc : c = 1 := by
    have h0 : (c - 1) ^ 2 ^ m = 0 := by
      rw [sub_pow_char_pow, hc1, one_pow, sub_self]
    exact sub_eq_zero.mp (pow_eq_zero_iff (pow_ne_zero _ two_ne_zero) |>.mp h0)
  rw [← hyz, hc, one_smul, add_sub_cancel_right]
  exact hy

end Plane

section Coord

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
  {F : Type} [Field F] [Fintype F] {φ : ↥M →* ↥(StatedSL 3 F)} (hφ : IsSL3FullVia M T L φ)
include h hφ

theorem commutator_uloc_le_usup_of_le_normalizer (hC : CentHyp (puAmalgam h.le))
    (hb : 4 < critDist (puAmalgam h.le)) {μ σ : Vtx (puAmalgam h.le)} (hμ : IsMVtx _ μ)
    (hμσ : (puAmalgam h.le).treeGraph.Adj μ σ) {X : Subgroup (puAmalgam h.le).Universal}
    (hXs : X ≤ stab _ μ) (hX2 : IsPGroup 2 ↥X)
    (hle : X ≤ Subgroup.normalizer (Usup (puAmalgam h.le) μ σ : Set (puAmalgam h.le).Universal)) :
    ⁅Uloc h.le L μ, X⁆ ≤ Usup (puAmalgam h.le) μ σ := by
  obtain ⟨ψ, -, hψ⟩ := exists_natural_Uloc h hφ hμ
  obtain ⟨n, hn⟩ := hφ.1
  have hFn : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card, hn]
  have : CharP F 2 := FFC.charP_two_of_card_pow hFn
  have hk2 := finrank_commN_qv h hφ hC hb hμ hμσ hψ
  have hXU : X ≤ Subgroup.normalizer (Uloc h.le L μ : Set (puAmalgam h.le).Universal) :=
    hXs.trans (stab_le_normalizer_uloc h μ)
  rw [Subgroup.commutator_le]
  intro u hu x hx
  have hcU : ⁅u, x⁆ ∈ Uloc h.le L μ :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp hXU
      (Subgroup.commutator_mem_commutator hu hx)
  refine (mem_usup_iff_natVec h hφ hμ hμσ hψ ⟨_, hcU⟩).mpr ?_
  rw [natVec_commutator hψ ⟨x, hXs hx⟩ ⟨u, hu⟩ ⟨_, hcU⟩ rfl]
  have hst := (mem_normalizer_usup_iff h hφ hμ hμσ hψ ⟨x, hXs hx⟩).mp (hle hx)
  obtain ⟨m, hm⟩ := hX2 ⟨x, hx⟩
  have hxm : (⟨x, hXs hx⟩ : ↥(stab (puAmalgam h.le) μ)) ^ 2 ^ m = 1 := by
    apply Subtype.ext
    simpa using congrArg Subtype.val hm
  have hm' : toSL3 ψ ⟨x, hXs hx⟩ ^ 2 ^ m = 1 := by rw [← map_pow, hxm, map_one]
  have hmem := sub_mem_of_mem_stabilizer_of_pow hk2 hst hm' (natVec hψ ⟨u, hu⟩)
  have : natVec hψ ⟨u, hu⟩ - ((toSL3 ψ ⟨x, hXs hx⟩ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
      natVec hψ ⟨u, hu⟩ = -(((toSL3 ψ ⟨x, hXs hx⟩ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
      natVec hψ ⟨u, hu⟩ - natVec hψ ⟨u, hu⟩) := by abel
  rw [this]
  exact Submodule.neg_mem _ hmem

theorem exists_adj_not_le_normalizer_usup (hC : CentHyp (puAmalgam h.le))
    (hb : 4 < critDist (puAmalgam h.le)) {δ δ' : Vtx (puAmalgam h.le)}
    (hc : IsCritical (puAmalgam h.le) δ δ') :
    ∃ γ, (puAmalgam h.le).treeGraph.Adj δ γ ∧
      ¬ ZM (puAmalgam h.le) δ' ≤
        Subgroup.normalizer (Usup (puAmalgam h.le) δ γ : Set (puAmalgam h.le).Universal) := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hφ⟩
  have hb0 := h.critDist_pos
  have hδ := hc.1
  have hδ' := hc.isMVtx_right _ h.hyp20
  have hβ : (puAmalgam h.le).treeGraph.Adj δ (geo _ δ δ' 1) := adj_geo_one_of_isCritical _ hb0 hc
  by_contra hall
  push Not at hall
  have hZs : ZM (puAmalgam h.le) δ' ≤ stab _ δ := zm_le_stab_of_isCritical _ h.hyp20 hb0 hc
  have hZ2 : IsPGroup 2 ↥(ZM (puAmalgam h.le) δ') :=
    (S46.isPGroup_qv_of_isMVtx h hδ').to_le (zm_le_qv_self _ hδ' hb0)
  have hR : ∀ γ, (puAmalgam h.le).treeGraph.Adj δ γ →
      ⁅Uloc h.le L δ, ZM (puAmalgam h.le) δ'⁆ ≤ Usup (puAmalgam h.le) δ γ := fun γ hγ =>
    commutator_uloc_le_usup_of_le_normalizer h hφ hC hb hδ hγ hZs hZ2 (hall γ hγ)
  have hRne : ⁅Uloc h.le L δ, ZM (puAmalgam h.le) δ'⁆ ≠ ⊥ := by
    rw [← commutator_zm_eq_uloc h hfull hδ hZs]
    exact ms22_ii _ h.hyp20 hb0 hC hc
  have hNle : conjCl (stab (puAmalgam h.le) δ) ⁅Uloc h.le L δ, ZM (puAmalgam h.le) δ'⁆ ≤
      Usup (puAmalgam h.le) δ (geo _ δ δ' 1) := by
    refine iSup₂_le fun g hg => ?_
    have hgδ : g • δ = δ := (mem_stab _).mp hg
    have hadj : (puAmalgam h.le).treeGraph.Adj δ (g⁻¹ • geo _ δ δ' 1) := by
      have := (adj_smul _ g⁻¹ _ _).mpr hβ
      rwa [show g⁻¹ • δ = δ by rw [inv_smul_eq_iff, hgδ]] at this
    calc (⁅Uloc h.le L δ, ZM (puAmalgam h.le) δ'⁆).map (MulAut.conj g).toMonoidHom ≤
          (Usup (puAmalgam h.le) δ (g⁻¹ • geo _ δ δ' 1)).map (MulAut.conj g).toMonoidHom :=
          Subgroup.map_mono (hR _ hadj)
      _ = Usup (puAmalgam h.le) δ (geo _ δ δ' 1) := by
          rw [← usup_smul, hgδ, smul_inv_smul]
  have hfin : Finite ↥(Usup (puAmalgam h.le) δ (geo _ δ δ' 1)) :=
    Nat.finite_of_card_ne_zero (by
      rw [card_usup_eq_sq h hφ hC hb hδ hβ]
      exact pow_ne_zero _ Fintype.card_ne_zero)
  have hcard := Subgroup.card_le_of_le hNle
  rw [card_usup_eq_sq h hφ hC hb hδ hβ] at hcard
  have hq : 1 < Fintype.card F := by
    rw [← Nat.card_eq_fintype_card]
    exact Finite.one_lt_card
  apply not_stab_le_normalizer_of_le_uloc h hφ hδ (hNle.trans (usup_le_uloc h hφ hδ hβ))
    (ne_bot_of_le_ne_bot hRne (le_conjCl _ _)) ?_ (le_normalizer_conjCl _ _)
  calc _ ≤ Fintype.card F ^ 2 := hcard
    _ < Fintype.card F ^ 3 := Nat.pow_lt_pow_right hq (by norm_num)

end Coord

section Good

universe u v

variable {A B : Type u} {C : Type v} [Group A] [Group C] [Group B] (X : GoldAmalgam A C B)

structure IsGoodPathB (p : ℕ → Vtx X) (N : ℕ) : Prop extends S45.IsNBPath X p N where
  mvtx : IsMVtx X (p 0)
  crit : ∀ i, Even i → i + critDist X ≤ N → IsCritical X (p (i + critDist X)) (p i)
  straight : ∀ i, Even i → 2 ≤ i → i + 2 ≤ N → ∃ g ∈ stab X (p i), g • p (i + 2) = p (i - 2)
  pe : ∀ i, Even i → critDist X ≤ i → i < N →
    ¬ ZM X (p (i - critDist X)) ≤
      Subgroup.normalizer (Usup X (p i) (p (i + 1)) : Set X.Universal)

theorem isGoodPathB_geo (h : Hyp20 X) {α α' : Vtx X} (hc : IsCritical X α α')
    (hs : IsStraight X α α') : IsGoodPathB X (fun i => geo X α' α i) (critDist X) := by
  have hd : X.treeGraph.dist α α' = critDist X := hc.2.1
  have hd' : X.treeGraph.dist α' α = critDist X := by rw [tdist_comm]; exact hd
  obtain ⟨k, hk⟩ := ms21_v X h
  have hsym : ∀ m, m ≤ critDist X → geo X α α' m = geo X α' α (critDist X - m) := fun m hm => by
    rw [← geo_symm X (show m ≤ X.treeGraph.dist α α' by omega), hd]
  refine ⟨⟨fun i hi => adj_geo X (by omega), fun i hi heq => ?_⟩, ?_, ?_, ?_, ?_⟩
  · have := dist_geo_geo X (u := α') (w := α) (show i ≤ i + 2 by omega) (by omega)
    rw [heq, SimpleGraph.dist_self] at this
    omega
  · simpa using IsCritical.isMVtx_right X h hc
  · intro i _ hi
    obtain rfl : i = 0 := by omega
    simpa [geo_of_le X (show X.treeGraph.dist α' α ≤ critDist X by omega)] using hc
  · intro i hie hi2 hi
    obtain ⟨j, rfl⟩ := hie
    obtain ⟨g, hg, hgeq⟩ := hs (k - j) (by omega) (by omega)
    refine ⟨g⁻¹, ?_, ?_⟩
    · rw [hsym _ (by omega), show critDist X - 2 * (k - j) = j + j by omega] at hg
      exact inv_mem hg
    · rw [hsym _ (by omega), hsym _ (by omega),
        show critDist X - (2 * (k - j) + 2) = j + j - 2 by omega,
        show critDist X - (2 * (k - j) - 2) = j + j + 2 by omega] at hgeq
      rw [inv_smul_eq_iff, ← hgeq]
  · intro i _ hi hi'
    omega

end Good

section Extend

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
include h

theorem IsGoodPathB.extend (hb4 : 4 < critDist (puAmalgam h.le))
    (h444 : ∀ α α' : Vtx (puAmalgam h.le), IsCritical _ α α' → IsStraight _ α α' →
      Concl444 h.le α α')
    (hγ : ∀ δ δ' : Vtx (puAmalgam h.le), IsCritical _ δ δ' →
      ∃ γ, (puAmalgam h.le).treeGraph.Adj δ γ ∧
        ¬ ZM _ δ' ≤ Subgroup.normalizer (Usup _ δ γ : Set (puAmalgam h.le).Universal))
    {p : ℕ → Vtx (puAmalgam h.le)} {N : ℕ} (hp : IsGoodPathB _ p N)
    (hN : critDist (puAmalgam h.le) ≤ N) (hNe : Even N) :
    ∃ p' : ℕ → Vtx (puAmalgam h.le), (∀ i, i ≤ N → p' i = p i) ∧ IsGoodPathB _ p' (N + 2) := by
  have hp' := hp.toIsNBPath
  obtain ⟨k, hk⟩ := ms21_v _ h.hyp20
  obtain ⟨m, hm⟩ := hNe
  have hc : IsCritical (puAmalgam h.le) (p N) (p (N - critDist (puAmalgam h.le))) := by
    have := hp.crit (N - critDist (puAmalgam h.le)) ⟨m - k, by omega⟩ (by omega)
    rwa [show N - critDist (puAmalgam h.le) + critDist (puAmalgam h.le) = N by omega] at this
  have hgeo : ∀ j, j ≤ critDist (puAmalgam h.le) →
      geo (puAmalgam h.le) (p N) (p (N - critDist (puAmalgam h.le))) j = p (N - j) :=
    fun j hj => by
      rw [hp'.eq_geo_rev (i := N - critDist (puAmalgam h.le)) (j := N) (k := N - j) (by omega)
        (by omega) le_rfl, show N - (N - j) = j by omega]
  have hgeo' : geo (puAmalgam h.le) (p (N - critDist (puAmalgam h.le))) (p N) 2 =
      p (N - critDist (puAmalgam h.le) + 2) := by
    rw [hp'.eq_geo (i := N - critDist (puAmalgam h.le)) (j := N)
      (k := N - critDist (puAmalgam h.le) + 2) (by omega) (by omega) le_rfl,
      show N - critDist (puAmalgam h.le) + 2 - (N - critDist (puAmalgam h.le)) = 2 by omega]
  have hs : IsStraight (puAmalgam h.le) (p N) (p (N - critDist (puAmalgam h.le))) := by
    intro j hj hj'
    rw [tdist_comm, hp'.dist_eq' (by omega) le_rfl] at hj'
    obtain ⟨g, hg, hgeq⟩ := hp.straight (N - 2 * j) ⟨m - j, by omega⟩ (by omega) (by omega)
    refine ⟨g⁻¹, ?_, ?_⟩
    · rw [hgeo _ (by omega)]
      exact inv_mem hg
    · rw [hgeo _ (by omega), hgeo _ (by omega), inv_smul_eq_iff,
        show N - (2 * j - 2) = N - 2 * j + 2 by omega, hgeq,
        show N - (2 * j + 2) = N - 2 * j - 2 by omega]
  obtain ⟨γ, hγa, hγZ⟩ := hγ _ _ hc
  obtain ⟨t, ht, htU, htZ⟩ := h444 _ _ hc hs γ hγa hγZ
  rw [hgeo 1 (by omega)] at htU
  rw [hgeo 2 (by omega), hgeo'] at htZ
  have ht' : t • p N = p N := mem_stab (puAmalgam h.le) |>.mp ht
  have hZ' : ¬ ZM (puAmalgam h.le) (t • p (N - 2)) ≤
      Qv (puAmalgam h.le) (p (N - critDist (puAmalgam h.le) + 2)) := by
    rw [zm_smul]; exact htZ
  have hMN2 : IsMVtx (puAmalgam h.le) (t • p (N - 2)) := by
    rw [isMVtx_smul, hp'.isMVtx_iff (by omega)]
    exact ⟨fun _ => ⟨m - 1, by omega⟩, fun _ => hp.mvtx⟩
  have hadj1 : (puAmalgam h.le).treeGraph.Adj (p (N - 2)) (p (N - 1)) := by
    simpa [show N - 2 + 1 = N - 1 by omega] using hp.adj (N - 2) (by omega)
  have hadj0 : (puAmalgam h.le).treeGraph.Adj (p (N - 1)) (p N) := by
    simpa [show N - 1 + 1 = N by omega] using hp.adj (N - 1) (by omega)
  have hne1 : t • p (N - 1) ≠ p (N - 1) := by
    intro heq
    apply hZ'
    apply zm_le_qv_of_dist_lt (puAmalgam h.le) hMN2
    have h1 : (puAmalgam h.le).treeGraph.Adj (t • p (N - 2)) (p (N - 1)) := by
      rw [← heq]; exact (adj_smul (puAmalgam h.le) t _ _).mpr hadj1
    have h2 := dist_triangle (puAmalgam h.le) (t • p (N - 2)) (p (N - 1))
      (p (N - critDist (puAmalgam h.le) + 2))
    rw [dist_eq_one_of_adj (puAmalgam h.le) h1, tdist_comm (puAmalgam h.le) (p (N - 1)),
      hp'.dist_eq' (show N - critDist (puAmalgam h.le) + 2 ≤ N - 1 by omega) (by omega)] at h2
    omega
  let p' : ℕ → Vtx (puAmalgam h.le) := fun i =>
    if i = N + 1 then t • p (N - 1) else if i = N + 2 then t • p (N - 2) else p i
  have hp'le : ∀ i, i ≤ N → p' i = p i := fun i hi => by
    simp [p', show i ≠ N + 1 by omega, show i ≠ N + 2 by omega]
  have hp'1 : p' (N + 1) = t • p (N - 1) := by simp [p']
  have hp'2 : p' (N + 2) = t • p (N - 2) := by simp [p']
  have hnb : S45.IsNBPath (puAmalgam h.le) p' (N + 2) := by
    refine ⟨fun i hi => ?_, fun i hi => ?_⟩
    · rcases (show i < N ∨ i = N ∨ i = N + 1 by omega) with hi' | hi' | hi'
      · rw [hp'le i (by omega), hp'le (i + 1) (by omega)]; exact hp.adj i hi'
      · subst i
        rw [hp'le _ le_rfl, hp'1, ← ht']
        exact (adj_smul (puAmalgam h.le) t _ _).mpr hadj0.symm
      · subst i
        rw [hp'1, hp'2]
        exact (adj_smul (puAmalgam h.le) t _ _).mpr hadj1.symm
    · rcases (show i + 2 ≤ N ∨ i = N - 1 ∨ i = N by omega) with hi' | hi' | hi'
      · rw [hp'le _ hi', hp'le i (by omega)]; exact hp.nb i hi'
      · subst i
        rw [show N - 1 + 2 = N + 1 by omega, hp'1, hp'le _ (by omega)]; exact hne1
      · subst i
        rw [hp'2, hp'le _ le_rfl]
        intro heq
        rw [← ht'] at heq
        have := smul_left_cancel t heq
        exact hp.nb (N - 2) (by omega) (by rw [show N - 2 + 2 = N by omega]; exact this.symm)
  refine ⟨p', hp'le, ⟨hnb, by rw [hp'le 0 (by omega)]; exact hp.mvtx, ?_, ?_, ?_⟩⟩
  · intro i hie hi
    rcases (show i + critDist (puAmalgam h.le) ≤ N ∨
        i = N - critDist (puAmalgam h.le) + 2 by obtain ⟨l, hl⟩ := hie; omega) with hi' | hi'
    · rw [hp'le _ hi', hp'le i (by omega)]; exact hp.crit i hie hi'
    · subst i
      rw [show N - critDist (puAmalgam h.le) + 2 + critDist (puAmalgam h.le) = N + 2 by omega,
        hp'2, hp'le _ (by omega)]
      refine ⟨hMN2, ?_, hZ'⟩
      have := hnb.dist_eq' (show N - critDist (puAmalgam h.le) + 2 ≤ N + 2 by omega) le_rfl
      rw [hp'2, hp'le _ (by omega),
        show N + 2 - (N - critDist (puAmalgam h.le) + 2) = critDist (puAmalgam h.le) by omega]
        at this
      rw [tdist_comm, this]
  · intro i hie hi2 hi
    rcases (show i + 2 ≤ N ∨ i = N by obtain ⟨l, hl⟩ := hie; omega) with hi' | hi'
    · rw [hp'le _ hi', hp'le i (by omega), hp'le (i - 2) (by omega)]
      exact hp.straight i hie hi2 hi'
    · subst i
      refine ⟨t⁻¹, ?_, ?_⟩
      · rw [hp'le _ le_rfl]; exact inv_mem ht
      · rw [hp'2, hp'le _ (by omega), inv_smul_smul]
  · intro i hie hib hi
    rcases (show i < N ∨ i = N by obtain ⟨l, hl⟩ := hie; omega) with hi' | hi'
    · rw [hp'le _ (by omega), hp'le _ (by omega), hp'le _ (by omega)]
      exact hp.pe i hie hib hi'
    · subst i
      rw [hp'le _ (by omega), hp'le _ le_rfl, hp'1]
      have : Usup (puAmalgam h.le) (p N) (t • p (N - 1)) = Usup (puAmalgam h.le) (p N) γ := by
        conv_lhs => rw [← ht']
        rw [usup_smul, htU]
      rw [this]
      exact hγZ

theorem exists_isGoodPathB (hb4 : 4 < critDist (puAmalgam h.le))
    (h444 : ∀ α α' : Vtx (puAmalgam h.le), IsCritical _ α α' → IsStraight _ α α' →
      Concl444 h.le α α')
    (hγ : ∀ δ δ' : Vtx (puAmalgam h.le), IsCritical _ δ δ' →
      ∃ γ, (puAmalgam h.le).treeGraph.Adj δ γ ∧
        ¬ ZM _ δ' ≤ Subgroup.normalizer (Usup _ δ γ : Set (puAmalgam h.le).Universal))
    {α α' : Vtx (puAmalgam h.le)} (hc : IsCritical _ α α') (hs : IsStraight _ α α') :
    ∀ n : ℕ, ∃ p : ℕ → Vtx (puAmalgam h.le),
      IsGoodPathB _ p (critDist (puAmalgam h.le) + 2 * n) ∧
        ∀ i, i ≤ critDist (puAmalgam h.le) → p i = geo _ α' α i := by
  obtain ⟨k, hk⟩ := ms21_v _ h.hyp20
  intro n
  induction n with
  | zero => exact ⟨_, isGoodPathB_geo _ h.hyp20 hc hs, fun _ _ => rfl⟩
  | succ n ih =>
    obtain ⟨p, hp, hpi⟩ := ih
    obtain ⟨p', hp'i, hp'⟩ := hp.extend h hb4 h444 hγ (by omega) ⟨k + n, by omega⟩
    refine ⟨p', by rwa [show critDist (puAmalgam h.le) + 2 * (n + 1) =
      critDist (puAmalgam h.le) + 2 * n + 2 by omega], fun i hi => ?_⟩
    rw [hp'i i (by omega), hpi i hi]

end Extend

end CFSG.Quasithin.MS93.S4A
