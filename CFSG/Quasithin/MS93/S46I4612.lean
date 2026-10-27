module

public import CFSG.Quasithin.MS93.S46I4610
public import CFSG.Quasithin.MS93.S46I467Dec
public import CFSG.Quasithin.MS93.S46I466a
public import CFSG.Quasithin.MS93.S46Last
public import CFSG.Quasithin.MS93.S4A431G
public import CFSG.Quasithin.MS93.S4A433
public import CFSG.Quasithin.MS93.S4ABridge
public import CFSG.Quasithin.MS93.S4AL1

public section

namespace CFSG.Quasithin.MS93.S46

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open CFSG.Quasithin.MS93.S4A
open scoped commutatorElement Matrix

@[expose] def KC4612 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (F : Type) [Field F] [Fintype F]
    (φ : ↥M →* ↥(StatedSL 3 F)) (c : Hyp46 M T L φ) (α α' : Vtx (puAmalgam c.pu.le)),
    IsCritical _ α α' → ∀ g ∈ stab (puAmalgam c.pu.le) α,
      ZM (puAmalgam c.pu.le) (g • geo _ α α' 2) ≤ Qv _ (geo _ α α' 2)

@[expose] def Idx4612 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (F : Type) [Field F] [Fintype F]
    (φ : ↥M →* ↥(StatedSL 3 F)) (c : Hyp46 M T L φ) (α : Vtx (puAmalgam c.pu.le)),
    IsMVtx _ α → (Bloc c.pu.le L α).relIndex (Vv (puAmalgam c.pu.le) α) ≤ Fintype.card F ^ 6

@[expose] def KC4612Cfg {G : Type} [Group G] [Finite G] (M T L : Subgroup G) {F : Type} [Field F]
    [Fintype F] (φ : ↥M →* ↥(StatedSL 3 F)) : Prop :=
  ∀ (c : Hyp46 M T L φ) (α α' : Vtx (puAmalgam c.pu.le)),
    IsCritical _ α α' → ∀ g ∈ stab (puAmalgam c.pu.le) α,
      ZM (puAmalgam c.pu.le) (g • geo _ α α' 2) ≤ Qv _ (geo _ α α' 2)

@[expose] def Idx4612Cfg {G : Type} [Group G] [Finite G] (M T L : Subgroup G) {F : Type}
    [Field F] [Fintype F] (φ : ↥M →* ↥(StatedSL 3 F)) : Prop :=
  ∀ (c : Hyp46 M T L φ) (α : Vtx (puAmalgam c.pu.le)),
    IsMVtx _ α → (Bloc c.pu.le L α).relIndex (Vv (puAmalgam c.pu.le) α) ≤ Fintype.card F ^ 6

section Count

variable {𝔾 : Type} [Group 𝔾] {F : Type} [Field F] [Fintype F]

theorem le_of_isSum_dual {K W Z Y T : Subgroup 𝔾} {ψ : ↥K →* ↥(StatedSL 3 F)}
    (hd : IsSumOfNaturalModulesVia K W Z ψ true 1)
    (hT : ∀ c : F, ∃ t : ↥K, (t : 𝔾) ∈ T ∧ toSL3 ψ t = rootElt 1 0 c)
    (hWT : ∀ w ∈ W, ∀ t ∈ T, ⁅w, t⁆ ∈ Y) [Finite ↥Y]
    (hYZ : Z.relIndex Y ≤ Fintype.card F) : Y ≤ W := by
  classical
  set N := NatSec.ofIsSum hd
  obtain ⟨w, hw, hwc⟩ := N.exists_coord_eq ![0, 1, 0]
  choose t ht htc using hT
  have hconj : ∀ c, ((t c : ↥K) : 𝔾) * w⁻¹ * ((t c : ↥K) : 𝔾)⁻¹ ∈ W := fun c =>
    N.conj_mem (t c) (W.inv_mem hw)
  have e : ∀ c, ⁅w, ((t c : ↥K) : 𝔾)⁆ = w * (((t c : ↥K) : 𝔾) * w⁻¹ * ((t c : ↥K) : 𝔾)⁻¹) :=
    fun c => by simp only [commutatorElement_def]; group
  have hmemW : ∀ c, ⁅w, ((t c : ↥K) : 𝔾)⁆ ∈ W := fun c => by
    rw [e c]
    exact W.mul_mem hw (hconj c)
  have hcoord : ∀ c, N.coord ⁅w, ((t c : ↥K) : 𝔾)⁆ = Pi.single 0 c := fun c => by
    rw [e c, N.coord_mul hw (hconj c), N.coord_conj (t c) (W.inv_mem hw), N.coord_inv hw,
      natAct_true, htc, hwc, Matrix.mulVec_neg, dualMat_rootElt_mulVec (by decide)]
    funext i
    fin_cases i <;> simp [Matrix.vecHead, Matrix.vecTail]
  let f : F → ↥Y ⧸ Z.subgroupOf Y := fun c =>
    QuotientGroup.mk ⟨⁅w, ((t c : ↥K) : 𝔾)⁆, hWT w hw _ (ht c)⟩
  have hf : Function.Injective f := by
    intro c c' hcc'
    have h1 := QuotientGroup.eq.mp hcc'
    rw [Subgroup.mem_subgroupOf] at h1
    have h2 : (⁅w, ((t c : ↥K) : 𝔾)⁆)⁻¹ * ⁅w, ((t c' : ↥K) : 𝔾)⁆ ∈ Z := by simpa using h1
    have h0 := (N.coord_eq_zero_iff (W.mul_mem (W.inv_mem (hmemW c)) (hmemW c'))).mpr h2
    rw [N.coord_mul (W.inv_mem (hmemW c)) (hmemW c'), N.coord_inv (hmemW c), hcoord,
      hcoord] at h0
    have h3 := congrFun h0 0
    simp only [Pi.add_apply, Pi.neg_apply, Pi.single_eq_same, Pi.zero_apply] at h3
    exact (neg_add_eq_zero.mp h3)
  have hcard : Nat.card (↥Y ⧸ Z.subgroupOf Y) ≤ Nat.card F := by
    rw [Nat.card_eq_fintype_card (α := F)]
    exact hYZ
  have hbij := hf.bijective_of_nat_card_le hcard
  intro y hy
  obtain ⟨c, hc⟩ := hbij.2 (QuotientGroup.mk ⟨y, hy⟩)
  have h1 := QuotientGroup.eq.mp hc
  rw [Subgroup.mem_subgroupOf] at h1
  have h2 : (⁅w, ((t c : ↥K) : 𝔾)⁆)⁻¹ * y ∈ Z := by simpa using h1
  have e2 : y = ⁅w, ((t c : ↥K) : 𝔾)⁆ * ((⁅w, ((t c : ↥K) : 𝔾)⁆)⁻¹ * y) := by group
  rw [e2]
  exact W.mul_mem (hmemW c) (hd.2.1 h2)

end Count

section Orbit

variable {G : Type} [Group G] {M T : Subgroup G} (hTM : T ≤ M)

private theorem le_normalizer_of_map_le {𝔾 : Type} [Group 𝔾] {K N : Subgroup 𝔾}
    (h : ∀ k ∈ K, N.map (MulAut.conj k).toMonoidHom ≤ N) :
    K ≤ Subgroup.normalizer (N : Set 𝔾) := by
  intro k hk
  rw [Subgroup.mem_normalizer_iff]
  intro n
  refine ⟨fun hn => h k hk ⟨n, hn, rfl⟩, fun hn => ?_⟩
  have := h k⁻¹ (K.inv_mem hk) ⟨k * n * k⁻¹, hn, rfl⟩
  simpa [mul_assoc] using this

private noncomputable def nOrb (α γ : Vtx (puAmalgam hTM)) : Subgroup (puAmalgam hTM).Universal :=
  (⨆ g ∈ stab (puAmalgam hTM) α, ZM (puAmalgam hTM) (g • γ)) ⊔ ZM _ α

private theorem nOrb_normal (α γ : Vtx (puAmalgam hTM)) :
    stab (puAmalgam hTM) α ≤ Subgroup.normalizer (nOrb hTM α γ : Set _) := by
  refine le_normalizer_of_map_le fun k hk => ?_
  rw [Subgroup.map_le_iff_le_comap]
  refine sup_le (iSup₂_le fun g hg => ?_) ?_
  · rw [← Subgroup.map_le_iff_le_comap, ← zm_smul, smul_smul]
    exact le_sup_of_le_left (le_iSup₂_of_le (f := fun g (_ : g ∈ stab (puAmalgam hTM) α) =>
      ZM (puAmalgam hTM) (g • γ)) (k * g) (Subgroup.mul_mem _ hk hg) le_rfl)
  · rw [← Subgroup.map_le_iff_le_comap, ← zm_smul, (mem_stab _).mp hk]
    exact le_sup_right

private theorem zm_le_nOrb (α γ : Vtx (puAmalgam hTM)) :
    ZM (puAmalgam hTM) γ ≤ nOrb hTM α γ := by
  have : ZM (puAmalgam hTM) ((1 : (puAmalgam hTM).Universal) • γ) ≤ nOrb hTM α γ :=
    le_sup_of_le_left (le_iSup₂_of_le (f := fun g (_ : g ∈ stab (puAmalgam hTM) α) =>
      ZM (puAmalgam hTM) (g • γ)) 1 (Subgroup.one_mem _) le_rfl)
  rwa [one_smul] at this

private theorem nOrb_le {α γ : Vtx (puAmalgam hTM)} {N : Subgroup (puAmalgam hTM).Universal}
    (hN : ∀ g ∈ stab (puAmalgam hTM) α, ZM (puAmalgam hTM) (g • γ) ≤ N)
    (hα : ZM (puAmalgam hTM) α ≤ N) : nOrb hTM α γ ≤ N :=
  sup_le (iSup₂_le hN) hα

private theorem nOrb_le_of_normal {α γ : Vtx (puAmalgam hTM)}
    {N : Subgroup (puAmalgam hTM).Universal}
    (hNn : stab (puAmalgam hTM) α ≤ Subgroup.normalizer (N : Set (puAmalgam hTM).Universal))
    (hγ : ZM (puAmalgam hTM) γ ≤ N) (hα : ZM (puAmalgam hTM) α ≤ N) : nOrb hTM α γ ≤ N := by
  refine nOrb_le hTM (fun g hg => ?_) hα
  rw [zm_smul]
  rintro _ ⟨y, hy, rfl⟩
  exact (Subgroup.mem_normalizer_iff.mp (hNn hg) y).mp (hγ hy)

private theorem nOrb_le_vv {α γ : Vtx (puAmalgam hTM)} (hγ : IsMVtx _ γ)
    (hd : (puAmalgam hTM).treeGraph.dist α γ ≤ 2) (hα : IsMVtx _ α) :
    nOrb hTM α γ ≤ Vv (puAmalgam hTM) α := by
  have key : ∀ δ : Vtx (puAmalgam hTM), IsMVtx _ δ → (puAmalgam hTM).treeGraph.dist α δ ≤ 2 →
      ZM (puAmalgam hTM) δ ≤ Vv _ α := fun δ hδ hdδ =>
    le_iSup₂_of_le (f := fun x (_ : x ∈ {x : Vtx (puAmalgam hTM) |
      (puAmalgam hTM).treeGraph.dist α x ≤ 2}) => Zv _ x) δ hdδ (zv_of_isMVtx _ hδ).ge
  refine nOrb_le hTM (fun g hg => key _ ((isMVtx_smul _ g γ).mpr hγ) ?_) (key α hα (by simp))
  rw [← (mem_stab _).mp hg, dist_smul]
  exact hd

end Orbit

section Normal

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} {F : Type} [Field F] [Fintype F]
  {φ : ↥M →* ↥(StatedSL 3 F)}

theorem zm_le_of_normal_cfg (h14 : MS14AS) (hSQ : SQTKQuot) (h465 : I465) (h467 : I467)
    (h469 : I469Cfg M T L φ) (c : Hyp46 M T L φ) {α β γ : Vtx (puAmalgam c.pu.le)}
    (hα : IsMVtx _ α)
    (hαβ : (puAmalgam c.pu.le).treeGraph.Adj α β) (hβγ : (puAmalgam c.pu.le).treeGraph.Adj β γ)
    (hZγ : ¬ ZM (puAmalgam c.pu.le) γ ≤ Bloc c.pu.le L α)
    {ψ : ↥(stab (puAmalgam c.pu.le) α) →* ↥(StatedSL 3 F)}
    (hLH : LastHyp (stab _ α) (Qv _ α) (Ltil c.pu.le L α) (Uloc c.pu.le L α) (Zloc c.pu.le L α)
      (ZM _ α) (Vv _ α) ψ)
    (hT : natImage ψ (Qv (puAmalgam c.pu.le) β) = rootGroup 1 0 ⊔ rootGroup 2 0)
    {N : Subgroup (puAmalgam c.pu.le).Universal}
    (hNn : stab (puAmalgam c.pu.le) α ≤
      Subgroup.normalizer (N : Set (puAmalgam c.pu.le).Universal))
    (hZN : ZM (puAmalgam c.pu.le) α ≤ N) (hN : N ≤ Vv _ α ⊓ Qv _ γ)
    (hNB : ¬ N ≤ Bloc c.pu.le L α) : ZM (puAmalgam c.pu.le) γ ≤ N := by
  obtain ⟨W, hWN, hW⟩ := exists_lastLayer_cfg h14 hSQ h465 h467 h469 c hα hαβ hβγ hZγ hLH hT hNn
    hZN hN hNB
  obtain ⟨h, hmin, hb4, hφ⟩ := c
  have h20 := h.hyp20
  have hb : 2 < critDist (puAmalgam h.le) := by omega
  have hKα := finite_stab h hα
  have hγ : IsMVtx (puAmalgam h.le) γ := by
    have h1 := isMVtx_iff_of_adj _ hαβ
    have h2 := isMVtx_iff_of_adj _ hβγ
    tauto
  have hαγ : α ≠ γ := by
    rintro rfl
    exact hZγ (zm_le_bloc h hb hα)
  have hdαγ : (puAmalgam h.le).treeGraph.dist α γ = 2 := dist_eq_two_of_adj_adj _ hαβ hβγ hαγ
  have hdγα : (puAmalgam h.le).treeGraph.dist γ α = 2 := by rw [tdist_comm]; exact hdαγ
  have hNV : N ≤ Vv _ α := hN.trans inf_le_left
  have hNQγ : N ≤ Qv _ γ := hN.trans inf_le_right
  obtain ⟨-, -, -, h9⟩ := h469 ⟨h, hmin, hb4, hφ⟩ α β hα hαβ
  obtain ⟨-, -, hZαγ⟩ := h9 γ hβγ hZγ
  obtain ⟨-, -, -, h9'⟩ := h469 ⟨h, hmin, hb4, hφ⟩ γ β hγ hβγ.symm
  obtain ⟨hTγ, -, -⟩ := h9' α hαβ.symm hZαγ
  have hβK : Qv (puAmalgam h.le) β ≤ stab _ α := qv_le_stab_of_adj _ hαβ.symm
  have hβKγ : Qv (puAmalgam h.le) β ≤ stab _ γ := qv_le_stab_of_adj _ hβγ
  have hQαβ : Qv (puAmalgam h.le) α ≤ Qv _ β := qv_le_qv _ h20 hα hαβ
  have hQγβ : Qv (puAmalgam h.le) γ ≤ Qv _ β := qv_le_qv _ h20 hγ hβγ.symm
  have hVγβ : Vv (puAmalgam h.le) γ ≤ Qv _ β := (vv_le_qv h hb hγ).trans hQγβ
  have hZγα : ZM (puAmalgam h.le) γ ≤ Qv _ α := zm_le_qv_of_dist_le_three hb4 hγ (by omega)
  have hZγK : ZM (puAmalgam h.le) γ ≤ stab _ α := hZγα.trans (qv_le_stab _ α)
  have hZαK : ZM (puAmalgam h.le) α ≤ stab _ α := hLH.zK
  have hZn := stab_le_normalizer_zm (puAmalgam h.le) α
  have hZnγ := stab_le_normalizer_zm (puAmalgam h.le) γ
  set Y := ZM (puAmalgam h.le) γ ⊔ ZM _ α with hY
  have hYK : Y ≤ stab _ α := sup_le hZγK hZαK
  have : Finite ↥Y := Finite.of_injective _ (Subgroup.inclusion_injective hYK)
  have hYZ : (ZM (puAmalgam h.le) α).relIndex Y ≤ Fintype.card F := by
    rw [hY]
    have := Subgroup.normal_subgroupOf_of_le_normalizer (hZγK.trans hZn)
    have := Subgroup.normal_subgroupOf_sup_of_le_normalizer (hZγK.trans hZn)
    rw [show (ZM (puAmalgam h.le) α).relIndex (ZM _ γ ⊔ ZM _ α) =
        (ZM (puAmalgam h.le) α).relIndex (ZM _ γ) from Nat.card_congr
      (QuotientGroup.quotientInfEquivProdNormalizerQuotient _ _ (hZγK.trans hZn)).toEquiv.symm]
    have hq := (h465 G M T L F φ ⟨h, hmin, hb4, hφ⟩ γ β hγ hβγ.symm).2.1
    rw [← hq]
    exact Subgroup.relIndex_le_of_le_left (zh_le_zm _ hαβ)
      (by rw [hq]; exact Fintype.card_ne_zero)
  have hNTY : ⁅N, Qv (puAmalgam h.le) β⁆ ≤ Y := by
    rw [Subgroup.commutator_comm, ← hTγ]
    have hYn : Qv (puAmalgam h.le) β ≤ Subgroup.normalizer (Y : Set _) :=
      CFSG.LieType.Steinberg.le_normalizer_sup (hβKγ.trans hZnγ) (hβK.trans hZn)
    refine commutator_sup_le_of_le_normalizer hYn hVγβ hQαβ ?_ ?_
    · have h1 := (h465 G M T L F φ ⟨h, hmin, hb4, hφ⟩ γ β hγ hβγ.symm).2.2
      exact ((Subgroup.commutator_mono le_rfl hNQγ).trans h1).trans le_sup_left
    · rw [Subgroup.commutator_comm]
      exact ((Subgroup.commutator_mono hNV le_rfl).trans hLH.vqc).trans le_sup_right
  have hTc : ∀ c : F, ∃ t : ↥(stab (puAmalgam h.le) α),
      (t : (puAmalgam h.le).Universal) ∈ Qv _ β ∧ toSL3 ψ t = rootElt 1 0 c := by
    intro c
    have hmem : rootElt 1 0 c ∈ natImage ψ (Qv (puAmalgam h.le) β) := by
      rw [hT]
      exact Subgroup.mem_sup_left ⟨c, rfl⟩
    exact mem_natImage.mp hmem
  have hYW := le_of_isSum_dual hW.dual hTc
    (fun w hw t ht => hNTY (Subgroup.commutator_mem_commutator (hWN hw) ht)) hYZ
  exact (le_sup_left.trans hYW).trans hWN

theorem zm_geo_two_not_le_bloc (h43 : S43) (h467 : I467) (c : Hyp46 M T L φ)
    {α α' : Vtx (puAmalgam c.pu.le)} (hc : IsCritical _ α α') :
    ¬ ZM (puAmalgam c.pu.le) (geo _ α α' 2) ≤ Bloc c.pu.le L α := by
  obtain ⟨h, hmin, hb4, hφ⟩ := c
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hφ⟩
  have h20 := h.hyp20
  have hb : 2 < critDist (puAmalgam h.le) := by omega
  have hb0 : 0 < critDist (puAmalgam h.le) := by omega
  have hα := hc.1
  have hγ : IsMVtx (puAmalgam h.le) (geo _ α α' 2) := isMVtx_geo_two' hb4 hc
  have hαβ : (puAmalgam h.le).treeGraph.Adj α (geo _ α α' 1) := adj_geo_one_of_isCritical _ hb0 hc
  have hβγ : (puAmalgam h.le).treeGraph.Adj (geo _ α α' 1) (geo _ α α' 2) :=
    adj_geo_crit hb4 hc (i := 1) (by omega)
  have hV := h43 G M T L h hmin hb hfull α α' hc
  rw [geo_rev_two hb4 hc] at hV
  intro hle
  apply hV
  rw [h467 G M T L F φ ⟨h, hmin, hb4, hφ⟩ α hα] at hle
  have hVs : Vv (puAmalgam h.le) α ≤ stab _ (geo _ α α' 2) :=
    ((vv_le_qv h hb hα).trans (qv_le_qv _ h20 hα hαβ)).trans (qv_le_stab_of_adj _ hβγ)
  refine le_trans (le_inf hVs ?_) (stab_inf_centralizer_uloc_le_qv h hφ hγ)
  intro v hv
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  have hu' := hle (uloc_le_zm h hfull hγ hu)
  exact (Subgroup.mem_centralizer_iff.mp hu'.2 v hv).symm

theorem exists_adj_not_commute (h467 : I467) (c : Hyp46 M T L φ) {α β : Vtx (puAmalgam c.pu.le)}
    (hα : IsMVtx _ α) (hαβ : (puAmalgam c.pu.le).treeGraph.Adj α β)
    {N : Subgroup (puAmalgam c.pu.le).Universal}
    (hNn : stab (puAmalgam c.pu.le) α ≤
      Subgroup.normalizer (N : Set (puAmalgam c.pu.le).Universal))
    (hNV : N ≤ Vv _ α) (hNB : ¬ N ≤ Bloc c.pu.le L α) :
    ∃ ρ, (puAmalgam c.pu.le).treeGraph.Adj β ρ ∧ ¬ ZM (puAmalgam c.pu.le) ρ ≤ Bloc c.pu.le L α ∧
      ∃ z ∈ ZM (puAmalgam c.pu.le) ρ, ∃ n ∈ N, z * n ≠ n * z := by
  obtain ⟨h, hmin, hb4, hφ⟩ := c
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hφ⟩
  have h20 := h.hyp20
  have hb : 2 < critDist (puAmalgam h.le) := by omega
  have hB := h467 G M T L F φ ⟨h, hmin, hb4, hφ⟩ α hα
  obtain ⟨n, hnN, hnc⟩ : ∃ n ∈ N, n ∉ Subgroup.centralizer (Vv (puAmalgam h.le) α : Set _) := by
    by_contra hcon
    push Not at hcon
    exact hNB (fun x hx => hB ▸ ⟨hNV hx, hcon x hx⟩)
  have hnQ : n ∈ Qv (puAmalgam h.le) α := vv_le_qv h hb hα (hNV hnN)
  obtain ⟨x, hx, z, hz, hzn⟩ : ∃ x, (puAmalgam h.le).treeGraph.dist α x ≤ 2 ∧
      ∃ z ∈ Zv (puAmalgam h.le) x, z * n ≠ n * z := by
    by_contra hcon
    push Not at hcon
    apply hnc
    have hle : Vv (puAmalgam h.le) α ≤ Subgroup.centralizer ({n} : Set _) := by
      refine iSup₂_le fun x hx => ?_
      intro z hz
      rw [Subgroup.mem_centralizer_iff]
      intro m hm
      rw [Set.mem_singleton_iff] at hm
      subst hm
      exact (hcon x hx z hz).symm
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact (Subgroup.mem_centralizer_iff.mp (hle hv) n (Set.mem_singleton n)).symm
  have hcomm : ∀ y ∈ ZM (puAmalgam h.le) α, y * n = n * y := fun y hy =>
    (Subgroup.mem_centralizer_iff.mp (zm_le_centralizer_qv _ h20 hα hy) n hnQ).symm
  rcases (by omega : (puAmalgam h.le).treeGraph.dist α x = 0 ∨
      (puAmalgam h.le).treeGraph.dist α x = 1 ∨ (puAmalgam h.le).treeGraph.dist α x = 2) with
    hd | hd | hd
  · exfalso
    rw [dist_eq_zero_iff] at hd
    subst hd
    rw [zv_of_isMVtx _ hα] at hz
    exact hzn (hcomm z hz)
  · exfalso
    have hadj : (puAmalgam h.le).treeGraph.Adj α x := SimpleGraph.dist_eq_one_iff_adj.mp hd
    have hxH : ¬ IsMVtx (puAmalgam h.le) x := (isMVtx_iff_of_adj _ hadj).mp hα
    rw [zv_of_not_isMVtx _ hxH] at hz
    exact hzn (hcomm z (zh_le_zm _ hadj hz))
  · have hxM : IsMVtx (puAmalgam h.le) x := by
      have := (even_dist_iff _ α x).mp (by rw [hd]; exact ⟨1, rfl⟩)
      exact this.mp hα
    rw [zv_of_isMVtx _ hxM] at hz
    have hxB : ¬ ZM (puAmalgam h.le) x ≤ Bloc h.le L α := by
      intro hle
      have hzc := (hB ▸ hle hz : z ∈ centerOf (Vv (puAmalgam h.le) α)).2
      exact hzn (Subgroup.mem_centralizer_iff.mp hzc n (hNV hnN)).symm
    set β' := geo (puAmalgam h.le) α x 1 with hβ'
    have hαβ' : (puAmalgam h.le).treeGraph.Adj α β' := adj_geo_one _ (by omega)
    have hβ'x : (puAmalgam h.le).treeGraph.Adj β' x := by
      have := adj_geo (puAmalgam h.le) (u := α) (w := x) (i := 1) (by omega)
      rwa [geo_of_le (puAmalgam h.le) (by omega : (puAmalgam h.le).treeGraph.dist α x ≤ 1 + 1)]
        at this
    obtain ⟨k, hk, hkβ⟩ := I467.exists_mem_stab_smul_eq hα hαβ' hαβ
    have hkα : k • α = α := (mem_stab _).mp hk
    refine ⟨k • x, ?_, ?_, k * z * k⁻¹, ?_, k * n * k⁻¹, ?_, ?_⟩
    · rw [← hkβ]
      exact (adj_smul _ k β' x).mpr hβ'x
    · intro hle
      apply hxB
      rw [zm_smul] at hle
      have h1 : Bloc h.le L α = (Bloc h.le L α).map (MulAut.conj k).toMonoidHom := by
        rw [← bloc_smul h k α, hkα]
      rw [h1] at hle
      exact (Subgroup.map_le_map_iff_of_injective (MulAut.conj k).injective).mp hle
    · rw [zm_smul]
      exact ⟨z, hz, rfl⟩
    · exact (Subgroup.mem_normalizer_iff.mp (hNn hk) n).mp hnN
    · intro heq
      apply hzn
      have e1 : k * z * k⁻¹ * (k * n * k⁻¹) = k * (z * n) * k⁻¹ := by group
      have e2 : k * n * k⁻¹ * (k * z * k⁻¹) = k * (n * z) * k⁻¹ := by group
      rw [e1, e2] at heq
      exact mul_left_cancel (mul_right_cancel heq)

theorem exists_isCritical_geo_two (h467 : I467) (c : Hyp46 M T L φ)
    {α ρ : Vtx (puAmalgam c.pu.le)} (hα : IsMVtx _ α) (hρ : IsMVtx _ ρ)
    (hd : (puAmalgam c.pu.le).treeGraph.dist α ρ = 2)
    (hZ : ¬ ZM (puAmalgam c.pu.le) α ≤ Bloc c.pu.le L ρ) :
    ∃ α', IsCritical (puAmalgam c.pu.le) α α' ∧ geo (puAmalgam c.pu.le) α α' 2 = ρ := by
  obtain ⟨h, hmin, hb4, hφ⟩ := c
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hφ⟩
  have h20 := h.hyp20
  have hC := centHyp_of_gen23 h hfull
  have hdρα : (puAmalgam h.le).treeGraph.dist ρ α = 2 := by rw [tdist_comm]; exact hd
  by_contra hno
  have hgen : critGen (puAmalgam h.le) α ρ = ⊥ :=
    le_bot_iff.mp (iSup₂_le fun δ hδ => (hno ⟨δ, hδ⟩).elim)
  have hVQ : Vv (puAmalgam h.le) ρ ≤ Qv _ α := by
    have := vv_le_critGen_sup h20 hC hb4 hρ hd
    rwa [hgen, bot_sup_eq] at this
  apply hZ
  rw [h467 G M T L F φ ⟨h, hmin, hb4, hφ⟩ ρ hρ]
  have hZV : ZM (puAmalgam h.le) α ≤ Vv _ ρ :=
    le_iSup₂_of_le (f := fun x (_ : x ∈ {x : Vtx (puAmalgam h.le) |
      (puAmalgam h.le).treeGraph.dist ρ x ≤ 2}) => Zv _ x) α (by simp [hdρα])
      (zv_of_isMVtx _ hα).ge
  exact le_inf hZV ((zm_le_centralizer_qv _ h20 hα).trans (Subgroup.centralizer_le hVQ))

private theorem le_normalizer_inf {𝔾 : Type} [Group 𝔾] {K N₁ N₂ : Subgroup 𝔾}
    (h₁ : K ≤ Subgroup.normalizer (N₁ : Set 𝔾)) (h₂ : K ≤ Subgroup.normalizer (N₂ : Set 𝔾)) :
    K ≤ Subgroup.normalizer ((N₁ ⊓ N₂ : Subgroup 𝔾) : Set 𝔾) := by
  intro k hk
  rw [Subgroup.mem_normalizer_iff]
  intro n
  simp only [Subgroup.mem_inf]
  rw [Subgroup.mem_normalizer_iff.mp (h₁ hk) n, Subgroup.mem_normalizer_iff.mp (h₂ hk) n]

theorem i4612Cfg_of (hKC : KC4612Cfg M T L φ) (hIdx : Idx4612Cfg M T L φ) (h14 : MS14AS)
    (hSQ : SQTKQuot) (h43 : S43) (h463 : I463) (h464 : I464) (h465 : I465) (h466a : I466a)
    (h466b : I466b) (h467 : I467) (h469 : I469Cfg M T L φ) : I4612Cfg M T L φ := by
  intro c α hα
  have h20 := c.pu.hyp20
  have hb4 := c.b4
  have hb : 2 < critDist (puAmalgam c.pu.le) := by omega
  have hb0 : 0 < critDist (puAmalgam c.pu.le) := by omega
  obtain ⟨α', hc⟩ := exists_isCritical_of_isMVtx _ h20 hα
  set β := geo (puAmalgam c.pu.le) α α' 1 with hβ
  set γ := geo (puAmalgam c.pu.le) α α' 2 with hγdef
  have hαβ : (puAmalgam c.pu.le).treeGraph.Adj α β := adj_geo_one_of_isCritical _ hb0 hc
  have hβγ : (puAmalgam c.pu.le).treeGraph.Adj β γ := adj_geo_crit hb4 hc (i := 1) (by omega)
  have hγ : IsMVtx (puAmalgam c.pu.le) γ := isMVtx_geo_two' hb4 hc
  have hZγ : ¬ ZM (puAmalgam c.pu.le) γ ≤ Bloc c.pu.le L α := zm_geo_two_not_le_bloc h43 h467 c hc
  have hαγ : α ≠ γ := by
    rintro hαγ
    exact hZγ (hαγ ▸ zm_le_bloc c.pu hb hα)
  have hdαγ : (puAmalgam c.pu.le).treeGraph.dist α γ = 2 := dist_eq_two_of_adj_adj _ hαβ hβγ hαγ
  have hNγn := nOrb_normal c.pu.le α γ
  have hNγV : nOrb c.pu.le α γ ≤ Vv _ α := nOrb_le_vv c.pu.le hγ hdαγ.le hα
  have hNγQ : nOrb c.pu.le α γ ≤ Qv _ γ :=
    nOrb_le c.pu.le (hKC c α α' hc) (zm_le_qv_of_dist_le_three hb4 hα (by omega))
  have hNγB : ¬ nOrb c.pu.le α γ ≤ Bloc c.pu.le L α := fun hle =>
    hZγ ((zm_le_nOrb c.pu.le α γ).trans hle)
  obtain ⟨ρ, hβρ, hZρ, z, hz, n, hn, hzn⟩ :=
    exists_adj_not_commute h467 c hα hαβ hNγn hNγV hNγB
  have hρ : IsMVtx (puAmalgam c.pu.le) ρ := by
    have h1 := isMVtx_iff_of_adj _ hαβ
    have h2 := isMVtx_iff_of_adj _ hβρ
    tauto
  have hαρ : α ≠ ρ := by
    rintro hαρ
    exact hZρ (hαρ ▸ zm_le_bloc c.pu hb hα)
  have hdαρ : (puAmalgam c.pu.le).treeGraph.dist α ρ = 2 := dist_eq_two_of_adj_adj _ hαβ hβρ hαρ
  obtain ⟨hQL, -, -, h9⟩ := h469 c α β hα hαβ
  have hZαρ : ¬ ZM (puAmalgam c.pu.le) α ≤ Bloc c.pu.le L ρ := (h9 ρ hβρ hZρ).2.2
  obtain ⟨α'', hc', hρ''⟩ := exists_isCritical_geo_two h467 c hα hρ hdαρ hZαρ
  have hNρn := nOrb_normal c.pu.le α ρ
  have hNρV : nOrb c.pu.le α ρ ≤ Vv _ α := nOrb_le_vv c.pu.le hρ hdαρ.le hα
  have hNρQ : nOrb c.pu.le α ρ ≤ Qv _ ρ := by
    have hK := hKC c α α'' hc'
    rw [hρ''] at hK
    exact nOrb_le c.pu.le hK (zm_le_qv_of_dist_le_three hb4 hα (by omega))
  have hNρB : ¬ nOrb c.pu.le α ρ ≤ Bloc c.pu.le L α := fun hle =>
    hZρ ((zm_le_nOrb c.pu.le α ρ).trans hle)
  refine ⟨β, γ, ρ, hαβ, hβγ, hβρ, hZγ, hZρ, nOrb c.pu.le α γ, nOrb c.pu.le α ρ, hNγn,
    le_sup_right, le_inf hNγV hNγQ, hNγB, hNρn, le_sup_right, le_inf hNρV hNρQ, hNρB, ?_,
    hIdx c α hα⟩
  by_contra hcon
  obtain ⟨ψ, hψs, hψU, hT⟩ := exists_coord_qv h464 h465 h466a c hα hαβ
  have hLH := lastHyp_of h463 h465 h466b h467 c hα hψs hψU hQL
  have hZN := zm_le_of_normal_cfg h14 hSQ h465 h467 h469 c hα hαβ hβγ hZγ hLH hT
    (le_normalizer_inf hNγn hNρn) (le_inf le_sup_right le_sup_right)
    ((inf_le_left).trans (le_inf hNγV hNγQ)) hcon
  have hle : nOrb c.pu.le α γ ≤ nOrb c.pu.le α ρ :=
    nOrb_le_of_normal c.pu.le hNρn (hZN.trans inf_le_right) le_sup_right
  exact hzn (Subgroup.mem_centralizer_iff.mp (zm_le_centralizer_qv _ h20 hρ hz) n
    (hNρQ (hle hn))).symm

theorem i4612_of (hKC : KC4612) (hIdx : Idx4612) (h14 : MS14AS) (hSQ : SQTKQuot) (h43 : S43)
    (h463 : I463) (h464 : I464) (h465 : I465) (h466a : I466a) (h466b : I466b) (h467 : I467)
    (h469 : I469) : I4612 :=
  fun G _ _ M T L F _ _ φ => i4612Cfg_of (hKC G M T L F φ) (hIdx G M T L F φ) h14 hSQ h43 h463
    h464 h465 h466a h466b h467 (h469 G M T L F φ)

end Normal

end CFSG.Quasithin.MS93.S46
