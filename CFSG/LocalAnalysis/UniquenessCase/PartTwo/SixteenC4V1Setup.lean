module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC4V1Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC4V1Model
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen24C4
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC4Out1

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.ClassicalGroups.Unitary
open CFSG.LieType.Universal.Unitary (SUid)
open scoped Matrix

variable {G : Type} [Group G] [Finite G]
variable {D : Data G} {V L : Subgroup G} {hV : IsElemAbelian 2 V}

private theorem s16c4v1_set_vec_of_mem (S : s16c4v1_Sit D V L hV) {v : G} (hv : v ∈ V) :
    s16c4v1_vec S v =
      S.F.vec (mkTil (v1Sub D.M ⊥ V hV L) V hV (IntMod.mk hV ⟨v, hv⟩)) := by
  unfold s16c4v1_vec
  rw [dif_pos hv]

private theorem s16c4v1_set_rho_pi (S : s16c4v1_Sit D V L hV) (γ : ↥(SUid S.F.σ 4))
    (x : Fin 4 → S.F.K) :
    S.F.rho (S.F.π γ : MulAut (Vtil (v1Sub D.M ⊥ V hV L) V hV)) x = γ • x := by
  calc S.F.rho (S.F.π γ) x
      = S.F.rho (S.F.π γ) (S.F.vec (S.F.ofVec x)) := by rw [S.F.vec_ofVec]
    _ = S.F.vec ((S.F.π γ : MulAut _) (S.F.ofVec x)) := S.F.rho_vec _ _
    _ = γ • S.F.vec (S.F.ofVec x) := S.F.vec_action γ (S.F.ofVec x)
    _ = γ • x := by rw [S.F.vec_ofVec]

private theorem s16c4v1_set_mkTil_bot_injective (V : Subgroup G) (hV : IsElemAbelian 2 V) :
    Function.Injective (mkTil (⊥ : Subgroup G) V hV) := by
  intro x y hxy
  have h : x.val * y.val⁻¹ = 1 := by
    have h' := (mkTil_eq_iff (⊥ : Subgroup G) V hV x y).1 hxy
    rwa [Subgroup.mem_bot] at h'
  exact IntMod.val_injective (mul_inv_eq_one.1 h)

private theorem s16c4v1_set_wSub_conj (S : s16c4v1_Sit D V L hV) {m : G} (hm : m ∈ D.M) :
    conjSubgroup (wSub (⊥ : Subgroup G) V hV L) m = wSub (⊥ : Subgroup G) V hV L := by
  have hpair := S.sect.setting.hyp16.hyp125.pairFacts
  have hmstab : m ∈ stabTil (⊥ : Subgroup G) V :=
    le_stabTil hpair.le_normalizer hpair.le_normalizer₀ hm
  have hbar : barSub (⊥ : Subgroup G) V hV (conjSubgroup L m) =
      barSub (⊥ : Subgroup G) V hV L :=
    (s15_Infra_mem_nBar_iff S.sect.setting.hyp16.hyp125 hV hm).1 (by
      rw [Sixteen24.nBar_eq_of_uFrame D S.sect.setting.hyp151 hV S.F]
      exact hm)
  have hw : wSub (⊥ : Subgroup G) V hV (conjSubgroup L m) = wSub (⊥ : Subgroup G) V hV L := by
    unfold wSub wTil
    rw [hbar]
  rw [← s15_Infra_wSub_conjSubgroup (V₀ := ⊥) (V := V) (L := L) hV hmstab, hw]

theorem s16c4v1_conj_mem (S : s16c4v1_Sit D V L hV) {m : G} (hm : m ∈ D.M) {v : G}
    (hv : v ∈ V) : m * v * m⁻¹ ∈ V :=
  (Subgroup.mem_normalizer_iff.1
    (S.sect.setting.hyp16.hyp125.pairFacts.le_normalizer hm) v).1 hv

theorem s16c4v1_conj_mem_v1 (S : s16c4v1_Sit D V L hV) {m : G} (hm : m ∈ D.M) {v : G}
    (hv : v ∈ v1Sub D.M ⊥ V hV L) : m * v * m⁻¹ ∈ v1Sub D.M ⊥ V hV L :=
  (Subgroup.mem_normalizer_iff.1
    (s15_Infra_le_normalizer_v1Sub S.sect.setting.hyp16.hyp125 hV hm) v).1 hv

theorem s16c4v1_v1_le (S : s16c4v1_Sit D V L hV) : v1Sub D.M ⊥ V hV L ≤ V :=
  s15_Infra_v1Sub_le S.sect.setting.hyp16.hyp125 hV

theorem s16c4v1_mem_stabTil (S : s16c4v1_Sit D V L hV) {m : G} (hm : m ∈ D.M) :
    m ∈ stabTil (v1Sub D.M ⊥ V hV L) V :=
  s15_T7_le_stabTil_v1Sub S.sect.setting.hyp151 hm

theorem s16c4v1_card_V (S : s16c4v1_Sit D V L hV) :
    Nat.card V = 2 ^ 8 * Nat.card (v1Sub D.M ⊥ V hV L) :=
  S.F.card_V_of_le (s16c4v1_v1_le S)

theorem s16c4v1_centralizes_iff (S : s16c4v1_Sit D V L hV) (h1217 : R1217 D) {m : G}
    (hm : m ∈ D.M) :
    (∀ v ∈ V, m * v * m⁻¹ * v⁻¹ ∈ v1Sub D.M ⊥ V hV L) ↔ ∀ v ∈ V, m * v * m⁻¹ = v := by
  have h := Sixteen24.centralizesMod_v1Sub_iff D h1217 S.sect.setting.hyp151 hV hm
  unfold CentralizesMod at h
  constructor
  · intro hc v hv
    have h1 := h.1 hc v hv
    rw [Subgroup.mem_bot, mul_inv_eq_one] at h1
    exact h1
  · intro hc
    refine h.2 fun v hv => ?_
    rw [Subgroup.mem_bot, mul_inv_eq_one]
    exact hc v hv

theorem s16c4v1_L_centralizes_V1 (S : s16c4v1_Sit D V L hV) {l : G} (hl : l ∈ L)
    {v : G} (hv : v ∈ v1Sub D.M ⊥ V hV L) : l * v * l⁻¹ = v := by
  have hlM : l ∈ D.M := S.sect.setting.hyp151.le hl
  have hpair := S.sect.setting.hyp16.hyp125.pairFacts
  have hle : v1Sub D.M ⊥ V hV L ≤ Subgroup.centralizer ({l} : Set G) := by
    rw [v1Sub_of_eq_bot D.M ⊥ V hV L rfl]
    refine iSup_le fun m => ?_
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    rw [mem_conjSubgroup_iff] at hx
    obtain ⟨hxW, hxC⟩ := Subgroup.mem_inf.1 hx
    let c : G := (m : G) * x * (m : G)⁻¹
    have hc : c = (m : G) * x * (m : G)⁻¹ := rfl
    have hxW' : c ∈ wSub (⊥ : Subgroup G) V hV L := by rw [hc]; exact hxW
    have hxC' : c ∈ centralizer (L : Set G) := by rw [hc]; exact hxC
    have hxW'' : c ∈ preTil (⊥ : Subgroup G) V hV (wTil (⊥ : Subgroup G) V hV L) := by
      rwa [wSub] at hxW'
    have hcV : c ∈ V := preTil_le (⊥ : Subgroup G) V hV _ hxW''
    have hxrepr : x = (m : G)⁻¹ * c * (m : G) := by rw [hc]; group
    let a : G := (m : G) * l * (m : G)⁻¹
    have ha : a = (m : G) * l * (m : G)⁻¹ := rfl
    have haM : a ∈ D.M := by
      rw [ha]; exact D.M.mul_mem (D.M.mul_mem m.2 hlM) (D.M.inv_mem m.2)
    have hastab : a ∈ stabTil (⊥ : Subgroup G) V :=
      le_stabTil hpair.le_normalizer hpair.le_normalizer₀ haM
    have haL : a ∈ conjSubgroup L (m : G)⁻¹ := by
      rw [mem_conjSubgroup_iff]
      have h : (m : G)⁻¹ * a * ((m : G)⁻¹)⁻¹ = l := by rw [ha]; group
      rw [h]; exact hl
    have hbar : barSub (⊥ : Subgroup G) V hV (conjSubgroup L (m : G)⁻¹) =
        barSub (⊥ : Subgroup G) V hV L :=
      (s15_Infra_mem_nBar_iff S.sect.setting.hyp16.hyp125 hV (D.M.inv_mem m.2)).1 (by
        rw [Sixteen24.nBar_eq_of_uFrame D S.sect.setting.hyp151 hV S.F]
        exact D.M.inv_mem m.2)
    have hmem : actTil (⊥ : Subgroup G) V hV ⟨a, hastab⟩ ∈ barSub (⊥ : Subgroup G) V hV L := by
      rw [← hbar]
      exact actTil_mem_barSub (⊥ : Subgroup G) V hV haL hastab
    obtain ⟨l', hl'L, hl'eq⟩ := (mem_barSub (⊥ : Subgroup G) V hV L _).1 hmem
    have haca : a * c * a⁻¹ = c := by
      have h1 : actTil (⊥ : Subgroup G) V hV (⟨a, hastab⟩⁻¹ * l') = 1 := by
        rw [map_mul, map_inv, hl'eq, inv_mul_cancel]
      have h2 := (actTil_eq_one_iff (⊥ : Subgroup G) V hV _).1 h1 c hcV
      rw [Subgroup.mem_bot, mul_inv_eq_one] at h2
      have h3 : a⁻¹ * ((l' : G) * c * (l' : G)⁻¹) * a = c := by
        simpa [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev, mul_assoc] using h2
      have h4 : a * c * a⁻¹ = (l' : G) * c * (l' : G)⁻¹ := by
        calc a * c * a⁻¹ = a * (a⁻¹ * ((l' : G) * c * (l' : G)⁻¹) * a) * a⁻¹ := by rw [h3]
          _ = (l' : G) * c * (l' : G)⁻¹ := by group
      have hcl : (l' : G) * c * (l' : G)⁻¹ = c := by
        have hcomm := (Subgroup.mem_centralizer_iff.1 hxC') (l' : G) hl'L
        rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
      rw [h4, hcl]
    have hlx : l * x * l⁻¹ = (m : G)⁻¹ * (a * c * a⁻¹) * (m : G) := by
      rw [hxrepr, ha, hc]
      group
    have hgoal : l * x * l⁻¹ = x := by rw [hlx, haca, hxrepr]
    show l * x = x * l
    rw [show l * x = (l * x * l⁻¹) * l by group, hgoal]
  have hcomm : l * v = v * l := (Subgroup.mem_centralizer_iff.1 (hle hv)) l (Set.mem_singleton l)
  rw [hcomm]
  group

theorem s16c4v1_comm_eq (S : s16c4v1_Sit D V L hV) : ⁅V, L⁆ = V := by
  have hpair := S.sect.setting.hyp16.hyp125.pairFacts
  have hWconj : ∀ m : D.M, conjSubgroup (wSub (⊥ : Subgroup G) V hV L) (m : G) =
      wSub (⊥ : Subgroup G) V hV L := fun m => s16c4v1_set_wSub_conj S m.2
  have hV1leW : v1Sub D.M ⊥ V hV L ≤ wSub (⊥ : Subgroup G) V hV L := by
    rw [v1Sub_of_eq_bot D.M ⊥ V hV L rfl]
    refine iSup_le fun m => ?_
    have h1 : conjSubgroup (wSub (⊥ : Subgroup G) V hV L ⊓ centralizer (L : Set G)) (m : G) ≤
        conjSubgroup (wSub (⊥ : Subgroup G) V hV L) (m : G) := Subgroup.map_mono inf_le_left
    rwa [hWconj m] at h1
  have hWV : wSub (⊥ : Subgroup G) V hV L = V := by
    have h := Sixteen24.wSub_sup_v1Sub_eq_of_uFrame D S.sect.setting.hyp151 hV S.F
    rw [sup_eq_left.mpr hV1leW] at h
    exact h
  have hle : ⁅V, L⁆ ≤ V := by
    rw [Subgroup.commutator_le]
    intro v hv l hl
    have hlN : l ∈ normalizer (V : Set G) :=
      hpair.le_normalizer (S.sect.setting.hyp151.le hl)
    have hconj : l * v⁻¹ * l⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.1 hlN v⁻¹).1 (V.inv_mem hv)
    show v * l * v⁻¹ * l⁻¹ ∈ V
    rw [show v * l * v⁻¹ * l⁻¹ = v * (l * v⁻¹ * l⁻¹) by group]
    exact V.mul_mem hv hconj
  have hWle : wSub (⊥ : Subgroup G) V hV L ≤ ⁅V, L⁆ := by
    intro g hg
    rw [wSub] at hg
    have hgV : g ∈ V := preTil_le (⊥ : Subgroup G) V hV _ hg
    have hgS : mkTil (⊥ : Subgroup G) V hV (IntMod.mk hV ⟨g, hgV⟩) ∈
        wTil (⊥ : Subgroup G) V hV L :=
      (mem_preTil_iff_of_mem (⊥ : Subgroup G) V hV _ hgV).1 hg
    have hgen : {c : Vtil (⊥ : Subgroup G) V hV |
        ∃ x ∈ barSub (⊥ : Subgroup G) V hV L,
          ∃ w ∈ (⊤ : Subgroup (Vtil (⊥ : Subgroup G) V hV)), x w * w⁻¹ = c} ⊆
        (intSub V hV ⁅V, L⁆).map (mkTil (⊥ : Subgroup G) V hV) := by
      rintro c ⟨x, hx, w, -, rfl⟩
      obtain ⟨l, hlL, hlφ⟩ := (mem_barSub (⊥ : Subgroup G) V hV L x).1 hx
      obtain ⟨y, rfl⟩ := mkTil_surjective (⊥ : Subgroup G) V hV w
      refine Subgroup.mem_map.mpr ⟨actStab (⊥ : Subgroup G) V hV l y * y⁻¹, ?_, ?_⟩
      · rw [mem_intSub, IntMod.val_mul, IntMod.val_inv, actStab_apply_val]
        rw [← Subgroup.commutator_comm L V]
        exact Subgroup.commutator_mem_commutator hlL y.val_mem
      · rw [← hlφ, actTil_mk, ← map_inv, ← map_mul]
    have hcomm : mkTil (⊥ : Subgroup G) V hV (IntMod.mk hV ⟨g, hgV⟩) ∈
        commSub (⊤ : Subgroup (Vtil (⊥ : Subgroup G) V hV))
          (barSub (⊥ : Subgroup G) V hV L) := by
      simpa [wTil] using hgS
    have hcl : commSub (⊤ : Subgroup (Vtil (⊥ : Subgroup G) V hV))
        (barSub (⊥ : Subgroup G) V hV L) ≤
        (intSub V hV ⁅V, L⁆).map (mkTil (⊥ : Subgroup G) V hV) := by
      rw [commSub, Subgroup.closure_le]
      exact hgen
    obtain ⟨x, hx, hxeq⟩ := Subgroup.mem_map.1 (hcl hcomm)
    rw [mem_intSub] at hx
    have hx' : x = IntMod.mk hV ⟨g, hgV⟩ := s16c4v1_set_mkTil_bot_injective V hV hxeq
    rw [hx'] at hx
    exact hx
  exact le_antisymm hle ((le_of_eq hWV.symm).trans hWle)

theorem s16c4v1_vec_mul (S : s16c4v1_Sit D V L hV) {v w : G} (hv : v ∈ V) (hw : w ∈ V) :
    s16c4v1_vec S (v * w) = s16c4v1_vec S v + s16c4v1_vec S w := by
  rw [s16c4v1_set_vec_of_mem S hv, s16c4v1_set_vec_of_mem S hw,
    s16c4v1_set_vec_of_mem S (V.mul_mem hv hw)]
  have h : (IntMod.mk hV ⟨v * w, V.mul_mem hv hw⟩ : IntMod V hV) =
      IntMod.mk hV ⟨v, hv⟩ * IntMod.mk hV ⟨w, hw⟩ := rfl
  rw [h, map_mul, S.F.vec_mul]

theorem s16c4v1_vec_one (S : s16c4v1_Sit D V L hV) : s16c4v1_vec S 1 = 0 := by
  rw [s16c4v1_set_vec_of_mem S V.one_mem]
  have h : (IntMod.mk hV ⟨1, V.one_mem⟩ : IntMod V hV) = 1 := rfl
  rw [h, map_one, S.F.vec_one]

theorem s16c4v1_vec_eq_zero_iff (S : s16c4v1_Sit D V L hV) {v : G} (hv : v ∈ V) :
    s16c4v1_vec S v = 0 ↔ v ∈ v1Sub D.M ⊥ V hV L := by
  rw [s16c4v1_set_vec_of_mem S hv]
  have h0 : (0 : Fin 4 → S.F.K) = S.F.vec (1 : Vtil (v1Sub D.M ⊥ V hV L) V hV) :=
    S.F.vec_one.symm
  rw [h0, S.F.vec_injective.eq_iff]
  exact (QuotientGroup.eq_one_iff (N := modNull (v1Sub D.M ⊥ V hV L) V hV)
      (IntMod.mk hV ⟨v, hv⟩)).trans (mem_modNull (v1Sub D.M ⊥ V hV L) V hV _)

theorem s16c4v1_exists_vec (S : s16c4v1_Sit D V L hV) (x : Fin 4 → S.F.K) :
    ∃ v ∈ V, s16c4v1_vec S v = x := by
  obtain ⟨y, hy⟩ := mkTil_surjective (v1Sub D.M ⊥ V hV L) V hV (S.F.ofVec x)
  refine ⟨y.val, y.val_mem, ?_⟩
  rw [s16c4v1_set_vec_of_mem S y.val_mem,
    show IntMod.mk hV ⟨y.val, y.val_mem⟩ = y from Subtype.ext rfl, hy, S.F.vec_ofVec]

theorem s16c4v1_vec_conj (S : s16c4v1_Sit D V L hV) {m : G} (hm : m ∈ D.M) {v : G}
    (hv : v ∈ V) :
    s16c4v1_vec S (m * v * m⁻¹) =
      S.F.rho (actTil (v1Sub D.M ⊥ V hV L) V hV ⟨m, s16c4v1_mem_stabTil S hm⟩)
        (s16c4v1_vec S v) := by
  have hmv : m * v * m⁻¹ ∈ V := s16c4v1_conj_mem S hm hv
  rw [s16c4v1_set_vec_of_mem S hmv, s16c4v1_set_vec_of_mem S hv,
    S.F.rho_vec (actTil (v1Sub D.M ⊥ V hV L) V hV ⟨m, s16c4v1_mem_stabTil S hm⟩)
      (mkTil (v1Sub D.M ⊥ V hV L) V hV (IntMod.mk hV ⟨v, hv⟩))]
  rw [S.F.vec_injective.eq_iff, actTil_mk]
  apply congrArg (mkTil (v1Sub D.M ⊥ V hV L) V hV)
  apply IntMod.val_injective
  rw [actStab_apply_val]
  rfl

theorem s16c4v1_induces_of_mem_L (S : s16c4v1_Sit D V L hV) {l : G} (hl : l ∈ L) :
    ∃ γ : ↥(SUid S.F.σ 4), s16c4v1_Induces S l γ := by
  have hlM : l ∈ D.M := S.sect.setting.hyp151.le hl
  have hφ : actTil (v1Sub D.M ⊥ V hV L) V hV ⟨l, s16c4v1_mem_stabTil S hlM⟩ ∈
      lBar (v1Sub D.M ⊥ V hV L) V hV L :=
    actTil_mem_barSub _ _ _ hl (s16c4v1_mem_stabTil S hlM)
  let γ : ↥(SUid S.F.σ 4) := S.F.π.symm ⟨_, hφ⟩
  refine ⟨γ, fun v hv => ?_⟩
  have hπ : (S.F.π γ : MulAut (Vtil (v1Sub D.M ⊥ V hV L) V hV)) =
      actTil (v1Sub D.M ⊥ V hV L) V hV ⟨l, s16c4v1_mem_stabTil S hlM⟩ := by
    simp [γ]
  rw [s16c4v1_vec_conj S hlM hv, ← hπ, s16c4v1_set_rho_pi]

theorem s16c4v1_exists_induces (S : s16c4v1_Sit D V L hV) (γ : ↥(SUid S.F.σ 4)) :
    ∃ l ∈ L, s16c4v1_Induces S l γ := by
  obtain ⟨g, hgL, hg⟩ := (mem_barSub (v1Sub D.M ⊥ V hV L) V hV L
    (S.F.π γ : MulAut (Vtil (v1Sub D.M ⊥ V hV L) V hV))).1 (S.F.π γ).2
  refine ⟨(g : G), hgL, fun v hv => ?_⟩
  have hgM : (g : G) ∈ D.M := S.sect.setting.hyp151.le hgL
  have hsub : (⟨(g : G), s16c4v1_mem_stabTil S hgM⟩ :
      stabTil (v1Sub D.M ⊥ V hV L) V) = g := Subtype.ext rfl
  rw [s16c4v1_vec_conj S hgM hv]
  rw [show actTil (v1Sub D.M ⊥ V hV L) V hV ⟨(g : G), s16c4v1_mem_stabTil S hgM⟩ =
      S.F.π γ from by rw [hsub, hg]]
  rw [s16c4v1_set_rho_pi]

theorem s16c4v1_induces_unique (S : s16c4v1_Sit D V L hV) {m : G} {γ γ' : ↥(SUid S.F.σ 4)}
    (h : s16c4v1_Induces S m γ) (h' : s16c4v1_Induces S m γ') : γ = γ' := by
  refine CFSG.ClassicalGroups.Unitary.ext_smul S.F.σ fun x => ?_
  obtain ⟨v, hv, hvx⟩ := s16c4v1_exists_vec S x
  rw [← hvx, ← h v hv, ← h' v hv]

theorem s16c4v1_induces_mul (S : s16c4v1_Sit D V L hV) {m m' : G} (hm : m ∈ D.M)
    (hm' : m' ∈ D.M) {γ γ' : ↥(SUid S.F.σ 4)} (h : s16c4v1_Induces S m γ)
    (h' : s16c4v1_Induces S m' γ') : s16c4v1_Induces S (m * m') (γ * γ') := by
  intro v hv
  have h1 : m' * v * m'⁻¹ ∈ V := s16c4v1_conj_mem S hm' hv
  have heq : m * (m' * v * m'⁻¹) * m⁻¹ = (m * m') * v * (m * m')⁻¹ := by group
  rw [← heq, h _ h1, h' v hv, mul_smul]

private theorem s16c4v1_set_isLin_mul (S : s16c4v1_Sit D V L hV)
    {φ ψ : MulAut (Vtil (v1Sub D.M ⊥ V hV L) V hV)}
    (hφ : S.F.IsLin φ) (hψ : S.F.IsLin ψ) : S.F.IsLin (φ * ψ) := by
  intro c x
  calc S.F.rho (φ * ψ) (c • x)
      = S.F.rho φ (S.F.rho ψ (c • x)) := S.F.rho_mul φ ψ (c • x)
    _ = S.F.rho φ (c • S.F.rho ψ x) := by rw [hψ c x]
    _ = c • S.F.rho φ (S.F.rho ψ x) := hφ c (S.F.rho ψ x)
    _ = c • S.F.rho (φ * ψ) x := by rw [S.F.rho_mul]

private theorem s16c4v1_set_isLin_pow (S : s16c4v1_Sit D V L hV)
    {φ : MulAut (Vtil (v1Sub D.M ⊥ V hV L) V hV)} (hφ : S.F.IsLin φ) (k : ℕ) :
    S.F.IsLin (φ ^ k) := by
  induction k with
  | zero => intro c x; simp [UFrame.rho]
  | succ k ih => rw [pow_succ]; exact s16c4v1_set_isLin_mul S ih hφ

theorem s16c4v1_odd_lin (S : s16c4v1_Sit D V L hV) (h1217 : R1217 D) {m : G} (hm : m ∈ D.M)
    (hodd : Odd (orderOf m)) : s16c4v1_Lin S m := by
  let g : stabTil (v1Sub D.M ⊥ V hV L) V := ⟨m, s16c4v1_mem_stabTil S hm⟩
  let φ : MulAut (Vtil (v1Sub D.M ⊥ V hV L) V hV) := actTil (v1Sub D.M ⊥ V hV L) V hV g
  have hgN : m ∈ nBar D.M ⊥ V hV L := by
    rw [Sixteen24.nBar_eq_of_uFrame D S.sect.setting.hyp151 hV S.F]
    exact hm
  have hφN : φ ∈ normalizer (lBar (v1Sub D.M ⊥ V hV L) V hV L :
      Set (MulAut (Vtil (v1Sub D.M ⊥ V hV L) V hV))) :=
    Sixteen24.actTil_v1Sub_mem_normalizer D h1217 S.sect.setting.hyp151 hV hm hgN g.2
  have hgn : g ^ orderOf m = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact pow_orderOf_eq_one m
  have hφn : φ ^ orderOf m = 1 := by
    change (actTil (v1Sub D.M ⊥ V hV L) V hV g) ^ orderOf m = 1
    rw [← map_pow, hgn, map_one]
  have hlin : S.F.IsLin φ := by
    rcases S.F.isLin_or_isSemi hφN with hl | hs
    · exact hl
    · exfalso
      obtain ⟨k, hk⟩ := hodd
      have hphi : φ = (φ ^ 2) ^ (k + 1) := by
        rw [← pow_mul]
        have h2 : 2 * (k + 1) = orderOf m + 1 := by omega
        rw [h2, pow_succ, hφn, one_mul]
      have hlin2 : S.F.IsLin (φ ^ 2) := by
        rw [pow_two]
        exact S.F.isLin_mul_of_isSemi hs hs
      have hlinφ : S.F.IsLin φ := by
        rw [hphi]
        exact s16c4v1_set_isLin_pow S hlin2 (k + 1)
      exact S.F.not_isSemi_of_isLin hlinφ hs
  let lin : (Fin 4 → S.F.K) →ₗ[S.F.K] (Fin 4 → S.F.K) :=
    { toFun := S.F.rho φ
      map_add' := fun x y => map_add (S.F.rho φ) x y
      map_smul' := hlin }
  let A : Matrix (Fin 4) (Fin 4) S.F.K := LinearMap.toMatrix' lin
  have hA : ∀ x, A *ᵥ x = S.F.rho φ x := fun x => by
    show LinearMap.toMatrix' lin *ᵥ x = S.F.rho φ x
    rw [LinearMap.toMatrix'_mulVec]
    rfl
  have hAunit : IsUnit A := by
    apply Matrix.mulVec_injective_iff_isUnit.1
    intro x y hxy
    exact (S.F.rho φ).injective (by rw [← hA x, ← hA y]; exact hxy)
  have hN : ∀ γ : ↥(SUid S.F.σ 4), ∃ γ' : ↥(SUid S.F.σ 4),
      ∀ x : Fin 4 → S.F.K, A *ᵥ (γ • x) = γ' • (A *ᵥ x) := by
    intro γ
    have hmem : φ * (S.F.π γ : MulAut (Vtil (v1Sub D.M ⊥ V hV L) V hV)) * φ⁻¹ ∈
        lBar (v1Sub D.M ⊥ V hV L) V hV L := by
      have h := (Subgroup.mem_set_normalizer_iff.1 hφN (S.F.π γ)).1 (S.F.π γ).2
      simpa using h
    let γ' : ↥(SUid S.F.σ 4) := S.F.π.symm ⟨_, hmem⟩
    have hπγ' : (S.F.π γ' : MulAut (Vtil (v1Sub D.M ⊥ V hV L) V hV)) =
        φ * (S.F.π γ) * φ⁻¹ := by simp [γ']
    refine ⟨γ', fun x => ?_⟩
    have hconj : φ * (S.F.π γ) = (S.F.π γ') * φ := by rw [hπγ']; group
    calc A *ᵥ (γ • x)
        = S.F.rho φ (γ • x) := hA (γ • x)
      _ = S.F.rho φ (S.F.rho (S.F.π γ) x) := by rw [← s16c4v1_set_rho_pi S γ x]
      _ = S.F.rho (φ * (S.F.π γ : MulAut (Vtil (v1Sub D.M ⊥ V hV L) V hV))) x :=
            (S.F.rho_mul φ (S.F.π γ) x).symm
      _ = S.F.rho ((S.F.π γ') * φ) x := by rw [hconj]
      _ = S.F.rho (S.F.π γ') (S.F.rho φ x) := S.F.rho_mul (S.F.π γ') φ x
      _ = γ' • (S.F.rho φ x) := s16c4v1_set_rho_pi S γ' (S.F.rho φ x)
      _ = γ' • (A *ᵥ x) := by rw [hA x]
  obtain ⟨c, γ, hc, hγ⟩ :=
    s16c4v1_lin_normalizer S.F.σ S.F.card_K S.F.isUnitary A hAunit hN
  refine ⟨c, γ, hc, fun v hv => ?_⟩
  rw [s16c4v1_vec_conj S hm hv, ← hA (s16c4v1_vec S v), hγ (s16c4v1_vec S v)]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
