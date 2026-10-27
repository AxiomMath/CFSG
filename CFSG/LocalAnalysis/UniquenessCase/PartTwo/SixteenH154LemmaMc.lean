module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154LemmaMa
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23ATwoConj
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenGlue
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

private theorem s16h_mkTil_bot_injective {V : Subgroup G} (hV : IsElemAbelian 2 V) :
    Function.Injective (mkTil (⊥ : Subgroup G) V hV) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_bot]
  constructor
  · intro h
    have hx : x ∈ modNull ⊥ V hV := (QuotientGroup.eq_one_iff (N := modNull ⊥ V hV) x).1 h
    rw [mem_modNull] at hx
    exact IntMod.val_injective (by simpa using hx)
  · rintro rfl
    exact map_one _

private theorem s16h_map_conj_one {A : Type*} [Group A] (H : Subgroup A) :
    H.map (MulAut.conj (1 : A)).toMonoidHom = H := by
  ext x
  simp [Subgroup.mem_map]

private theorem s16h_map_conj_mul {A : Type*} [Group A] (H : Subgroup A) (a b : A) :
    (H.map (MulAut.conj a).toMonoidHom).map (MulAut.conj b).toMonoidHom =
      H.map (MulAut.conj (b * a)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext t
  simp [MulAut.conj_apply, mul_assoc]

private theorem s16h_mem_preTil_inf_iff {V : Subgroup G} (hV : IsElemAbelian 2 V)
    {S T : Subgroup (Vtil ⊥ V hV)} {v : G} (hv : v ∈ V) :
    v ∈ preTil ⊥ V hV (S ⊓ T) ↔ v ∈ preTil ⊥ V hV S ∧ v ∈ preTil ⊥ V hV T := by
  simp only [mem_preTil_iff_of_mem ⊥ V hV _ hv, Subgroup.mem_inf]

private theorem s16h_wSub_inf_centralizer_eq_preTil_of_le {V : Subgroup G}
    (hV : IsElemAbelian 2 V) {L' : Subgroup G} (hL' : L' ≤ stabTil ⊥ V) :
    wSub ⊥ V hV L' ⊓ centralizer (L' : Set G) =
      preTil ⊥ V hV (commSub ⊤ (barSub ⊥ V hV L') ⊓ fixV (barSub ⊥ V hV L')) := by
  refine le_antisymm ?_ ?_
  · intro v hv
    have hvW : v ∈ wSub ⊥ V hV L' := (Subgroup.mem_inf.1 hv).1
    have hvC : v ∈ centralizer (L' : Set G) := (Subgroup.mem_inf.1 hv).2
    have hvV : v ∈ V := preTil_le ⊥ V hV _ hvW
    rw [mem_preTil_iff_of_mem ⊥ V hV _ hvV, Subgroup.mem_inf]
    constructor
    · unfold wSub wTil at hvW
      rwa [mem_preTil_iff_of_mem ⊥ V hV _ hvV] at hvW
    · rw [← mem_preTil_iff_of_mem ⊥ V hV _ hvV,
        s15_Glue_mem_preTil_fixV_iff ⊥ V L' hV hL' hvV]
      intro e he
      rw [Subgroup.mem_bot]
      have h := (Subgroup.mem_centralizer_iff.1 hvC) e he
      calc e * v * e⁻¹ * v⁻¹ = (v * e) * e⁻¹ * v⁻¹ := by rw [h]
        _ = 1 := by group
  · intro v hv
    have hvV : v ∈ V := preTil_le ⊥ V hV _ hv
    have hmem : mkTil ⊥ V hV (IntMod.mk hV ⟨v, hvV⟩) ∈
        commSub ⊤ (barSub ⊥ V hV L') ⊓ fixV (barSub ⊥ V hV L') :=
      (mem_preTil_iff_of_mem ⊥ V hV _ hvV).1 hv
    rw [Subgroup.mem_inf] at hmem
    rw [Subgroup.mem_inf]
    constructor
    · unfold wSub wTil
      rw [mem_preTil_iff_of_mem ⊥ V hV _ hvV]
      exact hmem.1
    · rw [Subgroup.mem_centralizer_iff]
      intro l hl
      have hfix : v ∈ preTil ⊥ V hV (fixV (barSub ⊥ V hV L')) := by
        rw [mem_preTil_iff_of_mem ⊥ V hV _ hvV]
        exact hmem.2
      rw [s15_Glue_mem_preTil_fixV_iff ⊥ V L' hV hL' hvV] at hfix
      have h := hfix l hl
      rw [Subgroup.mem_bot] at h
      have h1 : l * v * l⁻¹ = v := mul_inv_eq_one.1 h
      calc l * v = (l * v * l⁻¹) * l := by group
        _ = v * l := by rw [h1]

private theorem s16h_map_conj_eq_preTil (D : Data G) {V L : Subgroup G}
    (h : Setting16 D ⊥ V L) (hMs : D.M ≤ stabTil ⊥ V) {m : G} (hm : m ∈ D.M) :
    (wSub ⊥ V h.hyp151.isElemAbelian L ⊓ centralizer (L : Set G)).map
        (MulAut.conj m).toMonoidHom =
      preTil ⊥ V h.hyp151.isElemAbelian
        (commSub ⊤ ((lBar ⊥ V h.hyp151.isElemAbelian L).map
            (MulAut.conj (actTil ⊥ V h.hyp151.isElemAbelian ⟨m, hMs hm⟩)).toMonoidHom) ⊓
          fixV ((lBar ⊥ V h.hyp151.isElemAbelian L).map
            (MulAut.conj (actTil ⊥ V h.hyp151.isElemAbelian ⟨m, hMs hm⟩)).toMonoidHom)) := by
  have hV := h.hyp151.isElemAbelian
  have hminv : m⁻¹ ∈ stabTil ⊥ V := (stabTil ⊥ V).inv_mem (hMs hm)
  have hL' : conjSubgroup L m⁻¹ ≤ stabTil ⊥ V := by
    refine (E3.conjSubgroup_mono_left m⁻¹ (h.hyp151.le.trans hMs)).trans ?_
    rw [show conjSubgroup (stabTil ⊥ V) m⁻¹ = stabTil ⊥ V from
      conjSubgroup_eq_iff_mem_normalizer.mpr (Subgroup.le_normalizer hminv)]
  have hmap : (wSub ⊥ V hV L ⊓ centralizer (L : Set G)).map
      (MulAut.conj m).toMonoidHom =
      conjSubgroup (wSub ⊥ V hV L ⊓ centralizer (L : Set G)) m⁻¹ := by
    ext y
    rw [Subgroup.mem_map, mem_conjSubgroup_iff]
    constructor
    · rintro ⟨z, hz, rfl⟩
      show m⁻¹ * (m * z * m⁻¹) * (m⁻¹)⁻¹ ∈ wSub ⊥ V hV L ⊓ centralizer (L : Set G)
      rw [show m⁻¹ * (m * z * m⁻¹) * (m⁻¹)⁻¹ = z by group]
      exact hz
    · intro hy
      refine ⟨m⁻¹ * y * m, ?_, ?_⟩
      · simpa only [inv_inv] using hy
      · change m * (m⁻¹ * y * m) * m⁻¹ = y
        group
  have hconj : conjSubgroup (wSub ⊥ V hV L ⊓ centralizer (L : Set G)) m⁻¹ =
      wSub ⊥ V hV (conjSubgroup L m⁻¹) ⊓ centralizer (conjSubgroup L m⁻¹ : Set G) := by
    rw [E3.conjSubgroup_inf, E3.conjSubgroup_centralizer,
      ← s15_Infra_wSub_conjSubgroup ⊥ V L hV hminv]
  have hbar : barSub ⊥ V hV (conjSubgroup L m⁻¹) =
      (barSub ⊥ V hV L).map (MulAut.conj (actTil ⊥ V hV ⟨m, hMs hm⟩)).toMonoidHom := by
    rw [s15_Infra_barSub_conjSubgroup ⊥ V hV hminv L,
      show actTil ⊥ V hV (⟨m⁻¹, hminv⟩ : stabTil ⊥ V) =
          (actTil ⊥ V hV ⟨m, hMs hm⟩)⁻¹ from by
        rw [show (⟨m⁻¹, hminv⟩ : stabTil ⊥ V) = (⟨m, hMs hm⟩ : stabTil ⊥ V)⁻¹ from rfl,
          map_inv],
      inv_inv]
  calc (wSub ⊥ V hV L ⊓ centralizer (L : Set G)).map (MulAut.conj m).toMonoidHom
      = conjSubgroup (wSub ⊥ V hV L ⊓ centralizer (L : Set G)) m⁻¹ := hmap
    _ = wSub ⊥ V hV (conjSubgroup L m⁻¹) ⊓ centralizer (conjSubgroup L m⁻¹ : Set G) := hconj
    _ = preTil ⊥ V hV (commSub ⊤ (barSub ⊥ V hV (conjSubgroup L m⁻¹)) ⊓
          fixV (barSub ⊥ V hV (conjSubgroup L m⁻¹))) :=
        s16h_wSub_inf_centralizer_eq_preTil_of_le hV hL'
    _ = preTil ⊥ V hV
          (commSub ⊤ ((lBar ⊥ V hV L).map
              (MulAut.conj (actTil ⊥ V hV ⟨m, hMs hm⟩)).toMonoidHom) ⊓
            fixV ((lBar ⊥ V hV L).map
              (MulAut.conj (actTil ⊥ V hV ⟨m, hMs hm⟩)).toMonoidHom)) := by
        rw [hbar, lBar]

private theorem s16h_preTil_Z₁_eq (D : Data G) {V L : Subgroup G}
    (h : Setting16 D ⊥ V L) (hMs : D.M ≤ stabTil ⊥ V) :
    wSub ⊥ V h.hyp151.isElemAbelian L ⊓ centralizer (L : Set G) =
      preTil ⊥ V h.hyp151.isElemAbelian
        (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
          fixV (lBar ⊥ V h.hyp151.isElemAbelian L)) := by
  have hK := s16h_map_conj_eq_preTil D h hMs (m := 1) D.M.one_mem
  have hact1 : actTil ⊥ V h.hyp151.isElemAbelian
      (⟨1, hMs D.M.one_mem⟩ : stabTil ⊥ V) = 1 := map_one _
  simpa only [hact1, s16h_map_conj_one] using hK

private theorem s16h_Z₁x_map_conj_eq_preTil (D : Data G) {V L : Subgroup G}
    (h : Setting16 D ⊥ V L) (hMs : D.M ≤ stabTil ⊥ V) {x : G} (hxM : x ∈ D.M)
    {m : G} (hm : m ∈ D.M) :
    ((wSub ⊥ V h.hyp151.isElemAbelian L ⊓ centralizer (L : Set G)).map
        (MulAut.conj x).toMonoidHom).map (MulAut.conj m).toMonoidHom =
      preTil ⊥ V h.hyp151.isElemAbelian
        (commSub ⊤ (((lBar ⊥ V h.hyp151.isElemAbelian L).map
            (MulAut.conj (actTil ⊥ V h.hyp151.isElemAbelian ⟨x, hMs hxM⟩)).toMonoidHom).map
            (MulAut.conj (actTil ⊥ V h.hyp151.isElemAbelian ⟨m, hMs hm⟩)).toMonoidHom) ⊓
          fixV (((lBar ⊥ V h.hyp151.isElemAbelian L).map
            (MulAut.conj (actTil ⊥ V h.hyp151.isElemAbelian ⟨x, hMs hxM⟩)).toMonoidHom).map
            (MulAut.conj (actTil ⊥ V h.hyp151.isElemAbelian ⟨m, hMs hm⟩)).toMonoidHom)) := by
  have hV := h.hyp151.isElemAbelian
  have hact : actTil ⊥ V hV ⟨m * x, hMs (D.M.mul_mem hm hxM)⟩ =
      actTil ⊥ V hV ⟨m, hMs hm⟩ * actTil ⊥ V hV ⟨x, hMs hxM⟩ := by
    simpa using map_mul (actTil ⊥ V hV) (⟨m, hMs hm⟩ : stabTil ⊥ V)
      (⟨x, hMs hxM⟩ : stabTil ⊥ V)
  rw [s16h_map_conj_mul (wSub ⊥ V hV L ⊓ centralizer (L : Set G)) x m,
    s16h_map_conj_eq_preTil D h hMs (D.M.mul_mem hm hxM), hact,
    ← s16h_map_conj_mul (lBar ⊥ V hV L) (actTil ⊥ V hV ⟨x, hMs hxM⟩)
      (actTil ⊥ V hV ⟨m, hMs hm⟩)]

theorem s16h_mem_centralizer_preTil_iff {V M : Subgroup G} (hV : IsElemAbelian 2 V)
    (hM : M ≤ stabTil ⊥ V) (S : Subgroup (Vtil ⊥ V hV)) {g : G} (hg : g ∈ M) :
    g ∈ centralizer ((preTil ⊥ V hV S : Subgroup G) : Set G) ↔
      actTil ⊥ V hV ⟨g, hM hg⟩ ∈ centSub S := by
  constructor
  · intro hgC u hu
    obtain ⟨x, rfl⟩ := mkTil_surjective ⊥ V hV u
    rw [actTil_mk]
    congr 1
    apply IntMod.val_injective
    rw [actStab_apply_val]
    have hxS : x.val ∈ preTil ⊥ V hV S := (mem_preTil ⊥ V hV S).2 ⟨x, rfl, hu⟩
    have hcomm := (Subgroup.mem_centralizer_iff.1 hgC) x.val hxS
    calc g * x.val * g⁻¹ = (x.val * g) * g⁻¹ := by rw [hcomm]
      _ = x.val := by group
  · intro hfix
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    obtain ⟨x, rfl, hxS⟩ := (mem_preTil ⊥ V hV S).1 hv
    have h1 : actTil ⊥ V hV ⟨g, hM hg⟩ (mkTil ⊥ V hV x) = mkTil ⊥ V hV x :=
      hfix (mkTil ⊥ V hV x) hxS
    rw [actTil_mk] at h1
    have h2 : actStab ⊥ V hV ⟨g, hM hg⟩ x = x := s16h_mkTil_bot_injective hV h1
    have h3 : g * x.val * g⁻¹ = x.val := by
      have h := congrArg IntMod.val h2
      rwa [actStab_apply_val] at h
    have h4 : g * x.val = x.val * g := by
      calc g * x.val = (g * x.val * g⁻¹) * g := by group
        _ = x.val * g := by rw [h3]
    exact h4.symm

theorem s16h_wSub_inf_centralizer_eq_preTil (D : Data G) {V L : Subgroup G}
    (h : Setting16 D ⊥ V L) :
    wSub ⊥ V h.hyp151.isElemAbelian L ⊓ centralizer (L : Set G) =
      preTil ⊥ V h.hyp151.isElemAbelian
        (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
          fixV (lBar ⊥ V h.hyp151.isElemAbelian L)) := by
  have hMs : D.M ≤ stabTil ⊥ V :=
    le_stabTil h.hyp151.hyp125.pairFacts.le_normalizer h.hyp151.hyp125.pairFacts.le_normalizer₀
  simpa [lBar] using
    s16h_wSub_inf_centralizer_eq_preTil_of_le h.hyp151.isElemAbelian (h.hyp151.le.trans hMs)

theorem s16h_v1Sub_eq_sup_of_s_two (D : Data G) {V L : Subgroup G} (h : Setting16 D ⊥ V L)
    (hs : s15 D.M ⊥ V h.hyp151.isElemAbelian L = 2) {x : G} (hxM : x ∈ D.M)
    (hx : x ∉ nBar D.M ⊥ V h.hyp151.isElemAbelian L) :
    v1Sub D.M ⊥ V h.hyp151.isElemAbelian L =
        (wSub ⊥ V h.hyp151.isElemAbelian L ⊓ centralizer (L : Set G)) ⊔
          (wSub ⊥ V h.hyp151.isElemAbelian L ⊓ centralizer (L : Set G)).map
            (MulAut.conj x).toMonoidHom ∧
      ∀ m ∈ D.M,
        ((wSub ⊥ V h.hyp151.isElemAbelian L ⊓ centralizer (L : Set G)).map
              (MulAut.conj m).toMonoidHom =
            wSub ⊥ V h.hyp151.isElemAbelian L ⊓ centralizer (L : Set G) ∧
          ((wSub ⊥ V h.hyp151.isElemAbelian L ⊓ centralizer (L : Set G)).map
              (MulAut.conj x).toMonoidHom).map (MulAut.conj m).toMonoidHom =
            (wSub ⊥ V h.hyp151.isElemAbelian L ⊓ centralizer (L : Set G)).map
              (MulAut.conj x).toMonoidHom) ∨
        ((wSub ⊥ V h.hyp151.isElemAbelian L ⊓ centralizer (L : Set G)).map
              (MulAut.conj m).toMonoidHom =
            (wSub ⊥ V h.hyp151.isElemAbelian L ⊓ centralizer (L : Set G)).map
              (MulAut.conj x).toMonoidHom ∧
          ((wSub ⊥ V h.hyp151.isElemAbelian L ⊓ centralizer (L : Set G)).map
              (MulAut.conj x).toMonoidHom).map (MulAut.conj m).toMonoidHom =
            wSub ⊥ V h.hyp151.isElemAbelian L ⊓ centralizer (L : Set G)) := by
  have hV := h.hyp151.isElemAbelian
  have h125 := h.hyp151.hyp125
  have hMs : D.M ≤ stabTil ⊥ V :=
    le_stabTil h125.pairFacts.le_normalizer h125.pairFacts.le_normalizer₀
  have hxbar_mem : actTil ⊥ V hV ⟨x, hMs hxM⟩ ∈ Mbar D.M ⊥ V hV :=
    actTil_mem_barSub ⊥ V hV hxM (hMs hxM)
  have hxne : (lBar ⊥ V hV L).map (MulAut.conj (actTil ⊥ V hV ⟨x, hMs hxM⟩)).toMonoidHom ≠
      lBar ⊥ V hV L := by
    intro hcon
    apply hx
    rw [nBar, mem_preBarSub]
    exact ⟨hxM, hMs hxM, (Subgroup.mem_normalizer_iff_map_conj_eq).2 hcon⟩
  have hs' : Set.ncard {X : Subgroup (MulAut (Vtil ⊥ V hV)) |
      ∃ φ ∈ Mbar D.M ⊥ V hV, X = (lBar ⊥ V hV L).map (MulAut.conj φ).toMonoidHom} = 2 := by
    simpa [s15, lBar] using hs
  have hperm := (c23a_two_conj hs').2 (actTil ⊥ V hV ⟨x, hMs hxM⟩) hxbar_mem hxne
  have hcases : ∀ φ ∈ Mbar D.M ⊥ V hV, (lBar ⊥ V hV L).map
        (MulAut.conj φ).toMonoidHom = lBar ⊥ V hV L ∨
      (lBar ⊥ V hV L).map (MulAut.conj φ).toMonoidHom =
        (lBar ⊥ V hV L).map (MulAut.conj (actTil ⊥ V hV ⟨x, hMs hxM⟩)).toMonoidHom :=
    hperm.1
  have hZ₁eq : wSub ⊥ V hV L ⊓ centralizer (L : Set G) =
      preTil ⊥ V hV (commSub ⊤ (lBar ⊥ V hV L) ⊓ fixV (lBar ⊥ V hV L)) :=
    s16h_preTil_Z₁_eq D h hMs
  refine ⟨?_, ?_⟩
  · rw [s15_Infra_v1Sub_eq_iSup h125 hV rfl]
    refine le_antisymm ?_ ?_
    · refine iSup_le fun m => ?_
      have hterm : wSub ⊥ V hV (conjSubgroup L (m : G)) ⊓
          centralizer (conjSubgroup L (m : G) : Set G) =
          conjSubgroup (wSub ⊥ V hV L ⊓ centralizer (L : Set G)) (m : G) := by
        rw [E3.conjSubgroup_inf, E3.conjSubgroup_centralizer,
          ← s15_Infra_wSub_conjSubgroup ⊥ V L hV (hMs m.2)]
      rw [hterm,
        show conjSubgroup (wSub ⊥ V hV L ⊓ centralizer (L : Set G)) (m : G) =
            (wSub ⊥ V hV L ⊓ centralizer (L : Set G)).map
              (MulAut.conj (m : G)⁻¹).toMonoidHom from rfl]
      have hK := s16h_map_conj_eq_preTil D h hMs (m := (m : G)⁻¹) (D.M.inv_mem m.2)
      rw [hK]
      rcases hcases (actTil ⊥ V hV ⟨(m : G)⁻¹, hMs (D.M.inv_mem m.2)⟩)
          (actTil_mem_barSub ⊥ V hV (D.M.inv_mem m.2) (hMs (D.M.inv_mem m.2))) with hLb | hLb
      · rw [hLb, ← hZ₁eq]
        exact le_sup_left
      · rw [hLb, ← s16h_map_conj_eq_preTil D h hMs hxM]
        exact le_sup_right
    · refine sup_le ?_ ?_
      · have h1term : wSub ⊥ V hV (conjSubgroup L ((1 : D.M) : G)) ⊓
            centralizer (conjSubgroup L ((1 : D.M) : G) : Set G) =
            wSub ⊥ V hV L ⊓ centralizer (L : Set G) := by
          simp [conjSubgroup_one]
        rw [← h1term]
        exact le_iSup (fun m : D.M => wSub ⊥ V hV (conjSubgroup L (m : G)) ⊓
          centralizer (conjSubgroup L (m : G) : Set G)) ⟨1, D.M.one_mem⟩
      · have hxterm : wSub ⊥ V hV (conjSubgroup L ((⟨x, hxM⟩ : D.M) : G)⁻¹) ⊓
            centralizer (conjSubgroup L ((⟨x, hxM⟩ : D.M) : G)⁻¹ : Set G) =
            (wSub ⊥ V hV L ⊓ centralizer (L : Set G)).map
              (MulAut.conj x).toMonoidHom := by
          rw [show (wSub ⊥ V hV L ⊓ centralizer (L : Set G)).map
              (MulAut.conj x).toMonoidHom =
              conjSubgroup (wSub ⊥ V hV L ⊓ centralizer (L : Set G)) x⁻¹ from by
            rw [conjSubgroup, inv_inv]]
          rw [E3.conjSubgroup_inf, E3.conjSubgroup_centralizer,
            ← s15_Infra_wSub_conjSubgroup ⊥ V L hV ((stabTil ⊥ V).inv_mem (hMs hxM))]
        rw [← hxterm]
        exact le_iSup (fun m : D.M => wSub ⊥ V hV (conjSubgroup L (m : G)) ⊓
          centralizer (conjSubgroup L (m : G) : Set G)) ⟨(⟨x, hxM⟩ : D.M)⁻¹, D.M.inv_mem hxM⟩
  · intro m hm
    have hKZ₁ := s16h_map_conj_eq_preTil D h hMs hm
    have hKZ₁x := s16h_map_conj_eq_preTil D h hMs hxM
    have hKZ₁xm := s16h_Z₁x_map_conj_eq_preTil D h hMs hxM hm
    rcases hperm.2 (actTil ⊥ V hV ⟨m, hMs hm⟩)
        (actTil_mem_barSub ⊥ V hV hm (hMs hm)) with ⟨hLb, hLb2⟩ | ⟨hLb, hLb2⟩
    · left
      exact ⟨by rw [hKZ₁, hLb, ← hZ₁eq], by rw [hKZ₁xm, hLb2, ← hKZ₁x]⟩
    · right
      exact ⟨by rw [hKZ₁, hLb, ← hKZ₁x], by rw [hKZ₁xm, hLb2, ← hZ₁eq]⟩

theorem s16h_mixedCfg_of_s_two (D : Data G) {V L : Subgroup G} (h : Setting16 D ⊥ V L)
    (hs : s15 D.M ⊥ V h.hyp151.isElemAbelian L = 2) {x : G} (hxM : x ∈ D.M)
    (hx : x ∉ nBar D.M ⊥ V h.hyp151.isElemAbelian L)
    (hne : (wSub ⊥ V h.hyp151.isElemAbelian L ⊓ centralizer (L : Set G)).map
        (MulAut.conj x).toMonoidHom ≠
      wSub ⊥ V h.hyp151.isElemAbelian L ⊓ centralizer (L : Set G)) :
    s16h_MixedCfg D.M (nBar D.M ⊥ V h.hyp151.isElemAbelian L)
      (v1Sub D.M ⊥ V h.hyp151.isElemAbelian L)
      (wSub ⊥ V h.hyp151.isElemAbelian L ⊓ centralizer (L : Set G)) x := by
  have hV := h.hyp151.isElemAbelian
  have h125 := h.hyp151.hyp125
  have hMs : D.M ≤ stabTil ⊥ V :=
    le_stabTil h125.pairFacts.le_normalizer h125.pairFacts.le_normalizer₀
  have h3 := s16h_v1Sub_eq_sup_of_s_two D h hs hxM hx
  refine ⟨hxM, ?_, ?_, ?_, h3.1, h3.2, ?_, ?_⟩
  · exact (s15_Infra_v1Sub_le h125 hV).trans h125.pairFacts.le_M
  · exact s15_Infra_le_normalizer_v1Sub h125 hV
  · exact hV.mono (s15_Infra_v1Sub_le h125 hV)
  · intro g hg
    exact ((mem_preBarSub D.M ⊥ V hV _).1 hg).1
  · intro m hm
    constructor
    · intro hmn
      obtain ⟨-, hstab, hnorm⟩ := (mem_preBarSub D.M ⊥ V hV _).1 hmn
      have heq : (⟨m, hstab⟩ : stabTil ⊥ V) = ⟨m, hMs hm⟩ := Subtype.ext rfl
      rw [heq] at hnorm
      have hLb : (lBar ⊥ V hV L).map (MulAut.conj (actTil ⊥ V hV ⟨m, hMs hm⟩)).toMonoidHom =
          lBar ⊥ V hV L := by
        simpa [lBar] using (Subgroup.mem_normalizer_iff_map_conj_eq).1 hnorm
      rw [s16h_map_conj_eq_preTil D h hMs hm, hLb]
      exact (s16h_preTil_Z₁_eq D h hMs).symm
    · intro hfix
      by_contra hmn
      have hxbar_mem : actTil ⊥ V hV ⟨x, hMs hxM⟩ ∈ Mbar D.M ⊥ V hV :=
        actTil_mem_barSub ⊥ V hV hxM (hMs hxM)
      have hxne : (lBar ⊥ V hV L).map (MulAut.conj (actTil ⊥ V hV ⟨x, hMs hxM⟩)).toMonoidHom ≠
          lBar ⊥ V hV L := by
        intro hcon
        exact hx (by
          rw [nBar, mem_preBarSub]
          exact ⟨hxM, hMs hxM, (Subgroup.mem_normalizer_iff_map_conj_eq).2 hcon⟩)
      have hs' : Set.ncard {X : Subgroup (MulAut (Vtil ⊥ V hV)) |
          ∃ φ ∈ Mbar D.M ⊥ V hV, X = (lBar ⊥ V hV L).map
            (MulAut.conj φ).toMonoidHom} = 2 := by
        simpa [s15, lBar] using hs
      have hcases := ((c23a_two_conj hs').2 (actTil ⊥ V hV ⟨x, hMs hxM⟩) hxbar_mem hxne).1
      rcases hcases (actTil ⊥ V hV ⟨m, hMs hm⟩)
          (actTil_mem_barSub ⊥ V hV hm (hMs hm)) with hLb | hLb
      · exact hmn (by
          rw [nBar, mem_preBarSub]
          exact ⟨hm, hMs hm, (Subgroup.mem_normalizer_iff_map_conj_eq).2 hLb⟩)
      · exact hne (by
          have hz : (wSub ⊥ V hV L ⊓ centralizer (L : Set G)).map
                (MulAut.conj m).toMonoidHom =
              (wSub ⊥ V hV L ⊓ centralizer (L : Set G)).map
                (MulAut.conj x).toMonoidHom := by
            rw [s16h_map_conj_eq_preTil D h hMs hm,
              s16h_map_conj_eq_preTil D h hMs hxM, hLb]
          exact hz.symm.trans hfix)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
