module

public import CFSG.Quasithin.Recognition.Kleidman.F53Hss36.Claim5
public import CFSG.Quasithin.Recognition.Kleidman.F53Hss36.LemmaI

public section

namespace CFSG.Quasithin.Kleidman.F53Hss36

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod CFSG.Quasithin.F53 CFSG.Quasithin.F53.Stellmacher
open CFSG.Quasithin.CosetGeom CFSG.Quasithin.EmptyFaithful.Stellmacher
open scoped commutatorElement

set_option linter.unusedSectionVars false

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem relIndex_sup_eq_inf {X L : Subgroup G} (hX : X ≤ Subgroup.normalizer (L : Set G)) :
    L.relIndex (X ⊔ L) = (X ⊓ L).relIndex X := by
  let NG : Subgroup G := Subgroup.normalizer (L : Set G)
  have hKleNG : L ≤ NG := Subgroup.le_normalizer
  have hXLleNG : X ⊔ L ≤ NG := sup_le hX hKleNG
  let : (L.subgroupOf NG).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (H := L) (K := NG) hKleNG).2 le_rfl
  calc L.relIndex (X ⊔ L)
      = (L.subgroupOf NG).relIndex ((X ⊔ L).subgroupOf NG) :=
        (Subgroup.relIndex_subgroupOf (H := L) (K := X ⊔ L) (L := NG) hXLleNG).symm
    _ = (L.subgroupOf NG).relIndex ((X.subgroupOf NG) ⊔ (L.subgroupOf NG)) := by
        rw [Subgroup.subgroupOf_sup (A := X) (A' := L) (B := NG) hX hKleNG]
    _ = (L.subgroupOf NG).relIndex (X.subgroupOf NG) :=
        Subgroup.relIndex_sup_right (H := X.subgroupOf NG) (K := L.subgroupOf NG)
    _ = ((X.subgroupOf NG) ⊓ (L.subgroupOf NG)).relIndex (X.subgroupOf NG) :=
        (Subgroup.inf_relIndex_left (H := X.subgroupOf NG) (K := L.subgroupOf NG)).symm
    _ = ((X ⊓ L).subgroupOf NG).relIndex (X.subgroupOf NG) := by
        rw [show (X.subgroupOf NG) ⊓ (L.subgroupOf NG) = (X ⊓ L).subgroupOf NG by
          ext x; simp [Subgroup.mem_subgroupOf]]
    _ = (X ⊓ L).relIndex X :=
        Subgroup.relIndex_subgroupOf (H := X ⊓ L) (K := X) (L := NG) hX

theorem card_comm_zpowers_eq {E : Subgroup G} (hE : IsElemAbelian 2 E) {y : G}
    (hy : y ∈ Subgroup.normalizer (E : Set G)) (hy2 : y ^ 2 = 1) :
    Nat.card ↥⁅E, Subgroup.zpowers y⁆ = (Subgroup.centralizer {y} ⊓ E).relIndex E := by
  let φ : ↥E →* ↥E :=
    { toFun := fun v => ⟨⁅(v : G), y⁆, comm_mem_of_normalizer hy v.2⟩
      map_one' := by ext; simp
      map_mul' := by
        intro v w
        ext
        simp only [Subgroup.coe_mul]
        rw [commutator_mul_of_abelian hE hy v.2 w.2]
        exact elemAbelian_comm hE (comm_mem_of_normalizer hy w.2) (comm_mem_of_normalizer hy v.2) }
  have hker : φ.ker = (Subgroup.centralizer {y} ⊓ E).subgroupOf E := by
    ext v
    simp only [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      Subgroup.mem_centralizer_iff, Set.mem_singleton_iff, forall_eq]
    constructor
    · intro h
      have h' : ⁅(v : G), y⁆ = 1 := congrArg Subtype.val h
      exact ⟨((commutatorElement_eq_one_iff_mul_comm).mp h').symm, v.2⟩
    · rintro ⟨h, -⟩
      ext
      exact (commutatorElement_eq_one_iff_mul_comm).mpr h.symm
  have h1 := Subgroup.index_ker φ
  unfold Subgroup.relIndex
  rw [← hker, h1]
  have hcomm : ⁅E, Subgroup.zpowers y⁆ = φ.range.map E.subtype := by
    apply le_antisymm
    · rw [Subgroup.commutator_le]
      intro v hv g hg
      obtain ⟨k, hk, rfl⟩ := (mem_zpowers_iff_of_pow_eq_one hy2 (by norm_num)).mp hg
      interval_cases k
      · simp
      · simp only [pow_one]
        exact ⟨⟨⁅v, y⁆, comm_mem_of_normalizer hy hv⟩, ⟨⟨v, hv⟩, rfl⟩, rfl⟩
    · rintro _ ⟨_, ⟨v, rfl⟩, rfl⟩
      exact Subgroup.commutator_mem_commutator v.2 (Subgroup.mem_zpowers y)
  rw [hcomm]
  exact Subgroup.card_map_of_injective (Subgroup.subtype_injective E)

theorem comm_zpowers_le_centralizer {E : Subgroup G} (hE : IsElemAbelian 2 E) {y : G}
    (hy : y ∈ Subgroup.normalizer (E : Set G)) (hy2 : y ^ 2 = 1) :
    ⁅E, Subgroup.zpowers y⁆ ≤ Subgroup.centralizer {y} := by
  rw [Subgroup.commutator_le]
  intro v hv g hg
  obtain ⟨k, hk, rfl⟩ := (mem_zpowers_iff_of_pow_eq_one hy2 (by norm_num)).mp hg
  interval_cases k
  · simp
  · simp only [pow_one]
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    have hyy : h * h = 1 := by simpa [pow_two] using hy2
    have hyi : h⁻¹ = h := inv_eq_of_mul_eq_one_left hyy
    have hgE : ⁅v, h⁆ ∈ E := comm_mem_of_normalizer hy hv
    have hg2 : ⁅v, h⁆ * ⁅v, h⁆ = 1 := by simpa [pow_two] using hE.2 _ hgE
    have h1 : h * ⁅v, h⁆ * h⁻¹ = ⁅v, h⁆⁻¹ := by
      simp only [commutatorElement_def, hyi, mul_inv_rev, inv_inv, mul_assoc]
      rw [hyy, mul_one]
    have h2 : ⁅v, h⁆⁻¹ = ⁅v, h⁆ := inv_eq_of_mul_eq_one_left hg2
    rw [h2] at h1
    calc h * ⁅v, h⁆ = h * ⁅v, h⁆ * h⁻¹ * h := by group
      _ = ⁅v, h⁆ * h := by rw [h1]

theorem sup_eq_centralizer_of_card {V C R : Subgroup G} {y : G}
    (hCV : C ≤ V) (hRN : R ≤ Subgroup.normalizer (C : Set G)) (hR4 : Nat.card R = 4)
    (hRC : R ⊓ C = ⊥) (hVC : C.relIndex V = 16)
    (hcent4 : (Subgroup.centralizer {y} ⊓ V).relIndex V = 4)
    (hle : R ⊔ C ≤ Subgroup.centralizer {y} ⊓ V) : R ⊔ C = Subgroup.centralizer {y} ⊓ V := by
  have h1 := Subgroup.relIndex_mul_card (H := C) (K := R ⊔ C)
  rw [inf_of_le_left le_sup_right, relIndex_sup_eq_inf hRN, hRC, Subgroup.relIndex_bot_left,
    hR4] at h1
  have h2 := Subgroup.relIndex_mul_card (H := C) (K := V)
  rw [inf_of_le_left hCV, hVC] at h2
  have h3 := Subgroup.relIndex_mul_card (H := Subgroup.centralizer {y} ⊓ V) (K := V)
  rw [inf_of_le_left inf_le_right, hcent4] at h3
  exact Subgroup.eq_of_le_of_card_ge hle (by omega)

omit [Finite G] in
theorem Iv_smul_conj (g : ↥(H ⊔ M)) (ν : Geo H M) : Iv (g • ν) = conjSub (g : G) (Iv ν) := by
  ext x
  simp only [Iv, Subgroup.mem_iInf, mem_conjSub]
  constructor
  · intro h δ hδ
    have h1 : g • δ ∈ nbrs (g • ν) := (smul_adj g).mpr hδ
    have := h _ h1
    rw [Vn_smul, mem_conjSub] at this
    exact this
  · intro h δ hδ
    obtain ⟨δ', rfl⟩ : ∃ δ', δ = g • δ' := ⟨g⁻¹ • δ, by simp⟩
    have hδ' : δ' ∈ nbrs ν := (smul_adj g).mp hδ
    rw [Vn_smul, mem_conjSub]
    exact h _ hδ'

namespace Ctx

variable {α β α' : Geo H M} (C : Ctx H M S α β α')

include C

theorem card_Iv_eq_of_nbrs {β' ν μ : Geo H M} (hν : ν ∈ nbrs β') (hμ : μ ∈ nbrs β') :
    Nat.card (Iv ν) = Nat.card (Iv μ) := by
  obtain ⟨g, -, hg⟩ := stab_transitive_on_nbrs hμ hν
  rw [← hg, Iv_smul_conj, card_conjSub]

theorem card_Vn_eq {δ δ' : Geo H M} (h : vtype δ = vtype δ') :
    Nat.card (Vn δ) = Nat.card (Vn δ') := by
  obtain ⟨g, rfl⟩ := exists_smul_of_vtype_eq (δ := δ) (δ' := δ') h
  rw [Vn_smul, card_conjSub]

theorem relIndex_Cv_Vn {δ : Geo H M} (hδ : vtype δ = false) :
    (F53B3.Cv δ).relIndex (Vn δ) = 16 :=
  (C.isNatSec hδ).relIndex_eq

theorem relIndex_Iv_Vn_le_four (hZ : Zv α' ≤ Vn β) {ν : Geo H M} (hν : ν ∈ nbrs β) :
    (Iv ν).relIndex (Vn β) ≤ 4 := by
  obtain ⟨μ, hμ, μ1, hμ1, hne, h4⟩ := C.exists_arc_index_le_four hZ
  have hvμ : vtype μ = true := vtype_true_of_mem_nbrs_false hμ C.vtype_beta
  have hvμ1 : vtype μ1 = false := vtype_false_of_mem_nbrs_true hμ1 hvμ
  have e1 := Subgroup.relIndex_mul_card (H := Iv μ) (K := Vn μ1)
  rw [inf_of_le_left (Iv_le_Vn hμ1)] at e1
  have e2 := Subgroup.relIndex_mul_card (H := Iv ν) (K := Vn β)
  rw [inf_of_le_left (Iv_le_Vn (mem_nbrs_comm hν))] at e2
  have e3 := C.card_Vn_eq (δ := μ1) (δ' := β) (by rw [hvμ1, C.vtype_beta])
  have e4 := C.card_Iv_eq_of_nbrs hν hμ
  rw [e4] at e2
  have hpos : 0 < Nat.card (Iv μ) := Nat.card_pos
  have : (Iv ν).relIndex (Vn β) = (Iv μ).relIndex (Vn μ1) := by
    apply Nat.eq_of_mul_eq_mul_right hpos
    rw [e2, e1, e3]
  omega

theorem Cv_le_Zv_and_centralizer_le (hZ : Zv α' ≤ Vn β) {y : G} (hy : y ∈ Vn α')
    (hyQ : y ∉ Qv β) :
    F53B3.Cv β ≤ Zv β ∧
      Subgroup.centralizer {y} ⊓ Vn β ≤ ⁅Vn β, Subgroup.zpowers y⁆ ⊔ F53B3.Cv β := by
  set P := critPathOf C.hc with hP
  have hb5 := C.hb5
  have hν : P.p 2 ∈ nbrs β := by
    have := P.isGeodesic.mem_nbrs_succ (i := 1) (by omega)
    rwa [P.p_one] at this
  have hν1 : P.p 3 ∈ nbrs (P.p 2) := P.isGeodesic.mem_nbrs_succ (i := 2) (by omega)
  have hvν : vtype (P.p 2) = true := vtype_true_of_mem_nbrs_false hν C.vtype_beta
  have hvν1 : vtype (P.p 3) = false := vtype_false_of_mem_nbrs_true hν1 hvν
  have hVab : IsElemAbelian 2 (Vn β) := isElemAbelian_Vn C.hA C.hb3 β
  have hy2 : y ^ 2 = 1 := (isElemAbelian_Vn C.hA C.hb3 α').2 y hy
  have hys : y ∈ stab β := C.Vn_alpha'_le_stab hy
  have hyN : y ∈ Subgroup.normalizer (Vn β : Set G) := stab_le_normalizer_Vn β hys
  set R := ⁅Vn β, Subgroup.zpowers y⁆ with hR
  set Cb := F53B3.Cv β with hCb
  have hCV : Cb ≤ Vn β := inf_le_left
  have hRV : R ≤ Vn β := comm_le_of_le_normalizer ((Subgroup.zpowers_le).mpr hyN)
  have hVst : Vn β ≤ stab β :=
    (C.Vn_le_Qv_self C.vtype_beta).trans (CFSG.Quasithin.F53B3.N37.Qv_le_stab_self β)
  have hstabN := CFSG.Quasithin.F53B3.N37.stab_le_normalizer_Cv (H := H) (M := M) β
  have hRN : R ≤ Subgroup.normalizer (Cb : Set G) := (hRV.trans hVst).trans hstabN
  have hcard : Nat.card R = (Subgroup.centralizer {y} ⊓ Vn β).relIndex (Vn β) :=
    card_comm_zpowers_eq hVab hyN hy2
  have hT1 := C.four_le_relIndex_commSec C.vtype_beta hys hyQ
  have hsup : commSec (Subgroup.zpowers y) Cb (Vn β) = R ⊔ Cb := rfl
  rw [hsup, relIndex_sup_eq_inf hRN] at hT1
  have hR4' : 4 ≤ Nat.card R := by
    have := Subgroup.relIndex_mul_card (H := R ⊓ Cb) (K := R)
    rw [inf_of_le_left inf_le_left] at this
    have h2 := Nat.le_of_dvd Nat.card_pos (Subgroup.relIndex_dvd_card (R ⊓ Cb) R)
    omega
  have hVst' := C.relIndex_Iv_Vn_le_four hZ hν
  have hIcent : Iv (P.p 2) ≤ Subgroup.centralizer {y} ⊓ Vn β := by
    refine le_inf ?_ (Iv_le_Vn (mem_nbrs_comm hν))
    intro z hz
    have hz1 : z ∈ Vn (P.p 3) := Iv_le_Vn hν1 hz
    have hd : dist (P.p 3) α' + 3 ≤ bMin H M := by
      have := P.dist_of_le (i := 3) (j := bMin H M) (by omega) le_rfl
      rw [P.p_b] at this
      omega
    have := C.comm_Vn_Vn (δ := P.p 3) (δ' := α') C.vtype_alpha' hd
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    have := Subgroup.commutator_mem_commutator hz1 hy
    rw [‹⁅Vn (P.p 3), Vn α'⁆ = ⊥›, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
    exact this.symm
  have hle4 : (Subgroup.centralizer {y} ⊓ Vn β).relIndex (Vn β) ≤ 4 :=
    (Subgroup.relIndex_le_of_le_left hIcent (relIndex_ne_zero' _ _)).trans hVst'
  have hm4 : Nat.card R = 4 := by omega
  have hcent4 : (Subgroup.centralizer {y} ⊓ Vn β).relIndex (Vn β) = 4 := by omega
  have hRC : R ⊓ Cb = ⊥ := by
    have h1 := Subgroup.relIndex_mul_card (H := R ⊓ Cb) (K := R)
    rw [inf_of_le_left inf_le_left, hm4] at h1
    have hpos : 0 < Nat.card ↥(R ⊓ Cb) := Nat.card_pos
    have h3 : (R ⊓ Cb).relIndex R * 1 ≤ (R ⊓ Cb).relIndex R * Nat.card ↥(R ⊓ Cb) :=
      Nat.mul_le_mul_left _ hpos
    have hr : (R ⊓ Cb).relIndex R = 4 := by omega
    rw [hr] at h1
    have h2 : Nat.card ↥(R ⊓ Cb) = 1 := by omega
    exact Subgroup.eq_bot_of_card_eq _ h2
  have hCcent : Cb ≤ Subgroup.centralizer {y} := by
    intro c hc
    have h1 : ⁅c, y⁆ ∈ R := Subgroup.commutator_mem_commutator (hCV hc) (Subgroup.mem_zpowers y)
    have h2 : ⁅c, y⁆ ∈ Cb := by
      have hyN' := hstabN hys
      have := (Subgroup.mem_normalizer_iff.mp hyN' c⁻¹).mp (Cb.inv_mem hc)
      have e : ⁅c, y⁆ = c * (y * c⁻¹ * y⁻¹) := by simp [commutatorElement_def, mul_assoc]
      rw [e]; exact Cb.mul_mem hc this
    have h3 : ⁅c, y⁆ = 1 := by
      have : ⁅c, y⁆ ∈ R ⊓ Cb := ⟨h1, h2⟩
      rw [hRC] at this
      exact this
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    exact (commutatorElement_eq_one_iff_mul_comm.mp h3).symm
  have hCle : Cb ≤ Subgroup.centralizer {y} ⊓ Vn β := le_inf hCcent hCV
  have hIeq : Iv (P.p 2) = Subgroup.centralizer {y} ⊓ Vn β := by
    have h1 := Subgroup.relIndex_mul_relIndex _ _ _ hIcent (inf_le_right :
      Subgroup.centralizer {y} ⊓ Vn β ≤ Vn β)
    rw [hcent4] at h1
    have hp2 : 0 < (Iv (P.p 2)).relIndex (Subgroup.centralizer {y} ⊓ Vn β) :=
      Nat.pos_of_ne_zero (relIndex_ne_zero' _ _)
    have h2 : (Iv (P.p 2)).relIndex (Subgroup.centralizer {y} ⊓ Vn β) = 1 := by omega
    exact le_antisymm hIcent (Subgroup.relIndex_eq_one.mp h2)
  have hCZ : Cb ≤ Zv β := by
    rw [← C.Iv_inf_Cv_eq hvν (mem_nbrs_comm hν)]
    exact le_inf (hIeq ▸ hCle) le_rfl
  refine ⟨hCZ, ?_⟩
  have hfull := sup_eq_centralizer_of_card hCV hRN hm4 hRC (C.relIndex_Cv_Vn C.vtype_beta) hcent4
    (sup_le (le_inf (comm_zpowers_le_centralizer hVab hyN hy2) hRV) hCle)
  exact hfull.symm.le

theorem not_Zv_le_Vn : ¬ Zv α' ≤ Vn β := by
  intro hZ
  have rel2 := C.relIndex_eq_two_of_Zv_le hZ
  have rel2' : (Qv β).relIndex (Vn α') = 2 := C.relIndex_Qv_Vn_eq.1.trans rel2
  obtain ⟨μ', C'⟩ := C.exists_mirror
  have hZ' : Zv β ≤ Vn α' := C'.Zv_le_Vn_of_relIndex_two rel2'
  obtain ⟨y, hyV, hyQ⟩ := Set.not_subset.mp C.not_Vn_beta_le_Qv_alpha'
  obtain ⟨hC, hcent⟩ := C'.Cv_le_Zv_and_centralizer_le hZ' hyV hyQ
  apply C.false_of_comm_Wnn_le
  rw [Subgroup.commutator_le]
  intro w hw v hv
  have hwst : w ∈ stab α' := C.Wnn_le_stab_alpha'_of_Zv_le hZ hw
  have hvst : v ∈ stab β := C.Vn_alpha'_le_stab hv
  have hc1 : ⁅w, v⁆ ∈ Vn α' := by
    have := (Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_Vn α' hwst) v).mp hv
    have e : ⁅w, v⁆ = (w * v * w⁻¹) * v⁻¹ := by simp [commutatorElement_def, mul_assoc]
    rw [e]; exact (Vn α').mul_mem this ((Vn α').inv_mem hv)
  have hc2 : ⁅w, v⁆ ∈ Wnn β := by
    have := (Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_Wnn β hvst) w⁻¹).mp
      ((Wnn β).inv_mem hw)
    have e : ⁅w, v⁆ = w * (v * w⁻¹ * v⁻¹) := by simp [commutatorElement_def, mul_assoc]
    rw [e]; exact (Wnn β).mul_mem hw this
  have hc3 : ⁅w, v⁆ ∈ Subgroup.centralizer (Vn β : Set G) :=
    C.Wnn_le_centralizer_Vn C.vtype_beta hc2
  have hc4 : ⁅w, v⁆ ∈ Subgroup.centralizer {y} :=
    Subgroup.mem_centralizer_iff.mpr fun h hh => by
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact Subgroup.mem_centralizer_iff.mp hc3 h hyV
  have h5 := hcent ⟨hc4, hc1⟩
  have hR : ⁅Vn α', Subgroup.zpowers y⁆ ≤ Vn β := by
    calc ⁅Vn α', Subgroup.zpowers y⁆ ≤ ⁅Vn α', Vn β⁆ :=
          Subgroup.commutator_mono le_rfl ((Subgroup.zpowers_le).mpr hyV)
      _ = ⁅Vn β, Vn α'⁆ := Subgroup.commutator_comm _ _
      _ ≤ Vn β := C.comm_Vn_Vn_le
  exact (sup_le hR (hC.trans hZ)) h5

theorem claim5_long : ¬ Zv α' ≤ Vn β ∧ (Qv α').relIndex (Vn β) = 4 ∧ (Qv β).relIndex (Vn α') = 4 ∧
    ¬ Zv β ≤ Vn α' := by
  have hn := C.not_Zv_le_Vn
  obtain ⟨μ', C'⟩ := C.exists_mirror
  obtain ⟨he, h24⟩ := C.relIndex_Qv_Vn_eq
  have h4 : (Qv α').relIndex (Vn β) = 4 := by
    by_contra hne
    rw [← he] at hne
    have h2 : (Qv β).relIndex (Vn α') = 2 := by omega
    exact hn (C.Zv_le_Vn_of_relIndex_two (he ▸ h2))
  exact ⟨hn, h4, he.trans h4, C'.not_Zv_le_Vn⟩

theorem claim5 : ¬ Zv α' ≤ Vn β ∧ (Qv α').relIndex (Vn β) = 4 ∧ ¬ Zv β ≤ Vn α' :=
  ⟨C.claim5_long.1, C.claim5_long.2.1, C.claim5_long.2.2.2⟩

end Ctx

end CFSG.Quasithin.Kleidman.F53Hss36
