module

public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Gaschutz
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec3.HypA39AuxSchur
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec3.HypA39AuxSylow

public section

open CFSG.Open
open CFSG.SignalizerFunctorTheorem
open CFSG.SignalizerFunctorTheorem.McBride.Nonsolv
open scoped Pointwise commutatorElement

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Near

theorem exists_pGroup_le_of_not_dvd_index {G : Type*} [Group G] [Finite G] {r : ℕ}
    (hr : r.Prime) {M : Subgroup G} (h : ¬ r ∣ M.index) :
    ∃ P : Subgroup G, P ≤ M ∧ IsPGroup r P ∧ ¬ r ∣ P.index := by
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨Q⟩ : Nonempty (Sylow r ↥M) := inferInstance
  refine ⟨(Q : Subgroup ↥M).map M.subtype, Subgroup.map_subtype_le _,
    Q.isPGroup'.map M.subtype, ?_⟩
  rw [Subgroup.index_map_subtype]
  exact fun hd => (hr.dvd_mul.mp hd).elim Q.not_dvd_index h

variable {Γ : Type u} [Group Γ]

theorem relIndex_inf_qpre {L K₁ : Subgroup Γ} (hK₁n : K₁ ≤ AChief.nrm L)
    (M' : Subgroup (AChief.QG L)) :
    (K₁ ⊓ SolQuot.qpre L M').relIndex K₁ = M'.relIndex (AChief.qimg L K₁) := by
  have h : (K₁ ⊓ SolQuot.qpre L M').subgroupOf K₁ =
      (M'.subgroupOf (AChief.qimg L K₁)).comap (SolQuot.qres L K₁ hK₁n) := by
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_comap, SolQuot.coe_qres]
    constructor
    · rintro ⟨-, hx⟩
      exact (SolQuot.mem_qpre_iff.mp hx).2
    · intro hx
      exact ⟨x.2, SolQuot.mem_qpre_iff.mpr ⟨hK₁n x.2, hx⟩⟩
  rw [Subgroup.relIndex, Subgroup.relIndex, h,
    Subgroup.index_comap_of_surjective _ (SolQuot.qres_surjective hK₁n)]

theorem commutator_mul_mul_of_central {Y : Type*} [Group Y] {n₁ n₂ d₁ d₂ : Y}
    (h₁ : ∀ g, g * n₁ = n₁ * g) (h₂ : ∀ g, g * n₂ = n₂ * g) :
    ⁅n₁ * d₁, n₂ * d₂⁆ = ⁅d₁, d₂⁆ := by
  have e1 : n₁ * (d₁ * (n₂ * d₂) * d₁⁻¹) * n₁⁻¹ = d₁ * (n₂ * d₂) * d₁⁻¹ := by
    rw [mul_inv_eq_iff_eq_mul, ← h₁]
  have e2 : n₂ * (d₁ * d₂ * d₁⁻¹ * d₂⁻¹) * n₂⁻¹ = d₁ * d₂ * d₁⁻¹ * d₂⁻¹ := by
    rw [mul_inv_eq_iff_eq_mul, ← h₂]
  calc ⁅n₁ * d₁, n₂ * d₂⁆ = n₁ * (d₁ * (n₂ * d₂) * d₁⁻¹) * n₁⁻¹ * d₂⁻¹ * n₂⁻¹ := by
        simp only [commutatorElement_def]
        group
    _ = d₁ * (n₂ * d₂) * d₁⁻¹ * d₂⁻¹ * n₂⁻¹ := by rw [e1]
    _ = (d₁ * n₂) * d₂ * d₁⁻¹ * d₂⁻¹ * n₂⁻¹ := by group
    _ = (n₂ * d₁) * d₂ * d₁⁻¹ * d₂⁻¹ * n₂⁻¹ := by rw [h₂ d₁]
    _ = n₂ * (d₁ * d₂ * d₁⁻¹ * d₂⁻¹) * n₂⁻¹ := by group
    _ = d₁ * d₂ * d₁⁻¹ * d₂⁻¹ := e2
    _ = ⁅d₁, d₂⁆ := rfl

theorem commutator_le_of_central_complement {Y : Type*} [Group Y] {N D' : Subgroup Y}
    (hN : N ≤ Subgroup.center Y) (h₂ : N ⊔ D' = ⊤) : ⁅(⊤ : Subgroup Y), ⊤⁆ ≤ D' := by
  have hc : ∀ n ∈ N, ∀ g : Y, g * n = n * g := fun n hn g => Subgroup.mem_center_iff.mp (hN hn) g
  have hND : N ≤ Subgroup.normalizer (D' : Set Y) := admits_of_centralizes fun n hn x _ =>
    (hc n hn x).symm
  refine Subgroup.commutator_le.mpr fun x _ y _ => ?_
  have hx : x ∈ N ⊔ D' := h₂ ▸ Subgroup.mem_top x
  have hy : y ∈ N ⊔ D' := h₂ ▸ Subgroup.mem_top y
  obtain ⟨n₁, hn₁, d₁, hd₁, rfl⟩ := (mem_sup_iff_mul_of_le_normalizer hND).mp hx
  obtain ⟨n₂, hn₂, d₂, hd₂, rfl⟩ := (mem_sup_iff_mul_of_le_normalizer hND).mp hy
  rw [commutator_mul_mul_of_central (hc n₁ hn₁) (hc n₂ hn₂)]
  exact mul_mem (mul_mem (mul_mem hd₁ hd₂) (inv_mem hd₁)) (inv_mem hd₂)

theorem qimg_le_centralizer_of_commute {N X Y : Subgroup Γ}
    (h : ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x) :
    AChief.qimg N X ≤ Subgroup.centralizer (AChief.qimg N Y : Set (AChief.QG N)) := by
  intro g hg
  obtain ⟨x, hx, rfl⟩ := (AChief.mem_qimg_iff N X g).mp hg
  refine Subgroup.mem_centralizer_iff.mpr fun b hb => ?_
  obtain ⟨y, hy, rfl⟩ := (AChief.mem_qimg_iff N Y b).mp hb
  rw [← map_mul, ← map_mul]
  exact congrArg (AChief.qmap N) (Subtype.ext (h x hx y hy).symm)

variable {p : ℕ} {H A D D₁ D₂ E L R K₁ : Subgroup Γ}

namespace Red

theorem false_of_K1Data
    [Finite Γ] (c : Red p H A D D₁ D₂ E L R)
    (d : K1Data H A D₁ E L R K₁) : False := by
  classical
  obtain ⟨r, hr, hrL⟩ := c.exists_prime
  have hnc := c.exists_noncomm d
  obtain ⟨-, J₂, hJ₂, hmodel₂⟩ := c.schur_model d hnc hr hrL
  have hK₁H := c.K₁_le_H d
  have hLK₁ := L_le_K₁ d
  have hGn : H ⊔ A ≤ AChief.nrm L := c.hLG
  have hK₁n : K₁ ≤ AChief.nrm L := hK₁H.trans (le_sup_left.trans hGn)
  have hAn : A ≤ AChief.nrm L := le_sup_right.trans hGn
  have hDn : D ≤ AChief.nrm L := (c.D_le.trans le_sup_left).trans hGn
  have hAK₁ : Admits A K₁ := le_sup_right.trans d.admits
  have hAS := c.qK_isASimple d hnc
  have hss : IsSemisimple (AChief.qimg L K₁) := AChief.isDirectProduct_simpleComponents hAS
  have hnear : NearASolvable p (AChief.qimg L A) (AChief.qimg L K₁) :=
    HypAAux.nearASolvable_qimg c.h15.prime c.h15.a1_elemAbelian hAK₁ hK₁n hAn
      (nearASolvable_of_le c.h15.prime c.h15.a1_near hK₁H hAK₁)
  have hne : AChief.qimg L K₁ ≠ ⊥ := fun h0 =>
    absurd ((SolQuot.qimg_eq_bot_iff hK₁n).mp h0) (not_le_of_gt d.L_lt)
  have hSA : SemisimpleAction p (AChief.qimg L A) (AChief.qimg L K₁) :=
    { prime := c.h15.prime
      odd := c.h15.odd
      elemAbelian := AChief.isElemAbelian_qimg c.h15.a1_elemAbelian
      admits := AChief.qimg_le_normalizer hAK₁
      nearPSolvable := hnear.1
      solvable_cen := hnear.2
      semisimple := hss
      ne_bot := hne }
  have hmodel : ∀ J ∈ lcal (AChief.qimg L K₁),
      (r = 2 ∧ Nonempty (↥J ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 3 p))) ∨
      (r = 3 ∧ Nonempty (↥J ≃* PSU3 2 p)) := by
    intro J hJ
    rw [hss.lcal_eq] at hJ hJ₂
    obtain ⟨g, -, hJeq⟩ := hAS.components_transitive hJ₂ hJ
    let e : ↥J ≃* ↥J₂ := (MulEquiv.subgroupCongr hJeq).trans
      (Subgroup.equivMapOfInjective J₂ (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).symm
    rcases hmodel₂ with ⟨h2, h⟩ | ⟨h3, h⟩
    · exact Or.inl ⟨h2, h.map fun f => e.trans f⟩
    · exact Or.inr ⟨h3, h.map fun f => e.trans f⟩
  have hidx : ¬ r ∣ (mOf (AChief.qimg L A) (AChief.qimg L K₁)).relIndex (AChief.qimg L K₁) :=
    hSA.not_dvd_relIndex_mOf_of_model hr hmodel
  set Mb : Subgroup (AChief.QG L) := mOf (AChief.qimg L A) (AChief.qimg L K₁) with hMb
  have hDAN : AChief.qimg L D ⊔ AChief.qimg L A ≤
      Subgroup.normalizer ((AChief.qimg L K₁ : Subgroup (AChief.QG L)) : Set (AChief.QG L)) :=
    sup_le (AChief.qimg_le_normalizer ((c.D_le.trans le_sup_left).trans d.admits))
      (AChief.qimg_le_normalizer hAK₁)
  have hDAC : AChief.qimg L D ⊔ AChief.qimg L A ≤
      Subgroup.centralizer
        ((AChief.qimg L A : Subgroup (AChief.QG L)) : Set (AChief.QG L)) :=
    sup_le (qimg_le_centralizer_of_commute fun x hx y hy =>
      (Subgroup.mem_centralizer_iff.mp (c.h15.D_le_centralizer hx) y hy).symm)
      (qimg_le_centralizer_of_commute fun x hx y hy =>
        (commute_of_mem c.h15.a1_elemAbelian.1 hx hy).eq)
  have hMbadm : Admits (AChief.qimg L D ⊔ AChief.qimg L A) Mb :=
    admits_of_forall_conj fun g hg x hx => hSA.conj_mem_mOf (hDAN hg) (hDAC hg) hx
  have hqDA : AChief.qimg L (D ⊔ A) = AChief.qimg L D ⊔ AChief.qimg L A :=
    SolQuot.qimg_sup hDn hAn
  set M₁ : Subgroup Γ := K₁ ⊓ SolQuot.qpre L Mb with hM₁
  have hM₁K₁ : M₁ ≤ K₁ := inf_le_left
  have hM₁adm : Admits (D ⊔ A) M₁ := (d.admits.mono_left c.DA_le_G).inf
    (HypAAux.admits_qpre (sup_le hDn hAn) (by rw [hqDA]; exact hMbadm))
  set S' : Subgroup Γ := M₁ ⊔ D with hS'
  have hS'H : S' ≤ H := sup_le (hM₁K₁.trans hK₁H) c.D_le
  have hS'adm : Admits (D ⊔ A) S' := hM₁adm.sup c.admits_D
  have hS'ne : S' ⊔ A ≠ H ⊔ A := by
    intro heq
    have hK₁S' : K₁ ≤ S' := fun x hx => c.h15.inf_sup_le_of_le hS'H (hS'adm.mono_left le_sup_right)
      (Subgroup.mem_inf.mpr ⟨hK₁H hx, heq ▸ Subgroup.mem_sup_left (hK₁H hx)⟩)
    have hK₁D : K₁ ⊓ D ≤ M₁ := by
      intro x hx
      obtain ⟨hxK, hxD⟩ := Subgroup.mem_inf.mp hx
      refine Subgroup.mem_inf.mpr ⟨hxK, SolQuot.mem_qpre_iff.mpr ⟨hK₁n hxK, ?_⟩⟩
      have hqx : AChief.qmap L ⟨x, hK₁n hxK⟩ ∈ AChief.qimg L K₁ :=
        (AChief.mem_qimg_iff L K₁ _).mpr ⟨_, hxK, rfl⟩
      have hqC : AChief.qmap L ⟨x, hK₁n hxK⟩ ∈
          Subgroup.centralizer
            ((AChief.qimg L A : Subgroup (AChief.QG L)) : Set (AChief.QG L)) := by
        refine Subgroup.mem_centralizer_iff.mpr fun b hb => ?_
        obtain ⟨a, ha, rfl⟩ := (AChief.mem_qimg_iff L A b).mp hb
        rw [← map_mul, ← map_mul]
        refine congrArg (AChief.qmap L) (Subtype.ext ?_)
        exact (Subgroup.mem_centralizer_iff.mp (c.h15.D_le_centralizer hxD) a ha)
      have := hSA.cenIn_le_kProd (Subgroup.mem_inf.mpr ⟨hqx, hqC⟩)
      rwa [← hSA.mOf_eq_kProd] at this
    have hK₁M₁ : K₁ ≤ M₁ := by
      have h1 : K₁ ≤ M₁ ⊔ (K₁ ⊓ D) :=
        (le_inf le_rfl hK₁S').trans (inf_sup_le_sup_inf' hM₁K₁ (le_sup_left.trans hM₁adm))
      exact h1.trans (sup_le le_rfl hK₁D)
    have hKbMb : AChief.qimg L K₁ ≤ Mb :=
      (SolQuot.qimg_mono hK₁M₁).trans ((SolQuot.qimg_le_iff (hM₁K₁.trans hK₁n)).mpr inf_le_right)
    obtain ⟨-, -, hMsol⟩ := (thm210b hSA).1
    have := hMsol
    exact c.qK_not_solvable d hnc
      (Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hKbMb))
  have h6S' := c.restrict S' hS'H le_sup_right hS'adm hS'ne
  have hLS' : L ≤ S' := c.L_le_D.trans le_sup_right
  have hRD'' : S' ⊓ R ⊓ D = D₁ := le_antisymm
    ((inf_le_inf_right D inf_le_right).trans c.hRD.le)
    (le_inf (le_inf (c.D₁_le_D.trans le_sup_right) c.D₁_le_R) c.D₁_le_D)
  obtain ⟨B, hBR, -, hBD, hRB⟩ := c.hasB_of_hypA6 h6S' inf_le_left (le_inf hLS' c.L_le_R)
    inf_le_right (hS'adm.inf c.admits_R) hRD''
  have hD₂B : D₂ ≤ B := by
    rw [← hBD]
    exact inf_le_left
  have hBR' : B ≤ R := hBR.trans inf_le_right
  have hBL : B ≤ Subgroup.normalizer (L : Set Γ) :=
    admits_of_centralizes fun b hb l hl => c.R_cen b (hBR' hb) l hl
  have hS'R : S' ⊓ R = B ⊔ L := by
    rw [hRB, c.hD₁, ← sup_assoc, sup_eq_left.mpr hD₂B]
  have hidx1 : ¬ r ∣ (M₁.subgroupOf K₁).index := by
    have h2 : (M₁.subgroupOf K₁).index = Mb.relIndex (AChief.qimg L K₁) :=
      relIndex_inf_qpre hK₁n Mb
    rw [h2]
    exact hidx
  obtain ⟨P', hP'M, hP'p, hP'idx⟩ := exists_pGroup_le_of_not_dvd_index hr hidx1
  have : Fact r.Prime := ⟨hr⟩
  let Psyl : Sylow r ↥K₁ := hP'p.toSylow hP'idx
  have hLK₁N : (L.subgroupOf K₁).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hLK₁]
    intro h k hh hk
    exact c.hLG.conj_mem (Subgroup.mem_sup_left (hK₁H hk)) hh
  have hLr : IsPGroup r ↥(L.subgroupOf K₁) := fun x => ⟨1, by
    apply Subtype.ext
    apply Subtype.ext
    simpa using hrL x (Subgroup.mem_subgroupOf.mp x.2)⟩
  have hL'P : L.subgroupOf K₁ ≤ P' := hLr.le_sylow_of_normal Psyl
  set P : Subgroup Γ := P'.map K₁.subtype with hP
  have hPM₁ : P ≤ M₁ :=
    (Subgroup.map_mono hP'M).trans (Subgroup.map_subgroupOf_eq_of_le hM₁K₁).le
  have hPK₁ : P ≤ K₁ := Subgroup.map_subtype_le _
  have hLP : L ≤ P := by
    have h1 := Subgroup.map_mono (f := K₁.subtype) hL'P
    rwa [Subgroup.map_subgroupOf_eq_of_le hLK₁] at h1
  have hPBL : P ≤ L ⊔ (P ⊓ B) := by
    have hPle : P ≤ S' ⊓ R := le_inf (hPM₁.trans le_sup_left) (hPK₁.trans d.le_R)
    rw [hS'R, sup_comm] at hPle
    exact (le_inf le_rfl hPle).trans (inf_sup_le_sup_inf' hLP hBL)
  have hLB : L ⊓ B = ⊥ := by
    refine le_bot_iff.mp fun x hx => ?_
    obtain ⟨hxL, hxB⟩ := Subgroup.mem_inf.mp hx
    have : x ∈ D₂ ⊓ L := Subgroup.mem_inf.mpr
      ⟨by rw [← hBD]; exact Subgroup.mem_inf.mpr ⟨hxB, c.L_le_D hxL⟩, hxL⟩
    rwa [c.hD₂L] at this
  have hLC : L ⊓ (P ⊓ B) = ⊥ := le_bot_iff.mp ((inf_le_inf_left L inf_le_right).trans hLB.le)
  have hLCP : L ⊔ (P ⊓ B) = P := le_antisymm (sup_le hLP inf_le_left) hPBL
  have : IsMulCommutative ↥(L.subgroupOf K₁) := ⟨⟨fun a b => Subtype.ext (Subtype.ext
    (c.L_comm a (Subgroup.mem_subgroupOf.mp a.2) b (Subgroup.mem_subgroupOf.mp b.2)))⟩⟩
  have hNK : L.subgroupOf K₁ ⊓ (P ⊓ B).subgroupOf K₁ = ⊥ := by
    have : (L ⊓ (P ⊓ B)).subgroupOf K₁ = L.subgroupOf K₁ ⊓ (P ⊓ B).subgroupOf K₁ :=
      Subgroup.comap_inf _ _ _
    rw [← this, hLC, Subgroup.bot_subgroupOf]
  have hsup : L.subgroupOf K₁ ⊔ (P ⊓ B).subgroupOf K₁ = (Psyl : Subgroup ↥K₁) := by
    rw [← Subgroup.subgroupOf_sup hLK₁ (inf_le_left.trans hPK₁), hLCP]
    exact Subgroup.comap_map_eq_self_of_injective K₁.subtype_injective P'
  obtain ⟨D', hD'1, hD'2⟩ := McBride.exists_complement_of_sylow_complement hr hLr Psyl hL'P hNK
    hsup
  have hcenL : L.subgroupOf K₁ ≤ Subgroup.center ↥K₁ := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (c.K₁_cen d g g.2 x (Subgroup.mem_subgroupOf.mp hx))
  have hcomm := commutator_le_of_central_complement hcenL hD'2
  have hperf : ⁅(⊤ : Subgroup ↥K₁), ⊤⁆ = ⊤ :=
    (Subgroup.isPerfect_iff.mpr (c.commutator_eq d hnc)).commutator_eq_top
  have hD'top : D' = ⊤ := top_le_iff.mp (hperf ▸ hcomm)
  have hL1 : L.subgroupOf K₁ ≠ ⊥ := by
    intro h0
    apply c.hL0
    rw [← Subgroup.map_subgroupOf_eq_of_le hLK₁, h0, Subgroup.map_bot]
  apply hL1
  rw [← inf_top_eq (L.subgroupOf K₁), ← hD'top]
  exact hD'1

theorem false'
    [Finite Γ] (c : Red p H A D D₁ D₂ E L R) : False := by
  obtain ⟨K₁, d⟩ := c.exists_K1Data
  exact c.false_of_K1Data d

end Red

theorem L39.false_of_not_hypA6
    [Finite Γ] {p : ℕ} {H A D D₁ D₂ E : Subgroup Γ}
    (c : L39 p H A D D₁ D₂ E) (h : ¬ HypA6 H A D D₁ D₂) : False := by
  obtain ⟨H', L, R, r⟩ := exists_red c h
  exact r.false'

end CFSG.SignalizerFunctorTheorem.McBride.Near
