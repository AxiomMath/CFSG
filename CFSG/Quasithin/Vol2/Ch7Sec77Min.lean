module

public import CFSG.Quasithin.Vol2.Ch7Prop772
public import CFSG.Quasithin.Background.HSL3S77Span

public section

namespace CFSG.Quasithin.H13.Sec77

open CFSG.Open CFSG.Quasithin.E3 CFSG.Quasithin.H CFSG.Quasithin.H.S77
  CFSG.Quasithin.H.SL3Pair CFSG.LieType.BorelTits CFSG.QuasithinUnique
open scoped IsMulCommutative Matrix

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem act_zero_of_dstab {g : SL32} (hg : (g : Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ *ᵥ e1 = e1)
    {x : Vec} (hx : x 0 = 0) : (act g x) 0 = 0 := by
  have h1 := congrFun hg 1
  have h2 := congrFun hg 2
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.transpose_apply] at h1 h2
  simp only [act, Matrix.mulVec, dotProduct, Fin.sum_univ_three, hx]
  simp_all

@[expose] def pairVmI : Subgroup (PairMod (ZMod 2)) := pairVm ⊓ V₁ (ZMod 2)

@[expose] def pairVmD : Subgroup (PairMod (ZMod 2)) := pairVm ⊓ V₂ (ZMod 2)

theorem mem_pairVmI {p : PairMod (ZMod 2)} : p ∈ pairVmI ↔ (vp p).1 0 = 0 ∧ (vp p).2 = 0 := by
  rw [pairVmI, Subgroup.mem_inf, mem_pairVm, mem_V₁_iff_vp]
  constructor
  · rintro ⟨⟨h1, -⟩, h2⟩
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨⟨h1, ?_⟩, h2⟩
    rw [h2]
    rfl

theorem mem_pairVmD {p : PairMod (ZMod 2)} : p ∈ pairVmD ↔ (vp p).1 = 0 ∧ (vp p).2 0 = 0 := by
  rw [pairVmD, Subgroup.mem_inf, mem_pairVm, mem_V₂]
  constructor
  · rintro ⟨⟨-, h2⟩, h1⟩
    refine ⟨?_, h2⟩
    change Multiplicative.toAdd p.1 = 0
    rw [h1, toAdd_one]
  · rintro ⟨h1, h2⟩
    refine ⟨⟨?_, h2⟩, Multiplicative.toAdd.injective (h1.trans toAdd_one.symm)⟩
    rw [h1]
    rfl

theorem rho_mem_pairVmI {g : SL32}
    (hgd : (g : Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ *ᵥ e1 = e1) {p : PairMod (ZMod 2)}
    (hp : p ∈ pairVmI) : SL3One.rho g p ∈ pairVmI := by
  rw [mem_pairVmI] at hp ⊢
  rw [vp_rho]
  refine ⟨act_zero_of_dstab hgd hp.1, ?_⟩
  change dact g (vp p).2 = 0
  rw [hp.2]
  simp only [dact, Matrix.mulVec_zero]

theorem rho_mem_pairVmD {g : SL32} (hg1 : act g e1 = e1) {p : PairMod (ZMod 2)}
    (hp : p ∈ pairVmD) : SL3One.rho g p ∈ pairVmD := by
  rw [mem_pairVmD] at hp ⊢
  rw [vp_rho]
  refine ⟨?_, dact_zero_of_stab hg1 hp.2⟩
  change act g (vp p).1 = 0
  rw [hp.1]
  simp only [act, Matrix.mulVec_zero]

theorem pairVmI_ne_bot : pairVmI ≠ ⊥ := by
  intro h
  have hp : pv (![0, 1, 0], 0) ∈ pairVmI := mem_pairVmI.mpr ⟨rfl, rfl⟩
  rw [h, Subgroup.mem_bot] at hp
  have := congrArg (fun q : PairMod (ZMod 2) => (vp q).1 1) hp
  exact absurd this (by decide)

theorem pairVmD_ne_bot : pairVmD ≠ ⊥ := by
  intro h
  have hp : pv (0, ![0, 1, 0]) ∈ pairVmD := mem_pairVmD.mpr ⟨rfl, rfl⟩
  rw [h, Subgroup.mem_bot] at hp
  have := congrArg (fun q : PairMod (ZMod 2) => (vp q).2 1) hp
  exact absurd this (by decide)

theorem mem_closure_six {x y : Vec} (hx0 : x 0 = 0) (hx : x ≠ 0) (hy0 : y 0 = 0) (hy : y ≠ 0)
    (p : PairMod (ZMod 2)) :
    p ∈ Subgroup.closure ({a1, b1, pv (x, 0), SL3One.rho th0 (pv (x, 0)), pv (0, y),
      SL3One.rho th0 (pv (0, y))} : Set (PairMod (ZMod 2))) := by
  set C := Subgroup.closure ({a1, b1, pv (x, 0), SL3One.rho th0 (pv (x, 0)), pv (0, y),
      SL3One.rho th0 (pv (0, y))} : Set (PairMod (ZMod 2))) with hC
  have hsmul : ∀ (c : ZMod 2) (q : Vec × Vec), pv q ∈ C → pv (c • q) ∈ C := by
    intro c q hq
    rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c with rfl | rfl
    · rw [zero_smul]
      exact C.one_mem
    · rwa [one_smul]
  have hadd : ∀ q r : Vec × Vec, pv q ∈ C → pv r ∈ C → pv (q + r) ∈ C := fun q r hq hr =>
    C.mul_mem hq hr
  have h1 : pv (x, 0) ∈ C := Subgroup.subset_closure (by simp)
  have h2 : pv (act th0 x, 0) ∈ C := by
    have h : SL3One.rho th0 (pv (x, 0)) = pv (act th0 x, 0) := by
      apply vp_injective
      rw [vp_rho]
      refine Prod.ext rfl ?_
      change dact th0 0 = 0
      simp only [dact, Matrix.mulVec_zero]
    rw [← h]
    exact Subgroup.subset_closure (by simp)
  have h3 : pv (0, y) ∈ C := Subgroup.subset_closure (by simp)
  have h4 : pv (0, th0d *ᵥ y) ∈ C := by
    have h : SL3One.rho th0 (pv (0, y)) = pv (0, th0d *ᵥ y) := by
      apply vp_injective
      rw [vp_rho, dact_th0]
      refine Prod.ext ?_ rfl
      change act th0 0 = 0
      simp only [act, Matrix.mulVec_zero]
    rw [← h]
    exact Subgroup.subset_closure (by simp)
  have ha1 : pv (e1, 0) ∈ C := Subgroup.subset_closure (by simp)
  have hb1 : pv (0, e1) ∈ C := Subgroup.subset_closure (by simp)
  set z := (vp p).1
  set w := (vp p).2
  have hz : (z - z 0 • e1) 0 = 0 := by simp
  have hw : (w - w 0 • e1) 0 = 0 := by simp
  obtain ⟨a, b, hab⟩ := span_th0 x hx0 hx _ hz
  obtain ⟨c, d, hcd⟩ := span_th0d y hy0 hy _ hw
  have hp : p = pv ((z 0 • (e1, 0) + (a • (x, 0) + b • (act th0 x, 0))) +
      (w 0 • (0, e1) + (c • (0, y) + d • (0, th0d *ᵥ y)))) := by
    apply vp_injective
    change (z, w) = _
    refine Prod.ext ?_ ?_
    · change z = (z 0 • e1 + (a • x + b • act th0 x)) + (w 0 • 0 + (c • 0 + d • 0))
      rw [← hab]
      simp only [smul_zero, add_zero]
      exact (add_sub_cancel _ _).symm
    · change w = (z 0 • 0 + (a • 0 + b • 0)) + (w 0 • e1 + (c • y + d • (th0d *ᵥ y)))
      rw [← hcd]
      simp only [smul_zero, add_zero, zero_add]
      exact (add_sub_cancel _ _).symm
  rw [hp]
  exact hadd _ _ (hadd _ _ (hsmul _ _ ha1) (hadd _ _ (hsmul _ _ h1) (hsmul _ _ h2)))
    (hadd _ _ (hsmul _ _ hb1) (hadd _ _ (hsmul _ _ h3) (hsmul _ _ h4)))

omit [Finite G] in
theorem map_conj_V0 {V : Subgroup G} {m : G} (hm : m ∈ Subgroup.normalizer (V : Set G))
    (θ : G) : (V ⊓ Subgroup.centralizer ({θ} : Set G)).map (MulAut.conj m).toMonoidHom =
      V ⊓ Subgroup.centralizer ({m * θ * m⁻¹} : Set G) := by
  have hV : V.map (MulAut.conj m).toMonoidHom = V := Subgroup.mem_normalizer_iff_map_conj_eq.mp hm
  rw [Subgroup.map_inf _ _ _ (MulAut.conj m).injective, ← centralizer_conj_eq, hV]

namespace Setup

variable (S : Setup T L I)
include S

variable {S} {e : IntMod (fsuV T I) S.hV ≃* PairMod (ZMod 2)} {θ : G}

variable (S) in
@[expose] def vecSub (e : IntMod (fsuV T I) S.hV ≃* PairMod (ZMod 2))
    (P : Subgroup (PairMod (ZMod 2))) : Subgroup G :=
  (P.comap e.toMonoidHom).map (E3.valHom S.hV)

theorem mem_vecSub_iff {P : Subgroup (PairMod (ZMod 2))} {w : G} :
    w ∈ S.vecSub e P ↔ ∃ p ∈ P, S.vec e p = w := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨e x, hx, ?_⟩
    rw [vec, MulEquiv.symm_apply_apply]
  · rintro ⟨p, hp, rfl⟩
    exact ⟨e.symm p, by simpa using hp, rfl⟩

theorem vecSub_le (P : Subgroup (PairMod (ZMod 2))) : S.vecSub e P ≤ fsuV T I :=
  E3.map_valHom_le S.hV _

theorem vecSub_ne_bot {P : Subgroup (PairMod (ZMod 2))} (hP : P ≠ ⊥) : S.vecSub e P ≠ ⊥ := by
  intro h
  apply hP
  rw [eq_bot_iff]
  intro p hp
  have h1 : S.vec e p ∈ S.vecSub e P := mem_vecSub_iff.mpr ⟨p, hp, rfl⟩
  rw [h, Subgroup.mem_bot] at h1
  rw [Subgroup.mem_bot]
  exact vec_injective (h1.trans vec_one.symm)

theorem le_normalizer_vecSub {P : Subgroup (PairMod (ZMod 2))} {X : Subgroup G}
    (hXN : X ≤ Subgroup.normalizer (fsuV T I : Set G))
    (hP : ∀ x (hx : x ∈ X), ∀ p ∈ P, congrHom e (convI S.hV ⟨x, hXN hx⟩) p ∈ P) :
    X ≤ Subgroup.normalizer (S.vecSub e P : Set G) := by
  intro x hx
  have key : ∀ y (hy : y ∈ X), ∀ w ∈ S.vecSub e P, y * w * y⁻¹ ∈ S.vecSub e P := by
    intro y hy w hw
    obtain ⟨p, hp, rfl⟩ := mem_vecSub_iff.mp hw
    rw [conj_vec (hXN hy)]
    exact mem_vecSub_iff.mpr ⟨_, hP y hy p hp, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro w
  refine ⟨key x hx w, fun h => ?_⟩
  have := key x⁻¹ (X.inv_mem hx) _ h
  simpa [mul_assoc] using this

theorem exists_stab0 (hc : S.Coord θ e) {x : G} (hxM : x ∈ fsuM T L)
    (hx : x ∈ Subgroup.centralizer ((fsuV T I ⊓ Subgroup.centralizer ({θ} : Set G) :
      Subgroup G) : Set G)) :
    ∃ g : SL32, act g e1 = e1 ∧ (g : Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ *ᵥ e1 = e1 ∧
      congrHom e (convI S.hV ⟨x, S.hMN hxM⟩) = SL3One.rho g := by
  have hx1 : x ∈ Subgroup.centralizer ({S.vec e a1} : Set G) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr (vec_a1_mem_V0 hc)) hx
  have hxb : x ∈ Subgroup.centralizer ({S.vec e b1} : Set G) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr (vec_b1_mem_V0 hc)) hx
  obtain ⟨g, hg1, hg⟩ := exists_stab hc hxM hx1
  refine ⟨g, hg1, ?_, hg⟩
  have hb := (mem_centralizer_vec_iff (S.hMN hxM) b1).mp hxb
  rw [hg] at hb
  have h1 := congrArg (fun p => Multiplicative.toAdd p.2) hb
  change Multiplicative.toAdd (SL3One.rho g b1).2 = e1 at h1
  rw [rho_snd] at h1
  exact (dact_eq_iff g e1).mp h1

theorem exists_coord_sylow0 (h3104 : Stmt3_2_10_four) {θ : G} (hθL : θ ∈ L)
    (hθ3 : θ ^ 3 ∈ Subgroup.centralizer (fsuV T I : Set G))
    (hθ1 : θ ∉ Subgroup.centralizer (fsuV T I : Set G)) :
    ∃ m ∈ fsuM T L, ∃ θ' e', S.Coord θ' e' ∧
      fsuV T I ⊓ Subgroup.centralizer ({θ'} : Set G) =
        (fsuV T I ⊓ Subgroup.centralizer ({θ} : Set G)).map (MulAut.conj m).toMonoidHom ∧
      IsSylowTwoOf (T ⊓ Subgroup.centralizer ((fsuV T I ⊓ Subgroup.centralizer ({θ'} : Set G) :
        Subgroup G) : Set G)) (Subgroup.centralizer ((fsuV T I ⊓
        Subgroup.centralizer ({θ'} : Set G) : Subgroup G) : Set G)) ∧
      IsSylowTwoOf (T ⊓ Subgroup.centralizer ((fsuV T I ⊓ Subgroup.centralizer ({θ'} : Set G) :
        Subgroup G) : Set G)) (fsuM T L ⊓ Subgroup.centralizer ((fsuV T I ⊓
        Subgroup.centralizer ({θ'} : Set G) : Subgroup G) : Set G)) := by
  obtain ⟨m, hmM, hG, hM⟩ := S.exists_conj_sylow h3104
    (inf_le_left : fsuV T I ⊓ Subgroup.centralizer ({θ} : Set G) ≤ fsuV T I)
  have hmN := S.hMN hmM
  rw [map_conj_V0 hmN] at hG hM
  have hθ₁L : m * θ * m⁻¹ ∈ L :=
    (Subgroup.mem_normalizer_iff.mp (S.fsuM_le_normalizer_L hmM) θ).mp hθL
  have hθ₁3 : (m * θ * m⁻¹) ^ 3 ∈ Subgroup.centralizer (fsuV T I : Set G) := by
    rw [conj_pow]
    exact conj_mem_centralizer hmN hθ3
  have hθ₁1 : m * θ * m⁻¹ ∉ Subgroup.centralizer (fsuV T I : Set G) := by
    intro h
    apply hθ1
    have h2 := conj_mem_centralizer (Subgroup.inv_mem _ hmN) h
    have e2 : m⁻¹ * (m * θ * m⁻¹) * m⁻¹⁻¹ = θ := by group
    rwa [e2] at h2
  obtain ⟨θ', e', hc, hfix⟩ := S.exists_coord hθ₁L hθ₁3 hθ₁1
  have heq : fsuV T I ⊓ Subgroup.centralizer ({θ'} : Set G) =
      fsuV T I ⊓ Subgroup.centralizer ({m * θ * m⁻¹} : Set G) := by
    ext w
    constructor
    · rintro ⟨hw, h⟩
      exact ⟨hw, (hfix w hw).mp h⟩
    · rintro ⟨hw, h⟩
      exact ⟨hw, (hfix w hw).mpr h⟩
  refine ⟨m, hmM, θ', e', hc, heq.trans (map_conj_V0 hmN θ).symm, ?_, ?_⟩
  · rw [heq]
    exact hG
  · rw [heq]
    exact hM

theorem centralizer_V0_le_of_sylow (h3104 : Stmt3_2_10_four)
    (h : ∀ θ' e', S.Coord θ' e' →
      IsSylowTwoOf (T ⊓ Subgroup.centralizer ((fsuV T I ⊓ Subgroup.centralizer ({θ'} : Set G) :
        Subgroup G) : Set G)) (Subgroup.centralizer ((fsuV T I ⊓
        Subgroup.centralizer ({θ'} : Set G) : Subgroup G) : Set G)) →
      IsSylowTwoOf (T ⊓ Subgroup.centralizer ((fsuV T I ⊓ Subgroup.centralizer ({θ'} : Set G) :
        Subgroup G) : Set G)) (fsuM T L ⊓ Subgroup.centralizer ((fsuV T I ⊓
        Subgroup.centralizer ({θ'} : Set G) : Subgroup G) : Set G)) →
      Subgroup.centralizer ((fsuV T I ⊓ Subgroup.centralizer ({θ'} : Set G) : Subgroup G) :
        Set G) ≤ fsuM T L)
    {θ : G} (hθL : θ ∈ L) (hθ3 : θ ^ 3 ∈ Subgroup.centralizer (fsuV T I : Set G))
    (hθ1 : θ ∉ Subgroup.centralizer (fsuV T I : Set G)) :
    Subgroup.centralizer ((fsuV T I ⊓ Subgroup.centralizer ({θ} : Set G) : Subgroup G) :
      Set G) ≤ fsuM T L := by
  obtain ⟨m, hmM, θ', e', hc, heq, hG, hM⟩ := S.exists_coord_sylow0 h3104 hθL hθ3 hθ1
  have h1 := h θ' e' hc hG hM
  rw [heq, CFSG.QuasithinUnique.centralizer_map_equiv] at h1
  intro x hx
  have h2 : m * x * m⁻¹ ∈ fsuM T L := h1 ⟨x, hx, rfl⟩
  have h3 : x = m⁻¹ * (m * x * m⁻¹) * m := by group
  rw [h3]
  exact (fsuM T L).mul_mem ((fsuM T L).mul_mem ((fsuM T L).inv_mem hmM) h2) hmM

variable (S) in
structure MinConf (θ : G) (e : IntMod (fsuV T I) S.hV ≃* PairMod (ZMod 2)) (Vp H : Subgroup G) :
    Prop where
  conf : S.Conf θ e Vp H
  hVp : Vp = fsuV T I ⊓ Subgroup.centralizer ({θ} : Set G)
  not_le : ¬ H ≤ fsuM T L
  min : ∀ H' : Subgroup G, oTwoUpper (L ⊓ Subgroup.centralizer (Vp : Set G)) ⊔
      (T ⊓ Subgroup.centralizer (Vp : Set G)) ≤ H' → H' ≤ H → ¬ H' ≤ fsuM T L → H' = H

theorem exists_minConf (hc : S.Coord θ e) {Vp : Subgroup G}
    (hVp : Vp = fsuV T I ⊓ Subgroup.centralizer ({θ} : Set G))
    (hG : IsSylowTwoOf (T ⊓ Subgroup.centralizer (Vp : Set G)) (Subgroup.centralizer (Vp : Set G)))
    (hM : IsSylowTwoOf (T ⊓ Subgroup.centralizer (Vp : Set G))
      (fsuM T L ⊓ Subgroup.centralizer (Vp : Set G)))
    (hnot : ¬ Subgroup.centralizer (Vp : Set G) ≤ fsuM T L) : ∃ H, S.MinConf θ e Vp H := by
  have hLTC : oTwoUpper (L ⊓ Subgroup.centralizer (Vp : Set G)) ⊔
      (T ⊓ Subgroup.centralizer (Vp : Set G)) ≤ Subgroup.centralizer (Vp : Set G) :=
    sup_le ((oTwoUpper_le _).trans inf_le_right) inf_le_right
  obtain ⟨H, hH⟩ := (Set.toFinite {H : Subgroup G | oTwoUpper (L ⊓ Subgroup.centralizer
      (Vp : Set G)) ⊔ (T ⊓ Subgroup.centralizer (Vp : Set G)) ≤ H ∧
      H ≤ Subgroup.centralizer (Vp : Set G) ∧ ¬ H ≤ fsuM T L}).exists_minimal
    ⟨Subgroup.centralizer (Vp : Set G), hLTC, le_rfl, hnot⟩
  obtain ⟨hLH, hHG, hHM⟩ := hH.prop
  exact ⟨H, ⟨hc, Or.inl hVp, hG, hM, hLH, hHG⟩, hVp, hHM,
    fun H' h1 h2 h3 => hH.eq_of_le ⟨h1, h2.trans hHG, h3⟩ h2⟩

namespace MinConf

variable {Vp H : Subgroup G} (C : S.MinConf θ e Vp H)
include C

theorem not_thompsonJ_le (h3108 : Stmt3_2_10_eight) : ¬ thompsonJ H ≤ fsuM T L := by
  intro hJM
  apply C.not_le
  have hTp := C.conf.sylH
  have hJH : thompsonJ H ≤ H := thompsonJ_le_self H
  have hHJ : H ≤ Subgroup.normalizer ((thompsonJ H : Subgroup G) : Set G) := fun g hg =>
    GammaExtra.normalizer_le_normalizer_thompsonJ H (Subgroup.le_normalizer hg)
  have hJn : ((thompsonJ H).subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hJH).2 hHJ
  set Tp := T ⊓ Subgroup.centralizer (Vp : Set G) with hTpdef
  set R := Tp ⊓ thompsonJ H with hRdef
  have hR : IsSylowTwoOf R (thompsonJ H) :=
    RankOneRecog.isSylowTwoOf_inf_of_subnormal hTp hJH hJn.isSubnormal
  have hVp' : IsVplus T L I (fsuV T I) := Or.inr ⟨fun h => h.1 S.hL, rfl⟩
  have hJTp : thompsonJ T ≤ Tp := le_inf (thompsonJ_le_self T)
    (S.hJ.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr C.conf.vp_le_V)))
  have hJeq := (h3108 G T L I (fsuV T I) S.hyp.fsu hVp' S.hJ Tp hTp.2.1 hJTp).1
  have hJR : thompsonJ T ≤ R := le_inf hJTp (hJeq ▸ B6.thompsonJ_le_of_sylow hTp)
  have hNR := (h3108 G T L I (fsuV T I) S.hyp.fsu hVp' S.hJ R (hTp.2.1.to_le inf_le_left)
    hJR).2
  intro h hh
  have hRh : IsSylowTwoOf (R.map (MulAut.conj h).toMonoidHom) (thompsonJ H) := by
    have := isSylowTwoOf_map_of_injective (f := (MulAut.conj h).toMonoidHom)
      (MulAut.conj h).injective hR
    have hJh : (thompsonJ H).map (MulAut.conj h).toMonoidHom = thompsonJ H :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hHJ hh)
    rwa [hJh] at this
  obtain ⟨j, hj, hjR⟩ := A4.exists_conj_of_isSylowTwoOf hR hRh
  have hn : j⁻¹ * h ∈ Subgroup.normalizer (R : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have e1 : j⁻¹ * h * y * (j⁻¹ * h)⁻¹ = j⁻¹ * (h * y * h⁻¹) * j := by group
    rw [e1, ← hjR, Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
    have e2 : h⁻¹ * (h * y * h⁻¹) * h = y := by group
    rw [e2]
  have h4 : h = j * (j⁻¹ * h) := by group
  rw [h4]
  exact (fsuM T L).mul_mem (hJM hj) (hNR hn)

theorem isTwoReduced_U (hF : CharTwo H) :
    IsElemAbelian 2 (conjClosure (quasithinOmegaOneCenter (T ⊓ Subgroup.centralizer
      (Vp : Set G))) H) ∧
    IsTwoReducedIn H (conjClosure (quasithinOmegaOneCenter (T ⊓ Subgroup.centralizer
      (Vp : Set G))) H) := by
  obtain ⟨-, hel, hred⟩ := conjClosure_isTwoReducedIn_of_charTwo C.conf.sylH hF le_rfl
  exact ⟨hel, hred⟩

theorem exists_omegaOneCenter {W : Subgroup G} (hWV : W ≤ fsuV T I) (hW : W ≠ ⊥)
    (hWN : T ⊓ Subgroup.centralizer (Vp : Set G) ≤ Subgroup.normalizer (W : Set G)) :
    ∃ w ∈ W, w ≠ 1 ∧ w ∈ quasithinOmegaOneCenter (T ⊓ Subgroup.centralizer (Vp : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Tp := T ⊓ Subgroup.centralizer (Vp : Set G) with hTpdef
  have hWTp : W ≤ Tp := hWV.trans C.conf.V_le_tp
  have hnil : Group.IsNilpotent ↥Tp := IsPGroup.isNilpotent C.conf.sylH.2.1
  have hn : (W.subgroupOf Tp).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hWTp).2 hWN
  have hne : W.subgroupOf Tp ≠ ⊥ := by
    intro h
    apply hW
    rw [eq_bot_iff]
    intro w hw
    have h1 : (⟨w, hWTp hw⟩ : ↥Tp) ∈ W.subgroupOf Tp := Subgroup.mem_subgroupOf.mpr hw
    rw [h, Subgroup.mem_bot] at h1
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val h1
  obtain ⟨⟨x, hxW, hxZ⟩, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
  refine ⟨(x : G), Subgroup.mem_subgroupOf.mp hxW, fun h => hx1 (Subtype.ext (Subtype.ext h)), ?_⟩
  apply Subgroup.subset_closure
  refine ⟨⟨x.2, Subgroup.mem_centralizer_iff.mpr fun t ht => ?_⟩, ?_⟩
  · exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hxZ ⟨t, ht⟩)
  · exact S.hV.2 _ (hWV (Subgroup.mem_subgroupOf.mp hxW))

theorem V_le_U : fsuV T I ≤ conjClosure (quasithinOmegaOneCenter (T ⊓ Subgroup.centralizer
    (Vp : Set G))) H := by
  have hc := C.conf.hc
  set Tp := T ⊓ Subgroup.centralizer (Vp : Set G) with hTpdef
  set U := conjClosure (quasithinOmegaOneCenter Tp) H with hU
  have hTpM : Tp ≤ fsuM T L := inf_le_left.trans S.T_le_fsuM
  have hTpN : Tp ≤ Subgroup.normalizer (fsuV T I : Set G) := hTpM.trans S.hMN
  have hTpC : ∀ t ∈ Tp, t ∈ Subgroup.centralizer ((fsuV T I ⊓
      Subgroup.centralizer ({θ} : Set G) : Subgroup G) : Set G) := by
    intro t ht
    rw [← C.hVp]
    exact ht.2
  have hNI : Tp ≤ Subgroup.normalizer (S.vecSub e pairVmI : Set G) :=
    le_normalizer_vecSub hTpN fun t ht p hp => by
      obtain ⟨g, -, hgd, hg⟩ := exists_stab0 hc (hTpM ht) (hTpC t ht)
      have hg' : congrHom e (convI S.hV ⟨t, hTpN ht⟩) = SL3One.rho g := hg
      rw [hg']
      exact rho_mem_pairVmI hgd hp
  have hND : Tp ≤ Subgroup.normalizer (S.vecSub e pairVmD : Set G) :=
    le_normalizer_vecSub hTpN fun t ht p hp => by
      obtain ⟨g, hg1, -, hg⟩ := exists_stab0 hc (hTpM ht) (hTpC t ht)
      have hg' : congrHom e (convI S.hV ⟨t, hTpN ht⟩) = SL3One.rho g := hg
      rw [hg']
      exact rho_mem_pairVmD hg1 hp
  obtain ⟨w₁, hw₁W, hw₁1, hw₁Z⟩ :=
    C.exists_omegaOneCenter (vecSub_le _) (vecSub_ne_bot pairVmI_ne_bot) hNI
  obtain ⟨w₂, hw₂W, hw₂1, hw₂Z⟩ :=
    C.exists_omegaOneCenter (vecSub_le _) (vecSub_ne_bot pairVmD_ne_bot) hND
  obtain ⟨p₁, hp₁, rfl⟩ := mem_vecSub_iff.mp hw₁W
  obtain ⟨p₂, hp₂, rfl⟩ := mem_vecSub_iff.mp hw₂W
  rw [mem_pairVmI] at hp₁
  rw [mem_pairVmD] at hp₂
  have hp₁' : p₁ = pv ((vp p₁).1, 0) := vp_injective (Prod.ext rfl hp₁.2)
  have hp₂' : p₂ = pv (0, (vp p₂).2) := vp_injective (Prod.ext hp₂.1 rfl)
  have hx : (vp p₁).1 ≠ 0 := by
    intro h
    apply hw₁1
    rw [hp₁', h]
    exact vec_one
  have hy : (vp p₂).2 ≠ 0 := by
    intro h
    apply hw₂1
    rw [hp₂', h]
    exact vec_one
  have hθU : θ ∈ Subgroup.normalizer (U : Set G) := le_normalizer_conjClosure _ H C.conf.th_mem_H
  have hZU : ∀ z ∈ quasithinOmegaOneCenter Tp, z ∈ U := fun z hz => le_conjClosure _ _ hz
  have hconjU : ∀ q, S.vec e q ∈ U → S.vec e (SL3One.rho th0 q) ∈ U := fun q hq => by
    rw [← conj_vec_th hc]
    exact (Subgroup.mem_normalizer_iff.mp hθU _).mp hq
  have hVpZ : ∀ v ∈ Vp, v ∈ quasithinOmegaOneCenter Tp := fun v hv => Subgroup.subset_closure
    ⟨⟨C.conf.V_le_tp (C.conf.vp_le_V hv), Subgroup.mem_centralizer_iff.mpr fun t ht =>
      (Subgroup.mem_centralizer_iff.mp ht.2 v hv).symm⟩, S.hV.2 v (C.conf.vp_le_V hv)⟩
  have ha1 : S.vec e a1 ∈ U := by
    refine hZU _ (hVpZ _ ?_)
    rw [C.hVp]
    exact vec_a1_mem_V0 hc
  have hb1 : S.vec e b1 ∈ U := by
    refine hZU _ (hVpZ _ ?_)
    rw [C.hVp]
    exact vec_b1_mem_V0 hc
  have h1 : S.vec e (pv ((vp p₁).1, 0)) ∈ U := by
    rw [← hp₁']
    exact hZU _ hw₁Z
  have h2 : S.vec e (pv (0, (vp p₂).2)) ∈ U := by
    rw [← hp₂']
    exact hZU _ hw₂Z
  have hU6 : ∀ q ∈ ({a1, b1, pv ((vp p₁).1, 0), SL3One.rho th0 (pv ((vp p₁).1, 0)),
      pv (0, (vp p₂).2), SL3One.rho th0 (pv (0, (vp p₂).2))} : Set (PairMod (ZMod 2))),
      S.vec e q ∈ U := by
    intro q hq
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ha1
    · exact hb1
    · exact h1
    · exact hconjU _ h1
    · exact h2
    · exact hconjU _ h2
  intro v hv
  obtain ⟨q, rfl⟩ := exists_vec (S := S) (e := e) hv
  have hq := mem_closure_six hp₁.1 hx hp₂.2 hy q
  set f : PairMod (ZMod 2) →* G := (E3.valHom S.hV).comp e.symm.toMonoidHom with hf
  have hfq : f q ∈ (Subgroup.closure ({a1, b1, pv ((vp p₁).1, 0),
      SL3One.rho th0 (pv ((vp p₁).1, 0)), pv (0, (vp p₂).2),
      SL3One.rho th0 (pv (0, (vp p₂).2))} : Set (PairMod (ZMod 2)))).map f := ⟨q, hq, rfl⟩
  rw [MonoidHom.map_closure] at hfq
  refine (Subgroup.closure_le U).mpr ?_ hfq
  rintro _ ⟨q', hq', rfl⟩
  exact hU6 q' hq'

theorem inf_centralizer_U_le :
    H ⊓ Subgroup.centralizer ((conjClosure (quasithinOmegaOneCenter (T ⊓
      Subgroup.centralizer (Vp : Set G))) H : Subgroup G) : Set G) ≤ fsuM T L := fun _ hx =>
  S.centralizer_le_fsuM (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr C.V_le_U) hx.2)

end MinConf

end Setup

end CFSG.Quasithin.H13.Sec77
