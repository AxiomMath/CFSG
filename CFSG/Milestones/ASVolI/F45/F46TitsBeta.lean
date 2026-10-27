module

public import CFSG.Milestones.ASVolI.F45.F46TitsTransfer
public import CFSG.Milestones.ASVolI.F4Reductions
public import CFSG.Milestones.ASVolI.F45.F46TitsHyp

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.TitsGeo CFSG.Quasithin.F7
  CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion CFSG.ASVolI.ChF

section Dihedral

variable {X V : Type*} [Group X] [MulAction X V] {Γ : SimpleGraph V} [GraphAction X Γ]

theorem burnsideF46_dihedral {a : V} {lab : ZMod 5 → V} (A : AffLab X Γ a lab) {H : Subgroup X}
    (hHa : H ≤ MulAction.stabilizer X a) (hcard : Nat.card H = 10)
    (hfaith : ∀ g ∈ H, (∀ w, Γ.Adj a w → g • w = w) → g = 1) :
    Nonempty (H ≃* DihedralGroup 5) := by
  let σ : X → ZMod 5 → ZMod 5 := fun g i => Function.invFun lab (g • lab i)
  have hadj : ∀ g ∈ MulAction.stabilizer X a, ∀ i, Γ.Adj a (g • lab i) := fun g hg i => by
    have := (GraphAction.adj_smul g a (lab i)).mpr (A.adj i)
    rwa [MulAction.mem_stabilizer_iff.mp hg] at this
  have hσlab : ∀ g ∈ MulAction.stabilizer X a, ∀ i, lab (σ g i) = g • lab i := fun g hg i =>
    Function.invFun_eq (A.surj _ (hadj g hg i))
  have hσaff : ∀ g ∈ MulAction.stabilizer X a, ∀ i, σ g i = (σ g 1 - σ g 0) * i + σ g 0 := by
    intro g hg i
    obtain ⟨e, b, -, hab⟩ := A.aff g (MulAction.mem_stabilizer_iff.mp hg)
    have h : ∀ j, σ g j = e * j + b := fun j => A.inj (by rw [hσlab g hg j, hab])
    rw [h i, h 1, h 0]
    ring
  have hσmul : ∀ g ∈ MulAction.stabilizer X a, ∀ h ∈ MulAction.stabilizer X a, ∀ i,
      σ (g * h) i = σ g (σ h i) := by
    intro g hg h hh i
    apply A.inj
    rw [hσlab _ (mul_mem hg hh), hσlab g hg, hσlab h hh, mul_smul]
  have hσpow : ∀ g ∈ MulAction.stabilizer X a, ∀ (n : ℕ) i, σ (g ^ n) i = (σ g)^[n] i := by
    intro g hg n
    induction n with
    | zero =>
      intro i
      apply A.inj
      rw [pow_zero, hσlab _ (one_mem _), one_smul, Function.iterate_zero_apply]
    | succ n ih =>
      intro i
      rw [pow_succ', hσmul g hg _ (pow_mem hg n), ih, Function.iterate_succ_apply']
  let ε : X → ZMod 5 := fun g => σ g 1 - σ g 0
  let τ : X → ZMod 5 := fun g => σ g 0
  have hsign : ∀ g : H, ε g = 1 ∨ ε g = -1 := by
    intro g
    have hgx : (g : X) ∈ MulAction.stabilizer X a := hHa g.2
    have h10 : (g : X) ^ 10 = 1 := by
      have := pow_card_eq_one' (G := H) (x := g)
      rw [hcard] at this
      exact congrArg Subtype.val this
    have hfun : σ g = fun i => ε g * i + τ g := funext (hσaff g hgx)
    have hit : ∀ i, (fun i => ε g * i + τ g)^[10] i = i := by
      intro i
      rw [← hfun, ← hσpow g hgx 10 i, h10]
      apply A.inj
      rw [hσlab _ (one_mem _), one_smul]
    exact burnsideF45_aff_iter (ε g) (τ g) (hit 0) (hit 1)
  let f : H → DihedralGroup 5 := fun g => burnsideF45_dih (ε g) (τ g)
  have hf : ∀ g h : H, f (g * h) = f g * f h := by
    intro g h
    have hgx : (g : X) ∈ MulAction.stabilizer X a := hHa g.2
    have hhx : (h : X) ∈ MulAction.stabilizer X a := hHa h.2
    have e1 : ε (g * h : H) = ε g * ε h := by
      show σ (g * h) 1 - σ (g * h) 0 = (σ g 1 - σ g 0) * (σ h 1 - σ h 0)
      rw [hσmul _ hgx _ hhx, hσmul _ hgx _ hhx, hσaff g hgx (σ h 1), hσaff g hgx (σ h 0)]
      ring
    have e2 : τ (g * h : H) = ε g * τ h + τ g := by
      show σ (g * h) 0 = (σ g 1 - σ g 0) * σ h 0 + σ g 0
      rw [hσmul _ hgx _ hhx, hσaff g hgx (σ h 0)]
    show burnsideF45_dih (ε (g * h : H)) (τ (g * h : H)) =
      burnsideF45_dih (ε g) (τ g) * burnsideF45_dih (ε h) (τ h)
    rw [e1, e2, burnsideF45_dih_mul _ _ _ _ (hsign g) (hsign h)]
  let ρ : H →* DihedralGroup 5 := MonoidHom.mk' f hf
  have hinj : Function.Injective ρ := by
    intro g h hgh
    have hgx : (g : X) ∈ MulAction.stabilizer X a := hHa g.2
    have hhx : (h : X) ∈ MulAction.stabilizer X a := hHa h.2
    obtain ⟨he, hb⟩ := burnsideF45_dih_inj _ _ _ _ (hsign g) (hsign h) hgh
    have hσ : ∀ i, σ g i = σ h i := by
      intro i
      rw [hσaff g hgx, hσaff h hhx]
      exact congrArg₂ (fun a b => a * i + b) he hb
    have hk : ((h : X)⁻¹ * g) = 1 := by
      refine hfaith _ (mul_mem (inv_mem h.2) g.2) fun w hw => ?_
      obtain ⟨i, rfl⟩ := A.surj w hw
      rw [mul_smul, ← hσlab g hgx, hσ i, hσlab h hhx, inv_smul_smul]
    exact Subtype.ext (inv_mul_eq_one.mp hk).symm
  have hbij : Function.Bijective ρ :=
    hinj.bijective_of_nat_card_le (by rw [DihedralGroup.nat_card, hcard])
  exact ⟨MulEquiv.ofBijective ρ hbij⟩

end Dihedral

section Conj

variable {G : Type*} [Group G]

theorem burnsideF46_relIndex_conjSub (g : G) (H K : Subgroup G) :
    (conjSub g H).relIndex (conjSub g K) = H.relIndex K :=
  Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g).injective

end Conj

variable {α : RankTwoAmalgam.{0}} {Y : Type} [Group Y]

structure burnsideF46_Data (c : α.Completion Y) (Qx Ql : Subgroup c.G0) : Prop where
  hyp : TitsHyp c 6
  qOne : α.qOne = 4
  qTwo : α.qTwo = 2
  qn : QNormalized Qx Ql
  qx_le : Qx ≤ stv c c.xv
  ql_le : Ql ≤ stv c c.lv
  fix_x : ∀ w, c.graph.Adj c.xv w → Qx ≤ stv c w
  fix_l : ∀ w, c.graph.Adj c.lv w → Ql ≤ stv c w
  compl_l : ∀ q ∈ GPath.nbPaths c.graph c.lv 8,
    IsComplementIn q.stabPath Ql (stv c c.lv ⊓ stv c (q 1))
  idx_x : ∀ q ∈ GPath.nbPaths c.graph c.xv 8, (q.stabPath : Subgroup c.G0) ⊓ Qx = ⊥ ∧
    (Qx ⊔ q.stabPath).relIndex (stv c c.xv ⊓ stv c (q 1)) = 2
  card_x : ∀ q ∈ GPath.nbPaths c.graph c.xv 8, Nat.card (q.stabPath : Subgroup c.G0) = 2
  nontriv_x : ∀ q ∈ GPath.nbPaths c.graph c.xv 8,
    ∃ t ∈ (q.stabPath : Subgroup c.G0), ∃ w, c.graph.Adj c.xv w ∧ t • w ≠ w
  aff : ∃ lab : ZMod 5 → c.Γ, AffLab c.G0 c.graph c.xv lab
  two_orb : burnsideF46_TwoOrb c c.lv 8

namespace burnsideF46_Data

variable {c : α.Completion Y} {Qx Ql : Subgroup c.G0} (D : burnsideF46_Data c Qx Ql)

include D

theorem hval : ∀ v a b : c.Γ, ∃ w, c.graph.Adj v w ∧ w ≠ a ∧ w ≠ b := burnsideF46_hval D.hyp

theorem transPt {a : c.Γ} (ha : CosetGeom.vtype a = false) : c.PathTrans a 8 := D.hyp.transPt a ha

theorem transLn {a : c.Γ} (ha : CosetGeom.vtype a = true) : c.PathTrans a 7 := D.hyp.transLn a ha

theorem uniq {n : ℕ} (hn : n < 8) {a : c.Γ} {p : GPath c.graph n}
    (hp : p ∈ GPath.nbPaths c.graph a n) :
    c.graph.dist a (p n) = n ∧
      ∀ q : GPath c.graph n, q 0 = a → q n = p n → q.IsGeodesic → q = p :=
  burnsideF46_uniq_all D.hyp hn hp

theorem dist_m {a : c.Γ} {p : GPath c.graph 8} (hp : p ∈ GPath.nbPaths c.graph a 8) :
    c.graph.dist a (p 8) = 8 :=
  burnsideF46_dist_m_all D.hyp hp

theorem alt {a : c.Γ} {p : GPath c.graph 8} (hp : p ∈ GPath.nbPaths c.graph a 8) :
    (∀ t : GPath c.graph 8, t 0 = a → t 8 = p 8 → t.IsGeodesic → t = p) ∨ BijFirst c 8 a (p 8) :=
  burnsideF46_alt_all D.hyp hp

theorem mem_geods {a : c.Γ} {p : GPath c.graph 8} (hp : p ∈ GPath.nbPaths c.graph a 8) :
    p ∈ c.geods 8 a (p 8) := by
  refine ⟨hp.1, rfl, ?_⟩
  show c.graph.dist (p 0) (p 8) = 8
  rw [hp.1]
  exact D.dist_m hp

theorem nbPaths_of_geods {a b : c.Γ} {t : GPath c.graph 8} (ht : t ∈ c.geods 8 a b) :
    t ∈ GPath.nbPaths c.graph a 8 :=
  ⟨ht.1, GPath.noBack_of_dist_eq (connected_graph c) t ht.2.2⟩

theorem Q_le (u : c.Γ) :
    c.Qvert Qx Ql u ≤ stv c u ∧ ∀ w, c.graph.Adj u w → c.Qvert Qx Ql u ≤ stv c w := by
  obtain ⟨g, hg⟩ := exists_smul_eq_baseVert c u
  have e : c.Qvert Qx Ql u = conjSub g (cond (CosetGeom.vtype u) Ql Qx) :=
    Qvert_eq_conjSub D.qn hg
  have hbase : cond (CosetGeom.vtype u) Ql Qx ≤ stv c (c.baseVert (CosetGeom.vtype u)) ∧
      ∀ w, c.graph.Adj (c.baseVert (CosetGeom.vtype u)) w →
        cond (CosetGeom.vtype u) Ql Qx ≤ stv c w := by
    cases CosetGeom.vtype u
    · exact ⟨D.qx_le, D.fix_x⟩
    · exact ⟨D.ql_le, D.fix_l⟩
  have hs : stv c u = conjSub g (stv c (c.baseVert (CosetGeom.vtype u))) := by
    rw [← stv_smul, hg]
  refine ⟨?_, fun w hw => ?_⟩
  · rw [e, hs]
    exact conjSub_mono g hbase.1
  · have hw' : c.graph.Adj (c.baseVert (CosetGeom.vtype u)) (g⁻¹ • w) := by
      have := (GraphAction.adj_smul g⁻¹ u w).mpr hw
      rwa [← hg, inv_smul_smul] at this
    rw [e]
    have := conjSub_mono g (hbase.2 _ hw')
    rwa [← stv_smul, smul_inv_smul] at this

theorem Q_conj (u : c.Γ) {h : c.G0} (hh : h ∈ stv c u) {x : c.G0}
    (hx : x ∈ c.Qvert Qx Ql u) : h * x * h⁻¹ ∈ c.Qvert Qx Ql u := by
  have hconj : conjSub h (c.Qvert Qx Ql u) = c.Qvert Qx Ql u := by
    rw [← Qvert_smul D.qn h u, MulAction.mem_stabilizer_iff.mp hh]
  rw [← hconj]
  exact mul_mem_conjSub hx

theorem compl_line {u : c.Γ} (hu : CosetGeom.vtype u = true) {r : GPath c.graph 8}
    (hr : r ∈ GPath.nbPaths c.graph u 8) :
    IsComplementIn r.stabPath (c.Qvert Qx Ql u) (stv c u ⊓ stv c (r 1)) := by
  obtain ⟨g, hg⟩ := exists_smul_eq_baseVert c u
  have e2 := Qvert_eq_conjSub D.qn hg
  have hg' : g • c.lv = u := by
    have := hg
    rw [hu] at this
    exact this
  have hq : g⁻¹ • r ∈ GPath.nbPaths c.graph c.lv 8 := by
    refine ⟨?_, GPath.smul_noBack hr.2⟩
    show g⁻¹ • r 0 = c.lv
    rw [hr.1, ← hg', inv_smul_smul]
  have h2 := (IsComplementIn.conjSub_iff g).mpr (D.compl_l _ hq)
  have e1 : conjSub g (g⁻¹ • r).stabPath = r.stabPath := by
    rw [← GPath.stabPath_smul, ← GPath.mul_smul', mul_inv_cancel, GPath.one_smul']
  have e3 : conjSub g (stv c c.lv ⊓ stv c ((g⁻¹ • r) 1)) = stv c u ⊓ stv c (r 1) := by
    rw [conjSub_inf, ← stv_smul, ← stv_smul, hg', GPath.smul_apply, smul_inv_smul]
  have e2' : c.Qvert Qx Ql u = conjSub g Ql := by
    rw [e2, hu]
    rfl
  rw [e1, e3, ← e2'] at h2
  exact h2

theorem idx_point {u : c.Γ} (hu : CosetGeom.vtype u = false) {r : GPath c.graph 8}
    (hr : r ∈ GPath.nbPaths c.graph u 8) :
    (r.stabPath : Subgroup c.G0) ⊓ c.Qvert Qx Ql u = ⊥ ∧
      (c.Qvert Qx Ql u ⊔ r.stabPath).relIndex (stv c u ⊓ stv c (r 1)) = 2 := by
  obtain ⟨g, hg⟩ := exists_smul_eq_baseVert c u
  have e2 := Qvert_eq_conjSub D.qn hg
  have hg' : g • c.xv = u := by
    have := hg
    rw [hu] at this
    exact this
  have hq : g⁻¹ • r ∈ GPath.nbPaths c.graph c.xv 8 := by
    refine ⟨?_, GPath.smul_noBack hr.2⟩
    show g⁻¹ • r 0 = c.xv
    rw [hr.1, ← hg', inv_smul_smul]
  obtain ⟨h1, h2⟩ := D.idx_x _ hq
  have e1 : (r.stabPath : Subgroup c.G0) = conjSub g (g⁻¹ • r).stabPath := by
    rw [← GPath.stabPath_smul, ← GPath.mul_smul', mul_inv_cancel, GPath.one_smul']
  have e3 : stv c u ⊓ stv c (r 1) = conjSub g (stv c c.xv ⊓ stv c ((g⁻¹ • r) 1)) := by
    rw [conjSub_inf, ← stv_smul, ← stv_smul, hg', GPath.smul_apply, smul_inv_smul]
  have e2' : c.Qvert Qx Ql u = conjSub g Qx := by
    rw [e2, hu]
    rfl
  rw [e1, e3, e2', ← conjSub_inf, ← conjSub_sup, conjSub_eq_bot_iff,
    burnsideF46_relIndex_conjSub]
  exact ⟨h1, h2⟩

theorem card_point {u : c.Γ} (hu : CosetGeom.vtype u = false) {r : GPath c.graph 8}
    (hr : r ∈ GPath.nbPaths c.graph u 8) : Nat.card (r.stabPath : Subgroup c.G0) = 2 := by
  obtain ⟨g, hg⟩ := exists_smul_eq_baseVert c u
  rw [hu] at hg
  subst hg
  exact burnsideF46_card_stabPath_smul 2 D.card_x g hr

theorem nontriv_point {u : c.Γ} (hu : CosetGeom.vtype u = false) {r : GPath c.graph 8}
    (hr : r ∈ GPath.nbPaths c.graph u 8) :
    ∃ t ∈ (r.stabPath : Subgroup c.G0), ∃ w, c.graph.Adj u w ∧ t • w ≠ w := by
  obtain ⟨g, hg⟩ := exists_smul_eq_baseVert c u
  rw [hu] at hg
  subst hg
  exact burnsideF46_nontriv_smul D.nontriv_x g hr

theorem aff_point {u : c.Γ} (hu : CosetGeom.vtype u = false) :
    ∃ lab : ZMod 5 → c.Γ, AffLab c.G0 c.graph u lab := by
  obtain ⟨g, hg⟩ := exists_smul_eq_baseVert c u
  rw [hu] at hg
  subst hg
  obtain ⟨lab, A⟩ := D.aff
  exact ⟨_, burnsideF46_affLab_smul A g⟩

theorem twoOrb_line {u : c.Γ} (hu : CosetGeom.vtype u = true) : burnsideF46_TwoOrb c u 8 := by
  obtain ⟨g, hg⟩ := exists_smul_eq_baseVert c u
  rw [hu] at hg
  subst hg
  exact burnsideF46_twoOrb_smul D.two_orb g

theorem five (a : c.Γ) {q : GPath c.graph 8} (hq : q ∈ GPath.nbPaths c.graph a 8) :
    IsComplementIn (q.stabPath : Subgroup c.G0) (c.Qvert Qx Ql (q 8)) (stv c (q 7) ⊓ stv c (q 8)) ∨
      (CosetGeom.vtype a = false ∧ (q.stabPath : Subgroup c.G0) ⊓ c.Qvert Qx Ql (q 8) = ⊥ ∧
        (c.Qvert Qx Ql (q 8) ⊔ (q.stabPath : Subgroup c.G0)).relIndex
          (stv c (q 7) ⊓ stv c (q 8)) = 2) := by
  have hrev : q.rev ∈ GPath.nbPaths c.graph (q 8) 8 := rev_mem_nbPaths hq
  have hv : CosetGeom.vtype (q 8) = CosetGeom.vtype a := by
    rw [vtype_path_even q le_rfl (by decide), hq.1]
  have e1 : q.rev 1 = q 7 := by rw [GPath.rev_apply _ (by norm_num)]
  have es : (q.rev.stabPath : Subgroup c.G0) = q.stabPath := GPath.stabPath_rev q
  cases ha : CosetGeom.vtype a
  · right
    have h := D.idx_point (by rw [hv, ha]) hrev
    rw [es, e1, inf_comm (stv c (q 8))] at h
    exact ⟨rfl, h⟩
  · left
    have h := D.compl_line (by rw [hv, ha]) hrev
    rw [es, e1, inf_comm] at h
    exact h

theorem trans_sphere {n : ℕ} (hn : n < 8) (a : c.Γ) {v w : c.Γ} (hv : c.graph.dist a v = n)
    (hw : c.graph.dist a w = n) : ∃ g : c.G0, g • a = a ∧ g • v = w := by
  cases ha : CosetGeom.vtype a
  · exact GPath.exists_fix_smul_eq_of_dist (m := 7) D.hval (D.transPt ha) (connected_graph c)
      (by omega) hv hw
  · exact GPath.exists_fix_smul_eq_of_dist (m := 6) D.hval (D.transLn ha) (connected_graph c)
      (by omega) hv hw

theorem mem_stabPath_iff_fix {n : ℕ} (hn : n < 8) {a : c.Γ} {p : GPath c.graph n}
    (hp : p ∈ GPath.nbPaths c.graph a n) {g : c.G0} (hga : g • a = a) :
    g ∈ p.stabPath ↔ g • p n = p n := by
  constructor
  · intro h
    exact h n le_rfl
  · intro h
    have hpg : g • p ∈ GPath.nbPaths c.graph a n := by
      refine ⟨?_, GPath.smul_noBack hp.2⟩
      show g • p 0 = a
      rw [hp.1, hga]
    have hgeo : (g • p).IsGeodesic := by
      show c.graph.dist ((g • p) 0) ((g • p) n) = n
      rw [hpg.1]
      exact (D.uniq hn hpg).1
    have := (D.uniq hn hp).2 (g • p) hpg.1 (by simpa using h) hgeo
    intro i hi
    have := congrArg (fun r : GPath c.graph n => r i) this
    simpa using this

theorem six {n : ℕ} (hn : n < 8) {a : c.Γ} {q : GPath c.graph n}
    (hq : q ∈ GPath.nbPaths c.graph a n) :
    (∀ u ∈ CosetGeom.sphere n a, ∀ v ∈ CosetGeom.sphere n a, ∃ g ∈ stv c a, g • u = v) ∧
      q n ∈ CosetGeom.sphere n a ∧ q.IsGeodesic ∧
      (∀ r : GPath c.graph n, r 0 = a → r n = q n → r.IsGeodesic → r = q) ∧
      (2 ≤ n → ∀ S : Set c.Γ, ¬ IsPolygon c.graph S (2 * n)) ∧
      Nat.card ↥(CosetGeom.sphere n a) = (q.stabPath : Subgroup c.G0).relIndex (stv c a) := by
  have hu := D.uniq hn hq
  have hv : q n ∈ CosetGeom.sphere n a := hu.1
  refine ⟨fun u hu' v hv' => ?_, hv, ?_, hu.2, fun h2 S =>
    (burnsideF46_facts46 D.hyp).no_polygon h2 hn S, ?_⟩
  · obtain ⟨g, hga, hgv⟩ := D.trans_sphere hn a hu' hv'
    exact ⟨g, MulAction.mem_stabilizer_iff.mpr hga, hgv⟩
  · show c.graph.dist (q 0) (q n) = n
    rw [hq.1]
    exact hu.1
  · have horb : MulAction.orbit (stv c a) (q n) = CosetGeom.sphere n a := by
      ext w
      constructor
      · rintro ⟨g, rfl⟩
        have hg : (g : c.G0) • a = a := MulAction.mem_stabilizer_iff.mp g.2
        show c.graph.dist a ((g : c.G0) • q n) = n
        have := GPath.dist_smul (connected_graph c) (g : c.G0) a (q n)
        rw [hg] at this
        rw [this]
        exact hv
      · intro hw
        obtain ⟨g, hga, hgv⟩ := D.trans_sphere hn a hv hw
        exact ⟨⟨g, MulAction.mem_stabilizer_iff.mpr hga⟩, hgv⟩
    have hstab : MulAction.stabilizer (stv c a) (q n) = q.stabPath.subgroupOf (stv c a) := by
      ext g
      rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf]
      have hg : (g : c.G0) • a = a := MulAction.mem_stabilizer_iff.mp g.2
      rw [D.mem_stabPath_iff_fix hn hq hg]
      rfl
    rw [← horb, Nat.card_congr (MulAction.orbitEquivQuotientStabilizer (stv c a) (q n)), hstab]
    rfl

theorem four [Finite α.G1] [Finite α.G2] {n : ℕ} (hn : n ≤ 8) {a : c.Γ}
    (hex : ¬ (CosetGeom.vtype a = true ∧ n = 8)) {q : GPath c.graph n}
    (hq : q ∈ GPath.nbPaths c.graph a n) :
    (q.stabPath : Subgroup c.G0).relIndex (stv c a) = α.pathNum (CosetGeom.vtype a) n := by
  cases ha : CosetGeom.vtype a
  · have := burnsideF4b_relIndex_pathNum D.hyp.faithful D.hval (m := 7) (D.transPt ha) n hn q hq
    rwa [ha] at this
  · have hn7 : n ≤ 7 := by
      by_contra h
      exact hex ⟨ha, by omega⟩
    have := burnsideF4b_relIndex_pathNum D.hyp.faithful D.hval (m := 6) (D.transLn ha) n hn7 q hq
    rwa [ha] at this

theorem stabPath_eq {a : c.Γ} {p : GPath c.graph 8} (hp : p ∈ GPath.nbPaths c.graph a 8) :
    (p.stabPath : Subgroup c.G0) = stv c a ⊓ stv c (p 1) ⊓ stv c (p 8) := by
  ext g
  rw [Subgroup.mem_inf, Subgroup.mem_inf, MulAction.mem_stabilizer_iff,
    MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff]
  constructor
  · intro h
    exact ⟨⟨by rw [← hp.1]; exact h 0 (Nat.zero_le 8), h 1 (by norm_num)⟩, h 8 le_rfl⟩
  · rintro ⟨⟨hga, hg1⟩, hg8⟩
    let t : GPath c.graph 7 := p.drop 1 (by norm_num)
    have ht0 : t ∈ GPath.nbPaths c.graph (p 1) 7 :=
      ⟨by show p (1 + min 0 7) = p 1; simp, hp.2.drop 1 (by norm_num)⟩
    have htm : t 7 = p 8 := by
      show p (1 + min 7 7) = p 8
      simp
    have hgt : g • t ∈ GPath.nbPaths c.graph (p 1) 7 := by
      refine ⟨?_, GPath.smul_noBack ht0.2⟩
      show g • t 0 = p 1
      rw [ht0.1, hg1]
    have hgeo : (g • t).IsGeodesic := by
      show c.graph.dist ((g • t) 0) ((g • t) 7) = 7
      rw [hgt.1]
      exact (D.uniq (by norm_num) hgt).1
    have heq := (D.uniq (by norm_num) ht0).2 (g • t) hgt.1
      (by show g • t 7 = t 7; rw [htm, hg8]) hgeo
    intro i hi
    by_cases hi0 : i = 0
    · subst hi0
      rw [hp.1]
      exact hga
    · have := congrArg (fun r : GPath c.graph 7 => r (i - 1)) heq
      simp only [GPath.smul_apply] at this
      have e : t (i - 1) = p i := by
        show p (1 + min (i - 1) 7) = p i
        congr 1
        omega
      rwa [e] at this

theorem trans_nbrs {a : c.Γ} {p : GPath c.graph 8} (hp : p ∈ GPath.nbPaths c.graph a 8)
    (hb : BijFirst c 8 a (p 8)) {y y' : c.Γ} (hy : c.graph.Adj a y) (hy' : c.graph.Adj a y') :
    ∃ h ∈ stv c a ⊓ stv c (p 8), h • y = y' := by
  obtain ⟨z, hz, hz1, -⟩ := D.hval a (p 1) (p 1)
  obtain ⟨q, hq, hq1⟩ := hb.2.2 (show z ∈ CosetGeom.nbrs a from hz)
  have hq1' : q 1 = z := hq1
  have hqnb := D.nbPaths_of_geods hq
  obtain ⟨g, hg, hgy⟩ := D.hyp.pair a p hp q hqnb (by rw [hq1']; exact Ne.symm hz1) y y' hy hy'
  have hle : (p.stabPath : Subgroup c.G0) ⊔ q.stabPath ≤ stv c a ⊓ stv c (p 8) :=
    sup_le (stabPath_le_stab_ends hp.1 rfl) (stabPath_le_stab_ends hq.1 hq.2.1)
  exact ⟨g, hle hg, hgy⟩

theorem smul_geods {a b : c.Γ} {g : c.G0} (hg : g ∈ stv c a ⊓ stv c b) {t : GPath c.graph 8}
    (ht : t ∈ c.geods 8 a b) : g • t ∈ c.geods 8 a b := by
  refine ⟨?_, ?_, ht.2.2.smul (connected_graph c) g⟩
  · show g • t 0 = a
    rw [ht.1]
    exact MulAction.mem_stabilizer_iff.mp hg.1
  · show g • t 8 = b
    rw [ht.2.1]
    exact MulAction.mem_stabilizer_iff.mp hg.2

theorem trans_geods {a : c.Γ} {p : GPath c.graph 8} (hp : p ∈ GPath.nbPaths c.graph a 8)
    (hb : BijFirst c 8 a (p 8)) {q₁ q₂ : GPath c.graph 8} (h₁ : q₁ ∈ c.geods 8 a (p 8))
    (h₂ : q₂ ∈ c.geods 8 a (p 8)) : ∃ g ∈ stv c a ⊓ stv c (p 8), g • q₁ = q₂ := by
  obtain ⟨g, hg, hg1⟩ := D.trans_nbrs hp hb (hb.1 h₁) (hb.1 h₂)
  exact ⟨g, hg, hb.2.1 (D.smul_geods hg h₁) h₂ (by simpa using hg1)⟩

theorem two_trans_line {a : c.Γ} (ha : CosetGeom.vtype a = true) {u₁ u₂ u₁' u₂' : c.Γ}
    (h1 : c.graph.Adj a u₁) (h2 : c.graph.Adj a u₂) (h12 : u₁ ≠ u₂) (h1' : c.graph.Adj a u₁')
    (h2' : c.graph.Adj a u₂') (h12' : u₁' ≠ u₂') :
    ∃ g ∈ stv c a, g • u₁ = u₁' ∧ g • u₂ = u₂' := by
  obtain ⟨g₁, hg₁a, hg₁u⟩ := GPath.exists_fix_smul_eq_of_dist (m := 6) D.hval (D.transLn ha)
    (connected_graph c) (k := 1) (by norm_num) (SimpleGraph.dist_eq_one_iff_adj.mpr h1)
    (SimpleGraph.dist_eq_one_iff_adj.mpr h1')
  have hv1 : CosetGeom.vtype u₁' = false := by
    have := CosetGeom.vtype_ne_of_adj h1'
    rw [ha] at this
    cases h : CosetGeom.vtype u₁'
    · rfl
    · exact absurd h.symm this
  have hadj : c.graph.Adj u₁' a := h1'.symm
  have e1 : burnsideF45_edge hadj 1 = a := burnsideF45_edge_one hadj
  have e0 : burnsideF45_edge hadj 0 = u₁' := burnsideF45_edge_zero hadj
  have hy : c.graph.Adj a (g₁ • u₂) := by
    have := (GraphAction.adj_smul g₁ a u₂).mpr h2
    rwa [hg₁a] at this
  have hy1 : g₁ • u₂ ≠ u₁' := by
    rw [← hg₁u]
    exact fun h => h12 (smul_left_cancel _ h).symm
  obtain ⟨h, hhu, hhq, hhy⟩ := GPath.exists_fix_path_smul_eq (m := 7) D.hval (D.transPt hv1)
    (i := 1) (by norm_num) (burnsideF45_edge_mem hadj) (y := g₁ • u₂) (y' := u₂')
    (by rw [e1]; exact hy) (by rw [e1]; exact h2') (fun _ => by rw [e0]; exact hy1)
    (fun _ => by rw [e0]; exact Ne.symm h12')
  have hha : h • a = a := by
    have := congrArg (fun r : GPath c.graph 1 => r 1) hhq
    simpa [e1] using this
  refine ⟨h * g₁, MulAction.mem_stabilizer_iff.mpr (by rw [mul_smul, hg₁a, hha]), ?_, ?_⟩
  · rw [mul_smul, hg₁u, hhu]
  · rw [mul_smul, hhy]

theorem card_nbrs [Finite α.G1] [Finite α.G2] (a : c.Γ) :
    Nat.card (CosetGeom.nbrs a) = α.qv (CosetGeom.vtype a) + 1 :=
  burnsideF4b_card_nbrs D.hyp.faithful a

theorem eight_line [Finite α.G1] [Finite α.G2] {a : c.Γ} (ha : CosetGeom.vtype a = true)
    {p : GPath c.graph 8} (hp : p ∈ GPath.nbPaths c.graph a 8) (hb : BijFirst c 8 a (p 8)) :
    IsComplementIn (stv c a ⊓ stv c (p 8)) (c.Qvert Qx Ql a) (stv c a) ∧
      (∀ q₁ ∈ c.geods 8 a (p 8), ∀ q₂ ∈ c.geods 8 a (p 8), q₁ ≠ q₂ →
        ∀ r₁ ∈ c.geods 8 a (p 8), ∀ r₂ ∈ c.geods 8 a (p 8), r₁ ≠ r₂ →
          ∃ g ∈ stv c a ⊓ stv c (p 8), g • q₁ = r₁ ∧ g • q₂ = r₂) ∧
      Nat.card ↥(c.geods 8 a (p 8)) = α.qv (CosetGeom.vtype a) + 1 := by
  have hc := D.compl_line ha hp
  have hseq := D.stabPath_eq hp
  have hcompl : IsComplementIn (stv c a ⊓ stv c (p 8)) (c.Qvert Qx Ql a) (stv c a) := by
    refine ⟨hc.1.trans inf_le_left, inf_le_left, ?_, ?_⟩
    · refine eq_bot_iff.mpr fun x hx => ?_
      have hx1 := hc.1 hx.1
      have hx2 : x ∈ p.stabPath := by
        rw [hseq]
        exact ⟨hx1, hx.2.2⟩
      have : x ∈ c.Qvert Qx Ql a ⊓ p.stabPath := ⟨hx.1, hx2⟩
      rw [hc.2.2.1] at this
      exact this
    · intro g hg
      have hga : g • a = a := MulAction.mem_stabilizer_iff.mp hg
      have hadj : c.graph.Adj a (p 1) := burnsideF45_adj_first (by norm_num) hp
      have hadj' : c.graph.Adj a (g • p 1) := by
        have := (GraphAction.adj_smul g a (p 1)).mpr hadj
        rwa [hga] at this
      obtain ⟨h, hh, hhy⟩ := D.trans_nbrs hp hb hadj hadj'
      have hha : h • a = a := MulAction.mem_stabilizer_iff.mp hh.1
      have hmem : h⁻¹ * g ∈ stv c a ⊓ stv c (p 1) := by
        refine ⟨MulAction.mem_stabilizer_iff.mpr ?_, MulAction.mem_stabilizer_iff.mpr ?_⟩
        · rw [mul_smul, hga, inv_smul_eq_iff]
          exact hha.symm
        · rw [mul_smul, ← hhy, inv_smul_smul]
      obtain ⟨q, hq, k, hk, hqk⟩ := hc.2.2.2 _ hmem
      have hkab : k ∈ stv c a ⊓ stv c (p 8) := by
        rw [hseq] at hk
        exact ⟨hk.1.1, hk.2⟩
      refine ⟨h * q * h⁻¹, D.Q_conj a hh.1 hq, h * k,
        (stv c a ⊓ stv c (p 8)).mul_mem hh hkab, ?_⟩
      calc h * q * h⁻¹ * (h * k) = h * (q * k) := by group
        _ = g := by rw [hqk]; group
  refine ⟨hcompl, ?_, ?_⟩
  · intro q₁ hq₁ q₂ hq₂ hne r₁ hr₁ r₂ hr₂ hne'
    have i1 : q₁ 1 ≠ q₂ 1 := fun h => hne (hb.2.1 hq₁ hq₂ h)
    have i2 : r₁ 1 ≠ r₂ 1 := fun h => hne' (hb.2.1 hr₁ hr₂ h)
    obtain ⟨g, hg, hg1, hg2⟩ := D.two_trans_line ha (hb.1 hq₁) (hb.1 hq₂) i1 (hb.1 hr₁)
      (hb.1 hr₂) i2
    obtain ⟨x, hx, h, hh, hxh⟩ := hcompl.2.2.2 g hg
    have hxfix : ∀ w, c.graph.Adj a w → x⁻¹ • w = w := fun w hw =>
      MulAction.mem_stabilizer_iff.mp ((D.Q_le a).2 w hw (inv_mem hx))
    have hh' : h = x⁻¹ * g := by
      rw [← hxh]
      group
    have e1 : h • q₁ 1 = r₁ 1 := by
      rw [hh', mul_smul, hg1, hxfix _ (hb.1 hr₁)]
    have e2 : h • q₂ 1 = r₂ 1 := by
      rw [hh', mul_smul, hg2, hxfix _ (hb.1 hr₂)]
    exact ⟨h, hh, hb.2.1 (D.smul_geods hh hq₁) hr₁ (by simpa using e1),
      hb.2.1 (D.smul_geods hh hq₂) hr₂ (by simpa using e2)⟩
  · rw [Nat.card_congr (hb.equiv _), D.card_nbrs a]

theorem eight_point [Finite α.G1] [Finite α.G2] {a : c.Γ} (ha : CosetGeom.vtype a = false)
    {p : GPath c.graph 8} (hp : p ∈ GPath.nbPaths c.graph a 8) (hb : BijFirst c 8 a (p 8)) :
    Nonempty (↥(stv c a ⊓ stv c (p 8)) ≃* DihedralGroup 5) ∧
      (∀ q₁ ∈ c.geods 8 a (p 8), ∀ q₂ ∈ c.geods 8 a (p 8),
        ∃ g ∈ stv c a ⊓ stv c (p 8), g • q₁ = q₂) ∧
      Nat.card ↥(c.geods 8 a (p 8)) = 5 := by
  have hn5 : Nat.card (CosetGeom.nbrs a) = 5 := by
    rw [D.card_nbrs a, ha]
    show α.qOne + 1 = 5
    rw [D.qOne]
  refine ⟨?_, fun q₁ h₁ q₂ h₂ => D.trans_geods hp hb h₁ h₂, ?_⟩
  · obtain ⟨lab, A⟩ := D.aff_point ha
    have hseq := D.stabPath_eq hp
    have hadj : c.graph.Adj a (p 1) := burnsideF45_adj_first (by norm_num) hp
    have hst : stv c (p 1) ⊓ (stv c a ⊓ stv c (p 8)) = p.stabPath := by
      rw [hseq]
      ext g
      simp only [Subgroup.mem_inf]
      tauto
    have horb : MulAction.orbit ↥(stv c a ⊓ stv c (p 8)) (p 1) = CosetGeom.nbrs a := by
      ext t
      constructor
      · rintro ⟨g, rfl⟩
        have hga : (g : c.G0) • a = a := MulAction.mem_stabilizer_iff.mp g.2.1
        show c.graph.Adj a ((g : c.G0) • p 1)
        have := (GraphAction.adj_smul (g : c.G0) a (p 1)).mpr hadj
        rwa [hga] at this
      · intro ht
        obtain ⟨h, hh, hht⟩ := D.trans_nbrs hp hb hadj ht
        exact ⟨⟨h, hh⟩, hht⟩
    have hcard : Nat.card ↥(stv c a ⊓ stv c (p 8)) = 10 := by
      have h1 := Subgroup.relIndex_mul_card (stv c (p 1)) (stv c a ⊓ stv c (p 8))
      rw [hst, D.card_point ha hp, burnsideF45_relIndex_stv, horb, ← Nat.card_coe_set_eq,
        hn5] at h1
      omega
    obtain ⟨t, ht, w, hw, htw⟩ := D.nontriv_point ha hp
    refine burnsideF46_dihedral A inf_le_left hcard fun g hg hfix => ?_
    have hgp : g ∈ (p.stabPath : Subgroup c.G0) := by
      rw [hseq]
      exact ⟨⟨hg.1, MulAction.mem_stabilizer_iff.mpr (hfix _ hadj)⟩, hg.2⟩
    exact burnsideF45_eq_one_of_card_two (D.card_point ha hp) ht hgp htw (hfix w hw)
  · rw [Nat.card_congr (hb.equiv _), hn5]

theorem paths_trans {a : c.Γ} {q₁ q₂ : GPath c.graph 8} (h₁ : q₁ ∈ GPath.nbPaths c.graph a 8)
    (h₂ : q₂ ∈ GPath.nbPaths c.graph a 8) (he : q₁ 8 = q₂ 8) :
    ∃ g ∈ stv c a ⊓ stv c (q₁ 8), g • q₁ = q₂ := by
  have hg₂ : q₂ ∈ c.geods 8 a (q₁ 8) := by
    have := D.mem_geods h₂
    rwa [← he] at this
  rcases D.alt h₁ with hi | hb
  · refine ⟨1, one_mem _, ?_⟩
    rw [GPath.one_smul']
    exact (hi q₂ h₂.1 he.symm hg₂.2.2).symm
  · exact D.trans_geods h₁ hb (D.mem_geods h₁) hg₂

end burnsideF46_Data

end CFSG.ASVolI
