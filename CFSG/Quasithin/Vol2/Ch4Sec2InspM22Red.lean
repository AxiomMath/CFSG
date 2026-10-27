module

public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.Sporadic.Schreier.MathieuOddCoreCentral

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Quasithin CFSG.Sporadic.Schreier
open scoped commutatorElement

section Perfect

variable {G : Type*} [Group G]

theorem eq_one_of_perfect_central_hom [Group.IsPerfect G] (f : G →* G)
    (hf : ∀ g, f g ∈ Subgroup.center G) (g : G) : f g = 1 := by
  have hcomm : ∀ a b : G, f ⁅a, b⁆ = 1 := fun a b => by
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact Subgroup.mem_center_iff.1 (hf b) (f a)
  have hc : (⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ : Subgroup G) = ⊤ :=
    Group.IsPerfect.commutator_eq_top
  have htop : (⊤ : Subgroup G) ≤ f.ker := by
    rw [← hc, Subgroup.commutator_le]
    intro a _ b _
    exact MonoidHom.mem_ker.2 (hcomm a b)
  exact MonoidHom.mem_ker.1 (htop (Subgroup.mem_top g))

theorem mem_center_of_comm_mem [Group.IsPerfect G] (c : G)
    (h : ∀ g : G, g⁻¹ * c⁻¹ * g * c ∈ Subgroup.center G) : c ∈ Subgroup.center G := by
  let w : G →* G :=
    { toFun := fun g => g⁻¹ * c⁻¹ * g * c
      map_one' := by group
      map_mul' := fun a b => by
        show (a * b)⁻¹ * c⁻¹ * (a * b) * c = (a⁻¹ * c⁻¹ * a * c) * (b⁻¹ * c⁻¹ * b * c)
        calc (a * b)⁻¹ * c⁻¹ * (a * b) * c
            = b⁻¹ * (a⁻¹ * c⁻¹ * a * c) * c⁻¹ * b * c := by group
          _ = (a⁻¹ * c⁻¹ * a * c) * b⁻¹ * c⁻¹ * b * c := by
            rw [Subgroup.mem_center_iff.1 (h a) b⁻¹]
          _ = (a⁻¹ * c⁻¹ * a * c) * (b⁻¹ * c⁻¹ * b * c) := by group }
  have hw : ∀ g, w g = 1 := fun g => eq_one_of_perfect_central_hom w h g
  rw [Subgroup.mem_center_iff]
  intro g
  have hg : g⁻¹ * c⁻¹ * g * c = 1 := hw g
  have h1 : c⁻¹ * g * c = g := by
    have : g * (g⁻¹ * c⁻¹ * g * c) = c⁻¹ * g * c := by group
    rw [← this, hg, mul_one]
  calc g * c = c * (c⁻¹ * g * c) := by group
    _ = c * g := by rw [h1]

theorem center_quotient_eq_map [Group.IsPerfect G] (N : Subgroup G) [N.Normal]
    (hN : N ≤ Subgroup.center G) :
    Subgroup.center (G ⧸ N) = (Subgroup.center G).map (QuotientGroup.mk' N) := by
  ext x
  rw [Subgroup.mem_map]
  constructor
  · intro hx
    obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective x
    refine ⟨c, mem_center_of_comm_mem c (fun g => ?_), rfl⟩
    have hcomm := (Subgroup.mem_center_iff.1 hx) (g : G ⧸ N)
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq] at hcomm
    have hmem : ((g * c)⁻¹ * (c * g))⁻¹ ∈ N := N.inv_mem hcomm
    have heq : ((g * c)⁻¹ * (c * g))⁻¹ = g⁻¹ * c⁻¹ * g * c := by group
    rw [heq] at hmem
    exact hN hmem
  · rintro ⟨c, hc, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
    change (g : G ⧸ N) * (c : G ⧸ N) = (c : G ⧸ N) * (g : G ⧸ N)
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, Subgroup.mem_center_iff.1 hc g]

end Perfect

theorem center_map_equiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    (Subgroup.center A).map e.toMonoidHom = Subgroup.center B := by
  ext x
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨a, ha, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨a', rfl⟩ := e.surjective y
    have h := Subgroup.mem_center_iff.1 ha a'
    show e a' * e a = e a * e a'
    rw [← map_mul, ← map_mul, h]
  · intro hx
    refine ⟨e.symm x, ?_, by simp⟩
    rw [Subgroup.mem_center_iff]
    intro a
    have h := Subgroup.mem_center_iff.1 hx (e a)
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact h

noncomputable def quotCenterCongr {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    A ⧸ Subgroup.center A ≃* B ⧸ Subgroup.center B :=
  QuotientGroup.congr (Subgroup.center A) (Subgroup.center B) e (center_map_equiv e)

section Quotient

variable {G : Type*} [Group G]

noncomputable def quotCenterEquiv [Group.IsPerfect G] (N : Subgroup G) [N.Normal]
    (hN : N ≤ Subgroup.center G) :
    (G ⧸ N) ⧸ Subgroup.center (G ⧸ N) ≃* G ⧸ Subgroup.center G :=
  (QuotientGroup.quotientMulEquivOfEq (center_quotient_eq_map N hN)).trans
    (QuotientGroup.quotientQuotientEquivQuotient N (Subgroup.center G) hN)

theorem isQuasisimple_quotient (hQ : CFSG.IsQuasisimple G) (N : Subgroup G) [N.Normal]
    (hN : N ≤ Subgroup.center G) : CFSG.IsQuasisimple (G ⧸ N) := by
  haveI : Group.IsPerfect G := hQ.1
  haveI : IsSimpleGroup (G ⧸ Subgroup.center G) := hQ.2.1
  have hperf : Group.IsPerfect (G ⧸ N) := by
    refine ⟨?_⟩
    have h1 := Subgroup.map_commutator (⊤ : Subgroup G) (⊤ : Subgroup G) (QuotientGroup.mk' N)
    have htop : Subgroup.map (QuotientGroup.mk' N) (⊤ : Subgroup G) = ⊤ := by
      ext x
      constructor
      · intro _
        exact Subgroup.mem_top x
      · intro _
        obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
        exact Subgroup.mem_map.2 ⟨g, Subgroup.mem_top g, rfl⟩
    have hc : (⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ : Subgroup G) = ⊤ :=
      Group.IsPerfect.commutator_eq_top
    rw [hc, htop] at h1
    exact h1.symm
  unfold CFSG.IsQuasisimple
  refine ⟨hperf, (quotCenterEquiv N hN).isSimpleGroup, ?_⟩
  obtain ⟨a, b, hab⟩ := hQ.2.2
  refine ⟨(quotCenterEquiv N hN).symm a, (quotCenterEquiv N hN).symm b, fun h => hab ?_⟩
  have := congrArg (quotCenterEquiv N hN) h
  simpa using this

end Quotient

section Reduction

variable {Yh : Type} [Group Yh]

def conjY (Y : Subgroup Yh) (hY : Y.Normal) (r : Yh) (y : ↥Y) : ↥Y :=
  ⟨r * y * r⁻¹, hY.conj_mem y y.2 r⟩

theorem conjY_conjY (Y : Subgroup Yh) (hY : Y.Normal) (r : Yh) (hr : r ^ 2 = 1) (y : ↥Y) :
    conjY Y hY r (conjY Y hY r y) = y := by
  apply Subtype.ext
  have hrr : r * r = 1 := by rw [← pow_two]; exact hr
  have hr' : r⁻¹ = r := inv_eq_of_mul_eq_one_right hrr
  show r * (r * (y : Yh) * r⁻¹) * r⁻¹ = (y : Yh)
  rw [hr']
  calc r * (r * (y : Yh) * r) * r = (r * r) * y * (r * r) := by group
    _ = y := by rw [hrr, one_mul, mul_one]

def involConj (Y : Subgroup Yh) (hY : Y.Normal) (r : Yh) (hr : r ^ 2 = 1) : MulAut ↥Y :=
  { toFun := conjY Y hY r
    invFun := conjY Y hY r
    left_inv := conjY_conjY Y hY r hr
    right_inv := conjY_conjY Y hY r hr
    map_mul' := fun a b => by
      apply Subtype.ext
      show r * ((a : Yh) * b) * r⁻¹ = (r * a * r⁻¹) * (r * b * r⁻¹)
      group }

theorem conjY_mul (Y : Subgroup Yh) (hY : Y.Normal) (r : Yh) (hr : r ^ 2 = 1) (a b : ↥Y) :
    conjY Y hY r (a * b) = conjY Y hY r a * conjY Y hY r b :=
  (involConj Y hY r hr).map_mul a b

theorem conjY_mem_center (Y : Subgroup Yh) (hY : Y.Normal) (r : Yh) (hr : r ^ 2 = 1)
    {z : ↥Y} (hz : z ∈ Subgroup.center ↥Y) : conjY Y hY r z ∈ Subgroup.center ↥Y := by
  rw [Subgroup.mem_center_iff]
  intro g
  obtain ⟨h, rfl⟩ : ∃ h, g = conjY Y hY r h :=
    ⟨conjY Y hY r g, (conjY_conjY Y hY r hr g).symm⟩
  rw [← conjY_mul Y hY r hr, ← conjY_mul Y hY r hr, Subgroup.mem_center_iff.1 hz h]

def involQuotMap (Y : Subgroup Yh) (hY : Y.Normal) (r : Yh) (hr : r ^ 2 = 1) :
    (↥Y ⧸ Subgroup.center ↥Y) →* (↥Y ⧸ Subgroup.center ↥Y) :=
  QuotientGroup.map (Subgroup.center ↥Y) (Subgroup.center ↥Y) (involConj Y hY r hr).toMonoidHom
    (fun _ hz => conjY_mem_center Y hY r hr hz)

theorem involQuotMap_mk (Y : Subgroup Yh) (hY : Y.Normal) (r : Yh) (hr : r ^ 2 = 1) (y : ↥Y) :
    involQuotMap Y hY r hr (QuotientGroup.mk y) = QuotientGroup.mk (conjY Y hY r y) :=
  QuotientGroup.map_mk _ _ _ _ y

theorem involQuotMap_invol (Y : Subgroup Yh) (hY : Y.Normal) (r : Yh) (hr : r ^ 2 = 1)
    (x : ↥Y ⧸ Subgroup.center ↥Y) : involQuotMap Y hY r hr (involQuotMap Y hY r hr x) = x := by
  refine QuotientGroup.induction_on x (fun z => ?_)
  rw [involQuotMap_mk, involQuotMap_mk, conjY_conjY Y hY r hr z]

def involQuot (Y : Subgroup Yh) (hY : Y.Normal) (r : Yh) (hr : r ^ 2 = 1) :
    MulAut (↥Y ⧸ Subgroup.center ↥Y) :=
  { toFun := involQuotMap Y hY r hr
    invFun := involQuotMap Y hY r hr
    left_inv := involQuotMap_invol Y hY r hr
    right_inv := involQuotMap_invol Y hY r hr
    map_mul' := (involQuotMap Y hY r hr).map_mul }

theorem involQuot_mk (Y : Subgroup Yh) (hY : Y.Normal) (r : Yh) (hr : r ^ 2 = 1) (y : ↥Y) :
    involQuot Y hY r hr (QuotientGroup.mk y) = QuotientGroup.mk (conjY Y hY r y) :=
  involQuotMap_mk Y hY r hr y

theorem involQuot_sq (Y : Subgroup Yh) (hY : Y.Normal) (r : Yh) (hr : r ^ 2 = 1) :
    involQuot Y hY r hr ^ 2 = 1 := by
  refine MulEquiv.ext (fun x => ?_)
  show involQuotMap Y hY r hr (involQuotMap Y hY r hr x) = x
  exact involQuotMap_invol Y hY r hr x

theorem involQuot_ne_one (Y : Subgroup Yh) [Group.IsPerfect ↥Y] (hY : Y.Normal) (r : Yh)
    (hr : r ^ 2 = 1) (hnc : ¬ Y ≤ Subgroup.centralizer ({r} : Set Yh)) :
    involQuot Y hY r hr ≠ 1 := by
  intro h1
  have hfix : ∀ x, involQuotMap Y hY r hr x = x := fun x => by
    have h2 : involQuot Y hY r hr x = x := by rw [h1]; rfl
    exact h2
  have hcent : ∀ z : ↥Y, z⁻¹ * conjY Y hY r z ∈ Subgroup.center ↥Y := by
    intro z
    have hz := hfix (QuotientGroup.mk z)
    rw [involQuotMap_mk, QuotientGroup.eq] at hz
    have := (Subgroup.center ↥Y).inv_mem hz
    simpa using this
  let δ : ↥Y →* ↥Y :=
    { toFun := fun z => z⁻¹ * conjY Y hY r z
      map_one' := by
        apply Subtype.ext
        simp [conjY]
      map_mul' := fun x y => by
        show (x * y)⁻¹ * conjY Y hY r (x * y) =
          (x⁻¹ * conjY Y hY r x) * (y⁻¹ * conjY Y hY r y)
        rw [conjY_mul Y hY r hr]
        calc (x * y)⁻¹ * (conjY Y hY r x * conjY Y hY r y)
            = y⁻¹ * (x⁻¹ * conjY Y hY r x) * conjY Y hY r y := by group
          _ = (x⁻¹ * conjY Y hY r x) * y⁻¹ * conjY Y hY r y := by
            rw [Subgroup.mem_center_iff.1 (hcent x) y⁻¹]
          _ = (x⁻¹ * conjY Y hY r x) * (y⁻¹ * conjY Y hY r y) := by group }
  apply hnc
  intro y hy
  have hz : (⟨y, hy⟩ : ↥Y)⁻¹ * conjY Y hY r ⟨y, hy⟩ = 1 :=
    eq_one_of_perfect_central_hom δ hcent ⟨y, hy⟩
  have hc : conjY Y hY r ⟨y, hy⟩ = ⟨y, hy⟩ := (inv_mul_eq_one.1 hz).symm
  have hc' : r * y * r⁻¹ = y := congrArg Subtype.val hc
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  rw [Set.mem_singleton_iff.1 hh]
  exact mul_inv_eq_iff_eq_mul.1 hc'



theorem conjY_eq_of_comm (Y : Subgroup Yh) (hY : Y.Normal) (r : Yh) (y : ↥Y)
    (h : r * (y : Yh) = (y : Yh) * r) : conjY Y hY r y = y := by
  apply Subtype.ext
  exact mul_inv_eq_iff_eq_mul.2 h

theorem comm_of_conjY_eq (Y : Subgroup Yh) (hY : Y.Normal) (r : Yh) (y : ↥Y)
    (h : conjY Y hY r y = y) : r * (y : Yh) = (y : Yh) * r := by
  have h' : r * (y : Yh) * r⁻¹ = y := congrArg Subtype.val h
  exact mul_inv_eq_iff_eq_mul.1 h'

def cenY (Y : Subgroup Yh) (hY : Y.Normal) (r : Yh) (hr : r ^ 2 = 1) : Subgroup ↥Y :=
  fixSub (involConj Y hY r hr)

theorem mem_cenY (Y : Subgroup Yh) (hY : Y.Normal) (r : Yh) (hr : r ^ 2 = 1) (y : ↥Y) :
    y ∈ cenY Y hY r hr ↔ conjY Y hY r y = y := by
  rw [cenY, mem_fixSub]
  rfl

def fixPre (Y : Subgroup Yh) (hY : Y.Normal) (r : Yh) (hr : r ^ 2 = 1) : Subgroup ↥Y :=
  (fixSub (involQuot Y hY r hr)).comap (QuotientGroup.mk' (Subgroup.center ↥Y))

theorem mem_fixPre (Y : Subgroup Yh) (hY : Y.Normal) (r : Yh) (hr : r ^ 2 = 1) (y : ↥Y) :
    y ∈ fixPre Y hY r hr ↔
      (QuotientGroup.mk (conjY Y hY r y) : ↥Y ⧸ Subgroup.center ↥Y) = QuotientGroup.mk y := by
  rw [fixPre, Subgroup.mem_comap, mem_fixSub]
  show involQuot Y hY r hr (QuotientGroup.mk y) = QuotientGroup.mk y ↔ _
  rw [involQuot_mk]

def cenIso (Y : Subgroup Yh) (hY : Y.Normal) (r : Yh) (hr : r ^ 2 = 1) :
    ↥(Y ⊓ Subgroup.centralizer ({r} : Set Yh)) ≃* ↥(cenY Y hY r hr) where
  toFun z := ⟨⟨z.1, (Subgroup.mem_inf.1 z.2).1⟩,
    (mem_cenY Y hY r hr _).2
      (conjY_eq_of_comm Y hY r _ (Subgroup.mem_centralizer_iff.1
        (Subgroup.mem_inf.1 z.2).2 r (Set.mem_singleton r)))⟩
  invFun x := ⟨x.1.1, Subgroup.mem_inf.2 ⟨x.1.2, Subgroup.mem_centralizer_iff.2
    (fun h hh => by
      rw [Set.mem_singleton_iff.1 hh]
      exact comm_of_conjY_eq Y hY r x.1 ((mem_cenY Y hY r hr x.1).1 x.2))⟩⟩
  left_inv z := rfl
  right_inv x := rfl
  map_mul' a b := rfl

theorem cenY_le_fixPre (Y : Subgroup Yh) (hY : Y.Normal) (r : Yh) (hr : r ^ 2 = 1) :
    cenY Y hY r hr ≤ fixPre Y hY r hr := by
  intro y hy
  rw [mem_fixPre, (mem_cenY Y hY r hr y).1 hy]

theorem cenY_normal_in_fixPre (Y : Subgroup Yh) (hY : Y.Normal) (r : Yh) (hr : r ^ 2 = 1) :
    ((cenY Y hY r hr).subgroupOf (fixPre Y hY r hr)).Normal := by
  have hcentral : ∀ x : ↥(fixPre Y hY r hr),
      (x : ↥Y)⁻¹ * conjY Y hY r x ∈ Subgroup.center ↥Y := by
    intro x
    exact QuotientGroup.eq.1 ((mem_fixPre Y hY r hr x).1 x.2).symm
  let δF : ↥(fixPre Y hY r hr) →* ↥Y :=
    { toFun := fun x => (x : ↥Y)⁻¹ * conjY Y hY r x
      map_one' := by
        show ((1 : ↥Y))⁻¹ * conjY Y hY r 1 = 1
        apply Subtype.ext
        simp [conjY]
      map_mul' := fun x y => by
        have hcx := hcentral x
        show ((x : ↥Y) * (y : ↥Y))⁻¹ * conjY Y hY r ((x : ↥Y) * (y : ↥Y)) =
          ((x : ↥Y)⁻¹ * conjY Y hY r x) * ((y : ↥Y)⁻¹ * conjY Y hY r y)
        rw [conjY_mul Y hY r hr]
        calc ((x : ↥Y) * (y : ↥Y))⁻¹ * (conjY Y hY r x * conjY Y hY r y)
            = (y : ↥Y)⁻¹ * ((x : ↥Y)⁻¹ * conjY Y hY r x) * conjY Y hY r y := by group
          _ = ((x : ↥Y)⁻¹ * conjY Y hY r x) * (y : ↥Y)⁻¹ * conjY Y hY r y := by
            rw [Subgroup.mem_center_iff.1 hcx (y : ↥Y)⁻¹]
          _ = ((x : ↥Y)⁻¹ * conjY Y hY r x) * ((y : ↥Y)⁻¹ * conjY Y hY r y) := by group }
  have hker : δF.ker = (cenY Y hY r hr).subgroupOf (fixPre Y hY r hr) := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    show (x : ↥Y)⁻¹ * conjY Y hY r x = 1 ↔ _
    rw [inv_mul_eq_one, mem_cenY]
    exact eq_comm
  rw [← hker]
  exact MonoidHom.normal_ker δF

theorem cenIso_image (Y : Subgroup Yh) (hY : Y.Normal) (r : Yh) (hr : r ^ 2 = 1) (C : Subgroup Yh) :
    (C.subgroupOf (Y ⊓ Subgroup.centralizer ({r} : Set Yh))).map
        (cenIso Y hY r hr).toMonoidHom = (C.subgroupOf Y).subgroupOf (cenY Y hY r hr) := by
  ext x
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact Subgroup.mem_subgroupOf.2 (Subgroup.mem_subgroupOf.2 (Subgroup.mem_subgroupOf.1 hz))
  · intro hx
    exact ⟨(cenIso Y hY r hr).symm x,
      Subgroup.mem_subgroupOf.2 (Subgroup.mem_subgroupOf.2 (Subgroup.mem_subgroupOf.1 hx)),
      (cenIso Y hY r hr).apply_symm_apply x⟩

theorem isSubnormal_cenY (Y : Subgroup Yh) (hY : Y.Normal) (r : Yh) (hr : r ^ 2 = 1) (C : Subgroup Yh)
    (hsn : (C.subgroupOf (Y ⊓ Subgroup.centralizer ({r} : Set Yh))).IsSubnormal) :
    ((C.subgroupOf Y).subgroupOf (cenY Y hY r hr)).IsSubnormal := by
  rw [← cenIso_image Y hY r hr C]
  exact Subgroup.IsSubnormal.map (cenIso Y hY r hr).surjective hsn

theorem sub_map_eq (Y : Subgroup Yh) (hY : Y.Normal) (r : Yh) (hr : r ^ 2 = 1) (C : Subgroup Yh) :
    ((C.subgroupOf Y).subgroupOf (cenY Y hY r hr)).map
        (Subgroup.subgroupOfEquivOfLe (cenY_le_fixPre Y hY r hr)).symm.toMonoidHom =
      ((C.subgroupOf Y).subgroupOf (fixPre Y hY r hr)).subgroupOf
        ((cenY Y hY r hr).subgroupOf (fixPre Y hY r hr)) := by
  ext x
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact Subgroup.mem_subgroupOf.2 (Subgroup.mem_subgroupOf.2 (Subgroup.mem_subgroupOf.2
      (Subgroup.mem_subgroupOf.1 (Subgroup.mem_subgroupOf.1 hw))))
  · intro hx
    exact ⟨Subgroup.subgroupOfEquivOfLe (cenY_le_fixPre Y hY r hr) x,
      Subgroup.mem_subgroupOf.2 (Subgroup.mem_subgroupOf.2
        (Subgroup.mem_subgroupOf.1 (Subgroup.mem_subgroupOf.1 (Subgroup.mem_subgroupOf.1 hx)))),
      (Subgroup.subgroupOfEquivOfLe (cenY_le_fixPre Y hY r hr)).symm_apply_apply x⟩

theorem exists_invol_aut_of_component [Finite Yh] (Y : Subgroup Yh)
    (r : Yh) (hY : Y.Normal) (hq : CFSG.IsQuasisimple ↥Y) (hr : r ^ 2 = 1)
    (hnc : ¬ Y ≤ Subgroup.centralizer ({r} : Set Yh))
    (C : Subgroup Yh) (hC : C ≤ Y ⊓ Subgroup.centralizer ({r} : Set Yh))
    (hsn : (C.subgroupOf (Y ⊓ Subgroup.centralizer ({r} : Set Yh))).IsSubnormal)
    (hCq : CFSG.IsQuasisimple ↥C) (hM : IsSporadic .M22 (↥C ⧸ Subgroup.center ↥C)) :
    ∃ β : MulAut (↥Y ⧸ Subgroup.center ↥Y), β ^ 2 = 1 ∧ β ≠ 1 ∧
      ∃ D : Subgroup (↥Y ⧸ Subgroup.center ↥Y),
        (∀ x ∈ D, β x = x) ∧
        (D.subgroupOf (fixSub β)).IsSubnormal ∧ CFSG.IsQuasisimple ↥D ∧
        IsSporadic .M22 (↥D ⧸ Subgroup.center ↥D) := by
  haveI : Group.IsPerfect ↥Y := hq.1
  have hC_le_Y : C ≤ Y := hC.trans inf_le_left
  have hCK : C.subgroupOf Y ≤ cenY Y hY r hr := by
    intro y hy
    rw [Subgroup.mem_subgroupOf] at hy
    have hcent := (Subgroup.mem_inf.1 (hC hy)).2
    rw [mem_cenY]
    exact conjY_eq_of_comm Y hY r y (Subgroup.mem_centralizer_iff.1 hcent r (Set.mem_singleton r))
  have hQCg : CFSG.IsQuasisimple ↥(C.subgroupOf Y) :=
    CFSG.IsQuasisimple.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hC_le_Y) hCq
  refine ⟨involQuot Y hY r hr, involQuot_sq Y hY r hr, involQuot_ne_one Y hY r hr hnc,
    Subgroup.map (QuotientGroup.mk' (Subgroup.center ↥Y)) (C.subgroupOf Y), ?_, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.1 hx
    change involQuot Y hY r hr (QuotientGroup.mk c) = QuotientGroup.mk c
    rw [involQuot_mk, (mem_cenY Y hY r hr c).1 (hCK hc)]
  ·
    have hKn := cenY_normal_in_fixPre Y hY r hr
    have hle : (C.subgroupOf Y).subgroupOf (fixPre Y hY r hr) ≤
        (cenY Y hY r hr).subgroupOf (fixPre Y hY r hr) := fun x hx =>
      Subgroup.mem_subgroupOf.2 (hCK (Subgroup.mem_subgroupOf.1 hx))
    have hCfK : (((C.subgroupOf Y).subgroupOf (fixPre Y hY r hr)).subgroupOf
        ((cenY Y hY r hr).subgroupOf (fixPre Y hY r hr))).IsSubnormal := by
      rw [← sub_map_eq Y hY r hr C]
      exact Subgroup.IsSubnormal.map
        (Subgroup.subgroupOfEquivOfLe (cenY_le_fixPre Y hY r hr)).symm.surjective
        (isSubnormal_cenY Y hY r hr C hsn)
    have hCf : ((C.subgroupOf Y).subgroupOf (fixPre Y hY r hr)).IsSubnormal :=
      Subgroup.IsSubnormal.trans hle hCfK (Subgroup.Normal.isSubnormal hKn)
    let ψ : ↥(fixPre Y hY r hr) →* ↥(fixSub (involQuot Y hY r hr)) :=
      ((QuotientGroup.mk' (Subgroup.center ↥Y)).comp (fixPre Y hY r hr).subtype).codRestrict
        (fixSub (involQuot Y hY r hr)) (fun x => Subgroup.mem_comap.1 x.2)
    have hψ : Function.Surjective ψ := by
      intro f
      obtain ⟨f, hf⟩ := f
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective f
      exact ⟨⟨y, hf⟩, rfl⟩
    have himg := Subgroup.IsSubnormal.map hψ hCf
    have heq : Subgroup.map ψ ((C.subgroupOf Y).subgroupOf (fixPre Y hY r hr)) =
        (Subgroup.map (QuotientGroup.mk' (Subgroup.center ↥Y)) (C.subgroupOf Y)).subgroupOf
          (fixSub (involQuot Y hY r hr)) := by
      ext x
      constructor
      · rintro ⟨w, hw, rfl⟩
        exact Subgroup.mem_subgroupOf.2 (Subgroup.mem_map.2 ⟨(w : ↥Y),
          Subgroup.mem_subgroupOf.1 hw, rfl⟩)
      · intro hx
        obtain ⟨c, hc, hcx⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hx)
        have hcF : c ∈ fixPre Y hY r hr := by
          show (QuotientGroup.mk' (Subgroup.center ↥Y)) c ∈ fixSub (involQuot Y hY r hr)
          rw [hcx]
          exact x.2
        exact ⟨⟨c, hcF⟩, Subgroup.mem_subgroupOf.2 hc, Subtype.ext hcx⟩
    rw [heq] at himg
    exact himg
  ·
    let φ : ↥(C.subgroupOf Y) →* ↥(Subgroup.map (QuotientGroup.mk' (Subgroup.center ↥Y))
        (C.subgroupOf Y)) :=
      ((QuotientGroup.mk' (Subgroup.center ↥Y)).comp (C.subgroupOf Y).subtype).codRestrict
        _ (fun x => Subgroup.mem_map_of_mem _ x.2)
    have hφ : Function.Surjective φ := by
      intro d
      obtain ⟨d, hd⟩ := d
      obtain ⟨c, hc, hcd⟩ := Subgroup.mem_map.1 hd
      exact ⟨⟨c, hc⟩, Subtype.ext hcd⟩
    have hker : φ.ker ≤ Subgroup.center ↥(C.subgroupOf Y) := by
      intro x hx
      have h1 : ((QuotientGroup.mk (x.1 : ↥Y)) : ↥Y ⧸ Subgroup.center ↥Y) = 1 := by
        have h2 := congrArg Subtype.val (MonoidHom.mem_ker.1 hx)
        exact h2
      have hz : (x.1 : ↥Y) ∈ Subgroup.center ↥Y := (QuotientGroup.eq_one_iff _).1 h1
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      exact Subgroup.mem_center_iff.1 hz g.1
    have hQD : CFSG.IsQuasisimple (↥(C.subgroupOf Y) ⧸ φ.ker) :=
      isQuasisimple_quotient hQCg φ.ker hker
    have e1 : ↥(C.subgroupOf Y) ⧸ φ.ker ≃* ↥(Subgroup.map (QuotientGroup.mk' (Subgroup.center ↥Y))
        (C.subgroupOf Y)) := QuotientGroup.quotientKerEquivOfSurjective φ hφ
    exact CFSG.IsQuasisimple.of_mulEquiv e1.symm hQD
  ·
    haveI : Group.IsPerfect ↥(C.subgroupOf Y) := hQCg.1
    let φ : ↥(C.subgroupOf Y) →* ↥(Subgroup.map (QuotientGroup.mk' (Subgroup.center ↥Y))
        (C.subgroupOf Y)) :=
      ((QuotientGroup.mk' (Subgroup.center ↥Y)).comp (C.subgroupOf Y).subtype).codRestrict
        _ (fun x => Subgroup.mem_map_of_mem _ x.2)
    have hφ : Function.Surjective φ := by
      intro d
      obtain ⟨d, hd⟩ := d
      obtain ⟨c, hc, hcd⟩ := Subgroup.mem_map.1 hd
      exact ⟨⟨c, hc⟩, Subtype.ext hcd⟩
    have hker : φ.ker ≤ Subgroup.center ↥(C.subgroupOf Y) := by
      intro x hx
      have h1 : ((QuotientGroup.mk (x.1 : ↥Y)) : ↥Y ⧸ Subgroup.center ↥Y) = 1 := by
        have h2 := congrArg Subtype.val (MonoidHom.mem_ker.1 hx)
        exact h2
      have hz : (x.1 : ↥Y) ∈ Subgroup.center ↥Y := (QuotientGroup.eq_one_iff _).1 h1
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      exact Subgroup.mem_center_iff.1 hz g.1
    have e1 : ↥(C.subgroupOf Y) ⧸ φ.ker ≃* ↥(Subgroup.map (QuotientGroup.mk' (Subgroup.center ↥Y))
        (C.subgroupOf Y)) := QuotientGroup.quotientKerEquivOfSurjective φ hφ
    have e3 := quotCenterCongr e1.symm
    have e4 := quotCenterEquiv φ.ker hker
    have e5 := quotCenterCongr (Subgroup.subgroupOfEquivOfLe hC_le_Y)
    obtain ⟨eM⟩ := hM
    exact ⟨e3.trans (e4.trans (e5.trans eM))⟩

end Reduction

end CFSG.Quasithin.H13.Ch4

end
