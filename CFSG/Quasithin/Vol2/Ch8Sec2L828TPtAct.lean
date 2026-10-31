module

public import CFSG.Quasithin.Vol2.Ch8Sec2L828TQMod
public import Mathlib.Tactic.Group
public import Mathlib.Order.ConditionallyCompleteLattice.Basic

public section

namespace CFSG.Quasithin.H13.L828T

open scoped commutatorElement IsMulCommutative

variable {G : Type*} [Group G]

abbrev QB (V B U : Subgroup G) [IsMulCommutative ↥V] : Type _ :=
  QMod (W := ↥V) (B.subgroupOf V) (U.subgroupOf V)

@[expose] def qb (V B U : Subgroup G) [IsMulCommutative ↥V] (b : ↥(B.subgroupOf V)) : QB V B U :=
  QMod.mk (W := ↥V) (B.subgroupOf V) (U.subgroupOf V) b

@[expose] def PtCong (V B U : Subgroup G) (h g : G) (b₁ b₂ β₁ β₂ : ↥(B.subgroupOf V)) : Prop :=
  g * (((b₁ : ↥V) : G) * h * ((b₂ : ↥V) : G) * h⁻¹) * g⁻¹ *
    (((β₁ : ↥V) : G) * h * ((β₂ : ↥V) : G) * h⁻¹)⁻¹ ∈ U

class PtActCentralAbelian (P U : Subgroup G) : Prop where
  central : ∀ u ∈ U, ∀ p ∈ P, p * u * p⁻¹ = u
  comm_mod : ∀ p ∈ P, ∀ q ∈ P, ⁅p, q⁆ ∈ U

structure PtActSetup (V B U P A : Subgroup G) (h : G) : Prop where
  hBV : B ≤ V
  hBP : B ≤ P
  hAP : A ≤ P
  hUA : U ≤ A
  hPeq : P = A ⊔ B
  hhU : ∀ u ∈ U, h * u * h⁻¹ = u
  hhB : ∀ b ∈ B, h * b * h⁻¹ ∈ A
  hhA : ∀ a ∈ A, h⁻¹ * a * h ∈ B
  hAB : A ⊓ B ≤ U

@[expose] instance ptActNormal (P U : Subgroup G) [PtActCentralAbelian P U] :
    (U.subgroupOf P).Normal :=
  ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
      PtActCentralAbelian.central (P := P) (U := U) _ hn _ g.2]
    exact hn⟩

theorem ptActMk_eq_iff (P U : Subgroup G) [PtActCentralAbelian P U] (a b : ↥P) :
    (QuotientGroup.mk a : ↥P ⧸ U.subgroupOf P) = QuotientGroup.mk b ↔
      (a : G) * (b : G)⁻¹ ∈ U := by
  rw [QuotientGroup.eq_iff_div_mem, Subgroup.mem_subgroupOf, div_eq_mul_inv,
    Subgroup.coe_mul, Subgroup.coe_inv]

instance ptActCommGroup (P U : Subgroup G) [PtActCentralAbelian P U] :
    CommGroup (↥P ⧸ U.subgroupOf P) :=
  { (inferInstance : Group (↥P ⧸ U.subgroupOf P)) with
    mul_comm := fun x y => by
      induction x using QuotientGroup.induction_on with
      | H a =>
        induction y using QuotientGroup.induction_on with
        | H b =>
          rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, ptActMk_eq_iff]
          have hc := PtActCentralAbelian.comm_mod (P := P) (U := U) (a : G) a.2 (b : G) b.2
          rw [commutatorElement_def] at hc
          convert hc using 1
          simp only [Subgroup.coe_mul, mul_inv_rev]
          group }

theorem ptActExists_mul_of_mem_sup {P U A B : Subgroup G} [PtActCentralAbelian P U]
    (hUA : U ≤ A) (hBP : B ≤ P) (hAP : A ≤ P) {p : G} (hp : p ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, p = a * b := by
  have hconj : ∀ b ∈ B, ∀ a ∈ A, b * a * b⁻¹ ∈ A := by
    intro b hb a ha
    have hc := PtActCentralAbelian.comm_mod (P := P) (U := U) b (hBP hb) a (hAP ha)
    rw [commutatorElement_def] at hc
    have e : b * a * b⁻¹ = (b * a * b⁻¹ * a⁻¹) * a := by group
    rw [e]
    exact A.mul_mem (hUA hc) ha
  let S : Subgroup G :=
    { carrier := {x | ∃ a ∈ A, ∃ b ∈ B, x = a * b}
      mul_mem' := by
        rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
        refine ⟨a * (b * a' * b⁻¹), A.mul_mem ha (hconj b hb a' ha'), b * b',
          B.mul_mem hb hb', ?_⟩
        group
      one_mem' := ⟨1, A.one_mem, 1, B.one_mem, by group⟩
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨b⁻¹ * a⁻¹ * b⁻¹⁻¹, hconj b⁻¹ (B.inv_mem hb) a⁻¹ (A.inv_mem ha), b⁻¹,
          B.inv_mem hb, ?_⟩
        group }
  have hle : A ⊔ B ≤ S :=
    sup_le (fun x hx => ⟨x, hx, 1, B.one_mem, by group⟩)
      (fun x hx => ⟨1, A.one_mem, x, hx, by group⟩)
  obtain ⟨a, ha, b, hb, hab⟩ := hle hp
  exact ⟨a, ha, b, hb, hab⟩

theorem ptActInj_core {h : G} {U A B : Subgroup G} (hUA : U ≤ A) (hAB : A ⊓ B ≤ U)
    (hhU : ∀ u ∈ U, h * u * h⁻¹ = u) (hhB : ∀ b ∈ B, h * b * h⁻¹ ∈ A) {b₁ b₂ : G}
    (hb₁ : b₁ ∈ B) (hb₂ : b₂ ∈ B) (hw : b₁ * (h * b₂ * h⁻¹) ∈ U) : b₁ ∈ U ∧ b₂ ∈ U := by
  have hwA : h * b₂ * h⁻¹ ∈ A := hhB b₂ hb₂
  have hb₁A : b₁ ∈ A := by
    have e : b₁ = b₁ * (h * b₂ * h⁻¹) * (h * b₂ * h⁻¹)⁻¹ := by group
    rw [e]
    exact A.mul_mem (hUA hw) (A.inv_mem hwA)
  have hb₁U : b₁ ∈ U := hAB ⟨hb₁A, hb₁⟩
  have hwU : h * b₂ * h⁻¹ ∈ U := by
    have e : h * b₂ * h⁻¹ = b₁⁻¹ * (b₁ * (h * b₂ * h⁻¹)) := by group
    rw [e]
    exact U.mul_mem (U.inv_mem hb₁U) hw
  have hinv : ∀ u ∈ U, h⁻¹ * u * h = u := by
    intro u hu
    have h1 : h * u * h⁻¹ = u := hhU u hu
    have h2 : h * u = u * h := by
      calc h * u = h * u * h⁻¹ * h := by group
        _ = u * h := by rw [h1]
    calc h⁻¹ * u * h = h⁻¹ * (u * h) := by group
      _ = h⁻¹ * (h * u) := by rw [h2]
      _ = u := by group
  have hb₂U : b₂ ∈ U := by
    have e : b₂ = h⁻¹ * (h * b₂ * h⁻¹) * h := by group
    rw [e, hinv _ hwU]
    exact hwU
  exact ⟨hb₁U, hb₂U⟩

@[expose] def ptActIncl (V B P : Subgroup G) (hBP : B ≤ P) : ↥(B.subgroupOf V) →* ↥P :=
  MonoidHom.mk' (fun b => ⟨((b : ↥V) : G), hBP (Subgroup.mem_subgroupOf.mp b.2)⟩)
    (fun a b => Subtype.ext (by simp))

@[expose] def ptActConjIncl (V B P A : Subgroup G) (h : G) (hAP : A ≤ P)
    (hhB : ∀ b ∈ B, h * b * h⁻¹ ∈ A) : ↥(B.subgroupOf V) →* ↥P :=
  MonoidHom.mk' (fun b => ⟨h * ((b : ↥V) : G) * h⁻¹, hAP (hhB _ (Subgroup.mem_subgroupOf.mp b.2))⟩)
    (fun a b => Subtype.ext (by simp [mul_assoc]))

theorem ptActLe_ker_of {V B U P : Subgroup G} [PtActCentralAbelian P U]
    (f : ↥(B.subgroupOf V) →* ↥P)
    (hf : ∀ x : ↥(B.subgroupOf V), x ∈ (U.subgroupOf V).subgroupOf (B.subgroupOf V) →
      (f x : G) ∈ U) :
    (U.subgroupOf V).subgroupOf (B.subgroupOf V) ≤
      ((QuotientGroup.mk' (U.subgroupOf P)).comp f).ker := by
  intro x hx
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  exact hf x hx

@[expose] def ptActF1 (V B U P : Subgroup G) [IsMulCommutative ↥V] [PtActCentralAbelian P U]
    (hBP : B ≤ P) : QB V B U →+ Additive (↥P ⧸ U.subgroupOf P) :=
  MonoidHom.toAdditive (QuotientGroup.lift ((U.subgroupOf V).subgroupOf (B.subgroupOf V))
    ((QuotientGroup.mk' (U.subgroupOf P)).comp (ptActIncl V B P hBP))
    (ptActLe_ker_of (ptActIncl V B P hBP) fun x hx =>
      Subgroup.mem_subgroupOf.mp (Subgroup.mem_subgroupOf.mp hx)))

@[expose] def ptActF2 (V B U P A : Subgroup G) (h : G) [IsMulCommutative ↥V]
    [PtActCentralAbelian P U] (hAP : A ≤ P) (hhB : ∀ b ∈ B, h * b * h⁻¹ ∈ A)
    (hhU : ∀ u ∈ U, h * u * h⁻¹ = u) :
    QB V B U →+ Additive (↥P ⧸ U.subgroupOf P) :=
  MonoidHom.toAdditive (QuotientGroup.lift ((U.subgroupOf V).subgroupOf (B.subgroupOf V))
    ((QuotientGroup.mk' (U.subgroupOf P)).comp (ptActConjIncl V B P A h hAP hhB))
    (ptActLe_ker_of (ptActConjIncl V B P A h hAP hhB) fun x hx => by
      have hu : ((x : ↥V) : G) ∈ U := Subgroup.mem_subgroupOf.mp (Subgroup.mem_subgroupOf.mp hx)
      show h * ((x : ↥V) : G) * h⁻¹ ∈ U
      rw [hhU _ hu]
      exact hu))

@[expose] def ptActTheta {V B U P A : Subgroup G} {h : G} [IsMulCommutative ↥V]
    [PtActCentralAbelian P U] (hyp : PtActSetup V B U P A h) :
    QB V B U × QB V B U →+ Additive (↥P ⧸ U.subgroupOf P) :=
  (ptActF1 V B U P hyp.hBP).coprod (ptActF2 V B U P A h hyp.hAP hyp.hhB hyp.hhU)

theorem ptActTheta_apply {V B U P A : Subgroup G} {h : G} [IsMulCommutative ↥V]
    [PtActCentralAbelian P U] (hyp : PtActSetup V B U P A h) (b₁ b₂ : ↥(B.subgroupOf V)) :
    ptActTheta hyp (qb V B U b₁, qb V B U b₂) =
      Additive.ofMul (QuotientGroup.mk (ptActIncl V B P hyp.hBP b₁ *
        ptActConjIncl V B P A h hyp.hAP hyp.hhB b₂) : ↥P ⧸ U.subgroupOf P) :=
  rfl

theorem ptActTheta_injective {V B U P A : Subgroup G} {h : G} [IsMulCommutative ↥V]
    [PtActCentralAbelian P U] (hyp : PtActSetup V B U P A h) :
    Function.Injective (ptActTheta hyp) := by
  rw [injective_iff_map_eq_zero]
  rintro ⟨x, y⟩ hxy
  obtain ⟨b₁, rfl⟩ : ∃ b, qb V B U b = x := QMod.mk_surjective _ _ x
  obtain ⟨b₂, rfl⟩ : ∃ b, qb V B U b = y := QMod.mk_surjective _ _ y
  rw [ptActTheta_apply, ofMul_eq_zero, QuotientGroup.eq_one_iff,
    Subgroup.mem_subgroupOf, Subgroup.coe_mul] at hxy
  obtain ⟨hb₁U, hb₂U⟩ := ptActInj_core hyp.hUA hyp.hAB hyp.hhU hyp.hhB
    (Subgroup.mem_subgroupOf.mp b₁.2) (Subgroup.mem_subgroupOf.mp b₂.2) hxy
  have hz : ∀ b : ↥(B.subgroupOf V), ((b : ↥V) : G) ∈ U → qb V B U b = 0 := by
    intro b hb
    show QMod.mk (B.subgroupOf V) (U.subgroupOf V) b = 0
    rw [← QMod.mk_one (B.subgroupOf V) (U.subgroupOf V), QMod.mk_eq_mk_iff,
      Subgroup.mem_subgroupOf]
    simpa using hb
  exact Prod.ext (hz b₁ hb₁U) (hz b₂ hb₂U)

theorem ptActTheta_surjective {V B U P A : Subgroup G} {h : G} [IsMulCommutative ↥V]
    [PtActCentralAbelian P U] (hyp : PtActSetup V B U P A h) :
    Function.Surjective (ptActTheta hyp) := by
  intro q
  obtain ⟨p, hp⟩ := QuotientGroup.mk_surjective (Additive.toMul q)
  have hpP : (p : G) ∈ A ⊔ B := by
    rw [← hyp.hPeq]
    exact p.2
  obtain ⟨a, ha, b, hb, hpab⟩ :=
    ptActExists_mul_of_mem_sup (P := P) (U := U) hyp.hUA hyp.hBP hyp.hAP hpP
  obtain ⟨b', hb'⟩ : ∃ b', b' = h⁻¹ * a * h := ⟨_, rfl⟩
  have hb'B : b' ∈ B := by
    rw [hb']
    exact hyp.hhA a ha
  have hae : h * b' * h⁻¹ = a := by
    rw [hb']
    group
  refine ⟨(qb V B U ⟨⟨b, hyp.hBV hb⟩, hb⟩, qb V B U ⟨⟨b', hyp.hBV hb'B⟩, hb'B⟩), ?_⟩
  rw [ptActTheta_apply]
  have hmk : (QuotientGroup.mk (ptActIncl V B P hyp.hBP ⟨⟨b, hyp.hBV hb⟩, hb⟩ *
      ptActConjIncl V B P A h hyp.hAP hyp.hhB ⟨⟨b', hyp.hBV hb'B⟩, hb'B⟩) :
        ↥P ⧸ U.subgroupOf P) = QuotientGroup.mk p := by
    rw [ptActMk_eq_iff]
    have hc := PtActCentralAbelian.comm_mod (P := P) (U := U) b (hyp.hBP hb) a (hyp.hAP ha)
    rw [commutatorElement_def] at hc
    have e : ((ptActIncl V B P hyp.hBP ⟨⟨b, hyp.hBV hb⟩, hb⟩ *
        ptActConjIncl V B P A h hyp.hAP hyp.hhB ⟨⟨b', hyp.hBV hb'B⟩, hb'B⟩ : ↥P) : G) *
          (p : G)⁻¹ = b * a * b⁻¹ * a⁻¹ := by
      change b * (h * b' * h⁻¹) * (p : G)⁻¹ = _
      rw [hae, hpab]
      group
    rw [e]
    exact hc
  rw [hmk, hp]
  exact ofMul_toMul q

@[expose] noncomputable def ptActThetaEquiv {V B U P A : Subgroup G} {h : G} [IsMulCommutative ↥V]
    [PtActCentralAbelian P U] (hyp : PtActSetup V B U P A h) :
    QB V B U × QB V B U ≃+ Additive (↥P ⧸ U.subgroupOf P) :=
  AddEquiv.ofBijective (ptActTheta hyp) ⟨ptActTheta_injective hyp, ptActTheta_surjective hyp⟩

@[expose] def ptActConjP (P : Subgroup G) (g : G) (hg : g ∈ Subgroup.normalizer (P : Set G)) :
    ↥P →* ↥P :=
  MonoidHom.mk' (fun x => ⟨g * (x : G) * g⁻¹, (Subgroup.mem_normalizer_iff.mp hg _).mp x.2⟩)
    (fun a b => Subtype.ext (by simp [mul_assoc]))

@[expose] noncomputable def ptActConj (P U : Subgroup G) [PtActCentralAbelian P U] (g : G)
    (hg : g ∈ Subgroup.normalizer (P : Set G)) (hgU : g ∈ Subgroup.normalizer (U : Set G)) :
    (↥P ⧸ U.subgroupOf P) →* (↥P ⧸ U.subgroupOf P) :=
  QuotientGroup.map (U.subgroupOf P) (U.subgroupOf P) (ptActConjP P g hg) (fun x hx => by
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
    exact (Subgroup.mem_normalizer_iff.mp hgU _).mp (Subgroup.mem_subgroupOf.mp hx))

theorem ptActConj_mk (P U : Subgroup G) [PtActCentralAbelian P U] (g : G)
    (hg : g ∈ Subgroup.normalizer (P : Set G)) (hgU : g ∈ Subgroup.normalizer (U : Set G))
    (a : ↥P) : ptActConj P U g hg hgU (QuotientGroup.mk a) =
      QuotientGroup.mk (ptActConjP P g hg a) :=
  rfl

theorem ptActConj_one (P U : Subgroup G) [PtActCentralAbelian P U]
    (hg : (1 : G) ∈ Subgroup.normalizer (P : Set G))
    (hgU : (1 : G) ∈ Subgroup.normalizer (U : Set G)) (q : ↥P ⧸ U.subgroupOf P) :
    ptActConj P U 1 hg hgU q = q := by
  induction q using QuotientGroup.induction_on with
  | H a =>
    rw [ptActConj_mk]
    congr 1
    exact Subtype.ext (by simp [ptActConjP])

theorem ptActConj_mul (P U : Subgroup G) [PtActCentralAbelian P U] (g g' : G)
    (hg : g ∈ Subgroup.normalizer (P : Set G)) (hg' : g' ∈ Subgroup.normalizer (P : Set G))
    (hgg' : g * g' ∈ Subgroup.normalizer (P : Set G))
    (hgU : g ∈ Subgroup.normalizer (U : Set G)) (hgU' : g' ∈ Subgroup.normalizer (U : Set G))
    (hgg'U : g * g' ∈ Subgroup.normalizer (U : Set G)) (q : ↥P ⧸ U.subgroupOf P) :
    ptActConj P U (g * g') hgg' hgg'U q =
      ptActConj P U g hg hgU (ptActConj P U g' hg' hgU' q) := by
  induction q using QuotientGroup.induction_on with
  | H a =>
    rw [ptActConj_mk, ptActConj_mk, ptActConj_mk]
    congr 1
    exact Subtype.ext (by simp [ptActConjP, mul_assoc])

theorem ptActConj_toAdditive_mk (P U : Subgroup G) [PtActCentralAbelian P U] (g : G)
    (hg : g ∈ Subgroup.normalizer (P : Set G)) (hgU : g ∈ Subgroup.normalizer (U : Set G))
    (a : ↥P) : MonoidHom.toAdditive (ptActConj P U g hg hgU) (Additive.ofMul (QuotientGroup.mk a)) =
      Additive.ofMul (QuotientGroup.mk (ptActConjP P g hg a)) :=
  rfl

theorem ptActConj_mul_toAdditive (P U : Subgroup G) [PtActCentralAbelian P U] (g g' : G)
    (hg : g ∈ Subgroup.normalizer (P : Set G)) (hg' : g' ∈ Subgroup.normalizer (P : Set G))
    (hgg' : g * g' ∈ Subgroup.normalizer (P : Set G))
    (hgU : g ∈ Subgroup.normalizer (U : Set G)) (hgU' : g' ∈ Subgroup.normalizer (U : Set G))
    (hgg'U : g * g' ∈ Subgroup.normalizer (U : Set G)) (y : Additive (↥P ⧸ U.subgroupOf P)) :
    MonoidHom.toAdditive (ptActConj P U (g * g') hgg' hgg'U) y =
      MonoidHom.toAdditive (ptActConj P U g hg hgU)
        (MonoidHom.toAdditive (ptActConj P U g' hg' hgU') y) :=
  congrArg Additive.ofMul (ptActConj_mul P U g g' hg hg' hgg' hgU hgU' hgg'U (Additive.toMul y))

theorem ptActConj_one_toAdditive (P U : Subgroup G) [PtActCentralAbelian P U]
    (hg : (1 : G) ∈ Subgroup.normalizer (P : Set G))
    (hgU : (1 : G) ∈ Subgroup.normalizer (U : Set G))
    (y : Additive (↥P ⧸ U.subgroupOf P)) :
    MonoidHom.toAdditive (ptActConj P U 1 hg hgU) y = y :=
  congrArg Additive.ofMul (ptActConj_one P U hg hgU (Additive.toMul y))

@[expose] noncomputable def ptActRho {V B U P A : Subgroup G} {h : G} [IsMulCommutative ↥V]
    [PtActCentralAbelian P U] (hyp : PtActSetup V B U P A h) (g : G)
    (hg : g ∈ Subgroup.normalizer (P : Set G) ⊓ Subgroup.normalizer (U : Set G)) :
    AddMonoid.End (QB V B U × QB V B U) :=
  (ptActThetaEquiv hyp).symm.toAddMonoidHom.comp
    ((MonoidHom.toAdditive (ptActConj P U g (Subgroup.mem_inf.mp hg).1
      (Subgroup.mem_inf.mp hg).2)).comp (ptActThetaEquiv hyp).toAddMonoidHom)

theorem ptActRho_apply {V B U P A : Subgroup G} {h : G} [IsMulCommutative ↥V]
    [PtActCentralAbelian P U] (hyp : PtActSetup V B U P A h) (g : G)
    (hg : g ∈ Subgroup.normalizer (P : Set G) ⊓ Subgroup.normalizer (U : Set G))
    (x : QB V B U × QB V B U) : ptActRho hyp g hg x =
      (ptActThetaEquiv hyp).symm (MonoidHom.toAdditive (ptActConj P U g (Subgroup.mem_inf.mp hg).1
        (Subgroup.mem_inf.mp hg).2) ((ptActThetaEquiv hyp) x)) :=
  rfl

theorem ptActCong_exists {V B U P A : Subgroup G} {h : G} [IsMulCommutative ↥V]
    [PtActCentralAbelian P U] (hyp : PtActSetup V B U P A h) (g : G)
    (hg : g ∈ Subgroup.normalizer (P : Set G) ⊓ Subgroup.normalizer (U : Set G))
    (b₁ b₂ : ↥(B.subgroupOf V)) :
    ∃ β₁ β₂ : ↥(B.subgroupOf V), PtCong V B U h g b₁ b₂ β₁ β₂ := by
  have hgP : ∀ x : G, x ∈ P ↔ g * x * g⁻¹ ∈ P :=
    Subgroup.mem_normalizer_iff.mp (Subgroup.mem_inf.mp hg).1
  have hx1 : ((b₁ : ↥V) : G) * (h * ((b₂ : ↥V) : G) * h⁻¹) ∈ P :=
    P.mul_mem (hyp.hBP (Subgroup.mem_subgroupOf.mp b₁.2))
      (hyp.hAP (hyp.hhB _ (Subgroup.mem_subgroupOf.mp b₂.2)))
  have hzP : g * (((b₁ : ↥V) : G) * (h * ((b₂ : ↥V) : G) * h⁻¹)) * g⁻¹ ∈ P :=
    (hgP _).mp hx1
  obtain ⟨⟨x₁, x₂⟩, hx⟩ := ptActTheta_surjective hyp
    (Additive.ofMul (QuotientGroup.mk ⟨_, hzP⟩ : ↥P ⧸ U.subgroupOf P))
  obtain ⟨β₁, rfl⟩ : ∃ b, qb V B U b = x₁ := QMod.mk_surjective _ _ x₁
  obtain ⟨β₂, rfl⟩ : ∃ b, qb V B U b = x₂ := QMod.mk_surjective _ _ x₂
  rw [ptActTheta_apply] at hx
  have h2 := (ptActMk_eq_iff P U _ _).mp (Additive.ofMul.injective hx).symm
  refine ⟨β₁, β₂, ?_⟩
  have h4 : g * (((b₁ : ↥V) : G) * (h * ((b₂ : ↥V) : G) * h⁻¹)) * g⁻¹ *
      ((((β₁ : ↥V) : G) * (h * ((β₂ : ↥V) : G) * h⁻¹)))⁻¹ ∈ U := h2
  unfold PtCong
  simpa only [mul_assoc] using h4

theorem ptActRho_of_cong {V B U P A : Subgroup G} {h : G} [IsMulCommutative ↥V]
    [PtActCentralAbelian P U] (hyp : PtActSetup V B U P A h) (g : G)
    (hg : g ∈ Subgroup.normalizer (P : Set G) ⊓ Subgroup.normalizer (U : Set G))
    (b₁ b₂ β₁ β₂ : ↥(B.subgroupOf V)) (hc : PtCong V B U h g b₁ b₂ β₁ β₂) :
    ptActRho hyp g hg (qb V B U b₁, qb V B U b₂) = (qb V B U β₁, qb V B U β₂) := by
  rw [ptActRho_apply, AddEquiv.symm_apply_eq]
  change MonoidHom.toAdditive (ptActConj P U g (Subgroup.mem_inf.mp hg).1
      (Subgroup.mem_inf.mp hg).2) (ptActTheta hyp (qb V B U b₁, qb V B U b₂)) =
    ptActTheta hyp (qb V B U β₁, qb V B U β₂)
  rw [ptActTheta_apply, ptActTheta_apply, ptActConj_toAdditive_mk]
  congr 1
  rw [ptActMk_eq_iff]
  show g * (((b₁ : ↥V) : G) * (h * ((b₂ : ↥V) : G) * h⁻¹)) * g⁻¹ *
    ((((β₁ : ↥V) : G) * (h * ((β₂ : ↥V) : G) * h⁻¹)))⁻¹ ∈ U
  unfold PtCong at hc
  simpa only [mul_assoc] using hc

theorem ptActRho_eq_one_iff {V B U P A : Subgroup G} {h : G} [IsMulCommutative ↥V]
    [PtActCentralAbelian P U] (hyp : PtActSetup V B U P A h) (g : G)
    (hg : g ∈ Subgroup.normalizer (P : Set G) ⊓ Subgroup.normalizer (U : Set G)) :
    ptActRho hyp g hg = 1 ↔ ∀ p ∈ P, g * p * g⁻¹ * p⁻¹ ∈ U := by
  constructor
  · intro h1 p hp
    have hx := DFunLike.congr_fun h1
      ((ptActThetaEquiv hyp).symm (Additive.ofMul (QuotientGroup.mk ⟨p, hp⟩ : ↥P ⧸ U.subgroupOf P)))
    rw [ptActRho_apply, AddEquiv.apply_symm_apply] at hx
    have hx' : (ptActThetaEquiv hyp).symm (MonoidHom.toAdditive (ptActConj P U g
        (Subgroup.mem_inf.mp hg).1 (Subgroup.mem_inf.mp hg).2)
          (Additive.ofMul (QuotientGroup.mk ⟨p, hp⟩ : ↥P ⧸ U.subgroupOf P))) =
        (ptActThetaEquiv hyp).symm
          (Additive.ofMul (QuotientGroup.mk ⟨p, hp⟩ : ↥P ⧸ U.subgroupOf P)) :=
      hx
    have hc := (ptActThetaEquiv hyp).symm.injective hx'
    rw [ptActConj_toAdditive_mk] at hc
    exact (ptActMk_eq_iff P U _ _).mp (Additive.ofMul.injective hc)
  · intro hp
    refine AddMonoidHom.ext fun x => ?_
    show ptActRho hyp g hg x = x
    obtain ⟨p, hpq⟩ := QuotientGroup.mk_surjective (Additive.toMul ((ptActThetaEquiv hyp) x))
    have hy : (ptActThetaEquiv hyp) x = Additive.ofMul (QuotientGroup.mk p) := by
      rw [hpq]
      exact (ofMul_toMul _).symm
    have hc : MonoidHom.toAdditive (ptActConj P U g (Subgroup.mem_inf.mp hg).1
        (Subgroup.mem_inf.mp hg).2) ((ptActThetaEquiv hyp) x) = (ptActThetaEquiv hyp) x := by
      rw [hy, ptActConj_toAdditive_mk]
      congr 1
      exact (ptActMk_eq_iff P U _ _).mpr (hp (p : G) p.2)
    rw [ptActRho_apply, hc, AddEquiv.symm_apply_apply]

theorem ptActRho_one {V B U P A : Subgroup G} {h : G} [IsMulCommutative ↥V]
    [PtActCentralAbelian P U] (hyp : PtActSetup V B U P A h)
    (hg : (1 : G) ∈ Subgroup.normalizer (P : Set G) ⊓ Subgroup.normalizer (U : Set G)) :
    ptActRho hyp 1 hg = 1 := by
  refine AddMonoidHom.ext fun x => ?_
  show ptActRho hyp 1 hg x = x
  rw [ptActRho_apply]
  have hc := ptActConj_one_toAdditive P U (Subgroup.mem_inf.mp hg).1 (Subgroup.mem_inf.mp hg).2
  rw [hc, AddEquiv.symm_apply_apply]

theorem ptActRho_mul {V B U P A : Subgroup G} {h : G} [IsMulCommutative ↥V]
    [PtActCentralAbelian P U] (hyp : PtActSetup V B U P A h) (g g' : G)
    (hg : g ∈ Subgroup.normalizer (P : Set G) ⊓ Subgroup.normalizer (U : Set G))
    (hg' : g' ∈ Subgroup.normalizer (P : Set G) ⊓ Subgroup.normalizer (U : Set G))
    (hgg' : g * g' ∈ Subgroup.normalizer (P : Set G) ⊓ Subgroup.normalizer (U : Set G)) :
    ptActRho hyp (g * g') hgg' = ptActRho hyp g hg * ptActRho hyp g' hg' := by
  refine AddMonoidHom.ext fun x => ?_
  show ptActRho hyp (g * g') hgg' x = ptActRho hyp g hg (ptActRho hyp g' hg' x)
  rw [ptActRho_apply, ptActRho_apply, ptActRho_apply, AddEquiv.apply_symm_apply]
  congr 1
  exact ptActConj_mul_toAdditive P U g g' (Subgroup.mem_inf.mp hg).1 (Subgroup.mem_inf.mp hg').1
    (Subgroup.mem_inf.mp hgg').1 (Subgroup.mem_inf.mp hg).2 (Subgroup.mem_inf.mp hg').2
    (Subgroup.mem_inf.mp hgg').2 _

@[expose] noncomputable def ptActRhoHom {V B U P A : Subgroup G} {h : G} [IsMulCommutative ↥V]
    [PtActCentralAbelian P U] (hyp : PtActSetup V B U P A h) :
    ↥(Subgroup.normalizer (P : Set G) ⊓ Subgroup.normalizer (U : Set G)) →*
      AddMonoid.End (QB V B U × QB V B U) where
  toFun g := ptActRho hyp g.1 g.2
  map_one' := ptActRho_one hyp (Subgroup.one_mem _)
  map_mul' g g' := ptActRho_mul hyp g.1 g'.1 g.2 g'.2 (mul_mem g.2 g'.2)

theorem exists_ptAct_surj {V B U P A : Subgroup G} {h : G} [IsMulCommutative ↥V]
    (hBV : B ≤ V) (hBP : B ≤ P) (hAP : A ≤ P) (hUA : U ≤ A) (hPeq : P = A ⊔ B)
    (hP2 : ∀ p ∈ P, ∀ q ∈ P, ⁅p, q⁆ ∈ U)
    (hPU : ∀ u ∈ U, ∀ p ∈ P, p * u * p⁻¹ = u) (hhU : ∀ u ∈ U, h * u * h⁻¹ = u)
    (hhB : ∀ b ∈ B, h * b * h⁻¹ ∈ A) (hhA : ∀ a ∈ A, h⁻¹ * a * h ∈ B) (hAB : A ⊓ B ≤ U) :
    ∀ p ∈ P, ∃ b₁ b₂ : ↥(B.subgroupOf V),
      p * (((b₁ : ↥V) : G) * h * ((b₂ : ↥V) : G) * h⁻¹)⁻¹ ∈ U := by
  haveI : PtActCentralAbelian P U := ⟨hPU, hP2⟩
  have hyp : PtActSetup V B U P A h := ⟨hBV, hBP, hAP, hUA, hPeq, hhU, hhB, hhA, hAB⟩
  intro p hp
  obtain ⟨⟨x₁, x₂⟩, hx⟩ := ptActTheta_surjective hyp
    (Additive.ofMul (QuotientGroup.mk ⟨p, hp⟩ : ↥P ⧸ U.subgroupOf P))
  obtain ⟨β₁, rfl⟩ : ∃ b, qb V B U b = x₁ := QMod.mk_surjective _ _ x₁
  obtain ⟨β₂, rfl⟩ : ∃ b, qb V B U b = x₂ := QMod.mk_surjective _ _ x₂
  rw [ptActTheta_apply] at hx
  have h2 := (ptActMk_eq_iff P U _ _).mp (Additive.ofMul.injective hx)
  refine ⟨β₁, β₂, ?_⟩
  have h3 : ((((β₁ : ↥V) : G) * (h * ((β₂ : ↥V) : G) * h⁻¹)) * (p : G)⁻¹)⁻¹ ∈ U :=
    U.inv_mem h2
  have e : (p : G) * (((β₁ : ↥V) : G) * h * ((β₂ : ↥V) : G) * h⁻¹)⁻¹ =
      ((((β₁ : ↥V) : G) * (h * ((β₂ : ↥V) : G) * h⁻¹)) * (p : G)⁻¹)⁻¹ := by
    group
  rw [e]
  exact h3

theorem exists_ptAct {V B U P A : Subgroup G} {h : G} [IsMulCommutative ↥V]
    (hUB : U ≤ B) (hBV : B ≤ V) (hBP : B ≤ P) (hAP : A ≤ P) (hUA : U ≤ A)
    (hPeq : P = A ⊔ B) (hP2 : ∀ p ∈ P, ∀ q ∈ P, ⁅p, q⁆ ∈ U)
    (hPU : ∀ u ∈ U, ∀ p ∈ P, p * u * p⁻¹ = u)
    (hhP : h ∈ Subgroup.normalizer (P : Set G)) (hhU : ∀ u ∈ U, h * u * h⁻¹ = u)
    (hhB : ∀ b ∈ B, h * b * h⁻¹ ∈ A) (hhA : ∀ a ∈ A, h⁻¹ * a * h ∈ B) (hAB : A ⊓ B ≤ U) :
    ∃ ρ : ↥(Subgroup.normalizer (P : Set G) ⊓ Subgroup.normalizer (U : Set G)) →*
        AddMonoid.End (QB V B U × QB V B U),
      (∀ (g : ↥(Subgroup.normalizer (P : Set G) ⊓ Subgroup.normalizer (U : Set G)))
          (b₁ b₂ : ↥(B.subgroupOf V)),
        ∃ β₁ β₂ : ↥(B.subgroupOf V), PtCong V B U h g b₁ b₂ β₁ β₂) ∧
      (∀ (g : ↥(Subgroup.normalizer (P : Set G) ⊓ Subgroup.normalizer (U : Set G)))
          (b₁ b₂ β₁ β₂ : ↥(B.subgroupOf V)), PtCong V B U h g b₁ b₂ β₁ β₂ →
        ρ g (qb V B U b₁, qb V B U b₂) = (qb V B U β₁, qb V B U β₂)) ∧
      (∀ g : ↥(Subgroup.normalizer (P : Set G) ⊓ Subgroup.normalizer (U : Set G)),
        ρ g = 1 ↔ ∀ p ∈ P, (g : G) * p * (g : G)⁻¹ * p⁻¹ ∈ U) := by
  haveI : PtActCentralAbelian P U := ⟨hPU, hP2⟩
  have hyp : PtActSetup V B U P A h := ⟨hBV, hBP, hAP, hUA, hPeq, hhU, hhB, hhA, hAB⟩
  exact ⟨ptActRhoHom hyp, fun g b₁ b₂ => ptActCong_exists hyp g.1 g.2 b₁ b₂,
    fun g b₁ b₂ β₁ β₂ hc => ptActRho_of_cong hyp g.1 g.2 b₁ b₂ β₁ β₂ hc,
    fun g => ptActRho_eq_one_iff hyp g.1 g.2⟩

end CFSG.Quasithin.H13.L828T
