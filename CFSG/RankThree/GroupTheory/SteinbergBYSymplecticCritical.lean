module

public import CFSG.GroupTheory.SteinbergBWCritical
public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergBXSymplecticCentralProduct

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.RankThree.GroupTheory.SteinbergBY

open Subgroup CFSG.SectionRank.Ccomm CFSG.LocalAnalysis.GorensteinLyons
open scoped commutatorElement

variable {P : Type*} [Group P]

theorem characteristic_map_subtype {H : Subgroup P} (hH : H.Characteristic) {K : Subgroup H}
    (hK : K.Characteristic) : (K.map H.subtype).Characteristic := by
  rw [characteristic_iff_map_eq]
  intro φ
  have hHmap : H.map φ.toMonoidHom = H := characteristic_iff_map_eq.mp hH φ
  let φH : H ≃* H := (φ.subgroupMap H).trans (MulEquiv.subgroupCongr hHmap)
  have hKmap : K.map φH.toMonoidHom = K := characteristic_iff_map_eq.mp hK φH
  have hcomp : φ.toMonoidHom.comp H.subtype = H.subtype.comp φH.toMonoidHom := by
    ext x
    rfl
  rw [map_map, hcomp, ← map_map, hKmap]

theorem glaSymplecticType_of_characteristic (hP : IsPGroup 2 P)
    (hsymp : ∀ A : Subgroup P, A.Characteristic → IsMulCommutative A → IsCyclic A)
    {D : Subgroup P} (hD : D.Characteristic) : CFSG.Open.GLASymplecticType D := by
  refine ⟨hP.to_subgroup D, fun A hA hAc => ?_⟩
  set e := A.equivMapOfInjective D.subtype D.subtype_injective
  have hcomm : IsMulCommutative (A.map D.subtype) := by
    refine ⟨⟨fun a b => ?_⟩⟩
    obtain ⟨a', rfl⟩ := e.surjective a
    obtain ⟨b', rfl⟩ := e.surjective b
    rw [← map_mul, ← map_mul, hAc.is_comm.comm a' b']
  exact e.isCyclic.mpr (hsymp _ (characteristic_map_subtype hD hA) hcomm)

theorem frattini_le_center_of_thompsonCritical {D : Subgroup P} (hD : ThompsonCritical D) :
    frattini D ≤ center D := by
  have h := hD.2.1
  rw [← map_center_subtype] at h
  exact (map_le_map_iff_of_injective D.subtype_injective).mp h

theorem centralizer_eq_of_thompsonCritical {D : Subgroup P} (hD : ThompsonCritical D) :
    centralizer (D : Set P) = (center D).map D.subtype := by
  rw [map_center_subtype]
  exact hD.2.2.2

theorem commutator_le_of_thompsonCritical {D : Subgroup P} (hD : ThompsonCritical D) :
    ⁅(⊤ : Subgroup P), D⁆ ≤ (center D).map D.subtype := by
  rw [map_center_subtype]
  exact hD.2.2.1

theorem map_center_le_centralizer (D : Subgroup P) :
    (center D).map D.subtype ≤ centralizer (D : Set P) := by
  rw [map_center_subtype]
  exact inf_le_right

theorem map_center_le (D : Subgroup P) : (center D).map D.subtype ≤ D := by
  rw [map_center_subtype]
  exact inf_le_left

theorem mem_center_of_unique_involution {Z : Subgroup P} (hZ : Z.Characteristic) {z : P}
    (hzZ : z ∈ Z) (hz : orderOf z = 2) (huniq : ∀ x ∈ Z, orderOf x = 2 → x = z) :
    z ∈ center P := by
  rw [mem_center_iff]
  intro g
  have hmem : g * z * g⁻¹ ∈ Z := (normal_of_characteristic Z).conj_mem z hzZ g
  have hord : orderOf (g * z * g⁻¹) = 2 := by
    rw [← hz, ← MulAut.conj_apply]
    exact orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective z
  have h := huniq _ hmem hord
  calc g * z = g * z * g⁻¹ * g := by group
    _ = z * g := by rw [h]

open scoped IsMulCommutative in
theorem exists_inner_of_conj_mem_zpowers [Finite P] {E : Subgroup P} {z : P} (hzE : z ∈ E)
    (hz : orderOf z = 2) (hzc : z ∈ center P) (hcomm : ∀ x ∈ E, ∀ y ∈ E, ⁅x, y⁆ ∈ zpowers z)
    (hsq : ∀ x ∈ E, x ^ 2 ∈ zpowers z) (hcen : (center E).map E.subtype = zpowers z)
    {g : P} (hg : ∀ e ∈ E, e⁻¹ * (g * e * g⁻¹) ∈ zpowers z) :
    ∃ t ∈ E, ∀ e ∈ E, t * e * t⁻¹ = g * e * g⁻¹ := by
  classical
  set zE : E := ⟨z, hzE⟩ with hzEdef
  have hzpE : zpowers z ≤ E := zpowers_le.mpr hzE
  have hzpc : zpowers z ≤ center P := zpowers_le.mpr hzc
  have hmemcen : ∀ x : E, (x : P) ∈ zpowers z → x ∈ center E := by
    intro x hx
    rw [← hcen] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    rwa [← Subtype.ext hyx]
  have hpair : ∀ x : E, (x : P) ∈ zpowers z → x = 1 ∨ x = zE := by
    intro x hx
    rcases eq_one_or_eq_of_mem_zpowers_of_orderOf_eq_two hz hx with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)
  have H : CommPairHyp E zE :=
    { mem_center := hmemcen zE (mem_zpowers z)
      orderOf_eq := by rw [hzEdef, Subgroup.orderOf_mk, hz]
      comm_pair := fun a b => hpair _ (hcomm a a.2 b b.2)
      sq_mem_center := fun a => hmemcen _ (hsq a a.2) }
  have := H.isElementaryAbelian_quotient
  let cE : E → E := fun e => ⟨(e : P)⁻¹ * (g * e * g⁻¹), hzpE (hg e e.2)⟩
  have hc01 : ∀ e : E, cE e = 1 ∨ cE e = zE := fun e => hpair _ (hg e e.2)
  have hcmul : ∀ e e' : E, cE (e * e') = cE e * cE e' := by
    intro e e'
    apply Subtype.ext
    have hc := mem_center_iff.mp (hzpc (hg e e.2))
    change ((e : P) * e')⁻¹ * (g * ((e : P) * e') * g⁻¹) =
      ((e : P)⁻¹ * (g * e * g⁻¹)) * ((e' : P)⁻¹ * (g * e' * g⁻¹))
    calc ((e : P) * e')⁻¹ * (g * ((e : P) * e') * g⁻¹)
        = (e' : P)⁻¹ * ((e : P)⁻¹ * (g * e * g⁻¹)) * (g * e' * g⁻¹) := by group
      _ = ((e : P)⁻¹ * (g * e * g⁻¹)) * (e' : P)⁻¹ * (g * e' * g⁻¹) := by
          rw [hc (e' : P)⁻¹]
      _ = ((e : P)⁻¹ * (g * e * g⁻¹)) * ((e' : P)⁻¹ * (g * e' * g⁻¹)) := by
          rw [mul_assoc]
  have hccen : ∀ (e : E) (s : E), s ∈ center E → cE (e * s) = cE e := by
    intro e s hs
    rw [hcmul]
    have hs' : (s : P) ∈ center P := by
      apply hzpc
      rw [← hcen]
      exact ⟨s, hs, rfl⟩
    have h1 : cE s = 1 := by
      apply Subtype.ext
      change (s : P)⁻¹ * (g * s * g⁻¹) = 1
      rw [mem_center_iff.mp hs' g, mul_assoc, mul_inv_cancel, mul_one, inv_mul_cancel]
    rw [h1, mul_one]
  let φf : Additive (E ⧸ center E) → ZMod 2 := fun u =>
    zlog zE (cE (Quotient.out (Additive.toMul u)))
  have hφmk : ∀ y : E, φf (Additive.ofMul (y : E ⧸ center E)) = zlog zE (cE y) := by
    intro y
    obtain ⟨s, hs⟩ := QuotientGroup.mk_out_eq_mul (center E) y
    simp only [φf, toMul_ofMul, hs, hccen y s s.2]
  have hsurj : ∀ u : Additive (E ⧸ center E), ∃ y : E, u = Additive.ofMul (y : E ⧸ center E) := by
    intro u
    obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective (Additive.toMul u)
    exact ⟨y, by rw [hy]; rfl⟩
  have hφadd : ∀ u v, φf (u + v) = φf u + φf v := by
    intro u v
    obtain ⟨a, rfl⟩ := hsurj u
    obtain ⟨b, rfl⟩ := hsurj v
    rw [show Additive.ofMul (a : E ⧸ center E) + Additive.ofMul (b : E ⧸ center E) =
      Additive.ofMul ((a * b : E) : E ⧸ center E) from rfl, hφmk, hφmk, hφmk, hcmul]
    exact H.zlog_mul (hc01 a) (hc01 b)
  have : Module.Finite (ZMod 2) (Additive (E ⧸ center E)) := Module.Finite.of_finite
  let φl : Module.Dual (ZMod 2) (Additive (E ⧸ center E)) :=
    AddMonoidHom.toZModLinearMap 2 (AddMonoidHom.mk' φf hφadd)
  set u := (H.commForm.toDual H.commForm_nondegenerate).symm φl with hu
  have huv : ∀ v, H.commForm u v = φf v := by
    intro v
    rw [← LinearMap.BilinForm.toDual_def H.commForm_nondegenerate, hu,
      LinearEquiv.apply_symm_apply]
    rfl
  obtain ⟨t, ht⟩ := hsurj u
  refine ⟨t, t.2, fun e he => ?_⟩
  have h1 := huv (Additive.ofMul ((⟨e, he⟩ : E) : E ⧸ center E))
  rw [hφmk, ht, H.commForm_apply, toMul_ofMul, toMul_ofMul, H.commVal_mk] at h1
  have h2 : ⁅t, (⟨e, he⟩ : E)⁆ = cE ⟨e, he⟩ := by
    rw [H.eq_zpow_zlog (H.comm_pair _ _), h1, ← H.eq_zpow_zlog (hc01 _)]
  have h3 : ⁅(⟨e, he⟩ : E)⁻¹, t⁆ = cE ⟨e, he⟩ := by
    rw [H.comm_inv_left, H.comm_symm, h2]
  have h4 := congrArg Subtype.val h3
  change e⁻¹ * t * e⁻¹⁻¹ * (t : P)⁻¹ = e⁻¹ * (g * e * g⁻¹) at h4
  rw [inv_inv, mul_assoc, mul_assoc, mul_left_cancel_iff, ← mul_assoc] at h4
  exact h4

theorem ker_conjNormal (Z : Subgroup P) [Z.Normal] :
    (MulAut.conjNormal (H := Z)).ker = centralizer (Z : Set P) := by
  ext g
  rw [MonoidHom.mem_ker, mem_centralizer_iff]
  constructor
  · intro h x hx
    have h1 := congrArg (fun f : MulAut Z => ((f ⟨x, hx⟩ : Z) : P)) h
    simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h1
    calc x * g = g * x * g⁻¹ * g := by rw [h1]
      _ = g * x := by group
  · intro h
    ext x
    rw [MulAut.conjNormal_apply, MulAut.one_apply, ← h x x.2]
    group

theorem ker_conjNormal_comp_subtype (Z R : Subgroup P) [Z.Normal]
    (hRZ : R ⊓ centralizer (Z : Set P) = Z) :
    ((MulAut.conjNormal (H := Z)).comp R.subtype).ker = Z.subgroupOf R := by
  ext r
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, ker_conjNormal,
    mem_subgroupOf]
  have h := Subgroup.ext_iff.mp hRZ (r : P)
  exact ⟨fun h' => h.mp ⟨r.2, h'⟩, fun h' => (h.mpr h').2⟩

theorem symplectic_critical_subgroup_central_product [Finite P] [Nontrivial P]
    (hP : IsPGroup 2 P)
    (hsymp : ∀ A : Subgroup P, A.Characteristic → IsMulCommutative A → IsCyclic A) :
    (∃ D : Subgroup P, D ≠ ⊥ ∧ ThompsonCritical D) ∧
    ∀ D : Subgroup P, ThompsonCritical D →
      (center D).map D.subtype ≠ ⊥ ∧ IsCyclic ((center D).map D.subtype) ∧
      ((center D).map D.subtype).Characteristic ∧
      ∃ z ∈ (center D).map D.subtype, orderOf z = 2 ∧
        (∀ x ∈ (center D).map D.subtype, orderOf x = 2 → x = z) ∧
        z ∈ center P ∧ (∀ x ∈ center P, orderOf x = 2 → x = z) ∧
        centralizer ((center D).map D.subtype : Set P) = D ∧
        ∃ E R : Subgroup P, E ⊔ (center D).map D.subtype = D ∧
          R = centralizer (E : Set P) ∧ E ⊔ R = ⊤ ∧ ⁅E, R⁆ = ⊥ ∧
          R ⊓ centralizer ((center D).map D.subtype : Set P) = (center D).map D.subtype ∧
          E.Normal ∧ R.Normal ∧
          ((IsCyclic D ∧ E = ⊥ ∧ R = ⊤) ∨
            ∃ w : ℕ, 1 ≤ w ∧ CFSG.IsElementaryAbelian 2 (D ⧸ center D) ∧
              Nat.card (D ⧸ center D) = 2 ^ (2 * w) ∧
              (∀ w' : ℕ, Nat.card (D ⧸ center D) = 2 ^ (2 * w') → w' = w) ∧
              IsExtraspecialPGroup 2 E ∧ Nat.card E = 2 ^ (1 + 2 * w) ∧
              (∀ e ∈ E, e ^ 4 = 1) ∧ E ⊓ R = zpowers z ∧
              E ⊓ (center D).map D.subtype = zpowers z ∧
              (center E).map E.subtype = zpowers z ∧
              ∃ b : D ⧸ center D → D ⧸ center D → ZMod 2,
                (∀ u v t, b (u * v) t = b u t + b v t) ∧
                (∀ u v t, b u (v * t) = b u v + b u t) ∧
                (∀ u, b u u = 0) ∧ (∀ u, (∀ v, b u v = 0) → u = 1) ∧
                ∀ x y : D, (x : P)⁻¹ * (y : P)⁻¹ * x * y =
                  z ^ (b (x : D ⧸ center D) (y : D ⧸ center D)).val) ∧
          (∃ φ : P →* MulAut ((center D).map D.subtype),
            (∀ (g : P) (x : (center D).map D.subtype),
              ((φ g x : (center D).map D.subtype) : P) = g * x * g⁻¹) ∧ φ.ker = D) ∧
          ∃ ψ : R →* MulAut ((center D).map D.subtype),
            (∀ (r : R) (x : (center D).map D.subtype),
              ((ψ r x : (center D).map D.subtype) : P) = r * x * r⁻¹) ∧
            ψ.ker = ((center D).map D.subtype).subgroupOf R := by
  classical
  refine ⟨?_, fun D hD => ?_⟩
  · obtain ⟨⟨D, hD⟩, hnt⟩ := CFSG.GroupTheory.PG.exists_thompsonCritical hP
    exact ⟨D, hnt inferInstance D hD, hD⟩
  set Z := (center D).map D.subtype with hZdef
  have hDchar : D.Characteristic := hD.1
  have hD0 : D ≠ ⊥ := (CFSG.GroupTheory.PG.exists_thompsonCritical hP).2 inferInstance D hD
  have hZchar : Z.Characteristic := characteristic_map_subtype hDchar inferInstance
  have : Z.Normal := normal_of_characteristic Z
  have hZD : Z ≤ D := map_center_le D
  have hZcD : Z ≤ centralizer (D : Set P) := map_center_le_centralizer D
  have hDcZ : D ≤ centralizer (Z : Set P) := le_centralizer_iff.mp hZcD
  have hcD : centralizer (D : Set P) = Z := centralizer_eq_of_thompsonCritical hD
  have hcomm : ⁅(⊤ : Subgroup P), D⁆ ≤ Z := commutator_le_of_thompsonCritical hD
  have hDs := glaSymplecticType_of_characteristic hP hsymp hDchar
  have hΦ := frattini_le_center_of_thompsonCritical hD
  obtain ⟨hcyc, z, hzZ, hz, huniq, hab, hnab⟩ :=
    symplectic_central_frattini_central_product hD0 hDs hΦ
  have hzc : z ∈ center P := mem_center_of_unique_involution hZchar hzZ hz huniq
  have hcycP : IsCyclic (center P) := hsymp (center P) inferInstance inferInstance
  have huniqP : ∀ x ∈ center P, orderOf x = 2 → x = z := by
    intro x hx hx2
    have hx' := mem_zpowers_of_sq_eq_one hcycP hzc hz hx
      (by rw [← hx2]; exact pow_orderOf_eq_one x)
    rcases eq_one_or_eq_of_mem_zpowers_of_orderOf_eq_two hz hx' with h | h
    · rw [h, orderOf_one] at hx2
      exact absurd hx2 (by norm_num)
    · exact h
  have hZ0 : Z ≠ ⊥ := by
    intro h
    have hzZ' : z ∈ Z := hzZ
    rw [h, mem_bot] at hzZ'
    rw [hzZ', orderOf_one] at hz
    exact absurd hz (by norm_num)
  have hZab : Z ≤ centralizer (Z : Set P) := fun y hy =>
    mem_centralizer_iff.mpr fun x hx => mem_centralizer_iff.mp (hZcD hy) x (hZD hx)
  obtain ⟨E, R, hEZ, hR, hER, hERc, hRZ, hEn, hRn, hcases, hcZ⟩ :
      ∃ E R : Subgroup P, E ⊔ Z = D ∧ R = centralizer (E : Set P) ∧ E ⊔ R = ⊤ ∧ ⁅E, R⁆ = ⊥ ∧
        R ⊓ centralizer (Z : Set P) = Z ∧ E.Normal ∧ R.Normal ∧
        ((IsCyclic D ∧ E = ⊥ ∧ R = ⊤) ∨
          ∃ w : ℕ, 1 ≤ w ∧ CFSG.IsElementaryAbelian 2 (D ⧸ center D) ∧
            Nat.card (D ⧸ center D) = 2 ^ (2 * w) ∧
            (∀ w' : ℕ, Nat.card (D ⧸ center D) = 2 ^ (2 * w') → w' = w) ∧
            IsExtraspecialPGroup 2 E ∧ Nat.card E = 2 ^ (1 + 2 * w) ∧
            (∀ e ∈ E, e ^ 4 = 1) ∧ E ⊓ R = zpowers z ∧ E ⊓ Z = zpowers z ∧
            (center E).map E.subtype = zpowers z ∧
            ∃ b : D ⧸ center D → D ⧸ center D → ZMod 2,
              (∀ u v t, b (u * v) t = b u t + b v t) ∧
              (∀ u v t, b u (v * t) = b u v + b u t) ∧
              (∀ u, b u u = 0) ∧ (∀ u, (∀ v, b u v = 0) → u = 1) ∧
              ∀ x y : D, (x : P)⁻¹ * (y : P)⁻¹ * x * y =
                z ^ (b (x : D ⧸ center D) (y : D ⧸ center D)).val) ∧
        centralizer (Z : Set P) = D := by
    by_cases hD_ab : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x
    ·
      have hDZ : D = Z := hab hD_ab
      have hDcyc : IsCyclic D :=
        hsymp D hDchar { is_comm := ⟨fun a b => Subtype.ext (hD_ab a a.2 b b.2)⟩ }
      have hcR : centralizer ((⊥ : Subgroup P) : Set P) = ⊤ := by
        rw [eq_top_iff]
        intro g _
        rw [mem_centralizer_iff]
        intro h hh
        rw [SetLike.mem_coe, mem_bot] at hh
        rw [hh, one_mul, mul_one]
      have hcZ : centralizer (Z : Set P) = D := by rw [← hDZ, hcD, hDZ]
      refine ⟨⊥, ⊤, by rw [bot_sup_eq, hDZ], hcR.symm, bot_sup_eq _, commutator_bot_left _,
        by rw [top_inf_eq, hcZ, hDZ], inferInstance, inferInstance,
        Or.inl ⟨hDcyc, rfl, rfl⟩, hcZ⟩
    · push Not at hD_ab
      obtain ⟨x, hx, y, hy, hxy⟩ := hD_ab
      obtain ⟨w, hw, hV, hcard, hwuniq, b, hb1, hb2, hb3, hb4, hb5, ⟨E, hE⟩, -, -⟩ :=
        hnab ⟨x, hx, y, hy, hxy⟩
      obtain ⟨hED, hEx, hEcard, hEZ, -, hEZi, hEcen, hE4⟩ := hE
      have hEZ : E ⊔ Z = D := hEZ
      have hEZi : E ⊓ Z = zpowers z := hEZi
      have hzE : z ∈ E := by
        have h : z ∈ E ⊓ Z := by
          rw [hEZi]
          exact mem_zpowers z
        exact h.1
      have hzpE : zpowers z ≤ E := zpowers_le.mpr hzE
      have hzpc : zpowers z ≤ center P := zpowers_le.mpr hzc
      obtain ⟨hsqD, hcommD⟩ := sq_mem_center_and_comm_mem_center (hP.to_subgroup D) hΦ
      have hsqZ : ∀ x ∈ D, x ^ 2 ∈ Z := fun x hx => ⟨⟨x, hx⟩ ^ 2, hsqD _, rfl⟩
      have hcommZ : ∀ x ∈ D, ∀ y ∈ D, ⁅x, y⁆ ∈ Z := fun x hx y hy =>
        ⟨⁅(⟨x, hx⟩ : D), ⟨y, hy⟩⁆, hcommD _ _, rfl⟩
      have hsqE : ∀ x ∈ E, x ^ 2 ∈ zpowers z := fun x hx =>
        hEZi ▸ mem_inf.mpr ⟨pow_mem hx 2, hsqZ x (hED hx)⟩
      have hcommE : ∀ x ∈ E, ∀ y ∈ E, ⁅x, y⁆ ∈ zpowers z := fun x hx y hy =>
        hEZi ▸ mem_inf.mpr ⟨by
          rw [commutatorElement_def]
          exact mul_mem (mul_mem (mul_mem hx hy) (inv_mem hx)) (inv_mem hy),
          hcommZ x (hED hx) y (hED hy)⟩
      have hdef : ∀ e ∈ E, ∀ g : P, e⁻¹ * (g * e * g⁻¹) ∈ zpowers z := by
        intro e he g
        set c := e⁻¹ * (g * e * g⁻¹) with hcdef
        have hcZ : c ∈ Z := by
          apply hcomm
          rw [commutator_comm]
          have h := commutator_mem_commutator (inv_mem (hED he)) (mem_top g)
          have hc' : c = ⁅e⁻¹, g⁆ := by
            rw [hcdef, commutatorElement_def, inv_inv]
            group
          rw [hc']
          exact h
        have hce : c * e = e * c := mem_centralizer_iff.mp (hZcD hcZ) e (hED he) |>.symm
        have he2 : e ^ 2 ∈ center P := hzpc (hsqE e he)
        have hconj : g * e * g⁻¹ = e * c := by rw [hcdef, mul_inv_cancel_left]
        have hsq : (g * e * g⁻¹) ^ 2 = e ^ 2 := by
          rw [show (g * e * g⁻¹) ^ 2 = g * e ^ 2 * g⁻¹ by rw [pow_two, pow_two]; group,
            mem_center_iff.mp he2 g,
            mul_inv_cancel_right]
        have hc2 : c ^ 2 = 1 := by
          rw [hconj, pow_two, pow_two, mul_assoc, ← mul_assoc c e c, hce, mul_assoc,
            ← mul_assoc, ← pow_two, ← pow_two, mul_eq_left] at hsq
          exact hsq
        by_cases hc1 : c = 1
        · rw [hc1]
          exact one_mem _
        · have hco : orderOf c = 2 := orderOf_eq_prime hc2 hc1
          rw [huniq c hcZ hco]
          exact mem_zpowers z
      have hEn : E.Normal := ⟨fun e he g => by
        have h := mul_mem he (hzpE (hdef e he g))
        rwa [mul_inv_cancel_left] at h⟩
      set R := centralizer (E : Set P) with hRdef
      have hRn : R.Normal := normal_centralizer
      have hfact : ∀ g : P, ∃ t ∈ E, t⁻¹ * g ∈ R := by
        intro g
        obtain ⟨t, ht, hte⟩ := exists_inner_of_conj_mem_zpowers hzE hz hzc hcommE hsqE hEcen
          (fun e he => hdef e he g)
        refine ⟨t, ht, mem_centralizer_iff.mpr fun e he => ?_⟩
        have h := hte e he
        calc e * (t⁻¹ * g) = t⁻¹ * (t * e * t⁻¹) * g := by group
          _ = t⁻¹ * (g * e * g⁻¹) * g := by rw [h]
          _ = t⁻¹ * g * e := by group
      have hER : E ⊔ R = ⊤ := by
        rw [eq_top_iff]
        intro g _
        obtain ⟨t, ht, htg⟩ := hfact g
        have h := mul_mem (mem_sup_left ht : t ∈ E ⊔ R) (mem_sup_right htg)
        rwa [mul_inv_cancel_left] at h
      have hERc : ⁅E, R⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr
        (le_centralizer_iff.mpr le_rfl)
      have hZR : Z ≤ R := le_centralizer_iff.mp (hED.trans hDcZ)
      have hRZ : R ⊓ centralizer (Z : Set P) = Z := by
        refine le_antisymm ?_ (le_inf hZR hZab)
        rintro r ⟨hrE, hrZ⟩
        have h1 : E ≤ centralizer ((zpowers r : Subgroup P) : Set P) := by
          rw [le_centralizer_iff, zpowers_le]
          exact hrE
        have h2 : Z ≤ centralizer ((zpowers r : Subgroup P) : Set P) := by
          rw [le_centralizer_iff, zpowers_le]
          exact hrZ
        have h3 : D ≤ centralizer ((zpowers r : Subgroup P) : Set P) := hEZ ▸ sup_le h1 h2
        rw [le_centralizer_iff, zpowers_le, hcD] at h3
        exact h3
      have hcZ : centralizer (Z : Set P) = D := by
        refine le_antisymm (fun g hg => ?_) hDcZ
        obtain ⟨t, ht, htg⟩ := hfact g
        have htg' : t⁻¹ * g ∈ centralizer (Z : Set P) :=
          mul_mem (inv_mem (hDcZ (hED ht))) hg
        have h := mul_mem (hED ht) (hZD (hRZ ▸ mem_inf.mpr ⟨htg, htg'⟩))
        rwa [mul_inv_cancel_left] at h
      have hER' : E ⊓ R = zpowers z := by
        rw [hRdef, ← map_center_subtype, hEcen]
      exact ⟨E, R, hEZ, rfl, hER, hERc, hRZ, hEn, hRn,
        Or.inr ⟨w, hw, hV, hcard, hwuniq, hEx, hEcard, hE4, hER', hEZi, hEcen,
          b, hb1, hb2, hb3, hb4, hb5⟩, hcZ⟩
  refine ⟨hZ0, hcyc, hZchar, z, hzZ, hz, huniq, hzc, huniqP, hcZ, E, R, hEZ, hR, hER, hERc,
    hRZ, hEn, hRn, hcases, ⟨MulAut.conjNormal, fun g x => MulAut.conjNormal_apply g x, ?_⟩,
    ⟨(MulAut.conjNormal (H := Z)).comp R.subtype, fun r x => MulAut.conjNormal_apply _ x,
      ker_conjNormal_comp_subtype Z R hRZ⟩⟩
  rw [ker_conjNormal, hcZ]

end CFSG.RankThree.GroupTheory.SteinbergBY
