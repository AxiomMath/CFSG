module

public import CFSG.RankThree.GF2n.Stroth78.Sec2Three
public import CFSG.RankThree.GF2n.Stroth78.Sec2Conj

public section

namespace CFSG.RankThree.GF2n.Stroth78

open CFSG CFSG.Open CFSG.RankThree.GF2n.Tim79a CFSG.LargeExtraspecial.Timmesfeld
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G} {E F : Subgroup G}

theorem QaOf_eq_map_conj (S : Setting z E F) {a g : G}
    (hg : g * z * g⁻¹ = a) :
    QaOf a = (Q z).map (MulAut.conj g).toMonoidHom := by
  have ha : a = g * z * g⁻¹ := hg.symm
  show fStar (Subgroup.centralizer ({a} : Set G)) =
    (fStar (Subgroup.centralizer ({z} : Set G))).map (MulAut.conj g).toMonoidHom
  rw [ha, centralizer_map_conj z g, fStar_map_conj]

theorem centerIn_QaOf_eq_map_conj (S : Setting z E F) {a g : G}
    (hg : g * z * g⁻¹ = a) :
    centerIn (QaOf a) = (ZQ z).map (MulAut.conj g).toMonoidHom := by
  let φ : G ≃* G := MulAut.conj g
  have hQa : QaOf a = (Q z).map φ.toMonoidHom := QaOf_eq_map_conj S hg
  have hC : Subgroup.centralizer ((Q z).map φ.toMonoidHom : Set G) =
      (Subgroup.centralizer (Q z : Set G)).map φ.toMonoidHom :=
    (CFSG.Literature.GL52.map_centralizer_subgroup φ (Q z)).symm
  calc
    centerIn (QaOf a) = QaOf a ⊓ Subgroup.centralizer (QaOf a : Set G) := rfl
    _ = (Q z).map φ.toMonoidHom ⊓
          Subgroup.centralizer ((Q z).map φ.toMonoidHom : Set G) := by rw [hQa]
    _ = (Q z).map φ.toMonoidHom ⊓
          (Subgroup.centralizer (Q z : Set G)).map φ.toMonoidHom := by rw [hC]
    _ = ((Q z) ⊓ Subgroup.centralizer (Q z : Set G)).map φ.toMonoidHom :=
          (Subgroup.map_inf_eq (Q z) (Subgroup.centralizer (Q z : Set G)) φ.toMonoidHom
            φ.injective).symm
    _ = (ZQ z).map φ.toMonoidHom := rfl

theorem commutator_QaOf_eq_zpowers (S : Setting z E F) {a g : G}
    (hg : g * z * g⁻¹ = a) :
    ⁅QaOf a, QaOf a⁆ = Subgroup.zpowers a := by
  rw [QaOf_eq_map_conj S hg]
  rw [← Subgroup.map_commutator (f := (MulAut.conj g).toMonoidHom)
    (H₁ := Q z) (H₂ := Q z)]
  rw [Q_deriv_eq S, MonoidHom.map_zpowers]
  show Subgroup.zpowers (MulAut.conj g z) = Subgroup.zpowers a
  rw [MulAut.conj_apply, hg]

theorem inf_ZQ_Qa_le_centerIn (S : Setting z E F) {a : G}
    (hconj : IsConj z a) (haZ : a ∉ ZQ z) (hza : z ∈ centerIn (QaOf a)) :
    ZQ z ⊓ QaOf a ≤ centerIn (QaOf a) := by
  have hconj' := hconj
  obtain ⟨g, hg⟩ := isConj_iff.mp hconj
  intro x hx
  obtain ⟨hxZ, hxQa⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨hxQ, hxCentQ⟩ := Subgroup.mem_inf.mp hxZ
  refine Subgroup.mem_inf.mpr ⟨hxQa, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  by_contra hxy
  have hcomm_ne : ⁅y, x⁆ ≠ 1 := fun h =>
    hxy (commutatorElement_eq_one_iff_mul_comm.mp h)
  have hcomm_mem : ⁅y, x⁆ ∈ Subgroup.zpowers a := by
    rw [← commutator_QaOf_eq_zpowers S hg]
    exact Subgroup.commutator_mem_commutator hy hxQa
  have ha2 : a ^ 2 = 1 := sq_eq_one_of_isConj S hconj'
  have hcomm_eq : ⁅y, x⁆ = a := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hcomm_mem
    obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' k
    · exfalso
      apply hcomm_ne
      rw [← hk, zpow_mul]
      simp [ha2]
    · rw [← hk, zpow_add, zpow_mul]
      simp [ha2]
  have hyH : y ∈ H z := by
    rw [H, Subgroup.mem_centralizer_iff]
    intro t ht
    rw [Set.mem_singleton_iff] at ht
    subst t
    exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hza).2 y hy).symm
  have hyxQ : y * x * y⁻¹ ∈ Q z := fStar_normal (M := H z) hyH hxQ
  have hyxZ : y * x * y⁻¹ ∈ ZQ z := by
    refine Subgroup.mem_inf.mpr ⟨hyxQ, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    have hry : y⁻¹ * r * y ∈ Q z := by
      change y⁻¹ * r * y ∈ fStar (H z)
      simpa using fStar_normal (M := H z) (Subgroup.inv_mem (H z) hyH) hr
    have hxr : (y⁻¹ * r * y) * x = x * (y⁻¹ * r * y) :=
      Subgroup.mem_centralizer_iff.mp hxCentQ _ hry
    calc
      r * (y * x * y⁻¹) = y * (y⁻¹ * r * y) * x * y⁻¹ := by group
      _ = y * ((y⁻¹ * r * y) * x) * y⁻¹ := by group
      _ = y * (x * (y⁻¹ * r * y)) * y⁻¹ := by rw [hxr]
      _ = (y * x * y⁻¹) * r := by group
  have hyx_eq : y * x * y⁻¹ = a * x := by
    have h : y * x * y⁻¹ * x⁻¹ = a := by
      rw [← commutatorElement_def]
      exact hcomm_eq
    calc
      y * x * y⁻¹ = (y * x * y⁻¹ * x⁻¹) * x := by group
      _ = a * x := by rw [h]
  have haZQ : a ∈ ZQ z := by
    have hxinv : x⁻¹ ∈ ZQ z := (ZQ z).inv_mem hxZ
    have haeq : a = (y * x * y⁻¹) * x⁻¹ := by rw [hyx_eq]; group
    rw [haeq]
    exact (ZQ z).mul_mem hyxZ hxinv
  exact haZ haZQ

theorem mem_QaOf_of_forall_commutator_mem_centerIn (S : Setting z E F) {a c g : G}
    (hg : g * z * g⁻¹ = a)
    (hcCa : c ∈ Subgroup.centralizer ({a} : Set G))
    (hact : ∀ y ∈ QaOf a, c * y * c⁻¹ * y⁻¹ ∈ centerIn (QaOf a)) :
    c ∈ QaOf a := by
  have hQa := QaOf_eq_map_conj S hg
  have hZ := centerIn_QaOf_eq_map_conj S hg
  have hcH : g⁻¹ * c * g ∈ H z := by
    rw [H, Subgroup.mem_centralizer_iff]
    intro t ht
    rw [Set.mem_singleton_iff] at ht
    subst t
    have hca : a * c = c * a :=
      Subgroup.mem_centralizer_iff.mp hcCa a (Set.mem_singleton a)
    calc
      z * (g⁻¹ * c * g) = g⁻¹ * (g * z * g⁻¹) * c * g := by group
      _ = g⁻¹ * a * c * g := by rw [hg]
      _ = g⁻¹ * c * a * g := by
        calc
          g⁻¹ * a * c * g = g⁻¹ * (a * c) * g := by group
          _ = g⁻¹ * (c * a) * g := by rw [hca]
          _ = g⁻¹ * c * a * g := by group
      _ = g⁻¹ * c * (g * z * g⁻¹) * g := by rw [← hg]
      _ = (g⁻¹ * c * g) * z := by group
  have hactQ : ∀ x ∈ Q z,
      (g⁻¹ * c * g) * x * (g⁻¹ * c * g)⁻¹ * x⁻¹ ∈ ZQ z := by
    intro x hx
    have hy : g * x * g⁻¹ ∈ QaOf a := by
      rw [hQa]
      exact Subgroup.mem_map.mpr
        ⟨x, hx, by rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]⟩
    have hmem : c * (g * x * g⁻¹) * c⁻¹ * (g * x * g⁻¹)⁻¹ ∈
        centerIn (QaOf a) := hact _ hy
    have hmemZ : c * (g * x * g⁻¹) * c⁻¹ * (g * x * g⁻¹)⁻¹ ∈
        (ZQ z).map (MulAut.conj g).toMonoidHom := by
      rwa [← hZ]
    obtain ⟨u, hu, hueq⟩ := Subgroup.mem_map.mp hmemZ
    have hgroup : g⁻¹ * (c * (g * x * g⁻¹) * c⁻¹ * (g * x * g⁻¹)⁻¹) * g =
        (g⁻¹ * c * g) * x * (g⁻¹ * c * g)⁻¹ * x⁻¹ := by group
    rw [← hgroup]
    have hconj : g⁻¹ * (c * (g * x * g⁻¹) * c⁻¹ * (g * x * g⁻¹)⁻¹) * g = u := by
      rw [← hueq, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [hconj]
    exact hu
  have hcQ : g⁻¹ * c * g ∈ Q z :=
    (S.hyp.centralizer_quotient (g⁻¹ * c * g)).mp ⟨hcH, hactQ⟩
  rw [hQa]
  exact Subgroup.mem_map.mpr ⟨g⁻¹ * c * g, hcQ, by
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group⟩

theorem z_not_mem_centerIn_Qa
    (S : Setting z E F)
    {a : G} (haQ : a ∈ Q z) (hconj : IsConj z a) (haZ : a ∉ ZQ z)
    (hza : z ∈ QaOf a) :
    z ∉ centerIn (QaOf a) := by
  intro hz
  have hQa_le_H : QaOf a ≤ H z := by
    intro y hy
    rw [H, Subgroup.mem_centralizer_iff]
    intro t ht
    rw [Set.mem_singleton_iff] at ht
    subst t
    exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hz).2 y hy).symm
  have hkey := inf_ZQ_Qa_le_centerIn S hconj haZ hz
  by_cases hle : ZQ z ≤ QaOf a
  ·
    have hsub : ZQ z ≤ centerIn (QaOf a) := fun x hx =>
      hkey (Subgroup.mem_inf.mpr ⟨hx, hle hx⟩)
    have hcard : Nat.card (centerIn (QaOf a)) ≤ Nat.card (ZQ z) := by
      rw [ZQ_card S, card_centerIn_QaOf S hconj, Nat.mul_comm]
    have heq : ZQ z = centerIn (QaOf a) := Subgroup.eq_of_le_of_card_ge hsub hcard
    have haZQa : a ∈ centerIn (QaOf a) := by
      refine Subgroup.mem_inf.mpr ⟨mem_QaOf_self a, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact (Subgroup.mem_centralizer_iff.mp
        (fStar_le (Subgroup.centralizer ({a} : Set G)) hy) a
          (Set.mem_singleton a)).symm
    exact haZ (heq.symm ▸ haZQa)
  ·
    obtain ⟨e, heZ, heQa⟩ := Set.not_subset.mp hle
    have heQ : e ∈ Q z := (Subgroup.mem_inf.mp heZ).1
    have heCa : e ∈ Subgroup.centralizer ({a} : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst y
      exact Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp heZ).2 a haQ
    have hact : ∀ y ∈ QaOf a, e * y * e⁻¹ * y⁻¹ ∈ centerIn (QaOf a) := by
      intro y hy
      have heyQa : e * y * e⁻¹ ∈ QaOf a :=
        fStar_normal (M := Subgroup.centralizer ({a} : Set G)) heCa hy
      have heyQa' : e * y * e⁻¹ * y⁻¹ ∈ QaOf a :=
        (QaOf a).mul_mem heyQa ((QaOf a).inv_mem hy)
      have hyH : y ∈ H z := hQa_le_H hy
      have hyeyQ : y * e * y⁻¹ ∈ Q z := fStar_normal (M := H z) hyH heQ
      have heyQ : e * y * e⁻¹ * y⁻¹ ∈ Q z := by
        have hmem : ⁅y, e⁆ ∈ Q z := by
          rw [commutatorElement_def]
          exact (Q z).mul_mem hyeyQ ((Q z).inv_mem heQ)
        have hcomm : ⁅y, e⁆⁻¹ = e * y * e⁻¹ * y⁻¹ := by
          rw [commutatorElement_inv, commutatorElement_def]
        rw [← hcomm]
        exact (Q z).inv_mem hmem
      have hyeyZ : y * e * y⁻¹ ∈ ZQ z := by
        refine Subgroup.mem_inf.mpr ⟨hyeyQ, ?_⟩
        rw [Subgroup.mem_centralizer_iff]
        intro r hr
        have hry : y⁻¹ * r * y ∈ Q z := by
          change y⁻¹ * r * y ∈ fStar (H z)
          simpa using fStar_normal (M := H z) (Subgroup.inv_mem (H z) hyH) hr
        have her : (y⁻¹ * r * y) * e = e * (y⁻¹ * r * y) :=
          Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp heZ).2 _ hry
        calc
          r * (y * e * y⁻¹) = y * (y⁻¹ * r * y) * e * y⁻¹ := by group
          _ = y * ((y⁻¹ * r * y) * e) * y⁻¹ := by group
          _ = y * (e * (y⁻¹ * r * y)) * y⁻¹ := by rw [her]
          _ = (y * e * y⁻¹) * r := by group
      have heyZ : e * y * e⁻¹ * y⁻¹ ∈ ZQ z := by
        have h : e * (y * e * y⁻¹)⁻¹ ∈ ZQ z :=
          (ZQ z).mul_mem heZ ((ZQ z).inv_mem hyeyZ)
        convert h using 1
        group
      exact hkey (Subgroup.mem_inf.mpr ⟨heyZ, heyQa'⟩)
    obtain ⟨g, hg⟩ := isConj_iff.mp hconj
    exact heQa (mem_QaOf_of_forall_commutator_mem_centerIn S hg heCa hact)

end CFSG.RankThree.GF2n.Stroth78
