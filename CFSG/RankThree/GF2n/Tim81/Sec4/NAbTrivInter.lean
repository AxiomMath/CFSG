module

public import CFSG.RankThree.GF2n.Tim81.Sec4.OrthExt
public import CFSG.RankThree.GF2n.Tim81.Sec4.SL2Facts

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Tim78 CFSG.Quasithin
open CFSG.RankThree.GF2n.Tim81.Sec4
open scoped commutatorElement MatrixGroups

variable {G : Type} [Group G] [Finite G] {M V H : Subgroup G}

namespace RootHyp

private theorem mul_comm_of_mem_Pc_inf_kOf
    (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {y : G}
    (hHy : H = Pc M V ⊔ conjSubgroup y (Pc M V)) (hnM : ¬ H ≤ M) (hyH : y ∈ H)
    {x w p' : G} (hwW : w ∈ Tim79a.xOf V H)
    (hpPy : p' ∈ conjSubgroup y (Pc M V)) (hwx : w * p' = x)
    (hxP : x ∈ Pc M V) {a : G} (haP : a ∈ Pc M V) (haK : a ∈ kOf V H) :
    a * x = x * a := by
  classical
  have hP2 : IsPGroup 2 (Pc M V) := (inSubgroup_pCore_two M).1.to_le inf_le_left
  have hwK : w ∈ kOf V H := xOf_le_kOf h hPH hVH hwW
  have ha_w : a * w = w * a :=
    (Subgroup.mem_centralizer_iff.mp ((mem_kOf_iff.mp haK).2) w hwW).symm
  have ha_p : ⁅a, p'⁆ ∈ conjSubgroup y (Pc M V) := by
    have h1 : a * p' * a⁻¹ ∈ conjSubgroup y (Pc M V) :=
      (Subgroup.mem_normalizer_iff.mp
        (kOf_le_normalizer_conjSubgroup_Pc_of_mem h hyH haK) p').mp hpPy
    simpa [commutatorElement_def] using
      (conjSubgroup y (Pc M V)).mul_mem h1 ((conjSubgroup y (Pc M V)).inv_mem hpPy)
  have hconj_x : ⁅a, x⁆ = w * ⁅a, p'⁆ * w⁻¹ := by
    rw [← hwx, commutatorElement_def, commutatorElement_def]
    rw [show a * (w * p') * a⁻¹ * (w * p')⁻¹ =
      w * (a * p' * a⁻¹ * p'⁻¹) * w⁻¹ by
      rw [← mul_assoc a w p', ha_w]; group]
  have hx_Py : ⁅a, x⁆ ∈ conjSubgroup y (Pc M V) := by
    rw [hconj_x]
    exact (Subgroup.mem_normalizer_iff.mp
      (kOf_le_normalizer_conjSubgroup_Pc_of_mem h hyH hwK) ⁅a, p'⁆).mp ha_p
  have hx_V : ⁅a, x⁆ ∈ V :=
    h.toHyp.frattini_Pc_le (commutatorElement_mem_inSubgroup_frattini hP2 haP hxP)
  have hx1 : ⁅a, x⁆ = 1 := by
    have hmem : ⁅a, x⁆ ∈ V ⊓ conjSubgroup y (Pc M V) :=
      Subgroup.mem_inf.mpr ⟨hx_V, hx_Py⟩
    rwa [inf_conj_Pc_eq_bot h hHy hnM] at hmem
  exact commutatorElement_eq_one_iff_mul_comm.mp hx1

private theorem mul_comm_of_mem_conj_inf_kOf
    (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {y : G}
    (hHy : H = Pc M V ⊔ conjSubgroup y (Pc M V)) (hnM : ¬ H ≤ M) (hyH : y ∈ H)
    {x w p' : G} (hwW : w ∈ Tim79a.xOf V H)
    (hpPy : p' ∈ conjSubgroup y (Pc M V)) (hwx : w * p' = x)
    (hxP : x ∈ Pc M V) {b : G} (hbPy : b ∈ conjSubgroup y (Pc M V))
    (hbK : b ∈ kOf V H) :
    b * x = x * b := by
  classical
  have hP2 : IsPGroup 2 (Pc M V) := (inSubgroup_pCore_two M).1.to_le inf_le_left
  have hb_w : b * w = w * b :=
    (Subgroup.mem_centralizer_iff.mp ((mem_kOf_iff.mp hbK).2) w hwW).symm
  have hb_norm : b ∈ Subgroup.normalizer (Pc M V : Set G) :=
    h.toHyp.le_normalizer_Pc (kOf_le_M h hbK)
  have hP2y : IsPGroup 2 (conjSubgroup y (Pc M V)) :=
    hP2.map (MulAut.conj y).toMonoidHom
  have hb_p : ⁅b, p'⁆ ∈ conjSubgroup y V :=
    (frattini_conj_le hP2 h.toHyp.frattini_Pc_le y)
      (commutatorElement_mem_inSubgroup_frattini hP2y hbPy hpPy)
  have hw_cent : w * ⁅b, p'⁆ * w⁻¹ = ⁅b, p'⁆ := by
    have hc := Subgroup.mem_centralizer_iff.mp
      (xOf_le_centralizer_conj h hPH hVH hyH hwW) ⁅b, p'⁆ hb_p
    rw [hc.symm]
    group
  have hconj_x : ⁅b, x⁆ = w * ⁅b, p'⁆ * w⁻¹ := by
    rw [← hwx, commutatorElement_def, commutatorElement_def]
    rw [show b * (w * p') * b⁻¹ * (w * p')⁻¹ =
      w * (b * p' * b⁻¹ * p'⁻¹) * w⁻¹ by
      rw [← mul_assoc b w p', hb_w]; group]
  have hx_Vy : ⁅b, x⁆ ∈ conjSubgroup y V := by
    rw [hconj_x, hw_cent]
    exact hb_p
  have hx_P : ⁅b, x⁆ ∈ Pc M V := by
    have h1 : b * x * b⁻¹ ∈ Pc M V :=
      (Subgroup.mem_normalizer_iff.mp hb_norm x).mp hxP
    simpa [commutatorElement_def] using
      (Pc M V).mul_mem h1 ((Pc M V).inv_mem hxP)
  have hx1 : ⁅b, x⁆ = 1 := by
    have hmem : ⁅b, x⁆ ∈ conjSubgroup y V ⊓ Pc M V :=
      Subgroup.mem_inf.mpr ⟨hx_Vy, hx_P⟩
    rwa [conjSubgroup_inf_Pc_eq_bot h hHy hnM] at hmem
  exact commutatorElement_eq_one_iff_mul_comm.mp hx1

private theorem exists_mul_and_centralizes_of_mem_inf_sup_conj
    (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {y : G}
    (hHy : H = Pc M V ⊔ conjSubgroup y (Pc M V)) (hnM : ¬ H ≤ M) (hyH : y ∈ H)
    {x : G} (hxP : x ∈ Pc M V)
    (hxsup : x ∈ Tim79a.xOf V H ⊔ conjSubgroup y (Pc M V))
    (hK' : kOf V H = (Pc M V ⊓ kOf V H) ⊔ (conjSubgroup y (Pc M V) ⊓ kOf V H)) :
    ∃ w p' : G, w ∈ Tim79a.xOf V H ∧ p' ∈ conjSubgroup y (Pc M V) ∧
      w * p' = x ∧ ∀ k ∈ kOf V H, k * x = x * k := by
  classical
  have hVH' : V ≤ H := hVH.trans (inSubgroup_pCore_two H).2.1
  have hWH : Tim79a.xOf V H ≤ H := Tim79a.xOf_le_H hVH'
  have hPyH : conjSubgroup y (Pc M V) ≤ H := by rw [hHy]; exact le_sup_right
  haveI : ((Tim79a.xOf V H).subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hWH).2 (Tim79a.H_le_normalizer_xOf V H)
  have hxH : x ∈ H := hPH hxP
  have hxsupH : (⟨x, hxH⟩ : ↥H) ∈ (Tim79a.xOf V H).subgroupOf H ⊔
      (conjSubgroup y (Pc M V)).subgroupOf H := by
    rw [← Subgroup.subgroupOf_sup hWH hPyH]
    exact Subgroup.mem_subgroupOf.mpr hxsup
  obtain ⟨w, hw, p', hp', hwp⟩ :=
    (Subgroup.mem_sup_of_normal_left (s := (Tim79a.xOf V H).subgroupOf H)
      (t := (conjSubgroup y (Pc M V)).subgroupOf H)).mp hxsupH
  have hwW : (w : G) ∈ Tim79a.xOf V H := Subgroup.mem_subgroupOf.mp hw
  have hpPy : (p' : G) ∈ conjSubgroup y (Pc M V) := Subgroup.mem_subgroupOf.mp hp'
  have hwx : (w : G) * (p' : G) = x := congrArg Subtype.val hwp
  have hcommA : ∀ a ∈ Pc M V ⊓ kOf V H, a * x = x * a := by
    rintro a ⟨haP, haK⟩
    exact mul_comm_of_mem_Pc_inf_kOf h hPH hVH hHy hnM hyH hwW hpPy hwx hxP haP haK
  have hcommB : ∀ b ∈ conjSubgroup y (Pc M V) ⊓ kOf V H, b * x = x * b := by
    rintro b ⟨hbPy, hbK⟩
    exact mul_comm_of_mem_conj_inf_kOf h hPH hVH hHy hnM hyH hwW hpPy hwx hxP hbPy hbK
  have hA : Pc M V ⊓ kOf V H ≤ Subgroup.centralizer ({x} : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst z
    exact (hcommA a ha).symm
  have hB : conjSubgroup y (Pc M V) ⊓ kOf V H ≤
      Subgroup.centralizer ({x} : Set G) := by
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst z
    exact (hcommB b hb).symm
  have hsup := sup_le hA hB
  have hcommK : ∀ k ∈ kOf V H, k * x = x * k := by
    intro k hk
    have hk' : k ∈ (Pc M V ⊓ kOf V H) ⊔ (conjSubgroup y (Pc M V) ⊓ kOf V H) :=
      hK' ▸ hk
    have hc := hsup hk'
    rw [Subgroup.mem_centralizer_iff] at hc
    exact (hc x (Set.mem_singleton x)).symm
  exact ⟨(w : G), (p' : G), hwW, hpPy, hwx, hcommK⟩

theorem inf_Pc_sup_conj_le_xOf (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    (hK : KFactorization M V H h₀)
    {F : Type} [Field F] [Fintype F] [CharP F 2] (ψ : HBar V H ≃* SL(2, F))
    {l : ℕ} (hl : Fintype.card F = 2 ^ (2 * l))
    {hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H)}
    [Module (ZMod 2) (Additive (IntMod (Tim79a.xOf V H) hW))]
    (horth : Sec2.IsOrthModule hl (subRepW hW ψ (le_refl (Tim79a.xOf V H))
      (Tim79a.H_le_normalizer_xOf V H))) :
    Pc M V ⊓ (Tim79a.xOf V H ⊔ conjSubgroup h₀ (Pc M V)) ≤ Tim79a.xOf V H := by
  classical
  obtain ⟨y, hyH, hPy, -, hHy⟩ := h.exists_mem_conj_eq_of_eq_sup hPH hH
  rw [hPy]
  have hK' : kOf V H = (Pc M V ⊓ kOf V H) ⊔ (conjSubgroup y (Pc M V) ⊓ kOf V H) := by
    conv_lhs => rw [hK]
    rw [hPy]
  intro x hx
  obtain ⟨hxP, hxsup⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨w, p', hwW, hpPy, hwx, hcommK⟩ :=
    exists_mul_and_centralizes_of_mem_inf_sup_conj h hPH hVH hHy hnM hyH hxP hxsup hK'
  have hP2 : IsPGroup 2 (Pc M V) := (inSubgroup_pCore_two M).1.to_le inf_le_left
  have hPyH : conjSubgroup y (Pc M V) ≤ H := by rw [hHy]; exact le_sup_right
  have hvP : ∀ p ∈ Pc M V, ⁅p, x⁆ ∈ Tim79a.xOf V H := by
    intro p hp
    exact le_xOf_self V H (h.toHyp.frattini_Pc_le
      (commutatorElement_mem_inSubgroup_frattini hP2 hp hxP))
  have hvP' : ∀ p ∈ conjSubgroup y (Pc M V), ⁅p, x⁆ ∈ Tim79a.xOf V H := by
    intro p hp
    have hpH : p ∈ H := hPyH hp
    have hp_w : ⁅p, w⁆ ∈ Tim79a.xOf V H := by
      have h1 : p * w * p⁻¹ ∈ Tim79a.xOf V H :=
        (Subgroup.mem_normalizer_iff.mp (Tim79a.H_le_normalizer_xOf V H hpH) w).mp hwW
      simpa [commutatorElement_def] using
        (Tim79a.xOf V H).mul_mem h1 ((Tim79a.xOf V H).inv_mem hwW)
    have hP2y : IsPGroup 2 (conjSubgroup y (Pc M V)) :=
      hP2.map (MulAut.conj y).toMonoidHom
    have hp_p : ⁅p, p'⁆ ∈ conjSubgroup y V :=
      (frattini_conj_le hP2 h.toHyp.frattini_Pc_le y)
        (commutatorElement_mem_inSubgroup_frattini hP2y hp hpPy)
    have hp_pW : ⁅p, p'⁆ ∈ Tim79a.xOf V H :=
      conjSubgroup_le_xOf_of_mem (V := V) (H := H) hyH hp_p
    have hmid : w * ⁅p, p'⁆ * w⁻¹ ∈ Tim79a.xOf V H := by
      have hc := Subgroup.mem_centralizer_iff.mp
        (xOf_le_centralizer_conj h hPH hVH hyH hwW) ⁅p, p'⁆ hp_p
      rw [show w * ⁅p, p'⁆ * w⁻¹ = ⁅p, p'⁆ by rw [hc.symm]; group]
      exact hp_pW
    have hconj_x : ⁅p, x⁆ = ⁅p, w⁆ * (w * ⁅p, p'⁆ * w⁻¹) := by
      rw [← hwx, commutatorElement_def, commutatorElement_def]
      group
    rw [hconj_x]
    exact (Tim79a.xOf V H).mul_mem hp_w hmid
  have hvP'' : ∀ p ∈ conjSubgroup h₀ (Pc M V), ⁅p, x⁆ ∈ Tim79a.xOf V H := by
    rw [hPy]
    exact hvP'
  exact mem_of_isOrthModule_of_forall_commutator_mem h hPH hVH hH hnM ψ hl
    (le_refl (Tim79a.xOf V H)) (Tim79a.H_le_normalizer_xOf V H) horth hcommK hvP hvP''

private theorem exists_y_maps_of_imgK_ne
    (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    {F : Type} [Field F] [Fintype F] [CharP F 2] (ψ : HBar V H ≃* SL(2, F))
    {g : G} (hg : g ∈ H)
    (hne : imgK V H (conjSubgroup g (Pc M V)) ≠ imgK V H (Pc M V)) :
    ∃ (y : G) (hyH : y ∈ H) (a₀ : SL(2, F)),
      conjSubgroup h₀ (Pc M V) = conjSubgroup y (Pc M V) ∧
      H = Pc M V ⊔ conjSubgroup y (Pc M V) ∧
      (imgK V H (Pc M V)).map ψ.toMonoidHom = conjSubgroup a₀ (utri F) ∧
      conjSubgroup (ψ (piK V H ⟨y, hyH⟩)) (conjSubgroup a₀ (utri F)) ≠
        conjSubgroup a₀ (utri F) ∧
      conjSubgroup (ψ (piK V H ⟨g, hg⟩)) (conjSubgroup a₀ (utri F)) ≠
        conjSubgroup a₀ (utri F) := by
  classical
  obtain ⟨y, hyH, hPy, -, hHy⟩ := h.exists_mem_conj_eq_of_eq_sup hPH hH
  have hneY : imgK V H (conjSubgroup y (Pc M V)) ≠ imgK V H (Pc M V) := by
    have h := (imgK_ne_bot_and_ne_of_sup h hPH hH hnM).2
    rw [hPy] at h
    exact h.symm
  obtain ⟨-, -, a₀, -, hmapA, -, -⟩ := imgK_map_sl2 h hPH hVH hH hnM ψ
  set A : Subgroup (HBar V H) := imgK V H (Pc M V)
  set C : Subgroup (SL(2, F)) := conjSubgroup a₀ (utri F)
  have hmapA' : A.map ψ.toMonoidHom = C := hmapA
  have hmapPg : (imgK V H (conjSubgroup g (Pc M V))).map ψ.toMonoidHom =
      conjSubgroup (ψ (piK V H ⟨g, hg⟩)) C := by
    rw [imgK_conjSubgroup hg hPH,
      CFSG.CGT.Timmesfeld75.map_conjSubgroup (f := ψ.toMonoidHom), hmapA']
    rfl
  have hmapPy' : (imgK V H (conjSubgroup y (Pc M V))).map ψ.toMonoidHom =
      conjSubgroup (ψ (piK V H ⟨y, hyH⟩)) C := by
    rw [imgK_conjSubgroup hyH hPH,
      CFSG.CGT.Timmesfeld75.map_conjSubgroup (f := ψ.toMonoidHom), hmapA']
    rfl
  have hne_gC : conjSubgroup (ψ (piK V H ⟨g, hg⟩)) C ≠ C := by
    intro heq
    apply hne
    have h1 : (imgK V H (conjSubgroup g (Pc M V))).map ψ.toMonoidHom =
        A.map ψ.toMonoidHom := by
      rw [hmapPg, heq, ← hmapA']
    exact Subgroup.map_injective ψ.injective h1
  have hne_yC : conjSubgroup (ψ (piK V H ⟨y, hyH⟩)) C ≠ C := by
    intro heq
    apply hneY
    have h1 : (imgK V H (conjSubgroup y (Pc M V))).map ψ.toMonoidHom =
        A.map ψ.toMonoidHom := by
      rw [hmapPy', heq, ← hmapA']
    exact Subgroup.map_injective ψ.injective h1
  exact ⟨y, hyH, a₀, hPy, hHy, hmapA, hne_yC, hne_gC⟩

private theorem exists_z_imgK_eq_of_F8
    (hPH : Pc M V ≤ H)
    {F : Type} [Field F] [Fintype F] [CharP F 2] (ψ : HBar V H ≃* SL(2, F))
    {g : G} (hg : g ∈ H)
    {y : G} (hyH : y ∈ H) {a₀ : SL(2, F)}
    (hmapA : (imgK V H (Pc M V)).map ψ.toMonoidHom = conjSubgroup a₀ (utri F))
    (hne_yC : conjSubgroup (ψ (piK V H ⟨y, hyH⟩)) (conjSubgroup a₀ (utri F)) ≠
      conjSubgroup a₀ (utri F))
    (hne_gC : conjSubgroup (ψ (piK V H ⟨g, hg⟩)) (conjSubgroup a₀ (utri F)) ≠
      conjSubgroup a₀ (utri F)) :
    ∃ z : G, z ∈ Pc M V ∧
      imgK V H (conjSubgroup g (Pc M V)) =
        imgK V H (conjSubgroup (z * y) (Pc M V)) := by
  classical
  set A : Subgroup (HBar V H) := imgK V H (Pc M V)
  set C : Subgroup (SL(2, F)) := conjSubgroup a₀ (utri F)
  have hmapA' : A.map ψ.toMonoidHom = C := hmapA
  obtain ⟨s, hs, hF8⟩ :=
    CFSG.RankThree.GF2n.Tim81.Sec4.exists_mul_conjSubgroup_conj_utri_eq_of_ne
      (a := ψ (piK V H ⟨y, hyH⟩)) (b := ψ (piK V H ⟨g, hg⟩)) (c := a₀) hne_yC hne_gC
  have hsA : s ∈ A.map ψ.toMonoidHom := by rwa [hmapA']
  obtain ⟨zbar, hzbarA, hzbar_eq⟩ := Subgroup.mem_map.mp hsA
  obtain ⟨zH, hzP, hzpi⟩ := (mem_imgK_iff (V := V) (H := H) (S := Pc M V)).mp hzbarA
  set z : G := (zH : G) with hz
  have hzH : z ∈ H := zH.2
  have hzy : z * y ∈ H := H.mul_mem hzH hyH
  have hzy_pi : piK V H ⟨z * y, hzy⟩ =
      piK V H ⟨z, hzH⟩ * piK V H ⟨y, hyH⟩ := by
    rw [← map_mul]
    congr 1
  have hzpi' : piK V H ⟨z, hzH⟩ = zbar := by simpa [hz] using hzpi
  have hzbar_eq' : ψ zbar = s := hzbar_eq
  have hzy_psi : ψ (piK V H ⟨z * y, hzy⟩) = s * ψ (piK V H ⟨y, hyH⟩) := by
    rw [hzy_pi, map_mul, hzpi', hzbar_eq']
  have hzy_psi' : ψ.toMonoidHom (piK V H ⟨z * y, hzy⟩) =
      s * ψ (piK V H ⟨y, hyH⟩) := hzy_psi
  have hbar_eq : conjSubgroup (piK V H ⟨g, hg⟩) A =
      conjSubgroup (piK V H ⟨z * y, hzy⟩) A := by
    apply Subgroup.map_injective (f := ψ.toMonoidHom) ψ.injective
    have hleft : (conjSubgroup (piK V H ⟨g, hg⟩) A).map ψ.toMonoidHom =
        conjSubgroup (ψ (piK V H ⟨g, hg⟩)) C := by
      rw [CFSG.CGT.Timmesfeld75.map_conjSubgroup (f := ψ.toMonoidHom), hmapA']
      rfl
    have hright : (conjSubgroup (piK V H ⟨z * y, hzy⟩) A).map ψ.toMonoidHom =
        conjSubgroup (s * ψ (piK V H ⟨y, hyH⟩)) C := by
      rw [CFSG.CGT.Timmesfeld75.map_conjSubgroup (f := ψ.toMonoidHom), hmapA', hzy_psi']
    calc (conjSubgroup (piK V H ⟨g, hg⟩) A).map ψ.toMonoidHom
        = conjSubgroup (ψ (piK V H ⟨g, hg⟩)) C := hleft
      _ = conjSubgroup (s * ψ (piK V H ⟨y, hyH⟩)) C := hF8
      _ = (conjSubgroup (piK V H ⟨z * y, hzy⟩) A).map ψ.toMonoidHom := hright.symm
  have himg : imgK V H (conjSubgroup g (Pc M V)) =
      imgK V H (conjSubgroup (z * y) (Pc M V)) := by
    rw [imgK_conjSubgroup hg hPH, imgK_conjSubgroup hzy hPH]
    exact hbar_eq
  exact ⟨z, hzP, himg⟩

private theorem exists_mul_Pc_imgK_eq_of_imgK_ne
    (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    {F : Type} [Field F] [Fintype F] [CharP F 2] (ψ : HBar V H ≃* SL(2, F))
    {g : G} (hg : g ∈ H)
    (hne : imgK V H (conjSubgroup g (Pc M V)) ≠ imgK V H (Pc M V)) :
    ∃ z y : G, z ∈ Pc M V ∧ y ∈ H ∧
      conjSubgroup h₀ (Pc M V) = conjSubgroup y (Pc M V) ∧
      H = Pc M V ⊔ conjSubgroup y (Pc M V) ∧
      imgK V H (conjSubgroup g (Pc M V)) =
        imgK V H (conjSubgroup (z * y) (Pc M V)) := by
  classical
  obtain ⟨y, hyH, a₀, hPy, hHy, hmapA, hne_yC, hne_gC⟩ :=
    exists_y_maps_of_imgK_ne h hPH hVH hH hnM ψ hg hne
  obtain ⟨z, hzP, himg⟩ :=
    exists_z_imgK_eq_of_F8 hPH ψ hg hyH hmapA hne_yC hne_gC
  exact ⟨z, y, hzP, hyH, hPy, hHy, himg⟩

private theorem conjSubgroup_eq_of_imgK_conjSubgroup_eq_of_mem_Pc
    (h : RootHyp M V) (hPH : Pc M V ≤ H)
    {g z y : G}
    (hg : g ∈ H) (hzP : z ∈ Pc M V) (hyH : y ∈ H)
    (himg : imgK V H (conjSubgroup g (Pc M V)) =
      imgK V H (conjSubgroup (z * y) (Pc M V))) :
    conjSubgroup g (Pc M V) = conjSubgroup (z * y) (Pc M V) := by
  classical
  have hzH : z ∈ H := hPH hzP
  have hzy : z * y ∈ H := H.mul_mem hzH hyH
  have hsup : conjSubgroup g (Pc M V) ⊔ kOf V H =
      conjSubgroup (z * y) (Pc M V) ⊔ kOf V H :=
    (imgK_eq_iff_sup_kOf_eq (conjSubgroup_le_of_le_of_mem hPH hg)
      (conjSubgroup_le_of_le_of_mem hPH hzy)).mp himg
  have hKzy : conjSubgroup ((z * y)⁻¹) (kOf V H) = kOf V H :=
    conjSubgroup_eq_self_iff.mpr (le_normalizer_kOf V H (H.inv_mem hzy))
  have hsup' : conjSubgroup ((z * y)⁻¹ * g) (Pc M V) ⊔ kOf V H =
      Pc M V ⊔ kOf V H := by
    have h := congrArg (conjSubgroup ((z * y)⁻¹)) hsup
    rw [CFSG.CGT.Timmesfeld75.conjSubgroup_sup,
      CFSG.CGT.Timmesfeld75.conjSubgroup_sup, hKzy,
      CFSG.CGT.Timmesfeld75.conjSubgroup_conjSubgroup,
      CFSG.CGT.Timmesfeld75.conjSubgroup_conjSubgroup, inv_mul_cancel,
      conjSubgroup_one] at h
    exact h
  have huH : (z * y)⁻¹ * g ∈ H := H.mul_mem (H.inv_mem hzy) hg
  have hrig := RootHyp.conjSubgroup_eq_self_of_sup_conj_Pc_eq h hPH huH hsup'
  have h := congrArg (conjSubgroup (z * y)) hrig.2.1
  rw [CFSG.CGT.Timmesfeld75.conjSubgroup_conjSubgroup] at h
  rw [show z * y * ((z * y)⁻¹ * g) = g by group] at h
  exact h

theorem inf_Pc_sup_conjSubgroup_le_xOf_of_ne (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    (hK : KFactorization M V H h₀)
    {F : Type} [Field F] [Fintype F] [CharP F 2] (ψ : HBar V H ≃* SL(2, F))
    {l : ℕ} (hl : Fintype.card F = 2 ^ (2 * l))
    {hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H)}
    [Module (ZMod 2) (Additive (IntMod (Tim79a.xOf V H) hW))]
    (horth : Sec2.IsOrthModule hl (subRepW hW ψ (le_refl (Tim79a.xOf V H))
      (Tim79a.H_le_normalizer_xOf V H)))
    {g : G} (hg : g ∈ H)
    (hne : imgK V H (conjSubgroup g (Pc M V)) ≠ imgK V H (Pc M V)) :
    Pc M V ⊓ (Tim79a.xOf V H ⊔ conjSubgroup g (Pc M V)) ≤ Tim79a.xOf V H := by
  classical
  obtain ⟨z, y, hzP, hyH, hPy, hHy, himg⟩ :=
    exists_mul_Pc_imgK_eq_of_imgK_ne h hPH hVH hH hnM ψ hg hne
  have hPg_eq : conjSubgroup g (Pc M V) = conjSubgroup (z * y) (Pc M V) :=
    conjSubgroup_eq_of_imgK_conjSubgroup_eq_of_mem_Pc h hPH hg hzP hyH himg
  have hzH : z ∈ H := hPH hzP
  have hC20 : Pc M V ⊓ (Tim79a.xOf V H ⊔ conjSubgroup y (Pc M V)) ≤
      Tim79a.xOf V H := by
    have h := inf_Pc_sup_conj_le_xOf h hPH hVH hH hnM hK ψ hl horth
    rwa [hPy] at h
  have hzW : conjSubgroup z (Tim79a.xOf V H) = Tim79a.xOf V H :=
    conjSubgroup_eq_self_iff.mpr (Tim79a.H_le_normalizer_xOf V H hzH)
  have hzPc : conjSubgroup z (Pc M V) = Pc M V :=
    conjSubgroup_eq_self_iff.mpr (Subgroup.le_normalizer (H := Pc M V) hzP)
  have hconj := conjSubgroup_mono (g := z) hC20
  rw [conjSubgroup_inf, CFSG.CGT.Timmesfeld75.conjSubgroup_sup, hzPc, hzW,
    CFSG.CGT.Timmesfeld75.conjSubgroup_conjSubgroup] at hconj
  rw [hPg_eq]
  exact hconj

theorem inf_conj_Pc_sup_conjSubgroup_le_xOf_of_ne (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    (hK : KFactorization M V H h₀)
    {F : Type} [Field F] [Fintype F] [CharP F 2] (ψ : HBar V H ≃* SL(2, F))
    {l : ℕ} (hl : Fintype.card F = 2 ^ (2 * l))
    {hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H)}
    [Module (ZMod 2) (Additive (IntMod (Tim79a.xOf V H) hW))]
    (horth : Sec2.IsOrthModule hl (subRepW hW ψ (le_refl (Tim79a.xOf V H))
      (Tim79a.H_le_normalizer_xOf V H)))
    {g : G} (hg : g ∈ H)
    (hne : imgK V H (conjSubgroup g (Pc M V)) ≠
      imgK V H (conjSubgroup h₀ (Pc M V))) :
    conjSubgroup h₀ (Pc M V) ⊓
      (Tim79a.xOf V H ⊔ conjSubgroup g (Pc M V)) ≤ Tim79a.xOf V H := by
  classical
  obtain ⟨y, hyH, hPy, -, hHy⟩ := h.exists_mem_conj_eq_of_eq_sup hPH hH
  have huH : y⁻¹ * g ∈ H := H.mul_mem (H.inv_mem hyH) hg
  have hne' : imgK V H (conjSubgroup (y⁻¹ * g) (Pc M V)) ≠ imgK V H (Pc M V) := by
    intro heq
    apply hne
    have hu_le : conjSubgroup (y⁻¹ * g) (Pc M V) ≤ H :=
      conjSubgroup_le_of_le_of_mem hPH huH
    have hsup_u : conjSubgroup (y⁻¹ * g) (Pc M V) ⊔ kOf V H = Pc M V ⊔ kOf V H :=
      (imgK_eq_iff_sup_kOf_eq hu_le hPH).mp heq
    have hKy : conjSubgroup y (kOf V H) = kOf V H :=
      conjSubgroup_eq_self_iff.mpr (le_normalizer_kOf V H hyH)
    have h1 : conjSubgroup g (Pc M V) ⊔ kOf V H =
        conjSubgroup y (Pc M V) ⊔ kOf V H := by
      have h2 := congrArg (conjSubgroup y) hsup_u
      rw [CFSG.CGT.Timmesfeld75.conjSubgroup_sup,
        CFSG.CGT.Timmesfeld75.conjSubgroup_sup, hKy,
        CFSG.CGT.Timmesfeld75.conjSubgroup_conjSubgroup] at h2
      rw [show y * (y⁻¹ * g) = g by group] at h2
      exact h2
    rw [hPy]
    exact (imgK_eq_iff_sup_kOf_eq (conjSubgroup_le_of_le_of_mem hPH hg)
      (conjSubgroup_le_of_le_of_mem hPH hyH)).mpr h1
  have hC := inf_Pc_sup_conjSubgroup_le_xOf_of_ne h hPH hVH hH hnM hK ψ hl horth huH hne'
  have hWy : conjSubgroup y (Tim79a.xOf V H) = Tim79a.xOf V H :=
    conjSubgroup_eq_self_iff.mpr (Tim79a.H_le_normalizer_xOf V H hyH)
  have hconj := conjSubgroup_mono (g := y) hC
  rw [conjSubgroup_inf, CFSG.CGT.Timmesfeld75.conjSubgroup_sup, hWy,
    CFSG.CGT.Timmesfeld75.conjSubgroup_conjSubgroup] at hconj
  rw [show y * (y⁻¹ * g) = g by group] at hconj
  rw [hPy]
  exact hconj

end RootHyp

end CFSG.RankThree.GF2n.Tim81

end
