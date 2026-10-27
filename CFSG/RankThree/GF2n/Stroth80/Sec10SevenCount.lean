module

public import CFSG.RankThree.GF2n.Smith81.TiRootLines
public import CFSG.RankThree.GF2n.Stroth80.Sec10SevenChi
public import CFSG.RankThree.GF2n.Stroth80.Sec103Root
public import CFSG.RankThree.GF2n.Stroth80.Sec10CardU

public section

namespace CFSG

theorem card_mul_card_le_card_comap_mul {A B : Type*} [Group A] [Group B] [Finite A] [Finite B]
    (f : A →* B) (S : Subgroup B) :
    Nat.card A * Nat.card S ≤ Nat.card (S.comap f) * Nat.card B := by
  have hle : (S.comap f).index ≤ S.index := by
    rw [Subgroup.index_comap, ← Subgroup.relIndex_top_right]
    exact Subgroup.relIndex_le_of_le_right le_top
      (by rw [Subgroup.relIndex_top_right]; exact Subgroup.index_ne_zero_of_finite)
  rw [← (S.comap f).card_mul_index, ← S.card_mul_index]
  calc Nat.card (S.comap f) * (S.comap f).index * Nat.card S
      ≤ Nat.card (S.comap f) * S.index * Nat.card S := by gcongr
    _ = Nat.card (S.comap f) * (Nat.card S * S.index) := by ring

end CFSG

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n.Smith81
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

private theorem commutatorToVtHom_mul (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (hspread : StrothNoA2SpreadStatement) {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n)
    {t : G} (ht : Good103 M Q Z B t)
    (hVab : IsMulCommutative ↥(Vt M (LB M Q B) B Z t))
    (x x' : ↥(Wt Q (Vt M (LB M Q B) B Z t))) :
    ⁅(x : G) * (x' : G), t⁆ = ⁅(x : G), t⁆ * ⁅(x' : G), t⁆ := by
  have hxt' : ⁅(x' : G), t⁆ ∈ Vt M (LB M Q B) B Z t :=
    (Good103.comm_mem_Vt_iff h34 h311a hspread H ht x'.2.1).mpr x'.2
  have hxt : ⁅(x : G), t⁆ ∈ Vt M (LB M Q B) B Z t :=
    (Good103.comm_mem_Vt_iff h34 h311a hspread H ht x.2.1).mpr x.2
  have hcomm : ⁅(x' : G), t⁆ * (x : G) = (x : G) * ⁅(x' : G), t⁆ :=
    Subgroup.mem_centralizer_iff.mp x.2.2 ⁅(x' : G), t⁆ hxt'
  have hVcomm : ∀ a ∈ Vt M (LB M Q B) B Z t, ∀ b ∈ Vt M (LB M Q B) B Z t,
      a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hVab.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  calc ⁅(x : G) * (x' : G), t⁆
      = (x : G) * ⁅(x' : G), t⁆ * (x : G)⁻¹ * ⁅(x : G), t⁆ := by
          rw [commutatorElement_def]; group
    _ = ⁅(x' : G), t⁆ * ⁅(x : G), t⁆ := by
          rw [show (x : G) * ⁅(x' : G), t⁆ * (x : G)⁻¹ = ⁅(x' : G), t⁆ from by
            rw [← hcomm]; group]
    _ = ⁅(x : G), t⁆ * ⁅(x' : G), t⁆ := (hVcomm _ hxt _ hxt').symm

private def commutatorToVtHom (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (hspread : StrothNoA2SpreadStatement) {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n)
    {t : G} (ht : Good103 M Q Z B t)
    (hVab : IsMulCommutative ↥(Vt M (LB M Q B) B Z t)) :
    ↥(Wt Q (Vt M (LB M Q B) B Z t)) →* ↥(Vt M (LB M Q B) B Z t) :=
  MonoidHom.mk' (fun x => ⟨⁅(x : G), t⁆,
      (Good103.comm_mem_Vt_iff h34 h311a hspread H ht x.2.1).mpr x.2⟩)
    (fun x x' => Subtype.ext (commutatorToVtHom_mul h34 h311a hspread H ht hVab x x'))

private theorem exists_psi_card (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (hspread : StrothNoA2SpreadStatement) {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n)
    {t : G} (ht : Good103 M Q Z B t) {Y : Subgroup G} (hs : Sit M Q Z Y t)
    {C : Subgroup G} (hCY : C ≤ Q ⊓ QB Y) :
    ∃ Ψ : Subgroup G,
      (∀ x : G, x ∈ Ψ ↔ x ∈ Wt Q (Vt M (LB M Q B) B Z t) ∧
        ⁅x, t⁆ ∈ C ⊔ Z) ∧
      Nat.card ↥(Wt Q (Vt M (LB M Q B) B Z t)) * Nat.card ↥(C ⊔ Z) ≤
        Nat.card ↥Ψ * Nat.card ↥(Vt M (LB M Q B) B Z t) := by
  let V : Subgroup G := Vt M (LB M Q B) B Z t
  let W : Subgroup G := Wt Q V
  have hVab : IsElemAbelian 2 V := by
    have h := (Sit.inf_QB_elemAbelian hs).sup_of_commute hc.hyp.isElemAbelian_Z
      (fun x hx y hy => (Z_central hc.hyp hy hx.1).symm)
    rw [show V = (Q ⊓ QB Y) ⊔ Z from Good103.Vt_eq ht hs]
    exact h
  let ν : ↥W →* ↥V := commutatorToVtHom h34 h311a hspread H ht hVab.1
  have hCV : C ⊔ Z ≤ V := by
    rw [show V = (Q ⊓ QB Y) ⊔ Z from Good103.Vt_eq ht hs]
    exact sup_le (fun x hx => Subgroup.mem_sup_left (hCY hx))
      (fun z hz => Subgroup.mem_sup_right hz)
  haveI : IsMulCommutative ↥V := hVab.1
  let S : Subgroup ↥V := (C ⊔ Z).subgroupOf V
  let Ψ' : Subgroup ↥W := S.comap ν
  let Ψ : Subgroup G := Ψ'.map W.subtype
  have hS : Nat.card ↥S = Nat.card ↥(C ⊔ Z) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCV).toEquiv
  have hΨcard : Nat.card ↥Ψ = Nat.card ↥Ψ' :=
    Subgroup.card_map_of_injective W.subtype_injective
  have hH1 := card_mul_card_le_card_comap_mul ν S
  refine ⟨Ψ, ?_, ?_⟩
  · intro x
    constructor
    · intro hx
      obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hx
      refine ⟨w.2, ?_⟩
      exact Subgroup.mem_subgroupOf.mp (Subgroup.mem_comap.mp hw)
    · rintro ⟨hxW, hxt⟩
      exact Subgroup.mem_map.mpr ⟨⟨x, hxW⟩,
        Subgroup.mem_comap.mpr (Subgroup.mem_subgroupOf.mpr hxt), rfl⟩
  · rw [hS, ← hΨcard] at hH1
    exact hH1



private theorem comm_mem_Vt_of_comm_mem_Z (hc : Ctx M Q Z B) {t : G}
    (ht : Good103 M Q Z B t)
    {Y : Subgroup G} (hs : Sit M Q Z Y t)
    (hnft : ∀ w ∈ Q, ∀ z ∈ Z, w * t * w⁻¹ = t * z → z = 1) {y : G}
    (hyCt : ∀ x ∈ Q ⊓ Subgroup.centralizer ({t} : Set G), ⁅x, y⁆ ∈ Q ⊓ QB Y)
    {x : G} (hxQ : x ∈ Q) (hxtZ : ⁅x, t⁆ ∈ Z) :
    ⁅x, y⁆ ∈ Vt M (LB M Q B) B Z t := by
  have htZ : ∀ z ∈ Z, t * z = z * t := fun z hz => by
    have h := hc.LB_centralizes_Z ht.1.mem_LB z hz
    calc t * z = (t * z * t⁻¹) * t := by group
      _ = z * t := by rw [h]
  have hxC : x ∈ Subgroup.centralizer ({t} : Set G) :=
    mem_centralizer_of_comm_mem_Z htZ hnft hxQ hxtZ
  have hmem : ⁅x, y⁆ ∈ Q ⊓ QB Y := hyCt x ⟨hxQ, hxC⟩
  rw [Good103.Vt_eq ht hs]
  exact Subgroup.mem_sup_left hmem

private theorem exists_root_comm_data (h34 : Stroth34Statement)
    (hspread : StrothNoA2SpreadStatement)
    {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n) {t : G} (ht : Good103 M Q Z B t)
    {Y : Subgroup G} (hs : Sit M Q Z Y t) {C : Subgroup G} (hCY : C ≤ Q ⊓ QB Y)
    (hCroot : ∀ γ ∈ C, γ ≠ 1 → ∃ D : Subgroup G, Ctx M Q Z D ∧ γ ∈ D ∧ D ≤ C)
    {x γ z : G} (hγC : γ ∈ C) (hγ1 : γ ≠ 1) (hγz : γ * z = ⁅x, t⁆) :
    ∃ (D : Subgroup G) (a : G), Ctx M Q Z D ∧ D ≤ C ∧ γ ∈ D ∧ a ∈ Q ⊓ QB D ∧
      ⁅t, a⁆ = γ ∧ γ * γ = 1 ∧ γ * a = a * γ ∧ t * a = (γ * a) * t ∧
      x * t * x⁻¹ = (γ * z) * t := by
  obtain ⟨D, hD, hγD, hDC⟩ := hCroot γ hγC hγ1
  obtain ⟨r, hr, hrD⟩ := H.rootTrans h34 hspread D hD
  have hD' : D = conjSubgroup r B := hrD.symm
  subst D
  have hDY : conjSubgroup r B ≤ QB Y := fun v hv => (Subgroup.mem_inf.mp (hCY (hDC hv))).2
  have hne : conjSubgroup r B ≠ Y := by
    intro heq
    apply hγ1
    have hγY : γ ∈ Y := heq ▸ hγD
    have hγQ : γ ∈ Q := (Subgroup.mem_inf.mp (hCY (hDC hγD))).1
    have hmem : γ ∈ Y ⊓ Q := ⟨hγY, hγQ⟩
    rw [(smith_1_12 hs).2, Subgroup.mem_bot] at hmem
    exact hmem
  have htD : t ∈ QB (conjSubgroup r B) :=
    hc.hyp.le_QB_of_le_QB hD.conj hs.conj hne hDY hs.mem
  have hno : NoA2 Q Z (LB M Q (conjSubgroup r B)) := hc.noA2_conj H.noA2 hr
  obtain ⟨a, ha, hat⟩ := hD.exists_comm_eq_of_mem_QB H.width (by have := H.n_gt; omega) hno htD
    ht.1.2.2.1 hγD
  have hγ2 : γ * γ = 1 := by
    simpa [pow_two] using (isElemAbelian_conjSubgroup hc.isElemAbelian_B r).2 γ hγD
  have hγa : γ * a = a * γ := by
    haveI : IsMulCommutative ↥(Q ⊓ QB (conjSubgroup r B)) := hD.inf_QB_elemAbelian.1
    exact Subgroup.mul_comm_of_mem_isMulCommutative
      (H := Q ⊓ QB (conjSubgroup r B)) ⟨hD.le hγD, hD.B_le_QB hγD⟩ ha
  have hta : t * a = (γ * a) * t := by
    have h := hat
    rw [commutatorElement_def] at h
    calc t * a = (t * a * t⁻¹ * a⁻¹) * (a * t) := by group
      _ = γ * (a * t) := by rw [h]
      _ = (γ * a) * t := by group
  have hxt' : x * t * x⁻¹ = (γ * z) * t := by
    have h := hγz
    rw [commutatorElement_def] at h
    calc x * t * x⁻¹ = (x * t * x⁻¹ * t⁻¹) * t := by group
      _ = (γ * z) * t := by rw [h]
  exact ⟨conjSubgroup r B, a, hD, hDC, hγD, ha, hat, hγ2, hγa, hta, hxt'⟩

private theorem comm_inv_mul_eq {a x γ z t : G}
    (hγ2 : γ * γ = 1) (hγa : γ * a = a * γ) (hza : z * a = a * z)
    (hzγ : z * γ = γ * z) (hta : t * a = (γ * a) * t) (hxt' : x * t * x⁻¹ = (γ * z) * t) :
    ⁅a⁻¹ * x, t⁆ = z := by
  have haγz : a⁻¹ * (γ * z) = (γ * z) * a⁻¹ := by
    have h1 : a⁻¹ * γ = γ * a⁻¹ := (Commute.inv_left_iff.mpr hγa.symm).eq
    have h2 : a⁻¹ * z = z * a⁻¹ := (Commute.inv_left_iff.mpr hza.symm).eq
    calc a⁻¹ * (γ * z) = (a⁻¹ * γ) * z := (mul_assoc _ _ _).symm
      _ = (γ * a⁻¹) * z := by rw [h1]
      _ = γ * (a⁻¹ * z) := mul_assoc _ _ _
      _ = γ * (z * a⁻¹) := by rw [h2]
      _ = (γ * z) * a⁻¹ := (mul_assoc _ _ _).symm
  calc ⁅a⁻¹ * x, t⁆ = a⁻¹ * (x * t * x⁻¹) * a * t⁻¹ := by
        rw [commutatorElement_def]; group
    _ = a⁻¹ * ((γ * z) * t) * a * t⁻¹ := by rw [hxt']
    _ = z := by
        calc a⁻¹ * ((γ * z) * t) * a * t⁻¹
            = (a⁻¹ * (γ * z)) * (t * a) * t⁻¹ := by group
          _ = ((γ * z) * a⁻¹) * (t * a) * t⁻¹ := by rw [haγz]
          _ = (γ * z) * (a⁻¹ * ((γ * a) * t)) * t⁻¹ := by rw [hta]; group
          _ = (γ * z) * ((a⁻¹ * (γ * a)) * t) * t⁻¹ := by group
          _ = (γ * z) * (γ * (t * t⁻¹)) := by
                have h1 : a⁻¹ * (γ * a) = γ := by rw [hγa]; group
                rw [h1]; group
          _ = z := by
                rw [mul_inv_cancel, mul_one, mul_assoc, hzγ, ← mul_assoc, hγ2, one_mul]

private theorem comm_mem_Vt_of_comm_mem_sup_ne_one (h34 : Stroth34Statement)
    (hspread : StrothNoA2SpreadStatement)
    {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n) {t : G} (ht : Good103 M Q Z B t)
    {Y : Subgroup G} (hs : Sit M Q Z Y t)
    (hnft : ∀ w ∈ Q, ∀ z ∈ Z, w * t * w⁻¹ = t * z → z = 1)
    {C : Subgroup G} (hCY : C ≤ Q ⊓ QB Y)
    (hCroot : ∀ γ ∈ C, γ ≠ 1 → ∃ D : Subgroup G, Ctx M Q Z D ∧ γ ∈ D ∧ D ≤ C)
    {y : G} (hyD : ∀ D : Subgroup G, Ctx M Q Z D → D ≤ C → y ∈ QB D)
    (hyCt : ∀ x ∈ Q ⊓ Subgroup.centralizer ({t} : Set G), ⁅x, y⁆ ∈ Q ⊓ QB Y)
    {x γ z : G} (hxQ : x ∈ Q) (hγC : γ ∈ C) (hγ1 : γ ≠ 1) (hzZ : z ∈ Z)
    (hγz : γ * z = ⁅x, t⁆) :
    ⁅x, y⁆ ∈ Vt M (LB M Q B) B Z t := by
  have hV : Vt M (LB M Q B) B Z t = (Q ⊓ QB Y) ⊔ Z := Good103.Vt_eq ht hs
  have htZ : ∀ z ∈ Z, t * z = z * t := fun z hz => by
    have h := hc.LB_centralizes_Z ht.1.mem_LB z hz
    calc t * z = (t * z * t⁻¹) * t := by group
      _ = z * t := by rw [h]
  obtain ⟨D, a, hD, hDC, hγD, ha, hat, hγ2, hγa, hta, hxt'⟩ :=
    exists_root_comm_data h34 hspread H ht hs hCY hCroot hγC hγ1 hγz
  have hzγ : z * γ = γ * z := Z_central hc.hyp hzZ (hCY hγC).1
  have hza : z * a = a * z := Z_central hc.hyp hzZ ha.1
  have hct : ⁅a⁻¹ * x, t⁆ = z := comm_inv_mul_eq hγ2 hγa hza hzγ hta hxt'
  have hcQ : a⁻¹ * x ∈ Q := Q.mul_mem (Q.inv_mem ha.1) hxQ
  have hcx : a⁻¹ * x ∈ Subgroup.centralizer ({t} : Set G) := by
    refine mem_centralizer_of_comm_mem_Z htZ hnft hcQ ?_
    rw [hct]
    exact hzZ
  have hcy : ⁅a⁻¹ * x, y⁆ ∈ Q ⊓ QB Y := hyCt _ ⟨hcQ, hcx⟩
  have hcyV : ⁅a⁻¹ * x, y⁆ ∈ Vt M (LB M Q B) B Z t := by
    rw [hV]
    exact Subgroup.mem_sup_left hcy
  have hZV : Z ≤ Vt M (LB M Q B) B Z t := by
    rw [hV]
    exact fun z hz => Subgroup.mem_sup_right hz
  have hDV : D ≤ Vt M (LB M Q B) B Z t := by
    rw [hV]
    exact fun v hv => Subgroup.mem_sup_left (hCY (hDC hv))
  have hay : ⁅a, y⁆ ∈ Vt M (LB M Q B) B Z t :=
    hDV (hD.comm_QB_le_B ha.2 (hyD _ hD hDC))
  have hcommZ : ⁅a, ⁅a⁻¹ * x, y⁆⁆ ∈ Z := comm_mem_Z hc.hyp ha.1 hcy.1
  have hconj : a * ⁅a⁻¹ * x, y⁆ * a⁻¹ ∈ Vt M (LB M Q B) B Z t := by
    have h1 : a * ⁅a⁻¹ * x, y⁆ * a⁻¹ = ⁅a, ⁅a⁻¹ * x, y⁆⁆ * ⁅a⁻¹ * x, y⁆ := by
      rw [commutatorElement_def]; group
    rw [h1]
    exact (Vt M (LB M Q B) B Z t).mul_mem (hZV hcommZ) hcyV
  have hfinal : ⁅x, y⁆ = (a * ⁅a⁻¹ * x, y⁆ * a⁻¹) * ⁅a, y⁆ := by
    rw [show x = a * (a⁻¹ * x) by group, commutatorElement_def]
    group
  rw [hfinal]
  exact (Vt M (LB M Q B) B Z t).mul_mem hconj hay

private theorem comm_mem_Vt_of_comm_mem_sup (h34 : Stroth34Statement)
    (hspread : StrothNoA2SpreadStatement)
    {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n) {t : G} (ht : Good103 M Q Z B t)
    {Y : Subgroup G} (hs : Sit M Q Z Y t)
    (hnft : ∀ w ∈ Q, ∀ z ∈ Z, w * t * w⁻¹ = t * z → z = 1)
    {C : Subgroup G} (hCY : C ≤ Q ⊓ QB Y)
    (hCroot : ∀ γ ∈ C, γ ≠ 1 → ∃ D : Subgroup G, Ctx M Q Z D ∧ γ ∈ D ∧ D ≤ C)
    {y : G} (hyD : ∀ D : Subgroup G, Ctx M Q Z D → D ≤ C → y ∈ QB D)
    (hyCt : ∀ x ∈ Q ⊓ Subgroup.centralizer ({t} : Set G), ⁅x, y⁆ ∈ Q ⊓ QB Y) :
    ∀ x ∈ Q, ⁅x, t⁆ ∈ C ⊔ Z → ⁅x, y⁆ ∈ Vt M (LB M Q B) B Z t := by
  intro x hxQ hxt
  have hnorm : C ≤ Subgroup.normalizer (Z : Set G) := fun c hc' =>
    hc.hyp.Z_normal.2 (hc.hyp.Q_normal.1 (hCY hc').1)
  obtain ⟨γ, hγC, z, hzZ, hγz⟩ :=
    exists_mul_of_mem_sup_of_le_normalizer hnorm hxt
  by_cases hγ1 : γ = 1
  · have hxtZ : ⁅x, t⁆ ∈ Z := by
      rw [← hγz, hγ1, one_mul]
      exact hzZ
    exact comm_mem_Vt_of_comm_mem_Z hc ht hs hnft hyCt hxQ hxtZ
  · exact comm_mem_Vt_of_comm_mem_sup_ne_one h34 hspread H ht hs hnft hCY hCroot
      hyD hyCt hxQ hγC hγ1 hzZ hγz

private def psiToQuot (hc : Ctx M Q Z B) {t y : G} {C Ψ : Subgroup G} (hΨQ : Ψ ≤ Q)
    (hΨt : ∀ x ∈ Ψ, ⁅x, t⁆ ∈ C ⊔ Z)
    (hΨV : ∀ x ∈ Q, ⁅x, t⁆ ∈ C ⊔ Z → ⁅x, y⁆ ∈ Vt M (LB M Q B) B Z t)
    (hcon : ∀ x ∈ Q, ⁅x, y⁆ ∈ Vt M (LB M Q B) B Z t → ⁅x, y⁆ ∈ C ⊔ Z)
    [hCab : IsMulCommutative ↥(C ⊔ Z)] :
    ↥Ψ →* ↥(C ⊔ Z) ⧸ Z.subgroupOf (C ⊔ Z) :=
  MonoidHom.mk' (fun x => QuotientGroup.mk' _ ⟨⁅(x : G), y⁆,
      hcon x.1 (hΨQ x.2) (hΨV x.1 (hΨQ x.2) (hΨt x.1 x.2))⟩) (by
    intro x x'
    apply QuotientGroup.eq_iff_div_mem.mpr
    rw [Subgroup.mem_subgroupOf]
    change ⁅(x : G) * (x' : G), y⁆ / (⁅(x : G), y⁆ * ⁅(x' : G), y⁆) ∈ Z
    have hxQ : (x : G) ∈ Q := hΨQ x.2
    have hx'Q : (x' : G) ∈ Q := hΨQ x'.2
    have hxV : ⁅(x : G), y⁆ ∈ Vt M (LB M Q B) B Z t :=
      hΨV x.1 hxQ (hΨt x.1 x.2)
    have hx'V : ⁅(x' : G), y⁆ ∈ Vt M (LB M Q B) B Z t :=
      hΨV x'.1 hx'Q (hΨt x'.1 x'.2)
    have hbQ : ⁅(x' : G), y⁆ ∈ Q := hc.Vt_le_Q t hx'V
    have hcommZ : ⁅(x : G), ⁅(x' : G), y⁆⁆ ∈ Z := comm_mem_Z hc.hyp hxQ hbQ
    have hcommV : ⁅(x' : G), y⁆ * ⁅(x : G), y⁆ = ⁅(x : G), y⁆ * ⁅(x' : G), y⁆ :=
      (congrArg Subtype.val (hCab.is_comm.comm
        ⟨⁅(x : G), y⁆, hcon x.1 hxQ (hΨV x.1 hxQ (hΨt x.1 x.2))⟩
        ⟨⁅(x' : G), y⁆, hcon x'.1 hx'Q (hΨV x'.1 hx'Q (hΨt x'.1 x'.2))⟩)).symm
    have h1 : ⁅(x : G) * (x' : G), y⁆ =
        ⁅(x : G), ⁅(x' : G), y⁆⁆ * ⁅(x' : G), y⁆ * ⁅(x : G), y⁆ := by
      rw [commutatorElement_def]; group
    have h2 : ⁅(x' : G), y⁆ * ⁅(x : G), y⁆ * ⁅(x' : G), y⁆⁻¹ *
        ⁅(x : G), y⁆⁻¹ = 1 := by
      rw [hcommV]; group
    have hratio : ⁅(x : G) * (x' : G), y⁆ / (⁅(x : G), y⁆ * ⁅(x' : G), y⁆) =
        ⁅(x : G), ⁅(x' : G), y⁆⁆ := by
      calc ⁅(x : G) * (x' : G), y⁆ / (⁅(x : G), y⁆ * ⁅(x' : G), y⁆)
          = (⁅(x : G), ⁅(x' : G), y⁆⁆ * ⁅(x' : G), y⁆ * ⁅(x : G), y⁆) *
              (⁅(x : G), y⁆ * ⁅(x' : G), y⁆)⁻¹ := by rw [h1, div_eq_mul_inv]
        _ = ⁅(x : G), ⁅(x' : G), y⁆⁆ * (⁅(x' : G), y⁆ * ⁅(x : G), y⁆ *
              ⁅(x' : G), y⁆⁻¹ * ⁅(x : G), y⁆⁻¹) := by group
        _ = ⁅(x : G), ⁅(x' : G), y⁆⁆ := by rw [h2, mul_one]
    rw [hratio]
    exact hcommZ)

private theorem psiToQuot_apply (hc : Ctx M Q Z B) {t y : G} {C Ψ : Subgroup G}
    (hΨQ : Ψ ≤ Q) (hΨt : ∀ x ∈ Ψ, ⁅x, t⁆ ∈ C ⊔ Z)
    (hΨV : ∀ x ∈ Q, ⁅x, t⁆ ∈ C ⊔ Z → ⁅x, y⁆ ∈ Vt M (LB M Q B) B Z t)
    (hcon : ∀ x ∈ Q, ⁅x, y⁆ ∈ Vt M (LB M Q B) B Z t → ⁅x, y⁆ ∈ C ⊔ Z)
    [hCab : IsMulCommutative ↥(C ⊔ Z)] (x : ↥Ψ) :
    psiToQuot hc hΨQ hΨt hΨV hcon x =
      QuotientGroup.mk' (Z.subgroupOf (C ⊔ Z))
        (⟨⁅(x : G), y⁆, hcon x.1 (hΨQ x.2)
          (hΨV x.1 (hΨQ x.2) (hΨt x.1 x.2))⟩ : ↥(C ⊔ Z)) := rfl

private theorem ker_psiToQuot (hc : Ctx M Q Z B) {t y : G} {C Ψ : Subgroup G}
    (hΨQ : Ψ ≤ Q)
    (hΨt : ∀ x ∈ Ψ, ⁅x, t⁆ ∈ C ⊔ Z)
    (hΨV : ∀ x ∈ Q, ⁅x, t⁆ ∈ C ⊔ Z → ⁅x, y⁆ ∈ Vt M (LB M Q B) B Z t)
    (hcon : ∀ x ∈ Q, ⁅x, y⁆ ∈ Vt M (LB M Q B) B Z t → ⁅x, y⁆ ∈ C ⊔ Z)
    [hCab : IsMulCommutative ↥(C ⊔ Z)]
    (hyZ : ∀ z ∈ Z, y * z = z * y)
    (hnfy : ∀ w ∈ Q, ∀ z ∈ Z, w * y * w⁻¹ = y * z → z = 1) :
    (psiToQuot hc hΨQ hΨt hΨV hcon).ker =
      (Ψ ⊓ Subgroup.centralizer ({y} : Set G)).subgroupOf Ψ := by
  ext x
  constructor
  · intro hx
    have hx1 : (psiToQuot hc hΨQ hΨt hΨV hcon) x = 1 := hx
    rw [psiToQuot_apply] at hx1
    rw [QuotientGroup.mk'_apply] at hx1
    rw [QuotientGroup.eq_one_iff] at hx1
    have hxyZ : ⁅(x : G), y⁆ ∈ Z := Subgroup.mem_subgroupOf.mp hx1
    have hxQ : (x : G) ∈ Q := hΨQ x.2
    have hxCy : (x : G) ∈ Subgroup.centralizer ({y} : Set G) :=
      mem_centralizer_of_comm_mem_Z hyZ hnfy hxQ hxyZ
    exact Subgroup.mem_subgroupOf.mpr ⟨x.2, hxCy⟩
  · intro hx
    change (psiToQuot hc hΨQ hΨt hΨV hcon) x = 1
    rw [psiToQuot_apply]
    rw [QuotientGroup.mk'_apply]
    rw [QuotientGroup.eq_one_iff]
    refine Subgroup.mem_subgroupOf.mpr ?_
    change ⁅(x : G), y⁆ ∈ Z
    have hxCy : (x : G) ∈ Subgroup.centralizer ({y} : Set G) :=
      (Subgroup.mem_subgroupOf.mp hx).2
    have hxy : ⁅(x : G), y⁆ = 1 := by
      rw [commutatorElement_eq_one_iff_mul_comm]
      exact Subgroup.mem_centralizer_singleton_iff.mp hxCy
    rw [hxy]
    exact Z.one_mem

private theorem card_psi_le_inf_mul_card (hc : Ctx M Q Z B) {t y : G} {C Ψ : Subgroup G}
    (hΨQ : Ψ ≤ Q)
    (hΨt : ∀ x ∈ Ψ, ⁅x, t⁆ ∈ C ⊔ Z)
    (hΨV : ∀ x ∈ Q, ⁅x, t⁆ ∈ C ⊔ Z → ⁅x, y⁆ ∈ Vt M (LB M Q B) B Z t)
    (hcon : ∀ x ∈ Q, ⁅x, y⁆ ∈ Vt M (LB M Q B) B Z t → ⁅x, y⁆ ∈ C ⊔ Z)
    [hCab : IsMulCommutative ↥(C ⊔ Z)]
    (hyZ : ∀ z ∈ Z, y * z = z * y)
    (hnfy : ∀ w ∈ Q, ∀ z ∈ Z, w * y * w⁻¹ = y * z → z = 1)
    (hCquot : Nat.card (↥(C ⊔ Z) ⧸ Z.subgroupOf (C ⊔ Z)) = Nat.card C) :
    Nat.card ↥Ψ ≤ Nat.card ↥(Ψ ⊓ Subgroup.centralizer ({y} : Set G)) * Nat.card C := by
  have hker := ker_psiToQuot hc hΨQ hΨt hΨV hcon hyZ hnfy
  have h1 : Nat.card ↥Ψ = Nat.card ↥(psiToQuot hc hΨQ hΨt hΨV hcon).ker *
      Nat.card ↥(psiToQuot hc hΨQ hΨt hΨV hcon).range :=
    (Subgroup.card_ker_mul_card_range (psiToQuot hc hΨQ hΨt hΨV hcon)).symm
  have h2 : Nat.card ↥(psiToQuot hc hΨQ hΨt hΨV hcon).range ≤
      Nat.card (↥(C ⊔ Z) ⧸ Z.subgroupOf (C ⊔ Z)) := Subgroup.card_le_card_group _
  have h3 : Nat.card ↥((Ψ ⊓ Subgroup.centralizer ({y} : Set G)).subgroupOf Ψ) =
      Nat.card ↥(Ψ ⊓ Subgroup.centralizer ({y} : Set G)) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  calc Nat.card ↥Ψ
      = Nat.card ↥(psiToQuot hc hΨQ hΨt hΨV hcon).ker *
          Nat.card ↥(psiToQuot hc hΨQ hΨt hΨV hcon).range := h1
    _ = Nat.card ↥((Ψ ⊓ Subgroup.centralizer ({y} : Set G)).subgroupOf Ψ) *
          Nat.card ↥(psiToQuot hc hΨQ hΨt hΨV hcon).range := by rw [hker]
    _ = Nat.card ↥(Ψ ⊓ Subgroup.centralizer ({y} : Set G)) *
          Nat.card ↥(psiToQuot hc hΨQ hΨt hΨV hcon).range := by rw [h3]
    _ ≤ Nat.card ↥(Ψ ⊓ Subgroup.centralizer ({y} : Set G)) * Nat.card C := by
        rw [← hCquot]
        exact Nat.mul_le_mul_left _ h2


private theorem card_sup_Z_eq (hc : Ctx M Q Z B) {t : G} {Y : Subgroup G}
    (hs : Sit M Q Z Y t) {C : Subgroup G} (hCY : C ≤ Q ⊓ QB Y) :
    Nat.card ↥(C ⊔ Z) = Nat.card C * Nat.card Z := by
  have hZY : Z ⊓ QB Y = ⊥ := Z_inf_QB_eq_bot hs (smith_1_12 hs)
  have hCZ : C ⊓ Z = ⊥ := by
    rw [inf_comm]
    refine le_antisymm ?_ bot_le
    intro x hx
    have hx1 : x ∈ Q ⊓ QB Y := hCY hx.2
    have hx3 : x ∈ Z ⊓ QB Y := ⟨hx.1, hx1.2⟩
    rw [hZY, Subgroup.mem_bot] at hx3
    exact hx3
  have hnorm : C ≤ Subgroup.normalizer (Z : Set G) := fun c hc' =>
    hc.hyp.Z_normal.2 (hc.hyp.Q_normal.1 (hCY hc').1)
  have hcard := card_sup_mul_card_inf_of_normalizer (A := Z) (C := C) hnorm
  rw [inf_comm, hCZ, Subgroup.card_bot, mul_one, sup_comm, mul_comm] at hcard
  exact hcard

private theorem card_quotient_sup_Z_eq (hc : Ctx M Q Z B) {t : G} {Y : Subgroup G}
    (hs : Sit M Q Z Y t) {C : Subgroup G} (hCY : C ≤ Q ⊓ QB Y) :
    Nat.card (↥(C ⊔ Z) ⧸ Z.subgroupOf (C ⊔ Z)) = Nat.card C := by
  have hCcard := card_sup_Z_eq hc hs hCY
  have hquot := Subgroup.card_eq_card_quotient_mul_card_subgroup (Z.subgroupOf (C ⊔ Z))
  have hZcard : Nat.card ↥(Z.subgroupOf (C ⊔ Z)) = Nat.card Z :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right : Z ≤ C ⊔ Z)).toEquiv
  rw [hZcard, hCcard] at hquot
  exact (Nat.eq_of_mul_eq_mul_right Nat.card_pos hquot).symm

private theorem card_Q_le_card_inf_mul_pow {t y : G} {m : ℕ} {C Ψ : Subgroup G}
    (hWcard : Nat.card ↥(Wt Q (Vt M (LB M Q B) B Z t)) *
      Nat.card ↥(Vt M (LB M Q B) B Z t) = Nat.card Q * Nat.card Z)
    (hVcard : Nat.card ↥(Vt M (LB M Q B) B Z t) = Nat.card Z ^ (m + 1))
    (hCcard : Nat.card ↥(C ⊔ Z) = Nat.card C * Nat.card Z)
    (h41 : Nat.card ↥(Wt Q (Vt M (LB M Q B) B Z t)) * Nat.card ↥(C ⊔ Z) ≤
      Nat.card ↥Ψ * Nat.card ↥(Vt M (LB M Q B) B Z t))
    (h43 : Nat.card ↥Ψ ≤
      Nat.card ↥(Ψ ⊓ Subgroup.centralizer ({y} : Set G)) * Nat.card C) :
    Nat.card Q ≤ Nat.card ↥(Ψ ⊓ Subgroup.centralizer ({y} : Set G)) *
      Nat.card Z ^ (2 * m) := by
  let V : Subgroup G := Vt M (LB M Q B) B Z t
  let W : Subgroup G := Wt Q V
  let Cy : Subgroup G := Subgroup.centralizer ({y} : Set G)
  have hCpos : 0 < Nat.card C := Nat.card_pos
  have hWq : Nat.card ↥W * Nat.card Z ≤ Nat.card ↥(Ψ ⊓ Cy) * Nat.card ↥V := by
    have hmul : Nat.card C * (Nat.card ↥W * Nat.card Z) ≤
        Nat.card C * (Nat.card ↥(Ψ ⊓ Cy) * Nat.card ↥V) := by
      calc Nat.card C * (Nat.card ↥W * Nat.card Z)
          = Nat.card ↥W * Nat.card ↥(C ⊔ Z) := by rw [hCcard]; ring
        _ ≤ Nat.card ↥Ψ * Nat.card ↥V := h41
        _ ≤ (Nat.card ↥(Ψ ⊓ Cy) * Nat.card C) * Nat.card ↥V :=
            Nat.mul_le_mul_right _ h43
        _ = Nat.card C * (Nat.card ↥(Ψ ⊓ Cy) * Nat.card ↥V) := by ring
    exact Nat.le_of_mul_le_mul_left hmul hCpos
  have hmul2 : (Nat.card ↥W * Nat.card Z) * Nat.card ↥V ≤
      (Nat.card ↥(Ψ ⊓ Cy) * Nat.card ↥V) * Nat.card ↥V :=
    Nat.mul_le_mul_right _ hWq
  have hL : (Nat.card ↥W * Nat.card Z) * Nat.card ↥V =
      Nat.card Q * Nat.card Z ^ 2 := by
    rw [show Nat.card ↥V = Nat.card Z ^ (m + 1) from hVcard]
    have hW' : Nat.card ↥W * Nat.card Z ^ (m + 1) = Nat.card Q * Nat.card Z := by
      rw [← hVcard]
      exact hWcard
    calc Nat.card ↥W * Nat.card Z * Nat.card Z ^ (m + 1)
        = (Nat.card ↥W * Nat.card Z ^ (m + 1)) * Nat.card Z := by ring
      _ = (Nat.card Q * Nat.card Z) * Nat.card Z := by rw [hW']
      _ = Nat.card Q * Nat.card Z ^ 2 := by ring
  have hR : (Nat.card ↥(Ψ ⊓ Cy) * Nat.card ↥V) * Nat.card ↥V =
      (Nat.card ↥(Ψ ⊓ Cy) * Nat.card Z ^ (2 * m)) * Nat.card Z ^ 2 := by
    rw [show Nat.card ↥V = Nat.card Z ^ (m + 1) from hVcard]
    calc (Nat.card ↥(Ψ ⊓ Cy) * Nat.card Z ^ (m + 1)) * Nat.card Z ^ (m + 1)
        = Nat.card ↥(Ψ ⊓ Cy) *
            (Nat.card Z ^ (m + 1) * Nat.card Z ^ (m + 1)) := by ring
      _ = Nat.card ↥(Ψ ⊓ Cy) * Nat.card Z ^ ((m + 1) + (m + 1)) := by rw [← pow_add]
      _ = (Nat.card ↥(Ψ ⊓ Cy) * Nat.card Z ^ (2 * m)) * Nat.card Z ^ 2 := by
            rw [show (m + 1) + (m + 1) = 2 * m + 2 by omega, pow_add]
            ring
  rw [hL, hR] at hmul2
  exact Nat.le_of_mul_le_mul_right hmul2 (pow_pos Nat.card_pos 2)

private theorem card_inf_le_card_inf_of_counts {t y : G} {m : ℕ} {C Ψ : Subgroup G}
    (hWcard : Nat.card ↥(Wt Q (Vt M (LB M Q B) B Z t)) *
      Nat.card ↥(Vt M (LB M Q B) B Z t) = Nat.card Q * Nat.card Z)
    (hVcard : Nat.card ↥(Vt M (LB M Q B) B Z t) = Nat.card Z ^ (m + 1))
    (hCcard : Nat.card ↥(C ⊔ Z) = Nat.card C * Nat.card Z)
    (h41 : Nat.card ↥(Wt Q (Vt M (LB M Q B) B Z t)) * Nat.card ↥(C ⊔ Z) ≤
      Nat.card ↥Ψ * Nat.card ↥(Vt M (LB M Q B) B Z t))
    (h43 : Nat.card ↥Ψ ≤
      Nat.card ↥(Ψ ⊓ Subgroup.centralizer ({y} : Set G)) * Nat.card C)
    (hcardy : Nat.card ↥(Q ⊓ Subgroup.centralizer ({y} : Set G)) *
      Nat.card Z ^ (2 * m) ≤ Nat.card Q) :
    Nat.card ↥(Q ⊓ Subgroup.centralizer ({y} : Set G)) ≤
      Nat.card ↥(Ψ ⊓ Subgroup.centralizer ({y} : Set G)) := by
  have hQle := card_Q_le_card_inf_mul_pow hWcard hVcard hCcard h41 h43
  have hle : Nat.card ↥(Q ⊓ Subgroup.centralizer ({y} : Set G)) * Nat.card Z ^ (2 * m) ≤
      Nat.card ↥(Ψ ⊓ Subgroup.centralizer ({y} : Set G)) * Nat.card Z ^ (2 * m) :=
    le_trans hcardy hQle
  exact Nat.le_of_mul_le_mul_right hle (pow_pos Nat.card_pos (2 * m))

private theorem eq_inf_centralizer_of_counts (hc : Ctx M Q Z B) {t y : G} {m : ℕ}
    {C Ψ : Subgroup G}
    (hΨ : ∀ x : G, x ∈ Ψ ↔ x ∈ Wt Q (Vt M (LB M Q B) B Z t) ∧ ⁅x, t⁆ ∈ C ⊔ Z)
    (h41 : Nat.card ↥(Wt Q (Vt M (LB M Q B) B Z t)) * Nat.card ↥(C ⊔ Z) ≤
      Nat.card ↥Ψ * Nat.card ↥(Vt M (LB M Q B) B Z t))
    (hΨV : ∀ x ∈ Q, ⁅x, t⁆ ∈ C ⊔ Z → ⁅x, y⁆ ∈ Vt M (LB M Q B) B Z t)
    (hVab : IsMulCommutative ↥(Vt M (LB M Q B) B Z t))
    (hCV : C ⊔ Z ≤ Vt M (LB M Q B) B Z t)
    (hCquot : Nat.card (↥(C ⊔ Z) ⧸ Z.subgroupOf (C ⊔ Z)) = Nat.card C)
    (hCcard : Nat.card ↥(C ⊔ Z) = Nat.card C * Nat.card Z)
    (hVcard : Nat.card ↥(Vt M (LB M Q B) B Z t) = Nat.card Z ^ (m + 1))
    (hWcard : Nat.card ↥(Wt Q (Vt M (LB M Q B) B Z t)) *
      Nat.card ↥(Vt M (LB M Q B) B Z t) = Nat.card Q * Nat.card Z)
    (hcon : ∀ x ∈ Q, ⁅x, y⁆ ∈ Vt M (LB M Q B) B Z t → ⁅x, y⁆ ∈ C ⊔ Z)
    (hyZ : ∀ z ∈ Z, y * z = z * y)
    (hnfy : ∀ w ∈ Q, ∀ z ∈ Z, w * y * w⁻¹ = y * z → z = 1)
    (hcardy : Nat.card ↥(Q ⊓ Subgroup.centralizer ({y} : Set G)) *
      Nat.card Z ^ (2 * m) ≤ Nat.card Q) :
    Ψ ⊓ Subgroup.centralizer ({y} : Set G) =
      Q ⊓ Subgroup.centralizer ({y} : Set G) := by
  let Cy : Subgroup G := Subgroup.centralizer ({y} : Set G)
  have hΨQ : Ψ ≤ Q := fun x hx => (Subgroup.mem_inf.mp ((hΨ x).mp hx).1).1
  have hΨt : ∀ x ∈ Ψ, ⁅x, t⁆ ∈ C ⊔ Z := fun x hx => ((hΨ x).mp hx).2
  have hCab : IsMulCommutative ↥(C ⊔ Z) := IsMulCommutative.of_comm fun a b =>
    Subtype.ext (congrArg (fun x : ↥(Vt M (LB M Q B) B Z t) => (x : G))
      (hVab.is_comm.comm ⟨a.1, hCV a.2⟩ ⟨b.1, hCV b.2⟩))
  have h43 := card_psi_le_inf_mul_card hc hΨQ hΨt hΨV hcon (hCab := hCab) hyZ hnfy hCquot
  have hcardQle := card_inf_le_card_inf_of_counts hWcard hVcard hCcard h41 h43 hcardy
  exact Subgroup.eq_of_le_of_card_ge (inf_le_inf_right _ hΨQ) (by
    simpa only [Cy] using hcardQle)

private theorem exists_comm_mem_Vt_not_mem_sup_of_eq {t y : G} {m : ℕ}
    {C Ψ : Subgroup G} (hVQ : Vt M (LB M Q B) B Z t ≤ Q)
    (hΨ : ∀ x : G, x ∈ Ψ ↔ x ∈ Wt Q (Vt M (LB M Q B) B Z t) ∧ ⁅x, t⁆ ∈ C ⊔ Z)
    (hQeq : Ψ ⊓ Subgroup.centralizer ({y} : Set G) =
      Q ⊓ Subgroup.centralizer ({y} : Set G))
    (hCV : C ⊔ Z ≤ Vt M (LB M Q B) B Z t)
    (hCcard : Nat.card ↥(C ⊔ Z) = Nat.card C * Nat.card Z)
    (hVcard : Nat.card ↥(Vt M (LB M Q B) B Z t) = Nat.card Z ^ (m + 1))
    (hClt : Nat.card C < Nat.card Z ^ m)
    (hWU : Wt Q (Q ⊓ Subgroup.centralizer ({y} : Set G)) = Ut Q Z y)
    (hUy : ∀ u ∈ Ut Q Z y, ∃ x ∈ Q, ∃ z ∈ Z, u = ⁅x, y⁆ * z) :
    ∃ x ∈ Q, ⁅x, y⁆ ∈ Vt M (LB M Q B) B Z t ∧ ⁅x, y⁆ ∉ C ⊔ Z := by
  let V : Subgroup G := Vt M (LB M Q B) B Z t
  let Cy : Subgroup G := Subgroup.centralizer ({y} : Set G)
  have hQleΨ : Q ⊓ Cy ≤ Ψ := by rw [← hQeq]; exact inf_le_left
  have hQleW : Q ⊓ Cy ≤ Wt Q V := fun x hx => ((hΨ x).mp (hQleΨ hx)).1
  have hVU : V ≤ Wt Q (Q ⊓ Cy) := by
    intro v hv
    refine Subgroup.mem_inf.mpr ⟨hVQ hv, Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro x hx
    exact ((Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (hQleW hx)).2) v hv).symm
  have hVUy : V ≤ Ut Q Z y := by
    rw [← hWU]
    exact hVU
  have hnotle : ¬ V ≤ C ⊔ Z := by
    intro hle
    have hcard := Subgroup.card_le_of_le hle
    have hlt : Nat.card ↥(C ⊔ Z) < Nat.card ↥V := by
      rw [show V = Vt M (LB M Q B) B Z t from rfl, hCcard, hVcard, pow_succ]
      exact Nat.mul_lt_mul_of_pos_right hClt Nat.card_pos
    omega
  obtain ⟨α, hαV, hαC⟩ := Set.not_subset.mp hnotle
  obtain ⟨x, hxQ, z, hzZ, hα⟩ := hUy α (hVUy hαV)
  have hZV : Z ≤ V := fun z hz => hCV (Subgroup.mem_sup_right hz)
  have hxV : ⁅x, y⁆ ∈ V := by
    have hxy : ⁅x, y⁆ = α * z⁻¹ := by rw [hα]; group
    rw [hxy]
    exact V.mul_mem hαV (hZV (Z.inv_mem hzZ))
  refine ⟨x, hxQ, hxV, ?_⟩
  intro hxy
  exact hαC (by
    rw [hα]
    exact (C ⊔ Z).mul_mem hxy (Subgroup.mem_sup_right hzZ))

theorem Good103.exists_comm_mem_Vt_not_mem_sup (h34 : Stroth34Statement)
    (h311a : Stroth311aStatement) (hspread : StrothNoA2SpreadStatement)
    {hc : Ctx M Q Z B} {n m : ℕ} (H : Sec10Hyp hc n) {t : G} (ht : Good103 M Q Z B t)
    {Y : Subgroup G} (hs : Sit M Q Z Y t) (hm : SLMNat hc t m)
    (hnft : ∀ w ∈ Q, ∀ z ∈ Z, w * t * w⁻¹ = t * z → z = 1)
    {C : Subgroup G} (hCY : C ≤ Q ⊓ QB Y) (hClt : Nat.card C < Nat.card Z ^ m)
    (hCroot : ∀ γ ∈ C, γ ≠ 1 → ∃ D : Subgroup G, Ctx M Q Z D ∧ γ ∈ D ∧ D ≤ C)
    {y : G} (hyZ : ∀ z ∈ Z, y * z = z * y)
    (hyD : ∀ D : Subgroup G, Ctx M Q Z D → D ≤ C → y ∈ QB D)
    (hyCt : ∀ x ∈ Q ⊓ Subgroup.centralizer ({t} : Set G), ⁅x, y⁆ ∈ Q ⊓ QB Y)
    (hnfy : ∀ w ∈ Q, ∀ z ∈ Z, w * y * w⁻¹ = y * z → z = 1)
    (hcardy : Nat.card ↥(Q ⊓ Subgroup.centralizer ({y} : Set G)) * Nat.card Z ^ (2 * m) ≤
      Nat.card Q)
    (hWU : Wt Q (Q ⊓ Subgroup.centralizer ({y} : Set G)) = Ut Q Z y)
    (hUy : ∀ u ∈ Ut Q Z y, ∃ x ∈ Q, ∃ z ∈ Z, u = ⁅x, y⁆ * z) :
    ∃ x ∈ Q, ⁅x, y⁆ ∈ Vt M (LB M Q B) B Z t ∧ ⁅x, y⁆ ∉ C ⊔ Z := by
  obtain ⟨Ψ, hΨ, h41⟩ := exists_psi_card h34 h311a hspread H ht hs hCY
  have hΨV := comm_mem_Vt_of_comm_mem_sup h34 hspread H ht hs hnft hCY hCroot hyD hyCt
  have hVab : IsMulCommutative ↥(Vt M (LB M Q B) B Z t) := by
    have h := (Sit.inf_QB_elemAbelian hs).sup_of_commute hc.hyp.isElemAbelian_Z
      (fun x hx y hy => (Z_central hc.hyp hy hx.1).symm)
    rw [show Vt M (LB M Q B) B Z t = (Q ⊓ QB Y) ⊔ Z from Good103.Vt_eq ht hs]
    exact h.1
  have hCV : C ⊔ Z ≤ Vt M (LB M Q B) B Z t := by
    rw [Good103.Vt_eq ht hs]
    exact sup_le (fun x hx => Subgroup.mem_sup_left (hCY hx))
      (fun z hz => Subgroup.mem_sup_right hz)
  have hCquot := card_quotient_sup_Z_eq hc hs hCY
  have hCcard := card_sup_Z_eq hc hs hCY
  have hVcard := SLMNat.card_Vt hm
  have hWcard := hc.card_Wt_mul_card_Vt t
  by_contra hcon
  have hcon' : ∀ x ∈ Q, ⁅x, y⁆ ∈ Vt M (LB M Q B) B Z t → ⁅x, y⁆ ∈ C ⊔ Z := by
    intro x hxQ hxV
    by_contra hxnot
    exact hcon ⟨x, hxQ, hxV, hxnot⟩
  have hQeq := eq_inf_centralizer_of_counts hc hΨ h41 hΨV hVab hCV hCquot hCcard hVcard
    hWcard hcon' hyZ hnfy hcardy
  exact hcon (exists_comm_mem_Vt_not_mem_sup_of_eq (hc.Vt_le_Q t) hΨ hQeq hCV hCcard
    hVcard hClt hWU hUy)


end CFSG.RankThree.GF2n.Stroth80
