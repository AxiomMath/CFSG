module

public import CFSG.Quasithin.H13.L32A767n
public import CFSG.Quasithin.H13.L32A767j
public import CFSG.Quasithin.H13.L32A767m

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open CFSG.Quasithin.CosetGeom

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

abbrev eD (T V : Subgroup G) : Subgroup G := conjClosure (fsuV1 T V) (dK T V)

omit [Finite G] in
theorem eD_le_centralizer_kz : eD T V ≤ Subgroup.centralizer (kz T V : Set G) := by
  refine conjClosure_le fun d hd v hv => Subgroup.mem_centralizer_iff.mpr fun k hk => ?_
  have hk' : d⁻¹ * k * d ∈ kz T V := by
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem hd.1) k).mp hk
    simpa using this
  have hkv : v * (d⁻¹ * k * d) = (d⁻¹ * k * d) * v :=
    Subgroup.mem_centralizer_iff.mp (oTwoUpper_le _ hk') v hv
  calc k * (d * v * d⁻¹) = d * ((d⁻¹ * k * d) * v) * d⁻¹ := by group
    _ = d * (v * (d⁻¹ * k * d)) * d⁻¹ := by rw [hkv]
    _ = d * v * d⁻¹ * k := by group

omit [Finite G] in
theorem kz_le_centralizer_eD : kz T V ≤ Subgroup.centralizer (eD T V : Set G) :=
  Subgroup.le_centralizer_iff.mp eD_le_centralizer_kz

theorem hz_le_normalizer_eD : hz T V ≤ Subgroup.normalizer (eD T V : Set G) := by
  intro g hg
  have key : eD T V ≤ (eD T V).comap (MulAut.conj g).toMonoidHom := by
    refine conjClosure_le fun d hd v hv => ?_
    show g * (d * v * d⁻¹) * g⁻¹ ∈ eD T V
    have hgd : g * d * g⁻¹ ∈ dK T V :=
      (Subgroup.mem_normalizer_iff.mp (mK_le_normalizer_dK (le_normalizer_oTwoUpper _ hg)) d).mp
        hd
    have hgv : g * v * g⁻¹ = v := by
      rw [← Subgroup.mem_centralizer_iff.mp hg v hv, mul_inv_cancel_right]
    rw [show g * (d * v * d⁻¹) * g⁻¹ = (g * d * g⁻¹) * (g * v * g⁻¹) * (g * d * g⁻¹)⁻¹ by
      group, hgv]
    exact Subgroup.subset_closure ⟨_, hgd, v, hv, rfl⟩
  exact mem_normalizer_of_forall_conj_mem fun x hx => key hx

theorem mem_mK_of_conjSub_le {g : G} (hg : conjSub g (fsuV1 T V) ≤ eD T V) : g ∈ mK T V := by
  have hKH : ∀ k ∈ kz T V, g⁻¹ * k * g ∈ hz T V := by
    intro k hk
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have hgv : g * v * g⁻¹ ∈ eD T V := hg (mul_mem_conjSub hv)
    have hc := Subgroup.mem_centralizer_iff.mp (kz_le_centralizer_eD hk) _ hgv
    calc v * (g⁻¹ * k * g) = g⁻¹ * ((g * v * g⁻¹) * k) * g := by group
      _ = g⁻¹ * (k * (g * v * g⁻¹)) * g := by rw [hc]
      _ = g⁻¹ * k * g * v := by group
  have hKK : ∀ k ∈ kz T V, g⁻¹ * k * g ∈ kz T V := by
    intro k hk
    induction hk using Subgroup.closure_induction with
    | mem x hx =>
      refine mem_oTwoUpper_of_odd (hKH x (mem_oTwoUpper_of_odd hx.1 hx.2)) ?_
      rw [show g⁻¹ * x * g = g⁻¹ * x * g⁻¹⁻¹ by rw [inv_inv], ← MulAut.conj_apply,
        MulEquiv.orderOf_eq]
      exact hx.2
    | one => simp
    | mul x y _ _ ihx ihy =>
      rw [show g⁻¹ * (x * y) * g = (g⁻¹ * x * g) * (g⁻¹ * y * g) by group]
      exact mul_mem ihx ihy
    | inv x _ ih =>
      rw [show g⁻¹ * x⁻¹ * g = (g⁻¹ * x * g)⁻¹ by group]
      exact inv_mem ih
  have hgi : g⁻¹ ∈ mK T V := mem_normalizer_of_forall_conj_mem fun k hk => by
    rw [inv_inv]
    exact hKK k hk
  simpa using inv_mem hgi

theorem conjSub_le_centralizer_eD (h : Hyp147 G T L V) (hMod : StmtL32NModule)
    (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4) {g : G}
    (hg : conjSub g (fsuV1 T V) ≤ eD T V) :
    conjSub g V ≤ Subgroup.centralizer (eD T V : Set G) := by
  have hgK := mem_mK_of_conjSub_le hg
  intro x hx
  rw [mem_conjSub] at hx
  have hxK : x ∈ kz T V := by
    have := (Subgroup.mem_normalizer_iff.mp hgK _).mp (v_le_kz h hMod h1222 h1332 h1334 hx)
    simpa [mul_assoc] using this
  exact kz_le_centralizer_eD hxK

theorem normalizer_le_of_relIndex_le_two (h : Hyp147 G T L V) (hMod : StmtL32NModule)
    (h63 : Thm14_7_63) (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4)
    (hF : HypF98 T V L (fsuV1 T V) V (hz T V)) {P : Subgroup G}
    (hPR : P ≤ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T))
    (hRP : pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) ≤ Subgroup.normalizer (P : Set G))
    (hidx : P.relIndex (pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T)) ≤ 2) :
    (dK T V ⊔ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T)) ⊓ Subgroup.normalizer (P : Set G) ≤
      Subgroup.normalizer (L : Set G) := by
  have h13322 := stmt13_3_2_two_of h1332
  have h672 := (lemma14_7_67_one_two_five h h1222 h1332 h1334 h63 hF).2.1
  set R := pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) with hR
  set X := dK T V ⊔ R with hX
  set Y := X ⊓ Subgroup.normalizer (P : Set G) with hY
  set VY := eD T V ⊓ Subgroup.centralizer (pCoreOf 2 Y : Set G) with hVY
  have hSX := isSylowTwoOf_R1_dK h hMod h63
  have hTH := T_le_hz h h63
  have hRT : R ≤ T :=
    EscapingLocal.pCoreOf_le_of_isSylowTwoOf (isSylowTwoOf_of_le h le_sup_right)
  have hRY : R ≤ Y := le_inf le_sup_right hRP
  have hS : IsSylowTwoOf R Y := by
    refine ⟨hRY, pCoreOf_isPGroup 2 _, fun h2 => hSX.2.2 (h2.trans ?_)⟩
    exact Dvd.intro _ (Subgroup.relIndex_mul_relIndex R Y X hRY inf_le_left)
  have hPO : P ≤ pCoreOf 2 Y :=
    le_pCoreOf_of_le_normalizer 2 (hPR.trans hRY) inf_le_right ((pCoreOf_isPGroup 2 _).to_le hPR)
  have hidx' : (pCoreOf 2 Y).relIndex R ≤ 2 := by
    have hpos : 0 < P.relIndex R := Nat.pos_of_ne_zero fun h0 => by
      have e := Subgroup.relIndex_mul_card P R
      rw [h0, zero_mul] at e
      exact (Nat.card_pos (α := ↥R)).ne' e.symm
    exact (Nat.le_of_dvd hpos (Subgroup.relIndex_dvd_of_le_left R hPO)).trans hidx
  have hXE : X ≤ Subgroup.normalizer (eD T V : Set G) :=
    sup_le (le_normalizer_conjClosure _ _) (hRT.trans (hTH.trans hz_le_normalizer_eD))
  have hYC : Y ≤ Subgroup.normalizer (Subgroup.centralizer (pCoreOf 2 Y : Set G) : Set G) := by
    intro y hy
    refine mem_normalizer_of_forall_conj_mem fun c hc => ?_
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro o ho
    have ho' : y⁻¹ * o * y ∈ pCoreOf 2 Y := by
      have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 Y (inv_mem hy)) o).mp ho
      simpa using this
    have := hc _ ho'
    calc o * (y * c * y⁻¹) = y * ((y⁻¹ * o * y) * c) * y⁻¹ := by group
      _ = y * (c * (y⁻¹ * o * y)) * y⁻¹ := by rw [this]
      _ = y * c * y⁻¹ * o := by group
  have hYV : Y ≤ Subgroup.normalizer (VY : Set G) := fun y hy =>
    mem_normalizer_inf_of_mem (hXE hy.1) (hYC hy)
  have hOV : pCoreOf 2 Y ≤ Subgroup.centralizer (VY : Set G) := by
    intro o ho
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hv).2 o ho).symm
  have hV1VY : fsuV1 T V ≤ VY := by
    refine le_inf (le_conjClosure _ _) fun v hv => Subgroup.mem_centralizer_iff.mpr fun o ho => ?_
    have hoH : o ∈ hz T V :=
      hTH (hRT (EscapingLocal.pCoreOf_le_of_isSylowTwoOf hS ho))
    exact (Subgroup.mem_centralizer_iff.mp hoH v hv).symm
  have hCY : Y ⊓ Subgroup.centralizer (VY : Set G) ≤ pCoreOf 2 Y := by
    have hle : Y ⊓ Subgroup.centralizer (VY : Set G) ≤ R := fun x hx =>
      inf_hz_le_R1 h hMod h63 ⟨hx.1.1, Subgroup.centralizer_le hV1VY hx.2⟩
    refine le_pCoreOf_of_le_normalizer 2 inf_le_left (fun y hy => ?_)
      ((pCoreOf_isPGroup 2 _).to_le hle)
    refine mem_normalizer_inf_of_mem (Subgroup.le_normalizer hy) ?_
    refine mem_normalizer_of_forall_conj_mem fun c hc => ?_
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro v hv
    have hv' : y⁻¹ * v * y ∈ VY := by
      have := (Subgroup.mem_normalizer_iff.mp (hYV (inv_mem hy)) v).mp hv
      simpa using this
    have := hc _ hv'
    calc v * (y * c * y⁻¹) = y * ((y⁻¹ * v * y) * c) * y⁻¹ := by group
      _ = y * (c * (y⁻¹ * v * y)) * y⁻¹ := by rw [this]
      _ = y * c * y⁻¹ * v := by group
  have hCV : R ⊓ Subgroup.centralizer (VY : Set G) ≤ pCoreOf 2 Y := fun x hx =>
    hCY ⟨hRY hx.1, hx.2⟩
  have hU : ∀ g : G, conjSub g (fsuV1 T V) ≤ VY →
      conjSub g V ≤ Subgroup.centralizer (VY : Set G) := fun g hg =>
    (conjSub_le_centralizer_eD h hMod h1222 h1332 h1334 (hg.trans inf_le_left)).trans
      (Subgroup.centralizer_le inf_le_left)
  exact (le_normalizer_wClos_R1_of h hMod h13322 h672 hS hidx' hYV hOV hCV hU).trans
    (normalizer_wClos_R1_le h hMod h63 h13322 hF h672)

theorem eq_one_of_normalizes (h : Hyp147 G T L V) (hMod : StmtL32NModule) (h63 : Thm14_7_63)
    (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4)
    (hF : HypF98 T V L (fsuV1 T V) V (hz T V)) {P : Subgroup G}
    (hPR : P ≤ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T))
    (hRP : pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) ≤ Subgroup.normalizer (P : Set G))
    (hidx : P.relIndex (pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T)) ≤ 2) {y : G} (hyD : y ∈ dK T V)
    (hyP : y ∈ Subgroup.normalizer (P : Set G)) (hodd : Odd (orderOf y)) : y = 1 :=
  eq_one_of_mem_dK_of_odd h hMod h63 (stmt13_3_2_two_of h1332) hyD
    (normalizer_le_of_relIndex_le_two h hMod h63 h1222 h1332 h1334 hF hPR hRP hidx
      ⟨Subgroup.mem_sup_left hyD, hyP⟩) hodd

end CFSG.Quasithin.H13.L32A
