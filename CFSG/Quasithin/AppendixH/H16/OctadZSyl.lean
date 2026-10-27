module

public import CFSG.Quasithin.AppendixH.H16.OctadZCent
public import CFSG.Quasithin.AppendixH.H16.OctadZFaith
public import CFSG.Quasithin.AppendixH.H14.H142Group
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatM24

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.ASVolI.H16

open CFSG.ASVolI.ChH CFSG.Quasithin CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.Mathieu.H16Pf
  CFSG.Quasithin.H.ModChk CFSG.Quasithin.H.Coc CFSG.Quasithin.H.FixSyl CFSG.Quasithin.H.LU24
  CFSG.Monster.Code CFSG.ASVolI.AppH CFSG.Open

private theorem xorF_comm (s t : Fin 16) : xorF s t = xorF t s := by
  apply Fin.ext
  simp [xorF, Nat.xor_comm]

private theorem conj_mem_fixO {d k : S24} (hd : d ∈ octStab octad0) (hk : k ∈ fixO) :
    d * k * d⁻¹ ∈ fixO := by
  have hk' : k ∈ octStab octad0 := fixO_le_octStab_octad0 hk
  have hmem : (⟨k, hk'⟩ : ↥(octStab octad0)) ∈ (octFix octad0).subgroupOf (octStab octad0) :=
    Subgroup.mem_subgroupOf.2 (by rw [octFix_octad0]; exact hk)
  have h1 := (normal_octFix octad0).conj_mem (⟨k, hk'⟩ : ↥(octStab octad0)) hmem
    (⟨d, hd⟩ : ↥(octStab octad0))
  have h2 := Subgroup.mem_subgroupOf.1 h1
  rw [octFix_octad0] at h2
  simpa [Subgroup.coe_mul, Subgroup.coe_inv] using h2

theorem mem_fixO_sup_dGrp_iff {x : S24} :
    x ∈ fixO ⊔ dGrp ↔ ∃ k ∈ fixO, ∃ d ∈ dGrp, x = k * d := by
  let KD : Subgroup S24 :=
    { carrier := {x | ∃ k ∈ fixO, ∃ d ∈ dGrp, x = k * d}
      mul_mem' := by
        rintro x y ⟨k, hk, d, hd, rfl⟩ ⟨k', hk', d', hd', rfl⟩
        refine ⟨k * (d * k' * d⁻¹), fixO.mul_mem hk (conj_mem_fixO (dGrp_le_octStab hd) hk'),
          d * d', dGrp.mul_mem hd hd', ?_⟩
        group
      one_mem' := ⟨1, fixO.one_mem, 1, dGrp.one_mem, by group⟩
      inv_mem' := by
        rintro x ⟨k, hk, d, hd, rfl⟩
        refine ⟨d⁻¹ * k⁻¹ * d, conj_mem_fixO ((octStab octad0).inv_mem (dGrp_le_octStab hd))
          (fixO.inv_mem hk), d⁻¹, dGrp.inv_mem hd, ?_⟩
        group }
  have hle : fixO ⊔ dGrp ≤ KD := by
    refine sup_le ?_ ?_
    · intro k hk
      exact ⟨k, hk, 1, dGrp.one_mem, by group⟩
    · intro d hd
      exact ⟨1, fixO.one_mem, d, hd, by group⟩
  exact ⟨fun hx => hle hx, fun ⟨k, hk, d, hd, hx⟩ => hx ▸ Subgroup.mul_mem_sup hk hd⟩

theorem fixO_sup_dGrp_le_cent :
    fixO ⊔ dGrp ≤ M24g ⊓ Subgroup.centralizer ({koPerm 1} : Set S24) := by
  refine sup_le ?_ ?_
  · refine le_inf (fixO_le_octStab_octad0.trans octStab_octad0_le_AutPerm) ?_
    intro k hk
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    obtain ⟨t, rfl⟩ := (mem_fixO_iff k).1 hk
    rw [koPerm_mul, koPerm_mul, xorF_comm]
  · refine le_inf dGrp_le_M24g ?_
    intro d hd
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    obtain ⟨u, hu⟩ := mem_dGrp_iff.mp hd
    rw [← hu, ← dPerm_one, dPerm_mul, dPerm_mul, xorF_comm]

theorem isPGroup_fixO_sup_dGrp : IsPGroup 2 ↥(fixO ⊔ dGrp) := by
  refine IsPGroup.of_card (n := 7) ?_
  rw [card_fixO_sup_dGrp]
  norm_num

private theorem koPerm_mem_M24g' (t : Fin 16) : koPerm t ∈ M24g :=
  (fixO_le_octStab_octad0.trans octStab_octad0_le_AutPerm) ((mem_fixO_iff _).2 ⟨t, rfl⟩)

private theorem imgCd_zpowers_koOne_eq_zpowers :
    imgCd (Subgroup.zpowers (koPerm 1)) =
      Subgroup.zpowers (rhoC11 AutPerm le_rfl ⟨koPerm 1, koPerm_mem_M24g' 1⟩) := by
  rw [imgCd]
  have hsub : (Subgroup.zpowers (koPerm 1)).subgroupOf AutPerm =
      Subgroup.zpowers (⟨koPerm 1, koPerm_mem_M24g' 1⟩ : ↥AutPerm) := by
    refine le_antisymm ?_ ?_
    · intro σ hσ
      rw [Subgroup.mem_subgroupOf] at hσ
      rw [Subgroup.mem_zpowers_iff] at hσ ⊢
      obtain ⟨n, hn⟩ := hσ
      exact ⟨n, Subtype.ext (by simpa using hn)⟩
    · intro σ hσ
      rw [Subgroup.mem_subgroupOf]
      rw [Subgroup.mem_zpowers_iff]
      rw [Subgroup.mem_zpowers_iff] at hσ
      obtain ⟨n, hn⟩ := hσ
      exact ⟨n, by simpa using congrArg Subtype.val hn⟩
  rw [hsub, MonoidHom.map_zpowers]

private theorem mem_fixV_zpowers_iff' {V : Type*} [CommGroup V] {a : MulAut V} {x : V} :
    x ∈ fixV (Subgroup.zpowers a) ↔ a x = x := by
  constructor
  · intro hx
    exact mem_fixV.1 hx a (Subgroup.mem_zpowers a)
  · intro hx
    rw [mem_fixV]
    intro g hg
    have hle : Subgroup.zpowers a ≤ MulAction.stabilizer (MulAut V) x :=
      Subgroup.zpowers_le.mpr ((MulAction.mem_stabilizer_iff).2 (by simpa [MulAut.smul_def] using hx))
    have hg' := hle hg
    rwa [MulAction.mem_stabilizer_iff, MulAut.smul_def] at hg'

private theorem rho_mem_octV5' {γ : ↥AutPerm} (hγ : (γ : S24) ∈ octStab octad0) {y : W11}
    (hy : y ∈ octV5) : rhoC11 AutPerm le_rfl γ y ∈ octV5 :=
  isActsInv_octV5 (fun v => rhoC11 AutPerm le_rfl γ v)
    ⟨rhoC11 AutPerm le_rfl γ, rhoCd_mem_imgCd γ.2 hγ, rfl⟩ y hy

private theorem conj_mem_dGrp {g d : S24} (hg : g ∈ octStab octad0)
    (hgM : g ∈ M24g) (hgz : g * koPerm 1 = koPerm 1 * g) (hd : d ∈ dGrp) : g * d * g⁻¹ ∈ dGrp := by
  obtain ⟨u, hu⟩ := mem_dGrp_iff.mp hd
  rw [← hu]
  refine mem_dGrp_of_fix_octVz ⟨g * dPerm u * g⁻¹,
    M24g.mul_mem (M24g.mul_mem hgM (dGrp_le_M24g (dPerm_mem_dGrp u))) (M24g.inv_mem hgM)⟩ ?_
  intro x hx
  let gA : ↥AutPerm := ⟨g, hgM⟩
  let dA : ↥AutPerm := ⟨dPerm u, dPerm_mem_M24g u⟩
  let zA : ↥AutPerm := ⟨koPerm 1, koPerm_mem_M24g' 1⟩
  change rhoC11 AutPerm le_rfl (gA * dA * gA⁻¹) x = x
  have hgAx5 : rhoC11 AutPerm le_rfl gA⁻¹ x ∈ octV5 :=
    rho_mem_octV5' (by simpa [gA] using (octStab octad0).inv_mem hg) (octVz_le_octV5 hx)
  have hgAxw : rhoC11 AutPerm le_rfl gA⁻¹ x ∈ octWz := by
    have hxw : x ∈ fixV (Subgroup.zpowers (rhoC11 AutPerm le_rfl zA)) := by
      rw [← imgCd_zpowers_koOne_eq_zpowers, fixV_imgCd_zpowers_koOne]
      exact octVz_le_octWz hx
    have hzx : rhoC11 AutPerm le_rfl zA x = x := (mem_fixV_zpowers_iff').1 hxw
    rw [← fixV_imgCd_zpowers_koOne, imgCd_zpowers_koOne_eq_zpowers, mem_fixV_zpowers_iff']
    have hzg : zA * gA = gA * zA := Subtype.ext (by simpa [zA, gA, Subgroup.coe_mul] using hgz.symm)
    have hzgi : zA * gA⁻¹ = gA⁻¹ * zA := by
      have h1 : gA⁻¹ * zA * gA = zA := by
        calc gA⁻¹ * zA * gA = gA⁻¹ * (zA * gA) := by group
          _ = gA⁻¹ * (gA * zA) := by rw [hzg]
          _ = zA := by group
      calc zA * gA⁻¹ = (gA⁻¹ * zA * gA) * gA⁻¹ := by rw [h1]
        _ = gA⁻¹ * zA := by group
    calc rhoC11 AutPerm le_rfl zA (rhoC11 AutPerm le_rfl gA⁻¹ x)
        = rhoC11 AutPerm le_rfl (zA * gA⁻¹) x := by rw [map_mul, MulAut.mul_apply]
      _ = rhoC11 AutPerm le_rfl (gA⁻¹ * zA) x := by rw [hzgi]
      _ = rhoC11 AutPerm le_rfl gA⁻¹ (rhoC11 AutPerm le_rfl zA x) := by
            rw [map_mul, MulAut.mul_apply]
      _ = rhoC11 AutPerm le_rfl gA⁻¹ x := by rw [hzx]
  have hgAx : rhoC11 AutPerm le_rfl gA⁻¹ x ∈ octVz := by
    rw [← octV5_inf_octWz]
    exact ⟨hgAx5, hgAxw⟩
  calc rhoC11 AutPerm le_rfl (gA * dA * gA⁻¹) x
      = rhoC11 AutPerm le_rfl gA (rhoC11 AutPerm le_rfl dA (rhoC11 AutPerm le_rfl gA⁻¹ x)) := by
          simp only [map_mul, MulAut.mul_apply]
    _ = rhoC11 AutPerm le_rfl gA (rhoC11 AutPerm le_rfl gA⁻¹ x) := by
          rw [show rhoC11 AutPerm le_rfl dA (rhoC11 AutPerm le_rfl gA⁻¹ x) =
            rhoC11 AutPerm le_rfl gA⁻¹ x from rhoC11_dPerm_fix_octVz u hgAx]
    _ = x := by rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]

theorem fixO_sup_dGrp_normal_in_cent :
    ((fixO ⊔ dGrp).subgroupOf (M24g ⊓ Subgroup.centralizer ({koPerm 1} : Set S24))).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  show (g : S24) * (n : S24) * (g : S24)⁻¹ ∈ fixO ⊔ dGrp
  obtain ⟨k, hk, d, hd, hn'⟩ := (mem_fixO_sup_dGrp_iff).1 hn
  rw [hn']
  have hg_stab : (g : S24) ∈ octStab octad0 := cent_koOne_le_octStab g.2
  have hgz : (g : S24) * koPerm 1 = koPerm 1 * (g : S24) :=
    (Subgroup.mem_centralizer_iff.mp g.2.2 (koPerm 1) (Set.mem_singleton _)).symm
  refine (mem_fixO_sup_dGrp_iff).2 ⟨(g : S24) * k * (g : S24)⁻¹,
    conj_mem_fixO hg_stab hk, (g : S24) * d * (g : S24)⁻¹,
    conj_mem_dGrp hg_stab g.2.1 hgz hd, ?_⟩
  group

private theorem m24Mems_o2_of_order_21504 :
    ∀ m ∈ CFSG.QuasithinUnique.Ch1.SporLat.M24.m24Mems, m.order = 21504 → m.o2 = 128 := by
  decide +kernel

theorem card_pCoreOf_cent_koOne :
    Nat.card ↥(pCoreOf 2 (M24g ⊓ Subgroup.centralizer ({koPerm 1} : Set S24))) = 128 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let C : Subgroup S24 := M24g ⊓ Subgroup.centralizer ({koPerm 1} : Set S24)
  let X : Type := ↥AutPerm
  have hle : C ≤ AutPerm := inf_le_left
  let Y : Subgroup X := C.subgroupOf AutPerm
  change Nat.card ↥(pCoreOf 2 C) = 128
  have hC : Nat.card ↥C = 21504 := card_cent_koOne
  have hY : Nat.card ↥Y = 21504 := by
    show Nat.card ↥(C.subgroupOf AutPerm) = 21504
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv]
    exact hC
  have hXcard : Nat.card X = 244823040 := card_AutPerm
  let P₂ : Sylow 2 ↥Y := Classical.choice (Sylow.nonempty (p := 2) (G := ↥Y))
  let T : Subgroup X := (P₂ : Subgroup ↥Y).map Y.subtype
  have hfac : (Nat.card ↥Y).factorization 2 = 10 := by
    rw [hY]
    have h : (21504 : ℕ) = 2 ^ 10 * 21 := by norm_num
    rw [h, Nat.factorization_mul (by norm_num) (by norm_num),
      Nat.Prime.factorization_pow Nat.prime_two]
    have h2 : (21 : ℕ).factorization 2 = 0 :=
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)
    simp [h2]
  have hP2card : Nat.card ↥(P₂ : Subgroup ↥Y) = 2 ^ 10 := by
    rw [Sylow.card_eq_multiplicity, hfac]
  have hcardT : Nat.card ↥T = 2 ^ 10 := by
    rw [Subgroup.card_map_of_injective Y.subtype_injective, hP2card]
  have hT2 : IsPGroup 2 T := IsPGroup.map P₂.isPGroup' Y.subtype
  have hTY : T ≤ Y := Subgroup.map_subtype_le (P₂ : Subgroup ↥Y)
  have hIdx : T.index = 239085 := by
    have h := Subgroup.card_mul_index T
    rw [hcardT, hXcard] at h
    have h2 : (244823040 : ℕ) = 2 ^ 10 * 239085 := by norm_num
    rw [h2] at h
    exact Nat.eq_of_mul_eq_mul_left (by positivity) h
  have hTsylow : CFSG.QuasithinUnique.IsSylowTwoOf T ⊤ := by
    refine ⟨le_top, hT2, ?_⟩
    show ¬ 2 ∣ T.relIndex ⊤
    rw [Subgroup.relIndex_top_right, hIdx]
    norm_num
  have hX : Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.Carrier .M24) := ⟨autPermEquivM24'⟩
  have hpc : Nat.card ↥(pCore 2 ↥C) = Nat.card ↥(pCore 2 ↥Y) := by
    have e : ↥Y ≃* ↥C := Subgroup.subgroupOfEquivOfLe hle
    have h := CFSG.pCore_map_iso (G := ↥Y) (G' := ↥C) 2 e
    rw [← h, Subgroup.card_map_of_injective e.injective]
  have htransfer : Nat.card ↥(pCoreOf 2 C) = Nat.card ↥(pCoreOf 2 Y) := by
    rw [pCoreOf, pCoreOf, Subgroup.card_map_of_injective C.subtype_injective,
      Subgroup.card_map_of_injective Y.subtype_injective]
    exact hpc
  rcases CFSG.QuasithinUnique.Ch1.SporLat.M24.m24_overgroups hX hTsylow hTY with htop | ⟨m, hm, hord, ho2, -⟩
  · exfalso
    rw [htop, Subgroup.card_top, hXcard] at hY
    norm_num at hY
  · have hmo : m.order = 21504 := by rw [← hord]; exact hY
    have hmo2 : m.o2 = 128 := m24Mems_o2_of_order_21504 m hm hmo
    have hYp : Nat.card ↥(pCoreOf 2 Y) = 128 := by rw [ho2, hmo2]
    exact htransfer.trans hYp

theorem pCoreOf_cent_koOne :
    pCoreOf 2 (M24g ⊓ Subgroup.centralizer ({koPerm 1} : Set S24)) = fixO ⊔ dGrp := by
  let C : Subgroup S24 := M24g ⊓ Subgroup.centralizer ({koPerm 1} : Set S24)
  let P : Subgroup S24 := fixO ⊔ dGrp
  change pCoreOf 2 C = P
  have hPC : P ≤ C := fixO_sup_dGrp_le_cent
  have hPnorm : (P.subgroupOf C).Normal := fixO_sup_dGrp_normal_in_cent
  have hP2 : IsPGroup 2 P := isPGroup_fixO_sup_dGrp
  have hle : P ≤ pCoreOf 2 C :=
    CFSG.Quasithin.AppendixH.H14.le_pCoreOf_of_normal hPC hPnorm hP2
  have hcardP : Nat.card ↥P = 128 := card_fixO_sup_dGrp
  have hcardC : Nat.card ↥(pCoreOf 2 C) = 128 := card_pCoreOf_cent_koOne
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hcardC, hcardP])).symm

end CFSG.ASVolI.H16
