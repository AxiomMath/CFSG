module

public import CFSG.Quasithin.H13.AS91Sec4EightBar

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.AS91

open Subgroup Module CFSG.Open CFSG.LargeExtraspecial CFSG.Quasithin CFSG.Quasithin.HatM22
open CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.GammaU.StepA
open CFSG.GF2Type.Smith1979.GammaU.Viol CFSG.GF2Type.Smith1979.GammaU.Enum
open CFSG.GF2Type.Smith1979.IdxFour
open scoped Pointwise

namespace Data41

variable {G : Type} [Group G] [Finite G] {z : G} {h : HypJ4 G z} (D : Data41 h)

section Img


theorem G13_le_M : D.G13 ≤ h.setting.M := pre_le_M _

theorem G13_le_N : D.G13 ≤ normalizer (D.E : Set G) := fun _ hg =>
  mem_normalizer_fintype fun _ he => D.conj_mem_E hg he

theorem QG_le_N : h.setting.QG ≤ normalizer (D.E : Set G) := fun _ hq =>
  D.G13_le_N (QG_le_pre _ hq)

@[expose] noncomputable def img (L : Subgroup G) : Subgroup ↥D.Mb :=
  (L.subgroupOf (normalizer (D.E : Set G))).map D.toMb

theorem mem_img {L : Subgroup G} {φ : ↥D.Mb} :
    φ ∈ D.img L ↔ ∃ (m : G) (hm : m ∈ normalizer (D.E : Set G)), m ∈ L ∧ D.toMb ⟨m, hm⟩ = φ := by
  constructor
  · rintro ⟨⟨m, hm⟩, hmL, rfl⟩
    exact ⟨m, hm, hmL, rfl⟩
  · rintro ⟨m, hm, hmL, rfl⟩
    exact ⟨⟨m, hm⟩, hmL, rfl⟩

theorem toMb_mem_img {L : Subgroup G} {m : G} (hm : m ∈ normalizer (D.E : Set G)) (hmL : m ∈ L) :
    D.toMb ⟨m, hm⟩ ∈ D.img L := D.mem_img.mpr ⟨m, hm, hmL, rfl⟩

end Img

section Card

variable
  (hOut : KG82HatM22Out) (hTw : KG82HatM22Twelve)
  (hHat : HatM22SmallModules)

include hOut hTw hHat

theorem card_img {L : Subgroup G} (hLN : L ≤ normalizer (D.E : Set G)) (hEL : D.E ≤ L) :
    Nat.card (D.img L) * Nat.card D.E = Nat.card L := by
  let f : ↥L →* ↥D.Mb := D.toMb.comp (Subgroup.inclusion hLN)
  have hrange : f.range = D.img L := by
    ext φ
    rw [MonoidHom.mem_range, D.mem_img]
    constructor
    · rintro ⟨⟨m, hmL⟩, rfl⟩
      exact ⟨m, hLN hmL, hmL, rfl⟩
    · rintro ⟨m, hm, hmL, rfl⟩
      exact ⟨⟨m, hmL⟩, rfl⟩
  have hker : Nat.card f.ker = Nat.card D.E := by
    refine Nat.card_congr (Equiv.ofBijective (fun x : f.ker => (⟨((x : ↥L) : G), ?_⟩ : ↥D.E))
      ⟨fun x y hxy => ?_, fun e => ?_⟩)
    · have hx := MonoidHom.mem_ker.mp x.2
      exact (D.toMb_eq_one_iff hOut hTw hHat _).mp hx
    · exact Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hxy))
    · refine ⟨⟨⟨e, hEL e.2⟩, MonoidHom.mem_ker.mpr ?_⟩, rfl⟩
      exact (D.toMb_eq_one_iff hOut hTw hHat ⟨e, hLN (hEL e.2)⟩).mpr e.2
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv, hrange, hker] at h1
  exact h1.symm

theorem Mz_eq_img : D.Mz = D.img D.G13 := by
  ext φ
  rw [D.mem_Mz_iff hOut hTw, D.mem_img]
  constructor
  · rintro ⟨m, hm, rfl⟩
    exact ⟨m, _, hm, rfl⟩
  · rintro ⟨m, hmN, hm, rfl⟩
    exact ⟨m, hm, rfl⟩

theorem card_Mz : Nat.card D.Mz = 138240 := by
  have h1 := D.card_img hOut hTw hHat D.G13_le_N (D.E_le_G13 hOut hTw)
  rw [← D.Mz_eq_img hOut hTw hHat, D.card_E hOut hTw, D.card_G13 hOut hTw] at h1
  omega

end Card

section Shape

variable
  (hOut : KG82HatM22Out) (hTw : KG82HatM22Twelve)

include hOut hTw

theorem presE1_of_mem_Mz {φ : ↥D.Mb} (hφ : φ ∈ D.Mz) : D.PresE1 (φ : MulAut ↥D.E) := by
  obtain ⟨m, hm, rfl⟩ := (D.mem_Mz_iff hOut hTw).mp hφ
  intro x hx
  exact D.conj_mem_E1 hm hx

theorem eq_of_agree_E1 (hHat : HatM22SmallModules) {φ ψ : ↥D.Mb}
    (h1 : ∀ x : ↥D.E, (x : G) ∈ D.E1 → (φ : MulAut ↥D.E) x = (ψ : MulAut ↥D.E) x) : φ = ψ := by
  obtain ⟨⟨m, hm⟩, rfl⟩ := D.toMb_surjective φ
  obtain ⟨⟨n, hn⟩, rfl⟩ := D.toMb_surjective ψ
  have hc : n⁻¹ * m ∈ D.E := D.mem_E.mpr fun y hy => by
    have h2 := congrArg Subtype.val (h1 ⟨y, D.E1_le_E hy⟩ hy)
    change m * y * m⁻¹ = n * y * n⁻¹ at h2
    calc y * (n⁻¹ * m) = n⁻¹ * (n * y * n⁻¹) * m := by group
      _ = n⁻¹ * (m * y * m⁻¹) * m := by rw [h2]
      _ = n⁻¹ * m * y := by group
  apply Subtype.ext
  apply MulEquiv.ext
  intro e
  apply Subtype.ext
  change m * e * m⁻¹ = n * e * n⁻¹
  have hEc : (n⁻¹ * m) * e = e * (n⁻¹ * m) := D.E_comm hOut hTw hHat hc e.2
  calc m * e * m⁻¹ = n * ((n⁻¹ * m) * e * (n⁻¹ * m)⁻¹) * n⁻¹ := by group
    _ = n * e * n⁻¹ := by rw [hEc, mul_inv_cancel_right]

end Shape

section Kap


theorem crd_div_two (x : G) : D.crd x / 2 = Two.crd6 (D.wc x) := by
  unfold crd
  split_ifs <;> omega

theorem wc_conj {m : G} (hm : m ∈ h.setting.M) {x : G} (hx : x ∈ h.setting.QG) :
    D.wc (m * x * m⁻¹) = codeOf (D.Φo (h.setting.ρ ⟨m, hm⟩) (vecOf (D.wc x))) := by
  rw [wc, ← h.setting.ρ_cl ⟨m, hm⟩ hx, ← Φo_apply_ψV, wc, vecOf_codeOf]

theorem appN_rowsOf (U : V12 ≃ₗ[ZMod 2] V12) {n : ℕ} (hn : n < 4096) :
    appN (rowsOf U) n = codeOf (U (vecOf n)) := by
  have h1 : vecOf (appN (rowsOf U) n) = U (vecOf n) := by
    rw [vecOf_appN, linOfRows_rowsOf]
  rw [← h1, codeOf_vecOf (appN_lt (rowsOf_lt U) _)]

end Kap

section Shape2

variable
  (hOut : KG82HatM22Out) (hTw : KG82HatM22Twelve)

include hOut hTw

theorem kap_toMb {m : G} (hm : m ∈ D.G13) :
    D.kap (D.toMb ⟨m, D.G13_le_N hm⟩ : MulAut ↥D.E) =
      Two.mk7 (Two.lam6 (D.kap (D.toMb ⟨m, D.G13_le_N hm⟩ : MulAut ↥D.E)))
        (Two.res6 (rowsOf (D.Φo (h.setting.ρ ⟨m, D.G13_le_M hm⟩)))) := by
  set φ : MulAut ↥D.E := (D.toMb ⟨m, D.G13_le_N hm⟩ : MulAut ↥D.E)
  have h0 : (D.kap φ)[0]! = 1 := by
    rw [D.kap_getElem φ (by norm_num)]
    have : ((φ (D.bEE 0) : ↥D.E) : G) = z := by
      change m * D.bE 0 * m⁻¹ = z
      rw [bE, if_pos rfl]
      have := h.setting.z_comm (D.G13_le_M hm)
      rw [h.setting_z] at this
      rw [this, mul_inv_cancel_right]
    rw [this, D.crd_z]
  have hA : Two.aPart (D.kap φ) = Two.res6 (rowsOf (D.Φo (h.setting.ρ ⟨m, D.G13_le_M hm⟩))) := by
    apply List.ext_getElem
    · simp [Two.aPart, Two.res6, kap_size, Two.w1Basis]
    · intro i h1 h2
      have hi : i < 6 := by simpa [Two.res6, Two.w1Basis] using h2
      have e1 : (Two.aPart (D.kap φ))[i] = (D.kap φ)[i + 1]! / 2 := by
        rw [getElem!_pos _ (i + 1) (by rw [kap_size]; omega)]
        simp [Two.aPart, kap_size, hi]
      refine e1.trans ?_
      rw [D.kap_getElem φ (by omega), crd_div_two]
      have e2 : ((φ (D.bEE (i + 1)) : ↥D.E) : G) =
          m * D.rep (Two.w1Basis.getD i 0) * m⁻¹ := by
        change m * D.bE (i + 1) * m⁻¹ = _
        rw [bE, if_neg (by omega)]
        rfl
      rw [e2, D.wc_conj (D.G13_le_M hm) (D.rep_mem _), wc, D.ψV_cl_rep,
        codeOf_vecOf (Two.w1List_lt _ (Two.w1Basis_getD_mem i))]
      simp only [Two.res6, List.getElem_map]
      rw [appN_rowsOf _ (Two.w1List_lt _ (by
        have := Two.w1Basis_getD_mem i
        rwa [List.getD_eq_getElem _ _ (by simpa [Two.w1Basis] using hi)] at this))]
      congr 3
      rw [List.getD_eq_getElem _ _ (by simpa [Two.w1Basis] using hi)]
  rw [← hA]
  exact Two.eq_mk7 (D.kap_size φ) h0

end Shape2

section T


@[expose] noncomputable def q0e : G := D.rep Two.q0c

theorem q0e_mem_QG : D.q0e ∈ h.setting.QG := D.rep_mem _

@[expose] noncomputable def tb : ↥D.Mb := D.toMb ⟨D.q0e, D.QG_le_N D.q0e_mem_QG⟩

@[expose] noncomputable def C3 : Subgroup ↥D.Mb := D.Mz ⊓ centralizer {D.tb}

@[expose] noncomputable def stbar : Subgroup h.setting.O :=
  (genGrp (Two.stabGens48 ())).comap D.Φo

@[expose] noncomputable def Ghat : Subgroup G := pre h.setting D.stbar

end T

section C3

variable
  (hOut : KG82HatM22Out) (hTw : KG82HatM22Twelve) (hHat : HatM22SmallModules)

include D hOut hTw in
theorem card_g13Grp : Nat.card Two.g13Grp = 34560 := by
  have h1 := D.card_g13bar hOut hTw
  rwa [g13bar, D.card_comap hOut hTw Two.g13Grp_le_nGrp] at h1

theorem Ghat_le_G13 : D.Ghat ≤ D.G13 := pre_le_pre (Subgroup.comap_mono Two.stab48_le_g13)

include hOut hTw hHat

theorem comm_tb_iff {m : G} (hm : m ∈ D.G13) :
    D.toMb ⟨m, D.G13_le_N hm⟩ * D.tb = D.tb * D.toMb ⟨m, D.G13_le_N hm⟩ ↔
      D.Φo (h.setting.ρ ⟨m, D.G13_le_M hm⟩) (vecOf Two.q0c) + vecOf Two.q0c ∈ Two.W1 := by
  have hmM := D.G13_le_M hm
  have hq := D.q0e_mem_QG
  have hcQ : m * D.q0e * m⁻¹ * D.q0e⁻¹ ∈ h.setting.QG :=
    mul_mem (h.setting.conj_mem_QG hmM hq) (inv_mem hq)
  have hcN : m * D.q0e * m⁻¹ * D.q0e⁻¹ ∈ normalizer (D.E : Set G) := D.QG_le_N hcQ
  have e1 : D.toMb ⟨m * D.q0e * m⁻¹ * D.q0e⁻¹, hcN⟩ =
      D.toMb ⟨m, D.G13_le_N hm⟩ * D.tb * (D.toMb ⟨m, D.G13_le_N hm⟩)⁻¹ * D.tb⁻¹ := by
    rw [tb, ← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
    rfl
  have hcomm : ∀ x y : ↥D.Mb, x * y = y * x ↔ x * y * x⁻¹ * y⁻¹ = 1 := fun x y => by
    constructor
    · intro hxy
      rw [hxy]
      group
    · intro hxy
      calc x * y = x * y * x⁻¹ * y⁻¹ * (y * x) := by group
        _ = y * x := by rw [hxy, one_mul]
  rw [hcomm, ← e1, D.toMb_eq_one_iff hOut hTw hHat]
  change m * D.q0e * m⁻¹ * D.q0e⁻¹ ∈ D.E ↔ _
  have hcl : D.ψV (h.setting.cl (m * D.q0e * m⁻¹ * D.q0e⁻¹)) =
      D.Φo (h.setting.ρ ⟨m, hmM⟩) (vecOf Two.q0c) + vecOf Two.q0c := by
    rw [h.setting.cl_mul (h.setting.conj_mem_QG hmM hq) (inv_mem hq), h.setting.cl_inv hq,
      ← h.setting.ρ_cl ⟨m, hmM⟩ hq, map_add, ← Φo_apply_ψV]
    rw [show D.ψV (h.setting.cl D.q0e) = vecOf Two.q0c from D.ψV_cl_rep _]
  constructor
  · intro hE
    have := D.mem_E1_of_mem_E hcQ hE
    rw [← hcl]
    exact (D.mem_E1.mp this).2
  · intro hW
    exact D.E1_le_E (D.mem_E1.mpr ⟨hcQ, by rw [hcl]; exact hW⟩)

theorem C3_eq_img : D.C3 = D.img D.Ghat := by
  ext φ
  constructor
  · rintro ⟨hφz, hφt⟩
    obtain ⟨m, hm, rfl⟩ := (D.mem_Mz_iff hOut hTw).mp hφz
    have hc := (D.comm_tb_iff hOut hTw hHat hm).mp (mem_centralizer_singleton_iff.mp hφt)
    have hU : D.Φo (h.setting.ρ ⟨m, D.G13_le_M hm⟩) ∈ Two.g13Grp := rho_mem_of_mem_pre hm _
    have hS := Two.mem_stab48 (D.card_g13Grp hOut hTw) hU hc
    exact D.toMb_mem_img _ (mem_pre_of_rho ⟨m, D.G13_le_M hm⟩ hS)
  · intro hφ
    obtain ⟨m, hmN, hmG, rfl⟩ := D.mem_img.mp hφ
    have hm : m ∈ D.G13 := D.Ghat_le_G13 hmG
    refine ⟨(D.mem_Mz_iff hOut hTw).mpr ⟨m, hm, rfl⟩, mem_centralizer_singleton_iff.mpr ?_⟩
    refine (D.comm_tb_iff hOut hTw hHat hm).mpr ?_
    have hS : D.Φo (h.setting.ρ ⟨m, D.G13_le_M hm⟩) ∈ genGrp (Two.stabGens48 ()) :=
      rho_mem_of_mem_pre hmG _
    exact (Two.image_S0_eq_iff (Two.mem_g13Grp.mp (Two.stab48_le_g13 hS)).2).mp (Two.stab48_fix hS)

theorem E_le_Ghat : D.E ≤ D.Ghat := by
  intro e he
  have hm : e ∈ D.G13 := D.E_le_G13 hOut hTw he
  have h1 : D.toMb ⟨e, D.G13_le_N hm⟩ = 1 := (D.toMb_eq_one_iff hOut hTw hHat _).mpr he
  have hc := (D.comm_tb_iff hOut hTw hHat hm).mp (by rw [h1, one_mul, mul_one])
  have hU : D.Φo (h.setting.ρ ⟨e, D.G13_le_M hm⟩) ∈ Two.g13Grp := rho_mem_of_mem_pre hm _
  exact mem_pre_of_rho ⟨e, D.G13_le_M hm⟩ (Two.mem_stab48 (D.card_g13Grp hOut hTw) hU hc)

theorem card_C3 : Nat.card D.C3 = 3072 := by
  have h1 := D.card_img hOut hTw hHat (D.Ghat_le_G13.trans D.G13_le_N) (D.E_le_Ghat hOut hTw hHat)
  have hst : Nat.card D.stbar = 768 := by
    rw [stbar, D.card_comap hOut hTw (Two.stab48_le_g13.trans Two.g13Grp_le_nGrp), Two.card_stab48]
  have hG : Nat.card D.Ghat = 768 * 2 ^ 13 := by
    rw [Ghat, card_pre (K := D.stbar)
      (show D.stbar ≤ h.setting.Mbar from
        D.comap_le_Mbar hOut hTw (Two.stab48_le_g13.trans Two.g13Grp_le_nGrp)), hst, D.card_QG]
  rw [← D.C3_eq_img hOut hTw hHat, D.card_E hOut hTw, hG] at h1
  omega

theorem kap_mem_c3List {φ : ↥D.Mb} (hφ : φ ∈ D.C3) : D.kap (φ : MulAut ↥D.E) ∈ Two.c3List () := by
  rw [D.C3_eq_img hOut hTw hHat] at hφ
  obtain ⟨m, hmN, hmG, rfl⟩ := D.mem_img.mp hφ
  have hm : m ∈ D.G13 := D.Ghat_le_G13 hmG
  have hS : D.Φo (h.setting.ρ ⟨m, D.G13_le_M hm⟩) ∈ genGrp (Two.stabGens48 ()) :=
    rho_mem_of_mem_pre hmG _
  obtain ⟨-, -, hid, hc, -⟩ := Two.stabOK48_spec
  obtain ⟨x, hx, hxU⟩ := complete hid hc _ hS
  have hrow : rowsOf (D.Φo (h.setting.ρ ⟨m, D.G13_le_M hm⟩)) = x :=
    rowsOf_eq (enumGrp_sound Two.gensOK_stab48 x hx).1 hxU
  rw [D.kap_toMb hOut hTw hm, hrow]
  refine Two.mem_c3List.mpr ⟨Two.res6 x, ?_, _, Two.lam6_lt _, rfl⟩
  simp only [Two.s48, List.mem_dedup, List.mem_map]
  exact ⟨x, hx, rfl⟩

theorem exists_of_mem_c3List {X : Array ℕ} (hX : X ∈ Two.c3List ()) :
    ∃ φ ∈ D.C3, D.kap (φ : MulAut ↥D.E) = X := by
  let f : ↥D.C3 → ↥(Two.c3List ()).toFinset := fun φ =>
    ⟨D.kap ((φ : ↥D.Mb) : MulAut ↥D.E), List.mem_toFinset.mpr (D.kap_mem_c3List hOut hTw hHat φ.2)⟩
  have hinj : Function.Injective f := by
    intro φ ψ hφψ
    have hk : D.kap ((φ : ↥D.Mb) : MulAut ↥D.E) = D.kap ((ψ : ↥D.Mb) : MulAut ↥D.E) :=
      congrArg Subtype.val hφψ
    have hφ := D.presE1_of_mem_Mz hOut hTw φ.2.1
    have hψ := D.presE1_of_mem_Mz hOut hTw ψ.2.1
    refine Subtype.ext (D.eq_of_agree_E1 hOut hTw hHat fun x hx => Subtype.ext ?_)
    exact D.crd_injective (hφ x hx) (hψ x hx) (by rw [D.crd_apply hφ hx, D.crd_apply hψ hx, hk])
  have hcard : Nat.card ↥(Two.c3List ()).toFinset ≤ Nat.card ↥D.C3 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe, List.card_toFinset, Two.c3OK48_spec.2.1,
      D.card_C3 hOut hTw hHat]
  obtain ⟨φ, hφ⟩ := (hinj.bijective_of_nat_card_le hcard).2 ⟨X, List.mem_toFinset.mpr hX⟩
  exact ⟨φ, φ.2, congrArg Subtype.val hφ⟩

end C3

end Data41

end CFSG.Quasithin.H13.AS91
