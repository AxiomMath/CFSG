module

public import CFSG.LocalAnalysis.StandardType.FF81.PropOne.AutB1
public import CFSG.LocalAnalysis.StandardType.FF81.PropOne.QSylow

@[expose] public section

namespace CFSG.StandardType.FF81.PropOne

open CFSG.RankThree.PartTwo.Sec4.Item434Kit
open scoped Pointwise commutatorElement

private theorem conj_vecElt_cyc {G : Type} [Group G] {z : Fin 3 → G} {c : G}
    (hc : ∀ i j, z i * z j = z j * z i)
    (hcyc : ∀ i, c * z i * c⁻¹ = z (finRotate 3 i)) (v : Fin 3 → ZMod 3) :
    c * vecElt z v * c⁻¹ = vecElt z ![v 2, v 0, v 1] := by
  have h0 : finRotate 3 (0 : Fin 3) = 1 := by decide
  have h1 : finRotate 3 (1 : Fin 3) = 2 := by decide
  have h2 : finRotate 3 (2 : Fin 3) = 0 := by decide
  have hc0 : c * z 0 * c⁻¹ = z 1 := by rw [hcyc 0, h0]
  have hc1 : c * z 1 * c⁻¹ = z 2 := by rw [hcyc 1, h1]
  have hc2 : c * z 2 * c⁻¹ = z 0 := by rw [hcyc 2, h2]
  have hc' : ∀ x : G, c * x * c⁻¹ = MulAut.conj c x := fun x => rfl
  rw [hc', vecElt, map_mul, map_mul, map_pow, map_pow, map_pow, ← hc', ← hc', ← hc',
    hc0, hc1, hc2, vecElt]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  have e1 : z 2 ^ (v 1).val * z 0 ^ (v 2).val = z 0 ^ (v 2).val * z 2 ^ (v 1).val :=
    (Commute.pow_pow (show Commute (z 2) (z 0) from hc 2 0) _ _).eq
  have e2 : z 1 ^ (v 0).val * z 0 ^ (v 2).val = z 0 ^ (v 2).val * z 1 ^ (v 0).val :=
    (Commute.pow_pow (show Commute (z 1) (z 0) from hc 1 0) _ _).eq
  calc z 1 ^ (v 0).val * z 2 ^ (v 1).val * z 0 ^ (v 2).val
      = z 1 ^ (v 0).val * (z 2 ^ (v 1).val * z 0 ^ (v 2).val) := by group
    _ = z 1 ^ (v 0).val * z 0 ^ (v 2).val * z 2 ^ (v 1).val := by rw [e1]; group
    _ = z 0 ^ (v 2).val * z 1 ^ (v 0).val * z 2 ^ (v 1).val := by rw [e2]

private theorem vecElt_const_eq_pow {G : Type} [Group G] {z : Fin 3 → G}
    (hc : ∀ i j, z i * z j = z j * z i) (a : ZMod 3) :
    vecElt z (fun _ => a) = (vecElt z ![1, 1, 1]) ^ a.val := by
  rw [vecElt, vecElt]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, ZMod.val_one, pow_one]
  rw [((show Commute (z 0) (z 2) from hc 0 2).mul_left
      (show Commute (z 1) (z 2) from hc 1 2)).mul_pow a.val,
    (show Commute (z 0) (z 1) from hc 0 1).mul_pow a.val]

private theorem card_cen_c_le_three {G : Type} [Group G] [Finite G] {n : ℕ} {b : G}
    {L : Subgroup G} {z : Fin 3 → ↥L} (h : Counterexample G n b L z) {c : G}
    (hcyc : ∀ i, c * GGFF.zs z i * c⁻¹ = GGFF.zs z (finRotate 3 i)) :
    Nat.card ↥(bOne z ⊓ Subgroup.centralizer ({c} : Set G)) ≤ 3 := by
  have hst := h.settingCore
  have hp := hst.zs_pow
  have hm := hst.zs_comm
  have hinj := hst.inj'
  have hle : bOne z ⊓ Subgroup.centralizer ({c} : Set G) ≤
      Subgroup.zpowers (vecElt (GGFF.zs z) ![1, 1, 1]) := by
    rintro x ⟨hx, hxc⟩
    obtain ⟨v, rfl⟩ := hst.mem_torG.mp hx
    have hfix : c * vecElt (GGFF.zs z) v * c⁻¹ = vecElt (GGFF.zs z) v := by
      have hcx : vecElt (GGFF.zs z) v * c = c * vecElt (GGFF.zs z) v :=
        Subgroup.mem_centralizer_singleton_iff.mp hxc
      rw [← hcx]; group
    rw [conj_vecElt_cyc hm hcyc v] at hfix
    have hv : ![v 2, v 0, v 1] = v := (GGFF.vecElt_injective hp hm hinj) hfix
    have h01 : v 0 = v 1 := by
      have := congrFun hv 1
      simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
        Matrix.tail_cons] using this
    have h12 : v 1 = v 2 := by
      have h02 : v 0 = v 2 := by
        have := congrFun hv 0
        simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
          Matrix.head_cons, Matrix.tail_cons] using this.symm
      exact h01.symm.trans h02
    have hvconst : v = fun _ => v 0 := by
      funext i; fin_cases i <;> simp [h01, h12]
    rw [hvconst, vecElt_const_eq_pow hm (v 0)]
    exact Subgroup.mem_zpowers_iff.mpr ⟨(v 0).val, by rw [zpow_natCast]⟩
  have hcard := Subgroup.card_le_of_le hle
  rw [Nat.card_zpowers] at hcard
  have he3 : (vecElt (GGFF.zs z) ![1, 1, 1]) ^ 3 = 1 :=
    (GGFF.isElemAbelian_tor hp hm).2 _ (GGFF.vecElt_mem_tor _ _)
  exact hcard.trans (Nat.le_of_dvd (by norm_num) (orderOf_dvd_iff_pow_eq_one.mpr he3))

private theorem commutator_sup_le_of_comm {G : Type} [Group G] {A Q : Subgroup G}
    (hQA : Q ≤ Subgroup.normalizer (A : Set G)) (hQcomm : IsMulCommutative Q) :
    ⁅A ⊔ Q, A ⊔ Q⁆ ≤ A := by
  let S : Subgroup G := A ⊔ Q
  have hA_le_S : A ≤ S := le_sup_left
  have hS_norA : S ≤ Subgroup.normalizer (A : Set G) :=
    sup_le Subgroup.le_normalizer hQA
  let A' : Subgroup ↥S := A.subgroupOf S
  let Q' : Subgroup ↥S := Q.subgroupOf S
  haveI : IsMulCommutative Q := hQcomm
  have hA'norm : A'.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hA_le_S).mpr hS_norA
  haveI : A'.Normal := hA'norm
  have hA'supQ' : A' ⊔ Q' = ⊤ := by
    have h := Subgroup.subgroupOf_sup (A := A) (A' := Q) (B := S) le_sup_left le_sup_right
    rw [show A ⊔ Q = S from rfl, Subgroup.subgroupOf_self] at h
    exact h.symm
  have hcomm : _root_.commutator ↥S ≤ A' :=
    Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top hA'supQ' inferInstance
  have h1 : (_root_.commutator ↥S).map S.subtype ≤ A'.map S.subtype :=
    Subgroup.map_mono hcomm
  rw [Subgroup.map_subtype_commutator S, Subgroup.map_subgroupOf_eq_of_le hA_le_S] at h1
  simpa only [S] using h1

private theorem conj_mem_normalizer {G : Type} [Group G] {A : Subgroup G} {g x : G}
    (hg : g ∈ Subgroup.normalizer (A : Set G)) (hx : x ∈ Subgroup.normalizer (A : Set G)) :
    g * x * g⁻¹ ∈ Subgroup.normalizer (A : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hg hx ⊢
  intro y
  constructor
  · intro hy
    have h1 : g⁻¹ * y * g ∈ A := (hg (g⁻¹ * y * g)).mpr (by convert hy using 1; group)
    have h2 : x * (g⁻¹ * y * g) * x⁻¹ ∈ A := (hx (g⁻¹ * y * g)).mp h1
    have h3 : g * (x * (g⁻¹ * y * g) * x⁻¹) * g⁻¹ ∈ A := (hg _).mp h2
    convert h3 using 1; group
  · intro hy
    have h3 : g * (x * (g⁻¹ * y * g) * x⁻¹) * g⁻¹ ∈ A := by convert hy using 1; group
    have h2 : x * (g⁻¹ * y * g) * x⁻¹ ∈ A := (hg (x * (g⁻¹ * y * g) * x⁻¹)).mpr h3
    have h1 : g⁻¹ * y * g ∈ A := (hx _).mpr h2
    have h0 : g * (g⁻¹ * y * g) * g⁻¹ ∈ A := (hg _).mp h1
    convert h0 using 1; group

private theorem conj_max {G : Type} [Group G] {S : Subgroup G} (m : G)
    (hmax : ∀ P : Subgroup G, IsPGroup 3 P → S ≤ P → P = S) :
    ∀ P : Subgroup G, IsPGroup 3 P → S.map (MulAut.conj m).toMonoidHom ≤ P →
      P = S.map (MulAut.conj m).toMonoidHom := by
  intro P hP hle
  have hcomp : (MulAut.conj m⁻¹).toMonoidHom.comp (MulAut.conj m).toMonoidHom = MonoidHom.id G := by
    ext x
    simp only [MonoidHom.comp_apply, MonoidHom.id_apply, MulEquiv.toMonoidHom_eq_coe,
      MonoidHom.coe_coe, MulAut.conj_apply]
    group
  have hle' : S ≤ P.map (MulAut.conj m⁻¹).toMonoidHom := by
    have h1 : (S.map (MulAut.conj m).toMonoidHom).map (MulAut.conj m⁻¹).toMonoidHom ≤
        P.map (MulAut.conj m⁻¹).toMonoidHom := Subgroup.map_mono hle
    rwa [Subgroup.map_map, hcomp, Subgroup.map_id] at h1
  have hEq : P.map (MulAut.conj m⁻¹).toMonoidHom = S := hmax _ (hP.map _) hle'
  have h2 : (P.map (MulAut.conj m⁻¹).toMonoidHom).map (MulAut.conj m).toMonoidHom =
      S.map (MulAut.conj m).toMonoidHom := congrArg _ hEq
  rw [Subgroup.map_map, show (MulAut.conj m).toMonoidHom.comp (MulAut.conj m⁻¹).toMonoidHom =
      MonoidHom.id G from by
    ext x
    simp only [MonoidHom.comp_apply, MonoidHom.id_apply, MulEquiv.toMonoidHom_eq_coe,
      MonoidHom.coe_coe, MulAut.conj_apply]
    group,
    Subgroup.map_id] at h2
  exact h2

private theorem centralizer_map_of_bijective {G H : Type} [Group G] [Group H]
    (f : G ≃* H) (S : Subgroup G) :
    Subgroup.centralizer ((S.map f.toMonoidHom : Subgroup H) : Set H) =
      (Subgroup.centralizer (S : Set G)).map f.toMonoidHom := by
  ext x
  constructor
  · intro hx
    rw [Subgroup.mem_map]
    refine ⟨f.symm x, ?_, by simp⟩
    rw [Subgroup.mem_centralizer_iff] at hx ⊢
    intro s hs
    have h := hx (f s) (Subgroup.mem_map_of_mem f.toMonoidHom hs)
    simpa using congrArg f.symm h
  · intro hx
    rw [Subgroup.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    rw [Subgroup.mem_centralizer_iff] at hy ⊢
    intro z hz
    have hz'' : z ∈ Subgroup.map f.toMonoidHom S := hz
    rw [Subgroup.mem_map] at hz''
    obtain ⟨s, hs, rfl⟩ := hz''
    simpa using congrArg f (hy s hs)

private theorem mem_normalizer_centralizer {G : Type} [Group G] {B : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (B : Set G)) :
    g ∈ Subgroup.normalizer (Subgroup.centralizer (B : Set G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hg ⊢
  intro x
  constructor
  · intro hx
    rw [Subgroup.mem_centralizer_iff] at hx ⊢
    intro b hb
    have hb' : g⁻¹ * b * g ∈ B := by
      apply (hg (g⁻¹ * b * g)).mpr
      rw [show g * (g⁻¹ * b * g) * g⁻¹ = b by group]
      exact hb
    have h := hx (g⁻¹ * b * g) hb'
    calc b * (g * x * g⁻¹) = g * ((g⁻¹ * b * g) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * b * g)) * g⁻¹ := by rw [h]
      _ = (g * x * g⁻¹) * b := by group
  · intro hx
    rw [Subgroup.mem_centralizer_iff] at hx ⊢
    intro b hb
    have hb' : g * b * g⁻¹ ∈ B := (hg b).mp hb
    have h := hx (g * b * g⁻¹) hb'
    have h' : g * (b * x) * g⁻¹ = g * (x * b) * g⁻¹ := by
      calc g * (b * x) * g⁻¹ = (g * b * g⁻¹) * (g * x * g⁻¹) := by group
        _ = (g * x * g⁻¹) * (g * b * g⁻¹) := h
        _ = g * (x * b) * g⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel h')

private theorem zpow_eq_pow_toNat_emod_orderOf {G : Type} [Group G] (x : G)
    (hfin : orderOf x ≠ 0) (j : ℤ) :
    x ^ j = x ^ ((j % (orderOf x : ℤ)).toNat) := by
  have hnat : ((j % (orderOf x : ℤ)).toNat : ℤ) = j % (orderOf x : ℤ) :=
    Int.toNat_of_nonneg (Int.emod_nonneg j (by exact_mod_cast hfin))
  calc x ^ j = x ^ (j % (orderOf x : ℤ)) := (zpow_mod_orderOf x j).symm
    _ = x ^ (((j % (orderOf x : ℤ)).toNat : ℤ)) := by rw [hnat]
    _ = x ^ ((j % (orderOf x : ℤ)).toNat) := zpow_natCast _ _

theorem not_conj_z0 {G : Type} [Group G] [Finite G] {n : ℕ} {b : G} {L : Subgroup G}
    {z : Fin 3 → ↥L} (h : Counterexample G n b L z) {B₂ A : Subgroup G} {τ c : G}
    (hB₂ : B2Package b z B₂) (hA : AStar b z B₂ A) (hτc : TauC z τ c)
    (hS : SylowData b B₂ A c) :
    ¬ ∃ m ∈ Subgroup.normalizer (B₂ : Set G), ∃ k : ℕ,
      m * (GGFF.zs z 0 * GGFF.zs z 1 * GGFF.zs z 2) ^ k * m⁻¹ = GGFF.zs z 0 := by
  rintro ⟨m, hmN, k, hmk⟩
  have hst := h.settingCore
  have hp := hst.zs_pow
  have hcomm := hst.zs_comm
  have hinj := hst.inj'
  let Q : Subgroup G := Subgroup.zpowers b ⊔ Subgroup.zpowers c
  let S : Subgroup G := A ⊔ Q
  let z0 : G := GGFF.zs z 0
  let e : G := GGFF.zs z 0 * GGFF.zs z 1 * GGFF.zs z 2
  have hmk' : m * e ^ k * m⁻¹ = z0 := hmk
  let N₂ : Subgroup G := Subgroup.normalizer (B₂ : Set G)
  let C₂ : Subgroup G := Subgroup.centralizer (B₂ : Set G)
  let H : Subgroup G := N₂ ⊓ Subgroup.centralizer ({z0} : Set G)
  have hc_nor_bOne : c ∈ Subgroup.normalizer ((bOne z : Subgroup G) : Set G) := by
    rw [show (bOne z : Subgroup G) =
        Subgroup.closure ({GGFF.zs z 0, GGFF.zs z 1, GGFF.zs z 2} : Set G) from
      CFSG.StandardType.GGFF.SettingCore.tor_eq_closure z]
    refine CFSG.StandardType.GGFF.mem_nor_of_closure
      (S := ({GGFF.zs z 0, GGFF.zs z 1, GGFF.zs z 2} : Set G)) ?_
    rintro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl | rfl
    · rw [hτc.cyc₀]; exact Subgroup.subset_closure (by simp)
    · rw [hτc.cyc₁]; exact Subgroup.subset_closure (by simp)
    · rw [hτc.cyc₂]; exact Subgroup.subset_closure (by simp)
  have hc_dGrp : c ∈ dGrp b z :=
    Subgroup.mem_sup_right (Subgroup.mem_inf.mpr ⟨hτc.c_mem, hc_nor_bOne⟩)
  have hb_dGrp : b ∈ dGrp b z := Subgroup.mem_sup_left (Subgroup.mem_zpowers b)
  have hQd : Q ≤ dGrp b z :=
    sup_le (Subgroup.zpowers_le.mpr hb_dGrp) (Subgroup.zpowers_le.mpr hc_dGrp)
  have hQA : Q ≤ Subgroup.normalizer (A : Set G) := by
    intro q hq
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx; exact hA.nor q (hQd hq) x hx
    · intro hx
      have h := hA.nor q⁻¹ (hQd (Q.inv_mem hq)) (q * x * q⁻¹) hx
      rwa [show q⁻¹ * (q * x * q⁻¹) * (q⁻¹)⁻¹ = x by group] at h
  have hbc : Commute b c :=
    (Subgroup.mem_centralizer_singleton_iff.mp (h.hypA.le hτc.c_mem)).symm
  have hQab : CFSG.Open.IsElemAbelian 3 Q := by
    have hb3 : b ^ 3 = 1 := by rw [← h.hypA.ord]; exact pow_orderOf_eq_one b
    exact CFSG.Open.IsElemAbelian.sup_of_commute
      (CFSG.Open.isElemAbelian_zpowers hb3)
      (CFSG.Open.isElemAbelian_zpowers hτc.c_cube)
      (fun x hx y hy => by
        obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
        obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
        exact (Commute.zpow_zpow hbc i j).eq)
  have hcommut : ⁅S, S⁆ ≤ A := commutator_sup_le_of_comm hQA hQab.1
  have hzsL : ∀ i : Fin 3, GGFF.zs z i ∈ L :=
    fun i => GGFF.SettingCore.tor_le z (Subgroup.subset_closure ⟨i, rfl⟩)
  have hb_comm_zs : ∀ i : Fin 3, Commute b (GGFF.zs z i) :=
    fun i => (Subgroup.mem_centralizer_singleton_iff.mp (h.hypA.le (hzsL i))).symm
  have hzA : ∀ i : Fin 3, GGFF.zs z i ∈ A :=
    fun i => hA.B₂_le (hB₂.B₁_le (Subgroup.subset_closure ⟨i, rfl⟩))
  have heA : e ∈ A := A.mul_mem (A.mul_mem (hzA 0) (hzA 1)) (hzA 2)
  have hfr : ∀ i : Fin 3, finRotate 3 i = ![1, 2, 0] i := by decide
  have hcyc : ∀ i : Fin 3, c * GGFF.zs z i * c⁻¹ = GGFF.zs z (finRotate 3 i) := by
    intro i
    fin_cases i <;> simp [hfr, hτc.cyc₀, hτc.cyc₁, hτc.cyc₂]
  have he_eq : e = vecElt (GGFF.zs z) ![1, 1, 1] := by simp [e, vecElt, ZMod.val_one]
  have hc_e : c * e * c⁻¹ = e := by
    rw [he_eq, conj_vecElt_cyc hcomm hcyc]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons]
  have hce : c * e = e * c := by
    calc c * e = c * e * c⁻¹ * c := by group
      _ = e * c := by rw [hc_e]
  have heCen : S ≤ Subgroup.centralizer ({e} : Set G) := by
    refine sup_le ?_ ?_
    · intro a ha
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (hA.comm e heA a ha).symm
    · refine sup_le ?_ ?_
      · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
        exact (((hb_comm_zs 0).mul_right (hb_comm_zs 1)).mul_right (hb_comm_zs 2)).eq
      · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
        exact hce
  have hAN₂ : A ≤ N₂ := hA.le_cen.trans (Subgroup.centralizer_le_normalizer (B₂ : Set G))
  have hbN₂ : b ∈ N₂ := Subgroup.mem_normalizer_fintype (fun x hx => hB₂.b_nor x hx)
  have hcN₂ : c ∈ N₂ := Subgroup.mem_normalizer_fintype
    (fun x hx => hB₂.D_nor c (Subgroup.mem_inf.mpr ⟨hτc.c_mem, hc_nor_bOne⟩) x hx)
  have hQN₂ : Q ≤ N₂ :=
    sup_le (Subgroup.zpowers_le.mpr hbN₂) (Subgroup.zpowers_le.mpr hcN₂)
  have hS_N₂ : S ≤ N₂ := sup_le hAN₂ hQN₂
  let S' : Subgroup G := S.map (MulAut.conj m).toMonoidHom
  have hS'_isP : IsPGroup 3 S' := hS.isP.map (MulAut.conj m).toMonoidHom
  have hS'_N₂ : S' ≤ N₂ := by
    intro d hd
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hd
    exact conj_mem_normalizer hmN (hS_N₂ hx)
  have hS'_cen : S' ≤ Subgroup.centralizer ({z0} : Set G) := by
    intro d hd
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hd
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hxcomm : x * e ^ k = e ^ k * x :=
      ((show Commute x e from
        Subgroup.mem_centralizer_singleton_iff.mp (heCen hx)).pow_right k).eq
    simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply]
    rw [← hmk']
    calc m * x * m⁻¹ * (m * e ^ k * m⁻¹) = m * (x * e ^ k) * m⁻¹ := by group
      _ = m * (e ^ k * x) * m⁻¹ := by rw [hxcomm]
      _ = (m * e ^ k * m⁻¹) * (m * x * m⁻¹) := by group
  have hS'_H : S' ≤ H := le_inf hS'_N₂ hS'_cen
  have hS'_max_G : ∀ R : Subgroup G, IsPGroup 3 R → S' ≤ R → R = S' :=
    conj_max (S := S) m (fun P hP hle => hS.max P hP hle)
  have hbH : b ∈ H := by
    refine Subgroup.mem_inf.mpr ⟨hbN₂, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_singleton_iff.mp
      (h.hypA.le (hzsL 0))).symm
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  haveI : Finite (Sylow 3 G) := Sylow.finite_of_finiteIndex (default : Sylow 3 G)
  have hbH_le : Subgroup.zpowers b ≤ H := Subgroup.zpowers_le.mpr hbH
  let Bp : Subgroup ↥H := (Subgroup.zpowers b).subgroupOf H
  have hbp3 : IsPGroup 3 (Subgroup.zpowers b : Subgroup G) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h.hypA.ord]; norm_num)
  have hBp3 : IsPGroup 3 Bp := hbp3.of_equiv (Subgroup.subgroupOfEquivOfLe hbH_le).symm
  obtain ⟨P, hbP⟩ := hBp3.exists_le_sylow
  let P₁ : Subgroup G := (P : Subgroup ↥H).map H.subtype
  have hbBp : (⟨b, hbH⟩ : ↥H) ∈ Bp := Subgroup.mem_subgroupOf.mpr (Subgroup.mem_zpowers b)
  have hbP₁ : b ∈ P₁ := Subgroup.mem_map.mpr ⟨⟨b, hbH⟩, hbP hbBp, rfl⟩
  have hP₁3 : IsPGroup 3 P₁ := P.isPGroup'.map H.subtype
  have hP₁_H : P₁ ≤ H := Subgroup.map_subtype_le _
  let Ssyl : Sylow 3 ↥H :=
    { toSubgroup := S'.subgroupOf H
      isPGroup' := hS'_isP.of_equiv (Subgroup.subgroupOfEquivOfLe hS'_H).symm
      is_maximal' := by
        intro Q hQ hle
        have hmaple : S' ≤ Q.map H.subtype := by
          rw [← Subgroup.map_subgroupOf_eq_of_le hS'_H]
          exact Subgroup.map_mono hle
        have hmap : Q.map H.subtype = S' :=
          hS'_max_G (Q.map H.subtype) (hQ.map H.subtype) hmaple
        calc Q = (Q.map H.subtype).comap H.subtype :=
              (Subgroup.comap_map_eq_self_of_injective H.subtype_injective Q).symm
          _ = S'.comap H.subtype := by rw [hmap]
          _ = S'.subgroupOf H := rfl }
  obtain ⟨u, hu⟩ :=
    (inferInstance : MulAction.IsPretransitive ↥H (Sylow 3 ↥H)).exists_smul_eq Ssyl P
  let u' : G := (u : G) * m
  have huN₂ : (u : G) ∈ N₂ := (Subgroup.mem_inf.mp u.2).1
  have hu'N₂ : u' ∈ N₂ := N₂.mul_mem huN₂ hmN
  have hPsub : (P : Subgroup ↥H) = (Ssyl : Subgroup ↥H).map (MulAut.conj u).toMonoidHom := by
    rw [← hu, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    rfl
  have hcomp2 : H.subtype.comp (MulAut.conj u).toMonoidHom =
      (MulAut.conj (u : G)).toMonoidHom.comp H.subtype := by
    ext x
    simp only [MonoidHom.comp_apply, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe,
      MulAut.conj_apply]
    rfl
  have hP₁_eq : P₁ = S.map (MulAut.conj u').toMonoidHom := by
    calc P₁ = ((S'.subgroupOf H).map (MulAut.conj u).toMonoidHom).map H.subtype := by
          rw [show P₁ = (P : Subgroup ↥H).map H.subtype from rfl, hPsub]
      _ = (S'.subgroupOf H).map (H.subtype.comp (MulAut.conj u).toMonoidHom) := by
          rw [Subgroup.map_map]
      _ = (S'.subgroupOf H).map ((MulAut.conj (u : G)).toMonoidHom.comp H.subtype) := by
          rw [hcomp2]
      _ = ((S'.subgroupOf H).map H.subtype).map (MulAut.conj (u : G)).toMonoidHom := by
          rw [← Subgroup.map_map]
      _ = S'.map (MulAut.conj (u : G)).toMonoidHom := by
          rw [Subgroup.map_subgroupOf_eq_of_le hS'_H]
      _ = S.map (MulAut.conj u').toMonoidHom := by
          rw [show S' = S.map (MulAut.conj m).toMonoidHom from rfl, Subgroup.map_map]
          apply congrArg (fun f => S.map f)
          ext y
          simp only [MonoidHom.comp_apply, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe,
            MulAut.conj_apply]
          rw [show u' = (u : G) * m from rfl]
          group
  have hrepr : ∀ d ∈ P₁, ∃ y ∈ S, d = u' * y * u'⁻¹ := by
    intro d hd
    rw [hP₁_eq] at hd
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hd
    exact ⟨y, hy, by
      simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply]⟩
  have hb_repr : ∃ yb ∈ S, b = u' * yb * u'⁻¹ := hrepr b hbP₁
  have hP₁_nor : P₁ ≤ Subgroup.normalizer ((bOne z : Subgroup G) : Set G) := by
    intro d hd
    obtain ⟨y, hy, hdy⟩ := hrepr d hd
    rw [hdy]
    let dG : G := u' * y * u'⁻¹
    change dG ∈ Subgroup.normalizer ((bOne z : Subgroup G) : Set G)
    have hdG_N₂ : dG ∈ N₂ := N₂.mul_mem (N₂.mul_mem hu'N₂ (hS_N₂ hy)) (N₂.inv_mem hu'N₂)
    obtain ⟨yb, hyb, hbeq⟩ := hb_repr
    have hwC₂ : dG * b * dG⁻¹ * b⁻¹ ∈ C₂ := by
      have hw_eq : dG * b * dG⁻¹ * b⁻¹ = u' * (y * yb * y⁻¹ * yb⁻¹) * u'⁻¹ := by
        dsimp only [dG]; rw [hbeq]; group
      have hcommA : y * yb * y⁻¹ * yb⁻¹ ∈ A := by
        have hmem := hcommut (Subgroup.commutator_mem_commutator hy hyb)
        simpa only [commutatorElement_def] using hmem
      have hcommC₂ : y * yb * y⁻¹ * yb⁻¹ ∈ C₂ := hA.le_cen hcommA
      have hu'C₂ : u' ∈ Subgroup.normalizer (C₂ : Set G) := mem_normalizer_centralizer hu'N₂
      rw [hw_eq]
      exact (Subgroup.mem_normalizer_iff.mp hu'C₂
        (y * yb * y⁻¹ * yb⁻¹)).mp hcommC₂
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    apply Subgroup.eq_of_le_of_card_ge _ (by
      rw [Subgroup.card_map_of_injective (MulAut.conj dG).injective])
    intro x hx
    obtain ⟨y0, hy0, rfl⟩ := Subgroup.mem_map.mp hx
    simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply]
    have hzB₂ : dG * y0 * dG⁻¹ ∈ B₂ :=
      (Subgroup.mem_normalizer_iff.mp hdG_N₂ y0).mp (hB₂.B₁_le hy0)
    apply hB₂.fix _ hzB₂
    have hwcomm : (dG * y0 * dG⁻¹) * (dG * b * dG⁻¹ * b⁻¹) =
        (dG * b * dG⁻¹ * b⁻¹) * (dG * y0 * dG⁻¹) :=
      Subgroup.mem_centralizer_iff.mp hwC₂ _ hzB₂
    have hdb : (dG * b * dG⁻¹ * b⁻¹) * b = dG * b * dG⁻¹ := by
      rw [mul_assoc, inv_mul_cancel, mul_one]
    have hconj : (dG * y0 * dG⁻¹) * (dG * b * dG⁻¹) =
        (dG * b * dG⁻¹) * (dG * y0 * dG⁻¹) := by
      calc (dG * y0 * dG⁻¹) * (dG * b * dG⁻¹) = dG * (y0 * b) * dG⁻¹ := by group
        _ = dG * (b * y0) * dG⁻¹ := by
              rw [show y0 * b = b * y0 from
                Subgroup.mem_centralizer_singleton_iff.mp
                  (h.hypA.le (GGFF.SettingCore.tor_le z hy0))]
        _ = (dG * b * dG⁻¹) * (dG * y0 * dG⁻¹) := by group
    have h1 : (dG * b * dG⁻¹ * b⁻¹) * ((dG * y0 * dG⁻¹) * b) =
        (dG * b * dG⁻¹ * b⁻¹) * (b * (dG * y0 * dG⁻¹)) := by
      calc (dG * b * dG⁻¹ * b⁻¹) * ((dG * y0 * dG⁻¹) * b)
          = ((dG * b * dG⁻¹ * b⁻¹) * (dG * y0 * dG⁻¹)) * b := by group
        _ = ((dG * y0 * dG⁻¹) * (dG * b * dG⁻¹ * b⁻¹)) * b := by rw [← hwcomm]
        _ = (dG * y0 * dG⁻¹) * ((dG * b * dG⁻¹ * b⁻¹) * b) := by group
        _ = (dG * y0 * dG⁻¹) * (dG * b * dG⁻¹) := by rw [hdb]
        _ = (dG * b * dG⁻¹) * (dG * y0 * dG⁻¹) := hconj
        _ = ((dG * b * dG⁻¹ * b⁻¹) * b) * (dG * y0 * dG⁻¹) := by rw [hdb]
        _ = (dG * b * dG⁻¹ * b⁻¹) * (b * (dG * y0 * dG⁻¹)) := by group
    exact mul_left_cancel h1
  have hA_cenB₁ : A ≤ Subgroup.centralizer ((bOne z : Subgroup G) : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro y0 hy0
    exact hA.comm y0 (hA.B₂_le (hB₂.B₁_le hy0)) a ha
  have hb_cenB₁ : b ∈ Subgroup.centralizer ((bOne z : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y0 hy0
    exact Subgroup.mem_centralizer_singleton_iff.mp
      (h.hypA.le (GGFF.SettingCore.tor_le z hy0))
  have hSN : S ≤ Subgroup.normalizer ((bOne z : Subgroup G) : Set G) :=
    sup_le (hA_cenB₁.trans (Subgroup.centralizer_le_normalizer _))
      (sup_le (Subgroup.zpowers_le.mpr
          (Subgroup.centralizer_le_normalizer _ hb_cenB₁))
        (Subgroup.zpowers_le.mpr hc_nor_bOne))
  have hcS : c ∈ S := Subgroup.mem_sup_right (Subgroup.mem_sup_right (Subgroup.mem_zpowers c))
  have hc_nor_zb : Subgroup.zpowers c ≤ Subgroup.normalizer (Subgroup.zpowers b : Set G) := by
    refine (Subgroup.zpowers_le.mpr ?_).trans (Subgroup.centralizer_le_normalizer _)
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact (Commute.zpow_left hbc i).eq
  have hQ_eq : (↑Q : Set G) = (Subgroup.zpowers b : Set G) * (Subgroup.zpowers c : Set G) := by
    simpa only [Q] using Subgroup.coe_mul_of_right_le_normalizer_left
      (Subgroup.zpowers b) (Subgroup.zpowers c) hc_nor_zb
  have hS_eq : (↑S : Set G) = (A : Set G) * (Q : Set G) := by
    simpa only [S] using Subgroup.coe_mul_of_right_le_normalizer_left A Q hQA
  have hQmul : ∀ q ∈ Q, ∃ i j : ℤ, b ^ i * c ^ j = q := by
    intro q hq
    have hq' : q ∈ (Subgroup.zpowers b : Set G) * (Subgroup.zpowers c : Set G) := by
      change q ∈ (↑Q : Set G) at hq
      rwa [hQ_eq] at hq
    obtain ⟨p, hp, r, hr, hpr⟩ := Set.mem_mul.mp hq'
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hp
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hr
    exact ⟨i, j, hpr⟩
  have hcyc_order : orderOf c ∣ 3 := orderOf_dvd_of_pow_eq_one hτc.c_cube
  have hcfin : orderOf c ≠ 0 := (Nat.pos_of_dvd_of_pos hcyc_order (by norm_num)).ne'
  have hSg : ∀ x ∈ S, ∃ kk : ℕ, ∀ y ∈ bOne z,
      x * y * x⁻¹ = c ^ kk * y * (c ^ kk)⁻¹ := by
    intro x hx
    have hx' : x ∈ (A : Set G) * (Q : Set G) := by
      change x ∈ (↑S : Set G) at hx
      rwa [hS_eq] at hx
    obtain ⟨a, ha, q, hq, haq⟩ := Set.mem_mul.mp hx'
    obtain ⟨i, j, hij⟩ := hQmul q hq
    refine ⟨(j % (orderOf c : ℤ)).toNat, fun y hy => ?_⟩
    rw [← haq, ← hij]
    have ha_y : a * y = y * a :=
      (Subgroup.mem_centralizer_iff.mp (hA_cenB₁ ha) y hy).symm
    have hbi_y : b ^ i * y = y * b ^ i :=
      (Subgroup.mem_centralizer_iff.mp
        ((Subgroup.centralizer ((bOne z : Subgroup G) : Set G)).zpow_mem hb_cenB₁ i) y hy).symm
    let zc : G := c ^ j * y * (c ^ j)⁻¹
    have hzc_mem : zc ∈ bOne z := by
      dsimp only [zc]
      exact (Subgroup.mem_normalizer_iff.mp
        ((Subgroup.normalizer ((bOne z : Subgroup G) : Set G)).zpow_mem hc_nor_bOne j) y).mp hy
    have hbi_zc : b ^ i * zc * (b ^ i)⁻¹ = zc := by
      have hcomm : zc * b ^ i = b ^ i * zc :=
        Subgroup.mem_centralizer_iff.mp
          ((Subgroup.centralizer ((bOne z : Subgroup G) : Set G)).zpow_mem hb_cenB₁ i) zc hzc_mem
      rw [← hcomm, mul_inv_cancel_right]
    have ha_zc : a * zc * a⁻¹ = zc := by
      have hcomm : zc * a = a * zc :=
        Subgroup.mem_centralizer_iff.mp (hA_cenB₁ ha) zc hzc_mem
      rw [← hcomm, mul_inv_cancel_right]
    calc (a * (b ^ i * c ^ j)) * y * (a * (b ^ i * c ^ j))⁻¹
        = a * (b ^ i * zc * (b ^ i)⁻¹) * a⁻¹ := by dsimp only [zc]; group
      _ = a * zc * a⁻¹ := by rw [hbi_zc]
      _ = zc := by rw [ha_zc]
      _ = c ^ ((j % (orderOf c : ℤ)).toNat) * y * (c ^ ((j % (orderOf c : ℤ)).toNat))⁻¹ := by
            dsimp only [zc]
            rw [zpow_eq_pow_toNat_emod_orderOf c hcfin j]
  have hdz : ∀ d ∈ P₁, d * z0 = z0 * d := by
    intro d hd
    exact Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp (hP₁_H hd)).2
  have hP₁_cen : ∀ d ∈ P₁, ∀ y ∈ bOne z, d * y * d⁻¹ = y := by
    intro d hd
    exact centralizes_bOne_of_fixes_z0 h hS.isP hS.max hSN hcS hSg
      (hP₁_nor hd) (hP₁3.to_le (Subgroup.zpowers_le.mpr hd)) (hdz d hd)
  have hB₁_le : bOne z ≤ Subgroup.centralizer (P₁ : Set G) ⊓ B₂ := by
    intro y hy
    refine Subgroup.mem_inf.mpr ⟨?_, hB₂.B₁_le hy⟩
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    calc d * y = d * y * d⁻¹ * d := by group
      _ = y * d := by rw [hP₁_cen d hd y hy]
  have hcard_ge : 27 ≤ Nat.card ↥(Subgroup.centralizer (P₁ : Set G) ⊓ B₂) := by
    calc 27 = Nat.card (bOne z) := hst.card_torG.symm
      _ ≤ Nat.card ↥(Subgroup.centralizer (P₁ : Set G) ⊓ B₂) := Subgroup.card_le_of_le hB₁_le
  have hC_eq : Subgroup.centralizer (P₁ : Set G) =
      (Subgroup.centralizer (S : Set G)).map (MulAut.conj u').toMonoidHom := by
    rw [hP₁_eq]
    exact centralizer_map_of_bijective (MulAut.conj u') S
  have hB₂map : B₂.map (MulAut.conj u').toMonoidHom = B₂ :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hu'N₂
  have hcard_eq : Nat.card ↥(Subgroup.centralizer (P₁ : Set G) ⊓ B₂) =
      Nat.card ↥(Subgroup.centralizer (S : Set G) ⊓ B₂) := by
    have h1 : Subgroup.centralizer (P₁ : Set G) ⊓ B₂ =
        (Subgroup.centralizer (S : Set G) ⊓ B₂).map (MulAut.conj u').toMonoidHom := by
      calc Subgroup.centralizer (P₁ : Set G) ⊓ B₂
          = (Subgroup.centralizer (S : Set G)).map (MulAut.conj u').toMonoidHom ⊓ B₂ := by
              rw [hC_eq]
        _ = (Subgroup.centralizer (S : Set G)).map (MulAut.conj u').toMonoidHom ⊓
              B₂.map (MulAut.conj u').toMonoidHom := by
              conv_lhs => rw [← hB₂map]
        _ = (Subgroup.centralizer (S : Set G) ⊓ B₂).map (MulAut.conj u').toMonoidHom := by
              rw [Subgroup.map_inf (Subgroup.centralizer (S : Set G)) B₂
                (MulAut.conj u').toMonoidHom (MulAut.conj u').injective]
    rw [h1, Subgroup.card_map_of_injective (MulAut.conj u').injective]
  have hCS_le : Subgroup.centralizer (S : Set G) ⊓ B₂ ≤
      bOne z ⊓ Subgroup.centralizer ({c} : Set G) := by
    intro x hx
    obtain ⟨hxC, hxB⟩ := Subgroup.mem_inf.mp hx
    have hxb : x * b = b * x :=
      (Subgroup.mem_centralizer_iff.mp hxC b
        (Subgroup.mem_sup_right (Subgroup.mem_sup_left (Subgroup.mem_zpowers b)))).symm
    have hxc : x * c = c * x :=
      (Subgroup.mem_centralizer_iff.mp hxC c
        (Subgroup.mem_sup_right (Subgroup.mem_sup_right (Subgroup.mem_zpowers c)))).symm
    exact Subgroup.mem_inf.mpr ⟨hB₂.fix x hxB hxb,
      Subgroup.mem_centralizer_singleton_iff.mpr hxc⟩
  have hcard_le : Nat.card ↥(Subgroup.centralizer (S : Set G) ⊓ B₂) ≤ 3 :=
    (Subgroup.card_le_of_le hCS_le).trans (card_cen_c_le_three h hcyc)
  omega

end CFSG.StandardType.FF81.PropOne

end
