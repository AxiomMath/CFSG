module

public import CFSG.Quasithin.H13.A5Sit15a
public import CFSG.Quasithin.H13.A5S1515b
public import CFSG.Quasithin.H13.A5SitY

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.H13.A5.Orth
open CFSG.Quasithin.H13.A5 (comm_of_conj_eq_inv_sq conj_eq_sq_of_conj_eq_inv pairSub mem_pairSub
  perm3_mul_of_ne perm3_exists_ne perm3_conj_ne)

namespace A5Sit

variable {G : Type} [Group G] [Finite G] {T V V₁ V₃ L₁ H : Subgroup G}
  (S : A5Sit G T V V₁ V₃ L₁ H)
include S

theorem mem_Q_iff {x : G} (hx : x ∈ H) :
    x ∈ pCoreOf 2 H ↔ ∀ u ∈ conjClosure V₃ H, x * u * x⁻¹ * u⁻¹ ∈ V₁ := by
  rw [S.hF.F92_3.1, mem_centralizerMod]
  exact ⟨fun h => h.2.2, fun h => ⟨hx, S.hF.H_normalizes_V₁ hx, h⟩⟩

theorem Q_le_NV : pCoreOf 2 H ≤ Subgroup.normalizer (V : Set G) := by
  intro q hq
  have h3 := S.hF.F92_3
  rw [h3.1] at hq
  exact (h3.2.2 (h3.2.1 hq)).2

end A5Sit

namespace A5SitY

variable {G : Type} [Group G] [Finite G] {T V V₁ V₃ L₁ H : Subgroup G}
  {S : A5Sit G T V V₁ V₃ L₁ H} {Y : Subgroup G} (SY : A5SitY S Y)

theorem c_mem_H : SY.c ∈ H := SY.Y_le_H SY.c_mem

end A5SitY

structure A5SitPf15 {G : Type} [Group G] [Finite G] {T V V₁ V₃ L₁ H : Subgroup G}
    (S : A5Sit G T V V₁ V₃ L₁ H) (SY : A5SitY S L₁) where
  hn : H ≤ Subgroup.normalizer (L₁ : Set G)
  U_eq : conjClosure V₃ H = pCoreOf 2 L₁
  hUQ8 : IsQ8Sq ↥(conjClosure V₃ H)
  g : G
  g_mem : g ∈ H
  hQ8 : IsQ8Sq ↥(V₃ ⊔ conjSub g⁻¹ V₃)
  hS3 : ∃ _ : ((pCoreOf 2 H).subgroupOf (V ⊔ conjSub g⁻¹ V)).Normal,
    Nonempty (↥(V ⊔ conjSub g⁻¹ V) ⧸ (pCoreOf 2 H).subgroupOf (V ⊔ conjSub g⁻¹ V) ≃*
      Equiv.Perm (Fin 3))
  hUI : (V ⊔ conjSub g⁻¹ V) ⊓ pCoreOf 2 H = V₃ ⊔ conjSub g⁻¹ V₃
  C : Q8Coords (conjClosure V₃ H)
  Cz : ∀ x, x ∈ V₁ ↔ x = 1 ∨ x = C.z
  v : G
  v_mem : v ∈ V
  v_not : v ∉ pCoreOf 2 H

namespace A5SitPf15

variable {G : Type} [Group G] [Finite G] {T V V₁ V₃ L₁ H : Subgroup G}
  {S : A5Sit G T V V₁ V₃ L₁ H} {SY : A5SitY S L₁} (P : A5SitPf15 S SY)
include P

theorem z_mem_V1 : P.C.z ∈ V₁ := (P.Cz _).2 (Or.inr rfl)

theorem comm_z {x : G} (hx : x ∈ H) : x * P.C.z = P.C.z * x :=
  (Subgroup.mem_centralizer_iff.mp (S.hF.H_le_centralizer hx) _ P.z_mem_V1).symm

theorem card_U : Nat.card (conjClosure V₃ H) = 32 := P.hUQ8.1

theorem Idata : V₃ ⊔ conjSub P.g⁻¹ V₃ = conjClosure V₃ H ∧
    pCoreOf 2 (V ⊔ conjSub P.g⁻¹ V) = conjClosure V₃ H ∧
    Nat.card (pCoreOf 2 (V ⊔ conjSub P.g⁻¹ V)) = 32 ∧
    Nonempty (oTwoQuot ↥(V ⊔ conjSub P.g⁻¹ V) ≃* Equiv.Perm (Fin 3)) :=
  S.I_data P.hUQ8 P.g_mem P.hQ8 P.hS3 P.hUI

theorem I_inf_Q : (V ⊔ conjSub P.g⁻¹ V) ⊓ pCoreOf 2 H = conjClosure V₃ H :=
  P.hUI.trans P.Idata.1

theorem I_le_H : V ⊔ conjSub P.g⁻¹ V ≤ H := sup_le S.V_le_H (S.hF.conjSub_inv_le_H P.g_mem)

theorem Q_le_NI :
    pCoreOf 2 H ≤ Subgroup.normalizer ((V ⊔ conjSub P.g⁻¹ V : Subgroup G) : Set G) := by
  refine B2F.le_normalizer_sup S.Q_le_NV fun q hq => ?_
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have hq' : P.g * q * P.g⁻¹ ∈ pCoreOf 2 H :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 H P.g_mem) q).mp hq
  rw [mem_conjSub, mem_conjSub, inv_inv]
  have e : P.g * (q * x * q⁻¹) * P.g⁻¹ =
      (P.g * q * P.g⁻¹) * (P.g * x * P.g⁻¹) * (P.g * q * P.g⁻¹)⁻¹ := by group
  rw [e]
  exact Subgroup.mem_normalizer_iff.mp (S.Q_le_NV hq') _

theorem mem_V1_of_central {x : G} (hx : x ∈ conjClosure V₃ H)
    (hc : ∀ u ∈ conjClosure V₃ H, x * u = u * x) : x ∈ V₁ :=
  (P.Cz x).2 (P.C.center ⟨x, hx⟩ fun u => Subtype.ext (hc u u.2))

theorem H_le_Cz : H ≤ Subgroup.centralizer ({P.C.z} : Set G) := fun _ hx =>
  Subgroup.mem_centralizer_singleton_iff.mpr (P.comm_z hx)

@[expose] noncomputable def Φ : ↥H →* MulAut (Multiplicative V4) :=
  P.C.act H (le_normalizer_conjClosure _ _) P.H_le_Cz

theorem Φ_mem (x : ↥H) : P.Φ x ∈ Oq := P.C.act_mem_Oq _ _ _ x

theorem Φ_eq_one_iff (x : ↥H) : P.Φ x = 1 ↔ (x : G) ∈ pCoreOf 2 H := by
  rw [S.mem_Q_iff x.2]
  unfold Φ
  rw [Q8Coords.act_eq_one_iff]
  refine forall₂_congr fun u _ => ?_
  rw [P.Cz]

theorem Φ_eq_iff (x y : ↥H) : P.Φ x = P.Φ y ↔ (x : G) * (y : G)⁻¹ ∈ pCoreOf 2 H := by
  rw [← mul_inv_eq_one, ← map_inv, ← map_mul, P.Φ_eq_one_iff]
  rfl

@[expose] noncomputable def ch : MulAut (Multiplicative V4) := P.Φ ⟨SY.c, SY.c_mem_H⟩

theorem mem_U_of_mem_L1_Q {x : G} (hx : x ∈ L₁) (hq : x ∈ pCoreOf 2 H) :
    x ∈ conjClosure V₃ H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [P.U_eq]
  refine le_pCoreOf_of_le_normalizer 2 (inf_le_left : L₁ ⊓ pCoreOf 2 H ≤ L₁)
    (F7.le_normalizer_inf Subgroup.le_normalizer (S.L1_le_H.trans (le_normalizer_pCoreOf 2 H)))
    ((pCoreOf_isPGroup 2 H).to_le inf_le_right) ⟨hx, hq⟩

theorem L1_trichotomy {x : G} (hx : x ∈ L₁) :
    x ∈ conjClosure V₃ H ∨ SY.c * SY.c * x ∈ conjClosure V₃ H ∨
      SY.c * x ∈ conjClosure V₃ H := by
  rw [P.U_eq]
  exact SY.decomp x hx

theorem Φ_L1 {x : ↥H} (hx : (x : G) ∈ L₁) :
    P.Φ x = 1 ∨ P.ch * P.ch * P.Φ x = 1 ∨ P.ch * P.Φ x = 1 := by
  unfold ch
  rcases P.L1_trichotomy hx with h | h | h
  · exact Or.inl ((P.Φ_eq_one_iff x).2 (S.U_le_Q h))
  · refine Or.inr (Or.inl ?_)
    rw [← map_mul, ← map_mul, P.Φ_eq_one_iff]
    exact S.U_le_Q h
  · refine Or.inr (Or.inr ?_)
    rw [← map_mul, P.Φ_eq_one_iff]
    exact S.U_le_Q h

theorem ch_ne_one : P.ch ≠ 1 := by
  intro h
  have hq := (P.Φ_eq_one_iff _).1 h
  have hu := P.mem_U_of_mem_L1_Q SY.c_mem hq
  rw [P.U_eq] at hu
  exact SY.c_not_mem hu

theorem ch_cube : P.ch ^ 3 = 1 := by
  unfold ch
  rw [← map_pow]
  have : ((⟨SY.c, SY.c_mem_H⟩ : ↥H) ^ 3 : ↥H) = 1 := Subtype.ext (by simpa using SY.c_cube)
  rw [this, map_one]

theorem ch_props : P.ch ∈ Oq ∧ P.ch ≠ 1 ∧ P.ch ^ 3 = 1 := ⟨P.Φ_mem _, P.ch_ne_one, P.ch_cube⟩

theorem Φ_normalizes (x : ↥H) :
    P.Φ x * P.ch = P.ch * P.Φ x ∨ P.Φ x * P.ch = P.ch * P.ch * P.Φ x := by
  have hy : ((x * ⟨SY.c, SY.c_mem_H⟩ * x⁻¹ : ↥H) : G) ∈ L₁ :=
    (Subgroup.mem_normalizer_iff.mp (P.hn x.2) _).mp SY.c_mem
  have hΦ : P.Φ (x * ⟨SY.c, SY.c_mem_H⟩ * x⁻¹) = P.Φ x * P.ch * (P.Φ x)⁻¹ := by
    rw [map_mul, map_mul, map_inv]
    rfl
  rcases P.Φ_L1 hy with h | h | h
  · rw [hΦ] at h
    exact absurd (by
      calc P.ch = (P.Φ x)⁻¹ * (P.Φ x * P.ch * (P.Φ x)⁻¹) * P.Φ x := by group
        _ = 1 := by rw [h]; group) P.ch_ne_one
  · rw [hΦ] at h
    exact Or.inl (comm_of_conj_eq_inv_sq P.ch_cube h)
  · rw [hΦ] at h
    exact Or.inr (conj_eq_sq_of_conj_eq_inv P.ch_cube h)

theorem v_mem_H : P.v ∈ H := S.V_le_H P.v_mem

theorem v'_mem : P.g⁻¹ * P.v * P.g ∈ conjSub P.g⁻¹ V := by
  rw [mem_conjSub, inv_inv]
  simpa [mul_assoc] using P.v_mem

theorem v'_mem_H : P.g⁻¹ * P.v * P.g ∈ H :=
  H.mul_mem (H.mul_mem (H.inv_mem P.g_mem) P.v_mem_H) P.g_mem

@[expose] noncomputable def t1 : MulAut (Multiplicative V4) := P.Φ ⟨P.v, P.v_mem_H⟩

@[expose] noncomputable def t2 : MulAut (Multiplicative V4) :=
  P.Φ ⟨P.g⁻¹ * P.v * P.g, P.v'_mem_H⟩

theorem comm_v_L1 {x : G} (hx : x ∈ L₁) : P.v * x * P.v⁻¹ * x⁻¹ ∈ pCoreOf 2 H :=
  S.comm_V_L1_mem_Q P.v_mem hx

theorem v'_not : P.g⁻¹ * P.v * P.g ∉ pCoreOf 2 H := fun h => by
  have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 H P.g_mem) _).mp h
  exact P.v_not (by simpa [mul_assoc] using this)

theorem t1_props : P.t1 ∈ Oq ∧ P.t1 ≠ 1 ∧ P.t1 * P.t1 = 1 ∧ P.t1 * P.ch = P.ch * P.t1 := by
  refine ⟨P.Φ_mem _, fun h => P.v_not ((P.Φ_eq_one_iff _).1 h), ?_, ?_⟩
  · unfold t1
    rw [← map_mul, P.Φ_eq_one_iff]
    show P.v * P.v ∈ pCoreOf 2 H
    rw [← pow_two, S.elemAbelian_V.2 _ P.v_mem]
    exact Subgroup.one_mem _
  · unfold t1 ch
    rw [← mul_inv_eq_one, mul_inv_rev, ← mul_assoc, ← map_inv, ← map_inv, ← map_mul, ← map_mul,
      ← map_mul, P.Φ_eq_one_iff]
    exact P.comm_v_L1 SY.c_mem

theorem t2_props : P.t2 ∈ Oq ∧ P.t2 ≠ 1 ∧ P.t2 * P.t2 = 1 ∧ P.t2 * P.ch = P.ch * P.t2 := by
  refine ⟨P.Φ_mem _, fun h => P.v'_not ((P.Φ_eq_one_iff _).1 h), ?_, ?_⟩
  · unfold t2
    rw [← map_mul, P.Φ_eq_one_iff]
    show P.g⁻¹ * P.v * P.g * (P.g⁻¹ * P.v * P.g) ∈ pCoreOf 2 H
    have hv2 : P.v * P.v = 1 := by rw [← pow_two]; exact S.elemAbelian_V.2 _ P.v_mem
    have e : P.g⁻¹ * P.v * P.g * (P.g⁻¹ * P.v * P.g) = P.g⁻¹ * (P.v * P.v) * P.g := by group
    rw [e, hv2]
    simp
  · unfold t2 ch
    rw [← mul_inv_eq_one, mul_inv_rev, ← mul_assoc, ← map_inv, ← map_inv, ← map_mul, ← map_mul,
      ← map_mul, P.Φ_eq_one_iff]
    have hc' : P.g * SY.c * P.g⁻¹ ∈ L₁ :=
      (Subgroup.mem_normalizer_iff.mp (P.hn P.g_mem) _).mp SY.c_mem
    have h := P.comm_v_L1 hc'
    have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 H (H.inv_mem P.g_mem)) _).mp h
    show P.g⁻¹ * P.v * P.g * SY.c * (P.g⁻¹ * P.v * P.g)⁻¹ * SY.c⁻¹ ∈ pCoreOf 2 H
    have e : P.g⁻¹ * P.v * P.g * SY.c * (P.g⁻¹ * P.v * P.g)⁻¹ * SY.c⁻¹ =
        P.g⁻¹ * (P.v * (P.g * SY.c * P.g⁻¹) * P.v⁻¹ * (P.g * SY.c * P.g⁻¹)⁻¹) * P.g⁻¹⁻¹ := by
      group
    rw [e]
    exact this

theorem V_cases {w : G} (hw : w ∈ V) : w ∈ pCoreOf 2 H ∨ w * P.v⁻¹ ∈ pCoreOf 2 H := by
  by_cases hwQ : w ∈ pCoreOf 2 H
  · exact Or.inl hwQ
  right
  have hV3 : V₃ = V ⊓ pCoreOf 2 H := (S.hF.F95_1 S.relIndex_V3 S.not_V_le).1
  have hidx : ((V ⊓ pCoreOf 2 H).subgroupOf V).index = 2 := by
    have := S.relIndex_V3
    rw [hV3] at this
    exact this
  have hmem := (Subgroup.mul_mem_iff_of_index_two hidx (a := ⟨w, hw⟩)
    (b := ⟨P.v⁻¹, V.inv_mem P.v_mem⟩)).2 (by
      constructor
      · intro h
        exact absurd (Subgroup.mem_subgroupOf.1 h).2 hwQ
      · intro h
        exact absurd ((pCoreOf 2 H).inv_mem_iff.1 (Subgroup.mem_subgroupOf.1 h).2) P.v_not)
  exact (Subgroup.mem_subgroupOf.1 hmem).2

theorem S3_facts : P.g⁻¹ * P.v * P.g * P.v⁻¹ ∉ pCoreOf 2 H ∧
    P.v * (P.g⁻¹ * P.v * P.g) ∉ pCoreOf 2 H ∧ (P.v * (P.g⁻¹ * P.v * P.g)) ^ 3 ∈ pCoreOf 2 H ∧
    ∃ y ∈ V ⊔ conjSub P.g⁻¹ V, y ^ 3 = 1 ∧ y ∉ Subgroup.normalizer (V : Set G) := by
  obtain ⟨hN, ⟨e⟩⟩ := P.hS3
  set I := V ⊔ conjSub P.g⁻¹ V with hIdef
  set π := QuotientGroup.mk' ((pCoreOf 2 H).subgroupOf I) with hπ
  have hπ1 : ∀ y : ↥I, π y = 1 ↔ (y : G) ∈ pCoreOf 2 H := fun y => by
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hπeq : ∀ y y' : ↥I, π y = π y' ↔ (y : G) * (y' : G)⁻¹ ∈ pCoreOf 2 H := fun y y' => by
    rw [← mul_inv_eq_one, ← map_inv, ← map_mul, hπ1]
    rfl
  have hvI : P.v ∈ I := le_sup_left (a := V) P.v_mem
  have hv'I : P.g⁻¹ * P.v * P.g ∈ I := le_sup_right (b := conjSub P.g⁻¹ V) P.v'_mem
  set a : ↥I := ⟨P.v, hvI⟩
  set b : ↥I := ⟨P.g⁻¹ * P.v * P.g, hv'I⟩
  have ha2 : π a * π a = 1 := by
    rw [← map_mul, hπ1]
    show P.v * P.v ∈ pCoreOf 2 H
    rw [← pow_two, S.elemAbelian_V.2 _ P.v_mem]
    exact Subgroup.one_mem _
  have hb2 : π b * π b = 1 := by
    rw [← map_mul, hπ1]
    show P.g⁻¹ * P.v * P.g * (P.g⁻¹ * P.v * P.g) ∈ pCoreOf 2 H
    have hv2 : P.v * P.v = 1 := by rw [← pow_two]; exact S.elemAbelian_V.2 _ P.v_mem
    have e : P.g⁻¹ * P.v * P.g * (P.g⁻¹ * P.v * P.g) = P.g⁻¹ * (P.v * P.v) * P.g := by group
    rw [e, hv2]
    simp
  have ha1 : π a ≠ 1 := fun h => P.v_not ((hπ1 a).1 h)
  have hb1 : π b ≠ 1 := fun h => P.v'_not ((hπ1 b).1 h)
  have hVimg : ∀ w (hw : w ∈ V), π ⟨w, le_sup_left (a := V) hw⟩ = 1 ∨
      π ⟨w, le_sup_left (a := V) hw⟩ = π a := by
    intro w hw
    rcases P.V_cases hw with h | h
    · exact Or.inl ((hπ1 _).2 h)
    · exact Or.inr ((hπeq _ _).2 h)
  have hV'img : ∀ w (hw : w ∈ conjSub P.g⁻¹ V), π ⟨w, le_sup_right (b := conjSub P.g⁻¹ V) hw⟩ = 1 ∨
      π ⟨w, le_sup_right (b := conjSub P.g⁻¹ V) hw⟩ = π b := by
    intro w hw
    have hw2 := hw
    rw [mem_conjSub, inv_inv] at hw2
    rcases P.V_cases hw2 with h | h
    · left
      rw [hπ1]
      have := (Subgroup.mem_normalizer_iff.mp
        (le_normalizer_pCoreOf 2 H (H.inv_mem P.g_mem)) _).mp h
      show w ∈ pCoreOf 2 H
      simpa [mul_assoc] using this
    · right
      rw [hπeq]
      have := (Subgroup.mem_normalizer_iff.mp
        (le_normalizer_pCoreOf 2 H (H.inv_mem P.g_mem)) _).mp h
      show w * (P.g⁻¹ * P.v * P.g)⁻¹ ∈ pCoreOf 2 H
      have e : w * (P.g⁻¹ * P.v * P.g)⁻¹ =
          P.g⁻¹ * (P.g * w * P.g⁻¹ * P.v⁻¹) * P.g⁻¹⁻¹ := by group
      rw [e]
      exact this
  have hab : π a ≠ π b := by
    intro hab
    set K : Subgroup G := ((pairSub (π a) ha2).comap π).map I.subtype
    have hIK : I ≤ K := by
      refine sup_le (fun w hw => ⟨⟨w, le_sup_left (a := V) hw⟩, hVimg w hw, rfl⟩) fun w hw =>
        ⟨⟨w, le_sup_right (b := conjSub P.g⁻¹ V) hw⟩, ?_, rfl⟩
      rcases hV'img w hw with h | h
      · exact Or.inl h
      · exact Or.inr (h.trans hab.symm)
    obtain ⟨ρ, hρ1, hρa⟩ := perm3_exists_ne (e (π a))
    obtain ⟨q, hq⟩ := QuotientGroup.mk_surjective (e.symm ρ)
    obtain ⟨y, hy, hyq⟩ := hIK q.2
    have hyq' : y = q := Subtype.ext hyq
    subst hyq'
    have hq' : e (π y) = ρ := by
      rw [show π y = (y : ↥I ⧸ (pCoreOf 2 H).subgroupOf I) from rfl, hq, MulEquiv.apply_symm_apply]
    rcases (show π y = 1 ∨ π y = π a from hy) with h | h
    · rw [h, map_one] at hq'
      exact hρ1 hq'.symm
    · rw [h] at hq'
      exact hρa hq'.symm
  have hστ := perm3_mul_of_ne (e (π a)) (e (π b)) (by rw [← map_mul, ha2, map_one])
    (by rw [← map_mul, hb2, map_one]) (fun h => ha1 (e.injective (h.trans (map_one e).symm)))
    (fun h => hb1 (e.injective (h.trans (map_one e).symm))) (fun h => hab (e.injective h))
  rw [← map_mul, ← map_mul] at hστ
  have hw1 : π (a * b) ≠ 1 := fun h => hστ.1 (by rw [h, map_one])
  have hw3 : π (a * b) ^ 3 = 1 := by
    apply e.injective
    rw [map_pow, map_one]
    exact hστ.2
  refine ⟨fun h => hab ((hπeq b a).2 h).symm, fun h => hw1 ((hπ1 (a * b)).2 h), ?_, ?_⟩
  · exact (hπ1 ((a * b) ^ 3)).1 (by rw [map_pow]; exact hw3)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hw3Q : (((a * b) ^ 3 : ↥I) : G) ∈ pCoreOf 2 H := (hπ1 _).1 (by rw [map_pow]; exact hw3)
  obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 H ⟨_, hw3Q⟩
  have hk' : (((a * b) ^ 3 : ↥I) : G) ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    exact this
  obtain ⟨y, hy⟩ : ∃ y : ↥I, y = (a * b) ^ 2 ^ k := ⟨_, rfl⟩
  have hy3 : (y : G) ^ 3 = 1 := by
    rw [hy, ← SubgroupClass.coe_pow, ← pow_mul, mul_comm (2 ^ k) 3, pow_mul,
      SubgroupClass.coe_pow]
    exact hk'
  have hord : orderOf (e (π (a * b))) = 3 :=
    orderOf_eq_prime (by rw [← map_pow, hw3, map_one]) (fun h => hw1 (e.injective
      (h.trans (map_one e).symm)))
  have hρ1 : e (π y) ≠ 1 := by
    intro h
    rw [hy, map_pow, map_pow] at h
    have := orderOf_dvd_of_pow_eq_one h
    rw [hord] at this
    have h3 := (Nat.prime_dvd_prime_iff_eq (Nat.prime_three) Nat.prime_two).1
      (Nat.Prime.dvd_of_dvd_pow Nat.prime_three this)
    omega
  have hρ3 : e (π y) ^ 3 = 1 := by
    rw [← map_pow, ← map_pow]
    have : y ^ 3 = 1 := Subtype.ext hy3
    rw [this, map_one, map_one]
  refine ⟨y, y.2, hy3, fun hyN => ?_⟩
  have hc : (y : G) * P.v * (y : G)⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hyN _).mp P.v_mem
  have hcon := perm3_conj_ne (e (π a)) (e (π y)) (by rw [← map_mul, ha2, map_one])
    (fun h => ha1 (e.injective (h.trans (map_one e).symm))) hρ3 hρ1
  have hyv : y * a * y⁻¹ = ⟨(y : G) * P.v * (y : G)⁻¹, le_sup_left (a := V) hc⟩ := rfl
  rcases hVimg _ hc with h | h
  · apply hcon.1
    rw [← map_inv, ← map_mul, ← map_mul, ← map_inv, ← map_mul, ← map_mul, hyv, h, map_one]
  · apply hcon.2
    rw [← map_inv, ← map_mul, ← map_mul, ← map_inv, ← map_mul, ← map_mul, hyv, h]

theorem t12_props : P.t1 * P.t2 ≠ 1 ∧ (P.t1 * P.t2) ^ 3 = 1 := by
  obtain ⟨-, h1, h3, -⟩ := P.S3_facts
  unfold t1 t2
  rw [← map_mul, ← map_pow]
  exact ⟨fun h => h1 ((P.Φ_eq_one_iff _).1 h), (P.Φ_eq_one_iff _).2 h3⟩

end A5SitPf15

end CFSG.Quasithin.H13
