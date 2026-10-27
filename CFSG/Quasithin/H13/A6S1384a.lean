module

public import CFSG.Quasithin.H13.A6S1383
public import CFSG.Quasithin.H13.A6S13710c
public import CFSG.Quasithin.Background.F9Fourteen
public import CFSG.Quasithin.Background.F9Sixteen
public import CFSG.Quasithin.Background.F9Dual
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.CosetGeom CFSG.Quasithin.F7
open scoped commutatorElement

theorem conjSub_conjClosure_eq {G : Type} [Group G] (a : G) (Z K : Subgroup G) :
    conjSub a (conjClosure Z K) = conjClosure (conjSub a Z) (conjSub a K) := by
  apply le_antisymm
  · rw [conjSub_le_iff]
    refine conjClosure_le fun k hk z hz => ?_
    rw [mem_conjSub, inv_inv]
    have e : a * (k * z * k⁻¹) * a⁻¹ = (a * k * a⁻¹) * (a * z * a⁻¹) * (a * k * a⁻¹)⁻¹ := by
      group
    rw [e]
    exact mem_conjClosure (mul_mem_conjSub hk) (mul_mem_conjSub hz)
  · refine conjClosure_le fun k hk z hz => ?_
    rw [mem_conjSub] at hk hz ⊢
    have e : a⁻¹ * (k * z * k⁻¹) * a = (a⁻¹ * k * a) * (a⁻¹ * z * a) * (a⁻¹ * k * a)⁻¹ := by
      group
    rw [e]
    exact mem_conjClosure hk hz

theorem isPGroup_of_isElemAbelian {G : Type} [Group G] {X : Subgroup G}
    (hX : IsElemAbelian 2 X) : IsPGroup 2 X := CFSG.Open.IsElemAbelian.isPGroup hX

theorem relIndex_ne_zero' {G : Type} [Group G] [Finite G] (H K : Subgroup G) :
    H.relIndex K ≠ 0 := by
  show (H.subgroupOf K).index ≠ 0
  exact Subgroup.index_ne_zero_of_finite

@[expose] def InducesTransvMod {G : Type} [Group G] (h : G) (X Y : Subgroup G) : Prop :=
  ¬ (∀ x ∈ X, h * x * h⁻¹ * x⁻¹ ∈ Y) ∧
    ∃ c : G, ∀ x ∈ X, h * x * h⁻¹ * x⁻¹ ∈ Y ∨ (h * x * h⁻¹ * x⁻¹) * c⁻¹ ∈ Y

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

section F98

variable (hNS : ¬ LieModel G .PSp 3 2 1) (h13315 : Stmt13_3_15) (h1356two : Input1356Two)
  {H : Subgroup G} (hH : H ∈ S.Hz) (hF : HypF98 T V L (fsuV1 T V) S.V3 H)
include hNS h13315 h1356two hH hF

theorem UL_le_Q :
    conjClosure (conjClosure S.V3 H) L ≤ pCoreOf 2 (L ⊔ T) := by
  have hab := hF.F911_3
  have hUQ : conjClosure S.V3 H ≤ pCoreOf 2 (L ⊔ T) := by
    rw [← S.cT]
    exact le_inf (S.UH_le_T hNS h1356two h13315 hH)
      (Setting4.UH_le_centralizer_V (S := S) hNS h13315 h1356two hH hab)
  refine conjClosure_le fun l hl u hu => ?_
  exact (Subgroup.mem_normalizer_iff.mp
    (le_normalizer_pCoreOf 2 (L ⊔ T) (Subgroup.mem_sup_left hl)) u).mp (hUQ hu)

omit hNS h13315 h1356two hH in
theorem isElemAbelian_UL_of_lt (hb : 3 < F8.b T V L H) :
    IsElemAbelian 2 (conjClosure (conjClosure S.V3 H) L) :=
  hF.F914_1_of_lt hb

omit hNS h13315 h1356two hH in
theorem exists_A1_le_of_b_eq_three {γ γ' : F8.Geom T L H} {g : ↥((L ⊔ T) ⊔ H)}
    (s : F8Setup T V L H γ γ' g) (hb : F8.b T V L H = 3) :
    ∃ k ∈ H, F8.A₁ (fsuV1 T V) (g : G) ≤ conjSub k⁻¹ V :=
  hF.F914_2 s hb

omit hF in
theorem V_not_le_UH (h13314 : Stmt13_3_14) :
    ¬ V ≤ conjClosure S.V3 H := by
  intro hVU
  apply S.not_comm_VH_H_le_UH hNS h13315 h1356two hH h13314
  have hVH : conjClosure V H ≤ conjClosure S.V3 H := by
    refine conjClosure_le fun h hh v hv => ?_
    exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure S.V3 H hh) v).mp (hVU hv)
  intro h hh x hx
  have hxU := hVH hx
  have hhU : h * x * h⁻¹ ∈ conjClosure S.V3 H :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure S.V3 H hh) x).mp hxU
  exact (conjClosure S.V3 H).mul_mem hhU ((conjClosure S.V3 H).inv_mem hxU)

omit hNS h13315 h1356two hH hF in
theorem relIndex_V3_V : S.V3.relIndex V = 2 := by
  have h1 := Subgroup.relIndex_mul_card S.V3 V
  rw [inf_eq_left.2 S.V3_le_V, S.card_V, S.card_V3] at h1
  omega

omit hF in
theorem V_inf_UH (h13314 : Stmt13_3_14) :
    V ⊓ conjClosure S.V3 H = S.V3 := by
  have hle : S.V3 ≤ V ⊓ conjClosure S.V3 H := le_inf S.V3_le_V (le_conjClosure _ _)
  have hlt : V ⊓ conjClosure S.V3 H < V :=
    lt_of_le_of_ne inf_le_left fun h => S.V_not_le_UH hNS h13315 h1356two hH h13314
      (h.ge.trans inf_le_right)
  have h1 := Subgroup.relIndex_mul_relIndex S.V3 (V ⊓ conjClosure S.V3 H) V hle inf_le_left
  rw [S.relIndex_V3_V] at h1
  have h2 : (V ⊓ conjClosure S.V3 H).relIndex V ≠ 1 := by
    rw [Ne, Subgroup.relIndex_eq_one]
    exact fun h => hlt.ne (le_antisymm inf_le_left h)
  have h3 : (V ⊓ conjClosure S.V3 H).relIndex V ≠ 0 := by
    show ((V ⊓ conjClosure S.V3 H).subgroupOf V).index ≠ 0
    exact Subgroup.index_ne_zero_of_finite
  have h4 : S.V3.relIndex (V ⊓ conjClosure S.V3 H) = 1 := by
    have hd : (V ⊓ conjClosure S.V3 H).relIndex V ∣ 2 := Dvd.intro_left _ h1
    have h5 : (V ⊓ conjClosure S.V3 H).relIndex V = 2 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hd with h | h
      · exact absurd h h2
      · exact h
    rw [h5] at h1
    omega
  exact le_antisymm (Subgroup.relIndex_eq_one.mp h4) hle

omit hNS h13315 h1356two hH in
theorem comm_comm_VH_Vγ {γ γ' : F8.Geom T L H} {g : ↥((L ⊔ T) ⊔ H)}
    (s : F8Setup T V L H γ γ' g) :
    ⁅⁅conjClosure V H, F8.Uγ V H (g : G)⁆, F8.Uγ V H (g : G)⁆ = ⊥ := by
  have h1 := hF.F913_3 s (X := V) (Y := V) (Or.inr rfl) (Or.inr rfl)
  have hab := hF.isElemAbelian_Vγ (g := g)
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact isElemAbelian_comm hab hy (h1 hx).2

omit hNS h13315 h1356two hH in
theorem comm_comm_UH_Vγ {γ γ' : F8.Geom T L H} {g : ↥((L ⊔ T) ⊔ H)}
    (s : F8Setup T V L H γ γ' g) :
    ⁅⁅conjClosure S.V3 H, F8.Uγ V H (g : G)⁆, F8.Uγ V H (g : G)⁆ = ⊥ := by
  have h1 := hF.F913_3 s (X := S.V3) (Y := V) (Or.inl rfl) (Or.inr rfl)
  have hab := hF.isElemAbelian_Vγ (g := g)
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact isElemAbelian_comm hab hy (h1 hx).2

omit hF in
theorem V_lt_UL (h13314 : Stmt13_3_14) :
    V < conjClosure (conjClosure S.V3 H) L := by
  have hzV3 : S.z ∈ S.V3 := (S.V1_le_V2.trans S.V2_le_V3) (S.mem_V1_iff.2 (Or.inr rfl))
  have hle : V ≤ conjClosure (conjClosure S.V3 H) L := by
    intro v hv
    by_cases hv1 : v = 1
    · rw [hv1]; exact Subgroup.one_mem _
    obtain ⟨l, hlL, hlv⟩ := S.exists_L_conj_z hv hv1
    have e : v = (l : G)⁻¹ * S.z * (l : G)⁻¹⁻¹ := by
      rw [← hlv]; group
    rw [e]
    exact mem_conjClosure (L.inv_mem hlL) (le_conjClosure _ _ hzV3)
  refine lt_of_le_of_ne hle fun h => ?_
  have hU : conjClosure S.V3 H ≤ V := (le_conjClosure _ L).trans h.ge
  have hUV3 : conjClosure S.V3 H ≤ S.V3 :=
    (le_inf hU le_rfl).trans (S.V_inf_UH hNS h13315 h1356two hH h13314).le
  exact (S.V3_lt_UH h13315 hH).ne' (le_antisymm hUV3 (le_conjClosure _ _))

omit hNS h13315 h1356two hH hF in
theorem comm_mem_V3_of_normalizes {y v : G} (hyV : y ∈ Subgroup.normalizer (V : Set G))
    (hyV3 : y ∈ Subgroup.normalizer (S.V3 : Set G)) (hv : v ∈ V) :
    y * v * y⁻¹ * v⁻¹ ∈ S.V3 := by
  have hidx : (S.V3.subgroupOf V).index = 2 := S.relIndex_V3_V
  have hyv : y * v * y⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hyV v).mp hv
  have key := Subgroup.mul_mem_iff_of_index_two hidx (a := ⟨y * v * y⁻¹, hyv⟩)
    (b := ⟨v⁻¹, V.inv_mem hv⟩)
  simp only [Subgroup.mem_subgroupOf] at key
  refine key.mpr ?_
  have h1 : y * v * y⁻¹ ∈ S.V3 ↔ v ∈ S.V3 := ((Subgroup.mem_normalizer_iff.mp hyV3 v)).symm
  have h2 : v⁻¹ ∈ S.V3 ↔ v ∈ S.V3 := Subgroup.inv_mem_iff _
  rw [h1, h2]

theorem not_comm_le_UH_of_gen (h13314 : Stmt13_3_14)
    {F : Subgroup G} (hFH : F ≤ H) (hgen : H = conjClosure F H ⊔ (H ⊓ (L ⊔ T))) :
    ¬ ⁅F, conjClosure V H⁆ ≤ conjClosure S.V3 H := by
  intro hle
  have hHU : H ≤ Subgroup.normalizer (conjClosure S.V3 H : Set G) :=
    le_normalizer_conjClosure S.V3 H
  have hFC : conjClosure F H ≤ centralizerMod (conjClosure S.V3 H) H V := by
    refine conjClosure_le fun k hk f hf => ⟨H.mul_mem (H.mul_mem hk (hFH hf)) (H.inv_mem hk),
      hHU (H.mul_mem (H.mul_mem hk (hFH hf)) (H.inv_mem hk)), fun v hv => ?_⟩
    have hv' : k⁻¹ * v * k⁻¹⁻¹ ∈ conjClosure V H := mem_conjClosure (H.inv_mem hk) hv
    have h1 := hle (Subgroup.commutator_mem_commutator hf hv')
    have h2 := (Subgroup.mem_normalizer_iff.mp (hHU hk) _).mp h1
    have e : k * f * k⁻¹ * v * (k * f * k⁻¹)⁻¹ * v⁻¹ =
        k * ⁅f, k⁻¹ * v * k⁻¹⁻¹⁆ * k⁻¹ := by
      rw [commutatorElement_def]; group
    rw [e]
    exact h2
  have hLTC : H ⊓ (L ⊔ T) ≤ centralizerMod (conjClosure S.V3 H) H V := by
    intro y hy
    refine ⟨hy.1, hHU hy.1, fun v hv => ?_⟩
    have hy' : y ∈ L₁Of L (fsuV1 T V) ⊔ T := by
      rw [← hF.LT_inf_H]
      exact ⟨hy.2, hy.1⟩
    have hyV3 := hF.L₁T_normalizes_Vp hy'
    have hyV : y ∈ Subgroup.normalizer (V : Set G) :=
      (sup_le (S.L1_le_L.trans S.frame.L_le) S.frame.T_le) hy'
    exact le_conjClosure _ H (S.comm_mem_V3_of_normalizes hyV hyV3 hv)
  have hall : H ≤ centralizerMod (conjClosure S.V3 H) H V :=
    hgen.le.trans (sup_le hFC hLTC)
  apply S.not_comm_VH_H_le_UH hNS h13315 h1356two hH h13314
  have hD : conjClosure V H ≤ centralizerMod (conjClosure S.V3 H) (conjClosure V H) H := by
    refine conjClosure_le fun k hk v hv => ⟨mem_conjClosure hk hv,
      hHU (H.mul_mem (H.mul_mem hk (hF.V_le_H hv)) (H.inv_mem hk)), fun h hh => ?_⟩
    have hh' : k⁻¹ * h * k⁻¹⁻¹ ∈ H := H.mul_mem (H.mul_mem (H.inv_mem hk) hh) (inv_mem
      (H.inv_mem hk))
    have h1 := (hall hh').2.2 v hv
    have h2 := (Subgroup.mem_normalizer_iff.mp (hHU hk) _).mp ((conjClosure S.V3 H).inv_mem h1)
    have e : k * v * k⁻¹ * h * (k * v * k⁻¹)⁻¹ * h⁻¹ =
        k * (k⁻¹ * h * k⁻¹⁻¹ * v * (k⁻¹ * h * k⁻¹⁻¹)⁻¹ * v⁻¹)⁻¹ * k⁻¹ := by group
    rw [e]
    exact h2
  intro h hh x hx
  have h1 := (hD hx).2.2 h hh
  have e : h * x * h⁻¹ * x⁻¹ = (x * h * x⁻¹ * h⁻¹)⁻¹ := by group
  rw [e]
  exact (conjClosure S.V3 H).inv_mem h1

variable {γ γ' : F8.Geom T L H} {g : ↥((L ⊔ T) ⊔ H)}

omit hNS h13315 h1356two hH in
theorem stab_γ_eq (s : F8Setup T V L H γ γ' g) : stab γ = conjSub (g : G) H := by
  rw [← s.edge₁, stab_smul, stab_γ₁ hF.amalgamHypV.le₂]

omit hNS h13315 h1356two hH in
theorem stab_γ'_eq (s : F8Setup T V L H γ γ' g) : stab γ' = conjSub (g : G) (L ⊔ T) := by
  rw [← s.edge₀, stab_smul, stab_γ₀ hF.amalgamHypV.le₁]

theorem not_comm_le_Uγ_of_gen (h13314 : Stmt13_3_14)
    (s : F8Setup T V L H γ γ' g) {F : Subgroup G} (hFγ : F ≤ stab γ)
    (hgen : stab γ = conjClosure F (stab γ) ⊔ (stab γ ⊓ stab γ')) :
    ¬ ⁅F, F8.Uγ V H (g : G)⁆ ≤ F8.Uγ S.V3 H (g : G) := by
  have hstab := S.stab_γ_eq hF s
  have hstab' := S.stab_γ'_eq hF s
  intro hle
  refine S.not_comm_le_UH_of_gen hNS h13315 h1356two hH hF h13314 (F := conjSub (g : G)⁻¹ F)
    ?_ ?_ ?_
  · rw [conjSub_le_iff, inv_inv, ← hstab]
    exact hFγ
  · have h1 := congrArg (conjSub (g : G)⁻¹) hgen
    rw [conjSub_sup, conjSub_inf, conjSub_conjClosure_eq, hstab, hstab', conjSub_conjSub_inv,
      conjSub_conjSub_inv] at h1
    exact h1
  · have h1 := conjSub_mono (g : G)⁻¹ hle
    rw [← conjSub_commutator, F8.Uγ, F8.Uγ, conjSub_conjSub_inv, conjSub_conjSub_inv] at h1
    exact h1

theorem comm_le_Uγ_sup_V1_of_gen (h13314 : Stmt13_3_14)
    (s : F8Setup T V L H γ γ' g) {F : Subgroup G} (hFU : F ≤ conjClosure S.V3 H)
    (hgen : stab γ = conjClosure F (stab γ) ⊔ (stab γ ⊓ stab γ'))
    (heq : ⁅F, F8.Uγ S.V3 H (g : G)⁆ ⊔ fsuV1 T V = ⁅F, F8.Uγ V H (g : G)⁆ ⊔ fsuV1 T V) :
    ¬ fsuV1 T V ≤ F8.Uγ S.V3 H (g : G) ∧
      ⁅F, F8.Uγ V H (g : G)⁆ ≤ F8.Uγ S.V3 H (g : G) ⊔ fsuV1 T V ∧
      ¬ ⁅F, F8.Uγ V H (g : G)⁆ ≤ F8.Uγ S.V3 H (g : G) := by
  have hUγ : conjClosure S.V3 H ≤ stab γ :=
    (conjClosure_mono S.V3_le_V le_rfl).trans ((hF.F913_2 s).1.trans ((pCoreOf_le 2 _).trans
      inf_le_right))
  have hFγ : F ≤ stab γ := hFU.trans hUγ
  have hnot := S.not_comm_le_Uγ_of_gen hNS h13315 h1356two hH hF h13314 s hFγ hgen
  have hFN : F ≤ Subgroup.normalizer (F8.Uγ S.V3 H (g : G) : Set G) :=
    hFγ.trans (HypF98.stab_le_normalizer_Uγ s hF S.V3)
  have hFUγ : ⁅F, F8.Uγ S.V3 H (g : G)⁆ ≤ F8.Uγ S.V3 H (g : G) := by
    rw [Subgroup.commutator_le]
    intro f hf u hu
    rw [commutatorElement_def]
    exact (F8.Uγ S.V3 H (g : G)).mul_mem ((Subgroup.mem_normalizer_iff.mp (hFN hf) u).mp hu)
      ((F8.Uγ S.V3 H (g : G)).inv_mem hu)
  have hle : ⁅F, F8.Uγ V H (g : G)⁆ ≤ F8.Uγ S.V3 H (g : G) ⊔ fsuV1 T V :=
    calc ⁅F, F8.Uγ V H (g : G)⁆ ≤ ⁅F, F8.Uγ V H (g : G)⁆ ⊔ fsuV1 T V := le_sup_left
      _ = ⁅F, F8.Uγ S.V3 H (g : G)⁆ ⊔ fsuV1 T V := heq.symm
      _ ≤ F8.Uγ S.V3 H (g : G) ⊔ fsuV1 T V := sup_le_sup_right hFUγ _
  exact ⟨fun hV1 => hnot (hle.trans (sup_le le_rfl hV1)), hle, hnot⟩

omit hNS h13315 h1356two hH in
theorem lemma13_8_10 (s : F8Setup T V L H γ γ' g)
    (hγ : mIdx (conjClosure S.V3 H) (F8.DH S.V3 (fsuV1 T V) H (g : G)) ≤
      mIdx (F8.Uγ S.V3 H (g : G)) (F8.Dγ S.V3 (fsuV1 T V) H (g : G)))
    (h1 : mIdx (F8.Uγ S.V3 H (g : G)) (F8.Dγ S.V3 (fsuV1 T V) H (g : G)) = 1)
    (hlt : F8.DH S.V3 (fsuV1 T V) H (g : G) < conjClosure S.V3 H) :
    mIdx (conjClosure S.V3 H) (F8.DH S.V3 (fsuV1 T V) H (g : G)) = 1 ∧
      (fsuV1 T V ≤ F8.Uγ S.V3 H (g : G) ∨
        ⁅conjClosure S.V3 H, F8.Dγ S.V3 (fsuV1 T V) H (g : G)⁆ = ⊥) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨?_, ?_⟩
  ·
    have hU2 : IsPGroup 2 (conjClosure S.V3 H) :=
      (pCoreOf_isPGroup 2 H).to_le hF.conjClosure_Vp_le_pCoreOf
    have hidx := HypF98.relIndex_eq_two_pow_mIdx (Y := F8.DH S.V3 (fsuV1 T V) H (g : G)) hU2
    have hne : (F8.DH S.V3 (fsuV1 T V) H (g : G)).relIndex (conjClosure S.V3 H) ≠ 1 := by
      rw [Ne, Subgroup.relIndex_eq_one]
      exact fun h => hlt.ne (le_antisymm hlt.le h)
    have hpos : mIdx (conjClosure S.V3 H) (F8.DH S.V3 (fsuV1 T V) H (g : G)) ≠ 0 := by
      intro h0
      rw [h0, pow_zero] at hidx
      exact hne hidx
    omega
  · by_cases hV1 : fsuV1 T V ≤ F8.Uγ S.V3 H (g : G)
    · exact Or.inl hV1
    · right
      have h2 : ⁅conjClosure S.V3 H, F8.Dγ S.V3 (fsuV1 T V) H (g : G)⁆ ≤ fsuV1 T V :=
        commutator_centralizerMod_le _ _ _
      have h3 : ⁅conjClosure S.V3 H, F8.Dγ S.V3 (fsuV1 T V) H (g : G)⁆ ≤
          F8.Uγ S.V3 H (g : G) :=
        (Subgroup.commutator_mono le_rfl (centralizerMod_le_left _ _ _)).trans
          ((hF.F913_3 s (X := S.V3) (Y := S.V3) (Or.inl rfl) (Or.inl rfl)).trans inf_le_right)
      have h4 : fsuV1 T V ⊓ F8.Uγ S.V3 H (g : G) = ⊥ := by
        by_contra hne
        exact hV1 (le_of_card_eq_two_of_inf_ne_bot hF.card_V₁ hne)
      exact le_bot_iff.mp ((le_inf h2 h3).trans h4.le)

theorem lemma13_8_11_one (h13314 : Stmt13_3_14)
    (s : F8Setup T V L H γ γ' g)
    (hgen : stab γ = conjClosure (conjClosure S.V3 H) (stab γ) ⊔ (stab γ ⊓ stab γ'))
    (hcase : fsuV1 T V ≤ F8.Uγ S.V3 H (g : G) ∨
      ∀ h ∈ H, ¬ InducesTransvMod h (conjClosure V H) (conjClosure S.V3 H)) :
    ¬ F8.Uγ V H (g : G) ≤ F8.Uγ S.V3 H (g : G) ⊔ pCoreOf 2 H := by
  intro hle
  have hF1 := hF.toHypF91
  have hUγH : F8.Uγ S.V3 H (g : G) ≤ H := hF.Uγ_le_H s
  have hUγQ : F8.Uγ S.V3 H (g : G) ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
    hUγH.trans (le_normalizer_pCoreOf 2 H)
  have heq : ⁅conjClosure S.V3 H, F8.Uγ S.V3 H (g : G)⁆ ⊔ fsuV1 T V =
      ⁅conjClosure S.V3 H, F8.Uγ V H (g : G)⁆ ⊔ fsuV1 T V := by
    refine le_antisymm (sup_le_sup_right (Subgroup.commutator_mono le_rfl hF.Uγ_le_Vγ) _) ?_
    refine sup_le ?_ le_sup_right
    rw [Subgroup.commutator_le]
    intro u hu x hx
    have hx' : x ∈ ((F8.Uγ S.V3 H (g : G) ⊔ pCoreOf 2 H : Subgroup G) : Set G) := hle hx
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hUγQ] at hx'
    obtain ⟨a, ha, q, hq, rfl⟩ := Set.mem_mul.mp hx'
    have huq : u * q * u⁻¹ * q⁻¹ ∈ fsuV1 T V := by
      have := (fsuV1 T V).inv_mem (hF1.commutator_mem_V₁ hq hu)
      have e : (q * u * q⁻¹ * u⁻¹)⁻¹ = u * q * u⁻¹ * q⁻¹ := by group
      rwa [e] at this
    have hc := hF1.conj_eq_of_mem_V₁ (hUγH ha) huq
    have e : ⁅u, a * q⁆ = ⁅u, a⁆ * (a * (u * q * u⁻¹ * q⁻¹) * a⁻¹) := by
      rw [commutatorElement_def, commutatorElement_def]; group
    rw [e, hc]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.commutator_mem_commutator hu ha))
      (Subgroup.mem_sup_right huq)
  obtain ⟨hV1, hle2, hnot⟩ := S.comm_le_Uγ_sup_V1_of_gen hNS h13315 h1356two hH hF h13314 s
    le_rfl hgen heq
  rcases hcase with hV1' | hnoT
  · exact hV1 hV1'
  ·
    obtain ⟨u, hu, x, hx, hux⟩ : ∃ u ∈ conjClosure S.V3 H, ∃ x ∈ F8.Uγ V H (g : G),
        u * x * u⁻¹ * x⁻¹ ∉ F8.Uγ S.V3 H (g : G) := by
      by_contra hall
      push Not at hall
      exact hnot (Subgroup.commutator_le.mpr fun u hu x hx => by
        rw [commutatorElement_def]; exact hall u hu x hx)
    obtain ⟨⟨z, hz⟩, hz1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hF.V₁_ne_bot
    have hV1z : ∀ w ∈ fsuV1 T V, w = 1 ∨ w = z := by
      intro w hw
      obtain ⟨y, hy, huniq⟩ := (Nat.card_eq_two_iff' (1 : ↥(fsuV1 T V))).mp hF.card_V₁
      have hz' : (⟨z, hz⟩ : ↥(fsuV1 T V)) = y := huniq _ hz1
      by_cases hw1 : w = 1
      · exact Or.inl hw1
      · right
        have hw' : (⟨w, hw⟩ : ↥(fsuV1 T V)) = y :=
          huniq _ (fun e => hw1 (by simpa using congrArg Subtype.val e))
        exact congrArg Subtype.val (hw'.trans hz'.symm)
    have hUH : conjClosure S.V3 H ≤ conjSub (g : G) H := by
      rw [← S.stab_γ_eq hF s]
      exact (conjClosure_mono S.V3_le_V le_rfl).trans ((hF.F913_2 s).1.trans
        ((pCoreOf_le 2 _).trans inf_le_right))
    have hu₀ : (g : G)⁻¹ * u * (g : G) ∈ H := by
      have := hUH hu
      rwa [mem_conjSub] at this
    refine hnoT _ hu₀ ⟨fun hall => hux ?_, (g : G)⁻¹ * z * (g : G), fun y hy => ?_⟩
    · have hx₀ : (g : G)⁻¹ * x * (g : G) ∈ conjClosure V H := by
        have := hx
        rwa [F8.Uγ, mem_conjSub] at this
      have h1 := hall _ hx₀
      have e : u * x * u⁻¹ * x⁻¹ = (g : G) * (((g : G)⁻¹ * u * (g : G)) *
          ((g : G)⁻¹ * x * (g : G)) * ((g : G)⁻¹ * u * (g : G))⁻¹ *
            ((g : G)⁻¹ * x * (g : G))⁻¹) * (g : G)⁻¹ := by group
      rw [e, F8.Uγ]
      exact mul_mem_conjSub h1
    · have hy' : (g : G) * y * (g : G)⁻¹ ∈ F8.Uγ V H (g : G) := by
        rw [F8.Uγ]; exact mul_mem_conjSub hy
      have h1 := hle2 (Subgroup.commutator_mem_commutator hu hy')
      rw [commutatorElement_def] at h1
      have hN : F8.Uγ S.V3 H (g : G) ≤ Subgroup.normalizer ((fsuV1 T V : Subgroup G) : Set G) :=
        hUγH.trans hF.H_normalizes_V₁
      have h1' : u * ((g : G) * y * (g : G)⁻¹) * u⁻¹ * ((g : G) * y * (g : G)⁻¹)⁻¹ ∈
          ((F8.Uγ S.V3 H (g : G) ⊔ fsuV1 T V : Subgroup G) : Set G) := h1
      rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hN] at h1'
      obtain ⟨a, ha, w, hw, hawe⟩ := Set.mem_mul.mp h1'
      have e₀ : ((g : G)⁻¹ * u * (g : G)) * y * ((g : G)⁻¹ * u * (g : G))⁻¹ * y⁻¹ =
          (g : G)⁻¹ * (u * ((g : G) * y * (g : G)⁻¹) * u⁻¹ * ((g : G) * y * (g : G)⁻¹)⁻¹) *
            (g : G) := by group
      have ha₀ : (g : G)⁻¹ * a * (g : G) ∈ conjClosure S.V3 H := by
        have ha' : a ∈ F8.Uγ S.V3 H (g : G) := ha
        rwa [F8.Uγ, mem_conjSub] at ha'
      rcases hV1z w hw with rfl | rfl
      · left
        rw [e₀, ← hawe, mul_one]
        exact ha₀
      · right
        rw [e₀, ← hawe]
        have e₁ : (g : G)⁻¹ * (a * w) * (g : G) * ((g : G)⁻¹ * w * (g : G))⁻¹ =
            (g : G)⁻¹ * a * (g : G) := by group
        rw [e₁]
        exact ha₀

theorem lemma13_8_11_two (h13314 : Stmt13_3_14)
    (s : F8Setup T V L H γ γ' g)
    (hne : F8.Dγ S.V3 (fsuV1 T V) H (g : G) < F8.Uγ S.V3 H (g : G))
    (hgen : stab γ = conjClosure (conjClosure S.V3 H) (stab γ) ⊔ (stab γ ⊓ stab γ'))
    (hγ : mIdx (conjClosure S.V3 H) (F8.DH S.V3 (fsuV1 T V) H (g : G)) ≤
      mIdx (F8.Uγ S.V3 H (g : G)) (F8.Dγ S.V3 (fsuV1 T V) H (g : G)))
    (hlt : F8.DH S.V3 (fsuV1 T V) H (g : G) < conjClosure S.V3 H)
    (hnot : ⁅conjClosure S.V3 H, F8.Dγ S.V3 (fsuV1 T V) H (g : G)⁆ ≠ ⊥) :
    1 < mIdx (F8.Uγ V H (g : G)) (F8.Uγ V H (g : G) ⊓ pCoreOf 2 H) := by
  by_contra hle
  push Not at hle
  set Q := pCoreOf 2 H with hQ
  set U := F8.Uγ S.V3 H (g : G) with hUdef
  set W := F8.Uγ V H (g : G) with hWdef
  have hUW : U ≤ W := hF.Uγ_le_Vγ
  have hU2 : IsPGroup 2 U := isPGroup_of_isElemAbelian hF.isElemAbelian_Uγ
  have hW2 : IsPGroup 2 W := isPGroup_of_isElemAbelian hF.isElemAbelian_Vγ
  have hD : F8.Dγ S.V3 (fsuV1 T V) H (g : G) = U ⊓ Q := hF.Dγ_eq_inf_pCoreOf s
  have iU : (U ⊓ Q).relIndex U = 2 ^ mIdx U (U ⊓ Q) := HypF98.relIndex_eq_two_pow_mIdx hU2
  have iW : (W ⊓ Q).relIndex W = 2 ^ mIdx W (W ⊓ Q) := HypF98.relIndex_eq_two_pow_mIdx hW2
  rw [Subgroup.inf_relIndex_left] at iU iW
  have hmU : mIdx U (U ⊓ Q) ≠ 0 := by
    intro h0
    rw [h0, pow_zero, Subgroup.relIndex_eq_one] at iU
    rw [hD] at hne
    exact hne.ne (le_antisymm inf_le_left (le_inf le_rfl iU))
  have hmono : mIdx U (U ⊓ Q) ≤ mIdx W (W ⊓ Q) := by
    have h1 := Subgroup.relIndex_le_of_le_right hUW (relIndex_ne_zero' Q W)
    rw [iU, iW] at h1
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h1
  have hmU1 : mIdx U (U ⊓ Q) = 1 := by omega
  have hmW1 : mIdx W (W ⊓ Q) = 1 := by omega
  rw [hmU1, pow_one] at iU
  rw [hmW1, pow_one] at iW
  have hVW : W ≤ U ⊔ Q := by
    set X := W ⊓ (U ⊔ Q) with hX
    have hUX : U ≤ X := le_inf hUW le_sup_left
    have h1 := Subgroup.relIndex_le_of_le_right hUX (relIndex_ne_zero' Q X)
    have hXW : X ≤ W := inf_le_left
    have h2 := Subgroup.relIndex_le_of_le_right hXW (relIndex_ne_zero' Q W)
    have hX2 : Q.relIndex X = 2 := by omega
    have hm := Subgroup.relIndex_mul_relIndex (Q ⊓ W) X W
      (le_inf inf_le_right (inf_le_left.trans le_sup_right)) inf_le_left
    rw [Subgroup.inf_relIndex_right] at hm
    have e : (Q ⊓ W).relIndex X = Q.relIndex X := by
      rw [← Subgroup.inf_relIndex_right (Q ⊓ W) X, ← Subgroup.inf_relIndex_right Q X]
      congr 1
      exact le_antisymm (inf_le_inf_right _ inf_le_left)
        (le_inf (le_inf inf_le_left (inf_le_right.trans inf_le_left)) inf_le_right)
    rw [e, hX2, iW] at hm
    have h3 : X.relIndex W = 1 := by omega
    exact (Subgroup.relIndex_eq_one.mp h3).trans inf_le_right
  have hm1 : mIdx U (F8.Dγ S.V3 (fsuV1 T V) H (g : G)) = 1 := by rw [hD]; exact hmU1
  obtain ⟨-, h10⟩ := S.lemma13_8_10 hF s hγ hm1 hlt
  rcases h10 with hV1 | hcomm
  · exact S.lemma13_8_11_one hNS h13315 h1356two hH hF h13314 s hgen (Or.inl hV1) hVW
  · exact hnot hcomm

end F98

end Setting4

end CFSG.Quasithin.H13.A6
