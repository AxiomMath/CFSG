module

public import CFSG.Quasithin.H13.A6S1372L76J

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.QuasithinUnique.Bridge
open scoped Pointwise IsMulCommutative

namespace A6L76K

theorem fix_L0 : ∀ γ : Perm (Fin 6), γ ^ 3 = 1 → A6L76E.PresL0 γ → act4f γ e0123 = e0123 →
    act4f γ (dv 0 2) = dv 0 2 ∧ act4f γ (dv 1 3) = dv 1 3 := by
  decide +kernel

theorem L0_pts : ∀ y : P6, A6L76E.InL0 y → y ≠ e0123 →
    (y = dv 0 2 ∧ e0123 * y = dv 1 3) ∨ (y = dv 1 3 ∧ e0123 * y = dv 0 2) := by
  decide +kernel

theorem e0123_facts : nrm (A6L76.vecS 6 {0, 1, 2, 3}) = e0123 ∧
    A6L76.vecS 6 {0, 1, 2, 3} ∈ (FFModel.altDn 6).sec :=
  ⟨by decide, G6.mem_coreMod.2 (by decide)⟩

theorem card_alt6 : Nat.card ↥(alternatingGroup (Fin 6)) = 360 := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  rfl

theorem permHom_ker (n : ℕ) : (A6L76J.permHom n).ker = ⊥ :=
  (MonoidHom.ker_eq_bot_iff _).2 fun _ _ h => Subtype.ext h

theorem not_three_dvd_permHom_ker (n : ℕ) : ¬ 3 ∣ Nat.card (A6L76J.permHom n).ker := by
  rw [permHom_ker, Subgroup.card_bot]
  norm_num

end A6L76K

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

@[expose] def TrivV3 (x : G) : Prop := ∀ v ∈ S.V3, x * v * x⁻¹ * v⁻¹ ∈ fsuV1 T V

theorem trivV3_mul {x y : G} (hy : y ∈ S.L1) (hx : S.TrivV3 x) (hy' : S.TrivV3 y) :
    S.TrivV3 (x * y) := by
  intro v hv
  have hv' : y * v * y⁻¹ ∈ S.V3 := conj_V3_of_L1 hy hv
  have e : x * y * v * (x * y)⁻¹ * v⁻¹ =
      (x * (y * v * y⁻¹) * x⁻¹ * (y * v * y⁻¹)⁻¹) * (y * v * y⁻¹ * v⁻¹) := by group
  rw [e]
  exact (fsuV1 T V).mul_mem (hx _ hv') (hy' v hv)

theorem trivV3_inv {x : G} (hx : x ∈ S.L1) (hx' : S.TrivV3 x) : S.TrivV3 x⁻¹ := by
  intro v hv
  have hv' : x⁻¹ * v * x⁻¹⁻¹ ∈ S.V3 := conj_V3_of_L1 (S.L1.inv_mem hx) hv
  have e : x⁻¹ * v * x⁻¹⁻¹ * v⁻¹ =
      (x * (x⁻¹ * v * x⁻¹⁻¹) * x⁻¹ * (x⁻¹ * v * x⁻¹⁻¹)⁻¹)⁻¹ := by group
  rw [e]
  exact (fsuV1 T V).inv_mem (hx' _ hv')

theorem trivV3_O2 {o : G} (ho : o ∈ pCoreOf 2 S.L1) :
    S.TrivV3 o :=
  fun _ hv => S.comm_O2L1_V3 ho hv

theorem not_trivV3_g {g : ↥(Subgroup.normalizer (V : Set G))}
    (hg : S.frame.ρ g = swap 0 1 * swap 1 2) : ¬ S.TrivV3 g :=
  fun h => S.comm_v2_not_mem_V1 hg (h _ S.v2_mem_V3)

theorem not_trivV3 (hhat : ¬ IsHatA6 L) {c : G}
    (hc : c ∈ S.L1) (hcO : c ∉ pCoreOf 2 S.L1) : ¬ S.TrivV3 c := by
  have hc0 := S.cL1_mem hhat
  have hc03 := S.cL1_cube hhat
  set c₀ : G := (S.cL1 hhat : G) with hc₀
  have hOL : ∀ o ∈ pCoreOf 2 S.L1, o ∈ S.L1 := fun o ho => pCoreOf_le 2 S.L1 ho
  have hc0' : ¬ S.TrivV3 c₀ := by
    intro h0
    obtain ⟨g, hgL, hg⟩ := S.exists_g012
    have h00 : S.TrivV3 (c₀ * c₀) := S.trivV3_mul hc0 h0 h0
    apply S.not_trivV3_g hg
    rcases S.L1_decomp hhat hgL with h | h | h
    · exact S.trivV3_O2 h
    · have e : (g : G) = (c₀ * c₀)⁻¹ * (c₀ * c₀ * g) := by group
      rw [e]
      exact S.trivV3_mul (hOL _ h) (S.trivV3_inv (S.L1.mul_mem hc0 hc0) h00) (S.trivV3_O2 h)
    · have e : (g : G) = c₀⁻¹ * (c₀ * g) := by group
      rw [e]
      exact S.trivV3_mul (hOL _ h) (S.trivV3_inv hc0 h0) (S.trivV3_O2 h)
  intro h
  apply hc0'
  rcases S.L1_decomp hhat hc with h' | h' | h'
  · exact absurd h' hcO
  · have h00 : S.TrivV3 (c₀ * c₀) := by
      have e : c₀ * c₀ = (c₀ * c₀ * c) * c⁻¹ := by group
      rw [e]
      exact S.trivV3_mul (S.L1.inv_mem hc) (S.trivV3_O2 h') (S.trivV3_inv hc h)
    have e : c₀ = c₀ * c₀ * (c₀ * c₀) := by
      rw [show c₀ * c₀ * (c₀ * c₀) = c₀ ^ 3 * c₀ by rw [pow_three']; simp only [mul_assoc],
        hc03, one_mul]
    rw [e]
    exact S.trivV3_mul (S.L1.mul_mem hc0 hc0) h00 h00
  · have e : c₀ = (c₀ * c) * c⁻¹ := by group
    rw [e]
    exact S.trivV3_mul (S.L1.inv_mem hc) (S.trivV3_O2 h') (S.trivV3_inv hc h)

variable {S}

namespace Ctx76

variable {H K : Subgroup G} [IsMulCommutative ↥(conjClosure S.V3 H)] {D : FFModel}

theorem βU_eq_one_of_conj (C : S.Ctx76 H K D) {k u : G} (hk : k ∈ K)
    (huU : u ∈ conjClosure S.V3 H) (h : C.βU ⟨k * u * k⁻¹, C.conj_mem_UH hk huU⟩ = 1) :
    C.βU ⟨u, huU⟩ = 1 := by
  rw [C.βU_eq_one_iff] at h ⊢
  intro k' hk'
  have h1 : (k * k' * k⁻¹) * (k * u * k⁻¹) * (k * k' * k⁻¹)⁻¹ * (k * u * k⁻¹)⁻¹ ∈ fsuV1 T V :=
    h _ (K.mul_mem (K.mul_mem hk hk') (K.inv_mem hk))
  show k' * u * k'⁻¹ * u⁻¹ ∈ fsuV1 T V
  have e : k' * u * k'⁻¹ * u⁻¹ = k⁻¹ * ((k * k' * k⁻¹) * (k * u * k⁻¹) * (k * k' * k⁻¹)⁻¹ *
      (k * u * k⁻¹)⁻¹) * k⁻¹⁻¹ := by group
  rw [e, S.conj_V1_of_mem C.hH (H.inv_mem (C.hKH hk)) h1]
  exact h1

theorem classes_V3_gen (C : S.Ctx76 H K D) {g : ↥(Subgroup.normalizer (V : Set G))}
    (hgL : (g : G) ∈ S.L1) (hg : S.frame.ρ g = swap 0 1 * swap 1 2) {u : G} (hu3 : u ∈ S.V3)
    (huU : u ∈ conjClosure S.V3 H) :
    C.βU ⟨u, huU⟩ = 1 ∨ C.βU ⟨u, huU⟩ = C.βU ⟨S.v2, S.v2_mem_UH H⟩ ∨
      C.βU ⟨u, huU⟩ = C.βU ⟨_, C.conj_mem_UH (C.hL1K hgL) (S.v2_mem_UH H)⟩ ∨
      C.βU ⟨u, huU⟩ = C.βU ⟨S.v2, S.v2_mem_UH H⟩ *
        C.βU ⟨_, C.conj_mem_UH (C.hL1K hgL) (S.v2_mem_UH H)⟩ := by
  rcases S.mem_V3_cases hg hu3 with h | h | h | h
  · exact Or.inl (C.βU_V1 h huU)
  · exact Or.inr (Or.inl (C.βU_eq_of_mul_mem huU (S.v2_mem_UH H) S.v2_mul_self h))
  · exact Or.inr (Or.inr (Or.inl (C.βU_eq_of_mul_mem huU _ (S.conj_v2_mul_self _) h)))
  · rw [← S.v2_mul_conj hg] at h
    have hb2 : (S.v2 * ((g : G) * S.v2 * (g : G)⁻¹)) * (S.v2 * ((g : G) * S.v2 * (g : G)⁻¹)) =
        1 := by
      rw [S.v2_mul_conj hg]
      exact S.conj_v2_mul_self _
    refine Or.inr (Or.inr (Or.inr ((C.βU_eq_of_mul_mem huU ((conjClosure S.V3 H).mul_mem
      (S.v2_mem_UH H) (C.conj_mem_UH (C.hL1K hgL) (S.v2_mem_UH H))) hb2 h).trans ?_)))
    rw [← map_mul]
    rfl

theorem βU_v2g_ne_one (C : S.Ctx76 H K D) {g : ↥(Subgroup.normalizer (V : Set G))}
    (hgL : (g : G) ∈ S.L1) : C.βU ⟨_, C.conj_mem_UH (C.hL1K hgL) (S.v2_mem_UH H)⟩ ≠ 1 :=
  fun h => C.βU_v2_ne_one (C.βU_eq_one_of_conj (C.hL1K hgL) (S.v2_mem_UH H) h)

theorem βU_v2_mul_ne_one (C : S.Ctx76 H K D) {g : ↥(Subgroup.normalizer (V : Set G))}
    (hgL : (g : G) ∈ S.L1) (hg : S.frame.ρ g = swap 0 1 * swap 1 2) :
    C.βU ⟨S.v2 * ((g : G) * S.v2 * (g : G)⁻¹), (conjClosure S.V3 H).mul_mem (S.v2_mem_UH H)
      (C.conj_mem_UH (C.hL1K hgL) (S.v2_mem_UH H))⟩ ≠ 1 := by
  have hg2K : ((g ^ 2 : ↥(Subgroup.normalizer (V : Set G))) : G) ∈ K := by
    rw [Subgroup.coe_pow]
    exact K.pow_mem (C.hL1K hgL) 2
  intro h
  apply C.βU_v2_ne_one
  apply C.βU_eq_one_of_conj hg2K (S.v2_mem_UH H)
  rw [← h]
  congr 1
  exact Subtype.ext (S.v2_mul_conj hg).symm

theorem βU_v2_ne_v2g (C : S.Ctx76 H K D) {g : ↥(Subgroup.normalizer (V : Set G))}
    (hgL : (g : G) ∈ S.L1) (hg : S.frame.ρ g = swap 0 1 * swap 1 2) :
    C.βU ⟨S.v2, S.v2_mem_UH H⟩ ≠ C.βU ⟨_, C.conj_mem_UH (C.hL1K hgL) (S.v2_mem_UH H)⟩ := by
  intro h
  apply C.βU_v2_mul_ne_one hgL hg
  rw [show (⟨S.v2 * ((g : G) * S.v2 * (g : G)⁻¹), (conjClosure S.V3 H).mul_mem (S.v2_mem_UH H)
      (C.conj_mem_UH (C.hL1K hgL) (S.v2_mem_UH H))⟩ : ↥(conjClosure S.V3 H)) =
      ⟨S.v2, S.v2_mem_UH H⟩ * ⟨_, C.conj_mem_UH (C.hL1K hgL) (S.v2_mem_UH H)⟩ from rfl,
    map_mul, ← h, ← map_mul,
    show (⟨S.v2, S.v2_mem_UH H⟩ * ⟨S.v2, S.v2_mem_UH H⟩ : ↥(conjClosure S.V3 H)) = 1 from
      Subtype.ext S.v2_mul_self, map_one]

theorem mem_V1_of_βU (C : S.Ctx76 H K D) {u : G} (hu3 : u ∈ S.V3)
    (huU : u ∈ conjClosure S.V3 H) (h : C.βU ⟨u, huU⟩ = 1) : u ∈ fsuV1 T V := by
  obtain ⟨g, hgL, hg⟩ := S.exists_g012
  rcases C.classes_V3_gen hgL hg hu3 huU with h' | h' | h' | h'
  · rcases S.mem_V3_cases hg hu3 with h1 | h1 | h1 | h1
    · exact h1
    · exact absurd ((C.βU_eq_of_mul_mem huU (S.v2_mem_UH H) S.v2_mul_self h1).symm.trans h)
        C.βU_v2_ne_one
    · exact absurd ((C.βU_eq_of_mul_mem huU _ (S.conj_v2_mul_self _) h1).symm.trans h)
        (C.βU_v2g_ne_one hgL)
    · rw [← S.v2_mul_conj hg] at h1
      have hb2 : (S.v2 * ((g : G) * S.v2 * (g : G)⁻¹)) *
          (S.v2 * ((g : G) * S.v2 * (g : G)⁻¹)) = 1 := by
        rw [S.v2_mul_conj hg]
        exact S.conj_v2_mul_self _
      exact absurd ((C.βU_eq_of_mul_mem huU _ hb2 h1).symm.trans h) (C.βU_v2_mul_ne_one hgL hg)
  · exact absurd (h'.symm.trans h) C.βU_v2_ne_one
  · exact absurd (h'.symm.trans h) (C.βU_v2g_ne_one hgL)
  · refine absurd (h'.symm.trans h) ?_
    rw [← map_mul]
    exact C.βU_v2_mul_ne_one hgL hg

theorem mapsOnto_V2_gen (C : S.Ctx76 H K D) {w : D.Amb} (hw : w ∈ D.sec)
    (hv : C.βU ⟨S.v2, S.v2_mem_UH H⟩ = QuotientGroup.mk ⟨w, hw⟩) :
    A6L76.MapsOnto C.β ((S.V2.subgroupOf (conjClosure S.V3 H)).map
      (InternalSec.secMk ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))) [1, w] := by
  refine ⟨fun x hx => ?_, fun v hv' => ?_⟩
  · obtain ⟨y, hy, hxy⟩ := Subgroup.mem_map.1 hx
    have e : x = C.ι y := Subtype.ext hxy.symm
    have hy2 : (y : G) ∈ S.V2 := Subgroup.mem_subgroupOf.1 hy
    rw [e]
    rcases S.mem_V2_cosets hy2 with h | h
    · refine ⟨1, ?_, List.mem_cons.2 (Or.inl rfl)⟩
      rw [show C.β (C.ι y) = C.βU ⟨y, y.2⟩ from rfl, C.βU_V1 h y.2]
      exact (QuotientGroup.mk_one _).symm
    · exact ⟨⟨w, hw⟩, (C.βU_eq_of_mul_mem y.2 (S.v2_mem_UH H) S.v2_mul_self h).trans hv,
        List.mem_cons.2 (Or.inr (List.mem_singleton.2 rfl))⟩
  · rcases List.mem_cons.1 hv' with rfl | hv'
    · exact ⟨1, Subgroup.one_mem _, 1, by rw [map_one]; exact (QuotientGroup.mk_one _).symm, rfl⟩
    · rw [List.mem_singleton.1 hv']
      exact ⟨C.ι ⟨S.v2, S.v2_mem_UH H⟩, Subgroup.mem_map_of_mem _
        (Subgroup.mem_subgroupOf.2 S.v2_mem_V2 : (⟨S.v2, S.v2_mem_UH H⟩ : ↥(conjClosure S.V3 H)) ∈
          S.V2.subgroupOf (conjClosure S.V3 H)), ⟨w, hw⟩, hv, rfl⟩

variable {H K : Subgroup G} [IsMulCommutative ↥(conjClosure S.V3 H)]

@[expose] noncomputable def β4 (C : S.Ctx76 H K (FFModel.altDn 6)) :
    ↥(conjClosure S.V3 H) →* ↥W4 :=
  modW4Equiv.toMonoidHom.comp C.βU

theorem β4_apply (C : S.Ctx76 H K (FFModel.altDn 6)) (u : ↥(conjClosure S.V3 H)) :
    C.β4 u = modW4Equiv (C.βU u) := rfl

theorem β4_eq_one_iff (C : S.Ctx76 H K (FFModel.altDn 6)) (u : ↥(conjClosure S.V3 H)) :
    C.β4 u = 1 ↔ C.βU u = 1 := by
  rw [β4_apply]
  exact MulEquiv.map_eq_one_iff _

theorem β4_equiv (C : S.Ctx76 H K (FFModel.altDn 6)) (k : ↥K) (u : ↥(conjClosure S.V3 H))
    (hku : (k : G) * u * (k : G)⁻¹ ∈ conjClosure S.V3 H) :
    C.β4 ⟨_, hku⟩ = act4 (A6L76C.permOf (C.α k)) (C.β4 u) := by
  obtain ⟨m, hxm⟩ := QuotientGroup.mk_surjective (C.βU u)
  rw [β4_apply, β4_apply, C.βU_equiv k u hku m.2 hxm.symm, ← hxm, modW4Equiv_mk, modW4Equiv_mk]
  apply Subtype.ext
  exact (nrm_permAct_nrm _ _).symm

theorem twist_β4 (C : S.Ctx76 H K (FFModel.altDn 6)) (τ : Perm (Fin 6))
    (u : ↥(conjClosure S.V3 H)) : (C.twist τ).β4 u = act4 τ (C.β4 u) := by
  obtain ⟨m, hxm⟩ := QuotientGroup.mk_surjective (C.βU u)
  rw [β4_apply, β4_apply, C.twist_βU, ← hxm, A6L76C.twistQ_mk, modW4Equiv_mk, modW4Equiv_mk]
  apply Subtype.ext
  exact (nrm_permAct_nrm _ _).symm

@[expose] noncomputable def x0 (C : S.Ctx76 H K (FFModel.altDn 6)) : P6 :=
  (C.β4 ⟨S.v2, S.v2_mem_UH H⟩ : ↥W4)

@[expose] noncomputable def y0 (C : S.Ctx76 H K (FFModel.altDn 6))
    {g : ↥(Subgroup.normalizer (V : Set G))} (hgL : (g : G) ∈ S.L1) : P6 :=
  (C.β4 ⟨_, C.conj_mem_UH (C.hL1K hgL) (S.v2_mem_UH H)⟩ : ↥W4)

variable (C : S.Ctx76 H K (FFModel.altDn 6)) {g : ↥(Subgroup.normalizer (V : Set G))}
  (hgL : (g : G) ∈ S.L1) (hg : S.frame.ρ g = swap 0 1 * swap 1 2)
include C

include hg in
theorem good : A6L76E.Good C.x0 (C.y0 hgL) := by
  refine ⟨(C.β4 _).2, (C.β4 _).2, fun h => C.βU_v2_ne_one ((C.β4_eq_one_iff _).1
    (Subtype.ext h)), fun h => C.βU_v2g_ne_one hgL ((C.β4_eq_one_iff _).1 (Subtype.ext h)),
    fun h => C.βU_v2_ne_v2g hgL hg (modW4Equiv.injective (Subtype.ext h))⟩

include hg in
theorem in3_of_V3 {u : G} (hu3 : u ∈ S.V3) (huU : u ∈ conjClosure S.V3 H)
    (h1 : C.βU ⟨u, huU⟩ ≠ 1) : A6L76E.In3 C.x0 (C.y0 hgL) (C.β4 ⟨u, huU⟩ : ↥W4) := by
  rcases C.classes_V3_gen hgL hg hu3 huU with h | h | h | h
  · exact absurd h h1
  · left
    rw [β4_apply, h]
    rfl
  · right; left
    rw [β4_apply, h]
    rfl
  · right; right
    rw [β4_apply, h, map_mul]
    rfl

include hg in
theorem mem_stabW {t : ↥K} (htT : (t : G) ∈ T) :
    A6L76C.permOf (C.α t) ∈ A6L76E.stabW (C.good hgL hg) := by
  have key : ∀ (w : G) (hw3 : w ∈ S.V3) (hwU : w ∈ conjClosure S.V3 H), C.βU ⟨w, hwU⟩ ≠ 1 →
      A6L76E.In3 C.x0 (C.y0 hgL) (act4f (A6L76C.permOf (C.α t)) (C.β4 ⟨w, hwU⟩ : ↥W4)) := by
    intro w hw3 hwU hw1
    have e : act4f (A6L76C.permOf (C.α t)) (C.β4 ⟨w, hwU⟩ : ↥W4) =
        (C.β4 ⟨_, C.conj_mem_UH t.2 hwU⟩ : ↥W4) := by
      rw [C.β4_equiv t ⟨w, hwU⟩ (C.conj_mem_UH t.2 hwU)]
      rfl
    rw [e]
    refine C.in3_of_V3 hgL hg
      ((Subgroup.mem_normalizer_iff.mp (S.T_le_normalizer_V3 htT) w).mp hw3) _ fun h => ?_
    exact hw1 (C.βU_eq_one_of_conj t.2 hwU h)
  exact ⟨⟨key _ S.v2_mem_V3 _ C.βU_v2_ne_one, key _ (S.conj_v2_mem_V3 hg) _
    (C.βU_v2g_ne_one hgL)⟩, A6L76C.permOf_sign _⟩

include hg in
theorem eight_dvd_stab : 8 ∣ A6L76E.stabCard C.x0 (C.y0 hgL) := by
  have hTs : IsSylowTwoOf T H := isSylowTwoOf_of_quasithinIsSylowTwo S.h13.sylow C.hTH
  have hKn : (K.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer C.hKH).mpr C.hHK
  have hTK : IsSylowTwoOf (T ⊓ K) K :=
    CFSG.QuasithinUnique.RankOneRecog.isSylowTwoOf_inf_of_subnormal hTs C.hKH hKn.isSubnormal
  set Dα : Subgroup (FFModel.altDn 6).Gam := ((T ⊓ K).subgroupOf K).map C.α with hDα
  have hodd : ¬ 2 ∣ Dα.index := fun h => hTK.2.2 (h.trans (Subgroup.index_map_dvd _ C.α_surj))
  have hcard : Nat.card Dα * Dα.index = 360 := by
    rw [Subgroup.card_mul_index]
    exact A6L76K.card_alt6
  have hcop : Nat.Coprime (2 ^ 3) Dα.index :=
    Nat.Coprime.pow_left 3
      (Nat.coprime_two_left.mpr (Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hodd)))
  have h8 : 2 ^ 3 ∣ Nat.card Dα := hcop.dvd_of_dvd_mul_right (by rw [hcard]; norm_num)
  have hle : Dα.map (A6L76J.permHom 6) ≤ A6L76E.stabW (C.good hgL hg) := by
    rintro _ ⟨_, ⟨t, ht, rfl⟩, rfl⟩
    exact C.mem_stabW hgL hg (Subgroup.mem_subgroupOf.1 ht).1
  have hinj : Nat.card (Dα.map (A6L76J.permHom 6)) = Nat.card Dα :=
    Subgroup.card_map_of_injective fun _ _ h => Subtype.ext h
  have h8' : 2 ^ 3 ∣ Nat.card (Dα.map (A6L76J.permHom 6)) := by
    rw [hinj]
    exact h8
  rw [← A6L76E.card_stabW (C.good hgL hg)]
  exact h8'.trans (Subgroup.card_dvd_of_le hle)

include hg in
theorem exists_normal6 :
    ∃ C' : S.Ctx76 H K (FFModel.altDn 6), C'.x0 = e0123 ∧ A6L76E.InL0 (C'.y0 hgL) := by
  obtain ⟨h1, h2⟩ := A6L76E.syn6 _ _ (C.good hgL hg) (C.eight_dvd_stab hgL hg)
  refine ⟨C.twist (A6L76E.tau6 C.x0 (C.y0 hgL)),
    (congrArg Subtype.val (C.twist_β4 _ _)).trans h1, ?_⟩
  have e := congrArg Subtype.val (C.twist_β4 (A6L76E.tau6 C.x0 (C.y0 hgL))
    ⟨_, C.conj_mem_UH (C.hL1K hgL) (S.v2_mem_UH H)⟩)
  show A6L76E.InL0 (((C.twist _).β4 ⟨_, C.conj_mem_UH (C.hL1K hgL) (S.v2_mem_UH H)⟩ : ↥W4) : P6)
  rw [e]
  exact h2

variable (hx0 : C.x0 = e0123) (hy0 : A6L76E.InL0 (C.y0 hgL))
include hx0 hy0

include hg in
theorem inL0_of_V3 {u : G} (hu3 : u ∈ S.V3) (huU : u ∈ conjClosure S.V3 H)
    (h1 : C.βU ⟨u, huU⟩ ≠ 1) : A6L76E.InL0 (C.β4 ⟨u, huU⟩ : ↥W4) := by
  obtain ⟨hmul, -, -, -⟩ := A6L76E.L0_facts
  have hx : A6L76E.InL0 C.x0 := by rw [hx0]; exact Or.inr (Or.inr rfl)
  rcases C.in3_of_V3 hgL hg hu3 huU h1 with h | h | h
  · rw [h]; exact hx
  · rw [h]; exact hy0
  · rw [h]; exact hmul _ _ hx hy0 (C.good hgL hg).2.2.2.2

include hg in
theorem presL0_of_conj {x : G} (hxK : x ∈ K) (hxN : ∀ v ∈ S.V3, x * v * x⁻¹ ∈ S.V3) :
    A6L76E.PresL0 (A6L76C.permOf (C.α ⟨x, hxK⟩)) := by
  have key : ∀ (w : G) (hw3 : w ∈ S.V3) (hwU : w ∈ conjClosure S.V3 H), C.βU ⟨w, hwU⟩ ≠ 1 →
      A6L76E.InL0 (act4f (A6L76C.permOf (C.α ⟨x, hxK⟩)) (C.β4 ⟨w, hwU⟩ : ↥W4)) := by
    intro w hw3 hwU hw1
    have e : act4f (A6L76C.permOf (C.α ⟨x, hxK⟩)) (C.β4 ⟨w, hwU⟩ : ↥W4) =
        (C.β4 ⟨_, C.conj_mem_UH hxK hwU⟩ : ↥W4) := by
      rw [C.β4_equiv ⟨x, hxK⟩ ⟨w, hwU⟩ (C.conj_mem_UH hxK hwU)]
      rfl
    rw [e]
    exact C.inL0_of_V3 hgL hg hx0 hy0 (hxN w hw3) _ fun h => hw1 (C.βU_eq_one_of_conj hxK hwU h)
  have hy1 := key _ (S.conj_v2_mem_V3 hg) _ (C.βU_v2g_ne_one hgL)
  have hxy1 := key _ (S.V3.mul_mem S.v2_mem_V3 (S.conj_v2_mem_V3 hg)) _
    (C.βU_v2_mul_ne_one hgL hg)
  have hxy : (C.β4 ⟨S.v2 * ((g : G) * S.v2 * (g : G)⁻¹), (conjClosure S.V3 H).mul_mem
      (S.v2_mem_UH H) (C.conj_mem_UH (C.hL1K hgL) (S.v2_mem_UH H))⟩ : ↥W4) =
      e0123 * C.y0 hgL := by
    rw [← hx0, show (⟨S.v2 * ((g : G) * S.v2 * (g : G)⁻¹), (conjClosure S.V3 H).mul_mem
      (S.v2_mem_UH H) (C.conj_mem_UH (C.hL1K hgL) (S.v2_mem_UH H))⟩ : ↥(conjClosure S.V3 H)) =
      ⟨S.v2, S.v2_mem_UH H⟩ * ⟨_, C.conj_mem_UH (C.hL1K hgL) (S.v2_mem_UH H)⟩ from rfl,
      map_mul]
    rfl
  rw [hxy] at hxy1
  have hne : C.y0 hgL ≠ e0123 := fun h => (C.good hgL hg).2.2.2.2 (hx0.trans h.symm)
  rcases A6L76K.L0_pts _ hy0 hne with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · refine ⟨?_, ?_⟩
    · rw [← h1]; exact hy1
    · rw [← h2]; exact hxy1
  · refine ⟨?_, ?_⟩
    · rw [← h2]; exact hxy1
    · rw [← h1]; exact hy1

include hg in
theorem not_hat_of_six : ¬ IsHatA6 L := by
  intro hhat
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h1 := S.two_le_pRank_L1_of_hat hhat
  have hX : (S.L1.subgroupOf K).map K.subtype = S.L1 := by
    rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left C.hL1K]
  have h2 := A6L76B.pRank_map_le (p := 3) K.subtype
    (by rw [Subgroup.ker_subtype, Subgroup.card_bot]; norm_num) (S.L1.subgroupOf K)
  rw [hX] at h2
  have h3 := A6L76F.pRank_le_map_of_not_dvd C.α C.not_three_dvd_ker (S.L1.subgroupOf K)
  have h4 := A6L76F.pRank_le_map_of_not_dvd (A6L76J.permHom 6)
    (A6L76K.not_three_dvd_permHom_ker 6) ((S.L1.subgroupOf K).map C.α)
  have hle : ((S.L1.subgroupOf K).map C.α).map (A6L76J.permHom 6) ≤ A6L76E.stabL0 := by
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    have hxL : (x : G) ∈ S.L1 := Subgroup.mem_subgroupOf.1 hx
    exact ⟨C.presL0_of_conj hgL hg hx0 hy0 x.2 fun v hv => conj_V3_of_L1 hxL hv,
      A6L76C.permOf_sign _⟩
  have h5 := CFSG.SectionRank.pRank_mono (p := 3) (by norm_num) hle
  have h6 := A6L76E.pRank_stabL0_le_one
  omega

include hg in
theorem fpf_of_six :
    ∀ c ∈ S.L1, c ^ 3 = 1 → c ∉ pCoreOf 2 S.L1 → ∀ u ∈ conjClosure S.V3 H,
      (∀ k ∈ K, k * (c * u * c⁻¹ * u⁻¹) * k⁻¹ * (c * u * c⁻¹ * u⁻¹)⁻¹ ∈ fsuV1 T V) →
      ∀ k ∈ K, k * u * k⁻¹ * u⁻¹ ∈ fsuV1 T V := by
  intro c hcL hc3 hcO u huU hcu
  have hhat := C.not_hat_of_six hgL hg hx0 hy0
  have hcK : c ∈ K := C.hL1K hcL
  set γ := A6L76C.permOf (C.α ⟨c, hcK⟩) with hγ
  have hpres : A6L76E.PresL0 γ :=
    C.presL0_of_conj hgL hg hx0 hy0 hcK fun v hv => conj_V3_of_L1 hcL hv
  have hγ3 : γ ^ 3 = 1 := C.permOf_α_pow hcK hc3
  have hact : ∀ (w : G) (hwU : w ∈ conjClosure S.V3 H),
      act4f γ (C.β4 ⟨w, hwU⟩ : ↥W4) = (C.β4 ⟨_, C.conj_mem_UH hcK hwU⟩ : ↥W4) := by
    intro w hwU
    rw [C.β4_equiv ⟨c, hcK⟩ ⟨w, hwU⟩ (C.conj_mem_UH hcK hwU)]
    rfl
  have hmove : act4f γ e0123 ≠ e0123 := by
    intro hfix
    obtain ⟨h02, h13⟩ := A6L76K.fix_L0 γ hγ3 hpres hfix
    apply S.not_trivV3 hhat hcL hcO
    intro v hv
    have hvU : v ∈ conjClosure S.V3 H := le_conjClosure _ _ hv
    have hcvU : c * v * c⁻¹ * v⁻¹ ∈ conjClosure S.V3 H :=
      (conjClosure S.V3 H).mul_mem (C.conj_mem_UH hcK hvU) ((conjClosure S.V3 H).inv_mem hvU)
    refine C.mem_V1_of_βU (S.V3.mul_mem (conj_V3_of_L1 hcL hv) (S.V3.inv_mem hv)) hcvU ?_
    have hfixv : C.β4 ⟨_, C.conj_mem_UH hcK hvU⟩ = C.β4 ⟨v, hvU⟩ := by
      apply Subtype.ext
      rw [← hact v hvU]
      by_cases hv1 : C.βU ⟨v, hvU⟩ = 1
      · rw [(C.β4_eq_one_iff _).2 hv1]
        exact congrArg Subtype.val (map_one (act4 γ))
      · rcases C.inL0_of_V3 hgL hg hx0 hy0 hv hvU hv1 with h | h | h
        · rw [h, h02]
        · rw [h, h13]
        · rw [h, hfix]
    have e : (⟨c * v * c⁻¹ * v⁻¹, hcvU⟩ : ↥(conjClosure S.V3 H)) =
        ⟨_, C.conj_mem_UH hcK hvU⟩ * (⟨v, hvU⟩)⁻¹ := rfl
    rw [← C.β4_eq_one_iff, e, map_mul, map_inv, hfixv, mul_inv_cancel]
  have hfpf := A6L76E.fpf6 γ (A6L76C.permOf_sign _) hγ3 hpres.1 hpres.2 hmove
  have hcuU : c * u * c⁻¹ * u⁻¹ ∈ conjClosure S.V3 H :=
    (conjClosure S.V3 H).mul_mem (C.conj_mem_UH hcK huU) ((conjClosure S.V3 H).inv_mem huU)
  have h1 : C.βU ⟨_, hcuU⟩ = 1 := (C.βU_eq_one_iff _).2 hcu
  have h2 : C.β4 ⟨_, C.conj_mem_UH hcK huU⟩ = C.β4 ⟨u, huU⟩ := by
    have e : (⟨_, C.conj_mem_UH hcK huU⟩ : ↥(conjClosure S.V3 H)) = ⟨_, hcuU⟩ * ⟨u, huU⟩ :=
      Subtype.ext (inv_mul_cancel_right _ _).symm
    rw [e, map_mul, (C.β4_eq_one_iff _).2 h1, one_mul]
  have h3 := hfpf _ (C.β4 ⟨u, huU⟩).2 ((hact u huU).trans (congrArg Subtype.val h2))
  exact (C.βU_eq_one_iff _).1 ((C.β4_eq_one_iff _).1 (Subtype.ext h3))

omit hy0 in
theorem βU_v2_six :
    C.βU ⟨S.v2, S.v2_mem_UH H⟩ = QuotientGroup.mk ⟨_, A6L76K.e0123_facts.2⟩ := by
  apply modW4Equiv.injective
  rw [modW4Equiv_mk]
  apply Subtype.ext
  exact hx0.trans A6L76K.e0123_facts.1.symm

end Ctx76

namespace Ctx76

variable {H K : Subgroup G} [IsMulCommutative ↥(conjClosure S.V3 H)]

theorem six (C : S.Ctx76 H K (FFModel.altDn 6)) :
    ¬ IsHatA6 L ∧
      (∀ c ∈ S.L1, c ^ 3 = 1 → c ∉ pCoreOf 2 S.L1 → ∀ u ∈ conjClosure S.V3 H,
        (∀ k ∈ K, k * (c * u * c⁻¹ * u⁻¹) * k⁻¹ * (c * u * c⁻¹ * u⁻¹)⁻¹ ∈ fsuV1 T V) →
        ∀ k ∈ K, k * u * k⁻¹ * u⁻¹ ∈ fsuV1 T V) ∧
      ∃ (π : (FFModel.altDn 6).Gam →* ↥(autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))))
        (β : ↥(commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))) →*
          ↥(FFModel.altDn 6).sec ⧸ (FFModel.altDn 6).ker.subgroupOf (FFModel.altDn 6).sec),
        CFSG.Quasithin.H.Mathieu.RealizesBy (FFModel.altDn 6)
          (autSec (autOn K (conjClosure S.V3 H)) ⊤
            ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))
          (commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
            ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))))
          (fixV (autSec (autOn K (conjClosure S.V3 H)) ⊤
              ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) ⊓
            commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
              ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))) π β ∧
        A6L76.MapsOnto β ((S.V2.subgroupOf (conjClosure S.V3 H)).map
            (InternalSec.secMk ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))))
          ([1, A6L76.vecS 6 {0, 1, 2, 3}] : List (FFModel.altDn 6).Amb) := by
  obtain ⟨g, hgL, hg⟩ := S.exists_g012
  obtain ⟨C', hx0, hy0⟩ := C.exists_normal6 hgL hg
  exact ⟨C'.not_hat_of_six hgL hg hx0 hy0, C'.fpf_of_six hgL hg hx0 hy0, C'.π, C'.β, C'.hR,
    C'.mapsOnto_V2_gen _ (C'.βU_v2_six hx0)⟩

end Ctx76

end Setting4

end CFSG.Quasithin.H13.A6
