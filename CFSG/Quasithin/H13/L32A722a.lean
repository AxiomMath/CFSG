module

public import CFSG.Quasithin.H13.L32A770e
public import CFSG.Quasithin.H13.L32A72e

public section

namespace CFSG.Quasithin.H13.S4

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open CFSG.Quasithin.H13.L32A
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G]

structure Data (T L V : Subgroup G) (θ : ↥L →* H6.Γ) (c : G) : Prop where
  surj : Function.Surjective θ
  ker : ∀ l : ↥L, θ l = 1 ↔ (l : G) ∈ Subgroup.centralizer (V : Set G)
  ll : ∀ l : ↥L, θ l ∈ H6.Ll ↔ (l : G) ∈ Subgroup.normalizer (fsuV1 T V : Set G)
  borel_two : IsPGroup 2 ↥((H6.borel.comap θ).map L.subtype)
  cent_le : L ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 (L ⊔ T)
  elem_v : IsElemAbelian 2 V
  card_v : Nat.card V = 8
  norm_v : L ⊔ T ≤ Subgroup.normalizer (V : Set G)
  card_v1 : Nat.card ↥(fsuV1 T V) = 2
  elem_u : IsElemAbelian 2 (fsuU T V)
  c_mem : c ∈ L32A.l1 T L V
  c3 : c ^ 3 = 1
  c_ne : c ≠ 1
  t_v1 : T ≤ Subgroup.normalizer (fsuV1 T V : Set G)
  mod : StmtL32NModule

namespace Data

variable {T L V : Subgroup G} {θ : ↥L →* H6.Γ} {c : G}

omit [Finite G] in
theorem l1_le (_ : Data T L V θ c) : L32A.l1 T L V ≤ L ⊓ Subgroup.normalizer (fsuV1 T V : Set G) :=
  oTwoUpper_le _

omit [Finite G] in
theorem c_L (D : Data T L V θ c) : c ∈ L := (D.l1_le D.c_mem).1

omit [Finite G] in
theorem c_N (D : Data T L V θ c) : c ∈ Subgroup.normalizer (fsuV1 T V : Set G) :=
  (D.l1_le D.c_mem).2

theorem theta_c (D : Data T L V θ c) : θ ⟨c, D.c_L⟩ ≠ 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro h
  have hcQ : c ∈ pCoreOf 2 (L ⊔ T) := D.cent_le ⟨D.c_L, (D.ker _).mp h⟩
  obtain ⟨n, hn⟩ := (pCoreOf_isPGroup 2 (L ⊔ T)) ⟨c, hcQ⟩
  have h2n : c ^ (2 ^ n) = 1 := by
    have := congrArg Subtype.val hn
    simpa using this
  have h1 : orderOf c = 1 := Nat.eq_one_of_dvd_coprimes
    (Nat.Coprime.pow_right n (by norm_num : Nat.Coprime 3 2)) (orderOf_dvd_of_pow_eq_one D.c3)
    (orderOf_dvd_of_pow_eq_one h2n)
  exact D.c_ne (orderOf_eq_one_iff.mp h1)

omit [Finite G] in
theorem theta_c3 (D : Data T L V θ c) : θ ⟨c, D.c_L⟩ ^ 3 = 1 := by
  rw [← map_pow]
  have : (⟨c, D.c_L⟩ : ↥L) ^ 3 = 1 := Subtype.ext (by simpa using D.c3)
  rw [this, map_one]

end Data

theorem exists_data (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4)
    {T L V H : Subgroup G} (S : Setting147 G T L V H) : ∃ θ c, Data T L V θ c := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h13322 := stmt13_3_2_two_of h1332
  have hMod : StmtL32NModule := stmtL32NModule_of_inputs h1332 h1334
  obtain ⟨hVe, hV8, hLTV, hV1, -⟩ := hMod G T L V S.hyp.hyp S.hyp.fsu
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := le_sup_left.trans hLTV
  have h1281 := S.hyp.hyp1281One h13322 hMod
  obtain ⟨hcard, hsq, -⟩ := h1281.card_sq
  have : IsMulCommutative ↥V := (hMod G T L V S.hyp.hyp S.hyp.fsu).1.1
  obtain ⟨e⟩ : Nonempty (↥V ≃* Multiplicative (Fin 3 → ZMod 2)) :=
    Vol2.Ch10.SecA.nonempty_mulEquiv_pi_of_sq_eq_one
      (fun x => Subtype.ext (by simpa using hsq x x.2)) hcard
  have hρs := repV_surjective hLV e (autOn_eq_top_of_hyp1281One h1281)
  obtain ⟨z, hzV1, hz1, hgen⟩ := exists_gen_of_card_two hV1
  have hzV : z ∈ V := (Subgroup.mem_inf.mp hzV1).1
  obtain ⟨A, hA⟩ := exists_sl3_e1 (Multiplicative.toAdd (e ⟨z, hzV⟩)) (by
    intro h0
    apply hz1
    have h1 : e ⟨z, hzV⟩ = 1 := by
      rw [← ofAdd_toAdd (e ⟨z, hzV⟩), h0]
      rfl
    exact congrArg Subtype.val (e.injective (h1.trans (map_one e).symm)))
  set θ := theta1 hLV e A with hθ
  have hθ1 : ∀ l : ↥L, θ l = 1 ↔ (l : G) ∈ Subgroup.centralizer (V : Set G) :=
    theta1_eq_one_iff hLV e A
  obtain ⟨V₂, hV2⟩ := S.hyp.exists_V2 h13322 hMod h1222
  have S14 := S.hyp.set14 h1222 h1332 h1334 hV2
  have hCp : IsPGroup 2 ↥((L ⊔ T) ⊓ Subgroup.centralizer (V : Set G)) := S14.isPGroup_cent_sup
  have hCQ : (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 (L ⊔ T) := by
    refine le_pCoreOf_of_le_normalizer inf_le_left (fun g hg => ?_) hCp
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have hgV := hLTV hg
    constructor
    · rintro ⟨hx1, hx2⟩
      refine ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hg hx1) (Subgroup.inv_mem _ hg),
        Subgroup.mem_centralizer_iff.mpr fun v hv => ?_⟩
      have hv' : g⁻¹ * v * g⁻¹⁻¹ ∈ V :=
        (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgV) v).mp hv
      have hc := Subgroup.mem_centralizer_iff.mp hx2 _ hv'
      calc v * (g * x * g⁻¹) = g * ((g⁻¹ * v * g⁻¹⁻¹) * x) * g⁻¹ := by group
        _ = g * (x * (g⁻¹ * v * g⁻¹⁻¹)) * g⁻¹ := by rw [hc]
        _ = g * x * g⁻¹ * v := by group
    · rintro ⟨hx1, hx2⟩
      refine ⟨?_, ?_⟩
      · have := Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hg) hx1) hg
        simpa [mul_assoc] using this
      · refine Subgroup.mem_centralizer_iff.mpr fun v hv => ?_
        have hv' : g * v * g⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hgV v).mp hv
        have hc := Subgroup.mem_centralizer_iff.mp hx2 _ hv'
        calc v * x = g⁻¹ * ((g * v * g⁻¹) * (g * x * g⁻¹)) * g := by group
          _ = g⁻¹ * ((g * x * g⁻¹) * (g * v * g⁻¹)) * g := by rw [hc]
          _ = x * v := by group
  obtain ⟨x, hxL1, hx3, hx1⟩ := exists_x3_l1 S.hyp hMod h1222 h1332 h1334
  have hxL1' : x ∈ L32A.l1 T L V := by
    rw [L32A.l1, ← oTwoRes_eq_oTwoUpper]
    exact hxL1
  refine ⟨θ, x, theta1_surjective hLV e A hρs, hθ1, fun l =>
    (theta1_mem_Ll_iff hLV e A hzV hA l).trans (mem_normalizer_iff_of_gen hzV1 hz1 hgen).symm,
    ?_, fun g hg => hCQ ⟨Subgroup.mem_sup_left hg.1, hg.2⟩, hVe, hV8, hLTV, hV1,
    isElemAbelian_fsuU_of S.hyp hMod, hxL1', hx3, hx1, (S.hyp.isTSub_V1 hMod).2.2, hMod⟩
  rintro ⟨b, hb⟩
  obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.mp hb
  have h4 : θ (l ^ 4) = 1 := by
    rw [map_pow]
    exact borel_pow_four _ hl
  have hc : ((l ^ 4 : ↥L) : G) ∈ (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) :=
    Subgroup.mem_inf.mpr ⟨Subgroup.mem_sup_left (l ^ 4).2, (hθ1 _).mp h4⟩
  obtain ⟨k, hk⟩ := hCp ⟨_, hc⟩
  refine ⟨k + 2, Subtype.ext ?_⟩
  have hk' := congrArg Subtype.val hk
  simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at hk' ⊢
  rw [show 2 ^ (k + 2) = 4 * 2 ^ k by ring, pow_mul]
  exact hk'

end CFSG.Quasithin.H13.S4
