module

public import CFSG.Quasithin.H13.L32A72e
public import CFSG.Quasithin.H13.L32A72d
public import CFSG.Quasithin.H13.L32ASecMod

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped IsMulCommutative Pointwise

variable {G : Type} [Group G] [Finite G]

namespace Ctx72

variable {T L V : Subgroup G} {l₀ : G} (C : Ctx72 G T L V l₀)
include C

theorem exists_st (hu0 : u0 T V = fsuV1 T V) (h65 : H6.VolI_H_6_5) (h71 : Lemma14_7_71) :
    ∃ (θ : ↥L →* H6.Γ) (m : G), Function.Surjective θ ∧
      (∀ l : ↥L, θ l = 1 ↔ (l : G) ∈ Subgroup.centralizer (V : Set G)) ∧
      IsPGroup 2 ↥((H6.borel.comap θ).map L.subtype) ∧
      m ∈ fsuU T V ∧ m ∉ V ∧
      (∀ l : ↥L, θ l ∈ H6.borel → (l : G) * m * (l : G)⁻¹ * m⁻¹ ∈ V) ∧
      (∀ s ∈ sL T L V, s ∈ Subgroup.closure
        ({y | ∃ l : ↥L, (l : G) * m * (l : G)⁻¹ = y} ∪ (V : Set G))) ∧
      ∃ χ : ↥(sL T L V) →* Multiplicative (Matrix (Fin 3) (Fin 3) (ZMod 2)),
        χ.ker = V.subgroupOf (sL T L V) ∧
        (∀ s, RuType.IsTraceZero (Multiplicative.toAdd (χ s))) ∧
        (∀ A, RuType.IsTraceZero A → ∃ s, χ s = Multiplicative.ofAdd A) ∧
        ∀ (l : ↥L) (s t : ↥(sL T L V)), (t : G) = l * s * (l : G)⁻¹ →
          χ t = Multiplicative.ofAdd (RuType.stAct (θ l) (Multiplicative.toAdd (χ s))) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hV8, hLTV, hV1, -⟩ := C.hMod G T L V C.hyp.hyp C.hyp.fsu
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := le_sup_left.trans hLTV
  have h1281 := C.hyp.hyp1281One C.h13322 C.hMod
  obtain ⟨hcard, hsq, -⟩ := h1281.card_sq
  have : IsMulCommutative ↥V := (C.hMod G T L V C.hyp.hyp C.hyp.fsu).1.1
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
  have hθs : Function.Surjective θ := theta1_surjective hLV e A hρs
  have hθ1 : ∀ l : ↥L, θ l = 1 ↔ (l : G) ∈ Subgroup.centralizer (V : Set G) :=
    theta1_eq_one_iff hLV e A
  have hθLl : ∀ l : ↥L, θ l ∈ H6.Ll ↔ (l : G) ∈ Subgroup.normalizer (fsuV1 T V : Set G) :=
    fun l => (theta1_mem_Ll_iff hLV e A hzV hA l).trans
      (mem_normalizer_iff_of_gen hzV1 hz1 hgen).symm
  have hNU := inf_normalizer_fsuU C.setting C.hF C.h13322 C.hMod
  have hLlU : ∀ l : ↥L, θ l ∈ H6.Ll → (l : G) ∈ Subgroup.normalizer (fsuU T V : Set G) := by
    intro l hl
    have h1 : (l : G) ∈ L ⊓ Subgroup.normalizer (fsuU T V : Set G) := by
      rw [hNU]
      exact Subgroup.mem_inf.mpr ⟨l.2, (hθLl l).mp hl⟩
    exact (Subgroup.mem_inf.mp h1).2
  obtain ⟨V₂, hV2⟩ := C.hyp.exists_V2 C.h13322 C.hMod C.h1222
  have S14 := C.hyp.set14 C.h1222 C.h1332 C.h1334 hV2
  set B : Subgroup G := (H6.borel.comap θ).map L.subtype with hB
  have hBmem : ∀ {b : G}, b ∈ B → ∃ l : ↥L, θ l ∈ H6.borel ∧ (l : G) = b := by
    intro b hb
    obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.mp hb
    exact ⟨l, hl, rfl⟩
  have hBp : IsPGroup 2 ↥B := by
    rintro ⟨b, hb⟩
    obtain ⟨l, hl, rfl⟩ := hBmem hb
    have h4 : θ (l ^ 4) = 1 := by
      rw [map_pow]
      exact borel_pow_four _ hl
    have hc : ((l ^ 4 : ↥L) : G) ∈ (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) :=
      Subgroup.mem_inf.mpr ⟨Subgroup.mem_sup_left (l ^ 4).2, (hθ1 _).mp h4⟩
    obtain ⟨k, hk⟩ := S14.isPGroup_cent_sup ⟨_, hc⟩
    refine ⟨k + 2, Subtype.ext ?_⟩
    have hk' := congrArg Subtype.val hk
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at hk' ⊢
    rw [show 2 ^ (k + 2) = 4 * 2 ^ k by ring, pow_mul]
    exact hk'
  have hBU : B ≤ Subgroup.normalizer (fsuU T V : Set G) := by
    intro b hb
    obtain ⟨l, hl, rfl⟩ := hBmem hb
    exact hLlU l (Subgroup.mem_inf.mp hl).2
  have hBV : B ≤ Subgroup.normalizer (V : Set G) := by
    intro b hb
    obtain ⟨l, -, rfl⟩ := hBmem hb
    exact hLV l.2
  have hUe := isElemAbelian_fsuU_of C.hyp C.hMod
  have hUp : IsPGroup 2 ↥(fsuU T V) := fun u => ⟨1, Subtype.ext (by
    simpa using F7.isElemAbelian_pow_eq_one hUe u.2)⟩
  have hUV : fsuU T V ≤ Subgroup.normalizer (V : Set G) :=
    le_normalizer_of_conj_mem' fun u hu v hv => by
      rw [F7.isElemAbelian_comm hUe hu (v_le_fsuU hv), mul_inv_cancel_right]
      exact hv
  have hne : V ≠ fsuU T V := by
    obtain ⟨u, hu, huV⟩ := C.exists_mem_fsuU hu0
    exact fun h => huV (h ▸ hu)
  obtain ⟨m, hmU, hmV, hmB⟩ := exists_mem_fix_mod v_le_fsuU hne hBp hUp hBU hBV hUV
  have hmT : ∀ l : ↥L, θ l ∈ H6.borel → (l : G) * m * (l : G)⁻¹ * m⁻¹ ∈ V := fun l hl =>
    hmB l (Subgroup.mem_map.mpr ⟨l, hl, rfl⟩)
  obtain ⟨x, hxL1, hx3, hx1, hxV⟩ := C.exists_x3
  have hxL : x ∈ L := (L32NSet14.Setting.L1_le.trans inf_le_left) hxL1
  have hxN1 : x ∈ Subgroup.normalizer (fsuV1 T V : Set G) :=
    (Subgroup.mem_inf.mp (L32NSet14.Setting.L1_le hxL1)).2
  have hgen : ∀ s ∈ sL T L V, s ∈ Subgroup.closure
      ({y | ∃ l : ↥L, (l : G) * m * (l : G)⁻¹ = y} ∪ (V : Set G)) := by
    have hDL : ∀ l ∈ L, ∀ d ∈ Subgroup.closure
        ({y | ∃ l : ↥L, (l : G) * m * (l : G)⁻¹ = y} ∪ (V : Set G)),
        l * d * l⁻¹ ∈ Subgroup.closure
          ({y | ∃ l : ↥L, (l : G) * m * (l : G)⁻¹ = y} ∪ (V : Set G)) := by
      intro l hl d hd
      induction hd using Subgroup.closure_induction with
      | mem y hy =>
        rcases hy with ⟨k, rfl⟩ | hyV
        · refine Subgroup.subset_closure (Or.inl ⟨⟨l, hl⟩ * k, ?_⟩)
          simp only [Subgroup.coe_mul]
          group
        · exact Subgroup.subset_closure
            (Or.inr ((Subgroup.mem_normalizer_iff.mp (hLV hl) y).mp hyV))
      | one => simp
      | mul a b _ _ iha ihb =>
        rw [show l * (a * b) * l⁻¹ = (l * a * l⁻¹) * (l * b * l⁻¹) by group]
        exact mul_mem iha ihb
      | inv a _ iha =>
        rw [show l * a⁻¹ * l⁻¹ = (l * a * l⁻¹)⁻¹ by group]
        exact inv_mem iha
    have hUD := C.fsuU_le_of_mem hu0 (D := Subgroup.closure
        ({y | ∃ l : ↥L, (l : G) * m * (l : G)⁻¹ = y} ∪ (V : Set G)))
      (fun v hv => Subgroup.subset_closure (Or.inr hv)) hmU hmV
      (Subgroup.subset_closure (Or.inl ⟨1, by simp⟩)) hxL1 hx3 hx1
      (Subgroup.subset_closure (Or.inl ⟨⟨x, hxL⟩, rfl⟩))
    exact fun s hs => conjClosure_le (fun l hl u hu => hDL l hl u (hUD hu)) hs
  have hW : V.relIndex (Subgroup.closure
      ({y | ∃ l : ↥L, θ l ∈ H6.Ll ∧ (l : G) * m * (l : G)⁻¹ = y} ∪ (V : Set G))) = 4 := by
    have hWU : Subgroup.closure
        ({y | ∃ l : ↥L, θ l ∈ H6.Ll ∧ (l : G) * m * (l : G)⁻¹ = y} ∪ (V : Set G)) ≤
        fsuU T V := by
      rw [Subgroup.closure_le]
      rintro _ (⟨l, hl, rfl⟩ | hyV)
      · exact (Subgroup.mem_normalizer_iff.mp (hLlU l hl) m).mp hmU
      · exact v_le_fsuU hyV
    have hUW := C.fsuU_le_of_mem hu0 (D := Subgroup.closure
        ({y | ∃ l : ↥L, θ l ∈ H6.Ll ∧ (l : G) * m * (l : G)⁻¹ = y} ∪ (V : Set G)))
      (fun v hv => Subgroup.subset_closure (Or.inr hv)) hmU hmV
      (Subgroup.subset_closure (Or.inl ⟨1, by rw [map_one]; exact one_mem _, by simp⟩))
      hxL1 hx3 hx1 (Subgroup.subset_closure (Or.inl ⟨⟨x, hxL⟩, (hθLl _).mpr hxN1, rfl⟩))
    rw [le_antisymm hWU hUW]
    exact C.relIndex_v hu0
  obtain ⟨Cx, hCx⟩ : ∃ Cx : Subgroup G, Cx = Subgroup.centralizer ({x} : Set G) ⊓ sL T L V :=
    ⟨_, rfl⟩
  have hCxS : Cx ≤ sL T L V := hCx ▸ inf_le_right
  have hCxV : Cx ≤ Subgroup.normalizer (V : Set G) := hCxS.trans C.sL_le_normalizer
  have hVS : V ≤ sL T L V := v_le_fsuU.trans (le_conjClosure _ _)
  have hVc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb =>
    F7.isElemAbelian_comm hUe (v_le_fsuU ha) (v_le_fsuU hb)
  have hV2 : ∀ a ∈ V, a * a = 1 := fun a ha => by
    rw [← pow_two]
    exact F7.isElemAbelian_pow_eq_one hUe (v_le_fsuU ha)
  have hC : ∀ s, s ∈ Cx ⊔ V ↔ s ∈ sL T L V ∧ x * s * x⁻¹ * s⁻¹ ∈ V := by
    intro s
    constructor
    · intro hs
      have hs' : s ∈ ((Cx : Set G) * (V : Set G)) := by
        rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hCxV]
        exact hs
      obtain ⟨c, hc, v, hv, rfl⟩ := hs'
      obtain ⟨hcx, hcS⟩ := Subgroup.mem_inf.mp (hCx ▸ hc)
      refine ⟨mul_mem hcS (hVS hv), ?_⟩
      have hxc : x * c * x⁻¹ = c := by
        rw [Subgroup.mem_centralizer_singleton_iff] at hcx
        rw [← hcx, mul_inv_cancel_right]
      have hxv : x * v * x⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp (hLV hxL) v).mp hv
      rw [show x * (c * v) * x⁻¹ * (c * v)⁻¹ =
        (x * c * x⁻¹) * (x * v * x⁻¹ * v⁻¹) * c⁻¹ by group, hxc]
      exact (Subgroup.mem_normalizer_iff.mp (hCxV hc) _).mp (mul_mem hxv (inv_mem hv))
    · rintro ⟨hsS, hsx⟩
      have hfix := conj_fix_of_comm_mem hx3 (hLV hxL) hVc hV2 hsx
      have haV : x * (x * s * x⁻¹ * s⁻¹) * x⁻¹ ∈ V :=
        (Subgroup.mem_normalizer_iff.mp (hLV hxL) _).mp hsx
      have hc : (x * (x * s * x⁻¹ * s⁻¹) * x⁻¹) * s ∈ Cx := by
        rw [hCx]
        refine Subgroup.mem_inf.mpr ⟨?_, mul_mem (hVS haV) hsS⟩
        rw [Subgroup.mem_centralizer_singleton_iff]
        calc (x * (x * s * x⁻¹ * s⁻¹) * x⁻¹) * s * x =
            x * ((x * (x * s * x⁻¹ * s⁻¹) * x⁻¹) * s) * x⁻¹ * x := by rw [hfix]
          _ = x * ((x * (x * s * x⁻¹ * s⁻¹) * x⁻¹) * s) := by group
      rw [show s = (x * (x * s * x⁻¹ * s⁻¹) * x⁻¹)⁻¹ *
        ((x * (x * s * x⁻¹ * s⁻¹) * x⁻¹) * s) by group]
      exact mul_mem (Subgroup.mem_sup_right (inv_mem haV)) (Subgroup.mem_sup_left hc)
  have hcV : Nat.card ↥(Cx ⊓ V) = 2 := by
    have heq : Cx ⊓ V = V ⊓ Subgroup.centralizer ({x} : Set G) := by
      ext w
      rw [hCx]
      simp only [Subgroup.mem_inf]
      exact ⟨fun ⟨⟨h1, _⟩, h3⟩ => ⟨h3, h1⟩, fun ⟨h3, h1⟩ => ⟨⟨h1, hVS h3⟩, h3⟩⟩
    rw [heq]
    exact card_inf_centralizer_eq_two hLV e hxL hx3 hxV
  have h712 := ((h71 G T L V C.hyp).2.1 x hxL1 hx3 hx1).2
  rw [← hCx] at h712
  have hcard1 := Subgroup.relIndex_mul_card Cx (sL T L V)
  rw [inf_eq_left.mpr hCxS, h712] at hcard1
  have hcard2 := L32NSet14.card_sup_mul_card_inf hCxV
  rw [hcV, hV8] at hcard2
  have hr1 := Subgroup.relIndex_mul_card V (sL T L V)
  rw [inf_eq_left.mpr hVS, hV8] at hr1
  have hr2 := Subgroup.relIndex_mul_card V (Cx ⊔ V)
  rw [inf_eq_left.mpr le_sup_right, hV8] at hr2
  rw [show (4 : ℕ) ^ 4 = 256 by norm_num] at hcard1
  have hidx : V.relIndex (sL T L V) = 64 * V.relIndex (Cx ⊔ V) := by
    omega
  have D : SecMod L (sL T L V) V θ :=
    { le := hVS
      normX := le_normalizer_conjClosure _ _
      normY := hLV
      comm := fun a ha b hb => C.comm_mem hu0 ha hb
      sq := fun a ha => C.sq_mem hu0 ha
      surj := hθs
      ker := fun l hl s hs => C.comm_mem_of_mem_centralizer hu0 l.2 ((hθ1 l).mp hl) hs
      faithful := fun l hl => (hθ1 l).mpr (C.mem_centralizer_of_comm_mem hu0 l.2 hl) }
  have hx3' : θ ⟨x, hxL⟩ ^ 3 = 1 := by
    rw [← map_pow, show (⟨x, hxL⟩ : ↥L) ^ 3 = 1 from Subtype.ext (by simpa using hx3),
      map_one]
  have hx1' : θ ⟨x, hxL⟩ ≠ 1 := fun h => hxV ((hθ1 _).mp h)
  obtain ⟨χ, hχ⟩ := D.exists_steinberg h65 (le_conjClosure _ _ hmU) hmT hgen rfl hW hx3' hx1'
    hC hidx
  exact ⟨θ, m, hθs, hθ1, hBp, hmU, hmV, hmT, hgen, χ, hχ⟩

end Ctx72

end CFSG.Quasithin.H13.L32A
