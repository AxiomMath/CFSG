module

public import CFSG.Quasithin.H13.NQS134ES
public import CFSG.Quasithin.H13.NQS134EH
public import CFSG.Quasithin.H13.NQS134EJ
public import CFSG.Quasithin.H13.NQS134EQ

public section

namespace CFSG.Quasithin.H13.NQS134

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6 CFSG.Quasithin.H13.NQS134.End134
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

namespace Data13410

variable {S : A6.Setting134 G T L V} {z : G} {H K W : Subgroup G} [IsMulCommutative ↥W]
  (D : Data13410 S z H K W)
include D

theorem false_l32 (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2)
    (hM : normalizer (L : Set G) = L ⊔ T) (hZV1 : quasithinOmegaOneCenter T = fsuV1 T V)
    (hL1Z : L₁Of L (fsuV1 T V) ≤ centralizer (quasithinOmegaOneCenter T : Set G))
    (hL1 : L₁Of L (fsuV1 T V) ≤ K) (hZW : quasithinOmegaOneCenter T ≤ W ⊔ U3.cZ T K)
    (hcZ : U3.cZ T K = zpowers z) (hK3 : LieModel (↥K ⧸ CFSG.pCore 2 ↥K) .PSL 3 2 1)
    (hnat : BinaryNaturalSL (V := ↥W) (autOn K W) ⊤ ⊥ 3 1)
    (hCMT : normalizer (L : Set G) ⊓ centralizer (V : Set G) ≤ T)
    (huniq : ∀ z' ∈ quasithinOmegaOneCenter T, z' ≠ 1 →
      ¬ centralizer ({z'} : Set G) ≤ normalizer (L : Set G) → z' = z) : False := by
  have hz := D.zV1
  have hzL := D.zL
  have hTZ : T ≤ centralizer (quasithinOmegaOneCenter T : Set G) :=
    le_centralizer_iff.mp ((U3.s134_Z_le_center T).trans inf_le_right)
  obtain ⟨C₀⟩ := exists_l3Coords hnat
  obtain ⟨C, hCB⟩ := C₀.exists_conj_eq D.Wirr.2.2.1 (S.h13.sylow.1.to_le inf_le_left)
  have hZK := center_eq_bot_of_simple_types (Or.inr (Or.inl hK3))
  have hCKTT := D.inf_centralizer_le_T hZK
  have hCKT : K ⊓ centralizer (W : Set G) ≤ T :=
    (inf_le_inf_right (centralizer (W : Set G)) (le_sup_left : K ≤ K ⊔ T)).trans hCKTT
  obtain ⟨DP, hB⟩ := l32_parData C hCB D.Wirr.2.2.1 D.T_le_K D.isSylowTwoOf_inf hCKT
    (sup_le_sup_right hL1 T) (centralizer_Z_le_L1T S hM hZV1) (sup_le hL1Z hTZ)
    D.mem_Z_of_mem_centralizer_T (D.mem_centralizer_Z_of_fix hZW) D.Wirr.2.1 S.h13.sylow.1
    D.TW D.W_le_T
  have hTB' : ∀ t : ↥(normalizer (W : Set G)), (t : G) ∈ T → C.ρ t ∈ l3Blist := by
    intro t ht
    refine l3B_self_normalizing _ fun b hb => ?_
    obtain ⟨s, hs, rfl⟩ := hB b hb
    have h1 : (t : G) * s * (t : G)⁻¹ ∈ T := mul_mem (mul_mem ht (mem_inf.1 hs).1) (inv_mem ht)
    have h2 : (t : G) * s * (t : G)⁻¹ ∈ K :=
      (mem_normalizer_iff.mp (D.T_le_K ht) s).mp (mem_inf.1 hs).2
    have := hCB (t * s * t⁻¹) (mem_inf.2 ⟨h1, h2⟩)
    rwa [map_mul, map_mul, map_inv] at this
  have hTY : ∀ t : ↥(normalizer (W : Set G)), (t : G) ∈ T → ∀ γ ∈ l3P2,
      C.ρ t * γ * (C.ρ t)⁻¹ ∈ l3P2 := by
    intro t ht γ hγ
    have htP : C.ρ t ∈ l3P2 := l3B_le_P2 _ (hTB' t ht)
    exact mul_mem (mul_mem htP hγ) (inv_mem htP)
  obtain ⟨g₀, hg₀, b₀, hb₀, hgb₀⟩ := exists_l3P2_conj
  obtain ⟨hstar, hPKT, -, -, hcl, hinc1, -⟩ := D.h2_of_parData hM hZV1 DP le_top hCB hB
    (fun Y hY _ => l3_overgroups hY) (fun x hx => l3B_le_P2 x hx) le_top l3P2_not_le
    l3Stab_not_le_P2 hTY l3B_relIndex_P2 (mem_l3P2.2 hg₀) hb₀ hgb₀
  set P := DP.parOf l3P2 with hPdef
  have hW2 : ∀ x ∈ W, x * x = 1 := fun x hx => by rw [← pow_two]; exact D.sq_eq_one hx
  have hinj : ∀ {x y : G} (hx : x ∈ W) (hy : y ∈ W), C.c ⟨x, hx⟩ = C.c ⟨y, hy⟩ → x = y :=
    fun hx hy h => congrArg Subtype.val (C.c_inj h)
  have hc0 : ∀ {x : G} (hx : x ∈ W), C.c ⟨x, hx⟩ = 0 → x = 1 := fun hx h =>
    hinj hx (one_mem W) (h.trans C.c_one.symm)
  have hzW : z ∉ W := by
    intro h
    have hfix : ∀ γ : L3.Γ, L3.act γ (C.c ⟨z, h⟩) = C.c ⟨z, h⟩ := by
      intro γ
      obtain ⟨g, hgK, rfl⟩ := C.image_K γ
      refine (C.fix_iff g ⟨z, h⟩).1 ?_
      show (g : G) * z * (g : G)⁻¹ = z
      rw [mem_centralizer_singleton_iff.1 (D.Kz hgK), mul_inv_cancel_right]
    exact D.z_ne_one (hc0 h (l3_fix_all _ hfix))
  have hzz : z * z = 1 := by rw [← pow_two]; exact D.z_sq
  have hzVZ := U3.s134_zV_mem_Z S
  have hzT : z ∈ T := (U3.s134_Z_le_center T hz.2).1
  have hzCT : z ∈ centralizer (T : Set G) := (U3.s134_Z_le_center T hz.2).2
  have hzVCT : S.zV ∈ centralizer (T : Set G) := (U3.s134_Z_le_center T hzVZ).2
  have hzVz : S.zV * z = z * S.zV :=
    mem_centralizer_iff.1 hzCT _ (U3.s134_Z_le_center T hzVZ).1
  obtain ⟨w₀, hw₀W, hw₀c⟩ : ∃ w₀ ∈ W, w₀ = S.zV ∨ w₀ = z * S.zV := by
    have h1 := hZW hzVZ
    rw [hcZ] at h1
    rcases mem_W_or_mul (D.TW hzT) hzz h1 with h | h
    · exact ⟨_, h, Or.inl rfl⟩
    · exact ⟨_, h, Or.inr hzVz⟩
  have hw₀CT : w₀ ∈ centralizer (T : Set G) := by
    rcases hw₀c with rfl | rfl
    · exact hzVCT
    · exact mul_mem hzCT hzVCT
  have hw₀V : w₀ ∈ V := by
    rcases hw₀c with rfl | rfl
    · exact S.zV_mem_V
    · exact mul_mem hz.1 S.zV_mem_V
  obtain ⟨h6', h4'⟩ := wtP_ne_of_zV S hz hzL
  have hw₀1 : w₀ ≠ 1 := by
    rcases hw₀c with rfl | rfl
    · exact S.zV_ne_one
    · exact mul_zV_ne_one S hzL
  have hw₀w : wtP (S.frame.ψ ⟨w₀, hw₀V⟩ : P6) ≠ wtP (S.frame.ψ ⟨z, hz.1⟩ : P6) := by
    rcases hw₀c with rfl | rfl
    · exact h6'
    · exact h4'
  have hcw₀ : C.c ⟨w₀, hw₀W⟩ = l3e1 := by
    refine l3_fixB _ (fun h => hw₀1 (hc0 hw₀W h)) fun β hβ => ?_
    obtain ⟨g, hg, rfl⟩ := hB β hβ
    refine (C.fix_iff g ⟨w₀, hw₀W⟩).1 ?_
    show (g : G) * w₀ * (g : G)⁻¹ = w₀
    rw [mem_centralizer_iff.1 hw₀CT g (mem_inf.1 hg).1, mul_inv_cancel_right]
  have hsurj : ∀ p : L3.Vec, ∃ (w : G) (hw : w ∈ W), C.c ⟨w, hw⟩ = p := by
    intro p
    by_cases hp : p = 0
    · exact ⟨1, one_mem W, C.c_one.trans hp.symm⟩
    · obtain ⟨γ', hγ'⟩ := l3_trans p l3e1 hp l3e1_ne_zero
      obtain ⟨g, -, hgγ⟩ := C.image_K γ'⁻¹
      refine ⟨(g : G) * w₀ * (g : G)⁻¹, (mem_normalizer_iff.mp g.2 w₀).mp hw₀W, ?_⟩
      rw [C.conj' g ⟨w₀, hw₀W⟩, hgγ, hcw₀, ← hγ', L3.act_inv_act]
  have horb : ∀ c ∈ W, c ≠ 1 → c ≠ z →
      ∃ g ∈ normalizer (W : Set G), g * c * g⁻¹ = S.zV ∨ g * c * g⁻¹ = z * S.zV := by
    intro c hc hc1 _
    have hp : C.c ⟨c, hc⟩ ≠ 0 := fun h => hc1 (hc0 hc h)
    obtain ⟨γ, hγ⟩ := l3_trans _ l3e1 hp l3e1_ne_zero
    obtain ⟨g, -, hgγ⟩ := C.image_K γ
    refine ⟨g, g.2, ?_⟩
    have h1 := C.conj' g ⟨c, hc⟩
    rw [hgγ, hγ, ← hcw₀] at h1
    have := hinj _ hw₀W h1
    rcases hw₀c with h' | h'
    · exact Or.inl (this.trans h')
    · exact Or.inr (this.trans h')
  have hnzT : ∀ x ∈ T, ∀ w ∈ W, x * w * x⁻¹ * w⁻¹ ≠ z := by
    intro x hx w hw h
    apply hzW
    rw [← h]
    exact mul_mem ((mem_normalizer_iff.mp (D.TW hx) w).mp hw) (inv_mem hw)
  have hWT := D.W_le_T
  have hWN : W ≤ normalizer (V : Set G) := hWT.trans S.frame.T_le
  have hVW : V ≤ normalizer (W : Set G) := S.V_le_T.trans D.TW
  have hnzC1 : ∀ x ∈ W, ∀ v ∈ V, x * v * x⁻¹ * v⁻¹ ≠ z := by
    intro x hx v hv h
    apply hzW
    rw [← h]
    have h2 : v * x⁻¹ * v⁻¹ ∈ W := (mem_normalizer_iff.mp (hVW hv) _).mp (inv_mem hx)
    have e : x * v * x⁻¹ * v⁻¹ = x * (v * x⁻¹ * v⁻¹) := by group
    rw [e]
    exact mul_mem hx h2
  have hcomm := comm_wt_of_orb S hz hzL h331 h1222 hWN hVW
    (fun c hc hc1 hcz => let ⟨g, _, hg⟩ := horb c hc hc1 hcz; ⟨g, hg⟩) hnzC1
  have hidx := centralizer_index_two S hz hzL hWN hW2 hcomm
  obtain ⟨⟨t₁, ht₁N⟩, ht₁TK, hρt₁⟩ := hB l3E23 l3E23_mem
  have ht₁T := (mem_inf.1 ht₁TK).1
  set U := W ⊓ centralizer ({t₁} : Set G) with hUdef
  have hUW : U ≤ W := inf_le_left
  have hmemU : ∀ (w : G) (hw : w ∈ W), w ∈ U ↔ InEll (C.c ⟨w, hw⟩) := by
    intro w hw
    have h1 := C.fix_iff ⟨t₁, ht₁N⟩ ⟨w, hw⟩
    rw [hρt₁] at h1
    simp only [hUdef, mem_inf, mem_centralizer_singleton_iff]
    rw [show (w * t₁ = t₁ * w ↔ t₁ * w * t₁⁻¹ = w) by rw [mul_inv_eq_iff_eq_mul, eq_comm]]
    exact ⟨fun h => h1.1 h.2, fun h => ⟨hw, h1.2 h⟩⟩
  have hw₀U : w₀ ∈ U := (hmemU w₀ hw₀W).2 (by rw [hcw₀]; exact inEll_e1)
  have hconjU : ∀ x : ↥(normalizer (W : Set G)),
      (∀ p : L3.Vec, InEll p → InEll (L3.act (C.ρ x) p)) →
        ∀ u ∈ U, (x : G) * u * (x : G)⁻¹ ∈ U := by
    intro x hx u hu
    have huW := hUW hu
    have h1 : (x : G) * u * (x : G)⁻¹ ∈ W := (mem_normalizer_iff.mp x.2 u).mp huW
    rw [hmemU _ h1, C.conj' x ⟨u, huW⟩]
    exact hx _ ((hmemU u huW).1 hu)
  have hPU : P ≤ normalizer (U : Set G) := by
    refine sup_le ?_ ?_
    · refine A5.le_normalizer_of_forall_conj_mem fun x hx u hu => ?_
      obtain ⟨⟨y, hyP, rfl⟩, -⟩ := mem_inf.1 hx
      exact hconjU y (fun p hp => ell_P2 _ hyP p hp) u hu
    · refine A5.le_normalizer_of_forall_conj_mem fun t ht u hu => ?_
      exact hconjU ⟨t, D.TW ht⟩ (fun p hp => ell_P2 _ (l3B_le_P2 _ (hTB' ⟨t, D.TW ht⟩ ht)) p hp)
        u hu
  have hCw₀ := centralizer_le_of_wtP_ne S hz hzL huniq h1222 hw₀V hw₀1 hw₀w
  have hPMT : P ⊓ normalizer (L : Set G) ≤ T := by
    rcases hcl (P ⊓ normalizer (L : Set G)) (le_inf (DP.T_le_parOf _) S.T_le_NL)
      (inf_le_left.trans hPKT) with h | h | h | h
    · exact h.le
    · exact absurd (h ▸ inf_le_left) hinc1
    · exact absurd (h ▸ inf_le_right) hstar.2.1
    · exfalso
      apply hstar.2.1
      exact hPKT.trans (h ▸ inf_le_right)
  have hPCT : P ⊓ centralizer (U : Set G) ≤ T := fun x hx =>
    hPMT (mem_inf.2 ⟨(mem_inf.1 hx).1,
      hCw₀ (centralizer_le (Set.singleton_subset_iff.2 hw₀U) (mem_inf.1 hx).2)⟩)
  have hF1 : ∀ u ∈ U, ∀ t ∈ T, u * t * u⁻¹ * t⁻¹ = 1 ∨ u * t * u⁻¹ * t⁻¹ = w₀ := by
    intro u hu t ht
    have huW := hUW hu
    have htN := D.TW ht
    have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right (hW2 u huW)
    have htu : t * u * t⁻¹ ∈ W := (mem_normalizer_iff.mp htN u).mp huW
    have e : u * t * u⁻¹ * t⁻¹ = u * (t * u * t⁻¹) := by rw [hui]; group
    have hcc : C.c ⟨u * (t * u * t⁻¹), mul_mem huW htu⟩ =
        C.c ⟨u, huW⟩ + L3.act (C.ρ ⟨t, htN⟩) (C.c ⟨u, huW⟩) := by
      rw [C.c_mul hW2 huW htu, C.conj' ⟨t, htN⟩ ⟨u, huW⟩]
    rw [e]
    rcases ell_comm _ (hTB' ⟨t, htN⟩ ht) _ ((hmemU u huW).1 hu) with h | h
    · left
      exact hc0 _ (hcc.trans h)
    · right
      exact hinj _ hw₀W (hcc.trans (h.trans hcw₀.symm))
  have hCU_iff : ∀ (t : G) (ht : t ∈ T),
      t ∈ centralizer (U : Set G) ↔ FixEll (C.ρ ⟨t, D.TW ht⟩) := by
    intro t ht
    constructor
    · intro htC p hp
      obtain ⟨w, hw, hcw⟩ := hsurj p
      have hwU : w ∈ U := (hmemU w hw).2 (by rw [hcw]; exact hp)
      have h1 : t * w * t⁻¹ = w := by
        rw [(mem_centralizer_iff.1 htC w hwU).symm, mul_inv_cancel_right]
      have h2 := (C.fix_iff ⟨t, D.TW ht⟩ ⟨w, hw⟩).1 h1
      rwa [hcw] at h2
    · intro hfix
      rw [mem_centralizer_iff]
      intro u hu
      have h1 := (C.fix_iff ⟨t, D.TW ht⟩ ⟨u, hUW hu⟩).2 (hfix _ ((hmemU u (hUW hu)).1 hu))
      calc u * t = t * u * t⁻¹ * t := by rw [show t * u * t⁻¹ = u from h1]
        _ = t * u := by group
  have hF2 : ∀ t ∈ T, ∀ t' ∈ T, t ∉ centralizer (U : Set G) → t' ∉ centralizer (U : Set G) →
      t * t' ∈ centralizer (U : Set G) := by
    intro t ht t' ht' h1 h2
    rw [hCU_iff t ht] at h1
    rw [hCU_iff t' ht'] at h2
    rw [hCU_iff _ (mul_mem ht ht')]
    have e : C.ρ ⟨t * t', D.TW (mul_mem ht ht')⟩ = C.ρ ⟨t, D.TW ht⟩ * C.ρ ⟨t', D.TW ht'⟩ := by
      rw [← map_mul]
      rfl
    rw [e]
    exact ell_index _ (hTB' _ ht) _ (hTB' _ ht') h1 h2
  have hW8 : Nat.card W = 8 := by
    have hbij : Function.Bijective C.c := ⟨C.c_inj, fun p => by
      obtain ⟨w, hw, hcw⟩ := hsurj p
      exact ⟨⟨w, hw⟩, hcw⟩⟩
    rw [Nat.card_congr (Equiv.ofBijective _ hbij), Nat.card_eq_fintype_card]
    rfl
  have hKEY : V ≤ centralizer (U : Set G) := by
    rcases hidx with hWC | h4
    · intro v hv
      rw [mem_centralizer_iff]
      intro u hu
      exact (mem_centralizer_iff.1 (hWC (hUW hu)) v hv).symm
    · have hC4 : Nat.card ↥(W ⊓ centralizer (V : Set G)) = 4 := by
        rw [hW8] at h4
        omega
      intro v hv
      have hvN := hVW hv
      have hv' : t₁ * v * t₁⁻¹ ∈ V := (mem_normalizer_iff.mp (S.frame.T_le ht₁T) v).mp hv
      have hv'N := hVW hv'
      have hσB := hTB' ⟨v, hvN⟩ (S.V_le_T hv)
      have hσ2 : C.ρ ⟨v, hvN⟩ * C.ρ ⟨v, hvN⟩ = 1 := by
        rw [← map_mul]
        have : (⟨v, hvN⟩ * ⟨v, hvN⟩ : ↥(normalizer (W : Set G))) = 1 :=
          Subtype.ext (mul_self_of_mem S hv)
        rw [this, map_one]
      have hρv' : C.ρ ⟨t₁ * v * t₁⁻¹, hv'N⟩ = l3E23 * C.ρ ⟨v, hvN⟩ * l3E23⁻¹ := by
        have e : (⟨t₁ * v * t₁⁻¹, hv'N⟩ : ↥(normalizer (W : Set G))) =
            ⟨t₁, ht₁N⟩ * ⟨v, hvN⟩ * (⟨t₁, ht₁N⟩)⁻¹ := rfl
        rw [e, map_mul, map_mul, map_inv, hρt₁]
      have hcount : 4 ≤ (Finset.univ.filter fun p : L3.Vec => L3.act (C.ρ ⟨v, hvN⟩) p = p ∧
          L3.act (l3E23 * C.ρ ⟨v, hvN⟩ * l3E23⁻¹) p = p).card := by
        classical
        let f : ↥(W ⊓ centralizer (V : Set G)) → {p : L3.Vec // p ∈ Finset.univ.filter
            fun p : L3.Vec => L3.act (C.ρ ⟨v, hvN⟩) p = p ∧
              L3.act (l3E23 * C.ρ ⟨v, hvN⟩ * l3E23⁻¹) p = p} :=
          fun w => ⟨C.c ⟨w, (mem_inf.1 w.2).1⟩, by
            have hwC := (mem_inf.1 w.2).2
            have h1 : v * (w : G) * v⁻¹ = w := by
              rw [mem_centralizer_iff.1 hwC v hv, mul_inv_cancel_right]
            have h2 : t₁ * v * t₁⁻¹ * (w : G) * (t₁ * v * t₁⁻¹)⁻¹ = w := by
              rw [mem_centralizer_iff.1 hwC _ hv', mul_inv_cancel_right]
            have h3 := (C.fix_iff ⟨v, hvN⟩ ⟨w, (mem_inf.1 w.2).1⟩).1 h1
            have h4 := (C.fix_iff ⟨t₁ * v * t₁⁻¹, hv'N⟩ ⟨w, (mem_inf.1 w.2).1⟩).1 h2
            rw [hρv'] at h4
            exact Finset.mem_filter.2 ⟨Finset.mem_univ _, h3, h4⟩⟩
        have hf : Function.Injective f := by
          intro a b hab
          have h1 : C.c ⟨a, (mem_inf.1 a.2).1⟩ = C.c ⟨b, (mem_inf.1 b.2).1⟩ :=
            congrArg (fun x : {p : L3.Vec // _} => (x : L3.Vec)) hab
          exact Subtype.ext (hinj _ _ h1)
        have h1 := Nat.card_le_card_of_injective f hf
        rw [hC4, Nat.card_eq_fintype_card, Fintype.card_coe] at h1
        exact h1
      have hfix := ell_key _ hσB hσ2 hcount
      rw [mem_centralizer_iff]
      intro u hu
      have h1 := (C.fix_iff ⟨v, hvN⟩ ⟨u, hUW hu⟩).2 (hfix _ ((hmemU u (hUW hu)).1 hu))
      calc u * v = v * u * v⁻¹ * v := by rw [show v * u * v⁻¹ = u from h1]
        _ = v * u := by group
  by_cases hA : ∀ g : G, conjSub g V ≤ T → conjSub g V ≤ centralizer (V : Set G)
  · exact false_of_all_comm S hz hzL huniq h331 h1222 hA (DP.T_le_parOf l3P2) hstar.2.1 hPU hPCT
      hw₀V hw₀1 hw₀w hF1 hF2 hKEY
  · push Not at hA
    obtain ⟨g, hgT, hgC⟩ := hA
    obtain ⟨hw2, i, j, hij, hρ⟩ := wt_two_of_le_T S hz hzL huniq h331 h1222 hgT hgC
    obtain ⟨y, hyT, -, a₁, ha₁, hρa₁⟩ := exists_conj_swap01 S hCMT hgT hij hρ hgC
    have hWA := not_le_centralizer_of_swap01 S hL1 D.Wirr.2.2.1 D.T_le_K hCKT hyT ha₁ hρa₁
    obtain ⟨⟨y₃, hy₃N⟩, hy₃L1, hρy₃⟩ := U3.s134_L1_three S (swap 0 1 * swap 1 2) (by decide)
    have hWC := le_centralizer_of_wt_two S hz hzL hw2 hWN hW2 hcomm hy₃N
      (D.Wirr.2.2.1 (hL1 hy₃L1)) hρy₃
    have hYN : conjSub y V ≤ normalizer (W : Set G) := hyT.trans D.TW
    have hE := C.card_le_four hYN (fun x hx => mul_self_of_mem_conj S hx)
      (fun x hx => hTB' ⟨x, hYN hx⟩ (hyT hx))
    have hpos := Nat.card_pos (α := ↥(conjSub y V ⊓ centralizer (W : Set G)))
    by_cases hU : ∀ a ∈ conjSub y V, ∀ u ∈ W, u ∈ normalizer (conjSub y V : Set G) →
        a * u = u * a
    · exact false_of_comm_eq S hz hzL huniq h1222 hWA hU (by omega) (fun h => by omega)
    · push Not at hU
      obtain ⟨a, ha, u, hu, huN, hau⟩ := hU
      exact false_of_comm_ne S hz hzL huniq h331 h1222 D.TW hWC horb hnzT hyT ha hu huN hau

end Data13410

end CFSG.Quasithin.H13.NQS134
