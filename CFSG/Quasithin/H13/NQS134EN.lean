module

public import CFSG.Quasithin.H13.NQS134EL
public import CFSG.Quasithin.H13.NQS134EH
public import CFSG.Quasithin.H13.NQS134EJ

public section

namespace CFSG.Quasithin.H13.NQS134

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6 CFSG.Quasithin.H13.U3.S6Out CFSG.Quasithin.H13.NQS134.End134
open scoped IsMulCommutative

theorem inS5_core : ∀ y : P6, InS5 y → ∑ i, Multiplicative.toAdd y i = 0 := by decide +kernel

theorem allOnes_mul_facts : G6.allOnes 6 * e45 = e0123 ∧ G6.allOnes 6 * e0123 = e45 := by decide

theorem exists_even_to {x : P6} (hx : ∑ i, Multiplicative.toAdd x i = 0) (h1 : x ≠ 1)
    (hO : x ≠ G6.allOnes 6) : ∃ τ : Perm (Fin 6), τ ∈ alternatingGroup (Fin 6) ∧
      (G6.permAct 6 τ x = e45 ∨ G6.permAct 6 τ x = e0123) := by
  have key : ∀ (y : P6) (σ : Perm (Fin 6)), G6.permAct 6 σ y = x →
      G6.permAct 6 (swap 4 5) y = y → ∃ τ : Perm (Fin 6), τ ∈ alternatingGroup (Fin 6) ∧
        G6.permAct 6 τ x = y := by
    intro y σ hσ h45
    have hinv : G6.permAct 6 σ⁻¹ x = y := by
      rw [← hσ, ← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply]
    rcases Int.units_eq_one_or (Perm.sign σ⁻¹) with h | h
    · exact ⟨σ⁻¹, Perm.mem_alternatingGroup.2 h, hinv⟩
    · refine ⟨swap 4 5 * σ⁻¹, Perm.mem_alternatingGroup.2 ?_, ?_⟩
      · rw [Perm.sign_mul, h, swap45_facts.1]
        rfl
      · rw [map_mul, MulAut.mul_apply, hinv, h45]
  rcases wtP_cases x hx with h | h | h | h
  · exact absurd h h1
  · exact absurd h hO
  · obtain ⟨σ, hσ⟩ := exists_perm_e45 x h
    obtain ⟨τ, hτ, hτx⟩ := key _ σ hσ swap45_facts.2.1
    exact ⟨τ, hτ, Or.inl hτx⟩
  · obtain ⟨σ, hσ⟩ := exists_perm_e0123 x h
    obtain ⟨τ, hτ, hτx⟩ := key _ σ hσ swap45_facts.2.2
    exact ⟨τ, hτ, Or.inr hτx⟩

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

namespace Data13410

variable {S : A6.Setting134 G T L V} {z : G} {H K W : Subgroup G} [IsMulCommutative ↥W]
  (D : Data13410 S z H K W)
include D

theorem false_core (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2)
    (h1332 : Stmt13_3_2) (hM : normalizer (L : Set G) = L ⊔ T)
    (hZV1 : quasithinOmegaOneCenter T = fsuV1 T V)
    (hL1Z : L₁Of L (fsuV1 T V) ≤ centralizer (quasithinOmegaOneCenter T : Set G))
    (hL1 : L₁Of L (fsuV1 T V) ≤ K) (hZW : quasithinOmegaOneCenter T ≤ W ⊔ U3.cZ T K)
    (hcZ : U3.cZ T K = zpowers z)
    (hK6 : Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 6)))
    (hW5 : Nat.card W = 2 ^ 5) (hc2 : Nat.card ↥(W ⊓ centralizer (K : Set G)) = 2)
    (hc : FFModel.Realizes (V := ↥W) (altCoreModel 6) (autOn K W) ⊤ ⊥)
    (hCMT : normalizer (L : Set G) ⊓ centralizer (V : Set G) ≤ T)
    (huniq : ∀ z' ∈ quasithinOmegaOneCenter T, z' ≠ 1 →
      ¬ centralizer ({z'} : Set G) ≤ normalizer (L : Set G) → z' = z) : False := by
  have hz := D.zV1
  have hzL := D.zL
  have hTZ : T ≤ centralizer (quasithinOmegaOneCenter T : Set G) :=
    le_centralizer_iff.mp ((U3.s134_Z_le_center T).trans inf_le_right)
  obtain ⟨R⟩ := exists_rawData6 D.Wirr.2.2.1 hc
  obtain ⟨F⟩ := exists_frame5 R (D.normalizer_W_le h1332) S.h13.sylow.1 D.TW D.isSylowTwoOf_inf
  have hZK := center_eq_bot_of_simple_types (Or.inr (Or.inr hK6))
  have hCKTT := D.inf_centralizer_le_T hZK
  obtain ⟨DP, hB⟩ := frame5_parData F D.T_le_K hCKTT
    (sup_le_sup_right hL1 T) (centralizer_Z_le_L1T S hM hZV1) (sup_le hL1Z hTZ)
    D.mem_Z_of_mem_centralizer_T (D.mem_centralizer_Z_of_fix hZW)
  have hTB : ∀ g : ↥(normalizer (W : Set G)), (g : G) ∈ T ⊓ K → F.ρ g ∈ a6D := fun g hg =>
    (mem_a6D_iff _).2 ⟨F.T_D g (mem_inf.1 hg).1,
      Perm.mem_alternatingGroup.1 ((F.image_L _).1 ⟨g, (mem_inf.1 hg).2, rfl⟩)⟩
  have hTY : ∀ t : ↥(normalizer (W : Set G)), (t : G) ∈ T → ∀ γ ∈ a6P2,
      F.ρ t * γ * (F.ρ t)⁻¹ ∈ a6P2 := fun t ht γ hγ =>
    a6P2_conj_D _ (F.T_D t ht) γ hγ
  obtain ⟨γ, hγ, β, hβ, hγβ⟩ := exists_a6P2_conj
  obtain ⟨hstar, hPKT, -, -, hcl, hinc1, -⟩ := D.h2_of_parData hM hZV1 DP stab45_le_alt hTB hB
    (fun Y hY hYA => a6_overgroups hY hYA)
    (fun x hx => a6D_le_P2 x hx) a6P2_le_alt a6P2_not_le stab45_not_le_P2 hTY a6D_relIndex_P2
    hγ hβ hγβ
  set P := DP.parOf a6P2 with hPdef
  have hzWK : z ∈ W ⊓ centralizer (K : Set G) := by
    rw [← D.zpowers_eq_inf hcZ hc2]
    exact mem_zpowers z
  have hzW : z ∈ W := (mem_inf.1 hzWK).1
  have hψz : (F.ψ ⟨z, hzW⟩ : P6) = G6.allOnes 6 :=
    (F5.centralizer_A6 F hzW (mem_inf.1 hzWK).2).resolve_left
      fun h => D.z_ne_one ((F5.psi_eq_one_iff F hzW).1 h)
  have hzz : z * z = 1 := by rw [← pow_two]; exact D.z_sq
  have hzVZ := U3.s134_zV_mem_Z S
  have hzVW : S.zV ∈ W := by
    have h1 := hZW hzVZ
    rwa [hcZ, sup_eq_left.2 (zpowers_le.2 hzW)] at h1
  have hzVT : S.zV ∈ centralizer (T : Set G) := (U3.s134_Z_le_center T hzVZ).2
  have hzVne : S.zV ≠ z := fun h => hzL (h ▸ (S.mem_ZV_iff.2 (Or.inr rfl)).2)
  have hψzV : (F.ψ ⟨S.zV, hzVW⟩ : P6) = e45 ∨ (F.ψ ⟨S.zV, hzVW⟩ : P6) = e0123 := by
    rcases F5.centralizer_T F hzVW hzVT with h | h | h | h
    · exact absurd ((F5.psi_eq_one_iff F hzVW).1 h) S.zV_ne_one
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd (F5.psi_inj F hzVW hzW (h.trans hψz.symm)) hzVne
  have hzzVW : z * S.zV ∈ W := mul_mem hzW hzVW
  have hψzzV : (F.ψ ⟨z * S.zV, hzzVW⟩ : P6) = G6.allOnes 6 * F.ψ ⟨S.zV, hzVW⟩ := by
    rw [F5.mul F hzW hzVW, hψz]
  obtain ⟨w₀, w₁, hw₀W, hw₁W, hψw₀, hψw₁, hw₀c, hw₁c⟩ : ∃ w₀ w₁ : G, ∃ (hw₀W : w₀ ∈ W)
      (hw₁W : w₁ ∈ W), (F.ψ ⟨w₀, hw₀W⟩ : P6) = e0123 ∧ (F.ψ ⟨w₁, hw₁W⟩ : P6) = e45 ∧
        (w₀ = S.zV ∨ w₀ = z * S.zV) ∧ (w₁ = S.zV ∨ w₁ = z * S.zV) := by
    rcases hψzV with h | h
    · refine ⟨z * S.zV, S.zV, hzzVW, hzVW, ?_, h, Or.inr rfl, Or.inl rfl⟩
      rw [hψzzV, h]
      exact allOnes_mul_facts.1
    · refine ⟨S.zV, z * S.zV, hzVW, hzzVW, h, ?_, Or.inl rfl, Or.inr rfl⟩
      rw [hψzzV, h]
      exact allOnes_mul_facts.2
  have hw₀V : w₀ ∈ V := by
    rcases hw₀c with rfl | rfl
    · exact S.zV_mem_V
    · exact mul_mem hz.1 S.zV_mem_V
  obtain ⟨h6, h4⟩ := wtP_ne_of_zV S hz hzL
  have hw₀1 : w₀ ≠ 1 := by
    rcases hw₀c with rfl | rfl
    · exact S.zV_ne_one
    · exact mul_zV_ne_one S hzL
  have hw₀w : wtP (S.frame.ψ ⟨w₀, hw₀V⟩ : P6) ≠ wtP (S.frame.ψ ⟨z, hz.1⟩ : P6) := by
    rcases hw₀c with rfl | rfl
    · exact h6
    · exact h4
  have horb : ∀ c ∈ W, c ≠ 1 → c ≠ z →
      ∃ g ∈ normalizer (W : Set G), g * c * g⁻¹ = S.zV ∨ g * c * g⁻¹ = z * S.zV := by
    intro c hc hc1 hcz
    have hx1 : (F.ψ ⟨c, hc⟩ : P6) ≠ 1 := fun h => hc1 ((F5.psi_eq_one_iff F hc).1 h)
    have hxO : (F.ψ ⟨c, hc⟩ : P6) ≠ G6.allOnes 6 := fun h =>
      hcz (F5.psi_inj F hc hzW (h.trans hψz.symm))
    obtain ⟨τ, hτA, hτ⟩ := exists_even_to (F5.psi_core F _) hx1 hxO
    obtain ⟨g, -, hgτ⟩ := (F.image_L τ).2 hτA
    refine ⟨g, g.2, ?_⟩
    have h1 := F5.conj F g ⟨c, hc⟩
    rw [hgτ] at h1
    rcases hτ with h | h
    · have := F5.psi_inj F _ hw₁W (h1.trans (h.trans hψw₁.symm))
      rcases hw₁c with h' | h'
      · exact Or.inl (this.trans h')
      · exact Or.inr (this.trans h')
    · have := F5.psi_inj F _ hw₀W (h1.trans (h.trans hψw₀.symm))
      rcases hw₀c with h' | h'
      · exact Or.inl (this.trans h')
      · exact Or.inr (this.trans h')
  have hnzT : ∀ x ∈ T, ∀ w ∈ W, x * w * x⁻¹ * w⁻¹ ≠ z := by
    intro x hx w hw h
    have hc : x * w * x⁻¹ * w⁻¹ ∈ W :=
      mul_mem ((mem_normalizer_iff.mp (F.T_le hx) w).mp hw) (inv_mem hw)
    have h1 := F5.comm F (F.T_le hx) hw hc
    have h2 : (F.ψ ⟨x * w * x⁻¹ * w⁻¹, hc⟩ : P6) = G6.allOnes 6 := by
      rw [show (⟨x * w * x⁻¹ * w⁻¹, hc⟩ : ↥W) = ⟨z, hzW⟩ from Subtype.ext h, hψz]
    exact comm_ne_allOnes _ _ (F5.psi_core F _) (h1.symm.trans h2)
  have hnzC1 : ∀ x ∈ W, ∀ v ∈ V, x * v * x⁻¹ * v⁻¹ ≠ z := by
    intro x hx v hv h
    apply hnzT v (S.V_le_T hv) x hx
    have e : v * x * v⁻¹ * x⁻¹ = (x * v * x⁻¹ * v⁻¹)⁻¹ := by group
    rw [e, h]
    exact inv_eq_of_mul_eq_one_right hzz
  have hWT := D.W_le_T
  have hWN : W ≤ normalizer (V : Set G) := hWT.trans S.frame.T_le
  have hVW : V ≤ normalizer (W : Set G) := S.V_le_T.trans D.TW
  have hW2 : ∀ x ∈ W, x * x = 1 := fun x hx => by rw [← pow_two]; exact D.sq_eq_one hx
  have hcomm := comm_wt_of_orb S hz hzL h331 h1222 hWN hVW
    (fun c hc hc1 hcz => let ⟨g, _, hg⟩ := horb c hc hc1 hcz; ⟨g, hg⟩) hnzC1
  have hidx := centralizer_index_two S hz hzL hWN hW2 hcomm
  obtain ⟨⟨t₁, ht₁N⟩, -, hρt₁⟩ :=
    F.DA_T (swap 0 1 * swap 2 3) (by decide) (Perm.mem_alternatingGroup.2 (by decide))
  obtain ⟨⟨t₂, ht₂N⟩, -, hρt₂⟩ :=
    F.DA_T (swap 0 1 * swap 4 5) (by decide) (Perm.mem_alternatingGroup.2 (by decide))
  set U := (W ⊓ centralizer ({t₁} : Set G)) ⊓ centralizer ({t₂} : Set G) with hUdef
  have hUW : U ≤ W := inf_le_left.trans inf_le_left
  have hcomm_iff : ∀ (t w : G), w * t = t * w ↔ t * w * t⁻¹ = w := fun t w => by
    rw [mul_inv_eq_iff_eq_mul, eq_comm]
  have hmemU : ∀ (w : G) (hw : w ∈ W), w ∈ U ↔ InS5 (F.ψ ⟨w, hw⟩ : P6) := by
    intro w hw
    have h1 := F5.fix_iff F ⟨t₁, ht₁N⟩ ⟨w, hw⟩
    have h2 := F5.fix_iff F ⟨t₂, ht₂N⟩ ⟨w, hw⟩
    rw [hρt₁] at h1
    rw [hρt₂] at h2
    simp only [hUdef, mem_inf, mem_centralizer_singleton_iff]
    rw [hcomm_iff, hcomm_iff]
    exact ⟨fun h => ⟨h1.1 h.1.2, h2.1 h.2⟩, fun h => ⟨⟨hw, h1.2 h.1⟩, h2.2 h.2⟩⟩
  have hw₀U : w₀ ∈ U := (hmemU w₀ hw₀W).2 (by rw [hψw₀]; exact inS5_facts.1)
  have hconjU : ∀ x : ↥(normalizer (W : Set G)),
      (∀ y : P6, InS5 y → InS5 (G6.permAct 6 (F.ρ x) y)) →
        ∀ u ∈ U, (x : G) * u * (x : G)⁻¹ ∈ U := by
    intro x hx u hu
    have huW := hUW hu
    have h1 : (x : G) * u * (x : G)⁻¹ ∈ W := (mem_normalizer_iff.mp x.2 u).mp huW
    rw [hmemU _ h1, F5.conj F x ⟨u, huW⟩]
    exact hx _ ((hmemU u huW).1 hu)
  have hPU : P ≤ normalizer (U : Set G) := by
    refine sup_le ?_ ?_
    · refine A5.le_normalizer_of_forall_conj_mem fun x hx u hu => ?_
      obtain ⟨⟨y, hyP, rfl⟩, -⟩ := mem_inf.1 hx
      exact hconjU y (fun y' hy' => s5_P2 _ hyP y' hy') u hu
    · refine A5.le_normalizer_of_forall_conj_mem fun t ht u hu => ?_
      obtain ⟨i, hi⟩ := mem_d6 _ (F.T_D ⟨t, F.T_le ht⟩ ht)
      exact hconjU ⟨t, F.T_le ht⟩ (fun y hy => by rw [← hi]; exact s5_D i y hy) u hu
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
    have htN := F.T_le ht
    have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right (hW2 u huW)
    have htu : t * u * t⁻¹ ∈ W := (mem_normalizer_iff.mp htN u).mp huW
    have e : u * t * u⁻¹ * t⁻¹ = u * (t * u * t⁻¹) := by rw [hui]; group
    have hψ : (F.ψ ⟨u * (t * u * t⁻¹), mul_mem huW htu⟩ : P6) =
        (F.ψ ⟨u, huW⟩ : P6) * G6.permAct 6 (F.ρ ⟨t, htN⟩) (F.ψ ⟨u, huW⟩ : P6) := by
      rw [F5.mul F huW htu, F5.conj F ⟨t, htN⟩ ⟨u, huW⟩]
    obtain ⟨i, hi⟩ := mem_d6 _ (F.T_D ⟨t, htN⟩ ht)
    rw [← hi] at hψ
    rw [e]
    rcases s5_comm i _ ((hmemU u huW).1 hu) with h | h
    · left
      exact (F5.psi_eq_one_iff F (mul_mem huW htu)).1 (hψ.trans h)
    · right
      exact F5.psi_inj F _ hw₀W (hψ.trans (h.trans hψw₀.symm))
  have hCU_iff : ∀ (t : G) (ht : t ∈ T),
      t ∈ centralizer (U : Set G) ↔ FixS5 (F.ρ ⟨t, F.T_le ht⟩) := by
    intro t ht
    constructor
    · intro htC y hy
      obtain ⟨w, hw, hψw⟩ := F5.exists_of_core F (inS5_core y hy)
      have hwU : w ∈ U := (hmemU w hw).2 (by rw [hψw]; exact hy)
      have h1 : t * w * t⁻¹ = w := by
        rw [(mem_centralizer_iff.1 htC w hwU).symm, mul_inv_cancel_right]
      have h2 := (F5.fix_iff F ⟨t, F.T_le ht⟩ ⟨w, hw⟩).1 h1
      rwa [hψw] at h2
    · intro hfix
      rw [mem_centralizer_iff]
      intro u hu
      have h1 := (F5.fix_iff F ⟨t, F.T_le ht⟩ ⟨u, hUW hu⟩).2 (hfix _ ((hmemU u (hUW hu)).1 hu))
      calc u * t = t * u * t⁻¹ * t := by rw [h1]
        _ = t * u := by group
  have hF2 : ∀ t ∈ T, ∀ t' ∈ T, t ∉ centralizer (U : Set G) → t' ∉ centralizer (U : Set G) →
      t * t' ∈ centralizer (U : Set G) := by
    intro t ht t' ht' h1 h2
    rw [hCU_iff t ht] at h1
    rw [hCU_iff t' ht'] at h2
    rw [hCU_iff _ (mul_mem ht ht')]
    obtain ⟨i, hi⟩ := mem_d6 _ (F.T_D ⟨t, F.T_le ht⟩ ht)
    obtain ⟨j, hj⟩ := mem_d6 _ (F.T_D ⟨t', F.T_le ht'⟩ ht')
    have e : F.ρ ⟨t * t', F.T_le (mul_mem ht ht')⟩ =
        F.ρ ⟨t, F.T_le ht⟩ * F.ρ ⟨t', F.T_le ht'⟩ := by
      rw [← map_mul]
      rfl
    rw [e, ← hi, ← hj]
    rw [← hi] at h1
    rw [← hj] at h2
    exact s5_index i j h1 h2
  have hKEY : V ≤ centralizer (U : Set G) := by
    rcases hidx with hWC | h16
    · intro v hv
      rw [mem_centralizer_iff]
      intro u hu
      exact (mem_centralizer_iff.1 (hWC (hUW hu)) v hv).symm
    · have hC16 : Nat.card ↥(W ⊓ centralizer (V : Set G)) = 16 := by
        rw [hW5] at h16
        omega
      obtain ⟨⟨t₃, ht₃N⟩, ht₃T, hρt₃⟩ :=
        F.DA_T (swap 0 2 * swap 1 3) (by decide) (Perm.mem_alternatingGroup.2 (by decide))
      intro v hv
      have hvN := hVW hv
      have hv' : t₃ * v * t₃⁻¹ ∈ V := (mem_normalizer_iff.mp (S.frame.T_le ht₃T) v).mp hv
      have hv'N := hVW hv'
      obtain ⟨i, hi⟩ := mem_d6 _ (F.T_D ⟨v, hvN⟩ (S.V_le_T hv))
      have hσ2 : d6 i * d6 i = 1 := by
        rw [hi, ← map_mul]
        have : (⟨v, hvN⟩ * ⟨v, hvN⟩ : ↥(normalizer (W : Set G))) = 1 :=
          Subtype.ext (mul_self_of_mem S hv)
        rw [this, map_one]
      have hρv' : F.ρ ⟨t₃ * v * t₃⁻¹, hv'N⟩ =
          swap 0 2 * swap 1 3 * d6 i * (swap 0 2 * swap 1 3)⁻¹ := by
        have e : (⟨t₃ * v * t₃⁻¹, hv'N⟩ : ↥(normalizer (W : Set G))) =
            ⟨t₃, ht₃N⟩ * ⟨v, hvN⟩ * (⟨t₃, ht₃N⟩)⁻¹ := rfl
        rw [e, map_mul, map_mul, map_inv, hρt₃, hi]
      have hcount : 16 ≤ (Finset.univ.filter fun x : P6 => ∑ j, Multiplicative.toAdd x j = 0 ∧
          G6.permAct 6 (d6 i) x = x ∧
            G6.permAct 6 (swap 0 2 * swap 1 3 * d6 i * (swap 0 2 * swap 1 3)⁻¹) x = x).card := by
        classical
        let f : ↥(W ⊓ centralizer (V : Set G)) → {x : P6 // x ∈ Finset.univ.filter fun x : P6 =>
            ∑ j, Multiplicative.toAdd x j = 0 ∧ G6.permAct 6 (d6 i) x = x ∧
              G6.permAct 6 (swap 0 2 * swap 1 3 * d6 i * (swap 0 2 * swap 1 3)⁻¹) x = x} :=
          fun w => ⟨F.ψ ⟨w, (mem_inf.1 w.2).1⟩, by
            have hwC := (mem_inf.1 w.2).2
            have h1 : v * (w : G) * v⁻¹ = w := by
              rw [mem_centralizer_iff.1 hwC v hv, mul_inv_cancel_right]
            have h2 : t₃ * v * t₃⁻¹ * (w : G) * (t₃ * v * t₃⁻¹)⁻¹ = w := by
              rw [mem_centralizer_iff.1 hwC _ hv', mul_inv_cancel_right]
            have h3 := (F5.fix_iff F ⟨v, hvN⟩ ⟨w, (mem_inf.1 w.2).1⟩).1 h1
            have h4 := (F5.fix_iff F ⟨t₃ * v * t₃⁻¹, hv'N⟩ ⟨w, (mem_inf.1 w.2).1⟩).1 h2
            rw [← hi] at h3
            rw [hρv'] at h4
            exact Finset.mem_filter.2 ⟨Finset.mem_univ _, F5.psi_core F _, h3, h4⟩⟩
        have hf : Function.Injective f := by
          intro a b hab
          have h1 : (F.ψ ⟨a, (mem_inf.1 a.2).1⟩ : P6) = F.ψ ⟨b, (mem_inf.1 b.2).1⟩ :=
            congrArg (fun x : {x : P6 // _} => (x : P6)) hab
          exact Subtype.ext (F5.psi_inj F _ _ h1)
        have h1 := Nat.card_le_card_of_injective f hf
        rw [hC16, Nat.card_eq_fintype_card, Fintype.card_coe] at h1
        exact h1
      have hfix := s5_key i hσ2 hcount
      rw [mem_centralizer_iff]
      intro u hu
      have h1 := (F5.fix_iff F ⟨v, hvN⟩ ⟨u, hUW hu⟩).2
        (by rw [← hi]; exact hfix _ ((hmemU u (hUW hu)).1 hu))
      calc u * v = v * u * v⁻¹ * v := by rw [h1]
        _ = v * u := by group
  by_cases hA : ∀ g : G, conjSub g V ≤ T → conjSub g V ≤ centralizer (V : Set G)
  · exact false_of_all_comm S hz hzL huniq h331 h1222 hA (DP.T_le_parOf a6P2) hstar.2.1 hPU hPCT
      hw₀V hw₀1 hw₀w hF1 hF2 hKEY
  · push Not at hA
    obtain ⟨g, hgT, hgC⟩ := hA
    obtain ⟨hw2, i, j, hij, hρ⟩ := wt_two_of_le_T S hz hzL huniq h331 h1222 hgT hgC
    obtain ⟨y, hyT, -, a₁, ha₁, hρa₁⟩ := exists_conj_swap01 S hCMT hgT hij hρ hgC
    have hCKT : K ⊓ centralizer (W : Set G) ≤ T := fun x hx =>
      hCKTT (mem_inf.2 ⟨mem_sup_left (mem_inf.1 hx).1, (mem_inf.1 hx).2⟩)
    have hWA := not_le_centralizer_of_swap01 S hL1 D.Wirr.2.2.1 D.T_le_K hCKT hyT ha₁ hρa₁
    obtain ⟨⟨y₃, hy₃N⟩, hy₃L1, hρy₃⟩ := U3.s134_L1_three S (swap 0 1 * swap 1 2) (by decide)
    have hWC := le_centralizer_of_wt_two S hz hzL hw2 hWN hW2 hcomm hy₃N
      (D.Wirr.2.2.1 (hL1 hy₃L1)) hρy₃
    obtain ⟨hE1, hE2⟩ := F5.card_le_eight F hyT (fun x hx => mul_self_of_mem_conj S hx)
    by_cases hU : ∀ a ∈ conjSub y V, ∀ u ∈ W, u ∈ normalizer (conjSub y V : Set G) →
        a * u = u * a
    · exact false_of_comm_eq S hz hzL huniq h1222 hWA hU hE1 hE2
    · push Not at hU
      obtain ⟨a, ha, u, hu, huN, hau⟩ := hU
      exact false_of_comm_ne S hz hzL huniq h331 h1222 D.TW hWC horb hnzT hyT ha hu huN hau

end Data13410

end CFSG.Quasithin.H13.NQS134
