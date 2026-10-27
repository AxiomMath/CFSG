module

public import CFSG.Quasithin.H13.A6S13834P

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement


open CFSG.Quasithin.CosetGeom

@[expose] def t3List : List (Perm (Fin 6)) := [1, swap 0 1, swap 2 3, swap 4 5]

theorem t3_mul : ∀ s ∈ t3List, ∀ t ∈ t3List, t ≠ 1 → s * t ∈ t3List → s = 1 ∨ s = t := by
  decide +kernel

theorem mem_t3 {σ : Perm (Fin 6)}
    (h : σ = 1 ∨ σ = swap 0 1 ∨ σ = swap 2 3 ∨ σ = swap 4 5) : σ ∈ t3List := by
  rcases h with rfl | rfl | rfl | rfl <;> decide

theorem mIdx_conjSub {G : Type} [Group G] (a : G) (X Y : Subgroup G) :
    mIdx (conjSub a X) (conjSub a Y) = mIdx X Y := by
  unfold mIdx
  rw [show (conjSub a Y).relIndex (conjSub a X) = Y.relIndex X from
    Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj a).injective]

theorem exists_conj_Vγ_le {G : Type} [Group G] [Finite G] {T V L V₁ Vp H : Subgroup G}
    (h : HypF98 T V L V₁ Vp H) {γ γ' : F8.Geom T L H} {g : ↥((L ⊔ T) ⊔ H)}
    (sk : F8Setup T V L H γ γ' g) :
    ∃ c ∈ H, conjSub c (F8.Uγ V H (g : G)) ≤ pCoreOf 2 (L₁Of L V₁ ⊔ T) := by
  have hb3 : 3 ≤ critDist ((L ⊔ T) ⊔ H) (L ⊔ T) H V := h.three_le_b_and_odd.1
  obtain ⟨-, ⟨γ₂, hγ₂nb, hd⟩⟩ :=
    exists_nbrs_of_geodesic h.amalgamHypV.gen sk.critical.geodesic (by omega : 2 ≤ _)
  have hV2 := (h.F913_2 sk).2 γ₂ hγ₂nb hd
  obtain ⟨c, hc, hcγ⟩ := stab_transitive_on_nbrs hγ₂nb
    (show F8.γ₀ T L H ∈ nbrs (F8.γ₁ T L H) from (adj_γ₀_γ₁ (G₀ := (L ⊔ T) ⊔ H)).symm)
  have hcH : (c : G) ∈ H := by rwa [stab_γ₁ h.amalgamHypV.le₂] at hc
  have hc1 : c • F8.γ₁ T L H = F8.γ₁ T L H := smul_eq_of_mem_stab hc
  refine ⟨c, hcH, ?_⟩
  have h1 := conjSub_mono (c : G) hV2
  rw [← pCoreOf_conjSub, conjSub_inf, ← stab_smul, ← stab_smul, hc1, hcγ, inf_comm,
    h.F913_1] at h1
  exact h1

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem comm_QH_VH_mem (hNS : ¬ LieModel G .PSp 3 2 1)
    (h13315 : Stmt13_3_15) (h1356two : Input1356Two) (hG1 : S.G1 ∈ S.Hz)
    (h13314 : Stmt13_3_14) {q : G} (hq : q ∈ pCoreOf 2 S.G1) {y : G}
    (hy : y ∈ conjClosure V S.G1) : q * y * q⁻¹ * y⁻¹ ∈ conjClosure S.V3 S.G1 := by
  have h := Subgroup.commutator_mem_commutator hy hq
  rw [S.comm_VH_QH_eq hNS h13315 h1356two hG1 h13314] at h
  have e : q * y * q⁻¹ * y⁻¹ = ⁅y, q⁆⁻¹ := by rw [commutatorElement_def]; group
  rw [e]
  exact (conjClosure S.V3 S.G1).inv_mem h

theorem A1_le_UH_of (hNS : ¬ LieModel G .PSp 3 2 1)
    (h13315 : Stmt13_3_15) (h1356two : Input1356Two) (hG1 : S.G1 ∈ S.Hz)
    (h13314 : Stmt13_3_14) (hF : HypF98 T V L (fsuV1 T V) S.V3 S.G1)
    {γ γ' : F8.Geom T L S.G1} {g : ↥((L ⊔ T) ⊔ S.G1)} (s : F8Setup T V L S.G1 γ γ' g)
    {K : Subgroup G} (hKT : K ⊔ T = S.G1) (hL1K : S.L1 ≤ K) (ρ : ↥S.G1 →* Perm (Fin 6))
    (hker : ∀ h : ↥S.G1, ρ h = 1 ↔ (h : G) ∈ pCoreOf 2 S.G1)
    (hKA : ∀ k : ↥S.G1, (k : G) ∈ K → ρ k ∈ alternatingGroup (Fin 6))
    (honto : ∀ σ ∈ alternatingGroup (Fin 6), ∃ k : ↥S.G1, (k : G) ∈ K ∧ ρ k = σ)
    (hβ : UHCoords S ρ) {c : G} (hc : c ∈ S.G1)
    (hcV : conjSub c (F8.Uγ V S.G1 (g : G)) ≤ pCoreOf 2 (S.L1 ⊔ T))
    (h1γ : mIdx (F8.Uγ S.V3 S.G1 (g : G)) (F8.Dγ S.V3 (fsuV1 T V) S.G1 (g : G)) = 1)
    (h1H : mIdx (conjClosure S.V3 S.G1) (F8.DH S.V3 (fsuV1 T V) S.G1 (g : G)) = 1)
    (hDH : F8.DH S.V3 (fsuV1 T V) S.G1 (g : G) < conjClosure S.V3 S.G1) :
    F8.A₁ (fsuV1 T V) (g : G) ≤ conjClosure S.V3 S.G1 := by
  by_contra hA
  obtain ⟨τ, ρ', hρ', hN', hker', hKA', honto', hE8, -⟩ :=
    S.exists_coords hF hKT hL1K ρ hker hKA honto hβ
  obtain ⟨R, hR⟩ := S.exists_repRel hβ
  set Q := pCoreOf 2 S.G1 with hQdef
  set U := conjClosure S.V3 S.G1 with hUdef
  set Uγ := F8.Uγ S.V3 S.G1 (g : G) with hUγdef
  set Vγ := F8.Uγ V S.G1 (g : G) with hVγdef
  set A₁ := F8.A₁ (fsuV1 T V) (g : G) with hA₁def
  set DH := F8.DH S.V3 (fsuV1 T V) S.G1 (g : G) with hDHdef
  set Dγ := F8.Dγ S.V3 (fsuV1 T V) S.G1 (g : G) with hDγdef
  have hQT : Q ≤ T := isSylowTwoOf_pCoreOf_le hF.toHypF91.sylow_H
  have hVle : V ≤ S.G1 := hF.toHypF91.V_le_H
  have hab : IsElemAbelian 2 U := hF.F911_3
  have hUQ : U ≤ Q := hF.conjClosure_Vp_le_pCoreOf
  have hU2 : IsPGroup 2 U := (pCoreOf_isPGroup 2 S.G1).to_le hUQ
  have hUN : ∀ k ∈ S.G1, ∀ u ∈ U, k * u * k⁻¹ ∈ U := fun k hk u hu =>
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure S.V3 S.G1 hk) u).mp hu
  have hQN : ∀ k ∈ S.G1, ∀ q ∈ Q, k * q * k⁻¹ ∈ Q := fun k hk q hq =>
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 S.G1 hk) q).mp hq
  have hstab : stab γ = conjSub (g : G) S.G1 := S.stab_γ_eq hF s
  have hUγst : U ≤ stab γ :=
    (conjClosure_mono S.V3_le_V le_rfl).trans ((hF.F913_2 s).1.trans ((pCoreOf_le 2 _).trans
      inf_le_right))
  have hUg : ∀ u ∈ U, (g : G)⁻¹ * u * (g : G) ∈ S.G1 := fun u hu => by
    have := hUγst hu
    rw [hstab, mem_conjSub] at this
    exact this
  have hUγH : Uγ ≤ S.G1 := hF.Uγ_le_H s
  have hVγH : Vγ ≤ S.G1 := hF.Vγ_le_H s
  have hA1U : ∀ x ∈ A₁, x ∈ U → x = 1 := by
    intro x hxA hxU
    by_contra hx1
    apply hA
    refine le_of_card_eq_two_of_inf_ne_bot (hF.card_A₁ (g := g)) ?_
    rw [Ne, Subgroup.eq_bot_iff_forall]
    push Not
    exact ⟨x, ⟨hxA, hxU⟩, hx1⟩
  have h3UU := hF.F913_3 s (X := S.V3) (Y := S.V3) (Or.inl rfl) (Or.inl rfl)
  have h3UV := hF.F913_3 s (X := S.V3) (Y := V) (Or.inl rfl) (Or.inr rfl)
  have hDHc : ∀ d ∈ DH, ∀ u ∈ Uγ, d * u * d⁻¹ * u⁻¹ = 1 := by
    intro d hd u hu
    have h1 : d * u * d⁻¹ * u⁻¹ ∈ A₁ := hd.2.2 u hu
    have h2 : d * u * d⁻¹ * u⁻¹ ∈ U := by
      have := (h3UU (Subgroup.commutator_mem_commutator hd.1 hu)).1
      rwa [commutatorElement_def] at this
    exact hA1U _ h1 h2
  have hVγDH : ∀ y ∈ Vγ, ∀ d ∈ DH, y * d * y⁻¹ * d⁻¹ = 1 := by
    intro y hy d hd
    have hdU : d ∈ U := hd.1
    set d₀ := (g : G)⁻¹ * d * (g : G) with hd₀
    have hd₀H : d₀ ∈ S.G1 := hUg d hdU
    have hd₀C : d₀ ∈ Subgroup.centralizer (U : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      have hu' : (g : G) * u * (g : G)⁻¹ ∈ Uγ := mul_mem_conjSub hu
      have hc := hDHc d hd _ hu'
      have e : d * ((g : G) * u * (g : G)⁻¹) = ((g : G) * u * (g : G)⁻¹) * d := by
        calc d * ((g : G) * u * (g : G)⁻¹) =
            (d * ((g : G) * u * (g : G)⁻¹) * d⁻¹ * ((g : G) * u * (g : G)⁻¹)⁻¹) *
              (((g : G) * u * (g : G)⁻¹) * d) := by group
          _ = ((g : G) * u * (g : G)⁻¹) * d := by rw [hc, one_mul]
      calc u * d₀ = (g : G)⁻¹ * (((g : G) * u * (g : G)⁻¹) * d) * (g : G) := by
            rw [hd₀]; group
        _ = (g : G)⁻¹ * (d * ((g : G) * u * (g : G)⁻¹)) * (g : G) := by rw [e]
        _ = d₀ * u := by rw [hd₀]; group
    have hd₀Q : d₀ ∈ Q := by
      rw [hQdef, hF.toHypF91.pCoreOf_eq_centralizerMod]
      refine ⟨hd₀H, hF.H_normalizes_V₁ hd₀H, fun u hu => ?_⟩
      rw [← Subgroup.mem_centralizer_iff.mp hd₀C u hu, mul_inv_cancel_right, mul_inv_cancel]
      exact (fsuV1 T V).one_mem
    have hy₀ : (g : G)⁻¹ * y * (g : G) ∈ conjClosure V S.G1 := by
      have := hy
      rwa [hVγdef, F8.Uγ, mem_conjSub] at this
    have h1 := S.comm_VH_HC hNS h13315 h1356two hG1 hd₀Q hd₀C hy₀
    have h2 : y * d * y⁻¹ * d⁻¹ ∈ A₁ := by
      have e : y * d * y⁻¹ * d⁻¹ = (g : G) * (((g : G)⁻¹ * y * (g : G)) * d₀ *
          ((g : G)⁻¹ * y * (g : G))⁻¹ * d₀⁻¹) * (g : G)⁻¹ := by rw [hd₀]; group
      rw [e, hA₁def, F8.A₁]
      exact mul_mem_conjSub h1
    have h3 : y * d * y⁻¹ * d⁻¹ ∈ U := by
      have := (h3UV (Subgroup.commutator_mem_commutator hdU hy)).1
      rw [commutatorElement_def] at this
      have e : y * d * y⁻¹ * d⁻¹ = (d * y * d⁻¹ * y⁻¹)⁻¹ := by group
      rw [e]
      exact U.inv_mem this
    exact hA1U _ h2 h3
  have hDH2 : DH.relIndex U = 2 := by
    rw [HypF98.relIndex_eq_two_pow_mIdx hU2, h1H, pow_one]
  have hDγ2 : Dγ.relIndex Uγ = 2 := by
    rw [HypF98.relIndex_eq_two_pow_mIdx (isPGroup_of_isElemAbelian hF.isElemAbelian_Uγ), h1γ,
      pow_one]
  have hconjU : ∀ k ∈ S.G1, conjSub k U = U := fun k hk =>
    F7.conjSub_eq_of_mem_normalizer (le_normalizer_conjClosure S.V3 S.G1 hk)
  have hVle' : Vγ ≤ Uγ ⊔ Q := by
    have hcD : (conjSub c DH).relIndex U = 2 := by
      rw [← hconjU c hc]
      rw [show (conjSub c DH).relIndex (conjSub c U) = DH.relIndex U from
        Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj c).injective]
      exact hDH2
    have hT3 : ∀ v ∈ Vγ, ∀ hv : c * v * c⁻¹ ∈ S.G1, ρ' ⟨_, hv⟩ ∈ t3List := by
      intro v hv hvH
      refine mem_t3 (S.rho_tv_of_centralizes hR hρ' hab
        (hE8 ⟨_, hvH⟩ (hcV (mul_mem_conjSub hv))) hcD ?_)
      intro d' hd'
      have hd : c⁻¹ * d' * c ∈ DH := mem_conjSub.mp hd'
      have h1 := hVγDH v hv _ hd
      calc c * v * c⁻¹ * d' * (c * v * c⁻¹)⁻¹ =
          c * (v * (c⁻¹ * d' * c) * v⁻¹ * (c⁻¹ * d' * c)⁻¹) * c⁻¹ * d' := by group
        _ = d' := by rw [h1]; group
    have hcH : ∀ v ∈ Vγ, c * v * c⁻¹ ∈ S.G1 := fun v hv =>
      S.G1.mul_mem (S.G1.mul_mem hc (hVγH hv)) (S.G1.inv_mem hc)
    obtain ⟨u, huγ, huQ⟩ : ∃ u ∈ Uγ, u ∉ Q := by
      by_contra hcon
      push Not at hcon
      have h1 : Dγ = Uγ := by
        rw [hDγdef, hF.Dγ_eq_inf_pCoreOf s]
        exact inf_eq_left.2 hcon
      rw [h1, Subgroup.relIndex_self] at hDγ2
      exact absurd hDγ2 (by norm_num)
    have huV : u ∈ Vγ := hF.Uγ_le_Vγ huγ
    have ht1 : ρ' ⟨_, hcH u huV⟩ ≠ 1 := by
      intro h1
      apply huQ
      have h2 := (hker' _).1 h1
      have := hQN _ (S.G1.inv_mem hc) _ h2
      rwa [show c⁻¹ * (c * u * c⁻¹) * c⁻¹⁻¹ = u by group] at this
    intro v hv
    have hvu : v * u ∈ Vγ := Vγ.mul_mem hv huV
    have hmul : ρ' ⟨_, hcH v hv⟩ * ρ' ⟨_, hcH u huV⟩ = ρ' ⟨_, hcH _ hvu⟩ := by
      rw [← map_mul]
      congr 1
      apply Subtype.ext
      show c * v * c⁻¹ * (c * u * c⁻¹) = c * (v * u) * c⁻¹
      group
    rcases t3_mul _ (hT3 v hv (hcH v hv)) _ (hT3 u huV (hcH u huV)) ht1
      (by rw [hmul]; exact hT3 _ hvu (hcH _ hvu)) with h | h
    · have h2 := (hker' _).1 h
      have := hQN _ (S.G1.inv_mem hc) _ h2
      rw [show c⁻¹ * (c * v * c⁻¹) * c⁻¹⁻¹ = v by group] at this
      exact Subgroup.mem_sup_right this
    · have h2 : ρ' (⟨_, hcH u huV⟩⁻¹ * ⟨_, hcH v hv⟩) = 1 := by
        rw [map_mul, map_inv, h, inv_mul_cancel]
      have h3 := (hker' _).1 h2
      simp only [Subgroup.coe_mul, InvMemClass.coe_inv] at h3
      have h4 := hQN _ (S.G1.inv_mem hc) _ h3
      have e : v = u * (c⁻¹ * ((c * u * c⁻¹)⁻¹ * (c * v * c⁻¹)) * c⁻¹⁻¹) := by group
      rw [e]
      exact (Uγ ⊔ Q).mul_mem (Subgroup.mem_sup_left huγ) (Subgroup.mem_sup_right h4)
  have hUγQ : Uγ ≤ Subgroup.normalizer (Q : Set G) := hUγH.trans (le_normalizer_pCoreOf 2 S.G1)
  have heq : ⁅U, Uγ⁆ ⊔ fsuV1 T V = ⁅U, Vγ⁆ ⊔ fsuV1 T V := by
    refine le_antisymm (sup_le_sup_right (Subgroup.commutator_mono le_rfl hF.Uγ_le_Vγ) _) ?_
    refine sup_le ?_ le_sup_right
    rw [Subgroup.commutator_le]
    intro u hu x hx
    have hx' : x ∈ ((Uγ ⊔ Q : Subgroup G) : Set G) := hVle' hx
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hUγQ] at hx'
    obtain ⟨a, ha, q, hq, rfl⟩ := Set.mem_mul.mp hx'
    have huq : u * q * u⁻¹ * q⁻¹ ∈ fsuV1 T V := by
      have := (fsuV1 T V).inv_mem (hF.toHypF91.commutator_mem_V₁ hq hu)
      have e : (q * u * q⁻¹ * u⁻¹)⁻¹ = u * q * u⁻¹ * q⁻¹ := by group
      rwa [e] at this
    have hcq := hF.toHypF91.conj_eq_of_mem_V₁ (hUγH ha) huq
    have e : ⁅u, a * q⁆ = ⁅u, a⁆ * (a * (u * q * u⁻¹ * q⁻¹) * a⁻¹) := by
      rw [commutatorElement_def, commutatorElement_def]; group
    rw [e, hcq]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.commutator_mem_commutator hu ha))
      (Subgroup.mem_sup_right huq)
  have hDHlt : DH < U := hDH
  have hgen := stab_eq_gen_of_struct S hF s hKT ρ hker hKA honto hDHlt
  obtain ⟨hV1, hle2, hnot⟩ := S.comm_le_Uγ_sup_V1_of_gen hNS h13315 h1356two hG1 hF h13314 s
    le_rfl hgen heq
  obtain ⟨-, hor⟩ := S.lemma13_8_10 hF s (le_of_eq (h1H.trans h1γ.symm)) h1γ hDHlt
  have hUDγ : ⁅U, Dγ⁆ = ⊥ := hor.resolve_left hV1
  obtain ⟨u, hu, y, hy, huy⟩ : ∃ u ∈ U, ∃ y ∈ Vγ, u * y * u⁻¹ * y⁻¹ ∉ Uγ := by
    by_contra hall
    push Not at hall
    exact hnot (Subgroup.commutator_le.mpr fun u hu y hy => by
      rw [commutatorElement_def]; exact hall u hu y hy)
  set u₀ : ↥S.G1 := ⟨(g : G)⁻¹ * u * (g : G), hUg u hu⟩ with hu₀
  have hu₀c : (u₀ : G) = (g : G)⁻¹ * u * (g : G) := rfl
  have hu₀8 : ρ' u₀ ∈ e8List := by
    refine hE8 u₀ ?_
    have h1 := hF.conjSub_inv_V_le_pCoreOf_L₁T s (W := U) (conjClosure_mono S.V3_le_V le_rfl)
    refine h1 ?_
    rw [mem_conjSub, inv_inv]
    show (g : G) * ((g : G)⁻¹ * u * (g : G)) * (g : G)⁻¹ ∈ U
    rw [show (g : G) * ((g : G)⁻¹ * u * (g : G)) * (g : G)⁻¹ = u by group]
    exact hu
  have hD'2 : (conjSub (g : G)⁻¹ Dγ).relIndex U = 2 := by
    have e : conjSub (g : G)⁻¹ Uγ = U := by
      rw [hUγdef, F8.Uγ, conjSub_conjSub_inv]
    rw [← e, show (conjSub (g : G)⁻¹ Dγ).relIndex (conjSub (g : G)⁻¹ Uγ) = Dγ.relIndex Uγ from
      Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj (g : G)⁻¹).injective]
    exact hDγ2
  have hu₀D : ∀ d ∈ conjSub (g : G)⁻¹ Dγ, (u₀ : G) * d * (u₀ : G)⁻¹ = d := by
    intro d hd
    have hd' : (g : G) * d * (g : G)⁻¹ ∈ Dγ := by
      have := mem_conjSub.mp hd
      rwa [inv_inv] at this
    have hc1 : u * ((g : G) * d * (g : G)⁻¹) * u⁻¹ * ((g : G) * d * (g : G)⁻¹)⁻¹ = 1 := by
      have := Subgroup.commutator_mem_commutator hu hd'
      rw [hUDγ, Subgroup.mem_bot, commutatorElement_def] at this
      exact this
    calc (u₀ : G) * d * (u₀ : G)⁻¹ =
        (g : G)⁻¹ * (u * ((g : G) * d * (g : G)⁻¹) * u⁻¹ * ((g : G) * d * (g : G)⁻¹)⁻¹) *
          (g : G) * d := by rw [hu₀c]; group
      _ = d := by rw [hc1]; group
  have hu₀t := S.rho_tv_of_centralizes hR hρ' hab hu₀8 hD'2 hu₀D
  have hy₀ : (g : G)⁻¹ * y * (g : G) ∈ conjClosure V S.G1 := by
    have := hy
    rwa [hVγdef, F8.Uγ, mem_conjSub] at this
  have hconjg : ∀ w : G, (u₀ : G) * ((g : G)⁻¹ * w * (g : G)) * (u₀ : G)⁻¹ *
      ((g : G)⁻¹ * w * (g : G))⁻¹ = (g : G)⁻¹ * (u * w * u⁻¹ * w⁻¹) * (g : G) := fun w => by
    rw [hu₀c]; group
  have hu₀1 : ρ' u₀ ≠ 1 := by
    intro h1
    apply huy
    have h2 := S.comm_QH_VH_mem hNS h13315 h1356two hG1 h13314 ((hker' _).1 h1) hy₀
    rw [hconjg] at h2
    have h3 : (g : G) * ((g : G)⁻¹ * (u * y * u⁻¹ * y⁻¹) * (g : G)) * (g : G)⁻¹ ∈ Uγ :=
      mul_mem_conjSub h2
    rwa [show (g : G) * ((g : G)⁻¹ * (u * y * u⁻¹ * y⁻¹) * (g : G)) * (g : G)⁻¹ =
      u * y * u⁻¹ * y⁻¹ by group] at h3
  have hx : ρ' u₀ = swap 0 1 ∨ ρ' u₀ = swap 2 3 ∨ ρ' u₀ = swap 4 5 := by
    rcases hu₀t with h | h
    · exact absurd h hu₀1
    · exact h
  have hzH : (g : G)⁻¹ * S.z * (g : G) ∈ S.G1 :=
    hUg _ (S.V3_le_UH (S.V1_le_V3 (S.mem_V1_iff.2 (Or.inr rfl))))
  have hUγN : Uγ ≤ Subgroup.normalizer (fsuV1 T V : Set G) := hUγH.trans hF.H_normalizes_V₁
  have hform : ∀ y₁ ∈ conjClosure V S.G1, (u₀ : G) * y₁ * (u₀ : G)⁻¹ * y₁⁻¹ ∉ U →
      ∃ a ∈ U, (u₀ : G) * y₁ * (u₀ : G)⁻¹ * y₁⁻¹ = a * ((g : G)⁻¹ * S.z * (g : G)) := by
    intro y₁ hy₁ hn
    have hy₁' : (g : G) * y₁ * (g : G)⁻¹ ∈ Vγ := by
      rw [hVγdef, F8.Uγ]; exact mul_mem_conjSub hy₁
    have h1 := hle2 (Subgroup.commutator_mem_commutator hu hy₁')
    rw [commutatorElement_def] at h1
    have h1' : u * ((g : G) * y₁ * (g : G)⁻¹) * u⁻¹ * ((g : G) * y₁ * (g : G)⁻¹)⁻¹ ∈
        ((Uγ ⊔ fsuV1 T V : Subgroup G) : Set G) := h1
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hUγN] at h1'
    obtain ⟨a, ha, w, hw, hawe⟩ := Set.mem_mul.mp h1'
    have e0 : (u₀ : G) * y₁ * (u₀ : G)⁻¹ * y₁⁻¹ =
        (g : G)⁻¹ * (u * ((g : G) * y₁ * (g : G)⁻¹) * u⁻¹ * ((g : G) * y₁ * (g : G)⁻¹)⁻¹) *
          (g : G) := by rw [hu₀c]; group
    have ha₀ : (g : G)⁻¹ * a * (g : G) ∈ U := by
      have ha' : a ∈ Uγ := ha
      rwa [hUγdef, F8.Uγ, mem_conjSub] at ha'
    rcases S.mem_V1_iff.1 hw with rfl | rfl
    · exfalso
      apply hn
      rw [e0, ← hawe, mul_one]
      exact ha₀
    · refine ⟨_, ha₀, ?_⟩
      rw [e0, ← hawe]
      group
  have htv : ∀ y₁ ∈ conjClosure V S.G1, ∀ y₂ ∈ conjClosure V S.G1,
      (u₀ : G) * y₁ * (u₀ : G)⁻¹ * y₁⁻¹ ∉ U → (u₀ : G) * y₂ * (u₀ : G)⁻¹ * y₂⁻¹ ∉ U →
      ((u₀ : G) * y₁ * (u₀ : G)⁻¹ * y₁⁻¹)⁻¹ * ((u₀ : G) * y₂ * (u₀ : G)⁻¹ * y₂⁻¹) ∈ U := by
    intro y₁ hy₁ y₂ hy₂ h1 h2
    obtain ⟨a₁, ha₁, e₁⟩ := hform y₁ hy₁ h1
    obtain ⟨a₂, ha₂, e₂⟩ := hform y₂ hy₂ h2
    rw [e₁, e₂]
    have := hUN _ (S.G1.inv_mem hzH) _ (U.mul_mem (U.inv_mem ha₁) ha₂)
    convert this using 1
    group
  exact S.false_of_transv hN' h13315 hNS h1356two hG1 h13314 hKT honto' hKA' hker' hQT hVle
    hF.F911_2 hF.toHypF91.elemAbelian hx htv

end Setting4

theorem lemma13834SixOneTwo_holds (h13315 : Stmt13_3_15)
    (h1356two : Input1356Two) (h13314 : Stmt13_3_14) : Lemma13834SixOneTwo := by
  intro G _ _ T L V S hNS hNU hG1 hab hF hst hhat hlt γ γ' g s hpos hle hQ c hc hcV
  obtain ⟨K, -, hKT, hL1K, -, hcase, -⟩ := hst
  rcases hcase with ⟨-, ρ, hker, hKA, honto, hβ⟩ | ⟨hh, -⟩
  swap
  · exact absurd hh hhat
  have h2 := S.lemma13_8_34_two hNS h13315 h1356two hG1 h13314 hF s hKT hL1K ρ hker hKA honto hβ
    hc hcV hpos
  have hDH := DH_lt_of_forall hF hlt s
  have h1H := (S.lemma13_8_10 hF s hle h2 hDH).1
  refine ⟨⟨S.A1_le_UH_of hNS h13315 h1356two hG1 h13314 hF s hKT hL1K ρ hker hKA honto hβ hc hcV
    h2 h1H hDH, ?_⟩, h2⟩
  obtain ⟨δ, δ', k, y, sk, -, hyδ, eU, eB, eDH, eDγ⟩ :=
    hF.exists_symmetric_setup s (hF.not_Vγ_le_ballStab_of_lt s (hlt γ γ' g s))
  have hky : ((k : G))⁻¹ * (y : G) ∈ S.G1 := by
    have h1 : (k⁻¹ * y) • F8.γ₁ T L S.G1 = F8.γ₁ T L S.G1 := by
      rw [mul_smul, hyδ, ← sk.edge₁, inv_smul_smul]
    have := mem_stab_of_smul_eq h1
    rw [stab_γ₁ hF.amalgamHypV.le₂] at this
    simpa using this
  have eA : F8.A₁ (fsuV1 T V) (k : G) = conjSub (y : G) (fsuV1 T V) := by
    have e : (y : G) = (k : G) * ((k : G)⁻¹ * (y : G)) := by group
    rw [F8.A₁, e, conjSub_mul, F7.conjSub_eq_of_mem_normalizer (hF.H_normalizes_V₁ hky)]
  obtain ⟨c', hc', hc'V⟩ := exists_conj_Vγ_le hF sk
  have h1δ : mIdx (F8.Uγ S.V3 S.G1 (k : G)) (F8.Dγ S.V3 (fsuV1 T V) S.G1 (k : G)) = 1 := by
    rw [eU, eDγ, mIdx_conjSub]
    exact h1H
  have h1Hk : mIdx (conjClosure S.V3 S.G1) (F8.DH S.V3 (fsuV1 T V) S.G1 (k : G)) = 1 := by
    rw [eDH, ← eB, mIdx_conjSub]
    exact h2
  have hDHk := DH_lt_of_forall hF hlt sk
  have h := S.A1_le_UH_of hNS h13315 h1356two hG1 h13314 hF sk hKT hL1K ρ hker hKA honto hβ hc'
    hc'V h1δ h1Hk hDHk
  rw [eA, ← eB] at h
  have := conjSub_mono ((y : G))⁻¹ h
  rwa [conjSub_conjSub_inv, conjSub_conjSub_inv] at this

end CFSG.Quasithin.H13.A6
