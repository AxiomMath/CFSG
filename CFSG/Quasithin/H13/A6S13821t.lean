module

public import CFSG.Quasithin.H13.A6S13821n
public import CFSG.Quasithin.H13.A6S13821s
public import CFSG.Quasithin.H13.A6S1372L19b
public import CFSG.Quasithin.H13.A6S13821d
public import CFSG.Quasithin.H13.A6S13825p
public import CFSG.Quasithin.H13.L32AStRec

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.F7

namespace A6S19

open CFSG.Quasithin.H6

theorem borel_eq_P0 : H6.borel = SL3.P0 := by
  ext g
  rw [mem_borel_iff]
  show IsB g ↔ SL3.InX1 g ∧ SL3.InX2 g
  revert g
  decide +kernel

theorem Ll_eq_X2 : H6.Ll = SL3.X2 := rfl

theorem Lp_eq_X1 : H6.Lp = SL3.X1 := by
  ext g
  rw [H6.Lp, MulAction.mem_stabilizer_iff]
  show g • (![1, 0, 0] : V3) = ![1, 0, 0] ↔ SL3.InX1 g
  revert g
  decide +kernel

end A6S19

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem relIndex_T_L1T (hhat : ¬ IsHatA6 L) :
    T.relIndex (S.L1 ⊔ T) = 3 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hL3 := S.relIndex_pCoreOf_L1 hhat
  have hPT : pCoreOf 2 S.L1 ≤ S.L1 ⊓ T := le_inf (pCoreOf_le 2 _) S.O2L1_le_T
  have hdvd : (S.L1 ⊓ T).relIndex S.L1 ∣ 3 := by
    rw [← hL3]
    exact Subgroup.relIndex_dvd_of_le_left S.L1 hPT
  have hne : (S.L1 ⊓ T).relIndex S.L1 ≠ 1 := by
    intro h1
    rw [Subgroup.relIndex_eq_one] at h1
    exact S.not_isPGroup_two_L1 (S.h13.sylow.1.to_le (h1.trans inf_le_right))
  have h3 : (S.L1 ⊓ T).relIndex S.L1 = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact absurd h hne
    · exact h
  have hXc := L32A.C.card_sup_eq S.T_le_normalizer_L1
  rw [sup_comm] at hXc
  have h1 := Subgroup.relIndex_mul_card S.L1 T
  have h2 := Subgroup.relIndex_mul_card (S.L1 ⊓ T) S.L1
  rw [inf_eq_left.mpr inf_le_left] at h2
  have h4 := Subgroup.relIndex_mul_card T (S.L1 ⊔ T)
  rw [inf_eq_left.mpr (le_sup_right : T ≤ S.L1 ⊔ T)] at h4
  have hpos : 0 < Nat.card ↥T := Nat.card_pos
  have key : T.relIndex (S.L1 ⊔ T) * Nat.card ↥T = 3 * Nat.card ↥T := by
    calc T.relIndex (S.L1 ⊔ T) * Nat.card ↥T = Nat.card ↥(S.L1 ⊔ T) := h4
      _ = S.L1.relIndex T * Nat.card ↥S.L1 := hXc
      _ = S.L1.relIndex T * ((S.L1 ⊓ T).relIndex S.L1 * Nat.card ↥(S.L1 ⊓ T)) := by rw [h2]
      _ = (S.L1 ⊓ T).relIndex S.L1 * (S.L1.relIndex T * Nat.card ↥(S.L1 ⊓ T)) := by ring
      _ = 3 * Nat.card ↥T := by rw [h1, h3]
  exact Nat.eq_of_mul_eq_mul_right hpos key

theorem exists_theta_l32 (hS : S.Hyp138) {H : Subgroup G}
    (hH : H ∈ S.Hz) (hhat : ¬ IsHatA6 L) (hP : IsPSL 3 2 1 ↥(S.KSt H H)) :
    ∃ θ : ↥H →* H6.Γ, Function.Surjective θ ∧ (∀ h : ↥H, θ h = 1 ↔ (h : G) ∈ pCoreOf 2 H) ∧
      (T.subgroupOf H).map θ = H6.borel ∧ ((S.L1 ⊔ T).subgroupOf H).map θ = H6.Ll := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF := (hS.hF H hH).toHypF91
  set φ := S1549C.starHom hF with hφ
  obtain ⟨e₀⟩ := isPSL_three_two_iff.mp hP
  set φ' : ↥H →* ↥(S.KSt H H) :=
    φ.codRestrict _ (fun h => by rw [S.kst_top hF]; exact ⟨h, rfl⟩) with hφ'
  have hφ's : Function.Surjective φ' := by
    rintro ⟨y, hy⟩
    have hy' := hy
    rw [S.kst_top hF] at hy'
    obtain ⟨h, rfl⟩ := hy'
    exact ⟨h, rfl⟩
  set θ₀ : ↥H →* H6.Γ := e₀.toMonoidHom.comp φ' with hθ₀
  have hθ₀s : Function.Surjective θ₀ := e₀.surjective.comp hφ's
  have hker₀ : ∀ h : ↥H, θ₀ h = 1 ↔ (h : G) ∈ pCoreOf 2 H := fun h => by
    rw [hθ₀, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff,
      ← (S1549C.starHom_eq_one_iff hF h)]
    exact ⟨fun h1 => congrArg Subtype.val h1, fun h1 => Subtype.ext h1⟩
  have hTH : T ≤ H := le_sup_right.trans hH.1.1
  have hTsylH : IsSylowTwoOf T H := isSylowTwoOf_of_quasithinIsSylowTwo S.h13.sylow hTH
  have hS2 : IsPGroup 2 (T.subgroupOf H) :=
    hTsylH.2.1.comap_of_injective H.subtype H.subtype_injective
  have hSi : ¬ 2 ∣ (T.subgroupOf H).index := hTsylH.2.2
  obtain ⟨g, hg⟩ := L32A.C.exists_conj_map_eq_of_sylow θ₀ hθ₀s hS2 hSi SL3.P0_sylow.1
    SL3.P0_sylow.2
  set θ₁ : ↥H →* H6.Γ := (MulAut.conj g⁻¹).toMonoidHom.comp θ₀ with hθ₁
  have hθ₁s : Function.Surjective θ₁ := (MulAut.conj g⁻¹).surjective.comp hθ₀s
  have hker₁ : ∀ h : ↥H, θ₁ h = 1 ↔ (h : G) ∈ pCoreOf 2 H := fun h => by
    rw [hθ₁, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff, hker₀]
  have hθ₁T : (T.subgroupOf H).map θ₁ = SL3.P0 := by
    rw [← hg, Subgroup.map_map]
  have hQT : pCoreOf 2 H ≤ T := pCoreOf_le_of_sylow S.h13.sylow hTH
  have hkerT : θ₁.ker ≤ T.subgroupOf H := fun h hh =>
    Subgroup.mem_subgroupOf.mpr (hQT ((hker₁ h).mp hh))
  have hTL : T ≤ S.L1 ⊔ T := le_sup_right
  set Y := ((S.L1 ⊔ T).subgroupOf H).map θ₁ with hY
  have hPY : SL3.P0 ≤ Y := by
    rw [← hθ₁T]
    exact Subgroup.map_mono fun x hx =>
      Subgroup.mem_subgroupOf.mpr (hTL (Subgroup.mem_subgroupOf.mp hx))
  have hidx : SL3.P0.relIndex Y = 3 := by
    rw [← hθ₁T, hY, Subgroup.relIndex_map_map, sup_eq_left.mpr hkerT,
      sup_eq_left.mpr (hkerT.trans fun x hx =>
        Subgroup.mem_subgroupOf.mpr (hTL (Subgroup.mem_subgroupOf.mp hx))),
      Subgroup.relIndex_subgroupOf hH.1.1]
    exact S.relIndex_T_L1T hhat
  have hPidx : SL3.P0.index = 21 := by
    have h1 := Subgroup.card_mul_index SL3.P0
    rw [SL3.card_P0, SL3.card_S] at h1
    omega
  rcases SL3.overgroups_SL3 Y hPY with h | h | h | h
  · rw [h, Subgroup.relIndex_self] at hidx
    omega
  ·
    refine ⟨H6.graph.toMonoidHom.comp θ₁, H6.graph.surjective.comp hθ₁s, fun h' => ?_, ?_, ?_⟩
    · rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff, hker₁]
    · rw [← Subgroup.map_map, hθ₁T, ← A6S19.borel_eq_P0]
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact (H6.graph_mem_borel_iff y).mpr hy
      · intro hx
        refine ⟨H6.graph x, (H6.graph_mem_borel_iff _).mp ?_, ?_⟩
        · rwa [H6.graph_apply, H6.graph_apply, H6.graphFun_graphFun]
        · show H6.graph (H6.graph x) = x
          rw [H6.graph_apply, H6.graph_apply, H6.graphFun_graphFun]
    · rw [← Subgroup.map_map, ← hY, h, ← A6S19.Lp_eq_X1]
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact (H6.graph_mem_Ll_iff y).mpr hy
      · intro hx
        refine ⟨H6.graph x, (H6.graph_mem_Ll_iff _).mp ?_, ?_⟩
        · rwa [H6.graph_apply, H6.graph_apply, H6.graphFun_graphFun]
        · show H6.graph (H6.graph x) = x
          rw [H6.graph_apply, H6.graph_apply, H6.graphFun_graphFun]
  ·
    exact ⟨θ₁, hθ₁s, hker₁, by rw [hθ₁T, A6S19.borel_eq_P0], by rw [← hY, h, A6S19.Ll_eq_X2]⟩
  · rw [h, Subgroup.relIndex_top_right, hPidx] at hidx
    omega

omit S in
theorem map_eq_top_of_cComp {H : Subgroup G} {θ : ↥H →* H6.Γ} (hθs : Function.Surjective θ)
    (hker : ∀ h : ↥H, θ h = 1 ↔ (h : G) ∈ pCoreOf 2 H) {K : Subgroup G} (hK : K ∈ cComp H)
    (hKn : H ≤ Subgroup.normalizer (K : Set G)) : (K.subgroupOf H).map θ = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsimp := CFSG.QuasithinUnique.Vol2Native.A312L.Seven.slThree_isSimple
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hKnorm : ((K.subgroupOf H).map θ).Normal :=
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mpr hKn).map θ hθs
  have hne : (K.subgroupOf H).map θ ≠ ⊥ := by
    intro hb
    have hle : K ≤ pCoreOf 2 H := fun k hk => by
      have h1 : θ ⟨k, hKH hk⟩ ∈ (K.subgroupOf H).map θ := ⟨⟨k, hKH hk⟩, hk, rfl⟩
      rw [hb, Subgroup.mem_bot] at h1
      exact (hker _).mp h1
    have h2 : IsPGroup 2 ↥K := (pCoreOf_isPGroup 2 H).to_le hle
    have : Group.IsNilpotent ↥K := h2.isNilpotent
    have : Group.IsPerfect ↥K := Subgroup.isPerfect_iff.mpr (perfect_of_mem_cComp hK)
    have : Nontrivial ↥K := (Subgroup.nontrivial_iff_ne_bot K).mpr (ne_bot_of_mem_cComp hK)
    exact Group.IsPerfect.not_isSolvable ↥K inferInstance
  exact (IsSimpleGroup.eq_bot_or_eq_top_of_normal _).resolve_left hne

theorem exists_cComp_l32 (h16 : Lem13816) (hS : S.Hyp138)
    {H : Subgroup G} (hH : H ∈ S.Hz) (hhat : ¬ IsHatA6 L) (hP : IsPSL 3 2 1 ↥(S.KSt H H)) :
    ∃ K ∈ cComp H, H ≤ Subgroup.normalizer (K : Set G) ∧ H = K ⊔ (S.L1 ⊔ T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨θ, hθs, hker, -, -⟩ := S.exists_theta_l32 hS hH hhat hP
  have hsimp := CFSG.QuasithinUnique.Vol2Native.A312L.Seven.slThree_isSimple
  have hnsΓ : ¬ Group.IsSolvable H6.Γ := fun hs =>
    CFSG.QuasithinUnique.Vol2Native.A312L.Seven.slThree_nonabelian.elim fun a ha =>
      ha.elim fun b hab => hab ((IsSimpleGroup.comm_iff_isSolvable.mpr hs) a b)
  have hnsH : ¬ Group.IsSolvable ↥H := fun hs => hnsΓ (Group.isSolvable_of_surjective hθs)
  obtain ⟨K, hK, -⟩ := exists_cComp_le_of_not_solvable (le_refl H)
    (by rw [Subgroup.subgroupOf_self]; exact Subgroup.normal_top) hnsH
  have hKn : H ≤ Subgroup.normalizer (K : Set G) := (h16 G T L V S hS H hH K hK).1.1
  have hKH : K ≤ H := le_of_mem_cComp hK
  refine ⟨K, hK, hKn, le_antisymm ?_ (sup_le hKH hH.1.1)⟩
  have htop := map_eq_top_of_cComp hθs hker hK hKn
  intro h hh
  obtain ⟨k, hk, hkh⟩ := (htop ▸ Subgroup.mem_top (θ ⟨h, hh⟩) :
    θ ⟨h, hh⟩ ∈ (K.subgroupOf H).map θ)
  have h1 : θ (k⁻¹ * ⟨h, hh⟩) = 1 := by rw [map_mul, map_inv, hkh, inv_mul_cancel]
  have h2 := (hker _).mp h1
  have hQT : pCoreOf 2 H ≤ T := pCoreOf_le_of_sylow S.h13.sylow (le_sup_right.trans hH.1.1)
  have e : h = (k : G) * ((k⁻¹ * ⟨h, hh⟩ : ↥H) : G) := by simp
  rw [e]
  exact mul_mem (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mp hk))
    (Subgroup.mem_sup_right (Subgroup.mem_sup_right (hQT h2)))

end Setting4

end CFSG.Quasithin.H13.A6
