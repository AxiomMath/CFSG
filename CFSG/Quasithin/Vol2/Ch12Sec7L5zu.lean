module

public import CFSG.Quasithin.Vol2.Ch12Sec7L5zt
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4Held
public import CFSG.Quasithin.Vol2.Ch12Sec7L5zh

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.S127.L715.Set714.N3

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.ASInputs S127 S127.L715 S127.L716
  G31 CFSG.LargeExtraspecial Module QuadraticMap
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} {t z : G}
  {s : Set714 G T L V t z} {h1222 : Stmt12_2_2} (hn : s.N3 h1222)
include hn

theorem nonempty_centralizer_mulEquiv
    (hU : autOn (U714 T L V z) V = autOn (R1 T L V) V) :
    Nonempty (Subgroup.centralizer ({z} : Set G) ≃* Subgroup.centralizer
      ({DW.cornerTransvection (N := 5) (by norm_num)} : Set (Matrix.SpecialLinearGroup (Fin 5)
        (ZMod 2)))) := by
  obtain ⟨W₂, hc, hinv⟩ := hn.exists_W2 hU
  have hts := hn.q_W2 hU hc hinv
  have hQG := hn.setting_QG
  have hpolW₂ : ∀ a ∈ W₂, ∀ b ∈ W₂, polar hn.setting.q a b = 0 := by
    intro a ha b hb
    rw [polar, hts _ (Submodule.add_mem _ ha hb), hts a ha, hts b hb]
    simp
  have hUQ : U714 T L V z ≤ hn.setting.QG := by rw [hQG]; exact s.U_le_Qz hn
  have hU2 : IsElemAbelian 2 (U714 T L V z) :=
    ⟨⟨⟨fun a b => Subtype.ext (s.comm_U hn a.2 b.2)⟩⟩, fun x hx => hn.sq_U x hx⟩
  have hV2 : IsElemAbelian 2 (hn.setting.clPre W₂) := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx =>
      (hn.setting.q_cl_eq_zero_iff hx.1).mp (hts _ hx.2)⟩
    exact (hn.setting.polar_cl_eq_zero_iff a.2.1 b.2.1).mp (hpolW₂ _ a.2.2 _ b.2.2)
  have hU12 : U714 T L V z ⊓ hn.setting.clPre W₂ = Subgroup.zpowers hn.setting.z := by
    apply le_antisymm
    · intro x hx
      have h0 := Submodule.disjoint_def.mp hc.1 _ (hn.setting.cl_mem_clSub hx.1 hx.2.1) hx.2.2
      rw [hn.setting.cl_eq_zero_iff hx.2.1] at h0
      rcases h0 with h | h
      · rw [h]
        exact Subgroup.one_mem _
      · rw [h]
        exact Subgroup.mem_zpowers _
    · exact Subgroup.zpowers_le_of_mem ⟨s.z_mem_U, hn.setting.z_mem_clPre W₂⟩
  have hU12' : U714 T L V z ⊔ hn.setting.clPre W₂ = hn.setting.QG := by
    apply le_antisymm (sup_le hUQ (hn.setting.clPre_le_QG W₂))
    intro q hq
    have hmem : hn.setting.cl q ∈ hn.setting.clSub (U714 T L V z) ⊔ W₂ := by
      rw [hc.2.eq_top]
      exact Submodule.mem_top
    obtain ⟨w₁, hw₁, w₂, hw₂, hw⟩ := Submodule.mem_sup.mp hmem
    obtain ⟨u, hu, huQ, rfl⟩ := hn.setting.mem_clSub_iff.mp hw₁
    have hq' : u⁻¹ * q ∈ hn.setting.clPre W₂ := by
      refine ⟨hn.setting.QG.mul_mem (hn.setting.QG.inv_mem huQ) hq, ?_⟩
      rw [hn.setting.cl_mul (hn.setting.QG.inv_mem huQ) hq, hn.setting.cl_inv huQ, ← hw]
      have e : hn.setting.cl u + (hn.setting.cl u + w₂) = w₂ := by
        rw [← add_assoc, CFSG.RankThree.OrthogonalInvolutions.add_self_vec (ZMod 2), zero_add]
      rw [e]
      exact hw₂
    have e : q = u * (u⁻¹ * q) := by group
    rw [e]
    exact Subgroup.mul_mem_sup hu hq'
  have hMU : hn.setting.M ≤ Subgroup.normalizer (U714 T L V z : Set G) := hn.Gz_le_normalizer_U
  have hMV₂ : hn.setting.M ≤ Subgroup.normalizer (hn.setting.clPre W₂ : Set G) := by
    intro m hm
    refine Subgroup.mem_normalizer_fintype fun x hx => ⟨hn.setting.conj_mem_QG hm hx.1, ?_⟩
    rw [← hn.setting.ρ_cl ⟨m, hm⟩ hx.1]
    exact hinv ⟨m, hm⟩ _ hx.2
  have hidx : Nat.card hn.setting.M = 168 * Nat.card hn.setting.Q := by
    rw [← hn.setting.card_QG_eq_card_Q, hQG, hn.card_Q]
    show Nat.card ↥(Subgroup.centralizer ({z} : Set G)) = _
    rw [hn.Gz_eq_H, hn.card_H]
    norm_num
  have hVM : V ≤ hn.setting.M := s.V_le_Gz h1222
  have hVab : IsElemAbelian 2 V :=
    ⟨s.isMulCommutative_V h1222, fun x hx => S127.sq_eq_one_of_mem s.setting.hyp.hyp hx⟩
  have hV64 : Nat.card ↥V = 64 := by
    rw [(S127.card_eq_of_1222 h1222 s.setting.hyp).2.1]
    norm_num
  have hVQ : Nat.card ↥(hn.setting.QG ⊓ V) = 16 := by
    rw [hQG, inf_comm, hn.card_VQ]
  exact CFSG.ComponentClassification.AS81.nonempty_centralizer_mulEquiv_sl5 hn.setting
    hn.setting_width
    hUQ (hn.setting.clPre_le_QG W₂) hU2 hV2 hU12 hU12' hMU hMV₂ hidx hVM hVab hV64 hVQ

theorem exists_conj_ne :
    ∃ g : G, g⁻¹ * z * g ∈ pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) ∧ g⁻¹ * z * g ≠ z := by
  obtain ⟨x, -, hx3, hxN, hxC⟩ := s.exists_x h1222
  have hp := CFSG.ComponentClassification.AS81.pCoreOf_two_eq_QG hn.setting
  rw [hn.setting_QG] at hp
  change pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) = s.Qz h1222 at hp
  rw [hp]
  have hxz : x * z * x⁻¹ ∈ V1 T L V := (Subgroup.mem_normalizer_iff.mp hxN z).mp s.mem
  refine ⟨x⁻¹, ?_, ?_⟩
  · rw [inv_inv]
    exact s.U_le_Qz hn (le_conjClosure _ _ hxz)
  · rw [inv_inv]
    intro hfix
    apply hxC
    obtain ⟨v, hv, hvz⟩ := s.exists_v h1222
    have hV1 : ∀ w ∈ V1 T L V, w ∈ Subgroup.zpowers z ∨ v⁻¹ * w ∈ Subgroup.zpowers z := by
      intro w hw
      by_cases hwz : w ∈ Subgroup.zpowers z
      · exact Or.inl hwz
      · right
        have hzV1 : Subgroup.zpowers z ≤ V1 T L V := Subgroup.zpowers_le_of_mem s.mem
        have hcard : Nat.card ↥(V1 T L V) ≤ 2 * Nat.card ↥(V1 T L V ⊓ Subgroup.zpowers z) := by
          rw [inf_of_le_right hzV1, Nat.card_zpowers, s.orderOf_z, s.card_V1 h1222]
        exact mul_mem_of_card_le hcard v hv w hw hvz hwz
    have hxzc : ∀ c ∈ Subgroup.zpowers z, x * c * x⁻¹ = c := by
      intro c hc
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
      rw [← conj_zpow, hfix]
    have hxv : x * v * x⁻¹ = v := by
      have hxvV1 : x * v * x⁻¹ ∈ V1 T L V := (Subgroup.mem_normalizer_iff.mp hxN v).mp hv
      rcases hV1 _ hxvV1 with h | h
      · exfalso
        apply hvz
        have h2 : x⁻¹ * (x * v * x⁻¹) * x = x * v * x⁻¹ := by
          calc x⁻¹ * (x * v * x⁻¹) * x
              = x⁻¹ * (x * (x * v * x⁻¹) * x⁻¹) * x := by rw [hxzc _ h]
            _ = x * v * x⁻¹ := by group
        have e : v = x⁻¹ * (x * v * x⁻¹) * x := by group
        rw [e, h2]
        exact h
      · obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
        set c := z ^ k with hc
        have hcz : c ∈ Subgroup.zpowers z := Subgroup.zpow_mem_zpowers z k
        have hxv' : x * v * x⁻¹ = v * c := by rw [hk]; group
        have hc2 : c * c = 1 := by
          rw [hc, ← zpow_add, ← two_mul, zpow_mul]
          rw [show z ^ (2 : ℤ) = 1 by rw [zpow_two, s.z_mul_z]]
          exact one_zpow k
        have h3 : x ^ 3 * v * (x ^ 3)⁻¹ = v * c := by
          have e : x ^ 3 * v * (x ^ 3)⁻¹ = x * (x * (x * v * x⁻¹) * x⁻¹) * x⁻¹ := by
            rw [pow_succ, pow_succ, pow_one]
            group
          rw [e, hxv']
          have e1 : x * (v * c) * x⁻¹ = (x * v * x⁻¹) * (x * c * x⁻¹) := by group
          rw [e1, hxv', hxzc c hcz, mul_assoc v c c, hc2, mul_one, hxv']
        rw [hx3, one_mul, inv_one, mul_one] at h3
        have hc1 : c = 1 := by
          have := congrArg (v⁻¹ * ·) h3
          simpa using this.symm
        rw [hxv', hc1, mul_one]
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rcases hV1 w hw with h | h
    · have := hxzc w h
      calc w * x = x * w * x⁻¹ * x := by rw [this]
        _ = x * w := by group
    · have hw' : w = v * (v⁻¹ * w) := by group
      have h1 := hxzc _ h
      have : x * w * x⁻¹ = w := by
        rw [hw']
        have e : x * (v * (v⁻¹ * w)) * x⁻¹ = (x * v * x⁻¹) * (x * (v⁻¹ * w) * x⁻¹) := by group
        rw [e, hxv, h1]
      calc w * x = x * w * x⁻¹ * x := by rw [this]
        _ = x * w := by group

end CFSG.Quasithin.H13.S127.L715.Set714.N3

namespace CFSG.Quasithin.H13.S127.L715

open CFSG.Open CFSG.Blueprint CFSG.Quasithin S127 S127.L716

theorem ident12714R1_of
    (h1222 : Stmt12_2_2) (h1226 : Stmt12_2_6) (h129 : Stmt12_2_9) (h1241 : Lemma12_4_1)
    (h10 : Lemma12_7_10) (h11 : Lemma12_7_11)
    (h36 : CFSG.QuasithinUnique.Vol2Native.A36CoreForSQTKCat) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (h39 : A39ForSQTK) (hrank : Lemma122Rank) : Ident12714R1 := by
  intro G _ _ T L V t hS z hz hz1 hTz hVz hU
  have s : Set714 G T L V t z := ⟨hS, hz, hz1, hTz, hVz⟩
  have hcomm : IsMulCommutative ↥(Ut T L V z) := (s.elemAbelian_Ut h1222).1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 ↥(Ut T L V z) := fun w =>
    ⟨1, by rw [pow_one]; exact Subtype.ext ((s.elemAbelian_Ut h1222).2 _ w.2)⟩
  obtain ⟨d, hd⟩ := hp.exists_card_eq
  have hd5 := s.dim_le_five h1222 h36 h37 h38 h39 hU hd
  have hd3 : 3 ≤ d := by
    have h8 := (s.Hs_eq_top h1222 h37 h38 h39 hU).2
    rw [hd] at h8
    by_contra hlt
    push Not at hlt
    have : 2 ^ d ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hd' : d = 3 := by
    interval_cases d
    · rfl
    · exact (s.dim_ne_four h1222 h1226 h129 h1241 h10 h11 h37 h38 h39 hU hd).elim
    · exact (s.dim_ne_five h1222 h36 h37 h38 h39 hrank hU hd).elim
  subst hd'
  have hn := s.n3 h1222 h1226 h129 h1241 h10 h11 h37 h38 h39 hU hd
  have ht : transvection15 = LargeExtraspecial.DW.cornerTransvection (N := 5) (by norm_num) := rfl
  rw [ht]
  exact ⟨s.orderOf_z, hn.nonempty_centralizer_mulEquiv hU, hn.exists_conj_ne⟩

end CFSG.Quasithin.H13.S127.L715
