module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.H13.A6S1385b

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.F7
open scoped Pointwise

namespace A6Hm

theorem pow_sixty_perm : ∀ σ : Perm (Fin 6), Perm.sign σ = 1 → σ ^ 60 = 1 := by
  intro σ _
  rw [← orderOf_dvd_iff_pow_eq_one, ← Equiv.Perm.lcm_cycleType, Multiset.lcm_dvd]
  intro n hn
  have h1 := Equiv.Perm.two_le_of_mem_cycleType hn
  have h2 : n ≤ 6 := (Equiv.Perm.le_card_support_of_mem_cycleType hn).trans
    ((Finset.card_le_univ _).trans_eq (Fintype.card_fin 6))
  interval_cases n <;> norm_num

theorem pow_sixty (x : alternatingGroup (Fin 6)) : x ^ 60 = 1 :=
  Subtype.ext (by simpa using pow_sixty_perm x (Perm.mem_alternatingGroup.1 x.2))

theorem card_le_factorial_index' {X : Type*} [Group X] [Finite X] [IsSimpleGroup X]
    {M : Subgroup X} (hM : M ≠ ⊤) : Nat.card X ≤ M.index.factorial := by
  have hcore : M.normalCore = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal M.normalCore with h | h
    · exact h
    · exact absurd (top_le_iff.mp (h ▸ M.normalCore_le)) hM
  have hinj : Function.Injective (MulAction.toPermHom X (X ⧸ M)) := by
    rw [← MonoidHom.ker_eq_bot_iff, ← Subgroup.normalCore_eq_ker, hcore]
  have : Finite (X ⧸ M) := inferInstance
  calc Nat.card X ≤ Nat.card (Perm (X ⧸ M)) := Nat.card_le_card_of_injective _ hinj
    _ = (Nat.card (X ⧸ M)).factorial := Nat.card_perm
    _ = M.index.factorial := by rw [Subgroup.index]

theorem card_eq_24 {P D : Subgroup (alternatingGroup (Fin 6))} (hP : P ≠ ⊤) (hDP : D ≤ P)
    (hD : Nat.card D = 8) {x : alternatingGroup (Fin 6)} (hxP : x ∈ P) (hx3 : x ^ 3 = 1)
    (hx1 : x ≠ 1) : Nat.card P = 24 := by
  have hA : Nat.card (alternatingGroup (Fin 6)) = 360 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]; rfl
  have : IsSimpleGroup (alternatingGroup (Fin 6)) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num)
  have h8 : 8 ∣ Nat.card P := by
    rw [← hD]
    exact Subgroup.card_dvd_of_le hDP
  have h3 : 3 ∣ Nat.card P := by
    have ho : orderOf x = 3 := orderOf_eq_prime hx3 hx1
    rw [← ho]
    have : orderOf (⟨x, hxP⟩ : ↥P) = orderOf x := Subgroup.orderOf_mk x hxP
    rw [← this]
    exact orderOf_dvd_natCard _
  have hdvd : Nat.card P ∣ 360 := by rw [← hA]; exact Subgroup.card_subgroup_dvd_card P
  have hidx := card_le_factorial_index' hP
  rw [hA] at hidx
  have hmul := Subgroup.card_mul_index P
  rw [hA] at hmul
  have hi6 : 6 ≤ P.index := by
    by_contra h
    push Not at h
    interval_cases hi : P.index <;> simp [Nat.factorial] at hidx
  have hle : Nat.card P ≤ 60 := by
    have h1 : Nat.card P * 6 ≤ 360 := hmul ▸ Nat.mul_le_mul_left _ hi6
    omega
  have h24 : 24 ∣ Nat.card P := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h8 h3
  obtain ⟨m, hm⟩ := h24
  have hpos : 0 < Nat.card P := Nat.card_pos
  have hm2 : m ≤ 2 := by omega
  interval_cases m
  · omega
  · omega
  · exfalso
    rw [hm] at hdvd
    norm_num at hdvd

theorem conj_of_card_24 {Γ : Type*} [Group Γ] [Finite Γ] (hΓ : Nat.card Γ = 24) {x y : Γ}
    (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) (hy3 : y ^ 3 = 1) (hy1 : y ≠ 1) :
    ∃ g : Γ, y = g * x * g⁻¹ ∨ y = g * x⁻¹ * g⁻¹ := by
  have h3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hfac : (Nat.card Γ).factorization 3 = 1 := by
    rw [hΓ, show (24 : ℕ) = 2 ^ 3 * 3 ^ 1 by norm_num, Nat.factorization_mul (by norm_num)
      (by norm_num), Nat.Prime.factorization_pow Nat.prime_two, Nat.Prime.factorization_pow
      Nat.prime_three]
    simp
  have hox : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  have hoy : orderOf y = 3 := orderOf_eq_prime hy3 hy1
  let Px : Sylow 3 Γ := Sylow.ofCard (Subgroup.zpowers x) (by
    rw [Nat.card_zpowers, hox, hfac, pow_one])
  let Py : Sylow 3 Γ := Sylow.ofCard (Subgroup.zpowers y) (by
    rw [Nat.card_zpowers, hoy, hfac, pow_one])
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Γ Px Py
  have hgy : y ∈ MulAut.conj g • (Subgroup.zpowers x) := by
    have h1 : ((g • Px : Sylow 3 Γ) : Subgroup Γ) = (Py : Subgroup Γ) := by rw [hg]
    rw [Sylow.coe_subgroup_smul] at h1
    have h2 : y ∈ (Py : Subgroup Γ) := Subgroup.mem_zpowers y
    rw [← h1] at h2
    exact h2
  obtain ⟨z, hz, hzy⟩ := Subgroup.mem_smul_pointwise_iff_exists _ _ _ |>.1 hgy
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
  refine ⟨g, ?_⟩
  have hj : x ^ j = x ^ (j % 3) := by
    conv_lhs => rw [← Int.mul_ediv_add_emod j 3]
    rw [zpow_add, zpow_mul, show (x : Γ) ^ (3 : ℤ) = 1 by exact_mod_cast hx3, one_zpow, one_mul]
  have hjr : j % 3 = 0 ∨ j % 3 = 1 ∨ j % 3 = 2 := by omega
  have hzy' : g * x ^ j * g⁻¹ = y := hzy
  rcases hjr with h0 | h1 | h2
  · exfalso
    rw [hj, h0, zpow_zero] at hzy'
    apply hy1
    rw [← hzy']
    group
  · left
    rw [hj, h1, zpow_one] at hzy'
    exact hzy'.symm
  · right
    have e : x ^ (2 : ℤ) = x⁻¹ := by
      rw [show (2 : ℤ) = 3 - 1 by norm_num, zpow_sub, zpow_one,
        show (x : Γ) ^ (3 : ℤ) = 1 by exact_mod_cast hx3, one_mul]
    rw [hj, h2, e] at hzy'
    exact hzy'.symm

end A6Hm

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)

theorem exists_alpha (hS : S.Hyp138) {H : Subgroup G} (hH : H ∈ S.Hz) {K : Subgroup G}
    (hKH : K ≤ H) (h6 : IsAlt 6 ↥(S.KSt H K)) :
    ∃ α : ↥K →* alternatingGroup (Fin 6), Function.Surjective α ∧
      ∀ k : ↥K, α k = 1 ↔ (k : G) ∈ pCoreOf 2 H := by
  obtain ⟨ι⟩ := h6
  have hF1 := (hS.hF H hH).toHypF91
  have hV₁ : H ≤ Subgroup.normalizer (fsuV1 T V : Set G) := hF1.H_normalizes_V₁
  have hIH : H ≤ Subgroup.normalizer (conjClosure S.V3 H : Set G) :=
    le_normalizer_conjClosure S.V3 H
  have : Fact (IsElemAbelian 2 (tildeOf (fsuV1 T V) (conjClosure S.V3 H))) :=
    ⟨hF1.isElemAbelian_tilde⟩
  have hIHN : conjClosure S.V3 H ≤ Subgroup.normalizer (fsuV1 T V : Set G) :=
    (hF1.conjClosure_Vp_le_pCoreOf.trans (pCoreOf_le 2 H)).trans hV₁
  have hker : ∀ x : ↥H, actH hV₁ hIH x = 1 ↔ (x : G) ∈ pCoreOf 2 H := by
    intro x
    rw [A6Tv.actH_eq_one_iff hV₁ hIHN hIH x, hF1.pCoreOf_eq_centralizerMod]
    exact ⟨fun h1 => ⟨x.2, hV₁ x.2, h1⟩, fun h1 => h1.2.2⟩
  have hKst : S.KSt H K = (K.subgroupOf H).map (actH hV₁ hIH) :=
    autOn_tilde_eq_map_actH hV₁ hIH hKH
  let f : ↥K →* ↥(S.KSt H K) := ((actH hV₁ hIH).comp (Subgroup.inclusion hKH)).codRestrict _
    fun k => by
      rw [hKst]
      exact ⟨Subgroup.inclusion hKH k, Subgroup.mem_subgroupOf.2 k.2, rfl⟩
  have hfs : Function.Surjective f := by
    rintro ⟨ψ, hψ⟩
    rw [hKst] at hψ
    obtain ⟨x, hx, rfl⟩ := hψ
    exact ⟨⟨x, Subgroup.mem_subgroupOf.1 hx⟩, rfl⟩
  refine ⟨ι.toMonoidHom.comp f, ι.surjective.comp hfs, fun k => ?_⟩
  rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff,
    ← Subtype.coe_inj]
  exact hker _


theorem isSylowTwoOf_T (hS : S.Hyp138) {H : Subgroup G} (hH : H ∈ S.Hz) {K : Subgroup G}
    (hHK : H = K ⊔ T) : IsSylowTwoOf T H := by
  have hF1 := (hS.hF H hH).toHypF91
  have hTH : T ≤ H := hHK ▸ le_sup_right
  refine ⟨hTH, hF1.sylow.2.1, fun h2 => hF1.sylow.2.2 ?_⟩
  have h1 : (T.subgroupOf H).index ∣ (T.subgroupOf ⊤).index := by
    have := Subgroup.relIndex_dvd_index_of_le hTH
    rw [Subgroup.relIndex] at this
    rwa [show (T.subgroupOf ⊤).index = T.index from Subgroup.relIndex_top_right T]
  exact h2.trans h1

theorem exists_c_class (hS : S.Hyp138) {H : Subgroup G}
    (hH : H ∈ S.Hz) {K : Subgroup G} (hKH : K ≤ H) (hKn : H ≤ Subgroup.normalizer (K : Set G))
    (hHK : H = K ⊔ T) (hL1K : S.L1 ≤ K) (h6 : IsAlt 6 ↥(S.KSt H K))
    {α : ↥K →* alternatingGroup (Fin 6)} (hαs : Function.Surjective α)
    (hαk : ∀ k : ↥K, α k = 1 ↔ (k : G) ∈ pCoreOf 2 H) :
    ∃ c ∈ S.L1, ∃ hcK : c ∈ K, (α ⟨c, hcK⟩) ^ 3 = 1 ∧ α ⟨c, hcK⟩ ≠ 1 ∧
      ∀ t ∈ T, ∃ k : ↥K, ∀ hct : t⁻¹ * c * t ∈ K,
        α ⟨t⁻¹ * c * t, hct⟩ = α k * α ⟨c, hcK⟩ * (α k)⁻¹ ∨
          α ⟨t⁻¹ * c * t, hct⟩ = α k * (α ⟨c, hcK⟩)⁻¹ * (α k)⁻¹ := by
  classical
  have hF := hS.hF H hH
  have hF1 := hF.toHypF91
  have hTH : T ≤ H := hHK ▸ le_sup_right
  have hTn3 : T ≤ Subgroup.normalizer (S.V3 : Set G) := le_sup_right.trans hF1.L₁T_normalizes_Vp
  have hL1n3 : S.L1 ≤ Subgroup.normalizer (S.V3 : Set G) := le_sup_left.trans hF1.L₁T_normalizes_Vp
  have hV3U : S.V3 ≤ conjClosure S.V3 H := le_conjClosure S.V3 H
  have hQc : ∀ q ∈ pCoreOf 2 H, ∀ u ∈ conjClosure S.V3 H, q * u * q⁻¹ * u⁻¹ ∈ fsuV1 T V := by
    intro q hq u hu
    rw [hF1.pCoreOf_eq_centralizerMod] at hq
    exact hq.2.2 u hu
  obtain ⟨c₀, hc₀L, hc₀ρ⟩ := S.exists_L1_c012
  set c₁ : ↥(Subgroup.normalizer (V : Set G)) := c₀ ^ 40 with hc₁
  have hc₁ρ : S.frame.ρ c₁ = swap 0 1 * swap 1 2 := by
    have h3 : (swap (0 : Fin 6) 1 * swap 1 2) ^ 3 = 1 := by decide
    rw [hc₁, map_pow, hc₀ρ, show 40 = 3 * 13 + 1 from rfl, pow_add, pow_mul, h3, one_pow,
      one_mul, pow_one]
  set c : G := (c₁ : G) with hcdef
  have hcL : c ∈ S.L1 := by
    rw [hcdef, hc₁, SubgroupClass.coe_pow]
    exact S.L1.pow_mem hc₀L 40
  have hcK : c ∈ K := hL1K hcL
  have hc₀K : (c₀ : G) ∈ K := hL1K hc₀L
  have hcα : α ⟨c, hcK⟩ = (α ⟨c₀, hc₀K⟩) ^ 40 := by
    rw [← map_pow]
    exact congrArg α (Subtype.ext (by simp [hcdef, hc₁]))
  have hc3 : (α ⟨c, hcK⟩) ^ 3 = 1 := by
    rw [hcα, ← pow_mul, show 40 * 3 = 60 * 2 by norm_num, pow_mul, A6Hm.pow_sixty, one_pow]
  have hcQ : c ∉ pCoreOf 2 H := by
    intro hcq
    have hV3V1 : S.V3 ≤ fsuV1 T V := fun v hv => mem_V1_of_c012 hc₁ρ hv (hQc c hcq v (hV3U hv))
    have h8 := Subgroup.card_le_of_le hV3V1
    rw [S.card_V3, S.card_V1] at h8
    exact absurd h8 (by norm_num)
  have hc1 : α ⟨c, hcK⟩ ≠ 1 := fun h => hcQ ((hαk _).1 h)
  set P : Subgroup G := K ⊓ Subgroup.normalizer (S.V3 : Set G) with hP
  set Γ : Subgroup (alternatingGroup (Fin 6)) := (P.subgroupOf K).map α with hΓ
  have hmemΓ : ∀ k : ↥K, (k : G) ∈ Subgroup.normalizer (S.V3 : Set G) → α k ∈ Γ :=
    fun k hk => ⟨k, Subgroup.mem_subgroupOf.2 ⟨k.2, hk⟩, rfl⟩
  have hcΓ : α ⟨c, hcK⟩ ∈ Γ := hmemΓ _ (hL1n3 hcL)
  have hΓtop : Γ ≠ ⊤ := by
    intro htop
    have hKV3 : ∀ k ∈ K, ∀ v ∈ S.V3, k * v * k⁻¹ ∈ S.V3 := by
      intro k hk v hv
      have hαk' : α ⟨k, hk⟩ ∈ Γ := htop ▸ Subgroup.mem_top _
      obtain ⟨p, hp, hpk⟩ := hαk'
      have hpP := Subgroup.mem_subgroupOf.1 hp
      have hq : ((p⁻¹ * ⟨k, hk⟩ : ↥K) : G) ∈ pCoreOf 2 H :=
        (hαk _).1 (by rw [map_mul, map_inv, hpk, inv_mul_cancel])
      set q : G := ((p⁻¹ * ⟨k, hk⟩ : ↥K) : G) with hqdef
      have hkpq : k = (p : G) * q := by
        rw [hqdef]
        simp
      have h1 : q * v * q⁻¹ * v⁻¹ ∈ fsuV1 T V := hQc q hq v (hV3U hv)
      have h2 : q * v * q⁻¹ ∈ S.V3 := by
        have e : q * v * q⁻¹ = (q * v * q⁻¹ * v⁻¹) * v := by group
        rw [e]
        exact S.V3.mul_mem ((S.V1_le_V2.trans S.V2_le_V3) h1) hv
      rw [hkpq]
      have e : (p : G) * q * v * ((p : G) * q)⁻¹ = (p : G) * (q * v * q⁻¹) * (p : G)⁻¹ := by group
      rw [e]
      exact (Subgroup.mem_normalizer_iff.mp hpP.2 _).mp h2
    have hHV3 : ∀ h ∈ H, ∀ v ∈ S.V3, h * v * h⁻¹ ∈ S.V3 := by
      intro h hh
      have hh' : h ∈ ((K ⊔ T : Subgroup G) : Set G) := by rw [← hHK]; exact hh
      rw [sup_comm, Subgroup.coe_mul_of_left_le_normalizer_right T K (hTH.trans hKn)] at hh'
      obtain ⟨t, ht, k, hk, rfl⟩ := hh'
      intro v hv
      have e : t * k * v * (t * k)⁻¹ = t * (k * v * k⁻¹) * t⁻¹ := by group
      rw [e]
      exact (Subgroup.mem_normalizer_iff.mp (hTn3 ht) _).mp (hKV3 k hk v hv)
    have hU : conjClosure S.V3 H = S.V3 := le_antisymm
      (conjClosure_le fun h hh v hv => hHV3 h hh v hv) hV3U
    have hcardU : Nat.card ↥(tildeOf (fsuV1 T V) (conjClosure S.V3 H)) = 4 := by
      rw [hU]
      have hV1V3 : fsuV1 T V ≤ S.V3 := (S.V1_le_V2.trans S.V2_le_V3)
      have h1 := relIndex_secImg (A := Subgroup.normalizer (fsuV1 T V : Set G))
        (B := fsuV1 T V) le_rfl hV1V3
        ((le_conjClosure S.V3 H |>.trans hU.le).trans
          (hU ▸ (hF1.conjClosure_Vp_le_pCoreOf.trans (pCoreOf_le 2 H)).trans hF1.H_normalizes_V₁))
      have hbot : secImg (Subgroup.normalizer (fsuV1 T V : Set G)) (fsuV1 T V) (fsuV1 T V) = ⊥ := by
        rw [eq_bot_iff]
        rintro _ ⟨y, hy, rfl⟩
        rw [Subgroup.mem_bot, secMk_eq_one_iff]
        exact Subgroup.mem_subgroupOf.1 hy
      rw [hbot, Subgroup.relIndex_bot_left] at h1
      unfold tildeOf
      rw [h1]
      have h2 := Subgroup.relIndex_mul_card (fsuV1 T V) S.V3
      rw [inf_eq_left.2 hV1V3, S.card_V3, S.card_V1] at h2
      omega
    obtain ⟨ι⟩ := h6
    have hK360 : Nat.card ↥(S.KSt H K) = 360 := by
      rw [Nat.card_congr ι.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
        Fintype.card_fin]
      rfl
    have hle : Nat.card ↥(S.KSt H K) ≤
        Nat.card (Perm ↥(tildeOf (fsuV1 T V) (conjClosure S.V3 H))) := by
      calc Nat.card ↥(S.KSt H K)
          ≤ Nat.card (MulAut ↥(tildeOf (fsuV1 T V) (conjClosure S.V3 H))) :=
            Subgroup.card_le_card_group _
        _ ≤ Nat.card (Perm ↥(tildeOf (fsuV1 T V) (conjClosure S.V3 H))) :=
            Nat.card_le_card_of_injective (fun e => e.toEquiv) fun e e' h =>
              MulEquiv.ext fun x => congrArg (fun f : Perm _ => f x) h
    rw [hK360, Nat.card_perm, hcardU] at hle
    exact absurd hle (by decide)
  have hTK : IsSylowTwoOf (T ⊓ K) K :=
    B6.isSylowTwoOf_inf_normal (S.isSylowTwoOf_T hS hH hHK) hKH hKn
  set D : Subgroup (alternatingGroup (Fin 6)) := ((T ⊓ K).subgroupOf K).map α with hD
  have hDΓ : D ≤ Γ := by
    rintro _ ⟨k, hk, rfl⟩
    exact hmemΓ k (hTn3 (Subgroup.mem_subgroupOf.1 hk).1)
  have hD8 : Nat.card D = 8 := by
    have hA : Nat.card (alternatingGroup (Fin 6)) = 360 := by
      rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]; rfl
    have hDp : IsPGroup 2 D := by
      have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have : IsPGroup 2 ((T ⊓ K).subgroupOf K) :=
        hTK.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe inf_le_right).symm
      exact this.map α
    have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨a, ha⟩ := hDp.exists_card_eq
    have hodd : ¬ 2 ∣ D.index := by
      intro h
      apply hTK.2.2
      exact h.trans (Subgroup.index_map_dvd _ hαs)
    have hmul := Subgroup.card_mul_index D
    rw [hA, ha] at hmul
    have ha3 : a ≤ 8 := by
      by_contra h
      push Not at h
      have : 2 ^ 9 ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) h
      have h1 : 2 ^ a ≤ 360 := Nat.le_of_dvd (by norm_num) ⟨_, hmul.symm⟩
      omega
    rw [ha]
    interval_cases a <;> omega
  have hΓ24 := A6Hm.card_eq_24 hΓtop hDΓ hD8 hcΓ hc3 hc1
  refine ⟨c, hcL, hcK, hc3, hc1, fun t ht => ?_⟩
  have htK : t⁻¹ * c * t ∈ K := by
    have := (Subgroup.mem_normalizer_iff.mp (hKn (hTH (T.inv_mem ht))) c).mp hcK
    simpa using this
  have htN : t⁻¹ * c * t ∈ Subgroup.normalizer (S.V3 : Set G) := by
    have h1 := hTn3 (T.inv_mem ht)
    have h2 := hL1n3 hcL
    have h3 := hTn3 ht
    have := Subgroup.mul_mem _ (Subgroup.mul_mem _ h1 h2) h3
    simpa using this
  set y : alternatingGroup (Fin 6) := α ⟨t⁻¹ * c * t, htK⟩ with hy
  have hyΓ : y ∈ Γ := hmemΓ _ htN
  have hy3 : y ^ 3 = 1 := by
    have hc3Q : c ^ 3 ∈ pCoreOf 2 H := by
      have := (hαk ⟨c ^ 3, K.pow_mem hcK 3⟩).1 (by rw [← hc3, ← map_pow]; rfl)
      exact this
    rw [hy, ← map_pow, hαk]
    have e : ((⟨t⁻¹ * c * t, htK⟩ ^ 3 : ↥K) : G) = t⁻¹ * c ^ 3 * t := by
      simp only [SubgroupClass.coe_pow]
      have := conj_pow (a := t⁻¹) (b := c) (i := 3)
      simpa using this
    rw [e]
    have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 H (hTH (T.inv_mem ht)))
      _).mp hc3Q
    simpa using this
  have hy1 : y ≠ 1 := by
    intro h
    apply hcQ
    have h1 : t⁻¹ * c * t ∈ pCoreOf 2 H := (hαk _).1 h
    have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 H (hTH ht)) _).mp h1
    simpa [mul_assoc] using this
  obtain ⟨g, hg⟩ := A6Hm.conj_of_card_24 hΓ24 (x := ⟨α ⟨c, hcK⟩, hcΓ⟩) (y := ⟨y, hyΓ⟩)
    (Subtype.ext (by simpa using hc3)) (fun h => hc1 (congrArg Subtype.val h))
    (Subtype.ext (by simpa using hy3)) (fun h => hy1 (congrArg Subtype.val h))
  obtain ⟨k, -, hk⟩ := g.2
  refine ⟨k, fun hct => ?_⟩
  have hyy : α ⟨t⁻¹ * c * t, hct⟩ = y := rfl
  rw [hyy]
  rcases hg with h | h
  · left
    have := congrArg Subtype.val h
    simpa [hk] using this
  · right
    have := congrArg Subtype.val h
    simpa [hk] using this

end Setting4

end CFSG.Quasithin.H13.A6
