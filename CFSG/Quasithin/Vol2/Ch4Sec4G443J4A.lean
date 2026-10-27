module

public import CFSG.Sporadic.J4
public import CFSG.Sporadic.J4.QTOutAuto
public import CFSG.Quasithin.Background.A1cRank
public import CFSG.Quasithin.Background.A3Structure312Embed
public import CFSG.Quasithin.Vol2.Ch4Sec1Defs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Quasithin.H13.Ch4.G443J4

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Blueprint
open scoped Pointwise

theorem exists_conj_of_mulEquiv {X Γ : Type} [Group X] [Group Γ] (e : X ≃* Γ)
    (h : ∀ φ : MulAut Γ, ∃ g : Γ, φ = MulAut.conj g) (α : MulAut X) :
    ∃ g : X, α = MulAut.conj g := by
  obtain ⟨g, hg⟩ := h (MulAut.congr e α)
  refine ⟨e.symm g, MulEquiv.ext fun x => e.injective ?_⟩
  have h1 : e (α x) = g * e x * g⁻¹ := by
    have := congrArg (fun φ : MulAut Γ => φ (e x)) hg
    simpa [MulAut.congr_apply] using this
  rw [h1, MulAut.conj_apply, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]

theorem all_inner_of_maps_sylow {X : Type} [Group X] [Finite X] (P : Sylow 2 X)
    (h : ∀ α : MulAut X, (∀ x ∈ (P : Subgroup X), α x ∈ (P : Subgroup X)) →
      ∃ k : X, ∀ x, α x = k * x * k⁻¹)
    (α : MulAut X) : ∃ g : X, α = MulAut.conj g := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Q : Sylow 2 X := P.mapSurjective (f := α.toMonoidHom) α.surjective
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X Q P
  have hP : ((g • Q : Sylow 2 X) : Subgroup X) = P := by rw [hg]
  rw [Sylow.coe_subgroup_smul] at hP
  obtain ⟨k, hk⟩ := h (MulAut.conj g * α) fun x hx => by
    have hxQ : α x ∈ (Q : Subgroup X) := ⟨x, hx, rfl⟩
    have : g * α x * g⁻¹ ∈ MulAut.conj g • (Q : Subgroup X) :=
      (Subgroup.mem_smul_pointwise_iff_exists _ _ _).2 ⟨α x, hxQ, rfl⟩
    rw [hP] at this
    simpa [MulAut.conj_apply] using this
  refine ⟨g⁻¹ * k, MulEquiv.ext fun x => ?_⟩
  have h1 : g * α x * g⁻¹ = k * x * k⁻¹ := by simpa [MulAut.conj_apply] using hk x
  rw [MulAut.conj_apply]
  calc α x = g⁻¹ * (g * α x * g⁻¹) * g := by group
    _ = g⁻¹ * k * x * (g⁻¹ * k)⁻¹ := by rw [h1]; group

open CFSG.Sporadic.J4 in
theorem all_inner_J
    (α : MulAut J) : ∃ g : J, α = MulAut.conj g := by
  have hF := j4Facts
  have hfin : Finite J := Finite.of_equiv _ (seedEquiv j4Facts.mat).toEquiv
  have hP0 : Nat.card QT.P0 = 2 ^ (Nat.card J).factorization 2 := by
    rw [QT.card_P0 hF.mat hF, QT.card_J_factorization hF]
  let P : Sylow 2 J := Sylow.ofCard QT.P0 hP0
  exact all_inner_of_maps_sylow P (fun β hβ => QT.aut_of_maps_P0 hF β hβ) α

theorem all_inner_of_isSporadic_j4
    {Q : Type} [Group Q] (h : IsSporadic .J4 Q) (α : MulAut Q) :
    ∃ g : Q, α = MulAut.conj g := by
  obtain ⟨e⟩ := h
  let e' : Q ≃* CFSG.Sporadic.J4.J :=
    e.trans (CFSG.Sporadic.J4.seedEquiv CFSG.Sporadic.J4.j4Facts.mat)
  exact @exists_conj_of_mulEquiv Q CFSG.Sporadic.J4.J _ (Subgroup.toGroup _) e' all_inner_J α

theorem isSimpleGroup_of_isSporadic_j4 {Q : Type} [Group Q]
    (h : IsSporadic .J4 Q) : IsSimpleGroup Q := by
  obtain ⟨e⟩ := h
  have hs0 : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .J4) :=
    CFSG.Sporadic.J4.fam_j4_simplicity.2.2
  exact e.isSimpleGroup

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem eq_one_of_mul_pow {K C : Subgroup G} (hZ : K ⊓ Subgroup.centralizer (K : Set G) = ⊥)
    (hC : Odd (Nat.card C)) {k c : G} (hk : k ∈ K) (hcK : c ∈ Subgroup.centralizer (K : Set G))
    (hcC : c ∈ C) {a : ℕ} (h : (k * c) ^ 2 ^ a = 1) : c = 1 := by
  have hcomm : Commute k c := Subgroup.mem_centralizer_iff.mp hcK k hk
  rw [hcomm.mul_pow] at h
  have hc2 : c ^ 2 ^ a = 1 := by
    have h1 : c ^ 2 ^ a = (k ^ 2 ^ a)⁻¹ := eq_inv_of_mul_eq_one_right h
    have h2 : c ^ 2 ^ a ∈ K ⊓ Subgroup.centralizer (K : Set G) :=
      ⟨h1 ▸ K.inv_mem (K.pow_mem hk _), Subgroup.pow_mem _ hcK _⟩
    rw [hZ] at h2
    exact h2
  have hodd : Odd (orderOf c) := by
    have := Subgroup.orderOf_dvd_natCard C hcC
    exact Odd.of_dvd_nat hC this
  have h1 : orderOf c ∣ 2 ^ a := orderOf_dvd_of_pow_eq_one hc2
  have h2 : orderOf c = 1 := by
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
    rcases j with _ | j
    · simpa using hj
    · rw [hj, pow_succ] at hodd
      exact absurd (even_two.mul_left _) (Nat.not_even_iff_odd.mpr hodd)
  exact orderOf_eq_one_iff.mp h2

omit [Finite G] in
theorem inf_centralizer_eq_bot {K : Subgroup G} (hK : IsSimpleGroup ↥K) (hKp : ⁅K, K⁆ = K) :
    K ⊓ Subgroup.centralizer (K : Set G) = ⊥ := by
  set C := Subgroup.centralizer (K : Set G) with hCdef
  have hn : ((K ⊓ C).subgroupOf K).Normal := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr fun k hk =>
      Subgroup.inf_normalizer_le_normalizer_inf
        ⟨Subgroup.le_normalizer hk,
          normalizer_le_normalizer_centralizer K (Subgroup.le_normalizer hk)⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((K ⊓ C).subgroupOf K) with h | h
  · rw [eq_bot_iff]
    intro x hx
    have : (⟨x, hx.1⟩ : ↥K) ∈ (K ⊓ C).subgroupOf K := hx
    rw [h, Subgroup.mem_bot] at this
    exact (Subgroup.mem_bot).mpr (congrArg Subtype.val this)
  · exfalso
    have hab : ⁅K, K⁆ = ⊥ := by
      rw [eq_bot_iff, Subgroup.commutator_le]
      intro a ha b hb
      have hb' : (⟨b, hb⟩ : ↥K) ∈ (K ⊓ C).subgroupOf K := h ▸ Subgroup.mem_top _
      have hbC : b ∈ C := hb'.2
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
      exact Subgroup.mem_centralizer_iff.mp hbC a ha
    rw [hKp] at hab
    have := hK.toNontrivial
    obtain ⟨x, hx⟩ := exists_ne (1 : ↥K)
    have h1 : (x : G) ∈ (⊥ : Subgroup G) := by
      rw [← hab]
      exact x.2
    exact hx (Subtype.ext (Subgroup.mem_bot.mp h1))

theorem false_of_le_normalizer {T M K B X : Subgroup G} (hT : quasithinIsSylowTwo T)
    (hK : IsSimpleGroup ↥K) (hKp : ⁅K, K⁆ = K)
    (hout : ∀ α : MulAut ↥K, ∃ g : ↥K, α = MulAut.conj g)
    (hTK : T ≤ Subgroup.normalizer (K : Set G)) (hU : IsUniqueM X M) (hX : X ≤ K ⊔ T)
    (hKM : ¬ K ≤ M) (hKB : K ≤ Subgroup.centralizer (B : Set G)) (hBM : B ≤ M) (hB : B ≠ ⊥)
    (hBodd : Odd (Nat.card B)) (hO2 : pCoreOf 2 M ≤ T) (hchar : CharTwo M) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := Subgroup.centralizer (K : Set G) with hCdef
  have hTC : T ≤ Subgroup.normalizer (C : Set G) :=
    hTK.trans (normalizer_le_normalizer_centralizer K)
  have hKC : ∀ {P : Subgroup G}, P ≤ C → K ≤ Subgroup.normalizer (P : Set G) := fun hPC =>
    (Subgroup.le_centralizer_iff.mpr hPC).trans (Subgroup.centralizer_le_normalizer _)
  have hP : T ⊓ C = ⊥ := by
    by_contra hne
    have hP2 : IsPGroup 2 ↥(T ⊓ C) := hT.1.to_le inf_le_left
    have hN : X ≤ Subgroup.normalizer ((T ⊓ C : Subgroup G) : Set G) :=
      hX.trans (sup_le (hKC inf_le_right) fun t ht => Subgroup.inf_normalizer_le_normalizer_inf
        ⟨Subgroup.le_normalizer ht, hTC ht⟩)
    exact hKM ((hKC inf_le_right).trans (isUniqueM_normalizer_le hU hne hP2 hN))
  have hZ : K ⊓ C = ⊥ := inf_centralizer_eq_bot hK hKp
  set H := K ⊔ T with hH
  have hTH : IsSylowTwoOf T H := ⟨le_sup_right, hT.1, fun h2 =>
    hT.2 (h2.trans (Subgroup.relIndex_dvd_index_of_le le_sup_right))⟩
  have hHC : H ≤ Subgroup.normalizer ((H ⊓ C : Subgroup G) : Set G) := by
    refine sup_le (fun k hk => Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer (Subgroup.mem_sup_left hk),
        normalizer_le_normalizer_centralizer K (Subgroup.le_normalizer hk)⟩)
      (fun t ht => Subgroup.inf_normalizer_le_normalizer_inf
        ⟨Subgroup.le_normalizer (Subgroup.mem_sup_right ht), hTC ht⟩)
  have hCn : ((H ⊓ C).subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr hHC
  have hSyl := A312.isSylowTwoOf_inf_of_subnormal (A3.subnormal_of_normal inf_le_left hCn) hTH
  have hTHC : T ⊓ (H ⊓ C) = ⊥ := by
    rw [eq_bot_iff, ← hP]
    exact inf_le_inf_left _ inf_le_right
  rw [hTHC] at hSyl
  have hCodd : Odd (Nat.card ↥(H ⊓ C)) := by
    have h1 := hSyl.2.2
    rw [Subgroup.bot_subgroupOf, Subgroup.index_bot] at h1
    exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp h1)
  have hTK' : T ≤ K := by
    intro t ht
    have hmap : K.map (MulAut.conj t).toMonoidHom = K :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hTK ht)
    let α : MulAut ↥K := ((MulAut.conj t).subgroupMap K).trans (MulEquiv.subgroupCongr hmap)
    obtain ⟨g, hg⟩ := hout α
    have hconj : ∀ x ∈ K, t * x * t⁻¹ = (g : G) * x * (g : G)⁻¹ := fun x hx => by
      have h1 := congrArg (fun φ : MulAut ↥K => ((φ ⟨x, hx⟩ : ↥K) : G)) hg
      have h2 : ((α ⟨x, hx⟩ : ↥K) : G) = t * x * t⁻¹ := rfl
      rw [← h2]
      simpa [MulAut.conj_apply] using h1
    have hcC : (g : G)⁻¹ * t ∈ C := Subgroup.mem_centralizer_iff.mpr fun x hx => by
      have h1 := hconj x hx
      calc x * ((g : G)⁻¹ * t) = (g : G)⁻¹ * ((g : G) * x * (g : G)⁻¹) * t := by group
        _ = (g : G)⁻¹ * (t * x * t⁻¹) * t := by rw [h1]
        _ = (g : G)⁻¹ * t * x := by group
    have hcH : (g : G)⁻¹ * t ∈ H :=
      H.mul_mem (H.inv_mem (Subgroup.mem_sup_left g.2)) (Subgroup.mem_sup_right ht)
    obtain ⟨a, ha⟩ := hT.1 ⟨t, ht⟩
    have hta : ((g : G) * ((g : G)⁻¹ * t)) ^ 2 ^ a = 1 := by
      rw [mul_inv_cancel_left]
      exact congrArg Subtype.val ha
    have hc1 := eq_one_of_mul_pow hZ hCodd g.2 hcC ⟨hcH, hcC⟩ hta
    have : t = g := by
      calc t = (g : G) * ((g : G)⁻¹ * t) := by group
        _ = g := by rw [hc1, mul_one]
    rw [this]
    exact g.2
  have hBO : B ≤ pCoreOf 2 M := fun b hb => hchar ⟨hBM hb,
    Subgroup.mem_centralizer_iff.mpr fun y hy =>
      (Subgroup.mem_centralizer_iff.mp (hKB (hTK' (hO2 hy))) b hb).symm⟩
  have hB2 : IsPGroup 2 ↥B := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M).to_le hBO
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hB2
  rcases n with _ | n
  · exact hB ((Subgroup.card_eq_one).mp (by simpa using hn))
  · rw [hn, pow_succ] at hBodd
    exact absurd (even_two.mul_left _) (Nat.not_even_iff_odd.mpr hBodd)

end CFSG.Quasithin.H13.Ch4.G443J4
