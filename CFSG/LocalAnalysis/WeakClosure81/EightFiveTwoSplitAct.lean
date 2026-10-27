module

public import CFSG.LocalAnalysis.WeakClosure81.EightFiveTwoSplitDefs
public import CFSG.LocalAnalysis.WeakClosure81.EightFiveBars

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.WeakClosure81.SevenK
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem exists_conj_aut {V H T : Subgroup G} (h : Hyp83 V H T) (hKT : H = kGenIn V H ⊔ T)
    {X : Type} [Group X] {φ : ↥(kGenIn V H) →* X}
    (hφ : IsBarMap (kGenIn V H) (pCoreOf 2 (kGenIn V H)) φ) {u : G} (hu : u ∈ H) :
    ∃ α : MulAut X, ∀ k k' : ↥(kGenIn V H), (k' : G) = u * k * u⁻¹ → α (φ k) = φ k' := by
  have hnK : u ∈ Subgroup.normalizer ((kGenIn V H : Subgroup G) : Set G) :=
    h.le_normalizer_kGenIn_of_eq_sup hKT hu
  have hnN : u ∈ Subgroup.normalizer ((pCoreOf 2 (kGenIn V H) : Subgroup G) : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 (kGenIn V H) hnK
  have conjHom : ∀ g : G, g ∈ Subgroup.normalizer ((kGenIn V H : Subgroup G) : Set G) →
      g ∈ Subgroup.normalizer ((pCoreOf 2 (kGenIn V H) : Subgroup G) : Set G) →
      ∃ c : ↥(kGenIn V H) →* ↥(kGenIn V H), (∀ k, ((c k : ↥(kGenIn V H)) : G) = g * k * g⁻¹) ∧
        ∀ k, φ k = 1 → φ (c k) = 1 := by
    intro g hgK hgN
    refine ⟨{ toFun := fun k => ⟨g * k * g⁻¹, (Subgroup.mem_normalizer_iff.1 hgK k).1 k.2⟩
              map_one' := by ext; simp
              map_mul' := fun a b => by ext; simp [mul_assoc] }, fun k => rfl, fun k hk => ?_⟩
    rw [hφ.ker_iff] at hk ⊢
    exact (Subgroup.mem_normalizer_iff.1 hgN k).1 hk
  obtain ⟨c, hc, hkc⟩ := conjHom u hnK hnN
  obtain ⟨c', hc', hkc'⟩ := conjHom u⁻¹ (inv_mem hnK) (inv_mem hnN)
  let α₀ : X →* X := (MonoidHom.liftOfSurjective φ hφ.surjective) ⟨φ.comp c, fun k hk => hkc k hk⟩
  let α₁ : X →* X :=
    (MonoidHom.liftOfSurjective φ hφ.surjective) ⟨φ.comp c', fun k hk => hkc' k hk⟩
  have hα₀ : ∀ k, α₀ (φ k) = φ (c k) := fun k =>
    MonoidHom.liftOfRightInverse_comp_apply φ _ _ ⟨φ.comp c, fun k hk => hkc k hk⟩ k
  have hα₁ : ∀ k, α₁ (φ k) = φ (c' k) := fun k =>
    MonoidHom.liftOfRightInverse_comp_apply φ _ _ ⟨φ.comp c', fun k hk => hkc' k hk⟩ k
  have hcc' : ∀ k, c (c' k) = k := fun k => by
    apply Subtype.ext
    rw [hc, hc']
    group
  have hc'c : ∀ k, c' (c k) = k := fun k => by
    apply Subtype.ext
    rw [hc', hc]
    group
  refine ⟨MonoidHom.toMulEquiv α₀ α₁ (MonoidHom.ext fun x => ?_) (MonoidHom.ext fun x => ?_), ?_⟩
  · obtain ⟨k, rfl⟩ := hφ.surjective x
    simp only [MonoidHom.comp_apply, MonoidHom.id_apply, hα₀, hα₁, hc'c]
  · obtain ⟨k, rfl⟩ := hφ.surjective x
    simp only [MonoidHom.comp_apply, MonoidHom.id_apply, hα₀, hα₁, hcc']
  · intro k k' hk'
    have : c k = k' := Subtype.ext (by rw [hc, hk'])
    simp [hα₀, this]

theorem exists_action {V H T U : Subgroup G} (hD : DispatchHyp V H T U)
    {X : Type} [Group X] {φ : ↥(kGenIn V H) →* X}
    (hφ : IsBarMap (kGenIn V H) (pCoreOf 2 (kGenIn V H)) φ) :
    ∃ (A : Subgroup (MulAut X)) (Z₁ : Subgroup X),
      ActionFacts X (barSub (kGenIn V H) φ V) A Z₁ (rk ↥V) ∧
      ∀ k : ↥(kGenIn V H),
        φ k ∈ Z₁ ↔ (k : G) ∈ Subgroup.centralizer (eSub V H T : Set G) := by
  have h83 : Hyp83 V H T := Hyp83.of_hyp7 hD.hyp7 hD.calH hD.not_calH0 hD.sylow
  have hKT := hD.eq_sup
  have hUH : U ≤ H := hD.le_T.trans h83.T_le_H
  have hnK : ∀ u : ↥U, (u : G) ∈ Subgroup.normalizer ((kGenIn V H : Subgroup G) : Set G) :=
    fun u => h83.le_normalizer_kGenIn_of_eq_sup hKT (hUH u.2)
  have hmem : ∀ (u : ↥U) (k : ↥(kGenIn V H)), (u : G) * k * (u : G)⁻¹ ∈ kGenIn V H :=
    fun u k => (Subgroup.mem_normalizer_iff.1 (hnK u) k).1 k.2
  let cj : ↥U → ↥(kGenIn V H) → ↥(kGenIn V H) := fun u k => ⟨u * k * u⁻¹, hmem u k⟩
  have hcj_one : ∀ k, cj 1 k = k := fun k => Subtype.ext (by simp [cj])
  have hcj_mul : ∀ a b k, cj (a * b) k = cj a (cj b k) := fun a b k =>
    Subtype.ext (by simp [cj, mul_assoc])
  have hcj_mul' : ∀ u k k', cj u (k * k') = cj u k * cj u k' := fun u k k' =>
    Subtype.ext (by simp [cj, mul_assoc])
  choose ρ₀ hρ₀ using fun u : ↥U => exists_conj_aut h83 hKT hφ (hUH u.2)
  have hρcj : ∀ u k, ρ₀ u (φ k) = φ (cj u k) := fun u k => hρ₀ u k (cj u k) rfl
  let ρ : ↥U →* MulAut X :=
    { toFun := ρ₀
      map_one' := by
        refine MulEquiv.ext fun x => ?_
        obtain ⟨k, rfl⟩ := hφ.surjective x
        rw [hρcj, hcj_one]
        rfl
      map_mul' := fun a b => by
        refine MulEquiv.ext fun x => ?_
        obtain ⟨k, rfl⟩ := hφ.surjective x
        rw [hρcj, hcj_mul]
        change _ = ρ₀ a (ρ₀ b (φ k))
        rw [hρcj, hρcj] }
  have hρ : ∀ u k, ρ u (φ k) = φ (cj u k) := hρcj
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hNC : pCoreOf 2 (kGenIn V H) ≤ Subgroup.centralizer (eSub V H T : Set G) :=
    h83.pCoreOf_kGenIn_le_centralizer_eSub
  have hinj : Function.Injective ρ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    let Y : Subgroup G := ρ.ker.map U.subtype
    have hYU : Y ≤ U := Subgroup.map_subtype_le _
    have hYK : ⁅Y, kGenIn V H⁆ ≤ Subgroup.centralizer (eSub V H T : Set G) := by
      rw [Subgroup.commutator_le]
      rintro y ⟨u, hu, rfl⟩ k hk
      have hρu : ρ u = 1 := hu
      let k₀ : ↥(kGenIn V H) := ⟨k, hk⟩
      have h1 : φ (cj u k₀) = φ k₀ := by rw [← hρ, hρu]; rfl
      have h2 : (((cj u k₀) * k₀⁻¹ : ↥(kGenIn V H)) : G) ∈ pCoreOf 2 (kGenIn V H) := by
        rw [← hφ.ker_iff, map_mul, h1, map_inv, mul_inv_cancel]
      apply hNC
      simpa [cj, commutatorElement_def] using h2
    have hY := hD.faithful Y hYU hYK
    intro u hu
    have h1 : (u : G) ∈ Y := ⟨u, hu, rfl⟩
    rw [hY, Subgroup.mem_bot] at h1
    exact (Subgroup.mem_bot.2 (Subtype.ext h1))
  have hUea : IsElemAbelian 2 U := by
    obtain ⟨g, hg⟩ := hD.conj
    rw [hg]
    exact isElemAbelian_conjSubgroup' h83.elemAbelian g
  have hUV : Nat.card ↥U = Nat.card ↥V := by
    obtain ⟨g, hg⟩ := hD.conj
    rw [hg]
    exact CFSG.Quasithin.E3.card_conjSubgroup V g
  have hVp : IsPGroup 2 ↥V :=
    CFSG.CGT.Timmesfeld75.isPGroup_two_of_isElemAbelian h83.elemAbelian
  have hVpow : Nat.card ↥V = 2 ^ rk ↥V := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hVp
    unfold rk
    rw [hk, padicValNat.prime_pow]
  have hAea : IsElemAbelian 2 ρ.range := by
    rw [MonoidHom.range_eq_map]
    have h1 : IsElemAbelian 2 (U.subgroupOf U) := hUea.subgroupOf U
    rw [Subgroup.subgroupOf_self] at h1
    exact h1.map ρ
  have hAcard : Nat.card ρ.range = 2 ^ rk ↥V := by
    rw [← hVpow, ← hUV]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hlt : Nat.card (barSub (kGenIn V H) φ V) < 2 ^ rk ↥V := by
    rw [h83.card_barSub_eq_two_pow_rankBarV hKT hφ, ← hVpow]
    have h1 := E3.card_eq_two_pow_mul hVp
      (U := V ⊓ Subgroup.centralizer (eSub V H T : Set G)) inf_le_left
    have h2 : 1 < Nat.card ↥(V ⊓ Subgroup.centralizer (eSub V H T : Set G)) :=
      (Subgroup.one_lt_card_iff_ne_bot _).2 hD.inf_V_ne_bot
    unfold rankBarV
    rw [h1]
    exact lt_mul_of_one_lt_right (by positivity) h2
  refine ⟨ρ.range, ((Subgroup.centralizer (eSub V H T : Set G)).subgroupOf (kGenIn V H)).map φ,
    ⟨hAea, hAcard, hlt, ?_, ?_, ?_⟩, ?_⟩
  ·
    rintro a ⟨u, rfl⟩ s hs
    obtain ⟨k, hkV, rfl⟩ := mem_barSub.1 hs
    rw [hρ]
    congr 1
    refine Subtype.ext ?_
    change (u : G) * k * (u : G)⁻¹ = k
    rw [hD.comm_V u u.2 k hkV]
    group
  ·
    intro z hz
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.1 hz
    rw [Subgroup.mem_center_iff]
    intro x
    obtain ⟨k', rfl⟩ := hφ.surjective x
    have h1 := h83.comm_mem_pCoreOf_of_mem_inf_centralizer hKT (r := (k : G))
      (Subgroup.mem_subgroupOf.1 hk) k' k'.2
    have h2 : φ (k * k' * k⁻¹ * k'⁻¹) = 1 := (hφ.ker_iff _).2 (by simpa using h1)
    simp only [map_mul, map_inv] at h2
    exact (commutatorElement_eq_one_iff_mul_comm.1 (by rwa [commutatorElement_def])).symm
  ·
    intro Q hQodd hQinv a ha q hq
    obtain ⟨u, rfl⟩ := ha
    obtain ⟨k, rfl⟩ := hφ.surjective q
    let Qh : Subgroup G := (Q.comap φ).map (kGenIn V H).subtype
    have hQK : Qh ≤ kGenIn V H := by
      rintro g ⟨k₀, -, rfl⟩
      exact k₀.2
    have hmemQh : ∀ k₀ : ↥(kGenIn V H), (k₀ : G) ∈ Qh ↔ φ k₀ ∈ Q := fun k₀ => by
      constructor
      · rintro ⟨k₁, hk₁, h⟩
        rw [← Subtype.ext h]
        exact hk₁
      · intro h
        exact ⟨k₀, h, rfl⟩
    have key : ∀ u' : ↥U, ∀ g ∈ Qh, (u' : G) * g * (u' : G)⁻¹ ∈ Qh := by
      intro u' g hg
      have hgK : g ∈ kGenIn V H := hQK hg
      have h1 : (u' : G) * g * (u' : G)⁻¹ = ((cj u' ⟨g, hgK⟩ : ↥(kGenIn V H)) : G) := rfl
      rw [h1, hmemQh, ← hρ]
      exact hQinv _ ⟨u', rfl⟩ _ ((hmemQh ⟨g, hgK⟩).1 hg)
    have hUn : U ≤ Subgroup.normalizer (Qh : Set G) := by
      intro u' hu'
      rw [Subgroup.mem_normalizer_iff]
      intro g
      refine ⟨fun hg => key ⟨u', hu'⟩ g hg, fun hg => ?_⟩
      have := key ⟨u'⁻¹, U.inv_mem hu'⟩ _ hg
      simpa [mul_assoc] using this
    have hodd : Odd ((Subgroup.centralizer (eSub V H T : Set G)).relIndex Qh) := by
      have h1 : barSub (kGenIn V H) φ Qh = Q := by
        have h2 : Qh.subgroupOf (kGenIn V H) = Q.comap φ := by
          ext k₀
          rw [Subgroup.mem_subgroupOf, hmemQh, Subgroup.mem_comap]
        change (Qh.subgroupOf (kGenIn V H)).map φ = Q
        rw [h2]
        exact Subgroup.map_comap_eq_self_of_surjective hφ.surjective Q
      have h3 := card_barSub_eq_relIndex_of_isBarMap hQK (CFSG.LieType.BorelTits.pCoreOf_le 2 _) hφ
      rw [h1] at h3
      rw [h3] at hQodd
      exact Odd.of_dvd_nat hQodd (Subgroup.relIndex_dvd_of_le_left Qh hNC)
    have hcomm := hD.odd_comm Qh hQK hUn hodd
    have hkQ : (k : G) ∈ Qh := (hmemQh k).2 hq
    have hc : ⁅(u : G), (k : G)⁆ ∈ Subgroup.centralizer (eSub V H T : Set G) := by
      apply hcomm
      rw [Subgroup.commutator_comm]
      exact Subgroup.commutator_mem_commutator u.2 hkQ
    rw [hρ, ← map_inv, ← map_mul]
    refine Subgroup.mem_map.2 ⟨cj u k * k⁻¹, Subgroup.mem_subgroupOf.2 ?_, rfl⟩
    simpa [cj, commutatorElement_def] using hc
  · intro k
    constructor
    · intro hk
      obtain ⟨k', hk', hkk⟩ := Subgroup.mem_map.1 hk
      have h1 : φ (k'⁻¹ * k) = 1 := by rw [map_mul, map_inv, hkk, inv_mul_cancel]
      have h2 := hNC ((hφ.ker_iff _).1 h1)
      have h3 := (Subgroup.centralizer (eSub V H T : Set G)).mul_mem
        (Subgroup.mem_subgroupOf.1 hk') h2
      simpa using h3
    · intro hk
      exact Subgroup.mem_map.2 ⟨k, Subgroup.mem_subgroupOf.2 hk, rfl⟩

end CFSG.LocalAnalysis.WeakClosure81

end
