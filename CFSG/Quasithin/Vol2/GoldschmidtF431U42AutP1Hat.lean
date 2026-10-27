module

public import CFSG.GH74.KGroups.Generic6
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutIface
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP0Base

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open CFSG.GH74.KGroups
open CFSG.Quasithin.H13.F431.U42 (Y P45 Xs Xs_eq card_Xs nonempty_mulEquiv_Y)
open CFSG.ComponentClassification.CatFactsSmall.PSp43 (QA45 QP45 exists_model)

theorem equiv_A_or_central_involution {Yb Gh : Type} [Group Yb]
    [Group Gh] (hY : CFSG.Blueprint.LieModel Yb .PSU 4 2 1) {ι : Yb →* Gh}
    (hinj : Function.Injective ι) (hidx : ι.range.index = 2) :
    Nonempty (Gh ≃* Ah) ∨ ∃ κ : Gh, κ ≠ 1 ∧ κ * κ = 1 ∧ ∀ g : Gh, g * κ = κ * g := by
  obtain ⟨eY⟩ := nonempty_mulEquiv_Y hY
  set N : Subgroup Gh := ι.range with hN
  have hNn : N.Normal := Subgroup.normal_of_index_eq_two hidx
  let e : ↥N ≃* ↥QP45.originalSubgroup :=
    (MonoidHom.ofInjective hinj).symm.trans (eY.trans (MulEquiv.subgroupCongr Xs_eq))
  obtain ⟨M, hMP, hMA⟩ := exists_model e
  have hPA : M.P ≤ M.A := by
    rw [hMP, hMA, ← Xs_eq]
    exact Xs_le_A
  have hcardN : Nat.card N = 25920 :=
    (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm.trans
      ((Nat.card_congr eY.toEquiv).trans card_Xs)
  have hcard : Nat.card Gh = 51840 := by
    have h := Subgroup.card_mul_index (H := N)
    rw [hcardN, hidx] at h
    omega
  have : Finite Gh := Nat.finite_of_card_ne_zero (by omega)
  have hcentN : ∀ c ∈ Subgroup.centralizer (N : Set Gh), c ∈ N → c = 1 := by
    intro c hc hcN
    have h1 : (M.e ⟨c, hcN⟩ : P45) = 1 := by
      refine M.centralizer_trivial (hPA (M.e ⟨c, hcN⟩).2) fun x hx => ?_
      obtain ⟨n, hn⟩ := M.e.surjective ⟨x, hx⟩
      have hnc : (⟨c, hcN⟩ : ↥N) * n = n * ⟨c, hcN⟩ :=
        Subtype.ext ((Subgroup.mem_centralizer_iff.1 hc) n n.2).symm
      have := congrArg (fun a => ((M.e a : M.P) : P45)) hnc
      simp only [map_mul, Subgroup.coe_mul, hn] at this
      exact this
    have h2 : M.e ⟨c, hcN⟩ = 1 := Subtype.ext h1
    have h3 : (⟨c, hcN⟩ : ↥N) = 1 := M.e.injective (by rw [h2, map_one])
    exact congrArg Subtype.val h3
  by_cases hC : Subgroup.centralizer (N : Set Gh) = ⊥
  · left
    have hmem : ∀ g, M.actHom N g ∈ QA45.originalSubgroup := fun g => hMA ▸ M.actHom_mem N g
    let act : Gh →* Ah := (M.actHom N).codRestrict QA45.originalSubgroup hmem
    have hinj' : Function.Injective act := fun a b h => by
      apply M.actHom_injective N hC
      exact congrArg (fun z : Ah => (z : P45)) h
    have hbij : Function.Bijective act :=
      hinj'.bijective_of_nat_card_le (by rw [hcard, card_A])
    exact ⟨MulEquiv.ofBijective act hbij⟩
  · right
    obtain ⟨⟨c, hc⟩, hc1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hC
    have hc1' : c ≠ 1 := fun h => hc1 (Subtype.ext h)
    have hcN : c ∉ N := fun h => hc1' (hcentN c hc h)
    have hc2 : c * c = 1 := by
      have h1 : c * c ∈ N := Subgroup.mul_self_mem_of_index_two hidx c
      have h2 : c * c ∈ Subgroup.centralizer (N : Set Gh) := Subgroup.mul_mem _ hc hc
      exact hcentN _ h2 h1
    refine ⟨c, hc1', hc2, fun g => ?_⟩
    by_cases hg : g ∈ N
    · exact (Subgroup.mem_centralizer_iff.1 hc) g hg
    · have h1 : g * c⁻¹ ∈ N := by
        rw [Subgroup.mul_mem_iff_of_index_two hidx]
        exact iff_of_false hg (fun h => hcN (by simpa using N.inv_mem h))
      have h2 := (Subgroup.mem_centralizer_iff.1 hc) _ h1
      calc g * c = (g * c⁻¹) * c * c := by group
        _ = c * (g * c⁻¹) * c := by rw [h2]
        _ = c * g := by group

theorem no_central_involution {G Gh : Type} [Group G] [Group Gh] {M₁ M₂ : Subgroup G}
    (hO2 : pCoreOf 2 (M₁ ⊔ M₂) = ⊥) {T N₁ N₂ : Subgroup Gh} (hp : IsYAmalgamPair T N₁ N₂)
    (iso0 : (RankTwoAmalgam.ofSubgroups M₁ M₂).Iso (RankTwoAmalgam.ofSubgroups N₁ N₂))
    {κ : Gh} (hκ1 : κ ≠ 1) (hκ2 : κ * κ = 1) (hκc : ∀ g : Gh, g * κ = κ * g) : False := by
  have hκT : κ ∈ T :=
    mem_of_central_of_isSylowTwoOf hp.1 (Subgroup.mem_top _) (fun b _ => hκc b) hκ2
  have hTN₁ : T ≤ N₁ := Subgroup.le_normalizer.trans ((hp.2.2 N₁).2 (Or.inl rfl)).2
  have hTN₂ : T ≤ N₂ := Subgroup.le_normalizer.trans ((hp.2.2 N₂).2 (Or.inr rfl)).2
  let φ1 : ↥M₁ ≃* ↥N₁ := iso0.φ1
  let φ2 : ↥M₂ ≃* ↥N₂ := iso0.φ2
  let φ12 : ↥(M₁ ⊓ M₂) ≃* ↥(N₁ ⊓ N₂) := iso0.φ12
  let κ12 : ↥(N₁ ⊓ N₂) := ⟨κ, hTN₁ hκT, hTN₂ hκT⟩
  let w : ↥(M₁ ⊓ M₂) := φ12.symm κ12
  have hwM1 : (w : G) ∈ M₁ := (Subgroup.mem_inf.1 w.2).1
  have hwM2 : (w : G) ∈ M₂ := (Subgroup.mem_inf.1 w.2).2
  have hφw : φ12 w = κ12 := φ12.apply_symm_apply κ12
  have hw1 : φ1 ⟨(w : G), hwM1⟩ = ⟨κ, hTN₁ hκT⟩ := by
    have h : Subgroup.inclusion (inf_le_left : N₁ ⊓ N₂ ≤ N₁) (φ12 w) =
        φ1 (Subgroup.inclusion (inf_le_left : M₁ ⊓ M₂ ≤ M₁) w) := iso0.comm1 w
    rw [hφw] at h
    exact h.symm
  have hw2 : φ2 ⟨(w : G), hwM2⟩ = ⟨κ, hTN₂ hκT⟩ := by
    have h : Subgroup.inclusion (inf_le_right : N₁ ⊓ N₂ ≤ N₂) (φ12 w) =
        φ2 (Subgroup.inclusion (inf_le_right : M₁ ⊓ M₂ ≤ M₂) w) := iso0.comm2 w
    rw [hφw] at h
    exact h.symm
  have hc1 : ∀ m ∈ M₁, m * (w : G) = (w : G) * m := by
    intro m hm
    have h : (⟨m, hm⟩ : ↥M₁) * ⟨(w : G), hwM1⟩ = ⟨(w : G), hwM1⟩ * ⟨m, hm⟩ := by
      apply φ1.injective
      rw [map_mul, map_mul, hw1]
      exact Subtype.ext (hκc _)
    exact congrArg Subtype.val h
  have hc2 : ∀ m ∈ M₂, m * (w : G) = (w : G) * m := by
    intro m hm
    have h : (⟨m, hm⟩ : ↥M₂) * ⟨(w : G), hwM2⟩ = ⟨(w : G), hwM2⟩ * ⟨m, hm⟩ := by
      apply φ2.injective
      rw [map_mul, map_mul, hw2]
      exact Subtype.ext (hκc _)
    exact congrArg Subtype.val h
  have hsup : M₁ ⊔ M₂ ≤ Subgroup.centralizer ({(w : G)} : Set G) := by
    refine sup_le (fun m hm => ?_) (fun m hm => ?_)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact hc1 m hm
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact hc2 m hm
  have hw2' : (w : G) * (w : G) = 1 := by
    have : w * w = 1 := by
      apply φ12.injective
      rw [map_mul, MulEquiv.apply_symm_apply, map_one]
      exact Subtype.ext hκ2
    exact congrArg Subtype.val this
  have hwH : (w : G) ∈ M₁ ⊔ M₂ := Subgroup.mem_sup_left hwM1
  have hnorm : M₁ ⊔ M₂ ≤ Subgroup.normalizer ((Subgroup.zpowers (w : G) : Subgroup G) : Set G) := by
    intro g hg
    have hc : g * (w : G) = (w : G) * g := Subgroup.mem_centralizer_singleton_iff.1 (hsup hg)
    have key : ∀ g' : G, g' * (w : G) * g'⁻¹ = (w : G) →
        ∀ h : G, h ∈ Subgroup.zpowers (w : G) → g' * h * g'⁻¹ ∈ Subgroup.zpowers (w : G) := by
      intro g' hg' h hh
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
      rw [show g' * (w : G) ^ n * g'⁻¹ = (g' * (w : G) * g'⁻¹) ^ n by simp [conj_zpow], hg']
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers (w : G)) n
    have hconj : g * (w : G) * g⁻¹ = (w : G) := by rw [hc]; simp
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · exact key g hconj h
    · intro hh
      have hconj' : g⁻¹ * (w : G) * g = (w : G) := by
        calc g⁻¹ * (w : G) * g = g⁻¹ * ((w : G) * g) := by rw [mul_assoc]
          _ = g⁻¹ * (g * (w : G)) := by rw [hc]
          _ = (w : G) := by rw [← mul_assoc]; simp
      have := key g⁻¹ (by simpa using hconj') _ hh
      simpa [mul_assoc] using this
  have hp2 : IsPGroup 2 (Subgroup.zpowers (w : G)) := by
    have hord : orderOf (w : G) ∣ 2 ^ 1 := by
      rw [pow_one]
      exact orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hw2')
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hord
    exact IsPGroup.of_card (n := m) (by rw [Nat.card_zpowers, hm])
  have hle := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    ((Subgroup.zpowers_le).2 hwH) hnorm hp2
  rw [hO2] at hle
  have hw1' : (w : G) = 1 := by
    have : (w : G) ∈ (⊥ : Subgroup G) := hle (Subgroup.mem_zpowers _)
    exact Subgroup.mem_bot.1 this
  have : w = 1 := Subtype.ext hw1'
  have : κ12 = 1 := by
    have h := congrArg φ12 this
    rwa [map_one, show φ12 w = κ12 from MulEquiv.apply_symm_apply _ _] at h
  exact hκ1 (congrArg Subtype.val this)

end CFSG.Quasithin.H13.F431.U42Aut
