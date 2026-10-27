module

public import CFSG.Quasithin.EmptyFaithful.S152O4Facts
public import CFSG.Quasithin.EmptyFaithful.S152Y14

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

namespace S152O4

@[expose] def SingThree (σ σ' : Gam) (z : Vec) : Prop :=
  act σ z = z → act σ' z = z → ∀ α : Gam, α ^ 3 = 1 → act α z = z → α = 1

local instance (σ σ' : Gam) (z : Vec) : Decidable (SingThree σ σ' z) := by
  unfold SingThree; infer_instance

@[expose] def KleinPair (σ σ' : Gam) : Prop :=
  σ ^ 2 = 1 → σ' ^ 2 = 1 → σ ≠ 1 → σ' ≠ 1 → σ ≠ σ' → σ * σ' = σ' * σ →
    ∀ z : Vec, z ≠ 1 → SingThree σ σ' z

local instance (σ σ' : Gam) : Decidable (KleinPair σ σ') := by
  unfold KleinPair; infer_instance

theorem model_sing_three : ∀ σ σ' : Gam, KleinPair σ σ' := by
  decide +kernel

variable {V : Type} [CommGroup V]

theorem om4_three_fix [Finite V] {X : Subgroup (MulAut V)} (hX : IsOmegaFourPlus X)
    {Tb : Subgroup (MulAut V)} (hTb : IsSylowTwoOf Tb X) {z : V} (hz : z ≠ 1)
    (hfix : ∀ t ∈ Tb, t z = z) {g : MulAut V} (hgX : g ∈ X) (hg3 : g ^ 3 = 1)
    (hgz : g z = z) : g = 1 := by
  obtain ⟨c, hc⟩ := om4_model hX
  have hTb4 : Nat.card Tb = 4 := card_sylow_two_eq_four hTb (card_eq_36 c hc)
  have hsq : ∀ x ∈ Tb, x * x = 1 := by
    intro x hx
    obtain ⟨k, hk⟩ := hTb.2.1 ⟨x, hx⟩
    have hk' : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    obtain ⟨γ, rfl⟩ := exists_rhoV_eq c hc (hTb.1 hx)
    have hγk : γ ^ 2 ^ k = 1 := rhoV_injective c (by rw [map_pow, map_one]; exact hk')
    have h1 : orderOf γ ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hγk
    have h2 : orderOf γ ∣ 6 := orderOf_dvd_of_pow_eq_one (pow_six γ)
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
    have hj1 : j ≤ 1 := by
      by_contra hcon
      have h4 : 4 ∣ orderOf γ := by
        rw [hj]
        exact (Nat.pow_dvd_pow 2 (by omega : 2 ≤ j))
      have : 4 ∣ 6 := h4.trans h2
      omega
    have h2' : γ ^ 2 = 1 := by
      have : orderOf γ ∣ 2 := by
        rw [hj]
        exact Nat.pow_dvd_pow 2 hj1
      exact orderOf_dvd_iff_pow_eq_one.mp this
    rw [← map_mul]
    have : γ * γ = 1 := by rw [← pow_two]; exact h2'
    rw [this, map_one]
  obtain ⟨s, hsT, s', hs'T, hs1, hs'1, hss', hcomm, -⟩ := exists_klein_elements hTb4 hsq
  obtain ⟨σ, rfl⟩ := exists_rhoV_eq c hc (hTb.1 hsT)
  obtain ⟨σ', rfl⟩ := exists_rhoV_eq c hc (hTb.1 hs'T)
  have hσ2 : σ ^ 2 = 1 := by
    apply rhoV_injective c
    rw [map_pow, map_one, pow_two]
    exact hsq _ hsT
  have hσ'2 : σ' ^ 2 = 1 := by
    apply rhoV_injective c
    rw [map_pow, map_one, pow_two]
    exact hsq _ hs'T
  have hσ1 : σ ≠ 1 := fun h => hs1 (by rw [h, map_one])
  have hσ'1 : σ' ≠ 1 := fun h => hs'1 (by rw [h, map_one])
  have hσσ' : σ ≠ σ' := fun h => hss' (by rw [h])
  have hσc : σ * σ' = σ' * σ := rhoV_injective c (by rw [map_mul, map_mul]; exact hcomm)
  have hz' : c z ≠ 1 := fun h => hz (c.injective (by rw [h, map_one]))
  have hσz : act σ (c z) = c z := by
    rw [← rhoV_apply_of, hfix _ hsT]
  have hσ'z : act σ' (c z) = c z := by
    rw [← rhoV_apply_of, hfix _ hs'T]
  obtain ⟨γ, rfl⟩ := exists_rhoV_eq c hc hgX
  have hγ3 : γ ^ 3 = 1 := rhoV_injective c (by rw [map_pow, map_one]; exact hg3)
  have hγz : act γ (c z) = c z := by
    rw [← rhoV_apply_of, hgz]
  have := model_sing_three σ σ' hσ2 hσ'2 hσ1 hσ'1 hσσ' hσc (c z) hz' hσz hσ'z γ hγ3 hγz
  rw [this, map_one]

end S152O4

namespace C1Pack12

variable {G : Type} [Group G] [Finite G]

theorem om4_three_fix_on {M T V : Subgroup G} (hOm : IsOmegaFourPlusOn M V)
    (hTb : IsSylowTwoOf (autOn T V) (autOn M V)) {z : V} (hz : z ≠ 1)
    (hfix : ∀ t ∈ autOn T V, t z = z) {g : MulAut V} (hgM : g ∈ autOn M V) (hg3 : g ^ 3 = 1)
    (hgz : g z = z) : g = 1 := by
  obtain ⟨hV, hX⟩ := hOm
  exact S152O4.om4_three_fix (V := IntMod V hV) hX hTb (z := z) hz hfix hgM hg3 hgz

theorem card_autOn_of_isOmegaFourPlusOn {M V : Subgroup G} (hOm : IsOmegaFourPlusOn M V) :
    Nat.card (autOn M V) = 36 := by
  obtain ⟨hV, hX⟩ := hOm
  exact (S152O4.om4_facts (V := IntMod V hV) hX).card_eq

theorem exists_three_lift {X V : Subgroup G} {g : MulAut V} (hg : g ∈ autOn X V)
    (h3 : orderOf g = 3) :
    ∃ (b : G) (hb : b ∈ Subgroup.normalizer (V : Set G)), b ∈ X ∧
      (∃ k : ℕ, orderOf b = 3 ^ k) ∧ conjAct V ⟨b, hb⟩ = g := by
  obtain ⟨a, haN, haX, rfl⟩ := mem_autOn_iff_exists.mp hg
  have hn : orderOf a ≠ 0 := (orderOf_pos a).ne'
  obtain ⟨k, m, hm, hnm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn 3 (by norm_num)
  have hb : a ^ (m * m) ∈ Subgroup.normalizer (V : Set G) := Subgroup.pow_mem _ haN _
  refine ⟨a ^ (m * m), hb, Subgroup.pow_mem X haX _, ?_, ?_⟩
  · have h1 : (a ^ (m * m)) ^ 3 ^ k = 1 := by
      rw [← pow_mul, show m * m * 3 ^ k = (3 ^ k * m) * m by ring, ← hnm, pow_mul,
        pow_orderOf_eq_one, one_pow]
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one h1)
    exact ⟨j, hj⟩
  · have hpow : conjAct V ⟨a ^ (m * m), hb⟩ = (conjAct V ⟨a, haN⟩) ^ (m * m) := by
      rw [← map_pow]
      rfl
    rw [hpow]
    have h31 : (conjAct V ⟨a, haN⟩) ^ 3 = 1 := by
      have := pow_orderOf_eq_one (conjAct V ⟨a, haN⟩)
      rwa [h3] at this
    have hmod : m * m % 3 = 1 := by
      have : m % 3 = 1 ∨ m % 3 = 2 := by omega
      rcases this with h | h <;> simp [Nat.mul_mod, h]
    rw [← Nat.div_add_mod (m * m) 3, hmod, pow_add, pow_mul, h31, one_pow, one_mul, pow_one]

omit [Finite G] in
theorem conjAct_apply_eq_self {V : Subgroup G} {b z : G} (hb : b ∈ Subgroup.normalizer (V : Set G))
    (hz : z ∈ V) (hbz : z * b = b * z) : conjAct V ⟨b, hb⟩ ⟨z, hz⟩ = ⟨z, hz⟩ := by
  apply Subtype.ext
  rw [conj_coe_apply]
  show b * z * b⁻¹ = z
  rw [← hbz]
  group

theorem exists_nonone_ZV {T Mc M : Subgroup G} (hd : S152Y.Data T Mc M) :
    ∃ z ∈ quasithinOmegaOneCenter T ⊓ V154 T Mc M, z ≠ 1 := by
  by_contra hcon
  push Not at hcon
  have hb : quasithinOmegaOneCenter T ⊓ V154 T Mc M = ⊥ :=
    eq_bot_iff.mpr fun z hz => Subgroup.mem_bot.mpr (hcon z hz)
  have h1 : V154 T Mc M = ⊥ := by
    refine le_bot_iff.mp ?_
    calc V154 T Mc M
        = conjClosure (quasithinOmegaOneCenter T ⊓ V154 T Mc M) (m0Of T Mc M) := hd.h1515.gen
      _ ≤ ⊥ := conjClosure_le fun h _ z hz => by
          rw [hb] at hz
          rw [Subgroup.mem_bot.mp hz]
          simp
  exact hd.hyp.ne_bot h1

theorem not_case1512Six_of_threeElements {T Mc M : Subgroup G} (hd : S152Y.Data T Mc M)
    (hc : ∀ x ∈ Mc, (∃ k : ℕ, orderOf x = 3 ^ k) →
      x ∈ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) :
    ¬ Case1512Six T Mc M := by
  intro hSix
  obtain ⟨-, -, -, -, -, hOm0, -, hidx⟩ := id hSix
  have hOm : IsOmegaFourPlusOn M (V154 T Mc M) := by
    rw [V154_eq_uJ hSix]
    exact hOm0
  have hMcV : M ⊓ Mc ≤ Subgroup.normalizer (V154 T Mc M : Set G) := inf_le_left.trans hd.hMV
  have hCV_le : M ⊓ Subgroup.centralizer (V154 T Mc M : Set G) ≤ M ⊓ Mc := fun x hx =>
    ⟨hx.1, hd.h1515.centralizer_le hx.2⟩
  have hcard : Nat.card (autOn M (V154 T Mc M)) =
      Nat.card (autOn (M ⊓ Mc) (V154 T Mc M)) * 3 := by
    rw [card_autOn_eq_relIndex hd.hMV, card_autOn_eq_relIndex hMcV]
    have e : (M ⊓ Mc) ⊓ Subgroup.centralizer (V154 T Mc M : Set G) =
        M ⊓ Subgroup.centralizer (V154 T Mc M : Set G) :=
      le_antisymm (fun x hx => ⟨hx.1.1, hx.2⟩) (fun x hx => ⟨hCV_le hx, hx.2⟩)
    rw [e, ← hidx]
    exact (Subgroup.relIndex_mul_relIndex _ (M ⊓ Mc) M hCV_le inf_le_left).symm
  have h36 : Nat.card (autOn M (V154 T Mc M)) = 36 := card_autOn_of_isOmegaFourPlusOn hOm
  have h12 : Nat.card (autOn (M ⊓ Mc) (V154 T Mc M)) = 12 := by omega
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite (autOn (M ⊓ Mc) (V154 T Mc M)) := Nat.finite_of_card_ne_zero (by omega)
  obtain ⟨x, hx3⟩ := exists_prime_orderOf_dvd_card' (G := ↥(autOn (M ⊓ Mc) (V154 T Mc M))) 3
    (by rw [h12]; norm_num)
  have hg3 : orderOf (x : MulAut (V154 T Mc M)) = 3 := by rw [Subgroup.orderOf_coe]; exact hx3
  obtain ⟨b, hb, hbX, ⟨k, hbk⟩, hbg⟩ := exists_three_lift x.2 hg3
  have hbC : b ∈ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := hc b hbX.2 ⟨k, hbk⟩
  obtain ⟨z, hzZV, hz1⟩ := exists_nonone_ZV hd
  have hfixb : conjAct (V154 T Mc M) ⟨b, hb⟩ ⟨z, hzZV.2⟩ = ⟨z, hzZV.2⟩ :=
    conjAct_apply_eq_self hb hzZV.2 (Subgroup.mem_centralizer_iff.mp hbC z hzZV.1)
  have hfixT : ∀ t ∈ autOn T (V154 T Mc M), t ⟨z, hzZV.2⟩ = ⟨z, hzZV.2⟩ := by
    intro t ht
    obtain ⟨s, hsN, hsT, rfl⟩ := mem_autOn_iff_exists.mp ht
    have hzT : z ∈ Subgroup.centralizer (T : Set G) :=
      (quasithinOmegaOneCenter_le_center T hzZV.1).2
    exact conjAct_apply_eq_self hsN hzZV.2 (Subgroup.mem_centralizer_iff.mp hzT s hsT).symm
  have hxM : (x : MulAut (V154 T Mc M)) ∈ autOn M (V154 T Mc M) :=
    A4.autOn_mono inf_le_left x.2
  have hg3' : (x : MulAut (V154 T Mc M)) ^ 3 = 1 := by
    have := pow_orderOf_eq_one (x : MulAut (V154 T Mc M))
    rwa [hg3] at this
  have h1 : (x : MulAut (V154 T Mc M)) = 1 :=
    om4_three_fix_on hOm (S152Y.isSylowTwoOf_Tb hd) (z := ⟨z, hzZV.2⟩)
      (fun h => hz1 (congrArg Subtype.val h)) hfixT hxM hg3' (by rw [← hbg]; exact hfixb)
  rw [h1, orderOf_one] at hg3
  omega

theorem not_case1512Six_of_oThreePrime {T Mc M H : Subgroup G} (hd : S152Y.Data T Mc M)
    (heq : conjClosure (oTwoUpper H) Mc = oPrimeResidualOf 3 Mc)
    (hle : conjClosure (oTwoUpper H) Mc ≤
      Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) :
    ¬ Case1512Six T Mc M :=
  not_case1512Six_of_threeElements hd fun _ hx hx3 =>
    hle (heq ▸ Subgroup.subset_closure ⟨hx, hx3⟩)

end C1Pack12

end CFSG.Quasithin
