module

public import CFSG.Quasithin.EmptyFaithful.S146F8

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement

@[expose] def Input14617V : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), Setting146 G T M →
    ∀ (H PQ : Subgroup G) (p : ℕ), IsRedCE T M H PQ p → PMaximal T M p → p = 3 → IsOFourPlusOn T M H →
      ∀ (H₀ H₁ H₂ : Subgroup G) (t : G), IsDec12 T M H p H₀ H₁ H₂ t →
        ∃ u₁ ∈ uHi T M H H₁, u₁ ∉ quasithinOmegaOneCenter T ∧
          ∃ u₂ ∈ uHi T M H H₂, u₂ ∉ quasithinOmegaOneCenter T ∧
            ∃ c ∈ conjClosure (VZ T M) H,
              (∀ h ∈ H, h * c * h⁻¹ * c⁻¹ ∈ quasithinOmegaOneCenter T) ∧
                VZ T M = quasithinOmegaOneCenter T ⊔ Subgroup.zpowers (u₁ * u₂ * c)

theorem centralizer_le_normalizer_zpowers' {G : Type} [Group G] (q : G) :
    Subgroup.centralizer ({q} : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers q : Set G) := by
  intro c hc
  have hcw : ∀ w ∈ Subgroup.zpowers q, c * w * c⁻¹ = w := by
    intro w hw
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    have hcu : Commute q c := Subgroup.mem_centralizer_iff.mp hc q rfl
    have h' : Commute c (q ^ n) := (hcu.zpow_left n).symm
    rw [h'.eq]
    group
  rw [Subgroup.mem_normalizer_iff]
  intro w
  constructor
  · intro hw
    rw [hcw w hw]
    exact hw
  · intro hw
    have h1 := hcw _ hw
    have h2 : c * (c * w * c⁻¹) = c * w := by
      calc c * (c * w * c⁻¹) = (c * (c * w * c⁻¹) * c⁻¹) * c := by group
        _ = (c * w * c⁻¹) * c := by rw [h1]
        _ = c * w := by group
    have e2 : c * w * c⁻¹ = w := mul_left_cancel h2
    rw [e2] at hw
    exact hw

section Five

variable {G : Type} [Group G] [Finite G] {T M H : Subgroup G} {p : ℕ} {H₀ H₁ H₂ : Subgroup G} {t : G}

omit [Finite G] in
theorem oTwoUpper_le_centralizer_of_comm_mem_Z {X : Subgroup G} (hX : X ≤ mcOf T) {a : G}
    (ha : ∀ x ∈ X, a * x * a⁻¹ * x⁻¹ ∈ quasithinOmegaOneCenter T) :
    oTwoUpper X ≤ Subgroup.centralizer ({a} : Set G) := by
  refine oTwoUpper_le_of_pow_mem fun x hx => ⟨1, ?_⟩
  have hc := ha x hx
  set c := a * x * a⁻¹ * x⁻¹ with hcdef
  have hcx : x * c = c * x := S146T.comm_Z (hX hx) hc
  have hc2 : c * c = 1 := by
    have := S146T.Z_sq hc
    simpa [pow_two] using this
  have e1 : a * x = c * x * a := by rw [hcdef]; group
  show x ^ 2 ^ 1 ∈ Subgroup.centralizer ({a} : Set G)
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  rw [Set.mem_singleton_iff] at hw
  subst hw
  have hx2 : x ^ 2 ^ 1 = x * x := by rw [pow_one, pow_two]
  rw [hx2]
  calc w * (x * x) = (w * x) * x := by group
    _ = (c * x * w) * x := by rw [e1]
    _ = c * x * (w * x) := by group
    _ = c * x * (c * x * w) := by rw [e1]
    _ = c * (x * c) * x * w := by group
    _ = c * (c * x) * x * w := by rw [hcx]
    _ = (c * c) * (x * x) * w := by group
    _ = x * x * w := by rw [hc2]; group

theorem IsDec12.card_conjClosure_oTwoUpper (S : Setting146 G T M) {PQ : Subgroup G}
    (hred : IsRedCE T M H PQ p) (hp3 : p = 3) (hOF : IsOFourPlusOn T M H)
    (h : IsDec12 T M H p H₀ H₁ H₂ t) {u₁ u₂ c : G} (hu₁ : u₁ ∈ uHi T M H H₁)
    (hu₁Z : u₁ ∉ quasithinOmegaOneCenter T) (hu₂ : u₂ ∈ uHi T M H H₂)
    (hu₂Z : u₂ ∉ quasithinOmegaOneCenter T) (hcU : c ∈ conjClosure (VZ T M) H)
    (hc : ∀ x ∈ H, x * c * x⁻¹ * c⁻¹ ∈ quasithinOmegaOneCenter T)
    (hV : VZ T M = quasithinOmegaOneCenter T ⊔ Subgroup.zpowers (u₁ * u₂ * c)) :
    Nat.card (conjClosure (VZ T M) (oTwoUpper H₂)) = 2 ^ 4 := by
  have hH : IsHTM T M H := hred.isHTM
  have hHG : H ≤ mcOf T := S.le_mcOf hH
  have hH₁H : H₁ ≤ H := h.le₁.trans h.le
  have hH₂H : H₂ ≤ H := h.le₂.trans h.le
  have hHU : H ≤ Subgroup.normalizer (conjClosure (VZ T M) H : Set G) := le_normalizer_conjClosure _ _
  have hUab : IsElemAbelian 2 (conjClosure (VZ T M) H) := S.lemma_14_5_15_two hH
  have hU₁U : u₁ ∈ conjClosure (VZ T M) H := uHi_le_conjClosure hH₁H hu₁
  have hU₂U : u₂ ∈ conjClosure (VZ T M) H := uHi_le_conjClosure hH₂H hu₂
  have hcom : ∀ a b : G, a ∈ conjClosure (VZ T M) H → b ∈ conjClosure (VZ T M) H → a * b = b * a :=
    fun a b ha hb => isElemAbelian_comm hUab ha hb
  have hZU₂ : quasithinOmegaOneCenter T ≤ uHi T M H H₂ := Z_le_uHi T M H H₂
  have hZc2 : Nat.card (quasithinOmegaOneCenter T) = 2 := S.card_Z
  have hK₂u₁ : oTwoUpper H₂ ≤ Subgroup.centralizer ({u₁} : Set G) :=
    oTwoUpper_le_centralizer_of_comm_mem_Z (hH₂H.trans hHG) fun x hx => by
      have h1 := h.cent₁ (Subgroup.commutator_mem_commutator hu₁ hx)
      simpa [commutatorElement_def] using h1
  have hK₂c : oTwoUpper H₂ ≤ Subgroup.centralizer ({c} : Set G) :=
    oTwoUpper_le_centralizer_of_comm_mem_Z (hH₂H.trans hHG) fun x hx => by
      have h1 := (quasithinOmegaOneCenter T).inv_mem (hc x (hH₂H hx))
      simpa [mul_assoc] using h1
  have hconj₁ : ∀ k ∈ oTwoUpper H₂, k * u₁ * k⁻¹ = u₁ := fun k hk => by
    have := Subgroup.mem_centralizer_iff.mp (hK₂u₁ hk) u₁ rfl
    rw [← this]
    group
  have hconjc : ∀ k ∈ oTwoUpper H₂, k * c * k⁻¹ = c := fun k hk => by
    have := Subgroup.mem_centralizer_iff.mp (hK₂c hk) c rfl
    rw [← this]
    group
  have hdec3 : IsDec12 T M H 3 H₀ H₂ H₁ t⁻¹ := hp3 ▸ h.swap
  obtain ⟨x₂, hx₂H₂, hx₂Q, hx₂odd, hx₂3⟩ := hdec3.exists_odd_three
  have hSec := h.swap.sec4 S hred hp3 hOF hx₂H₂ hx₂Q hx₂3
  have hx₂K : x₂ ∈ oTwoUpper H₂ := mem_oTwoUpper_of_odd hx₂H₂ hx₂odd
  have hN₂ : H₂ ≤ Subgroup.normalizer (uHi T M H H₂ : Set G) := h.swap.le_normalizer_uHi S hred
  set w := u₁ * u₂ * c with hw
  set Y := conjClosure (VZ T M) (oTwoUpper H₂) with hY
  have hVY : VZ T M ≤ Y := le_conjClosure _ _
  have hZV : quasithinOmegaOneCenter T ≤ VZ T M := by
    rw [hV]
    exact le_sup_left
  have hwV : w ∈ VZ T M := by
    rw [hV]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers w)
  have hwY : w ∈ Y := hVY hwV
  have hKY : oTwoUpper H₂ ≤ Subgroup.normalizer (Y : Set G) := le_normalizer_conjClosure _ _
  have hdU₂ : x₂ * u₂ * x₂⁻¹ * u₂⁻¹ ∈ uHi T M H H₂ :=
    (uHi T M H H₂).mul_mem ((Subgroup.mem_normalizer_iff.mp (hN₂ hx₂H₂) u₂).mp hu₂)
      ((uHi T M H H₂).inv_mem hu₂)
  have hdZ : x₂ * u₂ * x₂⁻¹ * u₂⁻¹ ∉ quasithinOmegaOneCenter T := fun hd => hu₂Z (hSec.fixed_mem hu₂ hd)
  have heU : x₂ * u₂ * x₂⁻¹ ∈ conjClosure (VZ T M) H :=
    (Subgroup.mem_normalizer_iff.mp (hHU (hH₂H hx₂H₂)) u₂).mp hU₂U
  have hdY : x₂ * u₂ * x₂⁻¹ * u₂⁻¹ ∈ Y := by
    have h1 : x₂ * w * x₂⁻¹ ∈ Y := (Subgroup.mem_normalizer_iff.mp (hKY hx₂K) w).mp hwY
    have h2 := Y.mul_mem h1 (Y.inv_mem hwY)
    have e1 : x₂ * w * x₂⁻¹ = u₁ * (x₂ * u₂ * x₂⁻¹) * c := by
      rw [hw]
      calc x₂ * (u₁ * u₂ * c) * x₂⁻¹ = (x₂ * u₁ * x₂⁻¹) * (x₂ * u₂ * x₂⁻¹) * (x₂ * c * x₂⁻¹) := by
            group
        _ = u₁ * (x₂ * u₂ * x₂⁻¹) * c := by rw [hconj₁ x₂ hx₂K, hconjc x₂ hx₂K]
    have e2 : x₂ * w * x₂⁻¹ * w⁻¹ = x₂ * u₂ * x₂⁻¹ * u₂⁻¹ := by
      rw [e1, hw]
      have hcu : u₁ * (x₂ * u₂ * x₂⁻¹ * u₂⁻¹) = (x₂ * u₂ * x₂⁻¹ * u₂⁻¹) * u₁ :=
        hcom _ _ hU₁U ((conjClosure (VZ T M) H).mul_mem heU ((conjClosure (VZ T M) H).inv_mem hU₂U))
      calc u₁ * (x₂ * u₂ * x₂⁻¹) * c * (u₁ * u₂ * c)⁻¹ = u₁ * (x₂ * u₂ * x₂⁻¹ * u₂⁻¹) * u₁⁻¹ := by
            group
        _ = x₂ * u₂ * x₂⁻¹ * u₂⁻¹ := by rw [hcu]; group
    rwa [e2] at h2
  have hU₂Y : uHi T M H H₂ ≤ Y := by
    have heq : Y ⊓ uHi T M H H₂ = uHi T M H H₂ := by
      refine hSec.eq_of_invariant (E := Y ⊓ uHi T M H H₂) (le_inf (hZV.trans hVY) hZU₂) inf_le_right
        (fun a ha => ⟨(Subgroup.mem_normalizer_iff.mp (hKY hx₂K) a).mp ha.1,
          (Subgroup.mem_normalizer_iff.mp (hN₂ hx₂H₂) a).mp ha.2⟩) ?_
      intro hle
      exact hdZ (hle ⟨hdY, hdU₂⟩)
    rw [← heq]
    exact inf_le_left
  set q := u₁ * c with hq
  have hqU : q ∈ conjClosure (VZ T M) H := (conjClosure (VZ T M) H).mul_mem hU₁U hcU
  have hqY : q ∈ Y := by
    have hqw : q = w * u₂⁻¹ := by
      rw [hq, hw]
      have h1 : u₂ * c = c * u₂ := hcom _ _ hU₂U hcU
      calc u₁ * c = u₁ * (c * u₂) * u₂⁻¹ := by group
        _ = u₁ * (u₂ * c) * u₂⁻¹ := by rw [h1]
        _ = u₁ * u₂ * c * u₂⁻¹ := by group
    rw [hqw]
    exact Y.mul_mem hwY (Y.inv_mem (hU₂Y hu₂))
  have hAY : uHi T M H H₂ ⊔ Subgroup.zpowers q ≤ Y :=
    sup_le hU₂Y (Subgroup.zpowers_le.mpr hqY)
  have hKA : oTwoUpper H₂ ≤ Subgroup.normalizer ((uHi T M H H₂ ⊔ Subgroup.zpowers q : Subgroup G) : Set G) := by
    have h1 : oTwoUpper H₂ ≤ Subgroup.normalizer (uHi T M H H₂ : Set G) :=
      (oTwoUpper_le H₂).trans hN₂
    have h2 : oTwoUpper H₂ ≤ Subgroup.normalizer (Subgroup.zpowers q : Set G) := by
      intro k hk
      have hkq : k * q * k⁻¹ = q := by
        rw [hq]
        calc k * (u₁ * c) * k⁻¹ = (k * u₁ * k⁻¹) * (k * c * k⁻¹) := by group
          _ = u₁ * c := by rw [hconj₁ k hk, hconjc k hk]
      refine centralizer_le_normalizer_zpowers' q ?_
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      calc q * k = (k * q * k⁻¹) * k := by rw [hkq]
        _ = k * q := by group
    exact (le_inf h1 h2).trans (Subgroup.inf_normalizer_le_normalizer_sup _ _)
  have hVA : VZ T M ≤ uHi T M H H₂ ⊔ Subgroup.zpowers q := by
    rw [hV]
    refine sup_le (hZU₂.trans le_sup_left) ?_
    refine Subgroup.zpowers_le.mpr ?_
    have hwq : w = q * u₂ := by
      rw [hw, hq]
      have h1 : u₂ * c = c * u₂ := hcom _ _ hU₂U hcU
      calc u₁ * u₂ * c = u₁ * (u₂ * c) := by group
        _ = u₁ * (c * u₂) := by rw [h1]
        _ = u₁ * c * u₂ := by group
    rw [hwq]
    exact (uHi T M H H₂ ⊔ Subgroup.zpowers q).mul_mem
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers q)) (Subgroup.mem_sup_left hu₂)
  have hYA : Y ≤ uHi T M H H₂ ⊔ Subgroup.zpowers q :=
    conjClosure_le fun k hk v hv => (Subgroup.mem_normalizer_iff.mp (hKA hk) v).mp (hVA hv)
  have hYeq : Y = uHi T M H H₂ ⊔ Subgroup.zpowers q := le_antisymm hYA hAY
  have hq2 : q ^ 2 = 1 := isElemAbelian_pow_eq_one hUab hqU
  have hqU₂ : q ∉ uHi T M H H₂ := by
    intro hqU₂
    have hdec1 : IsDec12 T M H 3 H₀ H₁ H₂ t := hp3 ▸ h
    obtain ⟨x₁, hx₁H₁, hx₁Q, hx₁odd, hx₁3⟩ := hdec1.exists_odd_three
    have hSec₁ := h.sec4 S hred hp3 hOF hx₁H₁ hx₁Q hx₁3
    have hx₁H : x₁ ∈ H := hH₁H hx₁H₁
    have ha : x₁ * q * x₁⁻¹ * q⁻¹ ∈ quasithinOmegaOneCenter T := by
      have h1 := (quasithinOmegaOneCenter T).inv_mem (h.cent₂ (Subgroup.commutator_mem_commutator hqU₂ hx₁H₁))
      rw [commutatorElement_inv] at h1
      simpa [commutatorElement_def] using h1
    have hb : c * x₁ * c⁻¹ * x₁⁻¹ ∈ quasithinOmegaOneCenter T := by
      have h1 := (quasithinOmegaOneCenter T).inv_mem (hc x₁ hx₁H)
      simpa [mul_assoc] using h1
    have hu₁G : u₁ ∈ mcOf T := S.mem_mcOf_of_mem_conjClosure hH hU₁U
    have hcen : u₁ * (c * x₁ * c⁻¹ * x₁⁻¹) = (c * x₁ * c⁻¹ * x₁⁻¹) * u₁ := S146T.comm_Z hu₁G hb
    have e : x₁ * u₁ * x₁⁻¹ * u₁⁻¹ = (x₁ * q * x₁⁻¹ * q⁻¹) * (u₁ * (c * x₁ * c⁻¹ * x₁⁻¹) * u₁⁻¹) := by
      rw [hq]; group
    have e2 : u₁ * (c * x₁ * c⁻¹ * x₁⁻¹) * u₁⁻¹ = c * x₁ * c⁻¹ * x₁⁻¹ := by
      rw [hcen]; group
    apply hu₁Z
    refine hSec₁.fixed_mem hu₁ ?_
    rw [e, e2]
    exact (quasithinOmegaOneCenter T).mul_mem ha hb
  have hq1 : q ≠ 1 := fun h1 => hqU₂ (h1 ▸ (uHi T M H H₂).one_mem)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hordq : orderOf q = 2 := orderOf_eq_prime hq2 hq1
  have hcardq : Nat.card (Subgroup.zpowers q) = 2 := by rw [Nat.card_zpowers, hordq]
  have hcomm₂ : ∀ x ∈ uHi T M H H₂, ∀ y ∈ Subgroup.zpowers q, x * y = y * x := by
    intro x hx y hy
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have hxq : x * q = q * x := hcom _ _ (uHi_le_conjClosure hH₂H hx) hqU
    exact ((show Commute x q from hxq).zpow_right n).eq
  obtain ⟨hprod, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute (uHi T M H H₂)
    (Subgroup.zpowers q) hcomm₂
  have hinf : Nat.card (uHi T M H H₂ ⊓ Subgroup.zpowers q : Subgroup G) = 1 := by
    have hdvd : Nat.card (uHi T M H H₂ ⊓ Subgroup.zpowers q : Subgroup G) ∣ 2 := by
      rw [← hcardq]
      exact Subgroup.card_dvd_of_le inf_le_right
    have hne : Nat.card (uHi T M H H₂ ⊓ Subgroup.zpowers q : Subgroup G) ≠ 2 := by
      intro h2
      have hle : (uHi T M H H₂ ⊓ Subgroup.zpowers q : Subgroup G) = Subgroup.zpowers q :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h2, hcardq])
      apply hqU₂
      have : q ∈ (uHi T M H H₂ ⊓ Subgroup.zpowers q : Subgroup G) := by
        rw [hle]
        exact Subgroup.mem_zpowers q
      exact this.1
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
    · exact h1
    · exact absurd h2 hne
  have hU₂card : Nat.card (uHi T M H H₂) = 8 := by
    have e := Subgroup.relIndex_mul_card (H := quasithinOmegaOneCenter T) (K := uHi T M H H₂)
    rw [inf_eq_left.mpr hZU₂, (h.relIndex_uHi_eq_four S hred hp3 hOF).2, hZc2] at e
    omega
  rw [hYeq]
  rw [hinf, hcardq, hU₂card] at hprod
  omega

end Five

theorem input14617Five_of (iV : Input14617V) : Input14617Five := by
  intro G _ _ T M S H PQ p hred hmax hp3 hOF H₀ H₁ H₂ t hdec
  obtain ⟨u₁, hu₁, hu₁Z, u₂, hu₂, hu₂Z, c, hcU, hc, hV⟩ :=
    iV G T M S H PQ p hred hmax hp3 hOF H₀ H₁ H₂ t hdec
  exact hdec.card_conjClosure_oTwoUpper S hred hp3 hOF hu₁ hu₁Z hu₂ hu₂Z hcU hc hV

end CFSG.Quasithin
