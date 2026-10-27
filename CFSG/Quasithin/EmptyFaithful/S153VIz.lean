module

public import CFSG.Quasithin.EmptyFaithful.S153VCore

public section

namespace CFSG.Quasithin.ModF

open scoped Pointwise commutatorElement
open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Lin2 CFSG.LieType.BorelTits
  CFSG.Quasithin.ModV CFSG.QuasithinUnique.A5.Delta5 Equiv

variable {G : Type} [Group G] [Finite G] {I S Iz K₁ K₂ : Subgroup G}

namespace A5Cfg

variable (c : A5Cfg I S Iz K₁ K₂)
include c

theorem memS_iff (P : AppC.A5Pi K₁) {p : Fin 5} (hp : ∀ g ∈ imgS K₁ S P.α, g p = p) (x : ↥K₁) :
    (x : G) ∈ S ↔ toPerm P.α x ∈ klein p := by
  have hker := c.ker_le₁ P.hαk
  rw [← mem_imgS_iff hker x]
  exact imgS_eq_klein P.hα hker c.sylow₁ hp _

theorem mem_normalizer_inf_of_fix (P : AppC.A5Pi K₁) {p : Fin 5}
    (hp : ∀ g ∈ imgS K₁ S P.α, g p = p) (x : ↥K₁) (hx : toPerm P.α x p = p) :
    (x : G) ∈ Subgroup.normalizer ((S ⊓ K₁ : Subgroup G) : Set G) := by
  have hkl : ∀ (a : Perm (Fin 5)), a p = p → ∀ v ∈ klein p, a * v * a⁻¹ ∈ klein p := by
    intro a ha v hv
    unfold klein at hv ⊢
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
    obtain ⟨h1, h2, h3⟩ := hv
    have hinv : a⁻¹ p = p := by
      rw [Equiv.Perm.inv_eq_iff_eq]
      exact ha.symm
    refine ⟨?_, ?_, ?_⟩
    · calc a * v * a⁻¹ * (a * v * a⁻¹) = a * (v * v) * a⁻¹ := by group
        _ = 1 := by rw [h1]; group
    · simp [Perm.sign_mul, Perm.sign_inv, h2]
    · simp only [Perm.mul_apply, hinv, h3, ha]
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · rintro ⟨hS, hK⟩
    refine ⟨?_, K₁.mul_mem (K₁.mul_mem x.2 hK) (K₁.inv_mem x.2)⟩
    have hmem : toPerm P.α ⟨h, hK⟩ ∈ klein p := (c.memS_iff P hp ⟨h, hK⟩).mp hS
    have h1 : toPerm P.α (x * ⟨h, hK⟩ * x⁻¹) ∈ klein p := by
      rw [map_mul, map_mul, map_inv]
      exact hkl _ hx _ hmem
    exact (c.memS_iff P hp _).mpr h1
  · rintro ⟨hS, hK⟩
    have hhK : h ∈ K₁ := by
      have := K₁.mul_mem (K₁.mul_mem (K₁.inv_mem x.2) hK) x.2
      simpa [mul_assoc] using this
    refine ⟨?_, hhK⟩
    have hmem : toPerm P.α (x * ⟨h, hhK⟩ * x⁻¹) ∈ klein p :=
      (c.memS_iff P hp (x * ⟨h, hhK⟩ * x⁻¹)).mp hS
    have hxinv : (toPerm P.α x)⁻¹ p = p := by
      rw [Equiv.Perm.inv_eq_iff_eq]
      exact hx.symm
    have hmem' : toPerm P.α x * toPerm P.α ⟨h, hhK⟩ * (toPerm P.α x)⁻¹ ∈ klein p := by
      simpa [map_mul, map_inv] using hmem
    have h1 := hkl _ hxinv _ hmem'
    have e : (toPerm P.α x)⁻¹ * (toPerm P.α x * toPerm P.α ⟨h, hhK⟩ * (toPerm P.α x)⁻¹) *
        ((toPerm P.α x)⁻¹)⁻¹ = toPerm P.α ⟨h, hhK⟩ := by group
    rw [e] at h1
    exact (c.memS_iff P hp ⟨h, hhK⟩).mpr h1

omit [Finite G] c in
theorem exists_lift {L : Subgroup G} (P : AppC.A5Pi L) (σ : Perm (Fin 5)) (hσ : Perm.sign σ = 1) :
    ∃ x : ↥L, toPerm P.α x = σ := by
  obtain ⟨x, hx⟩ := P.hα ⟨σ, Equiv.Perm.mem_alternatingGroup.mpr hσ⟩
  exact ⟨x, by rw [toPerm_apply, hx]⟩

theorem inf_Iz_fix (P : AppC.A5Pi K₁) {p : Fin 5} (hp : ∀ g ∈ imgS K₁ S P.α, g p = p)
    (hnot : ¬ K₁ ≤ Iz) (y : ↥K₁) (hy : (y : G) ∈ Iz) : toPerm P.α y p = p := by
  by_contra hmove
  apply hnot
  have hlift : ∀ σ : Perm (Fin 5), σ p = p → ∀ x : ↥K₁, toPerm P.α x = σ → (x : G) ∈ Iz := by
    intro σ hσp x hx
    exact c.normalizer_le_Iz₁ P.hα P.hαk x x.2
      (c.mem_normalizer_inf_of_fix P hp x (by rw [hx]; exact hσp))
  have hker := c.ker_le₁ P.hαk
  intro g hg
  have hσsign : Perm.sign (toPerm P.α ⟨g, hg⟩) = 1 := sign_toPerm _
  by_cases hσp : toPerm P.α ⟨g, hg⟩ p = p
  · exact hlift _ hσp ⟨g, hg⟩ rfl
  · obtain ⟨a, ha_sign, ha_p, ha_q⟩ :=
      exists_fix_mapping p (toPerm P.α y p) (toPerm P.α ⟨g, hg⟩ p) hmove hσp
    set σ := toPerm P.α ⟨g, hg⟩ with hσdef
    set h := toPerm P.α y with hhdef
    have hb_sign : Perm.sign (h⁻¹ * a⁻¹ * σ) = 1 := by
      simp [Perm.sign_mul, Perm.sign_inv, ha_sign, hσsign, hhdef, sign_toPerm]
    have hb_p : (h⁻¹ * a⁻¹ * σ) p = p := by
      have h1 : a⁻¹ (σ p) = h p := by
        rw [← ha_q]
        exact a.symm_apply_apply _
      simp only [Perm.mul_apply, h1]
      exact h.symm_apply_apply p
    obtain ⟨a', ha'⟩ := exists_lift P a ha_sign
    obtain ⟨b', hb'⟩ := exists_lift P (h⁻¹ * a⁻¹ * σ) hb_sign
    have ha'I : (a' : G) ∈ Iz := hlift a ha_p a' ha'
    have hb'I : (b' : G) ∈ Iz := hlift _ hb_p b' hb'
    have hg'I : ((a' * y * b' : ↥K₁) : G) ∈ Iz := Iz.mul_mem (Iz.mul_mem ha'I hy) hb'I
    have hg'σ : toPerm P.α (a' * y * b') = σ := by
      rw [map_mul, map_mul, ha', hb', ← hhdef]
      group
    have hα1 : P.α ((a' * y * b')⁻¹ * ⟨g, hg⟩) = 1 := by
      have := (toPerm_eq_iff (α := P.α) (a' * y * b') ⟨g, hg⟩).mp hg'σ
      rw [map_mul, map_inv, this, inv_mul_cancel]
    have hS : (((a' * y * b')⁻¹ * ⟨g, hg⟩ : ↥K₁) : G) ∈ S := hker _ hα1
    have e : g = ((a' * y * b' : ↥K₁) : G) * (((a' * y * b')⁻¹ * ⟨g, hg⟩ : ↥K₁) : G) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [e]
    exact Iz.mul_mem hg'I (c.S_le_Iz hS)

theorem inf_Iz_le_normalizer (P : AppC.A5Pi K₁) {p : Fin 5}
    (hp : ∀ g ∈ imgS K₁ S P.α, g p = p) (hnot : ¬ K₁ ≤ Iz) :
    ∀ y ∈ K₁, y ∈ Iz → y ∈ Subgroup.normalizer ((S ⊓ K₁ : Subgroup G) : Set G) := fun y hyK hyI =>
  c.mem_normalizer_inf_of_fix P hp ⟨y, hyK⟩ (c.inf_Iz_fix P hp hnot ⟨y, hyK⟩ hyI)

omit [Finite G] c in
theorem pf_pow_four {L : Subgroup G} (P : AppC.A5Pi L) {x : G}
    (hxN : x ∈ Subgroup.normalizer (L : Set G)) (hx : ∃ n : ℕ, x ^ 2 ^ n = 1) :
    (P.toPiData.pf x) ^ 4 = 1 := by
  obtain ⟨n, hn⟩ := hx
  apply pow_four_of_two_power
  refine ⟨n, ?_⟩
  rw [P.toPiData.pf_eq hxN, ← map_pow]
  have : (⟨x, hxN⟩ : ↥(Subgroup.normalizer (L : Set G))) ^ 2 ^ n = 1 := Subtype.ext (by simpa using hn)
  rw [this, map_one]

theorem lift_mem_Iz (P : AppC.A5Pi K₁) {p : Fin 5} (hp : ∀ g ∈ imgS K₁ S P.α, g p = p)
    {σ : Perm (Fin 5)} (hσp : σ p = p) (x : ↥K₁) (hx : toPerm P.α x = σ) : (x : G) ∈ Iz :=
  c.normalizer_le_Iz₁ P.hα P.hαk x x.2 (c.mem_normalizer_inf_of_fix P hp x (by rw [hx]; exact hσp))

theorem pf_mem_klein_of_mem_R (P : AppC.A5Pi K₁) {p : Fin 5} (hp : ∀ g ∈ imgS K₁ S P.α, g p = p)
    {r : G} (hr : r ∈ pCoreOf 2 Iz) : P.toPiData.pf r ∈ klein p := by
  have hrN : r ∈ Subgroup.normalizer (K₁ : Set G) := c.R_le_normalizer₁ hr
  have hR2 : IsPGroup 2 (pCoreOf 2 Iz) := pCoreOf_isPGroup 2 Iz
  apply mem_klein_of_two_group
  · exact pf_pow_four P hrN (C1.exists_pow_eq_one_of_isPGroup hR2 hr |>.imp fun _ h => h)
  · intro γ hγs hγp
    obtain ⟨g, hg⟩ := exists_lift P γ hγs
    have hgIz : (g : G) ∈ Iz := c.lift_mem_Iz P hp hγp g hg
    have hgN : (g : G) ∈ Subgroup.normalizer (K₁ : Set G) := Subgroup.le_normalizer g.2
    have h1 : (g : G) * r * (g : G)⁻¹ ∈ pCoreOf 2 Iz :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 Iz hgIz) r).mp hr
    have hcomm : (g : G) * r * (g : G)⁻¹ * r⁻¹ ∈ pCoreOf 2 Iz :=
      (pCoreOf 2 Iz).mul_mem h1 ((pCoreOf 2 Iz).inv_mem hr)
    have hcN : (g : G) * r * (g : G)⁻¹ * r⁻¹ ∈ Subgroup.normalizer (K₁ : Set G) :=
      c.R_le_normalizer₁ hcomm
    have hpow := pf_pow_four P hcN (C1.exists_pow_eq_one_of_isPGroup hR2 hcomm)
    have hgpf : P.toPiData.pf (g : G) = γ := by
      rw [pf_eq_alpha P g.2]
      have : (⟨(g : G), g.2⟩ : ↥K₁) = g := rfl
      rw [this, ← toPerm_apply, hg]
    have e : P.toPiData.pf ((g : G) * r * (g : G)⁻¹ * r⁻¹) =
        γ * P.toPiData.pf r * γ⁻¹ * (P.toPiData.pf r)⁻¹ := by
      have hginv : (g : G)⁻¹ ∈ Subgroup.normalizer (K₁ : Set G) := inv_mem hgN
      have hrinv : r⁻¹ ∈ Subgroup.normalizer (K₁ : Set G) := inv_mem hrN
      rw [P.toPiData.pf_mul (mul_mem (mul_mem hgN hrN) hginv) hrinv,
        P.toPiData.pf_mul (mul_mem hgN hrN) hginv, P.toPiData.pf_mul hgN hrN,
        P.toPiData.pf_inv hgN, P.toPiData.pf_inv hrN, hgpf]
    rw [← e]
    exact hpow

theorem exists_mem_inf_pf_eq (P : AppC.A5Pi K₁) {p : Fin 5} (hp : ∀ g ∈ imgS K₁ S P.α, g p = p)
    {w : Perm (Fin 5)} (hw : w ∈ klein p) : ∃ s ∈ S ⊓ K₁, P.toPiData.pf s = w := by
  have hker := c.ker_le₁ P.hαk
  have hmem : w ∈ imgS K₁ S P.α := (imgS_eq_klein P.hα hker c.sylow₁ hp w).mpr hw
  obtain ⟨x, hx, hxw⟩ := Subgroup.mem_map.mp hmem
  refine ⟨(x : G), Subgroup.mem_subgroupOf.mp hx, ?_⟩
  rw [pf_eq_alpha P x.2]
  have : (⟨(x : G), x.2⟩ : ↥K₁) = x := rfl
  rw [this, ← toPerm_apply, hxw]

theorem mem_normalizer_of_mul_mem_Iz (P : AppC.A5Pi K₁) {p : Fin 5}
    (hp : ∀ g ∈ imgS K₁ S P.α, g p = p) (hnot : ¬ K₁ ≤ Iz) {k₁ k₂ : G} (hk₁ : k₁ ∈ K₁)
    (hk₂ : k₂ ∈ K₂) (hy : k₁ * k₂ ∈ Iz) :
    k₁ ∈ Subgroup.normalizer ((S ⊓ K₁ : Subgroup G) : Set G) := by
  refine c.mem_normalizer_inf_of_fix P hp ⟨k₁, hk₁⟩ ?_
  refine fixes_of_normalizes p _ (sign_toPerm _) fun τ hτs hτp => ?_
  obtain ⟨t, ht⟩ := exists_lift P τ hτs
  have htIz : (t : G) ∈ Iz := c.lift_mem_Iz P hp hτp t ht
  have hzK : k₁ * (t : G) * k₁⁻¹ ∈ K₁ := K₁.mul_mem (K₁.mul_mem hk₁ t.2) (K₁.inv_mem hk₁)
  have hzIz : k₁ * (t : G) * k₁⁻¹ ∈ Iz := by
    have h1 := Iz.mul_mem (Iz.mul_mem hy htIz) (Iz.inv_mem hy)
    have h2 : k₁ * k₂ * (t : G) * (k₁ * k₂)⁻¹ = k₁ * (t : G) * k₁⁻¹ := by
      have hc := c.comm (t : G) t.2 k₂ hk₂
      calc k₁ * k₂ * (t : G) * (k₁ * k₂)⁻¹ = k₁ * (k₂ * t * k₂⁻¹) * k₁⁻¹ := by group
        _ = k₁ * (t * k₂ * k₂⁻¹) * k₁⁻¹ := by rw [← hc]
        _ = k₁ * (t : G) * k₁⁻¹ := by group
    rwa [h2] at h1
  have hfix := c.inf_Iz_fix P hp hnot ⟨k₁ * (t : G) * k₁⁻¹, hzK⟩ hzIz
  have e : toPerm P.α (⟨k₁ * (t : G) * k₁⁻¹, hzK⟩ : ↥K₁) =
      toPerm P.α ⟨k₁, hk₁⟩ * τ * (toPerm P.α ⟨k₁, hk₁⟩)⁻¹ := by
    have : (⟨k₁ * (t : G) * k₁⁻¹, hzK⟩ : ↥K₁) = ⟨k₁, hk₁⟩ * t * ⟨k₁, hk₁⟩⁻¹ := rfl
    rw [this, map_mul, map_mul, map_inv, ht]
  rw [e] at hfix
  exact hfix

omit [Finite G] in
theorem S_le_normalizer_P :
    S ≤ Subgroup.normalizer (((S ⊓ K₁) ⊔ (S ⊓ K₂) : Subgroup G) : Set G) := by
  set B := (S ⊓ K₁) ⊔ (S ⊓ K₂) with hBdef
  have hSB : ∀ s ∈ S, B6.conjSub s B ≤ B := by
    intro s hs
    have hS' : B6.conjSub s S = S := B6.conjSub_eq_self (Subgroup.le_normalizer hs)
    rw [hBdef, OrderIso.map_sup, OrderIso.map_inf, OrderIso.map_inf, hS']
    refine sup_le ?_ ?_
    · rcases c.perm₁ s hs with h | h
      · rw [h]; exact le_sup_left
      · rw [h]; exact le_sup_right
    · rcases c.perm₂ s hs with h | h
      · rw [h]; exact le_sup_left
      · rw [h]; exact le_sup_right
  exact fun s hs => B6.mem_normalizer_of_conjSub_le (hSB s hs) (hSB s⁻¹ (S.inv_mem hs))

theorem Iz_le_normalizer_P (hnot₁ : ¬ K₁ ≤ Iz) (hnot₂ : ¬ K₂ ≤ Iz) :
    Iz ≤ Subgroup.normalizer (((S ⊓ K₁) ⊔ (S ⊓ K₂) : Subgroup G) : Set G) := by
  obtain ⟨α₁, hα₁, hαk₁, -⟩ := c.a5₁
  obtain ⟨P₁, -⟩ := AppC.exists_a5pi c.blk₁.1 c.a5₁ α₁ hα₁ hαk₁
  obtain ⟨p₁, hp₁⟩ := exists_fixed (α := P₁.α) c.sylow₁
  obtain ⟨α₂, hα₂, hαk₂, -⟩ := c.a5₂
  obtain ⟨P₂, -⟩ := AppC.exists_a5pi c.blk₂.1 c.a5₂ α₂ hα₂ hαk₂
  obtain ⟨p₂, hp₂⟩ := exists_fixed (α := P₂.α) c.symm.sylow₁
  intro y hy
  have hyI : y ∈ I := c.Iz_le_I hy
  have hy' : y ∈ ((S : Subgroup G) : Set G) * ((K₁ ⊔ K₂ : Subgroup G) : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right S (K₁ ⊔ K₂) c.S_le_normalizer_sup, ← c.gen]
    exact hyI
  obtain ⟨s, hs, k, hk, rfl⟩ := hy'
  have hk' : k ∈ ((K₁ : Subgroup G) : Set G) * ((K₂ : Subgroup G) : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right K₁ K₂ c.K₁_le_normalizer₂]
    exact hk
  obtain ⟨k₁, hk₁, k₂, hk₂, rfl⟩ := hk'
  have hkIz : k₁ * k₂ ∈ Iz := by
    have := Iz.mul_mem (Iz.inv_mem (c.S_le_Iz hs)) hy
    simpa [mul_assoc] using this
  have hkIz' : k₂ * k₁ ∈ Iz := by rw [← c.comm k₁ hk₁ k₂ hk₂]; exact hkIz
  have hn₁ := c.mem_normalizer_of_mul_mem_Iz P₁ hp₁ hnot₁ hk₁ hk₂ hkIz
  have hn₂ := c.symm.mem_normalizer_of_mul_mem_Iz P₂ hp₂ hnot₂ hk₂ hk₁ hkIz'
  have hn₁' : k₁ ∈ Subgroup.normalizer ((S ⊓ K₂ : Subgroup G) : Set G) :=
    Lin2.le_normalizer_of_commute (A := S ⊓ K₂) (B := K₁)
      (fun a ha b hb => (c.comm b hb a ha.2).symm) hk₁
  have hn₂' : k₂ ∈ Subgroup.normalizer ((S ⊓ K₁ : Subgroup G) : Set G) :=
    Lin2.le_normalizer_of_commute (A := S ⊓ K₁) (B := K₂)
      (fun a ha b hb => c.comm a ha.2 b hb) hk₂
  exact mul_mem (c.S_le_normalizer_P hs) (mul_mem (mem_normalizer_sup hn₁ hn₁')
    (mem_normalizer_sup hn₂' hn₂))

theorem P_le_pCoreIz (hnot₁ : ¬ K₁ ≤ Iz) (hnot₂ : ¬ K₂ ≤ Iz) :
    (S ⊓ K₁) ⊔ (S ⊓ K₂) ≤ pCoreOf 2 Iz :=
  le_pCoreOf_of_le_normalizer 2 ((sup_le inf_le_left inf_le_left).trans c.S_le_Iz)
    (c.Iz_le_normalizer_P hnot₁ hnot₂) (c.sylow.isPGroup.to_le (sup_le inf_le_left inf_le_left))

theorem mem_pCoreOf_of_central {a : G} (haS : a ∈ S)
    (haN₁ : a ∈ Subgroup.normalizer (K₁ : Set G)) (haN₂ : a ∈ Subgroup.normalizer (K₂ : Set G))
    (hU₁ : ∀ u ∈ blockU K₁, a * u * a⁻¹ = u) (hU₂ : ∀ u ∈ blockU K₂, a * u * a⁻¹ = u) :
    a ∈ pCoreOf 2 I := by
  have haI : a ∈ I := c.sylow.le haS
  refine mem_pCoreOf_of_conj_mem c.sylow.isPGroup haI fun x hx => ?_
  have hx' : x ∈ ((S : Subgroup G) : Set G) * ((K₁ ⊔ K₂ : Subgroup G) : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right S (K₁ ⊔ K₂) c.S_le_normalizer_sup, ← c.gen]
    exact hx
  obtain ⟨s, hs, k, hk, rfl⟩ := hx'
  have hk' : k ∈ ((K₁ : Subgroup G) : Set G) * ((K₂ : Subgroup G) : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right K₁ K₂ c.K₁_le_normalizer₂]
    exact hk
  obtain ⟨k₁, hk₁, k₂, hk₂, rfl⟩ := hk'
  have q₁ := c.comm_mem_pCore₁ haN₁ hU₁ hk₁
  have q₂ := c.symm.comm_mem_pCore₁ haN₂ hU₂ hk₂
  have hq₂K : k₂ * a * k₂⁻¹ * a⁻¹ ∈ K₂ := pCoreOf_le 2 K₂ q₂
  have hcomm : k₁ * (k₂ * a * k₂⁻¹ * a⁻¹) = (k₂ * a * k₂⁻¹ * a⁻¹) * k₁ := c.comm k₁ hk₁ _ hq₂K
  have e : s * (k₁ * k₂) * a * (s * (k₁ * k₂))⁻¹ =
      s * ((k₂ * a * k₂⁻¹ * a⁻¹) * (k₁ * a * k₁⁻¹ * a⁻¹) * a) * s⁻¹ := by
    have h1 : s * (k₁ * k₂) * a * (s * (k₁ * k₂))⁻¹ =
        s * (k₁ * ((k₂ * a * k₂⁻¹ * a⁻¹) * a) * k₁⁻¹) * s⁻¹ := by group
    rw [h1]
    have h2 : k₁ * ((k₂ * a * k₂⁻¹ * a⁻¹) * a) * k₁⁻¹ =
        (k₁ * (k₂ * a * k₂⁻¹ * a⁻¹) * k₁⁻¹) * (k₁ * a * k₁⁻¹) := by group
    rw [h2]
    have h3 : k₁ * (k₂ * a * k₂⁻¹ * a⁻¹) * k₁⁻¹ = k₂ * a * k₂⁻¹ * a⁻¹ := by
      rw [hcomm]; group
    rw [h3]
    group
  rw [e]
  have hq₁S : k₁ * a * k₁⁻¹ * a⁻¹ ∈ S := (c.pCore_le₁ q₁).1
  have hq₂S : k₂ * a * k₂⁻¹ * a⁻¹ ∈ S := (c.symm.pCore_le₁ q₂).1
  exact S.mul_mem (S.mul_mem hs (S.mul_mem (S.mul_mem hq₂S hq₁S) haS)) (S.inv_mem hs)

theorem exists_decomp_R {r : G} (hr : r ∈ pCoreOf 2 Iz) :
    ∃ d ∈ dsub S K₁ K₂, ∃ s₁ ∈ S ⊓ K₁, ∃ s₂ ∈ S ⊓ K₂, r = d * (s₁ * s₂) := by
  obtain ⟨α₁, hα₁, hαk₁, -⟩ := c.a5₁
  obtain ⟨P₁, -⟩ := AppC.exists_a5pi c.blk₁.1 c.a5₁ α₁ hα₁ hαk₁
  obtain ⟨p₁, hp₁⟩ := exists_fixed (α := P₁.α) c.sylow₁
  obtain ⟨α₂, hα₂, hαk₂, -⟩ := c.a5₂
  obtain ⟨P₂, -⟩ := AppC.exists_a5pi c.blk₂.1 c.a5₂ α₂ hα₂ hαk₂
  obtain ⟨p₂, hp₂⟩ := exists_fixed (α := P₂.α) c.symm.sylow₁
  have hrS : r ∈ S := c.R_le_S hr
  have hrN₁ : r ∈ Subgroup.normalizer (K₁ : Set G) := c.R_le_normalizer₁ hr
  have hrN₂ : r ∈ Subgroup.normalizer (K₂ : Set G) := c.R_le_normalizer₂ hr
  obtain ⟨s₁, hs₁, hs₁pf⟩ := c.exists_mem_inf_pf_eq P₁ hp₁ (c.pf_mem_klein_of_mem_R P₁ hp₁ hr)
  obtain ⟨s₂, hs₂, hs₂pf⟩ := c.symm.exists_mem_inf_pf_eq P₂ hp₂ (c.symm.pf_mem_klein_of_mem_R P₂ hp₂ hr)
  have hs₁K : s₁ ∈ K₁ := hs₁.2
  have hs₂K : s₂ ∈ K₂ := hs₂.2
  have hs₁N₁ : s₁ ∈ Subgroup.normalizer (K₁ : Set G) := Subgroup.le_normalizer hs₁K
  have hs₂N₂ : s₂ ∈ Subgroup.normalizer (K₂ : Set G) := Subgroup.le_normalizer hs₂K
  have hs₁N₂ : s₁ ∈ Subgroup.normalizer (K₂ : Set G) := c.K₁_le_normalizer₂ hs₁K
  have hs₂N₁ : s₂ ∈ Subgroup.normalizer (K₁ : Set G) :=
    Lin2.le_normalizer_of_commute (A := K₁) (B := K₂) (fun a ha b hb => c.comm a ha b hb) hs₂K
  have hs₂U₁ : ∀ u ∈ blockU K₁, s₂ * u * s₂⁻¹ = u := fun u hu => by
    have := c.comm u (c.U₁_le_K₁ hu) s₂ hs₂K
    calc s₂ * u * s₂⁻¹ = (s₂ * u) * s₂⁻¹ := rfl
      _ = (u * s₂) * s₂⁻¹ := by rw [← this]
      _ = u := by group
  have hs₁U₂ : ∀ u ∈ blockU K₂, s₁ * u * s₁⁻¹ = u := fun u hu => by
    have := c.comm s₁ hs₁K u (c.U₂_le_K₂ hu)
    calc s₁ * u * s₁⁻¹ = (s₁ * u) * s₁⁻¹ := rfl
      _ = (u * s₁) * s₁⁻¹ := by rw [this]
      _ = u := by group
  have hpf₂s₂ : P₁.toPiData.pf s₂ = 1 := by
    have : P₁.π ⟨s₂, hs₂N₁⟩ = 1 := (P₁.hker ⟨s₂, hs₂N₁⟩).mpr hs₂U₁
    rw [P₁.toPiData.pf_eq hs₂N₁]
    exact this
  have hpf₁s₁ : P₂.toPiData.pf s₁ = 1 := by
    have : P₂.π ⟨s₁, hs₁N₂⟩ = 1 := (P₂.hker ⟨s₁, hs₁N₂⟩).mpr hs₁U₂
    rw [P₂.toPiData.pf_eq hs₁N₂]
    exact this
  have hqN₁ : (s₁ * s₂)⁻¹ * r ∈ Subgroup.normalizer (K₁ : Set G) :=
    mul_mem (inv_mem (mul_mem hs₁N₁ hs₂N₁)) hrN₁
  have hqN₂ : (s₁ * s₂)⁻¹ * r ∈ Subgroup.normalizer (K₂ : Set G) :=
    mul_mem (inv_mem (mul_mem hs₁N₂ hs₂N₂)) hrN₂
  have hqpf₁ : P₁.toPiData.pf ((s₁ * s₂)⁻¹ * r) = 1 := by
    rw [P₁.toPiData.pf_mul (inv_mem (mul_mem hs₁N₁ hs₂N₁)) hrN₁,
      P₁.toPiData.pf_inv (mul_mem hs₁N₁ hs₂N₁), P₁.toPiData.pf_mul hs₁N₁ hs₂N₁, hpf₂s₂, mul_one,
      hs₁pf, inv_mul_cancel]
  have hqpf₂ : P₂.toPiData.pf ((s₁ * s₂)⁻¹ * r) = 1 := by
    rw [P₂.toPiData.pf_mul (inv_mem (mul_mem hs₁N₂ hs₂N₂)) hrN₂,
      P₂.toPiData.pf_inv (mul_mem hs₁N₂ hs₂N₂), P₂.toPiData.pf_mul hs₁N₂ hs₂N₂, hpf₁s₁, one_mul,
      hs₂pf, inv_mul_cancel]
  have hqU₁ : ∀ u ∈ blockU K₁, (s₁ * s₂)⁻¹ * r * u * ((s₁ * s₂)⁻¹ * r)⁻¹ = u := fun u hu => by
    have h1 : P₁.π ⟨(s₁ * s₂)⁻¹ * r, hqN₁⟩ = 1 := by
      rw [← P₁.toPiData.pf_mk ⟨_, hqN₁⟩]
      exact hqpf₁
    exact (P₁.hker ⟨_, hqN₁⟩).mp h1 u hu
  have hqU₂ : ∀ u ∈ blockU K₂, (s₁ * s₂)⁻¹ * r * u * ((s₁ * s₂)⁻¹ * r)⁻¹ = u := fun u hu => by
    have h1 : P₂.π ⟨(s₁ * s₂)⁻¹ * r, hqN₂⟩ = 1 := by
      rw [← P₂.toPiData.pf_mk ⟨_, hqN₂⟩]
      exact hqpf₂
    exact (P₂.hker ⟨_, hqN₂⟩).mp h1 u hu
  have hqS : (s₁ * s₂)⁻¹ * r ∈ S :=
    S.mul_mem (S.inv_mem (S.mul_mem hs₁.1 hs₂.1)) hrS
  have hqQ : (s₁ * s₂)⁻¹ * r ∈ pCoreOf 2 I :=
    c.mem_pCoreOf_of_central hqS hqN₁ hqN₂ hqU₁ hqU₂
  obtain ⟨d, hd, u₁, hu₁, u₂, hu₂, hdu⟩ := c.exists_split_Q hqQ
  have hu₁S : u₁ ∈ S ⊓ K₁ := ⟨(c.pCore_le₁ (C1.blockU_le_blockQ c.blk₁.1 hu₁)).1, c.U₁_le_K₁ hu₁⟩
  have hu₂S : u₂ ∈ S ⊓ K₂ := ⟨(c.symm.pCore_le₁ (C1.blockU_le_blockQ c.blk₂.1 hu₂)).1,
    c.U₂_le_K₂ hu₂⟩
  refine ⟨d, hd, s₁ * u₁, (S ⊓ K₁).mul_mem hs₁ hu₁S, s₂ * u₂, (S ⊓ K₂).mul_mem hs₂ hu₂S, ?_⟩
  have hr' : r = (s₁ * s₂) * ((s₁ * s₂)⁻¹ * r) := by group
  have hdK : ∀ x ∈ K₁ ⊔ K₂, x * d = d * x := fun x hx => K_le_centralizer_dsub x hx d hd
  have hd₁ : s₁ * d = d * s₁ := hdK s₁ (Subgroup.mem_sup_left hs₁K)
  have hd₂ : s₂ * d = d * s₂ := hdK s₂ (Subgroup.mem_sup_right hs₂K)
  have hc₂₁ : s₂ * u₁ = u₁ * s₂ := (c.comm u₁ (c.U₁_le_K₁ hu₁) s₂ hs₂K).symm
  rw [hr', hdu]
  calc (s₁ * s₂) * (d * (u₁ * u₂)) = s₁ * (s₂ * d) * (u₁ * u₂) := by group
    _ = s₁ * (d * s₂) * (u₁ * u₂) := by rw [hd₂]
    _ = (s₁ * d) * (s₂ * u₁) * u₂ := by group
    _ = (d * s₁) * (u₁ * s₂) * u₂ := by rw [hd₁, hc₂₁]
    _ = d * ((s₁ * u₁) * (s₂ * u₂)) := by group

end A5Cfg

end CFSG.Quasithin.ModF
