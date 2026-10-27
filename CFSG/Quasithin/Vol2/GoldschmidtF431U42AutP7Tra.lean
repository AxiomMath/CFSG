module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP7Cl
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP7Cnt

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open U42F431
open CFSG.Quasithin.H13.F431.U42 (P45)

variable {G : Type} [Group G] [Finite G] {M₁ M₂ : Subgroup G} {z : G}

theorem claimT_core (c : AutCtx G M₁ M₂ z) {T₀ A : Subgroup G} (hT₀ : IsSylowTwoOf T₀ M₁)
    (hAab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hAsq : ∀ a ∈ A, a * a = 1)
    (hAcard : Nat.card ↥A = 16)
    (hcl : ∀ γ : G, B6.conjSub γ A ≤ T₀ → ∃ k ∈ M₁, B6.conjSub γ A = B6.conjSub k A) :
    ∀ u ∈ A, IsConj u z → ∃ n ∈ Subgroup.normalizer (A : Set G), n * z * n⁻¹ = u := by
  intro u hu hconj
  obtain ⟨c0, hc0⟩ := isConj_iff.1 hconj
  have hM1z : ∀ k ∈ M₁, k * z = z * k := fun k hk => by
    have : k ∈ cenOf z := by rw [c.cenOf_z]; exact hk
    exact Subgroup.mem_centralizer_singleton_iff.1 this
  set A' := B6.conjSub c0 A with hA'
  have hzA' : z ∈ A' := by
    rw [hA', B6.mem_conjSub]
    have : c0⁻¹ * z * c0 = u := by rw [← hc0]; group
    rw [this]
    exact hu
  have hA'ab := (conjSub_E16 c0 hAab hAsq).1
  have hA2 : IsPGroup 2 A := IsPGroup.of_card (n := 4) (by rw [hAcard]; norm_num)
  have hA2' : IsPGroup 2 A' :=
    hA2.of_equiv (Subgroup.equivMapOfInjective A (MulAut.conj c0).toMonoidHom
      (MulAut.conj c0).injective)
  have hA'M₁ : A' ≤ M₁ := by
    intro a ha
    apply c.cz
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hA'ab a ha z hzA'
  obtain ⟨S, hS, hA'S⟩ := B6.exists_isSylowTwoOf_ge hA2' hA'M₁
  obtain ⟨m, hmM, hTm⟩ := B6.isSylowTwoOf_exists_conj hS hT₀
  have hγ : B6.conjSub (m * c0) A ≤ T₀ := by
    rw [B6.conjSub_mul, hTm]
    exact (B6.conjSub m).monotone hA'S
  obtain ⟨k, hkM, hk⟩ := hcl (m * c0) hγ
  have hn₀ : k⁻¹ * (m * c0) ∈ Subgroup.normalizer (A : Set G) := by
    refine mem_normalizer_of_conjSub_eq ?_
    rw [B6.conjSub_mul, hk, ← B6.conjSub_mul, inv_mul_cancel, B6.conjSub_one]
  refine ⟨(k⁻¹ * (m * c0))⁻¹, Subgroup.inv_mem _ hn₀, ?_⟩
  have hkz : k * z * k⁻¹ = z := by
    rw [hM1z k hkM]
    group
  have hmz : m * z * m⁻¹ = z := by
    rw [hM1z m hmM]
    group
  have e1 : (k⁻¹ * (m * c0))⁻¹ * z * ((k⁻¹ * (m * c0))⁻¹)⁻¹ =
      c0⁻¹ * (m⁻¹ * (k * z * k⁻¹) * m) * c0 := by group
  rw [e1, hkz]
  have hmz' : m⁻¹ * z * m = z := by
    have := hM1z m hmM
    calc m⁻¹ * z * m = m⁻¹ * (z * m) := by group
      _ = m⁻¹ * (m * z) := by rw [this]
      _ = z := by group
  rw [hmz']
  rw [← hc0]
  group

section Cases

variable (c : AutCtx G M₁ M₂ z) (hZ : ZStmt c)

include hZ

theorem conj_A1_cases {γ : G} (hγ : B6.conjSub γ (c.iso.imgG A1h) ≤ c.iso.imgG That) :
    B6.conjSub γ (c.iso.imgG A1h) = c.iso.imgG A1h ∨
      B6.conjSub γ (c.iso.imgG A1h) = c.iso.imgG VA := by
  have hab := (imgG_E16 c.iso (K := A1h) (fun a ha b hb => A1h_comm ha hb) fun a ha => A1h_sq ha)
  have hcE := conjSub_E16 γ hab.1 hab.2
  have hcard : Nat.card ↥(B6.conjSub γ (c.iso.imgG A1h)) = 16 := by
    rw [conjSub_card, c.iso.card_imgG (A1h_le_That.trans That_le_Bh), card_A1h]
  have h5 : (Om (B6.conjSub γ (c.iso.imgG A1h)) z).ncard = 5 := by
    rw [ncard_Om_conjSub]
    exact ncard_Om_A1 c hZ
  rcases e16_G c.iso hγ hcard hcE.1 hcE.2 with h | h | h | h
  · exact Or.inl h
  · exfalso
    rw [h, ncard_Om_A2 c hZ] at h5
    omega
  · exfalso
    rw [h, ncard_Om_conjSub, ncard_Om_A2 c hZ] at h5
    omega
  · exact Or.inr h

theorem conj_A2_cases {γ : G} (hγ : B6.conjSub γ (c.iso.imgG A2h) ≤ c.iso.imgG That) :
    B6.conjSub γ (c.iso.imgG A2h) = c.iso.imgG A2h ∨
      B6.conjSub γ (c.iso.imgG A2h) = B6.conjSub (c.iso.toG yB) (c.iso.imgG A2h) := by
  have hab := (imgG_E16 c.iso (K := A2h) (fun a ha b hb => A2h_comm ha hb) fun a ha => A2h_sq ha)
  have hcE := conjSub_E16 γ hab.1 hab.2
  have hcard : Nat.card ↥(B6.conjSub γ (c.iso.imgG A2h)) = 16 := by
    rw [conjSub_card, c.iso.card_imgG (A2h_le_That.trans That_le_Bh), card_A2h]
  have h9 : (Om (B6.conjSub γ (c.iso.imgG A2h)) z).ncard = 9 := by
    rw [ncard_Om_conjSub]
    exact ncard_Om_A2 c hZ
  rcases e16_G c.iso hγ hcard hcE.1 hcE.2 with h | h | h | h
  · exfalso
    rw [h, ncard_Om_A1 c hZ] at h9
    omega
  · exact Or.inl h
  · exact Or.inr h
  · exfalso
    rw [h, ncard_Om_VA c hZ] at h9
    omega

end Cases

omit [Finite G] in
theorem imgG_mono' (iso : AutIso M₁ M₂) {K L : Subgroup Ah} (h : K ≤ L) :
    iso.imgG K ≤ iso.imgG L := by
  intro g hg
  obtain ⟨b, hb, rfl⟩ := iso.mem_imgG.1 hg
  exact iso.mem_imgG.2 ⟨b, h hb, rfl⟩

omit [Finite G] in
theorem imgG_le_normalizer (iso : AutIso M₁ M₂) {K L : Subgroup Ah}
    (h : K ≤ Subgroup.normalizer (L : Set Ah)) :
    iso.imgG K ≤ Subgroup.normalizer (iso.imgG L : Set G) := by
  intro g hg
  obtain ⟨b, hb, rfl⟩ := iso.mem_imgG.1 hg
  refine mem_normalizer_of_conjSub_eq ?_
  rw [← iso.imgG_conjSub b L, B6.conjSub_eq_self (h hb)]

omit [Finite G] in
theorem imgG_A1h_ne_VA (iso : AutIso M₁ M₂) : iso.imgG A1h ≠ iso.imgG VA := by
  have hne : ∃ l ∈ Al1, l ∉ Vl := by decide +kernel
  obtain ⟨l, hl, hlV⟩ := hne
  have hlT : l ∈ Thl := A1_check.2.2.2.1 l hl
  intro h
  have hrep : RepL l (eltB l : P45) := by
    rw [coe_eltB hlT]
    exact repL_eltOfL hlT
  have hmem : iso.toG (eltB l) ∈ iso.imgG A1h := iso.mem_imgG.2 ⟨eltB l, ⟨l, hl, hrep⟩, rfl⟩
  rw [h] at hmem
  obtain ⟨b, hb, hbg⟩ := iso.mem_imgG.1 hmem
  have : b = eltB l := iso.toG_injective hbg
  rw [this] at hb
  obtain ⟨l', hl', hrep'⟩ := (mem_VA_iff _).1 hb
  have := repL_unique hrep' hrep
  exact hlV (this ▸ hl')

theorem isSylowTwoOf_T₀_M₁ (c : AutCtx G M₁ M₂ z) (hT₀G : IsSylowTwoOf (c.iso.imgG That) ⊤) :
    IsSylowTwoOf (c.iso.imgG That) M₁ :=
  B6.isSylowTwoOf_mono hT₀G ((c.iso.imgG_le That).trans inf_le_left) le_top

section Instances

variable (c : AutCtx G M₁ M₂ z) (hZ : ZStmt c) (hT₀G : IsSylowTwoOf (c.iso.imgG That) ⊤)

include hZ hT₀G

theorem claimT_A1 : ∀ u ∈ c.iso.imgG A1h, IsConj u z →
    ∃ n ∈ Subgroup.normalizer (c.iso.imgG A1h : Set G), n * z * n⁻¹ = u := by
  have hab := (imgG_E16 c.iso (K := A1h) (fun a ha b hb => A1h_comm ha hb) fun a ha => A1h_sq ha)
  refine claimT_core c (isSylowTwoOf_T₀_M₁ c hT₀G) hab.1 hab.2
    (by rw [c.iso.card_imgG (A1h_le_That.trans That_le_Bh), card_A1h]) ?_
  intro γ hγ
  rcases conj_A1_cases c hZ hγ with h | h
  · exact ⟨1, Subgroup.one_mem _, by rw [h, B6.conjSub_one]⟩
  · exfalso
    refine not_conj_of_sylow hT₀G (imgG_le_normalizer c.iso That_le_normalizer_A1h)
      (imgG_le_normalizer c.iso That_le_normalizer_VA) (imgG_A1h_ne_VA c.iso) ?_ h
    intro s hs
    refine conj_A1_cases c hZ ?_
    have h1 := (B6.conjSub s).monotone (imgG_mono' c.iso A1h_le_That)
    rwa [B6.conjSub_eq_self hs] at h1

theorem claimT_A2 : ∀ u ∈ c.iso.imgG A2h, IsConj u z →
    ∃ n ∈ Subgroup.normalizer (c.iso.imgG A2h : Set G), n * z * n⁻¹ = u := by
  have hab := (imgG_E16 c.iso (K := A2h) (fun a ha b hb => A2h_comm ha hb) fun a ha => A2h_sq ha)
  refine claimT_core c (isSylowTwoOf_T₀_M₁ c hT₀G) hab.1 hab.2
    (by rw [c.iso.card_imgG (A2h_le_That.trans That_le_Bh), card_A2h]) ?_
  intro γ hγ
  rcases conj_A2_cases c hZ hγ with h | h
  · exact ⟨1, Subgroup.one_mem _, by rw [h, B6.conjSub_one]⟩
  · exact ⟨c.iso.toG yB, (c.iso.toG_mem yB).1, h⟩

end Instances

end CFSG.Quasithin.H13.F431.U42Aut
