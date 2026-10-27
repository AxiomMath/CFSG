module

public import CFSG.Quasithin.MS93.S32G2Alg
public import CFSG.Quasithin.Background.FFC4Real
public import CFSG.Quasithin.Background.SmithB42G2Nat
public import CFSG.Quasithin.Background.SmithB51Sp4Sec
public import CFSG.Quasithin.MS93.M15WeylQ

public section

namespace CFSG.Quasithin.MS93.S32

open CFSG.Quasithin CFSG.Open CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit
  CFSG.Quasithin.Vol2.Ch11.G2Q8 CFSG.Quasithin.B42G2
open CFSG.ClassicalInvolution.ModelFacts.OddCover (uSL)

variable {V : Type} [CommGroup V] [Finite V]

section Coord

variable {F : Type} [Field F] [CharP F 2]

omit [Finite V] in
private theorem exists_g2Coord {H : Subgroup (MulAut V)} {Z : Subgroup V}
    {π : ↥(quasithinG2 F) →* ↥H} (hπ : (FFModel.zornQ (quasithinG2 F)).RealizesVia H ⊤ Z π) :
    ∃ (f : V →* Multiplicative (Ix3 → F)) (ψ : ↥(cayleyGroup F) ≃* ↥H),
      Function.Surjective f ∧ f.ker = Z ∧
      ∀ (g : ↥(cayleyGroup F)) (v : V),
        Multiplicative.toAdd (f ((ψ g : MulAut V) v)) = g2Act g (Multiplicative.toAdd (f v)) := by
  have hq2 : quasithinG2 F = cayleyGroup F := G11.P3G2.quasithinG2_eq_cayleyGroup
  obtain ⟨f, hf⟩ :=
    Vol2.KGNat.exists_isCoord (Vol2.KGNat.linModelZorn (quasithinG2 F) hq2.le) hπ
  have hinj : Function.Injective π :=
    FFC.injective_of_faithful_sec (FFC.zornQ_faithful _ le_rfl) hπ
  refine ⟨hf.toHom, (MulEquiv.subgroupCongr hq2).symm.trans
    (MulEquiv.ofBijective π ⟨hinj, hπ.1⟩), fun m => ?_, ?_, fun g v => hf.act _ v⟩
  · obtain ⟨v, hv⟩ := hf.surj (Multiplicative.toAdd m)
    exact ⟨v, congrArg Multiplicative.ofAdd hv⟩
  · ext v
    rw [MonoidHom.mem_ker, ← hf.ker v]
    exact ⟨fun h => congrArg Multiplicative.toAdd h, fun h => congrArg Multiplicative.ofAdd h⟩

omit [Finite V] [CharP F 2] in
private theorem preimage_facts {H : Subgroup (MulAut V)} (ψ : ↥(cayleyGroup F) ≃* ↥H)
    {A : Subgroup (MulAut V)} (hAH : A ≤ H) (hA : IsElemAbelian2 A)
    {Γ : Subgroup ↥(cayleyGroup F)} (hΓ : ∀ γ, γ ∈ Γ ↔ ((ψ γ : ↥H) : MulAut V) ∈ A) :
    (∀ γ ∈ Γ, γ * γ = 1) ∧ (∀ γ ∈ Γ, ∀ δ ∈ Γ, γ * δ = δ * γ) ∧ Nat.card Γ = Nat.card A := by
  refine ⟨fun γ hγ => ψ.injective (Subtype.ext ?_), fun γ hγ δ hδ => ψ.injective
    (Subtype.ext ?_), Nat.card_congr (Equiv.ofBijective
      (fun γ : Γ => (⟨ψ γ.1, (hΓ γ.1).1 γ.2⟩ : A)) ⟨?_, ?_⟩)⟩
  · rw [map_mul, map_one, Subgroup.coe_mul, Subgroup.coe_one, ← sq]
    exact hA.2 _ ((hΓ γ).1 hγ)
  · rw [map_mul, map_mul, Subgroup.coe_mul, Subgroup.coe_mul]
    exact hA.1 _ ((hΓ γ).1 hγ) _ ((hΓ δ).1 hδ)
  · rintro ⟨γ, hγ⟩ ⟨δ, hδ⟩ h
    exact Subtype.ext (ψ.injective (Subtype.ext (congrArg (fun a : A => (a : MulAut V)) h)))
  · rintro ⟨a, ha⟩
    refine ⟨⟨ψ.symm ⟨a, hAH ha⟩, (hΓ _).2 (by rw [MulEquiv.apply_symm_apply]; exact ha)⟩, ?_⟩
    apply Subtype.ext
    show ((ψ (ψ.symm ⟨a, hAH ha⟩) : ↥H) : MulAut V) = a
    rw [MulEquiv.apply_symm_apply]

omit [CharP F 2] in
private theorem card_eq_of_coord [Finite F] {Z : Subgroup V} {f : V →* Multiplicative (Ix3 → F)}
    (hfs : Function.Surjective f) (hfk : f.ker = Z) :
    Nat.card V = Nat.card F ^ 6 * Nat.card Z := by
  have h := card_comap_eq_mul hfs ⊤
  rw [Subgroup.comap_top, Subgroup.card_top, Subgroup.card_top, hfk] at h
  rw [h, ← card_Q]
  rfl

private theorem card_comap_fixSubM {Z : Subgroup V} {f : V →* Multiplicative (Ix3 → F)}
    (hfs : Function.Surjective f) (hfk : f.ker = Z) (Γ : Subgroup ↥(cayleyGroup F)) :
    Nat.card ((fixSubM Γ).comap f) = Nat.card (fixSub Γ) * Nat.card Z := by
  rw [card_comap_eq_mul hfs, hfk]
  rfl

end Coord

theorem card_mul_card_fixV_le_g2_two {X : Subgroup (MulAut V)} {Z : Subgroup V}
    (hG : G2Natural X ⊤ Z 1) {A : Subgroup (MulAut V)} (hAX : A ≤ X) (hA : IsElemAbelian2 A) :
    Nat.card A * Nat.card (fixV A) ≤ Nat.card V := by
  obtain ⟨F, _, _, hF, π, hπ⟩ := hG
  have : Fintype F := Fintype.ofFinite F
  have hFc : Fintype.card F = 2 ^ 1 := by rw [← Nat.card_eq_fintype_card, hF]
  have : CharP F 2 := charP_of_card_eq_prime_pow hFc
  obtain ⟨f, ψ, hfs, hfk, hfa⟩ := exists_g2Coord hπ
  obtain ⟨Γ, hΓ⟩ : ∃ Γ : Subgroup ↥(cayleyGroup F),
      ∀ γ, γ ∈ Γ ↔ ((ψ γ : ↥X) : MulAut V) ∈ A :=
    ⟨(A.subgroupOf X).comap ψ.toMonoidHom, fun γ => Iff.rfl⟩
  obtain ⟨hΓ1, hΓc, hcΓ⟩ := preimage_facts ψ hAX hA hΓ
  have hfix : fixV A ≤ (fixSubM Γ).comap f := by
    intro v hv
    rw [Subgroup.mem_comap]
    show ∀ γ ∈ Γ, g2Act γ (Multiplicative.toAdd (f v)) = Multiplicative.toAdd (f v)
    intro γ hγ
    rw [← hfa, (mem_fixV.1 hv) _ ((hΓ γ).1 hγ)]
  obtain ⟨h6, -⟩ := card_mul_card_fixSub hF le_rfl hΓ1 hΓc
  calc Nat.card A * Nat.card (fixV A)
      ≤ Nat.card Γ * (Nat.card (fixSub Γ) * Nat.card Z) := by
        rw [hcΓ]
        exact Nat.mul_le_mul_left _
          ((Subgroup.card_le_of_le hfix).trans (card_comap_fixSubM hfs hfk Γ).le)
    _ = Nat.card Γ * Nat.card (fixSub Γ) * Nat.card Z := by ring
    _ ≤ Nat.card F ^ 6 * Nat.card Z := Nat.mul_le_mul_right _ h6
    _ = Nat.card V := (card_eq_of_coord hfs hfk).symm

theorem card_mul_card_fixV_le_g2 {X K : Subgroup (MulAut V)} {Z : Subgroup V} {n : ℕ}
    (hn : 2 ≤ n) (hG : G2Natural K ⊤ Z n) (hKX : K ≤ X)
    (hXN : X ≤ Subgroup.normalizer (K : Set (MulAut V)))
    (hXZ : ∀ x ∈ X, ∀ z ∈ Z, x z ∈ Z)
    (hfaith : ∀ x ∈ X, (∀ v : V, x v * v⁻¹ ∈ Z) → x = 1)
    {A : Subgroup (MulAut V)} (hAX : A ≤ X) (hA : IsElemAbelian2 A) :
    Nat.card A * Nat.card (fixV A) ≤ Nat.card V ∧
      (A ≠ ⊥ → Nat.card V ≤ Nat.card A * Nat.card ↥(fixQuot A Z) → A ≤ K) := by
  obtain ⟨F, _, _, hF, π, hπ⟩ := hG
  have : Fintype F := Fintype.ofFinite F
  have hFc : Fintype.card F = 2 ^ n := by rw [← Nat.card_eq_fintype_card, hF]
  have : CharP F 2 := charP_of_card_eq_prime_pow hFc
  have hXW : X ≤ stabSub (⊤ : Subgroup V) := fun _ _ _ => Iff.rfl
  have hXS : X ≤ stabSub Z := by
    intro x hx u
    refine ⟨fun hu => ?_, hXZ x hx u⟩
    have h1 := hXZ _ (X.inv_mem hx) _ hu
    rwa [MulAut.inv_apply_self] at h1
  have hfX : X ⊓ centSec ⊤ Z = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hx, hc⟩
    exact Subgroup.mem_bot.2 (hfaith x hx fun v => (mem_centSec.1 hc).2 v (Subgroup.mem_top v))
  have hfL : ∀ {L : Subgroup (MulAut V)}, L ≤ X → L ⊓ centSec ⊤ Z = ⊥ := fun hLX =>
    le_bot_iff.1 ((inf_le_inf_right _ hLX).trans hfX.le)
  have hσi : Function.Injective (B5.secHom X hXW hXS) :=
    (MonoidHom.ker_eq_bot_iff _).1 (B5.ker_secHom_eq_bot X hXW hXS hfX)
  have hmem : ∀ {L : Subgroup (MulAut V)}, L ≤ X → ∀ {y : MulAut (Sec ⊤ Z)},
      y ∈ autSec L ⊤ Z ↔ ∃ x : ↥X, (x : MulAut V) ∈ L ∧ B5.secHom X hXW hXS x = y := by
    intro L hLX y
    rw [← B5.map_secHom_eq_autSec X hXW hXS hLX, Subgroup.mem_map]
    exact ⟨fun ⟨x, hx, hxy⟩ => ⟨x, hx, hxy⟩, fun ⟨x, hx, hxy⟩ => ⟨x, hx, hxy⟩⟩
  obtain ⟨c₀, hc0, hc1⟩ := exists_ne_zero_ne_one_of_card hn hF
  have heq : ⁅quasithinG2 F, quasithinG2 F⁆ = quasithinG2 F :=
    (g2Derived_eq hc0 hc1).trans G11.P3G2.quasithinG2_eq_cayleyGroup.symm
  have hR : (FFModel.zornQ ⁅quasithinG2 F, quasithinG2 F⁆).Realizes (autSec K ⊤ Z) ⊤ ⊥ := by
    rw [heq]
    exact ⟨_, FFC.Sp4Off.realizesVia_autSec (hKX.trans hXW) (hKX.trans hXS) (hfL hKX) hπ⟩
  obtain ⟨π', hπ'⟩ := hR
  obtain ⟨fc, hfc⟩ := Vol2.KGNat.exists_isCoord (lmG F) hπ'
  have hĀN : autSec A ⊤ Z ≤ Subgroup.normalizer (autSec K ⊤ Z : Set (MulAut (Sec ⊤ Z))) := by
    refine le_normalizer_of_conj' fun g hg k hk => ?_
    obtain ⟨x, -, rfl⟩ := (hmem hAX).1 hg
    obtain ⟨y, hy, rfl⟩ := (hmem hKX).1 hk
    refine (hmem hKX).2 ⟨x * y * x⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
    exact (Subgroup.mem_normalizer_iff.mp (hXN x.2) y).mp hy
  have hĀe : IsElemAbelian2 (autSec A ⊤ Z) := by
    refine ⟨fun a ha b hb => ?_, fun a ha => ?_⟩
    · obtain ⟨x, hx, rfl⟩ := (hmem hAX).1 ha
      obtain ⟨y, hy, rfl⟩ := (hmem hAX).1 hb
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hA.1 _ hx _ hy)
    · obtain ⟨x, hx, rfl⟩ := (hmem hAX).1 ha
      rw [← map_pow]
      have : x ^ 2 = 1 := Subtype.ext (by simpa using hA.2 _ hx)
      rw [this, map_one]
  have hcA : Nat.card (autSec A ⊤ Z) = Nat.card A := by
    have h1 := card_autSec_mul (hAX.trans hXW) (hAX.trans hXS)
    rwa [hfL hAX, Subgroup.card_bot, mul_one] at h1
  have hfix : Nat.card (fixV (autSec A ⊤ Z)) * Nat.card Z = Nat.card (fixQuot A Z) := by
    have e : B5.fixSec A ⊤ Z = fixQuot A Z := by
      ext v
      exact ⟨fun hv => hv.2, fun hv => ⟨Subgroup.mem_top v, hv⟩⟩
    rw [B5.card_fixV_autSec_mul le_top (hAX.trans hXW) (hAX.trans hXS), e]
  have hsec : Nat.card V = Nat.card (Sec (⊤ : Subgroup V) Z) * Nat.card Z := by
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_top : Z ≤ ⊤)).toEquiv,
      ← Subgroup.card_eq_card_quotient_mul_card_subgroup, Subgroup.card_top]
  obtain ⟨h1, h2⟩ := offender_facts hF hn hfc hĀN hĀe
  have hZpos : 0 < Nat.card Z := Nat.card_pos
  refine ⟨?_, fun hA1 hcard => ?_⟩
  · have hle : fixV A ≤ fixQuot A Z := fun v hv a ha => by
      rw [hv a ha, mul_inv_cancel]
      exact Z.one_mem
    calc Nat.card A * Nat.card (fixV A) ≤ Nat.card A * Nat.card (fixQuot A Z) :=
          Nat.mul_le_mul_left _ (Subgroup.card_le_of_le hle)
      _ = Nat.card (autSec A ⊤ Z) * Nat.card (fixV (autSec A ⊤ Z)) * Nat.card Z := by
          rw [← hfix, hcA, mul_assoc]
      _ ≤ Nat.card (Sec (⊤ : Subgroup V) Z) * Nat.card Z := Nat.mul_le_mul_right _ h1
      _ = Nat.card V := hsec.symm
  · have hĀ1 : autSec A ⊤ Z ≠ ⊥ := by
      intro hbot
      apply hA1
      have h3 : Nat.card A = 1 := by rw [← hcA, hbot, Subgroup.card_bot]
      exact Subgroup.eq_bot_of_card_eq A h3
    have hĀcard : Nat.card (Sec (⊤ : Subgroup V) Z) ≤
        Nat.card (autSec A ⊤ Z) * Nat.card (fixV (autSec A ⊤ Z)) := by
      refine Nat.le_of_mul_le_mul_right ?_ hZpos
      rw [mul_assoc, hfix, ← hsec, hcA]
      exact hcard
    obtain ⟨hĀK, -, -⟩ := h2 hĀ1 hĀcard
    intro a ha
    obtain ⟨k, hk, hka⟩ := (hmem hKX).1 (hĀK ((hmem hAX).2 ⟨⟨a, hAX ha⟩, ha, rfl⟩))
    rw [hσi hka] at hk
    exact hk

section Crd

variable {F : Type} [Field F]

private def crdX : (Ix3 → F) →+ (Fin 3 → F) where
  toFun w := ![w (.inr 0), w (.inl 1), w (.inl 2)]
  map_zero' := by
    funext i
    fin_cases i <;> rfl
  map_add' _ _ := by
    funext i
    fin_cases i <;> rfl

private def crdY : (Ix3 → F) →+ (Fin 3 → F) where
  toFun w := ![w (.inl 0), w (.inr 1), w (.inr 2)]
  map_zero' := by
    funext i
    fin_cases i <;> rfl
  map_add' _ _ := by
    funext i
    fin_cases i <;> rfl

private theorem eq_zero_of_crd {w : Ix3 → F} (hX : crdX w = 0) (hY : crdY w = 0) : w = 0 := by
  have e0 := congrFun hX 0
  have e1 := congrFun hX 1
  have e2 := congrFun hX 2
  have f0 := congrFun hY 0
  have f1 := congrFun hY 1
  have f2 := congrFun hY 2
  funext j
  rcases j with j | j <;> fin_cases j
  · exact f0
  · exact e1
  · exact e2
  · exact e0
  · exact f1
  · exact f2

variable [CharP F 2]

private theorem crd_conj_A1_sub {x γ : ↥(cayleyGroup F)} {α p q' : F}
    (h : x⁻¹ * γ * x = g2X ![α, 0, 0] * g2Y ![0, 0, 0] * g2A (uSL p q' 0)) (w : Ix3 → F) :
    crdX (g2Act x⁻¹ (g2Act γ w - w)) = 0 ∧
      crdY (g2Act x⁻¹ (g2Act γ w - w)) = a1Pair (crdX (g2Act x⁻¹ w)) ![α, p, q'] := by
  have e1 : g2Act x⁻¹ (g2Act γ w) = g2Act (x⁻¹ * γ * x) (g2Act x⁻¹ w) := by
    rw [g2Act_mul_apply, g2Act_mul_apply, g2Act_apply_inv]
  rw [map_sub, e1, h]
  generalize g2Act x⁻¹ w = y
  have e2 : g2Act (g2X ![α, 0, 0] * g2Y ![0, 0, 0] * g2A (uSL p q' 0)) y - y =
      q6 (p * y (.inl 1) + q' * y (.inl 2) + α * α * y (.inr 0)) 0 0 0
        (p * y (.inr 0) + α * y (.inl 2)) (q' * y (.inr 0) + α * y (.inl 1)) := by
    conv_lhs => rw [q6_eta y]
    rw [g2Act_A1, q6_sub]
    refine q6_congr ?_ ?_ ?_ ?_ ?_ ?_ <;> ring
  rw [e2]
  constructor
  · funext i
    fin_cases i <;> rfl
  · funext i
    fin_cases i <;> rfl

private theorem a1E_inj {α p q' α' p' q'' : F}
    (h : g2X ![α, 0, 0] * g2Y ![0, 0, 0] * g2A (uSL p q' 0) =
      g2X ![α', 0, 0] * g2Y ![0, 0, 0] * g2A (uSL p' q'' 0)) :
    α = α' ∧ p = p' ∧ q' = q'' := by
  have h1 := congrArg (fun g => g2Act g (q6 (0 : F) 0 0 1 0 0)) h
  simp only [g2Act_A1] at h1
  obtain ⟨e0, -, -, -, e4, e5⟩ := q6_inj h1
  exact ⟨eq_of_mul_self_eq_charTwo (by linear_combination e0), by linear_combination e4,
    by linear_combination e5⟩

end Crd

theorem exists_a1Coords {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 1 ≤ n) {K : Subgroup (MulAut V)} {Z : Subgroup V}
    {π : ↥(quasithinG2 F) →* ↥K}
    (hπ : (FFModel.zornQ (quasithinG2 F)).RealizesVia K ⊤ Z π)
    {A : Subgroup (MulAut V)} (hAK : A ≤ K) (hA1 : A ≠ ⊥) (hA : IsElemAbelian2 A)
    (hoff : Nat.card V ≤ Nat.card A * Nat.card ↥(fixQuot A Z)) :
    ∃ (ξ θ : V →* Multiplicative (Fin 3 → F)) (η : ↥A → (Fin 3 → F)),
      Function.Surjective ξ ∧ Function.Bijective η ∧
      (∀ (a : ↥A) (v : V), Multiplicative.toAdd (θ ((a : MulAut V) v * v⁻¹)) =
        a1Pair (Multiplicative.toAdd (ξ v)) (η a)) ∧
      (∀ z ∈ Z, θ z = 1) ∧ (∀ w ∈ commV A, θ w = 1 → w ∈ Z) := by
  obtain ⟨f, ψ, hfs, hfk, hfa⟩ := exists_g2Coord hπ
  obtain ⟨Γ, hΓ⟩ : ∃ Γ : Subgroup ↥(cayleyGroup F),
      ∀ γ, γ ∈ Γ ↔ ((ψ γ : ↥K) : MulAut V) ∈ A :=
    ⟨(A.subgroupOf K).comap ψ.toMonoidHom, fun γ => Iff.rfl⟩
  obtain ⟨hΓ1, hΓc, hcΓ⟩ := preimage_facts ψ hAK hA hΓ
  have hfa' : ∀ (a : ↥A) (v : V), Multiplicative.toAdd (f ((a : MulAut V) v)) =
      g2Act (ψ.symm ⟨a, hAK a.2⟩) (Multiplicative.toAdd (f v)) := by
    intro a v
    rw [← hfa, MulEquiv.apply_symm_apply]
  have hmemΓ : ∀ a : ↥A, ψ.symm ⟨a, hAK a.2⟩ ∈ Γ := fun a =>
    (hΓ _).2 (by rw [MulEquiv.apply_symm_apply]; exact a.2)
  have hfixQ : fixQuot A Z = (fixSubM Γ).comap f := by
    ext v
    rw [mem_fixQuot, Subgroup.mem_comap]
    show _ ↔ ∀ γ ∈ Γ, g2Act γ (Multiplicative.toAdd (f v)) = Multiplicative.toAdd (f v)
    constructor
    · intro h γ hγ
      have h1 := h _ ((hΓ γ).1 hγ)
      rw [← hfk, MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one] at h1
      rw [← hfa, h1]
    · intro h a ha
      rw [← hfk, MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one]
      have h1 := hfa' ⟨a, ha⟩ v
      rw [h _ (hmemΓ ⟨a, ha⟩)] at h1
      exact congrArg Multiplicative.ofAdd h1
  have hΓne : Γ ≠ ⊥ := by
    intro h
    apply hA1
    have h1 : Nat.card A = 1 := by rw [← hcΓ, h, Subgroup.card_bot]
    exact Subgroup.eq_bot_of_card_eq A h1
  have hoff' : Nat.card F ^ 6 ≤ Nat.card Γ * Nat.card (fixSub Γ) := by
    have hpos : 0 < Nat.card Z := Nat.card_pos
    rw [card_eq_of_coord hfs hfk, hfixQ, card_comap_fixSubM hfs hfk Γ, ← hcΓ,
      ← mul_assoc] at hoff
    exact Nat.le_of_mul_le_mul_right hoff hpos
  obtain ⟨x, hx⟩ := eq_conj_A1_of_offender hF hn hΓ1 hΓc hΓne hoff'
  have hmemA1 : ∀ a : ↥A, x⁻¹ * ψ.symm ⟨a, hAK a.2⟩ * x ∈ A1 F := by
    intro a
    have h1 := hmemΓ a
    rw [hx] at h1
    obtain ⟨s, hs, hs'⟩ := h1
    rw [← hs']
    show x⁻¹ * (x * s * x⁻¹) * x ∈ A1 F
    rwa [show x⁻¹ * (x * s * x⁻¹) * x = s by group]
  choose α p q' hapq using fun a : ↥A => exists_eq_of_mem_A1 (hmemA1 a)
  have hpar : ∀ (a : ↥A) (γ : ↥(cayleyGroup F)), ((ψ γ : ↥K) : MulAut V) = a →
      x⁻¹ * γ * x = g2X ![α a, 0, 0] * g2Y ![0, 0, 0] * g2A (uSL (p a) (q' a) 0) := by
    intro a γ hγ
    have e : γ = ψ.symm ⟨a, hAK a.2⟩ := by
      rw [← ψ.symm_apply_apply γ]
      exact congrArg ψ.symm (Subtype.ext hγ)
    rw [e]
    exact hapq a
  have hcomm : ∀ (a : ↥A) (v : V),
      crdX (g2Act x⁻¹ (Multiplicative.toAdd (f ((a : MulAut V) v * v⁻¹)))) = 0 ∧
        crdY (g2Act x⁻¹ (Multiplicative.toAdd (f ((a : MulAut V) v * v⁻¹)))) =
          a1Pair (crdX (g2Act x⁻¹ (Multiplicative.toAdd (f v)))) ![α a, p a, q' a] := by
    intro a v
    rw [map_mul f, map_inv f, toAdd_mul, toAdd_inv, ← sub_eq_add_neg, hfa']
    exact crd_conj_A1_sub (hapq a) _
  refine ⟨(AddMonoidHom.toMultiplicative (crdX.comp (g2Act x⁻¹))).comp f,
    (AddMonoidHom.toMultiplicative (crdY.comp (g2Act x⁻¹))).comp f,
    fun a => ![α a, p a, q' a], ?_, ⟨?_, ?_⟩, fun a v => (hcomm a v).2, ?_, ?_⟩
  ·
    intro t
    obtain ⟨v, hv⟩ := hfs (Multiplicative.ofAdd (g2Act x (q6 0 (Multiplicative.toAdd t 1)
      (Multiplicative.toAdd t 2) (Multiplicative.toAdd t 0) 0 0)))
    refine ⟨v, Multiplicative.toAdd.injective ?_⟩
    show crdX (g2Act x⁻¹ (Multiplicative.toAdd (f v))) = Multiplicative.toAdd t
    rw [hv, toAdd_ofAdd, g2Act_inv_apply]
    funext i
    fin_cases i <;> rfl
  ·
    intro a b hab
    have hα : α a = α b := congrFun hab 0
    have hp : p a = p b := congrFun hab 1
    have hq : q' a = q' b := congrFun hab 2
    have h1 : x⁻¹ * ψ.symm ⟨a, hAK a.2⟩ * x = x⁻¹ * ψ.symm ⟨b, hAK b.2⟩ * x := by
      rw [hapq a, hapq b, hα, hp, hq]
    have h2 := ψ.symm.injective (mul_left_cancel (mul_right_cancel h1))
    exact Subtype.ext (congrArg (fun k : ↥K => (k : MulAut V)) h2)
  ·
    intro t
    have hγ : x * (g2X ![t 0, 0, 0] * g2Y ![0, 0, 0] * g2A (uSL (t 1) (t 2) 0)) * x⁻¹ ∈ Γ := by
      rw [hx]
      exact ⟨_, kerElt_mem_A1 (t 0) (t 1) (t 2), rfl⟩
    refine ⟨⟨_, (hΓ _).1 hγ⟩, ?_⟩
    have e := hpar ⟨_, (hΓ _).1 hγ⟩ _ rfl
    rw [show ∀ s : ↥(cayleyGroup F), x⁻¹ * (x * s * x⁻¹) * x = s from fun s => by group] at e
    obtain ⟨e0, e1, e2⟩ := a1E_inj e
    funext i
    fin_cases i
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
  ·
    intro z hz
    have h1 : f z = 1 := by
      rw [← MonoidHom.mem_ker, hfk]
      exact hz
    show Multiplicative.ofAdd (crdY (g2Act x⁻¹ (Multiplicative.toAdd (f z)))) = 1
    rw [h1, toAdd_one, map_zero, map_zero, ofAdd_zero]
  ·
    intro w hw hθw
    have hle : commV A ≤ ((AddMonoidHom.toMultiplicative (crdX.comp (g2Act x⁻¹))).comp f).ker := by
      rw [commV, Subgroup.closure_le]
      rintro _ ⟨a, ha, v, rfl⟩
      show Multiplicative.ofAdd (crdX (g2Act x⁻¹ (Multiplicative.toAdd (f (a v * v⁻¹))))) = 1
      rw [(hcomm ⟨a, ha⟩ v).1, ofAdd_zero]
    have hX : crdX (g2Act x⁻¹ (Multiplicative.toAdd (f w))) = 0 :=
      congrArg Multiplicative.toAdd (hle hw)
    have hY : crdY (g2Act x⁻¹ (Multiplicative.toAdd (f w))) = 0 :=
      congrArg Multiplicative.toAdd hθw
    have h0 := eq_zero_of_crd hX hY
    have h1 : Multiplicative.toAdd (f w) = 0 := by
      rw [← g2Act_apply_inv x (Multiplicative.toAdd (f w)), h0, map_zero]
    rw [← hfk, MonoidHom.mem_ker]
    exact congrArg Multiplicative.ofAdd h1

end CFSG.Quasithin.MS93.S32
