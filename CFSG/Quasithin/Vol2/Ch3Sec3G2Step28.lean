module

public import CFSG.Quasithin.Vol2.Ch3Sec3G2Three
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3328G2

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.Quasithin.H13.Ch3Sec3 CFSG.Quasithin.H13.Lem3328
open CFSG.QuasithinUnique.Vol2Native (A38ForSQTKCat A39ForSQTKCat)
open scoped commutatorElement

namespace G2Step28

open CFSG.Quasithin.H13.Orbit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit
open CFSG.Quasithin.H13.G2Three CFSG.Quasithin.H13.G2Dat

variable {G : Type} [Group G]

theorem exists_cocycle_mod {L U : Subgroup G} (σ : ↥L →* ↥subG2) (hσ : Function.Surjective σ)
    {q : G} (hcU : ∀ ℓ : ↥L, (ℓ : G) * q * (ℓ : G)⁻¹ * q⁻¹ ∈ U)
    (κ : ↥U → Ix3 → ZMod 2) (hκ : ∀ u u' : ↥U, κ (u * u') = κ u + κ u')
    (hκe : ∀ (ℓ : ↥L) (u u' : ↥U), (u' : G) = ℓ * u * (ℓ : G)⁻¹ → κ u' = muK (σ ℓ) (κ u))
    (hco : ∀ o : ↥L, σ o = 1 → κ ⟨_, hcU o⟩ = 0) :
    ∃ f ∈ Z1A muK, ∀ ℓ : ↥L, f (σ ℓ) = κ ⟨_, hcU ℓ⟩ := by
  classical
  let lift : ↥subG2 → ↥L := fun γ => (hσ γ).choose
  have hlift : ∀ γ, σ (lift γ) = γ := fun γ => (hσ γ).choose_spec
  have hmul : ∀ ℓ₁ ℓ₂ : ↥L, κ ⟨_, hcU (ℓ₁ * ℓ₂)⟩ = κ ⟨_, hcU ℓ₁⟩ + muK (σ ℓ₁) (κ ⟨_, hcU ℓ₂⟩) := by
    intro ℓ₁ ℓ₂
    have hmem : (ℓ₁ : G) * ((ℓ₂ : G) * q * (ℓ₂ : G)⁻¹ * q⁻¹) * (ℓ₁ : G)⁻¹ ∈ U := by
      have h1 := U.mul_mem (hcU (ℓ₁ * ℓ₂)) (U.inv_mem (hcU ℓ₁))
      have e : ((ℓ₁ * ℓ₂ : ↥L) : G) * q * ((ℓ₁ * ℓ₂ : ↥L) : G)⁻¹ * q⁻¹ *
          ((ℓ₁ : G) * q * (ℓ₁ : G)⁻¹ * q⁻¹)⁻¹ =
          (ℓ₁ : G) * ((ℓ₂ : G) * q * (ℓ₂ : G)⁻¹ * q⁻¹) * (ℓ₁ : G)⁻¹ := by
        push_cast
        group
      rwa [e] at h1
    have e2 : (⟨_, hcU (ℓ₁ * ℓ₂)⟩ : ↥U) = ⟨_, hmem⟩ * ⟨_, hcU ℓ₁⟩ := by
      apply Subtype.ext
      show ((ℓ₁ * ℓ₂ : ↥L) : G) * q * ((ℓ₁ * ℓ₂ : ↥L) : G)⁻¹ * q⁻¹ = _
      push_cast
      exact cq_mul q ℓ₁ ℓ₂
    rw [e2, hκ, hκe ℓ₁ ⟨_, hcU ℓ₂⟩ ⟨_, hmem⟩ rfl, add_comm]
  have hfib : ∀ ℓ ℓ' : ↥L, σ ℓ = σ ℓ' → κ ⟨_, hcU ℓ⟩ = κ ⟨_, hcU ℓ'⟩ := by
    intro ℓ ℓ' hll
    have ho : σ (ℓ⁻¹ * ℓ') = 1 := by rw [map_mul, map_inv, hll, inv_mul_cancel]
    have e : ℓ' = ℓ * (ℓ⁻¹ * ℓ') := by group
    have h1 := hmul ℓ (ℓ⁻¹ * ℓ')
    rw [← e, hco _ ho, map_zero, add_zero] at h1
    exact h1.symm
  refine ⟨fun γ => κ ⟨_, hcU (lift γ)⟩, fun γ δ => ?_, fun ℓ => hfib _ _ (hlift _)⟩
  show κ ⟨_, hcU (lift (γ * δ))⟩ = κ ⟨_, hcU (lift γ)⟩ + muK γ (κ ⟨_, hcU (lift δ)⟩)
  rw [hfib (lift (γ * δ)) (lift γ * lift δ) (by rw [hlift, map_mul, hlift, hlift]), hmul,
    hlift]

theorem commute_of_cob_mod [Finite G] {L U Z : Subgroup G} (σ : ↥L →* ↥subG2)
    (hL2 : ∀ (N : Subgroup ↥L) [N.Normal], IsPGroup 2 (↥L ⧸ N) → N = ⊤)
    {q : G} (hcU : ∀ ℓ : ↥L, (ℓ : G) * q * (ℓ : G)⁻¹ * q⁻¹ ∈ U)
    (κ : ↥U → Ix3 → ZMod 2) (hκ : ∀ u u' : ↥U, κ (u * u') = κ u + κ u')
    (hκ0 : ∀ u : ↥U, κ u = 0 ↔ (u : G) ∈ Z) (hZL : ∀ z ∈ Z, ∀ ℓ ∈ L, ℓ * z = z * ℓ)
    (hZ2 : ∀ z ∈ Z, z ^ 2 = 1) (hZc : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a)
    (hκe : ∀ (ℓ : ↥L) (u u' : ↥U), (u' : G) = ℓ * u * (ℓ : G)⁻¹ → κ u' = muK (σ ℓ) (κ u))
    (hLU : ∀ ℓ : ↥L, ∀ u : ↥U, (ℓ : G) * u * (ℓ : G)⁻¹ ∈ U)
    {m : Ix3 → ZMod 2} (hf : ∀ ℓ : ↥L, κ ⟨_, hcU ℓ⟩ = muK (σ ℓ) m - m) (v : ↥U)
    (hv : κ v = m) (ℓ : ↥L) :
    (ℓ : G) * ((v : G)⁻¹ * q) = (v : G)⁻¹ * q * ℓ := by
  classical
  set q' : G := (v : G)⁻¹ * q with hq'def
  have hκinv : ∀ u : ↥U, κ u⁻¹ = -κ u := fun u => by
    have h0 : κ 1 = 0 := by
      have := hκ 1 1
      rw [mul_one] at this
      exact left_eq_add.mp this
    have := hκ u u⁻¹
    rw [mul_inv_cancel, h0] at this
    exact eq_neg_of_add_eq_zero_right this.symm
  have hc' : ∀ ℓ : ↥L, (ℓ : G) * q' * (ℓ : G)⁻¹ * q'⁻¹ ∈ Z := by
    intro ℓ
    set w : ↥U := ⟨_, hLU ℓ v⟩
    have hw : κ w = muK (σ ℓ) m := by rw [hκe ℓ v w rfl, hv]
    have e : (ℓ : G) * q' * (ℓ : G)⁻¹ * q'⁻¹ = (((w⁻¹ * ⟨_, hcU ℓ⟩ * v : ↥U)) : G) := by
      show (ℓ : G) * ((v : G)⁻¹ * q) * (ℓ : G)⁻¹ * ((v : G)⁻¹ * q)⁻¹ =
        ((ℓ : G) * v * (ℓ : G)⁻¹)⁻¹ * ((ℓ : G) * q * (ℓ : G)⁻¹ * q⁻¹) * v
      group
    rw [e]
    refine (hκ0 _).mp ?_
    rw [hκ, hκ, hκinv, hw, hf, hv]
    abel
  let φ : ↥L →* ↥Z :=
    { toFun := fun ℓ => ⟨_, hc' ℓ⟩
      map_one' := by
        apply Subtype.ext
        show ((1 : ↥L) : G) * q' * ((1 : ↥L) : G)⁻¹ * q'⁻¹ = 1
        simp
      map_mul' := fun ℓ₁ ℓ₂ => by
        apply Subtype.ext
        show ((ℓ₁ * ℓ₂ : ↥L) : G) * q' * ((ℓ₁ * ℓ₂ : ↥L) : G)⁻¹ * q'⁻¹ =
          ((ℓ₁ : G) * q' * (ℓ₁ : G)⁻¹ * q'⁻¹) * ((ℓ₂ : G) * q' * (ℓ₂ : G)⁻¹ * q'⁻¹)
        push_cast
        rw [cq_mul q' ℓ₁ ℓ₂]
        have h1 := hZL _ (hc' ℓ₂) _ ℓ₁.2
        have h2 := hZc _ (hc' ℓ₂) _ (hc' ℓ₁)
        calc (ℓ₁ : G) * ((ℓ₂ : G) * q' * (ℓ₂ : G)⁻¹ * q'⁻¹) * (ℓ₁ : G)⁻¹ *
              ((ℓ₁ : G) * q' * (ℓ₁ : G)⁻¹ * q'⁻¹) =
            ((ℓ₁ : G) * ((ℓ₂ : G) * q' * (ℓ₂ : G)⁻¹ * q'⁻¹)) * (ℓ₁ : G)⁻¹ *
              ((ℓ₁ : G) * q' * (ℓ₁ : G)⁻¹ * q'⁻¹) := by group
          _ = (((ℓ₂ : G) * q' * (ℓ₂ : G)⁻¹ * q'⁻¹) * ℓ₁) * (ℓ₁ : G)⁻¹ *
              ((ℓ₁ : G) * q' * (ℓ₁ : G)⁻¹ * q'⁻¹) := by rw [h1]
          _ = ((ℓ₂ : G) * q' * (ℓ₂ : G)⁻¹ * q'⁻¹) *
              ((ℓ₁ : G) * q' * (ℓ₁ : G)⁻¹ * q'⁻¹) := by group
          _ = _ := h2 }
  have h2 : IsPGroup 2 (↥L ⧸ φ.ker) := by
    have h3 : IsPGroup 2 ↥φ.range := fun x => by
      refine ⟨1, Subtype.ext (Subtype.ext ?_)⟩
      have := hZ2 _ (x : ↥Z).2
      simpa using this
    exact h3.of_equiv (QuotientGroup.quotientKerEquivRange φ).symm
  have hN := hL2 φ.ker h2
  have h4 : φ ℓ = 1 := by
    have : ℓ ∈ φ.ker := by rw [hN]; exact Subgroup.mem_top ℓ
    exact this
  have h5 : (ℓ : G) * q' * (ℓ : G)⁻¹ * q'⁻¹ = 1 := congrArg Subtype.val h4
  calc (ℓ : G) * q' = ((ℓ : G) * q' * (ℓ : G)⁻¹ * q'⁻¹) * q' * ℓ := by group
    _ = q' * ℓ := by rw [h5, one_mul]

@[expose] def e8 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14]

@[expose] def fixQ2 (i j : ℕ) : ℕ :=
  (o0Codes.filter fun c => !c.testBit 0 && (fixQB (sM i) c && fixQB (sM j) c)).length

theorem d1 : ∀ k < 32, (k ≠ 0 ∧ mmul (sM (2 * k)) (sM (2 * k)) = idMat ∧
    ∀ l < 32, mmul bCode (sM (2 * k)) = mmul (sM (2 * l)) bCode →
      mmul (sM (2 * k)) (sM (2 * l)) = mmul (sM (2 * l)) (sM (2 * k))) →
    2 * k ∈ e8 ∧ ∃ l < 32, mmul bCode (sM (2 * k)) = mmul (sM (2 * l)) bCode ∧
      fixQ2 (2 * k) (2 * l) ≤ 8 := by
  decide +kernel

theorem d2 : ∀ k < 32, (∀ j ∈ e8, mmul (sM (2 * k)) (sM j) = mmul (sM j) (sM (2 * k))) →
    2 * k ∈ e8 := by
  decide +kernel

theorem d3 : sE8.getD 2 [] = e8 ∧ 1 ∈ sE8.getD 1 [] ∧ 9 ∈ sE8.getD 6 [] := by
  decide

theorem d4 : (o0Codes.filter fun c => !c.testBit 0 && fixQB (sM 8) c).length = 8 := by
  decide +kernel


section Count

variable {L : Subgroup G}

theorem card_blockU_eq (β : ↥(blockU L) →* ModQ) (hβs : Function.Surjective β)
    (hβk : ∀ u, β u = 1 ↔ (u : G) ∈ blockZ L) :
    Nat.card ↥(blockU L) = 64 * Nat.card ↥(blockZ L) := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup β.ker
  have hk : β.ker = (blockZ L).subgroupOf (blockU L) := by
    ext u
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hβk]
  have hZ : Nat.card ↥((blockZ L).subgroupOf (blockU L)) = Nat.card ↥(blockZ L) :=
    Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (show blockZ L ≤ blockU L from inf_le_left)).toEquiv
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective β hβs).toEquiv, card_ModQ, hk,
    hZ] at h1
  exact h1

theorem card_cU_le [Finite G] (ρ : ↥(Subgroup.normalizer (L : Set G)) →* ↥(quasithinG2 (ZMod 2)))
    (β : ↥(blockU L) →* ModQ) (hβk : ∀ u, β u = 1 ↔ (u : G) ∈ blockZ L)
    (hβe : ∀ (g : ↥(Subgroup.normalizer (L : Set G))) (u u' : ↥(blockU L)),
      (u' : G) = g * u * g⁻¹ → β u' = g2QAct (ZMod 2) (ρ g) (β u))
    {B : Subgroup G} (hBN : B ≤ Subgroup.normalizer (L : Set G)) :
    Nat.card ↥(blockU L ⊓ Subgroup.centralizer (B : Set G)) ≤
      Nat.card ↥(fixV ((ρ.comp (Subgroup.inclusion hBN)).range.map (g2QAct (ZMod 2)))) *
        Nat.card ↥(blockZ L) := by
  have : Finite ModQ := Nat.finite_of_card_ne_zero (by rw [card_ModQ]; norm_num)
  set W := (blockU L ⊓ Subgroup.centralizer (B : Set G)).subgroupOf (blockU L) with hWdef
  have hW : Nat.card ↥W = Nat.card ↥(blockU L ⊓ Subgroup.centralizer (B : Set G)) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  let φ : ↥W →* ModQ := β.comp W.subtype
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv] at h1
  rw [← hW, h1]
  refine Nat.mul_le_mul (Subgroup.card_le_of_le ?_) ?_
  · rintro _ ⟨w, rfl⟩
    rw [mem_fixV]
    rintro _ ⟨_, ⟨b, rfl⟩, rfl⟩
    have hwB : ((w : ↥(blockU L)) : G) ∈ Subgroup.centralizer (B : Set G) :=
      (Subgroup.mem_subgroupOf.mp w.2).2
    have hu : (((w : ↥(blockU L))) : G) = (b : G) * (w : ↥(blockU L)) * (b : G)⁻¹ := by
      rw [Subgroup.mem_centralizer_iff.mp hwB _ b.2]
      group
    exact (hβe ⟨b, hBN b.2⟩ (w : ↥(blockU L)) (w : ↥(blockU L)) hu).symm
  · refine Nat.card_le_card_of_injective (fun k => (⟨((k : ↥W) : ↥(blockU L)),
      (hβk _).mp (MonoidHom.mem_ker.mp k.2)⟩ : ↥(blockZ L))) ?_
    intro k₁ k₂ h12
    have h3 : (((k₁ : ↥W) : ↥(blockU L)) : G) = (((k₂ : ↥W) : ↥(blockU L)) : G) :=
      congrArg (fun x : ↥(blockZ L) => (x : G)) h12
    exact Subtype.ext (Subtype.ext (Subtype.ext h3))

theorem le_relIndex [Finite G]
    (ρ : ↥(Subgroup.normalizer (L : Set G)) →* ↥(quasithinG2 (ZMod 2)))
    (β : ↥(blockU L) →* ModQ) (hβs : Function.Surjective β)
    (hβk : ∀ u, β u = 1 ↔ (u : G) ∈ blockZ L)
    (hβe : ∀ (g : ↥(Subgroup.normalizer (L : Set G))) (u u' : ↥(blockU L)),
      (u' : G) = g * u * g⁻¹ → β u' = g2QAct (ZMod 2) (ρ g) (β u))
    {B Y : Subgroup G} (hBN : B ≤ Subgroup.normalizer (L : Set G)) {n : ℕ}
    (hn : n * Nat.card ↥(fixV ((ρ.comp (Subgroup.inclusion hBN)).range.map (g2QAct (ZMod 2)))) ≤
      64)
    (hYU : Y ⊓ blockU L = blockU L ⊓ Subgroup.centralizer (B : Set G)) :
    n ≤ Y.relIndex (blockU L) := by
  have h1 := Subgroup.relIndex_mul_card Y (blockU L)
  rw [hYU, card_blockU_eq β hβs hβk] at h1
  have h2 := card_cU_le ρ β hβk hβe hBN
  have hC : 0 < Nat.card ↥(blockU L ⊓ Subgroup.centralizer (B : Set G)) := Nat.card_pos
  refine Nat.le_of_mul_le_mul_right ?_ hC
  calc n * Nat.card ↥(blockU L ⊓ Subgroup.centralizer (B : Set G)) ≤
        n * (Nat.card ↥(fixV ((ρ.comp (Subgroup.inclusion hBN)).range.map (g2QAct (ZMod 2)))) *
          Nat.card ↥(blockZ L)) := Nat.mul_le_mul_left _ h2
    _ = n * Nat.card ↥(fixV ((ρ.comp (Subgroup.inclusion hBN)).range.map (g2QAct (ZMod 2)))) *
          Nat.card ↥(blockZ L) := by ring
    _ ≤ 64 * Nat.card ↥(blockZ L) := Nat.mul_le_mul_right _ hn
    _ = _ := h1.symm

theorem card_le_range_mul [Finite G] {Γ : Type*} [Group Γ]
    (ρ : ↥(Subgroup.normalizer (L : Set G)) →* Γ) {B K : Subgroup G}
    (hBN : B ≤ Subgroup.normalizer (L : Set G)) (hK : ∀ b (hb : b ∈ B), ρ ⟨b, hBN hb⟩ = 1 → b ∈ K) :
    Nat.card ↥B ≤ Nat.card ↥(ρ.comp (Subgroup.inclusion hBN)).range * Nat.card ↥(B ⊓ K) := by
  set f := ρ.comp (Subgroup.inclusion hBN) with hf
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv] at h1
  rw [h1]
  refine Nat.mul_le_mul_left _ (Nat.card_le_card_of_injective (fun k => (⟨((k : ↥B) : G),
    (k : ↥B).2, hK _ (k : ↥B).2 (MonoidHom.mem_ker.mp k.2)⟩ : ↥(B ⊓ K))) ?_)
  intro k₁ k₂ h12
  have h3 : ((k₁ : ↥B) : G) = ((k₂ : ↥B) : G) := congrArg (fun x : ↥(B ⊓ K) => (x : G)) h12
  exact Subtype.ext (Subtype.ext h3)

end Count

section Norm

open CFSG.Quasithin.H13.G2XS3

theorem exists_of_mem_r₀ {x : ↥(quasithinG2 (ZMod 2))} (hx : x ∈ r₀) :
    ∃ k < 32, sEltG (2 * k) = x := hx

theorem fix_le_eight {B : Subgroup ↥(quasithinG2 (ZMod 2))} (hBr : B ≤ r₀) (hB1 : B ≠ ⊥)
    (hBc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) (hB2 : ∀ b ∈ B, b ^ 2 = 1)
    (hb₀ : ∀ x ∈ B, b₀ * x * b₀⁻¹ ∈ B) :
    Nat.card ↥(fixV (B.map (g2QAct (ZMod 2)))) ≤ 8 ∧ ∀ i ∈ idx B, i ∈ e8 := by
  classical
  have hBS : B ≤ sSubG := hBr.trans r₀_le
  have key : ∀ k < 32, k ≠ 0 → sEltG (2 * k) ∈ B → 2 * k ∈ e8 ∧
      ∃ l < 32, sEltG (2 * l) ∈ B ∧ fixQ2 (2 * k) (2 * l) ≤ 8 := by
    intro k hk hk0 hkB
    have hk64 : 2 * k < 64 := by omega
    have hsq : mmul (sM (2 * k)) (sM (2 * k)) = idMat := by
      have h1 := congrArg (fun g : ↥(quasithinG2 (ZMod 2)) => matCode g.1) (hB2 _ hkB)
      simp only [pow_two, matCode_mulG, matCode_sEltG hk64] at h1
      rw [h1]
      exact matCode_one
    have hcomm : ∀ l < 32, mmul bCode (sM (2 * k)) = mmul (sM (2 * l)) bCode →
        mmul (sM (2 * k)) (sM (2 * l)) = mmul (sM (2 * l)) (sM (2 * k)) := by
      intro l hl he
      have hl64 : 2 * l < 64 := by omega
      have e1 : b₀ * sEltG (2 * k) = sEltG (2 * l) * b₀ := by
        apply eq_of_code
        rw [matCode_mulG, matCode_mulG, matCode_b₀, matCode_sEltG hk64, matCode_sEltG hl64]
        exact he
      have e2 : sEltG (2 * l) = b₀ * sEltG (2 * k) * b₀⁻¹ := by rw [e1]; group
      have hlB : sEltG (2 * l) ∈ B := e2 ▸ hb₀ _ hkB
      have h3 := hBc _ hkB _ hlB
      have h4 := congrArg (fun g : ↥(quasithinG2 (ZMod 2)) => matCode g.1) h3
      simp only [matCode_mulG, matCode_sEltG hk64, matCode_sEltG hl64] at h4
      exact h4
    obtain ⟨he8, l, hl, he, hfix⟩ := d1 k hk ⟨hk0, hsq, hcomm⟩
    refine ⟨he8, l, hl, ?_, hfix⟩
    have hl64 : 2 * l < 64 := by omega
    have e1 : b₀ * sEltG (2 * k) = sEltG (2 * l) * b₀ := by
      apply eq_of_code
      rw [matCode_mulG, matCode_mulG, matCode_b₀, matCode_sEltG hk64, matCode_sEltG hl64]
      exact he
    have e2 : sEltG (2 * l) = b₀ * sEltG (2 * k) * b₀⁻¹ := by rw [e1]; group
    exact e2 ▸ hb₀ _ hkB
  have hidx : ∀ i ∈ idx B, i = 0 ∨ ∃ k < 32, k ≠ 0 ∧ i = 2 * k ∧ sEltG (2 * k) ∈ B := by
    intro i hi
    obtain ⟨hi64, hiB⟩ := mem_idx.mp hi
    obtain ⟨k, hk, hke⟩ := exists_of_mem_r₀ (hBr hiB)
    have hik : i = 2 * k := (sEltG_injective hi64 (by omega) hke.symm)
    by_cases hk0 : k = 0
    · left
      rw [hik, hk0]
    · right
      exact ⟨k, hk, hk0, hik, hke ▸ hiB⟩
  refine ⟨?_, fun i hi => ?_⟩
  ·
    obtain ⟨i, hi, hi0⟩ : ∃ i ∈ idx B, i ≠ 0 := by
      by_contra hcon
      push Not at hcon
      apply hB1
      rw [eq_bot_iff]
      intro x hx
      obtain ⟨j, hj, rfl⟩ := mem_sSubG.mp (hBS hx)
      have := hcon j (mem_idx.mpr ⟨hj, hx⟩)
      rw [this, Subgroup.mem_bot]
      exact sEltG_zero
    rcases hidx i hi with h0 | ⟨k, hk, hk0, rfl, hkB⟩
    · exact absurd h0 hi0
    obtain ⟨-, l, hl, hlB, hfix⟩ := key k hk hk0 hkB
    let P : ℕ → Bool := fun c => decide (∀ i ∈ idx B, fixQB (sM i) c = true)
    have hP : ∀ c : O0C, P c.1 = true ↔ ∀ i ∈ idx B, fixQB (sM i) c.1 = true := fun c => by
      simp [P]
    rw [card_fixV_Q hBS P hP]
    refine le_trans (length_filter_le fun c hc => ?_) hfix
    simp only [P, Bool.and_eq_true, decide_eq_true_eq] at hc
    rw [Bool.and_eq_true, Bool.and_eq_true]
    exact ⟨hc.1, hc.2 _ hi, hc.2 _ (mem_idx.mpr ⟨by omega, hlB⟩)⟩
  · rcases hidx i hi with h0 | ⟨k, hk, hk0, rfl, hkB⟩
    · rw [h0]
      decide
    · exact (key k hk hk0 hkB).1

theorem mem_e8_of_commute {x : ↥(quasithinG2 (ZMod 2))} (hx : x ∈ r₀)
    (hc : ∀ j ∈ e8, x * sEltG j = sEltG j * x) : ∃ j ∈ e8, sEltG j = x := by
  obtain ⟨k, hk, rfl⟩ := exists_of_mem_r₀ hx
  have hk64 : 2 * k < 64 := by omega
  refine ⟨2 * k, d2 k hk fun j hj => ?_, rfl⟩
  have hj64 : j < 64 := by
    simp only [e8, List.mem_cons, List.not_mem_nil, or_false] at hj
    omega
  have h1 := congrArg (fun g : ↥(quasithinG2 (ZMod 2)) => matCode g.1) (hc j hj)
  simp only [matCode_mulG, matCode_sEltG hk64, matCode_sEltG hj64] at h1
  exact h1

end Norm



section Gen

theorem mem_sup_iff' {A B : Subgroup G} (h : A ≤ Subgroup.normalizer (B : Set G)) {x : G} :
    x ∈ A ⊔ B ↔ ∃ a ∈ A, ∃ b ∈ B, a * b = x := by
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right A B h]
  exact Set.mem_mul

theorem isElemAbelian_of_le_sup {A B H : Subgroup G} (hA : IsElemAbelian 2 A)
    (hB : IsElemAbelian 2 B) (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hH : H ≤ A ⊔ B) :
    IsElemAbelian 2 H := by
  have hN : A ≤ Subgroup.normalizer (B : Set G) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro b
    constructor
    · intro hb
      rw [hAB a ha b hb, mul_inv_cancel_right]
      exact hb
    · intro hb
      have h1 := hAB a⁻¹ (A.inv_mem ha) _ hb
      have e : b = a⁻¹ * (a * b * a⁻¹) * a := by group
      rw [e, h1, mul_assoc, inv_mul_cancel, mul_one]
      exact hb
  have hdec : ∀ x ∈ H, ∃ a ∈ A, ∃ b ∈ B, a * b = x := fun x hx => (mem_sup_iff' hN).mp (hH hx)
  have hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    ThreeL32.comm_of_isElemAbelian hA ha hb
  have hBc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a := fun a ha b hb =>
    ThreeL32.comm_of_isElemAbelian hB ha hb
  refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨a₁, ha₁, b₁, hb₁, e₁⟩ := hdec x x.2
    obtain ⟨a₂, ha₂, b₂, hb₂, e₂⟩ := hdec y y.2
    show (x : G) * y = y * x
    rw [← e₁, ← e₂]
    calc a₁ * b₁ * (a₂ * b₂) = a₁ * (b₁ * a₂) * b₂ := by group
      _ = a₁ * (a₂ * b₁) * b₂ := by rw [hAB a₂ ha₂ b₁ hb₁]
      _ = (a₁ * a₂) * (b₁ * b₂) := by group
      _ = (a₂ * a₁) * (b₂ * b₁) := by rw [hAc _ ha₁ _ ha₂, hBc _ hb₁ _ hb₂]
      _ = a₂ * (a₁ * b₂) * b₁ := by group
      _ = a₂ * (b₂ * a₁) * b₁ := by rw [hAB a₁ ha₁ b₂ hb₂]
      _ = a₂ * b₂ * (a₁ * b₁) := by group
  · obtain ⟨a, ha, b, hb, rfl⟩ := hdec x hx
    calc (a * b) ^ 2 = a * (b * a) * b := by rw [pow_two]; group
      _ = a * (a * b) * b := by rw [hAB a ha b hb]
      _ = a ^ 2 * b ^ 2 := by rw [pow_two, pow_two]; group
      _ = 1 := by rw [hA.2 a ha, hB.2 b hb, one_mul]

variable [Finite G]

theorem le_sup_of_relIndex {X U Q : Subgroup G} (hXQ : X ≤ Q) (hUQ : U ≤ Q)
    (h : X.relIndex Q ≤ X.relIndex U) : Q ≤ U ⊔ X := by
  have h1 := Subgroup.relIndex_mul_relIndex X (U ⊔ X) Q le_sup_right (sup_le hUQ hXQ)
  have h2 : X.relIndex U ≤ X.relIndex (U ⊔ X) :=
    Subgroup.relIndex_le_of_le_right le_sup_left Subgroup.index_ne_zero_of_finite
  have h3 : 0 < X.relIndex (U ⊔ X) := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have h4 : (U ⊔ X).relIndex Q ≠ 0 := Subgroup.index_ne_zero_of_finite
  refine Subgroup.relIndex_eq_one.mp ?_
  by_contra h6
  have h7 : X.relIndex (U ⊔ X) * 2 ≤ X.relIndex (U ⊔ X) * (U ⊔ X).relIndex Q :=
    Nat.mul_le_mul_left _ (by omega)
  omega

theorem le_of_relIndex_le {H K Q : Subgroup G} (hHK : H ≤ K) (hKQ : K ≤ Q)
    (h : H.relIndex Q ≤ K.relIndex Q) : K ≤ H := by
  have h1 := Subgroup.relIndex_mul_relIndex H K Q hHK hKQ
  have h3 : 0 < K.relIndex Q := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have h4 : H.relIndex K ≠ 0 := Subgroup.index_ne_zero_of_finite
  refine Subgroup.relIndex_eq_one.mp ?_
  by_contra h6
  have h7 : 2 * K.relIndex Q ≤ H.relIndex K * K.relIndex Q := Nat.mul_le_mul_right _ (by omega)
  omega

end Gen

section Conj

theorem card_conjugate [Finite G] (H : Subgroup G) (d : G) :
    Nat.card ↥(CFSG.conjugate H d) = Nat.card ↥H :=
  Subgroup.card_map_of_injective (MulAut.conj d⁻¹).injective

theorem conjugate_inf_centralizer (H K : Subgroup G) (d : G) :
    CFSG.conjugate (H ⊓ Subgroup.centralizer (K : Set G)) d =
      CFSG.conjugate H d ⊓ Subgroup.centralizer (CFSG.conjugate K d : Set G) := by
  ext x
  rw [Lem3331S.mem_conjugate_iff, Subgroup.mem_inf, Subgroup.mem_inf, Lem3331S.mem_conjugate_iff,
    Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  refine and_congr Iff.rfl ⟨fun h y hy => ?_, fun h y hy => ?_⟩
  · have hy' : d * y * d⁻¹ ∈ K := Lem3331S.mem_conjugate_iff.mp hy
    have h1 := h _ hy'
    have e : d * (y * x) * d⁻¹ = d * (x * y) * d⁻¹ := by
      calc d * (y * x) * d⁻¹ = (d * y * d⁻¹) * (d * x * d⁻¹) := by group
        _ = (d * x * d⁻¹) * (d * y * d⁻¹) := h1
        _ = d * (x * y) * d⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel e)
  · have hy' : d⁻¹ * y * d ∈ CFSG.conjugate K d := by
      rw [Lem3331S.mem_conjugate_iff]
      simpa [mul_assoc] using hy
    have h1 := h _ hy'
    calc y * (d * x * d⁻¹) = d * ((d⁻¹ * y * d) * x) * d⁻¹ := by group
      _ = d * (x * (d⁻¹ * y * d)) * d⁻¹ := by rw [h1]
      _ = d * x * d⁻¹ * y := by group

theorem conjugate_eq_of_mem_normalizer {H : Subgroup G} {d : G}
    (hd : d ∈ Subgroup.normalizer (H : Set G)) : CFSG.conjugate H d = H := by
  ext x
  rw [Lem3331S.mem_conjugate_iff]
  exact (Subgroup.mem_normalizer_iff.mp hd x).symm

theorem conjugate_conjugate_inv (H : Subgroup G) (d : G) :
    CFSG.conjugate (CFSG.conjugate H d) d⁻¹ = H := by
  ext x
  rw [Lem3331S.mem_conjugate_iff, Lem3331S.mem_conjugate_iff]
  simp [mul_assoc]


theorem conjugate_inv_conjugate (H : Subgroup G) (d : G) :
    CFSG.conjugate (CFSG.conjugate H d⁻¹) d = H := by
  have := conjugate_conjugate_inv H d⁻¹
  rwa [inv_inv] at this

theorem conjugate_le_of_mem_normalizer {H K : Subgroup G} {d : G} (hHK : H ≤ K)
    (hd : d ∈ Subgroup.normalizer (K : Set G)) : CFSG.conjugate H d ≤ K := fun x hx =>
  (Subgroup.mem_normalizer_iff.mp hd x).mpr (hHK (Lem3331S.mem_conjugate_iff.mp hx))

theorem conj_mem_conjugate {V P : Subgroup G} {d y x : G}
    (hPV : P ≤ Subgroup.normalizer (V : Set G)) (hdP : d ∈ Subgroup.normalizer (P : Set G))
    (hy : y ∈ P) (hx : x ∈ CFSG.conjugate V d) : y * x * y⁻¹ ∈ CFSG.conjugate V d := by
  rw [Lem3331S.mem_conjugate_iff] at hx ⊢
  have h1 : d * y * d⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp hdP y).mp hy
  have h2 := (Subgroup.mem_normalizer_iff.mp (hPV h1) _).mp hx
  have e : d * (y * x * y⁻¹) * d⁻¹ = d * y * d⁻¹ * (d * x * d⁻¹) * (d * y * d⁻¹)⁻¹ := by group
  rw [e]
  exact h2

theorem conjugate_comm {V : Subgroup G} (hV : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a) (d : G) :
    ∀ a ∈ CFSG.conjugate V d, ∀ b ∈ CFSG.conjugate V d, a * b = b * a := by
  intro a ha b hb
  have h1 := hV _ (Lem3331S.mem_conjugate_iff.mp ha) _ (Lem3331S.mem_conjugate_iff.mp hb)
  have e : d * (a * b) * d⁻¹ = d * (b * a) * d⁻¹ := by
    calc d * (a * b) * d⁻¹ = d * a * d⁻¹ * (d * b * d⁻¹) := by group
      _ = d * b * d⁻¹ * (d * a * d⁻¹) := h1
      _ = d * (b * a) * d⁻¹ := by group
  exact mul_left_cancel (mul_right_cancel e)

theorem conjugate_sq {V : Subgroup G} (hV : ∀ a ∈ V, a ^ 2 = 1) (d : G) :
    ∀ a ∈ CFSG.conjugate V d, a ^ 2 = 1 := by
  intro a ha
  have h1 := hV _ (Lem3331S.mem_conjugate_iff.mp ha)
  have e : d * a ^ 2 * d⁻¹ = (d * a * d⁻¹) ^ 2 := by rw [pow_two, pow_two]; group
  rw [← e] at h1
  have h2 : a ^ 2 = d⁻¹ * (d * a ^ 2 * d⁻¹) * d := by group
  rw [h2, h1]
  group

theorem relIndex_centralizer_conjugate [Finite G] (V W : Subgroup G) (d : G) :
    (Subgroup.centralizer (CFSG.conjugate W d : Set G)).relIndex (CFSG.conjugate V d) =
      (Subgroup.centralizer (W : Set G)).relIndex V := by
  have h1 := Subgroup.relIndex_mul_card (Subgroup.centralizer (W : Set G)) V
  have h2 := Subgroup.relIndex_mul_card (Subgroup.centralizer (CFSG.conjugate W d : Set G))
    (CFSG.conjugate V d)
  have h3 : Nat.card ↥(Subgroup.centralizer (CFSG.conjugate W d : Set G) ⊓ CFSG.conjugate V d) =
      Nat.card ↥(Subgroup.centralizer (W : Set G) ⊓ V) := by
    rw [inf_comm, ← conjugate_inf_centralizer, card_conjugate, inf_comm]
  rw [h3, card_conjugate] at h2
  have h4 : 0 < Nat.card ↥(Subgroup.centralizer (W : Set G) ⊓ V) := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_right h4 (h2.trans h1.symm)

end Conj


section Step

open CFSG.Quasithin.H13.G2XS3 CFSG.Quasithin.H13.Par32

local notation "Amb" => quasithinZorn (ZMod 2) ≃ₗ[ZMod 2] quasithinZorn (ZMod 2)

variable {L : Subgroup G}

theorem inf_centralizer_inf {Q U : Subgroup G} (hUQ : U ≤ Q) (S : Set G) :
    Q ⊓ Subgroup.centralizer S ⊓ U = U ⊓ Subgroup.centralizer S := by
  ext x
  constructor
  · rintro ⟨⟨-, hc⟩, hu⟩
    exact ⟨hu, hc⟩
  · rintro ⟨hu, hc⟩
    exact ⟨⟨hUQ hu, hc⟩, hu⟩

theorem range_comm {Γ : Type*} [Group Γ] (ρ : ↥(Subgroup.normalizer (L : Set G)) →* Γ)
    {B : Subgroup G} (hBN : B ≤ Subgroup.normalizer (L : Set G))
    (hBc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) :
    ∀ x ∈ (ρ.comp (Subgroup.inclusion hBN)).range,
      ∀ y ∈ (ρ.comp (Subgroup.inclusion hBN)).range, x * y = y * x := by
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
  rw [← map_mul, ← map_mul]
  exact congrArg _ (Subtype.ext (hBc _ a.2 _ b.2))

theorem range_sq {Γ : Type*} [Group Γ] (ρ : ↥(Subgroup.normalizer (L : Set G)) →* Γ)
    {B : Subgroup G} (hBN : B ≤ Subgroup.normalizer (L : Set G)) (hB2 : ∀ b ∈ B, b ^ 2 = 1) :
    ∀ x ∈ (ρ.comp (Subgroup.inclusion hBN)).range, x ^ 2 = 1 := by
  rintro _ ⟨a, rfl⟩
  have ha : a ^ 2 = 1 := Subtype.ext (by simpa using hB2 _ a.2)
  rw [← map_pow, ha, map_one]

theorem card_le_eight {B : Subgroup ↥(quasithinG2 (ZMod 2))} (hB : B ≤ sSubG)
    (h : ∀ i ∈ idx B, i ∈ e8) : Nat.card ↥B ≤ 8 := by
  classical
  rw [card_eq_idx hB]
  calc (idx B).card ≤ e8.toFinset.card :=
        Finset.card_le_card fun i hi => List.mem_toFinset.mpr (h i hi)
    _ = 8 := by decide

theorem mem_idx_of_card {B : Subgroup ↥(quasithinG2 (ZMod 2))} (hB : B ≤ sSubG)
    (h : ∀ i ∈ idx B, i ∈ e8) (h8 : 8 ≤ Nat.card ↥B) : ∀ j ∈ e8, j ∈ idx B := by
  classical
  intro j hj
  by_contra hjB
  rw [card_eq_idx hB] at h8
  have h1 : idx B ⊆ e8.toFinset.erase j := fun i hi =>
    Finset.mem_erase.mpr ⟨fun e => hjB (e ▸ hi), List.mem_toFinset.mpr (h i hi)⟩
  have h2 := Finset.card_le_card h1
  rw [Finset.card_erase_of_mem (List.mem_toFinset.mpr hj)] at h2
  have h3 : e8.toFinset.card = 8 := by decide
  omega

theorem even_of_mem_idx {B : Subgroup ↥(quasithinG2 (ZMod 2))} (hB : B ≤ r₀) {i : ℕ}
    (hi : i ∈ idx B) : i % 2 = 0 := by
  obtain ⟨hi64, hiB⟩ := mem_idx.mp hi
  obtain ⟨k, hk, hke⟩ := hB hiB
  have := sEltG_injective (by omega) hi64 hke
  omega

theorem card_fixV_le_of_mem {B : Subgroup ↥(quasithinG2 (ZMod 2))} (hBS : B ≤ sSubG) {k : ℕ}
    (hk : k < 64) (hkB : sEltG k ∈ B) :
    Nat.card ↥(fixV (B.map (g2QAct (ZMod 2)))) ≤
      (o0Codes.filter fun c => !c.testBit 0 && fixQB (sM k) c).length := by
  classical
  let P : ℕ → Bool := fun c => decide (∀ i ∈ idx B, fixQB (sM i) c = true)
  have hP : ∀ c : O0C, P c.1 = true ↔ ∀ i ∈ idx B, fixQB (sM i) c.1 = true := fun c => by
    simp [P]
  rw [card_fixV_Q hBS P hP]
  refine length_filter_le fun c hc => ?_
  simp only [P, Bool.and_eq_true, decide_eq_true_eq] at hc
  rw [Bool.and_eq_true]
  exact ⟨hc.1, hc.2 _ (mem_idx.mpr ⟨hk, hkB⟩)⟩

theorem fix_le_eight_of (ρ : ↥(Subgroup.normalizer (L : Set G)) →* ↥(quasithinG2 (ZMod 2)))
    {W : Subgroup G} (hWN : W ≤ Subgroup.normalizer (L : Set G))
    (hWr : ∀ w (hw : w ∈ W), ρ ⟨w, hWN hw⟩ ∈ r₀)
    (hWc : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a) (hW2 : ∀ w ∈ W, w ^ 2 = 1)
    (hW1 : ∃ w, ∃ hw : w ∈ W, ρ ⟨w, hWN hw⟩ ≠ 1)
    {g : ↥(Subgroup.normalizer (L : Set G))} (hg : ρ g = b₀)
    (hgW : ∀ w ∈ W, (g : G) * w * (g : G)⁻¹ ∈ W) :
    Nat.card ↥(fixV ((ρ.comp (Subgroup.inclusion hWN)).range.map (g2QAct (ZMod 2)))) ≤ 8 ∧
      ∀ i ∈ idx (ρ.comp (Subgroup.inclusion hWN)).range, i ∈ e8 := by
  have hBr : (ρ.comp (Subgroup.inclusion hWN)).range ≤ r₀ := by
    rintro _ ⟨w, rfl⟩
    exact hWr w.1 w.2
  refine fix_le_eight hBr ?_ (range_comm ρ hWN hWc) (range_sq ρ hWN hW2) ?_
  · obtain ⟨w, hw, h1⟩ := hW1
    intro hb
    apply h1
    have h2 : (ρ.comp (Subgroup.inclusion hWN)) ⟨w, hw⟩ ∈
        (ρ.comp (Subgroup.inclusion hWN)).range := ⟨⟨w, hw⟩, rfl⟩
    rw [hb, Subgroup.mem_bot] at h2
    exact h2
  · rintro _ ⟨a, rfl⟩
    refine ⟨⟨_, hgW _ a.2⟩, ?_⟩
    have e : (⟨(g : G) * a * (g : G)⁻¹, hWN (hgW _ a.2)⟩ : ↥(Subgroup.normalizer (L : Set G))) =
        g * ⟨a, hWN a.2⟩ * g⁻¹ := rfl
    show ρ ⟨_, hWN (hgW _ a.2)⟩ = b₀ * ρ ⟨a, hWN a.2⟩ * b₀⁻¹
    rw [e, map_mul, map_mul, map_inv, hg]

theorem rho_eq_one_of_mem_centralizer
    (ρ : ↥(Subgroup.normalizer (L : Set G)) →* ↥(quasithinG2 (ZMod 2)))
    (β : ↥(blockU L) →* ModQ) (hβs : Function.Surjective β)
    (hβe : ∀ (g : ↥(Subgroup.normalizer (L : Set G))) (u u' : ↥(blockU L)),
      (u' : G) = g * u * g⁻¹ → β u' = g2QAct (ZMod 2) (ρ g) (β u))
    (g : ↥(Subgroup.normalizer (L : Set G)))
    (hg : (g : G) ∈ Subgroup.centralizer (blockU L : Set G)) : ρ g = 1 := by
  apply g2QAct_injective
  rw [map_one]
  refine MulEquiv.ext fun m => ?_
  obtain ⟨u, rfl⟩ := hβs m
  have hu : (u : G) = g * u * (g : G)⁻¹ := by
    rw [← Subgroup.mem_centralizer_iff.mp hg _ u.2]
    group
  rw [MulAut.one_apply, ← hβe g u u hu]

theorem exists_mul_of_cocycle [Finite G]
    {Q Z A : Subgroup G}
    (ρ : ↥(Subgroup.normalizer (L : Set G)) →* ↥(quasithinG2 (ZMod 2)))
    (β : ↥(blockU L) →* ModQ) (hβs : Function.Surjective β)
    (hβk : ∀ u, β u = 1 ↔ (u : G) ∈ Z)
    (hβe : ∀ (g : ↥(Subgroup.normalizer (L : Set G))) (u u' : ↥(blockU L)),
      (u' : G) = g * u * g⁻¹ → β u' = g2QAct (ZMod 2) (ρ g) (β u))
    (hρL : ∀ ℓ (hℓ : ℓ ∈ L), ρ ⟨ℓ, Subgroup.le_normalizer hℓ⟩ ∈ g2Derived (ZMod 2))
    (hρL' : ∀ x ∈ g2Derived (ZMod 2), ∃ ℓ, ∃ hℓ : ℓ ∈ L, ρ ⟨ℓ, Subgroup.le_normalizer hℓ⟩ = x)
    (hKL : ∀ ℓ (hℓ : ℓ ∈ L), ρ ⟨ℓ, Subgroup.le_normalizer hℓ⟩ = 1 → ℓ ∈ Q)
    (hL2 : ∀ (N : Subgroup ↥L) [N.Normal], IsPGroup 2 (↥L ⧸ N) → N = ⊤)
    (hQLU : ⁅Q, L⁆ ≤ blockU L)
    (hQQ : ∀ a ∈ Q, ∀ b ∈ Q, ∀ ℓ ∈ L, ℓ * (a * b * a⁻¹ * b⁻¹) = a * b * a⁻¹ * b⁻¹ * ℓ)
    (hZ : ∀ x ∈ blockU L, (∀ ℓ ∈ L, ℓ * x = x * ℓ) → x ∈ Z)
    (hZL : ∀ z ∈ Z, ∀ ℓ ∈ L, ℓ * z = z * ℓ) (hZ2 : ∀ z ∈ Z, z ^ 2 = 1)
    (hZc : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a)
    (hAN : A ≤ Subgroup.normalizer (L : Set G)) {q : G} (hqQ : q ∈ Q)
    (hqA : ∀ a ∈ A, a * q = q * a) {a₁ a₂ : G} (ha₁A : a₁ ∈ A) (ha₂A : a₂ ∈ A)
    (ha₁ : ρ ⟨a₁, hAN ha₁A⟩ = sEltG 2) (ha₂ : ρ ⟨a₂, hAN ha₂A⟩ = sEltG 8) :
    ∃ v ∈ blockU L, ∀ ℓ ∈ L, ℓ * (v⁻¹ * q) = v⁻¹ * q * ℓ := by
  have hLU : ∀ ℓ : ↥L, ∀ u : ↥(blockU L), (ℓ : G) * u * (ℓ : G)⁻¹ ∈ blockU L := fun ℓ u =>
    (Subgroup.mem_normalizer_iff.mp (C1.mem_normalizer_blockU (Subgroup.le_normalizer ℓ.2))
      u).mp u.2
  have hσmem : ∀ ℓ : ↥L,
      ((ρ ⟨ℓ, Subgroup.le_normalizer ℓ.2⟩ : ↥(quasithinG2 (ZMod 2))) : Amb) ∈ subG2 := by
    intro ℓ
    rw [subG2_eq]
    exact Subgroup.mem_subgroupOf.mp (hρL ℓ ℓ.2)
  obtain ⟨σ, hσdef⟩ : ∃ σ : ↥L →* ↥subG2, σ = ((quasithinG2 (ZMod 2)).subtype.comp
      (ρ.comp (Subgroup.inclusion Subgroup.le_normalizer))).codRestrict subG2 hσmem := ⟨_, rfl⟩
  have hσv : ∀ ℓ : ↥L, ((σ ℓ : ↥subG2) : Amb) =
      ((ρ ⟨ℓ, Subgroup.le_normalizer ℓ.2⟩ : ↥(quasithinG2 (ZMod 2))) : Amb) := by
    intro ℓ
    rw [hσdef]
    rfl
  have hσs : Function.Surjective σ := by
    intro γ
    have h1 : (γ : Amb) ∈ ⁅quasithinG2 (ZMod 2), quasithinG2 (ZMod 2)⁆ := by
      rw [← subG2_eq]
      exact γ.2
    obtain ⟨ℓ, hℓ, e⟩ :=
      hρL' ⟨γ, Subgroup.commutator_le_self _ h1⟩ (Subgroup.mem_subgroupOf.mpr h1)
    refine ⟨⟨ℓ, hℓ⟩, Subtype.ext ?_⟩
    rw [hσv]
    exact congrArg (fun x : ↥(quasithinG2 (ZMod 2)) => (x : Amb)) e
  have hσQ : ∀ ℓ : ↥L, σ ℓ = 1 → (ℓ : G) ∈ Q := by
    intro ℓ h1
    have h2 : ρ ⟨ℓ, Subgroup.le_normalizer ℓ.2⟩ = 1 := by
      apply Subtype.ext
      rw [← hσv, h1]
      rfl
    exact hKL _ ℓ.2 h2
  have hκe : ∀ (ℓ : ↥L) (u u' : ↥(blockU L)), (u' : G) = ℓ * u * (ℓ : G)⁻¹ →
      coordQ (β u') = muK (σ ℓ) (coordQ (β u)) := by
    intro ℓ u u' hu'
    rw [hβe ⟨ℓ, Subgroup.le_normalizer ℓ.2⟩ u u' hu', coordQ_act]
    have e : Subgroup.inclusion subG2_le (σ ℓ) =
        ⟨_, le_cayley (ρ ⟨ℓ, Subgroup.le_normalizer ℓ.2⟩).2⟩ := Subtype.ext (hσv ℓ)
    show _ = g2Act (Subgroup.inclusion subG2_le (σ ℓ)) _
    rw [e]
  have hcU : ∀ ℓ : ↥L, (ℓ : G) * q * (ℓ : G)⁻¹ * q⁻¹ ∈ blockU L := by
    intro ℓ
    have h1 : ⁅(ℓ : G), q⁆ ∈ ⁅L, Q⁆ := Subgroup.commutator_mem_commutator ℓ.2 hqQ
    rw [Subgroup.commutator_comm] at h1
    rw [← commutatorElement_def]
    exact hQLU h1
  have hκ : ∀ u u' : ↥(blockU L), coordQ (β (u * u')) = coordQ (β u) + coordQ (β u') :=
    fun u u' => by simp only [map_mul, coordQ_mul]
  have hco : ∀ o : ↥L, σ o = 1 → coordQ (β ⟨_, hcU o⟩) = 0 := by
    intro o ho
    have hz : (o : G) * q * (o : G)⁻¹ * q⁻¹ ∈ Z :=
      hZ _ (hcU o) fun ℓ hℓ => hQQ _ (hσQ o ho) _ hqQ ℓ hℓ
    rw [(hβk _).mpr hz, coordQ_one]
  obtain ⟨f, hfZ, hfσ⟩ := exists_cocycle_mod σ hσs hcU (fun u => coordQ (β u)) hκ hκe hco
  rcases Z1A_K_cases hfZ with ⟨m, hm⟩ | ⟨m, hm⟩
  · obtain ⟨x, hx⟩ := coordQ_surjective m
    obtain ⟨v, rfl⟩ := hβs x
    have hf' : ∀ ℓ : ↥L, coordQ (β ⟨_, hcU ℓ⟩) = muK (σ ℓ) (coordQ (β v)) - coordQ (β v) :=
      fun ℓ => by
        rw [← hfσ ℓ, ← hm, hx]
        rfl
    have hκ0 : ∀ u : ↥(blockU L), coordQ (β u) = 0 ↔ (u : G) ∈ Z := fun u => by
      rw [← hβk]
      constructor
      · intro h1
        exact coordQ_injective (h1.trans coordQ_one.symm)
      · intro h1
        rw [h1, coordQ_one]
    exact ⟨v, v.2, fun ℓ hℓ => commute_of_cob_mod σ hL2 hcU (fun u => coordQ (β u)) hκ hκ0 hZL
      hZ2 hZc hκe hLU hf' v rfl ⟨ℓ, hℓ⟩⟩
  · exfalso
    have e1 := phi_eq_zero ρ β hβe σ hσs hσv hAN hqA hcU hfσ hm ha₁A
    have e2 := phi_eq_zero ρ β hβe σ hσs hσv hAN hqA hcU hfσ hm ha₂A
    have hb : ∀ (a : G) (haA : a ∈ A) (k : ℕ), ρ ⟨a, hAN haA⟩ = sEltG k →
        (⟨_, le_cayley (ρ ⟨a, hAN haA⟩).2⟩ : ↥(cayleyGroup (ZMod 2))) = sC k := by
      intro a haA k hk
      apply Subtype.ext
      show ((ρ ⟨a, hAN haA⟩ : ↥(quasithinG2 (ZMod 2))) : Amb) = sElt k
      rw [hk]
      rfl
    rw [hb a₁ ha₁A _ ha₁] at e1
    rw [hb a₂ ha₂A _ ha₂] at e2
    exact false_of_fG (p := (2, 8)) (by simp) m e1 e2


theorem isElemAbelian_of [Finite G]
    {T Q V R P : Subgroup G}
    (ρ : ↥(Subgroup.normalizer (L : Set G)) →* ↥(quasithinG2 (ZMod 2)))
    (β : ↥(blockU L) →* ModQ) (hβs : Function.Surjective β)
    (hβk : ∀ u, β u = 1 ↔ (u : G) ∈ blockZ L)
    (hβe : ∀ (g : ↥(Subgroup.normalizer (L : Set G))) (u u' : ↥(blockU L)),
      (u' : G) = g * u * g⁻¹ → β u' = g2QAct (ZMod 2) (ρ g) (β u))
    (hρL : ∀ ℓ (hℓ : ℓ ∈ L), ρ ⟨ℓ, Subgroup.le_normalizer hℓ⟩ ∈ g2Derived (ZMod 2))
    (hρL' : ∀ x ∈ g2Derived (ZMod 2), ∃ ℓ, ∃ hℓ : ℓ ∈ L, ρ ⟨ℓ, Subgroup.le_normalizer hℓ⟩ = x)
    (hLTN : L ⊔ T ≤ Subgroup.normalizer (L : Set G))
    (hK : ∀ g, g ∈ L ⊔ T → ∀ hgN : g ∈ Subgroup.normalizer (L : Set G), ρ ⟨g, hgN⟩ = 1 →
      g ∈ Q)
    (hR : R = pre ρ hLTN r₀) (hRT : R ≤ T) (hQR : Q ≤ R) (hPLT : P ≤ L ⊔ T)
    (hPV : P ≤ Subgroup.normalizer (V : Set G))
    (hbP : ∃ g, ∃ hg : g ∈ P, ρ ⟨g, hLTN (hPLT hg)⟩ = b₀)
    (hVQ : V ≤ Q) (hQV : Q ≤ Subgroup.centralizer (V : Set G)) (hUV : blockU L ≤ V)
    (hQT : Q ≤ T) (hCQ : T ⊓ Subgroup.centralizer (V : Set G) = Q) (hVe : IsElemAbelian 2 V)
    (hQLU : ⁅Q, L⁆ ≤ blockU L) (hQQ : ∀ a ∈ Q, ∀ b ∈ Q, a * b * a⁻¹ * b⁻¹ ∈ tC L T)
    (hCe : IsElemAbelian 2 (tC L T))
    (hL2 : ∀ (N : Subgroup ↥L) [N.Normal], IsPGroup 2 (↥L ⧸ N) → N = ⊤)
    {d : G} (hdR : d ∈ Subgroup.normalizer (R : Set G))
    (hdP : d ∈ Subgroup.normalizer (P : Set G)) (hVd : ¬ CFSG.conjugate V d ≤ Q) :
    IsElemAbelian 2 Q := by
  classical
  subst hR
  have hUQ : blockU L ≤ Q := hUV.trans hVQ
  have hRLT : pre ρ hLTN r₀ ≤ L ⊔ T := fun g hg => ((mem_pre ρ hLTN).mp hg).1
  have hRN : pre ρ hLTN r₀ ≤ Subgroup.normalizer (L : Set G) := hRLT.trans hLTN
  have hRr : ∀ g (hg : g ∈ pre ρ hLTN r₀), ρ ⟨g, hRN hg⟩ ∈ r₀ := fun g hg =>
    ((mem_pre ρ hLTN).mp hg).2
  have hVc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb =>
    ThreeL32.comm_of_isElemAbelian hVe ha hb
  obtain ⟨g₀, hg₀P, hg₀⟩ := hbP
  set Vd := CFSG.conjugate V d with hVddef
  set W := CFSG.conjugate V d⁻¹ with hWdef
  have hVR : V ≤ pre ρ hLTN r₀ := hVQ.trans hQR
  have hVdR : Vd ≤ pre ρ hLTN r₀ := conjugate_le_of_mem_normalizer hVR hdR
  have hWR : W ≤ pre ρ hLTN r₀ := conjugate_le_of_mem_normalizer hVR (Subgroup.inv_mem _ hdR)
  have hVdN : Vd ≤ Subgroup.normalizer (L : Set G) := hVdR.trans hRN
  have hWN : W ≤ Subgroup.normalizer (L : Set G) := hWR.trans hRN
  have hWQ : ¬ W ≤ Q := by
    intro hle
    apply hVd
    intro x hx
    rw [← hCQ]
    refine ⟨hRT (hVdR hx), Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
    have h1 : d * y * d⁻¹ ∈ W := by
      rw [hWdef, Lem3331S.mem_conjugate_iff]
      have e : d⁻¹ * (d * y * d⁻¹) * d⁻¹⁻¹ = y := by group
      rw [e]
      exact hy
    have h2 := Subgroup.mem_centralizer_iff.mp (hQV (hle h1)) _
      (Lem3331S.mem_conjugate_iff.mp hx)
    have e : d * (y * x) * d⁻¹ = d * (x * y) * d⁻¹ := by
      calc d * (y * x) * d⁻¹ = d * y * d⁻¹ * (d * x * d⁻¹) := by group
        _ = d * x * d⁻¹ * (d * y * d⁻¹) := h2.symm
        _ = d * (x * y) * d⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel e)
  have hg₀Vd : ∀ w ∈ Vd, g₀ * w * g₀⁻¹ ∈ Vd := fun w hw => conj_mem_conjugate hPV hdP hg₀P hw
  have hg₀W : ∀ w ∈ W, g₀ * w * g₀⁻¹ ∈ W := fun w hw =>
    conj_mem_conjugate hPV (Subgroup.inv_mem _ hdP) hg₀P hw
  have hVd1 : ∃ w, ∃ hw : w ∈ Vd, ρ ⟨w, hVdN hw⟩ ≠ 1 := by
    obtain ⟨w, hw, hwQ⟩ := IsConcreteLE.not_le_iff_exists.mp hVd
    exact ⟨w, hw, fun h1 => hwQ (hK w (hRLT (hVdR hw)) _ h1)⟩
  have hW1 : ∃ w, ∃ hw : w ∈ W, ρ ⟨w, hWN hw⟩ ≠ 1 := by
    obtain ⟨w, hw, hwQ⟩ := IsConcreteLE.not_le_iff_exists.mp hWQ
    exact ⟨w, hw, fun h1 => hwQ (hK w (hRLT (hWR hw)) _ h1)⟩
  obtain ⟨hfVd, he8⟩ := fix_le_eight_of ρ hVdN (fun w hw => hRr w (hVdR hw))
    (conjugate_comm hVc d) (conjugate_sq hVe.2 d) hVd1 (g := ⟨g₀, hLTN (hPLT hg₀P)⟩) hg₀ hg₀Vd
  obtain ⟨hfW, -⟩ := fix_le_eight_of ρ hWN (fun w hw => hRr w (hWR hw))
    (conjugate_comm hVc d⁻¹) (conjugate_sq hVe.2 d⁻¹) hW1 (g := ⟨g₀, hLTN (hPLT hg₀P)⟩) hg₀
    hg₀W
  set ρVd := (ρ.comp (Subgroup.inclusion hVdN)).range with hρVd
  have h8W : 8 ≤ (Subgroup.centralizer (W : Set G)).relIndex (blockU L) :=
    le_relIndex ρ β hβs hβk hβe hWN (by omega) (inf_comm _ _)
  have hcard : 8 ≤ Nat.card ↥ρVd := by
    have h1 : (Subgroup.centralizer (W : Set G)).relIndex (blockU L) ≤
        (Subgroup.centralizer (W : Set G)).relIndex V :=
      Subgroup.relIndex_le_of_le_right hUV Subgroup.index_ne_zero_of_finite
    have h2 : (Subgroup.centralizer (V : Set G)).relIndex Vd =
        (Subgroup.centralizer (W : Set G)).relIndex V := by
      have := relIndex_centralizer_conjugate V W d
      rwa [hWdef, conjugate_inv_conjugate] at this
    have h3 := card_le_range_mul ρ hVdN (K := Q) fun b hb h1 => hK b (hRLT (hVdR hb)) _ h1
    have h4 : Nat.card ↥(Vd ⊓ Q) ≤ Nat.card ↥(Subgroup.centralizer (V : Set G) ⊓ Vd) :=
      Subgroup.card_le_of_le fun x hx => ⟨hQV hx.2, hx.1⟩
    have h5 := Subgroup.relIndex_mul_card (Subgroup.centralizer (V : Set G)) Vd
    have h6 : 0 < Nat.card ↥(Subgroup.centralizer (V : Set G) ⊓ Vd) := Nat.card_pos
    have h7 : (Subgroup.centralizer (V : Set G)).relIndex Vd *
        Nat.card ↥(Subgroup.centralizer (V : Set G) ⊓ Vd) ≤
        Nat.card ↥ρVd * Nat.card ↥(Subgroup.centralizer (V : Set G) ⊓ Vd) := by
      rw [h5]
      exact h3.trans (Nat.mul_le_mul_left _ h4)
    have h8 := Nat.le_of_mul_le_mul_right h7 h6
    omega
  have hρVdS : ρVd ≤ sSubG := by
    rintro _ ⟨w, rfl⟩
    exact r₀_le (hRr w.1 (hVdR w.2))
  have hall : ∀ j ∈ e8, ∃ w, ∃ hw : w ∈ Vd, ρ ⟨w, hVdN hw⟩ = sEltG j := by
    intro j hj
    obtain ⟨-, w, hw⟩ := mem_idx.mp (mem_idx_of_card hρVdS he8 hcard j hj)
    exact ⟨w.1, w.2, hw⟩
  set X := Q ⊓ Subgroup.centralizer (Vd : Set G) with hXdef
  set Cr := pre ρ hLTN r₀ ⊓ Subgroup.centralizer (Vd : Set G) with hCrdef
  have hCrN : Cr ≤ Subgroup.normalizer (L : Set G) := inf_le_left.trans hRN
  have hCr8 : Nat.card ↥(ρ.comp (Subgroup.inclusion hCrN)).range ≤ 8 := by
    have hS : (ρ.comp (Subgroup.inclusion hCrN)).range ≤ sSubG := by
      rintro _ ⟨x, rfl⟩
      exact r₀_le (hRr x.1 x.2.1)
    refine card_le_eight hS fun i hi => ?_
    obtain ⟨hi64, x, hx⟩ := mem_idx.mp hi
    have hc : ∀ j ∈ e8, ρ ⟨x, hCrN x.2⟩ * sEltG j = sEltG j * ρ ⟨x, hCrN x.2⟩ := by
      intro j hj
      obtain ⟨w, hw, hwj⟩ := hall j hj
      rw [← hwj, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp x.2.2 w hw).symm
    obtain ⟨j, hj, hje⟩ := mem_e8_of_commute (hRr x.1 x.2.1) hc
    have hj64 : j < 64 := by
      simp only [e8, List.mem_cons, List.not_mem_nil, or_false] at hj
      omega
    have hij : i = j := sEltG_injective hi64 hj64 (hx.symm.trans hje.symm)
    rw [hij]
    exact hj
  have hCrQ : Nat.card ↥Cr ≤ 8 * Nat.card ↥X := by
    have h1 := card_le_range_mul ρ hCrN (K := Q) fun b hb h1 => hK b (hRLT hb.1) _ h1
    have h2 : Nat.card ↥(Cr ⊓ Q) ≤ Nat.card ↥X :=
      Subgroup.card_le_of_le fun x hx => ⟨hx.2, hx.1.2⟩
    exact h1.trans (Nat.mul_le_mul hCr8 h2)
  have hCrcard : Nat.card ↥Cr = Nat.card ↥Q := by
    have h1 : pre ρ hLTN r₀ ⊓ Subgroup.centralizer (V : Set G) = Q := by
      refine le_antisymm (fun x hx => ?_) (le_inf hQR hQV)
      rw [← hCQ]
      exact ⟨hRT hx.1, hx.2⟩
    have h2 : CFSG.conjugate (pre ρ hLTN r₀ ⊓ Subgroup.centralizer (V : Set G)) d = Cr := by
      rw [conjugate_inf_centralizer, conjugate_eq_of_mem_normalizer hdR]
    rw [← h2, card_conjugate, h1]
  have h8U : 8 ≤ X.relIndex (blockU L) :=
    le_relIndex ρ β hβs hβk hβe hVdN
      (show 8 * Nat.card ↥(fixV (ρVd.map (g2QAct (ZMod 2)))) ≤ 64 by omega)
      (inf_centralizer_inf hUQ _)
  have hQX : X.relIndex Q ≤ 8 := by
    have e1 := Subgroup.relIndex_mul_card X Q
    rw [inf_of_le_left inf_le_left] at e1
    have h1 : X.relIndex Q * Nat.card ↥X ≤ 8 * Nat.card ↥X := by
      rw [e1, ← hCrcard]
      exact hCrQ
    exact Nat.le_of_mul_le_mul_right h1 Nat.card_pos
  have hQUX : Q ≤ blockU L ⊔ X := le_sup_of_relIndex inf_le_left hUQ (hQX.trans h8U)
  obtain ⟨w₂, hw₂, hw₂e⟩ := hall 2 (by decide)
  obtain ⟨w₈, hw₈, hw₈e⟩ := hall 8 (by decide)
  have hUe : IsElemAbelian 2 (blockU L) :=
    ⟨⟨⟨fun a b => Subtype.ext (hVc _ (hUV a.2) _ (hUV b.2))⟩⟩, fun x hx => hVe.2 x (hUV hx)⟩
  have hUL : blockU L ≤ L := by
    show ⁅blockQ L, L⁆ ≤ L
    rw [Subgroup.commutator_le]
    intro g₁ hg₁ g₂ hg₂
    have h1 : g₁ ∈ L := CFSG.LieType.BorelTits.pCoreOf_le 2 L hg₁
    rw [commutatorElement_def]
    exact L.mul_mem (L.mul_mem (L.mul_mem h1 hg₂) (L.inv_mem h1)) (L.inv_mem hg₂)
  have hXUC : X ≤ blockU L ⊔ tC L T := by
    intro q hq
    obtain ⟨v, hv, hvq⟩ := exists_mul_of_cocycle ρ β hβs hβk hβe hρL hρL'
      (fun ℓ hℓ h1 => hK ℓ (Subgroup.mem_sup_left hℓ) _ h1) hL2 hQLU
      (fun a ha b hb ℓ hℓ => Subgroup.mem_centralizer_iff.mp (hQQ a ha b hb).2 ℓ hℓ)
      (fun x hx hxL => ⟨hx, Subgroup.mem_centralizer_iff.mpr hxL⟩)
      (fun z hz ℓ hℓ => Subgroup.mem_centralizer_iff.mp hz.2 ℓ hℓ)
      (fun z hz => hVe.2 z (hUV hz.1))
      (fun a ha b hb => hVc a (hUV ha.1) b (hUV hb.1))
      hVdN hq.1 (fun a ha => Subgroup.mem_centralizer_iff.mp hq.2 a ha) hw₂ hw₈ hw₂e hw₈e
    have h1 : v⁻¹ * q ∈ tC L T :=
      ⟨T.mul_mem (T.inv_mem (hQT (hUQ hv))) (hQT hq.1), Subgroup.mem_centralizer_iff.mpr hvq⟩
    have e : q = v * (v⁻¹ * q) := by group
    rw [e]
    exact Subgroup.mul_mem_sup hv h1
  exact isElemAbelian_of_le_sup hUe hCe
    (fun u hu t ht => Subgroup.mem_centralizer_iff.mp ht.2 u (hUL hu))
    (hQUX.trans (sup_le le_sup_left hXUC))


theorem card_le_of_rho [Finite G] {Q R : Subgroup G}
    (ρ : ↥(Subgroup.normalizer (L : Set G)) →* ↥(quasithinG2 (ZMod 2)))
    (β : ↥(blockU L) →* ModQ) (hβs : Function.Surjective β)
    (hβk : ∀ u, β u = 1 ↔ (u : G) ∈ blockZ L)
    (hβe : ∀ (g : ↥(Subgroup.normalizer (L : Set G))) (u u' : ↥(blockU L)),
      (u' : G) = g * u * g⁻¹ → β u' = g2QAct (ZMod 2) (ρ g) (β u))
    (hUQ : blockU L ≤ Q) (hRN : R ≤ Subgroup.normalizer (L : Set G))
    (hRr : ∀ x (hx : x ∈ R), ρ ⟨x, hRN hx⟩ ∈ r₀)
    (hK : ∀ x (hx : x ∈ R), ρ ⟨x, hRN hx⟩ = 1 → x ∈ Q)
    {B : Subgroup G} (hBR : B ≤ R) (hBe : IsElemAbelian 2 B) :
    Nat.card ↥B ≤ Nat.card ↥Q ∧ (Nat.card ↥Q ≤ Nat.card ↥B → ¬ B ≤ Q →
      (∀ i, i ∈ idx (ρ.comp (Subgroup.inclusion (hBR.trans hRN))).range ↔ i ∈ e8) ∧
      (Q ⊓ Subgroup.centralizer (B : Set G)).relIndex Q ≤ 8) := by
  classical
  have hBN : B ≤ Subgroup.normalizer (L : Set G) := hBR.trans hRN
  set RB := (ρ.comp (Subgroup.inclusion hBN)).range with hRBdef
  set Y := Q ⊓ Subgroup.centralizer (B : Set G) with hYdef
  have hBc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a := fun a ha b hb =>
    ThreeL32.comm_of_isElemAbelian hBe ha hb
  have hRBr : RB ≤ r₀ := by
    rintro _ ⟨b, rfl⟩
    exact hRr b.1 (hBR b.2)
  have hRBS : RB ≤ sSubG := hRBr.trans r₀_le
  have hcard : Nat.card ↥B ≤ Nat.card ↥RB * Nat.card ↥Y := by
    have h1 := card_le_range_mul ρ hBN (K := Y) fun b hb h1 =>
      ⟨hK b (hBR hb) h1, Subgroup.mem_centralizer_iff.mpr fun c hc => hBc c hc b hb⟩
    exact h1.trans (Nat.mul_le_mul_left _ (Subgroup.card_le_of_le inf_le_right))
  have hQY : Y.relIndex Q * Nat.card ↥Y = Nat.card ↥Q := by
    have h1 := Subgroup.relIndex_mul_card Y Q
    rwa [inf_of_le_left (inf_le_left : Y ≤ Q)] at h1
  have hY0 : 0 < Nat.card ↥Y := Nat.card_pos
  have hUY : Y.relIndex (blockU L) ≤ Y.relIndex Q :=
    Subgroup.relIndex_le_of_le_right hUQ Subgroup.index_ne_zero_of_finite
  by_cases hRB1 : RB = ⊥
  · have hBQ : B ≤ Q := fun b hb => hK b (hBR hb) (by
      have h1 : (ρ.comp (Subgroup.inclusion hBN)) ⟨b, hb⟩ ∈ RB := ⟨_, rfl⟩
      rw [hRB1, Subgroup.mem_bot] at h1
      exact h1)
    exact ⟨Subgroup.card_le_of_le hBQ, fun _ h => absurd hBQ h⟩
  obtain ⟨hle64, hcls⟩ := offender_bound hRBS hRB1 (range_comm ρ hBN hBc)
    (range_sq ρ hBN hBe.2)
  have hRBcard : Nat.card ↥RB = (idx RB).card := card_eq_idx hRBS
  have : Finite ModQ := Nat.finite_of_card_ne_zero (by rw [card_ModQ]; norm_num)
  have hfix0 : 0 < Nat.card ↥(fixV (RB.map (g2QAct (ZMod 2)))) := Nat.card_pos
  have h64 : 64 ≤ Y.relIndex Q * Nat.card ↥(fixV (RB.map (g2QAct (ZMod 2)))) := by
    have h1 := Subgroup.relIndex_mul_card Y (blockU L)
    rw [inf_centralizer_inf hUQ, card_blockU_eq β hβs hβk] at h1
    have h2 := card_cU_le ρ β hβk hβe hBN
    have hZ : 0 < Nat.card ↥(blockZ L) := Nat.card_pos
    refine Nat.le_of_mul_le_mul_right ?_ hZ
    calc 64 * Nat.card ↥(blockZ L) =
          Y.relIndex (blockU L) * Nat.card ↥(blockU L ⊓ Subgroup.centralizer (B : Set G)) :=
          h1.symm
      _ ≤ Y.relIndex Q * (Nat.card ↥(fixV (RB.map (g2QAct (ZMod 2)))) *
          Nat.card ↥(blockZ L)) := Nat.mul_le_mul hUY h2
      _ = _ := by ring
  have hRBY : (idx RB).card ≤ Y.relIndex Q :=
    Nat.le_of_mul_le_mul_right (hle64.trans h64) hfix0
  refine ⟨?_, fun hQB hBQ => ?_⟩
  · calc Nat.card ↥B ≤ Nat.card ↥RB * Nat.card ↥Y := hcard
      _ ≤ Y.relIndex Q * Nat.card ↥Y := by
          rw [hRBcard]
          exact Nat.mul_le_mul_right _ hRBY
      _ = Nat.card ↥Q := hQY
  · have hYRB : Y.relIndex Q ≤ (idx RB).card := by
      refine Nat.le_of_mul_le_mul_right ?_ hY0
      rw [hQY, ← hRBcard]
      exact hQB.trans hcard
    obtain ⟨e, he, hiff⟩ := hcls (h64.trans (Nat.mul_le_mul_right _ hYRB))
    have he2 : e = 2 := by
      rcases he with rfl | rfl | rfl
      · exact absurd (even_of_mem_idx hRBr ((hiff 1).mpr d3.2.1)) (by norm_num)
      · rfl
      · exact absurd (even_of_mem_idx hRBr ((hiff 9).mpr d3.2.2)) (by norm_num)
    subst he2
    have hiff' : ∀ i, i ∈ idx RB ↔ i ∈ e8 := fun i => by rw [hiff, d3.1]
    refine ⟨hiff', ?_⟩
    have hcard8 : (idx RB).card = 8 := by
      have h1 : idx RB = e8.toFinset := Finset.ext fun i => by rw [hiff', List.mem_toFinset]
      rw [h1]
      decide
    omega

theorem centralizer_eq_of_rho [Finite G] {Q R : Subgroup G}
    (ρ : ↥(Subgroup.normalizer (L : Set G)) →* ↥(quasithinG2 (ZMod 2)))
    (β : ↥(blockU L) →* ModQ) (hβs : Function.Surjective β)
    (hβk : ∀ u, β u = 1 ↔ (u : G) ∈ blockZ L)
    (hβe : ∀ (g : ↥(Subgroup.normalizer (L : Set G))) (u u' : ↥(blockU L)),
      (u' : G) = g * u * g⁻¹ → β u' = g2QAct (ZMod 2) (ρ g) (β u))
    (hUQ : blockU L ≤ Q) (hRN : R ≤ Subgroup.normalizer (L : Set G))
    {B : Subgroup G} (hBR : B ≤ R)
    (h8 : 8 ∈ idx (ρ.comp (Subgroup.inclusion (hBR.trans hRN))).range)
    (hY8 : (Q ⊓ Subgroup.centralizer (B : Set G)).relIndex Q ≤ 8) :
    ∃ b ∈ B, Q ⊓ Subgroup.centralizer (B : Set G) = Q ⊓ Subgroup.centralizer ({b} : Set G) := by
  obtain ⟨-, ⟨b, hbB⟩, hb⟩ := mem_idx.mp h8
  refine ⟨b, hbB, ?_⟩
  have hbN : b ∈ Subgroup.normalizer (L : Set G) := hRN (hBR hbB)
  have hρb : ρ ⟨b, hbN⟩ = sEltG 8 := hb
  have hzN : Subgroup.zpowers b ≤ Subgroup.normalizer (L : Set G) := Subgroup.zpowers_le.mpr hbN
  have hZS : (ρ.comp (Subgroup.inclusion hzN)).range ≤ sSubG := by
    rintro _ ⟨⟨y, hy⟩, rfl⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have e : (⟨b ^ k, hzN hy⟩ : ↥(Subgroup.normalizer (L : Set G))) = ⟨b, hbN⟩ ^ k :=
      Subtype.ext (by simp)
    show ρ ⟨b ^ k, hzN hy⟩ ∈ sSubG
    rw [e, map_zpow, hρb]
    exact zpow_mem (mem_sSubG.mpr ⟨8, by norm_num, rfl⟩) k
  have h8Z : sEltG 8 ∈ (ρ.comp (Subgroup.inclusion hzN)).range :=
    ⟨⟨b, Subgroup.mem_zpowers b⟩, hρb⟩
  have hfix := (card_fixV_le_of_mem hZS (by norm_num) h8Z).trans d4.le
  have hcz : Subgroup.centralizer ((Subgroup.zpowers b : Subgroup G) : Set G) =
      Subgroup.centralizer ({b} : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have h8U : 8 ≤ (Q ⊓ Subgroup.centralizer ({b} : Set G)).relIndex (blockU L) :=
    le_relIndex ρ β hβs hβk hβe hzN (by omega) (by rw [inf_centralizer_inf hUQ, hcz])
  have hUY : (Q ⊓ Subgroup.centralizer ({b} : Set G)).relIndex (blockU L) ≤
      (Q ⊓ Subgroup.centralizer ({b} : Set G)).relIndex Q :=
    Subgroup.relIndex_le_of_le_right hUQ Subgroup.index_ne_zero_of_finite
  have hYY : Q ⊓ Subgroup.centralizer (B : Set G) ≤ Q ⊓ Subgroup.centralizer ({b} : Set G) :=
    inf_le_inf_left Q (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hbB))
  exact le_antisymm hYY (le_of_relIndex_le hYY inf_le_left (hY8.trans (h8U.trans hUY)))

theorem le_sup_of_idx {Q R : Subgroup G}
    (ρ : ↥(Subgroup.normalizer (L : Set G)) →* ↥(quasithinG2 (ZMod 2)))
    (hRN : R ≤ Subgroup.normalizer (L : Set G)) (hRr : ∀ x (hx : x ∈ R), ρ ⟨x, hRN hx⟩ ∈ r₀)
    (hK : ∀ x (hx : x ∈ R), ρ ⟨x, hRN hx⟩ = 1 → x ∈ Q) {B B' : Subgroup G} (hBR : B ≤ R)
    (hB'R : B' ≤ R)
    (hidx : ∀ i, i ∈ idx (ρ.comp (Subgroup.inclusion (hBR.trans hRN))).range →
      i ∈ idx (ρ.comp (Subgroup.inclusion (hB'R.trans hRN))).range) :
    B ≤ B' ⊔ Q := by
  intro x hx
  obtain ⟨i, hi, hie⟩ := mem_sSubG.mp (r₀_le (hRr x (hBR hx)))
  have hi' : i ∈ idx (ρ.comp (Subgroup.inclusion (hBR.trans hRN))).range :=
    mem_idx.mpr ⟨hi, hie ▸ ⟨⟨x, hx⟩, rfl⟩⟩
  obtain ⟨-, ⟨x', hx'⟩, hx'e⟩ := mem_idx.mp (hidx i hi')
  have hmem : x'⁻¹ * x ∈ R := R.mul_mem (R.inv_mem (hB'R hx')) (hBR hx)
  have hq : x'⁻¹ * x ∈ Q := by
    refine hK _ hmem ?_
    have e : (⟨x'⁻¹ * x, hRN hmem⟩ : ↥(Subgroup.normalizer (L : Set G))) =
        (⟨x', hRN (hB'R hx')⟩ : ↥(Subgroup.normalizer (L : Set G)))⁻¹ * ⟨x, hRN (hBR hx)⟩ := rfl
    have e' : ρ ⟨x', hRN (hB'R hx')⟩ = ρ ⟨x, hRN (hBR hx)⟩ := hx'e.trans hie
    rw [e, map_mul, map_inv, e', inv_mul_cancel]
  have e : x = x' * (x'⁻¹ * x) := by group
  rw [e]
  exact Subgroup.mul_mem_sup hx' hq


theorem step3_3_28G2_of
    (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat) (h51 : AsB51) (h25 : Stmt3_3_25)
    (h27 : Stmt3_3_27) : Step3_3_28G2 := by
  intro G _ _ T M L D h hG2 hTL hTC d hdD hdM hVd
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLTN : L ⊔ T ≤ Subgroup.normalizer (L : Set G) := sup_le Subgroup.le_normalizer hTL
  have hred := Hyp331.vPlus_reduced h.toSetup331
  have hVQ : vPlus L T ≤ qL L T := hred.1.trans inf_le_left
  have hQV : qL L T ≤ Subgroup.centralizer (vPlus L T : Set G) :=
    Subgroup.le_centralizer_iff.mp (hred.1.trans inf_le_right)
  have hLTV : L ⊔ T ≤ Subgroup.normalizer (vPlus L T : Set G) := hred.2.2.2.1
  have hUV : blockU L ≤ vPlus L T := h.blockU_le_vPlus h38 h39 hG2.1 hTL
  have hUQ : blockU L ≤ qL L T := hUV.trans hVQ
  have hQT : qL L T ≤ T := ThreeL32.qL_le h
  have hQLT : qL L T ≤ L ⊔ T := CFSG.LieType.BorelTits.pCoreOf_le 2 _
  have hCQ : T ⊓ Subgroup.centralizer (vPlus L T : Set G) = qL L T :=
    (h.centralizer_vPlus h38 h39).2.1
  obtain ⟨ρ, β, hβs, hβk, hβe, hρL, hρL', hρT, hK⟩ := G2Rho.exists_rho h38 h39 h51 h hTL hG2
  have hX := G2XS3.cZ_eq h38 h39 h hTL hG2 ρ β hβk hβe hρL hρL' hρT
  obtain ⟨hXT, -, hRP⟩ := G2XS3.parabolic_of_rho h hTL ρ hρL' hρT hK
  have hPeq : oTwoUpper (L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) ⊔ T =
      pre ρ hLTN (pw w₀) := by
    rw [hX, hXT]
  have hR : rCZ L T = pre ρ hLTN r₀ := by
    show pCoreOf 2 (oTwoUpper (L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) ⊔
      T) = _
    rw [hPeq, hRP]
  have hker : ∀ g (hg : g ∈ qL L T), ρ ⟨g, hLTN (hQLT hg)⟩ = 1 := fun g hg =>
    rho_eq_one_of_mem_centralizer ρ β hβs hβe _
      (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hUV) (hQV hg))
  have hQR : qL L T ≤ rCZ L T := fun q hq => by
    rw [hR]
    exact (mem_pre ρ hLTN).mpr ⟨hQLT hq, by rw [hker q hq]; exact r₀.one_mem⟩
  have hRT : rCZ L T ≤ T := by
    have hTs : IsSylowTwoOf T
        (oTwoUpper (L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) ⊔ T) :=
      ⟨le_sup_right, h.sylow.1, Vol2.Ch10.SecA.not_two_dvd_index_of_le h.sylow le_sup_right⟩
    exact pCoreOf_le_of_isSylowTwoOf hTs
  have hPSL : ¬ IsPSL 3 2 1 ↥(autOn L (vPlus L T)) := by
    intro hP
    have h1 := G2Blk.card_autOn h38 h39 h hTL hG2
    rw [Vol2.Ch11.SecA.card_of_isPSL (by norm_num) hP] at h1
    revert h1
    decide
  obtain ⟨hDX, hDR, -⟩ := (h25 G T M L D h).2.1 hTC hPSL
  have hdR : d ∈ Subgroup.normalizer (rCZ L T : Set G) := hDR hdD
  have hdP : d ∈ Subgroup.normalizer ((oTwoUpper (L ⊓ Subgroup.centralizer
      (quasithinOmegaOneCenter T : Set G)) ⊔ T : Subgroup G) : Set G) :=
    C1.mem_normalizer_sup (hDX hdD) (h.DN hdD)
  have hPLT : oTwoUpper (L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) ⊔ T ≤
      L ⊔ T := sup_le_sup_right ((oTwoUpper_le _).trans inf_le_left) T
  obtain ⟨ℓb, hℓbL, hℓb⟩ := hρL' b₀ b₀_b₁_mem.1.1
  have hℓbP : ℓb ∈
      oTwoUpper (L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) ⊔ T := by
    rw [hPeq]
    refine (mem_pre ρ hLTN).mpr ⟨Subgroup.mem_sup_left hℓbL, ?_⟩
    rw [show ρ ⟨ℓb, hLTN (Subgroup.mem_sup_left hℓbL)⟩ = b₀ from hℓb]
    exact b₀_mem_pw
  have hQLU : ⁅qL L T, L⁆ ≤ blockU L := Hyp331.commutator_qL_le_blockU hG2.1 hTL
  have hΦQ := h.frattini_qL_le_tC h38 h39 hG2.1 hTL
  have hQQ : ∀ a ∈ qL L T, ∀ b ∈ qL L T, a * b * a⁻¹ * b⁻¹ ∈ tC L T := by
    intro a ha b hb
    have : Fact (IsPGroup 2 ↥(qL L T)) := ⟨CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _⟩
    have h1 : ⁅(⟨a, ha⟩ : ↥(qL L T)), ⟨b, hb⟩⁆ ∈ frattini ↥(qL L T) :=
      CFSG.commutator_le_frattini_of_isPGroup (p := 2) (by
        rw [commutator_def]
        exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))
    have h2 : ((⁅(⟨a, ha⟩ : ↥(qL L T)), ⟨b, hb⟩⁆ : ↥(qL L T)) : G) ∈ tC L T :=
      hΦQ ⟨_, h1, rfl⟩
    simpa [commutatorElement_def] using h2
  obtain ⟨-, hΦC, -⟩ := h27 G T M L D h d hdD hdM hVd hTC
  have hCe : IsElemAbelian 2 (tC L T) :=
    isElemAbelian_of_frattini_eq_bot (h.sylow.1.to_le inf_le_left) hΦC
  have hQe : IsElemAbelian 2 (qL L T) :=
    isElemAbelian_of ρ β hβs hβk hβe hρL hρL' hLTN hK hR hRT hQR hPLT (hPLT.trans hLTV)
      ⟨ℓb, hℓbP, hℓb⟩ hVQ hQV hUV hQT hCQ hred.2.1 hQLU hQQ hCe hG2.1.1 hdR hdP hVd
  have hRmem : ∀ x, x ∈ rCZ L T ↔ ∃ hx : x ∈ L ⊔ T, ρ ⟨x, hLTN hx⟩ ∈ r₀ := fun x => by
    rw [hR]
    exact mem_pre ρ hLTN
  have hRLT : rCZ L T ≤ L ⊔ T := fun x hx => ((hRmem x).mp hx).1
  have hRN : rCZ L T ≤ Subgroup.normalizer (L : Set G) := hRLT.trans hLTN
  have hRr : ∀ x (hx : x ∈ rCZ L T), ρ ⟨x, hRN hx⟩ ∈ r₀ := fun x hx => ((hRmem x).mp hx).2
  have hRK : ∀ x (hx : x ∈ rCZ L T), ρ ⟨x, hRN hx⟩ = 1 → x ∈ qL L T := fun x hx h1 =>
    hK x (hRLT hx) _ h1
  refine ⟨frattini_eq_bot_of_isElemAbelian hQe,
    fun B hBR hBe => (card_le_of_rho ρ β hβs hβk hβe hUQ hRN hRr hRK hBR hBe).1, ?_, ?_⟩
  · intro B hBm hBQ
    obtain ⟨hidx, hY8⟩ := (card_le_of_rho ρ β hβs hβk hβe hUQ hRN hRr hRK hBm.1 hBm.2.1).2
      (hBm.2.2 _ hQR hQe) hBQ
    exact centralizer_eq_of_rho ρ β hβs hβk hβe hUQ hRN hBm.1 ((hidx 8).mpr (by decide)) hY8
  · intro B B' hBm hB'm hBQ hB'Q
    obtain ⟨hidx, -⟩ := (card_le_of_rho ρ β hβs hβk hβe hUQ hRN hRr hRK hBm.1 hBm.2.1).2
      (hBm.2.2 _ hQR hQe) hBQ
    obtain ⟨hidx', -⟩ := (card_le_of_rho ρ β hβs hβk hβe hUQ hRN hRr hRK hB'm.1 hB'm.2.1).2
      (hB'm.2.2 _ hQR hQe) hB'Q
    exact le_antisymm
      (sup_le (le_sup_of_idx ρ hRN hRr hRK hBm.1 hB'm.1 fun i hi => (hidx' i).mpr ((hidx i).mp hi))
        le_sup_right)
      (sup_le (le_sup_of_idx ρ hRN hRr hRK hB'm.1 hBm.1 fun i hi => (hidx i).mpr ((hidx' i).mp hi))
        le_sup_right)

end Step

end G2Step28

end CFSG.Quasithin.H13

