module

public import CFSG.Quasithin.Background.F918C2

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank

section CoverMap

variable {W : Type} [CommGroup W] {L : Subgroup (MulAut W)}

theorem normalizes_inv_of_normalizes {x : MulAut W} (hx : ∀ y : MulAut W, y ∈ L ↔ x * y * x⁻¹ ∈ L) :
    ∀ y : MulAut W, y ∈ L ↔ x⁻¹ * y * x⁻¹⁻¹ ∈ L := by
  intro y
  rw [inv_inv, hx (x⁻¹ * y * x)]
  have h : x * (x⁻¹ * y * x) * x⁻¹ = y := by group
  rw [h]

theorem invariant_map_of_normalizes {x : MulAut W} (hx : ∀ y : MulAut W, y ∈ L ↔ x * y * x⁻¹ ∈ L)
    {U : Subgroup W} (hU : ∀ l ∈ L, ∀ w ∈ U, l w ∈ U) :
    ∀ l ∈ L, ∀ w ∈ U.map x.toMonoidHom, l w ∈ U.map x.toMonoidHom := by
  rintro l hl w ⟨u, hu, rfl⟩
  have h : x * (x⁻¹ * l * x) * x⁻¹ = l := by group
  have hl' : x⁻¹ * l * x ∈ L := (hx _).2 (by rw [h]; exact hl)
  refine ⟨(x⁻¹ * l * x) u, hU _ hl' u hu, ?_⟩
  simp [MulAut.mul_apply]

theorem uniserial_map_of_normalizes {x : MulAut W} (hx : ∀ y : MulAut W, y ∈ L ↔ x * y * x⁻¹ ∈ L)
    {V Z : Subgroup W}
    (huni : ∀ S : Subgroup W, S ≤ V → (∀ l ∈ L, ∀ s ∈ S, l s ∈ S) → S = ⊥ ∨ S = Z ∨ S = V) :
    ∀ T : Subgroup W, T ≤ V.map x.toMonoidHom → (∀ l ∈ L, ∀ t ∈ T, l t ∈ T) →
      T = ⊥ ∨ T = Z.map x.toMonoidHom ∨ T = V.map x.toMonoidHom := by
  intro T hT hTinv
  have hT'V : T.map x⁻¹.toMonoidHom ≤ V := by
    rintro w ⟨t, ht, rfl⟩
    obtain ⟨v, hv, rfl⟩ := hT ht
    simpa using hv
  have hT'inv := invariant_map_of_normalizes (normalizes_inv_of_normalizes hx) hTinv
  have hTT' : T = (T.map x⁻¹.toMonoidHom).map x.toMonoidHom := by
    rw [Subgroup.map_map]
    have h : x.toMonoidHom.comp x⁻¹.toMonoidHom = MonoidHom.id W := by
      ext w
      simp
    rw [h, Subgroup.map_id]
  rcases huni _ hT'V hT'inv with h | h | h
  · left
    rw [hTT', h, Subgroup.map_bot]
  · right; left
    rw [hTT', h]
  · right; right
    rw [hTT', h]

theorem inf_le_of_uniserial [Finite W] {X ZX Y : Subgroup W}
    (huniX : ∀ T : Subgroup W, T ≤ X → (∀ l ∈ L, ∀ t ∈ T, l t ∈ T) → T = ⊥ ∨ T = ZX ∨ T = X)
    (hX : ∀ l ∈ L, ∀ w ∈ X, l w ∈ X) (hY : ∀ l ∈ L, ∀ w ∈ Y, l w ∈ Y)
    (hcard : Nat.card Y ≤ Nat.card X) (hne : X ≠ Y) : X ⊓ Y ≤ ZX := by
  rcases huniX (X ⊓ Y) inf_le_left (fun l hl w hw => ⟨hX l hl w hw.1, hY l hl w hw.2⟩) with h | h | h
  · rw [h]
    exact bot_le
  · exact h.le
  · exact absurd (Subgroup.eq_of_le_of_card_ge (inf_eq_left.1 h) hcard) hne

theorem exists_projSec_hom {A B Z S : Subgroup W} (hS : S ≤ A ⊔ B) (hAB : A ⊓ B ≤ Z) :
    ∃ β : ↥S →* ↥A ⧸ Z.subgroupOf A, ∀ (s : ↥S) (a : ↥A) (b : W), b ∈ B → (s : W) = a * b →
      β s = QuotientGroup.mk a := by
  have hdec : ∀ s : ↥S, ∃ a : ↥A, ∃ b ∈ B, (s : W) = a * b := fun s => by
    obtain ⟨a, ha, b, hb, h⟩ := Subgroup.mem_sup.1 (hS s.2)
    exact ⟨⟨a, ha⟩, b, hb, h.symm⟩
  choose fa fb hfb hf using hdec
  have key : ∀ (s : ↥S) (a : ↥A) (b : W), b ∈ B → (s : W) = a * b →
      (QuotientGroup.mk (fa s) : ↥A ⧸ Z.subgroupOf A) = QuotientGroup.mk a := by
    intro s a b hb h
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    apply hAB
    have h3 : ((fa s : W)) * fb s = a * b := (hf s).symm.trans h
    have h2 : ((fa s : W))⁻¹ * a = fb s * b⁻¹ := by
      calc ((fa s : W))⁻¹ * a = ((fa s : W))⁻¹ * (a * b) * b⁻¹ := by group
        _ = ((fa s : W))⁻¹ * ((fa s : W) * fb s) * b⁻¹ := by rw [h3]
        _ = fb s * b⁻¹ := by group
    refine ⟨((fa s)⁻¹ * a).2, ?_⟩
    show ((((fa s)⁻¹ * a : ↥A)) : W) ∈ B
    rw [Subgroup.coe_mul, Subgroup.coe_inv, h2]
    exact B.mul_mem (hfb s) (B.inv_mem hb)
  refine ⟨{ toFun := fun s => QuotientGroup.mk (fa s), map_one' := ?_, map_mul' := ?_ }, ?_⟩
  · show (QuotientGroup.mk (fa 1) : ↥A ⧸ Z.subgroupOf A) = 1
    rw [key 1 1 1 B.one_mem (by simp)]
    rfl
  · intro s t
    show (QuotientGroup.mk (fa (s * t)) : ↥A ⧸ Z.subgroupOf A) =
      QuotientGroup.mk (fa s) * QuotientGroup.mk (fa t)
    rw [← QuotientGroup.mk_mul]
    apply key (s * t) (fa s * fa t) (fb s * fb t) (B.mul_mem (hfb s) (hfb t))
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hf s, hf t]
    exact mul_mul_mul_comm _ _ _ _
  · intro s a b hb h
    exact key s a b hb h

theorem exists_projSec_equivariant {A B Z S : Subgroup W}
    (hA : ∀ l ∈ L, ∀ w ∈ A, l w ∈ A) (hB : ∀ l ∈ L, ∀ w ∈ B, l w ∈ B)
    (hZ : ∀ l ∈ L, ∀ w ∈ Z, l w ∈ Z) (hS : S ≤ A ⊔ B) (hAB : A ⊓ B ≤ Z) :
    ∃ β : ↥S →* ↥A ⧸ Z.subgroupOf A,
      (∀ (γ : ↥L) (u : ↥S) (m : ↥A) (hu : (γ : MulAut W) (u : W) ∈ S)
        (hm : (γ : MulAut W) (m : W) ∈ A),
        β u = QuotientGroup.mk m →
          β ⟨(γ : MulAut W) (u : W), hu⟩ = QuotientGroup.mk ⟨(γ : MulAut W) (m : W), hm⟩) ∧
      ∀ s : ↥S, β s = 1 → (s : W) ∈ Z ⊔ B := by
  obtain ⟨β, hβ⟩ := exists_projSec_hom hS hAB
  refine ⟨β, ?_, ?_⟩
  · intro γ u m hu hm hum
    obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup.1 (hS u.2)
    have h1 : β u = QuotientGroup.mk ⟨a, ha⟩ := hβ u ⟨a, ha⟩ b hb hab.symm
    have h2 : β ⟨(γ : MulAut W) (u : W), hu⟩ = QuotientGroup.mk ⟨(γ : MulAut W) a, hA γ γ.2 a ha⟩ := by
      refine hβ _ _ ((γ : MulAut W) b) (hB γ γ.2 b hb) ?_
      show (γ : MulAut W) (u : W) = (γ : MulAut W) a * (γ : MulAut W) b
      rw [← hab, map_mul]
    rw [h2]
    rw [h1, QuotientGroup.eq, Subgroup.mem_subgroupOf] at hum
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have h3 := hZ γ γ.2 _ hum
    simpa [map_mul, map_inv] using h3
  · intro s hs
    obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup.1 (hS s.2)
    have h1 := hβ s ⟨a, ha⟩ b hb hab.symm
    rw [hs, eq_comm, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
    rw [← hab]
    exact Subgroup.mul_mem_sup h1 hb

theorem card_le_mul_card_inf_of_le_sup [Finite W] {A B S : Subgroup W} (h : S ≤ A ⊔ B) :
    Nat.card S ≤ Nat.card A * Nat.card ↥(S ⊓ B) := by
  obtain ⟨β, hβ⟩ := exists_projSec_hom (Z := A ⊓ B) h le_rfl
  have hkB : ∀ k : ↥β.ker, ((k : ↥S) : W) ∈ S ⊓ B := by
    intro k
    obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup.1 (h (k : ↥S).2)
    have h1 := hβ k ⟨a, ha⟩ b hb hab.symm
    have hk1 : β k = 1 := k.2
    rw [hk1, eq_comm, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
    refine ⟨(k : ↥S).2, ?_⟩
    rw [← hab]
    exact B.mul_mem h1.2 hb
  have hinj : Function.Injective (fun k : ↥β.ker => (⟨((k : ↥S) : W), hkB k⟩ : ↥(S ⊓ B))) := by
    intro k k' hkk'
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun x : ↥(S ⊓ B) => (x : W)) hkk'
  have h1 := Nat.card_le_card_of_injective _ hinj
  have h2 := Nat.card_le_card_of_injective _ (QuotientGroup.kerLift_injective β)
  have h3 := Nat.card_le_card_of_surjective (QuotientGroup.mk : ↥A → ↥A ⧸ (A ⊓ B).subgroupOf A)
    QuotientGroup.mk_surjective
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup β.ker]
  exact Nat.mul_le_mul (h2.trans h3) h1

theorem secIsoL_of_uniserial_hom [Finite W] {A ZA S ZS : Subgroup W}
    (hA : ∀ l ∈ L, ∀ w ∈ A, l w ∈ A) (hZA : ∀ l ∈ L, ∀ w ∈ ZA, l w ∈ ZA)
    (hS : ∀ l ∈ L, ∀ w ∈ S, l w ∈ S) (hZS : ∀ l ∈ L, ∀ w ∈ ZS, l w ∈ ZS)
    (hZAA : ZA ≤ A) (hZSS : ZS ≤ S)
    (huniS : ∀ T : Subgroup W, T ≤ S → (∀ l ∈ L, ∀ t ∈ T, l t ∈ T) → T = ⊥ ∨ T = ZS ∨ T = S)
    (hcard : Nat.card S = Nat.card A) (hZcard : Nat.card ZS = Nat.card ZA)
    (hZA1 : 1 < Nat.card ZA) (β : ↥S →* ↥A ⧸ ZA.subgroupOf A)
    (hβe : ∀ (γ : ↥L) (u : ↥S) (m : ↥A) (hu : (γ : MulAut W) (u : W) ∈ S)
      (hm : (γ : MulAut W) (m : W) ∈ A),
      β u = QuotientGroup.mk m →
        β ⟨(γ : MulAut W) (u : W), hu⟩ = QuotientGroup.mk ⟨(γ : MulAut W) (m : W), hm⟩)
    (hβ1 : ∃ s, β s ≠ 1) : SecIsoL L S ZS A ZA := by
  classical
  have hmemT : ∀ s : ↥S, (s : W) ∈ β.ker.map S.subtype ↔ β s = 1 := by
    intro s
    constructor
    · rintro ⟨s', hs', hss'⟩
      have : s' = s := Subtype.ext hss'
      rw [← this]
      exact hs'
    · intro h
      exact ⟨s, h, rfl⟩
  have hTS : β.ker.map S.subtype ≤ S := by
    rintro w ⟨s, -, rfl⟩
    exact s.2
  have hTinv : ∀ l ∈ L, ∀ t ∈ β.ker.map S.subtype, l t ∈ β.ker.map S.subtype := by
    rintro l hl w ⟨s, hs, rfl⟩
    have hls : l (s : W) ∈ S := hS l hl s s.2
    have h1 : β s = QuotientGroup.mk (1 : ↥A) := hs
    have h2 := hβe ⟨l, hl⟩ s 1 hls (by simp) h1
    refine (hmemT ⟨l s, hls⟩).2 ?_
    rw [h2, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    simp
  have hZAc : Nat.card (ZA.subgroupOf A) = Nat.card ZA :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZAA).toEquiv
  have hA' := Subgroup.card_eq_card_quotient_mul_card_subgroup (ZA.subgroupOf A)
  rw [hZAc] at hA'
  rcases huniS _ hTS hTinv with hT | hT | hT
  ·
    exfalso
    have hinj : Function.Injective β := by
      rw [injective_iff_map_eq_one]
      intro s hs
      have h1 : (s : W) ∈ β.ker.map S.subtype := (hmemT s).2 hs
      rw [hT, Subgroup.mem_bot] at h1
      exact Subtype.ext h1
    have h1 := Nat.card_le_card_of_injective β hinj
    have hApos : 0 < Nat.card A := Nat.card_pos
    have h2 : Nat.card (↥A ⧸ ZA.subgroupOf A) * 2 ≤ Nat.card (↥A ⧸ ZA.subgroupOf A) * Nat.card ZA :=
      Nat.mul_le_mul_left _ hZA1
    nlinarith
  · have hker : ∀ s : ↥S, β s = 1 ↔ (s : W) ∈ ZS := fun s => by rw [← hmemT s, hT]
    rw [B5.secIsoL_iff]
    refine ⟨hZSS, hZAA, fun h u hu => hS h h.2 u hu, fun h z hz => hZS h h.2 z hz,
      fun γ m hm => hA γ γ.2 m hm, fun γ m hm => hZA γ γ.2 m hm, β, ?_, hker, hβe⟩
    have hkerEq : β.ker = ZS.subgroupOf S := by
      ext s
      rw [MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf]
    have hS' := Subgroup.card_eq_card_quotient_mul_card_subgroup β.ker
    have h4 : Nat.card β.ker = Nat.card ZS := by
      rw [hkerEq]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZSS).toEquiv
    rw [h4, hZcard] at hS'
    have hq : Nat.card (↥S ⧸ β.ker) = Nat.card (↥A ⧸ ZA.subgroupOf A) := by
      have hpos : 0 < Nat.card ZA := by omega
      exact Nat.eq_of_mul_eq_mul_right hpos (hS'.symm.trans (hcard.trans hA'))
    have hbij := (Nat.bijective_iff_injective_and_card (QuotientGroup.kerLift β)).2
      ⟨QuotientGroup.kerLift_injective β, hq⟩
    intro y
    obtain ⟨q, hq'⟩ := hbij.2 y
    obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨s, (QuotientGroup.kerLift_mk β s).symm.trans hq'⟩
  ·
    exfalso
    obtain ⟨s, hs⟩ := hβ1
    exact hs ((hmemT s).1 (by rw [hT]; exact s.2))

theorem secIsoL_of_common_section {S ZS A ZA B ZB : Subgroup W}
    (h1 : SecIsoL L S ZS A ZA) (h2 : SecIsoL L S ZS B ZB) : SecIsoL L B ZB A ZA := by
  obtain ⟨-, hZAA, hS, -, hA, hZA, β₁, hβ₁s, hβ₁k, hβ₁e⟩ := B5.secIsoL_iff.1 h1
  obtain ⟨-, hZBB, -, -, hB, hZB, β₂, hβ₂s, hβ₂k, hβ₂e⟩ := B5.secIsoL_iff.1 h2
  have hk : β₂.ker = β₁.ker := by
    ext s
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, hβ₁k, hβ₂k]
  let E : (↥B ⧸ ZB.subgroupOf B) ≃* (↥A ⧸ ZA.subgroupOf A) :=
    (((QuotientGroup.quotientKerEquivOfSurjective β₂ hβ₂s).symm.trans
      (QuotientGroup.quotientMulEquivOfEq hk)).trans
      (QuotientGroup.quotientKerEquivOfSurjective β₁ hβ₁s))
  have hE : ∀ s : ↥S, E (β₂ s) = β₁ s := by
    intro s
    have h : (QuotientGroup.quotientKerEquivOfSurjective β₂ hβ₂s).symm (β₂ s) =
        (QuotientGroup.mk s : ↥S ⧸ β₂.ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    show (QuotientGroup.quotientKerEquivOfSurjective β₁ hβ₁s)
      ((QuotientGroup.quotientMulEquivOfEq hk)
        ((QuotientGroup.quotientKerEquivOfSurjective β₂ hβ₂s).symm (β₂ s))) = β₁ s
    rw [h]
    rfl
  let β : ↥B →* ↥A ⧸ ZA.subgroupOf A := E.toMonoidHom.comp (QuotientGroup.mk' _)
  have hβ : ∀ b : ↥B, β b = E (QuotientGroup.mk b) := fun b => rfl
  rw [B5.secIsoL_iff]
  refine ⟨hZBB, hZAA, fun h u hu => hB h u hu, fun h z hz => hZB h z hz, hA, hZA, β, ?_, ?_, ?_⟩
  · exact E.surjective.comp (QuotientGroup.mk'_surjective _)
  · intro b
    rw [hβ, MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  · intro γ b a hb ha hba
    obtain ⟨s, hs⟩ := hβ₂s (QuotientGroup.mk b)
    have hγs : (γ : MulAut W) (s : W) ∈ S := hS γ s s.2
    have h3 : β₁ s = QuotientGroup.mk a := by
      rw [← hE, hs, ← hβ]
      exact hba
    have h4 := hβ₂e γ s b hγs hb hs
    have h5 := hβ₁e γ s a hγs ha h3
    rw [hβ, ← h4, hE, h5]

theorem card_eq_sixteen_of_binaryNaturalSL3 {V Z : Subgroup W} (hnat : BinaryNaturalSL L V Z 3 1)
    (hZ : Nat.card Z = 2) : Nat.card V = 16 := by
  obtain ⟨K, _, _, hK, π, hπ⟩ := hnat
  obtain ⟨ε, -⟩ := exists_sec_equiv_nat (StatedSL 3 K) hπ
  have hZV : Z ≤ V := hπ.2.1
  have h1 : Nat.card (↥V ⧸ Z.subgroupOf V) = 8 := by
    rw [Nat.card_congr ε.toEquiv]
    show Nat.card (Fin 3 → K) = 8
    rw [Nat.card_fun, hK]
    simp
  have h2 : Nat.card (Z.subgroupOf V) = 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZV).toEquiv, hZ]
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Z.subgroupOf V), h1, h2]

theorem not_secIsoL_map_of_outer {V Z : Subgroup W} (hnat : BinaryNaturalSL L V Z 3 1)
    {σ : MulAut W} (hσL : ∀ x ∈ L, σ * x * σ⁻¹ ∈ L)
    (hdyn : ¬ ∃ l₀ ∈ L, ∀ x ∈ L, (σ * l₀⁻¹) * x = x * (σ * l₀⁻¹)) :
    ¬ SecIsoL L (V.map σ.toMonoidHom) (Z.map σ.toMonoidHom) V Z := by
  intro hiso
  obtain ⟨K, _, _, hK, π, hπ⟩ := hnat
  exact hdyn (exists_inner_of_twist_sl3 (by simpa using hK) hπ hσL rfl rfl hiso)

theorem cover_map_eq_or {W : Type} [CommGroup W] [Finite W] (hexp : ∀ w : W, w ^ 2 = 1)
    (L : Subgroup (MulAut W)) (V : Subgroup W) (hinv : ∀ x ∈ L, ∀ v ∈ V, x v ∈ V)
    (hcomm : XMod.commOf ↥L V = V) (hnat : BinaryNaturalSL L V (V ⊓ fixV L) 3 1)
    (hZ : Nat.card ↥(V ⊓ fixV L) = 2)
    (huni : ∀ S : Subgroup W, S ≤ V → (∀ x ∈ L, ∀ s ∈ S, x s ∈ S) → S = ⊥ ∨ S = V ⊓ fixV L ∨ S = V)
    (σ : MulAut W) (hσL : ∀ x : MulAut W, x ∈ L ↔ σ * x * σ⁻¹ ∈ L)
    (hne : V.map σ.toMonoidHom ≠ V)
    (hdyn : ¬ ∃ l₀ ∈ L, ∀ x ∈ L, (σ * l₀⁻¹) * x = x * (σ * l₀⁻¹))
    (hsum : V ⊔ V.map σ.toMonoidHom = ⊤) (hint : V ⊓ V.map σ.toMonoidHom ≤ fixV L)
    (g : MulAut W) (hgL : ∀ x : MulAut W, x ∈ L ↔ g * x * g⁻¹ ∈ L) :
    V.map g.toMonoidHom = V ∨ V.map g.toMonoidHom = V.map σ.toMonoidHom := by
  classical
  have _ := hexp
  have _ := hcomm
  have _ := hint
  set Z := V ⊓ fixV L with hZdef
  have hZinv : ∀ x ∈ L, ∀ w ∈ Z, x w ∈ Z := fun x hx w hw =>
    ⟨hinv x hx w hw.1, fun y hy => by rw [hw.2 x hx]; exact hw.2 y hy⟩
  have hZV : Z ≤ V := inf_le_left
  have hVcard : Nat.card V = 16 := card_eq_sixteen_of_binaryNaturalSL3 hnat hZ
  have hB := invariant_map_of_normalizes hσL hinv
  have hZB := invariant_map_of_normalizes hσL hZinv
  have huniB := uniserial_map_of_normalizes hσL huni
  have hBcard : Nat.card (V.map σ.toMonoidHom) = 16 := by
    rw [Subgroup.card_map_of_injective σ.injective, hVcard]
  have hZBcard : Nat.card (Z.map σ.toMonoidHom) = 2 := by
    rw [Subgroup.card_map_of_injective σ.injective, hZ]
  have hS := invariant_map_of_normalizes hgL hinv
  have hZS := invariant_map_of_normalizes hgL hZinv
  have huniS := uniserial_map_of_normalizes hgL huni
  have hScard : Nat.card (V.map g.toMonoidHom) = 16 := by
    rw [Subgroup.card_map_of_injective g.injective, hVcard]
  have hZScard : Nat.card (Z.map g.toMonoidHom) = 2 := by
    rw [Subgroup.card_map_of_injective g.injective, hZ]
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hSV, hSB⟩ := hcon
  have hAB : V ⊓ V.map σ.toMonoidHom ≤ Z :=
    inf_le_of_uniserial huni hinv hB (by rw [hBcard, hVcard]) (Ne.symm hne)
  have hBA : V.map σ.toMonoidHom ⊓ V ≤ Z.map σ.toMonoidHom :=
    inf_le_of_uniserial huniB hB hinv (by rw [hBcard, hVcard]) hne
  have hSiB : V.map g.toMonoidHom ⊓ V.map σ.toMonoidHom ≤ Z.map σ.toMonoidHom := by
    rw [inf_comm]
    exact inf_le_of_uniserial huniB hB hS (by rw [hBcard, hScard]) (Ne.symm hSB)
  have hSiA : V.map g.toMonoidHom ⊓ V ≤ Z := by
    rw [inf_comm]
    exact inf_le_of_uniserial huni hinv hS (by rw [hScard, hVcard]) (Ne.symm hSV)
  have hSAB : V.map g.toMonoidHom ≤ V ⊔ V.map σ.toMonoidHom := by
    rw [hsum]
    exact le_top
  have hSBA : V.map g.toMonoidHom ≤ V.map σ.toMonoidHom ⊔ V := by
    rw [sup_comm, hsum]
    exact le_top
  obtain ⟨β₁, hβ₁e, hβ₁k⟩ := exists_projSec_equivariant hinv hB hZinv hSAB hAB
  obtain ⟨β₂, hβ₂e, hβ₂k⟩ := exists_projSec_equivariant hB hinv hZB hSBA hBA
  have hn1 : ∃ s, β₁ s ≠ 1 := by
    by_contra h
    push Not at h
    have hle : V.map g.toMonoidHom ≤ Z ⊔ V.map σ.toMonoidHom := fun w hw => hβ₁k ⟨w, hw⟩ (h _)
    have h1 := card_le_mul_card_inf_of_le_sup hle
    have h2 := Subgroup.card_le_of_le hSiB
    rw [hScard, hZ] at h1
    rw [hZBcard] at h2
    omega
  have hn2 : ∃ s, β₂ s ≠ 1 := by
    by_contra h
    push Not at h
    have hle : V.map g.toMonoidHom ≤ Z.map σ.toMonoidHom ⊔ V := fun w hw => hβ₂k ⟨w, hw⟩ (h _)
    have h1 := card_le_mul_card_inf_of_le_sup hle
    have h2 := Subgroup.card_le_of_le hSiA
    rw [hScard, hZBcard] at h1
    rw [hZ] at h2
    omega
  have i1 : SecIsoL L (V.map g.toMonoidHom) (Z.map g.toMonoidHom) V Z :=
    secIsoL_of_uniserial_hom hinv hZinv hS hZS hZV (Subgroup.map_mono hZV) huniS
      (by rw [hScard, hVcard]) (by rw [hZScard, hZ]) (by rw [hZ]; norm_num) β₁ hβ₁e hn1
  have i2 : SecIsoL L (V.map g.toMonoidHom) (Z.map g.toMonoidHom) (V.map σ.toMonoidHom)
      (Z.map σ.toMonoidHom) :=
    secIsoL_of_uniserial_hom hB hZB hS hZS (Subgroup.map_mono hZV) (Subgroup.map_mono hZV) huniS
      (by rw [hScard, hBcard]) (by rw [hZScard, hZBcard]) (by rw [hZBcard]; norm_num) β₂ hβ₂e hn2
  exact not_secIsoL_map_of_outer hnat (fun x hx => (hσL x).1 hx) hdyn
    (secIsoL_of_common_section i1 i2)

end CoverMap

end CFSG.Quasithin
