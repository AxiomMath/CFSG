module

public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma4FStar
public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma4Perm
public import CFSG.Dihedral.Glauberman.DicksonMaxB
public import CFSG.Walter.PSL2Facts.Even
public import CFSG.Quasithin.H13.L1332Inputs

public section

namespace CFSG.Quasithin.H13

namespace L1294I

open CFSG.Open

variable {G : Type} [Group G] [Finite G]

theorem exists_pow_seven {N : Subgroup G} (h7 : 7 ∣ Nat.card N) :
    ∃ g ∈ N, g ^ 7 = 1 ∧ g ≠ 1 := by
  have : Fact (Nat.Prime 7) := ⟨by decide⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := N) 7 h7
  refine ⟨g, g.2, ?_, ?_⟩
  · rw [← Subgroup.coe_pow, ← hg, pow_orderOf_eq_one, Subgroup.coe_one]
  · intro h
    have : g = 1 := Subtype.ext h
    rw [this, orderOf_one] at hg
    norm_num at hg

theorem not_seven_dvd {N Γ : Subgroup G} (hNΓ : N ≤ Γ) (h7 : ∀ g ∈ Γ, g ^ 7 = 1 → g = 1) :
    ¬ 7 ∣ Nat.card N := fun hd => by
  obtain ⟨g, hg, hg7, hg1⟩ := exists_pow_seven hd
  exact hg1 (h7 g (hNΓ hg) hg7)

theorem card_sl_three : Nat.card (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) = 168 := by
  rw [card_sl_zmod_two]
  decide

theorem card_of_quot_sl3 {L : Subgroup G}
    (e : ↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :
    ∃ k, Nat.card L = 2 ^ k * 21 := by
  have h1 := (CFSG.pCore 2 ↥L).card_mul_index
  rw [Subgroup.index, Nat.card_congr e.toEquiv, card_sl_three] at h1
  obtain ⟨a, ha⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥L)).exists_card_eq
  exact ⟨a + 3, by rw [← h1, ha, pow_add]; ring⟩

omit [Finite G] in
theorem seven_dvd_of_card {L : Subgroup G} {k : ℕ} (h : Nat.card L = 2 ^ k * 21) :
    7 ∣ Nat.card L := by
  rw [h]
  exact Dvd.dvd.mul_left (by norm_num) _

omit [Finite G] in
theorem false_of_perm_iso {n : ℕ} (hn : n = 7 ∨ n = 8) {Γ S L : Subgroup G}
    (e : ↥Γ ≃* Equiv.Perm (Fin n)) (hS : QuasithinUnique.IsSylowTwoOf S Γ) (hLΓ : L ≤ Γ)
    (hSL : S ≤ Subgroup.normalizer (L : Set G)) {k : ℕ} (hL : Nat.card L = 2 ^ k * 21) :
    False := by
  obtain ⟨hSΓ, hS2, hidx⟩ := hS
  set S' := (S.subgroupOf Γ).map (e : ↥Γ →* Equiv.Perm (Fin n)) with hS'
  set L' := (L.subgroupOf Γ).map (e : ↥Γ →* Equiv.Perm (Fin n)) with hL'
  have hS'2 : IsPGroup 2 S' := by
    have h1 : IsPGroup 2 (S.subgroupOf Γ) := hS2.of_equiv (Subgroup.subgroupOfEquivOfLe hSΓ).symm
    exact h1.map _
  have hS'idx : ¬ 2 ∣ S'.index := by
    rw [hS', Subgroup.index_map_equiv]
    exact hidx
  have hL'c : Nat.card L' = 2 ^ k * 21 := by
    rw [hL', Subgroup.card_map_of_injective e.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLΓ).toEquiv, hL]
  have hS'L' : S' ≤ Subgroup.normalizer (L' : Set (Equiv.Perm (Fin n))) := by
    rintro _ ⟨s, hs, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have hsN := hSL (Subgroup.mem_subgroupOf.1 hs)
    obtain ⟨z, rfl⟩ := e.surjective y
    constructor
    · rintro ⟨l, hl, hle⟩
      have hzl : z = l := (e.injective hle).symm
      subst hzl
      refine ⟨s * z * s⁻¹, Subgroup.mem_subgroupOf.2 ?_, by simp⟩
      simpa using (Subgroup.mem_normalizer_iff.1 hsN (z : G)).1 (Subgroup.mem_subgroupOf.1 hl)
    · rintro ⟨l, hl, hle⟩
      have hzl : s * z * s⁻¹ = l := by
        apply e.injective
        have hle' : e l = e s * e z * (e s)⁻¹ := hle
        rw [hle', map_mul, map_mul, map_inv]
      refine ⟨z, Subgroup.mem_subgroupOf.2 ?_, rfl⟩
      have h2 := (Subgroup.mem_normalizer_iff.1 hsN (z : G)).2
      apply h2
      have : ((s * z * s⁻¹ : ↥Γ) : G) ∈ L := by rw [hzl]; exact Subgroup.mem_subgroupOf.1 hl
      simpa using this
  exact L1294J.false_of_perm hn hS'2 hS'idx hS'L' hL'c

theorem nonempty_sl2_four_mulEquiv :
    Nonempty (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 2) ≃* alternatingGroup (Fin 5)) := by
  obtain ⟨e⟩ := CFSG.Glauberman.Dickson.nonempty_psl2_galoisField_four_mulEquiv
  have : CharP (GaloisField 2 2) 2 := inferInstance
  exact ⟨(CFSG.Walter.psl2MulEquivSL2OfCharTwo (K := GaloisField 2 2)).symm.trans e⟩

theorem eq_one_of_pow_seven_prod {A : Type} [Group A] (eA : A ≃* alternatingGroup (Fin 5))
    (φ : ↥(genFittingFStar G) ≃* A × A) {g : G} (hg : g ^ 7 = 1) : g = 1 := by
  set F := genFittingFStar G with hF
  let ι₁ : A →* G := F.subtype.comp (φ.symm.toMonoidHom.comp (MonoidHom.inl A A))
  let ι₂ : A →* G := F.subtype.comp (φ.symm.toMonoidHom.comp (MonoidHom.inr A A))
  have hι₁ : ∀ a, ι₁ a = ((φ.symm (a, 1) : ↥F) : G) := fun a => rfl
  have hι₂ : ∀ b, ι₂ b = ((φ.symm (1, b) : ↥F) : G) := fun b => rfl
  have hinj₁ : Function.Injective ι₁ := fun a a' h => by
    have := φ.symm.injective (Subtype.ext h)
    exact congrArg Prod.fst this
  have hinj₂ : Function.Injective ι₂ := fun b b' h => by
    have := φ.symm.injective (Subtype.ext h)
    exact congrArg Prod.snd this
  have hc : ∀ x ∈ ι₁.range, ∀ y ∈ ι₂.range, x * y = y * x := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    rw [hι₁, hι₂, ← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul]
    congr 2
    simp
  have hinf : ι₁.range ⊓ ι₂.range = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨⟨a, rfl⟩, ⟨b, hb⟩⟩
    rw [hι₁, hι₂] at *
    have h1 : φ.symm (1, b) = φ.symm (a, 1) := Subtype.ext hb
    have h2 := congrArg Prod.fst (φ.symm.injective h1)
    simp only at h2
    rw [← h2]
    simp
  have hFeq : F = ι₁.range ⊔ ι₂.range := by
    refine le_antisymm (fun f hf => ?_) (sup_le ?_ ?_)
    · have hdec : (⟨f, hf⟩ : ↥F) = φ.symm ((φ ⟨f, hf⟩).1, 1) * φ.symm (1, (φ ⟨f, hf⟩).2) := by
        apply φ.injective
        rw [map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
        simp
      have : f = ι₁ (φ ⟨f, hf⟩).1 * ι₂ (φ ⟨f, hf⟩).2 := by
        rw [hι₁, hι₂, ← Subgroup.coe_mul, ← hdec]
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨_, rfl⟩) (Subgroup.mem_sup_right ⟨_, rfl⟩)
    · rintro _ ⟨a, rfl⟩
      exact (φ.symm (a, 1)).2
    · rintro _ ⟨b, rfl⟩
      exact (φ.symm (1, b)).2
  exact L1294F.eq_one_of_pow_seven hFeq hc hinf ((MonoidHom.ofInjective hinj₁).symm.trans eA)
    ((MonoidHom.ofInjective hinj₂).symm.trans eA) hg

theorem eq_one_of_pow_seven_sup {Γ L L' : Subgroup G} (hLΓ : L ≤ Γ) (hL'Γ : L' ≤ Γ)
    (hF : (genFittingFStar ↥Γ).map Γ.subtype = L ⊔ L') (hc : ∀ a ∈ L, ∀ b ∈ L', a * b = b * a)
    (hinf : L ⊓ L' = ⊥) (eL : ↥L ≃* alternatingGroup (Fin 5))
    (eL' : ↥L' ≃* alternatingGroup (Fin 5)) {g : G} (hgΓ : g ∈ Γ) (hg : g ^ 7 = 1) : g = 1 := by
  set L₀ := L.subgroupOf Γ
  set L₀' := L'.subgroupOf Γ
  have hF₀ : genFittingFStar ↥Γ = L₀ ⊔ L₀' := by
    apply Subgroup.map_injective Γ.subtype_injective
    rw [hF, Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hLΓ,
      Subgroup.map_subgroupOf_eq_of_le hL'Γ]
  have hc₀ : ∀ a ∈ L₀, ∀ b ∈ L₀', a * b = b * a := fun a ha b hb =>
    Subtype.ext (hc a (Subgroup.mem_subgroupOf.1 ha) b (Subgroup.mem_subgroupOf.1 hb))
  have hinf₀ : L₀ ⊓ L₀' = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hx, hx'⟩
    have : (x : G) ∈ L ⊓ L' := ⟨Subgroup.mem_subgroupOf.1 hx, Subgroup.mem_subgroupOf.1 hx'⟩
    rw [hinf, Subgroup.mem_bot] at this
    exact (Subgroup.mem_bot).2 (Subtype.ext this)
  have h := L1294F.eq_one_of_pow_seven hF₀ hc₀ hinf₀
    ((Subgroup.subgroupOfEquivOfLe hLΓ).trans eL) ((Subgroup.subgroupOfEquivOfLe hL'Γ).trans eL')
    (g := ⟨g, hgΓ⟩) (Subtype.ext (by simpa using hg))
  exact congrArg Subtype.val h

end L1294I

end CFSG.Quasithin.H13
