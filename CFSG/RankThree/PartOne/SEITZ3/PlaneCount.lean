module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.RankThree.PartOne.SEITZ3

open Subgroup
open scoped Pointwise

@[expose] def cenGen {G : Type*} [Group G] (E : Subgroup G) : Set G :=
  {k | ∃ x ∈ E, x ≠ 1 ∧ k * x = x * k}

@[expose] def cj {G : Type*} [Group G] (E : Subgroup G) (g : G) : Subgroup G :=
  E.map (MulAut.conj g).toMonoidHom

variable {G : Type*} [Group G]

theorem mem_cj {E : Subgroup G} {g x : G} : x ∈ cj E g ↔ g⁻¹ * x * g ∈ E := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hy
  · intro h
    exact ⟨g⁻¹ * x * g, h, by simp [MulAut.conj_apply, mul_assoc]⟩

theorem cj_cj {E : Subgroup G} {g : G} : cj (cj E g) g⁻¹ = E := by
  ext x
  rw [mem_cj, mem_cj]
  simp [mul_assoc]

theorem cj_inv_cj {E : Subgroup G} {g : G} : cj (cj E g⁻¹) g = E := by
  simpa using cj_cj (E := E) (g := g⁻¹)

theorem cj_le_cj {E F : Subgroup G} (h : E ≤ F) (g : G) : cj E g ≤ cj F g :=
  Subgroup.map_mono h

theorem card_cj {E : Subgroup G} {g : G} : Nat.card (cj E g) = Nat.card E :=
  Subgroup.card_map_of_injective (MulAut.conj g).injective

theorem pow_eq_one_of_mem_cj {E : Subgroup G} {g x : G} {p : ℕ} (hE : ∀ y ∈ E, y ^ p = 1)
    (hx : x ∈ cj E g) : x ^ p = 1 := by
  have h := hE _ (mem_cj.1 hx)
  have h2 : (g⁻¹ * x * g) ^ p = g⁻¹ * x ^ p * g := by
    simpa using conj_pow (a := g⁻¹) (b := x) (i := p)
  have h3 : x ^ p = g * (g⁻¹ * x ^ p * g) * g⁻¹ := by group
  rw [h3, ← h2, h]
  simp

theorem mem_normalizer_iff_cj {E : Subgroup G} {g : G} :
    g ∈ normalizer (E : Set G) ↔ cj E g = E := by
  rw [mem_normalizer_iff]
  constructor
  · intro h
    ext x
    rw [mem_cj, h (g⁻¹ * x * g)]
    simp [mul_assoc]
  · intro h y
    have h2 : g * y * g⁻¹ ∈ cj E g ↔ y ∈ E := by
      rw [mem_cj]
      simp [mul_assoc]
    rw [h] at h2
    exact h2.symm

theorem cenGen_cj (E : Subgroup G) (g : G) :
    cenGen (cj E g) = (MulAut.conj g).toMonoidHom '' cenGen E := by
  ext k
  constructor
  · rintro ⟨x, hx, hx1, hk⟩
    refine ⟨g⁻¹ * k * g, ⟨g⁻¹ * x * g, mem_cj.1 hx, ?_, ?_⟩, by simp [MulAut.conj_apply, mul_assoc]⟩
    · intro h
      apply hx1
      have : x = g * (g⁻¹ * x * g) * g⁻¹ := by simp [mul_assoc]
      rw [this, h]
      simp
    · calc g⁻¹ * k * g * (g⁻¹ * x * g) = g⁻¹ * (k * x) * g := by simp [mul_assoc]
        _ = g⁻¹ * (x * k) * g := by rw [hk]
        _ = g⁻¹ * x * g * (g⁻¹ * k * g) := by simp [mul_assoc]
  · rintro ⟨k', ⟨x, hx, hx1, hk⟩, rfl⟩
    refine ⟨g * x * g⁻¹, ⟨x, hx, rfl⟩, ?_, ?_⟩
    · intro h
      apply hx1
      have : x = g⁻¹ * (g * x * g⁻¹) * g := by simp [mul_assoc]
      rw [this, h]
      simp
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      calc g * k' * g⁻¹ * (g * x * g⁻¹) = g * (k' * x) * g⁻¹ := by simp [mul_assoc]
        _ = g * (x * k') * g⁻¹ := by rw [hk]
        _ = g * x * g⁻¹ * (g * k' * g⁻¹) := by simp [mul_assoc]

theorem closure_cenGen_cj (E : Subgroup G) (g : G) :
    closure (cenGen (cj E g)) = (closure (cenGen E)).map (MulAut.conj g).toMonoidHom := by
  rw [cenGen_cj, MonoidHom.map_closure]

theorem card_le_sq_of_exponent {p e : ℕ} (hp : p.Prime)
    (H : Subgroup (Fin 2 → Multiplicative (ZMod (p ^ e)))) (hH : ∀ h ∈ H, h ^ p = 1) :
    Nat.card H ≤ p ^ 2 := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hpe : p ^ e ≠ 0 := pow_ne_zero e hp.ne_zero
  have : NeZero (p ^ e) := ⟨hpe⟩
  let _ : Fintype (Multiplicative (ZMod (p ^ e))) := Fintype.ofFinite _
  have hcyc : ∀ n : ℕ, 0 < n → Nat.card {a : Multiplicative (ZMod (p ^ e)) // a ^ n = 1} ≤ n := by
    intro n hn
    have := IsCyclic.card_pow_eq_one_le (α := Multiplicative (ZMod (p ^ e))) hn
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    exact this
  let ι : H → (Fin 2 → {a : Multiplicative (ZMod (p ^ e)) // a ^ p = 1}) := fun h i =>
    ⟨(h : Fin 2 → Multiplicative (ZMod (p ^ e))) i, by
      have := congrFun (hH h h.2) i
      simpa using this⟩
  have hι : Function.Injective ι := by
    intro x y hxy
    apply Subtype.ext
    funext i
    have := congrFun hxy i
    exact congrArg Subtype.val this
  calc Nat.card H ≤ Nat.card (Fin 2 → {a : Multiplicative (ZMod (p ^ e)) // a ^ p = 1}) :=
        Nat.card_le_card_of_injective ι hι
    _ = (Nat.card {a : Multiplicative (ZMod (p ^ e)) // a ^ p = 1}) ^ 2 := by
        rw [Nat.card_fun, Nat.card_eq_fintype_card (α := Fin 2), Fintype.card_fin]
    _ ≤ p ^ 2 := Nat.pow_le_pow_left (hcyc p hp.pos) 2

theorem plane_unique [Finite G] {p e : ℕ} (hp : p.Prime) {S : Subgroup G}
    (φ : ↥S ≃* (Fin 2 → Multiplicative (ZMod (p ^ e)))) {F F' : Subgroup G}
    (hF : F ≤ S) (hF' : F' ≤ S) (hFp : ∀ x ∈ F, x ^ p = 1) (hFp' : ∀ x ∈ F', x ^ p = 1)
    (hc : Nat.card F = p ^ 2) (hc' : Nat.card F' = p ^ 2) : F = F' := by
  have hcomm : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x := by
    intro x hx y hy
    have h : (⟨x, hx⟩ : S) * ⟨y, hy⟩ = ⟨y, hy⟩ * ⟨x, hx⟩ :=
      φ.injective (by rw [map_mul, map_mul]; exact mul_comm _ _)
    exact congrArg Subtype.val h
  let W : Subgroup G :=
    { carrier := {x | x ∈ S ∧ x ^ p = 1}
      mul_mem' := by
        rintro a b ⟨ha, ha1⟩ ⟨hb, hb1⟩
        refine ⟨S.mul_mem ha hb, ?_⟩
        rw [(show Commute a b from hcomm a ha b hb).mul_pow, ha1, hb1, one_mul]
      one_mem' := ⟨S.one_mem, one_pow p⟩
      inv_mem' := by
        rintro a ⟨ha, ha1⟩
        exact ⟨S.inv_mem ha, by rw [inv_pow, ha1, inv_one]⟩ }
  have hFW : F ≤ W := fun x hx => ⟨hF hx, hFp x hx⟩
  have hF'W : F' ≤ W := fun x hx => ⟨hF' hx, hFp' x hx⟩
  have hJ : F ⊔ F' ≤ W := sup_le hFW hF'W
  have hJS : F ⊔ F' ≤ S := fun x hx => (hJ hx).1
  let Jm : Subgroup (Fin 2 → Multiplicative (ZMod (p ^ e))) :=
    ((F ⊔ F').subgroupOf S).map φ.toMonoidHom
  have hJm : ∀ h ∈ Jm, h ^ p = 1 := by
    rintro _ ⟨y, hy, rfl⟩
    have hy' : (y : G) ∈ F ⊔ F' := hy
    have hyp : (y : G) ^ p = 1 := (hJ hy').2
    have : y ^ p = 1 := Subtype.ext hyp
    show φ y ^ p = 1
    rw [← map_pow, this, map_one]
  have hcardJ : Nat.card (F ⊔ F' : Subgroup G) ≤ p ^ 2 := by
    have h1 := card_le_sq_of_exponent hp Jm hJm
    have h2 : Nat.card Jm = Nat.card ((F ⊔ F').subgroupOf S) :=
      Subgroup.card_map_of_injective φ.injective
    have h3 : Nat.card ((F ⊔ F').subgroupOf S) = Nat.card (F ⊔ F' : Subgroup G) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hJS).toEquiv
    rw [← h3, ← h2]
    exact h1
  have e1 : F = F ⊔ F' :=
    Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hc]; exact hcardJ)
  have e2 : F' = F ⊔ F' :=
    Subgroup.eq_of_le_of_card_ge le_sup_right (by rw [hc']; exact hcardJ)
  rw [e1, ← e2]

theorem exists_mem_normalizer_of_conj_le [Finite G] {p : ℕ} [Fact p.Prime] {S M : Subgroup G}
    (hSM : S ≤ M) (hSp : IsPGroup p ↥S) (hSidx : ¬ p ∣ S.index) {g : G}
    (hg : ∀ s ∈ S, g⁻¹ * s * g ∈ M) :
    ∃ m ∈ M, g * m ∈ normalizer (S : Set G) := by
  have hS'M : cj S g⁻¹ ≤ M := by
    intro x hx
    have := hg _ (mem_cj.1 hx)
    simpa [mul_assoc] using this
  have hS'p : IsPGroup p ↥(cj S g⁻¹) := hSp.map (MulAut.conj g⁻¹).toMonoidHom
  have hS'idx : (cj S g⁻¹).index = S.index :=
    Subgroup.index_map_equiv S (MulAut.conj g⁻¹)
  let S₁ : Subgroup ↥M := S.subgroupOf M
  let S₂ : Subgroup ↥M := (cj S g⁻¹).subgroupOf M
  have hS₁p : IsPGroup p ↥S₁ := hSp.of_equiv (Subgroup.subgroupOfEquivOfLe hSM).symm
  have hS₂p : IsPGroup p ↥S₂ := hS'p.of_equiv (Subgroup.subgroupOfEquivOfLe hS'M).symm
  have hS₁idx : ¬ p ∣ S₁.index := by
    intro h
    apply hSidx
    rw [← Subgroup.relIndex_mul_index hSM]
    exact h.mul_right _
  have hS₂idx : ¬ p ∣ S₂.index := by
    intro h
    apply hSidx
    rw [← hS'idx, ← Subgroup.relIndex_mul_index hS'M]
    exact h.mul_right _
  let Q₁ : Sylow p ↥M := hS₁p.toSylow hS₁idx
  let Q₂ : Sylow p ↥M := hS₂p.toSylow hS₂idx
  obtain ⟨m, hm⟩ := MulAction.exists_smul_eq (↥M) Q₁ Q₂
  have hle : cj S (g * (m : G)) ≤ S := by
    intro x hx
    obtain ⟨s, hs, rfl⟩ := hx
    have h1 : (⟨s, hSM hs⟩ : ↥M) ∈ S₁ := hs
    have h2 : MulAut.conj m • (⟨s, hSM hs⟩ : ↥M) ∈ ((m • Q₁ : Sylow p ↥M) : Subgroup ↥M) := by
      rw [Sylow.coe_subgroup_smul]
      exact Subgroup.smul_mem_pointwise_smul _ _ _ h1
    rw [hm] at h2
    have h3 : ((MulAut.conj m • (⟨s, hSM hs⟩ : ↥M) : ↥M) : G) ∈ cj S g⁻¹ := h2
    have h4 : ((MulAut.conj m • (⟨s, hSM hs⟩ : ↥M) : ↥M) : G) = (m : G) * s * (m : G)⁻¹ := by
      simp [MulAut.smul_def, MulAut.conj_apply]
    rw [h4] at h3
    have h5 := mem_cj.1 h3
    simpa [MulAut.conj_apply, mul_assoc] using h5
  have hS_fin : Finite ↥S := inferInstance
  have heq : cj S (g * (m : G)) = S :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [card_cj])
  exact ⟨m, m.2, mem_normalizer_iff_cj.2 heq⟩

theorem closure_cenGen_eq_top [Finite G] [IsSimpleGroup G] {p e : ℕ} [Fact p.Prime]
    (M S E' : Subgroup G) (φ : ↥S ≃* (Fin 2 → Multiplicative (ZMod (p ^ e))))
    (hSM : S ≤ M) (hSp : IsPGroup p ↥S) (hSidx : ¬ p ∣ S.index)
    (hE'S : E' ≤ S) (hE'p : ∀ x ∈ E', x ^ p = 1) (hE'c : Nat.card E' = p ^ 2)
    (hmax : ∀ N : Subgroup G, M ≤ N → N = M ∨ N = ⊤)
    (hind : ¬ M.index ≡ 1 [MOD p]) (hgen : M ≤ closure (cenGen E'))
    (F : Subgroup G) (hFp : ∀ x ∈ F, x ^ p = 1) (hFc : Nat.card F = p ^ 2) :
    closure (cenGen F) = ⊤ := by
  have hp : p.Prime := Fact.out
  have hE'ne : E' ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hE'c
    have : 1 < p ^ 2 := Nat.one_lt_pow (by norm_num) hp.one_lt
    omega
  have hMbot : M ≠ ⊥ := fun h => hE'ne (by
    rw [eq_bot_iff]; exact (hE'S.trans hSM).trans h.le)
  have hMtop : M ≠ ⊤ := fun h => hind (by rw [h, index_top])
  have hNM : normalizer (M : Set G) = M := by
    rcases hmax _ (le_normalizer (H := M)) with h | h
    · exact h
    · exfalso
      have hnormal : M.Normal := normalizer_eq_top_iff.1 h
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal M with h' | h'
      · exact hMbot h'
      · exact hMtop h'
  have hmain : closure (cenGen E') = ⊤ := by
    rcases hmax _ hgen with h | h
    · exfalso
      have hNS : ∀ n ∈ normalizer (S : Set G), n ∈ M := by
        intro n hn
        have hnS : cj S n = S := mem_normalizer_iff_cj.1 hn
        have h1 : cj E' n ≤ S := by
          intro x hx
          have : x ∈ cj S n := cj_le_cj hE'S n hx
          rwa [hnS] at this
        have h2 : cj E' n = E' :=
          plane_unique hp φ h1 hE'S (fun x hx => pow_eq_one_of_mem_cj hE'p hx) hE'p
            (by rw [card_cj]; exact hE'c) hE'c
        have h3 : closure (cenGen (cj E' n)) = closure (cenGen E') := by rw [h2]
        rw [closure_cenGen_cj, h] at h3
        have h4 : cj M n = M := h3
        have h5 := mem_normalizer_iff_cj.2 h4
        rwa [hNM] at h5
      have hmod : Nat.card (G ⧸ M) ≡ Nat.card (MulAction.fixedPoints S (G ⧸ M)) [MOD p] :=
        hSp.card_modEq_card_fixedPoints (G ⧸ M)
      have hfixed_iff : ∀ g : G, ((g : G ⧸ M) ∈ MulAction.fixedPoints S (G ⧸ M)) ↔
          ∀ s ∈ S, g⁻¹ * s * g ∈ M := by
        intro g
        rw [MulAction.mem_fixedPoints]
        have key : ∀ s : ↥S, s • (g : G ⧸ M) = (g : G ⧸ M) ↔ g⁻¹ * (s : G)⁻¹ * g ∈ M := by
          intro s
          rw [Subgroup.smul_def, MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq]
          have e : ((s : G) * g)⁻¹ * g = g⁻¹ * (s : G)⁻¹ * g := by group
          rw [e]
        simp only [key]
        constructor
        · intro h s hs
          have h1 := h ⟨s⁻¹, S.inv_mem hs⟩
          have e2 : g⁻¹ * (((⟨s⁻¹, S.inv_mem hs⟩ : ↥S) : G))⁻¹ * g = g⁻¹ * s * g := by
            simp
          rwa [e2] at h1
        · intro h s
          exact h _ (S.inv_mem s.2)
      have hfix : MulAction.fixedPoints S (G ⧸ M) = {((1 : G) : G ⧸ M)} := by
        ext x
        obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
        rw [Set.mem_singleton_iff, hfixed_iff, QuotientGroup.eq]
        constructor
        · intro hg
          obtain ⟨m, hmM, hmn⟩ := exists_mem_normalizer_of_conj_le hSM hSp hSidx hg
          have hgm : g * m ∈ M := hNS _ hmn
          have h6 := M.mul_mem hgm (M.inv_mem hmM)
          have h7 : g⁻¹ * 1 = (g * m * (m : G)⁻¹)⁻¹ := by group
          rw [h7]
          exact M.inv_mem (by simpa using h6)
        · intro hg s hs
          have hgM : g ∈ M := by simpa using M.inv_mem hg
          exact M.mul_mem (M.mul_mem (M.inv_mem hgM) (hSM hs)) hgM
      have hcard : Nat.card (MulAction.fixedPoints S (G ⧸ M)) = 1 := by
        rw [hfix]
        exact Nat.card_unique
      rw [hcard] at hmod
      exact hind hmod
    · exact h
  have hFpg : IsPGroup p ↥F := IsPGroup.of_card hFc
  obtain ⟨Q, hQ⟩ := hFpg.exists_le_sylow
  let S₀ : Sylow p G := hSp.toSylow hSidx
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq G S₀ Q
  have hQS : (Q : Subgroup G) = cj S c := by
    have h1 : ((c • S₀ : Sylow p G) : Subgroup G) = (Q : Subgroup G) := by rw [hc]
    have hS₀ : ((S₀ : Sylow p G) : Subgroup G) = S := rfl
    rw [← h1, Sylow.coe_subgroup_smul, hS₀]
    ext x
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, mem_cj]
    simp [MulAut.smul_def, ← map_inv, MulAut.conj_apply]
  have hFS : cj F c⁻¹ ≤ S := by
    intro x hx
    have h1 : x ∈ cj (cj S c) c⁻¹ := cj_le_cj (hQ.trans hQS.le) c⁻¹ hx
    rwa [cj_cj] at h1
  have hF' : cj F c⁻¹ = E' :=
    plane_unique hp φ hFS hE'S (fun x hx => pow_eq_one_of_mem_cj hFp hx) hE'p
      (by rw [card_cj]; exact hFc) hE'c
  have hF'' : F = cj E' c := by
    rw [← hF', cj_inv_cj]
  rw [hF'', closure_cenGen_cj, hmain]
  exact Subgroup.map_top_of_surjective _ (MulAut.conj c).surjective

end CFSG.RankThree.PartOne.SEITZ3
