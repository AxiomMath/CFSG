module

public import CFSG.Timmesfeld.Bridge.RootStructR2ManyModule

public section

universe u

namespace CFSG.Timmesfeld.Bridge

open CFSG.QuasithinUnique.Setup.SL2Modules
open scoped MatrixGroups

namespace RootMany

section Section

variable {R : Type u} [Group R] (E A : Subgroup R)

structure IsElemSection : Prop where
  le : A ≤ E
  comm : ∀ x ∈ E, ∀ y ∈ E, x * y * x⁻¹ * y⁻¹ ∈ A
  sq : ∀ x ∈ E, x * x ∈ A

abbrev SecMod : Type u := Additive (↥E ⧸ A.subgroupOf E)

variable [A.Normal]

@[expose] def secMk (e : E) : SecMod E A := Additive.ofMul (e : ↥E ⧸ A.subgroupOf E)

omit [A.Normal] in
theorem secMk_surjective : Function.Surjective (secMk E A) := fun v =>
  QuotientGroup.mk_surjective (Additive.toMul v)

theorem secMk_eq_zero_iff (e : E) : secMk E A e = 0 ↔ (e : R) ∈ A := by
  change (e : ↥E ⧸ A.subgroupOf E) = 1 ↔ _
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]

omit [A.Normal] in
theorem secMk_eq_secMk_iff (e e' : E) : secMk E A e = secMk E A e' ↔ (e : R)⁻¹ * e' ∈ A := by
  change (e : ↥E ⧸ A.subgroupOf E) = e' ↔ _
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
  simp

variable [hS : Fact (IsElemSection E A)]

instance : AddCommGroup (SecMod E A) :=
  @Additive.addCommGroup _ (quotCommGroup E A hS.out.comm)

omit hS in
theorem secMk_mul (e e' : E) : secMk E A (e * e') = secMk E A e + secMk E A e' := rfl

omit hS in
theorem secMk_inv (e : E) : secMk E A e⁻¹ = -secMk E A e := rfl

theorem two_nsmul_secMod (v : SecMod E A) : 2 • v = 0 := by
  obtain ⟨e, rfl⟩ := secMk_surjective E A v
  rw [two_nsmul, ← secMk_mul, secMk_eq_zero_iff]
  exact hS.out.sq _ e.2

instance : Module (ZMod 2) (SecMod E A) := AddCommGroup.zmodModule (two_nsmul_secMod E A)

instance [Finite R] : Finite (SecMod E A) :=
  Finite.of_surjective (secMk E A) (secMk_surjective E A)

omit [A.Normal] in
theorem card_secMod [Finite R] : Nat.card (SecMod E A) * Nat.card A = Nat.card E := by
  have hL := Subgroup.card_eq_card_quotient_mul_card_subgroup (A.subgroupOf E)
  have hA : Nat.card ↥(A.subgroupOf E) = Nat.card A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS.out.le).toEquiv
  rw [hL, hA]
  rfl

@[expose] def secSub (B : Subgroup R) : Submodule (ZMod 2) (SecMod E A) :=
  AddSubgroup.toZModSubmodule 2
    { carrier := {v | ∃ e : E, (e : R) ∈ B ∧ secMk E A e = v}
      add_mem' := by
        rintro _ _ ⟨e, he, rfl⟩ ⟨e', he', rfl⟩
        exact ⟨e * e', B.mul_mem he he', rfl⟩
      zero_mem' := ⟨1, B.one_mem, rfl⟩
      neg_mem' := by
        rintro _ ⟨e, he, rfl⟩
        exact ⟨e⁻¹, B.inv_mem he, rfl⟩ }

theorem mem_secSub {B : Subgroup R} {v : SecMod E A} :
    v ∈ secSub E A B ↔ ∃ e : E, (e : R) ∈ B ∧ secMk E A e = v := Iff.rfl

theorem secMk_mem_secSub_iff {B : Subgroup R} (hAB : A ≤ B) (e : E) :
    secMk E A e ∈ secSub E A B ↔ (e : R) ∈ B := by
  constructor
  · rintro ⟨e', he', h⟩
    rw [secMk_eq_secMk_iff] at h
    have := B.mul_mem he' (hAB h)
    simpa using this
  · intro h
    exact ⟨e, h, rfl⟩

@[expose] def secPre (W : Submodule (ZMod 2) (SecMod E A)) : Subgroup R where
  carrier := {g | ∃ h : g ∈ E, secMk E A ⟨g, h⟩ ∈ W}
  mul_mem' := by
    rintro g g' ⟨hg, hgW⟩ ⟨hg', hg'W⟩
    exact ⟨E.mul_mem hg hg', by
      have := W.add_mem hgW hg'W
      rwa [← secMk_mul] at this⟩
  one_mem' := ⟨E.one_mem, by
    rw [show (⟨1, E.one_mem⟩ : E) = 1 from rfl]
    exact W.zero_mem⟩
  inv_mem' := by
    rintro g ⟨hg, hgW⟩
    exact ⟨E.inv_mem hg, by
      have := W.neg_mem hgW
      rwa [← secMk_inv] at this⟩

theorem mem_secPre {W : Submodule (ZMod 2) (SecMod E A)} {g : R} :
    g ∈ secPre E A W ↔ ∃ h : g ∈ E, secMk E A ⟨g, h⟩ ∈ W := Iff.rfl

theorem le_secPre (W : Submodule (ZMod 2) (SecMod E A)) : A ≤ secPre E A W := fun g hg =>
  ⟨hS.out.le hg, by
    rw [(secMk_eq_zero_iff E A ⟨g, hS.out.le hg⟩).2 hg]
    exact W.zero_mem⟩

theorem secPre_le (W : Submodule (ZMod 2) (SecMod E A)) : secPre E A W ≤ E := fun _ ⟨h, _⟩ => h

theorem eq_bot_of_secPre_eq {W : Submodule (ZMod 2) (SecMod E A)} (h : secPre E A W = A) :
    W = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  obtain ⟨e, rfl⟩ := secMk_surjective E A v
  have he : (e : R) ∈ secPre E A W := ⟨e.2, hv⟩
  rw [h] at he
  rw [Submodule.mem_bot, secMk_eq_zero_iff]
  exact he

theorem eq_top_of_secPre_eq {W : Submodule (ZMod 2) (SecMod E A)} (h : secPre E A W = E) :
    W = ⊤ := by
  rw [eq_top_iff]
  intro v _
  obtain ⟨e, rfl⟩ := secMk_surjective E A v
  have he : (e : R) ∈ secPre E A W := by rw [h]; exact e.2
  obtain ⟨_, he'⟩ := he
  exact he'

variable [E.Normal]

@[expose] def secConj (r : R) : E →* E where
  toFun e := ⟨r * e * r⁻¹, ‹E.Normal›.conj_mem _ e.2 r⟩
  map_one' := Subtype.ext (by simp)
  map_mul' e e' := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

theorem coe_secConj (r : R) (e : E) : (secConj E r e : R) = r * e * r⁻¹ := rfl

@[expose] def secConjQ (r : R) : (↥E ⧸ A.subgroupOf E) →* (↥E ⧸ A.subgroupOf E) :=
  QuotientGroup.map _ _ (secConj E r) fun e he => by
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf, coe_secConj]
    exact ‹A.Normal›.conj_mem _ (Subgroup.mem_subgroupOf.mp he) r

@[expose] def secRep : R →* (SecMod E A →ₗ[ZMod 2] SecMod E A) where
  toFun r := (MonoidHom.toAdditive (secConjQ E A r)).toZModLinearMap 2
  map_one' := by
    refine LinearMap.ext fun v => ?_
    obtain ⟨e, rfl⟩ := secMk_surjective E A v
    change secMk E A (secConj E 1 e) = secMk E A e
    congr 1
    exact Subtype.ext (by simp [coe_secConj])
  map_mul' r s := by
    refine LinearMap.ext fun v => ?_
    obtain ⟨e, rfl⟩ := secMk_surjective E A v
    change secMk E A (secConj E (r * s) e) = secMk E A (secConj E r (secConj E s e))
    congr 1
    exact Subtype.ext (by simp only [coe_secConj]; group)

theorem secRep_mk (r : R) (e : E) : secRep E A r (secMk E A e) = secMk E A (secConj E r e) :=
  rfl

theorem secRep_eq_one_iff (r : R) :
    secRep E A r = 1 ↔ ∀ e ∈ E, r * e * r⁻¹ * e⁻¹ ∈ A := by
  constructor
  · intro h e he
    have h1 := LinearMap.congr_fun h (secMk E A ⟨e, he⟩)
    rw [secRep_mk, Module.End.one_apply, secMk_eq_secMk_iff, coe_secConj] at h1
    have h2 := (inv_mem h1 : _ ∈ A)
    have e2 : ((r * e * r⁻¹)⁻¹ * e)⁻¹ = e⁻¹ * (r * e * r⁻¹) := by group
    rw [e2] at h2
    have h3 := ‹A.Normal›.conj_mem _ h2 e
    convert h3 using 1
    group
  · intro h
    refine LinearMap.ext fun v => ?_
    obtain ⟨e, rfl⟩ := secMk_surjective E A v
    rw [secRep_mk, Module.End.one_apply, secMk_eq_secMk_iff, coe_secConj]
    have h1 := h e e.2
    have h2 := ‹A.Normal›.conj_mem _ (inv_mem h1) (e : R)⁻¹
    convert h2 using 1
    group

theorem secPre_normal {W : Submodule (ZMod 2) (SecMod E A)}
    (hW : ∀ r, ∀ v ∈ W, secRep E A r v ∈ W) : (secPre E A W).Normal :=
  ⟨fun g ⟨hg, hgW⟩ r => ⟨‹E.Normal›.conj_mem _ hg r, by
    have := hW r _ hgW
    rwa [secRep_mk] at this⟩⟩

variable {F : Type*} [Field F] (f : R →* SL(2, F)) (hf : Function.Surjective f)
  (hker : ∀ k ∈ f.ker, ∀ e ∈ E, k * e * k⁻¹ * e⁻¹ ∈ A)

include hker in
theorem ker_le_ker_secRep : f.ker ≤ (secRep E A).ker := fun k hk => by
  rw [MonoidHom.mem_ker, secRep_eq_one_iff]
  exact hker k hk

@[expose] noncomputable def slRep : Representation (ZMod 2) SL(2, F) (SecMod E A) :=
  (QuotientGroup.lift f.ker (secRep E A) (ker_le_ker_secRep E A f hker)).comp
    (QuotientGroup.quotientKerEquivOfSurjective f hf).symm.toMonoidHom

theorem slRep_apply (r : R) : slRep E A f hf hker (f r) = secRep E A r := by
  have he : (QuotientGroup.quotientKerEquivOfSurjective f hf).symm (f r) = (r : R ⧸ f.ker) := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  change QuotientGroup.lift f.ker (secRep E A) (ker_le_ker_secRep E A f hker)
    ((QuotientGroup.quotientKerEquivOfSurjective f hf).symm (f r)) = secRep E A r
  rw [he, QuotientGroup.lift_mk]

theorem exists_slRep_ne_one (hnt : ∃ r : R, ∃ e ∈ E, r * e * r⁻¹ * e⁻¹ ∉ A) :
    ∃ g, slRep E A f hf hker g ≠ 1 := by
  obtain ⟨r, e, he, hre⟩ := hnt
  refine ⟨f r, fun h => hre ?_⟩
  rw [slRep_apply, secRep_eq_one_iff] at h
  exact h e he

theorem invariant_of_slRep {W : Submodule (ZMod 2) (SecMod E A)}
    (hW : ∀ g, ∀ v ∈ W, slRep E A f hf hker g v ∈ W) (r : R) :
    ∀ v ∈ W, secRep E A r v ∈ W := fun v hv => by
  rw [← slRep_apply E A f hf hker]
  exact hW _ v hv

omit [E.Normal] [A.Normal] hS in
theorem commutator_SL2_eq_top {m : ℕ} (hm : 2 ≤ m) [Finite F] (hF : Nat.card F = 2 ^ m) :
    commutator SL(2, F) = ⊤ := by
  classical
  have : Fintype F := Fintype.ofFinite F
  have h4 : ∃ s : Finset F, s.card = 4 := by
    have h : 4 ≤ (Finset.univ : Finset F).card := by
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hF]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq h
    exact ⟨s, hs⟩
  exact (CFSG.LinearGroups.special_linear_dimension_two_perfect h4).commutator_eq_top

include hf hker in
theorem sq_mul_card_le_card_of_section [Finite R] {m : ℕ} (hm : 2 ≤ m) [Finite F] [CharP F 2]
    (hF : Nat.card F = 2 ^ m) (hnt : ∃ r : R, ∃ e ∈ E, r * e * r⁻¹ * e⁻¹ ∉ A) :
    (2 ^ m) ^ 2 * Nat.card A ≤ Nat.card E := by
  classical
  have : Fintype F := Fintype.ofFinite F
  have hF' : Fintype.card F = 2 ^ m := by rw [← Nat.card_eq_fintype_card, hF]
  have h := sq_le_card_of_nontrivial hm hF' (slRep E A f hf hker)
    (exists_slRep_ne_one E A f hf hker hnt)
  rw [← card_secMod E A]
  exact Nat.mul_le_mul_right _ h

include hf hker in
theorem comm_mem_of_section {m : ℕ} (hm : 2 ≤ m) [Finite F] (hF : Nat.card F = 2 ^ m)
    {B : Subgroup R} (h1 : ∀ r : R, ∀ e ∈ E, r * e * r⁻¹ * e⁻¹ ∈ B)
    (h2 : ∀ r : R, ∀ b ∈ B, r * b * r⁻¹ * b⁻¹ ∈ A) (r : R) {e : R} (he : e ∈ E) :
    r * e * r⁻¹ * e⁻¹ ∈ A := by
  have hperf := commutator_SL2_eq_top hm hF
  have hρ := eq_one_of_trivial_of_perfect hperf (slRep E A f hf hker) (secSub E A B)
    (fun g x hx => by
      obtain ⟨s, rfl⟩ := hf g
      obtain ⟨b, hb, rfl⟩ := hx
      rw [slRep_apply, secRep_mk, secMk_eq_secMk_iff, coe_secConj]
      have h := ‹A.Normal›.conj_mem _ (inv_mem (h2 s b hb)) (b : R)⁻¹
      convert h using 1
      group)
    (fun g u => by
      obtain ⟨s, rfl⟩ := hf g
      obtain ⟨e', rfl⟩ := secMk_surjective E A u
      rw [slRep_apply, secRep_mk, sub_eq_add_neg, ← secMk_inv, ← secMk_mul]
      refine ⟨secConj E s e' * e'⁻¹, ?_, rfl⟩
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_secConj]
      exact h1 s e' e'.2) (f r)
  rw [slRep_apply, secRep_eq_one_iff] at hρ
  exact hρ e he

include hf hker in
theorem card_eq_of_irreducible_section [Finite R] {m : ℕ} (hm : 1 ≤ m) [Finite F] [CharP F 2]
    (hF : Nat.card F = 2 ^ m)
    (hirr : ∀ B : Subgroup R, B.Normal → A ≤ B → B ≤ E → B = A ∨ B = E)
    (hnt : ∃ r : R, ∃ e ∈ E, r * e * r⁻¹ * e⁻¹ ∉ A)
    (hcard : Nat.card E ^ 2 < (2 ^ m) ^ 5 * Nat.card A ^ 2) :
    Nat.card E = (2 ^ m) ^ 2 * Nat.card A := by
  classical
  have : Fintype F := Fintype.ofFinite F
  have hF' : Fintype.card F = 2 ^ m := by rw [← Nat.card_eq_fintype_card, hF]
  set ρ := slRep E A f hf hker with hρ
  have hntρ := exists_slRep_ne_one E A f hf hker hnt
  have hV : Nontrivial (SecMod E A) := by
    obtain ⟨g, hg⟩ := hntρ
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact hg (LinearMap.ext fun v => Subsingleton.elim _ _)
  have hirrρ : ρ.IsIrreducible := by
    have : Nontrivial (Subrepresentation ρ) := by
      refine ⟨⊥, ⊤, fun h' => ?_⟩
      obtain ⟨x, y, hxy⟩ := hV
      have h2 : (⊥ : Submodule (ZMod 2) (SecMod E A)) = ⊤ :=
        congrArg Subrepresentation.toSubmodule h'
      have h3 : x - y ∈ (⊥ : Submodule (ZMod 2) (SecMod E A)) := h2 ▸ Submodule.mem_top
      exact hxy (sub_eq_zero.mp ((Submodule.mem_bot _).mp h3))
    refine { eq_bot_or_eq_top := fun W => ?_ }
    have hW : ∀ r, ∀ v ∈ W.toSubmodule, secRep E A r v ∈ W.toSubmodule :=
      invariant_of_slRep E A f hf hker (fun g v hv => W.apply_mem_toSubmodule g hv)
    rcases hirr _ (secPre_normal E A hW) (le_secPre E A _) (secPre_le E A _) with h | h
    · exact Or.inl (Subrepresentation.toSubmodule_injective (eq_bot_of_secPre_eq E A h))
    · exact Or.inr (Subrepresentation.toSubmodule_injective (eq_top_of_secPre_eq E A h))
  have : Fact ρ.IsIrreducible := ⟨hirrρ⟩
  have hA : 0 < Nat.card A := Nat.card_pos
  have hcardV : Nat.card (SecMod E A) ^ 2 < (2 ^ m) ^ 5 := by
    rw [← card_secMod E A, mul_pow] at hcard
    exact lt_of_mul_lt_mul_right hcard (Nat.zero_le _)
  have h := Higman.card_eq_sq_of_irreducible hm hF' ρ hntρ hcardV
  rw [← card_secMod E A, h]

end Section

section InG

variable {G : Type u} [Group G] {R M E A : Subgroup G}

structure SecHyp (R M E A : Subgroup G) : Prop where
  le : A ≤ E
  le_R : E ≤ R
  conj_E : ∀ r ∈ R, ∀ e ∈ E, r * e * r⁻¹ ∈ E
  conj_A : ∀ r ∈ R, ∀ x ∈ A, r * x * r⁻¹ ∈ A
  comm : ∀ x ∈ E, ∀ y ∈ E, x * y * x⁻¹ * y⁻¹ ∈ A
  sq : ∀ x ∈ E, x * x ∈ A
  ker : ∀ k ∈ M, ∀ e ∈ E, k * e * k⁻¹ * e⁻¹ ∈ A

namespace SecHyp

variable (h : SecHyp R M E A)
include h

theorem normal_E : (E.subgroupOf R).Normal :=
  ⟨fun e he r => by
    rw [Subgroup.mem_subgroupOf] at he ⊢
    simpa using h.conj_E r r.2 e he⟩

theorem normal_A : (A.subgroupOf R).Normal :=
  ⟨fun e he r => by
    rw [Subgroup.mem_subgroupOf] at he ⊢
    simpa using h.conj_A r r.2 e he⟩

theorem isElemSection : IsElemSection (E.subgroupOf R) (A.subgroupOf R) where
  le := fun x hx => Subgroup.mem_subgroupOf.2 (h.le (Subgroup.mem_subgroupOf.1 hx))
  comm := fun x hx y hy => by
    rw [Subgroup.mem_subgroupOf] at hx hy ⊢
    simpa using h.comm _ hx _ hy
  sq := fun x hx => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    simpa using h.sq _ hx

theorem card_E : Nat.card (E.subgroupOf R) = Nat.card E :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.le_R).toEquiv

theorem card_A : Nat.card (A.subgroupOf R) = Nat.card A :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe (h.le.trans h.le_R)).toEquiv

variable {F : Type*} [Field F] (f : ↥R →* SL(2, F)) (hf : Function.Surjective f)
  (hker : f.ker = M.subgroupOf R)

include hker in
theorem ker' : ∀ k ∈ f.ker, ∀ e ∈ E.subgroupOf R, k * e * k⁻¹ * e⁻¹ ∈ A.subgroupOf R := by
  intro k hk e he
  rw [hker, Subgroup.mem_subgroupOf] at hk
  rw [Subgroup.mem_subgroupOf] at he ⊢
  simpa using h.ker _ hk _ he

theorem nt' {r : G} (hr : r ∈ R) {e : G} (he : e ∈ E) (hre : r * e * r⁻¹ * e⁻¹ ∉ A) :
    ∃ r' : R, ∃ e' ∈ E.subgroupOf R, r' * e' * r'⁻¹ * e'⁻¹ ∉ A.subgroupOf R :=
  ⟨⟨r, hr⟩, ⟨e, h.le_R he⟩, Subgroup.mem_subgroupOf.2 he, fun h' => hre (by
    rw [Subgroup.mem_subgroupOf] at h'
    simpa using h')⟩

include hf hker in
theorem sq_mul_card_le [Finite G] {m : ℕ} (hm : 2 ≤ m) [Finite F] [CharP F 2]
    (hF : Nat.card F = 2 ^ m) {r : G} (hr : r ∈ R) {e : G} (he : e ∈ E)
    (hre : r * e * r⁻¹ * e⁻¹ ∉ A) : (2 ^ m) ^ 2 * Nat.card A ≤ Nat.card E := by
  have := h.normal_E
  have := h.normal_A
  have : Fact (IsElemSection (E.subgroupOf R) (A.subgroupOf R)) := ⟨h.isElemSection⟩
  have := sq_mul_card_le_card_of_section _ _ f hf (h.ker' f hker) hm hF (h.nt' hr he hre)
  rwa [h.card_E, h.card_A] at this

include hf hker in
theorem comm_mem {m : ℕ} (hm : 2 ≤ m) [Finite F] (hF : Nat.card F = 2 ^ m) {B : Subgroup G}
    (h1 : ∀ r ∈ R, ∀ e ∈ E, r * e * r⁻¹ * e⁻¹ ∈ B)
    (h2 : ∀ r ∈ R, ∀ b ∈ B, r * b * r⁻¹ * b⁻¹ ∈ A) {r : G} (hr : r ∈ R) {e : G}
    (he : e ∈ E) : r * e * r⁻¹ * e⁻¹ ∈ A := by
  have := h.normal_E
  have := h.normal_A
  have : Fact (IsElemSection (E.subgroupOf R) (A.subgroupOf R)) := ⟨h.isElemSection⟩
  have key := comm_mem_of_section (E.subgroupOf R) (A.subgroupOf R) f hf (h.ker' f hker) hm hF
    (B := (B ⊓ R).subgroupOf R)
    (fun r e he => by
      rw [Subgroup.mem_subgroupOf] at he ⊢
      refine ⟨?_, (r * e * r⁻¹ * e⁻¹).2⟩
      simpa using h1 _ r.2 _ he)
    (fun r b hb => by
      rw [Subgroup.mem_subgroupOf] at hb ⊢
      simpa using h2 _ r.2 _ hb.1)
    ⟨r, hr⟩ (e := ⟨e, h.le_R he⟩) (Subgroup.mem_subgroupOf.2 he)
  rw [Subgroup.mem_subgroupOf] at key
  simpa using key

include hf hker in
theorem card_eq_of_irreducible [Finite G] {m : ℕ} (hm : 1 ≤ m) [Finite F] [CharP F 2]
    (hF : Nat.card F = 2 ^ m)
    (hirr : ∀ B : Subgroup G, A ≤ B → B ≤ E → (∀ r ∈ R, ∀ b ∈ B, r * b * r⁻¹ ∈ B) →
      B = A ∨ B = E)
    {r : G} (hr : r ∈ R) {e : G} (he : e ∈ E) (hre : r * e * r⁻¹ * e⁻¹ ∉ A)
    (hcard : Nat.card E ^ 2 < (2 ^ m) ^ 5 * Nat.card A ^ 2) :
    Nat.card E = (2 ^ m) ^ 2 * Nat.card A := by
  have := h.normal_E
  have := h.normal_A
  have : Fact (IsElemSection (E.subgroupOf R) (A.subgroupOf R)) := ⟨h.isElemSection⟩
  have key := card_eq_of_irreducible_section (E.subgroupOf R) (A.subgroupOf R) f hf
    (h.ker' f hker) hm hF (fun B hBn hAB hBE => ?_) (h.nt' hr he hre)
    (by rwa [h.card_E, h.card_A])
  · rwa [h.card_E, h.card_A] at key
  ·
    have hAB' : A ≤ B.map R.subtype := fun x hx =>
      ⟨⟨x, h.le_R (h.le hx)⟩, hAB (Subgroup.mem_subgroupOf.2 hx), rfl⟩
    have hBE' : B.map R.subtype ≤ E := by
      rintro _ ⟨b, hb, rfl⟩
      exact Subgroup.mem_subgroupOf.1 (hBE hb)
    have hBR : ∀ r ∈ R, ∀ b ∈ B.map R.subtype, r * b * r⁻¹ ∈ B.map R.subtype := by
      rintro r hr _ ⟨b, hb, rfl⟩
      exact ⟨⟨r, hr⟩ * b * ⟨r, hr⟩⁻¹, hBn.conj_mem b hb ⟨r, hr⟩, rfl⟩
    have hcomap : ∀ H : Subgroup G, H ≤ R → (B.map R.subtype = H ↔ B = H.subgroupOf R) := by
      intro H hHR
      constructor
      · rintro rfl
        ext b
        rw [Subgroup.mem_subgroupOf]
        exact ⟨fun hb => ⟨b, hb, rfl⟩, fun ⟨b', hb', e⟩ => by
          rw [← Subtype.ext e]
          exact hb'⟩
      · rintro rfl
        ext x
        constructor
        · rintro ⟨b, hb, rfl⟩
          exact Subgroup.mem_subgroupOf.1 hb
        · intro hx
          exact ⟨⟨x, hHR hx⟩, Subgroup.mem_subgroupOf.2 hx, rfl⟩
    rcases hirr _ hAB' hBE' hBR with h' | h'
    · exact Or.inl ((hcomap A (h.le.trans h.le_R)).1 h')
    · exact Or.inr ((hcomap E h.le_R).1 h')

end SecHyp

end InG

end RootMany

end CFSG.Timmesfeld.Bridge
