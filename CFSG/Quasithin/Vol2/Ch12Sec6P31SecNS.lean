module

public import Mathlib.GroupTheory.IsSubnormal
public import Mathlib.GroupTheory.Solvable
public import Mathlib.GroupTheory.QuotientGroup.Basic

public section

namespace CFSG.Quasithin.H13.P31Sec

@[expose] def IsSubnormalSection (W : Type) [Group W] (Q : Type) [Group Q] : Prop :=
  ∃ (M N : Subgroup Q) (_ : (N.subgroupOf M).Normal), N ≤ M ∧ N.IsSubnormal ∧ M.IsSubnormal ∧
    Nonempty ((↥M ⧸ N.subgroupOf M) ≃* W)

@[expose] def AllNS (S : Type) [Group S] (Q : Type) [Group Q] : Prop :=
  ∀ (W : Type) [Group W], IsSimpleGroup W → (∃ a b : W, a * b ≠ b * a) →
    IsSubnormalSection W Q → Nonempty (W ≃* S)

section Transfer

variable {Q Q' : Type} [Group Q] [Group Q']

theorem IsSubnormalSection.of_surjective {W : Type} [Group W] (f : Q →* Q')
    (hf : Function.Surjective f) : IsSubnormalSection W Q' → IsSubnormalSection W Q := by
  rintro ⟨M', N', hN', hle, hNs, hMs, ⟨e⟩⟩
  set M : Subgroup Q := M'.comap f with hM
  set N : Subgroup Q := N'.comap f with hN
  let g : ↥M →* ↥M' := f.subgroupComap M'
  have hg : Function.Surjective g := f.subgroupComap_surjective M' hf
  have hNeq : N.subgroupOf M = (N'.subgroupOf M').comap g := by
    ext x
    exact Iff.rfl
  haveI : (N.subgroupOf M).Normal := by
    rw [hNeq]
    exact hN'.comap g
  refine ⟨M, N, inferInstance, Subgroup.comap_mono hle, hNs.comap f, hMs.comap f, ?_⟩
  let h : ↥M →* ↥M' ⧸ N'.subgroupOf M' := (QuotientGroup.mk' (N'.subgroupOf M')).comp g
  have hh : Function.Surjective h := (QuotientGroup.mk'_surjective _).comp hg
  have hker : h.ker = N.subgroupOf M := by
    rw [hNeq]
    ext x
    simp [h, MonoidHom.mem_ker, QuotientGroup.eq_one_iff]
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective h hh)).trans e⟩

theorem AllNS.of_surjective {S : Type} [Group S] (f : Q →* Q') (hf : Function.Surjective f)
    (h : AllNS S Q) : AllNS S Q' :=
  fun W _ hs hab hW => h W hs hab (hW.of_surjective f hf)

theorem AllNS.of_mulEquiv {S : Type} [Group S] (e : Q ≃* Q') (h : AllNS S Q) : AllNS S Q' :=
  h.of_surjective e.toMonoidHom e.surjective

end Transfer

section Split

variable {Q : Type} [Group Q] (A : Subgroup Q) [hA : A.Normal]

theorem IsSubnormalSection.of_inf_le {W : Type} [Group W] (M N : Subgroup Q)
    [hN : (N.subgroupOf M).Normal] (hNM : N ≤ M) (hNs : N.IsSubnormal) (hMs : M.IsSubnormal)
    (e : (↥M ⧸ N.subgroupOf M) ≃* W) (hAN : M ⊓ A ≤ N) : IsSubnormalSection W (Q ⧸ A) := by
  let π : Q →* Q ⧸ A := QuotientGroup.mk' A
  set M₁ : Subgroup (Q ⧸ A) := M.map π with hM₁
  set N₁ : Subgroup (Q ⧸ A) := N.map π with hN₁
  let f₁ : ↥M →* ↥M₁ := π.subgroupMap M
  have hf₁ : Function.Surjective f₁ := π.subgroupMap_surjective M
  have hNeq : N₁.subgroupOf M₁ = (N.subgroupOf M).map f₁ := by
    ext y
    constructor
    · intro hy
      obtain ⟨n, hn, hny⟩ := Subgroup.mem_subgroupOf.1 hy
      refine ⟨⟨n, hNM hn⟩, Subgroup.mem_subgroupOf.2 hn, ?_⟩
      exact Subtype.ext hny
    · rintro ⟨x, hx, rfl⟩
      exact Subgroup.mem_subgroupOf.2 ⟨(x : Q), Subgroup.mem_subgroupOf.1 hx, rfl⟩
  haveI : (N₁.subgroupOf M₁).Normal := by
    rw [hNeq]
    exact hN.map f₁ hf₁
  refine ⟨M₁, N₁, inferInstance, Subgroup.map_mono hNM, hNs.map (QuotientGroup.mk'_surjective A),
    hMs.map (QuotientGroup.mk'_surjective A), ?_⟩
  let g₁ : ↥M →* ↥M₁ ⧸ N₁.subgroupOf M₁ := (QuotientGroup.mk' (N₁.subgroupOf M₁)).comp f₁
  have hg₁ : Function.Surjective g₁ := (QuotientGroup.mk'_surjective _).comp hf₁
  have hker : g₁.ker = N.subgroupOf M := by
    ext m
    simp only [g₁, MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
    constructor
    · intro hm
      obtain ⟨n, hn, hnm⟩ := Subgroup.mem_subgroupOf.1 hm
      have h1 : π (n⁻¹ * (m : Q)) = 1 := by
        rw [map_mul, map_inv]
        have : π n = π (m : Q) := hnm
        rw [this, inv_mul_cancel]
      have h2 : n⁻¹ * (m : Q) ∈ A := (QuotientGroup.eq_one_iff _).1 h1
      have h3 : n⁻¹ * (m : Q) ∈ M ⊓ A := ⟨M.mul_mem (M.inv_mem (hNM hn)) m.2, h2⟩
      have h4 : n⁻¹ * (m : Q) ∈ N := hAN h3
      have h5 : (m : Q) = n * (n⁻¹ * (m : Q)) := (mul_inv_cancel_left n _).symm
      exact Subgroup.mem_subgroupOf.2 (by rw [h5]; exact N.mul_mem hn h4)
    · intro hm
      exact Subgroup.mem_subgroupOf.2 ⟨(m : Q), Subgroup.mem_subgroupOf.1 hm, rfl⟩
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective g₁ hg₁)).symm.trans e⟩

theorem IsSubnormalSection.of_not_inf_le {W : Type} [Group W] (M N : Subgroup Q)
    [hN : (N.subgroupOf M).Normal] (hNM : N ≤ M) (hNs : N.IsSubnormal) (hMs : M.IsSubnormal)
    (e : (↥M ⧸ N.subgroupOf M) ≃* W) (hsimple : IsSimpleGroup (↥M ⧸ N.subgroupOf M))
    (hAN : ¬ M ⊓ A ≤ N) : IsSubnormalSection W ↥A := by
  set P : Subgroup ↥M := (M ⊓ A).subgroupOf M with hP
  haveI hPn : P.Normal := ⟨fun x hx g => by
    rw [hP, Subgroup.mem_subgroupOf] at hx ⊢
    exact ⟨M.mul_mem (M.mul_mem g.2 x.2) (M.inv_mem g.2), by
      have := hA.conj_mem (x : Q) hx.2 (g : Q)
      simpa using this⟩⟩
  set K : Subgroup (↥M ⧸ N.subgroupOf M) := P.map (QuotientGroup.mk' (N.subgroupOf M)) with hK
  haveI hKn : K.Normal := hPn.map _ (QuotientGroup.mk'_surjective _)
  obtain ⟨x, hx, hxN⟩ := SetLike.not_le_iff_exists.1 hAN
  have hKtop : K = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal K with h | h
    · exfalso
      have hmem : (QuotientGroup.mk (⟨x, hx.1⟩ : ↥M) : ↥M ⧸ N.subgroupOf M) ∈ K :=
        ⟨⟨x, hx.1⟩, Subgroup.mem_subgroupOf.2 hx, rfl⟩
      rw [h, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hmem
      exact hxN (Subgroup.mem_subgroupOf.1 hmem)
    · exact h
  let M₂ : Subgroup ↥A := M.subgroupOf A
  let N₂ : Subgroup ↥A := N.subgroupOf A
  let ι : ↥M₂ →* ↥M :=
    { toFun := fun x => ⟨((x : ↥A) : Q), x.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hNeq : N₂.subgroupOf M₂ = (N.subgroupOf M).comap ι := by
    ext x
    exact Iff.rfl
  haveI : (N₂.subgroupOf M₂).Normal := by
    rw [hNeq]
    exact hN.comap ι
  refine ⟨M₂, N₂, inferInstance, fun y hy => hNM hy, hNs.subgroupOf, hMs.subgroupOf, ?_⟩
  let g₂ : ↥M₂ →* ↥M ⧸ N.subgroupOf M := (QuotientGroup.mk' (N.subgroupOf M)).comp ι
  have hg₂ : Function.Surjective g₂ := by
    intro y
    have hy : y ∈ K := hKtop ▸ Subgroup.mem_top y
    obtain ⟨z, hz, rfl⟩ := hy
    refine ⟨⟨⟨(z : Q), (Subgroup.mem_subgroupOf.1 hz).2⟩, (Subgroup.mem_subgroupOf.1 hz).1⟩, ?_⟩
    rfl
  have hker : g₂.ker = N₂.subgroupOf M₂ := by
    rw [hNeq]
    ext y
    simp [g₂, MonoidHom.mem_ker, QuotientGroup.eq_one_iff]
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective g₂ hg₂)).trans e⟩

end Split

theorem AllNS.of_split {S : Type} [Group S] {Q : Type} [Group Q] (A : Subgroup Q) [A.Normal]
    (hA : AllNS S ↥A) (hQ : AllNS S (Q ⧸ A)) : AllNS S Q := by
  intro W _ hW hnab hsec
  obtain ⟨M, N, hN, hNM, hNs, hMs, ⟨e⟩⟩ := hsec
  haveI := hW
  haveI : IsSimpleGroup (↥M ⧸ N.subgroupOf M) := e.isSimpleGroup
  by_cases hAN : M ⊓ A ≤ N
  · exact hQ W hW hnab (IsSubnormalSection.of_inf_le A M N hNM hNs hMs e hAN)
  · exact hA W hW hnab (IsSubnormalSection.of_not_inf_le A M N hNM hNs hMs e inferInstance hAN)

section Basic

variable {S : Type} [Group S] {Q : Type} [Group Q]

theorem AllNS.of_solvable [Group.IsSolvable Q] : AllNS S Q := by
  intro W _ hW hnab hsec
  exfalso
  obtain ⟨M, N, hN, hNM, hNs, hMs, ⟨e⟩⟩ := hsec
  haveI : Group.IsSolvable ↥M := inferInstance
  haveI : Group.IsSolvable (↥M ⧸ N.subgroupOf M) := inferInstance
  haveI : Group.IsSolvable W := Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective
  obtain ⟨a, b, hab⟩ := hnab
  exact hab (((IsSimpleGroup.comm_iff_isSolvable (G := W)).2 inferInstance) a b)

theorem AllNS.of_simple (hQ : IsSimpleGroup Q) (e : Q ≃* S) : AllNS S Q := by
  intro W _ hW hnab hsec
  obtain ⟨M, N, hN, hNM, hNs, hMs, ⟨e'⟩⟩ := hsec
  have hM : M = ⊥ ∨ M = ⊤ := Subgroup.IsSubnormal.eq_bot_or_top_of_isSimpleGroup hQ hMs
  have hN' : N = ⊥ ∨ N = ⊤ := Subgroup.IsSubnormal.eq_bot_or_top_of_isSimpleGroup hQ hNs
  obtain ⟨a, b, hab⟩ := hnab
  rcases hM with rfl | rfl
  · exfalso
    have h1 : ∀ x : ↥(⊥ : Subgroup Q) ⧸ N.subgroupOf ⊥, x = 1 := fun x => by
      obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective x
      have : m = 1 := Subsingleton.elim _ _
      rw [this]
      rfl
    have ha : a = 1 := e'.symm.injective ((h1 _).trans (map_one e'.symm).symm)
    have hb : b = 1 := e'.symm.injective ((h1 _).trans (map_one e'.symm).symm)
    exact hab (by rw [ha, hb])
  · rcases hN' with rfl | rfl
    ·
      have e1 : (↥(⊤ : Subgroup Q) ⧸ (⊥ : Subgroup Q).subgroupOf ⊤) ≃* Q :=
        (QuotientGroup.quotientMulEquivOfEq (by simp)).trans
          ((QuotientGroup.quotientBot).trans Subgroup.topEquiv)
      exact ⟨e'.symm.trans (e1.trans e)⟩
    · exfalso
      have h1 : ∀ x : ↥(⊤ : Subgroup Q) ⧸ (⊤ : Subgroup Q).subgroupOf ⊤, x = 1 := fun x => by
        obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective x
        exact (QuotientGroup.eq_one_iff m).2 (Subgroup.mem_subgroupOf.2 (Subgroup.mem_top _))
      have ha : a = 1 := e'.symm.injective ((h1 _).trans (map_one e'.symm).symm)
      have hb : b = 1 := e'.symm.injective ((h1 _).trans (map_one e'.symm).symm)
      exact hab (by rw [ha, hb])

theorem AllNS.of_quasisimple (hQ : IsSimpleGroup (Q ⧸ Subgroup.center Q))
    (e : (Q ⧸ Subgroup.center Q) ≃* S) : AllNS S Q := by
  haveI : (Subgroup.center Q).Normal := inferInstance
  refine AllNS.of_split (Subgroup.center Q) ?_ (AllNS.of_simple hQ e)
  haveI : Group.IsSolvable ↥(Subgroup.center Q) := inferInstance
  exact AllNS.of_solvable

end Basic

end CFSG.Quasithin.H13.P31Sec
