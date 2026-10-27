module

public import CFSG.Quasithin.Background.B2Factorization
public import CFSG.Quasithin.Background.A4Defs
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115List

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace S152S


section SylowHelpers

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isSylowTwoOf_restrict {A C H : Subgroup G} (hA : IsSylowTwoOf A H) (hAC : A ≤ C)
    (hCH : C ≤ H) : IsSylowTwoOf A C := by
  refine ⟨hAC, hA.2.1, ?_⟩
  have h := Subgroup.relIndex_mul_relIndex A C H hAC hCH
  intro h2
  apply hA.2.2
  have h3 : 2 ∣ A.relIndex H := by rw [← h]; exact Dvd.dvd.mul_right h2 _
  exact h3

omit [Finite G] in
theorem cjSub_eq_self_of_mem_normalizer {g : G} {H : Subgroup G}
    (hg : g ∈ Subgroup.normalizer (H : Set G)) : cjSub g H = H := by
  ext x
  rw [mem_cjSub]
  have h := (Subgroup.mem_normalizer_iff.1 (inv_mem hg) x)
  simpa [mul_assoc] using h.symm

theorem isSylowTwoOf_cjSub_of_mem_normalizer {A H : Subgroup G} (hA : IsSylowTwoOf A H) {g : G}
    (hg : g ∈ Subgroup.normalizer (H : Set G)) : IsSylowTwoOf (cjSub g A) H := by
  refine ⟨cjSub_le hg hA.1, ?_, ?_⟩
  · obtain ⟨n, hn⟩ := (IsPGroup.iff_card.1 hA.2.1)
    exact IsPGroup.of_card (n := n) (by rw [card_cjSub]; exact hn)
  · have h := Subgroup.relIndex_map_map_of_injective (f := (MulAut.conj g).toMonoidHom) A H
      (MulAut.conj g).injective
    have e : (cjSub g H) = H := cjSub_eq_self_of_mem_normalizer hg
    have h' : (cjSub g A).relIndex H = A.relIndex H := by
      have := h
      unfold cjSub at e ⊢
      rw [e] at this
      exact this
    show ¬ 2 ∣ (cjSub g A).relIndex H
    rw [h']
    exact hA.2.2

theorem exists_cjSub_eq_of_isSylowTwoOf {T A H : Subgroup G} (hT : IsSylowTwoOf T H)
    (hA : IsSylowTwoOf A H) : ∃ h ∈ H, cjSub h A = T := by
  obtain ⟨h, hh, hle⟩ := exists_conj_le_of_isSylowTwoOf hT hA.1 hA.2.1
  obtain ⟨h', hh', hle'⟩ := exists_conj_le_of_isSylowTwoOf hA hT.1 hT.2.1
  have hcard1 : Nat.card A ≤ Nat.card T := by
    rw [← card_cjSub h A]; exact Subgroup.card_le_of_le hle
  have hcard2 : Nat.card T ≤ Nat.card A := by
    rw [← card_cjSub h' T]; exact Subgroup.card_le_of_le hle'
  exact ⟨h, hh, Subgroup.eq_of_le_of_card_ge hle (by rw [card_cjSub]; omega)⟩

omit [Finite G] in
theorem cjSub_mul_eq (a b : G) (X : Subgroup G) : cjSub (a * b) X = cjSub a (cjSub b X) := by
  ext x
  simp [mem_cjSub, mul_assoc]

omit [Finite G] in
theorem mem_normalizer_of_cjSub_eq_self {g : G} {K : Subgroup G} (h : cjSub g K = K) :
    g ∈ Subgroup.normalizer (K : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have h1 : g * x * g⁻¹ ∈ cjSub g K ↔ x ∈ K := by
    rw [mem_cjSub]
    simp [mul_assoc]
  rw [h] at h1
  exact h1.symm

omit [Finite G] in
theorem mem_normalizer_of_conj_mem_in {I L : Subgroup G} (hL : ∀ m ∈ I, ∀ x ∈ L, m * x * m⁻¹ ∈ L)
    {m : G} (hm : m ∈ I) : m ∈ Subgroup.normalizer (L : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => hL m hm x hx, fun hx => ?_⟩
  have := hL m⁻¹ (I.inv_mem hm) _ hx
  simpa [mul_assoc] using this

omit [Finite G] in
theorem mem_normalizer_conj_of_mem_normalizer_cjSub {b h : G} {A : Subgroup G}
    (hb : b ∈ Subgroup.normalizer ((cjSub h A : Subgroup G) : Set G)) :
    h⁻¹ * b * h ∈ Subgroup.normalizer (A : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  have h1 := Subgroup.mem_normalizer_iff.1 hb (h * y * h⁻¹)
  rw [mem_cjSub, mem_cjSub] at h1
  have e1 : h⁻¹ * (h * y * h⁻¹) * h = y := by group
  have e2 : h⁻¹ * (b * (h * y * h⁻¹) * b⁻¹) * h = h⁻¹ * b * h * y * (h⁻¹ * b * h)⁻¹ := by group
  rw [e1, e2] at h1
  exact h1

end SylowHelpers

section Core

variable {G : Type} [Group G] [Finite G]

def mulNormSub (Y Mi : Subgroup G) (h : ∀ m ∈ Mi, ∀ y ∈ Y, m * y * m⁻¹ ∈ Y) : Subgroup G where
  carrier := {x | ∃ y ∈ Y, ∃ m ∈ Mi, x = y * m}
  one_mem' := ⟨1, Y.one_mem, 1, Mi.one_mem, by simp⟩
  mul_mem' := by
    rintro _ _ ⟨y₁, hy₁, m₁, hm₁, rfl⟩ ⟨y₂, hy₂, m₂, hm₂, rfl⟩
    refine ⟨y₁ * (m₁ * y₂ * m₁⁻¹), Y.mul_mem hy₁ (h m₁ hm₁ y₂ hy₂), m₁ * m₂, Mi.mul_mem hm₁ hm₂, ?_⟩
    simp [mul_assoc]
  inv_mem' := by
    rintro _ ⟨y, hy, m, hm, rfl⟩
    refine ⟨m⁻¹ * y⁻¹ * m, ?_, m⁻¹, Mi.inv_mem hm, ?_⟩
    · have := h m⁻¹ (Mi.inv_mem hm) y⁻¹ (Y.inv_mem hy)
      simpa using this
    · simp [mul_assoc]

omit [Finite G] in
theorem eq_or_eq_of_maximal_invariant {I Mi L₀ Y : Subgroup G} (hL₀I : L₀ ≤ I) (hMiI : Mi ≤ I)
    (hmax : ∀ J : Subgroup G, Mi ≤ J → J ≤ I → J = Mi ∨ J = I)
    (hYL : Y ≤ L₀) (hMY : L₀ ⊓ Mi ≤ Y) (hinv : ∀ m ∈ Mi, ∀ y ∈ Y, m * y * m⁻¹ ∈ Y) :
    Y = L₀ ⊓ Mi ∨ Y = L₀ := by
  let J := mulNormSub Y Mi hinv
  have hMiJ : Mi ≤ J := fun m hm => ⟨1, Y.one_mem, m, hm, by simp⟩
  have hJI : J ≤ I := by
    rintro _ ⟨y, hy, m, hm, rfl⟩
    exact I.mul_mem (hL₀I (hYL hy)) (hMiI hm)
  rcases hmax J hMiJ hJI with hJ | hJ
  · left
    refine le_antisymm (fun y hy => ⟨hYL hy, ?_⟩) hMY
    have : y ∈ J := ⟨y, hy, 1, Mi.one_mem, by simp⟩
    rw [hJ] at this
    exact this
  · right
    refine le_antisymm hYL (fun l hl => ?_)
    have hlJ : l ∈ J := by rw [hJ]; exact hL₀I hl
    obtain ⟨y, hy, m, hm, rfl⟩ := hlJ
    have hmL : m ∈ L₀ := by
      have := L₀.mul_mem (L₀.inv_mem (hYL hy)) hl
      simpa using this
    exact Y.mul_mem hy (hMY ⟨hmL, hm⟩)

theorem normalizer_le_of_maximal_invariant {I Mi L₀ S₁ Z₀ P : Subgroup G}
    (hL₀I : L₀ ≤ I) (hMiI : Mi ≤ I)
    (hmax : ∀ J : Subgroup G, Mi ≤ J → J ≤ I → J = Mi ∨ J = I)
    (hL₀n : ∀ m ∈ I, ∀ x ∈ L₀, m * x * m⁻¹ ∈ L₀)
    (hZL' : ∀ g ∈ L₀, cjSub g Z₀ = Z₀) (hZMi' : ∀ m ∈ Mi, cjSub m Z₀ = Z₀)
    (hS₁ : IsSylowTwoOf S₁ L₀) (hS₁M : S₁ ≤ Mi)
    (hP : P ≤ L₀) (hPtop : P ≠ L₀) (hMP : L₀ ⊓ Mi ≤ P)
    (hNP : L₀ ⊓ Subgroup.normalizer ((S₁ ⊔ Z₀ : Subgroup G) : Set G) ≤ P) :
    L₀ ⊓ Subgroup.normalizer ((S₁ ⊔ Z₀ : Subgroup G) : Set G) ≤ L₀ ⊓ Mi := by
  set M₀ : Subgroup G := L₀ ⊓ Mi with hM₀
  set N : Subgroup G := L₀ ⊓ Subgroup.normalizer ((S₁ ⊔ Z₀ : Subgroup G) : Set G) with hN
  let Fam : Set (Subgroup G) := {Q | Q ≤ L₀ ∧ Q ≠ L₀ ∧ M₀ ≤ Q ∧ N ≤ Q}
  have hPF : P ∈ Fam := ⟨hP, hPtop, hMP, hNP⟩
  have hcj : ∀ m ∈ Mi, ∀ Q ∈ Fam, cjSub m Q ∈ Fam := by
    intro m hm Q hQ
    have hmI : m ∈ I := hMiI hm
    have hmN : m ∈ Subgroup.normalizer (L₀ : Set G) := mem_normalizer_of_conj_mem_in hL₀n hmI
    have hmN' : m⁻¹ ∈ Subgroup.normalizer (L₀ : Set G) := inv_mem hmN
    have hM₀Q : M₀ ≤ cjSub m Q := by
      intro x hx
      rw [mem_cjSub]
      refine hQ.2.2.1 ⟨?_, ?_⟩
      · have := hL₀n m⁻¹ (I.inv_mem hmI) x hx.1
        simpa [mul_assoc] using this
      · exact Mi.mul_mem (Mi.mul_mem (Mi.inv_mem hm) hx.2) hm
    refine ⟨cjSub_le hmN hQ.1, ?_, hM₀Q, ?_⟩
    · intro h
      apply hQ.2.1
      have h1 : cjSub m⁻¹ (cjSub m Q) = Q := cjSub_inv_cjSub m Q
      rw [h, cjSub_eq_self_of_mem_normalizer hmN'] at h1
      exact h1.symm
    · intro x hx
      have hS₂ : IsSylowTwoOf (cjSub m S₁) L₀ := isSylowTwoOf_cjSub_of_mem_normalizer hS₁ hmN
      have hS₂M : cjSub m S₁ ≤ M₀ :=
        le_inf hS₂.1 (cjSub_le (Subgroup.le_normalizer hm) hS₁M)
      have hS₁M₀ : IsSylowTwoOf S₁ M₀ :=
        isSylowTwoOf_restrict hS₁ (le_inf hS₁.1 hS₁M) inf_le_left
      have hS₂M₀ : IsSylowTwoOf (cjSub m S₁) M₀ := isSylowTwoOf_restrict hS₂ hS₂M inf_le_left
      obtain ⟨c, hcM, hc⟩ := exists_cjSub_eq_of_isSylowTwoOf hS₁M₀ hS₂M₀
      have hcL : c ∈ L₀ := hcM.1
      have hsup : cjSub (c * m) (S₁ ⊔ Z₀) = S₁ ⊔ Z₀ := by
        have e2 : cjSub m Z₀ = Z₀ := hZMi' m hm
        have e3 : cjSub c Z₀ = Z₀ := hZL' c hcL
        have hs : ∀ (g : G) (A B : Subgroup G), cjSub g (A ⊔ B) = cjSub g A ⊔ cjSub g B :=
          fun g A B => Subgroup.map_sup _ _ _
        rw [cjSub_mul_eq, hs, e2, hs, hc, e3]
      have hw : c * m ∈ Subgroup.normalizer ((S₁ ⊔ Z₀ : Subgroup G) : Set G) :=
        mem_normalizer_of_cjSub_eq_self hsup
      have hx' : (c * m)⁻¹ * x * (c * m) ∈ N := by
        refine ⟨?_, ?_⟩
        · have h1 : c⁻¹ * x * c ∈ L₀ := L₀.mul_mem (L₀.mul_mem (L₀.inv_mem hcL) hx.1) hcL
          have h2 := hL₀n m⁻¹ (I.inv_mem hmI) _ h1
          simpa [mul_assoc] using h2
        · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hw) hx.2) hw
      have hx'Q : m⁻¹ * (c⁻¹ * x * c) * m ∈ Q := by
        have := hQ.2.2.2 hx'
        simpa [mul_assoc] using this
      have hcx : c⁻¹ * x * c ∈ cjSub m Q := by
        rw [mem_cjSub]
        exact hx'Q
      have hcQ : c ∈ cjSub m Q := hM₀Q hcM
      have := (cjSub m Q).mul_mem (cjSub m Q |>.mul_mem hcQ hcx) ((cjSub m Q).inv_mem hcQ)
      simpa [mul_assoc] using this
  let Yh : Subgroup G := sInf Fam
  have hYhP : Yh ≤ P := sInf_le hPF
  have hMYh : M₀ ≤ Yh := le_sInf fun Q hQ => hQ.2.2.1
  have hNYh : N ≤ Yh := le_sInf fun Q hQ => hQ.2.2.2
  have hYhinv : ∀ m ∈ Mi, ∀ y ∈ Yh, m * y * m⁻¹ ∈ Yh := by
    intro m hm y hy
    rw [Subgroup.mem_sInf]
    intro Q hQ
    have h1 : cjSub m⁻¹ Q ∈ Fam := hcj m⁻¹ (Mi.inv_mem hm) Q hQ
    have h2 : y ∈ cjSub m⁻¹ Q := (Subgroup.mem_sInf.1 hy) _ h1
    rw [mem_cjSub] at h2
    simpa using h2
  have hYhL : Yh ≤ L₀ := hYhP.trans hP
  rcases eq_or_eq_of_maximal_invariant hL₀I hMiI hmax hYhL hMYh hYhinv with h | h
  · exact hNYh.trans h.le
  · exfalso
    apply hPtop
    exact le_antisymm hP (h ▸ hYhP)

end Core

end S152S

open S152S

variable {G : Type} [Group G] [Finite G]

@[expose] def BorelTitsLite (X : Type) [Group X] : Prop :=
  ∀ U : Subgroup X, U ≠ ⊥ → IsPGroup 2 U →
    ∃ (S : Sylow 2 X) (P : Subgroup X), P ≠ ⊤ ∧ Subgroup.normalizer (U : Set X) ≤ P ∧
      Subgroup.normalizer ((S : Subgroup X) : Set X) ≤ P

theorem BorelTitsLite.of_holds {X : Type} [Group X] (h : Holds X 2) : BorelTitsLite X := by
  intro U hU hp
  obtain ⟨S, P, hP, hN, -, -, hS⟩ := h U hU hp
  exact ⟨S, P, hP, hN, hS⟩

@[expose] def BorelCentralizerTrivial (X : Type) [Group X] : Prop :=
  ∀ U : Subgroup X, IsPGroup 2 U → ¬ 2 ∣ U.index → ∀ x : X,
    (∀ b ∈ Subgroup.normalizer (U : Set X), x * b = b * x) → x = 1

open CFSG.QuasithinUnique.Ch1 in
theorem false_of_inducesInner_borel {I S Mi L₀ : Subgroup G} {z : G}
    (hS : IsSylowTwoOf S I) (hzS : z ∈ Subgroup.centralizer (S : Set G)) (hz2 : z ^ 2 = 1)
    (hMi : Mi = I ⊓ Subgroup.centralizer ({z} : Set G))
    (hmax : ∀ J : Subgroup G, Mi ≤ J → J ≤ I → J = Mi ∨ J = I)
    (hL₀I : L₀ ≤ I) (hL₀n : (L₀.subgroupOf I).Normal)
    (hinn : InducesInner z L₀) (hnc : ¬ ∀ x ∈ L₀, x * z = z * x)
    (hBT : BorelTitsLite (↥L₀ ⧸ Subgroup.center ↥L₀))
    (hR1 : BorelCentralizerTrivial (↥L₀ ⧸ Subgroup.center ↥L₀)) : False := by
  obtain ⟨l₀, hl₀, hact⟩ := hinn
  have hMiI : Mi ≤ I := by rw [hMi]; exact inf_le_left
  have hL₀conj : ∀ m ∈ I, ∀ x ∈ L₀, m * x * m⁻¹ ∈ L₀ := by
    intro m hm x hx
    have := hL₀n.conj_mem ⟨x, hL₀I hx⟩ (Subgroup.mem_subgroupOf.2 hx) ⟨m, hm⟩
    exact Subgroup.mem_subgroupOf.1 this
  have hzz : z * z = 1 := by rw [← pow_two]; exact hz2
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hzz
  have hMl : ∀ x ∈ L₀ ⊓ Mi, x * l₀ = l₀ * x := by
    intro x hx
    have hxz : z * x = x * z := by
      have := Subgroup.mem_centralizer_iff.1 ((hMi ▸ hx.2 : x ∈ I ⊓ Subgroup.centralizer ({z} : Set G)).2) z
        (Set.mem_singleton z)
      exact this
    have h1 := hact x hx.1
    have h2 : z⁻¹ * x * z = x := by rw [hzi, mul_assoc, ← hxz, ← mul_assoc, hzz, one_mul]
    rw [h2] at h1
    calc x * l₀ = l₀ * (l₀⁻¹ * x * l₀) := by group
      _ = l₀ * x := by rw [← h1]
  have hl₀2 : ∀ y ∈ L₀, (l₀ * l₀) * y = y * (l₀ * l₀) := by
    intro y hy
    have hy' : l₀⁻¹ * y * l₀ ∈ L₀ := L₀.mul_mem (L₀.mul_mem (L₀.inv_mem hl₀) hy) hl₀
    have h1 := hact y hy
    have h2 := hact _ hy'
    have h3 : z⁻¹ * (z⁻¹ * y * z) * z = y := by
      rw [hzi]
      calc z * (z * y * z) * z = (z * z) * y * (z * z) := by group
        _ = y := by rw [hzz]; simp
    have h4 : l₀⁻¹ * (l₀⁻¹ * y * l₀) * l₀ = y := by
      rw [← h2, ← h1]; exact h3
    calc (l₀ * l₀) * y = (l₀ * l₀) * (l₀⁻¹ * (l₀⁻¹ * y * l₀) * l₀) := by rw [h4]
      _ = y * (l₀ * l₀) := by group
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let π : ↥L₀ →* (↥L₀ ⧸ Subgroup.center ↥L₀) := QuotientGroup.mk' _
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hπker : ∀ a : ↥L₀, π a = 1 ↔ a ∈ Subgroup.center ↥L₀ := fun a => QuotientGroup.eq_one_iff a
  let l₁ : ↥L₀ := ⟨l₀, hl₀⟩
  let lb : ↥L₀ ⧸ Subgroup.center ↥L₀ := π l₁
  have hlb2 : lb * lb = 1 := by
    show π l₁ * π l₁ = 1
    rw [← map_mul, hπker, Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (by simpa using (hl₀2 g.1 g.2).symm)
  have hlb1 : lb ≠ 1 := by
    intro h
    rw [show lb = π l₁ from rfl, hπker, Subgroup.mem_center_iff] at h
    apply hnc
    intro x hx
    have h1 := hact x hx
    have h2 : l₀⁻¹ * x * l₀ = x := by
      have := congrArg Subtype.val (h ⟨x, hx⟩)
      have h3 : x * l₀ = l₀ * x := this
      calc l₀⁻¹ * x * l₀ = l₀⁻¹ * (x * l₀) := by group
        _ = x := by rw [h3]; group
    rw [h2] at h1
    calc x * z = z * (z⁻¹ * x * z) := by group
      _ = z * x := by rw [h1]
  have hnorm : I ≤ Subgroup.normalizer (L₀ : Set G) := fun m hm =>
    mem_normalizer_of_conj_mem_in hL₀conj hm
  have hS₁ : IsSylowTwoOf (S ⊓ L₀) L₀ := A4.isSylowTwoOf_inf_normal hS hL₀I hnorm
  have hSMi : S ≤ Mi := by
    intro s hs
    rw [hMi]
    refine ⟨hS.1 hs, Subgroup.mem_centralizer_iff.2 ?_⟩
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    exact (Subgroup.mem_centralizer_iff.1 hzS s hs).symm
  have hS₁Mi : S ⊓ L₀ ≤ Mi := inf_le_left.trans hSMi
  let Q₁ : Sylow 2 ↥L₀ := IsPGroup.toSylow
    (P := (S ⊓ L₀).subgroupOf L₀) (hS₁.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS₁.1).symm) hS₁.2.2
  let Ub : Sylow 2 (↥L₀ ⧸ Subgroup.center ↥L₀) := Sylow.mapSurjective hπs Q₁
  have hUb : (Ub : Subgroup (↥L₀ ⧸ Subgroup.center ↥L₀)) = ((S ⊓ L₀).subgroupOf L₀).map π := by
    rw [Sylow.coe_mapSurjective]
    rfl
  have hU₁ne : Subgroup.zpowers lb ≠ ⊥ := by
    rw [Ne, Subgroup.zpowers_eq_bot]
    exact hlb1
  have hU₁p : IsPGroup 2 (Subgroup.zpowers lb) := by
    have : orderOf lb = 2 := orderOf_eq_prime (by rw [sq]; exact hlb2) hlb1
    exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, this]; simp)
  obtain ⟨S', P, hPtop, hNU, hNS'⟩ := hBT _ hU₁ne hU₁p
  have hcomm_mem : ∀ a : ↥L₀, (a : G) ∈ Mi → π a ∈ P := by
    intro a ha
    have hal : (a : G) * l₀ = l₀ * (a : G) := hMl a ⟨a.2, ha⟩
    apply hNU
    have hc : π a * lb = lb * π a := by
      show π a * π l₁ = π l₁ * π a
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext hal
    apply Subgroup.centralizer_le_normalizer
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    exact ((Commute.zpow_left (show Commute lb (π a) from hc.symm) k)).eq
  have hUbP : (Ub : Subgroup (↥L₀ ⧸ Subgroup.center ↥L₀)) ≤ P := by
    intro y hy
    rw [hUb] at hy
    obtain ⟨s, hs, rfl⟩ := hy
    exact hcomm_mem s (hS₁Mi (Subgroup.mem_subgroupOf.1 hs |> fun h => h))
  have hSylP : IsSylowTwoOf (Ub : Subgroup (↥L₀ ⧸ Subgroup.center ↥L₀)) P :=
    isSylowTwoOf_of_sylow Ub hUbP
  have hS'P : (S' : Subgroup (↥L₀ ⧸ Subgroup.center ↥L₀)) ≤ P :=
    Subgroup.le_normalizer.trans hNS'
  have hS'Syl : IsSylowTwoOf (S' : Subgroup (↥L₀ ⧸ Subgroup.center ↥L₀)) P :=
    isSylowTwoOf_of_sylow S' hS'P
  obtain ⟨h, hhP, hh⟩ := exists_cjSub_eq_of_isSylowTwoOf hSylP hS'Syl
  have hNUb : Subgroup.normalizer ((Ub : Subgroup (↥L₀ ⧸ Subgroup.center ↥L₀)) : Set _) ≤ P := by
    intro b hb
    rw [← hh] at hb
    have h1 := mem_normalizer_conj_of_mem_normalizer_cjSub hb
    have h2 : h⁻¹ * b * h ∈ P := hNS' h1
    have := P.mul_mem (P.mul_mem hhP h2) (P.inv_mem hhP)
    simpa [mul_assoc] using this
  let Z₀ : Subgroup G := (Subgroup.center ↥L₀).map L₀.subtype
  have hZmem : ∀ x : G, x ∈ Z₀ ↔ x ∈ L₀ ∧ ∀ y ∈ L₀, y * x = x * y := by
    intro x
    constructor
    · rintro ⟨c, hc, rfl⟩
      refine ⟨c.2, fun y hy => ?_⟩
      have := Subgroup.mem_center_iff.1 hc ⟨y, hy⟩
      exact congrArg Subtype.val this
    · rintro ⟨hx, hxc⟩
      exact ⟨⟨x, hx⟩, Subgroup.mem_center_iff.2 fun g => Subtype.ext (hxc g.1 g.2), rfl⟩
  have hZconj : ∀ g ∈ I, ∀ x ∈ Z₀, g * x * g⁻¹ ∈ Z₀ := by
    intro g hg x hx
    obtain ⟨hxL, hxc⟩ := (hZmem x).1 hx
    refine (hZmem _).2 ⟨hL₀conj g hg x hxL, fun y hy => ?_⟩
    have hy' : g⁻¹ * y * g ∈ L₀ := by
      have := hL₀conj g⁻¹ (I.inv_mem hg) y hy
      simpa using this
    have := hxc _ hy'
    calc y * (g * x * g⁻¹) = g * ((g⁻¹ * y * g) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * y * g)) * g⁻¹ := by rw [this]
      _ = g * x * g⁻¹ * y := by group
  have hZcj : ∀ g ∈ I, cjSub g Z₀ = Z₀ := by
    intro g hg
    ext x
    rw [mem_cjSub]
    constructor
    · intro h
      have := hZconj g hg _ h
      simpa [mul_assoc] using this
    · intro h
      have := hZconj g⁻¹ (I.inv_mem hg) _ h
      simpa [mul_assoc] using this
  let W' : Subgroup ↥L₀ := (Ub : Subgroup (↥L₀ ⧸ Subgroup.center ↥L₀)).comap π
  let W : Subgroup G := W'.map L₀.subtype
  have hWmem : ∀ c : ↥L₀, (c : G) ∈ W ↔ π c ∈ (Ub : Subgroup (↥L₀ ⧸ Subgroup.center ↥L₀)) := by
    intro c
    constructor
    · rintro ⟨a, ha, hac⟩
      have : a = c := Subtype.ext hac
      subst this
      exact ha
    · intro h
      exact ⟨c, h, rfl⟩
  have hW : (S ⊓ L₀) ⊔ Z₀ = W := by
    apply le_antisymm
    · refine sup_le (fun x hx => ?_) (fun x hx => ?_)
      · have hxs : (⟨x, hx.2⟩ : ↥L₀) ∈ (S ⊓ L₀).subgroupOf L₀ := hx
        have := (hWmem ⟨x, hx.2⟩).2 (by rw [hUb]; exact ⟨_, hxs, rfl⟩)
        exact this
      · obtain ⟨hxL, hxc⟩ := (hZmem x).1 hx
        refine (hWmem ⟨x, hxL⟩).2 ?_
        have : π ⟨x, hxL⟩ = 1 := by
          rw [hπker, Subgroup.mem_center_iff]
          intro g
          exact Subtype.ext (hxc g.1 g.2)
        rw [this]
        exact Subgroup.one_mem _
    · rintro x ⟨a, ha, rfl⟩
      have ha' : π a ∈ (Ub : Subgroup (↥L₀ ⧸ Subgroup.center ↥L₀)) := ha
      rw [hUb] at ha'
      obtain ⟨s, hs, hsa⟩ := ha'
      have hmem : s⁻¹ * a ∈ Subgroup.center ↥L₀ := by
        have : π s = π a := hsa
        exact (QuotientGroup.eq.1 this)
      have e : (a : G) = (s : G) * ((s⁻¹ * a : ↥L₀) : G) := by
        simp
      rw [show L₀.subtype a = (a : G) from rfl, e]
      exact Subgroup.mul_mem_sup (Subgroup.mem_subgroupOf.1 hs) ⟨s⁻¹ * a, hmem, rfl⟩
  have hK : ∀ a : ↥L₀, (a : G) ∈ Subgroup.normalizer (W : Set G) ↔
      π a ∈ Subgroup.normalizer ((Ub : Subgroup (↥L₀ ⧸ Subgroup.center ↥L₀)) : Set _) := by
    intro a
    rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
    constructor
    · intro h y
      obtain ⟨c, rfl⟩ := hπs y
      have h1 := h (c : G)
      have e1 : (a : G) * (c : G) * (a : G)⁻¹ = ((a * c * a⁻¹ : ↥L₀) : G) := by simp
      rw [e1, hWmem c, hWmem (a * c * a⁻¹), map_mul, map_mul, map_inv] at h1
      exact h1
    · intro h x
      by_cases hx : x ∈ L₀
      · have h1 := h (π ⟨x, hx⟩)
        have e1 : (a : G) * x * (a : G)⁻¹ = ((a * ⟨x, hx⟩ * a⁻¹ : ↥L₀) : G) := by simp
        rw [e1]
        have := hWmem ⟨x, hx⟩
        have h2 := hWmem (a * ⟨x, hx⟩ * a⁻¹)
        simp only at this
        rw [this, h2, map_mul, map_mul, map_inv]
        exact h1
      · have hxW : x ∉ W := fun hW' => hx (by
          obtain ⟨c, _, rfl⟩ := hW'
          exact c.2)
        have hxW' : (a : G) * x * (a : G)⁻¹ ∉ W := by
          intro hW'
          apply hx
          obtain ⟨c, _, hc⟩ := hW'
          have h3 : (a : G)⁻¹ * (c : G) * (a : G) ∈ L₀ := by
            have := hL₀conj ((a : G)⁻¹) (I.inv_mem (hL₀I a.2)) c c.2
            simpa using this
          have h4 : x = (a : G)⁻¹ * (c : G) * (a : G) := by
            have : (c : G) = (a : G) * x * (a : G)⁻¹ := hc
            rw [this]; group
          rw [h4]; exact h3
        exact ⟨fun h' => absurd h' hxW, fun h' => absurd h' hxW'⟩
  let Pt : Subgroup G := (P.comap π).map L₀.subtype
  have hPtmem : ∀ c : ↥L₀, (c : G) ∈ Pt ↔ π c ∈ P := by
    intro c
    constructor
    · rintro ⟨a, ha, hac⟩
      have : a = c := Subtype.ext hac
      subst this
      exact ha
    · intro h
      exact ⟨c, h, rfl⟩
  have hPt_le : Pt ≤ L₀ := by
    rintro x ⟨a, -, rfl⟩
    exact a.2
  have hPt_ne : Pt ≠ L₀ := by
    intro h
    apply hPtop
    rw [eq_top_iff]
    rintro y -
    obtain ⟨a, ha⟩ := hπs y
    rw [← ha]
    have haPt : (a : G) ∈ Pt := by rw [h]; exact a.2
    exact (hPtmem a).1 haPt
  have hMPt : L₀ ⊓ Mi ≤ Pt := fun x hx =>
    (hPtmem ⟨x, hx.1⟩).2 (hcomm_mem ⟨x, hx.1⟩ hx.2)
  have hNPt : L₀ ⊓ Subgroup.normalizer (((S ⊓ L₀) ⊔ Z₀ : Subgroup G) : Set G) ≤ Pt := by
    intro x hx
    rw [hW] at hx
    exact (hPtmem ⟨x, hx.1⟩).2 (hNUb ((hK ⟨x, hx.1⟩).1 hx.2))
  have hcore := normalizer_le_of_maximal_invariant hL₀I hMiI hmax hL₀conj
    (fun g hg => hZcj g (hL₀I hg)) (fun m hm => hZcj m (hMiI hm)) hS₁ hS₁Mi hPt_le hPt_ne hMPt hNPt
  have hcent : ∀ b ∈ Subgroup.normalizer
      ((Ub : Subgroup (↥L₀ ⧸ Subgroup.center ↥L₀)) : Set _), lb * b = b * lb := by
    intro b hb
    obtain ⟨a, ha⟩ := hπs b
    rw [← ha] at hb ⊢
    have h1 : (a : G) ∈ Subgroup.normalizer (W : Set G) := (hK a).2 hb
    rw [← hW] at h1
    have h2 := hcore ⟨a.2, h1⟩
    have h3 : (a : G) * l₀ = l₀ * (a : G) := hMl a h2
    show π l₁ * π a = π a * π l₁
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext h3.symm
  exact hlb1 (hR1 _ Ub.isPGroup' (Sylow.not_dvd_index Ub) lb hcent)


end CFSG.Quasithin
