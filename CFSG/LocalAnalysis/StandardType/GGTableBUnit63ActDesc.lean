module

public import CFSG.LocalAnalysis.StandardType.GGTableBUnit63Desc
public import CFSG.LocalAnalysis.StandardType.GGTableBUnit63ActCore
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitActMain

public section

namespace CFSG.StandardType.U63TB

open CFSG.StandardType CFSG.Assembly

@[expose] def IsTwoIn {L' : Type} [Group L'] (K : Subgroup L') (z : L') : Prop :=
  z ∈ K ∧ ∃ k : ℕ, z ^ 2 ^ k = 1

@[expose] def ActConclW (p : ℕ) {L' : Type} [Group L'] (K : Subgroup L')
    (A : Subgroup (MulAut L')) : Prop :=
  ∃ (H : Subgroup (MulAut L')) (W : Set L'), H ≤ A ∧ H ≠ ⊥ ∧
    (∀ n : L', MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L')) →
      ∀ h ∈ H, MulAut.conj n * h * (MulAut.conj n)⁻¹ ∈ H) ∧
    (∀ n ∈ W, ∀ a ∈ A, (n * (a n)⁻¹) ^ p = 1 ∧ ∀ a' ∈ A, a' (n * (a n)⁻¹) = n * (a n)⁻¹) ∧
    (∀ A' : Subgroup (MulAut L'), A' ≤ A → A' ≠ ⊥ →
      (∀ n ∈ W, ∀ a ∈ A', MulAut.conj n * a * (MulAut.conj n)⁻¹ ∈ A') → H ≤ A') ∧
    (∀ a ∈ A, (∀ n ∈ W, MulAut.conj n * a * (MulAut.conj n)⁻¹ = a) → a = 1) ∧
    (∀ n ∈ W, ∀ a ∈ A, MulAut.conj n * a * (MulAut.conj n)⁻¹ * a⁻¹ ∈ H) ∧
    (∀ n : L', MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L')) →
      ∃ w ∈ W, ∀ a ∈ A, ∃ z, IsTwoIn K z ∧ a (n * w⁻¹) = n * w⁻¹ * z) ∧
    (∀ n ∈ W, ∃ c ∈ Subgroup.closure {m | m ∈ W ∧ ∃ z, IsTwoIn K z ∧ m * m = z},
      ∃ z, IsTwoIn K z ∧ n = c * z) ∧
    ∀ f : MulAut L' → MulAut L', (∀ a ∈ H, f a ∈ H) →
      (∀ a ∈ H, ∀ b ∈ H, f (a * b) = f a * f b) →
      (∀ n ∈ W, ∀ a ∈ H, f (MulAut.conj n * a * (MulAut.conj n)⁻¹) =
        MulAut.conj n * f a * (MulAut.conj n)⁻¹) → ∃ c : ℕ, ∀ a ∈ H, f a = a ^ c

theorem ActConcl.toW {p : ℕ} {L' : Type} [Group L'] (K : Subgroup L') {A : Subgroup (MulAut L')}
    (h : ActConcl p A) : ActConclW p K A := by
  obtain ⟨H, W, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  have h1K : IsTwoIn K (1 : L') := ⟨K.one_mem, 0, by simp⟩
  refine ⟨H, W, h1, h2, h3, h4, h5, h6, h7, fun n hn => ?_, fun n hn => ?_, h10⟩
  · obtain ⟨w, hw, hf⟩ := h8 n hn
    exact ⟨w, hw, fun a ha => ⟨1, h1K, by rw [mul_one]; exact hf a ha⟩⟩
  · have hmono : {m | m ∈ W ∧ m * m = 1} ⊆ {m | m ∈ W ∧ ∃ z, IsTwoIn K z ∧ m * m = z} :=
      fun m hm => ⟨hm.1, 1, h1K, by rw [hm.2]⟩
    exact ⟨n, Subgroup.closure_mono hmono (h9 n hn), 1, h1K, by rw [mul_one]⟩

section ActDescent

variable {L' R : Type} [Group L'] [Finite L'] [Group R] {ψ : L' →* R}
  (hker : ψ.ker ≤ Subgroup.center L')

theorem normalizer_redSub {A : Subgroup (MulAut L')} (hAle : A ≤ presZ (twoSub ψ.ker hker))
    {n : L'} (hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L'))) :
    MulAut.conj (n : L' ⧸ twoSub ψ.ker hker) ∈
      Subgroup.normalizer ((redSub hker hAle).range : Set (MulAut (L' ⧸ twoSub ψ.ker hker))) := by
  haveI : Finite (MulAut (L' ⧸ twoSub ψ.ker hker)) :=
    Finite.of_injective (fun φ : MulAut (L' ⧸ twoSub ψ.ker hker) =>
      (φ : L' ⧸ twoSub ψ.ker hker → L' ⧸ twoSub ψ.ker hker)) DFunLike.coe_injective
  refine Subgroup.mem_normalizer_fintype fun a₁ ha₁ => ?_
  obtain ⟨b, rfl⟩ := ha₁
  have h1 := (Subgroup.mem_normalizer_iff.mp hn b.1).mp b.2
  exact ⟨⟨_, h1⟩, redSub_conj_triple hker hAle n b h1⟩

include hker in
theorem actConclW_descent (hψ : Function.Surjective ψ) (hperf : commutator L' = ⊤)
    {A : Subgroup (MulAut L')} (hA : CFSG.Open.IsElemAbelian 3 A) {I : Set (MulAut R)}
    (hAI : ∀ a ∈ A, ∃ x ∈ I, ∀ l : L', x (ψ l) = ψ (a l)) (hsc : GGTorusSelfCent 3 A)
    (H : ∀ (L₁ : Type) [Group L₁] [Finite L₁] (ψ₁ : L₁ →* R), Function.Surjective ψ₁ →
      ψ₁.ker ≤ Subgroup.center L₁ → commutator L₁ = ⊤ → Odd (Nat.card ψ₁.ker) →
      ∀ A₁ : Subgroup (MulAut L₁), CFSG.Open.IsElemAbelian 3 A₁ →
        (∀ a ∈ A₁, ∃ x ∈ I, ∀ l : L₁, x (ψ₁ l) = ψ₁ (a l)) → Nat.card A₁ = Nat.card A →
        GGTorusSelfCent 3 A₁ → ActConcl 3 A₁) :
    ActConclW 3 ψ.ker A := by
  classical
  have hAle : A ≤ presZ (twoSub ψ.ker hker) := fun a ha =>
    mem_presZ_of_ker hker fun z hz => preserves_ker (hAI a ha) hz
  have hρinj := redSub_injective hker hAle hperf
  haveI : Finite (MulAut (L' ⧸ twoSub ψ.ker hker)) :=
    Finite.of_injective (fun φ : MulAut (L' ⧸ twoSub ψ.ker hker) =>
      (φ : L' ⧸ twoSub ψ.ker hker → L' ⧸ twoSub ψ.ker hker)) DFunLike.coe_injective
  obtain ⟨H₁, W₁, hH₁A, hH₁ne, hH₁inv, hW₁, hirr₁, h6₁, h7₁, h8₁, h9₁, h10₁⟩ :=
    H (L' ⧸ twoSub ψ.ker hker) (psi1 hker) (psi1_surjective hker hψ)
      (psi1_ker_central hker) (commutator_quot hker hperf) (odd_card_ker_psi1 hker)
      (redSub hker hAle).range (isElemAbelian_range_redSub hker hAle hA)
      (redSub_hAI hker hAle hAI) (card_range_redSub hker hAle hperf)
      (selfCent_quot hker hA hAle hsc)
  set Hc : Subgroup A := H₁.comap (redSub hker hAle) with hHc
  set W : Set L' := {n | (∀ a ∈ A, (n * (a n)⁻¹) ^ 3 = 1 ∧
      ∀ a' ∈ A, a' (n * (a n)⁻¹) = n * (a n)⁻¹) ∧
      (n : L' ⧸ twoSub ψ.ker hker) ∈ W₁} with hW
  have hcomm : ∀ n ∈ W, ∀ a : A, ∃ b : A, b.1 = MulAut.conj n * a.1 * (MulAut.conj n)⁻¹ * a.1⁻¹ ∧
      redSub hker hAle b ∈ H₁ := by
    intro n hn a
    have hxp : MulAut.conj n * a.1 * (MulAut.conj n)⁻¹ * a.1⁻¹ ∈ presZ (twoSub ψ.ker hker) :=
      (presZ _).mul_mem ((presZ _).mul_mem ((presZ _).mul_mem (conjP _ n).2 (hAle a.2))
        ((presZ _).inv_mem (conjP _ n).2)) ((presZ _).inv_mem (hAle a.2))
    have hy : redHom (twoSub ψ.ker hker) ⟨_, hxp⟩ =
        MulAut.conj (n : L' ⧸ twoSub ψ.ker hker) * redSub hker hAle a *
          (MulAut.conj (n : L' ⧸ twoSub ψ.ker hker))⁻¹ * (redSub hker hAle a)⁻¹ := by
      have e : (⟨MulAut.conj n * a.1 * (MulAut.conj n)⁻¹ * a.1⁻¹, hxp⟩ : presZ (twoSub ψ.ker hker))
          = conjP _ n * ⟨a.1, hAle a.2⟩ * (conjP _ n)⁻¹ * (⟨a.1, hAle a.2⟩)⁻¹ := rfl
      rw [e, map_mul, map_mul, map_mul, map_inv, map_inv, redHom_conjP]
      rfl
    have hy₁ := h7₁ (n : L' ⧸ twoSub ψ.ker hker) hn.2 (redSub hker hAle a) ⟨a, rfl⟩
    obtain ⟨b, hb⟩ := hH₁A hy₁
    refine ⟨b, ?_, by rw [hb]; exact hy₁⟩
    have h2 : redHom (twoSub ψ.ker hker) ⟨b.1, hAle b.2⟩ =
        redHom (twoSub ψ.ker hker) ⟨_, hxp⟩ := by rw [hy, ← hb]; rfl
    exact congrArg Subtype.val (redHom_injective _ (twoSub_le_center hker) hperf h2)
  have hHA : ∀ a ∈ Hc.map A.subtype, a ∈ A := fun a ha => Subgroup.map_subtype_le _ ha
  have hHcH : ∀ a : A, a ∈ Hc → a.1 ∈ Hc.map A.subtype := fun a ha => ⟨a, ha, rfl⟩
  have hmemHc : ∀ (y : MulAut L') (hy : y ∈ Hc.map A.subtype), (⟨y, hHA y hy⟩ : A) ∈ Hc := by
    intro y hy
    obtain ⟨b, hb, rfl⟩ := hy
    exact hb
  have hconjH : ∀ n ∈ W, ∀ y ∈ Hc.map A.subtype,
      MulAut.conj n * y * (MulAut.conj n)⁻¹ ∈ Hc.map A.subtype := by
    intro n hn y hy
    obtain ⟨b, hb1, hb2⟩ := hcomm n hn ⟨y, hHA y hy⟩
    have h1 : MulAut.conj n * y * (MulAut.conj n)⁻¹ = b.1 * y := by
      rw [show b.1 = MulAut.conj n * y * (MulAut.conj n)⁻¹ * y⁻¹ from hb1]
      group
    rw [h1]
    exact (Hc.map A.subtype).mul_mem ⟨b, hb2, rfl⟩ hy
  refine ⟨Hc.map A.subtype, W, Subgroup.map_subtype_le _, ?_, ?_, fun n hn => hn.1, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  ·
    intro hbot
    obtain ⟨⟨x, hx⟩, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hH₁ne
    obtain ⟨a, ha⟩ := hH₁A hx
    have haHc : a ∈ Hc := by
      show redSub hker hAle a ∈ H₁
      rw [ha]
      exact hx
    have h1 : a.1 ∈ Hc.map A.subtype := ⟨a, haHc, rfl⟩
    rw [hbot, Subgroup.mem_bot] at h1
    have ha1 : a = 1 := Subtype.ext h1
    apply hx1
    apply Subtype.ext
    show x = 1
    rw [← ha, ha1, map_one]
  ·
    intro n hn h hh
    obtain ⟨a, haHc, rfl⟩ := hh
    have hconjA : MulAut.conj n * a.1 * (MulAut.conj n)⁻¹ ∈ A :=
      (Subgroup.mem_normalizer_iff.mp hn a.1).mp a.2
    have hnorm₁ := normalizer_redSub hker hAle hn
    refine ⟨⟨_, hconjA⟩, ?_, rfl⟩
    show redSub hker hAle ⟨_, hconjA⟩ ∈ H₁
    rw [redSub_conj_triple hker hAle n a hconjA]
    exact hH₁inv (n : L' ⧸ twoSub ψ.ker hker) hnorm₁ _ haHc
  ·
    intro A' hA'A hA'ne hinv
    set A'₁ : Subgroup (MulAut (L' ⧸ twoSub ψ.ker hker)) :=
      (A'.subgroupOf A).map (redSub hker hAle) with hA'₁
    have hA'₁le : A'₁ ≤ (redSub hker hAle).range := Subgroup.map_le_range _ _
    have hA'₁ne : A'₁ ≠ ⊥ := by
      intro hbot
      obtain ⟨⟨a, haA'⟩, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hA'ne
      have h1 : redSub hker hAle ⟨a, hA'A haA'⟩ ∈ A'₁ :=
        ⟨⟨a, hA'A haA'⟩, Subgroup.mem_subgroupOf.mpr haA', rfl⟩
      rw [hbot, Subgroup.mem_bot] at h1
      have h2 := hρinj (h1.trans (map_one (redSub hker hAle)).symm)
      have h3 : a = 1 := congrArg Subtype.val h2
      exact ha1 (Subtype.ext h3)
    have hinv₁ : ∀ w ∈ W₁, ∀ a ∈ A'₁, MulAut.conj w * a * (MulAut.conj w)⁻¹ ∈ A'₁ := by
      intro w hw a₁ ha₁
      obtain ⟨n, rfl, hn2⟩ := exists_lift_W hker hA hAle (hW₁ w hw)
      obtain ⟨a, haA', rfl⟩ := ha₁
      have haA'' : a.1 ∈ A' := Subgroup.mem_subgroupOf.mp haA'
      have h1 := hinv n ⟨hn2, hw⟩ a.1 haA''
      have h2 : MulAut.conj n * a.1 * (MulAut.conj n)⁻¹ ∈ A := hA'A h1
      exact ⟨⟨_, h2⟩, Subgroup.mem_subgroupOf.mpr h1, redSub_conj_triple hker hAle n a h2⟩
    have hirr := hirr₁ A'₁ hA'₁le hA'₁ne hinv₁
    rintro _ ⟨a, haHc, rfl⟩
    obtain ⟨b, hbA', hb⟩ := hirr (show redSub hker hAle a ∈ H₁ from haHc)
    have hba : b = a := hρinj hb
    subst hba
    exact Subgroup.mem_subgroupOf.mp hbA'
  ·
    intro a ha hfix
    have h1 : redSub hker hAle ⟨a, ha⟩ = 1 := by
      apply h6₁ _ ⟨⟨a, ha⟩, rfl⟩
      intro w hw
      obtain ⟨n, rfl, hn2⟩ := exists_lift_W hker hA hAle (hW₁ w hw)
      have h2 := hfix n ⟨hn2, hw⟩
      have h3 : MulAut.conj n * a * (MulAut.conj n)⁻¹ ∈ A := by rw [h2]; exact ha
      have h4 := redSub_conj_triple hker hAle n ⟨a, ha⟩ h3
      have h5 : (⟨MulAut.conj n * a * (MulAut.conj n)⁻¹, h3⟩ : A) = ⟨a, ha⟩ := Subtype.ext h2
      rw [h5] at h4
      exact h4.symm
    have h2 := hρinj (h1.trans (map_one (redSub hker hAle)).symm)
    exact congrArg Subtype.val h2
  ·
    intro n hn a ha
    obtain ⟨b, hb1, hb2⟩ := hcomm n hn ⟨a, ha⟩
    exact ⟨b, hb2, hb1⟩
  ·
    intro n hn
    have hn₁ := normalizer_redSub hker hAle hn
    obtain ⟨w₁, hw₁, hfix₁⟩ := h8₁ (n : L' ⧸ twoSub ψ.ker hker) hn₁
    obtain ⟨w, rfl, hw2⟩ := exists_lift_W hker hA hAle (hW₁ w₁ hw₁)
    refine ⟨w, ⟨hw2, hw₁⟩, fun a ha => ?_⟩
    have h1 := hfix₁ (redSub hker hAle ⟨a, ha⟩) ⟨⟨a, ha⟩, rfl⟩
    rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, redSub_mk] at h1
    have h2 : (n * w⁻¹)⁻¹ * a (n * w⁻¹) ∈ twoSub ψ.ker hker := QuotientGroup.eq.mp h1.symm
    exact ⟨(n * w⁻¹)⁻¹ * a (n * w⁻¹), ⟨h2.1, Nat.card L', h2.2⟩, by group⟩
  ·
    intro n hn
    have hmono : Subgroup.closure {m₁ : L' ⧸ twoSub ψ.ker hker | m₁ ∈ W₁ ∧ m₁ * m₁ = 1} ≤
        (Subgroup.closure {m | m ∈ W ∧ ∃ z, IsTwoIn ψ.ker z ∧ m * m = z} ⊔
          twoSub ψ.ker hker).map (QuotientGroup.mk' (twoSub ψ.ker hker)) := by
      rw [Subgroup.closure_le]
      rintro m₁ ⟨hm₁, hmm⟩
      obtain ⟨m, rfl, hm2⟩ := exists_lift_W hker hA hAle (hW₁ m₁ hm₁)
      have hmmZ : m * m ∈ twoSub ψ.ker hker := by
        rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul]
        exact hmm
      exact ⟨m, Subgroup.mem_sup_left (Subgroup.subset_closure
        ⟨⟨hm2, hm₁⟩, m * m, ⟨hmmZ.1, Nat.card L', hmmZ.2⟩, rfl⟩), rfl⟩
    obtain ⟨q, hq, hqn⟩ := hmono (h9₁ (n : L' ⧸ twoSub ψ.ker hker) hn.2)
    obtain ⟨c, hc, z', hz', rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hq
    have hz : (c * z')⁻¹ * n ∈ twoSub ψ.ker hker := QuotientGroup.eq.mp hqn
    have hzz := (twoSub ψ.ker hker).mul_mem hz' hz
    exact ⟨c, hc, z' * ((c * z')⁻¹ * n), ⟨hzz.1, Nat.card L', hzz.2⟩, by group⟩
  ·
    intro f hfH hfmul hfW
    have hfa : ∀ a : A, a ∈ Hc → f a.1 ∈ A := fun a ha => hHA _ (hfH _ (hHcH a ha))
    let σ : MulAut (L' ⧸ twoSub ψ.ker hker) → A := Function.invFun (redSub hker hAle)
    let f₁ : MulAut (L' ⧸ twoSub ψ.ker hker) → MulAut (L' ⧸ twoSub ψ.ker hker) := fun x =>
      if h : f (σ x).1 ∈ presZ (twoSub ψ.ker hker) then
        redHom (twoSub ψ.ker hker) ⟨f (σ x).1, h⟩ else x
    have hσ : ∀ a : A, σ (redSub hker hAle a) = a := fun a =>
      Function.leftInverse_invFun hρinj a
    have hf₁ : ∀ a : A, (ha : a ∈ Hc) →
        f₁ (redSub hker hAle a) = redSub hker hAle ⟨f a.1, hfa a ha⟩ := by
      intro a ha
      have hp : f a.1 ∈ presZ (twoSub ψ.ker hker) := hAle (hfa a ha)
      show (if h : f (σ (redSub hker hAle a)).1 ∈ presZ (twoSub ψ.ker hker) then
        redHom (twoSub ψ.ker hker) ⟨f (σ (redSub hker hAle a)).1, h⟩ else _) = _
      rw [hσ a, dif_pos hp]
      rfl
    have hA₁ : ∀ x₁ ∈ H₁, f₁ x₁ ∈ H₁ := by
      intro x₁ hx₁
      obtain ⟨a, rfl⟩ := hH₁A hx₁
      have haHc : a ∈ Hc := hx₁
      rw [hf₁ a haHc]
      exact hmemHc (f a.1) (hfH _ (hHcH a haHc))
    have hB₁ : ∀ x₁ ∈ H₁, ∀ y₁ ∈ H₁, f₁ (x₁ * y₁) = f₁ x₁ * f₁ y₁ := by
      intro x₁ hx₁ y₁ hy₁
      obtain ⟨a, rfl⟩ := hH₁A hx₁
      obtain ⟨b, rfl⟩ := hH₁A hy₁
      have haHc : a ∈ Hc := hx₁
      have hbHc : b ∈ Hc := hy₁
      rw [← map_mul, hf₁ (a * b) (Hc.mul_mem haHc hbHc), hf₁ a haHc, hf₁ b hbHc, ← map_mul]
      congr 1
      exact Subtype.ext (hfmul a.1 (hHcH a haHc) b.1 (hHcH b hbHc))
    have hC₁ : ∀ w₁ ∈ W₁, ∀ x₁ ∈ H₁, f₁ (MulAut.conj w₁ * x₁ * (MulAut.conj w₁)⁻¹) =
        MulAut.conj w₁ * f₁ x₁ * (MulAut.conj w₁)⁻¹ := by
      intro w₁ hw₁ x₁ hx₁
      obtain ⟨n, rfl, hn2⟩ := exists_lift_W hker hA hAle (hW₁ w₁ hw₁)
      have hnW : n ∈ W := ⟨hn2, hw₁⟩
      obtain ⟨a, rfl⟩ := hH₁A hx₁
      have haHc : a ∈ Hc := hx₁
      have hcn := hconjH n hnW a.1 (hHcH a haHc)
      have hcnA := hHA _ hcn
      have hbHc := hmemHc _ hcn
      have e1 := redSub_conj_triple hker hAle n a hcnA
      have hcn2 := hconjH n hnW (f a.1) (hfH _ (hHcH a haHc))
      have hcn2A := hHA _ hcn2
      have e2 := redSub_conj_triple hker hAle n ⟨f a.1, hfa a haHc⟩ hcn2A
      rw [← e1, hf₁ _ hbHc, hf₁ a haHc, ← e2]
      congr 1
      exact Subtype.ext (hfW n hnW a.1 (hHcH a haHc))
    obtain ⟨c, hc⟩ := h10₁ f₁ hA₁ hB₁ hC₁
    refine ⟨c, fun a ha => ?_⟩
    have haA : a ∈ A := hHA a ha
    have haHc : (⟨a, haA⟩ : A) ∈ Hc := hmemHc a ha
    have h1 := hc _ haHc
    rw [hf₁ ⟨a, haA⟩ haHc] at h1
    have h2 : redSub hker hAle ⟨f a, hfa ⟨a, haA⟩ haHc⟩ =
        redSub hker hAle ((⟨a, haA⟩ : A) ^ c) := by
      rw [h1, map_pow]
    exact congrArg Subtype.val (hρinj h2)

end ActDescent

end CFSG.StandardType.U63TB

end
