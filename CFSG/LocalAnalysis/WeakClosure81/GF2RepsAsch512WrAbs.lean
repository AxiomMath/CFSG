module

public import CFSG.HardMathSupport.Foote.E27.LieTwo.SylowNormal

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Asch80Wr

open Subgroup

section Unique

variable {G : Type*} [Group G]

theorem le_or_le_of_relIndex_eq_two {A C P : Subgroup G} (hAC : A ≤ C) (hCP : C ≤ P)
    (hA : A.relIndex P = 2) : C ≤ A ∨ P ≤ C := by
  have h := relIndex_mul_relIndex A C P hAC hCP
  rw [hA] at h
  rcases Nat.prime_two.eq_one_or_self_of_dvd _ (Dvd.intro _ h) with h1 | h2
  · exact Or.inl (relIndex_eq_one.mp h1)
  · rw [h2] at h
    exact Or.inr (relIndex_eq_one.mp (by omega))

theorem eq_of_isCommutative_of_relIndex_two {P A B : Subgroup G} [Finite P] (hAP : A ≤ P)
    (hBP : B ≤ P) (hA : IsMulCommutative ↥A) (hB : IsMulCommutative ↥B) (hAi : A.relIndex P = 2)
    (hBi : B.relIndex P = 2)
    (hZ : 4 * Nat.card ↥(P ⊓ centralizer (P : Set G)) < Nat.card P) : A = B := by
  by_contra hne
  have hcomm : ∀ {H : Subgroup G}, IsMulCommutative ↥H → ∀ {a b : G}, a ∈ H → b ∈ H →
      a * b = b * a := by
    intro H hH a b ha hb
    have := hH.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩
    exact congrArg Subtype.val this
  have hcent : A ⊓ B ≤ P ⊓ centralizer (P : Set G) := by
    intro x hx
    obtain ⟨hxA, hxB⟩ := mem_inf.mp hx
    refine mem_inf.mpr ⟨hAP hxA, ?_⟩
    set C := centralizer ({x} : Set G) ⊓ P with hC
    have hAC : A ≤ C := fun a ha =>
      mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr (hcomm hA ha hxA), hAP ha⟩
    have hBC : B ≤ C := fun b hb =>
      mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr (hcomm hB hb hxB), hBP hb⟩
    have hPC : P ≤ C := by
      rcases le_or_le_of_relIndex_eq_two hAC inf_le_right hAi with hCA | hPC
      · rcases le_or_le_of_relIndex_eq_two hBC inf_le_right hBi with hCB | hPC
        · exact absurd (le_antisymm (hAC.trans hCB) (hBC.trans hCA)) hne
        · exact hPC
      · exact hPC
    refine mem_centralizer_iff.mpr fun y hy => ?_
    exact mem_centralizer_singleton_iff.mp (mem_inf.mp (hPC hy)).1
  have : Finite ↥(P ⊓ centralizer (P : Set G)) :=
    Finite.of_injective (inclusion inf_le_left) (inclusion_injective _)
  have hI : (A ⊓ B).relIndex P ≤ 4 := by
    have := relIndex_inf_le (H := A) (K := B) (L := P)
    rw [hAi, hBi] at this
    exact this
  have hcard := relIndex_mul_card (H := A ⊓ B) (K := P)
  have hle : Nat.card ↥(A ⊓ B ⊓ P) ≤ Nat.card ↥(P ⊓ centralizer (P : Set G)) :=
    card_le_of_le (inf_le_left.trans hcent)
  have := Nat.mul_le_mul hI hle
  omega

end Unique

section Reduction

variable {Y : Type*} [Group Y]

theorem le_normalizer_inf_of_normal {E T : Subgroup Y} [hE : E.Normal] :
    T ≤ normalizer ((T ⊓ E : Subgroup Y) : Set Y) :=
  (le_inf le_normalizer (by rw [normalizer_eq_top_iff.mpr hE]; exact le_top)).trans
    inf_normalizer_le_normalizer_inf

theorem normalizer_le_normalizer_inf_centralizer (H : Subgroup Y) :
    normalizer (H : Set Y) ≤ normalizer ((H ⊓ centralizer (H : Set Y) : Subgroup Y) : Set Y) := by
  refine le_trans (le_inf le_rfl ?_) inf_normalizer_le_normalizer_inf
  intro g hg
  rw [mem_normalizer_iff] at hg ⊢
  have hg' : ∀ h, h ∈ H ↔ g⁻¹ * h * g ∈ H := fun h => by
    rw [hg (g⁻¹ * h * g)]
    group
  intro x
  simp only [mem_centralizer_iff, SetLike.mem_coe]
  constructor
  · intro hx h hh
    have h1 := hx (g⁻¹ * h * g) ((hg' h).mp hh)
    calc h * (g * x * g⁻¹) = g * ((g⁻¹ * h * g) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * h * g)) * g⁻¹ := by rw [h1]
      _ = g * x * g⁻¹ * h := by group
  · intro hx h hh
    have h1 := hx (g * h * g⁻¹) ((hg h).mp hh)
    have h2 : g * (h * x) * g⁻¹ = g * (x * h) * g⁻¹ := by
      calc g * (h * x) * g⁻¹ = g * h * g⁻¹ * (g * x * g⁻¹) := by group
        _ = g * x * g⁻¹ * (g * h * g⁻¹) := h1
        _ = g * (x * h) * g⁻¹ := by group
    simpa using h2

theorem normalizer_ne_top_of_le {E C : Subgroup Y} (hEs : IsSimpleGroup ↥E)
    (hE2 : ¬ IsPGroup 2 ↥E) (hCE : C ≤ E) (hC : IsPGroup 2 C) (hC1 : C ≠ ⊥) :
    normalizer (C : Set Y) ≠ ⊤ := by
  intro htop
  have hCn : C.Normal := normalizer_eq_top_iff.mp htop
  have := hCn.subgroupOf E
  rcases hEs.eq_bot_or_eq_top_of_normal (C.subgroupOf E) with h | h
  · exact hC1 ((subgroupOf_eq_bot.mp h).eq_bot_of_le hCE)
  · exact hE2 (hC.to_le (subgroupOf_eq_top.mp h))

theorem not_exists_max_of_normalizers [Finite Y] {E : Subgroup Y} [E.Normal]
    (hEs : IsSimpleGroup ↥E) (hE2 : ¬ IsPGroup 2 ↥E) (S : Sylow 2 Y) {C₁ C₂ : Subgroup Y}
    (hC₁ : C₁ ≤ (S : Subgroup Y) ⊓ E) (hC₂ : C₂ ≤ (S : Subgroup Y) ⊓ E) (h1 : C₁ ≠ ⊥)
    (h2 : C₂ ≠ ⊥)
    (hN₁ : normalizer (((S : Subgroup Y) ⊓ E : Subgroup Y) : Set Y) ≤ normalizer (C₁ : Set Y))
    (hN₂ : normalizer (((S : Subgroup Y) ⊓ E : Subgroup Y) : Set Y) ≤ normalizer (C₂ : Set Y))
    (hgen : E ≤ normalizer (C₁ : Set Y) ⊔ normalizer (C₂ : Set Y)) :
    ¬ ∃ M : Subgroup Y, M < ⊤ ∧ ∀ X : Subgroup Y, (S : Subgroup Y) ≤ X → X < ⊤ → X ≤ M := by
  rintro ⟨M, hMtop, hM⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set T₀ := (S : Subgroup Y) ⊓ E with hT₀
  have hST : (S : Subgroup Y) ≤ normalizer (T₀ : Set Y) := le_normalizer_inf_of_normal
  have hS2 : IsPGroup 2 T₀ := S.isPGroup'.to_inf_left
  have hNM : ∀ C : Subgroup Y, C ≤ T₀ → C ≠ ⊥ →
      normalizer (T₀ : Set Y) ≤ normalizer (C : Set Y) → normalizer (C : Set Y) ≤ M := by
    intro C hC hC1 hN
    refine hM _ (hST.trans hN) (lt_top_iff_ne_top.mpr ?_)
    exact normalizer_ne_top_of_le hEs hE2 (hC.trans inf_le_right) (hS2.to_le hC) hC1
  have hEM : E ≤ M := hgen.trans (sup_le (hNM C₁ hC₁ h1 hN₁) (hNM C₂ hC₂ h2 hN₂))
  have hNT₀M : normalizer (T₀ : Set Y) ≤ M := hN₁.trans (hNM C₁ hC₁ h1 hN₁)
  obtain ⟨P, hP⟩ := CFSG.HardMathSupport.Foote.E27.exists_sylow_subgroupOf_eq E S
  have hPmap : (P : Subgroup E).map E.subtype = T₀ := by
    rw [hP, subgroupOf_map_subtype]
  have hfr := Sylow.normalizer_sup_eq_top P
  rw [hPmap] at hfr
  exact hMtop.ne (top_le_iff.mp (hfr ▸ sup_le hNT₀M hEM))

@[expose] def WrModel (K : Type*) [Group K] : Prop :=
  ∃ (P₀ : Sylow 2 K) (A₀ : Subgroup K), A₀ ≤ P₀ ∧ IsMulCommutative ↥A₀ ∧ A₀.relIndex P₀ = 2 ∧
    4 * Nat.card ↥((P₀ : Subgroup K) ⊓ centralizer ((P₀ : Subgroup K) : Set K)) < Nat.card P₀ ∧
    normalizer (((P₀ : Subgroup K) ⊓ centralizer ((P₀ : Subgroup K) : Set K) : Subgroup K) :
      Set K) ⊔
      normalizer (A₀ : Set K) = ⊤ ∧ (P₀ : Subgroup K) ≠ ⊤

theorem map_inf_centralizer_of_injective {K : Type*} [Group K] {φ : K →* Y}
    (hφ : Function.Injective φ) (P : Subgroup K) :
    (P ⊓ centralizer (P : Set K)).map φ =
      P.map φ ⊓ centralizer ((P.map φ : Subgroup Y) : Set Y) := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨hxP, hxC⟩ := mem_inf.mp hx
    refine mem_inf.mpr ⟨⟨x, hxP, rfl⟩, mem_centralizer_iff.mpr ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, mem_centralizer_iff.mp hxC y hy]
  · intro y hy
    obtain ⟨⟨x, hxP, rfl⟩, hyC⟩ := mem_inf.mp hy
    refine ⟨x, mem_inf.mpr ⟨hxP, mem_centralizer_iff.mpr fun z hz => hφ ?_⟩, rfl⟩
    rw [map_mul, map_mul]
    exact mem_centralizer_iff.mp hyC (φ z) ⟨z, hz, rfl⟩

theorem exists_map_conj_eq {K : Type*} [Group K] [Finite K] {p : ℕ} [Fact p.Prime]
    (P Q : Sylow p K) : ∃ g : K, (P : Subgroup K).map (MulAut.conj g).toMonoidHom = Q := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K P Q
  refine ⟨g, ?_⟩
  rw [← hg, Sylow.coe_subgroup_smul, pointwise_smul_def]
  rfl

theorem not_exists_max_of_model [Finite Y] {E : Subgroup Y} [E.Normal] (hEs : IsSimpleGroup ↥E)
    (S : Sylow 2 Y) {K : Type*} [Group K] (e : ↥E ≃* K) (hK : WrModel K) :
    ¬ ∃ M : Subgroup Y, M < ⊤ ∧ ∀ X : Subgroup Y, (S : Subgroup Y) ≤ X → X < ⊤ → X ≤ M := by
  obtain ⟨P₀, A₀, hA₀P, hA₀, hA₀i, hZ, hgen, hP₀top⟩ := hK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite K := Finite.of_equiv _ e.toEquiv
  set Z₀ := (P₀ : Subgroup K) ⊓ centralizer ((P₀ : Subgroup K) : Set K) with hZ₀
  have hE2 : ¬ IsPGroup 2 ↥E := by
    intro h
    have hK2 : IsPGroup 2 (⊤ : Subgroup K) := (h.of_equiv e).of_equiv Subgroup.topEquiv.symm
    exact hP₀top (P₀.is_maximal' hK2 le_top).symm
  obtain ⟨P, hP⟩ := CFSG.HardMathSupport.Foote.E27.exists_sylow_subgroupOf_eq E S
  obtain ⟨g, hg₀⟩ := exists_map_conj_eq P₀ (P.mapSurjective (f := e.toMonoidHom) e.surjective)
  have hg : (P₀ : Subgroup K).map (MulAut.conj g).toMonoidHom =
      (P : Subgroup E).map e.toMonoidHom := hg₀
  set φ : K →* Y := E.subtype.comp (e.symm.toMonoidHom.comp (MulAut.conj g).toMonoidHom) with hφ
  have hφinj : Function.Injective φ :=
    E.subtype_injective.comp (e.symm.injective.comp (MulAut.conj g).injective)
  have hPe : ((P : Subgroup E).map e.toMonoidHom).map e.symm.toMonoidHom = (P : Subgroup E) := by
    rw [map_map, show e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id _ from
      MonoidHom.ext fun x => e.symm_apply_apply x, map_id]
  have hφP : (P₀ : Subgroup K).map φ = (S : Subgroup Y) ⊓ E := by
    have h1 : (P₀ : Subgroup K).map φ = (((P₀ : Subgroup K).map
        (MulAut.conj g).toMonoidHom).map e.symm.toMonoidHom).map E.subtype := by
      rw [hφ, map_map, map_map]
      rfl
    rw [h1, hg, hPe, hP, subgroupOf_map_subtype]
  have hcardZ : Nat.card ↥(Z₀.map φ) = Nat.card Z₀ := card_map_of_injective hφinj
  have hcardP : Nat.card ↥((P₀ : Subgroup K).map φ) = Nat.card P₀ := card_map_of_injective hφinj
  set T₀ := (S : Subgroup Y) ⊓ E with hT₀
  have hZT : Z₀.map φ = T₀ ⊓ centralizer (T₀ : Set Y) := by
    rw [hZ₀, map_inf_centralizer_of_injective hφinj, hφP]
  have hP₀bot : (P₀ : Subgroup K) ≠ ⊥ := by
    intro h
    rw [h, relIndex_bot_right] at hA₀i
    exact absurd hA₀i (by norm_num)
  have hZ₀bot : Z₀ ≠ ⊥ := by
    have : Nontrivial ↥(P₀ : Subgroup K) := (nontrivial_iff_ne_bot _).mpr hP₀bot
    have := P₀.isPGroup'.center_nontrivial
    obtain ⟨z, hz1⟩ := exists_ne (1 : center ↥(P₀ : Subgroup K))
    intro hbot
    have hzZ : ((z : ↥P₀) : K) ∈ Z₀ := by
      refine mem_inf.mpr ⟨(z : ↥P₀).2, mem_centralizer_iff.mpr fun y hy => ?_⟩
      have := mem_center_iff.mp z.2 ⟨y, hy⟩
      exact congrArg Subtype.val this
    rw [hbot, mem_bot] at hzZ
    exact hz1 (Subtype.ext (Subtype.ext hzZ))
  have hA₀bot : A₀ ≠ ⊥ := by
    intro h
    rw [h, relIndex_bot_left] at hA₀i
    have : 0 < Nat.card Z₀ := Nat.card_pos
    omega
  have hC₂ : A₀.map φ ≤ T₀ := hφP ▸ map_mono hA₀P
  refine not_exists_max_of_normalizers hEs hE2 S (C₁ := Z₀.map φ) (C₂ := A₀.map φ)
    (hZT ▸ inf_le_left) hC₂
    ((map_eq_bot_iff_of_injective _ hφinj).not.mpr hZ₀bot)
    ((map_eq_bot_iff_of_injective _ hφinj).not.mpr hA₀bot)
    (hZT ▸ normalizer_le_normalizer_inf_centralizer T₀) ?_ ?_
  ·
    intro y hy
    rw [mem_normalizer_iff_map_conj_eq] at hy ⊢
    rw [← hT₀] at hy
    have : Finite ↥T₀ := inferInstance
    refine eq_of_isCommutative_of_relIndex_two (P := T₀) ?_ hC₂ ?_ ?_ ?_ ?_ ?_
    · exact hy ▸ map_mono hC₂
    · have := hA₀
      have : IsMulCommutative ↥(A₀.map φ) := inferInstance
      exact inferInstance
    · have := hA₀
      exact inferInstance
    · rw [← hy, relIndex_map_map_of_injective _ _ (MulAut.conj y).injective, ← hφP,
        relIndex_map_map_of_injective _ _ hφinj, hA₀i]
    · rw [← hφP, relIndex_map_map_of_injective _ _ hφinj, hA₀i]
    · rw [← hZT, hcardZ, ← hφP, hcardP]
      exact hZ
  ·
    intro x hx
    have hxφ : x ∈ (⊤ : Subgroup K).map φ :=
      ⟨(MulAut.conj g).symm (e ⟨x, hx⟩), mem_top _, by simp [hφ, mul_assoc]⟩
    rw [← hgen, Subgroup.map_sup] at hxφ
    exact sup_le_sup (le_normalizer_map φ) (le_normalizer_map φ) hxφ

end Reduction

end CFSG.LocalAnalysis.WeakClosure81.Asch80Wr
