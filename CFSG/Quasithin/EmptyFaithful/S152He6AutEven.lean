module

public import CFSG.Walter.PSL2Facts.Even
public import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2
public import CFSG.Walter.Defs

public section

namespace CFSG.Quasithin.He6.Aut

abbrev cm {G : Type*} [Group G] (g : G) (P : Subgroup G) : Subgroup G := P.map (MulAut.conj g).toMonoidHom

theorem mem_cm {G : Type*} [Group G] {g x : G} {P : Subgroup G} : x ∈ cm g P ↔ g⁻¹ * x * g ∈ P := by
  show x ∈ P.map (MulAut.conj g).toMonoidHom ↔ _
  rw [Subgroup.mem_map_equiv]
  simp [MulAut.conj_symm_apply]

theorem cm_mul {G : Type*} [Group G] (a b : G) (P : Subgroup G) : cm (a * b) P = cm a (cm b P) := by
  ext x
  simp only [mem_cm, mul_inv_rev, mul_assoc]

theorem cm_one {G : Type*} [Group G] (P : Subgroup G) : cm 1 P = P := by
  ext x
  simp

abbrev am {G : Type*} [Group G] (α : MulAut G) (P : Subgroup G) : Subgroup G := P.map α.toMonoidHom

theorem mem_am {G : Type*} [Group G] {α : MulAut G} {x : G} {P : Subgroup G} : x ∈ am α P ↔ α⁻¹ x ∈ P := by
  show x ∈ P.map α.toMonoidHom ↔ _
  rw [Subgroup.mem_map_equiv]
  rfl

theorem am_cm {G : Type*} [Group G] (α : MulAut G) (g : G) (P : Subgroup G) :
    am α (cm g P) = cm (α g) (am α P) := by
  ext x
  rw [mem_am, mem_cm, mem_cm, mem_am]
  have : α⁻¹ ((α g)⁻¹ * x * α g) = g⁻¹ * α⁻¹ x * g := by
    simp [map_mul, map_inv]
  rw [this]

theorem am_mul {G : Type*} [Group G] (α β : MulAut G) (P : Subgroup G) :
    am (α * β) P = am α (am β P) := by
  ext x
  rw [mem_am, mem_am, mem_am]
  simp [mul_inv_rev]

theorem am_inv_am {G : Type*} [Group G] (α : MulAut G) (P : Subgroup G) : am α⁻¹ (am α P) = P := by
  rw [← am_mul]
  have : α⁻¹ * α = 1 := inv_mul_cancel α
  rw [this]
  ext x
  rw [mem_am]
  rfl

theorem am_of_fix {G : Type*} [Group G] {S : Subgroup G} (φ : MulAut G) (h : ∀ s ∈ S, φ s = s) :
    am φ S = S := by
  have h' : ∀ s ∈ S, φ⁻¹ s = s := fun s hs => by
    calc φ⁻¹ s = φ⁻¹ (φ s) := by rw [h s hs]
      _ = s := MulAut.inv_apply_self G φ s
  ext x
  rw [mem_am]
  constructor
  · intro hx
    have e : φ⁻¹ x = x := by
      have := h _ hx
      rw [MulAut.apply_inv_self] at this
      exact this.symm
    rw [e] at hx
    exact hx
  · intro hx
    rw [h' x hx]
    exact hx

theorem cm_eq_self_of_mem {G : Type*} [Group G] {S : Subgroup G} {g : G} (hg : g ∈ S) :
    cm g S = S := by
  ext x
  rw [mem_cm]
  constructor
  · intro hx
    have := S.mul_mem (S.mul_mem hg hx) (S.inv_mem hg)
    simpa [mul_assoc] using this
  · intro hx
    exact S.mul_mem (S.mul_mem (S.inv_mem hg) hx) hg

theorem card_subtype_ne_add_one {α : Type*} [Finite α] (a : α) :
    Nat.card {x : α // x ≠ a} + 1 = Nat.card α := by
  classical
  have := Fintype.ofFinite α
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.filter_ne',
    Finset.card_erase_of_mem (Finset.mem_univ a)]
  have : 0 < Fintype.card α := Fintype.card_pos_iff.2 ⟨a⟩
  rw [Finset.card_univ] at *
  omega

theorem smul_sylow_coe {G : Type*} [Group G] (g : G) (P : Sylow 2 G) :
    ((g • P : Sylow 2 G) : Subgroup G) = cm g (P : Subgroup G) := by
  ext x
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, mem_cm]
  simp [MulAut.smul_def, mul_assoc]

theorem aut_inner_of_transitive_sylow {G : Type*} [Group G] (hG : IsSimpleGroup G)
    (IsSyl : Subgroup G → Prop)
    (hmap : ∀ (φ : MulAut G) (P : Subgroup G), IsSyl P → IsSyl (am φ P))
    {S : Subgroup G} (hS : IsSyl S) (hSn : ∃ g : G, cm g S ≠ S)
    (hab : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x)
    (hP₀ : ∃ P₀, IsSyl P₀ ∧ P₀ ≠ S)
    (htrans : ∀ P Q : Subgroup G, IsSyl P → IsSyl Q → P ≠ S → Q ≠ S → ∃ u ∈ S, cm u P = Q)
    (α : MulAut G) (hα : ∀ s ∈ S, α s = s) : ∃ l : G, ∀ g : G, α g = l * g * l⁻¹ := by
  classical
  have hαS : am α S = S := am_of_fix α hα
  have hαS' : am α⁻¹ S = S := by
    calc am α⁻¹ S = am α⁻¹ (am α S) := by rw [hαS]
      _ = S := am_inv_am α S
  obtain ⟨P₀, hP₀syl, hP₀ne⟩ := hP₀
  have hQsyl : IsSyl (am α P₀) := hmap α P₀ hP₀syl
  have hQne : am α P₀ ≠ S := by
    intro hQS
    apply hP₀ne
    have h1 : am α⁻¹ (am α P₀) = P₀ := am_inv_am α P₀
    rw [hQS, hαS'] at h1
    exact h1.symm
  obtain ⟨u₀, hu₀S, hu₀⟩ := htrans P₀ (am α P₀) hP₀syl hQsyl hP₀ne hQne
  set β : MulAut G := MulAut.conj u₀⁻¹ * α with hβ
  have hβapp : ∀ g, β g = u₀⁻¹ * α g * u₀ := fun g => by
    simp [hβ]
  have hβS : ∀ s ∈ S, β s = s := by
    intro s hs
    rw [hβapp, hα s hs]
    have := hab u₀ hu₀S s hs
    calc u₀⁻¹ * s * u₀ = u₀⁻¹ * (s * u₀) := by group
      _ = u₀⁻¹ * (u₀ * s) := by rw [this]
      _ = s := by group
  have hβP₀ : am β P₀ = P₀ := by
    rw [hβ, am_mul]
    have h1 : am (MulAut.conj u₀⁻¹) (am α P₀) = cm u₀⁻¹ (am α P₀) := rfl
    rw [h1, ← hu₀, ← cm_mul, inv_mul_cancel, cm_one]
  have hall : ∀ P : Subgroup G, IsSyl P → am β P = P := by
    intro P hP
    by_cases hPS : P = S
    · subst hPS
      exact am_of_fix β hβS
    · obtain ⟨u, huS, hu⟩ := htrans P₀ P hP₀syl hP hP₀ne hPS
      rw [← hu, am_cm, hβP₀, hβS u huS]
  let K : Subgroup G :=
    { carrier := {x | ∀ P, IsSyl P → cm x P = P}
      one_mem' := fun P _ => cm_one P
      mul_mem' := by
        intro x y hx hy P hP
        rw [cm_mul, hy P hP, hx P hP]
      inv_mem' := by
        intro x hx P hP
        have h1 := hx P hP
        calc cm x⁻¹ P = cm x⁻¹ (cm x P) := by rw [h1]
          _ = cm (x⁻¹ * x) P := (cm_mul _ _ _).symm
          _ = P := by rw [inv_mul_cancel, cm_one] }
  have hKn : K.Normal := by
    refine ⟨fun x hx h P hP => ?_⟩
    have hP' : IsSyl (cm h⁻¹ P) := hmap (MulAut.conj h⁻¹) P hP
    calc cm (h * x * h⁻¹) P = cm h (cm x (cm h⁻¹ P)) := by rw [cm_mul, cm_mul]
      _ = cm h (cm h⁻¹ P) := by rw [hx _ hP']
      _ = cm (h * h⁻¹) P := (cm_mul _ _ _).symm
      _ = P := by rw [mul_inv_cancel, cm_one]
  have hKbot : K = ⊥ := by
    rcases hG.eq_bot_or_eq_top_of_normal K with h | h
    · exact h
    · exfalso
      obtain ⟨g, hg⟩ := hSn
      apply hg
      have : g ∈ K := by rw [h]; exact Subgroup.mem_top g
      exact this S hS
  have hβid : ∀ g, β g = g := by
    intro g
    have hmem : g⁻¹ * β g ∈ K := by
      intro P hP
      have h1 : cm (β g) P = cm g P := by
        calc cm (β g) P = cm (β g) (am β P) := by rw [hall P hP]
          _ = am β (cm g P) := (am_cm β g P).symm
          _ = cm g P := hall _ (hmap (MulAut.conj g) P hP)
      calc cm (g⁻¹ * β g) P = cm g⁻¹ (cm (β g) P) := cm_mul _ _ _
        _ = cm g⁻¹ (cm g P) := by rw [h1]
        _ = cm (g⁻¹ * g) P := (cm_mul _ _ _).symm
        _ = P := by rw [inv_mul_cancel, cm_one]
    rw [hKbot, Subgroup.mem_bot] at hmem
    calc β g = g * (g⁻¹ * β g) := by group
      _ = g := by rw [hmem, mul_one]
  refine ⟨u₀, fun g => ?_⟩
  have := hβid g
  rw [hβapp] at this
  calc α g = u₀ * (u₀⁻¹ * α g * u₀) * u₀⁻¹ := by group
    _ = u₀ * g * u₀⁻¹ := by rw [this]

open scoped MatrixGroups
open CFSG.Walter

section Even

variable {f : ℕ}

theorem autInner_psl2_even (hf : 2 ≤ f) (α : MulAut PSL(2, GaloisField 2 f))
    (S : Sylow 2 PSL(2, GaloisField 2 f)) (hα : ∀ s ∈ (S : Subgroup PSL(2, GaloisField 2 f)), α s = s) :
    ∃ l : PSL(2, GaloisField 2 f), ∀ g, α g = l * g * l⁻¹ := by
  classical
  have hf0 : f ≠ 0 := by omega
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set L := PSL(2, GaloisField 2 f) with hL
  have h4 : 3 < Nat.card (GaloisField 2 f) := by
    rw [GaloisField.card 2 f hf0]
    calc 3 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hsimple : IsSimpleGroup L := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4
  let IsSyl : Subgroup L → Prop := fun P => IsPGroup 2 P ∧ ¬ 2 ∣ P.index
  have hmap : ∀ (φ : MulAut L) (P : Subgroup L), IsSyl P → IsSyl (am φ P) := by
    intro φ P hP
    refine ⟨hP.1.map φ.toMonoidHom, ?_⟩
    have : (P.map φ.toMonoidHom).index = P.index := Subgroup.index_map_equiv P (φ : L ≃* L)
    rw [this]
    exact hP.2
  have hSsyl : IsSyl (S : Subgroup L) := ⟨S.isPGroup', S.not_dvd_index⟩
  obtain ⟨hSel, hScard⟩ := psl2_even_sylow_two hf S
  have hab : ∀ x ∈ (S : Subgroup L), ∀ y ∈ (S : Subgroup L), x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hSel.toIsMulCommutative.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hcardSyl : Nat.card (Sylow 2 L) = 2 ^ f + 1 := psl2_even_card_sylow hf0
  have hSylsyl : ∀ P : Sylow 2 L, IsSyl (P : Subgroup L) := fun P => ⟨P.isPGroup', P.not_dvd_index⟩
  have hex : ∃ P : Sylow 2 L, P ≠ S := by
    have h1 : 1 < Nat.card (Sylow 2 L) := by
      rw [hcardSyl]
      have := Nat.one_le_two_pow (n := f)
      omega
    have := Finite.one_lt_card_iff_nontrivial.1 h1
    exact exists_ne S
  have hSn : ∃ g : L, cm g (S : Subgroup L) ≠ S := by
    obtain ⟨P, hP⟩ := hex
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq L S P
    refine ⟨g, fun h => hP ?_⟩
    rw [← hg]
    apply Sylow.ext
    rw [smul_sylow_coe]
    exact h
  have hTI : ∀ P : Sylow 2 L, P ≠ S → ∀ x ∈ (S : Subgroup L), x ∈ (P : Subgroup L) → x = 1 := by
    intro P hPS x hxS hxP
    by_contra hx1
    have hC : Subgroup.centralizer ({x} : Set L) = (S : Subgroup L) :=
      psl2_even_centralizer_involution hf S hxS hx1
    obtain ⟨hPel, hPcard⟩ := psl2_even_sylow_two hf P
    have hle : (P : Subgroup L) ≤ (S : Subgroup L) := by
      rw [← hC]
      intro y hy
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (congrArg Subtype.val (hPel.toIsMulCommutative.is_comm.comm ⟨x, hxP⟩ ⟨y, hy⟩)).symm
    have : (P : Subgroup L) = S :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hPcard, hScard])
    exact hPS (Sylow.ext this)
  have htrans : ∀ P Q : Subgroup L, IsSyl P → IsSyl Q → P ≠ (S : Subgroup L) →
      Q ≠ (S : Subgroup L) → ∃ u ∈ (S : Subgroup L), cm u P = Q := by
    intro P Q hP hQ hPS hQS
    let P' : Sylow 2 L := hP.1.toSylow hP.2
    let Q' : Sylow 2 L := hQ.1.toSylow hQ.2
    have hP'S : P' ≠ S := fun h => hPS (congrArg (fun R : Sylow 2 L => (R : Subgroup L)) h)
    have hQ'S : Q' ≠ S := fun h => hQS (congrArg (fun R : Sylow 2 L => (R : Subgroup L)) h)
    have hsmul_ne : ∀ u : ↥(S : Subgroup L), (u : L) • P' ≠ S := by
      intro u h
      apply hP'S
      have h1 : (u : L)⁻¹ • ((u : L) • P') = P' := inv_smul_smul _ _
      rw [h] at h1
      rw [← h1]
      apply Sylow.ext
      rw [smul_sylow_coe]
      exact cm_eq_self_of_mem ((S : Subgroup L).inv_mem u.2)
    let ev : ↥(S : Subgroup L) → {R : Sylow 2 L // R ≠ S} := fun u => ⟨(u : L) • P', hsmul_ne u⟩
    have hinj : Function.Injective ev := by
      intro u v huv
      have h1 : (u : L) • P' = (v : L) • P' := congrArg Subtype.val huv
      have h2 : ((v : L)⁻¹ * (u : L)) • P' = P' := by
        rw [mul_smul, h1, inv_smul_smul]
      have h3 : (v : L)⁻¹ * (u : L) ∈ Subgroup.normalizer (P' : Set L) := Sylow.smul_eq_iff_mem_normalizer.mp h2
      have h4 : (v : L)⁻¹ * (u : L) ∈ (S : Subgroup L) :=
        (S : Subgroup L).mul_mem ((S : Subgroup L).inv_mem v.2) u.2
      have h5 : (v : L)⁻¹ * (u : L) ∈ (S : Subgroup L) ⊓ (P' : Subgroup L) := by
        rw [← (S.isPGroup'.inf_normalizer_sylow P')]
        exact ⟨h4, h3⟩
      have h6 := hTI P' hP'S _ h4 h5.2
      apply Subtype.ext
      have : (u : L) = (v : L) := by
        calc (u : L) = (v : L) * ((v : L)⁻¹ * (u : L)) := by group
          _ = (v : L) := by rw [h6, mul_one]
      exact this
    have hcardT : Nat.card {R : Sylow 2 L // R ≠ S} = Nat.card ↥(S : Subgroup L) := by
      have h1 : Nat.card {R : Sylow 2 L // R ≠ S} + 1 = 2 ^ f + 1 := by
        rw [← hcardSyl]
        exact card_subtype_ne_add_one S
      rw [hScard]
      exact Nat.add_right_cancel h1
    have hbij := hinj.bijective_of_nat_card_le (le_of_eq hcardT)
    obtain ⟨u, hu⟩ := hbij.2 ⟨Q', hQ'S⟩
    refine ⟨u, u.2, ?_⟩
    have h1 : (u : L) • P' = Q' := congrArg Subtype.val hu
    have h2 := congrArg (fun R : Sylow 2 L => (R : Subgroup L)) h1
    rw [smul_sylow_coe] at h2
    exact h2
  obtain ⟨P, hP⟩ := hex
  exact aut_inner_of_transitive_sylow hsimple IsSyl hmap hSsyl hSn hab
    ⟨P, hSylsyl P, fun h => hP (Sylow.ext h)⟩ htrans α hα

end Even

section Transport

theorem autInner_of_equiv {G H : Type*} [Group G] [Group H] [Finite G] (e : G ≃* H)
    (h : ∀ (α : MulAut H) (S : Sylow 2 H), (∀ s ∈ (S : Subgroup H), α s = s) →
      ∃ l : H, ∀ g, α g = l * g * l⁻¹)
    (α : MulAut G) (S : Sylow 2 G) (hα : ∀ s ∈ (S : Subgroup G), α s = s) :
    ∃ l : G, ∀ g, α g = l * g * l⁻¹ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let S' : Sylow 2 H := (S.isPGroup'.map e.toMonoidHom).toSylow (by
    have h1 := Subgroup.index_map_equiv (S : Subgroup G) e
    intro hd
    apply S.not_dvd_index
    rw [← h1]
    exact hd)
  have hS' : ∀ s' ∈ (S' : Subgroup H), (MulAut.congr e α) s' = s' := by
    intro s' hs'
    obtain ⟨s, hs, rfl⟩ := hs'
    show e (α (e.symm (e s))) = e s
    rw [MulEquiv.symm_apply_apply, hα s hs]
  obtain ⟨l', hl'⟩ := h (MulAut.congr e α) S' hS'
  refine ⟨e.symm l', fun g => ?_⟩
  have h1 := hl' (e g)
  have h2 : (MulAut.congr e α) (e g) = e (α g) := by
    show e (α (e.symm (e g))) = e (α g)
    rw [MulEquiv.symm_apply_apply]
  rw [h2] at h1
  apply e.injective
  rw [h1, map_mul, map_mul, MulEquiv.apply_symm_apply, map_inv, MulEquiv.apply_symm_apply]

end Transport

end CFSG.Quasithin.He6.Aut
