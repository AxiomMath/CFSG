module

public import CFSG.Goldschmidt.Steps.G310Basic

public section

namespace CFSG.RankThree.PartTwo.Sec13.F135Last

open CFSG Subgroup

theorem sl1_si_sylow_conj {X : Type*} [Group X] [Finite X] (A R₁ R₂ : Subgroup X) (q : ℕ)
    (hq : q.Prime) (hR₁A : R₁ ≤ A) (hR₂A : R₂ ≤ A) (hR₁ : IsPGroup q R₁) (hR₂ : IsPGroup q R₂)
    (h₁ : ¬ q ∣ R₁.relIndex A) (h₂ : ¬ q ∣ R₂.relIndex A) :
    ∃ g ∈ A, ∀ y : X, y ∈ R₂ ↔ g * y * g⁻¹ ∈ R₁ := by
  haveI : Fact (Nat.Prime q) := ⟨hq⟩
  haveI : Finite (Sylow q A) := Sylow.finite_of_finiteIndex (Classical.arbitrary (Sylow q A))
  have hP₁ : IsPGroup q (R₁.subgroupOf A) :=
    hR₁.of_injective (Subgroup.subgroupOfEquivOfLe hR₁A).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hR₁A).injective
  have hP₂ : IsPGroup q (R₂.subgroupOf A) :=
    hR₂.of_injective (Subgroup.subgroupOfEquivOfLe hR₂A).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hR₂A).injective
  let S₁ : Sylow q A := hP₁.toSylow h₁
  let S₂ : Sylow q A := hP₂.toSylow h₂
  have hmem₁ : ∀ w : A, w ∈ S₁ ↔ (w : X) ∈ R₁ := fun w =>
    (IsPGroup.mem_toSylow hP₁ h₁).trans Subgroup.mem_subgroupOf
  have hmem₂ : ∀ w : A, w ∈ S₂ ↔ (w : X) ∈ R₂ := fun w =>
    (IsPGroup.mem_toSylow hP₂ h₂).trans Subgroup.mem_subgroupOf
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (↥A) S₂ S₁
  have fwd : ∀ (h w : A) (P : Sylow q A), w ∈ P → MulAut.conj h w ∈ h • P := by
    intro h w P hw
    show MulAut.conj h w ∈ ((h • P : Sylow q A) : Subgroup A)
    rw [Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul _ _ _ hw
  have bwd : ∀ (h w : A) (P : Sylow q A), w ∈ h • P → (MulAut.conj h)⁻¹ w ∈ P := by
    intro h w P hw
    have hw' : w ∈ ((h • P : Sylow q A) : Subgroup A) := hw
    rw [Sylow.coe_subgroup_smul] at hw'
    exact Subgroup.mem_pointwise_smul_iff_inv_smul_mem.mp hw'
  have hval : ∀ (h w : A), ((MulAut.conj h w : A) : X) = (h : X) * (w : X) * (h : X)⁻¹ := by
    intro h w
    simp [MulAut.conj_apply]
  have hval' : ∀ (h w : A), (((MulAut.conj h)⁻¹ w : A) : X) = (h : X)⁻¹ * (w : X) * (h : X) := by
    intro h w
    simp [MulAut.conj_inv_apply]
  refine ⟨(g : X), g.2, fun y => ?_⟩
  constructor
  · intro hy
    have hyA : y ∈ A := hR₂A hy
    have h1 : (⟨y, hyA⟩ : A) ∈ S₂ := (hmem₂ _).mpr hy
    have h2 : MulAut.conj g ⟨y, hyA⟩ ∈ S₁ := by
      rw [← hg]
      exact fwd g _ S₂ h1
    have h3 := (hmem₁ _).mp h2
    rw [hval] at h3
    exact h3
  · intro hy
    have hyA : y ∈ A := by
      have h1 : (g : X) * y * (g : X)⁻¹ ∈ A := hR₁A hy
      have h2 := A.mul_mem (A.mul_mem (A.inv_mem g.2) h1) g.2
      have e : (g : X)⁻¹ * ((g : X) * y * (g : X)⁻¹) * (g : X) = y := by group
      rwa [e] at h2
    have h1 : (⟨(g : X) * y * (g : X)⁻¹, hR₁A hy⟩ : A) ∈ S₁ := (hmem₁ _).mpr hy
    have h2 : (MulAut.conj g)⁻¹ ⟨(g : X) * y * (g : X)⁻¹, hR₁A hy⟩ ∈ S₂ := by
      rw [← hg] at h1
      exact bwd g _ S₂ h1
    have h3 := (hmem₂ _).mp h2
    have h4 : (g : X)⁻¹ * ((g : X) * y * (g : X)⁻¹) * (g : X) ∈ R₂ := by
      rw [hval'] at h3
      exact h3
    have e : (g : X)⁻¹ * ((g : X) * y * (g : X)⁻¹) * (g : X) = y := by group
    rwa [e] at h4

theorem sl1_frattini_argument {X : Type*} [Group X] [Finite X] (J A R : Subgroup X) (q : ℕ)
    (hq : q.Prime) (hAJ : A ≤ J) (hAn : ∀ j ∈ J, ∀ a ∈ A, j * a * j⁻¹ ∈ A) (hRA : R ≤ A)
    (hRq : IsPGroup q R) (hRsyl : ¬ q ∣ R.relIndex A) :
    ∀ j ∈ J, ∃ a ∈ A, a * j ∈ Subgroup.normalizer (R : Set X) := by
  intro j hj
  have hinj : Function.Injective (MulAut.conj j).toMonoidHom := (MulAut.conj j).injective
  have hfapp : ∀ x : X, (MulAut.conj j).toMonoidHom x = j * x * j⁻¹ := fun x => rfl
  have hAmap : A.map (MulAut.conj j).toMonoidHom = A := by
    apply le_antisymm
    · rintro _ ⟨a, ha, rfl⟩
      rw [hfapp]
      exact hAn j hj a ha
    · intro x hx
      refine Subgroup.mem_map.mpr ⟨j⁻¹ * x * j⁻¹⁻¹, hAn j⁻¹ (J.inv_mem hj) x hx, ?_⟩
      rw [hfapp]
      group
  have hR₂A : R.map (MulAut.conj j).toMonoidHom ≤ A := by
    rintro _ ⟨r, hr, rfl⟩
    rw [hfapp]
    exact hAn j hj r (hRA hr)
  have hR₂syl : ¬ q ∣ (R.map (MulAut.conj j).toMonoidHom).relIndex A := by
    have h := Subgroup.relIndex_map_map_of_injective (f := (MulAut.conj j).toMonoidHom) R A hinj
    rw [hAmap] at h
    rw [h]
    exact hRsyl
  obtain ⟨g, hgA, hg⟩ := sl1_si_sylow_conj A R (R.map (MulAut.conj j).toMonoidHom) q hq hRA hR₂A
    hRq (hRq.map _) hRsyl hR₂syl
  refine ⟨g, hgA, ?_⟩
  refine Subgroup.mem_normalizer_iff.mpr fun x => ?_
  show x ∈ R ↔ g * j * x * (g * j)⁻¹ ∈ R
  have e : g * j * x * (g * j)⁻¹ = g * (MulAut.conj j).toMonoidHom x * g⁻¹ := by
    rw [hfapp]
    group
  rw [e, ← hg ((MulAut.conj j).toMonoidHom x)]
  exact (Subgroup.mem_map_iff_mem hinj).symm

theorem sl1_conj_sup {M : Type*} [Group M] (R : Subgroup M) [R.Normal] (c g : M)
    (hg : g * c * g⁻¹ ∈ R ⊔ Subgroup.zpowers c) :
    ∀ x ∈ R ⊔ Subgroup.zpowers c, g * x * g⁻¹ ∈ R ⊔ Subgroup.zpowers c := by
  have hle : R ⊔ Subgroup.zpowers c ≤
      (R ⊔ Subgroup.zpowers c).comap (MulAut.conj g).toMonoidHom := by
    refine sup_le ?_ ?_
    · intro r hr
      exact Subgroup.mem_comap.mpr (Subgroup.mem_sup_left (Subgroup.Normal.conj_mem ‹R.Normal› r hr g))
    · rw [Subgroup.zpowers_le]
      exact Subgroup.mem_comap.mpr hg
  intro x hx
  exact Subgroup.mem_comap.mp (hle hx)

theorem sl1_conj_zpowers {M : Type*} [Group M] (c g : M) (hg : g * c * g⁻¹ = c) :
    ∀ y ∈ Subgroup.zpowers c, g * y * g⁻¹ ∈ Subgroup.zpowers c := by
  have hle : Subgroup.zpowers c ≤ (Subgroup.zpowers c).comap (MulAut.conj g).toMonoidHom := by
    rw [Subgroup.zpowers_le, Subgroup.mem_comap]
    show g * c * g⁻¹ ∈ Subgroup.zpowers c
    rw [hg]
    exact Subgroup.mem_zpowers c
  intro y hy
  exact Subgroup.mem_comap.mp (hle hy)

theorem sl1_mem_normalizer_of {M : Type*} [Group M] (K : Subgroup M) {g : M}
    (h1 : ∀ y ∈ K, g * y * g⁻¹ ∈ K) (h2 : ∀ y ∈ K, g⁻¹ * y * g⁻¹⁻¹ ∈ K) :
    g ∈ Subgroup.normalizer (K : Set M) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · exact h1 y
  · intro hy
    have h := h2 _ hy
    have e : g⁻¹ * (g * y * g⁻¹) * g⁻¹⁻¹ = y := by group
    rwa [e] at h

theorem sl1_mem_sup {M : Type*} [Group M] (R : Subgroup M) [R.Normal] (c : M) {a : M}
    (ha : a ∈ R ⊔ Subgroup.zpowers c) : ∃ r ∈ R, ∃ k : ℤ, a = r * c ^ k := by
  obtain ⟨r, hr, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp ha
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  exact ⟨r, hr, k, rfl⟩

theorem sl1_mem_sup_of_conj {M : Type*} [Group M] (R : Subgroup M) (c g : M)
    (hg : g * c * g⁻¹ * c⁻¹ ∈ R) : g * c * g⁻¹ ∈ R ⊔ Subgroup.zpowers c := by
  have e : g * c * g⁻¹ = (g * c * g⁻¹ * c⁻¹) * c := by group
  rw [e]
  exact mul_mem (Subgroup.mem_sup_left hg) (Subgroup.mem_sup_right (Subgroup.mem_zpowers c))

theorem exists_sigma {M : Type*} [Group M] [Finite M] {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3)
    (c : M) (hc : orderOf c = 3) (E : Subgroup M) (hE : IsPGroup p E) (R : Subgroup M) [R.Normal]
    (hEc : ∀ e ∈ E, e * c = c * e) (hR : ¬ p ∣ Nat.card R) :
    ∃ S : Subgroup M, S ≤ R ⊔ Subgroup.zpowers c ∧ IsPGroup 3 S ∧
      ¬ 3 ∣ S.relIndex (R ⊔ Subgroup.zpowers c) ∧ c ∈ S ∧ E ≤ normalizer (S : Set M) := by
  classical
  have hc3 : IsPGroup 3 (Subgroup.zpowers c) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hc, pow_one])
  have hRel : R.relIndex (R ⊔ Subgroup.zpowers c) ∣ 3 := by
    rw [Subgroup.relIndex_sup_left]
    have h := Subgroup.relIndex_dvd_card R (Subgroup.zpowers c)
    rwa [Nat.card_zpowers, hc] at h
  have hcard : Nat.card (R ⊔ Subgroup.zpowers c : Subgroup M) =
      R.relIndex (R ⊔ Subgroup.zpowers c) * Nat.card R := by
    have h := Subgroup.relIndex_mul_card R (R ⊔ Subgroup.zpowers c)
    rw [inf_eq_left.mpr (le_sup_left : R ≤ R ⊔ Subgroup.zpowers c)] at h
    exact h.symm
  have hpH : ¬ p ∣ Nat.card (R ⊔ Subgroup.zpowers c : Subgroup M) := by
    rw [hcard]
    intro h
    rcases (Nat.Prime.dvd_mul hp).mp h with h1 | h1
    · exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (dvd_trans h1 hRel))
    · exact hR h1
  have hEc' : ∀ e ∈ E, e * c * e⁻¹ = c := fun e he => by
    rw [hEc e he, mul_inv_cancel_right]
  have hEH : E ≤ Subgroup.normalizer ((R ⊔ Subgroup.zpowers c : Subgroup M) : Set M) := by
    intro e he
    have h1 : ∀ x ∈ R ⊔ Subgroup.zpowers c, e * x * e⁻¹ ∈ R ⊔ Subgroup.zpowers c :=
      sl1_conj_sup R c e (by rw [hEc' e he]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers c))
    have h2 : ∀ x ∈ R ⊔ Subgroup.zpowers c, e⁻¹ * x * e⁻¹⁻¹ ∈ R ⊔ Subgroup.zpowers c :=
      sl1_conj_sup R c e⁻¹
        (by rw [hEc' e⁻¹ (E.inv_mem he)]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers c))
    exact sl1_mem_normalizer_of _ h1 h2
  have hEZ : E ≤ Subgroup.normalizer ((Subgroup.zpowers c : Subgroup M) : Set M) := by
    intro e he
    exact sl1_mem_normalizer_of _ (sl1_conj_zpowers c e (hEc' e he))
      (sl1_conj_zpowers c e⁻¹ (hEc' e⁻¹ (E.inv_mem he)))
  obtain ⟨S, hfus, hcT, hES⟩ := CFSG.Goldschmidt.G310.exists_invariant_sylow_containing
    hp Nat.prime_three hE hpH hEH le_sup_right hc3 hEZ
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P, hP⟩ := CFSG.Goldschmidt.G310.exists_sylow_of_fusionIsSylowIn hfus
  obtain ⟨hS_le, hS3, -⟩ := hfus
  have hSP : S.subgroupOf (R ⊔ Subgroup.zpowers c) =
      (P : Subgroup ↥(R ⊔ Subgroup.zpowers c)) := by
    rw [← hP]
    exact Subgroup.comap_map_eq_self_of_injective (R ⊔ Subgroup.zpowers c).subtype_injective _
  have hnd : ¬ 3 ∣ S.relIndex (R ⊔ Subgroup.zpowers c) := by
    rw [Subgroup.relIndex, hSP]
    exact P.not_dvd_index
  exact ⟨S, hS_le, hS3, hnd, hcT (Subgroup.mem_zpowers c), hES⟩

theorem frattini_cover {M : Type*} [Group M] [Finite M] (R I S : Subgroup M) [R.Normal] (c : M)
    (hRI : R ≤ I) (hIc : ∀ x ∈ I, x * c * x⁻¹ * c⁻¹ ∈ R)
    (hS_le : S ≤ R ⊔ Subgroup.zpowers c) (hS3 : IsPGroup 3 S)
    (hSidx : ¬ 3 ∣ S.relIndex (R ⊔ Subgroup.zpowers c)) (hcS : c ∈ S) :
    ∀ g ∈ I, ∃ r ∈ R, ∃ n ∈ I ⊓ normalizer (S : Set M), g = r * n := by
  have hIN : I ≤ Subgroup.normalizer ((R ⊔ Subgroup.zpowers c : Subgroup M) : Set M) := by
    intro x hx
    have hxc : ∀ y ∈ I, y * c * y⁻¹ ∈ R ⊔ Subgroup.zpowers c := fun y hy =>
      sl1_mem_sup_of_conj R c y (hIc y hy)
    exact sl1_mem_normalizer_of _ (sl1_conj_sup R c x (hxc x hx))
      (sl1_conj_sup R c x⁻¹ (hxc x⁻¹ (I.inv_mem hx)))
  have hJN : I ⊔ (R ⊔ Subgroup.zpowers c) ≤
      Subgroup.normalizer ((R ⊔ Subgroup.zpowers c : Subgroup M) : Set M) :=
    sup_le hIN Subgroup.le_normalizer
  have hAn : ∀ j ∈ I ⊔ (R ⊔ Subgroup.zpowers c), ∀ a ∈ R ⊔ Subgroup.zpowers c,
      j * a * j⁻¹ ∈ R ⊔ Subgroup.zpowers c := fun j hj a ha =>
    (Subgroup.mem_normalizer_iff.mp (hJN hj) a).mp ha
  intro g hg
  obtain ⟨a, ha, hag⟩ := sl1_frattini_argument (I ⊔ (R ⊔ Subgroup.zpowers c))
    (R ⊔ Subgroup.zpowers c) S 3 Nat.prime_three le_sup_right hAn hS_le hS3 hSidx g
    (Subgroup.mem_sup_left hg)
  obtain ⟨r₁, hr₁, k, rfl⟩ := sl1_mem_sup R c ha
  have hck : c ^ (-k) ∈ S := S.zpow_mem hcS (-k)
  have hnN : c ^ (-k) * (r₁ * c ^ k * g) ∈ Subgroup.normalizer (S : Set M) :=
    mul_mem (Subgroup.le_normalizer (H := S) hck) hag
  have hr' : c ^ (-k) * r₁ * c ^ k ∈ R := by
    have e1 : (c ^ (-k))⁻¹ = c ^ k := by rw [zpow_neg, inv_inv]
    have h := Subgroup.Normal.conj_mem ‹R.Normal› r₁ hr₁ (c ^ (-k))
    rw [e1] at h
    exact h
  have hnI : c ^ (-k) * (r₁ * c ^ k * g) ∈ I := by
    have e2 : c ^ (-k) * (r₁ * c ^ k * g) = (c ^ (-k) * r₁ * c ^ k) * g := by
      simp only [mul_assoc]
    rw [e2]
    exact mul_mem (hRI hr') hg
  refine ⟨(c ^ (-k) * r₁ * c ^ k)⁻¹, R.inv_mem hr', c ^ (-k) * (r₁ * c ^ k * g),
    Subgroup.mem_inf.mpr ⟨hnI, hnN⟩, ?_⟩
  group

end CFSG.RankThree.PartTwo.Sec13.F135Last
