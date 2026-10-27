module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.Quasithin.H13.L828N

open CFSG.Open

section Quot

variable {Γ : Type} [Group Γ] [Finite Γ] (J₀ : Subgroup Γ) [J₀.Normal]

theorem img_isPGroup {T : Subgroup Γ} (hT : IsPGroup 2 ↥T) :
    IsPGroup 2 ↥(T.map (QuotientGroup.mk' J₀)) :=
  hT.map (QuotientGroup.mk' J₀)

theorem img_index_odd {T : Subgroup Γ} (hT : ¬ 2 ∣ T.index) :
    ¬ 2 ∣ (T.map (QuotientGroup.mk' J₀)).index := fun h =>
  hT (dvd_trans h (Subgroup.index_map_dvd (H := T) (QuotientGroup.mk'_surjective J₀)))

theorem img_factor {Y T : Subgroup Γ} (h : ∀ g : Γ, ∃ y ∈ Y, ∃ t ∈ T, g = y * t) :
    ∀ x : Γ ⧸ J₀, ∃ y ∈ Y.map (QuotientGroup.mk' J₀), ∃ t ∈ T.map (QuotientGroup.mk' J₀),
      x = y * t := by
  intro x
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective J₀ x
  obtain ⟨y, hy, t, ht, rfl⟩ := h g
  exact ⟨QuotientGroup.mk' J₀ y, Subgroup.mem_map_of_mem _ hy, QuotientGroup.mk' J₀ t,
    Subgroup.mem_map_of_mem _ ht, map_mul (QuotientGroup.mk' J₀) y t⟩

theorem img_normal {Y : Subgroup Γ} [Y.Normal] : (Y.map (QuotientGroup.mk' J₀)).Normal :=
  Subgroup.Normal.map inferInstance (QuotientGroup.mk' J₀) (QuotientGroup.mk'_surjective J₀)

theorem img_unique_max {T Mm : Subgroup Γ} (hJM : J₀ ≤ Mm)
    (hM : ∀ B : Subgroup Γ, T ≤ B → B ≠ ⊤ → B ≤ Mm) :
    ∀ B' : Subgroup (Γ ⧸ J₀), T.map (QuotientGroup.mk' J₀) ≤ B' → B' ≠ ⊤ →
      B' ≤ Mm.map (QuotientGroup.mk' J₀) := by
  intro B' hTB hB'
  have hTle : T ≤ B'.comap (QuotientGroup.mk' J₀) := by
    intro t ht
    exact hTB (Subgroup.mem_map_of_mem _ ht)
  have hne : B'.comap (QuotientGroup.mk' J₀) ≠ ⊤ := by
    intro htop
    apply hB'
    rw [eq_top_iff]
    intro y _
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective J₀ y
    have hg : g ∈ B'.comap (QuotientGroup.mk' J₀) := by
      rw [htop]
      exact Subgroup.mem_top g
    exact hg
  have hle := hM _ hTle hne
  intro y hy
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective J₀ y
  exact Subgroup.mem_map_of_mem _ (hle (Subgroup.mem_comap.2 hy))

theorem img_ne_bot {V : Subgroup Γ} (h : ¬ V ≤ J₀) : V.map (QuotientGroup.mk' J₀) ≠ ⊥ := by
  intro hV
  apply h
  intro v hv
  have hmem : QuotientGroup.mk' J₀ v ∈ V.map (QuotientGroup.mk' J₀) :=
    Subgroup.mem_map_of_mem _ hv
  rw [hV, Subgroup.mem_bot] at hmem
  exact (QuotientGroup.eq_one_iff v).1 hmem

theorem img_elemAbelian {V : Subgroup Γ} (h : IsElemAbelian 2 V) :
    IsElemAbelian 2 (V.map (QuotientGroup.mk' J₀)) := by
  unfold IsElemAbelian at h ⊢
  obtain ⟨hc, hp⟩ := h
  have hcomm : ∀ a b : ↥V, a * b = b * a := fun a b => hc.is_comm.comm a b
  refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
  · rcases a with ⟨a, ha⟩
    rcases b with ⟨b, hb⟩
    obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.1 ha
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.1 hb
    have hvw : v * w = w * v := congrArg Subtype.val (hcomm ⟨v, hv⟩ ⟨w, hw⟩)
    apply Subtype.ext
    show QuotientGroup.mk' J₀ v * QuotientGroup.mk' J₀ w
      = QuotientGroup.mk' J₀ w * QuotientGroup.mk' J₀ v
    rw [← map_mul, ← map_mul, hvw]
  · intro x hx
    obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.1 hx
    rw [← map_pow, hp v hv, map_one]

theorem img_subgroupOf_normal {I P : Subgroup Γ} (hPI : P ≤ I) [(P.subgroupOf I).Normal] :
    ((P.map (QuotientGroup.mk' J₀)).subgroupOf (I.map (QuotientGroup.mk' J₀))).Normal := by
  refine ⟨fun n hn g => ?_⟩
  obtain ⟨p, hp, hpn⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hn)
  obtain ⟨i, hi, hig⟩ := Subgroup.mem_map.1 g.2
  have hb : (⟨p, hPI hp⟩ : ↥I) ∈ P.subgroupOf I := Subgroup.mem_subgroupOf.2 hp
  have h1 : (⟨i, hi⟩ : ↥I) * ⟨p, hPI hp⟩ * (⟨i, hi⟩ : ↥I)⁻¹ ∈ P.subgroupOf I :=
    (inferInstance : (P.subgroupOf I).Normal).conj_mem _ hb _
  have hconj : i * p * i⁻¹ ∈ P := Subgroup.mem_subgroupOf.1 h1
  refine Subgroup.mem_subgroupOf.2 (Subgroup.mem_map.2 ⟨i * p * i⁻¹, hconj, ?_⟩)
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, ← hig, ← hpn]

theorem img_dihedral {I P : Subgroup Γ} (hPI : P ≤ I) [(P.subgroupOf I).Normal]
    [((P.map (QuotientGroup.mk' J₀)).subgroupOf (I.map (QuotientGroup.mk' J₀))).Normal]
    (hJ : ∀ x ∈ I, x ∈ J₀ → x ∈ P) {D : Type} [Group D] (e : ↥I ⧸ P.subgroupOf I ≃* D) :
    Nonempty (↥(I.map (QuotientGroup.mk' J₀)) ⧸
      (P.map (QuotientGroup.mk' J₀)).subgroupOf (I.map (QuotientGroup.mk' J₀)) ≃* D) := by
  obtain ⟨f, hf_eq⟩ : ∃ f : ↥I →* ↥(I.map (QuotientGroup.mk' J₀)) ⧸
      (P.map (QuotientGroup.mk' J₀)).subgroupOf (I.map (QuotientGroup.mk' J₀)),
      f = (QuotientGroup.mk' ((P.map (QuotientGroup.mk' J₀)).subgroupOf
        (I.map (QuotientGroup.mk' J₀)))).comp ((QuotientGroup.mk' J₀).subgroupMap I) :=
    ⟨_, rfl⟩
  have hf : Function.Surjective f := by
    rw [hf_eq]
    exact (QuotientGroup.mk'_surjective _).comp (MonoidHom.subgroupMap_surjective _ _)
  have hker : f.ker = P.subgroupOf I := by
    ext i
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hf_eq]
    constructor
    · intro hi
      have h1 : QuotientGroup.mk' J₀ (i : Γ) ∈ P.map (QuotientGroup.mk' J₀) :=
        Subgroup.mem_subgroupOf.1
          ((QuotientGroup.eq_one_iff ((QuotientGroup.mk' J₀).subgroupMap I i)).1 hi)
      obtain ⟨p, hp, hpe⟩ := Subgroup.mem_map.1 h1
      simp only [QuotientGroup.mk'_apply] at hpe
      have hpJ : p⁻¹ * (i : Γ) ∈ J₀ := QuotientGroup.eq.1 hpe
      have hpI : p⁻¹ * (i : Γ) ∈ I := I.mul_mem (I.inv_mem (hPI hp)) i.2
      have hpP : p⁻¹ * (i : Γ) ∈ P := hJ _ hpI hpJ
      simpa using P.mul_mem hp hpP
    · intro hi
      exact (QuotientGroup.eq_one_iff ((QuotientGroup.mk' J₀).subgroupMap I i)).2
        (Subgroup.mem_subgroupOf.2 (Subgroup.mem_map_of_mem _ hi))
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hf)).symm.trans e⟩

theorem img_normal_two_group_eq_bot {T Mm : Subgroup Γ} (hT : IsPGroup 2 ↥T)
    (hT' : ¬ 2 ∣ T.index) (hTM : T ≤ Mm) (hJM : J₀ ≤ Mm)
    (hcore : ∀ N : Subgroup Γ, N.Normal → N ≤ Mm → N ≤ J₀)
    (W : Subgroup (Γ ⧸ J₀)) [W.Normal] (hW : IsPGroup 2 ↥W) : W = ⊥ := by
  have hT₀ : IsPGroup 2 ↥(T.map (QuotientGroup.mk' J₀)) := img_isPGroup J₀ hT
  have hT₀' : ¬ 2 ∣ (T.map (QuotientGroup.mk' J₀)).index := img_index_odd J₀ hT'
  have hWT : W ≤ T.map (QuotientGroup.mk' J₀) :=
    IsPGroup.le_sylow_of_normal hW (hT₀.toSylow hT₀')
  have hWc : W.comap (QuotientGroup.mk' J₀) ≤ Mm := by
    intro x hx
    obtain ⟨t, ht, hte⟩ := Subgroup.mem_map.1 (hWT (Subgroup.mem_comap.1 hx))
    simp only [QuotientGroup.mk'_apply] at hte
    have htx : t⁻¹ * x ∈ J₀ := QuotientGroup.eq.1 hte
    simpa using Mm.mul_mem (hTM ht) (hJM htx)
  have hle : W.comap (QuotientGroup.mk' J₀) ≤ J₀ :=
    hcore (W.comap (QuotientGroup.mk' J₀)) inferInstance hWc
  rw [eq_bot_iff]
  intro w hw
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective J₀ w
  have hx : x ∈ J₀ := hle (Subgroup.mem_comap.2 hw)
  exact Subgroup.mem_bot.2 ((QuotientGroup.eq_one_iff x).2 hx)

theorem img_centralizer_eq_bot {Y T Mm : Subgroup Γ} [Y.Normal] (hT : IsPGroup 2 ↥T)
    (hT' : ¬ 2 ∣ T.index) (hTM : T ≤ Mm) (hJM : J₀ ≤ Mm)
    (hcore : ∀ N : Subgroup Γ, N.Normal → N ≤ Mm → N ≤ J₀)
    (hY : ∀ g : Γ, ∃ y ∈ Y, ∃ t ∈ T, g = y * t)
    (hZ : ∀ x ∈ Y.map (QuotientGroup.mk' J₀),
      (∀ y ∈ Y.map (QuotientGroup.mk' J₀), x * y = y * x) → x = 1) :
    ∀ x : Γ ⧸ J₀, (∀ y ∈ Y.map (QuotientGroup.mk' J₀), x * y = y * x) → x = 1 := by
  intro x hx
  haveI : (Y.map (QuotientGroup.mk' J₀)).Normal := img_normal J₀
  obtain ⟨C, hCdef⟩ : ∃ C : Subgroup (Γ ⧸ J₀),
      C = Subgroup.centralizer
        ((Y.map (QuotientGroup.mk' J₀) : Subgroup (Γ ⧸ J₀)) : Set (Γ ⧸ J₀)) :=
    ⟨_, rfl⟩
  have hCmem : ∀ c : Γ ⧸ J₀, c ∈ C ↔ ∀ y ∈ Y.map (QuotientGroup.mk' J₀), y * c = c * y := by
    intro c
    rw [hCdef]
    exact Subgroup.mem_centralizer_iff
  have hCn : C.Normal := by
    rw [hCdef]
    exact Subgroup.normal_centralizer
  have hQ : IsPGroup 2 ((Γ ⧸ J₀) ⧸ Y.map (QuotientGroup.mk' J₀)) := by
    refine (img_isPGroup J₀ hT).of_surjective
      ((QuotientGroup.mk' (Y.map (QuotientGroup.mk' J₀))).comp
        (T.map (QuotientGroup.mk' J₀)).subtype) ?_
    intro z
    obtain ⟨x', rfl⟩ := QuotientGroup.mk'_surjective (Y.map (QuotientGroup.mk' J₀)) z
    obtain ⟨y, hy, t, ht, hx'⟩ := img_factor J₀ hY x'
    have hy1 : QuotientGroup.mk' (Y.map (QuotientGroup.mk' J₀)) y = 1 :=
      (QuotientGroup.eq_one_iff y).2 hy
    refine ⟨⟨t, ht⟩, ?_⟩
    show QuotientGroup.mk' (Y.map (QuotientGroup.mk' J₀)) t
      = QuotientGroup.mk' (Y.map (QuotientGroup.mk' J₀)) x'
    rw [hx', map_mul, hy1, one_mul]
  have hC2 : IsPGroup 2 ↥C := by
    refine hQ.of_injective
      ((QuotientGroup.mk' (Y.map (QuotientGroup.mk' J₀))).comp C.subtype) ?_
    rw [injective_iff_map_eq_one]
    rintro ⟨c, hc⟩ hc1
    have h2 : QuotientGroup.mk' (Y.map (QuotientGroup.mk' J₀)) c = 1 := hc1
    have hcY : c ∈ Y.map (QuotientGroup.mk' J₀) := (QuotientGroup.eq_one_iff c).1 h2
    have hcc : c = 1 := hZ c hcY (fun y hy => ((hCmem c).1 hc y hy).symm)
    exact Subtype.ext hcc
  have hCbot : C = ⊥ := img_normal_two_group_eq_bot J₀ hT hT' hTM hJM hcore C hC2
  have hxC : x ∈ C := (hCmem x).2 (fun y hy => (hx y hy).symm)
  rw [hCbot, Subgroup.mem_bot] at hxC
  exact hxC

end Quot

end CFSG.Quasithin.H13.L828N
