module

public import CFSG.LocalAnalysis.StandardType.GGPsiDiagInner
public import CFSG.LieType.Steinberg.Bruhat

public section

namespace CFSG.StandardType

open CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.Steinberg
  CFSG.LieType.CurtisTits

namespace PsiDiag

variable {K : Type*} [Group K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K}

theorem mem_borel_of_mem_ggTorus
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) {h : K} (hh : h ∈ ggTorus D) : h ∈ borel D H := by
  have hN : ∀ γ ∈ D.roots, h ∈ Subgroup.normalizer (D.rootGroup γ : Set K) := by
    simp only [ggTorus, Subgroup.mem_iInf] at hh
    exact hh
  have hU : h ∈ Subgroup.normalizer (posUnipotent D : Set K) := by
    refine le_normalizer_iSup₂ (A := Subgroup.zpowers h) (fun y hy γ hγ z hz => ?_)
      (Subgroup.mem_zpowers h)
    have hyN : y ∈ Subgroup.normalizer (D.rootGroup γ : Set K) :=
      (Subgroup.zpowers_le.mpr (hN γ hγ.1)) hy
    exact rootGroup_le_posUnipotent hγ.1 hγ.2 ((Subgroup.mem_normalizer_iff.mp hyN z).mp hz)
  obtain ⟨w, hw⟩ := exists_mem_bruhatCell hct hext h
  by_cases hw1 : w = 1
  · rw [hw1, bruhatCell_one hct] at hw
    exact hw
  exfalso
  obtain ⟨b₁, hb₁, b₂, hb₂, he⟩ := hw
  have hBN := borel_le_normalizer_posUnipotent (D := D) (H := H) hct
  have hnN : nrep hct w ∈ Subgroup.normalizer (posUnipotent D : Set K) := by
    have : nrep hct w = b₁⁻¹ * h * b₂⁻¹ := by rw [he]; group
    rw [this]
    exact mul_mem (mul_mem (inv_mem (hBN hb₁)) hU) (inv_mem (hBN hb₂))
  obtain ⟨i, hi⟩ := (coxeterMatrix D.isFiniteType).toCoxeterSystem.exists_rightDescent_of_ne_one hw1
  have hγ : weylAction D.isFiniteType w (Pi.single i 1) ∈ D.roots :=
    weylAction_mem_roots _ w (single_mem_roots i)
  have hneg := ht_weylAction_single_neg (D := D) hi
  have hact := actsAs_nrep hct w (Pi.single i 1) (single_mem_roots i)
  have hle : D.rootGroup (weylAction D.isFiniteType w (Pi.single i 1)) ≤ posUnipotent D := by
    rw [← hact, Subgroup.map_le_iff_le_comap]
    intro z hz
    have hz' : z ∈ posUnipotent D :=
      rootGroup_le_posUnipotent (single_mem_roots i) (ht_single_pos i) hz
    exact (Subgroup.mem_normalizer_iff.mp hnN z).mp hz'
  have hle' := rootGroup_le_negUnipotent hγ hneg
  have hbot : D.rootGroup (weylAction D.isFiniteType w (Pi.single i 1)) = ⊥ := by
    rw [eq_bot_iff, ← posUnipotent_inf_negUnipotent hext]
    exact le_inf hle hle'
  exact hext.ne_bot _ hγ hbot

theorem eq_one_of_mem_rootGroup_single_of_mem_posUnipotentExcept
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) (i : Fin D.rank) {z : K}
    (hz₁ : z ∈ D.rootGroup (Pi.single i 1)) (hz₂ : z ∈ posUnipotentExcept D i) : z = 1 := by
  have h1 : n i * z * (n i)⁻¹ ∈ posUnipotent D :=
    posUnipotentExcept_le_posUnipotent i (conj_n_mem_posUnipotentExcept hct i hz₂)
  have h2 : n i * z * (n i)⁻¹ ∈ negUnipotent D := by
    have h := hct.conj_mem i _ (single_mem_roots i) z hz₁
    rw [weylAction_simple_single] at h
    exact rootGroup_le_negUnipotent (neg_single_mem_roots i)
      (by rw [ht_neg]; exact neg_lt_zero.mpr (ht_single_pos (D := D) i)) h
  have h3 : n i * z * (n i)⁻¹ ∈ (⊥ : Subgroup K) := by
    rw [← posUnipotent_inf_negUnipotent hext]
    exact ⟨h1, h2⟩
  rw [Subgroup.mem_bot] at h3
  calc z = (n i)⁻¹ * (n i * z * (n i)⁻¹) * n i := by group
    _ = 1 := by rw [h3]; group

variable {k : Type*} [Field k] {x : (Fin D.rank → ℤ) → k → K}

@[expose] def scalarSub (x : (Fin D.rank → ℤ) → k → K) (γ : Fin D.rank → ℤ) : Subgroup K where
  carrier := {t | ∃ χ : kˣ, ∀ c, t * x γ c * t⁻¹ = x γ ((χ : k) * c)}
  one_mem' := ⟨1, fun c => by simp⟩
  mul_mem' := by
    rintro a b ⟨χa, ha⟩ ⟨χb, hb⟩
    refine ⟨χa * χb, fun c => ?_⟩
    calc a * b * x γ c * (a * b)⁻¹ = a * (b * x γ c * b⁻¹) * a⁻¹ := by group
      _ = x γ ((χa : k) * ((χb : k) * c)) := by rw [hb, ha]
      _ = x γ (((χa * χb : kˣ) : k) * c) := by rw [Units.val_mul, mul_assoc]
  inv_mem' := by
    rintro a ⟨χ, ha⟩
    exact ⟨χ⁻¹, fun c => by rw [inv_inv]; exact inv_conj_of_conj ha c⟩

theorem mem_scalarSub_iff {γ : Fin D.rank → ℤ} {t : K} :
    t ∈ scalarSub x γ ↔ ∃ χ : kˣ, ∀ c, t * x γ c * t⁻¹ = x γ ((χ : k) * c) :=
  Iff.rfl

theorem torusElt_mem_scalarSub {C : (Fin D.rank → ℤ) → (Fin D.rank → ℤ) → ℕ × ℕ → ℤ}
    {O : CommOrder (CFSG.LieType.Steinberg.RootSystem.ofCartan D.isFiniteType D.divisible)}
    (hE : ChevalleyExtras D k x C O) (j : Fin D.rank) (s : kˣ) {γ : Fin D.rank → ℤ}
    (hγ : γ ∈ D.roots) : torusElt x j s ∈ scalarSub x γ :=
  ⟨s ^ coroot D.cartan j γ, fun c => torusElt_conj hE j s hγ c⟩

theorem conj_single_of_mem_borel
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H)
    (hpar : IsParametrization (Φ := CFSG.LieType.Steinberg.RootSystem.ofCartan D.isFiniteType
      D.divisible) D.rootGroup x) (i : Fin D.rank)
    (hT : ⨆ j, H j ≤ scalarSub x (Pi.single i 1)) {h : K} (hB : h ∈ borel D H)
    (hN : h ∈ Subgroup.normalizer (D.rootGroup (Pi.single i 1) : Set K)) :
    ∃ χ : k, ∀ c, h * x (Pi.single i 1) c * h⁻¹ = x (Pi.single i 1) (χ * c) := by
  obtain ⟨t, ht, u, hu, y, hy, rfl⟩ := exists_eq_mul_mul_of_mem_borel hct hext i hB
  obtain ⟨χ, hχ⟩ := (mem_scalarSub_iff).mp (hT ht)
  refine ⟨χ, fun c => ?_⟩
  have hpi := hpar _ (single_mem_roots i)
  obtain ⟨a, rfl⟩ := (hpi.1 y).mp hy
  have hz : x (Pi.single i 1) c ∈ D.rootGroup (Pi.single i 1) := (hpi.1 _).mpr ⟨c, rfl⟩
  have hyz : x (Pi.single i 1) a * x (Pi.single i 1) c * (x (Pi.single i 1) a)⁻¹ =
      x (Pi.single i 1) c := by
    rw [← hpi.2.1, add_comm, hpi.2.1]
    group
  have htN : t ∈ Subgroup.normalizer (D.rootGroup (Pi.single i 1) : Set K) :=
    iSup_le_normalizer_rootGroup hct (single_mem_roots i) ht
  have hsplit : t * u * x (Pi.single i 1) a * x (Pi.single i 1) c *
      (t * u * x (Pi.single i 1) a)⁻¹ = t * (u * x (Pi.single i 1) c * u⁻¹) * t⁻¹ := by
    rw [show t * u * x (Pi.single i 1) a * x (Pi.single i 1) c *
        (t * u * x (Pi.single i 1) a)⁻¹ = t * (u * (x (Pi.single i 1) a * x (Pi.single i 1) c *
          (x (Pi.single i 1) a)⁻¹) * u⁻¹) * t⁻¹ by group, hyz]
  have h1 : u * x (Pi.single i 1) c * u⁻¹ ∈ D.rootGroup (Pi.single i 1) := by
    have hh := (Subgroup.mem_normalizer_iff.mp hN _).mp hz
    rw [hsplit] at hh
    have h' := (Subgroup.mem_normalizer_iff.mp (inv_mem htN) _).mp hh
    rwa [show t⁻¹ * (t * (u * x (Pi.single i 1) c * u⁻¹) * t⁻¹) * t⁻¹⁻¹ =
      u * x (Pi.single i 1) c * u⁻¹ by group] at h'
  have h2 : (x (Pi.single i 1) c)⁻¹ * (u * x (Pi.single i 1) c * u⁻¹) ∈
      posUnipotentExcept D i := by
    have hzN := rootGroup_single_le_normalizer hext i (inv_mem hz)
    rw [show (x (Pi.single i 1) c)⁻¹ * (u * x (Pi.single i 1) c * u⁻¹) =
      (x (Pi.single i 1) c)⁻¹ * u * (x (Pi.single i 1) c)⁻¹⁻¹ * u⁻¹ by group]
    exact mul_mem ((Subgroup.mem_normalizer_iff.mp hzN u).mp hu) (inv_mem hu)
  have h3 := eq_one_of_mem_rootGroup_single_of_mem_posUnipotentExcept hct hext i
    (mul_mem (inv_mem hz) h1) h2
  have huz : u * x (Pi.single i 1) c * u⁻¹ = x (Pi.single i 1) c := by
    calc u * x (Pi.single i 1) c * u⁻¹ = x (Pi.single i 1) c *
          ((x (Pi.single i 1) c)⁻¹ * (u * x (Pi.single i 1) c * u⁻¹)) := by group
      _ = x (Pi.single i 1) c := by rw [h3, mul_one]
  rw [hsplit, huz, hχ]

theorem ggTorus_conj_single
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H)
    (hpar : IsParametrization (Φ := CFSG.LieType.Steinberg.RootSystem.ofCartan D.isFiniteType
      D.divisible) D.rootGroup x) (i : Fin D.rank)
    (hT : ⨆ j, H j ≤ scalarSub x (Pi.single i 1)) {h : K} (hh : h ∈ ggTorus D) :
    ∃ χ : k, ∀ c, h * x (Pi.single i 1) c * h⁻¹ = x (Pi.single i 1) (χ * c) := by
  refine conj_single_of_mem_borel hct hext hpar i hT (mem_borel_of_mem_ggTorus hct hext hh) ?_
  simp only [ggTorus, Subgroup.mem_iInf] at hh
  exact hh _ (single_mem_roots i)

end PsiDiag

end CFSG.StandardType
