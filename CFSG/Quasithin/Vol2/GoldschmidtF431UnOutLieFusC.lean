module

public import CFSG.Quasithin.Vol2.GoldschmidtF431UnOutLieFusB
public import CFSG.Quasithin.Vol2.GoldschmidtF431UnOutLieFld
public import CFSG.Quasithin.Vol2.GoldschmidtF431UnOutLieFus
public import CFSG.Quasithin.Vol2.GoldschmidtF431UnOutLieLev

public noncomputable section

namespace CFSG.Quasithin.H13.F431.Un.OL

set_option linter.unusedSectionVars false

open Matrix Subgroup CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.EvenBN.U4

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K) [CharP K 2]

theorem fus_A1 (Fk : Subgroup (K ≃+* K)) {y : Xg h} (hy : y ∈ A1X h) (hy1 : y ≠ 1) :
    ∃ i, (i = z1X h ∨ i = z2X h) ∧
      ∃ m ∈ Ssd h (Ln h) (fStab_Ln h) Fk, m * cj h y * m⁻¹ = cj h i := by
  have hA : (y : GL (Fin 4) K) ∈ miyamotoA1 h := hy
  have hy1' : (y : GL (Fin 4) K) ≠ 1 := fun e => hy1 (Subtype.ext e)
  by_cases hQ : miyamotoQA1 h (y : GL (Fin 4) K) = 0
  · obtain ⟨n, hn, e⟩ := exists_N1_conj_z1 h hA hy1' hQ
    rw [← miyamotoZ1_eq h] at e
    refine ⟨z1X h, Or.inl rfl, fus_step' h Fk (g := ⟨n, miyamotoN1_le_gramSU h hn⟩)
      (mem_Ln_of_mem_N1 h hn) (Subtype.ext ?_)⟩
    change n * (y : GL (Fin 4) K) * n⁻¹ = miyamotoZ1 K
    rw [← e]
    group
  · have hmem : (y : GL (Fin 4) K) ∈ {y | ∃ g ∈ miyamotoI1 h ⊔ miyamotoN1 h,
        g⁻¹ * LocalAnalysis.miyamotoZ2 K * g = y} := by
      rw [miyamoto_orbit_z2_I1N1 h]
      exact ⟨hA, hQ⟩
    obtain ⟨g, hg, e⟩ := hmem
    have hgS : g ∈ gramSU h (miyamotoJ4 K) :=
      sup_le (miyamotoI1_le_SU h) (miyamotoN1_le_gramSU h) hg
    refine ⟨z2X h, Or.inr rfl, fus_step' h Fk (g := ⟨g, hgS⟩)
      (mem_Ln_of_mem_I1_sup_N1 h hg) (Subtype.ext ?_)⟩
    change g * (y : GL (Fin 4) K) * g⁻¹ = LocalAnalysis.miyamotoZ2 K
    rw [← e]
    group

theorem fusion_Ssd (F₂ Fk : Subgroup (K ≃+* K)) (x : MulAut (Xg h))
    (hx : x ∈ Ssd h (Psy h) (fStab_Psy h) ⊥) (hx2 : orderOf x = 2) :
    ∃ i, (i = cj h (z1X h) ∨ i = cj h (z2X h)) ∧
      Relation.ReflTransGen (fun a b : MulAut (Xg h) =>
        a ∈ Ssd h (Psy h) (fStab_Psy h) F₂ ∧ b ∈ Ssd h (Psy h) (fStab_Psy h) F₂ ∧
        ((∃ m ∈ Ssd h (Pt h) (fStab_Pt h) Fk, m * a * m⁻¹ = b) ∨
          (∃ m ∈ Ssd h (Ln h) (fStab_Ln h) Fk, m * a * m⁻¹ = b))) x i := by
  obtain ⟨u, hu, φ, hφ, rfl⟩ := hx
  rw [Subgroup.mem_bot] at hφ
  subst hφ
  rw [fa_one, mul_one] at hx2 ⊢
  have hsq : u * u = 1 := by
    have := pow_orderOf_eq_one (cj h u)
    rw [hx2, sq, ← cj_mul, ← cj_one h] at this
    exact (cj_inj h).1 this
  have hu1 : u ≠ 1 := fun e => by
    rw [e, cj_one, orderOf_one] at hx2
    exact absurd hx2 (by norm_num)
  have hT : ∀ w ∈ Psy h, cj h w ∈ Ssd h (Psy h) (fStab_Psy h) F₂ := fun w hw => cj_mem_Ssd h hw
  have hP : (u : GL (Fin 4) K) ∈ miyamotoP h := hu
  obtain ⟨a, b, c, d, hb, hd, hcoord⟩ := (mem_P h).1 hP
  by_cases ha : a = 0
  · have huA : u ∈ A1X h := by
      show (u : GL (Fin 4) K) ∈ miyamotoA1 h
      rw [hcoord]
      exact (miyamotoXGL_mem_A1_iff_of_mem_P h (hcoord ▸ hP)).2 ha
    obtain ⟨i, hi, m, hm, e⟩ := fus_A1 h Fk huA hu1
    have hiP : i ∈ Psy h := by
      rcases hi with rfl | rfl
      exacts [z1X_mem_Psy h, z2X_mem_Psy h]
    refine ⟨cj h i, ?_, ?_⟩
    · rcases hi with rfl | rfl
      exacts [Or.inl rfl, Or.inr rfl]
    · exact Relation.ReflTransGen.single ⟨hT u hu, hT i hiP, Or.inr ⟨m, hm, e⟩⟩
  · have hp2 : miyamotoXGL h a b c d * miyamotoXGL h a b c d = 1 := by
      have := congrArg Subtype.val hsq
      rw [Subgroup.coe_mul, hcoord] at this
      exact this
    obtain ⟨hb0, l, hlF, hdF, e1, e2⟩ := fus_coords h hb hd hp2 ha
    subst hb0
    have hy₁P : miyamotoXGL h 0 l 0 0 ∈ miyamotoP h :=
      (miyamotoXGL_mem_P h).2 ⟨hlF, by simp⟩
    have hu₁P : miyamotoXGL h a 0 0 d ∈ miyamotoP h :=
      (miyamotoXGL_mem_P h).2 ⟨map_zero _, by simpa using (add_bar_eq_zero_iff h).2 hdF⟩
    have hu₂A : miyamotoXGL h 0 0 a d ∈ miyamotoA1 h :=
      (miyamotoXGL_mem_A1 h).2 ⟨rfl, map_zero _, hdF⟩
    let y₁ : Xg h := ⟨_, miyamotoUnipotent_le_SU h false false hy₁P⟩
    let u₁ : Xg h := ⟨_, miyamotoUnipotent_le_SU h false false hu₁P⟩
    let u₂ : Xg h := ⟨_, miyamotoUnipotent_le_SU h true false hu₂A⟩
    have hy₁ : y₁ ∈ Psy h := hy₁P
    have hu₁ : u₁ ∈ Psy h := hu₁P
    have hu₂A' : u₂ ∈ A1X h := hu₂A
    have hu₂ : u₂ ∈ Psy h := miyamotoA1_le_P h hu₂A
    have hu₂1 : u₂ ≠ 1 := fun e => by
      have := congrArg Subtype.val e
      change miyamotoXGL h 0 0 a d = 1 at this
      rw [← miyamotoXGL_zero h, miyamotoXGL_inj] at this
      exact ha this.2.2.1
    obtain ⟨m₁, hm₁, em₁⟩ := fus_step h (hB := fStab_Pt h) Fk (g := y₁) (a := u) (b := u₁)
      (Psy_le_Pt h hy₁) (Subtype.ext (by
        change (miyamotoXGL h 0 l 0 0)⁻¹ * (u : GL (Fin 4) K) * miyamotoXGL h 0 l 0 0 = _
        rw [hcoord]
        exact e1))
    obtain ⟨m₂, hm₂, em₂⟩ := fus_step h (hB := fStab_Pt h) Fk
      (g := ⟨miyamotoR2 K, miyamotoR2_mem_gramSU h⟩) (a := u₁) (b := u₂) (fus_r2X_mem_Pt h)
      (Subtype.ext e2)
    obtain ⟨i, hi, m₃, hm₃, em₃⟩ := fus_A1 h Fk hu₂A' hu₂1
    have hiP : i ∈ Psy h := by
      rcases hi with rfl | rfl
      exacts [z1X_mem_Psy h, z2X_mem_Psy h]
    refine ⟨cj h i, ?_, ?_⟩
    · rcases hi with rfl | rfl
      exacts [Or.inl rfl, Or.inr rfl]
    · exact Relation.ReflTransGen.head ⟨hT u hu, hT u₁ hu₁, Or.inl ⟨m₁, hm₁, em₁⟩⟩
        (Relation.ReflTransGen.head ⟨hT u₁ hu₁, hT u₂ hu₂, Or.inl ⟨m₂, hm₂, em₂⟩⟩
          (Relation.ReflTransGen.single ⟨hT u₂ hu₂, hT i hiP, Or.inr ⟨m₃, hm₃, em₃⟩⟩))

end CFSG.Quasithin.H13.F431.Un.OL
