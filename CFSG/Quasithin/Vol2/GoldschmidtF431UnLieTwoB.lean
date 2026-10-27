module

public import CFSG.Quasithin.Vol2.GoldschmidtF431UnLieTwoA
public import CFSG.Quasithin.Vol2.GoldschmidtF431NFSpecial
public import CFSG.Quasithin.EmptyFaithful.S1421Inputs
public import CFSG.Quasithin.Vol2.GoldschmidtF431UnOutLieLev

public noncomputable section

namespace CFSG.Quasithin.H13.F431.Un.OL

set_option linter.unusedSectionVars false

open Matrix Subgroup CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.EvenBN.U4 CFSG.QuasithinUnique CFSG.Open CFSG.Quasithin

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K) [CharP K 2]

theorem mem_normalizer_sup {G : Type*} [Group G] {A B : Subgroup G} {g : G}
    (hA : g ∈ Subgroup.normalizer (A : Set G)) (hB : g ∈ Subgroup.normalizer (B : Set G)) :
    g ∈ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  have key : ∀ {g : G}, g ∈ Subgroup.normalizer (A : Set G) →
      g ∈ Subgroup.normalizer (B : Set G) → ∀ y ∈ A ⊔ B, g * y * g⁻¹ ∈ A ⊔ B := by
    intro g hA hB y hy
    have hle : A ⊔ B ≤ (A ⊔ B).comap (MulAut.conj g).toMonoidHom := by
      refine sup_le (fun a ha => ?_) (fun b hb => ?_)
      · exact mem_sup_left ((Subgroup.mem_normalizer_iff.1 hA a).1 ha)
      · exact mem_sup_right ((Subgroup.mem_normalizer_iff.1 hB b).1 hb)
    exact hle hy
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨key hA hB y, fun hy => ?_⟩
  have := key (inv_mem hA) (inv_mem hB) _ hy
  simpa [mul_assoc] using this

theorem P_le_A1_sup_A2 : miyamotoP h ≤ miyamotoA1 h ⊔ miyamotoA2 h := by
  intro g hg
  obtain ⟨a, b, c, d, hb, hd, rfl⟩ := (mem_P h).1 hg
  have hv : miyamotoXGL h a 0 c d ∈ miyamotoA2 h := (miyamotoXGL_mem_A2 h).2 ⟨rfl, hd⟩
  have hvP : miyamotoXGL h a 0 c d ∈ miyamotoP h := miyamotoA2_le_P h hv
  have hu := inv_mul_mem_A1_of_coord h hvP hg (by simp)
  have e : miyamotoXGL h a b c d =
      miyamotoXGL h a 0 c d * ((miyamotoXGL h a 0 c d)⁻¹ * miyamotoXGL h a b c d) := by group
  rw [e]
  exact mul_mem (mem_sup_right hv) (mem_sup_left hu)

theorem normalizer_A1_inf_A2_le {g : GL (Fin 4) K}
    (h1 : g ∈ Subgroup.normalizer (miyamotoA1 h : Set (GL (Fin 4) K)))
    (h2 : g ∈ Subgroup.normalizer (miyamotoA2 h : Set (GL (Fin 4) K))) :
    g ∈ Subgroup.normalizer (miyamotoP h : Set (GL (Fin 4) K)) := by
  have hP : miyamotoP h = miyamotoA1 h ⊔ miyamotoA2 h :=
    le_antisymm (P_le_A1_sup_A2 h) (sup_le (miyamotoA1_le_P h) (miyamotoA2_le_P h))
  rw [hP]
  exact mem_normalizer_sup h1 h2

theorem Pt_inf_Ln_le_normalizer_Psy : Pt h ⊓ Ln h ≤ Subgroup.normalizer (Psy h : Set (Xg h)) := by
  intro g hg
  rw [Subgroup.mem_inf, mem_Pt_iff, mem_Ln_iff] at hg
  exact (mem_normalizer_sg_iff h (miyamotoUnipotent_le_SU h false false)).2
    (normalizer_A1_inf_A2_le h hg.2 hg.1)

theorem normalizer_Psy_le : Subgroup.normalizer (Psy h : Set (Xg h)) ≤ Pt h ⊓ Ln h := by
  intro g hg
  have hg' := (mem_normalizer_sg_iff h (miyamotoUnipotent_le_SU h false false)).1 hg
  refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
  · rw [mem_Pt_iff]
    have hZ : (g : GL (Fin 4) K) ∈ Subgroup.normalizer (miyamotoZ h : Set (GL (Fin 4) K)) := by
      rw [← centerIn_miyamotoP h]
      exact normalizer_le_normalizer_centerIn _ hg'
    exact ((normalizer_miyamotoZ h).le (Subgroup.mem_inf.2 ⟨g.2, hZ⟩)).2
  · rw [mem_Ln_iff]
    exact normalizer_P_le_normalizer_A1 h hg'

theorem Psy_le_Pt_inf_Ln : Psy h ≤ Pt h ⊓ Ln h := fun _ hx =>
  normalizer_Psy_le h (Subgroup.le_normalizer hx)

theorem isSylowTwoOf_Psy_Pt_inf_Ln : IsSylowTwoOf (Psy h) (Pt h ⊓ Ln h) :=
  F7.isSylowTwoOf_mono_right (isSylowTwoOf_Psy h) (Psy_le_Pt_inf_Ln h) le_top

theorem map_Psy_le {α : MulAut (Xg h)} (hPt : α ∈ autStab (Pt h)) (hLn : α ∈ autStab (Ln h)) :
    ∀ x ∈ Psy h, α x ∈ Psy h := by
  have := finite_Xg h
  have hB : ∀ x ∈ Psy h, α x ∈ Pt h ⊓ Ln h := fun x hx =>
    Subgroup.mem_inf.2 ⟨(hPt x).1 (Psy_le_Pt_inf_Ln h hx).1, (hLn x).1 (Psy_le_Pt_inf_Ln h hx).2⟩
  have hSyl := isSylowTwoOf_Psy_Pt_inf_Ln h
  have hA : IsPGroup 2 ((Psy h).map α.toMonoidHom) :=
    (hSyl.2.1).of_equiv (Subgroup.equivMapOfInjective (Psy h) α.toMonoidHom α.injective)
  obtain ⟨m, hm, hmA⟩ := CFSG.Quasithin.H13.F431.NF.exists_conj_le_of_isPGroup hSyl.1 hSyl.2.1
    hSyl.2.2 (A := (Psy h).map α.toMonoidHom) (by rintro _ ⟨x, hx, rfl⟩; exact hB x hx) hA
  intro x hx
  have h1 := hmA (α x) ⟨x, hx, rfl⟩
  have hN := (Subgroup.mem_normalizer_iff.1 (Pt_inf_Ln_le_normalizer_Psy h (inv_mem hm))
    (m * α x * m⁻¹)).1 h1
  simpa [mul_assoc] using hN

theorem autStab_Psy_of_stab {α : MulAut (Xg h)} (hPt : α ∈ autStab (Pt h))
    (hLn : α ∈ autStab (Ln h)) : α ∈ autStab (Psy h) := by
  intro x
  refine ⟨fun hx => map_Psy_le h hPt hLn x hx, fun hx => ?_⟩
  have := map_Psy_le h ((autStab (Pt h)).inv_mem hPt) ((autStab (Ln h)).inv_mem hLn) _ hx
  simpa using this

theorem exists_conj_of_stab {α : MulAut (Xg h)} (hPt : α ∈ autStab (Pt h))
    (hLn : α ∈ autStab (Ln h)) :
    ∃ s ∈ Pt h ⊓ Ln h, α (z1X h) = s * z1X h * s⁻¹ ∧ α (z2X h) = s * z2X h * s⁻¹ := by
  obtain ⟨s, hs⟩ := exists_eq_conj_mul_fieldAut h α
  have hα := autStab_Psy_of_stab h hPt hLn
  generalize miyamotoFieldFactor h α = ψ at hs
  have hs' : α = cj h s * fa h ψ := hs
  refine ⟨s, normalizer_Psy_le h ?_, ?_, ?_⟩
  · refine (Subgroup.mem_normalizer_iff).2 fun y => ?_
    obtain ⟨x, rfl⟩ := (fa h ψ).surjective y
    have e : α x = s * fa h ψ x * s⁻¹ := by
      rw [hs']
      rfl
    exact (fStab_Psy h ψ x).trans ((hα x).trans (by rw [e]))
  · rw [hs', MulAut.mul_apply, fa_z1X, MulAut.conj_apply]
  · rw [hs', MulAut.mul_apply, fa_z2X, MulAut.conj_apply]

theorem center_Xg {w : Xg h} (hw : w ∈ Psy h) (hc : ∀ y ∈ Psy h, y * w = w * y) (hw1 : w ≠ 1) :
    ∃ b ∈ Pt h ⊓ Ln h, b * z1X h * b⁻¹ = w := by
  have hwP : (w : GL (Fin 4) K) ∈ miyamotoP h := hw
  have hwC : (w : GL (Fin 4) K) ∈ Subgroup.centralizer (miyamotoP h : Set (GL (Fin 4) K)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact congrArg (fun x : Xg h => (x : GL (Fin 4) K))
      (hc ⟨y, miyamotoUnipotent_le_SU h false false hy⟩ hy)
  have hwZ : (w : GL (Fin 4) K) ∈ miyamotoZ h := by
    rw [← centerIn_miyamotoP h]
    exact ⟨hwP, hwC⟩
  obtain ⟨d, hd, hwd⟩ := (mem_Z h).1 hwZ
  have hd0 : d ≠ 0 := by
    rintro rfl
    apply hw1
    apply Subtype.ext
    rw [hwd, miyamotoXGL_zero]
    rfl
  obtain ⟨g, hgI, hconj⟩ := exists_conj_Z h (d := 1) (d' := d) (map_one _) hd one_ne_zero hd0
  have hgS : g⁻¹ ∈ gramSU h (miyamotoJ4 K) := inv_mem (miyamotoI_le_gramSU h hgI)
  refine ⟨⟨g⁻¹, hgS⟩, Subgroup.mem_inf.2 ⟨?_, ?_⟩, Subtype.ext ?_⟩
  · rw [mem_Pt_iff]
    exact inv_mem (miyamotoI_le_normalizer_unipotent h false true hgI)
  · rw [mem_Ln_iff]
    exact inv_mem (miyamotoI_le_normalizer_unipotent h true false hgI)
  · show g⁻¹ * miyamotoZ1 K * g⁻¹⁻¹ = (w : GL (Fin 4) K)
    rw [inv_inv, miyamotoZ1_eq h, hconj, hwd]

theorem aut_z_Xg (α : MulAut (Xg h)) (hPt : α ∈ autStab (Pt h)) (hLn : α ∈ autStab (Ln h)) :
    ∃ b ∈ Pt h ⊓ Ln h, α (z1X h) = b * z1X h * b⁻¹ :=
  let ⟨s, hs, e1, _⟩ := exists_conj_of_stab h hPt hLn
  ⟨s, hs, e1⟩

theorem aut_t_Xg (α : MulAut (Xg h)) (hPt : α ∈ autStab (Pt h)) (hLn : α ∈ autStab (Ln h)) :
    ∃ b ∈ Pt h ⊓ Ln h, α (z2X h) = b * z2X h * b⁻¹ :=
  let ⟨s, hs, _, e2⟩ := exists_conj_of_stab h hPt hLn
  ⟨s, hs, e2⟩

end CFSG.Quasithin.H13.F431.Un.OL
