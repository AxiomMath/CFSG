module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangS1KGField
public import CFSG.LocalAnalysis.StandardType.GGNbrLangS1Labels
import CFSG.LocalAnalysis.StandardType.KGLangS1AUniComp
import CFSG.LocalAnalysis.StandardType.KGLangTorAUniLift
import CFSG.LocalAnalysis.StandardType.KGLangTorAFields
import CFSG.LocalAnalysis.StandardType.GGRecipeFieldUnitary
import CFSG.LocalAnalysis.StandardType.GGRecipeFieldSpUUnitary
import CFSG.LocalAnalysis.StandardType.GGL45TGSU
import CFSG.ClassicalGroups.Unitary.Simple

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private theorem kgFieldCompContUniAux_recipe {p : ℕ} (hp : p.Prime) (_hp2 : p ≠ 2)
    {l n : ℕ} (h6 : (p = 3 ∧ (l = 2 ∨ l = 5)) ∨ (p = 5 ∧ l = 4))
    (hn : 1 ≤ n) (hpn : p ∣ n)
    (F : Type) [Field F] [Finite F] (hF : Nat.card F = (2 ^ n) ^ 2) :
    KGFieldCompCont p ⟨.twA, l, n⟩
      (LargeEvenProj (LargeEvenSUGroup (Fin (l + 1)) F (2 ^ n)))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin (l + 1)) F (2 ^ n)))
        (LargeEvenGUSet (Fin (l + 1)) F (2 ^ n)))
      (LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSUGroup (Fin (l + 1)) F (2 ^ n)))) := by
  classical
  have hl : 2 ≤ l := by rcases h6 with ⟨-, h | h⟩ | ⟨-, h⟩ <;> omega
  let SU : Subgroup (GL (Fin (l + 1)) F) := LargeEvenSUGroup (Fin (l + 1)) F (2 ^ n)
  let R : Type := LargeEvenProj SU
  let I : Set (MulAut R) :=
    LargeEvenMatConjImage (LargeEvenProjMk SU) (LargeEvenGUSet (Fin (l + 1)) F (2 ^ n))
  let Fd : Set (MulAut R) := LargeEvenMatFieldImage (LargeEvenProjMk SU)
  have hd : 3 ≤ l + 1 := by omega
  have hp3 : 3 ≤ p := by
    have hodd := hp.odd_of_ne_two _hp2
    have h2 := hp.two_le
    omega
  have hn3 : 3 ≤ n := le_trans hp3 (Nat.le_of_dvd hn hpn)
  have hdq' : ¬(l + 1 = 3 ∧ 2 ^ n = 2) := by
    rintro ⟨-, h2⟩
    have hle : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn3
    rw [h2] at hle
    omega
  have hdq : (l + 1, 2 ^ n) ≠ (3, 2) := fun h => hdq' (Prod.mk.inj h)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdata : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 n F :=
    unitaryFieldData_of_card hn hF
  change KGFieldCompCont p ⟨.twA, l, n⟩ R I Fd
  have hsimple : IsSimpleGroup R :=
    CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU F 2 n hF (l + 1) hd hdq
  haveI hSUperf : Group.IsPerfect SU :=
    Subgroup.isPerfect_iff.mpr (GGL45TG.SU.commutator_su hdata hd (by omega : 2 ≤ n))
  haveI hRperf : Group.IsPerfect R :=
    Group.IsPerfect.ofSurjective (f := LargeEvenProjMk SU) (QuotientGroup.mk'_surjective _)
  haveI : Nontrivial R := hsimple.toNontrivial
  have hna : ∃ a b : R, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    exact Group.IsPerfect.not_isSolvable R (Group.isSolvable_of_comm hcon)
  have hFC : GGRawFieldConj p R I Fd :=
    RecipeFieldSpU.ggRawFieldConj_unitary hdata hF hd hdq' hp _hp2
  intro φ hφ hφI hφp J₀ hJ₀
  obtain ⟨u, hu, f, hf, hφeq⟩ := hφ
  have hφIp : (u * f) ^ p = 1 := by rw [← hφeq]; exact hφp
  have hφIf : u * f ∉ I := by rw [← hφeq]; exact hφI
  obtain ⟨f', hf'F, u', hu'I, hord', heq⟩ := hFC hsimple hna u hu f hf hφIf hφIp
  have hφu' : φ = u' * f' * u'⁻¹ := hφeq.trans heq
  obtain ⟨σ, hσord, hσE⟩ := kgLangTorA_uni_field hF hn hd hdq' hf'F hord'
  have hF₀card : Nat.card (CFSG.GroupTheory.SteinbergBK.semilinearFixedSubfield σ) =
      (2 ^ (n / p)) ^ 2 :=
    (kgLangTorA_card_fixed_unitary hn hp _hp2 hF hσord).2
  have hkerπ : (LargeEvenProjMk SU).ker ≤ Subgroup.center SU := by
    rw [show (LargeEvenProjMk SU).ker = (LargeEvenScalars (Fin (l + 1)) F).subgroupOf SU from
      QuotientGroup.ker_mk' _]
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    have hx' : (x : GL (Fin (l + 1)) F) ∈ Subgroup.center (GL (Fin (l + 1)) F) := by
      rw [Matrix.GeneralLinearGroup.center_eq_range_scalar, ← largeEvenScalars_def]
      exact Subgroup.mem_subgroupOf.mp hx
    exact Subtype.ext (Subgroup.mem_center_iff.mp hx' (y : GL (Fin (l + 1)) F))
  let κ'' : SU →* R := u'.toMonoidHom.comp (LargeEvenProjMk SU)
  have hκ''_apply : ∀ h, κ'' h = u' (LargeEvenProjMk SU h) := fun _ => rfl
  have hκ''surj : Function.Surjective κ'' :=
    (MulEquiv.surjective u').comp (QuotientGroup.mk'_surjective _)
  have hκ''ker : κ''.ker ≤ Subgroup.center SU := by
    intro h hh
    apply hkerπ
    rw [MonoidHom.mem_ker] at hh ⊢
    have hh' : u' (LargeEvenProjMk SU h) = 1 := by
      rw [← hκ''_apply h]
      exact hh
    exact MulEquiv.injective u' (by rw [hh', map_one])
  let ψ₀ : SU →* SU :=
    { toFun := fun g => ⟨Matrix.GeneralLinearGroup.map (σ : F →+* F) (g : GL (Fin (l + 1)) F),
        GGL45TG.SU.map_mem_su hdata σ g.2⟩
      map_one' := by
        apply Subtype.ext
        exact map_one (Matrix.GeneralLinearGroup.map (σ : F →+* F))
      map_mul' := by
        intro a b
        apply Subtype.ext
        exact map_mul (Matrix.GeneralLinearGroup.map (σ : F →+* F)) _ _ }
  have hψ₀ : ∀ g, ((ψ₀ g : SU) : GL (Fin (l + 1)) F) =
      Matrix.GeneralLinearGroup.map (σ : F →+* F) (g : GL (Fin (l + 1)) F) := fun _ => rfl
  have hf'_act : ∀ h : SU, f' (LargeEvenProjMk SU h) = LargeEvenProjMk SU (ψ₀ h) :=
    fun h => hσE h (ψ₀ h) rfl
  have hξ'' : ∀ h, φ (κ'' h) = κ'' (ψ₀ h) := by
    intro h
    rw [hφu', hκ''_apply h, hκ''_apply (ψ₀ h)]
    simp only [MulAut.mul_apply, MulAut.inv_apply_self, hf'_act h]
  have hfix_eq : ggFixSub φ = MonoidHom.eqLocus (φ : R →* R) (MonoidHom.id R) := by
    ext x
    rw [mem_ggFixSub]
    change φ x = x ↔ x ∈ MonoidHom.eqLocusM (φ : R →* R) (MonoidHom.id R)
    rw [MonoidHom.mem_eqLocusM]
    rfl
  have hJ₀' : IsComponentOf J₀ (ggFixSub φ) := by
    rw [hfix_eq]
    exact hJ₀
  by_cases hq₀ : l + 1 = 3 ∧ 2 ^ (n / p) = 2
  · exfalso
    obtain ⟨hd3, h2⟩ := hq₀
    have hl2 : l = 2 := by omega
    subst l
    exact (kgLangS1A_uni_not_component hF hn hp _hp2 hσord h2 κ'' hκ''surj hκ''ker ψ₀ hψ₀
      hξ'' J₀) hJ₀'
  · obtain ⟨ρ, -⟩ := kgLangS1A_uni_component (d := l + 1) hF hn hd hp _hp2 hσord hq₀ κ''
      hκ''surj hκ''ker ψ₀ hψ₀ hξ'' hJ₀'
    refine ⟨⟨.twA, l, n / p⟩, ?_, ?_, ?_, Or.inl ⟨rfl, rfl⟩⟩
    · dsimp only [LargeEvenInLambda2]
      refine ⟨?_, ?_, ?_⟩
      · exact Nat.div_pos (Nat.le_of_dvd hn hpn) hp.pos
      · exact hl
      · intro h1
        by_contra hlt
        have h1le : 1 ≤ n / p := Nat.div_pos (Nat.le_of_dvd hn hpn) hp.pos
        have hnp1 : n / p = 1 := by omega
        exact hq₀ ⟨by omega, by rw [hnp1]; norm_num⟩
    · unfold GGHasLabel CFSG.StandardType.LargeEvenRawDatum
      exact ⟨CFSG.GroupTheory.SteinbergBK.semilinearFixedSubfield σ, inferInstance,
        inferInstance, hF₀card, ⟨ρ⟩⟩
    · exact Nat.div_mul_cancel hpn

theorem kgFieldCompCont_uni {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (hS : GGNbrLangS1UniLabel p lab) :
    LargeEvenLabelAll lab (KGFieldCompCont p lab) := by
  intro Q hQ
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨hsix, -, hpn, htag⟩ := hS
  dsimp only at htag
  subst htag
  have hn : 1 ≤ n := hlab.1
  have h6 : (p = 3 ∧ (l = 2 ∨ l = 5)) ∨ (p = 5 ∧ l = 4) := hsix.2
  dsimp only [CFSG.StandardType.LargeEvenRawDatum] at hQ ⊢
  exact recipeUnitary_and (d := l + 1) (q := 2 ^ n) (Q := Q)
    (P := KGFieldCompCont p ⟨.twA, l, n⟩)
    (fun F _ _ hF => kgFieldCompContUniAux_recipe hp hp2 h6 hn hpn F hF) hQ

end CFSG.StandardType
