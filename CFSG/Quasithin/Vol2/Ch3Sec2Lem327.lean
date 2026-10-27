module

public import CFSG.Quasithin.H13.StatementsL6
public import CFSG.Quasithin.Vol2.Ch5ModulesNat
public import CFSG.LieType.Simplicity.Classical

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint

variable {G : Type} [Group G]

theorem isTISetUnder_of_eq_conjClosure {V M : Subgroup G} (h : V = conjClosure V M) :
    IsTISetUnder V M := by
  intro g hg hgn
  refine (hgn ?_).elim
  rw [h]
  exact le_normalizer_conjClosure V M hg

private theorem le_normalizer_conjClosure_aux {A I X : Subgroup G}
    (hAI : A ≤ Subgroup.normalizer (I : Set G)) (hXA : X ≤ Subgroup.normalizer (A : Set G)) :
    A ≤ Subgroup.normalizer (conjClosure I X : Set G) := by
  have key : ∀ a ∈ A, ∀ y ∈ conjClosure I X, a * y * a⁻¹ ∈ conjClosure I X := by
    intro a ha y hy
    have hle : conjClosure I X ≤ (conjClosure I X).comap (MulAut.conj a).toMonoidHom := by
      refine conjClosure_le fun x hx i hi => ?_
      show a * (x * i * x⁻¹) * a⁻¹ ∈ conjClosure I X
      have ha' : x⁻¹ * a * x ∈ A := by
        have := (Subgroup.mem_normalizer_iff.mp (hXA (X.inv_mem hx)) a).mp ha
        simpa using this
      have h2 : (x⁻¹ * a * x) * i * (x⁻¹ * a * x)⁻¹ ∈ I :=
        (Subgroup.mem_normalizer_iff.mp (hAI ha') i).mp hi
      have e : x * ((x⁻¹ * a * x) * i * (x⁻¹ * a * x)⁻¹) * x⁻¹ = a * (x * i * x⁻¹) * a⁻¹ := by
        group
      rw [← e]
      exact mem_conjClosure hx h2
    exact hle hy
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨key a ha y, fun hy => ?_⟩
  have := key a⁻¹ (A.inv_mem ha) _ hy
  simpa [mul_assoc] using this

variable [Finite G]

theorem isTISetUnder_of_stmt3_2_5 (h325 : Stmt3_2_5) {T L V₀ : Subgroup G}
    (hfsu : FSU G T L V₀) (hL : L = conjClosure L T) :
    IsTISetUnder (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)) := by
  obtain ⟨-, -, hcases⟩ := h325 G T L V₀ hfsu hL
  rw [← hL]
  rcases hcases with ⟨-, hVM⟩ | ⟨hV, -, -, -, hTI⟩ | ⟨-, -, ⟨t, ht, htN⟩, hall⟩
  · exact isTISetUnder_of_eq_conjClosure hVM
  · rw [← hV]
    exact hTI
  · exact isTISetUnder_of_eq_conjClosure (hall t ht htN).1.symm

theorem isTISetUnder_of_stmt3_2_5_of_le_normalizer (h325 : Stmt3_2_5) {T L V₀ : Subgroup G}
    (hfsu : FSU G T L V₀) (hTL : T ≤ Subgroup.normalizer (L : Set G)) :
    IsTISetUnder (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)) :=
  isTISetUnder_of_stmt3_2_5 h325 hfsu (le_antisymm (le_conjClosure L T)
    (conjClosure_le fun _ ht l hl => (Subgroup.mem_normalizer_iff.mp (hTL ht) l).mp hl))

theorem lieModel_autOn_fsuV_of_case3_2_6_iii {T L V₀ : Subgroup G} (hfsu : FSU G T L V₀)
    (hiii : Case3_2_6_iii T L V₀) : LieModel ↥(autOn L (conjClosure V₀ T)) .PSL 3 2 1 := by
  obtain ⟨-, hLie, -⟩ := hiii
  set V := conjClosure V₀ T with hVdef
  set L₀ := conjClosure L T with hL₀
  set VM := conjClosure V (Subgroup.normalizer (L₀ : Set G)) with hVM
  have hLL₀ : L ≤ L₀ := le_conjClosure L T
  have hTV : T ≤ Subgroup.normalizer (V : Set G) := le_normalizer_conjClosure V₀ T
  have hL₀V : L₀ ≤ Subgroup.normalizer (V : Set G) :=
    le_normalizer_conjClosure_aux hfsu.irrPlus.2.2.1 (le_normalizer_conjClosure L T)
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := hLL₀.trans hL₀V
  have hLVM : L ≤ Subgroup.normalizer (VM : Set G) :=
    (hLL₀.trans Subgroup.le_normalizer).trans (le_normalizer_conjClosure _ _)
  obtain ⟨r, hrs, -⟩ := exists_autOn_restrict hLVM hLV (le_conjClosure V _)
  rcases hLie with ⟨ht, hmodel⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
  swap
  · exact absurd h0 (by norm_num)
  swap
  · exact absurd h0 (by norm_num)
  swap
  · exact absurd h0 (by norm_num)
  obtain ⟨-, hsimp⟩ := CFSG.LieType.Simplicity.fam_PSL_simplicity _ 3 2 1 hmodel
  have hinj : Function.Injective r := by
    rcases hsimp.eq_bot_or_eq_top_of_normal r.ker with hk | hk
    · exact (MonoidHom.ker_eq_bot_iff r).mp hk
    · exfalso
      have hLC : L ≤ Subgroup.centralizer (V : Set G) := by
        intro l hl
        have hmem : A4.actionOn V L hLV ⟨l, hl⟩ ∈ autOn L V :=
          (A4.mem_autOn_iff hLV).mpr ⟨⟨l, hl⟩, rfl⟩
        obtain ⟨a, ha⟩ := hrs ⟨_, hmem⟩
        have ha1 : r a = 1 := (MonoidHom.mem_ker).mp (hk ▸ Subgroup.mem_top a)
        rw [ha1] at ha
        have h1 : A4.actionOn V L hLV ⟨l, hl⟩ = 1 := (congrArg Subtype.val ha).symm
        exact (A4.actionOn_eq_one_iff hLV ⟨l, hl⟩).mp h1
      have hL₀C : L₀ ≤ Subgroup.centralizer (V : Set G) := by
        refine conjClosure_le fun t ht l hl => ?_
        rw [Subgroup.mem_centralizer_iff]
        intro v hv
        have hv' : t⁻¹ * v * t⁻¹⁻¹ ∈ V :=
          (Subgroup.mem_normalizer_iff.mp (hTV (T.inv_mem ht)) v).mp hv
        have hc : t⁻¹ * v * t * l = l * (t⁻¹ * v * t) := by
          have := Subgroup.mem_centralizer_iff.mp (hLC hl) _ (by simpa using hv')
          exact this
        calc v * (t * l * t⁻¹) = t * (t⁻¹ * v * t * l) * t⁻¹ := by group
          _ = t * (l * (t⁻¹ * v * t)) * t⁻¹ := by rw [hc]
          _ = t * l * t⁻¹ * v := by group
      have hV₀ : V₀ ≤ V := le_conjClosure V₀ T
      have hcomm : ⁅V₀, L₀⁆ = ⊥ := by
        rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
        intro v hv
        rw [Subgroup.mem_centralizer_iff]
        intro l hl
        exact (Subgroup.mem_centralizer_iff.mp (hL₀C hl) v (hV₀ hv)).symm
      exact hfsu.irrPlus.2.1 (hfsu.irrPlus.2.2.2.1.symm.trans hcomm)
  let e := MulEquiv.ofBijective r ⟨hinj, hrs⟩
  obtain ⟨hadm, K, hK, hKf, hcard, ⟨e'⟩⟩ := hmodel
  exact Or.inl ⟨ht, hadm, K, hK, hKf, hcard, ⟨e.symm.trans e'⟩⟩

end CFSG.Quasithin.H13
