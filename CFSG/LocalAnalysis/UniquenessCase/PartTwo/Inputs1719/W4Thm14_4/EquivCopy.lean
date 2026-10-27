module

public import CFSG.LocalAnalysis.OddStandard.SmallAltFiveRho
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenT7A5
public import CFSG.CGT.PushingUpLit.Glue.NaturalIrred
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13AltModule
public import CFSG.Quasithin.Background.F6CatSmall
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.Quasithin.F6
open CFSG.LocalAnalysis.WeakClosure81
open scoped commutatorElement Pointwise Matrix

theorem exists_equivariant_copy_of_alternatingNatural {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {L A : Subgroup (MulAut W)} {I : Subgroup W}
    (hI : AlternatingNatural L I ⊥ 5) (hAN : A ≤ Subgroup.normalizer (L : Set (MulAut W)))
    (hA : IsPGroup 2 ↥A) :
    ∃ (s : ↥A →* Equiv.Perm (Fin 5)) (φ : ↥(G6.coreMod 5) →* W), Function.Injective φ ∧
      (∀ (a : ↥A) (x : ↥(G6.coreMod 5)), (a : MulAut W) (φ x) = φ (G6.coreAct 5 (s a) x)) ∧
      ∀ a : ↥A, s a = 1 → ∀ l ∈ L, (a : MulAut W) * l = l * (a : MulAut W) := by
  obtain ⟨π, ε, hπs, hHU, hεe⟩ := s15_T7_exists_iso hI
  have hπinj : Function.Injective π := by
    rw [injective_iff_map_eq_one]
    intro γ hγ
    have hact : G6.coreAct 5 γ = 1 := by
      apply MulEquiv.ext
      intro w
      obtain ⟨u, rfl⟩ := ε.surjective w
      have hmem : ((π γ : ↥L) : MulAut W) (u : W) ∈ I := hHU (π γ) u u.2
      have h1 := hεe γ u hmem
      have h2 : ((π γ : ↥L) : MulAut W) (u : W) = (u : W) := by rw [hγ]; rfl
      have h3 : (⟨((π γ : ↥L) : MulAut W) (u : W), hmem⟩ : ↥I) = u := Subtype.ext h2
      rw [h3] at h1
      exact h1.symm
    exact Subtype.ext (s15_T7_coreAct_injective (hact.trans (map_one (G6.coreAct 5)).symm))
  let φL : ↥L ≃* alternatingGroup (Fin 5) :=
    (MulEquiv.ofBijective π ⟨hπinj, hπs⟩).symm
  have hφπ : ∀ l : ↥L, π (φL l) = l := fun l =>
    (MulEquiv.ofBijective π ⟨hπinj, hπs⟩).apply_symm_apply l
  let s : ↥A →* Equiv.Perm (Fin 5) :=
    (CFSG.OddStandard.rhoOf φL).comp (Subgroup.inclusion hAN)
  have hs_apply : ∀ a : ↥A, s a = CFSG.OddStandard.rhoOf φL (Subgroup.inclusion hAN a) :=
    fun _ => rfl
  let H : Subgroup (↥(G6.coreMod 5) →* W) :=
    { carrier := {f | ∀ (l : ↥L) (x : ↥(G6.coreMod 5)),
        f (G6.coreAct 5 ((φL l : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5)) x) =
          (l : MulAut W) (f x)}
      one_mem' := by
        intro l x
        simp
      mul_mem' := by
        intro f g hf hg l x
        simp only [MonoidHom.mul_apply]
        rw [hf l x, hg l x, map_mul]
      inv_mem' := by
        intro f hf l x
        simp only [MonoidHom.inv_apply]
        rw [hf l x, map_inv] }
  let φ₀ : ↥(G6.coreMod 5) →* W := (Subgroup.subtype I).comp (ε.symm : ↥(G6.coreMod 5) →* ↥I)
  have hφ₀H : φ₀ ∈ H := by
    intro l x
    have hu : (l : MulAut W) (ε.symm x : W) ∈ I := hHU l (ε.symm x) (ε.symm x).2
    have h1 : ε ⟨(l : MulAut W) (ε.symm x : W), hu⟩ = G6.coreAct 5 (φL l) x := by
      have h := hεe (φL l) (ε.symm x) ((hφπ l).symm ▸ hu)
      simpa [hφπ l] using h
    have h3 : ε.symm (G6.coreAct 5 (φL l) x) = ⟨(l : MulAut W) (ε.symm x : W), hu⟩ := by
      rw [← h1]
      exact ε.symm_apply_apply _
    show ((ε.symm (G6.coreAct 5 (φL l) x) : ↥I) : W) =
      (l : MulAut W) ((ε.symm x : ↥I) : W)
    rw [h3]
  let ve : ↥(CFSG.QuasithinUnique.evenWeight 5) :=
    ⟨CFSG.CGT.PushingUpLit.Glue.pairVec (0 : Fin 5) 1,
      CFSG.CGT.PushingUpLit.Glue.pairVec_mem_evenWeight (0 : Fin 5) 1⟩
  have hve : ve ≠ 0 := by
    intro h
    have h0 := congrFun (congrArg Subtype.val h) 0
    simp [ve, CFSG.CGT.PushingUpLit.Glue.pairVec] at h0
  let x₀ : ↥(G6.coreMod 5) := s15T7OfEven ve
  have hx1 : x₀ ≠ 1 := fun h =>
    hve (Function.LeftInverse.injective s15_T7_toEven_ofEven (by
      rw [show x₀ = s15T7OfEven ve from rfl,
        show (1 : ↥(G6.coreMod 5)) = s15T7OfEven 0 from rfl] at h
      exact h))
  have hφ₀ne : φ₀ ≠ 1 := by
    intro h
    have hx : φ₀ x₀ = 1 := by
      rw [show φ₀ x₀ = (1 : ↥(G6.coreMod 5) →* W) x₀ from
        congrArg (fun g : ↥(G6.coreMod 5) →* W => g x₀) h]
      rfl
    have hsym : ε.symm x₀ = 1 := by
      apply Subtype.ext
      exact hx
    apply hx1
    have := congrArg ε hsym
    simpa using this
  have hH2 : IsPGroup 2 ↥H := by
    apply isPGroup_two_of_sq_eq_one
    intro f
    apply Subtype.ext
    apply MonoidHom.ext
    intro x
    change (f.1 ^ 2) x = (1 : ↥(G6.coreMod 5) →* W) x
    rw [pow_two, MonoidHom.mul_apply, MonoidHom.one_apply]
    simpa [pow_two] using hW (f.1 x)
  haveI : Finite ↥H :=
    Finite.of_injective (fun f : ↥H => (f.1 : ↥(G6.coreMod 5) → W))
      (fun f g h => Subtype.ext (MonoidHom.ext (congrFun h)))
  haveI : Nontrivial ↥H :=
    ⟨⟨φ₀, hφ₀H⟩, 1, fun h => hφ₀ne (congrArg Subtype.val h)⟩
  let actFun : ↥A → ↥H → ↥H := fun a f =>
    ⟨{ toFun := fun x => (a : MulAut W) (f.1 ((G6.coreAct 5 (s a))⁻¹ x))
       map_one' := by simp
       map_mul' := by
         intro x y
         simp only [map_mul] },
     by
       intro l x
       set ρa : Equiv.Perm (Fin 5) := s a with hρa
       have ha : (a : MulAut W) ∈ Subgroup.normalizer (L : Set (MulAut W)) := hAN a.2
       let l' : ↥L := ⟨(a : MulAut W)⁻¹ * (l : MulAut W) * (a : MulAut W), by
         have hai : (a : MulAut W)⁻¹ ∈ Subgroup.normalizer (L : Set (MulAut W)) :=
           (Subgroup.normalizer (L : Set (MulAut W))).inv_mem ha
         have hmem := (Subgroup.mem_normalizer_iff.mp hai (l : MulAut W)).mp l.2
         simpa using hmem⟩
       have hconj : (a : MulAut W) * (l' : MulAut W) * (a : MulAut W)⁻¹ = (l : MulAut W) := by
         show (a : MulAut W) *
           ((a : MulAut W)⁻¹ * (l : MulAut W) * (a : MulAut W)) * (a : MulAut W)⁻¹ =
             (l : MulAut W)
         group
       have hρa' : ρa = CFSG.OddStandard.rhoOf φL ⟨(a : MulAut W), ha⟩ := rfl
       have hkey : ((φL l' : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5)) =
           ρa⁻¹ * ((φL l : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5)) * ρa := by
         have h := CFSG.OddStandard.rhoOf_transports φL ⟨(a : MulAut W), ha⟩ l' l
           (by simpa using hconj)
         have h' : ((φL l : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5)) =
             (CFSG.OddStandard.rhoOf φL ⟨(a : MulAut W), ha⟩) *
               ((φL l' : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5)) *
               (CFSG.OddStandard.rhoOf φL ⟨(a : MulAut W), ha⟩)⁻¹ := h
         rw [hρa', h']
         group
       have hkeysq : ρa⁻¹ * ((φL l : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5)) =
           ((φL l' : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5)) * ρa⁻¹ := by
         rw [hkey]
         group
       have hcore : (G6.coreAct 5 ρa)⁻¹
           (G6.coreAct 5 ((φL l : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5)) x) =
           G6.coreAct 5 ((φL l' : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5))
             ((G6.coreAct 5 ρa)⁻¹ x) := by
         calc
           (G6.coreAct 5 ρa)⁻¹
               (G6.coreAct 5 ((φL l : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5)) x)
               = G6.coreAct 5 (ρa⁻¹)
                   (G6.coreAct 5 ((φL l : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5)) x) := by
                 rw [← map_inv]
           _ = G6.coreAct 5 (ρa⁻¹ *
                 ((φL l : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5))) x := by
                 rw [map_mul]
                 rfl
           _ = G6.coreAct 5 (((φL l' : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5)) *
                 ρa⁻¹) x := by rw [hkeysq]
           _ = G6.coreAct 5 ((φL l' : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5))
                 (G6.coreAct 5 (ρa⁻¹) x) := by
                 rw [map_mul]
                 rfl
           _ = G6.coreAct 5 ((φL l' : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5))
                 ((G6.coreAct 5 ρa)⁻¹ x) := by
                 rw [map_inv]
       set y : W := f.1 ((G6.coreAct 5 ρa)⁻¹ x) with hy
       show (a : MulAut W) (f.1 ((G6.coreAct 5 ρa)⁻¹
         (G6.coreAct 5 ((φL l : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5)) x))) =
         (l : MulAut W) ((a : MulAut W) (f.1 ((G6.coreAct 5 ρa)⁻¹ x)))
       rw [hcore, f.2 l' ((G6.coreAct 5 ρa)⁻¹ x)]
       have h := congrArg (fun g : MulAut W => g ((a : MulAut W) y)) hconj
       simpa [MulAut.mul_apply, hy] using h⟩
  have h_act_one : ∀ a : ↥A, actFun a (1 : ↥H) = 1 := by
    intro a
    apply Subtype.ext
    apply MonoidHom.ext
    intro x
    simp [actFun]
  have h_one : ∀ f : ↥H, actFun 1 f = f := by
    intro f
    apply Subtype.ext
    apply MonoidHom.ext
    intro x
    simp [actFun]
  have h_mul : ∀ (a b : ↥A) (f : ↥H), actFun (a * b) f = actFun a (actFun b f) := by
    intro a b f
    apply Subtype.ext
    apply MonoidHom.ext
    intro x
    simp [actFun, MulAut.mul_apply, map_mul, mul_inv_rev]
  letI : MulAction ↥A ↥H :=
    { smul := actFun
      one_smul := h_one
      mul_smul := h_mul }
  have hcard_gt : 1 < Nat.card ↥H := Finite.one_lt_card
  have hdvd : 2 ∣ Nat.card ↥H := by
    rcases hH2.card_eq_or_dvd with h | h
    · rw [h] at hcard_gt
      omega
    · exact h
  obtain ⟨f, hfmem, hfne⟩ :=
    hA.exists_fixed_point_of_prime_dvd_card_of_fixed_point (α := ↥H) hdvd
      (a := (1 : ↥H)) (by rw [MulAction.mem_fixedPoints]; exact h_act_one)
  have hf1 : f ≠ 1 := fun h => hfne h.symm
  have hfeq : ∀ a : ↥A, actFun a f = f := MulAction.mem_fixedPoints.mp hfmem
  have hequiv : ∀ (a : ↥A) (x : ↥(G6.coreMod 5)),
      (a : MulAut W) (f.1 x) = f.1 (G6.coreAct 5 (s a) x) := by
    intro a x
    have h := congrArg (fun g : ↥H => g.1 (G6.coreAct 5 (s a) x)) (hfeq a)
    simpa [actFun] using h
  have hfinj : Function.Injective f.1 := by
    rw [injective_iff_map_eq_one]
    intro x hx
    let N : AddSubgroup (Fin 5 → ZMod 2) :=
      { carrier := {v | ∃ y : ↥(G6.coreMod 5), f.1 y = 1 ∧
          Multiplicative.toAdd (y : G6.PermMod 5) = v}
        zero_mem' := ⟨1, map_one f.1, rfl⟩
        add_mem' := by
          rintro v w ⟨y, hy, rfl⟩ ⟨z, hz, rfl⟩
          exact ⟨y * z, by rw [map_mul, hy, hz, mul_one], rfl⟩
        neg_mem' := by
          rintro v ⟨y, hy, rfl⟩
          exact ⟨y⁻¹, by rw [map_inv, hy, inv_one], by simp⟩ }
    have hNΔ : N ≤ CFSG.CGT.PushingUpLit.Glue.evenWeight 5 := by
      rintro v ⟨y, -, rfl⟩
      rw [CFSG.CGT.PushingUpLit.Glue.mem_evenWeight_iff]
      exact y.2
    have hNinv : ∀ σ ∈ alternatingGroup (Fin 5), ∀ v ∈ N,
        CFSG.CGT.PushingUpLit.Glue.permVec σ v ∈ N := by
      rintro σ hσ v ⟨y, hy, rfl⟩
      refine ⟨G6.coreAct 5 σ y, ?_, rfl⟩
      have h := f.2 (φL.symm ⟨σ, hσ⟩) y
      rw [MulEquiv.apply_symm_apply, hy, map_one] at h
      exact h
    rcases CFSG.CGT.PushingUpLit.Glue.altInvariant_eq_bot_or_evenWeight (n := 5)
      (by norm_num) (by norm_num) N hNΔ hNinv with hbot | htop
    · have hv : Multiplicative.toAdd (x : G6.PermMod 5) ∈ N := ⟨x, hx, rfl⟩
      rw [hbot, AddSubgroup.mem_bot] at hv
      exact Subtype.ext (Multiplicative.toAdd.injective hv)
    · exfalso
      apply hf1
      apply Subtype.ext
      apply MonoidHom.ext
      intro y
      have hv : Multiplicative.toAdd (y : G6.PermMod 5) ∈ N := by
        rw [htop]
        exact y.2
      obtain ⟨z, hz, hzy⟩ := hv
      have hzy' : z = y := Subtype.ext (Multiplicative.toAdd.injective hzy)
      rwa [hzy'] at hz
  refine ⟨s, f.1, hfinj, hequiv, ?_⟩
  intro a hsa l hl
  have hmem : Subgroup.inclusion hAN a ∈ (CFSG.OddStandard.rhoOf φL).ker := by
    rw [MonoidHom.mem_ker]
    exact hsa
  have hcent : ((Subgroup.inclusion hAN a : ↥(Subgroup.normalizer (L : Set (MulAut W))))
      : MulAut W) ∈ Subgroup.centralizer (L : Set (MulAut W)) := by
    have h := hmem
    rw [CFSG.OddStandard.rhoOf_ker] at h
    exact Subgroup.mem_subgroupOf.mp h
  have hcomm := (Subgroup.mem_centralizer_iff.mp hcent l hl).symm
  simpa using hcomm

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
