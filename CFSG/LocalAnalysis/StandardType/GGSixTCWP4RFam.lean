module

public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4RParam
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4ULang
public import CFSG.LieType.Chevalley.GraphFixedD4TorusWords
public import CFSG.LieType.Chevalley.CLSOddToralOrdinaryComponentRootFactor
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4RVec
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4Orbit
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4E6Two
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4Lift

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.LangTorus

section Plane

variable {Lf : Type} [Field Lf] {p : ℕ} [NeZero p] {ζ : Lfˣ} {τ : Tag}

theorem tcExpVec_mul (hζ : IsPrimitiveRoot ζ p) (a b c : Fin τ.rank → Lfˣ)
    (ha : ∀ j, a j ^ p = 1) (hb : ∀ j, b j ^ p = 1) (hc : ∀ j, c j ^ p = 1)
    (habc : ∀ j, c j = a j * b j) :
    tcExpVec hζ c hc = tcExpVec hζ a ha + tcExpVec hζ b hb := by
  funext j
  have hpow : ζ ^ (tcExpVec hζ c hc j).val =
      ζ ^ ((tcExpVec hζ a ha j).val + (tcExpVec hζ b hb j).val) := by
    rw [tcExpVec_pow_val hζ c hc j, pow_add, tcExpVec_pow_val hζ a ha j,
      tcExpVec_pow_val hζ b hb j]
    exact habc j
  have h2 := (tc_pow_eq_iff hζ _ _).1 hpow
  simp only [Nat.cast_add, ZMod.natCast_zmod_val] at h2
  rw [Pi.add_apply]
  exact h2

theorem tcExpVec_eq_zero_iff (hζ : IsPrimitiveRoot ζ p) (a : Fin τ.rank → Lfˣ)
    (ha : ∀ j, a j ^ p = 1) : tcExpVec hζ a ha = 0 ↔ ∀ j, a j = 1 := by
  constructor
  · intro h j
    have hj : tcExpVec hζ a ha j = 0 := by
      have h0 := congrFun h j
      rwa [Pi.zero_apply] at h0
    rw [← tcExpVec_pow_val hζ a ha j, hj, ZMod.val_zero, pow_zero]
  · intro h
    funext j
    have h1 : ζ ^ (tcExpVec hζ a ha j).val = ζ ^ (0 : ℕ) := by
      rw [tcExpVec_pow_val hζ a ha j, pow_zero]
      exact h j
    have h2 := (tc_pow_eq_iff hζ _ _).1 h1
    rw [Nat.cast_zero, ZMod.natCast_zmod_val] at h2
    rw [Pi.zero_apply]
    exact h2

theorem tc_plane_of_hom [Fact p.Prime] {n : ℕ} {G : Type*} [Group G]
    (vv : G → (Fin n → ZMod p)) (hadd : ∀ u u' : G, vv (u * u') = vv u + vv u')
    (h1 : vv 1 = 0) (hinj : Function.Injective vv) (hcard : Nat.card G = p ^ 2) :
    ∃ P : Submodule (ZMod p) (Fin n → ZMod p), Module.finrank (ZMod p) P = 2 ∧
      ∀ v, v ∈ P ↔ ∃ u, vv u = v := by
  have hpow : ∀ (u : G) (k : ℕ), vv (u ^ k) = k • vv u := by
    intro u k
    induction k with
    | zero => rw [pow_zero, h1, zero_smul]
    | succ k ih => rw [pow_succ, hadd, ih, succ_nsmul]
  let P : Submodule (ZMod p) (Fin n → ZMod p) :=
    { carrier := Set.range vv
      add_mem' := by
        rintro _ _ ⟨u, rfl⟩ ⟨u', rfl⟩
        exact ⟨u * u', hadd u u'⟩
      zero_mem' := ⟨1, h1⟩
      smul_mem' := by
        rintro c _ ⟨u, rfl⟩
        refine ⟨u ^ c.val, ?_⟩
        rw [hpow, ← Nat.cast_smul_eq_nsmul (ZMod p) c.val (vv u), ZMod.natCast_zmod_val] }
  refine ⟨P, ?_, fun v => Iff.rfl⟩
  have hPcard : Nat.card P = Nat.card G := Nat.card_range_of_injective hinj
  have hPfin := Module.natCard_eq_pow_finrank (K := ZMod p) (V := ↥P)
  rw [Nat.card_zmod, hPcard, hcard] at hPfin
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  exact (Nat.pow_right_injective hp2 hPfin).symm

theorem exists_tcPlane [Fact p.Prime]
    (hζ : IsPrimitiveRoot ζ p) (Dg : Subgroup (ModGL τ Lf)) (hDcard : Nat.card Dg = p ^ 2)
    (a : ↥Dg → Fin τ.rank → Lfˣ) (ha : ∀ u : ↥Dg, (u : ModGL τ Lf) = rootDiagUnit τ (a u))
    (hap : ∀ u j, a u j ^ p = 1) :
    ∃ P : Submodule (ZMod p) (Fin τ.rank → ZMod p), Module.finrank (ZMod p) P = 2 ∧
      (∀ v, v ∈ P ↔ ∃ u, tcExpVec hζ (a u) (hap u) = v) ∧
      (∀ u u' : ↥Dg, tcExpVec hζ (a (u * u')) (hap (u * u')) =
        tcExpVec hζ (a u) (hap u) + tcExpVec hζ (a u') (hap u')) ∧
      (∀ u : ↥Dg, tcExpVec hζ (a u) (hap u) = 0 → u = 1) := by
  have haMul : ∀ u u' : ↥Dg, a (u * u') = a u * a u' := by
    intro u u'
    have h1 : rootDiagUnit τ (a (u * u')) = rootDiagUnit τ (a u * a u') := by
      rw [rootDiagUnit_mul, ← ha u, ← ha u', ← ha (u * u'), Subgroup.coe_mul]
    exact rootDiagUnit_injective h1
  have ha1 : a 1 = 1 := by
    have h1 : rootDiagUnit τ (a 1) = rootDiagUnit τ 1 := by
      rw [← ha 1, Subgroup.coe_one, rootDiagUnit_one]
    exact rootDiagUnit_injective h1
  have hadd : ∀ u u' : ↥Dg, tcExpVec hζ (a (u * u')) (hap (u * u')) =
      tcExpVec hζ (a u) (hap u) + tcExpVec hζ (a u') (hap u') := fun u u' =>
    tcExpVec_mul hζ (a u) (a u') (a (u * u')) (hap u) (hap u') (hap (u * u'))
      (fun j => congrFun (haMul u u') j)
  have hvv1 : tcExpVec hζ (a 1) (hap 1) = 0 :=
    (tcExpVec_eq_zero_iff hζ (a 1) (hap 1)).2 fun j => congrFun ha1 j
  have hinj : Function.Injective (fun u : ↥Dg => tcExpVec hζ (a u) (hap u)) := by
    intro u u' huu'
    have hfun : a u = a u' := funext fun j => by
      have hj : tcExpVec hζ (a u) (hap u) j = tcExpVec hζ (a u') (hap u') j := congrFun huu' j
      rw [← tcExpVec_pow_val hζ (a u) (hap u) j, ← tcExpVec_pow_val hζ (a u') (hap u') j, hj]
    apply Subtype.ext
    rw [ha u, ha u', hfun]
  obtain ⟨P, hfin, hmem⟩ :=
    tc_plane_of_hom (fun u : ↥Dg => tcExpVec hζ (a u) (hap u)) hadd hvv1 hinj hDcard
  exact ⟨P, hfin, hmem, hadd, fun u hu => hinj (hu.trans hvv1.symm)⟩

end Plane

end CFSG.StandardType.TableCRes


namespace CFSG.StandardType.TableCRes

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.LangTorus

section Kernel

variable {Lf : Type} [Field Lf] {p : ℕ} [NeZero p] {ζ : Lfˣ} {τ : Tag}

theorem kernelRoots_famChar_eq_plane (hζ : IsPrimitiveRoot ζ p) {ι : Type}
    (a : ι → Fin τ.rank → Lfˣ) (hap : ∀ u j, a u j ^ p = 1)
    (P : Submodule (ZMod p) (Fin τ.rank → ZMod p))
    (hP : ∀ v, v ∈ P ↔ ∃ u, tcExpVec hζ (a u) (hap u) = v) :
    kernelRoots (famCharHom a) = kernelRoots (tcChiPl τ p P) := by
  ext γ
  rw [mem_kernelRoots_famChar a,
    mem_kernelRoots_chiQ (τ := τ) p (P : Set (Fin τ.rank → ZMod p)) γ]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun v hv => ?_⟩
    obtain ⟨u, rfl⟩ := (hP v).1 hv
    exact (tcRootChar_eq_one_iff hζ (a u) (hap u) γ).1 (h2 u)
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun u => ?_⟩
    have hmem : tcExpVec hζ (a u) (hap u) ∈ P := (hP _).2 ⟨u, rfl⟩
    exact (tcRootChar_eq_one_iff hζ (a u) (hap u) γ).2
      (h2 (tcExpVec hζ (a u) (hap u)) hmem)

theorem kernelRoots_rootCharHom_eq_line (hζ : IsPrimitiveRoot ζ p) (a : Fin τ.rank → Lfˣ)
    (ha : ∀ j, a j ^ p = 1) :
    kernelRoots (rootCharHom a) = kernelRoots (tcChiLn τ p (tcExpVec hζ a ha)) := by
  ext γ
  rw [kernelRoots_rootCharHom, Set.mem_setOf_eq,
    mem_kernelRoots_chiQ (τ := τ) p ({tcExpVec hζ a ha} : Set (Fin τ.rank → ZMod p)) γ]
  simp only [Set.mem_singleton_iff, forall_eq]
  rw [tcRootChar_eq_one_iff hζ a ha γ]

theorem kernelRoots_famChar_punit_eq (a : Fin τ.rank → Lfˣ) :
    kernelRoots (famCharHom (fun _ : PUnit.{1} => a)) = kernelRoots (rootCharHom a) := by
  ext γ
  rw [mem_kernelRoots_famChar, kernelRoots_rootCharHom, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, h2 PUnit.unit⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun _ => h2⟩

theorem exists_componentRoots_eq {M M' : Type*} [CommGroup M] [CommGroup M']
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M} {χ' : Multiplicative (Fin τ.rank → ℤ) →* M'}
    (h : kernelRoots χ = kernelRoots χ') (i : KernelComponent χ) :
    ∃ j : KernelComponent χ', componentRoots χ i = componentRoots χ' j := by
  obtain ⟨x, rfl⟩ := Quotient.exists_rep i
  have hx' : (x : Fin τ.rank → ℤ) ∈ kernelRoots χ' := h ▸ x.2
  exact ⟨⟦⟨x, hx'⟩⟧, OddToralOrdinary.componentRoots_eq_of_kernelRoots_eq h x.2 hx'⟩

theorem tcFrob_plane
    [IsAlgClosed Lf] {p₀ : ℕ} (hζ : IsPrimitiveRoot ζ p)
    (S : LangSetup τ Lf p₀) {ι : Type} (a : ι → Fin τ.rank → Lfˣ) (hap : ∀ u j, a u j ^ p = 1)
    (hT : ∀ u, rootDiagUnit τ (a u) ∈ S.D.torus) (P : Submodule (ZMod p) (Fin τ.rank → ZMod p))
    (hP : ∀ v, v ∈ P ↔ ∃ u, tcExpVec hζ (a u) (hap u) = v) :
    ∀ v ∈ P, ∀ j : Fin τ.rank,
      ∑ k, (((S.ρ (Pi.single j 1)) k : ℤ) : ZMod p) * v k = ((S.D.q : ℕ) : ZMod p) * v j := by
  intro v hv j
  obtain ⟨u, rfl⟩ := (hP v).1 hv
  exact tc_frobenius hζ S (a u) (hap u) (hT u) j

end Kernel

end CFSG.StandardType.TableCRes

end
