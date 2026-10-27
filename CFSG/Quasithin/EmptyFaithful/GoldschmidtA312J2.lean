module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312J2Model
public import CFSG.Quasithin.Background.A312SporGen
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListFamilies
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListAlt7

public section

namespace CFSG.Quasithin.A312J2

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native.A312L
open CFSG.QuasithinUnique.Ch1.SporLat CFSG.Quasithin.E2P.SporB

theorem lFamily_eq_sup_of_isExt {X : Type} [Group X] [Finite X] {T B : Subgroup X}
    (hB : B ∈ lFamily T) (hperf : ⁅B ⊔ T, B ⊔ T⁆ = B ⊔ T)
    (hext : IsExt ↥(B ⊔ T) (fun V _ => IsExtraspecial2 2 V) (fun Z _ => IsAlt 5 Z)) :
    B = B ⊔ T := by
  obtain ⟨V, hVn, ⟨hVe, hVcard⟩, ⟨e⟩⟩ := hext
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hVsolv : Group.IsSolvable ↥V := by
    have h2 : IsPGroup 2 ↥V := IsExtraspecial.isPGroup 2 ↥V
    have := h2.isNilpotent
    infer_instance
  have hpc : perfectCore (B ⊔ T) = B ⊔ T := perfectCore_eq_self_of_perfect hperf
  let eP : ↥(perfectCore (B ⊔ T)) ≃* ↥(B ⊔ T) := MulEquiv.subgroupCongr hpc
  let g : ↥(perfectCore (B ⊔ T)) →* alternatingGroup (Fin 5) :=
    e.toMonoidHom.comp ((QuotientGroup.mk' V).comp eP.toMonoidHom)
  have hg : Function.Surjective g :=
    e.surjective.comp ((QuotientGroup.mk'_surjective V).comp eP.surjective)
  have hsolv : Group.IsSolvable g.ker := by
    let φ : g.ker →* ↥V :=
      (eP.toMonoidHom.comp g.ker.subtype).codRestrict V fun x => by
        have hx := x.2
        rw [MonoidHom.mem_ker] at hx
        have : (QuotientGroup.mk' V) (eP (x : ↥(perfectCore (B ⊔ T)))) = 1 :=
          e.injective (hx.trans e.map_one.symm)
        exact (QuotientGroup.eq_one_iff _).mp this
    have hφ : Function.Injective φ := by
      intro x y hxy
      have h1 : eP (x : ↥(perfectCore (B ⊔ T))) = eP (y : ↥(perfectCore (B ⊔ T))) :=
        congrArg Subtype.val hxy
      exact Subtype.ext (eP.injective h1)
    exact Group.isSolvable_of_isSolvable_injective hφ
  have := Seven.alt5_simple
  have hBeq := lFamily_eq_perfectCore hB Seven.alt5_nonabelian g hg hsolv
  rwa [hpc] at hBeq

theorem false_of_solvable_member {Γ : Type} [Group Γ] [Finite Γ] {S B Y : Subgroup Γ}
    (hB : B ∈ lFamily S) (hY : B ⊔ S = Y) (hs : Group.IsSolvable ↥Y) : False :=
  CFSG.Quasithin.A312S.not_isSolvable_sup hB (hY ▸ hs)

theorem nonempty_top_equiv {Γ A : Type} [Group Γ] [Group A] (e : Γ ≃* A) :
    Nonempty (↥(⊤ : Subgroup Γ) ≃* A) :=
  ⟨Subgroup.topEquiv.trans e⟩

theorem j2_case_three
    {B : Subgroup ↥CFSG.Sporadic.J2.J}
    (hB : B ∈ lFamily j2CtxA.S) (hY : B ⊔ j2CtxA.S = j2CtxA.Y 3) : A312Case B ⊤ := by
  obtain ⟨hext, hperf⟩ := j2_Y3_ext
  rw [← hY] at hext hperf
  have hBeq := lFamily_eq_sup_of_isExt hB hperf hext
  have hB' : IsExt ↥B (fun V _ => IsExtraspecial2 2 V) (fun Z _ => IsAlt 5 Z) := by
    rw [hBeq]
    exact hext
  have hJ2 : IsSporadic .J2 ↥(⊤ : Subgroup ↥CFSG.Sporadic.J2.J) :=
    @nonempty_top_equiv ↥CFSG.Sporadic.J2.J _ inferInstance inferInstance
      CFSG.Sporadic.Bridge.J2.nativeEquiv.symm
  iterate 14 right
  left
  exact ⟨hB', hJ2⟩

theorem a312For_J2
    (hq : CFSG.IsQuasisimple ↥CFSG.Sporadic.J2.J) :
    A312For ↥CFSG.Sporadic.J2.J := by
  refine CFSG.Quasithin.A312S.a312For_of_members hq j2A_sylow (lat_all j2CtxA j2A_hL)
    fun j hj B hB hY => ?_
  have hj5 : j < 5 := by simpa using hj
  have hc := j2A_card hj5
  have h23 : ∀ {a b : ℕ}, Nat.card (j2CtxA.Y j) = 2 ^ a * 3 ^ b → False := fun h =>
    false_of_solvable_member hB hY
      (CFSG.Quasithin.A312S.isSolvable_of_card_pq Nat.prime_two Nat.prime_three (by norm_num) h)
  interval_cases j
  · exact (h23 (a := 7) (b := 0) (by rw [hc]; rfl)).elim
  · exact (h23 (a := 7) (b := 1) (by rw [hc]; rfl)).elim
  · exact (h23 (a := 7) (b := 2) (by rw [hc]; rfl)).elim
  · exact j2_case_three hB hY
  · exact (h23 (a := 7) (b := 1) (by rw [hc]; rfl)).elim

theorem a312For_of_equiv_native {N Γ : Type} [Group N] [Group Γ] [Finite Γ] (e : N ≃* Γ)
    (h : CFSG.IsQuasisimple Γ → A312For Γ) (X : Type) [Group X] [Finite X]
    (hq : CFSG.IsQuasisimple X) (hX : Nonempty (X ≃* N)) : A312For X := by
  obtain ⟨f⟩ := hX
  let e' : X ≃* Γ := f.trans e
  exact A312For.of_mulEquiv e' (h (CFSG.LocalCores.isQuasisimple_of_mulEquiv e' hq))

theorem famJ2_holds :
    FamJ2 := by
  intro X _ _ hq hX
  exact @a312For_of_equiv_native CFSG.Blueprint.NativeSporadic.J2 ↥CFSG.Sporadic.J2.J inferInstance
    inferInstance inferInstance CFSG.Sporadic.Bridge.J2.nativeEquiv a312For_J2 X _ _ hq hX

end CFSG.Quasithin.A312J2
