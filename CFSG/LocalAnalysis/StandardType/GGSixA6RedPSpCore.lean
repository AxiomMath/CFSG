module

public import CFSG.LocalAnalysis.StandardType.GGSixA6RedCenter
public import CFSG.LocalAnalysis.StandardType.GGSixA6RedSpStatedX
public import CFSG.LocalAnalysis.StandardType.GGSixA6RedPEqThree
public import CFSG.LocalAnalysis.ComponentInitial.DerivedFixedLayer
public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.StandardType.A6Red

open CFSG.Assembly CFSG.Blueprint CFSG.Assembly.LowTwoRank
open LinearMap (BilinForm)

private theorem ggA6sp_map_centralizer_mulEquiv {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (s : Set G) :
    (Subgroup.centralizer s).map e.toMonoidHom = Subgroup.centralizer (e '' s) := by
  refine le_antisymm (Subgroup.map_centralizer_le_centralizer_image s e.toMonoidHom) ?_
  intro h hh
  rw [Subgroup.mem_map]
  refine ⟨e.symm h, ?_, by simp⟩
  rw [Subgroup.mem_centralizer_iff] at hh ⊢
  intro x hx
  have h1 : e x * h = h * e x := hh (e x) ⟨x, hx, rfl⟩
  apply e.injective
  rw [map_mul, map_mul, e.apply_symm_apply]
  exact h1

section Genuine

theorem ggA6_PSp_core
    : GGA6PSpCore := by
  intro X _ _ n f ψ p G₀ B₁ D J L x hr hk hlie hp hp2 hcop hBN hdiag hab hDB hDcard hJc
    hxD hx1 hLG hLc hJL hDL hmk hA6
  obtain ⟨_, hBG⟩ := ggA6_center_le .PSp (Or.inl rfl) X n f ψ p G₀ B₁ hr hk hlie hp hp2
    hcop hBN hdiag hab
  have hDG : D ≤ G₀ := hDB.trans hBG
  have hxG : x ∈ G₀ := hDG hxD
  have hadm : StatedLieAdmissible .PSp n 2 f := LieModel.admissible hlie
  have hcenterK : Subgroup.center (ggU .PSp n f).K = ⊥ := by
    exact CFSG.ClassicalGroups.Symplectic.center_statedSp_eq_bot_of_charP_two (m := n)
      (F := GaloisField 2 f) (by have := hadm.2.2.1; omega)
  have hkerbot : ψ.ker = ⊥ := le_bot_iff.mp (hk.trans_eq hcenterK)
  have hinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    exact hkerbot
  let e : (ggU .PSp n f).K ≃* ↥G₀ :=
    (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hr)
  let x' : ↥G₀ := ⟨x, hxG⟩
  let D' : Subgroup ↥G₀ := D.subgroupOf G₀
  let J' : Subgroup ↥G₀ := J.subgroupOf G₀
  let L' : Subgroup ↥G₀ := L.subgroupOf G₀
  have hD' : IsElemAbelian p D' :=
    CFSG.Open.IsElemAbelian.subgroupOf (CFSG.Open.IsElemAbelian.mono hab hDB) G₀
  have hDcard' : Nat.card D' = p ^ 2 := by
    rw [← hDcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDG).toEquiv
  have hJ' : IsComponentOf J' (Subgroup.centralizer (D' : Set ↥G₀)) := by
    have hC : (G₀ ⊓ Subgroup.centralizer (D : Set X)).subgroupOf G₀ =
        Subgroup.centralizer (D' : Set ↥G₀) := by
      ext g
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_iff,
        Subgroup.mem_centralizer_iff]
      constructor
      · rintro ⟨-, hc⟩ d hd
        exact Subtype.ext (hc (d : X) hd)
      · rintro hc
        exact ⟨g.2, fun d hd => congrArg Subtype.val (hc ⟨d, hDG hd⟩ hd)⟩
    have hmain : IsComponentOf ((J.subgroupOf G₀).map G₀.subtype)
        (((G₀ ⊓ Subgroup.centralizer (D : Set X)).subgroupOf G₀).map G₀.subtype) := by
      rwa [Subgroup.map_subgroupOf_eq_of_le (hJc.1.trans inf_le_left),
        Subgroup.map_subgroupOf_eq_of_le inf_le_left]
    have h' := (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_iff
      (f := G₀.subtype) G₀.subtype_injective).1 hmain
    rwa [hC] at h'
  have hL' : IsComponentOf L' (Subgroup.centralizer ({x'} : Set ↥G₀)) := by
    have hC : (G₀ ⊓ Subgroup.centralizer ({x} : Set X)).subgroupOf G₀ =
        Subgroup.centralizer ({x'} : Set ↥G₀) := by
      ext g
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
        Subgroup.mem_centralizer_singleton_iff]
      exact ⟨fun h => Subtype.ext h.2, fun h => ⟨g.2, congrArg Subtype.val h⟩⟩
    have hmain : IsComponentOf ((L.subgroupOf G₀).map G₀.subtype)
        (((G₀ ⊓ Subgroup.centralizer ({x} : Set X)).subgroupOf G₀).map G₀.subtype) := by
      rwa [Subgroup.map_subgroupOf_eq_of_le hLG, Subgroup.map_subgroupOf_eq_of_le inf_le_left]
    have h' := (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_iff
      (f := G₀.subtype) G₀.subtype_injective).1 hmain
    rwa [hC] at h'
  have hJL' : J' ≤ L' := fun j hj => hJL hj
  have hA6' : Nonempty (↥J' ≃* alternatingGroup (Fin 6)) :=
    hA6.elim fun eA => ⟨(Subgroup.subgroupOfEquivOfLe (hJc.1.trans inf_le_left)).trans eA⟩
  have hx'D : x' ∈ D' := hxD
  have hDL' : ¬ D' ≤ Subgroup.centralizer (L' : Set ↥G₀) := by
    rintro h
    apply hDL
    intro d hd
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have hd' : (⟨d, hDG hd⟩ : ↥G₀) ∈ D' := hd
    exact congrArg Subtype.val
      (Subgroup.mem_centralizer_iff.mp (h hd') (⟨l, hLG hl⟩ : ↥G₀) hl)
  let P : Subgroup (StatedSp n (GaloisField 2 f)) := D'.map e.symm.toMonoidHom
  let Jk : Subgroup (StatedSp n (GaloisField 2 f)) := J'.map e.symm.toMonoidHom
  let Lk : Subgroup (StatedSp n (GaloisField 2 f)) := L'.map e.symm.toMonoidHom
  let xk : StatedSp n (GaloisField 2 f) := e.symm x'
  have hcentD : (Subgroup.centralizer (D' : Set ↥G₀)).map e.symm.toMonoidHom
      = Subgroup.centralizer (P : Set (StatedSp n (GaloisField 2 f))) := by
    rw [ggA6sp_map_centralizer_mulEquiv]
    rfl
  have hcentX : (Subgroup.centralizer ({x'} : Set ↥G₀)).map e.symm.toMonoidHom
      = Subgroup.centralizer ({xk} : Set (StatedSp n (GaloisField 2 f))) := by
    rw [ggA6sp_map_centralizer_mulEquiv, Set.image_singleton]
    rfl
  have hcentLk : (Subgroup.centralizer (L' : Set ↥G₀)).map e.symm.toMonoidHom
      = Subgroup.centralizer (Lk : Set (StatedSp n (GaloisField 2 f))) := by
    rw [ggA6sp_map_centralizer_mulEquiv]
    rfl
  have hJk : IsComponentOf Jk (Subgroup.centralizer (P : Set (StatedSp n (GaloisField 2 f)))) := by
    have h := (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_iff
      (f := e.symm.toMonoidHom) e.symm.injective).2 hJ'
    rwa [hcentD] at h
  have hLk : IsComponentOf Lk (Subgroup.centralizer ({xk} : Set (StatedSp n (GaloisField 2 f)))) := by
    have h := (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_iff
      (f := e.symm.toMonoidHom) e.symm.injective).2 hL'
    rwa [hcentX] at h
  have hxPk : xk ∈ P := Subgroup.mem_map.mpr ⟨x', hx'D, rfl⟩
  have hJLk : Jk ≤ Lk := Subgroup.map_mono hJL'
  have hPLk : ¬ P ≤ Subgroup.centralizer (Lk : Set (StatedSp n (GaloisField 2 f))) := by
    rw [← hcentLk]
    change ¬ D'.map e.symm.toMonoidHom
      ≤ (Subgroup.centralizer (L' : Set ↥G₀)).map e.symm.toMonoidHom
    rw [Subgroup.map_le_map_iff_of_injective e.symm.injective]
    exact hDL'
  have hoddP : Odd (Nat.card P) := by
    change Odd (Nat.card (D'.map e.symm.toMonoidHom))
    rw [Subgroup.card_map_of_injective (K := D') (f := e.symm.toMonoidHom)
      e.symm.injective, hDcard']
    exact (hp.odd_of_ne_two hp2).pow
  have habP : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a := by
    have hcomm : IsMulCommutative P := (CFSG.Open.IsElemAbelian.map hD' e.symm.toMonoidHom).1
    intro a ha b hb
    exact congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : P) ⟨b, hb⟩)
  have hA6k : Nonempty (↥Jk ≃* alternatingGroup (Fin 6)) :=
    hA6'.elim fun eA =>
      ⟨(J'.equivMapOfInjective e.symm.toMonoidHom e.symm.injective).symm.trans eA⟩
  obtain ⟨hF2, m, hm3, hmn, hLmK⟩ :=
    ggA6_sp_core_stated (F := GaloisField 2 f) n P hoddP habP xk hxPk Jk Lk hJk hLk hJLk hPLk hA6k
  have hcF : Nat.card (GaloisField 2 f) = 2 ^ f :=
    GaloisField.card 2 f (by have := hadm.2.1; omega)
  have hpoweq : 2 ^ f = 2 := hcF.symm.trans hF2
  have hf1 : f = 1 :=
    Nat.pow_right_injective (le_refl 2) (hpoweq.trans (pow_one 2).symm)
  have hLm' : LieModel ↥L' .PSp m 2 1 :=
    LieModel.of_mulEquiv (L'.equivMapOfInjective e.symm.toMonoidHom e.symm.injective).symm hLmK
  have hLm : LieModel ↥L .PSp m 2 1 :=
    LieModel.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hLG) hLm'
  have hp3 : p = 3 := ggA6_p_eq_three m hLm p hp hmk
  exact ⟨hp3, hf1, by omega, m, hm3, hLm⟩

end Genuine

end CFSG.StandardType.A6Red
