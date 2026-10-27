module

public import CFSG.LocalAnalysis.StandardType.GGSixA6RedDefs
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotLeviSp6
public import CFSG.LocalAnalysis.ComponentInitial.DerivedFixedLayer
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.StandardType.GGSixA6RedCenter
public import CFSG.LocalAnalysis.StandardType.GGSixA6RedF4ClassDefs

public section

namespace CFSG.StandardType.A6Red

open CFSG.Assembly CFSG.Blueprint CFSG.Assembly.LowTwoRank

section Genuine

theorem ggA6_F4_core_of_f_eq_one
    (hCls : GGA6F4ClassInput) (X : Type) [Group X] [Finite X] (n : ℕ)
    (ψ : (ggU .F4 n 1).K →* X)
    (p : ℕ) (G₀ B₁ D J L : Subgroup X) (x : X) :
    ψ.range = G₀ → ψ.ker ≤ Subgroup.center (ggU .F4 n 1).K →
    LieModel (↥G₀ ⧸ Subgroup.center ↥G₀) .F4 n 2 1 → p.Prime → p ≠ 2 →
    ¬ p ∣ Nat.card (Subgroup.centralizer (G₀ : Set X)) →
    B₁ ≤ Subgroup.normalizer (G₀ : Set X) →
    (∀ b ∈ B₁, GGPsiInnerDiag (ggU .F4 n 1).D ψ b) →
    IsElemAbelian p B₁ → D ≤ B₁ → Nat.card D = p ^ 2 →
    IsComponentOf J (G₀ ⊓ Subgroup.centralizer (D : Set X)) →
    x ∈ D → x ≠ 1 → L ≤ G₀ → IsComponentOf L (G₀ ⊓ Subgroup.centralizer {x}) → J ≤ L →
    ¬ D ≤ Subgroup.centralizer (L : Set X) →
    LargeEvenMarking ↥L (fun lab _ _ _ _ _ => LargeEvenSplit p lab) →
    Nonempty (↥J ≃* alternatingGroup (Fin 6)) →
      p = 3 ∧ ∃ m : ℕ, 3 ≤ m ∧ LieModel ↥L .PSp m 2 1 := by
  intro hr hk hlie hp hp2 hcop hBN hdiag hab hDB hDcard hJc hxD hx1 hLG hLc hJL hDL hmk hA6
  obtain ⟨hZ, hBG⟩ := ggA6_center_le .F4 (Or.inr rfl) X n 1 ψ p G₀ B₁ hr hk hlie hp hp2
    hcop hBN hdiag hab
  have hDG : D ≤ G₀ := hDB.trans hBG
  have hxG : x ∈ G₀ := hDG hxD
  have hcenterK : Subgroup.center (ggU .F4 n 1).K = ⊥ := by
    change Subgroup.center ↥(CFSG.Blueprint.Chevalley.adjointGroup .F4
      (GaloisField 2 1)) = ⊥
    exact CFSG.LieType.Chevalley.center_adjointGroup_eq_bot
  have hkerbot : ψ.ker = ⊥ := le_bot_iff.mp (hk.trans_eq hcenterK)
  have hinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    exact hkerbot
  let e : (ggU .F4 n 1).K ≃* ↥G₀ :=
    (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hr)
  haveI : Fact p.Prime := ⟨hp⟩
  have hxord : orderOf x = p := orderOf_eq_prime (hab.2 x (hDB hxD)) hx1
  let x' : ↥G₀ := ⟨x, hxG⟩
  let D' : Subgroup ↥G₀ := D.subgroupOf G₀
  let J' : Subgroup ↥G₀ := J.subgroupOf G₀
  let L' : Subgroup ↥G₀ := L.subgroupOf G₀
  have hx1' : x' ≠ 1 := fun h => hx1 (congrArg Subtype.val h)
  have hx'ord : orderOf x' = p := (Subgroup.orderOf_coe x').symm.trans hxord
  have hD' : IsElemAbelian p D' :=
    CFSG.Open.IsElemAbelian.subgroupOf (CFSG.Open.IsElemAbelian.mono hab hDB) G₀
  have hDcard' : Nat.card D' = p ^ 2 := by
    rw [← hDcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDG).toEquiv
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
  have hJx' : J' ≤ Subgroup.centralizer ({x'} : Set ↥G₀) := hJL'.trans hL'.1
  have hA6' : Nonempty (↥J' ≃* alternatingGroup (Fin 6)) :=
    hA6.elim fun eA => ⟨(Subgroup.subgroupOfEquivOfLe (hJc.1.trans inf_le_left)).trans eA⟩
  have hDJ' : D' ≤ Subgroup.centralizer (J' : Set ↥G₀) := by
    intro d hd
    rw [Subgroup.mem_centralizer_iff]
    intro j hj
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp
      (Subgroup.mem_inf.mp (hJc.1 hj)).2 (d : X) hd).symm
  have hDL' : ¬ D' ≤ Subgroup.centralizer (L' : Set ↥G₀) := by
    rintro h
    apply hDL
    intro d hd
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have hd' : (⟨d, hDG hd⟩ : ↥G₀) ∈ D' := hd
    exact congrArg Subtype.val
      (Subgroup.mem_centralizer_iff.mp (h hd') (⟨l, hLG hl⟩ : ↥G₀) hl)
  have hK2 : Nat.card (GaloisField 2 1) = 2 := by
    rw [GaloisField.card 2 1 (by norm_num)]
    norm_num
  obtain ⟨hp3, ⟨eL⟩⟩ := hCls (GaloisField 2 1) hK2 ↥G₀ e.symm p hp hp2 x' hx'ord
    hx1' D' J' L' hD' hDcard' hxD hJx' hL' hJL' hA6' hDJ' hDL'
  have hLm' : LieModel ↥L' .PSp 3 2 1 :=
    LieModel.of_mulEquiv eL.symm
      (CFSG.SeitzReduction.F4Pilot.lieModel_C3Levi (K := GaloisField 2 1) (f := 1) hK2)
  have hLm : LieModel ↥L .PSp 3 2 1 :=
    LieModel.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hLG) hLm'
  exact ⟨hp3, 3, by norm_num, hLm⟩

end Genuine

end CFSG.StandardType.A6Red
