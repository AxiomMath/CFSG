module

public import CFSG.Quasithin.Vol2.Ch10SecQ3CX
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Quasithin.Background.F1Models
public import CFSG.Quasithin.Vol2.Ch10SecB3Ind

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

namespace C11AmS

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique

structure Ctx {G : Type} [Group G] [Finite G] (T L I H K : Subgroup G) (n k : ℕ) (b : G)
    (hel : IsElemAbelian 2 (VZ T H)) (I' : Finset (Subgroup (MulAut (IntMod (VZ T H) hel))))
    (K₀ : Subgroup (MulAut (IntMod (VZ T H) hel))) : Prop where
  h37 : Vol2Native.A37ForSQTKCat
  h38 : Vol2Native.A38ForSQTKCat
  h322 : TmpL6_3_2_2_two
  h331 : Stmt3_3_1
  h3228 : TmpL6_3_2_2_eight
  he23 : E2.E23Statement
  hyp : Hyp10 G T L I
  h1 : Case10_1_1One T L I n
  hH : IsHStar T (fsuM T L) H
  hn1 : 1 < E1.nParam H
  hZH : ⁅quasithinOmegaOneCenter T, H⁆ ≠ ⊥
  hfaith : HallFaithful T L I H
  hk2 : 2 ≤ k
  hKc : K ∈ cComp H
  hHK : H = K ⊔ T
  hKF : ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ k ∧
    Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* Matrix.SpecialLinearGroup (Fin 2) F)
  h2J : twoResidual H ≤ thompsonJ H
  hD : E23Data H T (VZ T H) hel I'
  hK₀ : K₀ ∈ I'
  hnat : E2.IsL2Natural K₀ (fixV (autI hel (twoResidual H))) k ∨ (E2.IsA5Module K₀ ∧ k = 2)
  hKA : autI hel K = oTwoUpper K₀
  hbHM : b ∈ H ⊓ fsuM T L
  hbK : b ∈ K
  hbo : Odd (orderOf b)
  hbk : 2 ^ k - 1 ∣ orderOf b
  hbB0 : b ∈ B0 T L
  hbD : ∃ D : Subgroup G, Lin2.IsHallTwoPrimeOf D (B0 T L) ∧ b ∈ D
  hbZ : b ∉ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)
  hbS : b ∈ Subgroup.normalizer (baum T : Set G)
  hL0J : fsuL0 T L = ⁅fsuL0 T L, thompsonJ T⁆

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

omit [Finite G] in
theorem map_conj_eq_self {H : Subgroup G} {t : G} (ht : t ∈ H) :
    H.map (MulAut.conj t).toMonoidHom = H := by
  apply le_antisymm
  · rintro _ ⟨h, hh, rfl⟩
    exact H.mul_mem (H.mul_mem ht hh) (H.inv_mem ht)
  · intro h hh
    refine ⟨t⁻¹ * h * t, H.mul_mem (H.mul_mem (H.inv_mem ht) hh) ht, ?_⟩
    simp [MulAut.conj_apply, mul_assoc]

end C11AmS

end CFSG.Quasithin.Vol2.Ch10.SecB
