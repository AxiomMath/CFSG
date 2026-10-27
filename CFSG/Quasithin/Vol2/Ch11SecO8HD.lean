module

public import CFSG.Quasithin.Vol2.Ch11SecO8HB
public import CFSG.Quasithin.Vol2.Ch11SecE44Nat
public import CFSG.Quasithin.Vol2.Ch11SecE44Pre

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecD

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13

namespace O8H

variable {G : Type} [Group G] [Finite G]

theorem exists_isHallTwoPrimeOf {S B : Subgroup G} (hSB : S ≤ B)
    (hBS : B ≤ Subgroup.normalizer (S : Set G)) (hS : IsPGroup 2 S) (hodd : Odd (S.relIndex B)) :
    ∃ D : Subgroup G, QuasithinUnique.Lin2.IsHallTwoPrimeOf D B := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hN : (S.subgroupOf B).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hSB).mpr hBS
  obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp hS
  have hNcard : Nat.card (S.subgroupOf B) = 2 ^ j := by
    rw [← hj]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSB).toEquiv
  have hodd' : Odd (S.subgroupOf B).index := hodd
  obtain ⟨H, hH⟩ := Subgroup.exists_right_complement'_of_coprime (N := S.subgroupOf B)
    (by rw [hNcard]; exact (Nat.coprime_two_left.mpr hodd').pow_left j)
  refine ⟨H.map B.subtype, Subgroup.map_subtype_le _, ?_, j, ?_⟩
  · rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _), ← hH.symm.index_eq_card]
    exact hodd'
  · rw [Subgroup.relIndex, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _), hH.index_eq_card,
      hNcard]

theorem exists_isHallTwoPrimeOf_inf_normalizer {T : Subgroup G} (hT : quasithinIsSylowTwo T)
    (J : Subgroup G) : ∃ D : Subgroup G,
      QuasithinUnique.Lin2.IsHallTwoPrimeOf D (J ⊓ Subgroup.normalizer (T : Set G)) := by
  set B := J ⊓ Subgroup.normalizer (T : Set G) with hB
  have hBT : B ≤ Subgroup.normalizer (T : Set G) := inf_le_right
  refine exists_isHallTwoPrimeOf (S := T ⊓ B) inf_le_right
    (fun b hb => Subgroup.inf_normalizer_le_normalizer_inf ⟨hBT hb, Subgroup.le_normalizer hb⟩)
    (hT.1.to_le inf_le_left) ?_
  rw [Subgroup.inf_relIndex_right, ← relIndex_sup_eq hBT]
  have h2 : ¬ 2 ∣ T.relIndex (B ⊔ T) := fun h2 =>
    hT.2 (h2.trans (Subgroup.relIndex_dvd_index_of_le le_sup_right))
  exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp h2)

theorem le_normalizer_conjClosure_of {Z H X : Subgroup G}
    (hX : ∀ h ∈ H, X ≤ Subgroup.normalizer
      ((Z.map (MulAut.conj h).toMonoidHom : Subgroup G) : Set G)) :
    X ≤ Subgroup.normalizer (conjClosure Z H : Set G) := by
  intro x hx
  have key : (conjClosure Z H).map (MulAut.conj x).toMonoidHom ≤ conjClosure Z H := by
    rw [conjClosure, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨_, ⟨h, hh, z, hz, rfl⟩, rfl⟩
    have h1 : h * z * h⁻¹ ∈ Z.map (MulAut.conj h).toMonoidHom := ⟨z, hz, rfl⟩
    obtain ⟨z', hz', he⟩ := (Subgroup.mem_normalizer_iff.mp (hX h hh hx) _).mp h1
    change x * (h * z * h⁻¹) * x⁻¹ ∈ conjClosure Z H
    rw [← he]
    exact mem_conjClosure hh hz'
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  exact Subgroup.eq_of_le_of_card_ge key
    (by rw [Subgroup.card_map_of_injective (MulAut.conj x).injective])

omit [Finite G] in
theorem conj_mem_centralizer {V : Subgroup G} {x c : G}
    (hx : x ∈ Subgroup.normalizer (V : Set G)) (hc : c ∈ Subgroup.centralizer (V : Set G)) :
    x * c * x⁻¹ ∈ Subgroup.centralizer (V : Set G) :=
  (Subgroup.mem_normalizer_iff.mp ((Subgroup.normal_subgroupOf_iff_le_normalizer
    (Subgroup.centralizer_le_normalizer _)).mp
      (Subgroup.normal_subgroupOf_centralizer_normalizer _) hx) c).mp hc

variable {T L I V₁ X : Subgroup G} {n : ℕ}

theorem exists_conj_centralized_torus (hT44 : SecE.Facts44) (h331 : Stmt3_3_1)
    (h1102 : Stmt11_0_2) (h1103 : Stmt11_0_3) (h : Hyp11 G T L I n)
    (hcV : fsuV T I ⊓ Subgroup.centralizer (L : Set G) = ⊥) (hV₁ : IsVi T L I n 1 V₁)
    (hX : IsCartanX T L X) {J₀ D : Subgroup G}
    (hJ₀ : J₀ ≤ Subgroup.centralizer (V₁ : Set G) ⊓
      sectionCentralizer (KOf L V₁ V₁) (pCoreOf 2 (KOf L V₁ V₁)))
    (hXJ₀ : X ≤ Subgroup.normalizer (J₀ : Set G))
    (hD : QuasithinUnique.Lin2.IsHallTwoPrimeOf D (J₀ ⊓ Subgroup.normalizer (T : Set G)))
    (hDq : Nat.Coprime (Nat.card D) (2 ^ n - 1)) : ∃ u ∈ J₀,
      X ≤ Subgroup.centralizer ((D.map (MulAut.conj u).toMonoidHom : Subgroup G) : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hDJ : D ≤ J₀ := hD.1.trans inf_le_left
  have hDL : D ≤ Subgroup.normalizer (L : Set G) :=
    (hD.1.trans inf_le_right).trans (SecA.normalizer_T_le h331 h)
  obtain ⟨⟨z, hzV₁⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp (SecA.IsVi.ne_bot h hV₁ le_rfl)
  have hz1' : z ≠ 1 := fun h' => hz1 (Subtype.ext h')
  have hDz : D ≤ Subgroup.centralizer ({z} : Set G) := fun d hd =>
    Subgroup.mem_centralizer_iff.mpr fun w hw => by
      rw [Set.mem_singleton_iff.mp hw]
      exact Subgroup.mem_centralizer_iff.mp (hJ₀ (hDJ hd)).1 z hzV₁
  have hDV : D ≤ Subgroup.normalizer (fsuV T I : Set G) :=
    SecE.le_normalizer_fsuV_of_le h1103 h (SecA.IsVi.le_fsuV hV₁ hzV₁) hz1' hDL hDz
  have hDC : D ≤ Subgroup.centralizer (fsuV T I : Set G) := fun d hd => by
    have hdY := hJ₀ (hDJ hd)
    have hdV₁ : d ∈ Subgroup.normalizer (V₁ : Set G) :=
      Subgroup.centralizer_le_normalizer _ hdY.1
    refine SecE.mem_centralizer_of_odd hT44 h1102 h hcV hV₁ (hDL hd) (hDV hd)
      (mem_sectionCentralizer_lOf (mem_normalizer_lOf (hDL hd) hdV₁) hdY.2) ?_
    have hod : orderOf d ∣ Nat.card D := Subgroup.orderOf_dvd_natCard D hd
    exact ⟨orderOf d, hD.2.1.of_dvd_nat hod, hDq.coprime_dvd_left hod, pow_orderOf_eq_one d⟩
  have hXL : X ≤ L := fun x hx => (hX.1 hx).1
  have hPp : IsPGroup 2 ↥(pCoreOf 2 L ⊓ J₀) :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L).to_le inf_le_left
  have hDP : D ≤ Subgroup.normalizer ((pCoreOf 2 L ⊓ J₀ : Subgroup G) : Set G) := fun d hd =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L (hDL hd),
        Subgroup.le_normalizer (hDJ hd)⟩
  have hXP : X ≤ Subgroup.normalizer ((pCoreOf 2 L ⊓ J₀ : Subgroup G) : Set G) := fun x hx =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L (hXL hx), hXJ₀ hx⟩
  have hDX : ∀ d ∈ D, ∀ x ∈ X, d * x * d⁻¹ * x⁻¹ ∈ pCoreOf 2 L ⊓ J₀ := by
    intro d hd x hx
    have hxL := hXL hx
    have hxV : x ∈ Subgroup.normalizer (fsuV T I : Set G) := SecA.L_le_normalizer_fsuV h hxL
    have h1 : x * d⁻¹ * x⁻¹ ∈ J₀ :=
      (Subgroup.mem_normalizer_iff.mp (hXJ₀ hx) _).mp (J₀.inv_mem (hDJ hd))
    have hmem : d * x * d⁻¹ * x⁻¹ = d * (x * d⁻¹ * x⁻¹) := by group
    refine ⟨?_, hmem ▸ J₀.mul_mem (hDJ hd) h1⟩
    rw [← SecA.centralizer_eq_pCoreOf h1102 h]
    refine ⟨L.mul_mem ((Subgroup.mem_normalizer_iff.mp (hDL hd) x).mp hxL) (L.inv_mem hxL), ?_⟩
    rw [hmem]
    exact Subgroup.mul_mem _ (hDC hd) (conj_mem_centralizer hxV (Subgroup.inv_mem _ (hDC hd)))
  obtain ⟨u, hu, hXu⟩ := exists_conj_centralized hPp hD.2.1 hX.2.1 hDP hXP hDX
  exact ⟨u, hu.2, hXu⟩

end O8H

end CFSG.Quasithin.Vol2.Ch11.SecD
