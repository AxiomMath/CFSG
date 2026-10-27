module

public import CFSG.Quasithin.Vol2.Ch11SecO1A
public import CFSG.Quasithin.Vol2.KGNatSp4Flag
public import CFSG.Quasithin.Vol2.Ch11G2Q8Real
public import CFSG.Quasithin.Background.G2
public import CFSG.Quasithin.Vol2.Ch11SecSCartanT3
public import CFSG.Quasithin.Vol2.Ch11SecSFacts

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecO1

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13 SecA SecS
open scoped IsMulCommutative

theorem mem_stabW_bot {W : Type*} [Group W] (τ : MulAut W) : τ ∈ stabW (⊥ : Subgroup W) :=
  fun w => by simp only [Subgroup.mem_bot, MulEquiv.map_eq_one_iff]

theorem mem_stabW_of_mem_normalizer {W : Type*} [Group W] {H P : Subgroup (MulAut W)}
    {Z U : Subgroup W} {q i : ℕ} (hU : IsFlagW H P Z q i U)
    (huniq : ∀ U', IsFlagW H P Z q i U' → U' = U) {τ : MulAut W} (hτH : τ ∈ H)
    (hτP : τ ∈ Subgroup.normalizer (P : Set (MulAut W))) (hτZ : τ ∈ stabW Z) :
    τ ∈ stabW U := by
  refine mem_stabW_of_map_eq (huniq _ (isFlagW_map hU hτZ
    (fun h hh => H.mul_mem (H.mul_mem hτH hh) (H.inv_mem hτH)) fun g hg => ?_))
  have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hτP) g).mp hg
  simpa using this

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

theorem tL_eq_sup (hS : SecD.NatSetting11 G T L I n) :
    TL T L = pCoreOf 2 (L ⊔ T) ⊔ (T ⊓ L) := by
  have hOT : pCoreOf 2 (L ⊔ T) ≤ T := pCoreOf_two_le_of_isSylowTwoOf
    (isSylowTwoOf_of_quasithinIsSylowTwo hS.sylow le_sup_right)
  have hON : pCoreOf 2 (L ⊔ T) ≤ Subgroup.normalizer (L : Set G) :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 (L ⊔ T)).trans (sup_le Subgroup.le_normalizer hS.normal)
  have h1 := A3.eq_sup_inf_of_le_sup hON (le_inf hOT le_sup_right)
    (inf_le_right.trans (sup_comm L _).le : TL T L ≤ pCoreOf 2 (L ⊔ T) ⊔ L)
  rwa [tL_inf] at h1

theorem conj_mem_inf_of_mem_normalizer (hS : SecD.NatSetting11 G T L I n) {y : G}
    (hyL : y ∈ L) (hyV : y ∈ Subgroup.normalizer (fsuV T I : Set G))
    (hy : conjV (fsuV T I) y hyV ∈
      Subgroup.normalizer (autOn (T ⊓ L) (fsuV T I) : Set (MulAut ↥(fsuV T I))))
    {s : G} (hs : s ∈ T ⊓ L) : y * s * y⁻¹ ∈ T ⊓ L := by
  have hsV := hS.le_normalizer hs.2
  have h1 := (Subgroup.mem_normalizer_iff.mp hy _).mp (conjV_mem_autOn hs hsV)
  rw [← conjV_inv, ← conjV_mul, ← conjV_mul] at h1
  obtain ⟨t, ht, htV, hte⟩ := mem_autOn_iff.mp h1
  have hw : y * s * y⁻¹ ∈ L := L.mul_mem (L.mul_mem hyL hs.2) (L.inv_mem hyL)
  have hc : t⁻¹ * (y * s * y⁻¹) ∈ L ⊓ Subgroup.centralizer (fsuV T I : Set G) :=
    ⟨L.mul_mem (L.inv_mem ht.2) hw, inv_mul_mem_centralizer hte.symm⟩
  rw [inf_centralizer_eq hS] at hc
  have hOT : pCoreOf 2 L ≤ T ⊓ L := pCoreOf_two_le_of_isSylowTwoOf (isSylowTwoOf_inf hS)
  have := (T ⊓ L).mul_mem ht (hOT hc)
  rwa [mul_inv_cancel_left] at this

theorem autOn_borel (hS : SecD.NatSetting11 G T L I n) :
    autOn (L ⊓ Subgroup.normalizer (TL T L : Set G)) (fsuV T I) =
      autOn L (fsuV T I) ⊓
        Subgroup.normalizer (autOn (T ⊓ L) (fsuV T I) : Set (MulAut ↥(fsuV T I))) := by
  apply le_antisymm
  · exact le_inf (autOn_mono inf_le_left) (autOn_le_normalizer fun x hx =>
      mem_normalizer_inf_of_mem hx.1 hx.2)
  · rintro g ⟨hgL, hgN⟩
    obtain ⟨y, hyL, hyV, rfl⟩ := mem_autOn_iff.mp hgL
    have hyN : y ∈ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro s
      refine ⟨conj_mem_inf_of_mem_normalizer hS hyL hyV hgN, fun hs => ?_⟩
      have hyV' := Subgroup.inv_mem _ hyV
      have hgN' : conjV (fsuV T I) y⁻¹ hyV' ∈ Subgroup.normalizer
          (autOn (T ⊓ L) (fsuV T I) : Set (MulAut ↥(fsuV T I))) := by
        rw [conjV_inv _ hyV]
        exact Subgroup.inv_mem _ hgN
      have := conj_mem_inf_of_mem_normalizer hS (L.inv_mem hyL) hyV' hgN' hs
      simpa [mul_assoc] using this
    have hyO : y ∈ Subgroup.normalizer (pCoreOf 2 (L ⊔ T) : Set G) :=
      CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (L ⊔ T) (Subgroup.mem_sup_left hyL)
    have hyT : y ∈ Subgroup.normalizer (TL T L : Set G) := by
      rw [Subgroup.mem_normalizer_iff_map_conj_eq, tL_eq_sup hS, Subgroup.map_sup,
        Subgroup.mem_normalizer_iff_map_conj_eq.mp hyO,
        Subgroup.mem_normalizer_iff_map_conj_eq.mp hyN]
    exact conjV_mem_autOn (Subgroup.mem_inf.mpr ⟨hyL, hyT⟩) hyV

theorem cartan_inf_centralizer (hS : SecD.NatSetting11 G T L I n) {X : Subgroup G}
    (hX : IsCartanX T L X) : X ⊓ Subgroup.centralizer (fsuV T I : Set G) = ⊥ := by
  have hle : X ⊓ Subgroup.centralizer (fsuV T I : Set G) ≤ pCoreOf 2 L ⊓ X := by
    rw [← inf_centralizer_eq hS]
    exact le_inf (inf_le_inf_right _ fun x hx => (hX.1 hx).1) inf_le_left
  have := inf_eq_bot_of_odd (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L) hX.2.1
  exact eq_bot_iff.mpr (this ▸ hle)

theorem isHall_autOn_cartan (hS : SecD.NatSetting11 G T L I n) {X : Subgroup G}
    (hX : IsCartanX T L X) :
    QuasithinUnique.Lin2.IsHallTwoPrimeOf (autOn X (fsuV T I))
      (autOn L (fsuV T I) ⊓
        Subgroup.normalizer (autOn (T ⊓ L) (fsuV T I) : Set (MulAut ↥(fsuV T I)))) := by
  have hB : L ⊓ Subgroup.normalizer (TL T L : Set G) ≤ Subgroup.normalizer (fsuV T I : Set G) :=
    inf_le_left.trans hS.le_normalizer
  rw [← autOn_borel hS]
  refine ⟨autOn_mono hX.1, ?_, ?_⟩
  · rw [card_autOn_eq (hX.1.trans hB) (cartan_inf_centralizer hS hX) le_rfl]
    exact hX.2.1
  · obtain ⟨k, hk⟩ := hX.2.2
    have hd := relIndex_autOn_dvd hX.1 hB
    rw [hk] at hd
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
    exact ⟨j, hj⟩

theorem hasUniqueFlag (hS : SecD.NatSetting11 G T L I n) :
    HasUniqueFlagW (autOn L (fsuV T I)) (autOn (T ⊓ L) (fsuV T I)) ⊥ (2 ^ n) := by
  have := isMulCommutative hS
  have hn : 2 ≤ n := hS.one_lt
  rcases realizes_cases hS with ⟨K, _, _, hK, π, hπ⟩ | ⟨K, _, _, hK, π, hπ⟩ |
    ⟨K, _, _, hK, π, hπ⟩
  · exact KGNat.factFlagSL3_holds K n hn hK _ (sq_eq_one hS) _ _ π hπ _ (isSylowTwoOf_P hS)
  · exact KGNat.factFlagSp4_holds K n hn hK _ (sq_eq_one hS) _ _ π hπ _ (isSylowTwoOf_P hS)
  · exact G2Q8.factFlagG2_holds K n hn hK _ (sq_eq_one hS) _ _ π hπ _ (isSylowTwoOf_P hS)

theorem cartan_le_normalizer_Vi (hS : SecD.NatSetting11 G T L I n) {i : ℕ}
    (hi : i = 1 ∨ i = 2 ∨ i = 3) {U X : Subgroup G} (hU : IsVi T L I n i U)
    (hX : IsCartanX T L X) : X ≤ Subgroup.normalizer (U : Set G) := by
  intro x hx
  have hxV : x ∈ Subgroup.normalizer (fsuV T I : Set G) := hS.le_normalizer (hX.1 hx).1
  have hmem := (isHall_autOn_cartan hS hX).1 (conjV_mem_autOn hx hxV)
  have hflag := isFlagW_of_isVi hS hU
  obtain ⟨U₁, U₂, U₃, h₁, h₂, h₃, -, -, hu₁, hu₂, hu₃⟩ := hasUniqueFlag hS
  have huniq : ∀ U', IsFlagW (autOn L (fsuV T I)) (autOn (T ⊓ L) (fsuV T I)) ⊥ (2 ^ n) i U' →
      U' = U.subgroupOf (fsuV T I) := by
    intro U' hU'
    rcases hi with rfl | rfl | rfl
    · exact (hu₁ _ hU').trans (hu₁ _ hflag).symm
    · exact (hu₂ _ hU').trans (hu₂ _ hflag).symm
    · exact (hu₃ _ hU').trans (hu₃ _ hflag).symm
  have hst := mem_stabW_of_mem_normalizer hflag huniq hmem.1 hmem.2 (mem_stabW_bot _)
  exact (conjV_mem_stabW_iff (SecA.IsVi.le_fsuV hU) hxV).mp hst

end CFSG.Quasithin.Vol2.Ch11.SecO1
