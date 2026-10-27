module

public import CFSG.Quasithin.Background.G2
public import CFSG.Quasithin.Vol2.Ch11SecSCartanT3

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 SecA

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

theorem tL_eq_sup (h : Hyp11 G T L I n) : TL T L = pCoreOf 2 (L ⊔ T) ⊔ (T ⊓ L) := by
  have hOT : pCoreOf 2 (L ⊔ T) ≤ T := pCoreOf_two_le_of_isSylowTwoOf
    (isSylowTwoOf_of_quasithinIsSylowTwo h.fsu.sylow le_sup_right)
  have hON : pCoreOf 2 (L ⊔ T) ≤ Subgroup.normalizer (L : Set G) :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 (L ⊔ T)).trans (sup_le Subgroup.le_normalizer h.normal)
  have h1 := A3.eq_sup_inf_of_le_sup hON (le_inf hOT le_sup_right)
    (inf_le_right.trans (sup_comm L _).le : TL T L ≤ pCoreOf 2 (L ⊔ T) ⊔ L)
  rwa [tL_inf] at h1

theorem conj_mem_inf_of_mem_normalizer (h1102 : Stmt11_0_2) (h : Hyp11 G T L I n) {y : G}
    (hyL : y ∈ L) (hyV : y ∈ Subgroup.normalizer (fsuV T I : Set G))
    (hy : conjV (fsuV T I) y hyV ∈
      Subgroup.normalizer (autOn (T ⊓ L) (fsuV T I) : Set (MulAut ↥(fsuV T I))))
    {s : G} (hs : s ∈ T ⊓ L) : y * s * y⁻¹ ∈ T ⊓ L := by
  have hL := L_le_normalizer_fsuV h
  have hsV := hL hs.2
  have h1 := (Subgroup.mem_normalizer_iff.mp hy _).mp (conjV_mem_autOn hs hsV)
  rw [← conjV_inv, ← conjV_mul, ← conjV_mul] at h1
  obtain ⟨t, ht, htV, hte⟩ := mem_autOn_iff.mp h1
  have hw : y * s * y⁻¹ ∈ L := L.mul_mem (L.mul_mem hyL hs.2) (L.inv_mem hyL)
  have hc : t⁻¹ * (y * s * y⁻¹) ∈ L ⊓ Subgroup.centralizer (fsuV T I : Set G) :=
    ⟨L.mul_mem (L.inv_mem ht.2) hw, inv_mul_mem_centralizer hte.symm⟩
  rw [centralizer_eq_pCoreOf h1102 h] at hc
  have hOT : pCoreOf 2 L ≤ T ⊓ L := pCoreOf_two_le_of_isSylowTwoOf (isSylowTwoOf_inf_L h)
  have := (T ⊓ L).mul_mem ht (hOT hc)
  rwa [mul_inv_cancel_left] at this

theorem autOn_borel (h1102 : Stmt11_0_2) (h : Hyp11 G T L I n) :
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
      refine ⟨conj_mem_inf_of_mem_normalizer h1102 h hyL hyV hgN, fun hs => ?_⟩
      have hyV' := Subgroup.inv_mem _ hyV
      have hgN' : conjV (fsuV T I) y⁻¹ hyV' ∈ Subgroup.normalizer
          (autOn (T ⊓ L) (fsuV T I) : Set (MulAut ↥(fsuV T I))) := by
        rw [conjV_inv _ hyV]
        exact Subgroup.inv_mem _ hgN
      have := conj_mem_inf_of_mem_normalizer h1102 h (L.inv_mem hyL) hyV' hgN' hs
      simpa [mul_assoc] using this
    have hyO : y ∈ Subgroup.normalizer (pCoreOf 2 (L ⊔ T) : Set G) :=
      CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (L ⊔ T) (Subgroup.mem_sup_left hyL)
    have hyT : y ∈ Subgroup.normalizer (TL T L : Set G) := by
      rw [Subgroup.mem_normalizer_iff_map_conj_eq, tL_eq_sup h, Subgroup.map_sup,
        Subgroup.mem_normalizer_iff_map_conj_eq.mp hyO,
        Subgroup.mem_normalizer_iff_map_conj_eq.mp hyN]
    exact conjV_mem_autOn (Subgroup.mem_inf.mpr ⟨hyL, hyT⟩) hyV

theorem isHall_autOn_cartan (h1102 : Stmt11_0_2) (h : Hyp11 G T L I n) {X : Subgroup G}
    (hX : IsCartanX T L X) :
    QuasithinUnique.Lin2.IsHallTwoPrimeOf (autOn X (fsuV T I))
      (autOn L (fsuV T I) ⊓
        Subgroup.normalizer (autOn (T ⊓ L) (fsuV T I) : Set (MulAut ↥(fsuV T I)))) := by
  have hB : L ⊓ Subgroup.normalizer (TL T L : Set G) ≤ Subgroup.normalizer (fsuV T I : Set G) :=
    inf_le_left.trans (L_le_normalizer_fsuV h)
  rw [← autOn_borel h1102 h]
  refine ⟨autOn_mono hX.1, ?_, ?_⟩
  · rw [card_autOn_eq (hX.1.trans hB) (cartan_inf_centralizer h1102 h hX) le_rfl]
    exact hX.2.1
  · obtain ⟨k, hk⟩ := hX.2.2
    have hd := relIndex_autOn_dvd hX.1 hB
    rw [hk] at hd
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
    exact ⟨j, hj⟩

end CFSG.Quasithin.Vol2.Ch11.SecS
