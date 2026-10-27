module

public import CFSG.Quasithin.Vol2.Ch11SecC37B4

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecC

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin.InternalSec
open CFSG.Assembly.LowTwoRank
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem isHallTwoPrimeOf_conj {U X : Subgroup G}
    (hU : QuasithinUnique.Lin2.IsHallTwoPrimeOf U X) {y : G} (hy : y ∈ X) :
    QuasithinUnique.Lin2.IsHallTwoPrimeOf (U.map (MulAut.conj y).toMonoidHom) X := by
  obtain ⟨hUX, hodd, k, hk⟩ := hU
  have hc : Nat.card (U.map (MulAut.conj y).toMonoidHom) = Nat.card U :=
    Subgroup.card_map_of_injective (MulAut.conj y).injective
  have hle : U.map (MulAut.conj y).toMonoidHom ≤ X := by
    rintro _ ⟨u, hu, rfl⟩
    exact X.mul_mem (X.mul_mem hy (hUX hu)) (X.inv_mem hy)
  refine ⟨hle, hc ▸ hodd, k, ?_⟩
  have h1 := Subgroup.relIndex_mul_card (U.map (MulAut.conj y).toMonoidHom) X
  have h2 := Subgroup.relIndex_mul_card U X
  rw [inf_eq_left.mpr hle, hc] at h1
  rw [inf_eq_left.mpr hUX, hk] at h2
  rw [← h2] at h1
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h1

namespace Set37

variable {T L I : Subgroup G} {n : ℕ} {V₁ H : Subgroup G} {g : G} (s : Set37 T L I n V₁ H g)
include s

theorem VZ_inf_centralizer_K (i : Inp37) (hJ : L = ⁅L, thompsonJ T⁆) {D : Subgroup G}
    (hD : QuasithinUnique.Lin2.IsHallTwoPrimeOf D (H ⊓ Subgroup.normalizer (L : Set G))) :
    VZ T H ⊓ Subgroup.centralizer (oTwoUpper H : Set G) = ⊥ := by
  have hZL := s.Z_inf_centralizer_L hJ i.hG16 i.hAS i.hFPF i.hF i.h1102 i.hKF.2.2.2 i.h1122
    i.h1104 i.h1134 i.h1135 i.h1136 i.h331 i.hSN i.hB hD
  obtain ⟨d, hd, hfpf⟩ := s.exists_fpf i hJ hD
  have hdL : d ∈ L := d0Of_le i.h1104 i.h1134 i.h1135 i.h1136 i.hB s.hyp hJ s.hV₁ s.h31 s.hnot
    s.hAT s.hAC hD hd
  have hodd : Odd (orderOf d) := hD.2.1.of_dvd_nat (by
    rw [← Subgroup.orderOf_mk d (d0Of_le_self D hd)]
    exact orderOf_dvd_natCard _)
  have hdK : d ∈ oTwoUpper H := mem_oTwoUpper_of_odd (hD.1 (d0Of_le_self D hd)).1 hodd
  have hZK : ∀ z ∈ quasithinOmegaOneCenter T,
      z ∈ Subgroup.centralizer (oTwoUpper H : Set G) → z = 1 := fun z hz hzK =>
    s.Z_fix hZL hdL hfpf hz (by rw [Subgroup.mem_centralizer_iff.mp hzK d hdK,
      mul_inv_cancel_right])
  by_contra hne
  have hCT : VZ T H ⊓ Subgroup.centralizer (oTwoUpper H : Set G) ≤ T :=
    inf_le_left.trans s.VZ_le_T
  have hTC : T ≤ Subgroup.normalizer
      ((VZ T H ⊓ Subgroup.centralizer (oTwoUpper H : Set G) : Subgroup G) : Set G) :=
    fun t ht => F7.mem_normalizer_inf (le_normalizer_VZ T H (s.T_le ht))
      (le_normalizer_centralizer (s.T_le.trans (le_normalizer_oTwoUpper H)) ht)
  have h1 := SecB.inf_centralizer_ne_bot s.hyp.fsu.sylow.1 hCT hTC hne
  obtain ⟨⟨u, hu⟩, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp h1
  have huZ : u ∈ quasithinOmegaOneCenter T :=
    Subgroup.subset_closure ⟨⟨hCT hu.1, hu.2⟩, s.isElemAbelian_VZ.2 u hu.1.1⟩
  exact hu1 (Subtype.ext (hZK u huZ hu.1.2))

theorem fsuV_le_U (h1102 : Stmt11_0_2)
    (hVL : fsuV T I ⊓ Subgroup.centralizer (L : Set G) = ⊥) :
    fsuV T I ≤ ⁅VZ T (L ⊔ T), L⁆ := by
  obtain ⟨-, -, -, hVL', -, -, -⟩ := SecB.natSetting h1102 s.hyp
  calc fsuV T I = ⁅fsuV T I, L⁆ := hVL'.symm
    _ ≤ ⁅VZ T (L ⊔ T), L⁆ := Subgroup.commutator_mono (s.fsuV_le_W h1102 hVL) le_rfl

theorem card_fix_V_le (i : Inp37) (hVL : fsuV T I ⊓ Subgroup.centralizer (L : Set G) = ⊥) :
    Nat.card ↥(fsuV T I ⊓ Subgroup.centralizer ((T ⊓ L : Subgroup G) : Set G)) ≤ 2 ^ n := by
  obtain ⟨hc, -, -, -, hk⟩ := i.h1102 G T L I n s.hyp
  have hLV : L ≤ Subgroup.normalizer (fsuV T I : Set G) := SecA.L_le_normalizer_fsuV s.hyp
  have hS := CFSG.QuasithinUnique.Setup.isSylowTwoOf_autOn s.sylow_TL hLV
  have hV2 : ∀ w : ↥(fsuV T I), w ^ 2 = 1 := fun w =>
    Subtype.ext (by simpa using (SecA.isElemAbelian_fsuV s.hyp).2 w w.2)
  have hZ1 : Nat.card ↥((Subgroup.centralizer (L : Set G)).subgroupOf (fsuV T I)) = 1 := by
    rw [Subgroup.card_eq_one, eq_bot_iff]
    intro x hx
    have : (x : G) ∈ fsuV T I ⊓ Subgroup.centralizer (L : Set G) :=
      ⟨x.2, Subgroup.mem_subgroupOf.mp hx⟩
    rw [hVL, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.mpr (Subtype.ext this)
  have key : Nat.card ↥(fsuV T I ⊓ Subgroup.centralizer ((T ⊓ L : Subgroup G) : Set G)) ≤
      Nat.card {w : ↥(fsuV T I) // ∀ σ ∈ autOn (T ⊓ L) (fsuV T I), σ w * w⁻¹ ∈
        (Subgroup.centralizer (L : Set G)).subgroupOf (fsuV T I)} := by
    refine Nat.card_le_card_of_injective (fun x => ⟨⟨x, x.2.1⟩, ?_⟩) ?_
    · rintro σ ⟨z, hz, rfl⟩
      have h1 : conjAct (fsuV T I) z ⟨x, x.2.1⟩ = ⟨x, x.2.1⟩ :=
        Subtype.ext ((conjAct_apply_coe _ z _).trans (by
          show (z : G) * x * (z : G)⁻¹ = x
          rw [Subgroup.mem_centralizer_iff.mp x.2.2 z (Subgroup.mem_subgroupOf.mp hz),
            mul_inv_cancel_right]))
      rw [h1, mul_inv_cancel]
      exact Subgroup.one_mem _
    · intro a b hab
      exact Subtype.ext (congrArg (fun w => ((w.1 : ↥(fsuV T I)) : G)) hab)
  rcases hk with ⟨F, _, _, hF, -, π, hπ, -⟩ | ⟨F, _, _, hF, -, π, hπ, -⟩ | ⟨F, _, _, hF, ⟨e⟩, -⟩
  · have := (i.hTS F n s.two_le hF ↥(fsuV T I) hV2 _ _ π hπ _ hS).1
    rw [hZ1, mul_one] at this
    exact this ▸ key
  · have := (i.hTP F n s.two_le hF ↥(fsuV T I) hV2 _ _ π hπ _ hS).1
    rw [hZ1, mul_one] at this
    exact this ▸ key
  · exfalso
    have hk2 : KindG2 L (fsuV T I) n := ⟨F, inferInstance, inferInstance, hF, ⟨e⟩⟩
    rcases s.kind i.h1134 with h1 | h1
    · exact SecA.kind_not_SL3_G2 i.hKF.2.2.2 s.two_le h1 hk2
    · exact SecA.kind_not_Sp4_G2 i.hKF.2.2.2 s.two_le h1 hk2

theorem V₁_eq_inf (i : Inp37) (hVL : fsuV T I ⊓ Subgroup.centralizer (L : Set G) = ⊥) :
    V₁ = fsuV T I ⊓ Subgroup.centralizer ((T ⊓ L : Subgroup G) : Set G) := by
  have hTV₁ := s.inf_le_centralizer_V₁ i.hFC1 i.h1102
  have hle : V₁ ≤ fsuV T I ⊓ Subgroup.centralizer ((T ⊓ L : Subgroup G) : Set G) := fun v hv =>
    ⟨SecA.IsVi.le_fsuV s.hV₁ hv, Subgroup.mem_centralizer_iff.mpr fun p hp =>
      (Subgroup.mem_centralizer_iff.mp (hTV₁ hp) v hv).symm⟩
  have hcard : Nat.card V₁ = 2 ^ n := by
    have := SecA.IsVi.relIndex_eq s.hV₁
    rwa [hVL, Subgroup.relIndex_bot_left, mul_one] at this
  exact Subgroup.eq_of_le_of_card_ge hle (hcard ▸ s.card_fix_V_le i hVL)

end Set37

end CFSG.Quasithin.Vol2.Ch11.SecC
