module

public import CFSG.Quasithin.Vol2.Ch10SecQ4FS8
public import CFSG.Quasithin.Vol2.Ch10SecQ4FS7

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecF.C10P4F

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem isSylowTwoOf_T0 (hyp : Hyp10 G T L I) : IsSylowTwoOf (Ch10.T0 T L) (fsuL0 T L) := by
  have hloc := hyp.fsu.maximal.1
  have hT : IsSylowTwoOf T (L ⊔ T) := ⟨le_sup_right, hloc.1, hloc.2.2.1⟩
  exact B6.isSylowTwoOf_inf_normal hT (SecA.fsuL0_le_sup T L)
    (sup_le ((SecA.le_fsuL0 T L).trans Subgroup.le_normalizer) (SecA.le_fsuM T L))

theorem charTwo_fsuL0 (hyp : Hyp10 G T L I) : CharTwo (fsuL0 T L) :=
  A4.charTwo_of_normal le_sup_left (sup_le Subgroup.le_normalizer (SecA.le_fsuM T L))
    (SecA.charTwo_L0T hyp)

theorem mem_L_or_of_block (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (hyp : Hyp10 G T L I) (h2 : Ch10.Case10_1_1Two T L I)
    {H : Subgroup G} (hH : IsHStar T (fsuM T L) H) {K : Subgroup G} (hKc : K ∈ cComp H)
    (hKs : IsShort2 K) (hKa : IsAltType K 5) {q : G} (hqK : q ∈ K) (hq3 : orderOf q = 3)
    (hqL0 : q ∈ fsuL0 T L) (hqT0 : q ∈ Subgroup.normalizer (Ch10.T0 T L : Set G)) {t : G}
    (ht : t ∈ T) (htn : t ∉ Subgroup.normalizer (L : Set G)) : q ∈ L ∨ t * q * t⁻¹ ∈ L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq3' : q ^ 3 = 1 := by rw [← hq3]; exact pow_orderOf_eq_one q
  obtain ⟨⟨e⟩, -⟩ := h2
  obtain ⟨Ψ, α, hΨs, hΨk, hΨL, hΨt⟩ := SecB.exists_coordQ h37 h38 hyp e ht htn
  have hO2 : IsPGroup 2 (pCoreOf 2 (fsuL0 T L)) :=
    CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hOT0 : pCoreOf 2 (fsuL0 T L) ≤ Ch10.T0 T L := SecA.pCoreOf_fsuL0_le_T0 hyp.fsu.sylow
  have hOL : pCoreOf 2 (fsuL0 T L) ≤ Subgroup.normalizer (L : Set G) :=
    (hOT0.trans (SecA.T0_le_T1 hyp.fsu.maximal.1)).trans inf_le_right
  have key : ∀ (y : G) (hy : y ∈ fsuL0 T L), y ^ 3 = 1 → (Ψ ⟨y, hy⟩).2 = 1 → y ∈ L := by
    intro y hy hy3 hy2
    obtain ⟨lb, hlb⟩ := e.surjective (Ψ ⟨y, hy⟩).1
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective lb
    have hl0 : (l : G) ∈ fsuL0 T L := SecA.le_fsuL0 T L l.2
    have hΨl := hΨL l hl0 l.2
    have hdiff : Ψ (⟨l, hl0⟩⁻¹ * ⟨y, hy⟩) = 1 := by
      rw [map_mul, map_inv, hΨl]
      refine Prod.ext ?_ ?_
      · rw [Prod.fst_mul, Prod.fst_inv, ← hlb]
        exact inv_mul_cancel _
      · rw [Prod.snd_mul, Prod.snd_inv, hy2]
        simp
    have hk := (hΨk _).mp hdiff
    have hyLO : y ∈ L ⊔ pCoreOf 2 (fsuL0 T L) := by
      have e1 : y = (l : G) * ((l : G)⁻¹ * y) := by group
      rw [e1]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left l.2) (Subgroup.mem_sup_right hk)
    exact mem_of_mem_sup_of_pow_three hOL hO2 hyLO hy3
  set q' : ↥(fsuL0 T L) := ⟨q, hqL0⟩ with hq'
  by_cases hb : (Ψ q').2 = 1
  · exact Or.inl (key q hqL0 hq3' hb)
  by_cases ha : (Ψ q').1 = 1
  · right
    have htM := SecA.le_fsuM T L ht
    have hy : t * q * t⁻¹ ∈ fsuL0 T L := (Subgroup.mem_normalizer_iff.mp htM q).mp hqL0
    have hyt : t⁻¹ * (t * q * t⁻¹) * t ∈ fsuL0 T L := by
      have e1 : t⁻¹ * (t * q * t⁻¹) * t = q := by group
      rw [e1]; exact hqL0
    have h1 := hΨt ⟨t * q * t⁻¹, hy⟩ hyt
    have e1 : (⟨t⁻¹ * (t * q * t⁻¹) * t, hyt⟩ : ↥(fsuL0 T L)) = q' :=
      Subtype.ext (by show t⁻¹ * (t * q * t⁻¹) * t = q; group)
    rw [e1] at h1
    have h2' : (Ψ ⟨t * q * t⁻¹, hy⟩).2 = 1 := by
      have h3 := congrArg Prod.fst h1
      rw [ha] at h3
      exact (MulEquiv.map_eq_one_iff α).mp h3.symm
    refine key _ hy ?_ h2'
    rw [conj_pow, hq3', mul_one, mul_inv_cancel]
  · exfalso
    have hT0 := isSylowTwoOf_T0 hyp
    have hc16 : (Subgroup.centralizer ({q} : Set G)).relIndex (Ch10.T0 T L) ≤ 16 :=
      relIndex_centralizer_T0_le hH.1.1 hKc hKs hKa hqK hq3 inf_le_left hT0.2.1 hqT0
    have hΨq3 : (Ψ q') ^ 3 = 1 := by
      rw [← map_pow]
      have : q' ^ 3 = 1 := Subtype.ext (by simpa using hq3')
      rw [this, map_one]
    have hCO : Ch10.T0 T L ⊓ Subgroup.centralizer ({q} : Set G) ≤ pCoreOf 2 (fsuL0 T L) := by
      rintro x ⟨hxT0, hxC⟩
      have hxL0 : x ∈ fsuL0 T L := hxT0.2
      obtain ⟨k, hk⟩ := hT0.2.1 ⟨x, hxT0⟩
      have hxk : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
      have hcomm : Ψ ⟨x, hxL0⟩ * Ψ q' = Ψ q' * Ψ ⟨x, hxL0⟩ := by
        rw [← map_mul, ← map_mul]
        congr 1
        exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hxC)
      have hΨx : (Ψ ⟨x, hxL0⟩) ^ 2 ^ k = 1 := by
        rw [← map_pow]
        have : (⟨x, hxL0⟩ : ↥(fsuL0 T L)) ^ 2 ^ k = 1 := Subtype.ext (by simpa using hxk)
        rw [this, map_one]
      have h1 : (Ψ ⟨x, hxL0⟩).1 = 1 :=
        eq_one_of_commute_three (mul_self_eq_one_of_two_elt (k := k)
          (by rw [← Prod.pow_fst, hΨx, Prod.fst_one]))
          (by rw [← Prod.pow_fst, hΨq3, Prod.fst_one]) ha
          (by have := congrArg Prod.fst hcomm; simpa using this)
      have h2 : (Ψ ⟨x, hxL0⟩).2 = 1 :=
        eq_one_of_commute_three (mul_self_eq_one_of_two_elt (k := k)
          (by rw [← Prod.pow_snd, hΨx, Prod.snd_one]))
          (by rw [← Prod.pow_snd, hΨq3, Prod.snd_one]) hb
          (by have := congrArg Prod.snd hcomm; simpa using this)
      exact (hΨk _).mp (Prod.ext h1 h2)
    have hN : Ch10.T0 T L ⊓ Subgroup.centralizer ({q} : Set G) ≤
        Subgroup.normalizer (pCoreOf 2 (fsuL0 T L) : Set G) :=
      fun x hx => CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _ hx.1.2
    have h1 := relIndex_centralizer_eq_mul hOT0 hN
    rw [sup_eq_left.mpr hCO] at h1
    have hker : (pCoreOf 2 (fsuL0 T L)).subgroupOf (fsuL0 T L) = Ψ.ker := by
      ext y
      rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker, hΨk]
    have hidx : (pCoreOf 2 (fsuL0 T L)).relIndex (Ch10.T0 T L) = 16 := by
      have h2 := Subgroup.relIndex_map_map Ψ ⊥ ((Ch10.T0 T L).subgroupOf (fsuL0 T L))
      rw [Subgroup.map_bot, Subgroup.relIndex_bot_left, bot_sup_eq, ← hker,
        sup_eq_left.mpr (Subgroup.subgroupOf_mono _ hOT0),
        Subgroup.relIndex_subgroupOf inf_le_right] at h2
      rw [← h2]
      exact card_sylow_A5_prod (SecB.isSylowTwoOf_map_of_surjective hT0 Ψ hΨs)
    have hc2 : 2 ≤ (Subgroup.centralizer ({q} : Set G)).relIndex (pCoreOf 2 (fsuL0 T L)) := by
      have h0 : (Subgroup.centralizer ({q} : Set G)).relIndex (pCoreOf 2 (fsuL0 T L)) ≠ 0 :=
        Subgroup.index_ne_zero_of_finite
      have h1' : (Subgroup.centralizer ({q} : Set G)).relIndex (pCoreOf 2 (fsuL0 T L)) ≠ 1 := by
        intro h
        have hle := Subgroup.relIndex_eq_one.mp h
        have hqc : q ∈ fsuL0 T L ⊓ Subgroup.centralizer (pCoreOf 2 (fsuL0 T L) : Set G) :=
          ⟨hqL0, Subgroup.mem_centralizer_iff.mpr fun o ho =>
            Subgroup.mem_centralizer_singleton_iff.mp (hle ho)⟩
        have hqO := charTwo_fsuL0 hyp hqc
        obtain ⟨n, hn⟩ := hO2 ⟨q, hqO⟩
        have hqn : q ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
        have h3 := orderOf_dvd_of_pow_eq_one hqn
        rw [hq3] at h3
        have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
          (Nat.prime_three.dvd_of_dvd_pow h3)
        omega
      omega
    rw [h1, hidx] at hc16
    omega

end CFSG.Quasithin.Vol2.Ch10.SecF.C10P4F
