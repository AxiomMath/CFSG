module

public import CFSG.Quasithin.Vol2.Ch12Sec7Statements
public import CFSG.Sporadic.Schreier.MathieuOddCoreM24
import CFSG.Adapters.StatedClassicalSmallOrders

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint

namespace S127

theorem card_of_statedPSL {X : Type} [Group X] {k p e : ℕ} (hk : 0 < k)
    (h : Assembly.LowTwoRank.StatedClassicalModel X .PSL k p e) :
    Nat.card X = ((p ^ e) ^ (k * (k - 1) / 2) * ∏ i ∈ Finset.Icc 2 k, ((p ^ e) ^ i - 1)) /
      k.gcd (p ^ e - 1) :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl hk h

theorem card_of_lieModel_psl_five_two {X : Type} [Group X] (h : LieModel X .PSL 5 2 1) :
    Nat.card X = 9999360 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_five_two (h.statedClassicalModel (by decide))

variable {G : Type} [Group G]

theorem ne_one_of_relIndex {L : Subgroup G} {t : G} {n : ℕ}
    (h : (Subgroup.centralizer ({t} : Set G)).relIndex L = n) (hn : n ≠ 1) : t ≠ 1 := by
  rintro rfl
  have : Subgroup.centralizer ({(1 : G)} : Set G) = ⊤ := by
    ext x
    simp [Subgroup.mem_centralizer_singleton_iff]
  rw [this, Subgroup.relIndex_top_left] at h
  exact hn h.symm

theorem dvd_card_of_hatA6Quot {L V : Subgroup G} (h : HatA6Quot L V) : 1080 ∣ Nat.card L := by
  obtain ⟨_, -, h3, ⟨e⟩⟩ := h
  have hA6 : Nat.card ↥(alternatingGroup (Fin 6)) = 360 := by
    rw [nat_card_alternatingGroup, Nat.card_fin]
    decide
  have hQ := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (Subgroup.center (↥L ⧸ (Subgroup.centralizer (V : Set G)).subgroupOf L))
  rw [Nat.card_congr e.toEquiv, hA6, h3] at hQ
  rw [((Subgroup.centralizer (V : Set G)).subgroupOf L).card_eq_card_quotient_mul_card_subgroup,
    hQ]
  exact Dvd.intro _ rfl

theorem not_lieModel_psl_five_two [Finite G] {T L V : Subgroup G} (h : Hyp1271 G T L V) :
    ¬ LieModel G .PSL 5 2 1 := by
  intro hL
  have h27 : 27 ∣ Nat.card G :=
    (Dvd.dvd.trans (by norm_num) (dvd_card_of_hatA6Quot h.hatA6)).trans L.card_subgroup_dvd_card
  rw [card_of_lieModel_psl_five_two hL] at h27
  norm_num at h27

end S127

namespace S127

open CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu CFSG.Sporadic.Schreier.Native

theorem conjClass_conj {M : Type*} [Group M] {H : Subgroup M} {c : M} (hc : c ∈ H) (r : M) :
    conjClass H (c * r * c⁻¹) = conjClass H r := by
  ext x
  constructor
  · rintro ⟨d, hd, rfl⟩
    exact ⟨d * c, H.mul_mem hd hc, by group⟩
  · rintro ⟨d, hd, rfl⟩
    exact ⟨d * c⁻¹, H.mul_mem hd (H.inv_mem hc), by group⟩

theorem card_centralizerIn_m24_le
    {u : Equiv.Perm (Fin 24)} (hu : u ∈ NativeSporadic.M24)
    (ho : orderOf u = 2) : Nat.card (centralizerIn NativeSporadic.M24 u) ≤ 21504 := by
  have hn : (24 : ℕ) < 2 ^ 32 := by norm_num
  obtain ⟨hok, hsz, -⟩ := m24_oddcore_cover
  rw [m24InvReps_eq] at hok hsz
  simp only [repSizes, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hsz
  obtain ⟨hr1, hro1, hK1, hKc1, -⟩ := m24_rep_data1
  obtain ⟨hr2, hro2, hK2, hKc2, -⟩ := m24_rep_data2
  have hA : m24gA ∈ m24Certificate.originalSubgroup := m24_gens_mem _ (by simp)
  have hB : m24gB ∈ m24Certificate.originalSubgroup := m24_gens_mem _ (by simp)
  have h := exists_conj_of_repsOK hn m24Certificate m24Certificate_check
    (pairTables_spec hn hA hB) 1 (fun h hh => by rw [inv_one, one_mul, mul_one]; exact hh)
    (by norm_num) [m24Rep1, m24Rep2] (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨by simpa using hr1, hro1⟩
      · exact ⟨by simpa using hr2, hro2⟩) 40000 hok
  rw [m24Certificate_originalSubgroup] at h hK1 hK2
  obtain ⟨hcov, hcl⟩ := h
  have hC1 : centralizerIn NativeSporadic.M24 m24Rep1 = m24CentQ1.originalSubgroup := by
    refine centralizerIn_eq_of_le _ _ hK1 (hcl _ (by simp)) ?_
    rw [hsz.1, hKc1, m24_card]
  have hC2 : centralizerIn NativeSporadic.M24 m24Rep2 = m24CentQ2.originalSubgroup := by
    refine centralizerIn_eq_of_le _ _ hK2 (hcl _ (by simp)) ?_
    rw [hsz.2, hKc2, m24_card]
  obtain ⟨r, hr, c, hc, rfl⟩ := hcov u (by simpa using hu) ho
  have hos := ncard_conjClass_mul_card NativeSporadic.M24 (c * r * c⁻¹)
  have hos' := ncard_conjClass_mul_card NativeSporadic.M24 r
  rw [conjClass_conj hc] at hos
  have hpos : 0 < (conjClass NativeSporadic.M24 r).ncard := by
    rcases Nat.eq_zero_or_pos (conjClass NativeSporadic.M24 r).ncard with h0 | h0
    · rw [h0, zero_mul] at hos'
      exact absurd hos'.symm Nat.card_pos.ne'
    · exact h0
  have heq : Nat.card (centralizerIn NativeSporadic.M24 (c * r * c⁻¹)) =
      Nat.card (centralizerIn NativeSporadic.M24 r) :=
    Nat.eq_of_mul_eq_mul_left hpos (hos.trans hos'.symm)
  rw [heq]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [hC1, hKc1]
    norm_num
  · rw [hC2, hKc2]

theorem card_centralizer_le_of_m24
    {X : Type} [Group X] (φ : X ≃* NativeSporadic.M24) {t : X}
    (ht : orderOf t = 2) : Nat.card (Subgroup.centralizer ({t} : Set X)) ≤ 21504 := by
  have hmap : ((Subgroup.centralizer ({t} : Set X)).map
      ((NativeSporadic.M24.subtype).comp φ.toMonoidHom)) =
      centralizerIn NativeSporadic.M24 ((φ t : NativeSporadic.M24) : Equiv.Perm (Fin 24)) := by
    ext x
    rw [mem_centralizerIn]
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff] at hy
      refine ⟨(φ y).2, ?_⟩
      simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
        Subgroup.coe_subtype]
      rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul, hy]
    · rintro ⟨hx, hxt⟩
      refine ⟨φ.symm ⟨x, hx⟩, ?_, ?_⟩
      · rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
        apply φ.injective
        rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
        exact Subtype.ext hxt
      · simp
  have hinj : Function.Injective ((NativeSporadic.M24.subtype).comp φ.toMonoidHom) :=
    (Subgroup.subtype_injective _).comp φ.injective
  rw [← Subgroup.card_map_of_injective hinj, hmap]
  refine card_centralizerIn_m24_le (φ t).2 ?_
  rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, ht]

end S127

end CFSG.Quasithin.H13
