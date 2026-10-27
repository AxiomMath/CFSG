module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem uc22p22na_le_of_sylow_two {K S N X : Subgroup G}
    (hS : CFSG.ABGLocalTools.IsSylowOf 2 S K) {n : ℕ} (hN : N.relIndex K = 2 ^ n)
    (hSX : S ≤ X) (hNX : K ⊓ N ≤ X) : K ≤ X := by
  have hodd : ¬ 2 ∣ S.relIndex K := (CFSG.ABGLocalTools.isSylowOf_iff.1 hS).2.2
  have h1 : X.relIndex K ∣ S.relIndex K := Subgroup.relIndex_dvd_of_le_left K hSX
  have h2 : X.relIndex K ∣ 2 ^ n := by
    rw [← hN]
    refine Subgroup.index_dvd_of_le fun x hx => ?_
    exact hNX ⟨x.2, hx⟩
  have hcop : Nat.Coprime (X.relIndex K) (2 ^ n) :=
    Nat.Coprime.pow_right n
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 fun h => hodd (h.trans h1)).symm
  exact Subgroup.relIndex_eq_one.1 (Nat.Coprime.eq_one_of_dvd hcop h2)

theorem uc22p22na_centralizer_of_conj {M Z K : Subgroup G} (hMK : M ≤ normalizer (K : Set G))
    (hKZ : K ≤ centralizer (Z : Set G)) :
    K ≤ centralizer ((⨆ m : M, Z.map (MulAut.conj (m : G)).toMonoidHom : Subgroup G) : Set G) := by
  rw [← Subgroup.le_centralizer_iff]
  refine iSup_le fun m => ?_
  rintro _ ⟨z, hz, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  have hk' : (m : G)⁻¹ * k * m ∈ K := by
    simpa using (Subgroup.mem_normalizer_iff.1 (hMK (M.inv_mem m.2)) k).1 hk
  have hc : (m : G)⁻¹ * k * m * z = z * ((m : G)⁻¹ * k * m) :=
    Subgroup.mem_centralizer_iff.1 (hKZ hk') z hz |>.symm
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  calc k * ((m : G) * z * (m : G)⁻¹) = (m : G) * ((m : G)⁻¹ * k * m * z) * (m : G)⁻¹ := by group
    _ = (m : G) * (z * ((m : G)⁻¹ * k * m)) * (m : G)⁻¹ := by rw [hc]
    _ = (m : G) * z * (m : G)⁻¹ * k := by group

theorem uc22p22na_twoReduced_iSup_conj {M T Z : Subgroup G}
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M) (hZ : Z ≤ centralizer (T : Set G)) :
    TwoReduced M (⨆ m : M, Z.map (MulAut.conj (m : G)).toMonoidHom) := by
  intro K hKM hMK _ ⟨n, hn⟩
  have hZV : Z ≤ (⨆ m : M, Z.map (MulAut.conj (m : G)).toMonoidHom : Subgroup G) := fun z hz =>
    le_iSup (fun m : M => Z.map (MulAut.conj (m : G)).toMonoidHom) 1
      (Subgroup.mem_map.2 ⟨z, hz, by simp⟩)
  refine uc22p22na_centralizer_of_conj hMK ?_
  refine uc22p22na_le_of_sylow_two (hT.inf_of_le_normalizer hKM hMK) hn ?_ ?_
  · intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact (Subgroup.mem_centralizer_iff.1 (hZ hz) x hx.1).symm
  · exact fun x hx => Subgroup.centralizer_le (SetLike.coe_subset_coe.2 hZV) hx.2

theorem uc22p22na_le_sylow_of_normal {M T V : Subgroup G}
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M) (hVM : V ≤ M) (hMV : M ≤ normalizer (V : Set G))
    (hV : IsPGroup 2 V) : V ≤ T := by
  obtain ⟨Q, hQ⟩ := hT.exists_sylow_eq_subgroupOf
  haveI : (V.subgroupOf M).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hVM).2 hMV
  have hV' : IsPGroup 2 (V.subgroupOf M) := hV.comap_subtype
  intro v hv
  have h : (⟨v, hVM hv⟩ : M) ∈ (Q : Subgroup M) := hV'.le_sylow_of_normal Q hv
  rwa [hQ] at h

theorem uc22p22na_le_T_of_inCalV (D : Data G) {V : Subgroup G} (hV : InCalV D.M V) : V ≤ D.T :=
  uc22p22na_le_sylow_of_normal D.sylowM hV.2.1 hV.2.2.1
    fun g => ⟨1, Subtype.ext (by simpa using hV.2.2.2.2 (g : G) g.2)⟩

theorem uc22p22na_inf_center_ne_bot {T V : Subgroup G} (hT : IsPGroup 2 T) (hVT : V ≤ T)
    (hTV : T ≤ normalizer (V : Set G)) (hV : V ≠ ⊥) :
    V ⊓ (T ⊓ centralizer (T : Set G)) ≠ ⊥ := by
  have : Group.IsNilpotent T := hT.isNilpotent
  have hnormal : (V.subgroupOf T).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hTV
  have hne : V.subgroupOf T ≠ ⊥ := by
    intro h
    apply hV
    rw [← Subgroup.map_subgroupOf_eq_of_le hVT, h, Subgroup.map_bot]
  obtain ⟨⟨y, hy⟩, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
  have hyC : (y : G) ∈ centralizer (T : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hy.2 ⟨t, ht⟩)
  intro h
  have hmem : (y : G) ∈ V ⊓ (T ⊓ centralizer (T : Set G)) := ⟨hy.1, y.2, hyC⟩
  rw [h, Subgroup.mem_bot] at hmem
  exact hy1 (Subtype.ext (Subtype.ext hmem))

theorem uc22p22na_twoReduced_of_irr (D : Data G) {V : Subgroup G} (hV : InCalV D.M V)
    (hirr : IrrOn D.M V) : TwoReduced D.M V := by
  have hMV : D.M ≤ normalizer (V : Set G) := hV.2.2.1
  obtain ⟨⟨z, hz⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1
    (uc22p22na_inf_center_ne_bot D.sylowM.isPGroup (uc22p22na_le_T_of_inCalV D hV)
      (D.sylowM.le.trans hMV) hV.1)
  have hz1' : z ≠ 1 := fun h => hz1 (Subtype.ext h)
  intro K hKM hMK _ ⟨n, hn⟩
  have hKz : K ≤ centralizer ({z} : Set G) := by
    refine uc22p22na_le_of_sylow_two (D.sylowM.inf_of_le_normalizer hKM hMK) hn ?_ ?_
    · intro x hx
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.1 hz.2.2 x hx.1
    · intro x hx
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.1 hx.2 z hz.1).symm
  have hzK : z ∈ centralizer (K : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    exact fun k hk => Subgroup.mem_centralizer_singleton_iff.1 (hKz hk)
  have hWM : ∀ m ∈ D.M, ∀ w ∈ V ⊓ centralizer (K : Set G),
      m * w * m⁻¹ ∈ V ⊓ centralizer (K : Set G) := by
    intro m hm w hw
    refine Subgroup.mem_inf.2 ⟨(Subgroup.mem_normalizer_iff.1 (hMV hm) w).1 hw.1, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have hk' : m⁻¹ * k * m ∈ K := by
      simpa using (Subgroup.mem_normalizer_iff.1 (hMK (D.M.inv_mem hm)) k).1 hk
    have hc := Subgroup.mem_centralizer_iff.1 hw.2 _ hk'
    calc k * (m * w * m⁻¹) = m * ((m⁻¹ * k * m) * w) * m⁻¹ := by group
      _ = m * (w * (m⁻¹ * k * m)) * m⁻¹ := by rw [hc]
      _ = m * w * m⁻¹ * k := by group
  have hMW : D.M ≤ normalizer ((V ⊓ centralizer (K : Set G) : Subgroup G) : Set G) := by
    intro m hm
    rw [Subgroup.mem_normalizer_iff]
    intro w
    refine ⟨hWM m hm w, fun h => ?_⟩
    simpa [mul_assoc] using hWM m⁻¹ (D.M.inv_mem hm) _ h
  rcases hirr _ inf_le_left hMW with h | h
  · exfalso
    have hzW : z ∈ (⊥ : Subgroup G) := h ▸ (⟨hz.1, hzK⟩ : z ∈ V ⊓ centralizer (K : Set G))
    exact hz1' (Subgroup.mem_bot.1 hzW)
  · refine Subgroup.le_centralizer_iff.1 fun v hv => ?_
    exact (h.symm ▸ hv : v ∈ V ⊓ centralizer (K : Set G)).2

end CFSG.LocalAnalysis.UniquenessCase.UC22
