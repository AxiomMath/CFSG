module

public import CFSG.LocalAnalysis.UniquenessCase.Lie.Suzuki
public import CFSG.LieType.Ree.SuzukiSplitTorusCentralizers
public import CFSG.GroupTheory.SteinbergBKSolvableHallConjugacy
public import CFSG.Assembly.OrderReductions.StrongEmbeddingInheritance
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Blueprint CFSG.LieType.Ree Subgroup

variable {a : ℕ} {K : Type} [Field K] [Finite K]

private theorem uc22r3e5c_map_conj_map {G : Type*} [Group G] (H : Subgroup G) (x y : G) :
    (H.map (MulAut.conj x).toMonoidHom).map (MulAut.conj y).toMonoidHom =
      H.map (MulAut.conj (y * x)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  refine MonoidHom.ext fun z => ?_
  change (MulAut.conj y) ((MulAut.conj x) z) = (MulAut.conj (y * x)) z
  rw [MulAut.conj_apply, MulAut.conj_apply, MulAut.conj_apply]
  group

private theorem uc22r3e5c_conj_mul_hom {G : Type*} [Group G] (x y : G) :
    (MulAut.conj (x * y)).toMonoidHom =
      (MulAut.conj x).toMonoidHom.comp (MulAut.conj y).toMonoidHom := by
  refine MonoidHom.ext fun z => ?_
  change (MulAut.conj (x * y)) z = (MulAut.conj x) ((MulAut.conj y) z)
  rw [MulAut.conj_apply, MulAut.conj_apply, MulAut.conj_apply]
  group

private theorem uc22r3e5c_conj_inv_comp {G : Type*} [Group G] (x : G) :
    (MulAut.conj x).toMonoidHom.comp (MulAut.conj x⁻¹).toMonoidHom = MonoidHom.id G := by
  refine MonoidHom.ext fun z => ?_
  change (MulAut.conj x) ((MulAut.conj x⁻¹) z) = z
  rw [MulAut.conj_apply, MulAut.conj_apply]
  group

private theorem uc22r3e5c_map_conj_inv {G : Type*} [Group G] {U U₀ : Subgroup G} {s : G}
    (h : U = U₀.map (MulAut.conj s).toMonoidHom) :
    U.map (MulAut.conj s⁻¹).toMonoidHom = U₀ := by
  rw [h, Subgroup.map_map]
  have hid : (MulAut.conj s⁻¹).toMonoidHom.comp (MulAut.conj s).toMonoidHom =
      MonoidHom.id G := by
    simpa using uc22r3e5c_conj_inv_comp (G := G) s⁻¹
  rw [hid, Subgroup.map_id]

private theorem uc22r3e5c_map_conj_apply {G : Type*} [Group G] {α : MulAut G}
    {H K : Subgroup G} {y : G} (hHK : K = H.map (MulAut.conj y).toMonoidHom)
    (hαH : H.map α.toMonoidHom = H) (hαK : K.map α.toMonoidHom = K) :
    H.map (MulAut.conj (α y)).toMonoidHom = K := by
  have h := CFSG.OrderReductions.StrongEmbeddingInheritance.map_conjugate α.toMonoidHom H y
  rw [← hHK, hαK, hαH] at h
  exact h.symm

private theorem uc22r3e5c_map_conj_inv_mul {G : Type*} [Group G] {H K : Subgroup G}
    {α : MulAut G} {s : G} (hαs : H.map (MulAut.conj (α s)).toMonoidHom = K)
    (hs : K.map (MulAut.conj s⁻¹).toMonoidHom = H) :
    H.map (MulAut.conj (s⁻¹ * α s)).toMonoidHom = H := by
  rw [uc22r3e5c_conj_mul_hom s⁻¹ (α s), ← Subgroup.map_map, hαs, hs]

private theorem uc22r3e5c_exists_unit_ne_one (ha : 1 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) : ∃ l : Kˣ, l ≠ 1 := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fintype (suzukiGroup a K) := Fintype.ofFinite _
  have hTcard : Nat.card (suzukiT a K) = 2 ^ (2 * a + 1) - 1 :=
    (suzuki_borel_structure hK).2.2.1
  have hcard : 1 < Nat.card (suzukiT a K) := by
    rw [hTcard]
    have h8 : 8 ≤ 2 ^ (2 * a + 1) := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hcard' : 1 < Fintype.card (suzukiT a K) := by
    rwa [Nat.card_eq_fintype_card] at hcard
  obtain ⟨t, ht⟩ := Fintype.exists_ne_of_one_lt_card hcard' (1 : suzukiT a K)
  obtain ⟨m, hm⟩ := mem_suzukiT_iff.1 t.2
  exact ⟨m, fun h => ht (Subtype.ext (by rw [← hm, h, suzukiDElt_one]; rfl))⟩

theorem uc22r3e5c_mem_suzukiT_of_mem_normalizer (ha : 1 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {x : suzukiGroup a K} (hx : x ∈ suzukiB a K)
    (hn : x ∈ Subgroup.normalizer (suzukiT a K : Set (suzukiGroup a K))) :
    x ∈ suzukiT a K := by
  classical
  have hinf : x • suzukiInfty K = suzukiInfty K := by
    refine MulAction.mem_stabilizer_iff.1 ?_
    rw [(suzuki_ovoid_stabilizer hK).1]
    exact hx
  obtain ⟨l, hl⟩ := uc22r3e5c_exists_unit_ne_one ha hK
  have hmem : x⁻¹ * suzukiDElt a K l * x ∈ suzukiT a K := by
    refine (Subgroup.mem_normalizer_iff.1 hn (x⁻¹ * suzukiDElt a K l * x)).2 ?_
    have h1 : x * (x⁻¹ * suzukiDElt a K l * x) * x⁻¹ = suzukiDElt a K l := by group
    rw [h1]
    exact suzukiDElt_mem_suzukiT a K l
  have hfix : suzukiDElt a K l • (x • suzukiLine a K 0 0) = x • suzukiLine a K 0 0 := by
    obtain ⟨m, hm⟩ := mem_suzukiT_iff.1 hmem
    rw [← mul_smul, show suzukiDElt a K l * x = x * (x⁻¹ * suzukiDElt a K l * x) by group,
      ← hm, mul_smul, suzukiDElt_smul_suzukiLine_zero hK]
  rcases fixed_mem_suzukiOmega hK hl
    (suzuki_smul_mem_suzukiOmega hK x (suzukiLine_mem_suzukiOmega a K 0 0)) hfix with h | h
  · exact absurd (smul_left_cancel x (h.trans hinf.symm))
      (suzukiLine_ne_suzukiInfty (a := a) 0 0)
  · exact mem_suzukiT_of_smul_eq hK hinf h

theorem uc22r3e5c_normalizer_inf_borel (ha : 1 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    suzukiB a K ⊓ Subgroup.normalizer (suzukiT a K : Set (suzukiGroup a K)) = suzukiT a K := by
  refine le_antisymm (fun x hx => ?_) (le_inf (suzukiT_le_suzukiB a K) Subgroup.le_normalizer)
  exact uc22r3e5c_mem_suzukiT_of_mem_normalizer ha hK (Subgroup.mem_inf.1 hx).1
    (Subgroup.mem_inf.1 hx).2

theorem uc22r3e5c_isHall_subgroupOf (hK : Nat.card K = 2 ^ (2 * a + 1))
    {C : Subgroup (suzukiGroup a K)} (hCB : C ≤ suzukiB a K)
    (hCcard : Nat.card C = 2 ^ (2 * a + 1) - 1) :
    CFSG.IsHallSubgroup {p : Nat.Primes | p.val ≠ 2} (C.subgroupOf (suzukiB a K)) := by
  classical
  refine CFSG.isHallSubgroup_of _ _ ?_ ?_
  · intro p hp
    change p.val ≠ 2
    have hcard : Nat.card (C.subgroupOf (suzukiB a K)) = Nat.card C :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCB).toEquiv
    rw [hcard, hCcard] at hp
    have heven : Even (2 ^ (2 * a + 1)) := Nat.even_pow.2 ⟨even_two, by omega⟩
    exact (Nat.Even.sub_odd Nat.one_le_two_pow heven odd_one).ne_two_of_dvd_nat hp
  · intro p hp hpidx
    change p.val ≠ 2 at hp
    have hcard : Nat.card (C.subgroupOf (suzukiB a K)) = 2 ^ (2 * a + 1) - 1 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCB).toEquiv, hCcard]
    have hcardB : Nat.card ↥(suzukiB a K) =
        (2 ^ (2 * a + 1)) ^ 2 * (2 ^ (2 * a + 1) - 1) :=
      (suzuki_borel_structure hK).2.2.2.2.2.2.2
    have hmul := Subgroup.card_mul_index (C.subgroupOf (suzukiB a K))
    rw [hcard, hcardB] at hmul
    have hq1 : 0 < 2 ^ (2 * a + 1) - 1 := by
      have := Nat.one_lt_two_pow (n := 2 * a + 1) (by omega)
      omega
    have hidx : (C.subgroupOf (suzukiB a K)).index = (2 ^ (2 * a + 1)) ^ 2 := by
      refine Nat.eq_of_mul_eq_mul_left hq1 ?_
      rw [hmul]; ring
    rw [hidx] at hpidx
    have h2 : p.val ∣ (2 : ℕ) ^ (2 * (2 * a + 1)) := by
      rwa [show (2 ^ (2 * a + 1)) ^ 2 = 2 ^ (2 * (2 * a + 1)) by ring] at hpidx
    have hp2 : p.val ∣ 2 := Nat.Prime.dvd_of_dvd_pow p.2 h2
    exact hp ((Nat.prime_dvd_prime_iff_eq p.2 Nat.prime_two).1 hp2)

theorem uc22r3e5c_exists_conj_torus (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    {C : Subgroup (suzukiGroup a K)} (hCB : C ≤ suzukiB a K)
    (hCcard : Nat.card C = 2 ^ (2 * a + 1) - 1) :
    ∃ b ∈ suzukiB a K, C = (suzukiT a K).map (MulAut.conj b).toMonoidHom := by
  haveI : Finite (suzukiGroup a K) := finite_suzukiGroup hK
  have hTcard : Nat.card (suzukiT a K) = 2 ^ (2 * a + 1) - 1 :=
    (suzuki_borel_structure hK).2.2.1
  have hTHall := uc22r3e5c_isHall_subgroupOf hK (suzukiT_le_suzukiB a K) hTcard
  have hCHall := uc22r3e5c_isHall_subgroupOf hK hCB hCcard
  obtain ⟨b, hb⟩ := CFSG.GroupTheory.SteinbergBK.solvable_hall_conjugacy
    (G := ↥(suzukiB a K)) (suzuki_borel_solvable hK).1 hTHall hCHall
  refine ⟨(b : suzukiGroup a K)⁻¹, (suzukiB a K).inv_mem b.2, ?_⟩
  have h := congrArg (Subgroup.map (suzukiB a K).subtype) hb
  simp only [CFSG.conjugate] at h
  rw [Subgroup.map_map, show (suzukiB a K).subtype.comp (MulAut.conj b⁻¹).toMonoidHom =
      (MulAut.conj ((b : suzukiGroup a K)⁻¹)).toMonoidHom.comp (suzukiB a K).subtype from by
    ext y; rfl, ← Subgroup.map_map, Subgroup.subgroupOf_map_subtype,
    Subgroup.subgroupOf_map_subtype, inf_of_le_left (suzukiT_le_suzukiB a K),
    inf_of_le_left hCB] at h
  exact h.symm

theorem uc22r3e5c_normalizer_inf_torus (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    {C : Subgroup (suzukiGroup a K)} (hCB : C ≤ suzukiB a K)
    (hCcard : Nat.card C = 2 ^ (2 * a + 1) - 1) :
    suzukiB a K ⊓ Subgroup.normalizer (C : Set (suzukiGroup a K)) = C := by
  obtain ⟨b, hbB, hb⟩ := uc22r3e5c_exists_conj_torus ha hK hCB hCcard
  refine le_antisymm (fun x hx => ?_) (le_inf hCB Subgroup.le_normalizer)
  obtain ⟨hxB, hxN⟩ := Subgroup.mem_inf.1 hx
  have hmap : (Subgroup.normalizer (C : Set (suzukiGroup a K))).map
      (MulAut.conj b⁻¹).toMonoidHom =
      Subgroup.normalizer (suzukiT a K : Set (suzukiGroup a K)) := by
    rw [Subgroup.map_equiv_normalizer_eq]
    have hCT : C.map (MulAut.conj b⁻¹).toMonoidHom = suzukiT a K := by
      rw [hb, Subgroup.map_map]
      have hid : (MulAut.conj b⁻¹).toMonoidHom.comp (MulAut.conj b).toMonoidHom =
          MonoidHom.id _ := by
        refine MonoidHom.ext fun y => ?_
        change (MulAut.conj b⁻¹) ((MulAut.conj b) y) = y
        rw [MulAut.conj_apply, MulAut.conj_apply]
        group
      rw [hid, Subgroup.map_id]
    rw [hCT]
  have hmem : b⁻¹ * x * b ∈ Subgroup.normalizer (suzukiT a K : Set (suzukiGroup a K)) := by
    rw [← hmap]
    exact Subgroup.mem_map.2 ⟨x, hxN, rfl⟩
  have hmemB : b⁻¹ * x * b ∈ suzukiB a K :=
    (suzukiB a K).mul_mem ((suzukiB a K).mul_mem ((suzukiB a K).inv_mem hbB) hxB) hbB
  have hT : b⁻¹ * x * b ∈ suzukiT a K :=
    uc22r3e5c_mem_suzukiT_of_mem_normalizer ha hK hmemB hmem
  rw [hb]
  exact Subgroup.mem_map.2 ⟨b⁻¹ * x * b, hT, by
    show b * (b⁻¹ * x * b) * b⁻¹ = x
    group⟩


private theorem uc22r3e5c_conj_inv_le_borel (hK : Nat.card K = 2 ^ (2 * a + 1))
    {U C : Subgroup (suzukiGroup a K)} {s : suzukiGroup a K}
    (hU : U = (suzukiU a K).map (MulAut.conj s).toMonoidHom)
    (hC : C ≤ Subgroup.normalizer (U : Set (suzukiGroup a K))) :
    C.map (MulAut.conj s⁻¹).toMonoidHom ≤ suzukiB a K := by
  have hle : C.map (MulAut.conj s⁻¹).toMonoidHom ≤
      (Subgroup.normalizer (U : Set (suzukiGroup a K))).map
        (MulAut.conj s⁻¹).toMonoidHom := Subgroup.map_mono hC
  rw [Subgroup.map_equiv_normalizer_eq, uc22r3e5c_map_conj_inv hU,
    uc22pwr1_sz_normalizer hK] at hle
  exact hle

theorem uc22r3e5c_exists_conj_pair_sylow (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    (U : Sylow 2 (suzukiGroup a K)) (C : Subgroup (suzukiGroup a K))
    (hC : C ≤ Subgroup.normalizer ((U : Subgroup (suzukiGroup a K)) : Set (suzukiGroup a K)))
    (hc : Nat.card C = 2 ^ (2 * a + 1) - 1) :
    ∃ t : suzukiGroup a K,
      (U : Subgroup (suzukiGroup a K)) =
          (suzukiU a K).map (MulAut.conj t).toMonoidHom ∧
        C = (suzukiT a K).map (MulAut.conj t).toMonoidHom := by
  classical
  obtain ⟨s, hs⟩ := MulAction.exists_smul_eq (suzukiGroup a K) (uc22pwr1_sz_sylow hK) U
  have hU : (U : Subgroup (suzukiGroup a K)) =
      (suzukiU a K).map (MulAut.conj s).toMonoidHom := by
    rw [← hs]; rfl
  have hCs := uc22r3e5c_conj_inv_le_borel hK hU hC
  have hcard' : Nat.card (C.map (MulAut.conj s⁻¹).toMonoidHom) = 2 ^ (2 * a + 1) - 1 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj s⁻¹).injective, hc]
  obtain ⟨b, hbB, hb⟩ := uc22r3e5c_exists_conj_torus ha hK hCs hcard'
  have hbU : (suzukiU a K).map (MulAut.conj b).toMonoidHom = suzukiU a K :=
    Subgroup.mem_normalizer_iff_map_conj_eq.1 (by
      rw [uc22pwr1_sz_normalizer hK]; exact hbB)
  refine ⟨s * b, ?_, ?_⟩
  · rw [hU, ← uc22r3e5c_map_conj_map (suzukiU a K) b s, hbU]
  · calc C = (C.map (MulAut.conj s⁻¹).toMonoidHom).map (MulAut.conj s).toMonoidHom := by
          rw [Subgroup.map_map, uc22r3e5c_conj_inv_comp, Subgroup.map_id]
      _ = ((suzukiT a K).map (MulAut.conj b).toMonoidHom).map
            (MulAut.conj s).toMonoidHom := by rw [hb]
      _ = (suzukiT a K).map ((MulAut.conj s).toMonoidHom.comp
            (MulAut.conj b).toMonoidHom) := by rw [Subgroup.map_map]
      _ = (suzukiT a K).map (MulAut.conj (s * b)).toMonoidHom := by
            rw [← uc22r3e5c_conj_mul_hom s b]

private theorem uc22r3e5c_normalizer_inf_of_conj (ha : 1 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {U C : Subgroup (suzukiGroup a K)}
    {t : suzukiGroup a K} (hU : U = (suzukiU a K).map (MulAut.conj t).toMonoidHom)
    (hC : C = (suzukiT a K).map (MulAut.conj t).toMonoidHom) :
    Subgroup.normalizer (U : Set (suzukiGroup a K)) ⊓
      Subgroup.normalizer (C : Set (suzukiGroup a K)) = C := by
  have hUinv := uc22r3e5c_map_conj_inv hU
  have hCinv := uc22r3e5c_map_conj_inv hC
  have hmap : (Subgroup.normalizer (U : Set (suzukiGroup a K)) ⊓
      Subgroup.normalizer (C : Set (suzukiGroup a K))).map
      (MulAut.conj t⁻¹).toMonoidHom = suzukiT a K := by
    rw [Subgroup.map_inf _ _ (MulAut.conj t⁻¹).toMonoidHom (MulAut.conj t⁻¹).injective,
      Subgroup.map_equiv_normalizer_eq, Subgroup.map_equiv_normalizer_eq,
      hUinv, hCinv, uc22pwr1_sz_normalizer hK, uc22r3e5c_normalizer_inf_borel ha hK]
  calc Subgroup.normalizer (U : Set (suzukiGroup a K)) ⊓
        Subgroup.normalizer (C : Set (suzukiGroup a K))
      = ((Subgroup.normalizer (U : Set (suzukiGroup a K)) ⊓
          Subgroup.normalizer (C : Set (suzukiGroup a K))).map
          (MulAut.conj t⁻¹).toMonoidHom).map (MulAut.conj t).toMonoidHom := by
        rw [Subgroup.map_map, uc22r3e5c_conj_inv_comp, Subgroup.map_id]
    _ = (suzukiT a K).map (MulAut.conj t).toMonoidHom := by rw [hmap]
    _ = C := hC.symm

private theorem uc22r3e5c_comm_of_map_conj (hK : Nat.card K = 2 ^ (2 * a + 1))
    {C : Subgroup (suzukiGroup a K)} {t : suzukiGroup a K}
    (hC : C = (suzukiT a K).map (MulAut.conj t).toMonoidHom) :
    ∀ c ∈ C, ∀ d ∈ C, c * d = d * c := by
  intro c hc d hd
  rw [hC] at hc hd
  obtain ⟨c', hc', rfl⟩ := Subgroup.mem_map.1 hc
  obtain ⟨d', hd', rfl⟩ := Subgroup.mem_map.1 hd
  have h := (suzuki_borel_structure hK).2.1 c' hc' d' hd'
  simpa [MulAut.conj_apply] using congrArg (fun z => t * z * t⁻¹) h

private theorem uc22r3e5c_conj_pow_apply {G : Type*} [Group G] {α : MulAut G}
    {C : Subgroup G} {s x : G} {e : ℕ} (hab : ∀ c ∈ C, ∀ d ∈ C, c * d = d * c)
    (he : ∀ c ∈ C, α c = c ^ e) (hx : x ∈ C) (hxs : x = s⁻¹ * α s) {c : G} (hc : c ∈ C) :
    α (s * c * s⁻¹) = (s * c * s⁻¹) ^ e := by
  have hxcomm : x * c ^ e = c ^ e * x := hab _ hx _ (C.pow_mem hc e)
  have hpow : s * c ^ e * s⁻¹ = (s * c * s⁻¹) ^ e := by
    rw [← MulAut.conj_apply s (c ^ e), map_pow, MulAut.conj_apply]
  calc α (s * c * s⁻¹) = α s * α c * (α s)⁻¹ := by rw [map_mul, map_mul, map_inv]
    _ = s * (x * c ^ e * x⁻¹) * s⁻¹ := by rw [he c hc, hxs]; group
    _ = s * c ^ e * s⁻¹ := by rw [hxcomm]; group
    _ = (s * c * s⁻¹) ^ e := hpow

theorem uc22r3e5c_torusExp_eq_suzuki (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    (α : MulAut (suzukiGroup a K)) (U₁ U₂ : Sylow 2 (suzukiGroup a K))
    (C₁ C₂ : Subgroup (suzukiGroup a K))
    (hC₁ : C₁ ≤ Subgroup.normalizer ((U₁ : Subgroup (suzukiGroup a K)) :
      Set (suzukiGroup a K)))
    (hC₂ : C₂ ≤ Subgroup.normalizer ((U₂ : Subgroup (suzukiGroup a K)) :
      Set (suzukiGroup a K)))
    (hcard₁ : Nat.card C₁ = 2 ^ (2 * a + 1) - 1)
    (hcard₂ : Nat.card C₂ = 2 ^ (2 * a + 1) - 1)
    (hαU₁ : (U₁ : Subgroup (suzukiGroup a K)).map α.toMonoidHom =
      (U₁ : Subgroup (suzukiGroup a K)))
    (hαC₁ : C₁.map α.toMonoidHom = C₁)
    (hαU₂ : (U₂ : Subgroup (suzukiGroup a K)).map α.toMonoidHom =
      (U₂ : Subgroup (suzukiGroup a K)))
    (hαC₂ : C₂.map α.toMonoidHom = C₂)
    {e : ℕ} (he : ∀ c ∈ C₁, α c = c ^ e) :
    ∀ c ∈ C₂, α c = c ^ e := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t₁, hU₁, hC₁'⟩ := uc22r3e5c_exists_conj_pair_sylow ha hK U₁ C₁ hC₁ hcard₁
  obtain ⟨t₂, hU₂, hC₂'⟩ := uc22r3e5c_exists_conj_pair_sylow ha hK U₂ C₂ hC₂ hcard₂
  set s : suzukiGroup a K := t₂ * t₁⁻¹ with hs
  have hst : s * t₁ = t₂ := by rw [hs]; group
  have hsU : (U₂ : Subgroup (suzukiGroup a K)) =
      (U₁ : Subgroup (suzukiGroup a K)).map (MulAut.conj s).toMonoidHom := by
    rw [hU₂, hU₁, uc22r3e5c_map_conj_map (suzukiU a K) t₁ s, hst]
  have hsC : C₂ = C₁.map (MulAut.conj s).toMonoidHom := by
    rw [hC₂', hC₁', uc22r3e5c_map_conj_map (suzukiT a K) t₁ s, hst]
  have hUs := uc22r3e5c_map_conj_apply hsU hαU₁ hαU₂
  have hCs := uc22r3e5c_map_conj_apply hsC hαC₁ hαC₂
  have hN : Subgroup.normalizer ((U₁ : Subgroup (suzukiGroup a K)) :
        Set (suzukiGroup a K)) ⊓
      Subgroup.normalizer (C₁ : Set (suzukiGroup a K)) = C₁ :=
    uc22r3e5c_normalizer_inf_of_conj ha hK hU₁ hC₁'
  have hab := uc22r3e5c_comm_of_map_conj hK hC₁'
  have hxU : (U₁ : Subgroup (suzukiGroup a K)).map
      (MulAut.conj (s⁻¹ * α s)).toMonoidHom = (U₁ : Subgroup (suzukiGroup a K)) :=
    uc22r3e5c_map_conj_inv_mul hUs (uc22r3e5c_map_conj_inv hsU)
  have hxC : C₁.map (MulAut.conj (s⁻¹ * α s)).toMonoidHom = C₁ :=
    uc22r3e5c_map_conj_inv_mul hCs (uc22r3e5c_map_conj_inv hsC)
  have hxin : s⁻¹ * α s ∈ C₁ := by
    rw [← hN]
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · rw [Subgroup.mem_normalizer_iff_map_conj_eq]; exact hxU
    · rw [Subgroup.mem_normalizer_iff_map_conj_eq]; exact hxC
  intro c hc
  obtain ⟨c', hc', hcs⟩ := Subgroup.mem_map.1 (hsC ▸ hc)
  have hc_eq : c = s * c' * s⁻¹ := by
    rw [← hcs]
    change (MulAut.conj s) c' = s * c' * s⁻¹
    rw [MulAut.conj_apply]
  rw [hc_eq]
  exact uc22r3e5c_conj_pow_apply hab he hxin rfl hc'

end CFSG.LocalAnalysis.UniquenessCase.UC22
