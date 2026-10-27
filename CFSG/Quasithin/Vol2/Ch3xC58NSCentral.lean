module

public import CFSG.Quasithin.Vol2.Ch3xC58NSLin2
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppCZ

public section

namespace CFSG.Quasithin.C58NS

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.C5 Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem exists_mem_comm_mod {T M N : Subgroup G} (hT : IsPGroup 2 T) (hNT : N ≤ T)
    (hMN : M ≤ N) (hTM : T ≤ normalizer (M : Set G)) (hTN : T ≤ normalizer (N : Set G))
    (hne : ¬ N ≤ M) : ∃ p ∈ N, p ∉ M ∧ ∀ t ∈ T, t * p * t⁻¹ * p⁻¹ ∈ M := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hMT : M ≤ T := hMN.trans hNT
  have hM' : (M.subgroupOf T).Normal := (normal_subgroupOf_iff_le_normalizer hMT).mpr hTM
  have hN' : (N.subgroupOf T).Normal := (normal_subgroupOf_iff_le_normalizer hNT).mpr hTN
  let φ := QuotientGroup.mk' (M.subgroupOf T)
  have hQ2 : IsPGroup 2 (↥T ⧸ M.subgroupOf T) := hT.to_quotient _
  have : Fact (IsPGroup 2 (↥T ⧸ M.subgroupOf T)) := ⟨hQ2⟩
  have hN'' : ((N.subgroupOf T).map φ).Normal := hN'.map φ (QuotientGroup.mk'_surjective _)
  obtain ⟨n, hnN, hnM⟩ := IsConcreteLE.not_le_iff_exists.mp hne
  have : Nontrivial ((N.subgroupOf T).map φ) := by
    refine ⟨⟨⟨φ ⟨n, hNT hnN⟩, Subgroup.mem_map_of_mem φ (Subgroup.mem_subgroupOf.mpr hnN)⟩,
      1, ?_⟩⟩
    intro h
    apply hnM
    have h1 : φ ⟨n, hNT hnN⟩ = 1 := congrArg Subtype.val h
    have h2 := (QuotientGroup.eq_one_iff _).mp h1
    exact Subgroup.mem_subgroupOf.mp h2
  obtain ⟨x, hx1, hxc⟩ :=
    CFSG.exists_nontrivial_center_mem_normal (N := (N.subgroupOf T).map φ) (p := 2)
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp x.2
  refine ⟨(y : G), Subgroup.mem_subgroupOf.mp hy, ?_, ?_⟩
  · intro hyM
    apply hx1
    apply Subtype.ext
    rw [← hyx]
    exact (QuotientGroup.eq_one_iff y).mpr (Subgroup.mem_subgroupOf.mpr hyM)
  · intro t ht
    have hc := Subgroup.mem_center_iff.mp hxc (φ ⟨t, ht⟩)
    have h1 : φ (⟨t, ht⟩ * y * (⟨t, ht⟩ : ↥T)⁻¹ * y⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hyx, hc]
      group
    have h2 := (QuotientGroup.eq_one_iff _).mp h1
    exact Subgroup.mem_subgroupOf.mp h2

theorem mem_blockZ_of_comm_mod {L : Subgroup G} (hL : IsShort2 L) {e : G}
    (heU : e ∈ blockU L) (he : ∀ k ∈ L, k * e * k⁻¹ * e⁻¹ ∈ blockZ L) : e ∈ blockZ L := by
  have hUc : ∀ a ∈ blockU L, ∀ b ∈ blockU L, a * b = b * a := (C1.elemAb2_blockU hL).1
  have hZU : blockZ L ≤ blockU L := inf_le_left
  let W : Subgroup G :=
    { carrier := {u | u ∈ blockU L ∧ ∀ k ∈ L, k * u * k⁻¹ * u⁻¹ ∈ blockZ L}
      one_mem' := ⟨one_mem _, fun k _ => by simp⟩
      mul_mem' := by
        rintro u v ⟨hu, hu'⟩ ⟨hv, hv'⟩
        refine ⟨mul_mem hu hv, fun k hk => ?_⟩
        have e1 : k * (u * v) * k⁻¹ * (u * v)⁻¹ =
            (k * u * k⁻¹ * u⁻¹) * (u * (k * v * k⁻¹ * v⁻¹) * u⁻¹) := by group
        have e2 : u * (k * v * k⁻¹ * v⁻¹) * u⁻¹ = k * v * k⁻¹ * v⁻¹ := by
          rw [hUc u hu _ (hZU (hv' k hk))]; group
        rw [e1, e2]
        exact mul_mem (hu' k hk) (hv' k hk)
      inv_mem' := by
        rintro u ⟨hu, hu'⟩
        refine ⟨inv_mem hu, fun k hk => ?_⟩
        have e1 : k * u⁻¹ * k⁻¹ * u⁻¹⁻¹ = u⁻¹ * (k * u * k⁻¹ * u⁻¹)⁻¹ * u := by group
        have e2 : u⁻¹ * (k * u * k⁻¹ * u⁻¹)⁻¹ * u = (k * u * k⁻¹ * u⁻¹)⁻¹ := by
          rw [hUc u⁻¹ (inv_mem hu) _ (inv_mem (hZU (hu' k hk)))]; group
        rw [e1, e2]
        exact inv_mem (hu' k hk) }
  have hZW : blockZ L ≤ W := fun z hz => ⟨hZU hz, fun k hk => by
    have h1 := mem_centralizer_iff.mp hz.2 k hk
    have h2 : k * z * k⁻¹ * z⁻¹ = 1 := by rw [h1]; group
    rw [h2]; exact one_mem _⟩
  have hWU : W ≤ blockU L := fun u hu => hu.1
  have hconj : ∀ l ∈ L, ∀ u ∈ W, l * u * l⁻¹ ∈ W := by
    intro l hl u hu
    refine ⟨(mem_normalizer_iff.mp (C1.le_normalizer_blockU L hl) u).mp hu.1, fun k hk => ?_⟩
    have hk' : l⁻¹ * k * l ∈ L := mul_mem (mul_mem (inv_mem hl) hk) hl
    have h1 := hu.2 _ hk'
    have e1 : k * (l * u * l⁻¹) * k⁻¹ * (l * u * l⁻¹)⁻¹ =
        l * ((l⁻¹ * k * l) * u * (l⁻¹ * k * l)⁻¹ * u⁻¹) * l⁻¹ := by group
    rw [e1]
    have h2 := mem_centralizer_iff.mp h1.2 l hl
    rw [h2]
    simpa [mul_assoc] using h1
  have hLW : L ≤ normalizer (W : Set G) := fun l hl =>
    B6.mem_normalizer_of_forall_mem (fun u hu => hconj l hl u hu)
      (fun u hu => by simpa using hconj l⁻¹ (inv_mem hl) u hu)
  rcases hL.2.2.2.2.2 W hZW hWU hLW with h | h
  · rw [← h]; exact ⟨heU, he⟩
  · exfalso
    apply (lt_iff_le_not_ge.mp hL.2.2.2.2.1).2
    calc blockU L = ⁅blockU L, L⁆ := (C1.commutator_blockU hL).symm
      _ ≤ blockZ L := by
          rw [Subgroup.commutator_le]
          intro u hu k hk
          have hu' : u⁻¹ ∈ W := by rw [h]; exact inv_mem hu
          have h1 := hu'.2 k hk
          have e1 : ⁅u, k⁆ = u * (k * u⁻¹ * k⁻¹ * u⁻¹⁻¹) * u⁻¹ := by
            rw [commutatorElement_def]; group
          rw [e1, hUc u hu _ (hZU h1)]
          simpa using h1

theorem blockU_le_of_mem {L C : Subgroup G} (hL : IsShort2 L)
    (hLC : L ≤ normalizer (C : Set G)) {e : G} (heU : e ∈ blockU L) (heZ : e ∉ blockZ L)
    (hmem : ∀ k ∈ L, e * (k * e * k⁻¹)⁻¹ ∈ C) : blockU L ≤ C := by
  have hUc : ∀ a ∈ blockU L, ∀ b ∈ blockU L, a * b = b * a := (C1.elemAb2_blockU hL).1
  have hZU : blockZ L ≤ blockU L := inf_le_left
  have hLU : L ≤ normalizer (blockU L : Set G) := C1.le_normalizer_blockU L
  have hLZ : L ≤ normalizer (blockZ L : Set G) := fun l hl =>
    mem_normalizer_inf (hLU hl) (mem_normalizer_centralizer (Subgroup.le_normalizer hl))
  set W := (C ⊓ blockU L) ⊔ blockZ L with hW
  have hLW : L ≤ normalizer (W : Set G) := fun l hl =>
    C1.mem_normalizer_sup (mem_normalizer_inf (hLC hl) (hLU hl)) (hLZ hl)
  have hcomm : ∀ a ∈ C ⊓ blockU L, ∀ z ∈ blockZ L, a * z = z * a := fun a ha z hz =>
    hUc a ha.2 z (hZU hz)
  rcases hL.2.2.2.2.2 W le_sup_right (sup_le inf_le_right hZU) hLW with h | h
  · exfalso
    apply heZ
    refine mem_blockZ_of_comm_mod hL heU fun k hk => ?_
    have hkeU : k * e * k⁻¹ ∈ blockU L := (mem_normalizer_iff.mp (hLU hk) e).mp heU
    have h1 : e * (k * e * k⁻¹)⁻¹ ∈ W :=
      mem_sup_left (Subgroup.mem_inf.mpr ⟨hmem k hk, mul_mem heU (inv_mem hkeU)⟩)
    rw [h] at h1
    have h2 := inv_mem h1
    have e1 : (e * (k * e * k⁻¹)⁻¹)⁻¹ = k * e * k⁻¹ * e⁻¹ := by group
    rwa [e1] at h2
  · have hUC : blockU L ≤ C ⊓ blockU L := by
      calc blockU L = ⁅blockU L, L⁆ := (C1.commutator_blockU hL).symm
        _ ≤ C ⊓ blockU L := by
            rw [Subgroup.commutator_le]
            intro u hu k hk
            have hu' : u ∈ W := by rw [h]; exact hu
            obtain ⟨a, ha, z, hz, rfl⟩ := mem_sup_of_commute hcomm hu'
            have hzk : z * k = k * z := (mem_centralizer_iff.mp hz.2 k hk).symm
            have e1 : ⁅a * z, k⁆ = a * (k * a⁻¹ * k⁻¹) := by
              rw [commutatorElement_def]
              calc a * z * k * (a * z)⁻¹ * k⁻¹ = a * (z * k) * z⁻¹ * a⁻¹ * k⁻¹ := by group
                _ = a * (k * z) * z⁻¹ * a⁻¹ * k⁻¹ := by rw [hzk]
                _ = a * (k * a⁻¹ * k⁻¹) := by group
            rw [e1]
            refine ⟨mul_mem ha.1 ((mem_normalizer_iff.mp (hLC hk) _).mp (inv_mem ha.1)), ?_⟩
            exact mul_mem ha.2 ((mem_normalizer_iff.mp (hLU hk) _).mp (inv_mem ha.2))
    exact hUC.trans inf_le_left

theorem lin2_exists_central {L T₁ : Subgroup G} (hL : IsShort2 L) {n : ℕ} (hn : 1 ≤ n)
    (hlin : IsLin2Type L n) (hT₁ : IsPGroup 2 T₁) (hT₁L : T₁ ≤ normalizer (L : Set G))
    (hsyl : IsSylowTwoOf (T₁ ⊓ L) L) :
    ∃ e ∈ blockU L ⊓ centralizer ((T₁ ⊓ L : Subgroup G) : Set G), e ∉ blockZ L ∧
      ∀ y ∈ T₁, y * e = e * y := by
  classical
  obtain ⟨hR1, hR2', -, hR4, -, -⟩ := C56.lin2_module_facts hL hn hlin hsyl
  have hQP : blockQ L ≤ T₁ ⊓ L :=
    hsyl.le_of_normalizes (C1.blockQ_le L) (C1.le_normalizer_blockQ L) (C1.blockQ_isPGroup L)
  have hP₀Q : ¬ T₁ ⊓ L ≤ blockQ L := by
    intro h
    have h1 : (blockQ L).relIndex (T₁ ⊓ L) = 1 := Subgroup.relIndex_eq_one.mpr h
    rw [hR2'] at h1
    have h2 : 2 ^ 1 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    omega
  have hT₁Q : T₁ ≤ normalizer (blockQ L : Set G) := fun g hg => by
    rw [← conjSubgroup_eq_iff_mem_normalizer]
    show conjSubgroup (pCoreOf 2 L) g = pCoreOf 2 L
    rw [conjSubgroup_pCoreOf, conjSubgroup_eq_iff_mem_normalizer.mpr (hT₁L hg)]
  have hT₁P : T₁ ≤ normalizer ((T₁ ⊓ L : Subgroup G) : Set G) := fun g hg =>
    mem_normalizer_inf (Subgroup.le_normalizer hg) (hT₁L hg)
  obtain ⟨p, hpP, hpQ, hpc⟩ := exists_mem_comm_mod hT₁ inf_le_left hQP hT₁Q hT₁P hP₀Q
  have hpN : p ∈ normalizer (L : Set G) := Subgroup.le_normalizer hpP.2
  have hpU : p ∈ normalizer (blockU L : Set G) := C1.mem_normalizer_blockU hpN
  have hUc : ∀ a ∈ blockU L, ∀ b ∈ blockU L, a * b = b * a := (C1.elemAb2_blockU hL).1
  have hφU : ∀ u ∈ blockU L, p * u * p⁻¹ * u⁻¹ ∈ blockU L := fun u hu =>
    mul_mem ((mem_normalizer_iff.mp hpU u).mp hu) (inv_mem hu)
  set E := Subgroup.closure {w | ∃ u ∈ blockU L, w = p * u * p⁻¹ * u⁻¹} with hEdef
  have hE : ∀ w ∈ E, ∃ u ∈ blockU L, w = p * u * p⁻¹ * u⁻¹ := by
    intro w hw
    induction hw using Subgroup.closure_induction with
    | mem w hw => exact hw
    | one => exact ⟨1, one_mem _, by group⟩
    | mul a b _ _ ha hb =>
      obtain ⟨u, hu, rfl⟩ := ha
      obtain ⟨v, hv, rfl⟩ := hb
      refine ⟨u * v, mul_mem hu hv, ?_⟩
      have h1 : p * v * p⁻¹ ∈ blockU L := (mem_normalizer_iff.mp hpU v).mp hv
      have k1 := hUc u⁻¹ (inv_mem hu) _ h1
      have k2 := hUc u⁻¹ (inv_mem hu) v⁻¹ (inv_mem hv)
      calc p * u * p⁻¹ * u⁻¹ * (p * v * p⁻¹ * v⁻¹)
          = p * u * p⁻¹ * (u⁻¹ * (p * v * p⁻¹)) * v⁻¹ := by group
        _ = p * u * p⁻¹ * ((p * v * p⁻¹) * u⁻¹) * v⁻¹ := by rw [k1]
        _ = p * (u * v) * p⁻¹ * (u⁻¹ * v⁻¹) := by group
        _ = p * (u * v) * p⁻¹ * (v⁻¹ * u⁻¹) := by rw [k2]
        _ = p * (u * v) * p⁻¹ * (u * v)⁻¹ := by group
    | inv a _ ha =>
      obtain ⟨u, hu, rfl⟩ := ha
      refine ⟨u⁻¹, inv_mem hu, ?_⟩
      have h1 : p * u * p⁻¹ ∈ blockU L := (mem_normalizer_iff.mp hpU u).mp hu
      have k1 := hUc u (hu) _ (inv_mem h1)
      calc (p * u * p⁻¹ * u⁻¹)⁻¹ = u * (p * u * p⁻¹)⁻¹ := by group
        _ = (p * u * p⁻¹)⁻¹ * u := k1
        _ = p * u⁻¹ * p⁻¹ * u⁻¹⁻¹ := by group
  have hEU : E ≤ blockU L := (Subgroup.closure_le _).mpr fun w ⟨u, hu, hw⟩ => hw ▸ hφU u hu
  have hET : E ≤ T₁ := hEU.trans ((C1.blockU_le_blockQ hL).trans (hQP.trans inf_le_left))
  have hTE : T₁ ≤ normalizer (E : Set G) := by
    have key : ∀ t ∈ T₁, ∀ w ∈ E, t * w * t⁻¹ ∈ E := by
      intro t ht w hw
      obtain ⟨u, hu, rfl⟩ := hE w hw
      have hc := hpc t ht
      have htN : t ∈ normalizer (blockU L : Set G) := C1.mem_normalizer_blockU (hT₁L ht)
      have hu' : t * u * t⁻¹ ∈ blockU L := (mem_normalizer_iff.mp htN u).mp hu
      have hpu : p * (t * u * t⁻¹) * p⁻¹ ∈ blockU L := (mem_normalizer_iff.mp hpU _).mp hu'
      have hcomm := C1.blockU_comm hL _ hpu _ hc
      refine Subgroup.subset_closure ⟨t * u * t⁻¹, hu', ?_⟩
      have e1 : t * (p * u * p⁻¹ * u⁻¹) * t⁻¹ =
          (t * p * t⁻¹ * p⁻¹) * (p * (t * u * t⁻¹) * p⁻¹) * (t * p * t⁻¹ * p⁻¹)⁻¹ *
            (t * u * t⁻¹)⁻¹ := by group
      rw [e1, ← hcomm]
      group
    exact fun t ht => B6.mem_normalizer_of_forall_mem (fun w hw => key t ht w hw)
      (fun w hw => by simpa using key t⁻¹ (inv_mem ht) w hw)
  have hEne : E ≠ ⊥ := by
    intro hbot
    apply hpQ
    have hpC : p ∈ L ⊓ centralizer (blockU L : Set G) := by
      refine ⟨hpP.2, mem_centralizer_iff.mpr fun u hu => ?_⟩
      have h1 : p * u * p⁻¹ * u⁻¹ ∈ E := Subgroup.subset_closure ⟨u, hu, rfl⟩
      rw [hbot, Subgroup.mem_bot] at h1
      have h2 : p * u * p⁻¹ = u := mul_inv_eq_one.mp h1
      exact (mul_inv_eq_iff_eq_mul.mp h2).symm
    rw [hR1] at hpC
    exact hpC
  obtain ⟨e, heE, he1, hec⟩ := DoubleA3.exists_central_of_normal hEne hET hTE hT₁
  have heC : e ∈ blockU L ⊓ centralizer ((T₁ ⊓ L : Subgroup G) : Set G) := by
    rw [← hR4]
    obtain ⟨u, hu, rfl⟩ := hE e heE
    have h1 := Subgroup.commutator_mem_commutator hu hpP
    have e1 : p * u * p⁻¹ * u⁻¹ = ⁅u, p⁆⁻¹ := by rw [commutatorElement_def]; group
    rw [e1]
    exact inv_mem h1
  refine ⟨e, heC, fun heZ => he1 ?_, hec⟩
  obtain ⟨u, hu, rfl⟩ := hE e heE
  have h1 := lin2_comm_of_mem_blockZ hL hn hlin hsyl hpP hpQ hu heZ
  rw [← h1]; group

theorem exists_central_of_block {L T₁ : Subgroup G} (hL : IsShort2 L)
    (htyp : (∃ n : ℕ, 1 < n ∧ IsLin2Type L n) ∨ IsAltType L 5) (hT₁ : IsPGroup 2 T₁)
    (hT₁L : T₁ ≤ normalizer (L : Set G)) (hsyl : IsSylowTwoOf (T₁ ⊓ L) L)
    (hUT : blockU L ≤ T₁) : ∃ e ∈ blockU L, e ∉ blockZ L ∧ ∀ y ∈ T₁, y * e = e * y := by
  rcases htyp with ⟨n, hn, hlin⟩ | h5
  · obtain ⟨e, heU, heZ, hec⟩ := lin2_exists_central hL (by omega) hlin hT₁ hT₁L hsyl
    exact ⟨e, heU.1, heZ, hec⟩
  · have hZ := AppC.blockZ_eq_bot_of_alt5 hL h5
    have hUne : blockU L ≠ ⊥ := by
      intro h
      have := hL.2.2.2.2.1
      rw [hZ, h] at this
      exact lt_irrefl _ this
    obtain ⟨e, heU, he1, hec⟩ := DoubleA3.exists_central_of_normal hUne hUT
      (fun t ht => C1.mem_normalizer_blockU (hT₁L ht)) hT₁
    refine ⟨e, heU, fun h => he1 ?_, hec⟩
    rw [hZ] at h
    exact h

end CFSG.Quasithin.C58NS
