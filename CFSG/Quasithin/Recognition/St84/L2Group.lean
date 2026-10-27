module

public import CFSG.Walter.PSL2Facts.Even
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2NormalizedRootSylowCount
public import CFSG.Assembly.Defs
public import CFSG.Walter.Defs

public section

namespace CFSG.Quasithin.St84

attribute [local instance] Subgroup.normal_in_normalizer

open scoped MatrixGroups LinearAlgebra.Projectivization Pointwise
open Matrix Projectivization
open CFSG.Walter
open CFSG.BenderSuzuki.External

variable {f : ℕ}

local instance instNormalizerSubgroupNormal :
    ∀ (U : Sylow 2 (PSL(2, GaloisField 2 f))),
      ((U : Subgroup (PSL(2, GaloisField 2 f))).subgroupOf
        (Subgroup.normalizer (U : Set (PSL(2, GaloisField 2 f))))).Normal :=
  fun _ => Subgroup.normal_in_normalizer

theorem psl2_sylow_two_card (hf : 1 ≤ f) (U : Sylow 2 (PSL(2, GaloisField 2 f))) :
    Nat.card (U : Subgroup (PSL(2, GaloisField 2 f))) = 2 ^ f := by
  have hK : Nat.card (GaloisField 2 f) = 2 ^ f :=
    GaloisField.card 2 f (by omega)
  obtain ⟨e⟩ := huppert_II_8_2_a_sylow_equiv_additive (F := GaloisField 2 f) (p := 2) hK U
  calc
    Nat.card (U : Subgroup (PSL(2, GaloisField 2 f)))
        = Nat.card (Multiplicative (GaloisField 2 f)) := (Nat.card_congr e.toEquiv).symm
    _ = Nat.card (GaloisField 2 f) := Nat.card_congr Multiplicative.toAdd
    _ = 2 ^ f := hK

theorem psl2_center_eq_bot {f : ℕ} :
    Subgroup.center (PSL(2, GaloisField 2 f)) = ⊥ := by
  let e := CFSG.Walter.psl2MulEquivSL2OfCharTwo (K := GaloisField 2 f)
  let eHom : PSL(2, GaloisField 2 f) →* SL(2, GaloisField 2 f) := e
  have hinj : Function.Injective eHom := e.injective
  have hmap : (Subgroup.center (PSL(2, GaloisField 2 f))).map eHom = ⊥ := by
    rw [Subgroup.map_center_eq, CFSG.Walter.sl2_center_eq_bot_of_charTwo]
  exact (Subgroup.map_injective hinj) (by rw [hmap, Subgroup.map_bot])

theorem psl2_ti (hf : 1 ≤ f) {U V : Sylow 2 (PSL(2, GaloisField 2 f))} (hUV : U ≠ V) :
    (U : Subgroup (PSL(2, GaloisField 2 f))) ⊓
      (V : Subgroup (PSL(2, GaloisField 2 f))) = ⊥ := by
  classical
  by_cases hf2 : 2 ≤ f
  · rw [eq_bot_iff]
    rintro x ⟨hxU, hxV⟩
    by_contra hx1
    have hxo : orderOf x = 2 := by
      obtain ⟨hUel, -⟩ := psl2_even_sylow_two hf2 U
      exact orderOf_eq_prime
        (elemPow_eq_one_of_isElementaryAbelian (p := 2)
          (A := (U : Subgroup (PSL(2, GaloisField 2 f)))) x hxU) hx1
    have hcen : Subgroup.centralizer ({x} : Set (PSL(2, GaloisField 2 f))) =
        (U : Subgroup (PSL(2, GaloisField 2 f))) :=
      psl2_even_centralizer_involution hf2 U hxU hx1
    obtain ⟨hVel, -⟩ := psl2_even_sylow_two hf2 V
    have hVle : (V : Subgroup (PSL(2, GaloisField 2 f))) ≤
        Subgroup.centralizer ({x} : Set (PSL(2, GaloisField 2 f))) := by
      intro v hv
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact congrArg Subtype.val (hVel.toIsMulCommutative.is_comm.comm ⟨v, hv⟩ ⟨x, hxV⟩)
    have hVU : (V : Subgroup (PSL(2, GaloisField 2 f))) ≤
        (U : Subgroup (PSL(2, GaloisField 2 f))) := hcen ▸ hVle
    have hVeq : V = U := Sylow.ext (Subgroup.eq_of_le_of_card_ge hVU (by
      rw [psl2_sylow_two_card hf U, psl2_sylow_two_card hf V]))
    exact hUV hVeq.symm
  · have hU2 : Nat.card (U : Subgroup (PSL(2, GaloisField 2 f))) = 2 := by
      have h := psl2_sylow_two_card hf U
      have hf1 : f = 1 := by omega
      simpa [hf1] using h
    have hV2 : Nat.card (V : Subgroup (PSL(2, GaloisField 2 f))) = 2 := by
      have h := psl2_sylow_two_card hf V
      have hf1 : f = 1 := by omega
      simpa [hf1] using h
    rw [eq_bot_iff]
    rintro x ⟨hxU, hxV⟩
    by_contra hx1
    have hxU' : x ∈ (U : Subgroup (PSL(2, GaloisField 2 f))) := hxU
    have hxV' : x ∈ (V : Subgroup (PSL(2, GaloisField 2 f))) := hxV
    have hordU : orderOf x ∣ 2 :=
      (by simpa [hU2] using Subgroup.orderOf_dvd_natCard (U : Subgroup (PSL(2, GaloisField 2 f))) hxU')
    have hord : orderOf x = 2 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hordU with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hx1
      · exact h
    have hzU : Subgroup.zpowers x = (U : Subgroup (PSL(2, GaloisField 2 f))) :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hxU') (by
        rw [Nat.card_zpowers, hord, hU2])
    have hzV : Subgroup.zpowers x = (V : Subgroup (PSL(2, GaloisField 2 f))) :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hxV') (by
        rw [Nat.card_zpowers, hord, hV2])
    exact hUV (Sylow.ext (hzU.symm.trans hzV))

theorem psl2_sylow_two_eq_of_mem (hf : 1 ≤ f)
    {U V : Sylow 2 (PSL(2, GaloisField 2 f))} {x : PSL(2, GaloisField 2 f)}
    (hxU : x ∈ (U : Subgroup (PSL(2, GaloisField 2 f))))
    (hxV : x ∈ (V : Subgroup (PSL(2, GaloisField 2 f)))) (hx1 : x ≠ 1) : U = V := by
  by_contra hUV
  have hbot := psl2_ti hf hUV
  have hxbot : x ∈ (⊥ : Subgroup (PSL(2, GaloisField 2 f))) := by
    rw [← hbot]
    exact ⟨hxU, hxV⟩
  exact hx1 (by simpa using hxbot)

theorem psl2_sylow_two_normalizes_iff (hf : 1 ≤ f)
    {U V : Sylow 2 (PSL(2, GaloisField 2 f))} {x : PSL(2, GaloisField 2 f)}
    (hxU : x ∈ (U : Subgroup (PSL(2, GaloisField 2 f)))) (hx1 : x ≠ 1) :
    x ∈ Subgroup.normalizer (V : Set (PSL(2, GaloisField 2 f))) ↔ V = U := by
  constructor
  · intro hxN
    have hxV : x ∈ (V : Subgroup (PSL(2, GaloisField 2 f))) := by
      have hinf := IsPGroup.inf_normalizer_sylow (p := 2)
        (P := (U : Subgroup (PSL(2, GaloisField 2 f)))) U.2 V
      have hx : x ∈ (U : Subgroup (PSL(2, GaloisField 2 f))) ⊓
          Subgroup.normalizer (V : Set (PSL(2, GaloisField 2 f))) := ⟨hxU, hxN⟩
      rw [hinf] at hx
      exact hx.2
    exact (psl2_sylow_two_eq_of_mem hf hxU hxV hx1).symm
  · rintro rfl
    exact Subgroup.le_normalizer hxU

theorem psl2_sylow_two_ne_card (hf : 1 ≤ f)
    (U : Sylow 2 (PSL(2, GaloisField 2 f))) :
    Nat.card {V : Sylow 2 (PSL(2, GaloisField 2 f)) // V ≠ U} = 2 ^ f := by
  let : Fintype (Sylow 2 (PSL(2, GaloisField 2 f))) := Fintype.ofFinite _
  let : Fintype {V : Sylow 2 (PSL(2, GaloisField 2 f)) // V ≠ U} := Fintype.ofFinite _
  have htotal : Nat.card (Sylow 2 (PSL(2, GaloisField 2 f))) = 2 ^ f + 1 :=
    psl2_even_card_sylow (by omega)
  simp only [Nat.card_eq_fintype_card] at htotal ⊢
  rw [Fintype.card_subtype_compl (p := fun V : Sylow 2 (PSL(2, GaloisField 2 f)) => V = U),
    Fintype.card_subtype_eq, htotal]
  exact Nat.add_sub_cancel _ _

theorem psl2_sylow_two_stabilizer_eq_bot (hf : 1 ≤ f)
    {U V : Sylow 2 (PSL(2, GaloisField 2 f))} (hUV : U ≠ V) :
    MulAction.stabilizer (U : Subgroup (PSL(2, GaloisField 2 f))) V = ⊥ := by
  refine le_antisymm ?_ bot_le
  intro x hx
  rw [Subgroup.mem_bot]
  by_contra hx1
  have hxU : (x : PSL(2, GaloisField 2 f)) ∈
      (U : Subgroup (PSL(2, GaloisField 2 f))) := x.2
  have hxN : (x : PSL(2, GaloisField 2 f)) ∈
      Subgroup.normalizer (V : Set (PSL(2, GaloisField 2 f))) := by
    rw [← Sylow.smul_eq_iff_mem_normalizer, ← MulAction.subgroup_smul_def]
    exact MulAction.mem_stabilizer_iff.mp hx
  exact hUV ((psl2_sylow_two_normalizes_iff hf hxU
    (fun h => hx1 (Subtype.ext h))).mp hxN).symm

theorem psl2_sylow_two_smul_eq_of_ne (hf : 1 ≤ f)
    {U V W : Sylow 2 (PSL(2, GaloisField 2 f))} (hVU : V ≠ U) (hWU : W ≠ U) :
    ∃ u : (U : Subgroup (PSL(2, GaloisField 2 f))), u • V = W := by
  classical
  let H : Subgroup (PSL(2, GaloisField 2 f)) := U
  have hcardH : Nat.card H = 2 ^ f := psl2_sylow_two_card hf U
  have hUstab : ∀ u : H, u • U = U := by
    intro u
    rw [MulAction.subgroup_smul_def, Sylow.smul_eq_iff_mem_normalizer]
    exact Subgroup.le_normalizer u.2
  let g : H → {X : Sylow 2 (PSL(2, GaloisField 2 f)) // X ≠ U} := fun u =>
    ⟨u • V, by
      intro h
      have h' := congrArg (fun X : Sylow 2 (PSL(2, GaloisField 2 f)) => u⁻¹ • X) h
      rw [← mul_smul, inv_mul_cancel, one_smul, hUstab u⁻¹] at h'
      exact hVU h'⟩
  have hginj : Function.Injective g := by
    intro u v huv
    have huveq : u • V = v • V := congrArg Subtype.val huv
    have hstab : v⁻¹ * u ∈ MulAction.stabilizer H V := by
      rw [MulAction.mem_stabilizer_iff]
      calc
        (v⁻¹ * u) • V = v⁻¹ • (u • V) := by rw [mul_smul]
        _ = v⁻¹ • (v • V) := by rw [huveq]
        _ = V := by rw [← mul_smul, inv_mul_cancel, one_smul]
    have hbot := psl2_sylow_two_stabilizer_eq_bot hf (U := U) (V := V) hVU.symm
    have hvu : v⁻¹ * u = 1 := by
      have h : v⁻¹ * u ∈ (⊥ : Subgroup H) := by
        rwa [hbot] at hstab
      simpa using h
    calc
      u = v * (v⁻¹ * u) := by group
      _ = v * 1 := by rw [hvu]
      _ = v := mul_one v
  have hcard : Nat.card {X : Sylow 2 (PSL(2, GaloisField 2 f)) // X ≠ U} ≤ Nat.card H := by
    rw [psl2_sylow_two_ne_card hf U, hcardH]
  obtain ⟨u, hu⟩ := (hginj.bijective_of_nat_card_le hcard).2 ⟨W, hWU⟩
  exact ⟨u, congrArg Subtype.val hu⟩

theorem psl2_sylow_two_sup_eq_top (hf : 1 ≤ f)
    {U V : Sylow 2 (PSL(2, GaloisField 2 f))} (hUV : U ≠ V) :
    (U : Subgroup (PSL(2, GaloisField 2 f))) ⊔
      (V : Subgroup (PSL(2, GaloisField 2 f))) = ⊤ := by
  classical
  let L := PSL(2, GaloisField 2 f)
  let H : Subgroup L := (U : Subgroup L) ⊔ (V : Subgroup L)
  have hall : ∀ W : Sylow 2 L, (W : Subgroup L) ≤ H := by
    intro W
    by_cases hWU : W = U
    · rw [hWU]
      exact le_sup_left
    · obtain ⟨u, hu⟩ := psl2_sylow_two_smul_eq_of_ne hf (U := U) (V := V) hUV.symm hWU
      rw [← hu]
      exact Sylow.smul_le (p := 2) (P := V) le_sup_right
        ⟨u, Subgroup.mem_sup_left u.2⟩
  by_cases hf2 : 2 ≤ f
  · have h4 : 4 ≤ Nat.card (GaloisField 2 f) := by
      rw [GaloisField.card 2 f (by omega)]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
    haveI : IsSimpleGroup L := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4
    have hSle : Subgroup.normalClosure (U : Set L) ≤ H := by
      rw [Subgroup.normalClosure, Subgroup.closure_le]
      intro x hx
      obtain ⟨a, ha, hconj⟩ := Group.mem_conjugatesOfSet_iff.mp hx
      obtain ⟨c, rfl⟩ := isConj_iff.mp hconj
      exact hall (c • U) (by
        rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
        exact Subgroup.mem_map_of_mem (MulAut.conj c : L →* L) ha)
    have hUne : (U : Subgroup L) ≠ ⊥ := by
      intro h
      have hc : Nat.card (U : Subgroup L) = 1 := by rw [h, Subgroup.card_bot]
      rw [psl2_sylow_two_card hf U] at hc
      have h2 : 2 ≤ 2 ^ f := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
      omega
    have hStop : Subgroup.normalClosure (U : Set L) = ⊤ := by
      rcases (inferInstance : (Subgroup.normalClosure (U : Set L)).Normal).eq_bot_or_eq_top with
        hbot | htop
      · exfalso
        have hUle : (U : Subgroup L) ≤ Subgroup.normalClosure (U : Set L) :=
          Subgroup.le_normalClosure
        rw [hbot] at hUle
        exact hUne (eq_bot_iff.mpr hUle)
      · exact htop
    exact top_unique (hStop ▸ hSle)
  · have hf1 : f = 1 := by omega
    have hL6 : Nat.card L = 6 := by
      change Nat.card (PSL(2, GaloisField 2 f)) = 6
      rw [hf1]
      have h := psl2_even_card (f := 1) (by omega)
      norm_num at h ⊢
      exact h
    have hU2 : Nat.card (U : Subgroup L) = 2 := by
      simpa [hf1] using psl2_sylow_two_card hf U
    have hV2 : Nat.card (V : Subgroup L) = 2 := by
      simpa [hf1] using psl2_sylow_two_card hf V
    let U' : Subgroup L := U
    let V' : Subgroup L := V
    let g : U' × V' → H := fun p =>
      ⟨(p.1 : L) * (p.2 : L), H.mul_mem ((le_sup_left : U' ≤ H) p.1.2)
        ((le_sup_right : V' ≤ H) p.2.2)⟩
    have hginj : Function.Injective g := by
      rintro ⟨u₁, v₁⟩ ⟨u₂, v₂⟩ h
      have h' : (u₁ : L) * (v₁ : L) = (u₂ : L) * (v₂ : L) := congrArg Subtype.val h
      have hmem : (u₂ : L)⁻¹ * (u₁ : L) ∈ U' ⊓ V' := by
        refine ⟨U'.mul_mem (U'.inv_mem u₂.2) u₁.2, ?_⟩
        have hc : (u₂ : L)⁻¹ * (u₁ : L) = (v₂ : L) * (v₁ : L)⁻¹ := by
          calc
            (u₂ : L)⁻¹ * (u₁ : L) =
                (u₂ : L)⁻¹ * ((u₁ : L) * (v₁ : L)) * (v₁ : L)⁻¹ := by group
            _ = (u₂ : L)⁻¹ * ((u₂ : L) * (v₂ : L)) * (v₁ : L)⁻¹ := by rw [h']
            _ = (v₂ : L) * (v₁ : L)⁻¹ := by group
        rw [hc]
        exact V'.mul_mem v₂.2 (V'.inv_mem v₁.2)
      have hti : (u₂ : L)⁻¹ * (u₁ : L) = 1 := by
        have hbot : (u₂ : L)⁻¹ * (u₁ : L) ∈ (⊥ : Subgroup L) := by
          rwa [psl2_ti hf hUV] at hmem
        simpa using hbot
      have hu : u₁ = u₂ := by
        apply Subtype.ext
        calc
          (u₁ : L) = (u₂ : L) * ((u₂ : L)⁻¹ * (u₁ : L)) := by group
          _ = (u₂ : L) * 1 := by rw [hti]
          _ = (u₂ : L) := mul_one _
      have hv : v₁ = v₂ := by
        apply Subtype.ext
        have hc : (u₂ : L) * (v₁ : L) = (u₂ : L) * (v₂ : L) := by
          rw [← h', ← hu]
        exact mul_left_cancel hc
      exact Prod.ext hu hv
    have h4H : 4 ≤ Nat.card H := by
      have hcardprod : Nat.card (U' × V') = 4 := by
        rw [Nat.card_prod, hU2, hV2]
      calc
        4 = Nat.card (U' × V') := hcardprod.symm
        _ ≤ Nat.card H := Nat.card_le_card_of_injective _ hginj
    have hdvd : Nat.card H ∣ 6 := by
      rw [← hL6]
      exact Subgroup.card_subgroup_dvd_card H
    have hH6 : Nat.card H = 6 := by
      have hle : Nat.card H ≤ 6 := by
        rw [← hL6]
        exact Nat.card_le_card_of_injective H.subtype H.subtype_injective
      have h456 : Nat.card H = 4 ∨ Nat.card H = 5 ∨ Nat.card H = 6 := by omega
      rcases h456 with h | h | h
      · rw [h] at hdvd
        norm_num at hdvd
      · rw [h] at hdvd
        norm_num at hdvd
      · exact h
    exact Subgroup.eq_top_of_card_eq H (by rw [hH6, ← hL6])

theorem psl2_borel_of_card (hf : 1 ≤ f)
    {H : Subgroup (PSL(2, GaloisField 2 f))}
    (hcard : Nat.card H = 2 ^ f * (2 ^ f - 1)) :
    ∃ U : Sylow 2 (PSL(2, GaloisField 2 f)),
      (U : Subgroup (PSL(2, GaloisField 2 f))) ≤ H ∧
        H = Subgroup.normalizer
          (U : Set (PSL(2, GaloisField 2 f))) := by
  classical
  let L := PSL(2, GaloisField 2 f)
  have hqpos : 0 < 2 ^ f := Nat.two_pow_pos f
  have hq2 : 2 ≤ 2 ^ f := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hLcard : Nat.card L = 2 ^ f * ((2 ^ f) ^ 2 - 1) := by
    simpa [L] using psl2_even_card (f := f) (by omega)
  obtain ⟨K, hKcard, -, hKH⟩ :=
    Sylow.exists_subgroup_card_pow_prime_le_le (G := L) (p := 2) (n := f)
      Nat.prime_two (H := ⊥) (L := H)
      (by rw [Subgroup.card_bot]; exact one_dvd _)
      (by rw [hcard]; exact dvd_mul_right _ _) bot_le
  have hKisP : IsPGroup 2 K := IsPGroup.of_card hKcard
  have hKindex : ¬ 2 ∣ K.index := by
    have hmul : 2 ^ f * K.index = 2 ^ f * ((2 ^ f) ^ 2 - 1) := by
      have h := Subgroup.card_mul_index K
      rw [hKcard, hLcard] at h
      exact h
    have hidx : K.index = (2 ^ f) ^ 2 - 1 :=
      Nat.eq_of_mul_eq_mul_left hqpos hmul
    have heven : Even (2 ^ f) := by
      exact Nat.even_pow.mpr ⟨even_two, by omega⟩
    have hodd1 : Odd (2 ^ f - 1) :=
      Nat.Even.sub_odd hqpos heven odd_one
    have hodd2 : Odd (2 ^ f + 1) := heven.add_odd odd_one
    have hidx' : K.index = (2 ^ f - 1) * (2 ^ f + 1) := by
      rw [hidx, show (2 ^ f) ^ 2 - 1 = (2 ^ f - 1) * (2 ^ f + 1) by
        rw [show (1 : ℕ) = 1 ^ 2 by norm_num, Nat.sq_sub_sq, one_pow, mul_comm]]
    have hodd : Odd K.index := by rw [hidx']; exact hodd1.mul hodd2
    intro h2
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)
  let U : Sylow 2 L := hKisP.toSylow hKindex
  have hUcoe : (U : Subgroup L) = K := rfl
  have hUle : (U : Subgroup L) ≤ H := by rw [hUcoe]; exact hKH
  have hHne : H ≠ ⊤ := by
    intro htop
    have heq : 2 ^ f * (2 ^ f - 1) = 2 ^ f * ((2 ^ f) ^ 2 - 1) := by
      have h : Nat.card H = Nat.card L := by rw [htop, Subgroup.card_top]
      rw [hcard, hLcard] at h
      exact h
    have hsub : 2 ^ f - 1 = (2 ^ f) ^ 2 - 1 :=
      Nat.eq_of_mul_eq_mul_left hqpos heq
    have : 2 ^ f = (2 ^ f) ^ 2 := by omega
    nlinarith
  have hHnorm : H ≤ Subgroup.normalizer (U : Set L) := by
    intro h hhH
    rw [← Sylow.smul_eq_iff_mem_normalizer]
    by_contra hne
    have hle : ((h • U : Sylow 2 L) : Subgroup L) ≤ H :=
      Sylow.smul_le (p := 2) (P := U) hUle ⟨h, hhH⟩
    have htop : ((U : Subgroup L) ⊔ ((h • U : Sylow 2 L) : Subgroup L)) = ⊤ :=
      psl2_sylow_two_sup_eq_top hf (fun heq => hne heq.symm)
    have : H = ⊤ := top_unique (htop ▸ sup_le hUle hle)
    exact hHne this
  refine ⟨U, hUle, ?_⟩
  refine Subgroup.eq_of_le_of_card_ge hHnorm ?_
  change Nat.card (Subgroup.normalizer
    ((U : Subgroup (PSL(2, GaloisField 2 f))) : Set (PSL(2, GaloisField 2 f)))) ≤ Nat.card H
  rw [psl2_even_card_normalizer_sylow_two (f := f) (by omega) U, hcard]

theorem psl2_torus_card (hf : 1 ≤ f)
    {U : Sylow 2 (PSL(2, GaloisField 2 f))}
    {D : Subgroup (PSL(2, GaloisField 2 f))}
    (hDU : D ⊓ (U : Subgroup (PSL(2, GaloisField 2 f))) = ⊥)
    (hsup : D ⊔ (U : Subgroup (PSL(2, GaloisField 2 f))) =
      Subgroup.normalizer (U : Set (PSL(2, GaloisField 2 f)))) :
    Nat.card D = 2 ^ f - 1 := by
  classical
  let L := PSL(2, GaloisField 2 f)
  let N : Subgroup L := Subgroup.normalizer (U : Set L)
  have hDle : D ≤ N := by
    dsimp [N]
    rw [← hsup]
    exact le_sup_left
  have hUle : (U : Subgroup L) ≤ N := by
    dsimp [N]
    rw [← hsup]
    exact le_sup_right
  let fmap : D × (U : Subgroup L) → N := fun p =>
    ⟨(p.1 : L) * (p.2 : L), N.mul_mem (hDle p.1.2) (hUle p.2.2)⟩
  have hinj : Function.Injective fmap := by
    rintro ⟨d₁, u₁⟩ ⟨d₂, u₂⟩ h
    have h' : (d₁ : L) * (u₁ : L) = (d₂ : L) * (u₂ : L) := congrArg Subtype.val h
    have hmem : (d₂ : L)⁻¹ * (d₁ : L) ∈
        D ⊓ (U : Subgroup (PSL(2, GaloisField 2 f))) := by
      refine ⟨D.mul_mem (D.inv_mem d₂.2) d₁.2, ?_⟩
      have hc : (d₂ : L)⁻¹ * (d₁ : L) = (u₂ : L) * (u₁ : L)⁻¹ := by
        calc
          (d₂ : L)⁻¹ * (d₁ : L) =
              (d₂ : L)⁻¹ * ((d₁ : L) * (u₁ : L)) * (u₁ : L)⁻¹ := by group
          _ = (d₂ : L)⁻¹ * ((d₂ : L) * (u₂ : L)) * (u₁ : L)⁻¹ := by rw [h']
          _ = (u₂ : L) * (u₁ : L)⁻¹ := by group
      rw [hc]
      exact U.mul_mem u₂.2 (U.inv_mem u₁.2)
    have hd : (d₂ : L)⁻¹ * (d₁ : L) = 1 := by
      have := hmem
      rw [hDU] at this
      simpa using this
    have hdd : d₁ = d₂ := by
      apply Subtype.ext
      calc
        (d₁ : L) = (d₂ : L) * ((d₂ : L)⁻¹ * (d₁ : L)) := by group
        _ = (d₂ : L) * 1 := by rw [hd]
        _ = (d₂ : L) := mul_one _
    have huu : u₁ = u₂ := by
      apply Subtype.ext
      have hc : (d₂ : L) * (u₁ : L) = (d₂ : L) * (u₂ : L) := by rw [← h', ← hdd]
      exact mul_left_cancel hc
    exact Prod.ext hdd huu
  have hsurj : Function.Surjective fmap := by
    intro n
    have hmem : (n : L) ∈ (D : Set L) * ((U : Subgroup L) : Set L) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right D (U : Subgroup L) hDle, hsup]
      exact n.2
    obtain ⟨d, hd, u, hu, hdu⟩ := hmem
    exact ⟨⟨⟨d, hd⟩, ⟨u, hu⟩⟩, Subtype.ext hdu⟩
  have hNcard : Nat.card N = 2 ^ f * (2 ^ f - 1) := by
    change Nat.card (Subgroup.normalizer
      ((U : Subgroup (PSL(2, GaloisField 2 f))) : Set (PSL(2, GaloisField 2 f)))) =
      2 ^ f * (2 ^ f - 1)
    exact psl2_even_card_normalizer_sylow_two (f := f) (by omega) U
  have hbij := Nat.card_congr (Equiv.ofBijective fmap ⟨hinj, hsurj⟩)
  rw [Nat.card_prod, psl2_sylow_two_card hf U, hNcard] at hbij
  have h' : 2 ^ f * Nat.card D = 2 ^ f * (2 ^ f - 1) := by
    rw [mul_comm, hbij]
  exact Nat.eq_of_mul_eq_mul_left (Nat.two_pow_pos f) h'

theorem psl2_normalizer_quotient_cyclic (hf : 2 ≤ f)
    (U : Sylow 2 (PSL(2, GaloisField 2 f))) :
    IsCyclic (Subgroup.normalizer (U : Set (PSL(2, GaloisField 2 f))) ⧸
      (U : Subgroup (PSL(2, GaloisField 2 f))).subgroupOf
        (Subgroup.normalizer (U : Set (PSL(2, GaloisField 2 f))))) := by
  classical
  let L := PSL(2, GaloisField 2 f)
  let N : Subgroup L := Subgroup.normalizer (U : Set L)
  obtain ⟨D0, hD0cyc, -, hUD0, hsup0, -⟩ := psl2_even_normalizer_sylow_two hf U
  have hD0le : D0 ≤ N := by
    change D0 ≤ Subgroup.normalizer (U : Set L)
    exact le_trans le_sup_right (le_of_eq hsup0)
  have hD0sup : D0 ⊔ (U : Subgroup L) = N := by
    change D0 ⊔ (U : Subgroup L) = Subgroup.normalizer (U : Set L)
    rw [sup_comm]
    exact hsup0
  haveI : ((U : Subgroup L).subgroupOf N).Normal := by
    change ((U : Subgroup L).subgroupOf
      (Subgroup.normalizer (U : Set L))).Normal
    exact Subgroup.normal_subgroupOf_of_le_normalizer le_rfl
  let π : N →* N ⧸ (U : Subgroup L).subgroupOf N := QuotientGroup.mk' _
  let ι : D0 →* N := Subgroup.inclusion hD0le
  let πD0 : D0 →* N ⧸ (U : Subgroup L).subgroupOf N := π.comp ι
  have hπ_inj : Function.Injective πD0 := by
    intro d₁ d₂ hq
    have hmem : (d₂ : L)⁻¹ * (d₁ : L) ∈ (U : Subgroup L) := by
      have h1 : πD0 (d₂⁻¹ * d₁) = 1 := by
        rw [map_mul, map_inv, hq, inv_mul_cancel]
      have h2 : (⟨(d₂ : L)⁻¹ * (d₁ : L),
          N.mul_mem (N.inv_mem (hD0le d₂.2)) (hD0le d₁.2)⟩ : N) ∈
          (U : Subgroup L).subgroupOf N := by
        rw [← QuotientGroup.eq_one_iff]
        exact h1
      exact h2
    have hmemD : (d₂ : L)⁻¹ * (d₁ : L) ∈ D0 :=
      D0.mul_mem (D0.inv_mem d₂.2) d₁.2
    have hbot : (d₂ : L)⁻¹ * (d₁ : L) ∈ (⊥ : Subgroup L) := by
      rw [← hUD0]
      exact ⟨hmem, hmemD⟩
    have hd : (d₂ : L)⁻¹ * (d₁ : L) = 1 := by simpa using hbot
    apply Subtype.ext
    calc
      (d₁ : L) = (d₂ : L) * ((d₂ : L)⁻¹ * (d₁ : L)) := by group
      _ = (d₂ : L) * 1 := by rw [hd]
      _ = (d₂ : L) := mul_one _
  have hπ_surj : Function.Surjective πD0 := by
    intro x
    obtain ⟨n, rfl⟩ := QuotientGroup.mk'_surjective _ x
    have hmem : (n : L) ∈ (D0 : Set L) * ((U : Subgroup L) : Set L) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right D0 (U : Subgroup L) hD0le, hD0sup]
      exact n.2
    obtain ⟨d, hd, u, hu, hdu⟩ := hmem
    refine ⟨⟨d, hd⟩, ?_⟩
    have hnd : (n : L) = (d : L) * (u : L) := hdu.symm
    apply QuotientGroup.eq.mpr
    change ((d : L)⁻¹ * (n : L)) ∈ (U : Subgroup L)
    rw [hnd]
    simpa [mul_assoc] using U.inv_mem hu
  let e0 : D0 ≃* (N ⧸ (U : Subgroup L).subgroupOf N) :=
    MulEquiv.ofBijective πD0 ⟨hπ_inj, hπ_surj⟩
  haveI : IsCyclic D0 := hD0cyc
  change IsCyclic (N ⧸ (U : Subgroup L).subgroupOf N)
  exact isCyclic_of_injective e0.symm.toMonoidHom e0.symm.injective

theorem psl2_torus_cyclic (hf : 1 ≤ f)
    {U : Sylow 2 (PSL(2, GaloisField 2 f))}
    {D : Subgroup (PSL(2, GaloisField 2 f))}
    (hDU : D ⊓ (U : Subgroup (PSL(2, GaloisField 2 f))) = ⊥)
    (hsup : D ⊔ (U : Subgroup (PSL(2, GaloisField 2 f))) =
      Subgroup.normalizer (U : Set (PSL(2, GaloisField 2 f)))) :
    IsCyclic D := by
  classical
  by_cases hf2 : 2 ≤ f
  · let L := PSL(2, GaloisField 2 f)
    let N : Subgroup L := Subgroup.normalizer (U : Set L)
    have hDle : D ≤ N := by
      change D ≤ Subgroup.normalizer (U : Set L)
      exact le_trans le_sup_left (le_of_eq hsup)
    haveI : ((U : Subgroup L).subgroupOf N).Normal := by
      change ((U : Subgroup L).subgroupOf
        (Subgroup.normalizer (U : Set L))).Normal
      exact Subgroup.normal_subgroupOf_of_le_normalizer le_rfl
    let πD : D →* N ⧸ (U : Subgroup L).subgroupOf N :=
      (QuotientGroup.mk' _).comp (Subgroup.inclusion hDle)
    have hQcyc : IsCyclic (N ⧸ (U : Subgroup L).subgroupOf N) := by
      have h := psl2_normalizer_quotient_cyclic hf2 U
      change IsCyclic (N ⧸ (U : Subgroup L).subgroupOf N)
      exact h
    haveI : IsCyclic (N ⧸ (U : Subgroup L).subgroupOf N) := hQcyc
    have hinj : Function.Injective πD := by
      intro d₁ d₂ hq
      have hmem : (d₂ : L)⁻¹ * (d₁ : L) ∈ (U : Subgroup L) := by
        have h1 : πD (d₂⁻¹ * d₁) = 1 := by
          rw [map_mul, map_inv, hq, inv_mul_cancel]
        have h2 : (⟨(d₂ : L)⁻¹ * (d₁ : L),
            N.mul_mem (N.inv_mem (hDle d₂.2)) (hDle d₁.2)⟩ : N) ∈
            (U : Subgroup L).subgroupOf N := by
          rw [← QuotientGroup.eq_one_iff]
          exact h1
        exact h2
      have hmemD : (d₂ : L)⁻¹ * (d₁ : L) ∈ D :=
        D.mul_mem (D.inv_mem d₂.2) d₁.2
      have hbot : (d₂ : L)⁻¹ * (d₁ : L) ∈ (⊥ : Subgroup L) := by
        rw [← hDU]
        exact ⟨hmemD, hmem⟩
      have hd : (d₂ : L)⁻¹ * (d₁ : L) = 1 := by simpa using hbot
      apply Subtype.ext
      calc
        (d₁ : L) = (d₂ : L) * ((d₂ : L)⁻¹ * (d₁ : L)) := by group
        _ = (d₂ : L) * 1 := by rw [hd]
        _ = (d₂ : L) := mul_one _
    exact isCyclic_of_injective πD hinj
  · have hf1 : f = 1 := by omega
    have hcardD : Nat.card D = 1 := by
      have h := psl2_torus_card hf hDU hsup
      have h3 : 2 ^ f - 1 = 1 := by rw [hf1]; norm_num
      rwa [h3] at h
    have hbot : D = ⊥ := Subgroup.eq_bot_of_card_eq D hcardD
    rw [hbot]
    infer_instance

theorem psl2_torus_fixed_card_two (hf : 2 ≤ f)
    {U : Sylow 2 (PSL(2, GaloisField 2 f))}
    {D : Subgroup (PSL(2, GaloisField 2 f))}
    (hDU : D ⊓ (U : Subgroup (PSL(2, GaloisField 2 f))) = ⊥)
    (hsup : D ⊔ (U : Subgroup (PSL(2, GaloisField 2 f))) =
      Subgroup.normalizer (U : Set (PSL(2, GaloisField 2 f)))) :
    ∀ d : D, d ≠ 1 → Nat.card (MulAction.fixedBy (Sylow 2 (PSL(2, GaloisField 2 f))) d) = 2 := by
  classical
  let L := PSL(2, GaloisField 2 f)
  let N : Subgroup L := Subgroup.normalizer (U : Set L)
  have hDle : D ≤ N := by
    change D ≤ Subgroup.normalizer (U : Set L)
    exact le_trans le_sup_left (le_of_eq hsup)
  have hUfix : ∀ d : D, U ∈ MulAction.fixedBy (Sylow 2 L) d := by
    intro d
    rw [MulAction.mem_fixedBy, MulAction.subgroup_smul_def,
      Sylow.smul_eq_iff_mem_normalizer]
    exact hDle d.2
  have hfix_iff : ∀ (d : D) (W : Sylow 2 L),
      W ∈ MulAction.fixedBy (Sylow 2 L) d ↔
        (d : L) ∈ Subgroup.normalizer (W : Set L) := by
    intro d W
    rw [MulAction.mem_fixedBy, MulAction.subgroup_smul_def,
      Sylow.smul_eq_iff_mem_normalizer]
  have hKcard : Nat.card (GaloisField 2 f) = 2 ^ f :=
    GaloisField.card 2 f (by omega)
  have hbound : ∀ d : D, d ≠ 1 →
      Nat.card (MulAction.fixedBy (Sylow 2 L) d) ≤ 2 := by
    intro d hd1
    have hd1' : (d : L) ≠ 1 := fun h => hd1 (Subtype.ext h)
    have h := CFSG.GorensteinWalter.psl2_normalized_rootSylow_card_le_two
      (K := GaloisField 2 f) (r := 2) (f := f) hKcard (d : L) hd1'
    let e : MulAction.fixedBy (Sylow 2 L) d →
        {S : Sylow 2 L // (d : L) ∈ Subgroup.normalizer (S : Set L)} :=
      fun S => ⟨S.1, (hfix_iff d S.1).mp S.2⟩
    have hinj : Function.Injective e := by
      intro a b hab
      have hval : (e a : Sylow 2 L) = (e b : Sylow 2 L) := congrArg Subtype.val hab
      exact Subtype.ext hval
    exact le_trans (Nat.card_le_card_of_injective e hinj) h
  let : Fintype D := Fintype.ofFinite D
  let : Fintype (Sylow 2 L) := Fintype.ofFinite (Sylow 2 L)
  let : Fintype (MulAction.orbitRel.Quotient D (Sylow 2 L)) :=
    Fintype.ofFinite _
  let : ∀ d : D, Fintype (MulAction.fixedBy (Sylow 2 L) d) :=
    fun d => Fintype.ofFinite _
  let fcard : D → ℕ := fun d => Nat.card (MulAction.fixedBy (Sylow 2 L) d)
  have hburnside : (∑ d : D, fcard d) =
      Nat.card (MulAction.orbitRel.Quotient D (Sylow 2 L)) * Nat.card D := by
    simpa [fcard, Nat.card_eq_fintype_card] using
      MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group (G := D) (X := Sylow 2 L)
  have hfix_one : fcard 1 = 2 ^ f + 1 := by
    have hset : MulAction.fixedBy (Sylow 2 L) (1 : D) = Set.univ := by
      ext W
      rw [MulAction.mem_fixedBy]
      simp
    change Nat.card (MulAction.fixedBy (Sylow 2 L) (1 : D)) = 2 ^ f + 1
    rw [hset, Nat.card_coe_set_eq, Set.ncard_univ]
    exact psl2_even_card_sylow (f := f) (by omega)
  have hfix_pos : ∀ d : D, 0 < fcard d := fun d => by
    have hne : (MulAction.fixedBy (Sylow 2 L) d).Nonempty := ⟨U, hUfix d⟩
    exact Nat.card_pos_iff.mpr ⟨hne.to_subtype, Set.toFinite _⟩
  have hT_eq : (∑ d : D, (fcard d - 1)) =
      (fcard 1 - 1) + Finset.sum (Finset.univ.erase (1 : D)) (fun d => fcard d - 1) := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (1 : D))]
    exact add_comm _ _
  have hsum_add : (∑ d : D, ((fcard d - 1) + 1)) = ∑ d : D, fcard d := by
    apply Finset.sum_congr rfl
    intro d _
    exact Nat.sub_add_cancel (hfix_pos d)
  have hsum_split : (∑ d : D, ((fcard d - 1) + 1)) =
      (∑ d : D, (fcard d - 1)) + Nat.card D := by
    rw [Finset.sum_add_distrib]
    simp [Nat.card_eq_fintype_card]
  have hS : (∑ d : D, fcard d) = (∑ d : D, (fcard d - 1)) + Nat.card D := by
    rw [← hsum_add, hsum_split]
  have hdvdS : Nat.card D ∣ ∑ d : D, fcard d := by
    rw [hburnside]
    exact dvd_mul_left _ _
  have hdvdT : Nat.card D ∣ ∑ d : D, (fcard d - 1) := by
    have hsub : (∑ d : D, fcard d) - Nat.card D = ∑ d : D, (fcard d - 1) := by
      omega
    rw [← hsub]
    exact Nat.dvd_sub hdvdS (dvd_refl _)
  have hDcard : Nat.card D = 2 ^ f - 1 := psl2_torus_card (by omega) hDU hsup
  have hq3 : 3 ≤ 2 ^ f := by
    calc 3 ≤ 4 := by norm_num
      _ = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hDpos : 0 < Nat.card D := by rw [hDcard]; omega
  have h1 : fcard 1 - 1 = Nat.card D + 1 := by
    rw [hfix_one, hDcard]
    omega
  have hcard_erase : (Finset.sum (Finset.univ.erase (1 : D)) (fun _ => (1 : ℕ))) = Nat.card D - 1 := by
    rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ, Nat.card_eq_fintype_card, smul_eq_mul, mul_one]
  have hT_lower : Nat.card D + 1 ≤ ∑ d : D, (fcard d - 1) := by
    rw [hT_eq]
    have hnonneg : 0 ≤ Finset.sum (Finset.univ.erase (1 : D)) (fun d => fcard d - 1) :=
      Finset.sum_nonneg fun d _ => by
        have := hfix_pos d
        omega
    omega
  have hT_upper : (∑ d : D, (fcard d - 1)) ≤ 2 * Nat.card D := by
    rw [hT_eq]
    have hupper : (Finset.sum (Finset.univ.erase (1 : D)) (fun d => fcard d - 1)) ≤
        Finset.sum (Finset.univ.erase (1 : D)) (fun _ => (1 : ℕ)) := by
      apply Finset.sum_le_sum
      intro d hd
      have hd1 : d ≠ 1 := Finset.ne_of_mem_erase hd
      have hle : fcard d ≤ 2 := by simpa [fcard] using hbound d hd1
      have hpos := hfix_pos d
      omega
    rw [hcard_erase] at hupper
    omega
  have hT : (∑ d : D, (fcard d - 1)) = 2 * Nat.card D := by
    rcases hdvdT with ⟨k, hk⟩
    have hk_le : k ≤ 2 := by
      have hle : k * Nat.card D ≤ 2 * Nat.card D := by
        calc
          k * Nat.card D = Nat.card D * k := mul_comm _ _
          _ = ∑ d : D, (fcard d - 1) := hk.symm
          _ ≤ 2 * Nat.card D := hT_upper
      exact Nat.le_of_mul_le_mul_right hle hDpos
    have hk_ge : 1 ≤ k := by
      by_contra hk0
      have hk0' : k = 0 := by omega
      rw [hk0', mul_zero] at hk
      have := hT_lower
      rw [hk] at this
      omega
    have hk2 : k = 2 := by
      by_contra hk2
      have hk1 : k = 1 := by omega
      rw [hk1, mul_one] at hk
      have := hT_lower
      rw [hk] at this
      omega
    rw [hk2, mul_comm (Nat.card D) 2] at hk
    exact hk
  have hT' : (Finset.sum (Finset.univ.erase (1 : D)) (fun d => fcard d - 1)) = Nat.card D - 1 := by
    have := hT
    rw [hT_eq, h1] at this
    omega
  have hle' : ∀ d ∈ Finset.univ.erase (1 : D), fcard d - 1 ≤ 1 := by
    intro d hd
    have hd1 : d ≠ 1 := Finset.ne_of_mem_erase hd
    have hle : fcard d ≤ 2 := by simpa [fcard] using hbound d hd1
    have hpos := hfix_pos d
    omega
  have hall : ∀ d ∈ Finset.univ.erase (1 : D), fcard d - 1 = 1 := by
    intro d hd
    by_contra hne
    have hlt : fcard d - 1 < 1 := by
      have := hle' d hd
      omega
    have hsum_lt : (Finset.sum (Finset.univ.erase (1 : D)) (fun e => fcard e - 1)) <
        Finset.sum (Finset.univ.erase (1 : D)) (fun _ => (1 : ℕ)) := by
      apply Finset.sum_lt_sum
      · intro e he
        exact hle' e he
      · exact ⟨d, hd, hlt⟩
    rw [hcard_erase, hT'] at hsum_lt
    omega
  intro d hd1
  have hdmem : d ∈ Finset.univ.erase (1 : D) :=
    Finset.mem_erase.mpr ⟨hd1, Finset.mem_univ d⟩
  have := hall d hdmem
  have hpos := hfix_pos d
  change fcard d = 2
  omega

theorem psl2_torus_fixed_sylow (hf : 2 ≤ f)
    {U : Sylow 2 (PSL(2, GaloisField 2 f))}
    {D : Subgroup (PSL(2, GaloisField 2 f))}
    (hDU : D ⊓ (U : Subgroup (PSL(2, GaloisField 2 f))) = ⊥)
    (hsup : D ⊔ (U : Subgroup (PSL(2, GaloisField 2 f))) =
      Subgroup.normalizer (U : Set (PSL(2, GaloisField 2 f)))) :
    ∃ V : Sylow 2 (PSL(2, GaloisField 2 f)),
      V ≠ U ∧
      D ≤ Subgroup.normalizer (V : Set (PSL(2, GaloisField 2 f))) ∧
      ∀ d : D, d ≠ 1 → ∀ W : Sylow 2 (PSL(2, GaloisField 2 f)),
        (d : PSL(2, GaloisField 2 f)) ∈
          Subgroup.normalizer (W : Set (PSL(2, GaloisField 2 f))) ↔
          W = U ∨ W = V := by
  classical
  let L := PSL(2, GaloisField 2 f)
  let N : Subgroup L := Subgroup.normalizer (U : Set L)
  have hDle : D ≤ N := by
    change D ≤ Subgroup.normalizer (U : Set L)
    exact le_trans le_sup_left (le_of_eq hsup)
  have hUfix : ∀ d : D, U ∈ MulAction.fixedBy (Sylow 2 L) d := by
    intro d
    rw [MulAction.mem_fixedBy, MulAction.subgroup_smul_def,
      Sylow.smul_eq_iff_mem_normalizer]
    exact hDle d.2
  have hfix_iff : ∀ (d : D) (W : Sylow 2 L),
      W ∈ MulAction.fixedBy (Sylow 2 L) d ↔
        (d : L) ∈ Subgroup.normalizer (W : Set L) := by
    intro d W
    rw [MulAction.mem_fixedBy, MulAction.subgroup_smul_def,
      Sylow.smul_eq_iff_mem_normalizer]
  have hcard_two := psl2_torus_fixed_card_two hf hDU hsup
  have hDcard : Nat.card D = 2 ^ f - 1 := psl2_torus_card (by omega) hDU hsup
  have hq4 : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hD1lt : 1 < Nat.card D := by rw [hDcard]; omega
  haveI : Nontrivial D := Finite.one_lt_card_iff_nontrivial.mp hD1lt
  obtain ⟨d0, hd0⟩ : ∃ d0 : D, d0 ≠ 1 := exists_ne (1 : D)
  have hfixd0 : Nat.card (MulAction.fixedBy (Sylow 2 L) d0) = 2 := hcard_two d0 hd0
  have hfixd0' : (MulAction.fixedBy (Sylow 2 L) d0).ncard = 2 := by
    rw [← Nat.card_coe_set_eq]
    exact hfixd0
  have hsdiff : (MulAction.fixedBy (Sylow 2 L) d0 \ {U}).ncard = 1 := by
    rw [Set.ncard_sdiff_singleton_of_mem (hUfix d0), hfixd0']
  have hne : (MulAction.fixedBy (Sylow 2 L) d0 \ {U}).Nonempty := by
    rw [← Set.ncard_pos (s := MulAction.fixedBy (Sylow 2 L) d0 \ {U})]
    omega
  obtain ⟨V, hVdiff⟩ := hne
  have hVmem : V ∈ MulAction.fixedBy (Sylow 2 L) d0 := hVdiff.1
  have hVne : V ≠ U := by
    intro hVU
    exact hVdiff.2 (by simp [hVU])
  have hfixset0 : MulAction.fixedBy (Sylow 2 L) d0 = {U, V} := by
    apply Set.eq_of_subset_of_ncard_le (t := ({U, V} : Set (Sylow 2 L)))
    · intro W hW
      rw [Set.mem_insert_iff, Set.mem_singleton_iff]
      by_contra h
      push Not at h
      have hsub3 : ({U, V, W} : Set (Sylow 2 L)) ⊆
          MulAction.fixedBy (Sylow 2 L) d0 := by
        intro X hX
        rcases hX with rfl | hX
        · exact hUfix d0
        rcases hX with rfl | rfl
        · exact hVmem
        · exact hW
      have htriple : ({U, V, W} : Set (Sylow 2 L)).ncard = 3 := by
        have hset : ({U, V, W} : Set (Sylow 2 L)) =
            insert W ({U, V} : Set (Sylow 2 L)) := by
          ext Y
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
          tauto
        rw [hset, Set.ncard_insert_of_notMem (by simp [h.1, h.2]),
          Set.ncard_pair hVne.symm]
      have hcard3 : 3 ≤ (MulAction.fixedBy (Sylow 2 L) d0).ncard := by
        calc 3 = ({U, V, W} : Set (Sylow 2 L)).ncard := htriple.symm
          _ ≤ (MulAction.fixedBy (Sylow 2 L) d0).ncard :=
              Set.ncard_le_ncard hsub3
      rw [show (MulAction.fixedBy (Sylow 2 L) d0).ncard = 2 from by
        rw [← Nat.card_coe_set_eq]; exact hfixd0] at hcard3
      omega
    · have hpair : ({U, V} : Set (Sylow 2 L)).ncard = 2 := by
        rw [Set.ncard_pair hVne.symm]
      rw [show (MulAction.fixedBy (Sylow 2 L) d0).ncard = 2 from by
        rw [← Nat.card_coe_set_eq]; exact hfixd0, hpair]
  have hVfix_all : ∀ d : D, d ≠ 1 → V ∈ MulAction.fixedBy (Sylow 2 L) d := by
    intro d hd1
    rw [MulAction.mem_fixedBy]
    haveI : IsCyclic D := psl2_torus_cyclic (by omega) hDU hsup
    have hcomm : Commute d0 d := (inferInstance : IsMulCommutative D).is_comm.comm d0 d
    have hWV : d • V ∈ MulAction.fixedBy (Sylow 2 L) d0 := by
      rw [MulAction.mem_fixedBy]
      calc
        d0 • (d • V) = (d0 * d) • V := by rw [mul_smul]
        _ = (d * d0) • V := by rw [hcomm.eq]
        _ = d • (d0 • V) := by rw [mul_smul]
        _ = d • V := by rw [MulAction.mem_fixedBy.mp hVmem]
    rw [hfixset0, Set.mem_insert_iff, Set.mem_singleton_iff] at hWV
    rcases hWV with hWV | hWV
    · exfalso
      have hVU : V = U := by
        calc
          V = d⁻¹ • (d • V) := by rw [← mul_smul, inv_mul_cancel, one_smul]
          _ = d⁻¹ • U := by rw [hWV]
          _ = U := MulAction.mem_fixedBy.mp (hUfix d⁻¹)
      exact hVne hVU
    · exact hWV
  have hVle : D ≤ Subgroup.normalizer (V : Set L) := by
    intro d hd
    by_cases hd1 : (⟨d, hd⟩ : D) = 1
    · have hdL : d = 1 := congrArg Subtype.val hd1
      subst hdL
      exact Subgroup.one_mem _
    · exact (hfix_iff ⟨d, hd⟩ V).mp (hVfix_all ⟨d, hd⟩ hd1)
  refine ⟨V, hVne, hVle, ?_⟩
  intro d hd1 W
  rw [← hfix_iff d W]
  have hfixsetd : MulAction.fixedBy (Sylow 2 L) d = {U, V} := by
    apply Set.eq_of_subset_of_ncard_le (t := ({U, V} : Set (Sylow 2 L)))
    · intro X hX
      rw [Set.mem_insert_iff, Set.mem_singleton_iff]
      by_contra h
      push Not at h
      have hsub3 : ({U, V, X} : Set (Sylow 2 L)) ⊆
          MulAction.fixedBy (Sylow 2 L) d := by
        intro Y hY
        rcases hY with rfl | hY
        · exact hUfix d
        rcases hY with rfl | rfl
        · exact hVfix_all d hd1
        · exact hX
      have htriple : ({U, V, X} : Set (Sylow 2 L)).ncard = 3 := by
        have hset : ({U, V, X} : Set (Sylow 2 L)) =
            insert X ({U, V} : Set (Sylow 2 L)) := by
          ext Y
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
          tauto
        rw [hset, Set.ncard_insert_of_notMem (by simp [h.1, h.2]),
          Set.ncard_pair hVne.symm]
      have hle : 3 ≤ (MulAction.fixedBy (Sylow 2 L) d).ncard := by
        calc 3 = ({U, V, X} : Set (Sylow 2 L)).ncard := htriple.symm
          _ ≤ (MulAction.fixedBy (Sylow 2 L) d).ncard :=
              Set.ncard_le_ncard hsub3
      have hcardd : (MulAction.fixedBy (Sylow 2 L) d).ncard = 2 := by
        rw [← Nat.card_coe_set_eq]
        exact hcard_two d hd1
      rw [hcardd] at hle
      omega
    · have hcardd : (MulAction.fixedBy (Sylow 2 L) d).ncard = 2 := by
        rw [← Nat.card_coe_set_eq]
        exact hcard_two d hd1
      rw [hcardd]
      have hpair : ({U, V} : Set (Sylow 2 L)).ncard = 2 := by
        rw [Set.ncard_pair hVne.symm]
      rw [hpair]
  rw [hfixsetd, Set.mem_insert_iff, Set.mem_singleton_iff]

theorem psl2_torus_normalizer_inf (hf : 2 ≤ f)
    {U : Sylow 2 (PSL(2, GaloisField 2 f))}
    {D : Subgroup (PSL(2, GaloisField 2 f))}
    (hDU : D ⊓ (U : Subgroup (PSL(2, GaloisField 2 f))) = ⊥)
    (hsup : D ⊔ (U : Subgroup (PSL(2, GaloisField 2 f))) =
      Subgroup.normalizer (U : Set (PSL(2, GaloisField 2 f))))
    {V : Sylow 2 (PSL(2, GaloisField 2 f))} (hVU : V ≠ U)
    (hVle : D ≤ Subgroup.normalizer (V : Set (PSL(2, GaloisField 2 f)))) :
    Subgroup.normalizer (U : Set (PSL(2, GaloisField 2 f))) ⊓
      Subgroup.normalizer (V : Set (PSL(2, GaloisField 2 f))) = D := by
  classical
  let L := PSL(2, GaloisField 2 f)
  let N : Subgroup L := Subgroup.normalizer (U : Set L)
  have hDle : D ≤ N := by
    change D ≤ Subgroup.normalizer (U : Set L)
    exact le_trans le_sup_left (le_of_eq hsup)
  refine le_antisymm ?_ (le_inf hDle ?_)
  · rintro x ⟨hxU, hxV⟩
    have hxmem : x ∈ (D : Set L) * ((U : Subgroup L) : Set L) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right D (U : Subgroup L) hDle, hsup]
      exact hxU
    obtain ⟨d, hd, u, hu, hdu⟩ := hxmem
    have huV : u ∈ Subgroup.normalizer (V : Set L) := by
      have hdInv : d⁻¹ ∈ Subgroup.normalizer (V : Set L) :=
        Subgroup.inv_mem (H := Subgroup.normalizer (V : Set L)) (hVle hd)
      have : d⁻¹ * x ∈ Subgroup.normalizer (V : Set L) :=
        Subgroup.mul_mem (H := Subgroup.normalizer (V : Set L)) hdInv hxV
      rw [← hdu] at this
      simpa [mul_assoc] using this
    have hu1 : u = 1 := by
      by_contra hu_ne
      have hvu : V = U := (psl2_sylow_two_normalizes_iff (by omega) (U := U) (V := V)
        hu hu_ne).mp huV
      exact hVU hvu
    rw [← hdu, hu1]
    simpa using hd
  · change D ≤ Subgroup.normalizer (V : Set L)
    exact hVle

theorem psl2_torus_regular_on_sylow (hf : 2 ≤ f)
    {U : Sylow 2 (PSL(2, GaloisField 2 f))}
    {D : Subgroup (PSL(2, GaloisField 2 f))}
    (hDU : D ⊓ (U : Subgroup (PSL(2, GaloisField 2 f))) = ⊥)
    (hsup : D ⊔ (U : Subgroup (PSL(2, GaloisField 2 f))) =
      Subgroup.normalizer (U : Set (PSL(2, GaloisField 2 f)))) :
    ∀ u ∈ (U : Subgroup (PSL(2, GaloisField 2 f))), u ≠ 1 →
      ∀ v ∈ (U : Subgroup (PSL(2, GaloisField 2 f))), v ≠ 1 →
        ∃ d ∈ D, d * u * d⁻¹ = v := by
  classical
  let L := PSL(2, GaloisField 2 f)
  let N : Subgroup L := Subgroup.normalizer (U : Set L)
  have hDle : D ≤ N := by
    change D ≤ Subgroup.normalizer (U : Set L)
    exact le_trans le_sup_left (le_of_eq hsup)
  intro u hu hu1 v hv hv1
  have hcen : Subgroup.centralizer ({u} : Set L) = (U : Subgroup L) :=
    psl2_even_centralizer_involution hf U hu hu1
  let g : D → {w : (U : Subgroup L) // w ≠ 1} := fun d =>
    ⟨⟨d * u * d⁻¹, (Subgroup.mem_normalizer_iff.mp (hDle d.2) u).mp hu⟩, by
      intro h
      have hL : d * u * d⁻¹ = 1 := congrArg Subtype.val h
      have hu_eq : u = 1 := by
        have := congrArg (fun z : L => d⁻¹ * z * d) hL
        simpa [mul_assoc] using this
      exact hu1 hu_eq⟩
  have hginj : Function.Injective g := by
    intro d₁ d₂ h
    have hval : (g d₁ : (U : Subgroup L)) = (g d₂ : (U : Subgroup L)) :=
      congrArg Subtype.val h
    have hvalU : (g d₁ : (U : Subgroup L)) = (g d₂ : (U : Subgroup L)) :=
      congrArg Subtype.val h
    have hvalL : (d₁ : L) * u * (d₁ : L)⁻¹ =
        (d₂ : L) * u * (d₂ : L)⁻¹ := by
      have := congrArg (fun z : (U : Subgroup L) => (z : L)) hvalU
      simpa [g] using this
    let w : L := (d₂ : L)⁻¹ * (d₁ : L)
    have hcomm : w * u = u * w := by
      dsimp [w]
      calc
        ((d₂ : L)⁻¹ * (d₁ : L)) * u =
            (d₂ : L)⁻¹ * ((d₁ : L) * u * (d₁ : L)⁻¹) * (d₁ : L) := by group
        _ = (d₂ : L)⁻¹ * ((d₂ : L) * u * (d₂ : L)⁻¹) * (d₁ : L) :=
            congrArg (fun z : L => (d₂ : L)⁻¹ * z * (d₁ : L)) hvalL
        _ = u * ((d₂ : L)⁻¹ * (d₁ : L)) := by group
    have hmemC : w ∈ Subgroup.centralizer ({u} : Set L) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hcomm
    have hmemD : w ∈ D := D.mul_mem (D.inv_mem d₂.2) d₁.2
    have hbot : w ∈ (⊥ : Subgroup L) := by
      rw [hcen] at hmemC
      rw [← hDU]
      exact ⟨hmemD, hmemC⟩
    have hw : w = 1 := by simpa using hbot
    have hdL : (d₂ : L)⁻¹ * (d₁ : L) = 1 := hw
    apply Subtype.ext
    calc
      (d₁ : L) = (d₂ : L) * ((d₂ : L)⁻¹ * (d₁ : L)) := by group
      _ = (d₂ : L) * 1 := by rw [hdL]
      _ = (d₂ : L) := mul_one _
  have hcardD : Nat.card D = 2 ^ f - 1 := psl2_torus_card (by omega) hDU hsup
  have hcardU : Nat.card (U : Subgroup L) = 2 ^ f := psl2_sylow_two_card (by omega) U
  have hcardUsharp : Nat.card {w : (U : Subgroup L) // w ≠ 1} = 2 ^ f - 1 := by
    haveI : Finite (U : Subgroup L) :=
      Finite.of_injective (fun x : (U : Subgroup L) => (x : L)) Subtype.coe_injective
    let : Fintype (U : Subgroup L) := Fintype.ofFinite _
    let : Fintype {w : (U : Subgroup L) // w ≠ 1} := Fintype.ofFinite _
    have hcardU' : Fintype.card (U : Subgroup L) = 2 ^ f := by
      rw [← Nat.card_eq_fintype_card]
      exact hcardU
    rw [Nat.card_eq_fintype_card,
      Fintype.card_subtype_compl (p := fun w : (U : Subgroup L) => w = 1),
      Fintype.card_subtype_eq, hcardU']
  have hbij : Function.Bijective g := by
    refine hginj.bijective_of_nat_card_le ?_
    rw [hcardUsharp, hcardD]
  have hv1' : (⟨v, hv⟩ : (U : Subgroup L)) ≠ 1 := fun h => hv1 (congrArg Subtype.val h)
  obtain ⟨d, hd⟩ := hbij.2 ⟨⟨v, hv⟩, hv1'⟩
  refine ⟨d, d.2, ?_⟩
  have h1 : ((g d : (U : Subgroup L)) : L) = v := by
    have := congrArg (fun z : {w : (U : Subgroup L) // w ≠ 1} =>
      ((z.1 : (U : Subgroup L)) : L)) hd
    simpa using this
  simpa [g] using h1

theorem psl2_torus_centralizer (hf : 2 ≤ f)
    {U : Sylow 2 (PSL(2, GaloisField 2 f))}
    {D : Subgroup (PSL(2, GaloisField 2 f))}
    (hDU : D ⊓ (U : Subgroup (PSL(2, GaloisField 2 f))) = ⊥)
    (hsup : D ⊔ (U : Subgroup (PSL(2, GaloisField 2 f))) =
      Subgroup.normalizer (U : Set (PSL(2, GaloisField 2 f)))) :
    Subgroup.centralizer (D : Set (PSL(2, GaloisField 2 f))) = D := by
  classical
  let L := PSL(2, GaloisField 2 f)
  let N : Subgroup L := Subgroup.normalizer (U : Set L)
  have hDle : D ≤ N := by
    change D ≤ Subgroup.normalizer (U : Set L)
    exact le_trans le_sup_left (le_of_eq hsup)
  obtain ⟨V, hVU, hVle, hViff⟩ := psl2_torus_fixed_sylow hf hDU hsup
  have hNinf : N ⊓ Subgroup.normalizer (V : Set L) = D := by
    change Subgroup.normalizer (U : Set L) ⊓ Subgroup.normalizer (V : Set L) = D
    exact psl2_torus_normalizer_inf hf hDU hsup hVU hVle
  haveI : IsCyclic D := psl2_torus_cyclic (by omega) hDU hsup
  have hDcard : Nat.card D = 2 ^ f - 1 := psl2_torus_card (by omega) hDU hsup
  have hDodd : Odd (Nat.card D) := by
    rw [hDcard]
    have heven : Even (2 ^ f) := Nat.even_pow.mpr ⟨even_two, by omega⟩
    exact Nat.Even.sub_odd (Nat.two_pow_pos f) heven odd_one
  have hD1lt : 1 < Nat.card D := by
    rw [hDcard]
    have h4 : 4 ≤ 2 ^ f := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    omega
  haveI : Nontrivial D := Finite.one_lt_card_iff_nontrivial.mp hD1lt
  obtain ⟨d0, hd0⟩ : ∃ d0 : D, d0 ≠ 1 := exists_ne (1 : D)
  have hfix_iff : ∀ W : Sylow 2 L,
      (d0 : L) ∈ Subgroup.normalizer (W : Set L) ↔ W = U ∨ W = V :=
    fun W => hViff d0 hd0 W
  have hd0odd : Odd (orderOf (d0 : L)) := by
    exact Odd.of_dvd_nat hDodd (Subgroup.orderOf_dvd_natCard D d0.2)
  refine le_antisymm ?_ ?_
  · intro c hc
    have hcD : c ∈ Subgroup.centralizer (D : Set L) := hc
    have hc_comm : c * (d0 : L) = (d0 : L) * c :=
      (Subgroup.mem_centralizer_iff.mp hcD (d0 : L) d0.2).symm
    have hfix_cU : c • U ∈ ({U, V} : Set (Sylow 2 L)) := by
      have hd0N : (d0 : L) ∈ Subgroup.normalizer ((c • U : Sylow 2 L) : Set L) := by
        rw [← Sylow.smul_eq_iff_mem_normalizer]
        calc
          (d0 : L) • (c • U) = ((d0 : L) * c) • U := by rw [mul_smul]
          _ = (c * (d0 : L)) • U := by rw [hc_comm]
          _ = c • ((d0 : L) • U) := by rw [mul_smul]
          _ = c • U := by
            rw [show (d0 : L) • U = U from
              (Sylow.smul_eq_iff_mem_normalizer.mpr (hDle d0.2))]
      have := (hfix_iff (c • U)).mp hd0N
      simpa using this
    have hfix_cV : c • V ∈ ({U, V} : Set (Sylow 2 L)) := by
      have hd0N : (d0 : L) ∈ Subgroup.normalizer ((c • V : Sylow 2 L) : Set L) := by
        rw [← Sylow.smul_eq_iff_mem_normalizer]
        calc
          (d0 : L) • (c • V) = ((d0 : L) * c) • V := by rw [mul_smul]
          _ = (c * (d0 : L)) • V := by rw [hc_comm]
          _ = c • ((d0 : L) • V) := by rw [mul_smul]
          _ = c • V := by
            rw [show (d0 : L) • V = V from
              (Sylow.smul_eq_iff_mem_normalizer.mpr (hVle d0.2))]
      have := (hfix_iff (c • V)).mp hd0N
      simpa using this
    rcases (by simpa using hfix_cU) with hcU | hcU
    ·
      have hcV : c • V = V := by
        rcases (by simpa using hfix_cV) with hcV | hcV
        · exfalso
          have : c • U = c • V := by rw [hcU, hcV]
          have : U = V := (MulAction.injective c) this
          exact hVU this.symm
        · exact hcV
      rw [← hNinf]
      exact ⟨(Sylow.smul_eq_iff_mem_normalizer.mp hcU),
        (Sylow.smul_eq_iff_mem_normalizer.mp hcV)⟩
    ·
      have hcV : c • V = U := by
        rcases (by simpa using hfix_cV) with hcV | hcV
        · exact hcV
        · exfalso
          have : c • U = c • V := by rw [hcU, hcV]
          have : U = V := (MulAction.injective c) this
          exact hVU this.symm
      have hc2U : c ^ 2 • U = U := by
        rw [pow_two, mul_smul, hcU, hcV]
      have hc2V : c ^ 2 • V = V := by
        rw [pow_two, mul_smul, hcV, hcU]
      have hc2D : c ^ 2 ∈ D := by
        rw [← hNinf]
        exact ⟨(Sylow.smul_eq_iff_mem_normalizer.mp hc2U),
          (Sylow.smul_eq_iff_mem_normalizer.mp hc2V)⟩
      have h_not_odd : ¬ Odd (orderOf c) := by
        intro hodd
        obtain ⟨k, hk⟩ := hodd
        have hc2kD : (c ^ 2) ^ k ∈ D := D.pow_mem hc2D k
        have hfixV : (c ^ 2) ^ k • V = V :=
          Sylow.smul_eq_iff_mem_normalizer.mpr (hVle hc2kD)
        have hpow : c ^ (2 * k + 1) • U = V := by
          rw [show c ^ (2 * k + 1) = (c ^ 2) ^ k * c by
            rw [pow_succ, pow_mul]]
          rw [mul_smul, hcU, hfixV]
        have hpow1 : c ^ (orderOf c) = 1 := pow_orderOf_eq_one c
        have hpow1' : c ^ (2 * k + 1) = 1 := by rw [← hk]; exact hpow1
        rw [hpow1', one_smul] at hpow
        exact hVU hpow.symm
      have heven : Even (orderOf c) := Nat.not_odd_iff_even.mp h_not_odd
      obtain ⟨k, hk⟩ := heven
      let t : L := c ^ k
      have ht2 : t ^ 2 = 1 := by
        dsimp [t]
        rw [← pow_mul]
        rw [show k * 2 = orderOf c by omega, pow_orderOf_eq_one]
      have ht_ne : t ≠ 1 := by
        intro ht1
        have hck : c ^ k = 1 := ht1
        have hdvd : orderOf c ∣ k := orderOf_dvd_of_pow_eq_one hck
        have hkpos : 0 < k := by
          have := orderOf_pos c
          omega
        have hklt : k < orderOf c := by omega
        exact (Nat.not_dvd_of_pos_of_lt hkpos hklt) hdvd
      have htcomm : t * (d0 : L) = (d0 : L) * t := by
        dsimp [t]
        have hpow_comm : ∀ n : ℕ, c ^ n * (d0 : L) = (d0 : L) * c ^ n := by
          intro n
          induction n with
          | zero => simp
          | succ n ih =>
              rw [pow_succ, mul_assoc, hc_comm, ← mul_assoc, ih, mul_assoc]
        simpa using hpow_comm k
      let z : Subgroup L := Subgroup.zpowers t
      have htord : orderOf t = 2 := orderOf_eq_prime (by simpa using ht2) ht_ne
      have hzP : IsPGroup 2 z := by
        refine IsPGroup.of_card (n := 1) ?_
        rw [Nat.card_zpowers, htord]
        rfl
      obtain ⟨T, hT⟩ := hzP.exists_le_sylow
      have htT : t ∈ (T : Subgroup L) := hT (Subgroup.mem_zpowers t)
      have hcenT : Subgroup.centralizer ({t} : Set L) = (T : Subgroup L) :=
        psl2_even_centralizer_involution hf T htT ht_ne
      have hd0memT : (d0 : L) ∈ (T : Subgroup L) := by
        rw [← hcenT]
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact htcomm.symm
      obtain ⟨n, hn⟩ := T.isPGroup' ⟨(d0 : L), hd0memT⟩
      have hnL : (d0 : L) ^ (2 ^ n) = 1 := congrArg Subtype.val hn
      have hdvd : orderOf (d0 : L) ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hnL
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
      have hj0 : j = 0 := by
        cases j with
        | zero => rfl
        | succ j =>
            exfalso
            have heven : Even (2 ^ (j + 1)) := by
              rw [pow_succ]
              exact even_two.mul_left _
            exact (Nat.not_even_iff_odd.mpr (hj ▸ hd0odd)) heven
      have horderone : orderOf (d0 : L) = 1 := by
        rw [hj, hj0, pow_zero]
      exfalso
      exact hd0 (Subtype.ext (orderOf_eq_one_iff.mp horderone))
  · intro d hd
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hcommD : (⟨y, hy⟩ : D) * ⟨d, hd⟩ = ⟨d, hd⟩ * ⟨y, hy⟩ :=
      (inferInstance : IsMulCommutative D).is_comm.comm ⟨y, hy⟩ ⟨d, hd⟩
    exact congrArg Subtype.val hcommD

end CFSG.Quasithin.St84
