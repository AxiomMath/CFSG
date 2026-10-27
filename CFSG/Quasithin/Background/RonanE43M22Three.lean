module

public import CFSG.Quasithin.Background.RonanE43M22
public import CFSG.Quasithin.Background.RonanE43M22Pull
public import CFSG.Quasithin.Background.RonanE43M22Real
public import CFSG.Quasithin.Background.RonanE43Lift3
public import CFSG.Sporadic.Recognition.M22MultiplierCert

public section

namespace CFSG.Quasithin.RonanE43

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.E3 CFSG.QuasithinUnique
  CFSG.QuasithinUnique.Vol2Native.A312L.M22Lat

theorem center_map_normal {G : Type*} [Group G] {L : Subgroup G} (hK : L.Normal) :
    ((Subgroup.center ↥L).map L.subtype).Normal := by
  refine ⟨fun n hn g => ?_⟩
  obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hn
  have hgL : g * (w : G) * g⁻¹ ∈ L := hK.conj_mem _ w.2 g
  refine Subgroup.mem_map.mpr ⟨⟨g * (w : G) * g⁻¹, hgL⟩, ?_, rfl⟩
  rw [Subgroup.mem_center_iff]
  intro l
  apply Subtype.ext
  have hl' : g⁻¹ * (l : G) * g ∈ L := by simpa using hK.conj_mem _ l.2 g⁻¹
  have hc := congrArg Subtype.val (Subgroup.mem_center_iff.mp hw ⟨g⁻¹ * (l : G) * g, hl'⟩)
  simp only [Subgroup.coe_mul] at hc ⊢
  calc (l : G) * (g * (w : G) * g⁻¹) = g * ((g⁻¹ * (l : G) * g) * (w : G)) * g⁻¹ := by group
    _ = g * ((w : G) * (g⁻¹ * (l : G) * g)) * g⁻¹ := by rw [hc]
    _ = g * (w : G) * g⁻¹ * (l : G) := by group

theorem coprime_two_card_of_normal_comm {G : Type*} [Group G] [Finite G]
    (hO2 : pCoreOf 2 (⊤ : Subgroup G) = ⊥) {Z : Subgroup G} [Z.Normal]
    (hc : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a) : Nat.Coprime (Nat.card Z) 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
  intro hdvd
  let W : Subgroup G :=
    { carrier := {x | x ∈ Z ∧ ∃ n : ℕ, x ^ 2 ^ n = 1}
      one_mem' := ⟨Z.one_mem, 0, by simp⟩
      mul_mem' := by
        rintro a b ⟨ha, n, hn⟩ ⟨hb, m, hm⟩
        refine ⟨Z.mul_mem ha hb, n + m, ?_⟩
        have hcomm : Commute a b := hc a ha b hb
        have h1 : a ^ 2 ^ (n + m) = 1 := by rw [pow_add, pow_mul, hn, one_pow]
        have h2 : b ^ 2 ^ (n + m) = 1 := by rw [add_comm, pow_add, pow_mul, hm, one_pow]
        rw [hcomm.mul_pow, h1, h2, one_mul]
      inv_mem' := by
        rintro a ⟨ha, n, hn⟩
        exact ⟨Z.inv_mem ha, n, by rw [inv_pow, hn, inv_one]⟩ }
  haveI hWn : W.Normal := ⟨fun x hx g => by
    obtain ⟨hxZ, n, hn⟩ := hx
    exact ⟨‹Z.Normal›.conj_mem x hxZ g, n, by rw [conj_pow, hn]; simp⟩⟩
  have hWp : IsPGroup 2 W := fun x => by
    obtain ⟨n, hn⟩ := x.2.2
    exact ⟨n, Subtype.ext (by simpa using hn)⟩
  have hle : W ≤ pCoreOf 2 (⊤ : Subgroup G) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 le_top
      (by rw [(Subgroup.normalizer_eq_top_iff).mpr hWn]) hWp
  rw [hO2] at hle
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥Z) 2 hdvd
  have hord : orderOf (x : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hx
  have hx2 : (x : G) ^ 2 ^ 1 = 1 := by
    rw [pow_one, ← hord]
    exact pow_orderOf_eq_one _
  have hx1 : (x : G) = 1 := Subgroup.mem_bot.mp (hle ⟨x.2, 1, hx2⟩)
  rw [hx1, orderOf_one] at hord
  omega

section M22Three

variable {G : Type} [Group G] [Finite G]

open scoped IsMulCommutative in
theorem e43_M22_three (V : Type) [CommGroup V] [Finite V] (ρ : G →* MulAut V)
    (hρ : Function.Injective ρ) (hO2 : pCoreOf 2 (⊤ : Subgroup G) = ⊥) {T L : Subgroup G}
    (hT : IsSylowIn 2 T ⊤) (hlt : fixV ρ.range < fixV (T.map ρ))
    (hLF : L = CFSG.generalizedFitting G) (hLq : CFSG.IsQuasisimple ↥L)
    (h : IsSporadic .M22 (↥L ⧸ Subgroup.center ↥L))
    (hZ3 : Nat.card (Subgroup.center ↥L) = 3) : aParam ρ.range ≤ 3 := by
  classical
  haveI hK : L.Normal := normal_of_generalizedFitting hLF
  have hLT : L ⊔ T = ⊤ := sup_eq_top_of_index_le_two hT (index_le_two_of_M22 hLF hLq h)
  set Z : Subgroup G := (Subgroup.center ↥L).map L.subtype with hZdef
  have hZL : Z ≤ L := Subgroup.map_subtype_le _
  have hZcard : Nat.card Z = 3 := by
    rw [hZdef, Subgroup.card_map_of_injective L.subtype_injective, hZ3]
  have hZc : ∀ z ∈ Z, ∀ l ∈ L, z * l = l * z := by
    intro z hz l hl
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hz
    exact (congrArg Subtype.val (Subgroup.mem_center_iff.mp hw ⟨l, hl⟩)).symm
  haveI hZn : Z.Normal := center_map_normal hK
  let π : G →* G ⧸ Z := QuotientGroup.mk' Z
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective Z
  have hkerπ : π.ker = Z := QuotientGroup.ker_mk' Z
  have hT' : IsSylowIn 2 (T.map π) ⊤ :=
    ⟨le_top, hT.isPGroup.map π, by
      rw [Subgroup.relIndex_top_right]
      exact isSylowIn_map π hπ hT⟩
  have hL'n : (L.map π).Normal := hK.map π hπ
  let ψ : ↥L →* G ⧸ Z := π.comp L.subtype
  have hψker : ψ.ker = Subgroup.center ↥L := by
    ext x
    rw [MonoidHom.mem_ker]
    show π (x : G) = 1 ↔ _
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    constructor
    · rintro ⟨y, hy, hyx⟩
      have : y = x := Subtype.ext hyx
      rw [← this]
      exact hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  have hψrange : ψ.range = L.map π := by
    show (π.comp L.subtype).range = L.map π
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have h' := h
  obtain ⟨e⟩ := h'
  have e' : (↥L ⧸ Subgroup.center ↥L) ≃* ↥CFSG.Blueprint.NativeSporadic.M22 := e
  let eM : (↥L ⧸ Subgroup.center ↥L) ≃* ↥Mgrp :=
    e'.trans (MulEquiv.subgroupCongr mGens_closure.symm)
  let eQ : (↥L ⧸ Subgroup.center ↥L) ≃* ↥ψ.range :=
    (QuotientGroup.quotientMulEquivOfEq hψker.symm).trans (QuotientGroup.quotientKerEquivRange ψ)
  let e₀ : ↥(L.map π) ≃* ↥Mgrp :=
    (MulEquiv.subgroupCongr hψrange.symm).trans (eQ.symm.trans eM)
  obtain ⟨Ah, Vh, Ph, hAL, hPL, hA5, hAn, hPn, hTP, hP3, hAcard, hPcard, hgen⟩ :=
    m22_pull_data hT' hL'n e₀
  have hreal : ∀ y : ↥L ⧸ Subgroup.center ↥L, y ^ 3 = 1 →
      ∃ g : ↥L ⧸ Subgroup.center ↥L, g * y * g⁻¹ = y⁻¹ := by
    intro y hy
    obtain ⟨g, hg⟩ := real3_M22 (eM y) (by rw [← map_pow, hy, map_one])
    refine ⟨eM.symm g, ?_⟩
    apply eM.injective
    rw [map_mul, map_mul, map_inv, map_inv, MulEquiv.apply_symm_apply]
    exact hg
  have hker9 : (QuotientGroup.mk' (Subgroup.center ↥L)).ker =
      (Subgroup.center ↥L).subtype.range := by
    rw [QuotientGroup.ker_mk', Subgroup.range_subtype]
  have h9L := cube_eq_one_of_real (Λ := ↥L) (Γ := ↥L ⧸ Subgroup.center ↥L)
    (Zc := ↥(Subgroup.center ↥L)) hZ3 (Subgroup.center ↥L).subtype
    (Subgroup.subtype_injective _) (fun z => z.2) (QuotientGroup.mk' (Subgroup.center ↥L))
    (QuotientGroup.mk'_surjective _) hker9 hreal
  have h9 : ∀ x ∈ L, x ^ 3 ∈ Z → x ^ 3 = 1 := by
    intro x hx hx3
    have h1 : (⟨x, hx⟩ : ↥L) ^ 3 ∈ (Subgroup.center ↥L).subtype.range := by
      obtain ⟨w, hw, hwx⟩ := Subgroup.mem_map.mp hx3
      refine ⟨⟨w, hw⟩, ?_⟩
      apply Subtype.ext
      simpa using hwx
    have := h9L ⟨x, hx⟩ h1
    simpa using congrArg Subtype.val this
  haveI : Group.IsPerfect ↥L := hLq.1
  have hperf : L ≤ ⁅L, L⁆ := (Subgroup.commutator_eq_self (H := L)).ge
  have hGF : GoodFamily T 3 :=
    goodFamily_of_lift3 π hπ hkerπ hZcard hT hLT hZL hZc hperf h9 hA5 hAL hPL hAn hPn hTP hP3
      ⟨320, by omega, by norm_num⟩ ⟨128, by omega, by norm_num⟩ hgen
  exact aParam_le_of_goodFamily V ρ hρ hO2 hT hLF hLq hLT hlt hGF


theorem e43_M22_all (V : Type) [CommGroup V] [Finite V] (ρ : G →* MulAut V)
    (hρ : Function.Injective ρ) (hO2 : pCoreOf 2 (⊤ : Subgroup G) = ⊥) {T L : Subgroup G}
    (hT : IsSylowIn 2 T ⊤) (hlt : fixV ρ.range < fixV (T.map ρ))
    (hLF : L = CFSG.generalizedFitting G) (hLq : CFSG.IsQuasisimple ↥L)
    (h : IsSporadic .M22 (↥L ⧸ Subgroup.center ↥L)) : aParam ρ.range ≤ 3 := by
  classical
  haveI hK : L.Normal := normal_of_generalizedFitting hLF
  have h' := h
  obtain ⟨e⟩ := h'
  have e' : (↥L ⧸ Subgroup.center ↥L) ≃* ↥CFSG.Blueprint.NativeSporadic.M22 := e
  obtain ⟨-, hdvd⟩ :=
    CFSG.Sporadic.Recognition.M22Multiplier.center_cyclic_dvd_twelve_of_certificate
      (Group.isPerfect_def.2 hLq.1.commutator_eq_top) e'
  haveI hZn : ((Subgroup.center ↥L).map L.subtype).Normal := center_map_normal hK
  have hodd : Nat.Coprime (Nat.card ((Subgroup.center ↥L).map L.subtype)) 2 := by
    refine coprime_two_card_of_normal_comm hO2 ?_
    intro a ha b hb
    obtain ⟨w₁, hw₁, rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨w₂, hw₂, rfl⟩ := Subgroup.mem_map.mp hb
    exact (congrArg Subtype.val (Subgroup.mem_center_iff.mp hw₁ w₂)).symm
  rw [Subgroup.card_map_of_injective L.subtype_injective] at hodd
  have h2 : ¬ 2 ∣ Nat.card (Subgroup.center ↥L) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp hodd.symm
  have h13 : Nat.card (Subgroup.center ↥L) = 1 ∨ Nat.card (Subgroup.center ↥L) = 3 := by
    have hle : Nat.card (Subgroup.center ↥L) ≤ 12 := Nat.le_of_dvd (by norm_num) hdvd
    generalize Nat.card (Subgroup.center ↥L) = c at hdvd h2 hle ⊢
    interval_cases c <;> omega
  rcases h13 with h1 | h3
  · exact e43_M22' V ρ hρ hO2 hT hlt hLF hLq h (Or.inr (Subgroup.eq_bot_of_card_eq _ h1))
  · exact e43_M22_three V ρ hρ hO2 hT hlt hLF hLq h h3

end M22Three

end CFSG.Quasithin.RonanE43
