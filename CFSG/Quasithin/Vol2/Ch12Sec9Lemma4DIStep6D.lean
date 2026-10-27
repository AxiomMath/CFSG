module

public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma4DIStep6C
public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma4DIStep6B
public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma4DIStep6

public section

namespace CFSG.Quasithin.H13.C1294

open CFSG.Open CFSG.Quasithin CFSG.Blueprint CFSG.Quasithin.H13

section Assembly

variable {G : Type} [Group G] [Finite G]

theorem order_three_not_mem_two_group {H : Subgroup G} (hH : IsPGroup 2 H) {y : G}
    (hy : y ∈ H) (hy3 : orderOf y = 3) : False := by
  obtain ⟨n, hn⟩ := hH ⟨y, hy⟩
  have h : y ^ 2 ^ n = 1 := by
    have := congrArg Subtype.val hn
    simpa using this
  have hd : orderOf y ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one h
  rw [hy3] at hd
  have : (3 : ℕ) ∣ 2 ^ n := hd
  have h3 : Nat.Prime 3 := Nat.prime_three
  have := (Nat.Prime.dvd_of_dvd_pow h3 this)
  omega

theorem step6_main (h1222 : Stmt12_2_2) (h12213 : Stmt12_2_13) (h1289 : Lemma12_8_9W)
    (h12810 : Lemma12_8_10) (h12812 : Lemma12_8_12_two) (h12813 : Lemma12_8_13)
    (F2 : FactF2) (F3 : FactF3)
    {T L V V₁ V₂ K₁ : Subgroup G} (hcx : Cx1291 G T L V 4) (hs : Setting1282One G T L V 4 V₁ V₂)
    (hLK : lOne L V₁ ≤ K₁) (hK₁H : K₁ ≤ Subgroup.normalizer (V₁ : Set G))
    (hK₁U : K₁ ≤ Subgroup.normalizer (u128 V V₁ : Set G))
    {g : G} (hgP : g ∈ p128 T L V) (hgN : g ∉ Subgroup.normalizer (V₁ : Set G))
    (hlt : V₁ < zU128 V V₁)
    (D : HatModelU (u128 V V₁)) {q : D.V → ZMod 2}
    (hΩF4 : F4Out q D.B (D.img K₁))
    (S : Submodule (ZMod 2) D.V) (hS3 : Module.finrank (ZMod 2) S = 3)
    (hSq : ∀ s ∈ S, q s = 0) (hSV : ∀ v ∈ V, D.π v ∈ S)
    (hSπ : ∀ s ∈ S, ∃ v ∈ V, D.π v = s)
    (hTS : ∀ t ∈ T, ∀ htU : t ∈ Subgroup.normalizer (u128 V V₁ : Set G),
      D.ρ ⟨t, htU⟩ ∈ stabS S)
    (hTΩ : ∀ t ∈ T, ∀ htU : t ∈ Subgroup.normalizer (u128 V V₁ : Set G),
      D.ρ ⟨t, htU⟩ ∈ D.img K₁)
    {a : G} (haV₂ : a ∈ V₂) (haV₁ : a ∉ V₁)
    (hker : ∀ k : G, ∀ hk : k ∈ K₁, ∀ hkN : k ∈ Subgroup.normalizer (u128 V V₁ : Set G),
      D.ρ ⟨k, hkN⟩ = 1 ↔ k ∈ pCoreOf 2 K₁)
    {M : Type} [AddCommGroup M] [Module (ZMod 2) M] [Finite M]
    (hM : Module.finrank (ZMod 2) M = 4)
    (kap : ↥(D.img K₁) ≃* (M ≃ₗ[ZMod 2] M))
    (p ℓ Pl : Submodule (ZMod 2) M) (hp : Module.finrank (ZMod 2) p = 1)
    (hℓ : Module.finrank (ZMod 2) ℓ = 2) (hPl : Module.finrank (ZMod 2) Pl = 3)
    (hpℓ : p < ℓ) (hℓPl : ℓ < Pl)
    (hY₁ : kmapOf (D.img K₁) kap (stabS (Submodule.span (ZMod 2) {D.π a})) = stabS ℓ)
    (hY₂ : kmapOf (D.img K₁) kap (stabS S) = stabS p ∨ kmapOf (D.img K₁) kap (stabS S) = stabS Pl)
    {y₀ : G} (hy₀ : y₀ ∈ L ⊓ Subgroup.centralizer (V₂ : Set G)) (hy₀3 : orderOf y₀ = 3) :
    kmapOf (D.img K₁) kap (D.img (CFSG.conjugate (zU128 V V₁) g)) =
        pCoreOf 2 (kmapOf (D.img K₁) kap (stabS S)) ⊓ pCoreOf 2 (stabS ℓ) ∧
      Nat.card ↥(D.img (CFSG.conjugate (zU128 V V₁) g)) = 4 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := hcx.hyp.hyp.irrPlus.2.2.1
  set Dg := CFSG.conjugate (zU128 V V₁) g with hDg
  set Y₂ := kmapOf (D.img K₁) kap (stabS S) with hY₂def
  set D0 := pCoreOf 2 Y₂ ⊓ pCoreOf 2 (stabS ℓ) with hD0
  have hDgT : Dg ≤ T := Dg_le_T h1222 h1289 hcx hs hgP hgN
  have hLV' := hLV
  have hDgC : ∀ d ∈ Dg, d ∈ Subgroup.centralizer (V : Set G) := fun d hd =>
    Dg_le_centralizer_V h12813 hs hgP hgN hd
  have hV₁V : V₁ ≤ V := hs.v1.1
  have hCC : Subgroup.centralizer (V : Set G) ≤ Subgroup.centralizer (V₁ : Set G) :=
    Subgroup.centralizer_le (fun x hx => hV₁V hx)
  have hDgN1 : ∀ d ∈ Dg, d ∈ Subgroup.normalizer (V₁ : Set G) := fun d hd =>
    Subgroup.centralizer_le_normalizer _ (hCC (hDgC d hd))
  have hDgU : ∀ d ∈ Dg, d ∈ Subgroup.normalizer (u128 V V₁ : Set G) := fun d hd =>
    le_normalizer_conjClosure V _ (hDgN1 d hd)
  have hDdΩ : D.img Dg ≤ (D.img K₁) := by
    intro γ hγ
    obtain ⟨d, hd, hdN, rfl⟩ := (L128A.HatU.mem_img D).1 hγ
    exact hTΩ d (hDgT hd) hdN
  have hy₀L : y₀ ∈ L := (Subgroup.mem_inf.1 hy₀).1
  have hy₀C : y₀ ∈ Subgroup.centralizer (V₂ : Set G) := (Subgroup.mem_inf.1 hy₀).2
  have hy₀K : y₀ ∈ K₁ := L0_le_K₁ hLK hs.le (Subgroup.subset_closure ⟨hy₀, by rw [hy₀3]; decide⟩)
  have hy₀U : y₀ ∈ Subgroup.normalizer (u128 V V₁ : Set G) := hK₁U hy₀K
  have hy₀V : y₀ ∈ Subgroup.normalizer (V : Set G) := hLV hy₀L
  have hy₀V₁ : y₀ ∈ Subgroup.normalizer (V₁ : Set G) := hK₁H hy₀K
  have hy₀V₂ : y₀ ∈ Subgroup.normalizer (V₂ : Set G) := Subgroup.centralizer_le_normalizer _ hy₀C
  have hfixa : y₀ * a * y₀⁻¹ = a := by
    have hc := (Subgroup.mem_centralizer_iff.1 hy₀C) a haV₂
    calc y₀ * a * y₀⁻¹ = (y₀ * a) * y₀⁻¹ := rfl
      _ = (a * y₀) * y₀⁻¹ := by rw [← hc]
      _ = a := by group
  have hρy₀a : D.ρ ⟨y₀, hy₀U⟩ (D.π a) = D.π a := by
    rw [D.ρ_π ⟨y₀, hy₀U⟩ a (le_conjClosure V _ (hs.v2.1 haV₂)), hfixa]
  have hρy₀Ω : D.ρ ⟨y₀, hy₀U⟩ ∈ (D.img K₁) := L128A.HatU.rho_mem_img D hy₀K hy₀U
  have hρy₀ne : D.ρ ⟨y₀, hy₀U⟩ ≠ 1 := fun h =>
    order_three_not_mem_two_group (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K₁)
      ((hker y₀ hy₀K hy₀U).1 h) hy₀3
  have hρy₀S : D.ρ ⟨y₀, hy₀U⟩ ∈ stabS S := rho_stab_S D hSV hSπ hy₀V hy₀U
  have hρy₀stab : D.ρ ⟨y₀, hy₀U⟩ ∈ stabS (Submodule.span (ZMod 2) {D.π a}) :=
    mem_stabS_span_of_fix hρy₀a
  set ρ₀ : ↥(D.img K₁) := ⟨D.ρ ⟨y₀, hy₀U⟩, hρy₀Ω⟩ with hρ₀
  set g₀ : M ≃ₗ[ZMod 2] M := kap ρ₀ with hg₀
  have hρ₀ne : ρ₀ ≠ 1 := by
    intro h
    apply hρy₀ne
    exact congrArg Subtype.val h
  have hg₀ne : g₀ ≠ 1 := by
    intro h
    apply hρ₀ne
    apply kap.injective
    rw [map_one]
    exact h
  have hy3 : y₀ ^ 3 = 1 := by
    rw [← hy₀3]
    exact pow_orderOf_eq_one y₀
  have h1 : (⟨y₀, hy₀U⟩ : Subgroup.normalizer (u128 V V₁ : Set G)) ^ 3 = 1 :=
    Subtype.ext (by simpa using hy3)
  have hρ₀3 : ρ₀ ^ 3 = 1 := by
    apply Subtype.ext
    show (D.ρ ⟨y₀, hy₀U⟩) ^ 3 = 1
    rw [← map_pow, h1, map_one]
  have hg₀3 : g₀ ^ 3 = 1 := by
    rw [hg₀, ← map_pow, hρ₀3, map_one]
  have hg₀ord : orderOf g₀ = 3 := orderOf_eq_prime hg₀3 hg₀ne
  have hρ₀mem : ρ₀ ∈ (stabS (Submodule.span (ZMod 2) {D.π a})).subgroupOf (D.img K₁) :=
    Subgroup.mem_subgroupOf.2 hρy₀stab
  have hρ₀memS : ρ₀ ∈ (stabS S).subgroupOf (D.img K₁) := Subgroup.mem_subgroupOf.2 hρy₀S
  have hg₀ℓ : g₀ ∈ stabS ℓ := by
    rw [← hY₁]
    exact Subgroup.mem_map_of_mem kap.toMonoidHom hρ₀mem
  have hg₀Y₂ : g₀ ∈ Y₂ := Subgroup.mem_map_of_mem kap.toMonoidHom hρ₀memS
  set Kd := kmapOf (D.img K₁) kap (D.img Dg) with hKd
  have hKd_norm : ∀ x ∈ Kd, g₀ * x * g₀⁻¹ ∈ Kd := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
    have hyD : (y : D.V ≃ₗ[ZMod 2] D.V) ∈ D.img Dg := Subgroup.mem_subgroupOf.1 hy
    have hconj := rho_normalizes_Dg h12812 hs hgP hgN D hDgN1 hy₀V₁ hy₀V₂ hy₀U _ hyD
    refine Subgroup.mem_map.2 ⟨ρ₀ * y * ρ₀⁻¹, Subgroup.mem_subgroupOf.2 hconj, ?_⟩
    simp [hg₀, map_mul, map_inv]
  have hKd_le : Kd ≤ D0 := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
    have hyD : (y : D.V ≃ₗ[ZMod 2] D.V) ∈ D.img Dg := Subgroup.mem_subgroupOf.1 hy
    obtain ⟨d, hd, hdN, hdρ⟩ := (L128A.HatU.mem_img D).1 hyD
    have hpcs := rho_Dg_pieces h1222 h12213 h12810 hcx hs hgP hgN D hΩF4 S hS3 hSq hSV hSπ hTS hTΩ
      haV₂ haV₁ hd (hDgT hd) (hDgC d hd) hdN
    have hyeq : (y : D.V ≃ₗ[ZMod 2] D.V) = D.ρ ⟨d, hdN⟩ := hdρ.symm
    have hyΩ : (y : D.V ≃ₗ[ZMod 2] D.V) ∈ (D.img K₁) := y.2
    have hy_pc1 : (y : D.V ≃ₗ[ZMod 2] D.V) ∈ pCoreOf 2 (stabS S ⊓ D.img K₁) := by
      rw [hyeq]
      exact hpcs.1
    have hy_pc2 : (y : D.V ≃ₗ[ZMod 2] D.V) ∈ pCoreOf 2 (stabS (Submodule.span (ZMod 2) {D.π a})
        ⊓ D.img K₁) := by
      rw [hyeq]
      exact hpcs.2
    have h1 := (kmap_pCore_mem (D.img K₁) kap (stabS S) y.2 hy_pc1).2
    have h2 := (kmap_pCore_mem (D.img K₁) kap (stabS (Submodule.span (ZMod 2) {D.π a})) y.2
      hy_pc2).2
    have h2' : kap y ∈ pCoreOf 2 (stabS ℓ) := by
      have h3 : kmapOf (D.img K₁) kap (stabS (Submodule.span (ZMod 2) {D.π a})) = stabS ℓ := hY₁
      unfold kmapOf at h3
      rw [h3] at h2
      exact h2
    exact Subgroup.mem_inf.2 ⟨h1, h2'⟩
  obtain ⟨d0, hd0, hd0N, hd0ne⟩ := rho_Dg_ne_one h12813 hs hgP hgN D hDgN1 hlt
  have hΩd0 : D.ρ ⟨d0, hd0N⟩ ∈ D.img K₁ := hTΩ d0 (hDgT hd0) hd0N
  have hy0mem : (⟨D.ρ ⟨d0, hd0N⟩, hΩd0⟩ : ↥(D.img K₁)) ∈ (D.img Dg).subgroupOf (D.img K₁) :=
    Subgroup.mem_subgroupOf.2 (L128A.HatU.rho_mem_img D hd0 hd0N)
  have hkap0 : kap ⟨D.ρ ⟨d0, hd0N⟩, hΩd0⟩ ∈ kmapOf (D.img K₁) kap (D.img Dg) :=
    Subgroup.mem_map_of_mem kap.toMonoidHom hy0mem
  have hkap0ne : kap ⟨D.ρ ⟨d0, hd0N⟩, hΩd0⟩ ≠ 1 := by
    intro h
    apply hd0ne
    have h2 : (⟨D.ρ ⟨d0, hd0N⟩, hΩd0⟩ : ↥(D.img K₁)) = 1 := kap.injective (h.trans (map_one kap).symm)
    exact congrArg Subtype.val h2
  have hKd_ne : kmapOf (D.img K₁) kap (D.img Dg) ≠ ⊥ := by
    intro hbot
    apply hkap0ne
    have := hkap0
    rw [hbot] at this
    exact Subgroup.mem_bot.1 this
  haveI : Finite (M ≃ₗ[ZMod 2] M) :=
    Finite.of_injective (fun f : M ≃ₗ[ZMod 2] M => (f : M → M)) DFunLike.coe_injective
  have hfpf := fpf_D0 F3 hM p ℓ Pl hp hℓ hPl hpℓ hℓPl Y₂ hY₂ hg₀ord hg₀ℓ hg₀Y₂
  have hcard0 := card_D0 F2 hM p ℓ Pl hp hℓ hPl hpℓ hℓPl Y₂ hY₂
  have heq : kmapOf (D.img K₁) kap (D.img Dg) = D0 :=
    eq_of_fpf hcard0 hKd_le hKd_ne hg₀3 hKd_norm hfpf
  refine ⟨heq, ?_⟩
  have hcardKd : Nat.card ↥(kmapOf (D.img K₁) kap (D.img Dg)) = Nat.card ↥(D.img Dg) := by
    unfold kmapOf
    rw [Subgroup.card_map_of_injective kap.injective]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDdΩ).toEquiv
  rw [← hcardKd, heq, hcard0]

end Assembly


end CFSG.Quasithin.H13.C1294
