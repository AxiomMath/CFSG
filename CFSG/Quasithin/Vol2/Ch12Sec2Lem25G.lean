module

public import CFSG.Quasithin.Vol2.Ch12Sec2Lem25E
public import CFSG.Quasithin.Vol2.Ch12Sec2Lem25F

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique Matrix
open scoped IsMulCommutative

namespace Lem25

variable {G : Type} [Group G]

theorem comm_mem_of_index_two {V A : Subgroup G} (hA : (A.subgroupOf V).index = 2) {x : G}
    (hxV : x ∈ Subgroup.normalizer (V : Set G)) (hxA : x ∈ Subgroup.normalizer (A : Set G))
    {v : G} (hv : v ∈ V) : x * v * x⁻¹ * v⁻¹ ∈ A := by
  have hw : x * v * x⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hxV v).mp hv
  have h1 := (Subgroup.mul_mem_iff_of_index_two hA (a := (⟨x * v * x⁻¹, hw⟩ : ↥V))
    (b := (⟨v, hv⟩ : ↥V)⁻¹)).mpr (by
      rw [inv_mem_iff, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      exact ((Subgroup.mem_normalizer_iff.mp hxA v)).symm)
  rw [Subgroup.mem_subgroupOf] at h1
  exact h1

end Lem25

open Lem25

theorem lem12225N5_of
    (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (h323 : Stmt3_2_3)
    (h1216 : Stmt12_2_16) (h1220 : Stmt12_2_20) (hY : Lem12225YNormal) : Lem12225N5 := by
  intro G _ _ T L V H P U I h n p hH hNE hC
  classical
  rcases hC.2.2.1 with hn | hn | hn
  · exact Or.inl hn
  · exact Or.inr hn
  exfalso
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hCTL := ctl_eq_bot_of_yNormal h331 h1222 h323 h1216 h1220 hY hH hNE hC (by omega)
  have hstar := lem12225Star_of h331 h1222 h323 h1216 h1220 G T L V H P U I h n p hH hNE hC
  have hYN := hY G T L V H P U I h n p hH hNE hC (by omega)
  obtain ⟨S, rfl⟩ := exists_sylow_coe_eq hH.sylow
  obtain ⟨-, -, hc2, -, -, -, -, -, -, -, -, -, hYR⟩ := hstar
  obtain ⟨hHs, -, -, hVn, -, -, hp, hp2, hP, hord, hhH, hhM, hI, -, hUd, hUi, hUe, -, hUP,
    hidx, ⟨hcommV, -⟩, hUO, -, -, hHU, -, hIP, hHIT, -, -⟩ := hC
  subst hn
  set M := Subgroup.normalizer (L : Set G) with hMdef
  set Y := oTwoUpper (L ⊓ Subgroup.normalizer ((U ⊓ V : Subgroup G) : Set G)) with hYdef
  set N := Subgroup.normalizer (U : Set G) with hNdef
  have hTH : (S : Subgroup G) ≤ H := hHs.1.1
  have hLV := le_normalizer_of_hyp1223 hH
  have hVe : IsElemAbelian 2 V := S125.isElemAbelian_of_hyp1223 hH
  have hVab : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hVe.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hUab : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hUe.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hU2 : IsPGroup 2 U := B2F.isPGroup_of_isElemAbelian hUe
  have hUT : U ≤ (S : Subgroup G) :=
    hUO.trans (A7.pCoreOf_le_of_le_normalizer S (hTH.trans Subgroup.le_normalizer))
  obtain ⟨-, -, -, htop, -, -⟩ := h1220 G S L V hH hNE
  have : IsMulCommutative ↥V := hcommV
  have hV2' : ∀ v : ↥V, v * v = 1 := fun v => by
    rw [← pow_two]
    exact Subtype.ext (hVe.2 v v.2)
  have hPh : (P : Subgroup G) = Subgroup.zpowers h := hP
  obtain ⟨-, -, hall⟩ := ((h1222 G S hH.simple hH.nonabelian hH.qtke hH.sylow).resolve_left
    hH.notAlt) L hH.maximal hH.faithful hH.quasisimple
  obtain ⟨⟨hVT, hTV, hredV, -⟩, -, -, -, -⟩ := hall V hH.irrPlus
  have hUN : U ≤ Subgroup.normalizer (V : Set G) := hUT.trans hTV
  have hhI : h ∈ I := by rw [hIP]; exact Subgroup.mem_sup_left (Subgroup.mem_sup_left (hPh ▸
    Subgroup.mem_zpowers h))
  have hIH : I ≤ H := hHIT ▸ le_sup_left
  have hIN : I ≤ N := hIH.trans hHU
  have hhN : h ∈ N := hHU hhH
  have hVI : V ≤ I := by rw [hI]; exact le_sup_left
  have hVhI : CFSG.conjugate V h ≤ I := by rw [hI]; exact le_sup_right
  have hRU : (S : Subgroup G) ⊓ Subgroup.centralizer (U : Set G) = U := by
    rw [hc2, hCTL, sup_bot_eq]
  have hYU : Y ≤ N := by
    have := hYR
    rw [hRU] at this
    exact le_sup_left.trans this
  have hNY : N ≤ Subgroup.normalizer (Y : Set G) := by
    have := hYN
    rw [hRU] at this
    exact this
  have hhY : h ∈ Subgroup.normalizer (Y : Set G) := hNY hhN
  have hYLA : Y ≤ L ⊓ Subgroup.normalizer ((U ⊓ V : Subgroup G) : Set G) := oTwoUpper_le _
  have hYV : ∀ y ∈ Y, ∀ v ∈ V, y * v * y⁻¹ * v⁻¹ ∈ U ⊓ V := fun y hy v hv =>
    comm_mem_of_index_two hidx (hLV (hYLA hy).1) (hYLA hy).2 hv
  set K : Subgroup G :=
    { carrier := {g | g ∈ N ∧ ∀ y ∈ Y, g * y * g⁻¹ * y⁻¹ ∈ U}
      mul_mem' := by
        rintro a b ⟨haN, ha⟩ ⟨hbN, hb⟩
        refine ⟨N.mul_mem haN hbN, fun y hy => ?_⟩
        have h1 := (Subgroup.mem_normalizer_iff.mp haN _).mp (hb y hy)
        rw [show a * b * y * (a * b)⁻¹ * y⁻¹ =
          (a * (b * y * b⁻¹ * y⁻¹) * a⁻¹) * (a * y * a⁻¹ * y⁻¹) by group]
        exact U.mul_mem h1 (ha y hy)
      one_mem' := by
        refine ⟨N.one_mem, fun y _ => ?_⟩
        rw [one_mul, inv_one, mul_one, mul_inv_cancel]
        exact U.one_mem
      inv_mem' := by
        rintro a ⟨haN, ha⟩
        refine ⟨N.inv_mem haN, fun y hy => ?_⟩
        have h1 := (Subgroup.mem_normalizer_iff.mp (N.inv_mem haN) _).mp (U.inv_mem (ha y hy))
        rw [show a⁻¹ * y * a⁻¹⁻¹ * y⁻¹ = a⁻¹ * (a * y * a⁻¹ * y⁻¹)⁻¹ * a⁻¹⁻¹ by group]
        exact h1 } with hKdef
  have hVK : V ≤ K := fun v hv => ⟨hIN (hVI hv), fun y hy => by
    have h1 := (U ⊓ V).inv_mem (hYV y hy v hv)
    rw [show v * y * v⁻¹ * y⁻¹ = (y * v * y⁻¹ * v⁻¹)⁻¹ by group]
    exact h1.1⟩
  have hVhK : CFSG.conjugate V h ≤ K := fun x hx => by
    refine ⟨hIN (hVhI hx), fun y hy => ?_⟩
    have hxv : h * x * h⁻¹ ∈ V := BlueprintB2.mem_conjugate_iff.mp hx
    have hy' : h * y * h⁻¹ ∈ Y := (Subgroup.mem_normalizer_iff.mp hhY y).mp hy
    have h1 := (hVK hxv).2 _ hy'
    have h2 := (Subgroup.mem_normalizer_iff.mp (N.inv_mem hhN) _).mp h1
    rw [show x * y * x⁻¹ * y⁻¹ = h⁻¹ * ((h * x * h⁻¹) * (h * y * h⁻¹) * (h * x * h⁻¹)⁻¹ *
      (h * y * h⁻¹)⁻¹) * h⁻¹⁻¹ by group]
    exact h2
  have hIK : I ≤ K := by rw [hI]; exact sup_le hVK hVhK
  have hhK : ∀ y ∈ Y, h * y * h⁻¹ * y⁻¹ ∈ U := (hIK hhI).2
  have hcomm : ∀ y ∈ Y, ∀ x ∈ U, h * (y * x * y⁻¹) * h⁻¹ = y * (h * x * h⁻¹) * y⁻¹ := by
    intro y hy x hx
    have hc := hhK y hy
    have hz : y * (h * x * h⁻¹) * y⁻¹ ∈ U :=
      (Subgroup.mem_normalizer_iff.mp (hYU hy) _).mp
        ((Subgroup.mem_normalizer_iff.mp hhN x).mp hx)
    calc h * (y * x * y⁻¹) * h⁻¹ =
        (h * y * h⁻¹ * y⁻¹) * (y * (h * x * h⁻¹) * y⁻¹) * (h * y * h⁻¹ * y⁻¹)⁻¹ := by group
      _ = (y * (h * x * h⁻¹) * y⁻¹) * (h * y * h⁻¹ * y⁻¹) * (h * y * h⁻¹ * y⁻¹)⁻¹ := by
        rw [hUab _ hc _ hz]
      _ = y * (h * x * h⁻¹) * y⁻¹ := by group
  have hcard5 : Nat.card ↥V = 2 ^ (4 + 1) := hVn
  obtain ⟨e, he⟩ := exists_coords_index_two hV2' hcard5 (A := (U ⊓ V).subgroupOf V) hidx
  have he' : ∀ w : ↥V, (w : G) ∈ U ⊓ V ↔ Multiplicative.toAdd (e w) 0 = 0 := fun w => by
    rw [← he, Subgroup.mem_subgroupOf]
  have hψs := actGL_surjective hLV e htop
  have hodd3 : ∀ g : GL (Fin (4 + 1)) (ZMod 2), g ^ 3 = 1 → g ≠ 1 → Odd (orderOf g) :=
    fun g hg hg1 => by rw [orderOf_eq_three hg hg1]; decide
  obtain ⟨x₁, hx₁o, hx₁⟩ := exists_odd_lift (actGL hLV e) hψs (hodd3 _ m12_cube m12_ne_one)
  obtain ⟨x₂, hx₂o, hx₂⟩ := exists_odd_lift (actGL hLV e) hψs (hodd3 _ m23_cube m23_ne_one)
  have hx₁A : (x₁ : G) ∈ Subgroup.normalizer ((U ⊓ V : Subgroup G) : Set G) :=
    mem_normalizer_of_actGL hLV e 0 inf_le_right he' x₁ fun y => by
      rw [hx₁, coe_m12]; exact M12_mulVec_zero y
  have hx₂A : (x₂ : G) ∈ Subgroup.normalizer ((U ⊓ V : Subgroup G) : Set G) :=
    mem_normalizer_of_actGL hLV e 0 inf_le_right he' x₂ fun y => by
      rw [hx₂, coe_m23]; exact M23_mulVec_zero y
  have hx₁Y : (x₁ : G) ∈ Y := mem_oTwoUpper_of_odd ⟨x₁.2, hx₁A⟩ hx₁o
  have hx₂Y : (x₂ : G) ∈ Y := mem_oTwoUpper_of_odd ⟨x₂.2, hx₂A⟩ hx₂o
  set a : ↥V := e.symm (Multiplicative.ofAdd (Pi.single 4 1)) with hadef
  have hea : Multiplicative.toAdd (e a) = Pi.single 4 1 := by
    rw [hadef, MulEquiv.apply_symm_apply, toAdd_ofAdd]
  have haA : (a : G) ∈ U ⊓ V := by
    rw [he', hea]
    exact single4_zero
  have ha1 : (a : G) ≠ 1 := by
    intro h1
    have h2 : a = 1 := Subtype.ext h1
    have h3 := hea
    rw [h2, map_one, toAdd_one] at h3
    exact single4_ne_zero h3.symm
  have hfixa : ∀ (x : ↥L) (M0 : Matrix (Fin (4 + 1)) (Fin (4 + 1)) (ZMod 2)),
      ((actGL hLV e x : GL (Fin (4 + 1)) (ZMod 2)) : Matrix _ _ _) = M0 →
      M0 *ᵥ (Pi.single 4 1 : Fin (4 + 1) → ZMod 2) = Pi.single 4 1 →
      (x : G) * a * (x : G)⁻¹ = a := by
    intro x M0 hxM hM0
    have h1 := actGL_mulVec hLV e x a
    rw [hxM, hea, hM0, ← hea] at h1
    have h2 := e.injective (Multiplicative.toAdd.injective h1).symm
    have h3 := congrArg Subtype.val h2
    rwa [A4.actionOn_apply_coe] at h3
  have hx₁a : (x₁ : G) * a * (x₁ : G)⁻¹ = a :=
    hfixa x₁ M12 (by rw [hx₁, coe_m12]) M12_single4
  have hx₂a : (x₂ : G) * a * (x₂ : G)⁻¹ = a :=
    hfixa x₂ M23 (by rw [hx₂, coe_m23]) M23_single4
  have hCA : ∀ v ∈ U ⊓ V, (x₁ : G) * v * (x₁ : G)⁻¹ = v → (x₂ : G) * v * (x₂ : G)⁻¹ = v →
      v = 1 ∨ v = a := by
    intro v hv h1 h2
    set w : ↥V := ⟨v, hv.2⟩ with hw
    have hw0 : Multiplicative.toAdd (e w) 0 = 0 := (he' w).mp hv
    have hfix : ∀ (x : ↥L) (M0 : Matrix (Fin (4 + 1)) (Fin (4 + 1)) (ZMod 2)),
        ((actGL hLV e x : GL (Fin (4 + 1)) (ZMod 2)) : Matrix _ _ _) = M0 →
        (x : G) * v * (x : G)⁻¹ = v → M0 *ᵥ Multiplicative.toAdd (e w) =
          Multiplicative.toAdd (e w) := by
      intro x M0 hxM hxv
      have h3 := actGL_mulVec hLV e x w
      rw [hxM] at h3
      rw [h3]
      congr 2
      exact Subtype.ext (by rw [A4.actionOn_apply_coe]; exact hxv)
    rcases m12_m23_fix _ hw0 (hfix x₁ M12 (by rw [hx₁, coe_m12]) h1)
      (hfix x₂ M23 (by rw [hx₂, coe_m23]) h2) with h3 | h3
    · left
      have h4 : e w = 1 := Multiplicative.toAdd.injective (by rw [h3, toAdd_one])
      have h5 : w = 1 := by rw [← map_one e] at h4; exact e.injective h4
      exact congrArg Subtype.val h5
    · right
      have h4 : e w = e a := Multiplicative.toAdd.injective (by rw [h3, hea])
      exact congrArg Subtype.val (e.injective h4)
  set B := U ⊓ CFSG.conjugate V h with hBdef
  set F := U ⊓ Subgroup.centralizer ({(x₁ : G), (x₂ : G)} : Set G) with hFdef
  have hmemF : ∀ g, g ∈ F ↔ g ∈ U ∧ (x₁ : G) * g * (x₁ : G)⁻¹ = g ∧
      (x₂ : G) * g * (x₂ : G)⁻¹ = g := by
    intro g
    rw [hFdef, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
    constructor
    · rintro ⟨hg, hc⟩
      refine ⟨hg, ?_, ?_⟩
      · rw [hc _ (Set.mem_insert _ _), mul_inv_cancel_right]
      · rw [hc _ (Set.mem_insert_of_mem _ rfl), mul_inv_cancel_right]
    · rintro ⟨hg, h1, h2⟩
      refine ⟨hg, fun x hx => ?_⟩
      rcases hx with rfl | hx
      · calc (x₁ : G) * g = (x₁ * g * (x₁ : G)⁻¹) * x₁ := by group
          _ = g * x₁ := by rw [h1]
      · rw [Set.mem_singleton_iff] at hx
        subst hx
        calc (x₂ : G) * g = (x₂ * g * (x₂ : G)⁻¹) * x₂ := by group
          _ = g * x₂ := by rw [h2]
  have hhF : ∀ g ∈ F, h * g * h⁻¹ ∈ F := by
    intro g hg
    obtain ⟨hgU, h1, h2⟩ := (hmemF g).mp hg
    refine (hmemF _).mpr ⟨(Subgroup.mem_normalizer_iff.mp hhN g).mp hgU, ?_, ?_⟩
    · rw [← hcomm _ hx₁Y g hgU, h1]
    · rw [← hcomm _ hx₂Y g hgU, h2]
  have hhF' : ∀ g, h * g * h⁻¹ ∈ F → g ∈ F := by
    intro g hg
    obtain ⟨hgU, h1, h2⟩ := (hmemF _).mp hg
    have hgU' : g ∈ U := by
      have := (Subgroup.mem_normalizer_iff.mp (N.inv_mem hhN) _).mp hgU
      rwa [show h⁻¹ * (h * g * h⁻¹) * h⁻¹⁻¹ = g by group] at this
    refine (hmemF g).mpr ⟨hgU', ?_, ?_⟩
    · have h3 := hcomm _ hx₁Y g hgU'
      rw [h1] at h3
      have := congrArg (fun z => h⁻¹ * z * h) h3
      simpa [mul_assoc] using this
    · have h3 := hcomm _ hx₂Y g hgU'
      rw [h2] at h3
      have := congrArg (fun z => h⁻¹ * z * h) h3
      simpa [mul_assoc] using this
  have hhNF : h ∈ Subgroup.normalizer (F : Set G) :=
    Subgroup.mem_normalizer_iff.mpr fun g => ⟨hhF g, hhF' g⟩
  have hFA : F ⊓ (U ⊓ V) = Subgroup.zpowers (a : G) := by
    apply le_antisymm
    · rintro v ⟨hvF, hvA⟩
      obtain ⟨-, h1, h2⟩ := (hmemF v).mp hvF
      rcases hCA v hvA h1 h2 with rfl | rfl
      · exact Subgroup.one_mem _
      · exact Subgroup.mem_zpowers _
    · rw [Subgroup.zpowers_le]
      exact ⟨(hmemF _).mpr ⟨haA.1, hx₁a, hx₂a⟩, haA⟩
  have hBA : ∀ g ∈ B, h * g * h⁻¹ ∈ U ⊓ V := fun g hg =>
    ⟨(Subgroup.mem_normalizer_iff.mp hhN g).mp hg.1, BlueprintB2.mem_conjugate_iff.mp hg.2⟩
  have hxB : ∀ x ∈ Y, ∀ g ∈ B, x * g * x⁻¹ ∈ B := by
    intro x hx g hg
    refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp (hYU hx) g).mp hg.1,
      BlueprintB2.mem_conjugate_iff.mpr ?_⟩
    rw [hcomm x hx g hg.1]
    exact (Subgroup.mem_normalizer_iff.mp (hLV (hYLA hx).1) _).mp (hBA g hg).2
  set b : G := h⁻¹ * a * h with hbdef
  have hb2 : b * b = 1 := by
    rw [hbdef, show h⁻¹ * (a : G) * h * (h⁻¹ * a * h) = h⁻¹ * (a * a) * h by group]
    rw [show (a : G) * a = 1 from congrArg Subtype.val (hV2' a), mul_one, inv_mul_cancel]
  have hb1 : b ≠ 1 := fun h1 => by
    apply ha1
    calc (a : G) = h * b * h⁻¹ := by rw [hbdef]; group
      _ = 1 := by rw [h1, mul_one, mul_inv_cancel]
  have hhb : h * b * h⁻¹ = a := by rw [hbdef]; group
  have hbF : b ∈ F := hhF' b (by rw [hhb]; exact (hmemF _).mpr ⟨haA.1, hx₁a, hx₂a⟩)
  have hbB : b ∈ B := ⟨((hmemF b).mp hbF).1, BlueprintB2.mem_conjugate_iff.mpr (by
    rw [hhb]; exact a.2)⟩
  have hFB : F ⊓ B = Subgroup.zpowers b := by
    apply le_antisymm
    · rintro g ⟨hgF, hgB⟩
      have h1 : h * g * h⁻¹ ∈ F ⊓ (U ⊓ V) := ⟨hhF g hgF, hBA g hgB⟩
      rw [hFA] at h1
      have h2 : h * g * h⁻¹ = 1 ∨ h * g * h⁻¹ = a := by
        have ha2 : (a : G) ^ 2 = 1 := by rw [pow_two]; exact congrArg Subtype.val (hV2' a)
        have hord2 : orderOf (a : G) = 2 := orderOf_eq_prime ha2 ha1
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h1
        rw [← hk, ← zpow_mod_orderOf, hord2]
        have : k % (2 : ℕ) = 0 ∨ k % (2 : ℕ) = 1 := by omega
        rcases this with h0 | h0
        · left; rw [h0, zpow_zero]
        · right; rw [h0, zpow_one]
      rcases h2 with h2 | h2
      · have : g = 1 := by
          calc g = h⁻¹ * (h * g * h⁻¹) * h := by group
            _ = 1 := by rw [h2]; group
        rw [this]
        exact Subgroup.one_mem _
      · have : g = b := by
          calc g = h⁻¹ * (h * g * h⁻¹) * h := by group
            _ = b := by rw [h2]
        rw [this]
        exact Subgroup.mem_zpowers _
    · rw [Subgroup.zpowers_le]
      exact ⟨hbF, hbB⟩
  have hAB : (U ⊓ V) ⊓ B = ⊥ := hUi
  have hFAB : F = (F ⊓ (U ⊓ V)) ⊔ (F ⊓ B) := by
    apply le_antisymm
    · intro f hf
      obtain ⟨hfU, hf1, hf2⟩ := (hmemF f).mp hf
      have hBC : B ≤ Subgroup.centralizer ((U ⊓ V : Subgroup G) : Set G) := fun g hg =>
        Subgroup.mem_centralizer_iff.mpr fun c hc => hUab c hc.1 g hg.1
      have hf' : f ∈ (U ⊓ V) ⊔ B := hUd ▸ hfU
      obtain ⟨c, hc, d, hd, rfl⟩ := exists_mul_of_mem_sup_centralizer hBC hf'
      have hcomp : ∀ x ∈ Y, x * (c * d) * x⁻¹ = c * d → x * c * x⁻¹ = c := by
        intro x hx hxf
        have hxc : x * c * x⁻¹ ∈ U ⊓ V :=
          ⟨(Subgroup.mem_normalizer_iff.mp (hYU hx) c).mp hc.1,
            (Subgroup.mem_normalizer_iff.mp (hLV (hYLA hx).1) c).mp hc.2⟩
        have hxd : x * d * x⁻¹ ∈ B := hxB x hx d hd
        have h1 : c⁻¹ * (x * c * x⁻¹) = d * (x * d * x⁻¹)⁻¹ := by
          have : (x * c * x⁻¹) * (x * d * x⁻¹) = c * d := by
            rw [show (x * c * x⁻¹) * (x * d * x⁻¹) = x * (c * d) * x⁻¹ by group, hxf]
          calc c⁻¹ * (x * c * x⁻¹) = c⁻¹ * ((x * c * x⁻¹) * (x * d * x⁻¹)) *
              (x * d * x⁻¹)⁻¹ := by group
            _ = c⁻¹ * (c * d) * (x * d * x⁻¹)⁻¹ := by rw [this]
            _ = d * (x * d * x⁻¹)⁻¹ := by group
        have h2 : c⁻¹ * (x * c * x⁻¹) ∈ (U ⊓ V) ⊓ B :=
          ⟨(U ⊓ V).mul_mem ((U ⊓ V).inv_mem hc) hxc,
            h1 ▸ B.mul_mem hd (B.inv_mem hxd)⟩
        rw [hAB, Subgroup.mem_bot] at h2
        calc x * c * x⁻¹ = c * (c⁻¹ * (x * c * x⁻¹)) := by group
          _ = c := by rw [h2, mul_one]
      have hc1 := hcomp _ hx₁Y hf1
      have hc2' := hcomp _ hx₂Y hf2
      have hcF : c ∈ F := (hmemF c).mpr ⟨hc.1, hc1, hc2'⟩
      have hdF : d ∈ F := by
        have := F.mul_mem (F.inv_mem hcF) hf
        rwa [show c⁻¹ * (c * d) = d by group] at this
      exact Subgroup.mul_mem_sup ⟨hcF, hc⟩ ⟨hdF, hd⟩
    · exact sup_le inf_le_left inf_le_left
  have hcardF : Nat.card F = 4 := by
    have hBC' : F ⊓ B ≤ Subgroup.centralizer ((F ⊓ (U ⊓ V) : Subgroup G) : Set G) :=
      fun g hg => Subgroup.mem_centralizer_iff.mpr fun c hc => hUab c hc.2.1 g hg.2.1
    have hdisj : (F ⊓ (U ⊓ V)) ⊓ (F ⊓ B) = ⊥ :=
      eq_bot_iff.mpr fun g hg => by
        rw [← hAB]
        exact ⟨hg.1.2, hg.2.2⟩
    have h1 := card_sup_eq_mul hBC' hdisj
    rw [← hFAB, hFA, hFB, Nat.card_zpowers, Nat.card_zpowers] at h1
    have ha2 : (a : G) ^ 2 = 1 := by rw [pow_two]; exact congrArg Subtype.val (hV2' a)
    have hb2' : b ^ 2 = 1 := by rw [pow_two]; exact hb2
    rw [h1, orderOf_eq_prime ha2 ha1, orderOf_eq_prime hb2' hb1]
  have hp3 : p = 3 := by
    have hPN : Subgroup.zpowers h ≤ Subgroup.normalizer (F : Set G) :=
      Subgroup.zpowers_le.mpr hhNF
    let φ₀ : ↥(Subgroup.zpowers h) →* MulAut ↥F :=
      (Subgroup.normalizerMonoidHom F).comp (Subgroup.inclusion hPN)
    let _ : MulAction ↥(Subgroup.zpowers h) ↥F := MulAction.compHom ↥F φ₀
    have hsmul : ∀ (g : ↥(Subgroup.zpowers h)) (f : ↥F),
        ((g • f : ↥F) : G) = (g : G) * (f : G) * (g : G)⁻¹ := fun _ _ => rfl
    have : Fact p.Prime := ⟨hp⟩
    have hPp : IsPGroup p ↥(Subgroup.zpowers h) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord, pow_one])
    have hmod := hPp.card_modEq_card_fixedPoints ↥F
    have hfix : Nat.card (MulAction.fixedPoints ↥(Subgroup.zpowers h) ↥F) = 1 := by
      rw [Nat.card_eq_one_iff_exists]
      refine ⟨⟨1, fun g => Subtype.ext ?_⟩, fun y => Subtype.ext (Subtype.ext ?_)⟩
      · rw [hsmul]
        simp
      · have hyC : ((y : ↥F) : G) ∈ U ⊓ Subgroup.centralizer (P : Set G) := by
          refine ⟨((hmemF _).mp (y : ↥F).2).1, Subgroup.mem_centralizer_iff.mpr fun k hk => ?_⟩
          rw [hPh] at hk
          have h1 := congrArg Subtype.val (y.2 ⟨k, hk⟩)
          rw [hsmul] at h1
          calc k * ((y : ↥F) : G) = k * (y : ↥F) * k⁻¹ * k := by group
            _ = (y : ↥F) * k := by rw [h1]
        rw [hUP, Subgroup.mem_bot] at hyC
        exact hyC
    rw [hcardF, hfix] at hmod
    have hdvd : p ∣ 3 := (Nat.modEq_iff_dvd' (by norm_num)).mp hmod.symm
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp hdvd
  subst hp3
  have hker : IsPGroup 2 (actGL hLV e).ker := by
    rintro ⟨x, hx⟩
    have hxC : ((x : ↥L) : G) ∈ Subgroup.centralizer (V : Set G) :=
      (actGL_eq_one_iff hLV e x).mp hx
    have hxO := Lem24.centralizer_le_pCoreOf hH hredV (by norm_num) e htop ⟨x.2, hxC⟩
    obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L ⟨_, hxO⟩
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    have := congrArg Subtype.val hk
    simpa using this
  have hE : e9five ≤ (actGL hLV e).range := fun g _ => hψs g
  obtain ⟨S₉, hS₉L, hS₉c, hS₉e, hS₉E, hS₉inj⟩ :=
    exists_elemAbelian_lift (actGL hLV e) hker hE e9five_elem (k := 2)
      (by rw [card_e9five]; norm_num)
  have hS₉Y : S₉ ≤ Y := by
    intro s hs
    have hsA : s ∈ Subgroup.normalizer ((U ⊓ V : Subgroup G) : Set G) :=
      mem_normalizer_of_actGL hLV e 0 inf_le_right he' ⟨s, hS₉L hs⟩ fun y =>
        e9five_mulVec_zero (hS₉E ⟨s, hS₉L hs⟩ hs) y
    have hs3 : s ^ 3 = 1 := hS₉e.2 s hs
    have hso : Odd (orderOf s) := by
      have h1 : orderOf s ∣ 3 := orderOf_dvd_of_pow_eq_one hs3
      rcases (Nat.dvd_prime Nat.prime_three).mp h1 with h2 | h2 <;> rw [h2] <;> decide
    exact mem_oTwoUpper_of_odd ⟨hS₉L hs, hsA⟩ hso
  have hS₉N : S₉ ≤ N := hS₉Y.trans hYU
  have hPN : Subgroup.zpowers h ≤ N := Subgroup.zpowers_le.mpr hhN
  have hUN' : U ≤ N := Subgroup.le_normalizer
  let U' : Subgroup ↥N := U.subgroupOf N
  have : U'.Normal := Subgroup.normal_in_normalizer
  let π : ↥N →* ↥N ⧸ U' := QuotientGroup.mk' U'
  let f₁ : ↥S₉ →* ↥N ⧸ U' := π.comp (Subgroup.inclusion hS₉N)
  let f₂ : ↥(Subgroup.zpowers h) →* ↥N ⧸ U' := π.comp (Subgroup.inclusion hPN)
  have hπ : ∀ x y : ↥N, π x = π y ↔ ((x : G))⁻¹ * y ∈ U := fun x y => by
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    exact Subgroup.mem_subgroupOf
  have hπh : ∀ s : ↥S₉, Commute (f₁ s) (π ⟨h, hhN⟩) := by
    intro s
    show π (Subgroup.inclusion hS₉N s) * π ⟨h, hhN⟩ = π ⟨h, hhN⟩ * π (Subgroup.inclusion hS₉N s)
    rw [← map_mul, ← map_mul, hπ]
    have h1 := hhK _ (hS₉Y s.2)
    have h2 : ((Subgroup.inclusion hS₉N s * ⟨h, hhN⟩ : ↥N) : G)⁻¹ *
        ((⟨h, hhN⟩ * Subgroup.inclusion hS₉N s : ↥N) : G) =
        (s : G)⁻¹ * (h⁻¹ * (h * s * h⁻¹ * (s : G)⁻¹) * h) * s := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inclusion]
      group
    rw [h2]
    have h3 := (Subgroup.mem_normalizer_iff.mp (N.inv_mem hhN) _).mp h1
    rw [inv_inv] at h3
    have h4 := (Subgroup.mem_normalizer_iff.mp (N.inv_mem (hS₉N s.2)) _).mp h3
    rwa [inv_inv] at h4
  have hcomm₁₂ : ∀ (s : ↥S₉) (k : ↥(Subgroup.zpowers h)), Commute (f₁ s) (f₂ k) := by
    rintro s ⟨k, hk⟩
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hk
    have h1 : f₂ ⟨h ^ j, hk⟩ = (π ⟨h, hhN⟩) ^ j := by
      rw [← map_zpow]
      rfl
    rw [h1]
    exact (hπh s).zpow_right j
  set f := f₁.noncommCoprod f₂ hcomm₁₂ with hfdef
  have hfinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    rintro ⟨s, k⟩ h1
    rw [hfdef, MonoidHom.noncommCoprod_apply] at h1
    have h2 : π (Subgroup.inclusion hS₉N s * Subgroup.inclusion hPN k) = 1 := by
      rw [map_mul]
      exact h1
    rw [← map_one π, hπ] at h2
    simp only [OneMemClass.coe_one, mul_one, Subgroup.coe_mul, Subgroup.coe_inclusion] at h2
    replace h2 : (s : G) * k ∈ U := inv_mem_iff.mp h2
    have hkM : (k : G) ∈ M := by
      have hsM : (s : G) ∈ M := Subgroup.le_normalizer (hS₉L s.2)
      have huM : (s : G) * k ∈ M := hH.normalizes (hUT h2)
      have := M.mul_mem (M.inv_mem hsM) huM
      rwa [show (s : G)⁻¹ * (s * k) = k by group] at this
    have hk1 : k = 1 := by
      have : Fact (Nat.card ↥(Subgroup.zpowers h)).Prime :=
        ⟨by rw [Nat.card_zpowers, hord]; exact hp⟩
      rcases Subgroup.eq_bot_or_eq_top_of_prime_card (M.subgroupOf (Subgroup.zpowers h)) with
        h3 | h3
      · have : k ∈ M.subgroupOf (Subgroup.zpowers h) := Subgroup.mem_subgroupOf.mpr hkM
        rw [h3, Subgroup.mem_bot] at this
        exact this
      · exfalso
        apply hhM
        have : (⟨h, Subgroup.mem_zpowers h⟩ : ↥(Subgroup.zpowers h)) ∈
            M.subgroupOf (Subgroup.zpowers h) := by rw [h3]; exact Subgroup.mem_top _
        exact Subgroup.mem_subgroupOf.mp this
    subst hk1
    have hsU : (s : G) ∈ U := by simpa using h2
    have hs1 : s = 1 := by
      obtain ⟨j, hj⟩ := hU2 ⟨s, hsU⟩
      have hj' : (s : G) ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
      have hs3 : (s : G) ^ 3 = 1 := hS₉e.2 s s.2
      have hcop : Nat.gcd (2 ^ j) 3 = 1 := Nat.Coprime.pow_left j (by norm_num)
      have := pow_gcd_eq_one.mpr ⟨hj', hs3⟩
      rw [hcop, pow_one] at this
      exact Subtype.ext this
    rw [hs1]
    rfl
  have hcardA : Nat.card (↥S₉ × ↥(Subgroup.zpowers h)) = 3 ^ 3 := by
    rw [Nat.card_prod, hS₉c, Nat.card_zpowers, hord]
    norm_num
  have hle : 3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (↥N ⧸ U')) := by
    refine CFSG.SectionRank.le_pRank_of_injective (by norm_num) (fun x y => ?_) (fun x => ?_)
      hcardA f hfinj le_top
    · refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
      · exact congrArg Subtype.val (hS₉e.1.1.comm x.1 y.1)
      · obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp x.2.2
        obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp y.2.2
        show (x.2 : G) * y.2 = y.2 * x.2
        rw [← hi, ← hj]
        exact ((Commute.refl h).zpow_zpow i j).eq
    · refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
      · show (x.1 : G) ^ 3 = 1
        exact hS₉e.2 _ x.1.2
      · obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp x.2.2
        have hh3 : h ^ 3 = 1 := by rw [← hord]; exact pow_orderOf_eq_one h
        show (x.2 : G) ^ 3 = 1
        rw [← hi, ← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast,
          hh3, _root_.one_zpow]
  have hU'2 : IsPGroup 2 U' := by
    rintro ⟨x, hx⟩
    obtain ⟨k, hk⟩ := hU2 ⟨x, Subgroup.mem_subgroupOf.mp hx⟩
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    have := congrArg Subtype.val hk
    simpa using this
  rw [CFSG.SectionRank.pRank_quotient_two_group U' hU'2 Nat.prime_three (by norm_num)] at hle
  have hle2 := (CFSG.SectionRank.pRank_le_map (p := 3) (by norm_num) N.subtype
    N.subtype_injective ⊤)
  rw [← MonoidHom.range_eq_map, Subgroup.range_subtype] at hle2
  have hN2 : pCoreOf 2 N ≠ ⊥ := by
    intro h0
    have hUle : U ≤ pCoreOf 2 N :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hUN' le_rfl hU2
    rw [h0] at hUle
    have hUb : U = ⊥ := eq_bot_iff.mpr hUle
    rw [hUb, bot_inf_eq, Subgroup.relIndex_bot_left] at hidx
    rw [hVn] at hidx
    norm_num at hidx
  have h3 := pRank_le_two_of_pCoreOf_ne_bot hH.qtke hN2 Nat.prime_three (by norm_num)
  omega

end CFSG.Quasithin.H13
