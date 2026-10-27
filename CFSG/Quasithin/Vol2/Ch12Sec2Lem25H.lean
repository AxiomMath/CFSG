module

public import CFSG.Quasithin.Vol2.Ch12Sec2Lem25G

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique Matrix
open scoped IsMulCommutative

namespace Lem25

variable {G : Type} [Group G]

theorem dvd_card_sub_one_of_fpf [Finite G] {F : Subgroup G} {h : G} {p : ℕ} (hp : p.Prime)
    (hord : orderOf h = p) (hhF : h ∈ Subgroup.normalizer (F : Set G))
    (hfix : ∀ f ∈ F, h * f * h⁻¹ = f → f = 1) : p ∣ Nat.card F - 1 := by
  have hPN : Subgroup.zpowers h ≤ Subgroup.normalizer (F : Set G) :=
    Subgroup.zpowers_le.mpr hhF
  let φ₀ : ↥(Subgroup.zpowers h) →* MulAut ↥F :=
    (Subgroup.normalizerMonoidHom F).comp (Subgroup.inclusion hPN)
  let _ : MulAction ↥(Subgroup.zpowers h) ↥F := MulAction.compHom ↥F φ₀
  have hsmul : ∀ (g : ↥(Subgroup.zpowers h)) (f : ↥F),
      ((g • f : ↥F) : G) = (g : G) * (f : G) * (g : G)⁻¹ := fun _ _ => rfl
  have : Fact p.Prime := ⟨hp⟩
  have hPp : IsPGroup p ↥(Subgroup.zpowers h) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord, pow_one])
  have hmod := hPp.card_modEq_card_fixedPoints ↥F
  have hfix1 : Nat.card (MulAction.fixedPoints ↥(Subgroup.zpowers h) ↥F) = 1 := by
    rw [Nat.card_eq_one_iff_exists]
    refine ⟨⟨1, fun g => Subtype.ext ?_⟩, fun y => Subtype.ext (Subtype.ext ?_)⟩
    · rw [hsmul]
      simp
    · have h1 := congrArg Subtype.val (y.2 ⟨h, Subgroup.mem_zpowers h⟩)
      rw [hsmul] at h1
      exact hfix _ (y : ↥F).2 h1
  rw [hfix1] at hmod
  exact (Nat.modEq_iff_dvd' Nat.card_pos).mp hmod.symm

theorem comm_of_yNormal
    (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (h323 : Stmt3_2_3)
    (h1216 : Stmt12_2_16) (h1220 : Stmt12_2_20) (hY : Lem12225YNormal) [Finite G]
    {T L V H P U I : Subgroup G} {h : G} {n p : ℕ} (hH : Hyp1223 G T L V)
    (hNE : NoEscape12_2_13 L V) (hC : Config12_2_24 T L V H P U I h n p) (hn3 : n ≠ 3) :
    oTwoUpper (L ⊓ Subgroup.normalizer ((U ⊓ V : Subgroup G) : Set G)) ≤
        Subgroup.normalizer (U : Set G) ∧
      h ∈ Subgroup.normalizer
        ((oTwoUpper (L ⊓ Subgroup.normalizer ((U ⊓ V : Subgroup G) : Set G)) : Subgroup G) :
          Set G) ∧
      (∀ y ∈ oTwoUpper (L ⊓ Subgroup.normalizer ((U ⊓ V : Subgroup G) : Set G)),
        h * y * h⁻¹ * y⁻¹ ∈ U) ∧
      ∀ y ∈ oTwoUpper (L ⊓ Subgroup.normalizer ((U ⊓ V : Subgroup G) : Set G)), ∀ x ∈ U,
        h * (y * x * y⁻¹) * h⁻¹ = y * (h * x * h⁻¹) * y⁻¹ := by
  classical
  have hCTL := ctl_eq_bot_of_yNormal h331 h1222 h323 h1216 h1220 hY hH hNE hC hn3
  have hstar := lem12225Star_of h331 h1222 h323 h1216 h1220 G T L V H P U I h n p hH hNE hC
  have hYN := hY G T L V H P U I h n p hH hNE hC hn3
  obtain ⟨-, -, hc2, -, -, -, -, -, -, -, -, -, hYR⟩ := hstar
  obtain ⟨hHs, -, -, -, -, -, -, -, hP, -, hhH, -, hI, -, -, -, hUe, -, -,
    hidx, -, -, -, -, hHU, -, hIP, hHIT, -, -⟩ := hC
  set Y := oTwoUpper (L ⊓ Subgroup.normalizer ((U ⊓ V : Subgroup G) : Set G)) with hYdef
  set N := Subgroup.normalizer (U : Set G) with hNdef
  have hLV := le_normalizer_of_hyp1223 hH
  have hUab : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hUe.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hPh : P = Subgroup.zpowers h := hP
  have hhI : h ∈ I := by rw [hIP]; exact Subgroup.mem_sup_left (Subgroup.mem_sup_left (hPh ▸
    Subgroup.mem_zpowers h))
  have hIN : I ≤ N := (hHIT ▸ le_sup_left : I ≤ H).trans hHU
  have hhN : h ∈ N := hHU hhH
  have hVI : V ≤ I := by rw [hI]; exact le_sup_left
  have hVhI : CFSG.conjugate V h ≤ I := by rw [hI]; exact le_sup_right
  have hRU : T ⊓ Subgroup.centralizer (U : Set G) = U := by
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
  refine ⟨hYU, hhY, hhK, fun y hy x hx => ?_⟩
  have hc := hhK y hy
  have hz : y * (h * x * h⁻¹) * y⁻¹ ∈ U :=
    (Subgroup.mem_normalizer_iff.mp (hYU hy) _).mp ((Subgroup.mem_normalizer_iff.mp hhN x).mp hx)
  calc h * (y * x * y⁻¹) * h⁻¹ =
      (h * y * h⁻¹ * y⁻¹) * (y * (h * x * h⁻¹) * y⁻¹) * (h * y * h⁻¹ * y⁻¹)⁻¹ := by group
    _ = (y * (h * x * h⁻¹) * y⁻¹) * (h * y * h⁻¹ * y⁻¹) * (h * y * h⁻¹ * y⁻¹)⁻¹ := by
      rw [hUab _ hc _ hz]
    _ = y * (h * x * h⁻¹) * y⁻¹ := by group

theorem prime_eq_three_of_fix [Finite G] {U V : Subgroup G} {h a : G} {p : ℕ} {X : Set G}
    (hp : p.Prime) (hord : orderOf h = p) (hUab : ∀ x ∈ U, ∀ y ∈ U, x * y = y * x)
    (hUd : U = (U ⊓ V) ⊔ (U ⊓ CFSG.conjugate V h))
    (hUi : (U ⊓ V) ⊓ (U ⊓ CFSG.conjugate V h) = ⊥)
    (hhU : h ∈ Subgroup.normalizer (U : Set G)) (hUh : ∀ u ∈ U, h * u * h⁻¹ = u → u = 1)
    (hXU : ∀ x ∈ X, x ∈ Subgroup.normalizer (U : Set G))
    (hXV : ∀ x ∈ X, x ∈ Subgroup.normalizer (V : Set G))
    (hXA : ∀ x ∈ X, x ∈ Subgroup.normalizer ((U ⊓ V : Subgroup G) : Set G))
    (hcomm : ∀ x ∈ X, ∀ u ∈ U, h * (x * u * x⁻¹) * h⁻¹ = x * (h * u * h⁻¹) * x⁻¹)
    (haA : a ∈ U ⊓ V) (ha1 : a ≠ 1) (ha2 : a * a = 1) (haX : ∀ x ∈ X, x * a * x⁻¹ = a)
    (hCA : ∀ v ∈ U ⊓ V, (∀ x ∈ X, x * v * x⁻¹ = v) → v = 1 ∨ v = a) : p = 3 := by
  classical
  set B := U ⊓ CFSG.conjugate V h with hBdef
  set F := U ⊓ Subgroup.centralizer X with hFdef
  have hmemF : ∀ g, g ∈ F ↔ g ∈ U ∧ ∀ x ∈ X, x * g * x⁻¹ = g := by
    intro g
    rw [hFdef, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
    constructor
    · rintro ⟨hg, hc⟩
      exact ⟨hg, fun x hx => by rw [hc x hx, mul_inv_cancel_right]⟩
    · rintro ⟨hg, hc⟩
      exact ⟨hg, fun x hx => by
        calc x * g = (x * g * x⁻¹) * x := by group
          _ = g * x := by rw [hc x hx]⟩
  have hhF : ∀ g ∈ F, h * g * h⁻¹ ∈ F := by
    intro g hg
    obtain ⟨hgU, hgX⟩ := (hmemF g).mp hg
    refine (hmemF _).mpr ⟨(Subgroup.mem_normalizer_iff.mp hhU g).mp hgU, fun x hx => ?_⟩
    rw [← hcomm x hx g hgU, hgX x hx]
  have hhF' : ∀ g, h * g * h⁻¹ ∈ F → g ∈ F := by
    intro g hg
    obtain ⟨hgU, hgX⟩ := (hmemF _).mp hg
    have hgU' : g ∈ U := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hhU) _).mp hgU
      rwa [show h⁻¹ * (h * g * h⁻¹) * h⁻¹⁻¹ = g by group] at this
    refine (hmemF g).mpr ⟨hgU', fun x hx => ?_⟩
    have h3 := hcomm x hx g hgU'
    rw [hgX x hx] at h3
    have := congrArg (fun z => h⁻¹ * z * h) h3
    simpa [mul_assoc] using this
  have hhNF : h ∈ Subgroup.normalizer (F : Set G) :=
    Subgroup.mem_normalizer_iff.mpr fun g => ⟨hhF g, hhF' g⟩
  have hFA : F ⊓ (U ⊓ V) = Subgroup.zpowers a := by
    apply le_antisymm
    · rintro v ⟨hvF, hvA⟩
      rcases hCA v hvA ((hmemF v).mp hvF).2 with rfl | rfl
      · exact Subgroup.one_mem _
      · exact Subgroup.mem_zpowers _
    · rw [Subgroup.zpowers_le]
      exact ⟨(hmemF _).mpr ⟨haA.1, haX⟩, haA⟩
  have hBA : ∀ g ∈ B, h * g * h⁻¹ ∈ U ⊓ V := fun g hg =>
    ⟨(Subgroup.mem_normalizer_iff.mp hhU g).mp hg.1, BlueprintB2.mem_conjugate_iff.mp hg.2⟩
  have hxB : ∀ x ∈ X, ∀ g ∈ B, x * g * x⁻¹ ∈ B := by
    intro x hx g hg
    refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp (hXU x hx) g).mp hg.1,
      BlueprintB2.mem_conjugate_iff.mpr ?_⟩
    rw [hcomm x hx g hg.1]
    exact (Subgroup.mem_normalizer_iff.mp (hXV x hx) _).mp (hBA g hg).2
  set b : G := h⁻¹ * a * h with hbdef
  have hb2 : b * b = 1 := by
    rw [hbdef, show h⁻¹ * a * h * (h⁻¹ * a * h) = h⁻¹ * (a * a) * h by group, ha2, mul_one,
      inv_mul_cancel]
  have hb1 : b ≠ 1 := fun h1 => by
    apply ha1
    calc a = h * b * h⁻¹ := by rw [hbdef]; group
      _ = 1 := by rw [h1, mul_one, mul_inv_cancel]
  have hhb : h * b * h⁻¹ = a := by rw [hbdef]; group
  have hbF : b ∈ F := hhF' b (by rw [hhb]; exact (hmemF _).mpr ⟨haA.1, haX⟩)
  have hbB : b ∈ B := ⟨((hmemF b).mp hbF).1, BlueprintB2.mem_conjugate_iff.mpr (by
    rw [hhb]; exact haA.2)⟩
  have ha2' : a ^ 2 = 1 := by rw [pow_two]; exact ha2
  have hord2 : orderOf a = 2 := orderOf_eq_prime ha2' ha1
  have hFB : F ⊓ B = Subgroup.zpowers b := by
    apply le_antisymm
    · rintro g ⟨hgF, hgB⟩
      have h1 : h * g * h⁻¹ ∈ F ⊓ (U ⊓ V) := ⟨hhF g hgF, hBA g hgB⟩
      rw [hFA] at h1
      have h2 : h * g * h⁻¹ = 1 ∨ h * g * h⁻¹ = a := by
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
  have hFAB : F = (F ⊓ (U ⊓ V)) ⊔ (F ⊓ B) := by
    apply le_antisymm
    · intro f hf
      obtain ⟨hfU, hfX⟩ := (hmemF f).mp hf
      have hBC : B ≤ Subgroup.centralizer ((U ⊓ V : Subgroup G) : Set G) := fun g hg =>
        Subgroup.mem_centralizer_iff.mpr fun c hc => hUab c hc.1 g hg.1
      have hf' : f ∈ (U ⊓ V) ⊔ B := hUd ▸ hfU
      obtain ⟨c, hc, d, hd, rfl⟩ := exists_mul_of_mem_sup_centralizer hBC hf'
      have hcomp : ∀ x ∈ X, x * (c * d) * x⁻¹ = c * d → x * c * x⁻¹ = c := by
        intro x hx hxf
        have hxc : x * c * x⁻¹ ∈ U ⊓ V := (Subgroup.mem_normalizer_iff.mp (hXA x hx) c).mp hc
        have hxd : x * d * x⁻¹ ∈ B := hxB x hx d hd
        have h1 : c⁻¹ * (x * c * x⁻¹) = d * (x * d * x⁻¹)⁻¹ := by
          have : (x * c * x⁻¹) * (x * d * x⁻¹) = c * d := by
            rw [show (x * c * x⁻¹) * (x * d * x⁻¹) = x * (c * d) * x⁻¹ by group, hxf]
          calc c⁻¹ * (x * c * x⁻¹) = c⁻¹ * ((x * c * x⁻¹) * (x * d * x⁻¹)) *
              (x * d * x⁻¹)⁻¹ := by group
            _ = c⁻¹ * (c * d) * (x * d * x⁻¹)⁻¹ := by rw [this]
            _ = d * (x * d * x⁻¹)⁻¹ := by group
        have h2 : c⁻¹ * (x * c * x⁻¹) ∈ (U ⊓ V) ⊓ B :=
          ⟨(U ⊓ V).mul_mem ((U ⊓ V).inv_mem hc) hxc, h1 ▸ B.mul_mem hd (B.inv_mem hxd)⟩
        rw [hUi, Subgroup.mem_bot] at h2
        calc x * c * x⁻¹ = c * (c⁻¹ * (x * c * x⁻¹)) := by group
          _ = c := by rw [h2, mul_one]
      have hcF : c ∈ F := (hmemF c).mpr ⟨hc.1, fun x hx => hcomp x hx (hfX x hx)⟩
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
        rw [← hUi]
        exact ⟨hg.1.2, hg.2.2⟩
    have h1 := card_sup_eq_mul hBC' hdisj
    rw [← hFAB, hFA, hFB, Nat.card_zpowers, Nat.card_zpowers] at h1
    have hb2' : b ^ 2 = 1 := by rw [pow_two]; exact hb2
    rw [h1, hord2, orderOf_eq_prime hb2' hb1]
  have hdvd := dvd_card_sub_one_of_fpf hp hord hhNF fun f hf hfix =>
    hUh f ((hmemF f).mp hf).1 hfix
  rw [hcardF] at hdvd
  exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp hdvd

@[expose] def M12f : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![1, 0, 0, 0; 0, 0, 1, 0; 0, 1, 1, 0; 0, 0, 0, 1]

@[expose] def m12f : GL (Fin 4) (ZMod 2) :=
  ⟨M12f, M12f ^ 2, by unfold M12f; decide +kernel, by unfold M12f; decide +kernel⟩

theorem coe_m12f : (m12f : Matrix (Fin 4) (Fin 4) (ZMod 2)) = M12f := rfl

theorem m12f_cube : m12f ^ 3 = 1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, coe_m12f, Units.val_one]
  unfold M12f
  decide +kernel

theorem m12f_ne_one : m12f ≠ 1 := fun h => by
  have := congrArg (fun g : GL (Fin 4) (ZMod 2) => (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) 1 1) h
  simp only [coe_m12f, Units.val_one] at this
  revert this
  unfold M12f
  decide

theorem M12f_mulVec_zero (x : Fin 4 → ZMod 2) : (M12f *ᵥ x) 0 = x 0 := by
  simp [M12f, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

theorem M12f_fix : ∀ x : Fin 4 → ZMod 2, x 0 = 0 → M12f *ᵥ x = x →
    x = 0 ∨ x = Pi.single 3 1 := by
  unfold M12f
  decide +kernel

theorem single3_zero : (Pi.single 3 1 : Fin 4 → ZMod 2) 0 = 0 := by decide

theorem single3_ne_zero : (Pi.single 3 1 : Fin 4 → ZMod 2) ≠ 0 := by decide

theorem M12f_single3 : M12f *ᵥ (Pi.single 3 1 : Fin 4 → ZMod 2) = Pi.single 3 1 := by
  unfold M12f
  decide +kernel

theorem prime_eq_three_of_yNormal
    (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (h323 : Stmt3_2_3)
    (h1216 : Stmt12_2_16) (h1220 : Stmt12_2_20) (hY : Lem12225YNormal) [Finite G]
    {T L V H P U I : Subgroup G} {h : G} {n p : ℕ} (hH : Hyp1223 G T L V)
    (hNE : NoEscape12_2_13 L V) (hC : Config12_2_24 T L V H P U I h n p) (hn3 : n ≠ 3) :
    p = 3 := by
  classical
  obtain ⟨hYU, -, -, hcomm⟩ := comm_of_yNormal h331 h1222 h323 h1216 h1220 hY hH hNE hC hn3
  obtain ⟨-, -, hn, hVn, -, -, hp, -, hP, hord, hhH, -, -, -, hUd, hUi, hUe, -, hUP,
    hidx, ⟨hcommV, -⟩, -, -, -, hHU, -, -, -, -, -⟩ := hC
  set Y := oTwoUpper (L ⊓ Subgroup.normalizer ((U ⊓ V : Subgroup G) : Set G)) with hYdef
  have hLV := le_normalizer_of_hyp1223 hH
  have hVe : IsElemAbelian 2 V := S125.isElemAbelian_of_hyp1223 hH
  have hUab : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hUe.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have : IsMulCommutative ↥V := hcommV
  have hV2' : ∀ v : ↥V, v * v = 1 := fun v => by
    rw [← pow_two]
    exact Subtype.ext (hVe.2 v v.2)
  obtain ⟨-, -, -, htop, -, -⟩ := h1220 G T L V hH hNE
  have hhU : h ∈ Subgroup.normalizer (U : Set G) := hHU hhH
  have hPh : P = Subgroup.zpowers h := hP
  have hUh : ∀ u ∈ U, h * u * h⁻¹ = u → u = 1 := by
    intro u hu hfix
    have huP : u ∈ U ⊓ Subgroup.centralizer (P : Set G) := by
      refine ⟨hu, Subgroup.mem_centralizer_iff.mpr fun k hk => ?_⟩
      rw [hPh] at hk
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hk
      have hc : Commute h u := by
        calc h * u = h * u * h⁻¹ * h := by group
          _ = u * h := by rw [hfix]
      exact (hc.zpow_left j).eq
    rw [hUP, Subgroup.mem_bot] at huP
    exact huP
  have hYLA : Y ≤ L ⊓ Subgroup.normalizer ((U ⊓ V : Subgroup G) : Set G) := oTwoUpper_le _
  have hodd3 : ∀ {m : ℕ} (g : GL (Fin m) (ZMod 2)), g ^ 3 = 1 → g ≠ 1 → Odd (orderOf g) :=
    fun g hg hg1 => by rw [orderOf_eq_three hg hg1]; decide
  have hcoord : ∀ {m : ℕ} (e : ↥V ≃* Multiplicative (Fin (m + 1) → ZMod 2)),
      (∀ w : ↥V, (w : G) ∈ U ⊓ V ↔ Multiplicative.toAdd (e w) 0 = 0) →
      ∀ (x : ↥L) (M0 : Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod 2)),
        ((actGL hLV e x : GL (Fin (m + 1)) (ZMod 2)) : Matrix _ _ _) = M0 →
        ∀ w : ↥V, ((x : G) * w * (x : G)⁻¹ = w ↔
          M0 *ᵥ Multiplicative.toAdd (e w) = Multiplicative.toAdd (e w)) := by
    intro m e _ x M0 hxM w
    have h1 := actGL_mulVec hLV e x w
    rw [hxM] at h1
    rw [h1]
    constructor
    · intro hxw
      congr 2
      exact Subtype.ext (by rw [A4.actionOn_apply_coe]; exact hxw)
    · intro hxw
      have h2 := e.injective (Multiplicative.toAdd.injective hxw)
      have h3 := congrArg Subtype.val h2
      rwa [A4.actionOn_apply_coe] at h3
  rcases hn with h3 | h4 | h5
  · exact absurd h3 hn3
  ·
    subst h4
    have hcard4 : Nat.card ↥V = 2 ^ (3 + 1) := hVn
    obtain ⟨e, he⟩ := exists_coords_index_two hV2' hcard4 (A := (U ⊓ V).subgroupOf V) hidx
    have he' : ∀ w : ↥V, (w : G) ∈ U ⊓ V ↔ Multiplicative.toAdd (e w) 0 = 0 := fun w => by
      rw [← he, Subgroup.mem_subgroupOf]
    obtain ⟨x₁, hx₁o, hx₁⟩ := exists_odd_lift (actGL hLV e) (actGL_surjective hLV e htop)
      (hodd3 _ m12f_cube m12f_ne_one)
    have hx₁A : (x₁ : G) ∈ Subgroup.normalizer ((U ⊓ V : Subgroup G) : Set G) :=
      mem_normalizer_of_actGL hLV e 0 inf_le_right he' x₁ fun y => by
        rw [hx₁, coe_m12f]; exact M12f_mulVec_zero y
    have hx₁Y : (x₁ : G) ∈ Y := mem_oTwoUpper_of_odd ⟨x₁.2, hx₁A⟩ hx₁o
    have hcx := hcoord e he' x₁ M12f (by rw [hx₁, coe_m12f])
    set a : ↥V := e.symm (Multiplicative.ofAdd (Pi.single 3 1)) with hadef
    have hea : Multiplicative.toAdd (e a) = Pi.single 3 1 := by
      rw [hadef, MulEquiv.apply_symm_apply, toAdd_ofAdd]
    refine prime_eq_three_of_fix (X := {(x₁ : G)}) (a := (a : G)) hp hord hUab hUd hUi hhU hUh
      (fun x hx => by rw [Set.mem_singleton_iff] at hx; subst hx; exact hYU hx₁Y)
      (fun x hx => by rw [Set.mem_singleton_iff] at hx; subst hx; exact hLV x₁.2)
      (fun x hx => by rw [Set.mem_singleton_iff] at hx; subst hx; exact hx₁A)
      (fun x hx => by rw [Set.mem_singleton_iff] at hx; subst hx; exact hcomm _ hx₁Y)
      (by rw [he', hea]; exact single3_zero) (fun h1 => ?_)
      (congrArg Subtype.val (hV2' a))
      (fun x hx => by
        rw [Set.mem_singleton_iff] at hx; subst hx
        exact (hcx a).mpr (by rw [hea]; exact M12f_single3)) ?_
    · have h2 : a = 1 := Subtype.ext h1
      have h3 := hea
      rw [h2, map_one, toAdd_one] at h3
      exact single3_ne_zero h3.symm
    · intro v hv hvX
      set w : ↥V := ⟨v, hv.2⟩ with hw
      have hw0 : Multiplicative.toAdd (e w) 0 = 0 := (he' w).mp hv
      rcases M12f_fix _ hw0 ((hcx w).mp (hvX _ rfl)) with h3 | h3
      · left
        have h4 : e w = 1 := Multiplicative.toAdd.injective (by rw [h3, toAdd_one])
        have h5 : w = 1 := by rw [← map_one e] at h4; exact e.injective h4
        exact congrArg Subtype.val h5
      · right
        have h4 : e w = e a := Multiplicative.toAdd.injective (by rw [h3, hea])
        exact congrArg Subtype.val (e.injective h4)
  ·
    subst h5
    have hcard5 : Nat.card ↥V = 2 ^ (4 + 1) := hVn
    obtain ⟨e, he⟩ := exists_coords_index_two hV2' hcard5 (A := (U ⊓ V).subgroupOf V) hidx
    have he' : ∀ w : ↥V, (w : G) ∈ U ⊓ V ↔ Multiplicative.toAdd (e w) 0 = 0 := fun w => by
      rw [← he, Subgroup.mem_subgroupOf]
    obtain ⟨x₁, hx₁o, hx₁⟩ := exists_odd_lift (actGL hLV e) (actGL_surjective hLV e htop)
      (hodd3 _ m12_cube m12_ne_one)
    obtain ⟨x₂, hx₂o, hx₂⟩ := exists_odd_lift (actGL hLV e) (actGL_surjective hLV e htop)
      (hodd3 _ m23_cube m23_ne_one)
    have hx₁A : (x₁ : G) ∈ Subgroup.normalizer ((U ⊓ V : Subgroup G) : Set G) :=
      mem_normalizer_of_actGL hLV e 0 inf_le_right he' x₁ fun y => by
        rw [hx₁, coe_m12]; exact M12_mulVec_zero y
    have hx₂A : (x₂ : G) ∈ Subgroup.normalizer ((U ⊓ V : Subgroup G) : Set G) :=
      mem_normalizer_of_actGL hLV e 0 inf_le_right he' x₂ fun y => by
        rw [hx₂, coe_m23]; exact M23_mulVec_zero y
    have hx₁Y : (x₁ : G) ∈ Y := mem_oTwoUpper_of_odd ⟨x₁.2, hx₁A⟩ hx₁o
    have hx₂Y : (x₂ : G) ∈ Y := mem_oTwoUpper_of_odd ⟨x₂.2, hx₂A⟩ hx₂o
    have hcx₁ := hcoord e he' x₁ M12 (by rw [hx₁, coe_m12])
    have hcx₂ := hcoord e he' x₂ M23 (by rw [hx₂, coe_m23])
    set a : ↥V := e.symm (Multiplicative.ofAdd (Pi.single 4 1)) with hadef
    have hea : Multiplicative.toAdd (e a) = Pi.single 4 1 := by
      rw [hadef, MulEquiv.apply_symm_apply, toAdd_ofAdd]
    have hXY : ∀ x ∈ ({(x₁ : G), (x₂ : G)} : Set G), x ∈ Y := by
      rintro x (rfl | hx)
      · exact hx₁Y
      · rw [Set.mem_singleton_iff] at hx; subst hx; exact hx₂Y
    refine prime_eq_three_of_fix (X := {(x₁ : G), (x₂ : G)}) (a := (a : G)) hp hord hUab hUd hUi
      hhU hUh (fun x hx => hYU (hXY x hx)) (fun x hx => hLV (hYLA (hXY x hx)).1)
      (fun x hx => (hYLA (hXY x hx)).2) (fun x hx => hcomm _ (hXY x hx))
      (by rw [he', hea]; exact single4_zero) (fun h1 => ?_)
      (congrArg Subtype.val (hV2' a)) ?_ ?_
    · have h2 : a = 1 := Subtype.ext h1
      have h3 := hea
      rw [h2, map_one, toAdd_one] at h3
      exact single4_ne_zero h3.symm
    · rintro x (rfl | hx)
      · exact (hcx₁ a).mpr (by rw [hea]; exact M12_single4)
      · rw [Set.mem_singleton_iff] at hx; subst hx
        exact (hcx₂ a).mpr (by rw [hea]; exact M23_single4)
    · intro v hv hvX
      set w : ↥V := ⟨v, hv.2⟩ with hw
      have hw0 : Multiplicative.toAdd (e w) 0 = 0 := (he' w).mp hv
      rcases m12_m23_fix _ hw0 ((hcx₁ w).mp (hvX _ (Set.mem_insert _ _)))
        ((hcx₂ w).mp (hvX _ (Set.mem_insert_of_mem _ rfl))) with h3 | h3
      · left
        have h4 : e w = 1 := Multiplicative.toAdd.injective (by rw [h3, toAdd_one])
        have h5 : w = 1 := by rw [← map_one e] at h4; exact e.injective h4
        exact congrArg Subtype.val h5
      · right
        have h4 : e w = e a := Multiplicative.toAdd.injective (by rw [h3, hea])
        exact congrArg Subtype.val (e.injective h4)

end Lem25

end CFSG.Quasithin.H13
