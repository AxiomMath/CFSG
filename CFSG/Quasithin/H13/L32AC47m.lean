module

public import CFSG.Quasithin.H13.L32AC40c
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7

attribute [local instance] commGroupOfFact

variable {G : Type} [Group G] [Finite G] {T L V H K : Subgroup G}

theorem mem_normalizer_sup_of {A B : Subgroup G} (hBA : B ≤ Subgroup.normalizer (A : Set G))
    {g : G} (hA : ∀ a ∈ A, g * a * g⁻¹ ∈ A ⊔ B) (hB : ∀ b ∈ B, g * b * g⁻¹ ∈ A ⊔ B) :
    g ∈ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  refine Subgroup.mem_normalizer_fintype fun x hx => ?_
  obtain ⟨a, ha, b, hb, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hBA).mp hx
  have e : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
  rw [e]
  exact mul_mem (hA a ha) (hB b hb)

theorem H_le_N_l1_of_comm (S : Setting147 G T L V H) (h1332 : Stmt13_3_2)
    (hHeq : H = K ⊔ (l1 T L V ⊔ T))
    (hcomm : ∀ x ∈ l1 T L V, ∀ k ∈ K, x * k * x⁻¹ * k⁻¹ ∈ pCoreOf 2 H) :
    H ≤ Subgroup.normalizer (l1 T L V : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKH : K ≤ H := by rw [hHeq]; exact le_sup_left
  have hQT : pCoreOf 2 H ≤ T := pCoreOf_le_of_le S.hyp (Setting147.TH' S)
  have hQL : pCoreOf 2 H ≤ Subgroup.normalizer (l1 T L V : Set G) :=
    hQT.trans (Setting147.T_le_N_l1 S h1332)
  have hQn : ∀ g ∈ H, ∀ q ∈ pCoreOf 2 H, g * q * g⁻¹ ∈ l1 T L V ⊔ pCoreOf 2 H :=
    fun g hg q hq => Subgroup.mem_sup_right
      ((Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 H hg) q).mp hq)
  have hl1N : l1 T L V ⊔ T ≤ Subgroup.normalizer (l1 T L V : Set G) :=
    sup_le Subgroup.le_normalizer (Setting147.T_le_N_l1 S h1332)
  have hLQ : H ≤ Subgroup.normalizer ((l1 T L V ⊔ pCoreOf 2 H : Subgroup G) : Set G) := by
    calc H = K ⊔ (l1 T L V ⊔ T) := hHeq
      _ ≤ _ := by
        refine sup_le (fun k hk => ?_) (fun g hg => ?_)
        · refine mem_normalizer_sup_of hQL (fun l hl => ?_) (hQn k (hKH hk))
          have h1 := hcomm l⁻¹ ((l1 T L V).inv_mem hl) k hk
          have e : k * l * k⁻¹ = l * (l⁻¹ * k * l⁻¹⁻¹ * k⁻¹) := by group
          rw [e]
          exact mul_mem (Subgroup.mem_sup_left hl) (Subgroup.mem_sup_right h1)
        · refine mem_normalizer_sup_of hQL (fun l hl => Subgroup.mem_sup_left
            ((Subgroup.mem_normalizer_iff.mp (hl1N hg) l).mp hl)) (hQn g ?_)
          exact (sup_le (Setting147.l1H' S) (Setting147.TH' S)) hg
  have hO : oTwoUpper (l1 T L V ⊔ pCoreOf 2 H) = l1 T L V :=
    le_antisymm (oTwoUpper_sup_le_two' (pCoreOf_isPGroup 2 H) hQL)
      (calc l1 T L V = oTwoUpper (l1 T L V) := (oTwoUpper_oTwoUpper _).symm
        _ ≤ _ := oTwoUpper_mono le_sup_left)
  rw [← hO]
  exact hLQ.trans (normalizer_le_normalizer_oTwoUpper _)

theorem relIndex_l1_eq_three (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4)
    (S : Setting147 G T L V H) (hHL : H ≤ Subgroup.normalizer (l1 T L V : Set G)) :
    (pCoreOf 2 H).relIndex (l1 T L V) = 3 := by
  rw [← card_modO2Image' (Setting147.l1H' S)]
  exact Setting147.card_l1_star S h1222 h1332 h1334 hHL

theorem cube_mem_V (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4) (S : Setting147 G T L V H)
    {x : G} (hxl : x ∈ l1 T L V) (hx3 : x ^ 3 = 1)
    (hfpf : ∀ v ∈ V, x * v * x⁻¹ * v⁻¹ ∈ fsuV1 T V → v ∈ fsuV1 T V) {v : G} (hv : v ∈ V) :
    v * (x * v * x⁻¹) * (x * (x * v * x⁻¹) * x⁻¹) ∈ fsuV1 T V := by
  have hMod := stmtL32NModule_of_inputs h1332 h1334
  obtain ⟨⟨hVc, -⟩, -, hLTV, -⟩ := hMod G T L V S.hyp.hyp S.hyp.fsu
  have hxV : x ∈ Subgroup.normalizer (V : Set G) :=
    le_sup_left.trans hLTV ((oTwoUpper_le _).trans inf_le_left hxl)
  have hconj : ∀ w ∈ V, x * w * x⁻¹ ∈ V := fun w hw =>
    (Subgroup.mem_normalizer_iff.mp hxV w).mp hw
  set w := v * (x * v * x⁻¹) * (x * (x * v * x⁻¹) * x⁻¹) with hw
  have h1 := hconj v hv
  have h2 := hconj _ h1
  have hwV : w ∈ V := V.mul_mem (V.mul_mem hv h1) h2
  have hxxx : x * x * x = 1 := by rw [← pow_three', hx3]
  have h3 : x * (x * (x * v * x⁻¹) * x⁻¹) * x⁻¹ = v := by
    calc x * (x * (x * v * x⁻¹) * x⁻¹) * x⁻¹ = (x * x * x) * v * (x * x * x)⁻¹ := by group
      _ = v := by rw [hxxx]; group
  have hcomm : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hVc.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hxw : x * w * x⁻¹ = w := by
    have e : x * w * x⁻¹ = (x * v * x⁻¹) * (x * (x * v * x⁻¹) * x⁻¹) *
        (x * (x * (x * v * x⁻¹) * x⁻¹) * x⁻¹) := by rw [hw]; group
    rw [e, h3, hcomm _ (V.mul_mem h1 h2) v hv, ← mul_assoc]
  exact hfpf w hwV (by rw [hxw, mul_inv_cancel]; exact (fsuV1 T V).one_mem)

theorem cube_mem (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4)
    (S : Setting147 G T L V H) (hF : HypF918 T V L (fsuV1 T V) V H K)
    (hHL : H ≤ Subgroup.normalizer (l1 T L V : Set G)) {x : G} (hxl : x ∈ l1 T L V)
    (hx3 : x ^ 3 = 1) (hfpf : ∀ v ∈ V, x * v * x⁻¹ * v⁻¹ ∈ fsuV1 T V → v ∈ fsuV1 T V) :
    ∀ u ∈ conjClosure V H, u * (x * u * x⁻¹) * (x * (x * u * x⁻¹) * x⁻¹) ∈ fsuV1 T V := by
  have := factElem hF (le_conjClosure V H)
  have hUN : conjClosure V H ≤ Subgroup.normalizer (fsuV1 T V : Set G) :=
    hF.conjClosure_le_normalizer_V₁ (le_conjClosure V H)
  have hL1H : l1 T L V ≤ H := Setting147.l1H' S
  have hHU := le_normalizer_conjClosure V H
  have hV₁V : fsuV1 T V ≤ V := inf_le_left
  set Φ := phiU hF with hΦ
  have hker := phiU_eq_one_iff hF
  set xH : ↥H := ⟨x, hL1H hxl⟩ with hxH
  set y := Φ xH with hy
  have hy3 : y ^ 3 = 1 := by
    have h1 : xH ^ 3 = 1 := Subtype.ext (by simpa [hxH] using hx3)
    rw [hy, ← map_pow, h1, map_one]
  have hyu : ∀ u (hu : u ∈ conjClosure V H), y (modMk hUN u hu) =
      modMk hUN (x * u * x⁻¹) ((Subgroup.mem_normalizer_iff.mp (hHU (hL1H hxl)) u).mp hu) :=
    fun u hu => actH_modMk hF.H_le_normalizer_V₁ hUN hHU xH hu
  have key : ∀ u (hu : u ∈ conjClosure V H), ∃ hθ, modMk hUN u hu * y (modMk hUN u hu) *
      y (y (modMk hUN u hu)) =
        modMk hUN (u * (x * u * x⁻¹) * (x * (x * u * x⁻¹) * x⁻¹)) hθ := by
    intro u hu
    have h1 := (Subgroup.mem_normalizer_iff.mp (hHU (hL1H hxl)) u).mp hu
    have h2 := (Subgroup.mem_normalizer_iff.mp (hHU (hL1H hxl)) _).mp h1
    refine ⟨(conjClosure V H).mul_mem ((conjClosure V H).mul_mem hu h1) h2, ?_⟩
    rw [hyu u hu, hyu _ h1]
    apply Subtype.ext
    show secMk _ _ ⟨u, _⟩ * secMk _ _ ⟨x * u * x⁻¹, _⟩ * secMk _ _ ⟨x * (x * u * x⁻¹) * x⁻¹, _⟩ =
      secMk _ _ ⟨u * (x * u * x⁻¹) * (x * (x * u * x⁻¹) * x⁻¹), _⟩
    rw [← map_mul, ← map_mul]
    rfl
  have hMod := stmtL32NModule_of_inputs h1332 h1334
  obtain ⟨-, hV8, -, hV12, -⟩ := hMod G T L V S.hyp.hyp S.hyp.fsu
  have hy1 : y ≠ 1 := by
    intro hy1
    have hne : fsuV1 T V ≠ V := by
      intro h
      rw [h, hV8] at hV12
      omega
    obtain ⟨v, hv, hvn⟩ := IsConcreteLE.exists_of_lt (lt_of_le_of_ne hV₁V hne)
    apply hvn
    have hvU := le_conjClosure V H hv
    have h1 := hyu v hvU
    rw [hy1, MulAut.one_apply] at h1
    have h2 := (secMk_eq_secMk_iff (A := Subgroup.normalizer (fsuV1 T V : Set G))
      (B := fsuV1 T V)).mp (congrArg Subtype.val h1)
    have h3 : v⁻¹ * (x * v * x⁻¹) ∈ fsuV1 T V := h2
    have hvN : v ∈ Subgroup.normalizer (fsuV1 T V : Set G) := hUN hvU
    have h4 := (Subgroup.mem_normalizer_iff.mp hvN _).mp h3
    refine hfpf v hv ?_
    have e : x * v * x⁻¹ * v⁻¹ = v * (v⁻¹ * (x * v * x⁻¹)) * v⁻¹ := by group
    rw [e]
    exact h4
  have hord : orderOf y = 3 := orderOf_eq_prime hy3 hy1
  have hzp : Subgroup.zpowers y = ((l1 T L V).subgroupOf H).map Φ := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rw [Subgroup.zpowers_le]
      exact ⟨xH, Subgroup.mem_subgroupOf.mpr hxl, rfl⟩
    · rw [Nat.card_zpowers, hord, card_map_eq_relIndex Φ hker hL1H,
        relIndex_l1_eq_three h1222 h1332 h1334 S hHL]
  let N : Subgroup ↥(tildeOf (fsuV1 T V) (conjClosure V H)) :=
    { carrier := {w | w * y w * y (y w) = 1}
      one_mem' := by
        show (1 : ↥(tildeOf (fsuV1 T V) (conjClosure V H))) * y 1 * y (y 1) = 1
        simp only [map_one, mul_one]
      mul_mem' := fun {a b} ha hb => by
        have ha' : a * y a * y (y a) = 1 := ha
        have hb' : b * y b * y (y b) = 1 := hb
        show a * b * y (a * b) * y (y (a * b)) = 1
        rw [map_mul, map_mul, mul_mul_mul_comm a b, mul_mul_mul_comm (a * y a), ha', hb',
          mul_one]
      inv_mem' := fun {a} ha => by
        have ha' : a * y a * y (y a) = 1 := ha
        show a⁻¹ * y a⁻¹ * y (y a⁻¹) = 1
        rw [map_inv, map_inv, ← mul_inv, ← mul_inv, ha', inv_one] }
  have hmemN : ∀ w, w ∈ N ↔ w * y w * y (y w) = 1 := fun w => Iff.rfl
  have hyyy : ∀ w, y (y (y w)) = w := fun w => by
    rw [← MulAut.mul_apply, ← MulAut.mul_apply, ← pow_three', hy3, MulAut.one_apply]
  have hinv : ∀ h : ↥H, ∀ w ∈ N, Φ h w ∈ N := by
    intro h w hw
    have hw' : w * y w * y (y w) = 1 := hw
    have hz : (Φ h)⁻¹ * y * Φ h ∈ Subgroup.zpowers y := by
      rw [hzp]
      refine ⟨h⁻¹ * xH * h, Subgroup.mem_subgroupOf.mpr ?_, by rw [map_mul, map_mul, map_inv]⟩
      have h1 := (Subgroup.mem_normalizer_iff.mp (hHL (H.inv_mem h.2)) x).mp hxl
      simpa [hxH] using h1
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hz
    have hyg : ∀ v, y (Φ h v) = Φ h (((Φ h)⁻¹ * y * Φ h) v) := fun v => by
      rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.apply_inv_self]
    rw [hmemN, hyg, hyg, ← hk, ← map_mul, ← map_mul]
    have hk3 : y ^ k = y ^ (k % 3) := by
      rw [← zpow_mod_orderOf, hord]
      rfl
    have hcases : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
    rcases hcases with h0 | h0 | h0
    ·
      exfalso
      rw [h0, zpow_zero] at hk3
      have : y = 1 := by
        have h1 : (Φ h)⁻¹ * y * Φ h = 1 := by rw [← hk, hk3]
        have h2 : y = Φ h * ((Φ h)⁻¹ * y * Φ h) * (Φ h)⁻¹ := by group
        rw [h2, h1, mul_one, mul_inv_cancel]
      exact hy1 this
    · rw [hk3, h0, zpow_one, hw', map_one]
    · rw [hk3, h0]
      have e2 : y ^ (2 : ℤ) = y * y := by rw [zpow_two]
      rw [e2]
      simp only [MulAut.mul_apply]
      rw [hyyy]
      have e3 : w * y (y w) * y w = w * y w * y (y w) := by
        rw [mul_assoc, mul_comm (y (y w)), ← mul_assoc]
      rw [e3, hw', map_one]
  have hVN : subM (fsuV1 T V) (conjClosure V H) V ≤ N := by
    intro w hw
    obtain ⟨a, haV, haw⟩ := mem_secImg.mp (show ((w : ↥(tildeOf (fsuV1 T V) (conjClosure V H))) :
      SecQuot (Subgroup.normalizer (fsuV1 T V : Set G)) (fsuV1 T V)) ∈ tildeOf (fsuV1 T V) V
      from hw)
    have haU : (a : G) ∈ conjClosure V H := le_conjClosure V H haV
    have hwa : w = modMk hUN (a : G) haU := Subtype.ext haw.symm
    rw [hmemN, hwa]
    obtain ⟨hθ, he⟩ := key (a : G) haU
    rw [he]
    apply Subtype.ext
    exact (secMk_eq_one_iff (A := Subgroup.normalizer (fsuV1 T V : Set G))
      (B := fsuV1 T V) (x := ⟨_, hUN hθ⟩)).mpr (cube_mem_V h1332 h1334 S hxl hx3 hfpf haV)
  have htop := iSup_actH_subM_eq_top hF.H_le_normalizer_V₁ hUN hHU hV₁V
  have hNtop : (⊤ : Subgroup ↥(tildeOf (fsuV1 T V) (conjClosure V H))) ≤ N := by
    rw [← htop]
    refine iSup₂_le fun m hm => ?_
    obtain ⟨h, -, rfl⟩ := hm
    rintro _ ⟨w, hw, rfl⟩
    exact hinv h w (hVN hw)
  intro u hu
  obtain ⟨hθ, he⟩ := key u hu
  have h1 : modMk hUN u hu ∈ N := hNtop trivial
  rw [hmemN, he] at h1
  exact (secMk_eq_one_iff (A := Subgroup.normalizer (fsuV1 T V : Set G))
    (B := fsuV1 T V) (x := ⟨_, hUN hθ⟩)).mp (congrArg Subtype.val h1)

end CFSG.Quasithin.H13.L32A.C
