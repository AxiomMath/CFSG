module

public import CFSG.Quasithin.H13.AS91Sec4Two
public import CFSG.GF2Type.Smith1979.CharTwoLift
public import CFSG.LargeExtraspecial.S4Three
public import CFSG.LargeExtraspecial.S3bConj
public import Certificates.Certificate89403

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.AS91

open Subgroup CFSG.Open CFSG.LargeExtraspecial CFSG.Quasithin CFSG.Quasithin.HatM22 Module
open CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.GammaU.StepA
open CFSG.GF2Type.Smith1979.GammaU.Viol CFSG.GF2Type.Smith1979.GammaU.Enum
open CFSG.GF2Type.Smith1979.IdxFour CFSG.GF2Type.Smith1979.IdxFour.Orb
open scoped commutatorElement

namespace Two

theorem iOK43_spec :
    ((List.range 4096).filter inIb).length = 64 ∧
      (∀ w < 4096, inIb w = false →
        (sel7 (orbitList (stab1Gens ()) w)).size = 7 ∧
        (∀ v ∈ sel7 (orbitList (stab1Gens ()) w), v ∈ orbitList (stab1Gens ()) w) ∧
        ((List.range 128).map (appN (sel7 (orbitList (stab1Gens ()) w)))).Nodup) ∧
      ∀ y < 4096, (inIb y && inIb (appN (wordRows nGensI tInvWord) y)) = inZb y := by
  have h := Certificates.certificate89403
  simp only [iOK43, Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨by simpa [iCountOK] using h1, fun w hw hI => ?_, fun y hy => ?_⟩
  · have := List.all_eq_true.1 h2 w (List.mem_range.2 hw)
    simp only [iWitOK1, hI, Bool.false_or, Bool.and_eq_true, beq_iff_eq, Array.all_eq_true',
      List.contains_iff_mem, decide_eq_true_eq] at this
    exact ⟨this.1.1, fun v hv => by simpa using this.1.2 v (by simpa using hv), this.2⟩
  · have := List.all_eq_true.1 h3 y (List.mem_range.2 hy)
    simpa using this

theorem orbitList_lt {gs : List (Array ℕ)} (hgs : GensOK gs) {w : ℕ} (hw : w < 4096) :
    ∀ n ∈ orbitList gs w, n < 4096 := by
  unfold orbitList
  refine bfsClosure_inv id (gs.map appN) (P := fun n => n < 4096) ?_ 4096 [w] _ [] ?_ (by simp)
  · intro f hf n _
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hf
    exact appN_lt (okRows_spec (hgs g hg).1).2 n
  · simpa using hw

theorem tWord_three : appN (wordRows nGensI tWord) 3 = 192 := by decide +kernel

theorem tWord_mul_inv : mulR (wordRows nGensI tWord) (wordRows nGensI tInvWord) = idR := by
  decide +kernel

theorem tInvWord_mul : mulR (wordRows nGensI tInvWord) (wordRows nGensI tWord) = idR := by
  decide +kernel

@[expose] noncomputable def tE : V12 ≃ₗ[ZMod 2] V12 :=
  eqvOf (wordRows nGensI tWord) (wordRows nGensI tInvWord) tWord_mul_inv tInvWord_mul

theorem tE_apply (v : V12) : tE v = linOfRows (wordRows nGensI tWord) v := rfl

theorem tE_inv_apply (v : V12) : tE⁻¹ v = linOfRows (wordRows nGensI tInvWord) v := rfl

theorem tE_mem : tE ∈ nGrp := by
  obtain ⟨-, U, hU, hUv⟩ := rep_word gensOK_nGensI tWord (by decide)
  rw [show tE = U from LinearEquiv.ext fun v => (hUv v).symm]
  exact hU

theorem tE_three : tE (vecOf 3) = theta0 (vecOf 3) := by
  rw [tE_apply, ← vecOf_appN, tWord_three, ← vecOf_theta0N (by norm_num)]
  rfl

@[expose] def InI (v : V12) : Prop := inIb (codeOf v) = true

@[expose] def InZ (v : V12) : Prop := inZb (codeOf v) = true

theorem inI_and_inI_tE_inv_iff (y : V12) :
    InI y ∧ InI (tE⁻¹ y) ↔ InZ y := by
  have hti : ∀ x ∈ wordRows nGensI tInvWord, x < 4096 := by decide +kernel
  have hc : codeOf (tE⁻¹ y) = appN (wordRows nGensI tInvWord) (codeOf y) := by
    rw [tE_inv_apply, ← vecOf_codeOf y, ← vecOf_appN, codeOf_vecOf (appN_lt hti _),
      vecOf_codeOf]
  have := iOK43_spec.2.2 (codeOf y) (codeOf_lt y)
  rw [InI, InI, InZ, hc, ← this]
  cases inIb (codeOf y) <;> cases inIb (appN (wordRows nGensI tInvWord) (codeOf y)) <;> simp

theorem linOfRows_mem {W : Set V12} (h0 : (0 : V12) ∈ W) (hadd : ∀ x ∈ W, ∀ y ∈ W, x + y ∈ W)
    {vs : Array ℕ} (hvs : ∀ j : Fin 12, vecOf vs[(j : ℕ)]! ∈ W) (c : V12) :
    linOfRows vs c ∈ W := by
  rw [linOfRows_apply]
  refine Finset.sum_induction _ (· ∈ W) (fun a b ha hb => hadd a ha b hb) h0 fun j _ => ?_
  rcases CFSG.RankThree.Literature.FSmith.zmod2_cases (c j) with h | h
  · rw [h, zero_smul]
    exact h0
  · rw [h, one_smul]
    exact hvs j

theorem subset_inI {W : Set V12}
    (h0 : (0 : V12) ∈ W) (hadd : ∀ x ∈ W, ∀ y ∈ W, x + y ∈ W)
    (hinv : ∀ U ∈ genGrp (stab1Gens ()), ∀ x ∈ W, U x ∈ W) (hcard : W.ncard ≤ 64) :
    ∀ x ∈ W, InI x := by
  intro x hx
  by_contra hI
  have hgs : GensOK (stab1Gens ()) := (stabOK_spec (Data41.stabOK42_spec).1).1
  have hw : inIb (codeOf x) = false := by simpa [InI] using hI
  obtain ⟨hsz, hmem, hnd⟩ := iOK43_spec.2.1 (codeOf x) (codeOf_lt x) hw
  set vs := sel7 (orbitList (stab1Gens ()) (codeOf x)) with hvs
  have hvW : ∀ v ∈ vs, vecOf v ∈ W ∧ v < 4096 := fun v hv => by
    obtain ⟨U, hU, hUv⟩ := orbitList_spec hgs _ v (hmem v hv)
    rw [vecOf_codeOf] at hUv
    have hlt : v < 4096 := orbitList_lt hgs (codeOf_lt x) v (hmem v hv)
    exact ⟨hUv ▸ hinv U hU x hx, hlt⟩
  have hvs12 : ∀ j : Fin 12, vecOf vs[(j : ℕ)]! ∈ W := fun j => by
    by_cases hj : (j : ℕ) < vs.size
    · rw [getElem!_pos vs (j : ℕ) hj]
      exact (hvW _ (Array.getElem_mem hj)).1
    · rw [getElem!_neg vs (j : ℕ) hj]
      simpa using h0
  have hlt : ∀ v ∈ vs, v < 4096 := fun v hv => (hvW v hv).2
  have hcomb : ∀ c, vecOf (appN vs c) ∈ W := fun c => by
    rw [vecOf_appN]
    exact linOfRows_mem h0 hadd hvs12 _
  set L := ((List.range 128).map (appN vs)).map vecOf with hL
  have hLnd : L.Nodup := by
    refine List.Nodup.map_on (fun a ha b hb hab => ?_) hnd
    obtain ⟨c, -, rfl⟩ := List.mem_map.1 ha
    obtain ⟨d, -, rfl⟩ := List.mem_map.1 hb
    exact vecOf_inj (appN_lt (fun v hv => hlt v (by simpa using hv)) c)
      (appN_lt (fun v hv => hlt v (by simpa using hv)) d) hab
  have hsub : (L.toFinset : Set V12) ⊆ W := by
    intro y hy
    rw [Finset.mem_coe, List.mem_toFinset] at hy
    obtain ⟨n, hn, rfl⟩ := List.mem_map.1 hy
    obtain ⟨c, -, rfl⟩ := List.mem_map.1 hn
    exact hcomb c
  have h128 : (L.toFinset : Set V12).ncard = 128 := by
    rw [Set.ncard_coe_finset, List.toFinset_card_of_nodup hLnd]
    simp [hL]
  have := Set.ncard_le_ncard hsub (Set.toFinite W)
  omega

theorem ncard_inI : {v : V12 | InI v}.ncard = 64 := by
  rw [← Nat.card_coe_set_eq, ← iOK43_spec.1]
  refine card_of_codes (P := fun v => v ∈ {v : V12 | InI v}) (List.nodup_range.filter _)
    (fun n hn => List.mem_range.1 (List.mem_of_mem_filter hn)) (fun y => ?_)
  simp only [Set.mem_setOf_eq, List.mem_filter, List.mem_range, InI, decide_eq_true_eq]
  exact ⟨fun h => ⟨codeOf_lt y, h⟩, fun h => h.2⟩

theorem eq_inI {W : Set V12}
    (h0 : (0 : V12) ∈ W) (hadd : ∀ x ∈ W, ∀ y ∈ W, x + y ∈ W)
    (hinv : ∀ U ∈ genGrp (stab1Gens ()), ∀ x ∈ W, U x ∈ W) (hcard : W.ncard = 64) :
    W = {v | InI v} :=
  Set.eq_of_subset_of_ncard_le (subset_inI h0 hadd hinv hcard.le)
    (by rw [ncard_inI, hcard]) (Set.toFinite _)

theorem inZ_iff (v : V12) :
    InZ v ↔ v = 0 ∨ v = vecOf 3 ∨ v = vecOf 192 ∨ v = vecOf 195 := by
  rw [InZ]
  constructor
  · intro h
    have hc : codeOf v = 0 ∨ codeOf v = 3 ∨ codeOf v = 192 ∨ codeOf v = 195 := by
      simpa [inZb, zList] using h
    rcases hc with h | h | h | h <;> [left; (right; left); (right; right; left);
      (right; right; right)] <;> rw [← vecOf_codeOf v, h]
    exact vecOf_zero
  · rintro (rfl | rfl | rfl | rfl)
    · simp [inZb, zList, codeOf_vecOf (show (0 : ℕ) < 4096 by norm_num), ← vecOf_zero]
    all_goals rw [codeOf_vecOf (by norm_num)]; decide

theorem inZ_vecOf_iff {n : ℕ} (hn : n < 4096) : InZ (vecOf n) ↔ n ∈ zList := by
  rw [InZ, codeOf_vecOf hn, inZb, List.contains_iff_mem]

theorem inZ_theta0 {u : V12} (hu : InZ u) : InZ (theta0 u) := by
  rcases (inZ_iff u).mp hu with rfl | rfl | rfl | rfl
  · rw [map_zero]; exact hu
  all_goals
    rw [← vecOf_theta0N (by norm_num), inZ_vecOf_iff (by decide)]
    decide

theorem q0_of_inZ {u : V12} (hu : InZ u) : q0 u = 0 := by
  rcases (inZ_iff u).mp hu with rfl | rfl | rfl | rfl
  · simp [q0]
  all_goals rw [q0_vecOf]; decide

theorem inZ_zero : InZ 0 := by
  rw [← vecOf_zero, inZ_vecOf_iff (by norm_num)]
  decide

theorem card_inZ : Nat.card {u : V12 // InZ u} = 4 :=
  card_of_codes (L := zList) (by decide) (by decide) fun y => by
    rw [InZ, inZb, List.contains_iff_mem]

end Two

variable {G : Type} [Group G] [Finite G]

theorem Lbar_le_stab (S : Setting G) {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG) :
    S.Lbar g ≤ stab S (S.cl (g * S.z * g⁻¹)) := by
  intro p hp
  refine ⟨S.Lbar_le_Mbar g hp, ?_⟩
  obtain ⟨y, hyL, rfl⟩ := S.mem_Lbar_iff.mp hp
  rw [S.ρ_cl y haQ]
  congr 1
  have hc : (y : G) * (g * S.z * g⁻¹) = (g * S.z * g⁻¹) * y := (S.conjBy g).z_comm_QG hyL.1
  rw [hc, mul_inv_cancel_right]

theorem Lbar_conj_mem (S : Setting G) {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (ha1 : g * S.z * g⁻¹ ≠ 1) (hne : g * S.z * g⁻¹ ≠ S.z) {s : S.O}
    (hs : s ∈ stab S (S.cl (g * S.z * g⁻¹))) {p : S.O} (hp : p ∈ S.Lbar g) :
    s * p * s⁻¹ ∈ S.Lbar g := by
  obtain ⟨m, hma, rfl⟩ := exists_centralizer_lift S haQ ha1 hne hs
  obtain ⟨y, hyL, rfl⟩ := S.mem_Lbar_iff.mp hp
  refine S.mem_Lbar_iff.mpr ⟨m * y * m⁻¹, ⟨?_, (m * y * m⁻¹).2⟩, by
    rw [map_mul, map_mul, map_inv]⟩
  exact (S.conjBy g).conj_mem_QG (mem_centralizer_singleton_iff.mpr hma) hyL.1

theorem card_Lbar_le (S : Setting G) {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (ha1 : g * S.z * g⁻¹ ≠ 1) (hne : g * S.z * g⁻¹ ≠ S.z) {n : ℕ}
    (hle : ∀ P : Subgroup S.O, P ≤ stab S (S.cl (g * S.z * g⁻¹)) →
      (∀ s ∈ stab S (S.cl (g * S.z * g⁻¹)), ∀ p ∈ P, s * p * s⁻¹ ∈ P) → IsPGroup 2 P →
        Nat.card P ≤ n) :
    Nat.card (S.Lbar g) ≤ n := by
  refine hle _ (Lbar_le_stab S haQ) (fun s hs p hp => Lbar_conj_mem S haQ ha1 hne hs hp) ?_
  haveI := S.isElementaryAbelian_Lbar haQ
  exact CFSG.IsElementaryAbelian.isPGroup 2 _

theorem mem_Qa_iff_conj (S : Setting G) (k x : G) : x ∈ S.Qa k ↔ k⁻¹ * x * k ∈ S.QG := by
  rw [Setting.Qa_eq_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hy
  · intro hx
    exact ⟨k⁻¹ * x * k, hx, by simp [MulAut.conj_apply, mul_assoc]⟩

theorem cl_commutator (S : Setting G) {a : G} (ha : a ∈ S.QG) (b : S.M) :
    S.cl (a * b * a⁻¹ * (b : G)⁻¹) =
      S.cl a + ((S.ρ b : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl a) := by
  have hb : (b : G) * a⁻¹ * (b : G)⁻¹ ∈ S.QG := S.conj_mem_QG b.2 (S.QG.inv_mem ha)
  have e : a * b * a⁻¹ * (b : G)⁻¹ = a * ((b : G) * a⁻¹ * (b : G)⁻¹) := by group
  rw [e, S.cl_mul ha hb, S.ρ_cl b ha, ← S.cl_inv (S.conj_mem_QG b.2 ha)]
  congr 2
  group

theorem HypJ4.z_mul_z {z : G} (h : HypJ4 G z) : z * z = 1 := by
  have h2 := pow_orderOf_eq_one z
  rw [h.orderOf_z, pow_two] at h2
  exact h2

namespace Data41

variable {z : G} {h : HypJ4 G z} (D : Data41 h)

theorem conj_z
    (hOut : KG82HatM22Out)
    (hTw : KG82HatM22Twelve) (g : G) (hg : g * z * g⁻¹ ∈ Q z) :
    g * z * g⁻¹ = z ∨ ∃ k ∈ H z, k * D.rep 3 * k⁻¹ = g * z * g⁻¹ := by
  by_cases hne : g * z * g⁻¹ = z
  · exact Or.inl hne
  right
  have hz2 : g * z * g⁻¹ * (g * z * g⁻¹) = 1 := by
    calc g * z * g⁻¹ * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
      _ = 1 := by rw [h.z_mul_z]; group
  have h1 : g * z * g⁻¹ ≠ 1 := fun he => by
    have : z = 1 := by
      calc z = g⁻¹ * (g * z * g⁻¹) * g := by group
        _ = 1 := by rw [he]; group
    have h2 := h.orderOf_z
    rw [this, orderOf_one] at h2
    exact absurd h2 (by norm_num)
  rcases D.conj_or hg hz2 h1 hne with ⟨k, hk, hkr⟩ | ⟨k, hk, hkr⟩
  · exact ⟨k⁻¹, inv_mem hk, by rw [← hkr]; group⟩
  · exfalso
    have hg' : (k * g) * h.setting.z * (k * g)⁻¹ = D.rep 5 := by
      rw [← hkr, h.setting_z]
      group
    have haQ : (k * g) * h.setting.z * (k * g)⁻¹ ∈ h.setting.QG := by rw [hg']; exact D.rep_mem 5
    obtain ⟨-, h51, h5z⟩ := D.rep_props vecOf_five_ne q0_five
    have hle := card_Lbar_le h.setting haQ (by rw [hg']; exact h51) (by rw [hg']; exact h5z)
      (n := 2 ^ 4) (by rw [hg']; exact (D.core_five hOut hTw).2)
    have hge := h.setting.card_Lbar_ge haQ (by rw [hg']; exact h5z)
    rw [h.setting_width] at hge
    norm_num at hge hle
    omega

theorem exists_g₁
    (hOut : KG82HatM22Out)
    (hTw : KG82HatM22Twelve) : ∃ g₁ : G, g₁ * z * g₁⁻¹ = D.rep 3 := by
  obtain ⟨g, hgQ, hgne⟩ := h.not_weaklyClosed
  have hg' : g⁻¹ * z * g⁻¹⁻¹ ∈ Q z := by rwa [inv_inv]
  rcases D.conj_z hOut hTw g⁻¹ hg' with h1 | ⟨k, -, hkr⟩
  · exact absurd (by rwa [inv_inv] at h1) hgne
  · refine ⟨k⁻¹ * g⁻¹, ?_⟩
    calc k⁻¹ * g⁻¹ * z * (k⁻¹ * g⁻¹)⁻¹ = k⁻¹ * (g⁻¹ * z * g⁻¹⁻¹) * k := by group
      _ = D.rep 3 := by rw [← hkr]; group

theorem card_QG_inf_Qa_g₁
    (hOut : KG82HatM22Out)
    (hTw : KG82HatM22Twelve) {g₁ : G} (hg₁ : g₁ * z * g₁⁻¹ = D.rep 3) :
    Nat.card (h.setting.QG ⊓ h.setting.Qa g₁ : Subgroup G) = 2 ^ 7 := by
  obtain ⟨-, h31, h3z⟩ := D.rep_props vecOf_three_ne q0_three
  have hg₁' : g₁ * h.setting.z * g₁⁻¹ = D.rep 3 := hg₁
  have haQ : g₁ * h.setting.z * g₁⁻¹ ∈ h.setting.QG := by rw [hg₁']; exact D.rep_mem 3
  have hne : g₁ * h.setting.z * g₁⁻¹ ≠ h.setting.z := by rw [hg₁']; exact h3z
  have hle := card_Lbar_le h.setting haQ (by rw [hg₁']; exact h31) hne (n := 2 ^ 5)
    (by rw [hg₁']; exact (D.core_three hOut hTw).2)
  have hmul := h.setting.card_Lbar_mul g₁
  rw [h.setting.card_L0 haQ hne, h.setting_width] at hmul
  have hub := h.setting.card_QG_inf_Qa_le hne
  rw [h.setting_width] at hub
  have h1 : 2 ^ (2 * 6) ≤ 2 ^ 5 * Nat.card (h.setting.QG ⊓ h.setting.Qa g₁ : Subgroup G) := by
    rw [← hmul]
    exact Nat.mul_le_mul_right _ hle
  norm_num at h1 hub ⊢
  omega

theorem genGrp_stab1_eq
    (hOut : KG82HatM22Out)
    (hTw : KG82HatM22Twelve) :
    genGrp (Two.stab1Gens ()) = (stab h.setting (h.setting.cl (D.rep 3))).map D.Φo := by
  obtain ⟨-, hfix, hcS, -⟩ := Two.stabOK_spec stabOK42_spec.1
  rw [D.map_stab hOut hTw 3]
  refine Subgroup.eq_of_le_of_card_ge (fun U hU => mem_stabIn.mpr
    ⟨genGrp_stabGens_le (ws := Two.stab1Words) (by decide) hU, hfix U hU⟩) ?_
  rw [← D.map_stab hOut hTw 3, Subgroup.card_map_of_injective D.Φo_injective,
    D.card_stab_three hOut hTw, hcS]

theorem ψV_clSub_eq
    (hOut : KG82HatM22Out) (hTw : KG82HatM22Twelve) {g₁ : G} (hg₁ : g₁ * z * g₁⁻¹ = D.rep 3) :
    D.ψV '' (h.setting.clSub (h.setting.QG ⊓ h.setting.Qa g₁) : Set h.setting.Qt) =
      {v | Two.InI v} := by
  obtain ⟨-, h31, h3z⟩ := D.rep_props vecOf_three_ne q0_three
  have hg₁' : g₁ * h.setting.z * g₁⁻¹ = D.rep 3 := hg₁
  have haQ : g₁ * h.setting.z * g₁⁻¹ ∈ h.setting.QG := by rw [hg₁']; exact D.rep_mem 3
  have ha1 : g₁ * h.setting.z * g₁⁻¹ ≠ 1 := by rw [hg₁']; exact h31
  have hne : g₁ * h.setting.z * g₁⁻¹ ≠ h.setting.z := by rw [hg₁']; exact h3z
  refine Two.eq_inI ⟨0, Submodule.zero_mem _, map_zero _⟩ ?_ (fun U hU x hx => ?_) ?_
  · rintro _ ⟨u, hu, rfl⟩ _ ⟨u', hu', rfl⟩
    exact ⟨u + u', Submodule.add_mem _ hu hu', map_add _ _ _⟩
  · rw [D.genGrp_stab1_eq hOut hTw] at hU
    obtain ⟨s, hs, rfl⟩ := hU
    obtain ⟨u, hu, rfl⟩ := hx
    refine ⟨(s : h.setting.Qt ≃ₗ[ZMod 2] h.setting.Qt) u, ?_, (D.Φo_apply_ψV s u).symm⟩
    rw [← hg₁'] at hs
    obtain ⟨m, hma, rfl⟩ := exists_centralizer_lift h.setting haQ ha1 hne hs
    obtain ⟨v, hvV, hvQ, rfl⟩ := h.setting.mem_clSub_iff.mp hu
    rw [h.setting.ρ_cl m hvQ]
    exact h.setting.cl_mem_clSub ⟨h.setting.conj_mem_QG m.2 hvQ,
      (h.setting.conjBy g₁).conj_mem_QG (mem_centralizer_singleton_iff.mpr hma) hvV.2⟩
      (h.setting.conj_mem_QG m.2 hvQ)
  · rw [Set.ncard_image_of_injective _ D.ψV.injective, ← Nat.card_coe_set_eq,
      SetLike.coe_sort_coe, h.setting.card_submodule,
      S4.finrank_clSub_QG_inf_Qa haQ hne (by rw [h.setting_width]; exact D.card_QG_inf_Qa_g₁ hOut hTw hg₁),
      h.setting_width]
    norm_num

theorem mem_Qa_iff_inI
    (hOut : KG82HatM22Out) (hTw : KG82HatM22Twelve) {g₁ : G} (hg₁ : g₁ * z * g₁⁻¹ = D.rep 3)
    {x : G} (hx : x ∈ h.setting.QG) :
    x ∈ h.setting.Qa g₁ ↔ Two.InI (D.ψV (h.setting.cl x)) := by
  obtain ⟨-, -, h3z⟩ := D.rep_props vecOf_three_ne q0_three
  have hg₁' : g₁ * h.setting.z * g₁⁻¹ = D.rep 3 := hg₁
  have haQ : g₁ * h.setting.z * g₁⁻¹ ∈ h.setting.QG := by rw [hg₁']; exact D.rep_mem 3
  have hne : g₁ * h.setting.z * g₁⁻¹ ≠ h.setting.z := by rw [hg₁']; exact h3z
  have heq := D.ψV_clSub_eq hOut hTw hg₁
  constructor
  · intro hxa
    have : D.ψV (h.setting.cl x) ∈ D.ψV '' (h.setting.clSub (h.setting.QG ⊓ h.setting.Qa g₁) :
        Set h.setting.Qt) := ⟨_, h.setting.cl_mem_clSub ⟨hx, hxa⟩ hx, rfl⟩
    rw [heq] at this
    exact this
  · intro hI
    have : D.ψV (h.setting.cl x) ∈ D.ψV '' (h.setting.clSub (h.setting.QG ⊓ h.setting.Qa g₁) :
        Set h.setting.Qt) := by rw [heq]; exact hI
    obtain ⟨u, hu, hux⟩ := this
    rw [D.ψV.injective hux] at hu
    have hz : h.setting.z ∈ h.setting.QG ⊓ h.setting.Qa g₁ :=
      ⟨h.setting.z_mem_QG, h.setting.z_mem_Qa_of_mem_QG rfl haQ hne⟩
    have hx' : x ∈ h.setting.clPre (h.setting.clSub (h.setting.QG ⊓ h.setting.Qa g₁)) := ⟨hx, hu⟩
    rw [h.setting.clPre_clSub inf_le_left hz] at hx'
    exact hx'.2

theorem exists_s₀
    (hOut : KG82HatM22Out) (hTw : KG82HatM22Twelve) :
    ∃ s₀ : h.setting.M, D.Φo (h.setting.ρ s₀) = Two.tE := by
  have := Two.tE_mem
  rw [← D.map_Mbar_Φo hOut hTw] at this
  obtain ⟨m, hm, hmt⟩ := this
  obtain ⟨s₀, rfl⟩ := MonoidHom.mem_range.mp hm
  exact ⟨s₀, hmt⟩

theorem mem_Qa_s₀_iff
    (hOut : KG82HatM22Out) (hTw : KG82HatM22Twelve) {g₁ : G} (hg₁ : g₁ * z * g₁⁻¹ = D.rep 3)
    {s₀ : h.setting.M} (hs₀ : D.Φo (h.setting.ρ s₀) = Two.tE) {x : G} (hx : x ∈ h.setting.QG) :
    x ∈ h.setting.Qa ((s₀ : G) * g₁) ↔ Two.InI (Two.tE⁻¹ (D.ψV (h.setting.cl x))) := by
  have hx' : (s₀ : G)⁻¹ * x * (s₀ : G) ∈ h.setting.QG := by
    have := h.setting.conj_mem_QG (inv_mem s₀.2) hx
    simpa using this
  have e1 : x ∈ h.setting.Qa ((s₀ : G) * g₁) ↔ (s₀ : G)⁻¹ * x * (s₀ : G) ∈ h.setting.Qa g₁ := by
    rw [mem_Qa_iff_conj, mem_Qa_iff_conj, mul_inv_rev]
    simp only [mul_assoc]
  rw [e1, D.mem_Qa_iff_inI hOut hTw hg₁ hx']
  have hcl : h.setting.cl ((s₀ : G)⁻¹ * x * (s₀ : G)) =
      ((h.setting.ρ s₀⁻¹ : h.setting.O) : h.setting.Qt ≃ₗ[ZMod 2] h.setting.Qt)
        (h.setting.cl x) := by
    rw [h.setting.ρ_cl s₀⁻¹ hx]
    congr 1
    simp
  rw [hcl, ← Φo_apply_ψV, map_inv, map_inv, hs₀]

theorem mem_Z_iff
    (hOut : KG82HatM22Out) (hTw : KG82HatM22Twelve) {g₁ : G} (hg₁ : g₁ * z * g₁⁻¹ = D.rep 3)
    {s₀ : h.setting.M} (hs₀ : D.Φo (h.setting.ρ s₀) = Two.tE) {x : G} :
    x ∈ h.setting.QG ⊓ h.setting.Qa g₁ ⊓ h.setting.Qa ((s₀ : G) * g₁) ↔
      x ∈ h.setting.QG ∧ Two.InZ (D.ψV (h.setting.cl x)) := by
  constructor
  · rintro ⟨⟨hx, h1⟩, h2⟩
    exact ⟨hx, (Two.inI_and_inI_tE_inv_iff _).mp ⟨(D.mem_Qa_iff_inI hOut hTw hg₁ hx).mp h1,
      (D.mem_Qa_s₀_iff hOut hTw hg₁ hs₀ hx).mp h2⟩⟩
  · rintro ⟨hx, hZ⟩
    obtain ⟨h1, h2⟩ := (Two.inI_and_inI_tE_inv_iff _).mpr hZ
    exact ⟨⟨hx, (D.mem_Qa_iff_inI hOut hTw hg₁ hx).mpr h1⟩,
      (D.mem_Qa_s₀_iff hOut hTw hg₁ hs₀ hx).mpr h2⟩

theorem mem_of_classes {Y : Subgroup G} (hz : z ∈ Y) {y₁ y₂ : G} (hy₁ : y₁ ∈ Y) (hy₂ : y₂ ∈ Y)
    (hy₁Q : y₁ ∈ h.setting.QG) (hy₂Q : y₂ ∈ h.setting.QG) {a b : ℕ}
    (ha : D.ψV (h.setting.cl y₁) = vecOf a) (hb : D.ψV (h.setting.cl y₂) = vecOf b)
    (hab : ∀ n ∈ [3, 192, 195], n = a ∨ n = b ∨ n = a ^^^ b) {x : G} (hxQ : x ∈ h.setting.QG)
    (hxZ : Two.InZ (D.ψV (h.setting.cl x))) : x ∈ Y := by
  have hzY : h.setting.z ∈ Y := hz
  have key : ∀ y ∈ Y, y ∈ h.setting.QG → D.ψV (h.setting.cl y) = D.ψV (h.setting.cl x) →
      x ∈ Y := by
    intro y hy hyQ he
    rcases (h.setting.cl_eq_cl_iff hyQ hxQ).mp (D.ψV.injective he) with rfl | rfl
    · exact hy
    · exact Y.mul_mem hy hzY
  have hy12 : D.ψV (h.setting.cl (y₁ * y₂)) = vecOf (a ^^^ b) := by
    rw [h.setting.cl_mul hy₁Q hy₂Q, map_add, ha, hb, vecOf_xor]
  rcases (Two.inZ_iff _).mp hxZ with h0 | h3 | h192 | h195
  · refine key 1 Y.one_mem h.setting.QG.one_mem ?_
    rw [h0, h.setting.cl_one, map_zero]
  · rcases hab 3 (by simp) with e | e | e
    · exact key y₁ hy₁ hy₁Q (by rw [h3, ha, e])
    · exact key y₂ hy₂ hy₂Q (by rw [h3, hb, e])
    · exact key _ (Y.mul_mem hy₁ hy₂) (h.setting.QG.mul_mem hy₁Q hy₂Q) (by rw [h3, hy12, e])
  · rcases hab 192 (by simp) with e | e | e
    · exact key y₁ hy₁ hy₁Q (by rw [h192, ha, e])
    · exact key y₂ hy₂ hy₂Q (by rw [h192, hb, e])
    · exact key _ (Y.mul_mem hy₁ hy₂) (h.setting.QG.mul_mem hy₁Q hy₂Q) (by rw [h192, hy12, e])
  · rcases hab 195 (by simp) with e | e | e
    · exact key y₁ hy₁ hy₁Q (by rw [h195, ha, e])
    · exact key y₂ hy₂ hy₂Q (by rw [h195, hb, e])
    · exact key _ (Y.mul_mem hy₁ hy₂) (h.setting.QG.mul_mem hy₁Q hy₂Q) (by rw [h195, hy12, e])

@[expose] def Zinf (g₁ : G) (s₀ : h.setting.M) : Subgroup G :=
  Q z ⊓ (Q z).map (MulAut.conj g₁).toMonoidHom ⊓
    (Q z).map (MulAut.conj ((s₀ : G) * g₁)).toMonoidHom

omit D in
theorem Zinf_eq (g₁ : G) (s₀ : h.setting.M) :
    Zinf (h := h) g₁ s₀ = h.setting.QG ⊓ h.setting.Qa g₁ ⊓ h.setting.Qa ((s₀ : G) * g₁) := by
  rw [Zinf, ← h.setting_QG, ← Setting.Qa_eq_map, ← Setting.Qa_eq_map]

section Z

variable
  (hOut : KG82HatM22Out) (hTw : KG82HatM22Twelve) {g₁ : G} (hg₁ : g₁ * z * g₁⁻¹ = D.rep 3)
  {s₀ : h.setting.M} (hs₀ : D.Φo (h.setting.ρ s₀) = Two.tE)

include hOut hTw hg₁ hs₀

theorem mem_Zinf_iff {x : G} :
    x ∈ Zinf (h := h) g₁ s₀ ↔ x ∈ h.setting.QG ∧ Two.InZ (D.ψV (h.setting.cl x)) := by
  rw [Zinf_eq]
  exact D.mem_Z_iff hOut hTw hg₁ hs₀

theorem z_mem_Zinf : z ∈ Zinf (h := h) g₁ s₀ :=
  (D.mem_Zinf_iff hOut hTw hg₁ hs₀).mpr ⟨h.setting.z_mem_QG, by
    rw [show h.setting.cl z = 0 from h.setting.cl_z, map_zero]; exact Two.inZ_zero⟩

theorem rep3_mem_Zinf : D.rep 3 ∈ Zinf (h := h) g₁ s₀ :=
  (D.mem_Zinf_iff hOut hTw hg₁ hs₀).mpr ⟨D.rep_mem 3, by
    rw [ψV_cl_rep, Two.inZ_vecOf_iff (by norm_num)]; decide⟩

theorem ψV_cl_conj_rep3 :
    D.ψV (h.setting.cl ((s₀ : G) * D.rep 3 * (s₀ : G)⁻¹)) = vecOf 192 := by
  rw [← h.setting.ρ_cl s₀ (D.rep_mem 3), ← Φo_apply_ψV, ψV_cl_rep, hs₀, Two.tE_three,
    ← vecOf_theta0N (by norm_num)]
  rfl

theorem conj_rep3_mem_Zinf : (s₀ : G) * D.rep 3 * (s₀ : G)⁻¹ ∈ Zinf (h := h) g₁ s₀ :=
  (D.mem_Zinf_iff hOut hTw hg₁ hs₀).mpr ⟨h.setting.conj_mem_QG s₀.2 (D.rep_mem 3), by
    rw [D.ψV_cl_conj_rep3 hOut hTw hg₁ hs₀, Two.inZ_vecOf_iff (by norm_num)]; decide⟩

theorem card_Zinf : Nat.card (Zinf (h := h) g₁ s₀) = 8 := by
  have hZQ : Zinf (h := h) g₁ s₀ ≤ h.setting.QG := fun x hx =>
    ((D.mem_Zinf_iff hOut hTw hg₁ hs₀).mp hx).1
  have h1 := h.setting.card_clPre (h.setting.clSub (Zinf (h := h) g₁ s₀))
  rw [h.setting.clPre_clSub hZQ (D.z_mem_Zinf hOut hTw hg₁ hs₀)] at h1
  have hset : ∀ v, v ∈ h.setting.clSub (Zinf (h := h) g₁ s₀) ↔ Two.InZ (D.ψV v) := by
    intro v
    rw [h.setting.mem_clSub_iff]
    constructor
    · rintro ⟨x, hx, -, rfl⟩
      exact ((D.mem_Zinf_iff hOut hTw hg₁ hs₀).mp hx).2
    · intro hv
      obtain ⟨x, hxQ, rfl⟩ := h.setting.exists_cl v
      exact ⟨x, (D.mem_Zinf_iff hOut hTw hg₁ hs₀).mpr ⟨hxQ, hv⟩, hxQ, rfl⟩
  have h2 : Nat.card (h.setting.clSub (Zinf (h := h) g₁ s₀)) = 4 := by
    rw [← Two.card_inZ]
    exact Nat.card_congr ((Equiv.subtypeEquivRight hset).trans
      (D.ψV.toEquiv.subtypeEquiv fun v => Iff.rfl))
  rw [h1, h2]

theorem Zinf_sq {x : G} (hx : x ∈ Zinf (h := h) g₁ s₀) : x * x = 1 := by
  obtain ⟨hxQ, hxZ⟩ := (D.mem_Zinf_iff hOut hTw hg₁ hs₀).mp hx
  have hq : h.setting.q (h.setting.cl x) = 0 := by
    rw [← D.ψV.symm_apply_apply (h.setting.cl x), D.q_ψV_symm]
    exact Two.q0_of_inZ hxZ
  rw [h.setting.q_cl_eq_zero_iff hxQ, pow_two] at hq
  exact hq

theorem closure_eq_Zinf :
    closure {z, g₁ * z * g₁⁻¹, ((s₀ : G) * g₁) * z * ((s₀ : G) * g₁)⁻¹} =
      Zinf (h := h) g₁ s₀ := by
  have e : ((s₀ : G) * g₁) * z * ((s₀ : G) * g₁)⁻¹ = (s₀ : G) * D.rep 3 * (s₀ : G)⁻¹ := by
    rw [← hg₁]; group
  rw [hg₁, e]
  apply le_antisymm
  · rw [closure_le]
    rintro x (rfl | rfl | rfl)
    · exact D.z_mem_Zinf hOut hTw hg₁ hs₀
    · exact D.rep3_mem_Zinf hOut hTw hg₁ hs₀
    · exact D.conj_rep3_mem_Zinf hOut hTw hg₁ hs₀
  · intro x hx
    obtain ⟨hxQ, hxZ⟩ := (D.mem_Zinf_iff hOut hTw hg₁ hs₀).mp hx
    exact D.mem_of_classes (subset_closure (by simp)) (subset_closure (by simp))
      (subset_closure (by simp)) (D.rep_mem 3) (h.setting.conj_mem_QG s₀.2 (D.rep_mem 3))
      (D.ψV_cl_rep 3) (D.ψV_cl_conj_rep3 hOut hTw hg₁ hs₀) (by decide) hxQ hxZ

theorem c_conj_mem_Zinf {y : G} (hy : y ∈ Zinf (h := h) g₁ s₀) :
    (D.c : G) * y * (D.c : G)⁻¹ ∈ Zinf (h := h) g₁ s₀ := by
  obtain ⟨hyQ, hyZ⟩ := (D.mem_Zinf_iff hOut hTw hg₁ hs₀).mp hy
  refine (D.mem_Zinf_iff hOut hTw hg₁ hs₀).mpr ⟨h.setting.conj_mem_QG D.c.2 hyQ, ?_⟩
  rw [← h.setting.ρ_cl D.c hyQ, ← Φo_apply_ψV, Φo_apply, D.ρ_c]
  rcases D.Φ_θ with hθ | hθ
  · rw [hθ]; exact Two.inZ_theta0 hyZ
  · rw [hθ]; exact Two.inZ_theta0 (Two.inZ_theta0 hyZ)

theorem sup_eq_Zinf :
    zpowers z ⊔ ⁅zpowers (D.rep 3), zpowers (D.c : G)⁆ = Zinf (h := h) g₁ s₀ := by
  classical
  have hN : (D.c : G) ∈ normalizer (Zinf (h := h) g₁ s₀ : Set G) :=
    mem_normalizer_fintype fun y hy => D.c_conj_mem_Zinf hOut hTw hg₁ hs₀ hy
  have hNc : zpowers (D.c : G) ≤ normalizer (Zinf (h := h) g₁ s₀ : Set G) := zpowers_le.mpr hN
  have hr : zpowers (D.rep 3) ≤ Zinf (h := h) g₁ s₀ :=
    zpowers_le.mpr (D.rep3_mem_Zinf hOut hTw hg₁ hs₀)
  apply le_antisymm
  · refine sup_le (zpowers_le.mpr (D.z_mem_Zinf hOut hTw hg₁ hs₀)) ?_
    rw [commutator_le]
    intro a ha b hb
    have haZ := hr ha
    have hb' := (mem_normalizer_iff.mp (hNc hb) a⁻¹).mp (inv_mem haZ)
    rw [commutatorElement_def, mul_assoc a b, mul_assoc a]
    exact mul_mem haZ (by simpa [mul_assoc] using hb')
  · intro x hx
    obtain ⟨hxQ, hxZ⟩ := (D.mem_Zinf_iff hOut hTw hg₁ hs₀).mp hx
    have hc1 : ⁅D.rep 3, (D.c : G)⁆ ∈ zpowers z ⊔ ⁅zpowers (D.rep 3), zpowers (D.c : G)⁆ :=
      mem_sup_right (commutator_mem_commutator (mem_zpowers _) (mem_zpowers _))
    have hc2 : ⁅D.rep 3, ((D.c⁻¹ : h.setting.M) : G)⁆ ∈
        zpowers z ⊔ ⁅zpowers (D.rep 3), zpowers (D.c : G)⁆ :=
      mem_sup_right (commutator_mem_commutator (mem_zpowers _)
        (by rw [Subgroup.coe_inv]; exact inv_mem (mem_zpowers _)))
    have hcl : ∀ b : h.setting.M, D.ψV (h.setting.cl ⁅D.rep 3, (b : G)⁆) =
        vecOf 3 + D.Φo (h.setting.ρ b) (vecOf 3) := fun b => by
      rw [commutatorElement_def, cl_commutator h.setting (D.rep_mem 3) b, map_add, ψV_cl_rep,
        ← Φo_apply_ψV, ψV_cl_rep]
    have hQ : ∀ b : h.setting.M, ⁅D.rep 3, (b : G)⁆ ∈ h.setting.QG := fun b => by
      rw [commutatorElement_def, mul_assoc (D.rep 3), mul_assoc (D.rep 3)]
      refine h.setting.QG.mul_mem (D.rep_mem 3) ?_
      have := h.setting.conj_mem_QG b.2 (h.setting.QG.inv_mem (D.rep_mem 3))
      simpa [mul_assoc] using this
    have hθ1 : D.Φo (h.setting.ρ D.c) = D.Φ (D.θ : h.setting.Qt ≃ₗ[ZMod 2] h.setting.Qt) := by
      rw [Φo_apply, D.ρ_c]
    have hθ2 : D.Φo (h.setting.ρ D.c⁻¹) =
        (D.Φ (D.θ : h.setting.Qt ≃ₗ[ZMod 2] h.setting.Qt))⁻¹ := by
      rw [map_inv, map_inv, hθ1]
    have h3 := theta0_theta0_theta0
    rcases D.Φ_θ with hθ | hθ
    · have e1 : D.ψV (h.setting.cl ⁅D.rep 3, (D.c : G)⁆) = vecOf 195 := by
        rw [hcl, hθ1, hθ, ← vecOf_theta0N (by norm_num), ← vecOf_xor]; rfl
      have e2 : D.ψV (h.setting.cl ⁅D.rep 3, ((D.c⁻¹ : h.setting.M) : G)⁆) = vecOf 192 := by
        rw [hcl, hθ2]
        have hinv : (D.Φ (D.θ : h.setting.Qt ≃ₗ[ZMod 2] h.setting.Qt))⁻¹ (vecOf 3) =
            theta0 (theta0 (vecOf 3)) := by
          change (D.Φ _).symm _ = _
          rw [LinearEquiv.symm_apply_eq, hθ, h3]
        rw [hinv, ← vecOf_theta0N (by norm_num), ← vecOf_theta0N (by decide), ← vecOf_xor]; rfl
      exact D.mem_of_classes (mem_sup_left (mem_zpowers z)) hc1 hc2 (hQ D.c) (hQ D.c⁻¹) e1 e2
        (by decide) hxQ hxZ
    · have e1 : D.ψV (h.setting.cl ⁅D.rep 3, (D.c : G)⁆) = vecOf 192 := by
        rw [hcl, hθ1, hθ, ← vecOf_theta0N (by norm_num), ← vecOf_theta0N (by decide),
          ← vecOf_xor]; rfl
      have e2 : D.ψV (h.setting.cl ⁅D.rep 3, ((D.c⁻¹ : h.setting.M) : G)⁆) = vecOf 195 := by
        rw [hcl, hθ2]
        have hinv : (D.Φ (D.θ : h.setting.Qt ≃ₗ[ZMod 2] h.setting.Qt))⁻¹ (vecOf 3) =
            theta0 (vecOf 3) := by
          change (D.Φ _).symm _ = _
          rw [LinearEquiv.symm_apply_eq, hθ, h3]
        rw [hinv, ← vecOf_theta0N (by norm_num), ← vecOf_xor]; rfl
      exact D.mem_of_classes (mem_sup_left (mem_zpowers z)) hc1 hc2 (hQ D.c) (hQ D.c⁻¹) e1 e2
        (by decide) hxQ hxZ

end Z

@[expose] noncomputable def toLoc43
    (hHat : HatM22SmallModules) (hOut : KG82HatM22Out) (hTw : KG82HatM22Twelve) : Loc43 G z where
  toLoc42 := D.toLoc42 hHat hOut hTw
  g₁ := (D.exists_g₁ hOut hTw).choose
  r₁_eq := (D.exists_g₁ hOut hTw).choose_spec
  conj_z := D.conj_z hOut hTw
  card_inf := by
    rw [← h.setting_QG, ← Setting.Qa_eq_map]
    exact D.card_QG_inf_Qa_g₁ hOut hTw (D.exists_g₁ hOut hTw).choose_spec
  k₁ := ((D.exists_s₀ hOut hTw).choose : G) * (D.exists_g₁ hOut hTw).choose
  Z := Zinf (h := h) (D.exists_g₁ hOut hTw).choose (D.exists_s₀ hOut hTw).choose
  Z_eq_inf := rfl
  Z_eq_closure := (D.closure_eq_Zinf hOut hTw (D.exists_g₁ hOut hTw).choose_spec
    (D.exists_s₀ hOut hTw).choose_spec).symm
  Z_eq_sup := (D.sup_eq_Zinf hOut hTw (D.exists_g₁ hOut hTw).choose_spec
    (D.exists_s₀ hOut hTw).choose_spec).symm
  card_Z := D.card_Zinf hOut hTw (D.exists_g₁ hOut hTw).choose_spec
    (D.exists_s₀ hOut hTw).choose_spec
  Z_sq := fun _ hx => D.Zinf_sq hOut hTw (D.exists_g₁ hOut hTw).choose_spec
    (D.exists_s₀ hOut hTw).choose_spec hx

end Data41

end CFSG.Quasithin.H13.AS91
