module

public import CFSG.Quasithin.Vol2.Ch12Sec4C8X
public import CFSG.Quasithin.Background.S1549DL3N
public import CFSG.Quasithin.Vol2.Ch12Sec4G2NormZorn

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin Orbit
open CFSG.Quasithin.H.Mathieu (RealizesBy realizes_iff)
open scoped Pointwise

namespace G2NoOff

theorem matCode_wordG {w : List ℕ} (hw : ∀ t ∈ w, t = 1 ∨ t = 2) :
    matCode ⇑(wordG (R := ZMod 2) w) = (List.range 8).map fun k => applyG w (2 ^ k) := by
  unfold matCode
  refine List.map_congr_left fun k hk => ?_
  have hk8 : 2 ^ k < 256 := by
    have h8 : k < 8 := List.mem_range.1 hk
    calc 2 ^ k < 2 ^ 8 := Nat.pow_lt_pow_right (by norm_num) h8
      _ = 256 := by norm_num
  obtain ⟨h1, h2⟩ := decodeZ_applyG hw hk8
  rw [← h1, encodeZ_decodeZ _ h2]

@[expose] def wT01 : List ℕ := [1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2]

@[expose] def wT10 : List ℕ := [2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1]

@[expose] def outerIdx : List ℕ := [8, 9, 10, 16, 32, 48]

@[expose] def outerW : List (List ℕ) := [
  [1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 2], [2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 1],
  [2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2], [], [1, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2],
  [2, 1, 2, 1, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2]]

@[expose] def outerWord (i : ℕ) : List ℕ := outerW.getD (outerIdx.idxOf i) []

theorem words_check :
    (∀ t ∈ wT01, t = 1 ∨ t = 2) ∧ (∀ t ∈ wT10, t = 1 ∨ t = 2) ∧
      (List.range 8).map (fun k => applyG wT01 (2 ^ k)) = matT01 ∧
      (List.range 8).map (fun k => applyG wT10 (2 ^ k)) = matT10 := by
  decide +kernel

theorem outer_check : ∀ i ∈ outerIdx, (∀ t ∈ outerWord i, t = 1 ∨ t = 2) ∧ i < 64 ∧
    mmul ((List.range 8).map fun k => applyG (outerWord i) (2 ^ k)) matX = sM i := by
  decide +kernel

theorem sE8_outer : ∀ e < 8, ∃ i ∈ sE8.getD e [], i ∈ outerIdx := by
  decide

theorem zT01_mem :
    (zT01 : quasithinZorn (ZMod 2) ≃ₗ[ZMod 2] _) ∈ ⁅quasithinG2 (ZMod 2), quasithinG2 (ZMod 2)⁆ := by
  obtain ⟨h1, -, h3, -⟩ := words_check
  have e : (zT01 : quasithinZorn (ZMod 2) ≃ₗ[ZMod 2] _) = wordG wT01 :=
    linearEquiv_eq_of_matCode (by rw [matCode_zT01, matCode_wordG h1, h3])
  rw [e]
  exact wordG_mem _

theorem zT10_mem :
    (zT10 : quasithinZorn (ZMod 2) ≃ₗ[ZMod 2] _) ∈ ⁅quasithinG2 (ZMod 2), quasithinG2 (ZMod 2)⁆ := by
  obtain ⟨-, h2, -, h4⟩ := words_check
  have e : (zT10 : quasithinZorn (ZMod 2) ≃ₗ[ZMod 2] _) = wordG wT10 :=
    linearEquiv_eq_of_matCode (by rw [matCode_zT10, matCode_wordG h2, h4])
  rw [e]
  exact wordG_mem _

theorem zX_not_mem :
    (zX : quasithinZorn (ZMod 2) ≃ₗ[ZMod 2] _) ∉ ⁅quasithinG2 (ZMod 2), quasithinG2 (ZMod 2)⁆ := by
  intro hX
  set D := ⁅quasithinG2 (ZMod 2), quasithinG2 (ZMod 2)⁆ with hD
  have hgen : ∀ j, sGenE j ∈ D := by
    intro j
    unfold sGenE
    split_ifs
    · exact zT01_mem
    · exact hX
    · exact mul_mem (mul_mem (mul_mem (mul_mem zT10_mem zT01_mem) hX) zT01_mem) zT10_mem
  have hfold : ∀ (w : List ℕ) (g : quasithinZorn (ZMod 2) ≃ₗ[ZMod 2] quasithinZorn (ZMod 2)),
      g ∈ D → w.foldl (fun g j => g * sGenE j) g ∈ D := by
    intro w
    induction w with
    | nil => exact fun g hg => hg
    | cons j w ih => exact fun g hg => ih _ (mul_mem hg (hgen j))
  have hS : sSub ≤ D := by
    intro g hg
    obtain ⟨i, -, rfl⟩ := mem_sSub.1 hg
    exact hfold _ 1 (one_mem _)
  have hdvd := Subgroup.card_dvd_of_le hS
  rw [card_sSub, S1549D.card_commutator_quasithinG2_two (Nat.card_zmod 2)] at hdvd
  norm_num at hdvd

theorem sEltG_not_mem
    {i : ℕ} (hi : i ∈ outerIdx) :
    sEltG i ∉ g2Derived (ZMod 2) := by
  intro h
  have h' : sElt i ∈ ⁅quasithinG2 (ZMod 2), quasithinG2 (ZMod 2)⁆ := Subgroup.mem_subgroupOf.1 h
  obtain ⟨hw, hi64, hcode⟩ := outer_check i hi
  have e : sElt i = wordG (outerWord i) * zX :=
    linearEquiv_eq_of_matCode (by
      rw [matCode_sElt hi64, matCode_mul, matCode_wordG hw, matCode_zX, hcode])
  rw [e] at h'
  apply zX_not_mem
  have h2 := mul_mem (inv_mem (wordG_mem (R := ZMod 2) (outerWord i))) h'
  rwa [inv_mul_cancel_left] at h2

theorem false_of_sylow
    {B : Subgroup ↥(quasithinG2 (ZMod 2))} (hB : B ≤ sSubG) (hBD : B ≤ g2Derived (ZMod 2))
    (hB1 : B ≠ ⊥) (hBc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) (hB2 : ∀ b ∈ B, b ^ 2 = 1)
    (hff : 128 ≤ (idx B).card * Nat.card (fixV (B.map (g2OAct (ZMod 2))))) : False := by
  classical
  let P : ℕ → Bool := fun c => decide (∀ i ∈ idx B, fixOB (sM i) c = true)
  have hP : ∀ c : O0C, P c.1 = true ↔ ∀ i ∈ idx B, fixOB (sM i) c.1 = true := fun c => by
    simp [P]
  have hC := card_fixV_O hB P hP
  have hCi : ∀ i ∈ idx B, Nat.card (fixV (B.map (g2OAct (ZMod 2)))) ≤
      (o0Codes.filter (fixOB (sM i))).length := fun i hi => by
    rw [hC]
    exact length_filter_le fun c hc => by simp only [P, decide_eq_true_eq] at hc; exact hc i hi
  have hCij : ∀ i ∈ idx B, ∀ j ∈ idx B, Nat.card (fixV (B.map (g2OAct (ZMod 2)))) ≤
      (o0Codes.filter fun c => fixOB (sM i) c && fixOB (sM j) c).length := fun i hi j hj => by
    rw [hC]
    refine length_filter_le fun c hc => ?_
    simp only [P, decide_eq_true_eq] at hc
    simp [hc i hi, hc j hj]
  have hsingle : ∀ i ∈ idx B, i ≠ 0 → (o0Codes.filter (fixOB (sM i))).length ≤ 32 := by
    intro i hi hi0
    rcases List.mem_append.1 (idx_inv hB2 hi hi0) with h | h
    · rw [(sInner_fix i h).1]
    · rw [(sOuter_fix i h).1]
      norm_num
  rcases pow_two_cases (card_idx_pow hB hB2) with hn | hn | hn | h8
  · exact hB1 (Subgroup.eq_bot_of_card_eq B (by rw [card_eq_idx hB, hn]))
  · obtain ⟨i, hi, hi0⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (s := ({0} : Finset ℕ)) (t := idx B) (by rw [Finset.card_singleton, hn]; norm_num)
    rw [Finset.mem_singleton] at hi0
    have h1 := (hCi i hi).trans (hsingle i hi hi0)
    rw [hn] at hff
    omega
  · obtain ⟨i, hi, hi0⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (s := ({0} : Finset ℕ)) (t := idx B) (by rw [Finset.card_singleton, hn]; norm_num)
    obtain ⟨j, hj, hj0⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (s := ({0, i} : Finset ℕ)) (t := idx B)
      (by have := Finset.card_le_two (a := 0) (b := i); rw [hn]; omega)
    simp only [Finset.mem_singleton, Finset.mem_insert, not_or] at hi0 hj0
    rw [hn] at hff
    have hbound : Nat.card (fixV (B.map (g2OAct (ZMod 2)))) < 32 := by
      rcases List.mem_append.1 (idx_inv hB2 hi hi0) with h | h
      · rcases List.mem_append.1 (idx_inv hB2 hj hj0.1) with h' | h'
        · exact (hCij i hi j hj).trans_lt
            (sInner_pair i h j h' (Ne.symm hj0.2) (idx_comm hBc hi hj)).1
        · have := (hCi j hj).trans_eq (sOuter_fix j h').1
          omega
      · have := (hCi i hi).trans_eq (sOuter_fix i h).1
        omega
    omega
  · obtain ⟨e, he, hiff⟩ := idx_eq_sE8 hB hB2 hBc h8
    obtain ⟨i, hi, hiO⟩ := sE8_outer e he
    exact sEltG_not_mem hiO (hBD (mem_idx.1 ((hiff i).2 hi)).2)

theorem false_of_derived
    {B : Subgroup ↥(quasithinG2 (ZMod 2))} (hBD : B ≤ g2Derived (ZMod 2)) (hB1 : B ≠ ⊥)
    (hBc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) (hB2 : ∀ b ∈ B, b ^ 2 = 1)
    (hff : 128 ≤ Nat.card B * Nat.card (fixV (B.map (g2OAct (ZMod 2))))) : False := by
  set ρ := g2OAct (ZMod 2)
  have hp : IsPGroup 2 ↥B := fun g => ⟨1, by rw [pow_one]; exact Subtype.ext (hB2 g.1 g.2)⟩
  obtain ⟨P, hP⟩ := hp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥(quasithinG2 (ZMod 2)) P sylowSub
  set c := (MulAut.conj g).toMonoidHom with hcdef
  have hcinj : Function.Injective c := (MulAut.conj g).injective
  set B₁ := B.map c with hB₁def
  have hB₁S : B₁ ≤ sSubG := by
    rintro _ ⟨b, hb, rfl⟩
    have h1 : MulAut.conj g • b ∈ MulAut.conj g • (P : Subgroup ↥(quasithinG2 (ZMod 2))) :=
      Subgroup.smul_mem_pointwise_smul _ _ _ (hP hb)
    rw [← Sylow.coe_subgroup_smul, hg] at h1
    exact h1
  have hn : (g2Derived (ZMod 2)).Normal := by
    rw [g2Derived_eq_commutator]
    exact Subgroup.commutator_normal ⊤ ⊤
  have hB₁D : B₁ ≤ g2Derived (ZMod 2) := by
    rintro _ ⟨b, hb, rfl⟩
    exact hn.conj_mem _ (hBD hb) g
  have hB₁ne : B₁ ≠ ⊥ := by
    intro h
    exact hB1 ((Subgroup.map_eq_bot_iff_of_injective _ hcinj).1 h)
  have hB₁c : ∀ a ∈ B₁, ∀ b ∈ B₁, a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hBc a ha b hb]
  have hB₁2 : ∀ b ∈ B₁, b ^ 2 = 1 := by
    rintro _ ⟨b, hb, rfl⟩
    rw [← map_pow, hB2 b hb, map_one]
  have hmap : B₁.map ρ = (B.map ρ).map (MulAut.congr (ρ g)).toMonoidHom := by
    rw [hB₁def, Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext b m
    change ρ (g * b * g⁻¹) m = MulAut.congr (ρ g) (ρ b) m
    rw [congr_eq_conj, map_mul, map_mul, map_inv]
  have hcardB : Nat.card B₁ = Nat.card B := by
    rw [hB₁def, Subgroup.card_map_of_injective hcinj]
  have hfix : Nat.card (fixV (B₁.map ρ)) = Nat.card (fixV (B.map ρ)) := by
    rw [hmap, fixV_map_congr,
      Subgroup.card_map_of_injective (f := (ρ g).toMonoidHom) (ρ g).injective]
  exact false_of_sylow hB₁S hB₁D hB₁ne hB₁c hB₁2
    (by rw [← card_eq_idx hB₁S, hcardB, hfix]; exact hff)

theorem congr_trans {A B C : Type} [Group A] [Group B] [Group C] (e : A ≃* B) (f : B ≃* C) :
    (MulAut.congr (e.trans f)).toMonoidHom =
      (MulAut.congr f).toMonoidHom.comp (MulAut.congr e).toMonoidHom := by
  ext a x
  rfl

theorem exists_weylEquiv
    {V : Type} [CommGroup V] [Finite V] (hV2 : ∀ v : V, v ^ 2 = 1) {Lb : Subgroup (MulAut V)}
    (hcomm : commV Lb = ⊤) (hfix : Nat.card (fixV Lb) = 2)
    (hnat : G2NaturalDerived Lb ⊤ (fixV Lb) 1) :
    ∃ e : V ≃* ModO,
      Lb.map (MulAut.congr e).toMonoidHom = (g2Derived (ZMod 2)).map (g2OAct (ZMod 2)) := by
  rcases VolI.g2NaturalCover_holds V hV2 Lb (fixV Lb) le_rfl hcomm hnat with hZ | ⟨-, -, hWeyl⟩
  · rw [hZ, Subgroup.card_bot] at hfix
    norm_num at hfix
  · obtain ⟨K, _, _, hK2, hR⟩ := hWeyl
    have := charP_two_of_natCard_two hK2
    obtain ⟨π, β, hβ⟩ := (realizes_iff _ Lb ⊤ ⊥).1 hR
    let e₁ : V ≃* (zornO0Model (quasithinG2 K)).Mod :=
      realizeEquiv (D := zornO0Model ⁅quasithinG2 K, quasithinG2 K⁆) hβ
    have h1 : Lb.map (MulAut.congr e₁).toMonoidHom = (g2Derived K).map (g2OAct K) :=
      map_congr_eq_of_equivariant e₁ π hβ.1 (g2OAct K)
        (fun γ => ⟨γ.1, Subgroup.commutator_le_self _ γ.2⟩) (realizeEquiv_zornO0 hβ) _
        (mem_map_g2Derived_iff (g2OAct K))
    refine ⟨e₁.trans (modOEquivK hK2).symm, ?_⟩
    rw [congr_trans, ← Subgroup.map_map, h1, Subgroup.map_map, ← map_g2Derived_conjF2Hom hK2,
      Subgroup.map_map]
    congr 1
    ext g : 1
    change MulAut.congr (modOEquivK hK2).symm (g2OAct K g) = g2OAct (ZMod 2) (conjF2Hom hK2 g)
    rw [congr_modOEquivK_symm hK2 g, conjF2Hom_apply]

end G2NoOff

open G2NoOff

theorem g2DerivedNoOffender1248 :
    G2DerivedNoOffender1248 := by
  intro V _ _ hV2 Lb hcomm hfix hnat B hBL hB1 hBe hff
  obtain ⟨e, he⟩ := exists_weylEquiv hV2 hcomm hfix hnat
  set φ := (MulAut.congr e).toMonoidHom with hφdef
  have hφinj : Function.Injective φ := (MulAut.congr e).injective
  set B' := B.map φ with hB'def
  have hB'le : B' ≤ (g2Derived (ZMod 2)).map (g2OAct (ZMod 2)) := by
    rw [← he]
    exact Subgroup.map_mono hBL
  have hB'e : IsElemAbelian2 B' := isElemAbelian2_map_congr e hBe
  set B₀ := B'.comap (g2OAct (ZMod 2)) with hB₀def
  have hB₀map : B₀.map (g2OAct (ZMod 2)) = B' :=
    Subgroup.map_comap_eq_self (hB'le.trans (Subgroup.map_le_range _ _))
  have hB₀D : B₀ ≤ g2Derived (ZMod 2) := by
    intro g hg
    obtain ⟨d, hd, hdg⟩ := hB'le hg
    rwa [g2OAct_injective hdg] at hd
  have hB₀ne : B₀ ≠ ⊥ := by
    intro h
    apply hB1
    have h1 : B' = ⊥ := by rw [← hB₀map, h, Subgroup.map_bot]
    exact (Subgroup.map_eq_bot_iff_of_injective _ hφinj).1 h1
  have hB₀c : ∀ a ∈ B₀, ∀ b ∈ B₀, a * b = b * a := fun a ha b hb =>
    g2OAct_injective (by rw [map_mul, map_mul]; exact hB'e.1 _ ha _ hb)
  have hB₀2 : ∀ b ∈ B₀, b ^ 2 = 1 := fun b hb =>
    g2OAct_injective (by rw [map_pow, map_one]; exact hB'e.2 _ hb)
  have hcard : Nat.card B₀ = Nat.card B := by
    rw [← Subgroup.card_map_of_injective (K := B₀) g2OAct_injective, hB₀map,
      Subgroup.card_map_of_injective hφinj]
  have hfixeq : Nat.card (fixV (B₀.map (g2OAct (ZMod 2)))) = Nat.card (fixV B) := by
    rw [hB₀map, hB'def, fixV_map_congr,
      Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective]
  have hV : Nat.card V = 128 := by rw [Nat.card_congr e.toEquiv, card_ModO]
  exact false_of_derived hB₀D hB₀ne hB₀c hB₀2 (by rw [hcard, hfixeq, ← hV]; exact hff)

end CFSG.Quasithin.H13
