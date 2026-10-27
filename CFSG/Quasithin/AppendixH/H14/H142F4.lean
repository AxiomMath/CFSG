module

public import CFSG.GH74.KGroups.FieldGF
public import CFSG.Quasithin.AppendixH.H14.Vocab

public section

namespace CFSG.Quasithin.AppendixH.H14

open CFSG.GH74.KGroups CFSG.ASVolI.ChH

lemma gf4_eq_cases (c : GF4) : c = 0 ∨ c = 1 ∨ c = GF4.ofNat' 2 ∨ c = GF4.ofNat' 3 := by
  fin_cases c <;> decide

lemma gf4_root_sq_add_self_add_one :
    ∀ s : GF4, s * s + s + 1 = 0 → s = GF4.ofNat' 2 ∨ s = GF4.ofNat' 3 := by
  decide

theorem card_gf4 : Nat.card GF4 = 4 := by
  rw [Nat.card_eq_fintype_card]
  decide

@[expose] def frobGF4 : GF4 ≃+* GF4 where
  toFun c := c * c
  invFun c := c * c
  left_inv := by decide
  right_inv := by decide
  map_mul' := by decide
  map_add' := by decide

theorem ringEquiv_gf4_cases (σ : GF4 ≃+* GF4) : σ = RingEquiv.refl GF4 ∨ σ = frobGF4 := by
  have hs : σ (GF4.ofNat' 2) * σ (GF4.ofNat' 2) + σ (GF4.ofNat' 2) + 1 = 0 := by
    have h2 : GF4.ofNat' 2 * GF4.ofNat' 2 + GF4.ofNat' 2 + 1 = 0 := by decide
    simpa using congrArg σ h2
  have h3 : GF4.ofNat' 3 = GF4.ofNat' 2 + 1 := by decide
  rcases gf4_root_sq_add_self_add_one _ hs with h | h
  · left
    ext c
    rcases gf4_eq_cases c with hc | hc | hc | hc
    · subst hc; simp
    · subst hc; simp
    · subst hc; simpa using h
    · subst hc
      rw [h3, map_add, map_one, h]
      simp
  · right
    ext c
    rcases gf4_eq_cases c with hc | hc | hc | hc
    · subst hc; simp
    · subst hc; simp
    · subst hc; rw [h]; decide
    · subst hc
      rw [h3, map_add, map_one, h]
      decide

@[expose] def codeOf (w : Fin 2 → GF4) : ℕ := (w 0).toNat + 4 * (w 1).toNat

@[expose] def wOfCode (n : ℕ) : Fin 2 → GF4 := ![GF4.ofNat' n, GF4.ofNat' (n / 4)]

@[expose] def sigC (s c : ℕ) : ℕ := if s = 0 then c else GF4.mulNat c c

@[expose] def smulCode (c n : ℕ) : ℕ := GF4.mulNat c (n % 4) + 4 * GF4.mulNat c (n / 4)

@[expose] def sigF (s : ℕ) (c : GF4) : GF4 := if s = 0 then c else c * c

@[expose] def sigE (s : ℕ) : GF4 ≃+* GF4 := if s = 0 then RingEquiv.refl GF4 else frobGF4

lemma gf4_ofNat_toNat (a : GF4) : GF4.ofNat' a.toNat = a := by
  decide +revert

lemma gf4_mulNat_lt_four {a b : ℕ} (ha : a < 4) (hb : b < 4) : GF4.mulNat a b < 4 := by
  have key : ∀ a b : Fin 4, GF4.mulNat (a : ℕ) (b : ℕ) < 4 := by decide
  exact key ⟨a, ha⟩ ⟨b, hb⟩

lemma sigC_lt {s c : ℕ} (hc : c < 4) : sigC s c < 4 := by
  unfold sigC
  split
  · assumption
  · exact gf4_mulNat_lt_four hc hc

lemma ofNat_sigC (s : ℕ) (c : GF4) : GF4.ofNat' (sigC s c.toNat) = sigF s c := by
  by_cases hs : s = 0
  · simp [sigC, sigF, hs, gf4_ofNat_toNat]
  · simp only [sigC, sigF, if_neg hs]
    rfl

lemma sigE_toNat (s : ℕ) (c : GF4) : (sigE s c).toNat = sigC s c.toNat := by
  by_cases hs : s = 0
  · simp [sigE, sigC, hs]
  · rw [sigE, if_neg hs]
    change (c * c).toNat = sigC s c.toNat
    rw [sigC, if_neg hs]
    show (GF4.mulNat c.toNat c.toNat) % 4 = GF4.mulNat c.toNat c.toNat
    exact Nat.mod_eq_of_lt (gf4_mulNat_lt_four c.val.isLt c.val.isLt)

lemma wOfCode_smulCode {d m : ℕ} (hd : d < 4) (hm : m < 16) :
    wOfCode (smulCode d m) = GF4.ofNat' d • wOfCode m := by
  have key : ∀ d : Fin 4, ∀ m : Fin 16,
      wOfCode (smulCode (d : ℕ) (m : ℕ)) = GF4.ofNat' (d : ℕ) • wOfCode (m : ℕ) := by decide
  exact key ⟨d, hd⟩ ⟨m, hm⟩

lemma wOfCode_one : wOfCode 1 = ![1, 0] := by decide

lemma wOfCode_four : wOfCode 4 = ![0, 1] := by decide

theorem sigE_apply (s : ℕ) (c : GF4) : sigE s c = sigF s c := by
  by_cases hs : s = 0 <;> simp [sigE, sigF, hs, frobGF4]

theorem codeOf_lt (w : Fin 2 → GF4) : codeOf w < 16 := by
  have h0 := (w 0).val.isLt
  have h1 := (w 1).val.isLt
  simp only [codeOf, GF4.toNat]
  omega

lemma gf4_toNat_ofNat (n : ℕ) : (GF4.ofNat' n).toNat = n % 4 := rfl

theorem codeOf_wOfCode {n : ℕ} (hn : n < 16) : codeOf (wOfCode n) = n := by
  have h0 : (wOfCode n) 0 = GF4.ofNat' n := by simp [wOfCode]
  have h1 : (wOfCode n) 1 = GF4.ofNat' (n / 4) := by simp [wOfCode]
  rw [codeOf, h0, h1, gf4_toNat_ofNat, gf4_toNat_ofNat]
  rw [Nat.mod_eq_of_lt (show n / 4 < 4 by omega), Nat.mod_add_div]

theorem wOfCode_codeOf (w : Fin 2 → GF4) : wOfCode (codeOf w) = w := by
  have key : ∀ a b : GF4, wOfCode (codeOf ![a, b]) = ![a, b] := by decide
  have hw : w = ![w 0, w 1] := by funext i; fin_cases i <;> simp
  rw [hw]
  exact key (w 0) (w 1)

lemma codeOf_injective : Function.Injective codeOf := by
  intro v w h
  rw [← wOfCode_codeOf v, ← wOfCode_codeOf w, h]

lemma wOfCode_injOn : Set.InjOn wOfCode {n : ℕ | n < 16} := by
  intro n hn m hm h
  have h' := congrArg codeOf h
  rwa [codeOf_wOfCode hn, codeOf_wOfCode hm] at h'

theorem codeOf_add (v w : Fin 2 → GF4) : codeOf (v + w) = codeOf v ^^^ codeOf w := by
  have key : ∀ a b c d : GF4,
      codeOf (![a, b] + ![c, d]) = codeOf ![a, b] ^^^ codeOf ![c, d] := by decide
  have hv : v = ![v 0, v 1] := by funext i; fin_cases i <;> simp
  have hw : w = ![w 0, w 1] := by funext i; fin_cases i <;> simp
  rw [hv, hw]
  exact key (v 0) (v 1) (w 0) (w 1)

theorem codeOf_smul (c : GF4) (w : Fin 2 → GF4) : codeOf (c • w) = smulCode c.toNat (codeOf w) := by
  have key : ∀ c a b : GF4,
      codeOf (c • ![a, b]) = smulCode c.toNat (codeOf ![a, b]) := by decide
  have hw : w = ![w 0, w 1] := by funext i; fin_cases i <;> simp
  rw [hw]
  exact key c (w 0) (w 1)

theorem semilinear_of_code {M : ℕ → ℕ} (s : ℕ) (hs : s < 2)
    (hlt : ∀ n < 16, M n < 16)
    (h : ∀ c < 4, ∀ n < 16, M (smulCode c n) = smulCode (sigC s c) (M n)) (c : GF4)
    (w : Fin 2 → GF4) :
    wOfCode (M (codeOf (c • w))) = sigF s c • wOfCode (M (codeOf w)) := by
  have hc : c.toNat < 4 := c.val.isLt
  have hn : codeOf w < 16 := codeOf_lt w
  rw [codeOf_smul c w, h c.toNat hc (codeOf w) hn]
  rw [wOfCode_smulCode (sigC_lt hc) (hlt (codeOf w) hn), ofNat_sigC s c]

@[expose] def goodTriple (s v0 v1 : ℕ) : Bool :=
  ((List.range 16).map fun n => smulCode (sigC s (n % 4)) v0 ^^^ smulCode (sigC s (n / 4)) v1).Nodup

@[expose] def SemilinearOf (σ : GF4 ≃+* GF4) (γ : MulAut (Multiplicative (Fin 2 → GF4))) : Prop :=
  ∀ (c : GF4) (w : Fin 2 → GF4),
    γ (Multiplicative.ofAdd (c • w)) =
      Multiplicative.ofAdd (σ c • Multiplicative.toAdd (γ (Multiplicative.ofAdd w)))

lemma eq_smul_basis (w : Fin 2 → GF4) : w = w 0 • wOfCode 1 + w 1 • wOfCode 4 := by
  rw [wOfCode_one, wOfCode_four]
  funext i
  fin_cases i <;> simp

lemma semilinear_add {σ : GF4 ≃+* GF4} {γ : MulAut (Multiplicative (Fin 2 → GF4))}
    (h : SemilinearOf σ γ) (c d : GF4) (u v : Fin 2 → GF4) :
    γ (Multiplicative.ofAdd (c • u + d • v)) =
      Multiplicative.ofAdd (σ c • Multiplicative.toAdd (γ (Multiplicative.ofAdd u)) +
        σ d • Multiplicative.toAdd (γ (Multiplicative.ofAdd v))) := by
  rw [ofAdd_add, map_mul, h c u, h d v, ← ofAdd_add]

theorem mem_gammaLset2_iff (γ : MulAut (Multiplicative (Fin 2 → GF4))) :
    γ ∈ gammaLset 2 GF4 ↔ ∃ σ : GF4 ≃+* GF4, SemilinearOf σ γ := Iff.rfl

lemma gamma_code_injOn (γ : MulAut (Multiplicative (Fin 2 → GF4))) :
    Set.InjOn (fun n => codeOf (Multiplicative.toAdd (γ (Multiplicative.ofAdd (wOfCode n)))))
      {n : ℕ | n < 16} := by
  intro n hn m hm h
  have h1 : Multiplicative.toAdd (γ (Multiplicative.ofAdd (wOfCode n))) =
      Multiplicative.toAdd (γ (Multiplicative.ofAdd (wOfCode m))) := codeOf_injective h
  have h2 : γ (Multiplicative.ofAdd (wOfCode n)) = γ (Multiplicative.ofAdd (wOfCode m)) := by
    simpa using congrArg Multiplicative.ofAdd h1
  have h3 : Multiplicative.ofAdd (wOfCode n) = Multiplicative.ofAdd (wOfCode m) := γ.injective h2
  have h4 : wOfCode n = wOfCode m := by
    simpa using congrArg Multiplicative.toAdd h3
  exact wOfCode_injOn hn hm h4

lemma goodTriple_of_semilinear {s : ℕ} {γ : MulAut (Multiplicative (Fin 2 → GF4))}
    (hσ : SemilinearOf (sigE s) γ) {v0 v1 : ℕ} (hv0 : v0 < 16) (hv1 : v1 < 16)
    (h0 : γ (Multiplicative.ofAdd (wOfCode 1)) = Multiplicative.ofAdd (wOfCode v0))
    (h1 : γ (Multiplicative.ofAdd (wOfCode 4)) = Multiplicative.ofAdd (wOfCode v1)) :
    goodTriple s v0 v1 = true := by
  have formula : ∀ n < 16,
      codeOf (Multiplicative.toAdd (γ (Multiplicative.ofAdd (wOfCode n)))) =
        smulCode (sigC s (n % 4)) v0 ^^^ smulCode (sigC s (n / 4)) v1 := by
    intro n hn
    have hwn : wOfCode n = GF4.ofNat' n • wOfCode 1 + GF4.ofNat' (n / 4) • wOfCode 4 := by
      rw [eq_smul_basis (wOfCode n)]
      simp [wOfCode]
    have hsplit : Multiplicative.toAdd (γ (Multiplicative.ofAdd (wOfCode n))) =
        Multiplicative.toAdd (γ (Multiplicative.ofAdd (GF4.ofNat' n • wOfCode 1))) +
        Multiplicative.toAdd (γ (Multiplicative.ofAdd (GF4.ofNat' (n / 4) • wOfCode 4))) := by
      rw [hwn, ofAdd_add, map_mul, toAdd_mul]
    have hbase0 : ∀ c : GF4,
        Multiplicative.toAdd (γ (Multiplicative.ofAdd (c • wOfCode 1))) =
          sigE s c • wOfCode v0 := by
      intro c
      have hc := congrArg Multiplicative.toAdd (hσ c (wOfCode 1))
      simpa [h0] using hc
    have hbase1 : ∀ c : GF4,
        Multiplicative.toAdd (γ (Multiplicative.ofAdd (c • wOfCode 4))) =
          sigE s c • wOfCode v1 := by
      intro c
      have hc := congrArg Multiplicative.toAdd (hσ c (wOfCode 4))
      simpa [h1] using hc
    calc
      codeOf (Multiplicative.toAdd (γ (Multiplicative.ofAdd (wOfCode n))))
          = codeOf (Multiplicative.toAdd (γ (Multiplicative.ofAdd (GF4.ofNat' n • wOfCode 1))) +
                Multiplicative.toAdd
                  (γ (Multiplicative.ofAdd (GF4.ofNat' (n / 4) • wOfCode 4)))) := by
              rw [hsplit]
      _ = codeOf (Multiplicative.toAdd (γ (Multiplicative.ofAdd (GF4.ofNat' n • wOfCode 1)))) ^^^
            codeOf (Multiplicative.toAdd
              (γ (Multiplicative.ofAdd (GF4.ofNat' (n / 4) • wOfCode 4)))) :=
              codeOf_add _ _
      _ = codeOf (sigE s (GF4.ofNat' n) • wOfCode v0) ^^^
            codeOf (sigE s (GF4.ofNat' (n / 4)) • wOfCode v1) := by
              rw [hbase0, hbase1]
      _ = smulCode (sigC s (n % 4)) v0 ^^^ smulCode (sigC s (n / 4)) v1 := by
              rw [codeOf_smul, codeOf_smul, codeOf_wOfCode hv0, codeOf_wOfCode hv1]
              rw [sigE_toNat, sigE_toNat]
              simp only [GF4.toNat, GF4.ofNat', Fin.val_mk]
              rw [Nat.mod_eq_of_lt (show n / 4 < 4 by omega)]
  have hmap : (List.range 16).map
        (fun n => smulCode (sigC s (n % 4)) v0 ^^^ smulCode (sigC s (n / 4)) v1) =
      (List.range 16).map
        (fun n => codeOf (Multiplicative.toAdd (γ (Multiplicative.ofAdd (wOfCode n))))) := by
    apply List.map_congr_left
    intro n hn
    exact (formula n (List.mem_range.mp hn)).symm
  have hnodup : ((List.range 16).map
      (fun n => smulCode (sigC s (n % 4)) v0 ^^^ smulCode (sigC s (n / 4)) v1)).Nodup := by
    rw [hmap]
    exact List.Nodup.map_on
      (fun x hx y hy hxy => gamma_code_injOn γ (List.mem_range.mp hx) (List.mem_range.mp hy) hxy)
      List.nodup_range
  unfold goodTriple
  exact decide_eq_true hnodup

theorem eq_of_triple {σ : GF4 ≃+* GF4} {γ γ' : MulAut (Multiplicative (Fin 2 → GF4))}
    (h : SemilinearOf σ γ) (h' : SemilinearOf σ γ')
    (h0 : γ (Multiplicative.ofAdd (wOfCode 1)) = γ' (Multiplicative.ofAdd (wOfCode 1)))
    (h1 : γ (Multiplicative.ofAdd (wOfCode 4)) = γ' (Multiplicative.ofAdd (wOfCode 4))) :
    γ = γ' := by
  apply MulEquiv.ext
  intro x
  have key : ∀ w : Fin 2 → GF4,
      γ (Multiplicative.ofAdd w) = γ' (Multiplicative.ofAdd w) := by
    intro w
    rw [eq_smul_basis w]
    rw [semilinear_add h, semilinear_add h']
    rw [h0, h1]
  rw [← ofAdd_toAdd x]
  exact key (Multiplicative.toAdd x)

theorem exists_triple_of_mem_gammaLset {γ : MulAut (Multiplicative (Fin 2 → GF4))}
    (hγ : γ ∈ gammaLset 2 GF4) :
    ∃ s < 2, ∃ v0 < 16, ∃ v1 < 16, goodTriple s v0 v1 = true ∧
      γ (Multiplicative.ofAdd (wOfCode 1)) = Multiplicative.ofAdd (wOfCode v0) ∧
      γ (Multiplicative.ofAdd (wOfCode 4)) = Multiplicative.ofAdd (wOfCode v1) ∧
      SemilinearOf (sigE s) γ := by
  obtain ⟨σ, hσ⟩ := (mem_gammaLset2_iff γ).mp hγ
  set x0 : Fin 2 → GF4 := Multiplicative.toAdd (γ (Multiplicative.ofAdd (wOfCode 1))) with hx0
  set x1 : Fin 2 → GF4 := Multiplicative.toAdd (γ (Multiplicative.ofAdd (wOfCode 4))) with hx1
  have hv0 : codeOf x0 < 16 := codeOf_lt x0
  have hv1 : codeOf x1 < 16 := codeOf_lt x1
  have h0 : γ (Multiplicative.ofAdd (wOfCode 1)) =
      Multiplicative.ofAdd (wOfCode (codeOf x0)) := by
    rw [wOfCode_codeOf, hx0, ofAdd_toAdd]
  have h1 : γ (Multiplicative.ofAdd (wOfCode 4)) =
      Multiplicative.ofAdd (wOfCode (codeOf x1)) := by
    rw [wOfCode_codeOf, hx1, ofAdd_toAdd]
  rcases ringEquiv_gf4_cases σ with hrefl | hfrob
  · refine ⟨0, by norm_num, codeOf x0, hv0, codeOf x1, hv1, ?_, h0, h1, ?_⟩
    · exact goodTriple_of_semilinear (s := 0) (by simpa [sigE, hrefl] using hσ) hv0 hv1 h0 h1
    · simpa [sigE, hrefl] using hσ
  · refine ⟨1, by norm_num, codeOf x0, hv0, codeOf x1, hv1, ?_, h0, h1, ?_⟩
    · exact goodTriple_of_semilinear (s := 1) (by simpa [sigE, hfrob] using hσ) hv0 hv1 h0 h1
    · simpa [sigE, hfrob] using hσ

end CFSG.Quasithin.AppendixH.H14
