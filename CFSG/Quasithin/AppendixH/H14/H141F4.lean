module

public import CFSG.Quasithin.AppendixH.H14.H141Coord
public import CFSG.Quasithin.AppendixH.H14.H142F4

public section

namespace CFSG.Quasithin.AppendixH.H14

open CFSG.GH74.KGroups CFSG.ASVolI.ChH

@[expose] def codeOf3 (w : Fin 3 → GF4) : ℕ := (w 0).toNat + 4 * (w 1).toNat + 16 * (w 2).toNat

@[expose] def wOfCode3 (n : ℕ) : Fin 3 → GF4 :=
  ![GF4.ofNat' n, GF4.ofNat' (n / 4), GF4.ofNat' (n / 16)]

@[expose] def smulCode3 (c n : ℕ) : ℕ :=
  GF4.mulNat c (n % 4) + 4 * GF4.mulNat c (n / 4 % 4) + 16 * GF4.mulNat c (n / 16)

theorem codeOf3_lt (w : Fin 3 → GF4) : codeOf3 w < 64 := by
  have h0 := (w 0).val.isLt
  have h1 := (w 1).val.isLt
  have h2 := (w 2).val.isLt
  simp only [codeOf3, GF4.toNat]
  omega

theorem codeOf3_wOfCode3 {n : ℕ} (hn : n < 64) : codeOf3 (wOfCode3 n) = n := by
  have key : ∀ n : Fin 64, codeOf3 (wOfCode3 (n : ℕ)) = (n : ℕ) := by decide
  exact key ⟨n, hn⟩

theorem wOfCode3_codeOf3 (w : Fin 3 → GF4) : wOfCode3 (codeOf3 w) = w := by
  have key : ∀ a b c : GF4, wOfCode3 (codeOf3 ![a, b, c]) = ![a, b, c] := by decide
  have hw : w = ![w 0, w 1, w 2] := by funext i; fin_cases i <;> simp
  rw [hw]
  exact key (w 0) (w 1) (w 2)

theorem wOfCode3_zero : wOfCode3 0 = 0 := by
  decide

theorem codeOf3_injective : Function.Injective codeOf3 := by
  intro v w h
  rw [← wOfCode3_codeOf3 v, ← wOfCode3_codeOf3 w, h]

theorem wOfCode3_injOn : Set.InjOn wOfCode3 {n : ℕ | n < 64} := by
  intro n hn m hm h
  have h' := congrArg codeOf3 h
  rwa [codeOf3_wOfCode3 hn, codeOf3_wOfCode3 hm] at h'

theorem codeOf3_add (v w : Fin 3 → GF4) : codeOf3 (v + w) = codeOf3 v ^^^ codeOf3 w := by
  have key : ∀ a b c d e f : GF4,
      codeOf3 (![a, b, c] + ![d, e, f]) = codeOf3 ![a, b, c] ^^^ codeOf3 ![d, e, f] := by
    decide
  have hv : v = ![v 0, v 1, v 2] := by funext i; fin_cases i <;> simp
  have hw : w = ![w 0, w 1, w 2] := by funext i; fin_cases i <;> simp
  rw [hv, hw]
  exact key (v 0) (v 1) (v 2) (w 0) (w 1) (w 2)

theorem codeOf3_smul (c : GF4) (w : Fin 3 → GF4) :
    codeOf3 (c • w) = smulCode3 c.toNat (codeOf3 w) := by
  have key : ∀ c a b d : GF4,
      codeOf3 (c • ![a, b, d]) = smulCode3 c.toNat (codeOf3 ![a, b, d]) := by decide
  have hw : w = ![w 0, w 1, w 2] := by funext i; fin_cases i <;> simp
  rw [hw]
  exact key c (w 0) (w 1) (w 2)

theorem smulCode3_lt (c n : ℕ) (hc : c < 4) (hn : n < 64) : smulCode3 c n < 64 := by
  have key : ∀ c : Fin 4, ∀ n : Fin 64, smulCode3 (c : ℕ) (n : ℕ) < 64 := by decide
  exact key ⟨c, hc⟩ ⟨n, hn⟩

theorem wOfCode3_smulCode3 {d m : ℕ} (hd : d < 4) (hm : m < 64) :
    wOfCode3 (smulCode3 d m) = GF4.ofNat' d • wOfCode3 m := by
  have key : ∀ d : Fin 4, ∀ m : Fin 64,
      wOfCode3 (smulCode3 (d : ℕ) (m : ℕ)) = GF4.ofNat' (d : ℕ) • wOfCode3 (m : ℕ) := by
    decide
  exact key ⟨d, hd⟩ ⟨m, hm⟩

theorem wOfCode3_one : wOfCode3 1 = ![1, 0, 0] := by
  decide

theorem wOfCode3_four : wOfCode3 4 = ![0, 1, 0] := by
  decide

theorem wOfCode3_sixteen : wOfCode3 16 = ![0, 0, 1] := by
  decide

@[expose] def coordF4 : Coord64 (Multiplicative (Fin 3 → GF4)) where
  code w := codeOf3 (Multiplicative.toAdd w)
  ofCode n := Multiplicative.ofAdd (wOfCode3 n)
  code_lt w := codeOf3_lt _
  ofCode_code w := by
    show Multiplicative.ofAdd (wOfCode3 (codeOf3 (Multiplicative.toAdd w))) = w
    rw [wOfCode3_codeOf3, ofAdd_toAdd]
  code_ofCode n hn := by
    show codeOf3 (Multiplicative.toAdd (Multiplicative.ofAdd (wOfCode3 n))) = n
    rw [toAdd_ofAdd, codeOf3_wOfCode3 hn]
  code_mul a b := by
    show codeOf3 (Multiplicative.toAdd (a * b)) =
      codeOf3 (Multiplicative.toAdd a) ^^^ codeOf3 (Multiplicative.toAdd b)
    rw [toAdd_mul, codeOf3_add]

theorem semilinear3_of_code {M : ℕ → ℕ} (s : ℕ) (hs : s < 2)
    (hlt : ∀ n < 64, M n < 64)
    (h : ∀ c < 4, ∀ n < 64, M (smulCode3 c n) = smulCode3 (sigC s c) (M n)) (c : GF4)
    (w : Fin 3 → GF4) :
    wOfCode3 (M (codeOf3 (c • w))) = sigF s c • wOfCode3 (M (codeOf3 w)) := by
  have hc : c.toNat < 4 := c.val.isLt
  have hn : codeOf3 w < 64 := codeOf3_lt w
  rw [codeOf3_smul c w, h c.toNat hc (codeOf3 w) hn]
  rw [wOfCode3_smulCode3 (sigC_lt hc) (hlt (codeOf3 w) hn), ofNat_sigC s c]

@[expose] def SemilinearOf3 (σ : GF4 ≃+* GF4) (γ : MulAut (Multiplicative (Fin 3 → GF4))) : Prop :=
  ∀ (c : GF4) (w : Fin 3 → GF4),
    γ (Multiplicative.ofAdd (c • w)) =
      Multiplicative.ofAdd (σ c • Multiplicative.toAdd (γ (Multiplicative.ofAdd w)))

theorem mem_gammaLset3_iff (γ : MulAut (Multiplicative (Fin 3 → GF4))) :
    γ ∈ gammaLset 3 GF4 ↔ ∃ σ : GF4 ≃+* GF4, SemilinearOf3 σ γ := Iff.rfl

theorem eq_smul_basis3 (w : Fin 3 → GF4) :
    w = w 0 • wOfCode3 1 + w 1 • wOfCode3 4 + w 2 • wOfCode3 16 := by
  rw [wOfCode3_one, wOfCode3_four, wOfCode3_sixteen]
  funext i
  fin_cases i <;> simp

@[expose] def mKey (s v0 v1 v2 n : ℕ) : ℕ :=
  smulCode3 (sigC s (n % 4)) v0 ^^^ smulCode3 (sigC s (n / 4 % 4)) v1 ^^^
    smulCode3 (sigC s (n / 16)) v2

theorem code_apply_eq_mKey {s : ℕ} {γ : MulAut (Multiplicative (Fin 3 → GF4))}
    (hσ : SemilinearOf3 (sigE s) γ) {v0 v1 v2 : ℕ} (hv0 : v0 < 64) (hv1 : v1 < 64) (hv2 : v2 < 64)
    (h0 : γ (Multiplicative.ofAdd (wOfCode3 1)) = Multiplicative.ofAdd (wOfCode3 v0))
    (h1 : γ (Multiplicative.ofAdd (wOfCode3 4)) = Multiplicative.ofAdd (wOfCode3 v1))
    (h2 : γ (Multiplicative.ofAdd (wOfCode3 16)) = Multiplicative.ofAdd (wOfCode3 v2))
    {n : ℕ} (hn : n < 64) :
    codeOf3 (Multiplicative.toAdd (γ (Multiplicative.ofAdd (wOfCode3 n)))) = mKey s v0 v1 v2 n := by
  have hwn : wOfCode3 n = GF4.ofNat' n • wOfCode3 1 + GF4.ofNat' (n / 4) • wOfCode3 4 +
      GF4.ofNat' (n / 16) • wOfCode3 16 := by
    rw [eq_smul_basis3 (wOfCode3 n)]
    simp [wOfCode3]
  have hsplit : Multiplicative.toAdd (γ (Multiplicative.ofAdd (wOfCode3 n))) =
      Multiplicative.toAdd (γ (Multiplicative.ofAdd (GF4.ofNat' n • wOfCode3 1))) +
      Multiplicative.toAdd (γ (Multiplicative.ofAdd (GF4.ofNat' (n / 4) • wOfCode3 4))) +
      Multiplicative.toAdd (γ (Multiplicative.ofAdd (GF4.ofNat' (n / 16) • wOfCode3 16))) := by
    rw [hwn, ofAdd_add, ofAdd_add, map_mul, toAdd_mul, map_mul, toAdd_mul]
  have hbase0 : ∀ c : GF4,
      Multiplicative.toAdd (γ (Multiplicative.ofAdd (c • wOfCode3 1))) =
        sigE s c • wOfCode3 v0 := by
    intro c
    have hc := congrArg Multiplicative.toAdd (hσ c (wOfCode3 1))
    simpa [h0] using hc
  have hbase1 : ∀ c : GF4,
      Multiplicative.toAdd (γ (Multiplicative.ofAdd (c • wOfCode3 4))) =
        sigE s c • wOfCode3 v1 := by
    intro c
    have hc := congrArg Multiplicative.toAdd (hσ c (wOfCode3 4))
    simpa [h1] using hc
  have hbase2 : ∀ c : GF4,
      Multiplicative.toAdd (γ (Multiplicative.ofAdd (c • wOfCode3 16))) =
        sigE s c • wOfCode3 v2 := by
    intro c
    have hc := congrArg Multiplicative.toAdd (hσ c (wOfCode3 16))
    simpa [h2] using hc
  calc
    codeOf3 (Multiplicative.toAdd (γ (Multiplicative.ofAdd (wOfCode3 n))))
        = codeOf3 (Multiplicative.toAdd (γ (Multiplicative.ofAdd (GF4.ofNat' n • wOfCode3 1))) +
              Multiplicative.toAdd
                (γ (Multiplicative.ofAdd (GF4.ofNat' (n / 4) • wOfCode3 4))) +
              Multiplicative.toAdd
                (γ (Multiplicative.ofAdd (GF4.ofNat' (n / 16) • wOfCode3 16)))) := by
            rw [hsplit]
    _ = codeOf3 (Multiplicative.toAdd (γ (Multiplicative.ofAdd (GF4.ofNat' n • wOfCode3 1)))) ^^^
          codeOf3 (Multiplicative.toAdd
            (γ (Multiplicative.ofAdd (GF4.ofNat' (n / 4) • wOfCode3 4)))) ^^^
          codeOf3 (Multiplicative.toAdd
            (γ (Multiplicative.ofAdd (GF4.ofNat' (n / 16) • wOfCode3 16)))) := by
            rw [codeOf3_add, codeOf3_add]
    _ = codeOf3 (sigE s (GF4.ofNat' n) • wOfCode3 v0) ^^^
          codeOf3 (sigE s (GF4.ofNat' (n / 4)) • wOfCode3 v1) ^^^
          codeOf3 (sigE s (GF4.ofNat' (n / 16)) • wOfCode3 v2) := by
            rw [hbase0, hbase1, hbase2]
    _ = smulCode3 (sigC s (n % 4)) v0 ^^^ smulCode3 (sigC s (n / 4 % 4)) v1 ^^^
          smulCode3 (sigC s (n / 16)) v2 := by
            rw [codeOf3_smul, codeOf3_smul, codeOf3_smul, codeOf3_wOfCode3 hv0,
              codeOf3_wOfCode3 hv1, codeOf3_wOfCode3 hv2]
            rw [sigE_toNat, sigE_toNat, sigE_toNat]
            simp only [GF4.toNat, GF4.ofNat', Fin.val_mk]
            rw [Nat.mod_eq_of_lt (show n / 16 < 4 by omega)]

theorem exists_key3_of_mem_gammaLset {γ : MulAut (Multiplicative (Fin 3 → GF4))}
    (hγ : γ ∈ gammaLset 3 GF4) :
    ∃ s < 2, ∃ v0 < 64, ∃ v1 < 64, ∃ v2 < 64,
      γ (Multiplicative.ofAdd (wOfCode3 1)) = Multiplicative.ofAdd (wOfCode3 v0) ∧
      γ (Multiplicative.ofAdd (wOfCode3 4)) = Multiplicative.ofAdd (wOfCode3 v1) ∧
      γ (Multiplicative.ofAdd (wOfCode3 16)) = Multiplicative.ofAdd (wOfCode3 v2) ∧
      SemilinearOf3 (sigE s) γ := by
  obtain ⟨σ, hσ⟩ := (mem_gammaLset3_iff γ).mp hγ
  set x0 : Fin 3 → GF4 := Multiplicative.toAdd (γ (Multiplicative.ofAdd (wOfCode3 1))) with hx0
  set x1 : Fin 3 → GF4 := Multiplicative.toAdd (γ (Multiplicative.ofAdd (wOfCode3 4))) with hx1
  set x2 : Fin 3 → GF4 := Multiplicative.toAdd (γ (Multiplicative.ofAdd (wOfCode3 16))) with hx2
  have hv0 : codeOf3 x0 < 64 := codeOf3_lt x0
  have hv1 : codeOf3 x1 < 64 := codeOf3_lt x1
  have hv2 : codeOf3 x2 < 64 := codeOf3_lt x2
  have h0 : γ (Multiplicative.ofAdd (wOfCode3 1)) =
      Multiplicative.ofAdd (wOfCode3 (codeOf3 x0)) := by
    rw [wOfCode3_codeOf3, hx0, ofAdd_toAdd]
  have h1 : γ (Multiplicative.ofAdd (wOfCode3 4)) =
      Multiplicative.ofAdd (wOfCode3 (codeOf3 x1)) := by
    rw [wOfCode3_codeOf3, hx1, ofAdd_toAdd]
  have h2 : γ (Multiplicative.ofAdd (wOfCode3 16)) =
      Multiplicative.ofAdd (wOfCode3 (codeOf3 x2)) := by
    rw [wOfCode3_codeOf3, hx2, ofAdd_toAdd]
  rcases ringEquiv_gf4_cases σ with hrefl | hfrob
  · refine ⟨0, by norm_num, codeOf3 x0, hv0, codeOf3 x1, hv1, codeOf3 x2, hv2, h0, h1, h2, ?_⟩
    simpa [sigE, hrefl] using hσ
  · refine ⟨1, by norm_num, codeOf3 x0, hv0, codeOf3 x1, hv1, codeOf3 x2, hv2, h0, h1, h2, ?_⟩
    simpa [sigE, hfrob] using hσ

end CFSG.Quasithin.AppendixH.H14
