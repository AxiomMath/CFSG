
module


public import CFSG.Quasithin.H13.J4ClassesBase

public import CFSG.Quasithin.H13.J4ClassCheck
public import CFSG.Quasithin.H13.J4FixCount
public import CFSG.Sporadic.Schreier.J4SOrderBase1
public import CFSG.Quasithin.H13.J4Words
public import CFSG.Sporadic.Schreier.J4SNative
public import CFSG.Sporadic.Schreier.J4SCols
public import CFSG.Sporadic.Schreier.J4SOrbits
public meta import CFSG.Sporadic.Schreier.J4SOrbits
public import CFSG.Sporadic.J4.Local
public import CFSG.Quasithin.H13.J4ClassCheckInputs
public import Certificates.Data.CFSGNative.H13.J4Class
public import Certificates.Data.CFSGNative.H13.J4Elems
public import CFSG.Sporadic.Schreier.J4SKCent

@[expose] public noncomputable section


namespace CFSG.Quasithin.H13.J4Classes

open CFSG.Sporadic.J4 CFSG.Sporadic.J4Schreier CFSG.Sporadic.GLQ CFSG.Sporadic.SmallF2
  CFSG.Sporadic.SmallF2.Native
open CFSG.Quasithin.H13.J4 (xyPairs m2Cols ClsFacts e2Word imOK cls2_ok cls3_ok im2_ok im3_ok
  ker3_ok bounded_xy card_eq_card_image_mul uP vP dP tP e2P e3P cnjP conjEqP fusionChecks
  fusionChecks_eq lettersOK letters_uv)
open CFSG.Quasithin.H13.J4.Native (conjCols cmp11 colsBounded
  imCols uLetters vLetters)

theorem imOK_parts {C : Array ℕ} {L : List ℕ} (h : imOK C L = true) :
    (∀ β < 2048, (β ^^^ app11 C β) ∈ L) ∧ (∀ w ∈ L, w < 2048 ∧ ∃ β < 2048, β ^^^ app11 C β = w) ∧
      L.Nodup := by
  simp only [imOK, Bool.and_eq_true, List.all_eq_true, List.mem_range, List.contains_iff_mem,
    decide_eq_true_eq, List.any_eq_true, beq_iff_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  exact ⟨h1, fun w hw => ⟨(h2 w hw).1, (h2 w hw).2⟩, h3⟩

def e2 : J := signedWord x y e2Word ^ 6

theorem letters_ok_of {w : List ℤ} (h : lettersOK w = true) :
    ∀ l ∈ w, l = 1 ∨ l = -1 ∨ l = 2 ∨ l = -2 := by
  intro l hl
  simp only [lettersOK, List.all_eq_true, Bool.or_eq_true, beq_iff_eq] at h
  have := h l hl
  tauto

theorem η_one : η 1 = z := by
  have h := η_two_pow ⟨0, by norm_num⟩
  rw [pow_zero] at h
  exact h.trans u_zero

theorem conjOrbit_eq_of_mem' {L : Subgroup J} {m e : J} (h : m ∈ conjOrbit L e) :
    conjOrbit L m = conjOrbit L e := by
  obtain ⟨g, hg, rfl⟩ := h
  ext a
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k * g, L.mul_mem hk hg, by group⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k * g⁻¹, L.mul_mem hk (L.inv_mem hg), by group⟩

theorem self_mem_conjOrbit (L : Subgroup J) (e : J) : e ∈ conjOrbit L e :=
  ⟨1, L.one_mem, by group⟩

theorem conjOrbit_subset {L : Subgroup J} {e : J} (he : e ∈ L) : conjOrbit L e ⊆ L := by
  rintro _ ⟨k, hk, rfl⟩
  exact L.mul_mem (L.mul_mem hk he) (L.inv_mem hk)

theorem coe_conj_K (c : K) {k : J} (hk : k ∈ K) :
    ((c * ⟨k, hk⟩ * c⁻¹ : K) : J) = (c : J) * k * (c : J)⁻¹ := by
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]

theorem mem_conjOrbit_H_of_N {e s : J} (hs : s ∈ conjOrbit N e) : s ∈ conjOrbit H e := by
  obtain ⟨b, hb, rfl⟩ := hs
  exact ⟨b, N_le_H hb, rfl⟩

theorem conj_mem_conjOrbit {L : Subgroup J} {e x s : J} (hx : x ∈ L) (hs : s ∈ conjOrbit L e) :
    x * s * x⁻¹ ∈ conjOrbit L e := by
  obtain ⟨h, hh, rfl⟩ := hs
  exact ⟨x * h, L.mul_mem hx hh, by group⟩

def gxy (g : ℕ) : J := if g = 0 then x else y

theorem gxy_mem (g : ℕ) : gxy g ∈ K := by
  unfold gxy
  split_ifs
  · exact x_mem_K
  · exact y_mem_K

def e3 : J := η 1096 * x

theorem z_mem_H' : z ∈ H := z_mem_H

theorem e3_mem_H : e3 ∈ H := H.mul_mem (N_le_H (η_mem_N _)) x_mem_H

def vS : J := signedWord a b vLetters

theorem coe_letter_ab {l : ℤ} (hl : l = 1 ∨ l = -1 ∨ l = 2 ∨ l = -2) :
    ((letter a b l : J) : GL (Fin 112) (ZMod 2)) =
      if 0 < l then baseGL (l.toNat - 1) else (baseGL ((-l).toNat - 1))⁻¹ := by
  rcases hl with rfl | rfl | rfl | rfl <;> rfl

theorem coe_signedWord_ab (w : List ℤ) (hw : ∀ l ∈ w, l = 1 ∨ l = -1 ∨ l = 2 ∨ l = -2) :
    ((signedWord a b w : J) : GL (Fin 112) (ZMod 2)) = wordProd baseGL w := by
  induction w with
  | nil => simp [signedWord, wordProd]
  | cons l w ih =>
    have h1 := ih fun l' hl' => hw l' (List.mem_cons_of_mem _ hl')
    have h2 := coe_letter_ab (hw l (List.mem_cons_self ..))
    simp only [signedWord, wordProd, List.map_cons, List.prod_cons, Subgroup.coe_mul] at h1 ⊢
    rw [h1, h2]

theorem N_comm'
    {a b : J} (ha : a ∈ N) (hb : b ∈ N) : a * b = b * a := by
  obtain ⟨i, -, rfl⟩ := exists_η_eq ha
  obtain ⟨k, -, rfl⟩ := exists_η_eq hb
  rw [← η_xor, ← η_xor, Nat.xor_comm]

theorem conj_mem_N'
    {h n : J} (hh : h ∈ H) (hn : n ∈ N) : h * n * h⁻¹ ∈ N :=
  (Subgroup.mem_normalizer_iff.1 (H_le_normalizer hh) n).1 hn

theorem η_mul_self
    (a : ℕ) : η a * η a = 1 := by rw [← η_xor, Nat.xor_self, η_zero]

theorem η_inv
    (a : ℕ) : (η a)⁻¹ = η a := inv_eq_of_mul_eq_one_right (η_mul_self a)

theorem ρH_mul {x y : J} (hx : x ∈ H) (hy : y ∈ H) :
    ρH ⟨x * y, H.mul_mem hx hy⟩ = ρH ⟨x, hx⟩ * ρH ⟨y, hy⟩ := by
  rw [show (⟨x * y, H.mul_mem hx hy⟩ : H) = ⟨x, hx⟩ * ⟨y, hy⟩ from rfl, map_mul]

theorem ρH_inv
    {x : J} (hx : x ∈ H) : ρH ⟨x⁻¹, H.inv_mem hx⟩ = (ρH ⟨x, hx⟩)⁻¹ := by
  rw [show (⟨x⁻¹, H.inv_mem hx⟩ : H) = (⟨x, hx⟩ : H)⁻¹ from rfl, map_inv]

theorem ρH_conj {g s : J} (hg : g ∈ H) (hs : s ∈ H) :
    ρH ⟨g * s * g⁻¹, H.mul_mem (H.mul_mem hg hs) (H.inv_mem hg)⟩ =
      ρH ⟨g, hg⟩ * ρH ⟨s, hs⟩ * (ρH ⟨g, hg⟩)⁻¹ := by
  rw [ρH_mul (H.mul_mem hg hs) (H.inv_mem hg), ρH_mul hg hs, ρH_inv hg]

theorem ρH_of_mem_K
    {c : J} (hc : c ∈ K) : ρH ⟨c, K_le_H hc⟩ = ρK ⟨c, hc⟩ :=
  (ρK_eq ⟨c, hc⟩).symm

theorem ρH_conj_K' {k : J} (hk : k ∈ K) (c : K) :
    ρH ⟨c * k * (c : J)⁻¹, H.mul_mem (H.mul_mem (K_le_H c.2) (K_le_H hk))
        (H.inv_mem (K_le_H c.2))⟩ = ρK (c * ⟨k, hk⟩ * c⁻¹) := by
  rw [ρH_conj (K_le_H c.2) (K_le_H hk), ρH_of_mem_K c.2, ρH_of_mem_K hk, map_mul, map_mul,
    map_inv]

theorem actsBy_conj_mul
    {k : J} {C : Array ℕ} (hC : ActsBy k C) (β n₀ : ℕ) :
    η β * (η n₀ * k) * (η β)⁻¹ = η (n₀ ^^^ (β ^^^ app11 C β)) * k := by
  have h1 : k * (η β)⁻¹ = η (app11 C β) * k := by
    rw [η_inv]
    calc k * η β = k * η β * k⁻¹ * k := by group
      _ = η (app11 C β) * k := by rw [hC β]
  have h2 : η β * η n₀ = η n₀ * η β := N_comm' (η_mem_N _) (η_mem_N _)
  calc η β * (η n₀ * k) * (η β)⁻¹ = η β * η n₀ * (k * (η β)⁻¹) := by group
    _ = η n₀ * η β * (η (app11 C β) * k) := by rw [h1, h2]
    _ = η (n₀ ^^^ (β ^^^ app11 C β)) * k := by rw [η_xor, η_xor]; group

theorem ncard_conjOrbit_N
    {k : J} {C : Array ℕ} (hC : ActsBy k C) {n₀ : ℕ} (hn₀ : n₀ < 2048)
    {L : List ℕ} (hL : imOK C L = true) : (conjOrbit N (η n₀ * k)).ncard = L.length := by
  obtain ⟨h1, h2, h3⟩ := imOK_parts hL
  have e : conjOrbit N (η n₀ * k) = (fun w => η (n₀ ^^^ w) * k) '' {w | w ∈ L} := by
    ext m
    constructor
    · rintro ⟨b, hb, rfl⟩
      obtain ⟨β, hβ, rfl⟩ := exists_η_eq hb
      exact ⟨_, h1 β hβ, (actsBy_conj_mul hC β n₀).symm⟩
    · rintro ⟨w, hw, rfl⟩
      obtain ⟨-, β, -, rfl⟩ := h2 w hw
      exact ⟨η β, η_mem_N β, (actsBy_conj_mul hC β n₀).symm⟩
  have e' : {w | w ∈ L} = (L.toFinset : Set ℕ) := by
    ext w
    simp
  rw [e, Set.InjOn.ncard_image, e', Set.ncard_coe_finset, List.toFinset_card_of_nodup h3]
  intro w hw w' hw' hww
  have hww' : η (n₀ ^^^ w) * k = η (n₀ ^^^ w') * k := hww
  have hlt : ∀ w ∈ L, n₀ ^^^ w < 2 ^ 11 := fun w hw =>
    Nat.xor_lt_two_pow (by simpa using hn₀) (by simpa using (h2 w hw).1)
  have := η_injOn (hlt w hw) (hlt w' hw') (mul_right_cancel hww')
  have key : ∀ a, n₀ ^^^ (n₀ ^^^ a) = a := fun a => by
    rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
  rw [← key w, this, key]

theorem actsBy_x : ActsBy x xColumns := x_conj_η

theorem actsBy_x_inv : ActsBy x⁻¹ xInvColumns := fun a => by
  rw [inv_inv]; exact x_inv_conj_η a

theorem actsBy_y : ActsBy y yColumns := y_conj_η

theorem actsBy_y_inv : ActsBy y⁻¹ yInvColumns := fun a => by
  rw [inv_inv]; exact y_inv_conj_η a

theorem actsBy_gxy {g : ℕ} (hg : g < xyPairs.size) :
    ActsBy (gxy g) (xyPairs[g]!).1 ∧ ActsBy (gxy g)⁻¹ (xyPairs[g]!).2 := by
  have hg2 : g < 2 := hg
  obtain rfl | rfl : g = 0 ∨ g = 1 := by omega
  · exact ⟨actsBy_x, actsBy_x_inv⟩
  · exact ⟨actsBy_y, actsBy_y_inv⟩

theorem actsBy_conjCols
    {g m : J} {G G' B : Array ℕ} (hg : ActsBy g G) (hg' : ActsBy g⁻¹ G')
    (hm : ActsBy m B) : ActsBy (g * m * g⁻¹) (conjCols G G' B) :=
  actsBy_mul (actsBy_mul hg hm) hg'

theorem actsBy_e2
    : ActsBy e2 m2Cols := actsBy_pow 6 (word_conj_η_cols e2Word)

theorem ker3_parts
    : app11 xColumns 1096 = 1096 ∧ 1096 ∉ imCols xColumns ∧
    ∀ a < 2048, app11 xColumns a = a → a ∈ imCols xColumns ∨ (a ^^^ 1096) ∈ imCols xColumns :=
  ker3_ok

theorem uLetters_ok
    : ∀ l ∈ uLetters, l = 1 ∨ l = -1 ∨ l = 2 ∨ l = -2 :=
  letters_ok_of letters_uv.1

theorem vLetters_ok
    : ∀ l ∈ vLetters, l = 1 ∨ l = -1 ∨ l = 2 ∨ l = -2 :=
  letters_ok_of letters_uv.2

theorem fusion_parts : conjEqP (cnjP (mulP Bn An) Zn 3) Zn = true ∧
    conjEqP (cnjP (mulP An Bn) e2P 6) e2P = true ∧ conjEqP (cnjP oneP e3P 6) e3P = true := by
  have h := fusionChecks_eq
  simp only [fusionChecks, Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩


def uS : J := signedWord a b uLetters

def tS : J := (vS⁻¹ * uS * vS * uS) ^ 22

theorem tS_coe
    : (tS : GL (Fin 112) (ZMod 2)) = CFSG.Quasithin.H13.J4.t := by
  have hu : (uS : GL (Fin 112) (ZMod 2)) = CFSG.Quasithin.H13.J4.u := by
    rw [uS, coe_signedWord_ab _ uLetters_ok, CFSG.Quasithin.H13.J4.u_eq_wordProd]
  have hv : (vS : GL (Fin 112) (ZMod 2)) = CFSG.Quasithin.H13.J4.v := by
    rw [vS, coe_signedWord_ab _ vLetters_ok, CFSG.Quasithin.H13.J4.v_eq_wordProd]
  rw [tS, CFSG.Quasithin.H13.J4.t, CFSG.Quasithin.H13.J4.d, SubgroupClass.coe_pow,
    Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hu, hv]

theorem rep_tS : Rep Sp φ tS tP := by
  have hu := rep_wordP (rep_a matFacts) (rep_b matFacts) uLetters
  have hv := rep_wordP (rep_a matFacts) (rep_b matFacts) vLetters
  exact rep_powP (rep_mulP (rep_mulP (rep_mulP (rep_invP hv) hu) hv) hu) 22

theorem fusion_of_check
    {g e : J} {G E : Pair} (hg : Rep Sp φ g G) (he : Rep Sp φ e E) (k : ℕ)
    (h : conjEqP (cnjP G E k) E = true) : IsConj tS e := by
  have hc : Rep Sp φ (g * ((g⁻¹ * tS * g) * e) ^ k) (cnjP G E k) :=
    rep_mulP hg (rep_powP (rep_mulP (rep_mulP (rep_mulP (rep_invP hg) rep_tS) hg) he) k)
  have hct := rep_mulP (rep_mulP (rep_invP hc) rep_tS) hc
  have e1 := eq_of_rep hct he h
  refine isConj_iff.2 ⟨(g * ((g⁻¹ * tS * g) * e) ^ k)⁻¹, ?_⟩
  rw [inv_inv]
  exact e1

theorem isConj_tS_z : IsConj tS z :=
  fusion_of_check (rep_mulP (rep_b matFacts) (rep_a matFacts)) (rep_z matFacts) 3 fusion_parts.1

end CFSG.Quasithin.H13.J4Classes
