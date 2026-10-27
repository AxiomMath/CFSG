module

public import CFSG.Quasithin.H13.J4ClassesBase1

public import CFSG.Quasithin.H13.J4ClassCheck
public import CFSG.Quasithin.H13.J4FixCount
public import CFSG.Sporadic.Schreier.J4SOrder
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
public import CFSG.Sporadic.Schreier.J4SSylow

public noncomputable section

namespace CFSG.Quasithin.H13.J4Classes

open CFSG.Sporadic.J4 CFSG.Sporadic.J4Schreier CFSG.Sporadic.GLQ CFSG.Sporadic.SmallF2
  CFSG.Sporadic.SmallF2.Native
open CFSG.Quasithin.H13.J4 (xyPairs m2Cols ClsFacts e2Word imOK cls2_ok cls3_ok im2_ok im3_ok
  ker3_ok bounded_xy card_eq_card_image_mul uP vP dP tP e2P e3P cnjP conjEqP fusionChecks
  fusionChecks_eq lettersOK letters_uv)
open CFSG.Quasithin.H13.J4.Native (conjCols cmp11 colsBounded
  imCols uLetters vLetters)

theorem isConj_tS_e2 : IsConj tS e2 :=
  fusion_of_check (rep_mulP (rep_a matFacts) (rep_b matFacts))
    (rep_powP (rep_wordP (rep_x matFacts) (rep_y matFacts) e2Word) 6) 6 fusion_parts.2.1

theorem isConj_tS_e3 : IsConj tS e3 :=
  fusion_of_check rep_oneP (rep_mulP (rep_etaP matFacts 1096) (rep_x matFacts)) 6
    fusion_parts.2.2

theorem colsBounded_spec {C : Array ℕ} (h : colsBounded C = true) :
    C.size = 11 ∧ ∀ j < 11, C[j]! < 2048 := by
  simp only [colsBounded, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    decide_eq_true_eq] at h
  exact h

theorem app11_lt {C : Array ℕ} (h : colsBounded C = true) (a : ℕ) : app11 C a < 2048 := by
  have hb := colsBounded_spec h
  have := vecMulN_lt (d := 11) (R := C) (fun j hj => by
    rw [← getElem!_eq_getD']
    exact hb.2 j hj) a
  exact this

theorem fix_e3 :
    ∀ c ∈ K, c * x * c⁻¹ = x →
    ∃ b ∈ N, c * (η 1096 * x) * c⁻¹ = b * (η 1096 * x) * b⁻¹ := by
  intro c hc hcx
  obtain ⟨hk1, hk2, hk3⟩ := ker3_parts
  obtain ⟨i1, i2, -⟩ := imOK_parts im3_ok.1
  have hxb : colsBounded xColumns = true := bounded_xy.1
  have hcomm : c * x = x * c := by
    calc c * x = c * x * c⁻¹ * c := by group
      _ = x * c := by rw [hcx]
  obtain ⟨m, hm, hmη⟩ := exists_η_eq (conj_mem_N_of_mem_K hc (η_mem_N 1096))
  have hfix : app11 xColumns m = m := by
    have e : x * η m * x⁻¹ = η m := by
      rw [hmη]
      calc x * (c * η 1096 * c⁻¹) * x⁻¹ = c * (x * η 1096 * x⁻¹) * c⁻¹ := by
            calc x * (c * η 1096 * c⁻¹) * x⁻¹ = (x * c) * η 1096 * (x * c)⁻¹ := by group
              _ = (c * x) * η 1096 * (c * x)⁻¹ := by rw [hcomm]
              _ = c * (x * η 1096 * x⁻¹) * c⁻¹ := by group
        _ = c * η 1096 * c⁻¹ := by rw [x_conj_η, hk1]
    rw [x_conj_η] at e
    exact η_injOn (app11_lt hxb m) hm e
  have hnot : m ∉ imCols xColumns := by
    intro hmem
    obtain ⟨-, β, hβ, hβm⟩ := i2 m hmem
    obtain ⟨β', hβ', hβ'η⟩ := exists_η_eq (conj_mem_N_of_mem_K (K.inv_mem hc) (η_mem_N β))
    apply hk2
    have e1 : η 1096 = η (β' ^^^ app11 xColumns β') := by
      have hx' : c⁻¹ * x = x * c⁻¹ := by
        calc c⁻¹ * x = c⁻¹ * (x * c) * c⁻¹ := by group
          _ = c⁻¹ * (c * x) * c⁻¹ := by rw [hcomm]
          _ = x * c⁻¹ := by group
      have h1 : η 1096 = c⁻¹ * η m * c := by rw [hmη]; group
      rw [h1, ← hβm, η_xor, η_xor, ← x_conj_η, ← x_conj_η, hβ'η]
      calc c⁻¹ * (η β * (x * η β * x⁻¹)) * c =
            (c⁻¹ * η β * c⁻¹⁻¹) * ((c⁻¹ * x) * η β * (c⁻¹ * x)⁻¹ * c⁻¹⁻¹⁻¹ * c⁻¹⁻¹) := by group
        _ = (c⁻¹ * η β * c⁻¹⁻¹) * ((x * c⁻¹) * η β * (x * c⁻¹)⁻¹ * c⁻¹⁻¹⁻¹ * c⁻¹⁻¹) := by
            rw [hx']
        _ = (c⁻¹ * η β * c⁻¹⁻¹) * (x * (c⁻¹ * η β * c⁻¹⁻¹) * x⁻¹) := by group
    have e2 := η_injOn (by norm_num) (Nat.xor_lt_two_pow hβ' (app11_lt hxb β')) e1
    rw [e2]
    exact i1 β' hβ'
  have hmem : (m ^^^ 1096) ∈ imCols xColumns := (hk3 m hm hfix).resolve_left hnot
  obtain ⟨-, β, -, hβ⟩ := i2 _ hmem
  refine ⟨η β, η_mem_N β, ?_⟩
  rw [actsBy_conj_mul actsBy_x β 1096, hβ]
  have e : 1096 ^^^ (m ^^^ 1096) = m := by
    rw [Nat.xor_comm m, ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
  rw [e, hmη]
  calc c * (η 1096 * x) * c⁻¹ = c * η 1096 * c⁻¹ * (c * x * c⁻¹) := by group
    _ = c * η 1096 * c⁻¹ * x := by rw [hcx]

theorem e2_mem_K : e2 ∈ K := K.pow_mem (signedWord_mem_K _) _

theorem e2_mem_H : e2 ∈ H := K_le_H e2_mem_K

theorem ρH_of_mem_N
    {b : J} (hb : b ∈ N) : ρH ⟨b, N_le_H hb⟩ = 1 := by
  have h : (⟨b, N_le_H hb⟩ : H) ∈ ρH.ker := by
    rw [ker_ρH, Subgroup.mem_subgroupOf]
    exact hb
  exact h

theorem ρH_eq_iff
    {x y : J} (hx : x ∈ H) (hy : y ∈ H) :
    ρH ⟨x, hx⟩ = ρH ⟨y, hy⟩ ↔ x * y⁻¹ ∈ N := by
  rw [← mul_inv_eq_one, ← ρH_inv hy, ← ρH_mul hx (H.inv_mem hy), ← MonoidHom.mem_ker, ker_ρH,
    Subgroup.mem_subgroupOf]

theorem ρH_nk
    {b c : J} (hb : b ∈ N) (hc : c ∈ K) :
    ρH ⟨b * c, H.mul_mem (N_le_H hb) (K_le_H hc)⟩ = ρK ⟨c, hc⟩ := by
  rw [ρH_mul (N_le_H hb) (K_le_H hc), ρH_of_mem_N hb, one_mul, ρH_of_mem_K hc]

theorem ρH_class
    {n₀ k h : J} (hn₀ : n₀ ∈ N) (hk : k ∈ K) (hh : h ∈ H) :
    ∃ c : K, ρH ⟨h * (n₀ * k) * h⁻¹, H.mul_mem (H.mul_mem hh (H.mul_mem (N_le_H hn₀) (K_le_H hk)))
        (H.inv_mem hh)⟩ = ρK (c * ⟨k, hk⟩ * c⁻¹) ∧ ∃ b ∈ N, h = b * c := by
  obtain ⟨b, hb, c, hc, rfl⟩ := exists_mul_of_mem_H hh
  refine ⟨⟨c, hc⟩, ?_, b, hb, rfl⟩
  rw [ρH_conj hh (H.mul_mem (N_le_H hn₀) (K_le_H hk)), ρH_nk hb hc, ρH_nk hn₀ hk, map_mul,
    map_mul, map_inv]

theorem ρH_conj_K
    {n₀ k : J} (hn₀ : n₀ ∈ N) (hk : k ∈ K) (c : K) :
    ρH ⟨c * (n₀ * k) * (c : J)⁻¹, H.mul_mem (H.mul_mem (K_le_H c.2)
        (H.mul_mem (N_le_H hn₀) (K_le_H hk))) (H.inv_mem (K_le_H c.2))⟩ =
      ρK (c * ⟨k, hk⟩ * c⁻¹) := by
  rw [ρH_conj (K_le_H c.2) (H.mul_mem (N_le_H hn₀) (K_le_H hk)), ρH_of_mem_K c.2,
    ρH_nk hn₀ hk, map_mul, map_mul, map_inv]

theorem fiber_eq
    {n₀ k : J} (hn₀ : n₀ ∈ N) (hk : k ∈ K)
    (hfix : ∀ c ∈ K, c * k * c⁻¹ = k → ∃ b ∈ N, c * (n₀ * k) * c⁻¹ = b * (n₀ * k) * b⁻¹)
    {s : J} (hs : s ∈ conjOrbit H (n₀ * k)) :
    ρH ⟨s, conjOrbit_subset (H.mul_mem (N_le_H hn₀) (K_le_H hk)) hs⟩ = ρK ⟨k, hk⟩ ↔
      s ∈ conjOrbit N (n₀ * k) := by
  have he : n₀ * k ∈ H := H.mul_mem (N_le_H hn₀) (K_le_H hk)
  constructor
  · intro hsk
    obtain ⟨h, hh, rfl⟩ := hs
    obtain ⟨c, h1, b, hb, rfl⟩ := ρH_class hn₀ hk hh
    have hck' : c * ⟨k, hk⟩ * c⁻¹ = ⟨k, hk⟩ := ρK_injective (h1.symm.trans hsk)
    have hck : (c : J) * k * (c : J)⁻¹ = k := by
      rw [← coe_conj_K c hk, hck']
    obtain ⟨b', hb', hcb⟩ := hfix c c.2 hck
    refine ⟨b * b', N.mul_mem hb hb', ?_⟩
    calc b * c * (n₀ * k) * (b * c)⁻¹ = b * (c * (n₀ * k) * (c : J)⁻¹) * b⁻¹ := by group
      _ = b * (b' * (n₀ * k) * b'⁻¹) * b⁻¹ := by rw [hcb]
      _ = b * b' * (n₀ * k) * (b * b')⁻¹ := by group
  · rintro ⟨b, hb, rfl⟩
    rw [ρH_conj (N_le_H hb) he, ρH_of_mem_N hb, ρH_nk hn₀ hk, one_mul, inv_one, mul_one]

theorem card_fiber
    {n₀ k : J} (hn₀ : n₀ ∈ N) (hk : k ∈ K)
    (hfix : ∀ c ∈ K, c * k * c⁻¹ = k → ∃ b ∈ N, c * (n₀ * k) * c⁻¹ = b * (n₀ * k) * b⁻¹)
    (g : K) :
    Nat.card {a : conjOrbit H (n₀ * k) //
      ρH ⟨a.1, conjOrbit_subset (H.mul_mem (N_le_H hn₀) (K_le_H hk)) a.2⟩ =
        ρK (g * ⟨k, hk⟩ * g⁻¹)} = (conjOrbit N (n₀ * k)).ncard := by
  have he : n₀ * k ∈ H := H.mul_mem (N_le_H hn₀) (K_le_H hk)
  have hgH : (g : J) ∈ H := K_le_H g.2
  have hcK : ρK (g * ⟨k, hk⟩ * g⁻¹) = ρH ⟨g, hgH⟩ * ρK ⟨k, hk⟩ * (ρH ⟨g, hgH⟩)⁻¹ := by
    rw [ρH_of_mem_K g.2, map_mul, map_mul, map_inv]
  have hmem : ∀ a : conjOrbit H (n₀ * k), (g : J)⁻¹ * a.1 * g ∈ conjOrbit H (n₀ * k) := by
    intro a
    have := conj_mem_conjOrbit (H.inv_mem hgH) a.2
    rwa [inv_inv] at this
  have hval : ∀ a : conjOrbit H (n₀ * k),
      ρH ⟨a.1, conjOrbit_subset he a.2⟩ = ρK (g * ⟨k, hk⟩ * g⁻¹) →
        ρH ⟨(g : J)⁻¹ * a.1 * g, conjOrbit_subset he (hmem a)⟩ = ρK ⟨k, hk⟩ := by
    intro a ha
    rw [ρH_mul (H.mul_mem (H.inv_mem hgH) (conjOrbit_subset he a.2)) hgH,
      ρH_mul (H.inv_mem hgH) (conjOrbit_subset he a.2), ρH_inv hgH, ha, hcK]
    group
  rw [← Nat.card_coe_set_eq]
  exact Nat.card_congr
    { toFun := fun a => ⟨(g : J)⁻¹ * a.1.1 * g,
        (fiber_eq hn₀ hk hfix (hmem a.1)).1 (hval a.1 a.2)⟩
      invFun := fun s => ⟨⟨g * s.1 * (g : J)⁻¹, conj_mem_conjOrbit hgH
          (mem_conjOrbit_H_of_N s.2)⟩, by
        show ρH ⟨g * s.1 * (g : J)⁻¹, _⟩ = _
        rw [ρH_conj hgH (conjOrbit_subset he (mem_conjOrbit_H_of_N s.2)),
          (fiber_eq hn₀ hk hfix (mem_conjOrbit_H_of_N s.2)).2 s.2, hcK]⟩
      left_inv := fun a => by
        apply Subtype.ext
        apply Subtype.ext
        show (g : J) * ((g : J)⁻¹ * a.1.1 * g) * (g : J)⁻¹ = a.1.1
        group
      right_inv := fun s => by
        apply Subtype.ext
        show (g : J)⁻¹ * (g * s.1 * (g : J)⁻¹) * g = s.1
        group }

theorem ncard_conjOrbit_H
    {n₀ k : J} (hn₀ : n₀ ∈ N) (hk : k ∈ K)
    (hfix : ∀ c ∈ K, c * k * c⁻¹ = k → ∃ b ∈ N, c * (n₀ * k) * c⁻¹ = b * (n₀ * k) * b⁻¹) :
    (conjOrbit H (n₀ * k)).ncard = (conjOrbit K k).ncard * (conjOrbit N (n₀ * k)).ncard := by
  have he : n₀ * k ∈ H := H.mul_mem (N_le_H hn₀) (K_le_H hk)
  have hS : ∀ ψ, ψ ∈ (fun c : K => ρK (c * ⟨k, hk⟩ * c⁻¹)) '' Set.univ ↔
      ∃ a : conjOrbit H (n₀ * k), ρH ⟨a.1, conjOrbit_subset he a.2⟩ = ψ := by
    intro ψ
    constructor
    · rintro ⟨c, -, rfl⟩
      exact ⟨⟨c * (n₀ * k) * (c : J)⁻¹, c, K_le_H c.2, rfl⟩, ρH_conj_K hn₀ hk c⟩
    · rintro ⟨⟨_, h, hh, rfl⟩, rfl⟩
      obtain ⟨c, h1, -⟩ := ρH_class hn₀ hk hh
      exact ⟨c, Set.mem_univ _, h1.symm⟩
  have hm : ∀ ψ ∈ (fun c : K => ρK (c * ⟨k, hk⟩ * c⁻¹)) '' Set.univ,
      Nat.card {a : conjOrbit H (n₀ * k) // ρH ⟨a.1, conjOrbit_subset he a.2⟩ = ψ} =
        (conjOrbit N (n₀ * k)).ncard := by
    rintro _ ⟨g, -, rfl⟩
    exact card_fiber hn₀ hk hfix g
  have hfin : Finite (conjOrbit H (n₀ * k)) := Subtype.finite
  have h := card_eq_card_image_mul (fun a : conjOrbit H (n₀ * k) =>
    ρH ⟨a.1, conjOrbit_subset he a.2⟩) _ hS (conjOrbit N (n₀ * k)).ncard hm
  rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq] at h
  rw [h]
  congr 1
  symm
  refine Set.ncard_congr (fun m hm => ρH ⟨m, K_le_H (conjOrbit_subset hk hm)⟩) ?_ ?_ ?_
  · rintro _ ⟨g, hg, rfl⟩
    exact ⟨⟨g, hg⟩, Set.mem_univ _, (ρH_conj_K' hk ⟨g, hg⟩).symm⟩
  · intro m m' hm hm' hmm
    have h1 := (ρH_eq_iff _ _).1 hmm
    have h2 : m * m'⁻¹ ∈ K ⊓ N := Subgroup.mem_inf.2
      ⟨K.mul_mem (conjOrbit_subset hk hm) (K.inv_mem (conjOrbit_subset hk hm')), h1⟩
    rw [K_inf_N, Subgroup.mem_bot, mul_inv_eq_one] at h2
    exact h2
  · rintro _ ⟨c, -, rfl⟩
    exact ⟨c * k * (c : J)⁻¹, ⟨c, c.2, rfl⟩, ρH_conj_K' hk c⟩

theorem ncard_conjOrbit_K_of_clsFacts
    {k : J} (hk : k ∈ K) {M : Array ℕ} (hM : ActsBy k M)
    {n : ℕ} (hn : 0 < n) (h : ClsFacts xyPairs M n) :
    (conjOrbit K k).ncard = n := by
  obtain ⟨E, h0, hB, hD, hP, hC⟩ := h
  have hreach : ∀ i < n, ∃ c ∈ K, ActsBy (c * k * c⁻¹) (E i) := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi
      rcases Nat.eq_zero_or_pos i with rfl | hi0
      · exact ⟨1, K.one_mem, by rw [h0]; simpa using hM⟩
      · obtain ⟨p, hp, g, hg, he⟩ := hP i hi hi0
        obtain ⟨c, hc, hcA⟩ := ih _ hp (lt_trans hp hi)
        obtain ⟨h1, h2⟩ := actsBy_gxy hg
        refine ⟨gxy g * c, K.mul_mem (gxy_mem _) hc, ?_⟩
        rw [he]
        have := actsBy_conjCols h1 h2 hcA
        have e : gxy g * (c * k * c⁻¹) * (gxy g)⁻¹ = gxy g * c * k * (gxy g * c)⁻¹ := by group
        rw [e] at this
        exact this
  have hclosed : ∀ c ∈ K, ∀ m ∈ {m : J | ∃ i < n, ActsBy m (E i)},
      c * m * c⁻¹ ∈ {m : J | ∃ i < n, ActsBy m (E i)} := by
    refine conj_mem_of_inv_closed ?_ ?_
    · rintro m ⟨i, hi, hm⟩
      obtain ⟨j, hj, h4⟩ := hC i hi 0 (by decide)
      refine ⟨j, hj, ?_⟩
      rw [h4, inv_inv]
      have := actsBy_conjCols actsBy_x_inv (by rw [inv_inv]; exact actsBy_x) hm
      rw [inv_inv] at this
      exact this
    · rintro m ⟨i, hi, hm⟩
      obtain ⟨j, hj, h4⟩ := hC i hi 1 (by decide)
      refine ⟨j, hj, ?_⟩
      rw [h4, inv_inv]
      have := actsBy_conjCols actsBy_y_inv (by rw [inv_inv]; exact actsBy_y) hm
      rw [inv_inv] at this
      exact this
  have hbd : ∀ i < n, (E i).size = 11 ∧ ∀ j < 11, (E i)[j]! < 2048 :=
    fun i hi => colsBounded_spec (hB i hi)
  choose c hcK hcA using hreach
  let f : Fin n → J := fun i => c i i.2 * k * (c i i.2)⁻¹
  have hf : Function.Injective f := by
    intro i j hij
    have e : E i.val = E j.val := by
      have hi := hcA i i.2
      have hj := hcA j j.2
      change ActsBy (f i) _ at hi
      change ActsBy (f j) _ at hj
      rw [hij] at hi
      exact cols_eq_of_actsBy hi hj (hbd i i.2).1 (hbd j j.2).1 (hbd i i.2).2 (hbd j j.2).2
    rcases lt_trichotomy i.val j.val with hl | hl | hl
    · exact absurd e (hD j j.2 i hl)
    · exact Fin.ext hl
    · exact absurd e.symm (hD i i.2 j hl)
  have hrange : conjOrbit K k = Set.range f := by
    ext m
    constructor
    · rintro ⟨g, hg, rfl⟩
      obtain ⟨i, hi, hm⟩ := hclosed g hg k ⟨0, hn, by rw [h0]; exact hM⟩
      refine ⟨⟨i, hi⟩, ?_⟩
      exact eq_of_actsBy (K.mul_mem (K.mul_mem (hcK i hi) hk) (K.inv_mem (hcK i hi)))
        (K.mul_mem (K.mul_mem hg hk) (K.inv_mem hg)) (hcA i hi) hm
    · rintro ⟨i, rfl⟩
      exact ⟨c i i.2, hcK i i.2, rfl⟩
  rw [hrange, Set.ncard_range_of_injective hf, Nat.card_fin]

theorem conjOrbit_H_z
    : conjOrbit H z = conjOrbit K z := by
  ext m
  constructor
  · rintro ⟨h, hh, rfl⟩
    obtain ⟨n, hn, c, hc, rfl⟩ := exists_mul_of_mem_H hh
    refine ⟨c, hc, ?_⟩
    have hcz : c * z * c⁻¹ ∈ N := conj_mem_N_of_mem_K hc z_mem_N
    calc n * c * z * (n * c)⁻¹ = n * (c * z * c⁻¹) * n⁻¹ := by group
      _ = (c * z * c⁻¹) * n * n⁻¹ := by rw [N_comm' hn hcz]
      _ = c * z * c⁻¹ := by group
  · rintro ⟨c, hc, rfl⟩
    exact ⟨c, K_le_H hc, rfl⟩

theorem ncard_class_e1
    : (conjOrbit H z).ncard = 1771 := by
  rw [conjOrbit_H_z, ← η_one]
  exact QT_unique_J4_local_normal_module_irreducible.2.2.2.1

theorem ncard_class_e2
    : (conjOrbit H e2).ncard = 182160 := by
  have h := ncard_conjOrbit_H (n₀ := η 0) (k := e2) (η_mem_N 0) e2_mem_K (fun c _ hc =>
    ⟨1, N.one_mem, by rw [η_zero, one_mul, hc]; group⟩)
  rw [η_zero, one_mul] at h
  rw [h, ncard_conjOrbit_K_of_clsFacts e2_mem_K actsBy_e2 (by norm_num) cls2_ok]
  have := ncard_conjOrbit_N actsBy_e2 (n₀ := 0) (by norm_num) im2_ok.1
  rw [η_zero, one_mul, im2_ok.2] at this
  rw [this]

theorem ncard_class_e3
    : (conjOrbit H e3).ncard = 1020096 := by
  have h := ncard_conjOrbit_H (η_mem_N 1096) x_mem_K fix_e3
  rw [show e3 = η 1096 * x from rfl, h,
    ncard_conjOrbit_K_of_clsFacts x_mem_K actsBy_x (by norm_num) cls3_ok,
    ncard_conjOrbit_N actsBy_x (by norm_num) im3_ok.1, im3_ok.2]

end CFSG.Quasithin.H13.J4Classes
