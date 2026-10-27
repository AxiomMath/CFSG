module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporM24Data
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporBFS
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporHash
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.Sporadic.Schreier.Enumeration
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporM24CheckInputs
import Certificates.Kernel.LocalQT.Pairs.C4094c
import Certificates.Kernel.LocalQT.Pairs.C4094o
import Certificates.Kernel.LocalQT.Pairs.C4094k1
import Certificates.Kernel.LocalQT.Pairs.C4094k1h
import Certificates.Kernel.LocalQT.Pairs.C4094k2
import Certificates.Kernel.LocalQT.Pairs.C4094ti
import Certificates.Kernel.LocalQT.Pairs.C4094tt
import Certificates.Kernel.LocalQT.Pairs.C4094tn0
import Certificates.Kernel.LocalQT.Pairs.C4094tn1
import Certificates.Kernel.Sporadic.ON.Gen

set_option maxRecDepth 100000

public section

#kon_join CFSG.KD.LQT.C4094.k1all CFSG.KD.LQT.C4094.k1f 24
#kon_join CFSG.KD.LQT.C4094.k1hAll CFSG.KD.LQT.C4094.k1h 6
#kon_join CFSG.KD.LQT.C4094.k2fAll CFSG.KD.LQT.C4094.k2f 24
#kon_join CFSG.KD.LQT.C4094.k2hAll CFSG.KD.LQT.C4094.k2h 3
#kon_join CFSG.KD.LQT.C4094.ttAll CFSG.KD.LQT.C4094.tt 24
#kon_join CFSG.KD.LQT.C4094.tnAll CFSG.KD.LQT.C4094.tn 24
#kon_join CFSG.KD.LQT.C4094.tiAll CFSG.KD.LQT.C4094.ti 8
#kon_join CFSG.KD.LQT.C4094.clBAll CFSG.KD.LQT.C4094.clB 12

namespace CFSG.KD.LQT.C4094

open CFSG.KC.LQT.PH CFSG.KD.LQT.M24Chain CFSG.KD.LQT.M24K CFSG.KC.LQT.L
  CFSG.QuasithinUnique.Vol2Native.L239 CFSG.QuasithinUnique.Vol2Native.L239.M24Pairs
  CFSG.Sporadic.Mathieu CFSG.Sporadic.Schreier
open scoped Pointwise

private theorem cX_def (x : X24) : cX x = CFSG.KC.LQT.W.codeP x.1 := rfl

attribute [local irreducible] cX CFSG.KC.LQT.W.codeP CFSG.KC.LQT.P.mul CFSG.KC.LQT.P.inv
  CFSG.KC.LQT.P.one encK

private theorem tabX_eq' (x : X24) : tabX x = x := Subtype.ext (tab_eq x.1)

private theorem filter_map_code (L : List X24) (p : X24 → Bool) (q : ℕ → Bool)
    (hp : ∀ x, p x = q (cX x)) : (L.filter p).map cX = (L.map cX).filter q := by
  induction L with
  | nil => rfl
  | cons x L ih =>
    rw [List.filter_cons, List.map_cons, List.filter_cons, hp x]
    cases q (cX x)
    · simpa using ih
    · simpa using ih

private theorem map_code (L : List X24) (f : X24 → ℕ) (g : ℕ → ℕ) (h : ∀ q, f q = g (cX q)) :
    L.map f = (L.map cX).map g := by
  induction L with
  | nil => rfl
  | cons q L ih => rw [List.map_cons, List.map_cons, List.map_cons, h q, ih]

private theorem cnt_const (C : List Lvl) (hC : chainOK 24 C = true) (L : List X24) (hnd : L.Nodup)
    (hL : ∀ x, x ∈ L ↔ inC 24 C (chainF C) (cX x) = true)
    (hs : ∀ σ : Equiv.Perm (Fin 24), inC 24 C (chainF C) (CFSG.KC.LQT.W.codeP σ) = true →
      ∃ x ∈ L, cX x = CFSG.KC.LQT.W.codeP σ) (p : X24 → Bool) (pk : ℕ → Bool)
    (hp : ∀ x, p x = pk (cX x)) (cs : List ℕ) (m : ℕ) (hcs : cs = List.replicate 24 m)
    (hc : ∀ j < 24, Nat.beq (cntChunk 24 C pk j) m = true) : (L.filter p).length = cs.sum := by
  rw [hcs, chain_cnt C hC L hnd hL hs p pk hp _ List.length_replicate fun j hj => by
    rw [Nat.eq_of_beq_eq_true (hc j hj), List.getD_eq_getElem _ _ (by simpa using hj),
      List.getElem_replicate]]

private theorem beq_of_eq {a b : ℕ} (h : a = b) : Nat.beq a b = true := h ▸ Nat.beq_refl a

private theorem nodup_of_sincK {l : List ℕ}
    (h : CFSG.KC.LQT.T2.sincK (CFSG.KC.LQT.Syl.sortN l) = true) : l.Nodup :=
  (sortN_perm l).nodup_iff.1 (sincK_nodup h)

private theorem flat_nodup {s : ℕ} {B : List Blk} (h : sortedB s B = true) : (flatB B).Nodup :=
  sincK_nodup (andB_true.1 h).1

private theorem code_of_mem {Ps : List (Equiv.Perm (Fin 24))} {PC : List ℕ}
    (hPC : Ps.map CFSG.KC.LQT.W.codeP = PC) {c : ℕ} (hc : c ∈ PC) :
    ∃ σ : Equiv.Perm (Fin 24), CFSG.KC.LQT.W.codeP σ = c := by
  rw [← hPC, List.mem_map] at hc
  obtain ⟨σ, -, e⟩ := hc
  exact ⟨σ, e⟩

private theorem gx (w : List ℤ) : cX (genX w) = CFSG.KC.LQT.W.evalZK 24 GAB w := genX_code hA hB w

private theorem mapgx : ∀ ws : List (List ℤ),
    (ws.map genX).map cX = ws.map (CFSG.KC.LQT.W.evalZK 24 GAB)
  | [] => rfl
  | w :: ws => by rw [List.map_cons, List.map_cons, List.map_cons, gx, mapgx ws]

private theorem s0c : s0gen.map cX = S0G := by
  rw [s0gen, mapgx, hS0]

private theorem t1c : cX t1X = t1C := by
  rw [t1X, gx, ht1]

private theorem t3c : cX t3X = t3C := by
  rw [t3X, gx, ht3]

private theorem k1c : k1gen.map cX = K1G := by
  rw [k1gen, List.map_append, s0c, List.map_singleton, t1c]
  rfl

private theorem t0c : tgen.map cX = T0G := by
  rw [tgen, List.map_append, s0c, List.map_singleton, t3c]
  rfl

private theorem hS : S0X.Nodup ∧ S0X.length = chainF CS ∧
    (∀ x, (x ∈ S0X ↔ inC 24 CS (chainF CS) (cX x) = true) ∧
      (x ∈ S0X ↔ x ∈ Subgroup.closure {g | g ∈ s0gen})) ∧
    ∀ σ : Equiv.Perm (Fin 24), inC 24 CS (chainF CS) (CFSG.KC.LQT.W.codeP σ) = true →
      ∃ x ∈ S0X, cX x = CFSG.KC.LQT.W.codeP σ :=
  clH_sound s0gen (by rw [s0c]) 40 40 le_rfl CS WS kCS iCS gS
    (hk_radix CS kCS iCS 1 one_pos fun r hr => by
      interval_cases r
      exact hkS)

private theorem pA1_eq (x : X24) :
    (s0gen.all fun s => enc (s * x) == enc (x * s)) = pA1 (cX x) := by
  rw [all_codes (L := s0gen) (by rw [s0c]) _
    (fun c => Nat.beq (CFSG.KC.LQT.P.mul 24 c (cX x)) (CFSG.KC.LQT.P.mul 24 (cX x) c))]
  intro s
  rw [beq_enc, cX_mul, cX_mul]

private theorem hA1 : (A1X.map cX).Perm A1L := by
  rw [← eqL_eq kA1]
  exact (chain_col CS kCS S0X hS.1 (fun x => (hS.2.2.1 x).1) hS.2.2.2 _ pA1 pA1_eq).trans
    (sortN_perm _).symm

private theorem pZ2_eq (y : X24) :
    (s0gen.all fun s => (A1X.map enc).contains (enc (y * s * y⁻¹ * s⁻¹))) = pZ2 (cX y) := by
  rw [all_codes (L := s0gen) (by rw [s0c]) _ (fun c => CFSG.KC.LQT.S.memL
    (CFSG.KC.LQT.P.mul 24 (CFSG.KC.LQT.P.mul 24 (CFSG.KC.LQT.P.mul 24 (cX y) c)
      (CFSG.KC.LQT.P.inv 24 (cX y))) (CFSG.KC.LQT.P.inv 24 c)) A1L)]
  intro s
  rw [contains_enc hA1, cX_mul, cX_mul, cX_mul, cX_inv, cX_inv]

private theorem hZ2 : (Z2X.map cX).Perm Z2L := by
  rw [← eqL_eq kZ2]
  exact (chain_col CS kCS S0X hS.1 (fun x => (hS.2.2.1 x).1) hS.2.2.2 _ pZ2 pZ2_eq).trans
    (sortN_perm _).symm

private theorem pA2_eq (x : X24) : (Z2X.all fun y => enc (y * x) == enc (x * y)) = pA2 (cX x) := by
  rw [all_codes hZ2 _
    (fun c => Nat.beq (CFSG.KC.LQT.P.mul 24 c (cX x)) (CFSG.KC.LQT.P.mul 24 (cX x) c))]
  intro y
  rw [beq_enc, cX_mul, cX_mul]

private theorem hA2 : (A2X.map cX).Perm A2L := by
  rw [← eqL_eq kA2]
  exact (chain_col CS kCS S0X hS.1 (fun x => (hS.2.2.1 x).1) hS.2.2.2 _ pA2 pA2_eq).trans
    (sortN_perm _).symm

private theorem head_ne_one (L : List X24) (LC : List ℕ) (hL : (L.map cX).Perm LC) (c : ℕ)
    (p : X24 → Bool) (hp : ∀ x, p x = CFSG.KC.Ord.notB (Nat.beq (cX x) (CFSG.KC.LQT.P.one 24)))
    (h : CFSG.KC.LQT.S.filtL LC (fun c => CFSG.KC.Ord.notB (Nat.beq c (CFSG.KC.LQT.P.one 24))) =
      [c]) :
    cX ((L.filter p).headD 1) = c := by
  have e : (L.filter p).map cX = [c] := by
    rw [filter_map_code L p (fun c => CFSG.KC.Ord.notB (Nat.beq c (CFSG.KC.LQT.P.one 24))) hp]
    have h2 := hL.filter (fun c => CFSG.KC.Ord.notB (Nat.beq c (CFSG.KC.LQT.P.one 24)))
    exact List.perm_singleton.1 (h2.trans (List.Perm.of_eq ((filtL_eq _ _).symm.trans h)))
  exact head_code e

private theorem hz : cX zX = zC := by
  unfold zX
  refine head_ne_one A1X A1L hA1 zC _ (fun x => ?_) (eqL_eq kz)
  simp only [bne, beq_enc, cX_one, notB_eq]

private theorem one_A2X : (1 : X24) ∈ A2X := by
  refine List.mem_filter.2 ⟨(hS.2.2.1 1).2.2 (Subgroup.one_mem _), ?_⟩
  simp

private theorem A2X_nodup : A2X.Nodup := hS.1.filter _

private theorem A2X_len : A2X.length = 256 := by
  rw [← List.length_map (f := cX), hA2.length_eq]
  rfl

private theorem A2P_nodup : A2P.Nodup := nodup_of_sincK kA2Pd

private theorem ha2g : (a2gen.map cX).Perm A2P :=
  filter_perm_codes S0X hS.1 a2Perms hA2P A2P_nodup fun c hc => by
    obtain ⟨σ, rfl⟩ := code_of_mem hA2P hc
    exact hS.2.2.2 σ (andB_true.1 ((allL_iff _ _).1 kA2P _ hc)).1

private theorem hq1g : (q1gen.map cX).Perm Q1P :=
  filter_perm_codes S0X hS.1 q1Perms hQ1P (nodup_of_sincK kQ1Pd) fun c hc => by
    obtain ⟨σ, rfl⟩ := code_of_mem hQ1P hc
    exact hS.2.2.2 σ ((allL_iff _ _).1 kQ1P _ hc)

private theorem hA2c : A2cl.Nodup ∧ A2cl.length = chainF CA2 ∧
    (∀ x, (x ∈ A2cl ↔ inC 24 CA2 (chainF CA2) (cX x) = true) ∧
      (x ∈ A2cl ↔ x ∈ Subgroup.closure {g | g ∈ a2gen})) ∧
    ∀ σ : Equiv.Perm (Fin 24), inC 24 CA2 (chainF CA2) (CFSG.KC.LQT.W.codeP σ) = true →
      ∃ x ∈ A2cl, cX x = CFSG.KC.LQT.W.codeP σ :=
  clH_sound a2gen ha2g 40 40 le_rfl CA2 WA2 kCA2 iCA2 gA2
    (hk_radix CA2 kCA2 iCA2 1 one_pos fun r hr => by
      interval_cases r
      exact hkA2)

private theorem A2X_cl (x : X24) (hx : x ∈ A2X) : x ∈ A2cl :=
  ((hA2c.2.2.1 x).1).2 ((allL_iff _ _).1 kA2cl _ ((mem_codes hA2 x).1 hx))

private theorem A2X_iff (x : X24) : x ∈ A2X ↔ inC 24 CA2 (chainF CA2) (cX x) = true := by
  rw [← (hA2c.2.2.1 x).1]
  have hp : A2X.Perm A2cl := (List.subperm_of_subset A2X_nodup A2X_cl).perm_of_length_le
    (by rw [hA2c.2.1, lA2, A2X_len])
  exact hp.mem_iff

private theorem a_facts : A1X.length = 2 ∧ Z2X.length = 8 ∧ A2X.length = 256 ∧
    (∀ a ∈ a2gen, enc a ∈ A2X.map enc) ∧ (∀ y ∈ A2X, enc y ∈ A2cl.map enc) := by
  refine ⟨?_, ?_, A2X_len, fun a ha => ?_, fun y hy => List.mem_map_of_mem (A2X_cl y hy)⟩
  · rw [← List.length_map (f := cX), hA1.length_eq]
    rfl
  · rw [← List.length_map (f := cX), hZ2.length_eq]
    rfl
  · rw [mem_enc hA2, ← memL_iff]
    exact (andB_true.1 ((allL_iff _ _).1 kA2P _ ((mem_codes ha2g a).1 ha))).2

private theorem s0_facts : S0X.length = 1024 ∧
    strictAsc ((S0X.map enc).mergeSort (fun a b => decide (a ≤ b))) = true ∧ (1 : X24) ∈ S0X ∧
    (∀ x ∈ S0X, ∀ g ∈ s0gen, enc (x * g) ∈ S0X.map enc) ∧ (∀ x ∈ S0X, x ^ (2 ^ 10) = 1) := by
  refine ⟨hS.2.1.trans lS, strictAsc_enc hS.1, (hS.2.2.1 1).2.2 (Subgroup.one_mem _),
    fun x hx g hg => List.mem_map_of_mem ((hS.2.2.1 _).2.2 (Subgroup.mul_mem _
      ((hS.2.2.1 x).2.1 hx) (Subgroup.subset_closure hg))), fun x hx => ?_⟩
  have h := chain_allC CS kCS _ kSe x ((hS.2.2.1 x).1.1 hx)
  apply cX_injective
  rw [cX_sq, cX_one]
  exact Nat.eq_of_beq_eq_true h

private theorem hK1 : K1X.Nodup ∧ K1X.length = chainF CK1 ∧
    (∀ x, (x ∈ K1X ↔ inC 24 CK1 (chainF CK1) (cX x) = true) ∧
      (x ∈ K1X ↔ x ∈ Subgroup.closure {g | g ∈ k1gen})) ∧
    ∀ σ : Equiv.Perm (Fin 24), inC 24 CK1 (chainF CK1) (CFSG.KC.LQT.W.codeP σ) = true →
      ∃ x ∈ K1X, cX x = CFSG.KC.LQT.W.codeP σ :=
  clH_sound k1gen (by rw [k1c]) 60 60 le_rfl CK1 WK1 kCK1 iCK1
    (grpS_imp (by norm_num) kCK1 pK1 gK1)
    (hk_radix CK1 kCK1 iCK1 6 (by norm_num) k1hAll)

private theorem fK1_at {x : X24} (hx : x ∈ K1X) :
    Nat.beq (CFSG.KC.LQT.P.conj 24 (cX x) zC) zC = true ∧
      CFSG.KC.LQT.P.allL A1L (fun a => CFSG.KC.Ord.andB
        (CFSG.KC.LQT.S.memL (CFSG.KC.LQT.P.conj 24 (cX x) a) A1L)
        (CFSG.KC.LQT.S.memL (CFSG.KC.LQT.Pairs.conjI 24 (cX x) a) A1L)) = true ∧
      CFSG.KC.LQT.P.impB (CFSG.KC.LQT.P.allL Q1L fun q => CFSG.KC.LQT.P.comm 24 (cX x) q)
        (CFSG.KC.LQT.S.memL (cX x) Q1L) = true ∧
      CFSG.KC.LQT.P.impB (ord3 (cX x)) (fiveK (fun q => encK 24 (CFSG.KC.LQT.P.mul 24
        (CFSG.KC.LQT.P.conj 24 q (cX x)) (CFSG.KC.LQT.P.inv 24 (cX x)))) Q1L) = true := by
  have h := chain_all CK1 kCK1 fK1 k1all x ((hK1.2.2.1 x).1.1 hx)
  obtain ⟨h1, h2⟩ := andB_true.1 h
  obtain ⟨h2, h3⟩ := andB_true.1 h2
  obtain ⟨h3, h4⟩ := andB_true.1 h3
  exact ⟨h1, h2, h3, h4⟩

private theorem k1_facts : K1X.length = 21504 ∧
    strictAsc ((K1X.map enc).mergeSort (fun a b => decide (a ≤ b))) = true ∧
    (∀ x ∈ K1X, enc (x * zX * x⁻¹) = enc zX) ∧
    (∀ x ∈ K1X, ∀ a ∈ A1X, enc (x * a * x⁻¹) ∈ A1X.map enc ∧ enc (x⁻¹ * a * x) ∈ A1X.map enc) ∧
    zX ≠ 1 ∧ (∀ a ∈ A1X, enc a = enc 1 ∨ enc a = enc zX) ∧ enc zX ∈ A1X.map enc := by
  refine ⟨hK1.2.1.trans lK1, strictAsc_enc hK1.1, fun x hx => ?_, fun x hx a ha => ?_, fun h => ?_,
    fun a ha => ?_, (mem_enc hA1 zX).2 (by rw [hz]; exact (memL_iff _ _).1 kzA1)⟩
  · congr 1
    apply cX_injective
    rw [cX_mul, cX_mul, cX_inv, hz]
    exact Nat.eq_of_beq_eq_true (fK1_at hx).1
  · have h := andB_true.1 ((allL_iff _ _).1 (fK1_at hx).2.1 _ ((mem_codes hA1 a).1 ha))
    constructor
    · rw [mem_enc hA1, cX_mul, cX_mul, cX_inv, ← memL_iff]
      exact h.1
    · rw [mem_enc hA1, cX_mul, cX_mul, cX_inv, ← memL_iff]
      exact h.2
  · have e := congrArg cX h
    rw [hz, cX_one] at e
    have k := kz1
    rw [e, Nat.beq_refl] at k
    exact absurd k (by decide)
  · have h := (orB_true.1 ((allL_iff _ _).1 kA1z _ ((mem_codes hA1 a).1 ha)))
    rcases h with h | h
    · left
      rw [← cX_one] at h
      rw [cX_injective (Nat.eq_of_beq_eq_true h)]
    · right
      rw [← hz] at h
      rw [cX_injective (Nat.eq_of_beq_eq_true h)]

private theorem hQ1 : Q1X.Nodup ∧ Q1X.length = chainF CQ1 ∧
    (∀ x, (x ∈ Q1X ↔ inC 24 CQ1 (chainF CQ1) (cX x) = true) ∧
      (x ∈ Q1X ↔ x ∈ Subgroup.closure {g | g ∈ q1gen})) ∧
    ∀ σ : Equiv.Perm (Fin 24), inC 24 CQ1 (chainF CQ1) (CFSG.KC.LQT.W.codeP σ) = true →
      ∃ x ∈ Q1X, cX x = CFSG.KC.LQT.W.codeP σ :=
  clH_sound q1gen hq1g 40 40 le_rfl CQ1 WQ1 kCQ1 iCQ1 gQ1
    (hk_radix CQ1 kCQ1 iCQ1 1 one_pos fun r hr => by
      interval_cases r
      exact hkQ1)

private theorem hQ1L : (Q1X.map cX).Perm Q1L := by
  have h := chain_col CQ1 kCQ1 Q1X hQ1.1 (fun x => (hQ1.2.2.1 x).1) hQ1.2.2.2 (fun _ => true)
    (fun _ => true) fun _ => rfl
  rw [List.filter_true] at h
  rw [← eqL_eq kQ1L]
  exact h.trans (sortN_perm _).symm

private theorem five_of {L : List X24} {LC : List ℕ} (hL : (L.map cX).Perm LC) (b : X24)
    (h : fiveK (fun q => encK 24 (CFSG.KC.LQT.P.mul 24 (CFSG.KC.LQT.P.conj 24 q (cX b))
      (CFSG.KC.LQT.P.inv 24 (cX b)))) LC = true) :
    4 < ((L.map fun q => enc (q * b * q⁻¹ * b⁻¹)).dedup).length := by
  have e : (L.map fun q => enc (q * b * q⁻¹ * b⁻¹)) = (L.map cX).map (fun q => encK 24
      (CFSG.KC.LQT.P.mul 24 (CFSG.KC.LQT.P.conj 24 q (cX b)) (CFSG.KC.LQT.P.inv 24 (cX b)))) :=
    map_code L _ _ fun q => by rw [enc_code, cX_mul, cX_mul, cX_mul, cX_inv, cX_inv]; rfl
  rw [e, ((hL.map _).dedup).length_eq]
  exact fiveK_sound _ _ h

private theorem ord3_of {b : X24} (h1 : b ≠ 1) (h3 : b ^ 3 = 1) : ord3 (cX b) = true := by
  refine andB_true.2 ⟨?_, ?_⟩
  · rw [notB_eq, ← cX_one, beq_code]
    simpa using h1
  · rw [← cX_pow, h3, cX_one]
    exact Nat.beq_refl _

private theorem q1_facts : Q1X.length = 128 ∧
    strictAsc ((Q1X.map enc).mergeSort (fun a b => decide (a ≤ b))) = true ∧
    (∀ q ∈ Q1X, enc q ∈ K1X.map enc) ∧ (1 : X24) ∈ Q1X ∧
    (∀ p ∈ Q1X, ∀ q ∈ Q1X, enc (p * q) ∈ Q1X.map enc) ∧
    (∀ k ∈ k1gen, ∀ q ∈ Q1X,
      enc (k * q * k⁻¹) ∈ Q1X.map enc ∧ enc (k⁻¹ * q * k) ∈ Q1X.map enc) ∧
    (∀ q ∈ Q1X, q ^ (2 ^ 4) = 1) ∧
    (∀ y ∈ K1X, (∀ q ∈ Q1X, enc (y * q) = enc (q * y)) → enc y ∈ Q1X.map enc) ∧
    (∀ b ∈ K1X, b ≠ 1 → b ^ 3 = 1 →
      4 < ((Q1X.map fun q => enc (q * b * q⁻¹ * b⁻¹)).dedup).length) ∧
    K1X.length / Q1X.length = 168 := by
  have mQ : ∀ x, x ∈ Q1X ↔ x ∈ Subgroup.closure {g | g ∈ q1gen} := fun x => (hQ1.2.2.1 x).2
  refine ⟨hQ1.2.1.trans lQ1, strictAsc_enc hQ1.1, fun q hq => List.mem_map_of_mem
    ((hK1.2.2.1 q).1.2 ((allL_iff _ _).1 kQ1K _ ((mem_codes hQ1L q).1 hq))),
    (mQ 1).2 (Subgroup.one_mem _), fun p hp q hq => List.mem_map_of_mem
      ((mQ _).2 (Subgroup.mul_mem _ ((mQ p).1 hp) ((mQ q).1 hq))), fun k hk q hq => ?_,
    fun q hq => ?_, fun y hy hc => ?_, fun b hb h1 h3 => ?_, ?_⟩
  · have hkc : cX k ∈ K1G := by
      rw [← k1c]
      exact List.mem_map_of_mem hk
    have h := andB_true.1 ((allL_iff _ _).1 ((allL_iff _ _).1 kQ1n _ ((mem_codes hQ1L q).1 hq))
      _ hkc)
    constructor
    · refine List.mem_map_of_mem ((hQ1.2.2.1 _).1.2 ?_)
      rw [cX_mul, cX_mul, cX_inv]
      exact h.1
    · refine List.mem_map_of_mem ((hQ1.2.2.1 _).1.2 ?_)
      rw [cX_mul, cX_mul, cX_inv]
      exact h.2
  · apply cX_injective
    rw [cX_sq, cX_one]
    exact Nat.eq_of_beq_eq_true ((allL_iff _ _).1 kQ1e _ ((mem_codes hQ1L q).1 hq))
  · rw [mem_enc hQ1L, ← memL_iff]
    refine impB_true (fK1_at hy).2.2.1 ((allL_iff _ _).2 fun c hcm => ?_)
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 (hQ1L.mem_iff.2 hcm)
    have e : y * q = q * y := enc_injective' (hc q hq)
    change Nat.beq (CFSG.KC.LQT.P.mul 24 (cX y) (cX q)) (CFSG.KC.LQT.P.mul 24 (cX q) (cX y)) = true
    exact beq_of_eq (by rw [← cX_mul, ← cX_mul, e])
  · exact five_of hQ1L b (impB_true (fK1_at hb).2.2.2 (ord3_of h1 h3))
  · rw [hK1.2.1, lK1, hQ1.2.1, lQ1]

private theorem class_facts : Reach gensC zX classRes.1 classRes.2.1 classRes.2.2 ∧
    classRes.1.length = 11385 ∧
    strictAsc ((classRes.1.map enc).mergeSort (fun a b => decide (a ≤ b))) = true := by
  have hN := Nat.eq_of_beq_eq_true cN
  have hc : (classRes.1.map cX).Perm (flatB CFSG.KD.LQT.M24Class.B) :=
    class_sound zX 20000 hA hB hz 128 12 3 CFSG.KD.LQT.M24Class.B CFSG.KD.LQT.M24Class.T cS
    cZ clBAll
    (by rw [Nat.eq_of_beq_eq_true cK]; norm_num) (by norm_num) (fun r hr => by
      interval_cases r
      exacts [ch0, ch1, ch2]) (by rw [hN]; norm_num)
  refine ⟨reach_bfsOrbit tabX tabX_eq' hkey gensC zX 20000, ?_, ?_⟩
  · rw [← List.length_map (f := cX), hc.length_eq, ← lenL_eq, hN]
  · exact strictAsc_enc ((hc.nodup_iff.2 (flat_nodup cS)).of_map cX)

private theorem trio_eq : trio = ((List.finRange 24).map (orbL A2X)).toFinset := rfl

private theorem trio_code' : encTrioN trio = tC := (trio_code A2X hA2 kts).trans kt

private theorem trio_ne : (∅ : Finset (Fin 24)) ∉ trio := by
  intro h
  rw [trio_eq, List.mem_toFinset, List.mem_map] at h
  obtain ⟨i, -, hi⟩ := h
  have hm : i ∈ orbL A2X i := by
    rw [orbL, List.mem_toFinset, List.mem_map]
    exact ⟨1, one_A2X, rfl⟩
  rw [hi] at hm
  exact absurd hm (Finset.notMem_empty i)

private theorem trio_card : trio.card ≤ 24 := by
  rw [trio_eq]
  exact (List.toFinset_card_le _).trans (by simp)

private theorem trio_facts : Reach gensA trio trioRes.1 trioRes.2.1 trioRes.2.2 ∧
    trioRes.1.length = 3795 ∧
    strictAsc ((trioRes.1.map encTrioN).mergeSort (fun a b => decide (a ≤ b))) = true := by
  have hN := Nat.eq_of_beq_eq_true oN
  have ht : (trioRes.1.map encTrioN).Perm (flatB CFSG.KD.LQT.M24Trio.B) :=
    trio_sound trio 10000 hA hB trio_code' trio_ne trio_card 128 4 CFSG.KD.LQT.M24Trio.B
    CFSG.KD.LQT.M24Trio.T oS oZ (fun k hk => by
      interval_cases k
      exacts [ob0, ob1, ob2, ob3])
    (by rw [Nat.eq_of_beq_eq_true oK]; norm_num) (by rw [hN]; norm_num)
  refine ⟨reach_bfsOrbit id (fun _ => rfl) encTrio gensA trio 10000, ?_, ?_⟩
  · rw [← List.length_map (f := encTrioN), ht.length_eq, ← lenL_eq, hN]
  · exact strictAsc_nat (ht.nodup_iff.2 (flat_nodup oS))

private theorem hT0 : T0X.Nodup ∧ T0X.length = chainF CT0 ∧
    (∀ x, (x ∈ T0X ↔ inC 24 CT0 (chainF CT0) (cX x) = true) ∧
      (x ∈ T0X ↔ x ∈ Subgroup.closure {g | g ∈ tgen})) ∧
    ∀ σ : Equiv.Perm (Fin 24), inC 24 CT0 (chainF CT0) (CFSG.KC.LQT.W.codeP σ) = true →
      ∃ x ∈ T0X, cX x = CFSG.KC.LQT.W.codeP σ :=
  clH_sound tgen (by rw [t0c]) 60 60 le_rfl CT0 WT0 kCT0 iCT0
    (grpS_imp (by norm_num) kCT0 pT0 gT0)
    (hk_data CT0 kCT0 iCT0 CFSG.KD.LQT.M24Idx.I 8 (by rw [Nat.eq_of_beq_eq_true tiN, lT0]) rfl
      tiAll)

private theorem pN_eq (x : X24) : nrmTestGens enc (A2X.map enc) a2gen x = pN (cX x) := by
  rw [nrmTestGens, all_codes ha2g _
    (fun c => CFSG.KC.LQT.S.memL (CFSG.KC.LQT.P.conj 24 (cX x) c) A2L)]
  intro a
  rw [decide_enc hA2, cX_mul, cX_mul, cX_inv]
  rfl

private theorem t0_facts : T0X.length = 64512 ∧
    strictAsc ((T0X.map enc).mergeSort (fun a b => decide (a ≤ b))) = true ∧
    (∀ x ∈ T0X, x • trio = trio) ∧ T0N.length = 9216 := by
  refine ⟨hT0.2.1.trans lT0, strictAsc_enc hT0.1, fun x hx => ?_, ?_⟩
  · refine trio_fix x trio trio_ne trio_card ?_
    rw [trio_code']
    exact Nat.eq_of_beq_eq_true (chain_all CT0 kCT0 fT ttAll x ((hT0.2.2.1 x).1.1 hx))
  · have hc : ∀ j < 24, Nat.beq (cntChunk 24 CT0 pN j) 384 = true := tnAll
    exact (cnt_const CT0 kCT0 T0X hT0.1 (fun x => (hT0.2.2.1 x).1) hT0.2.2.2 _ pN pN_eq nT0 384
      rfl hc).trans (by decide +kernel)

private theorem ht2X : cX t2X = t2C := by
  obtain ⟨w, hw, hwc⟩ := hT0.2.2.2 (t2Perm.headD 1) (by rw [ht2]; exact kt2)
  replace hwc := hwc.trans ht2
  have key : ∀ x : X24, (enc x == encPerm (t2Perm.headD 1)) = true ↔ cX x = t2C := by
    intro x
    rw [beq_iff_eq, ← ht2, cX_def]
    exact ⟨fun e => congrArg CFSG.KC.LQT.W.codeP (encPerm_injective (by norm_num) e),
      fun e => congrArg encPerm (codeP_injective e)⟩
  refine head_code (list_single ((hT0.1.filter _).map cX_injective) (fun c hc => ?_)
    (List.mem_map.2 ⟨w, List.mem_filter.2 ⟨hw, (key w).2 hwc⟩, hwc⟩))
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hc
  exact (key x).1 (List.mem_filter.1 hx).2

private theorem k2c : k2gen.map cX = K2G := by
  rw [k2gen, List.map_append, s0c, List.map_singleton, ht2X]
  rfl

private theorem hK2 : K2X.Nodup ∧ K2X.length = chainF CK2 ∧
    (∀ x, (x ∈ K2X ↔ inC 24 CK2 (chainF CK2) (cX x) = true) ∧
      (x ∈ K2X ↔ x ∈ Subgroup.closure {g | g ∈ k2gen})) ∧
    ∀ σ : Equiv.Perm (Fin 24), inC 24 CK2 (chainF CK2) (CFSG.KC.LQT.W.codeP σ) = true →
      ∃ x ∈ K2X, cX x = CFSG.KC.LQT.W.codeP σ :=
  clH_sound k2gen (by rw [k2c]) 60 60 le_rfl CK2 WK2 kCK2 iCK2
    (grpS_imp (by norm_num) kCK2 pK2 gK2)
    (hk_radix CK2 kCK2 iCK2 3 (by norm_num) k2hAll)

private theorem fK2_at {x : X24} (hx : x ∈ K2X) :
    pN (cX x) = true ∧
      CFSG.KC.LQT.P.impB (CFSG.KC.LQT.P.allL A2L fun q => CFSG.KC.LQT.P.comm 24 (cX x) q)
        (CFSG.KC.LQT.S.memL (cX x) A2L) = true ∧
      CFSG.KC.LQT.P.impB (ord3 (cX x)) (fiveK (fun q => encK 24 (CFSG.KC.LQT.P.mul 24
        (CFSG.KC.LQT.P.conj 24 q (cX x)) (CFSG.KC.LQT.P.inv 24 (cX x)))) A2L) = true := by
  have h := chain_all CK2 kCK2 fK2 k2fAll x ((hK2.2.2.1 x).1.1 hx)
  obtain ⟨h1, h2⟩ := andB_true.1 h
  obtain ⟨h2, h3⟩ := andB_true.1 h2
  exact ⟨h1, h2, h3⟩

private theorem k2_facts : K2X.length = 9216 ∧
    strictAsc ((K2X.map enc).mergeSort (fun a b => decide (a ≤ b))) = true ∧
    (∀ x ∈ K2X, nrmTestGens enc (A2X.map enc) a2gen x = true) :=
  ⟨hK2.2.1.trans lK2, strictAsc_enc hK2.1, fun x hx => by rw [pN_eq]; exact (fK2_at hx).1⟩

private theorem q2_facts :
    strictAsc ((A2X.map enc).mergeSort (fun a b => decide (a ≤ b))) = true ∧
    (∀ q ∈ A2X, enc q ∈ K2X.map enc) ∧ (1 : X24) ∈ A2X ∧
    (∀ p ∈ A2X, ∀ q ∈ A2X, enc (p * q) ∈ A2X.map enc) ∧
    (∀ k ∈ k2gen, ∀ q ∈ A2X,
      enc (k * q * k⁻¹) ∈ A2X.map enc ∧ enc (k⁻¹ * q * k) ∈ A2X.map enc) ∧
    (∀ q ∈ A2X, q ^ (2 ^ 4) = 1) ∧
    (∀ y ∈ K2X, (∀ q ∈ A2X, enc (y * q) = enc (q * y)) → enc y ∈ A2X.map enc) ∧
    (∀ b ∈ K2X, b ≠ 1 → b ^ 3 = 1 →
      4 < ((A2X.map fun q => enc (q * b * q⁻¹ * b⁻¹)).dedup).length) ∧
    K2X.length / A2X.length = 36 := by
  have mA : ∀ x, x ∈ A2X ↔ x ∈ Subgroup.closure {g | g ∈ a2gen} := fun x =>
    (A2X_iff x).trans ((hA2c.2.2.1 x).1.symm.trans (hA2c.2.2.1 x).2)
  refine ⟨strictAsc_enc A2X_nodup, fun q hq => List.mem_map_of_mem
    ((hK2.2.2.1 q).1.2 ((allL_iff _ _).1 kA2K _ ((mem_codes hA2 q).1 hq))), one_A2X,
    fun p hp q hq => List.mem_map_of_mem
      ((mA _).2 (Subgroup.mul_mem _ ((mA p).1 hp) ((mA q).1 hq))), fun k hk q hq => ?_,
    fun q hq => ?_, fun y hy hc => ?_, fun b hb h1 h3 => ?_, ?_⟩
  · have hkc : cX k ∈ K2G := by
      rw [← k2c]
      exact List.mem_map_of_mem hk
    have h := andB_true.1 ((allL_iff _ _).1 ((allL_iff _ _).1 kA2n _ ((mem_codes hA2 q).1 hq))
      _ hkc)
    constructor
    · refine List.mem_map_of_mem ((A2X_iff _).2 ?_)
      rw [cX_mul, cX_mul, cX_inv]
      exact h.1
    · refine List.mem_map_of_mem ((A2X_iff _).2 ?_)
      rw [cX_mul, cX_mul, cX_inv]
      exact h.2
  · apply cX_injective
    rw [cX_sq, cX_one]
    exact Nat.eq_of_beq_eq_true ((allL_iff _ _).1 kA2e _ ((mem_codes hA2 q).1 hq))
  · rw [mem_enc hA2, ← memL_iff]
    refine impB_true (fK2_at hy).2.1 ((allL_iff _ _).2 fun c hcm => ?_)
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 (hA2.mem_iff.2 hcm)
    have e : y * q = q * y := enc_injective' (hc q hq)
    change Nat.beq (CFSG.KC.LQT.P.mul 24 (cX y) (cX q)) (CFSG.KC.LQT.P.mul 24 (cX q) (cX y)) = true
    exact beq_of_eq (by rw [← cX_mul, ← cX_mul, e])
  · exact five_of hA2 b (impB_true (fK2_at hb).2.2 (ord3_of h1 h3))
  · rw [hK2.2.1, lK2, A2X_len]

private theorem gen_facts :
    (jLetters.all fun g => (K1X ++ K2X).any fun x => enc x == encPerm g) = true ∧
    evalW jLetters wordA = m24gA ∧ evalW jLetters wordB = m24gB := by
  refine ⟨List.all_eq_true.2 fun g hg => ?_, hwA, hwB⟩
  have hc : CFSG.KC.LQT.W.codeP g ∈ JL := by
    rw [← hJL]
    exact List.mem_map_of_mem hg
  have hx : ∃ x ∈ K1X ++ K2X, cX x = CFSG.KC.LQT.W.codeP g := by
    rcases orB_true.1 ((allL_iff _ _).1 kJ _ hc) with h | h
    · obtain ⟨x, hx, e⟩ := hK1.2.2.2 _ h
      exact ⟨x, List.mem_append_left _ hx, e⟩
    · obtain ⟨x, hx, e⟩ := hK2.2.2.2 _ h
      exact ⟨x, List.mem_append_right _ hx, e⟩
  obtain ⟨x, hx, e⟩ := hx
  refine List.any_eq_true.2 ⟨x, hx, ?_⟩
  rw [beq_iff_eq]
  rw [cX_def] at e
  exact congrArg encPerm (codeP_injective e)

end CFSG.KD.LQT.C4094

namespace Certificates

open CFSG CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native CFSG.QuasithinUnique.Vol2Native.L239 CFSG.QuasithinUnique.Vol2Native.L239.M24Pairs in
open scoped Pointwise in
open CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu CFSG.Blueprint in
theorem certificate4094 : (S0X.length = 1024 ∧
          strictAsc ((S0X.map enc).mergeSort (fun a b => decide (a ≤ b))) = true ∧ (1 : X24) ∈ S0X ∧
          (∀ x ∈ S0X, ∀ g ∈ s0gen, enc (x * g) ∈ S0X.map enc) ∧ (∀ x ∈ S0X, x ^ (2 ^ 10) = 1))
    ∧ (A1X.length = 2 ∧ Z2X.length = 8 ∧ A2X.length = 256 ∧
          (∀ a ∈ a2gen, enc a ∈ A2X.map enc) ∧ (∀ y ∈ A2X, enc y ∈ A2cl.map enc))
    ∧ (K1X.length = 21504 ∧
          strictAsc ((K1X.map enc).mergeSort (fun a b => decide (a ≤ b))) = true ∧
          (∀ x ∈ K1X, enc (x * zX * x⁻¹) = enc zX) ∧
          (∀ x ∈ K1X, ∀ a ∈ A1X, enc (x * a * x⁻¹) ∈ A1X.map enc ∧ enc (x⁻¹ * a * x) ∈ A1X.map enc) ∧
          zX ≠ 1 ∧ (∀ a ∈ A1X, enc a = enc 1 ∨ enc a = enc zX) ∧ enc zX ∈ A1X.map enc)
    ∧ (CFSG.QuasithinUnique.Vol2Native.L239.Reach gensC zX classRes.1 classRes.2.1 classRes.2.2 ∧
          classRes.1.length = 11385 ∧
          strictAsc ((classRes.1.map enc).mergeSort (fun a b => decide (a ≤ b))) = true)
    ∧ (CFSG.QuasithinUnique.Vol2Native.L239.Reach gensA CFSG.QuasithinUnique.Vol2Native.L239.M24Pairs.trio trioRes.1 trioRes.2.1 trioRes.2.2 ∧
          trioRes.1.length = 3795 ∧
          strictAsc ((trioRes.1.map encTrioN).mergeSort (fun a b => decide (a ≤ b))) = true)
    ∧ (T0X.length = 64512 ∧
          strictAsc ((T0X.map enc).mergeSort (fun a b => decide (a ≤ b))) = true ∧
          (∀ x ∈ T0X, x • CFSG.QuasithinUnique.Vol2Native.L239.M24Pairs.trio = CFSG.QuasithinUnique.Vol2Native.L239.M24Pairs.trio) ∧ T0N.length = 9216)
    ∧ (K2X.length = 9216 ∧
          strictAsc ((K2X.map enc).mergeSort (fun a b => decide (a ≤ b))) = true ∧
          (∀ x ∈ K2X, nrmTestGens enc (A2X.map enc) a2gen x = true))
    ∧ (Q1X.length = 128 ∧
          strictAsc ((Q1X.map enc).mergeSort (fun a b => decide (a ≤ b))) = true ∧
          (∀ q ∈ Q1X, enc q ∈ K1X.map enc) ∧ (1 : X24) ∈ Q1X ∧
          (∀ p ∈ Q1X, ∀ q ∈ Q1X, enc (p * q) ∈ Q1X.map enc) ∧
          (∀ k ∈ k1gen, ∀ q ∈ Q1X,
            enc (k * q * k⁻¹) ∈ Q1X.map enc ∧ enc (k⁻¹ * q * k) ∈ Q1X.map enc) ∧
          (∀ q ∈ Q1X, q ^ (2 ^ 4) = 1) ∧
          (∀ y ∈ K1X, (∀ q ∈ Q1X, enc (y * q) = enc (q * y)) → enc y ∈ Q1X.map enc) ∧
          (∀ b ∈ K1X, b ≠ 1 → b ^ 3 = 1 →
            4 < ((Q1X.map fun q => enc (q * b * q⁻¹ * b⁻¹)).dedup).length) ∧
          K1X.length / Q1X.length = 168)
    ∧ (strictAsc ((A2X.map enc).mergeSort (fun a b => decide (a ≤ b))) = true ∧
          (∀ q ∈ A2X, enc q ∈ K2X.map enc) ∧ (1 : X24) ∈ A2X ∧
          (∀ p ∈ A2X, ∀ q ∈ A2X, enc (p * q) ∈ A2X.map enc) ∧
          (∀ k ∈ k2gen, ∀ q ∈ A2X,
            enc (k * q * k⁻¹) ∈ A2X.map enc ∧ enc (k⁻¹ * q * k) ∈ A2X.map enc) ∧
          (∀ q ∈ A2X, q ^ (2 ^ 4) = 1) ∧
          (∀ y ∈ K2X, (∀ q ∈ A2X, enc (y * q) = enc (q * y)) → enc y ∈ A2X.map enc) ∧
          (∀ b ∈ K2X, b ≠ 1 → b ^ 3 = 1 →
            4 < ((A2X.map fun q => enc (q * b * q⁻¹ * b⁻¹)).dedup).length) ∧
          K2X.length / A2X.length = 36)
    ∧ ((jLetters.all fun g => (K1X ++ K2X).any fun x => enc x == encPerm g) = true ∧
          CFSG.QuasithinUnique.Vol2Native.L239.M24Pairs.evalW jLetters CFSG.QuasithinUnique.Vol2Native.L239.M24Pairs.wordA = m24gA ∧ CFSG.QuasithinUnique.Vol2Native.L239.M24Pairs.evalW jLetters CFSG.QuasithinUnique.Vol2Native.L239.M24Pairs.wordB = m24gB) :=
  ⟨CFSG.KD.LQT.C4094.s0_facts, CFSG.KD.LQT.C4094.a_facts, CFSG.KD.LQT.C4094.k1_facts,
    CFSG.KD.LQT.C4094.class_facts, CFSG.KD.LQT.C4094.trio_facts, CFSG.KD.LQT.C4094.t0_facts,
    CFSG.KD.LQT.C4094.k2_facts, CFSG.KD.LQT.C4094.q1_facts, CFSG.KD.LQT.C4094.q2_facts,
    CFSG.KD.LQT.C4094.gen_facts⟩

end Certificates

end
