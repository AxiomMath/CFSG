module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporJ2CheckInputs
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporGood
import Certificates.Kernel.LocalQT.Pairs.C4091g1
import Certificates.Kernel.LocalQT.Pairs.C4091g1c
import Certificates.Kernel.LocalQT.Pairs.C4091g1d
import Certificates.Kernel.LocalQT.Pairs.C4091g1k
import Certificates.Kernel.LocalQT.Pairs.C4091g2
import Certificates.Kernel.LocalQT.Pairs.C4091g2c
import Certificates.Kernel.LocalQT.Pairs.C4091o
import Certificates.Kernel.LocalQT.Pairs.C4091f1b
import Certificates.Kernel.LocalQT.Pairs.C4091f2
import Certificates.Kernel.LocalQT.Pairs.C4091q
import Certificates.Kernel.LocalQT.Pairs.C4091s

set_option maxRecDepth 100000

public section

namespace CFSG.KD.LQT.C4091

open CFSG.KC.LQT.PW CFSG.KC.LQT.PH CFSG.KD.LQT.J2T CFSG.ComponentClassification.J2Cover
  CFSG.QuasithinUnique.Vol2Native.L239 CFSG.QuasithinUnique.Vol2Native.L239.J2Pairs
  CFSG.Sporadic.Schreier
open scoped Pointwise

attribute [local irreducible] cJ mulW invW oneW encW imgMaskW

private theorem mem_cJ {L : List XJ} {LC : List ℕ} (hL : (L.map cJ).Perm LC) (w : XJ) :
    w ∈ L ↔ cJ w ∈ LC := by
  rw [← hL.mem_iff, List.mem_map]
  exact ⟨fun h => ⟨w, h, rfl⟩, fun ⟨y, hy, e⟩ => by rwa [← cJ_injective e]⟩

private theorem mem_encJ {L : List XJ} {LC : List ℕ} (hL : (L.map cJ).Perm LC) (w : XJ) :
    enc w ∈ L.map enc ↔ cJ w ∈ LC := by
  rw [← mem_cJ hL, List.mem_map]
  exact ⟨fun ⟨y, hy, e⟩ => by rwa [← enc_injective e], fun h => ⟨w, h, rfl⟩⟩

private theorem all_cJ {L : List XJ} {LC : List ℕ} (hL : (L.map cJ).Perm LC) (g : XJ → Bool)
    (gk : ℕ → Bool) (hg : ∀ y, g y = gk (cJ y)) : L.all g = CFSG.KC.LQT.P.allL LC gk := by
  rw [Bool.eq_iff_iff, List.all_eq_true, allL_iff]
  constructor
  · intro h c hc
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 (hL.mem_iff.2 hc)
    rw [← hg]
    exact h y hy
  · intro h y hy
    rw [hg]
    exact h _ (hL.mem_iff.1 (List.mem_map_of_mem hy))

private theorem filter_cJ (L : List XJ) (p : XJ → Bool) (q : ℕ → Bool)
    (hp : ∀ x, p x = q (cJ x)) : (L.filter p).map cJ = (L.map cJ).filter q := by
  induction L with
  | nil => rfl
  | cons x L ih =>
    rw [List.filter_cons, List.map_cons, List.filter_cons, hp x]
    cases q (cJ x)
    · simpa using ih
    · simpa using ih

private theorem map_cJ (L : List XJ) (f : XJ → ℕ) (g : ℕ → ℕ) (h : ∀ q, f q = g (cJ q)) :
    L.map f = (L.map cJ).map g := by
  induction L with
  | nil => rfl
  | cons q L ih => rw [List.map_cons, List.map_cons, List.map_cons, h q, ih]

private theorem filter_perm {L : List XJ} {LC : List ℕ} (hL : (L.map cJ).Perm LC) (p : XJ → Bool)
    (q : ℕ → Bool) (hp : ∀ x, p x = q (cJ x)) :
    ((L.filter p).map cJ).Perm (CFSG.KC.LQT.S.filtL LC q) := by
  rw [filter_cJ L p q hp, filtL_eq]
  exact hL.filter q

private theorem beq_cJ (u v : XJ) : (enc u == enc v) = Nat.beq (cJ u) (cJ v) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, Nat.beq_eq, enc_injective.eq_iff, cJ_injective.eq_iff]

private theorem beq_of_eq {a b : ℕ} (h : a = b) : Nat.beq a b = true := h ▸ Nat.beq_refl a

private theorem sqW_succ (y e : ℕ) : sqW 315 9 y (e + 1) = sqW 315 9 (mulW 315 9 y y) e :=
  letN_eq _ _

private theorem cJ_sq (x : XJ) (e : ℕ) : cJ (x ^ 2 ^ e) = sqW 315 9 (cJ x) e := by
  induction e generalizing x with
  | zero => rw [pow_zero, pow_one]; rfl
  | succ e ih =>
    have h1 : x ^ 2 ^ (e + 1) = (x * x) ^ 2 ^ e := by rw [pow_succ', pow_mul, sq]
    rw [h1, sqW_succ, ← cJ_mul, ih]

private theorem cJ_conj (k q : XJ) : cJ (k * q * k⁻¹) = conjW 315 9 (cJ k) (cJ q) := by
  rw [cJ_mul, cJ_mul, cJ_inv]
  rfl

private theorem cJ_conjI (k q : XJ) : cJ (k⁻¹ * q * k) = conjIW 315 9 (cJ k) (cJ q) := by
  rw [cJ_mul, cJ_mul, cJ_inv]
  rfl

private theorem cJ_cm (q b : XJ) : cJ (q * b * q⁻¹ * b⁻¹) = cmW (cJ q) (cJ b) := by
  rw [cJ_mul, cJ_conj, cJ_inv]

private theorem allBs_cons {b : Bool} {l : List Bool} (h : CFSG.KC.LQT.S.allBs (b :: l) = true) :
    b = true ∧ CFSG.KC.LQT.S.allBs l = true :=
  andB_true.1 h

private theorem getK_mem : ∀ (l : List ℕ) (i : ℕ), i < l.length → CFSG.KC.LQT.S.getK l i ∈ l
  | [], _, h => absurd h (by simp)
  | x :: l, 0, _ => List.mem_cons_self
  | x :: l, i + 1, h => by
    have e : CFSG.KC.LQT.S.getK (x :: l) (i + 1) = CFSG.KC.LQT.S.getK l i := rfl
    rw [e]
    exact List.mem_cons_of_mem _ (getK_mem l i (by simpa using h))

private theorem slice_mem (L : List ℕ) (s K : ℕ) (hs : 0 < s) (hK : L.length ≤ K * s) (x : ℕ)
    (hx : x ∈ L) : ∃ k < K, x ∈ sliceK L (k * s) s := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  refine ⟨i / s, ?_, ?_⟩
  · exact (Nat.div_lt_iff_lt_mul hs).2 (lt_of_lt_of_le hi hK)
  · rw [sliceK, List.mem_iff_getElem]
    have h1 : i / s * s ≤ i := Nat.div_mul_le_self i s
    have h2 : i - i / s * s < s := by
      have := Nat.mod_lt i hs
      rw [Nat.mod_eq_sub_mul_div] at this
      rw [Nat.mul_comm]
      exact this
    refine ⟨i - i / s * s, ?_, ?_⟩
    · rw [List.length_take, List.length_drop]
      omega
    · rw [List.getElem_take, List.getElem_drop]
      congr 1
      omega

private theorem zipN_mem : ∀ (l h : List ℕ) (f : ℕ → ℕ → Bool), zipN l h f = true →
    ∀ x ∈ l, ∃ e ∈ h, f x e = true
  | [], _, _, _, x, hx => absurd hx (by simp)
  | x :: l, [], f, hz, _, _ => absurd hz (by simp [zipN])
  | x :: l, e :: h, f, hz, y, hy => by
    have hz' : CFSG.KC.Ord.andB (f x e) (zipN l h f) = true := hz
    obtain ⟨h1, h2⟩ := andB_true.1 hz'
    rcases List.mem_cons.1 hy with rfl | hy
    · exact ⟨e, List.mem_cons_self, h1⟩
    · obtain ⟨e', he', h3⟩ := zipN_mem l h f h2 y hy
      exact ⟨e', List.mem_cons_of_mem _ he', h3⟩

private theorem allL_slice {L : List ℕ} {s K : ℕ} (hs : 0 < s) (hK : L.length ≤ K * s)
    {f : ℕ → Bool} (h : ∀ k < K, CFSG.KC.LQT.P.allL (sliceK L (k * s) s) f = true) :
    ∀ x ∈ L, f x = true := by
  intro x hx
  obtain ⟨k, hk, hm⟩ := slice_mem L s K hs hK x hx
  exact (allL_iff _ _).1 (h k hk) x hm

private theorem zip_slice {L H : List ℕ} {s K : ℕ} (hs : 0 < s) (hK : L.length ≤ K * s)
    {f : ℕ → ℕ → Bool} (h : ∀ k < K, zipN (sliceK L (k * s) s) (sliceK H (k * s) s) f = true) :
    ∀ x ∈ L, ∃ e ∈ H, f x e = true := by
  intro x hx
  obtain ⟨k, hk, hm⟩ := slice_mem L s K hs hK x hx
  obtain ⟨e, he, hf⟩ := zipN_mem _ _ f (h k hk) x hm
  exact ⟨e, List.mem_of_mem_drop (List.mem_of_mem_take he), hf⟩

private theorem getK_of_mem : ∀ (l : List ℕ) (g : ℕ), g ∈ l →
    ∃ i < l.length, CFSG.KC.LQT.S.getK l i = g
  | [], _, h => absurd h (by simp)
  | x :: l, g, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact ⟨0, by simp, rfl⟩
    · obtain ⟨i, hi, e⟩ := getK_of_mem l g h
      exact ⟨i + 1, by simpa using hi, e⟩

private theorem closed_slices {G E : List ℕ} {s K : ℕ} (hs : 0 < s) (hK : E.length ≤ K * s)
    (h : ∀ i < G.length, ∀ k < K, closedS (CFSG.KC.LQT.S.getK G i) E (k * s) s = true) :
    ∀ g ∈ G, ∀ x ∈ E, mulW 315 9 g x ∈ E := by
  intro g hg x hx
  obtain ⟨i, hi, rfl⟩ := getK_of_mem G g hg
  obtain ⟨k, hk, hm⟩ := slice_mem E s K hs hK x hx
  exact closedS_sound (h i hi k hk) x hm

private theorem norm_closure (gens L : List XJ)
    (hg : ∀ g ∈ gens, ∀ a ∈ L, g * a * g⁻¹ ∈ L ∧ g⁻¹ * a * g ∈ L) :
    ∀ x ∈ Subgroup.closure {g | g ∈ gens}, ∀ a ∈ L, x * a * x⁻¹ ∈ L ∧ x⁻¹ * a * x ∈ L := by
  intro x hx
  induction hx using Subgroup.closure_induction with
  | mem g h => exact hg g h
  | one => intro a ha; simpa using ha
  | mul x y _ _ ihx ihy =>
    intro a ha
    constructor
    · have := (ihx _ (ihy a ha).1).1
      rwa [show x * (y * a * y⁻¹) * x⁻¹ = x * y * a * (x * y)⁻¹ by group] at this
    · have := (ihy _ (ihx a ha).2).2
      rwa [show y⁻¹ * (x⁻¹ * a * x) * y = (x * y)⁻¹ * a * (x * y) by group] at this
  | inv x _ ih =>
    intro a ha
    constructor
    · simpa using (ih a ha).2
    · simpa using (ih a ha).1

private theorem fix_closure (gens : List XJ) (S : Finset (Fin 315)) (hg : ∀ g ∈ gens, g • S = S) :
    ∀ x ∈ Subgroup.closure {g | g ∈ gens}, x • S = S := by
  intro x hx
  have hle : Subgroup.closure {g | g ∈ gens} ≤ MulAction.stabilizer XJ S :=
    (Subgroup.closure_le _).2 fun g h => hg g h
  exact hle hx

private theorem gc : gensA.map cJ = GAB := by
  rw [gensA, List.map_cons, List.map_cons, List.map_nil, cJ_paC, cJ_pbC]

private theorem gx (w : List ℤ) : cJ (genX w) = evalZW 315 9 GAB w := by
  rw [genX, tabX_eq, cJ_evalW, ← gc]
  rfl

private theorem mapgx : ∀ ws : List (List ℤ),
    (ws.map genX).map cJ = ws.map (evalZW 315 9 GAB)
  | [] => rfl
  | w :: ws => by rw [List.map_cons, List.map_cons, List.map_cons, gx, mapgx ws]

private theorem s0c : s0gen.map cJ = S0G := by
  rw [s0gen, mapgx]

private theorem mapev (S : List XJ) {SC : List ℕ} (hS : S.map cJ = SC) : ∀ ws : List (List ℤ),
    (ws.map (evalW S)).map cJ = ws.map (evalZW 315 9 SC)
  | [] => rfl
  | w :: ws => by
    rw [List.map_cons, List.map_cons, List.map_cons, cJ_evalW, hS, mapev S hS ws]

private theorem t1c : cJ t1X = t1C := by rw [t1X, gx]

private theorem t2c : cJ t2X = t2C := by rw [t2X, gx]

private theorem k1c : k1gen.map cJ = K1G := by
  rw [k1gen, List.map_append, s0c, List.map_singleton, t1c]
  rfl

private theorem k2c : k2gen.map cJ = K2G := by
  rw [k2gen, List.map_append, s0c, List.map_singleton, t2c]
  rfl

private theorem a2c : a2gen.map cJ = A2G := by rw [a2gen, mapev s0gen s0c]

private theorem q1c : q1gen.map cJ = Q1G := by rw [q1gen, mapev s0gen s0c]

private theorem hS : S0X.Nodup ∧ (S0X.map cJ).Perm S0E ∧
    ∀ x, x ∈ S0X ↔ x ∈ Subgroup.closure {g | g ∈ s0gen} :=
  grp_sound s0gen s0c S0P 40 gS1 gS2 (closedE_sound gS3) gS4 gS5

private theorem hA2c : A2cl.Nodup ∧ (A2cl.map cJ).Perm A2E ∧
    ∀ x, x ∈ A2cl ↔ x ∈ Subgroup.closure {g | g ∈ a2gen} :=
  grp_sound a2gen a2c A2P 40 gA1 gA2 (closedE_sound gA3) gA4 gA5

private theorem hQ1 : Q1X.Nodup ∧ (Q1X.map cJ).Perm Q1E ∧
    ∀ x, x ∈ Q1X ↔ x ∈ Subgroup.closure {g | g ∈ q1gen} :=
  grp_sound q1gen q1c Q1P 40 gQ1 gQ2 (closedE_sound gQ3) gQ4 gQ5

private theorem k1glen : K1G.length = 4 := by
  rw [← k1c, List.length_map, k1gen, List.length_append, s0gen, List.length_map]
  rfl

private theorem k2glen : K2G.length = 4 := by
  rw [← k2c, List.length_map, k2gen, List.length_append, s0gen, List.length_map]
  rfl

private theorem hK1 : K1X.Nodup ∧ (K1X.map cJ).Perm K1E ∧
    ∀ x, x ∈ K1X ↔ x ∈ Subgroup.closure {g | g ∈ k1gen} :=
  grp_sound k1gen k1c K1P 40 gK11 gK12
    (closed_slices (s := 960) (K := 2) (by norm_num)
      (by rw [← lenL_eq, Nat.eq_of_beq_eq_true lK1]) fun i hi k hk => by
        rw [k1glen] at hi
        interval_cases i <;> interval_cases k
        exacts [c100, c101, c110, c111, c120, c121, c130, c131])
    gK14 gK15

private theorem hK2 : K2X.Nodup ∧ (K2X.map cJ).Perm K2E ∧
    ∀ x, x ∈ K2X ↔ x ∈ Subgroup.closure {g | g ∈ k2gen} :=
  grp_sound k2gen k2c K2P 40 gK21 gK22
    (closed_slices (s := 1152) (K := 1) (by norm_num)
      (by rw [← lenL_eq, Nat.eq_of_beq_eq_true lK2]) fun i hi k hk => by
        rw [k2glen] at hi
        interval_cases i <;> interval_cases k
        exacts [c20, c21, c22, c23])
    gK24 gK25

private theorem len_of {L : List XJ} {LC : List ℕ} (hL : (L.map cJ).Perm LC) {n : ℕ}
    (h : Nat.beq (CFSG.KC.LQT.S.lenL LC) n = true) : L.length = n := by
  rw [← List.length_map (f := cJ), hL.length_eq, ← lenL_eq]
  exact Nat.eq_of_beq_eq_true h

private theorem hA1 : (A1X.map cJ).Perm A1E :=
  filter_perm hS.2.1 _ pA1 fun x => by
    rw [all_cJ (L := s0gen) (List.Perm.of_eq s0c) _
      (fun c => Nat.beq (mulW 315 9 c (cJ x)) (mulW 315 9 (cJ x) c))]
    intro s
    rw [beq_cJ, cJ_mul, cJ_mul]

private theorem hZ2 : (Z2X.map cJ).Perm Z2E :=
  filter_perm hS.2.1 _ pZ2 fun y => by
    rw [all_cJ (L := s0gen) (List.Perm.of_eq s0c) _ (fun c => CFSG.KC.LQT.S.memL
      (mulW 315 9 (mulW 315 9 (mulW 315 9 (cJ y) c) (invW 315 9 (cJ y))) (invW 315 9 c)) A1E)]
    intro s
    rw [Bool.eq_iff_iff, List.contains_iff_mem, memL_iff, mem_encJ hA1, cJ_mul, cJ_mul, cJ_mul,
      cJ_inv, cJ_inv]

private theorem hA2 : (A2X.map cJ).Perm A2X' :=
  filter_perm hS.2.1 _ pA2 fun x => by
    rw [all_cJ hZ2 _ (fun c => Nat.beq (mulW 315 9 c (cJ x)) (mulW 315 9 (cJ x) c))]
    intro y
    rw [beq_cJ, cJ_mul, cJ_mul]

private theorem lA' : Nat.beq (CFSG.KC.LQT.S.lenL A1E) 2 = true ∧
    Nat.beq (CFSG.KC.LQT.S.lenL Z2E) 4 = true ∧ Nat.beq (CFSG.KC.LQT.S.lenL A2X') 64 = true := by
  obtain ⟨h1, h⟩ := allBs_cons lA
  obtain ⟨h2, h⟩ := allBs_cons h
  exact ⟨h1, h2, (allBs_cons h).1⟩

private theorem one_S0 : (1 : XJ) ∈ S0X := (hS.2.2 1).2 (Subgroup.one_mem _)

private theorem s0_facts : S0X.length = 128 ∧
    strictAsc ((S0X.map enc).mergeSort (fun a b => decide (a ≤ b))) = true ∧ (1 : XJ) ∈ S0X ∧
    (∀ x ∈ S0X, ∀ g ∈ s0gen, enc (x * g) ∈ S0X.map enc) ∧ (∀ x ∈ S0X, x ^ (2 ^ 3) = 1) := by
  refine ⟨len_of hS.2.1 lS, strictAsc_nat (hS.1.map enc_injective), one_S0,
    fun x hx g hg => List.mem_map_of_mem ((hS.2.2 _).2 (Subgroup.mul_mem _
      ((hS.2.2 x).1 hx) (Subgroup.subset_closure hg))), fun x hx => ?_⟩
  apply cJ_injective
  rw [cJ_sq, cJ_one]
  exact Nat.eq_of_beq_eq_true ((allL_iff _ _).1 kSe _ ((mem_cJ hS.2.1 x).1 hx))

private theorem a_facts : A1X.length = 2 ∧ Z2X.length = 4 ∧ A2X.length = 64 ∧
    (∀ a ∈ a2gen, enc a ∈ A2X.map enc) ∧ (∀ y ∈ A2X, enc y ∈ A2cl.map enc) := by
  refine ⟨len_of hA1 lA'.1, len_of hZ2 lA'.2.1, len_of hA2 lA'.2.2, fun a ha => ?_, fun y hy => ?_⟩
  · rw [mem_encJ hA2, ← memL_iff]
    exact (allL_iff _ _).1 kA2g _ (by rw [← a2c]; exact List.mem_map_of_mem ha)
  · rw [mem_encJ hA2c.2.1, ← memL_iff]
    exact (allL_iff _ _).1 kA2c _ ((mem_cJ hA2 y).1 hy)

private theorem hF1 : maskF F1X = F1M := fix_mask A1X hA1

private theorem hF2 : maskF F2X = F2M := fix_mask A2X hA2

private theorem orb1_facts : Reach gensA F1X orb1.1 orb1.2.1 orb1.2.2 ∧ orb1.1.length = 315 ∧
    strictAsc ((orb1.1.map maskF).mergeSort (fun a b => decide (a ≤ b))) = true := by
  have hN := Nat.eq_of_beq_eq_true o1N
  have ho : (orb1.1.map maskF).Perm O1E := by
    have h := orb_sound F1X 1000 gc O1P o11 o1L (by rw [hF1]; exact o12) (by rw [hF1]; exact o13)
      (by rw [hF1, hN]; norm_num)
    rw [hF1] at h
    exact h
  refine ⟨reach_bfsOrbit id (fun _ => rfl) maskF gensA F1X 1000, ?_, ?_⟩
  · rw [← List.length_map (f := maskF), ho.length_eq, ← lenL_eq, hN]
  · exact strictAsc_nat (ho.nodup_iff.2 ((sortN_perm _).nodup_iff.1 (sincK_nodup o12)))

private theorem orb2_facts : Reach gensA F2X orb2.1 orb2.2.1 orb2.2.2 ∧ orb2.1.length = 525 ∧
    strictAsc ((orb2.1.map maskF).mergeSort (fun a b => decide (a ≤ b))) = true := by
  have hN := Nat.eq_of_beq_eq_true o2N
  have ho : (orb2.1.map maskF).Perm O2E := by
    have h := orb_sound F2X 1000 gc O2P o21 o2L (by rw [hF2]; exact o22) (by rw [hF2]; exact o23)
      (by rw [hF2, hN]; norm_num)
    rw [hF2] at h
    exact h
  refine ⟨reach_bfsOrbit id (fun _ => rfl) maskF gensA F2X 1000, ?_, ?_⟩
  · rw [← List.length_map (f := maskF), ho.length_eq, ← lenL_eq, hN]
  · exact strictAsc_nat (ho.nodup_iff.2 ((sortN_perm _).nodup_iff.1 (sincK_nodup o22)))

private theorem fK1_at {x : XJ} (hx : x ∈ K1X) : ∃ h ∈ K1H, fK1 (cJ x) h = true :=
  zip_slice (s := 240) (K := 8) (by norm_num) (by rw [← lenL_eq, Nat.eq_of_beq_eq_true lK1])
    (fun k hk => by
      interval_cases k
      exacts [f10, f11, f12, f13, f14, f15, f16, f17]) _ ((mem_cJ hK1.2.1 x).1 hx)

private theorem fK1_parts {x : XJ} {h : ℕ} (hf : fK1 (cJ x) h = true) :
    CFSG.KC.LQT.P.impB (CFSG.KC.LQT.P.allL Q1G fun q => commW 315 9 (cJ x) q)
      (CFSG.KC.LQT.S.memL (cJ x) Q1E) = true ∧
    CFSG.KC.LQT.P.impB (ord3 (cJ x))
      (CFSG.KC.LQT.P.letB (cmW (CFSG.KC.LQT.S.getK Q1E (Nat.div h 32)) (cJ x)) fun cp =>
        CFSG.KC.LQT.P.letB (cmW (CFSG.KC.LQT.S.getK Q1E (Nat.mod h 32)) (cJ x)) fun cq =>
          CFSG.KC.Ord.orB (CFSG.KC.Ord.notB (Nat.beq (mulW 315 9 cp cq) (mulW 315 9 cq cp)))
            (CFSG.KC.Ord.notB (Nat.beq (mulW 315 9 cp cp) (oneW 315 9)))) = true := by
  obtain ⟨h1, hf⟩ := allBs_cons hf
  exact ⟨h1, (allBs_cons hf).1⟩

private theorem gen_norm (gens L : List XJ) {G LC : List ℕ} (hG : gens.map cJ = G)
    (hL : (L.map cJ).Perm LC)
    (h : CFSG.KC.LQT.P.allL G (fun g => CFSG.KC.LQT.P.allL LC fun a =>
      CFSG.KC.Ord.andB (CFSG.KC.LQT.S.memL (conjW 315 9 g a) LC)
        (CFSG.KC.LQT.S.memL (conjIW 315 9 g a) LC)) = true) :
    ∀ g ∈ gens, ∀ a ∈ L, g * a * g⁻¹ ∈ L ∧ g⁻¹ * a * g ∈ L := by
  intro g hg a ha
  have hgc : cJ g ∈ G := by
    rw [← hG]
    exact List.mem_map_of_mem hg
  have k := andB_true.1 ((allL_iff _ _).1 ((allL_iff _ _).1 h _ hgc) _ ((mem_cJ hL a).1 ha))
  rw [mem_cJ hL, mem_cJ hL, cJ_conj, cJ_conjI, ← memL_iff, ← memL_iff]
  exact k

private theorem gen_fix (gens : List XJ) {G : List ℕ} (hG : gens.map cJ = G) (S : Finset (Fin 315))
    {M : ℕ} (hM : maskF S = M)
    (h : CFSG.KC.LQT.P.allL G (fun g => Nat.beq (imgMaskW 315 9 g M) M) = true) :
    ∀ g ∈ gens, g • S = S := by
  intro g hg
  have hgc : cJ g ∈ G := by
    rw [← hG]
    exact List.mem_map_of_mem hg
  refine smul_mask g S ?_
  rw [hM]
  exact Nat.eq_of_beq_eq_true ((allL_iff _ _).1 h _ hgc)

private theorem k1_facts : K1X.length = 1920 ∧
    strictAsc ((K1X.map enc).mergeSort (fun a b => decide (a ≤ b))) = true ∧
    (∀ x ∈ K1X, ∀ a ∈ A1X, enc (x * a * x⁻¹) ∈ A1X.map enc ∧ enc (x⁻¹ * a * x) ∈ A1X.map enc) ∧
    (∀ x ∈ K1X, x • F1X = F1X) := by
  refine ⟨len_of hK1.2.1 lK1, strictAsc_nat (hK1.1.map enc_injective), fun x hx a ha => ?_,
    fun x hx => fix_closure k1gen F1X (gen_fix k1gen k1c F1X hF1 kF1) x ((hK1.2.2 x).1 hx)⟩
  have k := norm_closure k1gen A1X (gen_norm k1gen A1X k1c hA1 kz1) x ((hK1.2.2 x).1 hx) a ha
  exact ⟨List.mem_map_of_mem k.1, List.mem_map_of_mem k.2⟩

private theorem ord3_of {b : XJ} (h1 : b ≠ 1) (h3 : b ^ 3 = 1) : ord3 (cJ b) = true := by
  refine andB_true.2 ⟨?_, ?_⟩
  · rw [notB_eq, ← cJ_one, Bool.not_eq_true', ← Bool.not_eq_true, Nat.beq_eq, cJ_injective.eq_iff]
    exact h1
  · rw [← cJ_mul, ← cJ_mul, ← pow_three', h3, cJ_one]
    exact Nat.beq_refl _

private theorem letB_eq (y : ℕ) (k : ℕ → Bool) : CFSG.KC.LQT.P.letB y k = k y := by
  cases y <;> rfl

private theorem q1len : Q1E.length = 32 := by
  rw [← lenL_eq]
  exact Nat.eq_of_beq_eq_true lQ

private theorem q1_facts : Q1X.length = 32 ∧
    strictAsc ((Q1X.map enc).mergeSort (fun a b => decide (a ≤ b))) = true ∧
    (∀ q ∈ Q1X, enc q ∈ K1X.map enc) ∧ (1 : XJ) ∈ Q1X ∧
    (∀ p ∈ Q1X, ∀ q ∈ Q1X, enc (p * q) ∈ Q1X.map enc) ∧
    (∀ k ∈ k1gen, ∀ q ∈ Q1X,
      enc (k * q * k⁻¹) ∈ Q1X.map enc ∧ enc (k⁻¹ * q * k) ∈ Q1X.map enc) ∧
    (∀ q ∈ Q1X, q ^ (2 ^ 2) = 1) ∧
    (∀ y ∈ K1X, (∀ q ∈ Q1X, enc (y * q) = enc (q * y)) → enc y ∈ Q1X.map enc) ∧
    (∀ b ∈ K1X, b ≠ 1 → b ^ 3 = 1 → ∃ p ∈ Q1X, ∃ q ∈ Q1X,
      enc ((p * b * p⁻¹ * b⁻¹) * (q * b * q⁻¹ * b⁻¹)) ≠
        enc ((q * b * q⁻¹ * b⁻¹) * (p * b * p⁻¹ * b⁻¹)) ∨
      enc ((p * b * p⁻¹ * b⁻¹) * (p * b * p⁻¹ * b⁻¹)) ≠ enc 1) := by
  have mQ : ∀ x, x ∈ Q1X ↔ x ∈ Subgroup.closure {g | g ∈ q1gen} := hQ1.2.2
  have getQ : ∀ i < 32, ∃ p ∈ Q1X, cJ p = CFSG.KC.LQT.S.getK Q1E i := by
    intro i hi
    have hm := getK_mem Q1E i (by rw [q1len]; exact hi)
    obtain ⟨p, hp, e⟩ := List.mem_map.1 (hQ1.2.1.mem_iff.2 hm)
    exact ⟨p, hp, e⟩
  refine ⟨len_of hQ1.2.1 lQ, strictAsc_nat (hQ1.1.map enc_injective), fun q hq => ?_,
    (mQ 1).2 (Subgroup.one_mem _), fun p hp q hq => List.mem_map_of_mem
      ((mQ _).2 (Subgroup.mul_mem _ ((mQ p).1 hp) ((mQ q).1 hq))), fun k hk q hq => ?_,
    fun q hq => ?_, fun y hy hc => ?_, fun b hb h1 h3 => ?_⟩
  · rw [mem_encJ hK1.2.1, ← memL_iff]
    exact (allL_iff _ _).1 kQK _ ((mem_cJ hQ1.2.1 q).1 hq)
  · have k := gen_norm k1gen Q1X k1c hQ1.2.1 kQn k hk q hq
    exact ⟨List.mem_map_of_mem k.1, List.mem_map_of_mem k.2⟩
  · apply cJ_injective
    rw [cJ_sq, cJ_one]
    exact Nat.eq_of_beq_eq_true ((allL_iff _ _).1 kQe _ ((mem_cJ hQ1.2.1 q).1 hq))
  · obtain ⟨h, -, hf⟩ := fK1_at hy
    rw [mem_encJ hQ1.2.1, ← memL_iff]
    refine impB_true (fK1_parts hf).1 ((allL_iff _ _).2 fun c hcm => ?_)
    rw [← q1c] at hcm
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hcm
    have e : y * q = q * y := enc_injective (hc q ((mQ q).2 (Subgroup.subset_closure hq)))
    change Nat.beq (mulW 315 9 (cJ y) (cJ q)) (mulW 315 9 (cJ q) (cJ y)) = true
    exact beq_of_eq (by rw [← cJ_mul, ← cJ_mul, e])
  · obtain ⟨h, hH, hf⟩ := fK1_at hb
    have hh : h < 1024 := by
      have := (allL_iff _ _).1 kH h hH
      rwa [Nat.blt_eq] at this
    have hd : Nat.div h 32 < 32 := by
      change h / 32 < 32
      omega
    have hm : Nat.mod h 32 < 32 := Nat.mod_lt _ (by norm_num)
    obtain ⟨p, hp, ep⟩ := getQ (Nat.div h 32) hd
    obtain ⟨q, hq, eq⟩ := getQ (Nat.mod h 32) hm
    have k := impB_true (fK1_parts hf).2 (ord3_of h1 h3)
    rw [letB_eq, letB_eq, ← ep, ← eq, ← cJ_cm, ← cJ_cm, ← cJ_mul, ← cJ_mul, ← cJ_mul, ← cJ_one,
      notB_eq, notB_eq] at k
    refine ⟨p, hp, q, hq, ?_⟩
    rcases orB_true.1 k with k | k
    · left
      intro e
      rw [Bool.not_eq_true', ← Bool.not_eq_true, Nat.beq_eq] at k
      exact k (cJ_injective.eq_iff.2 (enc_injective e))
    · right
      intro e
      rw [Bool.not_eq_true', ← Bool.not_eq_true, Nat.beq_eq] at k
      exact k (cJ_injective.eq_iff.2 (enc_injective e))

private theorem fK2_at {x : XJ} (hx : x ∈ K2X) : fK2 (cJ x) = true :=
  allL_slice (s := 192) (K := 6) (by norm_num) (by rw [← lenL_eq, Nat.eq_of_beq_eq_true lK2])
    (fun k hk => by
      interval_cases k
      exacts [f20, f21, f22, f23, f24, f25]) _ ((mem_cJ hK2.2.1 x).1 hx)

private theorem fK2_parts {x : XJ} (hf : fK2 (cJ x) = true) :
    CFSG.KC.LQT.P.impB (CFSG.KC.LQT.P.allL A2G fun q => commW 315 9 (cJ x) q)
      (CFSG.KC.LQT.S.memL (cJ x) A2X') = true ∧
    CFSG.KC.LQT.P.impB (ord3 (cJ x)) (fiveK (fun q => encW 315 9 (cmW q (cJ x))) A2X') = true := by
  obtain ⟨h1, hf⟩ := allBs_cons hf
  exact ⟨h1, (allBs_cons hf).1⟩

private theorem A2X_cl (x : XJ) (hx : x ∈ A2X) : x ∈ A2cl := by
  rw [mem_cJ hA2c.2.1, ← memL_iff]
  exact (allL_iff _ _).1 kA2c _ ((mem_cJ hA2 x).1 hx)

private theorem A2X_iff (x : XJ) : x ∈ A2X ↔ x ∈ Subgroup.closure {g | g ∈ a2gen} := by
  rw [← hA2c.2.2 x]
  have hp : A2X.Perm A2cl := (List.subperm_of_subset (hS.1.filter _) fun y hy => A2X_cl y hy)
    |>.perm_of_length_le (by rw [len_of hA2c.2.1 lA2]; exact (len_of hA2 lA'.2.2).ge)
  exact hp.mem_iff

private theorem a2g_A2X (a : XJ) (ha : a ∈ a2gen) : a ∈ A2X :=
  (A2X_iff a).2 (Subgroup.subset_closure ha)

private theorem k2_norm (x : XJ) (hx : x ∈ K2X) :
    x ∈ Subgroup.normalizer ((Subgroup.closure {g | g ∈ a2gen} : Subgroup XJ) : Set XJ) := by
  have hle : Subgroup.closure {g | g ∈ k2gen} ≤
      Subgroup.normalizer ((Subgroup.closure {g | g ∈ a2gen} : Subgroup XJ) : Set XJ) := by
    rw [Subgroup.closure_le]
    intro g hg
    rw [SetLike.mem_coe, mem_normalizer_of_gens enc enc_injective _ A2X a2gen
      (fun y => (A2X_iff y).symm) a2g_A2X (fun y hy => (A2X_iff y).1 hy), nrmTestGens,
      List.all_eq_true]
    intro a ha
    rw [decide_eq_true_eq]
    exact List.mem_map_of_mem (gen_norm k2gen A2X k2c hA2 kN2 g hg a (a2g_A2X a ha)).1
  exact hle ((hK2.2.2 x).1 hx)

private theorem k2_facts : K2X.length = 1152 ∧
    strictAsc ((K2X.map enc).mergeSort (fun a b => decide (a ≤ b))) = true ∧
    (∀ x ∈ K2X, nrmTestGens enc (A2X.map enc) a2gen x = true) ∧ (∀ x ∈ K2X, x • F2X = F2X) := by
  refine ⟨len_of hK2.2.1 lK2, strictAsc_nat (hK2.1.map enc_injective), fun x hx => ?_,
    fun x hx => fix_closure k2gen F2X (gen_fix k2gen k2c F2X hF2 kF2) x ((hK2.2.2 x).1 hx)⟩
  exact (mem_normalizer_of_gens enc enc_injective _ A2X a2gen (fun y => (A2X_iff y).symm)
    a2g_A2X (fun y hy => (A2X_iff y).1 hy) x).1 (k2_norm x hx)

private theorem q2_facts :
    strictAsc ((A2X.map enc).mergeSort (fun a b => decide (a ≤ b))) = true ∧
    (∀ q ∈ A2X, enc q ∈ K2X.map enc) ∧ (1 : XJ) ∈ A2X ∧
    (∀ p ∈ A2X, ∀ q ∈ A2X, enc (p * q) ∈ A2X.map enc) ∧
    (∀ k ∈ k2gen, ∀ q ∈ A2X,
      enc (k * q * k⁻¹) ∈ A2X.map enc ∧ enc (k⁻¹ * q * k) ∈ A2X.map enc) ∧
    (∀ q ∈ A2X, q ^ (2 ^ 2) = 1) ∧
    (∀ y ∈ K2X, (∀ q ∈ A2X, enc (y * q) = enc (q * y)) → enc y ∈ A2X.map enc) ∧
    (∀ b ∈ K2X, b ≠ 1 → b ^ 3 = 1 →
      4 < ((A2X.map fun q => enc (q * b * q⁻¹ * b⁻¹)).dedup).length) ∧
    K2X.length / A2X.length = 18 := by
  have hnd : A2X.Nodup := hS.1.filter _
  refine ⟨strictAsc_nat (hnd.map enc_injective), fun q hq => ?_, ?_, fun p hp q hq => ?_,
    fun k hk q hq => ?_, fun q hq => ?_, fun y hy hc => ?_, fun b hb h1 h3 => ?_, ?_⟩
  · rw [mem_encJ hK2.2.1, ← memL_iff]
    exact (allL_iff _ _).1 kAK _ ((mem_cJ hA2 q).1 hq)
  · rw [mem_cJ hA2, cJ_one, ← memL_iff]
    exact kA1
  · exact List.mem_map_of_mem ((A2X_iff _).2 (Subgroup.mul_mem _ ((A2X_iff p).1 hp)
      ((A2X_iff q).1 hq)))
  · have k := gen_norm k2gen A2X k2c hA2 kN2 k hk q hq
    exact ⟨List.mem_map_of_mem k.1, List.mem_map_of_mem k.2⟩
  · apply cJ_injective
    rw [cJ_sq, cJ_one]
    exact Nat.eq_of_beq_eq_true ((allL_iff _ _).1 kAe _ ((mem_cJ hA2 q).1 hq))
  · rw [mem_encJ hA2, ← memL_iff]
    refine impB_true (fK2_parts (fK2_at hy)).1 ((allL_iff _ _).2 fun c hcm => ?_)
    rw [← a2c] at hcm
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hcm
    have e : y * q = q * y := enc_injective (hc q (a2g_A2X q hq))
    change Nat.beq (mulW 315 9 (cJ y) (cJ q)) (mulW 315 9 (cJ q) (cJ y)) = true
    exact beq_of_eq (by rw [← cJ_mul, ← cJ_mul, e])
  · have h := impB_true (fK2_parts (fK2_at hb)).2 (ord3_of h1 h3)
    have e : (A2X.map fun q => enc (q * b * q⁻¹ * b⁻¹)) =
        (A2X.map cJ).map (fun q => encW 315 9 (cmW q (cJ b))) := map_cJ A2X _ _ fun q => by
      rw [enc_cJ, cJ_cm]
    rw [e, ((hA2.map _).dedup).length_eq]
    exact fiveK_sound _ _ h
  · rw [len_of hK2.2.1 lK2, len_of hA2 lA'.2.2]

private theorem gen_facts :
    (jLetters.all fun g => (K1X ++ K2X).any fun x => enc x == enc g) = true ∧
    evalW jLetters wordA = paC ∧ evalW jLetters wordB = pbC := by
  have hj : jLetters.map cJ = List.append S0G [t1C, t2C] := by
    rw [jLetters, List.map_append, s0c, List.map_cons, List.map_cons, List.map_nil, t1c, t2c]
    rfl
  refine ⟨List.all_eq_true.2 fun g hg => List.any_eq_true.2 ⟨g, ?_, beq_self_eq_true _⟩, ?_, ?_⟩
  · rw [jLetters, List.mem_append, List.mem_cons, List.mem_singleton] at hg
    rcases hg with hg | rfl | rfl
    · exact List.mem_append_left _ ((hK1.2.2 g).2 (Subgroup.subset_closure
        (List.mem_append_left _ hg)))
    · exact List.mem_append_left _ ((hK1.2.2 _).2 (Subgroup.subset_closure
        (List.mem_append_right _ (List.mem_singleton_self _))))
    · exact List.mem_append_right _ ((hK2.2.2 _).2 (Subgroup.subset_closure
        (List.mem_append_right _ (List.mem_singleton_self _))))
  · apply cJ_injective
    rw [cJ_evalW, hj, kwA, cJ_paC]
  · apply cJ_injective
    rw [cJ_evalW, hj, kwB, cJ_pbC]

end CFSG.KD.LQT.C4091

namespace Certificates

open CFSG CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native CFSG.QuasithinUnique.Vol2Native.L239 CFSG.QuasithinUnique.Vol2Native.L239.J2Pairs in
open scoped Pointwise in
open CFSG.Sporadic.Schreier in
theorem certificate4091 : (S0X.length = 128 ∧
          strictAsc ((S0X.map enc).mergeSort (fun a b => decide (a ≤ b))) = true ∧ (1 : CFSG.QuasithinUnique.Vol2Native.L239.J2Pairs.XJ) ∈ S0X ∧
          (∀ x ∈ S0X, ∀ g ∈ s0gen, enc (x * g) ∈ S0X.map enc) ∧ (∀ x ∈ S0X, x ^ (2 ^ 3) = 1))
    ∧ (A1X.length = 2 ∧ Z2X.length = 4 ∧ A2X.length = 64 ∧
          (∀ a ∈ a2gen, enc a ∈ A2X.map enc) ∧ (∀ y ∈ A2X, enc y ∈ A2cl.map enc))
    ∧ (K1X.length = 1920 ∧
          strictAsc ((K1X.map enc).mergeSort (fun a b => decide (a ≤ b))) = true ∧
          (∀ x ∈ K1X, ∀ a ∈ A1X, enc (x * a * x⁻¹) ∈ A1X.map enc ∧ enc (x⁻¹ * a * x) ∈ A1X.map enc) ∧
          (∀ x ∈ K1X, x • F1X = F1X))
    ∧ (Reach CFSG.QuasithinUnique.Vol2Native.L239.J2Pairs.gensA F1X orb1.1 orb1.2.1 orb1.2.2 ∧ orb1.1.length = 315 ∧
          strictAsc ((orb1.1.map CFSG.QuasithinUnique.Vol2Native.L239.J2Pairs.maskF).mergeSort (fun a b => decide (a ≤ b))) = true)
    ∧ (K2X.length = 1152 ∧
          strictAsc ((K2X.map enc).mergeSort (fun a b => decide (a ≤ b))) = true ∧
          (∀ x ∈ K2X, nrmTestGens enc (A2X.map enc) a2gen x = true) ∧ (∀ x ∈ K2X, x • F2X = F2X))
    ∧ (Reach CFSG.QuasithinUnique.Vol2Native.L239.J2Pairs.gensA F2X orb2.1 orb2.2.1 orb2.2.2 ∧ orb2.1.length = 525 ∧
          strictAsc ((orb2.1.map CFSG.QuasithinUnique.Vol2Native.L239.J2Pairs.maskF).mergeSort (fun a b => decide (a ≤ b))) = true)
    ∧ (Q1X.length = 32 ∧
          strictAsc ((Q1X.map enc).mergeSort (fun a b => decide (a ≤ b))) = true ∧
          (∀ q ∈ Q1X, enc q ∈ K1X.map enc) ∧ (1 : CFSG.QuasithinUnique.Vol2Native.L239.J2Pairs.XJ) ∈ Q1X ∧
          (∀ p ∈ Q1X, ∀ q ∈ Q1X, enc (p * q) ∈ Q1X.map enc) ∧
          (∀ k ∈ k1gen, ∀ q ∈ Q1X,
            enc (k * q * k⁻¹) ∈ Q1X.map enc ∧ enc (k⁻¹ * q * k) ∈ Q1X.map enc) ∧
          (∀ q ∈ Q1X, q ^ (2 ^ 2) = 1) ∧
          (∀ y ∈ K1X, (∀ q ∈ Q1X, enc (y * q) = enc (q * y)) → enc y ∈ Q1X.map enc) ∧
          (∀ b ∈ K1X, b ≠ 1 → b ^ 3 = 1 → ∃ p ∈ Q1X, ∃ q ∈ Q1X,
            enc ((p * b * p⁻¹ * b⁻¹) * (q * b * q⁻¹ * b⁻¹)) ≠
              enc ((q * b * q⁻¹ * b⁻¹) * (p * b * p⁻¹ * b⁻¹)) ∨
            enc ((p * b * p⁻¹ * b⁻¹) * (p * b * p⁻¹ * b⁻¹)) ≠ enc 1))
    ∧ (strictAsc ((A2X.map enc).mergeSort (fun a b => decide (a ≤ b))) = true ∧
          (∀ q ∈ A2X, enc q ∈ K2X.map enc) ∧ (1 : CFSG.QuasithinUnique.Vol2Native.L239.J2Pairs.XJ) ∈ A2X ∧
          (∀ p ∈ A2X, ∀ q ∈ A2X, enc (p * q) ∈ A2X.map enc) ∧
          (∀ k ∈ k2gen, ∀ q ∈ A2X,
            enc (k * q * k⁻¹) ∈ A2X.map enc ∧ enc (k⁻¹ * q * k) ∈ A2X.map enc) ∧
          (∀ q ∈ A2X, q ^ (2 ^ 2) = 1) ∧
          (∀ y ∈ K2X, (∀ q ∈ A2X, enc (y * q) = enc (q * y)) → enc y ∈ A2X.map enc) ∧
          (∀ b ∈ K2X, b ≠ 1 → b ^ 3 = 1 →
            4 < ((A2X.map fun q => enc (q * b * q⁻¹ * b⁻¹)).dedup).length) ∧
          K2X.length / A2X.length = 18)
    ∧ ((CFSG.QuasithinUnique.Vol2Native.L239.J2Pairs.jLetters.all fun g => (K1X ++ K2X).any fun x => enc x == enc g) = true ∧
          evalW CFSG.QuasithinUnique.Vol2Native.L239.J2Pairs.jLetters wordA = paC ∧ evalW CFSG.QuasithinUnique.Vol2Native.L239.J2Pairs.jLetters wordB = pbC) :=
  ⟨CFSG.KD.LQT.C4091.s0_facts, CFSG.KD.LQT.C4091.a_facts, CFSG.KD.LQT.C4091.k1_facts,
    CFSG.KD.LQT.C4091.orb1_facts, CFSG.KD.LQT.C4091.k2_facts, CFSG.KD.LQT.C4091.orb2_facts,
    CFSG.KD.LQT.C4091.q1_facts, CFSG.KD.LQT.C4091.q2_facts, CFSG.KD.LQT.C4091.gen_facts⟩

end Certificates

end
