module

public import Certificates.Kernel.A45Cls.Checks
public import CFSG.Certificates.Kernel.A45Cls.DefsSound
public import CFSG.Certificates.Kernel.OrbFindSound
public import CFSG.Certificates.Kernel.ConjOrbSound
public import CFSG.Certificates.Kernel.PermCent.SylowReps
public import CFSG.Certificates.Kernel.PermCent.CVSound
public import CFSG.Sporadic.SmallOddCore.GroupFacts
public import Certificates.Certificate2012
public import CFSG.Certificates.Kernel.Spor.RawOrbGrp

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelA45

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw.Orb CFSG.KC.OrbFind CFSG.KC.OrbGroup CFSG.KC.ConjOrb
  CFSG.KC.LeftOrb CFSG.KC.BfsPin CFSG.KC.A45Cls CFSG.Certificates.Kernel.PkCV
  CFSG.ComponentClassification.CatFactsSmall.PSp43 CFSG.Sporadic.SmallOddCore CFSG.Certificates
  CFSG.Sporadic.Schreier CFSG.GH74.KGroups CFSG.KC.SylowReps Subgroup

local notation "P45" => Equiv.Perm (Fin 45)

abbrev A : Subgroup P45 := QA45.originalSubgroup

@[expose] def gA' (k : ℕ) : P45 := [x45, y45, f45].getD k 1

@[expose] def sg (k : ℕ) : P45 := ((sW.getD k []).map gA').prod

@[expose] def cg (k : ℕ) : P45 := ((cW.getD k []).map gA').prod

abbrev sylS : Subgroup P45 := Subgroup.closure (sg '' {k | k < 4})

@[expose] def tauFix (m : ℕ) : ℕ :=
  if m = 13 then 1152 else if m = 5 then 192 else if m = 15 then 1440 else if m = 7 then 96 else 0

@[expose] def InCls (x : P45) : Prop :=
  ∃ t ∈ [Certificates.P43Twin.tA (), Certificates.P43Twin.tB (), Certificates.P43Twin.t36 (),
    Certificates.P43Twin.t540 ()], ∃ g ∈ A, x = g * t * g⁻¹

theorem hn45 : (45 : ℕ) < 2 ^ 32 := by norm_num

theorem ps_lt : ∀ p ∈ ps, p < 45 := by decide

theorem wC45 : wC 45 = 6 := by
  have e : Nat.log2 (45 + 1) = 5 := (Nat.log2_eq_iff (by norm_num)).2 ⟨by norm_num, by norm_num⟩
  unfold wC
  rw [e]

theorem prep_cOf (σ : P45) : PRep 45 6 (cOf σ).1 σ := by
  intro x
  have h := ev_apply (cOf σ) x
  rw [ev_cOf] at h
  rw [h]
  change pg 6 (mask 6) (cOf σ).1 x = pg (wC 45) (mask (wC 45)) (cOf σ).1 x
  rw [wC45]

theorem card_A : Nat.card A = 51840 := by
  rw [card_group QA45 Certificates.certificate2012.2.1.1,
    Certificates.certificate2012.2.1.2]

theorem closure_gA : Subgroup.closure (gA' '' {k | k < 3}) = A := by
  change Subgroup.closure _ = QA45.originalSubgroup
  rw [QA45, certificate_originalSubgroup]
  congr 1
  ext g
  simp only [Set.mem_image, Set.mem_setOf_eq, List.mem_cons, List.not_mem_nil, or_false, tab_eq]
  constructor
  · rintro ⟨k, hk, rfl⟩
    interval_cases k
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  · rintro (rfl | rfl | rfl)
    · exact ⟨0, by norm_num, rfl⟩
    · exact ⟨1, by norm_num, rfl⟩
    · exact ⟨2, by norm_num, rfl⟩

theorem gA'_mem {k : ℕ} (hk : k < 3) : gA' k ∈ A := by
  rw [← closure_gA]
  exact Subgroup.subset_closure ⟨k, hk, rfl⟩

theorem prep_gA : ∀ k < 3, PRep 45 6 (KA.G k) (gA' k) := by
  obtain ⟨bx, byy, bf, -⟩ := binds
  intro k hk
  interval_cases k
  · rw [← bx]
    exact prep_cOf x45
  · rw [← byy]
    exact prep_cOf y45
  · rw [← bf]
    exact prep_cOf f45

theorem prep_gens {G : ℕ → ℕ} (h0 : G 0 = KA.G 0) (h1 : G 1 = KA.G 1) (h2 : G 2 = KA.G 2) :
    ∀ k < 3, PRep 45 6 (G k) (gA' k) := by
  intro k hk
  interval_cases k
  · rw [h0]
    exact prep_gA 0 (by norm_num)
  · rw [h1]
    exact prep_gA 1 (by norm_num)
  · rw [h2]
    exact prep_gA 2 (by norm_num)

theorem prep_word {G : ℕ → ℕ} {ws : List (List ℕ)} (hb : bindWs 45 6 3 KA.G G ws 0 = true)
    {j : ℕ} (hj : j < ws.length) :
    PRep 45 6 (G j) ((ws.getD j []).map gA').prod ∧ ((ws.getD j []).map gA').prod ∈ A := by
  obtain ⟨hl, he⟩ := bindWs_spec hb j hj
  rw [Nat.zero_add] at he
  rw [List.getD_eq_getElem _ _ hj, he]
  refine ⟨wordK_prep (by norm_num) (by norm_num) _ fun k hk => prep_gA k (hl k hk), ?_⟩
  refine list_prod_mem fun y hy => ?_
  obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hy
  exact gA'_mem (hl k hk)

theorem conj_closed_A {X : Type*} [Group X] [Finite X] {s O : Set X}
    (hs : ∀ g ∈ s, ∀ x ∈ O, g * x * g⁻¹ ∈ O) : ∀ g ∈ Subgroup.closure s, ∀ x ∈ O, g * x * g⁻¹ ∈ O := by
  intro d hd
  induction hd using Subgroup.closure_induction with
  | mem x hx => exact hs x hx
  | one =>
    intro y hy
    rw [one_mul, inv_one, mul_one]
    exact hy
  | mul a b _ _ ha hb =>
    intro y hy
    have e : a * b * y * (a * b)⁻¹ = a * (b * y * b⁻¹) * a⁻¹ := by group
    rw [e]
    exact ha _ (hb y hy)
  | inv a _ ha =>
    intro y hy
    obtain ⟨z, hz, e⟩ := surj_of_mapsTo (fun z => a * z * a⁻¹)
      (fun u v e => by simpa using e) ha y hy
    have e2 : a⁻¹ * y * a⁻¹⁻¹ = z := by
      rw [← e]
      group
    rw [e2]
    exact hz

theorem class_A {N r : ℕ} {G GI T E D S : ℕ → ℕ} {t : P45}
    (hh : headK 45 6 3 G GI = true) (hg : ∀ k < 3, PRep 45 6 (G k) (gA' k))
    (hcl : ∀ i < N, closPt 45 6 3 N G GI T E i = true)
    (htr : ∀ i < N, treePt 3 N r E D i = true) (hr : r < N) (ht : PRep 45 6 (T r) t)
    (hK : distinctK N (fun i => pkeyK 45 6 ps (T i)) S = true) :
    N * Nat.card ↥(A ⊓ centralizer ({t} : Set P45)) = 51840 ∧
      ∀ i < N, ∀ v, PRep 45 6 (T i) v → ∃ g ∈ A, v = g * t * g⁻¹ := by
  obtain ⟨c, hc, hreach, hcl', hinj⟩ := conjOrb_reps (g := gA') (t := t) hn45 hh hg hcl htr
    hr ht ps_lt hK
  rw [closure_gA] at hreach
  have hcr : c r = t := prep_eq (hc r hr) ht
  have hset : conjClass A t = {y | ∃ i < N, c i = (MonoidHom.id _) y} := by
    ext x
    constructor
    · rintro ⟨g, hg', rfl⟩
      rw [← closure_gA] at hg'
      refine conj_closed_A (O := {y | ∃ i < N, c i = (MonoidHom.id _) y}) ?_ g hg' t
        ⟨r, hr, hcr⟩
      rintro _ ⟨k, hk, rfl⟩ _ ⟨i, hi, rfl⟩
      obtain ⟨j, hj, e⟩ := hcl' i hi k hk
      exact ⟨j, hj, e.symm⟩
    · rintro ⟨i, hi, e⟩
      obtain ⟨h, hh', e2⟩ := hreach i hi
      exact ⟨h, hh', by rw [← e2]; exact e.symm⟩
  have hN := ncard_of_reps (MonoidHom.id _) (fun _ _ h => h) c (fun i _ => ⟨c i, rfl⟩) hinj
  rw [← hset] at hN
  have hmul := ncard_conjClass_mul_card A t
  rw [hN, card_A] at hmul
  refine ⟨hmul, fun i hi v hv => ?_⟩
  obtain ⟨h, hh', e2⟩ := hreach i hi
  exact ⟨h, hh', by rw [prep_eq hv (hc i hi), e2]⟩

theorem group_A {N ng : ℕ} {G T E D S : ℕ → ℕ} {g : ℕ → P45}
    (hg : ∀ k < ng, PRep 45 6 (G k) (g k))
    (hcl : ∀ i < N, closPtL 45 6 ng N G T E i = true)
    (htr : ∀ i < N, treePt ng N 0 E D i = true) (hN : 0 < N) (h0 : T 0 = pidn 45 6)
    (hK : distinctK N (fun i => pkeyK 45 6 ps (T i)) S = true) :
    Nat.card (closure (g '' {k | k < ng})) = N ∧
      ∀ y ∈ Subgroup.closure (g '' {k | k < ng}), ∃ i < N, PRep 45 6 (T i) y := by
  have hid : PRep 45 6 (T 0) 1 := by
    rw [h0]
    exact prep_pidn (by norm_num) (by norm_num)
  obtain ⟨c, hc0, hc, hmem, hcl', hinj⟩ := leftOrb_reps (g := g) hn45 hg hcl htr hN hid ps_lt hK
  obtain ⟨hcard, hall⟩ := group_of_reps (MonoidHom.id _) (fun _ _ h => h) g c ⟨0, hN, hc0⟩ hmem
    hcl' hinj
  refine ⟨hcard, fun y hy => ?_⟩
  obtain ⟨i, hi, e⟩ := hall y hy
  have e' : c i = y := e
  exact ⟨i, hi, by rw [← e']; exact hc i hi⟩

theorem cls_tA :
    45 * Nat.card ↥(A ⊓ centralizer ({Certificates.P43Twin.tA ()} : Set P45)) = 51840 ∧
      ∀ i < 45, ∀ v, PRep 45 6 (KA.T i) v →
        ∃ g ∈ A, v = g * Certificates.P43Twin.tA () * g⁻¹ := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, bt, -⟩ := binds
  exact class_A KA.h prep_gA KA.cl KA.tr0 (by decide) (by rw [← bt]; exact prep_cOf _) KA.k

theorem cls_tB :
    270 * Nat.card ↥(A ⊓ centralizer ({Certificates.P43Twin.tB ()} : Set P45)) = 51840 ∧
      ∀ i < 270, ∀ v, PRep 45 6 (KB.T i) v →
        ∃ g ∈ A, v = g * Certificates.P43Twin.tB () * g⁻¹ := by
  obtain ⟨-, -, -, h0, h1, h2, -, -, -, -, -, -, -, bt, -⟩ := binds
  exact class_A KB.h (prep_gens h0 h1 h2) KB.cl KB.tr0 (by decide)
    (by rw [← bt]; exact prep_cOf _) KB.k

theorem cls_t36 :
    36 * Nat.card ↥(A ⊓ centralizer ({Certificates.P43Twin.t36 ()} : Set P45)) = 51840 ∧
      ∀ i < 36, ∀ v, PRep 45 6 (K36.T i) v →
        ∃ g ∈ A, v = g * Certificates.P43Twin.t36 () * g⁻¹ := by
  obtain ⟨-, -, -, -, -, -, h0, h1, h2, -, -, -, -, -, bt, -⟩ := binds
  exact class_A K36.h (prep_gens h0 h1 h2) K36.cl K36.tr0 (by decide)
    (by rw [← bt]; exact prep_cOf _) K36.k

theorem cls_t540 :
    540 * Nat.card ↥(A ⊓ centralizer ({Certificates.P43Twin.t540 ()} : Set P45)) = 51840 ∧
      ∀ i < 540, ∀ v, PRep 45 6 (K540.T i) v →
        ∃ g ∈ A, v = g * Certificates.P43Twin.t540 () * g⁻¹ := by
  obtain ⟨-, -, -, -, -, -, -, -, -, h0, h1, h2, -, -, -, bt⟩ := binds
  exact class_A K540.h (prep_gens h0 h1 h2) K540.cl K540.tr0 (by decide)
    (by rw [← bt]; exact prep_cOf _) K540.k

theorem inCls_of_memCls {v : ℕ} {x : P45} (hv : PRep 45 6 v x)
    (h : memCls v = true) : InCls x := by
  unfold memCls at h
  simp only [Bool.or_eq_true] at h
  rcases h with ((h | h) | h) | h
  · obtain ⟨j, hj, e⟩ := memK_spec h
    obtain ⟨g, hg, e2⟩ := cls_tA.2 j hj x (by rw [e]; exact hv)
    exact ⟨_, List.mem_cons_self, g, hg, e2⟩
  · obtain ⟨j, hj, e⟩ := memK_spec h
    obtain ⟨g, hg, e2⟩ := cls_tB.2 j hj x (by rw [e]; exact hv)
    exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, g, hg, e2⟩
  · obtain ⟨j, hj, e⟩ := memK_spec h
    obtain ⟨g, hg, e2⟩ := cls_t36.2 j hj x (by rw [e]; exact hv)
    exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), g, hg, e2⟩
  · obtain ⟨j, hj, e⟩ := memK_spec h
    obtain ⟨g, hg, e2⟩ := cls_t540.2 j hj x (by rw [e]; exact hv)
    exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      List.mem_cons_self)), g, hg, e2⟩

theorem prep_sg : ∀ k < 4, PRep 45 6 (SY.G k) (sg k) ∧ sg k ∈ A :=
  fun _ hk => prep_word words.1 hk

theorem sylS_le : sylS ≤ A := by
  rw [Subgroup.closure_le]
  rintro _ ⟨k, hk, rfl⟩
  exact (prep_sg k hk).2

theorem sylS_facts : Nat.card sylS = 128 ∧ ∀ y ∈ sylS, ∃ i < 128, PRep 45 6 (SY.T i) y :=
  group_A (fun k hk => (prep_sg k hk).1) SY.cl SY.tr (by norm_num) ids.1 SY.k

theorem card_sylS : Nat.card sylS = 128 := sylS_facts.1

theorem inCls_of_inv {x : P45} (hx : x ∈ A) (h2 : x * x = 1)
    (h1 : x ≠ 1) : InCls x := by
  have hΦ : ∀ g ∈ A, ∀ x ∈ A, (fun y => y * y = 1 → y ≠ 1 → InCls y) (g * x * g⁻¹) →
      (fun y => y * y = 1 → y ≠ 1 → InCls y) x := by
    intro g hg x _ h hx2 hx1
    have e : x = g⁻¹ * (g * x * g⁻¹) * g := by group
    have hs : g * x * g⁻¹ * (g * x * g⁻¹) = 1 := by
      calc g * x * g⁻¹ * (g * x * g⁻¹) = g * (x * x) * g⁻¹ := by group
        _ = 1 := by rw [hx2]; group
    have hn : g * x * g⁻¹ ≠ 1 := by
      intro h0
      apply hx1
      rw [e, h0]
      group
    obtain ⟨t, ht, k, hk, e2⟩ := h hs hn
    refine ⟨t, ht, g⁻¹ * k, mul_mem (inv_mem hg) hk, ?_⟩
    rw [e, e2]
    group
  have hT : ∀ y ∈ sylS, (fun y => y * y = 1 → y ≠ 1 → InCls y) y := by
    intro y hy hy2 hy1
    obtain ⟨i, hi, hp⟩ := sylS_facts.2 y hy
    have hc := allN_spec cover i (by rw [orders.2.2.2.2.2.2.2.2.1]; exact hi)
    rw [strictB_eq', Bool.or_eq_true] at hc
    rcases hc with hc | hc
    · have ho : orderOf y = 2 := orderOf_eq_prime (by rw [sq]; exact hy2) hy1
      rw [← isInvK_iff hn45 hp] at ho
      rw [ho] at hc
      exact absurd hc (by decide)
    · exact inCls_of_memCls hp hc
  refine forall_of_sylow A sylS Nat.prime_two sylS_le (k := 7) (m := 405)
    (by rw [card_sylS]; norm_num) (by rw [card_A]; norm_num) (by decide) _ hΦ hT x hx ?_ h2 h1
  rw [show 2 ^ 7 = 2 * 64 by norm_num, pow_mul, sq, h2, one_pow]

theorem card_cent_conj {g t : P45} (hg : g ∈ A) :
    Nat.card ↥(A ⊓ centralizer ({g * t * g⁻¹} : Set P45)) =
      Nat.card ↥(A ⊓ centralizer ({t} : Set P45)) := by
  rw [inf_centralizer_conj A hg t]
  exact Subgroup.card_map_of_injective (MulEquiv.injective (MulAut.conj g))

theorem fix_tA : fixC (Certificates.P43Twin.tA ()) = 13 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, bt, -⟩ := binds
  rw [← fixK_eq (prep_cOf _), bt]
  exact fixes.1

theorem fix_tB : fixC (Certificates.P43Twin.tB ()) = 5 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, bt, -⟩ := binds
  rw [← fixK_eq (prep_cOf _), bt]
  exact fixes.2.1

theorem fix_t36 : fixC (Certificates.P43Twin.t36 ()) = 15 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, bt, -⟩ := binds
  rw [← fixK_eq (prep_cOf _), bt]
  exact fixes.2.2.1

theorem fix_t540 : fixC (Certificates.P43Twin.t540 ()) = 7 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, bt⟩ := binds
  rw [← fixK_eq (prep_cOf _), bt]
  exact fixes.2.2.2

theorem card_cent_eq {x : P45} (hx : x ∈ A) (h2 : x * x = 1)
    (h1 : x ≠ 1) : Nat.card ↥(A ⊓ centralizer ({x} : Set P45)) = tauFix (fixC x) := by
  obtain ⟨t, ht, g, hg, rfl⟩ := inCls_of_inv hx h2 h1
  rw [card_cent_conj hg, fixC_conj]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl
  · rw [fix_tA, show tauFix 13 = 1152 from rfl]
    have := cls_tA.1
    omega
  · rw [fix_tB, show tauFix 5 = 192 from rfl]
    have := cls_tB.1
    omega
  · rw [fix_t36, show tauFix 15 = 1440 from rfl]
    have := cls_t36.1
    omega
  · rw [fix_t540, show tauFix 7 = 96 from rfl]
    have := cls_t540.1
    omega

theorem comm_of_eq22 {P Q : ℕ} {g h : P45} (hP : PRep 45 6 P g) (hQ : PRep 45 6 Q h)
    (hc : eq22 45 6 (mask 6) P Q Q P = true) : g * h = h * g := by
  unfold eq22 at hc
  rw [allN_iff] at hc
  refine Equiv.ext fun x => Fin.ext ?_
  have := Nat.eq_of_beq_eq_true (hc x x.2)
  rw [hQ x, hP (h x), hP x, hQ (g x)] at this
  exact this

theorem prep_cg : ∀ k < 3, PRep 45 6 (CA.G k) (cg k) ∧ cg k ∈ A :=
  fun _ hk => prep_word words.2 hk

theorem centA_eq :
    Subgroup.closure (cg '' {k | k < 3}) = A ⊓ centralizer ({Certificates.P43Twin.tA ()} : Set P45) ∧
      Nat.card ↥(A ⊓ centralizer ({Certificates.P43Twin.tA ()} : Set P45)) = 1152 ∧
      ∀ y ∈ A ⊓ centralizer ({Certificates.P43Twin.tA ()} : Set P45),
        ∃ i < 1152, PRep 45 6 (CA.T i) y := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, bt, -⟩ := binds
  have htA : PRep 45 6 (KA.T KA.r0) (Certificates.P43Twin.tA ()) := by
    rw [← bt]
    exact prep_cOf _
  have hC : Nat.card ↥(A ⊓ centralizer ({Certificates.P43Twin.tA ()} : Set P45)) = 1152 := by
    have := cls_tA.1
    omega
  obtain ⟨hcard, hall⟩ := group_A (fun k hk => (prep_cg k hk).1) CA.cl CA.tr (by norm_num)
    ids.2 CA.k
  have hle : Subgroup.closure (cg '' {k | k < 3}) ≤
      A ⊓ centralizer ({Certificates.P43Twin.tA ()} : Set P45) := by
    rw [Subgroup.closure_le]
    rintro _ ⟨k, hk, rfl⟩
    refine mem_inf.2 ⟨(prep_cg k hk).2, mem_centralizer_singleton_iff.2 ?_⟩
    exact comm_of_eq22 (prep_cg k hk).1 htA (allN_spec cent k hk)
  have heq : Subgroup.closure (cg '' {k | k < 3}) =
      A ⊓ centralizer ({Certificates.P43Twin.tA ()} : Set P45) :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hC, hcard])
  refine ⟨heq, hC, fun y hy => ?_⟩
  rw [← heq] at hy
  exact hall y hy

end CertificateChecks.KernelA45

end
