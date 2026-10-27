module

public import Certificates.Kernel.B433Alt.FiveSem
public import Certificates.Kernel.B433Alt.FiveC
public import Certificates.Kernel.B433Alt.Chains
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabBFiveCentSyl
public import CFSG.Certificates.Kernel.Common.ForallTree
public import CFSG.YGroups.Model233F

set_option maxRecDepth 100000

public section

namespace CertificateChecks.KernelB433

open CFSG.KC.B4A CFSG.KC.B433Alt CFSG.YGroups CFSG.Certificates.CosetEnumeration
  CertificateChecks.KernelY442 CFSG.KC.Y333 CFSG.KD.B4AF

#kc_forall_tree five_ok (fun k => CFSG.KD.B4AF.nodeChk k = true) 17 CFSG.KD.B4AF.five

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 1000000 in
theorem five_data : FJ.length = 17 ∧ ∀ k < 17,
    (FA.getD k 0 = 1 ∨ FA.getD k 0 = 2) ∧ (PX.getD k []).length = FA.getD k 0 ∧
    (∀ i < 6, (PQ.getD k []).getD i 0 < 31671) ∧
    (∀ l < (NB.getD k []).length, (NB.getD k []).getD l 0 < 31671) ∧
    (NP.getD k []).length = (NB.getD k []).length ∧
    (∀ l < (NB.getD k []).length, ∀ g < (lg k l).length, ∀ i < 4,
      (((NE.getD k []).getD l []).getD g []).getD i 0 < 5) ∧
    (∀ e < (EQ.getD k []).length, 0 < (EQ.getD k []).getD e 0 ∧
      (∀ i < 4, ((EE.getD k []).getD e []).getD i 0 < 5) ∧
      (∀ p < (EQ.getD k []).getD e 0 + 1, ¬ (1 < p ∧ (∀ d < p, 1 < d → ¬ d ∣ p) ∧
        p ∣ (EQ.getD k []).getD e 0 ∧ p ∉ (EF.getD k []).getD e [])) ∧
      (∀ i < ((EF.getD k []).getD e []).length, (((EP.getD k []).getD e []).getD i 0) < 31671)) ∧
    0 < FB.getD k 0 := by
  decide +kernel


@[expose] noncomputable def Kof (j : ℕ) : Subgroup (Equiv.Perm (Fin 31671)) := (nodeSub j).map rho432F

theorem recP_mem {j : ℕ} : ∀ {refs : List ℕ}, refsOK j refs = true → recP refs ∈ Kof j
  | [], _ => Subgroup.one_mem _
  | r :: refs, h => by
    change andB (andB (isStab (dKind (CFSG.KD.B4A.RD (Nat.div r 2))))
      (Nat.beq (dN2 (CFSG.KD.B4A.RD (Nat.div r 2))) j)) (refsOK j refs) = true at h
    simp only [andB_iff] at h
    obtain ⟨⟨hs, hj⟩, hr⟩ := h
    have hg : rho432F (wVal (yGen 4 3 2) (CFSG.KD.B4A.RW (r / 2))) ∈ Kof j :=
      ⟨_, Subgroup.subset_closure ⟨r / 2, ⟨hs, Nat.eq_of_beq_eq_true hj⟩, rfl⟩, rfl⟩
    refine Subgroup.mul_mem _ ?_ (recP_mem hr)
    unfold recV
    split_ifs
    · exact Subgroup.inv_mem _ hg
    · exact hg

theorem refs_wInH {j : ℕ} : ∀ {refs : List ℕ}, refsOK j refs = true →
    ∀ r ∈ refs, wInH (CFSG.KD.B4A.RW (r / 2)) = true
  | [], _ => fun _ h => absurd h List.not_mem_nil
  | r :: refs, h => by
    change andB (andB (isStab (dKind (CFSG.KD.B4A.RD (Nat.div r 2))))
      (Nat.beq (dN2 (CFSG.KD.B4A.RD (Nat.div r 2))) j)) (refsOK j refs) = true at h
    simp only [andB_iff] at h
    intro r' hr'
    rcases List.mem_cons.1 hr' with rfl | hr'
    · exact rw_stab _ h.1.1
    · exact refs_wInH h.2 r' hr'

section

theorem node_parts {k : ℕ} (hk : k < 17) : tChk k = true ∧ pChk k = true ∧
    (∀ l < (NB.getD k []).length, levelChk k l = true) ∧
    (∀ e < (EQ.getD k []).length, CFSG.KD.B4AF.finChk k e = true) ∧
    FB.getD k 0 = orbProd k * ordLcm k := by
  have h := five_ok k hk
  unfold nodeChk at h
  simp only [andB_iff, belowAll_iff] at h
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, Nat.eq_of_beq_eq_true h.2.2.2.2⟩

theorem tW_lt {k : ℕ} (hk : k < 17) : ∀ t, ∀ c ∈ tW k t, c < 10 := by
  intro t
  have h := (node_parts hk).1
  unfold tChk at h
  rw [belowAll_iff] at h
  by_cases ht : t < (TW.getD k []).length
  · have h1 := h t ht
    rw [andB_iff] at h1
    exact lettersOK_iff.1 h1.1
  · rw [tW, List.getD_eq_default (TW.getD k []) [] (by omega : (TW.getD k []).length ≤ t)]
    intro c hc
    exact absurd hc List.not_mem_nil

@[expose] noncomputable def el (k : ℕ) (refs : List ℕ) : Equiv.Perm (Fin 31671) := tv (tW k) refs

theorem ev_spec {k : ℕ} (hk : k < 17) (refs : List ℕ) (x : ℕ) (hx : x < 31671) :
    (el k refs ⟨x, hx⟩ : ℕ) = ev k refs x :=
  evT_spec (tW_lt hk) refs x hx

theorem evI_spec {k : ℕ} (hk : k < 17) (refs : List ℕ) (x : ℕ) (hx : x < 31671) :
    ((el k refs)⁻¹ ⟨x, hx⟩ : ℕ) = evI k refs x :=
  evTI_spec (tW_lt hk) refs x hx

theorem ev_lt {k : ℕ} (hk : k < 17) (refs : List ℕ) {x : ℕ} (hx : x < 31671) : ev k refs x < 31671 := by
  rw [← ev_spec hk refs x hx]; exact Fin.isLt _

theorem evI_lt {k : ℕ} (hk : k < 17) (refs : List ℕ) {x : ℕ} (hx : x < 31671) :
    evI k refs x < 31671 := by
  rw [← evI_spec hk refs x hx]; exact Fin.isLt _

@[expose] def Desc (g : Equiv.Perm (Fin 31671)) (f : ℕ → ℕ) : Prop :=
  ∀ (x : ℕ) (hx : x < 31671), (g ⟨x, hx⟩ : ℕ) = f x

theorem desc_lt {g : Equiv.Perm (Fin 31671)} {f : ℕ → ℕ} (h : Desc g f) {x : ℕ} (hx : x < 31671) :
    f x < 31671 := by
  rw [← h x hx]; exact Fin.isLt _

theorem desc_mul {g h : Equiv.Perm (Fin 31671)} {f e : ℕ → ℕ} (hg : Desc g f) (hh : Desc h e) :
    Desc (g * h) (fun x => f (e x)) := by
  intro x hx
  rw [Equiv.Perm.mul_apply]
  have e1 : h ⟨x, hx⟩ = ⟨_, desc_lt hh hx⟩ := Fin.ext (hh x hx)
  rw [e1]
  exact hg _ _

theorem desc_el {k : ℕ} (hk : k < 17) (refs : List ℕ) : Desc (el k refs) (ev k refs) :=
  ev_spec hk refs

theorem desc_elI {k : ℕ} (hk : k < 17) (refs : List ℕ) : Desc (el k refs)⁻¹ (evI k refs) :=
  evI_spec hk refs

theorem desc_pow {g : Equiv.Perm (Fin 31671)} {f : ℕ → ℕ} (h : Desc g f) (n : ℕ) :
    Desc (g ^ n) (iter f n) :=
  iter_spec h n

theorem el_mem_range (k : ℕ) (refs : List ℕ) : el k refs ∈ rho432F.range := tv_mem_range _ refs

theorem eq_one_of_fix5 {g : Equiv.Perm (Fin 31671)} (hg : g ∈ rho432F.range) {f : ℕ → ℕ}
    (hd : Desc g f) (h : fix5 f = true) : g = 1 :=
  fix5_spec hg hd h

theorem ne_one_of_moves {g : Equiv.Perm (Fin 31671)} {f : ℕ → ℕ} (hd : Desc g f) {q : ℕ}
    (hq : q < 31671) (h : notB (Nat.beq (f q) q) = true) : g ≠ 1 := by
  intro h1
  have e := hd q hq
  rw [h1, Equiv.Perm.one_apply] at e
  rw [← e] at h
  exact absurd h (by simp [notB, Nat.beq_refl])

theorem tW_mem {k : ℕ} (hk : k < 17) (t : ℕ) : vw (tW k t) ∈ Kof (FJ.getD k 0) := by
  have h := (node_parts hk).1
  unfold tChk at h
  rw [belowAll_iff] at h
  by_cases ht : t < (TW.getD k []).length
  · have h1 := h t ht
    simp only [andB_iff] at h1
    obtain ⟨hl, hr, hf⟩ := h1
    have hd : Desc (vw (tW k t) * (recP ((TR.getD k []).getD t []))⁻¹)
        (fun x => evL CFSG.KD.B4A.LP (tW k t) (CFSG.KD.B4AF.evRecI ((TR.getD k []).getD t []) x)) :=
      desc_mul (evL_spec _ (lettersOK_iff.1 hl)) (evRecI_spec _ (refs_wInH hr))
    have hrange : vw (tW k t) * (recP ((TR.getD k []).getD t []))⁻¹ ∈ rho432F.range := by
      refine Subgroup.mul_mem _ (vw_mem_range _) (Subgroup.inv_mem _ ?_)
      exact Subgroup.map_le_range _ _ (recP_mem hr)
    have h1 := eq_one_of_fix5 hrange hd hf
    rw [mul_inv_eq_one] at h1
    rw [h1]
    exact recP_mem hr
  · rw [tW, List.getD_eq_default (TW.getD k []) [] (by omega : (TW.getD k []).length ≤ t), vw_nil]
    exact Subgroup.one_mem _

theorem el_mem {k : ℕ} (hk : k < 17) (refs : List ℕ) : el k refs ∈ Kof (FJ.getD k 0) :=
  tv_mem (tW_mem hk) refs

@[expose] noncomputable def pS (k : ℕ) : Set (Equiv.Perm (Fin 31671)) :=
  {σ | ∃ i < FA.getD k 0, σ = el k (pg k i)}

theorem p_facts {k : ℕ} (hk : k < 17) : el k (pg k 0) ^ 5 = 1 ∧ el k (pg k 0) ≠ 1 ∧
    (FA.getD k 0 = 2 → el k (pg k 1) ^ 5 = 1 ∧
      el k (pg k 0) * el k (pg k 1) = el k (pg k 1) * el k (pg k 0) ∧
      ∀ i < 5, el k (pg k 1) ≠ el k (pg k 0) ^ i) := by
  have h := (node_parts hk).2.1
  have hd := (five_data.2 k hk)
  unfold pChk at h
  simp only [andB_iff] at h
  obtain ⟨h5, hm, h2⟩ := h
  have hx := desc_el hk (pg k 0)
  refine ⟨eq_one_of_fix5 (Subgroup.pow_mem _ (el_mem_range _ _) _) (desc_pow hx 5) h5,
    ne_one_of_moves hx (hd.2.2.1 0 (by norm_num)) hm, fun ha => ?_⟩
  rw [ha] at h2
  change andB _ (andB _ _) = true at h2
  simp only [andB_iff, belowAll_iff] at h2
  obtain ⟨hy5, hxy, hyx⟩ := h2
  have hy := desc_el hk (pg k 1)
  refine ⟨eq_one_of_fix5 (Subgroup.pow_mem _ (el_mem_range _ _) _) (desc_pow hy 5) hy5, ?_,
    fun i hi he => ?_⟩
  · have hc := eq_one_of_fix5 (g := el k (pg k 0) * el k (pg k 1) * (el k (pg k 0))⁻¹ *
      (el k (pg k 1))⁻¹)
      (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (el_mem_range _ _)
        (el_mem_range _ _)) (Subgroup.inv_mem _ (el_mem_range _ _)))
        (Subgroup.inv_mem _ (el_mem_range _ _)))
      (desc_mul (desc_mul (desc_mul hx hy) (desc_elI hk _)) (desc_elI hk _)) hxy
    calc el k (pg k 0) * el k (pg k 1)
        = el k (pg k 0) * el k (pg k 1) * (el k (pg k 0))⁻¹ * (el k (pg k 1))⁻¹ *
            (el k (pg k 1) * el k (pg k 0)) := by group
      _ = el k (pg k 1) * el k (pg k 0) := by rw [hc, one_mul]
  · have := ne_one_of_moves (desc_mul hy (desc_pow (desc_elI hk (pg k 0)) i))
      (hd.2.2.1 (i + 1) (by omega)) (hyx i hi)
    apply this
    rw [he, inv_pow, mul_inv_cancel]

theorem p_group {k : ℕ} (hk : k < 17) :
    (∀ z ∈ Subgroup.closure (pS k), z ^ 5 = 1) ∧ 5 ^ FA.getD k 0 ≤ Nat.card (Subgroup.closure (pS k)) ∧
    Subgroup.closure (pS k) ≤ Kof (FJ.getD k 0) := by
  obtain ⟨hx5, hx1, h2⟩ := p_facts hk
  rcases (five_data.2 k hk).1 with ha | ha
  · have hS : pS k = {el k (pg k 0)} := by
      ext σ
      simp only [pS, ha, Set.mem_setOf_eq, Set.mem_singleton_iff]
      exact ⟨fun ⟨i, hi, h⟩ => by rw [h, show i = 0 by omega], fun h => ⟨0, by norm_num, h⟩⟩
    refine ⟨?_, ?_, ?_⟩
    · refine CFSG.HardMathSupport.Dickson.I271.TabBFiveCent.pow_eq_one_of_mem_closure
        (fun a ha' b hb => ?_) (fun a ha' => ?_)
      · rw [hS] at ha' hb
        rw [ha', hb]
      · rw [hS] at ha'
        rw [ha']
        exact hx5
    · rw [ha, pow_one, hS]
      have hp : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
      have ho : orderOf (el k (pg k 0)) = 5 := orderOf_eq_prime hx5 hx1
      have hz : Subgroup.zpowers (el k (pg k 0)) ≤ Subgroup.closure {el k (pg k 0)} :=
        (Subgroup.zpowers_le).2 (Subgroup.subset_closure rfl)
      calc 5 = Nat.card (Subgroup.zpowers (el k (pg k 0))) := by rw [Nat.card_zpowers, ho]
        _ ≤ _ := Subgroup.card_le_of_le hz
    · rw [Subgroup.closure_le]
      rintro _ ⟨i, -, rfl⟩
      exact el_mem hk _
  · obtain ⟨hy5, hxy, hyx⟩ := h2 ha
    have hS : pS k = {el k (pg k 0), el k (pg k 1)} := by
      ext σ
      simp only [pS, ha, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨i, hi, rfl⟩
        interval_cases i
        · exact Or.inl rfl
        · exact Or.inr rfl
      · rintro (h | h)
        · exact ⟨0, by norm_num, h⟩
        · exact ⟨1, by norm_num, h⟩
    refine ⟨?_, ?_, ?_⟩
    · refine CFSG.HardMathSupport.Dickson.I271.TabBFiveCent.pow_eq_one_of_mem_closure
        (fun a ha' b hb => ?_) (fun a ha' => ?_)
      · rw [hS] at ha' hb
        rcases ha' with rfl | rfl <;> rcases hb with rfl | rfl
        · rfl
        · exact hxy
        · exact hxy.symm
        · rfl
      · rw [hS] at ha'
        rcases ha' with rfl | rfl
        · exact hx5
        · exact hy5
    · rw [ha, hS]
      exact card_ge_25 hx5 hx1 hy5 hxy hyx
    · rw [Subgroup.closure_le]
      rintro _ ⟨i, -, rfl⟩
      exact el_mem hk _

theorem desc_powI {k : ℕ} (hk : k < 17) {g : List ℕ} (h5 : el k g ^ 5 = 1) {e : ℕ} (he : e < 5) :
    Desc ((el k g ^ e)⁻¹) (powI k g e) := by
  unfold powI
  cases hb : Nat.ble e 2
  · have h1 : (el k g ^ e)⁻¹ = el k g ^ (5 - e) := by
      rw [inv_eq_iff_mul_eq_one, ← pow_add, Nat.add_sub_of_le (by omega : e ≤ 5), h5]
    rw [h1]
    exact desc_pow (desc_el hk g) _
  · rw [← inv_pow]
    exact desc_pow (desc_elI hk g) _

theorem el_nil (k : ℕ) : el k [] = 1 := rfl

theorem norm_conj {k : ℕ} (hk : k < 17) {n es : List ℕ} (hes : ∀ i < 4, es.getD i 0 < 5)
    (h : normB k n es = true) :
    ∀ g ∈ pS k, el k n * g * (el k n)⁻¹ ∈ Subgroup.closure (pS k) := by
  rintro _ ⟨i, hi, rfl⟩
  unfold normB at h
  rw [belowAll_iff] at h
  obtain ⟨hx5, -, h2⟩ := p_facts hk
  have ha := (five_data.2 k hk).1
  have hi2 : i < 2 := by omega
  set e1 := es.getD (Nat.mul 2 i) 0
  set e2 := es.getD (Nat.add (Nat.mul 2 i) 1) 0
  have he1 : e1 < 5 := hes _ (by change 2 * i < 4; omega)
  have he2 : e2 < 5 := hes _ (by change 2 * i + 1 < 4; omega)
  have hy5 : el k (pg k 1) ^ 5 = 1 := by
    rcases ha with ha | ha
    · have hl := (five_data.2 k hk).2.1
      have hy : pg k 1 = [] := by
        unfold pg
        rw [List.getD_eq_default (PX.getD k []) [] (by omega : (PX.getD k []).length ≤ 1)]
      rw [hy, el_nil, one_pow]
    · exact (h2 ha).1
  have hd := desc_mul (desc_mul (desc_mul (desc_el hk n) (desc_el hk (pg k i))) (desc_elI hk n))
    (desc_mul (desc_powI hk hy5 he2) (desc_powI hk hx5 he1))
  have hc := eq_one_of_fix5 (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _
    (el_mem_range _ _) (el_mem_range _ _)) (Subgroup.inv_mem _ (el_mem_range _ _)))
    (Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.pow_mem _ (el_mem_range _ _) _))
      (Subgroup.inv_mem _ (Subgroup.pow_mem _ (el_mem_range _ _) _)))) hd (h i hi)
  have e : el k n * el k (pg k i) * (el k n)⁻¹ = el k (pg k 0) ^ e1 * el k (pg k 1) ^ e2 := by
    rw [← mul_inv_eq_one, mul_inv_rev]
    rw [mul_assoc] at hc
    exact hc
  rw [e]
  have h0 : el k (pg k 0) ∈ pS k := ⟨0, by omega, rfl⟩
  refine Subgroup.mul_mem _ (Subgroup.pow_mem _ (Subgroup.subset_closure h0) _) ?_
  rcases ha with ha | ha
  · have hl := (five_data.2 k hk).2.1
    have hy : pg k 1 = [] := by
      unfold pg
      rw [List.getD_eq_default (PX.getD k []) [] (by omega : (PX.getD k []).length ≤ 1)]
    rw [hy, el_nil, one_pow]
    exact Subgroup.one_mem _
  · have h1 : el k (pg k 1) ∈ pS k := ⟨1, by omega, rfl⟩
    exact Subgroup.pow_mem _ (Subgroup.subset_closure h1) _

end

@[expose] noncomputable def lS (k l : ℕ) : Set (Equiv.Perm (Fin 31671)) :=
  {σ | ∃ w ∈ lg k l, σ = el k w}

@[expose] noncomputable def eL (k : ℕ) : List (Equiv.Perm (Fin 31671)) :=
  (List.range (EQ.getD k []).length).map fun e => el k (ew k e)

@[expose] noncomputable def bF (k l : ℕ) : Fin 31671 :=
  if h : (NB.getD k []).getD l 0 < 31671 then ⟨_, h⟩ else 0

@[expose] noncomputable def lvOf (k s m : ℕ) : List (Fin 31671 × Set (Equiv.Perm (Fin 31671)) × ℕ) :=
  (List.range' s m).map fun l => (bF k l, lS k l, ((NP.getD k []).getD l []).length)

@[expose] noncomputable def nS (k : ℕ) : Set (Equiv.Perm (Fin 31671)) :=
  {σ | σ ∈ eL k} ∪ lvSet (lvOf k 0 (NB.getD k []).length)

theorem mem_lvSet {g : Equiv.Perm (Fin 31671)} :
    ∀ lv : List (Fin 31671 × Set (Equiv.Perm (Fin 31671)) × ℕ), g ∈ lvSet lv ↔ ∃ x ∈ lv, g ∈ x.2.1
  | [] => by simp [lvSet]
  | x :: lv => by
    simp only [lvSet, Set.mem_union, mem_lvSet lv, List.mem_cons]
    constructor
    · rintro (h | ⟨y, hy, h⟩)
      · exact ⟨x, Or.inl rfl, h⟩
      · exact ⟨y, Or.inr hy, h⟩
    · rintro ⟨y, (rfl | hy), h⟩
      · exact Or.inl h
      · exact Or.inr ⟨y, hy, h⟩

theorem mem_lvOf {k s m : ℕ} {g : Equiv.Perm (Fin 31671)} :
    g ∈ lvSet (lvOf k s m) ↔ ∃ l, s ≤ l ∧ l < s + m ∧ g ∈ lS k l := by
  rw [mem_lvSet]
  constructor
  · rintro ⟨x, hx, hg⟩
    obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hx
    rw [List.mem_range'_1] at hl
    exact ⟨l, hl.1, hl.2, hg⟩
  · rintro ⟨l, h1, h2, hg⟩
    exact ⟨_, List.mem_map.2 ⟨l, List.mem_range'_1.2 ⟨h1, h2⟩, rfl⟩, hg⟩

section

theorem fixB_spec {k : ℕ} (hk : k < 17) {n : List ℕ} {m : ℕ} (hm : m ≤ (NB.getD k []).length)
    (h : fixB k n (NB.getD k []) m = true) : ∀ i < m, el k n (bF k i) = bF k i := by
  unfold fixB at h
  rw [belowAll_iff] at h
  intro i hi
  have hb := (five_data.2 k hk).2.2.2.1 i (by omega)
  apply Fin.ext
  have e : bF k i = ⟨_, hb⟩ := by rw [bF, dif_pos hb]
  rw [e]
  exact (ev_spec hk n _ hb).trans (Nat.eq_of_beq_eq_true (h i hi))

theorem lS_facts {k : ℕ} (hk : k < 17) {l : ℕ} (hl : l < (NB.getD k []).length) :
    ∀ g ∈ lS k l, (∀ i < l, g (bF k i) = bF k i) ∧ ∀ z ∈ pS k, g * z * g⁻¹ ∈ Subgroup.closure (pS k) := by
  rintro _ ⟨w, hw, rfl⟩
  obtain ⟨gi, hgi, rfl⟩ := List.getElem_of_mem hw
  have h := (node_parts hk).2.2.1 l hl
  unfold levelChk at h
  rw [andB_iff, belowAll_iff] at h
  have h1 := h.1 gi hgi
  rw [andB_iff, List.getD_eq_getElem _ _ hgi] at h1
  refine ⟨fixB_spec hk hl.le h1.2, norm_conj hk ?_ h1.1⟩
  intro i hi
  exact (five_data.2 k hk).2.2.2.2.2.1 l hl gi hgi i hi

theorem eL_facts {k : ℕ} (hk : k < 17) {e : ℕ} (he : e < (EQ.getD k []).length) :
    (∀ i < (NB.getD k []).length, el k (ew k e) (bF k i) = bF k i) ∧
    (∀ z ∈ pS k, el k (ew k e) * z * (el k (ew k e))⁻¹ ∈ Subgroup.closure (pS k)) ∧
    orderOf (el k (ew k e)) = (EQ.getD k []).getD e 0 := by
  have h := (node_parts hk).2.2.2.1 e he
  obtain ⟨hq0, hes, hpr, hpt⟩ := (five_data.2 k hk).2.2.2.2.2.2.1 e he
  unfold CFSG.KD.B4AF.finChk at h
  simp only [andB_iff, belowAll_iff] at h
  obtain ⟨hn, hf, h1, hmv⟩ := h
  refine ⟨fixB_spec hk le_rfl hf, norm_conj hk hes hn, ?_⟩
  have hd := desc_el hk (ew k e)
  refine orderOf_eq_of_pow_and_pow_div_prime hq0
    (eq_one_of_fix5 (Subgroup.pow_mem _ (el_mem_range _ _) _) (desc_pow hd _) h1) ?_
  intro p hp hpq
  have hdiv : ∀ d < p, 1 < d → ¬ d ∣ p := fun d hd' h1d hdp => by
    rcases hp.eq_one_or_self_of_dvd d hdp with h' | h' <;> omega
  have hmem : p ∈ (EF.getD k []).getD e [] := by
    by_contra hn
    exact hpr p (Nat.lt_succ_of_le (Nat.le_of_dvd hq0 hpq)) ⟨hp.one_lt, hdiv, hpq, hn⟩
  obtain ⟨i, hi, hpi⟩ := List.getElem_of_mem hmem
  have := ne_one_of_moves (desc_pow hd _) (hpt i hi) (hmv i hi)
  rw [List.getD_eq_getElem _ _ hi, hpi] at this
  exact this

theorem lvValid {k : ℕ} (hk : k < 17) :
    ∀ m s, s + m = (NB.getD k []).length → LvValid {σ | σ ∈ eL k} (lvOf k s m)
  | 0, _, _ => trivial
  | m + 1, s, hsm => by
    have hl : s < (NB.getD k []).length := by omega
    have e : lvOf k s (m + 1) = (bF k s, lS k s, ((NP.getD k []).getD s []).length) :: lvOf k (s + 1) m := by
      simp [lvOf, List.range'_succ]
    rw [e]
    refine ⟨?_, ?_, lvValid hk m (s + 1) (by omega)⟩
    · rintro g (hg | hg)
      · obtain ⟨ei, hei, rfl⟩ := List.mem_map.1 (show g ∈ eL k from hg)
        exact (eL_facts hk (List.mem_range.1 hei)).1 s hl
      · obtain ⟨l, h1, h2, hgl⟩ := mem_lvOf.1 hg
        exact (lS_facts hk (by omega) g hgl).1 s (by omega)
    · have h := (node_parts hk).2.2.1 s hl
      unfold levelChk at h
      rw [andB_iff] at h
      have hb := (five_data.2 k hk).2.2.2.1 s hl
      have h3 := orbListChk_spec (tW_lt hk) hb h.2
      have e2 : bF k s = ⟨_, hb⟩ := by rw [bF, dif_pos hb]
      change ((NP.getD k []).getD s []).length ≤
        (MulAction.orbit (Subgroup.closure (lS k s)) (bF k s)).ncard
      rw [e2]
      exact h3

theorem n_group {k : ℕ} (hk : k < 17) :
    Subgroup.closure (nS k) ≤ Kof (FJ.getD k 0) ∧
    Subgroup.closure (nS k) ≤ Subgroup.normalizer (Subgroup.closure (pS k) : Set (Equiv.Perm (Fin 31671))) ∧
    FB.getD k 0 ≤ Nat.card (Subgroup.closure (nS k)) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Subgroup.closure_le]
    rintro g (hg | hg)
    · obtain ⟨ei, -, rfl⟩ := List.mem_map.1 (show g ∈ eL k from hg)
      exact el_mem hk _
    · obtain ⟨l, -, -, w, hw, rfl⟩ := mem_lvOf.1 hg
      exact el_mem hk _
  · refine CFSG.HardMathSupport.Dickson.I271.TabBFiveCent.closure_le_normalizer fun n hn g hg => ?_
    rcases hn with hn | hn
    · obtain ⟨ei, hei, rfl⟩ := List.mem_map.1 (show n ∈ eL k from hn)
      exact (eL_facts hk (List.mem_range.1 hei)).2.1 g hg
    · obtain ⟨l, -, h2, hnl⟩ := mem_lvOf.1 hn
      exact (lS_facts hk (by omega) n hnl).2 g hg
  · have hq := lcm_le_card (eL k)
    have hord : (eL k).map orderOf = EQ.getD k [] := by
      apply List.ext_getElem (by simp [eL])
      intro i h1 h2
      simp only [eL, List.map_map, List.getElem_map, List.getElem_range, Function.comp]
      rw [(eL_facts hk h2).2.2, List.getD_eq_getElem _ _ h2]
    rw [hord] at hq
    have hc := chain_le_card {σ | σ ∈ eL k} _ hq _
      (lvValid hk (NB.getD k []).length 0 (Nat.zero_add _))
    have hprod : ((lvOf k 0 (NB.getD k []).length).map fun x => x.2.2).prod = orbProd k := by
      have hlen := (five_data.2 k hk).2.2.2.2.1
      have e : ((List.range' 0 (NB.getD k []).length).map fun l => ((NP.getD k []).getD l []).length) =
          (NP.getD k []).map List.length := by
        apply List.ext_getElem (by rw [List.length_map, List.length_map, List.length_range', hlen])
        intro i h1 h2
        have hi : i < (NP.getD k []).length := by rwa [List.length_map] at h2
        simp only [List.getElem_map, List.getElem_range', Nat.zero_add, Nat.one_mul]
        rw [List.getD_eq_getElem _ _ hi]
      have e2 : ∀ l : List ℕ, l.prod = l.foldr Nat.mul 1 := fun l => by
        induction l with
        | nil => rfl
        | cons a l ih =>
          rw [List.prod_cons, List.foldr_cons, ih]
          rfl
      unfold orbProd lvOf
      rw [List.map_map]
      change ((List.range' 0 (NB.getD k []).length).map fun l =>
        ((NP.getD k []).getD l []).length).prod = _
      rw [e, e2]
    rw [hprod] at hc
    rw [(node_parts hk).2.2.2.2]
    exact hc

theorem ncard_five_le {k : ℕ} (hk : k < 17) {c : ℕ} (hc : Nat.card (Kof (FJ.getD k 0)) = c)
    (h5 : ¬ 5 ^ (FA.getD k 0 + 1) ∣ c) :
    {σ : Equiv.Perm (Fin 31671) | σ ∈ Kof (FJ.getD k 0) ∧ orderOf σ = 5}.ncard ≤
      c / FB.getD k 0 * (5 ^ FA.getD k 0 - 1) := by
  have hp : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨hexp, hcard, hPK⟩ := p_group hk
  obtain ⟨hNK, hN, hFB⟩ := n_group hk
  have h := CFSG.HardMathSupport.Dickson.I271.TabBFiveCent.ncard_orderOf_le_of_normalizer
    hPK hNK hexp hcard (by rwa [hc]) hN
  rw [hc] at h
  refine h.trans (Nat.mul_le_mul_right _ (Nat.div_le_div_left hFB ?_))
  exact (five_data.2 k hk).2.2.2.2.2.2.2

end

end CertificateChecks.KernelB433

end
