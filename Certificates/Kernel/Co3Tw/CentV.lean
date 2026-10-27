module

public import Certificates.Kernel.Co3Tw.CentGlue
public import Certificates.Kernel.Co3Tw.Facts

public section

namespace CertificateChecks.KernelCo3Tw

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.RankThree.Native CFSG.Sporadic.Schreier.Co3
  CFSG.Certificates.Native CFSG.Certificates
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.B3S3K CFSG.KC.PermWit CFSG.KC.Co3Tw
  CFSG.KC.CentSrch CertificateChecks.KernelSpor

theorem prep_uniq {P : Nat} {g h : Equiv.Perm (Fin 276)} (hg : Orb.PRep 276 9 P g)
    (hh : Orb.PRep 276 9 P h) : g = h :=
  Equiv.ext fun x => Fin.ext ((hg x).symm.trans (hh x))

theorem prep_mul {P Q : Nat} {g h : Equiv.Perm (Fin 276)} (hg : Orb.PRep 276 9 P g)
    (hh : Orb.PRep 276 9 Q h) : Orb.PRep 276 9 (pcomp 276 9 (mask 9) P Q) (g * h) :=
  Orb.prep_pcomp (by norm_num) hg hh

theorem comm_of_commP {p q : Nat} (hp : CFSG.KC.Misc.ArrEnum.permB 276 9 p = true)
    (hq : CFSG.KC.Misc.ArrEnum.permB 276 9 q = true) (h : commP p q = true) :
    ppK p * ppK q = ppK q * ppK p := by
  have e := Nat.eq_of_beq_eq_true h
  have h1 := prep_mul (prep_ppK hp) (prep_ppK hq)
  have h2 := prep_mul (prep_ppK hq) (prep_ppK hp)
  rw [e] at h1
  exact prep_uniq h1 h2

theorem inT_spec {N p : Nat} {T : Nat → Nat} (h : inT N T p = true) : ∃ i < N, T i = p := by
  by_contra hne
  simp only [not_exists, not_and] at hne
  have ha : allN N (fun i => !(Nat.beq (T i) p)) = true := Orb.allN_iff.2 fun i hi => by
    rw [Bool.not_eq_true', Bool.eq_false_iff]
    exact fun h' => hne i hi (Nat.eq_of_beq_eq_true h')
  unfold inT at h
  rw [ha] at h
  exact absurd h (by decide)

theorem cenOK_spec {x y p : Nat} (h : cenOK x y p = true) :
    CFSG.KC.Misc.ArrEnum.permB 276 9 p = true ∧ siftR 276 9 Co3C.LR Co3C.TRI Co3C.BP 7 p = true ∧
      commP p x = true ∧ commP p y = true := by
  unfold cenOK at h
  rw [bA_eq, bA_eq, bA_eq, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2.1, h.2.2⟩


theorem mem_Cent {k p : Nat} (hk : k < 7) (h : cenOK (xpK k) (ypK k) p = true) : ppK p ∈ Cent k := by
  obtain ⟨hp, hs, hx, hy⟩ := cenOK_spec h
  refine Subgroup.mem_inf.2 ⟨ppK_mem hp hs, Subgroup.mem_centralizer_iff.2 ?_⟩
  rintro z (rfl | rfl)
  · exact (comm_of_commP hp (gk k hk).1 hx).symm
  · exact (comm_of_commP hp (gk k hk).2 hy).symm

theorem fac972 : (972 : ℕ).factorization 3 = 5 := by
  rw [show (972 : ℕ) = 3 ^ 5 * 4 by norm_num, Nat.factorization_mul (by norm_num) (by norm_num),
    Finsupp.add_apply, Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num), add_zero]

theorem closed_of_V {H V : Subgroup (Equiv.Perm (Fin 276))} (hcard : Nat.card H = 972)
    (hV : Nat.card V = 243) (hVH : V ≤ H) {c : Equiv.Perm (Fin 276)} (hcH : c ∈ H) (hc2 : c * c = 1)
    (hc1 : c ≠ 1) (hcN : ∀ v ∈ V, c * v * c⁻¹ ∈ V) {a b : Equiv.Perm (Fin 276)} (ha : a ∈ H)
    (hb : b ∈ H) (ha3 : ∃ m, a ^ 3 ^ m = 1) (hb3 : ∃ m, b ^ 3 ^ m = 1) :
    ∃ m, (a * b) ^ 3 ^ m = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hfin : Finite H := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hci : c⁻¹ = c := inv_eq_of_mul_eq_one_right hc2
  set W := V.subgroupOf H with hW
  have hWc : Nat.card W = 243 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVH).toEquiv, hV]
  have hconj : ∀ z : H, (((⟨c, hcH⟩ : H) * z * (⟨c, hcH⟩ : H)⁻¹ : H) : Equiv.Perm (Fin 276)) =
      c * z * c⁻¹ := fun z => by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mk]
  have hcN' : (⟨c, hcH⟩ : H) ∈ Subgroup.normalizer (W : Set H) := by
    rw [Subgroup.mem_normalizer_iff]
    intro z
    rw [hW, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, hconj]
    constructor
    · exact hcN _
    · intro hz
      have h1 := hcN _ hz
      have e : c * (c * (z : Equiv.Perm (Fin 276)) * c⁻¹) * c⁻¹ = z := by
        rw [hci, mul_assoc, mul_assoc, hc2, mul_one, ← mul_assoc, hc2, one_mul]
      rwa [e] at h1
  have hcV : (⟨c, hcH⟩ : H) ∉ W := by
    intro hc
    rw [hW, Subgroup.mem_subgroupOf] at hc
    have h243 := pow_card_eq_one' (G := V) (x := ⟨c, hc⟩)
    rw [hV] at h243
    have h243' : c ^ 243 = 1 := by simpa using congrArg Subtype.val h243
    have e : c ^ 243 = c := by
      rw [show 243 = 2 * 121 + 1 by norm_num, pow_succ, pow_mul, sq, hc2, one_pow, one_mul]
    exact hc1 (e.symm.trans h243')
  have hWn : W.Normal := normal_of_normalizer hcard hWc hcN' hcV
  have hP : Nat.card W = 3 ^ (Nat.card H).factorization 3 := by
    rw [hWc, hcard, fac972]
    norm_num
  exact closed_of_normal (Sylow.ofCard W hP) (by rw [Sylow.coe_ofCard]; exact hWn) ha hb ha3 hb3

theorem ppK_pidn : ppK (pidn 276 9) = 1 :=
  prep_uniq (prep_ppK (by decide +kernel)) (Orb.prep_pidn (by norm_num) (by norm_num))

theorem ppK_ne_one {c : Nat} (hc : CFSG.KC.Misc.ArrEnum.permB 276 9 c = true)
    (h : (!(Nat.beq c (pidn 276 9))) = true) : ppK c ≠ 1 := by
  intro h1
  have hpid : CFSG.KC.Misc.ArrEnum.permB 276 9 (pidn 276 9) = true := by decide +kernel
  have e := (eqA_iff (rep_of_validA (validA_of hc)) (rep_of_validA (validA_of hpid))).2
    (h1.trans ppK_pidn.symm)
  rw [CFSG.KC.Misc.ArrEnum.eqA_unpack' szW hc hpid] at e
  rw [e] at h
  exact absurd h (by decide)

theorem closed_of_vOK {k : Nat} (hk : k < 7) (hcard : Nat.card (Cent k) = 972) {ng N : Nat}
    {G T E S : Nat → Nat} {SK : List Nat} {c : Nat} (hng : ng = 5)
    (hok : bfsK 276 9 ng G N T E S = true) (hK : keysSK 276 9 co3ChainBaseArr.toList N T SK = true)
    (hv : vOK ng N G T (xpK k) (ypK k) c = true) {a b : Equiv.Perm (Fin 276)} (ha : a ∈ Cent k)
    (hb : b ∈ Cent k) (ha3 : ∃ m, a ^ 3 ^ m = 1) (hb3 : ∃ m, b ^ 3 ^ m = 1) :
    ∃ m, (a * b) ^ 3 ^ m = 1 := by
  unfold vOK at hv
  rw [bA_eq, bA_eq, bA_eq, bA_eq, bA_eq, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
    Bool.and_eq_true, Bool.and_eq_true] at hv
  obtain ⟨⟨hN, hG⟩, hc, ⟨hcc, hc1⟩, hin⟩ := hv
  have hN' : N = 243 := Nat.eq_of_beq_eq_true hN
  set gs : Array (Array ℕ) := Array.ofFn (n := 5) fun j => unpack 276 9 (G j) with hgs
  have gs_size : gs.size = 5 := by simp [hgs]
  have gs_get : ∀ j < 5, gs[j]! = unpack 276 9 (G j) := by
    intro j hj
    rw [getElem!_pos gs j (by rw [gs_size]; exact hj)]
    simp [hgs]
  have hGc : ∀ j < 5, cenOK (xpK k) (ypK k) (G j) = true := fun j hj =>
    Orb.allN_iff.1 hG j (by rw [hng]; exact hj)
  have hGp : ∀ j < ng, CFSG.KC.Misc.ArrEnum.permB 276 9 (G j) = true := fun j hj =>
    (cenOK_spec (hGc j (by rw [← hng]; exact hj))).1
  have hbind : BindA 276 9 gs ng G :=
    ⟨by rw [gs_size, hng], fun j hj => gs_get j (by rw [← hng]; exact hj)⟩
  have hen := enum_of hbind hGp hok base_lt hK (by rw [hN']; norm_num : N ≤ 3000)
  obtain ⟨hmem, hcardV, hval⟩ := enumOK_spec base_lt hen.1
  set V := Subgroup.closure (permsA 276 gs)
  have hVc : Nat.card V = 243 := by rw [hcardV, hen.2.1, hN']
  have hgen : ∀ t ∈ permsA 276 gs, ∃ j < 5, t = ppK (G j) := by
    intro t ht
    obtain ⟨j, hj, rfl⟩ := ht
    rw [Set.mem_setOf_eq, gs_size] at hj
    refine ⟨j, hj, ?_⟩
    change permOfArr 276 gs[j]! = ppK (G j)
    rw [gs_get j hj]
    rfl
  have hVC : V ≤ Cent k := by
    rw [Subgroup.closure_le]
    intro t ht
    obtain ⟨j, hj, rfl⟩ := hgen t ht
    exact mem_Cent hk (hGc j hj)
  obtain ⟨hcp, -, -, -⟩ := cenOK_spec hc
  have hc2 : ppK c * ppK c = 1 :=
    prep_uniq (prep_mul (prep_ppK hcp) (prep_ppK hcp)) (by
      rw [Nat.eq_of_beq_eq_true hcc]
      exact Orb.prep_pidn (by norm_num) (by norm_num))
  have hci : (ppK c)⁻¹ = ppK c := inv_eq_of_mul_eq_one_right hc2
  have hcN : ∀ v ∈ V, ppK c * v * (ppK c)⁻¹ ∈ V := by
    have hle : Subgroup.closure ({ppK c} : Set (Equiv.Perm (Fin 276))) ≤
        Subgroup.normalizer (V : Set (Equiv.Perm (Fin 276))) := by
      apply closure_le_normalizer_closure
      intro s hs t ht
      rw [Set.mem_singleton_iff] at hs
      subst hs
      obtain ⟨j, hj, rfl⟩ := hgen t ht
      obtain ⟨i, hi, he⟩ := inT_spec (Orb.allN_iff.1 hin j (by rw [hng]; exact hj))
      have hpr : Orb.PRep 276 9 (T i) (ppK c * ppK (G j) * (ppK c)⁻¹) := by
        rw [he, hci]
        exact prep_mul (prep_mul (prep_ppK hcp) (prep_ppK (hGp j (by rw [hng]; exact hj))))
          (prep_ppK hcp)
      have hi' : i < (enumBfs 276 gs co3ChainBaseArr.toList 3000).pts.size := by
        rw [hen.2.1]
        exact hi
      have hrep : Rep 276 (enumBfs 276 gs co3ChainBaseArr.toList 3000).pts[i]!
          (ppK c * ppK (G j) * (ppK c)⁻¹) := by
        rw [hen.2.2 i hi]
        exact Orb.rep_unpack hpr
      exact enumOK_mem base_lt hen.1 hi' hrep
    intro v hv
    have hcn := hle (Subgroup.subset_closure (Set.mem_singleton _))
    exact (Subgroup.mem_normalizer_iff.1 hcn v).1 hv
  exact closed_of_V hcard hVc hVC (mem_Cent hk hc) hc2 (ppK_ne_one hcp hc1) hcN ha hb ha3 hb3

theorem ok3 : bfsK 276 9 EV3.ng EV3.G EV3.N EV3.T EV3.E EV3.S = true :=
  bfsK_of_slices (L := 81) (K := 3) (C := EV3.C) (by decide) (by norm_num) szW EV3.g EV3.csAll EV3.t0
    EV3.dist (Nat.eq_of_beq_eq_true EV3.c0) (Nat.eq_of_beq_eq_true EV3.cK) EV3.rsAll

theorem ok4 : bfsK 276 9 EV4.ng EV4.G EV4.N EV4.T EV4.E EV4.S = true :=
  bfsK_of_slices (L := 81) (K := 3) (C := EV4.C) (by decide) (by norm_num) szW EV4.g EV4.csAll EV4.t0
    EV4.dist (Nat.eq_of_beq_eq_true EV4.c0) (Nat.eq_of_beq_eq_true EV4.cK) EV4.rsAll

theorem closed_cent_big {k : Nat} (hk : k = 3 ∨ k = 4) {a b : Equiv.Perm (Fin 276)}
    (ha : a ∈ Cent k) (hb : b ∈ Cent k) (ha3 : ∃ m, a ^ 3 ^ m = 1) (hb3 : ∃ m, b ^ 3 ^ m = 1) :
    ∃ m, (a * b) ^ 3 ^ m = 1 := by
  rcases hk with rfl | rfl
  · exact closed_of_vOK (by norm_num) card_cent3 (by decide) ok3 EV3.keys ch431008v3 ha hb ha3 hb3
  · exact closed_of_vOK (by norm_num) card_cent4 (by decide) ok4 EV4.keys ch431008v4 ha hb ha3 hb3

theorem closed_cent {k : Nat} (hk : k < 7) {a b : Equiv.Perm (Fin 276)} (ha : a ∈ Cent k)
    (hb : b ∈ Cent k) (ha3 : ∃ m, a ^ 3 ^ m = 1) (hb3 : ∃ m, b ^ 3 ^ m = 1) :
    ∃ m, (a * b) ^ 3 ^ m = 1 := by
  interval_cases k
  · exact closed_cent_small (Or.inl rfl) ha hb ha3 hb3
  · exact closed_cent_small (Or.inr (Or.inl rfl)) ha hb ha3 hb3
  · exact closed_cent_small (Or.inr (Or.inr (Or.inl rfl))) ha hb ha3 hb3
  · exact closed_cent_big (Or.inl rfl) ha hb ha3 hb3
  · exact closed_cent_big (Or.inr rfl) ha hb ha3 hb3
  · exact closed_cent_small (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) ha hb ha3 hb3
  · exact closed_cent_small (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) ha hb ha3 hb3

end CertificateChecks.KernelCo3Tw

end
