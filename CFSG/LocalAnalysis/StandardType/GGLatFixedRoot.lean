module

public import CFSG.LocalAnalysis.StandardType.GGLatRootBridge

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank

namespace LatFixedRoot

section FiniteFacts

def rootsE6 : List (Fin Tag.E6.rank → ℤ) :=
  (List.range (Tag.rootCertificate .E6).roots.length).map (Tag.rootCertificate .E6).root

def nip (a b : Fin Tag.E6.rank → ℤ) : ℤ := latGram (Tag.cartan .E6) a b

def vecEqB (a b : Fin Tag.E6.rank → ℤ) : Bool :=
  (List.finRange Tag.E6.rank).all fun i => a i == b i

def rootB (v : Fin Tag.E6.rank → ℤ) : Bool := rootsE6.any fun r => vecEqB v r

def chkA1 : Bool :=
  rootsE6.all fun a => rootsE6.all fun b => decide (-2 ≤ nip a b ∧ nip a b ≤ 2)

def chkA2 : Bool :=
  rootsE6.all fun a => rootsE6.all fun b => decide (nip a b = 2 → a = b)

def chkA3 : Bool :=
  rootsE6.all fun a => rootsE6.all fun b => decide (nip a b = -2 → b = -a)

def chkA4 : Bool := rootsE6.all fun a => decide (nip a a = 2)

def chkA5 : Bool :=
  rootsE6.all fun a => rootsE6.all fun b => decide (nip a b = -1 → rootB (a + b) = true)

def chkA7 : Bool :=
  rootsE6.all fun a => decide ((∀ i, 0 ≤ a i) ∨ ∀ i, a i ≤ 0)

theorem vecEqB_sound {a b : Fin Tag.E6.rank → ℤ} (h : vecEqB a b = true) : a = b := by
  funext i
  exact eq_of_beq (List.all_eq_true.mp h i (List.mem_finRange i))

private def nipF (a b : Fin Tag.E6.rank → ℤ) : ℤ :=
  2 * (a (0 : Fin 6) * b (0 : Fin 6) + a (1 : Fin 6) * b (1 : Fin 6) +
      a (2 : Fin 6) * b (2 : Fin 6) + a (3 : Fin 6) * b (3 : Fin 6) +
      a (4 : Fin 6) * b (4 : Fin 6) + a (5 : Fin 6) * b (5 : Fin 6))
    - (a (0 : Fin 6) * b (2 : Fin 6) + a (2 : Fin 6) * b (0 : Fin 6) +
      a (1 : Fin 6) * b (3 : Fin 6) + a (3 : Fin 6) * b (1 : Fin 6) +
      a (2 : Fin 6) * b (3 : Fin 6) + a (3 : Fin 6) * b (2 : Fin 6) +
      a (3 : Fin 6) * b (4 : Fin 6) + a (4 : Fin 6) * b (3 : Fin 6) +
      a (4 : Fin 6) * b (5 : Fin 6) + a (5 : Fin 6) * b (4 : Fin 6))

private def nipF6 (a b : Fin Tag.E6.rank → ℤ) : ℤ :=
  ∑ i : Fin 6, ∑ j : Fin 6, a i * Tag.cartan .E6 i j * b j

private lemma nipF6_eq_nipF (a b : Fin Tag.E6.rank → ℤ) : nipF6 a b = nipF a b := by
  simp only [nipF6, Fin.sum_univ_six, Tag.cartan, Tag.cartanE, nipF]
  norm_num
  ring

private lemma nip_eq_nipF (a b : Fin Tag.E6.rank → ℤ) : nip a b = nipF a b := by
  have h : nip a b = nipF6 a b := rfl
  rw [h]
  exact nipF6_eq_nipF a b

private def rootKey (v : Fin Tag.E6.rank → ℤ) : Nat :=
  Nat.pair (v (0 : Fin 6) + 8).toNat
    (Nat.pair (v (1 : Fin 6) + 8).toNat
      (Nat.pair (v (2 : Fin 6) + 8).toNat
        (Nat.pair (v (3 : Fin 6) + 8).toNat
          (Nat.pair (v (4 : Fin 6) + 8).toNat (v (5 : Fin 6) + 8).toNat))))

private def rootKeys : List Nat := [
  2843022933992939970107592627273, 2843022933992943342360806128857,
  2843023210939056399505027293177, 2846574214519044322913175393849,
  72863536696017141250167278842952, 15622393182009710524812426319289,
  2843022933992939970107592627271, 2843023210939056399505027293178,
  2843022933992936597854379125689, 2846574214519047697271908260908,
  2843022657046843774229438970809, 2846574491724574730365950155672,
  2839475530711912579276008969657, 72924202586629146829154490129177,
  422321810402127870489937177529, 85703393930557993312698084662649,
  2325329778214950001180116207929, 2843022657046843774229438970808,
  2846574491724574730365950155673, 2839475530711909209127329334344,
  2846574491724578104724847323889, 72924202586629163908288260508652,
  2839475254025028013656834102344, 72924205743187084214428966341272,
  421653117135783745418530083912, 85773316632816692494563303979592,
  62581447853924446882958830137, 2839475254025028013656834102343,
  2846574491724578104724847323890, 72924205743187084214428966341273,
  2839475254025024643508318665657, 421653117135782446722080353209,
  72924205743187101293563106359857, 85773316632816711017340269954937,
  421653050948211390847546731449, 85773320197936677177925647892329,
  62455671905240498417219884104, 2839475254025024643508318665656,
  421653050948211390847546731448, 72924205743187101293563106359858,
  85773320197936677177925647892330, 421653050948210092151198929992,
  62455671905239998594563713977, 72984915827578122317009739721164,
  85773320197936695700702998812108, 62455656102265107547951602617,
  421653050948210092151198929991, 62455656102265107547951602616,
  72984915827578122317009739721165, 85773320197936695700702998812109,
  420985284386405918805322139577, 62455656102264607725358666824,
  85843292814053199807524363402289, 420985284386405918805322139576,
  62455656102264607725358666823, 72984918986106855241325417322034,
  85843292814053199807524363402290, 62330101419028693512319523769,
  1626312732532514242389663562375089, 420985218277472232698006837831,
  62330101419028693512319523768, 85843296381354352758773590696909,
  1626312732532514242389663562375090, 7123424318520818970713046969,
  62330085639888845979843356231, 7123424318520818970713046968,
  1626312764926399621862210792940109, 7123421216986926419911537223,
  1627231099221877900385684312994034, 7104641418001774913376990656,
  1627231099221877981063589571419725, 7104641418001606335307028971,
  ]

private def rootKeysMap : List Nat :=
  (Tag.rootCertificate .E6).roots.map fun c => rootKey (decodeVec c)

private lemma rootKeys_eq : rootKeys = rootKeysMap := by decide +kernel

private def rootFast (v : Fin Tag.E6.rank → ℤ) : Bool := rootKeys.contains (rootKey v)

private lemma rootKey_inj {v w : Fin Tag.E6.rank → ℤ}
    (hv : ∀ i, -8 ≤ v i) (hw : ∀ i, -8 ≤ w i) (h : rootKey v = rootKey w) : v = w := by
  have h' := h
  simp only [rootKey, Nat.pair_eq_pair] at h'
  have hdigs : ∀ i : Fin Tag.E6.rank, (v i + 8).toNat = (w i + 8).toNat := by
    intro i
    fin_cases i
    · exact h'.1
    · exact h'.2.1
    · exact h'.2.2.1
    · exact h'.2.2.2.1
    · exact h'.2.2.2.2.1
    · exact h'.2.2.2.2.2
  funext i
  have hdig := hdigs i
  have hvi : -8 ≤ v i := hv i
  have hwi : -8 ≤ w i := hw i
  have hv' : 0 ≤ v i + 8 := by omega
  have hw' : 0 ≤ w i + 8 := by omega
  have hcast : ((v i + 8).toNat : ℤ) = ((w i + 8).toNat : ℤ) := by exact_mod_cast hdig
  rw [Int.toNat_of_nonneg hv', Int.toNat_of_nonneg hw'] at hcast
  omega

private lemma decodeVec_mem_rootsE6 {c : Nat}
    (hc : c ∈ (Tag.rootCertificate .E6).roots) : decodeVec c ∈ rootsE6 := by
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hc
  rw [rootsE6, List.mem_map]
  refine ⟨k, List.mem_range.mpr hk, ?_⟩
  simp only [RootCertificate.root, List.getD_eq_getElem _ _ hk]

private lemma vecEqB_self (v : Fin Tag.E6.rank → ℤ) : vecEqB v v = true := by
  rw [vecEqB, List.all_eq_true]
  intro i _
  exact beq_self_eq_true (v i)

private lemma rootFast_sound {v : Fin Tag.E6.rank → ℤ}
    (hv : ∀ i, -8 ≤ v i) (h : rootFast v = true) : rootB v = true := by
  have hmem : rootKey v ∈ rootKeys := List.contains_iff_mem.mp h
  rw [rootKeys_eq, rootKeysMap, List.mem_map] at hmem
  obtain ⟨c, hc, hceq⟩ := hmem
  have hdec : ∀ i : Fin Tag.E6.rank, -8 ≤ decodeVec (τ := Tag.E6) c i := by
    intro i
    simp only [decodeVec]
    have : (0 : ℤ) ≤ ((c / 16 ^ (i : ℕ) % 16 : ℕ) : ℤ) := by exact_mod_cast Nat.zero_le _
    omega
  have hvc : v = decodeVec c := rootKey_inj hv hdec hceq.symm
  have hvmem : v ∈ rootsE6 := by
    rw [hvc]
    exact decodeVec_mem_rootsE6 hc
  exact List.any_eq_true.mpr ⟨v, hvmem, vecEqB_self v⟩

private def chkCoord : Bool := rootsE6.all fun a =>
  decide ((∀ i, -3 ≤ a i) ∧ ∀ i, a i ≤ 3)

private theorem chkCoord_eq : chkCoord = true := by decide +kernel

private lemma coord_bound {a : Fin Tag.E6.rank → ℤ} (ha : a ∈ rootsE6) :
    (∀ i, -3 ≤ a i) ∧ ∀ i, a i ≤ 3 := by
  have h := List.all_eq_true.mp chkCoord_eq a ha
  exact of_decide_eq_true h

private def pairFast (a b : Fin Tag.E6.rank → ℤ) : Bool :=
  let n := nipF a b
  decide (-2 ≤ n ∧ n ≤ 2) && (n != 2 || vecEqB a b) && (n != -2 || vecEqB b (-a)) &&
    (n != -1 || rootFast (a + b)) && (n != 1 || rootFast (a - b))

private def chkAll : Bool := rootsE6.all fun a => rootsE6.all fun b => pairFast a b

private theorem chkAll_eq : chkAll = true := by decide +kernel

private lemma pairFast_spec {a b : Fin Tag.E6.rank → ℤ} (h : pairFast a b = true) :
    (-2 ≤ nipF a b ∧ nipF a b ≤ 2) ∧
    (nipF a b = 2 → vecEqB a b = true) ∧
    (nipF a b = -2 → vecEqB b (-a) = true) ∧
    (nipF a b = -1 → rootFast (a + b) = true) ∧
    (nipF a b = 1 → rootFast (a - b) = true) := by
  simp only [pairFast, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, decide_eq_true_eq] at h
  refine ⟨h.1.1.1.1, ?_, ?_, ?_, ?_⟩
  · intro hn
    rcases h.1.1.1.2 with hne | hv
    · exact absurd hn hne
    · exact hv
  · intro hn
    rcases h.1.1.2 with hne | hv
    · exact absurd hn hne
    · exact hv
  · intro hn
    rcases h.1.2 with hne | hv
    · exact absurd hn hne
    · exact hv
  · intro hn
    rcases h.2 with hne | hv
    · exact absurd hn hne
    · exact hv

theorem chkA1_eq : chkA1 = true := by
  rw [chkA1]
  apply List.all_eq_true.mpr
  intro a ha
  apply List.all_eq_true.mpr
  intro b hb
  rw [decide_eq_true_eq]
  have h := pairFast_spec (List.all_eq_true.mp (List.all_eq_true.mp chkAll_eq a ha) b hb)
  rw [nip_eq_nipF]
  exact h.1

theorem chkA2_eq : chkA2 = true := by
  rw [chkA2]
  apply List.all_eq_true.mpr
  intro a ha
  apply List.all_eq_true.mpr
  intro b hb
  rw [decide_eq_true_eq]
  intro hn
  have h := pairFast_spec (List.all_eq_true.mp (List.all_eq_true.mp chkAll_eq a ha) b hb)
  exact vecEqB_sound (h.2.1 (by rwa [nip_eq_nipF] at hn))

theorem chkA3_eq : chkA3 = true := by
  rw [chkA3]
  apply List.all_eq_true.mpr
  intro a ha
  apply List.all_eq_true.mpr
  intro b hb
  rw [decide_eq_true_eq]
  intro hn
  have h := pairFast_spec (List.all_eq_true.mp (List.all_eq_true.mp chkAll_eq a ha) b hb)
  exact vecEqB_sound (h.2.2.1 (by rwa [nip_eq_nipF] at hn))

theorem chkA4_eq : chkA4 = true := by decide +kernel

theorem chkA5_eq : chkA5 = true := by
  rw [chkA5]
  apply List.all_eq_true.mpr
  intro a ha
  apply List.all_eq_true.mpr
  intro b hb
  rw [decide_eq_true_eq]
  intro hn
  have h := pairFast_spec (List.all_eq_true.mp (List.all_eq_true.mp chkAll_eq a ha) b hb)
  have hfast := h.2.2.2.1 (by rwa [nip_eq_nipF] at hn)
  have hca := coord_bound ha
  have hcb := coord_bound hb
  have hv : ∀ i, -8 ≤ (a + b) i := by
    intro i
    have hai := hca.1 i
    have hbi := hcb.1 i
    simp only [Pi.add_apply]
    omega
  exact rootFast_sound hv hfast

theorem chkA7_eq : chkA7 = true := by decide +kernel
theorem rootsE6_mem {a : Fin Tag.E6.rank → ℤ} :
    a ∈ rootsE6 ↔ a ∈ rootFinset Tag.E6 := by
  show a ∈ rootsE6 ↔ a ∈ rootsE6.toFinset
  exact List.mem_toFinset.symm

theorem rootB_sound {v : Fin Tag.E6.rank → ℤ} (h : rootB v = true) :
    v ∈ rootFinset Tag.E6 := by
  obtain ⟨r, hr, hvr⟩ :=
    List.any_eq_true.mp (show rootsE6.any (fun r => vecEqB v r) = true from h)
  rw [rootsE6_mem] at hr
  rwa [vecEqB_sound hvr]

theorem nip_bound {a b : Fin Tag.E6.rank → ℤ}
    (ha : a ∈ rootFinset Tag.E6) (hb : b ∈ rootFinset Tag.E6) :
    -2 ≤ nip a b ∧ nip a b ≤ 2 := by
  have h1 : rootsE6.all (fun a => rootsE6.all fun b =>
      decide (-2 ≤ nip a b ∧ nip a b ≤ 2)) = true := chkA1_eq
  have h2 := List.all_eq_true.mp h1 a (rootsE6_mem.mpr ha)
  exact of_decide_eq_true (List.all_eq_true.mp h2 b (rootsE6_mem.mpr hb))

theorem nip_eq_two {a b : Fin Tag.E6.rank → ℤ}
    (ha : a ∈ rootFinset Tag.E6) (hb : b ∈ rootFinset Tag.E6) (h : nip a b = 2) : a = b := by
  have h1 : rootsE6.all (fun a => rootsE6.all fun b =>
      decide (nip a b = 2 → a = b)) = true := chkA2_eq
  have h2 := List.all_eq_true.mp h1 a (rootsE6_mem.mpr ha)
  exact of_decide_eq_true (List.all_eq_true.mp h2 b (rootsE6_mem.mpr hb)) h

theorem nip_eq_neg_two {a b : Fin Tag.E6.rank → ℤ}
    (ha : a ∈ rootFinset Tag.E6) (hb : b ∈ rootFinset Tag.E6) (h : nip a b = -2) : b = -a := by
  have h1 : rootsE6.all (fun a => rootsE6.all fun b =>
      decide (nip a b = -2 → b = -a)) = true := chkA3_eq
  have h2 := List.all_eq_true.mp h1 a (rootsE6_mem.mpr ha)
  exact of_decide_eq_true (List.all_eq_true.mp h2 b (rootsE6_mem.mpr hb)) h

theorem nip_self {a : Fin Tag.E6.rank → ℤ} (ha : a ∈ rootFinset Tag.E6) : nip a a = 2 := by
  have h1 : rootsE6.all (fun a => decide (nip a a = 2)) = true := chkA4_eq
  exact of_decide_eq_true (List.all_eq_true.mp h1 a (rootsE6_mem.mpr ha))

theorem nip_add_mem {a b : Fin Tag.E6.rank → ℤ}
    (ha : a ∈ rootFinset Tag.E6) (hb : b ∈ rootFinset Tag.E6) (h : nip a b = -1) :
    a + b ∈ rootFinset Tag.E6 := by
  have h1 : rootsE6.all (fun a => rootsE6.all fun b =>
      decide (nip a b = -1 → rootB (a + b) = true)) = true := chkA5_eq
  have h2 := List.all_eq_true.mp h1 a (rootsE6_mem.mpr ha)
  have h3 : rootB (a + b) = true :=
    of_decide_eq_true (List.all_eq_true.mp h2 b (rootsE6_mem.mpr hb)) h
  exact rootB_sound h3

theorem root_sign {a : Fin Tag.E6.rank → ℤ} (ha : a ∈ rootFinset Tag.E6) :
    (∀ i, 0 ≤ a i) ∨ ∀ i, a i ≤ 0 := by
  have h1 : rootsE6.all (fun a => decide ((∀ i, 0 ≤ a i) ∨ ∀ i, a i ≤ 0)) = true := chkA7_eq
  exact of_decide_eq_true (List.all_eq_true.mp h1 a (rootsE6_mem.mpr ha))

private lemma latGram_add_left {N : ℕ} (S : Matrix (Fin N) (Fin N) ℤ) (α β γ : Fin N → ℤ) :
    latGram S (α + β) γ = latGram S α γ + latGram S β γ := by
  simp only [latGram, Pi.add_apply, add_mul, Finset.sum_add_distrib, mul_assoc]

private lemma latGram_add_right {N : ℕ} (S : Matrix (Fin N) (Fin N) ℤ) (α β γ : Fin N → ℤ) :
    latGram S α (β + γ) = latGram S α β + latGram S α γ := by
  simp only [latGram, Pi.add_apply, mul_add, Finset.sum_add_distrib, mul_assoc]

private lemma latGram_neg_left {N : ℕ} (S : Matrix (Fin N) (Fin N) ℤ) (α β : Fin N → ℤ) :
    latGram S (-α) β = -latGram S α β := by
  simp only [latGram, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]

private lemma latGram_neg_right {N : ℕ} (S : Matrix (Fin N) (Fin N) ℤ) (α β : Fin N → ℤ) :
    latGram S α (-β) = -latGram S α β := by
  simp only [latGram, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]

private lemma latGram_sub_left {N : ℕ} (S : Matrix (Fin N) (Fin N) ℤ) (α β γ : Fin N → ℤ) :
    latGram S (α - β) γ = latGram S α γ - latGram S β γ := by
  rw [sub_eq_add_neg, latGram_add_left, latGram_neg_left, sub_eq_add_neg]

private lemma latGram_sub_right {N : ℕ} (S : Matrix (Fin N) (Fin N) ℤ) (α β γ : Fin N → ℤ) :
    latGram S α (β - γ) = latGram S α β - latGram S α γ := by
  rw [sub_eq_add_neg, latGram_add_right, latGram_neg_right, sub_eq_add_neg]

private lemma latGram_smul_matrix {N : ℕ} (k : ℤ) (C : Matrix (Fin N) (Fin N) ℤ)
    (a b : Fin N → ℤ) : latGram (k • C) a b = k * latGram C a b := by
  simp only [latGram, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

private lemma latGram_symm {N : ℕ} {S : Matrix (Fin N) (Fin N) ℤ}
    (hsym : ∀ i j, S i j = S j i) (a b : Fin N → ℤ) : latGram S a b = latGram S b a := by
  simp only [latGram]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  rw [hsym i j]
  ring

private lemma cartanE6_symm :
    ∀ i j : Fin Tag.E6.rank, Tag.cartan .E6 i j = Tag.cartan .E6 j i := by
  intro i j
  fin_cases i <;> fin_cases j <;> decide +kernel

private lemma nip_add_left (a b c : Fin Tag.E6.rank → ℤ) :
    nip (a + b) c = nip a c + nip b c := latGram_add_left _ _ _ _

private lemma nip_add_right (a b c : Fin Tag.E6.rank → ℤ) :
    nip a (b + c) = nip a b + nip a c := latGram_add_right _ _ _ _

private lemma nip_neg_left (a b : Fin Tag.E6.rank → ℤ) : nip (-a) b = -nip a b :=
  latGram_neg_left _ _ _

private lemma nip_neg_right (a b : Fin Tag.E6.rank → ℤ) : nip a (-b) = -nip a b :=
  latGram_neg_right _ _ _

private lemma nip_sub_left (a b c : Fin Tag.E6.rank → ℤ) :
    nip (a - b) c = nip a c - nip b c := latGram_sub_left _ _ _ _

private lemma nip_sub_right (a b c : Fin Tag.E6.rank → ℤ) :
    nip a (b - c) = nip a b - nip a c := latGram_sub_right _ _ _ _

private lemma nip_symm (a b : Fin Tag.E6.rank → ℤ) : nip a b = nip b a :=
  latGram_symm cartanE6_symm a b

private lemma nip_zero : nip (0 : Fin Tag.E6.rank → ℤ) 0 = 0 := by
  simp [nip, latGram]

end FiniteFacts

theorem fixed_core {k : ℕ} (hk : 0 < k)
    {S : Matrix (Fin Tag.E6.rank) (Fin Tag.E6.rank) ℤ}
    (hS : S = (k : ℤ) • Tag.cartan .E6)
    {π : Equiv.Perm (Fin Tag.E6.rank)} {Φ O : Set (Fin Tag.E6.rank → ℤ)}
    (hΦ : Φ ⊆ (rootFinset Tag.E6 : Set (Fin Tag.E6.rank → ℤ)))
    (hrefl : ∀ α ∈ Φ, ∀ β ∈ Φ, latRefl S α β ∈ Φ)
    (hadd : ∀ α ∈ Φ, ∀ β ∈ Φ,
      α + β ∈ (rootFinset Tag.E6 : Set (Fin Tag.E6.rank → ℤ)) → α + β ∈ Φ)
    (hO : ∃ α ∈ Φ, O = {β | latLinked S Φ α β})
    (hstab : ∀ γ ∈ O, latPerm π γ ∈ O) :
    ∃ γ ∈ O, latPerm π γ = γ := by
  classical
  have hk' : (0 : ℤ) < (k : ℤ) := by exact_mod_cast hk
  have hkne : (k : ℤ) ≠ 0 := by omega
  have hgram : ∀ a b, latGram S a b = (k : ℤ) * nip a b := by
    intro a b
    rw [hS, latGram_smul_matrix]
    rfl
  have hne_iff : ∀ a b, latGram S a b ≠ 0 ↔ nip a b ≠ 0 := by
    intro a b
    rw [hgram a b]
    exact ⟨fun h h0 => h (by rw [h0, mul_zero]),
      fun h h0 => h ((mul_eq_zero.mp h0).resolve_left hkne)⟩
  have hsymS : ∀ i j, S i j = S j i := by
    intro i j
    rw [hS]
    simp only [Matrix.smul_apply, smul_eq_mul]
    rw [cartanE6_symm i j]
  obtain ⟨α₀, hα₀Φ, hOeq⟩ := hO
  have hα₀O : α₀ ∈ O := by
    rw [hOeq]
    exact Relation.EqvGen.refl _
  have hiff : ∀ a b, latLinked S Φ a b → (a ∈ Φ ↔ b ∈ Φ) := by
    intro a b h
    induction h with
    | rel x y hxy => exact ⟨fun _ => hxy.2.1, fun _ => hxy.1⟩
    | refl x => exact Iff.rfl
    | symm x y _ ih => exact ih.symm
    | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2
  have hOΦ : O ⊆ Φ := by
    intro x hx
    have hx' : latLinked S Φ α₀ x := by
      have := hx
      rwa [hOeq] at this
    exact (hiff α₀ x hx').mp hα₀Φ
  have hC1 : ∀ x ∈ O, ∀ y ∈ Φ, latGram S x y ≠ 0 → y ∈ O := by
    intro x hx y hy hxy
    have hxΦ : x ∈ Φ := hOΦ hx
    have hxlink : latLinked S Φ α₀ x := by
      have := hx
      rwa [hOeq] at this
    rw [hOeq]
    exact Relation.EqvGen.trans _ _ _ hxlink (Relation.EqvGen.rel _ _ ⟨hxΦ, hy, hxy⟩)
  have hlatRefl_self : ∀ x, x ∈ (rootFinset Tag.E6 : Set (Fin Tag.E6.rank → ℤ)) →
      latRefl S x x = -x := by
    intro x hxR
    have hxx : latGram S x x = (k : ℤ) * 2 := by rw [hgram, nip_self hxR]
    have hk2 : (k : ℤ) * 2 ≠ 0 := by omega
    have hquot : 2 * latGram S x x / latGram S x x = 2 := by
      rw [hxx]
      exact Int.mul_ediv_cancel 2 hk2
    unfold latRefl
    rw [hquot, two_smul]
    abel
  have hC2 : ∀ x ∈ O, -x ∈ O := by
    intro x hx
    have hxΦ : x ∈ Φ := hOΦ hx
    have hxR : x ∈ (rootFinset Tag.E6 : Set (Fin Tag.E6.rank → ℤ)) := hΦ hxΦ
    have hxrefl : latRefl S x x ∈ Φ := hrefl x hxΦ x hxΦ
    have hnegΦ : -x ∈ Φ := by
      have := hxrefl
      rwa [hlatRefl_self x hxR] at this
    refine hC1 x hx (-x) hnegΦ ?_
    rw [hgram, nip_neg_right, nip_self hxR]
    omega
  have hC3 : ∀ x ∈ O, ∀ y ∈ O, nip x y = -1 → x + y ∈ O := by
    intro x hx y hy hxy
    have hxΦ : x ∈ Φ := hOΦ hx
    have hyΦ : y ∈ Φ := hOΦ hy
    have hxR : x ∈ rootFinset Tag.E6 := hΦ hxΦ
    have hyR : y ∈ rootFinset Tag.E6 := hΦ hyΦ
    have hsumR : x + y ∈ rootFinset Tag.E6 := nip_add_mem hxR hyR hxy
    have hsumΦ : x + y ∈ Φ := hadd x hxΦ y hyΦ hsumR
    refine hC1 x hx (x + y) hsumΦ ?_
    rw [hgram, nip_add_right, nip_self hxR, hxy]
    omega
  have hC4 : ∀ x ∈ O, ∀ y ∈ O, nip x y = 1 → x - y ∈ O := by
    intro x hx y hy hxy
    have hxΦ : x ∈ Φ := hOΦ hx
    have hyΦ : y ∈ Φ := hOΦ hy
    have hxR : x ∈ rootFinset Tag.E6 := hΦ hxΦ
    have hyR : y ∈ rootFinset Tag.E6 := hΦ hyΦ
    have hrefl_yx : latRefl S y x = x - y := by
      have hyx : latGram S y x = (k : ℤ) * 1 := by rw [hgram, nip_symm, hxy]
      have hyy : latGram S y y = (k : ℤ) * 2 := by rw [hgram, nip_self hyR]
      have hk2 : (k : ℤ) * 2 ≠ 0 := by omega
      have hquot : 2 * latGram S y x / latGram S y y = 1 := by
        rw [hyx, hyy]
        rw [show 2 * ((k : ℤ) * 1) = ((k : ℤ) * 2) * 1 by ring]
        exact Int.mul_ediv_cancel_left 1 hk2
      unfold latRefl
      rw [hquot, one_smul]
    have hsubΦ : x - y ∈ Φ := by
      have := hrefl y hyΦ x hxΦ
      rwa [hrefl_yx] at this
    refine hC1 x hx (x - y) hsubΦ ?_
    rw [hgram, nip_sub_right, nip_self hxR, hxy]
    omega
  have hC5 : ∀ {X : Set (Fin Tag.E6.rank → ℤ)} {θ : Fin Tag.E6.rank → ℤ},
      θ ∈ O → θ ∈ X →
      (∀ x ∈ O, x ∈ X → ∀ y ∈ O, latGram S x y ≠ 0 → y ∈ X) → O ⊆ X := by
    intro X θ hθO hθX hstep
    let X' : Set (Fin Tag.E6.rank → ℤ) := {x | x ∈ O ∧ x ∈ X}
    let Eqv : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ) → Prop :=
      fun a b => (a ∈ X' ↔ b ∈ X')
    haveI : IsEquiv (Fin Tag.E6.rank → ℤ) Eqv :=
      { refl := fun _ => Iff.rfl
        symm := fun _ _ h => h.symm
        trans := fun _ _ _ h1 h2 => h1.trans h2 }
    have hrle : ∀ a b, (a ∈ Φ ∧ b ∈ Φ ∧ latGram S a b ≠ 0) → Eqv a b := by
      intro a b ⟨haΦ, hbΦ, hab⟩
      constructor
      · intro haX'
        have hbO : b ∈ O := hC1 a haX'.1 b hbΦ hab
        exact ⟨hbO, hstep a haX'.1 haX'.2 b hbO hab⟩
      · intro hbX'
        have hba : latGram S b a ≠ 0 := by
          rw [latGram_symm hsymS b a]
          exact hab
        have haO : a ∈ O := hC1 b hbX'.1 a haΦ hba
        exact ⟨haO, hstep b hbX'.1 hbX'.2 a haO hba⟩
    have hle : latLinked S Φ ≤ Eqv := Relation.EqvGen.eqvGen_le hrle
    intro x hx
    have hxlink : latLinked S Φ α₀ x := by
      have := hx
      rwa [hOeq] at this
    have hθlink : latLinked S Φ α₀ θ := by
      have := hθO
      rwa [hOeq] at this
    have hlink : latLinked S Φ θ x :=
      Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ hθlink) hxlink
    have he := hle θ x hlink
    exact (he.mp ⟨hθO, hθX⟩).2
  have hC6 : ∀ θ ∈ O, ∀ γ ∈ O,
      nip θ γ ≠ 0 ∨ ∃ y ∈ O, nip θ y ≠ 0 ∧ nip y γ ≠ 0 := by
    intro θ hθ γ hγ
    let X : Set (Fin Tag.E6.rank → ℤ) :=
      fun γ => nip θ γ ≠ 0 ∨ ∃ y ∈ O, nip θ y ≠ 0 ∧ nip y γ ≠ 0
    have hθX : θ ∈ X := Or.inl (by
      have := nip_self (hΦ (hOΦ hθ))
      omega)
    have hstep : ∀ x ∈ O, x ∈ X → ∀ y ∈ O, latGram S x y ≠ 0 → y ∈ X := by
      intro x hx hxX y hy hxy
      have hxy' : nip x y ≠ 0 := (hne_iff x y).mp hxy
      by_cases hθx0 : nip θ x = 0
      · rcases hxX with hθx | ⟨y₀, hy₀O, hθy₀, hy₀x⟩
        · exact absurd hθx0 hθx
        · by_cases hy₀y : nip y₀ y = 0
          · have hx_ne : x ≠ y₀ := by
              intro h
              rw [← h] at hθy₀
              exact hθy₀ hθx0
            have hx_ne_neg : x ≠ -y₀ := by
              intro h
              have hz : nip θ (-y₀) = 0 := by rw [← h]; exact hθx0
              rw [nip_neg_right] at hz
              exact hθy₀ (neg_eq_zero.mp hz)
            have hy₀xR : y₀ ∈ rootFinset Tag.E6 := hΦ (hOΦ hy₀O)
            have hxR : x ∈ rootFinset Tag.E6 := hΦ (hOΦ hx)
            have hb := nip_bound hy₀xR hxR
            have hcase : nip y₀ x = 1 ∨ nip y₀ x = -1 := by
              have hne0 : nip y₀ x ≠ 0 := hy₀x
              have hne2 : nip y₀ x ≠ 2 := fun h => hx_ne (nip_eq_two hy₀xR hxR h).symm
              have hne_2 : nip y₀ x ≠ -2 := fun h => hx_ne_neg (nip_eq_neg_two hy₀xR hxR h)
              omega
            rcases hcase with h1 | hneg1
            · have hzO : y₀ - x ∈ O := hC4 y₀ hy₀O x hx h1
              have hzθ : nip θ (y₀ - x) ≠ 0 := by
                rw [nip_sub_right, hθx0, sub_zero]
                exact hθy₀
              have hzy : nip (y₀ - x) y ≠ 0 := by
                rw [nip_sub_left, hy₀y, zero_sub]
                exact neg_ne_zero.mpr hxy'
              exact Or.inr ⟨y₀ - x, hzO, hzθ, hzy⟩
            · have hzO : y₀ + x ∈ O := hC3 y₀ hy₀O x hx hneg1
              have hzθ : nip θ (y₀ + x) ≠ 0 := by
                rw [nip_add_right, hθx0, add_zero]
                exact hθy₀
              have hzy : nip (y₀ + x) y ≠ 0 := by
                rw [nip_add_left, hy₀y, zero_add]
                exact hxy'
              exact Or.inr ⟨y₀ + x, hzO, hzθ, hzy⟩
          · exact Or.inr ⟨y₀, hy₀O, hθy₀, hy₀y⟩
      · exact Or.inr ⟨x, hx, hθx0, hxy'⟩
    exact hC5 (X := X) hθ hθX hstep hγ
  let Oplus : Set (Fin Tag.E6.rank → ℤ) := {β | β ∈ O ∧ ∀ i, 0 ≤ β i}
  have hOplus_nonzero : ∀ β ∈ Oplus, β ≠ 0 := by
    intro β hβ h0
    have hβR : β ∈ rootFinset Tag.E6 := hΦ (hOΦ hβ.1)
    have h2 : nip β β = 2 := nip_self hβR
    have h0' : nip β β = 0 := by rw [h0]; exact nip_zero
    omega
  have hOplus_height : ∀ β ∈ Oplus, 1 ≤ height β := by
    intro β hβ
    have hnn : ∀ i, 0 ≤ β i := hβ.2
    have hsum_nn : 0 ≤ height β := Finset.sum_nonneg fun i _ => hnn i
    have hne : β ≠ 0 := hOplus_nonzero β hβ
    have hpos : 0 < height β := by
      rcases lt_or_eq_of_le hsum_nn with h | h
      · exact h
      · exfalso
        apply hne
        ext i
        have hz : (∑ i, β i) = 0 := by simpa [height] using h.symm
        have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hnn i)).mp hz i (Finset.mem_univ i)
        simpa using this
    omega
  have hD1 : ∀ β ∈ O, β ∈ Oplus ∨ -β ∈ Oplus := by
    intro β hβ
    have hβR : β ∈ rootFinset Tag.E6 := hΦ (hOΦ hβ)
    rcases root_sign hβR with hs | hs
    · exact Or.inl ⟨hβ, hs⟩
    · exact Or.inr ⟨hC2 β hβ, fun i => neg_nonneg.mpr (hs i)⟩
  have hD2 : ∀ θ ∈ Oplus, (∀ β ∈ Oplus, height β ≤ height θ) →
      ∀ β ∈ Oplus, 0 ≤ nip θ β := by
    intro θ hθ hmax β hβ
    by_contra hneg
    have hθR : θ ∈ rootFinset Tag.E6 := hΦ (hOΦ hθ.1)
    have hβR : β ∈ rootFinset Tag.E6 := hΦ (hOΦ hβ.1)
    have hb1 := nip_bound hθR hβR
    have hlt : nip θ β < 0 := lt_of_not_ge hneg
    have hcases : nip θ β = -2 ∨ nip θ β = -1 := by omega
    rcases hcases with h2 | h1
    · have hβθ : β = -θ := nip_eq_neg_two hθR hβR h2
      have hθ0 : θ = 0 := by
        ext i
        change θ i = 0
        have hi : β i = -θ i := congrFun hβθ i
        have hnnθ : 0 ≤ θ i := hθ.2 i
        have hnnβ : 0 ≤ β i := hβ.2 i
        omega
      exact hOplus_nonzero θ hθ hθ0
    · have hsumR : θ + β ∈ rootFinset Tag.E6 := nip_add_mem hθR hβR h1
      have hsumΦ : θ + β ∈ Φ := hadd θ (hOΦ hθ.1) β (hOΦ hβ.1) hsumR
      have hsumO : θ + β ∈ O := hC3 θ hθ.1 β hβ.1 h1
      have hmem : θ + β ∈ Oplus := ⟨hsumO, fun i => add_nonneg (hθ.2 i) (hβ.2 i)⟩
      have hmax' := hmax (θ + β) hmem
      have hβh : 1 ≤ height β := hOplus_height β hβ
      have hht : height (θ + β) = height θ + height β := by
        simp only [height, Pi.add_apply, Finset.sum_add_distrib]
      omega
  have hD3 : ∀ θ ∈ Oplus, (∀ β ∈ Oplus, 0 ≤ nip θ β) →
      ∀ θ' ∈ Oplus, (∀ β ∈ Oplus, 0 ≤ nip θ' β) → θ ≠ θ' → nip θ θ' = 0 := by
    intro θ hθ hdom θ' hθ' hdom' hne
    have hθR : θ ∈ rootFinset Tag.E6 := hΦ (hOΦ hθ.1)
    have hθ'R : θ' ∈ rootFinset Tag.E6 := hΦ (hOΦ hθ'.1)
    have hbound := nip_bound hθR hθ'R
    have hge : 0 ≤ nip θ θ' := hdom θ' hθ'
    have hne2 : nip θ θ' ≠ 2 := fun h => hne (nip_eq_two hθR hθ'R h)
    have hne1 : nip θ θ' ≠ 1 := by
      intro h1
      have hdO : θ - θ' ∈ O := hC4 θ hθ.1 θ' hθ'.1 h1
      have hdR : θ - θ' ∈ rootFinset Tag.E6 := hΦ (hOΦ hdO)
      rcases root_sign hdR with hdnn | hdnp
      · have hdmem : θ - θ' ∈ Oplus := ⟨hdO, hdnn⟩
        have hcontr := hdom' (θ - θ') hdmem
        have hval : nip θ' (θ - θ') = -1 := by
          rw [nip_sub_right, nip_symm θ' θ, nip_self hθ'R, h1]
          ring
        omega
      · have hnegO : -(θ - θ') ∈ O := hC2 (θ - θ') hdO
        have hnegmem : -(θ - θ') ∈ Oplus := ⟨hnegO, fun i => neg_nonneg.mpr (hdnp i)⟩
        have hcontr := hdom (-(θ - θ')) hnegmem
        have hval : nip θ (-(θ - θ')) = -1 := by
          rw [nip_neg_right, nip_sub_right, nip_self hθR, h1]
          ring
        omega
    omega
  have hD4 : ∀ θ ∈ Oplus, (∀ β ∈ Oplus, 0 ≤ nip θ β) →
      ∀ θ' ∈ Oplus, (∀ β ∈ Oplus, 0 ≤ nip θ' β) → θ = θ' := by
    intro θ hθ hdom θ' hθ' hdom'
    by_contra hne
    have hθR : θ ∈ rootFinset Tag.E6 := hΦ (hOΦ hθ.1)
    have hθ'R : θ' ∈ rootFinset Tag.E6 := hΦ (hOΦ hθ'.1)
    have horth : nip θ θ' = 0 := hD3 θ hθ hdom θ' hθ' hdom' hne
    obtain ⟨y, hyO, hθy, hyθ'⟩ : ∃ y ∈ O, nip θ y ≠ 0 ∧ nip y θ' ≠ 0 := by
      rcases hC6 θ hθ.1 θ' hθ'.1 with h | h
      · exact absurd horth h
      · exact h
    have key : ∀ y ∈ Oplus, nip θ y ≠ 0 → nip y θ' ≠ 0 → False := by
      intro y hy_plus hθy hyθ'
      have hyO : y ∈ O := hy_plus.1
      have hyR : y ∈ rootFinset Tag.E6 := hΦ (hOΦ hyO)
      have h1 : nip θ y = 1 := by
        have hge : 0 ≤ nip θ y := hdom y hy_plus
        have hne2 : nip θ y ≠ 2 := by
          intro h2
          have hyθ : y = θ := (nip_eq_two hθR hyR h2).symm
          rw [hyθ] at hyθ'
          exact hyθ' horth
        have hb := nip_bound hθR hyR
        omega
      have h1' : nip θ' y = 1 := by
        have hge : 0 ≤ nip θ' y := hdom' y hy_plus
        have hne0' : nip θ' y ≠ 0 := fun h => hyθ' (by rw [nip_symm] at h; exact h)
        have hne2 : nip θ' y ≠ 2 := by
          intro h2
          have hyθ : y = θ' := (nip_eq_two hθ'R hyR h2).symm
          rw [hyθ] at hθy
          exact hθy horth
        have hb := nip_bound hθ'R hyR
        omega
      have hdO : θ - y ∈ O := hC4 θ hθ.1 y hyO h1
      have hdR : θ - y ∈ rootFinset Tag.E6 := hΦ (hOΦ hdO)
      rcases root_sign hdR with hdnn | hdnp
      · have hdmem : θ - y ∈ Oplus := ⟨hdO, hdnn⟩
        have hcontr := hdom' (θ - y) hdmem
        have hval : nip θ' (θ - y) = -1 := by
          rw [nip_sub_right, nip_symm θ' θ, horth, h1']
          ring
        omega
      · have hnegO : -(θ - y) ∈ O := hC2 (θ - y) hdO
        have hnegmem : -(θ - y) ∈ Oplus := ⟨hnegO, fun i => neg_nonneg.mpr (hdnp i)⟩
        have hcontr := hdom (-(θ - y)) hnegmem
        have hval : nip θ (-(θ - y)) = -1 := by
          rw [nip_neg_right, nip_sub_right, nip_self hθR, h1]
          ring
        omega
    rcases hD1 y hyO with hy_plus | hy_neg
    · exact key y hy_plus hθy hyθ'
    · have hθny : nip θ (-y) ≠ 0 := by
        rw [nip_neg_right]
        exact neg_ne_zero.mpr hθy
      have hnyθ' : nip (-y) θ' ≠ 0 := by
        rw [nip_neg_left]
        exact neg_ne_zero.mpr hyθ'
      exact key (-y) hy_neg hθny hnyθ'
  let P : Finset (Fin Tag.E6.rank → ℤ) :=
    (rootFinset Tag.E6).filter fun β => β ∈ O ∧ ∀ i, 0 ≤ β i
  have hPnonempty : P.Nonempty := by
    rcases hD1 α₀ hα₀O with h | h
    · exact ⟨α₀, Finset.mem_filter.mpr ⟨hΦ hα₀Φ, h.1, h.2⟩⟩
    · exact ⟨-α₀, Finset.mem_filter.mpr ⟨hΦ (hOΦ h.1), h.1, h.2⟩⟩
  obtain ⟨θ, hθP, hθmax⟩ := Finset.exists_max_image P (@height Tag.E6) hPnonempty
  have hθO : θ ∈ O := (Finset.mem_filter.mp hθP).2.1
  have hθnn : ∀ i, 0 ≤ θ i := (Finset.mem_filter.mp hθP).2.2
  have hθplus : θ ∈ Oplus := ⟨hθO, hθnn⟩
  have hθmax' : ∀ β ∈ Oplus, height β ≤ height θ := by
    intro β hβ
    exact hθmax β (Finset.mem_filter.mpr ⟨hΦ (hOΦ hβ.1), hβ.1, hβ.2⟩)
  have hθdom : ∀ β ∈ Oplus, 0 ≤ nip θ β := hD2 θ hθplus hθmax'
  refine ⟨θ, hθO, ?_⟩
  have hθ'O : latPerm π θ ∈ O := hstab θ hθO
  have hθ'nn : ∀ i, 0 ≤ (latPerm π θ) i := fun i => hθnn (π.symm i)
  have hθ'plus : latPerm π θ ∈ Oplus := ⟨hθ'O, hθ'nn⟩
  have hθ'height : height (latPerm π θ) = height θ := by
    simp only [height, latPerm]
    exact Equiv.sum_comp π.symm θ
  have hθ'max : ∀ β ∈ Oplus, height β ≤ height (latPerm π θ) := by
    intro β hβ
    rw [hθ'height]
    exact hθmax' β hβ
  have hθ'dom : ∀ β ∈ Oplus, 0 ≤ nip (latPerm π θ) β := hD2 (latPerm π θ) hθ'plus hθ'max
  exact (hD4 θ hθplus hθdom (latPerm π θ) hθ'plus hθ'dom).symm

end LatFixedRoot

open LatFixedRoot

section E6

theorem exists_fixed_root_of_stable_component_E6 (n f : ℕ)
    (S : Matrix (Fin (ggU .E6 n f).D.rank) (Fin (ggU .E6 n f).D.rank) ℤ)
    (hS : IsRootGram (ggU .E6 n f).D S)
    (π : Equiv.Perm (Fin (ggU .E6 n f).D.rank)) (hπ : IsDiagAut (ggU .E6 n f).D π)
    {Φ O : Set (Fin (ggU .E6 n f).D.rank → ℤ)}
    (hΦ : Φ ⊆ (ggU .E6 n f).D.roots) (hrefl : ∀ α ∈ Φ, ∀ β ∈ Φ, latRefl S α β ∈ Φ)
    (hadd : ∀ α ∈ Φ, ∀ β ∈ Φ, α + β ∈ (ggU .E6 n f).D.roots → α + β ∈ Φ)
    (hO : ∃ α ∈ Φ, O = {β | latLinked S Φ α β}) (hstab : ∀ γ ∈ O, latPerm π γ ∈ O) :
    ∃ γ ∈ O, latPerm π γ = γ := by
  obtain ⟨k, hk, hS⟩ := isRootGram_E6 n f S hS
  have hsymm : Tag.symmetrizedCartan .E6 =
      (Tag.cartan .E6 : Matrix (Fin Tag.E6.rank) (Fin Tag.E6.rank) ℤ) := by
    rw [Tag.symmetrizedCartan, Tag.symmetrizer, Matrix.one_mul]
  have hS' : S = (k : ℤ) • Tag.cartan .E6 := by rw [hS, hsymm]
  refine fixed_core hk hS' ?_ hrefl ?_ hO hstab
  · intro a ha
    exact (mem_roots_E6 n f a).mp (hΦ ha)
  · intro α hα β hβ hab
    exact hadd α hα β hβ ((mem_roots_E6 n f (α + β)).mpr hab)

end E6

end CFSG.StandardType
