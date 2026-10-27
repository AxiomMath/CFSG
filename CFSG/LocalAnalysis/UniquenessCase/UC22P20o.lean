module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P20d
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20i
public import CFSG.Timmesfeld.Orders.Bang
public import CFSG.LocalAnalysis.UniquenessCase.UC22ListB
public import Certificates.Kernel.Sporadic.Fi22.C2068
public import Certificates.Kernel.Sporadic.Fi22.C3151

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.Assembly.LowTwoRank (StatedLieTag)
open scoped Pointwise

@[expose] def uc22p20oRankWit (K : Type) [Group K] (p k : ℕ) : Prop :=
  ∃ E : Subgroup K, IsElemAbelian p E ∧ Nat.card E = p ^ k

@[expose] def uc22p20oBorelWit (K : Type) [Group K] (p k : ℕ) : Prop :=
  ∀ P : Sylow 2 K, ∃ F : Subgroup K, F ≤ normalizer (P : Set K) ∧ IsElemAbelian p F ∧
    Nat.card F = p ^ k

@[expose] def uc22p20oExcl (t : StatedLieTag) (m n : ℕ) : Prop :=
  2 < n ∧ ((t = .PSL ∧ 5 ≤ m) ∨ (t = .PSU ∧ 5 ≤ m) ∨ (t = .PSp ∧ 4 ≤ m) ∨ t = .POmegaPlus ∨
    (t = .POmegaMinus ∧ 5 ≤ m) ∨ t = .F4 ∨ t = .E6 ∨ t = .E7 ∨ t = .E8 ∨ t = .twistedE6)

@[expose] def uc22p20oTwo (t : StatedLieTag) (m n : ℕ) : Prop :=
  (2 < n ∧ ((t = .PSL ∧ (m = 3 ∨ m = 4)) ∨ (t = .PSU ∧ (m = 3 ∨ m = 4)) ∨ t = .G2 ∨
    t = .trialityD4 ∨ t = .twistedF4 ∨ (t = .PSp ∧ (m = 2 ∨ m = 3)) ∨ (t = .POmegaMinus ∧ m = 4))) ∨
  (n = 2 ∧ ((t = .PSU ∧ (m = 4 ∨ m = 5)) ∨ t = .trialityD4 ∨ (t = .POmegaMinus ∧ m = 4))) ∨
  (n = 1 ∧ t = .trialityD4)

@[expose] def uc22p20oNoOddMult (t : StatedLieTag) (m n : ℕ) : Prop :=
  (2 < n ∧ ((t = .PSL ∧ (m = 2 ∨ m = 4)) ∨ (t = .PSU ∧ m = 4) ∨ t = .G2 ∨ t = .trialityD4 ∨
    t = .twistedF4 ∨ t = .twistedB2 ∨ (t = .PSp ∧ (m = 2 ∨ m = 3)) ∨ (t = .POmegaMinus ∧ m = 4))) ∨
  (n = 2 ∧ ((t = .PSU ∧ m = 4) ∨ t = .trialityD4 ∨ (t = .POmegaMinus ∧ m = 4))) ∨
  (n = 1 ∧ t = .trialityD4)

@[expose] def uc22p20oExclWitness : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K → Odd (Nat.card (center K)) →
    ∀ (t : StatedLieTag) (m n : ℕ),
      (uc22p20oExcl t m n ∨ (t = .PSU ∧ m = 5 ∧ n = 2 ∧ center K ≠ ⊥)) →
      LieModel (K ⧸ center K) t m 2 n →
      ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧
        ((p = 3 ∧ uc22p20oRankWit K 3 4) ∨ (uc22p20oRankWit K p 4 ∧ uc22p20oBorelWit K p 2))

@[expose] def uc22p20oTwoWitness : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K → Odd (Nat.card (center K)) →
    ∀ (t : StatedLieTag) (m n : ℕ), uc22p20oTwo t m n →
      LieModel (K ⧸ center K) t m 2 n →
      (t = .PSU ∧ m = 3 ∧ n = 3 → False) →
      ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ ¬ p ∣ Nat.card (center K) ∧ uc22p20oRankWit K p 2 ∧
        (p = 3 ∨ uc22p20oBorelWit K p 1)

@[expose] def uc22p20oU38Witness : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K → Odd (Nat.card (center K)) →
    IsU3 (K ⧸ center K) 3 → Nat.card (center K) ∣ 3 ∧ uc22p20oRankWit K 3 2

@[expose] def uc22p20oTrivialCenter : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K → Odd (Nat.card (center K)) →
    ∀ (t : StatedLieTag) (m n : ℕ), uc22p20oNoOddMult t m n →
      LieModel (K ⧸ center K) t m 2 n → center K = ⊥

@[expose] def uc22p20oA9Witness : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K → Odd (Nat.card (center K)) →
    Nonempty ((K ⧸ center K) ≃* alternatingGroup (Fin 9)) → center K = ⊥ ∧ uc22p20oRankWit K 3 2

structure Global22f : Prop where
  excl : uc22p20oExclWitness
  two : uc22p20oTwoWitness
  u38 : uc22p20oU38Witness
  center : uc22p20oTrivialCenter
  a9 : uc22p20oA9Witness

@[expose] def uc22p20oShapeOne (X : Type) [Group X] : Prop :=
  (∃ n : ℕ, 2 < n ∧ (IsSz X n ∨ IsL2 X n ∨ IsL3 X n ∨ IsU3 X n ∨ LieModel X .PSL 4 2 n ∨ IsU4 X n ∨
      IsG2 X n ∨ Is3D4 X n ∨ LieModel X .twistedF4 0 2 n ∨ IsSp4 X n ∨ IsSL3 X n ∨ IsSU3 X n ∨
      LieModel X .PSp 3 2 n ∨ IsOmega8m X n)) ∨
    IsU4 X 2 ∨ IsU5 X 2 ∨ IsOmega8m X 2 ∨ Is3D4 X 2 ∨ Is3D4 X 1

theorem uc22p20o_two_pow_two_mul_sub_one (a : ℕ) : 2 ^ (2 * a) - 1 = (2 ^ a - 1) * (2 ^ a + 1) := by
  have h2 : 2 ^ (2 * a) = 2 ^ a * 2 ^ a := by rw [← pow_add]; ring_nf
  have h3 := Nat.mul_self_sub_mul_self_eq (2 ^ a) 1
  rw [h2]
  simpa [mul_comm] using h3

theorem uc22p20o_two_pow_mod_three : ∀ m : ℕ, 2 ^ m % 3 = 1 ∨ 2 ^ m % 3 = 2 := by
  intro m
  induction m with
  | zero => simp
  | succ k ih =>
    have h' : 2 ^ (k + 1) % 3 = (2 ^ k % 3 * 2) % 3 := by rw [pow_succ, Nat.mul_mod]
    rcases ih with h | h <;> simp [h', h]

theorem uc22p20o_prime_sub_one_ne_three {n : ℕ} (hn : 3 ≤ n) :
    ∃ p : ℕ, p.Prime ∧ p ∣ 2 ^ n - 1 ∧ p ≠ 3 := by
  by_cases h6 : n = 6
  · exact ⟨7, by norm_num, by subst h6; norm_num, by norm_num⟩
  · obtain ⟨p, hp, hpd, hmin⟩ := CFSG.Timmesfeld.exists_primitive_prime_dvd_two_pow_sub_one n (by omega) h6
    refine ⟨p, hp, hpd, ?_⟩
    rintro rfl
    exact hmin 2 (by norm_num) (by omega) (by norm_num)

theorem uc22p20o_prime_sub_one_ne_five {n : ℕ} (hn : 2 ≤ n) :
    ∃ p : ℕ, p.Prime ∧ p ∣ 2 ^ n - 1 ∧ p ≠ 5 := by
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  · refine ⟨3, Nat.prime_three, ?_, by norm_num⟩
    have : n = 2 * m := by omega
    subst this
    rw [uc22p20o_two_pow_two_mul_sub_one]
    have : 3 ∣ 2 ^ m + 1 ∨ 3 ∣ 2 ^ m - 1 := by
      have h := Nat.one_le_two_pow (n := m)
      have := uc22p20o_two_pow_mod_three m
      omega
    rcases this with h | h
    · exact Dvd.dvd.mul_left h _
    · exact Dvd.dvd.mul_right h _
  · have h1 : 2 ^ n - 1 ≠ 1 := by
      have : 4 ≤ 2 ^ n := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
      omega
    refine ⟨Nat.minFac (2 ^ n - 1), Nat.minFac_prime h1, Nat.minFac_dvd _, ?_⟩
    intro h5
    have hd : 5 ∣ 2 ^ n - 1 := h5 ▸ Nat.minFac_dvd _
    have h4 : 2 ^ n % 5 = 2 ∨ 2 ^ n % 5 = 3 := by
      subst hm
      have : ∀ k : ℕ, 2 ^ (2 * k + 1) % 5 = 2 ∨ 2 ^ (2 * k + 1) % 5 = 3 := by
        intro k
        induction k with
        | zero => simp
        | succ j ih =>
          have : 2 ^ (2 * (j + 1) + 1) = 4 * 2 ^ (2 * j + 1) := by ring
          rw [this]; omega
      exact this m
    have := Nat.one_le_two_pow (n := n)
    omega

theorem uc22p20o_prime_add_one_ne_three_five {n : ℕ} (hn : 4 ≤ n) :
    ∃ p : ℕ, p.Prime ∧ p ∣ 2 ^ n + 1 ∧ p ≠ 3 ∧ p ≠ 5 := by
  obtain ⟨p, hp, hpd, hmin⟩ := CFSG.Timmesfeld.exists_primitive_prime_dvd_two_pow_sub_one (2 * n) (by omega) (by omega)
  rw [uc22p20o_two_pow_two_mul_sub_one] at hpd
  have hnd : ¬ p ∣ 2 ^ n - 1 := hmin n (by omega) (by omega)
  have hd : p ∣ 2 ^ n + 1 := by
    rcases (Nat.Prime.dvd_mul hp).1 hpd with h | h
    · exact absurd h hnd
    · exact h
  refine ⟨p, hp, hd, ?_, ?_⟩
  · rintro rfl
    exact hmin 2 (by norm_num) (by omega) (by norm_num)
  · rintro rfl
    exact hmin 4 (by norm_num) (by omega) (by norm_num)

section Bookkeeping

variable {G : Type} [Group G] [Finite G]

theorem uc22p20o_oTwoE_top (D : Data G) {L : Subgroup G} (hL : L ∈ calL D.T D.M) : OTwoE ↥L = ⊤ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨K, hK, hLK⟩ := hL.2.2.2
  have hH : L ⊔ D.T ∈ hSet D.T D.M := hL.2.2.1
  set H : Subgroup G := L ⊔ D.T with hHdef
  have hLH : L ≤ H := le_sup_left
  have hTH : D.T ≤ H := le_sup_right
  have hLn : (L.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLH).2 (sup_le Subgroup.le_normalizer hL.1)
  have hsub : CFSG.Open.IsSubnormal L H := .step hLH hLn (.refl H)
  have hKc : K ∈ CFSG.Quasithin.cComp L := uc22p20e_cComp_of_calC hK
  have hKH : K ∈ CFSG.Quasithin.cComp H := CFSG.Quasithin.cComp_mem_of_subnormal hsub hKc
  have hcC : CFSG.Quasithin.cComp L = Set.range (fun t : D.T => uc22p20bCj (t : G) K) := by
    have h := uc22p20b_cComp_orb hKH hTH
    have e : uc22p20bOrb D.T K = L := hLK.symm
    rwa [e] at h
  haveI hPn : (CFSG.pCore 2 ↥L).Normal := CFSG.pCore_normal
  haveI hPs : Group.IsSolvable ↥(CFSG.pCore 2 ↥L) := uc22p20d_pCore_solvable L
  have hπ : Function.Surjective (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) :=
    QuotientGroup.mk'_surjective _
  have hcomp : ∀ t : D.T, CFSG.IsComponent
      (((uc22p20bCj (t : G) K).subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L))) := by
    intro t
    have hKt : uc22p20bCj (t : G) K ∈ CFSG.Quasithin.cComp L := by rw [hcC]; exact ⟨t, rfl⟩
    have hKtL : uc22p20bCj (t : G) K ≤ L := CFSG.Quasithin.le_of_mem_cComp hKt
    have hKtsub : CFSG.Open.IsSubnormal (uc22p20bCj (t : G) K) L :=
      CFSG.Quasithin.subnormal_of_mem_cComp hKt
    have hK' : (uc22p20bCj (t : G) K).subgroupOf L ∈ CFSG.Quasithin.cComp (⊤ : Subgroup ↥L) :=
      CFSG.Quasithin.subgroupOf_mem_cComp hKt
    have hKbar := CFSG.Quasithin.map_mem_cComp_top (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) hπ
      (by rw [QuotientGroup.ker_mk']; exact hPs) hK'
    refine ⟨?_, CFSG.Quasithin.A3.subnormal_top_iff.mp
      (CFSG.Quasithin.subnormal_of_mem_cComp hKbar)⟩
    obtain ⟨e, -⟩ := uc22p20d_bar2Equiv hKtL hKtsub
    obtain ⟨f⟩ := uc22p20d_bar2_conj (t : G) K
    have hqKt : CFSG.Open.IsQuasisimple (Bar2 (uc22p20bCj (t : G) K)) :=
      CFSG.Open.IsQuasisimple.of_mulEquiv f.symm hK.2.2
    exact CFSG.Quasithin.A3.isQuasisimple_iff_open.mpr (CFSG.Open.IsQuasisimple.of_mulEquiv e.symm hqKt)
  have hlayer : CFSG.layer (↥L ⧸ CFSG.pCore 2 ↥L) = ⊤ := by
    have hW : L ≤ ((CFSG.layer (↥L ⧸ CFSG.pCore 2 ↥L)).comap
        (QuotientGroup.mk' (CFSG.pCore 2 ↥L))).map L.subtype := by
      refine hLK.le.trans (iSup_le fun t => ?_)
      intro g hg
      have hg' : g ∈ uc22p20bCj (t : G) K := hg
      have hKt : uc22p20bCj (t : G) K ∈ CFSG.Quasithin.cComp L := by rw [hcC]; exact ⟨t, rfl⟩
      have hgL : g ∈ L := CFSG.Quasithin.le_of_mem_cComp hKt hg'
      refine ⟨⟨g, hgL⟩, ?_, rfl⟩
      exact CFSG.LocalCores.component_le_layer (hcomp t)
        ⟨⟨g, hgL⟩, Subgroup.mem_subgroupOf.2 hg', rfl⟩
    rw [eq_top_iff]
    intro y _
    obtain ⟨x, rfl⟩ := hπ y
    obtain ⟨x', hx', hxx'⟩ := hW x.2
    have : x' = x := Subtype.ext hxx'
    exact this ▸ hx'
  show (CFSG.layer (↥L ⧸ CFSG.pCore 2 ↥L)).comap (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) = ⊤
  rw [hlayer]
  exact Subgroup.comap_top _

theorem uc22p20o_orbit_card (D : Data G) (K : Subgroup G) :
    ∃ k : ℕ, Nat.card (Set.range fun t : D.T => uc22p20bCj (t : G) K) = 2 ^ k := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : MulAction ↥D.T (Subgroup G) :=
    MulAction.compHom (Subgroup G) (ConjAct.toConjAct.toMonoidHom.comp D.T.subtype)
  have hsmul : ∀ t : D.T, t • K = uc22p20bCj (t : G) K := by
    intro t
    have h0 : t • K = (ConjAct.toConjAct (t : G)) • K := rfl
    rw [h0]
    ext x
    simp only [uc22p20bCj, Subgroup.mem_map, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe,
      MulAut.conj_apply]
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    simp only [ConjAct.smul_def, map_inv, ConjAct.ofConjAct_toConjAct, inv_inv]
    constructor
    · intro h; exact ⟨(t : G)⁻¹ * x * (t : G), h, by group⟩
    · rintro ⟨y, hy, rfl⟩; simpa [mul_assoc] using hy
  have horb : Set.range (fun t : D.T => uc22p20bCj (t : G) K) = MulAction.orbit ↥D.T K := by
    ext X
    simp only [Set.mem_range, MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨t, rfl⟩; exact ⟨t, hsmul t⟩
    · rintro ⟨t, rfl⟩; exact ⟨t, (hsmul t).symm⟩
  rw [horb, Nat.card_coe_set_eq, ← MulAction.index_stabilizer]
  obtain ⟨m, hm⟩ := D.sylowM.isPGroup.exists_card_eq
  have hdvd : (MulAction.stabilizer ↥D.T K).index ∣ 2 ^ m := hm ▸ Subgroup.index_dvd_card _
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  exact ⟨k, hk⟩

theorem uc22p20o_rank_data4 (D : Data G) (hQ : QuasisimpleDichotomy) {H : Subgroup G}
    (hHtop : H ≠ ⊤) (hH : H ∈ hSet D.T D.M) {K : Subgroup G} (hK : K ∈ CFSG.Quasithin.cComp H)
    (g : Fin 4 → G) (hg : ∀ i, g i ∈ H) (hinj : Function.Injective fun i => uc22p20bCj (g i) K)
    (hO : OTwoE ↥(uc22p20bOrb H K) = ⊤) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ ∃ E : Subgroup G, E ≤ H ∧ IsElemAbelian p E ∧
      Nat.card E = p ^ 4 ∧
      (p = 3 ∨ ∃ Z : Subgroup G, D.T ≤ Z ∧ Z ≤ H ∧ Group.IsSolvable ↥Z ∧ E ≤ Z) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Y : Subgroup G := uc22p20bOrb H K with hYdef
  have hKH : K ≤ H := CFSG.Quasithin.le_of_mem_cComp hK
  have hYH : Y ≤ H := uc22p20b_orb_le le_rfl hKH
  have hHn : H ≤ normalizer (Y : Set G) := uc22p20b_le_normalizer_orb H K
  have hspan : sSup (CFSG.Quasithin.cComp Y) = Y := uc22p20b_sSup_cComp_orb hK le_rfl
  have hcC : CFSG.Quasithin.cComp Y = Set.range (fun t : H => uc22p20bCj (t : G) K) :=
    uc22p20b_cComp_orb hK le_rfl
  have hKi : ∀ i, uc22p20bCj (g i) K ∈ CFSG.Quasithin.cComp Y := fun i => by
    rw [hcC]; exact ⟨⟨g i, hg i⟩, rfl⟩
  have hK0 : K ∈ CFSG.Quasithin.cComp Y := by
    rw [hcC]; exact ⟨⟨1, H.one_mem⟩, uc22p20b_cj_one K⟩
  have hqs : CFSG.Open.IsQuasisimple (Bar2 K) := uc22p20b_isQuasisimple_bar2 hO hK0
  have hKiY : ∀ i, uc22p20bCj (g i) K ≤ Y := fun i => CFSG.Quasithin.le_of_mem_cComp (hKi i)
  have hKisub : ∀ i, CFSG.Open.IsSubnormal (uc22p20bCj (g i) K) Y := fun i =>
    CFSG.Quasithin.subnormal_of_mem_cComp (hKi i)
  have hne : ∀ i j, i ≠ j → uc22p20bCj (g i) K ≠ uc22p20bCj (g j) K :=
    fun i j h h' => h (hinj h')
  have e : ∀ i, Bar2 K ≃* Bar2 (uc22p20bCj (g i) K) := fun i =>
    (uc22p20d_bar2_conj (g i) K).some
  haveI hPn : (CFSG.pCore 2 ↥Y).Normal := CFSG.pCore_normal
  let φ : ↥Y →* ↥Y ⧸ CFSG.pCore 2 ↥Y := QuotientGroup.mk' (CFSG.pCore 2 ↥Y)
  let A : Fin 4 → Subgroup (↥Y ⧸ CFSG.pCore 2 ↥Y) := fun i =>
    ((uc22p20bCj (g i) K).subgroupOf Y).map φ
  have hcomm : ∀ i j, i ≠ j → ∀ a ∈ A i, ∀ b ∈ A j, a * b = b * a := fun i j hij =>
    uc22p20d_commute_images hO (hKi i) (hKi j) (hne i j hij)
  have hmemA : ∀ (i : Fin 4) (c : ↥(uc22p20bCj (g i) K)),
      (QuotientGroup.mk (Subgroup.inclusion (hKiY i) c) : ↥Y ⧸ CFSG.pCore 2 ↥Y) ∈ A i :=
    fun i c => Subgroup.mem_map.2 ⟨Subgroup.inclusion (hKiY i) c,
      Subgroup.mem_subgroupOf.2 c.2, rfl⟩
  have hcat : CFSG.Assembly.InCatalog (Bar2 K ⧸ Subgroup.center (Bar2 K)) :=
    uc22p20d_inCatalog_bar2 D.standing.kProper
      (fun h => hHtop (top_le_iff.mp (h ▸ hKH))) hqs
  rcases hQ (Bar2 K) hqs hcat with ⟨x₀, hx₀o, hx₀z⟩ | ⟨p, hp, hp2, hP⟩
  ·
    have hsel : ∀ i, ∃ c : ↥(uc22p20bCj (g i) K),
        (QuotientGroup.mk c : Bar2 (uc22p20bCj (g i) K)) = e i x₀ := fun i =>
      QuotientGroup.mk_surjective (e i x₀)
    choose c hc using hsel
    have hx₀p : x₀ ^ 3 = 1 := by rw [← hx₀o]; exact pow_orderOf_eq_one x₀
    have hprops := fun i => uc22p20d_image_props (hKiY i) (hKisub i) (p := 3) (c i)
      (by rw [hc i, ← map_pow, hx₀p, map_one])
      (by rw [hc i]; exact uc22p20d_not_mem_center_map (e i) hx₀z)
    obtain ⟨E₀, -, hE₀, hE₀c⟩ := uc22p20d_elemAbelian_of_commuting
      (X := ↥Y ⧸ CFSG.pCore 2 ↥Y) 3 4 Nat.prime_three A
      (fun i => (QuotientGroup.mk (Subgroup.inclusion (hKiY i) (c i)) : ↥Y ⧸ CFSG.pCore 2 ↥Y))
      hcomm (fun i => hmemA i (c i)) (fun i => (hprops i).1) (fun i => (hprops i).2)
    obtain ⟨E, -, hE, hEc⟩ := uc22p20d_lift_elemAbelian (CFSG.pCore 2 ↥Y)
      (CFSG.pCore_isPGroup) Nat.prime_three (by norm_num) (⊤ : Subgroup ↥Y) E₀ hE₀ hE₀c
      (by rw [Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]; exact le_top)
    refine ⟨3, Nat.prime_three, by norm_num, E.map Y.subtype,
      (Subgroup.map_subtype_le E).trans hYH,
      uc22p20d_isElemAbelian_map Y.subtype Y.subtype_injective hE, ?_, Or.inl rfl⟩
    rw [Subgroup.card_map_of_injective Y.subtype_injective, hEc]
  ·
    set U : Subgroup G := D.T ⊓ Y with hU
    have hTH : CFSG.ABGLocalTools.IsSylowOf 2 D.T H := D.sylowG.of_le hH.1 le_top
    have hUY : CFSG.ABGLocalTools.IsSylowOf 2 U Y := hTH.inf_of_le_normalizer hYH hHn
    have hSyl := uc22p20d_isSylowOf_inf_comp hspan hUY
    have hsel : ∀ i, ∃ c : ↥(uc22p20bCj (g i) K),
        ((c : ↥(uc22p20bCj (g i) K)) : G) ∈ uc22p20dB U (uc22p20bCj (g i) K) ∧
          orderOf (QuotientGroup.mk c : Bar2 (uc22p20bCj (g i) K)) = p ∧
          (QuotientGroup.mk c : Bar2 (uc22p20bCj (g i) K)) ∉
            Subgroup.center (Bar2 (uc22p20bCj (g i) K)) := fun i =>
      uc22p20d_mem_B (hSyl _ (hKi i)) p (uc22p20d_transport_sylow (e i) hP)
    choose c hcB hco hcz using hsel
    have hprops := fun i => uc22p20d_image_props (hKiY i) (hKisub i) (p := p) (c i)
      (by rw [← hco i]; exact pow_orderOf_eq_one _) (hcz i)
    obtain ⟨E₀, hE₀le, hE₀, hE₀c⟩ := uc22p20d_elemAbelian_of_commuting
      (X := ↥Y ⧸ CFSG.pCore 2 ↥Y) p 4 hp A
      (fun i => (QuotientGroup.mk (Subgroup.inclusion (hKiY i) (c i)) : ↥Y ⧸ CFSG.pCore 2 ↥Y))
      hcomm (fun i => hmemA i (c i)) (fun i => (hprops i).1) (fun i => (hprops i).2)
    set D' : Subgroup G := uc22p20dD U (CFSG.Quasithin.cComp Y) with hD'
    have hD'mem : ∀ i, ((c i : ↥(uc22p20bCj (g i) K)) : G) ∈ D' := fun i =>
      (le_iSup₂ (f := fun (C : Subgroup G) (_ : C ∈ CFSG.Quasithin.cComp Y) => uc22p20dB U C)
        (uc22p20bCj (g i) K) (hKi i)) (hcB i)
    have hD'Y : D' ≤ Y := iSup₂_le fun C hC =>
      (uc22p20dB_le U C).trans (CFSG.Quasithin.le_of_mem_cComp hC)
    obtain ⟨E, hEB, hE, hEc⟩ := uc22p20d_lift_elemAbelian (CFSG.pCore 2 ↥Y)
      (CFSG.pCore_isPGroup) hp hp2 (D'.subgroupOf Y) E₀ hE₀ hE₀c (by
        refine hE₀le.trans ((Subgroup.closure_le _).2 ?_)
        rintro _ ⟨i, rfl⟩
        exact Subgroup.mem_map.2 ⟨Subgroup.inclusion (hKiY i) (c i),
          Subgroup.mem_subgroupOf.2 (hD'mem i), rfl⟩)
    have hEG : E.map Y.subtype ≤ D' := by
      rintro _ ⟨x, hx, rfl⟩
      exact Subgroup.mem_subgroupOf.1 (hEB hx)
    have hDsolv : Group.IsSolvable ↥D' := uc22p20d_solvable_D hO hspan hUY
    have hTY : D.T ≤ normalizer (Y : Set G) := hH.1.trans hHn
    have h𝒪 : ∀ t ∈ D.T, ∀ C ∈ CFSG.Quasithin.cComp Y, uc22p20bCj t C ∈ CFSG.Quasithin.cComp Y := by
      intro t ht C hC
      rw [hcC] at hC ⊢
      obtain ⟨⟨s, hs⟩, rfl⟩ := hC
      exact ⟨⟨t * s, H.mul_mem (hH.1 ht) hs⟩, (uc22p20b_cj_cj t s K).symm⟩
    have hTn : D.T ≤ normalizer (D' : Set G) :=
      uc22p20d_T_le_normalizer_D hU hTY (CFSG.Quasithin.cComp Y) h𝒪
    have hTs : Group.IsSolvable ↥D.T := by
      haveI : Group.IsNilpotent ↥D.T := D.sylowM.isPGroup.isNilpotent
      infer_instance
    haveI := hDsolv
    haveI := hTs
    have hZs : Group.IsSolvable ↥(D' ⊔ D.T) := CFSG.Quasithin.A3.isSolvable_sup_of_le_normalizer hTn
    refine ⟨p, hp, hp2, E.map Y.subtype, (hEG.trans hD'Y).trans hYH,
      uc22p20d_isElemAbelian_map Y.subtype Y.subtype_injective hE, ?_,
      Or.inr ⟨D' ⊔ D.T, le_sup_right, sup_le (hD'Y.trans hYH) hH.1, hZs, hEG.trans le_sup_left⟩⟩
    rw [Subgroup.card_map_of_injective Y.subtype_injective, hEc]

theorem uc22p20o_false_of_rank4 (D : Data G) (hB : ListBNonabelian) (h20_1 : S20_1_124 D)
    (h1930 : H1930 D) {H : Subgroup G} (hH : H ∈ hSet D.T D.M)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {E : Subgroup G} (hEH : E ≤ H)
    (hE : IsElemAbelian p E) (hcard : Nat.card E = p ^ 4)
    (hloc : p = 3 ∨ ∃ Z : Subgroup G, D.T ≤ Z ∧ Z ≤ H ∧ Group.IsSolvable ↥Z ∧ E ≤ Z) :
    False := by
  have h4 : 4 ≤ CFSG.Open.pRank p H := CFSG.SectionRank.le_pRank hp.one_lt hEH hE hcard
  obtain ⟨h1, h2, -⟩ := h20_1 h1930 H hH
  rcases hloc with rfl | ⟨Z, hTZ, hZH, hZs, hEZ⟩
  · omega
  · have hZM : Z ≤ D.M := uc22p20b_le_M_of_solvable D hB h1930 hH hTZ hZH hZs
    have hEHM : E ≤ H ⊓ D.M := le_inf hEH (hEZ.trans hZM)
    have h5 : 4 ≤ CFSG.Open.pRank p (H ⊓ D.M) := CFSG.SectionRank.le_pRank hp.one_lt hEHM hE hcard
    have h6 := h2 p hp hp2 (by omega)
    omega

theorem uc22p20o_four_comps (D : Data G) (hQ : QuasisimpleDichotomy) (hB : ListBNonabelian)
    (h20_1 : S20_1_124 D) (h1930 : H1930 D) {L K : Subgroup G} (hL : L ∈ calL D.T D.M)
    (hOT : OTwoE ↥L = ⊤) (hK : K ∈ calC L) (hLK : L = uc22p20bOrb D.T K) (g : Fin 4 → G)
    (hg : ∀ i, g i ∈ D.T) (hinj : Function.Injective fun i => uc22p20bCj (g i) K) : False := by
  have hH : L ⊔ D.T ∈ hSet D.T D.M := hL.2.2.1
  set H : Subgroup G := L ⊔ D.T with hHdef
  have hLH : L ≤ H := le_sup_left
  have hTH : D.T ≤ H := le_sup_right
  have hHtop : H ≠ ⊤ := by
    haveI := D.standing.simple
    obtain ⟨N, hN, hHN⟩ := uc22p20a_exists_mem_calMOf D hH
    intro htop
    have hNtop : N = ⊤ := top_le_iff.mp (htop ▸ hHN)
    exact CFSG.PreuniquenessRankFour.Helpers.twoLocal_ne_top D.standing.nonab hN.1.1 hNtop
  have hLn : (L.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLH).2 (sup_le Subgroup.le_normalizer hL.1)
  have hsub : CFSG.Open.IsSubnormal L H := .step hLH hLn (.refl H)
  have hKc : K ∈ CFSG.Quasithin.cComp L := uc22p20e_cComp_of_calC hK
  have hKH : K ∈ CFSG.Quasithin.cComp H := CFSG.Quasithin.cComp_mem_of_subnormal hsub hKc
  have hHn : H ≤ normalizer (L : Set G) := sup_le Subgroup.le_normalizer hL.1
  have hOrb : uc22p20bOrb H K = L := by
    apply le_antisymm
    · refine iSup_le fun t x hx => ?_
      obtain ⟨y, hy, rfl⟩ := uc22p20b_mem_cj.1 hx
      have hyL : y ∈ L := CFSG.Quasithin.le_of_mem_cComp hKc hy
      exact (Subgroup.mem_normalizer_iff.1 (hHn t.2) y).1 hyL
    · rw [hLK]
      exact iSup_le fun t => le_iSup_of_le ⟨(t : G), hTH t.2⟩ le_rfl
  obtain ⟨p, hp, hp2, E, hEH, hE, hcard, hloc⟩ := uc22p20o_rank_data4 D hQ hHtop hH hKH g
    (fun i => hTH (hg i)) hinj (by rw [hOrb]; exact hOT)
  exact uc22p20o_false_of_rank4 D hB h20_1 h1930 hH hp hp2 hEH hE hcard hloc

theorem uc22p20o_core (D : Data G) (hB : ListBNonabelian) (h1930 : H1930 D) (h20_1 : S20_1_124 D)
    {L : Subgroup G} (hL : L ∈ calL D.T D.M) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (E : Subgroup (Bar2 L)) (hE : IsElemAbelian p E) (hEc : Nat.card E = p ^ 4)
    (hloc : p = 3 ∨ ∃ F : Subgroup (Bar2 L), IsElemAbelian p F ∧ Nat.card F = p ^ 2 ∧
      F ≤ normalizer ((uc22p20iSylowBar D L : Subgroup (Bar2 L)) : Set (Bar2 L))) : False := by
  obtain ⟨h1, h2⟩ := uc22p20i_rank_bounds D hB h1930 h20_1 hL
  have h4 : 4 ≤ CFSG.Open.pRank p (⊤ : Subgroup (Bar2 L)) :=
    CFSG.SectionRank.le_pRank hp.one_lt le_top hE hEc
  rcases hloc with rfl | ⟨F, hF, hFc, hFle⟩
  · omega
  · have h5 : 2 ≤ CFSG.Open.pRank p (normalizer ((uc22p20iSylowBar D L : Subgroup (Bar2 L)) :
        Set (Bar2 L))) := CFSG.SectionRank.le_pRank hp.one_lt hFle hF hFc
    have h6 := h2 p hp hp2 (by omega)
    omega

theorem uc22p20o_excl_false_one (hG : Global22f) (hB : ListBNonabelian) (D : Data G)
    (h20_1 : S20_1_124 D) (h1930 : H1930 D) {L : Subgroup G} (hL : L ∈ calL D.T D.M)
    (hLc : L ∈ calC L) {t : StatedLieTag} {m n : ℕ} (hodd : Odd (Nat.card (center (Bar2 L))))
    (hex : uc22p20oExcl t m n ∨ (t = .PSU ∧ m = 5 ∧ n = 2 ∧ center (Bar2 L) ≠ ⊥))
    (hM : LieModel (Bar2 L ⧸ center (Bar2 L)) t m 2 n) : False := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq : CFSG.Open.IsQuasisimple (Bar2 L) := hLc.2.2
  obtain ⟨p, hp, hp2, h⟩ := hG.excl (Bar2 L) hq hodd t m n hex hM
  rcases h with ⟨rfl, E, hE, hEc⟩ | ⟨⟨E, hE, hEc⟩, hBor⟩
  · exact uc22p20o_core D hB h1930 h20_1 hL hp hp2 E hE hEc (Or.inl rfl)
  · obtain ⟨F, hFN, hF, hFc⟩ := hBor
      ((uc22p20i_sylowBar_isPGroup D).toSylow (uc22p20i_sylowBar_index D hL))
    exact uc22p20o_core D hB h1930 h20_1 hL hp hp2 E hE hEc (Or.inr ⟨F, hF, hFc, hFN⟩)

end Bookkeeping

end CFSG.LocalAnalysis.UniquenessCase.UC22
