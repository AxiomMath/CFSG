module

public import CFSG.Quasithin.Recognition.St84.Sec48A
public import CFSG.GroupTheory.SubgroupCardMul
public import CFSG.GroupTheory.Commutator.SupNormalizer
public import CFSG.Timmesfeld.LocalTwoSubgroups.CoprimeActionBounds
public import CFSG.Quasithin.Vol2.Ch11SecO8HB
public import CFSG.Quasithin.Vol2.Ch8Sec2KGCover
public import CFSG.Quasithin.Vol2.Ch10SecACoprime
public import CFSG.Quasithin.Recognition.St84.Gen.OTwoResL2
public import CFSG.Quasithin.Recognition.St84.TransportMap
public import CFSG.LocalAnalysis.SteinbergBVA7ConstantRankFactorization
public import CFSG.Quasithin.Recognition.St84.Gen.NatSecPre
public import CFSG.Quasithin.Recognition.St84.Gen.NatSecLines
public import CFSG.Quasithin.Recognition.St84.Gen.L2SecFinite
public import CFSG.Quasithin.Recognition.GoldschmidtF112RAutJ2

public section

namespace CFSG.Quasithin.St84

open SimpleGraph CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.Fan86
  CFSG.GH74.QTGen4.DSGen4 CFSG.Quasithin.F6.GoldAmL3T CFSG.Quasithin.F7

open scoped Pointwise commutatorElement

variable {V : Type*} {G : Type} [Group G] [MulAction G V] {Γ : SimpleGraph V} {s : ℕ}

namespace Setup

variable (X : Setup Γ G)

abbrev Vk (k : ℤ) : Subgroup G :=
  ⨆ (g : G) (_ : g ∈ X.L k), conjSub g (X.Z (k + 1))

abbrev R48 (d : ℕ) : Subgroup G := ⁅X.Z (-1), X.Z ((d : ℤ) + 1)⁆

theorem Vk_add (m k : ℤ) :
    X.Vk (k + 2 * m) = conjSub (X.τ ^ m) (X.Vk k) := by
  unfold Setup.Vk
  simp_rw [conjSub_iSup]
  refine le_antisymm ?_ ?_
  · refine iSup_le fun h => iSup_le fun hh => ?_
    have hh' : (X.τ ^ m)⁻¹ * h * (X.τ ^ m) ∈ X.L k := by
      rw [X.L_add] at hh
      exact mem_conjSub.mp (by convert hh using 1 <;> group)
    have hZ : X.Z (k + 2 * m + 1) = conjSub (X.τ ^ m) (X.Z (k + 1)) := by
      rw [show k + 2 * m + 1 = (k + 1) + 2 * m by ring, X.Z_add]
    have hterm : conjSub h (X.Z (k + 2 * m + 1)) =
        conjSub (X.τ ^ m) (conjSub ((X.τ ^ m)⁻¹ * h * (X.τ ^ m)) (X.Z (k + 1))) := by
      rw [hZ, ← conjSub_mul, ← conjSub_mul]
      congr 1
      group
    rw [hterm]
    exact le_iSup_of_le ((X.τ ^ m)⁻¹ * h * (X.τ ^ m)) (le_iSup_of_le hh' le_rfl)
  · refine iSup_le fun g => iSup_le fun hg => ?_
    have hg' : X.τ ^ m * g * (X.τ ^ m)⁻¹ ∈ X.L (k + 2 * m) := by
      rw [X.L_add]
      exact mem_conjSub.mpr (by convert hg using 1 <;> group)
    have hZ : X.Z (k + 2 * m + 1) = conjSub (X.τ ^ m) (X.Z (k + 1)) := by
      rw [show k + 2 * m + 1 = (k + 1) + 2 * m by ring, X.Z_add]
    have hterm : conjSub (X.τ ^ m) (conjSub g (X.Z (k + 1))) =
        conjSub (X.τ ^ m * g * (X.τ ^ m)⁻¹) (X.Z (k + 2 * m + 1)) := by
      rw [hZ, ← conjSub_mul, ← conjSub_mul]
      congr 1
      group
    rw [hterm]
    exact le_iSup₂_of_le _ hg' le_rfl

theorem Gi_le_normalizer_Vk (i : ℤ) : X.Gi i ≤ Subgroup.normalizer (X.Vk i : Set G) := by
  have hZi : X.Z (i + 1) = vertZ (X.vert (i + 1)) := X.Z_eq_vertZ (i + 1)
  have hstep : ∀ g ∈ X.Gi i, conjSub g (X.Vk i) ≤ X.Vk i := by
    intro g hg
    obtain ⟨l, hlL, hl⟩ : ∃ l ∈ X.L i, l • X.vert (i + 1) = g • X.vert (i + 1) := by
      obtain ⟨l, hlL, hl⟩ := (X.hyp.isLocL2_oTwoPrime (X.vert i)).trans (X.vert (i + 1))
        (g • X.vert (i + 1)) (X.adj i) (by
          have hgfix : g • X.vert i = X.vert i := MulAction.mem_stabilizer_iff.mp hg
          rw [← hgfix]
          exact (X.hyp.adj_smul g (X.vert i) (X.vert (i + 1))).mpr (X.adj i))
      exact ⟨l, hlL, hl⟩
    have hZg : conjSub g (X.Z (i + 1)) = conjSub l (X.Z (i + 1)) := by
      rw [hZi, ← vertZ_smul g (X.vert (i + 1)), ← hl, ← vertZ_smul l (X.vert (i + 1))]
    have hLnorm : X.Gi i ≤ Subgroup.normalizer (X.L i : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer (X.L_le_Gi i)).mp
        (X.hyp.isLocL2_oTwoPrime (X.vert i)).normal
    change conjSub g (⨆ (h : G), ⨆ (_ : h ∈ X.L i), conjSub h (X.Z (i + 1))) ≤ X.Vk i
    rw [conjSub_iSup]
    refine iSup_le fun h => ?_
    rw [conjSub_iSup]
    refine iSup_le fun hh => ?_
    have hhL : h ∈ X.L i := hh
    have hgh : g * h * g⁻¹ ∈ X.L i := by
      have := Subgroup.mem_normalizer_iff.mp (hLnorm hg) h
      exact this.mp hhL
    have e : conjSub g (conjSub h (X.Z (i + 1))) =
        conjSub ((g * h * g⁻¹) * l) (X.Z (i + 1)) := by
      conv_lhs => rw [← conjSub_mul, show g * h = (g * h * g⁻¹) * g by group,
        conjSub_mul, hZg]
      rw [← conjSub_mul]
    rw [e]
    exact le_iSup_of_le ((g * h * g⁻¹) * l)
      (le_iSup_of_le ((X.L i).mul_mem hgh hlL) le_rfl)
  intro g hg
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  refine le_antisymm (hstep g hg) ?_
  have hg' : g⁻¹ ∈ X.Gi i := (X.Gi i).inv_mem hg
  have h := conjSub_mono g (hstep g⁻¹ hg')
  rwa [conjSub_inv_conjSub] at h

theorem L_le_normalizer_Vk (k : ℤ) :
    X.L k ≤ Subgroup.normalizer (X.Vk k : Set G) :=
  (X.L_le_Gi k).trans (X.Gi_le_normalizer_Vk k)

variable {r d : ℕ}

variable {X}

theorem Z_one_le_Vk_zero : X.Z 1 ≤ X.Vk 0 := by
  intro y hy
  exact Subgroup.mem_iSup_of_mem (1 : G)
    (Subgroup.mem_iSup_of_mem (by simp) (by rw [conjSub_one]; exact hy))

theorem Z_neg_one_le_Vk_zero : X.Z (-1) ≤ X.Vk 0 := by
  obtain ⟨g, hgL, hg1⟩ := (X.hyp.isLocL2_oTwoPrime (X.vert 0)).trans
    (X.vert 1) (X.vert (-1)) (X.adj 0) (by
      have h := (X.adj (-1)).symm
      rwa [show -1 + 1 = 0 by norm_num] at h)
  have hZg : conjSub g (X.Z 1) = X.Z (-1) := (X.Z_smul X hg1).symm
  rw [← hZg]
  intro y hy
  exact Subgroup.mem_iSup_of_mem g (Subgroup.mem_iSup_of_mem hgL hy)

private abbrev Co (X : Setup Γ G) : Subgroup G :=
  X.Vk 0 ⊓ Subgroup.centralizer (oTwoRes (X.L 0) : Set G)

namespace Comm48

private theorem n_eq_n_zero_of_even {X : Setup Γ G} {b : ℤ} (hb : Even b) :
    X.n b = X.n 0 := by
  obtain ⟨m, hm⟩ := hb
  have h := X.n_add m 0
  rwa [show (0 : ℤ) + 2 * m = b by omega] at h

private theorem s48_Zb_card (C : X.Comm48 s r d) :
    Nat.card (X.Z ((d : ℤ) + 1)) = 2 ^ X.n 0 ∧ X.Z ((d : ℤ) + 1) ≠ ⊥ := by
  classical
  set b : ℤ := (d : ℤ) + 1 with hbdef
  have hn0 : 2 ≤ X.n 0 := C.hyp.two_le_n 0
  have hb0 : Even b := by
    obtain ⟨k, hk⟩ := C.even
    exact ⟨(k : ℤ), by rw [hbdef]; exact_mod_cast hk⟩
  obtain ⟨-, h2r, hZbQg, hZ0eq, hcardZ0, -, -, -⟩ := X.s48_2 C
  obtain ⟨m, hm⟩ := hb0
  have hbm : b = 2 * m := by omega
  have hZ0eqb : X.Z 0 = pCoreOf 2 (X.arcStab (-b) b) := by
    rw [hbdef]
    exact hZ0eq
  have harc : X.arcStab 0 (r : ℤ) = conjSub (X.τ ^ m) (X.arcStab (-b) b) := by
    have hbr : b + 2 * m = (r : ℤ) := by
      have hr' : (r : ℤ) = 2 * ((d : ℤ) + 1) := by
        exact_mod_cast h2r.symm
      rw [hbdef] at hbm ⊢
      omega
    have h := X.arcStab_add m (-b) b
    rw [show -b + 2 * m = 0 by omega, hbr] at h
    exact h
  have hZbArc : X.Z b = pCoreOf 2 (X.arcStab 0 (r : ℤ)) := by
    rw [hbdef, hZbQg]
  have hZb_conj : X.Z b = conjSub (X.τ ^ m) (X.Z 0) := by
    rw [hZbArc, hZ0eqb, harc, pCoreOf_conjSub]
  have hcardZb : Nat.card (X.Z b) = 2 ^ X.n 0 := by
    rw [hZb_conj, card_conjSub, hcardZ0]
  have hZb_ne : X.Z b ≠ ⊥ := by
    intro hbot
    rw [hbot] at hcardZb
    simp only [Subgroup.card_bot] at hcardZb
    have h2 : 2 ^ 2 ≤ 2 ^ X.n 0 := Nat.pow_le_pow_right (by norm_num) hn0
    omega
  exact ⟨by simpa [hbdef] using hcardZb, by simpa [hbdef] using hZb_ne⟩

private theorem s48_pCoreOf_arcStab_zero_ne_bot (C : X.Comm48 s r d) :
    pCoreOf 2 (X.arcStab 0 (r : ℤ)) ≠ ⊥ := by
  obtain ⟨hcardZb, -⟩ := s48_Zb_card (X := X) C
  obtain ⟨-, -, hZbQg, -, -, -, -, -⟩ := X.s48_2 C
  intro hbot
  have h := hcardZb
  rw [hZbQg, Setup.Qg] at h
  rw [hbot] at h
  simp only [Subgroup.card_bot] at h
  have h2 : 2 ^ 2 ≤ 2 ^ X.n 0 := Nat.pow_le_pow_right (by norm_num) (C.hyp.two_le_n 0)
  omega

private theorem s48_Zb_inf_edge (C : X.Comm48 s r d) :
    X.Z ((d : ℤ) + 1) ⊓ X.Q 0 = ⊥ ∧ X.Z ((d : ℤ) + 1) ≤ X.edgeSylow 0 := by
  set b : ℤ := (d : ℤ) + 1 with hbdef
  obtain ⟨-, -, hZbQg, -, -, -, -, -⟩ := X.s48_2 C
  have hneQg := s48_pCoreOf_arcStab_zero_ne_bot (X := X) C
  obtain ⟨-, hArcQ0, -, -, -⟩ := X.pCoreOf_arcStab_r C.hyp 0 (by simpa using hneQg)
  have hZb_inf_Q0 : X.Z b ⊓ X.Q 0 = ⊥ := by
    rw [hbdef, hZbQg, Setup.Qg]
    simpa using hArcQ0
  have hrpos : (0 : ℤ) < (r : ℤ) := by
    have := C.hyp.five_le
    have := C.hyp.le_r
    omega
  have hKA : X.K ≤ X.arcStab 0 (r : ℤ) :=
    X.K_le_GT.trans (X.GT_le_arcStab 0 (r : ℤ))
  have hA_edge : X.arcStab 0 (r : ℤ) ≤ X.Gi 0 ⊓ X.Gi 1 :=
    le_inf (X.arcStab_le_Gi_left hrpos) (X.arcStab_le_Gi_left_succ hrpos)
  have hZb_le_edge : X.Z b ≤ X.edgeSylow 0 := by
    have h := (X.pCoreOf_eq_inf_edgeSylow 0 hKA hA_edge).1
    rw [hZbQg, Setup.Qg, h]
    exact inf_le_right
  exact ⟨by simpa [hbdef] using hZb_inf_Q0, by simpa [hbdef] using hZb_le_edge⟩

end Comm48

variable (X) in
open Comm48 in
theorem Z_succ_sup_Q_zero_and_inf (C : X.Comm48 s r d) :
    X.Z ((d : ℤ) + 1) ⊔ X.Q 0 = X.edgeSylow 0 ∧
      X.Z ((d : ℤ) + 1) ⊓ X.Q 0 = ⊥ := by
  set b : ℤ := (d : ℤ) + 1 with hbdef
  obtain ⟨-, hZb_ne⟩ := s48_Zb_card (X := X) C
  obtain ⟨hZb_inf_Q0, hZb_le_edge⟩ := s48_Zb_inf_edge (X := X) C
  have hZb_ne' : X.Z b ≠ ⊥ := by simpa [hbdef] using hZb_ne
  have hZb_inf' : X.Z b ⊓ X.Q 0 = ⊥ := by simpa [hbdef] using hZb_inf_Q0
  have hZb_le_edge' : X.Z b ≤ X.edgeSylow 0 := by simpa [hbdef] using hZb_le_edge
  have hKnormZb : X.K ≤ Subgroup.normalizer (X.Z b : Set G) := fun k hk =>
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr (X.Z_normal b k (X.K_le_Gi b hk))
  have hZb_not_Q0 : ¬ X.Z b ≤ X.Q 0 := by
    intro hle
    have hbot : X.Z b ≤ (⊥ : Subgroup G) := by
      rw [← hZb_inf']
      exact le_inf le_rfl hle
    exact hZb_ne' (le_bot_iff.mp hbot)
  have hZb_sup_Q0 : X.Z b ⊔ X.Q 0 = X.edgeSylow 0 :=
    X.sup_Q_eq_edgeSylow_of_left_gen 0 (A := X.Z b)
      (inf_le_left.trans hKnormZb) hZb_le_edge' hZb_not_Q0
  exact ⟨by simpa [hbdef] using hZb_sup_Q0, by simpa [hbdef] using hZb_inf_Q0⟩

namespace Comm48

private theorem Ki_inf_Ki_zero_eq_bot_of_fixes {b : ℤ}
    (hfixKb : ∀ w, Γ.Adj (X.vert 0) w → ∀ x ∈ X.Ki b, x • w = w) :
    X.Ki b ⊓ X.Ki 0 = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  have hvKb : v ∈ X.Ki b := (Subgroup.mem_inf.mp hv).1
  have hvK0 : v ∈ X.Ki 0 := (Subgroup.mem_inf.mp hv).2
  have hvL0 : v ∈ X.L 0 := hvK0.2
  have hfixv : ∀ w, Γ.Adj (X.vert 0) w → v • w = w :=
    fun w hw => hfixKb w hw v hvKb
  have hN := X.hyp.isLocL2_oTwoPrime (X.vert 0)
  have hvQ0 : v ∈ X.Q 0 :=
    hN.N_fixes_neighbors_mem_Q X.hyp.adj_smul (X.hyp.finite_stab (X.vert 0))
      (X.hyp.valency (X.vert 0)).2 (X.hyp.valency (X.vert 0)).1 (x := ⟨v, hvL0⟩) hfixv
  have hvK : v ∈ X.K := hvK0.1
  have hmem : v ∈ X.K ⊓ X.edgeSylow 0 :=
    ⟨hvK, X.Q_le_edgeSylow_left 0 hvQ0⟩
  rw [X.K_inf_edgeSylow 0] at hmem
  exact hmem

private theorem card_K_lower {b : ℤ} (hb : Even b)
    (hfirst : X.Ki b ⊓ X.Ki 0 = ⊥) :
    (2 ^ X.n 0 - 1) ^ 2 ≤ Nat.card X.K := by
  have hcardKb : Nat.card (X.Ki b) = 2 ^ X.n 0 - 1 := by
    rw [X.card_Ki b, n_eq_n_zero_of_even (X := X) hb]
  have hcardK0 : Nat.card (X.Ki 0) = 2 ^ X.n 0 - 1 := X.card_Ki 0
  haveI : Finite ↥X.K := finite_of_le_stabilizer X.hyp (H := X.K) (X.K_le_Gi 0)
  have hlower : (2 ^ X.n 0 - 1) * (2 ^ X.n 0 - 1) ≤ Nat.card X.K := by
    have h := CFSG.card_mul_card_le_of_inf_eq_bot (G := G) (A := X.K)
      (D := X.Ki b) (D' := X.Ki 0) inf_le_left inf_le_left hfirst
    rwa [hcardKb, hcardK0] at h
  simpa [pow_two] using hlower

private theorem card_quot_Ki0_le :
    Nat.card ((↥X.K) ⧸ (X.Ki 0).subgroupOf X.K) ≤ 2 ^ X.n 1 - 1 := by
  haveI : Finite ↥X.K := finite_of_le_stabilizer X.hyp (H := X.K) (X.K_le_Gi 0)
  haveI : Finite ↥(X.Ki 1) :=
    finite_of_le_stabilizer X.hyp (H := X.Ki 1) (inf_le_left.trans (X.K_le_Gi 1))
  have hKiNormalK : ∀ i : ℤ, X.K ≤ Subgroup.normalizer (X.Ki i : Set G) := by
    intro i k hk
    rw [mem_normalizer_iff_conjSub]
    have hLinorm : X.Gi i ≤ Subgroup.normalizer (X.L i : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer (X.L_le_Gi i)).mp
        (X.hyp.isLocL2_oTwoPrime (X.vert i)).normal
    have hconjL : conjSub k (X.L i) = X.L i := by
      rw [show conjSub k (X.L i) = Subgroup.map (MulAut.conj k) (X.L i) from rfl]
      exact Subgroup.mem_normalizer_iff_map_conj_eq.mp (hLinorm (X.K_le_Gi i hk))
    rw [conjSub_inf, conjSub_eq_of_mem (H := X.K) hk, hconjL]
  have hK0normal : ((X.Ki 0).subgroupOf X.K).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (hKiNormalK 0)
  let φ : ↥(X.Ki 1) → (↥X.K) ⧸ (X.Ki 0).subgroupOf X.K := fun x =>
    QuotientGroup.mk' ((X.Ki 0).subgroupOf X.K) ⟨x.1, (Subgroup.mem_inf.mp x.2).1⟩
  have hφsurj : Function.Surjective φ := by
    intro q
    refine Quotient.inductionOn q ?_
    intro k
    have hk : (k : G) ∈ X.Ki 0 ⊔ X.Ki 1 := by
      rw [← X.K_eq_sup]
      exact k.2
    have hcoe : ((X.Ki 0 ⊔ X.Ki 1 : Subgroup G) : Set G) =
        (X.Ki 0 : Set G) * (X.Ki 1 : Set G) :=
      Subgroup.coe_mul_of_right_le_normalizer_left (X.Ki 0) (X.Ki 1)
        (by intro x hx; exact hKiNormalK 0 (Subgroup.mem_inf.mp hx).1)
    have hk' : (k : G) ∈ (X.Ki 0 : Set G) * (X.Ki 1 : Set G) := by
      rw [← hcoe]
      exact hk
    obtain ⟨a, ha, q', hq', haq'⟩ := Set.mem_mul.mp hk'
    refine ⟨⟨q', hq'⟩, ?_⟩
    have hk_eq : k =
        (⟨a, (Subgroup.mem_inf.mp ha).1⟩ : ↥X.K) * ⟨q', (Subgroup.mem_inf.mp hq').1⟩ := by
      ext
      exact haq'.symm
    change QuotientGroup.mk' ((X.Ki 0).subgroupOf X.K) ⟨q', (Subgroup.mem_inf.mp hq').1⟩ =
      QuotientGroup.mk' ((X.Ki 0).subgroupOf X.K) k
    rw [hk_eq, map_mul]
    have ha1 : QuotientGroup.mk' ((X.Ki 0).subgroupOf X.K)
        (⟨a, (Subgroup.mem_inf.mp ha).1⟩ : ↥X.K) = 1 := by
      rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']
      exact ha
    rw [ha1, one_mul]
  have h := Nat.card_le_card_of_surjective φ hφsurj
  rwa [X.card_Ki 1] at h

private theorem card_K_upper :
    Nat.card X.K ≤ (2 ^ X.n 0 - 1) * (2 ^ X.n 1 - 1) := by
  have hcardK0 : Nat.card (X.Ki 0) = 2 ^ X.n 0 - 1 := X.card_Ki 0
  haveI : Finite ↥X.K := finite_of_le_stabilizer X.hyp (H := X.K) (X.K_le_Gi 0)
  haveI : Finite ↥(X.Ki 0) :=
    finite_of_le_stabilizer X.hyp (H := X.Ki 0) (inf_le_left.trans (X.K_le_Gi 0))
  have hcardK := Subgroup.card_eq_card_quotient_mul_card_subgroup
    ((X.Ki 0).subgroupOf X.K)
  have hsubcard : Nat.card ((X.Ki 0).subgroupOf X.K) = 2 ^ X.n 0 - 1 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (show X.Ki 0 ≤ X.K from inf_le_left)).toEquiv).trans hcardK0
  calc Nat.card X.K = Nat.card ((↥X.K) ⧸ (X.Ki 0).subgroupOf X.K) *
        Nat.card ((X.Ki 0).subgroupOf X.K) := hcardK
    _ = Nat.card ((↥X.K) ⧸ (X.Ki 0).subgroupOf X.K) * (2 ^ X.n 0 - 1) := by
        rw [hsubcard]
    _ ≤ (2 ^ X.n 1 - 1) * (2 ^ X.n 0 - 1) := Nat.mul_le_mul_right _ card_quot_Ki0_le
    _ = (2 ^ X.n 0 - 1) * (2 ^ X.n 1 - 1) := by rw [Nat.mul_comm]

private theorem card_K_bounds {b : ℤ} (hb : Even b)
    (hfirst : X.Ki b ⊓ X.Ki 0 = ⊥) :
    (2 ^ X.n 0 - 1) ^ 2 ≤ Nat.card X.K ∧
      Nat.card X.K ≤ (2 ^ X.n 0 - 1) * (2 ^ X.n 1 - 1) :=
  ⟨card_K_lower (X := X) hb hfirst, card_K_upper (X := X)⟩

private theorem n_zero_le_n_one_of_inf_eq_bot (C : X.Comm48 s r d) {b : ℤ} (hb : Even b)
    (hfirst : X.Ki b ⊓ X.Ki 0 = ⊥) : X.n 0 ≤ X.n 1 := by
  obtain ⟨hlow, hup⟩ := card_K_bounds (X := X) hb hfirst
  have hq : 0 < 2 ^ X.n 0 - 1 := by
    have h2 : 4 ≤ 2 ^ X.n 0 := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ X.n 0 := Nat.pow_le_pow_right (by norm_num) (C.hyp.two_le_n 0)
    omega
  have hle : (2 ^ X.n 0 - 1) * (2 ^ X.n 0 - 1) ≤
      (2 ^ X.n 0 - 1) * (2 ^ X.n 1 - 1) := by simpa [pow_two] using hlow.trans hup
  have hle' : 2 ^ X.n 0 - 1 ≤ 2 ^ X.n 1 - 1 :=
    Nat.le_of_mul_le_mul_left hle hq
  have hle'' : 2 ^ X.n 0 ≤ 2 ^ X.n 1 := by omega
  exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hle''

end Comm48

variable (X) in
open Comm48 in
theorem s48_6 (C : X.Comm48 s r d) :
    X.Ki ((d : ℤ) + 1) ⊓ X.Ki 0 = ⊥ ∧ X.n 0 ≤ X.n 1 ∧
      (∀ w, Γ.Adj (X.vert 0) w → ∀ x ∈ X.Ki ((d : ℤ) + 1), x • w = w) := by
  set b : ℤ := (d : ℤ) + 1 with hbdef
  have hc : CharTwoStab (V := V) (G := G) := C.hyp.char
  have hZb_sup_Q0 : X.Z b ⊔ X.Q 0 = X.edgeSylow 0 := by
    rw [hbdef]
    exact (X.Z_succ_sup_Q_zero_and_inf C).1
  have hcenter : X.Z b = centerOf (X.L b) := by
    rw [hbdef]
    exact (X.s48_0 C).1
  have hKbZb : X.Z b ≤ Subgroup.centralizer (X.Ki b : Set G) := by
    rw [hcenter]
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have hzu : z ∈ Subgroup.centralizer (X.L b : Set G) := (Subgroup.mem_inf.mp hz).2
    exact (Subgroup.mem_centralizer_iff.mp hzu) u (Subgroup.mem_inf.mp hu).2
  have hfixKb : ∀ w, Γ.Adj (X.vert 0) w → ∀ x ∈ X.Ki b, x • w = w :=
    (X.fix_nbrs_of_centralizes hc 0 (U := X.Ki b) (P := X.Z b) inf_le_left
      ((pCoreOf_isPGroup' (X.Gi b)).to_le (X.Z_le_Q b))
      (Or.inl hZb_sup_Q0) hKbZb).1
  have hfirst : X.Ki b ⊓ X.Ki 0 = ⊥ := Ki_inf_Ki_zero_eq_bot_of_fixes hfixKb
  have hb : Even b := by
    obtain ⟨k, hk⟩ := C.even
    exact ⟨(k : ℤ), by rw [hbdef]; exact_mod_cast hk⟩
  exact ⟨hfirst, n_zero_le_n_one_of_inf_eq_bot C hb hfirst, hfixKb⟩

namespace Comm48

theorem card_Z_one_gt (C : X.Comm48 s r d) : 2 ^ X.n 0 < Nat.card (X.Z 1) := by
  haveI : Finite ↥(X.Z 0) := finite_of_le_stabilizer X.hyp (H := X.Z 0) (X.Z_le_Gi 0)
  haveI : Finite ↥(X.Z 1) := finite_of_le_stabilizer X.hyp (H := X.Z 1) (X.Z_le_Gi 1)
  obtain ⟨hZ0leZ1, hoddCenter⟩ := X.s48_1 C
  have hcardZ0 : Nat.card (X.Z 0) = 2 ^ X.n 0 := (X.s48_2 C).2.2.2.2.1
  have hZ0L0 : X.Z 0 ≤ X.L 0 := by
    rw [(X.s48_0 C).2]
    exact inf_le_left
  have hcenterNorm0 : X.L 0 ≤ Subgroup.normalizer (X.Z 0 : Set G) := fun l hl =>
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr (X.Z_normal 0 l (X.L_le_Gi 0 hl))
  have hZ0neZ1 : X.Z 0 ≠ X.Z 1 := by
    intro heq
    have hZ1L0 : X.Z 1 ≤ X.L 0 := by rw [← heq]; exact hZ0L0
    have hnα : ((X.Z 1).subgroupOf (X.L 0)).Normal := by
      rw [← heq]
      exact Subgroup.normal_subgroupOf_of_le_normalizer hcenterNorm0
    have hZ1L1 : X.Z 1 ≤ X.L 1 :=
      (X.Z_le_Q 1).trans (X.Q_le_L 1)
    have hnβ : ((X.Z 1).subgroupOf (X.L 1)).Normal :=
      Subgroup.normal_subgroupOf_of_le_normalizer fun l hl =>
        Subgroup.mem_normalizer_iff_map_conj_eq.mpr (X.Z_normal 1 l (X.L_le_Gi 1 hl))
    have hbot := eq_bot_of_normal_in_oTwoPrime X.hyp (X.adj 0) (X := X.Z 1)
      hZ1L0 hnα hZ1L1 hnβ
    have hcard1 : Nat.card (X.Z 1) = 1 := by rw [hbot]; simp
    have hlecard : Nat.card (X.Z 0) ≤ Nat.card (X.Z 1) := Subgroup.card_le_of_le hZ0leZ1
    have h2 : 1 < 2 ^ X.n 0 := by
      have h4 : 4 ≤ 2 ^ X.n 0 := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ X.n 0 := Nat.pow_le_pow_right (by norm_num) (C.hyp.two_le_n 0)
      omega
    omega
  have hlt : X.Z 0 < X.Z 1 := lt_of_le_of_ne hZ0leZ1 hZ0neZ1
  have hcardlt := Subgroup.card_lt_of_lt hlt
  rwa [← hcardZ0]

private theorem s48_H_relIndex (C : X.Comm48 s r d) :
    (X.Z 1 ⊓ X.Q ((d : ℤ) + 1)).relIndex (X.Z 1) ≤ 2 ^ X.n 0 := by
  have hd1 : X.HasB 1 d := C.hasB
  have hZ1Qpred : X.Z 1 ≤ X.Q (d : ℤ) := by
    have hdpos : 1 ≤ d := X.one_le_of_hasB hd1
    have h := X.Z_le_Q_of_lt hd1 (i := 1) (j := (d : ℤ)) (by
      have hz : ((d : ℤ) - 1) = ((d - 1 : ℕ) : ℤ) := by omega
      rw [hz, Int.natAbs_natCast]
      omega)
    simpa using h
  have hZ1leEdge : X.Z 1 ≤ X.edgeSylow (d : ℤ) :=
    hZ1Qpred.trans (X.Q_le_edgeSylow_left (d : ℤ))
  have hrelEdge : (X.Q ((d : ℤ) + 1)).relIndex (X.edgeSylow (d : ℤ)) = 2 ^ X.n 0 := by
    have h := X.relIndex_Q_succ_edgeSylow (d : ℤ)
    have hb : Even ((d : ℤ) + 1) := by
      obtain ⟨k, hk⟩ := C.even
      exact ⟨(k : ℤ), by exact_mod_cast hk⟩
    rw [n_eq_n_zero_of_even (X := X) hb] at h
    simpa using h
  have hEq : (X.Z 1 ⊓ X.Q ((d : ℤ) + 1)).relIndex (X.Z 1) =
      (X.Q ((d : ℤ) + 1)).relIndex (X.Z 1) := by
    simpa [inf_comm] using Subgroup.inf_relIndex_right (H := X.Q ((d : ℤ) + 1)) (K := X.Z 1)
  rw [hEq]
  calc (X.Q ((d : ℤ) + 1)).relIndex (X.Z 1)
      ≤ (X.Q ((d : ℤ) + 1)).relIndex (X.edgeSylow (d : ℤ)) :=
        Subgroup.relIndex_le_of_le_right hZ1leEdge (by rw [hrelEdge]; simp)
    _ = 2 ^ X.n 0 := hrelEdge

private theorem s48_H_ne (C : X.Comm48 s r d) : X.ZQ d ≠ ⊥ := by
  intro hbot
  have hrel : (X.ZQ d).relIndex (X.Z 1) ≤ 2 ^ X.n 0 := s48_H_relIndex (X := X) C
  rw [hbot, Subgroup.relIndex_bot_left] at hrel
  have hgt := card_Z_one_gt (X := X) C
  omega

private theorem s48_H_arc (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) :
    X.ZQ d ≤ X.arcStab (1 - (d : ℤ)) ((d : ℤ) + 3) := by
  have hd1 : X.HasB 1 d := C.hasB
  have hHdef : X.ZQ d = X.Z 1 ⊓ X.Q ((d : ℤ) + 1) := rfl
  have hHleQ : X.ZQ d ≤ X.Q ((d : ℤ) + 2) := hH
  refine X.le_arcStab_of_fixSet ?_
  intro j hj
  rw [Set.mem_Icc] at hj
  intro z hz
  have hz1 : z ∈ X.Z 1 := (Subgroup.mem_inf.mp (by rwa [hHdef] at hz)).1
  have hzQ : z ∈ X.Q ((d : ℤ) + 2) := hHleQ hz
  by_cases hjb : j ≤ (d : ℤ) + 1
  · have hfixZ1 : j ∈ X.fixSet (X.Z 1) := by
      rw [X.fixSet_Z 1 hd1]
      rw [Set.mem_Icc]
      omega
    exact hfixZ1 z hz1
  · have hjb' : j = (d : ℤ) + 2 ∨ j = (d : ℤ) + 3 := by omega
    rcases hjb' with rfl | rfl
    · exact MulAction.mem_stabilizer_iff.mp (X.Q_le_Gi ((d : ℤ) + 2) hzQ)
    · exact MulAction.mem_stabilizer_iff.mp
        (Subgroup.mem_inf.mp (X.Q_le_Gi_adj ((d : ℤ) + 2) hzQ)).2

private theorem s48_H_pCore_eq (C : X.Comm48 s r d) :
    pCoreOf 2 (X.arcStab (1 - (d : ℤ)) ((d : ℤ) + 3)) = X.Z 2 := by
  obtain ⟨-, -, -, hZ0eq, -, -, -, -⟩ := X.s48_2 C
  have harc : X.arcStab (1 - (d : ℤ)) ((d : ℤ) + 3) =
      conjSub X.τ (X.arcStab (-((d : ℤ) + 1)) ((d : ℤ) + 1)) := by
    have h := X.arcStab_add 1 (-((d : ℤ) + 1)) ((d : ℤ) + 1)
    rw [show X.τ ^ (1 : ℤ) = X.τ by simp] at h
    convert h using 1 <;> ring_nf
  rw [harc, pCoreOf_conjSub, ← hZ0eq]
  have hZ2 : X.Z 2 = conjSub X.τ (X.Z 0) := by
    simpa using (X.Z_add 1 0)
  exact hZ2.symm

private theorem s48_H_Kinv (C : X.Comm48 s r d) :
    X.K ≤ Subgroup.normalizer (X.ZQ d : Set G) := by
  have hHdef : X.ZQ d = X.Z 1 ⊓ X.Q ((d : ℤ) + 1) := rfl
  intro k hk
  rw [mem_normalizer_iff_conjSub]
  rw [hHdef, conjSub_inf, X.Z_normal 1 k (X.K_le_Gi 1 hk)]
  have hQn : k ∈ Subgroup.normalizer (X.Q ((d : ℤ) + 1) : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi ((d : ℤ) + 1))
      (X.K_le_Gi ((d : ℤ) + 1) hk)
  exact congrArg (fun H => X.Z 1 ⊓ H)
    (Subgroup.mem_normalizer_iff_map_conj_eq.mp hQn)

private theorem s48_H_eq (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) : X.ZQ d = X.Z 2 := by
  have hHdef : X.ZQ d = X.Z 1 ⊓ X.Q ((d : ℤ) + 1) := rfl
  have hH2 : IsPGroup 2 (X.ZQ d) :=
    (pCoreOf_isPGroup' (X.Gi 1)).to_le ((hHdef ▸ inf_le_left).trans (X.Z_le_Q 1))
  have hKinv : X.K ≤ Subgroup.normalizer (X.ZQ d : Set G) := s48_H_Kinv (X := X) C
  have hHarc := s48_H_arc (X := X) C hH
  have hHpc : X.ZQ d ≤ pCoreOf 2 (X.arcStab (1 - (d : ℤ)) ((1 - (d : ℤ)) + (r : ℤ))) := by
    apply X.le_pCoreOf_arcStab_r C.hyp hH2
    rw [show (1 - (d : ℤ)) + (r : ℤ) = (d : ℤ) + 3 by
      have := (X.s48_2 C).2.1
      have : (r : ℤ) = 2 * ((d : ℤ) + 1) := by exact_mod_cast this.symm
      omega]
    exact hHarc
  have h := X.eq_of_le_pCoreOf_arcStab_r C.hyp hKinv (s48_H_ne (X := X) C) hHpc
  rw [show (1 - (d : ℤ)) + (r : ℤ) = (d : ℤ) + 3 by
    have := (X.s48_2 C).2.1
    have : (r : ℤ) = 2 * ((d : ℤ) + 1) := by exact_mod_cast this.symm
    omega,
    s48_H_pCore_eq (X := X) C] at h
  exact h

private theorem s48_Z0Z2_bot (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) : X.Z 0 ⊓ X.Z 2 = ⊥ := by
  classical
  obtain ⟨-, h2r, -, hZ0eq, -, -, -, -⟩ := X.s48_2 C
  have hH_eq : X.ZQ d = X.Z 2 := s48_H_eq (X := X) C hH
  have hHarc : X.ZQ d ≤ X.arcStab (1 - (d : ℤ)) ((d : ℤ) + 3) := s48_H_arc (X := X) C hH
  have hZ2arc : X.Z 2 ≤ X.arcStab (1 - (d : ℤ)) ((d : ℤ) + 3) := by
    rw [← hH_eq]; exact hHarc
  have hZ0arc : X.Z 0 ≤ X.arcStab (-((d : ℤ) + 1)) ((d : ℤ) + 1) := by
    rw [hZ0eq]; exact CFSG.LieType.BorelTits.pCoreOf_le 2 _
  have hr : (r : ℤ) = 2 * ((d : ℤ) + 1) := by
    have h := h2r
    exact_mod_cast h.symm
  by_contra hne
  have hU2 : IsPGroup 2 (X.Z 0 ⊓ X.Z 2 : Subgroup G) :=
    (pCoreOf_isPGroup' (G := G) (X.Gi 0)).to_le (inf_le_left.trans (X.Z_le_Q 0))
  have hUarc : X.Z 0 ⊓ X.Z 2 ≤ X.arcStab (-((d : ℤ) + 1)) ((d : ℤ) + 3) := by
    refine X.le_arcStab_of_fixSet ?_
    intro j hj
    rw [Set.mem_Icc] at hj
    intro u hu
    have hu0 : u ∈ X.Z 0 := (Subgroup.mem_inf.mp hu).1
    have hu2 : u ∈ X.Z 2 := (Subgroup.mem_inf.mp hu).2
    by_cases hjb : j ≤ (d : ℤ) + 1
    · have hu' : u ∈ Fan86.fixSet G
          (X.vert '' Set.Icc (-((d : ℤ) + 1)) ((d : ℤ) + 1)) := by
        simpa [Setup.arcStab] using hZ0arc hu0
      exact (Fan86.mem_fixSet.mp hu') (X.vert j)
        ⟨j, by rw [Set.mem_Icc]; omega, rfl⟩
    · have hu' : u ∈ Fan86.fixSet G
          (X.vert '' Set.Icc (1 - (d : ℤ)) ((d : ℤ) + 3)) := by
        simpa [Setup.arcStab] using hZ2arc hu2
      exact (Fan86.mem_fixSet.mp hu') (X.vert j)
        ⟨j, by rw [Set.mem_Icc]; omega, rfl⟩
  have hlong : X.Z 0 ⊓ X.Z 2 ≤
      X.arcStab (-((d : ℤ) + 1)) ((-((d : ℤ) + 1)) + ((2 * d + 4 : ℕ) : ℤ)) := by
    convert hUarc using 2
    push_cast
    ring
  have hle := X.le_r_of_fixes C.hyp hU2 hne hlong
  omega

private theorem s48_Z2_card (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) :
    Nat.card (X.Z 2) = 2 ^ X.n 0 ∧ X.Z 2 ≤ X.L 0 := by
  have hdpos : 1 ≤ d := X.one_le_of_hasB C.hasB
  haveI : Finite ↥(X.Z 2) := finite_of_le_stabilizer X.hyp (H := X.Z 2) (X.Z_le_Gi 2)
  obtain ⟨-, h2r, -, -, -, -, -, -⟩ := X.s48_2 C
  have hH_eq : X.ZQ d = X.Z 2 := s48_H_eq (X := X) C hH
  have hHne : X.ZQ d ≠ ⊥ := s48_H_ne (X := X) C
  have hZ2ne : X.Z 2 ≠ ⊥ := by rw [← hH_eq]; exact hHne
  have hnePc : pCoreOf 2 (X.arcStab (1 - (d : ℤ)) ((1 - (d : ℤ)) + (r : ℤ))) ≠ ⊥ := by
    rw [show (1 - (d : ℤ)) + (r : ℤ) = (d : ℤ) + 3 by omega,
      s48_H_pCore_eq (X := X) C]
    exact hZ2ne
  have hcardZ2 : Nat.card (X.Z 2) = 2 ^ X.n 0 := by
    have h := (X.pCoreOf_arcStab_r C.hyp (1 - (d : ℤ)) hnePc).1
    rw [show (1 - (d : ℤ)) + (r : ℤ) = (d : ℤ) + 3 by omega,
      s48_H_pCore_eq (X := X) C] at h
    have hb : Even ((1 : ℤ) - d) := by
      obtain ⟨k, hk⟩ := C.even
      have hk' : ((d : ℤ) + 1) = (k : ℤ) + (k : ℤ) := by exact_mod_cast hk
      exact ⟨1 - (k : ℤ), by omega⟩
    rw [n_eq_n_zero_of_even (X := X) hb] at h
    exact h
  have hZ2arc : X.Z 2 ≤ X.arcStab (1 - (d : ℤ)) ((d : ℤ) + 3) := by
    rw [← hH_eq]; exact s48_H_arc (X := X) C hH
  have hZ2leL0 : X.Z 2 ≤ X.L 0 := by
    have hleft : X.Z 2 ≤ X.Gi (1 - (d : ℤ)) :=
      hZ2arc.trans (X.arcStab_le_Gi_left (m := 1 - (d : ℤ)) (r := (d : ℤ) + 3) (by omega))
    have hright : X.Z 2 ≤ X.Gi ((d : ℤ) + 3) :=
      hZ2arc.trans (X.arcStab_le_Gi_right (m := 1 - (d : ℤ)) (r := (d : ℤ) + 3) (by omega))
    have hleGi : X.Z 2 ≤ X.Gi 0 := by
      intro z hz
      exact X.mem_Gi_of_between (hleft hz) (hright hz) (by omega) (by omega)
    have hZ2p : IsPGroup 2 (X.Z 2 : Subgroup G) :=
      (pCoreOf_isPGroup' (G := G) (X.Gi 2)).to_le (X.Z_le_Q 2)
    exact le_oTwoPrime_of_isPGroup hZ2p hleGi
  exact ⟨hcardZ2, hZ2leL0⟩

private theorem s48_Z1_sup_card (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) :
    X.Z 1 = X.Z 0 ⊔ X.Z 2 ∧ X.Z 0 ⊓ X.Z 2 = ⊥ ∧
      Nat.card (X.Z 1) = 2 ^ (2 * X.n 0) := by
  haveI : Finite ↥(X.Z 1) := finite_of_le_stabilizer X.hyp (H := X.Z 1) (X.Z_le_Gi 1)
  haveI : Finite ↥(X.Z 2) := finite_of_le_stabilizer X.hyp (H := X.Z 2) (X.Z_le_Gi 2)
  obtain ⟨-, -, -, -, hcardZ0, -, -, -⟩ := X.s48_2 C
  obtain ⟨hZ0leZ1, -⟩ := X.s48_1 C
  have hH_eq : X.ZQ d = X.Z 2 := s48_H_eq (X := X) C hH
  have hZ2leZ1 : X.Z 2 ≤ X.Z 1 := by
    rw [← hH_eq]; exact inf_le_left
  obtain ⟨hcardZ2, hZ2leL0⟩ := s48_Z2_card (X := X) C hH
  have hcardZ1le : Nat.card (X.Z 1) ≤ 2 ^ X.n 0 * 2 ^ X.n 0 := by
    have hHrel2 : (X.Z 2).relIndex (X.Z 1) ≤ 2 ^ X.n 0 := by
      rw [← hH_eq]; exact s48_H_relIndex (X := X) C
    have h := Subgroup.relIndex_mul_card (H := X.Z 2) (K := X.Z 1)
    rw [inf_eq_left.mpr hZ2leZ1] at h
    rw [← h, hcardZ2]
    exact Nat.mul_le_mul_right (2 ^ X.n 0) hHrel2
  have hZ2centZ0 : X.Z 2 ≤ Subgroup.normalizer (X.Z 0 : Set G) := fun z hz =>
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr
      (X.Z_normal 0 z (X.L_le_Gi 0 (hZ2leL0 hz)))
  have hZ0Z2bot : X.Z 0 ⊓ X.Z 2 = ⊥ := s48_Z0Z2_bot (X := X) C hH
  have hprod : Nat.card (X.Z 0 ⊔ X.Z 2 : Subgroup G) = 2 ^ (2 * X.n 0) := by
    rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
      (A := X.Z 0) (B := X.Z 2) hZ2centZ0 (disjoint_iff.mpr hZ0Z2bot), hcardZ0, hcardZ2,
      ← pow_add]
    congr 1
    omega
  have hsup : X.Z 1 = X.Z 0 ⊔ X.Z 2 := by
    have hle : X.Z 0 ⊔ X.Z 2 ≤ X.Z 1 := sup_le hZ0leZ1 hZ2leZ1
    have hcardge : Nat.card (X.Z 1) ≤ Nat.card (X.Z 0 ⊔ X.Z 2 : Subgroup G) := by
      rw [hprod]
      calc Nat.card (X.Z 1) ≤ 2 ^ X.n 0 * 2 ^ X.n 0 := hcardZ1le
        _ = 2 ^ (2 * X.n 0) := by rw [← pow_add]; congr 1; omega
    exact (Subgroup.eq_of_le_of_card_ge hle hcardge).symm
  exact ⟨hsup, hZ0Z2bot, by rw [hsup, hprod]⟩

private theorem s48_Z1_elem (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) : IsElemAbelian 2 (X.Z 1) := by
  obtain ⟨-, h2r, -, -, -, helemZ0, -, -⟩ := X.s48_2 C
  obtain ⟨hsup, -, -⟩ := s48_Z1_sup_card (X := X) C hH
  obtain ⟨-, hZ2leL0⟩ := s48_Z2_card (X := X) C hH
  have hcomm : ∀ a ∈ X.Z 0, ∀ c ∈ X.Z 2, a * c = c * a := by
    intro a ha c hc
    have hac : a ∈ Subgroup.centralizer (X.L 0 : Set G) := by
      rw [(X.s48_0 C).2] at ha
      exact (Subgroup.mem_inf.mp ha).2
    exact ((Subgroup.mem_centralizer_iff.mp hac) c (hZ2leL0 hc)).symm
  have helemZ2 : IsElemAbelian 2 (X.Z 2) := by
    have h := X.isElemAbelian_pCoreOf_arcStab_r C.hyp (1 - (d : ℤ))
    rwa [show (1 - (d : ℤ)) + (r : ℤ) = (d : ℤ) + 3 by omega,
      s48_H_pCore_eq (X := X) C] at h
  rw [hsup]
  exact CFSG.Open.IsElemAbelian.sup_of_commute helemZ0 helemZ2 hcomm

private theorem s48_Z1_struct (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) :
    X.Z 1 = X.Z 0 ⊔ X.Z 2 ∧ X.Z 0 ⊓ X.Z 2 = ⊥ ∧
      Nat.card (X.Z 1) = 2 ^ (2 * X.n 0) ∧ IsElemAbelian 2 (X.Z 1) := by
  obtain ⟨hsup, hbot, hcard⟩ := s48_Z1_sup_card (X := X) C hH
  exact ⟨hsup, hbot, hcard, s48_Z1_elem (X := X) C hH⟩

private theorem s48_Z1_nontriv (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) :
    ∃ l ∈ X.L 1, ∃ e ∈ X.Z 1, ⁅l, e⁆ ∉ (⊥ : Subgroup G) := by
  obtain ⟨-, -, hcardZ1, -⟩ := s48_Z1_struct (X := X) C hH
  have hoddCenter := (X.s48_1 C).2
  by_contra! hcon
  have hZ1center : X.Z 1 ≤ centerOf (X.L 1) := by
    refine le_inf ((X.Z_le_Q 1).trans (X.Q_le_L 1)) ?_
    intro e he
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have h := hcon l hl e he
    rw [Subgroup.mem_bot] at h
    exact commutatorElement_eq_one_iff_mul_comm.mp h
  have hbot : centerOf (X.L 1) = ⊥ := hoddCenter 1 (by norm_num)
  have hZ1bot : X.Z 1 = ⊥ := le_bot_iff.mp (hbot ▸ hZ1center)
  have hcard1 : Nat.card (X.Z 1) = 1 := by rw [hZ1bot]; simp
  have h2 : 1 < Nat.card (X.Z 1) := by
    rw [hcardZ1]
    have h4 : 4 ≤ 2 ^ (2 * X.n 0) := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (2 * X.n 0) :=
          Nat.pow_le_pow_right (by norm_num) (by have := C.hyp.two_le_n 0; omega)
    omega
  omega

private theorem s48_Z1_sec (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) : IsElemSec (⊥ : Subgroup G) (X.Z 1) := by
  obtain ⟨-, -, -, helemZ1⟩ := s48_Z1_struct (X := X) C hH
  refine ⟨bot_le, ?_, ?_⟩
  · rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [Subgroup.mem_bot]
    exact commutatorElement_eq_one_iff_mul_comm.mpr
      (CFSG.Open.IsElemAbelian.comm helemZ1 ha hb)
  · intro e he
    rw [Subgroup.mem_bot]
    exact helemZ1.2 e he

private theorem s48_Z1_normal :
    X.L 1 ≤ Subgroup.normalizer (X.Z 1 : Set G) ⊓
      Subgroup.normalizer (⊥ : Subgroup G) := by
  refine le_inf ?_ ?_
  · intro l hl
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr (X.Z_normal 1 l (X.L_le_Gi 1 hl))
  · intro l hl
    rw [Subgroup.normalizer_eq_top_iff.mpr inferInstance]
    exact Subgroup.mem_top l

theorem n_one_eq (C : X.Comm48 s r d) (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) :
    X.n 1 = X.n 0 := by
  have hle : X.n 1 ≤ X.n 0 := by
    obtain ⟨-, -, hcardZ1, -⟩ := s48_Z1_struct (X := X) C hH
    haveI : Finite ↥(X.L 1) := finite_of_le_stabilizer X.hyp (H := X.L 1) (X.L_le_Gi 1)
    have hm : 1 ≤ X.n 1 := le_trans (by norm_num) (C.hyp.two_le_n 1)
    have hquot : IsL2Quot (X.n 1) (oTwoQuot ↥(X.L 1)) :=
      (X.hyp.isLocL2_oTwoPrime (X.vert 1)).quot
    have hsec : IsElemSec (⊥ : Subgroup G) (X.Z 1) := s48_Z1_sec (X := X) C hH
    have hL := s48_Z1_normal (X := X)
    have hQ : ∀ p ∈ pCoreOf 2 (X.L 1), ∀ v ∈ X.Z 1, ⁅p, v⁆ ∈ (⊥ : Subgroup G) := by
      intro p hp v hv
      rw [Subgroup.mem_bot]
      have hpQ : p ∈ X.Q 1 := by
        change p ∈ pCoreOf 2 (MulAction.stabilizer G (X.vert 1))
        rw [← (X.hyp.isLocL2_oTwoPrime (X.vert 1)).pCoreOf_eq]
        exact hp
      have hvc : v ∈ Subgroup.centralizer (X.Q 1 : Set G) :=
        (Subgroup.mem_inf.mp (X.Z_le_center 1 hv)).2
      exact commutatorElement_eq_one_iff_mul_comm.mpr
        ((Subgroup.mem_centralizer_iff.mp hvc) p hpQ)
    have hnt := s48_Z1_nontriv (X := X) C hH
    have hEL : X.Z 1 ≤ X.L 1 := (X.Z_le_Q 1).trans (X.Q_le_L 1)
    have h := two_pow_le_relIndex_of_nontrivial_of_le (L := X.L 1) (V := X.Z 1) (Z := ⊥)
      hm hquot hEL hsec hL hQ hnt
    rw [Subgroup.relIndex_bot_left, hcardZ1] at h
    have h2 : 2 * X.n 1 ≤ 2 * X.n 0 :=
      (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h
    omega
  have hge : X.n 0 ≤ X.n 1 := (X.s48_6 C).2.1
  omega

private theorem Z_zero_le_relCent_Z_one (C : X.Comm48 s r d) :
    X.Z 0 ≤ relCent (X.Z 1) (⊥ : Subgroup G) (X.edgeSylow 0) := by
  intro z hz
  rw [mem_relCent (E := X.Z 1) (Z := (⊥ : Subgroup G)) (A := X.edgeSylow 0)
    (by
      intro x hx
      rw [Subgroup.normalizer_eq_top_iff.mpr inferInstance]
      exact Subgroup.mem_top x)]
  refine ⟨(X.s48_1 C).1 hz, ?_⟩
  intro a ha
  rw [Subgroup.mem_bot]
  have hzC : z ∈ Subgroup.centralizer (X.L 0 : Set G) := by
    rw [(X.s48_0 C).2] at hz
    exact (Subgroup.mem_inf.mp hz).2
  exact commutatorElement_eq_one_iff_mul_comm.mpr
    ((Subgroup.mem_centralizer_iff.mp hzC) a (X.edgeSylow_le_L 0 ha)).symm

private theorem s48_natPre (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) :
    NatPre (X.Gi 1) (X.L 1) (X.Z 1) ⊥ (X.n 1) := by
  obtain ⟨-, -, hcardZ1, -⟩ := s48_Z1_struct (X := X) C hH
  haveI : Finite ↥(X.Gi 1) := X.hyp.finite_stab (X.vert 1)
  haveI : Finite ↥(X.L 1) := finite_of_le_stabilizer X.hyp (H := X.L 1) (X.L_le_Gi 1)
  have hLP : X.L 1 ≤ X.Gi 1 := X.L_le_Gi 1
  have hPL : X.Gi 1 ≤ Subgroup.normalizer (X.L 1 : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (X.L_le_Gi 1)).mp
      (X.hyp.isLocL2_oTwoPrime (X.vert 1)).normal
  have hPE : X.Gi 1 ≤ Subgroup.normalizer (X.Z 1 : Set G) := fun g hg =>
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr (X.Z_normal 1 g hg)
  have hquot : IsL2Quot (X.n 1) (oTwoQuot ↥(X.L 1)) :=
    (X.hyp.isLocL2_oTwoPrime (X.vert 1)).quot
  have hsec : IsElemSec (⊥ : Subgroup G) (X.Z 1) := s48_Z1_sec (X := X) C hH
  have hcore : ∀ q ∈ pCoreOf 2 (X.Gi 1), ∀ e ∈ X.Z 1, ⁅q, e⁆ ∈ (⊥ : Subgroup G) := by
    intro q hq e he
    rw [Subgroup.mem_bot]
    have hqQ : q ∈ X.Q 1 := hq
    have hec : e ∈ Subgroup.centralizer (X.Q 1 : Set G) :=
      (Subgroup.mem_inf.mp (X.Z_le_center 1 he)).2
    exact commutatorElement_eq_one_iff_mul_comm.mpr
      ((Subgroup.mem_centralizer_iff.mp hec) q hqQ)
  have hnontriv : ∃ l ∈ X.L 1, ∃ e ∈ X.Z 1, ⁅l, e⁆ ∉ (⊥ : Subgroup G) :=
    s48_Z1_nontriv (X := X) C hH
  exact
    { le := hLP
      norm_L := hPL
      norm_E := hPE
      norm_K := by
        intro x hx
        rw [Subgroup.normalizer_eq_top_iff.mpr inferInstance]
        exact Subgroup.mem_top x
      sec := hsec
      card := by
        rw [Subgroup.relIndex_bot_left, hcardZ1, n_one_eq (X := X) C hH]
      core := hcore
      quot := hquot
      nontriv := hnontriv }

private theorem s48_natQuot (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) : NatQuot (X.L 1) (X.Z 1) ⊥ (X.n 1) := by
  obtain ⟨-, -, -, -, hcardZ0, -, -, -⟩ := X.s48_2 C
  have hNP := s48_natPre (X := X) C hH
  haveI : Finite ↥(X.Gi 1) := X.hyp.finite_stab (X.vert 1)
  have hT : IsSylowTwoOf (X.edgeSylow 0) (X.L 1) := by
    have h := X.isSylowTwoOf_edgeSylow_L_succ 0
    simpa using h
  have hZ0rel := Z_zero_le_relCent_Z_one (X := X) C
  haveI : Finite ↥(relCent (X.Z 1) (⊥ : Subgroup G) (X.edgeSylow 0)) :=
    finite_of_le_stabilizer X.hyp
      (H := relCent (X.Z 1) (⊥ : Subgroup G) (X.edgeSylow 0))
      (fun x hx => X.Z_le_Gi 1 hx.1)
  have hC : 2 ^ X.n 1 ≤ (⊥ : Subgroup G).relIndex
      (relCent (X.Z 1) (⊥ : Subgroup G) (X.edgeSylow 0)) := by
    rw [Subgroup.relIndex_bot_left]
    have h := Subgroup.card_le_of_le hZ0rel
    rw [hcardZ0] at h
    simpa [n_one_eq (X := X) C hH] using h
  have hEL : X.Z 1 ≤ X.L 1 := (X.Z_le_Q 1).trans (X.Q_le_L 1)
  exact natQuot_of_two_pow_le (C.hyp.two_le_n 1) hNP hEL hT hC

end Comm48

variable (X) in
open Comm48 in
theorem s48_4' (C : X.Comm48 s r d) (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) :
    X.ZQ d = X.Z 2 ∧ X.Z 1 = X.Z 0 ⊔ X.Z 2 ∧ X.Z 0 ⊓ X.Z 2 = ⊥ ∧
      Nat.card (X.Z 1) = 2 ^ (2 * X.n 0) ∧ IsElemAbelian 2 (X.Z 1) ∧
      NatQuot (X.L 1) (X.Z 1) ⊥ (X.n 1) := by
  have hH_eq : X.ZQ d = X.Z 2 := s48_H_eq (X := X) C hH
  obtain ⟨hsup, hbot, hcard, helem⟩ := s48_Z1_struct (X := X) C hH
  exact ⟨hH_eq, hsup, hbot, hcard, helem, s48_natQuot (X := X) C hH⟩

namespace Comm48

theorem card_K (C : X.Comm48 s r d) (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) :
    Nat.card X.K = (2 ^ X.n 0 - 1) ^ 2 := by
  have hb : Even ((d : ℤ) + 1) := by
    obtain ⟨k, hk⟩ := C.even
    exact ⟨(k : ℤ), by exact_mod_cast hk⟩
  have hfirst : X.Ki ((d : ℤ) + 1) ⊓ X.Ki 0 = ⊥ := (X.s48_6 C).1
  obtain ⟨hlow, hup⟩ := card_K_bounds (X := X) hb hfirst
  have hup' : Nat.card X.K ≤ (2 ^ X.n 0 - 1) ^ 2 := by
    rw [n_one_eq (X := X) C hH] at hup
    simpa [pow_two] using hup
  exact le_antisymm hup' hlow

theorem comm_Z1_edgeSylow (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) :
    ⁅X.Z 1, X.edgeSylow 0⁆ = X.Z 0 := by
  obtain ⟨-, -, -, -, hcardZ0, -, -, -⟩ := X.s48_2 C
  obtain ⟨-, -, -, -, -, hnatZ1⟩ := X.s48_4' C hH
  have hS : IsSylowTwoOf (X.edgeSylow 0) (X.L 1) := by
    have h := X.isSylowTwoOf_edgeSylow_L_succ 0
    simpa using h
  have hZ0rel := Z_zero_le_relCent_Z_one (X := X) C
  have hline : (⊥ : Subgroup G).relIndex
      (relCent (X.Z 1) (⊥ : Subgroup G) (X.edgeSylow 0)) = 2 ^ X.n 0 := by
    have h := hnatZ1.line (X.edgeSylow 0) hS
    rw [n_one_eq (X := X) C hH] at h
    simpa using h
  haveI hrelFin : Finite ↥(relCent (X.Z 1) (⊥ : Subgroup G) (X.edgeSylow 0)) :=
    finite_of_le_stabilizer X.hyp
      (H := relCent (X.Z 1) (⊥ : Subgroup G) (X.edgeSylow 0))
      (fun x hx => X.Z_le_Gi 1 hx.1)
  have hcardrel : Nat.card ↥(relCent (X.Z 1) (⊥ : Subgroup G) (X.edgeSylow 0)) = 2 ^ X.n 0 := by
    rw [← Subgroup.relIndex_bot_left (H := relCent (X.Z 1) (⊥ : Subgroup G)
      (X.edgeSylow 0))]
    exact hline
  have heq : relCent (X.Z 1) (⊥ : Subgroup G) (X.edgeSylow 0) = X.Z 0 := by
    refine (Subgroup.eq_of_le_of_card_ge hZ0rel ?_).symm
    rw [hcardrel, hcardZ0]
  have hcomm := hnatZ1.comm_eq (X.edgeSylow 0) hS
  rw [heq] at hcomm
  simpa using hcomm

theorem comm_Z1_Q0 (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) :
    ⁅X.Z 1, X.Q 0⁆ = X.Z 0 := by
  have hcommS := comm_Z1_edgeSylow (X := X) C hH
  have hsup : X.Q 1 ⊔ X.Q 0 = X.edgeSylow 0 := by
    have h := X.sup_Q_eq_edgeSylow C.hyp.char 0
    simpa only [zero_add, sup_comm] using h
  have hQ1norm : X.Q 0 ≤ Subgroup.normalizer (X.Q 1 : Set G) :=
    (X.Q_le_edgeSylow_left 0).trans
      (((X.isSylowTwoOf_edgeSylow 0).1.trans inf_le_right).trans
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 1)))
  have hBA : ⁅X.Q 1, X.Z 1⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro q hq
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hzC := (Subgroup.mem_inf.mp (X.Z_le_center 1 hz)).2
    exact ((Subgroup.mem_centralizer_iff.mp hzC) q hq).symm
  have h := CFSG.LocalAnalysis.SteinbergBV.ConstantRank.commutator_sup_eq_of_centralizer
    (W := X.Z 1) (B := X.Q 0) (N := X.Q 1)
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hBA) hQ1norm
  rw [← h, sup_comm (X.Q 0) (X.Q 1), hsup]
  exact hcommS

private theorem s48_7_Z0_normalized (C : X.Comm48 s r 1) :
    X.L 0 ≤ Subgroup.normalizer (X.Z 0 : Set G) := by
  rw [(X.s48_0 C).2]
  exact le_normalizer_centerOf_self (X.L 0)

private theorem s48_7_Z1_le_C (C : X.Comm48 s r 1)
    (hH : X.ZQ 1 ≤ X.Q (((1 : ℕ) : ℤ) + 2)) :
    X.Z 1 ≤ relCent (X.L 0) (X.Z 0) (X.Q 0) := by
  have hZ0eq : ⁅X.Z 1, X.Q 0⁆ = X.Z 0 := comm_Z1_Q0 (X := X) C hH
  have hZ0n : X.L 0 ≤ Subgroup.normalizer (X.Z 0 : Set G) := s48_7_Z0_normalized (X := X) C
  have hZ1Gi0 : X.Z 1 ≤ X.Gi 0 := C.hasB.Z_le_Gi (by omega)
  have hZ1p : IsPGroup 2 (X.Z 1) := (pCoreOf_isPGroup' (X.Gi 1)).to_le (X.Z_le_Q 1)
  have hZ1L0 : X.Z 1 ≤ X.L 0 := le_oTwoPrime_of_isPGroup hZ1p hZ1Gi0
  intro z hz
  rw [mem_relCent hZ0n]
  refine ⟨hZ1L0 hz, ?_⟩
  intro q hq
  have h1 : ⁅z, q⁆ ∈ ⁅X.Z 1, X.Q 0⁆ := Subgroup.commutator_mem_commutator hz hq
  rwa [hZ0eq] at h1

private theorem s48_7_C_not_le_Q0 (C : X.Comm48 s r 1)
    (hH : X.ZQ 1 ≤ X.Q (((1 : ℕ) : ℤ) + 2)) :
    ¬ relCent (X.L 0) (X.Z 0) (X.Q 0) ≤ X.Q 0 := by
  intro hle
  have hZ1C : X.Z 1 ≤ relCent (X.L 0) (X.Z 0) (X.Q 0) := s48_7_Z1_le_C (X := X) C hH
  have hnot : ¬ X.Z 1 ≤ X.Q 0 := by
    have h := (X.not_Z_le_Q_edge C.hasB).2
    simpa using h
  exact hnot (hZ1C.trans hle)

private theorem s48_7_C_normal (C : X.Comm48 s r 1) :
    X.L 0 ≤ Subgroup.normalizer
      (relCent (X.L 0) (X.Z 0) (X.Q 0) : Set G) := by
  have hZ0n : X.L 0 ≤ Subgroup.normalizer (X.Z 0 : Set G) := s48_7_Z0_normalized (X := X) C
  have hmemC : ∀ g, g ∈ relCent (X.L 0) (X.Z 0) (X.Q 0) ↔
      g ∈ X.L 0 ∧ ∀ a ∈ X.Q 0, ⁅g, a⁆ ∈ X.Z 0 := fun g => mem_relCent hZ0n
  have hQ0n : X.L 0 ≤ Subgroup.normalizer (X.Q 0 : Set G) :=
    (X.L_le_Gi 0).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 0))
  have hconj : ∀ l ∈ X.L 0, ∀ c ∈ relCent (X.L 0) (X.Z 0) (X.Q 0),
      l * c * l⁻¹ ∈ relCent (X.L 0) (X.Z 0) (X.Q 0) := by
    intro l hl c hc
    rw [hmemC] at hc ⊢
    refine ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hl hc.1) (Subgroup.inv_mem _ hl), ?_⟩
    intro a ha
    have ha' : l⁻¹ * a * l ∈ X.Q 0 :=
      (Subgroup.mem_normalizer_iff''.mp (hQ0n hl) a).mp ha
    have h1 : ⁅c, l⁻¹ * a * l⁆ ∈ X.Z 0 := hc.2 _ ha'
    have h2 : l * ⁅c, l⁻¹ * a * l⁆ * l⁻¹ ∈ X.Z 0 :=
      (Subgroup.mem_normalizer_iff.mp (hZ0n hl) _).mp h1
    have heq : l * ⁅c, l⁻¹ * a * l⁆ * l⁻¹ = ⁅l * c * l⁻¹, a⁆ := by
      rw [conjugate_commutatorElement]
      congr 1 <;> group
    rwa [heq] at h2
  intro l hl
  rw [Subgroup.mem_normalizer_iff]
  intro c
  exact ⟨fun hc => hconj l hl c hc, fun hc => by
    have h := hconj l⁻¹ (Subgroup.inv_mem _ hl) (l * c * l⁻¹) hc
    have hgc : l⁻¹ * (l * c * l⁻¹) * (l⁻¹)⁻¹ = c := by group
    rwa [hgc] at h⟩

private theorem s48_7_C_map_top (C : X.Comm48 s r 1)
    (hH : X.ZQ 1 ≤ X.Q (((1 : ℕ) : ℤ) + 2)) :
    ((relCent (X.L 0) (X.Z 0) (X.Q 0)).subgroupOf (X.L 0)).map
      (QuotientGroup.mk' (CFSG.pCore 2 ↥(X.L 0))) = ⊤ := by
  have hZ0n : X.L 0 ≤ Subgroup.normalizer (X.Z 0 : Set G) := s48_7_Z0_normalized (X := X) C
  have hC0n : X.L 0 ≤ Subgroup.normalizer
      (relCent (X.L 0) (X.Z 0) (X.Q 0) : Set G) := s48_7_C_normal (X := X) C
  have hC0Q0 : ¬ relCent (X.L 0) (X.Z 0) (X.Q 0) ≤ X.Q 0 :=
    s48_7_C_not_le_Q0 (X := X) C hH
  haveI hLfin : Finite ↥(X.L 0) := finite_of_le_stabilizer X.hyp (H := X.L 0) (X.L_le_Gi 0)
  have hQ0eq : X.Q 0 = pCoreOf 2 (X.L 0) :=
    ((X.hyp.isLocL2_oTwoPrime (X.vert 0)).pCoreOf_eq).symm
  have hquot0 : IsL2Quot (X.n 0) (oTwoQuot ↥(X.L 0)) :=
    (X.hyp.isLocL2_oTwoPrime (X.vert 0)).quot
  haveI hsimple : IsSimpleGroup (oTwoQuot ↥(X.L 0)) := by
    obtain ⟨e⟩ := hquot0
    have hF : 4 ≤ Nat.card (GaloisField 2 (X.n 0)) := by
      rw [GaloisField.card 2 (X.n 0) (by have := C.hyp.two_le_n 0; omega)]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ X.n 0 := Nat.pow_le_pow_right (by norm_num) (C.hyp.two_le_n 0)
    haveI : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 (X.n 0))) :=
      Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hF
    exact e.isSimpleGroup
  set Qb : Subgroup ↥(X.L 0) := (X.Q 0).subgroupOf (X.L 0) with hQbdef
  set Cb : Subgroup ↥(X.L 0) :=
    (relCent (X.L 0) (X.Z 0) (X.Q 0)).subgroupOf (X.L 0) with hCbdef
  have hpcore : CFSG.pCore 2 ↥(X.L 0) = Qb := by
    rw [hQbdef, hQ0eq]
    exact (CFSG.openPCoreOf_subgroupOf 2 (X.L 0)).symm
  haveI hQbNormal : Qb.Normal := by rw [← hpcore]; infer_instance
  haveI hCbNormal : Cb.Normal := Subgroup.normal_subgroupOf_of_le_normalizer hC0n
  set Nim : Subgroup (oTwoQuot ↥(X.L 0)) :=
    Cb.map (QuotientGroup.mk' (CFSG.pCore 2 ↥(X.L 0))) with hNimdef
  haveI hNimNormal : Nim.Normal := hCbNormal.map _ (QuotientGroup.mk'_surjective _)
  have hNim_ne : Nim ≠ ⊥ := by
    intro hbot
    apply hC0Q0
    intro c hc
    have hcL : c ∈ X.L 0 := (mem_relCent hZ0n).mp hc |>.1
    have hmem : (⟨c, hcL⟩ : ↥(X.L 0)) ∈ Cb := Subgroup.mem_subgroupOf.mpr hc
    have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥(X.L 0)) (⟨c, hcL⟩ : ↥(X.L 0)) ∈ Nim := by
      rw [hNimdef]
      exact Subgroup.mem_map_of_mem _ hmem
    rw [hbot] at h1
    have h2 : QuotientGroup.mk' (CFSG.pCore 2 ↥(X.L 0)) (⟨c, hcL⟩ : ↥(X.L 0)) = 1 :=
      Subgroup.mem_bot.mp h1
    have h3 : (⟨c, hcL⟩ : ↥(X.L 0)) ∈ CFSG.pCore 2 ↥(X.L 0) :=
      (QuotientGroup.eq_one_iff _).mp h2
    rw [hpcore] at h3
    exact Subgroup.mem_subgroupOf.mp h3
  have hNim_top : Nim = ⊤ := (Subgroup.Normal.eq_bot_or_eq_top Nim).resolve_left hNim_ne
  simpa [hNimdef, hCbdef] using hNim_top

private theorem s48_7_C_le (C : X.Comm48 s r 1)
    (hH : X.ZQ 1 ≤ X.Q (((1 : ℕ) : ℤ) + 2)) :
    X.L 0 ≤ relCent (X.L 0) (X.Z 0) (X.Q 0) ⊔ X.Q 0 := by
  have hQ0eq : X.Q 0 = pCoreOf 2 (X.L 0) :=
    ((X.hyp.isLocL2_oTwoPrime (X.vert 0)).pCoreOf_eq).symm
  have hpcore : CFSG.pCore 2 ↥(X.L 0) = (X.Q 0).subgroupOf (X.L 0) := by
    rw [hQ0eq]
    exact (CFSG.openPCoreOf_subgroupOf 2 (X.L 0)).symm
  have hmap := s48_7_C_map_top (X := X) C hH
  intro x hx
  have hxbar : QuotientGroup.mk' (CFSG.pCore 2 ↥(X.L 0)) (⟨x, hx⟩ : ↥(X.L 0)) ∈
      ((relCent (X.L 0) (X.Z 0) (X.Q 0)).subgroupOf (X.L 0)).map
        (QuotientGroup.mk' (CFSG.pCore 2 ↥(X.L 0))) := by
    rw [hmap]
    exact Subgroup.mem_top _
  obtain ⟨c, hcCb, hceq⟩ := Subgroup.mem_map.mp hxbar
  have hcC : (c : G) ∈ relCent (X.L 0) (X.Z 0) (X.Q 0) :=
    Subgroup.mem_subgroupOf.mp hcCb
  have hdiff : c⁻¹ * (⟨x, hx⟩ : ↥(X.L 0)) ∈ (X.Q 0).subgroupOf (X.L 0) := by
    have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥(X.L 0))
        (c⁻¹ * (⟨x, hx⟩ : ↥(X.L 0))) = 1 := by
      rw [map_mul, map_inv, hceq, inv_mul_cancel]
    have h2 : c⁻¹ * (⟨x, hx⟩ : ↥(X.L 0)) ∈ CFSG.pCore 2 ↥(X.L 0) :=
      (QuotientGroup.eq_one_iff _).mp h1
    rwa [hpcore] at h2
  have hq : ((c⁻¹ * (⟨x, hx⟩ : ↥(X.L 0)) : ↥(X.L 0)) : G) ∈ X.Q 0 :=
    Subgroup.mem_subgroupOf.mp hdiff
  have hcq : (c : G) * ((c⁻¹ * (⟨x, hx⟩ : ↥(X.L 0)) : ↥(X.L 0)) : G) = x := by
    have h : (c * (c⁻¹ * (⟨x, hx⟩ : ↥(X.L 0))) : ↥(X.L 0)) = ⟨x, hx⟩ := by group
    simpa using congrArg Subtype.val h
  rw [← hcq]
  exact Subgroup.mul_mem_sup hcC hq

private theorem s48_7_C_sup (C : X.Comm48 s r 1)
    (hH : X.ZQ 1 ≤ X.Q (((1 : ℕ) : ℤ) + 2)) :
    X.L 0 = relCent (X.L 0) (X.Z 0) (X.Q 0) ⊔ X.Q 0 := by
  have hZ0n : X.L 0 ≤ Subgroup.normalizer (X.Z 0 : Set G) := s48_7_Z0_normalized (X := X) C
  have hC0n : X.L 0 ≤ Subgroup.normalizer
      (relCent (X.L 0) (X.Z 0) (X.Q 0) : Set G) := s48_7_C_normal (X := X) C
  have hle := s48_7_C_le (X := X) C hH
  refine le_antisymm hle (sup_le ?_ ?_)
  · intro c hc
    exact (mem_relCent hZ0n).mp hc |>.1
  · exact X.Q_le_L 0

private theorem s48_7_odd_mem_C (C : X.Comm48 s r 1)
    (hH : X.ZQ 1 ≤ X.Q (((1 : ℕ) : ℤ) + 2))
    {x : G} (hxL : x ∈ X.L 0) (hxodd : Odd (orderOf x)) :
    x ∈ relCent (X.L 0) (X.Z 0) (X.Q 0) := by
  have hZ0n : X.L 0 ≤ Subgroup.normalizer (X.Z 0 : Set G) := s48_7_Z0_normalized (X := X) C
  have hmemC : ∀ g, g ∈ relCent (X.L 0) (X.Z 0) (X.Q 0) ↔
      g ∈ X.L 0 ∧ ∀ a ∈ X.Q 0, ⁅g, a⁆ ∈ X.Z 0 := fun g => mem_relCent hZ0n
  have hsup : X.L 0 = relCent (X.L 0) (X.Z 0) (X.Q 0) ⊔ X.Q 0 := s48_7_C_sup (X := X) C hH
  have hC0L0 : relCent (X.L 0) (X.Z 0) (X.Q 0) ≤ X.L 0 :=
    fun c hc => (hmemC c).mp hc |>.1
  have hQ0n : X.L 0 ≤ Subgroup.normalizer (X.Q 0 : Set G) :=
    (X.L_le_Gi 0).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 0))
  have hCNQ0 : relCent (X.L 0) (X.Z 0) (X.Q 0) ≤
      Subgroup.normalizer (X.Q 0 : Set G) := hC0L0.trans hQ0n
  have hxmem : x ∈ relCent (X.L 0) (X.Z 0) (X.Q 0) ⊔ X.Q 0 := by
    rw [← hsup]
    exact hxL
  obtain ⟨c, hcC, q, hqQ, hcq⟩ :=
    (CFSG.Quasithin.F1.mem_sup_iff_exists_mul_of_le_normalizer hCNQ0).mp hxmem
  have hcL : c ∈ X.L 0 := hC0L0 hcC
  have hqL : q ∈ X.L 0 := X.Q_le_L 0 hqQ
  have hqC : q ∈ relCent (X.L 0) (X.Z 0) (X.Q 0) := by
    have hQ0p : IsPGroup 2 (X.Q 0) := pCoreOf_isPGroup' (X.Gi 0)
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hQ0p) ⟨q, hqQ⟩
    have hqord : orderOf q = 2 ^ k := by simpa using hk
    have hC0n : X.L 0 ≤ Subgroup.normalizer
        (relCent (X.L 0) (X.Z 0) (X.Q 0) : Set G) := s48_7_C_normal (X := X) C
    set Cb : Subgroup ↥(X.L 0) :=
      (relCent (X.L 0) (X.Z 0) (X.Q 0)).subgroupOf (X.L 0) with hCbdef
    haveI hCbNormal : Cb.Normal := Subgroup.normal_subgroupOf_of_le_normalizer hC0n
    have heq : QuotientGroup.mk' Cb (⟨x, hxL⟩ : ↥(X.L 0)) =
        QuotientGroup.mk' Cb (⟨q, hqL⟩ : ↥(X.L 0)) := by
      have hxeq : (⟨x, hxL⟩ : ↥(X.L 0)) = ⟨c, hcL⟩ * ⟨q, hqL⟩ := by
        ext
        exact hcq
      rw [hxeq, map_mul]
      have hc1 : QuotientGroup.mk' Cb (⟨c, hcL⟩ : ↥(X.L 0)) = 1 := by
        rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']
        exact Subgroup.mem_subgroupOf.mpr hcC
      rw [hc1, one_mul]
    have hordx : orderOf (QuotientGroup.mk' Cb (⟨q, hqL⟩ : ↥(X.L 0))) ∣ orderOf x := by
      have h := orderOf_map_dvd (QuotientGroup.mk' Cb) (⟨x, hxL⟩ : ↥(X.L 0))
      rw [Subgroup.orderOf_mk] at h
      rwa [heq] at h
    have hord2 : orderOf (QuotientGroup.mk' Cb (⟨q, hqL⟩ : ↥(X.L 0))) ∣ 2 ^ k := by
      have h := orderOf_map_dvd (QuotientGroup.mk' Cb) (⟨q, hqL⟩ : ↥(X.L 0))
      rwa [Subgroup.orderOf_mk, hqord] at h
    have hcop : Nat.Coprime (orderOf x) (2 ^ k) := hxodd.coprime_two_right.pow_right k
    have h1 : orderOf (QuotientGroup.mk' Cb (⟨q, hqL⟩ : ↥(X.L 0))) = 1 :=
      Nat.eq_one_of_dvd_coprimes hcop hordx hord2
    have h2 : QuotientGroup.mk' Cb (⟨q, hqL⟩ : ↥(X.L 0)) = 1 := orderOf_eq_one_iff.mp h1
    have h3 : (⟨q, hqL⟩ : ↥(X.L 0)) ∈ Cb := (QuotientGroup.eq_one_iff _).mp h2
    exact Subgroup.mem_subgroupOf.mp h3
  rw [hcq]
  exact (relCent (X.L 0) (X.Z 0) (X.Q 0)).mul_mem hcC hqC

private theorem commutator_eq_bot_of_coprime_of_le {F W R : Subgroup G} [Finite ↥F]
    (hWF : W ≤ F) (hRF : R ≤ F) (hRW : R ≤ Subgroup.normalizer (W : Set G))
    (hcop : Nat.Coprime (Nat.card R) (Nat.card W)) (hdouble : ⁅⁅W, R⁆, R⁆ = ⊥) :
    ⁅W, R⁆ = ⊥ := by
  have hWmap : (W.subgroupOf F).map F.subtype = W := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hWF]
  have hRmap : (R.subgroupOf F).map F.subtype = R := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hRF]
  have hdouble' : ⁅⁅W.subgroupOf F, R.subgroupOf F⁆, R.subgroupOf F⁆ = ⊥ := by
    refine (Subgroup.map_eq_bot_iff_of_injective
      (H := ⁅⁅W.subgroupOf F, R.subgroupOf F⁆, R.subgroupOf F⁆) (f := F.subtype)
      Subtype.coe_injective).mp ?_
    rw [Subgroup.map_commutator, Subgroup.map_commutator, hWmap, hRmap, hdouble]
  have hRW' : R.subgroupOf F ≤ Subgroup.normalizer (W.subgroupOf F : Set ↥F) := by
    have h1 : R.subgroupOf F ≤ (Subgroup.normalizer (W : Set G)).subgroupOf F :=
      Subgroup.subgroupOf_mono F hRW
    rwa [Subgroup.subgroupOf_normalizer_eq hWF] at h1
  have hcop' : Nat.Coprime (Nat.card (R.subgroupOf F)) (Nat.card (W.subgroupOf F)) := by
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRF).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWF).toEquiv]
  have h := CFSG.GorensteinWalter.commutator_eq_bot_of_coprime_double_commutator_eq_bot
    (W.subgroupOf F) (R.subgroupOf F) hRW' hcop' hdouble'
  have hmap := congrArg (Subgroup.map F.subtype) h
  rwa [Subgroup.map_commutator, hWmap, hRmap, Subgroup.map_bot] at hmap

private theorem s48_7_exists_cent (C : X.Comm48 s r 1)
    (hH : X.ZQ 1 ≤ X.Q (((1 : ℕ) : ℤ) + 2)) :
    ∃ k : G, k ∈ X.Ki 0 ∧ k ≠ 1 ∧ k ∈ Subgroup.centralizer (X.Q 0 : Set G) := by
  obtain ⟨k, hkKi, hk1, hkord, -⟩ := X.exists_generator_Ki 0 (C.hyp.two_le_n 0)
  have hkL : k ∈ X.L 0 := (Subgroup.mem_inf.mp hkKi).2
  have hkGi : k ∈ X.Gi 0 := X.L_le_Gi 0 hkL
  have hodd : Odd (orderOf k) := by
    rw [hkord]
    exact CFSG.Timmesfeld.Orders.odd_two_pow_sub_one (by have := C.hyp.two_le_n 0; omega)
  have hodd' : Odd (2 ^ X.n 0 - 1) := by rwa [hkord] at hodd
  have hZ0n : X.L 0 ≤ Subgroup.normalizer (X.Z 0 : Set G) := s48_7_Z0_normalized (X := X) C
  have hkC : k ∈ relCent (X.L 0) (X.Z 0) (X.Q 0) :=
    s48_7_odd_mem_C (X := X) C hH hkL hodd
  have hmemC : ∀ g, g ∈ relCent (X.L 0) (X.Z 0) (X.Q 0) ↔
      g ∈ X.L 0 ∧ ∀ a ∈ X.Q 0, ⁅g, a⁆ ∈ X.Z 0 := fun g => mem_relCent hZ0n
  have hzpowsC : Subgroup.zpowers k ≤ relCent (X.L 0) (X.Z 0) (X.Q 0) :=
    Subgroup.zpowers_le.mpr hkC
  have hQ0k_le : ⁅X.Q 0, Subgroup.zpowers k⁆ ≤ X.Z 0 := by
    rw [Subgroup.commutator_comm]
    refine Subgroup.commutator_le.mpr ?_
    intro r hr q hq
    exact (hmemC r).mp (hzpowsC hr) |>.2 q hq
  have hkCentZ0 : Subgroup.zpowers k ≤ Subgroup.centralizer (X.Z 0 : Set G) := by
    refine Subgroup.zpowers_le.mpr ?_
    refine Subgroup.mem_centralizer_iff.mpr ?_
    intro z hz
    rw [(X.s48_0 C).2] at hz
    exact ((Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hz).2) k hkL).symm
  have hZ0k_bot : ⁅X.Z 0, Subgroup.zpowers k⁆ = (⊥ : Subgroup G) := by
    rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hkCentZ0
  have hdouble_amb : ⁅⁅X.Q 0, Subgroup.zpowers k⁆, Subgroup.zpowers k⁆ = (⊥ : Subgroup G) := by
    have hle : ⁅⁅X.Q 0, Subgroup.zpowers k⁆, Subgroup.zpowers k⁆ ≤
        ⁅X.Z 0, Subgroup.zpowers k⁆ := Subgroup.commutator_mono_left hQ0k_le
    rw [hZ0k_bot] at hle
    exact le_bot_iff.mp hle
  haveI : Finite ↥(X.Gi 0) := X.hyp.finite_stab (X.vert 0)
  haveI : Finite ↥(X.Q 0) := finite_of_le_stabilizer X.hyp (H := X.Q 0) (X.Q_le_Gi 0)
  have hcoprime : Nat.Coprime (Nat.card (Subgroup.zpowers k)) (Nat.card (X.Q 0)) := by
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp (pCoreOf_isPGroup' (X.Gi 0) : IsPGroup 2 (X.Q 0))
    rw [Nat.card_zpowers, hkord, hm]
    exact hodd'.coprime_two_right.pow_right m
  have hamb : ⁅X.Q 0, Subgroup.zpowers k⁆ = ⊥ :=
    commutator_eq_bot_of_coprime_of_le (F := X.Gi 0) (X.Q_le_Gi 0)
      (Subgroup.zpowers_le.mpr hkGi)
      (Subgroup.zpowers_le.mpr (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 0) hkGi))
      hcoprime hdouble_amb
  have hkCentQ : k ∈ Subgroup.centralizer (X.Q 0 : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have hmem : ⁅k, q⁆ ∈ ⁅Subgroup.zpowers k, X.Q 0⁆ :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_zpowers k) hq
    have h' : ⁅Subgroup.zpowers k, X.Q 0⁆ = ⊥ := by
      rw [Subgroup.commutator_comm]; exact hamb
    rw [h', Subgroup.mem_bot] at hmem
    exact (commutatorElement_eq_one_iff_mul_comm.mp hmem).symm
  exact ⟨k, hkKi, hk1, hkCentQ⟩

private theorem s48_7_false_of_d_one (C : X.Comm48 s r 1)
    (hH : X.ZQ 1 ≤ X.Q (((1 : ℕ) : ℤ) + 2)) : False := by
  obtain ⟨k, hkKi, hk1, hkCentQ⟩ := s48_7_exists_cent (X := X) C hH
  have hkGi : k ∈ X.Gi 0 := X.L_le_Gi 0 (Subgroup.mem_inf.mp hkKi).2
  have hkQ0 : k ∈ X.Q 0 := C.hyp.char (X.vert 0) ⟨hkGi, hkCentQ⟩
  have hkK : k ∈ X.K := (Subgroup.mem_inf.mp hkKi).1
  have hmem : k ∈ X.K ⊓ X.edgeSylow 0 := ⟨hkK, X.Q_le_edgeSylow_left 0 hkQ0⟩
  rw [X.K_inf_edgeSylow 0] at hmem
  exact hk1 (Subgroup.mem_bot.mp hmem)

theorem three_le_d (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) : 3 ≤ d := by
  obtain ⟨m, hm⟩ := C.even
  have hd1 : 1 ≤ d := X.one_le_of_hasB C.hasB
  by_contra hcon
  have hd2 : d ≤ 2 := by omega
  have hd : d = 1 := by omega
  subst hd
  exact s48_7_false_of_d_one (X := X) C hH

private theorem n_lt_two_mul (C : X.Comm48 s r d) (i : ℤ) : X.n i < 2 * X.n i := by
  have h := C.hyp.two_le_n i
  omega

private theorem dist_three_of_adj_T0 {g : G} (hg : g ∈ X.Gi 0) {w : V}
    (hw : Γ.Adj (X.vert 0) w) :
    Γ.dist (X.vert 1) (g⁻¹ • w) ≤ 3 := by
  have hfix : g⁻¹ • X.vert 0 = X.vert 0 :=
    MulAction.mem_stabilizer_iff.mp ((X.Gi 0).inv_mem hg)
  have h1 : Γ.Adj (X.vert 1) (X.vert 0) := (X.adj 0).symm
  have h2 : Γ.Adj (X.vert 0) (g⁻¹ • w) := by
    have h := (X.hyp.adj_smul g⁻¹ (X.vert 0) w).mpr hw
    rwa [hfix] at h
  have hwalk : (SimpleGraph.Walk.cons h1
      (SimpleGraph.Walk.cons h2 SimpleGraph.Walk.nil)).length = 2 := rfl
  calc Γ.dist (X.vert 1) (g⁻¹ • w)
      ≤ (SimpleGraph.Walk.cons h1
          (SimpleGraph.Walk.cons h2 SimpleGraph.Walk.nil)).length :=
        SimpleGraph.dist_le _
    _ = 2 := hwalk
    _ ≤ 3 := by norm_num

private theorem dist_three_of_adj_T1 {g : G} (hg : g ∈ X.Gi 0) {w : V}
    (hw : Γ.Adj (X.vert 1) w) :
    Γ.dist (X.vert 1) (g⁻¹ • w) ≤ 3 := by
  have hfix : g⁻¹ • X.vert 0 = X.vert 0 :=
    MulAction.mem_stabilizer_iff.mp ((X.Gi 0).inv_mem hg)
  have h1 : Γ.Adj (X.vert 1) (X.vert 0) := (X.adj 0).symm
  have h2 : Γ.Adj (X.vert 0) (g⁻¹ • X.vert 1) := by
    have h := (X.hyp.adj_smul g⁻¹ (X.vert 0) (X.vert 1)).mpr (X.adj 0)
    rwa [hfix] at h
  have h3 : Γ.Adj (g⁻¹ • X.vert 1) (g⁻¹ • w) :=
    (X.hyp.adj_smul g⁻¹ (X.vert 1) w).mpr hw
  have hwalk : (SimpleGraph.Walk.cons h1
      (SimpleGraph.Walk.cons h2
        (SimpleGraph.Walk.cons h3 SimpleGraph.Walk.nil))).length = 3 := rfl
  calc Γ.dist (X.vert 1) (g⁻¹ • w)
      ≤ (SimpleGraph.Walk.cons h1
          (SimpleGraph.Walk.cons h2
            (SimpleGraph.Walk.cons h3 SimpleGraph.Walk.nil))).length :=
        SimpleGraph.dist_le _
    _ = 3 := hwalk

private theorem conjSub_Z1_le_Q01 (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) {g : G} (hg : g ∈ X.L 0) :
    conjSub g (X.Z 1) ≤ X.Q 0 ⊓ X.Q 1 := by
  have hd3 : 3 ≤ d := C.three_le_d hH
  have hs5 : 5 ≤ s := C.hyp.five_le
  have hmin : 3 ≤ min d s := le_min (by omega) (by omega)
  have hgGi : g ∈ X.Gi 0 := X.L_le_Gi 0 hg
  have hgfix : g • X.vert 0 = X.vert 0 := MulAction.mem_stabilizer_iff.mp hgGi
  have hZ1T0 : X.Z 1 ≤ X.Gi 0 := C.hasB.Z_le_Gi (by omega)
  have hfix : ∀ z ∈ X.Z 1, ∀ w : V,
      (Γ.Adj (X.vert 0) w ∨ Γ.Adj (X.vert 1) w) →
      (g * z * g⁻¹) • w = w := by
    intro z hz w hw
    have hdist : Γ.dist (X.vert 1) (g⁻¹ • w) ≤ 3 := by
      rcases hw with hw | hw
      · exact dist_three_of_adj_T0 (X := X) hgGi hw
      · exact dist_three_of_adj_T1 (X := X) hgGi hw
    have hk : Γ.dist (X.vert 1) (g⁻¹ • w) ≤ min d s := le_trans hdist hmin
    have hfixz := X.fixes_ball_of_hasB C.hyp (i := 1) (e := d) C.hasB
      (k := Γ.dist (X.vert 1) (g⁻¹ • w)) hk (w := g⁻¹ • w) rfl z hz
    calc (g * z * g⁻¹) • w = g • (z • (g⁻¹ • w)) := by
          rw [mul_smul, mul_smul]
      _ = g • (g⁻¹ • w) := by rw [hfixz]
      _ = w := by rw [smul_inv_smul]
  refine le_inf ?_ ?_
  ·
    apply X.le_Q_of_fixes_nbrs (i := 0)
    · exact F7.isPGroup_conjSub ((pCoreOf_isPGroup' (X.Gi 1)).to_le (X.Z_le_Q 1))
    · intro x hx
      rw [mem_conjSub] at hx
      have hxg : g * (g⁻¹ * x * g) * g⁻¹ ∈ X.Gi 0 :=
        (X.Gi 0).mul_mem ((X.Gi 0).mul_mem hgGi (hZ1T0 hx)) ((X.Gi 0).inv_mem hgGi)
      rwa [show g * (g⁻¹ * x * g) * g⁻¹ = x by group] at hxg
    · intro w hw x hx
      rw [mem_conjSub] at hx
      have hxfix := hfix (g⁻¹ * x * g) hx w (Or.inl hw)
      rwa [show g * (g⁻¹ * x * g) * g⁻¹ = x by group] at hxfix
  ·
    apply X.le_Q_of_fixes_nbrs (i := 1)
    · exact F7.isPGroup_conjSub ((pCoreOf_isPGroup' (X.Gi 1)).to_le (X.Z_le_Q 1))
    · intro x hx
      rw [mem_conjSub] at hx
      refine MulAction.mem_stabilizer_iff.mpr ?_
      have hfix1 := hfix (g⁻¹ * x * g) hx (X.vert 1) (Or.inl (X.adj 0))
      rwa [show g * (g⁻¹ * x * g) * g⁻¹ = x by group] at hfix1
    · intro w hw x hx
      rw [mem_conjSub] at hx
      have hxfix := hfix (g⁻¹ * x * g) hx w (Or.inr hw)
      rwa [show g * (g⁻¹ * x * g) * g⁻¹ = x by group] at hxfix

private theorem Vk_zero_le_Q01 (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) :
    X.Vk 0 ≤ X.Q 0 ⊓ X.Q 1 := by
  refine iSup_le fun g => iSup_le fun hg => ?_
  exact conjSub_Z1_le_Q01 (X := X) C hH hg

private theorem comm_conjSub_Z1_Q0 (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) {g : G} (hg : g ∈ X.L 0) :
    ⁅conjSub g (X.Z 1), X.Q 0⁆ ≤ X.Z 0 := by
  have hgGi : g ∈ X.Gi 0 := X.L_le_Gi 0 hg
  have hQ0 : conjSub g (X.Q 0) = X.Q 0 :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp
      ((CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 0)) hgGi)
  have hZ0 : conjSub g (X.Z 0) = X.Z 0 := X.Z_normal 0 g hgGi
  have h := conjSub_mono g (le_of_eq (C.comm_Z1_Q0 hH))
  rw [← conjSub_commutator, hQ0, hZ0] at h
  exact h

private theorem comm_Vk_Q0 (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) :
    ⁅X.Vk 0, X.Q 0⁆ = X.Z 0 := by
  refine le_antisymm ?_ ?_
  ·
    have hstep : ∀ x ∈ X.Vk 0, ∀ y : G, (∀ q ∈ X.Q 0, ⁅x, q⁆ ∈ X.Z 0) →
        (∀ q ∈ X.Q 0, ⁅y, q⁆ ∈ X.Z 0) → ∀ q ∈ X.Q 0, ⁅x * y, q⁆ ∈ X.Z 0 := by
      intro x hxV y ihx ihy q hq
      have hxGi : x ∈ X.Gi 0 := X.Q_le_Gi 0 ((Vk_zero_le_Q01 (X := X) C hH) hxV).1
      rw [commutatorElement_mul_left_eq_conj_mul]
      exact (X.Z 0).mul_mem ((Subgroup.mem_normalizer_iff.mp
        (Subgroup.mem_normalizer_iff_map_conj_eq.mpr (X.Z_normal 0 x hxGi)) ⁅y, q⁆).mp
        (ihy q hq)) (ihx q hq)
    have hgen : ∀ g, ∀ v ∈ (⨆ (_ : g ∈ X.L 0), conjSub g (X.Z 1)),
        ∀ q ∈ X.Q 0, ⁅v, q⁆ ∈ X.Z 0 := by
      intro g v hv
      refine Subgroup.iSup_induction' (fun (hg : g ∈ X.L 0) => conjSub g (X.Z 1))
        ?_ ?_ ?_ hv
      · intro hg v hv q hq
        exact comm_conjSub_Z1_Q0 (X := X) C hH hg
          (Subgroup.commutator_mem_commutator hv hq)
      · intro q hq
        simp
      · intro x y hx hy ihx ihy q hq
        exact hstep x (Subgroup.mem_iSup_of_mem g hx) y ihx ihy q hq
    rw [Subgroup.commutator_le]
    intro v hv q hq
    refine Subgroup.iSup_induction' (fun g => ⨆ (_ : g ∈ X.L 0), conjSub g (X.Z 1))
      (fun g v hv => hgen g v hv) (by intro q hq; simp) ?_ hv q hq
    intro x y hx hy ihx ihy q hq
    exact hstep x hx y ihx ihy q hq
  ·
    calc X.Z 0 = ⁅X.Z 1, X.Q 0⁆ := (C.comm_Z1_Q0 hH).symm
      _ ≤ ⁅X.Vk 0, X.Q 0⁆ := Subgroup.commutator_mono X.Z_one_le_Vk_zero le_rfl

private theorem Z1_le_centralizer_Vk (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) :
    X.Z 1 ≤ Subgroup.centralizer (X.Vk 0 : Set G) := by
  intro z hz
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have hvQ : v ∈ X.Q 1 := (Vk_zero_le_Q01 (X := X) C hH) hv |>.2
  have hzC := (Subgroup.mem_inf.mp (X.Z_le_center 1 hz)).2
  exact (Subgroup.mem_centralizer_iff.mp hzC) v hvQ

private theorem isElemAbelian_Vk (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) :
    IsElemAbelian 2 (X.Vk 0) := by
  obtain ⟨-, -, -, -, hZ1elem, -⟩ := X.s48_4' C hH
  have hZ1cent := Z1_le_centralizer_Vk (X := X) C hH
  have hV0 : X.Vk 0 = Subgroup.closure
      {x : G | ∃ g : G, ∃ _ : g ∈ X.L 0, x ∈ conjSub g (X.Z 1)} := by
    refine le_antisymm ?_ ?_
    · refine iSup_le fun g => iSup_le fun hg => ?_
      intro x hx
      exact Subgroup.subset_closure ⟨g, hg, hx⟩
    · rw [Subgroup.closure_le]
      rintro x ⟨g, hg, hx⟩
      exact Subgroup.mem_iSup_of_mem g (Subgroup.mem_iSup_of_mem hg hx)
  have hs_comm : ∀ a ∈ {x : G | ∃ g : G, ∃ _ : g ∈ X.L 0, x ∈ conjSub g (X.Z 1)},
      ∀ b ∈ {x : G | ∃ g : G, ∃ _ : g ∈ X.L 0, x ∈ conjSub g (X.Z 1)},
      a * b = b * a := by
    rintro a ⟨ga, hga, ha⟩ b ⟨gb, hgb, hb⟩
    rw [mem_conjSub] at ha
    rw [mem_conjSub] at hb
    have hbV : b ∈ X.Vk 0 := by
      rw [hV0]
      exact Subgroup.subset_closure ⟨gb, hgb, by rw [mem_conjSub]; exact hb⟩
    have hconjV : conjSub ga (X.Vk 0) = X.Vk 0 :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp ((X.L_le_normalizer_Vk 0) hga)
    have hb' : ga⁻¹ * b * ga ∈ X.Vk 0 := by
      have hbin : b ∈ conjSub ga (X.Vk 0) := by rwa [hconjV]
      exact mem_conjSub.mp hbin
    have hza : ga⁻¹ * a * ga ∈ X.Z 1 := ha
    have hcomm' : (ga⁻¹ * a * ga) * (ga⁻¹ * b * ga) =
        (ga⁻¹ * b * ga) * (ga⁻¹ * a * ga) :=
      ((Subgroup.mem_centralizer_iff.mp (hZ1cent hza)) (ga⁻¹ * b * ga) hb').symm
    calc a * b = ga * ((ga⁻¹ * a * ga) * (ga⁻¹ * b * ga)) * ga⁻¹ := by group
      _ = ga * ((ga⁻¹ * b * ga) * (ga⁻¹ * a * ga)) * ga⁻¹ := by rw [hcomm']
      _ = b * a := by group
  have hs_sq : ∀ a ∈ {x : G | ∃ g : G, ∃ _ : g ∈ X.L 0, x ∈ conjSub g (X.Z 1)},
      a ^ 2 = 1 := by
    rintro a ⟨g, hg, ha⟩
    rw [mem_conjSub] at ha
    have h := F7.isElemAbelian_conjSub (p := 2) (g := g) hZ1elem
    have ha' : a ∈ conjSub g (X.Z 1) := by rw [mem_conjSub]; exact ha
    exact (F7.isElemAbelian_iff.mp h).2 a ha'
  have hclosure := IsElemAbelian.closure_of_commute (p := 2) hs_comm hs_sq
  rwa [← hV0] at hclosure

end Comm48

variable (X) in
theorem Z_eq_sup_of_odd (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) {j : ℤ} (hj : Odd j) :
    X.Z j = X.Z (j - 1) ⊔ X.Z (j + 1) := by
  obtain ⟨k, hk⟩ := hj
  obtain ⟨-, hZ1sup, -, -, -, -⟩ := X.s48_4' C hH
  have h := X.Z_add k 1
  rw [show (1 : ℤ) + 2 * k = j by omega] at h
  rw [h, hZ1sup, conjSub_sup, ← X.Z_add k 0, ← X.Z_add k 2]
  rw [show (0 : ℤ) + 2 * k = j - 1 by omega,
    show (2 : ℤ) + 2 * k = j + 1 by omega]

namespace Comm48

private theorem Z1_inf_Zneg1 (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) : X.Z 1 ⊓ X.Z (-1) = X.Z 0 := by
  classical
  obtain ⟨-, h2r, -, hZ0eq, -, -, -, -⟩ := X.s48_2 C
  obtain ⟨hZ0leZ1, -⟩ := X.s48_1 C
  have hd3 : 3 ≤ d := C.three_le_d hH
  have hZ1sup : X.Z 1 = X.Z 0 ⊔ X.Z 2 := (X.s48_4' C hH).2.1
  have hZneg := X.Z_eq_sup_of_odd C hH (j := -1) (by norm_num)
  have hZ0leZneg : X.Z 0 ≤ X.Z (-1) := by
    rw [hZneg]; exact le_sup_right
  refine le_antisymm ?_ (le_inf hZ0leZ1 hZ0leZneg)
  have hd1 : X.HasB 1 d := C.hasB
  have hdm1 : X.HasB (-1) d := by
    have h := (X.hasB_iff_of_even (i := 1) (j := -1)
      (by norm_num : Even ((1 : ℤ) - (-1))) d).mp hd1
    simpa using h
  have hU2 : IsPGroup 2 (X.Z 1 ⊓ X.Z (-1) : Subgroup G) :=
    (pCoreOf_isPGroup' (G := G) (X.Gi 1)).to_le (inf_le_left.trans (X.Z_le_Q 1))
  have hKinv : X.K ≤ Subgroup.normalizer ((X.Z 1 ⊓ X.Z (-1) : Subgroup G) : Set G) := by
    intro k hk
    rw [mem_normalizer_iff_conjSub]
    rw [conjSub_inf, X.Z_normal 1 k (X.K_le_Gi 1 hk),
      X.Z_normal (-1) k (X.K_le_Gi (-1) hk)]
  have hUarc : X.Z 1 ⊓ X.Z (-1) ≤ X.arcStab (-((d : ℤ) + 1)) ((d : ℤ) + 1) := by
    refine X.le_arcStab_of_fixSet ?_
    intro j hj
    rw [Set.mem_Icc] at hj
    intro u hu
    have hu1 : u ∈ X.Z 1 := (Subgroup.mem_inf.mp hu).1
    have hum1 : u ∈ X.Z (-1) := (Subgroup.mem_inf.mp hu).2
    by_cases hjb : 2 - (d : ℤ) ≤ j
    · have hfix1 : j ∈ X.fixSet (X.Z 1) := by
        rw [X.fixSet_Z 1 hd1]
        rw [Set.mem_Icc]
        constructor <;> omega
      exact hfix1 u hu1
    · have hfixm1 : j ∈ X.fixSet (X.Z (-1)) := by
        rw [X.fixSet_Z (-1) hdm1]
        rw [Set.mem_Icc]
        constructor <;> omega
      exact hfixm1 u hum1
  have hUlePc : X.Z 1 ⊓ X.Z (-1) ≤
      pCoreOf 2 (X.arcStab (-((d : ℤ) + 1)) ((-((d : ℤ) + 1)) + (r : ℤ))) := by
    apply X.le_pCoreOf_arcStab_r C.hyp hU2
    rw [show -((d : ℤ) + 1) + (r : ℤ) = (d : ℤ) + 1 by
      have hr : (r : ℤ) = 2 * ((d : ℤ) + 1) := by
        have := h2r; exact_mod_cast this.symm
      omega]
    exact hUarc
  have hpc : pCoreOf 2 (X.arcStab (-((d : ℤ) + 1)) ((-((d : ℤ) + 1)) + (r : ℤ))) = X.Z 0 := by
    rw [show -((d : ℤ) + 1) + (r : ℤ) = (d : ℤ) + 1 by
      have hr : (r : ℤ) = 2 * ((d : ℤ) + 1) := by
        have := h2r; exact_mod_cast this.symm
      omega]
    exact hZ0eq.symm
  rw [hpc] at hUlePc
  exact hUlePc

private theorem card_Z0 (C : X.Comm48 s r d) :
    Nat.card (X.Z 0) = 2 ^ X.n 0 :=
  (X.s48_2 C).2.2.2.2.1

private theorem card_Z1 (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) : Nat.card (X.Z 1) = 2 ^ (2 * X.n 0) :=
  (X.s48_4' C hH).2.2.2.1

private theorem card_Zneg1 (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) : Nat.card (X.Z (-1)) = 2 ^ (2 * X.n 0) := by
  have h : X.Z (-1) = conjSub (X.τ ^ (-1 : ℤ)) (X.Z 1) := by
    simpa using X.Z_add (-1) 1
  rw [h, card_conjSub, card_Z1 (X := X) C hH]

private theorem card_Z1_sup_Zneg1 (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) :
    Nat.card (X.Z 1 ⊔ X.Z (-1) : Subgroup G) = 2 ^ (3 * X.n 0) := by
  have hV0ab : IsElemAbelian 2 (X.Vk 0) := isElemAbelian_Vk (X := X) C hH
  have hcent : X.Z (-1) ≤ Subgroup.centralizer (X.Z 1 : Set G) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hc := hV0ab.1.is_comm.comm ⟨z, X.Z_neg_one_le_Vk_zero hz⟩ ⟨y, X.Z_one_le_Vk_zero hy⟩
    exact (congrArg Subtype.val hc).symm
  have hcomm : ∀ b ∈ X.Z 1, ∀ n ∈ X.Z (-1), b * n * b⁻¹ ∈ X.Z (-1) := by
    intro b hb n hn
    have hnb : b * n = n * b :=
      (Subgroup.mem_centralizer_iff.mp (hcent hn)) b hb
    rw [show b * n * b⁻¹ = n by rw [hnb]; group]
    exact hn
  have h := CFSG.Timmesfeld.LocalTwoSubgroups.FrobeniusFixedSpaceBounds.card_sup_mul_card_inf
    (H := X.Z 1) (N := X.Z (-1)) hcomm
  rw [Z1_inf_Zneg1 (X := X) C hH, card_Z1 (X := X) C hH, card_Zneg1 (X := X) C hH,
    card_Z0 (X := X) C] at h
  refine Nat.mul_right_cancel ((pow_pos (by norm_num : (0 : ℕ) < 2) (X.n 0))) ?_
  show Nat.card (X.Z 1 ⊔ X.Z (-1) : Subgroup G) * 2 ^ X.n 0 =
    2 ^ (3 * X.n 0) * 2 ^ X.n 0
  calc Nat.card (X.Z 1 ⊔ X.Z (-1) : Subgroup G) * 2 ^ X.n 0
      = (2 ^ (2 * X.n 0)) * (2 ^ (2 * X.n 0)) := h
    _ = 2 ^ (3 * X.n 0) * 2 ^ X.n 0 := by
        rw [← pow_add, ← pow_add]
        congr 1
        omega

private theorem orbit_Zb_Tneg1 (C : X.Comm48 s r d) :
    ∀ w, Γ.Adj (X.vert 0) w → w ≠ X.vert 1 →
      ∃ z ∈ X.Z ((d : ℤ) + 1), z • X.vert (-1) = w := by
  intro w hw hw1
  have hS := (X.Z_succ_sup_Q_zero_and_inf C).1
  have hleft : Γ.Adj (X.vert 0) (X.vert (-1)) := by
    have h := (X.adj (-1)).symm
    rwa [show -1 + 1 = 0 by norm_num] at h
  have hne : X.vert (-1) ≠ X.vert 1 := by
    intro h
    have := X.vert_injective h
    omega
  obtain ⟨s, hsS, hsw⟩ :=
    X.edgeSylow_transitive_left 0 (X.vert (-1)) w hleft hne hw hw1
  have hZbGi0 : X.Z ((d : ℤ) + 1) ≤ X.Gi 0 :=
    (le_sup_left : X.Z ((d : ℤ) + 1) ≤ X.Z ((d : ℤ) + 1) ⊔ X.Q 0).trans
      (hS.le.trans ((X.isSylowTwoOf_edgeSylow 0).1.trans inf_le_left))
  have hZbNormQ0 : X.Z ((d : ℤ) + 1) ≤ Subgroup.normalizer (X.Q 0 : Set G) :=
    hZbGi0.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 0))
  rw [← hS] at hsS
  rw [sup_comm] at hsS
  change s ∈ ((X.Q 0 ⊔ X.Z ((d : ℤ) + 1) : Subgroup G) : Set G) at hsS
  rw [Subgroup.coe_mul_of_right_le_normalizer_left (X.Q 0) (X.Z ((d : ℤ) + 1))
    hZbNormQ0] at hsS
  obtain ⟨q, hq, z, hz, rfl⟩ := Set.mem_mul.mp hsS
  refine ⟨z, hz, ?_⟩
  have hzT0 : z • X.vert 0 = X.vert 0 :=
    MulAction.mem_stabilizer_iff.mp (hZbGi0 hz)
  have hadj : Γ.Adj (X.vert 0) (z • X.vert (-1)) := by
    have h := (X.hyp.adj_smul z (X.vert 0) (X.vert (-1))).mpr hleft
    rwa [hzT0] at h
  have hqfix : q • (z • X.vert (-1)) = z • X.vert (-1) :=
    X.Q_fixes_neighbors_vert 0 _ hadj q hq
  calc z • X.vert (-1) = q • (z • X.vert (-1)) := hqfix.symm
    _ = (q * z) • X.vert (-1) := (mul_smul q z _).symm
    _ = w := hsw

private theorem R_le_Vk (C : X.Comm48 s r d) : X.R48 d ≤ X.Vk 0 := by
  have hZL0 : X.Z ((d : ℤ) + 1) ≤ X.L 0 :=
    (le_sup_left : X.Z ((d : ℤ) + 1) ≤ X.Z ((d : ℤ) + 1) ⊔ X.Q 0).trans
      ((X.Z_succ_sup_Q_zero_and_inf C).1.le.trans (X.edgeSylow_le_L 0))
  exact (Subgroup.commutator_mono X.Z_neg_one_le_Vk_zero hZL0).trans
    (Subgroup.le_normalizer_iff_commutator_le_left.mp (X.L_le_normalizer_Vk 0))

private theorem Vk_eq_sup_R (C : X.Comm48 s r d) :
    X.Vk 0 = X.R48 d ⊔ X.Z 1 ⊔ X.Z (-1) := by
  have hRle := R_le_Vk (X := X) C
  refine le_antisymm ?_ ?_
  ·
    refine iSup_le fun g => iSup_le fun hg => ?_
    have hgT0 : g • X.vert 0 = X.vert 0 :=
      MulAction.mem_stabilizer_iff.mp (X.L_le_Gi 0 hg)
    have hw : Γ.Adj (X.vert 0) (g • X.vert 1) := by
      have h := (X.hyp.adj_smul g (X.vert 0) (X.vert 1)).mpr (X.adj 0)
      rwa [hgT0] at h
    have hgen_eq : conjSub g (X.Z 1) = vertZ (V := V) (G := G) (g • X.vert 1) := by
      rw [X.Z_eq_vertZ 1, ← vertZ_smul]
    change conjSub g (X.Z 1) ≤ X.R48 d ⊔ X.Z 1 ⊔ X.Z (-1)
    by_cases hg1 : g • X.vert 1 = X.vert 1
    · rw [hgen_eq, hg1, X.Z_eq_vertZ]
      exact (le_sup_of_le_right le_rfl).trans le_sup_left
    · obtain ⟨z, hz, hzv⟩ := orbit_Zb_Tneg1 (X := X) C (g • X.vert 1) hw hg1
      rw [hgen_eq, ← hzv, vertZ_smul, ← X.Z_eq_vertZ (-1)]
      have hgen : conjSub z (X.Z (-1)) ≤ X.Z (-1) ⊔ X.R48 d := by
        intro x hx
        rw [mem_conjSub] at hx
        have hyinv : (z⁻¹ * x * z)⁻¹ ∈ X.Z (-1) := (X.Z (-1)).inv_mem hx
        have hcomm : ⁅(z⁻¹ * x * z)⁻¹, z⁆ ∈ X.R48 d :=
          Subgroup.commutator_mem_commutator hyinv hz
        have hxeq : x = (z⁻¹ * x * z) * ⁅(z⁻¹ * x * z)⁻¹, z⁆ := by
          rw [commutatorElement_def]
          group
        rw [hxeq]
        exact Subgroup.mul_mem_sup hx hcomm
      refine hgen.trans (sup_le ?_ ?_)
      · exact le_sup_right
      · exact (le_sup_of_le_left le_rfl).trans le_sup_left
  ·
    exact sup_le (sup_le hRle X.Z_one_le_Vk_zero) X.Z_neg_one_le_Vk_zero

private theorem exists_commutator_Vk_zero_notMem_Z_zero (C : X.Comm48 s r d) (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) :
    ∃ l ∈ X.L 0, ∃ e ∈ X.Vk 0, ⁅l, e⁆ ∉ X.Z 0 := by
  obtain ⟨hZ0leZ1, -⟩ := X.s48_1 C
  haveI : Finite ↥(X.Z 0) := finite_of_le_stabilizer X.hyp (H := X.Z 0) (X.Z_le_Gi 0)
  by_contra! hcon
  obtain ⟨l, hlL, hl1⟩ := (X.hyp.isLocL2_oTwoPrime (X.vert 0)).trans
    (X.vert 1) (X.vert (-1)) (X.adj 0) (by
      have h := (X.adj (-1)).symm
      rwa [show -1 + 1 = 0 by norm_num] at h)
  have hZl : conjSub l (X.Z 1) = X.Z (-1) := (X.Z_smul X hl1).symm
  have hle : conjSub l (X.Z 1) ≤ X.Z 0 := by
    intro y hy
    rw [mem_conjSub] at hy
    have hcomm := hcon l hlL (l⁻¹ * y * l) (X.Z_one_le_Vk_zero hy)
    have hmemZ1 : l * (l⁻¹ * y * l) * l⁻¹ ∈ X.Z 1 := by
      have e : l * (l⁻¹ * y * l) * l⁻¹ = ⁅l, l⁻¹ * y * l⁆ * (l⁻¹ * y * l) := by
        rw [commutatorElement_def]
        group
      rw [e]
      exact (X.Z 1).mul_mem (hZ0leZ1 hcomm) hy
    have hmemZm1 : l * (l⁻¹ * y * l) * l⁻¹ ∈ X.Z (-1) := by
      have h : l * (l⁻¹ * y * l) * l⁻¹ ∈ conjSub l (X.Z 1) := by
        rw [mem_conjSub]
        have e : l⁻¹ * (l * (l⁻¹ * y * l) * l⁻¹) * l = l⁻¹ * y * l := by group
        rwa [e]
      rwa [hZl] at h
    have hyZ0 : l * (l⁻¹ * y * l) * l⁻¹ ∈ X.Z 0 := by
      have hinf : l * (l⁻¹ * y * l) * l⁻¹ ∈ X.Z 1 ⊓ X.Z (-1) :=
        Subgroup.mem_inf.mpr ⟨hmemZ1, hmemZm1⟩
      rwa [Z1_inf_Zneg1 (X := X) C hH] at hinf
    simpa [show l * (l⁻¹ * y * l) * l⁻¹ = y by group] using hyZ0
  rw [hZl] at hle
  have hcardle := Subgroup.card_le_of_le hle
  rw [card_Zneg1 (X := X) C hH, card_Z0 (X := X) C] at hcardle
  have hlt : 2 ^ X.n 0 < 2 ^ (2 * X.n 0) := by
    apply (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mpr
    exact n_lt_two_mul C 0
  exact (not_le_of_gt hlt) hcardle

private theorem Z_zero_Z_one_le_relCent_Vk_zero (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) :
    X.Z 0 ≤ relCent (X.Vk 0) (X.Z 0) (X.edgeSylow 0) ∧
      X.Z 1 ≤ relCent (X.Vk 0) (X.Z 0) (X.edgeSylow 0) := by
  obtain ⟨hZ0leZ1, -⟩ := X.s48_1 C
  have hVkLeQ01 := Vk_zero_le_Q01 (X := X) C hH
  have hZ0leVk : X.Z 0 ≤ X.Vk 0 := hZ0leZ1.trans X.Z_one_le_Vk_zero
  have hVkNormZ : X.Vk 0 ≤ Subgroup.normalizer (X.Z 0 : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact X.Z_normal 0 x (X.Q_le_Gi 0 ((hVkLeQ01 hx).1))
  constructor
  · intro z hz
    rw [mem_relCent (E := X.Vk 0) (Z := X.Z 0) (A := X.edgeSylow 0) hVkNormZ]
    refine ⟨hZ0leVk hz, ?_⟩
    intro a ha
    have haL : a ∈ X.L 0 := X.edgeSylow_le_L 0 ha
    have hzC : z ∈ Subgroup.centralizer (X.L 0 : Set G) := by
      rw [(X.s48_0 C).2] at hz
      exact (Subgroup.mem_inf.mp hz).2
    have h1 : ⁅z, a⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr
        ((Subgroup.mem_centralizer_iff.mp hzC) a haL).symm
    rw [h1]
    exact (X.Z 0).one_mem
  · intro z hz
    rw [mem_relCent (E := X.Vk 0) (Z := X.Z 0) (A := X.edgeSylow 0) hVkNormZ]
    refine ⟨X.Z_one_le_Vk_zero hz, ?_⟩
    intro a ha
    have h := C.comm_Z1_edgeSylow hH
    rw [← h]
    exact Subgroup.commutator_mem_commutator hz ha

private theorem two_pow_le_relIndex_relCent_Vk_zero (C : X.Comm48 s r d) (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) :
    2 ^ X.n 0 ≤ (X.Z 0).relIndex (relCent (X.Vk 0) (X.Z 0) (X.edgeSylow 0)) := by
  obtain ⟨hZ0leZ1, -⟩ := X.s48_1 C
  obtain ⟨hZ0leRelCent, hZ1rel⟩ := Z_zero_Z_one_le_relCent_Vk_zero (X := X) C hH
  have hVkLeQ01 := Vk_zero_le_Q01 (X := X) C hH
  haveI : Finite ↥(X.Vk 0) := finite_of_le_stabilizer X.hyp (H := X.Vk 0)
    (hVkLeQ01.trans (inf_le_left.trans (X.Q_le_Gi 0)))
  have hZ0relZ1 : (X.Z 0).relIndex (X.Z 1) = 2 ^ X.n 0 := by
    have h := Subgroup.relIndex_mul_card (H := X.Z 0) (K := X.Z 1)
    rw [inf_eq_left.mpr hZ0leZ1, card_Z0 (X := X) C, card_Z1 (X := X) C hH] at h
    refine Nat.mul_right_cancel ((pow_pos (by norm_num : (0 : ℕ) < 2) (X.n 0))) ?_
    show (X.Z 0).relIndex (X.Z 1) * 2 ^ X.n 0 = 2 ^ X.n 0 * 2 ^ X.n 0
    calc (X.Z 0).relIndex (X.Z 1) * 2 ^ X.n 0
        = 2 ^ (2 * X.n 0) := h
      _ = 2 ^ X.n 0 * 2 ^ X.n 0 := by
          rw [← pow_add]
          congr 1
          omega
  haveI : Finite ↥(relCent (X.Vk 0) (X.Z 0) (X.edgeSylow 0)) :=
    Finite.of_injective
      (Subgroup.inclusion (show relCent (X.Vk 0) (X.Z 0) (X.edgeSylow 0) ≤ X.Vk 0 from
        fun x hx => hx.1))
      (Subgroup.inclusion_injective _)
  have hrelne : (X.Z 0).relIndex (relCent (X.Vk 0) (X.Z 0) (X.edgeSylow 0)) ≠ 0 := by
    intro h0
    have h := Subgroup.relIndex_mul_card (H := X.Z 0)
      (K := relCent (X.Vk 0) (X.Z 0) (X.edgeSylow 0))
    rw [inf_eq_left.mpr hZ0leRelCent, h0, zero_mul] at h
    exact (Nat.card_pos (α := ↥(relCent (X.Vk 0) (X.Z 0) (X.edgeSylow 0)))).ne' h.symm
  calc 2 ^ X.n 0 = (X.Z 0).relIndex (X.Z 1) := hZ0relZ1.symm
    _ ≤ (X.Z 0).relIndex (relCent (X.Vk 0) (X.Z 0) (X.edgeSylow 0)) :=
      Subgroup.relIndex_le_of_le_right hZ1rel hrelne

private theorem isElemSec_Vk_Z0 (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) :
    IsElemSec (X.Z 0) (X.Vk 0) := by
  obtain ⟨hZ0leZ1, -⟩ := X.s48_1 C
  have hElem := isElemAbelian_Vk (X := X) C hH
  have hZ0leVk : X.Z 0 ≤ X.Vk 0 := hZ0leZ1.trans X.Z_one_le_Vk_zero
  have hcommV : ⁅X.Vk 0, X.Vk 0⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hc := hElem.1.is_comm.comm (⟨x, hx⟩ : ↥(X.Vk 0)) (⟨y, hy⟩ : ↥(X.Vk 0))
    exact (congrArg Subtype.val hc).symm
  refine ⟨hZ0leVk, ?_, ?_⟩
  · rw [hcommV]
    exact bot_le
  · intro e he
    have hsq : e * e = 1 := by simpa [pow_two] using hElem.2 e he
    rw [pow_two, hsq]
    exact (X.Z 0).one_mem

private theorem relIndex_Z0_Vk (C : X.Comm48 s r d)
    (hcard : Nat.card (X.Vk 0) = 2 ^ (3 * X.n 0)) :
    (X.Z 0).relIndex (X.Vk 0) = 2 ^ (2 * X.n 0) := by
  obtain ⟨-, -, -, -, hcardZ0, -, -, -⟩ := X.s48_2 C
  obtain ⟨hZ0leZ1, -⟩ := X.s48_1 C
  have hZ0leVk : X.Z 0 ≤ X.Vk 0 := hZ0leZ1.trans X.Z_one_le_Vk_zero
  have h := Subgroup.relIndex_mul_card (H := X.Z 0) (K := X.Vk 0)
  rw [inf_eq_left.mpr hZ0leVk, hcardZ0, hcard] at h
  refine Nat.mul_right_cancel ((pow_pos (by norm_num : (0 : ℕ) < 2) (X.n 0))) ?_
  show (X.Z 0).relIndex (X.Vk 0) * 2 ^ X.n 0 = 2 ^ (2 * X.n 0) * 2 ^ X.n 0
  calc (X.Z 0).relIndex (X.Vk 0) * 2 ^ X.n 0
      = 2 ^ (3 * X.n 0) := h
    _ = 2 ^ (2 * X.n 0) * 2 ^ X.n 0 := by
        rw [show 3 * X.n 0 = 2 * X.n 0 + X.n 0 by omega, pow_add]

private theorem natPre_Vk (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2))
    (hcard : Nat.card (X.Vk 0) = 2 ^ (3 * X.n 0)) :
    NatPre (X.L 0) (X.L 0) (X.Vk 0) (X.Z 0) (X.n 0) := by
  have hVkLeQ01 := Vk_zero_le_Q01 (X := X) C hH
  haveI : Finite ↥(X.L 0) := finite_of_le_stabilizer X.hyp (H := X.L 0) (X.L_le_Gi 0)
  haveI : Finite ↥(X.Vk 0) := finite_of_le_stabilizer X.hyp (H := X.Vk 0)
    (hVkLeQ01.trans (inf_le_left.trans (X.Q_le_Gi 0)))
  haveI : Finite ↥(X.Z 0) := finite_of_le_stabilizer X.hyp (H := X.Z 0) (X.Z_le_Gi 0)
  have hQ0pc : pCoreOf 2 (X.L 0) = X.Q 0 :=
    (X.hyp.isLocL2_oTwoPrime (X.vert 0)).pCoreOf_eq
  have hquot : IsL2Quot (X.n 0) (oTwoQuot ↥(X.L 0)) :=
    (X.hyp.isLocL2_oTwoPrime (X.vert 0)).quot
  have hnontriv := exists_commutator_Vk_zero_notMem_Z_zero (X := X) C hH
  have hcore : ∀ q ∈ pCoreOf 2 (X.L 0), ∀ e ∈ X.Vk 0, ⁅q, e⁆ ∈ X.Z 0 := by
    intro q hq e he
    rw [hQ0pc] at hq
    have hmem : ⁅e, q⁆ ∈ X.Z 0 := by
      have h := comm_Vk_Q0 (X := X) C hH
      rw [← h]
      exact Subgroup.commutator_mem_commutator he hq
    have hinv := (X.Z 0).inv_mem hmem
    rwa [commutatorElement_inv] at hinv
  have hnormZ : X.L 0 ≤ Subgroup.normalizer (X.Z 0 : Set G) := by
    intro l hl
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact X.Z_normal 0 l (X.L_le_Gi 0 hl)
  exact
    { le := le_rfl
      norm_L := Subgroup.le_normalizer
      norm_E := X.L_le_normalizer_Vk 0
      norm_K := hnormZ
      sec := isElemSec_Vk_Z0 (X := X) C hH
      card := relIndex_Z0_Vk (X := X) C hcard
      core := hcore
      quot := hquot
      nontriv := hnontriv }

private theorem natQuot_Vk_of_card (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) (hcard : Nat.card (X.Vk 0) = 2 ^ (3 * X.n 0)) :
    NatQuot (X.L 0) (X.Vk 0) (X.Z 0) (X.n 0) := by
  have hpre := natPre_Vk (X := X) C hH hcard
  haveI : Finite ↥(X.L 0) := finite_of_le_stabilizer X.hyp (H := X.L 0) (X.L_le_Gi 0)
  have hC := two_pow_le_relIndex_relCent_Vk_zero (X := X) C hH
  have hS : IsSylowTwoOf (X.edgeSylow 0) (X.L 0) := by
    have h := X.isSylowTwoOf_edgeSylow_L 0
    simpa using h
  have hVkleL : X.Vk 0 ≤ X.L 0 :=
    ((Vk_zero_le_Q01 (X := X) C hH).trans inf_le_left).trans (X.Q_le_L 0)
  exact natQuot_of_two_pow_le (P := X.L 0) (L := X.L 0) (E := X.Vk 0) (Z := X.Z 0)
    (T := X.edgeSylow 0) (C.hyp.two_le_n 0) hpre hVkleL hS hC

private theorem isElemAbelian_Vk_even (C : X.Comm48 s r d) (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) {k : ℤ} (hk : Even k) :
    IsElemAbelian 2 (X.Vk k) := by
  obtain ⟨m, hm⟩ := hk
  have h := X.Vk_add m 0
  rw [show (0 : ℤ) + 2 * m = k by omega] at h
  rw [h]
  exact F7.isElemAbelian_conjSub (isElemAbelian_Vk (X := X) C hH)

private theorem Z0_le_Co (C : X.Comm48 s r d) : X.Z 0 ≤ X.Co := by
  obtain ⟨hZ0leZ1, -⟩ := X.s48_1 C
  have hcent : X.Z 0 ≤ Subgroup.centralizer (oTwoRes (X.L 0) : Set G) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hxL : x ∈ X.L 0 := oTwoRes_le (X.L 0) hx
    have hzC : z ∈ Subgroup.centralizer (X.L 0 : Set G) := by
      have hz' : z ∈ centerOf (X.L 0) := by
        rw [← (X.s48_0 C).2]
        exact hz
      exact (Subgroup.mem_inf.mp hz').2
    exact (Subgroup.mem_centralizer_iff.mp hzC) x hxL
  intro z hz
  exact Subgroup.mem_inf.mpr ⟨hZ0leZ1.trans X.Z_one_le_Vk_zero hz, hcent hz⟩

private theorem L0_le_normalizer_Co :
    X.L 0 ≤ Subgroup.normalizer (X.Co : Set G) :=
  CFSG.Quasithin.F7.le_normalizer_inf (X.L_le_normalizer_Vk 0)
    (CFSG.Quasithin.B6.le_normalizer_centralizer (le_normalizer_oTwoRes (X.L 0)))

private theorem Vk_le_normalizer_Co (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) :
    X.Vk 0 ≤ Subgroup.normalizer (X.Co : Set G) := by
  rw [Subgroup.le_normalizer_iff_commutator_le_left]
  have hcomm : ⁅X.Vk 0, X.Vk 0⁆ = ⊥ := by
    have h := (isElemAbelian_Vk (X := X) C hH).1
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact congrArg Subtype.val (h.is_comm.comm ⟨w, hw⟩ ⟨v, hv⟩)
  calc ⁅X.Co, X.Vk 0⁆ ≤ ⁅X.Vk 0, X.Vk 0⁆ :=
        Subgroup.commutator_mono (show X.Co ≤ X.Vk 0 from inf_le_left) le_rfl
    _ = ⊥ := hcomm
    _ ≤ X.Co := bot_le

private theorem pCoreOf_L0_eq :
    pCoreOf 2 (X.L 0) = X.Q 0 :=
  (X.hyp.isLocL2_oTwoPrime (X.vert 0)).pCoreOf_eq

private theorem oTwoRes_sup_pCoreOf_L0 (C : X.Comm48 s r d) :
    oTwoRes (X.L 0) ⊔ pCoreOf 2 (X.L 0) = X.L 0 := by
  haveI : Finite ↥(X.L 0) := finite_of_le_stabilizer X.hyp (H := X.L 0) (X.L_le_Gi 0)
  have hqL : IsL2Quot (X.n 0) (oTwoQuot ↥(X.L 0)) :=
    (X.hyp.isLocL2_oTwoPrime (X.vert 0)).quot
  have hq : IsL2Quot (X.n 0) (oTwoQuot ↥(⊤ : Subgroup ↥(X.L 0))) := by
    obtain ⟨eL⟩ := hqL
    exact ⟨(CFSG.Quasithin.F112R.oTwoQuotCongr Subgroup.topEquiv).trans eL⟩
  have hsup := CFSG.Quasithin.F112R.St84.f112sl_oTwoRes_sup_pCoreOf
    (H := ↥(X.L 0)) (L := ⊤) (n := X.n 0) (C.hyp.two_le_n 0) hq
  have hmap := congrArg (Subgroup.map (X.L 0).subtype) hsup
  rw [Subgroup.map_sup, Subgroup.map_top, Subgroup.range_subtype] at hmap
  have ho2 : Subgroup.map (X.L 0).subtype
      (oTwoRes (⊤ : Subgroup ↥(X.L 0))) = oTwoRes (X.L 0) := by
    rw [← oTwoRes_map (X.L 0).subtype (Subgroup.subtype_injective _) ⊤, Subgroup.map_top,
      Subgroup.range_subtype]
  have hpc : Subgroup.map (X.L 0).subtype
      (pCoreOf 2 (⊤ : Subgroup ↥(X.L 0))) = pCoreOf 2 (X.L 0) := by
    rw [← Subgroup.subgroupOf_self (H := X.L 0)]
    exact CFSG.Quasithin.H13.map_pCoreOf_subgroupOf (le_refl (X.L 0))
  rw [ho2, hpc] at hmap
  exact hmap

private theorem K_le_normalizer_oTwoRes :
    X.K ≤ Subgroup.normalizer (oTwoRes (X.L 0) : Set G) := by
  intro k hk
  have hLN : X.Gi 0 ≤ Subgroup.normalizer (X.L 0 : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (X.L_le_Gi 0)).mp
      (X.hyp.isLocL2_oTwoPrime (X.vert 0)).normal
  rw [mem_normalizer_iff_conjSub]
  rw [conjSub_oTwoRes]
  have hL : conjSub k (X.L 0) = X.L 0 :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hLN (X.K_le_Gi 0 hk))
  rw [hL]

private theorem K_le_normalizer_Vk (C : X.Comm48 s r d) :
    X.K ≤ Subgroup.normalizer (X.Vk 0 : Set G) := by
  intro k hk
  rw [mem_normalizer_iff_conjSub]
  rw [Vk_eq_sup_R (X := X) C]
  rw [conjSub_sup, conjSub_sup]
  have hR : conjSub k (X.R48 d) = X.R48 d := by
    rw [Setup.R48, ← conjSub_commutator k (X.Z (-1)) (X.Z ((d : ℤ) + 1)),
      X.Z_normal (-1) k (X.K_le_Gi (-1) hk),
      X.Z_normal ((d : ℤ) + 1) k (X.K_le_Gi ((d : ℤ) + 1) hk)]
  have hZ1 : conjSub k (X.Z 1) = X.Z 1 := X.Z_normal 1 k (X.K_le_Gi 1 hk)
  have hZm : conjSub k (X.Z (-1)) = X.Z (-1) := X.Z_normal (-1) k (X.K_le_Gi (-1) hk)
  rw [hR, hZ1, hZm]

private theorem K_le_normalizer_Co (C : X.Comm48 s r d) :
    X.K ≤ Subgroup.normalizer (X.Co : Set G) :=
  CFSG.Quasithin.F7.le_normalizer_inf (K_le_normalizer_Vk (X := X) C)
    (CFSG.Quasithin.B6.le_normalizer_centralizer (K_le_normalizer_oTwoRes (X := X)))

private theorem Z0_le_Zneg1 (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) : X.Z 0 ≤ X.Z (-1) := by
  have h := X.Z_eq_sup_of_odd C hH (j := -1) (by norm_num)
  rw [h]
  exact le_sup_right

private theorem even_pred (C : X.Comm48 s r d) : Even ((d : ℤ) - 1) := by
  obtain ⟨k, hk⟩ := C.even
  exact ⟨(k : ℤ) - 1, by omega⟩

private theorem Zb_le_Vk_pred (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) :
    X.Z ((d : ℤ) + 1) ≤ X.Vk ((d : ℤ) - 1) := by
  obtain ⟨k, hk⟩ := C.even
  have hbodd : Odd ((d : ℤ) + 1 - 1) := by
    refine ⟨(k : ℤ) - 1, ?_⟩
    omega
  have hZsup : X.Z ((d : ℤ) + 1 - 1) =
      X.Z ((d : ℤ) + 1 - 1 - 1) ⊔ X.Z ((d : ℤ) + 1) := by
    have h := X.Z_eq_sup_of_odd C hH hbodd
    rw [show ((d : ℤ) + 1 - 1) + 1 = (d : ℤ) + 1 by ring] at h
    simpa using h
  have hZb_le : X.Z ((d : ℤ) + 1) ≤ X.Z ((d : ℤ) + 1 - 1) := by
    rw [hZsup]
    exact le_sup_right
  have hZVk : X.Z (((d : ℤ) - 1) + 1) ≤ X.Vk ((d : ℤ) - 1) := by
    have h := le_iSup₂_of_le
      (f := fun g (_ : g ∈ X.L ((d : ℤ) - 1)) => conjSub g (X.Z (((d : ℤ) - 1) + 1)))
      (1 : G) (X.L ((d : ℤ) - 1)).one_mem le_rfl
    simpa [Setup.Vk, conjSub_one] using h
  have hbm1 : ((d : ℤ) - 1) + 1 = (d : ℤ) + 1 - 1 := by ring
  rw [hbm1] at hZVk
  exact hZb_le.trans hZVk

private theorem R_le_Vk_pred (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) :
    X.R48 d ≤ X.Vk ((d : ℤ) - 1) := by
  have hdneg : X.HasB (-1) d :=
    (X.hasB_iff_of_even (i := -1) (j := 1) (by norm_num) d).mpr C.hasB
  have hZmG : X.Z (-1) ≤ X.Gi ((d : ℤ) - 1) := hdneg.Z_le_Gi (by omega)
  have hZm2 : IsPGroup 2 (X.Z (-1) : Subgroup G) :=
    (pCoreOf_isPGroup' (G := G) (X.Gi (-1))).to_le (X.Z_le_Q (-1))
  have hZmL : X.Z (-1) ≤ X.L ((d : ℤ) - 1) :=
    le_oTwoPrime_of_isPGroup hZm2 hZmG
  exact (Subgroup.commutator_mono hZmL (Zb_le_Vk_pred (X := X) C hH)).trans
    (Subgroup.le_normalizer_iff_commutator_le_right.mp
      (X.L_le_normalizer_Vk ((d : ℤ) - 1)))

private theorem comm_R_Zb (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) :
    ⁅X.R48 d, X.Z ((d : ℤ) + 1)⁆ = ⊥ := by
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro r hr
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  have hrV : r ∈ X.Vk ((d : ℤ) - 1) := R_le_Vk_pred (X := X) C hH hr
  have hzV : z ∈ X.Vk ((d : ℤ) - 1) := Zb_le_Vk_pred (X := X) C hH hz
  have hcomm := (isElemAbelian_Vk_even (X := X) C hH (even_pred (X := X) C)).1.is_comm.comm
    ⟨r, hrV⟩ ⟨z, hzV⟩
  exact (congrArg Subtype.val hcomm).symm

private theorem Z1_sup_R_le_relCent (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) :
    X.Z 1 ⊔ X.R48 d ≤ relCent (X.Vk 0) X.Co (X.edgeSylow 0) := by
  have hEZ : X.Vk 0 ≤ Subgroup.normalizer (X.Co : Set G) :=
    Vk_le_normalizer_Co (X := X) C hH
  refine sup_le ?_ ?_
  · intro z hz
    rw [mem_relCent hEZ]
    refine ⟨X.Z_one_le_Vk_zero hz, fun a ha => ?_⟩
    have hmem : ⁅z, a⁆ ∈ ⁅X.Z 1, X.edgeSylow 0⁆ :=
      Subgroup.commutator_mem_commutator hz ha
    rw [C.comm_Z1_edgeSylow hH] at hmem
    exact Z0_le_Co (X := X) C hmem
  · intro r hr
    rw [mem_relCent hEZ]
    refine ⟨R_le_Vk (X := X) C hr, fun a ha => ?_⟩
    set b : ℤ := (d : ℤ) + 1 with hbdef
    have hS : X.edgeSylow 0 = X.Q 0 ⊔ X.Z b := by
      rw [hbdef, ← (X.Z_succ_sup_Q_zero_and_inf C).1]
      exact sup_comm _ _
    have hnorm : X.Z b ≤ Subgroup.normalizer (X.Q 0 : Set G) := by
      have hZbEdge : X.Z b ≤ X.edgeSylow 0 := by
        rw [← (X.Z_succ_sup_Q_zero_and_inf C).1]
        exact le_sup_left
      exact hZbEdge.trans ((X.edgeSylow_le_L 0).trans ((X.L_le_Gi 0).trans
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 0))))
    have ha' : a ∈ (X.Q 0 ⊔ X.Z b : Subgroup G) := by rwa [← hS]
    have ha'' : a ∈ ((X.Q 0 ⊔ X.Z b : Subgroup G) : Set G) := ha'
    rw [Subgroup.coe_mul_of_right_le_normalizer_left (X.Q 0) (X.Z b) hnorm] at ha''
    obtain ⟨q, hq, z, hz, rfl⟩ := Set.mem_mul.mp ha''
    have hrq : ⁅r, q⁆ ∈ X.Co := by
      have hmem : ⁅r, q⁆ ∈ ⁅X.Vk 0, X.Q 0⁆ :=
        Subgroup.commutator_mem_commutator (R_le_Vk (X := X) C hr) hq
      rw [comm_Vk_Q0 (X := X) C hH] at hmem
      exact Z0_le_Co (X := X) C hmem
    have hrz : ⁅r, z⁆ = 1 := by
      have h := comm_R_Zb (X := X) C hH
      have hmem : ⁅r, z⁆ ∈ (⊥ : Subgroup G) := by
        have hmem' : ⁅r, z⁆ ∈ ⁅X.R48 d, X.Z b⁆ :=
          Subgroup.commutator_mem_commutator hr (by rw [hbdef]; exact hz)
        rwa [h] at hmem'
      exact Subgroup.mem_bot.mp hmem
    have heq : ⁅r, q * z⁆ = ⁅r, q⁆ := by
      rw [commutatorElement_mul_right_eq_mul_conj, hrz, mul_one]
      group
    rw [heq]
    exact hrq

private theorem relIndex_sup_R_le_two_pow (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) :
    (X.Z 1 ⊔ X.R48 d).relIndex (X.Vk 0) ≤ 2 ^ X.n 0 := by
  have hVsup : X.Vk 0 = (X.Z 1 ⊔ X.R48 d) ⊔ X.Z (-1) := by
    rw [Vk_eq_sup_R (X := X) C, sup_comm (X.R48 d) (X.Z 1)]
  have hAleV : X.Z 1 ⊔ X.R48 d ≤ X.Vk 0 := by
    rw [hVsup]
    exact le_sup_left
  have hBleV : X.Z (-1) ≤ X.Vk 0 := X.Z_neg_one_le_Vk_zero
  have hab : IsMulCommutative ↥(X.Vk 0) := (isElemAbelian_Vk (X := X) C hH).1
  have hcomm : X.Z (-1) ≤
      Subgroup.normalizer (((X.Z 1 ⊔ X.R48 d) : Subgroup G) : Set G) := by
    rw [Subgroup.le_normalizer_iff_commutator_le_left]
    have hbot : ⁅(X.Z 1 ⊔ X.R48 d), X.Z (-1)⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro a ha
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      exact (congrArg Subtype.val (hab.is_comm.comm ⟨a, hAleV ha⟩ ⟨z, hBleV hz⟩)).symm
    rw [hbot]
    exact bot_le
  have hrelEq : (X.Z 1 ⊔ X.R48 d).relIndex (X.Vk 0) =
      (X.Z 1 ⊔ X.R48 d).relIndex (X.Z (-1)) := by
    rw [hVsup, sup_comm ((X.Z 1 ⊔ X.R48 d)) (X.Z (-1))]
    exact CFSG.Quasithin.Vol2.Ch11.SecD.O8H.relIndex_sup_eq
      (A := X.Z (-1)) (B := X.Z 1 ⊔ X.R48 d) hcomm
  have hZ0leA : X.Z 0 ≤ X.Z 1 ⊔ X.R48 d := (X.s48_1 C).1.trans le_sup_left
  have hZ0leB : X.Z 0 ≤ X.Z (-1) := Z0_le_Zneg1 (X := X) C hH
  have hZ0le : X.Z 0 ≤ (X.Z 1 ⊔ X.R48 d) ⊓ X.Z (-1) := le_inf hZ0leA hZ0leB
  have hZ0rel : (X.Z 0).relIndex (X.Z (-1)) = 2 ^ X.n 0 := by
    have h := Subgroup.relIndex_mul_card (H := X.Z 0) (K := X.Z (-1))
    rw [inf_eq_left.mpr hZ0leB, card_Z0 (X := X) C, card_Zneg1 (X := X) C hH] at h
    refine Nat.mul_right_cancel ((pow_pos (by norm_num : (0 : ℕ) < 2) (X.n 0))) ?_
    show (X.Z 0).relIndex (X.Z (-1)) * 2 ^ X.n 0 = 2 ^ X.n 0 * 2 ^ X.n 0
    calc (X.Z 0).relIndex (X.Z (-1)) * 2 ^ X.n 0
        = 2 ^ (2 * X.n 0) := h
      _ = 2 ^ X.n 0 * 2 ^ X.n 0 := by
          rw [← pow_add]
          congr 1
          omega
  have hdvd : ((X.Z 1 ⊔ X.R48 d) ⊓ X.Z (-1)).relIndex (X.Z (-1)) ∣
      (X.Z 0).relIndex (X.Z (-1)) :=
    Subgroup.relIndex_dvd_of_le_left (X.Z (-1)) hZ0le
  have hle : ((X.Z 1 ⊔ X.R48 d) ⊓ X.Z (-1)).relIndex (X.Z (-1)) ≤ 2 ^ X.n 0 := by
    rw [hZ0rel] at hdvd
    exact Nat.le_of_dvd (by positivity) hdvd
  calc (X.Z 1 ⊔ X.R48 d).relIndex (X.Vk 0)
      = (X.Z 1 ⊔ X.R48 d).relIndex (X.Z (-1)) := hrelEq
    _ = ((X.Z 1 ⊔ X.R48 d) ⊓ X.Z (-1)).relIndex (X.Z (-1)) :=
          (Subgroup.inf_relIndex_right (X.Z 1 ⊔ X.R48 d) (X.Z (-1))).symm
    _ ≤ 2 ^ X.n 0 := hle

private theorem relIndex_relCent_le_two_pow (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) :
    (relCent (X.Vk 0) X.Co (X.edgeSylow 0)).relIndex (X.Vk 0) ≤ 2 ^ X.n 0 := by
  haveI : Finite ↥(X.Vk 0) := finite_of_le_stabilizer X.hyp (H := X.Vk 0)
    (((Vk_zero_le_Q01 (X := X) C hH).trans inf_le_left).trans (X.Q_le_Gi 0))
  have hKle := Z1_sup_R_le_relCent (X := X) C hH
  have hpos : (X.Z 1 ⊔ X.R48 d).relIndex (X.Vk 0) ≠ 0 := by
    intro h0
    have h := Subgroup.relIndex_mul_card (H := X.Z 1 ⊔ X.R48 d) (K := X.Vk 0)
    rw [h0] at h
    have hcard0 : Nat.card (X.Vk 0) = 0 := by simpa using h.symm
    exact Nat.card_pos.ne' hcard0
  exact (Subgroup.relIndex_le_of_le_left hKle hpos) |>.trans
    (relIndex_sup_R_le_two_pow (X := X) C hH)

private theorem K_le_normalizer_edgeSylow (i : ℤ) :
    X.K ≤ Subgroup.normalizer (X.edgeSylow i : Set G) := by
  intro k hk
  unfold Setup.edgeSylow
  exact (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2
    (X.Gi i ⊓ X.Gi (i + 1)))
    (Subgroup.mem_inf.mpr ⟨X.K_le_Gi i hk, X.K_le_Gi (i + 1) hk⟩)

private theorem conjSub_reflection_arcStab {i a : ℤ} {t : G}
    (href : ∀ m : ℤ, t • X.vert (i + m) = X.vert (i - m)) :
    conjSub t (X.arcStab a (a + 1)) = X.arcStab (2 * i - a - 1) (2 * i - a) := by
  unfold Setup.arcStab
  rw [conjSub_fixSet]
  congr 1
  ext v
  rw [Set.mem_smul_set]
  constructor
  · rintro ⟨w, ⟨j, hj, rfl⟩, rfl⟩
    refine ⟨i + (i - j), ?_, ?_⟩
    · rw [Set.mem_Icc] at hj ⊢
      omega
    · have h := href (j - i)
      rw [show i + (j - i) = j by ring, show i - (j - i) = 2 * i - j by ring] at h
      rw [h]
      congr 1
      ring
  · rintro ⟨j, hj, rfl⟩
    refine ⟨X.vert (i + (i - j)), ⟨i + (i - j), ?_, rfl⟩, ?_⟩
    · rw [Set.mem_Icc] at hj ⊢
      omega
    · have h := href (i - j)
      simpa [show i + (i - j) = 2 * i - j by ring,
        show i - (i - j) = j by ring] using h

private theorem conjSub_reflection_edgeSylow {i : ℤ} {t : G}
    (href : ∀ m : ℤ, t • X.vert (i + m) = X.vert (i - m)) :
    conjSub t (X.edgeSylow (i - 1)) = X.edgeSylow i := by
  have h1 : X.edgeSylow (i - 1) = pCoreOf 2 (X.arcStab (i - 1) ((i - 1) + 1)) := by
    rw [X.arcStab_eq_inf (by omega)]
  have h2 : X.edgeSylow i = pCoreOf 2 (X.arcStab i (i + 1)) := by
    rw [X.arcStab_eq_inf (by omega)]
  rw [h1, h2, ← pCoreOf_conjSub, conjSub_reflection_arcStab (X := X) (a := i - 1) href]
  congr 1 <;> ring

private theorem relIndex_relCent_edgeSylow_neg_one_le_two_pow (C : X.Comm48 s r d) (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) :
    (relCent (X.Vk 0) X.Co (X.edgeSylow (-1))).relIndex (X.Vk 0) ≤ 2 ^ X.n 0 := by
  obtain ⟨t, ht, htref, ht2⟩ := X.exists_reflection_oTwoRes C.hyp 0
  have htL : t ∈ X.L 0 := oTwoRes_le (X.L 0) ht.1
  have hVt : conjSub t (X.Vk 0) = X.Vk 0 :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (X.L_le_normalizer_Vk 0 htL)
  have hCt : conjSub t X.Co = X.Co :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (L0_le_normalizer_Co htL)
  have hS't : conjSub t (X.edgeSylow (-1)) = X.edgeSylow 0 := by
    simpa using conjSub_reflection_edgeSylow (X := X) (i := 0) htref
  have hSt : conjSub t (X.edgeSylow 0) = X.edgeSylow (-1) := by
    rw [← hS't, ← conjSub_mul]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp
      (K_le_normalizer_edgeSylow (X := X) (-1) (by simpa [pow_two] using ht2))
  have hrel : relCent (X.Vk 0) X.Co (X.edgeSylow (-1)) =
      conjSub t (relCent (X.Vk 0) X.Co (X.edgeSylow 0)) := by
    have hconj := conjSub_relCent t (E := X.Vk 0) (Z := X.Co)
      (A := X.edgeSylow 0) (Vk_le_normalizer_Co (X := X) C hH)
    rw [hVt, hCt, hSt] at hconj
    exact hconj.symm
  have hri : (conjSub t (relCent (X.Vk 0) X.Co (X.edgeSylow 0))).relIndex
      (conjSub t (X.Vk 0)) =
      (relCent (X.Vk 0) X.Co (X.edgeSylow 0)).relIndex (X.Vk 0) :=
    Subgroup.relIndex_map_map_of_injective (f := (MulAut.conj t).toMonoidHom) _ _
      (MulAut.conj t).injective
  rw [hrel]
  nth_rw 2 [← hVt]
  rw [hri]
  exact relIndex_relCent_le_two_pow (X := X) C hH

private theorem commutator_eq_one_of_odd (C : X.Comm48 s r d) (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2))
    {v x : G} (hv : v ∈ X.Vk 0) (hxL : x ∈ X.L 0) (hodd : Odd (orderOf x))
    (hcomm : ∀ a ∈ X.L 0, ⁅v, a⁆ ∈ X.Co) : ⁅v, x⁆ = 1 := by
  have hmemCo : ⁅v, x⁆ ∈ X.Co := hcomm x hxL
  have hmemV : ⁅v, x⁆ ∈ ⁅X.Vk 0, Subgroup.zpowers x⁆ :=
    Subgroup.commutator_mem_commutator hv (Subgroup.mem_zpowers x)
  have hxMem : x ∈ oTwoRes (X.L 0) :=
    Subgroup.subset_closure ⟨hxL, orderOf x, hodd, pow_orderOf_eq_one x⟩
  have hcentx : ⁅v, x⁆ ∈ Subgroup.centralizer (Subgroup.zpowers x : Set G) := by
    obtain ⟨-, hcC⟩ := Subgroup.mem_inf.mp hmemCo
    refine Subgroup.centralizer_le ?_ hcC
    intro y hy
    exact (Subgroup.zpowers_le).mpr hxMem hy
  have hfinx : IsOfFinOrder x :=
    isOfFinOrder_iff_pow_eq_one.mpr ⟨orderOf x, hodd.pos, pow_orderOf_eq_one x⟩
  haveI : Finite ↥(Subgroup.zpowers x) :=
    Finite.of_equiv (Fin (orderOf x)) (finEquivZPowers hfinx)
  haveI : IsMulCommutative ↥(X.Vk 0) := (isElemAbelian_Vk (X := X) C hH).1
  have hDodd : Odd (Nat.card ↥(Subgroup.zpowers x)) := by
    rw [Nat.card_zpowers]
    exact hodd
  have hDW : Subgroup.zpowers x ≤ Subgroup.normalizer (X.Vk 0 : Set G) :=
    Subgroup.zpowers_le.mpr (X.L_le_normalizer_Vk 0 hxL)
  have hbot := CFSG.Quasithin.Vol2.Ch10.SecA.commutator_inf_centralizer_eq_bot
    (W := X.Vk 0) (D := Subgroup.zpowers x)
    (fun w hw => (isElemAbelian_Vk (X := X) C hH).2 w hw) hDodd hDW
  have hmemBot : ⁅v, x⁆ ∈ (⊥ : Subgroup G) := by
    rw [← hbot]
    exact Subgroup.mem_inf.mpr ⟨hmemV, hcentx⟩
  exact Subgroup.mem_bot.mp hmemBot

private theorem relCent_Vk_Co_L0 (C : X.Comm48 s r d) (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) :
    relCent (X.Vk 0) X.Co (X.L 0) = X.Co := by
  have hEZ : X.Vk 0 ≤ Subgroup.normalizer (X.Co : Set G) :=
    Vk_le_normalizer_Co (X := X) C hH
  refine le_antisymm ?_ ?_
  · intro v hv
    obtain ⟨hvV, hcomm⟩ := (mem_relCent hEZ).mp hv
    refine Subgroup.mem_inf.mpr ⟨hvV, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hgen : oTwoRes (X.L 0) ≤ Subgroup.centralizer ({v} : Set G) := by
      rw [oTwoRes]
      refine (Subgroup.closure_le (K := Subgroup.centralizer ({v} : Set G))).mpr ?_
      rintro x ⟨hxL, m, hm, hxm⟩
      change x ∈ Subgroup.centralizer ({v} : Set G)
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hodd : Odd (orderOf x) :=
        Odd.of_dvd_nat hm (orderOf_dvd_of_pow_eq_one hxm)
      have h1 : ⁅v, x⁆ = 1 :=
        commutator_eq_one_of_odd (X := X) C hH hvV hxL hodd hcomm
      exact (commutatorElement_eq_one_iff_mul_comm.mp h1).symm
    exact Subgroup.mem_centralizer_singleton_iff.mp (hgen hx)
  · intro c hc
    obtain ⟨hcV, hcC⟩ := Subgroup.mem_inf.mp hc
    rw [mem_relCent hEZ]
    refine ⟨hcV, fun a ha => ?_⟩
    have ha' : a ∈ (oTwoRes (X.L 0) ⊔ pCoreOf 2 (X.L 0) : Subgroup G) := by
      rw [oTwoRes_sup_pCoreOf_L0 (X := X) C]
      exact ha
    have hnorm : oTwoRes (X.L 0) ≤
        Subgroup.normalizer (pCoreOf 2 (X.L 0) : Set G) :=
      (oTwoRes_le (X.L 0)).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.L 0))
    have ha'' : a ∈ ((oTwoRes (X.L 0) ⊔ pCoreOf 2 (X.L 0) : Subgroup G) : Set G) := ha'
    rw [Subgroup.coe_mul_of_left_le_normalizer_right (oTwoRes (X.L 0))
      (pCoreOf 2 (X.L 0)) hnorm] at ha''
    obtain ⟨x, hx, q, hq, rfl⟩ := Set.mem_mul.mp ha''
    have hcx : ⁅c, x⁆ = 1 := by
      have hcomm' : x * c = c * x :=
        (Subgroup.mem_centralizer_iff.mp hcC) x hx
      exact commutatorElement_eq_one_iff_mul_comm.mpr hcomm'.symm
    have hcq : ⁅c, q⁆ ∈ X.Co := by
      have hqQ : q ∈ X.Q 0 := by
        rwa [← pCoreOf_L0_eq (X := X)]
      have hmem : ⁅c, q⁆ ∈ ⁅X.Vk 0, X.Q 0⁆ :=
        Subgroup.commutator_mem_commutator hcV hqQ
      rw [comm_Vk_Q0 (X := X) C hH] at hmem
      exact Z0_le_Co (X := X) C hmem
    rw [commutatorElement_mul_right_eq_mul_conj, hcx, one_mul]
    exact (Subgroup.mem_normalizer_iff.mp
      (L0_le_normalizer_Co (oTwoRes_le (X.L 0) hx)) ⁅c, q⁆).mp hcq

private theorem not_Z_one_le_Co (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) :
    ¬ X.Z 1 ≤ X.Co := by
  intro hZ1leCo
  have hZ1leC : X.Z 1 ≤ Subgroup.centralizer (oTwoRes (X.L 0) : Set G) := by
    intro z hz
    exact (Subgroup.mem_inf.mp (hZ1leCo hz)).2
  have hO2N : oTwoRes (X.L 0) ≤ Subgroup.normalizer (X.Z 1 : Set G) :=
    (Subgroup.le_centralizer_iff.mp hZ1leC).trans
      (Subgroup.centralizer_le_normalizer _)
  have hQ0N : X.Q 0 ≤ Subgroup.normalizer (X.Z 1 : Set G) := by
    have hQ0L1 : X.Q 0 ≤ X.L 1 :=
      le_oTwoPrime_of_isPGroup (pCoreOf_isPGroup' (X.Gi 0))
        ((X.Q_le_Gi_adj 0).trans inf_le_right)
    exact hQ0L1.trans (fun l hl => Subgroup.mem_normalizer_iff_map_conj_eq.mpr
      (X.Z_normal 1 l (X.L_le_Gi 1 hl)))
  have hL0N : X.L 0 ≤ Subgroup.normalizer (X.Z 1 : Set G) := by
    rw [← oTwoRes_sup_pCoreOf_L0 (X := X) C]
    exact sup_le hO2N (by rwa [pCoreOf_L0_eq (X := X)])
  have hZ1leL0 : X.Z 1 ≤ X.L 0 :=
    (X.Z_le_Q 1).trans (le_oTwoPrime_of_isPGroup (pCoreOf_isPGroup' (X.Gi 1))
      ((X.Q_le_Gi_adj 1).trans inf_le_left))
  have hZ1leL1 : X.Z 1 ≤ X.L 1 :=
    (X.Z_le_Q 1).trans (X.Q_le_L 1)
  have hNα : ((X.Z 1).subgroupOf
      (oTwoPrime (MulAction.stabilizer G (X.vert 0)))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hZ1leL0).mpr hL0N
  have hNβ : ((X.Z 1).subgroupOf
      (oTwoPrime (MulAction.stabilizer G (X.vert 1)))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hZ1leL1).mpr
      (fun l hl => Subgroup.mem_normalizer_iff_map_conj_eq.mpr
        (X.Z_normal 1 l (X.L_le_Gi 1 hl)))
  have hbotZ1 : X.Z 1 = ⊥ :=
    eq_bot_of_normal_in_oTwoPrime X.hyp (X.adj 0) hZ1leL0 hNα hZ1leL1 hNβ
  have hcard := card_Z1 (X := X) C hH
  rw [hbotZ1] at hcard
  have hcardbot : Nat.card (⊥ : Subgroup G) = 1 := by simp
  rw [hcardbot] at hcard
  have hn0 : 2 ≤ X.n 0 := C.hyp.two_le_n 0
  have hlt : 1 < 2 ^ (2 * X.n 0) :=
    Nat.one_lt_pow (by omega) (by norm_num)
  exact (not_le_of_gt hlt) (le_of_eq hcard.symm)

private theorem Z_two_eq_pCoreOf (C : X.Comm48 s r d) :
    X.Z 2 = pCoreOf 2
      (X.arcStab (2 - ((d : ℤ) + 1)) ((2 - ((d : ℤ) + 1)) + (r : ℤ))) := by
  have hZ0 : X.Z 0 = pCoreOf 2 (X.arcStab (-((d : ℤ) + 1)) ((d : ℤ) + 1)) :=
    (X.s48_2 C).2.2.2.1
  have hZ2 : X.Z 2 = conjSub X.τ (X.Z 0) := by
    simpa using X.Z_add 1 0
  rw [hZ2, hZ0, ← pCoreOf_conjSub]
  congr 1
  have h := X.arcStab_add 1 (-((d : ℤ) + 1)) ((d : ℤ) + 1)
  rw [show X.τ ^ (1 : ℤ) = X.τ by simp] at h
  rw [← h]
  have hr : (r : ℤ) = 2 * ((d : ℤ) + 1) := by
    have := (X.s48_2 C).2.1
    exact_mod_cast this.symm
  congr 1 <;> omega

private theorem Z1_inf_Co_le_Z0_of_disjoint (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2))
    (hBbot : (X.Z 1 ⊓ X.Co) ⊓ X.Z 2 = ⊥) :
    X.Z 1 ⊓ X.Co ≤ X.Z 0 := by
  have hZ1sup : X.Z 1 = X.Z 0 ⊔ X.Z 2 := (X.s48_4' C hH).2.1
  have hZ0leZ1 : X.Z 0 ≤ X.Z 1 := (X.s48_1 C).1
  have hZ0leA : X.Z 0 ≤ X.Z 1 ⊓ X.Co :=
    le_inf hZ0leZ1 (Z0_le_Co (X := X) C)
  have hZ2leZ1 : X.Z 2 ≤ X.Z 1 := by
    rw [hZ1sup]
    exact le_sup_right
  have hZ2centZ0 : X.Z 2 ≤ Subgroup.centralizer (X.Z 0 : Set G) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hc := (X.s48_4' C hH).2.2.2.2.1.1.is_comm.comm
      (⟨y, hZ0leZ1 hy⟩ : ↥(X.Z 1)) (⟨z, hZ2leZ1 hz⟩ : ↥(X.Z 1))
    exact congrArg Subtype.val hc
  have hZ2normZ0 : X.Z 2 ≤ Subgroup.normalizer (X.Z 0 : Set G) :=
    hZ2centZ0.trans (Subgroup.centralizer_le_normalizer (X.Z 0 : Set G))
  intro a ha
  have ha' : a ∈ X.Z 0 ⊔ X.Z 2 := by
    rw [← hZ1sup]
    exact (inf_le_left : X.Z 1 ⊓ X.Co ≤ X.Z 1) ha
  obtain ⟨y, hy, z, hz, rfl⟩ :=
    (CFSG.Quasithin.F1.mem_sup_iff_exists_mul_of_normalizes hZ2normZ0).mp ha'
  have hzA : z ∈ X.Z 1 ⊓ X.Co := by
    have hzEq : z = y⁻¹ * (y * z) := by group
    rw [hzEq]
    exact (X.Z 1 ⊓ X.Co).mul_mem ((X.Z 1 ⊓ X.Co).inv_mem (hZ0leA hy)) ha
  have hzbot : z ∈ (⊥ : Subgroup G) := by
    rw [← hBbot]
    exact Subgroup.mem_inf.mpr ⟨hzA, hz⟩
  have hz1 : z = 1 := Subgroup.mem_bot.mp hzbot
  rw [hz1, mul_one]
  exact hy

private theorem Z1_inf_Co (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) :
    X.Z 1 ⊓ X.Co = X.Z 0 := by
  have hZ1sup : X.Z 1 = X.Z 0 ⊔ X.Z 2 := (X.s48_4' C hH).2.1
  have hZ0leA : X.Z 0 ≤ X.Z 1 ⊓ X.Co :=
    le_inf (X.s48_1 C).1 (Z0_le_Co (X := X) C)
  have hZ2eq : X.Z 2 = pCoreOf 2
      (X.arcStab (2 - ((d : ℤ) + 1)) ((2 - ((d : ℤ) + 1)) + (r : ℤ))) :=
    Z_two_eq_pCoreOf (X := X) C
  have hBpc : (X.Z 1 ⊓ X.Co) ⊓ X.Z 2 ≤ pCoreOf 2
      (X.arcStab (2 - ((d : ℤ) + 1)) ((2 - ((d : ℤ) + 1)) + (r : ℤ))) := by
    rw [hZ2eq]
    exact inf_le_right
  have hKinv : X.K ≤ Subgroup.normalizer (((X.Z 1 ⊓ X.Co) ⊓ X.Z 2 : Subgroup G) : Set G) := by
    intro k hk
    rw [mem_normalizer_iff_conjSub]
    rw [conjSub_inf, conjSub_inf, X.Z_normal 1 k (X.K_le_Gi 1 hk),
      mem_normalizer_iff_conjSub.mp (K_le_normalizer_Co (X := X) C hk),
      X.Z_normal 2 k (X.K_le_Gi 2 hk)]
  by_cases hBbot : (X.Z 1 ⊓ X.Co) ⊓ X.Z 2 = ⊥
  · exact le_antisymm (Z1_inf_Co_le_Z0_of_disjoint (X := X) C hH hBbot) hZ0leA
  · have hBeq : (X.Z 1 ⊓ X.Co) ⊓ X.Z 2 = pCoreOf 2
        (X.arcStab (2 - ((d : ℤ) + 1)) ((2 - ((d : ℤ) + 1)) + (r : ℤ))) :=
      X.eq_of_le_pCoreOf_arcStab_r C.hyp (U := (X.Z 1 ⊓ X.Co) ⊓ X.Z 2)
        (a := 2 - ((d : ℤ) + 1)) hKinv hBbot hBpc
    have hZ2leA : X.Z 2 ≤ X.Z 1 ⊓ X.Co := by
      rw [hZ2eq, ← hBeq]
      exact inf_le_left
    have hZ1leCo : X.Z 1 ≤ X.Co := by
      rw [hZ1sup]
      exact sup_le (hZ0leA.trans inf_le_right) (hZ2leA.trans inf_le_right)
    exact absurd hZ1leCo (not_Z_one_le_Co (X := X) C hH)

private theorem Co_relIndex_Vk (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) :
    X.Co.relIndex (X.Vk 0) = 2 ^ (2 * X.n 0) ∧
      X.Co.relIndex (relCent (X.Vk 0) X.Co (X.edgeSylow 0)) = 2 ^ X.n 0 := by
  haveI hLfin : Finite ↥(X.L 0) := finite_of_le_stabilizer X.hyp (H := X.L 0) (X.L_le_Gi 0)
  have hVleGi : X.Vk 0 ≤ X.Gi 0 :=
    (Vk_zero_le_Q01 (X := X) C hH).trans inf_le_left |>.trans (X.Q_le_Gi 0)
  haveI hVfin : Finite ↥(X.Vk 0) := finite_of_le_stabilizer X.hyp (H := X.Vk 0) hVleGi
  have hq : IsL2Quot (X.n 0) (oTwoQuot ↥(X.L 0)) :=
    (X.hyp.isLocL2_oTwoPrime (X.vert 0)).quot
  have hZE : X.Co ≤ X.Vk 0 := inf_le_left
  have hEZ : X.Vk 0 ≤ Subgroup.normalizer (X.Co : Set G) :=
    Vk_le_normalizer_Co (X := X) C hH
  have hLE : X.L 0 ≤ Subgroup.normalizer (X.Vk 0 : Set G) := X.L_le_normalizer_Vk 0
  have hLZ : X.L 0 ≤ Subgroup.normalizer (X.Co : Set G) :=
    L0_le_normalizer_Co
  have hE : IsPGroup 2 (X.Vk 0) :=
    (pCoreOf_isPGroup' (X.Gi 0)).to_le
      ((Vk_zero_le_Q01 (X := X) C hH).trans inf_le_left)
  have hcore : ⁅X.Vk 0, pCoreOf 2 (X.L 0)⁆ ≤ X.Co := by
    rw [pCoreOf_L0_eq (X := X)]
    exact (comm_Vk_Q0 (X := X) C hH).le.trans (Z0_le_Co (X := X) C)
  have hT : X.edgeSylow 0 ≤ X.L 0 := X.edgeSylow_le_L 0
  have hT' : X.edgeSylow (-1) ≤ X.L 0 := by
    refine le_oTwoPrime_of_isPGroup (X.isPGroup_edgeSylow (-1)) ?_
    exact ((X.isSylowTwoOf_edgeSylow (-1)).1.trans inf_le_right)
  have hgen : X.L 0 ≤ (X.edgeSylow 0 ⊔ X.edgeSylow (-1)) ⊔ pCoreOf 2 (X.L 0) := by
    have hLsup : X.L 0 = X.edgeSylow (-1) ⊔ X.edgeSylow 0 := by
      simpa using (X.edgeSylow_sup_edgeSylow 0).symm
    rw [hLsup, sup_comm (X.edgeSylow (-1)) (X.edgeSylow 0)]
    exact le_sup_left
  have hcent : relCent (X.Vk 0) X.Co (X.L 0) = X.Co :=
    relCent_Vk_Co_L0 (X := X) C hH
  have hne : X.Co ≠ X.Vk 0 := by
    intro hCo
    have hZ1leCo : X.Z 1 ≤ X.Co := by
      rw [hCo]; exact X.Z_one_le_Vk_zero
    have h := Z1_inf_Co (X := X) C hH
    rw [inf_eq_left.mpr hZ1leCo] at h
    have hc := card_Z1 (X := X) C hH
    rw [h, card_Z0 (X := X) C] at hc
    have hlt : 2 ^ X.n 0 < 2 ^ (2 * X.n 0) := by
      apply (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mpr
      exact n_lt_two_mul C 0
    exact (not_le_of_gt hlt) (le_of_eq hc.symm)
  have hTq : (relCent (X.Vk 0) X.Co (X.edgeSylow 0)).relIndex (X.Vk 0) ≤ 2 ^ X.n 0 :=
    relIndex_relCent_le_two_pow (X := X) C hH
  have hTq' : (relCent (X.Vk 0) X.Co (X.edgeSylow (-1))).relIndex (X.Vk 0) ≤ 2 ^ X.n 0 :=
    relIndex_relCent_edgeSylow_neg_one_le_two_pow (X := X) C hH
  exact relIndex_eq_two_pow_of_lines (L := X.L 0) (E := X.Vk 0) (Z := X.Co)
    (T := X.edgeSylow 0) (T' := X.edgeSylow (-1)) (n := X.n 0)
    (hn := by have h := C.hyp.two_le_n 0; omega)
    (hq := hq) (hZE := hZE) (hEZ := hEZ) (hLE := hLE) (hLZ := hLZ) (hE := hE)
    (hcore := hcore) (hT := hT) (hT' := hT') (hgen := hgen) (hcent := hcent)
    (hne := hne) (hTq := hTq) (hTq' := hTq')

private theorem card_Vk_zero_eq_mul_card_Co (C : X.Comm48 s r d) (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) :
    Nat.card (X.Vk 0) = 2 ^ (2 * X.n 0) * Nat.card X.Co := by
  have h := Subgroup.relIndex_mul_card (H := X.Co) (K := X.Vk 0)
  rw [(Co_relIndex_Vk (X := X) C hH).1, inf_eq_left.mpr (inf_le_left : X.Co ≤ X.Vk 0)] at h
  exact h.symm

private theorem card_sup_Z1_Co (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) :
    Nat.card (X.Z 1 ⊔ X.Co : Subgroup G) = 2 ^ X.n 0 * Nat.card X.Co := by
  have hnorm : X.Z 1 ≤ Subgroup.normalizer (X.Co : Set G) :=
    X.Z_one_le_Vk_zero.trans (Vk_le_normalizer_Co (X := X) C hH)
  have hcomm : ∀ b ∈ X.Z 1, ∀ n ∈ X.Co, b * n * b⁻¹ ∈ X.Co := by
    intro b hb n hn
    exact (Subgroup.mem_normalizer_iff.mp (hnorm hb) n).mp hn
  have h := CFSG.Timmesfeld.LocalTwoSubgroups.FrobeniusFixedSpaceBounds.card_sup_mul_card_inf
    (H := X.Z 1) (N := X.Co) hcomm
  rw [Z1_inf_Co (X := X) C hH, card_Z1 (X := X) C hH, card_Z0 (X := X) C] at h
  refine Nat.mul_right_cancel ((pow_pos (by norm_num : (0 : ℕ) < 2) (X.n 0))) ?_
  show Nat.card (X.Z 1 ⊔ X.Co : Subgroup G) * 2 ^ X.n 0 =
    (2 ^ X.n 0 * Nat.card X.Co) * 2 ^ X.n 0
  calc Nat.card (X.Z 1 ⊔ X.Co : Subgroup G) * 2 ^ X.n 0
      = 2 ^ (2 * X.n 0) * Nat.card X.Co := h
    _ = (2 ^ X.n 0 * Nat.card X.Co) * 2 ^ X.n 0 := by ring

private theorem relCent_edge_eq (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) :
    relCent (X.Vk 0) X.Co (X.edgeSylow 0) = X.Z 1 ⊔ X.Co := by
  have hVleGi : X.Vk 0 ≤ X.Gi 0 :=
    (Vk_zero_le_Q01 (X := X) C hH).trans inf_le_left |>.trans (X.Q_le_Gi 0)
  haveI hVfin : Finite ↥(X.Vk 0) := finite_of_le_stabilizer X.hyp (H := X.Vk 0) hVleGi
  haveI hCofin : Finite ↥(X.Co) :=
    Finite.of_injective (Subgroup.inclusion inf_le_left) (Subgroup.inclusion_injective _)
  obtain ⟨hrelq2, hrelq⟩ := Co_relIndex_Vk (X := X) C hH
  have hsub : X.Z 1 ⊔ X.Co ≤ relCent (X.Vk 0) X.Co (X.edgeSylow 0) :=
    sup_le ((le_sup_left : X.Z 1 ≤ X.Z 1 ⊔ X.R48 d).trans
      (Z1_sup_R_le_relCent (X := X) C hH)) (by
      intro c hc
      rw [mem_relCent (E := X.Vk 0) (Z := X.Co) (A := X.edgeSylow 0)
        (Vk_le_normalizer_Co (X := X) C hH)]
      refine ⟨(inf_le_left : X.Co ≤ X.Vk 0) hc, ?_⟩
      intro s hs
      have hconj : s * c⁻¹ * s⁻¹ ∈ X.Co :=
        (Subgroup.mem_normalizer_iff.mp
          (L0_le_normalizer_Co (X.edgeSylow_le_L 0 hs)) c⁻¹).mp
          ((X.Co).inv_mem hc)
      have hmul := (X.Co).mul_mem hc hconj
      simpa [commutatorElement_def, mul_assoc] using hmul)
  have hRelLe : relCent (X.Vk 0) X.Co (X.edgeSylow 0) ≤ X.Vk 0 := by
    intro x hx
    exact ((mem_relCent (E := X.Vk 0) (Z := X.Co) (A := X.edgeSylow 0)
      (Vk_le_normalizer_Co (X := X) C hH)).mp hx).1
  haveI hRelfin : Finite ↥(relCent (X.Vk 0) X.Co (X.edgeSylow 0)) := by
    let f : ↥(relCent (X.Vk 0) X.Co (X.edgeSylow 0)) → ↥(X.Vk 0) :=
      Subgroup.inclusion hRelLe
    exact Finite.of_injective (f := f) (Subgroup.inclusion_injective hRelLe)
  have hcardZ1C := card_sup_Z1_Co (X := X) C hH
  have hcardRel : Nat.card ↥(relCent (X.Vk 0) X.Co (X.edgeSylow 0)) =
      2 ^ X.n 0 * Nat.card X.Co := by
    have h := Subgroup.relIndex_mul_card (H := X.Co)
      (K := relCent (X.Vk 0) X.Co (X.edgeSylow 0))
    rw [hrelq] at h
    rw [inf_eq_left.mpr ((le_sup_right : X.Co ≤ X.Z 1 ⊔ X.Co).trans hsub)] at h
    exact h.symm
  have hcardle : Nat.card ↥(X.Z 1 ⊔ X.Co) ≤
      Nat.card ↥(relCent (X.Vk 0) X.Co (X.edgeSylow 0)) :=
    Nat.card_le_card_of_injective (Subgroup.inclusion hsub) (Subgroup.inclusion_injective _)
  have heqCard : Nat.card ↥(X.Z 1 ⊔ X.Co) =
      Nat.card ↥(relCent (X.Vk 0) X.Co (X.edgeSylow 0)) :=
    hcardZ1C.trans hcardRel.symm
  exact (Subgroup.eq_of_le_of_card_ge hsub (by rw [heqCard])).symm

private theorem R_le_Z1_Co (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) :
    X.R48 d ≤ X.Z 1 ⊔ X.Co := by
  have hRrel : X.R48 d ≤ relCent (X.Vk 0) X.Co (X.edgeSylow 0) :=
    (le_sup_right : X.R48 d ≤ X.Z 1 ⊔ X.R48 d).trans
      (Z1_sup_R_le_relCent (X := X) C hH)
  rwa [relCent_edge_eq (X := X) C hH] at hRrel

private theorem Vk_eq_sup_Co (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) : X.Vk 0 = X.Z 1 ⊔ X.Z (-1) ⊔ X.Co := by
  refine le_antisymm ((Vk_eq_sup_R (X := X) C).le.trans ?_)
    (sup_le (sup_le X.Z_one_le_Vk_zero X.Z_neg_one_le_Vk_zero) inf_le_left)
  exact sup_le (sup_le ((R_le_Z1_Co (X := X) C hH).trans
    (sup_le (le_sup_left.trans le_sup_left) le_sup_right)) (le_sup_left.trans le_sup_left))
    (le_sup_right.trans le_sup_left)

private theorem Z_one_sup_Z_neg_one_inf_Co (C : X.Comm48 s r d) (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) :
    (X.Z 1 ⊔ X.Z (-1)) ⊓ X.Co = X.Z 0 := by
  have hVGi : X.Vk 0 ≤ X.Gi 0 :=
    ((Vk_zero_le_Q01 (X := X) C hH).trans inf_le_left).trans (X.Q_le_Gi 0)
  haveI : Finite ↥X.Co := finite_of_le_stabilizer X.hyp (H := X.Co) (inf_le_left.trans hVGi)
  haveI : Finite ↥((X.Z 1 ⊔ X.Z (-1)) ⊓ X.Co) := finite_of_le_stabilizer X.hyp
    (H := (X.Z 1 ⊔ X.Z (-1)) ⊓ X.Co) (inf_le_right.trans (inf_le_left.trans hVGi))
  have hab := (isElemAbelian_Vk (X := X) C hH).1
  have hconj : ∀ b ∈ X.Z 1 ⊔ X.Z (-1), ∀ n ∈ X.Co, b * n * b⁻¹ ∈ X.Co := by
    intro b hb n hn
    have hbn : b * n = n * b := congrArg Subtype.val (hab.is_comm.comm
      ⟨b, sup_le X.Z_one_le_Vk_zero X.Z_neg_one_le_Vk_zero hb⟩ ⟨n, (inf_le_left : X.Co ≤ X.Vk 0) hn⟩)
    rwa [hbn, mul_inv_cancel_right]
  have h := CFSG.Timmesfeld.LocalTwoSubgroups.FrobeniusFixedSpaceBounds.card_sup_mul_card_inf
    (X.Z 1 ⊔ X.Z (-1)) X.Co hconj
  rw [← Vk_eq_sup_Co (X := X) C hH, card_Vk_zero_eq_mul_card_Co (X := X) C hH,
    card_Z1_sup_Zneg1 (X := X) C hH] at h
  have hAq : Nat.card ↥((X.Z 1 ⊔ X.Z (-1)) ⊓ X.Co) = 2 ^ X.n 0 := by
    refine Nat.mul_left_cancel (Nat.mul_pos ((pow_pos (by norm_num : (0 : ℕ) < 2) (2 * X.n 0))) (Nat.card_pos (α := ↥X.Co))) ?_
    show (2 ^ (2 * X.n 0) * Nat.card X.Co) *
          Nat.card ↥((X.Z 1 ⊔ X.Z (-1)) ⊓ X.Co)
        = (2 ^ (2 * X.n 0) * Nat.card X.Co) * 2 ^ X.n 0
    calc (2 ^ (2 * X.n 0) * Nat.card X.Co) *
          Nat.card ↥((X.Z 1 ⊔ X.Z (-1)) ⊓ X.Co)
        = 2 ^ (3 * X.n 0) * Nat.card X.Co := h
      _ = (2 ^ (2 * X.n 0) * Nat.card X.Co) * 2 ^ X.n 0 := by
          rw [show 3 * X.n 0 = 2 * X.n 0 + X.n 0 by omega, pow_add]
          ring
  have hZ0le : X.Z 0 ≤ (X.Z 1 ⊔ X.Z (-1)) ⊓ X.Co :=
    le_inf ((X.s48_1 C).1.trans le_sup_left) (Z0_le_Co (X := X) C)
  exact (Subgroup.eq_of_le_of_card_ge hZ0le (by rw [hAq, card_Z0 (X := X) C])).symm

private theorem Z_neg_one_le_Gi_of_between (C : X.Comm48 s r d) {j : ℤ}
    (hj0 : 0 ≤ j) (hjd : j ≤ (d : ℤ) - 1) : X.Z (-1) ≤ X.Gi j := by
  have hdneg : X.HasB (-1) d :=
    (X.hasB_iff_of_even (i := -1) (j := 1) (by norm_num) d).mpr C.hasB
  exact hdneg.Z_le_Gi (by omega)

private theorem Z_succ_le_Gi_of_between (C : X.Comm48 s r d) {j : ℤ}
    (hj0 : 0 ≤ j) (hjd : j ≤ (d : ℤ) - 1) : X.Z ((d : ℤ) + 1) ≤ X.Gi j := by
  obtain ⟨-, h2r, hZbQg, -, -, -, -, -⟩ := X.s48_2 C
  have hr : (r : ℤ) = 2 * ((d : ℤ) + 1) := by
    have := h2r; exact_mod_cast this.symm
  have hKA : X.K ≤ X.arcStab 0 (r : ℤ) := X.K_le_GT.trans (X.GT_le_arcStab 0 (r : ℤ))
  have hA : X.arcStab 0 (r : ℤ) ≤ X.Gi 0 ⊓ X.Gi 1 :=
    le_inf (X.arcStab_le_Gi_left (by omega)) (X.arcStab_le_Gi_left_succ (by omega))
  have hQgArc : X.Qg r ≤ X.arcStab 0 (r : ℤ) := by
    rw [show X.Qg r = X.arcStab 0 (r : ℤ) ⊓ X.edgeSylow 0 from
      (X.pCoreOf_eq_inf_edgeSylow 0 hKA hA).1]
    exact inf_le_left
  have hZbArc : X.Z ((d : ℤ) + 1) ≤ X.arcStab 0 (r : ℤ) := by
    rw [hZbQg]; exact hQgArc
  have harc : j ∈ Set.Icc (0 : ℤ) (r : ℤ) := by
    rw [Set.mem_Icc]
    constructor <;> omega
  intro z hz
  have hzfix : z ∈ Fan86.fixSet G (X.vert '' Set.Icc (0 : ℤ) (r : ℤ)) := by
    simpa [Setup.arcStab] using hZbArc hz
  exact MulAction.mem_stabilizer_iff.mpr
    ((Fan86.mem_fixSet.mp hzfix) (X.vert j) ⟨j, harc, rfl⟩)

private theorem R_le_arcStab_zero_succ (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) :
    X.R48 d ≤ X.arcStab 0 ((d : ℤ) + 1) := by
  classical
  obtain ⟨m, hm⟩ : ∃ m : ℤ, (d : ℤ) - 1 = 2 * m := by
    obtain ⟨k, hk⟩ := C.even
    exact ⟨(k : ℤ) - 1, by omega⟩
  have hVk_eq : X.Vk ((d : ℤ) - 1) = conjSub (X.τ ^ m) (X.Vk 0) := by
    have h := X.Vk_add m 0
    rwa [show (0 : ℤ) + 2 * m = (d : ℤ) - 1 by omega] at h
  have hQ0 : X.Q ((d : ℤ) - 1) = conjSub (X.τ ^ m) (X.Q 0) := by
    have h := X.Q_add m 0
    rwa [show (0 : ℤ) + 2 * m = (d : ℤ) - 1 by omega] at h
  have hQ1 : X.Q ((d : ℤ)) = conjSub (X.τ ^ m) (X.Q 1) := by
    have h := X.Q_add m 1
    rwa [show (1 : ℤ) + 2 * m = (d : ℤ) by omega] at h
  have hRVk : X.R48 d ≤ X.Vk ((d : ℤ) - 1) := R_le_Vk_pred (X := X) C hH
  have hVkQ : X.Vk ((d : ℤ) - 1) ≤ X.Q ((d : ℤ) - 1) ⊓ X.Q ((d : ℤ)) := by
    rw [hVk_eq, hQ0, hQ1, ← conjSub_inf]
    exact conjSub_mono (X.τ ^ m) (Vk_zero_le_Q01 (X := X) C hH)
  have hRQ : X.R48 d ≤ X.Q ((d : ℤ)) :=
    hRVk.trans (hVkQ.trans inf_le_right)
  have hZm_fix : ∀ j : ℤ, 0 ≤ j → j ≤ (d : ℤ) - 1 →
      X.Z (-1) ≤ X.Gi j := fun j hj0 hjd => Z_neg_one_le_Gi_of_between C hj0 hjd
  have hZb_fix : ∀ j : ℤ, 0 ≤ j → j ≤ (d : ℤ) - 1 →
      X.Z ((d : ℤ) + 1) ≤ X.Gi j := fun j hj0 hjd => Z_succ_le_Gi_of_between C hj0 hjd
  refine X.le_arcStab_of_fixSet ?_
  intro j hj x hx
  rw [Set.mem_Icc] at hj
  by_cases hle : j ≤ (d : ℤ) - 1
  ·
    exact MulAction.mem_stabilizer_iff.mp
      (Subgroup.commutator_le_of_le (hZm_fix j (by omega) hle) (hZb_fix j (by omega) hle) hx)
  ·
    have hQd : X.Q ((d : ℤ)) ≤ X.Gi j := by
      have h1 : j = (d : ℤ) - 1 ∨ j = (d : ℤ) ∨ j = (d : ℤ) + 1 := by omega
      rcases h1 with rfl | rfl | rfl
      · exact (X.Q_le_Gi_adj (d : ℤ)).trans inf_le_left
      · exact X.Q_le_Gi (d : ℤ)
      · exact (X.Q_le_Gi_adj (d : ℤ)).trans inf_le_right
    exact MulAction.mem_stabilizer_iff.mp (hQd (hRQ hx))

private theorem Z_one_le_arcStab_zero_succ (C : X.Comm48 s r d) :
    X.Z 1 ≤ X.arcStab 0 ((d : ℤ) + 1) := by
  have hd1 : 1 ≤ d := X.one_le_of_hasB C.hasB
  refine X.le_arcStab_of_fixSet ?_
  intro j hj z hz
  rw [Set.mem_Icc] at hj
  have hle : X.Z 1 ≤ X.Gi j := C.hasB.Z_le_Gi (by omega)
  exact MulAction.mem_stabilizer_iff.mp (hle hz)

private theorem Vk_eq_inf_sup_Z1_Zneg1 (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) :
    X.Vk 0 = ((X.R48 d ⊔ X.Z 1) ⊓ X.Co) ⊔ (X.Z 1 ⊔ X.Z (-1)) := by
  have hVk : X.Vk 0 = X.R48 d ⊔ X.Z 1 ⊔ X.Z (-1) := Vk_eq_sup_R (X := X) C
  have hZ1norm : X.Z 1 ≤ Subgroup.normalizer (X.Co : Set G) :=
    X.Z_one_le_Vk_zero.trans (Vk_le_normalizer_Co (X := X) C hH)
  have hDed : X.R48 d ⊔ X.Z 1 = X.Z 1 ⊔ ((X.R48 d ⊔ X.Z 1) ⊓ X.Co) :=
    CFSG.Quasithin.A3.eq_sup_inf_of_le_sup hZ1norm le_sup_right
      (sup_le (R_le_Z1_Co (X := X) C hH) le_sup_left)
  calc X.Vk 0 = (X.R48 d ⊔ X.Z 1) ⊔ X.Z (-1) := hVk
    _ = (X.Z 1 ⊔ ((X.R48 d ⊔ X.Z 1) ⊓ X.Co)) ⊔ X.Z (-1) :=
        congrArg (fun A => A ⊔ X.Z (-1)) hDed
    _ = ((X.R48 d ⊔ X.Z 1) ⊓ X.Co) ⊔ (X.Z 1 ⊔ X.Z (-1)) := by
        rw [sup_comm (X.Z 1) ((X.R48 d ⊔ X.Z 1) ⊓ X.Co), sup_assoc]

private theorem Z1_sup_Zneg1_le_normalizer_inf (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) :
    X.Z 1 ⊔ X.Z (-1) ≤
      Subgroup.normalizer (((X.R48 d ⊔ X.Z 1) ⊓ X.Co) : Subgroup G) := by
  have hV_DH := Vk_eq_inf_sup_Z1_Zneg1 (X := X) C hH
  have hDleV : ((X.R48 d ⊔ X.Z 1) ⊓ X.Co) ≤ X.Vk 0 := by
    rw [hV_DH]; exact le_sup_left
  have hHleV : X.Z 1 ⊔ X.Z (-1) ≤ X.Vk 0 := by
    rw [hV_DH]; exact le_sup_right
  have hElem := isElemAbelian_Vk (X := X) C hH
  have hcommV : ∀ a ∈ X.Vk 0, ∀ x ∈ X.Vk 0, a * x = x * a := by
    intro a ha x hx
    exact congrArg Subtype.val (hElem.1.is_comm.comm ⟨a, ha⟩ ⟨x, hx⟩)
  intro h hh
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have hxV : x ∈ X.Vk 0 := hDleV hx
    have heq : h * x * h⁻¹ = x := by
      rw [hcommV h (hHleV hh) x hxV]; group
    rwa [heq]
  · intro hx
    have hxV : x ∈ X.Vk 0 := by
      have h1 : h * x * h⁻¹ ∈ X.Vk 0 := hDleV hx
      have h2 : h⁻¹ * (h * x * h⁻¹) * h ∈ X.Vk 0 :=
        (X.Vk 0).mul_mem ((X.Vk 0).mul_mem ((X.Vk 0).inv_mem (hHleV hh)) h1)
          (hHleV hh)
      simpa [mul_assoc] using h2
    have heq : h * x * h⁻¹ = x := by
      rw [hcommV h (hHleV hh) x hxV]; group
    rwa [heq] at hx

private theorem Co_le_R_sup_Z_one (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) : X.Co ≤ X.R48 d ⊔ X.Z 1 := by
  have hInf : (X.Z 1 ⊔ X.Z (-1)) ⊓ X.Co = X.Z 0 :=
    Z_one_sup_Z_neg_one_inf_Co (X := X) C hH
  have hV_DH := Vk_eq_inf_sup_Z1_Zneg1 (X := X) C hH
  have hHnormD := Z1_sup_Zneg1_le_normalizer_inf (X := X) C hH
  have hDHmul : ((((X.R48 d ⊔ X.Z 1) ⊓ X.Co) ⊔ (X.Z 1 ⊔ X.Z (-1)) : Subgroup G) : Set G) =
      (((X.R48 d ⊔ X.Z 1) ⊓ X.Co : Subgroup G) : Set G) *
        ((X.Z 1 ⊔ X.Z (-1) : Subgroup G) : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left ((X.R48 d ⊔ X.Z 1) ⊓ X.Co)
      (X.Z 1 ⊔ X.Z (-1)) hHnormD
  intro c hc
  have hcDH : c ∈ ((X.R48 d ⊔ X.Z 1) ⊓ X.Co) ⊔ (X.Z 1 ⊔ X.Z (-1)) := by
    rw [← hV_DH]
    exact (inf_le_left : X.Co ≤ X.Vk 0) hc
  have hcset : c ∈
      ((((X.R48 d ⊔ X.Z 1) ⊓ X.Co) ⊔ (X.Z 1 ⊔ X.Z (-1)) : Subgroup G) : Set G) :=
    hcDH
  rw [hDHmul] at hcset
  obtain ⟨d0, hd0D, h1, hh1H, hdh⟩ := Set.mem_mul.mp hcset
  have hd0C : d0 ∈ X.Co :=
    (inf_le_right : ((X.R48 d ⊔ X.Z 1) ⊓ X.Co) ≤ X.Co) hd0D
  have hZ0leD : X.Z 0 ≤ ((X.R48 d ⊔ X.Z 1) ⊓ X.Co) :=
    le_inf ((X.s48_1 C).1.trans le_sup_right) (Z0_le_Co (X := X) C)
  have h1C : h1 ∈ X.Co := by
    have heq : h1 = d0⁻¹ * c := by rw [← hdh]; group
    rw [heq]
    exact (X.Co).mul_mem ((X.Co).inv_mem hd0C) hc
  have h1Z0 : h1 ∈ X.Z 0 := by
    rw [← hInf]
    exact Subgroup.mem_inf.mpr ⟨hh1H, h1C⟩
  have h1D : h1 ∈ ((X.R48 d ⊔ X.Z 1) ⊓ X.Co) := hZ0leD h1Z0
  have hcD : c ∈ ((X.R48 d ⊔ X.Z 1) ⊓ X.Co) := by
    rw [← hdh]
    exact ((X.R48 d ⊔ X.Z 1) ⊓ X.Co).mul_mem hd0D h1D
  exact (inf_le_left : ((X.R48 d ⊔ X.Z 1) ⊓ X.Co) ≤ X.R48 d ⊔ X.Z 1) hcD

private theorem Co_le_arcStab_symm (C : X.Comm48 s r d)
    (h0 : X.Co ≤ X.arcStab 0 ((d : ℤ) + 1)) :
    X.Co ≤ X.arcStab (-((d : ℤ) + 1)) ((d : ℤ) + 1) := by
  obtain ⟨t, ht, href, -⟩ := X.exists_reflection_oTwoRes C.hyp 0
  have htL : t ∈ X.L 0 := oTwoRes_le (X.L 0) ht.1
  have htN : t ∈ Subgroup.normalizer (X.Co : Set G) :=
    L0_le_normalizer_Co htL
  have hconj : conjSub t (X.Co) = X.Co := by
    simpa [conjSub] using (Subgroup.mem_normalizer_iff_map_conj_eq.mp htN)
  refine X.le_arcStab_of_fixSet ?_
  intro j hj
  rw [Set.mem_Icc] at hj
  intro c hc
  by_cases hj0 : 0 ≤ j
  · have hjI : j ∈ Set.Icc (0 : ℤ) ((d : ℤ) + 1) :=
      ⟨hj0, by omega⟩
    have hmem : c ∈ Fan86.fixSet G (X.vert '' Set.Icc (0 : ℤ) ((d : ℤ) + 1)) := by
      have h := h0 hc
      simpa only [Setup.arcStab] using h
    exact (Fan86.mem_fixSet.mp hmem) (X.vert j) ⟨j, hjI, rfl⟩
  · have hmI : -j ∈ Set.Icc (0 : ℤ) ((d : ℤ) + 1) :=
      ⟨by omega, by omega⟩
    have hc' : t⁻¹ * c * t ∈ X.Co := by
      have hmem : c ∈ conjSub t (X.Co) := by rw [hconj]; exact hc
      exact mem_conjSub.mp hmem
    have hfixc' : (t⁻¹ * c * t) • X.vert (-j) = X.vert (-j) := by
      have hmem : (t⁻¹ * c * t) ∈
          Fan86.fixSet G (X.vert '' Set.Icc (0 : ℤ) ((d : ℤ) + 1)) := by
        have h := h0 hc'
        simpa only [Setup.arcStab] using h
      exact (Fan86.mem_fixSet.mp hmem) (X.vert (-j)) ⟨-j, hmI, rfl⟩
    have htin : t⁻¹ • X.vert j = X.vert (-j) := by
      rw [inv_smul_eq_iff]
      have h := href (-j)
      simpa using h.symm
    have htj : t • X.vert (-j) = X.vert j := by
      have h := href (-j)
      simpa using h
    have hsplit : c = t * (t⁻¹ * c * t) * t⁻¹ := by group
    calc c • X.vert j
        = (t * (t⁻¹ * c * t) * t⁻¹) • X.vert j :=
            congrArg (fun x => x • X.vert j) hsplit
      _ = t • ((t⁻¹ * c * t) • (t⁻¹ • X.vert j)) := by
            rw [mul_smul (t * (t⁻¹ * c * t)) t⁻¹, mul_smul t (t⁻¹ * c * t)]
      _ = t • ((t⁻¹ * c * t) • X.vert (-j)) := by rw [htin]
      _ = t • X.vert (-j) := by rw [hfixc']
      _ = X.vert j := htj

private theorem Co_eq_Z0 (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) :
    X.Co = X.Z 0 := by
  have h2r : 2 * (d + 1) = r := (X.s48_2 C).2.1
  have h2rz : (r : ℤ) = 2 * ((d : ℤ) + 1) := by
    have h : (r : ℤ) = ((2 * (d + 1) : ℕ) : ℤ) := by exact_mod_cast h2r.symm
    simpa using h
  have hE : IsPGroup 2 (X.Vk 0) :=
    (pCoreOf_isPGroup' (X.Gi 0)).to_le ((Vk_zero_le_Q01 (X := X) C hH).trans inf_le_left)
  have hCo2 : IsPGroup 2 (X.Co : Subgroup G) := hE.to_le inf_le_left
  have hCleRZ := Co_le_R_sup_Z_one (X := X) C hH
  have hZ1arc := Z_one_le_arcStab_zero_succ (X := X) C
  have hRarc := R_le_arcStab_zero_succ (X := X) C hH
  have hC0arc0b : X.Co ≤ X.arcStab 0 ((d : ℤ) + 1) :=
    hCleRZ.trans (sup_le hRarc hZ1arc)
  have hCofix := Co_le_arcStab_symm (X := X) C hC0arc0b
  have hC0arc : X.Co ≤ X.arcStab (-((d : ℤ) + 1)) ((-((d : ℤ) + 1)) + (r : ℤ)) := by
    have he : -((d : ℤ) + 1) + (r : ℤ) = (d : ℤ) + 1 := by omega
    rw [he]
    exact hCofix
  have hCo_le_pc : X.Co ≤ pCoreOf 2
      (X.arcStab (-((d : ℤ) + 1)) ((-((d : ℤ) + 1)) + (r : ℤ))) :=
    X.le_pCoreOf_arcStab_r C.hyp (U := X.Co) (a := -((d : ℤ) + 1)) hCo2 hC0arc
  have hCo_le_Z0 : X.Co ≤ X.Z 0 := by
    have h := hCo_le_pc
    rw [show -((d : ℤ) + 1) + (r : ℤ) = (d : ℤ) + 1 by omega] at h
    rw [(X.s48_2 C).2.2.2.1]
    exact h
  exact le_antisymm hCo_le_Z0 (Z0_le_Co (X := X) C)

private theorem Vk_zero_card (C : X.Comm48 s r d) (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) :
    Nat.card (X.Vk 0) = 2 ^ (3 * X.n 0) := by
  rw [card_Vk_zero_eq_mul_card_Co (X := X) C hH, Co_eq_Z0 (X := X) C hH,
    card_Z0 (X := X) C, ← pow_add]
  congr 1
  omega

end Comm48

variable (X) in
open Comm48 in
theorem s48_8 (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) :
    X.Vk 0 = X.Z 1 ⊔ X.Z (-1) ∧ Nat.card (X.Vk 0) = 2 ^ (3 * X.n 0) ∧
      IsElemAbelian 2 (X.Vk 0) ∧ X.Vk 0 ≤ X.Q 0 ⊓ X.Q 1 ∧
      ⁅X.Vk 0, X.Q 0⁆ = X.Z 0 ∧ NatQuot (X.L 0) (X.Vk 0) (X.Z 0) (X.n 0) ∧
      X.R48 d ≤ X.Z 1 := by
  have hcard : Nat.card (X.Vk 0) = 2 ^ (3 * X.n 0) := Vk_zero_card (X := X) C hH
  haveI : Finite ↥(X.Vk 0) := finite_of_le_stabilizer X.hyp (H := X.Vk 0)
    (((Vk_zero_le_Q01 (X := X) C hH).trans inf_le_left).trans (X.Q_le_Gi 0))
  have hsup : X.Vk 0 = X.Z 1 ⊔ X.Z (-1) := by
    have hWle : X.Z 1 ⊔ X.Z (-1) ≤ X.Vk 0 :=
      sup_le X.Z_one_le_Vk_zero X.Z_neg_one_le_Vk_zero
    have hWcard : Nat.card (X.Z 1 ⊔ X.Z (-1) : Subgroup G) = 2 ^ (3 * X.n 0) :=
      card_Z1_sup_Zneg1 (X := X) C hH
    exact (Subgroup.eq_of_le_of_card_ge hWle (by rw [hcard, hWcard])).symm
  have hRle : X.R48 d ≤ X.Z 1 := by
    have h := R_le_Z1_Co (X := X) C hH
    rw [Co_eq_Z0 (X := X) C hH] at h
    rwa [sup_eq_left.mpr (X.s48_1 C).1] at h
  exact ⟨hsup, hcard, isElemAbelian_Vk (X := X) C hH,
    Vk_zero_le_Q01 (X := X) C hH, comm_Vk_Q0 (X := X) C hH,
    natQuot_Vk_of_card (X := X) C hH hcard, hRle⟩

namespace Comm48

private theorem Z_succ_centralizes_Vk_of_R_eq_bot (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) (hR : X.R48 d = ⊥) :
    X.Z ((d : ℤ) + 1) ≤ Subgroup.centralizer (X.Vk 0 : Set G) := by
  obtain ⟨hV0sup, -, -, -, -, -, -⟩ := X.s48_8 C hH
  have hRbot : ⁅X.Z (-1), X.Z ((d : ℤ) + 1)⁆ = ⊥ := by
    simpa [Setup.R48] using hR
  have hZ1cent : X.Z 1 ≤ Subgroup.centralizer (X.Z ((d : ℤ) + 1) : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp C.comm
  have hZmCent : X.Z (-1) ≤ Subgroup.centralizer (X.Z ((d : ℤ) + 1) : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hRbot
  exact Subgroup.le_centralizer_iff.mpr (by
    rw [hV0sup]
    exact sup_le hZ1cent hZmCent)

private theorem R48_ne_bot (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) : X.R48 d ≠ ⊥ := by
  obtain ⟨hV0sup, -, -, hV0Q, hV0comm, hV0nat, -⟩ := X.s48_8 C hH
  set b : ℤ := (d : ℤ) + 1 with hbdef
  have hZb_sup_Q0 : X.Z b ⊔ X.Q 0 = X.edgeSylow 0 := by
    rw [hbdef]
    exact (X.Z_succ_sup_Q_zero_and_inf C).1
  intro hR
  have hZbCentV0 := Z_succ_centralizes_Vk_of_R_eq_bot (X := X) C hH hR
  have hZb_le_edge : X.Z b ≤ X.edgeSylow 0 := by
    rw [← hZb_sup_Q0]
    exact le_sup_left
  have hZbNormQ0 : X.Z b ≤ Subgroup.normalizer (X.Q 0 : Set G) :=
    hZb_le_edge.trans ((X.edgeSylow_le_L 0).trans ((X.L_le_Gi 0).trans
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 0))))
  have hcommV0S : ⁅X.Vk 0, X.Z b ⊔ X.Q 0⁆ = X.Z 0 := by
    have h := CFSG.commutator_sup_eq_commutator_left (A := X.Q 0) (B := X.Z b)
      (U := X.Vk 0) hZbNormQ0 hZbCentV0
    rw [Subgroup.commutator_comm (X.Vk 0) (X.Z b ⊔ X.Q 0), sup_comm (X.Z b) (X.Q 0), h,
      Subgroup.commutator_comm (X.Q 0) (X.Vk 0), hV0comm]
  have hV0Q0 : X.Vk 0 ≤ X.Q 0 := fun x hx => (hV0Q hx).1
  have hV0L : X.Vk 0 ≤ X.L 0 := hV0Q0.trans (X.Q_le_L 0)
  have hV0normZ0 : X.Vk 0 ≤ Subgroup.normalizer (X.Z 0 : Set G) :=
    fun x hx => (hV0nat.normal (hV0L hx)).2
  have hV0_relCent : X.Vk 0 ≤ relCent (X.Vk 0) (X.Z 0) (X.Z b ⊔ X.Q 0) := by
    intro v hv
    rw [mem_relCent (E := X.Vk 0) (Z := X.Z 0) (A := X.Z b ⊔ X.Q 0) hV0normZ0]
    refine ⟨hv, ?_⟩
    intro s hs
    have hmem : ⁅v, s⁆ ∈ ⁅X.Vk 0, X.Z b ⊔ X.Q 0⁆ :=
      Subgroup.commutator_mem_commutator hv hs
    rwa [hcommV0S] at hmem
  have hrel_eq : relCent (X.Vk 0) (X.Z 0) (X.Z b ⊔ X.Q 0) = X.Vk 0 := by
    refine le_antisymm ?_ hV0_relCent
    intro v hv
    exact ((mem_relCent (E := X.Vk 0) (Z := X.Z 0) (A := X.Z b ⊔ X.Q 0)
      hV0normZ0).mp hv).1
  have hS_syl : IsSylowTwoOf (X.Z b ⊔ X.Q 0) (X.L 0) := by
    rw [hZb_sup_Q0]
    exact X.isSylowTwoOf_edgeSylow_L 0
  have hline := hV0nat.line (X.Z b ⊔ X.Q 0) hS_syl
  rw [hrel_eq] at hline
  have hidx := hV0nat.index
  have hlt : 2 ^ X.n 0 < 2 ^ (2 * X.n 0) := by
    apply (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mpr
    exact n_lt_two_mul C 0
  exact (ne_of_lt hlt) (hline.symm.trans hidx)

private theorem R48_le_arcStab (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) :
    X.R48 d ≤ X.arcStab (-((d : ℤ) - 1)) (2 * ((d : ℤ) - 1)) := by
  obtain ⟨hV0sup, -, -, -, -, -, hRle⟩ := X.s48_8 C hH
  have hRVk : X.R48 d ≤ X.Vk ((d : ℤ) - 1) := R_le_Vk_pred (X := X) C hH
  have hRV0 : X.R48 d ≤ X.Vk 0 := by
    rw [hV0sup]
    exact hRle.trans le_sup_left
  have hdneg : X.HasB (-1) d :=
    (X.hasB_iff_of_even (i := -1) (j := 1) (by norm_num) d).mpr C.hasB
  have hV0_arc : X.Vk 0 ≤ X.arcStab (-((d : ℤ) - 1)) ((d : ℤ) - 1) := by
    rw [hV0sup]
    refine sup_le ?_ ?_
    · refine X.le_arcStab_of_fixSet ?_
      intro j hj
      rw [Set.mem_Icc] at hj
      intro z hz
      have hle : X.Z 1 ≤ X.Gi j := C.hasB.Z_le_Gi (by omega)
      exact MulAction.mem_stabilizer_iff.mp (hle hz)
    · refine X.le_arcStab_of_fixSet ?_
      intro j hj
      rw [Set.mem_Icc] at hj
      intro z hz
      have hle : X.Z (-1) ≤ X.Gi j := hdneg.Z_le_Gi (by omega)
      exact MulAction.mem_stabilizer_iff.mp (hle hz)
  obtain ⟨m, hm⟩ : ∃ m : ℤ, (d : ℤ) - 1 = 2 * m := by
    obtain ⟨k, hk⟩ := C.even
    exact ⟨(k : ℤ) - 1, by omega⟩
  have hVk_eq : X.Vk ((d : ℤ) - 1) = conjSub (X.τ ^ m) (X.Vk 0) := by
    have h := X.Vk_add m 0
    rwa [show (0 : ℤ) + 2 * m = (d : ℤ) - 1 by omega] at h
  have hVk_arc : X.Vk ((d : ℤ) - 1) ≤ X.arcStab 0 (2 * ((d : ℤ) - 1)) := by
    rw [hVk_eq]
    have h := X.arcStab_add m (-((d : ℤ) - 1)) ((d : ℤ) - 1)
    rw [show -((d : ℤ) - 1) + 2 * m = 0 by omega,
      show ((d : ℤ) - 1) + 2 * m = 2 * ((d : ℤ) - 1) by omega] at h
    rw [h]
    exact conjSub_mono (X.τ ^ m) hV0_arc
  have hRfix : X.R48 d ≤ X.arcStab (-((d : ℤ) - 1)) (2 * ((d : ℤ) - 1)) := by
    refine X.le_arcStab_of_fixSet ?_
    intro j hj
    rw [Set.mem_Icc] at hj
    intro u hu
    by_cases hjc : j ≤ (d : ℤ) - 1
    · have hj' : j ∈ Set.Icc (-((d : ℤ) - 1)) ((d : ℤ) - 1) := by
        rw [Set.mem_Icc]
        omega
      have hu' : u ∈ Fan86.fixSet G
          (X.vert '' Set.Icc (-((d : ℤ) - 1)) ((d : ℤ) - 1)) := by
        simpa [Setup.arcStab] using hV0_arc (hRV0 hu)
      exact (Fan86.mem_fixSet.mp hu') (X.vert j) ⟨j, hj', rfl⟩
    · have hj' : j ∈ Set.Icc (0 : ℤ) (2 * ((d : ℤ) - 1)) := by
        rw [Set.mem_Icc]
        omega
      have hu' : u ∈ Fan86.fixSet G
          (X.vert '' Set.Icc (0 : ℤ) (2 * ((d : ℤ) - 1))) := by
        simpa [Setup.arcStab] using hVk_arc (hRVk hu)
      exact (Fan86.mem_fixSet.mp hu') (X.vert j) ⟨j, hj', rfl⟩
  exact hRfix

end Comm48

variable (X) in
open Comm48 in
theorem s48_9 (C : X.Comm48 s r d)
    (hH : X.ZQ d ≤ X.Q ((d : ℤ) + 2)) :
    X.R48 d ≠ ⊥ ∧ (r = 8 ∨ r = 12) := by
  have hd3 : 3 ≤ d := C.three_le_d hH
  obtain ⟨-, -, -, -, -, -, hRle⟩ := X.s48_8 C hH
  have hRne := R48_ne_bot (X := X) C hH
  have hRfix := R48_le_arcStab (X := X) C hH
  have hR2 : IsPGroup 2 (X.R48 d : Subgroup G) :=
    ((pCoreOf_isPGroup' (X.Gi 1)).to_le (X.Z_le_Q 1)).to_le hRle
  have hcast : ((3 * (d - 1) : ℕ) : ℤ) = 3 * ((d : ℤ) - 1) := by
    rw [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ d)]
    norm_num
  have hfix' : X.R48 d ≤ X.arcStab (-((d : ℤ) - 1))
      ((-((d : ℤ) - 1)) + ((3 * (d - 1) : ℕ) : ℤ)) := by
    have he : (-((d : ℤ) - 1)) + ((3 * (d - 1) : ℕ) : ℤ) =
        2 * ((d : ℤ) - 1) := by
      rw [hcast]
      ring
    rw [he]
    exact hRfix
  have hdle : d ≤ 5 := by
    have hk := X.le_r_of_fixes C.hyp hR2 hRne hfix'
    have h2r : 2 * (d + 1) = r := (X.s48_2 C).2.1
    have hkz : (3 * ((d : ℤ) - 1)) ≤ (r : ℤ) := by
      have hk' : ((3 * (d - 1) : ℕ) : ℤ) ≤ (r : ℤ) := by exact_mod_cast hk
      rwa [hcast] at hk'
    have h2rz : (r : ℤ) = 2 * ((d : ℤ) + 1) := by
      exact_mod_cast h2r.symm
    omega
  have hd35 : d = 3 ∨ d = 5 := by
    obtain ⟨k, hk⟩ := C.even
    have hk' : d = 2 * (k - 1) + 1 := by omega
    omega
  have hcases : r = 8 ∨ r = 12 := by
    have h2r : 2 * (d + 1) = r := (X.s48_2 C).2.1
    rcases hd35 with rfl | rfl
    · left
      omega
    · right
      omega
  exact ⟨hRne, hcases⟩

end Setup

end CFSG.Quasithin.St84

end
