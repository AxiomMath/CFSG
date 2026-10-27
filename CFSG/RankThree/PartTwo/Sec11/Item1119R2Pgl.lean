module

public import CFSG.RankThree.PartTwo.Sec11.Item1119R2Core
public import CFSG.RankThree.PartTwo.Sec11.Item1119R2Lie
import CFSG.RankThree.PartTwo.Sec13.Item136PGL

public section

namespace CFSG.RankThree.PartTwo.Sec11.Item1119R2

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.RankThreeEven (projImage projSL projSU)
open CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly.LowTwoRank
open Matrix

variable {G : Type} [Group G] [Finite G]

theorem toYA_central {a : G} {Y A : Subgroup G} (hAC : A ≤ Subgroup.centralizer ({a} : Set G))
    (haA : a ∈ A) (q : sec11YA a Y A) :
    toYA a Y A hAC ⟨a, haA⟩ * q = q * toYA a Y A hAC ⟨a, haA⟩ := by
  obtain ⟨c', hc'⟩ := QuotientGroup.mk_surjective q.1
  apply Subtype.ext
  show ((toYA a Y A hAC ⟨a, haA⟩ : sec11YA a Y A) :
      Subgroup.centralizer ({a} : Set G) ⧸
        aschbacherSolvableCore 3 (Subgroup.centralizer ({a} : Set G))) * q.1 =
    q.1 * ((toYA a Y A hAC ⟨a, haA⟩ : sec11YA a Y A) :
      Subgroup.centralizer ({a} : Set G) ⧸
        aschbacherSolvableCore 3 (Subgroup.centralizer ({a} : Set G)))
  rw [← hc', toYA, toSec_coe, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  congr 1
  apply Subtype.ext
  have h4 := c'.2
  rw [Subgroup.mem_centralizer_singleton_iff] at h4
  exact h4.symm

theorem toSec_comm {a : G} {Y A B B' : Subgroup G} (hAC : A ≤ Subgroup.centralizer ({a} : Set G))
    (hBC : B ≤ Subgroup.centralizer ({a} : Set G)) (hB : B ≤ Y ⊔ A)
    (hB'C : B' ≤ Subgroup.centralizer ({a} : Set G)) (hB' : B' ≤ Y ⊔ A) (u : B) (v : B')
    (huv : (u : G) * v = v * u) :
    toSec a Y A B hBC hB u * toSec a Y A B' hB'C hB' v =
      toSec a Y A B' hB'C hB' v * toSec a Y A B hBC hB u := by
  apply Subtype.ext
  show ((toSec a Y A B hBC hB u : sec11YA a Y A) :
      Subgroup.centralizer ({a} : Set G) ⧸
        aschbacherSolvableCore 3 (Subgroup.centralizer ({a} : Set G))) *
      ((toSec a Y A B' hB'C hB' v : sec11YA a Y A) :
      Subgroup.centralizer ({a} : Set G) ⧸
        aschbacherSolvableCore 3 (Subgroup.centralizer ({a} : Set G))) =
    ((toSec a Y A B' hB'C hB' v : sec11YA a Y A) :
      Subgroup.centralizer ({a} : Set G) ⧸
        aschbacherSolvableCore 3 (Subgroup.centralizer ({a} : Set G))) *
      ((toSec a Y A B hBC hB u : sec11YA a Y A) :
      Subgroup.centralizer ({a} : Set G) ⧸
        aschbacherSolvableCore 3 (Subgroup.centralizer ({a} : Set G)))
  rw [toSec_coe, toSec_coe, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  congr 1
  exact Subtype.ext huv

theorem pow_eq_one_of_toSec {a : G} {Y A B : Subgroup G}
    (hBC : B ≤ Subgroup.centralizer ({a} : Set G)) (hB : B ≤ Y ⊔ A) (z : B)
    (hz3 : ∃ k : ℕ, z ^ 3 ^ k = 1) (n : ℕ) (hn : toSec a Y A B hBC hB z ^ n = 1) : z ^ n = 1 := by
  obtain ⟨k, hk⟩ := hz3
  have h1 : ((Subgroup.inclusion hBC z) ^ n : Subgroup.centralizer ({a} : Set G)) ∈
      aschbacherSolvableCore 3 (Subgroup.centralizer ({a} : Set G)) := by
    have h2 := congrArg (fun m : sec11YA a Y A =>
      (m : Subgroup.centralizer ({a} : Set G) ⧸
        aschbacherSolvableCore 3 (Subgroup.centralizer ({a} : Set G)))) hn
    simp only [Subgroup.coe_pow, toSec_coe, ← QuotientGroup.mk_pow, Subgroup.coe_one] at h2
    exact (QuotientGroup.eq_one_iff _).mp h2
  have h3 : ((z : G) ^ n) ∈ sym1119Theta a := ⟨_, h1, rfl⟩
  have h4 : orderOf ((z : G) ^ n) ∣ 3 ^ k := by
    apply orderOf_dvd_of_pow_eq_one
    rw [← pow_mul, mul_comm, pow_mul]
    have : ((z : G)) ^ 3 ^ k = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    rw [this, one_pow]
  have h5 : orderOf ((z : G) ^ n) ∣ Nat.card (sym1119Theta a) := by
    have := Subgroup.orderOf_dvd_natCard (sym1119Theta a) h3
    simpa using this
  have hcop : Nat.Coprime (3 ^ k) (Nat.card (sym1119Theta a)) :=
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr
      (not_three_dvd_card_thetaG a))
  have h6 : orderOf ((z : G) ^ n) = 1 := Nat.eq_one_of_dvd_coprimes hcop h4 h5
  apply Subtype.ext
  simpa using orderOf_eq_one_iff.mp h6

open CFSG.RankThree.PartTwo.Sec11.KS11LieProof in
theorem center_projImage_glPi_eq_bot {π : Bool} {p f : ℕ} {F : Type} [Field F]
    (hF : PiField π p f F) (hq : ModThree π (p ^ f)) (hq2 : 2 < p ^ f) :
    Subgroup.center (projImage (glPi π 3 (p ^ f) F)) = ⊥ := by
  have hπ : π = false → UnitaryFieldData p f F := fun h => by subst h; exact hF.unitary
  haveI : Group.IsPerfect (projImage (slPi π 3 (p ^ f) F)) :=
    Sec13.isPerfect_projImage_slPi hF hq2
  rw [eq_bot_iff]
  intro ζ hζ
  obtain ⟨y, hyH, hy⟩ := ζ.2
  rw [Subgroup.mem_bot]
  have hy1 : y ∈ StatedScalars (Fin 3) F := by
    refine mem_statedScalars_of_comm_mod hF hq fun s hs => ?_
    rw [← mk_eq_one_iff_mem_statedScalars]
    have hs' : ProjGenLinGroup.mk s ∈ projImage (glPi π 3 (p ^ f) F) :=
      ⟨s, slPi_le_glPi hπ hs, rfl⟩
    have hc := congrArg Subtype.val (Subgroup.mem_center_iff.mp hζ ⟨ProjGenLinGroup.mk s, hs'⟩)
    have hc' : ProjGenLinGroup.mk y * ProjGenLinGroup.mk s =
        ProjGenLinGroup.mk s * ProjGenLinGroup.mk y := by
      rw [hy]
      exact hc.symm
    simp only [map_mul, map_inv]
    rw [hc', mul_inv_cancel_right, mul_inv_cancel]
  apply Subtype.ext
  show (ζ : ProjGenLinGroup (Fin 3) F) = 1
  rw [← hy]
  exact mk_eq_one_iff_mem_statedScalars.mpr hy1

open CFSG.RankThree.PartTwo.Sec11.KS11LieProof in
theorem hF_of_pgl {a c z d : G} {Y A K : Subgroup G}
    (hY : Y ∈ thetaComponentsAt 3 a) (hAC : A ≤ Subgroup.centralizer ({a} : Set G))
    (hAY : A ≤ Subgroup.normalizer (Y : Set G)) (hA : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u)
    (hA3 : ∀ u ∈ A, u ^ 3 = 1) (hAgen : A = Subgroup.closure {c, a, d})
    (hcA : c ∈ A) (haA : a ∈ A) (hdA : d ∈ A)
    (hKY : K ≤ Y) (hKc : ∀ k ∈ K, k * c = c * k) (hKp : Group.IsPerfect K) (hdK : d ∈ K)
    (hzK : z ∈ K) (hz3 : ∃ k : ℕ, z ^ 3 ^ k = 1) (hz9 : 9 ∣ orderOf z)
    {π : Bool} {p f : ℕ} {F : Type} [Field F] (hF : PiField π p f F) (hq : ModThree π (p ^ f))
    (hq2 : 2 < p ^ f)
    (e : sec11YA a Y A ≃* Multiplicative (ZMod 3) × projImage (glPi π 3 (p ^ f) F)) :
    ∀ u : A, (e (toYA a Y A hAC u)).2 ∈ _root_.commutator (projImage (glPi π 3 (p ^ f) F)) := by
  have hYC : Y ≤ Subgroup.centralizer ({a} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hY
  have hKC : K ≤ Subgroup.centralizer ({a} : Set G) := hKY.trans hYC
  have hKYA : K ≤ Y ⊔ A := hKY.trans le_sup_left
  set ψ := toYA a Y A hAC with hψ
  set ψK := toSec a Y A K hKC hKYA with hψK
  have hcomm_iff := Sec13.commutator_projImage_glPi hF hq2
  have hmemX : ∀ x : (projImage (glPi π 3 (p ^ f) F)), x ∈ _root_.commutator (projImage (glPi π 3 (p ^ f) F)) ↔
      (x : ProjGenLinGroup (Fin 3) F) ∈ projImage (slPi π 3 (p ^ f) F) := by
    intro x
    rw [hcomm_iff]
    exact Subgroup.mem_subgroupOf
  have hKcomm : ∀ k : K, ψK k ∈ _root_.commutator (sec11YA a Y A) := fun k =>
    (mem_sup_theta_iff hY hAC hAY hA hKC hKYA k).mp (Subgroup.mem_sup_left (hKY k.2))
  set κ : K →* (projImage (glPi π 3 (p ^ f) F)) := (MonoidHom.snd _ _).comp (e.toMonoidHom.comp ψK) with hκ
  have hκk : ∀ k : K, κ k = (e (ψK k)).2 := fun k => rfl
  set γ : (projImage (glPi π 3 (p ^ f) F)) := (e (ψ ⟨c, hcA⟩)).2 with hγ
  have hγ3 : γ ^ 3 = 1 := by
    have h1 : (ψ ⟨c, hcA⟩) ^ 3 = 1 := by
      rw [← map_pow]
      have : (⟨c, hcA⟩ : A) ^ 3 = 1 := Subtype.ext (by simpa using hA3 c hcA)
      rw [this, map_one]
    have h2 := congrArg (fun m => (e m).2) h1
    simpa [map_pow] using h2
  haveI := hKp
  have hJp : Group.IsPerfect κ.range :=
    Group.IsPerfect.ofSurjective (f := κ.rangeRestrict) (MonoidHom.rangeRestrict_surjective κ)
  have hξ9 : 9 ∣ orderOf (κ ⟨z, hzK⟩) := by
    refine hz9.trans ?_
    have h1 : orderOf z = orderOf (⟨z, hzK⟩ : K) := (Subgroup.orderOf_mk z hzK).symm
    rw [h1]
    apply orderOf_dvd_of_pow_eq_one
    set n := orderOf (κ ⟨z, hzK⟩) with hn
    have h2 : (κ ⟨z, hzK⟩) ^ n = 1 := pow_orderOf_eq_one _
    have h3 : e (ψK ⟨z, hzK⟩) ^ n = 1 := by
      have hz1 := ((mem_commutator_iff_of_equiv e _).mp (hKcomm ⟨z, hzK⟩)).1
      apply Prod.ext
      · simp only [Prod.pow_fst, Prod.fst_one]
        rw [hz1, one_pow]
      · simpa [hκk] using h2
    have h4 : ψK ⟨z, hzK⟩ ^ n = 1 := by
      apply e.injective
      rw [map_pow, h3, map_one]
    obtain ⟨k, hk⟩ := hz3
    exact pow_eq_one_of_toSec hKC hKYA ⟨z, hzK⟩ ⟨k, Subtype.ext (by simpa using hk)⟩ n h4
  have hγS : (γ : ProjGenLinGroup (Fin 3) F) ∈ projImage (slPi π 3 (p ^ f) F) := by
    refine mem_projImage_slPi_of_cent hF hq hq2 γ hγ3 κ.range hJp ?_ ?_ (κ ⟨z, hzK⟩)
      ⟨⟨z, hzK⟩, rfl⟩ ?_ hξ9
    · rintro _ ⟨k, rfl⟩
      exact (hmemX _).mp ((mem_commutator_iff_of_equiv e _).mp (hKcomm k)).2
    · rintro _ ⟨k, rfl⟩
      have hcomm := toSec_comm (B := A) (B' := K) hAC hAC le_sup_right hKC hKYA ⟨c, hcA⟩ k
        (hKc k k.2).symm
      have h2 := congrArg (fun m => (e m).2) hcomm
      simpa [hκk, hγ] using h2
    · obtain ⟨k, hk⟩ := hz3
      refine ⟨k, ?_⟩
      rw [← map_pow]
      have : (⟨z, hzK⟩ : K) ^ 3 ^ k = 1 := Subtype.ext (by simpa using hk)
      rw [this, map_one]
  have hγc : γ ∈ _root_.commutator (projImage (glPi π 3 (p ^ f) F)) := (hmemX γ).mpr hγS
  set χ : A →* (projImage (glPi π 3 (p ^ f) F)) := (MonoidHom.snd _ _).comp (e.toMonoidHom.comp ψ) with hχ
  set S' : Subgroup G := ((_root_.commutator (projImage (glPi π 3 (p ^ f) F))).comap χ).map A.subtype with hS'
  have hgen : Subgroup.closure ({c, a, d} : Set G) ≤ S' := by
    rw [Subgroup.closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl
    · exact ⟨⟨g, hcA⟩, hγc, rfl⟩
    · refine ⟨⟨g, haA⟩, ?_, rfl⟩
      have hcen : (e (ψ ⟨g, haA⟩)).2 ∈ Subgroup.center (projImage (glPi π 3 (p ^ f) F)) := by
        rw [Subgroup.mem_center_iff]
        intro x
        have h := congrArg e (toYA_central hAC haA (e.symm (1, x)))
        rw [map_mul, map_mul, MulEquiv.apply_symm_apply] at h
        exact (congrArg Prod.snd h).symm
      rw [center_projImage_glPi_eq_bot hF hq hq2, Subgroup.mem_bot] at hcen
      show (e (ψ ⟨g, haA⟩)).2 ∈ _root_.commutator (projImage (glPi π 3 (p ^ f) F))
      rw [hcen]
      exact one_mem _
    · refine ⟨⟨g, hdA⟩, ?_, rfl⟩
      exact ((mem_commutator_iff_of_equiv e _).mp (hKcomm ⟨g, hdK⟩)).2
  intro u
  have hu : (u : G) ∈ S' := hgen (hAgen ▸ u.2)
  obtain ⟨u', hu', hu'u⟩ := hu
  have : u' = u := Subtype.ext hu'u
  rw [this] at hu'
  exact Subgroup.mem_comap.mp hu'

end CFSG.RankThree.PartTwo.Sec11.Item1119R2
