module

public import CFSG.LocalAnalysis.StandardType.GGTorusMaxSieveDefs
public import CFSG.LocalAnalysis.EvenSmallLie.CatalogOrdersLie
public import CFSG.HardMathSupport.Solomon.Coordinator.I14_20LieOrd
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LieType.Chevalley.RootCommutator
public import CFSG.LieType.Steinberg.Classical.SpinFrame
public import CFSG.LieType.Steinberg.Exceptional.E6E7
public import CFSG.LieType.Steinberg.Families
public import CFSG.LieType.Steinberg.G2
public import CFSG.LieType.Universal.Spin.Generation
public import CFSG.LieType.Universal.Spin.OddCT
public import CFSG.LieType.Universal.Spin.PlusCT
public import CFSG.LieType.Universal.Spin.Structure
public import CFSG.LieType.Universal.SpinOmega
public import CFSG.LieType.Universal.Unitary
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.LocalAnalysis.SectionRank.ClassicalOdd
public import CFSG.LocalAnalysis.SectionRank.EvenCover.LinearStep
public import CFSG.LocalAnalysis.SectionRank.SporadicCover
public import CFSG.Sporadic.M23.M23Group
public import CFSG.Sporadic.Th.F2Spec
public import TauCeti.LinearAlgebra.CliffordAlgebra.Monomials

public section

namespace CFSG.StandardType.FrameRoute

open CFSG.EvenSmallLie.CatalogOrders CFSG.Open

@[expose] def tmMin : StatedLieTag → ℕ
  | .PSL => 2
  | .PSU => 3
  | .PSp => 1
  | .POmegaOdd => 1
  | .POmegaPlus => 4
  | .POmegaMinus => 4
  | _ => 0

theorem tmExp_dvd {t : StatedLieTag} {n : ℕ} (hn : tmMin t ≤ n) (q : ℕ) :
    q ^ lieExp t n ∣ lieOrd t n q := by
  cases t <;> simp only [tmMin, lieExp, lieOrd] at hn ⊢
  · exact pow_dvd_ordA hn q
  · exact pow_dvd_ordTwistedA (by omega) q
  · exact pow_dvd_ordBC (by omega) q
  · exact pow_dvd_ordBC (by omega) q
  · exact pow_dvd_ordD n q
  · exact pow_dvd_ordTwistedD n q
  · unfold ordG2; simp only [mul_assoc]; exact dvd_mul_right _ _
  · unfold ordF4; simp only [mul_assoc]; exact dvd_mul_right _ _
  · exact pow_dvd_ordE6 q
  · exact pow_dvd_ordE7 q
  · unfold ordE8; simp only [mul_assoc]; exact dvd_mul_right _ _
  · exact pow_dvd_ordTwistedE6 q
  · unfold ordTrialityD4; simp only [mul_assoc]; exact dvd_mul_right _ _
  · unfold ordSuzuki; simp only [mul_assoc]; exact dvd_mul_right _ _
  · unfold ordRee; simp only [mul_assoc]; exact dvd_mul_right _ _
  · exact dvd_zero _
  · exact dvd_zero _

theorem tm_one_le_lieExp {t : StatedLieTag} (ht : t ∈ searchTags) {n : ℕ} (hn : tmMin t ≤ n) :
    1 ≤ lieExp t n := by
  cases t <;> simp only [tmMin, lieExp, searchTags] at hn ht ⊢
  · have h1 : 1 ≤ n - 1 := by omega
    have h2 : 2 ≤ n := by omega
    have hm : 1 * 2 ≤ (n - 1) * n := Nat.mul_le_mul h1 h2
    rw [Nat.one_le_div_iff (by norm_num : 0 < 2)]
    omega
  · have h1 : 1 ≤ n - 1 := by omega
    have h2 : 2 ≤ n := by omega
    have hm : 1 * 2 ≤ (n - 1) * n := Nat.mul_le_mul h1 h2
    rw [Nat.one_le_div_iff (by norm_num : 0 < 2)]
    omega
  · exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  · exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  · have h1 : 1 ≤ n := by omega
    have h2 : 1 ≤ n - 1 := by omega
    have hm : 1 * 1 ≤ n * (n - 1) := Nat.mul_le_mul h1 h2
    omega
  · have h1 : 1 ≤ n := by omega
    have h2 : 1 ≤ n - 1 := by omega
    have hm : 1 * 1 ≤ n * (n - 1) := Nat.mul_le_mul h1 h2
    omega
  all_goals first | omega | exact absurd ht (by decide)

@[expose] def tmSearchOn (ns : List ℕ) (tags : List StatedLieTag) (ps : List ℕ) (N : ℕ)
    (C : StatedLieTag → ℕ → ℕ → ℕ → ℕ → Bool) : Bool :=
  ps.all fun p =>
    tags.all fun t =>
      ns.all fun n =>
        (List.range (Nat.log p N / lieExp t n + 1)).all fun f =>
          !(decide (tmMin t ≤ n) && decide (lieExp t n ≤ Nat.log p N) &&
              lieAdm t p (f + 1) && N % lieOrd t n (p ^ (f + 1)) == 0) ||
            C t n p (f + 1) (lieOrd t n (p ^ (f + 1)))

@[expose] def tmSearch (ns : List ℕ) (ps : List ℕ) (N : ℕ)
    (C : StatedLieTag → ℕ → ℕ → ℕ → ℕ → Bool) : Bool :=
  tmSearchOn ns searchTags ps N C

theorem tmList_all_and {α : Type} (l : List α) (p q : α → Bool) :
    (l.all fun a => p a && q a) = (l.all p && l.all q) := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.all_cons, List.all_cons, List.all_cons, ih]; ac_rfl

theorem tmSearchOn_append (ns : List ℕ) (l₁ l₂ : List StatedLieTag) (ps : List ℕ) (N : ℕ)
    (C : StatedLieTag → ℕ → ℕ → ℕ → ℕ → Bool) :
    tmSearchOn ns (l₁ ++ l₂) ps N C = (tmSearchOn ns l₁ ps N C && tmSearchOn ns l₂ ps N C) := by
  unfold tmSearchOn
  simp only [List.all_append]
  exact tmList_all_and ps _ _

theorem tmSearchOn_ns_append (ns₁ ns₂ : List ℕ) (tags : List StatedLieTag) (ps : List ℕ) (N : ℕ)
    (C : StatedLieTag → ℕ → ℕ → ℕ → ℕ → Bool) :
    tmSearchOn (ns₁ ++ ns₂) tags ps N C =
      (tmSearchOn ns₁ tags ps N C && tmSearchOn ns₂ tags ps N C) := by
  unfold tmSearchOn
  simp only [List.all_append]
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.all_cons, ih]
    rw [tmList_all_and]
    ac_rfl

theorem tmSearchOn_single_tags {tags : List StatedLieTag} {ns : List ℕ} {ps : List ℕ} {N : ℕ}
    {C : StatedLieTag → ℕ → ℕ → ℕ → ℕ → Bool}
    (h : ∀ t ∈ tags, tmSearchOn ns [t] ps N C = true) : tmSearchOn ns tags ps N C = true := by
  induction tags with
  | nil => simp [tmSearchOn]
  | cons t tags ih =>
    change tmSearchOn ns ([t] ++ tags) ps N C = true
    rw [tmSearchOn_append]
    exact (Bool.and_eq_true ..).mpr ⟨h t (by simp),
      ih (fun u hu => h u (by simp [hu]))⟩

theorem tmSearchOn_single_ns {ns : List ℕ} {tags : List StatedLieTag} {ps : List ℕ} {N : ℕ}
    {C : StatedLieTag → ℕ → ℕ → ℕ → ℕ → Bool}
    (h : ∀ n ∈ ns, tmSearchOn [n] tags ps N C = true) : tmSearchOn ns tags ps N C = true := by
  induction ns with
  | nil => simp [tmSearchOn]
  | cons n ns ih =>
    change tmSearchOn ([n] ++ ns) tags ps N C = true
    rw [tmSearchOn_ns_append]
    exact (Bool.and_eq_true ..).mpr ⟨h n (by simp),
      ih (fun m hm => h m (by simp [hm]))⟩

theorem tmSearch_sound {ns : List ℕ} {ps : List ℕ} {N : ℕ} (hN : N ≠ 0)
    (hps : ∀ p : ℕ, p.Prime → p ∣ N → p ∈ ps)
    {C : StatedLieTag → ℕ → ℕ → ℕ → ℕ → Bool} (hS : tmSearch ns ps N C = true)
    {t : StatedLieTag} (ht : t ∈ searchTags) {n p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    (hn : tmMin t ≤ n) (hnmem : n ∈ ns) (hadm : lieAdm t p f = true)
    (hd : lieOrd t n (p ^ f) ∣ N) : C t n p f (lieOrd t n (p ^ f)) = true := by
  have hq : 2 ≤ p ^ f := hp.two_le.trans (Nat.le_self_pow (by omega) p)
  have hqd : (p ^ f) ^ lieExp t n ∣ N :=
    (pow_dvd_pow_of_dvd (dvd_refl _) _).trans ((tmExp_dvd hn _).trans hd)
  have he : 1 ≤ lieExp t n := tm_one_le_lieExp ht hn
  have hpN : p ∣ N := (dvd_pow_self p (by omega : f ≠ 0)).trans
    ((dvd_pow_self (p ^ f) (by omega : lieExp t n ≠ 0)).trans hqd)
  have hpmem : p ∈ ps := hps p hp hpN
  have hpow : p ^ (f * lieExp t n) ∣ N := by rw [pow_mul]; exact hqd
  have hle : p ^ (f * lieExp t n) ≤ N := Nat.le_of_dvd (Nat.pos_of_ne_zero hN) hpow
  have hlog : f * lieExp t n ≤ Nat.log p N := Nat.le_log_of_pow_le hp.one_lt hle
  have hdiv : f ≤ Nat.log p N / lieExp t n :=
    Nat.le_div_iff_mul_le (by omega) |>.2 (by simpa [mul_comm] using hlog)
  have hLle : lieExp t n ≤ Nat.log p N := (Nat.le_mul_of_pos_left _ hf).trans hlog
  unfold tmSearch tmSearchOn at hS
  rw [List.all_eq_true] at hS
  have h1 := hS p hpmem
  rw [List.all_eq_true] at h1
  have h2 := h1 t ht
  rw [List.all_eq_true] at h2
  have h3 := h2 n hnmem
  rw [List.all_eq_true] at h3
  have h4 := h3 (f - 1) (List.mem_range.2 (by omega))
  rw [Nat.sub_add_cancel hf] at h4
  have hg : (decide (tmMin t ≤ n) && decide (lieExp t n ≤ Nat.log p N) && lieAdm t p f &&
      N % lieOrd t n (p ^ f) == 0) = true := by
    simp [hn, hLle, hadm, Nat.mod_eq_zero_of_dvd hd]
  rw [hg] at h4
  simpa using h4

@[expose] def tmTag : TauCeti.LieTypeIndex → StatedLieTag
  | .A _ _ => .PSL
  | .twistedA _ _ => .PSU
  | .B _ _ => .POmegaOdd
  | .C _ _ => .PSp
  | .D _ _ => .POmegaPlus
  | .twistedD _ _ => .POmegaMinus
  | .E6 _ => .E6
  | .E7 _ => .E7
  | .E8 _ => .E8
  | .F4 _ => .F4
  | .G2 _ => .G2
  | .twistedE6 _ => .twistedE6
  | .trialityD4 _ => .trialityD4
  | .suzuki _ => .twistedB2
  | .reeG2 _ => .twistedG2
  | .reeF4 _ => .twistedF4
  | .tits => .Tits

@[expose] def tmRank : TauCeti.LieTypeIndex → ℕ
  | .A n _ => n + 1
  | .twistedA n _ => n + 1
  | .B n _ => n
  | .C n _ => n
  | .D n _ => n
  | .twistedD n _ => n
  | _ => 0

@[expose] def tmChar : TauCeti.LieTypeIndex → ℕ
  | .A _ q => q.p
  | .twistedA _ q => q.p
  | .B _ q => q.p
  | .C _ q => q.p
  | .D _ q => q.p
  | .twistedD _ q => q.p
  | .E6 q => q.p
  | .E7 q => q.p
  | .E8 q => q.p
  | .F4 q => q.p
  | .G2 q => q.p
  | .twistedE6 q => q.p
  | .trialityD4 q => q.p
  | .suzuki _ => 2
  | .reeG2 _ => 3
  | .reeF4 _ => 2
  | .tits => 2

@[expose] def tmDeg : TauCeti.LieTypeIndex → ℕ
  | .A _ q => q.exponent
  | .twistedA _ q => q.exponent
  | .B _ q => q.exponent
  | .C _ q => q.exponent
  | .D _ q => q.exponent
  | .twistedD _ q => q.exponent
  | .E6 q => q.exponent
  | .E7 q => q.exponent
  | .E8 q => q.exponent
  | .F4 q => q.exponent
  | .G2 q => q.exponent
  | .twistedE6 q => q.exponent
  | .trialityD4 q => q.exponent
  | .suzuki m => 2 * m + 1
  | .reeG2 m => 2 * m + 1
  | .reeF4 m => 2 * m + 1
  | .tits => 1

@[expose] def tmOutTag (t : StatedLieTag) (n p f : ℕ) : ℕ :=
  let q := p ^ f
  match t with
  | .PSL => Nat.gcd n (q - 1) * f * (if n = 2 then 1 else 2)
  | .PSU => 2 * Nat.gcd n (q + 1) * f
  | .POmegaOdd => Nat.gcd 2 (q - 1) * f * (if n = 2 ∧ p = 2 then 2 else 1)
  | .PSp => Nat.gcd 2 (q - 1) * f
  | .POmegaPlus => Nat.gcd 4 (q ^ n - 1) * f * (if n = 4 then 6 else 2)
  | .POmegaMinus => Nat.gcd 4 (q ^ n + 1) * f * 2
  | .E6 => 2 * Nat.gcd 3 (q - 1) * f
  | .E7 => Nat.gcd 2 (q - 1) * f
  | .E8 => f
  | .F4 => f * (if p = 2 then 2 else 1)
  | .G2 => f * (if p = 3 then 2 else 1)
  | .twistedE6 => 2 * Nat.gcd 3 (q + 1) * f
  | .trialityD4 => 3 * f
  | .twistedB2 => 2 * ((f - 1) / 2) + 1
  | .twistedG2 => 2 * ((f - 1) / 2) + 1
  | .twistedF4 => 2 * ((f - 1) / 2) + 1
  | .Tits => 2

@[expose] def tmIsTarget7 (t : StatedLieTag) (n p f : ℕ) : Bool :=
  (t == .PSU) && (n == 9) && (p == 2) && (f == 1)

@[expose] def tmIsTarget8 (t : StatedLieTag) (n p f : ℕ) : Bool :=
  ((t == .PSU) && (n == 10) && (p == 2) && (f == 1)) ||
    ((t == .POmegaPlus) && (n == 4) && (p == 3) && (f == 1))

end CFSG.StandardType.FrameRoute

end
