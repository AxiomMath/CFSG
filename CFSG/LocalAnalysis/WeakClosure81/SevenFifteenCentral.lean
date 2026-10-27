module

public import CFSG.LocalAnalysis.WeakClosure81.SevenFifteenExtra
public import CFSG.LocalAnalysis.WeakClosure81.SevenFifteenMod
import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeFactorization
import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec3.IntrThm35Aux2
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open
open scoped commutatorElement

variable {G : Type*} [Group G]

private theorem zpow_eq_one_or_self_of_mul_self_eq_one {x : G} (hx : x * x = 1) (n : ℤ) :
    x ^ n = 1 ∨ x ^ n = x := by
  obtain ⟨k, hk | hk⟩ := Int.even_or_odd' n
  · left
    rw [hk, zpow_mul]
    have h2 : x ^ (2 : ℤ) = 1 := by
      rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast, pow_two, hx]
    rw [h2, one_zpow]
  · right
    rw [hk, zpow_add, zpow_one, zpow_mul]
    have h2 : x ^ (2 : ℤ) = 1 := by
      rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast, pow_two, hx]
    rw [h2, one_zpow, one_mul]

private theorem mem_normalizer_commutator_of_mem_normalizer {A B : Subgroup G} {g : G}
    (hA : g ∈ Subgroup.normalizer (A : Set G)) (hB : g ∈ Subgroup.normalizer (B : Set G)) :
    g ∈ Subgroup.normalizer ((⁅A, B⁆ : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hA hB ⊢
  rw [Subgroup.map_commutator, hA, hB]

private theorem mem_normalizer_sup_of_mem_normalizer {A B : Subgroup G} {g : G}
    (hA : g ∈ Subgroup.normalizer (A : Set G)) (hB : g ∈ Subgroup.normalizer (B : Set G)) :
    g ∈ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hA hB ⊢
  rw [Subgroup.map_sup, hA, hB]

private theorem mem_normalizer_inf_of_mem_normalizer {A B : Subgroup G} {g : G}
    (hA : g ∈ Subgroup.normalizer (A : Set G)) (hB : g ∈ Subgroup.normalizer (B : Set G)) :
    g ∈ Subgroup.normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hA hB ⊢
  intro x
  rw [Subgroup.mem_inf, Subgroup.mem_inf]
  exact ⟨fun hx => ⟨(hA x).mp hx.1, (hB x).mp hx.2⟩,
    fun hx => ⟨(hA x).mpr hx.1, (hB x).mpr hx.2⟩⟩

private theorem mem_normalizer_centralizer_of_mem_normalizer {A : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (A : Set G)) :
    g ∈ Subgroup.normalizer (Subgroup.centralizer (A : Set G)) := by
  rw [Subgroup.mem_normalizer_iff] at hg ⊢
  intro t
  constructor
  · intro ht
    rw [Subgroup.mem_centralizer_iff] at ht ⊢
    intro a ha
    have hga : g⁻¹ * a * g ∈ A := (hg (g⁻¹ * a * g)).mpr (by
      have h : g * (g⁻¹ * a * g) * g⁻¹ = a := by group
      rw [h]; exact ha)
    have hta : (g⁻¹ * a * g) * t = t * (g⁻¹ * a * g) := ht _ hga
    calc a * (g * t * g⁻¹) = g * ((g⁻¹ * a * g) * t) * g⁻¹ := by group
      _ = g * (t * (g⁻¹ * a * g)) * g⁻¹ := by rw [hta]
      _ = (g * t * g⁻¹) * a := by group
  · intro ht
    rw [Subgroup.mem_centralizer_iff] at ht ⊢
    intro a ha
    have hga : g * a * g⁻¹ ∈ A := (hg a).mp ha
    have hta : (g * a * g⁻¹) * (g * t * g⁻¹) = (g * t * g⁻¹) * (g * a * g⁻¹) :=
      ht _ hga
    calc a * t = g⁻¹ * ((g * a * g⁻¹) * (g * t * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * t * g⁻¹) * (g * a * g⁻¹)) * g := by rw [hta]
      _ = t * a := by group

private theorem mem_normalizer_centralizer_singleton_of_mem_centralizer {b t : G}
    (ht : t ∈ Subgroup.centralizer ({b} : Set G)) :
    t ∈ Subgroup.normalizer (Subgroup.centralizer ({b} : Set G)) := by
  have htzn : t ∈ Subgroup.normalizer (Subgroup.zpowers b : Set G) := by
    have htcent : t ∈ Subgroup.centralizer (Subgroup.zpowers b : Set G) := by
      rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
      exact ht
    exact Subgroup.centralizer_le_normalizer _ htcent
  have h := mem_normalizer_centralizer_of_mem_normalizer htzn
  rwa [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure] at h

private theorem mem_normalizer_of_conj_mem {M : Subgroup G} {v : G} (hv : v * v = 1)
    (h : ∀ a ∈ M, v * a * v⁻¹ ∈ M) : v ∈ Subgroup.normalizer (M : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro a
  constructor
  · exact h a
  · intro ha
    have h2 : v * (v * a * v⁻¹) * v⁻¹ ∈ M := h (v * a * v⁻¹) ha
    have haeq : a = v * (v * a * v⁻¹) * v⁻¹ := by
      have hv' : v⁻¹ * v⁻¹ = 1 := by rw [← mul_inv_rev, hv, inv_one]
      calc a = (v * v) * a * (v⁻¹ * v⁻¹) := by rw [hv, hv']; group
        _ = v * (v * a * v⁻¹) * v⁻¹ := by group
    rw [haeq]
    exact h2

private theorem mem_normalizer_of_conj_mem' {M : Subgroup G} {v : G}
    (h1 : ∀ a ∈ M, v * a * v⁻¹ ∈ M) (h2 : ∀ a ∈ M, v⁻¹ * a * v ∈ M) :
    v ∈ Subgroup.normalizer (M : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro a
  constructor
  · exact h1 a
  · intro ha
    have h := h2 (v * a * v⁻¹) ha
    have haeq : a = v⁻¹ * (v * a * v⁻¹) * v := by group
    rw [haeq]
    exact h

theorem commutator_closure_le {I T : Subgroup G} {S : Set G}
    (hS : ∀ s ∈ S, s ∈ Subgroup.normalizer (T : Set G) ∧ ∀ a ∈ I, ⁅a, s⁆ ∈ T) :
    ⁅I, Subgroup.closure S⁆ ≤ T := by
  rw [Subgroup.commutator_le]
  intro a ha k hk
  have hmain : ∀ k ∈ Subgroup.closure S,
      k ∈ Subgroup.normalizer (T : Set G) ∧ ∀ a ∈ I, ⁅a, k⁆ ∈ T := by
    intro k hk
    induction hk using Subgroup.closure_induction with
    | mem s hs => exact hS s hs
    | one =>
        refine ⟨(Subgroup.normalizer (T : Set G)).one_mem, fun a ha => ?_⟩
        rw [commutatorElement_one_right]
        exact T.one_mem
    | mul x y hx hy ihx ihy =>
        refine ⟨(Subgroup.normalizer (T : Set G)).mul_mem ihx.1 ihy.1, fun a ha => ?_⟩
        have h2 : ⁅a, x * y⁆ = ⁅a, x⁆ * (x * ⁅a, y⁆ * x⁻¹) := by
          simp only [commutatorElement_def]; group
        rw [h2]
        exact T.mul_mem (ihx.2 a ha) ((Subgroup.mem_normalizer_iff.mp ihx.1 _).mp (ihy.2 a ha))
    | inv x hx ihx =>
        refine ⟨(Subgroup.normalizer (T : Set G)).inv_mem ihx.1, fun a ha => ?_⟩
        have hxinv : x⁻¹ ∈ Subgroup.normalizer (T : Set G) :=
          (Subgroup.normalizer (T : Set G)).inv_mem ihx.1
        have hmov : x⁻¹ * (⁅a, x⁆)⁻¹ * x ∈ T := by
          have h := (Subgroup.mem_normalizer_iff.mp hxinv (⁅a, x⁆)⁻¹).mp
            (T.inv_mem (ihx.2 a ha))
          simpa using h
        have h2 : ⁅a, x⁻¹⁆ = x⁻¹ * (⁅a, x⁆)⁻¹ * x := by
          simp only [commutatorElement_def]; group
        rw [h2]
        exact hmov
  exact (hmain k hk).2 a ha

theorem inf_centralizer_eq_bot_of_commutator_generation {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    [Finite G] {I P : Subgroup G} {v : G} (hI : IsElemAbelian 2 I) (hP : IsPGroup p ↥P)
    (hPI : P ≤ Subgroup.normalizer (I : Set G)) (hvI : v ∈ Subgroup.normalizer (I : Set G))
    (hv : v * v = 1) (hvP : v ∈ Subgroup.normalizer (P : Set G))
    (hIgen : I ≤ ⁅I, I ⊔ P ⊔ Subgroup.zpowers v⁆) :
    I ⊓ Subgroup.centralizer (P : Set G) = ⊥ := by
  haveI := hI.1
  set R : Subgroup G := ⁅I, P⁆ with hRdef
  set C : Subgroup G := I ⊓ Subgroup.centralizer (P : Set G) with hCdef
  set D : Subgroup G := ⁅C, Subgroup.zpowers v⁆ with hDdef
  set T : Subgroup G := R ⊔ D with hTdef
  have hRleI : R ≤ I := by
    rw [hRdef]
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp hPI
  have hCleI : C ≤ I := by rw [hCdef]; exact inf_le_left
  have hCcentP : C ≤ Subgroup.centralizer (P : Set G) := by rw [hCdef]; exact inf_le_right
  have hcompl : ¬ p ∣ Nat.card ↥I := by
    obtain ⟨k, hk⟩ := hI.isPGroup.exists_card_eq
    rw [hk]
    intro hdiv
    exact hp ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp
      (Nat.Prime.dvd_of_dvd_pow Fact.out hdiv))
  have hcop : Nat.Coprime p (Nat.card ↥I) := (Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hcompl
  have hfac : I = R ⊔ C := by
    rw [hRdef, hCdef]
    exact CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_centralizer_factorization
      p Fact.out P I hP hcompl hPI
  have hFit : R ⊓ C = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [hRdef, hCdef] at hx
    have hx' : x ∈ ⁅I, P⁆ ⊓ Subgroup.centralizer (P : Set G) := ⟨hx.1, hx.2.2⟩
    rw [CFSG.SignalizerFunctorTheorem.McBride.Near.Thm35.commutator_inf_centralizer_eq_bot
      Fact.out hP hPI hcop] at hx'
    simpa using hx'
  have hRcent : R ≤ Subgroup.centralizer (C : Set G) := by
    intro r hr
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    exact hI.comm (hCleI hc) (hRleI hr)
  have hvC : v ∈ Subgroup.normalizer (C : Set G) := by
    rw [hCdef]
    exact mem_normalizer_inf_of_mem_normalizer hvI
      (mem_normalizer_centralizer_of_mem_normalizer hvP)
  have hDleC : D ≤ C := by
    rw [hDdef, Subgroup.commutator_comm]
    exact Subgroup.le_normalizer_iff_commutator_le_right.mp (Subgroup.zpowers_le.mpr hvC)
  have hDleI : D ≤ I := hDleC.trans hCleI
  have hTleI : T ≤ I := by rw [hTdef]; exact sup_le hRleI hDleI
  have hvRnorm : v ∈ Subgroup.normalizer (R : Set G) := by
    rw [hRdef]
    exact mem_normalizer_commutator_of_mem_normalizer hvI hvP
  have hvDnorm : v ∈ Subgroup.normalizer (D : Set G) := by
    rw [hDdef]
    exact mem_normalizer_commutator_of_mem_normalizer hvC
      (Subgroup.le_normalizer (Subgroup.mem_zpowers v))
  have hPRnorm : P ≤ Subgroup.normalizer (R : Set G) := by
    rw [hRdef]
    exact Subgroup.normalizer_commutator_ge_right (H₁ := I) (H₂ := P)
  have hPDcent : P ≤ Subgroup.centralizer (D : Set G) := by
    intro s hs
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    exact (Subgroup.mem_centralizer_iff.mp (hCcentP (hDleC hd)) s hs).symm
  have hPDnorm : P ≤ Subgroup.normalizer (D : Set G) :=
    hPDcent.trans (Subgroup.centralizer_le_normalizer (D : Set G))
  have hS : ∀ s ∈ (I : Set G) ∪ (P : Set G) ∪ {v},
      s ∈ Subgroup.normalizer (T : Set G) ∧ ∀ a ∈ I, ⁅a, s⁆ ∈ T := by
    intro s hs
    simp only [Set.mem_union, Set.mem_singleton_iff] at hs
    rcases hs with (hsI | hsP) | hsv
    · refine ⟨?_, ?_⟩
      · refine Subgroup.centralizer_le_normalizer (T : Set G) ?_
        rw [Subgroup.mem_centralizer_iff]
        intro t ht
        exact (hI.comm hsI (hTleI ht)).symm
      · intro a ha
        rw [commutatorElement_eq_one_iff_mul_comm.mpr (hI.comm ha hsI)]
        exact T.one_mem
    · refine ⟨?_, ?_⟩
      · rw [hTdef]
        exact mem_normalizer_sup_of_mem_normalizer (hPRnorm hsP) (hPDnorm hsP)
      · intro a ha
        rw [hTdef]
        exact Subgroup.mem_sup_left (hRdef.symm ▸ Subgroup.commutator_mem_commutator ha hsP)
    · rw [hsv]
      refine ⟨?_, ?_⟩
      · rw [hTdef]
        exact mem_normalizer_sup_of_mem_normalizer hvRnorm hvDnorm
      · intro a ha
        have ha' : a ∈ R ⊔ C := by rw [← hfac]; exact ha
        rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right R C
          (hRcent.trans (Subgroup.centralizer_le_normalizer (C : Set G)))] at ha'
        obtain ⟨r, hr, c, hc, hrc⟩ := ha'
        rw [hTdef, ← hrc]
        have hcvD : ⁅c, v⁆ ∈ D := by
          rw [hDdef]
          exact Subgroup.commutator_mem_commutator hc (Subgroup.mem_zpowers v)
        have hrvR : ⁅r, v⁆ ∈ R := by
          have hvr : v * r⁻¹ * v⁻¹ ∈ R :=
            (Subgroup.mem_normalizer_iff.mp hvRnorm r⁻¹).mp (R.inv_mem hr)
          rw [commutatorElement_def]
          simpa only [mul_assoc] using R.mul_mem hr hvr
        have hmain : ⁅r * c, v⁆ = r * ⁅c, v⁆ * r⁻¹ * ⁅r, v⁆ := by
          simp only [commutatorElement_def]; group
        rw [hmain]
        have h1 : r * ⁅c, v⁆ * r⁻¹ ∈ D := by
          have hcomm : r * ⁅c, v⁆ = ⁅c, v⁆ * r :=
            hI.comm (hRleI hr) (hCleI (hDleC hcvD))
          rw [show r * ⁅c, v⁆ * r⁻¹ = ⁅c, v⁆ by rw [hcomm]; group]
          exact hcvD
        exact (R ⊔ D).mul_mem (Subgroup.mem_sup_right h1) (Subgroup.mem_sup_left hrvR)
  have hIKle : ⁅I, I ⊔ P ⊔ Subgroup.zpowers v⁆ ≤ T := by
    have hKle : (I ⊔ P ⊔ Subgroup.zpowers v) ≤
        Subgroup.closure ((I : Set G) ∪ (P : Set G) ∪ {v}) := by
      refine sup_le (sup_le ?_ ?_) ?_
      · exact fun a ha => Subgroup.subset_closure (Or.inl (Or.inl ha))
      · exact fun a ha => Subgroup.subset_closure (Or.inl (Or.inr ha))
      · rw [Subgroup.zpowers_le]
        exact Subgroup.subset_closure (Or.inr rfl)
    exact (Subgroup.commutator_mono le_rfl hKle).trans (commutator_closure_le hS)
  have hCleT : C ≤ T := fun c hc => hIKle (hIgen (hCleI hc))
  have hC_le_D : C ≤ D := by
    intro c hc
    have hcT : c ∈ T := hCleT hc
    have hRD : R ≤ Subgroup.normalizer (D : Set G) :=
      (hRcent.trans
        (Subgroup.centralizer_le (show (D : Set G) ⊆ (C : Set G) from hDleC))).trans
        (Subgroup.centralizer_le_normalizer (D : Set G))
    have hcT' : c ∈ R ⊔ D := hTdef ▸ hcT
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right R D hRD] at hcT'
    obtain ⟨r, hr, d, hd, rfl⟩ := hcT'
    have hrC : r ∈ C := by
      have : r = (r * d) * d⁻¹ := by group
      rw [this]
      exact C.mul_mem hc (C.inv_mem (hDleC hd))
    have hrbot : r ∈ R ⊓ C := ⟨hr, hrC⟩
    rw [hFit] at hrbot
    have hr1 : r = 1 := by simpa using hrbot
    simpa [hr1] using hd
  have hD_le_cent : D ≤ Subgroup.centralizer ({v} : Set G) := by
    rw [hDdef, Subgroup.commutator_le]
    intro c hc w hw
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    rcases zpow_eq_one_or_self_of_mul_self_eq_one hv n with h | h
    · rw [h, commutatorElement_one_right]
      exact (Subgroup.centralizer ({v} : Set G)).one_mem
    · rw [h, Subgroup.mem_centralizer_singleton_iff]
      have hcI : c ∈ I := hCleI hc
      have hcinv : c⁻¹ = c := inv_eq_of_mul_eq_one_right (hI.mul_self_eq_one hcI)
      have hcvcC : v * c * v⁻¹ ∈ C := (Subgroup.mem_normalizer_iff.mp hvC c).mp hc
      have h1 : ⁅c, v⁆ = c * (v * c * v⁻¹) := by
        rw [commutatorElement_def, hcinv]
        group
      have hvv2 : v⁻¹ * v⁻¹ = 1 := by rw [← mul_inv_rev, hv, inv_one]
      have hvv2' : v * (v * c * v⁻¹) * v⁻¹ = c := by
        calc v * (v * c * v⁻¹) * v⁻¹ = (v * v) * c * (v⁻¹ * v⁻¹) := by group
          _ = c := by rw [hv, hvv2]; group
      have hkey : v * ⁅c, v⁆ * v⁻¹ = ⁅c, v⁆ := by
        calc v * ⁅c, v⁆ * v⁻¹ = v * (c * (v * c * v⁻¹)) * v⁻¹ := by rw [h1]
          _ = (v * c * v⁻¹) * (v * (v * c * v⁻¹) * v⁻¹) := by group
          _ = (v * c * v⁻¹) * c := by rw [hvv2']
          _ = c * (v * c * v⁻¹) := hI.comm (hCleI hcvcC) hcI
          _ = ⁅c, v⁆ := h1.symm
      have hcomm : ⁅c, v⁆ * v = v * ⁅c, v⁆ := by
        have hstep := congrArg (fun t => t * v) hkey
        simp only [mul_assoc, inv_mul_cancel, mul_one] at hstep
        exact hstep.symm
      exact hcomm
  have hC_le_cent : C ≤ Subgroup.centralizer ({v} : Set G) := hC_le_D.trans hD_le_cent
  have hDbot : D = ⊥ := by
    rw [hDdef, Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro c hc
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    have hcv : c * v = v * c := Subgroup.mem_centralizer_singleton_iff.mp (hC_le_cent hc)
    exact (Commute.zpow_right (show Commute c v from hcv) n).eq.symm
  exact le_bot_iff.mp (hC_le_D.trans (le_of_eq hDbot))

theorem le_centralizer_involution_of_le_centralizer {I P M : Subgroup G} {v y z : G}
    (hMI : M ≤ I) (hvI : v ∈ Subgroup.normalizer (I : Set G))
    (hvM : v ∈ Subgroup.normalizer (M : Set G)) (hvP : v ∈ Subgroup.normalizer (P : Set G))
    (hPIbot : P ⊓ I = ⊥) (hyP : y ∈ P) (hyI : y ∈ Subgroup.normalizer (I : Set G))
    (hcent : ∀ u ∈ P, v * u = u * v → u ∈ Subgroup.zpowers z) (hyz : y ∉ Subgroup.zpowers z)
    (hT : ∀ y ∈ Subgroup.normalizer (I : Set G), ∀ w ∈ ⁅I, Subgroup.zpowers v⁆, w ≠ 1 →
      y ∈ Subgroup.centralizer ({w} : Set G) → ⁅v, y⁆ ∈ I)
    (hyM : M ≤ Subgroup.centralizer ({y} : Set G)) :
    M ≤ Subgroup.centralizer ({v} : Set G) := by
  intro a ha
  rw [Subgroup.mem_centralizer_singleton_iff]
  set w : G := ⁅a, v⁆ with hwdef
  have haI : a ∈ I := hMI ha
  have hwM : w ∈ M := by
    rw [hwdef, commutatorElement_def]
    simpa only [mul_assoc] using
      M.mul_mem ha ((Subgroup.mem_normalizer_iff.mp hvM a⁻¹).mp (M.inv_mem ha))
  have hwcomm : w ∈ ⁅I, Subgroup.zpowers v⁆ := by
    rw [hwdef]
    exact Subgroup.commutator_mem_commutator haI (Subgroup.mem_zpowers v)
  have hycomm : y ∈ Subgroup.centralizer ({w} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    exact (Subgroup.mem_centralizer_iff.mp (hyM hwM) y (Set.mem_singleton y)).symm
  have hw1 : w = 1 := by
    by_contra hwne
    have hvyI : ⁅v, y⁆ ∈ I := hT y hyI w hwcomm hwne hycomm
    have hvyP : ⁅v, y⁆ ∈ P := by
      rw [commutatorElement_def]
      simpa only [mul_assoc] using
        P.mul_mem ((Subgroup.mem_normalizer_iff.mp hvP y).mp hyP) (P.inv_mem hyP)
    have hvy1 : ⁅v, y⁆ = 1 := by
      have hmem : ⁅v, y⁆ ∈ P ⊓ I := ⟨hvyP, hvyI⟩
      rw [hPIbot] at hmem
      simpa using hmem
    exact hyz (hcent y hyP (commutatorElement_eq_one_iff_mul_comm.mp hvy1))
  rw [hwdef] at hw1
  exact commutatorElement_eq_one_iff_mul_comm.mp hw1

theorem inf_centralizer_le_centralizer_involution {p : ℕ} {I P : Subgroup G} {v x z g : G}
    (hPI : P ≤ Subgroup.normalizer (I : Set G)) (hvI : v ∈ Subgroup.normalizer (I : Set G))
    (hvP : v ∈ Subgroup.normalizer (P : Set G)) (cfg : HeisConfig p P v x z g)
    (hPIbot : P ⊓ I = ⊥)
    (hT : ∀ y ∈ Subgroup.normalizer (I : Set G), ∀ w ∈ ⁅I, Subgroup.zpowers v⁆, w ≠ 1 →
      y ∈ Subgroup.centralizer ({w} : Set G) → ⁅v, y⁆ ∈ I) :
    I ⊓ Subgroup.centralizer ({x} : Set G) ≤ Subgroup.centralizer ({v} : Set G) := by
  have hxz : x ∉ Subgroup.zpowers z := by
    intro hx
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hx
    have hcomm : Commute x g := by
      rw [← hn]
      exact (show Commute z g from (cfg.z_central g cfg.g_mem).symm).zpow_left n
    have hconj : g * x * g⁻¹ = x := by rw [← hcomm.eq]; group
    rw [cfg.g_conj_x] at hconj
    have hz1 : z = 1 := mul_left_cancel (show x * z = x * 1 by rw [hconj, mul_one])
    exact cfg.z_ne_one hz1
  have hvxinv : v⁻¹ * x * v = x⁻¹ := by
    have hx : x = v⁻¹ * x⁻¹ * v := by
      calc x = v⁻¹ * (v * x * v⁻¹) * v := by group
        _ = v⁻¹ * x⁻¹ * v := by rw [cfg.v_conj_x]
    have h := congrArg Inv.inv hx
    simpa only [mul_inv_rev, inv_inv, mul_assoc] using h.symm
  have hvxinv' : v * x⁻¹ * v⁻¹ = x := by
    have h := congrArg Inv.inv cfg.v_conj_x
    simpa only [mul_inv_rev, inv_inv, mul_assoc] using h
  have hvxinv'' : v⁻¹ * x⁻¹ * v = x := by
    have hx : x = v⁻¹ * x⁻¹ * v := by
      calc x = v⁻¹ * (v * x * v⁻¹) * v := by group
        _ = v⁻¹ * x⁻¹ * v := by rw [cfg.v_conj_x]
    exact hx.symm
  have hvx' : v⁻¹ * x = x⁻¹ * v⁻¹ := by
    rw [← hvxinv]; group
  have hvx'' : v * x = x⁻¹ * v := by
    calc v * x = (v * x * v⁻¹) * v := by group
      _ = x⁻¹ * v := by rw [cfg.v_conj_x]
  have hM1 : ∀ a ∈ I ⊓ Subgroup.centralizer ({x} : Set G),
      v * a * v⁻¹ ∈ I ⊓ Subgroup.centralizer ({x} : Set G) := by
    intro a ha
    have hax : a * x = x * a := Subgroup.mem_centralizer_singleton_iff.mp ha.2
    have haxinv : a * x⁻¹ = x⁻¹ * a := (Commute.inv_right (show Commute a x from hax)).eq
    refine ⟨?_, ?_⟩
    · simpa using (Subgroup.mem_normalizer_iff.mp hvI a).mp ha.1
    · exact Subgroup.mem_centralizer_singleton_iff.mpr (by
        calc (v * a * v⁻¹) * x = v * a * (v⁻¹ * x) := by group
          _ = v * a * (x⁻¹ * v⁻¹) := by rw [hvx']
          _ = v * (a * x⁻¹) * v⁻¹ := by group
          _ = v * (x⁻¹ * a) * v⁻¹ := by rw [haxinv]
          _ = (v * x⁻¹ * v⁻¹) * (v * a * v⁻¹) := by group
          _ = x * (v * a * v⁻¹) := by rw [hvxinv'])
  have hM2 : ∀ a ∈ I ⊓ Subgroup.centralizer ({x} : Set G),
      v⁻¹ * a * v ∈ I ⊓ Subgroup.centralizer ({x} : Set G) := by
    intro a ha
    have hax : a * x = x * a := Subgroup.mem_centralizer_singleton_iff.mp ha.2
    have haxinv : a * x⁻¹ = x⁻¹ * a := (Commute.inv_right (show Commute a x from hax)).eq
    have hvI' : v⁻¹ ∈ Subgroup.normalizer (I : Set G) :=
      (Subgroup.normalizer (I : Set G)).inv_mem hvI
    refine ⟨?_, ?_⟩
    · simpa using (Subgroup.mem_normalizer_iff.mp hvI' a).mp ha.1
    · exact Subgroup.mem_centralizer_singleton_iff.mpr (by
        calc (v⁻¹ * a * v) * x = v⁻¹ * a * (v * x) := by group
          _ = v⁻¹ * a * (x⁻¹ * v) := by rw [hvx'']
          _ = v⁻¹ * (a * x⁻¹) * v := by group
          _ = v⁻¹ * (x⁻¹ * a) * v := by rw [haxinv]
          _ = (v⁻¹ * x⁻¹ * v) * (v⁻¹ * a * v) := by group
          _ = x * (v⁻¹ * a * v) := by rw [hvxinv''])
  have hvM : v ∈ Subgroup.normalizer
      ((I ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G) : Set G) :=
    mem_normalizer_of_conj_mem' hM1 hM2
  exact le_centralizer_involution_of_le_centralizer
    (I := I) (M := I ⊓ Subgroup.centralizer ({x} : Set G))
    (y := x) (z := z) inf_le_left hvI hvM hvP hPIbot cfg.x_mem (hPI cfg.x_mem)
    cfg.centralizer_le hxz hT inf_le_right

theorem inf_centralizer_eq_bot {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) [Finite G]
    {I P : Subgroup G} {v x z g : G} (hI : IsElemAbelian 2 I) (hP : IsPGroup p ↥P)
    (hPI : P ≤ Subgroup.normalizer (I : Set G)) (hvI : v ∈ Subgroup.normalizer (I : Set G))
    (hv : v * v = 1) (hvP : v ∈ Subgroup.normalizer (P : Set G)) (cfg : HeisConfig p P v x z g)
    (hPIbot : P ⊓ I = ⊥) (hPv : ⁅P, Subgroup.zpowers v⁆ = P)
    (hIgen : I ≤ ⁅I, I ⊔ P ⊔ Subgroup.zpowers v⁆)
    (hT : ∀ y ∈ Subgroup.normalizer (I : Set G), ∀ w ∈ ⁅I, Subgroup.zpowers v⁆, w ≠ 1 →
      y ∈ Subgroup.centralizer ({w} : Set G) → ⁅v, y⁆ ∈ I) :
    I ⊓ Subgroup.centralizer ({z} : Set G) = ⊥ := by
  haveI := hI.1
  set N : Subgroup G := I ⊓ Subgroup.centralizer ({z} : Set G) with hNdef
  have hNleI : N ≤ I := by rw [hNdef]; exact inf_le_left
  have hNleCz : N ≤ Subgroup.centralizer ({z} : Set G) := by rw [hNdef]; exact inf_le_right
  have hN : IsElemAbelian 2 N := hI.mono hNleI
  have hPN : P ≤ Subgroup.normalizer (N : Set G) := by
    intro t ht
    have htI : t ∈ Subgroup.normalizer (I : Set G) := hPI ht
    have htz : t ∈ Subgroup.centralizer ({z} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact cfg.z_central t ht
    have htCz := mem_normalizer_centralizer_singleton_of_mem_centralizer htz
    rw [hNdef]
    exact mem_normalizer_inf_of_mem_normalizer htI htCz
  have hvN : v ∈ Subgroup.normalizer (N : Set G) := by
    have hvz : v ∈ Subgroup.centralizer ({z} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact cfg.v_comm_z
    have hvCz := mem_normalizer_centralizer_singleton_of_mem_centralizer hvz
    rw [hNdef]
    exact mem_normalizer_inf_of_mem_normalizer hvI hvCz
  have hxN : x ∈ Subgroup.normalizer (N : Set G) := hPN cfg.x_mem
  have hgN : g ∈ Subgroup.normalizer (N : Set G) := hPN cfg.g_mem
  have hzg : z * g = g * z := (cfg.z_central g cfg.g_mem).symm
  have hgx : g * x = x * z * g := by
    calc g * x = (g * x * g⁻¹) * g := by group
      _ = (x * z) * g := by rw [cfg.g_conj_x]
  have hxg : x * g = g * x * z⁻¹ := by
    have h1 : x * g * z = g * x := by
      calc x * g * z = x * (g * z) := by group
        _ = x * (z * g) := by rw [hzg]
        _ = x * z * g := by group
        _ = g * x := by rw [hgx]
    calc x * g = x * g * (z * z⁻¹) := by group
      _ = (x * g * z) * z⁻¹ := by group
      _ = (g * x) * z⁻¹ := by rw [h1]
  have hxy : ∀ a ∈ N, x * (g * a * g⁻¹) * x⁻¹ = g * (x * a * x⁻¹) * g⁻¹ := by
    intro a ha
    have haz : a * z = z * a := Subgroup.mem_centralizer_singleton_iff.mp (hNleCz ha)
    have hz_a : z⁻¹ * a * z = a := by
      calc z⁻¹ * a * z = z⁻¹ * (a * z) := by group
        _ = z⁻¹ * (z * a) := by rw [haz]
        _ = a := by group
    have hxg_a : (x * g) * a * (x * g)⁻¹ = (g * x) * a * (g * x)⁻¹ := by
      calc (x * g) * a * (x * g)⁻¹
          = (g * x * z⁻¹) * a * (z * (g * x)⁻¹) := by rw [hxg, mul_inv_rev, inv_inv]
        _ = (g * x) * (z⁻¹ * a * z) * (g * x)⁻¹ := by group
        _ = (g * x) * a * (g * x)⁻¹ := by rw [hz_a]
    calc x * (g * a * g⁻¹) * x⁻¹ = (x * g) * a * (x * g)⁻¹ := by group
      _ = (g * x) * a * (g * x)⁻¹ := hxg_a
      _ = g * (x * a * x⁻¹) * g⁻¹ := by group
  have hfix : N ⊓ Subgroup.centralizer ({x} : Set G) ⊓
      Subgroup.centralizer ({g} : Set G) = ⊥ := by
    have hle : N ⊓ Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({g} : Set G) ≤
        I ⊓ Subgroup.centralizer (P : Set G) := by
      intro w hw
      have hwN : w ∈ N := hw.1.1
      have hwx : w ∈ Subgroup.centralizer ({x} : Set G) := hw.1.2
      have hwg : w ∈ Subgroup.centralizer ({g} : Set G) := hw.2
      have hwz : w ∈ Subgroup.centralizer ({z} : Set G) := hNleCz hwN
      refine ⟨hNleI hwN, ?_⟩
      have hwC : w ∈ Subgroup.centralizer (Subgroup.closure ({x, g, z} : Set G) : Set G) := by
        rw [Subgroup.centralizer_closure]
        rw [Subgroup.mem_centralizer_iff]
        intro s hs
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
        rcases hs with hx | hg | hz
        · rw [hx]; exact (Subgroup.mem_centralizer_singleton_iff.mp hwx).symm
        · rw [hg]; exact (Subgroup.mem_centralizer_singleton_iff.mp hwg).symm
        · rw [hz]; exact (Subgroup.mem_centralizer_singleton_iff.mp hwz).symm
      exact Subgroup.centralizer_le cfg.le_closure hwC
    have hbot := inf_centralizer_eq_bot_of_commutator_generation (p := p) hp hI hP hPI hvI hv hvP
      hIgen
    rw [hbot] at hle
    exact le_bot_iff.mp hle
  have hgen := le_iSup_inf_centralizer (p := p) hp hN hxN hgN cfg.x_pow cfg.g_pow hxy hfix
  have hxgbz : ∀ b : ZMod p, x * g ^ b.val ∉ Subgroup.zpowers z := by
    intro b hmem
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hcomm : Commute (x * g ^ b.val) g := by
      rw [← hn]
      exact (show Commute z g from (cfg.z_central g cfg.g_mem).symm).zpow_left n
    have hconj : g * (x * g ^ b.val) * g⁻¹ = x * g ^ b.val := by
      rw [← hcomm.eq]; group
    have hgb : g * g ^ b.val * g⁻¹ = g ^ b.val := by
      calc g * g ^ b.val * g⁻¹ = g ^ (b.val + 1) * g⁻¹ := by rw [pow_succ']
        _ = (g ^ b.val * g) * g⁻¹ := by rw [pow_succ]
        _ = g ^ b.val := by group
    have hcalc : g * (x * g ^ b.val) * g⁻¹ = x * z * g ^ b.val := by
      calc g * (x * g ^ b.val) * g⁻¹
          = (g * x * g⁻¹) * (g * g ^ b.val * g⁻¹) := by group
        _ = (x * z) * g ^ b.val := by rw [cfg.g_conj_x, hgb]
    rw [hcalc] at hconj
    have h1 : z * g ^ b.val = g ^ b.val := mul_left_cancel (show
      x * (z * g ^ b.val) = x * g ^ b.val by rw [← mul_assoc]; exact hconj)
    have hz1 : z = 1 := mul_right_cancel (show z * g ^ b.val = 1 * g ^ b.val by rw [h1, one_mul])
    exact cfg.z_ne_one hz1
  have hgz : g ∉ Subgroup.zpowers z := by
    intro hmem
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hcomm : Commute g x := by
      rw [← hn]
      exact (show Commute z x from (cfg.z_central x cfg.x_mem).symm).zpow_left n
    have hconj : g * x * g⁻¹ = x := by rw [hcomm.eq]; group
    rw [cfg.g_conj_x] at hconj
    have hz1 : z = 1 := mul_left_cancel (show x * z = x * 1 by rw [hconj, mul_one])
    exact cfg.z_ne_one hz1
  have hpiece : ∀ y' : G, y' ∈ P → y' ∉ Subgroup.zpowers z →
      N ⊓ Subgroup.centralizer ({y'} : Set G) ≤ Subgroup.centralizer ({v} : Set G) := by
    intro y' hy'P hy'z
    obtain ⟨c, hc_mem, hc_eq⟩ := cfg.v_conj_mem y' hy'P
    have hv_inv : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv
    have hy'v : v⁻¹ * y' * v = y'⁻¹ * c := by
      rw [hv_inv] at hc_eq ⊢
      exact hc_eq
    refine le_centralizer_involution_of_le_centralizer
      (I := I) (M := N ⊓ Subgroup.centralizer ({y'} : Set G)) (y := y') (z := z)
      (inf_le_left.trans hNleI) hvI ?_ hvP hPIbot hy'P (hPI hy'P) cfg.centralizer_le hy'z hT
      inf_le_right
    refine mem_normalizer_of_conj_mem hv ?_
    intro a ha
    have haN : a ∈ N := ha.1
    have hay' : a * y' = y' * a := Subgroup.mem_centralizer_singleton_iff.mp ha.2
    have ha_yinv : a * y'⁻¹ = y'⁻¹ * a := (Commute.inv_right (show Commute a y' from hay')).eq
    have haz : a * z = z * a := Subgroup.mem_centralizer_singleton_iff.mp (hNleCz haN)
    have ha_c : a * c = c * a := by
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hc_mem
      rw [← hm]
      exact (Commute.zpow_right (show Commute a z from haz) m).eq
    have hy'v' : v⁻¹ * y' = y'⁻¹ * c * v⁻¹ := by
      calc v⁻¹ * y' = (v⁻¹ * y' * v) * v⁻¹ := by group
        _ = (y'⁻¹ * c) * v⁻¹ := by rw [hy'v]
    have ha'_comm : (v * a * v⁻¹) * y' = y' * (v * a * v⁻¹) := by
      calc (v * a * v⁻¹) * y' = v * a * (v⁻¹ * y') := by group
        _ = v * a * (y'⁻¹ * c * v⁻¹) := by rw [hy'v']
        _ = (v * a * y'⁻¹) * (c * v⁻¹) := by group
        _ = (v * (a * y'⁻¹)) * (c * v⁻¹) := by group
        _ = (v * (y'⁻¹ * a)) * (c * v⁻¹) := by rw [ha_yinv]
        _ = (v * y'⁻¹) * (a * c) * v⁻¹ := by group
        _ = (v * y'⁻¹) * (c * a) * v⁻¹ := by rw [ha_c]
        _ = v * ((y'⁻¹ * c) * a) * v⁻¹ := by group
        _ = v * ((v⁻¹ * y' * v) * a) * v⁻¹ := by rw [← hy'v]
        _ = y' * (v * a * v⁻¹) := by group
    refine ⟨(Subgroup.mem_normalizer_iff.mp hvN a).mp haN, ?_⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr ha'_comm
  have hN_le_centv : N ≤ Subgroup.centralizer ({v} : Set G) :=
    hgen.trans (sup_le (iSup_le fun b =>
      hpiece (x * g ^ b.val) (P.mul_mem cfg.x_mem (P.pow_mem cfg.g_mem b.val)) (hxgbz b))
      (hpiece g cfg.g_mem hgz))
  have hN_le_centP : N ≤ Subgroup.centralizer (P : Set G) := by
    rw [Subgroup.le_centralizer_iff]
    rw [← hPv]
    rw [Subgroup.commutator_le]
    intro y hy w hw
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    rcases zpow_eq_one_or_self_of_mul_self_eq_one hv n with h | h
    · rw [h, commutatorElement_one_right]
      exact (Subgroup.centralizer (N : Set G)).one_mem
    · rw [h, Subgroup.mem_centralizer_iff]
      intro a ha
      have haN : a ∈ N := ha
      have hbN : y⁻¹ * a * y ∈ N := (Subgroup.mem_normalizer_iff''.mp (hPN hy) a).mp haN
      have hvb : v * (y⁻¹ * a * y) * v⁻¹ = y⁻¹ * a * y := by
        have h := Subgroup.mem_centralizer_singleton_iff.mp (hN_le_centv hbN)
        rw [← h]; group
      have hva : v⁻¹ * a * v = a := by
        have hav : a * v = v * a := Subgroup.mem_centralizer_singleton_iff.mp (hN_le_centv haN)
        have hvv : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv
        rw [hvv]
        calc v * a * v = (a * v) * v := by rw [← hav]
          _ = a * (v * v) := by group
          _ = a := by rw [hv, mul_one]
      have hconj : ⁅y, v⁆ * a * ⁅y, v⁆⁻¹ = a := by
        have hinv : (y * v * y⁻¹ * v⁻¹)⁻¹ = v * y * v⁻¹ * y⁻¹ := by group
        rw [commutatorElement_def, hinv]
        calc (y * v * y⁻¹ * v⁻¹) * a * (v * y * v⁻¹ * y⁻¹)
            = y * v * y⁻¹ * (v⁻¹ * a * v) * y * v⁻¹ * y⁻¹ := by group
          _ = y * v * y⁻¹ * a * y * v⁻¹ * y⁻¹ := by rw [hva]
          _ = y * (v * (y⁻¹ * a * y) * v⁻¹) * y⁻¹ := by group
          _ = y * (y⁻¹ * a * y) * y⁻¹ := by rw [hvb]
          _ = a := by group
      have hka : ⁅y, v⁆ * a = a * ⁅y, v⁆ := by
        have hstep := congrArg (fun t => t * ⁅y, v⁆) hconj
        simpa only [mul_assoc, inv_mul_cancel, mul_one] using hstep
      exact hka.symm
  have hle : N ≤ I ⊓ Subgroup.centralizer (P : Set G) := le_inf hNleI hN_le_centP
  have hbot := inf_centralizer_eq_bot_of_commutator_generation (p := p) hp hI hP hPI hvI hv hvP
    hIgen
  rw [hbot] at hle
  exact le_bot_iff.mp hle

end CFSG.LocalAnalysis.WeakClosure81
