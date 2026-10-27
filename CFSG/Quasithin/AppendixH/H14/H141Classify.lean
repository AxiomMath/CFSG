module

public import CFSG.Quasithin.AppendixH.H14.H141SChecks
public import CFSG.Quasithin.AppendixH.H14.H141TChecks
public import CFSG.Quasithin.AppendixH.H14.H141Std
public import CFSG.Quasithin.AppendixH.H14.H142Conj
public import CFSG.Quasithin.AppendixH.H14.H142Group
public import Certificates.Certificate490001

public section

open scoped Pointwise

namespace CFSG.Quasithin.AppendixH.H14

open CFSG.ASVolI.ChH CFSG.Quasithin CFSG.Quasithin.H.Mathieu CFSG.QuasithinUnique.Setup.X1
  CFSG.Open CFSG.Monster.Code

section Search

theorem c1All :
    forallGreedyAll pos24s2 inv24s2 predC1 7 [] = true :=
  Certificates.certificate490001

theorem greedyC1 {k : ℕ} (hk : k ≤ 7) :
    forallGreedy T24s2.invols predC1 k [] = true :=
  (forallGreedyP_eq pos24s2_eq predC1 k []).symm.trans (forallGreedyAll_le 7 [] c1All k hk)

theorem predC1_spec {l : List T24s2.Elem} (h : predC1 l = true) :
    l.length ≤ 6 ∧ (5 ≤ l.length →
      (∀ x ∈ subprods l, inTab64 tabS (T24s2.arr x) = true) ∨
      (∀ x ∈ subprods l, inTab64 tabT (T24s2.arr x) = true) ∨
      (l.length = 5 ∧ ∃ cs ∈ c1Fuse, ∀ x ∈ subprods l,
        inTab64 (if cs.2 then tabS else tabT) (c1Conj cs.1 (T24s2.arr x)) = true)) := by
  unfold predC1 at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.any_eq_true, beq_iff_eq] at h
  refine ⟨h.1, fun h5 => ?_⟩
  have hAn : ¬ l.length < 5 := by omega
  rcases h.2 with hABC | hD
  · rcases hABC with hAB | hC
    · rcases hAB with hA | hB
      · exact absurd hA hAn
      · exact Or.inl hB
    · exact Or.inr (Or.inl hC)
  · exact Or.inr (Or.inr hD)

end Search

theorem mem_tab64Sub_of_inTab64 {tab : Array (Array ℕ)} (hT : tab64OK tab = true) {σ : S24}
    {b : Array ℕ} (hσ : HasArr σ b) (hb : inTab64 tab b = true) : σ ∈ tab64Sub tab hT := by
  unfold inTab64 at hb
  rw [List.any_eq_true] at hb
  obtain ⟨m, hm, hbeq⟩ := hb
  have hm64 : m < 64 := List.mem_range.mp hm
  have hmb : tab[m]! = b := beq_iff_eq.mp hbeq
  have hσ' : HasArr σ tab[m]! := hmb ▸ hσ
  have huniq : σ = tab64Perm tab m := hasArr_unique hσ' (hasArr_tab64Perm hT hm64)
  rw [huniq]
  exact tab64Perm_mem_tab64Sub hT hm64

theorem c1Conj_eq (a t : Array ℕ) : c1Conj a t = conj24 a t := by
  unfold c1Conj c1Comp conj24 comp24
  rfl

theorem c1Fuse_ok : ∀ cs ∈ c1Fuse, inAutOK cs.1 = true := by
  have h : c1Fuse.all (fun cs => inAutOK cs.1) = true := by decide +kernel
  exact fun cs hcs => List.all_eq_true.mp h cs hcs

theorem tab64Sub_S_ne_T : tab64Sub tabS tabS_ok ≠ tab64Sub tabT tabT_ok := by
  intro heq
  have hfind : (List.range 64).any (fun n =>
      (List.range 64).all fun m => decide (tabS[n]! ≠ tabT[m]!)) = true := by decide +kernel
  obtain ⟨n, hn, hnin⟩ := List.any_eq_true.mp hfind
  have hn64 : n < 64 := List.mem_range.mp hn
  have hforall : ∀ m < 64, tabS[n]! ≠ tabT[m]! := by
    intro m hm
    exact of_decide_eq_true (List.all_eq_true.mp hnin m (List.mem_range.mpr hm))
  have hmemS : tab64Perm tabS n ∈ tab64Sub tabS tabS_ok := tab64Perm_mem_tab64Sub tabS_ok hn64
  rw [heq] at hmemS
  obtain ⟨m, hm64, hm⟩ := (mem_tab64Sub tabT_ok).mp hmemS
  have hS : HasArr (tab64Perm tabS n) tabS[n]! := hasArr_tab64Perm tabS_ok hn64
  have hT' : HasArr (tab64Perm tabT m) tabT[m]! := hasArr_tab64Perm tabT_ok hm64
  rw [hm] at hS
  have hentry : tabS[n]! = tabT[m]! :=
    arr_eq_of_hasArr hS hT' (tab64_size_lt tabS_ok hn64) (tab64_size_lt tabT_ok hm64)
  exact hforall m hm64 hentry

theorem isPGroup_of_isElemAbelian {A : Subgroup S24} (hel : IsElemAbelian 2 A) :
    IsPGroup 2 A := by
  refine CFSG.Quasithin.isPGroup_two_of_sq_eq_one ?_
  intro v
  rw [pow_two]
  exact Subtype.ext (((isElemAbelian_two_iff A).mp hel).2 v v.2)

theorem card_eq_two_pow_rk {A : Subgroup S24} (hel : IsElemAbelian 2 A) :
    Nat.card ↥A = 2 ^ rk ↥A :=
  CFSG.Quasithin.card_eq_two_pow_of_isPGroup (isPGroup_of_isElemAbelian hel)

section Chains

theorem le_tab64Sub_of_forall {tab : Array (Array ℕ)} (hT : tab64OK tab = true) {B : Subgroup S24}
    (hB : ∀ b ∈ B, ∃ p : T24s2.Elem, b = T24s2.perm p ∧ inTab64 tab (T24s2.arr p) = true) :
    B ≤ tab64Sub tab hT := by
  intro b hb
  obtain ⟨p, rfl, hp⟩ := hB b hb
  exact mem_tab64Sub_of_inTab64 hT (T24s2.hasArr_perm p) hp

theorem exists_chain {A : Subgroup S24} (hAT : ∀ a ∈ A, ∃ p : T24s2.Elem, a = T24s2.perm p)
    (hel : IsElemAbelian 2 A) {k : ℕ} (hk : k ≤ 7) (hcard : Nat.card ↥A = 2 ^ k) :
    ∃ l : List T24s2.Elem, l.length = k ∧ predC1 l = true ∧
      ∀ a ∈ A, ∃ p ∈ subprods l, a = T24s2.perm p := by
  let B : Subgroup T24s2.Elem := A.comap T24s2.toPerm
  have helA := (isElemAbelian_two_iff A).mp hel
  have hcommB : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := by
    intro x hx y hy
    apply T24s2.toPerm_injective
    rw [map_mul, map_mul]
    exact helA.1 (T24s2.toPerm x) (Subgroup.mem_comap.mp hx) (T24s2.toPerm y)
      (Subgroup.mem_comap.mp hy)
  have hsqB : ∀ x ∈ B, x * x = 1 := by
    intro x hx
    apply T24s2.toPerm_injective
    rw [map_mul, map_one]
    exact helA.2 (T24s2.toPerm x) (Subgroup.mem_comap.mp hx)
  have hRB : ∀ x ∈ B, x ≠ 1 → x ∈ T24s2.invols := fun x hx hx1 =>
    T24s2.mem_invols hx1 (hsqB x hx)
  have hcardB : Nat.card B = 2 ^ k := by
    have hBmap : B.map T24s2.toPerm = A := by
      refine Subgroup.map_comap_eq_self ?_
      intro a ha
      obtain ⟨p, rfl⟩ := hAT a ha
      exact ⟨p, by rw [T24s2.toPerm_apply]⟩
    calc Nat.card B = Nat.card ↥(B.map T24s2.toPerm) :=
          (Subgroup.card_map_of_injective (K := B) T24s2.toPerm_injective).symm
      _ = Nat.card ↥A := by rw [hBmap]
      _ = 2 ^ k := hcard
  obtain ⟨l, hlen, _hind, hmem, hpred⟩ :=
    forallGreedy_sound (greedyC1 hk) B hcommB hsqB hRB hcardB
  refine ⟨l, hlen, hpred, fun a ha => ?_⟩
  obtain ⟨p, rfl⟩ := hAT a ha
  refine ⟨p, (hmem p).1 ?_, rfl⟩
  show T24s2.toPerm p ∈ A
  rwa [T24s2.toPerm_apply]

theorem rank_le_six {A : Subgroup S24} (hAT : ∀ a ∈ A, ∃ p : T24s2.Elem, a = T24s2.perm p)
    (hel : IsElemAbelian 2 A) {k : ℕ} (hcard : Nat.card ↥A = 2 ^ k) : k ≤ 6 := by
  by_contra hk
  have hk7 : 7 ≤ k := by have := Nat.lt_of_not_le hk; omega
  have hpA : IsPGroup 2 A := isPGroup_of_isElemAbelian hel
  have h2k : 2 ^ 7 ≤ Nat.card ↥A := by
    rw [hcard]
    exact Nat.pow_le_pow_right (by norm_num) hk7
  obtain ⟨H', hH'card⟩ :=
    Sylow.exists_subgroup_card_pow_prime_of_le_card (p := 2) (n := 7) Nat.prime_two hpA h2k
  set A7 : Subgroup S24 := H'.map A.subtype with hA7def
  have hcard7 : Nat.card ↥A7 = 2 ^ 7 := by
    rw [hA7def, Subgroup.card_map_of_injective A.subtype_injective, hH'card]
  have hA7A : A7 ≤ A := by
    rw [hA7def]
    rintro x ⟨y, hy, rfl⟩
    exact y.2
  have hAT7 : ∀ a ∈ A7, ∃ p : T24s2.Elem, a = T24s2.perm p := fun a ha => hAT a (hA7A ha)
  have hel7 : IsElemAbelian 2 A7 := by
    have hA' := (isElemAbelian_two_iff A).mp hel
    refine (isElemAbelian_two_iff A7).mpr ⟨?_, ?_⟩
    · intro x hx y hy
      exact hA'.1 x (hA7A hx) y (hA7A hy)
    · intro x hx
      exact hA'.2 x (hA7A hx)
  obtain ⟨l, hlen, hpred, _⟩ := exists_chain hAT7 hel7 (k := 7) le_rfl hcard7
  have := (predC1_spec hpred).1
  omega

theorem classify_E64 {A : Subgroup S24} (hAT : ∀ a ∈ A, ∃ p : T24s2.Elem, a = T24s2.perm p)
    (hE : IsE2k 6 A) : A = tab64Sub tabS tabS_ok ∨ A = tab64Sub tabT tabT_ok := by
  obtain ⟨l, hlen, hpred, hchain⟩ := exists_chain hAT hE.1 (k := 6) (by norm_num) hE.2
  rcases (predC1_spec hpred).2 (by rw [hlen]; norm_num) with hS | hT | ⟨h5, _⟩
  · left
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · exact le_tab64Sub_of_forall tabS_ok (fun b hb => by
        obtain ⟨p, hp_mem, rfl⟩ := hchain b hb
        exact ⟨p, rfl, hS p hp_mem⟩)
    · rw [card_tab64Sub, hE.2]
      norm_num
  · right
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · exact le_tab64Sub_of_forall tabT_ok (fun b hb => by
        obtain ⟨p, hp_mem, rfl⟩ := hchain b hb
        exact ⟨p, rfl, hT p hp_mem⟩)
    · rw [card_tab64Sub, hE.2]
      norm_num
  · omega

end Chains

theorem classify_ge5
    {A : Subgroup S24} (hA : A ≤ M24g)
    (hel : IsElemAbelian 2 A) (h5 : 5 ≤ rk ↥A) :
    ∃ g ∈ M24g, conjSubg g A ≤ tab64Sub tabS tabS_ok ∨ conjSubg g A ≤ tab64Sub tabT tabT_ok := by
  set k : ℕ := rk ↥A with hkdef
  have hcard : Nat.card ↥A = 2 ^ k := by
    rw [hkdef]
    exact card_eq_two_pow_rk hel
  have hp : IsPGroup 2 A := isPGroup_of_isElemAbelian hel
  obtain ⟨h, hh, hconj⟩ := exists_conj_qPerms hA hp
  set A' : Subgroup S24 := conjSubg h A with hA'def
  have hAT' : ∀ a ∈ A', ∃ p : T24s2.Elem, a = T24s2.perm p := by
    intro a ha
    rw [hA'def, conjSubg] at ha
    obtain ⟨a₀, ha₀, rfl⟩ := Subgroup.mem_map.mp ha
    simpa [MulAut.conj_apply] using hconj a₀ ha₀
  have hel' : IsElemAbelian 2 A' := by
    rw [hA'def, conjSubg]
    exact isElemAbelian_map_conj 2 h hel
  have hcard' : Nat.card ↥A' = 2 ^ k := by
    rw [hA'def, conjSubg, card_map_conj h A, hcard]
  have hkle : k ≤ 6 := rank_le_six hAT' hel' hcard'
  obtain ⟨l, hlen, hpred, hchain⟩ := exists_chain hAT' hel' (by omega) hcard'
  have h5l : 5 ≤ l.length := by rw [hlen, hkdef]; exact h5
  rcases (predC1_spec hpred).2 h5l with hS | hT | ⟨hlen5, cs, hcs, hcarry⟩
  · refine ⟨h, hh, Or.inl ?_⟩
    rw [← hA'def]
    exact le_tab64Sub_of_forall tabS_ok (fun b hb => by
      obtain ⟨p, hp_mem, rfl⟩ := hchain b hb
      exact ⟨p, rfl, hS p hp_mem⟩)
  · refine ⟨h, hh, Or.inr ?_⟩
    rw [← hA'def]
    exact le_tab64Sub_of_forall tabT_ok (fun b hb => by
      obtain ⟨p, hp_mem, rfl⟩ := hchain b hb
      exact ⟨p, rfl, hT p hp_mem⟩)
  · refine ⟨permOfArrD cs.1 * h,
      M24g.mul_mem (permOfArrD_mem_M24g (c1Fuse_ok cs hcs)) hh, ?_⟩
    have key : ∀ (tab : Array (Array ℕ)) (hT : tab64OK tab = true),
        (∀ x ∈ subprods l, inTab64 tab (c1Conj cs.1 (T24s2.arr x)) = true) →
        conjSubg (permOfArrD cs.1 * h) A ≤ tab64Sub tab hT := by
      intro tab hT hcr a ha
      obtain ⟨a₀, ha₀, haeq⟩ := Subgroup.mem_map.mp ha
      obtain ⟨p, hp_eq⟩ := hconj a₀ ha₀
      have hmemA' : h * a₀ * h⁻¹ ∈ A' := by
        rw [hA'def]
        exact Subgroup.mem_map.mpr ⟨a₀, ha₀, by simp [MulAut.conj_apply]⟩
      obtain ⟨p', hp'mem, hp'eq⟩ := hchain _ hmemA'
      have hpp' : p = p' := T24s2.perm_injective (hp_eq.symm.trans hp'eq)
      have hp_mem : p ∈ subprods l := hpp' ▸ hp'mem
      have harr : HasArr (permOfArrD cs.1 * T24s2.perm p * (permOfArrD cs.1)⁻¹)
          (conj24 cs.1 (T24s2.arr p)) :=
        hasArr_conj (hasArr_permOfArrD (c1Fuse_ok cs hcs)) (c1Fuse_ok cs hcs)
          (T24s2.hasArr_perm p)
      have hb : inTab64 tab (conj24 cs.1 (T24s2.arr p)) = true := by
        have h := hcr p hp_mem
        rwa [c1Conj_eq] at h
      have hmem : permOfArrD cs.1 * T24s2.perm p * (permOfArrD cs.1)⁻¹ ∈ tab64Sub tab hT :=
        mem_tab64Sub_of_inTab64 hT harr hb
      have heq : a = permOfArrD cs.1 * T24s2.perm p * (permOfArrD cs.1)⁻¹ := by
        rw [← haeq]
        show (permOfArrD cs.1 * h) * a₀ * (permOfArrD cs.1 * h)⁻¹ =
          permOfArrD cs.1 * T24s2.perm p * (permOfArrD cs.1)⁻¹
        rw [show (permOfArrD cs.1 * h) * a₀ * (permOfArrD cs.1 * h)⁻¹ =
            permOfArrD cs.1 * (h * a₀ * h⁻¹) * (permOfArrD cs.1)⁻¹ by group, hp_eq]
      rw [heq]
      exact hmem
    by_cases hside : cs.2
    · left
      have hcarry' : ∀ x ∈ subprods l,
          inTab64 tabS (c1Conj cs.1 (T24s2.arr x)) = true := by
        intro x hx
        have h := hcarry x hx
        rwa [if_pos hside] at h
      exact key tabS tabS_ok hcarry'
    · right
      have hcarry' : ∀ x ∈ subprods l,
          inTab64 tabT (c1Conj cs.1 (T24s2.arr x)) = true := by
        intro x hx
        have h := hcarry x hx
        rwa [if_neg hside] at h
      exact key tabT tabT_ok hcarry'

end CFSG.Quasithin.AppendixH.H14
