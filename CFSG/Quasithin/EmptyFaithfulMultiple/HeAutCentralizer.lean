module

public import CFSG.Quasithin.EmptyFaithfulMultiple.Inputs5
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1HeAut
public import Certificates.Certificate260000

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

open CFSG.QuasithinUnique.Setup.X1 CFSG.Sporadic.HeldB CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Open

section Enum

variable {n : ℕ}

theorem sylVerify_enum {N : ℕ} {H : Subgroup (Equiv.Perm (Fin n))} {gens : List PArr}
    (hgens : RegIn n H gens) {par lab tab : List ℕ} {Al : Array (Array ℕ)} {r : ℕ}
    (hv : sylVerify n N gens par lab tab Al r = true) :
    (∀ k < N, Rep n Al[k]! (permOfArr n Al[k]!)) ∧ permOfArr n Al[0]! = 1 ∧
    (∀ k < N, permOfArr n Al[k]! ∈ H) ∧
    (∀ i < N, ∀ j < N, permOfArr n Al[i]! = permOfArr n Al[j]! → i = j) ∧
    ∃ U : Subgroup (Equiv.Perm (Fin n)), ∀ x, x ∈ U ↔ ∃ i < N, x = permOfArr n Al[i]! := by
  classical
  simp only [sylVerify, Bool.and_eq_true, decide_eq_true_eq, allLt_iff] at hv
  obtain ⟨⟨⟨⟨⟨⟨⟨-, hN0⟩, h0⟩, hpar⟩, htab⟩, hinv⟩, hnd⟩, -⟩ := hv
  have hgj : ∀ j : ℕ, ∃ g ∈ H, PRep n (gens.getD j (pId n)) g := fun j => hgens.getD j
  choose gp hgpH hgpRep using hgj
  set E : ℕ → Equiv.Perm (Fin n) := fun k => permOfArr n Al[k]! with hE
  have hrep : ∀ k < N, Rep n Al[k]! (E k) := fun k hk => (rep_permOfArr (hinv k hk)).1
  have hE0 : E 0 = 1 := (eqA_iff (hrep 0 hN0) rep_idA).1 h0
  have hstep : ∀ k < N, k ≠ 0 → par.getD k 0 < k ∧ lab.getD k 0 < gens.length ∧
      E k = E (par.getD k 0) * gp (lab.getD k 0) := by
    intro k hk hk0
    have h := hpar k hk
    simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with h | ⟨⟨hp, hl⟩, he⟩
    · exact absurd h hk0
    · refine ⟨hp, hl, ?_⟩
      have hr2 : Rep n (compA n Al[par.getD k 0]! (gens.getD (lab.getD k 0) (pId n)).1)
          (E (par.getD k 0) * gp (lab.getD k 0)) :=
        rep_compA (hrep _ (hp.trans hk)) (hgpRep _).1
      exact (eqA_iff (hrep k hk) hr2).1 he
  have htabE : ∀ i < N, ∀ j < gens.length, ∃ k < N, E i * gp j = E k := by
    intro i hi j hj
    obtain ⟨hk, he⟩ := htab i hi j hj
    refine ⟨tab.getD (i * gens.length + j) 0, hk, ?_⟩
    have hr2 : Rep n (compA n Al[i]! (gens.getD j (pId n)).1) (E i * gp j) :=
      rep_compA (hrep i hi) (hgpRep j).1
    exact (eqA_iff hr2 (hrep _ hk)).1 he
  set rg : List (Equiv.Perm (Fin n)) := (List.range gens.length).map gp with hrg
  have hEclos : ∀ k < N, E k ∈ Subgroup.closure {g | g ∈ rg} := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk
      by_cases hk0 : k = 0
      · subst hk0
        rw [hE0]
        exact Subgroup.one_mem _
      · obtain ⟨hp, hl, he⟩ := hstep k hk hk0
        rw [he]
        refine Subgroup.mul_mem _ (ih _ hp (hp.trans hk)) (Subgroup.subset_closure ?_)
        exact List.mem_map.2 ⟨_, List.mem_range.2 hl, rfl⟩
  have hEH : ∀ k < N, E k ∈ H := by
    intro k hk
    have : Subgroup.closure {g | g ∈ rg} ≤ H := by
      refine (Subgroup.closure_le H).2 fun g hg => ?_
      obtain ⟨j, -, rfl⟩ := List.mem_map.1 hg
      exact hgpH j
    exact this (hEclos k hk)
  have hinjE : ∀ i < N, ∀ j < N, E i = E j → i = j := by
    intro i hi j hj hij
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · have h := hnd j hj i hlt
      rw [(eqA_iff (hrep j hj) (hrep i hi)).2 hij.symm] at h
      exact absurd h (by simp)
    · have h := hnd i hi j hlt
      rw [(eqA_iff (hrep i hi) (hrep j hj)).2 hij] at h
      exact absurd h (by simp)
  obtain ⟨U0, hU0⟩ := exists_subgroup_of_gens rg ((List.range N).map E)
    (List.mem_map.2 ⟨0, List.mem_range.2 hN0, hE0⟩)
    (by
      intro x hx g hg
      obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
      obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hg
      obtain ⟨k, hk, hik⟩ := htabE i (List.mem_range.1 hi) j (List.mem_range.1 hj)
      exact List.mem_map.2 ⟨k, List.mem_range.2 hk, hik.symm⟩)
    (by
      intro x hx
      obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
      exact hEclos i (List.mem_range.1 hi))
  refine ⟨hrep, hE0, hEH, hinjE, U0, fun x => ?_⟩
  rw [hU0, List.mem_map]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, List.mem_range.1 hi, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, List.mem_range.2 hi, rfl⟩

theorem card_of_enum {G : Type*} [Group G] {N : ℕ} (E : ℕ → G)
    (hinj : ∀ i < N, ∀ j < N, E i = E j → i = j) (U : Subgroup G)
    (hU : ∀ x, x ∈ U ↔ ∃ i < N, x = E i) : Nat.card U = N := by
  have hbij : Function.Bijective (fun i : Fin N => (⟨E i, (hU _).2 ⟨i, i.2, rfl⟩⟩ : U)) := by
    constructor
    · intro i j hij
      exact Fin.ext (hinj i i.2 j j.2 (congrArg Subtype.val hij))
    · rintro ⟨x, hx⟩
      obtain ⟨i, hi, rfl⟩ := (hU x).1 hx
      exact ⟨⟨i, hi⟩, rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective _ hbij), Nat.card_eq_fintype_card, Fintype.card_fin]

end Enum

section Sylow

variable {G : Type*} [Group G]

theorem isPGroup_zpowers_of_mul_self {a : G} (ha : a * a = 1) :
    IsPGroup 2 (Subgroup.zpowers a) := by
  have hdvd : orderOf a ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact ha)
  rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
  · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h, pow_zero])
  · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h, pow_one])

variable [Finite G]

theorem exists_conj_le_of_isPGroup (U : Subgroup G) {a m : ℕ} (hU : Nat.card U = 2 ^ a)
    (hG : Nat.card G = 2 ^ a * m) (hm : Odd m) (B : Subgroup G) (hB : IsPGroup 2 B) :
    ∃ g : G, ∀ x ∈ B, g * x * g⁻¹ ∈ U := by
  have hidx : U.index = m := by
    have := Subgroup.card_mul_index U
    rw [hU, hG] at this
    exact Nat.eq_of_mul_eq_mul_left (by positivity) this
  have hodd : ¬ 2 ∣ U.index := by
    rw [hidx]
    intro hd
    obtain ⟨k, hk⟩ := hm
    omega
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpg : IsPGroup 2 U := IsPGroup.of_card hU
  obtain ⟨Q, hQ⟩ := hB.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Q (hpg.toSylow hodd)
  refine ⟨g, fun x hx => ?_⟩
  have hmem : g * x * g⁻¹ ∈ ((g • Q : Sylow 2 G) : Set G) := by
    rw [Sylow.coe_smul]
    exact ⟨x, hQ hx, rfl⟩
  rw [hg] at hmem
  exact hmem

theorem exists_conj_le_of_isPGroup_of_le {H U Q : Subgroup G} (hUH : U ≤ H) (hQH : Q ≤ H)
    {a m : ℕ} (hU : Nat.card U = 2 ^ a) (hH : Nat.card H = 2 ^ a * m) (hm : Odd m)
    (hQ : IsPGroup 2 Q) : ∃ g ∈ H, ∀ x ∈ Q, g * x * g⁻¹ ∈ U := by
  have hU' : Nat.card (U.subgroupOf H) = 2 ^ a := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUH).toEquiv, hU]
  obtain ⟨g, hg⟩ := exists_conj_le_of_isPGroup (U.subgroupOf H) hU' hH hm (Q.subgroupOf H)
    hQ.comap_subtype
  refine ⟨g, g.2, fun x hx => ?_⟩
  have h := hg ⟨x, hQH hx⟩ (Subgroup.mem_subgroupOf.2 hx)
  rw [Subgroup.mem_subgroupOf] at h
  simpa using h

theorem card_eq_of_quasithinIsSylowTwo {S : Subgroup G} (hS : quasithinIsSylowTwo S)
    (hG : Nat.card G = 4030387200) : Nat.card S = 1024 := by
  obtain ⟨hp, hidx⟩ := hS
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hp
  have hmul := Subgroup.card_mul_index S
  rw [hk, hG] at hmul
  have h1 : 2 ^ k ∣ 2 ^ 10 * 3935925 := ⟨S.index, by rw [hmul]; norm_num⟩
  have h2 : 2 ^ 10 ∣ 2 ^ k * S.index := ⟨3935925, by rw [hmul]; norm_num⟩
  have hc1 : Nat.Coprime (2 ^ k) 3935925 := Nat.Coprime.pow_left k (by norm_num)
  have hc2 : Nat.Coprime (2 ^ 10) S.index :=
    Nat.Coprime.pow_left 10 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hidx)
  have hk1 : k ≤ 10 :=
    (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 (hc1.dvd_of_dvd_mul_right h1)
  have hk2 : 10 ≤ k :=
    (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 (hc2.dvd_of_dvd_mul_right h2)
  rw [hk, show k = 10 by omega]
  norm_num

end Sylow

section Perm

theorem heSyl_enum :
    (∀ k < 2048, Rep 8330 heSylAl[k]! (permOfArr 8330 heSylAl[k]!)) ∧
    permOfArr 8330 heSylAl[0]! = 1 ∧ (∀ k < 2048, permOfArr 8330 heSylAl[k]! ∈ heAutGroup) ∧
    (∀ i < 2048, ∀ j < 2048, permOfArr 8330 heSylAl[i]! = permOfArr 8330 heSylAl[j]! →
      i = j) ∧
    ∃ U : Subgroup (Equiv.Perm (Fin 8330)),
      ∀ x, x ∈ U ↔ ∃ i < 2048, x = permOfArr 8330 heSylAl[i]! :=
  sylVerify_enum regIn_heSylGens he_syl_check

theorem heCent_check :
    heSiftAll heSylAl heCentIdx = true ∧ sylCentCheck 8330 2048 heSylAl heCentIdx 1 = true :=
  Certificates.certificate260000

theorem he_perm_core
    {S : Subgroup (Equiv.Perm (Fin 8330))} (hSP : S ≤ heP) (hS : Nat.card S = 1024)
    {a b : Equiv.Perm (Fin 8330)} (ha : a ∈ heAutGroup) (hb : b ∈ heAutGroup)
    (hab : a * b = b * a) (ha2 : a * a = 1) (hb2 : b * b = 1)
    (haS : ∀ s ∈ S, a * s = s * a) (hbS : ∀ s ∈ S, b * s = s * b) :
    a = 1 ∨ b = 1 ∨ a = b := by
  obtain ⟨hrep, hE0, hER, hinj, U, hU⟩ := heSyl_enum
  obtain ⟨hsift, hcent⟩ := heCent_check
  unfold heSiftAll at hsift
  have hUR : U ≤ heAutGroup := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := (hU x).1 hx
    exact hER i hi
  have hUc : Nat.card U = 2 ^ 11 := card_of_enum _ hinj U hU
  have hSp : IsPGroup 2 S := IsPGroup.of_card (n := 10) (by rw [hS]; norm_num)
  have hQ1 : IsPGroup 2 (S ⊔ Subgroup.zpowers a : Subgroup (Equiv.Perm (Fin 8330))) :=
    hSp.to_sup_of_normal_left' (isPGroup_zpowers_of_mul_self ha2)
      (Subgroup.zpowers_le.2 (Subgroup.centralizer_le_normalizer _
        (Subgroup.mem_centralizer_iff.2 fun h hh => (haS h hh).symm)))
  have hbQ1 : ∀ h ∈ S ⊔ Subgroup.zpowers a, h * b = b * h := by
    have hle : S ⊔ Subgroup.zpowers a ≤ Subgroup.centralizer {b} :=
      sup_le (fun s hs => Subgroup.mem_centralizer_singleton_iff.2 (hbS s hs).symm)
        (Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_singleton_iff.2 hab))
    exact fun h hh => Subgroup.mem_centralizer_singleton_iff.1 (hle hh)
  have hQ : IsPGroup 2
      ((S ⊔ Subgroup.zpowers a) ⊔ Subgroup.zpowers b : Subgroup (Equiv.Perm (Fin 8330))) :=
    hQ1.to_sup_of_normal_left' (isPGroup_zpowers_of_mul_self hb2)
      (Subgroup.zpowers_le.2 (Subgroup.centralizer_le_normalizer _
        (Subgroup.mem_centralizer_iff.2 hbQ1)))
  have hQR : (S ⊔ Subgroup.zpowers a) ⊔ Subgroup.zpowers b ≤ heAutGroup :=
    sup_le (sup_le (hSP.trans heP_le_heAutGroup) (Subgroup.zpowers_le.2 ha))
      (Subgroup.zpowers_le.2 hb)
  obtain ⟨g, hgR, hg⟩ := exists_conj_le_of_isPGroup_of_le (m := 3935925) hUR hQR hUc
    (by rw [card_heAutGroup]; norm_num) (by decide) hQ
  have hSQ : ∀ s ∈ S, s ∈ (S ⊔ Subgroup.zpowers a) ⊔ Subgroup.zpowers b :=
    fun s hs => Subgroup.mem_sup_left (Subgroup.mem_sup_left hs)
  have haQ : a ∈ (S ⊔ Subgroup.zpowers a) ⊔ Subgroup.zpowers b :=
    Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers a))
  have hbQ : b ∈ (S ⊔ Subgroup.zpowers a) ⊔ Subgroup.zpowers b :=
    Subgroup.mem_sup_right (Subgroup.mem_zpowers b)
  have hgN : g ∈ Subgroup.normalizer (heP : Set (Equiv.Perm (Fin 8330))) :=
    heAutGroup_le_normalizer hgR
  have hS3 : S.map (MulAut.conj g).toMonoidHom ≤ U ⊓ heP := by
    rintro _ ⟨s, hs, rfl⟩
    exact Subgroup.mem_inf.2 ⟨hg s (hSQ s hs), (Subgroup.mem_normalizer_iff.1 hgN s).1 (hSP hs)⟩
  have hS3c : Nat.card (S.map (MulAut.conj g).toMonoidHom) = 1024 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hS]
  have hUPc : Nat.card (U ⊓ heP : Subgroup (Equiv.Perm (Fin 8330))) ≤ 1024 := by
    have h1 : Nat.card (U ⊓ heP : Subgroup (Equiv.Perm (Fin 8330))) ∣ 2048 := by
      have := Subgroup.card_dvd_of_le (inf_le_left : U ⊓ heP ≤ U)
      rwa [hUc] at this
    have h2 : Nat.card (U ⊓ heP : Subgroup (Equiv.Perm (Fin 8330))) ∣ 4030387200 := by
      have := Subgroup.card_dvd_of_le (inf_le_right : U ⊓ heP ≤ heP)
      rwa [card_heP] at this
    have h3 := Nat.dvd_gcd h1 h2
    norm_num at h3
    exact Nat.le_of_dvd (by norm_num) h3
  have hS3eq : S.map (MulAut.conj g).toMonoidHom = U ⊓ heP :=
    Subgroup.eq_of_le_of_card_ge hS3 (by rw [hS3c]; exact hUPc)
  have hidx : ∀ j ∈ heCentIdx, j < 2048 := by
    intro j hj
    simp only [heCentIdx, List.mem_cons, List.not_mem_nil, or_false] at hj
    omega
  have hgen : ∀ j ∈ heCentIdx, ∃ s ∈ S, g * s * g⁻¹ = permOfArr 8330 heSylAl[j]! := by
    intro j hj
    have hjP : permOfArr 8330 heSylAl[j]! ∈ heP :=
      (mem_heP_iff_siftA (hrep j (hidx j hj))).1 (List.all_eq_true.1 hsift j hj)
    have hmem : permOfArr 8330 heSylAl[j]! ∈ U ⊓ heP :=
      Subgroup.mem_inf.2 ⟨(hU _).2 ⟨j, hidx j hj, rfl⟩, hjP⟩
    rw [← hS3eq] at hmem
    obtain ⟨s, hs, hse⟩ := hmem
    exact ⟨s, hs, hse⟩
  have key : ∀ x ∈ (S ⊔ Subgroup.zpowers a) ⊔ Subgroup.zpowers b, (∀ s ∈ S, x * s = s * x) →
      g * x * g⁻¹ = 1 ∨ g * x * g⁻¹ = permOfArr 8330 heSylAl[1]! := by
    intro x hxQ hxS
    obtain ⟨i, hi, hix⟩ := (hU _).1 (hg x hxQ)
    have hcomm : sylCommAll 8330 heSylAl heCentIdx i = true := by
      simp only [sylCommAll, List.all_eq_true]
      intro j hj
      obtain ⟨s, hs, hse⟩ := hgen j hj
      rw [eqA_iff (rep_compA (hrep i hi) (hrep j (hidx j hj)))
        (rep_compA (hrep j (hidx j hj)) (hrep i hi)), ← hix, ← hse]
      calc g * x * g⁻¹ * (g * s * g⁻¹) = g * (x * s) * g⁻¹ := by group
        _ = g * (s * x) * g⁻¹ := by rw [hxS s hs]
        _ = g * s * g⁻¹ * (g * x * g⁻¹) := by group
    have hci := (allLt_iff.1 hcent) i hi
    simp only [hcomm, Bool.not_true, Bool.false_or, Bool.or_eq_true, beq_iff_eq] at hci
    rcases hci with rfl | rfl
    · exact Or.inl (hix.trans hE0)
    · exact Or.inr hix
  rcases key a haQ haS with h1 | h1
  · exact Or.inl (conj_eq_one_iff.1 h1)
  rcases key b hbQ hbS with h2 | h2
  · exact Or.inr (Or.inl (conj_eq_one_iff.1 h2))
  · exact Or.inr (Or.inr (mul_left_cancel (mul_right_cancel (h1.trans h2.symm))))

end Perm

theorem heAutCentralizer_holds :
    HeAutCentralizer := by
  intro X _ hX S hS α β hα hβ hαβ hα2 hβ2
  obtain ⟨e⟩ := hX
  have hbij := ctbh_full_automorphism_permutation_model.1
  let φ : X ≃* heP := e.trans heEquivP
  have : Finite X := Finite.of_equiv _ φ.symm.toEquiv
  have hSc : Nat.card S = 1024 :=
    card_eq_of_quasithinIsSylowTwo hS (by rw [Nat.card_congr φ.toEquiv, card_heP])
  let c : heAutGroup ≃* MulAut heP := MulEquiv.ofBijective heConjR hbij
  let κ : MulAut X ≃* MulAut heP := MulAut.congr φ
  have hc : ∀ x, c x = heConjR x := fun _ => rfl
  have hS₂P : (S.map φ.toMonoidHom).map heP.subtype ≤ heP := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  have hS₂c : Nat.card ((S.map φ.toMonoidHom).map heP.subtype) = 1024 := by
    rw [Subgroup.card_map_of_injective heP.subtype_injective,
      Subgroup.card_map_of_injective φ.injective, hSc]
  have hfix : ∀ γ : MulAut X, (∀ s ∈ S, γ s = s) →
      ∀ t ∈ (S.map φ.toMonoidHom).map heP.subtype,
        ((c.symm (κ γ) : heAutGroup) : Equiv.Perm (Fin 8330)) * t =
          t * (c.symm (κ γ) : heAutGroup) := by
    rintro γ hγ _ ⟨_, ⟨s, hs, rfl⟩, rfl⟩
    have h1 : heConjR (c.symm (κ γ)) (φ s) = φ s := by
      rw [← hc, MulEquiv.apply_symm_apply]
      simp only [κ, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
        hγ s hs]
    have h2 := congrArg Subtype.val h1
    rw [heConjR_apply, Subgroup.coe_inv] at h2
    show ((c.symm (κ γ) : heAutGroup) : Equiv.Perm (Fin 8330)) * ((φ s : heP) : _) =
      ((φ s : heP) : Equiv.Perm (Fin 8330)) * ((c.symm (κ γ) : heAutGroup) : _)
    generalize ((c.symm (κ γ) : heAutGroup) : Equiv.Perm (Fin 8330)) = y at h2 ⊢
    generalize ((φ s : heP) : Equiv.Perm (Fin 8330)) = t at h2 ⊢
    calc y * t = y * t * y⁻¹ * y := by group
      _ = t * y := by rw [h2]
  have hmul : ∀ γ δ : MulAut X,
      ((c.symm (κ γ) : heAutGroup) : Equiv.Perm (Fin 8330)) * (c.symm (κ δ) : heAutGroup) =
        ((c.symm (κ (γ * δ)) : heAutGroup) : Equiv.Perm (Fin 8330)) := by
    intro γ δ
    rw [map_mul, map_mul]
    rfl
  have hone : ∀ γ : MulAut X,
      ((c.symm (κ γ) : heAutGroup) : Equiv.Perm (Fin 8330)) = 1 → γ = 1 := by
    intro γ h
    have h' : c.symm (κ γ) = 1 := Subtype.ext h
    have : κ γ = 1 := by
      rw [← MulEquiv.apply_symm_apply c (κ γ), h', map_one]
    exact κ.injective (this.trans (map_one κ).symm)
  have hcore := he_perm_core hS₂P hS₂c (c.symm (κ α)).2 (c.symm (κ β)).2
    (by rw [hmul, hmul, hαβ]) (by rw [hmul, hα2, map_one, map_one]; rfl)
    (by rw [hmul, hβ2, map_one, map_one]; rfl) (hfix α hα) (hfix β hβ)
  rcases hcore with h | h | h
  · exact Or.inl (hone α h)
  · exact Or.inr (Or.inl (hone β h))
  · refine Or.inr (Or.inr ?_)
    exact κ.injective (c.symm.injective (Subtype.ext h))

end CFSG.Quasithin.EmptyFaithfulMultiple
