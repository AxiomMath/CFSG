module

public import CFSG.LocalAnalysis.StandardType.GGKacK0V2

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private lemma ggKacA12_map_commutator_subtype {L' : Type} [Group L'] (S : Subgroup L') :
    Subgroup.map S.subtype (commutator ↥S) = ⁅S, S⁆ := by
  change Subgroup.map S.subtype (⁅(⊤ : Subgroup ↥S), ⊤⁆) = ⁅S, S⁆
  rw [Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]

private lemma ggKacA12_conj_not_mem_zpowers {L' : Type} [Group L'] {e : MulAut L'}
    {S : Subgroup L'} (hSfix : S ≤ ggFixSub e) {t : ↥S}
    (ht : t ∉ Subgroup.center ↥S) :
    (MulAut.conj (t : L') : MulAut L') ∉ Subgroup.zpowers e := by
  intro hmem
  apply ht
  rw [Subgroup.mem_center_iff]
  intro s
  have hH : Subgroup.zpowers e ≤
      ({ carrier := {φ : MulAut L' | ∀ s ∈ S, φ s = s}
         one_mem' := by intro s _; rfl
         mul_mem' := by
           intro φ ψ hφ hψ s hs
           simp only [Set.mem_setOf_eq] at hφ hψ ⊢
           rw [MulAut.mul_apply, hψ s hs, hφ s hs]
         inv_mem' := by
           intro φ hφ s hs
           apply φ.injective
           simp only [Set.mem_setOf_eq] at hφ ⊢
           simpa [hφ s hs] } : Subgroup (MulAut L')) := by
    apply Subgroup.zpowers_le.mpr
    intro s hs
    exact mem_ggFixSub.mp (hSfix hs)
  have hconj := hH hmem (s : L') s.2
  have hc : (t : L') * (s : L') * (t : L')⁻¹ = (s : L') := by
    simpa [MulAut.conj_apply] using hconj
  apply Subtype.ext
  calc (s : L') * (t : L') = ((t : L') * (s : L') * (t : L')⁻¹) * (t : L') := by rw [hc]
    _ = (t : L') * (s : L') := by group

private lemma ggKacA12_pow_three {L' : Type} [Group L'] {S : Subgroup L'} {t0 : ↥S}
    (ht0 : t0 ∈ commutator ↥S) (hcard : Nat.card ↥(commutator ↥S) = 3) :
    (t0 : L') ^ 3 = 1 := by
  have hK : ((⟨t0, ht0⟩ : commutator ↥S) ^ 3) = 1 := by
    have h := pow_card_eq_one' (x := (⟨t0, ht0⟩ : commutator ↥S))
    rwa [hcard] at h
  have h2 : t0 ^ 3 = 1 := by
    have := congrArg (fun x : commutator ↥S => (x : ↥S)) hK
    simpa using this
  have := congrArg (fun x : ↥S => (x : L')) h2
  simpa using this

private lemma ggKacA12_aut_fixes {L' : Type} [Group L'] {p : ℕ} (hp : p = 3)
    {e : MulAut L'} {S : Subgroup L'}
    (hinv : ∀ φ : MulAut L', φ * e = e * φ → Subgroup.map (φ : L' →* L') S = S)
    {A : Subgroup (MulAut L')} (hA : IsElemAbelian p A) (heA : e ∈ A)
    {t0 : ↥S} (ht0 : t0 ∈ commutator ↥S) (ht0ne : t0 ≠ 1)
    (hcard : Nat.card ↥(commutator ↥S) = 3) :
    ∀ a ∈ A, a (t0 : L') = (t0 : L') := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hKmap := ggKacA12_map_commutator_subtype S
  have htC : (t0 : L') ∈ ⁅S, S⁆ := by
    have : (t0 : L') ∈ Subgroup.map S.subtype (commutator ↥S) :=
      Subgroup.mem_map_of_mem S.subtype ht0
    rwa [hKmap] at this
  have ht3 : (t0 : L') ^ 3 = 1 := ggKacA12_pow_three ht0 hcard
  intro a ha
  have hae : a * e = e * a := by
    have h := hA.1.is_comm.comm (⟨a, ha⟩ : ↥A) (⟨e, heA⟩ : ↥A)
    simpa using congrArg (fun x : ↥A => (x : MulAut L')) h
  have haS : S.map (a : L' →* L') = S := hinv a hae
  have ha3 : a ^ 3 = 1 := by
    have := hA.2 a ha
    rwa [hp] at this
  have hatC : a (t0 : L') ∈ ⁅S, S⁆ := by
    have hmap : Subgroup.map (a : L' →* L') ⁅S, S⁆ = ⁅S, S⁆ := by
      rw [Subgroup.map_commutator, haS]
    have : a (t0 : L') ∈ Subgroup.map (a : L' →* L') ⁅S, S⁆ :=
      Subgroup.mem_map_of_mem (a : L' →* L') htC
    rwa [hmap] at this
  have hatS : a (t0 : L') ∈ S := by
    have : a (t0 : L') ∈ Subgroup.map (a : L' →* L') S :=
      Subgroup.mem_map_of_mem (a : L' →* L') t0.2
    rwa [haS] at this
  have hatK : (⟨a (t0 : L'), hatS⟩ : ↥S) ∈ commutator ↥S := by
    have h : a (t0 : L') ∈ Subgroup.map S.subtype (commutator ↥S) := by
      rw [hKmap]
      exact hatC
    exact (Subgroup.mem_map_iff_mem (f := S.subtype)
      (Subgroup.subtype_injective S)).mp h
  let g : ↥(commutator ↥S) := ⟨t0, ht0⟩
  let u : ↥(commutator ↥S) := ⟨⟨a (t0 : L'), hatS⟩, hatK⟩
  have hg : g ≠ 1 := by
    intro h
    exact ht0ne (Subtype.ext_iff.mp h)
  have hg3 : g ^ 3 = 1 := by
    have := pow_card_eq_one' (x := g)
    rwa [hcard] at this
  have hu_ne : u ≠ 1 := by
    intro h
    have h1 : a (t0 : L') = 1 := by
      have := congrArg (fun x : ↥(commutator ↥S) => ((x : ↥S) : L')) h
      simpa [u] using this
    have h2 : (t0 : L') = 1 := by
      have := congrArg (fun x : L' => (a⁻¹ : MulAut L') x) h1
      simpa using this
    exact ht0ne (Subtype.ext h2)
  have hu : u = g ∨ u = g ^ 2 := by
    have hmem : u ∈ Submonoid.powers g := mem_powers_of_prime_card hcard hg
    rw [Submonoid.mem_powers_iff] at hmem
    obtain ⟨n, hn⟩ := hmem
    have hnmod : g ^ n = g ^ (n % 3) :=
      pow_eq_pow_of_modEq (Nat.mod_modEq n 3).symm hg3
    have hu2 : u = g ^ (n % 3) := by rw [← hn, hnmod]
    have hr : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by
      have := Nat.mod_lt n (by norm_num : 0 < 3)
      omega
    rcases hr with h0 | h1 | h2
    · rw [h0] at hu2
      simp only [pow_zero] at hu2
      exact (hu_ne hu2).elim
    · left
      rw [h1] at hu2
      simpa using hu2
    · right
      rw [h2] at hu2
      exact hu2
  rcases hu with h1 | h2
  · have := congrArg (fun x : ↥(commutator ↥S) => ((x : ↥S) : L')) h1
    simpa [u, g] using this
  · exfalso
    have hat2 : a (t0 : L') = (t0 : L') ^ 2 := by
      have := congrArg (fun x : ↥(commutator ↥S) => ((x : ↥S) : L')) h2
      simpa [u, g] using this
    have ha2t : ((a ^ 2 : MulAut L')) (t0 : L') = (t0 : L') := by
      rw [show ((a ^ 2 : MulAut L')) (t0 : L') = a (a (t0 : L')) from rfl, hat2, map_pow,
        hat2, ← pow_mul]
      show (t0 : L') ^ (2 * 2) = (t0 : L')
      rw [show 2 * 2 = 3 + 1 by norm_num, pow_succ, ht3, one_mul]
    have ha3t : ((a ^ 3 : MulAut L')) (t0 : L') = (t0 : L') ^ 2 := by
      rw [show ((a ^ 3 : MulAut L')) (t0 : L') = a (((a ^ 2 : MulAut L')) (t0 : L')) from rfl,
        ha2t, hat2]
    have hteq : (t0 : L') = (t0 : L') ^ 2 := by
      rw [ha3] at ha3t
      simpa using ha3t
    have ht1 : (t0 : L') = 1 := by
      have hmul : (t0 : L') * 1 = (t0 : L') * (t0 : L') := by
        rw [mul_one, ← pow_two, ← hteq]
      exact (mul_left_cancel hmul).symm
    exact ht0ne (Subtype.ext ht1)

theorem ggKacA12_sigma {L' : Type} [Group L'] {p : ℕ} (hp : p = 3) (e : MulAut L')
    (S : Subgroup L') (hSfix : S ≤ ggFixSub e)
    (hcomp : ∀ J : Subgroup L', CFSG.Assembly.IsComponentOf J (ggFixSub e) →
      ∀ s ∈ S, ∀ j ∈ J, s * j = j * s)
    (hinv : ∀ φ : MulAut L', φ * e = e * φ → Subgroup.map (φ : L' →* L') S = S)
    (hcard : Nat.card ↥(commutator ↥S) = 3) (hnc : ¬ commutator ↥S ≤ Subgroup.center ↥S)
    (A : Subgroup (MulAut L')) (heA : e ∈ A) (hA : IsElemAbelian p A) :
    ∃ t : L', t ^ p = 1 ∧ (∀ a ∈ A, a t = t) ∧
      (∀ J : Subgroup L', CFSG.Assembly.IsComponentOf J (ggFixSub e) →
        ∀ j ∈ J, t * j = j * t) ∧
      (MulAut.conj t : MulAut L') ∉ Subgroup.zpowers e := by
  obtain ⟨t0, ht0K, ht0nc⟩ := Set.not_subset.mp hnc
  have ht0ne : t0 ≠ 1 := by
    intro h
    exact ht0nc (by rw [h]; exact Subgroup.one_mem _)
  refine ⟨(t0 : L'), ?_, ?_, ?_, ?_⟩
  · rw [hp]
    exact ggKacA12_pow_three ht0K hcard
  · intro a ha
    exact ggKacA12_aut_fixes hp hinv hA heA ht0K ht0ne hcard a ha
  · intro J hJ j hj
    exact hcomp J hJ (t0 : L') t0.2 j hj
  · exact ggKacA12_conj_not_mem_zpowers hSfix ht0nc

end CFSG.StandardType

end
