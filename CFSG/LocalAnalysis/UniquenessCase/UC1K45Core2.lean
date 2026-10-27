module

public import CFSG.LocalAnalysis.UniquenessCase.UC1K45Core2Aux
public import CFSG.LocalAnalysis.UniquenessCase.UC1K45CommSub
public import CFSG.LocalAnalysis.UniquenessCase.UC1K45XGen

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.UC46

open Subgroup
open scoped commutatorElement

private lemma isKGroup_of_isSolvable_self (M : Type*) [Group M] [Group.IsSolvable M] :
    CFSG.Open.IsKGroup M := by
  intro K L _ hN hsimple hnab
  haveI := hsimple
  obtain ⟨a, b, hab⟩ := hnab
  exact (hab ((IsSimpleGroup.comm_iff_isSolvable).mpr inferInstance a b)).elim

lemma exists_invariant_sylow_conjNormal {Γ : Type} [Group Γ] [Finite Γ]
    {Dbar Kbar : Subgroup Γ} [Kbar.Normal] (d : Γ) (hdmem : d ∈ Dbar)
    (hD : Nat.card Dbar = 3) (hcop : Nat.Coprime 3 (Nat.card Kbar))
    (q : ℕ) (hq : q.Prime) :
    ∃ Q : Sylow q ↥Kbar,
      (Q : Subgroup ↥Kbar).map (MulAut.conjNormal d).toMonoidHom = Q := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime q) := ⟨hq⟩
  obtain ⟨Q, hQinv⟩ :=
    CFSG.OrderReductions.InvariantSylow.exists_invariant_sylow_of_coprime
      (actor := ↥Dbar) (group := ↥Kbar) 3 q
      (IsPGroup.of_card (n := 1) (by rw [hD]; norm_num))
      ((Nat.prime_three.coprime_iff_not_dvd).mp hcop)
      ((MulAut.conjNormal : Γ →* MulAut ↥Kbar).comp Dbar.subtype)
  exact ⟨Q, by simpa using hQinv ⟨d, hdmem⟩⟩

lemma eq_one_of_orderOf_dvd_two_pow_and_odd_prime {G : Type} [Group G] {y : G} {q m n : ℕ}
    (hq : q.Prime) (hq2 : q ≠ 2) (hm : orderOf y ∣ 2 ^ m) (hn : orderOf y ∣ q ^ n) :
    y = 1 := by
  have hnot2 : ¬ 2 ∣ q := fun h =>
    hq2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hq).mp h).symm
  have hcop2q : Nat.Coprime 2 q := (Nat.prime_two.coprime_iff_not_dvd).mpr hnot2
  have hcopP : Nat.Coprime (2 ^ m) (q ^ n) := by
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · subst hm0
      simp
    · rcases Nat.eq_zero_or_pos n with hn0 | hnpos
      · subst hn0
        simp
      · exact (Nat.coprime_pow_right_iff hnpos _ _).mpr
          ((Nat.coprime_pow_left_iff hmpos _ _).mpr hcop2q)
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcopP hm hn)

lemma conjNormal_eq_self_of_mem_invariant_sylow {Γ : Type} [Group Γ] [Finite Γ]
    {Dbar Kbar : Subgroup Γ} [Kbar.Normal] (d : Γ) (hdmem : d ∈ Dbar)
    (hD : Nat.card Dbar = 3)
    (hpair : ∀ k ∈ Kbar, Z3E9A5Mod2 (Dbar ⊔ Dbar.map (MulAut.conj k).toMonoidHom))
    (hsolv : Group.IsSolvable ↥Kbar) (hcop : Nat.Coprime 3 (Nat.card Kbar))
    (q : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) (Q : Sylow q ↥Kbar)
    (hQinv : (Q : Subgroup ↥Kbar).map (MulAut.conjNormal d).toMonoidHom = Q) :
    ∀ x ∈ (Q : Subgroup ↥Kbar), MulAut.conjNormal d x = x := by
  intro x hx
  have hσx : MulAut.conjNormal d x ∈ (Q : Subgroup ↥Kbar) := by
    have h : MulAut.conjNormal d x ∈
        (Q : Subgroup ↥Kbar).map (MulAut.conjNormal d).toMonoidHom :=
      Subgroup.mem_map_of_mem _ hx
    rwa [hQinv] at h
  have hyQ : x⁻¹ * MulAut.conjNormal d x ∈ (Q : Subgroup ↥Kbar) :=
    (Q : Subgroup ↥Kbar).mul_mem ((Q : Subgroup ↥Kbar).inv_mem hx) hσx
  obtain ⟨m, hm⟩ :=
    exists_orderOf_inv_mul_conjNormal_dvd_two d hdmem hD hpair hsolv hcop x
  obtain ⟨n, hn⟩ := IsPGroup.exists_orderOf_dvd_pow Q.isPGroup'
    (⟨x⁻¹ * MulAut.conjNormal d x, hyQ⟩ : ↥(Q : Subgroup ↥Kbar))
  have hn' : orderOf (x⁻¹ * MulAut.conjNormal d x) ∣ q ^ n := by
    rw [Subgroup.orderOf_mk] at hn
    exact hn
  have hxx : x⁻¹ * MulAut.conjNormal d x = 1 :=
    eq_one_of_orderOf_dvd_two_pow_and_odd_prime hq hq2 hm hn'
  calc MulAut.conjNormal d x = x * (x⁻¹ * MulAut.conjNormal d x) := by group
    _ = x * 1 := by rw [hxx]
    _ = x := mul_one x

lemma fixesSylow_conjNormal_odd {Γ : Type} [Group Γ] [Finite Γ] {Dbar Kbar : Subgroup Γ}
    [Kbar.Normal] (d : Γ) (hdmem : d ∈ Dbar) (hD : Nat.card Dbar = 3)
    (hpair : ∀ k ∈ Kbar, Z3E9A5Mod2 (Dbar ⊔ Dbar.map (MulAut.conj k).toMonoidHom))
    (hsolv : Group.IsSolvable ↥Kbar) (hcop : Nat.Coprime 3 (Nat.card Kbar)) :
    ∀ q, q.Prime → q ≠ 2 → q ≠ 2 →
      K22p.FixesSylow (MulAut.conjNormal d : MulAut ↥Kbar) q := by
  intro q hq hq2 _
  obtain ⟨Q, hQinv⟩ := exists_invariant_sylow_conjNormal d hdmem hD hcop q hq
  exact ⟨Q, conjNormal_eq_self_of_mem_invariant_sylow d hdmem hD hpair hsolv hcop q hq hq2
    Q hQinv⟩

lemma commSub_isPGroup_two (hAbs : K22p.K22pAbs) (hSz1 : SimpleThreePrimeIsSz)
    (hSz2 : SzOrder3Aut) {Γ : Type} [Group Γ] [Finite Γ] {Kbar : Subgroup Γ}
    [Kbar.Normal] (d : Γ) (hsolv : Group.IsSolvable ↥Kbar)
    (hcop : Nat.Coprime 3 (Nat.card Kbar))
    (hσ3 : (MulAut.conjNormal d : MulAut ↥Kbar) ^ 3 = 1)
    (hfix : ∀ q, q.Prime → q ≠ 2 → q ≠ 2 →
      K22p.FixesSylow (MulAut.conjNormal d : MulAut ↥Kbar) q) :
    IsPGroup 2 (K22p.commSub (MulAut.conjNormal d : MulAut ↥Kbar)) := by
  have hKgroup : CFSG.Open.IsKGroup ↥Kbar := by
    haveI : Group.IsSolvable ↥Kbar := hsolv
    exact isKGroup_of_isSolvable_self ↥Kbar
  have hprime : ∀ r, r.Prime →
      r ∣ Nat.card (K22p.commSub (MulAut.conjNormal d : MulAut ↥Kbar)) → r = 2 := by
    intro r hr hrdvd
    rcases hAbs hSz1 hSz2 2 ↥Kbar hKgroup
      ((Nat.prime_three.coprime_iff_not_dvd).mp hcop) (MulAut.conjNormal d) hσ3 hfix
      r hr hrdvd with h | h
    · exact h
    · exact h
  exact IsPGroup.of_card (p := 2)
    (n := (Nat.card (K22p.commSub (MulAut.conjNormal d : MulAut ↥Kbar))).primeFactorsList.length)
    (Nat.eq_prime_pow_of_unique_prime_dvd
      (Nat.card_pos (α := ↥(K22p.commSub (MulAut.conjNormal d : MulAut ↥Kbar)))).ne'
      (fun {r} hr hrdvd => hprime r hr hrdvd))

lemma eq_pCoreOf_of_commutator_top {Γ : Type} [Group Γ] [Finite Γ] {Dbar Kbar : Subgroup Γ}
    [Kbar.Normal] (d : Γ) (hd : Dbar = Subgroup.zpowers d)
    (hgen : Subgroup.normalClosure (Dbar : Set Γ) = ⊤)
    (hperf : ⁅Kbar, (⊤ : Subgroup Γ)⁆ = Kbar)
    (hcommSub2 : IsPGroup 2 (K22p.commSub (MulAut.conjNormal d : MulAut ↥Kbar))) :
    Kbar = CFSG.Open.pCoreOf 2 Kbar := by
  have hcommSubNormal : (K22p.commSub (MulAut.conjNormal d : MulAut ↥Kbar)).Normal :=
    ⟨fun c hc m => conj_mem_commSub (MulAut.conjNormal d) m hc⟩
  have hLO : ⁅Kbar, Dbar⁆ ≤ CFSG.Open.pCoreOf 2 Kbar := by
    have hle : K22p.commSub (MulAut.conjNormal d : MulAut ↥Kbar) ≤ CFSG.pCore 2 ↥Kbar := by
      show _ ≤ sSup {K : Subgroup ↥Kbar | K.Normal ∧ IsPGroup 2 K}
      exact le_sSup ⟨hcommSubNormal, hcommSub2⟩
    have hmap : (K22p.commSub (MulAut.conjNormal d : MulAut ↥Kbar)).map Kbar.subtype ≤
        (CFSG.pCore 2 ↥Kbar).map Kbar.subtype :=
      Subgroup.map_mono (f := Kbar.subtype) hle
    rw [commSub_conjNormal_map Kbar Dbar d hd] at hmap
    exact hmap
  have hO_normal : (CFSG.Open.pCoreOf 2 Kbar).Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [CFSG.openPCoreOf_eq_map_pCore] at hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
    refine Subgroup.mem_map.2 ⟨MulAut.conjNormal g y, ?_, ?_⟩
    · haveI : (CFSG.pCore 2 ↥Kbar).Characteristic := inferInstance
      have h := (Subgroup.characteristic_iff_map_le.1
        (inferInstance : (CFSG.pCore 2 ↥Kbar).Characteristic)) (MulAut.conjNormal g)
      exact h ⟨y, hy, rfl⟩
    · simp [MulAut.conjNormal_apply]
  haveI : (CFSG.Open.pCoreOf 2 Kbar).Normal := hO_normal
  apply le_antisymm
  · calc Kbar = ⁅Kbar, (⊤ : Subgroup Γ)⁆ := hperf.symm
      _ = Subgroup.normalClosure ((⁅Kbar, Dbar⁆ : Subgroup Γ) : Set Γ) :=
            commutator_top_eq_normalClosure (N := Kbar) (D := Dbar) hgen
      _ ≤ CFSG.Open.pCoreOf 2 Kbar :=
            Subgroup.normalClosure_le_normal
              (s := ((⁅Kbar, Dbar⁆ : Subgroup Γ) : Set Γ)) hLO
  · exact CFSG.openPCoreOf_le 2 Kbar

theorem core2_of (hAbs : K22p.K22pAbs) (hSz1 : SimpleThreePrimeIsSz) (hSz2 : SzOrder3Aut) :
    Core2 := by
  intro Γ _ _ Dbar Kbar _ hD hgen hsolv hcop hperf hpair
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨d, hd⟩ : ∃ d : Γ, Dbar = Subgroup.zpowers d := by
    have hcyc : IsCyclic ↥Dbar := isCyclic_of_prime_card hD
    obtain ⟨g, hg⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top Dbar).mp hcyc
    exact ⟨g, hg.symm⟩
  have hdmem : d ∈ Dbar := hd ▸ Subgroup.mem_zpowers d
  have horder : orderOf d = 3 := by
    have h : Nat.card (Subgroup.zpowers d) = 3 := by
      rw [← hd]
      exact hD
    rw [Nat.card_zpowers] at h
    exact h
  have hd3 : d ^ 3 = 1 := by
    rw [← horder]
    exact pow_orderOf_eq_one d
  have hσ3 : (MulAut.conjNormal d : MulAut ↥Kbar) ^ 3 = 1 := by
    rw [← map_pow (MulAut.conjNormal : Γ →* MulAut ↥Kbar), hd3, map_one]
  have hfix := fixesSylow_conjNormal_odd d hdmem hD hpair hsolv hcop
  have hcommSub2 := commSub_isPGroup_two hAbs hSz1 hSz2 d hsolv hcop hσ3 hfix
  have hKbar_eq_O := eq_pCoreOf_of_commutator_top d hd hgen hperf hcommSub2
  have hO2 : IsPGroup 2 (CFSG.Open.pCoreOf 2 Kbar) := by
    rw [CFSG.openPCoreOf_eq_map_pCore]
    exact (CFSG.pCore_isPGroup (p := 2) (G := ↥Kbar)).map Kbar.subtype
  rw [hKbar_eq_O]
  exact hO2

end CFSG.LocalAnalysis.UniquenessCase.UCK.UC46
