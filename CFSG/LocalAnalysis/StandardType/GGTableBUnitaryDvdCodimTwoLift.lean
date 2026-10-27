module

public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryTorus
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryEndNodeRestCover

public section

namespace CFSG.StandardType

open CFSG.Assembly TableB

namespace TableBUDT

section Lift

open CFSG.LieType.Steinberg TableBU

variable {H R L : Type} [Group H] [Group R] [Group L] [Finite H] [Finite L]

theorem exists_lift_elemAbelian (q : H →* R)
    (hsplit : ∀ (E : Type) [Group E] [Finite E] (π : E →* H), Function.Surjective π →
      π.ker ≤ Subgroup.center E → Nat.Coprime 2 (Nat.card π.ker) →
        ∃ s : H →* E, ∀ h, π (s h) = h)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {E₀ : Subgroup H} (hE₀ : IsElemAbelian p E₀)
    (hE₀q : E₀ ⊓ q.ker = ⊥) (ψ : L →* R) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center L) :
    ∃ E : Subgroup L, IsElemAbelian p E ∧ Nat.card E = Nat.card E₀ ∧ E ⊓ ψ.ker = ⊥ := by
  classical
  have := Fact.mk hp
  set N := twoPartOf ψ.ker hker (Nat.card L) with hNdef
  have hNk : N ≤ ψ.ker := twoPartOf_le _ hker _
  set π : L →* L ⧸ N := QuotientGroup.mk' N with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective N
  have hkerπ : π.ker = N := QuotientGroup.ker_mk' N
  set ψb : L ⧸ N →* R := QuotientGroup.lift N ψ hNk with hψb
  have hψbπ : ∀ l, ψb (π l) = ψ l := fun l => QuotientGroup.lift_mk N hNk l
  have hψbs : Function.Surjective ψb := by
    intro r
    obtain ⟨l, rfl⟩ := hψ r
    exact ⟨π l, hψbπ l⟩
  have hψbc : ψb.ker ≤ Subgroup.center (L ⧸ N) := by
    intro y hy
    obtain ⟨z, rfl⟩ := hπs y
    have hz : z ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, ← hψbπ]
      exact hy
    rw [Subgroup.mem_center_iff]
    intro w
    obtain ⟨v, rfl⟩ := hπs w
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp (hker hz) v]
  have hψbodd : ∀ y ∈ ψb.ker, y ^ 2 = 1 → y = 1 := fun y hy hy2 =>
    sq_eq_one_ker_lift hker y hy hy2
  set Pb := pullback q ψb with hPb
  have hfst := pullbackFst_surjective (β := q) hψbs
  have hfstc := ker_pullbackFst_le_center (β := q) hψbc
  have hcop : Nat.Coprime 2 (Nat.card (pullbackFst q ψb).ker) := by
    refine coprime_two_card_of_sq fun y hy2 => ?_
    obtain ⟨h1, h2⟩ := snd_mem_ker_of_mem_ker_pullbackFst y.2
    have h3 : (((y : Pb) : H × (L ⧸ N)).2) ^ 2 = 1 := by
      have := congrArg (fun z : (pullbackFst q ψb).ker => ((z : Pb) : H × (L ⧸ N)).2) hy2
      simpa using this
    have h4 := hψbodd _ h2 h3
    exact Subtype.ext (Subtype.ext (Prod.ext h1 h4))
  obtain ⟨σ, hσ⟩ := hsplit Pb (pullbackFst q ψb) hfst hfstc hcop
  set α : H →* L ⧸ N := ((MonoidHom.snd H (L ⧸ N)).comp Pb.subtype).comp σ with hαdef
  have hα : ∀ h, ψb (α h) = q h := by
    intro h
    have hmem := mem_pullback.1 (σ h).2
    have h1 : ((σ h : Pb) : H × (L ⧸ N)).1 = h := hσ h
    change ψb ((σ h : Pb) : H × (L ⧸ N)).2 = q h
    rw [← hmem, h1]
  set E' := E₀.map α with hE'
  have hinj : Function.Injective (α.comp E₀.subtype) := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have h1 : q (a : H) = 1 := by
      rw [← hα, show α (a : H) = 1 from ha, map_one]
    have h2 : (a : H) ∈ E₀ ⊓ q.ker := ⟨a.2, h1⟩
    rw [hE₀q, Subgroup.mem_bot] at h2
    exact Subtype.ext h2
  have hE'card : Nat.card E' = Nat.card E₀ := by
    have h1 : (α.comp E₀.subtype).range = E' := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [← h1]
    exact Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm
  have hE'ab : IsElemAbelian p E' := isElemAbelian_map hE₀ α
  set H' := E'.comap π with hH'
  have hNH' : N ≤ H' := by
    intro n hn
    have hn' : n ∈ π.ker := by
      rw [hkerπ]
      exact hn
    show π n ∈ E'
    rw [show π n = 1 from hn']
    exact E'.one_mem
  set f' : H' →* L ⧸ N := π.comp H'.subtype with hf'
  have hkerf' : f'.ker = N.subgroupOf H' := by
    ext h
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    show π h = 1 ↔ (h : L) ∈ N
    rw [← MonoidHom.mem_ker, hkerπ]
  have hrangef' : f'.range = E' := by
    ext y
    rw [MonoidHom.mem_range]
    constructor
    · rintro ⟨h, rfl⟩
      exact h.2
    · intro hy
      obtain ⟨l, rfl⟩ := hπs y
      exact ⟨⟨l, hy⟩, rfl⟩
  have hindex : (N.subgroupOf H').index = Nat.card E₀ := by
    rw [← hkerf', Subgroup.index_ker, hrangef', hE'card]
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp (isPGroup_twoPartOf ψ.ker hker (Nat.card L))
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp (isPGroup_of_isElemAbelian hE₀)
  have hcardN' : Nat.card (N.subgroupOf H') = 2 ^ a := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNH').toEquiv]
    exact ha
  have h2p : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).mpr fun h => hp2 h.symm
  have hcop' : Nat.Coprime (Nat.card (N.subgroupOf H')) (N.subgroupOf H').index := by
    rw [hcardN', hindex, hm]
    exact Nat.Coprime.pow a m h2p
  obtain ⟨C, hC⟩ := Subgroup.exists_right_complement'_of_coprime hcop'
  have hCcard : Nat.card C = Nat.card E₀ := by
    have h1 := hC.card_mul_card
    have h2 := Subgroup.card_mul_index (N.subgroupOf H')
    rw [← hindex]
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos (h1.trans h2.symm)
  set E : Subgroup L := C.map H'.subtype with hEdef
  have hEN : ∀ e ∈ E, π e = 1 → e = 1 := by
    rintro _ ⟨c, hc, rfl⟩ hce
    have hcN : c ∈ N.subgroupOf H' := by
      rw [← hkerf']
      exact hce
    have hc1 : c ∈ N.subgroupOf H' ⊓ C := ⟨hcN, hc⟩
    rw [hC.disjoint.eq_bot, Subgroup.mem_bot] at hc1
    rw [hc1]
    rfl
  have hEE' : ∀ e ∈ E, π e ∈ E' := by
    rintro _ ⟨c, -, rfl⟩
    exact c.2
  have hEab : IsElemAbelian p E := by
    refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun e he => ?_⟩
    · have hc : (x : L) * y * (x : L)⁻¹ * (y : L)⁻¹ = 1 := by
        refine hEN _ (E.mul_mem (E.mul_mem (E.mul_mem x.2 y.2) (E.inv_mem x.2)) (E.inv_mem y.2)) ?_
        have hxy := IsElemAbelian.comm hE'ab (hEE' _ x.2) (hEE' _ y.2)
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, hxy]
        group
      show (x : L) * y = y * x
      calc (x : L) * y = (x : L) * y * (x : L)⁻¹ * (y : L)⁻¹ * (y * x) := by group
        _ = y * x := by rw [hc, one_mul]
    · refine hEN _ (E.pow_mem he p) ?_
      rw [map_pow]
      exact hE'ab.2 _ (hEE' e he)
  have hEcard : Nat.card E = Nat.card E₀ := by
    rw [hEdef, Subgroup.card_map_of_injective H'.subtype_injective, hCcard]
  have hEker : E ⊓ ψ.ker = ⊥ := by
    rw [eq_bot_iff]
    rintro e ⟨heE, heK⟩
    obtain ⟨s, hs, hse⟩ := hEE' e heE
    have hqs : q s = 1 := by
      rw [← hα, hse, hψbπ]
      exact heK
    have hs1 : s ∈ E₀ ⊓ q.ker := ⟨hs, hqs⟩
    rw [hE₀q, Subgroup.mem_bot] at hs1
    rw [hs1, map_one] at hse
    exact (Subgroup.mem_bot).mpr (hEN e heE hse.symm)
  exact ⟨E, hEab, hEcard, hEker⟩

end Lift

section Torus

open CFSG.RankThree.Classical2 CFSG.SectionRank.OddCover CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial TableBU

variable {K : Type} [Field K] {n d p : ℕ}

theorem exists_torus_sub_two (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hd : 2 ≤ d)
    (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1) :
    ∃ E₀ : Subgroup (LargeEvenSUGroup (Fin d) K (2 ^ n)), IsElemAbelian p E₀ ∧
      Nat.card E₀ = p ^ (d - 2) ∧
        E₀ ⊓ (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n))).ker = ⊥ := by
  classical
  have := Fact.mk hp
  have : NeZero p := ⟨hp.ne_zero⟩
  have hKd : UnitaryFieldData 2 n K := unitaryFieldData_of_card hK hn
  set H := LargeEvenSUGroup (Fin d) K (2 ^ n) with hH
  obtain ⟨ζ, hζo, hζq⟩ := exists_orderOf_eq_norm_one hKd hp hpq
  have hζp : ζ ^ p = 1 := hζo ▸ pow_orderOf_eq_one ζ
  set i₀ : Fin d := ⟨d - 2, by omega⟩ with hi₀
  set i₁ : Fin d := ⟨d - 1, by omega⟩ with hi₁
  set c : Fin (d - 2) → Fin d → Kˣ := fun j =>
    Pi.mulSingle (⟨j, by omega⟩ : Fin d) ζ * Pi.mulSingle i₀ ζ⁻¹ with hc
  have hcpow : ∀ (k : ℕ), ζ ^ k = 1 → ∀ j i, c j i ^ k = 1 := by
    intro k hk j i
    simp only [hc, Pi.mul_apply, Pi.mulSingle_apply, mul_pow]
    split_ifs <;> simp [hk, inv_pow]
  have hcp : ∀ j i, c j i ^ p = 1 := hcpow p hζp
  have hcnorm : ∀ j i, c j i ^ (2 ^ n + 1) = 1 := hcpow _ hζq
  have hcprod : ∀ j, ∏ i, c j i = 1 := fun j => by
    simp only [hc, Pi.mul_apply, Finset.prod_mul_distrib, Fintype.prod_pi_mulSingle']
    group
  have hmemH : ∀ a, diagHom d (expHom c hcp a) ∈ H := fun a =>
    diagHom_expHom_mem_unitarySU hKd c hcp hcprod hcnorm a
  have hpriv : ∀ j, ∃ i, (∀ j', j' ≠ j → c j' i = 1) ∧ orderOf (c j i) = p := by
    intro j
    have hji₀ : (⟨j, by omega⟩ : Fin d) ≠ i₀ := by
      simp only [hi₀, ne_eq, Fin.mk.injEq]
      omega
    refine ⟨⟨j, by omega⟩, fun j' hj' => ?_, ?_⟩
    · have h1 : (⟨j, by omega⟩ : Fin d) ≠ ⟨j', by omega⟩ := by
        simp only [ne_eq, Fin.mk.injEq]
        exact fun h => hj' (Fin.ext h.symm)
      simp only [hc, Pi.mul_apply, Pi.mulSingle_eq_of_ne h1, Pi.mulSingle_eq_of_ne hji₀,
        mul_one]
    · simp only [hc, Pi.mul_apply, Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne hji₀, mul_one]
      exact hζo
  have hexpinj := expHom_injective c hcp hpriv
  set φ : Multiplicative (Fin (d - 2) → ZMod p) →* H :=
    ((diagHom d).comp (expHom c hcp)).codRestrict H hmemH with hφ
  have hφinj : Function.Injective φ := by
    intro a b hab
    have h1 : diagHom d (expHom c hcp a) = diagHom d (expHom c hcp b) := congrArg Subtype.val hab
    exact hexpinj (diagHom_injective d h1)
  set E₀ := φ.range with hE₀
  have hE₀card : Nat.card E₀ = p ^ (d - 2) := by
    rw [hE₀, Nat.card_congr (MonoidHom.ofInjective hφinj).toEquiv.symm,
      Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card,
      Fintype.card_fin]
  have hapow : ∀ a : Multiplicative (Fin (d - 2) → ZMod p), a ^ p = 1 := by
    intro a
    rw [← toAdd_eq_zero, toAdd_pow]
    funext i
    simp [Pi.smul_apply, nsmul_eq_mul]
  have hE₀ab : IsElemAbelian p E₀ := isElemAbelian_range (fun a b => mul_comm a b) hapow φ
  set q := LargeEvenProjMk H with hq
  have hkerq : q.ker = (LargeEvenScalars (Fin d) K).subgroupOf H := QuotientGroup.ker_mk' _
  have hscal : ∀ x : H, x ∈ q.ker → (x : GL (Fin d) K) ∈ Subgroup.center (GL (Fin d) K) := by
    intro x hx
    rw [hkerq, Subgroup.mem_subgroupOf] at hx
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact hx
  have hlast : ∀ a, expHom c hcp a i₁ = 1 := by
    intro a
    rw [expHom_apply]
    refine Finset.prod_eq_one fun j _ => ?_
    have h1 : i₁ ≠ ⟨j, by omega⟩ := by
      simp only [hi₁, ne_eq, Fin.mk.injEq]
      omega
    have h2 : i₁ ≠ i₀ := by
      simp only [hi₁, hi₀, ne_eq, Fin.mk.injEq]
      omega
    simp only [hc, Pi.mul_apply, Pi.mulSingle_eq_of_ne h1, Pi.mulSingle_eq_of_ne h2, mul_one,
      one_pow]
  have hE₀q : E₀ ⊓ q.ker = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨⟨a, rfl⟩, hx⟩
    have hcen : diagHom d (expHom c hcp a) ∈ Subgroup.center (GL (Fin d) K) := hscal _ hx
    have htc := diagHom_eq_of_mem_center hcen
    have ht1 : expHom c hcp a = 1 := by
      funext i
      rw [htc i i₁, hlast]
      rfl
    have ha1 : a = 1 := hexpinj (by rw [ht1, map_one])
    rw [ha1, map_one]
    exact Subgroup.one_mem _
  exact ⟨E₀, hE₀ab, hE₀card, hE₀q⟩

end Torus

section Cover

open CFSG.LocalAnalysis.ComponentInitial TableBU

variable {K : Type} [Field K] [Finite K] {n d p : ℕ}

theorem exists_elemAbelian_cover
    (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hd : 3 ≤ d)
    (hdq : (d, 2 ^ n) ≠ (3, 2)) (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1) {L : Type} [Group L]
    [Finite L] (ψ : L →* LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L) :
    ∃ E : Subgroup L, IsElemAbelian p E ∧ Nat.card E = p ^ (d - 2) ∧ E ⊓ ψ.ker = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKd : UnitaryFieldData 2 n K := unitaryFieldData_of_card hK hn
  have : CharP K 2 := hKd.charP
  have hp2 : p ≠ 2 := ne_two_of_dvd_two_pow_add_one hn hpq
  have hsplit : ∀ (E : Type) [Group E] [Finite E] (π : E →* LargeEvenSUGroup (Fin d) K (2 ^ n)),
      Function.Surjective π → π.ker ≤ Subgroup.center E → Nat.Coprime 2 (Nat.card π.ker) →
        ∃ s : LargeEvenSUGroup (Fin d) K (2 ^ n) →* E, ∀ h, π (s h) = h := by
    intro E _ _ π hπ hcen hC
    by_cases he : Even d
    · exact CFSG.LieType.Steinberg.CentralExt.SUClosed.statedSU_exists_section_of_coprime
        (F := K) (p := 2) (f := n) hK he (by omega) E π hπ hcen hC
    · exact CFSG.LieType.Steinberg.CentralExt.SUOdd.statedSU_odd_exists_section_of_central
        (F := K) (p := 2) (f := n) hK hn hd he hdq hπ hcen
  obtain ⟨E₀, hE₀, hcard, hE₀q⟩ := exists_torus_sub_two (d := d) hK hn (by omega) hp hpq
  obtain ⟨E, hE, hEc, hEk⟩ := exists_lift_elemAbelian
    (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n))) hsplit hp hp2 hE₀ hE₀q ψ hψ hker
  exact ⟨E, hE, hEc.trans hcard, hEk⟩

theorem exists_elemAbelian_cover_succ
    (hK : Nat.card K = (2 ^ n) ^ 2)
    (hn : 1 ≤ n) (hd : 3 ≤ d) (hdq : (d, 2 ^ n) ≠ (3, 2)) (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1)
    {L : Type} [Group L] [Finite L] (ψ : L →* LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L)
    (hpk : p ∣ Nat.card ψ.ker) :
    ∃ E : Subgroup L, IsElemAbelian p E ∧ Nat.card E = p ^ (d - 1) := by
  classical
  have := Fact.mk hp
  obtain ⟨E, hE, hEc, hEk⟩ := exists_elemAbelian_cover hK hn hd hdq hp hpq ψ hψ hker
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' p hpk
  set w : L := (z : L) with hw
  have hwc : w ∈ Subgroup.center L := hker z.2
  have hwo : orderOf w = p := by rw [hw, Subgroup.orderOf_coe, hz]
  set Z := Subgroup.zpowers w with hZ
  have hZk : Z ≤ ψ.ker := Subgroup.zpowers_le.mpr z.2
  have hcomm : ∀ (e : E) (u : Z), Commute (E.subtype e) (Z.subtype u) := by
    rintro e ⟨_, k, rfl⟩
    exact ((Subgroup.mem_center_iff.mp (Subgroup.zpow_mem _ hwc k)) (e : L))
  set f : E × Z →* L := MonoidHom.noncommCoprod E.subtype Z.subtype hcomm with hf
  have hfapp : ∀ x : E × Z, f x = (x.1 : L) * (x.2 : L) := fun x => rfl
  have hfinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    rintro ⟨e, u⟩ he
    rw [hfapp] at he
    have h1 : (e : L) = (u : L)⁻¹ := eq_inv_of_mul_eq_one_left he
    have h2 : (e : L) ∈ E ⊓ ψ.ker := ⟨e.2, h1 ▸ hZk (Z.inv_mem u.2)⟩
    rw [hEk, Subgroup.mem_bot] at h2
    have h3 : (u : L) = 1 := by rw [h2, one_mul] at he; exact he
    exact Prod.ext (Subtype.ext h2) (Subtype.ext h3)
  have hcomm' : ∀ a b : E × Z, a * b = b * a := by
    rintro ⟨e, u⟩ ⟨e', u'⟩
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · exact IsElemAbelian.comm hE e.2 e'.2
    · obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp u.2
      obtain ⟨k', hk'⟩ := Subgroup.mem_zpowers_iff.mp u'.2
      show (u : L) * u' = u' * u
      rw [← hk, ← hk', ← zpow_add, ← zpow_add, add_comm]
  have hpow : ∀ a : E × Z, a ^ p = 1 := by
    rintro ⟨e, u⟩
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · show (e : L) ^ p = 1
      exact hE.2 _ e.2
    · obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp u.2
      show (u : L) ^ p = 1
      rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hwo,
        pow_orderOf_eq_one, one_zpow]
  refine ⟨f.range, isElemAbelian_range hcomm' hpow f, ?_⟩
  rw [show Nat.card f.range = Nat.card (E × Z) from Nat.card_range_of_injective hfinj,
    Nat.card_prod, hEc, Nat.card_zpowers, hwo,
    show d - 1 = (d - 2) + 1 by omega, pow_succ]

theorem admissible_alpha
    (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hd : 3 ≤ d)
    (hdq : (d, 2 ^ n) ≠ (3, 2)) (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1) {L' : Type} [Group L']
    [Finite L'] (ψ : L' →* LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    {A : Subgroup (MulAut L')} (hA : Nat.card A < p ^ (d - 2)) (hadm : GGAdmissible p L' A) :
    ∃ U : Subgroup (MulAut L'), U ≠ ⊥ ∧ IsPGroup 2 U ∧
      A ≤ Subgroup.normalizer (U : Set (MulAut L')) := by
  rcases hadm with hα | ⟨-, hδ⟩ | ⟨hpZ, hδ⟩
  · exact hα
  · exfalso
    obtain ⟨E, hE, hEc, -⟩ := exists_elemAbelian_cover hK hn hd hdq hp hpq ψ hψ hker
    have := hδ E hE
    omega
  · exfalso
    have hZ := TableBUE.center_proj_eq_bot hK hd hdq
    have hkc := TableBUR.ker_eq_center_of_surjective hψ hker hZ
    rw [← hkc] at hpZ
    obtain ⟨E, hE, hEc⟩ := exists_elemAbelian_cover_succ hK hn hd hdq hp hpq ψ hψ hker hpZ
    have h1 : p ^ (d - 1) = p * p ^ (d - 2) := by
      rw [show d - 1 = (d - 2) + 1 by omega, pow_succ, mul_comm]
    have h2 := (hδ E hE).trans_lt (Nat.mul_lt_mul_of_pos_left hA hp.pos)
    rw [← h1, ← hEc] at h2
    exact lt_irrefl _ h2

end Cover

end TableBUDT

end CFSG.StandardType
